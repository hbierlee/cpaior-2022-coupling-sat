/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// TODO [?] how do I check for unused includes?

#include <minizinc/ast.hh>
#include <minizinc/eval_par.hh>
#include <minizinc/file_utils.hh>
#include <minizinc/process.hh>
#include <minizinc/solns2out.hh>
#include <minizinc/solver_instance.hh>
#include <minizinc/solvers/sat/sat_model.hh>
#include <minizinc/solvers/sat/sat_solparser.hh>
#include <minizinc/solvers/sat/sat_solreader.hh>
#include <minizinc/solvers/sat/sat_solverinstance.hh>

#include <algorithm>
#include <array>
#include <cassert>  // for assert()
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <numeric>
#include <ostream>
#include <utility>
#include <vector>

using namespace std;

namespace MiniZinc {

/** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** ***
 * *** *** *** *** *** **/
// Solver Factory

SATSolverFactory::SATSolverFactory() {
  SolverConfig sc("org.minizinc.mzn-sat",
                  MZN_VERSION_MAJOR "." MZN_VERSION_MINOR "." MZN_VERSION_PATCH);
  sc.name("Generic (Max)SAT driver");
  sc.mznlibVersion(1);
  sc.description("MiniZinc generic (Max)SAT solver plugin");
  sc.inputType(SolverConfig::O_WDIMACS);
  sc.mznlib("-Gsat");
  sc.requiredFlags({"--sat-cmd"});
  sc.stdFlags({"-a", "-i"});
  sc.tags({"__internal__"});
  SolverConfigs::registerBuiltinSolver(sc);
}

string SATSolverFactory::getDescription(SolverInstanceBase::Options* /* opt*/) {
  string v = "SAT solver plugin, compiled  " __DATE__ "  " __TIME__;
  return v;
}

string SATSolverFactory::getVersion(SolverInstanceBase::Options* /* opt */) {
  return MZN_VERSION_MAJOR;
}

string SATSolverFactory::getId() { return "org.minizinc.mzn-sat"; }

void SATSolverFactory::printHelp(ostream& os) {
  os << "MZN-SAT plugin options" << std::endl
     << "  -a, --all, --all-solns, --all-solutions\n     Print all solutions.\n"
     << "--intermediate-solutions\n     Print intermediate solutions "
        "(optimization problems only).\n"
     << "  --extra-solver-args\n     Specify any extra arguments (2nd, 3rd, "
        "etc.) that needs to be passed to the solver.\n"
     << "  --output-dimacs-to-file <file>\n     Output a (W)DIMACS file "
        "(.dimacs file) to <file>\n"
     << "  --sat-solver <exe>\n     Path to the backend SAT solver.\n"
     << "  --max-sat-solver <exe>\n     Path to the backend MaxSAT solver. If no --sat-solver "
        "specified, the solver will be used for satisfaction problems.\n"
     << "  --sat-flag <option>\n     As above, but for a single option string "
        "that need to be quoted in a shell.\n"
     << "  --sat-flags <options>\n     Specify option to be passed to the SAT "
        "solver"
     << "  -t <ms>, --solver-time-limit <ms>, --fzn-time-limit <ms>\n     Set "
        "time limit (in milliseconds) for solving.\n";

}  // TODO [?] Can sat-flags/sat-flag/extra-solver-args be merged into one
   // generic 'extra-solver-args' flag? Basically, the only thing we need to add
   // (at this point of development in the interface) is the model path.

SolverInstanceBase::Options* SATSolverFactory::createOptions() { return new SATSolverOptions; }

SolverInstanceBase* SATSolverFactory::doCreateSI(Env& env, std::ostream& log,
                                                 SolverInstanceBase::Options* opt) {
  return new SATSolverInstance(env, log, opt);
}

bool SATSolverFactory::processOption(SolverInstanceBase::Options* opt, int& i,
                                     std::vector<std::string>& argv,
                                     const std::string& workingDir) {
  auto& _opt = static_cast<SATSolverOptions&>(*opt);
  CLOParser cop(i, argv);
  string buffer;

  int nn = -1;
  // TODO [>] add keep-output option?
  if (cop.getOption("--sat-cmd", &buffer)) {
    _opt.solver = buffer;
  } else if (cop.getOption("--sat-no-weights")) {
    _opt.solverInputFormat = SATModel::SolverInputFormat::DIMACS_CNF;
  } else if (cop.getOption("-a --all --all-solns --all-solutions")) {
    _opt.allSolutions = true;
  } else if (cop.getOption("-i --intermediate --intermediate-solutions")) {
    _opt.intermediateSolutions = true;
  } else if (cop.getOption("--output-dimacs-to-file", &buffer)) {
    _opt.outputDimacs = buffer;
  } else if (cop.getOption("-s --solver-statistics")) {
    // TODO this is now necessary to support in the interface?
    _opt.solverStatistics = true;
  } else if (cop.getOption("-v --verbose-solving")) {
    _opt.verbose = true;
  } else if (cop.getOption("-t --solver-time-limit --fzn-time-limit", &nn)) {
    _opt.solverTimeLimitMs = nn;
  } else if (cop.getOption("--extra-solver-args", &buffer)) {
    _opt.extraSolverArgs = buffer;
  } else {
    for (auto& fznf : _opt.satSolverFlags) {
      if (fznf.t == MZNFZNSolverFlag::FT_ARG && cop.getOption(fznf.n.c_str(), &buffer)) {
        _opt.satFlags.push_back(fznf.n);
        _opt.satFlags.push_back(buffer);
        return true;
      }
      if (fznf.t == MZNFZNSolverFlag::FT_NOARG && cop.getOption(fznf.n.c_str())) {
        _opt.satFlags.push_back(fznf.n);
        return true;
      }
    }
    return false;
  }

  return true;
}

// SATSolverInstance
SATSolverInstance::SATSolverInstance(Env& env, std::ostream& log,
                                     SolverInstanceBase::Options* options)
    : SolverInstanceBase(env, log, options),
      _fzn(env.flat()),
      _ozn(env.output()),
      _satModel(env, make_shared<PBConfigClass>()) {}

SATSolverInstance::~SATSolverInstance() {}

void SATSolverInstance::resetSolver() {}

void SATSolverInstance::processFlatZinc() {
  _processFlatZincTimer.reset();
  auto& opt = static_cast<SATSolverOptions&>(*_options);

  // Add the objective first
  auto* solve_item = _fzn->solveItem()->cast<SolveI>();
  if (opt.allSolutions && solve_item->st() != SolveI::SolveType::ST_SAT) {
    opt.allSolutions = false;
    // TODO why does the test sometimes for COP problem set allSolutions??
    // throw Error("The all solutions flag is supported for satisfaction "
    //             "problems, but not for optimization since MaxSAT solvers "
    //             "usually don't output intermediate solutions. ");
  }

  _satModel.addSolve(solve_item->st(), solve_item->e(), opt.solverInputFormat);

  // First go through negations (bool_not constraints) and (half-)fixed
  // equalities
  for (auto& it : _fzn->constraints()) {
    if (!it.removed()) {
      Expression* e = follow_id_to_decl(it.e());

      if (e->eid() == Expression::E_CALL) {
        const Call& call = *e->cast<Call>();

        // Typecheck every constraint here

        if (call.id() == _env.envi().constants.ids.bool_not) {
          _satModel.addNegation(call);
        } else if (call.id() == _env.envi().constants.ids.bool_eq) {
          // TODO this section can be removed once the compiler doesn't output
          // these resolvable bool_eq's
          if (call.arg(0)->type().isPar() && call.arg(1)->type().isPar()) {
            if (call.arg(0)->cast<BoolLit>()->v() == call.arg(1)->cast<BoolLit>()->v()) {
              continue;
            }
            Solns2Out* out = getSolns2Out();
            out->evalStatus(SolverInstance::UNSAT);
            return;
          }
          if (call.arg(0)->type().isPar() != call.arg(1)->type().isPar()) {
            Expression* var = call.arg(0)->type().isPar() ? follow_id_to_decl(call.arg(1))
                                                          : follow_id_to_decl(call.arg(0));
            bool par = call.arg(0)->type().isPar() ? call.arg(0)->cast<BoolLit>()->v()
                                                   : call.arg(1)->cast<BoolLit>()->v();
            std::vector<Expression*> vec_var = {var};
            std::vector<Expression*> vec_emp = {};
            auto* al_var = new ArrayLit(Location().introduce(), vec_var);
            auto* al_emp = new ArrayLit(Location().introduce(), vec_emp);
            al_var->type(Type::varbool(1));
            al_emp->type(Type::varbool(1));
            if (par) {
              _satModel.addClause(al_var, al_emp);
            } else {
              _satModel.addClause(al_emp, al_var);
            }
          } else {
            assert(false && "CNFlatZinc contains bool_eq with 2 non-fixed variables");
          }
        }
      }
    }
  }

  // Then through clauses (bool_clause, bool_clause_weighted)
  // TODO here we should recognize bool_clause([a,b], [a,b]) = bool_not([a,b])
  // and handle them as negations too
  for (auto& it : _fzn->constraints()) {
    if (!it.removed()) {
      Expression* e = follow_id_to_decl(it.e());

      bool model_consistent = true;
      Call& call = *e->cast<Call>();

      if (call.id() == _env.envi().constants.ids.bool_clause) {
        ArrayLit* positive_vars = eval_array_lit(_env.envi(), call.arg(0));
        ArrayLit* negative_vars = eval_array_lit(_env.envi(), call.arg(1));

        model_consistent = _satModel.addClause(positive_vars, negative_vars, IntVal::infinity());
      } else if (call.id() == "bool_clause_weighted") {
        if (call.argCount() == 5) {
          ArrayLit* positive_vars = eval_array_lit(_env.envi(), call.arg(0));
          ArrayLit* negative_vars = eval_array_lit(_env.envi(), call.arg(1));
          IntVal weight = eval_int(_env.envi(), call.arg(2));
          bool is_solve_minimize = eval_bool(_env.envi(), call.arg(4));
          model_consistent =
              _satModel.addClause(positive_vars, negative_vars, weight, is_solve_minimize);
        } else if (call.argCount() == 2) {
          IntVal weight = eval_int(_env.envi(), call.arg(0));
          model_consistent = _satModel.addClause(weight);
        }
      } else if (call.id() == "pblib_bool_at_most_one_pairwise") {
        assert(false && "deprecated");
        ArrayLit* lits = eval_array_lit(_env.envi(), call.arg(0));
        _satModel._pb_config->amo_encoder = AMO_ENCODER::PAIRWISE;
        model_consistent = _satModel.addPbConstraint<PBLib::Comparator::LEQ>(
            nullptr, lits, 1, nullptr, SATModel::PB_CONSTRAINT_CONTEXT::ROOT);
      } else if (call.id() == "pblib_bool_at_most_one_bimander") {
        assert(false && "deprecated");
        // TODO filter out fixed lits (should be merged with the other pblib funcs)
        ArrayLit* lits = eval_array_lit(_env.envi(), call.arg(0));
        auto bimander_m = eval_int(_env.envi(), call.arg(1)).toInt();
        auto bimander_offset = eval_int(_env.envi(), call.arg(2)).toInt();
        // TODO how to parse enums..
        auto bimander_aux_pattern = eval_int(_env.envi(), call.arg(3)).toInt();
        auto bimander_enforce_aux_var_domain = eval_bool(_env.envi(), call.arg(4));
        assert(bimander_m <= lits->length());

        _satModel._pb_config->amo_encoder = AMO_ENCODER::BIMANDER;
        _satModel._pb_config->bimander_m = bimander_m;
        _satModel._pb_config->bimander_m_is = BIMANDER_M_IS::FIXED;
        _satModel._pb_config->bimander_offset = bimander_offset;
        _satModel._pb_config->bimander_enforce_aux_var_domain = bimander_enforce_aux_var_domain;

        _statBimanderCount++;
        _statBimanderTotalN += lits->length();
        _statBimanderTotalM += bimander_m;
        _statBimanderTotalOffset += bimander_offset;

        if (bimander_aux_pattern == 1) {
          _satModel._pb_config->bimander_aux_pattern = BIMANDER_AUX_PATTERN::BINARY;
        } else if (bimander_aux_pattern == 2) {
          _satModel._pb_config->bimander_aux_pattern = BIMANDER_AUX_PATTERN::GRAY;
        } else {
          assert(false && "unexpected bimander_aux_pattern type");
        }
        model_consistent = _satModel.addPbConstraint<PBLib::Comparator::LEQ>(
            nullptr, lits, 1, nullptr, SATModel::PB_CONSTRAINT_CONTEXT::ROOT);
      } else if (call.id().beginsWith("pblib_bool_lin_") ||
                 call.id().beginsWith("pblib_bool_count_")) {
        ArrayLit* weights;
        ArrayLit* lits;
        IntVal res;
        Expression* reif;

        if (call.id().beginsWith("pblib_bool_lin_")) {
          weights = eval_array_lit(_env.envi(), call.arg(0));
          lits = eval_array_lit(_env.envi(), call.arg(1));
          res = eval_int(_env.envi(), call.arg(2));
          reif = call.argCount() == 5 ? follow_id_to_decl(call.arg(4)) : nullptr;
          auto method = eval_int(_env.envi(), call.arg(3)).toInt() - 1;
          _satModel._pb_config->pb_encoder = static_cast<PB_ENCODER::PB2CNF_PB_Encoder>(method);
        } else {  // count
          lits = eval_array_lit(_env.envi(), call.arg(0));
          weights = nullptr;
          res = eval_int(_env.envi(), call.arg(1));
          reif = call.argCount() == 4 ? follow_id_to_decl(call.arg(3)) : nullptr;
          auto method = eval_int(_env.envi(), call.arg(2)).toInt() - 1;
          _satModel._pb_config->amk_encoder = static_cast<AMK_ENCODER::PB2CNF_AMK_Encoder>(method);
        }

        SATModel::PB_CONSTRAINT_CONTEXT pb_constraint_context;
        if (call.id().endsWith("_impl")) {
          pb_constraint_context = SATModel::PB_CONSTRAINT_CONTEXT::IMP;
        } else if (call.id().endsWith("_reif")) {
          pb_constraint_context = SATModel::PB_CONSTRAINT_CONTEXT::REIF;
        } else {
          pb_constraint_context = SATModel::PB_CONSTRAINT_CONTEXT::ROOT;
          assert(reif == nullptr);
        }

        if (call.id().endsWith("_le") || call.id().endsWith("_le_impl") ||
            call.id().endsWith("_le_reif")) {
          model_consistent = _satModel.addPbConstraint<PBLib::Comparator::LEQ>(
              weights, lits, res, reif, pb_constraint_context);
        } else if (call.id().endsWith("_ge") || call.id().endsWith("_ge_impl") ||
                   call.id().endsWith("_ge_reif")) {
          model_consistent = _satModel.addPbConstraint<PBLib::Comparator::GEQ>(
              weights, lits, res, reif, pb_constraint_context);
        } else if (call.id().endsWith("_eq") || call.id().endsWith("_eq_impl") ||
                   call.id().endsWith("_eq_reif")) {
          model_consistent = _satModel.addPbConstraint<PBLib::Comparator::BOTH>(
              weights, lits, res, reif, pb_constraint_context);
        } else {
          assert(false && "Unknown pblib_bool_count_*/pblib_bool_lin_* call");
        }

        // if (pb_constraint_context == SATModel::PB_CONSTRAINT_CONTEXT::IMP ||
        //     SATModel::PB_CONSTRAINT_CONTEXT::REIF) {
        //   result = true;
        // }

      } else if (call.id() != _env.envi().constants.ids.bool_not &&
                 call.id() != _env.envi().constants.ids.bool_eq) {
        std::stringstream msg;
        msg << "MiniZinc SAT: Unsupported call found in generated FlatZinc: " << call;

        throw Error(msg.str());
      }
      if (!model_consistent) {
        std::ostringstream oss;
        oss << "Model inconsistency for call " << call << std::endl;
        for (size_t i = 0; i < call.argCount(); ++i) {
          oss << "Where arg " << i << " is " << *follow_id_to_decl(call.arg(i)) << std::endl;
        }
        Solns2Out* out = getSolns2Out();
        out->evalStatus(SolverInstance::UNSAT);
        // TODO how to use this so that tests/spec/unit/general/test_model_inconsistency.mzn passes?
        // not it either, and you get less info; getEnv()->envi().fail();
        throw ModelInconsistent(getEnv()->envi(), call.loc(), oss.str());
      }
    }
  }

  if (_satModel.getClauseCount() == 0 && _satModel.getLiteralCount() == 0) {
    Solns2Out* out = getSolns2Out();
    out->evalStatus(SolverInstance::SAT);
  }
}

void SATSolverInstance::printCompilationStatistics() {
  EnvI& env = getEnv()->envi();
  std::ios oldState(nullptr);
  oldState.copyfmt(env.outstream);

  env.outstream.setf(std::ios::fixed);
  env.outstream.precision(4);

  // TODO could have a look at Printer
  env.outstream << "%%%mzn-stat: processFlatZincTime=" << _processFlatZincTime << std::endl;
  env.outstream << "%%%mzn-stat: bimanderCount=" << _statBimanderCount << std::endl;
  env.outstream << "%%%mzn-stat: bimanderTotalN=" << _statBimanderTotalN << std::endl;
  env.outstream << "%%%mzn-stat: bimanderTotalM=" << _statBimanderTotalM << std::endl;
  env.outstream << "%%%mzn-stat: bimanderTotalOffset=" << _statBimanderTotalOffset << std::endl;
  env.outstream << "%%%mzn-stat: bimanderTotalAbsoluteBalance="
                << std::accumulate(_satModel.encoder.stats->totalBitBalances.begin(),
                                   _satModel.encoder.stats->totalBitBalances.end(), 0,
                                   [](size_t sum, int val) { return sum + std::fabs(val); })
                << std::endl;

  env.outstream << "%%%mzn-stat: nVariables=" << _satModel.getLiteralCount() << std::endl;
  env.outstream << "%%%mzn-stat: nClauses=" << _satModel.getClauseCount() << std::endl;
  env.outstream << "%%%mzn-stat: nClauseVariables=" << _satModel.getClauseLiteralCount()
                << std::endl;

  env.outstream.copyfmt(oldState);
}

void SATSolverInstance::printStatistics() {
  EnvI& env = getEnv()->envi();
  std::ios oldState(nullptr);
  oldState.copyfmt(env.outstream);

  env.outstream.setf(std::ios::fixed);
  env.outstream.precision(4);
  env.outstream << "%%%mzn-stat: solveTime=" << _solveTime << std::endl;
  env.outstream.copyfmt(oldState);
}

SolverInstance::Status SATSolverInstance::solve() {
  // Get the options
  auto& opt = static_cast<SATSolverOptions&>(*_options);

  Solns2Out* out = getSolns2Out();

  // If model was decided during compilation
  if (out->status == SolverInstance::UNSAT) {
    return out->status;
  }
  if (out->status == SolverInstance::SAT) {
    SATSolns2Out s2o = SATSolns2Out(out, _fzn, _satModel, opt.allSolutions,
                                    opt.intermediateSolutions, opt.verbose);
    s2o.sendSolutionToOut(SATStatus::OPTIMAL);
    if (opt.allSolutions) {  // search is complete
      out->evalStatus(SolverInstance::OPT);
    }
    return out->status;
  }

  string file_sat;
  FileUtils::TmpDir* tmpdir = nullptr;

  int exitStatus = -1;

  file_sat = opt.outputDimacs.empty() ? (new FileUtils::TmpDir())->name() + "/model.dimacs"
                                      : opt.outputDimacs;
  std::ofstream outfile(file_sat);

  // Get solver input
  _satModel.dimacsToOut(outfile, opt.solverInputFormat);
  outfile.close();

  // We only check here for a (Max)SAT solver so that at least the solver input
  // will be prepared in any case
  if (opt.solver.empty()) {
    if (tmpdir != nullptr) {
      delete tmpdir;
      tmpdir = nullptr;
    }
    outfile.close();
    throw InternalError("Provide a (Max)SAT solver with --sat-solver or --max-sat-solver.");
  }

  // Get solver command line invocation
  vector<string> cmd_line;

  // Split up solver and flags
  std::string delim = " ";
  auto start = 0U;
  auto end = opt.solver.find(delim);
  while (end != std::string::npos) {
    cmd_line.push_back(opt.solver.substr(start, end - start));
    start = end + delim.length();
    end = opt.solver.find(delim, start);
  }
  cmd_line.push_back(opt.solver.substr(start, end));
  cmd_line.push_back(file_sat);

  if (!opt.extraSolverArgs.empty()) {
    cmd_line.push_back(opt.extraSolverArgs);
  }

  SATSolns2Out s2o =
      SATSolns2Out(out, _fzn, _satModel, opt.allSolutions, opt.intermediateSolutions, opt.verbose);
  do {
    // Every time we find a solution, make it illegal for the next run
    if (out->status == SolverInstance::Status::SAT) {
      // if we have a new solution, make it illegal for the next run
      vector<bool> last_solution = s2o.getLastSolution();
      bool illegal_solution_added =
          _satModel.addIllegalSolution(_fzn, out->getEnv()->envi(), last_solution);
      if (!illegal_solution_added) {
        out->evalStatus(SolverInstance::Status::OPT);
        break;
      }
      outfile.open(file_sat);
      _satModel.dimacsToOut(outfile, opt.solverInputFormat);
      outfile.flush();
      outfile.close();
    }

    // Record flatzinc processing time once
    _processFlatZincTime =
        _processFlatZincTime == 0.0 ? _processFlatZincTimer.s() : _processFlatZincTime;

    if (opt.solverStatistics) {
      printCompilationStatistics();
    }

    // last argument means we interrupt directly with SIGTERM at timeout, no
    // preliminary SIGINT
    // TODO reduce solverTimeLimitMs by previous run time?
    Process<SATSolns2Out> proc(cmd_line, &s2o, opt.solverTimeLimitMs, false);

    // TODO what to do with solve time for all solutions? For now, aggregate
    Timer solve_timer;
    exitStatus = proc.run();
    _solveTime += solve_timer.s();

    // Declare output if solving process completed successfully (exitStatus 10
    // is SAT, 20 means UNSAT for some SAT solvers, 30 also means OPTIMAL for
    // some MaxSAT solvers)
    exitStatus = exitStatus == 10 || exitStatus == 20 || exitStatus == 30 ? 0 : exitStatus;

    s2o.sendSolutionToOut();
    // if (exitStatus == 0) {
    //   s2o.send_solution_to_out();
    // } else {
    //   assert(false);
    //   // error of some kind (at least unexpected exit status)
    //   break;
    // }

  } while (opt.allSolutions && out->status == SolverInstance::Status::SAT);

  if (opt.solverStatistics) {
    printStatistics();
  }

  return exitStatus == 0 ? out->status : Status::ERROR;
}

// // Unused
// Expression* SATSolverInstance::getSolutionValue(Id* id) {
//   assert(false);
//   return nullptr;
// }

}  // namespace MiniZinc
