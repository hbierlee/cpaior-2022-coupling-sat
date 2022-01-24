#include <minizinc/solvers/sat/sat_solreader.hh>

#include "minizinc/ast.hh"
#include "minizinc/aststring.hh"
#include "minizinc/eval_par.hh"
#include "minizinc/gc.hh"
#include "minizinc/solver_instance.hh"
#include "minizinc/solvers/sat/sat_model.hh"
#include "minizinc/solvers/sat/sat_solparser.hh"
#include "minizinc/solvers/sat/sat_solverinstance.hh"
#include "minizinc/values.hh"

#include <cstdlib>
#include <fstream>
#include <ios>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace MiniZinc {

// Receives solver output (in chunks)
bool SATSolns2Out::feedRawDataChunk(const char* data) {
  // TODO [?] in nl_solreader, they prefix every line with a %.. should we do
  // that here too?
  getLog() << data;

  int old_c = _lexer.cost();
  _lexer.parseData(data);
  int new_c = _lexer.cost();

  if (_intermediateSolutions && old_c != new_c) {
    sendSolutionToOut();
  }

  return true;
}

Expression* SATSolns2Out::getExpressionValue(Expression* e) {
  // Follow indirection if the vdecl has a RHS
  Expression* followed_expression = follow_id_to_value(e);

  if (followed_expression->type().isPar()) {
    // Expression or its RHS is a literal
    return follow_id_to_value(e);
  }
  auto* followed_vdecl = follow_id_to_decl(e)->cast<VarDecl>();

  // Solve item
  if (followed_vdecl->type().isint() &&
      follow_id_to_decl(_fzn->solveItem()->e()) == followed_vdecl &&
      (_satModel.getObjective() == SATModel::SATObjective::MINSAT ||
       _satModel.getObjective() == SATModel::SATObjective::MAXSAT)) {
    // TODO should be fixed better, but cost = -1 if no solution has
    // been found (or if the solver didn't run at all if the model was
    // decided during compilation
    IntLit* value = IntLit::a(IntVal(_satModel.getObjectiveValue(std::max(_lexer.cost(), 0))));
    return value;
  }
  if (followed_vdecl->type().isint()) {  // free int var
    return followed_vdecl;
  }
  if (followed_vdecl->type().isbool()) {  // bool var decl
    if (followed_vdecl->e() != nullptr &&
        followed_vdecl->e()->type().isPar()) {  // value in FlatZinc
      Expression* value = follow_id_to_value(followed_vdecl);
      return value;
    }
    long literal = _satModel.getLiteral(followed_vdecl);

    if (literal != 0) {  // value in SAT model
      return _lexer.getLiteralValue(literal) ? Constants::constants().literalTrue
                                             : Constants::constants().literalFalse;
    }
    return followed_vdecl;
  }
  assert(false && "SAT interface is unable to handle output variable");
  return nullptr;
}

void SATSolns2Out::assignOutputVariables() {
  GCLock lock;

  // Find solutions (if any) for each output var and send them to out
  for (auto& it : _fzn->vardecls()) {
    if (!it.removed()) {
      VarDecl* vdecl = it.e();

      if (!vdecl->ann().isEmpty()) {  // TODO unnecessary?
        if (vdecl->ann().contains(Constants::constants().ann.output_var)) {
          Expression* value = getExpressionValue(vdecl);
          _out->findOutputVar(vdecl->id()->str()).first->e(value);

          if (value->isa<VarDecl>()) {
            _freeVariables.push_back(value->cast<VarDecl>());
          }

        } else if (vdecl->ann().containsCall(Constants::constants().ann.output_array)) {
          assert(vdecl->e());
          ArrayLit* al = eval_array_lit(_out->getEnv()->envi(), vdecl->e());

          // Get dimensions (TODO maybe there's a better way like in
          // soln2out.cpp but couldn't figure out what was happening there)
          Call* c = vdecl->ann().getCall(Constants::constants().ann.output_array);
          ArrayLit* output_array_annotation = eval_array_lit(_out->getEnv()->envi(), c->arg(0));

          std::vector<std::pair<int, int>> dims;
          for (size_t i = 0; i < output_array_annotation->size(); ++i) {
            IntSetVal* index_set =
                eval_intset(_out->getEnv()->envi(), (*output_array_annotation)[i]);
            dims.emplace_back(index_set->min().toInt(), index_set->max().toInt());
          }

          std::vector<Expression*> array_elements;
          for (int i = 0; i < al->size(); ++i) {
            Expression* value = getExpressionValue(follow_id_to_decl((*al)[i]));

            if (value->isa<VarDecl>() &&
                !value->ann().contains(Constants::constants().ann.output_var)) {
              _freeVariables.push_back(value->cast<VarDecl>());
            } else {
              array_elements.push_back(value);
            }
          }

          auto* nlit = new ArrayLit(Location().introduce(), array_elements, dims);
          _out->findOutputVar(vdecl->id()->str()).first->e(nlit);
        }
      }
    } else {
      assert(false && "iterator went over a removed var?");
    }
  }
}

void SATSolns2Out::outputSolution(bool all_solutions, size_t free_variable_index) {
  GCLock lock;
  for (; free_variable_index < _freeVariables.size(); ++free_variable_index) {
    VarDecl* free_var = _freeVariables[free_variable_index];

    if (free_var->type().isbool()) {
      if (all_solutions) {
        free_var->e(Constants::constants().literalTrue);
        outputSolution(all_solutions, free_variable_index + 1);
      }

      free_var->e(Constants::constants().literalFalse);

    } else if (free_var->type().isint()) {
      IntSetVal* domain = free_var->ti()->domain() != nullptr
                              ? eval_intset(_out->getEnv()->envi(), free_var->ti()->domain())
                              : IntSetVal::a(IntVal::minint(), IntVal::maxint());

      if (all_solutions) {
        for (IntVal v = domain->min(); v < domain->max(); ++v) {
          if (domain->contains(v)) {
            free_var->e(IntLit::a(v));
            outputSolution(all_solutions, free_variable_index + 1);
          }
        }
      }

      free_var->e(IntLit::a(domain->max()));
      // output_solution(all_solutions, free_variable_index + 1);

    } else {
      assert(false && "Unexpected non int/bool free variable in model");
    }
  }

  // Assign output variables now that free variables are fixed
  assignOutputVariables();

  // Final solution after all free var version have been output
  _out->evalOutput();
  if (_lexer.status() == SATStatus::OPTIMAL) {
    _out->evalStatus(SolverInstance::Status::SAT);  // ------
  }
}

void SATSolns2Out::sendSolutionToOut() { return sendSolutionToOut(_lexer.status()); }

void SATSolns2Out::sendSolutionToOut(SATStatus status) {
  switch (status) {
    case SATStatus::UNCERTAIN:
    case SATStatus::OPTIMAL: {
      _out->declNewOutput();

      _freeVariables.clear();
      assert(_lexer.solution().size() == _satModel.getLiteralCount());

      // assign solver solution and collect free vars
      assignOutputVariables();

      outputSolution(_allSolutions);

      _out->evalOutput();

      // TODO we should reuse SolverInstance::Status
      // If this is an optimization function, output optimal if optimal
      if (_satModel.getObjective() == SATModel::SATObjective::MINSAT ||
          _satModel.getObjective() == SATModel::SATObjective::MAXSAT) {
        if (status == SATStatus::OPTIMAL) {
          _out->evalStatus(SolverInstance::Status::OPT);  // =====
        }
      }

      // clear value assigned to free variables
      for (auto* e : _freeVariables) {
        e->e(nullptr);
      }

      break;
    }
    case SATStatus::UNSATISFIABLE: {
      if (_lexer.cost() == -1) {
        // we never saw a solution
        _out->declNewOutput();
        _out->evalStatus(SolverInstance::Status::UNSAT);
      } else {
        // we saw at least one solution, and now search is complete
        _out->declNewOutput();
        _out->evalStatus(SolverInstance::Status::OPT);
      }
      break;
    }
    case SATStatus::UNKNOWN:
      assert(_lexer.cost() == -1);
      // solution should be all-false (default values)
      assert(std::find(_lexer.solution().begin(), _lexer.solution().end(), true) ==
             _lexer.solution().end());
      // TODO is this timeout scenario? should we declare some output?
      break;
  }
}

ostream& SATSolns2Out::getLog() { return _verbose ? _out->getLog() : _dummyStream; }
}  // namespace MiniZinc
