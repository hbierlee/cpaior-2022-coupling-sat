/**
 *  A SAT (CNF) model representation.
 *  The purpose of this file is to interface CNFlatZinc with (W)DIMACS format
 */
#include "minizinc/solvers/sat/sat_model.hh"

#include "minizinc/ast.hh"
#include "minizinc/flatten_internal.hh"
#include "minizinc/solvers/sat/sat_solverinstance.hh"
#include "minizinc/values.hh"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdlib>
#include <iterator>
#include <numeric>
#include <string>
#include <utility>
#include <vector>

namespace MiniZinc {

int32_t SATModel::SATLiterals::declToVar(const VarDecl* vdecl, int32_t dimacs_id) {
  int32_t lit = dimacs_id;
  if (lit == 0) {
    lit = getVariable();
  }
  assert(lit != 0);

  auto res = _varMap.emplace(vdecl, lit);
  assert(res.second);  // Insertion should be successful;

  // If we just inserted a new literal that wasn't a negation of a previous
  // literal, then add its reverse mapping
  if (dimacs_id != 0) {
    _declMap.insert(std::make_pair(lit, vdecl));
  }

  return lit;
}

int32_t SATModel::SATLiterals::newVar() { return getVariable(); }

int32_t SATModel::SATLiterals::getVar(const VarDecl* decl) const {
  auto dimacs = _varMap.find(decl);
  return dimacs != _varMap.end() ? dimacs->second : 0;
}

const VarDecl* SATModel::SATLiterals::getDecl(int32_t var) {
  auto it = _declMap.find(var);
  assert(it != _declMap.end());
  return it->second;
}

void SATModel::addNegation(const Call& call) {
  auto* lhs = follow_id_to_decl(call.arg(0))->cast<VarDecl>();
  auto* rhs = follow_id_to_decl(call.arg(1))->cast<VarDecl>();

  // *_dimacs = 0 if literal hasn't been added before (and 0 in C++ is falsey)
  int32_t lhs_dimacs = getLiteral(lhs);
  int32_t rhs_dimacs = getLiteral(rhs);

  // TODO fixed vars have already been taking care off in MiniZinc, but we could
  // also simply add them as unit clauses (e.g., bool_not(p_i,true) -> -i 0).
  if (lhs_dimacs != 0 && rhs_dimacs != 0) {
    // Can't use `(std::vector<Expression *>) {call.arg(0), call.arg(1)}` on
    // windows (Triggers error "a parenthesized type followed by an initializer
    // list is a non-standard explicit type conversion syntax")
    std::vector<Expression*> lhs_array_elements = {call.arg(0), call.arg(1)};
    auto* al_vars = new ArrayLit(Location().introduce(), lhs_array_elements);

    std::vector<Expression*> rhs_array_elements = {};
    auto* al_empty = new ArrayLit(Location().introduce(), rhs_array_elements);

    // constrain negation
    addClause(al_vars, al_empty);  // can't be both true
    addClause(al_empty, al_vars);  // can't be both false
  } else if (lhs_dimacs != 0) {    // rhs unknown
    _literals.declToVar(rhs, -lhs_dimacs);
  } else if (rhs_dimacs != 0) {
    _literals.declToVar(lhs, -rhs_dimacs);
  } else {  // should be rare?
    // TODO wonder if it's maybe better to add the lower idn one first? Although
    // adding lhs first should also accomplish this
    lhs_dimacs = _literals.declToVar(lhs);
    _literals.declToVar(rhs, -lhs_dimacs);
  }
}

void add_illegal_solution_var(std::vector<int32_t>& dimacs_clause, int32_t var,
                              const std::vector<bool>& solution) {
  if (var != 0) {
    int32_t var_abs = abs(var);  // we ignore the view
    int32_t var_assignment = solution[var_abs - 1] ? -var_abs : var_abs;
    // Avoid tautologies
    if (std::find(dimacs_clause.begin(), dimacs_clause.end(), -var_assignment) ==
        dimacs_clause.end()) {
      dimacs_clause.push_back(var_assignment);
    }
  }
}

bool SATModel::addIllegalSolution(Model* fzn, EnvI& envi, const std::vector<bool>& solution) {
  std::vector<int32_t> dimacs_clause;
  // Add the negation of the assignment of output variables as no-good clause
  for (auto& it : fzn->vardecls()) {
    if (!it.removed()) {
      VarDecl* decl = it.e();
      if (decl->ann().contains(envi.constants.ann.output_var)) {
        add_illegal_solution_var(dimacs_clause, _literals.getVar(decl), solution);
      } else if (decl->ann().containsCall(envi.constants.ann.output_array)) {
        ArrayLit* al = eval_array_lit(envi, decl->e());

        for (int i = 0; i < al->size(); ++i) {
          Expression* al_i = follow_id_to_decl((*al)[i]);
          if (al_i->dynamicCast<VarDecl>() != nullptr &&
              !al_i->ann().contains(envi.constants.ann.output_var)) {
            add_illegal_solution_var(dimacs_clause, _literals.getVar(al_i->cast<VarDecl>()),
                                     solution);
          }
        }
      }
    }
  }

  if (dimacs_clause.empty()) {
    return false;  // no new solution was added
  }
  _clauses.addClause(dimacs_clause);
  return true;
}

bool SATModel::addClause(const IntVal weight) {
  assert(weight.isFinite());
  _baseWeight += weight.toInt();
  return true;
}

bool SATModel::addClause(ArrayLit* positive_vars, ArrayLit* negative_vars, const IntVal weight,
                         bool is_solve_minimize) {
  std::vector<int32_t> dimacs_clause;

  // Create fixed-length vector (that is not pre-filled with zeros)
  size_t number_of_literals = positive_vars->size() + negative_vars->size();
  dimacs_clause.reserve(number_of_literals);

  if (is_solve_minimize) {
    _is_solve_minimize = true;
  }
  for (size_t i = 0; i < number_of_literals; ++i) {
    // Go through all positive/negative pars/vars
    bool is_positive = i < positive_vars->size();
    Expression* e = is_positive ? (*positive_vars)[i] : (*negative_vars)[i - positive_vars->size()];

    if (auto* decl = follow_id_to_decl(e)->dynamicCast<VarDecl>()) {
      // TODO for negative literals, we could map the decl to a negative literal
      // instead of negating the dimacs id after adding.
      assert(weight > 0 &&
             "All variable, non-positive weights should have been handled in sat/optimization.mzn");

      int32_t dimacs_id = _literals.getVar(decl);
      if (dimacs_id == 0) {
        dimacs_id = _literals.declToVar(decl);
      }

      // negate literal if it's one of the negative literals of the clause
      dimacs_id = is_positive ? dimacs_id : -dimacs_id;

      // negate literal of objective if minimizing
      if (_objective == MINSAT && weight.isFinite() && !is_solve_minimize) {
        dimacs_id = -dimacs_id;
      }

      dimacs_clause.push_back(dimacs_id);
    } else if (auto* par_lit = e->dynamicCast<BoolLit>()) {
      // expression is a (possibly negated) par literal
      bool par_lit_val = is_positive ? par_lit->v() : !par_lit->v();
      if (par_lit_val) {
        return true;  // clause contains a false literal -> clause is already SAT so doesn't have to
                      // included
      }
      continue;  // clause contains a false literal -> literal can be removed from clause
    } else {
      assert(false &&
             "Should never happen: CNFlatZinc model contained array literal "
             "with something other than variables or literals.");
    }
  }

  // Empty clause is UNSAT
  if (dimacs_clause.empty()) {
    if (weight.isFinite()) {
      _baseWeight += weight.toInt();  // cost is incurred
    } else {
      return false;  // in case of hard clause, the whole model is UNSAT
    }
  }

  if (weight.isPlusInfinity()) {
    _clauses.addClause(dimacs_clause);
  } else {
    _softClauses.push_back(dimacs_clause);
    _weights.push_back(weight.toInt());
  }

  return true;
}

void SATModel::addSolve(SolveI::SolveType st, const Expression* e,
                        SolverInputFormat solverInputFormat) {
  // We can only have one objective. Prevent override.
  // assert(!m_objective == NULL);

  switch (st) {
    case SolveI::SolveType::ST_SAT: {
      // Satisfy: implemented by minimizing 0 (print n0 for an empty expression
      // graph)
      _objective = SATObjective::SAT;

      // Add dummy clause to be compatible with MaxSAT solvers that refuse to solve models without
      // soft clauses
      if (solverInputFormat == SolverInputFormat::DIMACS_WCNF) {
        _softClauses.push_back((std::vector<int32_t>){});
        _weights.push_back(1);
      }
      return;
    }
    case SolveI::SolveType::ST_MAX: {
      _objective = SATObjective::MAXSAT;
      return;
    }
    case SolveI::SolveType::ST_MIN: {
      _objective = SATObjective::MINSAT;
      return;
    }
    default: {
      throw Error("Unexpected objective");
    }
  }
}

long SATModel::getObjectiveValue(long cost) const {
  assert(cost <= getSumOfWeights());
  long objective_value;
  if (_is_solve_minimize) {
    objective_value = cost;
    assert(_objective == MINSAT);
  } else if (_objective == MAXSAT) {
    objective_value = -cost;
  } else if (_objective == MINSAT) {
    objective_value = cost - getSumOfWeights();
  } else {
    assert(false);
  }
  return objective_value - _baseWeight;
}

int32_t SATModel::getLiteral(const VarDecl* vd) const { return _literals.getVar(vd); }

long SATModel::getSumOfWeights() const {
  return std::accumulate(_weights.begin(), _weights.end(), (long)0);
}

size_t SATModel::getClauseCount() const { return _clauses.size() + _softClauses.size(); }

SATModel::SATObjective SATModel::getObjective() { return _objective; }

void SATModel::dimacsToOut(std::ostream& os, SolverInputFormat solver_input_format) const {
  int32_t max_dimacs_id = _literals.max();
  size_t clause_count = getClauseCount();

  std::string dimacs_type = solver_input_format == SolverInputFormat::DIMACS_CNF ? "cnf" : "wcnf";

  // Hard clauses have weight top and soft clauses have a weight smaller than
  // top. top will always be greater than the sum of the soft clause weights.
  long dimacs_top = getSumOfWeights() + 1;

  // Header comment
  if (solver_input_format == SolverInputFormat::DIMACS_CNF) {
    os << "c A DIMACS CNF model derived from a CNFlatZinc model" << std::endl;
  } else {
    os << "c A DIMACS WCNF model derived from a CNFlatZinc model" << std::endl;
  }

  // Header with model parameters
  os << "p " << dimacs_type << " " << max_dimacs_id << " " << clause_count;
  if (solver_input_format == SolverInputFormat::DIMACS_WCNF) {
    os << " " << dimacs_top;
  }
  os << std::endl << std::endl;

  // Add constraints
  if (!_clauses.empty()) {
    os << "c CONSTRAINTS (hard clause(s))" << std::endl;
    for (auto clause : _clauses) {
      // Add top as weight if wcnf
      if (solver_input_format == SolverInputFormat::DIMACS_WCNF) {
        os << dimacs_top << " ";
      }

      // Add (hard) clauses
      for (int32_t lit : clause) {
        os << lit << " ";
      }

      os << "0" << std::endl;  // mandatory clause delimiter
    }

    os << std::endl;
  }

  // Add objective (even for SAT problems since some MaxSAT solvers otherwise refuse to solve it)
  if (solver_input_format == SolverInputFormat::DIMACS_WCNF) {
    os << "c OBJECTIVE (soft clause(s))" << std::endl;
    for (size_t i = 0; i < _softClauses.size(); i++) {
      std::vector<int32_t> clause = _softClauses[i];

      // Add weights
      if (solver_input_format == SolverInputFormat::DIMACS_WCNF) {
        os << _weights[i] << " ";
      }

      // Add (soft) clauses
      for (int32_t lit : clause) {
        os << lit << " ";
      }

      os << "0" << std::endl;  // mandatory clause delimiter
    }
  }
}

int32_t SATModel::getLiteralCount() { return _literals.max(); }
int32_t SATModel::getClauseLiteralCount() const {
  return accumulate(_clauses.begin(), _clauses.end(), (int32_t)0,
                    [](int32_t acc, std::vector<int32_t> v) { return acc + v.size(); });
}

}  // namespace MiniZinc
