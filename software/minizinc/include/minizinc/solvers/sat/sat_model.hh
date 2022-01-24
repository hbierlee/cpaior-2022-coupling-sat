#ifndef __MINIZINC_SAT_MODEL_HH__
#define __MINIZINC_SAT_MODEL_HH__

#include <minizinc/ast.hh>
#include <minizinc/eval_par.hh>
#include <minizinc/model.hh>

#include <iterator>
#include <map>
#include <pblib/pb2cnf.h>
#include <pblib/pbconstraint.h>
#include <vector>

namespace MiniZinc {

class SATModel {
protected:
  // Inner class to provide two-way mapping between CNFlatZinc and DIMACS
  // literals, which are represented as positive integers.
  class SATLiterals : public AuxVarManager {
  private:
    std::unordered_map<const VarDecl*, int32_t> _varMap;
    std::unordered_map<int32_t, const VarDecl*> _declMap;

  public:
    SATLiterals() : AuxVarManager(1) {}
    int32_t declToVar(const VarDecl* vdecl, int32_t dimacs_id = 0);
    int32_t newVar();
    int32_t getVar(const VarDecl* decl) const;
    const VarDecl* getDecl(int32_t var);

    int32_t max() const { return const_cast<SATLiterals*>(this)->getBiggestReturnedAuxVar(); }
  } _literals;

  // TODO: Correctly handle the UNSAT state that can be set here
  class SATClauses : public ClauseDatabase {
    using database = std::vector<std::vector<int32_t>>;
    using const_iterator = database::const_iterator;

  protected:
    database _clauses;
    void addClauseIntern(std::vector<int32_t> const& clause) override {
      _clauses.push_back(clause);
    }

  public:
    SATClauses(PBConfig config) : ClauseDatabase(config) {}
    ~SATClauses() override = default;

    size_t size() const { return _clauses.size(); }
    bool empty() const { return _clauses.empty(); }
    const_iterator begin() const { return _clauses.cbegin(); }
    const_iterator end() const { return _clauses.cend(); }
  } _clauses;

  Env& _env;

public:
  PB2CNF encoder;
  enum SATObjective { SAT = 1, MINSAT = 2, MAXSAT = 3 };
  enum SolverInputFormat { DIMACS_CNF = 0, DIMACS_WCNF = 1 };
  enum PB_CONSTRAINT_CONTEXT {
    ROOT = 0,
    IMP = 1,
    REIF = 2,
  };

  SATModel(Env& env, PBConfig config)
      : _clauses(config), _env(env), encoder(config), _pb_config(config){};
  bool addClause(IntVal weight);
  bool addClause(ArrayLit* positive_vars, ArrayLit* negative_vars,
                 IntVal weight = IntVal::infinity(), bool is_solve_minimize = false);
  template <PBLib::Comparator comp>
  bool addPbConstraint(ArrayLit* weights, ArrayLit* literals, IntVal c, Expression* reif = nullptr,
                       PB_CONSTRAINT_CONTEXT context = ROOT);
  // Returns whether an illegal solution was added
  bool addIllegalSolution(Model* fzn, EnvI& envi, const std::vector<bool>& solution);
  void addSolve(SolveI::SolveType st, const Expression* e, SolverInputFormat solverInputFormat);
  void addNegation(const Call& call);
  int32_t getLiteralCount();
  int32_t getLiteral(const VarDecl* vd) const;
  SATModel::SATObjective getObjective();
  void dimacsToOut(std::ostream& os, SolverInputFormat solver_input_format) const;
  long getObjectiveValue(long cost) const;
  size_t getClauseCount() const;
  int32_t getClauseLiteralCount() const;
  std::shared_ptr<PBConfigClass> _pb_config;

private:
  std::vector<std::vector<int32_t>> _softClauses;
  std::vector<long> _weights;

  SATModel::SATObjective _objective;
  long _baseWeight = 0;
  bool _is_solve_minimize = false;

  long getSumOfWeights() const;
};

template <PBLib::Comparator comp>
bool SATModel::addPbConstraint(ArrayLit* weights, ArrayLit* literals, IntVal c, Expression* reif,
                               SATModel::PB_CONSTRAINT_CONTEXT context) {
  // in case of count (amk/amo) constraint, weights == nullptr (and every weight is implicitly 1)
  assert(weights == nullptr || weights->size() == literals->size());
  int64_t res = c.toInt();

  std::vector<PBLib::WeightedLit> wlits;
  wlits.reserve(literals->size());

  for (size_t i = 0; i < literals->size(); ++i) {
    int64_t weight = weights ? eval_int(_env.envi(), (*weights)[i]).toInt() : 1;

    if (weight == 0) {
      continue;
    }
    if (auto* decl = follow_id_to_decl((*literals)[i])->dynamicCast<VarDecl>()) {
      int32_t lit = _literals.getVar(decl);
      if (lit == 0) {
        lit = _literals.declToVar(decl);
      }
      wlits.emplace_back(lit, weight);
    } else {
      auto* par = (*literals)[i]->cast<BoolLit>();
      res -= par->v() * weight;
      continue;
    }
  }

  PBLib::PBConstraint cons(wlits, comp, res);
  if (context != ROOT) {
    int32_t reif_var;
    if (reif->isa<VarDecl>()) {
      reif_var = _literals.getVar(reif->cast<VarDecl>());
      if (reif_var == 0) {
        reif_var = _literals.declToVar(reif->cast<VarDecl>());
      }
    } else if (reif->type().isPar()) {
      auto* r = reif->cast<BoolLit>();

      if (r->v()) {
        context = SATModel::PB_CONSTRAINT_CONTEXT::ROOT;
      } else if (context == SATModel::PB_CONSTRAINT_CONTEXT::IMP) {
        return true;  // false conditional -> true (so skip encoding)
      } else if (context == SATModel::PB_CONSTRAINT_CONTEXT::REIF) {
        // TODO we need a NE comparator in PBLib
        reif_var = _literals.newVar();
        _clauses.addClause(-reif_var);
      }
    }

    if (context == IMP) {
      cons.addConditional(reif_var);
    } else if (context == REIF) {
      cons.setReification(reif_var);
    }
  }

  // cons.print(true);
  encoder.encode(cons, _clauses, _literals);
  if (_clauses.isSetToUnsat() && (context == IMP || context == REIF)) {
    _clauses.deleteIsSetToUnsatFlag();
  }

  return context == REIF || context == IMP || !_clauses.isSetToUnsat();
}

}  // namespace MiniZinc
#endif
