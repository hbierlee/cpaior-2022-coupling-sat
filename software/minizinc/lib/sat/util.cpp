#include <minizinc/ast.hh>

#include "minizinc/flatten_internal.hh"

namespace MiniZinc {

// TODO maybe only return Id
VarDecl* add_bool_var(EnvI& env) {
  auto* ti = new TypeInst(Location().introduce(), Type::varbool());
  auto* newVar = new VarDecl(Location().introduce(), ti, env.genId());
  newVar->flat(newVar);
  env.flatAddItem(new VarDeclI(Location().introduce(), newVar));
  return newVar;
}

Call* make_bool_clause(std::vector<Expression*> pos, std::vector<Expression*> neg) {
  auto* positives = new ArrayLit(Location().introduce(), pos);
  auto* negatives = new ArrayLit(Location().introduce(), neg);
  positives->type(Type::varbool(1));
  negatives->type(Type::varbool(1));

  Call* bool_clause = new Call(Location().introduce(), Constants::constants().ids.bool_clause,
                               {positives, negatives});
  bool_clause->type(Type::varbool());

  return bool_clause;
}

};  // namespace MiniZinc
