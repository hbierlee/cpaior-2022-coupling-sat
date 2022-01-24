#include <minizinc/ast.hh>

namespace MiniZinc {
VarDecl* add_bool_var(EnvI& env);
Call* make_bool_clause(std::vector<Expression*> pos, std::vector<Expression*> neg);
};  // namespace MiniZinc
