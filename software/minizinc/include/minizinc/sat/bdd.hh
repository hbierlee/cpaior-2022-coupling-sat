#include <minizinc/ast.hh>
#include <minizinc/sat/at_most1.hh>

namespace MiniZinc {
Expression* b_build_bdd_le(EnvI& env, Call* call);
Expression* b_build_bdd_eq(EnvI& env, Call* call);
Expression* b_build_bdd_ne(EnvI& env, Call* call);
};  // namespace MiniZinc
