#include <minizinc/ast.hh>

namespace MiniZinc {
// Ignore weird clang-tidy redundant definition errors
Expression* b_at_most1_pairwise(EnvI& env, Call* call);  // NOLINT
Expression* b_at_most1_bimander(EnvI& env, Call* call);  // NOLINT
Expression* b_at_most1_mimander(EnvI& env, Call* call);  // NOLINT
};                                                       // namespace MiniZinc
