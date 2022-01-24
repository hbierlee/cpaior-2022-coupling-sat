#include <minizinc/ast.hh>
#include <minizinc/sat/networks.hh>

namespace MiniZinc {
std::vector<Expression*> build_merge_network_direct(EnvI& env, std::vector<Expression*>& as,
                                                    std::vector<Expression*>& bs,
                                                    SortingNetworkComparator comparator, size_t c,
                                                    Expression* reif);
std::vector<Expression*> build_merge_network_recursive(EnvI& env, std::vector<Expression*>& as,
                                                       std::vector<Expression*>& bs,
                                                       SortingNetworkComparator comparator,
                                                       size_t c, Expression* reif, double lambda);

std::vector<Expression*> build_merge_network_mixed(EnvI& env, std::vector<Expression*>& as,
                                                   std::vector<Expression*>& bs,
                                                   SortingNetworkComparator comparator, size_t c,
                                                   Expression* reif, double lambda);

std::pair<size_t, size_t> calculate_recursive_merge_network(size_t a, size_t b, size_t c);
}  // namespace MiniZinc
