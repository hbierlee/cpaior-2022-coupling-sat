#include <minizinc/ast.hh>
#include <minizinc/sat/merge_networks.hh>
#include <minizinc/sat/networks.hh>

namespace MiniZinc {
std::vector<Expression*> build_two_comparator(EnvI& env, Expression* x1, Expression* x2,
                                              SortingNetworkComparator comparator, size_t c,
                                              Expression* reif);
std::vector<Expression*> build_sorting_network_recursive(EnvI& env, std::vector<Expression*> xs,
                                                         SortingNetworkComparator comparator,
                                                         size_t c, Expression* reif, double lambda);

std::vector<Expression*> build_sorting_network_direct(EnvI& env, std::vector<Expression*> xs,
                                                      SortingNetworkComparator comparator, size_t c,
                                                      Expression* reif);

std::vector<Expression*> build_sorting_network_mixed(EnvI& env, std::vector<Expression*> xs,
                                                     SortingNetworkComparator comparator, size_t c,
                                                     Expression* reif, double lambda);

std::pair<size_t, size_t> calculate_two_comparator_network(size_t a, size_t b, size_t c);
}  // namespace MiniZinc
