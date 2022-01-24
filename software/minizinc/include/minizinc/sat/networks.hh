#pragma once
#include <minizinc/ast.hh>

// TODO how to share this BDD by making it available from util.cpp/hh
namespace MiniZinc {

enum SortingNetworkComparator { LE = 0, EQ = 1, GE = 2 };
Expression* b_build_sorting_network(EnvI& env, Call* call);

double formula_value(std::pair<size_t, size_t> form, double lambda);
};  // namespace MiniZinc
