#define __STDCPP_WANT_MATH_SPEC_FUNCS__ 1
#include <minizinc/sat/networks.hh>
#include <minizinc/sat/sorting_networks.hh>
#include <minizinc/sat/util.hh>

#include "minizinc/ast.hh"
#include "minizinc/flatten_internal.hh"

#include <cmath>
#include <map>
#include <vector>

namespace MiniZinc {

#if defined __APPLE__ || defined _WIN32
size_t binom(size_t n, size_t k) {
  return std::tgamma(n + 1) / (std::tgamma(n - k + 1) * std::tgamma(k + 1));
}
#else
size_t binom(size_t n, size_t k) {  // std::beta is c++2017
  return 1 / ((n + 1) * (size_t)std::beta(n - k + 1, k + 1));
}
#endif

static std::map<std::pair<size_t, size_t>, std::pair<size_t, size_t>> recursive_sorter_values;

// TODO totally experimental, not for any use yet
std::vector<Expression*> build_binary_two_comparator(EnvI& env, Expression* b0, Expression* b1,
                                                     SortingNetworkComparator comparator, size_t c,
                                                     Expression* reif) {
  Id* y1 = add_bool_var(env)->id();
  Id* y2 = add_bool_var(env)->id();
  Id* y3 = add_bool_var(env)->id();

  // b0 -> y1
  env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({y1}, {b0})));
  // b1 -> y2 /\ y3
  env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({y1, y2}, {b1})));
  // b0 /\ b1 -> y1 /\ y2 /\ y3
  env.flatAddItem(
      new ConstraintI(Location().introduce(), make_bool_clause({y1, y2, y3}, {b0, b1})));

  // not b0 -> not y3
  env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({b0}, {y3})));
  // not b1 -> not y2 /\ not y3
  env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({b1}, {y2, y3})));
  // not b0 /\ not b1 -> not y1 /\ not y2 /\ not y3
  env.flatAddItem(
      new ConstraintI(Location().introduce(), make_bool_clause({b0, b1}, {y1, y2, y3})));

  return {y1, y2, y3};
}

// TODO this could be all moved to a 'sorting_network' mzn predicate
// x1 x2 y1 y2
//  0  0  0  0
//  0  1  1  0
//  1  0  1  0
//  1  1  1  1
std::vector<Expression*> build_two_comparator(EnvI& env, Expression* x1, Expression* x2,
                                              SortingNetworkComparator comparator, size_t c,
                                              Expression* reif) {
  // TODO reserve end vector to size 2?
  // TODO unified way to do this
  Id* y1 = add_bool_var(env)->id();

  if (comparator == LE || comparator == EQ) {
    env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({y1}, {x1})));
    env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({y1}, {x2})));
  }

  if (comparator == GE || comparator == EQ) {
    env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({x1, x2}, {y1})));
  }

  if (c == 0) {
    assert(false &&
           "Maybe this should be allowed, but it'd be a weird case "
           "and should be investigated");
    return {};
  }
  if (c == 1) {
    // if (reif == constants().lit_true) {
    //   // env.flatAddItem(new ConstraintI(Location().introduce(),
    //   //                                  make_bool_clause({}, {x1, x2})));
    // } else {
    //   // (not x1 /\ not x2) -> not reif => not reif \/ not x1 \/ not x2
    //   // env.flatAddItem(new ConstraintI(Location().introduce(),
    //   //                                  make_bool_clause({}, {reif, x1,
    //   x2})));
    // }
    return {y1};
  }
  Id* y2 = add_bool_var(env)->id();

  if (comparator == LE || comparator == EQ) {
    env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({y2}, {x1, x2})));
  }

  if (comparator == GE || comparator == EQ) {
    env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({x1}, {y2})));
    env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({x2}, {y2})));
  }

  return {y1, y2};
}

std::vector<Expression*> build_sorting_network_recursive(EnvI& env, std::vector<Expression*> xs,
                                                         SortingNetworkComparator comparator,
                                                         size_t c, Expression* reif,
                                                         double lambda) {
  size_t n = xs.size();

  if (n == 1) {
    return xs;
  }
  if (n == 2) {
    return build_two_comparator(env, xs[0], xs[1], comparator, c, reif);
  }  // TODO make parameter
  size_t l = n / 2;

  std::vector<Expression*> xs_left;
  for (size_t i = 0; i < l; ++i) {
    xs_left.push_back(xs[i]);
  }

  std::vector<Expression*> xs_right;
  for (size_t i = l; i < n; ++i) {
    xs_right.push_back(xs[i]);
  }

  std::vector<Expression*> z_left =
      build_sorting_network_mixed(env, xs_left, comparator, c, reif, lambda);
  std::vector<Expression*> z_right =
      build_sorting_network_mixed(env, xs_right, comparator, c, reif, lambda);

  assert(z_left.size() == std::min(n, std::min(l, c)));
  assert(z_right.size() == std::min(n, std::min(n - l, c)));

  return build_merge_network_mixed(env, z_left, z_right, comparator, c, reif, lambda);
}

std::vector<Expression*> build_sorting_network_direct(EnvI& env, std::vector<Expression*> xs,
                                                      SortingNetworkComparator comparator, size_t c,
                                                      Expression* reif) {
  size_t n = xs.size();
  c = std::min(n, c);

  std::vector<Expression*> ys;
  for (size_t k = 0; k < c; ++k) {
    Expression* y_k = add_bool_var(env)->id();
    ys.push_back(y_k);
  }

  // TODO limit to pow(2,c) for LE (and start higher than two for GE?)
  int bitmask = 1;
  while (bitmask < std::pow(2, n)) {
    std::vector<Expression*> xis;

    for (size_t i = 0; i < n; ++i) {
      if ((1 << i) & bitmask) {
        xis.push_back(xs[i]);
      }
    }

    if (comparator == SortingNetworkComparator::LE || comparator == SortingNetworkComparator::EQ) {
      // TODO might be more clear to move this one up, specify case below
      // explicitly as n-k
      size_t k = xis.size() - 1;

      if (k < c) {
        // /\ x_i -> y_k
        env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({ys[k]}, xis)));
      } else {
        // /\ x_i -> false => \/ not x_i
        // /\ x_i -> not r => \/ not x_i \/ not r
        // xis.push_back(reif);
        // env.flatAddItem(
        //     new ConstraintI(Location().introduce(), make_bool_clause({},
        //     xis)));
        // xis.pop_back();
      }
    }

    if (comparator == SortingNetworkComparator::GE || comparator == SortingNetworkComparator::EQ) {
      size_t k = n - xis.size();
      if (k < c) {
        // /\ not x_i -> not y_(n-k) (=> \/ x_i \/ y_(n-k))
        env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause(xis, {ys[k]})));
      }  // else: /\ not x_i -> not false => /\ not x_i -> true => true
      // TODO add this one (if reif, can be omitted for fixed r)
      // else: /\ not x_i -> r => \/ x_i \/ r ?
    }

    bitmask++;
  }

  assert(ys.size() == c);
  return ys;
}

std::pair<size_t, size_t> calculate_two_comparator_network(size_t a, size_t b, size_t c) {
  return c == 1 ? std::make_pair(1, 3) : std::make_pair(2, 6);
}

std::pair<size_t, size_t> calculate_direct_sorting_network(size_t n, size_t c) {
  if (n == c) {
    return std::make_pair(n, std::pow(2, n) - 1);
  }
  size_t clauses = 0;
  for (size_t i = 1; i <= c; ++i) {
    clauses += binom(n, i);
  }
  return std::make_pair(c, clauses);
}

std::pair<size_t, size_t> calculate_recursive_sorting_network(size_t n, size_t c) {
  if (n == 1) {
    return std::make_pair(0, 0);
  }
  if (n == 2) {
    return std::make_pair(2, 3);
  }

  auto entry = recursive_sorter_values.find(std::pair<size_t, size_t>(n, c));

  if (entry != recursive_sorter_values.end()) {
    return entry->second;
  }
  auto half = calculate_recursive_sorting_network(n / 2, c);
  auto curr = calculate_recursive_merge_network(n / 2, n / 2, c);
  auto res = std::make_pair(2 * half.first + curr.first, 2 * half.second + curr.second);
  recursive_sorter_values[std::pair<size_t, size_t>(n, c)] = res;
  return res;
}

std::vector<Expression*> build_sorting_network_mixed(EnvI& env, std::vector<Expression*> xs,
                                                     SortingNetworkComparator comparator, size_t c,
                                                     Expression* reif, double lambda) {
  c = std::min(c, xs.size());  // For the calculations, we should keep c <= n
  if (lambda == -1) {
    return build_sorting_network_direct(env, xs, comparator, c, reif);
  }
  if (lambda == -2) {
    return build_sorting_network_recursive(env, xs, comparator, c, reif, lambda);
  }

  size_t n = xs.size();

  auto direct_formula = calculate_direct_sorting_network(n, c);
  auto recursive_formula = calculate_recursive_sorting_network(n, c);

  double direct = formula_value(direct_formula, lambda);
  double recursive = formula_value(recursive_formula, lambda);

  if (direct <= recursive) {
    return build_sorting_network_direct(env, xs, comparator, c, reif);
  }
  return build_sorting_network_recursive(env, xs, comparator, c, reif, lambda);
}
}  // namespace MiniZinc
