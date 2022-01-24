#include <minizinc/sat/merge_networks.hh>
#include <minizinc/sat/networks.hh>
#include <minizinc/sat/sorting_networks.hh>
#include <minizinc/sat/util.hh>

#include "minizinc/ast.hh"
#include "minizinc/flatten_internal.hh"

#include <map>
#include <vector>

namespace MiniZinc {

static std::map<std::tuple<size_t, size_t, size_t>, std::pair<size_t, size_t>>
    recursive_merger_values;

std::vector<Expression*> build_merge_network_direct(EnvI& env, std::vector<Expression*>& as,
                                                    std::vector<Expression*>& bs,
                                                    SortingNetworkComparator comparator, size_t c,
                                                    Expression* reif) {
  size_t a = as.size();
  size_t b = bs.size();
  size_t n = a + b;
  c = std::min(n, c);

  std::vector<Expression*> ys;
  for (size_t k = 0; k < c; ++k) {
    ys.push_back(add_bool_var(env)->id());
  }

  for (size_t i = 0; i < a; ++i) {
    if (comparator == SortingNetworkComparator::LE || comparator == SortingNetworkComparator::EQ) {
      // a_i -> y_i
      env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({ys[i]}, {as[i]})));
    }
    if (comparator == SortingNetworkComparator::GE || comparator == SortingNetworkComparator::EQ) {
      size_t k = b + i;
      // not a_i -> not y_k
      // TODO possibly redundant check, as it's not in the paper for the LE constraint.
      if (k < c) {
        env.flatAddItem(
            new ConstraintI(Location().introduce(), make_bool_clause({as[i]}, {ys[k]})));
      }
    }
  }

  for (size_t j = 0; j < b; ++j) {
    if (comparator == SortingNetworkComparator::LE || comparator == SortingNetworkComparator::EQ) {
      env.flatAddItem(new ConstraintI(Location().introduce(), make_bool_clause({ys[j]}, {bs[j]})));
    }
    if (comparator == SortingNetworkComparator::GE || comparator == SortingNetworkComparator::EQ) {
      size_t k = a + j;
      // not b_j -> not y_k
      if (k < c) {
        env.flatAddItem(
            new ConstraintI(Location().introduce(), make_bool_clause({bs[j]}, {ys[k]})));
      }
    }
  }

  for (size_t i = 0; i < a; ++i) {
    for (size_t j = 0; j < b; ++j) {
      if (comparator == SortingNetworkComparator::LE ||
          comparator == SortingNetworkComparator::EQ) {
        size_t k = i + j + 1;
        if (k < c) {
          // a_i /\ b_j -> y_[k]
          env.flatAddItem(
              new ConstraintI(Location().introduce(), make_bool_clause({ys[k]}, {as[i], bs[j]})));
        } else {
          // a_i /\ b_j -> false => not a_i \/ not b_j
          // a_i /\ b_j -> not r => not a_i \/ not b_j \/ not r
          // env.flatAddItem(
          //     new ConstraintI(Location().introduce(),
          //                     make_bool_clause({}, {reif, as[i], bs[j]})));
        }
      }

      if (comparator == SortingNetworkComparator::GE ||
          comparator == SortingNetworkComparator::EQ) {
        size_t k = i + j;
        if (k < c) {
          // not a_i /\ not b_j -> not y_[k]
          env.flatAddItem(
              new ConstraintI(Location().introduce(), make_bool_clause({as[i], bs[j]}, {ys[k]})));
        }  // else: not a_i /\ not b_i -> not false => true
      }
    }
  }

  return ys;
}
std::vector<Expression*> build_merge_network_recursive(EnvI& env, std::vector<Expression*>& as,
                                                       std::vector<Expression*>& bs,
                                                       SortingNetworkComparator comparator,
                                                       size_t c, Expression* reif, double lambda) {
  // These recursive cases are handled directly (without recursive call)
  if (as.size() > c) {
    as.resize(c);
  }

  if (bs.size() > c) {
    bs.resize(c);
  }

  size_t a = as.size();
  size_t b = bs.size();

  // Our two comparator has a cardinality parameter, so this case also handles
  // `&& c == 1`
  if (a == 1 && b == 1) {
    // TODO according to paper, this can be just a1->y, b1->y, return y. But
    // does this work for all comparators? (I think so, test this later though)
    return build_two_comparator(env, as[0], bs[0], comparator, c, reif);
  }
  if (a == 0) {
    return bs;
  }
  if (b == 0) {
    return as;
  }
  std::vector<Expression*> as_odd;
  std::vector<Expression*> as_even;

  for (auto it = as.cbegin(); it != as.end();) {
    as_odd.push_back(*it++);

    if (it != as.end()) {
      as_even.push_back(*it++);
    } else {
      break;
    }
  }

  std::vector<Expression*> bs_odd;
  std::vector<Expression*> bs_even;

  for (auto it = bs.cbegin(); it != bs.end();) {
    bs_odd.push_back(*it++);

    if (it != bs.end()) {
      bs_even.push_back(*it++);
    } else {
      break;
    }
  }

  // Handles two cases:
  // If a + b <= c, acts like normal merge network
  // If not, it uses simplified merge network with c tweaked based on polarity
  std::vector<Expression*> z_odd =
      a + b <= c ? build_merge_network_mixed(env, as_odd, bs_odd, comparator, c, reif, lambda)
      : c % 2 == 0
          ? build_merge_network_mixed(env, as_odd, bs_odd, comparator, (c / 2) + 1, reif, lambda)
          : build_merge_network_mixed(env, as_odd, bs_odd, comparator, (c + 1) / 2, reif, lambda);
  assert(z_odd.size() == a + b <= c ? a : (c % 2 == 0 ? c + 1 : c));

  std::vector<Expression*> z_even =
      a + b <= c ? build_merge_network_mixed(env, as_even, bs_even, comparator, c, reif, lambda)
      : c % 2 == 0
          ? build_merge_network_mixed(env, as_even, bs_even, comparator, c / 2, reif, lambda)
          : build_merge_network_mixed(env, as_even, bs_even, comparator, (c - 1) / 2, reif, lambda);
  assert(z_odd.size() == a + b <= c ? b : (c % 2 == 0 ? c : c - 1));

  std::vector<Expression*> result;
  auto z_odd_it = z_odd.cbegin();
  auto z_even_it = z_even.cbegin();

  // Interleaves z_odd/z_even, with its elements transformed by two comparator
  // To preserve the invariant that the size of the result is c, the
  // cardinality of the two comparator is changed (only happens in the even
  // case)
  result.push_back(*z_odd_it++);
  while (z_even_it != z_even.cend() && z_odd_it != z_odd.cend()) {
    std::vector<Expression*> ys =
        build_two_comparator(env, *z_even_it++, *z_odd_it++, comparator, c - result.size(), reif);
    result.insert(result.end(), ys.begin(), ys.end());
  }

  // In normal merges, the last element needs to be added as-is to the result
  if (z_odd_it != z_odd.cend()) {
    result.push_back(*z_odd_it++);
  } else if (z_even_it != z_even.cend()) {
    result.push_back(*z_even_it++);
  }

  // We have processed all elements of z
  assert(z_odd_it == z_odd.end());
  assert(z_even_it == z_even.end());

  // We have preserved the invariant
  assert(result.size() == std::min(a + b, c));

  return result;
}

std::pair<size_t, size_t> calculate_direct_merge_network(size_t a, size_t b, size_t c) {
  if (a + b == c) {
    return std::make_pair(a + b, a * b + a + b);
  }
  return std::make_pair(c, (a + b) * c - (a * (a - 1)) / 2 - (b * (b - 1)) / 2 - (c * (c - 1)) / 2);
}

std::pair<size_t, size_t> calculate_recursive_merge_network(size_t a, size_t b, size_t c) {
  if (a == 1 && b == 1) {
    return calculate_two_comparator_network(a, b, c);
  }
  if (a == 0 || b == 0) {
    return std::pair<size_t, size_t>(0, 0);
  }

  auto entry = recursive_merger_values.find(std::tuple<size_t, size_t, size_t>(a, b, c));

  if (entry != recursive_merger_values.end()) {
    return entry->second;
  }  // TODO leads to segfault ?
  auto left = calculate_recursive_merge_network(std::ceil(a / 2.), std::ceil(b / 2.),
                                                std::floor(c / 2.) + 1);
  auto right =
      calculate_recursive_merge_network(std::floor(a / 2.), std::floor(b / 2.), std::floor(c / 2.));

  if (c == a + b) {
    std::pair<size_t, size_t> res =
        std::make_pair(left.first + right.first + 2 * ((a + b - 1) / 2),
                       left.first + right.first + 3 * ((a + b - 1) / 2));
    recursive_merger_values[std::tuple<int32_t, int32_t, int32_t>(a, b, c)] = res;

    return res;
  }
  std::pair<size_t, size_t> res =
      std::make_pair(left.first + right.first + c - 1,
                     left.first + right.first + c % 2 == 1 ? (3 * c - 3) / 2 : (3 * c - 2) / 2 + 2);
  recursive_merger_values[std::tuple<int32_t, int32_t, int32_t>(a, b, a + b)] = res;
  return res;
}

std::vector<Expression*> build_merge_network_mixed(EnvI& env, std::vector<Expression*>& as,
                                                   std::vector<Expression*>& bs,
                                                   SortingNetworkComparator comparator, size_t c,
                                                   Expression* reif, double lambda) {
  if (lambda == -1) {
    return build_merge_network_direct(env, as, bs, comparator, c, reif);
  }
  if (lambda == -2) {
    return build_merge_network_recursive(env, as, bs, comparator, c, reif, lambda);
  }

  size_t a = as.size();
  size_t b = bs.size();

  auto direct_formula = calculate_direct_merge_network(a, b, c);
  auto recursive_formula = calculate_recursive_merge_network(a, b, c);

  double direct = formula_value(direct_formula, lambda);
  double recursive = formula_value(recursive_formula, lambda);

  if (direct < recursive) {
    return build_merge_network_direct(env, as, bs, comparator, c, reif);
  }
  return build_merge_network_recursive(env, as, bs, comparator, c, reif, lambda);
}
}  // namespace MiniZinc
