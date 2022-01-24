#include <minizinc/builtins.hh>
#include <minizinc/flatten_internal.hh>
#include <minizinc/sat/at_most1.hh>
#include <minizinc/sat/util.hh>

#include "minizinc/ast.hh"
#include "minizinc/eval_par.hh"

#include <bitset>
#include <cmath>
#include <cstddef>
#include <map>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

namespace MiniZinc {

// TODO maybe integrate to SAT model directly
// TODO why doesn't unordered_map work with set of Expression as key? (although
// this is definitely fine too)
// TODO reference to set?

// TODO keeping `i` is unnecessary
// a map from group to the offset, count and config of aux variables
static std::map<std::set<Expression*>, std::tuple<size_t, size_t, size_t>> mimander_map;
static std::vector<Expression*> mimander_bs;

// From Nguyen, Mai. A New Method to Encode the At-Most-One Constraint into SAT.
// 7th SoICT (2015).
void at_most1_bimander(EnvI& env, ArrayLit* as, std::vector<Expression*>& bool_clauses) {
  size_t n = as->size();
  // int m = std::ceil(std::sqrt(n)); // TODO make m parameter
  size_t m = std::ceil((float)n / 2.);
  size_t g = std::ceil((float)n / (float)m);

  // pairwise for every group
  for (size_t group = 0; group < m; group++) {
    // TODO here it might be better to post a at_most1(_pairwise) constraint for
    // CSE. However, CSE will already kick in at the clause level
    for (size_t i = 0; i < g; ++i) {
      size_t group_i = group * g + i;
      for (size_t j = i + 1; j < g; ++j) {
        size_t group_j = group * g + j;
        if (group_j < as->size()) {
          bool_clauses.push_back(make_bool_clause({}, {(*as)[group_i], (*as)[group_j]}));
        }
      }
    }
  }

  // aux
  std::vector<VarDecl*> bs;
  for (int i = 0; i < std::ceil(std::log2(m)); ++i) {
    bs.push_back(add_bool_var(env));
  }

  size_t g_idx = 0;
  for (size_t i = 0; i < m; i++) {
    for (size_t h = 0; h < g; h++) {
      if (g_idx < as->size()) {
        Expression* g_i_h = (*as)[g_idx];
        for (size_t j = 0; j < bs.size(); j++) {
          Id* b_id = bs[j]->id();

          if (((i >> j) & 0x1) != 0U) {  // the jth bit of binary rep of i is 1
            bool_clauses.push_back(make_bool_clause({b_id}, {g_i_h}));
          } else {
            bool_clauses.push_back(make_bool_clause({}, {g_i_h, b_id}));
          }
        }

        g_idx++;
      }
    }
  }

  // TODO make assert a maximal difference since it's overestimating a bit
  // assert(bs.size() == std::ceil(std::log2(m)));
  // assert(bool_clauses.size() == ceil((double)(n * n) / (double)(2 * m)) + n *
}

void at_most1_mimander(EnvI& env, ArrayLit* as, std::vector<Expression*>& bool_clauses) {
  size_t n = as->size();
  size_t m = n;
  // int m = std::ceil(std::sqrt(n)); // TODO make m parameter
  // int m = std::ceil((float)n / 2.);
  int g = std::ceil((float)n / (float)m);

  // TODO if m=1, only do pairwise (maybe not in mimander?)

  // Create m empty (placeholder) groups
  // groups are sets; no order and we use them as key for mimander_map
  std::map<size_t, std::set<Expression*>> groups;
  std::vector<std::set<Expression*>> new_groups;
  std::vector<Expression*> bs;

  for (size_t i = 0; i < m; i++) {
    std::set<Expression*> group;
    // make groups of size g, last group may have fewer elements
    for (size_t j = i * g; j < (i + 1) * g && j < n; j++) {
      group.insert((*as)[j]);
    }

    // buffer new groups, insert existing groups
    auto connected_group = mimander_map.find(group);
    if (connected_group != mimander_map.end()) {
      size_t offset = std::get<0>(connected_group->second);
      size_t count = std::get<1>(connected_group->second);
      size_t group_key = std::get<2>(connected_group->second);

      // every new aux var doubles the groups size

      // TODO maybe less complicated if we just jump by 2^group_size
      size_t next_group_key = (group_key + 1) << bs.size();

      for (size_t shifted_group_key = group_key << bs.size();
           shifted_group_key < ((group_key + 1) << bs.size()); shifted_group_key++) {
        if (groups.count(shifted_group_key) > 0 && !groups[shifted_group_key].empty()) {
          // conflict

          // move the occupying group
          size_t dest = next_group_key;
          for (size_t i = 1;; i++) {
            size_t dest = (group_key + i) << bs.size();

            if (groups.count(dest) == 0) {
              groups[dest] = groups[shifted_group_key];
              // empty group means illegal for all other groups
              groups[shifted_group_key].clear();
              break;
            }
          }
        } else {
          groups[shifted_group_key] = connected_group->first;
          break;
        }
        shifted_group_key++;
      }

      // then add the commander variables of the connected group
      for (size_t j = offset; j < offset + count; j++) {
        bs.push_back(mimander_bs[j]);
      }
    } else {
      new_groups.push_back(group);

      // Pairwise at-most-one for the elements in each new group
      for (auto i = group.begin(); i != group.end(); i++) {
        auto j = i;
        j++;

        for (; j != group.end(); j++) {
          bool_clauses.push_back(make_bool_clause({}, {*i, *j}));
        }
      }
    }
  }

  size_t old_mimander_bs = mimander_bs.size();

  // Add new var bools if we don't have enough from reuse
  for (size_t i = bs.size(); i < std::ceil(std::log2(m)); i++) {
    Expression* new_aux_var = add_bool_var(env)->id();
    bs.push_back(new_aux_var);
    mimander_bs.push_back(new_aux_var);
  }

  // TODO std::move?
  // Insert new groups into the holes
  size_t new_group_index = 0;
  for (auto new_group : new_groups) {
    for (auto it = groups.cbegin(), end = groups.cend();
         it != end && it->second.empty() && new_group_index == it->first; ++it, ++new_group_index) {
    }
    groups[new_group_index] = new_group;

    // group g_i has aux variables offset..offset+new_bs_count, config i
    mimander_map.emplace(std::piecewise_construct, std::forward_as_tuple(new_group),
                         std::forward_as_tuple(old_mimander_bs, bs.size(), new_group_index));
    new_group_index++;
  }

  // The elements of each group imply an unique combination of aux vars
  for (auto const& group_pair : groups) {
    size_t i = group_pair.first;
    std::set<Expression*> group = group_pair.second;
    // std::set<Expression *> group = groups[i];
    if (group.empty()) {
      continue;
    }

    for (Expression* g_i_h : group) {
      for (size_t j = 0; j < bs.size(); j++) {
        if (((i >> j) & 0x1) != 0U) {  // the jth bit of binary rep of i is 1
          bool_clauses.push_back(make_bool_clause({bs[j]}, {g_i_h}));
        } else {
          bool_clauses.push_back(make_bool_clause({}, {g_i_h, bs[j]}));
        }
      }
    }
  }

  // assert(bs.size() == std::ceil(std::log2(m)));
  // assert(bool_clauses.size() == ceil((double)(n * n) / (double)(2 * m)) + n *
}

Expression* b_at_most1_pairwise(EnvI& env, Call* call) {
  ArrayLit* as = eval_array_lit(env, call->arg(0));
  std::vector<Expression*> bool_clauses;

  // pairwise encoding
  for (size_t i = 0; i < as->size(); ++i) {
    for (size_t j = i + 1; j < as->size(); ++j) {
      bool_clauses.push_back(make_bool_clause({}, {(*as)[i], (*as)[j]}));
    }
  }

  auto* al = new ArrayLit(Location().introduce(), bool_clauses);
  al->type(Type::varbool(1));
  Call* forall = new Call(Location().introduce(), env.constants.ids.forall, {al});
  forall->type(Type::varbool());

  return forall;
}

Expression* b_at_most1_bimander(EnvI& env, Call* call) {
  // TODO filter fixed vars (for now done in mzn due to unavailability of
  // exp_is_fixed builtin)
  ArrayLit* as = eval_array_lit(env, call->arg(0));

  std::vector<Expression*> bool_clauses;
  at_most1_bimander(env, as, bool_clauses);

  auto* bool_clauses_al = new ArrayLit(Location().introduce(), bool_clauses);
  bool_clauses_al->type(Type::varbool(1));
  Call* forall = new Call(Location().introduce(), env.constants.ids.forall, {bool_clauses_al});
  forall->type(Type::varbool());

  return forall;
}

Expression* b_at_most1_mimander(EnvI& env, Call* call) {
  // TODO filter fixed vars (for now done in mzn due to unavailability of
  // exp_is_fixed builtin)
  ArrayLit* al = eval_array_lit(env, call->arg(0));

  std::vector<Expression*> bool_clauses;
  at_most1_mimander(env, al, bool_clauses);

  auto* bool_clauses_al = new ArrayLit(Location().introduce(), bool_clauses);
  bool_clauses_al->type(Type::varbool(1));
  Call* forall = new Call(Location().introduce(), env.constants.ids.forall, {bool_clauses_al});
  forall->type(Type::varbool());

  return forall;
}
};  // namespace MiniZinc
