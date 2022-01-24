#include <minizinc/builtins.hh>
#include <minizinc/flatten_internal.hh>
#include <minizinc/sat/at_most1.hh>

#include "minizinc/ast.hh"
#include "minizinc/eval_par.hh"

#include <cassert>
#include <cstddef>
#include <map>
#include <numeric>
#include <queue>
#include <type_traits>

namespace MiniZinc {

// TODO duplicated from builtins.cpp
// is there another way to check for fixed variables?
Expression* my_exp_is_fixed(EnvI& env, Expression* e) {
  GCLock lock;
  Expression* cur = e;
  for (;;) {
    if (cur == nullptr) {
      return nullptr;
    }
    if (cur->type().isPar()) {
      return eval_par(env, cur);
    }
    switch (cur->eid()) {
      case Expression::E_ID:
        cur = cur->cast<Id>()->decl();
        break;
      case Expression::E_VARDECL:
        if (cur->type().st() != Type::ST_SET) {
          Expression* dom = cur->cast<VarDecl>()->ti()->domain();
          if (dom != nullptr &&
              (dom->isa<IntLit>() || dom->isa<BoolLit>() || dom->isa<FloatLit>())) {
            return dom;
          }
          if (dom != nullptr && dom->isa<SetLit>()) {
            auto* sl = dom->cast<SetLit>();
            auto* isv = sl->isv();
            if (isv != nullptr && isv->min() == isv->max()) {
              return IntLit::a(isv->min());
            }
            auto* fsv = sl->fsv();
            if (fsv != nullptr && fsv->min() == fsv->max()) {
              return FloatLit::a(fsv->min());
            }
          }
        }
        cur = cur->cast<VarDecl>()->e();
        break;
      default:
        return nullptr;
    }
  }
}

struct BDD {
  size_t x = 0;
  size_t lowChild = 0;
  size_t highChild = 0;

  BDD(size_t terminal) : x(terminal) { assert(terminal == 0 || terminal == 1); };
  BDD(size_t x, size_t low_child, size_t high_child)
      : x(x), lowChild(low_child), highChild(high_child) {
    // this should not happen (and we use this fact later to recognize terminal
    // nodes)
    assert(low_child > 0 || high_child > 0);
  };
};

// TODO [?] this setup should make a std::map<BDDInterval_t, x> behave like a
// binary search tree, no?
struct BDDInterval {
  IntVal l;
  IntVal u;
  BDDInterval(IntVal l, IntVal u) : l(l), u(u){};
};

// Since maps use the less operator to check for equivalence (using !(a < b) &&
// !(b < a)), overloading it should let a map behave as an interval map, e.g.,
// doing a look-up of key [x,x] it will return the first interval [a,b] where a
// <= x <= b.
bool operator<(const BDDInterval& lhs, const BDDInterval& rhs) { return lhs.u < rhs.l; };

std::ostream& operator<<(std::ostream& out, const BDDInterval& obj) {
  out << "[" << obj.l << "," << obj.u << "]";
  return out;
}

// TODO make recursive
std::map<BDDInterval, int>::iterator bdd_construction(
    EnvI& env, int i, std::vector<IntVal>& as, std::vector<Expression*>& bs, IntVal c,
    std::vector<std::map<BDDInterval, int>>& levels, std::vector<BDD>& bdds) {
  auto search = levels[i].find(BDDInterval(c, c));
  if (search != levels[i].end()) {
    return search;
  }
  IntVal a_i = as[i];
  auto low_child_node = bdd_construction(env, i + 1, as, bs, c, levels, bdds);
  auto high_child_node = bdd_construction(env, i + 1, as, bs, c - a_i, levels, bdds);

  if (low_child_node->first.l == high_child_node->first.l &&
      low_child_node->first.u == high_child_node->first.u) {
    // If children intervals are equivalent, their BDDs should be the same BDD
    assert(low_child_node->second == high_child_node->second);

    return levels[i]
        .emplace(std::piecewise_construct,
                 std::forward_as_tuple(high_child_node->first.l + a_i, high_child_node->first.u),
                 std::forward_as_tuple(high_child_node->second))
        .first;
  }
  if (high_child_node->first.l + a_i > low_child_node->first.u ||
      low_child_node->first.l > high_child_node->first.u + a_i.toInt()) {
    assert(false && "should not happen?");
  }

  // Calculate intersection of low child interval, and the high child
  // interval increased by a_i
  IntVal lower = std::max(low_child_node->first.l, high_child_node->first.l + a_i);
  IntVal upper = std::min(low_child_node->first.u, high_child_node->first.u + a_i);

  bdds.emplace_back(i, low_child_node->second, high_child_node->second);

  return levels[i]
      .emplace(std::piecewise_construct, std::forward_as_tuple(lower, upper),
               std::forward_as_tuple(bdds.size() - 1))
      .first;
}

enum BDDComparison { LE = 0, EQ = 1, NE = 2 };

Expression* build_bdd(EnvI& env, Call* call, BDDComparison comparison) {
  ArrayLit* as_al = eval_array_lit(env, call->arg(0));
  ArrayLit* bs_al = eval_array_lit(env, call->arg(1));
  IntVal c = eval_int(env, call->arg(2));

  Expression* zero_terminal_arg = call->arg(3);
  Expression* one_terminal_arg = call->arg(4);

  assert(as_al->size() == bs_al->size());

  std::vector<IntVal> as;
  std::vector<Expression*> bs;

  for (size_t i = 0; i < as_al->size(); i++) {
    IntVal a = eval_int(env, (*as_al)[i]);
    Expression* b = (*bs_al)[i];

    // Pre-processing: Filter out fixed variables
    if (Expression* b_fixed = my_exp_is_fixed(env, b)) {
      bool b_literal = b_fixed->cast<BoolLit>()->v();

      if (b_literal) {
        c -= a;
      }  // subtract if true literal
    } else {
      // Pre-processing: convert negative coefficients to positive by negating
      // their variables
      if (a < 0) {
        a = std::abs(a);
        b = new UnOp(Location().introduce(), UOT_NOT, b);
        b->type(Type::varbool());
        c += a;
      }

      // Pre-processing: filter coefficients of value 0
      if (a != 0) {
        as.push_back(a);
        bs.push_back(b);
      }
    }
  }

  // With only positive coefficients, a negative right-hand side is
  // unsatisfiable
  if (c < 0) {
    std::cerr << "%%%dot }" << std::endl;
    return zero_terminal_arg;
  }

  // // Similarly, a right-hand side of 0 means all variables are false
  // // TODO [!] not for EQ!!
  // if (c == 0) {
  //   // TODO are all these uses of new correct?
  //   // TODO also, am I using location correctly? Probably doesn't matter too
  //   // much but still
  //   std::vector<Expression *> bool_clauses;
  //   for (Expression *b : bs) {
  //     ArrayLit *positives =
  //         new ArrayLit(Location().introduce(), std::vector<Expression *>({}));
  //     ArrayLit *negatives =
  //         new ArrayLit(Location().introduce(), std::vector<Expression *>({b}));
  //     positives->type(Type::varbool(1));
  //     negatives->type(Type::varbool(1));

  //     Call *bool_clause =
  //         new Call(Location().introduce(), constants().ids.bool_clause,
  //                  {positives, negatives});
  //     bool_clause->type(Type::varbool());
  //     bool_clauses.push_back(bool_clause);
  //   }
  //   ArrayLit *al = new ArrayLit(Location().introduce(), bool_clauses);
  //   al->type(Type::varbool(1));
  //   Call *forall =
  //       new Call(Location().introduce(), constants().ids.forall, {al});
  //   forall->type(Type::varbool());

  //   std::cerr << "%%%dot }" << std::endl;
  //   assert(false && "todo: probably return reif i/o forall");
  //   return forall;
  // }

  {  // Pre-processing: sort from big to small
    std::vector<size_t> permutation(as.size());
    iota(permutation.begin(), permutation.end(), 0);
    std::sort(permutation.begin(), permutation.end(),
              [&as](std::size_t i, std::size_t j) { return as[i] > as[j]; });

    // Apply permutation to both as and bs
    std::vector<IntVal> as_sorted(as.size());
    std::transform(permutation.begin(), permutation.end(), as_sorted.begin(),
                   [&](std::size_t i) { return as[i]; });

    std::vector<Expression*> bs_sorted(bs.size());
    std::transform(permutation.begin(), permutation.end(), bs_sorted.begin(),
                   [&](std::size_t i) { return bs[i]; });

    as = std::move(as_sorted);
    bs = std::move(bs_sorted);
  }

  // Each level contains the nodes for variable x_i
  int n = as.size();
  std::vector<std::map<BDDInterval, int>> levels(n + 1, std::map<BDDInterval, int>());

  IntVal sum_of_coefficients_from_i = std::accumulate(as.begin(), as.end(), IntVal());

  // TODO for now, we have multiple zero/one terminals, maybe we could get away
  // with just having one of each. Then we should pass by reference or pointers
  // instead (note pairs do not support references), but this begs the questions
  // where do we keep the regular nodes? ..heap? Add a zero and one terminal
  // node on each level
  std::vector<BDD> bdds;

  size_t zero_terminal = 0;
  size_t one_terminal = 1;

  switch (comparison) {
    case BDDComparison::LE:
      // Base case for bool_lin_le[_reif]
      // If the RHS < 0, the constraint is 0 (terminal)
      // If the RHS >= LHS sum, the constraint is 1 (terminal)
      for (size_t i = 0; i < n + 1; i++) {
        bdds.emplace_back(zero_terminal);
        levels[i].emplace(std::piecewise_construct,
                          std::forward_as_tuple(-IntVal::infinity(), IntVal(-1)),
                          std::forward_as_tuple(bdds.size() - 1));

        bdds.emplace_back(one_terminal);
        levels[i].emplace(std::piecewise_construct,
                          std::forward_as_tuple(sum_of_coefficients_from_i, IntVal::infinity()),
                          std::forward_as_tuple(bdds.size() - 1));

        sum_of_coefficients_from_i = i < n ? sum_of_coefficients_from_i - as[i] : 0;
      }
      break;
    case BDDComparison::NE:
      std::swap(zero_terminal, one_terminal);
    case BDDComparison::EQ:
      // Base case for bool_lin_eq[_reif]
      // If the RHS < 0, the constraint is 0
      // If the RHS > LHS sum, the constraint is 0
      // If the RHS = LHS sum, then all its literals have to be true for the
      // constraint to be 1

      for (size_t i = 0; i < n + 1; i++) {
        bdds.emplace_back(zero_terminal);
        levels[i].emplace(std::piecewise_construct,
                          std::forward_as_tuple(-IntVal::infinity(), IntVal(-1)),
                          std::forward_as_tuple(bdds.size() - 1));

        bdds.emplace_back(zero_terminal);
        levels[i].emplace(
            std::piecewise_construct,
            std::forward_as_tuple(sum_of_coefficients_from_i.plus(1), IntVal::infinity()),
            std::forward_as_tuple(bdds.size() - 1));

        // TODO instead of a BDD chain, this case (RHS=LHS) should be implemented
        // with a conjunction if possible
        if (i < n) {
          // low child is 0 terminal (the first BDD node), the high child is the
          // next variable one level down
          bdds.emplace_back(i, 0, 5 + i * 3);
        } else {
          // the last high child, which is 1 (terminal)
          bdds.emplace_back(one_terminal);
        }

        levels[i].emplace(
            std::piecewise_construct,
            std::forward_as_tuple(sum_of_coefficients_from_i, sum_of_coefficients_from_i),
            std::forward_as_tuple(bdds.size() - 1));

        sum_of_coefficients_from_i = i < n ? sum_of_coefficients_from_i - as[i] : 0;
      }
      break;
    default:
      assert(false);
  }

  size_t root = bdd_construction(env, 0, as, bs, c, levels, bdds)->second;
  BDD bdd = bdds[root];

  // terminal
  if (bdd.lowChild == 0 && bdd.highChild == 0) {
    std::cerr << "%%%dot }" << std::endl;
    return bdd.x != 0 ? one_terminal_arg : zero_terminal_arg;
  }

  // Construct BDD binary tree
  // Set of nodes for the variables, one set of edges for the high outputs, one
  // for the low
  std::vector<Expression*> variables;
  std::vector<Expression*> edge_sets[2];  // edge_set[0][i] = j means the
                                          // 0-output of node i leads to node j

  // Traverse BDD breadth-first
  // TODO a nice improvement would be if we would just iterate over levels to
  // traverse breadth-first. However, not all nodes in levels should end up in
  // the final tree (only connected ones). There could be something smart there.
  std::queue<size_t> queue;
  std::unordered_map<size_t, size_t> discovered;
  queue.push(root);

  int i = 2;  // root node has label 1
  while (!queue.empty()) {
    size_t next = queue.front();
    BDD next_bdd = bdds[next];
    queue.pop();

    variables.push_back(bs[next_bdd.x]);

    size_t children[2] = {next_bdd.lowChild, next_bdd.highChild};
    for (int output = 0; output < 2; ++output) {
      size_t child = children[output];
      BDD child_bdd = bdds[child];

      // Terminal children always both point to 0 (and never for leaf)
      if (child_bdd.lowChild == 0 && child_bdd.highChild == 0) {
        // terminal
        edge_sets[output].push_back(IntLit::a(child_bdd.x));
      } else {
        auto it = discovered.find(child);
        if (it == discovered.end()) {
          edge_sets[output].push_back(IntLit::a(i));
          queue.push(child);
          discovered.emplace(child, i);
          i++;
        } else {
          edge_sets[output].push_back(IntLit::a(it->second));
        }
      }
    }
  }

  std::vector<Expression*> args(5);
  args[0] = new ArrayLit(call->loc(), variables);
  args[0]->type(Type::varbool(1));

  args[1] = new ArrayLit(call->loc(), edge_sets[0]);
  args[1]->type(Type::parint(1));

  args[2] = new ArrayLit(call->loc(), edge_sets[1]);
  args[2]->type(Type::parint(1));

  args[3] = zero_terminal_arg;
  args[4] = one_terminal_arg;

  auto* nc = new Call(call->loc().introduce(), "bdd", args);
  nc->type(Type::varbool());

  return nc;
}

Expression* b_build_bdd_le(EnvI& env, Call* call) {
  return build_bdd(env, call, BDDComparison::LE);
}

Expression* b_build_bdd_eq(EnvI& env, Call* call) {
  return build_bdd(env, call, BDDComparison::EQ);
}

Expression* b_build_bdd_ne(EnvI& env, Call* call) {
  return build_bdd(env, call, BDDComparison::NE);
}

}  // namespace MiniZinc
