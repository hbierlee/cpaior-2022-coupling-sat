#include <minizinc/ast.hh>
#include <minizinc/eval_par.hh>
#include <minizinc/flat_exp.hh>
#include <minizinc/flatten_internal.hh>
#include <minizinc/sat/at_most1.hh>
#include <minizinc/sat/sorting_networks.hh>
#include <minizinc/sat/util.hh>
#include <minizinc/type.hh>
#include <minizinc/values.hh>

#include <cassert>
#include <cmath>
#include <cstddef>
#include <utility>
#include <vector>

namespace MiniZinc {

double formula_value(std::pair<size_t, size_t> form, double lambda) {
  return lambda * form.first + form.second;
}

Expression* b_build_sorting_network(EnvI& env, Call* call) {
  ArrayLit* xs = eval_array_lit(env, call->arg(0));

  auto comparator = static_cast<SortingNetworkComparator>(eval_int(env, call->arg(1)).toInt());

  // sorting network size limiter
  size_t cardinality = eval_int(env, call->arg(2)).toInt();
  double lambda = eval_float(env, call->arg(3)).toDouble();

  // Get reification variable
  // TODO remove
  Expression* reif =
      call->argCount() == 5 ? follow_id_to_value(call->arg(4)) : env.constants.literalTrue;

  assert(cardinality >= 0);

  // TODO [?] faster way to get expressionvector out of arraylits?
  std::vector<Expression*> xs_vec;
  for (size_t i = 0; i < xs->size(); ++i) {
    xs_vec.push_back((*xs)[i]);
  }

  cardinality = std::min(xs_vec.size(), cardinality);

  auto* cardinality_network =
      new ArrayLit(Location().introduce(),
                   build_sorting_network_mixed(env, xs_vec, comparator, cardinality, reif, lambda));

  cardinality_network->type(Type::varbool(1));
  // assert(cardinality_network->size() == std::min(xs_vec.size(),
  // cardinality));
  return cardinality_network;
  // TODO add comparator to network value calculations
};

};  // namespace MiniZinc
