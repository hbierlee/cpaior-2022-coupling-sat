#include <minizinc/ast.hh>
#include <minizinc/eval_par.hh>
#include <minizinc/flatten_internal.hh>
#include <minizinc/sat/binary.hh>

#include <bitset>
#include <cmath>
#include <vector>

namespace MiniZinc {
Expression* b_binary(EnvI& env, Call* call) {
  auto k = eval_int(env, call->arg(0)).toInt();
  auto n = eval_int(env, call->arg(1)).toInt();
  // Switch between unsigned and two complement
  bool two_complement = eval_bool(env, call->arg(2));

  // To create a two_complement representation, we offset `k` by the value of the sign bit (making k
  // non-negative) and create its n-bit unsigned binary representation, turning it into two's
  // complement by flipping the sign/n'th bit.

  // n=4, so the value of the sign-bit is 2^(4-1)=2^3=8
  // k=-2 -> k=-2+8= 6=0110 (unsigned) = 0111 = -2 (two's complement)
  // k= 2 -> k= 2+8=10=0111 (unsigned) = 0110 =  2 (two's complement)

  if (two_complement) {
    k += std::pow(2, (n - 1));
  }

  assert(0 <= k && k <= std::pow(2, n) && "bitset of size n is too small to encode k");

  std::bitset<64> bitset(k);
  std::vector<Expression*> binary;
  binary.reserve(n);

  // Regular bits
  for (size_t i = 0; i < n - 1; ++i) {
    binary.push_back(env.constants.boollit(bitset[i]));
  }

  // Add the n'th bit (flipped for two's complement)
  binary.push_back(env.constants.boollit(two_complement ? !bitset[n - 1] : bitset[n - 1]));

  auto* res = new ArrayLit(Location().introduce(), binary);
  res->type(Type::parbool(1));

  return res;
}
}  // namespace MiniZinc
