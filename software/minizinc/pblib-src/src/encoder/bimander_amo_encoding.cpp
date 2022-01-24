#include <pblib/encoder/bimander_amo_encoding.h>

#include <cmath>
#include <numeric>

using namespace PBLib;
using namespace std;

template <typename T>
ostream& operator<<(ostream& out, vector<T>& vec) {
  if (vec.size() == 0) {
    cout << "{ }";
    return out;
  }

  out << "{ " << vec[0];

  for (int i = 1; i < vec.size(); ++i) out << ", " << vec[i];

  out << " }";
  return out;
}

int64_t Bimander_amo_encoding::encodingValue(
    const SimplePBConstraint& pbconstraint) {
  int m = config->bimander_m;
  int n = pbconstraint.getN();

  if (config->bimander_m_is == BIMANDER_M_IS::FIXED) {
    m = config->bimander_m;
  } else if (config->bimander_m_is == BIMANDER_M_IS::N_HALF) {
    m = ceil((double)n / 2);
  } else if (config->bimander_m_is == BIMANDER_M_IS::N_SQRT) {
    m = ceil(sqrt((double)n));
  } else {
    m = config->bimander_m;
}

  int64_t clauses =
      ceil((double)(n * n) / (double)(2 * m)) + n * ceil(log2(m)) -
      ceil((double)n /
           2);  // from the paper .. seems to overestimating .. FIXME
  int64_t auxvars = ceil(log2(m));

  return valueFunction(clauses, auxvars);
}

void Bimander_amo_encoding::encode_intern(vector<Lit>& literals,
                                          ClauseDatabase& formula,
                                          AuxVarManager& auxvars) {
  int n = literals.size();

  if (config->bimander_m_is == BIMANDER_M_IS::FIXED) {
    m = config->bimander_m;
  } else if (config->bimander_m_is == BIMANDER_M_IS::COMMANDER) {
    m = 2;
  } else if (config->bimander_m_is == BIMANDER_M_IS::BINARY) {
    m = n;
  } else if (config->bimander_m_is == BIMANDER_M_IS::N_HALF) {
    m = ceil((double)n / 2);
  } else if (config->bimander_m_is == BIMANDER_M_IS::N_SQRT) {
    m = ceil(sqrt((double)n));
  } else {
    m = config->bimander_m;
  }

  assert(m > 0);
  // create the m groups
  groups.clear();
  groups.resize(m);

  int g = ceil((double)n / m);
  int ig = 0;
  int i;
  for (i = 0; i < literals.size();) {
    while (i < g) {
      groups[ig].push_back(literals[i]);
      i++;
    }
    ig++;
    g = g + ceil((double)(n - i) / (m - ig));
  }
  assert(ig == m);
  assert(m == groups.size());
  assert(i == literals.size());

  for (auto & group : groups) {
    naive_amo_encoder.encode_intern(group, formula);
  }

  bits.clear();
  for (int i = 0; i < ceil(log2(m)); ++i) {
    bits.push_back(auxvars.getVariable());
  }
  two_pow_nbits = pow(2, bits.size());

  std::vector<int> bit_balances(bits.size(), 0);

  if (config->bimander_aux_pattern == BIMANDER_AUX_PATTERN::BINARY || (config->bimander_aux_pattern == BIMANDER_AUX_PATTERN::GRAY && config->bimander_offset != -2)) {
    size_t offset = config->bimander_offset;

    for (size_t i = 0; i < m; i++) {  // for every group i
      size_t k = i+offset;
      size_t bit_pattern = config->bimander_aux_pattern == BIMANDER_AUX_PATTERN::BINARY ? k : k ^ (k >> 1);
      for (size_t h = 0; h < groups[i].size(); h++) {  // for every lit h in group i
        for (size_t j = 0; j < bits.size(); j++) { // for every bit j
          if (((bit_pattern >> j) & 0x1) != 0U) {  // the jth bit of binary rep of i is 1
            formula.addClause(-groups[i][h], bits[j]);
            bit_balances[j]++;
          } else {
            formula.addClause(-groups[i][h], -bits[j]);
            bit_balances[j]--;
          }
        }
      }
    }
    // lex_geq(c,x) = c >= x =  forall (i in index_set(c) where not c[i]) (not x[i] \/ exists (j in index_set(c) where j < i /\ c[j]) (not x[j]))
    if (config->bimander_aux_pattern == BIMANDER_AUX_PATTERN::BINARY && config->bimander_enforce_aux_var_domain) {
      size_t lb = offset;
      size_t ub = m + offset;

      // lex_leq(c,x) = c <= x =  forall (i in index_set(c) where c[i]) (x[i] \/ exists (j in index_set(c) where j < i /\ not c[j]) (x[j]))
                              // for every i=1 in c, either there's a 1 at the same position, or a 1 at a higher significance j in x where not c[j]
      if (lb > 0) {
        for (size_t i = 0; i < bits.size(); i++) {
          if (((lb >> i) & 0x1) != 0U) { // for i in where c_i == 1
            std::vector<int> clause;
            clause.push_back(bits[i]); // x[i]
            for (size_t j = i+1; j < bits.size(); j++) {

              if (((lb >> j) & 0x1) == 0U) { // for j<i in where c_j == 0
                clause.push_back(bits[j]); // x[j]
              }
            }
            formula.addClause(clause);
          }
        }
      }

      // lex_geq(c,x) = c >= x =  forall (i in index_set(c) where not c[i]) (not x[i] \/ exists (j in index_set(c) where j < i /\ c[j]) (not x[j]))
      if (ub < two_pow_nbits) {
        for (size_t i = 0; i < bits.size(); i++) {

          if (((ub >> i) & 0x1) == 0U) { // for i in where not c_i
            std::vector<int> clause;
            clause.push_back(-bits[i]); // not x[i]
            for (size_t j = i+1; j < bits.size(); j++) {

              if (((ub >> j) & 0x1) != 0U) { // for j<i in where c_j == 1
                clause.push_back(-bits[j]); // not x[j]
              }
            }
            formula.addClause(clause);
          }
        }
      }
    }
  } else { // offset = -2; spread/gray pattern
    // TODO binary pattern
    // TODO instead of skipping, redundantly add the groups 
    bits.clear();
    nBits = ceil(log2(m));
    k = (two_pow_nbits - m) * 2;  // k is the number of literals that share a bit because of redundancy
    int gray_code;
    int next_gray;
    i = 0;
    int index = -1;
    for (; i < k; ++i) {
      index++;
      gray_code = i ^ (i >> 1);
      i++;  // we skip the next binary string to use the redundancy
      next_gray = i ^ (i >> 1);
      for (int j = 0; j < nBits; ++j) {
        if ((gray_code & (1 << j)) == (next_gray & (1 << j))) {
          if ((gray_code & (1 << j)) != 0) {
            for (int g = 0; g < groups[index].size(); ++g) {
              formula.addClause(-groups[index][g], bits[j]);
              bit_balances[j]++;
            }
          } else {
            for (int g = 0; g < groups[index].size(); ++g) {
              formula.addClause(-groups[index][g], -bits[j]);
              bit_balances[j]--;
            }
          }
        }
        // else skip that bit since it is redundant
      }
    }

    for (; i < two_pow_nbits; ++i) {
      index++;
      gray_code = i ^ (i >> 1);
      for (int j = 0; j < nBits; ++j) {
        if ((gray_code & (1 << j)) != 0) {
          for (int g = 0; g < groups[index].size(); ++g) {
            formula.addClause(-groups[index][g], bits[j]);
            bit_balances[j]++;
          }
        } else {
          for (int g = 0; g < groups[index].size(); ++g) {
            formula.addClause(-groups[index][g], -bits[j]);
            bit_balances[j]--;
          }
        }
      }
    }
    assert(index + 1 == groups.size());
  }
  _stats->totalBitBalances.push_back(std::accumulate(bit_balances.begin(), bit_balances.end(), 0, [] (int x, int y) {return x + std::abs(y);}));
}

void Bimander_amo_encoding::encode(const SimplePBConstraint& pbconstraint,
                                   ClauseDatabase& formula,
                                   AuxVarManager& auxvars) {
  formula.addConditionals(pbconstraint.getConditionals());

  if (config->print_used_encodings)
    cout << "c encode with bimander amo" << endl;

  assert(pbconstraint.getLeq() == 1);

  _literals.clear();

  for (int i = 0; i < (int)pbconstraint.getN(); ++i)
    _literals.push_back(pbconstraint.getWeightedLiterals()[i].lit);

  if (pbconstraint.getComparator() == BOTH && (pbconstraint.getGeq() == 1)) {
    assert(pbconstraint.getGeq() == 1 && pbconstraint.getLeq() == 1);
    formula.addClause(_literals);
  }

  encode_intern(_literals, formula, auxvars);
  for (int i = 0; i < pbconstraint.getConditionals().size(); ++i)
    formula.getConditionals().pop_back();
}
