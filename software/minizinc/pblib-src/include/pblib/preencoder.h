#ifndef PREENCODER_H
#define PREENCODER_H

#include <pblib/PBConfig.h>
#include <pblib/SimplePBConstraint.h>
#include <pblib/clausedatabase.h>
#include <pblib/incpbconstraint.h>

class PreEncoder {
private:
  int64_t tmpWeight;
  PreEncoder(const PreEncoder& other) = delete;
  virtual PreEncoder& operator=(const PreEncoder& other) = delete;
  virtual bool operator==(const PreEncoder& other) const = delete;
  void join_duplicat_literals();
  void normalize_variables();
  void remove_lits_with_w_greater_leq_and_check_isamk(ClauseDatabase& formula, int32_t reification);

  template <class PBCon>
  void init_and_normalize(PBCon const& pbconstraint, ClauseDatabase& formula, int32_t reification=0);
  void check_for_trivial_constraints(ClauseDatabase& formula,
                                     int32_t reification = 0);
  void sort_literals();

  std::vector<PBLib::WeightedLit> literals;
  std::vector<int32_t> clause;
  int64_t max_weight;
  int64_t max_sum;
  int64_t bound_offset;
  PBTYPE type;
  bool isAMK;
  bool isAMKEqual;
  int64_t check_amk_equal;
  int n;
  int64_t leq;
  int64_t geq;
  PBLib::Comparator comparator;

  PBConfig config;
  statistic* stats;
  bool private_stats;

public:
  PreEncoder(PBConfig config, statistic* stats = 0);
  virtual ~PreEncoder();

  // after preencoding the following constraints hold for the returned
  // SimplePBConstraint:
  /// all weights > 0
  /// non trivial constraint
  /// sorted
  /// no literal duplicates
  SimplePBConstraint preEncodePBConstraint(
      PBLib::PBConstraint const& pbconstraint, ClauseDatabase& formula);
  std::shared_ptr<IncSimplePBConstraint> preEncodeIncPBConstraint(
      IncPBConstraint& pbconstraint, ClauseDatabase& formula);
};

#endif  // PREENCODER_H
