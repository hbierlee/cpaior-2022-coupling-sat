#ifndef PBCONFIG_H
#define PBCONFIG_H

#include <vector>
#include <cstdint>
#include <memory>
#include <set>
#include <string>

struct statistic {
  int num_bdd_gates_encodings = 0;
  int num_bdd_clause_encodings = 0;
  int num_card_encodings = 0;
  int num_adder_encodings = 0;
  int num_amo_encodings = 0;
  int num_clause = 0;
  int num_trivial = 0;
  int num_amo = 0;
  int num_amk = 0;
  int num_pb = 0;
  std::vector<int> totalBitBalances;

  void printStatistic();
  void printStatisticRelative();
};

// TODO why is this in its own namespace?
namespace BIMANDER_M_IS {
enum BIMANDER_M_IS { N_HALF, N_SQRT, FIXED, COMMANDER, BINARY };
};

namespace BIMANDER_AUX_PATTERN {
enum BIMANDER_AUX_PATTERN { BINARY, GRAY };
};

namespace AMO_ENCODER {
enum PB2CNF_AMO_Encoder {
  BEST,
  NESTED,
  BDD,
  BIMANDER,
  COMMANDER,
  KPRODUCT,
  BINARY,
  PAIRWISE
};
};

namespace AMK_ENCODER {
enum PB2CNF_AMK_Encoder { BEST, BDD, CARD };
};

namespace PB_ENCODER {
enum PB2CNF_PB_Encoder { BEST, BDD, SWC, SORTINGNETWORKS, ADDER, BINARY_MERGE };
};

class PBConfigClass {
private:
public:
  PB_ENCODER::PB2CNF_PB_Encoder pb_encoder = PB_ENCODER::BEST;
  AMK_ENCODER::PB2CNF_AMK_Encoder amk_encoder = AMK_ENCODER::BEST;
  AMO_ENCODER::PB2CNF_AMO_Encoder amo_encoder = AMO_ENCODER::BEST;
  BIMANDER_M_IS::BIMANDER_M_IS bimander_m_is = BIMANDER_M_IS::N_HALF;
  BIMANDER_AUX_PATTERN::BIMANDER_AUX_PATTERN bimander_aux_pattern = BIMANDER_AUX_PATTERN::GRAY;
  int bimander_m = 3;
  int bimander_offset = 0;
  bool bimander_enforce_aux_var_domain = false;
  int k_product_minimum_lit_count_for_splitting = 10;
  int k_product_k = 2;
  int commander_encoding_k = 3;
  int64_t MAX_CLAUSES_PER_CONSTRAINT = 1000000;
  bool use_formula_cache = false;
  bool print_used_encodings = false;
  bool check_for_dup_literals = false;
  bool use_gac_binary_merge = false;
  bool binary_merge_no_support_for_single_bits = true;
  bool use_recursive_bdd_test = false;
  bool use_real_robdds = true;
  bool use_watch_dog_encoding_in_binary_merger = false;

  std::string debug_value = "";
  bool just_approximate = false;
  int64_t approximate_max_value = 1000;
  std::set<std::string> cmd_line_options;

  PBConfigClass() = default;
  virtual ~PBConfigClass() = default;

  std::string config_name = "";
};

typedef std::shared_ptr<PBConfigClass> PBConfig;
#endif  // PBCONFIG_H
