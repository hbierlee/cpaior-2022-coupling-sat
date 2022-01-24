#ifndef BDD_Encoder_H
#define BDD_Encoder_H

#include <assert.h>
#include <pblib/PBConfig.h>
#include <pblib/SimplePBConstraint.h>
#include <pblib/auxvarmanager.h>
#include <pblib/clausedatabase.h>
#include <pblib/encoder/Encoder.h>
#include <pblib/weightedlit.h>
#include <stdlib.h>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

class BDD_Encoder : public Encoder {
private:
  bool canceled = false;

  struct build_data {
    int64_t maxsum = -1;
    int64_t currentsum = -1;
    int32_t result = 0;
    int32_t low = 0;
    int32_t high = 0;
  };

  int32_t current_node_id = 3;

  std::vector<build_data> stack;

  std::map<std::pair<int32_t, int64_t>, int32_t> sumHistory;
  std::map<std::tuple<int32_t, int32_t, int32_t>, int32_t> nodeHistory;

  int64_t k;
  // TODO perhaps move to auxvarmanager to re-use between all encoders
  int32_t true_lit;
  bool reified = false;

  int32_t test_counter = 0;

  std::vector<PBLib::WeightedLit> inputVars;

  int32_t buildBDD(int index, int64_t currentsum, int64_t maxsum,
                   ClauseDatabase& formula, AuxVarManager& auxvars);
  void recusiveEncoding(const SimplePBConstraint& pbconstraint,
                        ClauseDatabase& formula, AuxVarManager& auxvars);
  void iterativeEncoding(const SimplePBConstraint& pbconstraint,
                         ClauseDatabase& formula, AuxVarManager& auxvars,
                         bool noLimit = true, int64_t maxClauses = 0);

public:
  bool wasToBig() const;
  void bddEncode(const SimplePBConstraint& pbconstraint,
                 ClauseDatabase& formula, AuxVarManager& auxvars,
                 bool noLimit = true, int64_t maxClauses = 0);
  void encode(const SimplePBConstraint& pbconstraint, ClauseDatabase& formula,
              AuxVarManager& auxvars);

  int64_t encodingValue(const SimplePBConstraint& pbconstraint);

  BDD_Encoder(PBConfig& config) : Encoder(config) {}

  virtual ~BDD_Encoder() = default;
};

#endif  // BDD_Encoder_H
