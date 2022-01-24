#ifndef SIMPLEPBCONSTRAINT_H
#define SIMPLEPBCONSTRAINT_H

#include <pblib/pbconstraint.h>

#include <cassert>
#include <vector>

enum PBTYPE { DONTCARE, AMO, AMK, PB };

class SimplePBConstraint : public PBLib::PBConstraint {
private:
  virtual bool operator==(const SimplePBConstraint& other) const;

protected:
  PBTYPE type;
  int64_t max_sum;
  int64_t max_weight;

public:
  SimplePBConstraint(int64_t max_sum, int64_t max_weight, PBTYPE type,
                     std::vector<PBLib::WeightedLit> const& literals,
                     PBLib::Comparator comparator, int64_t less_eq,
                     int64_t greater_eq);
  SimplePBConstraint(int64_t max_sum, int64_t max_weight, PBTYPE type,
                     std::vector<PBLib::WeightedLit> const& literals,
                     PBLib::Comparator comparator, int64_t bound);
  virtual ~SimplePBConstraint() = default;

  PBTYPE getType() const;
  int64_t getMaxWeight() const;
  int64_t getMaxSum() const;

  virtual void print(bool errStream = false) const;
  virtual void printNoNL(bool errStream = false) const;
};

#endif  // SIMPLEPBCONSTRAINT_H
