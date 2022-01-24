#ifndef PBCONSTRAINT_H
#define PBCONSTRAINT_H

#include <pblib/weightedlit.h>

#include <cassert>
#include <vector>

namespace PBLib {
enum Comparator { LEQ, GEQ, BOTH };

class PBConstraint {
private:
  virtual bool operator==(const PBConstraint& other) const;

protected:
  int64_t leq;
  int64_t geq;
  std::vector<PBLib::WeightedLit> weighted_literals;
  Comparator comparator;
  std::vector<int32_t> conditionals;
  int32_t reification = 0;

public:
  PBConstraint(std::vector<PBLib::WeightedLit> const& literals,
               Comparator comparator, int64_t less_eq, int64_t greater_eq);
  PBConstraint(std::vector<PBLib::WeightedLit> const& literals,
               Comparator comparator, int64_t bound);
  PBConstraint() : comparator(LEQ), leq(0), geq(0){};
  void addConditional(int32_t lit);
  void setReification(int32_t lit);
  void addConditionals(std::vector<int32_t> lits);
  void clearConditionals();
  std::vector<int32_t> const& getConditionals() const;
  const int32_t getReification() const;

  std::vector<PBLib::WeightedLit>& getWeightedLiterals();
  std::vector<PBLib::WeightedLit> const& getWeightedLiterals() const;
  int64_t getLeq() const;
  int64_t getGeq() const;
  virtual ~PBConstraint() = default;
  Comparator getComparator() const;

  PBConstraint getGeqConstraint() const;
  PBConstraint getLeqConstraint() const;

  int64_t getMinSum() const;
  int64_t getMaxSum() const;

  void setLeq(int64_t leq);
  void setGeq(int64_t geq);

  int getN() const;

  void setComparator(Comparator comparator);

  virtual void printGeq(bool errStream = false) const;
  virtual void print(bool errStream = false) const;
  virtual void printNoNL(bool errStream = false) const;
};
}  // namespace PBLib
#endif  // PBCONSTRAINT_H
