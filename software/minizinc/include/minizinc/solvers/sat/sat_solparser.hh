#pragma once

#include <cassert>
#include <functional>
#include <string>
#include <utility>
#include <vector>

// A re-entrant parser for the SAT solution as output by many SAT/MaxSAT solvers
// (see http://www.satcompetition.org/2009/format-benchmarks2009.html and
// https://maxsat-evaluations.github.io/2019/rules.html). The parser technology
// is based on Rob Pike's talk on lexical scanning
// (https://www.youtube.com/watch?v=HxaD_trXwRE), and was implemented by Jip
// Dekker.

/*
Example:
c --------------------------
c My MaxSAT Solver
c --------------------------
o 143
s OPTIMUM FOUND
v -1 2 3 -4 -5 6 -7 8 9 10 -11 -12 13 -14 -15 16 -17 18 19 20
*/

namespace MiniZinc {
class SATLexer;

struct StateFn {
  using FnType = std::function<StateFn(SATLexer*)>;
  // TODO weird clang-tidy fix from
  FnType fn;
  StateFn(FnType fn) : fn(std::move(fn)) {}
  StateFn operator()(SATLexer* l) const { return fn(l); }
};

enum SATStatus {
  UNKNOWN = -1,       // No solutions yet
  OPTIMAL = 0,        // Optimal solution has been found
  UNCERTAIN = 1,      // At least one solution, but maybe non-optimal
  UNSATISFIABLE = 2,  // No solutions exist
};

class SATLexer {
private:
  StateFn _state;

  std::string _source;
  size_t _start, _pos;

  int _cost = -1;
  std::vector<bool> _solution;
  SATStatus _status = UNKNOWN;

protected:
  std::string current() const { return _source.substr(_start, _pos - _start); }
  std::string commit() {
    std::string cur = current();
    _start = _pos;
    return cur;
  }
  bool empty() const { return _start == _pos; }
  void ignore() { _start = _pos; }
  void backup() {
    assert(_pos > _start);  // You don't want to backup past start
    _pos -= 1;
  }
  char next() {
    assert(_pos <= _source.size());  // You don't want to advance past \0
    return _source[_pos++];
  }
  char peek() const { return _source[_pos]; }
  bool accept(std::string accepted) {
    if (accepted.find(next()) != std::string::npos) {
      return true;
    }
    backup();
    return true;
  }
  void acceptRun(std::string accepted) {
    while (accepted.find(next()) != std::string::npos) {
    };
    backup();
  }

public:
  static StateFn parseOutput(SATLexer*);
  static StateFn parseComment(SATLexer*);
  static StateFn parseCost(SATLexer*);
  static StateFn parseStatus(SATLexer*);
  static StateFn parseValues(SATLexer*);

  SATLexer(size_t num_lit) : _state(parseOutput), _start(0), _pos(0), _solution(num_lit){};
  ~SATLexer() = default;

  void parseData(const char* data) {
    _source += std::string(data);
    while (_pos < _source.size()) {
      _state = _state(this);
    }
    assert(_pos <= _source.size());  // Position should remain behind end of string
    _source = _source.substr(_start);
    _pos = _pos - _start;
    _start = 0;
  };

  SATStatus status() const { return _status; };
  bool getLiteralValue(long l) const { return l > 0 ? _solution[l - 1] : !_solution[-l - 1]; };
  int cost() const { return _cost; }
  const std::vector<bool>& solution() const { return _solution; }
};
}  // namespace MiniZinc
