#include <minizinc/solvers/sat/sat_solparser.hh>

#include <algorithm>
#include <iostream>

namespace MiniZinc {
StateFn SATLexer::parseOutput(SATLexer* l) {
  // Ignore whitespace
  l->acceptRun(" \n\t");
  l->ignore();

  // Determine kind of message
  switch (l->next()) {
    case 'c': {
      l->ignore();
      return {SATLexer::parseComment};
    }
    case 'o': {
      l->ignore();
      return {SATLexer::parseCost};
    }
    case 'S':
    case 's': {
      l->ignore();
      return {SATLexer::parseStatus};
    }
    case 'v': {
      l->ignore();
      return {SATLexer::parseValues};
    }
    case '\0': {
      l->backup();
      return {SATLexer::parseOutput};
    }
    default: {
      l->backup();
      throw std::runtime_error(std::string("Unknown message kind ASCII `") + l->next() + "'");
    }
  }
}

StateFn SATLexer::parseComment(SATLexer* l) {
  char n;
  do {
    n = l->next();
  } while (n != '\n' && n != '\0');
  if (n == '\0') {
    l->backup();
    return {SATLexer::parseComment};
  }
  l->ignore();
  return {SATLexer::parseOutput};
}

StateFn SATLexer::parseCost(SATLexer* l) {
  // Ignore whitespace
  if (l->empty()) {
    l->acceptRun(" \t");
    l->ignore();
  }

  l->acceptRun("1234567890");
  if (l->peek() == '\0') {
    return {SATLexer::parseCost};
  }
  l->_cost = std::stoi(l->commit());
  if (l->status() == SATStatus::UNKNOWN) {
    l->_status = SATStatus::UNCERTAIN;
  }

  return {SATLexer::parseOutput};
}
StateFn SATLexer::parseStatus(SATLexer* l) {
  // Ignore whitespace
  if (l->empty()) {
    l->acceptRun(" \t");
    l->ignore();
  }

  // Read Status
  l->acceptRun("ABCDEFGHIJKLMNOPQRSTUVWXYZ");
  if (l->current().find(' ') == std::string::npos && l->peek() == ' ') {
    l->next();
    l->acceptRun("ABCDEFGHIJKLMNOPQRSTUVWXYZ");
  }
  if (l->peek() == '\0') {
    return {SATLexer::parseStatus};
  }

  std::string status = l->commit();
  if (status == "UNKNOWN") {
    l->_status = SATStatus::UNKNOWN;
  } else if (status == "UNSATISFIABLE") {
    l->_status = SATStatus::UNSATISFIABLE;
  } else if (status == "SATISFIABLE") {
    l->_status = SATStatus::UNCERTAIN;
    l->_cost = std::max(l->_cost, 0);
  } else if (status == "OPTIMUM FOUND") {
    l->_status = SATStatus::OPTIMAL;
    // set cost to at least 0 if we found a solution
    l->_cost = std::max(l->_cost, 0);
  } else {
    throw std::runtime_error("Unknown status `" + status + "'");
  }

  return {SATLexer::parseOutput};
}

StateFn SATLexer::parseValues(SATLexer* l) {
  do {
    if (l->empty()) {
      l->accept("-");
    }
    l->acceptRun("1234567890");
    if (l->peek() == '\0') {
      return {SATLexer::parseValues};
    }
    std::string cur = l->commit();
    if (!cur.empty()) {
      int lit = std::stoi(cur);

      // 0 is not a literal but an end of values indicator (in some formats)
      if (lit != 0) {
        l->_solution[abs(lit) - 1] = lit > 0;
      }
    }

    // Ignore whitespace
    l->acceptRun(" \t");
    l->ignore();
  } while (l->peek() != '\0' && l->peek() != '\n');
  if (l->peek() == '\0') {
    return {SATLexer::parseValues};
  }
  return {SATLexer::parseOutput};
}
}  // namespace MiniZinc
