/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef __MINIZINC_SAT_SOLVER_INSTANCE_HH__
#define __MINIZINC_SAT_SOLVER_INSTANCE_HH__

#include <minizinc/ast.hh>
#include <minizinc/flattener.hh>
#include <minizinc/solver.hh>
#include <minizinc/solvers/sat/sat_model.hh>

#ifdef _WIN32
#undef ERROR
#endif

namespace MiniZinc {

class SATSolverOptions : public SolverInstanceBase::Options {
public:
  std::string solver;
  std::string extraSolverArgs;
  std::vector<std::string> satFlags;
  std::vector<MZNFZNSolverFlag> satSolverFlags;
  std::string outputDimacs;
  SATModel::SolverInputFormat solverInputFormat = SATModel::DIMACS_WCNF;
  int solverTimeLimitMs = 0;
  bool supportsWeights = true;
  bool allSolutions = false;
  bool intermediateSolutions = false;
  bool solverStatistics = false;
};

class SATSolverInstance : public SolverInstanceBase {
protected:
  Model* _fzn;
  Model* _ozn;

private:
  std::string _fznSolver;
  SATModel _satModel;

  // Statistics
  // double m_solver_d_cpu_time = 0.0;
  // std::clock_t m_solver_d_cpu_time_0 = 0;

  double _solveTime = 0.0;
  Timer _processFlatZincTimer;        // spans multiple methods, so need Timer as member
  double _processFlatZincTime = 0.0;  // time to process FlatZinc into DIMACS

  unsigned int _statBimanderCount = 0;
  unsigned int _statBimanderTotalN = 0;
  int _statBimanderTotalM = 0;
  int _statBimanderTotalOffset = 0;

public:
  SATSolverInstance(Env& env, std::ostream& log, SolverInstanceBase::Options* opt);

  ~SATSolverInstance() override;

  Status next() override { return SolverInstance::Status::ERROR; }

  Status solve() override;

  void processFlatZinc() override;

  void resetSolver() override;

  void printStatistics() override;
  void printCompilationStatistics();

protected:
  // Expression* getSolutionValue(Id* id);

  void analyse(const Item* i);
};

class SATSolverFactory : public SolverFactory {
protected:
  SolverInstanceBase* doCreateSI(Env& env, std::ostream& log,
                                 SolverInstanceBase::Options* opt) override;

public:
  SATSolverFactory();
  SolverInstanceBase::Options* createOptions() override;
  std::string getDescription(SolverInstanceBase::Options* opt = nullptr) override;
  std::string getVersion(SolverInstanceBase::Options* opt = nullptr) override;
  std::string getId() override;
  bool processOption(SolverInstanceBase::Options* opt, int& i, std::vector<std::string>& argv,
                     const std::string& workingDir = std::string()) override;
  void printHelp(std::ostream& os) override;
  // void setAcceptedFlags(SolverInstanceBase::Options* opt, const
  // std::vector<MZNFZNSolverFlag>& flags);
};

}  // namespace MiniZinc

#endif
