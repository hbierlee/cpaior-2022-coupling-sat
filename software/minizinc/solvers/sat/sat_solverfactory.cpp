#include <minizinc/solvers/sat/sat_solverfactory.hh>
#include <minizinc/solvers/sat/sat_solverinstance.hh>

namespace MiniZinc {
namespace {
void get_wrapper() { static SATSolverFactory _sat_solverfactory; }
}  // namespace

SATSolverFactoryInitialiser::SATSolverFactoryInitialiser() { get_wrapper(); }
}  // namespace MiniZinc
