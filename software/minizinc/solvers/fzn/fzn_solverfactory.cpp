#include <minizinc/solvers/fzn_solverfactory.hh>
#include <minizinc/solvers/fzn_solverinstance.hh>

namespace MiniZinc {
namespace {
void get_wrapper() { static FZNSolverFactory _fznSolverfactory; }
}  // namespace
FZNSolverFactoryInitialiser::FZNSolverFactoryInitialiser() { get_wrapper(); }
}  // namespace MiniZinc
