#ifndef __MINIZINC_SAT_READ_SOL_HH__
#define __MINIZINC_SAT_READ_SOL_HH__

#include <minizinc/solns2out.hh>
#include <minizinc/solvers/sat/sat_model.hh>
#include <minizinc/solvers/sat/sat_solparser.hh>

#include "minizinc/ast.hh"

#include <cstring>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

using namespace std;

namespace MiniZinc {

// Receives solver output chunks, runs parser, handles logging and sends
// solution to MiniZinc output

class SATSolns2Out {
private:
  Solns2Out* _out;
  Model* _fzn;
  SATModel& _satModel;
  SATLexer _lexer;
  std::vector<VarDecl*> _freeVariables;

  // TODO [?] [Jip] Is this the only way to handle a dummy stream?
  std::ofstream _dummyStream;
  bool _allSolutions = false;
  bool _intermediateSolutions = false;
  bool _verbose = false;

  // Should be called after solver process finishes
  bool feedRawDataChunk(const char* data, bool do_buffer);

public:
  SATSolns2Out(Solns2Out* out0, Model* fzn, SATModel& sat_model, bool all_solutions,
               bool intermediate_solutions, bool verbose)
      : _out(out0),
        _fzn(fzn),
        _satModel(sat_model),
        _lexer(sat_model.getLiteralCount()),
        _allSolutions(all_solutions),
        _intermediateSolutions(intermediate_solutions),
        _verbose(verbose) {}

  bool feedRawDataChunk(const char* data);
  void sendSolutionToOut();
  void sendSolutionToOut(SATStatus status);

  std::ostream& getLog();

  void outputSolution(bool all_solutions, size_t free_variable_index = 0);
  const std::vector<bool>& getLastSolution() const { return _lexer.solution(); }

private:
  void assignOutputVariables();
  Expression* getExpressionValue(Expression* e);
};
}  // namespace MiniZinc

#endif
