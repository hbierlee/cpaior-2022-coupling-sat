### MiniZinc SAT Executable Solver Target

FetchContent_Declare(
  PBLib
  GIT_REPOSITORY    https://github.com/Dekker1/PBLib.git
  GIT_TAG           origin/feature/improve_bimander_distribution
)

#TODO: From CMake 3.14 this should be replaced by FetchContent_MakeAvailable(minisat)
FetchContent_GetProperties(PBLib)
if(NOT minisat_POPULATED)
  FetchContent_Populate(PBLib)
  add_subdirectory(${pblib_SOURCE_DIR} ${pblib_BINARY_DIR} EXCLUDE_FROM_ALL)
endif()

add_library(minizinc_sat OBJECT
  solvers/sat/sat_solverfactory.cpp
  solvers/sat/sat_solverinstance.cpp
  solvers/sat/sat_model.cpp
  solvers/sat/sat_solreader.cpp
  solvers/sat/sat_solparser.cpp

  include/minizinc/solvers/sat/sat_solreader.hh
  include/minizinc/solvers/sat/sat_solverfactory.hh
  include/minizinc/solvers/sat/sat_model.hh
  include/minizinc/solvers/sat/sat_solverinstance.hh
  include/minizinc/solvers/sat/sat_solparser.hh
)

target_link_libraries(minizinc_sat pblib)
add_dependencies(minizinc_sat minizinc_parser)
