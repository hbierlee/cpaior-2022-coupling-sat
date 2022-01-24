message("\n----- MiniZinc build configuration ----")
if(BUILD_REF)
  set(STR_BUILD_REF "build ${BUILD_REF}")
endif()
message("MiniZinc version: ${libminizinc_VERSION} ${STR_BUILD_REF}")
message("Enabled drivers:")

if(TARGET minizinc_geas)
  message("\tGeas: ${GEAS_INCLUDE_DIRS}")
endif()
if(TARGET minizinc_gecode)
  message("\tGecode ${GECODE_VERSION}: ${GECODE_INCLUDE_DIRS}")
endif()
if(TARGET minizinc_osicbc)
  message("\tOSICBC ${OSICBC_VERSION}: ${OSICBC_INCLUDE_DIRS}")
endif()
if(TARGET minizinc_cplex)
  if(CPLEX_PLUGIN)
		message("\tCPLEX: (PLUGIN)")
	else()
		message("\tCPLEX ${CPLEX_VERSION}${STR_CPLEX_PLUGIN}: ${CPLEX_INCLUDE_DIRS}")
  endif()
endif()
if(TARGET minizinc_gurobi)
  if(GUROBI_PLUGIN)
		message("\tGurobi: (PLUGIN)")
	else()
		message("\tGurobi ${GUROBI_VERSION}${STR_GUROBI_PLUGIN}: ${GUROBI_INCLUDE_DIRS}")
  endif()
endif()
if(TARGET minizinc_scip)
	message("\tSCIP: (PLUGIN)")
endif()
if(TARGET minizinc_xpress)
	message("\tXPress: (PLUGIN)")
endif()
message("---------------------------------------\n")