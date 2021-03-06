#ifdef _MSC_VER
   typedef __int64 CPXLONG;
#else
   typedef long long CPXLONG;
#endif
#ifdef _WIN32
#define CPXPUBLIC      __stdcall
#else
#define CPXPUBLIC
#endif
#define CPX_STR_PARAM_MAX    512
#define CALLBACK_CUT_ARGS  CPXCENVptr xenv, void *cbdata,   int wherefrom, void *cbhandle, int *useraction_p
#define CPX_INFBOUND  1.0E+20
#define CPX_PARAMTYPE_INT    1
#define CPX_PARAMTYPE_DOUBLE 2 
#define CPX_PARAMTYPE_STRING 3
#define CPX_PARAMTYPE_LONG   4
#define CPX_ON                           1
#define CPX_OFF                          0
#define CPX_MIN                          1
#define CPX_CONTINUOUS                   'C'
#define CPX_BINARY                       'B'
#define CPX_INTEGER                      'I'
#define CPX_MIPSEARCH_TRADITIONAL        1
#define CPX_CALLBACK_MIP                      101
#define CPX_CALLBACK_MIP_CUT_LOOP             106
#define CPX_CALLBACK_MIP_CUT_LAST             114
#define CPX_CALLBACK_INFO_BEST_INTEGER        101
#define CPX_CALLBACK_INFO_BEST_REMAINING      102
#define CPX_CALLBACK_INFO_NODE_COUNT          103
#define CPX_CALLBACK_INFO_NODES_LEFT          104
#define CPX_CALLBACK_INFO_MIP_FEAS            109
#define CPX_CALLBACK_INFO_NODE_OBJVAL         205
#define CPX_CALLBACK_INFO_NODE_SEQNUM         209
#define CPX_CALLBACK_DEFAULT             0
#define CPX_CALLBACK_SET                 2
#define CPX_CALLBACK_ABORT_CUT_LOOP      3
#define CPX_USECUT_FORCE                 0
#define CPX_USECUT_PURGE                 1
#define CPX_USECUT_FILTER                2
#define CPXMESSAGEBUFSIZE 1024
#define CPXMIP_ABORT_FEAS 113
#define CPXMIP_ABORT_INFEAS 114
#define CPXMIP_ABORT_RELAXATION_UNBOUNDED 133
#define CPXMIP_FAIL_FEAS 109
#define CPXMIP_FAIL_FEAS_NO_TREE 116
#define CPXMIP_FAIL_INFEAS 110
#define CPXMIP_INFEASIBLE 103
#define CPXMIP_INForUNBD 119
#define CPXMIP_MEM_LIM_FEAS 111
#define CPXMIP_NODE_LIM_FEAS 105
#define CPXMIP_OPTIMAL 101
#define CPXMIP_OPTIMAL_INFEAS 115
#define CPXMIP_OPTIMAL_TOL 102
#define CPXMIP_SOL_LIM 104
#define CPXMIP_TIME_LIM_FEAS 107
#define CPXMIP_UNBOUNDED 118
#define CPXPARAM_Advance 1001
#define CPXPARAM_Barrier_Algorithm 3007
#define CPXPARAM_Barrier_ColNonzeros 3009
#define CPXPARAM_Barrier_ConvergeTol 3002
#define CPXPARAM_Barrier_Crossover 3018
#define CPXPARAM_Barrier_Display 3010
#define CPXPARAM_Barrier_Limits_Corrections 3013
#define CPXPARAM_Barrier_Limits_Growth 3003
#define CPXPARAM_Barrier_Limits_Iteration 3012
#define CPXPARAM_Barrier_Limits_ObjRange 3004
#define CPXPARAM_Barrier_Ordering 3014
#define CPXPARAM_Barrier_QCPConvergeTol 3020
#define CPXPARAM_Barrier_StartAlg 3017
#define CPXPARAM_Benders_Strategy 1501
#define CPXPARAM_Benders_Tolerances_feasibilitycut 1509
#define CPXPARAM_Benders_Tolerances_optimalitycut 1510
#define CPXPARAM_Benders_WorkerAlgorithm 1500
#define CPXPARAM_ClockType 1006
#define CPXPARAM_Conflict_Algorithm 1073
#define CPXPARAM_Conflict_Display 1074
#define CPXPARAM_CPUmask 1144
#define CPXPARAM_DetTimeLimit 1127
#define CPXPARAM_DistMIP_Rampup_DetTimeLimit 2164
#define CPXPARAM_DistMIP_Rampup_Duration 2163
#define CPXPARAM_DistMIP_Rampup_TimeLimit 2165
#define CPXPARAM_Emphasis_Memory 1082
#define CPXPARAM_Emphasis_MIP 2058
#define CPXPARAM_Emphasis_Numerical 1083
#define CPXPARAM_Feasopt_Mode 1084
#define CPXPARAM_Feasopt_Tolerance 2073
#define CPXPARAM_LPMethod 1062
#define CPXPARAM_MIP_Cuts_BQP 2195
#define CPXPARAM_MIP_Cuts_Cliques 2003
#define CPXPARAM_MIP_Cuts_Covers 2005
#define CPXPARAM_MIP_Cuts_Disjunctive 2053
#define CPXPARAM_MIP_Cuts_FlowCovers 2040
#define CPXPARAM_MIP_Cuts_Gomory 2049
#define CPXPARAM_MIP_Cuts_GUBCovers 2044
#define CPXPARAM_MIP_Cuts_Implied 2041
#define CPXPARAM_MIP_Cuts_LiftProj 2152
#define CPXPARAM_MIP_Cuts_LocalImplied 2181
#define CPXPARAM_MIP_Cuts_MCFCut 2134
#define CPXPARAM_MIP_Cuts_MIRCut 2052
#define CPXPARAM_MIP_Cuts_PathCut 2051
#define CPXPARAM_MIP_Cuts_RLT 2196
#define CPXPARAM_MIP_Cuts_ZeroHalfCut 2111
#define CPXPARAM_MIP_Display 2012
#define CPXPARAM_MIP_Interval 2013
#define CPXPARAM_MIP_Limits_AggForCut 2054
#define CPXPARAM_MIP_Limits_AuxRootThreads 2139
#define CPXPARAM_MIP_Limits_CutPasses 2056
#define CPXPARAM_MIP_Limits_CutsFactor 2033
#define CPXPARAM_MIP_Limits_EachCutLimit 2102
#define CPXPARAM_MIP_Limits_GomoryCand 2048
#define CPXPARAM_MIP_Limits_GomoryPass 2050
#define CPXPARAM_MIP_Limits_Nodes 2017
#define CPXPARAM_MIP_Limits_PolishTime 2066
#define CPXPARAM_MIP_Limits_Populate 2108
#define CPXPARAM_MIP_Limits_ProbeDetTime 2150
#define CPXPARAM_MIP_Limits_ProbeTime 2065
#define CPXPARAM_MIP_Limits_RepairTries 2067
#define CPXPARAM_MIP_Limits_Solutions 2015
#define CPXPARAM_MIP_Limits_StrongCand 2045
#define CPXPARAM_MIP_Limits_StrongIt 2046
#define CPXPARAM_MIP_Limits_TreeMemory 2027
#define CPXPARAM_MIP_OrderType 2032
#define CPXPARAM_MIP_PolishAfter_AbsMIPGap 2126
#define CPXPARAM_MIP_PolishAfter_DetTime 2151
#define CPXPARAM_MIP_PolishAfter_MIPGap 2127
#define CPXPARAM_MIP_PolishAfter_Nodes 2128
#define CPXPARAM_MIP_PolishAfter_Solutions 2129
#define CPXPARAM_MIP_PolishAfter_Time 2130
#define CPXPARAM_MIP_Pool_AbsGap 2106
#define CPXPARAM_MIP_Pool_Capacity 2103
#define CPXPARAM_MIP_Pool_Intensity 2107
#define CPXPARAM_MIP_Pool_RelGap 2105
#define CPXPARAM_MIP_Pool_Replace 2104
#define CPXPARAM_MIP_Strategy_Backtrack 2002
#define CPXPARAM_MIP_Strategy_BBInterval 2039
#define CPXPARAM_MIP_Strategy_Branch 2001
#define CPXPARAM_MIP_Strategy_CallbackReducedLP 2055
#define CPXPARAM_MIP_Strategy_Dive 2060
#define CPXPARAM_MIP_Strategy_File 2016
#define CPXPARAM_MIP_Strategy_FPHeur 2098
#define CPXPARAM_MIP_Strategy_HeuristicEffort 2120
#define CPXPARAM_MIP_Strategy_HeuristicFreq 2031
#define CPXPARAM_MIP_Strategy_KappaStats 2137
#define CPXPARAM_MIP_Strategy_LBHeur 2063
#define CPXPARAM_MIP_Strategy_MIQCPStrat 2110
#define CPXPARAM_MIP_Strategy_NodeSelect 2018
#define CPXPARAM_MIP_Strategy_Order 2020
#define CPXPARAM_MIP_Strategy_PresolveNode 2037
#define CPXPARAM_MIP_Strategy_Probe 2042
#define CPXPARAM_MIP_Strategy_RINSHeur 2061
#define CPXPARAM_MIP_Strategy_Search 2109
#define CPXPARAM_MIP_Strategy_StartAlgorithm 2025
#define CPXPARAM_MIP_Strategy_SubAlgorithm 2026
#define CPXPARAM_MIP_Strategy_VariableSelect 2028
#define CPXPARAM_MIP_SubMIP_StartAlg 2205
#define CPXPARAM_MIP_SubMIP_SubAlg 2206
#define CPXPARAM_MIP_SubMIP_NodeLimit 2212
#define CPXPARAM_MIP_SubMIP_Scale 2207
#define CPXPARAM_MIP_Tolerances_AbsMIPGap 2008
#define CPXPARAM_MIP_Tolerances_Linearization 2068
#define CPXPARAM_MIP_Tolerances_Integrality 2010
#define CPXPARAM_MIP_Tolerances_LowerCutoff 2006
#define CPXPARAM_MIP_Tolerances_MIPGap 2009
#define CPXPARAM_MIP_Tolerances_ObjDifference 2019
#define CPXPARAM_MIP_Tolerances_RelObjDifference 2022
#define CPXPARAM_MIP_Tolerances_UpperCutoff 2007
#define CPXPARAM_MultiObjective_Display 1600
#define CPXPARAM_Network_Display 5005
#define CPXPARAM_Network_Iterations 5001
#define CPXPARAM_Network_NetFind 1022
#define CPXPARAM_Network_Pricing 5004
#define CPXPARAM_Network_Tolerances_Feasibility 5003
#define CPXPARAM_Network_Tolerances_Optimality 5002
#define CPXPARAM_OptimalityTarget 1131
#define CPXPARAM_Output_CloneLog 1132
#define CPXPARAM_Output_IntSolFilePrefix 2143
#define CPXPARAM_Output_MPSLong 1081
#define CPXPARAM_Output_WriteLevel 1114
#define CPXPARAM_Parallel 1109
#define CPXPARAM_ParamDisplay 1163
#define CPXPARAM_Preprocessing_Aggregator 1003
#define CPXPARAM_Preprocessing_BoundStrength 2029
#define CPXPARAM_Preprocessing_CoeffReduce 2004
#define CPXPARAM_Preprocessing_Dependency 1008
#define CPXPARAM_Preprocessing_Dual 1044
#define CPXPARAM_Preprocessing_Fill 1002
#define CPXPARAM_Preprocessing_Folding 1164
#define CPXPARAM_Preprocessing_Linear 1058
#define CPXPARAM_Preprocessing_NumPass 1052
#define CPXPARAM_Preprocessing_Presolve 1030
#define CPXPARAM_Preprocessing_QCPDuals 4003
#define CPXPARAM_Preprocessing_QPMakePSD 4010
#define CPXPARAM_Preprocessing_QToLin 4012
#define CPXPARAM_Preprocessing_Reduce 1057
#define CPXPARAM_Preprocessing_Relax 2034
#define CPXPARAM_Preprocessing_RepeatPresolve 2064
#define CPXPARAM_Preprocessing_Symmetry 2059
#define CPXPARAM_QPMethod 1063
#define CPXPARAM_RandomSeed 1124
#define CPXPARAM_Read_APIEncoding 1130
#define CPXPARAM_Read_Constraints 1021
#define CPXPARAM_Read_DataCheck 1056
#define CPXPARAM_Read_FileEncoding 1129
#define CPXPARAM_Read_Nonzeros 1024
#define CPXPARAM_Read_QPNonzeros 4001
#define CPXPARAM_Read_Scale 1034
#define CPXPARAM_Read_Variables 1023
#define CPXPARAM_Read_WarningLimit 1157
#define CPXPARAM_Record 1162
#define CPXPARAM_ScreenOutput 1035
#define CPXPARAM_Sifting_Algorithm 1077
#define CPXPARAM_Sifting_Simplex 1158
#define CPXPARAM_Sifting_Display 1076
#define CPXPARAM_Sifting_Iterations 1078
#define CPXPARAM_Simplex_Crash 1007
#define CPXPARAM_Simplex_DGradient 1009
#define CPXPARAM_Simplex_Display 1019
#define CPXPARAM_Simplex_DynamicRows 1161
#define CPXPARAM_Simplex_Limits_Iterations 1020
#define CPXPARAM_Simplex_Limits_LowerObj 1025
#define CPXPARAM_Simplex_Limits_Perturbation 1028
#define CPXPARAM_Simplex_Limits_Singularity 1037
#define CPXPARAM_Simplex_Limits_UpperObj 1026
#define CPXPARAM_Simplex_Perturbation_Constant 1015
#define CPXPARAM_Simplex_Perturbation_Indicator 1027
#define CPXPARAM_Simplex_PGradient 1029
#define CPXPARAM_Simplex_Pricing 1010
#define CPXPARAM_Simplex_Refactor 1031
#define CPXPARAM_Simplex_Tolerances_Feasibility 1016
#define CPXPARAM_Simplex_Tolerances_Markowitz 1013
#define CPXPARAM_Simplex_Tolerances_Optimality 1014
#define CPXPARAM_SolutionType 1147
#define CPXPARAM_Threads 1067
#define CPXPARAM_TimeLimit 1039
#define CPXPARAM_Tune_DetTimeLimit 1139
#define CPXPARAM_Tune_Display 1113
#define CPXPARAM_Tune_Measure 1110
#define CPXPARAM_Tune_Repeat 1111
#define CPXPARAM_Tune_TimeLimit 1112
#define CPXPARAM_WorkDir 1064
#define CPXPARAM_WorkMem 1065
#define CPX_PARAM_ADVIND 1001
#define CPX_PARAM_AGGFILL 1002
#define CPX_PARAM_AGGIND 1003
#define CPX_PARAM_CLOCKTYPE 1006
#define CPX_PARAM_CRAIND 1007
#define CPX_PARAM_DEPIND 1008
#define CPX_PARAM_DPRIIND 1009
#define CPX_PARAM_PRICELIM 1010
#define CPX_PARAM_EPMRK 1013
#define CPX_PARAM_EPOPT 1014
#define CPX_PARAM_EPPER 1015
#define CPX_PARAM_EPRHS 1016
#define CPX_PARAM_SIMDISPLAY 1019
#define CPX_PARAM_ITLIM 1020
#define CPX_PARAM_ROWREADLIM 1021
#define CPX_PARAM_NETFIND 1022
#define CPX_PARAM_COLREADLIM 1023
#define CPX_PARAM_NZREADLIM 1024
#define CPX_PARAM_OBJLLIM 1025
#define CPX_PARAM_OBJULIM 1026
#define CPX_PARAM_PERIND 1027
#define CPX_PARAM_PERLIM 1028
#define CPX_PARAM_PPRIIND 1029
#define CPX_PARAM_PREIND 1030
#define CPX_PARAM_REINV 1031
#define CPX_PARAM_SCAIND 1034
#define CPX_PARAM_SCRIND 1035
#define CPX_PARAM_SINGLIM 1037
#define CPX_PARAM_TILIM 1039
#define CPX_PARAM_PREDUAL 1044
#define CPX_PARAM_PREPASS 1052
#define CPX_PARAM_DATACHECK 1056
#define CPX_PARAM_REDUCE 1057
#define CPX_PARAM_PRELINEAR 1058
#define CPX_PARAM_LPMETHOD 1062
#define CPX_PARAM_QPMETHOD 1063
#define CPX_PARAM_WORKDIR 1064
#define CPX_PARAM_WORKMEM 1065
#define CPX_PARAM_THREADS 1067
#define CPX_PARAM_CONFLICTALG 1073
#define CPX_PARAM_CONFLICTDISPLAY 1074
#define CPX_PARAM_SIFTDISPLAY 1076
#define CPX_PARAM_SIFTALG 1077
#define CPX_PARAM_SIFTITLIM 1078
#define CPX_PARAM_MPSLONGNUM 1081
#define CPX_PARAM_MEMORYEMPHASIS 1082
#define CPX_PARAM_NUMERICALEMPHASIS 1083
#define CPX_PARAM_FEASOPTMODE 1084
#define CPX_PARAM_PARALLELMODE 1109
#define CPX_PARAM_TUNINGMEASURE 1110
#define CPX_PARAM_TUNINGREPEAT 1111
#define CPX_PARAM_TUNINGTILIM 1112
#define CPX_PARAM_TUNINGDISPLAY 1113
#define CPX_PARAM_WRITELEVEL 1114
#define CPX_PARAM_RANDOMSEED 1124
#define CPX_PARAM_DETTILIM 1127
#define CPX_PARAM_FILEENCODING 1129
#define CPX_PARAM_APIENCODING 1130
#define CPX_PARAM_OPTIMALITYTARGET 1131
#define CPX_PARAM_CLONELOG 1132
#define CPX_PARAM_TUNINGDETTILIM 1139
#define CPX_PARAM_CPUMASK 1144
#define CPX_PARAM_SOLUTIONTYPE 1147
#define CPX_PARAM_WARNLIM 1157
#define CPX_PARAM_SIFTSIM 1158
#define CPX_PARAM_DYNAMICROWS 1161
#define CPX_PARAM_RECORD 1162
#define CPX_PARAM_PARAMDISPLAY 1163
#define CPX_PARAM_FOLDING 1164
#define CPX_PARAM_WORKERALG 1500
#define CPX_PARAM_BENDERSSTRATEGY 1501
#define CPX_PARAM_BENDERSFEASCUTTOL 1509
#define CPX_PARAM_BENDERSOPTCUTTOL 1510
#define CPX_PARAM_MULTIOBJDISPLAY 1600
#define CPX_PARAM_BRDIR 2001
#define CPX_PARAM_BTTOL 2002
#define CPX_PARAM_CLIQUES 2003
#define CPX_PARAM_COEREDIND 2004
#define CPX_PARAM_COVERS 2005
#define CPX_PARAM_CUTLO 2006
#define CPX_PARAM_CUTUP 2007
#define CPX_PARAM_EPAGAP 2008
#define CPX_PARAM_EPGAP 2009
#define CPX_PARAM_EPINT 2010
#define CPX_PARAM_MIPDISPLAY 2012
#define CPX_PARAM_MIPINTERVAL 2013
#define CPX_PARAM_INTSOLLIM 2015
#define CPX_PARAM_NODEFILEIND 2016
#define CPX_PARAM_NODELIM 2017
#define CPX_PARAM_NODESEL 2018
#define CPX_PARAM_OBJDIF 2019
#define CPX_PARAM_MIPORDIND 2020
#define CPX_PARAM_RELOBJDIF 2022
#define CPX_PARAM_STARTALG 2025
#define CPX_PARAM_SUBALG 2026
#define CPX_PARAM_TRELIM 2027
#define CPX_PARAM_VARSEL 2028
#define CPX_PARAM_BNDSTRENIND 2029
#define CPX_PARAM_HEURFREQ 2031
#define CPX_PARAM_MIPORDTYPE 2032
#define CPX_PARAM_CUTSFACTOR 2033
#define CPX_PARAM_RELAXPREIND 2034
#define CPX_PARAM_PRESLVND 2037
#define CPX_PARAM_BBINTERVAL 2039
#define CPX_PARAM_FLOWCOVERS 2040
#define CPX_PARAM_IMPLBD 2041
#define CPX_PARAM_PROBE 2042
#define CPX_PARAM_GUBCOVERS 2044
#define CPX_PARAM_STRONGCANDLIM 2045
#define CPX_PARAM_STRONGITLIM 2046
#define CPX_PARAM_FRACCAND 2048
#define CPX_PARAM_FRACCUTS 2049
#define CPX_PARAM_FRACPASS 2050
#define CPX_PARAM_FLOWPATHS 2051
#define CPX_PARAM_MIRCUTS 2052
#define CPX_PARAM_DISJCUTS 2053
#define CPX_PARAM_AGGCUTLIM 2054
#define CPX_PARAM_MIPCBREDLP 2055
#define CPX_PARAM_CUTPASS 2056
#define CPX_PARAM_MIPEMPHASIS 2058
#define CPX_PARAM_SYMMETRY 2059
#define CPX_PARAM_DIVETYPE 2060
#define CPX_PARAM_RINSHEUR 2061
#define CPX_PARAM_LBHEUR 2063
#define CPX_PARAM_REPEATPRESOLVE 2064
#define CPX_PARAM_PROBETIME 2065
#define CPX_PARAM_POLISHTIME 2066
#define CPX_PARAM_REPAIRTRIES 2067
#define CPX_PARAM_EPLIN 2068
#define CPX_PARAM_EPRELAX 2073
#define CPX_PARAM_FPHEUR 2098
#define CPX_PARAM_EACHCUTLIM 2102
#define CPX_PARAM_SOLNPOOLCAPACITY 2103
#define CPX_PARAM_SOLNPOOLREPLACE 2104
#define CPX_PARAM_SOLNPOOLGAP 2105
#define CPX_PARAM_SOLNPOOLAGAP 2106
#define CPX_PARAM_SOLNPOOLINTENSITY 2107
#define CPX_PARAM_POPULATELIM 2108
#define CPX_PARAM_MIPSEARCH 2109
#define CPX_PARAM_MIQCPSTRAT 2110
#define CPX_PARAM_ZEROHALFCUTS 2111
#define CPX_PARAM_HEUREFFORT 2120
#define CPX_PARAM_POLISHAFTEREPAGAP 2126
#define CPX_PARAM_POLISHAFTEREPGAP 2127
#define CPX_PARAM_POLISHAFTERNODE 2128
#define CPX_PARAM_POLISHAFTERINTSOL 2129
#define CPX_PARAM_POLISHAFTERTIME 2130
#define CPX_PARAM_MCFCUTS 2134
#define CPX_PARAM_MIPKAPPASTATS 2137
#define CPX_PARAM_AUXROOTTHREADS 2139
#define CPX_PARAM_INTSOLFILEPREFIX 2143
#define CPX_PARAM_PROBEDETTIME 2150
#define CPX_PARAM_POLISHAFTERDETTIME 2151
#define CPX_PARAM_LANDPCUTS 2152
#define CPX_PARAM_RAMPUPDURATION 2163
#define CPX_PARAM_RAMPUPDETTILIM 2164
#define CPX_PARAM_RAMPUPTILIM 2165
#define CPX_PARAM_LOCALIMPLBD 2181
#define CPX_PARAM_BQPCUTS 2195
#define CPX_PARAM_RLTCUTS 2196
#define CPX_PARAM_SUBMIPSTARTALG 2205
#define CPX_PARAM_SUBMIPSUBALG 2206
#define CPX_PARAM_SUBMIPSCAIND 2207
#define CPX_PARAM_SUBMIPNODELIMIT 2212
#define CPX_PARAM_BAREPCOMP 3002
#define CPX_PARAM_BARGROWTH 3003
#define CPX_PARAM_BAROBJRNG 3004
#define CPX_PARAM_BARALG 3007
#define CPX_PARAM_BARCOLNZ 3009
#define CPX_PARAM_BARDISPLAY 3010
#define CPX_PARAM_BARITLIM 3012
#define CPX_PARAM_BARMAXCOR 3013
#define CPX_PARAM_BARORDER 3014
#define CPX_PARAM_BARSTARTALG 3017
#define CPX_PARAM_BARCROSSALG 3018
#define CPX_PARAM_BARQCPEPCOMP 3020
#define CPX_PARAM_QPNZREADLIM 4001
#define CPX_PARAM_CALCQCPDUALS 4003
#define CPX_PARAM_QPMAKEPSDIND 4010
#define CPX_PARAM_QTOLININD 4012
#define CPX_PARAM_NETITLIM 5001
#define CPX_PARAM_NETEPOPT 5002
#define CPX_PARAM_NETEPRHS 5003
#define CPX_PARAM_NETPPRIIND 5004
#define CPX_PARAM_NETDISPLAY 5005
typedef int CPXINT;
typedef struct cpxenv *CPXENVptr;
typedef struct cpxenv const *CPXCENVptr;
typedef struct cpxchannel  *CPXCHANNELptr;
typedef struct cpxlp        *CPXLPptr;
typedef const struct cpxlp  *CPXCLPptr;
typedef char       *CPXCHARptr;
typedef const char *CPXCCHARptr;
