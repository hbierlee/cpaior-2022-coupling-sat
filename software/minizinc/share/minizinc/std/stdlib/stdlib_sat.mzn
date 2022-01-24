/***
  @groupdef builtins.sat SAT redefinition helpers
  
  These functions implement helper (algorithms) for SAT 
*/  

/** @group builtins.sat Return the binary representation of `k` in `n` bits, using either unsigned (for `k>=n`) or two's complement encoding **/
function array[int] of bool: binary(int: k, int: n) = 
  let { constraint assert(k>=0, "if two_complement, k should be non-negative") } in binary(k, n, false);
function array[int] of bool: binary(int: k, int: n, bool: two_complement);

/** @group builtins.sat Build sorting network */
% TODO int -> enum
function array[int] of var bool: build_sorting_network(array[int] of var bool: xs, int: Comparator) =
  build_sorting_network(xs, Comparator, length(xs), 5.0);
function array[int] of var bool: build_sorting_network(array[int] of var bool: xs, int: Comparator, int: cardinality) =
  build_sorting_network(xs, Comparator, cardinality, 5.0);
function array[int] of var bool: build_sorting_network(array[int] of var bool: xs, int: Comparator, float: lambda) =
  build_sorting_network(xs, Comparator, length(xs), lambda);
function array[int] of var bool: build_sorting_network(array[int] of var bool: xs, int: Comparator, int: cardinality, float: lambda);

/** @group builtins.sat Encode at_most1 constraint as CNF via the pairwise method */
predicate at_most1_pairwise(array[int] of var bool: xs);

/** @group builtins.sat Encode at_most1 constraint as CNF via the bimander method */
% TODO add m overloaded version
predicate at_most1_bimander(array[int] of var bool: xs);

/** @group builtins.sat Encode at_most1 constraint as CNF via the mimander method */
predicate at_most1_mimander(array[int] of var bool: xs);

% TODO add BDDComparator enum
/** @group builtins.sat Construct BDD that reifies r for a linear PB less-than constraint */
predicate build_bdd_le(array[int] of int: as, array[int] of var bool: bs, int: c) = 
  build_bdd_le(as, bs, c, false, true);
predicate build_bdd_le(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: zero_terminal, var bool: one_terminal);

/** @group builtins.sat Construct BDD for a linear PB equality constraint */
predicate build_bdd_eq(array[int] of int: as, array[int] of var bool: bs, int: c) = 
  build_bdd_eq(as, bs, c, false, true);
predicate build_bdd_eq(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: zero_terminal, var bool: one_terminal);

/** @group builtins.sat Construct BDD for a linear PB inequality constraint */
predicate build_bdd_ne(array[int] of int: as, array[int] of var bool: bs, int: c) = 
  build_bdd_ne(as, bs, c, false, true);
predicate build_bdd_ne(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: zero_terminal, var bool: one_terminal);

/** @group options Whether to wrap the objective in a linear objective expression that can be redefined separately */
opt bool: mzn_opt_linearize_objective;

/** @group options Check whether to wrap the objective in a linear objective expression that can be redefined separately */
test mzn_check_linearize_objective() =
  if absent(mzn_opt_linearize_objective) then false
  else deopt(mzn_opt_linearize_objective) endif;
