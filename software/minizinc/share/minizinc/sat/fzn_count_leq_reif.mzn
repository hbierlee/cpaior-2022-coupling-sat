predicate fzn_count_leq_reif(array[int] of var int: x, var int: y, var int: c, var bool: b) =
   b <-> (sat_count_fn(x,y) >= c);
  % TODO bug in tests/spec/unit/globals/count/globals_count_leq_par_reif.mzn when using binary encoding and this redef from std
  % let { var int: z = count(x,y) } in b <-> z >= c;
