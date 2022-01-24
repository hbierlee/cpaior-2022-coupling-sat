predicate fzn_count_geq_reif(array[int] of var int: x, var int: y, var int: c, var bool: b) =
  b <-> (sat_count_fn(x,y) <= c);
