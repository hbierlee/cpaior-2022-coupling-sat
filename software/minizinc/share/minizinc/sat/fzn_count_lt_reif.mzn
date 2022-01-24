predicate fzn_count_lt_reif(array[int] of var int: x, var int: y, var int: c, var bool: b) =
  fzn_count_leq_reif(x, y, c+1, b);
