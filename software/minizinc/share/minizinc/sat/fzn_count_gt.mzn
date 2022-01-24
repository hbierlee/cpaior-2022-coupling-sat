predicate fzn_count_gt(array[int] of var int: x, var int: y, int: c) =
  fzn_count_geq(x, y, c-1);

predicate fzn_count_gt(array[int] of var int: x, var int: y, var int: c) =
  sat_count_fn(x,y) < c;
