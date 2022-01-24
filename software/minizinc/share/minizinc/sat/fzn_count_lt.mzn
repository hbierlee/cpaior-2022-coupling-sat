predicate fzn_count_lt(array[int] of var int: x, var int: y, int: c) =
  fzn_count_leq(x, y, c-1);

predicate fzn_count_lt(array[int] of var int: x, var int: y, var int: c) =
  sat_count_fn(x,y) > c;
