predicate fzn_count_neq(array[int] of var int: x, var int: y, var int: c) =
  sat_count_fn(x,y) != c;
