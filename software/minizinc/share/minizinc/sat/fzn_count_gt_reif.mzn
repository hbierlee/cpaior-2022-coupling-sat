predicate fzn_count_gt_reif(array[int] of var int: x, var int: y, var int: c, var bool: b) =
  fzn_count_geq_reif(x, y, c-1, b);
