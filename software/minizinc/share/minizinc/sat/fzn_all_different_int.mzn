include "alldifferent_except.mzn";
predicate fzn_all_different_int(array[int] of var int: xs) =
  alldifferent_except(xs, {});
