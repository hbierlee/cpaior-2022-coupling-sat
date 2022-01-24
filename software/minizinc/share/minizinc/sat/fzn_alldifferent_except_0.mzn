include "alldifferent_except.mzn";
predicate fzn_alldifferent_except_0(array[int] of var int: xs) =
  alldifferent_except(xs, {0});
