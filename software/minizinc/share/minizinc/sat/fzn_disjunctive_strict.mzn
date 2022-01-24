include "fzn_disjunctive.mzn";
predicate fzn_disjunctive_strict(array[int] of var int: s, array[int] of var int: d) =
  let {
    constraint abort("unsupported");
  } in false;
predicate fzn_disjunctive_strict(array[int] of var int: s, array[int] of int: d) =
  let {
    constraint assert(forall(d_i in d)(d_i>0), "forall(d_i in d)(d_i>0) because strict not supported; uses regular disjunctive");
  } in fzn_disjunctive(s,d);

