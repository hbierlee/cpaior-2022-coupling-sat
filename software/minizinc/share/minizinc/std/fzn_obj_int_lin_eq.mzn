predicate fzn_obj_int_lin_eq(array[int] of int: as, array[int] of var int: bs, int: c, var int: obj) =
  int_lin_eq(as ++ [-1], bs ++ [obj], -c);
