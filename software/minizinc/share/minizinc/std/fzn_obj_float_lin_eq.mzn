predicate fzn_obj_float_lin_eq(array[int] of float: as, array[int] of var float: bs, float: c, var float: obj) =
  float_lin_eq(as ++ [-1], bs ++ [obj], -c);
