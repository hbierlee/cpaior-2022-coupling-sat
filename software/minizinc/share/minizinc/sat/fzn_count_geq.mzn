predicate fzn_count_geq(array[int] of var int: x, var int: y, var int: c) =
  sat_count_fn(x, y) <= c;

predicate fzn_count_geq(array[int] of var int: x, var int: y, int: c) =
  sat_count_geq([ x_i == y | x_i in x ], c);

predicate sat_count_geq(array[int] of var bool: xs, int: c) =
  let {
    array[int] of var bool: xs_vars = [ x | x in xs where not is_fixed(x) ];
    int: new_c = c - sum(x in xs where is_fixed(x))(bool2int(fix(x)));
  } in
    if new_c < 0 then
      false
    elseif new_c == 0 then
      forall(x in xs_vars)(not x)
    elseif new_c == 1 /\ length(xs_vars) == 2 then
      bool_clause([],xs_vars)
    elseif new_c >= length(xs_vars) then
      true
    else
      pblib_bool_count_le(xs_vars, new_c)
    endif;
