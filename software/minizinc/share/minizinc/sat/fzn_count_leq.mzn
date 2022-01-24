predicate fzn_count_leq(array[int] of var int: x, var int: y, var int: c) =
  sat_count_fn(x,y) >= c;

predicate fzn_count_leq(array[int] of var int: x, var int: y, int: c) =
  sat_count_leq([ x_i == y | x_i in x ], c);

predicate sat_count_leq(array[int] of var bool: xs, int: c) =
  let {
    array[int] of var bool: xs_vars = [ x | x in xs where not is_fixed(x) ];
    int: new_c = c - sum(x in xs where is_fixed(x))(bool2int(fix(x)));
  } in
    if new_c <= 0 then
      true
    elseif new_c == 1 then
      exists(xs_vars)
    elseif new_c == length(xs_vars) then
      forall(x in xs_vars)(x)
    elseif new_c > length(xs_vars) then
      false
    else
      pblib_bool_count_ge(xs_vars, new_c)
    endif;
