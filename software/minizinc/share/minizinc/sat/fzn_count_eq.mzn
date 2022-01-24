predicate fzn_count_eq(array[int] of var int: x, var int: y, var int: c) =
  sat_count_fn(x, y) == c;

predicate fzn_count_eq(array[int] of var int: x, var int: y, int: c) =
  sat_count_eq([ x_i == y | x_i in x ], c);

predicate sat_count_eq(array[int] of var bool: xs, int: c) =
  let {
    array[int] of var bool: xs_vars = [ x | x in xs where not is_fixed(x) ];
    int: new_c = c - sum(x in xs where is_fixed(x))(bool2int(fix(x)));
  } in
    if new_c < 0 then
      false
    elseif new_c == 0 then
      forall(x in xs_vars)(not x)
    elseif new_c == 1 /\ length(xs_vars) == 2 then
      xs_vars[1] != xs_vars[2]
    elseif (new_c == length(xs_vars)) then
      forall(x in xs_vars)(x)
    elseif new_c > length(xs_vars) then
      false
    % elseif new_c == 1 then
    %   exists(xs_vars) /\ pblib_bool_at_most_one(xs_vars)
    else
      pblib_bool_count_eq(xs_vars, new_c)
    endif;

function var int: sat_count_fn(array[int] of var int: x, var int: y) =
  sum(i in index_set(x)) ( bool2int(x[i] == y) );

  % encode_count(x, y, c, EQ);
  % bool_lin_eq([ 1 | i in index_set(x)], [ x[i] == y | i in index_set(x) ], c);
  % exactly_k([ x[i] == y | i in index_set(x) ], c);
  % pblib_bool_count_eq([ x[i] == y | i in index_set(x) ], c);
  % c = sum(i in index_set(x)) ( bool2int(x[i] == y) );

