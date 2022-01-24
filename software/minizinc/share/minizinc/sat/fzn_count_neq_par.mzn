predicate fzn_count_neq_par(array[int] of var int: x, int: y, int: c) =
  let {
    array[int] of var bool: z = [ x_i == y | x_i in x ];
    array[int] of var bool: z_vars = [ z_i | z_i in z where not is_fixed(z_i) ];
    int: new_c = c - sum(z_i in z where is_fixed(z_i))(bool2int(fix(z_i)));
  } in
    if new_c < 0 then
      true
    elseif new_c == 0 then
      exists(z_vars)
    elseif new_c == length(z_vars) then
      exists(z_i in z_vars)(not z_i)
    elseif new_c > length(z_vars) then
      true
    else
      sat_count_fn(x,y) != c
    endif;
