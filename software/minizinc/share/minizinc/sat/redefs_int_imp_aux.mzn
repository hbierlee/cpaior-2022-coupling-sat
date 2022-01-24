predicate aux_int_eq_if_1(var int: x, var int: y, var int: p) =
  if is_fixed(p) then
    if fix(p) = 1 then (x = y) else true endif
  elseif is_fixed(x) /\ is_fixed(y) then
    if fix(x) != fix(y) then (p = 0) else true endif
  else
    aux_int_le_if_1(x, y, p) /\ aux_int_ge_if_1(x, y, p)
  endif;

predicate aux_int_ge_if_0(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(y - x, p);

predicate aux_int_ge_if_1(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(y - x, 1 - p);

predicate aux_int_gt_if_0(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(y - x + 1, p);

predicate aux_int_gt_if_1(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(y - x + 1, 1 - p);

predicate aux_int_le_if_0(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(x - y, p);

predicate aux_int_le_if_1(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(x - y, 1 - p);

predicate aux_int_le_zero_if_0(var int: x, var int: p) =
  if is_fixed(p) then
    if 0==fix(p) then x<=0 else true endif         %% 0==fix !!
  elseif lb(x)>0 then
    p==1
  elseif not (0 in dom(x)) then
    let {
      constraint assert( ub(x) < infinity,
        "aux_int_le_zero_if_0: variable \(x)'s domain: dom(\(x)) = \(dom(x)), should have finite upper bound\n" ),
      set of int: sDomNeg = dom(x) intersect -infinity..-1,
      constraint assert( card( sDomNeg ) > 0,
        "Variable \(x): dom(\(x)) = \(dom(x)), but dom() intersect -inf..-1: \(sDomNeg)\n" ),
    } in
    aux_int_le_if_0( x, max( sDomNeg ), p )
  else
    assert( ub(x)<infinity, "Variable \(x) needs finite upper bound for a big-M constraint, current domain \(dom(x))" ) /\
    x <= ub(x) * p
  endif;

predicate aux_int_lt_if_0(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(x - y + 1, p);

predicate aux_int_lt_if_1(var int: x, var int: y, var int: p) =
  aux_int_le_zero_if_0(x - y + 1, 1 - p);

predicate aux_int_ne_if_1(var int: x, var int: y, var int: p) =
  if is_fixed(p) then
    if fix(p) = 1 then (x != y) else true endif
  elseif is_fixed(x) /\ is_fixed(y) then
    if fix(x) = fix(y) then (p = 0) else true endif
  else
    let { array[1..2] of var bool: q } in
      ( q[1] -> (x < y) ) /\
      ( q[2] -> (x > y) ) /\
      (sum(q) = p)
  endif;

