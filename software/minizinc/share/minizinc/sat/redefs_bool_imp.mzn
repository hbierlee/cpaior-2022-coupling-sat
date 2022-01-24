predicate array_bool_and_imp(array[int] of var bool: as, bool: r) =
  if r then forall(a in as)(bool_clause([a],[])) else true endif;

predicate array_bool_and_imp(array[int] of var bool: as, var bool: r) =
  if forall(a in as)(is_fixed(a) /\ fix(a)) then % all are true
    true
  elseif exists(a in as)(is_fixed(a) /\ not fix(a)) then % one is false
    not r
  else
    forall(a in as)(bool_clause([a],[r]))
  endif;

predicate array_bool_or_imp(array[int] of var bool: as, bool: r) =
  if r then bool_clause(as,[]) else true endif;

predicate array_bool_or_imp(array[int] of var bool: as, var bool: r) =
  if forall(a in as)(is_fixed(a) /\ not fix(a)) then % all are false
    not r
  elseif exists(a in as)(is_fixed(a) /\ fix(a)) then % one is true
    true
  else
    bool_clause(as,[r])
  endif;

predicate array_bool_xor_imp(array[int] of var bool: as, bool: r) =
  abort("% TODO");

predicate bool_and_imp(var bool: p, var bool: q, var bool: r) =
  array_bool_and_imp([p,q],r);

predicate bool_eq_imp(var bool: p, var bool: q, bool: r) =
  if r then p = q else true endif;

predicate bool_eq_imp(var bool: p, var bool: q, var bool: r) =
  bool_clause([q],[p,r]) /\ bool_clause([p],[q,r]);
  % TODO [?] further chance for unification here?

predicate bool_le_imp(var bool: p, var bool: q, bool: r) =
  if r then p <= q else true endif;

predicate bool_le_imp(var bool: p, var bool: q, var bool: r) =
  bool_clause([q],[p,r]);

predicate bool_lin_eq_imp(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) =
  pblib_bool_lin_eq_impl(as, bs, c, r);

predicate bool_lin_ge_imp(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) =
  pblib_bool_lin_ge_impl(as, bs, c, r);

predicate bool_lin_le_imp(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) =
  pblib_bool_lin_le_impl(as, bs, c, r);

predicate bool_lt_imp(var bool: p, var bool: q, bool: r) =
  if r then p < q else true endif;

predicate bool_lt_imp(var bool: p, var bool: q, var bool: r) =
  bool_and_imp(not p, q, r);

predicate bool_ne_imp(var bool: p, var bool: q, bool: r) =
  if r then p != q else true endif;

predicate bool_ne_imp(var bool: p, var bool: q, var bool: r) =
  bool_xor_imp(p, q, r);

predicate bool_or_imp(var bool: p, var bool: q, var bool: r) =
  array_bool_or_imp([p,q], r);

predicate bool_xor_imp(var bool: p, var bool: q, bool: r) =
  if r then bool_xor(p,q) else true endif;

predicate bool_xor_imp(var bool: p, var bool: q, var bool: r) =
  bool_clause([],[p,q,r]) /\ bool_clause([p,q],[r]);

