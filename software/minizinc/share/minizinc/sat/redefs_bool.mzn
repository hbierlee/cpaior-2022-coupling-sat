include "redefs_bool_aux.mzn";

predicate array_bool_and(array[int] of var bool: as, bool: r) =
  if r then
    forall(a in as)(a)
  else
    exists(a in as)(not a)
  endif;

predicate array_bool_and(array[int] of var bool: as, var bool: r) =
  % TODO in case of half-refications these should be avoided!
  clause([r],[a | a in as]) /\ forall(a in as)(clause([a],[r]));

predicate array_bool_or(array[int] of bool: as, bool: r) =
  if r then
    exists(as)
  else
    forall(a in as)(not a)
  endif;

predicate array_bool_or(array[int] of var bool: as, bool: r) =
  if r then
    let {
      array[int] of var bool: as_fixed = [ fix(a) | a in as where is_fixed(a) ];
    } in
    if exists(as_fixed) then
      true
    else
      bool_clause([ a | a in as where not is_fixed(a) ],[])
    endif
  else
    forall(a in as)(not a)
  endif;

predicate array_bool_or(array[int] of var bool: as, var bool: r) =
  if exists(a in as)(is_fixed(a) /\ fix(a)) then
    r
  else
    let {
      array[int] of var bool: as_non_fixed = [a | a in as where not is_fixed(a)];
    } in
    if length(as_non_fixed) == 0 then
      not r
    elseif length(as_non_fixed) == 1 then
      r <-> as_non_fixed[min(index_set(as_non_fixed))]
    else
      bool_clause(as_non_fixed,[r]) /\ forall(a in as_non_fixed)(bool_clause([r], [a]))
    endif
  endif;

predicate array_bool_xor(array[int] of var bool: a) =
  abort("% TODO");

predicate bool_and(var bool: p, var bool: q, var bool: r) =
  bool_clause([p],[r]) /\ bool_clause([q],[r]) /\ bool_clause([r],[p,q]);

predicate bool_clause(array[int] of var bool: as, array[int] of var bool: bs);

predicate bool_eq_reif(bool: p, bool: q, var bool: r) =
  if p == q then
    r
  else
    not r
  endif;

predicate bool_eq_reif(bool: p, var bool: q, var bool: r) =
  bool_eq_reif(q, p, r);

predicate bool_eq_reif(var bool: p, bool: q, var bool: r) =
  if q then p == r else p != r endif;

predicate bool_eq_reif(var bool: p, var bool: q, var bool: r) =
  bool_clause([r],[p,q]) /\ bool_clause([q],[p,r]) /\ bool_clause([p],[q,r]) /\ bool_clause([r,p,q],[]);

predicate bool_le(var bool: p, var bool: q) =
  bool_clause([q],[p]);

predicate bool_le_reif(bool: p, var bool: q, var bool: r) =
  if p then q == r else r endif;

predicate bool_le_reif(var bool: p, bool: q, var bool: r) =
  if q then r else p != r endif;

predicate bool_le_reif(var bool: p, var bool: q, var bool: r) =
  bool_clause([q],[q,r]) /\ bool_clause([p,r],[]) /\ bool_clause([r],[q]);

predicate bool_lin_eq(array[int] of int: as, array[int] of var bool: bs, int: c) =
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
  } in pblib_bool_lin_eq(as,bs,c);


predicate bool_lin_eq_reif(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) =
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
  } in
  if SAT_pblib_reify then
    pblib_bool_lin_eq_reif(as,bs,c, r)
  else
    let {
      var bool: p;
      var bool: q;
    } in (bool_lin_eq_imp(as, bs, c, r))
    /\ (bool_lin_le_imp(as, bs, c-1, p))
    /\ (bool_lin_ge_imp(as, bs, c+1, q))
    /\ ((not p /\ not q) <-> r)
  endif; % not p /\ not q -> not (LHS < c) /\ not (LHS > c) -> LHS == c -> r

% TODO not correct for some reason
%     var bool: p;
%     var bool: q;
%   } in % r <-> LHS == c, so r -> LHS == c /\ LHS == c -> r
%        % (r -> bool_lin_eq(as, bs, c))
%     % /\ (p -> bool_lin_le(as, bs, c-1)) % ne
%     % /\ (q -> bool_lin_ge(as, bs, c+1))
%     % /\ ((not p /\ not q) <-> r); % not p /\ not q -> not (LHS < c) /\ not (LHS > c) -> LHS == c -> r

predicate bool_lin_ge_reif(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) =
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
  } in
  if SAT_pblib_reify then
    pblib_bool_lin_ge_reif(as,bs,c, r)
  else
    let {
      var bool: p;
    } in
       (bool_lin_ge_imp(as, bs, c, r))
    /\ (bool_lin_le_imp(as, bs, c-1, p))
    /\ (p != r)
  endif;


predicate bool_lin_le_reif(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) =
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
  } in
  if SAT_pblib_reify then % TODO causes unsat on hrc
    pblib_bool_lin_le_reif(as,bs,c, r)
  else
    let {
      var bool: p;
    } in % r <-> LHS <= c, so r -> LHS <= c /\ LHS <= c -> r
      (bool_lin_le_imp(as, bs, c, r)) % r -> LHS <= c
   /\ (bool_lin_ge_imp(as, bs, c+1, p)) % p -> (LHS > c)
   /\ (p != r) % not p -> not LHS > c -> LHS <= c -> r
    % (r -> bool_lin_le(as, bs, c)) % r -> LHS <= c
 % /\ (p -> bool_lin_ge(as, bs, c+1)) % p -> (LHS > c)
 % /\ (p != r); % not p -> not LHS > c -> LHS <= c -> r
  endif;


predicate bool_lin_eq(array[int] of int: as, array[int] of var bool: bs, var int: c) =
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
    array[int] of SAT_encoding_modes: encs = get_one_sat_encoding([c], SAT_INT_EQUALITY_ENCODING_PREFS);
  } in bool_lin_eq(
    as ++ pbify_coefficients([-1], [c], encs),
    bs ++ [b_i_j | b_i_j in pbify_variables([c], encs) where not is_fixed(b_i_j)],
    -encode_int_lin_exp_constant([-1], [c], encs),
  );

predicate bool_lin_ge(array [int] of int: as, array [int] of var bool: bs, int: c) =
  % Non fzn built-in, but still convenient to have
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
  } in pblib_bool_lin_ge(as, bs, c);

predicate bool_lin_le(array [int] of int: as, array [int] of var bool: bs, int: c) =
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
  } in pblib_bool_lin_le(as, bs, c);

predicate bool_lin_le(array [int] of int: as, array [int] of var bool: bs, var int: c) =
  let {
    constraint assert(index_set(as) == index_set(bs), "Index sets of coefficients (\(index_set(as))) does not match the index set of the variables (\(index_set(bs)))");
    array[int] of SAT_encoding_modes: encs = get_one_sat_encoding([c], SAT_INT_INEQUALITY_ENCODING_PREFS);
  } in bool_lin_le(
    as ++ pbify_coefficients([-1], [c], encs),
    bs ++ [b_i_j | b_i_j in pbify_variables([c], encs) where not is_fixed(b_i_j) ],
    -encode_int_lin_exp_constant([-1], [c], encs),
  );

predicate bool_lt(var bool: p, var bool: q) =
  bool_clause([],[p]) /\ bool_clause([q],[]);

predicate bool_lt_reif(bool: p, var bool: q, var bool: r) =
  if p then not r else q == r endif;

predicate bool_lt_reif(var bool: p, bool: q, var bool: r) =
  if q then p != r else not r endif;

predicate bool_lt_reif(var bool: p, var bool: q, var bool: r) =
  bool_clause([],[p,r]) /\ bool_clause([p,r],[q]) /\  bool_clause([q],[r]);

predicate bool_not(bool: p, var bool: q) = 
  if p then not q else q endif;

predicate bool_not(var bool: p, bool: q) = 
  if q then not p else p endif;

predicate bool_not(var bool: p, var bool: q);

predicate bool_or(var bool: p, var bool: q, var bool: r) =
  bool_clause([r],[p]) /\ bool_clause([q,p],[r]) /\ bool_clause([r],[q]);

predicate bool_xor(var bool: p, var bool: q) = 
  bool_not(p,q);

predicate bool_xor(var bool: p, var bool: q, bool: r) =
  if r then bool_not(p, q) else p == q endif;

predicate bool_xor(var bool: p, var bool: q, var bool: r) =
  bool_clause([],[p,q,r]) /\ bool_clause([q,r],[p])/\ bool_clause([p,r],[q]) /\ bool_clause([p,q],[r]);

