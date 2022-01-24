% Unary encoding predicates
predicate int_eq_unary(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  forall(i in index_set(a_enc) union index_set(b_enc))(
    a_enc[i]::maybe_partial == b_enc[i]::maybe_partial
  );

predicate int_eq_unary(array[int] of var bool: a_enc, int: b) =
  a_enc[b] /\ forall(i in index_set(a_enc) diff {b})(not a_enc[i]);

function array[int,int] of var bool: int_eq_var_var_unary_func(var int: a, var int: b) =
  int_eq_var_var_unary_func(unary_encode(a), unary_encode(b));

function array[int] of var bool: int_eq_var_par_unary_func(var int: a, int: b) =
  int_eq_var_par_unary_func(unary_encode(a), b);

function array[int] of var bool: int_eq_var_par_unary_func(array[int] of var bool: a_enc, int: b) =
  [ a_enc[b]::maybe_partial ];

function array[int,int] of var bool: int_eq_var_var_unary_func(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  let {
    set of int: bounds = min(min(index_set(a_enc)), min(index_set(b_enc)))..max(max(index_set(a_enc)), max(index_set(b_enc)));
  } in array2d(
      bounds,
      1..2,
      [ if j==1 then a_enc[i]::maybe_partial else b_enc[i]::maybe_partial endif | i in bounds, j in 1..2 ]
            % TODO this array will be very big for fixed encodings with index_sets 0..0 and 1000.1000
     );

% TODO should be using _funcs perhaps to avoid duplication? Same for order/binary
predicate int_eq_unary_reif(array[int] of var bool: a_enc, int: b, var bool: r) =
  r <-> a_enc[b]::maybe_partial;

predicate int_ge_unary(array[int] of var bool: a_enc, int: b) =
  forall(i in min(index_set(a_enc))..b-1)(not a_enc[i]);

predicate int_ge_unary_reif(array[int] of var bool: a_enc, int: b, var bool: r) =
  r <-> exists(i in b..max(index_set(a_enc)))(a_enc[i]);

predicate int_le_unary(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  forall(i in index_set(a_enc))(
    % a_i implies at least one of the preceding b_0..b_j should be true
    a_enc[i] -> exists(j in max(i, min(index_set(b_enc)))..max(index_set(b_enc)))(b_enc[j])
  );

predicate int_le_unary(array[int] of var bool: a_enc, int: b) =
  forall(i in b+1..max(index_set(a_enc)))(not a_enc[i]);

predicate int_le_unary_reif(array[int] of var bool: a_enc, int: b, var bool: r) =
  r <-> exists(i in min(index_set(a_enc))..b)(a_enc[i]);

predicate int_ne_unary(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  % intersect because if i not in enc, then the clause is SAT
  forall(i in index_set(a_enc) intersect index_set(b_enc))(
    clause([],[a_enc[i],b_enc[i]])
  );

predicate int_ne_unary(array[int] of var bool: a_enc, int: b) =
  not a_enc[b]::maybe_partial;

predicate int_plus_unary(array[int] of var bool: a_enc, array[int] of var bool: b_enc, array[int] of var bool: c_enc) =
  forall(i in index_set(a_enc), j in index_set(b_enc))(
    (a_enc[i] /\ b_enc[j]) -> c_enc[i+j]::maybe_partial
  );


predicate annotate_possible_view(var int: a, var int: b, ann: encoding) =
  if not has_sat_ann(a, encoding) then
    annotate(a, SAT_is_view)
  elseif not has_sat_ann(b, encoding) then
    annotate(b, SAT_is_view)
  else % TODO [?] bug?
    true
  endif;

predicate int_lin_of_3_unary(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  let {
    % a*x+b*y+c*z=d -> a*x+b*y=d-c*z
    array[int] of var bool: A = int_times_unary(bs[1], as[1]);
    array[int] of var bool: B = int_times_unary(bs[2], as[2]);
    array[int] of var bool: C = int_plus_unary(int_times_unary(bs[3], -as[3]), c);
  } in int_plus_unary(A, B, C);

predicate int_max_unary(var int: a, var int: b, var int: c) =
  array_int_maximum(c, [a,b]);

predicate int_max_unary(var int: a, int: b, var int: c) =
  let {
    constraint abort("TODO int_max_unary; current implementation is wrong; should have exists(a_enc[..b]) <-> c[b] AND forall(i in b+1..) ( c_enc[i]==a_enc[i])) ");
    constraint assert(lb(c)>=b, "int_max_order: lb(c)>=b");
    constraint assert(ub(a)==ub(c), "int_max_order: ub(a)==ub(c)");
    constraint partial_view(c, a);
  } in
  let {
    array[int] of var bool: a_enc = unary_encode(a);
    array[int] of var bool: c_enc = unary_encode(c);
  } in forall(i in min(index_set(a_enc))..b-1)(a_enc[i] -> c_enc[b]);
    % forall(a_enc_i in unary_encode(a)[..b-1])(a_enc_i -> unary_encode(c)[b]); % TODO causes weird bug in fix behaviour in unary_encode

predicate int_min_unary(var int: a, var int: b, var int: c) =
  array_int_minimum(c, [a,b]);

% Non-standardized yet
predicate int_minus_unary(var int: a, var int: b, var int: c) =
  let {
    array[int] of var bool: a_enc = unary_encode(a);
    array[int] of var bool: b_enc = unary_encode(b);
    array[int] of var bool: c_enc = unary_encode(c);
  } in forall(i in index_set(a_enc), j in index_set(b_enc))(
    (a_enc[i] /\ b_enc[j]) -> c_enc[i-j]::maybe_partial
  );

predicate int_times_unary(var int: a, int: b, var int: c) =
  let {
    array[int] of var bool: a_enc = unary_encode(a);
    array[int] of var bool: c_enc = unary_encode(c);
    % TODO c's not covered in this loop should be set to false (although now it works implicitly because of EO(c)). So maybe it's worth it to put a double loop here.
    % TODO [?] makes a bool_eq??
  } in forall(i in index_set(a_enc))(
    a_enc[i] <-> c_enc[i*b]::maybe_partial
  );

predicate int_times_unary(var int: a, var int: b, int: c) =
  let {
    array[int] of var bool: a_enc = unary_encode(a);
    array[int] of var bool: b_enc = unary_encode(b);
  } in forall(i in index_set(a_enc)) (
    forall(j in index_set(b_enc))(
      if i * j == c then
        a_enc[i] <-> b_enc[j]
      else
        not a_enc[i] \/ not b_enc[j]
      endif
    )
  );

predicate int_times_unary(var int: a, var int: b, var int: c) =
  if card(dom(a))==2 /\ card(dom(b))==2 /\ 0 in dom(a) /\ 0 in dom(b) then
    let {
      % if the domains are {0,i} and {0,j}
      int: i = max(dom(a) diff {0});
      int: j = max(dom(b) diff {0});
      array[int] of var bool: a_enc = unary_encode(a);
      array[int] of var bool: b_enc = unary_encode(b);
      % TODO like in other places, check if we can do without problems; constraint c in {0, i*j};
      array[int] of var bool: c_enc = unary_encode(c);
      % TODO this could just use normal bool_or?
    } in ((a_enc[0] \/ b_enc[0]) <-> c_enc[0]::maybe_partial)
      /\ ((a_enc[i] /\ b_enc[j]) <-> c_enc[i*j]::maybe_partial)
  elseif card(dom(a)) * card(dom(b)) > SAT_nMZN__UnarySizeMax_intTimes \/
    ( SAT_fIntTimesBool /\ (
      %% Peter's idea for *bool. More optimal but worse values on carpet cutting.
      (card(dom(a))==2 /\ 0 in dom(a)) \/ (card(dom(b))==2 /\ 0 in dom(b))) ) then
    if card(dom(a)) > card(dom(b)) \/ ( card(dom(a))==card(dom(b)) /\ 0 in dom(b) /\ not (0 in dom(a)) ) then
      int_times(b,a,c)
    else
      let {
        set of int: s = lb(a)..ub(a);
        set of int: r = {lb(a)*lb(b), lb(a)*ub(b), ub(a)*lb(b), ub(a)*ub(b)};
        array[s] of var min(r)..max(r): ady = array1d(
          s,
          [if d in dom(a) then d*b else min(r) endif | d in s ]
        );
        % TODO I think something like this can be implemented easier with our encodings
        } in ady[a] = c                             %% use element()
      endif
  else
    let {
      set of int: r = {lb(a)*lb(b), lb(a)*ub(b), ub(a)*lb(b), ub(a)*ub(b)};
      array[int, int] of var bool: pp = unary_encode(a, b);
      array[int] of var bool: c_enc = unary_encode(c);
    } in
      c >= min(r) /\ c <= max(r) /\
      forall(i in index_set_1of2(pp), j in index_set_2of2(pp))(pp[i, j] == c_enc[i*j]::maybe_partial)
  endif;

predicate int_mod_unary(var int: x, var int: y, var int: z) =
  let {
    array[int] of var bool: x_enc = unary_encode(x);
    array[int] of var bool: y_enc = unary_encode(y);
    array[int] of var bool: z_enc = unary_encode(z);
  } in forall(i in index_set(x_enc), j in index_set(y_enc) diff {0})(
    (x_enc[i] /\ y_enc[j]) -> z_enc[i mod j]::maybe_partial
  );

predicate int_abs_unary(var int: a, var int: b) =
  let {
    array[int] of var bool: a_enc = unary_encode(a);
    array[int] of var bool: b_enc = unary_encode(b);
    int: min_pos_index = max(1, min(index_set(b_enc)));
    int: max_neg_index = min(-1, max(index_set(b_enc)));
  } in
    forall(i in index_set(b_enc[min_pos_index..]))(
      b_enc[i] <-> a_enc[i]::maybe_partial \/ a_enc[-i]::maybe_partial
    )
    /\ forall(i in index_set(b_enc[..max_neg_index]))(not b_enc[i])
    /\ a_enc[0]::maybe_partial == b_enc[0]::maybe_partial;

predicate int_div_unary(var int: x, var int: y, var int: z) =
  let {
    array[int] of var bool: x_enc = unary_encode(x);
    array[int] of var bool: y_enc = unary_encode(y);
    array[int] of var bool: z_enc = unary_encode(z);
  } in not y_enc[0]::maybe_partial
    /\ forall(i in index_set(x_enc), j in index_set(y_enc) diff {0})(
    (x_enc[i] /\ y_enc[j]) -> z_enc[i div j]::maybe_partial
  );

% Convenience functions that convert var int's to their encoding
predicate int_eq_unary(var int: a, int: b) =
  assert(b in dom(a), SAT_TRIVIAL_QUALITY_ERROR) /\
  int_eq_unary(unary_encode(a), b);

predicate int_eq_unary(var int: a, var int: b) =
  if has_ann(a, SAT_is_view) /\ has_ann(b, SAT_is_view) then
    let {
      var int: a_ = resolve_view_var(a);
      var int: b_ = resolve_view_var(b);
      constraint annotate(a_, SAT_skip_unary_consistency_constraint);
      constraint annotate(b_, SAT_skip_unary_consistency_constraint);
    } in
    let {
      array[int] of var bool: a_enc = unary_encode(a);
      array[int] of var bool: b_enc = unary_encode(b);
      constraint int_eq_unary(a_enc, b_enc);
    } in unary_encoding_constraints(a, a_enc)
  elseif has_ann(a, SAT_is_view) then
    affine_view(b, a, SAT_UNARY)
  else
    affine_view(a, b, SAT_UNARY)
  endif;


predicate int_ge_unary(var int: a, int: b) =
  int_ge_unary(unary_encode(a), b);

predicate int_ge_unary_reif(var int: a, int: b, var bool: r) =
  annotate(r, expression_name_dbg("<-> \(a) == \(b) \\/ \(a) == \(b+1) \\/ ...")) /\
  int_ge_unary_reif(unary_encode(a), b, r);

predicate int_le_unary(int: a, array[int] of var bool: b_enc) =
  abort("This should have been a call to int_ge_unary");

predicate int_le_unary(int: a, var int: b) =
  abort("This should have been a call to int_ge_unary");

predicate int_le_unary(var int: a, int: b) =
  int_le_unary(unary_encode(a), b);

predicate int_le_unary(var int: a, var int: b) =
  int_le_unary(unary_encode(a), unary_encode(b));
predicate int_le_unary_reif(int: a, array[int] of var bool: b, var bool: r) =
  abort("This should have been a call to int_ge_unary_reif");

predicate int_le_unary_reif(int: a, var int: b, var bool: r) =
  abort("This should have been a call to int_ge_unary_reif");

predicate int_le_unary_reif(var int: a, int: b, var bool: r) =
  annotate(r, expression_name_dbg("<-> \(a) == \(b) \\/ \(a) == \(b-1) \\/ ...")) /\
  int_le_unary_reif(unary_encode(a), b, r);

predicate int_ne_unary(var int: a, int: b) =
  int_ne_unary(unary_encode(a), b);

predicate int_ne_unary(var int: a, var int: b) =
  int_ne_unary(unary_encode(a), unary_encode(b));

predicate int_plus_unary(var int: a, var int: b, var int: c) =
  int_plus_unary(unary_encode(a), unary_encode(b), unary_encode(c));

