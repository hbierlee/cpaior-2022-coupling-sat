% TODO use arg min/max to tighten loops (since outsides of arrays will be fixed - but keep first fixed lit of course)

function array[int] of var bool: int_eq_var_par_order_func(var int: a, int: b) =
  int_eq_var_par_order_func(order_encode(a), b);

function array[int] of var bool: int_eq_var_par_order_func(array[int] of var bool: a_enc, int: b) =
  [a_enc[b], not a_enc[b+1]::maybe_partial ];

function array[int,int] of var bool: int_eq_var_var_order_func(var int: a, var int: b) =
  int_eq_var_var_order_func(order_encode(a), order_encode(b));

function array[int,int] of var bool: int_eq_var_var_order_func(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  let {
    set of int: bounds = min(min(index_set(a_enc)), min(index_set(b_enc)))..max(max(index_set(a_enc)), max(index_set(b_enc)));
  } in
  array2d(
    bounds,
    1..2,
    [ if j==1 then order_encoding_element_partial(a_enc, i) else order_encoding_element_partial(b_enc, i) endif | i in bounds, j in 1..2 ]
   );

predicate int_eq_order(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  let {
    int: lb_a = min(index_set(a_enc));
    int: ub_a = max(index_set(a_enc));
    int: lb_b = min(index_set(b_enc));
    int: ub_b = max(index_set(b_enc));
  } in
     forall(i in lb_a..lb_b-1)(a_enc[i])
  /\ forall(i in lb_b..lb_a-1)(b_enc[i])
  /\ forall(i in ub_b+1..ub_a)(not a_enc[i])
  /\ forall(i in ub_a+1..ub_b)(not b_enc[i])
  /\ forall(i in index_set(a_enc) intersect index_set(b_enc))( % TODO for some reason, this can lead to e.g. bool_eq(a_enc[i], true) without an additional fixed check
    if is_fixed(a_enc[i]) then
      if fix(a_enc[i]) then
        b_enc[i]
      else
        not b_enc[i]
      endif
    elseif is_fixed(b_enc[i]) then
      if fix(b_enc[i]) then
        a_enc[i]
      else
        not a_enc[i]
      endif
    else
      b_enc[i] <-> a_enc[i]
    endif
  );

predicate int_eq_order(array[int] of var bool: a_enc, int: b) =
  forall(i in min(index_set(a_enc))..b)(a_enc[i])
  /\ forall(i in b+1..max(index_set(a_enc)))(not a_enc[i]);

predicate int_eq_order_reif(array[int] of var bool: a_enc, int: b, var bool: r) =
  r <-> (order_encoding_element_partial(a_enc,b) /\ not order_encoding_element_partial(a_enc,b+1));

% % int_le_order
% predicate int_le_order(int: a, var int: b) =
%   let {
%     constraint abort("int_le_order for par/var was called, should have redirected to var/par");
%   } in false;

% predicate int_le_order(var int: a, int: b) =
%   assert(not (ub(a) <= b \/ lb(a) > b), SAT_TRIVIAL_QUALITY_ERROR) /\
%   int_le_order(order_encode(a), b, true);

predicate int_le_order_reif(var int: a, int: b, var bool: r) =
  int_le_order_reif(order_encode(a), b, r);
predicate int_le_order_imp(var int: a, int: b, var bool: r) =
  int_le_order_imp(order_encode(a), b, r);

% predicate int_le_order(var int: a, var int: b) =
%   int_le_order_imp(a,b,true);
predicate int_le_order_imp(var int: a, var int: b, var bool: r) =
  let {
    array[int] of var bool: a_enc = order_encode(a);
    array[int] of var bool: b_enc = order_encode(b);
    set of int: D =
      if SAT_domain_aware_enc then
        let {
          set of int: A = dom(a) diff {min(dom(a))};
          set of int: B = (dom(b) diff {min(dom(b))}) union { d+1 | d in dom(b) diff {max(dom(b))} };
        } in A intersect B
      else
        index_set(a_enc) intersect index_set(b_enc)
      endif
  } in
  assert(not (ub(a) < lb(b) \/ lb(a) > ub(b)), SAT_TRIVIAL_QUALITY_ERROR) /\
  forall(i in D)(
    clause([b_enc[i]],[a_enc[i],r])
      ::expression_name_dbg("int_le_order: \(a)>=\(i)->\(b)>=\(i)")
  );


predicate int_le_order_imp(array[int] of var bool: a_enc, int: b) =
  forall(i in b+1..max(index_set(a_enc)))(not a_enc[i])  % different from imp, where we just add one clause
    ::expression_name_dbg("int_le_order on fixed \(b)")
  ;

predicate int_le_order_imp(array[int] of var bool: a_enc, int: b, var bool: r) =
    clause([],[r,order_encoding_element_partial(a_enc, b+1)])
      ::expression_name_dbg("int_le_order_imp on fixed \(b)")
  ;
predicate int_le_order_reif(array[int] of var bool: a_enc, int: b, var bool: r) =
  (r != order_encoding_element_partial(a_enc, b+1))
    ;

predicate int_ne_order(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  forall(i in index_set(a_enc) intersect index_set(b_enc))(
    (not a_enc[i] \/ a_enc[i+1]::maybe_partial \/ not b_enc[i] \/ b_enc[i+1]::maybe_partial)
      ::expression_name_dbg("x!=\(i) or y!=\(i)")
  );

predicate int_ne_order(array[int] of var bool: a_enc, int: b) =
  assert(b >= min(index_set(a_enc)), "b (\(b)) should not be 'left' of the order encoding's index set, otherwise we can't use maybe_partial") /\
  a_enc[b] <-> a_enc[b+1]::maybe_partial;

predicate int_lin_of_3_order(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  let {
    % a*x+b*y+c*z=d -> a*x+b*y=d-c*z
    array[int] of var bool: A = int_times_order(bs[1], as[1]);
    array[int] of var bool: B = int_times_order(bs[2], as[2]);
    array[int] of var bool: C = int_plus_order(int_times_order(bs[3], -as[3]), c);
  } in int_plus_order(A, B, C);

predicate int_plus_order(array[int] of var bool: a_enc, array[int] of var bool: b_enc, array[int] of var bool: c_enc) =
  % TODO tighten these loops
    % hard-coded x=i <-> x>=i /\ x<i+1 (in case forall doesn't flatten it (TODO CHECK))
    forall(i in index_set(a_enc), j in index_set(b_enc))(
     ((a_enc[i] /\ b_enc[j]) -> order_encoding_element_partial(c_enc, i+j))
     /\ ((not a_enc[i+1]::maybe_partial /\ not b_enc[j+1]::maybe_partial) -> not order_encoding_element_partial(c_enc, i+j+1)) % k = i+1+j+1-1 = i+j+1
     );
    % Old
    % let {
    %   array[int] of var bool: a_enc = unary_encode(a);
    %   array[int] of var bool: b_enc = unary_encode(b);
    %   array[int] of var bool: c_enc = unary_encode(c); %TODO ouch
    % } in forall(i in index_set(a_enc))(
    %   forall(j in index_set(b_enc))(
    %     (a_enc[i] -> c_enc[i]) /\
    %     (b_enc[j] -> c_enc[j]) /\
    %     ( (a_enc[i] /\ b_enc[j]) -> order_encoding_element_partial(c_enc, i+j) )
    %   )
    % )

predicate int_times_order(var int: a, var int: b, var int: c) =
  forall(i in dom(a), j in dom(b))(
    a == i /\ b == j -> c == i*j
    % TODO something like this could work, right?
    % let {
    %   int: k = i*j;
    % } in (a >= i /\ b >= j -> c >= k)
    %   /\ (a <  i /\ b <  j -> c <  k)
  % let {
  %   constraint SAT_trace(2, "i \(i)\n");
  %   constraint SAT_trace(2, "j \(j)\n");
  %   int: k = i*j;
  %   constraint SAT_trace(2, "k \(k)\n");
  %   var bool: a_reif = a>=i;
  %   var bool: b_reif = b>=j;
  %   var bool: c_reif = c>=k;
  %   constraint SAT_trace(2, "a_reif \(a_reif)\n");
  %   constraint SAT_trace(2, "b_reif \(b_reif)\n");
  %   constraint SAT_trace(2, "c_reif \(c_reif)\n");
  % } in
  % bool_clause([c_reif],[a_reif,b_reif]) /\ bool_clause([a_reif,b_reif],[c_reif])
  % ((a_reif /\ b_reif) -> c_reif) /\ ((not a_reif /\ not b_reif) -> not c_reif)
    % ((a_reif /\ b_reif) -> c_reif)
    % /\
    % (((not a_reif) /\ (not b_reif)) -> (not c_reif))
    % TODO not doing reif?
    % ((a >= i /\ b >= j) -> c >= k)
    % /\
    % ((a < i /\ b < j) -> c < k)
  );
  % let {
  %   array[int] of var bool: a_enc = order_encode(a);
  %   array[int] of var bool: b_enc = order_encode(b);
  %   array[int] of var bool: c_enc = order_encode(c);
  % } in
  %   forall(i in index_set(a_enc), j in index_set(b_enc))(
  %     let {
  %       int: k = i*j;
  %       constraint SAT_trace(2, "k \(k)\n");
  %     } in
  %       if k > index_set(c_enc) then
  %         a_enc[i] /\ b_enc[j] -> c_enc[i*j]
  %       endif
  %   );

predicate int_min_order(var int: a, int: b, var int: c) =
  partial_view(c, a);

predicate int_max_order(var int: a, int: b, var int: c) =
  partial_view(c, a);

% Non-standardized yet
predicate array_int_maximum_order(var int: m, array[int] of var int: x) =
  let {
    array[int] of var bool: m_enc = order_encode(m);
    array[int,int] of var bool: x_enc = order_encode(x);
    set of int: x_enc_cols = index_set_2of2(x_enc);
  } in forall(col in index_set(m_enc) union x_enc_cols)(
      if col < min(x_enc_cols) then
        m_enc[col]
      elseif col > max(x_enc_cols) then
        not m_enc[col]
      else
        exists(
          x_enc[..,col],
        ) <->
          if col < min(index_set(m_enc)) then
            true
          elseif col > max(index_set(m_enc)) then
            false
          else
            m_enc[col]
          endif
      endif
    );

predicate array_int_minimum_order(var int: m, array[int] of var int: x) =
  let {
    % 11100
    % 11000
    % 10000
    % 10000 min (ANDS)
    % 11100 max (ORS)
    array[int] of var bool: m_enc = order_encode(m);
    array[int,int] of var bool: x_enc = order_encode(x);
    set of int: x_enc_cols = index_set_2of2(x_enc);
  } in forall(col in index_set(m_enc) union x_enc_cols)(
      if col < min(x_enc_cols) then
        m_enc[col]
      elseif col > max(x_enc_cols) then
        not m_enc[col]
      else
        array_bool_and(
          x_enc[..,col],
          if col < min(index_set(m_enc)) then
            true
          elseif col > max(index_set(m_enc)) then
            false
          else
            m_enc[col]
          endif
        )
      endif
    );

predicate int_abs_order(var int: a, var int: b) =
  % b = |a|
  let {
    array[int] of var bool: a_enc = order_encode(a);
    array[int] of var bool: b_enc = order_encode(b);
  } in
    forall(i in min(index_set(b_enc))..0)(b_enc[i]) % b must be positive
    % For positive i, if f(a >= i) -> f(b >= i)
    % 21012
    % aaa1a
    % 1111b
    /\ forall(i in 0..max(index_set(a_enc)))(a_enc[i] -> order_encoding_element_partial(b_enc, i))
    % However, if f(a < i), then f(b < i) only if also f(a>=-i+1) (otherwise it could be that f(b >= i) if i is sufficiently negative)
    % 21012
    % a1aa0
    % 11110
    /\ forall(i in 0..max(index_set(a_enc)))((not a_enc[i] /\ order_encoding_element_partial(a_enc, -i+1)) -> not order_encoding_element_partial(b_enc, i))
    % For negative i, if f(a < i) -> f(b >= -i+1)
    % 21012
    % a0aaa
    % 111b1
    /\ forall(i in min(index_set(a_enc))..0)((not a_enc[i] -> order_encoding_element_partial(b_enc, -i+1)))
    % 21012
    % 1aa0a
    % 111b1
    /\ forall(i in min(index_set(a_enc))..0)((a_enc[i] /\ not order_encoding_element_partial(a_enc, -i-1) -> order_encoding_element_partial(b_enc, i)));

% switchers 
predicate int_eq_order(var int: a, int: b) =
  b in dom(a) /\
  int_eq_order(order_encode(a), b);

predicate int_eq_order(var int: a, var int: b) =
  if has_ann(a, SAT_is_view) /\ has_ann(b, SAT_is_view) then
    let {
      var int: a_ = resolve_view_var(a);
      var int: b_ = resolve_view_var(b);
      constraint annotate(a_, SAT_skip_order_consistency_constraint);
      constraint annotate(b_, SAT_skip_order_consistency_constraint);
    } in
    let {
      array[int] of var bool: a_enc = order_encode(a);
      array[int] of var bool: b_enc = order_encode(b);
      constraint int_eq_order(a_enc, b_enc);
    } in order_encoding_constraints(a, a_enc)
  elseif has_ann(a, SAT_is_view) then
    affine_view(b, a, SAT_ORDER)
  else
    affine_view(a, b, SAT_ORDER)
  endif;

predicate int_eq_order_reif(var int: a, int: b, var bool: r) =
  % annotate(r, expression_name_dbg("<-> \(b)<=\(a) /\\ \(a)<=\(b)")) /\
  int_eq_order_reif(order_encode(a), b, r);







predicate int_ne_order(var int: a, int: b) =
  int_ne_order(order_encode(a), b);

predicate int_ne_order(var int: a, var int: b) =
  int_ne_order(order_encode(a), order_encode(b));

predicate int_plus_order(var int: a, var int: b, var int: c) =
  int_plus_order(order_encode(a), order_encode(b), order_encode(c));

  % TODO remove
  % f(a >= b) /\ f(a != b) -> f(a > b) -> f(a >= b+1)
  % (order_encoding_element_partial(a_enc, b) -> order_encoding_element_partial(a_enc, b+1));
  % not f(a >= b+1) /\ f(a != b) -> f(a < b+1) /\ f(a != b) -> f(a <= b) /\ f(a != b) -> f(a < b) -> not f(a >= b)
  % /\ ( (not order_encoding_element_partial(a_enc, b+1)) -> (not order_encoding_element_partial(a_enc, b)) );
  % Simply put: if it's at least b, but cannot be b, it has to be at least b+1. If it's less than b+1, but not b, it has to be less than b
% predicate int_ne_order(var int: a, var int: b) =
%     let {
%       array[int] of var bool: a_enc = order_encode(a);
%       array[int] of var bool: b_enc = order_encode(b);
%     } in forall(i in index_set(a_enc) union index_set(b_enc))(
%       % ((a_enc[i] /\ not a_enc[i+1]::maybe_partial) -> ((not b_enc[i]) \/ b_enc[i+1]::maybe_partial)));
%       ((order_encoding_element_partial(a_enc, i) /\ not order_encoding_element_partial(a_enc, i+1))
%       -> not (order_encoding_element_partial(b_enc, i) /\ not order_encoding_element_partial(b_enc, i+1)))
%       /\
%       ((order_encoding_element_partial(b_enc, i) /\ not order_encoding_element_partial(b_enc, i+1))
%       -> not (order_encoding_element_partial(a_enc, i) /\ not order_encoding_element_partial(a_enc, i+1)))
%     );
% TODO probably equivalent;
% predicate int_abs_order(var int: a, var int: b) =
%   % b = |a|
%   let {
%     array[int] of var bool: a_enc = order_encode(a);
%     array[int] of var bool: b_enc = order_encode(b);
%   } in
%     forall(i in min(index_set(b_enc))..0)(b_enc[i]) % b must be positive
%     % For positive i, if f(a >= i) -> f(b >= i)
%     % 21012
%     % aaa1a
%     % 1111b
%     /\ forall(i in index_set(a_enc) union index_set(b_enc))((
%     order_encoding_element_partial(a_enc, i) \/ not order_encoding_element_partial(a_enc, -i+1)) <-> order_encoding_element_partial(b_enc, i))
