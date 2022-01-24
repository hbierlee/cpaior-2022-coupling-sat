include "unary_encode.mzn";
include "redefs_int_lin.mzn";
include "redefs_int_element.mzn";
include "arithmetic.mzn";

predicate int_abs(var int: a, int: b) =
  a >= max(0,b) /\ a == b;

predicate int_abs(int: a, var int: b) =
  abs(a) == b;

predicate int_abs(var int: a, var int: b) =
  if has_sat_ann(a, binary_encoded) \/ has_sat_ann(a, binary_encoded) then
    int_abs_binary(a, b)
  elseif has_sat_ann(a, unary_encoded) \/ has_sat_ann(a, unary_encoded) then
    int_abs_unary(a, b)
  elseif has_sat_ann(a, order_encoded) \/ has_sat_ann(a, order_encoded) then
    int_abs_order(a, b)
  else
       annotate_sat_encoding(a, SAT_INT_ABS_DEFAULT_ENCODING)
    /\ int_abs(a, b)
  endif;

predicate int_div(int: x, int: y, int: z) =
  x div y == z; % Needed for tests/spec/unit/division/test_div1.mzn

predicate int_div(var int: x, var int: y, var int: z) =
  let {
    constraint assert(not (0 in dom(y)), "0 should not be in the domain of the divisor");
  } in
  if has_sat_ann(x, unary_encoded) \/ has_sat_ann(y, unary_encoded) \/ has_sat_ann(z, unary_encoded) then
    int_div_unary(x, y, z)
  elseif has_sat_ann(x, binary_encoded) \/ has_sat_ann(y, binary_encoded) \/ has_sat_ann(z, binary_encoded)
    \/ has_sat_ann(x, order_encoded) \/ has_sat_ann(y, order_encoded) \/ has_sat_ann(z, order_encoded) then
      int_div_binary(x, y, z)
  else
       annotate_sat_encoding(x, SAT_INT_DIV_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(y, SAT_INT_DIV_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(z, SAT_INT_DIV_DEFAULT_ENCODING)
    /\ int_div(x, y, z)
  endif;

predicate int_eq(int: a, int: b) =
  a == b;

predicate int_eq(var int: a, int: b) =
    b in dom(a) /\
  % TODO do this for all available encodings (but only when binary actually propagates)
    if has_sat_ann(a, unary_encoded) then int_eq_unary(a, b) endif /\
    if has_sat_ann(a, order_encoded) then int_eq_order(a, b) endif /\
    if has_sat_ann(a, binary_encoded) then int_eq_binary(a, b) endif /\
    if not has_sat_ann(a, unary_encoded) /\ not has_sat_ann(a, order_encoded) /\ not has_sat_ann(a, binary_encoded) then
         annotate_sat_encoding(a, SAT_INT_EQUALITY_DEFAULT_ENCODING)
      /\ int_eq(a, b)
    endif;

predicate int_eq(int: a, var int: b) =
  int_eq(b, a);

% returns conjunction of vars
function array[int] of var bool: int_eq_var_par_func(int: a, int: b) =
  if a == b then [true] else [false] endif;

function array[int] of var bool: int_eq_var_par_func(int: a, var int: b) =
  int_eq_var_par_func(b, a);

% # TODO should actually (maybe) return lits and negated lits (in bool_clause format)
function array[int] of var bool: int_eq_var_par_func(var int: a, int: b) =
  if b in dom(a) then
    let {
      array[int] of bool: encs = get_sat_encodings(a, SAT_INT_EQUALITY_ENCODING_PREFS);
    } in if encs[1] then
           int_eq_var_par_unary_func(a,b)
         elseif encs[2] then
           int_eq_var_par_order_func(a,b)
         elseif encs[3] then
           int_eq_var_par_binary_func(a,b)
          else
            let {
              constraint abort("unknown encoding");
            } in [false]
         endif
  else
    [false]
  endif;

% function array[int, int] of var bool: int_eq_var_var_func(var int: a, int: b) = # TODO do this?
function array[int, int] of var bool: int_eq_var_var_func(var int: a, var int: b) =
  let {
    array[int] of bool: encs = get_sat_encodings([a,b], SAT_INT_EQUALITY_ENCODING_PREFS);
  } in
    if encs[1] then
      int_eq_var_var_unary_func(a,b)
    elseif encs[2] then
      int_eq_var_var_order_func(a,b)
    elseif encs[3] then
      int_eq_var_var_binary_func(a,b)
     else
       let {
         constraint abort("no or unknown encoding");
       } in [|true,false|]
    endif;

predicate int_eq(var int: a, var int: b) =
  % TODO why is this one necessary for "constraint xs[1] = 1;"?
  % TODO add in binary_encode(..) = order_encode(..) ..- for CSE sake
  % trivial
  % (not (ub(a) < lb(b) \/ ub(b) < lb(a))) /\
  if card(dom(a) intersect dom(b)) == 0 then
    false
  else
    % binary
    if has_sat_ann(a, binary_encoded) /\ has_sat_ann(b, binary_encoded) then
      int_eq_binary(a, b)
      % binary_encode(a) == binary_encode(b)
    elseif has_sat_ann(a, binary_encoded) /\ has_sat_ann(b, unary_encoded) then
      channel_unary_binary_two_way(unary_encode(b), binary_encode(a))
    elseif has_sat_ann(a, binary_encoded) /\ has_sat_ann(b, order_encoded) then
      channel_order_binary_two_way(order_encode(b), binary_encode(a))
    % unary
    elseif has_sat_ann(a, unary_encoded) /\ has_sat_ann(b, unary_encoded) then
      int_eq_unary(a, b)
      % unary_encode(a) == unary_encode(b)
    elseif has_sat_ann(a, unary_encoded) /\ has_sat_ann(b, binary_encoded) then
      channel_unary_binary_two_way(unary_encode(a), binary_encode(b))
    elseif has_sat_ann(a, unary_encoded) /\ has_sat_ann(b, order_encoded) then
      channel_unary_order_two_way(unary_encode(a), order_encode(b))
    % order
    elseif has_sat_ann(a, order_encoded) /\ has_sat_ann(b, order_encoded) then
      int_eq_order(a, b)
      % order_encode(a) == order_encode(b)
    elseif has_sat_ann(a, order_encoded) /\ has_sat_ann(b, binary_encoded) then
      channel_order_binary_two_way(order_encode(a), binary_encode(b))
    elseif has_sat_ann(a, order_encoded) /\ has_sat_ann(b, unary_encoded) then
      channel_unary_order(unary_encode(b), order_encode(a))
    % one or the other has an encoding
    elseif has_sat_ann(a, unary_encoded) \/ has_sat_ann(b, unary_encoded) then
      int_eq_unary(a, b)
    elseif has_sat_ann(a, order_encoded) \/ has_sat_ann(b, order_encoded) then
      int_eq_order(a, b)
    elseif has_sat_ann(a, binary_encoded) \/ has_sat_ann(b, binary_encoded) then
      int_eq_binary(a, b)
    else % neither have encodings
         annotate_sat_encoding(a, SAT_INT_EQUALITY_DEFAULT_ENCODING)
      /\ annotate_sat_encoding(b, SAT_INT_EQUALITY_DEFAULT_ENCODING)
      /\ int_eq(a, b)
    endif
  endif;


% predicate int_eq_reif(var int: a, var int: b, var bool: r) =
%   r <-> int_eq_dispatch(a, b);

% TODO what is better for r=false: int_eq_binary reified vs int_ne_binary? Adding this will use the latter
% predicate int_eq_reif(var int: a, int: b, bool: r) =
%   let {
%   } in
%   if r then a == b else a != b endif;

predicate int_eq_reif(var int: a, var int: b, bool: r) =
  abort("TODO (apparently)");

% TODO what is better for r=false: int_eq_binary reified vs int_ne_binary? Adding this will use the latter
predicate int_eq_reif(var int: a, int: b, bool: r) =
  if r then a == b else a != b endif;

% predicate int_eq_reif(var int: a, var int: b, bool: r) =
%   abort("TODO (apparently)");

predicate int_le(var int: a, var int: b) =
  int_le_mixed_imp(a,b,true);

predicate int_le_imp(var int: a, var int: b, var bool: r) =
  let {
    constraint int_le_mixed_imp(lb(a),b,r);
    constraint int_le_mixed_imp(a,ub(b),r);
  } in
  % r->int_le_mixed(a,b);
  int_le_mixed_imp(a,b,r);

% predicate int_le_reif(var int: a, var int: b, var bool: r) =
%   (int_le_mixed_imp(a,b,r)) /\ ((not r) -> (a>b));

predicate int_le_mixed(int: a, int: b) =
  a<=b;

predicate int_le_mixed_imp(int: a, var int: b, var bool: r) =
  let {
    set of SAT_encoding_modes: encs = encodings(b);
    constraint assert(if SAT_strict then card(encs)>0 endif, "strict: no reason to call int_le_mixed(par,var) if the var has no encodings.");
  } in
    if SAT_UNARY  in encs then int_le_mixed_imp(affine(b,-1), -a, r) endif /\
    if SAT_ORDER  in encs then int_le_mixed_imp(affine(b,-1), -a, r) endif /\
    if SAT_BINARY in encs then int_le_mixed_imp(affine(b,-1,-1), -a-1, r) endif;

predicate int_le_mixed_imp(var int: a, int: b, var bool: r) =
  if ub(a) <= b then true
  elseif lb(a) > b then not r
  % elseif lb(a) == b then r->(a==b)
  else  % TODO for reif we should run only one of these!
    let {
      set of SAT_encoding_modes: encs = encodings(a);
      constraint assert(if SAT_strict then card(encs)>0 endif, "strict: no reason to call int_le_mixed(var,par) if the var has no encodings.");
    } in
    if SAT_UNARY  in encs then r->int_le_unary(a, b) endif /\
    if SAT_ORDER  in encs then int_le_order_imp(a, b, r) endif /\
    if SAT_BINARY in encs then r->int_le_binary(a, b) endif
  endif;

% predicate int_le_mixed(var int: a, var int: b) =
%   int_le_mixed_imp(a,b,true);

predicate int_le_mixed_imp(var int: a, var int: b, var bool: r) =
  let {
    constraint int_le_mixed_imp(lb(a),b,r);
    constraint int_le_mixed_imp(a,ub(b),r);
  } in
  if ub(a) < lb(b) then true
  elseif lb(a) > ub(b) then not r
  else
    let {
      array[int] of SAT_encoding_modes: encs = decide_encodings([a,b], SAT_ORDER);
    } in
    if encs == [SAT_ORDER,SAT_BINARY] then
      int_le_order_binary_imp(a, b, r)
    elseif encs == [SAT_BINARY,SAT_ORDER] then
      int_le_binary_order_imp(a, b, r)
    elseif exists(e in encs)(e == SAT_ORDER) then
      int_le_order_imp(a, b, r)
    elseif exists(e in encs)(e == SAT_BINARY) then
      r->int_le_binary(a, b)
    elseif exists(e in encs)(e == SAT_UNARY) then
      r->int_le_unary(a, b)
    else
      let { constraint abort(SAT_UNKNOWN_ENCODING_ERROR); } in false
    endif
  endif;

function set of int: bit_indices(int: x, int: n, bool: pos) =
  let {
    array[int] of bool: bin = binary(x,n);
  } in { j | j in index_set(bin) where bin[j] == pos };

predicate int_le_order_binary_next_dom_imp(var bool: a_d, array[int] of var bool: binary, int: last_dominated, int: end, var bool: r) =
  let {
    int: n = length(binary);
  } in
  if not SAT_domain_aware_enc then
    forall(i in end..last_dominated)(
      let { array[int] of bool: bin =  binary(i,n) } in
      clause(
          [ binary[j] | j in 1..n where not bin[j] ],
          [ r, a_d ] ++ [ binary[j] | j in 1..n where bin[j] ],
        )
        ::expression_name_dbg("int_le_order_binary: \(a_d) -> k=\(last_dominated) [\(last_dominated)-\(end)]")
    )
  elseif last_dominated >= end then
    let {
      array[int] of var bool: consequents = [ binary[j] | j in bit_indices(last_dominated,n,false) ];
      constraint clause(
          consequents,
          [ r, a_d ],
        )
        ::expression_name_dbg("int_le_order_binary: \(a_d) -> k=\(last_dominated) [\(last_dominated)-\(end)] (\(length(consequents))/\(n))")
        ;
      set of int: last_dominated_bits = bit_indices(last_dominated,n,false);
      set of int: rest = end..last_dominated-1;
      % find the first bitstring not dominated by the current one 
      array[int] of bool: dominates = [ last_dominated_bits subset bit_indices(k,n,false) | k in reverse(rest) ];
      int: next = if end == last_dominated then end-1 else last_dominated-arg_min_extended(dominates) endif;
    } in int_le_order_binary_next_dom_imp(a_d, binary, next, end, r)
  else
    true
  endif;

% predicate int_le_order_binary(var int: a, var int: b) =
%   int_le_order_binary_imp(a,b,true);

predicate int_le_order_binary_imp(var int: a, var int: b, var bool: r) =
  let {
    array[int] of var bool: a_enc = order_encode(a);
    array[int] of var bool: b_enc = binary_encode(b);
    constraint assert(ub(b)<=binary_ub(b_enc), "ub(b)<=binary_ub(b_enc)");
    array[int] of var bool: b_enc_orderable = b_enc[..length(b_enc)-1] ++ [not b_enc[length(b_enc)]];

    int: sign_bit_val = 2^(card(index_set(b_enc))-1);
    int: binary_lb = binary_lb(b_enc);
    int: binary_ub = binary_ub(b_enc);
    array[int] of int: S = dom(a) intersect binary_lb..binary_ub;
  } in
  forall(i in index_set(S) diff {1})(
    int_le_order_binary_next_dom_imp(order_encoding_element_partial(a_enc, S[i]), b_enc_orderable, S[i]+sign_bit_val-1, S[i-1]+sign_bit_val, r)
  );

% predicate int_le_binary_order(var int: a, var int: b) =
%   int_le_binary_order_imp(a,b,true);

predicate int_le_binary_order_imp(var int: a, var int: b, var bool: r) =
  int_gt_order_binary_imp(affine(b,1,1), a, r);  % a<=b = b>=a = b>a-1 = b+1>a

predicate int_gt_order_binary_imp(var int: a, var int: b, var bool: r) = % TODO could be merged with int_le_binary_order
  int_le_order_binary_imp(affine(a,-1), affine(b,-1,-1), r);  % a>b = -a<-b = -a<=-b-1 = -a<=-b-1

predicate int_max(var int: a, int: b, int: c) =
  b==c /\ a<=c;

predicate int_max(var int: a, int: b, var int: c) =
  let {
    constraint assert(lb(c)>=b, "int_max: lb(c)==b");
    constraint assert(ub(a)==ub(c), "int_max: ub(a)==ub(c)");
    SAT_encoding_modes: enc = decide_encoding(a, SAT_ORDER);
  } in
    if enc == SAT_ORDER then
      int_max_order(a,b,c)
    elseif enc == SAT_UNARY then
      int_max_unary(a,b,c)
    elseif enc == SAT_BINARY then
      int_max_binary(a,b,c)
    else
      let { constraint abort(SAT_UNKNOWN_ENCODING_ERROR); } in false
    endif;

predicate int_max(int: a, var int: b, var int: c) =
  int_max(b, a, c);

predicate int_max(var int: a, var int: b, var int: c) =
  array_int_maximum(c,[a,b]);

predicate int_min(var int: a, int: b, int: c) =
  b==c /\ a>=c;


predicate int_min(var int: a, int: b, var int: c) =
  let {
    constraint assert(ub(c)==b, "int_min: ub(c)==b");
    constraint assert(lb(a)==lb(c), "int_min: lb(a)==lb(c)");
    SAT_encoding_modes: enc = decide_encoding(a, SAT_ORDER);
  } in
    if enc == SAT_ORDER then
      int_min_order(a,b,c)
    elseif enc == SAT_UNARY then
      int_min_unary(a,b,c)
    elseif enc == SAT_BINARY then
      int_min_binary(a,b,c)
    else
      let { constraint abort(SAT_UNKNOWN_ENCODING_ERROR); } in false
    endif;

predicate int_min(int: a, var int: b, var int: c) =
  int_min(b, a, c);

predicate int_mod(var int: a, var int: b, var int: c) =
  let {
    constraint assert(not (0 in dom(b)), "0 should not be in the domain of the divisor");
  } in
  if has_sat_ann(a, binary_encoded) \/ has_sat_ann(b, binary_encoded) \/ has_sat_ann(c, binary_encoded)
    \/ has_sat_ann(a, order_encoded) \/ has_sat_ann(b, order_encoded) \/ has_sat_ann(c, order_encoded) then
    int_mod_binary(a, b, c)
  elseif has_sat_ann(a, unary_encoded) \/ has_sat_ann(b, unary_encoded) \/ has_sat_ann(c, unary_encoded) then
    int_mod_unary(a, b, c)
  else
       annotate_sat_encoding(a, SAT_INT_MOD_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(b, SAT_INT_MOD_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(c, SAT_INT_MOD_DEFAULT_ENCODING)
    /\ int_mod(a, b, c)
  endif;

predicate int_ne(int: a, var int: b) = int_ne(b,a);

predicate int_ne(var int: a, int: b) =
  if not (b in dom(a)) then
    true
  else
    let {
      array[int] of bool: encs = get_sat_encodings(a, SAT_INT_EQUALITY_ENCODING_PREFS);
    } in forall(i in index_set(encs) where encs[i])(
         if i == 1 then int_ne_unary(a,b) endif
      /\ if i == 2 then int_ne_order(a,b) endif
      /\ if i == 3 then int_ne_binary(a,b) endif
    )
    % TODO ???????????????? why no work
    % } in [
    %     int_ne_unary(a,b),
    %     int_ne_order(a,b),
    %     int_ne_binary(a,b),
    %   ][i])
  endif;
    % TODO pre-emptive partial encoding?

predicate int_ne(var int: a, var int: b) =
  let {
    % TODO union each element
    % array[int] of bool: encs_a = get_sat_encodings(a, SAT_INT_EQUALITY_ENCODING_PREFS);
    % array[int] of bool: encs_b = get_sat_encodings(b, SAT_INT_EQUALITY_ENCODING_PREFS);
    % array[int] of bool: encs = [ encs_a[i] \/ encs_b[i] | i in index_set(encs_a) ];
    array[int] of bool: encs = get_sat_encodings(a, SAT_INT_EQUALITY_ENCODING_PREFS);
  } in forall(i in index_set(encs) where encs[i])(
       if i == 1 then int_ne_unary(a,b) endif
    /\ if i == 2 then int_ne_order(a,b) endif
    /\ if i == 3 then int_ne_binary(a,b) endif);
      % ([
        % int_ne_unary(a,b),
        % int_ne_order(a,b),
        % int_ne_binary(a,b),
      % ][i]);

% predicate int_ne_reif(var int: a, var int: b, var bool: r) =
%   not r <-> a == b;
%   % TODO why doesn't this one work for unit/division/int_div6?
%   % } in r <-> (a != b);
%   % No pre-emptive partial encoding since int_eq_reif will already take care of that

predicate int_plus(int: a, int: b, var int: c) =
  % Needed to prevent infinite recursion
  c = a+b;

predicate int_plus(int: a, var int: b, var int: c) =
  int_plus(b, a, c);

predicate int_plus(var int: a, int: b, var int: c) =
  if has_sat_ann(a, unary_encoded) \/ has_sat_ann(c, unary_encoded) then
    int_eq_unary(
      unary_encode(a),
      array1d(lb(c)-b..ub(c)-b, unary_encode(c))
    )
  elseif has_sat_ann(a, order_encoded) \/ has_sat_ann(c, order_encoded) then
    int_eq_order(
      order_encode(a),
      array1d(lb(c)-b..ub(c)-b, order_encode(c))
    )
  elseif has_sat_ann(a, binary_encoded) \/ has_sat_ann(c, binary_encoded) then
    int_plus_binary(a, b, c)
  else
       annotate_sat_encoding(a, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(c, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ int_plus(a, b, c)
  endif;

% TODO should be somehow generalized from int_plus
predicate int_minus(var int: a, var int: b, var int: c) =
  if has_sat_ann(a, unary_encoded) \/ has_sat_ann(b, unary_encoded) \/ has_sat_ann(c, unary_encoded) then
    int_minus_unary(a, b, c)
  elseif has_sat_ann(a, order_encoded) \/ has_sat_ann(b, order_encoded) \/ has_sat_ann(c, order_encoded) then
    abort("todo")
  else
       annotate_sat_encoding(a, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(b, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(c, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ int_minus(a, b, c)
  endif;

predicate int_plus(var int: a, var int: b, var int: c) =
  if has_sat_ann(a, unary_encoded) \/ has_sat_ann(b, unary_encoded) \/ has_sat_ann(c, unary_encoded) then
    int_plus_unary(a, b, c)
  elseif has_sat_ann(a, order_encoded) \/ has_sat_ann(b, order_encoded) \/ has_sat_ann(c, order_encoded) then
    int_plus_order(a, b, c)
  elseif has_sat_ann(a, binary_encoded) \/ has_sat_ann(b, binary_encoded) \/ has_sat_ann(c, binary_encoded) then
    int_plus_binary(a, b, c)
  else
       annotate_sat_encoding(a, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(b, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ annotate_sat_encoding(c, SAT_INT_PLUS_DEFAULT_ENCODING)
    /\ int_plus(a, b, c)
  endif;

predicate int_plus_reif(var int: a, var int: b, int: c, var bool: r) =
  let {
    array[int] of var bool: a_enc = unary_encode(a);
    array[int] of var bool: b_enc = unary_encode(b);
    % array[c-lb(b)..c-ub(b)] of var bool: b_enc_shift = array1d(c-lb(b)..c-ub(b), [b | b in b_enc]);
  } in
  forall(i in index_set(a_enc) union index_set(b_enc))(
  let { var bool: x = a_enc[i]::maybe_partial; var bool: y = b_enc[c-i]::maybe_partial; } in
    ((r /\ x) -> y) /\
    ((r /\ y) -> x) /\
    ((not r /\ x) -> not y) % (= not r /\ y -> not x)
  );
    % array_bool_eq_reif(
    %   a_enc,
    %   b_enc_shift,
    %   r,
    %   c,
    % );
    % array_bool_eq_reif(
    %   a_enc,
    %   [ b_enc[c - i] | i in index_set(b_enc) ],
    %   r
    % );
  % forall(i in index_set(a_enc))(
  %   (a_enc[i] == b_enc[c - i]::maybe_partial) <-> r
  % );

predicate int_pow(var int: x, int: y, var int: r) =
  let {
    constraint assert(y >= 0, "For int_pow, exponent should be non-negative");
  } in
  if y == 0 then
    r == 1
  elseif y == 1 then
    x == r
  else
    let {
      var dom(r): p;
    } in r = x*p /\ int_pow(x, y-1, p)
  endif;

predicate int_pow(var int: x, var int: y, var int: r) =
  abort("int_pow with variable exponent is not supported for SAT library");
  % TODO works decenlty, but not for order Same as linear library
  % let {
  %   array[ int, int ] of int: x2y = array2d( lb(x)..ub(x), lb(y)..ub(y),
  %     [ pow( X, Y ) | X in lb(x)..ub(x), Y in lb(y)..ub(y) ] )
  % } in r == x2y[ x, y ];

predicate int_times(int: a, int: b, var int: c) =
  % TODO [?] no idea why this is needed
  a*b==c;

predicate int_times(var int: a, int: b, var int: c) =
    if has_sat_ann(a, unary_encoded) \/ has_sat_ann(b, unary_encoded) \/ has_sat_ann(c, unary_encoded) then
      int_times_unary(a, b, c)
    elseif has_sat_ann(a, order_encoded) \/ has_sat_ann(b, order_encoded) \/ has_sat_ann(c, order_encoded) then
      int_times_order(a, b, c)
    elseif has_sat_ann(a, binary_encoded) \/ has_sat_ann(b, binary_encoded) \/ has_sat_ann(c, binary_encoded) then
      int_lin([b,-1], [a,c], 0, INT_EQ)
    else
         annotate_sat_encoding(a, SAT_INT_TIMES_DEFAULT_ENCODING)
      /\ annotate_sat_encoding(b, SAT_INT_TIMES_DEFAULT_ENCODING)
      /\ annotate_sat_encoding(c, SAT_INT_TIMES_DEFAULT_ENCODING)
      /\ int_times(a, b, c)
    endif;

predicate int_times(int: a, var int: b, var int: c) =
  int_times(b, a, c);

predicate int_times(var int: a, var int: b, var int: c) =
    if has_sat_ann(a, binary_encoded) \/ has_sat_ann(b, binary_encoded) \/ has_sat_ann(c, binary_encoded) then
      int_times_binary(a, b, c)
    elseif has_sat_ann(a, unary_encoded) \/ has_sat_ann(b, unary_encoded) \/ has_sat_ann(c, unary_encoded) then
      int_times_unary(a,b,c)
    elseif has_sat_ann(a, order_encoded) \/ has_sat_ann(b, order_encoded) \/ has_sat_ann(c, order_encoded) then
      int_times_order(a,b,c)
    else
         annotate_sat_encoding(a, SAT_INT_TIMES_DEFAULT_ENCODING)
      /\ annotate_sat_encoding(b, SAT_INT_TIMES_DEFAULT_ENCODING)
      /\ annotate_sat_encoding(c, SAT_INT_TIMES_DEFAULT_ENCODING)
      /\ int_times(a, b, c)
    endif;

% TODO maybe move to separate builtins file (for non-fzn builtins?)
% TODO std bool2int  doesn't use promise total
function var int: bool2int(var bool: b)::promise_total =
  let {
    var 0..1: x;
    constraint if SAT_encoding_mode == SAT_UNARY then
      unary_encode(x) = array1d(0..1, [not b, b])
    elseif SAT_encoding_mode == SAT_ORDER then
      order_encode(x) = array1d(0..1, [true, b])
    elseif SAT_encoding_mode == SAT_BINARY then
      binary_encode(x) = [b, false]
    else
      unary_encode(x) = array1d(0..1, [not b, b])
    endif
  } in x;
