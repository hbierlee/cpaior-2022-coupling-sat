% order encoding constraints for 
% Constrains b_i <-> x >= i (so also: not b_i <-> x < i)
% Example: 5 in 1..8 = 111100

% TODO without a trace statement, this one will be used incorrectly in tests/spec/unit/sat/encodings/test_channel_binary_order_one_way.mzn  over the var version
function array[int] of var bool: order_encode(int: x)::promise_total =
  % let {
  %   constraint SAT_trace("WARNING: calling order_encode on fixed var \(x) in \(dom(x))\n");
  % } in
  array1d(dom(x), [true]);

ann: SAT_skip_order_consistency_constraint;

function array[int] of var bool: order_encode(var int: x)::promise_total =
  let {
    constraint SAT_trace(2, "LOG: order_encode(\(x) in \(dom(x)))\n");
    constraint assert(SAT_allow_redundant_encodings \/ (not has_sat_ann(x, unary_encoded) /\ not has_sat_ann(x, binary_encoded)), "Redundant encodings not allowed but \(x) has \(get_sat_encodings(x))");
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_ORDER, "order_encode should not be called in encoding mode \(SAT_encoding_mode)");
    constraint assert(has_bounds(x), "Variable \(x) cannot be encoded since it is boundless");
  } in
  if is_fixed(x) then
    array1d(dom(x), [true])
  elseif has_ann(x, SAT_is_view) then
    let {
      constraint annotate(x, order_encoded);
      array[int] of var bool: x_enc = resolve_view(x, SAT_ORDER);
      constraint if forall(x_enc_i in x_enc)(is_fixed(x_enc_i)) then
        trace("WARNING: fully fixed x_enc \(index_set(x_enc)), \(x_enc) for \(x) in \(dom(x))\n")
        /\ x == reverse_order(array1d(index_set(x_enc), [fix(x_enc_i) | x_enc_i in x_enc])) % TODO what would fix(x_enc) do ?
        else
          set_order_encoding_as_root(x, x_enc)
      endif;
    } in x_enc
  else
    let {
      % TODO expression_name doesn't stick for some reason
      set of int: dom = dom(x);
      % TODO do this with set2ranges
      array[int] of int: dom_without_holes = [ if i in dom then i else min(dom diff min(dom)..i) endif | i in min(dom)+1..max(dom) ];
      constraint assert(length(dom_without_holes) == ub(x)-lb(x), "should be card(x)-1");
      array[int] of var bool: x_enc
      ::expression_name_dbg("order_encode(\(x))")
        = array1d(lb(x)..ub(x), [true] ++ [ order_new_var(x, i) | i in dom_without_holes ]);

      constraint order_encoding_constraints(x, x_enc);

      bool: uo = has_ann(x, unary_order_channeled);
      bool: ub = has_ann(x, unary_binary_channeled);
      bool: ob = has_ann(x, order_binary_channeled);

      constraint
        if has_sat_ann(x, unary_encoded) /\ needs_channel(uo, ub, ob) then
          annotate(x, unary_order_channeled) /\ channel_order_unary(x_enc, unary_encode(x))
        elseif has_sat_ann(x, binary_encoded) /\ needs_channel(ob, uo, ub) then
          annotate(x, order_binary_channeled) /\ channel_order_binary(x_enc, binary_encode(x))
        else
          set_order_encoding_as_root(x, x_enc) /\ order_encoding_constraints(x, x_enc)
        endif;


      constraint annotate(x, order_encoded);
    } in x_enc
  endif;

predicate set_order_encoding_as_root(var int: x, array[int] of var bool: x_enc) =
  (x = reverse_order(x_enc))::is_reverse_map;

predicate order_encoding_constraints(var int: x, array[int] of var bool: x_enc) =
  if not has_ann(x, SAT_skip_order_consistency_constraint) then
      forall(i in index_set(x_enc) diff {min(index_set(x_enc))})(
        (x_enc[i] -> x_enc[i-1])
        ::expression_name_dbg("order_encoding_constraints: \(x)>=\(i)->\(x)>=\(i-1)")
      )
  endif;

% Create a Boolean variable encoding x=value. Return through CSE, so needs value and to be a different function from the one other encoding files.
function var bool: order_new_var(var int: x, int: value) ::promise_total =
  if value <= lb(x) then
    true
  elseif value > ub(x) then
    false
  elseif value in dom(x) then
    let { var bool: xi::expression_name_dbg("\(x)>=\(value)"); } in xi
  else
    let {
      constraint abort("order_new_var was called with value \(value) outside domain of x \(x) with domain \(dom(x))");
    } in
    order_new_var(x, value + 1)
  endif;

% Array of variables
function array[int,int] of var bool: order_encode(array[int] of var int: xs) ::promise_total =
  let {
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_ORDER, "order_encode should not be called in encoding mode \(SAT_encoding_mode)");
    constraint assert(forall(x in xs)(has_bounds(x)), "An element of input array \(xs) does not have any bounds and cannot be encoded");
  } in 
  let {
    set of int: n = index_set(xs);
    set of int: m = lb_array(xs)..ub_array(xs);

    % encode each var in xs with order_encode(var int) function so that CSE will reuse earlier encodings
    array[int] of var bool: xs_enc = [
      let {
        array[int] of var bool: x_enc = order_encode(xs[i]);
      } in order_encoding_element_partial(x_enc, j)
      | i in n, j in m
    ];
  } in array2d(n, m, xs_enc);

% TODO [?] Will use of this function significantly lower performance ? (Or will it be inlined?)
function var bool: order_encoding_element_partial(array[int] of var bool: x_enc, int: i) =
  if i <= min(index_set(x_enc)) then
    true
  elseif i > max(index_set(x_enc)) then
    false
  else
    x_enc[i]
  endif;

% % Reverse mappings (order to integer)
function var int: reverse_order(array[int] of var bool: xs);
function int: reverse_order(array[int] of bool: x_enc) =
  % let {
  %   % TODO if include decreasing.mzn, we get  MiniZinc: flattening error: cannot find matching declaration
  %   % constraint assert(fix(decreasing(fix(x_enc))), "reverse_order: consistency constraint violated (decreasing(x_enc)) on order encoding \(x_enc)");
  %   constraint assert(
  %     forall(i in index_set(x_enc) diff {min(index_set(x_enc))})(
  %       (x_enc[i] -> x_enc[i-1])
  %     ), "reverse_order: consistency constraint violated (decreasing(x_enc)) on order encoding \(x_enc)");
  % } in
  if x_enc[max(index_set(x_enc))] then max(index_set(x_enc)) else arg_min(x_enc) - 1 endif;
