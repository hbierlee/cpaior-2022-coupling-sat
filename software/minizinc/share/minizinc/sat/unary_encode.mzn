% Unary encoding constraints for 
% Constrains b_i=1 <=> x=i, sum(b)=1
% Example: 5 in 1..8 = 00010000
% When x_enc encodes x, index_set(x_enc) = lb(x)..ub(x) = dom(x) but without holes (since arrays need continuous index sets), so the values in the index set denote the integer values the Booleans in x_enc encode

include "arg_max.mzn";
include "count.mzn";

% Encoding functions process
% 1. Create (direct) encoding
% 2. if SAT_ADD_ALL_ENCODING_CONSTRAINTS, then ALWAYS create atomic (AMO) constraints
% 3. if no channeling (annotations) exists (so no existing root), make this root encoding
  % but for direct encoding, if there's an order encoding, make that one the root (since order encoding atomic constraints > AMO)
% 4. if another encoding (annotation exists but no channeling (annotation), create other encoding, add channeling annotation (preventing recursion), and channel

% Functions
% Single variable
% TODO create_channeling_constraint -> parent_encoding
function array[int] of var bool: unary_encode(int: x)::promise_total =
  let {
    constraint SAT_trace("WARNING: calling unary_encode on fixed var \(x) in \(dom(x)))\n");
  } in array1d(dom(x), [true]);

ann: SAT_skip_unary_consistency_constraint;

function array[int] of var bool: unary_encode(var int: x)::promise_total =
  let {
    % TODO removing this trace causes seg fault
    constraint SAT_trace(2, "LOG: unary_encode(\(x) in \(dom(x))) \(has_sat_ann(x, SAT_is_view))\n");
    constraint assert(SAT_allow_redundant_encodings \/ (not has_sat_ann(x, order_encoded) /\ not has_sat_ann(x, binary_encoded)), "Redundant encodings not allowed");
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_UNARY, "unary_encode should not be called in encoding mode \(SAT_encoding_mode)");
    constraint assert(has_bounds(x), "Variable \(x) cannot be encoded since it is boundless");
  } in
  if is_fixed(x) then
    array1d(dom(x), [true])
  elseif has_ann(x, SAT_is_view) then
    let {
      constraint annotate(x, unary_encoded);
      array[int] of var bool: x_enc = resolve_view(x, SAT_UNARY);
      constraint set_unary_encoding_as_root(x, x_enc);
      constraint if forall(x_enc_i in x_enc)(is_fixed(x_enc_i)) then
        assert(false, "WARNING and TODO: fully fixed x_enc \(index_set(x_enc)), \(x_enc) for \(x) in \(dom(x))\n")
      endif;
    } in x_enc
  else
    let {
      constraint assert(has_bounds(x), "Variable \(x) does not have any bounds and cannot be encoded");

      % Turn domain into ranges so we don't have to check `j in domain` for every value j in the domain
      array[int] of int: dom_ranges = set_to_ranges(dom(x)) ++ [ub(x)+1];

      array[int] of var bool: x_enc
          ::expression_name_dbg("unary_encode(\(x))")
          = array1d(
        lb(x)..ub(x), [
          if j <= dom_ranges[i+1] then
            unary_new_var(x, j)
          else
            false
          endif
        | i in index_set(dom_ranges[..max(index_set(dom_ranges))-2]), j in dom_ranges[i]..dom_ranges[i+2]-1
          where i mod 2 == 1
        ]);

      constraint if SAT_ADD_ALL_ENCODING_CONSTRAINTS then
        unary_encoding_constraints(x, x_enc)
      endif;

      bool: uo = has_ann(x, unary_order_channeled);
      bool: ub = has_ann(x, unary_binary_channeled);
      bool: ob = has_ann(x, order_binary_channeled);

      constraint
        if has_sat_ann(x, order_encoded) /\ needs_channel(uo, ub, ob) then
          annotate(x, unary_order_channeled) /\ channel_unary_order(x_enc, order_encode(x))
        elseif has_sat_ann(x, binary_encoded) /\ needs_channel(ub, uo, ob) then
          annotate(x, unary_binary_channeled) /\ channel_unary_binary(x_enc, binary_encode(x))
        else
          set_unary_encoding_as_root(x, x_enc) /\ unary_encoding_constraints(x, x_enc)
        endif;

      constraint annotate(x, unary_encoded);
    } in x_enc
  endif;

% We need a channel between A and B if there's no A<->B, or if there's no A<->C<->B
function bool: needs_channel(bool: direct_path, bool: indirect_path_a, bool: indirect_path_b) =
  not direct_path /\ not (indirect_path_a /\ indirect_path_b);

predicate set_unary_encoding_as_root(var int: x, array[int] of var bool: x_enc) =
  (x = reverse_unary(x_enc))::is_reverse_map;

% TODO can use CSE to call only once (even if multiple encodings)
  % if unary -> unary_encoding_constraints elseif order -> ..
predicate unary_encoding_constraints(var int: x, array[int] of var bool: x_enc) =
  if not has_ann(x, SAT_skip_unary_consistency_constraint) then
    let {
      constraint SAT_trace("LOG: unary_encoding_constraints(\(x), \(x_enc))\n");
    } in sat_count_eq(x_enc, 1)
        ::expression_name_dbg("direct_encoding_constraints: count(\(x))==1")
  endif;

% Create (or return through CSE) a Boolean variable encoding x=value
function var bool: unary_new_var(var int: x, int: value) ::promise_total =
  let {
    constraint assert(value in dom(x), "The value \(value) was not in the domain \(dom(x)) of variable x \(x), so no unary encoding variable should be created");
    var bool: xi::expression_name_dbg("x==\(value)");
  } in xi;
  % TODO assert in domain?

%%% The same for 2 variables:
function var bool: unary_new_var(var int: x, int: i, var int: y, int: j) ::promise_total =
  if i in dom(x) /\ j in dom(y) then
    let { var bool: xi; } in xi
  else
    false
  endif;

% Array of variables
function array[int,int] of var bool: unary_encode(array[int] of var int: xs) ::promise_total =
  let {
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_UNARY, "unary_encode should not be called in encoding mode \(SAT_encoding_mode)"); 
    constraint assert(forall(x in xs)(has_bounds(x)), "An element of input array \(xs) does not have any bounds and cannot be encoded");
  } in
  let {
    set of int: n = index_set(xs);
    set of int: m = lb_array(xs)..ub_array(xs);

    % encode each var in xs with unary_encode(var int) function so that CSE will reuse earlier encodings
    array[int] of var bool: xs_enc = [
      let { array[int] of var bool: x_enc = unary_encode(xs[i]) } in
        if j in index_set(x_enc) then x_enc[j] else false endif % in case dom(xs[i]) < dom_array(xs)
      | i in n, j in m
    ];
  } in array2d(n, m, xs_enc);

% Array of parameters
function array[int,int] of bool: unary_encode(array[int] of int: xs) ::promise_total =
  let {
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_UNARY, "unary_encode should not be called in encoding mode \(SAT_encoding_mode)"); 
    set of int: n = index_set(xs);
    set of int: m = lb_array(xs)..ub_array(xs);
  } in array2d(n, m, [if i in m then j == xs[i] else false endif | i in n, j in m]);

% Dual variable encoding: x=d /\ y=e <-> xy_enc[d,e]
function array[int, int] of var bool: unary_encode(var int: x, var int: y) ::promise_total =
  let {
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_UNARY, "unary_encode should not be called in encoding mode \(SAT_encoding_mode)"); 
    constraint assert(has_bounds(x), "Variable \(x) does not have any bounds and cannot be encoded");
    constraint assert(has_bounds(y), "Variable \(y) does not have any bounds and cannot be encoded");
  } in 
  let {
    array[int] of var bool: x_enc = unary_encode(x);
    array[int] of var bool: y_enc = unary_encode(y);

    % This 2d array will always contain new variables, even if x_enc xor y_enc have been encoded in another dual variable encoding before
    array[lb(x)..ub(x), lb(y)..ub(y)] of var bool: xy_enc = array2d(
      index_set(x_enc),
      index_set(y_enc),
      [unary_new_var(x,i,y,j) | i in index_set(x_enc), j in index_set(y_enc)]
    );

    constraint sat_count_eq(array1d(xy_enc), 1);
    constraint forall(d in index_set(x_enc))(array_bool_or(xy_enc[d,..], x_enc[d]));
    constraint forall(e in index_set(y_enc))(array_bool_or(xy_enc[..,e], y_enc[e]));
    % TODO optimization: we could add a reverse mapping here too, so that x and y are only encoded once? xy_enc holds all info in x_enc and y_enc after all
  } in xy_enc;

% % Reverse mappings (unary to integer)
function var int: reverse_unary(array[int] of var bool: xs);

function int: reverse_unary(array[int] of bool: x_enc) =
  % let {
  %   % TODO cannot do == 1, since the all-false bogus intermediate solution would trip the assert
  %   % constraint assert(sum(x_enc) <= 1, "reverse_unary: consistency constraint violated (sum(x_enc) == 1) on direct encoding \(x_enc)");
  % } in
  arg_max(x_enc);
