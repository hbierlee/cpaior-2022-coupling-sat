% function var int: int_plus(array[int] of var bool: xs, int: c) =
function array[int] of var bool: array1d_shift(array[int] of var bool: xs, int: c) =
  if c == 0 then
    xs
  else
    array1d(min(index_set(xs))+c..max(index_set(xs))+c, xs)
  endif;

function array[int] of var bool: int_plus_unary(array[int] of var bool: xs, int: c) =
  array1d_shift(xs, c);

function array[int] of var bool: int_plus_order(array[int] of var bool: xs, int: c) =
  array1d_shift(xs, c);

function array[int] of var bool: int_times_unary(var int: x, int: c) =
  if c == 0 then
    let { constraint abort("int_times_unary for c=0 can be handled earlier"); } in unary_encode(0)
  else
    int_times_unary(unary_encode(x), c)
  endif;

function array[int] of var bool: int_times_unary(array[int] of var bool: x_enc, int: c) =
  if c == 0 then
    let { constraint abort("int_times_unary for c=0 can be handled earlier"); } in unary_encode(0)
  elseif c == 1 then
    x_enc
  elseif c < 0 then
    let {
      % 1..3,[a,b,c] -> -3..-1,[c,b,a]
      array[int] of var bool: y_enc = array1d(-max(index_set(x_enc))..-min(index_set(x_enc)), reverse(x_enc));
    } in int_times_unary(y_enc, abs(c))
  else
    array1d_partial({ d*c | d in index_set(x_enc) }, x_enc, false)
  endif;

function array[int] of var bool: int_times_order(var int: x, int: c) =
  if c == 0 then
    let { constraint abort("int_times_unary for c=0 can be handled earlier") } in order_encode(0)
  else
    int_times_order(order_encode(x), c)
  endif;

function array[int] of var bool: int_times_order(array[int] of var bool: x_enc, int: c) =
  if c == 0 then
    let { constraint abort("int_times_order for c=0 can be handled earlier"); } in unary_encode(0)
  elseif c == 1 then
    x_enc
  elseif c < 0 then % flip and recurse with positive c
    let {
      % 1..3, [1, f(x >= 2), f(x >= 3)] *-1 -> -3..-1, [f(x < -3), f(x < -2), 0]
      %                                     -> -4..-2, [1, f(x < -3), f(x < -2)]
      array[int] of var bool: y_enc = array1d( % flip and shift one to left (to fix left var)
        -max(index_set(x_enc))..-min(index_set(x_enc)),
        [true] ++ reverse([ not x_enc[i] | i in index_set(x_enc) diff { min(index_set(x_enc)) } ])
      );
    } in int_times_order(y_enc, abs(c))
  else % c > 1
    let {
      set of int: new_domain = { d*c | d in index_set(x_enc) };
    } in let {
      array[int] of var bool: new_x_enc = array1d_partial(
        new_domain,
        x_enc,
      );
      } in new_x_enc
  endif;

% Just like array1d, but supports non-range index sets (ie sets with holes).
% Any hole k (for which xs[k] with its new index set would be undefined) has `opt_def` values, which means xs is a new, larger array.
% Abusing opts: If opt_def is present, then xs[k]=deopt(opt_def), else then xs[k]=xs[k-1]. This latter repeating of the last defined element is useful for the order encoding.
function array[int] of var bool: array1d_partial(set of int: partial_index_set, array[int] of var bool: xs) = array1d_partial(partial_index_set, xs, <>);
function array[int] of var bool: array1d_partial(set of int: partial_index_set, array[int] of var bool: xs, opt bool: opt_def) =
  let {
    constraint assert(card(partial_index_set) == length(xs), "The cardinality of the partial_index_set should match the length of the array"); % Although if useful, we can support card<length
    set of int: new_index_set = min(partial_index_set)..max(partial_index_set);
      % || old_index_set 1..5
      % || partial_index_set {3,6,9,12,15}
      % || new_index_set 3..15
      % [x1, false, false, x2, false, false ..
      % [ 3,     4,     5,  6,     7,     8,   
       %   new length = 12

    array[int] of var bool: tmp_xs = array1d(xs);
    bool: repeat_last_element = absent(opt_def);
    array[int] of var bool: new_xs = [
      if i == 1 then tmp_xs[r_i] elseif repeat_last_element then tmp_xs[r_i+1] else deopt(opt_def) endif
        | r_i in 1..card(partial_index_set),
          i in if r_i+1 <= card(partial_index_set) then
                 1..partial_index_set[r_i+1]-partial_index_set[r_i]
               else
                 1..1
               endif
    ];
  } in array1d(new_index_set, new_xs);

% TODO SAT_optimize_int_lin_bounds; probably already done by -O3
% int: lb = lin_exp_lb(as, bs);
% int: ub = lin_exp_ub(as, bs);
% constraint if SAT_optimize_int_lin_bounds then forall(i in index_set(bs) where not is_fixed(bs[i]))(
%     if as[i] > 0 then
%       % term_i + lb_without_term_i <= c
%       % as[i]*bs[i] + lb - as[i]*lb(bs[i]) <= c
%       % as[i]*bs[i] - as[i]*lb(bs[i]) <= c - lb
%       % bs[i] - lb(bs[i]) <= (c - lb) div as[i]
%       % bs[i] <= ((c - lb) div as[i]) + lb(bs[i])
%       bs[i] <= ((c - lb) div as[i]) + lb(bs[i])
%     elseif as[i] < 0 then
%       % for as[i] < 0 we need ub(bs[i]) (becuase that's what's used to calculate `lb`)
%         % and >= (since we'll raise its lower bound)
%       bs[i] >= ((c - lb) div as[i]) + ub(bs[i])
%     else % TODO ? should be implied else
%       true
%   endif
% ) endif;


% PB case
function int: lin_exp_lb(array[int] of int: as) =
  sum(a in as where a < 0)(a);

function int: lin_exp_ub(array[int] of int: as) =
  sum(a in as where a > 0)(a);

% IP case
function int: lin_exp_lb(array[int] of int: as, array[int] of var int: bs) =
  let {
    constraint assert(forall(x in bs)(has_bounds(x)), "An element of input array \(bs) does not have any bounds and cannot be encoded"); % might be called before encoding
  } in sum([if as[i] > 0 then as[i]*lb(bs[i]) else as[i]*ub(bs[i]) endif | i in index_set(as)]);

function int: lin_exp_ub(array[int] of int: as, array[int] of var int: bs) =
  let {
    constraint assert(forall(x in bs)(has_bounds(x)), "An element of input array \(bs) does not have any bounds and cannot be encoded");
  } in sum([if as[i] > 0 then as[i]*ub(bs[i]) else as[i]*lb(bs[i]) endif | i in index_set(as)]);

function array[int] of var bool: int_plus_unary(var int: xs, int: c) =
  int_plus_unary(unary_encode(xs), c);

function array[int] of var bool: int_plus_order(var int: xs, int: c) =
  int_plus_order(order_encode(xs), c);

