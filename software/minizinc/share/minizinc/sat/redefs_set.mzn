include "nosets_sat.mzn";

% TODO what about promise totals?

test is_range(set of int: x) = card(x) == max(x)-min(x)+1;

function array[int,int] of int: set_to_ranges_2d(set of int: S) =
  let {
    array[int] of int: ranges = set_to_ranges(S);
  } in
  array2d(1..length(ranges) div 2, 1..2, ranges);

% disjunction of conjunctions (of encoding vars)
function array[int,int] of var bool: set_in_func(var int: x, set of int: S) =
  let {
    set of SAT_encoding_modes: encs = encodings(x);
  } in
  if encs == {SAT_UNARY} then
    let {
      array[int] of var bool: x_enc = unary_encode(x);
    } in array2d(
      1..card(S),
      1..1,
      [ x_enc[i]::maybe_partial | i in S ]
    )
  elseif encs == {SAT_ORDER} then
    let {
      array[int] of var bool: x_enc = order_encode(x);
      array[int,int] of int: groups = set_to_ranges_2d(S);
    } in array2d(
      index_set_1of2(groups),
      1..2,
      [ x_enc_j |
        k in index_set_1of2(groups),
        x_enc_j in [ x_enc[groups[k,1]], not x_enc[groups[k,2]+1]::maybe_partial ]
      ]
    )
  else
    let { constraint abort("XXX"); } in array2d(0..0,0..0,[])
  endif;

predicate exists_forall_implies_forall(array[int,int] of var bool: antecedents, array[int] of var bool: consequents) =
  forall(i in index_set_1of2(antecedents), c in consequents)(
    clause([c],antecedents[i,..])
  );


predicate exists_forall_implies(array[int,int] of var bool: antecedents, var bool: consequent) =
  exists_forall_implies_forall(antecedents, [consequent]);

predicate exists_forall(array[int,int] of var bool: antecedents) =
  exists(i in index_set_1of2(antecedents))(forall(antecedents[i,..]));

predicate set_in(var int: x, set of int: S) =
  let {
    constraint assert(not (ub(x) < min(S) /\ lb(x) > max(S)), "Is this a pre-condition?");
    % TODO if we add a set_in_reif, we could assert here that x is unencoded.. constraint assert(not has_sat_ann(x, unary_encoded), not has_sat_ann())
    % TODO efficient?
    % set of int: S = S intersect dom(x);
  } in
  if card(S) == 0 then
    false
  elseif card(S) == 1 then
    ( x == min(S) )
  else
    if has_sat_ann(x, unary_encoded) then
      let {
        array[int,int] of var bool: vars = set_in_func(x, S);
      } in exists_forall(vars)
    elseif has_sat_ann(x, order_encoded) then
      let {
        array[int] of var bool: x_enc = order_encode(x);
        array[int,int] of var bool: vars = set_in_func(x, S);
      } in exists_forall(vars)
    elseif has_sat_ann(x, binary_encoded) then
      let {
        array[int,int] of int: ranges = set_to_ranges_2d(S);
      } in
      exists(i in index_set_1of2(ranges))(
        if ranges[i,2] - ranges[i,1] + 1 <= SAT_RANGES_IN_REIF_CUT_OFF then
          exists(j in ranges[i,1]..ranges[i,2])(x == j)
        else
          x >= ranges[i,1] /\ x <= ranges[i,2]
        endif
      )
    else
      annotate_sat_encoding(x, SAT_SET_IN_DEFAULT_ENCODING)
      /\ set_in(x, S)
    endif
  endif;

predicate ranges_in_reif(var int: x, array[int] of int: ranges, var bool: r) =
  if has_sat_ann(x, unary_encoded) then
    let {
      array[int] of var bool: x_enc = unary_encode(x);
    } in r <-> exists( % we have to use a double generator to avoid an exist of reified exists which won't be flattened properly (although it would if it were root context)
      i in index_set(ranges) where i mod 2 == 1,
      j in ranges[i]..ranges[i+1])(
       % TODO the maybe_partial is for when a range is outside the domain of x, but this could be done better; we should just start/end at the first/last range that overlaps with the domain of x
        x_enc[j]::maybe_partial
      ) % TODO perhaps binary should be moved here as well, if binary range_in reif uses exists
  elseif has_sat_ann(x, order_encoded) then
    r <-> exists(i in index_set(ranges) where i mod 2 == 1)(
      x >= ranges[i] /\ x <= ranges[i+1]
    )
  elseif has_sat_ann(x, binary_encoded) then
    r <-> exists(i in index_set(ranges) where i mod 2 == 1)(
      if ranges[i+1] - ranges[i] + 1 <= SAT_RANGES_IN_REIF_CUT_OFF then
        exists(j in ranges[i]..ranges[i+1])(x == j)
      else
        x >= ranges[i] /\ x <= ranges[i+1]
      endif
    )
  else
    annotate_sat_encoding(x, SAT_SET_IN_DEFAULT_ENCODING)
    /\ ranges_in_reif(x, ranges, r)
  endif;

predicate range_in(var int: x, set of int: s) =
  assert(is_range(s), "range_in received a set that is not a range, but was \(s)")
  /\ range_in(x, min(s), max(s));

predicate range_in(var int: x, int: min, int: max) =
  % Not used in reified context when x is unary_encoded
  let {
    constraint assert(max - min >= 0, "Empty ranges should have been checked before calling range_in constraint");
  } in
    if min == max then
      x == max
    % TODO maybe better for binary (but shouldn't be better for order);
    % elseif max -min + 1 == 2 then
    %   x == min \/ x == m
    else % maybe only do this for a minimum range width
      x >= min /\ x <= max
    endif;

predicate set_in(var int: x, var set of int: s) ::promise_total =
  x in ub(s) /\ set2bools(s)[x];


% TODO would be nice to handle unary like this, but doesn't reified exist of reified exists is not optimal!
% predicate range_in_unary(var int: x, int: min, int: max) =
%   let {
%     array[int] of var bool: x_enc = unary_encode(x);
%   } in forall(i in min(index_set(x_enc))..min-1)(not x_enc[i])
%     /\ forall(i in max+1..max(index_set(x_enc)))(not x_enc[i]);

% % % Directly implemented for ranges_in_reif
% predicate range_in_unary_reif(var int: x, int: min, int: max, var bool: r) =
%   abort("Directly implemented for ranges_in_reif, so shouldn't be used");
%   % let {
%   % % } in r <-> exists(unary_encode(x)[min..max]);
%   %   array[int] of var bool: x_enc = unary_encode(x);
%   % } in r <-> exists(i in min..max)(x_enc[i]);


% predicate ranges_in(var int: x, array[int] of int: ranges) =
%   let {
%     constraint SAT_trace(2, "x \(x) in \(dom(x))\n");
%     constraint SAT_trace(2, "ranges \(ranges)\n");
%   } in
%   % ranges_in_reif(x, ranges, true);
%   % exists(i in index_set(ranges) where i mod 2 == 1)(
%   %   range_in(x, ranges[i], ranges[i+1])
%   % );
%   if has_sat_ann(x, unary_encoded) then
%     let {
%       array[int] of var bool: x_enc = unary_encode(x);
%       constraint SAT_trace(2, "x_enc \(x_enc)\n");
%     } in
%       forall(i in min(index_set(x_enc))..ranges[1]-1)(
%       SAT_trace(2, "i \(i)\n") /\
%         not x_enc[i]
%       ) /\
%       forall(
%         i in 2..max(index_set(ranges))-1 where i mod 2 == 0,
%         j in ranges[i]+1..ranges[i+1]-1)(
%         SAT_trace(2, "i \(i), j \(j)\n") /\
%         not x_enc[j]::maybe_partial
%       ) /\
%       forall(i in ranges[max(index_set(ranges))]+1..max(index_set(x_enc)))(
%       SAT_trace(2, "i \(i)\n") /\
%         not x_enc[i]
%       )
%     % exists( % we have to use a double generator to avoid an exist of reified exists which won't be flattened properly (although it would if it were root context)
%     %   i in index_set(ranges) where i mod 2 == 1,
%     %   j in ranges[i]..ranges[i+1])(
%     %    % TODO the maybe_partial is for when a range is outside the domain of x, but this could be done better; we should just start/end at the first/last range that overlaps with the domain of x
%     %     x_enc[j]::maybe_partial
%     %   ) % TODO perhaps binary should be moved here as well, if binary range_in reif uses exists
%   elseif has_sat_ann(x, order_encoded) \/ has_sat_ann(x, binary_encoded) then
%     exists(i in index_set(ranges) where i mod 2 == 1)(
%       range_in(x, ranges[i], ranges[i+1])
%     )
%   else
%     annotate_sat_encoding(x, SAT_SET_IN_DEFAULT_ENCODING)
%     /\ ranges_in(x, ranges)
%   endif;

