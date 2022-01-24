% TODO handle (some) fixed ints?
predicate fzn_alldifferent_except(array[int] of var int: xs, set of int: except) =
  if false then
    fzn_all_different_except_int_inequalities(xs, except)
  else
    if length(xs) <= 1 then true
    elseif card(dom_array(xs)) < length(xs) /\ except == {} then false % pigeonhole principle
    else
      let { array[int] of bool: encs = get_sat_encodings(xs, SAT_INT_EQUALITY_ENCODING_PREFS) } in
      forall(i in index_set(encs) where encs[i])(
           if i == 1 then fzn_all_different_except_int_unary(xs, except) endif
        /\ if i == 2 then fzn_all_different_except_int_order(xs, except) endif
        /\ if i == 3 then fzn_all_different_except_int_inequalities(xs, except) endif
      )
    endif
  endif;

% TODO remove par version sometime when it's safe
predicate fzn_all_different_except_int(array[int] of int: xs, set of int: except) =
  forall(i,j in index_set(xs) where i < j) ( i in except \/ j in except \/ xs[i] != xs[j] );

predicate fzn_all_different_except_int_inequalities(array[int] of var int: x, set of int: except) =
  assert(except == {}, "untested for excepting elements, but had \(except)") /\
  if not has_sat_ann(x, unary_encoded) /\ not has_sat_ann(x, order_encoded) /\ not has_sat_ann(x, binary_encoded) then
    annotate_sat_encoding(x, SAT_INT_EQUALITY_DEFAULT_ENCODING)
    /\ fzn_all_different_except_int_inequalities(x, except)
  else
    forall(i,j in index_set(x) where i < j) ( x[i] != x[j] )
  endif;

predicate fzn_all_different_except_int_unary(array[int] of var int: xs, set of int: except) =
  let {
    % constraint assert((SAT_encoding_mode == SAT_DEFAULT) \/ (SAT_encoding_mode == SAT_UNARY), "fzn_all_different_except_int_unary: SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_UNARY");
    constraint if not has_sat_ann(xs, unary_encoded) then
      SAT_trace("WARNING: creating redundant direct encoding\n") /\ assert(SAT_allow_redundant_encodings, "Redundant encodings not allowed but needed for fzn_all_different_except_int_unary") /\ annotate_sat_encoding(xs, SAT_UNARY)
    endif;
    int: n = length(xs);
    set of int: d = dom_array(xs) diff except;
  } in
    forall(i in d)(
      if except == {} /\ n == card(d) then
        sat_count_eq([ x == i | x in xs ], 1)
      else
        sat_count_geq([ x == i | x in xs ], 1)
      endif
    );

predicate fzn_all_different_except_int_order_count_method(array[int] of var int: xs, set of int: except) =
  assert(except == {}, "fzn_all_different_except_int_order_count_method incorrect when except is non-empty, and it was except=\(except)") /\
  let {
    constraint abort("untested");
    int: l = min(dom_array(xs));
    int: u = max(dom_array(xs));
    int: d = card(dom_array(xs));
    int: n = length(xs);
  } in
      forall(i in dom_array(xs))(
        let {
          var bool: b;
        } in
        sat_count_eq(
          [ x < i | x in xs ] ++ [ x >= i+1 | x in xs ] ++ [b], n)
        );

predicate fzn_all_different_except_int_order(array[int] of var int: xs, set of int: except) =
  let {
    int: l = min(dom_array(xs));
    int: u = max(dom_array(xs));
    set of int: d = dom_array(xs) diff except; % yes but now any column can potentially be 0
    int: n = length(xs);
  } in if except == {} /\ card(d) == n then
      forall(v in d)(sat_count_eq([ x >= v | x in xs ], u-(v-1)))
      % fzn_all_different_except_int_order_count_method(xs, except)
      % TODO what is this again? Works for dimensions, or just redundant constraints?
      % forall(i in d)(sat_count_geq([ x >= u-i+1 | x in xs ], i)) % counts <= i
      % /\ forall(i in d)(sat_count_geq([ x < l+i | x in xs ], i))
      else
        SAT_trace("WARNING: fzn_all_different_except_int_order had non-empty except (\(except)) so had to take fzn_all_different_except_int_unary\n") /\
        fzn_all_different_except_int_unary(xs, except) % backup
        % let {
        %   array[1..d-n] of var 1..d-n: ys;
        %   % TODO can some vars have shorter domains (in a pyramid shape?)
        %   % array[int] of var int: ys = [
        %   % let { var 1..d-n-i: y; } in y
        %   % | i in 1..d-n ];
        % } in fzn_all_different_except_int_order(xs++ys)
      endif;

predicate fzn_all_different_int_order_triple_loop(array[int] of var int: xs, set of int: except) =
  assert(except == {}, "untested for excepting elements, but had \(except)") /\
  fzn_all_different_int_order_triple_loop(xs, except, dom_array(xs));

predicate fzn_all_different_int_order_triple_loop(array[int] of var int: xs, set of int: except, set of int: dom) =
  assert(except == {}, "untested for excepting elements, but had \(except)") /\
  forall(i in index_set(xs))(
    forall(j in dom)(
      forall(k in index_set(xs) diff {i})(
        % ((xs[i] >= j) -> ((xs[i] >= j+1) \/ (xs[k] >= j+1) \/ (xs[k] < j)))
        ((xs[i] < j) \/ ((xs[i] >= j+1) \/ (xs[k] >= j+1) \/ (xs[k] < j)))
        /\
        % ((xs[i] < j) -> ((xs[i] < j-1) \/ (xs[k] >= j) \/ (xs[k] < j-1)))
        ((xs[i] >= j) \/ ((xs[i] < j-1) \/ (xs[k] >= j) \/ (xs[k] < j-1)))
        )
      )
    );

