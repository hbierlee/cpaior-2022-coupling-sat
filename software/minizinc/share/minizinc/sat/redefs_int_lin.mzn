enum Comparator = { INT_EQ, INT_LE, INT_NE };

predicate int_lin_eq(array[int] of int: as, array[int] of var int: bs, int: c) =
  int_lin(as, bs, c, INT_EQ);

predicate int_lin_le(array[int] of int: as, array[int] of var int: bs, int: c) =
  int_lin(as, bs, c, INT_LE);

predicate int_lin_ne(array[int] of int: as, array[int] of var int: bs, int: c) =
  int_lin(as, bs, c, INT_NE);

predicate int_lin(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  int_lin_dispatch(
    filter_lin_exp_fixed_vars_and_zero_pars_for_coefficients(as, bs),
    filter_lin_exp_fixed_vars_and_zero_pars_for_variables(as, bs),
    c - filter_lin_exp_fixed_vars_and_zero_pars_for_constant(as, bs),
    comp,
  );

predicate int_lin_dispatch(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  let {
    constraint assert((length(as) == 0 /\ length(bs) == 0) \/ (min(index_set(as)) == 1 /\ min(index_set(bs)) == 1), "% TODO apparently we need to normalize arrays");
    int: n = length(as);
  } in
    if n == 0 then
      if comp == INT_EQ then
        c == 0
      elseif comp == INT_NE then
        c != 0
      elseif comp == INT_LE then
        0 <= c
      else
        abort("Unknown comparator \(comp) in int_lin")
      endif
    elseif n == 1 then
      int_lin_of_1(as, bs, c, comp)  % a*x ~ c -> x ~ c div a
    elseif n == 2 then
      int_lin_of_2(as, bs, c, comp)  % a*x+b*y ~ c -> a*x ~ c-b*y
    % elseif n == 3 /\ forall(a in as)(a in -1..1) /\ comp == INT_EQ then
    %   int_lin_of_3(as, bs, c, comp)  % a*x+b*y+c*z ~ d -> a*x+b*y ~ d-c*z
    % Trivial bounds checking
    elseif comp == INT_LE /\ lin_exp_ub(as, bs) <= c then
      true
    elseif comp == INT_LE /\ lin_exp_lb(as, bs) > c then
      false
    elseif comp != INT_LE /\ (lin_exp_ub(as, bs) < c \/ lin_exp_lb(as, bs) > c) then
      if comp == INT_EQ then
        false
      elseif comp == INT_NE then
        true
      else
        abort("Unknown comparator \(comp) in int_lin")
      endif
    else
      pbify_int_lin(as, bs, c, comp)
    endif;

predicate pbify_int_lin(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  let {
    % TODO can still easily be made smarter:
        % 1) instead of dom_array -> check doms of individual int vars, and only overrule those that are >= limit
        % 2) for int_lin_of_2, also set a dom_limit (but much,much higher >5000, or if coefficient is very high (which'd require so much spacing)
        % 3) maybe channelling FROM binary (to direct/order) is not as hot an idea in all cases
    % array[int] of int: prefs = int_lin_comp_enc_prefs(as, bs, c, comp);
    array[int] of int: prefs = [3,2,1];
    array[int] of SAT_encoding_modes: encs = get_one_sat_encoding(bs, prefs, SAT_overrule_pbify);
    constraint SAT_trace(2, "WARNING: pbifying int_lin constraint of n=\(length(bs)), dom_array=\(dom_array(bs)): \(as), \(bs) \([ dom(b) | b in bs]), \(c), \(comp), \(encs)\n");
    constraint assert(SAT_assert_allow_pbify, "pbify_int_lin is not allowed but was called\n");
  } in
  bool_lin(
    pbify_coefficients(as, bs, encs),
    [ b_i_j | b_i_j in pbify_variables(bs, encs) where not is_fixed(b_i_j) ],
    c - encode_int_lin_exp_constant(as, bs, encs),
    comp,
  );

predicate int_lin_of_1(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  if comp == INT_EQ then
    bs[1] == c div as[1]
  elseif comp == INT_NE then
    int_ne(bs[1], c div as[1])
    % bs[1] != c div as[1]
  elseif comp == INT_LE then
    if as[1] > 0 then
      % int_le(bs[1], c div as[1])
      bs[1] <= c div as[1]
    else  % change inequality sign and round up
      % -a[1..3] <= c -> [1..3] >= c/-a -> c/-a <= [1..3]
      % TODO double-check usage of ceil
      int_le(ceil(c / as[1]), bs[1])
    endif
  else
    abort("Unknown comparator \(comp) in int_lin")
  endif;

function array[int] of int: int_lin_comp_enc_prefs(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  if length(as) >= 3 then
    [3] ++ if comp in {INT_EQ, INT_NE} then [p | p in SAT_INT_EQUALITY_ENCODING_PREFS where p != 3] else [ p | p in SAT_INT_INEQUALITY_ENCODING_PREFS where p != 3 ] endif
  elseif comp in {INT_EQ, INT_NE} then % for smaller linears, it depends on the comp
    SAT_INT_EQUALITY_ENCODING_PREFS
  else
    SAT_INT_INEQUALITY_ENCODING_PREFS
  endif;

% Whether for an int_lin on [x,y], we should move x or y to the rhs, in order to avoid/reduce the potential reverse of the direct/order encoding array
function bool: is_first_var_to_move(array[int] of int: as, array[int] of set of int: bs_doms) =
  let {
    bool: sign_x = as[1] > 0;
    bool: sign_y = as[2] > 0;
  } in  % TODO this could (or should) be just a sort, except in the case where both sign are negative
    if sign_x xor sign_y then % different signs
      sign_y % move x if y is the positive one
    else
      let {
        bool: x_has_larger_encoding = card(bs_doms[1]) >= card(bs_doms[2]);
      } in
      if sign_x /\ sign_y then % both positive
        not x_has_larger_encoding % move (and flip) x if it has the smaller encoding
      else % both negative
        x_has_larger_encoding % move x (and flip y) if x has the greater encoding
      endif
    endif;

predicate int_lin_of_2(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  let { % TODO perhaps the overrule value should have different behaviour here
    array[int] of int: prefs = int_lin_comp_enc_prefs(as, bs, c, comp);
    array[int] of SAT_encoding_modes: encs = inherit_encodings(bs, [SAT_UNARY, SAT_ORDER, SAT_BINARY][prefs[1]]);
    
   } in
    if encs == [SAT_BINARY, SAT_BINARY] then
      int_lin_of_2_binary(as,bs,c,comp)
    % elseif comp == INT_EQ /\ encs == [SAT_ORDER,SAT_ORDER] then % TODO this could handle INT_EQ's created by MiniZinc's linear expression; only problem is that those are created too late, so this view doesn't get resolved in the function that creates the linear
    %   let {
    %     constraint trace("EQQ\n");
    %   } in
    %   if as[2] == -1 then
    %    affine_view(bs[2], bs[1], as[1], -c, SAT_ORDER)
    %   else
    %     let {
    %       constraint abort("");
    %     } in true
    %   endif
    else
      let {  % a*x+b*y~c -> a*x~c-b*y (or b*y~c-a*x)
      % TODO in case of one unary, one binary, make sure the view on binary is identity (1x+0) or -1x-1
        bool: move_first_var = is_first_var_to_move(as, [ dom(b) | b in bs]);
        int: x_idx = move_first_var+1;
        int: y_idx = (not move_first_var)+1;
        int: lhs_c = if encs[x_idx] == SAT_BINARY /\ encs[y_idx] != SAT_BINARY then 0 else -c endif;
        int: rhs_c = if lhs_c == 0 then c else 0 endif;
        var int: lhs = affine(bs[x_idx],  as[x_idx], lhs_c);
        var int: rhs = affine(bs[y_idx], -as[y_idx], rhs_c);
      } in if comp == INT_EQ then
             int_eq(lhs, rhs)
           elseif comp == INT_NE then
             int_ne(lhs, rhs)
           elseif comp == INT_LE then
             int_le(lhs, rhs)
           else
             abort("unknown comparator")
           endif
     endif;

% predicate channel_encodings(var int: a_enc, var int: b_enc) =
%   let {
%     array[int] of SAT_encoding_modes: encs = get_one_sat_encoding(bs, prefs, false);
%   } in
%   if encs[1] == SAT_UNARY /\ encs[2] == SAT_UNARY then
%     int_eq_unary(a_enc, b_enc)
%   elseif encs[1] == SAT_UNARY /\ encs[2] == SAT_ORDER then
%     channel_unary_order(a_enc, b_enc)
%   elseif encs[1] == SAT_UNARY /\ encs[2] == SAT_BINARY then
%     channel_unary_binary(a_enc, b_enc)
%   elseif encs[1] == SAT_ORDER /\ encs[2] == SAT_ORDER then
%     int_eq_order(a_enc, b_enc)
%   elseif encs[1] == SAT_ORDER /\ encs[2] == SAT_UNARY then
%     channel_order_unary(a_enc, b_enc)
%   elseif encs[1] == SAT_ORDER /\ encs[2] == SAT_BINARY then
%     channel_order_binary(a_enc, b_enc)
%   elseif encs[1] == SAT_BINARY /\ encs[2] == SAT_BINARY then
%     int_eq_binary(a_enc, b_enc)
%   elseif encs[1] == SAT_BINARY /\ encs[2] == SAT_UNARY then
%     channel_binary_unary(a_enc, b_enc)
%   elseif encs[1] == SAT_BINARY /\ encs[2] == SAT_ORDER then
%     channel_binary_order(a_enc, b_enc)
%   else
%     abort("unsupported \(encs)")
%   endif;

predicate int_lin_of_3(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  assert(comp in {INT_NE, INT_EQ}, "int_lin_of_3 only supports INT_EQ/INT_NE, but was given \(comp)") /\
  let {
    constraint abort("Not sure if int_lin_of_3_direct/order is a good idea yet!");
    array[int] of bool: encs = get_sat_encodings(bs, int_lin_comp_enc_prefs(as, bs, c, comp));
    constraint SAT_trace(2, "LOG: int_lin constraint of n=\(length(bs)), dom_array=\(dom_array(bs)): \(as), \(bs) \([ dom(b) | b in bs]), \(c), \(comp), \(encs)\n");
  } in
  forall(i in index_set(encs) where encs[i])(
       if i == 1 then int_lin_of_3_unary(as, bs, c, comp) endif
    /\ if i == 2 then int_lin_of_3_order(as, bs, c, comp) endif
    /\ if i == 3 then int_lin_of_3_binary(as, bs, c, comp) endif
  );

predicate bool_lin(array[int] of int: as, array[int] of var bool: bs, int: c, Comparator: comp) =
  if comp == INT_EQ then
    bool_lin_eq(as,bs,c)
  elseif comp == INT_NE then
    not bool_lin_eq(as,bs,c)
  elseif comp == INT_LE then
    bool_lin_le(as,bs,c)
  else
    abort("Unknown comparator \(comp) in bool_lin")
  endif;
