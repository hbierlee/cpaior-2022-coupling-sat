/**
There's some convention here on these predicates to keep track of all the permutations:
  - channel_A_B(A, B) % simply provides the settings-based switch between using one-way or two-way channelling from encoding A to B. As for all predicates, the arguments have the same order as the predicate's name.
  - channel_A_B_one_way(A, b) % channels one-way from A to B
  - channel_A_B_two_way(A, B) % channels two-way between A and B: the argument and the name is always in the order of: unary, order, binary. (e.g., we never have channel_order_unary_one_way(order, unary), but instead: channel_unary_order_two_way(unary, order))
***/

% predicate channel_order_binary_two_way(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_bin) =
%   let {
%     array[int] of int: coefs = binary_encode_int_lin_exp_coefficients(length(x_enc_bin));
%   } in
%   forall(i in index_set(x_enc_ord) diff { min(index_set(x_enc_ord)) })(
%     let {
%       array[int] of bool: bin = (binary(i - min(index_set(x_enc_ord)), length(x_enc_bin)));
%       array[int] of var bool: rhs = [ x_enc_bin[i] | i in index_set(bin) where bin[i] ];
%     } in bool_clause([x_enc_ord[i]], rhs)
%     );


% predicate channel_order_binary_one_way(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_bin) =
%     forall(i in index_set(x_enc_ord) diff { min(index_set(x_enc_ord)) })(
%     let {
%       % TODO this is the binary carry sequence (https://oeis.org/A007814), can we hard-code/iterate over this easier without creating binary numbers?
%       int: y_i = arg_min(binary(i-1, length(x_enc_bin))); % TODO don't need the full number
%       int: j_a = i+(2^(y_i-1));
%       int: j_b = i-(2^(y_i-1));
%     } in
%       (
%        x_enc_ord[i] -> (x_enc_bin[y_i] \/
%          if j_a <= max(index_set(x_enc_ord)) then x_enc_ord[j_a] else false endif
%          )
%       )
%       /\
%       (
%        (not x_enc_ord[i]) -> ((not x_enc_bin[y_i]) \/
%          if j_b > min(index_set(x_enc_ord)) then (not x_enc_ord[j_b]) else true endif
%          )
%       )
%     );

% binary to order translation
predicate channel_order_binary_one_way(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_bin) =
  let {
    constraint SAT_trace(2, "LOG: channel order \(index_set(x_enc_ord)) <-> binary \(index_set(x_enc_bin)) : \(x_enc_ord) \(x_enc_bin)\n");
    % TODO why don't we have to flip the sign bit?
    % array[int] of var bool: x_enc_bin_orderable = x_enc_bin[..length(x_enc_bin)-1] ++ [not x_enc_bin[length(x_enc_bin)]];
    array[int] of var bool: x_enc_bin_orderable = x_enc_bin;
    int: l = binary_lb(x_enc_bin);
    int: u = binary_ub(x_enc_bin);
  } in
  forall(b in index_set(x_enc_bin))(
  % TODO should we spend time optimizing this for fixed variables in the encodings?
      % here (like in other place) we should be aware that the order encoding is decreasing
    let {
      int: size = pow(2, b-1);
      % the segment indices
      int: ls = l div size - (l mod size != 0);
      int: us = u div size;
    } in
      forall(s in ls..us)(
        let {
          int: curr = max(s*size, l);
          int: next = curr+size;
        } in
          if s mod 2 = 0 then  % even, so we are in a 0-segment
            bool_clause(
            % TODO NOOO idea why clause causes problems here, or why it redirects to arrya_bool_or
            % clause(
              [ order_encoding_element_partial(x_enc_ord, next) ],
              [ order_encoding_element_partial(x_enc_ord, curr) , x_enc_bin_orderable[b] ]
            ) 
            ::expression_name_dbg("O->B: -f(x,\(b-1)) \\/ f(x<\(curr)) \\/ f(x>=\(next))")
          else % we are in a 1-segment
            bool_clause(
            % clause(
              [ order_encoding_element_partial(x_enc_ord, next) , x_enc_bin_orderable[b] ],
              [ order_encoding_element_partial(x_enc_ord, curr) ]
            )
            ::expression_name_dbg("O->B: f(x,\(b-1)) \\/ f(x<\(curr)) \\/ f(x>=\(next))")
          endif
    )
  );


predicate channel_binary_order_one_way(array[int] of var bool: x_enc_bin, array[int] of var bool: x_enc_ord) =
  let {
    % flip sign bit
    constraint SAT_trace(2, "LOG: channel order<->binary \(x_enc_bin) \(x_enc_ord)\n");
    constraint abort("deprecated");
    array[int] of var bool: x_enc_bin_orderable = x_enc_bin[..length(x_enc_bin)-1] ++ [not x_enc_bin[length(x_enc_bin)]];
  } in
  forall(i in index_set(x_enc_ord))(
    let {
      % orderable binary representation of i
      array[int] of bool: bin = binary(i-binary_lb(x_enc_bin), length(x_enc_bin), false);
    } in
      % [f'(i,j) | j in index_set(bin) where bin[j]] -> f(x >= i)
      bool_clause([ x_enc_ord[i] ], [x_enc_bin_orderable[j] | j in index_set(bin) where bin[j]])
      /\
      % [f'(i,j) | j in index_set(bin) where not bin[j]] -> f(x < i+1)
      bool_clause([x_enc_bin_orderable[j] | j in index_set(bin) where not bin[j]], [ x_enc_ord[i+1]::maybe_partial ])
  );

bool: SAT_binary_unary_elimination_method = true;

predicate channel_binary_unary_one_way(array[int] of var bool: x_enc_bin, array[int] of var bool: x_enc_un) =
    let {
      constraint abort("other is preferable?");
      constraint SAT_trace(2, "LOG: channel unary<->binary \(x_enc_bin) \(x_enc_un)\n");
    } in
    if SAT_binary_unary_elimination_method then
      forall(i in index_set(x_enc_un))(
        let {
          array[int] of bool: bin = binary(i, length(x_enc_bin));
        } in
        forall(j in index_set(bin))(
          if bin[j] then
            not x_enc_bin[j] -> not x_enc_un[i]
          else
            x_enc_bin[j] -> not x_enc_un[i]
          endif
        )
      )
    else
      % TODO what is the correct iteration domain?
      forall(i in index_set(x_enc_un))(
        int_eq_binary(x_enc_bin, i) -> x_enc_un[i]
      )
    endif;

predicate channel_unary_binary_one_way(array[int] of var bool: x_enc_un, array[int] of var bool: x_enc_bin) =
    let {
      constraint SAT_trace(2, "LOG: channel unary<->binary \(x_enc_un) \(x_enc_bin)\n");
    } in
    forall(i in index_set(x_enc_un))(
      let {
        array[int] of bool: bin = binary(i, length(x_enc_bin), true);
      } in
        forall(j in index_set(bin))(
          if bin[j] then
            x_enc_un[i] -> x_enc_bin[j]
          else
            % x_enc_un[i] -> not x_enc_bin[j]
            clause([], [x_enc_un[i], x_enc_bin[j]])
          endif
        )
    ) /\
      % TODO optimize this, probably a much better way to flatten without all the calls to binary (especially by merging into the previous forall)
      forall(k in index_set(x_enc_bin))(
        clause(
          [x_enc_un[d] | d in index_set(x_enc_un) where binary(d, length(x_enc_bin), true)[k]],
          [x_enc_bin[k]]
        ) /\
        clause(
          [x_enc_un[d] | d in index_set(x_enc_un) where not binary(d, length(x_enc_bin), true)[k]]
          ++ [x_enc_bin[k]],
          []
        )
      );

% predicate channel_order_unary_one_way(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_un) =
%   forall(i in index_set(x_enc_ord) intersect index_set(x_enc_un))(
%     (x_enc_ord[i] -> not x_enc_un[i-1]::maybe_partial)
%     /\ (not x_enc_ord[i] -> not x_enc_un[i])
%     );

% Two-way channellings
predicate channel_unary_order_two_way(array[int] of var bool: x_enc_un, array[int] of var bool: x_enc_ord) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_unary_order_two_way called on \(x_enc_un) and \(x_enc_ord)") /\
  if SAT_channel_two_way_pb then
    channel_unary_order_two_way_pb(x_enc_un, x_enc_ord)
  else
    let {
      constraint SAT_trace(2, "LOG: channel unary<->order \(x_enc_un) \(x_enc_ord)\n");
    } in
    forall(i in index_set(x_enc_un) intersect index_set(x_enc_ord))(
      let {
        var bool: x_u_i = x_enc_un[i];
        var bool: x_o_i = x_enc_ord[i];
        var bool: x_o_i_next = x_enc_ord[i+1]::maybe_partial;
      } in (clause([x_o_i],[x_u_i])
         /\ clause([],[x_u_i,x_o_i_next])
         /\ clause([x_u_i, x_o_i_next],[x_o_i])
      )::expression_name_dbg("channel unary<->order")
      % (not x_u_i \/ x_o_i) /\ (not x_u_i \/ not x_o_i_next) /\ (x_u_i \/ not x_o_i \/ x_o_i_next)
    )
  endif;

predicate channel_unary_binary_two_way(array[int] of var bool: x_enc_un, array[int] of var bool: x_enc_bin) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_unary_binary_two_way called on \(x_enc_un) and \(x_enc_bin)") /\
  if SAT_channel_two_way_pb then
    channel_unary_binary_two_way_pb(x_enc_un, x_enc_bin)
  else
    channel_unary_binary_one_way(x_enc_un, x_enc_bin)
    % /\
    % channel_binary_unary_one_way(x_enc_bin, x_enc_un)
  endif;

predicate channel_order_binary_two_way(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_bin) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_order_binary_two_way called on \(x_enc_ord) and \(x_enc_bin)") /\
  if SAT_channel_two_way_pb then
    channel_order_binary_two_way_pb(x_enc_ord, x_enc_bin)
  else
    channel_order_binary_one_way(x_enc_ord, x_enc_bin)
    % /\
    % channel_binary_order_one_way(x_enc_bin, x_enc_ord)
  endif;

% Two-way channellings (PB)
predicate channel_unary_order_two_way_pb(array[int] of var bool: x_enc_un, array[int] of var bool: x_enc_ord) =
  bool_lin_eq(
    [i | i in index_set(x_enc_un)] ++ [-1 | i in index_set(x_enc_ord)],
    x_enc_un ++ x_enc_ord,
    min(index_set(x_enc_ord)) - 1,
  );

predicate channel_unary_binary_two_way_pb(array[int] of var bool: x_enc_un, array[int] of var bool: x_enc_bin) =
  bool_lin_eq(
    binary_encode_int_lin_exp_coefficients(x_enc_bin) ++ [-i | i in index_set(x_enc_un)],
    x_enc_bin ++ x_enc_un,
    0
  );

predicate channel_order_binary_two_way_pb(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_bin) =
  bool_lin_eq(
    binary_encode_int_lin_exp_coefficients(x_enc_bin) ++ [-1 | i in index_set(x_enc_ord)],
    x_enc_bin ++ x_enc_ord,
    min(index_set(x_enc_ord)) - 1,
  );

% TODO alternative one-way map approach
% predicate channel_binary_order(array[int] of var bool: x_enc_bin, array[int] of var bool: x_enc_ord) =
%   let {
%     int: l_bin = min(index_set(x_enc_bin));
%     int: u_bin = l_bin + 2^length(x_enc_bin) - 1;
%     int: l_ord = min(index_set(x_enc_ord));
%     int: u_ord = max(index_set(x_enc_ord));
%     array[int] of var bool: bits = array1d(0..length(x_enc_bin)-1, x_enc_bin);
%     % array[int] of var bool: sorted_bits = build_sorting_network(x_enc_bin, 1); % build EQ sorting network
%     % TODO cache the 2^.. ? or make some bit array to loop over
%   } in 
%   forall(i in index_set(bits))(
%   let {
%     int: bit_value = 2^i;
%   } in 
%     % b_i -> x >= l_bin + bit_value
%     (bits[i] -> forall(j in l_ord..min(u_ord, l_bin+bit_value))(trace("b\(i) -> o\(j)\n") /\ x_enc_ord[j]))
%     /\ % not b_i -> x < u_bin - bit_value -> x<=u_bin-bit_value+1
%     (not bits[i] -> forall(j in max(l_ord, u_bin-bit_value+1)..u_ord)(trace("not b\(i) -> not o\(j)\n") /\ not x_enc_ord[j]))
%   );

% channel_A_B Switchers/entry point
predicate channel_unary_order(array[int] of var bool: x_enc_un, array[int] of var bool: x_enc_ord) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_unary_order called on \(x_enc_un) and \(x_enc_ord)") /\
  if SAT_channel_two_way then
    channel_unary_order_two_way(x_enc_un, x_enc_ord)
  else
    % channel_unary_order_one_way(x_enc_un, x_enc_ord)
    abort("not implemented")
  endif;

predicate channel_order_unary(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_un) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_unary_order called on \(x_enc_ord) and \(x_enc_un)") /\
  if SAT_channel_two_way then
    channel_unary_order_two_way(x_enc_un, x_enc_ord)
  else
    % channel_order_unary_one_way(x_enc_ord, x_enc_un)
    abort("not implemented")
  endif;

predicate channel_unary_binary(array[int] of var bool: x_enc_un, array[int] of var bool: x_enc_bin) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_unary_binary called on \(x_enc_un) and \(x_enc_bin)") /\
  if SAT_channel_two_way then
    channel_unary_binary_two_way(x_enc_un, x_enc_bin)
  else
    channel_unary_binary_one_way(x_enc_un, x_enc_bin)
  endif;

predicate channel_binary_unary(array[int] of var bool: x_enc_bin, array[int] of var bool: x_enc_un) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_binary_unary called on \(x_enc_bin) and \(x_enc_un)") /\
  if SAT_channel_two_way then
    channel_unary_binary_two_way(x_enc_un, x_enc_bin)
  else
    channel_binary_unary_one_way(x_enc_bin, x_enc_un)
  endif;

predicate channel_order_binary(array[int] of var bool: x_enc_ord, array[int] of var bool: x_enc_bin) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_order_binary called on \(x_enc_ord) and \(x_enc_bin)") /\
  if SAT_channel_two_way then
    channel_order_binary_two_way(x_enc_ord, x_enc_bin)
  else
    channel_order_binary_one_way(x_enc_ord, x_enc_bin)
  endif;

predicate channel_binary_order(array[int] of var bool: x_enc_bin, array[int] of var bool: x_enc_ord) =
  assert(SAT_allow_redundant_encodings, "SAT_allow_redundant_encodings is \(SAT_allow_redundant_encodings), but channel_binary_order called on \(x_enc_bin) and \(x_enc_ord)") /\
  if SAT_channel_two_way then
    channel_order_binary_two_way(x_enc_ord, x_enc_bin)
  else
    channel_binary_order_one_way(x_enc_bin, x_enc_ord)
  endif;
