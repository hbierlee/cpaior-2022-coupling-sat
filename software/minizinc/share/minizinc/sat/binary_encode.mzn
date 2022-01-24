% Functions
% Single variable
function int: get_enc_size(var int: x) =
  get_enc_size(lb(x), ub(x));

function int: get_enc_size(int: lb_x, int: ub_x) =
  if (abs(lb_x) < abs(ub_x+1)) \/ (lb_x == ub_x /\ ub_x >= 0) then
    % magnitude of ub is greater and lb <= ub, so upper bound must be positive
    ceil(log2(abs(ub_x)+1))+1 % bottleneck is the largest (positive) number of the encoding
  else
    ceil(log2(abs(lb_x)))+1 % bottleneck is the smallest (negative) number ..
  endif;

function array[int] of var bool: binary_encode(int: x) ::promise_total =
  % let {
  %   constraint SAT_trace("WARNING: calling binary_encode on fixed var \(x) in \(dom(x))\n");
  % } in
  binary(x, get_enc_size(x), true);

ann: SAT_skip_binary_consistency_constraint;

function array[int] of var bool: binary_encode(var int: x) ::promise_total =
  let {
    constraint SAT_trace(2, "LOG: binary_encode(\(x) in \(dom(x)))\n");
    constraint assert(SAT_allow_redundant_encodings \/ (not has_sat_ann(x, unary_encoded) /\ not has_sat_ann(x, order_encoded)), "Redundant encodings not allowed");
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_BINARY, "binary_encode should not be called in encoding mode \(SAT_encoding_mode)");
    constraint assert(has_bounds(x), "Variable \(x) does not have any bounds and cannot be encoded");
  } in
  if is_fixed(x) then
    let {
      int: enc_size = get_enc_size(x);
      int: binary_lb = binary_lb(enc_size);
    } in binary(fix(x), enc_size, true)
  elseif has_ann(x, SAT_is_view) then
    let {
      constraint annotate(x, binary_encoded);
      % BUG -> minizinc: /home/hbierlee/Projects/libminizinc/lib/flatten/flat_exp.cpp:77: MiniZinc::EE MiniZinc::flat_exp(MiniZinc::EnvI&, const MiniZinc::Ctx&, MiniZinc::Expression*, MiniZinc::VarDecl*, MiniZinc::VarDecl*): Assertion `ctx.b != C_ROOT || b == constants().varTrue' failed.
      % workaround -> UNSAT
      % array[int] of var bool: x_enc = resolve_view(x, SAT_BINARY);

    % TODO still have to set this as root encoding but bug is preventing it
    % array[int] of var bool: x_enc = resolve_view(x, SAT_BINARY);
    % constraint if forall(x_enc_i in x_enc)(is_fixed(x_enc_i)) then
    %     % trace("WARNING: fully fixed binary x_enc \(index_set(x_enc)), \(x_enc) for \(x) in \(dom(x))\n")
    %      x == reverse_binary(array1d(index_set(x_enc), [fix(x_enc_i) | x_enc_i in x_enc]))
    %     else
    %       set_binary_encoding_as_root(x, x_enc)
    %   endif;
    % constraint set_binary_encoding_as_root(x, resolve_view(x, SAT_BINARY));
      % constraint (x = reverse_binary(resolve_view(x, SAT_BINARY)))::is_reverse_map;
    } in resolve_view(x, SAT_BINARY)
  else
    let {
      array[int] of var bool: x_enc = create_binary_encoding_variables(x);
      constraint if SAT_ADD_ALL_ENCODING_CONSTRAINTS then
        binary_encoding_constraints(x, x_enc)
      endif;

      % Create channelling constraint xor a reverse mapper
      bool: uo = has_ann(x, unary_order_channeled);
      bool: ub = has_ann(x, unary_binary_channeled);
      bool: ob = has_ann(x, order_binary_channeled);

      constraint
          if has_sat_ann(x, order_encoded) /\ needs_channel(ob, uo, ub) then
            annotate(x, order_binary_channeled) /\ channel_binary_order(x_enc, order_encode(x))
              /\ binary_encoding_constraints_holes(x, x_enc)
          elseif has_sat_ann(x, unary_encoded) /\ needs_channel(ub, ob, uo) then
            annotate(x, unary_binary_channeled) /\ channel_binary_unary(x_enc, unary_encode(x))
          else % no previous encoding -> add mapper
            set_binary_encoding_as_root(x, x_enc) /\ binary_encoding_constraints(x, x_enc)
          endif;

      constraint if not is_fixed(x) then annotate(x, binary_encoded) else SAT_trace("WARNING: binary enc fix consequences of views/vars becoming fixed") endif;
    } in x_enc
  endif;

function array[int] of var bool: create_binary_encoding_variables(var int: x) =
  % TODO add special case for 0..1 ints which only should take one bit
  let {
    constraint assert(has_bounds(x), "Variable \(x) does not have any bounds and cannot be encoded");
    int: enc_size = get_enc_size(x);
  } in [ binary_new_var(x, 1+2^i) | i in 0..enc_size-1 ];

predicate set_binary_encoding_as_root(var int: x, array[int] of var bool: x_enc) =
  (x = reverse_binary(x_enc))::is_reverse_map;

% TODO has to be replaceable by set_in(_binary)..
predicate binary_encoding_constraints(var int: x, array[int] of var bool: x_enc) =
  % let {
  %   constraint SAT_trace("LOG: binary_encoding_constraints(\(x), \(x_enc))\n");
  % } in % Constrain each domain gap..
  if not has_ann(x, SAT_skip_binary_consistency_constraint) then
     binary_encoding_constraints_holes(x, x_enc)
   % ..and constrain upper/lower bound
  /\ int_le_binary(x_enc, ub(x))::expression_name_dbg("binary_encoding_constraints: \(x)<=\(ub(x))")
  /\ int_ge_binary(x_enc, lb(x))::expression_name_dbg("binary_encoding_constraints: \(x)>=\(lb(x))")
  endif;

predicate binary_encoding_constraints_holes(var int: x, array[int] of var bool: x_enc) =
  % let {
  %   constraint SAT_trace("LOG: binary_encoding_constraints_holes(\(x), \(x_enc))\n");
  % } in % Constrain each domain gap..
  forall(i in lb(x)..ub(x) diff dom(x))(
    int_ne_binary(x_enc, i)::expression_name_dbg("binary_encoding_constraints: \(x)!=\(i)")
  );

% Array of variables
function array[int,int] of var bool: binary_encode(array[int] of var int: xs) ::promise_total =
  let {
    constraint assert(SAT_encoding_mode == SAT_DEFAULT \/ SAT_encoding_mode == SAT_BINARY, "binary_encode should not be called in encoding mode \(SAT_encoding_mode)"); 
    constraint assert(forall(x in xs)(has_bounds(x)), "An element of input array \(xs) does not have any bounds and cannot be encoded");
    set of int: n = index_set(xs);
    set of int: m = 1..get_enc_size(lb_array(xs), ub_array(xs));

    % encode each var in xs with order_encode(var int) function so that CSE will reuse earlier encodings
    array[int] of var bool: xs_enc = [
      let {
        array[int] of var bool: x_enc = two_complement_extend(binary_encode(xs[i]), max(m));
      } in x_enc[j]
      | i in n, j in m
    ];
  } in array2d(n, m, xs_enc);

% TODO probably refactor out this overload
function int: binary_lb(array[int] of var bool: enc) =
  binary_lb(length(enc));

function int: binary_lb(int: enc_size) =
  -(2^(enc_size-1));

function int: binary_ub(array[int] of var bool: enc) =
  (2^(length(enc)-1))-1;

% Create (or return through CSE) the i'th most significant bit encoding x
function var bool: binary_new_var(var int: x, int: i) ::promise_total =
  let {
    var bool: xi::expression_name_dbg("b(\(x),\(i-1))");
  } in xi;

% Reverse mappings (binary to integer)
function var int: reverse_binary(array[int] of var bool: xs);
function int: reverse_binary(array[int] of bool: x_enc) =
  let {
    array[int] of int: a_enc = binary_encode_int_lin_exp_coefficients(x_enc);
    int: bit_val = sum(i in bits(index_set(x_enc)) where x_enc[i])(a_enc[i]);
    int: sign_val = if is_inverted_binary(index_set(x_enc)) then
      (not x_enc[sign(index_set(x_enc))])*a_enc[sign(index_set(x_enc))]
    else
      (x_enc[sign(index_set(x_enc))])*a_enc[sign(index_set(x_enc))]
    endif;
    int: res = bit_val + sign_val;
  } in res;

function bool: is_inverted_binary(set of int: x_enc_index_set) =
  let {
    bool: r = min(x_enc_index_set) < 0;
  } in r;
  

function set of int: bits(set of int: x_enc_index_set) =
  % TODO faster way prob unneccsary
  x_enc_index_set diff {sign(x_enc_index_set)};

function int: sign(set of int: x_enc_index_set) =
  max(x_enc_index_set);
  % if is_inverted_binary(x_enc_index_set) then
  %   % TODO BUG ?!??!?!
  %   % min(index_set(x_enc_index_set))
  %   -card(x_enc_index_set)
  % else
  %   card(x_enc_index_set)
  % endif;

% Convert a two's complement to "ordinary" binary (which is lexicographically ordered by value)
function array[int] of var bool: twos_complement_to_orderable_binary(array[int] of var bool: enc) =
  reverse(enc[..length(enc)-1] ++ [not enc[length(enc)]]);


% function array[int] of var bool: binary_sum(array[int] of var bool: as, array[int] of bool: bs) =
% let {
  
% } in
%   [
%     let {
%       var bool: carry = as[i-1] /\ bs[i-1];
%     } in
%     if bs[i] then
%       not as[i]
%     else
%       as[i]
%     endif
%     | i in 2..length(bs)
%   ];

% the sum of bits x = s in binary. 
%            s[0], s[1], ..., s[k] where 2^k >= length(x) > 2^(k-1)
predicate binary_sum(array[int] of var bool:x, 
                     array[int] of var bool:s)=
     let { int: l = length(x) } in 
     if l == 1 then s[0] = x[1]
     elseif l == 2 then 
             s[0] = (x[1] xor x[2]) /\ s[1] = (x[1] /\ x[2])
     else let { int: ll = (l div 2),
                array[1..ll] of var bool: f = [ x[i] | i in 1..ll ], 
                array[1..ll] of var bool: t = [x[i]| i in ll+1..2*ll],
                var bool: b = if ll*2 == l then false else x[l] endif,
                int: cp = floor(log2(int2float(ll))),
                array[0..cp] of var bool: fs,
                array[0..cp] of var bool: ts } in
                binary_sum(f, fs) /\ binary_sum(t, ts) /\
                int_plus_binary(fs, ts, b, s)
     endif;

