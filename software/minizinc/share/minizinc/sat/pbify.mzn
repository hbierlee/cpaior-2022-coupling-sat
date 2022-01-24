include "binary_encode.mzn";

string: SAT_ENCODE_INT_FIXED_VAR_ERROR = "The pbify.mzn functions do not handle fixed variables";

% General IP -> PB

function array[int] of int: pbify_coefficients(array[int] of int: as, array[int] of var int: bs, array[int] of SAT_encoding_modes: encs) =
  let {
    constraint assert(index_set(as) == index_set(bs), "index_set(as) == index_set(bs)");
    constraint assert(index_set(as) == index_set(encs), "index_set(as) == index_set(encs)");
  } in [ as[i] * coefficient | i in index_set(as), coefficient in pbify_coefficient(bs[i], encs[i]) ];

function array[int] of int: pbify_coefficient(var int: b, SAT_encoding_modes: enc) =
  let {
    constraint assert(not is_fixed(b), SAT_ENCODE_INT_FIXED_VAR_ERROR ++ ", but got \(b)");
    constraint assert(has_bounds(b), "Integer variable \(b) does not have any bounds and cannot be encoded");
  } in
    if enc == SAT_UNARY then
      let { array[int] of var bool: b_enc = unary_encode(b) } in [i | i in index_set(b_enc) where not is_fixed(b_enc[i]) ]
    elseif enc == SAT_ORDER then
      let { array[int] of var bool: b_enc = order_encode(b) } in [1 | i in index_set(b_enc) where not is_fixed(b_enc[i]) ]
    elseif enc == SAT_BINARY then
      let {
        array[int] of var bool: b_enc = binary_encode(b);
        array[int] of int: coefs = binary_encode_int_lin_exp_coefficients(b_enc);
      } in [ coefs[i] | i in index_set(b_enc) where not is_fixed(b_enc[i]) ]
    else
      let { constraint abort("encoding should be decided before pbification but was \(enc)"); } in
      let {constraint annotate_sat_encoding(b, enc) } in pbify_coefficient(b, enc)
    endif;

function array[int] of var bool: pbify_variable(var int: x, SAT_encoding_modes: enc) =
  % let { constraint assert(not is_fixed(x), SAT_ENCODE_INT_FIXED_VAR_ERROR ++ ", but got \(x)"); } in
  if enc == SAT_BINARY then
    array1d([ x_enc_i | x_enc_i in binary_encode(x) where not is_fixed(x_enc_i) ])
  elseif enc == SAT_UNARY then
    array1d([ x_enc_i | x_enc_i in unary_encode(x) where not is_fixed(x_enc_i) ])
  elseif enc == SAT_ORDER then
    array1d([ x_enc_i | x_enc_i in order_encode(x) where not is_fixed(x_enc_i) ])
  else
    let { constraint annotate_sat_encoding(x, enc) } in pbify_variable(x, enc)
  endif;

% This one doesn't remove fixed variables, as CSE might cause this function to not match up with the other (par, non-CSE) functions. The caller should be remove the fixed vars.
function array[int] of var bool: pbify_variables(array[int] of var int: bs, array[int] of SAT_encoding_modes: encs) =
  let {
    constraint assert(index_set(bs) == index_set(encs), "index_set(bs) == index_set(encs)");
  } in [ b_i_j | i in index_set(bs), b_i_j in pbify_variable(bs[i], encs[i]) ];

function int: pbify_constant(int: a, int: b, SAT_encoding_modes: enc) =
  a*b;

function int: pbify_constant(int: a, var int: b, SAT_encoding_modes: enc) =
  if enc == SAT_BINARY then
    let {
      array[int] of var bool: b_enc = binary_encode(b);
      array[int] of int: a_enc = binary_encode_int_lin_exp_coefficients(b_enc);
    } in sum(i in index_set(b_enc) where is_fixed(b_enc[i]) /\ fix(b_enc[i]))(a*a_enc[i])
  elseif enc == SAT_UNARY then
    let { array[int] of var bool: b_enc = unary_encode(b) } in sum(i in index_set(b_enc) where is_fixed(b_enc[i]) /\ fix(b_enc[i]))(a*i)
  elseif enc == SAT_ORDER then
    let { array[int] of var bool: b_enc = order_encode(b) } in sum(i in index_set(b_enc) where is_fixed(b_enc[i]) /\ fix(b_enc[i]))(a) + (min(index_set(b_enc)) - 1) * a
  else
    let { constraint abort("encoding should be decided before pbification but was \(enc)"); } in
    let { constraint annotate_sat_encoding(b, enc) } in pbify_constant(a, b, enc)
  endif;

function int: encode_int_lin_exp_constant(array[int] of int: as, array[int] of var int: bs, array[int] of SAT_encoding_modes: encs) =
  let {
    constraint assert(index_set(as) == index_set(bs), "index_set(as) == index_set(bs)");
    constraint assert(index_set(as) == index_set(encs), "index_set(as) == index_set(encs)");
  } in
  sum(i in index_set(as))(pbify_constant(as[i], bs[i], encs[i]));

function array[int] of int: binary_encode_int_lin_exp_coefficients(array[int] of var bool: b_enc) =
  let {
    int: n = length(b_enc);
    array[int] of int: a_enc = [ 2 ^ i | i in 0..n-2 ] ++ [ -(2 ^ (n-1)) ];
  } in
  if is_inverted_binary(index_set(b_enc)) then
    % array1d(-n..-1, reverse([ -abs(a_enc_i) | a_enc_i in a_enc ]))
    array1d(-n..-1, reverse([ -a_enc_i | a_enc_i in a_enc ]))
  else
    a_enc
  endif;



% Some optimization functions that can be re-used

function array[int] of int: filter_lin_exp_fixed_vars_and_zero_pars_for_coefficients( array[int] of int: as, array[int] of var int: bs) =
  [ as[i] | i in index_set(bs) where (not is_fixed(bs[i])) /\ as[i] != 0 ];

function array[int] of var int: filter_lin_exp_fixed_vars_and_zero_pars_for_variables(array[int] of int: as, array[int] of var int: bs) =
  [ bs[i] | i in index_set(bs) where (not is_fixed(bs[i])) /\ as[i] != 0 ];

function int: filter_lin_exp_fixed_vars_and_zero_pars_for_constant(array[int] of int: as, array[int] of var int: bs) =
  sum(i in index_set(bs) where is_fixed(bs[i]))(as[i]*fix(bs[i]));




