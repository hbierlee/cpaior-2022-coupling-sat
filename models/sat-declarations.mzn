f_mzn_sat=false;

enum Comparator = { INT_EQ, INT_LE, INT_NE };
function array[int] of var bool: unary_encode(var int: x) =
  [];
function array[int] of var bool: order_encode(var int: x) =
  [];
function array[int] of var bool: binary_encode(var int: x) =
  [];

function array[int] of var bool: int_plus_order(array[int] of var bool: xs, int: c) =
  let { constraint abort("STUB"); } in [];

predicate int_le_order(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  let { constraint abort("STUB"); } in true;


function bool: has_sat_ann(var int: x, ann: encoding) =
  true;

function bool: has_sat_ann(int: x, ann: encoding) =
  true;

function bool: has_sat_ann(var int: x) =
  true;
  % Ignores SAT encodings that do not match the current encoding mode
function bool: has_sat_ann(array[int] of var int: xs, ann: default_encoding) =
  true;
  % TODO an array value that takes union of get_sat_encodings for each var element

function array[int] of bool: get_sat_encodings() =
  [true];
  % returns all available sat_encodings of x (e.g., [true,true,false] -> x has direct/order, but not binary)
function array[int] of bool: get_sat_encodings(var int: x) =
  [true];

function array[int] of bool: get_sat_encodings(var int: x, array[int] of int: preferences) =
  [true];

function array[int] of bool: get_sat_encodings(array[int] of var int: xs) =
  [true];

  % Returns a 2D array with the existing encodings for each x in xs
function array[int,int] of bool: get_sat_encodings_for_each(array[int] of var int: xs) =
  [|true|];

% Analogous to get_sat_encodings for single var int with preferences
function array[int] of bool: get_sat_encodings(array[int] of var int: xs, array[int] of int: preferences) =
  [true];

function array[int] of SAT_encoding_modes: get_one_sat_encoding(array[int] of var int: bs) = [SAT_DEFAULT];
function array[int] of SAT_encoding_modes: get_one_sat_encoding(array[int] of var int: bs, array[int] of int: preferences) = [SAT_DEFAULT];

function array[int] of SAT_encoding_modes: get_one_sat_encoding(array[int] of var int: bs, array[int] of int: preferences, opt bool: overrule) =
  [SAT_DEFAULT];

function SAT_encoding_modes: pick_one_sat_encoding(array[int] of bool: encs, array[int] of int: preferences) =
  SAT_DEFAULT;

predicate annotate_sat_encoding(int: x, SAT_encoding_modes: default_encoding) =
  true;

predicate annotate_sat_encoding(array[int] of var int: xs, SAT_encoding_modes: default_encoding) =
  true;

predicate annotate_sat_encoding(var int: x, SAT_encoding_modes: default_encoding) =
  true;

function array[int] of int: SAT_encoding_mode_to_prefs(SAT_encoding_modes: enc, array[int] of int: prefs) =
  [];

function var bool: order_encoding_element_partial(array[int] of var bool: x_enc, int: i) =
  let { constraint abort("STUB"); } in true;

function var int: affine(var int: x, int: scalar, int: add) =
  x*scalar + add;
