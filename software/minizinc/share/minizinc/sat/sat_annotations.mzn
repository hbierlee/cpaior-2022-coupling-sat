

% Ignores SAT encodings that do not match the current encoding mode
function bool: has_sat_ann(var int: x, ann: encoding) =
  if SAT_encoding_mode == SAT_DEFAULT then
    has_ann(x, encoding)
  elseif SAT_encoding_mode == SAT_UNARY then
    encoding == unary_encoded /\ has_ann(x, unary_encoded)
  elseif SAT_encoding_mode == SAT_ORDER then
    encoding == order_encoded /\ has_ann(x, order_encoded)
  elseif SAT_encoding_mode == SAT_BINARY then
    encoding == binary_encoded /\ has_ann(x, binary_encoded)
  else
    abort("Unexpected encoding annotation argument in has_sat_ann")
  endif;

function bool: has_sat_ann(int: x, ann: encoding) =
  let {
   constraint SAT_trace("WARNING: has_sat_ann called with fixed value \(x) for encoding \(encoding)\n");
  } in if SAT_encoding_mode == SAT_DEFAULT then
    true
  elseif SAT_encoding_mode == SAT_UNARY then
    encoding == unary_encoded
  elseif SAT_encoding_mode == SAT_ORDER then
    encoding == order_encoded
  elseif SAT_encoding_mode == SAT_BINARY then
    encoding == binary_encoded
  else
    abort("Unexpected encoding annotation argument in has_sat_ann")
  endif;

function SAT_encoding_modes: decide_encoding(var int: x, SAT_encoding_modes: default_encoding) =
  encodings(x, default_encoding)[1];

function array[int] of SAT_encoding_modes: decide_encodings(array[int] of var int: xs, SAT_encoding_modes: default_encoding) =
  [ decide_encoding(x, default_encoding) | x in xs ];

function array[int] of SAT_encoding_modes: decide_encodings(array[int] of var int: xs, array[int] of SAT_encoding_modes: default_encodings) =
  let {
    constraint assert(index_set(xs) == index_set(default_encodings), "index_set(xs) == index_set(default_encodings)");
  } in [ decide_encoding(xs[i], default_encodings[i]) | i in index_set(xs) ];


function array[int] of SAT_encoding_modes: inherit_encodings(array[int] of var int: xs, SAT_encoding_modes: default_encoding) =
  let {
    set of SAT_encoding_modes: encs = { e | encs in encodings(xs), e in encs };
  } in decide_encodings(xs, if encs == {} then default_encoding else encs[1] endif);
function set of SAT_encoding_modes: encodings(int: x, SAT_encoding_modes: default_encoding) =
  let {
    constraint SAT_trace("WARNING: encodings called on fixed int \(x) with default encoding \(default_encoding)\n");
    constraint assert(not SAT_strict, "not SAT_strict");
  } in {};

function set of SAT_encoding_modes: encodings(int: x) =
  {};

function set of SAT_encoding_modes: encodings(var int: x) =
  if SAT_encoding_mode == SAT_DEFAULT then
    { [SAT_UNARY, SAT_ORDER, SAT_BINARY][e]
    | e in 1..3 where [ has_ann(x, unary_encoded), has_ann(x, order_encoded), has_ann(x, binary_encoded) ][e] }
  else
    {SAT_encoding_mode}
  endif;

function array[int] of set of SAT_encoding_modes: encodings( array[int] of var int: xs) =
  [ encodings(x) | x in xs ];

function set of SAT_encoding_modes: encodings(var int: x, SAT_encoding_modes: default_encoding) =
  let {
    set of SAT_encoding_modes: encs = encodings(x);
  } in
    if encs == {} then
      let { constraint annotate_sat_encoding(x, default_encoding); } in {default_encoding}
    else
      encs
    endif;

function bool: has_sat_ann(var int: x) =
  has_sat_ann(x, unary_encoded) \/ has_sat_ann(x, order_encoded) \/ has_sat_ann(x, binary_encoded);

% Ignores SAT encodings that do not match the current encoding mode
function bool: has_sat_ann(array[int] of var int: xs, ann: default_encoding) =
  % filter out fixed vars, since they will return true for all encodings!
  exists(x in xs where not is_fixed(x))(has_sat_ann(x, default_encoding));

% TODO an array value that takes union of get_sat_encodings for each var element

function array[int] of bool: get_sat_encodings() =
  [ SAT_encoding_mode in { SAT_DEFAULT, SAT_UNARY }, SAT_encoding_mode == SAT_ORDER, SAT_encoding_mode == SAT_BINARY ];

% returns all available sat_encodings of x (e.g., [true,true,false] -> x has direct/order, but not binary)
function array[int] of bool: get_sat_encodings(var int: x) =
  [has_sat_ann(x, unary_encoded), has_sat_ann(x, order_encoded), has_sat_ann(x, binary_encoded)];

% Returns all available sat_encodings of x, but takes into account an order of preference.
  % If no encoding exist, the most preferred will be created.
  % If multiple exist, we pick encodings which we want to use.
function array[int] of bool: get_sat_encodings(var int: x, array[int] of int: preferences) = get_sat_encodings(x, preferences, <>);
function array[int] of bool: get_sat_encodings(var int: x, array[int] of int: preferences, opt bool: overrule_opt) =
  let {
    bool: overrule = overrule_opt default false;
    array[int] of bool: encs = get_sat_encodings(x);
    bool: annotate = not exists(encs) \/ overrule;
    constraint if annotate then
      % annotate most preferred (note SAT_encoding_mode will override this)
      annotate_sat_encoding(x, [SAT_UNARY, SAT_ORDER, SAT_BINARY][preferences[1]])
    endif;
  } in pick_sat_encodings(
      if annotate then get_sat_encodings(x) else encs endif,
      preferences,
    );

% Returns all occurring encodings in an var int array xs
  % [true,true,false] -> at least one x in xs has the direct encoding and at least one x has order (although they might be different ones)
function array[int] of bool: get_sat_encodings(array[int] of var int: xs) =
  if SAT_encoding_mode == SAT_DEFAULT then
    let {
      % fixed vars have all encodings, so don't consider those
      array[int] of var int: xs_vars = [ x | x in xs where not is_fixed(x) ];
      array[int,int] of bool: xs_encs = get_sat_encodings_for_each(xs_vars);
         % max over each of (three) encoding columns
    } in [ max(i in index_set_1of2(xs_encs))(xs_encs[i,j]) | j in index_set_2of2(xs_encs) ]
  else
    get_sat_encodings()
  endif;

% Returns a 2D array with the existing encodings for each x in xs
function array[int,int] of bool: get_sat_encodings_for_each(array[int] of var int: xs) =
  if length(xs) == 0 then
    array2d(
      1..1,
      index_set(SAT_ENCODING_ANNOTATIONS),
      get_sat_encodings()
    )
  else
    array2d(
      index_set(xs),
      index_set(SAT_ENCODING_ANNOTATIONS),
      [ enc | x in xs, enc in get_sat_encodings(x) ]
    )
  endif;

% Analogous to get_sat_encodings for single var int with preferences
function array[int] of bool: get_sat_encodings(array[int] of var int: xs, array[int] of int: preferences) =
  if SAT_encoding_mode == SAT_DEFAULT then
    let {
      array[int] of bool: encs = get_sat_encodings(xs);
      bool: has_encoding = exists(encs);
      constraint if not has_encoding then
        % annotate most preferred (note SAT_encoding_mode will override this)
        annotate_sat_encoding(xs, [SAT_UNARY, SAT_ORDER, SAT_BINARY][preferences[1]])
      endif;
    } in pick_sat_encodings( % refetch in case we annotated
        if has_encoding then encs else get_sat_encodings(xs) endif,
        preferences,
      )
  else
    get_sat_encodings()
  endif;

function array[int] of SAT_encoding_modes: get_one_sat_encoding(array[int] of var int: bs) =
  [ pick_one_sat_encoding(get_sat_encodings(b)) | b in bs ];
function array[int] of SAT_encoding_modes: get_one_sat_encoding(array[int] of var int: bs, array[int] of int: preferences) =
  get_one_sat_encoding(bs, preferences, <>);
function array[int] of SAT_encoding_modes: get_one_sat_encoding(array[int] of var int: bs, array[int] of int: preferences, opt bool: overrule) =
  [ pick_one_sat_encoding(get_sat_encodings(b, preferences, overrule), preferences) | b in bs ];

function SAT_encoding_modes: get_one_sat_encoding_var(var int: x, array[int] of int: preferences) =
  get_one_sat_encoding_var(x, preferences, <>);
function SAT_encoding_modes: get_one_sat_encoding_var(var int: x, array[int] of int: preferences, opt bool: overrule) =
   pick_one_sat_encoding(get_sat_encodings(x, preferences, overrule), preferences);
% function SAT_encoding_modes: get_one_sat_encoding_var(var int: x, array[int] of bool: encs, array[int] of int: preferences) =

  
function SAT_encoding_modes: pick_one_sat_encoding(array[int] of bool: encs) =
  let {
    int: n = count(encs);
  } in
  if n == 0 then
    SAT_DEFAULT
  elseif n == 1 then
    SAT_SINGLE_ENCODING_MODES[arg_max(encs)]
  else
    let {
      constraint abort("");
    } in SAT_DEFAULT
  endif;

function SAT_encoding_modes: pick_one_sat_encoding(array[int] of bool: encs, array[int] of int: preferences) =
  SAT_SINGLE_ENCODING_MODES[preferences[arg_max(i in preferences)(encs[i])]];

% Pick which sat encodings to constrain with; there are two strategies:
  % A) Pick the most preferred one
  % B) Constrain with all available encodings
function array[int] of bool: pick_sat_encodings(array[int] of bool: encs, array[int] of int: preferences) =
  let {
    constraint assert(exists(encs), "the encs argument of pick_sat_encodings should have at least one encoding but was \(encs).");
  } in
    if SAT_constrain_all_encodings then
      encs
    else
      let { % pick the most preferred existing encoding
        int: most_preferred = preferences[arg_max(i in preferences)(encs[i])];
      } in [ i == most_preferred | i in index_set(encs) ]
    endif;

% TODO std?
function bool: max(array[int] of bool: xs) =
  if length(xs) == 0 then
    true
  else
    max(x in xs)(bool2int(x)) == 1
  endif;


% % % TODO [bug?] if removed:
% % || MiniZinc: evaluation error: 
% % ||   /home/hbierlee/Projects/libminizinc/share/minizinc/sat//options.mzn:37:
% % ||   in variable declaration fSAT_encoding_mode
% % ||   cannot evaluate expression 'fSAT_encoding_mode'
% % || 
predicate annotate_sat_encoding(int: x, SAT_encoding_modes: default_encoding) =
  SAT_trace("WARNING: annotate_sat_encoding called on value \(x) with default_encoding \(default_encoding)\n") /\ true;

predicate annotate_sat_encoding(array[int] of var int: xs, SAT_encoding_modes: default_encoding) =
  forall(x in xs where not is_fixed(x))(annotate_sat_encoding(x, default_encoding));

predicate annotate_sat_encoding(var int: x, SAT_encoding_modes: default_encoding) =
  if SAT_encoding_mode == SAT_DEFAULT then
    if default_encoding == SAT_UNARY then
      annotate(x, unary_encoded)
    elseif default_encoding == SAT_ORDER then
      annotate(x, order_encoded)
    elseif default_encoding == SAT_BINARY then
      annotate(x, binary_encoded)
    else
      abort("SAT default encoding is not UNARY/ORDER/BINARY but \(default_encoding)")
    endif
  elseif SAT_encoding_mode == SAT_UNARY then
    annotate(x, unary_encoded)
  elseif SAT_encoding_mode == SAT_ORDER then
    annotate(x, order_encoded)
  elseif SAT_encoding_mode == SAT_BINARY then
    annotate(x, binary_encoded)
  else
    abort("Unknown SAT_encoding")
  endif;


function array[int] of int: SAT_encoding_mode_to_prefs(SAT_encoding_modes: enc, array[int] of int: prefs) =
  if enc == SAT_DEFAULT then
    prefs
  elseif enc == SAT_UNARY then
    [ 1 ] ++ [ p | p in prefs where p != 1 ]
  elseif enc == SAT_ORDER then
    [ 2 ] ++ [ p | p in prefs where p != 2 ]
  elseif enc == SAT_BINARY then
    [ 3 ] ++ [ p | p in prefs where p != 3 ]
  else
    let {
      constraint abort("Unknown encoding mode");
    } in []
  endif;

array[int] of ann: SAT_ENCODING_ANNOTATIONS = [unary_encoded, order_encoded, binary_encoded];
array[int] of SAT_encoding_modes: SAT_SINGLE_ENCODING_MODES = [SAT_UNARY, SAT_ORDER, SAT_BINARY];

% For testing purposes (makes sure x is encoded in at least 1 way)
array[int] of var bool: encode(var int: x, SAT_encoding_modes: enc) =
  if enc == SAT_UNARY then
    unary_encode(x)
  elseif enc == SAT_ORDER then
    order_encode(x)
  elseif enc == SAT_BINARY then
    binary_encode(x)
  else
    let { constraint abort("encode called on unknown enc \(enc)"); } in []
  endif
  ;
predicate encoded(var int: x) =
  let {
    constraint if not has_sat_ann(x, unary_encoded) /\ not has_sat_ann(x, order_encoded) /\ not has_sat_ann(x, binary_encoded) then
      annotate_sat_encoding(x, SAT_UNARY)
    endif;
  } in let {
    array[int] of var bool: x_enc =
      if has_sat_ann(x, unary_encoded) then
        unary_encode(x)
      elseif has_sat_ann(x, order_encoded) then
        order_encode(x)
      elseif has_sat_ann(x, binary_encoded) then
        binary_encode(x)
      else
        let {
          constraint abort("XXX") ;
        } in []
    endif;
  } in true;
