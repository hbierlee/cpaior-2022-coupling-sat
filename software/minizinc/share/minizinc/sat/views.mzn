predicate partial_view(var int: view, var int: x) =
  affine_view(view, x, 1, 0, true, get_one_sat_encoding_var(view, [2,1,3]));

predicate affine_view(var int: view, var int: x, SAT_encoding_modes: encoding) =
  affine_view(view, x, 1, 0, false, encoding);
predicate affine_view(var int: view, var int: x, int: scalar, SAT_encoding_modes: encoding) =
  affine_view(view, x, scalar, 0, false, encoding);
predicate affine_view(var int: view, var int: x, int: scalar, int: add, SAT_encoding_modes: encoding) =
  affine_view(view, x, scalar, add, false, encoding); % TODO bleh check partial for full views?

function var int: affine(var int: x, int: scalar) =
  affine(x, scalar, 0);
function var int: affine(var int: x, int: scalar, int: add)::promise_total =
  if scalar == 1 /\ add == 0 then
    x
  else
    let {
      constraint assert(scalar != 0, "TODO view: scalar of 0"); % TODO
      set of int: view_dom = lin_exp_lb([scalar],[x])+add..lin_exp_ub([scalar],[x])+add::is_defined_var;
      var view_dom: view;
      SAT_encoding_modes: encoding = get_one_sat_encoding_var(x, [2,1,3]);
      constraint if card(encodings(x)) <= 1 then SAT_trace("WARNING: card(encodings(x)) <= 1 otherwise this is an ambiguous call for \(x) with \(encodings(x))\n") endif;
      constraint annotate_sat_encoding(view, encoding);
      constraint affine_view(view, x, scalar, add, encoding) ::defines_var(view);
    } in view
  endif;

predicate affine_view(int: view, int: x, int: scalar, int: add, bool: is_partial, SAT_encoding_modes: encoding) =
  let {
    constraint assert(not is_partial, "fixed affine view: not is_partial");
  } in
  view == x*scalar + add;

bool: use_affine = true;
predicate affine_view(var int: view, var int: x, int: scalar, int: add, bool: is_partial, SAT_encoding_modes: encoding) =
  let {
    constraint SAT_trace("CREATE VIEW " ++ show_view(view, x, scalar, add, is_partial, encoding, SAT_DEFAULT));
    constraint assert(not has_ann(view, SAT_is_view), "not has_ann(view, SAT_is_view)");
  } in
    if encoding == SAT_BINARY /\ scalar == 1 /\ add == 0 /\ is_partial /\ (min(dom(view)) in -1..0 \/ max(dom(view)) in -1..0) then
      let {
        constraint annotate(view, SAT_is_view);
        constraint annotate(view, SAT_view(x, scalar, add, bool2int(is_partial)));
      } in let {
        array[int] of var bool: view_enc = if SAT_auto_resolve_view then encode(view, encoding) else [] endif;
      } in true
    elseif encoding != SAT_BINARY \/ (scalar == -1 /\ add == -1) then % TODO scalar in {2^k,0,-(2^k)} -> actual view
      let {
        constraint assert(encoding != SAT_BINARY \/ not is_partial, "not expecting this");
        constraint annotate(view, SAT_is_view);
        constraint annotate(view, SAT_view(x, scalar, add, bool2int(is_partial)));
      } in let {
        array[int] of var bool: view_enc = if SAT_auto_resolve_view then encode(view, encoding) else [] endif;
      } in true
    else
      assert(not is_partial, "not expecting this") /\
      int_lin_of_2_binary([scalar,-1],[x,view],-add, INT_EQ)
    endif;

bool: use_clean_view = true;

function array[int] of var bool: clean_view(array[int] of var bool: x_enc, SAT_encoding_modes: encoding) =
  if not use_clean_view then
    x_enc
  elseif encoding == SAT_UNARY then
    x_enc
  elseif encoding == SAT_ORDER then
    if length(x_enc) == 1 then
      x_enc % bit tricky with the arg_max on left slice not finding any elements
    elseif is_fixed(x_enc) then
      array1d(min(index_set(x_enc))..min(index_set(x_enc)), [true])
    else
      let {
        int: slice_left = min(index_set(x_enc)) + arg_max(x_enc_i in array1d(x_enc))(not is_fixed(x_enc_i)) - 2;
        int: slice_right = max(index_set(x_enc)) + 1 - arg_max(x_enc_i in array1d(reverse(x_enc)))(not is_fixed(x_enc_i));
        set of int: slice = slice_left..slice_right;
        constraint assert(fix(x_enc[min(slice)]), "clean order encoding (view): first element should be fixed");
        constraint assert(not is_fixed(x_enc[min(slice)+1]), "clean order encoding (view): second element should not be fixed");
        constraint assert(not is_fixed(x_enc[max(slice)]), "clean order encoding (view): last element should not be fixed");
        constraint assert(max(slice)+1>max(index_set(x_enc)) \/ (is_fixed(x_enc[max(slice)+1]) /\ not fix(x_enc[max(slice)+1])), "clean order encoding (view): element after last element should be fixed and false or should not exist in the original");
        % TODO we could check for fixed variables in the center of the encoding
      } in x_enc[slice]
    endif
  else
    % TODO any cleaning opportunity?
    x_enc
  endif;

function var int: resolve_view_var(var int: x) =
  if has_ann(x, SAT_is_view) then
    resolve_view_var(get_ann_arg(x, SAT_view(x), 1))
  else
    x
  endif;

function array[int] of var bool: resolve_view(var int: view, SAT_encoding_modes: encoding) =
  let {
    constraint assert(has_ann(view, SAT_is_view), "resolve_view: has_ann(view, SAT_is_view)");
  } in
  resolve_view(
    view,
    get_ann_arg(view, SAT_view(view), 1),
    fix(get_ann_arg(view, SAT_view(view), 2)),
    fix(get_ann_arg(view, SAT_view(view), 3)),
    fix(get_ann_arg(view, SAT_view(view), 4)) == 1,
    encoding,
  );

array[int] of var bool: take_two_complement(array[int] of var bool: bs) =
  [ not b | b in bs ];

function string: show_view(var int: view, var int: x, int: scalar, int: add, bool: is_partial, SAT_encoding_modes: view_encoding, SAT_encoding_modes: x_encoding) =
   "(\(view_encoding)->\(x_encoding)) \(view) in \(dom(view)) on " ++ if scalar != 1 then "\(scalar)*" else "" endif ++ "(\(x) in \(dom(x)))"++ if add!=0 then (if add > 0 then "+" else "-" endif)++"\(abs(add)) " else " " endif ++ if is_partial then "[\(dom(view))] partial " else "total" endif ++ "\n";

function array[int] of var bool: resolve_view(var int: view, var int: x, int: scalar, int: add, bool: is_partial, SAT_encoding_modes: view_encoding) =
  let {
    SAT_encoding_modes: x_encoding = get_one_sat_encoding_var(x,[2,3,1]);
    constraint SAT_trace("RESOLVE VIEW " ++ show_view(view, x, scalar, add, is_partial, view_encoding, x_encoding));
    } in let { 
    % TODO what if multiple view annotations?
    % TODO take into account domain of x? What should exactly happen if the views domain/view_encoding is larger ?
    % TODO can we shorten views (if most the outsides are fixed ? ); yes; this is what int_plus_* etc.. should do efficiently ! 
            % || view:order_encode(x) 0..4 [true, X_INTRODUCED_180_, false, false, false]

    array[int] of var bool: x_enc = encode(x, x_encoding);
    array[int] of var bool: x_enc_clean = clean_view(x_enc, x_encoding);
  } in let {
    constraint assert(not (is_partial /\ view_encoding == SAT_BINARY /\ x_encoding == SAT_ORDER), "asdf");
    array[int] of var bool: affine_view =
      if x_encoding == SAT_UNARY then
        int_plus_unary(
          int_times_unary(
            x_enc_clean,
            scalar,
          ),
          add,
        )
      elseif x_encoding == SAT_ORDER then
        int_plus_order(
          int_times_order(
            x_enc_clean,
            scalar,
          ),
          add,
        )
      elseif x_encoding == SAT_BINARY then
        let {
          constraint assert(add==-1 /\ scalar==-1 /\ not is_partial, "resolve view binary: add==-1 and scalar==-1");
        } in
        take_two_complement(x_enc_clean)
      else
        let { constraint abort("unsupported x view_encoding type \(x_encoding)"); } in []
      endif;

    array[int] of var bool: partial_affine_view =
      if is_partial then
        if x_encoding == SAT_UNARY then
          affine_view[lb(view)..ub(view)]
        elseif x_encoding == SAT_ORDER then
          let {
            set of int: slice = dom(view) intersect index_set(affine_view); % TODO pretty sure; the affine_view might have shrunk which is ok
          } in
              if slice == {} then % TODO this might be specific to maximum
                if max(dom(view)) < min(index_set(affine_view)) then
                  order_encode(max(dom(view)))  % the slice is left of its x (=affine_view), so it's all-true; reverser_order then returns its max element
                else
                  order_encode(min(dom(view)))  % the slide is right of its x, so its all false; so its the min value ?
                endif
              else
                array1d(slice, [true]++affine_view[slice diff {min(slice)}]) % TODO perhaps avoid concat if affine_view[min(slice)] == true
              endif
        elseif x_encoding == SAT_BINARY then
          affine_view
        else
          let { constraint abort("unsupported view view_encoding type \(view_encoding)"); } in []
        endif
      else
        affine_view
      endif;
    array[int] of var bool: partial_affine_view_clean = clean_view(partial_affine_view, view_encoding);
  } in let {

    array[int] of var bool: channelled_view_enc =
      if x_encoding != view_encoding then
        let {
            array[int] of var bool: view_enc = create_binary_encoding_variables(view);
          % TODO bug! minizinc: /home/hbierlee/Projects/libminizinc/lib/flatten/flat_exp.cpp:77: MiniZinc::EE MiniZinc::flat_exp(MiniZinc::EnvI&, const MiniZinc::Ctx&, MiniZinc::Expression*, MiniZinc::VarDecl*, MiniZinc::VarDecl*): Assertion `ctx.b != C_ROOT || b == constants().varTrue' failed.
          % constraint channel_binary_order(view_enc,partial_affine_view_clean);
        } in view_enc
      else
        partial_affine_view_clean
    endif;
    constraint if x_encoding != view_encoding then channel_binary_order(channelled_view_enc,partial_affine_view_clean) endif;
  } in channelled_view_enc;
