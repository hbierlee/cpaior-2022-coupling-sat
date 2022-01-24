predicate bool_clause_weighted(array[int] of var bool: as, array[int] of var bool: bs, int: weight, var int: avoid_cse) =
  bool_clause_weighted(as,bs,weight,avoid_cse,false);
predicate bool_clause_weighted(array[int] of var bool: as, array[int] of var bool: bs, int: weight, var int: avoid_cse, bool: is_solve_minimize); % prevent CSE
predicate bool_clause_weighted(int: weight, var int: avoid_cse); % (1,weight) always satisfied (minimizing or maximizing)

predicate fzn_obj_int_lin_eq(array[int] of int: as_in, array[int] of var int: bs_in, int: c_in, var int: obj) =
  let {
    array[int] of int: as = filter_lin_exp_fixed_vars_and_zero_pars_for_coefficients(as_in, bs_in);
    array[int] of var int: bs = filter_lin_exp_fixed_vars_and_zero_pars_for_variables(as_in, bs_in);
    int: c = c_in + filter_lin_exp_fixed_vars_and_zero_pars_for_constant(as_in, bs_in);
  } in fzn_obj_int_lin_eq_dispatch(as, bs, c, obj);

predicate fzn_obj_int_lin_eq_dispatch(array[int] of int: as, array[int] of var int: bs, int: c, var int: obj) =
  let {
    array[int] of int: prefs = int_lin_comp_enc_prefs(as, bs, c, INT_EQ);
    array[int] of SAT_encoding_modes: encodings = get_one_sat_encoding(bs, prefs, false);
    constraint forall(i in index_set(bs))(
      let {
        SAT_encoding_modes: encoding = encodings[i];
        array[int] of int: as_enc = pbify_coefficient(bs[i], encoding);
        array[int] of var bool: bs_enc = pbify_variable(bs[i], encoding);
        int: c_enc = pbify_constant(as[i], bs[i], encoding);

        var -1..0: avoid_cse_c;
        constraint clause_weighted(-c_enc, avoid_cse_c);
      } in
      if use_binary_views /\ encoding == SAT_BINARY then
        let {
          set of int: bits = bits(index_set(bs_enc));
          int: sign = sign(index_set(bs_enc));
          bool: EARLY = lb(bs[i]) < 0;
          var bool: s = bs_enc[sign];
          constraint if EARLY then
            let {
              var -1..0: avoid_cse_early;
            } in bool_clause_weighted([],[s],-as[i],avoid_cse_early,true)
            endif;
        } in
        forall(j in bits where not is_fixed(bs_enc[j]) /\ as_enc[j] != 0)(
          let {
            var bool: x = bs_enc[j];
            int: P = as[i]*as_enc[j];
          } in
            if EARLY then
            let {
             var -1..0: avoid_cse;
            } in
              bool_clause_weighted([x],[s],-P,avoid_cse,true)
            else
              let {
                var -1..0: avoid_cse;
              } in
              bool_clause_weighted([s],[x],P,avoid_cse,true)
            endif
        )
        else
          forall(j in index_set(bs_enc) where not is_fixed(bs_enc[j]) /\ as_enc[j] != 0)(
           let {
             int: weight = -as[i]*as_enc[j];  % if bs_enc[j] is false, we're missing out on its value
             var -1..0: avoid_cse;
           } in clause_weighted([], [bs_enc[j]], weight, avoid_cse)
          )
        endif
    );

    var -1..0: avoid_cse;
    constraint clause_weighted(-c, avoid_cse);
  } in true;


% A weighted clause that is always falsified. The objective value will decrease by the weight (no matter whether we min/maximize).
predicate clause_weighted(int: weight, var int: avoid_cse) =
  if weight != 0 then
    bool_clause_weighted(weight, avoid_cse)
  endif;

predicate clause_weighted(array[int] of bool: as, array[int] of bool: bs, int: weight, var int: avoid_cse) =
  if not clause(as,bs) then clause_weighted(weight, avoid_cse) endif;

predicate clause_weighted(array[int] of var bool: as, array[int] of var bool: bs, int: weight, var int: avoid_cse) =
  if weight > 0 then % TODO could just check x_enc[i] ? IF x_enc[i]>0 <-> weight>0  ?? would need to loop per int var instead of bool var
    bool_clause_weighted(as, bs, weight, avoid_cse)
  else % negate literals with negative weights to obtain only positive weights (a constant weighted clause (1,w) should be added later)
    let {
      int: n = length(as)+length(bs);
    } in
    if n == 1 then
      let {
        var -1..0: avoid_cse_2;
      } in
      clause_weighted(bs, as, -weight,avoid_cse) % negation of x incurs a now positive weight
      /\
      clause_weighted(weight, avoid_cse_2) % incur the negative cost
    elseif n == 2 then
      let {
        constraint abort("UNSUPPORTED since change to true weighted clause");
        array[1..2] of var bool: xs = as ++ [ not b | b in bs ];
        var bool: a = xs[1];
        var bool: b = xs[2];

        var -1..0: avoid_cse_2;
        var -1..0: avoid_cse_3;
      } in
        clause_weighted([a],[b],-weight, avoid_cse) /\
        clause_weighted([a],[],weight, avoid_cse_2) /\
        clause_weighted(weight, avoid_cse_3)
        % ALT
        % clause_weighted([b],[a],-weight,i) /\
        % clause_weighted([b],[],weight,i+1) /\
        % clause_weighted(weight,i+2)
      else
        abort("UNSUPPORTED")
    endif
  endif;

% predicate bool_and_weighted(array[int] of var bool: as, array[int] of var bool: bs, int: weight, var int: avoid_cse) =
%   let {
%     constraint trace("bool_and_weighted \(as) \(bs)\n");
%     constraint abort("has old semantics");
%   } in
%   assert(length(as)+length(bs)==2, "TODO length(as)+length(bs)==2") /\
%   clause_weighted(weight, avoid_cse) /\
%   % clause_weighted([],[a,b],-weight,i+1);
%   clause_weighted(bs,as,-weight, avoid_cse);
