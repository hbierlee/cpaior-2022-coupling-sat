
function array[int] of int: find_order_encoding_views(array[int] of int: as, array[int] of set of int: groups) =
  let {
    array[int] of set of int: groups_ext = array1d(0..length(groups)+1, [{min(index_set(as))-1, min(index_set(as))-1}] ++ groups ++ [{max(index_set(as))+1, max(index_set(as))+1}]);
    array[int] of bool: views_left = [
      let {
        bool: is_range = is_range(groups_ext[u]);
        bool: is_adjacent = max(groups_ext[u-1])+1==min(groups_ext[u]);
      } in is_range /\ is_adjacent | u in index_set(groups)
    ];

    array[int] of bool: views_right = [
      let {
        bool: is_range = is_range(groups_ext[u]);
        bool: is_adjacent = max(groups_ext[u])+1==min(groups_ext[u+1]);
      } in is_range /\ is_adjacent | u in index_set(groups)
    ];
  } in [arg_min_extended(views_left) - 1, arg_min_extended(reverse(views_right)) - 1];
        
function int: arg_min_extended(array[int] of bool: as) =
  let {  % if no false, will return length plus 1
    int: a = arg_min(as);
  } in if a == min(index_set(as)) /\ as[1] then max(index_set(as))+1 else a endif;

% TODO can we (in some cases) reorder as to create more repeating elements? If there is value symmetry?

function SAT_encoding_modes: first_sat_pred(array[int] of ann: annotations, SAT_encoding_modes: default_encoding) =
  let {
    % array[int] of ann: rev_preds = reverse(annotations); % TODO annotations should be reversed
    ann: a = annotations[arg_max(a in annotations)(a in [unary_encoded, order_encoded, binary_encoded])];
  } in
    if a == unary_encoded then
      SAT_UNARY
    elseif a == order_encoded then
      SAT_ORDER
    elseif a == binary_encoded then
      SAT_BINARY
    else
      default_encoding
    endif;

predicate array_int_element(var int: b, array[int] of int: as, var int: c) ann:annotations =
  let {
    constraint c in dom_array(as);
    SAT_encoding_modes: constraint_enc = first_sat_pred(annotations, SAT_DEFAULT);
    constraint if constraint_enc != SAT_DEFAULT then 
      let {
        SAT_encoding_modes: unused = decide_encoding(c, constraint_enc);
      } in true endif; % if constraint has enc anno
  } in
  let {
    array[int] of SAT_encoding_modes: encs = inherit_encodings([b,c], SAT_UNARY);
    constraint if not is_fixed(c) /\ encs[2] == SAT_UNARY then annotate(c, SAT_skip_unary_consistency_constraint) endif;
    % constraint if not is_fixed(c) /\ encs[2] == SAT_ORDER then annotate(c, SAT_skip_order_consistency_constraint) endif; % TODO decide on whether this should be added
    % constraint if not is_fixed(c) /\ encs[2] == SAT_BINARY then annotate(c, SAT_skip_binary_consistency_constraint) endif; % TODO decide on whether this should be added
  } in
    if SAT_array_int_element_method == DIRECT then
    forall(i in dom(b))(
      let {  % /\ selectors -> (result_var_1 /\ not result_var_2 /\ ...)
        array[int] of var bool: selectors = int_eq_var_par_func(b, i); % conjunction of encoding variables
        array[int] of var bool: result = int_eq_var_par_func(c, as[i]);  % conjunction of encoding variables
      } in forall(j in index_set(result))(
        clause([result[j]],selectors)
      )
    )
    elseif SAT_array_int_element_method == GROUPWISE then
      let {
        array[int] of set of int: groups = group(as); % groups[u] is a set of indices that all point to the same element (as[groups[u][1]]=as[groups[u][2]]=...)
        array[int] of int: U = [ as[min(group)] | group in groups ]; % the unique values in A in increasing order of appearance
        constraint forall(u in index_set(U) diff {max(index_set(U))})(assert(U[u] < U[u+1], "Expected \(U[u]) < \(U[u+1])"));

        bool: order_enc_views = encs == [SAT_ORDER,SAT_ORDER];

        array[int] of int: order_enc_views_monotone = if order_enc_views then find_order_encoding_views(as, groups) endif;
        array[int] of int: order_enc_views_antitone = if order_enc_views then find_order_encoding_views(as, group(reverse(as))) endif;
      } in
      forall(u in index_set(U))(
        let {  % Note, the groups are sorted by the element they refer to: as[groups[u][1]] < as[groups[u+1][1]]

          int: a = U[u]; % the u-th smallest unique element
          set of int: group = groups[u]; % the indices that point to a
          array[int] of var bool: c_eq_a = int_eq_var_par_func(c, a); % conjunction of vars that make c=a
        } in 
          if encs[1] == SAT_UNARY then
              if card(group) == 1 /\ encs[2] == SAT_UNARY then
                let {
                  array[int] of var bool: b_enc = unary_encode(b);
                  array[int] of var bool: c_enc = unary_encode(c);
                } in c_enc[a] == b_enc[min(group)]
              else
                let {
                  array[int] of var bool: b_in_group = array1d(set_in_func(b, group));
                } in
                clause(b_in_group, c_eq_a)
                  ::expression_name_dbg("\(b) not in \(group) -> c!=\(a)")
                /\
                forall(b_i in b_in_group)(clause(c_eq_a, [ b_i ]))
                  ::expression_name_dbg("\(b) in \(group) -> c==\(a)")
              endif
          elseif encs[1] == SAT_ORDER then
            let {
              array[int] of var bool: b_enc = order_encode(b);
              array[int] of var bool: c_enc = order_encode(c);
            } in % TODO this might be incorrect; even if view, you might want to add some clauses anyways! But for total views it will work
            if order_enc_views /\ (u <= order_enc_views_monotone[1] \/ u > length(U) - order_enc_views_monotone[2] ) then
              c_enc[a] == order_encoding_element_partial(b_enc, min(group))
            elseif order_enc_views /\ (u <= order_enc_views_antitone[1] \/ u > length(U) - order_enc_views_antitone[2] ) then
              c_enc[a] != b_enc[min(group)+1]::maybe_partial
            else
              let { % Constrain using the holes between ranges
                array[int,int] of var bool: b_in_group = set_in_func(b, group);
                array[int,int] of var bool: b_out_group = set_in_func(b, index_set(as) diff group);
              } in
              % TODO skip for views (but when and which?)
                forall(k in index_set_1of2(b_in_group))(
                  clause(c_eq_a,b_in_group[k,..])
                    ::expression_name_dbg("element: \(b) in \(group)[\(k)] -> \(c)=\(a)")
                ) /\
                forall(k in index_set_1of2(b_out_group))(
                  clause([],b_out_group[k,..]++c_eq_a)
                    ::expression_name_dbg("element: \(b) not in \(group) -> \(c)!=\(a)")
                )
            endif
          elseif encs[1] == SAT_BINARY then
            let { constraint abort("binary encoding for index not supported"); } in false
          else
            let { constraint abort("XXX"); } in false
          endif
      )
    elseif SAT_array_int_element_method == COLUMNWISE then
      if encs[2] == SAT_UNARY then
        let {
          array[int] of var bool: c_enc = unary_encode(c);
          array[int,int] of bool: as_enc = array2d(index_set(as), index_set(c_enc), [ j = as[i] | i in index_set(as), j in index_set(c_enc) ]);
        } in forall(j in index_set_2of2(as_enc))(array_bool_element(b, as_enc[..,j], c_enc[j]))
      elseif encs[2] == SAT_ORDER then
        let {
          array[int] of var bool: c_enc = order_encode(c);
          array[int,int] of bool: as_enc = array2d(index_set(as), index_set(c_enc), [ as[i] >= j | i in index_set(as), j in index_set(c_enc) ]);
        } in forall(j in index_set_2of2(as_enc))(array_bool_element(b, as_enc[..,j], c_enc[j]))
      elseif encs[2] == SAT_BINARY then
        let {
          array[int] of var bool: c_enc = binary_encode(c);
          array[int,int] of bool: as_enc = array2d(index_set(as), index_set(c_enc), [ j | i in index_set(as), j in binary(as[i],length(c_enc),true) ]);
        } in forall(j in index_set_2of2(as_enc))(array_bool_element(b, as_enc[..,j], c_enc[j]))
      else
        let { constraint abort("XXX"); } in false
      endif
    % elseif SAT_element_compact then
    %   forall(group in groups)(
    %     let {
    %     % TODO check this still gives views
    %       array[int,int] of var bool: antecedents = set_in_func(b, group);
    %       array[int] of var bool: consequents = int_eq_var_par_func(c, as[group[1]]);
    %       constraint trace("consequents \(consequents)\n");
    %     } in exists_forall_implies_forall(antecedents, consequents)
    %   )
    % elseif has_sat_ann(c, unary_encoded) then
    %   let {
    %     array[int] of var bool: c_enc = unary_encode(c);
    %     bool: index_is_unary_encoded = has_sat_ann(b, unary_encoded);
    %   } in
    %   forall(group in groups)(
    %     if index_is_unary_encoded /\ card(group) == 1 then
    %       % (b in group) <-> c_enc[as[group[1]]]
    %       (b == group[1]) <-> c_enc[as[group[1]]]
    %     else
    %       % ((b in group) -> c_enc[as[group[1]]])
    %       exists_forall_implies(set_in_func(b,group),c_enc[as[group[1]]])
    %         ::expression_name_dbg("array_int_element: \(b) in \(group) <-> c=\(as[group[1]])")
    %     endif
    %     )
    % elseif has_sat_ann(c, order_encoded) then
    %   let {
    %     array[int] of var bool: c_enc = order_encode(c);
    %   } in
    %   forall(u in array2set(as))(
    %     % ((b in { i | g in groups where as[g[1]]>=u, i in g }) -> c_enc[u])
    %     let {
    %       set of int: bs = { i | g in groups where as[g[1]]>=u, i in g };
    %       set of int: bs_not = { i | g in groups where as[g[1]]<u+1, i in g };
    %       % set of int: bs = { i | g in groups where as[g[1]]>=u, i in g };
    %       % set of int: bs_not = { i | g in groups where as[g[1]]<u+1, i in g };
    %       constraint trace("bs \(bs)\n");
    %       array[int,int] of var bool: antecedents = set_in_func(b, bs);
    %       constraint trace("bs_not \(bs_not)\n");
    %       array[int,int] of var bool: antecedents_not = set_in_func(b, bs_not);
    %     } in
    %     ( exists_forall_implies(antecedents, c_enc[u]) )
    %     % (b in bs -> c_enc[u])
    %             ::expression_name_dbg("array_int_element: \(b) in \(bs) -> c>=\(u)")
    %     /\ ( exists_forall_implies(antecedents_not, not c_enc[u+1]::maybe_partial) )
    %             ::expression_name_dbg("array_int_element: \(b) in \(bs) -> c<\(u)")
    %   )
    else
      let { constraint abort("XXX"); } in false
    endif;

% predicate array_var_int_element(int: b, array[int] of var int: as, int: c) =
%   as[b]==c;

predicate array_var_int_element(int: b, array[int] of var int: as, var int: c) =
  let {
    constraint assert(b in index_set(as), "fixed index should be in array's index_set for the fixed index array_var_int_element redefinition");
  } in as[b]==c;

predicate array_var_int_element(var int: b, array[int] of var int: as, var int: c) =
  % TODO check for fixed vars and call array_int_element on those?
  let {
    % constraint assert(dom(b) subset index_set(as), "The index variable's domain \(dom(b)) is not a subset of index set of the array \(index_set(as)).");
    constraint b in index_set(as);
    set of int: as_dom = dom_array(as);
    array[int] of bool: as_encs = get_sat_encodings(as, SAT_ARRAY_VAR_INT_ELEMENT_ELEMENTS_ENCODING_PREFS);
    array[int] of bool: b_encs = get_sat_encodings(b, SAT_ARRAY_VAR_INT_ELEMENT_INDEX_ENCODING_PREFS);
    array[int] of bool: c_encs = get_sat_encodings(c, SAT_ARRAY_VAR_INT_ELEMENT_RESULT_ENCODING_PREFS);
    % TODO fix, or create better 'encoding inheritance' method
    constraint if c_encs != [false,false,true] then
      c in as_dom
    else
      c >= min(as_dom) /\ c <= max(as_dom)
    endif; % domain of c is implied by b, so for binary encoding we can skip eliminating the gaps
  } in
    forall(i in dom(b))(
      let {  % /\ selectors -> (element_i_var_1 <-> result_var_1 /\ element_i_var_2 <-> result_2 /\ ...)
        array[int] of var bool: selectors = int_eq_var_par_func(b, i); % conjunction of encoding variables
        array[int,1..2] of var bool: result = int_eq_var_var_func(as[i], c);  % conjunction of equivalence of encoding variables
        % TODO fixed vars in result/selectors create over-encodings (at least for binary)
      } in forall(j in index_set_1of2(result))(
        clause([result[j,2]],selectors++[result[j,1]])
          ::expression_name_dbg("array_var_int_element selectors -> (result_\(j)_1 -> result_\(j)_2")
        /\
        clause([result[j,1]],selectors++[result[j,2]])
          ::expression_name_dbg("array_var_int_element selectors -> (result_\(j)_1 <- result_\(j)_2")
    )
  );


predicate array_bool_element(var int: b, array[int] of bool: as, var bool: c) =
  let {
    constraint assert(dom(b) subset index_set(as), "The index variable's domain \(dom(b)) is not a subset of index set \(index_set(as)).");

    SAT_encoding_modes: enc = decide_encoding(b, SAT_UNARY);


    set of int: group = { i | i in index_set(as) where as[i] }; % the group of indices where c is true
    array[int,int] of var bool: b_in_group = set_in_func(b, group);
    array[int,int] of var bool: b_out_group = set_in_func(b, index_set(as) diff group);
  } in 
    if enc == SAT_UNARY then
      exists(array1d(b_in_group)++[not c]) /\ exists(array1d(b_out_group)++[c])
    elseif enc == SAT_ORDER then
      exists_forall_implies(b_in_group, c) /\ exists_forall_implies(b_out_group, not c)
    elseif enc == SAT_BINARY then
      let { constraint abort("binary encoding for index not supported"); } in false
    else
      let { constraint abort("XXX"); } in false
    endif;

predicate array_var_bool_element(var int: b, array[int] of var bool: as, var bool: c) =
  forall(i in dom(b))(
    (b == i) -> (c == as[i])
  );
