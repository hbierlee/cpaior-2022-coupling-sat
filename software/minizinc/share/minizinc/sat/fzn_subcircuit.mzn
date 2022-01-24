include "arg_max.mzn";
include "alldifferent.mzn";
include "alldifferent_except_0.mzn";


%predicate fzn_subcircuit(array[int] of var int: x) =
%    let {
%        constraint annotate_sat_encoding(x, SAT_circuit_successor_var_encoding);
%        set of int: S = index_set(x);
%        int: n = card(S);
%        array[S] of var 0..n: y;
%        int: root = min(S);
%        constraint annotate_sat_encoding(y, SAT_circuit_order_var_encoding);
%            % binary, order
%    } in
%           y[x[root]] = 1
%        /\ alldifferent(x)
%        /\ if has_sat_ann(y, unary_encoded) then alldifferent_except_0(y) endif
%        % If the subcircuit is non-empty then y numbers the subcircuit.
%        %
%          % We start from the _successor_ of the root,
%          % for reasons which will become clear.
%          % The y of a successor is greater than its predecessor.
%        /\ let {
%             array[int] of var int: z = array1d(S, [
%               let {
%                 var int: z_i = y[i]-1;
%                 constraint annotate_sat_encoding(z_i, SAT_circuit_order_var_encoding);
%               } in z_i | i in S ]);
%          } in forall(i in S diff {root})(
%            y[i] = array1d(S, [ if i == j then 0 else z[j] endif | j in S ])[x[i]]
%          );

predicate fzn_subcircuit(array[int] of var int: x) =
    let {
        constraint annotate_sat_encoding(x, SAT_circuit_successor_var_encoding);
        set of int: S = index_set(x);
        int: n = card(S);
        array[S] of var 0..n: y;
        int: root = min(S);
        constraint annotate_sat_encoding(y, SAT_circuit_order_var_encoding);
    } in
           array_var_int_element(x[root], y, 1)
        /\ alldifferent(x)
        /\ if has_sat_ann(y, unary_encoded) then alldifferent_except_0(y) endif % this constraint is redundant (and we only support alldifferent_direct), so it's only added if a direct encoding is available
        % If the subcircuit is non-empty then y numbers the subcircuit.
        %
          % We start from the _successor_ of the root,
          % for reasons which will become clear.
          % The y of a successor is greater than its predecessor.
        /\ forall(i in S diff {root})(
          let {
            array[int] of var int: Y = array1d(S, [ if i == j then 0 else affine(y[j],1,-1) endif | j in S ]);
          } in
          array_var_int_element(
            x[i],
            Y,
            y[i]
          )
        );
