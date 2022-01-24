% sat/fzn_circuit
include "alldifferent.mzn";

% predicate fzn_circuit(array[int] of var int: x) =
%     let {
%     constraint annotate_sat_encoding(x, SAT_circuit_successor_var_encoding);
%     set of int: S = index_set(x);
%     int: l = min(S);
%     int: n = card(S);
%     array[S] of var 1..n: y;
%     % constraint trace("circuit\n");
%     % constraint trace("x \(index_set(x)) \(x)\n");
%     % constraint trace("y \(index_set(y)) \(y)\n");
%     constraint annotate_sat_encoding(y, SAT_circuit_order_var_encoding);
%   } in
%        forall(i in S)(x[i] != i)
%     /\ y[l] = n
%     /\ y[x[l]] = 1
%     /\ alldifferent(x)
%     /\ alldifferent(y)
%     /\ let {
%          array[int] of var int: z = array1d(S, [
%           let {
%             var int: z_i = y[i]-1;
%             constraint annotate_sat_encoding(z_i, SAT_circuit_order_var_encoding);
%           } in z_i
%          | i in S]);
%        } in
%          forall(i in S diff {l})(
%             y[i] = z[x[i]]
%           );

predicate fzn_circuit(array[int] of var int: x) =
    let {
    constraint annotate_sat_encoding(x, SAT_circuit_successor_var_encoding);
    set of int: S = index_set(x);
    int: l = min(S);
    int: n = card(S);
    array[S] of var 1..n: y;
    constraint annotate_sat_encoding(y, SAT_circuit_order_var_encoding);
  } in
       forall(i in S)(x[i] != i)
    /\ y[l] = n
    % /\ y[x[l]] = 1
    /\ array_var_int_element(x[l], y, 1)
    /\ alldifferent(x)
          ::expression_name_dbg("fzn_circuit: alldifferent(x)")
    /\ if has_sat_ann(y, unary_encoded) then alldifferent(y) endif
          ::expression_name_dbg("fzn_circuit: alldifferent(y)")
    /\ forall(i in S diff {l})(array_var_int_element(x[i], y, affine(y[i],1,1)))  % y[x[i]] = y[i]-1
    % /\ forall(i in S diff {l})((y[x[i]] = y[i]-1)) % y[x[i]] = y[i]-1
