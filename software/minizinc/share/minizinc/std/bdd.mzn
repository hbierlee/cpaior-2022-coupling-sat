include "fzn_bdd.mzn";

opt bool: fDOTTrace=false;
bool: mzn__dot_trace_on =
    if absent( fDOTTrace ) then false else deopt( fDOTTrace ) endif;
test dot_trace(string: msg) ::promise_total =
  if mzn__dot_trace_on then trace("%%%dot " ++ msg) else true endif;

% include "fzn_bdd_reif.mzn";

/** @group globals.extensional
  Requires that \a x defines a path from root node (with label 1) to a 1-terminal node through the BDD defined by the (binary) tree:
   @param low_children: denotes for each node its low child, or 0 for 0-terminal, or 1 for 1-terminal
   @param high_children: denotes for each node its high child, or 0 for 0-terminal, or 1 for 1-terminal
*/
predicate bdd(array[int] of var bool: x, array[int] of int: low_children, array[int] of int: high_children, var bool: zero_terminal, var bool: one_terminal) =
  let {
    % Print dot format
    constraint forall(i in index_set(x))(dot_trace("node\(i)[label=\"\(i): \(x[i])\"];\n"));
    constraint forall(i in index_set(x) where low_children[i] <= 1)(dot_trace("term\(i)_\(low_children[i])[label=\"\(if low_children[i] == 0 then zero_terminal else one_terminal endif)\",shape=plaintext];\n"));
    constraint forall(i in index_set(x) where high_children[i] <= 1)(dot_trace("term\(i)_\(high_children[i])[label=\"\(if high_children[i] == 0 then zero_terminal else one_terminal endif)\",shape=plaintext];\n"));
    constraint forall(i in index_set(x))(dot_trace(dot_edge(i, low_children[i], 0) ++ "\n"));
    constraint forall(i in index_set(x))(dot_trace(dot_edge(i, high_children[i], 1) ++ "\n"));
    constraint dot_trace("}\n");
  } in
  let {
    int: N = length(x);
    set of int: NODE = 1..N;
  } in 
    assert(index_set(x) = NODE, "bdd: number of variables does not match bdd size \(N)\n") /\
    assert(index_set(low_children) = NODE, "bdd: low children array does not match bdd size \(N)\n") /\
    assert(index_set(high_children) = NODE, "bdd: high children array does not match bdd size \(N)\n") /\
    forall(i in NODE)(
      assert(low_children[i] in 0..1 \/ low_children[i] <= N, "bdd: low child of node \(i) = \(low_children[i]) is not the 0-terminal or 1-terminal\n") /\
      assert(high_children[i] in 0..1 \/ high_children[i] <= N, "bdd: high child of node \(i) = \(high_children[i]) is not the 0-terminal or 1-terminal\n")
    ) /\ fzn_bdd(x, low_children, high_children, zero_terminal, one_terminal)::constraint_name("bdd");

function string: dot_edge(int: from , int: to, int: label) = 
  let {
    string: from_node = "node\(from)";
    string: to_node =
      if to > 1 then
        "node\(to)"
        else
        "term\(from)_\(to)"
        % else "\(to)"
      endif;
    string: style = if label == 0 then "dashed" else "solid" endif;
    string: tailport = if label == 0 then "sw" else "se" endif;
    } in "\(from_node)->\(to_node)[label=\(label),style=\(style),tailport=\(tailport)];";
