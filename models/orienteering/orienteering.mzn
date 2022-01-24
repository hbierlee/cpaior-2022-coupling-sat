% Orienteering
    % Note: we sometimes use annotate_sat_encoding instead of direct annotations (::binary_encoded), so that we can easily change the configuration via data parameters in experiments
include "../sat-declarations.mzn";
include "subcircuit.mzn";
opt bool: f_mzn_sat;
bool: mzn_sat = f_mzn_sat default true;


% number of nodes
int: n;
% start
int: start;
% finish, before returning to start
int: finish;
% max distance allowed
int: max_distance;
% distance from node i to j
array[1..n,1..n] of int: distance;
% value of visiting node i
array[1..n] of int: value;

% successor variables
array[1..n] of var 1..n: x;
ann: distance_encoding = 
  if SAT_array_int_element_result_encoding == SAT_UNARY then
    unary_encoded
  elseif SAT_array_int_element_result_encoding == SAT_ORDER then
    order_encoded
  else
    binary_encoded
  endif;

constraint if SAT_allow_redundant_encodings then
  annotate_sat_encoding(x, SAT_UNARY) /\ annotate_sat_encoding(x, SAT_ORDER)
endif;  % SAT_UNARY should be read as SAT_DIRECT

% The solution must form a path from start to finish
constraint x[finish] = start;

% x forms a subcircuit
constraint subcircuit(x);

% The subcircuit is limited in total distance
constraint sum(i in 1..n)(distance[i,x[i]]::distance_encoding) <= max_distance;
% We optimize the sum of the values of the nodes that we do visit
solve maximize sum(i in 1..n)((x[i]!=i)*value[i]);
