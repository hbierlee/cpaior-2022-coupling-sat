% Knight's Tour
    % Supports rectangular boards, and boards with holes; latter feature not used for our experiments
% Original knights.mzn by Ralph Becket
    % Note: we sometimes use annotate_sat_encoding instead of direct annotations (::binary_encoded), so that we can easily change the configuration via data parameters in experiments

include "../sat-declarations.mzn";
include "circuit.mzn";

opt bool: f_mzn_sat;
bool: mzn_sat = f_mzn_sat default true;


    % n is the length of side of the chessboard.
    %
int: n;
int: m;

constraint assert(n >= 3 /\ m >= 3, "Minimum size requirements are probably 3x3");

    % The ith square (r, c) on the path is given by p[i] = (r - 1) * n + c.
    %
int: nm = n * m;
set of int: sq = 1..nm;

set of int: row = 1..n;
set of int: col = 1..m;

set of 2..nm: holes;
set of 1..nm: holes_including_start = holes union {1};

array [sq] of set of sq: neighbours =
    [   { m * (R - 1) + C
        |
            i in 1..8,
            R in {R0 + [-1, -2, -2, -1,  1,  2,  2,  1][i]},
            C in {C0 + [-2, -1,  1,  2,  2,  1, -1, -2][i]}
            where R in row /\ C in col
        }
    |   R0 in row, C0 in col
    ];

% n-k-1 successors (first and last fixed), followed by k holes, followed by 1 to complete loop
% 6, 7, 2, 9, 5, 3, 8, 1
array [1..nm] of var sq: p::add_to_output =
  [ m+3 ] ++ % first move (from square 1)
  [ if i == 2*m+2 then % last square before holes
      max(holes_including_start) % start going down the holes
    elseif i in holes_including_start then % hole
      % holes form fixed path from hole with highest index down to hole with lowest index (=starting position)
      max({ h | h in holes_including_start where h < i })
    else
      let {
        var neighbours[i] diff holes_including_start: p_i;
        constraint if SAT_allow_redundant_encodings then
          annotate_sat_encoding(p_i, SAT_UNARY) /\ annotate_sat_encoding(p_i, SAT_ORDER)
        endif;
      } in p_i
    endif
      | i in 2..nm
  ];

constraint circuit(p);

solve
    :: int_search(
        p,
        input_order,
        indomain_min,
        complete
    )
    satisfy;
