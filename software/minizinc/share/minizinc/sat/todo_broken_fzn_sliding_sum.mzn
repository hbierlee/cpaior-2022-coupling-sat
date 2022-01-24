/** @group globals
  Requires that in each subsequence \a vs[\p i], ..., \a vs[\p i + \a seq - 1] the sum of the
  values belongs to the interval [\a low, \a up].
*/

% TODO breaks tests/spec/unit/globals/sliding_sum/globals_sliding_sum.mzn
predicate fzn_sliding_sum(int: low, int: up, int: seq, array[int] of var int: vs) =
    let { int: lx = min(index_set(vs)),
          int: ux = max(index_set(vs)),
        } in
        forall (i in lx .. ux - seq + 1) ( 
            let { 
                    var int: sum_of_l = sum(j in i..i + seq - 1) (vs[j]) 
            } in
                low <= sum_of_l /\ sum_of_l <= up
        );
