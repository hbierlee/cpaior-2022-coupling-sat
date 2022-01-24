predicate fzn_lex_lesseq_bool(array[int] of var bool: x,
                              array[int] of var bool: y) =
    let {
    constraint trace("fzn_lex_lesseq_bool SAT->STD\n");
    int: lx = min(index_set(x)),
          int: ux = max(index_set(x)),
          int: ly = min(index_set(y)),
          int: uy = max(index_set(y)),
          int: size = min(ux - lx, uy - ly),

          % TODO although maybe there's a prettier way to create a mixed var/par array..?
          array[1..size+1] of var bool: b_tmp,
          array[int] of var bool: b = array1d(0..size+1, [true] ++ b_tmp); 
    } in
    forall(i in 0..size) (
        b[i] =
          let {
            var bool: p = if is_fixed(x[lx + i]) then
              if fix(x[lx+i]) then % 1 <= Y -> Y
                y[ly+i]
              else % 0 <= Y -> 1
                true
              endif
            else
              x[lx+i] <= y[ly + i]
            endif;

            var bool: q = if is_fixed(x[lx + i]) then
              if fix(x[lx+i]) then % 1 < Y -> 0
                false
              else % 0 < Y -> Y
                y[ly+i]
              endif
            else
              x[lx+i] <  y[ly + i]
            endif;

          } in ( p /\ (q \/ b[i+1]) )
    )
    /\
    b[size + 1] = (ux - lx <= uy - ly);
