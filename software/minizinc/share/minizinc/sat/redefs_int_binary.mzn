predicate int_lin_of_2_binary(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  if comp == INT_EQ /\ c in {1,-1} /\ as == [1,-1] then
    let { % y = x - 1
      var int: y = bs[if c == 1 then 2 else 1 endif];
      var int: x = bs[if c == 1 then 1 else 2 endif];
      array[int] of var bool: y_enc = binary_encode(y);
      array[int] of var bool: x_enc = binary_encode(x);
      int: u = min(max(index_set(x_enc)), max(index_set(y_enc)));
      array[1..u-1] of var bool: z;
    } in
         (y_enc[1] != x_enc[1])
      /\ forall(i in index_set(z))(z[i] <-> (x_enc[i] \/ z[i-1]::maybe_partial))
      /\ forall(i in 2..u)(x_enc[i] <-> (y_enc[i] <-> z[i-1]))
      /\ forall(i in 2..u)(x_enc[i] <-> (y_enc[i] <-> z[i-1]))
      /\ forall(i in u+1..max(index_set(x_enc)))(not x_enc[i])
      /\ forall(i in u+1..max(index_set(y_enc)))(not y_enc[i])
  elseif comp == INT_NE /\ c == 0 /\ (as == [1,-1] \/ as == [-1,1]) then
    int_ne_binary(bs[1],bs[2])
  else
    pbify_int_lin(as, bs, c, comp) % TODO at least if as = [1,-1] we should be able to do better, or (more tricky) with powers of 2
  endif;
  % TODO in general, compare with adder

predicate int_lin_of_3_binary(array[int] of int: as, array[int] of var int: bs, int: c, Comparator: comp) =
  pbify_int_lin(as, bs, c, comp);

predicate int_eq_binary(var int: a, int: b) =
  int_eq_binary(binary_encode(a), b);

predicate int_eq_binary(array[int] of var bool: a_enc, int: b) =
  if binary_lb(a_enc) > b then
    false
  elseif binary_ub(a_enc) < b then
    false
  else
    a_enc == binary(b, length(a_enc), true)
  endif;

predicate int_eq_binary(var int: a, var int: b) =
  int_eq_binary(binary_encode(a), binary_encode(b));

function array[int,int] of var bool: int_eq_var_var_binary_func(var int: a, var int: b) =
  int_eq_var_var_binary_func(binary_encode(a), binary_encode(b));

function array[int] of var bool: int_eq_var_par_binary_func(var int: a, int: b) =
  int_eq_var_par_binary_func(binary_encode(a), b);

function array[int] of var bool: int_eq_var_par_binary_func(array[int] of var bool: a_enc, int: b) =
  let {
    array[int] of bool: binary = binary(b, length(a_enc), true);
  } in [ if binary[i] then a_enc[i] else not a_enc[i] endif | i in index_set(a_enc) ]; % TODO BUG?
% || minizinc: /home/hbierlee/Projects/libminizinc/lib/ast.cpp:322: int MiniZinc::ArrayLit::min(unsigned int) const: Assertion `i == 0' failed.
  % } in [ a_enc[i] == false | i in 1..3 ];

function array[int, int] of var bool: int_eq_var_var_binary_func(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
     array2d(index_set(a_enc) union index_set(b_enc), 1..2,
     [ if j==1 then a_enc[i] else b_enc[i] endif | i in 1..min(length(a_enc), length(b_enc)), j in 1..2 ]
  ++ [ if j==1 then a_enc[i-1] else a_enc[i] endif | i in length(b_enc)+1..length(a_enc), j in 1..2]
  ++ [ if j==1 then b_enc[i-1] else b_enc[i] endif | i in length(a_enc)+1..length(b_enc), j in 1..2 ]);
     % [ a_enc[i]   == b_enc[i] | i in 1..min(length(a_enc), length(b_enc)) ]
  % ++ [ a_enc[i-1] == a_enc[i] | i in length(b_enc)+1..length(a_enc)]
  % ++ [ b_enc[i-1] == b_enc[i] | i in length(a_enc)+1..length(b_enc)];

predicate int_eq_binary(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
     forall(i in 1..min(length(a_enc), length(b_enc)))(a_enc[i] == b_enc[i])
  /\ forall(i in length(b_enc)+1..length(a_enc))(a_enc[i-1] == a_enc[i])
  /\ forall(i in length(a_enc)+1..length(b_enc))(b_enc[i-1] == b_enc[i]);

predicate int_ge_binary(array[int] of var bool: a_enc, int: b) =
  % Bit duplicated from int_le par/var, but: a>=b <-> -a<=-b <-> -a-1<=-b-1 <-> a'<=-b-1
  int_le_binary(take_two_complement(a_enc), -b-1);

predicate int_le_binary(array[int] of var bool: a_enc, int: b) =
  let {
    int: a_lb = binary_lb(a_enc);
  } in
  if a_lb > b then
    false
  elseif binary_ub(a_enc) <= b then
    true
  else
    lex_lesseq_bool(
      twos_complement_to_orderable_binary(a_enc),
      reverse(binary(b - a_lb, length(a_enc)))
    )
  endif;

predicate int_le_binary(var int: a, int: b) =
  int_le_binary(binary_encode(a), b)
    ::expression_name_dbg("int_le_binary \(a)<=\(b)")
  ;

predicate int_le_binary(int: a, var int: b) =
  int_ge_binary(binary_encode(b),a) % a<=b <-> b>=a
    ::expression_name_dbg("int_le_binary \(a)<=\(b)")
  ;


include "lex_lesseq.mzn";
predicate int_le_binary(var int: a, var int: b) =
    let {
      array[int] of var bool: a_enc = binary_encode(a);
      array[int] of var bool: b_enc = binary_encode(b);
    } in
  lex_lesseq(
    twos_complement_to_orderable_binary(two_complement_extend(a_enc,length(b_enc))),
    twos_complement_to_orderable_binary(two_complement_extend(b_enc,length(a_enc)))
  )
    ::expression_name_dbg("int_le_binary \(a)<=\(b)")
  ;


predicate int_ne_binary(array[int] of var bool: a_enc, int: b) =
  let {
    array[int] of bool: b_enc = binary(b, length(a_enc), true);
  } in
    clause(
      [a_enc[i] | i in index_set(b_enc) where not b_enc[i]],
      [a_enc[i] | i in index_set(b_enc) where b_enc[i]],
    );

predicate int_ne_binary(var int: a, int: b) =
  int_ne_binary(binary_encode(a), b);

predicate int_ne_binary(var int: a, var int: b) =
  let {
    array[int] of var bool: a_enc = binary_encode(a);
    array[int] of var bool: b_enc = binary_encode(b);
    array[int] of var bool: a_enc_ext = two_complement_extend(a_enc,length(b_enc));
    array[int] of var bool: b_enc_ext = two_complement_extend(b_enc,length(a_enc));
    constraint assert(length(a_enc_ext) == length(b_enc_ext), "length(a_enc) == length(b_enc)");
    int: n = length(a_enc_ext);
    array[1..n] of var bool: r;
  } in
    clause(r,[]) /\
    forall(k in 1..n)(
        let {
          var bool: a_k = a_enc_ext[k];
          var bool: b_k = b_enc_ext[k];
          var bool: r_k = r[k];
        } in
           clause([a_k,b_k],[r_k])
        /\ clause([],[a_k,b_k,r_k])
              ::expression_name_dbg("int_ne_binary(\(r) -> (\(a) xor \(b)); bit \(k)")
    );

predicate int_min_binary(var int: a, int: b, var int: c) =
  if b == 0 then
    if use_binary_views then
      let {
        constraint annotate_sat_encoding(c, SAT_BINARY);
      } in
      partial_view(c, a)
    else
      let {
        array[int] of var bool: a_enc_tmp = binary_encode(a);
        array[int] of var bool: c_enc_tmp = binary_encode(c);
        array[int] of var bool: a_enc = two_complement_extend(a_enc_tmp, length(c_enc_tmp));
        array[int] of var bool: c_enc = two_complement_extend(c_enc_tmp, length(a_enc_tmp));
        int: sign = sign(index_set(c_enc));
        set of int: bits = bits(index_set(c_enc));
      } in forall(i in bits)(
             clause([a_enc[sign]],[c_enc[i]])
          /\ clause([c_enc[i]],[a_enc[i],a_enc[sign]])
          /\ clause([a_enc[i]],[c_enc[i],a_enc[sign]])
        )
    endif
  else
    array_int_minimum(c, [a,b])
  endif;
predicate int_max_binary(var int: a, int: b, var int: c) =
  if b == 0 then
    if use_binary_views then
      let {
        constraint annotate_sat_encoding(c, SAT_BINARY);
      } in
      partial_view(c, a)
    else
      let {
        array[int] of var bool: a_enc_tmp = binary_encode(a);
        array[int] of var bool: c_enc_tmp = binary_encode(c);
        array[int] of var bool: a_enc = two_complement_extend(a_enc_tmp, length(c_enc_tmp));
        array[int] of var bool: c_enc = two_complement_extend(c_enc_tmp, length(a_enc_tmp));
        int: sign = sign(index_set(c_enc));
        set of int: bits = bits(index_set(c_enc));
        constraint assert(is_fixed(c_enc[sign]) /\ not fix(c_enc[sign]), "sign bit should be taken care off");
      } in forall(i in bits)(
             clause([],[a_enc[sign],c_enc[i]])
          /\ clause([c_enc[i],a_enc[sign]],[a_enc[i]])
          /\ clause([a_enc[i],a_enc[sign]],[c_enc[i]])
        )
    endif
  else
    array_int_maximum(c, [a,b])
    % int_max_binary(a, b, c) % inf recursion for some reason?
  endif;

predicate int_max_binary(var int: a, var int: b, var int: c) =
  array_int_maximum(c, [a,b]);

predicate int_min_binary(var int: a, var int: b, var int: c) =
  array_int_minimum(c, [a,b]);

predicate int_abs_binary(var int: a, var int: b) =
  let {
    % b = |a|
    array[int] of var bool: a_enc = binary_encode(a);
    array[int] of var bool: b_enc = binary_encode(b);
  } in not b_enc[length(b_enc)]
    /\ (int_eq_binary(a_enc, b_enc) \/ two_complement(a_enc, b_enc));

function array[int] of var bool: two_complement_extend(array[int] of var bool: enc, int: k) =
  enc ++ [ enc[length(enc)] | i in length(enc)+1..k];

% two complement of a = -a = flip bits and add one to a_enc
predicate two_complement(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
  int_plus_binary([ not b | b in a_enc ], [ false | i in a_enc ], true, b_enc);

predicate int_plus_binary(var int: a, var int: b, var int: c) =
  int_plus_binary(
    binary_encode(a),
    binary_encode(b),
    binary_encode(c)
  );

predicate int_plus_binary(var int: a, int: b, var int: c) =
  let {
    array[int] of var bool: a_enc = binary_encode(a);
  } in
    int_plus_binary(
      a_enc,
      binary(b, length(a_enc), true),
      binary_encode(c)
    );

predicate int_plus_binary(array[int] of var bool: x, array[int] of var bool: y, array[int] of var bool: z) =
  if SAT_int_plus_pb then
    bool_lin_eq(
      binary_encode_int_lin_exp_coefficients(x) ++ binary_encode_int_lin_exp_coefficients(y) ++ [-c | c in binary_encode_int_lin_exp_coefficients(z)],
      x ++ y ++ z,
      0,
    )
  else
    int_plus_binary(x, y, false, z)
  endif;

predicate int_plus_binary(array[int] of var bool: x_in, array[int] of var bool: y_in, var bool: ci, array[int] of var bool: s_in) =
  if SAT_int_plus_pb then
    bool_lin_eq(
      binary_encode_int_lin_exp_coefficients(x_in) ++ binary_encode_int_lin_exp_coefficients(y_in) ++ [-c | c in binary_encode_int_lin_exp_coefficients(s_in)] ++ [ 1 ],
      x_in ++ y_in ++ s_in ++ [ ci ],
      0,
    )
  else
    let {
      array[int] of var bool: x = two_complement_extend(x_in, length(y_in));
      array[int] of var bool: y = two_complement_extend(y_in, length(x_in));
      array[int] of var bool: s = two_complement_extend(s_in, length(x));
      % TODO can x/y be shortened based on domain of s?
      int: l = length(x);
      int: n = length(s);
    } in
      % assert(l == length(y), "length of binary_add input args must be same") /\
      % assert(n == l \/ n == l+1, "length of binary_add output must be equal or one more than inputs") /\
    let {
      array[1..l] of var bool: c;
    } in
      full_adder(x[1], y[1], ci, s[1], c[1]) /\
      forall(i in 2..l)(
        full_adder(x[i], y[i], c[i-1], s[i], c[i])
      ) /\
        if n > l then
          s[n] == c[l]
        % TODO this is here for overflow detection I think but this prevents _times from working where the encoding can just roll over
        % else
        %   not c[l]
        endif
  endif;


predicate full_adder(var bool: x, var bool: y, var bool: ci,
                     var bool: s, var bool: co) =
          let { var bool: xy = x xor y } in
          s = (xy xor ci) /\ co = ((x /\ y) \/ (ci /\ xy));

% predicate full_multiplier(var bool: x, var bool: y, var bool: ci,
%                      var bool: m, var bool: co) =
%           let { var bool: xy = x /\ y } in
%           s = (xy xor ci) /\ co = ((x /\ y) \/ (ci /\ xy));


% TODO non-positive context error I still don't fully understand, as in other seemingly the same instances it is fine
% function array[int] of var bool: int_plus_binary(array[int] of var bool: a_enc, array[int] of var bool: b_enc) =
%   let {
%     array[int] of var bool: c_enc;
%     constraint int_plus_binary(a_enc, b_enc, c_enc);
%   } in c_enc;


% https://en.wikipedia.org/wiki/Two%27s_complement#Multiplication
% 0 0110  (6)  (multiplicand with extended sign bit) (size: 5)
% × 1011 (−5)  (multiplier) (size: 4)
% =|====|====
% 0|0110|0000  (first partial product (next bit is 1)) (size: 5)
% 0|0011|0000  (shift right, preserving extended sign bit) (size: 6)
% 0|0110|0000  (second partial product (next bit is 1)) (size: 5)
% 0|1001|0000  (partial sum)
% 0|0100|1000  (shift right, preserving extended sign bit)
% 0|0000|0000  (third partial product (next bit is 0))
% 0|0100|1000  (partial_sum: 0 so no change)
% 0|0010|0100  (shift right, preserving extended sign bit)
% 0|0110|0000  (fourth partial product (next bit is 1))
% 1|1010|0000  (negate (two complement) last partial product)
% 1|1100|0100  (partial_sum: subtract (add negated) last partial product since it's from sign bit)
% 1|1110|0010  (shift right, preserving extended sign bit)
%  |1110|0010  (discard extended sign bit, giving the final answer, −30)
predicate int_times_binary(var int: a, var int: b, var int: c) =
  int_times_binary(binary_encode(a), binary_encode(b), binary_encode(c));

% function array[int] of var bool: int_times_binary_partial(array[int] of var bool: a_enc, bool: next_bit) =
%   if next_bit then a_enc else [ false | a in a_enc ] endif;

function array[int] of var bool: int_times_binary_partial(array[int] of var bool: a_enc, var bool: next_bit) =
  [ next_bit /\ a | a in a_enc ];

predicate int_times_binary(array[int] of var bool: a_enc, array[int] of var bool: b_enc, array[int] of var bool: c_enc) =
  let {
    % constraint abort("X");
    array[int] of var bool: a_enc_extended = two_complement_extend(a_enc, length(a_enc)+1); % extend sign bit on multiplicand
    array[int] of var bool: partial = int_times_binary_partial(a_enc_extended, b_enc[1]);
  } in int_times_binary(
    a_enc_extended,
    b_enc,
    2,
    two_complement_extend(partial, length(partial)+1), % shift while preserving sign bit
    c_enc
  );

predicate int_times_binary(array[int] of var bool: a_enc, array[int] of var bool: b_enc, int: i, array[int] of var bool: prev_partial, array[int] of var bool: c_enc) =
  if i <= length(b_enc) then
    let {
      array[int] of var bool: next_partial = int_times_binary_partial(a_enc, b_enc[i]);

      % Sum the n most significant bits (and the sign) bit of the previous and next partial products, but subtract (take two's complement) for the last partial product
      array[1..length(b_enc)+1] of var bool: partial_sum;
      constraint int_plus_binary(
        array1d(prev_partial[i..]), % only the n most significant bits + the extended sign bit have to be summed
        if i == length(b_enc) then
          [ not b | b in next_partial ] % negate if taking two's complement
        else
          next_partial
        endif,
        i == length(b_enc), % add one if taking two's complement
        partial_sum
      );
    } in
      int_times_binary(
        a_enc,
        b_enc,
        i+1,
        two_complement_extend(prev_partial[..i-1]++partial_sum, length(partial_sum)+1), % re-add the "insignificant" bits and shift
        c_enc
      )
  else
    % discard sign bit and done
    int_eq_binary(c_enc, prev_partial[1..length(prev_partial)-1])
  endif;

function string: print_binary(array[int] of var bool: xs) =
  join("", [ if is_fixed(x) /\ fix(x) then "1" elseif is_fixed(x) /\ not fix(x) then "0" else "x" endif | x in reverse(xs) ]);

predicate int_times_binary(array[int] of var bool: a_enc, var bool: multiplicand, array[int] of var bool: c_enc) =
  forall(i in index_set(a_enc))( c_enc[i] <-> (multiplicand /\ a_enc[i]) );

% a/b = c -> a = b*c + r
predicate int_div_binary(var int: x, var int: y, var int: q) =
  q == aux_int_division_modulo_fn(x,y)[1];

predicate int_mod_binary(var int: x, var int: y, var int: r) =
  r == aux_int_division_modulo_fn(x,y)[2];

function array[int] of var int: aux_int_division_modulo_fn(var int: x, var int: y) =
  let {
    %% Domain of q
    set of int: dom_q =
      if lb(y)*ub(y)>0 then
        let {
          set of int: EP = { ub(x) div ub(y), ub(x) div lb(y), lb(x) div ub(y), lb(x) div lb(y) },
        } in min(EP)..max(EP)
      else
        let {
          int: mm = max( abs(lb(x)), abs(ub(x)) ),
        } in -mm..mm                   %% TODO case when -1 or 1 not in dom(x)
      endif,
    var dom_q: q;
    int: by = max(abs(lb(y)), abs(ub(y)));
    var -by+1..by-1: r;
    constraint x = y * q + r,
    constraint 0 <= x -> 0 <= r,  %%  which is    0 > x \/ 0 <= r
    constraint x < 0 -> r <= 0,   %%  which is    x >= 0 \/ r <= 0
    constraint abs(r) < abs(y);
  } in
    [ q, r ];


% TODO lexicographic constraints weren't half-reified properly!
predicate lex_lesseq_bool(array[int] of bool: c, array[int] of var bool: x) =
  lex_lesseq_bool_imp(c,x,true);

predicate lex_lesseq_bool_reif(array[int] of bool: c, array[int] of var bool: x) =
  let {
    constraint abort("_reif stubb should not be used");
  } in false;
predicate lex_lesseq_bool_imp(array[int] of bool: c, array[int] of var bool: x, var bool: r) =
  forall(i in index_set(c) where c[i])(
    clause([x[i]] ++ [ x[j] | j in index_set(c) where j < i /\ not c[j]],[r])
  );

% x <= c -> c >= x
predicate lex_lesseq_bool(array[int] of var bool: x, array[int] of bool: c) =
  lex_geq_bool(c,x);
predicate lex_geq_bool_imp(array[int] of bool: c, array[int] of var bool: x, var bool: r) =
  forall(i in index_set(c) where not c[i])(
    clause([], [r, x[i]] ++ [ x[j] | j in index_set(c) where j < i /\ c[j] ])
  );

predicate lex_geq_bool(array[int] of bool: c, array[int] of var bool: x) =
  lex_geq_bool_imp(c,x,true);

predicate lex_geq_bool_reif(array[int] of bool: c, array[int] of var bool: x, var bool: r) =
  let {
    constraint trace("lex_geq_bool_reif\n");
    constraint abort("");
  } in false;

