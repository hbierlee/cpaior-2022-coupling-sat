include "order_encode.mzn";

% https://www.wolframalpha.com/input/?i=r+EQUIVALENT+%28%28a+OR+b+OR+c%29+OR+%28not+d+or+not+e+or+not+f%29%29
predicate bool_clause_reif(array[int] of var bool: as, array[int] of var bool: bs, bool: r) =
  if r then bool_clause(as, bs) else forall([not a | a in as]) /\ forall(bs) endif;

predicate bool_clause_reif(array[int] of var bool: as, array[int] of var bool: bs, var bool: r) =
  bool_clause(as,bs++[r]) /\
  forall(a in as)(bool_clause([r],[a])) /\
  forall(b in bs)(bool_clause([b,r],[]));
    
predicate array_float_minimum(var float: m, array[int] of var float: x) =
  abort("Not supported");

predicate array_float_maximum(var float: m, array[int] of var float: x) =
  abort("Not supported");

% % TODO [std] this should probably be done in std?
predicate array_int_minimum(var int: m, array[int] of int: xs) =
  m = min(xs);

predicate array_int_minimum(var int: m, array[int] of var int: xs) =
  forall(x in xs)(m <= x) /\ let { var index_set(xs): i; } in array_var_int_element_nonshifted(i, xs, m);
  % TODO  array_int_maximum_order/min needs to be fixed first, tests/spec/unit/sat/bugs/5_stack_cuttingstock_array_int_max_order_potential_compiler_bug.mzn
  % if has_sat_ann(m, order_encoded) then
  % elseif has_sat_ann(m, unary_encoded) \/ has_sat_ann(m, binary_encoded) \/ is_fixed(m) then
  %   forall(x in xs)(m <= x) /\ let { var index_set(xs): i; } in m == xs[i]
  % else
  %   % TODO check xs elements encodings?
  %   annotate_sat_encoding(m, SAT_INT_INEQUALITY_DEFAULT_ENCODING)
  %   /\ array_int_minimum(m, xs)
  % endif;


  % TODO look into that array_int_minimum_order really works with fixed elements in xs
  % let {
  %   % m has to be at least as small as the smallest value
  %   array[int] of var int: xs_fix = [ x | x in xs where is_fixed(x) ];
  %   constraint if length(xs_fix) > 0 then m <= min(xs_fix) endif;
  %   array[int] of var int: xs_var = [ x | x in xs where not is_fixed(x) ];
  % } in
  % if length(xs_var) == 0 then
  %   m == min(xs_fix)
  % elseif length(xs_var) == 1 then
  % % m = min(5,b) -> m <= 5, b;8 then m=5, if b;3 then m=3
  %   m == xs_var[1]
  % else
  %   if has_sat_ann(m, order_encoded) then
  %     array_int_minimum_order(m, xs_var)
  %   elseif has_sat_ann(m, unary_encoded) \/ has_sat_ann(m, binary_encoded) then
  %     forall(x in xs_var)(m <= x) /\ let { var index_set(xs_var): i; } in m == xs_var[i]
  %   else
  %     % TODO check xs_var elements encodings?
  %     annotate_sat_encoding(m, SAT_INT_INEQUALITY_DEFAULT_ENCODING)
  %     /\ array_int_minimum(m, xs_var)
  %   endif
  % endif;

predicate array_int_maximum(var int: m, array[int] of int: xs) =
  m = max(xs);

% predicate array_int_maximum(var int: m, array[int] of var int: xs) =
% let {
%   constraint SAT_trace("array_int_maximum\n");
%   constraint SAT_trace(2, "m \(m) in \(dom(m))\n");
%   constraint SAT_trace(2, "xs \(index_set(xs)) \(xs)\n");
% } in
%     % array_int_maximum_order(m, xs);
%   % 0, 1..2
%   % 0 <= 2
%   % 1..2 <= 2
%   forall(x in xs)(x <= m)
%   % m == 1, 0 <= m, 1 <= m
%   % m == 2, 0 <= m, 2 <= m
%   /\ let { var index_set(xs): i; } in m = xs[i];

  % max(x in xs where is_fixed(x))(fix(x)) <= m
  % /\ forall(x in xs where not is_fixed(x))(x <= m)
  % /\ let { var index_set(xs): i; } in m = xs[i];




predicate array_int_maximum(var int: m, array[int] of var int: xs) =
  if has_sat_ann(m, order_encoded) then
    array_int_maximum_order(m, xs)
  elseif has_sat_ann(m, unary_encoded) \/ has_sat_ann(m, binary_encoded) \/ is_fixed(m) then
    forall(x in xs)(x <= m) /\ let { var index_set(xs): i; } in array_var_int_element_nonshifted(i, xs, m)
  else
    annotate_sat_encoding(m, SAT_INT_INEQUALITY_DEFAULT_ENCODING)
    /\ array_int_maximum(m, xs)
  endif;


% predicate array_int_maximum(var int: m, array[int] of var int: xs) =
%   % TODO look into that array_int_minimum_order really works with fixed elements in xs
%   let {
%     constraint assert(length(xs) > 0, "array in xs array_int_maximum should have at least one element but has 0");
%     % m has to be at least the greatest fixed value
%     array[int] of var int: xs_fix = [ x | x in xs where is_fixed(x) ];
%     constraint if length(xs_fix) > 0 then m >= max(xs_fix) endif;
%     array[int] of var int: xs_var = [ x | x in xs where not is_fixed(x) ];
%   } in
%   if length(xs_var) == 0 then
%     m == max(xs_fix)
%   elseif length(xs_var) == 1 then
%     m == xs_var[1]
%   else
%     if has_sat_ann(m, order_encoded) then
%       array_int_maximum_order(m, xs_var)
%     elseif has_sat_ann(m, unary_encoded) \/ has_sat_ann(m, binary_encoded) then
%       forall(x in xs_var)(x <= m) /\ let { var index_set(xs_var): i; } in m = xs_var[i]
%     else
%       annotate_sat_encoding(m, SAT_INT_INEQUALITY_DEFAULT_ENCODING)
%       /\ array_int_maximum(m, xs_var)
%     endif
%   endif;
