predicate fzn_bdd(array[int] of var bool: x, array[int] of int: low_children, array[int] of int: high_children, var bool: zero_terminal, var bool: one_terminal) =
  let {
    % aux variables denoting whether a[i] is in the path, except for a[0] and a[1], which are the zero and one terminal
    array[0..length(x)] of var bool: a;
    constraint a[0] = zero_terminal;
    constraint a[1] = one_terminal;
  } in
   forall(i in index_set(x))(
    fzn_bdd_node(
      x[i],
      a[low_children[i]],
      a[high_children[i]],
      % this is the only instance wherein a[i] refers to whether node i is in the path; which is always true since it's the root node
      if i == 1 then true else a[i] endif
    )
  ) /\
    if not is_fixed(zero_terminal) then
      zero_terminal -> exists(
        [a[i] /\ not x[i] | i in index_set(low_children) where low_children[i] == 0] % parent nodes of zero_terminal connected via false edge
        ++ [a[i] /\ x[i] | i in index_set(high_children) where high_children[i] == 0], % parent nodes of zero_terminal connected via true edge
      )
    endif /\
    if not is_fixed(one_terminal) then
    one_terminal -> exists(
        [a[i] /\ not x[i] | i in index_set(low_children) where low_children[i] == 1] % parent nodes of one_terminal connected via false edge
        ++ [a[i] /\ x[i] | i in index_set(high_children) where high_children[i] == 1], % parent nodes of one_terminal connected via true edge
    )
    endif;

% General case: No fixed variables
predicate fzn_bdd_node(var bool: x, var bool: f, var bool: t, var bool: a) = 
     (not x /\ not f -> not a)
  /\ (not x /\ f -> a)
  /\ (x /\ not t -> not a)
  /\ (x /\ t -> a)
  /\ (t /\ f -> a)
  /\ (not t /\ not f -> not a);

% % General case: No fixed variables
% predicate fzn_bdd_node(var bool: x, var bool: f, var bool: t, var bool: a) = 
%      bool_clause([f,x],[a])  % (not x /\ not f -> not a)
%   /\ bool_clause([a,x],[f])  % (not x /\ f -> a)
%   /\ bool_clause([t],[a,x])  % (x /\ not t -> not a) 
%   /\ bool_clause([a],[t,x])  % (x /\ t -> a) 
%   /\ bool_clause([a],[f,t])  % (t /\ f -> a)
%   /\ bool_clause([f,t],[a]); % (not t /\ not f -> not a);

% 5 observation about x, f, t and a in fzn_bdd_node
% the a's are never fixed, except for a[0] which is false and a[1] which is true (only the latter is as input argument of fzn_bdd_node)
% the x's are never fixed (because of preprocessing)
% t -> f (because making a coefficient false will only decrease the lhs)
% not f -> not t (similarly)
% Consequently: t and not f is impossible

% fixed a
predicate fzn_bdd_node(var bool: x, bool: f, var bool: t, bool: a) = 
  if f then bool_clause([t],[x]) else bool_clause([x],[]) endif;

predicate fzn_bdd_node(var bool: x, var bool: f, bool: t, bool: a) = 
  if t then bool_clause([x,f],[]) else bool_clause([],[x]) endif;

predicate fzn_bdd_node(var bool: x, bool: f, bool: t, bool: a) = 
   % let { constraint trace("fzn_bdd_node(var bool: \(x) bool: \(f) bool: \(t) bool: \(a)\n")} in 
  if t /\ f then
    true
  elseif f /\ not t then
    bool_clause([],[x])
  else
    false
  endif;

% fixed f or t
predicate fzn_bdd_node(var bool: x, var bool: f, var bool: t, bool: a) = 
  % let { constraint trace("fzn_bdd_node(var bool: \(x) var bool: \(f) var bool: \(t) bool: \(a)\n")} in
  bool_clause([x,f],[])
  /\ bool_clause([t],[x])
  /\ bool_clause([f,t],[]);

predicate fzn_bdd_node(var bool: x, bool: f, var bool: t, var bool: a) = 
  % let { constraint trace("fzn_bdd_node(var bool: \(x) bool: \(f) var bool: \(t) var bool: \(a)\n")} in 
  fzn_bdd_node_one_fixed_child(x, f, t, a, false);

predicate fzn_bdd_node(var bool: x, var bool: f, bool: t, var bool: a) = 
  % let { constraint trace("fzn_bdd_node(var bool: \(x) var bool: \(f) bool: \(t) var bool: \(a)\n") } in 
  fzn_bdd_node_one_fixed_child(x, t, f, a, true);
  
predicate fzn_bdd_node_one_fixed_child(var bool: x, bool: fixed_child, var bool: non_fixed_child, var bool: a, bool: inv) = 
  % let { constraint trace("fzn_bdd_node_one_fixed_child(var bool: \(x) bool: \(fixed_child) var bool: \(non_fixed_child) var bool: \(a) bool: \(inv)\n")} in 
  if fixed_child then
    if (is_fixed(non_fixed_child) /\ fix(non_fixed_child)) then
      bool_clause_inv([a],[],inv)
    elseif (is_fixed(non_fixed_child) /\ not fix(non_fixed_child)) then
      bool_clause([x,a], []) /\ bool_clause([], [x,a]) % x != a
    else
      bool_clause_inv([x,a],[],inv) /\ 
      bool_clause_inv([non_fixed_child],[x,a],inv) /\ 
      bool_clause_inv([a],[x,non_fixed_child],inv) /\ 
      bool_clause_inv([a],[non_fixed_child],inv)
    endif
  else % not f implies not t
    bool_clause_inv([],[a],inv)
  endif;

predicate bool_clause_inv(array[int] of var bool: a, array[int] of var bool: b, bool: inv) = 
  if (inv) then
    bool_clause(b,a)
  else
    bool_clause(a,b)
  endif;

% predicate fzn_bdd_node(var bool: x, var bool: f, var bool: t, var bool: a) = 
%   let { 
%     constraint trace("fzn_bdd_node x: \(x) f: \(f) t: \(t) a: \(a)\n"),
%   } in 
%   if is_fixed(f) then
%     if fix(f) then
%       if (is_fixed(t) /\ fix(t)) then
%         bool_clause([a],[])
%       elseif (is_fixed(t) /\ not fix(t)) then
%         bool_not(x,a)
%       else
%         bool_clause([x,a],[]) /\ 
%         bool_clause([t],[x,a]) /\ 
%         bool_clause([a],[x,t]) /\ 
%         bool_clause([a],[t])
%       endif
%     else % not f implies not t
%       bool_clause([],[a])
%     endif
%   elseif is_fixed(t) then
%     if fix(t) then % t implies f
%       bool_clause([a],[])
%     else
%       if (is_fixed(f) /\ fix(f)) then
%         bool_not(x,a)
%       elseif (is_fixed(f) /\ not fix(f)) then
%         bool_clause([],[a])
%       else
%         bool_clause([],[x,a]) /\ 
%         bool_clause([a,x],[f]) /\ 
%         bool_clause([f,x],[a]) /\ 
%         bool_clause([f],[a])
%       endif
%     endif
%   else
%        bool_clause([f,x],[a])  % (not x /\ not f -> not a)
%     /\ bool_clause([a,x],[f])  % (not x /\ f -> a)
%     /\ bool_clause([t],[a,x])  % (x /\ not t -> not a) 
%     /\ bool_clause([a],[t,x])  % (x /\ t -> a) 
%     /\ bool_clause([a],[f,t])  % (t /\ f -> a)
%     /\ bool_clause([f,t],[a]) % (not t /\ not f -> not a);
%   endif

     % (not x /\ not f -> not a) 
  % /\ (not x /\ f -> a)         
  % /\ (x /\ not t -> not a)     
  % /\ (x /\ t -> a)             
  % /\ (t /\ f -> a)             
  % /\ (not t /\ not f -> not a);


     % (not x /\ not f -> not a)
  % /\ (not x /\ f -> a)
  % /\ (x /\ not t -> not a) 
  % /\ (x /\ t -> a) 
  % /\ (t /\ f -> a)
  % /\ (not t /\ not f -> not a);
     % bool_and_imp(not x, not f, not a)
  % /\ bool_and_imp(not x, f, a)
  % /\ bool_and_imp(x, not t, not a)
  % /\ bool_and_imp(x, t, a)
  % /\ bool_and_imp(t, f, a)
  % /\ bool_and_imp(not t, not f, not a);

