
% STD
predicate fzn_disjunctive(array[int] of var int: s, array[int] of var int: d) =
  let {
    constraint abort("");
  } in
  forall (i in index_set(d)) (d[i] >= 0) /\
  forall (i,j in index_set(d) where i<j)(
    d[i]=0 \/ d[j]=0 \/ s[i]+d[i] <= s[j] \/ s[j]+d[j] <= s[i]
  );

% predicate fzn_disjunctive(array[int] of var int: s, array[int] of int: d) =
%   let {
%     array[int] of SAT_encoding_modes: encs = get_one_sat_encoding(s);
%     constraint trace("encs \(encs)\n");
%     set of int: S = index_set(s);
%     constraint assert(forall(d_i in d)(d_i>0), "disjunctive doesn't support strict: forall(d_i in d)(d>0)");
%     constraint assert(index_set(d) == S, "index_set(d) == S");
%   } in
%   if exists(e in encs)(e==SAT_ORDER) then disjunctive_order(
%     [ s[i] | i in S where encs[i] == SAT_ORDER ],
%     [ d[i] | i in S where encs[i] == SAT_ORDER ],
%   ) endif /\
%   forall(i,j in S where i<j /\ (encs[i] != SAT_ORDER \/ encs[j] != SAT_ORDER))(
%       let {
%         var bool: p;
%       } in
%       if SAT_fzn_disjunctive_half_reif then
%         (p->(s[i]+d[i] <= s[j])) /\
%           ((not p) -> (s[j]+d[j] <= s[i]))
%       else
%         (p<->(s[i]+d[i] <= s[j])) /\
%           ((not p) <-> (s[j]+d[j] <= s[i]))
%       endif
%   )

predicate fzn_disjunctive(array[int] of var int: s, array[int] of int: d) =
  let {
    array[int] of SAT_encoding_modes: encs = get_one_sat_encoding(s);
    set of int: S = index_set(s);
    constraint assert(forall(d_i in d)(d_i>0), "disjunctive doesn't support strict: forall(d_i in d)(d>0)");
    constraint assert(index_set(d) == S, "index_set(d) == S");
  } in
  if SAT_fzn_disjunctive_order_alternative then
    disjunctive_order(s, d)
  else
    forall(i,j in S where i<j)(
      let {
        var bool: p::expression_name_dbg("fzn_disjunctive p \(i),\(j)");
      } in
      if SAT_fzn_disjunctive_half_reif then
        int_le_imp(affine(s[i],1,d[i]), s[j], p)
        % (p->(s[i]+d[i] <= s[j]))
        ::expression_name_dbg("disjunctive_a \(p) -> \(s[i])+\(d[i])<=\(s[j]) \([i,j])")
        /\
        int_le_imp(affine(s[j],1,d[j]), s[i], not p)
        % ((not p) -> (s[j]+d[j] <= s[i]))
        ::expression_name_dbg("disjunctive_b not \(p) -> \(s[j])+\(d[j])<=\(s[i]) \([i,j])")
      else
        (p<->(s[i]+d[i] <= s[j])) /\
          ((not p) <-> (s[j]+d[j] <= s[i]))
      endif
    )
  endif;

bool: disjunctive_order_p = true;

predicate disjunctive_order(array [int] of var int: s, array [int] of int: d) =
  if length(s) <= 1 then true else
  let {
    set of int: tasks = index_set(s);
    int: first = min(tasks); % task #1
    % Can skip encoding everything before the earliest end time,
    % or latest s time (think about the resource profile).
    int: earliest_task_end = min(j in tasks)(lb(s[j]) + d[j] - 1);
    int: latest_task_start = max(j in tasks)(ub(s[j]));
    set of int: machine_horizon = earliest_task_end..latest_task_start;
    array[min(tasks)-1..max(tasks),machine_horizon] of var bool: p::expression_name_dbg("fzn_disjunctive p"); % for task i, whether it's running at time j
    constraint forall(p_j_t in p[min(tasks)-1,machine_horizon])(not p_j_t);
  } in
  forall(j in tasks)(
    let { % again, using order encoding variables and posting clauses directly (instead of using linearization) to avoid compilation bottleneck
      array[int] of var bool: job_task_j_enc = order_encode(s[j]);
      % constraint trace("job_task_j_enc \(job_task_j_enc)\n");
    } in
    forall(t in machine_horizon)(
      (p[j-1,t] -> p[j,t])
      ::expression_name_dbg("p0")
      /\
    let {
      var bool: t_after_end = order_encoding_element_partial(job_task_j_enc, t+1-d[j]);
      var bool: t_before_start = order_encoding_element_partial(job_task_j_enc, t+1);
    } in
        clause(
          [t_before_start, p[j,t]],
          [t_after_end],
        )
        ::expression_name_dbg("p1")
        /\ clause(
          [t_before_start],
          [t_after_end, p[j-1,t]],
        )
        ::expression_name_dbg("p2")
    )
  )
  endif;






% predicate cumulative_order_general(
%   array [int] of var int: x_k, % job_task start times of tasks requiring machine k
%   array [int] of int: job_task_duration,
%   array [int] of int: job_task_requirement,
%   int: cap) =
%     let {
%       set of int: tasks = index_set(x_k);
%       int: first = min(tasks); % task #1
%       % Can skip encoding everything before the earliest end time,
%       % or latest x_k time (think about the resource profile).
%       int: earliest_task_end = min(j in tasks)(lb(x_k[j]) + job_task_duration[j] - 1);
%       int: latest_task_start = max(j in tasks)(ub(x_k[j]));
%       set of int: horizon = earliest_task_end..latest_task_start;
%       array[min(tasks)-1..max(tasks),horizon] of var bool: p
%         ::expression_name("cumulative_order_general_p")
%       ;
%       constraint forall(p_j_t in p[min(tasks)-1,horizon])(not p_j_t);
%     } in
%     forall(j in tasks)(
%       % let { % again, using order encoding variables and posting clauses directly (instead of using linearization) to avoid compilation bottleneck
%       %   array[int] of var bool: job_task_j_enc = order_encode(x_k[j]);
%       % } in
%       forall(t in horizon)(
%         (p[j-1,t] -> p[j,t]) /\
%       let {
%         var bool: t_after_end = x_k[j] >= t+1-job_task_duration[j];
%         var bool: t_before_start = x_k[j] >= t+1;
%       } in (t_before_start \/ p[j,t] \/ not t_after_end)
%         /\ (t_before_start \/ not t_after_end \/ not p[j-1,t])
%     )
%   );

% %% Assumes s is order encoded, so the horizon isn't super huge.
% predicate cumulative_order_graeme(array [int] of var int: start, array [int] of int: d,
%   array [int] of int: r, int: cap) =
%   let {
%     constraint trace("cumulative_order_graeme\n");
%     set of int: Task = index_set(start) ;
%     int: first = min(Task) ;
%     % Can skip encoding everything before the earliest end time,
%     % or latest start time (think about the resource profile).
%     int: tMin = min (t in Task) (lb(start[t]) + d[t] - 1) ;
%     int: tMax = max (t in Task) (ub(start[t])) ;
%   } in
%   forall (t in tMin..tMax) (
%     let {
%       array [Task] of var 0..cap: psum; %% Should be order encoded.
%       constraint forall(i in Task)(annotate_sat_encoding(psum[i], SAT_ORDER));
%     } in
%     % We avoid the reified sum, to avoid introducing extra variables
%     psum[first] <= r[first] 
%     /\ (start[first] <= t - d[first] \/ start[first] > t \/ psum[first] >= r[first] )
%     /\ forall (i in Task diff {first}) (psum[i] >= psum[i-1])
%     /\ forall (i in Task diff {first}) (
%       forall (s in 0..cap) (
%         psum[i-1] < s \/ start[i] <= t - d[i] \/ start[i] > t \/ psum[i] >= s+r[i]
%       )
%     )
%   );

