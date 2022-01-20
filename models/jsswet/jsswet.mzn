% Job-shop-scheduling with weighted earliness/tardiness (jsswet)
    % Note: we sometimes use `annotate_sat_encoding` instead of direct annotations (::binary_encoded), so that we can easily change the configuration via data parameters in experiments
    % The included instances are converted from regular (non-WET, that is, makespan minimization) jobshop instances (https://github.com/MiniZinc/minizinc-benchmarks/tree/master/jobshop), without deadlines and earliness/tardiness coefficients.

predicate picat_cumulative(array[int] of var int: s, array[int] of var int: d, array[int] of var int: r, var int: b);
include "../../sat-declarations.mzn";
opt bool: f_mzn_sat;
bool: mzn_sat = f_mzn_sat default true;

opt bool: f_use_globals;
bool: use_globals = f_use_globals default not mzn_sat;

opt bool: f_is_picat_sat;
bool: is_picat_sat = f_is_picat_sat default false;

opt bool: f_use_cumulative;
bool: use_cumulative = f_use_cumulative default true;

opt bool: f_use_fixed_horizon;
bool: use_fixed_horizon = f_use_fixed_horizon default false;

bool: separateEarlinessFromTardinessCost = false;

int: n_machines;                        % The number of machines.
int: n_jobs;                            % The number of jobs.
int: n_tasks_per_job = n_machines;      % Each job has one task per machine.

opt bool: f_is_satisfiable;
bool: is_satisfiable = f_is_satisfiable default true;
set of int: jobs = 1..n_jobs;
set of int: tasks = 1..n_tasks_per_job;
set of int: machines = 0..n_machines-1;

int: job_penalty_mixed_cut = f_job_penalty_mixed_cut default 0;
opt int: f_job_penalty_mixed_cut;
array[jobs,1..3] of int: deadline; % deadline and early/tardy coefficients for each job ([deadline[t], earliness[t], tardiness[t]])

int: optimal;  % optimal (or near-optimal) objective value
float: HIGH_PRIORITY_RATIO = 0.4;
int: HIGH_PRIORITY_PENALTY = f_high_priority_penalty default -1;
opt int: f_high_priority_penalty;
int: HIGH_PRIORITY_HARD_DEADLINE = f_high_priority_hard_deadline default -1;
opt int: f_high_priority_hard_deadline;
array[jobs] of bool: high_priority = [ HIGH_PRIORITY_HARD_DEADLINE>=0 /\ i <= round(card(jobs)*HIGH_PRIORITY_RATIO) | i in jobs ];

array[int,int] of int: dl = array2d(jobs, 1..3, [
  if high_priority[i] /\ HIGH_PRIORITY_PENALTY != -1 then
    [deadline[i,1],HIGH_PRIORITY_PENALTY,HIGH_PRIORITY_PENALTY][j]
  else
    [deadline[i,1],max(1,deadline[i,2]),max(1,deadline[i,3])][j]
  endif
          | i in jobs, j in 1..3 ]);
float: margin = 1.0; % by what factor our objective constraint can be off from the optimal

% job_task_machine[j, k] is the machine required by task k of job j.
array[int,tasks] of machines: job_task_machine;

array [int,tasks] of int: job_task_duration;

% constraint trace("maxCosts \(maxCosts)\n");
% + sum(i in jobs where deadline[i,3] == 0)( % TODO to be replaced by horizon bounds in data
%   job_task_duration[i,max(tasks)]
% );


% Variables
% set of int: horizon = 0..sum(array1d(job_task_duration));
% set of int: horizon = 0..horizon_max;
set of int: fixed_horizon;
set of int: horizon = if use_fixed_horizon then
  fixed_horizon
else
  0..horizon_max
endif;

array [jobs, 1..2] of int: job_bounds =
  if use_fixed_horizon then
    array2d(jobs, 1..2, [ [min(fixed_horizon),max(fixed_horizon)][j] | i in jobs, j in 1..2 ])
  else
    array2d(jobs, 1..2, [
      if j==1 then
        max(min(horizon), dl[i,1] - maxCosts[1] div dl[i,2])
      else
        min(max(horizon), dl[i,1] + maxCosts[2] div dl[i,3])
      endif | i in jobs, j in 1..2 ])
  endif;

% constraint trace("job_bounds \(job_bounds)\n");

array [jobs, tasks] of var int: x::add_to_output =
  array2d(jobs, tasks, [ let {
    % int: lb = job_bounds[i,1] + sum(k in min(tasks)..j-1)(job_task_duration[i,k]);
    % int: ub = job_bounds[i,2] - sum(k in j+1..max(tasks))(job_task_duration[i,k]);
    int: lb = if high_priority[i] then max([min(horizon), dl[i,1]-HIGH_PRIORITY_HARD_DEADLINE, job_bounds[i,1]]) else job_bounds[i,1] endif;
    int: ub = if high_priority[i] then min([max(horizon), dl[i,1]+HIGH_PRIORITY_HARD_DEADLINE, job_bounds[i,2]]) else job_bounds[i,2] endif;
    var lb..ub: x_i_j;
    % constraint trace("maxCosts \(maxCosts)\n");
    % constraint trace("horizon \(horizon) \(0..sum(array1d(job_task_duration)))\n");
    % constraint trace("job-task \([i,j]) \(x_i_j) in \(dom(x_i_j)) \(dom_size(x_i_j))\n");
    % constraint trace("deadline[i,..] \(deadline[i,..])\n");
    constraint
      if SAT_encoding_mode == SAT_DEFAULT then
        if HIGH_PRIORITY_HARD_DEADLINE == -1 \/ dom_size(x_i_j) <= 2*HIGH_PRIORITY_HARD_DEADLINE+2 then
          annotate_sat_encoding(x_i_j, SAT_ORDER)
        else
          annotate_sat_encoding(x_i_j, SAT_BINARY)
        endif
      elseif SAT_encoding_mode == SAT_ORDER then
        annotate_sat_encoding(x_i_j, SAT_ORDER)
      elseif SAT_encoding_mode == SAT_BINARY then
        annotate_sat_encoding(x_i_j, SAT_BINARY)
      else
        abort("unary encoding not supported")
      endif;
    } in x_i_j |
        i in jobs,
        j in tasks
  ]);

% constraint trace("job-task-doms; \(([dom(x[i,j]) | i in jobs, j in tasks ]))\n");
% constraint trace("dom-sizes: \((sum([dom_size(x[i,j]) | i in jobs, j in tasks ])))\n");

% Asserts
constraint forall(i in jobs, j in tasks)(
  assert(job_task_duration[i, j] >= 0, "job \(i), task \(j) takes a negative amount of time.") /\
  assert(lb(x[i,j]) >= 0, "job \(i), task \(j) start earlier than time step 0")
);

% % Constraints
% Each job task must complete before the next.
constraint forall(i in jobs, j in tasks diff {max(tasks)})(
  x[i, j] + job_task_duration[i, j] <= x[i, j + 1]
);

% Tasks on the same machine cannot overlap.
% TODO check once more this takes for picat
include "disjunctive.mzn";
constraint forall(k in machines)(
  disjunctive(
    [                 x[i,j] | i in jobs, j in tasks where job_task_machine[i,j] == k ],
    [ job_task_duration[i,j] | i in jobs, j in tasks where job_task_machine[i,j] == k ],
  )
);

% array[jobs] of var int: first_tasks = x[jobs,min(tasks)];
% constraint trace("first_tasks \(index_set(first_tasks)) \(first_tasks)\n");
% array[jobs] of var int: last_tasks = x[jobs,max(tasks)];
% constraint trace("last_tasks \(index_set(last_tasks)) \(last_tasks)\n");

% Additional constraint: once started, jobs need to be finished within a certain time
opt float: f_quick_finish_slack;
float: quick_finish_slack = f_quick_finish_slack default -1.0; % -1.0 removes the constraint


enum Slack_Channel = { EQUALITY, INEQUALITY, DOUBLE_INEQUALITY };
opt Slack_Channel: f_slack_channel;
Slack_Channel: slack_channel = f_slack_channel default EQUALITY;
constraint if quick_finish_slack != -1.0 then 
  let {
    int: slack = round((1+quick_finish_slack)*sum(array1d(job_task_duration)));
  } in
  if not mzn_sat \/ SAT_encoding_mode in {SAT_ORDER, SAT_BINARY} \/ (slack_channel == EQUALITY /\ SAT_encoding_mode == SAT_DEFAULT) then
    sum(i in jobs)(
       x[i,max(tasks)] - x[i,min(tasks)] + job_task_duration[i,max(tasks)]
    ) <= slack
  else
    let {
      array[jobs,1..2] of var int: z = array2d(jobs, 1..2, [ let {
        var dom(x_i): z_i::binary_encoded;
        constraint x_i <= z_i;
        constraint if slack_channel == DOUBLE_INEQUALITY then x_i >= z_i endif;
      } in z_i
        | i in jobs,
          x_i in [ x[i,max(tasks)], affine(x[i,min(tasks)],-1,job_task_duration[i,max(tasks)]) ]
      ]);
    } in sum(z) <= slack
  endif
endif;

% % NEW
% BUGGG
array[jobs] of var int: y = [ affine(x[i,max(tasks)], 1, -dl[i,1]) | i in jobs ];

% constraint trace("y \(index_set(y)) \(y)\n");

solve minimize
  lin_exp(
    [ if j == 2 then
        -dl[i,j]
      else
         dl[i,j]
      endif | i in jobs, j in 2..3 ],
    [ 
    if j == 2 then
        min(0,y[i])
        % min(affine(last_tasks[i], 1, -dl[i,1]),0)
      else
        max(y[i],0)
        % max(affine(last_tasks[i], 1, -dl[i,1]),0)
      endif | i in jobs, j in 2..3
    ],
    0,
  );

      % if not mzn_sat \/ SAT_encoding_mode == SAT_BINARY then
      % else
      %   let { % avoid linearization compilation overhead by using order encoding variables directly; equivalent to the above case given an order encoding of x 
      %     array[int] of var bool: curr = order_encode(x[i,j]);
      %     array[int] of var bool: next = order_encode(x[i,j+1]);
      %   } in
      %     int_le_order(
      %         int_plus_order(curr, job_task_duration[i, j]),
      %         next,
      %       )
      %       ::expression_name("\(i)-\(j) before \(i)-\(j+1)")
      % endif

% fix compilation bottleneck
% 1. more memory efficient (valgrind etc)
% 2. add fixed horizon
% 3. use duration divided by 4
% 4. improve initial greedy schedule?
% 5. use oracle's good/optimal schedule?

function array [int] of int: schedJob_(array [int] of int: avail, array [int] of int: machine, array [int] of int: dur, int: k, int: t) =
  if k > length(machine) then
    avail ++ [t]
  else
    let {
      int: m = machine[k];
      int: eTask = max(avail[m], t) + dur[k];
      array [int] of int: availSucc = [ if other = machine[k] then eTask else avail[other] endif | other in 1..n_machines ];
    } in schedJob_(availSucc, machine, dur, k+1, eTask)
  endif;

function array[int] of int: wetMax_(array [int] of int: ord_jobs, int: k, array [int] of int: avail, int: Makespan, int: earlinessCostAcc, int: tardinessCostAcc) = 
  if k > length(ord_jobs) then
     [ earlinessCostAcc, tardinessCostAcc ]
  else
   let {
     int: i = ord_jobs[k];
     array [int] of int: jSched = schedJob_(avail, [job_task_machine[i, t]+1 | t in 1..n_tasks_per_job], job_task_duration[i, ..], 1, 0);
     int: complete = jSched[n_machines+1];
     int: cost = max(dl[i, 2] * (dl[i, 1] - complete), max(1, dl[i, 3]) * (complete - dl[i, 1]));
     int: earlinessCost = dl[i,2] * max(0, dl[i,1] - complete);
     int: tardinessCost = max(1, dl[i, 3]) * max(0, complete - dl[i, 1]);
     int: maxCost = max(earlinessCost, tardinessCost);
     int: newEarlinessCostAcc = if separateEarlinessFromTardinessCost then earlinessCost + earlinessCostAcc else maxCost + earlinessCostAcc  endif;
     int: newTardinessCostAcc = if separateEarlinessFromTardinessCost then tardinessCost + tardinessCostAcc else maxCost + earlinessCostAcc  endif;
   } in wetMax_(ord_jobs, k+1, jSched[1..n_machines], max(Makespan, complete), newEarlinessCostAcc, newTardinessCostAcc)
  endif;

function array[int] of int: wetMax(array [int] of int: ord_jobs) =
  wetMax_(ord_jobs, 1, [0 | m in 1..n_machines], 0, 0, 0);

% Variables
array[int] of int: ord_jobs = arg_sort(dl[..,1]);
array[1..2] of int: maxCosts = wetMax(ord_jobs);
int: horizon_max = max(i in jobs)(
  dl[i, 1] + maxCosts[2] div max(1, dl[i, 3])
);
