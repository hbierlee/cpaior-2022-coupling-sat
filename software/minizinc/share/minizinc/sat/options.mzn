/*
% Controls
%
*/
include "options_bimander.mzn";

mzn_opt_linearize_objective=true;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Subtour elimination in circuit %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% --------------------------------------------------------------------------------------- %
opt int: SAT_nSECcuts;       %% 0,1: use MTZ formulation
int: SAT_nMZN__fSECcuts =    %% 1,2: pass on circuit constraints to the MIP_solverinstance's cut gen
           if absent( SAT_nSECcuts ) then 0
           else deopt( SAT_nSECcuts ) endif;

%%%%%%%%%%%%%%%%%%%%%  Redundant constraints ---------------------------------------------- %
bool: SAT_fMZN__IgnoreRedundantCumulative=false;
%% NOT WORKING NOW, use redefs_2.0.2.mzn: 
%%%%% bool: fMZN__IgnoreAllUserRedundant=false;   %% ignore all user-spec redundant constr

% ----------------------------------------------------------------------------------------- %
bool: SAT_fIntTimesBool=true;       %% Special handling of multiplication with a boolean(*const)

%-----------------------------------------------------------------------------%
%    If not postprocessing domains: For unary encoding: maximal domain length to invoke it

int: SAT_nMZN__UnarySizeMax_intTimes=20;
int: SAT_nMZN__UnarySizeMax_cumul=2000;
int: SAT_nMZN__UnarySizeMax_1step_regular=20000;   %% network-flow decomp in the regular constraint

%-----------------------------------------------------------------------------%
%%% Set =true to PRINT TRACING messages for some constraints:

% Options

enum SAT_encoding_modes = { SAT_DEFAULT, SAT_UNARY, SAT_ORDER, SAT_BINARY };

ann: unary_order_channeled;
ann: unary_binary_channeled;
ann: order_binary_channeled;


opt SAT_encoding_modes: fSAT_encoding_mode;
opt bool: fSAT_int_plus_pb;
opt bool: fSAT_optimize_int_lin_bounds;
opt bool: fSAT_pblib_reify;
opt bool: fSAT_pre_emptive_partial_encoding;
opt bool: fSAT_set_in_to_ranges;
opt bool: fSAT_channel_two_way = true; % TODO one-way is not supported
opt bool: fSAT_channel_two_way_pb;
opt bool: fSAT_add_all_encoding_constraints;
opt bool: fSAT_constrain_all_encodings;
opt int: fSATVerbosity;

SAT_encoding_modes: SAT_ENCODING_MODE_DEFAULT = SAT_DEFAULT;
bool: SAT_ADD_ALL_ENCODING_CONSTRAINTS_DEFAULT = false;
bool: SAT_INT_PLUS_PB_DEFAULT = true;
bool: SAT_OPTIMIZE_INT_LIN_BOUNDS_DEFAULT = false;
bool: SAT_PBLIB_REIFY_DEFAULT = false;
bool: SAT_PRE_EMPTIVE_PARTIAL_ENCODING_DEFAULT = false;
bool: SAT_SET_IN_TO_RANGES_DEFAULT = true;
int: SAT_VERBOSITY_DEFAULT = 0;
bool: SAT_CHANNEL_TWO_WAY_DEFAULT = true;
bool: SAT_CHANNEL_TWO_WAY_PB_DEFAULT = false;
bool: SAT_CONSTRAIN_ALL_ENCODINGS_DEFAULT = false;
int: SAT_RANGES_IN_REIF_CUT_OFF = 7;

% dev options (can't be set by data)
bool: SAT_assert_allow_pbify = true;
opt bool: fSAT_allow_redundant_encodings;

bool: SAT_ALLOW_REDUNDANT_ENCODINGS_DEFAULT = true;

bool: SAT_allow_redundant_encodings =
  if absent( fSAT_allow_redundant_encodings ) then
    SAT_ALLOW_REDUNDANT_ENCODINGS_DEFAULT
  else deopt( fSAT_allow_redundant_encodings ) endif;

bool: SAT_constrain_all_encodings =
  if absent( fSAT_constrain_all_encodings ) then
    SAT_CONSTRAIN_ALL_ENCODINGS_DEFAULT
  else deopt( fSAT_constrain_all_encodings ) endif;


bool: SAT_channel_two_way =
  if absent( fSAT_channel_two_way ) then
    SAT_CHANNEL_TWO_WAY_DEFAULT
  else deopt( fSAT_channel_two_way ) endif;

bool: SAT_channel_two_way_pb =
  if absent( fSAT_channel_two_way_pb ) then
    SAT_CHANNEL_TWO_WAY_PB_DEFAULT
  else deopt( fSAT_channel_two_way_pb ) endif;

bool: SAT_ADD_ALL_ENCODING_CONSTRAINTS =
  if absent( fSAT_add_all_encoding_constraints ) then
    SAT_ADD_ALL_ENCODING_CONSTRAINTS_DEFAULT
  else deopt( fSAT_add_all_encoding_constraints ) endif;

bool: SAT_pre_emptive_partial_encoding =
  if absent( fSAT_pre_emptive_partial_encoding ) then
    SAT_PRE_EMPTIVE_PARTIAL_ENCODING_DEFAULT
  else deopt( fSAT_pre_emptive_partial_encoding ) endif;

bool: SAT_optimize_int_lin_bounds =
  if absent( fSAT_optimize_int_lin_bounds ) then
    SAT_OPTIMIZE_INT_LIN_BOUNDS_DEFAULT
  else deopt( fSAT_optimize_int_lin_bounds ) endif;

bool: SAT_pblib_reify =
  if absent( fSAT_pblib_reify ) then
    SAT_PBLIB_REIFY_DEFAULT
  else deopt( fSAT_pblib_reify ) endif;
bool: SAT_set_in_to_ranges =
  if absent( fSAT_set_in_to_ranges ) then
    SAT_SET_IN_TO_RANGES_DEFAULT
  else deopt( fSAT_set_in_to_ranges ) endif;

bool: SAT_int_plus_pb =
  if absent( fSAT_int_plus_pb ) then
    SAT_INT_PLUS_PB_DEFAULT
  else deopt( fSAT_int_plus_pb ) endif;

int: mzn__sat_verbosity =
  if absent( fSATVerbosity ) then SAT_VERBOSITY_DEFAULT else deopt( fSATVerbosity ) endif;

test SAT_trace(int: verbosity, string: msg) ::promise_total =
  if verbosity <= mzn__sat_verbosity then trace("!!! " ++ msg) endif;

test SAT_trace(string: msg) ::promise_total =
  SAT_trace(1, "!!! " ++ msg);

% clause weight multiplier (mixed encoding minimizes total weight, so lower weight, more clauses, less variables)
float: SAT_cardinality_network_lambda = 5; % balanced, -1 for always direct (hard-coded), -2 for always recursive (hard-coded)

SAT_encoding_modes: SAT_encoding_mode =
  if absent(fSAT_encoding_mode) then SAT_ENCODING_MODE_DEFAULT else deopt(fSAT_encoding_mode) endif;

string: SAT_TRIVIAL_QUALITY_ERROR = "This encoding-specific (in)equality redefinition is not responsible for constraining trivial cases, which are handled generally in sat/redefs_int.mzn";
string: SAT_UNKNOWN_ENCODING_ERROR = "Constraint dispatcher encountered unknown encoding(s)";
% Constraint default encodings

SAT_encoding_modes: SAT_INT_ABS_DEFAULT_ENCODING = SAT_BINARY;
SAT_encoding_modes: SAT_INT_DIV_DEFAULT_ENCODING = SAT_BINARY;
SAT_encoding_modes: SAT_INT_EQUALITY_DEFAULT_ENCODING = SAT_UNARY; % also for int_lin_eq, int_ne
SAT_encoding_modes: SAT_INT_INEQUALITY_DEFAULT_ENCODING = SAT_ORDER; % also for int_lin_le, min/max
SAT_encoding_modes: SAT_INT_PLUS_DEFAULT_ENCODING = SAT_BINARY;
SAT_encoding_modes: SAT_INT_MOD_DEFAULT_ENCODING = SAT_BINARY;
SAT_encoding_modes: SAT_INT_TIMES_DEFAULT_ENCODING = SAT_BINARY;
SAT_encoding_modes: SAT_SET_IN_DEFAULT_ENCODING = SAT_ORDER;
SAT_encoding_modes: SAT_OBJ_INT_LIN_EQ_DEFAULT_ENCODING = SAT_UNARY;

opt bool: f_use_binary_views;
bool: use_binary_views = f_use_binary_views default false;
SAT_encoding_modes: SAT_circuit_successor_var_encoding = fSAT_circuit_successor_var_encoding default SAT_UNARY;
opt SAT_encoding_modes: fSAT_circuit_successor_var_encoding;

opt SAT_encoding_modes: fSAT_circuit_order_var_encoding;
SAT_encoding_modes: SAT_circuit_order_var_encoding = fSAT_circuit_order_var_encoding default SAT_ORDER;

opt SAT_encoding_modes: fSAT_array_var_int_element_result_encoding;
SAT_encoding_modes: SAT_array_var_int_element_result_encoding = fSAT_array_var_int_element_result_encoding default SAT_ORDER;

opt SAT_encoding_modes: fSAT_array_int_element_result_encoding;
SAT_encoding_modes: SAT_array_int_element_result_encoding = fSAT_array_int_element_result_encoding default SAT_array_var_int_element_result_encoding;
opt bool: f_SAT_fzn_disjunctive_half_reif;
bool: SAT_fzn_disjunctive_half_reif = f_SAT_fzn_disjunctive_half_reif default true;

opt bool: f_SAT_fzn_disjunctive_order_alternative;
bool: SAT_fzn_disjunctive_order_alternative = f_SAT_fzn_disjunctive_order_alternative default false;

array[int] of int: SAT_INT_EQUALITY_ENCODING_PREFS = [1,2,3];
array[int] of int: SAT_INT_INEQUALITY_ENCODING_PREFS = [2,1,3];
array[int] of int: SAT_ARRAY_INT_ELEMENT_INDEX_ENCODING_PREFS = [1,2,3]; % direct
array[int] of int: SAT_ARRAY_INT_ELEMENT_RESULT_ENCODING_PREFS = [3,1,2]; % binary

array[int] of int: SAT_ARRAY_VAR_INT_ELEMENT_INDEX_ENCODING_PREFS = SAT_ARRAY_INT_ELEMENT_INDEX_ENCODING_PREFS;
array[int] of int: SAT_ARRAY_VAR_INT_ELEMENT_RESULT_ENCODING_PREFS = SAT_ARRAY_INT_ELEMENT_RESULT_ENCODING_PREFS;
array[int] of int: SAT_ARRAY_VAR_INT_ELEMENT_ELEMENTS_ENCODING_PREFS= SAT_ARRAY_INT_ELEMENT_RESULT_ENCODING_PREFS;

opt bool: f_SAT_overrule_pbify;
bool: SAT_overrule_pbify = f_SAT_overrule_pbify default true;

enum SAT_array_int_element_methods = { DIRECT, GROUPWISE, COLUMNWISE };
opt SAT_array_int_element_methods: fSAT_array_int_element_method;
SAT_array_int_element_methods: SAT_array_int_element_method = fSAT_array_int_element_method default DIRECT;

opt bool: f_SAT_auto_resolve_view;
bool: SAT_auto_resolve_view = f_SAT_auto_resolve_view default true;

bool: SAT_strict = true;

opt bool: f_SAT_domain_aware_enc;
bool: SAT_domain_aware_enc = f_SAT_domain_aware_enc default true;
