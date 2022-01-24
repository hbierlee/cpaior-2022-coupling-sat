PBLIB_BIMANDER_M: SAT_PBLIB_BIMANDER_M_DEFAULT = N_SQRT;


enum PBLIB_AMO_ENCODER = { BIMANDER, PAIRWISE };
opt PBLIB_AMO_ENCODER: fSAT_pblib_amo_encoder;

PBLIB_AMO_ENCODER: SAT_PBLIB_AMO_ENCODER_DEFAULT = BIMANDER;

PBLIB_AMO_ENCODER: SAT_pblib_amo_encoder =
  if absent( fSAT_pblib_amo_encoder ) then
    SAT_PBLIB_AMO_ENCODER_DEFAULT
  else deopt( fSAT_pblib_amo_encoder ) endif;

enum PBLIB_BIMANDER_M = { % TODO why does N_BINARY conflict with BINARY from aux pattern?
  N_HALF, N_SQRT, FIXED, COMMANDER, N_BINARY, N_TRUNCATED
};

opt bool: fSAT_pblib_bimander_enforce_aux_var_domain;

bool: SAT_PBLIB_BIMANDER_ENFORCE_AUX_VAR_DOMAIN_DEFAULT = true;

bool: SAT_pblib_bimander_enforce_aux_var_domain =
  if absent( fSAT_pblib_bimander_enforce_aux_var_domain ) then
    SAT_PBLIB_BIMANDER_ENFORCE_AUX_VAR_DOMAIN_DEFAULT
  else deopt( fSAT_pblib_bimander_enforce_aux_var_domain ) endif;

opt PBLIB_BIMANDER_M: fSAT_pblib_bimander_m;

PBLIB_BIMANDER_M: SAT_pblib_bimander_m =
  if absent(fSAT_pblib_bimander_m) then
    SAT_PBLIB_BIMANDER_M_DEFAULT
  else deopt( fSAT_pblib_bimander_m ) endif;

enum PBLIB_BIMANDER_AUX_PATTERN = { BINARY, GRAY };

opt PBLIB_BIMANDER_AUX_PATTERN: fSAT_pblib_bimander_aux_pattern;

PBLIB_BIMANDER_AUX_PATTERN: SAT_PBLIB_BIMANDER_AUX_PATTERN_DEFAULT = BINARY;

PBLIB_BIMANDER_AUX_PATTERN: SAT_pblib_bimander_aux_pattern =
  if absent( fSAT_pblib_bimander_aux_pattern ) then
    SAT_PBLIB_BIMANDER_AUX_PATTERN_DEFAULT
  else deopt( fSAT_pblib_bimander_aux_pattern ) endif;

opt int: fSAT_pblib_bimander_fixed_offset;

int: SAT_PBLIB_BIMANDER_FIXED_OFFSET_DEFAULT = 0;

int: SAT_pblib_bimander_fixed_offset =
  if absent( fSAT_pblib_bimander_fixed_offset ) then
    SAT_PBLIB_BIMANDER_FIXED_OFFSET_DEFAULT
  else deopt( fSAT_pblib_bimander_fixed_offset ) endif;

