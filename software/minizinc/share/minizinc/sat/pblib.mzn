enum PBlib_pb_encodings = { PB_BEST, PB_BDD, PB_SWC, PB_SORTINGNETWORKS, PB_ADDER, PB_BINARY_MERGE };
opt PBlib_pb_encodings: f_SAT_pb_encoder;
PBlib_pb_encodings: PBLIB_PB_DEFAULT = f_SAT_pb_encoder default PB_BEST;

enum PBlib_amk_encodings = { AMK_BEST, AMK_BDD, AMK_CARD };
opt PBlib_amk_encodings: f_SAT_amk_encoder;
PBlib_amk_encodings: PBLIB_AMK_DEFAULT = f_SAT_amk_encoder default AMK_BEST;

predicate pblib_bool_count_eq(array[int] of var bool: lits, int: k, PBlib_amk_encodings: enc);
predicate pblib_bool_count_eq(array[int] of var bool: lits, int: k) = pblib_bool_count_eq(lits,k,PBLIB_AMK_DEFAULT);
predicate pblib_bool_count_eq_impl(array[int] of var bool: lits, int: k, PBlib_amk_encodings:enc, var bool: r);
predicate pblib_bool_count_eq_impl(array[int] of var bool: lits, int: k, var bool: r) = pblib_bool_count_eq_impl(lits,k,PBLIB_AMK_DEFAULT,r);
predicate pblib_bool_count_ge(array[int] of var bool: lits, int: k, PBlib_amk_encodings: enc);
predicate pblib_bool_count_ge(array[int] of var bool: lits, int: k) = pblib_bool_count_ge(lits,k,PBLIB_AMK_DEFAULT);
predicate pblib_bool_count_ge_impl(array[int] of var bool: lits, int: k, PBlib_amk_encodings:enc, var bool: r);
predicate pblib_bool_count_ge_impl(array[int] of var bool: lits, int: k, var bool: r) = pblib_bool_count_ge_impl(lits,k,PBLIB_AMK_DEFAULT,r);
predicate pblib_bool_count_le(array[int] of var bool: lits, int: k, PBlib_amk_encodings: enc);
predicate pblib_bool_count_le(array[int] of var bool: lits, int: k) = pblib_bool_count_le(lits,k,PBLIB_AMK_DEFAULT);
predicate pblib_bool_count_le_impl(array[int] of var bool: lits, int: k, PBlib_amk_encodings:enc, var bool: r);
predicate pblib_bool_count_le_impl(array[int] of var bool: lits, int: k, var bool: r) = pblib_bool_count_le_impl(lits,k,PBLIB_AMK_DEFAULT,r);

% predicate pblib_bool_count_le_reif(array[int] of var bool: xs, int: k, var bool: r) =
%   (not build_sorting_network(xs, 0, k+1, SAT_cardinality_network_lambda)[k+1]) <-> r;
% predicate pblib_bool_count_ge(array[int] of var bool: xs, int: k, var bool: r) =
%   build_sorting_network(xs, 2, k, SAT_cardinality_network_lambda)[k] <-> r;
% predicate pblib_bool_count_eq_reif(array[int] of var bool: xs, int: k, var bool: r) =
%   let {
%     array[int] of var bool: xs_sorted = build_sorting_network(xs, 1, k+1, SAT_cardinality_network_lambda);
%   } in (xs_sorted[k] /\ not xs_sorted[k+1]) <-> r;

predicate pblib_bool_lin_eq(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc);
predicate pblib_bool_lin_eq(array[int] of int: as, array[int] of var bool: bs, int: c) = pblib_bool_lin_eq(as,bs,c,PBLIB_PB_DEFAULT);
predicate pblib_bool_lin_eq_impl(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc, var bool: r);
predicate pblib_bool_lin_eq_impl(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) = pblib_bool_lin_eq_impl(as,bs,c,PBLIB_PB_DEFAULT,r);
predicate pblib_bool_lin_eq_reif(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc, var bool: r);
predicate pblib_bool_lin_eq_reif(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) = pblib_bool_lin_eq_reif(as,bs,c,PBLIB_PB_DEFAULT,r);

predicate pblib_bool_lin_le(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc);
predicate pblib_bool_lin_le(array[int] of int: as, array[int] of var bool: bs, int: c) = pblib_bool_lin_le(as,bs,c,PBLIB_PB_DEFAULT);
predicate pblib_bool_lin_le_impl(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc, var bool: r);
predicate pblib_bool_lin_le_impl(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) = pblib_bool_lin_le_impl(as,bs,c,PBLIB_PB_DEFAULT,r);
predicate pblib_bool_lin_le_reif(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc, var bool: r);
predicate pblib_bool_lin_le_reif(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) = pblib_bool_lin_le_reif(as,bs,c,PBLIB_PB_DEFAULT,r);

predicate pblib_bool_lin_ge(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc);
predicate pblib_bool_lin_ge(array[int] of int: as, array[int] of var bool: bs, int: c) = pblib_bool_lin_ge(as,bs,c,PBLIB_PB_DEFAULT);
predicate pblib_bool_lin_ge_impl(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc, var bool: r);
predicate pblib_bool_lin_ge_impl(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) = pblib_bool_lin_ge_impl(as,bs,c,PBLIB_PB_DEFAULT,r);
predicate pblib_bool_lin_ge_reif(array[int] of int: as, array[int] of var bool: bs, int: c, PBlib_pb_encodings: enc, var bool: r);
predicate pblib_bool_lin_ge_reif(array[int] of int: as, array[int] of var bool: bs, int: c, var bool: r) = pblib_bool_lin_ge_reif(as,bs,c,PBLIB_PB_DEFAULT,r);

predicate pblib_bool_at_most_one(
  array[int] of var bool: lits) = pblib_bool_at_most_one(lits, <>);

predicate pblib_bool_at_most_one(
  array[int] of var bool: lits,
  opt PBLIB_AMO_ENCODER: pblib_amo_encoder_opt) =
  pblib_bool_at_most_one(lits, if occurs(pblib_amo_encoder_opt) then deopt(pblib_amo_encoder_opt) else SAT_pblib_amo_encoder endif);

predicate pblib_bool_at_most_one(
  array[int] of var bool: lits,
  PBLIB_AMO_ENCODER: pblib_amo_encoder) =
  if pblib_amo_encoder == PAIRWISE then
    pblib_bool_at_most_one_pairwise(lits)
  elseif pblib_amo_encoder == BIMANDER then
    pblib_bool_at_most_one_bimander(lits)
  else
    abort("Shouldn't happen")
  endif;

predicate pblib_bool_at_most_one_bimander(array[int] of var bool: lits) =
  pblib_bool_at_most_one_bimander(lits, <>, <>, <>, <>);

predicate pblib_bool_at_most_one_pairwise(array[int] of var bool: lits);

predicate pblib_bool_at_most_one_bimander(
  array[int] of var bool: lits,
  opt int: m_opt,
  opt int: offset_opt,
  opt PBLIB_BIMANDER_AUX_PATTERN: pattern_opt,
  opt bool: enforce_aux_var_domain_opt,
  ) =
    let {
      constraint abort("deprecated");
      int: n = length(lits);
      int: m =
        if occurs(m_opt) then
          deopt(m_opt)
        else
          if SAT_pblib_bimander_m == N_BINARY then
            n
          elseif SAT_pblib_bimander_m == N_HALF then
            ceil(n / 2)
          elseif SAT_pblib_bimander_m == N_SQRT then
            ceil(sqrt(n))
          elseif SAT_pblib_bimander_m == N_TRUNCATED then
            2^floor(log2(n)) % truncate smallest group
          elseif SAT_pblib_bimander_m == COMMANDER then
            2
          else
            abort("Shouldn't happen")
          endif
        endif;

      constraint assert(m in 0..n, "The bimander m parameter should be in the range of \(-1..n), but was \(m)");

      int: max_offset = 2^(ceil(log2(m))-1) - ceil(m/2);
      int: offset_tmp =
        if occurs(offset_opt) then
          deopt(offset_opt)
        else
          SAT_pblib_bimander_fixed_offset
        endif;
      int: offset = if offset_tmp == -1 then max_offset else offset_tmp endif;

      constraint assert(offset in {-2} union 0..max_offset, "The offset should be -2 (for spread) or in the range of \(0..max_offset) for m=\(m) groups, but was \(offset)");

      PBLIB_BIMANDER_AUX_PATTERN: pattern =
        if occurs(pattern_opt) then
          deopt(pattern_opt)
        else
          SAT_pblib_bimander_aux_pattern
        endif;

      bool: enforce_aux_var_domain =
        if occurs(enforce_aux_var_domain_opt) then
          deopt(enforce_aux_var_domain_opt)
        else
          SAT_pblib_bimander_enforce_aux_var_domain
        endif;
      } in pblib_bool_at_most_one_bimander(lits, m, offset, pattern, enforce_aux_var_domain);

predicate pblib_bool_at_most_one_bimander(array[int] of var bool: lits, int: m, int: offset, PBLIB_BIMANDER_AUX_PATTERN: pattern, bool: enforce_aux_var_domain);
