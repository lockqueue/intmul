import IntMulTM.Gate
import WP.W15.DynamicRange
import WP.W15.Recurrences
import WP.W15.PacketRouting
import WP.W15.Schedules
import WP.W15.LinearCircuits
import WP.W15.SyntheticDFT
import WP.W15.SyntheticDFTLowerBound

/-!
# WP.W15.Gate: G1 trust gate for the W15 package

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every W15 result holds only in an explicitly
defined restricted model (conserved-packet routing, bounded-coefficient linear circuits,
`⟨y⟩`-driven schedules), or is a counterexample to an omitted earlier-`[MS]`-draft barrier claim, or is an exact identity.

Module mode covers every constant of every `WP.W15.*` module. The declaration list holds the main
results per restricted-model topic (unsigned-slice range, `±1` entries, Floyd routing, recurrence telescoping, schedule depth, and Morgenstern's bound).
-/

#intmul_gate_modules WP.W15

#intmul_gate_check [
  -- Bit-slice dynamic range (refutations of omitted earlier-draft claims; exact ranges for unsigned slices)
  WP.W15.paper71_range_claim_false, WP.W15.paper71_sign_pattern_claim_false,
  WP.W15.paper71_width_claim_false, WP.W15.plusCount_eq_half, WP.W15.row_le, WP.W15.row_ge,
  WP.W15.row_attains_hi, WP.W15.row_attains_lo, WP.W15.row_abs_le_half,
  -- Matrix entries of M_B (refutation of omitted earlier-draft ±1 claim; exact entries)
  WP.W15.paper73_entries_claim_false, WP.W15.coeff_formula, WP.W15.row_nnz,
  -- Conserved-packet routing (Floyd with c registers, B67 embedding, witnesses, tightness)
  WP.W15.cReg_transpose_lower_bound, WP.W15.cReg_transpose_lower_bound_pow2,
  WP.W15.validTransposeTrace_to_cTrace, WP.W15.floyd_witness_two, WP.W15.floyd_witness_four,
  WP.W15.floyd_tight_two, WP.W15.floyd_tight_four, WP.W15.cTrace_witness_four,
  -- Prescribed recurrence (conditional telescoping, satisfiable and tight)
  WP.W15.telescoping_of_recurrence, WP.W15.satisfiesRec_closedForm, WP.W15.telescoping_tight,
  -- ⟨y⟩-driven schedules (refutation of omitted earlier-draft depth claim; admissibility and depth bound; snapshot schedule)
  WP.W15.paper75_depth_claim_false, WP.W15.tightK_extremal, WP.W15.YDrivenSchedule.admissible,
  WP.W15.YDrivenSchedule.depth_lower_bound, WP.W15.halving_depth_near_optimal,
  WP.W15.orderOf_snapshotTwiddle, WP.W15.paperStop_admissible,
  -- Morgenstern: model, determinant bound, non-vacuity
  WP.W15.LinSLP.norm_det_le_weight, WP.W15.LinSLP.norm_det_le_two_pow, WP.W15.LinSLP.exists_computes,
  -- G Gᵀ = t₁ I, det, and G = the snapshot's map
  WP.W15.synDFTMat_mul_transpose, WP.W15.synDFTMat_det_sq, WP.W15.synDFTMat_mulVec_eq_syntheticDFT,
  WP.W15.synDFTMat_mulVec_eq_syntheticFFTRadix2C, WP.W15.radixBMBOperatorInt_eq_synDFTMat,
  WP.W15.synDFTMatC_apply_eq_syntheticDFT, WP.W15.synDFTMatC_MB_apply,
  -- the factor-2 bounds
  WP.W15.synDFT_twoInputGates_lower_bound, WP.W15.synDFT_exists_circuit,
  WP.W15.MB_twoInputGates_lower_bound, WP.W15.syntheticDFT_twoInputGates_lower_bound,
  WP.W15.radixBMBOperatorInt_twoInputGates_lower_bound]
