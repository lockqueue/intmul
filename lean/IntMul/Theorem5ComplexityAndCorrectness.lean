import IntMul.Preliminaries
import IntMul.Theorem3BidiagonalAndSchedule

/-!
# `[MS]` Section 7: Theorem 1 — Root Precision, Exact Rounding & Complexity Recurrence Arithmetic

This module is part of our independent formalization of the recurrence and rounding identities
of `[MS]` Section 7 (`[MS]` Theorem 1, §7.2; companion manuscript `[MS]`,
*Integer multiplication in O(n log n) time on a single two-dimensional grid, with a machine-checked proof*):

1. **Tightened Root Precision `p_0 = 2 b + 2 K_0 + 6` & Exact Integer Recovery (`[MS]` §7.2, proof of Theorem 1, Part 1)**:
   - With `p_0 = 2 b + 2 K_0 + 6`, forward `FastDFT` error `≤ 2 * 2^{-p_0}`, pointwise squaring
     error `≤ 6 * 2^{-p_0}`, and inverse `FastDFT` error `≤ 2 * 2^{-p_0}` combine to `8 * 2^{-p_0}`.
   - Scaling by `2^{2 b - 1} R_0^2 = 2^{2 b + 2 K_0 - 1}` yields an integer convolution error bound
     of `8 * 2^{2 b + 2 K_0 - 1 - p_0} = 2^{-4} = 1 / 16 < 1 / 2`.
   - **Exact Rounding Theorem (`round_nearest_int_exact`)**: whenever `|C̃ - C| < 1 / 2` for `C ∈ ℤ`,
     `⌊C̃ + 1 / 2⌋ = C` recovers the integer convolution coefficient **100% bit-for-bit exactly**.
2. **Additive Precision Telescoping Across All `L ≤ log_2 log_2 n` Levels (`[MS]` §7.2, proof of Theorem 1, Part 1)**:
   - Closed-form recurrence solution:
     `levelPrecision p0 K ℓ = p0 + 2 * (∑ j ∈ range ℓ, K j) + 12 * ℓ`.
   - Uniform bound `levelPrecision p0 K ℓ ≤ p0 + 4 * K_0 + 12 * ℓ = Θ(log n)`.
3. **`(1/2)^ℓ` Geometric Contraction of Synthetic FFT & Routing Work (`[MS]` §7.2, proof of Theorem 1, Part 2)**:
   - Exact geometric series identity:
     `∑_{ℓ=0}^{L-1} (1 / 2)^ℓ = 2 * (1 - (1 / 2)^L) ≤ 2`
     (contrasted with `(5 / 8)^ℓ` summing to `(8 / 3) * (1 - (5 / 8)^L) ≤ 8 / 3` for the Plain-Gaussian
     schedule).
4. **`[MS]` Theorem 1 (`theorem5_end_to_end_complexity_bound`, §7.2, Part 3; historical `theorem5_*` identifier retained)**:
   - Combining the `O(n log n)` Synthetic FFT + Turing-machine routing work with the `L` levels of
     `O(n log log n)` secondary overhead and `O(n (log log n)^2)` leaf base cases yields
     `C_mul(n) = O(n log n) + O(n (log log n)^2)`.
-/

namespace IntMul

open scoped BigOperators
open Real Asymptotics Filter

/-! ## 1. Tightened Root Precision `p_0 = 2 b + 2 K_0 + 6` & Exact Integer Recovery (`[MS]` §§7.1–7.2) -/

/-- Tightened root precision `p_0 = 2 b + 2 K_0 + 6` for 2-call normalized complex packing (`[MS]` §7.1, Listing 1). -/
def rootPrecision (b K0 : ℕ) : ℕ :=
  2 * b + 2 * K0 + 6

/-- Pointwise complex squaring error propagation:
if `‖y - w‖ ≤ ε` with `‖w‖ ≤ W` and `ε ≤ E`, then `‖y^2 - w^2‖ ≤ (2 W + E) * ε`.
In particular, at the root where `W ≤ √2 < 2` and `2 W + E ≤ 3`, `ε ≤ 2 * 2^{-p_0}` gives
`‖y^2 - w^2‖ ≤ 6 * 2^{-p_0}`. -/
theorem complex_square_error_bound (y w : ℂ) (ε W E : ℝ)
    (h_err : ‖y - w‖ ≤ ε) (h_w : ‖w‖ ≤ W) (h_ε : ε ≤ E) :
    ‖y ^ 2 - w ^ 2‖ ≤ (2 * W + E) * ε := by
  have h_fact : y ^ 2 - w ^ 2 = (y + w) * (y - w) := by ring
  have h_sum_eq : y + w = (y - w) + 2 * w := by ring
  have h_sum_norm : ‖y + w‖ ≤ 2 * W + E := by
    rw [h_sum_eq]
    calc ‖(y - w) + 2 * w‖
        ≤ ‖y - w‖ + ‖(2 : ℂ) * w‖ := norm_add_le _ _
      _ = ‖y - w‖ + 2 * ‖w‖ := by rw [norm_mul, RCLike.norm_ofNat]
      _ ≤ E + 2 * W := add_le_add (h_err.trans h_ε) (mul_le_mul_of_nonneg_left h_w (by norm_num))
      _ = 2 * W + E := by ring
  rw [h_fact, norm_mul]
  exact mul_le_mul h_sum_norm h_err (norm_nonneg _) (by linarith [norm_nonneg (y + w)])

/-- **`[MS]` Theorem 1 (Part 1a: Root Convolution Error `< 2^{-4} < 1 / 2`, `[MS]` §7.2)**:
With `p_0 = rootPrecision b K_0 = 2 b + 2 K_0 + 6`, multiplying the `8 * 2^{-p_0}` inverse DFT
output error by `2^{2 b - 1} R_0^2 = 2^{2 b + 2 K_0 - 1}` yields an integer recovery error of
`8 * 2^{2 b + 2 K_0 - 1 - p_0} = 2^{-4} = 1 / 16 < 1 / 2`. -/
theorem theorem5_root_recovery_error_lt_half (b K0 : ℕ) :
    (8 : ℝ) * (2 : ℝ) ^ ((2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) - (rootPrecision b K0 : ℤ)) =
      (1 / 16 : ℝ) ∧
    (1 / 16 : ℝ) < (1 / 2 : ℝ) := by
  unfold rootPrecision
  have hexp : (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) - ((2 * b + 2 * K0 + 6 : ℕ) : ℤ) = (-7 : ℤ) := by
    push_cast
    omega
  rw [hexp]
  constructor <;> norm_num

/-- **`[MS]` Theorem 1 (Part 1b: 100% Exact Integer Recovery upon Nearest-Integer Rounding)**:
For any exact convolution integer `C ∈ ℤ` and any real approximation `C_approx ∈ ℝ`,
if `|C_approx - C| < 1 / 2`, then rounding to the nearest integer `⌊C_approx + 1 / 2⌋` returns
`C` **identically**. -/
theorem theorem5_round_nearest_int_exact (C : ℤ) (C_approx : ℝ)
    (herr : |C_approx - (C : ℝ)| < (1 / 2 : ℝ)) :
    ⌊C_approx + (1 / 2 : ℝ)⌋ = C := by
  rw [abs_lt] at herr
  rw [Int.floor_eq_iff]
  constructor <;> linarith

/-- **`[MS]` Theorem 1 (Part 1c: Composition of Per-Stage Error Hypotheses (`hy`, `hS`, `hinv`) into
`< 5 * 2^{-p_0}` Squaring Error and `< 8 * 2^{-p_0}` Root Pipeline Error, `[MS]` §7.2)**:
At the root level (`p_0 ≥ 6`), composing the per-stage error hypotheses:
- the true forward DFT mode `w : ℂ` of the packed input satisfies `‖w‖ ≤ √2` (`hw`),
- the approximate forward DFT output `y : ℂ` satisfies `‖y - w‖ ≤ √2 * 2^{-p_0}` (`hy`),
- the quantized pointwise square `S_tilde : ℂ` satisfies `‖S_tilde - y ^ 2‖ ≤ complexQuantizeMaxErr p0` (`hS`), and
- the approximate inverse DFT error `err_inv : ℝ` satisfies `err_inv ≤ ‖S_tilde - w ^ 2‖ + 3 * 2^{-p_0}` (`hinv`),
yields `‖S_tilde - w ^ 2‖ < 5 * 2^{-p_0}` and `err_inv < 8 * 2^{-p_0}`. -/
theorem theorem5_root_squaring_and_pipeline_error_lt_eight_ulp
    (p0 : ℕ) (hp0 : 6 ≤ p0) (w y S_tilde : ℂ) (err_inv : ℝ)
    (hw : ‖w‖ ≤ Real.sqrt 2)
    (hy : ‖y - w‖ ≤ Real.sqrt 2 * (2 : ℝ) ^ (-(p0 : ℤ)))
    (hS : ‖S_tilde - y ^ 2‖ ≤ complexQuantizeMaxErr p0)
    (hinv : err_inv ≤ ‖S_tilde - w ^ 2‖ + 3 * (2 : ℝ) ^ (-(p0 : ℤ))) :
    ‖S_tilde - w ^ 2‖ < 5 * (2 : ℝ) ^ (-(p0 : ℤ)) ∧
    err_inv < 8 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
  have hp0_zpow : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (2 : ℝ) ^ (-6 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hε_le : Real.sqrt 2 * (2 : ℝ) ^ (-(p0 : ℤ)) ≤ Real.sqrt 2 * (2 : ℝ) ^ (-6 : ℤ) :=
    mul_le_mul_of_nonneg_left hp0_zpow (Real.sqrt_nonneg 2)
  have hsq_err := complex_square_error_bound y w
    (Real.sqrt 2 * (2 : ℝ) ^ (-(p0 : ℤ))) (Real.sqrt 2) (Real.sqrt 2 * (2 : ℝ) ^ (-6 : ℤ))
    hy hw hε_le
  have h2_6 : (2 : ℝ) ^ (-6 : ℤ) = (1 / 64 : ℝ) := by norm_num
  have hsq_simp :
      (2 * Real.sqrt 2 + Real.sqrt 2 * (2 : ℝ) ^ (-6 : ℤ)) *
        (Real.sqrt 2 * (2 : ℝ) ^ (-(p0 : ℤ))) =
      (4 + 1 / 32 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    calc (2 * Real.sqrt 2 + Real.sqrt 2 * (2 : ℝ) ^ (-6 : ℤ)) *
          (Real.sqrt 2 * (2 : ℝ) ^ (-(p0 : ℤ)))
        = (2 + (2 : ℝ) ^ (-6 : ℤ)) * (Real.sqrt 2 ^ 2) * (2 : ℝ) ^ (-(p0 : ℤ)) := by ring
      _ = (2 + (2 : ℝ) ^ (-6 : ℤ)) * 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (4 + 1 / 32 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
          rw [h2_6]
          ring
  rw [hsq_simp] at hsq_err
  have hS_lt : ‖S_tilde - y ^ 2‖ < (0.354 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) :=
    hS.trans_lt (complexQuantizeMaxErr_lt p0)
  have htri : ‖S_tilde - w ^ 2‖ ≤ ‖S_tilde - y ^ 2‖ + ‖y ^ 2 - w ^ 2‖ := by
    have hsplit : S_tilde - w ^ 2 = (S_tilde - y ^ 2) + (y ^ 2 - w ^ 2) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p0 : ℤ)) := zpow_pos (by norm_num) _
  have hS_w : ‖S_tilde - w ^ 2‖ < 5 * (2 : ℝ) ^ (-(p0 : ℤ)) := by linarith
  refine ⟨hS_w, ?_⟩
  linarith

/-- **`[MS]` Theorem 1 (Part 1d: Root Pipeline Exact Integer Recovery Under Per-Stage Error Hypotheses, `[MS]` §7.2)**:
At `p_0 = rootPrecision b K0 = 2 b + 2 K_0 + 6`, composing the per-stage error hypotheses (`hw`, `hy`,
`hS`, `hinv`) of `theorem5_root_squaring_and_pipeline_error_lt_eight_ulp` with the scaled real
convolution estimate hypothesis `|C_approx - (C : ℝ)| ≤ err_inv * 2^{2 b + 2 K_0 - 1}` (`hC`)
shows that nearest-integer rounding recovers `⌊C_approx + 1 / 2⌋ = C`
exactly, given the per-stage error hypotheses. -/
theorem theorem5_root_pipeline_exact_int_recovery
    (b K0 : ℕ) (w y S_tilde : ℂ) (err_inv C_approx : ℝ) (C : ℤ)
    (hw : ‖w‖ ≤ Real.sqrt 2)
    (hy : ‖y - w‖ ≤ Real.sqrt 2 * (2 : ℝ) ^ (-(rootPrecision b K0 : ℤ)))
    (hS : ‖S_tilde - y ^ 2‖ ≤ complexQuantizeMaxErr (rootPrecision b K0))
    (hinv : err_inv ≤ ‖S_tilde - w ^ 2‖ + 3 * (2 : ℝ) ^ (-(rootPrecision b K0 : ℤ)))
    (hC : |C_approx - (C : ℝ)| ≤ err_inv * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)) :
    ⌊C_approx + (1 / 2 : ℝ)⌋ = C := by
  have hp0 : 6 ≤ rootPrecision b K0 := by
    unfold rootPrecision
    omega
  have herr_inv : err_inv < 8 * (2 : ℝ) ^ (-(rootPrecision b K0 : ℤ)) :=
    (theorem5_root_squaring_and_pipeline_error_lt_eight_ulp
      (rootPrecision b K0) hp0 w y S_tilde err_inv hw hy hS hinv).2
  have hscale_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) :=
    zpow_pos (by norm_num) _
  have hmul_lt :
      err_inv * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) <
        (8 : ℝ) * (2 : ℝ) ^ ((2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) - (rootPrecision b K0 : ℤ)) := by
    calc err_inv * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)
        < (8 * (2 : ℝ) ^ (-(rootPrecision b K0 : ℤ))) *
            (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) :=
          mul_lt_mul_of_pos_right herr_inv hscale_pos
      _ = (8 : ℝ) * ((2 : ℝ) ^ (-(rootPrecision b K0 : ℤ)) *
            (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)) := by ring
      _ = (8 : ℝ) * (2 : ℝ) ^ ((2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) - (rootPrecision b K0 : ℤ)) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 2
          ring
  have hrec := theorem5_root_recovery_error_lt_half b K0
  have hC_lt : |C_approx - (C : ℝ)| < (1 / 2 : ℝ) := by
    linarith [hC, hmul_lt, hrec.1, hrec.2]
  exact theorem5_round_nearest_int_exact C C_approx hC_lt

/-- Helper: for `2 ≤ K` and `t1 ≤ 2 ^ (K / 2)`, multiplying `2.36 * t_1` by `0.15 * 2^{-pWork p K}`
is strictly `< 0.003 * 2^{-p}`. -/
theorem lemma2_termA_conditioning_mul_zpow_lt
    (p K t1 : ℕ) (hK : 2 ≤ K) (ht1 : t1 ≤ 2 ^ (K / 2)) :
    (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ))) <
      (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have ht1_real : (t1 : ℝ) ≤ (2 : ℝ) ^ ((K / 2 : ℕ) : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast ht1
  have hexp_le : ((K / 2 : ℕ) : ℤ) + (-(pWork p K : ℤ)) ≤ (-7 : ℤ) + (-(p : ℤ)) := by
    unfold pWork
    omega
  have hzpow_work_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-(pWork p K : ℤ)) := zpow_nonneg (by norm_num) _
  have ht1_zpow_le :
      (t1 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) ≤ (1 / 128 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (t1 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ))
        ≤ (2 : ℝ) ^ ((K / 2 : ℕ) : ℤ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) :=
          mul_le_mul_of_nonneg_right ht1_real hzpow_work_nonneg
      _ = (2 : ℝ) ^ (((K / 2 : ℕ) : ℤ) + (-(pWork p K : ℤ))) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ (2 : ℝ) ^ ((-7 : ℤ) + (-(p : ℤ))) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp_le
      _ = (2 : ℝ) ^ (-7 : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (-7 : ℤ) (-(p : ℤ))
      _ = (1 / 128 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
          have h2_7 : (2 : ℝ) ^ (-7 : ℤ) = (1 / 128 : ℝ) := by norm_num
          rw [h2_7]
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  linarith

/-- **`[MS]` Lemma 6.5 (Term A Stopband Error Bound Composing `theorem3_stopband_alias_bound_alphaSchedule`
and the `2.36 * t_1` Conditioning Factor, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
For `K ≥ 2`, `t_1 ≤ 2^{K / 2}`, and `p ≥ 8` (so `8 ≤ pWork p K`), at `α = alphaSchedule (pWork p K)`
and any `y ∈ [0, 1]`, composing the stopband alias bound `theorem3_stopband_alias_bound_alphaSchedule`
with the bidiagonal conditioning factor `2.36 * t_1` yields strictly:
`2.36 * t_1 * (1 - c0Coeff (realErfScaled (alphaSchedule (pWork p K))) y -
  c1Coeff (realErfScaled (alphaSchedule (pWork p K))) y) < (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))`. -/
theorem lemma2_termA_stopband_error_bound
    (p K t1 : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1 : t1 ≤ 2 ^ (K / 2))
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (2.36 : ℝ) * (t1 : ℝ) *
      (1 - c0Coeff (realErfScaled (alphaSchedule (pWork p K))) y -
        c1Coeff (realErfScaled (alphaSchedule (pWork p K))) y) <
      (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have hp_work : 8 ≤ pWork p K := by
    unfold pWork
    omega
  have hstop := theorem3_stopband_alias_bound_alphaSchedule (pWork p K) hp_work y hy0 hy1
  have h236_t1_nonneg : (0 : ℝ) ≤ (2.36 : ℝ) * (t1 : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg t1)
  have hmul_le :
      (2.36 : ℝ) * (t1 : ℝ) *
        (1 - c0Coeff (realErfScaled (alphaSchedule (pWork p K))) y -
          c1Coeff (realErfScaled (alphaSchedule (pWork p K))) y) ≤
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ))) :=
    mul_le_mul_of_nonneg_left hstop.le h236_t1_nonneg
  exact hmul_le.trans_lt (lemma2_termA_conditioning_mul_zpow_lt p K t1 hK ht1)

/-- **`[MS]` Lemma 6.5 (Inductive Error Closure Discharging Term A via `lemma2_termA_stopband_error_bound`, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
For `p ≥ 8`, `K ≥ 2`, `t_1 ≤ 2^{K / 2}`, `y ∈ [0, 1]`, and `M > 0`, if Term A's stopband error satisfies
`err_A ≤ 2.36 * t_1 * (1 - c0Coeff (realErfScaled (alphaSchedule (pWork p K))) y -
  c1Coeff (realErfScaled (alphaSchedule (pWork p K))) y) * M`,
then `lemma2_termA_stopband_error_bound` automatically discharges the `hA` hypothesis of
`lemma2_inductive_error_closure`, proving
`err_A + err_BCD + err_quant < 0.394 * 2^{-p} * M < 2^{-p} * M`. -/
theorem lemma2_inductive_error_closure_with_stopband
    (p K t1 : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1 : t1 ≤ 2 ^ (K / 2))
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (M err_A err_BCD err_quant : ℝ) (hM : 0 < M)
    (hA_stop : err_A ≤ (2.36 : ℝ) * (t1 : ℝ) *
      (1 - c0Coeff (realErfScaled (alphaSchedule (pWork p K))) y -
        c1Coeff (realErfScaled (alphaSchedule (pWork p K))) y) * M)
    (hBCD : err_BCD ≤ (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M)
    (hQ : err_quant ≤ complexQuantizeMaxErr p * M) :
    err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hstop := mul_lt_mul_of_pos_right
    (lemma2_termA_stopband_error_bound p K t1 hp hK ht1 y hy0 hy1) hM
  exact lemma2_inductive_error_closure p M err_A err_BCD err_quant hM
    (hA_stop.trans hstop.le) hBCD hQ

/-- **`[MS]` Lemma 6.5 (End-to-End Term A Sinc-Gaussian 2D-DFT + Bidiagonal Deconvolution Error `< 0.003 * 2^{-p} * B_X`, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
For `p ≥ 8`, `K ≥ 2`, `0 < t1 ≤ 2 ^ (K / 2)`, `0 < r`, `0 < B_X`, and `∀ k < t1 * r, ‖x k‖ ≤ B_X`,
at `p_work = pWork p K = p + K + 6`, both the forward bidiagonal deconvolution (`2 * u2 < r`) and
the backward bidiagonal deconvolution (`r < 2 * u2` and `u2 < r`) of the 2D DFT of
`sincGaussianSpreadArray` recover the exact 1D DFT mode `dft1DGrid t1 r x u2 u1` (`u1 < t1`)
with error strictly `< (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X`. -/
theorem lemma2_termA_sincGaussian_deconv_error_lt
    (p K t1 r u1 u2 : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1_pos : 0 < t1) (ht1 : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 < B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (hu1 : u1 < t1) :
    (2 * u2 < r →
      (c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) /
        c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ))) ^ t1 ≤ (0.15 : ℝ) →
      ‖solveBidiagonalFwd t1
          (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
          u1 -
        dft1DGrid t1 r x u2 u1‖ <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X) ∧
    (r < 2 * u2 → u2 < r →
      (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) /
        c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ))) ^ t1 ≤ (0.15 : ℝ) →
      ‖solveBidiagonalBwd t1
          (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
          u1 -
        dft1DGrid t1 r x u2 u1‖ <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X) := by
  have hp_work : 8 ≤ pWork p K := by
    unfold pWork
    omega
  have hlt :
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * B_X) <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X := by
    have h1 := mul_lt_mul_of_pos_right (lemma2_termA_conditioning_mul_zpow_lt p K t1 hK ht1) hB
    linarith
  refine ⟨fun hu2_half hratio => ?_, fun hu2_half hu2 hratio => ?_⟩
  · exact (solveBidiagonalFwd_sincGaussian_dft2D_error_le
      (pWork p K) t1 r u1 u2 hp_work ht1_pos hr hu2_half hratio x B_X hB.le hx hu1).trans_lt hlt
  · exact (solveBidiagonalBwd_sincGaussian_dft2D_error_le
      (pWork p K) t1 r u1 u2 hp_work ht1_pos hr hu2_half hu2 hratio x B_X hB.le hx hu1).trans_lt hlt

/-- **`[MS]` Lemma 6.5 (Unconditional End-to-End Term A Sinc-Gaussian 2D-DFT + Bidiagonal Deconvolution Error `< 0.003 * 2^{-p} * B_X` for Balanced Splits `r ≤ 2 * t1`, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
For `p ≥ 8`, `K ≥ 2`, `0 < t1 ≤ 2 ^ (K / 2)`, `0 < r ≤ 2 * t1`, `0 < B_X`, and `∀ k < t1 * r, ‖x k‖ ≤ B_X`,
`c1_div_c0_pow_le_015_of_balanced` and `c0_div_c1_pow_le_015_of_balanced` automatically discharge the
wrap-around ratio hypothesis `hratio ≤ 0.15`, proving unconditionally that both the forward bidiagonal
deconvolution (`2 * u2 < r`) and backward bidiagonal deconvolution (`r < 2 * u2` and `u2 < r`) of the
2D DFT of `sincGaussianSpreadArray` recover `dft1DGrid t1 r x u2 u1` (`u1 < t1`) with error strictly
`< (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X`. -/
theorem lemma2_termA_sincGaussian_deconv_error_lt_of_balanced
    (p K t1 r u1 u2 : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1_pos : 0 < t1) (ht1 : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (hr_le : r ≤ 2 * t1)
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 < B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (hu1 : u1 < t1) :
    (2 * u2 < r →
      ‖solveBidiagonalFwd t1
          (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
          u1 -
        dft1DGrid t1 r x u2 u1‖ <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X) ∧
    (r < 2 * u2 → u2 < r →
      ‖solveBidiagonalBwd t1
          (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
          u1 -
        dft1DGrid t1 r x u2 u1‖ <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X) := by
  have hp_work : 8 ≤ pWork p K := by
    unfold pWork
    omega
  have hdeconv := lemma2_termA_sincGaussian_deconv_error_lt p K t1 r u1 u2
    (by omega) hK ht1_pos ht1 hr x B_X hB hx hu1
  refine ⟨fun hu2_half => hdeconv.1 hu2_half
    (c1_div_c0_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1_pos hr hr_le hu2_half),
    fun hu2_half hu2 => hdeconv.2 hu2_half hu2
    (c0_div_c1_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1_pos hr hr_le hu2_half hu2)⟩

/-- **`[MS]` Lemma 6.5 (Unconditional End-to-End Term A Sinc-Gaussian 2D-DFT + Nyquist Deconvolution Error `< 0.003 * 2^{-p} * B_X` at `2 * u_2 = r`, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
For `p ≥ 8`, `K ≥ 2`, `0 < t1 ≤ 2 ^ (K / 2)`, `0 < r`, `2 * u2 = r`, `0 < B_X`, and `∀ k < t1 * r, ‖x k‖ ≤ B_X`,
at `p_work = pWork p K = p + K + 6`, applying `solveNyquist` with exact alternating sum `alt_true`
to the 2D DFT of `sincGaussianSpreadArray` recovers `dft1DGrid t1 r x u2 u1` (`u1 < t1`) with error
strictly `< (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X`. -/
theorem lemma2_termA_sincGaussian_nyquist_deconv_error_lt
    (p K t1 r u1 u2 : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1_pos : 0 < t1) (ht1 : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (hu2_nyq : 2 * u2 = r)
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 < B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (alt_true : ℂ)
    (h_alt : alt_true = ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * dft1DGrid t1 r x u2 v)
    (hu1 : u1 < t1) :
    ‖solveNyquist t1
        (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
        (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
        alt_true u1 -
      dft1DGrid t1 r x u2 u1‖ <
      (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X := by
  have hp_work : 8 ≤ pWork p K := by
    unfold pWork
    omega
  have hlt :
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * B_X) <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X := by
    have h1 := mul_lt_mul_of_pos_right (lemma2_termA_conditioning_mul_zpow_lt p K t1 hK ht1) hB
    linarith
  exact (solveNyquist_sincGaussian_dft2D_error_le
    (pWork p K) t1 r u1 u2 hp_work ht1_pos hr hu2_nyq x B_X hB.le hx alt_true h_alt hu1).trans_lt hlt

/-- **`[MS]` Lemma 6.5 (Complete 3-Regime Unconditional Term A Sinc-Gaussian 2D-DFT Deconvolution Error `< 0.003 * 2^{-p} * B_X` for Balanced Splits `r ≤ 2 * t1`, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
For `p ≥ 8`, `K ≥ 2`, `0 < t1 ≤ 2 ^ (K / 2)`, `0 < r ≤ 2 * t1`, `0 < B_X`, and `∀ k < t1 * r, ‖x k‖ ≤ B_X`,
across all three column frequency regimes (`2 * u2 < r`, `2 * u2 = r`, and `r < 2 * u2 < 2 * r`),
the corresponding `[MS]` Theorem 5.1 (§5.1) solver (`solveBidiagonalFwd`, `solveNyquist`, or `solveBidiagonalBwd`)
applied to the 2D DFT of `sincGaussianSpreadArray` recovers `dft1DGrid t1 r x u2 u1` (`u1 < t1`)
with error strictly `< (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X`. -/
theorem lemma2_termA_sincGaussian_all_regimes_deconv_error_lt_of_balanced
    (p K t1 r u1 u2 : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1_pos : 0 < t1) (ht1 : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (hr_le : r ≤ 2 * t1)
    (x : ℕ → ℂ) (B_X : ℝ) (hB : 0 < B_X) (hx : ∀ k < t1 * r, ‖x k‖ ≤ B_X)
    (alt_true : ℂ)
    (h_alt : alt_true = ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * dft1DGrid t1 r x u2 v)
    (hu1 : u1 < t1) :
    (2 * u2 < r →
      ‖solveBidiagonalFwd t1
          (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
          u1 -
        dft1DGrid t1 r x u2 u1‖ <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X) ∧
    (2 * u2 = r →
      ‖solveNyquist t1
          (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
          alt_true u1 -
        dft1DGrid t1 r x u2 u1‖ <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X) ∧
    (r < 2 * u2 → u2 < r →
      ‖solveBidiagonalBwd t1
          (c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) : ℂ)
          (fun k => dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
          u1 -
        dft1DGrid t1 r x u2 u1‖ <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * B_X) := by
  have hbal := lemma2_termA_sincGaussian_deconv_error_lt_of_balanced
    p K t1 r u1 u2 hp hK ht1_pos ht1 hr hr_le x B_X hB hx hu1
  refine ⟨hbal.1, fun hu2_nyq =>
    lemma2_termA_sincGaussian_nyquist_deconv_error_lt
      p K t1 r u1 u2 (by omega) hK ht1_pos ht1 hr hu2_nyq x B_X hB hx alt_true h_alt hu1,
    hbal.2⟩

/-- **`[MS]` Lemma 6.5 (Full Four-Source Inductive Error Closure Composing Stopband Term A and Component Terms B1–D, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
Combines `lemma2_termA_stopband_error_bound` (for Term A) and `lemma2_inductive_error_closure_from_components`
(for Terms B1 via `lemma2_sincGaussian_spatial_tail_bound`, B2, B3 via `lemma1_synthetic_fft_rounding_bound`,
C, and D via `lemma2_termBCD_error_bound`, plus final quantization via `complexQuantizeMaxErr_lt`) into a
single end-to-end inductive error closure theorem. -/
theorem lemma2_inductive_error_closure_with_stopband_and_components
    (p K t1 k1 m1 W_eff : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1 : t1 ≤ 2 ^ (K / 2))
    (hk1 : 2 * k1 ≤ K)
    (y α δ log_alpha_term M err_A err_B1 err_B2 err_B3 err_C err_D err_BCD err_quant : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hM : 0 < M)
    (hα : 0 < α) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm1 : 8 ≤ m1)
    (h_win : (pChild p K : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / α ^ 2)
    (h_step : (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / α ^ 2)
    (hW : t1 * W_eff ≤ 2 ^ K)
    (h_sub : (t1 : ℝ) * (log_alpha_term + (0.18 : ℝ) * (K : ℝ) + 7) ≤ (15 / 2 : ℝ) * (2 : ℝ) ^ K)
    (hA_stop : err_A ≤ (2.36 : ℝ) * (t1 : ℝ) *
      (1 - c0Coeff (realErfScaled (alphaSchedule (pWork p K))) y -
        c1Coeff (realErfScaled (alphaSchedule (pWork p K))) y) * M)
    (hB1 : err_B1 ≤
      ((∑' k : ℕ, |sincGaussian α ((m1 + 1 + k : ℝ) - δ)|) +
        (∑' k : ℕ, |sincGaussian α (-((m1 + 1 + k : ℝ)) - δ)|)) * M)
    (hB2 : err_B2 ≤ ((1 / 2 : ℝ) * (W_eff : ℝ) + (5.22 : ℝ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hB3 : err_B3 ≤ (k1 : ℝ) * complexQuantizeMaxErr (pChild p K) * M)
    (hC : err_C ≤ log_alpha_term * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hD : err_D ≤ (1.38 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hBCD_amp : err_BCD ≤ (2.36 : ℝ) * (t1 : ℝ) * (err_B1 + err_B2 + err_B3 + err_C + err_D))
    (hQ : err_quant ≤ complexQuantizeMaxErr p * M) :
    err_BCD < (0.037 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hstop := mul_lt_mul_of_pos_right
    (lemma2_termA_stopband_error_bound p K t1 hp hK ht1 y hy0 hy1) hM
  exact lemma2_inductive_error_closure_from_components
    p K t1 k1 m1 W_eff α δ log_alpha_term M err_A err_B1 err_B2 err_B3 err_C err_D err_BCD err_quant
    hK hM hk1 hα hδ0 hδ1 hm1 h_win h_step hW h_sub (hA_stop.trans hstop.le)
    hB1 hB2 hB3 hC hD hBCD_amp hQ

/-- **`[MS]` Lemma 6.5 (Unconditional End-to-End Precision-Schedule Closure with Stopband Term A for All `p ≥ 8`, `K ≥ 2`, `t1 * r = 2 ^ K` — Zero `hW` or `h_sub` Hypotheses, `[MS]` §6.3, Lemma 6.5, eqs. (35)–(36))**:
Composes `lemma2_termA_stopband_error_bound` (discharging Term A from the exact stopband alias sum
`1 - c0Coeff - c1Coeff`) with `lemma2_precision_schedule_closure` (discharging the spatial window
rules `h_win`, `h_step` and Term B1 via `lemma2_sincGaussian_spatial_tail_bound` at `m1 = 2 * pChild p K`
or `m1 = pChild p K`, Terms B2/B3/D, and Term C via `r`-windowed child-DFT amplification) to close
the inductive error budget unconditionally for **all** `p ≥ 8`, `K ≥ 2`, `t1 ≤ 2 ^ (K / 2)`, `0 < r`,
`t1 * r = 2 ^ K` with **zero `hW` or `h_sub` hypotheses**:
`err_BCD < 0.036 * 2^{-p} * M`, `err_A + err_BCD + err_quant < 0.394 * 2^{-p} * M`, and
`err_A + err_BCD + err_quant < 2^{-p} * M`. -/
theorem lemma2_precision_schedule_closure_with_stopband
    (p K t1 r m1 : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (ht1 : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (y δ M err_A err_B1 err_B2 err_B3 err_C err_D err_BCD err_quant : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hM : 0 < M) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hm1 : m1 = 2 * pChild p K ∨ m1 = pChild p K)
    (hA_stop : err_A ≤ (2.36 : ℝ) * (t1 : ℝ) *
      (1 - c0Coeff (realErfScaled (alphaSchedule (pWork p K))) y -
        c1Coeff (realErfScaled (alphaSchedule (pWork p K))) y) * M)
    (hB1 : err_B1 ≤
      ((∑' k : ℕ, |sincGaussian (alphaSchedule (pWork p K)) ((m1 + 1 + k : ℝ) - δ)|) +
        (∑' k : ℕ, |sincGaussian (alphaSchedule (pWork p K)) (-((m1 + 1 + k : ℝ)) - δ)|)) * M)
    (hB2 : err_B2 ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hB3 : err_B3 ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hC : err_C ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M))
    (hD : err_D ≤ (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    (hBCD_amp : err_BCD ≤ (2.36 : ℝ) * (t1 : ℝ) * (err_B1 + err_B2 + err_B3 + err_C + err_D))
    (hQ : err_quant ≤ complexQuantizeMaxErr p * M) :
    err_BCD < (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ∧
    err_A + err_BCD + err_quant < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hstop := mul_lt_mul_of_pos_right
    (lemma2_termA_stopband_error_bound p K t1 hp hK ht1 y hy0 hy1) hM
  exact lemma2_precision_schedule_closure
    p K t1 r m1 δ M err_A err_B1 err_B2 err_B3 err_C err_D err_BCD err_quant
    hK hr hsize hM hδ0 hδ1 hm1 (hA_stop.trans hstop.le)
    hB1 hB2 hB3 hC hD hBCD_amp hQ

/-! ## 2. Purely Additive Precision Schedule Across All `L` Recursion Levels (`[MS]` §6.3 & §7.2) -/

/-- Precision `p_ℓ` at recursion depth `ℓ` under the additive schedule `p_{ℓ+1} = pChild p_ℓ K_ℓ`. -/
def levelPrecision (p0 : ℕ) (K : ℕ → ℕ) : ℕ → ℕ
  | 0 => p0
  | l + 1 => pChild (levelPrecision p0 K l) (K l)

/-- **`[MS]` Theorem 1 (Part 2a: Exact Closed-Form Telescoping of `p_ℓ`, `[MS]` §7.2, proof of Theorem 1)**:
At every recursion depth `ℓ ∈ ℕ`,
`levelPrecision p0 K ℓ = p0 + 2 * (∑ j ∈ Finset.range ℓ, K j) + 12 * ℓ`. -/
theorem theorem5_levelPrecision_closed_form (p0 : ℕ) (K : ℕ → ℕ) (l : ℕ) :
    levelPrecision p0 K l = p0 + 2 * (∑ j ∈ Finset.range l, K j) + 12 * l := by
  induction l with
  | zero => simp [levelPrecision]
  | succ l ih =>
    simp only [levelPrecision, pChild_eq_additive, ih, Finset.sum_range_succ]
    ring

/-- **`[MS]` Theorem 1 (Part 2b: Uniform `Θ(log n)` Bound on `p_ℓ`, `[MS]` §7.2, proof of Theorem 1)**:
Whenever `∑_{j=0}^{ℓ-1} K_j ≤ 2 K_0` (since `K_j ≈ K_0 / 2^j`), the working precision at depth `ℓ`
satisfies `levelPrecision p0 K ℓ ≤ p0 + 4 K_0 + 12 ℓ`. -/
theorem theorem5_levelPrecision_le (p0 K0 : ℕ) (K : ℕ → ℕ) (l : ℕ)
    (hK : ∑ j ∈ Finset.range l, K j ≤ 2 * K0) :
    levelPrecision p0 K l ≤ p0 + 4 * K0 + 12 * l := by
  rw [theorem5_levelPrecision_closed_form]
  omega

/-! ## 3. `(1/2)^ℓ` Geometric Contraction of Synthetic FFT & Routing Work (`[MS]` §7.2, Part 2) -/

/-- Exact geometric telescoping of the Sinc-Gaussian `(1/2)^ℓ` per-level Synthetic FFT contraction
(`[MS]`, Section 7.2, proof of Theorem 1, Part 2):
`∑_{ℓ=0}^{L-1} (1 / 2)^ℓ = 2 * (1 - (1 / 2)^L) ≤ 2`. -/
theorem theorem5_sinc_gaussian_contraction_sum (L : ℕ) :
    ∑ l ∈ Finset.range L, ((1 / 2 : ℝ) ^ l) = 2 * (1 - (1 / 2 : ℝ) ^ L) ∧
    ∑ l ∈ Finset.range L, ((1 / 2 : ℝ) ^ l) ≤ (2 : ℝ) := by
  have hsum : ∑ l ∈ Finset.range L, ((1 / 2 : ℝ) ^ l) = 2 * (1 - (1 / 2 : ℝ) ^ L) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  refine ⟨hsum, ?_⟩
  rw [hsum]
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ L := pow_nonneg (by norm_num) L
  linarith

/-- Comparison against the Plain-Gaussian `(5/8)^ℓ` per-level contraction (comparison table of an earlier `[MS]` draft, omitted in the current `[MS]`):
`∑_{ℓ=0}^{L-1} (5 / 8)^ℓ = (8 / 3) * (1 - (5 / 8)^L) ≤ 8 / 3`, and for all `L ≥ 2`, the
Sinc-Gaussian sum `2 * (1 - (1 / 2)^L)` is strictly smaller than the Plain-Gaussian sum
`(8 / 3) * (1 - (5 / 8)^L)`. -/
theorem theorem5_plain_gaussian_contraction_sum (L : ℕ) :
    ∑ l ∈ Finset.range L, ((5 / 8 : ℝ) ^ l) = (8 / 3 : ℝ) * (1 - (5 / 8 : ℝ) ^ L) ∧
    ∑ l ∈ Finset.range L, ((5 / 8 : ℝ) ^ l) ≤ (8 / 3 : ℝ) := by
  have hsum : ∑ l ∈ Finset.range L, ((5 / 8 : ℝ) ^ l) = (8 / 3 : ℝ) * (1 - (5 / 8 : ℝ) ^ L) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  refine ⟨hsum, ?_⟩
  rw [hsum]
  have hpos : (0 : ℝ) ≤ (5 / 8 : ℝ) ^ L := pow_nonneg (by norm_num) L
  linarith

/-! ## 4. `[MS]` Theorem 1 (§7.2): Complexity Recurrence Summation Under Per-Level Cost Hypotheses -/

/-- **`[MS]` Theorem 1 (Complexity Recurrence Summation Under Per-Level Cost Bounds, `[MS]` §7.2)**:
Let `n_log_n` denote `n log_2 n` and `n_log_log_n` denote `n log_2 log_2 n`.
If across `L` recursion levels:
1. Level-`ℓ` Synthetic FFT + Turing-machine routing work satisfies
   `W_syn(ℓ) ≤ C_syn * (1 / 2)^ℓ * n_log_n` (with `C_syn ≥ 0`),
2. Level-`ℓ` secondary overhead (Overlap-Add Kronecker spreading, twists, and bidiagonal solves)
   satisfies `W_ovh(ℓ) ≤ C_ovh * n_log_log_n` (with `C_ovh ≥ 0`), and
3. Leaf base-case FFT work at depth `L` satisfies `W_base ≤ C_base * (L : ℝ) * n_log_log_n`,
then total bit complexity satisfies:
`∑_{ℓ=0}^{L-1} W_syn(ℓ) + ∑_{ℓ=0}^{L-1} W_ovh(ℓ) + W_base ≤
  2 * C_syn * n_log_n + (C_ovh + C_base) * (L : ℝ) * n_log_log_n`. -/
theorem theorem5_end_to_end_complexity_bound
    (L : ℕ) (C_syn C_ovh C_base n_log_n n_log_log_n W_base : ℝ)
    (W_syn W_ovh : ℕ → ℝ)
    (hC_syn : 0 ≤ C_syn) (hn : 0 ≤ n_log_n)
    (h_syn : ∀ l ∈ Finset.range L, W_syn l ≤ C_syn * ((1 / 2 : ℝ) ^ l) * n_log_n)
    (h_ovh : ∀ l ∈ Finset.range L, W_ovh l ≤ C_ovh * n_log_log_n)
    (h_base : W_base ≤ C_base * (L : ℝ) * n_log_log_n) :
    (∑ l ∈ Finset.range L, W_syn l) + (∑ l ∈ Finset.range L, W_ovh l) + W_base ≤
      2 * C_syn * n_log_n + (C_ovh + C_base) * (L : ℝ) * n_log_log_n := by
  have h1 : ∑ l ∈ Finset.range L, W_syn l ≤ 2 * C_syn * n_log_n := by
    calc ∑ l ∈ Finset.range L, W_syn l
        ≤ ∑ l ∈ Finset.range L, C_syn * ((1 / 2 : ℝ) ^ l) * n_log_n :=
          Finset.sum_le_sum h_syn
      _ = C_syn * n_log_n * (∑ l ∈ Finset.range L, ((1 / 2 : ℝ) ^ l)) := by
          simp_rw [mul_comm (C_syn * _), ← mul_assoc, ← Finset.mul_sum]
          ring
      _ ≤ C_syn * n_log_n * 2 := by
          refine mul_le_mul_of_nonneg_left (theorem5_sinc_gaussian_contraction_sum L).2 ?_
          exact mul_nonneg hC_syn hn
      _ = 2 * C_syn * n_log_n := by ring
  have h2 : ∑ l ∈ Finset.range L, W_ovh l ≤ C_ovh * (L : ℝ) * n_log_log_n := by
    calc ∑ l ∈ Finset.range L, W_ovh l
        ≤ ∑ _l ∈ Finset.range L, C_ovh * n_log_log_n := Finset.sum_le_sum h_ovh
      _ = (L : ℝ) * (C_ovh * n_log_log_n) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = C_ovh * (L : ℝ) * n_log_log_n := by ring
  linarith

/-! ## 5. Concrete Operation Count of the Recursive Binary-Tree Radix-2 Synthetic FFT (`[MS]` §3.5 & §7.2) -/

/-- Exact recursive coefficient-addition count of the `k`-stage binary-tree Cooley–Tukey
Synthetic FFT over `R_r = ℂ[y]/(y^r + 1)` (`[MS]` §3.5 & §7.2):
A `0`-stage transform performs `0` additions; a `(k + 1)`-stage transform of length `2^{k+1}`
makes `2` recursive calls of `k` stages and combines `2^k` butterfly pairs, each costing `2 * r`
complex additions (one addition and one subtraction per degree-`< r` coefficient). -/
def syntheticFFTRadix2AddOps (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * syntheticFFTRadix2AddOps r k + 2 ^ k * (2 * r)

/-- Exact recursive general complex-multiplication count of the `k`-stage binary-tree Cooley–Tukey
Synthetic FFT over `R_r = ℂ[y]/(y^r + 1)` (`[MS]` §3.5 & §7.2):
Because all twiddle factors `y^s` in `R_r` are pure cyclic shifts with sign flips (`negacyclicShift`),
every stage performs **zero** general complex multiplications. -/
def syntheticFFTRadix2MulOps (_r : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * syntheticFFTRadix2MulOps _r k

/-- **Closed-Form Operation Counts of the `k`-Stage Radix-2 Synthetic FFT (`[MS]` §3.5 & §7.2)**:
For any polynomial degree `r` and stage count `k` (transform length `t_1 = 2^k`), the recursive
radix-2 Synthetic FFT performs `0` complex multiplications, `k * (2^k * r)` complex
additions/subtractions, and `2 * k * (2^k * r)` real additions/subtractions. -/
theorem syntheticFFTRadix2Ops_closed_form (r k : ℕ) :
    syntheticFFTRadix2MulOps r k = 0 ∧
    syntheticFFTRadix2AddOps r k = k * (2 ^ k * r) ∧
    2 * syntheticFFTRadix2AddOps r k = 2 * k * (2 ^ k * r) := by
  have hmul : syntheticFFTRadix2MulOps r k = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [syntheticFFTRadix2MulOps, ih]
  have hadd : syntheticFFTRadix2AddOps r k = k * (2 ^ k * r) := by
    clear hmul
    induction k with
    | zero => simp [syntheticFFTRadix2AddOps]
    | succ k ih =>
      simp only [syntheticFFTRadix2AddOps, ih, pow_succ]
      ring
  refine ⟨hmul, hadd, ?_⟩
  rw [hadd]
  ring

/-! ## 6. Branching Multi-Level Recursion Cost Tree & Same-Grid (`K = 1`) Subproblem Product (`[MS]` §7.2) -/

/-- Branching multi-level recursion cost tree of `FastDFT` starting at depth `l` with `rem` levels
remaining (`[MS]` §7.2):
- At a leaf (`rem = 0`), a subproblem at depth `l` incurs base-case cost `localBase l`.
- At an internal node (`rem + 1` levels remaining), a subproblem at depth `l` performs local
  Synthetic FFT + routing work `localSyn l`, local secondary overhead (Overlap-Add Kronecker
  spreading + twists + bidiagonal solve) `localOvh l`, and spawns `t1 l` recursive subproblems at
  depth `l + 1`. -/
def fastDFTBranchingCost (t1 : ℕ → ℕ) (localSyn localOvh : ℕ → ℝ) (localBase : ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0, l => localBase l
  | rem + 1, l =>
    localSyn l + localOvh l +
      (t1 l : ℝ) * fastDFTBranchingCost t1 localSyn localOvh localBase rem (l + 1)

/-- **Unit-Expansion (`K = 1`) Branching Recursion Tree Telescoping Identity (`[MS]` §7.2)**:
Because the Sinc-Gaussian Fractional-Shift algorithm uses unit expansion `K = 1`, the subproblem
transform length satisfies `R d = t1 d * R (d + 1)` at every level `d`, so the total work across
all `∏_{j < d} t1 j` subproblems at depth `l + d` preserves the invariant `R l = (∏ t1) * R (l + d)`
with **zero `2^ℓ` subproblem blowup**. -/
theorem fastDFTBranchingCost_unit_expansion_eq
    (t1 R : ℕ → ℕ) (localSyn localOvh localBase perElemSyn perElemOvh perElemBase : ℕ → ℝ)
    (hR : ∀ d, R d = t1 d * R (d + 1))
    (hSyn : ∀ d, localSyn d = (R d : ℝ) * perElemSyn d)
    (hOvh : ∀ d, localOvh d = (R d : ℝ) * perElemOvh d)
    (hBase : ∀ d, localBase d = (R d : ℝ) * perElemBase d)
    (rem l : ℕ) :
    fastDFTBranchingCost t1 localSyn localOvh localBase rem l =
      (R l : ℝ) *
        ((∑ d ∈ Finset.range rem, perElemSyn (l + d)) +
         (∑ d ∈ Finset.range rem, perElemOvh (l + d)) +
         perElemBase (l + rem)) := by
  induction rem generalizing l with
  | zero =>
    simp [fastDFTBranchingCost, hBase]
  | succ rem ih =>
    simp only [fastDFTBranchingCost, hSyn l, hOvh l, ih (l + 1)]
    have hR_cast : (R l : ℝ) = (t1 l : ℝ) * (R (l + 1) : ℝ) := by
      exact_mod_cast hR l
    have hsum1 : ∑ d ∈ Finset.range (rem + 1), perElemSyn (l + d) =
        perElemSyn l + ∑ d ∈ Finset.range rem, perElemSyn (l + 1 + d) := by
      rw [Finset.sum_range_succ' (fun d => perElemSyn (l + d)), Nat.add_zero, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      congr 1
      omega
    have hsum2 : ∑ d ∈ Finset.range (rem + 1), perElemOvh (l + d) =
        perElemOvh l + ∑ d ∈ Finset.range rem, perElemOvh (l + 1 + d) := by
      rw [Finset.sum_range_succ' (fun d => perElemOvh (l + d)), Nat.add_zero, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      congr 1
      omega
    have hbase_idx : l + (rem + 1) = l + 1 + rem := by omega
    rw [hsum1, hsum2, hbase_idx, hR_cast]
    ring

/-- **Root-to-Leaf Branching Recursion Tree Complexity Bound (`fastDFTBranchingCost_root_bound`, `[MS]` §7.2)**:
Composing `fastDFTBranchingCost_unit_expansion_eq` at the root (`l = 0`, `rem = L`) with the
per-element Synthetic FFT geometric contraction `perElemSyn d ≤ C_syn * (1/2)^d * K0_P`, the
per-element Overlap-Add + twist + bidiagonal overhead `perElemOvh d ≤ C_ovh * P_log_P`
(from `theorem4_window_width_cancellation`), and the leaf base-case bound
`perElemBase L ≤ C_base * L * P_log_P` yields the end-to-end root cost bound directly from the
branching recursion tree. -/
theorem fastDFTBranchingCost_root_bound
    (L : ℕ) (t1 R : ℕ → ℕ)
    (localSyn localOvh localBase perElemSyn perElemOvh perElemBase : ℕ → ℝ)
    (C_syn C_ovh C_base K0_P P_log_P : ℝ)
    (hR : ∀ d, R d = t1 d * R (d + 1))
    (hSyn : ∀ d, localSyn d = (R d : ℝ) * perElemSyn d)
    (hOvh : ∀ d, localOvh d = (R d : ℝ) * perElemOvh d)
    (hBase : ∀ d, localBase d = (R d : ℝ) * perElemBase d)
    (hC_syn : 0 ≤ C_syn) (hK0_P : 0 ≤ K0_P)
    (h_syn : ∀ d ∈ Finset.range L, perElemSyn d ≤ C_syn * ((1 / 2 : ℝ) ^ d) * K0_P)
    (h_ovh : ∀ d ∈ Finset.range L, perElemOvh d ≤ C_ovh * P_log_P)
    (h_base : perElemBase L ≤ C_base * (L : ℝ) * P_log_P) :
    fastDFTBranchingCost t1 localSyn localOvh localBase L 0 ≤
      2 * C_syn * ((R 0 : ℝ) * K0_P) +
        (C_ovh + C_base) * (L : ℝ) * ((R 0 : ℝ) * P_log_P) := by
  rw [fastDFTBranchingCost_unit_expansion_eq t1 R localSyn localOvh localBase
    perElemSyn perElemOvh perElemBase hR hSyn hOvh hBase L 0]
  simp only [Nat.zero_add]
  have hsum := theorem5_end_to_end_complexity_bound L C_syn C_ovh C_base K0_P P_log_P
    (perElemBase L) perElemSyn perElemOvh hC_syn hK0_P h_syn h_ovh h_base
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (R 0))
  linarith

/-! ## 7. Asymptotic Dominance `(log (log n))^2 ≤ 4 * log n` and `O(n log n)` Bit Complexity (`[MS]` §7.2, Theorem 1) -/

/-- Elementary domination of `(log y)^2` by `4 y`: for all `y ≥ 1`, `(Real.log y)^2 ≤ 4 * y`.
Proved from `Real.log y = 2 * Real.log (√y)` and `Real.log (√y) ≤ √y - 1 ≤ √y`. -/
theorem sq_log_le_four_mul (y : ℝ) (hy : 1 ≤ y) :
    (Real.log y) ^ 2 ≤ 4 * y := by
  have hy_pos : 0 < y := by linarith
  have hy_nonneg : 0 ≤ y := by linarith
  have hsqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy_pos
  have hlog_sqrt : Real.log y = 2 * Real.log (Real.sqrt y) := by
    calc Real.log y
        = Real.log ((Real.sqrt y) ^ 2) := by rw [Real.sq_sqrt hy_nonneg]
      _ = 2 * Real.log (Real.sqrt y) := by
          rw [Real.log_pow]
          norm_num
  have hlog_le : Real.log (Real.sqrt y) ≤ Real.sqrt y := by
    have h := Real.log_le_sub_one_of_pos hsqrt_pos
    linarith
  have hlog_y_le : Real.log y ≤ 2 * Real.sqrt y := by linarith
  have hlog_y_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy
  calc (Real.log y) ^ 2
      ≤ (2 * Real.sqrt y) ^ 2 := pow_le_pow_left₀ hlog_y_nonneg hlog_y_le 2
    _ = 4 * (Real.sqrt y) ^ 2 := by ring
    _ = 4 * y := by rw [Real.sq_sqrt hy_nonneg]

/-- For all `x ≥ 3`, `1 ≤ Real.log x` (since `exp 1 < 2.7182818286 < 3`). -/
theorem one_le_log_of_three_le (x : ℝ) (hx : 3 ≤ x) :
    1 ≤ Real.log x := by
  have hexp_le : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hexp_le

/-- Closed-form bit-complexity upper-bound expression for `Multiply` on `n`-bit integers (`[MS]` §7.2):
`2 * C_syn * (n * log n) + (C_ovh + C_base) * (n * (log (log n))^2)`, combining the
`2 * C_syn * (n * log n)` Synthetic FFT + routing work with the
`(C_ovh + C_base) * (n * (log (log n))^2)` secondary overhead and leaf base-case work.
(In `IntMul/ExecutableAlgorithm.lean`, the instrumented algorithms `syntheticFFTRadix2WithCost`,
`fastDFTWithCost`, and `fastDFTMultiplyWithCost` connect their accumulated operation counts directly
to `fastDFTBranchingCost` and `multiplyBitComplexityBound`.) -/
noncomputable def multiplyBitComplexityBound (C_syn C_ovh C_base : ℝ) (n : ℕ) : ℝ :=
  2 * C_syn * ((n : ℝ) * Real.log (n : ℝ)) +
    (C_ovh + C_base) * ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2)

/-- **Bridge from `fastDFTBranchingCost` to `multiplyBitComplexityBound` (`[MS]` §7.2)**:
Under the hypotheses of `fastDFTBranchingCost_root_bound`, whenever `0 ≤ C_syn`, `0 ≤ C_ovh + C_base`,
the root Synthetic FFT scale satisfies `(R 0 : ℝ) * K0_P ≤ (n : ℝ) * Real.log (n : ℝ)`, and the
`L`-level secondary/base scale satisfies
`(L : ℝ) * ((R 0 : ℝ) * P_log_P) ≤ (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2`,
the root branching recursion cost `fastDFTBranchingCost t1 localSyn localOvh localBase L 0` is
bounded above by `multiplyBitComplexityBound C_syn C_ovh C_base n`. -/
theorem fastDFTBranchingCost_le_multiplyBitComplexityBound
    (L n : ℕ) (t1 R : ℕ → ℕ)
    (localSyn localOvh localBase perElemSyn perElemOvh perElemBase : ℕ → ℝ)
    (C_syn C_ovh C_base K0_P P_log_P : ℝ)
    (hR : ∀ d, R d = t1 d * R (d + 1))
    (hSyn : ∀ d, localSyn d = (R d : ℝ) * perElemSyn d)
    (hOvh : ∀ d, localOvh d = (R d : ℝ) * perElemOvh d)
    (hBase : ∀ d, localBase d = (R d : ℝ) * perElemBase d)
    (hC_syn : 0 ≤ C_syn) (hC_ovh_base : 0 ≤ C_ovh + C_base) (hK0_P : 0 ≤ K0_P)
    (h_syn : ∀ d ∈ Finset.range L, perElemSyn d ≤ C_syn * ((1 / 2 : ℝ) ^ d) * K0_P)
    (h_ovh : ∀ d ∈ Finset.range L, perElemOvh d ≤ C_ovh * P_log_P)
    (h_base : perElemBase L ≤ C_base * (L : ℝ) * P_log_P)
    (h_scale_syn : (R 0 : ℝ) * K0_P ≤ (n : ℝ) * Real.log (n : ℝ))
    (h_scale_ovh : (L : ℝ) * ((R 0 : ℝ) * P_log_P) ≤
      (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2) :
    fastDFTBranchingCost t1 localSyn localOvh localBase L 0 ≤
      multiplyBitComplexityBound C_syn C_ovh C_base n := by
  have hroot := fastDFTBranchingCost_root_bound L t1 R localSyn localOvh localBase
    perElemSyn perElemOvh perElemBase C_syn C_ovh C_base K0_P P_log_P
    hR hSyn hOvh hBase hC_syn hK0_P h_syn h_ovh h_base
  unfold multiplyBitComplexityBound
  have h1 : 2 * C_syn * ((R 0 : ℝ) * K0_P) ≤ 2 * C_syn * ((n : ℝ) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left h_scale_syn (by linarith)
  have h2 : (C_ovh + C_base) * (L : ℝ) * ((R 0 : ℝ) * P_log_P) ≤
      (C_ovh + C_base) * ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2) := by
    calc (C_ovh + C_base) * (L : ℝ) * ((R 0 : ℝ) * P_log_P)
        = (C_ovh + C_base) * ((L : ℝ) * ((R 0 : ℝ) * P_log_P)) := by ring
      _ ≤ (C_ovh + C_base) * ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left h_scale_ovh hC_ovh_base
  linarith

/-- **Explicit Linear-in-`n log n` Upper Bound on `multiplyBitComplexityBound` for all `n ≥ 3` (`[MS]` §7.2)**:
Because `(log (log n))^2 ≤ 4 * log n` for all `n ≥ 3`, the secondary overhead and base-case term
`O(n (log log n)^2)` is strictly absorbed into `O(n log n)` with explicit constant:
`multiplyBitComplexityBound C_syn C_ovh C_base n ≤ (2 * C_syn + 4 * (C_ovh + C_base)) * (n * log n)`. -/
theorem theorem5_multiply_bit_complexity_le_n_log_n
    (C_syn C_ovh C_base : ℝ) (hC_ovh_base : 0 ≤ C_ovh + C_base)
    (n : ℕ) (hn : 3 ≤ n) :
    multiplyBitComplexityBound C_syn C_ovh C_base n ≤
      (2 * C_syn + 4 * (C_ovh + C_base)) * ((n : ℝ) * Real.log (n : ℝ)) := by
  unfold multiplyBitComplexityBound
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_ge_one : 1 ≤ Real.log (n : ℝ) := one_le_log_of_three_le (n : ℝ) hn_real
  have hsq_log : (Real.log (Real.log (n : ℝ))) ^ 2 ≤ 4 * Real.log (n : ℝ) :=
    sq_log_le_four_mul (Real.log (n : ℝ)) hlog_ge_one
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hterm :
      (C_ovh + C_base) * ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2) ≤
        (C_ovh + C_base) * ((n : ℝ) * (4 * Real.log (n : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq_log hn_nonneg) hC_ovh_base
  linarith

/-- **`[MS]` Theorem 1 (Asymptotic `O(n log n)` Bound on `multiplyBitComplexityBound`, `[MS]` §7.2)**:
In Mathlib's `Asymptotics.IsBigO` sense as `n → ∞`, the closed-form bit-complexity upper-bound
expression `multiplyBitComplexityBound C_syn C_ovh C_base` satisfies
`multiplyBitComplexityBound C_syn C_ovh C_base =O[atTop] (fun n => n * log n)`.
(Combined with the instrumented cost bridge theorems `fastDFTWithCost_snd_le_multiplyBitComplexityBound`
and `fastDFTMultiplyWithCost_snd_isBigO_n_log_n` in `IntMul/ExecutableAlgorithm.lean`, this yields the
end-to-end `O(n log n)` cost bound for the instrumented recursive multiplication pipeline.) -/
theorem theorem5_multiply_bit_complexity_isBigO_n_log_n
    (C_syn C_ovh C_base : ℝ) (hC_syn : 0 ≤ C_syn) (hC_ovh_base : 0 ≤ C_ovh + C_base) :
    multiplyBitComplexityBound C_syn C_ovh C_base =O[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (2 * C_syn + 4 * (C_ovh + C_base)) ?_
  rw [Filter.eventually_atTop]
  refine ⟨3, fun n hn => ?_⟩
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_ge_one : 1 ≤ Real.log (n : ℝ) := one_le_log_of_three_le (n : ℝ) hn_real
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have h_nlogn_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hn_nonneg hlog_nonneg
  have h_bound_nonneg : 0 ≤ multiplyBitComplexityBound C_syn C_ovh C_base n := by
    unfold multiplyBitComplexityBound
    have h1 : 0 ≤ 2 * C_syn * ((n : ℝ) * Real.log (n : ℝ)) := by positivity
    have h2 : 0 ≤ (C_ovh + C_base) * ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2) := by
      positivity
    linarith
  rw [Real.norm_of_nonneg h_bound_nonneg, Real.norm_of_nonneg h_nlogn_nonneg]
  exact theorem5_multiply_bit_complexity_le_n_log_n C_syn C_ovh C_base hC_ovh_base n hn

end IntMul
