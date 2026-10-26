import Mathlib

/-!
# Cost: absorbing logarithmic factors into the slack

Paper: Section 7.4 (`sec:main-gaps`, "Gaps and slack"): if `s = g_min - κ > 0` and
`j ≥ 0` is an integer, then for `P ≥ 2`, `(lg(2P))^j ≤ 4^j (ln P)^j ≤ j! (4/s)^j P^s`, "by the
`j`-th term of the exponential series". Here `lg = log₂` is `Real.logb 2` and `ln` is `Real.log`.

Theorems tagged CONTRACT are the contract statements; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

/-- CONTRACT (Section 7.4 (`sec:main-gaps`), first inequality): for `P ≥ 2`, `lg(2P) ≤ 4 ln P`. -/
theorem logb_two_mul_le_four_log {P : ℝ} (hP : 2 ≤ P) :
    Real.logb 2 (2 * P) ≤ 4 * Real.log P := by
  have hP0 : 0 < P := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hlogP0 : 0 ≤ Real.log P := le_trans hlog2.le hlogP
  rw [Real.logb, Real.log_mul (by norm_num) hP0.ne', div_le_iff₀ hlog2]
  have h := mul_le_mul_of_nonneg_left hlog2'.le hlogP0
  nlinarith

/-- CONTRACT (Section 7.4 (`sec:main-gaps`), slack absorption): for `P ≥ 2`, `s > 0` and `j : ℕ`,
`(lg(2P))^j ≤ j! (4/s)^j P^s`. -/
theorem logb_pow_le_factorial_mul_rpow {P s : ℝ} (hP : 2 ≤ P) (hs : 0 < s) (j : ℕ) :
    Real.logb 2 (2 * P) ^ j ≤ (Nat.factorial j : ℝ) * (4 / s) ^ j * P ^ s := by
  have hP0 : 0 < P := by linarith
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ Real.logb 2 (2 * P) := Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : Real.logb 2 (2 * P) ^ j ≤ (4 * Real.log P) ^ j :=
    pow_le_pow_left₀ hL0 (logb_two_mul_le_four_log hP) j
  have h2 : (s * Real.log P) ^ j / (Nat.factorial j) ≤ Real.exp (s * Real.log P) :=
    Real.pow_div_factorial_le_exp (s * Real.log P) (by positivity) j
  have h3 : Real.exp (s * Real.log P) = P ^ s := by
    rw [Real.rpow_def_of_pos hP0, mul_comm]
  have hfac : (0 : ℝ) < Nat.factorial j := by exact_mod_cast Nat.factorial_pos j
  have h4 : (s * Real.log P) ^ j ≤ (Nat.factorial j) * P ^ s := by
    rw [div_le_iff₀ hfac, h3] at h2
    linarith
  calc Real.logb 2 (2 * P) ^ j ≤ (4 * Real.log P) ^ j := h1
    _ = (4 / s) ^ j * (s * Real.log P) ^ j := by
        rw [← mul_pow]
        congr 1
        field_simp
    _ ≤ (4 / s) ^ j * ((Nat.factorial j) * P ^ s) := by
        apply mul_le_mul_of_nonneg_left h4
        positivity
    _ = (Nat.factorial j : ℝ) * (4 / s) ^ j * P ^ s := by ring

/-- CONTRACT (Section 7.6 (`sec:main-thm`), proof of Theorem 1 (`thm:main`), how the slack is used): for `P ≥ 2`, `κ < g` and `j : ℕ`,
`P^{1-g} (lg(2P))^j ≤ j! (4/(g-κ))^j P^{1-κ}` (take `s = g - κ` above). -/
theorem rpow_mul_logb_pow_le {P g κ : ℝ} (hP : 2 ≤ P) (hκg : κ < g) (j : ℕ) :
    P ^ (1 - g) * Real.logb 2 (2 * P) ^ j ≤
      (Nat.factorial j : ℝ) * (4 / (g - κ)) ^ j * P ^ (1 - κ) := by
  have hP0 : 0 < P := by linarith
  have hs : 0 < g - κ := sub_pos.2 hκg
  have h := logb_pow_le_factorial_mul_rpow hP hs j
  have hPg : 0 ≤ P ^ (1 - g) := Real.rpow_nonneg hP0.le _
  calc P ^ (1 - g) * Real.logb 2 (2 * P) ^ j
      ≤ P ^ (1 - g) * ((Nat.factorial j : ℝ) * (4 / (g - κ)) ^ j * P ^ (g - κ)) :=
        mul_le_mul_of_nonneg_left h hPg
    _ = (Nat.factorial j : ℝ) * (4 / (g - κ)) ^ j * (P ^ (1 - g) * P ^ (g - κ)) := by ring
    _ = (Nat.factorial j : ℝ) * (4 / (g - κ)) ^ j * P ^ (1 - κ) := by
        rw [← Real.rpow_add hP0, show 1 - g + (g - κ) = 1 - κ by ring]

/-- CONTRACT (helper for the `m(P²)` terms of Section 7.3, eq. (`eq:cost-W`)): for `P ≥ 1`, `lg(2P²) ≤ 2 lg(2P)`. -/
theorem logb_two_mul_sq_le {P : ℝ} (hP : 1 ≤ P) :
    Real.logb 2 (2 * P ^ 2) ≤ 2 * Real.logb 2 (2 * P) := by
  have hP0 : 0 < P := by linarith
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul (by norm_num) hP0.ne',
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  have : 0 ≤ Real.logb 2 P := Real.logb_nonneg (by norm_num) hP
  push_cast
  linarith

end SubNLogN.Math.Cost
