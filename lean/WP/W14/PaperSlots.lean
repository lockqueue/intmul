import WP.W14.PaperStop

/-!
# W14: the paper's schedule is admissible under the paper's stop rule

`paperSchedule_admissible : Admissible paperSchedule PaperStopRule`. All step slots except the
spread slot `hB12` hold at every node with `8 ≤ p`, `2 ≤ K`; `hB12` (window tail + raw-tap rounding
`(2 m1 + 1) · 5 · 2^-pChild`) uses the stop rule through `paperStop_window_budget`. The leaf slot holds
at `q_leaf = p + K + 2` for every `K`.
-/

namespace WP.W14

open IntMul Real

theorem sqrt_two_div_four_le : Real.sqrt 2 / 4 ≤ 0.354 := by linarith [sqrt_two_lt_1416]

theorem sqrt_two_nonneg' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2

/-- `2^K · 2^-(K+2) = 1/4`. -/
theorem natPow_mul_zpow_neg_add_two (K : ℕ) :
    ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-((K : ℤ) + 2)) = 1 / 4 := by
  rw [natPow_two_eq_zpow, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h : (K : ℤ) + -((K : ℤ) + 2) = -2 := by ring
  rw [h]; norm_num

theorem zpow_neg_add_two_le (K : ℕ) (hK : 2 ≤ K) : (2 : ℝ) ^ (-((K : ℤ) + 2)) ≤ 1 / 16 := by
  have h : (2 : ℝ) ^ (-((K : ℤ) + 2)) ≤ (2 : ℝ) ^ (-4 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc (2 : ℝ) ^ (-((K : ℤ) + 2)) ≤ (2 : ℝ) ^ (-4 : ℤ) := h
    _ = 1 / 16 := by norm_num

/-- `cqme(pChild) = (√2/4) · 2^-(K+2) · eUnit`. -/
theorem cqme_pChild_eq (p K : ℕ) :
    complexQuantizeMaxErr (pChild p K) =
      Real.sqrt 2 / 4 * ((2 : ℝ) ^ (-((K : ℤ) + 2)) * eUnit p K) := by
  rw [complexQuantizeMaxErr_eq, pow_pChild_eq]

/-- The step slots at the paper's schedule (`pSub = pChild`, `m1 = m1Paper`). -/
theorem paperSchedule_stepSlots (p K : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (hstop : PaperStopRule p K) :
    StepSlots (paperSchedule.pSub p K) (paperSchedule.m1 p K) p K := by
  show StepSlots (pChild p K) (m1Paper p K) p K
  have he0 := eUnit_pos p K
  have hz0 : (0 : ℝ) < (2 : ℝ) ^ (-((K : ℤ) + 2)) := zpow_pos (by norm_num) _
  have hz16 := zpow_neg_add_two_le K hK
  have hN := natPow_mul_zpow_neg_add_two K
  have hs := sqrt_two_div_four_le
  have hs0 := sqrt_two_nonneg'
  have hc := cqme_pChild_eq p K
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hp1 := two_zpow_neg_le_one p
  have hNc := natPow_mul_pow_pChild_le p K hK
  have hpc0 : (0 : ℝ) < (2 : ℝ) ^ (-(pChild p K : ℤ)) := zpow_pos (by norm_num) _
  set z := (2 : ℝ) ^ (-((K : ℤ) + 2))
  set e := eUnit p K
  set N : ℝ := ((2 ^ K : ℕ) : ℝ)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  refine ⟨windowRules_paper p K hp hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hc
    rw [hc]
    have h1 : Real.sqrt 2 / 4 * (z * e) ≤ 0.354 * ((1 / 16) * e) := by
      apply mul_le_mul hs (mul_le_mul_of_nonneg_right hz16 he0.le) (by positivity) (by norm_num)
    linarith
  · -- hcr
    rw [hc]
    have h1 : z * (N + 2) ≤ 1 / 4 + 2 * (1 / 16) := by nlinarith
    have h2 : 0 ≤ z * (N + 2) := by positivity
    have h3 : 2 * (Real.sqrt 2 / 4 * (z * e)) * (N + 2) =
        2 * (Real.sqrt 2 / 4) * (z * (N + 2)) * e := by ring
    rw [h3]
    have h4 : 2 * (Real.sqrt 2 / 4) * (z * (N + 2)) ≤ 2 * 0.354 * (1 / 4 + 2 * (1 / 16)) :=
      mul_le_mul (by linarith) h1 h2 (by norm_num)
    nlinarith
  · -- hclog
    rw [hc]
    have h1 : z * (N + 1) ≤ 1 / 4 + 1 / 16 := by nlinarith
    have h2 : 0 ≤ z * (N + 1) := by positivity
    have h3 : Real.sqrt 2 / 4 * (z * e) * (N + 1) = (Real.sqrt 2 / 4) * (z * (N + 1)) * e := by ring
    rw [h3]
    have h4 : (Real.sqrt 2 / 4) * (z * (N + 1)) ≤ 0.354 * (1 / 4 + 1 / 16) :=
      mul_le_mul hs h1 h2 (by norm_num)
    nlinarith
  · -- hB12 (uses the stop rule)
    have hbud := paperStop_window_budget hp hstop
    have hbudR : 5 * (2 * (m1Paper p K : ℝ) + 1) + 1 ≤ 2 * N := by
      have h : ((5 * (2 * m1Paper p K + 1) + 1 : ℕ) : ℝ) ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := by
        exact_mod_cast hbud
      push_cast at h
      have hN2 : ((2 : ℝ) ^ (K + 1)) = 2 * N := by
        simp only [N]; push_cast; ring
      linarith
    have hpi : 6 / (8 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    have hpi0 : 0 ≤ 6 / (8 * Real.pi) := by positivity
    rw [pow_pChild_eq]
    have h1 : (6 / (8 * Real.pi) + 5 * (2 * (m1Paper p K : ℝ) + 1)) ≤ 2 * N := by linarith
    have h2 : (6 / (8 * Real.pi) + 5 * (2 * (m1Paper p K : ℝ) + 1)) * z ≤ 2 * N * z :=
      mul_le_mul_of_nonneg_right h1 hz0.le
    have h3 : 2 * N * z = 1 / 2 := by rw [mul_assoc, hN]; norm_num
    have h4 : (6 / (8 * Real.pi)) * (z * e) + (2 * (m1Paper p K : ℝ) + 1) * 5 * (z * e) =
        ((6 / (8 * Real.pi) + 5 * (2 * (m1Paper p K : ℝ) + 1)) * z) * e := by ring
    rw [h4]
    nlinarith
  · -- hsolve
    rw [complexQuantizeMaxErr_eq]
    have h1 : N * (Real.sqrt 2 / 4 * (2 : ℝ) ^ (-(pChild p K : ℤ))) =
        (Real.sqrt 2 / 4) * (N * (2 : ℝ) ^ (-(pChild p K : ℤ))) := by ring
    rw [h1]
    have h2 : (Real.sqrt 2 / 4) * (N * (2 : ℝ) ^ (-(pChild p K : ℤ))) ≤
        0.354 * ((1 / 16384 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) :=
      mul_le_mul hs hNc (by positivity) (by norm_num)
    nlinarith
  · -- hratio
    rw [realQuantizeMaxErr_eq]
    have h1 : N * (10 * ((0.125 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)))) =
        1.25 * (N * (2 : ℝ) ^ (-(pChild p K : ℤ))) := by ring
    rw [h1]
    nlinarith
  · -- hq24
    rw [pChild_eq_additive]; omega

/-- The leaf slot at the paper's leaf grid `q_leaf = p + K + 2` (`p + K + 4` bits), for every `K`. -/
theorem paperSchedule_leafSlot (p K : ℕ) : LeafSlot (paperSchedule.qLeaf p K) p K := by
  show ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr (p + K + 2) ≤ 0.6 * (2 : ℝ) ^ (-(p : ℤ))
  rw [complexQuantizeMaxErr_eq]
  have hK1 : ((K + 1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_two_pow_self
  have hz : ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-((p + K + 2 : ℕ) : ℤ)) =
      (1 / 4) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [natPow_two_eq_zpow, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have h : (K : ℤ) + -((p + K + 2 : ℕ) : ℤ) = (-2 : ℤ) + (-(p : ℤ)) := by push_cast; ring
    rw [h, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hq0 : (0 : ℝ) < (2 : ℝ) ^ (-((p + K + 2 : ℕ) : ℤ)) := zpow_pos (by norm_num) _
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hs := sqrt_two_div_four_le
  have hs0 := sqrt_two_nonneg'
  have h1 : ((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((p + K + 2 : ℕ) : ℤ)) ≤
      (1 / 4) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [← hz]; exact mul_le_mul_of_nonneg_right hK1 hq0.le
  have h2 : ((K + 1 : ℕ) : ℝ) * 4 * (Real.sqrt 2 / 4 * (2 : ℝ) ^ (-((p + K + 2 : ℕ) : ℤ))) =
      Real.sqrt 2 * (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((p + K + 2 : ℕ) : ℤ))) := by ring
  rw [h2]
  have h3 : Real.sqrt 2 * (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((p + K + 2 : ℕ) : ℤ))) ≤
      1.416 * ((1 / 4) * (2 : ℝ) ^ (-(p : ℤ))) :=
    mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
  nlinarith

/-- **The paper's schedule is admissible on the paper's stop-rule nodes.** -/
theorem paperSchedule_admissible : Admissible paperSchedule PaperStopRule where
  step p K hp hK hstop := paperSchedule_stepSlots p K hp hK hstop
  leaf p K _ _ := paperSchedule_leafSlot p K

#assert_std_axioms natPow_mul_zpow_neg_add_two zpow_neg_add_two_le cqme_pChild_eq
  paperSchedule_stepSlots paperSchedule_leafSlot paperSchedule_admissible

end WP.W14
