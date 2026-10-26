import WP.W14.Exact
import WP.W14.PaperSlots

/-!
# W14 regression: the snapshot's schedule through the parametric route

`snapshotSchedule_admissible : Admissible snapshotSchedule (fun _ _ => True)` (no stop rule needed:
at `pSub = m1 = 2 pChild` every slot has a margin of `2^-(p+2K+10)` or more). With
`tablesFaithfulAt_snapshot_iff` and `computablePaperFastDFTMultiplyAt_snapshot` this re-derives the
snapshot's headline FTP:2304 (`computablePaperFastDFTMultiply_faithful_eq_mul`) from the W14 closure.
-/

namespace WP.W14

open IntMul Real

theorem four_mul_add_one_le_two_pow {P : ℕ} (hP : 5 ≤ P) : 4 * P + 1 ≤ 2 ^ P := by
  induction P, hP using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

/-- Exponent comparison for negative powers of two. -/
theorem zpow_two_neg_le_mul {a b c : ℕ} (h : b + c ≤ a) :
    (2 : ℝ) ^ (-(a : ℤ)) ≤ (2 : ℝ) ^ (-(c : ℤ)) * (2 : ℝ) ^ (-(b : ℤ)) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

theorem natPow_mul_zpow_neg (K a : ℕ) (h : K ≤ a) :
    ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(a : ℤ)) = (2 : ℝ) ^ (-((a - K : ℕ) : ℤ)) := by
  rw [natPow_two_eq_zpow, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1; push_cast [h]; ring

/-- The step slots at the snapshot's schedule (`pSub = m1 = 2 pChild`), at every node. -/
theorem snapshotSchedule_stepSlots (p K : ℕ) (hK : 2 ≤ K) :
    StepSlots (snapshotSchedule.pSub p K) (snapshotSchedule.m1 p K) p K := by
  show StepSlots (2 * pChild p K) (2 * pChild p K) p K
  have hP := pChild_eq_additive p K
  set P := pChild p K
  set x := (2 : ℝ) ^ (-((2 * P : ℕ) : ℤ)) with hx_def
  set e := eUnit p K with he_def
  set N : ℝ := ((2 ^ K : ℕ) : ℝ)
  have hx0 : 0 < x := zpow_pos (by norm_num) _
  have he0 : 0 < e := eUnit_pos p K
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hp1 := two_zpow_neg_le_one p
  have h16 : (2 : ℝ) ^ (-(4 : ℕ) : ℤ) = 1 / 16 := by norm_num
  -- (a) x ≤ e / 16
  have hxa : x ≤ (1 / 16) * e := by
    have := zpow_two_neg_le_mul (a := 2 * P) (b := p + K + 10) (c := 4) (by omega)
    rw [h16] at this; exact this
  -- (b) N x ≤ e / 16
  have hNx_eq : N * x = (2 : ℝ) ^ (-((2 * P - K : ℕ) : ℤ)) := natPow_mul_zpow_neg K (2 * P) (by omega)
  have hNxa : N * x ≤ (1 / 16) * e := by
    rw [hNx_eq]
    have := zpow_two_neg_le_mul (a := 2 * P - K) (b := p + K + 10) (c := 4) (by omega)
    rw [h16] at this; exact this
  -- (c) N x ≤ 2^-p / 16384
  have hNxc : N * x ≤ (1 / 16384) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [hNx_eq]
    have := zpow_two_neg_le_mul (a := 2 * P - K) (b := p) (c := 14) (by omega)
    have h14 : (2 : ℝ) ^ (-(14 : ℕ) : ℤ) = 1 / 16384 := by norm_num
    rw [h14] at this; exact this
  have hs := sqrt_two_div_four_le
  have hs0 := sqrt_two_nonneg'
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hc : complexQuantizeMaxErr (2 * P) = Real.sqrt 2 / 4 * x := complexQuantizeMaxErr_eq _
  refine ⟨windowRules_snapshot p K, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]; nlinarith
  · rw [hc]
    have h1 : 2 * (Real.sqrt 2 / 4 * x) * (N + 2) = 2 * (Real.sqrt 2 / 4) * (N * x + 2 * x) := by ring
    rw [h1]; nlinarith
  · rw [hc]
    have h1 : Real.sqrt 2 / 4 * x * (N + 1) = (Real.sqrt 2 / 4) * (N * x + x) := by ring
    rw [h1]; nlinarith
  · -- hB12
    have hP5 : 5 ≤ P := by omega
    have h4P := four_mul_add_one_le_two_pow hP5
    have h4PR : 4 * (P : ℝ) + 1 ≤ ((2 ^ P : ℕ) : ℝ) := by exact_mod_cast h4P
    have hPx : ((2 ^ P : ℕ) : ℝ) * x = (2 : ℝ) ^ (-(P : ℤ)) := by
      rw [natPow_mul_zpow_neg P (2 * P) (by omega)]; congr 2; omega
    have hpc := pow_pChild_eq p K
    have hz := zpow_neg_add_two_le K hK
    have hz0 : (0 : ℝ) < (2 : ℝ) ^ (-((K : ℤ) + 2)) := zpow_pos (by norm_num) _
    have hPe : (2 : ℝ) ^ (-(P : ℤ)) ≤ (1 / 16) * e := by
      rw [hpc]; exact mul_le_mul_of_nonneg_right hz he0.le
    have hpi : 6 / (8 * Real.pi) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
    have hpi0 : 0 ≤ 6 / (8 * Real.pi) := by positivity
    have h2 : (2 * ((2 * P : ℕ) : ℝ) + 1) * x ≤ (2 : ℝ) ^ (-(P : ℤ)) := by
      rw [← hPx]; push_cast
      have : 2 * (2 * (P : ℝ)) + 1 = 4 * (P : ℝ) + 1 := by ring
      have h4PR' : 4 * (P : ℝ) + 1 ≤ (2 : ℝ) ^ P := by exact_mod_cast h4P
      rw [this]; exact mul_le_mul_of_nonneg_right h4PR' hx0.le
    have h3 : (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(P : ℤ)) ≤ (1 / 4) * ((1 / 16) * e) :=
      mul_le_mul hpi hPe (by positivity) (by norm_num)
    have h5 : (2 * ((2 * P : ℕ) : ℝ) + 1) * 5 * x = 5 * ((2 * ((2 * P : ℕ) : ℝ) + 1) * x) := by ring
    rw [h5]
    linarith
  · -- hsolve
    rw [hc]
    have h1 : N * (Real.sqrt 2 / 4 * x) = (Real.sqrt 2 / 4) * (N * x) := by ring
    rw [h1]; nlinarith
  · -- hratio
    rw [realQuantizeMaxErr_eq]
    have h1 : N * (10 * ((0.125 : ℝ) * x)) = 1.25 * (N * x) := by ring
    rw [h1]; nlinarith
  · omega

/-- The leaf slot at the snapshot's leaf grid `2p + K + 8`. -/
theorem snapshotSchedule_leafSlot (p K : ℕ) : LeafSlot (snapshotSchedule.qLeaf p K) p K := by
  show ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr (2 * p + K + 8) ≤ 0.6 * (2 : ℝ) ^ (-(p : ℤ))
  rw [complexQuantizeMaxErr_eq]
  have hK1 : ((K + 1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
  have hNq := natPow_mul_zpow_neg K (2 * p + K + 8) (by omega)
  have hq : (2 : ℝ) ^ (-((2 * p + K + 8 - K : ℕ) : ℤ)) ≤
      (2 : ℝ) ^ (-(8 : ℕ) : ℤ) * (2 : ℝ) ^ (-(p : ℤ)) :=
    zpow_two_neg_le_mul (by omega)
  have h8 : (2 : ℝ) ^ (-(8 : ℕ) : ℤ) = 1 / 256 := by norm_num
  rw [h8] at hq
  have hq0 : (0 : ℝ) < (2 : ℝ) ^ (-((2 * p + K + 8 : ℕ) : ℤ)) := zpow_pos (by norm_num) _
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hs := sqrt_two_div_four_le
  have hs0 := sqrt_two_nonneg'
  have h1 : ((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((2 * p + K + 8 : ℕ) : ℤ)) ≤
      (1 / 256) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc ((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((2 * p + K + 8 : ℕ) : ℤ))
        ≤ ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-((2 * p + K + 8 : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_right hK1 hq0.le
      _ ≤ (1 / 256) * (2 : ℝ) ^ (-(p : ℤ)) := by rw [hNq]; exact hq
  have h2 : ((K + 1 : ℕ) : ℝ) * 4 * (Real.sqrt 2 / 4 * (2 : ℝ) ^ (-((2 * p + K + 8 : ℕ) : ℤ))) =
      Real.sqrt 2 * (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((2 * p + K + 8 : ℕ) : ℤ))) := by ring
  rw [h2]
  have h3 : Real.sqrt 2 * (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((2 * p + K + 8 : ℕ) : ℤ))) ≤
      1.416 * ((1 / 256) * (2 : ℝ) ^ (-(p : ℤ))) :=
    mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
  nlinarith

/-- The snapshot's schedule is admissible at every node (no stop rule). -/
theorem snapshotSchedule_admissible : Admissible snapshotSchedule (fun _ _ => True) where
  step p K _ hK _ := snapshotSchedule_stepSlots p K hK
  leaf p K _ _ := snapshotSchedule_leafSlot p K

theorem stepsSatisfy_true (spec : QuantizedFastDFTSpec) : StepsSatisfy (fun _ _ => True) spec := by
  induction spec with
  | base p R => trivial
  | step p K t1 r c1 v1Of child ih => exact ⟨trivial, ih⟩

/-- **Regression.** The snapshot's headline FTP:2304, re-derived through the W14 parametric
closure (`TablesFaithful = TablesFaithfulAt snapshotSchedule`, snapshot pipeline = parametric
pipeline at `snapshotQLeaf`). -/
theorem computablePaperFastDFTMultiply_faithful_eq_mul_via_W14
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (b K0 k1 k2 : ℕ) (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B = A * B := by
  rw [← computablePaperFastDFTMultiplyAt_snapshot]
  exact computablePaperFastDFTMultiplyAt_faithful_eq_mul snapshotSchedule (fun _ _ => True)
    snapshotSchedule_admissible spec hvalid (stepsSatisfy_true spec) cSpec
    ((tablesFaithfulAt_snapshot_iff cSpec spec).mpr hfaith) b K0 k1 k2 hsize hp0 hk A B hA hB

#assert_std_axioms four_mul_add_one_le_two_pow zpow_two_neg_le_mul natPow_mul_zpow_neg
  snapshotSchedule_stepSlots snapshotSchedule_leafSlot snapshotSchedule_admissible stepsSatisfy_true
  computablePaperFastDFTMultiply_faithful_eq_mul_via_W14

end WP.W14
