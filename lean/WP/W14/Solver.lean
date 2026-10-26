import IntMul.MaterializedAndComputable.FaithfulTablesPerturbation
import WP.W14.Spread

/-!
# W14: the solver stage of the step closure, at any grid

FTP:1898–2195 (the three bidiagonal/Nyquist solver branches of `sincGaussianFastDFTOfTables_step_error_le`)
as a stand-alone lemma. The grid `pSub` is a parameter; the snapshot's `pSub = 2 · pChild` facts
(`faithful_coeff_ratio_pow_le`, `t1_mul_complexQuantizeMaxErr_two_mul_pChild_le`) are replaced by the
hypotheses `hq`, `ht1q`, `ht1c` (consequences of `StepSlots`). The right-hand-side error `ε` is
abstract: `hY` says that every `z` within one rounding of the solver input `Ycol m` is within `ε` of
the ideal two-term passband right-hand side.
-/

namespace WP.W14

open IntMul Complex Real

/-- The ideal two-term passband right-hand side `c0 X(k) + c1 X((k-1) mod t1)` (FTP:1818). -/
noncomputable def passbandRHS (t1 : ℕ) (c0 c1 : ℂ) (X : ℕ → ℂ) : ℕ → ℂ := fun k =>
  c0 * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) + c1 * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)

/-- The `u2` clause of the passband-table faithfulness (FTP:70–85) at grid `pSub`. -/
def C01Clause (pSub p K r : ℕ) (c0Table c1Table : Array (ℤ × ℤ)) (u2 : ℕ) : Prop :=
  let y := (u2 : ℝ) / (r : ℝ)
  let α := alphaSchedule (pWork p K)
  let c0_pair := read1D c0Table u2
  let c1_pair := read1D c1Table u2
  c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
  0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
  0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
  |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
    2 * realQuantizeMaxErr pSub ∧
  |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
    2 * realQuantizeMaxErr pSub ∧
  (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
  (2 * u2 = r → c1_pair = c0_pair) ∧
  (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1)

/-- Coefficient facts extracted from `C01Clause` (FTP:1613–1644). -/
theorem c01Clause_facts {pSub p K r : ℕ} {c0Table c1Table : Array (ℤ × ℤ)} {u2 : ℕ}
    (h : C01Clause pSub p K r c0Table c1Table u2) :
    let c0R := c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ))
    let c1R := c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ))
    let c0_qR : ℝ := ((read1D c0Table u2).1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
    let c1_qR : ℝ := ((read1D c1Table u2).1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
    |c0_qR - c0R| ≤ 2 * realQuantizeMaxErr pSub ∧ |c1_qR - c1R| ≤ 2 * realQuantizeMaxErr pSub ∧
    0 ≤ c0_qR ∧ c0_qR ≤ 1 ∧ 0 ≤ c1_qR ∧ c1_qR ≤ 1 ∧
    (2 * u2 < r → c1_qR ≤ c0_qR) ∧ (r < 2 * u2 → c0_qR ≤ c1_qR) ∧
    (2 * u2 = r → toScaledComplex pSub (read1D c1Table u2) =
      toScaledComplex pSub (read1D c0Table u2)) ∧
    toScaledComplex pSub (read1D c0Table u2) = (c0_qR : ℂ) ∧
    toScaledComplex pSub (read1D c1Table u2) = (c1_qR : ℂ) := by
  obtain ⟨hc0_im, hc1_im, hc0_p_nonneg, hc0_p_le, hc1_p_nonneg, hc1_p_le,
    hc0_err_re, hc1_err_re, hc10_p_fwd, hc10_p_nyq, hc01_p_bwd⟩ := h
  have hpow_pSub2_pos : (0 : ℝ) < (2 : ℝ) ^ (pSub + 2) := by positivity
  refine ⟨hc0_err_re, hc1_err_re, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (by exact_mod_cast hc0_p_nonneg) hpow_pSub2_pos.le
  · exact (div_le_one hpow_pSub2_pos).mpr (by exact_mod_cast hc0_p_le)
  · exact div_nonneg (by exact_mod_cast hc1_p_nonneg) hpow_pSub2_pos.le
  · exact (div_le_one hpow_pSub2_pos).mpr (by exact_mod_cast hc1_p_le)
  · exact fun h => div_le_div_of_nonneg_right (by exact_mod_cast hc10_p_fwd h) hpow_pSub2_pos.le
  · exact fun h => div_le_div_of_nonneg_right (by exact_mod_cast hc01_p_bwd h) hpow_pSub2_pos.le
  · exact fun h => congrArg (toScaledComplex pSub) (hc10_p_nyq h)
  · apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; simp [toScaledComplex, hc0_im]
  · apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; simp [toScaledComplex, hc1_im]

#assert_std_axioms c01Clause_facts

end WP.W14
