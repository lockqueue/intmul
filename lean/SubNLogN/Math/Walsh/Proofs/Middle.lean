import SubNLogN.Math.Walsh.Middle

/-!
# Proof of Corollary 6.6 from Theorem 6.5 and Lemma 6.1

Paper: Corollary 6.6 (`cor:walsh-middle`, Section 6.5 (`sec:direct-fft-bridge`)) and
Definition 4.5 (`def:middle-contract`). Proves `walsh_middle_of : DirectFFTStmt →
PhaseTableStmt → WalshMiddleStmt` and its ideal-oracle specialization `walsh_middle_ideal_of`.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-- A disk-grid value at precision `q` has component width `q + 2` (each numerator `a` satisfies
`|a| ≤ 2^q < 2^{q+1}`; Definition 3.1 (`def:grid`)). -/
theorem fitsWidth_of_onDiskGrid {q : ℕ} {z : ℂ} (hz : OnDiskGrid q z) : FitsWidth q (q + 2) z := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hn⟩ := hz
  have key : ∀ (x : ℝ) (c : ℤ), x = c * gridUnit q → |x| ≤ 1 →
      -(2 : ℤ) ^ (q + 2 - 1) ≤ c ∧ c < (2 : ℤ) ^ (q + 2 - 1) := by
    intro x c hx hx1
    have h2 : (0 : ℝ) < 2 ^ q := by positivity
    have hcR : |(c : ℝ)| ≤ 2 ^ q := by
      rw [hx, abs_mul, show |gridUnit q| = gridUnit q from abs_of_pos (gridUnit_pos q)] at hx1
      unfold gridUnit at hx1
      rwa [← div_eq_mul_inv, div_le_one h2] at hx1
    have hc : |c| ≤ 2 ^ q := by exact_mod_cast hcR
    have hq : q + 2 - 1 = q + 1 := by omega
    rw [hq, pow_succ]
    have hpos : (0 : ℤ) < 2 ^ q := by positivity
    constructor <;> cases abs_le.mp hc <;> linarith
  exact ⟨⟨a, ha, key _ _ ha ((Complex.abs_re_le_norm z).trans hn)⟩,
    ⟨b, hb, key _ _ hb ((Complex.abs_im_le_norm z).trans hn)⟩⟩

/-- **Corollary 6.6** from Theorem 6.5 and Lemma 6.1. -/
theorem walsh_middle_of (h85 : DirectFFTStmt) (h81 : PhaseTableStmt) : WalshMiddleStmt := by
  intro layer P D ℓ K a hq hD hℓ hℓq hK1 hKℓ ha hOK
  have htab : PhaseTableSpec (P + 2) ℓ (phaseTable (P + 2) ℓ) := (h81 (P + 2) ℓ hq hℓq.le).1
  have hdisk : ∀ U : Idx (fftShape a ℓ) → ℂ, (∀ j, OnGrid (P + 2) (U j)) → ‖U‖ ≤ 1 / 8 →
      ∀ j, OnDiskGrid (P + 2) (U j) := by
    intro U hU hU8 j
    exact ⟨hU j, (norm_le_pi_norm U j).trans (hU8.trans (by norm_num))⟩
  have hmain := fun (U : Idx (fftShape a ℓ) → ℂ) (hU : ∀ j, OnGrid (P + 2) (U j))
      (hU8 : ‖U‖ ≤ 1 / 8) =>
    h85 layer (P + 2) D ℓ K a (phaseTable (P + 2) ℓ) hD hℓ hK1 hKℓ ha htab hOK U
      (hdisk U hU hU8)
  refine ⟨Nat.zero_le P, ?_, ?_, ?_, ?_⟩
  · -- `E_mid = 12ℓ ≤ 16 R (lg R + 1)` since `R ≥ 2^ℓ > ℓ`.
    have hlast : fftShape a ℓ (Fin.last D) = 2 ^ ℓ := by simp [fftShape, fftExp]
    have hR : 2 ^ ℓ ≤ totalLen (fftShape a ℓ) := by
      rw [← hlast]
      exact Nat.le_of_dvd (Finset.prod_pos fun i _ => by simp [fftShape])
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
    have hℓR : (ℓ : ℝ) ≤ (totalLen (fftShape a ℓ) : ℝ) := by
      have : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
      exact_mod_cast (this.le.trans hR)
    have hlg : (0 : ℝ) ≤ (lg (totalLen (fftShape a ℓ)) : ℝ) := Nat.cast_nonneg _
    have hR0 : (0 : ℝ) ≤ (totalLen (fftShape a ℓ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hR0 hlg]
  · intro U hU hU8 u
    exact ((hmain U hU hU8).1 u).1
  · intro U hU hU8 u
    exact fitsWidth_of_onDiskGrid ((hmain U hU hU8).1 u)
  · intro U hU hU8
    exact (hmain U hU hU8).2.le

/-- **Corollary 6.6 for the ideal oracle**: the Walsh middle transform built from `idealLayer` is a
middle transform with `E_mid = 12ℓ`, `δ_mid = 0`, under the paper's shape and size hypotheses of
Theorem 6.5 at `q = P + 2` only (no layer hypothesis). -/
theorem walsh_middle_ideal_of (h85 : DirectFFTStmt) (h81 : PhaseTableStmt) (P D ℓ K : ℕ)
    (a : Fin D → ℕ) (hq : 8 ≤ P + 2) (hD : 1 ≤ D) (hℓ : 2 ≤ ℓ) (hℓq : ℓ < P + 2) (hK1 : 1 ≤ K)
    (hKℓ : K ≤ ℓ - 1) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    IsMiddleTransform (fftShape a ℓ) P (12 * (ℓ : ℝ)) 0 (walshMiddle idealLayer (P + 2) D ℓ K a) :=
  walsh_middle_of h85 h81 idealLayer P D ℓ K a hq hD hℓ hℓq hK1 hKℓ ha
    (walshLayerOK_idealLayer _ _ _ _ _)

end SubNLogN.Math.Walsh
