import WP.W15.LinearCircuits
import WP.W15.SyntheticDFT
import Mathlib.Analysis.Complex.Basic
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W15.SyntheticDFTLowerBound: Morgenstern's bound for the snapshot's synthetic DFT

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every result in this file holds only in the
restricted model defined explicitly in `WP.W15.LinearCircuits`: exact fan-in-2 linear circuits over
`ℂ` whose coefficients have modulus `≤ 1`. Finite-ring arithmetic, Kronecker substitution, bit
slicing, table lookup, SWAR, fast matrix multiplication (unbounded constants) and the rounded
fixed-point computation that the snapshot actually executes all lie outside this model.

**What is proved** (`t₁ = 2^κ`, `r = 2^ρ`, `κ ≤ ρ + 1`; `synDFTMatC ρ κ` is the unnormalized
synthetic DFT `G` over `ℂ`, indexed by `Fin (t₁ r)`).
* `synDFT_twoInputGates_lower_bound`: every circuit with coefficients of modulus `≤ 1` that computes
  `G` has at least `(κ · t₁ · r) / 2 = (t₁ r log₂ t₁)/2` genuinely two-input gates.
* `synDFT_exists_circuit`: such circuits exist (the bound is not vacuous).
* `synDFTMatC_apply_eq_syntheticDFT`: for `κ ≤ ρ`, `G` is `t₁` times the snapshot's `syntheticDFT`
  (equivalently its radix-2 recursion `syntheticFFTRadix2C`), so the bound is a statement about the
  map the snapshot's synthetic-FFT stage computes (exactly, before rounding).
* `MB_twoInputGates_lower_bound`: the snapshot's `M_B` (`B = 2^k`) needs at least
  `k · N_B / 2` two-input gates, `N_B = B²/2`.
* `syntheticDFT_twoInputGates_lower_bound` and `radixBMBOperatorInt_twoInputGates_lower_bound`: the
  same bounds stated against the snapshot's definitions directly, for every matrix that realizes
  `P ↦ t₁ · syntheticDFT t₁ r P` (resp. `radixBMBOperatorInt (2^k)`); such a matrix is `synDFTMatC`
  (`eq_synDFTMatC_of_syntheticDFT`, `matrix_eq_of_int_apply`, `synDFTMatC_MB_apply`).
The radix-2 synthetic FFT (unnormalized butterflies `A ± y^s B`) uses exactly `t₁ r log₂ t₁` two-input
`±1` gates (the snapshot's own count, `syntheticFFTRadix2AddOps r κ = κ · 2^κ · r`,
Theorem5ComplexityAndCorrectness.lean:613), so it is optimal within a factor of `2` in this model; the
explicit circuit instance is not formalized here.
-/

namespace WP.W15

open IntMul
open scoped BigOperators Matrix

/-- `G` over `ℂ`, reindexed to `Fin (t₁ r)` (the index type of `LinSLP` inputs and outputs). -/
noncomputable def synDFTMatC (ρ κ : ℕ) : Matrix (Fin (2 ^ κ * 2 ^ ρ)) (Fin (2 ^ κ * 2 ^ ρ)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ))).map (Int.castRingHom ℂ))

theorem synDFTMatC_det_sq (ρ κ : ℕ) (hκ : κ ≤ ρ + 1) :
    (synDFTMatC ρ κ).det ^ 2 = ((2 ^ κ : ℕ) : ℂ) ^ (2 ^ κ * 2 ^ ρ) := by
  have hdet : (synDFTMatC ρ κ).det =
      Int.castRingHom ℂ (synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ))).det := by
    unfold synDFTMatC
    rw [Matrix.det_reindex_self, RingHom.map_det]
    rfl
  rw [hdet, ← map_pow, synDFTMat_det_sq ρ κ hκ, map_pow, map_natCast]

/-- Entries of `S^n` are `-1`, `0` or `1`. -/
theorem negShiftPow_entry_abs_le (r n : ℕ) (k m : Fin r) : |(negShiftMat r ^ n) k m| ≤ 1 := by
  have h := negShiftPow_mulVec_eq_iterInt r n (fun i => if i = (m : ℕ) then 1 else 0) k
  have hvec : (fun i : Fin r => (if (i : ℕ) = (m : ℕ) then (1 : ℤ) else 0)) = Pi.single m 1 := by
    funext i
    by_cases hi : i = m
    · subst hi
      simp
    · have : (i : ℕ) ≠ (m : ℕ) := fun h => hi (Fin.ext h)
      simp [hi, this]
  rw [hvec, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h, negacyclicShiftIterInt_eq_sourceAndSign, abs_mul,
    (negacyclicShiftSourceAndSign_sq_eq_one r n k).2, one_mul]
  split_ifs <;> simp

theorem synDFTMatC_entry_norm_le (ρ κ : ℕ) (i j : Fin (2 ^ κ * 2 ^ ρ)) :
    ‖synDFTMatC ρ κ i j‖ ≤ 1 := by
  unfold synDFTMatC
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, eq_intCast,
    Complex.norm_intCast]
  have h := negShiftPow_entry_abs_le (2 ^ ρ)
    (2 ^ (ρ + 1 - κ) * ((finProdFinEquiv.symm j).1 : ℕ) * ((finProdFinEquiv.symm i).1 : ℕ))
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
  unfold synDFTMat
  exact_mod_cast h

/-- **Non-vacuity.** Some circuit with coefficients of modulus `≤ 1` computes `G`. -/
theorem synDFT_exists_circuit (ρ κ : ℕ) :
    ∃ P : LinSLP ℂ (2 ^ κ * 2 ^ ρ), P.CoeffsLeOne ∧ P.Computes (synDFTMatC ρ κ) :=
  LinSLP.exists_computes _ (synDFTMatC_entry_norm_le ρ κ)

/-- **Lower bound for the synthetic DFT in model (b).** Every fan-in-2 linear circuit over `ℂ` with
coefficients of modulus `≤ 1` that computes the unnormalized synthetic DFT `G` (`t₁ = 2^κ`, `r = 2^ρ`)
has at least `κ · t₁ · r / 2 = (t₁ r log₂ t₁)/2` genuinely two-input gates. -/
theorem synDFT_twoInputGates_lower_bound (ρ κ : ℕ) (hκ : κ ≤ ρ + 1)
    (P : LinSLP ℂ (2 ^ κ * 2 ^ ρ)) (hP : P.CoeffsLeOne) (hcomp : P.Computes (synDFTMatC ρ κ)) :
    κ * 2 ^ κ * 2 ^ ρ ≤ 2 * P.twoInputGates := by
  have h1 := P.norm_det_le_two_pow hP hcomp
  have h2 : ‖(synDFTMatC ρ κ).det‖ ^ 2 = (2 : ℝ) ^ (κ * (2 ^ κ * 2 ^ ρ)) := by
    rw [← norm_pow, synDFTMatC_det_sq ρ κ hκ, norm_pow, Complex.norm_natCast]
    push_cast
    rw [← pow_mul]
  have h3 : (2 : ℝ) ^ (κ * (2 ^ κ * 2 ^ ρ)) ≤ (2 : ℝ) ^ (2 * P.twoInputGates) := by
    rw [← h2, mul_comm 2 P.twoInputGates, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h3
  calc κ * 2 ^ κ * 2 ^ ρ = κ * (2 ^ κ * 2 ^ ρ) := by ring
    _ ≤ 2 * P.twoInputGates := h4

/-- The rows of `synDFTMatC` are the snapshot's synthetic DFT (×`t₁`): applying `G` to the coefficient
array of `P` reproduces `t₁ · syntheticDFT t₁ r P` at every output coefficient. -/
theorem synDFTMatC_apply_eq_syntheticDFT (ρ κ : ℕ) (hκ : κ ≤ ρ) (P : ℕ → ℕ → ℂ)
    (v : Fin (2 ^ κ)) (k : Fin (2 ^ ρ)) :
    (synDFTMatC ρ κ *ᵥ fun x => P (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2)
        (finProdFinEquiv (v, k)) =
      ((2 ^ κ : ℕ) : ℂ) * syntheticDFT (2 ^ κ) (2 ^ ρ) P v k := by
  rw [← synDFTMat_mulVec_eq_syntheticDFT ρ κ hκ P v k]
  unfold synDFTMatC
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- **Corollary for `M_B`** (`B = 2^k`, `N_B = B²/2`): the snapshot's radix-`B` core operator is
`G` with `κ = k`, `ρ = k - 1` (`radixBMBOperatorInt_eq_synDFTMat`), so every such circuit computing it
has at least `k · N_B / 2` two-input gates. -/
theorem MB_twoInputGates_lower_bound (k : ℕ) (hk : 1 ≤ k)
    (P : LinSLP ℂ (2 ^ k * 2 ^ (k - 1))) (hP : P.CoeffsLeOne)
    (hcomp : P.Computes (synDFTMatC (k - 1) k)) :
    k * (2 ^ k * 2 ^ (k - 1)) ≤ 2 * P.twoInputGates := by
  have := synDFT_twoInputGates_lower_bound (k - 1) k (by omega) P hP hcomp
  calc k * (2 ^ k * 2 ^ (k - 1)) = k * 2 ^ k * 2 ^ (k - 1) := by ring
    _ ≤ 2 * P.twoInputGates := this

/-! ## The bounds stated against the snapshot's definitions directly

The next theorems do not ask the reader to trust the encoding `synDFTMatC`: any complex matrix that
realizes the snapshot's map (`syntheticDFT`, resp. `radixBMBOperatorInt`) on coefficient arrays is
`synDFTMatC`, so the gate bound applies to every circuit that computes the snapshot's map. -/

/-- A square complex matrix on `Fin (n₁ n₂)` is determined by its action on integer arrays. -/
theorem matrix_eq_of_int_apply {n₁ n₂ : ℕ} (A B : Matrix (Fin (n₁ * n₂)) (Fin (n₁ * n₂)) ℂ)
    (h : ∀ X : ℕ → ℕ → ℤ,
      (A *ᵥ fun x => ((X (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 : ℤ) : ℂ)) =
        B *ᵥ fun x => ((X (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 : ℤ) : ℂ)) :
    A = B := by
  ext i j
  have hvec : (fun x : Fin (n₁ * n₂) =>
      (((if ((finProdFinEquiv.symm x).1 : ℕ) = ((finProdFinEquiv.symm j).1 : ℕ) ∧
          ((finProdFinEquiv.symm x).2 : ℕ) = ((finProdFinEquiv.symm j).2 : ℕ) then 1 else 0 : ℤ)) :
        ℂ)) = Pi.single j 1 := by
    funext x
    by_cases hx : x = j
    · subst hx
      simp
    · have hne : ¬ (((finProdFinEquiv.symm x).1 : ℕ) = ((finProdFinEquiv.symm j).1 : ℕ) ∧
          ((finProdFinEquiv.symm x).2 : ℕ) = ((finProdFinEquiv.symm j).2 : ℕ)) := by
        rintro ⟨h1, h2⟩
        apply hx
        apply finProdFinEquiv.symm.injective
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)
      rw [if_neg hne, Pi.single_eq_of_ne hx]
      simp
  have hj := congrFun (h fun a b => if a = ((finProdFinEquiv.symm j).1 : ℕ) ∧
      b = ((finProdFinEquiv.symm j).2 : ℕ) then 1 else 0) i
  rw [hvec, Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.col_apply] at hj
  exact hj

/-- Any matrix realizing `P ↦ t₁ · syntheticDFT t₁ r P` (the snapshot's map) is `synDFTMatC`. -/
theorem eq_synDFTMatC_of_syntheticDFT (ρ κ : ℕ) (hκ : κ ≤ ρ)
    (A : Matrix (Fin (2 ^ κ * 2 ^ ρ)) (Fin (2 ^ κ * 2 ^ ρ)) ℂ)
    (hA : ∀ (P : ℕ → ℕ → ℂ) (v : Fin (2 ^ κ)) (k : Fin (2 ^ ρ)),
      (A *ᵥ fun x => P (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2)
          (finProdFinEquiv (v, k)) =
        ((2 ^ κ : ℕ) : ℂ) * syntheticDFT (2 ^ κ) (2 ^ ρ) P v k) :
    A = synDFTMatC ρ κ := by
  apply matrix_eq_of_int_apply
  intro X
  funext i
  obtain ⟨⟨v, k⟩, rfl⟩ := finProdFinEquiv.surjective i
  have h1 := hA (fun a b => (X a b : ℂ)) v k
  have h2 := synDFTMatC_apply_eq_syntheticDFT ρ κ hκ (fun a b => (X a b : ℂ)) v k
  exact h1.trans h2.symm

/-- **Morgenstern bound for the snapshot's synthetic DFT.** Every fan-in-2 linear circuit over `ℂ`
with coefficients of modulus `≤ 1` that computes the linear map `P ↦ t₁ · syntheticDFT t₁ r P`
(snapshot, Preliminaries.lean:283; `t₁ = 2^κ ≤ r = 2^ρ`) has at least `(t₁ r log₂ t₁)/2` two-input
gates. Non-vacuous: `synDFTMatC` realizes the map (`synDFTMatC_apply_eq_syntheticDFT`) and is
computed by such circuits (`synDFT_exists_circuit`). -/
theorem syntheticDFT_twoInputGates_lower_bound (ρ κ : ℕ) (hκ : κ ≤ ρ)
    (A : Matrix (Fin (2 ^ κ * 2 ^ ρ)) (Fin (2 ^ κ * 2 ^ ρ)) ℂ)
    (hA : ∀ (P : ℕ → ℕ → ℂ) (v : Fin (2 ^ κ)) (k : Fin (2 ^ ρ)),
      (A *ᵥ fun x => P (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2)
          (finProdFinEquiv (v, k)) =
        ((2 ^ κ : ℕ) : ℂ) * syntheticDFT (2 ^ κ) (2 ^ ρ) P v k)
    (C : LinSLP ℂ (2 ^ κ * 2 ^ ρ)) (hC : C.CoeffsLeOne) (hcomp : C.Computes A) :
    κ * 2 ^ κ * 2 ^ ρ ≤ 2 * C.twoInputGates := by
  rw [eq_synDFTMatC_of_syntheticDFT ρ κ hκ A hA] at hcomp
  exact synDFT_twoInputGates_lower_bound ρ κ (by omega) C hC hcomp

/-- `synDFTMatC (k-1) k` realizes the snapshot's integer `M_B` (`B = 2^k`) on integer arrays. -/
theorem synDFTMatC_MB_apply (k : ℕ) (hk : 1 ≤ k) (X : ℕ → ℕ → ℤ) (u : Fin (2 ^ k))
    (m : Fin (2 ^ (k - 1))) :
    (synDFTMatC (k - 1) k *ᵥ
        fun x => ((X (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 : ℤ) : ℂ))
        (finProdFinEquiv (u, m)) = (radixBMBOperatorInt (2 ^ k) X u m : ℂ) := by
  rw [radixBMBOperatorInt_eq_synDFTMat k hk X u m]
  unfold synDFTMatC
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, ← Equiv.sum_comp finProdFinEquiv]
  push_cast
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- **Morgenstern bound for the snapshot's `M_B`** (`B = 2^k`, `N_B = B²/2`). Every fan-in-2 linear
circuit over `ℂ` with coefficients of modulus `≤ 1` that computes a matrix realizing the snapshot's
`radixBMBOperatorInt (2^k)` (Theorem6And7Barriers.lean:267) on integer arrays has at least
`k · N_B / 2` two-input gates. Non-vacuous by `synDFTMatC_MB_apply` and `synDFT_exists_circuit`. -/
theorem radixBMBOperatorInt_twoInputGates_lower_bound (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin (2 ^ k * 2 ^ (k - 1))) (Fin (2 ^ k * 2 ^ (k - 1))) ℂ)
    (hA : ∀ (X : ℕ → ℕ → ℤ) (u : Fin (2 ^ k)) (m : Fin (2 ^ (k - 1))),
      (A *ᵥ fun x => ((X (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 : ℤ) : ℂ))
          (finProdFinEquiv (u, m)) = (radixBMBOperatorInt (2 ^ k) X u m : ℂ))
    (C : LinSLP ℂ (2 ^ k * 2 ^ (k - 1))) (hC : C.CoeffsLeOne) (hcomp : C.Computes A) :
    k * (2 ^ k * 2 ^ (k - 1)) ≤ 2 * C.twoInputGates := by
  have hAeq : A = synDFTMatC (k - 1) k := by
    apply matrix_eq_of_int_apply
    intro X
    funext i
    obtain ⟨⟨u, m⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [hA X u m, synDFTMatC_MB_apply k hk X u m]
  rw [hAeq] at hcomp
  exact MB_twoInputGates_lower_bound k hk C hC hcomp

#assert_std_axioms synDFTMatC_det_sq negShiftPow_entry_abs_le synDFTMatC_entry_norm_le
  synDFT_exists_circuit synDFT_twoInputGates_lower_bound synDFTMatC_apply_eq_syntheticDFT
  MB_twoInputGates_lower_bound matrix_eq_of_int_apply eq_synDFTMatC_of_syntheticDFT
  syntheticDFT_twoInputGates_lower_bound synDFTMatC_MB_apply
  radixBMBOperatorInt_twoInputGates_lower_bound

end WP.W15
