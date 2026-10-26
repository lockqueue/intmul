import IntMul.Theorem6And7Barriers
import IntMul.MaterializedAndComputable.MaterializedArrays
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Fin
import WP.W15.DynamicRange
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W15.SyntheticDFT: the unnormalized synthetic DFT `G`, `G Gᵀ = t₁ I`, and `G` = the snapshot's map

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every result in this file is exact linear algebra
about one fixed integer matrix; the lower bound that uses it (`WP.W15.SyntheticDFTLowerBound`) holds
only in the bounded-coefficient linear-circuit model defined in `WP.W15.LinearCircuits`.

**Objects.**
* `negShiftMat r : Matrix (Fin r) (Fin r) ℤ` is multiplication by `y` on `R_r = ℂ[y]/(y^r + 1)` in
  the monomial basis (a signed permutation matrix). Its powers act exactly as the snapshot's
  `negacyclicShiftIter` / `negacyclicShiftIterInt` (`negShiftPow_mulVec_eq_iter`,
  `negShiftPow_mulVec_eq_iterInt`).
* `synDFTMat t₁ r a` is the block matrix `(S^(a·j·v))_{v,j < t₁}`: the **unnormalized** synthetic DFT of
  length `t₁` over `R_r` with root `y^a`.

**What is proved** (for `t₁ = 2^κ`, `r = 2^ρ`, `κ ≤ ρ + 1`, `a = 2^(ρ+1-κ)`, so `a t₁ = 2r`).
* `synDFTMat_mul_transpose`: `G Gᵀ = t₁ • 1`; hence `synDFTMat_det_sq`: `det(G)² = t₁^(t₁ r)`.
* `synDFTMat_mulVec_eq_syntheticDFT` (for `κ ≤ ρ`): `G` applied to the coefficient array of `P` is
  exactly `t₁ · syntheticDFT t₁ r P` (the snapshot's `syntheticDFT`, Preliminaries.lean:283), and
  `synDFTMat_mulVec_eq_syntheticFFTRadix2C`: also `t₁ · syntheticFFTRadix2C` (the snapshot's radix-2
  recursion, Theorem1TwistedDuality.lean:427).
* `radixBMBOperatorInt_eq_synDFTMat`: the snapshot's `M_B` (Theorem6And7Barriers.lean:267) is the case
  `t₁ = B = 2r`, `a = 1`.
-/

namespace WP.W15

open IntMul
open scoped BigOperators Matrix

/-! ## The negacyclic shift matrix -/

/-- Multiplication by `y` on `R_r`: entry `(k, m)` is `±1` iff `finRotate r m = k`, with sign `-1`
exactly when the shift wraps (`k = 0`). -/
def negShiftMat (r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun k m => if finRotate r m = k then (if (k : ℕ) = 0 then -1 else 1) else 0

theorem negShiftMat_mul_transpose (r : ℕ) : negShiftMat r * (negShiftMat r)ᵀ = 1 := by
  ext k k'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, negShiftMat]
  rw [Finset.sum_eq_single ((finRotate r).symm k)]
  · simp only [Equiv.apply_symm_apply, if_true]
    by_cases h : k = k'
    · subst h
      simp only [if_true]
      split_ifs <;> norm_num
    · simp [h]
  · intro m _ hm
    have : finRotate r m ≠ k := fun h => hm (by rw [← h, Equiv.symm_apply_apply])
    simp [-finRotate_apply, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem negShiftMat_transpose_mul (r : ℕ) : (negShiftMat r)ᵀ * negShiftMat r = 1 :=
  mul_eq_one_comm.mp (negShiftMat_mul_transpose r)

/-- The predecessor of `k` modulo `r`, as a natural number. -/
theorem coe_finRotate_symm (r' : ℕ) (k : Fin (r' + 1)) :
    (((finRotate (r' + 1)).symm k : Fin (r' + 1)) : ℕ) = if (k : ℕ) = 0 then r' else (k : ℕ) - 1 := by
  set m0 := (finRotate (r' + 1)).symm k with hm0
  have hk : finRotate (r' + 1) m0 = k := by rw [hm0, Equiv.apply_symm_apply]
  have hcoe : ((finRotate (r' + 1) m0 : Fin (r' + 1)) : ℕ) =
      if m0 = Fin.last r' then 0 else (m0 : ℕ) + 1 := coe_finRotate m0
  rw [hk] at hcoe
  by_cases hlast : m0 = Fin.last r'
  · rw [if_pos hlast] at hcoe
    rw [if_pos hcoe, hlast, Fin.val_last]
  · rw [if_neg hlast] at hcoe
    rw [if_neg (by omega), hcoe]
    omega

/-- Generic one-step negacyclic shift `f ↦ y f` on coefficient sequences (the snapshot's
`negacyclicShiftStep` over `ℂ` and `negacyclicShiftStepInt` over `ℤ` are its instances). -/
def genStep {R : Type*} [Neg R] (r : ℕ) (f : ℕ → R) (k : ℕ) : R :=
  if k = 0 then -f (r - 1) else f (k - 1)

theorem genStep_eq_negacyclicShiftStep (r : ℕ) : genStep (R := ℂ) r = negacyclicShiftStep r := by
  funext f k
  rfl

theorem genStep_eq_negacyclicShiftStepInt (r : ℕ) : genStep (R := ℤ) r = negacyclicShiftStepInt r := by
  funext f k
  rfl

theorem negShiftMat_map_mulVec {R : Type*} [Ring R] (r : ℕ) (g : ℕ → R) (k : Fin r) :
    ((negShiftMat r).map (Int.castRingHom R) *ᵥ fun i : Fin r => g i) k = genStep r g k := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := k.pos; omega⟩
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ((finRotate (r' + 1)).symm k)]
  · simp only [Matrix.map_apply, negShiftMat, Equiv.apply_symm_apply, if_true]
    rw [coe_finRotate_symm]
    unfold genStep
    by_cases h0 : (k : ℕ) = 0
    · simp [h0]
    · simp [h0]
  · intro m _ hm
    have h1 : finRotate (r' + 1) m ≠ k := fun h => hm (by rw [← h, Equiv.symm_apply_apply])
    have h2 : m + 1 ≠ k := by rwa [finRotate_succ_apply] at h1
    simp [Matrix.map_apply, negShiftMat, h2]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem negShiftPow_map_mulVec {R : Type*} [Ring R] (r n : ℕ) (g : ℕ → R) (k : Fin r) :
    ((negShiftMat r ^ n).map (Int.castRingHom R) *ᵥ fun i : Fin r => g i) k =
      (genStep r)^[n] g k := by
  induction n generalizing k with
  | zero =>
    rw [pow_zero, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rfl
  | succ n ih =>
    rw [pow_succ', Matrix.map_mul, ← Matrix.mulVec_mulVec]
    have hfun : ((negShiftMat r ^ n).map (Int.castRingHom R) *ᵥ fun i : Fin r => g i) =
        fun i : Fin r => (genStep r)^[n] g i := funext ih
    rw [hfun, negShiftMat_map_mulVec r ((genStep r)^[n] g) k, Function.iterate_succ_apply']

/-- **Link to the snapshot (ℂ).** `S^n` acts as the snapshot's `negacyclicShiftIter r n`. -/
theorem negShiftPow_mulVec_eq_iter (r n : ℕ) (f : ℕ → ℂ) (k : Fin r) :
    ((negShiftMat r ^ n).map (Int.castRingHom ℂ) *ᵥ fun i : Fin r => f i) k =
      negacyclicShiftIter r n f k := by
  rw [negShiftPow_map_mulVec, genStep_eq_negacyclicShiftStep]
  rfl

/-- **Link to the snapshot (ℤ).** `S^n` acts as the snapshot's `negacyclicShiftIterInt r n`. -/
theorem negShiftPow_mulVec_eq_iterInt (r n : ℕ) (f : ℕ → ℤ) (k : Fin r) :
    ((negShiftMat r ^ n) *ᵥ fun i : Fin r => f i) k = negacyclicShiftIterInt r n f k := by
  have h := negShiftPow_map_mulVec (R := ℤ) r n f k
  have hmap : (negShiftMat r ^ n).map (Int.castRingHom ℤ) = negShiftMat r ^ n := by
    ext i j
    simp
  rw [hmap, genStep_eq_negacyclicShiftStepInt] at h
  exact h

/-- `S^r = -1` (i.e. `y^r = -1` in `R_r`), via the snapshot's `negacyclicShiftIter_r`. -/
theorem negShiftMat_pow_self (r : ℕ) : negShiftMat r ^ r = -1 := by
  ext k m
  have h := negShiftPow_mulVec_eq_iter r r (fun i => if i = (m : ℕ) then 1 else 0) k
  rw [negacyclicShiftIter_r r _ k k.isLt] at h
  have hvec : (fun i : Fin r => (if (i : ℕ) = (m : ℕ) then (1 : ℂ) else 0)) = Pi.single m 1 := by
    funext i
    by_cases hi : i = m
    · subst hi
      simp
    · have : (i : ℕ) ≠ (m : ℕ) := fun h => hi (Fin.ext h)
      simp [hi, this]
  rw [hvec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, eq_intCast] at h
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases hk : k = m
  · subst hk
    rw [if_pos rfl] at h
    rw [if_pos rfl]
    exact_mod_cast h
  · have hkm : (k : ℕ) ≠ (m : ℕ) := fun h => hk (Fin.ext h)
    rw [if_neg hkm, neg_zero] at h
    rw [if_neg hk, neg_zero]
    exact_mod_cast h

/-- `S` as a unit of the matrix ring, with inverse `Sᵀ`. -/
def negShiftUnit (r : ℕ) : (Matrix (Fin r) (Fin r) ℤ)ˣ where
  val := negShiftMat r
  inv := (negShiftMat r)ᵀ
  val_inv := negShiftMat_mul_transpose r
  inv_val := negShiftMat_transpose_mul r

theorem negShiftUnit_pow_self (r : ℕ) : negShiftUnit r ^ r = -1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  exact negShiftMat_pow_self r

theorem negShiftMat_pow_mul_transpose_pow (r p q : ℕ) :
    negShiftMat r ^ p * (negShiftMat r ^ q)ᵀ = (negShiftUnit r ^ ((p : ℤ) - q)).val := by
  have h1 : negShiftMat r ^ p = (negShiftUnit r ^ p).val := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  have h2 : (negShiftMat r ^ q)ᵀ = ((negShiftUnit r)⁻¹ ^ q).val := by
    rw [Matrix.transpose_pow, Units.val_pow_eq_pow_val]
    rfl
  rw [h1, h2, ← Units.val_mul, zpow_sub, zpow_natCast, zpow_natCast, inv_pow]

/-! ## The geometric-sum lemma -/

theorem sum_pow_eq_zero_of_pow_eq_neg_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℤ) (t h : ℕ) (ht : T ^ t = 1) (hh : T ^ h = -1) :
    ∑ j ∈ Finset.range t, T ^ j = 0 := by
  have hper : ∀ j, T ^ (j + t) = T ^ j := fun j => by rw [pow_add, ht, mul_one]
  have hshift := sum_range_shift_of_periodic (fun j => T ^ j) t hper h
  simp only [pow_add, hh, mul_neg, mul_one, Finset.sum_neg_distrib] at hshift
  ext i j
  have := congrFun (congrFun hshift i) j
  simp only [Matrix.neg_apply, Matrix.sum_apply, Matrix.zero_apply] at this ⊢
  linarith

/-! ## The block identity and `G Gᵀ = t₁ I` -/

/-- The unnormalized synthetic DFT of length `t1` over `R_r` with root `y^a`. -/
def synDFTMat (t1 r a : ℕ) : Matrix (Fin t1 × Fin r) (Fin t1 × Fin r) ℤ :=
  fun vk jm => (negShiftMat r ^ (a * (jm.1 : ℕ) * (vk.1 : ℕ))) vk.2 jm.2

theorem odd_part_exists (κ : ℕ) (v v' : Fin (2 ^ κ)) (hne : v ≠ v') :
    ∃ e o : ℕ, e < κ ∧ Odd o ∧ ((v : ℤ) - (v' : ℤ) = 2 ^ e * o ∨ (v : ℤ) - (v' : ℤ) = -(2 ^ e * o)) := by
  have hδ : ((v : ℤ) - (v' : ℤ)).natAbs ≠ 0 := by
    intro h
    apply hne
    apply Fin.ext
    have := Int.natAbs_eq_zero.mp h
    omega
  obtain ⟨e, o, ho, hδeq⟩ := Nat.exists_eq_two_pow_mul_odd hδ
  have hlt : ((v : ℤ) - (v' : ℤ)).natAbs < 2 ^ κ := by
    have hv := v.isLt
    have hv' := v'.isLt
    omega
  have he : e < κ := by
    have h1 : 2 ^ e ≤ ((v : ℤ) - (v' : ℤ)).natAbs := by
      rw [hδeq]
      exact Nat.le_mul_of_pos_right _ ho.pos
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h1 hlt)
  refine ⟨e, o, he, ho, ?_⟩
  rcases Int.natAbs_eq ((v : ℤ) - (v' : ℤ)) with h | h
  · left
    rw [h, hδeq]
    push_cast
    ring
  · right
    rw [h, hδeq]
    push_cast
    ring

theorem synDFT_block (ρ κ : ℕ) (hκ : κ ≤ ρ + 1) (v v' : Fin (2 ^ κ)) :
    ∑ j ∈ Finset.range (2 ^ κ),
        negShiftMat (2 ^ ρ) ^ (2 ^ (ρ + 1 - κ) * j * (v : ℕ)) *
          (negShiftMat (2 ^ ρ) ^ (2 ^ (ρ + 1 - κ) * j * (v' : ℕ)))ᵀ =
      if v = v' then ((2 ^ κ : ℕ) : ℤ) • (1 : Matrix (Fin (2 ^ ρ)) (Fin (2 ^ ρ)) ℤ) else 0 := by
  set U := negShiftUnit (2 ^ ρ) with hU
  set a : ℕ := 2 ^ (ρ + 1 - κ) with ha
  have hat : (a : ℤ) * ((2 ^ κ : ℕ) : ℤ) = ((2 * 2 ^ ρ : ℕ) : ℤ) := by
    rw [ha]
    push_cast
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  set T : (Matrix (Fin (2 ^ ρ)) (Fin (2 ^ ρ)) ℤ)ˣ := U ^ ((a : ℤ) * ((v : ℤ) - (v' : ℤ))) with hT
  have hterm : ∀ j : ℕ, negShiftMat (2 ^ ρ) ^ (a * j * (v : ℕ)) *
      (negShiftMat (2 ^ ρ) ^ (a * j * (v' : ℕ)))ᵀ = T.val ^ j := by
    intro j
    rw [negShiftMat_pow_mul_transpose_pow, ← Units.val_pow_eq_pow_val, hT, ← zpow_natCast,
      ← zpow_mul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  have hU2r : U ^ (2 * 2 ^ ρ) = 1 := by
    rw [pow_mul', hU, negShiftUnit_pow_self]
    norm_num
  have hTt : T.val ^ (2 ^ κ) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hT, ← zpow_natCast, ← zpow_mul]
    have : (a : ℤ) * ((v : ℤ) - (v' : ℤ)) * ((2 ^ κ : ℕ) : ℤ) =
        ((2 * 2 ^ ρ : ℕ) : ℤ) * ((v : ℤ) - (v' : ℤ)) := by
      rw [← hat]
      ring
    rw [this, zpow_mul, zpow_natCast, hU2r, one_zpow, Units.val_one]
  by_cases hvv : v = v'
  · subst hvv
    rw [if_pos rfl]
    have hT1 : T.val = 1 := by
      rw [hT, sub_self, mul_zero, zpow_zero, Units.val_one]
    rw [hT1]
    simp only [one_pow, Finset.sum_const, Finset.card_range]
    rw [natCast_zsmul]
  · rw [if_neg hvv]
    obtain ⟨e, o, he, ho, hδ⟩ := odd_part_exists κ v v' hvv
    have hTh : T.val ^ (2 ^ (κ - 1 - e)) = -1 := by
      rw [← Units.val_pow_eq_pow_val, hT, ← zpow_natCast, ← zpow_mul]
      have hpow : (a : ℤ) * 2 ^ e * ((2 ^ (κ - 1 - e) : ℕ) : ℤ) = ((2 ^ ρ : ℕ) : ℤ) := by
        rw [ha]
        push_cast
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      have hexp : ∃ m : ℤ, Odd m ∧ (a : ℤ) * ((v : ℤ) - (v' : ℤ)) * ((2 ^ (κ - 1 - e) : ℕ) : ℤ) =
          ((2 ^ ρ : ℕ) : ℤ) * m := by
        rcases hδ with h | h
        · refine ⟨o, by exact_mod_cast ho, ?_⟩
          rw [h, ← hpow]
          ring
        · refine ⟨-(o : ℤ), (show Odd (o : ℤ) by exact_mod_cast ho).neg, ?_⟩
          rw [h, ← hpow]
          ring
      obtain ⟨m, hm, hmeq⟩ := hexp
      have hneg : ((-1 : (Matrix (Fin (2 ^ ρ)) (Fin (2 ^ ρ)) ℤ)ˣ)) ^ m = -1 := by
        rw [neg_one_zpow_eq_ite, if_neg (Int.not_even_iff_odd.mpr hm)]
      rw [hmeq, zpow_mul, zpow_natCast, hU, negShiftUnit_pow_self, hneg,
        Units.val_neg, Units.val_one]
    exact sum_pow_eq_zero_of_pow_eq_neg_one _ _ _ hTt hTh

/-- **`G Gᵀ = t₁ I`** for the unnormalized synthetic DFT (`t₁ = 2^κ`, `r = 2^ρ`, `κ ≤ ρ+1`,
root `y^(2^(ρ+1-κ))`). -/
theorem synDFTMat_mul_transpose (ρ κ : ℕ) (hκ : κ ≤ ρ + 1) :
    synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ)) * (synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ)))ᵀ =
      ((2 ^ κ : ℕ) : ℤ) • (1 : Matrix (Fin (2 ^ κ) × Fin (2 ^ ρ)) (Fin (2 ^ κ) × Fin (2 ^ ρ)) ℤ) := by
  ext ⟨v, k⟩ ⟨v', k'⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.transpose_apply, synDFTMat]
  have hblock := synDFT_block ρ κ hκ v v'
  have hentry := congrFun (congrFun hblock k) k'
  rw [Matrix.sum_apply] at hentry
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hentry
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => ∑ m : Fin (2 ^ ρ), (negShiftMat (2 ^ ρ) ^ (2 ^ (ρ + 1 - κ) * j * (v : ℕ))) k m *
      (negShiftMat (2 ^ ρ) ^ (2 ^ (ρ + 1 - κ) * j * (v' : ℕ))) k' m)] at hentry
  rw [hentry]
  by_cases hv : v = v'
  · subst hv
    by_cases hk : k = k'
    · subst hk
      simp
    · simp [hk]
  · simp [hv]

/-- **`det(G)² = t₁^(t₁ r)`.** -/
theorem synDFTMat_det_sq (ρ κ : ℕ) (hκ : κ ≤ ρ + 1) :
    (synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ))).det ^ 2 = ((2 ^ κ : ℕ) : ℤ) ^ (2 ^ κ * 2 ^ ρ) := by
  have h := congrArg Matrix.det (synDFTMat_mul_transpose ρ κ hκ)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  rw [sq]
  exact h

/-! ## `G` is the snapshot's synthetic DFT -/

/-- **`G` is the snapshot's map.** For `κ ≤ ρ`, applying `G` (over `ℂ`) to the coefficient array of
`P` gives `t₁ · syntheticDFT t₁ r P` (Preliminaries.lean:283). -/
theorem synDFTMat_mulVec_eq_syntheticDFT (ρ κ : ℕ) (hκ : κ ≤ ρ) (P : ℕ → ℕ → ℂ)
    (v : Fin (2 ^ κ)) (k : Fin (2 ^ ρ)) :
    ((synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ))).map (Int.castRingHom ℂ) *ᵥ
        fun jm => P jm.1 jm.2) (v, k) =
      ((2 ^ κ : ℕ) : ℂ) * syntheticDFT (2 ^ κ) (2 ^ ρ) P v k := by
  have hc : 2 * (2 ^ ρ / 2 ^ κ) = 2 ^ (ρ + 1 - κ) := by
    rw [Nat.pow_div hκ (by norm_num), ← pow_succ']
    congr 1
    omega
  have hlhs : ((synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ))).map (Int.castRingHom ℂ) *ᵥ
      fun jm => P jm.1 jm.2) (v, k) =
      ∑ j : Fin (2 ^ κ), negacyclicShiftIter (2 ^ ρ) (2 ^ (ρ + 1 - κ) * (j : ℕ) * (v : ℕ)) (P j) k := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← negShiftPow_mulVec_eq_iter, Matrix.mulVec, dotProduct]
    rfl
  rw [hlhs]
  unfold syntheticDFT
  rw [hc, ← mul_assoc, mul_one_div_cancel (Nat.cast_ne_zero.mpr (pow_ne_zero _ two_ne_zero)),
    one_mul]
  exact Fin.sum_univ_eq_sum_range
    (fun j => negacyclicShiftIter (2 ^ ρ) (2 ^ (ρ + 1 - κ) * j * (v : ℕ)) (P j) k) (2 ^ κ)

/-- …and the snapshot's radix-2 recursion `syntheticFFTRadix2C` (Theorem1TwistedDuality.lean:427). -/
theorem synDFTMat_mulVec_eq_syntheticFFTRadix2C (ρ κ : ℕ) (hκ : κ ≤ ρ) (P : ℕ → ℕ → ℂ)
    (v : Fin (2 ^ κ)) (k : Fin (2 ^ ρ)) :
    ((synDFTMat (2 ^ κ) (2 ^ ρ) (2 ^ (ρ + 1 - κ))).map (Int.castRingHom ℂ) *ᵥ
        fun jm => P jm.1 jm.2) (v, k) =
      ((2 ^ κ : ℕ) : ℂ) * syntheticFFTRadix2C (2 ^ ρ) κ (2 ^ ρ / 2 ^ κ) P v k := by
  rw [synDFTMat_mulVec_eq_syntheticDFT ρ κ hκ, syntheticFFTRadix2C_eq_syntheticDFT]

/-- **`M_B` is the case `t₁ = B = 2r`, `a = 1`.** The snapshot's integer radix-`B` core operator
(Theorem6And7Barriers.lean:267) is `G` with `κ = k`, `ρ = k - 1`. -/
theorem radixBMBOperatorInt_eq_synDFTMat (k : ℕ) (hk : 1 ≤ k) (A : ℕ → ℕ → ℤ)
    (u : Fin (2 ^ k)) (m : Fin (2 ^ (k - 1))) :
    radixBMBOperatorInt (2 ^ k) A u m =
      (synDFTMat (2 ^ k) (2 ^ (k - 1)) (2 ^ ((k - 1) + 1 - k)) *ᵥ fun jm => A jm.1 jm.2) (u, m) := by
  have hB2 : 2 ^ k / 2 = 2 ^ (k - 1) := by
    rw [Nat.pow_div hk (by norm_num)]
  have ha : 2 ^ ((k - 1) + 1 - k) = 1 := by
    rw [show (k - 1) + 1 - k = 0 by omega, pow_zero]
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  unfold radixBMBOperatorInt
  rw [hB2, ← Fin.sum_univ_eq_sum_range
    (fun j => negacyclicShiftIterInt (2 ^ (k - 1)) (j * (u : ℕ)) (A j) (m : ℕ)) (2 ^ k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← negShiftPow_mulVec_eq_iterInt, Matrix.mulVec, dotProduct]
  simp only [synDFTMat, ha, one_mul]

#assert_std_axioms negShiftMat_mul_transpose negShiftPow_mulVec_eq_iter negShiftPow_mulVec_eq_iterInt
  negShiftMat_pow_self negShiftUnit_pow_self sum_pow_eq_zero_of_pow_eq_neg_one synDFT_block
  synDFTMat_mul_transpose synDFTMat_det_sq synDFTMat_mulVec_eq_syntheticDFT
  synDFTMat_mulVec_eq_syntheticFFTRadix2C radixBMBOperatorInt_eq_synDFTMat

#assert_std_axioms negShiftMat_transpose_mul coe_finRotate_symm genStep_eq_negacyclicShiftStep
  genStep_eq_negacyclicShiftStepInt negShiftMat_map_mulVec negShiftPow_map_mulVec
  negShiftMat_pow_mul_transpose_pow odd_part_exists

end WP.W15
