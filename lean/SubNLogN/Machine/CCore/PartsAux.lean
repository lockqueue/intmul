/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.PartsDefs

/-!
# C-core reduction: arithmetic and band lemmas (`CCore/PartsAux.lean`)

Helper lemmas for the `fix` induction (`CCore/Parts.lean`): positivity of `W` and `m`, the child
volume `V/W`, the child group fit, `cDepth` at a leaf, `K ≥ n` above a cutoff, and the cost
inequalities of one call against the recursion `Tm`. Everything is proved; nothing about the
C-core program is used here.
-/

namespace SubNLogN.Machine.CCore.PartsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks SubNLogN.Machine SubNLogN.Machine.CCore

theorem Wn_pos : 0 < Wn := by
  norm_num [Wn, tripleWc, tripleN, tripleV, tripleI, tripleZc]

theorem mn_pos : 0 < mn := by norm_num [mn, tripleM]

/-- The child volume is `V / W` when `W ∣ A`. -/
theorem childRT_volG (t : CCoreRT) (k : ℕ) (a : Fin mn) (b' : ℕ) (hW : Wn ∣ t.A) :
    (childRT t k a b').volG = t.volG / Wn := by
  obtain ⟨A', hA'⟩ := hW
  simp only [CCoreRT.volG, CCoreRT.M, CCoreRT.wg]
  rw [hA', Nat.mul_div_cancel_left A' Wn_pos]
  rw [show 2 * (Wn * A' * t.S * 2 ^ (t.K * t.D)) * t.r * (t.P + 2 * t.Δ + 3) =
      Wn * (2 * (A' * t.S * 2 ^ (t.K * t.D)) * t.r * (t.P + 2 * t.Δ + 3)) by ring,
    Nat.mul_div_cancel_left _ Wn_pos]

/-- The child volume does not depend on the slot and the growth bound. -/
theorem childRT_volG_indep (t : CCoreRT) (k : ℕ) (a a' : Fin mn) (b b' : ℕ) :
    (childRT t k a b).volG = (childRT t k a' b').volG := rfl

/-- The child's encoding is the compact encoding. -/
theorem Enc_childRT (t : CCoreRT) (k : ℕ) (a : Fin mn) (b' : ℕ)
    (hA : 0 < (childRT t k a b').A) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    Enc (childRT t k a b') hA hS w = Enc (compactRT t) hA' hS w := rfl

/-- The child group `j0 + a·m^(k-1), …` of size `m^(k-1)` fits in the parent group. -/
theorem child_fit (t : CCoreRT) (a : Fin mn) (hk : 1 ≤ t.k) (hg : t.j0 + t.e ≤ t.D) :
    t.j0 + a.val * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D := by
  obtain ⟨k', hk'⟩ : ∃ k', t.k = k' + 1 := ⟨t.k - 1, by omega⟩
  have he : t.e = mn * mn ^ k' := by
    simp only [CCoreRT.e, hk', pow_succ]
    ring
  have ha : a.val + 1 ≤ mn := a.isLt
  have h1 : (a.val + 1) * mn ^ k' ≤ mn * mn ^ k' := Nat.mul_le_mul_right _ ha
  rw [he] at hg
  rw [hk', Nat.add_sub_cancel]
  nlinarith [h1]

/-- `cDepth` at a leaf is `8e`. -/
theorem cDepth_leaf (d βn βd Estar k : ℕ) (h : k = 0 ∨ (mn ^ k) ^ βd < d ^ βn) :
    cDepth d βn βd Estar k = 8 * mn ^ k := by
  rcases k with _ | k
  · simp [cDepth]
  · rcases h with h | h
    · exact absurd h (Nat.succ_ne_zero k)
    · simp only [cDepth]
      rw [if_pos h]

/-- `K ≥ n` above a cutoff. -/
theorem exists_K_ge (p : LayerParams) (hOK : p.OK) (n : ℕ) :
    ∃ P₀ : ℕ, ∀ (P₁ : ℕ) (t : CCoreRT), P₀ ≤ P₁ → CCoreBands p P₁ t → n ≤ t.K := by
  obtain ⟨-, -, -, -, -, -, -, -, hc0, hε0, -, -, -, -, -, -, -, -, ha0, -, -, -, -, -, -⟩ := hOK
  refine ⟨⌈((n : ℝ) ^ p.c⁻¹ / p.a_d) ^ p.ε⁻¹⌉₊, fun P₁ t hP₁ ht => ?_⟩
  obtain ⟨hP, hd, -, -, -, hK, -⟩ := ht
  have ha0' : p.a_d ≠ 0 := ha0.ne'
  have hx0 : 0 ≤ (n : ℝ) ^ p.c⁻¹ / p.a_d :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha0.le
  have h1 : ((n : ℝ) ^ p.c⁻¹ / p.a_d) ^ p.ε⁻¹ ≤ (t.P : ℝ) := by
    calc ((n : ℝ) ^ p.c⁻¹ / p.a_d) ^ p.ε⁻¹
        ≤ (⌈((n : ℝ) ^ p.c⁻¹ / p.a_d) ^ p.ε⁻¹⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (P₁ : ℝ) := by exact_mod_cast hP₁
      _ ≤ (t.P : ℝ) := by exact_mod_cast hP
  have h2 : (n : ℝ) ^ p.c⁻¹ / p.a_d ≤ (t.P : ℝ) ^ p.ε := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hx0 _) h1 hε0.le
    rwa [Real.rpow_inv_rpow hx0 hε0.ne'] at h
  have h3 : (n : ℝ) ^ p.c⁻¹ ≤ (t.d : ℝ) := by
    have h4 : (n : ℝ) ^ p.c⁻¹ = p.a_d * ((n : ℝ) ^ p.c⁻¹ / p.a_d) := by field_simp
    rw [h4]
    exact le_trans (mul_le_mul_of_nonneg_left h2 ha0.le) hd
  have h5 : (n : ℝ) ≤ (t.d : ℝ) ^ p.c := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) h3 hc0.le
    rwa [Real.rpow_inv_rpow (Nat.cast_nonneg _) hc0.ne'] at h
  rw [hK]
  exact Nat.le_floor h5

/-- The volume of a call in the bands is positive. -/
theorem volG_pos {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (ht : CCoreBands p P₀ t) :
    1 ≤ t.volG := by
  obtain ⟨-, -, -, hr, -, -, -, hA, hS, -⟩ := ht
  have hr0 : 0 < t.r := by
    have h0 : (0 : ℝ) < (2 : ℝ) ^ (p.a_r * t.P / t.d) := Real.rpow_pos_of_pos (by norm_num) _
    exact_mod_cast lt_of_lt_of_le h0 hr
  have hM : 0 < t.M := by
    simp only [CCoreRT.M]
    exact Nat.mul_pos (Nat.mul_pos hA hS) (Nat.two_pow_pos _)
  have hw : 0 < t.wg := by simp only [CCoreRT.wg]; omega
  simp only [CCoreRT.volG]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hM) hr0) hw

/-- `W^k ∣ A` from the bands. -/
theorem bands_dvd {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (ht : CCoreBands p P₀ t) :
    Wn ^ t.k ∣ t.A := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRA, hWR, -⟩ := ht
  exact dvd_trans hWR hRA

end SubNLogN.Machine.CCore.PartsAux
