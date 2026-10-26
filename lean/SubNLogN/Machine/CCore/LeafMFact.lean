/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import IntMulTM.SpecFacts

/-!
# C-core leaf kernel: the `M log M` bound (`CCore/LeafMFact.lean`)

**Scope (honest summary).** `leafMFact_holds : LeafMFactStmt p`: in the bands (at any cutoff),
`M · (bitLen M + 1) ≤ c · V_g` with `c = ⌈C_M⌉₊ + 2`. The proof uses the band
`log₂ M ≤ C_M · P`, `r ≥ 1` and `w_g ≥ P + 3`. Proved without `sorry`.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-- **The `M log M` term of the leaf kernel is `O(V_g)`** above some cutoff. -/
def LeafMFactStmt (p : LayerParams) : Prop :=
  ∃ P₀ c : ℕ, ∀ t : CCoreRT, CCoreBands p P₀ t → t.M * (bitLen t.M + 1) ≤ c * t.volG

namespace LeafMFactAux

theorem bitLen_le_of_lt {n j : ℕ} (h : n < 2 ^ j) : bitLen n ≤ j := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.2 h

end LeafMFactAux

/-- The `M log M` bound at any cutoff, with the explicit constant `⌈C_M⌉₊ + 2`. -/
theorem LeafMFactAux.mlogm_le {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (ht : CCoreBands p P₀ t) :
    t.M * (bitLen t.M + 1) ≤ (⌈p.C_M⌉₊ + 2) * t.volG := by
  obtain ⟨-, -, -, hr1, -, -, -, hA, hS, -, -, -, -, hlog⟩ := ht
  have hr : 1 ≤ t.r := by
    have h0 : (0 : ℝ) < t.r := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) hr1
    exact_mod_cast h0
  have hM1 : 1 ≤ t.M := by
    simp only [CCoreRT.M]
    exact Nat.mul_pos (Nat.mul_pos hA hS) (Nat.two_pow_pos _)
  have hMle : (t.M : ℝ) ≤ (2 : ℝ) ^ ((⌈p.C_M⌉₊ * t.P : ℕ) : ℝ) := by
    have hM0 : (0 : ℝ) < t.M := by exact_mod_cast hM1
    have h1 : (t.M : ℝ) ≤ (2 : ℝ) ^ (p.C_M * t.P) :=
      (Real.logb_le_iff_le_rpow (by norm_num) hM0).1 hlog
    have h2 : p.C_M * (t.P : ℝ) ≤ ((⌈p.C_M⌉₊ * t.P : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by norm_num) h2)
  rw [Real.rpow_natCast] at hMle
  have hMle' : t.M ≤ 2 ^ (⌈p.C_M⌉₊ * t.P) := by exact_mod_cast hMle
  have hlt : 2 ^ (⌈p.C_M⌉₊ * t.P) < 2 ^ (⌈p.C_M⌉₊ * t.P + 1) := by
    have h2p : 1 ≤ 2 ^ (⌈p.C_M⌉₊ * t.P) := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hbit : bitLen t.M ≤ ⌈p.C_M⌉₊ * t.P + 1 :=
    LeafMFactAux.bitLen_le_of_lt (lt_of_le_of_lt hMle' hlt)
  have hwg : t.P + 3 ≤ t.wg := by simp only [CCoreRT.wg]; omega
  have hb2 : bitLen t.M + 1 ≤ (⌈p.C_M⌉₊ + 2) * t.wg := by
    have h3 : (⌈p.C_M⌉₊ + 2) * (t.P + 3) ≤ (⌈p.C_M⌉₊ + 2) * t.wg := Nat.mul_le_mul_left _ hwg
    have h4 : ⌈p.C_M⌉₊ * t.P + 2 ≤ (⌈p.C_M⌉₊ + 2) * (t.P + 3) := by
      nlinarith [Nat.zero_le ⌈p.C_M⌉₊, Nat.zero_le t.P]
    omega
  have hV : t.volG = 2 * t.M * t.r * t.wg := rfl
  calc t.M * (bitLen t.M + 1) ≤ t.M * ((⌈p.C_M⌉₊ + 2) * t.wg) := Nat.mul_le_mul_left _ hb2
    _ = (⌈p.C_M⌉₊ + 2) * (1 * t.M * 1 * t.wg) := by ring
    _ ≤ (⌈p.C_M⌉₊ + 2) * t.volG := by
      rw [hV]
      exact Nat.mul_le_mul_left _
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) hr) le_rfl)

theorem leafMFact_holds (p : LayerParams) : LeafMFactStmt p :=
  ⟨0, ⌈p.C_M⌉₊ + 2, fun _ ht => LeafMFactAux.mlogm_le ht⟩

end SubNLogN.Machine.CCore
