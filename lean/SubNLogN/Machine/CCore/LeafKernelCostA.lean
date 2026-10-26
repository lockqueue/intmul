/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernelPhase
import SubNLogN.Machine.CCore.LeafSplitAux
import SubNLogN.Machine.CCore.LeafHdrVol
import SubNLogN.Machine.CCore.LeafMFact

/-!
# C-core leaf kernel: cost of the setup phase (`CCore/LeafKernelCostA.lean`)

**Scope (honest summary).** Bounds for the leaf kernel's cost, used by `leafCost_holds`
(`CCore/LeafKernelCostProof.lean`). In the bands (cutoff `≥ 1`):
* `M ≤ V_g`, `w_g ≤ V_g`, `K·D ≤ M`;
* `costA_le`: the cost `costA` of the setup phase A (`CCore/LeafKernelPhase.lean`) is `O(V_g)`.
The constants depend only on `p`, the kernel constants and `bitLen m`. The term `bitLen m` is
kept symbolic. Everything is proved; nothing about the kernel's runs is used here.
-/

namespace SubNLogN.Machine.CCore.LeafCostAux

open TMFw TMFw.Contracts TMFw.Lib Computability SubNLogN.Machine SubNLogN.Machine.CCore
open SubNLogN.Machine.CCore.LeafKernelAux

theorem bl (n : ℕ) : bitLen n ≤ n := LeafSplitAux.bitLen_le_self' n

theorem M_le_volG {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hb : CCoreBands p P₀ t) :
    t.M ≤ t.volG := by
  have hr := LeafSplitAux.one_le_r_of_bands hb
  have hwg : 1 ≤ t.wg := by simp only [CCoreRT.wg]; omega
  have hV : t.volG = 2 * t.M * t.r * t.wg := rfl
  rw [hV]
  calc t.M = 1 * t.M * 1 * 1 := by ring
    _ ≤ 2 * t.M * t.r * t.wg :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) hr) hwg

theorem one_le_M {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hb : CCoreBands p P₀ t) : 1 ≤ t.M := by
  obtain ⟨-, -, -, -, -, -, -, hA, hS, -⟩ := hb
  simp only [CCoreRT.M]
  exact Nat.mul_pos (Nat.mul_pos hA hS) (Nat.two_pow_pos _)

theorem wg_le_volG {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hb : CCoreBands p P₀ t) :
    t.wg ≤ t.volG := by
  have hr := LeafSplitAux.one_le_r_of_bands hb
  have hM := one_le_M hb
  have hV : t.volG = 2 * t.M * t.r * t.wg := rfl
  rw [hV]
  calc t.wg = 1 * 1 * 1 * t.wg := by ring
    _ ≤ 2 * t.M * t.r * t.wg :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hM) hr) le_rfl

theorem KD_le_M {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hb : CCoreBands p P₀ t) :
    t.K * t.D ≤ t.M := by
  obtain ⟨-, -, -, -, -, -, -, hA, hS, -⟩ := hb
  exact le_trans (Nat.lt_two_pow_self).le (LeafSplitAux.two_pow_le_M t hA hS)

theorem costA1_le {P Δ V : ℕ} (hP : P ≤ V) (hΔ : Δ ≤ V) (hV : 1 ≤ V) :
    costA1 P Δ ≤ 304 * V := by
  have h3 := bl 3
  have hbP := le_trans (bl P) hP
  have hbΔ := le_trans (bl Δ) hΔ
  have hbPΔ : bitLen (P + Δ) ≤ 2 * V := le_trans (bl _) (by omega)
  have hbΔ3 : bitLen (Δ + 3) ≤ V + 3 := le_trans (bl _) (by omega)
  simp only [costA1]
  omega

theorem costA2_le {k V : ℕ} (hk : (k + 1) ^ 3 ≤ V) (hV : 1 ≤ V) :
    costA2 k ≤ (200 * (bitLen mn + 3) ^ 2 + 2) * V := by
  have h1 := bl 1
  have hpow : bitLen (1 * mn ^ k) ≤ k * bitLen mn + 1 := by
    rw [one_mul]; exact LeafHdrAux.bitLen_pow_le mn k
  have hsum : bitLen (1 * mn ^ k) + bitLen mn + 2 ≤ (bitLen mn + 3) * (k + 1) := by
    nlinarith [hpow]
  have hsq : (bitLen (1 * mn ^ k) + bitLen mn + 2) ^ 2 ≤ (bitLen mn + 3) ^ 2 * (k + 1) ^ 2 := by
    calc (bitLen (1 * mn ^ k) + bitLen mn + 2) ^ 2 ≤ ((bitLen mn + 3) * (k + 1)) ^ 2 :=
          Nat.pow_le_pow_left hsum 2
      _ = (bitLen mn + 3) ^ 2 * (k + 1) ^ 2 := by ring
  have hpc : NatArith.powCost mn 1 k ≤ 200 * (bitLen mn + 3) ^ 2 * V := by
    unfold NatArith.powCost
    calc (k + 1) * (200 * (bitLen (1 * mn ^ k) + bitLen mn + 2) ^ 2)
        ≤ (k + 1) * (200 * ((bitLen mn + 3) ^ 2 * (k + 1) ^ 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsq)
      _ = 200 * (bitLen mn + 3) ^ 2 * (k + 1) ^ 3 := by ring
      _ ≤ 200 * (bitLen mn + 3) ^ 2 * V := Nat.mul_le_mul_left _ hk
  have e : (200 * (bitLen mn + 3) ^ 2 + 2) * V = 200 * (bitLen mn + 3) ^ 2 * V + 2 * V := by ring
  simp only [costA2]
  rw [e]
  omega

/-- `mulCost a b ≤ 400 · cM · V` when `a, b ≤ M` and `M (bitLen M + 1) ≤ cM · V`. -/
theorem mulCost_le {a b M V cM : ℕ} (ha : a ≤ M) (hb : b ≤ M) (hM : 1 ≤ M)
    (hmf : M * (bitLen M + 1) ≤ cM * V) : NatArith.mulCost a b ≤ 400 * cM * V := by
  have hla : bitLen a ≤ bitLen M := NatArith.bitLen_mono'' ha
  have hlb : bitLen b ≤ bitLen M := NatArith.bitLen_mono'' hb
  have hLM : bitLen M + 1 ≤ 2 * M := by have := bl M; omega
  unfold NatArith.mulCost
  calc 100 * (bitLen a + 1) * (bitLen a + bitLen b + 2)
      ≤ 100 * (bitLen M + 1) * (2 * (bitLen M + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ = 200 * ((bitLen M + 1) * (bitLen M + 1)) := by ring
    _ ≤ 200 * ((2 * M) * (bitLen M + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hLM)
    _ = 400 * (M * (bitLen M + 1)) := by ring
    _ ≤ 400 * (cM * V) := Nat.mul_le_mul_left _ hmf
    _ = 400 * cM * V := by ring

theorem costA3_le {C3 K D j0 ρ M V cM : ℕ} (hD : D ≤ V) (hj : j0 ≤ V) (hρ : ρ ≤ V)
    (hKM : K ≤ M) (hDM : D ≤ M) (hKD : K * D ≤ V) (hM : 1 ≤ M) (hV : 1 ≤ V)
    (hmf : M * (bitLen M + 1) ≤ cM * V) :
    costA3 C3 K D j0 ρ ≤ (120 + 2 * C3 + 400 * cM) * V := by
  have hbD := le_trans (bl D) hD
  have hbj := le_trans (bl j0) hj
  have hbρ := le_trans (bl ρ) hρ
  have hz : zerosLead (encodeNat (D - j0 - 1 + 1)) ≤ V :=
    le_trans (zerosLead_le_length _) (le_trans (bl _) (by omega))
  have hmul := mulCost_le (a := K) (b := D - j0 - 1) hKM (by omega) hM hmf
  have hKx : K * (D - j0 - 1) ≤ V := le_trans (Nat.mul_le_mul_left _ (by omega)) hKD
  have hbKx := le_trans (bl (K * (D - j0 - 1))) hKx
  have hC3 : C3 * (zerosLead (encodeNat (D - j0 - 1 + 1)) + 1) ≤ 2 * C3 * V := by
    calc C3 * (zerosLead (encodeNat (D - j0 - 1 + 1)) + 1) ≤ C3 * (V + V) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * C3 * V := by ring
  have e : (120 + 2 * C3 + 400 * cM) * V = 120 * V + 2 * C3 * V + 400 * cM * V := by ring
  simp only [costA3]
  rw [e]
  omega

theorem costA4_le {C1 S x0 V : ℕ} (hS : S ≤ V) (hx : x0 ≤ 2 * V) (hV : 1 ≤ V) :
    costA4 C1 S x0 ≤ (14 + 5 * C1) * V := by
  have hbS := le_trans (bl S) hS
  have hbx := le_trans (bl x0) hx
  have hC1 : C1 * (x0 + bitLen x0 + 1) ≤ 5 * C1 * V := by
    calc C1 * (x0 + bitLen x0 + 1) ≤ C1 * (5 * V) := Nat.mul_le_mul_left _ (by omega)
      _ = 5 * C1 * V := by ring
  have e : (14 + 5 * C1) * V = 14 * V + 5 * C1 * V := by ring
  simp only [costA4]
  rw [e]
  omega

theorem costDrops_le {aP aΔ aD aS aj ak aρ a3 a1 a2 ay3 ay4 ax0 V : ℕ}
    (h1 : aP ≤ 2 * V + 3) (h2 : aΔ ≤ 2 * V + 3) (h3 : aD ≤ 2 * V + 3) (h4 : aS ≤ 2 * V + 3)
    (h5 : aj ≤ 2 * V + 3) (h6 : ak ≤ 2 * V + 3) (h7 : aρ ≤ 2 * V + 3) (h8 : a3 ≤ 2 * V + 3)
    (h9 : a1 ≤ 2 * V + 3) (h10 : a2 ≤ 2 * V + 3) (h11 : ay3 ≤ 2 * V + 3)
    (h12 : ay4 ≤ 2 * V + 3) (h13 : ax0 ≤ 2 * V + 3) (hV : 1 ≤ V) :
    costDrops aP aΔ aD aS aj ak aρ a3 a1 a2 ay3 ay4 ax0 ≤ 182 * V := by
  have b1 := bl aP; have b2 := bl aΔ; have b3 := bl aD; have b4 := bl aS; have b5 := bl aj
  have b6 := bl ak; have b7 := bl aρ; have b8 := bl a3; have b9 := bl a1; have b10 := bl a2
  have b11 := bl ay3; have b12 := bl ay4; have b13 := bl ax0
  simp only [costDrops]
  omega

/-- **The setup phase A costs `O(V_g)`** (cutoff `≥ 1`). -/
theorem costA_le (p : LayerParams) (C1 C3 : ℕ) : ∃ c : ℕ, ∀ (P₀ : ℕ) (t : CCoreRT), 1 ≤ P₀ →
    CCoreBands p P₀ t → costA C1 C3 t.P t.Δ t.K t.D t.S t.j0 t.k t.ρ ≤ c * t.volG := by
  refine ⟨304 + (200 * (bitLen mn + 3) ^ 2 + 2) + (120 + 2 * C3 + 400 * (⌈p.C_M⌉₊ + 2)) +
    (14 + 5 * C1) + 182, fun P₀ t hP hb => ?_⟩
  obtain ⟨hPV, -, hΔV, -, -, -, hDV, hSV, hjeV, hk3V, hρV, h1V, -⟩ :=
    LeafHdrAux.hdrFields_le_volG hb hP
  have hMV := M_le_volG hb
  have hM1 := one_le_M hb
  have hKDM := KD_le_M hb
  have hmf := LeafMFactAux.mlogm_le hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hjD, hρK, -⟩ := hb
  have he1 := LeafSplitAux.one_le_e t
  have hK1 : 1 ≤ t.K := by omega
  have hD1 : 1 ≤ t.D := by omega
  have hKM : t.K ≤ t.M := le_trans (Nat.le_mul_of_pos_right _ hD1) hKDM
  have hDM : t.D ≤ t.M := le_trans (Nat.le_mul_of_pos_left _ hK1) hKDM
  have hk : t.k ≤ t.volG :=
    le_trans (le_trans (Nat.le_succ _) (Nat.le_self_pow (by norm_num) _)) hk3V
  have hj : t.j0 ≤ t.volG := by omega
  have hKx : t.K * (t.D - t.j0 - 1) ≤ t.volG :=
    le_trans (Nat.mul_le_mul_left _ (by omega)) (le_trans hKDM hMV)
  have h1 := costA1_le hPV hΔV h1V
  have h2 := costA2_le hk3V h1V
  have h3 := costA3_le (C3 := C3) hDV hj hρV.le hKM hDM (le_trans hKDM hMV) hM1 h1V hmf
  have h4 := costA4_le (C1 := C1) (x0 := t.ρ + t.K * (t.D - t.j0 - 1)) hSV (by omega) h1V
  have h5 := costDrops_le (aP := t.P) (aΔ := t.Δ) (aD := t.D) (aS := t.S) (aj := t.j0)
    (ak := t.k) (aρ := t.ρ) (a3 := 3) (a1 := t.P + t.Δ) (a2 := t.Δ + 3)
    (ay3 := t.D - t.j0 - 1) (ay4 := t.K * (t.D - t.j0 - 1))
    (ax0 := t.ρ + t.K * (t.D - t.j0 - 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h1V
  have e : (304 + (200 * (bitLen mn + 3) ^ 2 + 2) + (120 + 2 * C3 + 400 * (⌈p.C_M⌉₊ + 2)) +
      (14 + 5 * C1) + 182) * t.volG = 304 * t.volG + (200 * (bitLen mn + 3) ^ 2 + 2) * t.volG +
      (120 + 2 * C3 + 400 * (⌈p.C_M⌉₊ + 2)) * t.volG + (14 + 5 * C1) * t.volG +
      182 * t.volG := by ring
  simp only [costA]
  rw [e]
  omega

end SubNLogN.Machine.CCore.LeafCostAux
