/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernelCost
import SubNLogN.Machine.CCore.LeafKernelCostA

/-!
# C-core leaf kernel: the cost bound (`CCore/LeafKernelCostProof.lean`)

**Scope (honest summary).** `leafCost_holds : LeafKernelAux.LeafCostStmt p`. For every choice of
the kernel cost constants, the exact step bound `leafCost` of the leaf program
(`CCore/LeafKernelCost.lean`) is at most `C · e · V_g` above a cutoff. The terms are bounded as
follows:
* the header term by `hdrLen_holds`;
* the setup phase by `costA_le` (`CCore/LeafKernelCostA.lean`);
* each of the `e` loop iterations by `costL_le`, which uses `M (bitLen M + 1) = O(V_g)`
  (`LeafMFactAux.mlogm_le`) and `wSel ≤ M`;
* the final phase by `costC_le`.
Proved without `sorry`.
-/

namespace SubNLogN.Machine.CCore.LeafCostAux

open TMFw TMFw.Contracts TMFw.Lib Computability SubNLogN.Machine SubNLogN.Machine.CCore
open SubNLogN.Machine.CCore.LeafKernelAux

theorem costL_le {Cc C2 C3 V M W0 w Kv e cM : ℕ} (hV : 1 ≤ V) (hW0 : W0 ≤ M)
    (hmf : M * (bitLen M + 1) ≤ cM * V) (hw : w ≤ V) (hK : Kv ≤ V) (he : e ≤ V) :
    costL Cc C2 C3 (2 * V) M W0 w Kv e ≤ (Cc * (4 + cM) + 3 * C2 + 2 * C3 + 1) * V := by
  have hbW : bitLen W0 ≤ bitLen M := NatArith.bitLen_mono'' hW0
  have h1 : M * (bitLen W0 + 1) ≤ cM * V := le_trans (Nat.mul_le_mul_left _ (by omega)) hmf
  have hbK := le_trans (bl Kv) hK
  have hbe := le_trans (bl e) he
  have i1 : Cc * (2 * V + M * (bitLen W0 + 1) + w + 1) ≤ Cc * (4 + cM) * V := by
    calc Cc * (2 * V + M * (bitLen W0 + 1) + w + 1) ≤ Cc * ((4 + cM) * V) := by
          apply Nat.mul_le_mul_left
          have : (4 + cM) * V = 4 * V + cM * V := by ring
          omega
      _ = Cc * (4 + cM) * V := by ring
  have i2 : C2 * (Kv + bitLen Kv + 1) ≤ 3 * C2 * V := by
    calc C2 * (Kv + bitLen Kv + 1) ≤ C2 * (3 * V) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * C2 * V := by ring
  have i3 : C3 * (bitLen e + 1) ≤ 2 * C3 * V := by
    calc C3 * (bitLen e + 1) ≤ C3 * (2 * V) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * C3 * V := by ring
  have e' : (Cc * (4 + cM) + 3 * C2 + 2 * C3 + 1) * V =
      Cc * (4 + cM) * V + 3 * C2 * V + 2 * C3 * V + V := by ring
  simp only [costL]
  rw [e']
  omega

theorem costC_le {wE wg Kv V : ℕ} (hE : wE ≤ V) (hw : wg ≤ V) (hK : Kv ≤ V) (hV : 1 ≤ V) :
    costC wE wg Kv ≤ 18 * V := by
  have h1 := le_trans (bl wE) hE
  have h2 := le_trans (bl wg) hw
  have h3 := le_trans (bl Kv) hK
  simp only [costC]
  omega

theorem layerAddrs_length_M (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) :
    (layerAddrs t.A t.K t.D t.S hA hS).length = t.M := by
  unfold layerAddrs
  rw [List.length_map, List.length_range]
  simp only [CCoreRT.M]
  ring

theorem wSel_le_M (t : CCoreRT) (hA : 0 < t.A) (hρ : t.ρ < t.K) (hj : t.j0 < t.D) :
    wSel t.K t.D t.S t.ρ t.j0 ≤ t.M := by
  unfold wSel
  have hpos := LeafKernelAux.pos_lt (K := t.K) (D := t.D) (j := t.j0) (k := t.ρ) hj hρ
  have h2 : 2 ^ (t.ρ + t.K * (t.D - 1 - t.j0)) ≤ 2 ^ (t.K * t.D) :=
    Nat.pow_le_pow_right (by norm_num) hpos.le
  simp only [CCoreRT.M]
  calc t.S * 2 ^ (t.ρ + t.K * (t.D - 1 - t.j0)) ≤ t.S * 2 ^ (t.K * t.D) :=
        Nat.mul_le_mul_left _ h2
    _ = 1 * t.S * 2 ^ (t.K * t.D) := by ring
    _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA)

end SubNLogN.Machine.CCore.LeafCostAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Lib Computability SubNLogN.Machine
open SubNLogN.Machine.CCore.LeafKernelAux SubNLogN.Machine.CCore.LeafCostAux

/-- **The leaf program's cost is `O(e · V_g)`** above a cutoff, for any kernel cost constants. -/
theorem leafCost_holds (p : LayerParams) : LeafKernelAux.LeafCostStmt p := by
  intro C1 C2 C3 Cc
  obtain ⟨cA, hcA⟩ := costA_le p C1 C3
  obtain ⟨Ph, hHdr⟩ := hdrLen_holds p
  refine ⟨max Ph 1, 40 + cA + (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1 + 3) + 18,
    fun t hA hS hρ hg hb => ?_⟩
  have hbh : CCoreBands p Ph t := ⟨le_trans (le_max_left _ _) hb.1, hb.2⟩
  have hP1 : 1 ≤ max Ph 1 := le_max_right _ _
  obtain ⟨-, -, -, -, -, hKV, -, -, hjeV, -, -, hV1, -⟩ := LeafHdrAux.hdrFields_le_volG hb hP1
  have hMV := M_le_volG hb
  have hwg : t.P + 2 * t.Δ + 3 ≤ t.volG := wg_le_volG hb
  have hmf := LeafMFactAux.mlogm_le hb
  have he1 := LeafSplitAux.one_le_e t
  have hH : t.hdr.length + 1 ≤ t.volG := hHdr t hbh
  have hAc := hcA (max Ph 1) t hP1 hb
  have hW0 : wSel t.K t.D t.S t.ρ t.j0 ≤ t.M := wSel_le_M t hA hρ (by omega)
  have hL : costL Cc C2 C3 (2 * t.volG) (layerAddrs t.A t.K t.D t.S hA hS).length
      (wSel t.K t.D t.S t.ρ t.j0) (t.P + 2 * t.Δ + 3) t.K t.e ≤
      (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1) * t.volG := by
    rw [layerAddrs_length_M t hA hS]
    exact costL_le hV1 hW0 hmf hwg hKV (by omega)
  have hVe : t.volG ≤ t.e * t.volG := Nat.le_mul_of_pos_left _ he1
  have hloop : 1 + loopCost (fun _ => costL Cc C2 C3 (2 * t.volG)
      (layerAddrs t.A t.K t.D t.S hA hS).length (wSel t.K t.D t.S t.ρ t.j0) (t.P + 2 * t.Δ + 3)
      t.K t.e) t.e ≤ (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1 + 3) * (t.e * t.volG) := by
    rw [TMFw.loopCost_const]
    have h1 := Nat.mul_le_mul_left t.e (Nat.add_le_add_right hL 1)
    have h3 : t.e ≤ t.e * t.volG := Nat.le_mul_of_pos_right _ hV1
    have h4 : 1 ≤ t.e * t.volG := le_trans he1 h3
    have e1 : t.e * ((Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1) * t.volG + 1) =
        (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1) * (t.e * t.volG) + t.e := by ring
    have e2 : (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1 + 3) * (t.e * t.volG) =
        (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1) * (t.e * t.volG) +
          3 * (t.e * t.volG) := by ring
    omega
  have hwE : wFun t.K t.D t.S t.ρ t.j0 t.e ≤ t.volG :=
    le_trans (Nat.div_le_self _ _) (le_trans hW0 hMV)
  have hC := costC_le hwE hwg hKV hV1
  have hcA' : cA * t.volG ≤ cA * (t.e * t.volG) := Nat.mul_le_mul_left _ hVe
  have e : (40 + cA + (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1 + 3) + 18) *
      (t.e * t.volG) = 40 * (t.e * t.volG) + cA * (t.e * t.volG) +
      (Cc * (4 + (⌈p.C_M⌉₊ + 2)) + 3 * C2 + 2 * C3 + 1 + 3) * (t.e * t.volG) +
      18 * (t.e * t.volG) := by ring
  simp only [leafCost]
  rw [e]
  omega

end SubNLogN.Machine.CCore
