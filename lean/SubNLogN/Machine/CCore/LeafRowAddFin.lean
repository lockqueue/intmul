/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddMain
import SubNLogN.Machine.CCore.LeafRowAddCostB
import SubNLogN.Machine.CCore.LeafRowAddGlue

/-!
# C-core leaf 9: discharging the glue and counter-cost statements (`CCore/LeafRowAddFin.lean`)

* `rowAddGlue_holds : RowAddGlueStmt`, from `LeafRowAddGlue.lean`: `mainP`,
  `closed_mainP`, `safe_mainP`.
* `rowAddCtrCost_of`: `RowAddCtrCostStmt p` from the counter cost bound
  `costAll t p₁ p₂ + costClr … ≤
  Cc·(ctrB t + 1)^3`. It also uses `ctrB_le` (`ctrB t = O(P)`) and `poly_absorb`
  (`κ(P+1)^n ≤ V_g`).
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.CCore.LeafRowAddAux

theorem rowAddGlue_holds : RowAddGlueStmt := by
  intro E7 _ _ R7 u Pctr Pclr P7
  exact ⟨LeafRowAddGlueAux.mainP u Pctr Pclr P7,
    fun h1 h2 h3 => LeafRowAddGlueAux.closed_mainP u h1 h2 h3,
    fun vals hdr tdesc v v' Tctr Tclr T7 hCtr hClr hC7 S hclean hd hrole =>
      LeafRowAddGlueAux.safe_mainP u Pctr Pclr P7 vals hdr tdesc v v' Tctr Tclr T7 hCtr hClr hC7
        S hclean hd hrole⟩

open LeafRowAddCostAux in
/-- `RowAddCtrCostStmt p` from the cubic counter cost bound in the size parameter `ctrB`. -/
theorem rowAddCtrCost_of (p : LayerParams) (hp : p.OK)
    (hAll : ∃ Cc : ℕ, ∀ (t : CCoreRT) (p₁ p₂ : ℕ), p₁ < mn → p₂ < mn → p₁ ≠ p₂ → 1 ≤ t.k →
      1 ≤ t.K → t.j0 + t.e ≤ t.D →
      costAll t p₁ p₂ + costClr (ctrVals t p₁ p₂) ≤ Cc * (ctrB t + 1) ^ 3) :
    RowAddCtrCostStmt p := by
  obtain ⟨Cc, hcc⟩ := hAll
  obtain ⟨P₁, c, hB⟩ := LeafRowAddCostAux.ctrB_le p hp
  obtain ⟨P₂, hpoly⟩ := poly_absorb p hp (Cc * (c + 1) ^ 3) 3
  refine ⟨max 1 (max P₁ P₂), 1, fun t p₁ p₂ hb h1 h2 h12 hk => ?_⟩
  have hb1 : CCoreBands p P₁ t := bands_mono (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hb2 : CCoreBands p P₂ t := bands_mono (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  obtain ⟨-, -, -, hK1, -, -, -, -, -⟩ := bands_basic hp (le_max_left _ _) hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfit, -, -⟩ := hb
  have hc := hcc t p₁ p₂ h1 h2 h12 hk hK1 hfit
  have hBt : ctrB t ≤ c * (t.P + 1) := hB t hb1
  have hpt := hpoly t hb2
  have h3 : (ctrB t + 1) ^ 3 ≤ (c + 1) ^ 3 * (t.P + 1) ^ 3 := by
    rw [← mul_pow]
    apply Nat.pow_le_pow_left
    nlinarith
  calc costAll t p₁ p₂ + costClr (ctrVals t p₁ p₂) ≤ Cc * (ctrB t + 1) ^ 3 := hc
    _ ≤ Cc * ((c + 1) ^ 3 * (t.P + 1) ^ 3) := Nat.mul_le_mul_left _ h3
    _ = Cc * (c + 1) ^ 3 * (t.P + 1) ^ 3 := by ring
    _ ≤ t.volG := hpt
    _ = 1 * t.volG := (one_mul _).symm

end SubNLogN.Machine.CCore
