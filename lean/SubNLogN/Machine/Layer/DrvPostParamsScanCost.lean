/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPostParamsScan

/-!
# Layer driver, post-phase parameters: cost of the phase-scan piece
(`Machine/Layer/DrvPostParamsScanCost.lean`)

**Scope (honest summary).** One theorem, proved (no `sorry`), in the namespace
`SubNLogN.Machine.Layer.DrvParamsAux`:
`postScanCost_le : ∃ c, ∀ t, postScanCost t ≤ c * (t.hdr.length + t.D * t.K + 1) ^ 3`.
This is the cost clause of `DrvPostParamsStmt` (`Layer/DrvParamsDefs.lean:75`) for the phase-scan
piece `runs_postScanN` (`Layer/DrvPostParamsScan.lean`). There are no hypotheses on `t`.

The proof shows more: `postScanCost t ≤ 20000·(|hdr| + 1)²`. Every value handled by the piece has bit
length at most `3|hdr| + 3`.
-/

namespace SubNLogN.Machine.Layer.DrvParamsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.NatArith
  SubNLogN.Machine.Layer.DrvArith

/-- The quadratic bound behind `postScanCost_le`. -/
theorem postScanCost_le_sq (t : LayerRT) :
    postScanCost t ≤ 20000 * (t.hdr.length + 1) ^ 2 := by
  have hP := bitLen_hdr_P t
  have hD := bitLen_hdr_D t
  have hR := bitLen_hdr_rho t
  have hcf : copyFieldCost (scanHdrList t) = 13 * t.hdr.length + 12 := rfl
  have b2 : bitLen 2 ≤ 2 := bitLen_le_of_lt' (by norm_num)
  have b3 : bitLen 3 ≤ 2 := bitLen_le_of_lt' (by norm_num)
  have b4 : bitLen 4 ≤ 3 := bitLen_le_of_lt' (by norm_num)
  have bρ : bitLen t.ρ ≤ bitLen (t.ρ + 1) := bitLen_mono'' (by omega)
  have bwg : bitLen (drvWg t) ≤ bitLen t.P + 2 := by
    apply bitLen_le_of_lt'
    have := lt_two_pow_bitLen t.P
    rw [drvWg_eq, pow_succ, pow_succ]
    omega
  have bwg1 : bitLen (drvWg t + 1) ≤ bitLen t.P + 3 := by
    apply bitLen_le_of_lt'
    have := lt_two_pow_bitLen t.P
    rw [drvWg_eq, pow_succ, pow_succ, pow_succ]
    omega
  have bP1 : bitLen (t.P + 1) ≤ bitLen t.P + 1 := by
    apply bitLen_le_of_lt'
    have := lt_two_pow_bitLen t.P
    rw [pow_succ]
    omega
  have bD2 : bitLen (t.D / 2) ≤ bitLen t.D := bitLen_mono'' (Nat.div_le_self _ _)
  have bDm : bitLen (t.D % 2) ≤ bitLen t.D := bitLen_mono'' (Nat.mod_le _ _)
  have bD3 : bitLen (t.D / 2 * 3) ≤ bitLen t.D + 1 := by
    apply bitLen_le_of_lt'
    have := lt_two_pow_bitLen t.D
    rw [pow_succ]
    omega
  have bD34 : bitLen (t.D / 2 * 3 / 4) ≤ bitLen t.D + 1 :=
    le_trans (bitLen_mono'' (Nat.div_le_self _ _)) bD3
  have bC : bitLen (drvPostC t) ≤ 2 := by
    apply bitLen_le_of_lt'
    rw [drvPostC_eq]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have bPD : bitLen (t.P + t.D / 2) ≤ bitLen t.P + bitLen t.D + 1 :=
    le_trans (bitLen_add_le' _ _) (by omega)
  have bsh : bitLen (drvPostShift t) ≤ bitLen t.P + 2 * bitLen t.D + 2 := by
    rw [drvPostShift_eq]
    exact le_trans (bitLen_add_le' _ _) (by omega)
  -- the quadratic pieces
  have hsq : (t.hdr.length + 3 + 1) ^ 2 ≤ 16 * (t.hdr.length + 1) ^ 2 :=
    calc (t.hdr.length + 3 + 1) ^ 2 ≤ (4 * (t.hdr.length + 1)) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
      _ = 16 * (t.hdr.length + 1) ^ 2 := by ring
  have m1 : mulConstCost (t.P + 1) 3 ≤ 300 * (t.hdr.length + 3 + 1) ^ 2 := by
    have e : (t.P + 1) * 3 = drvWg t := by rw [drvWg_eq]; ring
    exact mulConstCost_le' (by omega) (by omega) (by rw [e]; omega)
  have m2 : mulConstCost (t.D / 2) 3 ≤ 300 * (t.hdr.length + 3 + 1) ^ 2 :=
    mulConstCost_le' (by omega) (by omega) (by omega)
  have p1 : bitLen t.D * bitLen 2 ≤ t.hdr.length * 2 := Nat.mul_le_mul (by omega) b2
  have p2 : bitLen (t.D / 2 * 3) * bitLen 4 ≤ (t.hdr.length + 1) * 3 := Nat.mul_le_mul (by omega) b4
  have hY : t.hdr.length + 1 ≤ (t.hdr.length + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  simp only [postScanCost]
  omega

/-- **Cost clause of the phase-scan piece** (for `DrvPostParamsStmt`,
`Layer/DrvParamsDefs.lean:75`). -/
theorem postScanCost_le :
    ∃ c, ∀ t : LayerRT, postScanCost t ≤ c * (t.hdr.length + t.D * t.K + 1) ^ 3 := by
  refine ⟨20000, fun t => ?_⟩
  have h1 : (t.hdr.length + 1) ^ 2 ≤ (t.hdr.length + 1) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : (t.hdr.length + 1) ^ 3 ≤ (t.hdr.length + t.D * t.K + 1) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have h3 := postScanCost_le_sq t
  calc postScanCost t ≤ 20000 * (t.hdr.length + 1) ^ 2 := h3
    _ ≤ 20000 * (t.hdr.length + t.D * t.K + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (le_trans h1 h2)

end SubNLogN.Machine.Layer.DrvParamsAux
