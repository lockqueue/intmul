/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitBlockDefs

/-!
# Schedule compiler emitter, two straight-line blocks: proofs (`PosPermSchedEmitBlk.lean`)

Proofs of the two frozen block contracts of `PosPermSchedEmitBlockDefs.lean`, on the emitter states
`st S₀ v acc bt` (`PosPermSchedEmitSt.lean`):
* `emitBatch_holds : EmitBatchStmt`: thirteen wrapper steps (`pushA`, four times `copyR0` with
  `emitA`, `pushA`, `xferBT`, `emitA .cnt`, `pushA`), cost `13·opW V`;
* `gSetup_holds : GSetupStmt`: fourteen wrapper steps and one branch on `f = [d < J - g d]`, cost
  `14·opW V + 2`; the branch value `if d < w then d else w` is `min d w`.

**Scope (honest summary).** Both contracts are proved, with no hypotheses.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- **[PROVED] Batch command emission** (`EmitBatchStmt`, `PosPermSchedEmitBlockDefs.lean`). -/
theorem emitBatch_holds : EmitBatchStmt := by
  intro S₀ v acc bt V hU hB1 hb hV1 hrho hnS hD hj0 hcnt hbt
  have h1 := one_le_opW V
  refine runs_weak (runs_seq' (runs_pushA (V := V) S₀ v acc bt (Sym.tag 0))
    (runs_seq' (runs_copyR0 S₀ _ _ bt .rho .b hrho hb)
    (runs_seq' (runs_emitA S₀ _ _ bt .b hB1 hrho)
    (runs_seq' (runs_copyR0 S₀ _ _ bt .nS .b hnS rfl)
    (runs_seq' (runs_emitA S₀ _ _ bt .b hB1 hnS)
    (runs_seq' (runs_copyR0 S₀ _ _ bt .D .b hD rfl)
    (runs_seq' (runs_emitA S₀ _ _ bt .b hB1 hD)
    (runs_seq' (runs_copyR0 S₀ _ _ bt .j0 .b hj0 rfl)
    (runs_seq' (runs_emitA S₀ _ _ bt .b hB1 hj0)
    (runs_seq' (runs_pushA (V := V) S₀ _ _ bt Sym.sep2)
    (runs_seq' (runs_xfer S₀ _ _ bt hU hbt)
    (runs_seq' (runs_emitA S₀ _ _ [] .cnt hB1 hcnt)
      (runs_pushA (V := V) S₀ _ _ [] Sym.sep2) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
      le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
    (st_congr (fun r => by cases r <;> first | rfl | exact hb.symm)) (by omega)

/-- **[PROVED] Per-group setup** (`GSetupStmt`, `PosPermSchedEmitBlockDefs.lean`). -/
theorem gSetup_holds : GSetupStmt := by
  intro S₀ v acc V hq2 hq3 hq5 hf0 hj00 hD0 hDK0 hq40 hnS0 hd1 hK1 hV1 hm hd hK hJ hg hgdK
  have h1 := one_le_opW V
  have hgd : v .g * v .d ≤ V := by
    have : v .g * v .d * 1 ≤ v .g * v .d * v .K := Nat.mul_le_mul (le_refl _) hK1
    omega
  have hgdk : v .g * v .d * v .K ≤ V := by omega
  have hdk : v .d * v .K ≤ V := by omega
  have hw : v .J - v .g * v .d ≤ V := by omega
  have hmj : v .m - v .g * v .d * v .K ≤ V := by omega
  have hfv : (if v .d < v .J - v .g * v .d then 1 else 0) ≤ V := by split <;> omega
  by_cases hlt : v .d < v .J - v .g * v .d
  · simp only [gVals, min_eq_left hlt.le]
    refine runs_weak (runs_seq' (runs_mulR0 S₀ v acc [] .g .d .q2 hg hd hq2)
      (runs_seq' (runs_mulR0 S₀ _ acc [] .q2 .K .j0 hgd hK hj00)
      (runs_seq' (runs_subR0 S₀ _ acc [] .J .q2 .q3 hJ hgd hq3)
      (runs_seq' (runs_ltR0 S₀ _ acc [] .d .q3 .f hd hw hf0)
      (runs_seq' (runs_ifR_pos S₀ _ acc []
        (by show (if v .d < v .J - v .g * v .d then 1 else 0) ≠ 0; rw [if_pos hlt]; omega)
        (runs_copyR0 S₀ _ acc [] .d .D hd hD0))
      (runs_seq' (runs_clr S₀ _ acc [] .f hfv)
      (runs_seq' (runs_clr S₀ _ acc [] .q3 hw)
      (runs_seq' (runs_clr S₀ _ acc [] .q2 hgd)
      (runs_seq' (runs_mulR0 S₀ _ acc [] .D .K .DK hd hK hDK0)
      (runs_seq' (runs_copyR0 S₀ _ acc [] .j0 .q4 hgdk hq40)
      (runs_seq' (runs_copyR S₀ _ acc [] .DK .q4 hdk)
      (runs_seq' (runs_subR0 S₀ _ acc [] .m .j0 .q5 hm hgdk hq5)
      (runs_seq' (runs_subR0 S₀ _ acc [] .q5 .DK .nS hmj hdk hnS0)
        (runs_clr S₀ _ acc [] .q5 hmj) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
        le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
      (st_congr (fun r => by
        cases r <;> first | rfl | exact hq2.symm | exact hq3.symm | exact hq5.symm |
          exact hf0.symm)) (by omega)
  · have hle : v .J - v .g * v .d ≤ v .d := Nat.le_of_not_lt hlt
    have hwk : (v .J - v .g * v .d) * v .K ≤ V := by
      have : (v .J - v .g * v .d) * v .K ≤ v .d * v .K := Nat.mul_le_mul hle (le_refl _)
      omega
    simp only [gVals, min_eq_right hle]
    refine runs_weak (runs_seq' (runs_mulR0 S₀ v acc [] .g .d .q2 hg hd hq2)
      (runs_seq' (runs_mulR0 S₀ _ acc [] .q2 .K .j0 hgd hK hj00)
      (runs_seq' (runs_subR0 S₀ _ acc [] .J .q2 .q3 hJ hgd hq3)
      (runs_seq' (runs_ltR0 S₀ _ acc [] .d .q3 .f hd hw hf0)
      (runs_seq' (runs_ifR_neg S₀ _ acc []
        (by show (if v .d < v .J - v .g * v .d then 1 else 0) = 0; rw [if_neg hlt])
        (runs_copyR0 S₀ _ acc [] .q3 .D hw hD0))
      (runs_seq' (runs_clr S₀ _ acc [] .f hfv)
      (runs_seq' (runs_clr S₀ _ acc [] .q3 hw)
      (runs_seq' (runs_clr S₀ _ acc [] .q2 hgd)
      (runs_seq' (runs_mulR0 S₀ _ acc [] .D .K .DK hw hK hDK0)
      (runs_seq' (runs_copyR0 S₀ _ acc [] .j0 .q4 hgdk hq40)
      (runs_seq' (runs_copyR S₀ _ acc [] .DK .q4 hwk)
      (runs_seq' (runs_subR0 S₀ _ acc [] .m .j0 .q5 hm hgdk hq5)
      (runs_seq' (runs_subR0 S₀ _ acc [] .q5 .DK .nS hmj hwk hnS0)
        (runs_clr S₀ _ acc [] .q5 hmj) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
        le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
      (st_congr (fun r => by
        cases r <;> first | rfl | exact hq2.symm | exact hq3.symm | exact hq5.symm |
          exact hf0.symm)) (by omega)

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
