/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.LayerMid
import SubNLogN.Machine.CCore.LeafPhase
import SubNLogN.Machine.CCore.LeafPhaseMaskSelFinal
import SubNLogN.Machine.CCore.LeafRowAdd
import SubNLogN.Machine.AppC.C7Final
import SubNLogN.Machine.AppC.C6Holds
import SubNLogN.Machine.AppC.C7ExtractHolds

/-!
# The layer machine at the `C₁ = 14` Walsh-row parameters, last closures (`Machine/Layer/LayerMidHolds.lean`)

`layerMachine_mid_of_pre (hPre : DrvPreStmt (midLayerParams row46Layer 1)) :
LayerMachineStmt (midLayerParams row46Layer 1)`: `layerMachine_mid_of_remaining`
(`Layer/LayerMid.lean`) with
* `PhaseStmt` ← `phase_holds_of maskSel_holds _` (`CCore/LeafPhase.lean`,
  `CCore/LeafPhaseMaskSelFinal.lean`);
* `RowAddStmt` ← `rowAdd_of_c7 _ (c7PackedXor_mid_of_open c6_holds c7Extract_holds)
  (midLayerParams_OK 1 row46Layer_OK)` (`CCore/LeafRowAdd.lean`, `AppC/C7Final.lean`,
  `AppC/C6Holds.lean`, `AppC/C7ExtractHolds.lean`; `AppC`/`C6`/`C7` denote Appendix A, Lemma A.8, Lemma A.9).

**Remaining open statement (named hypothesis):** `DrvPreStmt (midLayerParams row46Layer 1)`.
No `sorry`.
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Machine.CCore SubNLogN.Assembly

/-- **Proposition A.11's machine part at `midLayerParams row46Layer 1`**, from the driver
pre-phase `DrvPreStmt` (named hypothesis); every C-core leaf and the driver post-phase proved. -/
theorem layerMachine_mid_of_pre (hPre : DrvPreStmt (midLayerParams row46Layer 1)) :
    LayerMachineStmt (midLayerParams row46Layer 1) :=
  layerMachine_mid_of_remaining (phase_holds_of maskSel_holds (midLayerParams row46Layer 1))
    (rowAdd_of_c7 (midLayerParams row46Layer 1)
      (c7PackedXor_mid_of_open c6_holds c7Extract_holds) (midLayerParams_OK 1 row46Layer_OK))
    hPre

end SubNLogN.Machine.Layer
