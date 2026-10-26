/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.LayerFinal
import SubNLogN.Machine.CCore.LeafPushHdr
import SubNLogN.Machine.CCore.LeafScalarRowTop
import SubNLogN.Machine.CCore.LeafKernelFinal
import SubNLogN.Machine.Layer.DrvPostParams

/-!
# The layer machine at the `C₁ = 14` Walsh-row parameters, closures (`Machine/Layer/LayerMid.lean`)

`layerMachine_mid_of_remaining : … → LayerMachineStmt (midLayerParams row46Layer 1)`: the frozen
W3 wiring `layerMachine_mid_of_open` (`Layer/LayerFinal.lean`) with the leaves that are now proved
(each proved under the three standard axioms) plugged in:
* `PushChildHdrStmt` ← `pushChildHdr_holds` (`CCore/LeafPushHdr.lean`);
* `ScalarRowStmt` ← `scalarRow_holds` (`CCore/LeafScalarRowTop.lean`);
* `LeafStmt` (every `βn βd`) ← `leaf_holds` (`CCore/LeafKernelFinal.lean`);
* `DrvPostParamsStmt` ← `drvPostParams_holds` (`Layer/DrvPostParams.lean`).

**Remaining open statements (explicit named hypotheses):** `PhaseStmt`, `RowAddStmt` and
`DrvPreStmt`, all at `midLayerParams row46Layer 1`. No `sorry`.
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Machine.CCore SubNLogN.Assembly

/-- **Proposition A.11's machine part at `midLayerParams row46Layer 1`**, from the remaining open
statements `PhaseStmt`, `RowAddStmt`, `DrvPreStmt` (named hypotheses). -/
theorem layerMachine_mid_of_remaining
    (hPhase : PhaseStmt (midLayerParams row46Layer 1))
    (hRowAdd : RowAddStmt (midLayerParams row46Layer 1))
    (hPre : DrvPreStmt (midLayerParams row46Layer 1)) :
    LayerMachineStmt (midLayerParams row46Layer 1) :=
  layerMachine_mid_of_open (pushChildHdr_holds (midLayerParams row46Layer 1)) hPhase hRowAdd
    (scalarRow_holds (midLayerParams row46Layer 1))
    (fun βn βd => leaf_holds (midLayerParams row46Layer 1) βn βd) drvPostParams_holds hPre

end SubNLogN.Machine.Layer
