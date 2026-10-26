/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.LayerAll
import SubNLogN.Machine.CCore.LeafHdrTest
import SubNLogN.Machine.CCore.LeafHdrDrop
import SubNLogN.Machine.CCore.LeafIo
import SubNLogN.Machine.CCore.LeafSplitCollect
import SubNLogN.Machine.CCore.MathInputs
import SubNLogN.Machine.Layer.DrvPost
import SubNLogN.Machine.Layer.DrvUnpad
import SubNLogN.Machine.Layer.DrvPhaseScan
import SubNLogN.Assembly.Row46Layer

/-!
# The layer machine at the `C₁ = 14` Walsh-row parameters (`Machine/Layer/LayerFinal.lean`)

`layerMachine_mid_of_open : … → LayerMachineStmt (midLayerParams row46Layer 1)`
(`Contracts/Layer.lean`; Proposition A.11's machine part at the constants of the `C₁ = 14` Walsh row,
`Assembly/Row46Layer.lean`, with `midLayerParams` (`Machine/FFT/Bands.lean`)), consumed by
the Walsh-middle wiring.

Assembled from `Layer.layerMachine_of_ccoreLeaves` (`Layer/LayerAll.lean`) with
* the admissibility `midLayerParams_OK 1 row46Layer_OK`;
* the **proved** C-core leaves `hdrTest_holds`, `dropHdr12_holds`, `roleToIo_holds`,
  `ioToRole_holds`, `split_holds`, `collect_holds`;
* the **proved** mathematical inputs `cCoreMathInputs_holds`;
* the driver post-phase `drvPost_of_parts` with the proved `drvUnpad_holds`,
  `drvPhaseScan_holds`.

**Open leaves (explicit named hypotheses, nothing else assumed):** `PushChildHdrStmt`,
`PhaseStmt`, `RowAddStmt`, `ScalarRowStmt`, `LeafStmt` (all at `midLayerParams row46Layer 1`; the
leaf for every `βn βd`), the driver parameter kernel `DrvPostParamsStmt`, and the driver pre-phase
`DrvPreStmt (midLayerParams row46Layer 1)`. No `sorry`.
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Machine.CCore SubNLogN.Assembly

/-- **Proposition A.11's machine part at `midLayerParams row46Layer 1`**, from the still-open
C-core leaves and driver kernels (named hypotheses). -/
theorem layerMachine_mid_of_open
    (hPush : PushChildHdrStmt (midLayerParams row46Layer 1))
    (hPhase : PhaseStmt (midLayerParams row46Layer 1))
    (hRowAdd : RowAddStmt (midLayerParams row46Layer 1))
    (hScalar : ScalarRowStmt (midLayerParams row46Layer 1))
    (hLeaf : ∀ βn βd : ℕ, LeafStmt (midLayerParams row46Layer 1) βn βd)
    (hParams : DrvPostParamsStmt)
    (hPre : DrvPreStmt (midLayerParams row46Layer 1)) :
    LayerMachineStmt (midLayerParams row46Layer 1) :=
  layerMachine_of_ccoreLeaves (midLayerParams row46Layer 1) (midLayerParams_OK 1 row46Layer_OK)
    (fun βn βd => ⟨hdrTest_holds (midLayerParams row46Layer 1) βn βd, hPush, dropHdr12_holds,
      roleToIo_holds, ioToRole_holds, split_holds (midLayerParams row46Layer 1),
      collect_holds (midLayerParams row46Layer 1), hPhase, hRowAdd, hScalar, hLeaf βn βd⟩)
    (fun βn βd => cCoreMathInputs_holds (midLayerParams row46Layer 1) βn βd) hPre
    (drvPost_of_parts (midLayerParams row46Layer 1) (midLayerParams_OK 1 row46Layer_OK) hParams
      drvUnpad_holds drvPhaseScan_holds)

end SubNLogN.Machine.Layer
