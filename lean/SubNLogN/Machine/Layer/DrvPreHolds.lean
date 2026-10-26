/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPre
import SubNLogN.Machine.Layer.DrvPreK
import SubNLogN.Machine.Layer.DrvPad
import SubNLogN.Machine.Layer.DrvPhaseScan
import SubNLogN.Machine.Layer.DrvPh1Bridge
import SubNLogN.Machine.Layer.DrvPadBridge
import SubNLogN.Machine.Layer.DrvPreCost
import SubNLogN.Machine.Layer.DrvDescHolds
import SubNLogN.Machine.Layer.R2DrvPreDefs
import SubNLogN.Machine.Layer.DrvPreParams
import SubNLogN.Machine.FFT.Bands
import SubNLogN.Assembly.Row46Layer

/-!
# Layer driver pre-phase with the proved parts plugged in (`Machine/Layer/DrvPreHolds.lean`)

**Scope (honest summary).**
* `drvPre_of_params`: `DrvPreStmt p` for every admissible `p` from the pre-phase parameter kernel
  `DrvPreParamsStmt` alone; everything else is proved: `drvCKernel_holds`, `drvPad_holds`,
  `drvDesc_holds`, `drvPhaseScan_holds`, `drvPh1Bridge_holds`, `drvPadBridge_holds`,
  `drvPreCost_holds` (and `Arith.shl_holds` inside `drvPre_of_parts`).
* `drvPre_of_open`: the same from the two halves `R2PartAStmt`, `R2PartBStmt` of the parameter kernel
  (`R2DrvPreDefs.lean`, via `drvPreParams_of_parts`).
* `drvPre_mid_of_open`: the instance at `midLayerParams row46Layer 1` (for `LayerFinal.lean`).
* **Closed forms** (no hypotheses besides admissibility), with `drvPreParams_holds` (`DrvPreParams.lean`):
  `drvPre_holds (p) (hp : p.OK) : DrvPreStmt p` and
  `drvPre_mid_holds : DrvPreStmt (midLayerParams row46Layer 1)`.
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Assembly

/-- **Driver pre-phase from the parameter kernel** (all other parts proved). -/
theorem drvPre_of_params (p : LayerParams) (hp : p.OK) (hParams : DrvPreParamsStmt) :
    DrvPreStmt p :=
  drvPre_of_parts p hp hParams DrvPreK.drvCKernel_holds drvPad_holds drvDesc_holds
    drvPhaseScan_holds drvPh1Bridge_holds drvPadBridge_holds drvPreCost_holds

/-- **Driver pre-phase from the open halves of the parameter kernel** (`R2PartAStmt`,
`R2PartBStmt`). -/
theorem drvPre_of_open (p : LayerParams) (hp : p.OK) (hA : R2DrvPre.R2PartAStmt)
    (hB : R2DrvPre.R2PartBStmt) : DrvPreStmt p :=
  drvPre_of_params p hp (R2DrvPre.drvPreParams_of_parts hA hB)

/-- **Driver pre-phase at the `C₁ = 14` Walsh-row parameters** `midLayerParams row46Layer 1`. -/
theorem drvPre_mid_of_open (hA : R2DrvPre.R2PartAStmt) (hB : R2DrvPre.R2PartBStmt) :
    DrvPreStmt (midLayerParams row46Layer 1) :=
  drvPre_of_open _ (midLayerParams_OK 1 row46Layer_OK) hA hB

/-- **Driver pre-phase, closed form** (every part proved). -/
theorem drvPre_holds (p : LayerParams) (hp : p.OK) : DrvPreStmt p :=
  drvPre_of_params p hp drvPreParams_holds

/-- **Driver pre-phase at the `C₁ = 14` Walsh-row parameters, closed form.** -/
theorem drvPre_mid_holds : DrvPreStmt (midLayerParams row46Layer 1) :=
  drvPre_holds _ (midLayerParams_OK 1 row46Layer_OK)

end SubNLogN.Machine.Layer
