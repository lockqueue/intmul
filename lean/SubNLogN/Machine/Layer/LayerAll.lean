/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DriverAll
import SubNLogN.Machine.CCore.Parts
import SubNLogN.Machine.CCore.SkelNodeRun
import SubNLogN.Machine.CCore.SkelImpl

/-!
# Proposition A.11, machine part: the reduction chain (`Machine/Layer/LayerAll.lean`)

**Scope (honest summary).** `layerMachine_of_ccoreParts`: for admissible constants `p` (`p.OK`),
the layer machine statement `LayerMachineStmt p` follows from
* the layout plumbing of the C-core skeleton (`SkelImpl p βn βd`, at every leaf exponent),
* the mathematical inputs of the C-core (`CCoreMathInputs p βn βd`, at every leaf exponent),
* the driver's pre- and post-phase kernels (`DrvPreStmt p`, `DrvPostStmt p`).
The node run is `nodeRun_holds` (proved). The C-core contract comes from `cCore_of_inputs`, the
layer from `layerMachine_of_kernels`. Proved without `sorry`; the four hypotheses above are open.

`layerMachine_of_ccoreLeaves` replaces the layout plumbing by the kernel leaves (`CCoreLeaves`,
via `skelImpl_of_leaves`).
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine.CCore

/-- **Proposition A.11's machine part from the C-core parts and the driver kernels.** -/
theorem layerMachine_of_ccoreParts (p : LayerParams) (hOK : p.OK)
    (himpl : ∀ βn βd : ℕ, SkelImpl p βn βd) (hin : ∀ βn βd : ℕ, CCoreMathInputs p βn βd)
    (hpre : DrvPreStmt p) (hpost : DrvPostStmt p) : LayerMachineStmt p :=
  layerMachine_of_kernels p hOK
    (fun βn βd => cCore_of_inputs p βn βd nodeRun_holds (himpl βn βd) (hin βn βd)) hpre hpost

/-- **Proposition A.11's machine part from the C-core kernel leaves, the C-core's mathematical
inputs and the driver kernels.** -/
theorem layerMachine_of_ccoreLeaves (p : LayerParams) (hOK : p.OK)
    (hleaves : ∀ βn βd : ℕ, CCoreLeaves p βn βd) (hin : ∀ βn βd : ℕ, CCoreMathInputs p βn βd)
    (hpre : DrvPreStmt p) (hpost : DrvPostStmt p) : LayerMachineStmt p :=
  layerMachine_of_ccoreParts p hOK (fun βn βd => skelImpl_of_leaves p βn βd (hleaves βn βd)) hin
    hpre hpost

end SubNLogN.Machine.Layer
