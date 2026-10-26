/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotBatch
import SubNLogN.Machine.Walsh.Lift

/-!
# K3-PERM (`Machine/Walsh/CnotBatchFull.lean`): Proposition 5.5 with the lift discharged

**Scope (honest summary).** One corollary: `cnotBatchMachine_of` with `LiftMachineStmt` and
`LowerMachineStmt` discharged by K3-LIFT's proved `WalshLift.liftMachine_holds`,
`WalshLift.lowerMachine_holds`. The remaining hypotheses are the layer call on a cube slice and the
two leaf contracts of `Machine/Walsh/CnotLeaf.lean`.
-/

namespace SubNLogN.Machine

/-- **Proposition 5.5 on the machine** (`prop:cnot-batch`) from the layer call on a
cube slice and the two leaf contracts (`CnotHdrStmt`, `CnotScanStmt`); lift and lowering are
proved. -/
theorem cnotBatchMachine_of_layer {Band : LayerRT → Prop} {lam' : ℝ}
    (hLay : CubeLayerStmt Band lam') (hHdr : CnotHdrStmt) (hScan : ∀ mode, CnotScanStmt mode) :
    CnotBatchMachineStmt Band lam' :=
  cnotBatchMachine_of hLay WalshLift.liftMachine_holds WalshLift.lowerMachine_holds hHdr hScan

end SubNLogN.Machine
