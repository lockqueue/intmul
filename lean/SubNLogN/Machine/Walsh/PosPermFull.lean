/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPerm
import SubNLogN.Machine.Walsh.CnotBatchFull
import SubNLogN.Machine.Walsh.Cnot1Holds
import SubNLogN.Machine.Walsh.CnotHdr

/-!
# K3-PERM (`Machine/Walsh/PosPermFull.lean`): Theorem 5.8 (`thm:positional-perm`) on the machine

**Scope (honest summary).** Corollaries of the sequencing reduction `positionalPermMachine_of`
with the proved single-flip, lift/lowering, and CNOT-header parts plugged in:
* `Cnot1MachineStmt` by `WalshCnot1.cnot1Machine_holds` (`Walsh/Cnot1Holds.lean`);
* `LiftMachineStmt`, `LowerMachineStmt` inside `cnotBatchMachine_of_layer`
  (`Walsh/CnotBatchFull.lean`);
* `CnotHdrStmt` by `WalshScanAux.cnotHdr_holds` (`Walsh/CnotHdr.lean`).

`positionalPermMachine_of_leaves` still takes as explicit hypotheses the slice layer call
(`CubeLayerStmt Band lam'`), the four recordwise scans (`CnotScanStmt mode`) and the runtime
schedule compiler (`PosPermSchedStmt`, `Walsh/PosPermLeaf.lean`). Everything here is proved.
-/

namespace SubNLogN.Machine

/-- **Theorem 5.8 on the machine** (`thm:positional-perm`) from the slice layer call,
the CNOT header builder and scans, and the schedule compiler (the single flip and the exact
lift/lowering are proved). -/
theorem positionalPermMachine_of_layer {Band : LayerRT → Prop} {lam' : ℝ}
    (hLay : CubeLayerStmt Band lam') (hHdr : CnotHdrStmt) (hScan : ∀ mode, CnotScanStmt mode)
    (hC : PosPermSchedStmt) : PositionalPermMachineStmt Band lam' :=
  positionalPermMachine_of (cnotBatchMachine_of_layer hLay hHdr hScan)
    WalshCnot1.cnot1Machine_holds hC

/-- **Theorem 5.8 on the machine** with the header builder also proved: the remaining hypotheses
are the slice layer call, the four recordwise scans and the schedule compiler. -/
theorem positionalPermMachine_of_leaves {Band : LayerRT → Prop} {lam' : ℝ}
    (hLay : CubeLayerStmt Band lam') (hScan : ∀ mode, CnotScanStmt mode)
    (hC : PosPermSchedStmt) : PositionalPermMachineStmt Band lam' :=
  positionalPermMachine_of_layer hLay WalshScanAux.cnotHdr_holds hScan hC

end SubNLogN.Machine
