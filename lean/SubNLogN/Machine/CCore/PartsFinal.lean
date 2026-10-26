/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.Parts
import SubNLogN.Machine.CCore.SkelNodeRun
import SubNLogN.Machine.CCore.SkelImpl
import SubNLogN.Machine.CCore.MathInputs

/-!
# C-core contract from the kernel leaves (`CCore/PartsFinal.lean`)

**Scope (honest summary).** `cCoreStmt_of_leaves : CCoreLeaves p βn βd → CCoreStmt p βn βd`. It
assembles:
* the node run `nodeRun_holds` and the layout plumbing `skelImpl_of_leaves`;
* the mathematical inputs `cCoreMathInputs_holds` (M1-M6 and the value-level network premises);
* the `fix` induction `cCore_of_inputs`.
Proved without `sorry`. The only hypothesis is the bundle of kernel leaves `CCoreLeaves`
(`CCore/SkelDefs.lean`).
-/

namespace SubNLogN.Machine.CCore

/-- **The C-core contract from the kernel leaves.** -/
theorem cCoreStmt_of_leaves (p : LayerParams) (βn βd : ℕ) (hL : CCoreLeaves p βn βd) :
    CCoreStmt p βn βd :=
  cCore_of_inputs p βn βd nodeRun_holds (skelImpl_of_leaves p βn βd hL)
    (cCoreMathInputs_holds p βn βd)

end SubNLogN.Machine.CCore
