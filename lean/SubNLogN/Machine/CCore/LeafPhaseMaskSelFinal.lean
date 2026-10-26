/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelMain
import SubNLogN.Machine.CCore.LeafPhaseMaskSelP0Run
import SubNLogN.Machine.CCore.LeafPhaseMaskSelP0B
import SubNLogN.Machine.CCore.LeafPhaseMaskSelScan
import SubNLogN.Machine.CCore.LeafPhaseMaskSelCost

/-!
# C-core phase leaf, record-wise sign selection: `MaskSelStmt` (`LeafPhaseMaskSelFinal.lean`)

**Scope (honest summary).** `maskSel_holds : LeafScalarAux.MaskSelStmt` (proved, no hypotheses).
It assembles the parts proved in the `LeafPhaseMaskSel*.lean` files:
* `maskSel_of` (`LeafPhaseMaskSelMain.lean`): the kernel and its run, given the five named parts;
* `phase0_of` (`LeafPhaseMaskSelP0Run.lean`) applied to `phase0B_holds` (`LeafPhaseMaskSelP0B.lean`):
  phase 0, the mask emitter;
* `maskTab_holds`, `tabProg_holds` (`LeafPhaseMaskSelVal.lean`): the parity table and its builder;
* `selLoop_holds` (`LeafPhaseMaskSelScan.lean`): the select loop;
* `maskSelCost_holds` (`LeafPhaseMaskSelCost.lean`): the cost bound.
-/

namespace SubNLogN.Machine.CCore

/-- **`MaskSelStmt`**: record-wise sign selection for the C-core phase leaf. -/
theorem maskSel_holds : LeafScalarAux.MaskSelStmt :=
  PhaseMaskAux.maskSel_of (PhaseMaskAux.phase0_of MaskP0BAux.phase0B_holds)
    MaskSelValAux.maskTab_holds MaskSelValAux.tabProg_holds MaskScanAux.selLoop_holds
    MaskSelCostAux.maskSelCost_holds

end SubNLogN.Machine.CCore
