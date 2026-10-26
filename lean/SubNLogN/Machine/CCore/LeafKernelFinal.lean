/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernel
import SubNLogN.Machine.CCore.LeafKernelCostProof

/-!
# C-core leaf kernel: `LeafStmt`, unconditional (`CCore/LeafKernelFinal.lean`)

**Theorem** `leaf_holds p βn βd : LeafStmt p βn βd`, with no hypotheses: `leaf_of_cost`
(`CCore/LeafKernel.lean`) with the cost inequality `leafCost_holds` (`CCore/LeafKernelCostProof.lean`).
-/

namespace SubNLogN.Machine.CCore

/-- **The C-core leaf kernel contract `LeafStmt` holds** (no hypotheses). -/
theorem leaf_holds (p : LayerParams) (βn βd : ℕ) : LeafStmt p βn βd :=
  leaf_of_cost p βn βd (leafCost_holds p)

end SubNLogN.Machine.CCore
