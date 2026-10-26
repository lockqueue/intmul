/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPushHdrProg
import SubNLogN.Machine.CCore.LeafPushHdrCost

/-!
# C-core leaf (2): `PushChildHdrStmt` (`CCore/LeafPushHdr.lean`)

`pushChildHdr_holds p : PushChildHdrStmt p` (`CCore/SkelDefs.lean:190`) for every `p`, with
cutoff `P₀ = 1`. At a node (`1 ≤ t.k`) the kernel (static slot `a`) pushes
`childHdr t a = (childRT t (t.k - 1) a 0).hdr` above the parent header on `desc`; every other stack
is unchanged and the private scratch is clean again; the run is boundary-safe for `ccoreFramed`
and costs at most `C · t.volG`.

* The kernel, its exact `Runs` fact and the embedding/safety argument:
  `pushChildHdr_of_cost` (`CCore/LeafPushHdrProg.lean`).
* The cost bound `costL t a ≤ C · t.volG` under `CCoreBands p 1 t`: `PushHdrAux.pushCost_le`
  (`CCore/LeafPushHdrCost.lean`).
-/

namespace SubNLogN.Machine.CCore

/-- **[LEAF (2)] `PushChildHdrStmt` holds** (`CCore/SkelDefs.lean:190`), for every `p`. -/
theorem pushChildHdr_holds (p : LayerParams) : PushChildHdrStmt p :=
  pushChildHdr_of_cost p (PushHdrAux.pushCost_le p)

end SubNLogN.Machine.CCore
