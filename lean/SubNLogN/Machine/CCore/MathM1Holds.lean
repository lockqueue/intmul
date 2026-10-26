/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.MathM1
import SubNLogN.Machine.CCore.NodeCode

/-!
# M1 proved (`CCore/MathM1Holds.lean`)

`nodeValue_holds cdat : NodeValueStmt cdat` (M1 of `CCore/SkelMathDefs.lean`): the assembly
`M1Aux.nodeValue_of_transport` (`CCore/MathM1.lean`: compact identity, ideal children, Lemma A.10)
applied to the op-by-op transport `nodeCode_transport` (`CCore/NodeCode.lean`).
-/

namespace SubNLogN.Machine.CCore

open SubNLogN.Math.Networks

/-- **(M1) Node value correctness, compact form** (`NodeValueStmt`). Under the value-level network and Lemma A.9
statements and valid edge data, at an internal node (`1 ≤ k`, `6 ≤ K`, `W_c^k ∣ A`, group inside `D`),
the node code run on the role streams of `z` (children computing `cCoreVal` on their slots) ends with
row class `u` of `cCoreVal z` on physical role `collectPerm u`. -/
theorem nodeValue_holds (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    NodeValueStmt cdat :=
  M1Aux.nodeValue_of_transport cdat
    (fun t hρ h1 hK hdiv hg hR8 hPA hPP hval crun hcrun Arr u =>
      nodeCode_transport t hρ h1 hK hdiv hg hR8 hPA hPP cdat hval crun hcrun Arr u)

end SubNLogN.Machine.CCore
