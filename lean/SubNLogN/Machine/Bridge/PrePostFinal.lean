/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPost
import SubNLogN.Machine.Arith.Shl
import SubNLogN.Machine.Bridge.PrePostPreFin

/-!
# K5 pre-scaling and output contract theorems (`Bridge/PrePostFinal.lean`)

**Scope (honest summary).** Unconditional instances of the pre-scaling and output bridge parts:

* `SubNLogN.Machine.post_holds : PostStmt` — the final step of the bridge
  (Section 4.4 (`sec:bridge-alg`), step (5)): exact `×2^e` of every coefficient, then nearest rounding
  (ties toward `+∞`, `roundHalfUpR`) to the `(p+2)`-grid, read from `arr` and pushed onto `dst`,
  `e` consumed from `ex`, at cost `C * postCost b`. It is `BridgePP.post_holds_of`
  (`Bridge/PrePostPost.lean`) applied to AR's proved shift kernels
  `Arith.shl_holds : ShlStmt` (`Arith/Shl.lean`) and
  `Arith.roundHalfUpShift_holds : RoundHalfUpShiftStmt` (`Arith/Shift.lean`).

* `SubNLogN.Machine.preScale_holds : PreScaleStmt` — the pre-scaling step of the bridge
  (Section 4.4 (`sec:bridge-alg`), step (1); Theorem 4.7 (`thm:bridge-precision`)): reads `x` on the `pIn`-grid from `src` (consumed), finds
  `H` by one scan, pushes the exactly pre-scaled array `x / 2^e` at `q = P + 2` onto `arr` and
  `e = preScaleExp t x` onto `ex`, at cost `C * preCost b`. It is `BridgePP.preScale_holds_of`
  (`Bridge/PrePostPreFin.lean`) applied to AR's proved kernels `Arith.truncShift_holds :
  TruncShiftStmt` (`Arith/Shift.lean`) and `Arith.shl_holds : ShlStmt` (`Arith/Shl.lean`).

No hypotheses remain; no `sorry`/axioms beyond Lean's standard ones.
-/

namespace SubNLogN.Machine

/-- **[K5, proved] Final step** (Section 4.4 (`sec:bridge-alg`), step (5)): `PostStmt` holds unconditionally. -/
theorem post_holds : PostStmt :=
  BridgePP.post_holds_of Arith.shl_holds Arith.roundHalfUpShift_holds

/-- **[K5, proved] Pre-scaling** (Section 4.4 (`sec:bridge-alg`), step (1); Theorem 4.7 (`thm:bridge-precision`)): `PreScaleStmt` holds
unconditionally. -/
theorem preScale_holds : PreScaleStmt :=
  BridgePP.preScale_holds_of Arith.truncShift_holds Arith.shl_holds

end SubNLogN.Machine
