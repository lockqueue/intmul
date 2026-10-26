/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedCycleA
import SubNLogN.Machine.Walsh.PosPermSchedCycleAScan
import SubNLogN.Machine.Walsh.PosPermSchedCycleB
import SubNLogN.Machine.Walsh.PosPermSchedCycPhase

/-!
# Schedule compiler, cycle phase assembled (`Machine/Walsh/PosPermSchedCycAll.lean`)

**Main result.** `SubNLogN.Machine.Walsh.PosPermSchedAux.cycPhase_holds : CycPhaseStmt`, with no
hypotheses: the whole cycle phase of the runtime schedule compiler (tables
`I0T := utab (finVals (invol0 π))`, `I1T := utab (finVals (invol1 π))`, see `CycPhaseStmt` in
`PosPermSchedDefs.lean`).

It is `cycPhase_of` (`PosPermSchedCycPhase.lean`) applied to the three proved sub-contracts
* `cycBase_holds : CycBaseStmt` (`PosPermSchedCycleA.lean`),
* `cycIdxLen_holds : CycIdxLenStmt` (`PosPermSchedCycleAScan.lean`),
* `cycPush_holds : CycPushStmt` (`PosPermSchedCycleB.lean`).
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

/-- The cycle-phase contract `CycPhaseStmt`, unconditionally (from the three proved phase pieces). -/
theorem cycPhase_holds : CycPhaseStmt :=
  cycPhase_of cycBase_holds cycIdxLen_holds cycPush_holds

end SubNLogN.Machine.Walsh.PosPermSchedAux
