/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitRho
import SubNLogN.Machine.Walsh.PosPermSchedEmitBlk
import SubNLogN.Machine.Walsh.PosPermSchedEmitGLoop
import SubNLogN.Machine.Walsh.PosPermSchedEmitLeft
import SubNLogN.Machine.Walsh.PosPermSchedEmitStage
import SubNLogN.Machine.Walsh.PosPermSchedMain

/-!
# Schedule compiler emitter, assembled (`Machine/Walsh/PosPermSchedEmitAll.lean`)

The emitter's parts, plugged together:
* `rhoBody_of` (one slice, `PosPermSchedEmitRho.lean`) with `emitBatch_holds`
  (`PosPermSchedEmitBlk.lean`);
* `gLoop_of` (all groups, `PosPermSchedEmitGLoop.lean`);
* `leftPass_holds` (the leftover pass, `PosPermSchedEmitLeft.lean`);
* `stageProg_of` (the stage assembly, `PosPermSchedEmitStage.lean`).

**Scope (honest summary).** Proved, no hypotheses:
* `rhoBody_holds : RhoBodyStmt` and `gLoop_holds : GLoopStmt`;
* the emitter contract `stageProg_holds : StageProgStmt` (`PosPermSchedState.lean`). The witness is
  `stageProgE` (`PosPermSchedEmitStageDefs.lean`); the cost constant is `C = 10^7` with exponent
  `k = 9`;
* combined with `posPermSched_of_emit` (`PosPermSchedMain.lean`), the schedule compiler
  `posPermSched_holds : PosPermSchedStmt` (`PosPermLeaf.lean`).
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

/-- **One slice of the emitter, proved.** -/
theorem rhoBody_holds : RhoBodyStmt := rhoBody_of emitBatch_holds

/-- **All groups of a stage, proved.** -/
theorem gLoop_holds : GLoopStmt := gLoop_of rhoBody_holds

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

/-- **EMIT, proved** (`StageProgStmt`, `PosPermSchedState.lean`). One closed stage program family
`stageProgE IT stA` pushes `(schedSyms (stageCmds m d K (stageA I or stageB I))).reverse` onto `ACC`
and restores everything else, within `10^7·(m + d + K + 1)^9`. -/
theorem stageProg_holds : StageProgStmt :=
  Emit.stageProg_of Emit.gLoop_holds Emit.leftPass_holds

end SubNLogN.Machine.Walsh.PosPermSchedAux

namespace SubNLogN.Machine

/-- **K3.5a, the runtime schedule compiler of Theorem 5.8, proved** (`PosPermSchedStmt`,
`PosPermLeaf.lean`): `posPermSched_of_emit` (`PosPermSchedMain.lean`) with the stage emitter
`stageProg_holds`. -/
theorem posPermSched_holds : PosPermSchedStmt :=
  posPermSched_of_emit Walsh.PosPermSchedAux.stageProg_holds

end SubNLogN.Machine
