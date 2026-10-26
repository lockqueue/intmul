/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitLoopDefs
import SubNLogN.Machine.Walsh.PosPermSchedEmitLeftDefs

/-!
# Schedule compiler emitter, the stage program (`PosPermSchedEmitStageDefs.lean`)

The witness program of `StageProgStmt` (`PosPermSchedState.lean`). It runs four parts in order:
* `setup` computes `J = m / K`, `G = (J + d - 1) / d` (`numGroups`) and `JK = J·K`;
* `gLoop` emits the slices (`GLoopStmt`, `PosPermSchedEmitLoopDefs.lean`);
* `lLoop` emits the leftover single flips (`LeftPassStmt`, `PosPermSchedEmitLeftDefs.lean`);
* the teardown clears `J, G, JK`.

**Scope (honest summary).** Definitions and closedness only.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- `J := m / K` (remainder in `v`, cleared), `q2 := J + d - 1`, `G := q2 / d` (remainder
cleared), clear `q2`, `JK := J·K`. -/
def setup : SProg Stk :=
  .seq (dmR .m .K .J .v) (.seq (clr .v) (.seq (copyR .J .q2) (.seq (copyR .d .q2) (.seq (dec .q2)
    (.seq (dmR .q2 .d .G .v) (.seq (clr .v) (.seq (clr .q2) (mulR .J .K .JK))))))))

/-- **The stage emitter**, the witness of `StageProgStmt`. -/
def stageProgE (IT : RawN) (stA : Bool) : SProg Stk :=
  .seq setup (.seq (gLoop IT stA) (.seq (lLoop IT stA) (.seq (clr .J) (.seq (clr .G) (clr .JK)))))

/-- The registers at the entry of a stage: `m, d, K`, all others `0`. -/
def vInit (m d K : ℕ) : RegN → ℕ := fun r =>
  match r with
  | .m => m
  | .d => d
  | .K => K
  | _ => 0

theorem closed_stageProgE (IT : RawN) (stA : Bool) : (stageProgE IT stA).Closed := by
  refine ⟨?_, closed_gLoop IT stA, closed_lLoop IT stA, ?_, ?_, ?_⟩ <;>
  simp [setup, dmR, clr, copyR, dec, mulR, divmodU, clearU, copyU, mulU, eqF, ltF, ifNE, incR,
    decR, forDown, whileNE, whileTop, moveU, mv, popR, pushR, peekR, pushC, skip, Prog.Closed,
    Prog.FreeBelow]

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
