/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapPh
import SubNLogN.Machine.Tables.TapPhBlockHolds

/-!
# K6 (`Machine/Tables/TapPhHolds.lean`): the tap phase, `tapPhase_holds`

**Scope (honest summary).** `tapPhase_holds : TapRecStmt → TapBlockRankStmt → TapPhaseStmt`:
the tap-phase driver `tapPhase_of_block` (`TapPh.lean`) applied to BC's proof of the per-axis block
`TapPhBlock.tapBlock_holds : TapRecStmt → TapBlockStmt` (`TapPhBlockHolds.lean`). The record order
`TapBlockRankStmt` is proved there (`tapBlockRank_holds`), so the hypothesis `_hRank` (kept for the
agreed interface) is not used.
-/

namespace SubNLogN.Machine.Tables

/-- **The tap phase** (`TapPhaseStmt`) from the tap-record machine (`TapRecStmt`). -/
theorem tapPhase_holds (hTap : TapRecStmt) (_hRank : TapBlockRankStmt) : TapPhaseStmt :=
  tapPhase_of_block (TapPhBlock.tapBlock_holds hTap)

end SubNLogN.Machine.Tables
