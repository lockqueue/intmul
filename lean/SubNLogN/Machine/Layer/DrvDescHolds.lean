/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDesc
import SubNLogN.Machine.Layer.DrvDescArithMain
import SubNLogN.Machine.Layer.DrvDescPiecesHolds

/-!
# Layer driver pre-phase: the descriptor kernel holds (`Machine/Layer/DrvDescHolds.lean`)

**Scope (honest summary).** `drvDesc_holds : DrvDescStmt` (`Machine/Layer/DrvPreDefs.lean`), with no
hypotheses and no `sorry`: the assembly `drvDesc_of` (`Machine/Layer/DrvDesc.lean`) applied to the
proved parts `drvDescArith_holds : DrvDescArithStmt` (`Machine/Layer/DrvDescArithMain.lean`) and
`drvDescPieces_holds : DrvDescPiecesStmt` (`Machine/Layer/DrvDescPiecesHolds.lean`).
-/

namespace SubNLogN.Machine.Layer

/-- **The piece-descriptor kernel of the driver pre-phase** (`DrvDescStmt`): from the layer header,
push `drvDescSyms t` (the C-core descriptors of the base-`m` pieces of `D - q₀`, then the end tag). -/
theorem drvDesc_holds : DrvDescStmt := drvDesc_of drvDescArith_holds drvDescPieces_holds

end SubNLogN.Machine.Layer
