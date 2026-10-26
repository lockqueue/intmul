/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescPiecesClosed

/-!
# DrvDesc PIECES, part 5 (`Machine/Layer/DrvDescPiecesHolds.lean`): the contract

**Scope (honest summary).** `drvDescPieces_holds : DrvDescPiecesStmt` (`DrvDescDefs.lean`), with
`J = 3` and `C = 10^12`, from the closed kernel `DrvDescPiecesAux.piecesProg`
(`DrvDescPieces.lean`; closedness in `DrvDescPiecesClosed.lean`) and its exact run
`DrvDescPiecesAux.runs_piecesProg`. Everything here is proved.
-/

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- **[PROVED] Piece descriptors from a value record** (`DrvDescPiecesStmt`). -/
theorem drvDescPieces_holds : DrvDescPiecesStmt :=
  ⟨3, 10 ^ 12, fun _ => ⟨DrvDescPiecesAux.PE, inferInstance, inferInstance,
    DrvDescPiecesAux.PReg, DrvDescPiecesAux.piecesProg, inferInstance, inferInstance,
    DrvDescPiecesAux.closed_piecesProg,
    fun P d r a R K e S ρ vrest Sk hR => WP.W9comp.runs_mono
      (DrvDescPiecesAux.runs_piecesProg P d r a R K e S ρ vrest Sk hR) (fun _ _ => trivial)
      (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))⟩⟩

end SubNLogN.Machine.Layer
