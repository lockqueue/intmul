/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescPieces

/-!
# DrvDesc PIECES: closedness (`Machine/Layer/DrvDescPiecesClosed.lean`)

Every subprogram of the piece-descriptor kernel (`DrvDescPiecesStmt`, `DrvDescDefs.lean`) is closed
(no free `recur`). The proofs assemble the closedness rules of `DrvDescPiecesKit.lean`
(`closed_pushW`, …, `closed_whileW`): `(.seq p q).Closed` unfolds to `p.Closed ∧ q.Closed`.

**Scope (honest summary).** Proved: `closed_piecesProg : piecesProg.Closed` (the kernel of
`DrvDescPieces.lean`), from the closedness of its parts: the emission and digit programs of
`DrvDescPiecesProg.lean` (`cl_emitF`, `cl_emitDesc`, `cl_innerStep`, `cl_entryStep`, `cl_dsA`,
`cl_dsB`, `cl_digitStep`, `cl_digitLoop`, `cl_emitLoop`) and the parse, initialization and clean-up
programs of `DrvDescPieces.lean` (`cl_parseF`, `cl_parseProg`, `cl_initProg`, `cl_cleanupProg`).
-/

namespace SubNLogN.Machine.Layer.DrvDescPiecesAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine

theorem cl_emitF (src : PE) : (emitF src).Closed := ⟨closed_pushW _ _, closed_copyW _ _ _⟩

theorem cl_emitDesc : emitDesc.Closed :=
  ⟨cl_emitF _, cl_emitF _, cl_emitF _, cl_emitF _, cl_emitF _, cl_emitF _, cl_emitF _, cl_emitF _,
    cl_emitF _, cl_emitF _, cl_emitF _, cl_emitF _⟩

theorem cl_innerStep : innerStep.Closed :=
  ⟨closed_decW _ _, closed_pushW _ _, closed_mulP _ _ _ _ _ _ _, closed_addTo _ _ _ _ _ _,
    cl_emitDesc, closed_dropFW _⟩

theorem cl_entryStep : entryStep.Closed :=
  ⟨closed_pushW _ _, closed_copyW _ _ _, closed_whileW _ _ cl_innerStep, closed_dropFW _,
    closed_dropFW _, closed_dropFW _, closed_dropFW _, closed_dropFW _⟩

theorem cl_dsA : dsA.Closed :=
  ⟨closed_pushW _ _, closed_pushW _ _, closed_dmP _ _ _ _ _ _ _, closed_dropW _, closed_copyW _ _ _,
    closed_dropFW _, closed_pushW _ _, closed_copyW _ _ _, closed_pushW _ _, closed_copyW _ _ _,
    closed_pushW _ _, closed_copyW _ _ _⟩

theorem cl_dsB : dsB.Closed :=
  ⟨closed_pushW _ _, closed_mulP _ _ _ _ _ _ _, closed_addTo _ _ _ _ _ _, closed_dropFW _,
    closed_mulBy _ _ _ _ _ _ _, closed_incW _ _⟩

theorem cl_digitStep : digitStep.Closed := ⟨cl_dsA, cl_dsB⟩

theorem cl_digitLoop : (whileW (sx .q) optIsBit digitStep).Closed :=
  closed_whileW _ _ cl_digitStep

theorem cl_emitLoop : (whileW (sx .tA) notSep entryStep).Closed :=
  closed_whileW _ _ cl_entryStep

theorem cl_parseF (f : PE) : (parseF f).Closed :=
  ⟨closed_pushW _ _, closed_copyW _ _ _, closed_dropW _, closed_popW _⟩

theorem cl_parseProg : parseProg.Closed :=
  ⟨closed_pushW _ _, closed_copyHdrW _ _ _ _, closed_popW _, cl_parseF _, cl_parseF _, cl_parseF _,
    cl_parseF _, cl_parseF _, cl_parseF _, cl_parseF _, cl_parseF _, cl_parseF _⟩

theorem cl_initProg : initProg.Closed :=
  ⟨closed_pushW _ _, closed_pushW _ _, closed_pushNatP _ _, closed_pushW _ _, closed_copyW _ _ _,
    closed_pushW _ _, closed_pushW _ _, closed_pushW _ _, closed_pushW _ _, closed_pushW _ _,
    closed_pushW _ _, closed_pushNatP _ _, closed_pushW _ _⟩

theorem cl_cleanupProg : cleanupProg.Closed :=
  ⟨closed_popW _, closed_popW _, closed_popW _, closed_popW _, closed_dropFW _, closed_dropFW _,
    closed_dropFW _, closed_dropFW _, closed_dropFW _, closed_dropFW _, closed_dropFW _,
    closed_dropFW _, closed_dropFW _, closed_dropFW _, closed_dropFW _, closed_dropFW _,
    closed_dropFW _, closed_dropFW _⟩

/-- **[PROVED] The piece-descriptor kernel is closed.** -/
theorem closed_piecesProg : piecesProg.Closed :=
  ⟨cl_parseProg, cl_initProg, cl_digitLoop, cl_emitLoop, cl_cleanupProg⟩

end SubNLogN.Machine.Layer.DrvDescPiecesAux
