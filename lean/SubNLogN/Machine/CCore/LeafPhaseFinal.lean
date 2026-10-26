/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhase
import SubNLogN.Machine.CCore.LeafPhaseMaskSelFinal

/-!
# C-core leaf 8: the phase kernel, unconditional (`CCore/LeafPhaseFinal.lean`)

**Result.** `phase_holds (p : LayerParams) : PhaseStmt p` (`CCore/SkelDefs.lean:257`), with no
hypothesis: `phase_holds_of` (`CCore/LeafPhase.lean`) applied to the proved machine statement
`maskSel_holds : MaskSelStmt` (`CCore/LeafPhaseMaskSelFinal.lean`, the record-wise sign selection of
the phase kinds `zSlot`/`zMask`). The other inputs are the proved `Layer.DrvPreK.rotIPow_holds`
(`×i^e`) and `maskVal_holds` (value identification of `zSlot`/`zMask`).
Paper: Lemma A.10 (`lem:transfer-phase`), Section A.5 (the phases `Z_{a,f}`, `Z^{⊗f}`, `(-i)^f`, `i^{27f}`,
`-1` at an internal node) and Lemma A.5 (`lem:transfer-long-record`; per-record streaming phase scans).
Cutoff `P₀ = 1`; cost `C·t.volG` with `C = 2000 + 10·C_rot + 20·C_ms + 20·Cd p` (`phaseC`).
-/

namespace SubNLogN.Machine.CCore

/-- **[LEAF 8] The phase kernel** (`PhaseStmt p`, unconditional). -/
theorem phase_holds (p : LayerParams) : PhaseStmt p := phase_holds_of maskSel_holds p

end SubNLogN.Machine.CCore
