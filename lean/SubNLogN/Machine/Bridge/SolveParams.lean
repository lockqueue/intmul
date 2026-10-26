/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsFinal
import SubNLogN.Machine.Bridge.SolveParamsHdr

/-!
# SOL-PARAM-ROWS: `SolParamRowsStmt`

`solParamRows_holds`: the solver parameter-row kernel. It runs the header parse
`SolveParamsHdrAux.hdrParse` (K5-SOLVE, `SolveParamsHdr.lean`), then `SolveParamsAux.bodyB`
(`SolveParamsAsm.lean`). The kernel contract is assembled by `SolveParamsAux.solParamRows_of_hdr`
(`SolveParamsFinal.lean`). Fully proved.
-/

namespace SubNLogN.Machine

/-- **[PROVED] `SolParamRowsStmt`**: the solver parameter rows of one half of a deconvolution
stage. -/
theorem solParamRows_holds : SolParamRowsStmt :=
  Bridge.SolveParamsAux.solParamRows_of_hdr Bridge.SolveParamsHdrAux.hdrParse
    Bridge.SolveParamsHdrAux.hdrParse_closed Bridge.SolveParamsHdrAux.runs_hdrParse

end SubNLogN.Machine
