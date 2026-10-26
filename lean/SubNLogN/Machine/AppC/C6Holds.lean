/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Final
import SubNLogN.Machine.AppC.C5NetFinal
import SubNLogN.Math.Networks.Proofs.H2Final
import SubNLogN.Math.Networks.Proofs.InterchangeCorrect
import SubNLogN.Math.Networks.Proofs.AppCFinal
import SubNLogN.Math.Networks.Proofs.InterchangeCounts

/-!
# Arbitrary-width interchange without hypotheses (`Machine/AppC/C6Holds.lean`)

Proves Lemma A.8 (`lem:transfer12`) at the machine level (Table 7 (`tab:lean-map`)): `c6_holds` gives
`KernelCut4.c6` unconditionally, and `c6Interchange_holds τ` holds for every `τ : ℝ`. (`Machine/AppC`
and `C5`/`C6`/`c6` retain earlier draft numbering for stability; see Appendix A (`app:parameter-transfer`).)

Proof: `c6_of_open` / `c6Interchange_of_open` (`AppC/C6Final.lean`), with network hypothesis
discharged by `C5.NetAuxF.c5Net_of` (`AppC/C5NetFinal.lean`) applied to `bitNetCert_holds`,
`interchangeProcCorrect_holds`, `AppCFinalAux.shearFacts_holds`, and `interchangeCallCount_holds`.
-/

namespace SubNLogN.Machine

open SubNLogN.Math.Networks SubNLogN.Math.Cost

namespace C6HoldsAux

/-- The Proposition A.7 (`prop:transfer11`) network leaf `C5.C5NetStmt q` under `C5Params q fac`. -/
theorem c5Net_of_params (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hC : C5Params q fac) : C5.C5NetStmt q :=
  C5.NetAuxF.c5Net_of bitNetCert_holds interchangeProcCorrect_holds AppCFinalAux.shearFacts_holds
    interchangeCallCount_holds q fac hC

end C6HoldsAux

/-- **Lemma A.8 (`lem:transfer12`) (`C6InterchangeStmt τ`) for every `τ`, with no hypotheses.** -/
theorem c6Interchange_holds (τ : ℝ) : C6InterchangeStmt τ :=
  c6Interchange_of_open τ C6HoldsAux.c5Net_of_params

/-- **The `c6` field of `KernelCut4`, with no hypotheses.** -/
theorem c6_holds : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ) :=
  c6_of_open C6HoldsAux.c5Net_of_params

end SubNLogN.Machine
