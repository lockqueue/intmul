/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractAssemble
import SubNLogN.Machine.AppC.C7BadTriMain
import SubNLogN.Machine.AppC.C7ExtractSetupProof
import SubNLogN.Machine.AppC.C7ExtractCost

/-!
# Repair-phase extraction for Lemma A.9 (`Machine/AppC/C7ExtractHolds.lean`)

Establishes `SubNLogN.Machine.c7Extract_holds σ : C7ExtractStmt σ` (`Machine/AppC/C7RepairDefs.lean`;
Lemma A.9 (`lem:transfer13`), Table 7 (`tab:lean-map`)), with no hypotheses, by applying
`c7Extract_of_parts` (`C7ExtractAssemble.lean`) to three proved components:
* `c7BadTri_holds` (`C7BadTriMain.lean`), `c7XSetup_holds` (`C7ExtractSetupProof.lean`), and
* `c7XCost_holds` (`C7ExtractCost.lean`).
(`Machine/AppC` and `C7`/`c7` retain an earlier draft's numbering for identifier stability;
they formalize Appendix A (`app:parameter-transfer`) and Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

/-- **Repair-phase extraction of Lemma A.9 (`lem:transfer13`)** (`C7ExtractStmt σ`), unconditional. -/
theorem c7Extract_holds (σ : Equiv.Perm (Fin 3)) : C7ExtractStmt σ :=
  c7Extract_of_parts σ c7BadTri_holds AppC.C7ExtractAux.c7XSetup_holds
    AppC.C7ExtractAux.c7XCost_holds

end SubNLogN.Machine
