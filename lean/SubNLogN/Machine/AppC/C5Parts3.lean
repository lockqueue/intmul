/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Parts2
import SubNLogN.Machine.AppC.C5StreamMain

/-!
# Proposition A.7 from the network leaf only (`AppC/C5Parts3.lean`)

`c5Interchange_of_netStmt`: `c5Interchange_of_net_stream` with the stream kernels (leaf L2)
discharged by `c5Stream_holds` (`AppC/C5StreamMain.lean`, for `2 ≤ q`). The only
remaining hypothesis is the network leaf `C5NetStmt q` (L6-L8). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine

open SubNLogN.Machine.C5

/-- **Proposition A.7 from the network leaf** (Proposition A.7 (`prop:transfer11`),
Appendix A.2 (`sec:transfer-power`)). Hypotheses: `2 ≤ q` and
`C5NetStmt q`. -/
theorem c5Interchange_of_netStmt (q : ℕ) (τ : ℝ) (hq2 : 2 ≤ q) (hNet : C5NetStmt q) :
    C5InterchangeStmt q τ :=
  c5Interchange_of_net_stream q τ hq2 hNet (fun op => c5Stream_holds q (tripleM 100) hq2 op)

end SubNLogN.Machine
