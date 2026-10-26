/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Parts
import SubNLogN.Machine.AppC.C5RowSize
import SubNLogN.Machine.AppC.C5Xor

/-!
# Proposition A.7 with the counter leaves discharged (`AppC/C5Parts2.lean`)

`c5Interchange_of_net`: `c5Interchange_of_parts` with L4 (`c5Desc_holds`, `AppC/C5Desc.lean`) and
L5 (`c5RowSize_holds`, `AppC/C5RowSize.lean`) plugged in (both proved for `2 ≤ q`,
`2 ≤ m`). Remaining hypotheses: the network leaf `C5NetStmt q` (L6-L8) and the kernel leaves L2
(`C5StreamStmt`) and L3 (`C5XorStmt`). `c5Interchange_of_net_stream` also plugs in L3
(`c5Xor_holds`, `AppC/C5Xor.lean`): only `C5NetStmt q` and L2 remain. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine

open SubNLogN.Machine.C5

/-- **Proposition A.7 from the network leaf and the stream/XOR kernels** (Proposition A.7 (`prop:transfer11`),
Appendix A.2 (`sec:transfer-power`)). Hypotheses: `2 ≤ q`, `C5NetStmt q`,
`C5StreamStmt q (tripleM 100) op` for every `op`, and `C5XorStmt`. -/
theorem c5Interchange_of_net (q : ℕ) (τ : ℝ) (hq2 : 2 ≤ q) (hNet : C5NetStmt q)
    (hL2 : ∀ op : StreamOp (tripleM 100), C5StreamStmt q (tripleM 100) op) (hL3 : C5XorStmt) :
    C5InterchangeStmt q τ := by
  have hm : 2 ≤ tripleM 100 := by rw [S1.tripleM_100]; norm_num
  exact c5Interchange_of_parts q τ hq2 hNet hL2 hL3 (c5Desc_holds hq2 hm) (c5RowSize_holds hq2 hm)

/-- **Proposition A.7 from the network leaf and the stream kernels** (Proposition A.7 (`prop:transfer11`),
Appendix A.2 (`sec:transfer-power`)): `c5Interchange_of_net` with L3 discharged
by `c5Xor_holds` (`AppC/C5Xor.lean`). Hypotheses: `2 ≤ q`, `C5NetStmt q`, and
`C5StreamStmt q (tripleM 100) op` for every `op`. -/
theorem c5Interchange_of_net_stream (q : ℕ) (τ : ℝ) (hq2 : 2 ≤ q) (hNet : C5NetStmt q)
    (hL2 : ∀ op : StreamOp (tripleM 100), C5StreamStmt q (tripleM 100) op) :
    C5InterchangeStmt q τ :=
  c5Interchange_of_net q τ hq2 hNet hL2 c5Xor_holds

end SubNLogN.Machine
