/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Kit
import SubNLogN.Machine.AppC.C5Final

/-!
# Proposition A.7 from its leaves (`AppC/C5Parts.lean`)

`c5Interchange_of_parts`: the Proposition A.7 contract `C5InterchangeStmt q τ` (Proposition A.7 (`prop:transfer11`),
Appendix A.2 (`sec:transfer-power`)) from the named leaves:
* `C5NetStmt q` (L6-L8, pure network math: a concrete network instance with `W_b` roles, at most
  `s_b` children per node, valid stream operations, XOR gates on distinct roles, and node
  correctness `NodeCorrect`);
* `C5StreamStmt q m op` for all `op` (L2, streaming kernels of the node; only valid ops are used);
* `C5XorStmt` (L3, the elementary XOR gate);
* `C5DescStmt q m i j` for all pivots (L4, child descriptor) and `C5RowSizeStmt q m` (L5);
with `m = tripleM 100` and `2 ≤ q`. The level-`0` swap (`K1PairPermMix`) and the cyclic row
distribution/merge (`K2DistributeBlk`, `K2MergeBlk`) are proved kernels, used directly.
Program: one `fix`-recursive machine program (`c5Prog`, `AppC/C5Skel.lean`) on the kit
`theKit` (`AppC/C5Kit.lean`); correctness and cost by `kit_runs` (`AppC/C5Node.lean`) and
`c5Interchange_of_kit` (`AppC/C5Final.lean`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.C5

/-- **Proposition A.7 from its leaves** (Proposition A.7 (`prop:transfer11`),
including the recurrence cost bound). Hypotheses: `2 ≤ q` (the radix of the digit fields; the intended instantiation is
the odd prime from `ExistsValidFacStmt`), the network leaf `C5NetStmt q` (L6-L8), and the kernel
leaves L2 (`C5StreamStmt`, for every stream operation), L3 (`C5XorStmt`), L4 (`C5DescStmt`, for
every pivot) and L5 (`C5RowSizeStmt`), all at `m = tripleM 100`. No other assumption. -/
theorem c5Interchange_of_parts (q : ℕ) (τ : ℝ) (hq2 : 2 ≤ q) (hNet : C5NetStmt q)
    (hL2 : ∀ op : StreamOp (tripleM 100), C5StreamStmt q (tripleM 100) op)
    (hL3 : C5XorStmt) (hL4 : ∀ i j : Fin (tripleM 100), C5DescStmt q (tripleM 100) i j)
    (hL5 : C5RowSizeStmt q (tripleM 100)) : C5InterchangeStmt q τ := by
  obtain ⟨D, hnode, hcalls, hvalid, hgates⟩ := hNet
  have : NeZero q := ⟨by omega⟩
  have hL : Leaves q D := ⟨hL2, hvalid, hL3, hL4, hL5, hgates⟩
  have hNF := netFacts_of_data q (by omega) D (tripleSb 100) hnode hcalls
  have hW : 0 < tripleWb 100 := by rw [S1.tripleWb_100]; norm_num
  exact c5Interchange_of_kit q τ hq2 hNF (theKit hL hW) rfl rfl rfl rfl rfl

end SubNLogN.Machine
