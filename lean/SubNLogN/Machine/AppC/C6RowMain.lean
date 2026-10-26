/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RowPass
import SubNLogN.Machine.AppC.C6RowCtr
import SubNLogN.Machine.AppC.C6RowCtrCostProof

/-!
# Lemma A.8 row padding / unpadding: assembly (`Machine/AppC/C6RowMain.lean`)

**Proved (0 `sorry`):** `c6RowPad_holds (q) (hq : 2 ≤ q) : C6RowPadStmt q` and
`c6RowUnpad_holds (q) (hq : 2 ≤ q) : C6RowUnpadStmt q` (the contracts of `C6LowLeaves.lean`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

`c6RowPad_of_cost`, `c6RowUnpad_of_cost`: the same contracts from the cost bound `CtrCostStmt` of
the counter kernel (`C6RowCost.lean`): the block passes (`C6RowPass.lean`) with the counter kernel
(`C6RowCtr.lean`) built from the `t` / `W_b^k` kernels of `C6TArith.lean` (`c6TPush_holds`,
`c6WPush_holds`) and the long division `W6a_divModNat`. The cost bound is `ctrCost_holds`
(`C6RowCtrCostProof.lean`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-- **Row padding** from the cost bound of the counter kernel. -/
theorem c6RowPad_of_cost (q : ℕ) (hq : 2 ≤ q)
    (hCost : ∀ CT CW CD : ℕ, AppC.C6RowAux.CtrCostStmt q CT CW CD) : C6RowPadStmt q :=
  AppC.C6RowAux.c6RowPad_of hq (AppC.C6RowAux.c6RowCtr_of hq (AppC.C6JoinAux.c6TPush_holds hq)
    AppC.C6JoinAux.c6WPush_holds hCost)

/-- **Row unpadding** from the cost bound of the counter kernel. -/
theorem c6RowUnpad_of_cost (q : ℕ) (hq : 2 ≤ q)
    (hCost : ∀ CT CW CD : ℕ, AppC.C6RowAux.CtrCostStmt q CT CW CD) : C6RowUnpadStmt q :=
  AppC.C6RowAux.c6RowUnpad_of hq (AppC.C6RowAux.c6RowCtr_of hq (AppC.C6JoinAux.c6TPush_holds hq)
    AppC.C6JoinAux.c6WPush_holds hCost)

/-- **Row padding** (Lemma A.8 (`lem:transfer12`)): `C6RowPadStmt q` for every `q ≥ 2`. -/
theorem c6RowPad_holds (q : ℕ) (hq : 2 ≤ q) : C6RowPadStmt q :=
  c6RowPad_of_cost q hq (fun CT CW CD => AppC.C6RowAux.ctrCost_holds hq CT CW CD)

/-- **Row unpadding** (Lemma A.8 (`lem:transfer12`)): `C6RowUnpadStmt q` for every `q ≥ 2`. -/
theorem c6RowUnpad_holds (q : ℕ) (hq : 2 ≤ q) : C6RowUnpadStmt q :=
  c6RowUnpad_of_cost q hq (fun CT CW CD => AppC.C6RowAux.ctrCost_holds hq CT CW CD)

end SubNLogN.Machine
