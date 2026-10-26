/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Main
import SubNLogN.Machine.AppC.C6BitMove
import SubNLogN.Machine.AppC.C6Radix
import SubNLogN.Machine.AppC.C6PcArgs
import SubNLogN.Machine.AppC.C6PcAdv

/-!
# Lemma A.8 assembly (`Machine/AppC/C6Assembly.lean`): plugging in the proved leaves

`c6Interchange_of_parts` (`C6Main.lean`) with the leaves that are already proved discharged:
* `c6BitMove_holds true/false` (`C6BitMove.lean`);
* `c6RadixPad_holds q hq`, `c6RadixUnpad_holds q hq` (`C6Radix.lean`);
* `c6PcTest_holds q hq`, `c6PcArgs_holds q hq`, `c6PcAdv_holds q hq` (`C6Pc*.lean`).

**Theorem** (`c6Interchange_of_remaining`, a reduction): for `q ≥ 2`, `C6InterchangeStmt τ` follows
from Proposition A.7 (`C5InterchangeStmt q τ`) and the remaining leaves `C6SmallTestStmt`, `C6SmallStmt q`,
`C6HighJoinStmt q`, `C6UnjoinStmt q`, `C6RowPadStmt q`, `C6RowUnpadStmt q`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

/-- **Lemma A.8 (`lem:transfer12`) with the proved leaves plugged in.** -/
theorem c6Interchange_of_remaining {q : ℕ} {τ : ℝ} (hq : 2 ≤ q) (h5 : C5InterchangeStmt q τ)
    (hTest : C6SmallTestStmt) (hSmall : C6SmallStmt q) (hHJ : C6HighJoinStmt q)
    (hUJ : C6UnjoinStmt q) (hRP : C6RowPadStmt q) (hRU : C6RowUnpadStmt q) :
    C6InterchangeStmt τ :=
  c6Interchange_of_parts hq h5 (c6BitMove_holds true) (c6BitMove_holds false)
    (c6RadixPad_holds q hq) (c6RadixUnpad_holds q hq) hTest hSmall hHJ hUJ hRP hRU
    (c6PcTest_holds q hq) (c6PcArgs_holds q hq) (c6PcAdv_holds q hq)

end SubNLogN.Machine
