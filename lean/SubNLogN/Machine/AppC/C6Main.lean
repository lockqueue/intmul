/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Q
import SubNLogN.Machine.AppC.C6Low
import SubNLogN.Machine.AppC.C6Pieces

/-!
# Lemma A.8 (`Machine/AppC/C6Main.lean`): the skeleton chained

**Theorems** (fully proved reductions, `lem:transfer12`; for any `q ≥ 2`):
* `c6Interchange_of_lowParts` (levels A-C): chains `c6Interchange_of_eq` (level A, `C6Top.lean`),
  `c6Eq_of_radix` (level B, `C6Eq.lean`) and `c6Q_of_parts` (level C, `C6Q.lean`).
* `c6Interchange_of_lowerParts` (levels A-D): `C6LowStmt q τ` replaced via `c6Low_of_parts`
  (level D, `C6Low.lean`: row padding, the base-`m` pieces, row unpadding).
* `c6Interchange_of_parts` (levels A-E): `C6PiecesStmt q τ` replaced via `c6Pieces_of_parts`
  (level E, `C6Pieces.lean`: the greedy piece loop over Proposition A.7). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

Leaves of `c6Interchange_of_parts` (statements in `Contracts/AppC.lean`, `C6Leaves.lean`,
`C6QLeaves.lean`, `C6LowLeaves.lean`, `C6PiecesLeaves.lean`):
* `C5InterchangeStmt q τ` (Proposition A.7);
* `C6BitMoveStmt true/false` (the single-bit moves);
* `C6RadixPadStmt q`, `C6RadixUnpadStmt q` (numerical padding of both coordinates);
* `C6SmallTestStmt`, `C6SmallStmt q` (`e ≤ 34`), `C6HighJoinStmt q`, `C6UnjoinStmt q`;
* `C6RowPadStmt q`, `C6RowUnpadStmt q` (row padding of `[q^{2t}]` to a multiple of `W_b^k`);
* `C6PcTestStmt q`, `C6PcArgsStmt q`, `C6PcAdvStmt q` (counter arithmetic of the piece loop).
-/

namespace SubNLogN.Machine

/-- **Lemma A.8 skeleton, levels A-C.** -/
theorem c6Interchange_of_lowParts {q : ℕ} {τ : ℝ} (hq : 2 ≤ q)
    (hBR : C6BitMoveStmt true) (hBL : C6BitMoveStmt false)
    (hPad : C6RadixPadStmt q) (hUnpad : C6RadixUnpadStmt q)
    (hTest : C6SmallTestStmt) (hSmall : C6SmallStmt q) (hHJ : C6HighJoinStmt q)
    (hLow : C6LowStmt q τ) (hUJ : C6UnjoinStmt q) : C6InterchangeStmt τ :=
  c6Interchange_of_eq
    (c6Eq_of_radix hq (c6Q_of_parts hq hTest hSmall hHJ hLow hUJ) hPad hUnpad) hBR hBL

/-- **Lemma A.8 skeleton, levels A-D.** -/
theorem c6Interchange_of_lowerParts {q : ℕ} {τ : ℝ} (hq : 2 ≤ q)
    (hBR : C6BitMoveStmt true) (hBL : C6BitMoveStmt false)
    (hPad : C6RadixPadStmt q) (hUnpad : C6RadixUnpadStmt q)
    (hTest : C6SmallTestStmt) (hSmall : C6SmallStmt q) (hHJ : C6HighJoinStmt q)
    (hUJ : C6UnjoinStmt q) (hRP : C6RowPadStmt q) (hPc : C6PiecesStmt q τ)
    (hRU : C6RowUnpadStmt q) : C6InterchangeStmt τ :=
  c6Interchange_of_lowParts hq hBR hBL hPad hUnpad hTest hSmall hHJ
    (c6Low_of_parts hq hRP hPc hRU) hUJ

/-- **Lemma A.8, levels A-E**: Proposition A.7 and the leaf contracts give `C6InterchangeStmt τ`. -/
theorem c6Interchange_of_parts {q : ℕ} {τ : ℝ} (hq : 2 ≤ q) (h5 : C5InterchangeStmt q τ)
    (hBR : C6BitMoveStmt true) (hBL : C6BitMoveStmt false)
    (hPad : C6RadixPadStmt q) (hUnpad : C6RadixUnpadStmt q)
    (hTest : C6SmallTestStmt) (hSmall : C6SmallStmt q) (hHJ : C6HighJoinStmt q)
    (hUJ : C6UnjoinStmt q) (hRP : C6RowPadStmt q) (hRU : C6RowUnpadStmt q)
    (hPT : C6PcTestStmt q) (hPA : C6PcArgsStmt q) (hPV : C6PcAdvStmt q) :
    C6InterchangeStmt τ :=
  c6Interchange_of_lowerParts hq hBR hBL hPad hUnpad hTest hSmall hHJ hUJ hRP
    (c6Pieces_of_parts hq h5 hPT hPA hPV) hRU

end SubNLogN.Machine
