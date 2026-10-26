/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamOps
import SubNLogN.Machine.AppC.C5StreamOff
import SubNLogN.Machine.AppC.C5StreamUnitId
import SubNLogN.Machine.AppC.C5StreamHdId
import SubNLogN.Machine.AppC.C5StreamLowMain

/-!
# Proposition A.7 stream kernel (leaf C5-L2): `C5StreamStmt`

**Result.** `c5Stream_holds q m hq op : C5StreamStmt q m op`, for every `q ≥ 2`, every `m` and
every stream operation `op`. There is no further hypothesis. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

`c5Stream_of_lowShift q m hq hLS op` is the same statement with the `lowShift` address-map identity
`StreamAux.LowShiftStmt q m` (`AppC/C5StreamDefs.lean`) as a hypothesis. That identity is proved
as `StreamAux.lowShift_holds` (`AppC/C5StreamLowMain.lean`). The other ingredients are:
* the offset routines `offPlus_holds`, `offMinus_holds` (`AppC/C5StreamOff.lean`);
* the identities `StreamAux.unitPos_holds`, `StreamAux.unitNeg_holds`
  (`AppC/C5StreamUnitId.lean`) and `StreamAux.hdShift_holds` (`AppC/C5StreamHdId.lean`);
* the sub-kernels `K1.k4RotateCtl_holds`, `K1.k5UnitMulMix_holds`, `K1.k5Neg_holds`;
* the assembly `StreamAux.c5Stream_of` (`AppC/C5StreamOps.lean`, on top of
  `C5StreamStep.lean`, `C5StreamAtom.lean`, `C5StreamKern.lean`, and the `NatArith` library `C5StreamArith.lean`).
-/

namespace SubNLogN.Machine.C5

/-- **C5-L2 modulo the `lowShift` identity.** Every valid stream operation of a Proposition A.7 node has an
in-place kernel of cost `C·(V + 1)` (for `2 ≤ q`). -/
theorem c5Stream_of_lowShift (q m : ℕ) (hq : 2 ≤ q) (hLS : StreamAux.LowShiftStmt q m)
    (op : StreamOp m) : C5StreamStmt q m op :=
  StreamAux.c5Stream_of q m hq (offPlus_holds q (by omega)) (offMinus_holds q (by omega))
    (StreamAux.unitPos_holds q m) (StreamAux.unitNeg_holds q m) (StreamAux.hdShift_holds q m)
    hLS op

/-- **[LEAF C5-L2] `C5StreamStmt`.** For `q ≥ 2`, every valid stream operation of a Proposition A.7 node has an
in-place kernel (named stacks `Fin 5`: the array and the counters `k, N1, G, B`) of cost
`C·(V + 1)`. -/
theorem c5Stream_holds (q m : ℕ) (hq : 2 ≤ q) (op : StreamOp m) : C5StreamStmt q m op :=
  c5Stream_of_lowShift q m hq (StreamAux.lowShift_holds q m) op

end SubNLogN.Machine.C5
