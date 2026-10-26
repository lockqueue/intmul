/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# K7 (`Machine/Pipe/ReadParamsCost.lean`): the step bound of the runtime-parameter kernel

`readParamsCost b K0 p_in` is the step bound charged for `ReadParamsStmt` (`BranchDefs.lean`, as
`C * rpCost b K0 p_in` with `rpCost := readParamsCost`). It is a closed polynomial in
`b + K0 + p_in`, kept stable for the cost absorption (`Math/Cost`). The kernel proof
(`readParams_holds`) is proved against this bound.
-/

namespace SubNLogN.Machine.Pipe

/-- Step bound of the runtime-parameter kernel at `(b, K0, p_in)`: `(b + K0 + p_in + 16)^6`. -/
def readParamsCost (b K0 pin : Nat) : Nat := (b + K0 + pin + 16) ^ 6

end SubNLogN.Machine.Pipe
