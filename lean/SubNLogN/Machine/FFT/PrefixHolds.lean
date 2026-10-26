/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.Prefix
import SubNLogN.Machine.FFT.PrefixPass
import SubNLogN.Machine.Arith.Shift
import SubNLogN.Machine.FFT.PrefixParam

/-!
# K4-PREFIX, `PrefixRoundStmt` with the proved sub-kernels (`Machine/FFT/PrefixHolds.lean`)

**Scope (honest summary).** `prefixRound_holds : PrefixRoundStmt` is unconditional. It plugs three
proved kernels into `prefixRound_of` (`Prefix.lean`):
* the parameter phase `prefixParam_holds` (`PrefixParam.lean`);
* the exact butterfly pass `PrefixPassAux.prefixPass_holds` (`PrefixPass.lean`, from
  `Arith.cAdd_holds`/`Arith.cSub_holds`);
* the truncation `Arith.truncShift_holds`.

`prefixRound_of_param` is the variant with the parameter phase as a hypothesis. No `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

/-- **`PrefixRoundStmt` from the parameter phase**, with the proved pass and truncation kernels. -/
theorem prefixRound_of_param (hPar : PrefixParamStmt) : PrefixRoundStmt :=
  prefixRound_of hPar PrefixPassAux.prefixPass_holds Arith.truncShift_holds

/-- **`PrefixRoundStmt`, unconditionally.** -/
theorem prefixRound_holds : PrefixRoundStmt :=
  prefixRound_of prefixParam_holds PrefixPassAux.prefixPass_holds Arith.truncShift_holds

end SubNLogN.Machine.FFT.PrefixAux
