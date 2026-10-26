/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleAddrAxis

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrCost.lean`): the routine's cost expression

**Scope (honest summary).** One definition, no theorem: `costTW C KM Q D v`, the sum of the phase
costs of `twProg` (`TwiddleAddrTop.lean`), in the order and shape of the composition in
`TwiddleAddr.lean`:
`hdrIn` (`13U+10`), counter copy (`U`), pass 1 (`D·(12U+5)+U+1`), `consts` (`21U+10`),
pass 2 (`D·(cAx+2U+1)+U+1`), `finish` (`8U`), `cleanup` (`13U`) and `hdrOut` (`10U+10`). Here
`U = U C KM Q`, and `cAx` (`TwiddleAddrAxis.lean`) is the cost of one axis.
-/

namespace SubNLogN.Machine.FFT.TwAddr

/-- The cost bound of `twProg` (sum of the phases). -/
def costTW (C KM Q D v : ℕ) : ℕ :=
  13 * U C KM Q + 10 + (U C KM Q + ((D * (10 * U C KM Q + 4 + 2 * U C KM Q + 1) + U C KM Q + 1) +
    (21 * U C KM Q + 10 + ((D * (cAx C KM Q v + 2 * U C KM Q + 1) + U C KM Q + 1) +
    (8 * U C KM Q + (13 * U C KM Q + (10 * U C KM Q + 10)))))))

end SubNLogN.Machine.FFT.TwAddr
