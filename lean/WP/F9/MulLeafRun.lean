import WP.F9.MulRun
import WP.F9.Top

/-!
# WP.F9.MulLeafRun — the whole W9 multiplier on leaf-only chains, run

`P9leaf` is `P9of` (WP.F9.Pipe), i.e. `W9_multiply_of_parts_holds`'s witness over the pipeline's
witness. It carries the concrete root and leaf kernels:
* splitPack: `WP.W9sp.Concrete`;
* square: `WP.W9sq.Concrete`;
* extract: `WP.W9ex.Concrete`;
* reconstruct: `WP.W9h.Concrete`;
* leaf FFT: `WP.W9gx.Concrete`.

On a leaf-only chain (`leafSpec`) the node kernels are never executed, so their slots hold `holeB`.
`runMulIx` (WP.F9.MulRun, the indexed runner) checks every stack against `W9_multiply`'s post-state
`OA = natSyms (computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B) ++ rA`, and checks that this
snapshot value is `A * B`.
-/

namespace WP.F9.MulLeafRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.F9.MulRun

/-- The W9 multiplier (WP.F9.Top, version 1). -/
abbrev P9leaf := WP.F9.Top.P9C

/-- Its initial registers. -/
abbrev P9leafR0 := WP.F9.Top.r9

/-- `A·B` with root parameters `b`, `K0`, `k1 = k2 = k` on the leaf-only chain of size `2^K0`:
`(stacks ok, snapshot value = A·B, steps)`. -/
def rowM (b K0 k A B : ℕ) : Bool × Bool × ℕ :=
  runMulIx P9leaf P9leafR0 (leafSpec (IntMul.rootPrecision b K0) K0) b K0 k k A B 30000000

-- `3 · 5` with `b = 2`, `K0 = 2`, `k = 2` (a 4-point transform) gave `(true, true, 2250826)`
-- (requiring about 110 s with the indexed runner, above the 60 s smoke-test budget).
-- The smoke run uses the 2-point transform: `13 · 11` with `b = 4`, `K0 = 1`, `k = 1`.
#eval rowM 4 1 1 13 11

end WP.F9.MulLeafRun
