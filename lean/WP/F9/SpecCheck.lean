import WP.F9.MulRun

/-!
# WP.F9.SpecCheck — which small root parameters make the snapshot multiplier exact

The pure snapshot value `computablePaperFastDFTMultiply (leafSpec p0 K0) b K0 k1 k2 A B` (with
`p0 = rootPrecision b K0`) is compared with `A * B` on leaf-only chains. This picks the root
parameters for the machine runs of WP.F9 (tiny, fast, exact).
-/

namespace WP.F9.SpecCheck

open IntMul IntMul.LevelSync TMFw TMFw.Contracts TMFw.Contracts.W9 WP.F9.MulRun

/-- `(A, B, snapshot product, A·B)` for root parameters `(b, K0, k1, k2)`. -/
def chk (b K0 k1 k2 A B : ℕ) : ℕ × ℕ × Bool :=
  let v := computablePaperFastDFTMultiply (leafSpec (rootPrecision b K0) K0) b K0 k1 k2 A B
  (A, B, v == A * B)

-- `b = 2`, `K0 = 2` (4 points), `k1 = k2 = 2` (operands below 16).
#eval [chk 2 2 2 2 0 0, chk 2 2 2 2 1 1, chk 2 2 2 2 3 5, chk 2 2 2 2 15 15, chk 2 2 2 2 7 9]
-- `b = 4`, `K0 = 2`, `k1 = k2 = 2` (operands below 256).
#eval [chk 4 2 2 2 255 255, chk 4 2 2 2 200 13]
-- `b = 2`, `K0 = 3` (8 points), `k1 = k2 = 4`.
#eval [chk 2 3 4 4 255 255, chk 2 3 4 4 123 45]

end WP.F9.SpecCheck
