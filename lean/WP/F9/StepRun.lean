import WP.F9.MulRun
import WP.F9.Top

/-!
# WP.F9.StepRun — harness for chains with a step level (PRE and POST nodes in the real pipeline)

On the headline schedule every planned input runs on a leaf-only chain (WP.F9.Top), so the
end-to-end runs never execute the PRE/POST node kernels. This harness builds a **step-level chain**
on purpose:

`stepChain p K := buildComputablePaperTables (quantizedBoxGaussianStepSpec p K (.base (pChild p K)
(2 ^ (K − K/2))))`

It has one PRE level, one LEAF level and one POST level, with `t1 = 2^(K/2)` and `r = 2^(K − K/2)`.
The snapshot proves the spec valid for `8 ≤ p` and `2 ≤ K` (`quantizedBoxGaussianStepSpec_valid`).
Its tables come from the snapshot's computable builder.

`P9stepOf rowK colK` is `P9C` with the two remaining kernels plugged in: the spread row kernel
(inside the W9cS driver) and the column solver. Once those exist concretely,
`runMulIx (P9stepOf rowC colC) … (stepChain p0 K0) …` checks `W9_multiply`'s post-state, where `OA`
holds `computablePaperFastDFTMultiply` at those parameters, and also compares it with `A·B`. That run
executes every node kernel (P1–P8, Q2–Q6) inside the real pipeline. For example: `b = 1`, `K0 = 2`,
`k1 = k2 = 2`, `p0 = rootPrecision 1 2 = 12`.
-/

namespace WP.F9.StepRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.F9.MulRun

/-- A valid chain with one step level over a radix-2 leaf. -/
def stepChain (p K : ℕ) : ComputablePaperFastDFTSpec :=
  buildComputablePaperTables (quantizedBoxGaussianStepSpec p K (.base (pChild p K) (2 ^ (K - K / 2))))

section Plug

variable {mr mq : ℕ} {Rr Rq : Type}

/-- `P9C` with the spread row kernel `rowK` and the column solver `colK`. -/
def P9stepOf (rowK : Prog (BLoc mr) (fun _ => Sym) Rr) (colK : Prog (BLoc mq) (fun _ => Sym) Rq) :=
  P9of (WP.W9cS.Concrete.progC rowK) WP.W9d.Concrete.Pre.progC WP.W9s.Concrete.progC
    WP.W9d.Concrete.Post.progC colK WP.W9gx.Concrete.progC WP.W9sp.Concrete.progC
    WP.W9sq.Concrete.progC WP.W9ex.Concrete.progC WP.W9h.Concrete.progC

/-- Its initial registers. -/
def P9stepR0 (r0r : Rr) (r0q : Rq) :=
  P9r0of (WP.W9cS.Concrete.r0C r0r) WP.W9d.Concrete.Pre.r0C WP.W9s.Concrete.r0C
    WP.W9d.Concrete.Post.r0C r0q WP.W9gx.Concrete.r0C WP.W9sp.Concrete.r0C WP.W9sq.Concrete.r0C
    WP.W9ex.Concrete.r0C WP.W9h.Concrete.r0C

/-- The step-chain multiply run: `(stacks ok, snapshot value = A·B, steps)`. -/
def rowStep (rowK : Prog (BLoc mr) (fun _ => Sym) Rr) (r0r : Rr)
    (colK : Prog (BLoc mq) (fun _ => Sym) Rq) (r0q : Rq) (b K0 k A B fuel : ℕ) : Bool × Bool × ℕ :=
  runMulIx (P9stepOf rowK colK) (P9stepR0 r0r r0q) (stepChain (IntMul.rootPrecision b K0) K0)
    b K0 k k A B fuel

end Plug

/-- Pure cross-check at the step chain: `(snapshot value, A·B)`. -/
def pureStep (b K0 k A B : ℕ) : ℕ × ℕ :=
  (computablePaperFastDFTMultiply (stepChain (IntMul.rootPrecision b K0) K0) b K0 k k A B, A * B)

-- The snapshot value at the step chain, against `A·B`.
#eval [pureStep 1 2 2 3 2, pureStep 1 2 2 1 1, pureStep 1 2 2 3 3]

end WP.F9.StepRun
