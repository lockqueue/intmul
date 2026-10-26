import WP.W9c.PassMain

/-!
# WP.W9c.PassCostSpec — the pass cost in the budget's terms (statement only)

`passT` (`WP.W9c.PassMain`) is the exact cost of one coordinate pass, as composed from the kit
costs. `PassTBound` states it in the units of `spreadRowBound`: `nb` W5 products at the declared
width `(W+1)(s+w)`, plus `O((W+1)(s+w+p_in+2))` per block, plus `O((r+W)(s+5))` per pass. Here
`r = zl + zr`, the digit/bucket/cell bit lengths are `k, k+1, k+3`, `k ≤ s + 1`, `q ≤ s`,
`ol ≤ 2W` and `nb·W ≤ r + W`. The counted loops (`pzT`) need `W3_dec_amortised`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts IntMul

/-- **Pass cost bound** (proved in `WP/W9c/PassCost.lean`). -/
def PassTBound : Prop :=
  W3_dec_amortised →
  ∀ (C : ℕ) (Mul : ℕ → ℕ) (k p_in q W zl zr ol w s nb : ℕ),
    1 ≤ W → k ≤ s + 1 → q ≤ s → ol ≤ 2 * W → nb * W ≤ zl + zr + W →
    passT C Mul k p_in q W zl zr ol ((W + 1) * (s + w)) w k (k + 1) (k + 3) nb ≤
      nb * (C * Mul ((W + 1) * (s + w))) +
        (C + 3) * 64 * (nb * ((W + 1) * (s + w + p_in + 2)) + (zl + zr + W) * (s + 5) + 1)

end WP.W9c
