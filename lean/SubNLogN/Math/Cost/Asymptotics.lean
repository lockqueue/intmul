import SubNLogN.Math.Cost.AsymSizes
import SubNLogN.Math.Cost.AsymBands
import SubNLogN.Math.Cost.AsymGrowth

/-!
# Cost: Lemma 7.1 (uniform root family) as eventual statements

Paper: Lemma 7.1 (`lem:root-family`, Section 7.1 (`sec:main-alg`)), with the uses in
Section 7.3 (`sec:main-tables`), eq. (`eq:setup`), Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`) and Remark A.12 (`rem:walsh-delta`). The statements are split into three files (grouping
the row-independent, band, and asymptotic growth clauses of Lemma 7.1):
* `AsymSizes.lean`: row-independent sizes (`k → ∞`, `b ≤ 2k`, `k ≤ b`, `b/k → 1`, `P/k → 20`,
  `16k ≤ q ≤ 32k`, `RP = Θ(n)`, `P = Θ(k) = Θ(lg n)`) and `paper_famFacts`;
* `AsymBands.lean`: `½k^ε ≤ d ≤ k^ε`, `d → ∞`, `ℓ ≥ 2`, the bands eq. (`eq:bands`), `K = Θ(P^{εc})`;
* `AsymGrowth.lean`: `Θ`/`o` forms, `K/log P → ∞`, `r/P^j → ∞`, `(R/r)/P^j → ∞`, `R/r ≥ r/2`,
  guard and setup bounds.
The `k`-level versions of the row-dependent facts (used for any root family, e.g. the machine's W8
family) are in `AsymK.lean`.
-/
