import SubNLogN.Math.Common.Grid
import SubNLogN.Math.Common.DFT

/-!
# Common: the middle-transform contract (Definition 4.5 (`def:middle-contract`))

Consumed by the bridge precision theorem (Theorem 4.7 (`thm:bridge-precision`)) and produced by the Walsh middle
(Corollary 6.6 (`cor:walsh-middle`): `E_mid = 12ℓ`, `δ_mid = 0`).

Value-level encoding of Definition 4.5. The input tensor is indexed by digit tuples `Idx t` (axis order
`(j_1,…,j_d)`); the output by frequency digit tuples `(u_1,…,u_d)`. The tape-layout clauses
("natural axis order, last axis contiguous", "natural frequency order") are not value statements:
in natural order with the last axis contiguous, the tape position of a digit tuple is
`encFreq t`; those clauses belong to the tape-level contracts (`SubNLogN.Machine`).
-/

namespace SubNLogN.Math.Common

/-- Definition 4.5 (`def:middle-contract`): `run` is a *middle transform at precision
`q = P + 2` with constant `E_mid` and widening `δ_mid`* for the shape `t` (`R = totalLen t`,
`k = lg R`). For every complete tensor `U` with entries on the `q`-grid and `‖U‖_∞ ≤ 1/8`, the
output `Ŷ = run U` lies on the `q`-grid, has component width at most `q + 2 + δ_mid`, and satisfies
`‖Ŷ - F_t U‖_∞ ≤ E_mid · 2^{-q}`; moreover `0 ≤ δ_mid ≤ P` and `E_mid ≤ 16 R (k+1)`. -/
structure IsMiddleTransform {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (Emid : ℝ) (δmid : ℕ)
    (run : (Idx t → ℂ) → (Idx t → ℂ)) : Prop where
  /-- `δ_mid ≤ P` (Definition 4.5 (`def:middle-contract`)). -/
  δmid_le : δmid ≤ P
  /-- `E_mid ≤ 16 R (k+1)` with `k = lg R` (Definition 4.5 (`def:middle-contract`)). -/
  Emid_le : Emid ≤ 16 * (totalLen t : ℝ) * ((lg (totalLen t) : ℝ) + 1)
  /-- The output lies on the `q`-grid (Definition 4.5 (`def:middle-contract`)). -/
  out_onGrid : ∀ U : Idx t → ℂ, (∀ j, OnGrid (P + 2) (U j)) → ‖U‖ ≤ 1 / 8 →
    ∀ u, OnGrid (P + 2) (run U u)
  /-- The output has component width at most `q + 2 + δ_mid` (Definition 4.5 (`def:middle-contract`)). -/
  out_width : ∀ U : Idx t → ℂ, (∀ j, OnGrid (P + 2) (U j)) → ‖U‖ ≤ 1 / 8 →
    ∀ u, FitsWidth (P + 2) (P + 2 + 2 + δmid) (run U u)
  /-- The error bound `‖Ŷ - F_t U‖_∞ ≤ E_mid · v`, `v = 2^{-q}` (Definition 4.5 (`def:middle-contract`)). -/
  err : ∀ U : Idx t → ℂ, (∀ j, OnGrid (P + 2) (U j)) → ‖U‖ ≤ 1 / 8 →
    ‖run U - dftTensor t U‖ ≤ Emid * gridUnit (P + 2)

end SubNLogN.Math.Common
