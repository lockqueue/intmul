import WP.W10.Cost

/-!
# WP.W10.Smoke — numeric sanity check of the W10 constants

W10 has no machine program, so there is nothing to run on the framework harness. Instead this file
evaluates a toy `StageCosts` record that satisfies `StageBounds toy 1` (not proved here, by
inspection: every level multiplies at the maximal width `(L+1)²`, the hardest case for the
`w^{3/2}/log w` rate), with the worst multiplication cost allowed by `MulBound worstM 1`. It
compares `toy.total worstM n` with the proved bound `C·n·log₂ n`,
`C = 2A + A·levelConst A CM = 18` for `A = CM = 1`.
-/

namespace WP.W10.Smoke

open IntMulTM.Contracts.Top

/-- The worst cost allowed by `MulBound · 1`: `⌊w·√w / log₂ w⌋`, and `1` below width 4. -/
def worstM (w : ℕ) : ℕ := if w < 4 then 1 else w * Nat.sqrt w / Nat.log2 w

/-- Toy record: `log₂ log₂ n + 1` levels, each with `n / (L+1)²` multiplications of width
`(L+1)²`, where `L = log₂ n`. -/
def toy : StageCosts where
  input n := n * Nat.log2 n
  tables _ := 0
  root _ := 0
  output _ := 0
  levels n := Nat.log2 (Nat.log2 n) + 1
  levelLin n _ := n * Nat.log2 n / (Nat.log2 (Nat.log2 n) + 1)
  mulCount n _ := n / (Nat.log2 n + 1) ^ 2
  mulWidth n _ := (Nat.log2 n + 1) ^ 2

/-- The constant of `W10_cost_holds` for `A = CM = 1`. -/
def C : ℕ := 2 * 1 + 1 * levelConst 1 1

/-- `(log₂ n, total, total / (n·log₂ n), C)` for `n = 2^j`. -/
def row (j : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let n := 2 ^ j
  (j, toy.total worstM n, toy.total worstM n / (n * Nat.log2 n), C)

#eval [4, 8, 16, 32, 64, 128, 256, 512, 1024].map row

/-- The proved bound holds on `n = 2^4, …, 2^200` and on every `n ∈ [4, 2000]`. -/
def boundHolds : Bool :=
  ((List.range 197).all fun j => toy.total worstM (2 ^ (j + 4)) ≤ C * 2 ^ (j + 4) * (j + 4)) &&
    ((List.range 1997).all fun i => toy.total worstM (i + 4) ≤ C * (i + 4) * Nat.log2 (i + 4))

#guard boundHolds

end WP.W10.Smoke
