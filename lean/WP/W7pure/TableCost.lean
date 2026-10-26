import WP.W7pure.Headline

/-!
# WP.W7pure.TableCost — `W7_tableCost_sqrt`: table work is `O(√n·log⁸ n)`

`W7_tableCost_sqrt` (Contracts/W7/Schedule.lean:128):
`∃ C N₀, ∀ n ≥ N₀, (W8.hSpec n).precomputeSeriesTableCost ≤ C·(√n + 1)·(log₂ n + 1)^8`.

Proof (with `ℓ = log₂ n + 1`, `N₀ = 0`): the proved headline bound `W7_tableCost_headline`
(CTB:715 `buildQuantizedSpecPaperStop_precomputeSeriesTableCost_le`) gives
`cost ≤ (L+1)·2^(K0 − ⌊K0/2⌋)·2^67·P^6`, and `WP.W7pure.Headline` gives
`L + 1 ≤ 4ℓ`, `2^(K0 − ⌊K0/2⌋) ≤ 8(√n+1)`, `P ≤ 88ℓ`. Hence
`cost ≤ 32·2^67·88^6·(√n+1)·ℓ^7 ≤ C·(√n+1)·ℓ^8` with `C = 32·2^67·88^6` (`tableCostConst`).
-/

namespace WP.W7pure

open TMFw.Contracts IntMul

/-- The constant of `W7_tableCost_sqrt_holds`. -/
def tableCostConst : ℕ := 32 * 2 ^ 67 * 88 ^ 6

/-- Explicit form, valid for every `n` (in fact with `ℓ^7`). -/
theorem tableCost_le (n : ℕ) :
    (IntMulTM.Contracts.W8.hSpec n).precomputeSeriesTableCost ≤
      tableCostConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8 := by
  have hcost := W7_tableCost_headline n
  have hL : IntMulTM.Contracts.W8.hL n + 1 ≤ 4 * (Nat.log2 n + 1) := by
    have h1 := hL_succ_le n
    have h2 := hK0_le n
    omega
  have hS := two_pow_ceil_half_hK0_le n
  have hP : leafPrecision (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n)
      (IntMulTM.Contracts.W8.hK0 n) ≤ 88 * (Nat.log2 n + 1) := by
    have h1 := leafP_le n
    omega
  calc (IntMulTM.Contracts.W8.hSpec n).precomputeSeriesTableCost
      ≤ (IntMulTM.Contracts.W8.hL n + 1) *
          2 ^ (IntMulTM.Contracts.W8.hK0 n - IntMulTM.Contracts.W8.hK0 n / 2) *
          (2 ^ 67 * leafPrecision (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n)
            (IntMulTM.Contracts.W8.hK0 n) ^ 6) := hcost
    _ ≤ (4 * (Nat.log2 n + 1)) * (8 * (Nat.sqrt n + 1)) *
          (2 ^ 67 * (88 * (Nat.log2 n + 1)) ^ 6) :=
        Nat.mul_le_mul (Nat.mul_le_mul hL hS) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 6))
    _ = tableCostConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 7 := by
        unfold tableCostConst
        ring
    _ ≤ tableCostConst * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))

/-- **W7_tableCost_sqrt** (Contracts/W7/Schedule.lean:128), with `C = 32·2^67·88^6`, `N₀ = 0`. -/
theorem W7_tableCost_sqrt_holds : W7_tableCost_sqrt :=
  ⟨tableCostConst, 0, fun n _ => tableCost_le n⟩

#assert_std_axioms tableCost_le W7_tableCost_sqrt_holds

end WP.W7pure
