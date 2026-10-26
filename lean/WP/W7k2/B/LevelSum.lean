import WP.W7k2.B.LevelCost

/-!
# WP.W7k2.B.LevelSum — the full-budget composition of the per-level costs (pure arithmetic)

Full-budget summation of W7k2 per-level costs: the guarded per-level costs
`stepLvG`, `leafLvG` (verbatim) and `levels_cost_le`, which sums them along the recursion
(`levelSum_le` with `A = 3000·C·(KM+1) + 6`, then the `_min` lemmas).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- Guarded step-level cost (charged only under the invariant `pIn ≤ 2p`). -/
def stepLvG (C KM : ℕ) : ℕ → ℕ → ℕ → ℕ := fun pIn p K =>
  if pIn ≤ 2 * p then stepLvCost C KM p K pIn else 0

/-- Guarded leaf-level cost (charged only under `pIn ≤ 2p` and `Lc ≤ p + K`). -/
def leafLvG (C KM : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ := fun pIn Lc p K =>
  if pIn ≤ 2 * p ∧ Lc ≤ p + K then leafLvCost C KM Lc p K pIn else 0

/-- **Full-budget composition.** -/
theorem levels_cost_le (C KM L p K : ℕ) (hC : 1 ≤ C) (hp : 8 ≤ p) :
    levelSum (stepLvG C KM) (leafLvG C KM) 0 (min L K) p K ≤
      (3000 * (C * (KM + 1)) + 6) *
        ((buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost +
          (tapeFromC 0 L p K).length + 1) := by
  rw [buildQuantizedSpecPaperStop_min L p K (by omega), tapeFromC_min 0 L p K (by omega)]
  refine levelSum_le (3000 * (C * (KM + 1)) + 6) (stepLvG C KM) (leafLvG C KM) ?_ ?_
    0 (min L K) p K hp
  · intro pIn p' K' hp' hK'
    simp only [stepLvG]
    split_ifs with hpIn
    · have h := stepLv_le C KM p' K' pIn hC hp' hK' hpIn
      have n1 := Nat.zero_le (C * KM * (preSegC pIn p' K').length)
      have n2 := Nat.zero_le (C * (preSegC pIn p' K').length)
      have n3 := Nat.zero_le (C * KM * (postSegC p' K').length)
      have n4 := Nat.zero_le (C * (postSegC p' K').length)
      have n5 := Nat.zero_le (precomputeStepSeriesTableBitCost p' K' (2 ^ (K' / 2)) (2 ^ (K' - K' / 2)))
      have n6 := Nat.zero_le (postSegC p' K').length
      linarith
    · exact Nat.zero_le _
  · intro pIn Lc p' K' hp'
    simp only [leafLvG]
    split_ifs with hcond
    · have h := leafLv_le C KM Lc p' K' pIn hC hp' hcond.1 hcond.2
      exact le_trans h (Nat.mul_le_mul_right _ (by omega))
    · exact Nat.zero_le _

#assert_std_axioms levels_cost_le

end WP.W7k2
