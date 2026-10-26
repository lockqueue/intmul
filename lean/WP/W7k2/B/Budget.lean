import WP.W7k2.Canon.Tape

/-!
# WP.W7k2.B.Budget — the table builder's budget relation (pure arithmetic)

Pure-arithmetic budget relations for the W7k2 table builder:

1. `buildQuantizedSpecPaperStop_min`, `tapeFromC_min`: fuel beyond `K` is irrelevant (a step level has
   `K ≥ 2`, its child has `K - K/2 ≤ K - 1`, and at `K ≤ 1` the stop test fires once `1 ≤ p`).
2. `levelSum`, `levelSum_le`: a cost defined by the recursion of `tapeFromC` is bounded by the
   snapshot budget `precomputeSeriesTableCost` plus the tape length, given per-level bounds.
3. `step_budget_ge`, `leaf_budget_ge`: per-level domination of the machine's cost unit
   (`Q⁴ · #kernel calls`) by the snapshot's per-level budget (CTB:421-438).
-/

namespace WP.W7k2

open IntMul

/-! ## Unfolding lemmas -/

theorem buildQuantizedSpecPaperStop_succ (L p K : ℕ) :
    buildQuantizedSpecPaperStop (L + 1) p K =
      if 2 ^ K ≤ 4 * p * p then .base p (2 ^ K)
      else quantizedBoxGaussianStepSpec p K
        (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2)) := rfl

theorem tapeFromC_succ (pIn L p K : ℕ) :
    tapeFromC pIn (L + 1) p K =
      if 2 ^ K ≤ 4 * p * p then leafSegC pIn p K
      else preSegC pIn p K ++ tapeFromC (2 * pChild p K) L (pChild p K) (K - K / 2) ++
        postSegC p K := rfl

theorem le_pChild (p K : ℕ) : p ≤ pChild p K := by unfold pChild pWork; omega

/-- At `K ≤ 1` the stop test fires (for `1 ≤ p`). -/
theorem stop_of_le_one {p K : ℕ} (hp : 1 ≤ p) (hK : K ≤ 1) : 2 ^ K ≤ 4 * p * p := by
  have h1 : 2 ^ K ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hK
  have h2 : 4 ≤ 4 * p * p := by nlinarith
  have h3 : (2 : ℕ) ^ 1 = 2 := rfl
  omega

/-- A node that does not stop has `K ≥ 2`. -/
theorem two_le_of_not_stop {p K : ℕ} (hp : 1 ≤ p) (hstop : ¬ 2 ^ K ≤ 4 * p * p) : 2 ≤ K := by
  by_contra h
  exact hstop (stop_of_le_one hp (by omega))

/-! ## (1), (2): fuel beyond `K` is irrelevant -/

theorem build_fuel_irrel (K : ℕ) : ∀ (L1 L2 p : ℕ), 1 ≤ p → K ≤ L1 → K ≤ L2 →
    buildQuantizedSpecPaperStop L1 p K = buildQuantizedSpecPaperStop L2 p K := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
  intro L1 L2 p hp h1 h2
  by_cases hstop : 2 ^ K ≤ 4 * p * p
  · have e : ∀ L, buildQuantizedSpecPaperStop L p K = .base p (2 ^ K) := by
      intro L
      cases L with
      | zero => rfl
      | succ L => rw [buildQuantizedSpecPaperStop_succ, if_pos hstop]
    rw [e L1, e L2]
  · have hK2 := two_le_of_not_stop hp hstop
    obtain ⟨L1', rfl⟩ : ∃ L1', L1 = L1' + 1 := ⟨L1 - 1, by omega⟩
    obtain ⟨L2', rfl⟩ : ∃ L2', L2 = L2' + 1 := ⟨L2 - 1, by omega⟩
    rw [buildQuantizedSpecPaperStop_succ, buildQuantizedSpecPaperStop_succ]
    simp only [if_neg hstop]
    rw [ih (K - K / 2) (by omega) L1' L2' (pChild p K) (le_trans hp (le_pChild p K))
      (by omega) (by omega)]

/-- **(1)** Fuel beyond `K` is irrelevant. -/
theorem buildQuantizedSpecPaperStop_min (L p K : ℕ) (hp : 1 ≤ p) :
    buildQuantizedSpecPaperStop L p K = buildQuantizedSpecPaperStop (min L K) p K := by
  rcases le_total L K with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    exact build_fuel_irrel K L K p hp h le_rfl

theorem tapeFromC_fuel_irrel (K : ℕ) : ∀ (pIn L1 L2 p : ℕ), 1 ≤ p → K ≤ L1 → K ≤ L2 →
    tapeFromC pIn L1 p K = tapeFromC pIn L2 p K := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
  intro pIn L1 L2 p hp h1 h2
  by_cases hstop : 2 ^ K ≤ 4 * p * p
  · have e : ∀ L, tapeFromC pIn L p K = leafSegC pIn p K := by
      intro L
      cases L with
      | zero => rfl
      | succ L => rw [tapeFromC_succ, if_pos hstop]
    rw [e L1, e L2]
  · have hK2 := two_le_of_not_stop hp hstop
    obtain ⟨L1', rfl⟩ : ∃ L1', L1 = L1' + 1 := ⟨L1 - 1, by omega⟩
    obtain ⟨L2', rfl⟩ : ∃ L2', L2 = L2' + 1 := ⟨L2 - 1, by omega⟩
    rw [tapeFromC_succ, tapeFromC_succ]
    simp only [if_neg hstop]
    rw [ih (K - K / 2) (by omega) (2 * pChild p K) L1' L2' (pChild p K)
      (le_trans hp (le_pChild p K)) (by omega) (by omega)]

/-- **(2)** The same for the canonical tape. -/
theorem tapeFromC_min (pIn L p K : ℕ) (hp : 1 ≤ p) :
    tapeFromC pIn L p K = tapeFromC pIn (min L K) p K := by
  rcases le_total L K with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    exact tapeFromC_fuel_irrel K pIn L K p hp h le_rfl

/-! ## (3): generic level sum -/

/-- A cost defined by the recursion of `tapeFromC`: `fs` at step levels, `fl` at the leaf. -/
def levelSum (fs : ℕ → ℕ → ℕ → ℕ) (fl : ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | pIn, 0, p, K => fl pIn 0 p K
  | pIn, L + 1, p, K =>
    if 2 ^ K ≤ 4 * p * p then fl pIn (L + 1) p K
    else fs pIn p K + levelSum fs fl (2 * pChild p K) L (pChild p K) (K - K / 2)

theorem levelSum_zero (fs : ℕ → ℕ → ℕ → ℕ) (fl : ℕ → ℕ → ℕ → ℕ → ℕ) (pIn p K : ℕ) :
    levelSum fs fl pIn 0 p K = fl pIn 0 p K := rfl

theorem levelSum_succ (fs : ℕ → ℕ → ℕ → ℕ) (fl : ℕ → ℕ → ℕ → ℕ → ℕ) (pIn L p K : ℕ) :
    levelSum fs fl pIn (L + 1) p K =
      if 2 ^ K ≤ 4 * p * p then fl pIn (L + 1) p K
      else fs pIn p K + levelSum fs fl (2 * pChild p K) L (pChild p K) (K - K / 2) := rfl

/-- **(3)** Per-level bounds sum to the snapshot budget plus the tape length. -/
theorem levelSum_le (A : ℕ) (fs : ℕ → ℕ → ℕ → ℕ) (fl : ℕ → ℕ → ℕ → ℕ → ℕ)
    (hs : ∀ pIn p K, 8 ≤ p → ¬ 2 ^ K ≤ 4 * p * p →
      fs pIn p K ≤ A * (precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) +
        (preSegC pIn p K).length + (postSegC p K).length))
    (hl : ∀ pIn Lc p K, 8 ≤ p →
      fl pIn Lc p K ≤ A * (precomputeLeafSeriesTableBitCost p (2 ^ K) + (leafSegC pIn p K).length + 1)) :
    ∀ pIn L p K, 8 ≤ p →
      levelSum fs fl pIn L p K ≤
        A * ((buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost +
          (tapeFromC pIn L p K).length + 1) := by
  intro pIn L
  induction L generalizing pIn with
  | zero =>
    intro p K hp
    exact hl pIn 0 p K hp
  | succ L ih =>
    intro p K hp
    rw [levelSum_succ, buildQuantizedSpecPaperStop_succ, tapeFromC_succ]
    by_cases hstop : 2 ^ K ≤ 4 * p * p
    · simp only [if_pos hstop]
      exact hl pIn (L + 1) p K hp
    · simp only [if_neg hstop]
      have h1 := hs pIn p K hp hstop
      have h2 := ih (2 * pChild p K) (pChild p K) (K - K / 2) (le_trans hp (le_pChild p K))
      have e1 : (quantizedBoxGaussianStepSpec p K
            (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2))).precomputeSeriesTableCost =
          precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) +
            (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2)).precomputeSeriesTableCost := rfl
      rw [e1, List.length_append, List.length_append]
      calc fs pIn p K + levelSum fs fl (2 * pChild p K) L (pChild p K) (K - K / 2)
          ≤ A * (precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) +
              (preSegC pIn p K).length + (postSegC p K).length) +
            A * ((buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2)).precomputeSeriesTableCost +
              (tapeFromC (2 * pChild p K) L (pChild p K) (K - K / 2)).length + 1) :=
            Nat.add_le_add h1 h2
        _ = A * (precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) +
              (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2)).precomputeSeriesTableCost +
              ((preSegC pIn p K).length +
                (tapeFromC (2 * pChild p K) L (pChild p K) (K - K / 2)).length +
                (postSegC p K).length) + 1) := by ring

/-! ## (4): per-level budget domination -/

set_option linter.unusedVariables false in
/-- **(4a)** Step level: `(t1 (4p′+1) + 4r) · (128 (pWork+1))⁴ ≤ precomputeStepSeriesTableBitCost`.
(`hp`, `hK` are part of the agreed signature; the inequality holds without them.) -/
theorem step_budget_ge (p K : ℕ) (hp : 8 ≤ p) (hK : ¬ 2 ^ K ≤ 4 * p * p) :
    (2 ^ (K / 2) * (4 * pChild p K + 1) + 4 * 2 ^ (K - K / 2)) * (128 * (pWork p K + 1)) ^ 4 ≤
      precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) := by
  unfold precomputeStepSeriesTableBitCost
  dsimp only
  refine Nat.mul_le_mul le_rfl ?_
  have hM : 128 * (pWork p K + 1) ≤
      1050 * (pWork p K + 2 * pChild p K + Nat.log2 (2 ^ (K / 2)) +
        Nat.log2 (2 * 2 ^ (K - K / 2)) + 21) := by omega
  calc (128 * (pWork p K + 1)) ^ 4
      ≤ (1050 * (pWork p K + 2 * pChild p K + Nat.log2 (2 ^ (K / 2)) +
          Nat.log2 (2 * 2 ^ (K - K / 2)) + 21)) ^ 4 := Nat.pow_le_pow_left hM 4
    _ ≤ 18000 * (1050 * (pWork p K + 2 * pChild p K + Nat.log2 (2 ^ (K / 2)) +
          Nat.log2 (2 * 2 ^ (K - K / 2)) + 21)) ^ 4 :=
        le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)
    _ ≤ _ := Nat.le_add_right _ _

set_option linter.unusedVariables false in
/-- **(4b)** Leaf: `K · 2^K · (2p + 2K + 40)⁴ ≤ precomputeLeafSeriesTableBitCost p (2^K)`.
(`hK` is part of the agreed signature; the inequality holds without it.) -/
theorem leaf_budget_ge (p K : ℕ) (hK : 1 ≤ K) :
    K * 2 ^ K * (2 * p + 2 * K + 40) ^ 4 ≤ precomputeLeafSeriesTableBitCost p (2 ^ K) := by
  unfold precomputeLeafSeriesTableBitCost
  dsimp only
  rw [nat_log2_two_pow]
  refine Nat.mul_le_mul le_rfl ?_
  calc (2 * p + 2 * K + 40) ^ 4 ≤ 18000 * (2 * p + 2 * K + 40) ^ 4 :=
        le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)
    _ ≤ _ := Nat.le_add_right _ _

#assert_std_axioms buildQuantizedSpecPaperStop_succ tapeFromC_succ le_pChild stop_of_le_one
  two_le_of_not_stop build_fuel_irrel buildQuantizedSpecPaperStop_min tapeFromC_fuel_irrel
  tapeFromC_min levelSum_zero levelSum_succ levelSum_le step_budget_ge leaf_budget_ge

end WP.W7k2
