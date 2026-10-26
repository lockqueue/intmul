import WP.W7k2.B.StepCost

/-!
# WP.W7k2.B.LevelCost — per-level cost bounds, with the stop test and the leaf (pure arithmetic)

Per-level cost lemmas for W7k2; the three definitions are verbatim upper
bounds of the builder's composed machine costs.

* `stopCost_le_gen`: the stop test costs at most `40·(KM+1)·C·Q⁴` for any `Q ≥ K+1, 2p+3`.
* `stepLv_le`: a step level costs at most `3000·C·(KM+1)·stepBudget + 6·|preSegC|`.
* `leafLv_le`: a leaf level costs at most `3000·C·(KM+1)·(leafBudget + |leafSegC| + 1)`.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open IntMul TMFw TMFw.Contracts

/-- Stop test of a level (`2^K` on y0, `4p²` on y1), the compare, the two drops. -/
def stopCost (C KM p K : ℕ) : ℕ :=
  (2 + C * (K + bitLen K + 1)) +
  (2 * (C * (bitLen p + 1)) + 2 * (C * (bitLen p + 1)) + (C * (KM * (bitLen p + 1) ^ 2) + C) + 5) +
  C * (1 + 1) + C * (1 + 1) +
  (C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) + 1) +
  (C * (bitLen (4 * p * p) + 1) + C * (bitLen (2 ^ K) + 1))

/-- A step level: two zero tests, the stop test, the step part (with `Lc` bounded by `p + K`), the
later move of its pre segment at the leaf (`3·|preSegC|`), the recursive call. -/
def stepLvCost (C KM p K pIn : ℕ) : ℕ :=
  2 * C + 6 + stopCost C KM p K + stepCostE C KM p K pIn (p + K) + 3 * (preSegC pIn p K).length

/-- A leaf level (the stop test is charged only when `K ≠ 0`). -/
def leafLvCost (C KM Lc p K pIn : ℕ) : ℕ :=
  let Qb := bitLen (2 * p + K + 8) + 5
  let Qk := 2 * p + 2 * K + 40
  2 * C + 4 + (if K = 0 then 0 else stopCost C KM p K) +
  (8 * (C * Qb) + 9 + (K * (2 ^ K * (C * Qk ^ 4 + 2 * (C * Qk) + 1) + 10 * (C * Qk) + 4 +
    2 * (C * Qb) + 1) + 2 * (C * Qb) + 1 + (1 + fieldsCost C [p, K, 2 * p + K + 8, pIn] +
    (1 + C * (bitLen (2 * p + K + 8) + 1))))) + 2 +
  (C * (bitLen Lc + 1) + C * (bitLen p + 1) + C * (bitLen K + 1) + C * (bitLen pIn + 1))

/-! ## The stop test -/

theorem bitLen_four_mul_sq_le (p : ℕ) : bitLen (4 * p * p) ≤ 2 * p + 3 := by
  have h1 := bitLen_mul_le (4 * p) p
  have h2 := bitLen_mul_le 4 p
  have h3 : bitLen 4 = 3 := by
    have h := bitLen_two_pow 2
    norm_num at h
    exact h
  have h4 := bitLen_le_self p
  omega

/-- The stop test costs at most `40·(KM+1)·C·Q⁴` for any `Q` with `K + 1 ≤ Q` and `2p + 3 ≤ Q`. -/
theorem stopCost_le_gen (C KM p K Q : ℕ) (hC : 1 ≤ C) (hQK : K + 1 ≤ Q) (hQp : 2 * p + 3 ≤ Q) :
    stopCost C KM p K ≤ 40 * ((KM + 1) * (C * Q ^ 4)) := by
  unfold stopCost
  have hQpos : 0 < Q := by omega
  have hbK : bitLen K ≤ K := bitLen_le_self K
  have hbp : bitLen p ≤ p := bitLen_le_self p
  have hb2K : bitLen (2 ^ K) = K + 1 := bitLen_two_pow K
  have hb4 := bitLen_four_mul_sq_le p
  have hQ4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQpos
  have hX1 : 1 ≤ C * Q ^ 4 := by simpa using Nat.mul_le_mul hC hQ4
  have hCX : C ≤ C * Q ^ 4 := by
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Q ^ 4 := Nat.mul_le_mul_left C hQ4
  have hCQ : C * Q ≤ C * Q ^ 4 := Nat.mul_le_mul_left C (Nat.le_self_pow (by norm_num) Q)
  have f1 : C * (K + bitLen K + 1) ≤ 2 * (C * Q) := by
    calc C * (K + bitLen K + 1) ≤ C * (2 * Q) := Nat.mul_le_mul_left C (by omega)
      _ = 2 * (C * Q) := by ring
  have f2 : C * (bitLen p + 1) ≤ C * Q := Nat.mul_le_mul_left C (by omega)
  have f3 : C * (KM * (bitLen p + 1) ^ 2) ≤ KM * (C * Q ^ 4) := by
    have hq : (bitLen p + 1) ^ 2 ≤ Q ^ 4 :=
      le_trans (Nat.pow_le_pow_left (by omega : bitLen p + 1 ≤ Q) 2)
        (Nat.pow_le_pow_right hQpos (by norm_num))
    calc C * (KM * (bitLen p + 1) ^ 2) = KM * (C * (bitLen p + 1) ^ 2) := by ring
      _ ≤ KM * (C * Q ^ 4) := Nat.mul_le_mul_left KM (Nat.mul_le_mul_left C hq)
  have f4 : C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) ≤ 2 * (C * Q) + C := by
    calc C * (bitLen (2 ^ K) + bitLen (4 * p * p) + 1) ≤ C * (2 * Q + 1) :=
          Nat.mul_le_mul_left C (by omega)
      _ = 2 * (C * Q) + C := by ring
  have f5 : C * (bitLen (4 * p * p) + 1) ≤ C * Q + C := by
    calc C * (bitLen (4 * p * p) + 1) ≤ C * (Q + 1) := Nat.mul_le_mul_left C (by omega)
      _ = C * Q + C := by ring
  have f6 : C * (bitLen (2 ^ K) + 1) ≤ C * Q + C := by
    calc C * (bitLen (2 ^ K) + 1) ≤ C * (Q + 1) := Nat.mul_le_mul_left C (by omega)
      _ = C * Q + C := by ring
  have n0 : 0 ≤ C * Q ^ 4 := Nat.zero_le _
  have n1 : 0 ≤ KM * (C * Q ^ 4) := Nat.zero_le _
  linarith

/-! ## A step level -/

/-- **Step level.** -/
theorem stepLv_le (C KM p K pIn : ℕ) (hC : 1 ≤ C) (hp : 8 ≤ p) (hK : ¬ 2 ^ K ≤ 4 * p * p)
    (hpIn : pIn ≤ 2 * p) :
    stepLvCost C KM p K pIn ≤
      3000 * (C * (KM + 1)) * precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) +
        6 * (preSegC pIn p K).length := by
  have hstep := stepCostE_le C KM p K pIn (p + K) hC hp hK le_rfl hpIn
  have hbud := step_budget_ge p K hp hK
  have hpw : pWork p K = p + K + 6 := rfl
  have hstop := stopCost_le_gen C KM p K (128 * (pWork p K + 1)) hC (by omega) (by omega)
  have hfac : 1 ≤ 2 ^ (K / 2) * (4 * pChild p K + 1) + 4 * 2 ^ (K - K / 2) := by
    have := Nat.one_le_two_pow (n := K - K / 2)
    omega
  unfold stepLvCost
  set S := precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) with hS
  set L := (preSegC pIn p K).length with hL
  set Q := 128 * (pWork p K + 1) with hQ
  set X := C * Q ^ 4 with hX
  have hQS : Q ^ 4 ≤ S := by
    calc Q ^ 4 = 1 * Q ^ 4 := (one_mul _).symm
      _ ≤ (2 ^ (K / 2) * (4 * pChild p K + 1) + 4 * 2 ^ (K - K / 2)) * Q ^ 4 :=
          Nat.mul_le_mul_right _ hfac
      _ ≤ S := hbud
  have hXS : (KM + 1) * X ≤ C * (KM + 1) * S := by
    calc (KM + 1) * X = C * (KM + 1) * Q ^ 4 := by rw [hX]; ring
      _ ≤ C * (KM + 1) * S := Nat.mul_le_mul_left _ hQS
  have hQpos : 0 < Q := by omega
  have hQ4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQpos
  have hX1 : 1 ≤ X := by rw [hX]; simpa using Nat.mul_le_mul hC hQ4
  have hCX : C ≤ X := by
    rw [hX]; calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Q ^ 4 := Nat.mul_le_mul_left C hQ4
  have n1 : 0 ≤ KM * X := Nat.zero_le _
  have n2 : 0 ≤ C * KM * S := Nat.zero_le _
  have n3 : 0 ≤ C * S := Nat.zero_le _
  linarith

/-! ## The leaf level -/

/-- The leaf segment lists the header field `2p + K + 8` in binary. -/
theorem leafSegC_length_ge (pIn p K : ℕ) :
    bitLen (2 * p + K + 8) ≤ (leafSegC pIn p K).length := by
  unfold leafSegC leafSegE
  simp only [List.length_cons, List.length_append, W7.header, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, W7.field, length_natSyms, List.length_singleton,
    List.length_nil, List.append_nil]
  omega

/-- **Leaf level.** -/
theorem leafLv_le (C KM Lc p K pIn : ℕ) (hC : 1 ≤ C) (hp : 8 ≤ p) (hpIn : pIn ≤ 2 * p)
    (hLc : Lc ≤ p + K) :
    leafLvCost C KM Lc p K pIn ≤
      3000 * (C * (KM + 1)) * (precomputeLeafSeriesTableBitCost p (2 ^ K) +
        (leafSegC pIn p K).length + 1) := by
  have hlen := leafSegC_length_ge pIn p K
  have hbp : bitLen p ≤ bitLen (2 * p + K + 8) := bitLen_mono (by omega)
  have hbK : bitLen K ≤ bitLen (2 * p + K + 8) := bitLen_mono (by omega)
  have hbpIn : bitLen pIn ≤ bitLen (2 * p + K + 8) := bitLen_mono (by omega)
  have hbLc : bitLen Lc ≤ bitLen (2 * p + K + 8) := bitLen_mono (by omega)
  have hbq : bitLen (2 * p + K + 8) ≤ 2 * p + K + 8 := bitLen_le_self _
  have hF := fieldsCost_le C (bitLen (2 * p + K + 8)) [p, K, 2 * p + K + 8, pIn]
    (by
      intro v hv
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h <;> rw [h] <;>
        first | exact hbp | exact hbK | exact hbpIn)
  simp only [List.length_cons, List.length_nil] at hF
  have hbl : ∀ v, bitLen v ≤ bitLen (2 * p + K + 8) →
      C * (bitLen v + 1) ≤ C * bitLen (2 * p + K + 8) + C := fun v hv => by
    calc C * (bitLen v + 1) ≤ C * (bitLen (2 * p + K + 8) + 1) := Nat.mul_le_mul_left C (by omega)
      _ = C * bitLen (2 * p + K + 8) + C := by ring
  have e1 := hbl Lc hbLc
  have e2 := hbl p hbp
  have e3 := hbl K hbK
  have e4 := hbl pIn hbpIn
  have hCL : C * bitLen (2 * p + K + 8) ≤ C * (leafSegC pIn p K).length :=
    Nat.mul_le_mul_left C hlen
  have hstop := stopCost_le_gen C KM p K (2 * p + 2 * K + 40) hC (by omega) (by omega)
  have hLBge : 1 ≤ K → K * 2 ^ K * (2 * p + 2 * K + 40) ^ 4 ≤
      precomputeLeafSeriesTableBitCost p (2 ^ K) := fun hK1 => leaf_budget_ge p K hK1
  unfold leafLvCost
  dsimp only
  set L := (leafSegC pIn p K).length with hL
  set LB := precomputeLeafSeriesTableBitCost p (2 ^ K) with hLB
  have n3 : 0 ≤ C * KM * L := Nat.zero_le _
  have n4 : 0 ≤ C * L := Nat.zero_le _
  have n5 : 0 ≤ C * KM := Nat.zero_le _
  have n6 : 0 ≤ C * KM * LB := Nat.zero_le _
  have n7 : 0 ≤ C * LB := Nat.zero_le _
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- K = 0: everything is `O(C · |leafSegC|)`
    subst hK0
    rw [if_pos rfl]
    linarith
  · -- K ≥ 1: `leaf_budget_ge`
    rw [if_neg (by omega)]
    have hLB1 := hLBge hKpos
    set Qk := 2 * p + 2 * K + 40 with hQk
    set Y := C * Qk ^ 4 with hY
    have hQkpos : 0 < Qk := by omega
    have hQ4 : 1 ≤ Qk ^ 4 := Nat.one_le_pow _ _ hQkpos
    have hY1 : 1 ≤ Y := by rw [hY]; simpa using Nat.mul_le_mul hC hQ4
    have hCY : C ≤ Y := by
      rw [hY]; calc C = C * 1 := (mul_one C).symm
        _ ≤ C * Qk ^ 4 := Nat.mul_le_mul_left C hQ4
    have hCQkY : C * Qk ≤ Y := by rw [hY]; exact Nat.mul_le_mul_left C (Nat.le_self_pow (by norm_num) Qk)
    have hCbqY : C * bitLen (2 * p + K + 8) ≤ Y :=
      le_trans (Nat.mul_le_mul_left C (by omega)) hCQkY
    have hCQbY : C * (bitLen (2 * p + K + 8) + 5) ≤ Y :=
      le_trans (Nat.mul_le_mul_left C (by omega)) hCQkY
    have hK2K : K ≤ K * 2 ^ K := by
      calc K = K * 1 := (mul_one K).symm
        _ ≤ K * 2 ^ K := Nat.mul_le_mul_left K Nat.one_le_two_pow
    have hE1 : 1 ≤ K * 2 ^ K := le_trans hKpos hK2K
    have hYE : Y ≤ K * 2 ^ K * Y := by
      calc Y = 1 * Y := (one_mul Y).symm
        _ ≤ K * 2 ^ K * Y := Nat.mul_le_mul_right Y hE1
    have hKY : K * Y ≤ K * 2 ^ K * Y := Nat.mul_le_mul_right Y hK2K
    have g1 : K * 2 ^ K * (C * Qk) ≤ K * 2 ^ K * Y := Nat.mul_le_mul_left _ hCQkY
    have g2 : K * 2 ^ K ≤ K * 2 ^ K * Y := by
      calc K * 2 ^ K = K * 2 ^ K * 1 := (mul_one _).symm
        _ ≤ K * 2 ^ K * Y := Nat.mul_le_mul_left _ hY1
    have g3 : K * (C * Qk) ≤ K * 2 ^ K * Y := le_trans (Nat.mul_le_mul_left K hCQkY) hKY
    have g4 : K ≤ K * 2 ^ K * Y := le_trans hK2K g2
    have g5 : K * (C * (bitLen (2 * p + K + 8) + 5)) ≤ K * 2 ^ K * Y :=
      le_trans (Nat.mul_le_mul_left K hCQbY) hKY
    have hKMY : KM * Y ≤ KM * (K * 2 ^ K * Y) := Nat.mul_le_mul_left KM hYE
    have hlinkL : (KM + 1) * (K * 2 ^ K * Y) ≤ C * (KM + 1) * LB := by
      have h := Nat.mul_le_mul_left (C * (KM + 1)) hLB1
      calc (KM + 1) * (K * 2 ^ K * Y) = C * (KM + 1) * (K * 2 ^ K * Qk ^ 4) := by rw [hY]; ring
        _ ≤ C * (KM + 1) * LB := h
    have n1 : 0 ≤ K * 2 ^ K * Y := Nat.zero_le _
    have n2 : 0 ≤ KM * (K * 2 ^ K * Y) := Nat.zero_le _
    linarith

#assert_std_axioms bitLen_four_mul_sq_le stopCost_le_gen stepLv_le leafSegC_length_ge leafLv_le

end WP.W7k2
