import Contracts.Machine.W5
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# WP.W5.Bound — the pipeline interface `W5_T3_bound` (pure arithmetic, no machine)

`T3 c0 c1 w0 w = 5·T3(⌈w/3⌉ + c0) + c1·w` above the threshold, constant base below.

**Proof idea** (all in `ℕ`, no real powers).
1. *Grid lemma* `T3_grid`: on the shifted grid `w ≤ 3^k + E` (with `E = 2c0 + 2`, a fixed point of
   `x ↦ ⌈x/3⌉ + c0` up to the offset), `T3 w + B·3^k ≤ A·5^k`. The subtracted `B·3^k` absorbs the
   linear term `c1·w`, because `5·3^k − 3·3^k = 2·3^k`.
2. *Exponent gap* `pow25_le`: `25^m · m² ≤ 676 · 27^m`. This is `log₃ 5 < 3/2` in squared form
   (`5² = 25 < 27 = 3³`), with room for the `log² w` factor.
3. For `3^j ≤ w < 3^(j+1)`: `T3 w ≤ A·5^(j+1)`, `log₂ w < 2(j+1)`, and `4·(w·⌊√w⌋)² ≥ 27^j`;
   squaring gives `T3 w · log₂ w ≤ 2808·A · (w·⌊√w⌋)`.
-/

namespace WP.W5

open TMFw TMFw.Contracts

/-- **Grid lemma.** With `E = 2c0 + 2`, `B = c1·(2c0 + 5)` and `A = T3(2c0 + 3) + B`:
`w ≤ 3^k + E → T3 w + B·3^k ≤ A·5^k`. -/
theorem T3_grid (c0 c1 w0 : ℕ) : ∀ k w : ℕ, w ≤ 3 ^ k + (2 * c0 + 2) →
    T3 c0 c1 w0 w + c1 * (2 * c0 + 5) * 3 ^ k ≤
      (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ k := by
  intro k
  induction k with
  | zero =>
    intro w hw
    simp only [pow_zero, Nat.mul_one] at hw ⊢
    have := T3_mono c0 c1 w0 (show w ≤ 2 * c0 + 3 by omega)
    omega
  | succ k ih =>
    intro w hw
    have hP : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hw3 : w ≤ 3 * 3 ^ k + (2 * c0 + 2) := by
      rw [pow_succ] at hw
      omega
    rw [T3_unfold c0 c1 w0 w]
    split_ifs with h
    · -- recursive case
      have hw' : (w + 2) / 3 + c0 ≤ 3 ^ k + (2 * c0 + 2) := by omega
      have ih' := ih _ hw'
      have hcP : c0 * 1 ≤ c0 * 3 ^ k := Nat.mul_le_mul_left _ hP
      have h1 : c1 * w ≤ c1 * (2 * c0 + 5) * 3 ^ k := by
        calc c1 * w ≤ c1 * (3 * 3 ^ k + (2 * c0 + 2)) := Nat.mul_le_mul_left _ hw3
          _ ≤ c1 * ((2 * c0 + 5) * 3 ^ k) := by
            apply Nat.mul_le_mul_left
            have e : (2 * c0 + 5) * 3 ^ k = 2 * (c0 * 3 ^ k) + 5 * 3 ^ k := by ring
            rw [e]
            omega
          _ = c1 * (2 * c0 + 5) * 3 ^ k := by ring
      have e1 : c1 * (2 * c0 + 5) * 3 ^ (k + 1) = 3 * (c1 * (2 * c0 + 5) * 3 ^ k) := by ring
      have e2 : (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (k + 1) =
          5 * ((T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ k) := by ring
      rw [e1, e2]
      omega
    · -- base case of the recurrence
      have hb := T3_ge_base c0 c1 w0 (2 * c0 + 3)
      have h5 : 1 ≤ 5 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      have h35 : 3 ^ (k + 1) ≤ 5 ^ (k + 1) := Nat.pow_le_pow_left (by norm_num) _
      have hA : T3 c0 c1 w0 (2 * c0 + 3) ≤ T3 c0 c1 w0 (2 * c0 + 3) * 5 ^ (k + 1) :=
        Nat.le_mul_of_pos_right _ h5
      have hB : c1 * (2 * c0 + 5) * 3 ^ (k + 1) ≤ c1 * (2 * c0 + 5) * 5 ^ (k + 1) :=
        Nat.mul_le_mul_left _ h35
      have e : (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (k + 1) =
          T3 c0 c1 w0 (2 * c0 + 3) * 5 ^ (k + 1) + c1 * (2 * c0 + 5) * 5 ^ (k + 1) := by ring
      rw [e]
      omega

/-- **Exponent gap** (`log₃ 5 < 3/2`, squared, with room for `log²`): `25^m·m² ≤ 676·27^m`. -/
theorem pow25_le : ∀ m : ℕ, 25 ^ m * (m * m) ≤ 676 * 27 ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    by_cases hm : m + 1 ≤ 26
    · have h1 : (m + 1) * (m + 1) ≤ 676 := by
        have := Nat.mul_le_mul hm hm
        omega
      have h2 : 25 ^ (m + 1) ≤ 27 ^ (m + 1) := Nat.pow_le_pow_left (by norm_num) _
      calc 25 ^ (m + 1) * ((m + 1) * (m + 1)) ≤ 27 ^ (m + 1) * 676 := Nat.mul_le_mul h2 h1
        _ = 676 * 27 ^ (m + 1) := Nat.mul_comm _ _
    · have h3 : 25 * ((m + 1) * (m + 1)) ≤ 27 * (m * m) := by nlinarith
      calc 25 ^ (m + 1) * ((m + 1) * (m + 1)) = 25 ^ m * (25 * ((m + 1) * (m + 1))) := by ring
        _ ≤ 25 ^ m * (27 * (m * m)) := Nat.mul_le_mul_left _ h3
        _ = 27 * (25 ^ m * (m * m)) := by ring
        _ ≤ 27 * (676 * 27 ^ m) := Nat.mul_le_mul_left _ ih
        _ = 676 * 27 ^ (m + 1) := by ring

/-- Every `w ≥ 1` lies in some `[3^j, 3^(j+1))`. -/
theorem exists_pow3 : ∀ w : ℕ, 1 ≤ w → ∃ j, 3 ^ j ≤ w ∧ w < 3 ^ (j + 1) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h : w < 3
    · exact ⟨0, by simp; omega, by simp; omega⟩
    · obtain ⟨j, h1, h2⟩ := ih (w / 3) (by omega) (by omega)
      refine ⟨j + 1, ?_, ?_⟩
      · rw [pow_succ]
        omega
      · rw [pow_succ]
        omega

/-- **`W5_T3_bound` holds**: `T3(w)·log₂ w ≤ C'·(w·⌊√w⌋)` for `w ≥ 4`, with
`C' = 2808·(T3(2c0 + 3) + c1·(2c0 + 5))`. -/
theorem W5_T3_bound_holds : W5_T3_bound := by
  intro c0 c1 w0
  refine ⟨2808 * (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)), fun w hw => ?_⟩
  obtain ⟨j, hj1, hj2⟩ := exists_pow3 w (by omega)
  have hT : T3 c0 c1 w0 w ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1) :=
    le_trans (Nat.le_add_right _ _) (T3_grid c0 c1 w0 (j + 1) w (by omega))
  have hL : Nat.log2 w ≤ 2 * (j + 1) := by
    have : Nat.log2 w < 2 * (j + 1) := by
      rw [Nat.log2_lt (by omega)]
      calc w < 3 ^ (j + 1) := hj2
        _ ≤ 4 ^ (j + 1) := Nat.pow_le_pow_left (by norm_num) _
        _ = 2 ^ (2 * (j + 1)) := by rw [pow_mul]; norm_num
    omega
  have hs1 : w < (Nat.sqrt w + 1) * (Nat.sqrt w + 1) := Nat.lt_succ_sqrt w
  have hs2 : 2 ≤ Nat.sqrt w := Nat.le_sqrt.2 (by omega)
  have h4s : 3 ^ j ≤ 4 * (Nat.sqrt w * Nat.sqrt w) := by nlinarith
  have h9 : 9 ^ j ≤ w * w := by
    calc 9 ^ j = 3 ^ j * 3 ^ j := by rw [show (9 : ℕ) = 3 * 3 by norm_num, mul_pow]
      _ ≤ w * w := Nat.mul_le_mul hj1 hj1
  have hws : 27 ^ j ≤ 4 * ((w * Nat.sqrt w) * (w * Nat.sqrt w)) := by
    calc 27 ^ j = 3 ^ j * 9 ^ j := by rw [show (27 : ℕ) = 3 * 9 by norm_num, mul_pow]
      _ ≤ (4 * (Nat.sqrt w * Nat.sqrt w)) * (w * w) := Nat.mul_le_mul h4s h9
      _ = 4 * ((w * Nat.sqrt w) * (w * Nat.sqrt w)) := by ring
  have hkey := pow25_le (j + 1)
  have hsq : (5 ^ (j + 1) * (2 * (j + 1))) * (5 ^ (j + 1) * (2 * (j + 1))) ≤
      (2808 * (w * Nat.sqrt w)) * (2808 * (w * Nat.sqrt w)) := by
    have e1 : (5 ^ (j + 1) * (2 * (j + 1))) * (5 ^ (j + 1) * (2 * (j + 1))) =
        4 * (25 ^ (j + 1) * ((j + 1) * (j + 1))) := by
      rw [show (25 : ℕ) = 5 * 5 by norm_num, mul_pow]
      ring
    have e2 : 27 ^ (j + 1) = 27 * 27 ^ j := by ring
    have e3 : (2808 * (w * Nat.sqrt w)) * (2808 * (w * Nat.sqrt w)) =
        7884864 * ((w * Nat.sqrt w) * (w * Nat.sqrt w)) := by ring
    rw [e1, e3]
    rw [e2] at hkey
    omega
  have hle : 5 ^ (j + 1) * (2 * (j + 1)) ≤ 2808 * (w * Nat.sqrt w) :=
    Nat.mul_self_le_mul_self_iff.1 hsq
  calc T3 c0 c1 w0 w * Nat.log2 w
      ≤ ((T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1)) * (2 * (j + 1)) :=
        Nat.mul_le_mul hT hL
    _ = (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * (5 ^ (j + 1) * (2 * (j + 1))) := by
        ring
    _ ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * (2808 * (w * Nat.sqrt w)) :=
        Nat.mul_le_mul_left _ hle
    _ = 2808 * (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * (w * Nat.sqrt w) := by ring

#assert_std_axioms T3_grid pow25_le exists_pow3 W5_T3_bound_holds

end WP.W5
