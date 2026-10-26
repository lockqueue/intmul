import WP.W0m.Sched
import WP.W10.Cost

/-!
# WP.Top.CostArith — arithmetic for the cost glue

* `succ_sq_le_two_pow`: `(k+1)² ≤ 2^(k+2)`.
* `sq_bitLen_le`: `(bitLen m + 1)² ≤ 8m` for `m ≥ 1`. This makes the input stage's
  `C·(Λ+1)²` term linear.
* `sqrt_polylog_le`: `(√n + 1)·(log₂ n + 1)^8 ≤ 2^42·n·log₂ n` for `n ≥ 2`. This absorbs W7's
  `O(√n·polylog n)` table and tape bounds.
* `poly_le`: `α·(√n+1)(log₂ n+1)^8 + β·n + γ ≤ (α·2^42 + β + γ)·n·log₂ n` for `n ≥ 2`.
* `nlogn_mono`, `log2_pos`.
-/

namespace WP.Top

open TMFw.Contracts

theorem succ_sq_le_two_pow (k : ℕ) : (k + 1) * (k + 1) ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : k < 2 ^ k := Nat.lt_two_pow_self
    have e1 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
    have e2 : 2 ^ (k + 1 + 2) = 8 * 2 ^ k := by rw [pow_add, pow_add]; ring
    have e3 : (k + 1 + 1) * (k + 1 + 1) = (k + 1) * (k + 1) + 2 * k + 3 := by ring
    rw [e2, e3]
    rw [e1] at ih
    omega

/-- `(bitLen m + 1)² ≤ 8m` for `m ≥ 1`. -/
theorem sq_bitLen_le (m : ℕ) (hm : 1 ≤ m) : (bitLen m + 1) * (bitLen m + 1) ≤ 8 * m := by
  rw [WP.W0m.bitLen_eq_size]
  have hs : 1 ≤ Nat.size m := by
    rw [← WP.W0m.bitLen_eq_size]
    exact WP.W0m.bitLen_pos (by omega)
  have h2 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.mp (by omega)
  have h3 := succ_sq_le_two_pow (Nat.size m)
  have e : 2 ^ (Nat.size m + 2) = 8 * 2 ^ (Nat.size m - 1) := by
    obtain ⟨j, hj⟩ : ∃ j, Nat.size m = j + 1 := ⟨Nat.size m - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, pow_add, pow_add]
    ring
  omega

theorem log2_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Nat.log2 n :=
  (Nat.le_log2 (by omega)).2 (by rw [pow_one]; exact hn)

/-- `n·log₂ n` is monotone. -/
theorem nlogn_mono {n L : ℕ} (h : n ≤ L) : n * Nat.log2 n ≤ L * Nat.log2 L := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.mul_le_mul h ((Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (by omega)).trans h))

/-- **`√n·polylog n` is `O(n log n)`**, with an explicit constant. -/
theorem sqrt_polylog_le (n : ℕ) (hn : 2 ≤ n) :
    (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8 ≤ 2 ^ 42 * (n * Nat.log2 n) := by
  have hn0 : n ≠ 0 := by omega
  have hx1 : 1 ≤ Nat.log2 n := log2_pos hn
  -- `x + 1 < 2^(x/16 + 5)` for `x = log₂ n`
  have h1 : Nat.log2 n + 1 < 2 ^ (Nat.log2 n / 16 + 5) := by
    have hq : Nat.log2 n / 16 < 2 ^ (Nat.log2 n / 16) := Nat.lt_two_pow_self
    have e : 2 ^ (Nat.log2 n / 16 + 5) = 32 * 2 ^ (Nat.log2 n / 16) := by rw [pow_add]; ring
    rw [e]
    omega
  -- `(x+1)^8 ≤ 2^(x/2 + 40)`
  have h2 : (Nat.log2 n + 1) ^ 8 ≤ 2 ^ (Nat.log2 n / 2 + 40) := by
    have h := Nat.pow_lt_pow_left h1 (by omega : (8 : ℕ) ≠ 0)
    rw [← pow_mul] at h
    exact le_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
  -- `2^(x/2) ≤ √n`
  have h3 : 2 ^ (Nat.log2 n / 2) ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]
    calc 2 ^ (Nat.log2 n / 2) * 2 ^ (Nat.log2 n / 2) = 2 ^ (Nat.log2 n / 2 + Nat.log2 n / 2) :=
          (pow_add _ _ _).symm
      _ ≤ 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := Nat.log2_self_le hn0
  have hs1 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hs2 : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have e40 : 2 ^ (Nat.log2 n / 2 + 40) = 2 ^ 40 * 2 ^ (Nat.log2 n / 2) := by rw [pow_add]; ring
  have h4 : (Nat.log2 n + 1) ^ 8 ≤ 2 ^ 40 * Nat.sqrt n :=
    h2.trans (by rw [e40]; exact Nat.mul_le_mul_left _ h3)
  calc (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8
      ≤ (Nat.sqrt n + 1) * (2 ^ 40 * Nat.sqrt n) := Nat.mul_le_mul_left _ h4
    _ = 2 ^ 40 * (Nat.sqrt n * Nat.sqrt n + Nat.sqrt n) := by ring
    _ ≤ 2 ^ 40 * (n + n) := Nat.mul_le_mul_left _ (Nat.add_le_add hs1 hs2)
    _ = 2 ^ 41 * n := by ring
    _ ≤ 2 ^ 41 * (n * Nat.log2 n) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right n hx1)
    _ ≤ 2 ^ 42 * (n * Nat.log2 n) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (show 41 ≤ 42 by omega))

/-- **Normal form of the auxiliary stage bounds.** -/
theorem poly_le (α β γ n : ℕ) (hn : 2 ≤ n) :
    α * ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8) + β * n + γ ≤
      (α * 2 ^ 42 + β + γ) * (n * Nat.log2 n) := by
  have hq := sqrt_polylog_le n hn
  have hx1 := log2_pos hn
  have hX1 : n ≤ n * Nat.log2 n := Nat.le_mul_of_pos_right n hx1
  have hX2 : 1 ≤ n * Nat.log2 n := le_trans (by omega) hX1
  have h1 : α * ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8) ≤ α * (2 ^ 42 * (n * Nat.log2 n)) :=
    Nat.mul_le_mul_left _ hq
  have h2 : β * n ≤ β * (n * Nat.log2 n) := Nat.mul_le_mul_left _ hX1
  have h3 : γ ≤ γ * (n * Nat.log2 n) := Nat.le_mul_of_pos_right γ hX2
  calc α * ((Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8) + β * n + γ
      ≤ α * (2 ^ 42 * (n * Nat.log2 n)) + β * (n * Nat.log2 n) + γ * (n * Nat.log2 n) :=
        Nat.add_le_add (Nat.add_le_add h1 h2) h3
    _ = (α * 2 ^ 42 + β + γ) * (n * Nat.log2 n) := by ring

#assert_std_axioms succ_sq_le_two_pow sq_bitLen_le log2_pos nlogn_mono sqrt_polylog_le poly_le

end WP.Top
