import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W10.Arith — `ℕ` helpers for the W10 cost theorem

Pure natural-number facts used by `WP.W10.Cost`:
* `succ_sq_le_four_mul_two_pow`: `(k + 1)² ≤ 4·2^k`, the only "logarithm versus power" fact needed;
* `sqrt_le_of_le_mul_sq`: `w ≤ A·(L+1)² → √w ≤ A·(L+1)` (large widths);
* `sqrt_mul_succ_le`: `2^k ≤ L → w ≤ L → √w·(k+1) ≤ 2L` (small widths);
* `sum_range_map_add`, `sum_range_map_mul_le`: sums over `List.range`.

`√` is `Nat.sqrt` (floor) throughout.
-/

namespace WP.W10

/-- `(k + 1)² ≤ 4·2^k`. -/
theorem succ_sq_le_four_mul_two_pow (k : ℕ) : (k + 1) ^ 2 ≤ 4 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have e1 : (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + 2 * k + 3 := by ring
    have e2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [e1, e2]
    omega

/-- Large widths: `w ≤ A·(L+1)²` gives `√w ≤ A·(L+1)` (via `A ≤ A²`, so no case split on `A`). -/
theorem sqrt_le_of_le_mul_sq {w A L : ℕ} (hw : w ≤ A * (L + 1) ^ 2) :
    Nat.sqrt w ≤ A * (L + 1) := by
  have h : w ≤ (A * (L + 1)) ^ 2 :=
    calc w ≤ A * (L + 1) ^ 2 := hw
      _ ≤ (A * A) * (L + 1) ^ 2 := Nat.mul_le_mul_right _ (Nat.le_mul_self A)
      _ = (A * (L + 1)) ^ 2 := by ring
  calc Nat.sqrt w ≤ Nat.sqrt ((A * (L + 1)) ^ 2) := Nat.sqrt_le_sqrt h
    _ = A * (L + 1) := Nat.sqrt_eq' _

/-- Small widths: if `2^k ≤ L` and `w ≤ L` then `√w·(k+1) ≤ 2L`, because
`(√w·(k+1))² ≤ L·4·2^k ≤ (2L)²`. -/
theorem sqrt_mul_succ_le {w L k : ℕ} (hpow : 2 ^ k ≤ L) (hw : w ≤ L) :
    Nat.sqrt w * (k + 1) ≤ 2 * L := by
  have hs : Nat.sqrt w ^ 2 ≤ L := le_trans (Nat.sqrt_le' w) hw
  have hk : (k + 1) ^ 2 ≤ 4 * L :=
    le_trans (succ_sq_le_four_mul_two_pow k) (Nat.mul_le_mul_left 4 hpow)
  have h2 : (Nat.sqrt w * (k + 1)) ^ 2 ≤ (2 * L) ^ 2 :=
    calc (Nat.sqrt w * (k + 1)) ^ 2 = Nat.sqrt w ^ 2 * (k + 1) ^ 2 := by ring
      _ ≤ L * (4 * L) := Nat.mul_le_mul hs hk
      _ = (2 * L) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide)).1 h2

/-- Sums over `List.range` split over `+`. -/
theorem sum_range_map_add (m : ℕ) (f g : ℕ → ℕ) :
    ((List.range m).map fun i => f i + g i).sum =
      ((List.range m).map f).sum + ((List.range m).map g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    simp only [hr, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ih]
    omega

/-- A termwise bound `f i·c ≤ B` over `List.range m` gives `(Σ f)·c ≤ m·B`. -/
theorem sum_range_map_mul_le (m : ℕ) (f : ℕ → ℕ) (c B : ℕ) (h : ∀ i < m, f i * c ≤ B) :
    ((List.range m).map f).sum * c ≤ m * B := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h m (by omega)
    have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    simp only [hr, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, Nat.add_mul, Nat.one_mul]
    omega

#assert_std_axioms succ_sq_le_four_mul_two_pow sqrt_le_of_le_mul_sq sqrt_mul_succ_le
  sum_range_map_add sum_range_map_mul_le

end WP.W10
