import WP.W9f.Spec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# WP.W9fF.CostArith — cost units of the forward core

`UA C Mul H = (C+1)·(Mul (solW H) + H + 1)` is the per-index unit and `UQ C H = (C+1)·(H+1)²`
the once-per-column unit. The per-statement caps of the abstract interpreter (`Bound.lean`) at
width `W = solW H` are multiples of these units.
-/

namespace WP.W9fF

open WP.W9f

/-- Per-index cost unit. -/
def UA (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) : ℕ := (C + 1) * (Mul (solW H) + H + 1)

/-- Once-per-column cost unit. -/
def UQ (C H : ℕ) : ℕ := (C + 1) * (H + 1) ^ 2

theorem one_le_UA (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) : 1 ≤ UA C Mul H := by
  unfold UA
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

theorem le_UA_H (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) : (C + 1) * (H + 1) ≤ UA C Mul H := by
  unfold UA
  exact Nat.mul_le_mul_left _ (by omega)

theorem le_UA_mul (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) : C * Mul (solW H) + C ≤ UA C Mul H := by
  unfold UA
  nlinarith [Nat.zero_le (C * H), Nat.zero_le (Mul (solW H)), Nat.zero_le H]

theorem le_UQ_H (C H : ℕ) : (C + 1) * (H + 1) ≤ UQ C H := by
  unfold UQ
  exact Nat.mul_le_mul_left _ (by nlinarith)

/-- Cap of one product statement. -/
theorem mulTerm_le (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) :
    C * Mul (solW H) + C + 20 * solW H + 43 ≤ 204 * UA C Mul H := by
  unfold UA
  generalize Mul (solW H) = M
  unfold solW
  nlinarith [Nat.zero_le (C * H), Nat.zero_le (C * M), Nat.zero_le M]

/-- Cap of one linear-cost statement. -/
theorem smallTerm_le (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) :
    C * (2 * solW H + 1) + 20 * solW H + 43 ≤ 220 * UA C Mul H := by
  unfold UA
  generalize Mul (solW H) = M
  unfold solW
  nlinarith [Nat.zero_le (C * H), Nat.zero_le (C * M), Nat.zero_le M]

/-- Cap of one division statement. -/
theorem divTerm_le (C H : ℕ) :
    C * (solW H * solW H + 2 * solW H + 1) + 20 * solW H + 43 ≤ 300 * UQ C H := by
  unfold solW UQ
  nlinarith [Nat.zero_le (C * (H + 1)), Nat.zero_le (C * (H + 1) ^ 2), Nat.zero_le H]

theorem le_UA_H' (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) : H + 1 ≤ UA C Mul H :=
  le_trans (Nat.le_mul_of_pos_left _ (by omega)) (le_UA_H C Mul H)

/-- Assembly of the total cost. -/
theorem total_le (D A Q t1 k1 k2 k3 T : ℕ) (ht : 1 ≤ t1) (hA : 1 ≤ A) (hQ : 1 ≤ Q) (hD : 1 ≤ D)
    (hT : T ≤ k1 * (D * A) + k2 * (D * Q) + t1 * (k3 * (D * A) + 4) + 6) :
    T ≤ (k1 + k2 + k3 + 12) * D * (t1 * A + Q) := by
  have hX : 1 ≤ D * A := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hY : 1 ≤ D * Q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e : (k1 + k2 + k3 + 12) * D * (t1 * A + Q) =
      (k1 + k2 + k3 + 12) * (t1 * (D * A)) + (k1 + k2 + k3 + 12) * (D * Q) := by ring
  rw [e]
  have h1 : D * A ≤ t1 * (D * A) := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : t1 ≤ t1 * (D * A) := Nat.le_mul_of_pos_right _ hX
  have e2 : t1 * (k3 * (D * A) + 4) = k3 * (t1 * (D * A)) + 4 * t1 := by ring
  rw [e2] at hT
  generalize D * A = X at *
  generalize D * Q = Y at *
  generalize t1 * X = Z at *
  have a1 : k1 * X ≤ k1 * Z := Nat.mul_le_mul_left _ h1
  have a2 : (k1 + k2 + k3 + 12) * Z = k1 * Z + k2 * Z + k3 * Z + 12 * Z := by ring
  have a3 : (k1 + k2 + k3 + 12) * Y = k1 * Y + k2 * Y + k3 * Y + 12 * Y := by ring
  rw [a2, a3]
  omega

#assert_std_axioms total_le le_UA_H' one_le_UA le_UA_H le_UA_mul le_UQ_H mulTerm_le smallTerm_le divTerm_le

end WP.W9fF
