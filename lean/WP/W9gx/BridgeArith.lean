import WP.W9g.Pure
import Contracts.W9.Leaf
import Mathlib.Tactic.Ring

/-!
# WP.W9gx.BridgeArith — the leaf arithmetic of `WP.W9g.Pure` is the snapshot's

* `drp_eq`: `drp = divRoundPow2` (a verbatim copy).
* `rescP_eq_gRescale`: the machine rescale (left shift, or rounding shift) is `gRescale`
  (`IntMul.divRoundRatInt` with power-of-two scales).
* `cellV_eq`: one butterfly cell is `costedButterflyAvg` after `costedGMulScaled`.
* `read1D_eq_getD`, `toList_evens`, `toList_odds`: array reads as list `getD`; the snapshot's
  even/odd splits are `evensL`/`oddsL`.
-/

namespace WP.W9gx

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul WP.W9g

attribute [local instance 10000] instZeroIntElementary

theorem drp_eq (x : ℤ) (s : ℕ) : drp x s = divRoundPow2 x s := rfl

theorem pow_cast_pos (n : ℕ) : (0 : ℤ) < ((2 ^ n : ℕ) : ℤ) := by
  exact_mod_cast Nat.two_pow_pos n

/-- The rescale of one coordinate. -/
theorem rescV_eq (pi po : ℕ) (a : ℤ) :
    IntMul.divRoundRatInt (a * ((2 ^ (po + 2) : ℕ) : ℤ)) ((2 ^ (pi + 2) : ℕ) : ℤ) = rescV pi po a := by
  have hpos := pow_cast_pos (pi + 2)
  unfold IntMul.divRoundRatInt rescV
  rw [if_pos hpos]
  by_cases h : pi ≤ po
  · rw [if_pos h]
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    have hS : ((2 ^ (pi + e + 2) : ℕ) : ℤ) = ((2 ^ (pi + 2) : ℕ) : ℤ) * ((2 ^ e : ℕ) : ℤ) := by
      rw [show pi + e + 2 = pi + 2 + e by omega, Nat.pow_add, Nat.cast_mul]
    rw [hS, show pi + e - pi = e by omega]
    obtain ⟨S, hSd⟩ : ∃ S : ℤ, ((2 ^ (pi + 2) : ℕ) : ℤ) = S := ⟨_, rfl⟩
    obtain ⟨E, hEd⟩ : ∃ E : ℤ, ((2 ^ e : ℕ) : ℤ) = E := ⟨_, rfl⟩
    rw [hSd] at hpos ⊢
    rw [hEd]
    rw [show 2 * (a * (S * E)) + S = S * (2 * (a * E) + 1) by ring, show 2 * S = S * 2 by ring,
      Int.mul_ediv_mul_of_pos _ _ hpos]
    omega
  · rw [if_neg h]
    obtain ⟨d, rfl⟩ : ∃ d, pi = po + (d + 1) := ⟨pi - po - 1, by omega⟩
    have hS : ((2 ^ (po + (d + 1) + 2) : ℕ) : ℤ) =
        ((2 ^ (po + 2) : ℕ) : ℤ) * 2 * ((2 ^ d : ℕ) : ℤ) := by
      rw [show po + (d + 1) + 2 = po + 2 + 1 + d by omega, Nat.pow_add, Nat.pow_succ, Nat.cast_mul,
        Nat.cast_mul]
      push_cast
      ring
    have hD : ((2 ^ (d + 1) : ℕ) : ℤ) = 2 * ((2 ^ d : ℕ) : ℤ) := by
      rw [Nat.pow_succ, Nat.cast_mul]
      push_cast
      ring
    unfold drp
    rw [show po + (d + 1) - po = d + 1 by omega, if_neg (by omega), show d + 1 - 1 = d by omega,
      hS, hD]
    have hS0 := pow_cast_pos (po + 2)
    obtain ⟨S, hSd⟩ : ∃ S : ℤ, ((2 ^ (po + 2) : ℕ) : ℤ) = S := ⟨_, rfl⟩
    obtain ⟨D, hDd⟩ : ∃ D : ℤ, ((2 ^ d : ℕ) : ℤ) = D := ⟨_, rfl⟩
    rw [hSd] at hS0 ⊢
    rw [hDd]
    have hS2 : 0 < S * 2 := by omega
    rw [show 2 * (a * S) + S * 2 * D = S * 2 * (a + D) by ring,
      show 2 * (S * 2 * D) = S * 2 * (2 * D) by ring, Int.mul_ediv_mul_of_pos _ _ hS2]

/-- **The rescale is `gRescale`.** -/
theorem rescP_eq_gRescale (pi po : ℕ) (z : ℤ × ℤ) : gRescale pi po z = rescP pi po z := by
  show (IntMul.divRoundRatInt (z.1 * ((2 ^ (po + 2) : ℕ) : ℤ)) ((2 ^ (pi + 2) : ℕ) : ℤ),
      IntMul.divRoundRatInt (z.2 * ((2 ^ (po + 2) : ℕ) : ℤ)) ((2 ^ (pi + 2) : ℕ) : ℤ)) =
    (rescV pi po z.1, rescV pi po z.2)
  rw [rescV_eq, rescV_eq]

/-- **One butterfly cell.** -/
theorem cellV_eq (q2 w : ℕ) (y0 y1 ω : ℤ × ℤ) :
    (costedButterflyAvg w y0 (costedGMulScaled q2 w ω y1).1).1 = cellV q2 y0 y1 ω := rfl

/-- An array read is a list `getD`. -/
theorem read1D_eq_getD (x : Array (ℤ × ℤ)) (i : ℕ) : read1D x i = x.toList.getD i (0, 0) := by
  unfold read1D
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [h]
    rfl

theorem ofFn_getD_evens : ∀ (n : ℕ) (l : List (ℤ × ℤ)), l.length = 2 * n →
    List.ofFn (fun j : Fin n => l.getD (2 * j.val) (0, 0)) = evensL l
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, a :: b :: l, h => by
    have ih := ofFn_getD_evens n l (by simp at h; omega)
    rw [List.ofFn_succ, evensL, ← ih]
    simp only [Fin.val_zero, Nat.mul_zero, List.getD_cons_zero, Fin.val_succ, Nat.mul_succ,
      List.getD_cons_succ]

theorem ofFn_getD_odds : ∀ (n : ℕ) (l : List (ℤ × ℤ)), l.length = 2 * n →
    List.ofFn (fun j : Fin n => l.getD (2 * j.val + 1) (0, 0)) = oddsL l
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, a :: b :: l, h => by
    have ih := ofFn_getD_odds n l (by simp at h; omega)
    rw [List.ofFn_succ, oddsL, ← ih]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, List.getD_cons_succ,
      Fin.val_succ, Nat.mul_succ]

/-- The snapshot's even split. -/
theorem toList_evens (x : Array (ℤ × ℤ)) (n : ℕ) (hx : x.size = 2 * n) :
    (Array.ofFn (fun j : Fin n => read1D x (2 * j.val))).toList = evensL x.toList := by
  rw [Array.toList_ofFn]
  simp only [read1D_eq_getD]
  exact ofFn_getD_evens n x.toList (by simpa using hx)

/-- The snapshot's odd split. -/
theorem toList_odds (x : Array (ℤ × ℤ)) (n : ℕ) (hx : x.size = 2 * n) :
    (Array.ofFn (fun j : Fin n => read1D x (2 * j.val + 1))).toList = oddsL x.toList := by
  rw [Array.toList_ofFn]
  simp only [read1D_eq_getD]
  exact ofFn_getD_odds n x.toList (by simpa using hx)

#assert_std_axioms drp_eq pow_cast_pos rescV_eq rescP_eq_gRescale cellV_eq read1D_eq_getD
  ofFn_getD_evens ofFn_getD_odds toList_evens toList_odds

end WP.W9gx
