import Contracts.Machine.Common
import Mathlib.Tactic.Ring

/-!
# WP.W9d.CostPure — the twist cost inequality (pure ℕ arithmetic)

`twist_cost_le`: the summed per-entry / per-row / setup / finish costs of the W9d twist kernel are at
most `(17·D + 150)·twistBound` (with `eb w` unfolded to `2·w + 4`). No new definitions; the
statement is fully unfolded so that W9d can match it against its own cost definitions by `unfold`.

Proof: with `Y = 4·Mul w + 2(2w+4) + 2·pSub + 2` (so `w + s + 1 ≤ Y`, `10 ≤ Y`) and
`Q = t1·r·Y`: entry `≤ 13·D·Y + 120·Y`, row `≤ r·(13·D·Y + 123·Y)`, all rows
`≤ 13·D·Q + 123·Q`, finish `≤ 9·Q`, setup `≤ 3 + 3·D·(hdrLen + 1)`. The products are named and
related by `ring` equalities; `omega` does the linear part.
-/

namespace WP.W9d

open TMFw.Contracts

theorem twist_cost_le (Mul : ℕ → ℕ) (D w pSub s Tstp t1 r tb ob hdrLen : ℕ)
    (hs : s ≤ 2 * pSub + 2) (hT : Tstp ≤ D * (2 * bitLen pSub + 4))
    (ht1 : 1 ≤ t1) (hr : 1 ≤ r) (htb : tb ≤ r * (2 * w + 4)) (hob : ob ≤ t1 * r * (2 * w + 4))
    (hhdr : bitLen pSub + 3 ≤ hdrLen) (hbs : bitLen s ≤ s) :
    (3 + D * (bitLen pSub + 1) + Tstp) +
      (t1 * (((r * ((4 * (D * Mul w + D) + 12 * (D * (w + s + 1)) + 120 * (w + s + 1)) + 2) + 2) +
        (tb * 4 + 2)) + 2) + 2) +
      (tb * 4 + ob * 4 + bitLen s * 3 + 12) ≤
    (17 * D + 150) * (t1 * r * (4 * Mul w + 2 * (2 * w + 4) + 2 * pSub + 2) + hdrLen + 1) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 4 * Mul w + 2 * (2 * w + 4) + 2 * pSub + 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E,
      E = 4 * (D * Mul w + D) + 12 * (D * (w + s + 1)) + 120 * (w + s + 1) := ⟨_, rfl⟩
  rw [← hY, ← hE]
  have hws : w + s + 1 ≤ Y := by omega
  have hY10 : 10 ≤ Y := by omega
  -- one entry
  have hE' : E ≤ 13 * (D * Y) + 120 * Y := by
    have h1 : D * (4 * Mul w + 4) ≤ D * Y := Nat.mul_le_mul (le_refl D) (by omega)
    have h2 : D * (w + s + 1) ≤ D * Y := Nat.mul_le_mul (le_refl D) hws
    have h3 : D * (4 * Mul w + 4) = 4 * (D * Mul w + D) := by ring
    omega
  -- one row
  have hrow : r * (E + 2) + 2 + (tb * 4 + 2) + 2 ≤ r * (13 * (D * Y) + 123 * Y) := by
    have h1 : r * (E + 2) ≤ r * (13 * (D * Y) + 120 * Y + 2) :=
      Nat.mul_le_mul (le_refl r) (by omega)
    have h2 : r * (8 * w + 16) ≤ r * (2 * Y) := Nat.mul_le_mul (le_refl r) (by omega)
    have h3 : r * 10 ≤ r * Y := Nat.mul_le_mul (le_refl r) hY10
    have e1 : r * (13 * (D * Y) + 120 * Y + 2) = 13 * (r * (D * Y)) + 120 * (r * Y) + 2 * r := by
      ring
    have e2 : r * (2 * Y) = 2 * (r * Y) := by ring
    have e3 : r * (13 * (D * Y) + 123 * Y) = 13 * (r * (D * Y)) + 123 * (r * Y) := by ring
    have e4 : r * (2 * w + 4) * 4 = r * (8 * w + 16) := by ring
    omega
  -- all rows
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = t1 * r * Y := ⟨_, rfl⟩
  have hrows : t1 * (r * (E + 2) + 2 + (tb * 4 + 2) + 2) ≤ 13 * (D * Q) + 123 * Q := by
    have h1 := Nat.mul_le_mul (le_refl t1) hrow
    have e : t1 * (r * (13 * (D * Y) + 123 * Y)) = 13 * (D * Q) + 123 * Q := by
      rw [hQ]
      ring
    omega
  -- the finish
  have hfin : tb * 4 + ob * 4 + bitLen s * 3 + 12 ≤ 9 * Q := by
    have hP : 1 ≤ t1 * r := by
      have := Nat.mul_le_mul ht1 hr
      omega
    have hYQ : Y ≤ Q := by
      have := Nat.mul_le_mul hP (le_refl Y)
      omega
    have hrY : r * Y ≤ Q := by
      have h := Nat.mul_le_mul ht1 (le_refl (r * Y))
      have e : t1 * (r * Y) = Q := by
        rw [hQ]
        ring
      omega
    have h2 : r * (8 * w + 16) ≤ r * (2 * Y) := Nat.mul_le_mul (le_refl r) (by omega)
    have e2 : r * (2 * Y) = 2 * (r * Y) := by ring
    have e4 : r * (2 * w + 4) * 4 = r * (8 * w + 16) := by ring
    have h3 : t1 * r * (8 * w + 16) ≤ t1 * r * (2 * Y) :=
      Nat.mul_le_mul (le_refl (t1 * r)) (by omega)
    have e5 : t1 * r * (2 * w + 4) * 4 = t1 * r * (8 * w + 16) := by ring
    have e6 : t1 * r * (2 * Y) = 2 * Q := by
      rw [hQ]
      ring
    omega
  -- the setup
  have hA : D * (bitLen pSub + 1) + D * (2 * bitLen pSub + 4) ≤ 3 * (D * (hdrLen + 1)) := by
    have h1 : D * (3 * bitLen pSub + 5) ≤ D * (3 * (hdrLen + 1)) :=
      Nat.mul_le_mul (le_refl D) (by omega)
    have e1 : D * (bitLen pSub + 1) + D * (2 * bitLen pSub + 4) = D * (3 * bitLen pSub + 5) := by
      ring
    have e2 : D * (3 * (hdrLen + 1)) = 3 * (D * (hdrLen + 1)) := by ring
    omega
  have eR : (17 * D + 150) * (t1 * r * Y + hdrLen + 1) =
      17 * (D * Q) + 150 * Q + 17 * (D * (hdrLen + 1)) + 150 * (hdrLen + 1) := by
    rw [hQ]
    ring
  omega

#assert_std_axioms twist_cost_le

end WP.W9d
