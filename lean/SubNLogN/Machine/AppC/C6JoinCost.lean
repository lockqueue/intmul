/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6JoinCommon

/-!
# Lemma A.8 join/unjoin: shared cost pieces (`Machine/AppC/C6JoinCost.lean`)

Bounds of the counter costs of the joining kernels by the budget `Λ = q^(2e)·G·B`
(`master_le`, `C6JoinMove.lean`), shared by the high join and the unjoin:
`costT_le`, `costP_le` (with `powCost_le_K0`), `loop_overhead_le`, the bit-length helpers
`bitLen_mul_pow_le`, `bitLen_mul_pow_pow_le`, the comparisons `B_pow_le_budget`,
`G_pow_le_budget`, and `Λ ≤ vol v` for both array shapes (`budget_le_vol_hj`, `budget_le_vol_uj`).
`K0 q = 512·(3·|q| + 5)²`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6JoinAux

open NatArith

/-- The constant of `master_le` with `c = |q| + 4`. -/
def K0 (q : ℕ) : ℕ := 512 * (3 * bitLen q + 5) ^ 2

theorem master_le' {q e G B n L : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (hn : n ≤ e)
    (hL : L ≤ 2 * e * bitLen q + bitLen G + bitLen B + (bitLen q + 4)) :
    (n + 1) * L ^ 2 ≤ K0 q * (q ^ (2 * e) * G * B) := by
  have h := master_le hq hG hB hn hL
  have e1 : 2 * bitLen q + (bitLen q + 4) + 1 = 3 * bitLen q + 5 := by ring
  rw [e1] at h
  exact h

theorem powCost_le_K0 {q e G B a n : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (hn : n ≤ e)
    (ha : bitLen (a * q ^ n) ≤ 2 * e * bitLen q + bitLen G + bitLen B + 2) :
    powCost q a n ≤ 200 * (K0 q * (q ^ (2 * e) * G * B)) := by
  have h := master_le' (L := bitLen (a * q ^ n) + bitLen q + 2) hq hG hB hn (by omega)
  unfold powCost
  calc (n + 1) * (200 * (bitLen (a * q ^ n) + bitLen q + 2) ^ 2)
      = 200 * ((n + 1) * (bitLen (a * q ^ n) + bitLen q + 2) ^ 2) := by ring
    _ ≤ 200 * (K0 q * (q ^ (2 * e) * G * B)) := Nat.mul_le_mul_left _ h

theorem pow_le_budget {q e G B : ℕ} (hG : 1 ≤ G) (hB : 1 ≤ B) :
    q ^ (2 * e) ≤ q ^ (2 * e) * G * B :=
  calc q ^ (2 * e) = q ^ (2 * e) * 1 * 1 := by ring
    _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) hB

theorem budget_pos {q e G B : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) :
    1 ≤ q ^ (2 * e) * G * B := by
  have := succ_le_budget (e := e) hq hG hB
  omega

theorem B_pow_le_budget {q e G B n : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hn : n ≤ 2 * e) :
    B * q ^ n ≤ q ^ (2 * e) * G * B := by
  have h1 : q ^ n ≤ q ^ (2 * e) := Nat.pow_le_pow_right (by omega) hn
  calc B * q ^ n ≤ B * q ^ (2 * e) := Nat.mul_le_mul_left _ h1
    _ = q ^ (2 * e) * 1 * B := by ring
    _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hG)

theorem G_pow_le_budget {q e G B n : ℕ} (hq : 2 ≤ q) (hB : 1 ≤ B) (hn : n ≤ 2 * e) :
    G * q ^ n ≤ q ^ (2 * e) * G * B := by
  have h1 : q ^ n ≤ q ^ (2 * e) := Nat.pow_le_pow_right (by omega) hn
  calc G * q ^ n ≤ G * q ^ (2 * e) := Nat.mul_le_mul_left _ h1
    _ = q ^ (2 * e) * G * 1 := by ring
    _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul_left _ hB

theorem bitLen_mul_pow_le (a q n : ℕ) : bitLen (a * q ^ n) ≤ bitLen a + n * bitLen q + 1 :=
  (bitLen_mul_le' a (q ^ n)).trans (by have := bitLen_pow_le' q n; omega)

theorem bitLen_mul_pow_pow_le (a q l r : ℕ) :
    bitLen (a * q ^ l * q ^ r) ≤ bitLen a + (l + r) * bitLen q + 2 := by
  have h1 := bitLen_mul_le' (a * q ^ l) (q ^ r)
  have h2 := bitLen_mul_pow_le a q l
  have h3 := bitLen_pow_le' q r
  have h4 : (l + r) * bitLen q = l * bitLen q + r * bitLen q := by ring
  omega

/-- `k·|q| ≤ 2e·|q|` for `k ≤ 2e`. -/
theorem mul_bitLen_le {k e : ℕ} (q : ℕ) (hk : k ≤ 2 * e) : k * bitLen q ≤ 2 * e * bitLen q :=
  Nat.mul_le_mul_right _ hk

theorem costP_le {q e G B a n : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (hn : n ≤ e)
    (haΛ : a ≤ q ^ (2 * e) * G * B)
    (ha : bitLen (a * q ^ n) ≤ 2 * e * bitLen q + bitLen G + bitLen B + 2) :
    costP q a n ≤ (200 * K0 q + 15) * (q ^ (2 * e) * G * B) := by
  have h1 := powCost_le_K0 hq hG hB hn ha
  have h2 : bitLen a ≤ a := bitLen_le_self' a
  have h3 := budget_pos (e := e) hq hG hB
  unfold costP
  nlinarith

theorem costT_le {q e G B : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (ht : c6T q e ≤ e) :
    costT q e ≤ (8 * tC q + 62) * (q ^ (2 * e) * G * B) := by
  have h1 := tCost_le hq e
  have h2 : (e + 1) ^ 3 ≤ 8 * (q ^ (2 * e) * G * B) :=
    (cube_le_four_pow e).trans
      (Nat.mul_le_mul_left 8 ((four_pow_le hq e).trans (pow_le_budget hG hB)))
  have h3 : tCost q e ≤ 8 * tC q * (q ^ (2 * e) * G * B) :=
    calc tCost q e ≤ tC q * (e + 1) ^ 3 := h1
      _ ≤ tC q * (8 * (q ^ (2 * e) * G * B)) := Nat.mul_le_mul_left _ h2
      _ = 8 * tC q * (q ^ (2 * e) * G * B) := by ring
  have h4 := succ_le_budget (e := e) hq hG hB
  have h5 := bitLen_le_self' e
  have h6 := bitLen_le_self' (c6T q e)
  unfold costT
  nlinarith

theorem loop_overhead_le {q e G B t : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (ht : t ≤ e) :
    16 * t + 13 * bitLen t + 12 ≤ 41 * (q ^ (2 * e) * G * B) := by
  have h1 := succ_le_budget (e := e) hq hG hB
  have h2 := bitLen_le_self' t
  omega

/-- `Λ ≤ vol v` for the array shape of the high join. -/
theorem budget_le_vol_hj {q e A G B : ℕ} {v : List (List Bool)} (hA : 1 ≤ A)
    (hlen : v.length = A * q ^ e * G * q ^ e * B) : q ^ (2 * e) * G * B ≤ vol v := by
  have e1 : A * q ^ e * G * q ^ e * B = A * (q ^ (2 * e) * G * B) := by
    rw [two_mul, pow_add]; ring
  have h1 : q ^ (2 * e) * G * B ≤ v.length := by
    rw [hlen, e1]
    exact Nat.le_mul_of_pos_left _ hA
  exact h1.trans (K1.length_le_vol v)

/-- `Λ ≤ vol v` for the array shape of the unjoin (`t + l = e`). -/
theorem budget_le_vol_uj {q e t l A G B : ℕ} {v : List (List Bool)} (hA : 1 ≤ A)
    (htl : t + l = e) (hlen : v.length = A * q ^ t * q ^ t * q ^ l * G * q ^ l * B) :
    q ^ (2 * e) * G * B ≤ vol v := by
  have e1 : A * q ^ t * q ^ t * q ^ l * G * q ^ l * B = A * (q ^ (2 * e) * G * B) := by
    rw [← htl, show 2 * (t + l) = t + t + l + l by ring, pow_add, pow_add, pow_add]; ring
  have h1 : q ^ (2 * e) * G * B ≤ v.length := by
    rw [hlen, e1]
    exact Nat.le_mul_of_pos_left _ hA
  exact h1.trans (K1.length_le_vol v)

end AppC.C6JoinAux

end SubNLogN.Machine
