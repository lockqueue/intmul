/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.Twos
import Mathlib.Tactic.Linarith

/-!
# `SubNLogN.Machine.K1.ShiftMath`: bit identities for the exact binary shift (pure)

Paper: Lemma A.4(5) (`lem:transfer-streams`: binary shifts by a
supplied integer exponent, with the necessary guard bits; proof: copy the retained
interval, fill the known zero or redundant sign bits).

**Scope (honest summary).** Pure lemmas, no machine programs. Proved (no `sorry`):
* `zbit z i`: bit `i` of the sign-extended two's-complement expansion of `z : ℤ`;
  `twosBits_eq_map : twosBits w z = (List.range w).map (zbit z)`.
* `zbit_mul_two_pow`, `zbit_ediv_two_pow`: bits of `a·2^t` and `a / 2^s`.
* `zbit_of_fits`: if `FitsTwos w a` (and `w ≥ 1`), every bit at position `≥ w - 1` is the sign.
* `padTo w s l`: truncate `l` to `w` bits, or pad it with copies of `s`.
* `shiftBits_left`, `shiftBits_right`: the record outputs of the shift kernel
  (`K1/Shift.lean`) are `twosBits w2 (a·2^t)` and `twosBits w2 (a / 2^s)`; here the guard
  `FitsTwos w1 a` *is* used (sign extension).
-/

namespace SubNLogN.Machine.K1.ShiftAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.K1

/-! ## Bits of an integer -/

/-- Bit `i` of the (sign-extended) two's-complement expansion of `z`. -/
def zbit (z : ℤ) (i : ℕ) : Bool := decide (z / 2 ^ i % 2 = 1)

theorem two_pow_pos' (i : ℕ) : (0 : ℤ) < 2 ^ i := pow_pos (by norm_num) _

theorem zbit_zero (z : ℤ) : zbit z 0 = decide (z % 2 = 1) := by
  simp [zbit]

theorem zbit_succ (z : ℤ) (i : ℕ) : zbit z (i + 1) = zbit (z / 2) i := by
  unfold zbit
  rw [Int.ediv_ediv_of_nonneg (by norm_num : (0 : ℤ) ≤ 2), ← pow_succ']

theorem twosBits_eq_map : ∀ (w : ℕ) (z : ℤ), twosBits w z = (List.range w).map (zbit z)
  | 0, _ => rfl
  | w + 1, z => by
    rw [twosBits_succ, twosBits_eq_map w (z / 2), List.range_succ_eq_map, List.map_cons,
      List.map_map, zbit_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, zbit_succ]

theorem zbit_mul_two_pow (a : ℤ) (t i : ℕ) :
    zbit (a * 2 ^ t) i = if i < t then false else zbit a (i - t) := by
  unfold zbit
  split_ifs with h
  · have e : a * 2 ^ t = (a * 2 ^ (t - i)) * 2 ^ i := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h.le]
    rw [e, Int.mul_ediv_cancel _ (two_pow_pos' i).ne']
    have hd : (2 : ℤ) ∣ a * 2 ^ (t - i) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) a
    rw [Int.emod_eq_zero_of_dvd hd]
    rfl
  · have h' : t ≤ i := Nat.le_of_not_lt h
    have e : (2 : ℤ) ^ i = 2 ^ t * 2 ^ (i - t) := by rw [← pow_add, Nat.add_sub_cancel' h']
    rw [e, mul_comm a, Int.mul_ediv_mul_of_pos _ _ (two_pow_pos' t)]

theorem zbit_ediv_two_pow (a : ℤ) (s i : ℕ) : zbit (a / 2 ^ s) i = zbit a (i + s) := by
  unfold zbit
  rw [Int.ediv_ediv_of_nonneg (two_pow_pos' s).le, ← pow_add, Nat.add_comm s i]

/-- **Sign extension.** Under the guard `FitsTwos w a`, every bit at position `≥ w - 1` is the
sign of `a`. -/
theorem zbit_of_fits {w : ℕ} {a : ℤ} (ha : FitsTwos w a) {j : ℕ} (hj : w - 1 ≤ j) :
    zbit a j = decide (a < 0) := by
  obtain ⟨h1, h2⟩ := ha
  have hp : (2 : ℤ) ^ (w - 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hpos := two_pow_pos' j
  unfold zbit
  by_cases ha0 : a < 0
  · have hq : a / 2 ^ j = -1 :=
      ((Int.ediv_emod_unique hpos).mpr
        ⟨(show a + 2 ^ j + 2 ^ j * (-1) = a by ring), (by linarith), (by linarith)⟩).1
    rw [hq]
    simp [ha0]
  · have hq : a / 2 ^ j = 0 := Int.ediv_eq_zero_of_lt (by linarith) (by linarith)
    rw [hq]
    simp [ha0]

/-! ## Padding and the record-level shift identities -/

/-- Truncate `l` to `w` bits, or pad it to `w` bits with copies of `s`. -/
def padTo (w : ℕ) (s : Bool) (l : List Bool) : List Bool :=
  l.take w ++ List.replicate (w - l.length) s

theorem length_padTo (w : ℕ) (s : Bool) (l : List Bool) : (padTo w s l).length = w := by
  simp only [padTo, List.length_append, List.length_take, List.length_replicate]
  omega

theorem getElem?_map_range (f : ℕ → Bool) (w i : ℕ) :
    ((List.range w).map f)[i]? = if i < w then some (f i) else none := by
  rw [List.getElem?_map]
  by_cases h : i < w
  · rw [if_pos h, List.getElem?_range h]
    rfl
  · rw [if_neg h, List.getElem?_eq_none (by simp only [List.length_range]; omega)]
    rfl

theorem getElem?_twosBits (w : ℕ) (z : ℤ) (i : ℕ) :
    (twosBits w z)[i]? = if i < w then some (zbit z i) else none := by
  rw [twosBits_eq_map, getElem?_map_range]

theorem getElem?_padTo (w : ℕ) (s : Bool) (l : List Bool) (i : ℕ) :
    (padTo w s l)[i]? = if i < w then some (l.getD i s) else none := by
  unfold padTo
  rw [List.getElem?_append, List.length_take, List.getElem?_take, List.getElem?_replicate,
    List.getD_eq_getElem?_getD]
  by_cases h1 : i < w
  · by_cases h2 : i < l.length
    · rw [if_pos (by omega), if_pos h1, if_pos h1, List.getElem?_eq_getElem h2]
      rfl
    · rw [if_neg (by omega), if_pos (by omega), if_pos h1, List.getElem?_eq_none (by omega)]
      rfl
  · rw [if_neg (by omega), if_neg (by omega), if_neg h1]

theorem getD_twosBits (w : ℕ) (z : ℤ) (i : ℕ) (s : Bool) :
    (twosBits w z).getD i s = if i < w then zbit z i else s := by
  rw [List.getD_eq_getElem?_getD, getElem?_twosBits]
  by_cases h : i < w
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

theorem getD_replicate_append (z i : ℕ) (b s : Bool) (l : List Bool) :
    (List.replicate z b ++ l).getD i s = if i < z then b else l.getD (i - z) s := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_replicate,
    List.getElem?_replicate, List.getD_eq_getElem?_getD]
  by_cases h : i < z
  · rw [if_pos h, if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

theorem getD_drop' (l : List Bool) (d i : ℕ) (s : Bool) :
    (l.drop d).getD i s = l.getD (d + i) s := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getD_eq_getElem?_getD]

/-- **Left shift, record level.** With `z = min t w2` leading zeros, then the input field, padded
with its sign (or truncated) to `w2` bits, the output is the field of `a·2^t`. -/
theorem shiftBits_left {w1 w2 : ℕ} {a : ℤ} (ha : FitsTwos w1 a) (t : ℕ) :
    padTo w2 (decide (a < 0)) (List.replicate (min t w2) false ++ twosBits w1 a) =
      twosBits w2 (a * 2 ^ t) := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_padTo, getElem?_twosBits, zbit_mul_two_pow, getD_replicate_append, getD_twosBits]
  by_cases hi : i < w2
  · rw [if_pos hi, if_pos hi]
    by_cases hz : i < min t w2
    · rw [if_pos hz, if_pos (by omega : i < t)]
    · rw [if_neg hz, if_neg (by omega : ¬ i < t)]
      have hm : min t w2 = t := by omega
      rw [hm]
      by_cases hw : i - t < w1
      · rw [if_pos hw]
      · rw [if_neg hw, zbit_of_fits ha (by omega)]
  · rw [if_neg hi, if_neg hi]

/-- **Right shift, record level.** Dropping the low `s` bits of the input field and padding with
its sign (or truncating) to `w2` bits gives the field of `a / 2^s`. -/
theorem shiftBits_right {w1 w2 : ℕ} {a : ℤ} (ha : FitsTwos w1 a) (s : ℕ) :
    padTo w2 (decide (a < 0)) ((twosBits w1 a).drop s) = twosBits w2 (a / 2 ^ s) := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_padTo, getElem?_twosBits, zbit_ediv_two_pow, getD_drop', getD_twosBits]
  by_cases hi : i < w2
  · rw [if_pos hi, if_pos hi]
    by_cases hw : s + i < w1
    · rw [if_pos hw, Nat.add_comm s i]
    · rw [if_neg hw, zbit_of_fits ha (by omega)]
  · rw [if_neg hi, if_neg hi]

/-- The last bit of a field is its sign. -/
theorem getLast?_twosBits {w : ℕ} {a : ℤ} (hw : 1 ≤ w) (ha : FitsTwos w a) :
    (twosBits w a).getLast? = some (decide (a < 0)) := by
  rw [List.getLast?_eq_getElem?, length_twosBits, getElem?_twosBits, if_pos (by omega),
    zbit_of_fits ha le_rfl]

end SubNLogN.Machine.K1.ShiftAux
