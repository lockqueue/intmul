/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitMoveDigitMix

/-!
# K1 digit arithmetic (`K1/DigitArith.lean`): uniform radix-`q` digits

**Scope (honest summary).** Pure lemmas about `digitAt`, `setDigit`, `pairPermAddr`
(`Contracts/Streams.lean` §2) and the descriptor keys `keyAt (descL k i j)`
(`K1/DigitWalk.lean`, `K1/DigitBuild.lean`). No program and no contract here.

* `dgt q e x = x / q^e % q` is the digit at (least significant) position `e`; `digitAt q k i` is
  `dgt q (k - 1 - i)` and `setDigit q k i` is `setD q (k - 1 - i)`.
* `dgt_setD`: replacing one digit changes no other digit.
* `keyAt_descL`: the walk keys are the digits at the marked positions.
* `ppu_key`, `ppu_lt`, `ppu_shift`: the merge consistency facts for `pairPermAddr`.
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts

/-- The digit at least-significant position `e`. -/
def dgt (q e x : ℕ) : ℕ := x / q ^ e % q

/-- Replace the digit at position `e` by `d`. -/
def setD (q e d x : ℕ) : ℕ := x - dgt q e x * q ^ e + d * q ^ e

theorem digitAt_eq (q k i x : ℕ) : digitAt q k i x = dgt q (k - 1 - i) x := rfl
theorem setDigit_eq (q k i d x : ℕ) : setDigit q k i d x = setD q (k - 1 - i) d x := rfl

section Digits

variable {q : ℕ}

theorem decompD (q e x : ℕ) : x = x / q ^ (e + 1) * q ^ (e + 1) + dgt q e x * q ^ e + x % q ^ e := by
  have h1 := Nat.div_add_mod' x (q ^ e)
  have h2 := Nat.div_add_mod' (x / q ^ e) q
  rw [Nat.div_div_eq_div_mul, ← pow_succ] at h2
  unfold dgt
  calc x = x / q ^ e * q ^ e + x % q ^ e := h1.symm
    _ = (x / q ^ (e + 1) * q + x / q ^ e % q) * q ^ e + x % q ^ e := by rw [h2]
    _ = x / q ^ (e + 1) * q ^ (e + 1) + x / q ^ e % q * q ^ e + x % q ^ e := by ring

theorem dgt_mul_le (q e x : ℕ) : dgt q e x * q ^ e ≤ x := by
  have h := decompD q e x
  generalize x / q ^ (e + 1) * q ^ (e + 1) = A at h
  generalize dgt q e x * q ^ e = B at h ⊢
  generalize x % q ^ e = C at h
  omega

theorem setD_eq (q e d x : ℕ) :
    setD q e d x = x / q ^ (e + 1) * q ^ (e + 1) + d * q ^ e + x % q ^ e := by
  have h := decompD q e x
  unfold setD
  generalize x / q ^ (e + 1) * q ^ (e + 1) = A at h ⊢
  generalize dgt q e x * q ^ e = B at h ⊢
  generalize x % q ^ e = C at h ⊢
  omega

theorem dgt_lt (hq : 0 < q) (e x : ℕ) : dgt q e x < q := Nat.mod_lt _ hq

/-- Digits of `H·q^(e+1) + d·q^e + L` with `d < q`, `L < q^e`. -/
theorem dgt_compose (hq : 0 < q) {H d L e : ℕ} (hd : d < q) (hL : L < q ^ e) (e' : ℕ) :
    dgt q e' (H * q ^ (e + 1) + d * q ^ e + L) =
      if e' < e then dgt q e' L else if e' = e then d else dgt q (e' - e - 1) H := by
  unfold dgt
  split_ifs with h1 h2
  · -- below the replaced digit
    obtain ⟨t, rfl⟩ : ∃ t, e = e' + 1 + t := ⟨e - e' - 1, by omega⟩
    have hA : H * q ^ (e' + 1 + t + 1) + d * q ^ (e' + 1 + t) =
        q ^ e' * (q * (H * q ^ (t + 1) + d * q ^ t)) := by ring
    rw [hA, Nat.mul_add_div (pow_pos hq _), Nat.add_comm, Nat.add_mul_mod_self_left]
  · subst h2
    have hA : H * q ^ (e' + 1) + d * q ^ e' + L = (H * q + d) * q ^ e' + L := by ring
    rw [hA, div_lin _ _ _ hL, mod_lin _ _ _ hd]
  · obtain ⟨t, rfl⟩ : ∃ t, e' = e + 1 + t := ⟨e' - e - 1, by omega⟩
    have hB : d * q ^ e + L < q ^ (e + 1) := by
      calc d * q ^ e + L < d * q ^ e + q ^ e := by omega
        _ = (d + 1) * q ^ e := by ring
        _ ≤ q * q ^ e := Nat.mul_le_mul_right _ hd
        _ = q ^ (e + 1) := by ring
    rw [show e + 1 + t - e - 1 = t by omega, show q ^ (e + 1 + t) = q ^ (e + 1) * q ^ t by
      rw [pow_add], ← Nat.div_div_eq_div_mul,
      show H * q ^ (e + 1) + d * q ^ e + L = H * q ^ (e + 1) + (d * q ^ e + L) by ring,
      Nat.add_comm, Nat.add_mul_div_right _ _ (pow_pos hq _), Nat.div_eq_of_lt hB,
      Nat.zero_add]

end Digits

section Digits2

variable {q : ℕ}

theorem dgt_of_decomp (hq : 0 < q) (e e' x : ℕ) :
    dgt q e' x = if e' < e then dgt q e' (x % q ^ e) else if e' = e then dgt q e x
      else dgt q (e' - e - 1) (x / q ^ (e + 1)) := by
  conv_lhs => rw [decompD q e x]
  exact dgt_compose hq (dgt_lt hq e x) (Nat.mod_lt _ (pow_pos hq e)) e'

/-- Replacing the digit at position `e` changes no other digit. -/
theorem dgt_setD (hq : 0 < q) {e d : ℕ} (hd : d < q) (e' x : ℕ) :
    dgt q e' (setD q e d x) = if e' = e then d else dgt q e' x := by
  rw [setD_eq, dgt_compose hq hd (Nat.mod_lt _ (pow_pos hq e)) e', dgt_of_decomp hq e e' x]
  split_ifs <;> first | rfl | omega

theorem setD_add (q e d x : ℕ) : setD q e d x + dgt q e x * q ^ e = x + d * q ^ e := by
  have h := dgt_mul_le q e x
  unfold setD
  generalize dgt q e x * q ^ e = B at h ⊢
  omega

theorem setD_lt (hq : 0 < q) {k e d x : ℕ} (he : e < k) (hd : d < q) (hx : x < q ^ k) :
    setD q e d x < q ^ k := by
  rw [setD_eq]
  have hk : q ^ k = q ^ (k - e - 1) * q ^ (e + 1) := by rw [← pow_add]; congr 1; omega
  have hH : x / q ^ (e + 1) < q ^ (k - e - 1) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq _), ← hk]; exact hx
  have hB : d * q ^ e + x % q ^ e < q ^ (e + 1) := by
    have := Nat.mod_lt x (pow_pos hq e)
    calc d * q ^ e + x % q ^ e < d * q ^ e + q ^ e := by omega
      _ = (d + 1) * q ^ e := by ring
      _ ≤ q * q ^ e := Nat.mul_le_mul_right _ hd
      _ = q ^ (e + 1) := by ring
  rw [hk]
  calc x / q ^ (e + 1) * q ^ (e + 1) + d * q ^ e + x % q ^ e <
      x / q ^ (e + 1) * q ^ (e + 1) + q ^ (e + 1) := by omega
    _ = (x / q ^ (e + 1) + 1) * q ^ (e + 1) := by ring
    _ ≤ q ^ (k - e - 1) * q ^ (e + 1) := Nat.mul_le_mul_right _ hH

theorem dgt_mod_pow (hq : 0 < q) {e m : ℕ} (x : ℕ) (h : e < m) : dgt q e (x % q ^ m) = dgt q e x := by
  unfold dgt
  have hm : q ^ m = q ^ e * q ^ (m - e) := by rw [← pow_add]; congr 1; omega
  rw [hm, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self q (by omega : m - e ≠ 0))]

end Digits2

/-! ## Keys of the uniform descriptor -/

section Keys

variable {q : ℕ} [NeZero q]

theorem keyAt_range' (a b : ℕ) : ∀ (m p : ℕ) (κ : Key q) (x : ℕ), x < q ^ m →
    keyAt q ((List.range' p m).map (labOf a b)) κ x =
      (if p ≤ a ∧ a < p + m then Fin.ofNat q (x / q ^ (p + m - 1 - a)) else κ.1,
       if p ≤ b ∧ b < p + m ∧ b ≠ a then Fin.ofNat q (x / q ^ (p + m - 1 - b)) else κ.2)
  | 0, p, κ, x, _ => by
    simp only [List.range'_zero, List.map_nil, keyAt]
    rw [if_neg (show ¬(p ≤ a ∧ a < p + 0) by omega),
      if_neg (show ¬(p ≤ b ∧ b < p + 0 ∧ b ≠ a) by omega)]
  | m + 1, p, κ, x, hx => by
    have hq : 0 < q := Nat.pos_of_neZero q
    rw [List.range'_succ, List.map_cons]
    simp only [keyAt, List.length_map, List.length_range']
    have hx' : x % q ^ m < q ^ m := Nat.mod_lt _ (pow_pos hq m)
    rw [keyAt_range' a b m (p + 1) _ (x % q ^ m) hx']
    have hdig : ∀ e, e < m →
        (Fin.ofNat q (x % q ^ m / q ^ e) : Fin q) = Fin.ofNat q (x / q ^ e) := by
      intro e he
      ext
      simp only [Fin.val_ofNat]
      exact dgt_mod_pow hq x he
    apply Prod.ext
    · by_cases ha : p = a
      · have hl : labOf a b p = .A := by simp [labOf, ha]
        rw [hl, if_neg (show ¬(p + 1 ≤ a ∧ a < p + 1 + m) by omega),
          if_pos (show p ≤ a ∧ a < p + (m + 1) by omega)]
        simp only [updKey]
        rw [show p + (m + 1) - 1 - a = m by omega]
      · have hl : (updKey (labOf a b p) (Fin.ofNat q (x / q ^ m)) κ).1 = κ.1 := by
          unfold labOf
          split_ifs <;> first | rfl | (exfalso; omega)
        rw [hl]
        by_cases h2 : p + 1 ≤ a ∧ a < p + 1 + m
        · rw [if_pos h2, if_pos (show p ≤ a ∧ a < p + (m + 1) by omega),
            show p + 1 + m - 1 - a = p + (m + 1) - 1 - a by omega]
          exact hdig _ (by omega)
        · rw [if_neg h2, if_neg (show ¬(p ≤ a ∧ a < p + (m + 1)) by omega)]
    · by_cases hb : p = b ∧ p ≠ a
      · have hl : labOf a b p = .B := by rw [labOf, if_neg hb.2, if_pos hb.1]
        rw [hl, if_neg (show ¬(p + 1 ≤ b ∧ b < p + 1 + m ∧ b ≠ a) by omega),
          if_pos (show p ≤ b ∧ b < p + (m + 1) ∧ b ≠ a by omega)]
        simp only [updKey]
        rw [show p + (m + 1) - 1 - b = m by omega]
      · have hl : (updKey (labOf a b p) (Fin.ofNat q (x / q ^ m)) κ).2 = κ.2 := by
          unfold labOf
          split_ifs with h1 h2 <;> first | rfl | exact absurd ⟨h2, h1⟩ hb
        rw [hl]
        by_cases h2 : p + 1 ≤ b ∧ b < p + 1 + m ∧ b ≠ a
        · rw [if_pos h2, if_pos (show p ≤ b ∧ b < p + (m + 1) ∧ b ≠ a by omega),
            show p + 1 + m - 1 - b = p + (m + 1) - 1 - b by omega]
          exact hdig _ (by omega)
        · rw [if_neg h2, if_neg (show ¬(p ≤ b ∧ b < p + (m + 1) ∧ b ≠ a) by omega)]

/-- **The walk keys of the uniform descriptor** are the two marked digits. -/
theorem keyAt_descL {k i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j) (κ : Key q) {x : ℕ}
    (hx : x < q ^ k) : keyAt q (descL k i j) κ x = (digitFin q k i x, digitFin q k j x) := by
  have h := keyAt_range' i j k 0 κ x hx
  rw [show (List.range' 0 k).map (labOf i j) = descL k i j by
    simp [descL, List.range_eq_range']] at h
  rw [h, if_pos ⟨Nat.zero_le _, by omega⟩, if_pos ⟨Nat.zero_le _, by omega, Ne.symm hij⟩]
  ext
  · simp [digitFin, digitAt, Fin.val_ofNat]
  · simp [digitFin, digitAt, Fin.val_ofNat]

end Keys

/-! ## The uniform pair permutation -/

section PPU

variable (q k i j : ℕ) [NeZero q]

/-- The key digits `(digit i, digit j)` of an address. -/
def ukey (x : ℕ) : Key q := (digitFin q k i x, digitFin q k j x)

theorem ppu_key (σ : Equiv.Perm (Key q)) (hi : i < k) (hj : j < k) (hij : i ≠ j) (x : ℕ) :
    ukey q k i j (pairPermAddr q k i j σ x) = σ (ukey q k i j x) := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have he : k - 1 - i ≠ k - 1 - j := by omega
  unfold pairPermAddr
  show (digitFin q k i _, digitFin q k j _) = σ (digitFin q k i x, digitFin q k j x)
  generalize σ (digitFin q k i x, digitFin q k j x) = p
  ext
  · simp only [digitFin, digitAt_eq, setDigit_eq]
    rw [dgt_setD hq p.2.isLt, if_neg he, dgt_setD hq p.1.isLt, if_pos rfl]
  · simp only [digitFin, digitAt_eq, setDigit_eq]
    rw [dgt_setD hq p.2.isLt, if_pos rfl]

theorem ppu_lt (σ : Equiv.Perm (Key q)) (hi : i < k) (hj : j < k) (x : ℕ) (hx : x < q ^ k) :
    pairPermAddr q k i j σ x < q ^ k := by
  have hq : 0 < q := Nat.pos_of_neZero q
  unfold pairPermAddr
  simp only [setDigit_eq]
  exact setD_lt hq (by omega) (Fin.isLt _) (setD_lt hq (by omega) (Fin.isLt _) hx)

theorem ppu_shift (σ : Equiv.Perm (Key q)) (hi : i < k) (hj : j < k) (hij : i ≠ j) (x : ℕ) :
    pairPermAddr q k i j σ x + (ukey q k i j x).1.val * q ^ (k - 1 - i) +
        (ukey q k i j x).2.val * q ^ (k - 1 - j) =
      x + (σ (ukey q k i j x)).1.val * q ^ (k - 1 - i) +
        (σ (ukey q k i j x)).2.val * q ^ (k - 1 - j) := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have he : k - 1 - j ≠ k - 1 - i := by omega
  unfold pairPermAddr
  simp only [ukey, setDigit_eq]
  generalize hp : σ (digitFin q k i x, digitFin q k j x) = p
  simp only [digitFin, digitAt_eq]
  have h1 := setD_add q (k - 1 - i) p.1.val x
  have h2 := setD_add q (k - 1 - j) p.2.val (setD q (k - 1 - i) p.1.val x)
  rw [dgt_setD hq p.1.isLt, if_neg he] at h2
  omega

end PPU

end SubNLogN.Machine.K1Digit
