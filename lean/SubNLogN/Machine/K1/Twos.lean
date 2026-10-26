/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import Mathlib.Tactic.LinearCombination

/-!
# `SubNLogN.Machine.K1.Twos`: arithmetic of `w`-bit two's-complement fields (pure)

Paper: Fact 3.3(5) (`fact:oai-streams`) and Lemma A.4(5) (`lem:transfer-streams`:
"exact fixed-width addition, subtraction, sign changes, ... when the
necessary guard bits are present"; "fixed-width coefficient arithmetic uses
ordinary carry scans").

**Scope (honest summary).** Pure lemmas about the field encoding `twosBits`
(`Contracts/Streams.lean:76`) and a bit-serial ripple `ripOut`. There are no machine programs
here. Everything is proved (no `sorry`):
* `bitsLE_succ`, `twosBits_succ`: peel off the least significant bit;
  `length_bitsLE`, `length_twosBits`; `bitsLE_mod`, `twosBits_eq_bitsLE`.
* `ripOut_twosBits`: let the bit function `f a b c = (out, c')` satisfy the linear carry law
  `α·a + β·b + γ·c = out + 2·γ·c'` (`LinBit f α β γ`). Then the ripple of `f` over two `w`-bit
  fields, from carry `c`, is the `w`-bit field of `α·x + β·y + γ·c`.
* Instances: `ripOut_add` (`x + y`, full adder), `ripOut_sub` (`x - y`, full subtractor),
  `ripOut_neg` (`-x`; the second operand is ignored).

These identities hold modulo `2^w` with no guard hypothesis. The contracts' guards `FitsTwos`
are needed only to read the fields back as the exact integers; the bit identities do not use
them.
-/

namespace SubNLogN.Machine.K1

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## Peeling bits -/

theorem length_bitsLE (w d : ℕ) : (bitsLE w d).length = w := by
  simp [bitsLE]

theorem length_twosBits (w : ℕ) (z : ℤ) : (twosBits w z).length = w :=
  length_bitsLE _ _

@[simp] theorem bitsLE_zero (d : ℕ) : bitsLE 0 d = [] := rfl

@[simp] theorem twosBits_zero (z : ℤ) : twosBits 0 z = [] := rfl

theorem bitsLE_succ (w d : ℕ) : bitsLE (w + 1) d = d.testBit 0 :: bitsLE w (d / 2) := by
  unfold bitsLE
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.testBit_div_two, Nat.succ_eq_add_one]

/-- `bitsLE w d` only depends on `d mod 2^w`. -/
theorem bitsLE_mod (w d : ℕ) : bitsLE w (d % 2 ^ w) = bitsLE w d := by
  unfold bitsLE
  apply List.map_congr_left
  intro i hi
  rw [Nat.testBit_mod_two_pow]
  simp [List.mem_range.1 hi]

/-- A natural representative of `z` modulo `2^w` gives the same field. -/
theorem twosBits_eq_bitsLE {w d : ℕ} {z : ℤ} (h : (d : ℤ) % 2 ^ w = z % 2 ^ w) :
    twosBits w z = bitsLE w d := by
  unfold twosBits
  rw [← h, ← bitsLE_mod w d]
  congr 1

/-- Peel off the least significant bit of a field. -/
theorem twosBits_succ (w : ℕ) (z : ℤ) :
    twosBits (w + 1) z = decide (z % 2 = 1) :: twosBits w (z / 2) := by
  have hM : (0 : ℤ) < 2 ^ (w + 1) := pow_pos (by norm_num) _
  have hd' : (((z % 2 ^ (w + 1)).toNat : ℕ) : ℤ) = z % 2 ^ (w + 1) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hq := Int.mul_ediv_add_emod z (2 ^ (w + 1))
  generalize (z % 2 ^ (w + 1)).toNat = d at hd'
  have e1 : twosBits (w + 1) z = bitsLE (w + 1) d := by
    unfold twosBits
    congr 1
    rw [← hd', Int.toNat_natCast]
  rw [e1, bitsLE_succ, Nat.testBit_zero]
  congr 1
  · have h2 : (z % 2 ^ (w + 1)) % 2 = z % 2 :=
      Int.emod_emod_of_dvd z (dvd_pow_self 2 (Nat.succ_ne_zero w))
    rw [← hd'] at h2
    simp only [decide_eq_decide]
    omega
  · symm
    apply twosBits_eq_bitsLE
    have e2 : (2 : ℤ) ^ (w + 1) * (z / 2 ^ (w + 1)) = 2 * (2 ^ w * (z / 2 ^ (w + 1))) := by
      ring
    rw [e2, ← hd'] at hq
    have hA : z / 2 = (d : ℤ) / 2 + 2 ^ w * (z / 2 ^ (w + 1)) := by
      generalize 2 ^ w * (z / 2 ^ (w + 1)) = A at hq ⊢
      omega
    rw [hA, Int.add_mul_emod_self_left]
    push_cast
    rfl

/-! ## Ripple of a linear bit function -/

/-- Bit-serial ripple of a bit function `f a b c = (out, c')` over two least-significant-first
bit lists, from carry `c`. The output has the length of the shorter list; the final carry is
dropped. -/
def ripOut (f : Bool → Bool → Bool → Bool × Bool) : Bool → List Bool → List Bool → List Bool
  | c, x :: xs, y :: ys => (f x y c).1 :: ripOut f (f x y c).2 xs ys
  | _, _, _ => []

@[simp] theorem ripOut_cons (f : Bool → Bool → Bool → Bool × Bool) (c x y : Bool)
    (xs ys : List Bool) :
    ripOut f c (x :: xs) (y :: ys) = (f x y c).1 :: ripOut f (f x y c).2 xs ys := rfl

@[simp] theorem ripOut_nil_left (f : Bool → Bool → Bool → Bool × Bool) (c : Bool)
    (ys : List Bool) : ripOut f c [] ys = [] := rfl

theorem length_ripOut (f : Bool → Bool → Bool → Bool × Bool) :
    ∀ (c : Bool) (xs ys : List Bool), xs.length = ys.length → (ripOut f c xs ys).length = xs.length
  | _, [], _, _ => rfl
  | _, _ :: _, [], h => by simp at h
  | c, x :: xs, y :: ys, h => by
    simp only [ripOut_cons, List.length_cons]
    rw [length_ripOut f _ xs ys (by simpa using h)]

/-- The linear carry law of a bit function `f a b c = (out, c')`:
`α·a + β·b + γ·c = out + 2·γ·c'`. -/
def LinBit (f : Bool → Bool → Bool → Bool × Bool) (α β γ : ℤ) : Prop :=
  ∀ a b c : Bool, α * (a.toNat : ℤ) + β * (b.toNat : ℤ) + γ * (c.toNat : ℤ) =
    ((f a b c).1.toNat : ℤ) + 2 * (γ * ((f a b c).2.toNat : ℤ))

theorem emod_two_eq_toNat (z : ℤ) : z % 2 = ((decide (z % 2 = 1)).toNat : ℤ) := by
  rcases Int.emod_two_eq_zero_or_one z with h | h <;> simp [h]

theorem bit_split (K : ℤ) (o : Bool) :
    decide ((2 * K + (o.toNat : ℤ)) % 2 = 1) = o ∧ (2 * K + (o.toNat : ℤ)) / 2 = K := by
  cases o
  · simp only [Bool.toNat_false, Nat.cast_zero, add_zero, decide_eq_false_iff_not]
    constructor <;> omega
  · simp only [Bool.toNat_true, Nat.cast_one, decide_eq_true_eq]
    constructor <;> omega

/-- **Ripple of a linear bit function on two's-complement fields.** -/
theorem ripOut_twosBits {f : Bool → Bool → Bool → Bool × Bool} {α β γ : ℤ}
    (hf : LinBit f α β γ) :
    ∀ (w : ℕ) (x y : ℤ) (c : Bool),
      ripOut f c (twosBits w x) (twosBits w y) = twosBits w (α * x + β * y + γ * c.toNat)
  | 0, _, _, _ => rfl
  | w + 1, x, y, c => by
    have hx : x = 2 * (x / 2) + ((decide (x % 2 = 1)).toNat : ℤ) := by
      rw [← emod_two_eq_toNat]; omega
    have hy : y = 2 * (y / 2) + ((decide (y % 2 = 1)).toNat : ℤ) := by
      rw [← emod_two_eq_toNat]; omega
    rw [twosBits_succ w x, twosBits_succ w y, twosBits_succ w, ripOut_cons]
    generalize decide (x % 2 = 1) = a at hx ⊢
    generalize decide (y % 2 = 1) = b at hy ⊢
    have hab := hf a b c
    generalize (f a b c).1 = o at hab ⊢
    generalize (f a b c).2 = c' at hab ⊢
    have key : α * x + β * y + γ * c.toNat =
        2 * (α * (x / 2) + β * (y / 2) + γ * c'.toNat) + o.toNat := by
      linear_combination α * hx + β * hy + hab
    rw [ripOut_twosBits hf w (x / 2) (y / 2) c', key,
      (bit_split (α * (x / 2) + β * (y / 2) + γ * c'.toNat) o).1,
      (bit_split (α * (x / 2) + β * (y / 2) + γ * c'.toNat) o).2]

/-! ## Full adder, full subtractor, negation -/

/-- Full adder: `a + b + c = out + 2·c'`. -/
def addBit (a b c : Bool) : Bool × Bool := (xor (xor a b) c, (a && b) || (a && c) || (b && c))

/-- Full subtractor: `a - b - c = out - 2·c'` (`c` is the borrow). -/
def subBit (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, (!a && b) || (!a && c) || (b && c))

/-- Negation step (the second operand is ignored): `-a - c = out - 2·c'`. -/
def negBit (a _b c : Bool) : Bool × Bool := (xor a c, a || c)

theorem linBit_add : LinBit addBit 1 1 1 := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [addBit]

theorem linBit_sub : LinBit subBit 1 (-1) (-1) := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [subBit]

theorem linBit_neg : LinBit negBit (-1) 0 (-1) := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [negBit]

theorem ripOut_add (w : ℕ) (x y : ℤ) :
    ripOut addBit false (twosBits w x) (twosBits w y) = twosBits w (x + y) := by
  rw [ripOut_twosBits linBit_add]; simp

theorem ripOut_sub (w : ℕ) (x y : ℤ) :
    ripOut subBit false (twosBits w x) (twosBits w y) = twosBits w (x - y) := by
  rw [ripOut_twosBits linBit_sub]; congr 1; simp; ring

theorem ripOut_neg (w : ℕ) (x y : ℤ) :
    ripOut negBit false (twosBits w x) (twosBits w y) = twosBits w (-x) := by
  rw [ripOut_twosBits linBit_neg]; congr 1; simp

end SubNLogN.Machine.K1
