import WP.W3.Basic

/-!
# WP.W3.Rip — ripple-carry / ripple-borrow on LSB-first bit lists (pure)

`rip f n c A B` runs `n` steps of a ripple loop with bit function `f a b c = (out, carry')`,
reading `A` and `B` LSB first (missing bits read as `0`) from carry `c`; the result lists the `n`
out bits (LSB first), then the final carry.

* `addBit` / `subBit`: full adder / full subtractor.
* `bitsVal_rip_add`: `bitsVal (rip addBit n c A B) = bitsVal A + bitsVal B + c` for `|A|, |B| ≤ n`.
* `bitsVal_rip_sub`: `bitsVal (rip subBit n false A B) = bitsVal A - bitsVal B` for `|A|, |B| ≤ n`
  and `bitsVal B ≤ bitsVal A`.
-/

namespace WP.W3

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- `n` steps of a ripple loop; out bits LSB first, then the final carry. -/
def rip (f : Bool → Bool → Bool → Bool × Bool) : ℕ → Bool → List Bool → List Bool → List Bool
  | 0, c, _, _ => [c]
  | n + 1, c, A, B =>
    (f (A.headD false) (B.headD false) c).1 ::
      rip f n (f (A.headD false) (B.headD false) c).2 A.tail B.tail

/-- Full adder: `a + b + c = out + 2·carry`. -/
def addBit (a b c : Bool) : Bool × Bool := (xor (xor a b) c, (a && b) || (a && c) || (b && c))

/-- Full subtractor: `a - b - c = out - 2·borrow`. -/
def subBit (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, (!a && b) || (!a && c) || (b && c))

theorem length_rip (f : Bool → Bool → Bool → Bool × Bool) :
    ∀ (n : ℕ) (c : Bool) (A B : List Bool), (rip f n c A B).length = n + 1
  | 0, _, _, _ => rfl
  | n + 1, c, A, B => by
    rw [rip, List.length_cons, length_rip f n]

theorem addBit_spec (a b c : Bool) :
    (addBit a b c).1.toNat + 2 * (addBit a b c).2.toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

theorem subBit_spec (a b c : Bool) :
    (subBit a b c).1.toNat + b.toNat + c.toNat = a.toNat + 2 * (subBit a b c).2.toNat := by
  cases a <;> cases b <;> cases c <;> decide

theorem length_tail_le {A : List Bool} {n : ℕ} (h : A.length ≤ n + 1) : A.tail.length ≤ n := by
  rw [List.length_tail]
  omega

theorem eq_nil_of_length_le_zero {A : List Bool} (h : A.length ≤ 0) : A = [] := by
  cases A with
  | nil => rfl
  | cons _ _ => simp at h

theorem bitsVal_rip_add : ∀ (n : ℕ) (c : Bool) (A B : List Bool), A.length ≤ n → B.length ≤ n →
    bitsVal (rip addBit n c A B) = bitsVal A + bitsVal B + c.toNat
  | 0, c, A, B, hA, hB => by
    rw [eq_nil_of_length_le_zero hA, eq_nil_of_length_le_zero hB]
    cases c <;> rfl
  | n + 1, c, A, B, hA, hB => by
    have ih := bitsVal_rip_add n (addBit (A.headD false) (B.headD false) c).2 A.tail B.tail
      (length_tail_le hA) (length_tail_le hB)
    have hs := addBit_spec (A.headD false) (B.headD false) c
    have hA' := bitsVal_eq_head_tail A
    have hB' := bitsVal_eq_head_tail B
    rw [rip, bitsVal_cons, ih]
    omega

theorem bitsVal_rip_sub_aux : ∀ (n : ℕ) (c : Bool) (A B : List Bool), A.length ≤ n →
    B.length ≤ n →
    ∃ k : ℕ, bitsVal (rip subBit n c A B) + bitsVal B + c.toNat = bitsVal A + 2 ^ (n + 1) * k
  | 0, c, A, B, hA, hB => by
    refine ⟨c.toNat, ?_⟩
    rw [eq_nil_of_length_le_zero hA, eq_nil_of_length_le_zero hB]
    cases c <;> rfl
  | n + 1, c, A, B, hA, hB => by
    obtain ⟨k, hk⟩ := bitsVal_rip_sub_aux n (subBit (A.headD false) (B.headD false) c).2 A.tail
      B.tail (length_tail_le hA) (length_tail_le hB)
    refine ⟨k, ?_⟩
    have hs := subBit_spec (A.headD false) (B.headD false) c
    have hA' := bitsVal_eq_head_tail A
    have hB' := bitsVal_eq_head_tail B
    have hp : 2 ^ (n + 1 + 1) * k = 2 * (2 ^ (n + 1) * k) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ (n + 1)) 2, Nat.mul_assoc]
    rw [rip, bitsVal_cons, hp]
    omega

theorem bitsVal_rip_sub (n : ℕ) (A B : List Bool) (hA : A.length ≤ n) (hB : B.length ≤ n)
    (hle : bitsVal B ≤ bitsVal A) : bitsVal (rip subBit n false A B) = bitsVal A - bitsVal B := by
  obtain ⟨k, hk⟩ := bitsVal_rip_sub_aux n false A B hA hB
  have hlt := bitsVal_lt_two_pow (rip subBit n false A B)
  rw [length_rip] at hlt
  have h0 : false.toNat = 0 := rfl
  rcases k with _ | k
  · rw [Nat.mul_zero] at hk
    omega
  · rw [Nat.mul_succ] at hk
    omega

#assert_std_axioms length_rip addBit_spec subBit_spec bitsVal_rip_add bitsVal_rip_sub

end WP.W3
