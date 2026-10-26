import IntMulTM.Framework.Bits
import IntMulTM.Framework.AxiomGuard
import Mathlib.Tactic.Ring

/-!
# WP.W4o.AddT — truncated binary addition / subtraction on LSB-first bit lists (pure)

`addT sub s U c` is the `|s|` low bits of `s + U + c` (`sub = false`) or `s − U − c`
(`sub = true`), computed LSB first with a carry / borrow; `U` is read only as far as `s` reaches
(missing bits are `0`). The machine kernel `WP.W4o.AddTProg` computes it in place.

* `length_addT`; `bitsVal_addT_add` : value `(val s + val U + c) mod 2^|s|`;
* `addT_round` : subtracting `U` undoes adding `U` (same carry-in), as lists.
-/

namespace TMFw.W4o

open TMFw Computability

/-- Sum bit. -/
def xor3 (x y c : Bool) : Bool := xor (xor x y) c

/-- Carry (`sub = false`) or borrow (`sub = true`). -/
def carry (sub x y c : Bool) : Bool :=
  ((if sub then !x else x) && y) || ((if sub then !x else x) && c) || (y && c)

/-- Truncated add / subtract (see the module doc). -/
def addT (sub : Bool) : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | x :: s, U, c => xor3 x (U.headD false) c :: addT sub s U.tail (carry sub x (U.headD false) c)

theorem length_addT (sub : Bool) :
    ∀ (s U : List Bool) (c : Bool), (addT sub s U c).length = s.length
  | [], _, _ => rfl
  | x :: s, U, c => by
    show (addT sub s U.tail (carry sub x (U.headD false) c)).length + 1 = s.length + 1
    rw [length_addT sub s]

theorem bit_id (x y c : Bool) :
    x.toNat + y.toNat + c.toNat = 2 * (carry false x y c).toNat + (xor3 x y c).toNat := by
  cases x <;> cases y <;> cases c <;> rfl

theorem carry_round (x y c : Bool) : carry true (xor3 x y c) y c = carry false x y c := by
  cases x <;> cases y <;> cases c <;> rfl

theorem xor_round (x y c : Bool) : xor3 (xor3 x y c) y c = x := by
  cases x <;> cases y <;> cases c <;> rfl

/-- `(2X + β) mod 2M = 2·(X mod M) + β` for a bit `β`. -/
theorem two_mul_add_mod (X M β : ℕ) (hβ : β < 2) (hM : 0 < M) :
    (2 * X + β) % (2 * M) = 2 * (X % M) + β := by
  have h0 := Nat.mod_add_div X M
  have h1 : 2 * X + β = (2 * (X % M) + β) + (2 * M) * (X / M) := by
    calc 2 * X + β = 2 * (X % M + M * (X / M)) + β := by rw [h0]
      _ = (2 * (X % M) + β) + (2 * M) * (X / M) := by ring
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt X hM
  omega

theorem bitsVal_split (U : List Bool) :
    bitsVal U = bitsVal U.tail + bitsVal U.tail + (U.headD false).toNat := by
  cases U with
  | nil => rfl
  | cons b l => rfl

theorem bitsVal_tail (U : List Bool) : bitsVal U.tail = bitsVal U / 2 := by
  rw [bitsVal_split U]
  have : (U.headD false).toNat < 2 := Bool.toNat_lt _
  omega

/-- **Value of the truncated sum.** -/
theorem bitsVal_addT_add : ∀ (s U : List Bool) (c : Bool),
    bitsVal (addT false s U c) = (bitsVal s + bitsVal U + c.toNat) % 2 ^ s.length
  | [], U, c => by
    show 0 = (0 + bitsVal U + c.toNat) % 2 ^ 0
    rw [Nat.pow_zero, Nat.mod_one]
  | x :: s, U, c => by
    obtain ⟨M, hMdef⟩ : ∃ M, M = 2 ^ s.length := ⟨_, rfl⟩
    have hM : 0 < M := by rw [hMdef]; exact Nat.two_pow_pos _
    have hpow : 2 ^ (x :: s).length = 2 * M := by
      rw [hMdef, List.length_cons, Nat.pow_succ, Nat.mul_comm]
    have ih := bitsVal_addT_add s U.tail (carry false x (U.headD false) c)
    rw [← hMdef] at ih
    have hU := bitsVal_split U
    have hb := bit_id x (U.headD false) c
    have hxr : (xor3 x (U.headD false) c).toNat < 2 := Bool.toNat_lt _
    have e1 : addT false (x :: s) U c = xor3 x (U.headD false) c ::
        addT false s U.tail (carry false x (U.headD false) c) := rfl
    rw [e1, hpow]
    simp only [bitsVal_cons]
    rw [ih, hU]
    have key : bitsVal s + bitsVal s + x.toNat +
        (bitsVal U.tail + bitsVal U.tail + (U.headD false).toNat) + c.toNat =
        2 * (bitsVal s + bitsVal U.tail + (carry false x (U.headD false) c).toNat) +
          (xor3 x (U.headD false) c).toNat := by omega
    rw [key, two_mul_add_mod _ _ _ hxr hM]
    omega

/-- **Round trip**: subtracting `U` undoes adding `U`. -/
theorem addT_round : ∀ (s U : List Bool) (c : Bool), addT true (addT false s U c) U c = s
  | [], _, _ => rfl
  | x :: s, U, c => by
    show xor3 (xor3 x (U.headD false) c) (U.headD false) c ::
        addT true (addT false s U.tail (carry false x (U.headD false) c)) U.tail
          (carry true (xor3 x (U.headD false) c) (U.headD false) c) = x :: s
    rw [xor_round, carry_round, addT_round s U.tail]

theorem encodeNat_odd (w : ℕ) (hw : w % 2 = 1) : encodeNat w = true :: encodeNat (w / 2) := by
  rw [show w = w / 2 + w / 2 + 1 by omega, encodeNat_add_add_one]
  congr 2
  omega

theorem bitsVal_lt_two_pow : ∀ s : List Bool, bitsVal s < 2 ^ s.length
  | [] => by decide
  | b :: s => by
    have := bitsVal_lt_two_pow s
    have : b.toNat < 2 := Bool.toNat_lt _
    rw [bitsVal_cons, List.length_cons, Nat.pow_succ]
    have : b.toNat ≤ 1 := by omega
    omega

#assert_std_axioms length_addT bitsVal_addT_add addT_round encodeNat_odd bitsVal_tail
  two_mul_add_mod bitsVal_lt_two_pow

end TMFw.W4o
