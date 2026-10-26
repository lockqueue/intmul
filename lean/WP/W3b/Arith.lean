import Contracts.Machine.W3
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# WP.W3b.Arith — pure bit-list arithmetic behind `×3` and exact `÷3`

* `×3`, LSB first (`m3run`): carry `c ∈ Fin 3`, step `3·b + c = 2·c' + o` (`m3_id`); after the
  input, the carry is flushed as `flushBits c` (`0 ↦ []`, `1 ↦ [1]`, `2 ↦ [0,1]`).
  `m3_result : out ++ flushBits c = encodeNat (3a)` (value by `m3run_val`, canonical form because
  the last carry of a canonical nonzero input is `≥ 1`, `m3run_carry_pos`).
* `÷3`, MSB first (`d3full`): remainder `r ∈ Fin 3`, step `2·r + b = 3·q + r'` (`d3_id`).
  `d3run` is the same scan but suppresses leading zero quotient bits (`d3run_eq`);
  `d3_result : (d3run 0 false (encodeNat A).reverse).reverse = encodeNat (A / 3)`.
-/

namespace TMFw.W3b

open TMFw Computability

/-! ## Bit lists -/

theorem bitsVal_append : ∀ L M : List Bool,
    bitsVal (L ++ M) = bitsVal L + 2 ^ L.length * bitsVal M
  | [], M => by simp
  | b :: L, M => by
    rw [List.cons_append, bitsVal_cons, bitsVal_append L M, bitsVal_cons, List.length_cons,
      pow_succ]
    ring

theorem normBits_append_true : ∀ M : List Bool, normBits (M ++ [true]) = M ++ [true]
  | [] => by simp [normBits]
  | b :: M => by
    rw [List.cons_append, normBits, normBits_append_true M]
    simp

theorem normBits_tail {b : Bool} {L : List Bool} (h : normBits (b :: L) = b :: L) :
    normBits L = L := by
  have h2 : (if b = false ∧ normBits L = [] then [] else b :: normBits L) = b :: L := h
  split at h2
  · exact absurd h2 (List.cons_ne_nil _ _).symm
  · exact (List.cons.inj h2).2

/-! ## `×3`, LSB first -/

/-- `3·b + c`. -/
def m3s (c : Fin 3) (b : Bool) : ℕ := 3 * b.toNat + c.val

/-- Output bit of one `×3` step. -/
def m3o (c : Fin 3) (b : Bool) : Bool := decide (m3s c b % 2 = 1)

/-- Carry out of one `×3` step. -/
def m3c (c : Fin 3) (b : Bool) : Fin 3 :=
  ⟨m3s c b / 2, by have := c.isLt; have := Bool.toNat_le b; unfold m3s; omega⟩

theorem m3_id (c : Fin 3) (b : Bool) : 3 * b.toNat + c.val = 2 * (m3c c b).val + (m3o c b).toNat := by
  revert c b
  decide

/-- Run `×3` over an LSB-first bit list: output bits and final carry. -/
def m3run : Fin 3 → List Bool → List Bool × Fin 3
  | c, [] => ([], c)
  | c, b :: l => (m3o c b :: (m3run (m3c c b) l).1, (m3run (m3c c b) l).2)

/-- The flushed carry, LSB first. -/
def flushBits (c : Fin 3) : List Bool :=
  if c.val = 0 then [] else if c.val = 1 then [true] else [false, true]

theorem bitsVal_flushBits (c : Fin 3) : bitsVal (flushBits c) = c.val := by
  revert c
  decide

theorem flushBits_length (c : Fin 3) : (flushBits c).length ≤ 2 := by
  revert c
  decide

theorem m3run_length : ∀ (c : Fin 3) (l : List Bool), (m3run c l).1.length = l.length
  | _, [] => rfl
  | c, b :: l => by simp [m3run, m3run_length (m3c c b) l]

theorem m3run_val : ∀ (c : Fin 3) (l : List Bool),
    bitsVal (m3run c l).1 + 2 ^ l.length * (m3run c l).2.val = 3 * bitsVal l + c.val
  | c, [] => by simp [m3run]
  | c, b :: l => by
    have ih := m3run_val (m3c c b) l
    have hid := m3_id c b
    simp only [m3run, bitsVal_cons, List.length_cons, pow_succ]
    linear_combination 2 * ih + hid.symm

theorem m3run_carry_pos : ∀ (L : List Bool) (c : Fin 3), normBits L = L → L ≠ [] →
    1 ≤ (m3run c L).2.val
  | [], _, _, h => absurd rfl h
  | [b], c, hn, _ => by
    cases b
    · simp [normBits] at hn
    · simp only [m3run, m3c, m3s, Bool.toNat_true]
      omega
  | b :: b' :: L, c, hn, _ => by
    simp only [m3run]
    exact m3run_carry_pos (b' :: L) (m3c c b) (normBits_tail hn) (List.cons_ne_nil _ _)

/-- **`×3` result**: output plus flushed carry is the canonical encoding of `3a`. -/
theorem m3_result (a : ℕ) :
    (m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2 = encodeNat (3 * a) := by
  have hval := m3run_val 0 (encodeNat a)
  have hlen := m3run_length 0 (encodeNat a)
  have hb : bitsVal ((m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2) =
      3 * a := by
    rw [bitsVal_append, bitsVal_flushBits, hlen, hval, bitsVal_encodeNat]
    simp
  have hn : normBits ((m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2) =
      (m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2 := by
    by_cases ha : a = 0
    · subst ha
      simp [encodeNat_zero, m3run, flushBits, normBits]
    · have hne : encodeNat a ≠ [] := fun h => ha ((encodeNat_eq_nil_iff a).1 h)
      have hpos := m3run_carry_pos (encodeNat a) 0 (normBits_encodeNat a) hne
      have hlt := (m3run 0 (encodeNat a)).2.isLt
      simp only [flushBits]
      rw [if_neg (show ¬ (m3run 0 (encodeNat a)).2.val = 0 by omega)]
      split_ifs
      · exact normBits_append_true _
      · rw [show (m3run 0 (encodeNat a)).1 ++ [false, true] =
          ((m3run 0 (encodeNat a)).1 ++ [false]) ++ [true] by simp]
        exact normBits_append_true _
  rw [← hb, encodeNat_bitsVal, hn]

/-! ## Exact `÷3`, MSB first -/

/-- `2·r + b`. -/
def d3v (r : Fin 3) (b : Bool) : ℕ := 2 * r.val + b.toNat

/-- Quotient bit of one long-division step. -/
def d3q (r : Fin 3) (b : Bool) : Bool := decide (3 ≤ d3v r b)

/-- Remainder after one long-division step. -/
def d3r (r : Fin 3) (b : Bool) : Fin 3 := ⟨d3v r b % 3, Nat.mod_lt _ (by decide)⟩

theorem d3_id (r : Fin 3) (b : Bool) : 2 * r.val + b.toNat = 3 * (d3q r b).toNat + (d3r r b).val := by
  revert r b
  decide

/-- Long division by 3 of an MSB-first bit list: all quotient bits (MSB first), final remainder. -/
def d3full : Fin 3 → List Bool → List Bool × Fin 3
  | r, [] => ([], r)
  | r, b :: l => (d3q r b :: (d3full (d3r r b) l).1, (d3full (d3r r b) l).2)

/-- The machine's emitted quotient bits: leading zeros are suppressed until `started`. -/
def d3run : Fin 3 → Bool → List Bool → List Bool
  | _, _, [] => []
  | r, st, b :: l =>
    if st || d3q r b then d3q r b :: d3run (d3r r b) (st || d3q r b) l
    else d3run (d3r r b) (st || d3q r b) l

theorem d3full_length : ∀ (r : Fin 3) (l : List Bool), (d3full r l).1.length = l.length
  | _, [] => rfl
  | r, b :: l => by simp [d3full, d3full_length (d3r r b) l]

theorem d3run_eq : ∀ (r : Fin 3) (st : Bool) (l : List Bool),
    d3run r st l = if st then (d3full r l).1 else (d3full r l).1.dropWhile (fun b => !b)
  | _, st, [] => by cases st <;> rfl
  | r, st, b :: l => by
    have ih : ∀ st', d3run (d3r r b) st' l =
        if st' then (d3full (d3r r b) l).1 else (d3full (d3r r b) l).1.dropWhile (fun b => !b) :=
      fun st' => d3run_eq (d3r r b) st' l
    cases st <;> cases hq : d3q r b <;> simp [d3run, d3full, hq, ih]

theorem d3full_val : ∀ (r : Fin 3) (l : List Bool),
    r.val * 2 ^ l.length + bitsVal l.reverse =
      3 * bitsVal (d3full r l).1.reverse + (d3full r l).2.val
  | r, [] => by simp [d3full]
  | r, b :: l => by
    have ih := d3full_val (d3r r b) l
    have hid := d3_id r b
    have hlen := d3full_length (d3r r b) l
    simp only [d3full, List.reverse_cons, bitsVal_append, List.length_reverse, hlen,
      List.length_cons, bitsVal_cons, bitsVal_nil]
    linear_combination ih + 2 ^ l.length * hid

/-- **Exact `÷3` result** (floor division; exact under `3 ∣ A`). -/
theorem d3_result (A : ℕ) :
    (d3run 0 false (encodeNat A).reverse).reverse = encodeNat (A / 3) := by
  have hv := d3full_val 0 (encodeNat A).reverse
  have hlt := (d3full 0 (encodeNat A).reverse).2.isLt
  rw [List.reverse_reverse, bitsVal_encodeNat] at hv
  rw [d3run_eq, if_neg Bool.false_ne_true, reverse_dropWhile_eq_encodeNat]
  congr 1
  simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add] at hv
  omega

#assert_std_axioms bitsVal_append normBits_append_true m3_id m3run_val m3run_carry_pos m3_result
  d3_id d3run_eq d3full_val d3_result

end TMFw.W3b
