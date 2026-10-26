import Mathlib.Computability.TMComputable

/-!
# IntMulTM.Framework.Bits — LSB-first bit lists and Mathlib's `encodeNat`

* `bitsVal`, `normBits` : value and normalization (drop high zeros) of LSB-first bit lists;
  `encodeNat_bitsVal : encodeNat (bitsVal l) = normBits l`,
  `bitsVal_encodeNat : bitsVal (encodeNat n) = n`, `normBits_encodeNat`.
* `normBits_eq_reverse_dropWhile` : the MSB-first view used by copy-out.
* `incBits`, `decBits`, `ones`, `zerosLead`, `popcount` : binary counters; `encodeNat_succ`,
  `decBits_encodeNat_succ`, and the amortisation identity `ones_add_popcount_incBits` with the
  sequence bound `incSeqCost_le`.
-/

namespace TMFw

open Computability

/-! ## Value and normalization -/

/-- Value of an LSB-first bit list. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: l => bitsVal l + bitsVal l + b.toNat

/-- Drop high-order zeros (trailing `false`s) of an LSB-first bit list. -/
def normBits : List Bool → List Bool
  | [] => []
  | b :: l => if b = false ∧ normBits l = [] then [] else b :: normBits l

@[simp] theorem bitsVal_nil : bitsVal [] = 0 := rfl

@[simp] theorem bitsVal_cons (b : Bool) (l : List Bool) :
    bitsVal (b :: l) = bitsVal l + bitsVal l + b.toNat := rfl

theorem encodeNum_bit1 (m : Num) : encodeNum m.bit1 = true :: encodeNum m := by
  cases m <;> rfl

theorem encodeNum_bit0 (m : Num) :
    encodeNum m.bit0 = if encodeNum m = [] then [] else false :: encodeNum m := by
  cases m with
  | zero => rfl
  | pos p =>
    show false :: encodePosNum p = if encodePosNum p = [] then [] else false :: encodePosNum p
    rw [if_neg (encodePosNum_nonempty p)]

theorem encodeNat_zero : encodeNat 0 = [] := by
  unfold encodeNat
  rw [Nat.cast_zero]
  rfl

theorem encodeNat_add_add_one (n : ℕ) : encodeNat (n + n + 1) = true :: encodeNat n := by
  unfold encodeNat
  rw [Nat.cast_succ, Nat.cast_add, Num.bit1_of_bit1, encodeNum_bit1]

theorem encodeNat_add (n : ℕ) :
    encodeNat (n + n) = if encodeNat n = [] then [] else false :: encodeNat n := by
  unfold encodeNat
  rw [Nat.cast_add, Num.bit0_of_bit0, encodeNum_bit0]

/-- `encodeNat` is the normalization of any bit list with the same value. -/
theorem encodeNat_bitsVal : ∀ l : List Bool, encodeNat (bitsVal l) = normBits l
  | [] => encodeNat_zero
  | true :: l => by
    show encodeNat (bitsVal l + bitsVal l + 1) = _
    rw [encodeNat_add_add_one, encodeNat_bitsVal l]
    simp [normBits]
  | false :: l => by
    show encodeNat (bitsVal l + bitsVal l + 0) = _
    rw [Nat.add_zero, encodeNat_add, encodeNat_bitsVal l]
    simp [normBits]

theorem bitsVal_encodeNat (n : ℕ) : bitsVal (encodeNat n) = n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [two_mul]
    by_cases hk : k = 0
    · subst hk
      rw [encodeNat_zero]
      rfl
    · have hk' : k < 2 * k := by omega
      have h1 := ih k hk'
      have hne : encodeNat k ≠ [] := by
        intro h
        rw [h] at h1
        exact hk h1.symm
      rw [encodeNat_add, if_neg hne, bitsVal_cons, h1]
      rfl
  · rw [two_mul, encodeNat_add_add_one, bitsVal_cons, ih k (by omega)]
    rfl

theorem normBits_encodeNat (n : ℕ) : normBits (encodeNat n) = encodeNat n := by
  rw [← encodeNat_bitsVal, bitsVal_encodeNat]

theorem encodeNat_eq_nil_iff (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have := bitsVal_encodeNat n
    rw [h] at this
    exact this.symm
  · rintro rfl
    exact encodeNat_zero

/-! ## MSB-first view (copy-out) -/

theorem dropWhile_append_singleton (p : Bool → Bool) :
    ∀ (xs : List Bool) (y : Bool), (xs ++ [y]).dropWhile p =
      if xs.dropWhile p = [] then [y].dropWhile p else xs.dropWhile p ++ [y]
  | [], y => by simp
  | x :: xs, y => by
    by_cases hx : p x = true
    · have e1 : (x :: (xs ++ [y])).dropWhile p = (xs ++ [y]).dropWhile p := by
        simp [hx]
      have e2 : (x :: xs).dropWhile p = xs.dropWhile p := by
        simp [hx]
      rw [List.cons_append, e1, e2]
      exact dropWhile_append_singleton p xs y
    · simp [hx]

/-- Normalization = drop leading zeros of the MSB-first (reversed) list. -/
theorem normBits_eq_reverse_dropWhile :
    ∀ l : List Bool, normBits l = (l.reverse.dropWhile (fun b => !b)).reverse
  | [] => rfl
  | b :: l => by
    rw [List.reverse_cons, dropWhile_append_singleton, normBits, normBits_eq_reverse_dropWhile l]
    by_cases hD : l.reverse.dropWhile (fun b => !b) = []
    · rw [hD, if_pos rfl]
      cases b <;> simp
    · rw [if_neg hD]
      have hD' : (l.reverse.dropWhile (fun b => !b)).reverse ≠ [] := by
        simpa using hD
      rw [if_neg (fun h => hD' h.2), List.reverse_append]
      rfl

/-- The output of copy-out (MSB-first `ds`, high zeros skipped, emitted LSB-first). -/
theorem reverse_dropWhile_eq_encodeNat (ds : List Bool) :
    (ds.dropWhile (fun b => !b)).reverse = encodeNat (bitsVal ds.reverse) := by
  rw [encodeNat_bitsVal, normBits_eq_reverse_dropWhile, List.reverse_reverse]

/-! ## Binary counters -/

/-- Increment (LSB first). -/
def incBits : List Bool → List Bool
  | [] => [true]
  | true :: l => false :: incBits l
  | false :: l => true :: l

/-- Decrement of a normalized nonzero number (LSB first); keeps the result normalized. -/
def decBits : List Bool → List Bool
  | [] => []
  | false :: l => true :: decBits l
  | true :: l => if l = [] then [] else false :: l

/-- Number of leading (= least significant) `1`s. -/
def ones : List Bool → ℕ
  | [] => 0
  | true :: l => ones l + 1
  | false :: _ => 0

/-- Number of leading (= least significant) `0`s. -/
def zerosLead : List Bool → ℕ
  | [] => 0
  | false :: l => zerosLead l + 1
  | true :: _ => 0

/-- Number of `1`s. -/
def popcount : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + popcount l

theorem encodePosNum_succ : ∀ n : PosNum, encodePosNum n.succ = incBits (encodePosNum n)
  | .one => rfl
  | .bit0 _ => rfl
  | .bit1 n => by
    show false :: encodePosNum n.succ = false :: incBits (encodePosNum n)
    rw [encodePosNum_succ n]

theorem encodeNum_succ : ∀ n : Num, encodeNum n.succ = incBits (encodeNum n)
  | .zero => rfl
  | .pos n => encodePosNum_succ n

theorem encodeNat_succ (n : ℕ) : encodeNat (n + 1) = incBits (encodeNat n) := by
  unfold encodeNat
  rw [Nat.cast_succ, Num.add_one, encodeNum_succ]

theorem decBits_incBits_of_norm : ∀ L : List Bool, normBits L = L → decBits (incBits L) = L
  | [], _ => rfl
  | true :: L, h => by
    have h' : normBits L = L := by
      simp only [normBits] at h
      simpa using h
    show true :: decBits (incBits L) = true :: L
    rw [decBits_incBits_of_norm L h']
  | false :: L, h => by
    have hne : L ≠ [] := by
      rintro rfl
      simp [normBits] at h
    show (if L = [] then [] else false :: L) = false :: L
    rw [if_neg hne]

theorem decBits_encodeNat_succ (n : ℕ) : decBits (encodeNat (n + 1)) = encodeNat n := by
  rw [encodeNat_succ, decBits_incBits_of_norm _ (normBits_encodeNat n)]

theorem ones_le_length : ∀ L : List Bool, ones L ≤ L.length
  | [] => Nat.le_refl _
  | true :: L => by
    have := ones_le_length L
    simp only [ones, List.length_cons]
    omega
  | false :: L => by simp [ones]

theorem zerosLead_le_length : ∀ L : List Bool, zerosLead L ≤ L.length
  | [] => Nat.le_refl _
  | false :: L => by
    have := zerosLead_le_length L
    simp only [zerosLead, List.length_cons]
    omega
  | true :: L => by simp [zerosLead]

/-- Amortisation identity: `ones` is paid for by the drop in `popcount`. -/
theorem ones_add_popcount_incBits : ∀ L : List Bool, ones L + popcount (incBits L) = popcount L + 1
  | [] => rfl
  | true :: L => by
    have := ones_add_popcount_incBits L
    simp only [ones, incBits, popcount, Bool.toNat_true, Bool.toNat_false]
    omega
  | false :: L => by
    simp only [ones, incBits, popcount, Bool.toNat_true, Bool.toNat_false]
    omega

/-- Total cost of the increments `0 → 1 → … → m` when one increment of `L` costs
`a * ones L + b`. -/
def incSeqCost (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => incSeqCost a b m + (a * ones (encodeNat m) + b)

theorem incSeqCost_add_popcount_le (a b : ℕ) :
    ∀ m, incSeqCost a b m + a * popcount (encodeNat m) ≤ (a + b) * m
  | 0 => by simp [incSeqCost, encodeNat_zero, popcount]
  | m + 1 => by
    have ih := incSeqCost_add_popcount_le a b m
    have key := ones_add_popcount_incBits (encodeNat m)
    have e : a * ones (encodeNat m) + a * popcount (incBits (encodeNat m)) =
        a * popcount (encodeNat m) + a := by
      rw [← Nat.mul_add, key, Nat.mul_add, Nat.mul_one]
    simp only [incSeqCost, encodeNat_succ, Nat.mul_succ]
    omega

/-- **Amortised increment bound**: `m` increments from `0` cost at most `(a + b) * m`. -/
theorem incSeqCost_le (a b m : ℕ) : incSeqCost a b m ≤ (a + b) * m :=
  le_trans (Nat.le_add_right _ _) (incSeqCost_add_popcount_le a b m)

end TMFw

