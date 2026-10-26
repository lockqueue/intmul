import Contracts.Machine.W3
import Mathlib.Tactic.Ring

/-!
# WP.W3s.Math — bit-list facts for shifts, split and concatenation

* `bitLen` facts (`bitLen_le_iff`, `bitLen_mono`; the first block is copied from `WP.W5.Arith`).
* `bitsVal_split : bitsVal L = bitsVal (take k L) + 2^k · bitsVal (drop k L)`, hence
  `encodeNat_div_two_pow : encodeNat (a / 2^k) = drop k (encodeNat a)` and `low_part`: the low part
  `a % 2^c` is what the split program emits (high zeros of `take c (encodeNat a)` dropped, MSB-first).
* `encodeNat_concat : hi ≠ 0 → lo < 2^c →
  encodeNat (lo + hi·2^c) = encodeNat lo ++ (replicate (c - |lo|) false ++ encodeNat hi)`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Bit lengths -/

theorem bitLen_zero : bitLen 0 = 0 := by simp [bitLen, encodeNat_zero]

theorem encodeNat_pos (n : ℕ) (hn : 0 < n) :
    encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2) := by
  obtain ⟨q, h | h⟩ := Nat.even_or_odd' n
  · subst h
    have hq : 0 < q := by omega
    have hne : encodeNat q ≠ [] := by rw [Ne, encodeNat_eq_nil_iff]; omega
    have h2 : 2 * q / 2 = q := by omega
    rw [two_mul, encodeNat_add, if_neg hne, ← two_mul, h2]
    simp
  · subst h
    have h1 : (2 * q + 1) % 2 = 1 := by omega
    have h2 : (2 * q + 1) / 2 = q := by omega
    rw [two_mul, encodeNat_add_add_one, ← two_mul, h2, h1]
    simp

theorem bitLen_pos (n : ℕ) (hn : 0 < n) : bitLen n = bitLen (n / 2) + 1 := by
  simp only [bitLen, encodeNat_pos n hn, List.length_cons]

theorem bitLen_le_iff : ∀ (m n : ℕ), bitLen n ≤ m ↔ n < 2 ^ m := by
  intro m
  induction m with
  | zero =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bitLen_zero]
    · rw [bitLen_pos n hn, pow_zero]
      constructor <;> intro h <;> omega
  | succ m ih =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bitLen_zero]
    · rw [bitLen_pos n hn, Nat.add_le_add_iff_right, ih, pow_succ]
      omega

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := (bitLen_le_iff _ n).1 le_rfl

theorem bitLen_le_of_lt {n m : ℕ} (h : n < 2 ^ m) : bitLen n ≤ m := (bitLen_le_iff m n).2 h

theorem bitLen_mono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b :=
  bitLen_le_of_lt (lt_of_le_of_lt h (lt_two_pow_bitLen b))

theorem bitLen_mod_le (a c : ℕ) : bitLen (a % 2 ^ c) ≤ min c (bitLen a) :=
  le_min (bitLen_le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos c))) (bitLen_mono (Nat.mod_le a _))

/-! ## Values of appended lists, `take` and `drop` -/

theorem bitsVal_append : ∀ (l₁ l₂ : List Bool),
    bitsVal (l₁ ++ l₂) = bitsVal l₁ + 2 ^ l₁.length * bitsVal l₂
  | [], l₂ => by simp
  | b :: l₁, l₂ => by
    rw [List.cons_append, bitsVal_cons, bitsVal_cons, bitsVal_append l₁ l₂, List.length_cons,
      pow_succ]
    ring

theorem bitsVal_replicate_false : ∀ n : ℕ, bitsVal (List.replicate n false) = 0
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, bitsVal_cons, bitsVal_replicate_false n]
    rfl

theorem bitsVal_split (k : ℕ) (L : List Bool) :
    bitsVal L = bitsVal (L.take k) + 2 ^ k * bitsVal (L.drop k) := by
  by_cases hk : k ≤ L.length
  · have h := bitsVal_append (L.take k) (L.drop k)
    rw [List.take_append_drop, List.length_take_of_le hk] at h
    exact h
  · rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega)]
    simp

theorem bitsVal_take_lt (k : ℕ) (L : List Bool) : bitsVal (L.take k) < 2 ^ k :=
  lt_of_lt_of_le (bitsVal_lt_two_pow _)
    (Nat.pow_le_pow_right (by omega) (List.length_take_le _ _))

theorem bitsVal_div_two_pow (k : ℕ) (L : List Bool) :
    bitsVal L / 2 ^ k = bitsVal (L.drop k) := by
  rw [bitsVal_split k L, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
    Nat.div_eq_of_lt (bitsVal_take_lt k L), Nat.zero_add]

theorem bitsVal_mod_two_pow (k : ℕ) (L : List Bool) :
    bitsVal L % 2 ^ k = bitsVal (L.take k) := by
  rw [bitsVal_split k L, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bitsVal_take_lt k L)]

/-! ## Normal forms -/

theorem normBits_of_cons {b : Bool} {l : List Bool} (h : normBits (b :: l) = b :: l) :
    normBits l = l := by
  simp only [normBits] at h
  by_cases hc : b = false ∧ normBits l = []
  · rw [if_pos hc] at h
    exact absurd h.symm (List.cons_ne_nil b l)
  · rw [if_neg hc] at h
    exact (List.cons.inj h).2

theorem normBits_drop : ∀ (k : ℕ) (l : List Bool), normBits l = l → normBits (l.drop k) = l.drop k
  | 0, _, h => h
  | _ + 1, [], _ => rfl
  | k + 1, _ :: l, h => normBits_drop k l (normBits_of_cons h)

theorem normBits_append (A B : List Bool) (hB : normBits B = B) (hne : B ≠ []) :
    normBits (A ++ B) = A ++ B := by
  induction A with
  | nil => simpa using hB
  | cons x A ih =>
    rw [List.cons_append]
    simp only [normBits]
    rw [ih, if_neg]
    rintro ⟨-, h⟩
    simp_all

theorem dropRun_false_eq_dropWhile :
    ∀ l : List Bool, dropRun false l = l.dropWhile (fun b => !b)
  | [] => rfl
  | false :: l => by simp [dropRun, dropRun_false_eq_dropWhile l]
  | true :: l => by simp [dropRun]

/-- `x ↦ x / 2^k` drops the `k` low bits. -/
theorem encodeNat_div_two_pow (a k : ℕ) : encodeNat (a / 2 ^ k) = (encodeNat a).drop k := by
  conv_lhs => rw [← bitsVal_encodeNat a]
  rw [bitsVal_div_two_pow, encodeNat_bitsVal, normBits_drop k _ (normBits_encodeNat a)]

/-- The split program's low part: the `c` low bits, MSB-first, high zeros dropped, reversed back. -/
theorem low_part (a c : ℕ) :
    (dropRun false ((encodeNat a).take c).reverse).reverse = encodeNat (a % 2 ^ c) := by
  rw [dropRun_false_eq_dropWhile, reverse_dropWhile_eq_encodeNat, List.reverse_reverse,
    ← bitsVal_mod_two_pow, bitsVal_encodeNat]

/-- Concatenation: `lo` padded to `c` bits, then `hi` (for `hi ≠ 0`). -/
theorem encodeNat_concat (lo hi c : ℕ) (hhi : hi ≠ 0) (hlo : lo < 2 ^ c) :
    encodeNat (lo + hi * 2 ^ c) =
      encodeNat lo ++ (List.replicate (c - bitLen lo) false ++ encodeNat hi) := by
  have hlen : bitLen lo ≤ c := bitLen_le_of_lt hlo
  have hne : encodeNat hi ≠ [] := by rw [Ne, encodeNat_eq_nil_iff]; exact hhi
  have hval : bitsVal (encodeNat lo ++ (List.replicate (c - bitLen lo) false ++ encodeNat hi)) =
      lo + hi * 2 ^ c := by
    rw [bitsVal_append, bitsVal_append, bitsVal_encodeNat, bitsVal_encodeNat,
      bitsVal_replicate_false, List.length_replicate]
    have hp : 2 ^ c = 2 ^ (encodeNat lo).length * 2 ^ (c - bitLen lo) := by
      rw [← pow_add]
      congr 1
      simp only [bitLen] at hlen ⊢
      omega
    rw [hp]
    ring
  have hn1 : normBits (List.replicate (c - bitLen lo) false ++ encodeNat hi) =
      List.replicate (c - bitLen lo) false ++ encodeNat hi :=
    normBits_append _ _ (normBits_encodeNat hi) hne
  have hn2 : List.replicate (c - bitLen lo) false ++ encodeNat hi ≠ [] := by simp [hne]
  rw [← hval, encodeNat_bitsVal, normBits_append _ _ hn1 hn2]

#assert_std_axioms bitLen_le_iff bitLen_mono bitLen_mod_le bitsVal_split encodeNat_div_two_pow
  low_part encodeNat_concat

end TMFw.W3s
