import WP.W9g.Macros

/-!
# WP.W9g.Arith — bit lengths and the rounding shift

* `bitLen` facts (characterisation `bitLen_le_iff`, sums, products, shifts, `bitLen (2^k)`), in the
  style of W7k2's Arith, proved without Mathlib-only tactics.
* `drp x s`: a verbatim copy of the snapshot's `divRoundPow2` (ComputablePrimitives:17); the bridge
  module proves `drp = IntMul.divRoundPow2` by `rfl`.
* Floor division by `2^k` on sign-magnitude numbers: `fdiv_nonneg`, `fdiv_neg`.
-/

namespace WP.W9g

open TMFw TMFw.Contracts Computability

/-! ## `bitLen` -/

theorem bitLen_zero' : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem bitLen_double_add_one (k : ℕ) : bitLen (2 * k + 1) = bitLen k + 1 := by
  unfold bitLen
  rw [Nat.two_mul, encodeNat_add_add_one]
  rfl

theorem bitLen_double (k : ℕ) (hk : 0 < k) : bitLen (2 * k) = bitLen k + 1 := by
  unfold bitLen
  rw [Nat.two_mul, encodeNat_add, if_neg]
  · rfl
  · rw [encodeNat_eq_nil_iff]
    omega

theorem bitLen_div2 (n : ℕ) (h : 0 < n) : bitLen n = bitLen (n / 2) + 1 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [bitLen_double k (by omega)]
    congr 2
    omega
  · rw [bitLen_double_add_one]
    congr 2
    omega

theorem bitLen_eq_zero_iff (n : ℕ) : bitLen n = 0 ↔ n = 0 := by
  unfold bitLen
  rw [List.length_eq_zero_iff, encodeNat_eq_nil_iff]

/-- **Characterisation of `bitLen`.** -/
theorem bitLen_le_iff : ∀ (k n : ℕ), bitLen n ≤ k ↔ n < 2 ^ k
  | 0, n => by
    rw [Nat.le_zero, bitLen_eq_zero_iff, Nat.pow_zero]
    omega
  | k + 1, n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [bitLen_zero']
      exact ⟨fun _ => Nat.two_pow_pos _, fun _ => by omega⟩
    · rw [bitLen_div2 n hn, Nat.add_le_add_iff_right, bitLen_le_iff k (n / 2), Nat.pow_succ]
      omega

theorem lt_two_pow_bitLen' (n : ℕ) : n < 2 ^ bitLen n :=
  (bitLen_le_iff _ n).mp le_rfl

theorem bitLen_le_of_lt {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k :=
  (bitLen_le_iff k n).mpr h

theorem bitLen_mono' {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n :=
  bitLen_le_of_lt (Nat.lt_of_le_of_lt h (lt_two_pow_bitLen' n))

theorem bitLen_two_pow (k : ℕ) : bitLen (2 ^ k) = k + 1 := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h1 : bitLen (2 ^ k) ≤ k + 1 := bitLen_le_of_lt (by rw [Nat.pow_succ]; omega)
  have h2 : ¬ bitLen (2 ^ k) ≤ k := fun h => by
    have := (bitLen_le_iff k (2 ^ k)).mp h
    omega
  omega

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  bitLen_le_of_lt Nat.lt_two_pow_self

theorem bitLen_add_le (m n : ℕ) : bitLen (m + n) ≤ max (bitLen m) (bitLen n) + 1 := by
  apply bitLen_le_of_lt
  have h1 : m < 2 ^ max (bitLen m) (bitLen n) :=
    Nat.lt_of_lt_of_le (lt_two_pow_bitLen' m) (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have h2 : n < 2 ^ max (bitLen m) (bitLen n) :=
    Nat.lt_of_lt_of_le (lt_two_pow_bitLen' n) (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  rw [Nat.pow_succ]
  omega

theorem bitLen_mul_le (m n : ℕ) : bitLen (m * n) ≤ bitLen m + bitLen n := by
  apply bitLen_le_of_lt
  rw [Nat.pow_add]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.mul_lt_mul_of_lt_of_le (lt_two_pow_bitLen' m) (lt_two_pow_bitLen' n).le
      (Nat.two_pow_pos _)

theorem bitLen_mul_two_pow_le (n k : ℕ) : bitLen (n * 2 ^ k) ≤ bitLen n + k := by
  apply bitLen_le_of_lt
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen' n) (Nat.two_pow_pos k)

theorem bitLen_div_le (n d : ℕ) : bitLen (n / d) ≤ bitLen n := bitLen_mono' (Nat.div_le_self n d)

theorem bitLen_sub_le (n d : ℕ) : bitLen (n - d) ≤ bitLen n := bitLen_mono' (Nat.sub_le n d)

/-! ## Signed sizes -/

theorem bitLen_natAbs_add (a b : ℤ) :
    bitLen (a + b).natAbs ≤ max (bitLen a.natAbs) (bitLen b.natAbs) + 1 :=
  le_trans (bitLen_mono' (Int.natAbs_add_le a b)) (bitLen_add_le _ _)

theorem bitLen_natAbs_sub (a b : ℤ) :
    bitLen (a - b).natAbs ≤ max (bitLen a.natAbs) (bitLen b.natAbs) + 1 := by
  have h := bitLen_natAbs_add a (-b)
  rwa [Int.natAbs_neg, ← Int.sub_eq_add_neg] at h

theorem bitLen_natAbs_mul (a b : ℤ) :
    bitLen (a * b).natAbs ≤ bitLen a.natAbs + bitLen b.natAbs := by
  rw [Int.natAbs_mul]
  exact bitLen_mul_le _ _

/-! ## Encodings -/

theorem natSyms_one : natSyms 1 = [Sym.bit true] := by
  show (encodeNat (0 + 1)).map Sym.bit = _
  rw [encodeNat_succ, encodeNat_zero]
  rfl

theorem intSyms_of_nonneg {z : ℤ} (hz : 0 ≤ z) : intSyms z = Sym.pos :: natSyms z.natAbs := by
  unfold intSyms sgnSym
  rw [if_neg (by omega)]

theorem intSyms_of_neg {z : ℤ} (hz : z < 0) : intSyms z = Sym.neg :: natSyms z.natAbs := by
  unfold intSyms sgnSym
  rw [if_pos hz]

theorem intSyms_negSucc (n : ℕ) : intSyms (-((n + 1 : ℕ) : ℤ)) = Sym.neg :: natSyms (n + 1) := by
  rw [intSyms_of_neg (by omega)]
  rfl

/-! ## Rounding shift (verbatim snapshot definition) and floor division -/

/-- Verbatim copy of the snapshot's `divRoundPow2` (ComputablePrimitives:17). -/
def drp (x : ℤ) (s : ℕ) : ℤ :=
  if s = 0 then x else (x + ((2 ^ (s - 1) : ℕ) : ℤ)) / ((2 ^ s : ℕ) : ℤ)

/-- Floor division of a non-negative number by `2^k` is the natural division of its magnitude. -/
theorem fdiv_nonneg {y : ℤ} (hy : 0 ≤ y) (k : ℕ) :
    y / ((2 ^ k : ℕ) : ℤ) = ((y.natAbs / 2 ^ k : ℕ) : ℤ) := by
  have h : y = ((y.natAbs : ℕ) : ℤ) := by omega
  rw [Int.natCast_ediv, ← h]

/-- Floor division of a negative number by `2^k`: `-(((|y| - 1) / 2^k) + 1)`. -/
theorem fdiv_neg {y : ℤ} (hy : y < 0) (k : ℕ) :
    y / ((2 ^ k : ℕ) : ℤ) = -((((y.natAbs - 1) / 2 ^ k + 1 : ℕ)) : ℤ) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, y = Int.negSucc a := ⟨y.natAbs - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 2 ^ k = b + 1 := ⟨2 ^ k - 1, by have := Nat.two_pow_pos k; omega⟩
  subst ha
  rw [hb]
  have e : Int.negSucc a / ((b + 1 : ℕ) : ℤ) = Int.negSucc (a / (b + 1)) :=
    Int.negSucc_ediv_ofNat_succ
  rw [e, Int.negSucc_eq]
  have h1 : (Int.negSucc a).natAbs - 1 = a := by simp
  rw [h1]
  push_cast
  omega

theorem natAbs_fdiv_le (y : ℤ) (k : ℕ) : (y / ((2 ^ k : ℕ) : ℤ)).natAbs ≤ y.natAbs := by
  rcases Int.lt_or_le y 0 with hy | hy
  · rw [fdiv_neg hy k, Int.natAbs_neg]
    show (y.natAbs - 1) / 2 ^ k + 1 ≤ y.natAbs
    have h1 : (y.natAbs - 1) / 2 ^ k ≤ y.natAbs - 1 := Nat.div_le_self _ _
    have h2 : 1 ≤ y.natAbs := by omega
    omega
  · rw [fdiv_nonneg hy k]
    show y.natAbs / 2 ^ k ≤ y.natAbs
    exact Nat.div_le_self y.natAbs (2 ^ k)

#assert_std_axioms bitLen_zero' bitLen_double_add_one bitLen_double bitLen_div2 bitLen_eq_zero_iff
  bitLen_le_iff lt_two_pow_bitLen' bitLen_le_of_lt bitLen_mono' bitLen_two_pow bitLen_le_self
  bitLen_add_le bitLen_mul_le bitLen_mul_two_pow_le bitLen_div_le bitLen_sub_le bitLen_natAbs_add
  bitLen_natAbs_sub bitLen_natAbs_mul natSyms_one intSyms_of_nonneg intSyms_of_neg intSyms_negSucc
  fdiv_nonneg fdiv_neg natAbs_fdiv_le

end WP.W9g
