import Contracts.W7.Tables

/-!
# WP.W7k2.Arith — bit-length facts and the quadratic bound on the Toom-3 recurrence

* `bitLen` (the size measure of every machine contract) is characterised by
  `bitLen_le_iff : bitLen n ≤ k ↔ n < 2^k`; from it: monotonicity, `bitLen (2^k) = k + 1`, and the
  bounds for sums, products and shifts used by the kernel cost proofs.
* `bitLen_le_of_fits`: the snapshot's width predicate `FitsSignedScalarWord w z` (what its
  per-call-site width theorems certify) bounds the machine operand size: `bitLen |z| ≤ w`.
* `T3_le_quad`: for all constants, `T3 c0 c1 w0 w ≤ K·(w+1)²`. This discharges the growth premise
  `∃ K, ∀ w, Mul w ≤ K·(w+1)²` of the W7 kernels at `Mul := T3 c0 c1 w0` (via the shared
  `W5_mulAt` interface).
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-! ## `bitLen` -/

theorem bitLen_zero : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem bitLen_double_add_one (k : ℕ) : bitLen (2 * k + 1) = bitLen k + 1 := by
  unfold bitLen
  rw [two_mul, encodeNat_add_add_one]
  rfl

theorem bitLen_double (k : ℕ) (hk : 0 < k) : bitLen (2 * k) = bitLen k + 1 := by
  unfold bitLen
  rw [two_mul, encodeNat_add, if_neg]
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
    rw [Nat.le_zero, bitLen_eq_zero_iff, pow_zero]
    omega
  | k + 1, n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [bitLen_zero]
      exact ⟨fun _ => by positivity, fun _ => by omega⟩
    · rw [bitLen_div2 n hn, Nat.add_le_add_iff_right, bitLen_le_iff k (n / 2), pow_succ]
      omega

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n :=
  (bitLen_le_iff _ n).mp le_rfl

theorem bitLen_le_of_lt {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k :=
  (bitLen_le_iff k n).mpr h

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n :=
  bitLen_le_of_lt (lt_of_le_of_lt h (lt_two_pow_bitLen n))

theorem bitLen_two_pow (k : ℕ) : bitLen (2 ^ k) = k + 1 := by
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have h1 : bitLen (2 ^ k) ≤ k + 1 := bitLen_le_of_lt (by rw [pow_succ]; omega)
  have h2 : ¬ bitLen (2 ^ k) ≤ k := fun h => by
    have := (bitLen_le_iff k (2 ^ k)).mp h
    omega
  omega

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  bitLen_le_of_lt (Nat.lt_two_pow_self)

theorem bitLen_mul_two_pow_le (n k : ℕ) : bitLen (n * 2 ^ k) ≤ bitLen n + k := by
  apply bitLen_le_of_lt
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen n) (by positivity)

theorem bitLen_add_le (m n : ℕ) : bitLen (m + n) ≤ max (bitLen m) (bitLen n) + 1 := by
  apply bitLen_le_of_lt
  have h1 : m < 2 ^ max (bitLen m) (bitLen n) :=
    lt_of_lt_of_le (lt_two_pow_bitLen m) (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have h2 : n < 2 ^ max (bitLen m) (bitLen n) :=
    lt_of_lt_of_le (lt_two_pow_bitLen n) (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  rw [pow_succ]
  omega

theorem bitLen_mul_le (m n : ℕ) : bitLen (m * n) ≤ bitLen m + bitLen n := by
  apply bitLen_le_of_lt
  rw [pow_add]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.mul_lt_mul_of_lt_of_le (lt_two_pow_bitLen m) (lt_two_pow_bitLen n).le
      (pow_pos (by norm_num) _)

/-- The snapshot's signed width predicate bounds the operand's bit length. -/
theorem bitLen_le_of_fits {w : ℕ} {z : ℤ} (h : IntMul.FitsSignedScalarWord w z) :
    bitLen z.natAbs ≤ w := by
  unfold IntMul.FitsSignedScalarWord at h
  have h1 : (z.natAbs : ℤ) < 2 ^ (w - 1) := by rwa [Int.natCast_natAbs]
  have h2 : z.natAbs < 2 ^ (w - 1) := by exact_mod_cast h1
  have h3 : 2 ^ (w - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  exact bitLen_le_of_lt (lt_of_lt_of_le h2 h3)

/-! ## The Toom-3 recurrence is at most quadratic -/

theorem T3_le_quad (c0 c1 w0 : ℕ) : ∃ K, ∀ w, T3 c0 c1 w0 w ≤ K * (w + 1) ^ 2 := by
  refine ⟨max (T3 c0 c1 w0 (30 * c0 + 30)) (5 * c1), fun w => ?_⟩
  set K := max (T3 c0 c1 w0 (30 * c0 + 30)) (5 * c1) with hK
  have hK1 : T3 c0 c1 w0 (30 * c0 + 30) ≤ K := le_max_left _ _
  have hK2 : 5 * c1 ≤ K := le_max_right _ _
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w ≤ 30 * c0 + 30
    · have h1 := T3_mono c0 c1 w0 hw
      have h2 : K ≤ K * (w + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    · rw [T3_unfold]
      split_ifs with h
      · have hv := ih _ h.2
        set v := (w + 2) / 3 + c0 with hv_def
        have hv1 : 5 * (v + 1) ≤ 2 * (w + 1) := by omega
        have hsq : 25 * ((v + 1) * (v + 1)) ≤ 4 * ((w + 1) * (w + 1)) := by
          have := Nat.mul_le_mul hv1 hv1
          nlinarith
        have hw1 : w ≤ (w + 1) * (w + 1) := by nlinarith
        have hcw : 5 * (c1 * w) ≤ K * ((w + 1) * (w + 1)) := by
          calc 5 * (c1 * w) = (5 * c1) * w := by ring
            _ ≤ K * w := Nat.mul_le_mul_right _ hK2
            _ ≤ K * ((w + 1) * (w + 1)) := Nat.mul_le_mul_left _ hw1
        have hKv : 5 * (5 * (K * (v + 1) ^ 2)) ≤ 4 * (K * (w + 1) ^ 2) := by
          have := Nat.mul_le_mul_left K hsq
          nlinarith
        have : 5 * (5 * T3 c0 c1 w0 v + c1 * w) ≤ 5 * (K * (w + 1) ^ 2) := by
          have h5 : 5 * (5 * T3 c0 c1 w0 v) ≤ 5 * (5 * (K * (v + 1) ^ 2)) := by omega
          nlinarith
        omega
      · have h1 := T3_ge_base c0 c1 w0 (30 * c0 + 30)
        have h2 : K ≤ K * (w + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
        omega

#assert_std_axioms bitLen_zero bitLen_double_add_one bitLen_double bitLen_div2 bitLen_eq_zero_iff
  bitLen_le_iff lt_two_pow_bitLen bitLen_le_of_lt bitLen_mono bitLen_two_pow bitLen_le_self
  bitLen_mul_two_pow_le bitLen_add_le bitLen_mul_le bitLen_le_of_fits T3_le_quad

end WP.W7k2
