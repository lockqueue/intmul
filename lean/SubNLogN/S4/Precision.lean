import SubNLogN.Spec

/-!
# Component S4 (`Precision.lean`): Master Precision Margin, Bridge Error `< 0.177021` & Root Recovery

**Scope.** Proves the four closed-form `ℕ` exponent and rational-enclosure inequalities accompanying Theorem 4.7 (`thm:bridge-precision`) and Proposition 7.2 (`prop:root-packing`); full analytical and `TM2` proofs live in `SubNLogN/{Math/Bridge,Machine/Bridge,Machine/Tables,Assembly}/`.
-/

namespace SubNLogN.S4

open SubNLogN

/-- **Master Precision Margin (`eq:master-margin`, Theorem 4.7 (`thm:bridge-precision`)):**
For all `p ≥ 8`, `k ≥ 1`, `1 ≤ d ≤ k`, and `lg_pk2 ≥ 1` with
`bridgeWorkingP p k lg_pk2 + 1 ≤ 2 ^ (lg_pk2 + 6)`,
`2^14 * d * (P + 1) * (2^k)^3 * 2^{p + 12} ≤ 2^q` where `q = bridgeGridQ p k lg_pk2`. -/
theorem bridge_master_margin (p k d lg_pk2 : ℕ)
    (hp : 8 ≤ p) (hk : 1 ≤ k) (hd1 : 1 ≤ d) (hdk : d ≤ k) (hlg : 1 ≤ lg_pk2)
    (hP : bridgeWorkingP p k lg_pk2 + 1 ≤ 2 ^ (lg_pk2 + 6)) :
    (2 ^ 14) * d * (bridgeWorkingP p k lg_pk2 + 1) * (2 ^ (3 * k)) * (2 ^ (p + 12)) ≤
      2 ^ (bridgeGridQ p k lg_pk2) := by
  have _ := hd1
  have hd2k : d ≤ 2 ^ k := le_trans hdk (Nat.le_of_lt Nat.lt_two_pow_self)
  have h1 : (2 ^ 14) * d * (bridgeWorkingP p k lg_pk2 + 1) * (2 ^ (3 * k)) * (2 ^ (p + 12)) ≤
      (2 ^ 14) * (2 ^ k) * (2 ^ (lg_pk2 + 6)) * (2 ^ (3 * k)) * (2 ^ (p + 12)) :=
    Nat.mul_le_mul_right (2 ^ (p + 12))
      (Nat.mul_le_mul_right (2 ^ (3 * k))
        (Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 14) hd2k) hP))
  have h2 : (2 ^ 14) * (2 ^ k) * (2 ^ (lg_pk2 + 6)) * (2 ^ (3 * k)) * (2 ^ (p + 12)) =
      2 ^ (14 + k + (lg_pk2 + 6) + 3 * k + (p + 12)) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  have h3 : 2 ^ (14 + k + (lg_pk2 + 6) + 3 * k + (p + 12)) ≤ 2 ^ (bridgeGridQ p k lg_pk2) := by
    apply Nat.pow_le_pow_right (by decide)
    unfold bridgeGridQ bridgeWorkingP
    omega
  exact le_trans h1 (le_of_eq_of_le h2 h3)

/-- Rational upper enclosure for `√2`: `2 < (1.4142136)^2`. -/
theorem sqrt2_upper_enclosure :
    2 * (10000000 : ℕ) ^ 2 < (14142136 : ℕ) ^ 2 := by decide

/-- **Total Bridge Error Coefficient (`eq:bridge-total`, Theorem 4.7 (`thm:bridge-precision`)):**
`1.4142136 / 8 + 2^{-12} + 2^{-23} < 0.177021`. -/
theorem bridge_total_error_lt_0177021 :
    (14142136 : ℕ) * (2 ^ 20) + (10000000 : ℕ) * (2 ^ 11 + 1) <
      (177021 : ℕ) * 10 * (2 ^ 23) := by decide

/-- **Two-Call Root Multiplication Recovery (Proposition 7.2 (`prop:root-packing`)):**
The accumulated pre-rounding error across both bridge calls and intermediate squaring is
`< 1.2391 · 2^{-p}`, and after scaling by `2^{2b + 2k - 1} = 2^{p - 7}` is
`< 1.2391 / 128 < 1 / 2`, so nearest-integer rounding recovers every convolution coefficient
`∑_{a+b'=j} α_a β_{b'}` exactly. -/
theorem two_call_root_recovery_lt_half :
    (12391 : ℕ) * 2 < 10000 * 128 := by decide

end SubNLogN.S4
