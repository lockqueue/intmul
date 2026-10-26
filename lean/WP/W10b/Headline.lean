import WP.W10b.Chain
import WP.W7pure.Headline

/-!
# WP.W10b.Headline — the headline schedule parameters in `n`

`W8.hSpec n = buildQuantizedSpecPaperStop L p0 K0` with `b = hB n`, `k = hK n`, `K0 = hK0 n`,
`L = hL n`, `p0 = hP0 n`; `P n = leafPrecision L p0 K0`. For `n ≥ 2` (so `b = log₂ n ≥ 1`):

| quantity | bound | lemma |
|---|---|---|
| `E = 2^K0` | `E·(log₂ n + 1) ≤ 32n` | `E_mul_le` |
| `k·b` | `≤ n + b` | `hK_mul_hB_le` |
| `L` | `≤ log₂ log₂ n + 2` | `hL_le_loglog` |
| `log₂ P` | `≤ log₂ log₂ n + 8` | `log2_P_le` |

The others (`b ≤ log₂ n + 1`, `K0 ≤ log₂ n + 4`, `P ≤ 22(log₂ n + 1) + 66`, `L + 1 ≤ K0`, `2^K0 ≤ 16(n+1)`)
are W7pure's.
-/

namespace WP.W10b

open TMFw.Contracts TMFw.Contracts.W9 IntMul IntMulTM.Contracts

/-- The leaf precision of the headline schedule (the largest precision on the chain). -/
def hP (n : ℕ) : ℕ := leafPrecision (W8.hL n) (W8.hP0 n) (W8.hK0 n)

theorem one_le_log2 {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Nat.log2 n :=
  (Nat.le_log2 (by omega)).2 (by simpa using hn)

theorem hB_eq {n : ℕ} (hn : 2 ≤ n) : W8.hB n = Nat.log2 n := max_eq_right (one_le_log2 hn)

theorem hK_mul_hB_le (n : ℕ) : W8.hK n * W8.hB n ≤ n + W8.hB n := by
  unfold W8.hK
  have h := Nat.div_mul_le_self n (W8.hB n)
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- **Level size times `log n` is linear.** -/
theorem E_mul_le {n : ℕ} (hn : 2 ≤ n) : 2 ^ W8.hK0 n * (Nat.log2 n + 1) ≤ 32 * n := by
  have hb1 := one_le_log2 hn
  have hbeq := hB_eq hn
  have hbn : Nat.log2 n ≤ n := Nat.log2_le_self n
  have hk := hK_mul_hB_le n
  have hk1 := WP.W7pure.one_le_hK n
  unfold W8.hK0
  rcases le_total 4 (Nat.log2 (2 * W8.hK n) + 2) with h | h
  · rw [max_eq_right h]
    have h1 : 2 ^ Nat.log2 (2 * W8.hK n) ≤ 2 * W8.hK n := Nat.log2_self_le (by omega)
    have e : 2 ^ (Nat.log2 (2 * W8.hK n) + 2) = 4 * 2 ^ Nat.log2 (2 * W8.hK n) := by ring
    rw [e]
    calc 4 * 2 ^ Nat.log2 (2 * W8.hK n) * (Nat.log2 n + 1)
        ≤ 4 * (2 * W8.hK n) * (2 * W8.hB n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 h1) (by omega)
      _ = 16 * (W8.hK n * W8.hB n) := by ring
      _ ≤ 16 * (n + W8.hB n) := Nat.mul_le_mul_left 16 hk
      _ ≤ 32 * n := by omega
  · rw [max_eq_left h]
    have e : (2 : ℕ) ^ 4 = 16 := by norm_num
    rw [e]
    omega

/-- `log₂ (2^j·x) = log₂ x + j` for `x ≠ 0`. -/
theorem log2_two_pow_mul (x : ℕ) (hx : x ≠ 0) : ∀ j, Nat.log2 (2 ^ j * x) = Nat.log2 x + j
  | 0 => by simp
  | j + 1 => by
    have h := log2_two_pow_mul x hx j
    have e : 2 ^ (j + 1) * x = 2 * (2 ^ j * x) := by ring
    rw [e, Nat.log2_two_mul (by positivity), h]
    ring

/-- **Fuel bound.** `L = log₂ (K0 − 1) ≤ log₂ log₂ n + 2`. -/
theorem hL_le_loglog {n : ℕ} (hn : 2 ≤ n) : W8.hL n ≤ Nat.log2 (Nat.log2 n) + 2 := by
  have hb1 := one_le_log2 hn
  have h1 := WP.W7pure.hK0_le n
  have h2 : W8.hK0 n - 1 ≤ 2 ^ 2 * Nat.log2 n := by
    have e : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [e]
    omega
  have h3 : Nat.log2 (W8.hK0 n - 1) ≤ Nat.log2 (2 ^ 2 * Nat.log2 n) := nat_log2_mono h2
  rw [log2_two_pow_mul _ (by omega)] at h3
  exact h3

/-- **Leaf precision.** `log₂ P ≤ log₂ log₂ n + 8`. -/
theorem log2_P_le {n : ℕ} (hn : 2 ≤ n) : Nat.log2 (hP n) ≤ Nat.log2 (Nat.log2 n) + 8 := by
  have hb1 := one_le_log2 hn
  have h1 := WP.W7pure.leafP_le n
  have h2 : hP n ≤ 2 ^ 8 * Nat.log2 n := by
    have e : (2 : ℕ) ^ 8 = 256 := by norm_num
    rw [e]
    unfold hP
    omega
  have h3 := nat_log2_mono h2
  rw [log2_two_pow_mul _ (by omega)] at h3
  exact h3

theorem hP0_le_hP (n : ℕ) : W8.hP0 n ≤ hP n := le_leafPrecision _ _ _

theorem hB_le_hP0 (n : ℕ) : W8.hB n ≤ W8.hP0 n := by
  unfold W8.hP0 rootPrecision
  omega

#assert_std_axioms one_le_log2 hB_eq hK_mul_hB_le E_mul_le log2_two_pow_mul hL_le_loglog log2_P_le
  hP0_le_hP hB_le_hP0

end WP.W10b
