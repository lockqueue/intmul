import WP.W7pure.Basic

/-!
# WP.W7pure.Headline — the headline schedule parameters in closed form

The headline schedule is `W8.hSpec n = buildQuantizedSpecPaperStop L p0 K0` (CSWS:2264-2269) with
`b = hB n`, `k = hK n`, `K0 = hK0 n`, `L = hL n`, `p0 = hP0 n = 2b + 2K0 + 6`, and leaf precision
`P = leafPrecision L p0 K0`. With `ℓ = log₂ n + 1`, for **every** `n`:

| quantity | bound | lemma |
|---|---|---|
| `b` | `≤ ℓ` | `hB_le` |
| `k` | `≤ n + 1` | `hK_le` |
| `K0` | `4 ≤ K0 ≤ ℓ + 3` | `four_le_hK0`, `hK0_le` |
| `2^K0` | `≤ 16(n+1)` | `two_pow_hK0_le` |
| `2^(K0/2)` | `≤ 4(√n+1)` | `two_pow_half_hK0_le` |
| `2^(K0 − K0/2)` | `≤ 8(√n+1)` | `two_pow_ceil_half_hK0_le` |
| `L` | `L + 1 ≤ K0` | `hL_succ_le` |
| `P` | `≤ 22ℓ + 66` | `leafP_le` (from `leafPrecision_le`) |

`√` is `Nat.sqrt` (floor).
-/

namespace WP.W7pure

open IntMul

theorem hB_le (n : ℕ) : IntMulTM.Contracts.W8.hB n ≤ Nat.log2 n + 1 := by
  unfold IntMulTM.Contracts.W8.hB
  exact max_le (by omega) (by omega)

theorem four_le_hK0 (n : ℕ) : 4 ≤ IntMulTM.Contracts.W8.hK0 n :=
  le_max_left 4 (Nat.log2 (2 * IntMulTM.Contracts.W8.hK n) + 2)

theorem hK_le (n : ℕ) : IntMulTM.Contracts.W8.hK n ≤ n + 1 := by
  unfold IntMulTM.Contracts.W8.hK
  have h := Nat.div_le_self n (IntMulTM.Contracts.W8.hB n)
  omega

theorem one_le_hK (n : ℕ) : 1 ≤ IntMulTM.Contracts.W8.hK n :=
  Nat.le_add_left 1 _

theorem hK0_le (n : ℕ) : IntMulTM.Contracts.W8.hK0 n ≤ Nat.log2 n + 4 := by
  have hk := hK_le n
  have hk1 := one_le_hK n
  have hn := lt_two_pow_log2_succ n
  have e : 2 ^ (Nat.log2 n + 3) = 4 * 2 ^ (Nat.log2 n + 1) := by ring
  have h2k : 2 * IntMulTM.Contracts.W8.hK n < 2 ^ (Nat.log2 n + 3) := by omega
  have hlog := (Nat.log2_lt (by omega : 2 * IntMulTM.Contracts.W8.hK n ≠ 0)).2 h2k
  unfold IntMulTM.Contracts.W8.hK0
  exact max_le (by omega) (by omega)

theorem two_pow_hK0_le (n : ℕ) : 2 ^ IntMulTM.Contracts.W8.hK0 n ≤ 16 * (n + 1) := by
  have hk := hK_le n
  have hk1 := one_le_hK n
  unfold IntMulTM.Contracts.W8.hK0
  rcases le_total 4 (Nat.log2 (2 * IntMulTM.Contracts.W8.hK n) + 2) with h | h
  · rw [max_eq_right h]
    have h1 : 2 ^ Nat.log2 (2 * IntMulTM.Contracts.W8.hK n) ≤ 2 * IntMulTM.Contracts.W8.hK n :=
      Nat.log2_self_le (by omega)
    have e : 2 ^ (Nat.log2 (2 * IntMulTM.Contracts.W8.hK n) + 2) =
        4 * 2 ^ Nat.log2 (2 * IntMulTM.Contracts.W8.hK n) := by ring
    omega
  · rw [max_eq_left h]
    calc 2 ^ 4 = 16 := by norm_num
      _ ≤ 16 * (n + 1) := by omega

theorem two_pow_half_hK0_le (n : ℕ) :
    2 ^ (IntMulTM.Contracts.W8.hK0 n / 2) ≤ 4 * (Nat.sqrt n + 1) := by
  have h1 : (2 ^ (IntMulTM.Contracts.W8.hK0 n / 2)) ^ 2 ≤ 2 ^ IntMulTM.Contracts.W8.hK0 n := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : n + 1 ≤ (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have h4 : (2 ^ (IntMulTM.Contracts.W8.hK0 n / 2)) ^ 2 ≤ (4 * (Nat.sqrt n + 1)) ^ 2 :=
    calc (2 ^ (IntMulTM.Contracts.W8.hK0 n / 2)) ^ 2 ≤ 2 ^ IntMulTM.Contracts.W8.hK0 n := h1
      _ ≤ 16 * (n + 1) := two_pow_hK0_le n
      _ ≤ 16 * (Nat.sqrt n + 1) ^ 2 := Nat.mul_le_mul_left 16 h3
      _ = (4 * (Nat.sqrt n + 1)) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide)).1 h4

theorem two_pow_ceil_half_le (K : ℕ) : 2 ^ (K - K / 2) ≤ 2 * 2 ^ (K / 2) :=
  calc 2 ^ (K - K / 2) ≤ 2 ^ (K / 2 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 * 2 ^ (K / 2) := by ring

theorem two_pow_ceil_half_hK0_le (n : ℕ) :
    2 ^ (IntMulTM.Contracts.W8.hK0 n - IntMulTM.Contracts.W8.hK0 n / 2) ≤
      8 * (Nat.sqrt n + 1) := by
  have h1 := two_pow_ceil_half_le (IntMulTM.Contracts.W8.hK0 n)
  have h2 := two_pow_half_hK0_le n
  omega

theorem hL_succ_le (n : ℕ) : IntMulTM.Contracts.W8.hL n + 1 ≤ IntMulTM.Contracts.W8.hK0 n := by
  have h4 := four_le_hK0 n
  have h1 := Nat.log2_le_self (IntMulTM.Contracts.W8.hK0 n - 1)
  unfold IntMulTM.Contracts.W8.hL
  omega

theorem leafP_le (n : ℕ) :
    leafPrecision (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n)
      (IntMulTM.Contracts.W8.hK0 n) ≤ 22 * (Nat.log2 n + 1) + 66 := by
  have h1 := leafPrecision_le (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n)
    (IntMulTM.Contracts.W8.hK0 n)
  have h2 : IntMulTM.Contracts.W8.hP0 n =
      2 * IntMulTM.Contracts.W8.hB n + 2 * IntMulTM.Contracts.W8.hK0 n + 6 := rfl
  have h3 := hB_le n
  have h4 := hK0_le n
  have h5 := hL_succ_le n
  omega

#assert_std_axioms hB_le four_le_hK0 hK_le one_le_hK hK0_le two_pow_hK0_le two_pow_half_hK0_le
  two_pow_ceil_half_le two_pow_ceil_half_hK0_le hL_succ_le leafP_le

end WP.W7pure
