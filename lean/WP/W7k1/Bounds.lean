import WP.W7k1.Canon
import WP.W7k1.IsqrtSpec

/-!
# WP.W7k1.Bounds — value and width bounds for the `π` and `ln 2` machine forms

The cost proofs of `W7_piScaled` and `W7_log2Scaled` charge every operation at the bit lengths of
its operands. This module bounds every intermediate value of `piNat` and `log2Nat`
(`WP.W7k1.Canon`):

| value | bound | width |
|---|---|---|
| `π`: `A_k = piIter S k` | `≤ 2^(S+1)` (`piIter_le`) | `≤ S+2` |
| `π`: isqrt argument `(A_k + 2^(S+1))·2^S` | `≤ 2^(2S+2)` | `≤ 2S+3` |
| `π`: final argument `(2^(S+1) − A)·2^S` | `≤ 2^(2S+1)` | `≤ 2S+2` |
| `π`: `d = piD B` | `≤ 2^(S+1)` | `≤ S+2` |
| `ln 2`: `a_k` | `≤ 2^(3B+11)` (non-increasing) | `≤ 3B+12` |
| `ln 2`: `s_k` | `≤ k·2^(3B+11)` | |

with `S = 4B+20`. `bitLen_le_of_lt` turns a value bound into a width bound.
-/

namespace WP.W7k1

open TMFw TMFw.Contracts Computability

/-! ## Bit lengths -/

theorem bitLen_le_of_lt {x k : ℕ} (h : x < 2 ^ k) : bitLen x ≤ k :=
  length_encodeNat_le k x h

theorem bitLen_le_of_le_pow {x k : ℕ} (h : x ≤ 2 ^ k) : bitLen x ≤ k + 1 :=
  bitLen_le_of_lt (lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)))

theorem lt_two_pow_bitLen (x : ℕ) : x < 2 ^ bitLen x := by
  have h := bitsVal_lt (encodeNat x)
  rwa [bitsVal_encodeNat] at h

theorem bitLen_mono {x y : ℕ} (h : x ≤ y) : bitLen x ≤ bitLen y :=
  bitLen_le_of_lt (lt_of_le_of_lt h (lt_two_pow_bitLen y))

/-! ## `π` -/

theorem piArg_le (S A : ℕ) (hA : A ≤ 2 ^ (S + 1)) :
    (A + 2 ^ (S + 1)) * 2 ^ S ≤ 2 ^ (2 * S + 2) := by
  calc (A + 2 ^ (S + 1)) * 2 ^ S ≤ (2 ^ (S + 1) + 2 ^ (S + 1)) * 2 ^ S :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (2 * S + 2) := by ring

theorem piIter_succ_arg_le (S k : ℕ) :
    (piIter S k + 2 ^ (S + 1)) * 2 ^ S ≤ 2 ^ (2 * S + 2) :=
  piArg_le S _ (piIter_le S k)

theorem piFinalArg_le (S A : ℕ) : (2 ^ (S + 1) - A) * 2 ^ S ≤ 2 ^ (2 * S + 1) := by
  calc (2 ^ (S + 1) - A) * 2 ^ S ≤ 2 ^ (S + 1) * 2 ^ S := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = 2 ^ (2 * S + 1) := by ring

theorem sqrt_le_of_le_pow {x S : ℕ} (h : x ≤ 2 ^ (2 * S + 2)) : Nat.sqrt x ≤ 2 ^ (S + 1) := by
  calc Nat.sqrt x ≤ Nat.sqrt (2 ^ (S + 1) * 2 ^ (S + 1)) :=
        Nat.sqrt_le_sqrt (by rw [← pow_add]; rw [show S + 1 + (S + 1) = 2 * S + 2 by ring]; exact h)
    _ = 2 ^ (S + 1) := Nat.sqrt_eq _

theorem piD_le (B : ℕ) : piD B ≤ 2 ^ (4 * B + 20 + 1) := by
  unfold piD
  refine sqrt_le_of_le_pow (le_trans (piFinalArg_le _ _) ?_)
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Widths of the `π` loop: operands of at most `2S+3` bits. -/
theorem piWidths (B k : ℕ) :
    bitLen (piIter (4 * B + 20) k) ≤ 4 * B + 22 ∧
    bitLen ((piIter (4 * B + 20) k + 2 ^ (4 * B + 20 + 1)) * 2 ^ (4 * B + 20)) ≤ 8 * B + 43 ∧
    bitLen ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) k) * 2 ^ (4 * B + 20)) ≤ 8 * B + 42 ∧
    bitLen (piD B) ≤ 4 * B + 22 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bitLen_le_of_le_pow (piIter_le _ k)
  · have := bitLen_le_of_le_pow (piIter_succ_arg_le (4 * B + 20) k)
    omega
  · have := bitLen_le_of_le_pow (piFinalArg_le (4 * B + 20) (piIter (4 * B + 20) k))
    omega
  · exact bitLen_le_of_le_pow (piD_le B)

/-! ## `ln 2` -/

theorem lnNatIter_a_le (B : ℕ) : ∀ k, (lnNatIter B k).1 ≤ 2 ^ (3 * B + 11)
  | 0 => le_refl _
  | k + 1 => by
    have ih := lnNatIter_a_le B k
    show ((lnNatIter B k).1 * (k + 1) + (k + 2)) / (2 * (k + 2)) ≤ _
    refine le_trans ?_ ih
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : (lnNatIter B k).1 * (k + 1) ≤ (lnNatIter B k).1 * (2 * (k + 2)) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : ((lnNatIter B k).1 + 1) * (2 * (k + 2)) =
        (lnNatIter B k).1 * (2 * (k + 2)) + 2 * (k + 2) := by ring
    rw [Nat.succ_eq_add_one, e]
    omega

theorem lnNatIter_s_le (B : ℕ) : ∀ k, (lnNatIter B k).2 ≤ k * 2 ^ (3 * B + 11)
  | 0 => by simp [lnNatIter]
  | k + 1 => by
    have ih := lnNatIter_s_le B k
    have ha := lnNatIter_a_le B k
    show (lnNatIter B k).2 + (lnNatIter B k).1 ≤ (k + 1) * 2 ^ (3 * B + 11)
    rw [Nat.succ_mul]
    omega

/-- Widths of the `ln 2` loop (`k ≤ B+2` steps). -/
theorem lnWidths (B k : ℕ) (hk : k ≤ B + 2) :
    bitLen (lnNatIter B k).1 ≤ 3 * B + 12 ∧ (lnNatIter B k).2 ≤ (B + 2) * 2 ^ (3 * B + 11) := by
  refine ⟨bitLen_le_of_le_pow (lnNatIter_a_le B k), le_trans (lnNatIter_s_le B k) ?_⟩
  exact Nat.mul_le_mul_right _ hk

#assert_std_axioms bitLen_le_of_lt bitLen_le_of_le_pow lt_two_pow_bitLen bitLen_mono piArg_le
  piIter_succ_arg_le piFinalArg_le sqrt_le_of_le_pow piD_le piWidths lnNatIter_a_le
  lnNatIter_s_le lnWidths

end WP.W7k1
