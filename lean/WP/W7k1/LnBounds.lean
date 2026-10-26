import WP.W7k1.Bounds
import WP.W7k1.PiCost

/-!
# WP.W7k1.LnBounds — the multiplication-free `ln 2` step, value bounds and cost unit

* `lnX B k = a_k(k+1) + (k+2)` and its step lemmas `lnX_div`, `lnX_succ` (the series step without a
  multiplication: one long division by `2k+4`).
* Value bounds (`lnSA_le`, `lnXD_le`): every operand has at most `4B+16 ≤ 8B+44` bits.
* `lnU K B = K·(8B+45)²`, the uniform per-step bound (division included).
* `lnTotal_le`: the total is at most `2^20·K·(B+1)^4`.
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2 Computability

/-! ## The series state without multiplication -/

/-- `X_k = a_k·(k+1) + (k+2)`, the numerator of the next series step. -/
def lnX (B k : ℕ) : ℕ := (lnNatIter B k).1 * (k + 1) + (k + 2)

theorem lnA_zero (B : ℕ) : (lnNatIter B 0).1 = 2 ^ (3 * B + 11) := rfl

theorem lnS_zero (B : ℕ) : (lnNatIter B 0).2 = 0 := rfl

theorem lnS_succ (B k : ℕ) : (lnNatIter B (k + 1)).2 = (lnNatIter B k).2 + (lnNatIter B k).1 :=
  rfl

theorem lnX_zero' (B : ℕ) : lnX B 0 = 2 ^ (3 * B + 11) + 1 + 1 := by
  show 2 ^ (3 * B + 11) * (0 + 1) + (0 + 2) = _
  ring

/-- The next `a` is one long division: `a_{k+1} = X_k / (2k+4)`. -/
theorem lnX_div (B k : ℕ) : lnX B k / (2 * k + 4) = (lnNatIter B (k + 1)).1 := by
  show ((lnNatIter B k).1 * (k + 1) + (k + 2)) / (2 * k + 4) =
    ((lnNatIter B k).1 * (k + 1) + (k + 2)) / (2 * (k + 2))
  rw [show 2 * k + 4 = 2 * (k + 2) by ring]

/-- The next `X` from the remainder: `X_{k+1} = (X_k − X_k % D + D)/2 + 1`, `D = 2k+4`. -/
theorem lnX_succ (B k : ℕ) :
    (lnX B k - lnX B k % (2 * k + 4) + (2 * k + 4)) / 2 ^ 1 + 1 = lnX B (k + 1) := by
  have hdm := Nat.div_add_mod (lnX B k) (2 * k + 4)
  rw [lnX_div] at hdm
  have hX1 : lnX B (k + 1) = (lnNatIter B (k + 1)).1 * (k + 1 + 1) + (k + 1 + 2) := rfl
  rw [hX1]
  generalize (lnNatIter B (k + 1)).1 = q at hdm ⊢
  generalize lnX B k % (2 * k + 4) = r at hdm ⊢
  generalize lnX B k = X at hdm ⊢
  subst hdm
  rw [show (2 * k + 4) * q + r - r + (2 * k + 4) = 2 * ((k + 2) * (q + 1)) by
    rw [Nat.add_sub_cancel]; ring]
  rw [pow_one, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

/-! ## Value bounds -/

theorem lt_two_pow' : ∀ n : ℕ, n < 2 ^ n
  | 0 => by norm_num
  | n + 1 => by
    have := lt_two_pow' n
    rw [pow_succ]
    omega

theorem ln_mul_le {B k : ℕ} (hk : k ≤ B + 2) : (k + 1) * 2 ^ (3 * B + 11) ≤ 2 ^ (4 * B + 14) := by
  have h1 : k + 1 ≤ 2 ^ (B + 3) :=
    le_of_lt (lt_of_le_of_lt (by omega : k + 1 ≤ B + 3) (lt_two_pow' (B + 3)))
  calc (k + 1) * 2 ^ (3 * B + 11) ≤ 2 ^ (B + 3) * 2 ^ (3 * B + 11) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (4 * B + 14) := by ring

/-- `s_k + a_k ≤ 2^(4B+14)` for `k ≤ B+2`. -/
theorem lnSA_le {B k : ℕ} (hk : k ≤ B + 2) :
    (lnNatIter B k).2 + (lnNatIter B k).1 ≤ 2 ^ (4 * B + 14) := by
  have hs := lnNatIter_s_le B k
  have ha := lnNatIter_a_le B k
  have h := ln_mul_le hk
  have e : (k + 1) * 2 ^ (3 * B + 11) = k * 2 ^ (3 * B + 11) + 2 ^ (3 * B + 11) := by ring
  omega

/-- `X_k + D_k ≤ 2^(4B+15)` for `k ≤ B+2`. -/
theorem lnXD_le {B k : ℕ} (hk : k ≤ B + 2) : lnX B k + (2 * k + 4) ≤ 2 ^ (4 * B + 15) := by
  have ha := lnNatIter_a_le B k
  have h1 := ln_mul_le hk
  have h2 : (lnNatIter B k).1 * (k + 1) ≤ (k + 1) * 2 ^ (3 * B + 11) :=
    le_of_le_of_eq (Nat.mul_le_mul_right (k + 1) ha) (Nat.mul_comm _ _)
  have h3 : 3 * B + 12 < 2 ^ (4 * B + 14) :=
    lt_of_lt_of_le (lt_two_pow' _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h4 : 2 ^ (4 * B + 15) = 2 ^ (4 * B + 14) + 2 ^ (4 * B + 14) := by ring
  unfold lnX
  omega

/-! ## The per-step cost bound -/

/-- The uniform per-step cost bound of the `ln 2` kernel. -/
def lnU (K B : ℕ) : ℕ := K * ((8 * B + 45) * (8 * B + 45))

section LnBounds

variable {K : ℕ} (B : ℕ)

theorem lnU_one (hK : 1 ≤ K) : 1 ≤ lnU K B := by
  unfold lnU
  exact le_trans hK (Nat.le_mul_of_pos_right K (by positivity))

theorem lnW_sq (x : ℕ) (hx : x ≤ 8 * B + 44) : x + x + 1 ≤ (8 * B + 45) * (8 * B + 45) := by
  have : 2 * (8 * B + 45) ≤ (8 * B + 45) * (8 * B + 45) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem lnU_lin {x : ℕ} (hx : x ≤ 8 * B + 44) : K * (x + 1) ≤ lnU K B :=
  Nat.mul_le_mul_left _ (by have := lnW_sq B x hx; omega)

theorem lnU_two {x y : ℕ} (hx : x ≤ 8 * B + 44) (hy : y ≤ 8 * B + 44) :
    K * (x + y + 1) ≤ lnU K B :=
  Nat.mul_le_mul_left _ (by have := lnW_sq B x hx; have := lnW_sq B y hy; omega)

theorem lnU_dm {x y : ℕ} (hx : x ≤ 8 * B + 44) (hy : y ≤ 8 * B + 44) :
    K * (x * y + x + y + 1) ≤ lnU K B := by
  apply Nat.mul_le_mul_left
  have h := Nat.mul_le_mul (show x + 1 ≤ 8 * B + 45 by omega) (show y + 1 ≤ 8 * B + 45 by omega)
  have e : x * y + x + y + 1 = (x + 1) * (y + 1) := by ring
  rw [e]
  exact h

theorem lnU_inc {x : ℕ} (hx : bitLen x ≤ 8 * B + 44) : K * (ones (encodeNat x) + 1) ≤ lnU K B := by
  have h1 : ones (encodeNat x) ≤ bitLen x := ones_le_length (encodeNat x)
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) (lnU_lin B hx)

theorem lnU_shl {y : ℕ} (hy : y ≤ 8 * B + 44) : K * (y + bitLen y + 1) ≤ lnU K B :=
  lnU_two B hy (le_trans (WP.W7k2.bitLen_le_self y) hy)

theorem lnU_shr {x y : ℕ} (hy : y ≤ 8 * B + 44) :
    K * (min y (bitLen x) + bitLen y + 1) ≤ lnU K B :=
  le_trans (Nat.mul_le_mul_left _ (by omega)) (lnU_shl B hy)

theorem lnU_k1 : K * (1 + 1) ≤ lnU K B := lnU_lin B (by omega)

end LnBounds

/-- **The total cost** of the `ln 2` kernel is at most `2^20·K·(B+1)^4`. -/
theorem lnTotal_le (K B L : ℕ) (hK : 1 ≤ K) (hL : L ≤ K + ((B + 2) * (17 * lnU K B + 1) + 1)) :
    29 * lnU K B + (L + (13 * lnU K B + 12 * lnU K B)) ≤ 1048576 * K * (B + 1) ^ 4 := by
  have hU : lnU K B ≤ 2025 * K * ((B + 1) * (B + 1)) := by
    unfold lnU
    have h1 : (8 * B + 45) * (8 * B + 45) ≤ 2025 * ((B + 1) * (B + 1)) := by nlinarith
    calc K * ((8 * B + 45) * (8 * B + 45)) ≤ K * (2025 * ((B + 1) * (B + 1))) :=
          Nat.mul_le_mul_left _ h1
      _ = 2025 * K * ((B + 1) * (B + 1)) := by ring
  have hB1 : 1 ≤ B + 1 := by omega
  have hP2 : (B + 1) * (B + 1) ≤ (B + 1) ^ 4 := by
    have : (B + 1) ^ 4 = ((B + 1) * (B + 1)) * ((B + 1) * (B + 1)) := by ring
    rw [this]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hP3 : (B + 2) * ((B + 1) * (B + 1)) ≤ 2 * (B + 1) ^ 4 := by
    have : (B + 1) ^ 4 = (B + 1) * ((B + 1) * ((B + 1) * (B + 1))) := by ring
    rw [this]
    have h4 : B + 2 ≤ 2 * (B + 1) := by omega
    calc (B + 2) * ((B + 1) * (B + 1)) ≤ (2 * (B + 1)) * ((B + 1) * (B + 1)) :=
          Nat.mul_le_mul_right _ h4
      _ ≤ (2 * (B + 1)) * ((B + 1) * ((B + 1) * (B + 1))) := by
          apply Nat.mul_le_mul_left
          exact Nat.le_mul_of_pos_left _ (by omega)
      _ = 2 * ((B + 1) * ((B + 1) * ((B + 1) * (B + 1)))) := by ring
  have hU4 : lnU K B ≤ 2025 * K * (B + 1) ^ 4 := le_trans hU (Nat.mul_le_mul_left _ hP2)
  have hUn : (B + 2) * lnU K B ≤ 2 * 2025 * K * (B + 1) ^ 4 := by
    calc (B + 2) * lnU K B ≤ (B + 2) * (2025 * K * ((B + 1) * (B + 1))) :=
          Nat.mul_le_mul_left _ hU
      _ = 2025 * K * ((B + 2) * ((B + 1) * (B + 1))) := by ring
      _ ≤ 2025 * K * (2 * (B + 1) ^ 4) := Nat.mul_le_mul_left _ hP3
      _ = 2 * 2025 * K * (B + 1) ^ 4 := by ring
  have hK4 : K ≤ K * (B + 1) ^ 4 := Nat.le_mul_of_pos_right _ (by positivity)
  have hB4 : B + 2 ≤ 2 * (K * (B + 1) ^ 4) := by
    have : B + 1 ≤ (B + 1) ^ 4 := by
      calc B + 1 = (B + 1) ^ 1 := (pow_one _).symm
        _ ≤ (B + 1) ^ 4 := Nat.pow_le_pow_right hB1 (by norm_num)
    have : (B + 1) ^ 4 ≤ K * (B + 1) ^ 4 := Nat.le_mul_of_pos_left _ hK
    omega
  have e1 : (B + 2) * (17 * lnU K B + 1) = 17 * ((B + 2) * lnU K B) + (B + 2) := by ring
  rw [e1] at hL
  have e2 : 1048576 * K * (B + 1) ^ 4 = 1048576 * (K * (B + 1) ^ 4) := by ring
  have e3 : 2 * 2025 * K * (B + 1) ^ 4 = 2 * 2025 * (K * (B + 1) ^ 4) := by ring
  have e4 : 2025 * K * (B + 1) ^ 4 = 2025 * (K * (B + 1) ^ 4) := by ring
  rw [e2]
  rw [e3] at hUn
  rw [e4] at hU4
  omega

#assert_std_axioms lnA_zero lnS_zero lnS_succ lnX_zero' lnX_div lnX_succ lt_two_pow' ln_mul_le
  lnSA_le lnXD_le lnU_one lnW_sq lnU_lin lnU_two lnU_dm lnU_inc lnU_shl lnU_shr lnU_k1
  lnTotal_le

end WP.W7k1
