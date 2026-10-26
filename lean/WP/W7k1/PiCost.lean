import WP.W7k2.Arith

/-!
# WP.W7k1.PiCost — cost arithmetic of the `π` kernel

Every step of the `π` kernel costs at most `piU K B = K·((8B+44)² + 1)`: each contract call costs
`K` times a linear or quadratic expression in operand widths and shift amounts, and every value of
the kernel has at most `8B+44` bits (`WP.W7k1.Bounds`). The phases have `24`, `5` per iteration,
`17` and `12` steps; the loop runs `B+4` times. `piTotal_le` bounds the sum by `C·(B+1)^4`.
-/

namespace WP.W7k1

open TMFw TMFw.Contracts Computability

/-- The uniform per-step cost bound of the `π` kernel. -/
def piU (K B : ℕ) : ℕ := K * ((8 * B + 44) * (8 * B + 44) + 1)

section Bounds

variable {K : ℕ} (B : ℕ)

theorem piU_one (hK : 1 ≤ K) : 1 ≤ piU K B := by
  unfold piU
  have : 1 ≤ (8 * B + 44) * (8 * B + 44) + 1 := by omega
  exact le_trans hK (Nat.le_mul_of_pos_right K (by omega))

theorem piW_sq (x : ℕ) (hx : x ≤ 8 * B + 44) : x + x + 1 ≤ (8 * B + 44) * (8 * B + 44) + 1 := by
  have h44 : 2 * (8 * B + 44) ≤ (8 * B + 44) * (8 * B + 44) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem piU_lin {x : ℕ} (hx : x ≤ 8 * B + 44) : K * (x + 1) ≤ piU K B :=
  Nat.mul_le_mul_left _ (by have := piW_sq B x hx; omega)

theorem piU_two {x y : ℕ} (hx : x ≤ 8 * B + 44) (hy : y ≤ 8 * B + 44) :
    K * (x + y + 1) ≤ piU K B :=
  Nat.mul_le_mul_left _ (by have := piW_sq B x hx; have := piW_sq B y hy; omega)

theorem piU_sq {x : ℕ} (hx : x ≤ 8 * B + 44) : K * (x * x + 1) ≤ piU K B :=
  Nat.mul_le_mul_left _ (by have := Nat.mul_le_mul hx hx; omega)

theorem piU_inc {x : ℕ} (hx : bitLen x ≤ 8 * B + 44) : K * (ones (encodeNat x) + 1) ≤ piU K B := by
  have h1 : ones (encodeNat x) ≤ bitLen x := ones_le_length (encodeNat x)
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) (piU_lin B hx)

theorem piU_shl {y : ℕ} (hy : y ≤ 8 * B + 44) : K * (y + bitLen y + 1) ≤ piU K B :=
  piU_two B hy (le_trans (WP.W7k2.bitLen_le_self y) hy)

theorem piU_shr {x y : ℕ} (hy : y ≤ 8 * B + 44) :
    K * (min y (bitLen x) + bitLen y + 1) ≤ piU K B :=
  le_trans (Nat.mul_le_mul_left _ (by omega)) (piU_shl B hy)

theorem piU_k1 : K * (1 + 1) ≤ piU K B := piU_lin B (by omega)

end Bounds

/-- `loopCost` is monotone in the iteration bounds below the trip count. -/
theorem loopCost_mono_lt {f g : ℕ → ℕ} : ∀ N, (∀ i, i < N → f i ≤ g i) →
    loopCost f N ≤ loopCost g N
  | 0, _ => le_rfl
  | N + 1, h => by
    have := loopCost_mono_lt N (fun i hi => h i (by omega))
    have := h N (by omega)
    simp only [loopCost]
    omega

/-- **The total cost** of the `π` kernel is at most `2^20·K·(B+1)^4`. -/
theorem piTotal_le (K B L : ℕ) (hK : 1 ≤ K) (hL : L ≤ K + ((B + 4) * (7 * piU K B + 1) + 1)) :
    24 * piU K B + (L + (17 * piU K B + 12 * piU K B)) ≤ 1048576 * K * (B + 1) ^ 4 := by
  have hU : piU K B ≤ 1937 * K * ((B + 1) * (B + 1)) := by
    unfold piU
    have h1 : (8 * B + 44) * (8 * B + 44) + 1 ≤ 1937 * ((B + 1) * (B + 1)) := by
      have : (8 * B + 44) * (8 * B + 44) ≤ 1936 * ((B + 1) * (B + 1)) := by nlinarith
      have : 1 ≤ (B + 1) * (B + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    calc K * ((8 * B + 44) * (8 * B + 44) + 1) ≤ K * (1937 * ((B + 1) * (B + 1))) :=
          Nat.mul_le_mul_left _ h1
      _ = 1937 * K * ((B + 1) * (B + 1)) := by ring
  have hB1 : 1 ≤ B + 1 := by omega
  have hP2 : (B + 1) * (B + 1) ≤ (B + 1) ^ 4 := by
    have : (B + 1) ^ 4 = ((B + 1) * (B + 1)) * ((B + 1) * (B + 1)) := by ring
    rw [this]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hP3 : (B + 4) * ((B + 1) * (B + 1)) ≤ 4 * (B + 1) ^ 4 := by
    have : (B + 1) ^ 4 = (B + 1) * ((B + 1) * ((B + 1) * (B + 1))) := by ring
    rw [this]
    have h4 : B + 4 ≤ 4 * (B + 1) := by omega
    calc (B + 4) * ((B + 1) * (B + 1)) ≤ (4 * (B + 1)) * ((B + 1) * (B + 1)) :=
          Nat.mul_le_mul_right _ h4
      _ ≤ (4 * (B + 1)) * ((B + 1) * ((B + 1) * (B + 1))) := by
          apply Nat.mul_le_mul_left
          exact Nat.le_mul_of_pos_left _ (by omega)
      _ = 4 * ((B + 1) * ((B + 1) * ((B + 1) * (B + 1)))) := by ring
  have hU4 : piU K B ≤ 1937 * K * (B + 1) ^ 4 := le_trans hU (Nat.mul_le_mul_left _ hP2)
  have hUn : (B + 4) * piU K B ≤ 4 * 1937 * K * (B + 1) ^ 4 := by
    calc (B + 4) * piU K B ≤ (B + 4) * (1937 * K * ((B + 1) * (B + 1))) :=
          Nat.mul_le_mul_left _ hU
      _ = 1937 * K * ((B + 4) * ((B + 1) * (B + 1))) := by ring
      _ ≤ 1937 * K * (4 * (B + 1) ^ 4) := Nat.mul_le_mul_left _ hP3
      _ = 4 * 1937 * K * (B + 1) ^ 4 := by ring
  have hK4 : K ≤ K * (B + 1) ^ 4 := Nat.le_mul_of_pos_right _ (by positivity)
  have hB4 : B + 4 ≤ 4 * (K * (B + 1) ^ 4) := by
    have : B + 1 ≤ (B + 1) ^ 4 := by
      calc B + 1 = (B + 1) ^ 1 := (pow_one _).symm
        _ ≤ (B + 1) ^ 4 := Nat.pow_le_pow_right hB1 (by norm_num)
    have : (B + 1) ^ 4 ≤ K * (B + 1) ^ 4 := Nat.le_mul_of_pos_left _ hK
    omega
  have e1 : (B + 4) * (7 * piU K B + 1) = 7 * ((B + 4) * piU K B) + (B + 4) := by ring
  rw [e1] at hL
  have e2 : 1048576 * K * (B + 1) ^ 4 = 1048576 * (K * (B + 1) ^ 4) := by ring
  have e3 : 4 * 1937 * K * (B + 1) ^ 4 = 4 * 1937 * (K * (B + 1) ^ 4) := by ring
  have e4 : 1937 * K * (B + 1) ^ 4 = 1937 * (K * (B + 1) ^ 4) := by ring
  rw [e2]
  rw [e3] at hUn
  rw [e4] at hU4
  omega

#assert_std_axioms piU_one piW_sq piU_lin piU_two piU_sq piU_inc piU_shl piU_shr piU_k1
  loopCost_mono_lt piTotal_le

end WP.W7k1
