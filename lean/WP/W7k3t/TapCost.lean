import WP.W7k3t.Vals

/-!
# WP.W7k3t.TapCost — the cost arithmetic of the tap kernel

`tap_cost_le`: the program's bound `2·(17·pSub+23)·160·uc U W + 1100·uc U W` at `W = tapW …`
(`≤ 569·(p_work + pSub + |t1| + 1)`) is at most `8460·569²·U·(p_work + pSub + |t1| + 1)⁴`
(the actual growth is cubic).
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

theorem log2_le_bitLen (n : ℕ) : Nat.log2 n ≤ bitLen n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact le_of_lt ((Nat.log2_lt (by omega)).mpr (lt_two_pow_bitLen n))

/-- The cost arithmetic: the program's bound is at most `C·(p_work + pSub + |t1| + 1)⁴`. -/
theorem tap_cost_le (U p_work pSub t1 : ℕ) :
    2 * ((17 * pSub + 23) * (160 * uc U (tapW p_work pSub t1))) +
        1100 * uc U (tapW p_work pSub t1) ≤
      (8460 * 569 ^ 2 * U) * (p_work + pSub + bitLen t1 + 1) ^ 4 := by
  have hL := log2_le_bitLen t1
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = p_work + pSub + bitLen t1 + 1 := ⟨_, rfl⟩
  rw [← hQ]
  have hQ1 : 1 ≤ Q := by omega
  have hW1 : tapW p_work pSub t1 + 1 ≤ 569 * Q := by unfold tapW; omega
  have hN : 17 * pSub + 23 ≤ 23 * Q := by omega
  have huc : uc U (tapW p_work pSub t1) ≤ U * (569 * Q) ^ 2 := by
    unfold uc
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW1 2)
  calc 2 * ((17 * pSub + 23) * (160 * uc U (tapW p_work pSub t1))) +
        1100 * uc U (tapW p_work pSub t1)
      ≤ 2 * ((23 * Q) * (160 * (U * (569 * Q) ^ 2))) + 1100 * (U * (569 * Q) ^ 2) := by
        gcongr
    _ = (7360 * Q + 1100) * (569 ^ 2 * U * Q ^ 2) := by ring
    _ ≤ (8460 * Q) * (569 ^ 2 * U * Q ^ 2) := by gcongr; omega
    _ = 8460 * 569 ^ 2 * U * Q ^ 3 := by ring
    _ ≤ 8460 * 569 ^ 2 * U * Q ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hQ1 (by norm_num))

#assert_std_axioms log2_le_bitLen tap_cost_le

end WP.W7k3t
