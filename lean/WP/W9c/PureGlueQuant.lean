import WP.W9c.PureSpec

/-!
# WP.W9c.PureGlueQuant — `GlueQuant` and `GluePackW` (split 4, pure)

* `gQuant_abs_lt`: `|v| < 2^w ⇒ |gQuantizeCoordToScale p_in q v| < 2^(w+q)`. With `D = 2^(p_in+2) ≥ 4`,
  `Q = 2^q`, `g = (2vQ + D) / (2D)`: `g ≥ 2^w·Q` or `g ≤ -2^w·Q` would force `D(2P − 1) < 2P` for
  `P = 2^w·Q ≥ 1`, impossible for `D ≥ 4`.
* `glueQuant_holds : GlueQuant`.
* `gluePackW_holds : GluePackW`: `PureUnpack.bitLen_pack_le` (`≤ B + k·|f|`) with `B = w + q` (blocks,
  by `GlueQuant`) or `B = w` (taps), `k = s - 1 + 1`; the degenerate case `s = w = 0` has only zero
  entries, so both packs are `0`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts IntMul

theorem abs_lt_of_bitLen {v : ℤ} {w : ℕ} (h : bitLen v.natAbs ≤ w) : |v| < 2 ^ w := by
  have h1 := (WP.W7k2.bitLen_le_iff w v.natAbs).1 h
  have h2 : ((v.natAbs : ℕ) : ℤ) < ((2 ^ w : ℕ) : ℤ) := by exact_mod_cast h1
  rw [Int.natCast_natAbs] at h2
  push_cast at h2
  exact h2

theorem bitLen_le_of_abs_lt {v : ℤ} {w : ℕ} (h : |v| < 2 ^ w) : bitLen v.natAbs ≤ w := by
  apply (WP.W7k2.bitLen_le_iff w v.natAbs).2
  have h2 : ((v.natAbs : ℕ) : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    exact h
  exact_mod_cast h2

theorem gQuant_abs_lt (p_in q w : ℕ) (v : ℤ) (hv : |v| < 2 ^ w) :
    |gQuantizeCoordToScale p_in q v| < 2 ^ (w + q) := by
  have hQc : (((2 ^ q : ℕ) : ℤ)) = (2 : ℤ) ^ q := by push_cast; ring
  have hDc : (((2 ^ (p_in + 2) : ℕ) : ℤ)) = (2 : ℤ) ^ (p_in + 2) := by push_cast; ring
  unfold gQuantizeCoordToScale IntMul.divRoundRatInt
  rw [hQc, hDc, pow_add (2 : ℤ) w q]
  have hA1 : (1 : ℤ) ≤ 2 ^ w := one_le_pow₀ (by norm_num)
  have hQ1 : (1 : ℤ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have hD4 : (4 : ℤ) ≤ 2 ^ (p_in + 2) := by
    have h1 : (1 : ℤ) ≤ 2 ^ p_in := one_le_pow₀ (by norm_num)
    rw [pow_add]
    nlinarith
  generalize (2 : ℤ) ^ w = A at *
  generalize (2 : ℤ) ^ q = Q at *
  generalize (2 : ℤ) ^ (p_in + 2) = D at *
  rw [if_pos (by omega)]
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  have hvQ1 : v * Q ≤ (A - 1) * Q := mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hvQ2 : -(A - 1) * Q ≤ v * Q := mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hAQ : 1 ≤ A * Q := by nlinarith
  have hE : 0 < 2 * D := by omega
  have hdef := Int.emod_def (2 * (v * Q) + D) (2 * D)
  have hr0 := Int.emod_nonneg (2 * (v * Q) + D) (ne_of_gt hE)
  have hr1 := Int.emod_lt_of_pos (2 * (v * Q) + D) hE
  generalize (2 * (v * Q) + D) % (2 * D) = rem at *
  generalize (2 * (v * Q) + D) / (2 * D) = g at *
  have h4 : 4 * (2 * (A * Q) - 1) ≤ D * (2 * (A * Q) - 1) :=
    mul_le_mul_of_nonneg_right hD4 (by omega)
  refine abs_lt.mpr ⟨?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have h5 : 2 * D * g ≤ 2 * D * (-(A * Q)) := mul_le_mul_of_nonneg_left hc (by omega)
    nlinarith
  · by_contra hc
    push_neg at hc
    have h5 : 2 * D * (A * Q) ≤ 2 * D * g := mul_le_mul_of_nonneg_left hc (by omega)
    nlinarith

/-- **GlueQuant**: quantization adds at most `q` bits. -/
theorem glueQuant_holds : GlueQuant := by
  intro p_in q w v hv
  exact bitLen_le_of_abs_lt (gQuant_abs_lt p_in q w v (abs_lt_of_bitLen hv))

theorem pack_eq_zero_of_all_zero (M : ℤ) :
    ∀ f : List ℤ, (∀ x ∈ f, x = 0) → packSignedKronecker M f = 0
  | [], _ => rfl
  | c :: f, h => by
    simp only [packSignedKronecker]
    rw [h c (by simp), pack_eq_zero_of_all_zero M f (fun x hx => h x (by simp [hx]))]
    ring

theorem gQuant_zero (p_in q : ℕ) : gQuantizeCoordToScale p_in q 0 = 0 := by
  unfold gQuantizeCoordToScale IntMul.divRoundRatInt
  have hD : (0 : ℤ) < ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
  rw [if_pos hD, zero_mul, mul_zero, zero_add]
  exact Int.ediv_eq_zero_of_lt (le_of_lt hD) (by omega)

theorem eq_zero_of_bitLen_le_zero {v : ℤ} (h : bitLen v.natAbs ≤ 0) : v = 0 := by
  have h1 := (WP.W7k2.bitLen_le_iff 0 v.natAbs).1 h
  rw [pow_zero] at h1
  exact Int.natAbs_eq_zero.1 (by omega)

theorem width_arith (s w W B n : ℕ) (hn : n ≤ W) (hB : B ≤ w + s) (hs : s = 0 → B ≤ w)
    (hsw : 1 ≤ s ∨ 1 ≤ w) : B + (s - 1 + 1) * n ≤ (W + 1) * (s + w) := by
  rcases Nat.eq_zero_or_pos s with h0 | hs1
  · subst h0
    have hw : 1 ≤ w := by omega
    have hB' := hs rfl
    have h1 : W * 1 ≤ W * w := Nat.mul_le_mul_left W hw
    simp only [Nat.zero_sub, Nat.zero_add, Nat.one_mul]
    nlinarith
  · have hk : s - 1 + 1 = s := by omega
    rw [hk]
    have h1 : s * n ≤ s * W := Nat.mul_le_mul_left s hn
    nlinarith

/-- **GluePackW**: both packs fit the declared W5 width `(W + 1)·(s + w)`. -/
theorem gluePackW_holds : GluePackW := by
  intro s p_in q w W blk taps hqs hblk htaps hb ht
  have hk : 1 ≤ s - 1 + 1 := by omega
  by_cases h00 : s = 0 ∧ w = 0
  · obtain ⟨hs0, hw0⟩ := h00
    subst hs0
    subst hw0
    have h1 : packSignedKronecker ((2 ^ (0 - 1 + 1) : ℕ) : ℤ)
        (blk.map (gQuantizeCoordToScale p_in q)) = 0 := by
      refine pack_eq_zero_of_all_zero _ _ (fun x hx => ?_)
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      rw [eq_zero_of_bitLen_le_zero (hb v hv), gQuant_zero]
    have h2 : packSignedKronecker ((2 ^ (0 - 1 + 1) : ℕ) : ℤ) taps = 0 :=
      pack_eq_zero_of_all_zero _ _ (fun t htt => eq_zero_of_bitLen_le_zero (ht t htt))
    rw [h1, h2]
    simp [WP.W7k2.bitLen_zero]
  · have hsw : 1 ≤ s ∨ 1 ≤ w := by omega
    constructor
    · have hq : ∀ x ∈ blk.map (gQuantizeCoordToScale p_in q), bitLen x.natAbs ≤ w + q := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
        exact glueQuant_holds p_in q w v (hb v hv)
      have h := bitLen_pack_le (s - 1 + 1) (w + q) hk _ hq
      rw [List.length_map] at h
      exact le_trans h (width_arith s w W (w + q) blk.length hblk (by omega) (by omega) hsw)
    · have h := bitLen_pack_le (s - 1 + 1) w hk taps ht
      exact le_trans h (width_arith s w W w taps.length htaps (by omega) (by omega) hsw)

#assert_std_axioms abs_lt_of_bitLen bitLen_le_of_abs_lt gQuant_abs_lt glueQuant_holds
  pack_eq_zero_of_all_zero gQuant_zero eq_zero_of_bitLen_le_zero width_arith gluePackW_holds

end WP.W9c
