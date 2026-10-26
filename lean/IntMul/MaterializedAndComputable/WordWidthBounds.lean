import IntMul.ExecutableAlgorithm

/-!
# Intermediate Word-Width and Dynamic-Range Invariants (`4 * pChild p K` Bits)
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## Intermediate Word-Width and Dynamic-Range Invariants (`4 * pChild p K` Bits) -/

/-- Exact integer fixed-point coordinate corresponding to `realQuantize q x`:
`realQuantizeInt q x = ⌊x * 2^(q + 2) + 1/2⌋ : ℤ`, so `realQuantize q x = (realQuantizeInt q x : ℝ) / 2^(q + 2)`. -/
noncomputable def realQuantizeInt (q : ℕ) (x : ℝ) : ℤ :=
  ⌊x * (2 : ℝ) ^ (q + 2) + 1 / 2⌋

/-- `realQuantize q x` is the exact dyadic rational `(realQuantizeInt q x : ℝ) / 2^(q + 2)`. -/
theorem realQuantize_eq_realQuantizeInt_div (q : ℕ) (x : ℝ) :
    realQuantize q x = (realQuantizeInt q x : ℝ) / (2 : ℝ) ^ (q + 2) := by
  rfl

/-- **Fixed-Point Integer Coordinate Bound (`abs_realQuantizeInt_le`)**:
If `|x| ≤ (2 : ℝ) ^ B`, then the quantized integer coordinate `realQuantizeInt q x` satisfies
`|realQuantizeInt q x| ≤ 2 ^ (B + q + 2)`. -/
theorem abs_realQuantizeInt_le (q B : ℕ) (x : ℝ) (hx : |x| ≤ (2 : ℝ) ^ B) :
    |realQuantizeInt q x| ≤ (2 : ℤ) ^ (B + q + 2) := by
  unfold realQuantizeInt
  have h1 := abs_le.mp hx
  have hscale_pos : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
  have hprod_upper : x * (2 : ℝ) ^ (q + 2) ≤ (2 : ℝ) ^ (B + q + 2) := by
    calc x * (2 : ℝ) ^ (q + 2)
        ≤ (2 : ℝ) ^ B * (2 : ℝ) ^ (q + 2) := mul_le_mul_of_nonneg_right h1.2 hscale_pos.le
      _ = (2 : ℝ) ^ (B + q + 2) := by rw [← pow_add, ← add_assoc]
  have hprod_lower : -((2 : ℝ) ^ (B + q + 2)) ≤ x * (2 : ℝ) ^ (q + 2) := by
    calc -((2 : ℝ) ^ (B + q + 2))
        = -((2 : ℝ) ^ B) * (2 : ℝ) ^ (q + 2) := by rw [neg_mul, ← pow_add, ← add_assoc]
      _ ≤ x * (2 : ℝ) ^ (q + 2) := mul_le_mul_of_nonneg_right h1.1 hscale_pos.le
  set M : ℤ := (2 : ℤ) ^ (B + q + 2)
  have hM_cast : (M : ℝ) = (2 : ℝ) ^ (B + q + 2) := by
    dsimp [M]
    push_cast
    rfl
  have hfloor_le : ⌊x * (2 : ℝ) ^ (q + 2) + 1 / 2⌋ ≤ M := by
    rw [Int.floor_le_iff]
    linarith
  have hfloor_ge : -M ≤ ⌊x * (2 : ℝ) ^ (q + 2) + 1 / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  exact abs_le.mpr ⟨hfloor_ge, hfloor_le⟩

/-- **Signed `4 * pChild p K`-Bit Word Membership (`realQuantizeInt_mem_four_mul_pChild_word`)**:
For any complex number `z : ℂ` with Euclidean norm `‖z‖ ≤ (2 : ℝ) ^ (pChild p K)`, its fixed-point
integer real and imaginary coordinates at sub-step precision `2 * pChild p K` satisfy:
`|realQuantizeInt (2 * pChild p K) z.re| < (2 : ℤ) ^ (4 * pChild p K - 1)` and
`|realQuantizeInt (2 * pChild p K) z.im| < (2 : ℤ) ^ (4 * pChild p K - 1)`,
fitting strictly inside a signed integer word of width `4 * pChild p K` bits. -/
theorem realQuantizeInt_mem_four_mul_pChild_word
    (p K : ℕ) (z : ℂ) (hz : ‖z‖ ≤ (2 : ℝ) ^ (pChild p K)) :
    |realQuantizeInt (2 * pChild p K) z.re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
    |realQuantizeInt (2 * pChild p K) z.im| < (2 : ℤ) ^ (4 * pChild p K - 1) := by
  have hp'_ge12 : 12 ≤ pChild p K := by
    rw [pChild_eq_additive]
    omega
  have hre : |z.re| ≤ (2 : ℝ) ^ (pChild p K) := (Complex.abs_re_le_norm z).trans hz
  have him : |z.im| ≤ (2 : ℝ) ^ (pChild p K) := (Complex.abs_im_le_norm z).trans hz
  have hre_int := abs_realQuantizeInt_le (2 * pChild p K) (pChild p K) z.re hre
  have him_int := abs_realQuantizeInt_le (2 * pChild p K) (pChild p K) z.im him
  have hexp_lt : pChild p K + 2 * pChild p K + 2 < 4 * pChild p K - 1 := by omega
  have hpow_lt : (2 : ℤ) ^ (pChild p K + 2 * pChild p K + 2) < (2 : ℤ) ^ (4 * pChild p K - 1) := by
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) hexp_lt
  exact ⟨hre_int.trans_lt hpow_lt, him_int.trans_lt hpow_lt⟩

/-- **Magnitude Bound for `zPartFwdQuantized` (`norm_zPartFwdQuantized_le`, `[MS]` §§5.1–5.2)**:
When `0 < ‖c0‖`, `‖c1‖ ≤ ‖c0‖`, and `∀ k ≤ u1, ‖Y k‖ ≤ M_Y`, the forward particular sweep
satisfies `‖zPartFwdQuantized q c0 c1 Y u1‖ ≤ u1 * (M_Y / ‖c0‖ + complexQuantizeMaxErr q)`. -/
theorem norm_zPartFwdQuantized_le
    (q : ℕ) (c0 c1 : ℂ) (hc0_pos : 0 < ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖)
    (Y : ℕ → ℂ) (M_Y : ℝ) (u1 : ℕ) (hY : ∀ k ≤ u1, ‖Y k‖ ≤ M_Y) :
    ‖zPartFwdQuantized q c0 c1 Y u1‖ ≤
      (u1 : ℝ) * (M_Y / ‖c0‖ + complexQuantizeMaxErr q) := by
  have hratio : ‖-c1 / c0‖ ≤ 1 := by
    rw [norm_div, norm_neg]
    exact (div_le_one hc0_pos).mpr hc10
  induction u1 with
  | zero =>
    simp [zPartFwdQuantized]
  | succ u1 ih =>
    dsimp only [zPartFwdQuantized]
    have hih := ih (fun k hk => hY k (Nat.le_succ_of_le hk))
    have hYu1 : ‖Y (u1 + 1)‖ ≤ M_Y := hY (u1 + 1) le_rfl
    have hdiv : ‖Y (u1 + 1) / c0‖ ≤ M_Y / ‖c0‖ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_right hYu1 hc0_pos.le
    have hmul : ‖(-c1 / c0) * zPartFwdQuantized q c0 c1 Y u1‖ ≤
        ‖zPartFwdQuantized q c0 c1 Y u1‖ := by
      rw [norm_mul]
      calc ‖-c1 / c0‖ * ‖zPartFwdQuantized q c0 c1 Y u1‖
          ≤ 1 * ‖zPartFwdQuantized q c0 c1 Y u1‖ :=
            mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
        _ = ‖zPartFwdQuantized q c0 c1 Y u1‖ := one_mul _
    have htri := norm_add_le (Y (u1 + 1) / c0) ((-c1 / c0) * zPartFwdQuantized q c0 c1 Y u1)
    have hq := norm_complexQuantize_le q
      (Y (u1 + 1) / c0 + (-c1 / c0) * zPartFwdQuantized q c0 c1 Y u1)
    push_cast
    linarith

/-- **Magnitude Bound for `zPartNyqQuantized` (`norm_zPartNyqQuantized_le`, `[MS]` §§5.1–5.2)**:
When `0 < ‖c0‖` and `∀ k ≤ u1, ‖Y k‖ ≤ M_Y`, the Nyquist particular sweep satisfies
`‖zPartNyqQuantized q c0 Y u1‖ ≤ u1 * (M_Y / ‖c0‖ + complexQuantizeMaxErr q)`. -/
theorem norm_zPartNyqQuantized_le
    (q : ℕ) (c0 : ℂ) (hc0_pos : 0 < ‖c0‖)
    (Y : ℕ → ℂ) (M_Y : ℝ) (u1 : ℕ) (hY : ∀ k ≤ u1, ‖Y k‖ ≤ M_Y) :
    ‖zPartNyqQuantized q c0 Y u1‖ ≤
      (u1 : ℝ) * (M_Y / ‖c0‖ + complexQuantizeMaxErr q) := by
  induction u1 with
  | zero =>
    simp [zPartNyqQuantized]
  | succ u1 ih =>
    dsimp only [zPartNyqQuantized]
    have hih := ih (fun k hk => hY k (Nat.le_succ_of_le hk))
    have hYu1 : ‖Y (u1 + 1)‖ ≤ M_Y := hY (u1 + 1) le_rfl
    have hdiv : ‖Y (u1 + 1) / c0‖ ≤ M_Y / ‖c0‖ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_right hYu1 hc0_pos.le
    have htri := norm_sub_le (Y (u1 + 1) / c0) (zPartNyqQuantized q c0 Y u1)
    have hq := norm_complexQuantize_le q (Y (u1 + 1) / c0 - zPartNyqQuantized q c0 Y u1)
    push_cast
    linarith

/-- Intermediate spread array `U(j1, k2)` at recursive step `(p, K, t1, r)`. -/
noncomputable def stepSpread (p K t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) : ℂ :=
  kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2

/-- Intermediate pre-twisted array `P(j1, k2)` at recursive step `(p, K, t1, r)`. -/
noncomputable def stepPreTwist (p K t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) : ℂ :=
  let pSub := 2 * pChild p K
  complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * stepSpread p K t1 r x j1 k2)

/-- Intermediate butterfly stage `s` (`0 ≤ s ≤ Nat.log2 t1`) of `syntheticFFTRadix2Quantized`
at recursive step `(p, K, t1, r)`. -/
noncomputable def stepSyntheticStage (p K t1 r : ℕ) (x : ℕ → ℂ) (s v1 k2 : ℕ) : ℂ :=
  let pSub := 2 * pChild p K
  syntheticFFTRadix2Quantized pSub r s (r / t1) (stepPreTwist p K t1 r x) v1 k2

/-- Quantized Synthetic FFT output `Q(v1, k2)` at recursive step `(p, K, t1, r)`. -/
noncomputable def stepSyntheticOut (p K t1 r : ℕ) (x : ℕ → ℂ) (v1 k2 : ℕ) : ℂ :=
  let pSub := 2 * pChild p K
  complexQuantize pSub (stepSyntheticStage p K t1 r x (Nat.log2 t1) v1 k2)

/-- Post-twisted child input `qPost(v1, k2)` at recursive step `(p, K, t1, r)`. -/
noncomputable def stepPostTwist (p K t1 r : ℕ) (x : ℕ → ℂ) (v1 k2 : ℕ) : ℂ :=
  let pSub := 2 * pChild p K
  complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * stepSyntheticOut p K t1 r x v1 k2)

/-- **Complete Intermediate Dynamic-Range and `4 * pChild p K`-Bit Word-Width Theorem (`step_intermediate_word_width_bounds`, `[MS]` §§3.2, 5.2 & 6.3)**:
At any internal node `.step p K t1 r c1 v1Of child` with `0 < t1`, `0 < r`, `t1 * r = 2 ^ K`,
and `∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p`, every intermediate array entry:
1. `stepSpread p K t1 r x j1 k2` (`j1 < t1, k2 < r`),
2. `stepPreTwist p K t1 r x j1 k2` (`j1 < t1, k2 < r`),
3. `stepSyntheticStage p K t1 r x s v1 k2` at every butterfly stage `s ≤ Nat.log2 t1` (`k2 < r`),
4. `stepSyntheticOut p K t1 r x v1 k2` (`k2 < r`), and
5. `stepPostTwist p K t1 r x v1 k2` (`k2 < r`)
has Euclidean norm bounded by `(2 : ℝ) ^ (pChild p K)` and fixed-point scaled integer coordinates
at `2 * pChild p K` strictly bounded by `(2 : ℤ) ^ (4 * pChild p K - 1)` (`4 * pChild p K` signed bits). -/
theorem step_intermediate_word_width_bounds
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (j1 v1 k2 s : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) (hs : s ≤ Nat.log2 t1) :
    ‖stepSpread p K t1 r x j1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖stepPreTwist p K t1 r x j1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖stepSyntheticStage p K t1 r x s v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖stepSyntheticOut p K t1 r x v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖stepPostTwist p K t1 r x v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    (|realQuantizeInt (2 * pChild p K) (stepSpread p K t1 r x j1 k2).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (stepSpread p K t1 r x j1 k2).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt (2 * pChild p K) (stepPreTwist p K t1 r x j1 k2).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (stepPreTwist p K t1 r x j1 k2).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt (2 * pChild p K) (stepSyntheticStage p K t1 r x s v1 k2).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (stepSyntheticStage p K t1 r x s v1 k2).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt (2 * pChild p K) (stepSyntheticOut p K t1 r x v1 k2).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (stepSyntheticOut p K t1 r x v1 k2).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt (2 * pChild p K) (stepPostTwist p K t1 r x v1 k2).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (stepPostTwist p K t1 r x v1 k2).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) := by
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hM_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hr_le : r ≤ 2 ^ K := by
    rw [← hsize]
    exact Nat.le_mul_of_pos_left r ht1
  have hr1_nat : r + 1 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : r + 1 ≤ 2 ^ (K + 1) := by
      rw [pow_succ]
      omega
    exact h2.trans (Nat.pow_le_pow_right zero_lt_two (by omega))
  have hr1_real : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast hr1_nat
  have hr1_M_le_p' : ((r : ℝ) + 1) * (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (pChild p K) := by
    calc ((r : ℝ) + 1) * (2 : ℝ) ^ p
        ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right hr1_real hM_nonneg
      _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
      _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]
  have hU_all : ∀ j < t1, ∀ m < r, ‖stepSpread p K t1 r x j m‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * (2 : ℝ) ^ p :=
    fun j hj m hm => norm_kroneckerSincGaussianSpreadArray_le p K t1 r ht1 hr x ((2 : ℝ) ^ p) hM1 hx j m hj hm
  have hP_all : ∀ j < t1, ∀ m < r, ‖stepPreTwist p K t1 r x j m‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p := by
    intro j hj m hm
    unfold stepPreTwist
    have h := norm_complexQuantize_zetaRoot_mul_le p K r hr_le (m : ℝ) (stepSpread p K t1 r x j m) (0.5 : ℝ)
      ((2 : ℝ) ^ p) (by norm_num) hM1 (hU_all j hj m hm)
    dsimp only at h
    linarith
  obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  have h2s_le_t1 : 2 ^ s ≤ t1 := by
    rw [← ht1_pow]
    exact Nat.pow_le_pow_right zero_lt_two hs
  have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hlog_err : complexQuantizeMaxErr (2 * pChild p K) * ((Nat.log2 t1 : ℝ) + 1) ≤ (0.01 : ℝ) := by
    have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
    nlinarith
  have hs_err : (s : ℝ) * complexQuantizeMaxErr (2 * pChild p K) ≤ (0.01 : ℝ) := by
    have hs_real : (s : ℝ) ≤ (Nat.log2 t1 : ℝ) := by exact_mod_cast hs
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr (2 * pChild p K) := by unfold complexQuantizeMaxErr; positivity
    nlinarith
  have hQ_stage_le : ‖stepSyntheticStage p K t1 r x s v1 k2‖ ≤ ((r : ℝ) + (0.53 : ℝ)) * (2 : ℝ) ^ p := by
    have hsyn : ‖stepSyntheticStage p K t1 r x s v1 k2‖ ≤
        ((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p + (s : ℝ) * complexQuantizeMaxErr (2 * pChild p K) :=
      norm_syntheticFFTRadix2Quantized_le (2 * pChild p K) r s (r / t1) hr (stepPreTwist p K t1 r x)
        (((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p) (fun j hj m hm => hP_all j (hj.trans_le h2s_le_t1) m hm) v1 k2 hk2
    have h01 : (0.01 : ℝ) ≤ (0.01 : ℝ) * (2 : ℝ) ^ p := by linarith
    linarith
  have hQ_le : ‖stepSyntheticOut p K t1 r x v1 k2‖ ≤ ((r : ℝ) + (0.53 : ℝ)) * (2 : ℝ) ^ p := by
    have hsyn : ‖stepSyntheticStage p K t1 r x (Nat.log2 t1) v1 k2‖ ≤
        ((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p + (Nat.log2 t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) :=
      norm_syntheticFFTRadix2Quantized_le (2 * pChild p K) r (Nat.log2 t1) (r / t1) hr (stepPreTwist p K t1 r x)
        (((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p) (fun j hj m hm => hP_all j (ht1_pow ▸ hj) m hm) v1 k2 hk2
    have hquant : ‖stepSyntheticOut p K t1 r x v1 k2‖ ≤
        ‖stepSyntheticStage p K t1 r x (Nat.log2 t1) v1 k2‖ + complexQuantizeMaxErr (2 * pChild p K) :=
      norm_complexQuantize_le (2 * pChild p K) (stepSyntheticStage p K t1 r x (Nat.log2 t1) v1 k2)
    have h01 : (0.01 : ℝ) ≤ (0.01 : ℝ) * (2 : ℝ) ^ p := by linarith
    linarith
  have hU_p' : ‖stepSpread p K t1 r x j1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) := by
    have h1 := hU_all j1 hj1 k2 hk2
    have h2 : ((r : ℝ) + (0.5 : ℝ)) * (2 : ℝ) ^ p ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right (by linarith) hM_nonneg
    exact h1.trans (h2.trans hr1_M_le_p')
  have hP_p' : ‖stepPreTwist p K t1 r x j1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) := by
    have h1 := hP_all j1 hj1 k2 hk2
    have h2 : ((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right (by linarith) hM_nonneg
    exact h1.trans (h2.trans hr1_M_le_p')
  have h053_le : ((r : ℝ) + (0.53 : ℝ)) * (2 : ℝ) ^ p ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p :=
    mul_le_mul_of_nonneg_right (by linarith) hM_nonneg
  have hQ_stage_p' : ‖stepSyntheticStage p K t1 r x s v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    hQ_stage_le.trans (h053_le.trans hr1_M_le_p')
  have hQ_p' : ‖stepSyntheticOut p K t1 r x v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    hQ_le.trans (h053_le.trans hr1_M_le_p')
  have hqPost_p' : ‖stepPostTwist p K t1 r x v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    norm_qPost_le_two_pow_pChild p K t1 r ht1 hr hsize x hx v1 k2 hk2
  exact ⟨hU_p', hP_p', hQ_stage_p', hQ_p', hqPost_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (stepSpread p K t1 r x j1 k2) hU_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (stepPreTwist p K t1 r x j1 k2) hP_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (stepSyntheticStage p K t1 r x s v1 k2) hQ_stage_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (stepSyntheticOut p K t1 r x v1 k2) hQ_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (stepPostTwist p K t1 r x v1 k2) hqPost_p'⟩

/-- **Solver Recurrence Dynamic-Range and `4 * pChild p K`-Bit Word-Width Theorem (`solver_recurrence_word_width_bounds`, `[MS]` §§5.1–5.2)**:
For any step with `t1 * r = 2 ^ K`, `0 < t1`, `0 < r`, `0.4999 ≤ ‖c0‖`, `‖c1‖ ≤ ‖c0‖`, and routed column
`Y : ℕ → ℂ` satisfying `∀ k < t1, ‖Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p`, every recurrence state
`zHomFwdQuantized (2 * pChild p K) c0 c1 u1`, `zPartFwdQuantized (2 * pChild p K) c0 c1 Y u1`, and
`zPartNyqQuantized (2 * pChild p K) c0 Y u1` (`u1 < t1`) has Euclidean norm bounded by `(2 : ℝ) ^ (pChild p K)`
and fixed-point scaled integer coordinates strictly inside `[-2^(4 * pChild p K - 1), 2^(4 * pChild p K - 1))`. -/
theorem solver_recurrence_word_width_bounds
    (p K t1 r : ℕ) (_ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (c0 c1 : ℂ) (hc0_ge : (0.4999 : ℝ) ≤ ‖c0‖) (hc10 : ‖c1‖ ≤ ‖c0‖)
    (Y : ℕ → ℂ) (hY : ∀ k < t1, ‖Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (u1 : ℕ) (hu1 : u1 < t1) :
    ‖zHomFwdQuantized (2 * pChild p K) c0 c1 u1‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖zPartFwdQuantized (2 * pChild p K) c0 c1 Y u1‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖zPartNyqQuantized (2 * pChild p K) c0 Y u1‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    (|realQuantizeInt (2 * pChild p K) (zHomFwdQuantized (2 * pChild p K) c0 c1 u1).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (zHomFwdQuantized (2 * pChild p K) c0 c1 u1).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt (2 * pChild p K) (zPartFwdQuantized (2 * pChild p K) c0 c1 Y u1).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (zPartFwdQuantized (2 * pChild p K) c0 c1 Y u1).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt (2 * pChild p K) (zPartNyqQuantized (2 * pChild p K) c0 Y u1).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (zPartNyqQuantized (2 * pChild p K) c0 Y u1).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) := by
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hM_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hc0_pos : 0 < ‖c0‖ := by linarith
  have ht1_le : t1 ≤ 2 ^ K := by
    rw [← hsize]
    exact Nat.le_mul_of_pos_right t1 hr
  have hu1_le_t1 : (u1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hu1.le
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr (2 * pChild p K) := by
    unfold complexQuantizeMaxErr
    positivity
  have ht1_err : (t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) ≤ (0.0001 : ℝ) :=
    (t1_mul_complexQuantizeMaxErr_two_mul_pChild_le p K t1 ht1_le).2
  have hu1_err : (u1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) ≤ (0.0001 : ℝ) :=
    (mul_le_mul_of_nonneg_right hu1_le_t1 hq_nonneg).trans ht1_err
  have hzHom_le2 : ‖zHomFwdQuantized (2 * pChild p K) c0 c1 u1‖ ≤ 2 := by
    have h1 := norm_zHomFwdQuantized_le (2 * pChild p K) c0 c1 hc0_pos hc10 u1
    linarith
  have hp'_ge12 : 12 ≤ pChild p K := by
    rw [pChild_eq_additive]
    omega
  have h2_le_p' : (2 : ℝ) ≤ (2 : ℝ) ^ (pChild p K) := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (pChild p K) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hzHom_p' : ‖zHomFwdQuantized (2 * pChild p K) c0 c1 u1‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    hzHom_le2.trans h2_le_p'
  have hdiv_c0 : ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) / ‖c0‖ ≤ 3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) := by
    rw [div_le_iff₀ hc0_pos]
    have hpos : 0 ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by positivity
    nlinarith
  have hY_u1 : ∀ k ≤ u1, ‖Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p :=
    fun k hk => hY k (hk.trans_lt hu1)
  have hstep_le :
      (u1 : ℝ) * (((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) / ‖c0‖ + complexQuantizeMaxErr (2 * pChild p K)) ≤
        (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) + 1 := by
    have h1 : (u1 : ℝ) * (((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) / ‖c0‖) ≤
        (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) := by
      calc (u1 : ℝ) * (((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) / ‖c0‖)
          ≤ (u1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) :=
            mul_le_mul_of_nonneg_left hdiv_c0 (Nat.cast_nonneg u1)
        _ ≤ (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) :=
            mul_le_mul_of_nonneg_right hu1_le_t1 (by positivity)
    linarith
  have hzPartF_bound :
      ‖zPartFwdQuantized (2 * pChild p K) c0 c1 Y u1‖ ≤
        (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) + 1 :=
    (norm_zPartFwdQuantized_le (2 * pChild p K) c0 c1 hc0_pos hc10 Y
      ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) u1 hY_u1).trans hstep_le
  have hzPartN_bound :
      ‖zPartNyqQuantized (2 * pChild p K) c0 Y u1‖ ≤
        (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) + 1 :=
    (norm_zPartNyqQuantized_le (2 * pChild p K) c0 hc0_pos Y
      ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) u1 hY_u1).trans hstep_le
  have htr_nat : t1 * (3 * (2 * r + 3)) + 1 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : t1 * (3 * (2 * r + 3)) + 1 = 6 * (t1 * r) + 9 * t1 + 1 := by ring
    have h3 : 6 * (t1 * r) + 9 * t1 + 1 ≤ 16 * 2 ^ K := by omega
    have h4 : 16 * 2 ^ K = 2 ^ (K + 4) := by
      have : (16 : ℕ) = 2 ^ 4 := by decide
      rw [this, ← pow_add]
      congr 1
      omega
    rw [h2]
    exact h3.trans (h4.le.trans (Nat.pow_le_pow_right zero_lt_two (by omega)))
  have htr_real : (t1 : ℝ) * (3 * (2 * (r : ℝ) + 3)) + 1 ≤ (2 : ℝ) ^ (2 * K + 12) := by
    exact_mod_cast htr_nat
  have hprod_le_p' : (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) + 1 ≤ (2 : ℝ) ^ (pChild p K) := by
    have hring : (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) + 1 =
        (t1 : ℝ) * (3 * (2 * (r : ℝ) + 3)) * (2 : ℝ) ^ p + 1 := by ring
    have hle1 : (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) + 1 ≤
        ((t1 : ℝ) * (3 * (2 * (r : ℝ) + 3)) + 1) * (2 : ℝ) ^ p := by
      linarith
    calc (t1 : ℝ) * (3 * ((2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)) + 1
        ≤ ((t1 : ℝ) * (3 * (2 * (r : ℝ) + 3)) + 1) * (2 : ℝ) ^ p := hle1
      _ ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right htr_real hM_nonneg
      _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
      _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]
  have hzPartF_p' : ‖zPartFwdQuantized (2 * pChild p K) c0 c1 Y u1‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    hzPartF_bound.trans hprod_le_p'
  have hzPartN_p' : ‖zPartNyqQuantized (2 * pChild p K) c0 Y u1‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    hzPartN_bound.trans hprod_le_p'
  exact ⟨hzHom_p', hzPartF_p', hzPartN_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (zHomFwdQuantized (2 * pChild p K) c0 c1 u1) hzHom_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (zPartFwdQuantized (2 * pChild p K) c0 c1 Y u1) hzPartF_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (zPartNyqQuantized (2 * pChild p K) c0 Y u1) hzPartN_p'⟩

/-- Tight bound `‖stepPostTwist p K t1 r x v1 k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p` for `k2 < r`. -/
theorem norm_stepPostTwist_le_r_add_one_mul
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    ‖stepPostTwist p K t1 r x v1 k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr_le : r ≤ 2 ^ K := by
    rw [← hsize]
    exact Nat.le_mul_of_pos_left r ht1
  have hU_all : ∀ j < t1, ∀ m < r, ‖stepSpread p K t1 r x j m‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * (2 : ℝ) ^ p :=
    fun j hj m hm => norm_kroneckerSincGaussianSpreadArray_le p K t1 r ht1 hr x ((2 : ℝ) ^ p) hM1 hx j m hj hm
  have hP_all : ∀ j < t1, ∀ m < r, ‖stepPreTwist p K t1 r x j m‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p := by
    intro j hj m hm
    unfold stepPreTwist
    have h := norm_complexQuantize_zetaRoot_mul_le p K r hr_le (m : ℝ) (stepSpread p K t1 r x j m) (0.5 : ℝ)
      ((2 : ℝ) ^ p) (by norm_num) hM1 (hU_all j hj m hm)
    dsimp only at h
    linarith
  obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hlog_err : complexQuantizeMaxErr (2 * pChild p K) * ((Nat.log2 t1 : ℝ) + 1) ≤ (0.01 : ℝ) := by
    have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
    nlinarith
  have hQ_le : ‖stepSyntheticOut p K t1 r x v1 k2‖ ≤ ((r : ℝ) + (0.53 : ℝ)) * (2 : ℝ) ^ p := by
    unfold stepSyntheticOut
    dsimp only
    have hsyn : ‖stepSyntheticStage p K t1 r x (Nat.log2 t1) v1 k2‖ ≤
        ((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p + (Nat.log2 t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) :=
      norm_syntheticFFTRadix2Quantized_le (2 * pChild p K) r (Nat.log2 t1) (r / t1) hr (stepPreTwist p K t1 r x)
        (((r : ℝ) + (0.52 : ℝ)) * (2 : ℝ) ^ p) (fun j hj m hm => hP_all j (ht1_pow ▸ hj) m hm) v1 k2 hk2
    have hquant := norm_complexQuantize_le (2 * pChild p K) (stepSyntheticStage p K t1 r x (Nat.log2 t1) v1 k2)
    have h01 : (0.01 : ℝ) ≤ (0.01 : ℝ) * (2 : ℝ) ^ p := by linarith
    linarith
  unfold stepPostTwist
  have h := norm_complexQuantize_zetaRoot_mul_le p K r hr_le (-(k2 : ℝ))
    (stepSyntheticOut p K t1 r x v1 k2) (0.53 : ℝ) ((2 : ℝ) ^ p) (by norm_num) hM1 hQ_le
  dsimp only at h
  linarith

/-- Routed and quantized child-DFT output `Y(u2, u1)` at recursive step `(p, K, t1, r)`. -/
noncomputable def stepRoutedChildOut (p K t1 r : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (child : QuantizedFastDFTSpec) (x : ℕ → ℂ) (u2 u1 : ℕ) : ℂ :=
  let pSub := 2 * pChild p K
  complexQuantize pSub (sincGaussianFastDFTQuantized child (stepPostTwist p K t1 r x (v1Of u2 u1)) u2)

/-- **Routed Child-DFT Output Dynamic-Range Bound (`norm_stepRoutedChildOut_le`, `[MS]` §§5.1–5.2)**:
For any valid child specification `child` (`hchild : child.Valid`, `hchild_size : child.size = r`,
`hchild_p : child.p = pChild p K`), if `∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p`, then every routed
child output `Y(u2, u1) = stepRoutedChildOut p K t1 r v1Of child x u2 u1` (`u2 < r`) satisfies:
1. `‖stepRoutedChildOut p K t1 r v1Of child x u2 u1‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p`
   (discharging the input hypothesis `hY` of `solver_recurrence_word_width_bounds`),
2. `‖stepRoutedChildOut p K t1 r v1Of child x u2 u1‖ ≤ (2 : ℝ) ^ (pChild p K)`, and
3. Its fixed-point integer coordinates at `2 * pChild p K` fit in `4 * pChild p K` signed bits. -/
theorem norm_stepRoutedChildOut_le
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (v1Of : ℕ → ℕ → ℕ) (child : QuantizedFastDFTSpec)
    (hchild : child.Valid) (hchild_size : child.size = r) (hchild_p : child.p = pChild p K)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (u2 u1 : ℕ) (hu2 : u2 < r) :
    ‖stepRoutedChildOut p K t1 r v1Of child x u2 u1‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p ∧
    ‖stepRoutedChildOut p K t1 r v1Of child x u2 u1‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    (|realQuantizeInt (2 * pChild p K) (stepRoutedChildOut p K t1 r v1Of child x u2 u1).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (stepRoutedChildOut p K t1 r v1Of child x u2 u1).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) := by
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hM_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hMr_ge1 : 1 ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by nlinarith
  set f := stepPostTwist p K t1 r x (v1Of u2 u1)
  have hf_le : ∀ k2 < r, ‖f k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p :=
    fun k2 hk2 => norm_stepPostTwist_le_r_add_one_mul p K t1 r ht1 hr hsize x hx (v1Of u2 u1) k2 hk2
  have hf_child : ∀ k2 < child.size, ‖f k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by
    intro k2 hk2
    exact hf_le k2 (hchild_size ▸ hk2)
  have hdft_zero : dft1D r (fun _ => 0) u2 = 0 := by simp [dft1D]
  have hdft_le : ‖dft1D r f u2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by
    have hsub := norm_dft1D_sub_le r hr f (fun _ => 0) (((r : ℝ) + 1) * (2 : ℝ) ^ p)
      (fun k2 hk2 => by simp [hf_le k2 hk2]) u2
    rwa [hdft_zero, sub_zero] at hsub
  have herr := sincGaussianFastDFTQuantized_error_le child hchild f
    (((r : ℝ) + 1) * (2 : ℝ) ^ p) hMr_ge1 hf_child u2 (hchild_size.symm ▸ hu2)
  rw [hchild_size, hchild_p] at herr
  have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have herr_le : ‖sincGaussianFastDFTQuantized child f u2 - dft1D r f u2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by
    calc ‖sincGaussianFastDFTQuantized child f u2 - dft1D r f u2‖
        ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * (2 : ℝ) ^ p) := herr
      _ ≤ 1 * (((r : ℝ) + 1) * (2 : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_right hpow_le1 (by positivity)
      _ = ((r : ℝ) + 1) * (2 : ℝ) ^ p := one_mul _
  have hqHat_le : ‖sincGaussianFastDFTQuantized child f u2‖ ≤ (2 * (r : ℝ) + 2) * (2 : ℝ) ^ p := by
    have htri := norm_add_le (sincGaussianFastDFTQuantized child f u2 - dft1D r f u2) (dft1D r f u2)
    rw [sub_add_cancel] at htri
    linarith
  set pSub := 2 * pChild p K
  have hq_err_le1 : complexQuantizeMaxErr pSub ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt pSub
    have hp_le1 : (2 : ℝ) ^ (-(pSub : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    linarith
  have hY_le : ‖stepRoutedChildOut p K t1 r v1Of child x u2 u1‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
    unfold stepRoutedChildOut
    dsimp only
    have hq := norm_complexQuantize_le pSub (sincGaussianFastDFTQuantized child f u2)
    linarith
  have hr_le : r ≤ 2 ^ K := by
    rw [← hsize]
    exact Nat.le_mul_of_pos_left r ht1
  have h2r3_nat : 2 * r + 3 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : 2 * r + 3 ≤ 8 * 2 ^ K := by omega
    have h3 : 8 * 2 ^ K = 2 ^ (K + 3) := by
      have : (8 : ℕ) = 2 ^ 3 := by decide
      rw [this, ← pow_add]
      congr 1
      omega
    exact h2.trans (h3.le.trans (Nat.pow_le_pow_right zero_lt_two (by omega)))
  have h2r3_real : 2 * (r : ℝ) + 3 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast h2r3_nat
  have hY_p' : ‖stepRoutedChildOut p K t1 r v1Of child x u2 u1‖ ≤ (2 : ℝ) ^ (pChild p K) := by
    calc ‖stepRoutedChildOut p K t1 r v1Of child x u2 u1‖
        ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := hY_le
      _ ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p := mul_le_mul_of_nonneg_right h2r3_real hM_nonneg
      _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
      _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]
  exact ⟨hY_le, hY_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (stepRoutedChildOut p K t1 r v1Of child x u2 u1) hY_p'⟩

/-- **Backward Recurrence Dynamic-Range and `4 * pChild p K`-Bit Word-Width Theorem (`solver_bwd_recurrence_word_width_bounds`, `[MS]` §§5.1–5.2)**:
For any step with `t1 * r = 2 ^ K`, `0 < t1`, `0 < r`, `0.4999 ≤ ‖c1‖`, `‖c0‖ ≤ ‖c1‖`, and routed column
`Y : ℕ → ℂ` satisfying `∀ k < t1, ‖Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p`, every backward recurrence
state `zHomBwdQuantized (2 * pChild p K) c0 c1 d` and `zPartBwdQuantized (2 * pChild p K) t1 c0 c1 Y d`
(`d < t1`) has Euclidean norm bounded by `(2 : ℝ) ^ (pChild p K)` and fixed-point integer coordinates
strictly inside `[-2^(4 * pChild p K - 1), 2^(4 * pChild p K - 1))`. -/
theorem solver_bwd_recurrence_word_width_bounds
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (c0 c1 : ℂ) (hc1_ge : (0.4999 : ℝ) ≤ ‖c1‖) (hc01 : ‖c0‖ ≤ ‖c1‖)
    (Y : ℕ → ℂ) (hY : ∀ k < t1, ‖Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (d : ℕ) (hd : d < t1) :
    ‖zHomBwdQuantized (2 * pChild p K) c0 c1 d‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖zPartBwdQuantized (2 * pChild p K) t1 c0 c1 Y d‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    (|realQuantizeInt (2 * pChild p K) (zHomBwdQuantized (2 * pChild p K) c0 c1 d).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (zHomBwdQuantized (2 * pChild p K) c0 c1 d).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt (2 * pChild p K) (zPartBwdQuantized (2 * pChild p K) t1 c0 c1 Y d).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt (2 * pChild p K) (zPartBwdQuantized (2 * pChild p K) t1 c0 c1 Y d).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) := by
  have hY_rev : ∀ k < t1, ‖bwdRevRHS t1 Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
    intro k hk
    unfold bwdRevRHS
    split_ifs with hk0
    · exact hY 0 ht1
    · exact hY (t1 - k) (by omega)
  have h := solver_recurrence_word_width_bounds p K t1 r ht1 hr hsize c1 c0 hc1_ge hc01 (bwdRevRHS t1 Y) hY_rev d hd
  rw [zPartBwdQuantized_eq_zPartFwdQuantized_rev]
  unfold zHomBwdQuantized
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- **Solver Boundary Scalars and Outputs `4 * pChild p K`-Bit Word-Width Theorem (`solver_outputs_word_width_bounds`, `[MS]` §§5.1–5.2)**:
Under the passband conditioning invariants of `[MS]` §§5.1–5.2 (`0.4999 ≤ ‖c0‖ ≤ 1`, `‖c1‖ ≤ ‖c0‖`, and
`0.4 ≤ ‖c0 + c1 * zHomFwdQuantized (2 * pChild p K) c0 c1 (t1 - 1)‖` in the forward regime;
symmetrically for `(c1_bwd, c0_bwd)` in the backward regime; and `0.4999 ≤ ‖c0_nyq‖`,
`‖alt_q‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p` at Nyquist), the boundary scalars `Z0`, `Z_last`, `diff`
and the solver outputs `solveBidiagonalFwdQuantized`, `solveBidiagonalBwdQuantized`, and
`solveNyquistQuantized` all have Euclidean norm bounded by `(2 : ℝ) ^ (pChild p K)` and fit in a
signed integer word of width `4 * pChild p K` bits. -/
theorem solver_outputs_word_width_bounds
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (c0 c1 : ℂ) (hc0_ge : (0.4999 : ℝ) ≤ ‖c0‖) (hc0_le1 : ‖c0‖ ≤ 1) (hc10 : ‖c1‖ ≤ ‖c0‖)
    (hDq : (0.4 : ℝ) ≤ ‖c0 + c1 * zHomFwdQuantized (2 * pChild p K) c0 c1 (t1 - 1)‖)
    (Y : ℕ → ℂ) (hY : ∀ k < t1, ‖Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (alt_q : ℂ) (halt_q : ‖alt_q‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (u1 : ℕ) (hu1 : u1 < t1) :
    let pSub := 2 * pChild p K
    let Z0 := complexQuantize pSub
      ((Y 0 - c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1)) /
        (c0 + c1 * zHomFwdQuantized pSub c0 c1 (t1 - 1)))
    let alt_part := ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyqQuantized pSub c0 Y v
    let diff := complexQuantize pSub ((alt_q - alt_part) / (t1 : ℂ))
    ‖Z0‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖solveBidiagonalFwdQuantized pSub t1 c0 c1 Y u1‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖diff‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    ‖solveNyquistQuantized pSub t1 c0 Y alt_q u1‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    (|realQuantizeInt pSub (solveBidiagonalFwdQuantized pSub t1 c0 c1 Y u1).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt pSub (solveBidiagonalFwdQuantized pSub t1 c0 c1 Y u1).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) ∧
    (|realQuantizeInt pSub (solveNyquistQuantized pSub t1 c0 Y alt_q u1).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt pSub (solveNyquistQuantized pSub t1 c0 Y alt_q u1).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) := by
  dsimp only
  set pSub := 2 * pChild p K
  set M_Y := (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hM_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hMY_ge1 : 1 ≤ M_Y := by dsimp [M_Y]; nlinarith
  have hc0_pos : 0 < ‖c0‖ := by linarith
  have hc1_le1 : ‖c1‖ ≤ 1 := hc10.trans hc0_le1
  have ht1_le : t1 ≤ 2 ^ K := by
    rw [← hsize]
    exact Nat.le_mul_of_pos_right t1 hr
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr pSub := by
    unfold complexQuantizeMaxErr
    positivity
  have hq_le1 : complexQuantizeMaxErr pSub ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt pSub
    have hp_le1 : (2 : ℝ) ^ (-(pSub : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    nlinarith
  have ht1_err : (t1 : ℝ) * complexQuantizeMaxErr pSub ≤ (0.0001 : ℝ) :=
    (t1_mul_complexQuantizeMaxErr_two_mul_pChild_le p K t1 ht1_le).2
  have hdiv_c0 : M_Y / ‖c0‖ ≤ 3 * M_Y := by
    rw [div_le_iff₀ hc0_pos]
    nlinarith
  have hzPartF_all : ∀ v < t1, ‖zPartFwdQuantized pSub c0 c1 Y v‖ ≤ (t1 : ℝ) * (3 * M_Y) + 1 := by
    intro v hv
    have hv_le : (v : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hv.le
    have hv_err : (v : ℝ) * complexQuantizeMaxErr pSub ≤ (0.0001 : ℝ) :=
      (mul_le_mul_of_nonneg_right hv_le hq_nonneg).trans ht1_err
    have h1 := norm_zPartFwdQuantized_le pSub c0 c1 hc0_pos hc10 Y M_Y v (fun k hk => hY k (hk.trans_lt hv))
    have h2 : (v : ℝ) * (M_Y / ‖c0‖) ≤ (t1 : ℝ) * (3 * M_Y) := by
      calc (v : ℝ) * (M_Y / ‖c0‖) ≤ (v : ℝ) * (3 * M_Y) :=
            mul_le_mul_of_nonneg_left hdiv_c0 (Nat.cast_nonneg v)
        _ ≤ (t1 : ℝ) * (3 * M_Y) := mul_le_mul_of_nonneg_right hv_le (by positivity)
    linarith
  have hzPartN_all : ∀ v < t1, ‖zPartNyqQuantized pSub c0 Y v‖ ≤ (t1 : ℝ) * (3 * M_Y) + 1 := by
    intro v hv
    have hv_le : (v : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hv.le
    have hv_err : (v : ℝ) * complexQuantizeMaxErr pSub ≤ (0.0001 : ℝ) :=
      (mul_le_mul_of_nonneg_right hv_le hq_nonneg).trans ht1_err
    have h1 := norm_zPartNyqQuantized_le pSub c0 hc0_pos Y M_Y v (fun k hk => hY k (hk.trans_lt hv))
    have h2 : (v : ℝ) * (M_Y / ‖c0‖) ≤ (t1 : ℝ) * (3 * M_Y) := by
      calc (v : ℝ) * (M_Y / ‖c0‖) ≤ (v : ℝ) * (3 * M_Y) :=
            mul_le_mul_of_nonneg_left hdiv_c0 (Nat.cast_nonneg v)
        _ ≤ (t1 : ℝ) * (3 * M_Y) := mul_le_mul_of_nonneg_right hv_le (by positivity)
    linarith
  have hzHom_u1 : ‖zHomFwdQuantized pSub c0 c1 u1‖ ≤ 2 := by
    have hu1_le : (u1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hu1.le
    have hu1_err : (u1 : ℝ) * complexQuantizeMaxErr pSub ≤ (0.0001 : ℝ) :=
      (mul_le_mul_of_nonneg_right hu1_le hq_nonneg).trans ht1_err
    have h1 := norm_zHomFwdQuantized_le pSub c0 c1 hc0_pos hc10 u1
    linarith
  set Z0 := complexQuantize pSub
    ((Y 0 - c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1)) /
      (c0 + c1 * zHomFwdQuantized pSub c0 c1 (t1 - 1)))
  have ht1_nonneg : (0 : ℝ) ≤ (t1 : ℝ) := Nat.cast_nonneg t1
  have ht1_MY : 0 ≤ (t1 : ℝ) * M_Y := by positivity
  have hZ0_bound : ‖Z0‖ ≤ (8 * (t1 : ℝ) + 7) * M_Y := by
    have hY0 := hY 0 ht1
    have hzP_last := hzPartF_all (t1 - 1) (by omega)
    have hmul_c1 : ‖c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1)‖ ≤ (t1 : ℝ) * (3 * M_Y) + 1 := by
      rw [norm_mul]
      calc ‖c1‖ * ‖zPartFwdQuantized pSub c0 c1 Y (t1 - 1)‖
          ≤ 1 * ((t1 : ℝ) * (3 * M_Y) + 1) := mul_le_mul hc1_le1 hzP_last (norm_nonneg _) zero_le_one
        _ = (t1 : ℝ) * (3 * M_Y) + 1 := one_mul _
    have hnum_le : ‖Y 0 - c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1)‖ ≤ M_Y + (t1 : ℝ) * (3 * M_Y) + 1 := by
      have htri := norm_sub_le (Y 0) (c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1))
      linarith
    have hDq_pos : 0 < ‖c0 + c1 * zHomFwdQuantized pSub c0 c1 (t1 - 1)‖ := by linarith
    have hquot_le :
        ‖(Y 0 - c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1)) /
          (c0 + c1 * zHomFwdQuantized pSub c0 c1 (t1 - 1))‖ ≤
          (2.5 : ℝ) * (M_Y + (t1 : ℝ) * (3 * M_Y) + 1) := by
      rw [norm_div, div_le_iff₀ hDq_pos]
      calc ‖Y 0 - c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1)‖
          ≤ M_Y + (t1 : ℝ) * (3 * M_Y) + 1 := hnum_le
        _ = (2.5 : ℝ) * (M_Y + (t1 : ℝ) * (3 * M_Y) + 1) * (0.4 : ℝ) := by ring
        _ ≤ (2.5 : ℝ) * (M_Y + (t1 : ℝ) * (3 * M_Y) + 1) *
              ‖c0 + c1 * zHomFwdQuantized pSub c0 c1 (t1 - 1)‖ :=
            mul_le_mul_of_nonneg_left hDq (by positivity)
    have hq := norm_complexQuantize_le pSub
      ((Y 0 - c1 * zPartFwdQuantized pSub c0 c1 Y (t1 - 1)) /
        (c0 + c1 * zHomFwdQuantized pSub c0 c1 (t1 - 1)))
    linarith [hquot_le, hq, hq_le1, hMY_ge1, ht1_MY]
  have hFwd_bound : ‖solveBidiagonalFwdQuantized pSub t1 c0 c1 Y u1‖ ≤ (20 * (t1 : ℝ) + 16) * M_Y := by
    unfold solveBidiagonalFwdQuantized
    have hzP_u1 := hzPartF_all u1 hu1
    have hmul_Z0 : ‖Z0 * zHomFwdQuantized pSub c0 c1 u1‖ ≤ 2 * ((8 * (t1 : ℝ) + 7) * M_Y) := by
      rw [norm_mul, mul_comm]
      exact mul_le_mul hzHom_u1 hZ0_bound (norm_nonneg _) (by positivity)
    have htri := norm_add_le (zPartFwdQuantized pSub c0 c1 Y u1) (Z0 * zHomFwdQuantized pSub c0 c1 u1)
    have hq := norm_complexQuantize_le pSub (zPartFwdQuantized pSub c0 c1 Y u1 + Z0 * zHomFwdQuantized pSub c0 c1 u1)
    linarith [hzP_u1, hmul_Z0, htri, hq, hq_le1, hMY_ge1, ht1_MY]
  set alt_part := ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * zPartNyqQuantized pSub c0 Y v
  set diff := complexQuantize pSub ((alt_q - alt_part) / (t1 : ℂ))
  have halt_part_le : ‖alt_part‖ ≤ (t1 : ℝ) * ((t1 : ℝ) * (3 * M_Y) + 1) := by
    calc ‖alt_part‖
        ≤ ∑ v ∈ Finset.range t1, ‖(-1 : ℂ) ^ v * zPartNyqQuantized pSub c0 Y v‖ := norm_sum_le _ _
      _ ≤ ∑ _v ∈ Finset.range t1, ((t1 : ℝ) * (3 * M_Y) + 1) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact hzPartN_all v (Finset.mem_range.mp hv)
      _ = (t1 : ℝ) * ((t1 : ℝ) * (3 * M_Y) + 1) := by simp; ring
  have ht1_ge1 : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1
  have ht1_pos_real : (0 : ℝ) < (t1 : ℝ) := by linarith
  have hnorm_t1 : ‖(t1 : ℂ)‖ = (t1 : ℝ) := by
    rw [Complex.norm_natCast]
  have hdiff_bound : ‖diff‖ ≤ (3 * (t1 : ℝ) + 3) * M_Y := by
    have htri := norm_sub_le alt_q alt_part
    have hquot : ‖(alt_q - alt_part) / (t1 : ℂ)‖ ≤ M_Y + ((t1 : ℝ) * (3 * M_Y) + 1) := by
      rw [norm_div, hnorm_t1, div_le_iff₀ ht1_pos_real]
      have hM_le_t1M : M_Y ≤ (t1 : ℝ) * M_Y := by
        calc M_Y = 1 * M_Y := (one_mul M_Y).symm
          _ ≤ (t1 : ℝ) * M_Y := mul_le_mul_of_nonneg_right ht1_ge1 (by positivity)
      linarith [htri, halt_q, halt_part_le, hM_le_t1M]
    have hq := norm_complexQuantize_le pSub ((alt_q - alt_part) / (t1 : ℂ))
    linarith [hquot, hq, hq_le1, hMY_ge1, ht1_MY]
  have hNyq_bound : ‖solveNyquistQuantized pSub t1 c0 Y alt_q u1‖ ≤ (20 * (t1 : ℝ) + 16) * M_Y := by
    unfold solveNyquistQuantized
    have hzN_u1 := hzPartN_all u1 hu1
    have hmul_diff : ‖(-1 : ℂ) ^ u1 * diff‖ = ‖diff‖ := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have htri := norm_add_le (zPartNyqQuantized pSub c0 Y u1) ((-1 : ℂ) ^ u1 * diff)
    have hq := norm_complexQuantize_le pSub (zPartNyqQuantized pSub c0 Y u1 + (-1 : ℂ) ^ u1 * diff)
    linarith [hzN_u1, hmul_diff, hdiff_bound, htri, hq, hq_le1, hMY_ge1, ht1_MY]
  have h20_nat : (20 * t1 + 16) * (2 * r + 3) ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have hr_le : r ≤ 2 ^ K := by
      rw [← hsize]
      exact Nat.le_mul_of_pos_left r ht1
    have h2 : (20 * t1 + 16) * (2 * r + 3) = 40 * (t1 * r) + 60 * t1 + 32 * r + 48 := by ring
    have h3 : 40 * (t1 * r) + 60 * t1 + 32 * r + 48 ≤ 256 * 2 ^ K := by omega
    have h4 : 256 * 2 ^ K = 2 ^ (K + 8) := by
      have : (256 : ℕ) = 2 ^ 8 := by decide
      rw [this, ← pow_add]
      congr 1
      omega
    rw [h2]
    exact h3.trans (h4.le.trans (Nat.pow_le_pow_right zero_lt_two (by omega)))
  have h20_real : (20 * (t1 : ℝ) + 16) * (2 * (r : ℝ) + 3) ≤ (2 : ℝ) ^ (2 * K + 12) := by
    exact_mod_cast h20_nat
  have h20_le_p' : (20 * (t1 : ℝ) + 16) * M_Y ≤ (2 : ℝ) ^ (pChild p K) := by
    calc (20 * (t1 : ℝ) + 16) * M_Y
        = ((20 * (t1 : ℝ) + 16) * (2 * (r : ℝ) + 3)) * (2 : ℝ) ^ p := by dsimp [M_Y]; ring
      _ ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p := mul_le_mul_of_nonneg_right h20_real hM_nonneg
      _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
      _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]
  have hZ0_p' : ‖Z0‖ ≤ (2 : ℝ) ^ (pChild p K) := by
    have hle : (8 * (t1 : ℝ) + 7) * M_Y ≤ (20 * (t1 : ℝ) + 16) * M_Y := by linarith [ht1_MY, hMY_ge1]
    exact hZ0_bound.trans (hle.trans h20_le_p')
  have hFwd_p' : ‖solveBidiagonalFwdQuantized pSub t1 c0 c1 Y u1‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    hFwd_bound.trans h20_le_p'
  have hdiff_p' : ‖diff‖ ≤ (2 : ℝ) ^ (pChild p K) := by
    have hle : (3 * (t1 : ℝ) + 3) * M_Y ≤ (20 * (t1 : ℝ) + 16) * M_Y := by linarith [ht1_MY, hMY_ge1]
    exact hdiff_bound.trans (hle.trans h20_le_p')
  have hNyq_p' : ‖solveNyquistQuantized pSub t1 c0 Y alt_q u1‖ ≤ (2 : ℝ) ^ (pChild p K) :=
    hNyq_bound.trans h20_le_p'
  exact ⟨hZ0_p', hFwd_p', hdiff_p', hNyq_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (solveBidiagonalFwdQuantized pSub t1 c0 c1 Y u1) hFwd_p',
    realQuantizeInt_mem_four_mul_pChild_word p K (solveNyquistQuantized pSub t1 c0 Y alt_q u1) hNyq_p'⟩

/-- **Backward Solver Output `4 * pChild p K`-Bit Word-Width Theorem (`solveBidiagonalBwdQuantized_word_width_bounds`, `[MS]` §§5.1–5.2)**:
By reversal symmetry (`solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev`), when
`0.4999 ≤ ‖c1‖ ≤ 1`, `‖c0‖ ≤ ‖c1‖`, and `0.4 ≤ ‖c1 + c0 * zHomBwdQuantized (2 * pChild p K) c0 c1 (t1 - 1)‖`,
the backward solver output `solveBidiagonalBwdQuantized (2 * pChild p K) t1 c0 c1 Y u1` has
Euclidean norm bounded by `(2 : ℝ) ^ (pChild p K)` and fits in `4 * pChild p K` signed bits. -/
theorem solveBidiagonalBwdQuantized_word_width_bounds
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (c0 c1 : ℂ) (hc1_ge : (0.4999 : ℝ) ≤ ‖c1‖) (hc1_le1 : ‖c1‖ ≤ 1) (hc01 : ‖c0‖ ≤ ‖c1‖)
    (hDq : (0.4 : ℝ) ≤ ‖c1 + c0 * zHomBwdQuantized (2 * pChild p K) c0 c1 (t1 - 1)‖)
    (Y : ℕ → ℂ) (hY : ∀ k < t1, ‖Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (u1 : ℕ) (hu1 : u1 < t1) :
    let pSub := 2 * pChild p K
    ‖solveBidiagonalBwdQuantized pSub t1 c0 c1 Y u1‖ ≤ (2 : ℝ) ^ (pChild p K) ∧
    (|realQuantizeInt pSub (solveBidiagonalBwdQuantized pSub t1 c0 c1 Y u1).re| < (2 : ℤ) ^ (4 * pChild p K - 1) ∧
     |realQuantizeInt pSub (solveBidiagonalBwdQuantized pSub t1 c0 c1 Y u1).im| < (2 : ℤ) ^ (4 * pChild p K - 1)) := by
  dsimp only
  rw [solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev]
  have hY_rev : ∀ k < t1, ‖bwdRevRHS t1 Y k‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
    intro k hk
    unfold bwdRevRHS
    split_ifs with hk0
    · exact hY 0 ht1
    · exact hY (t1 - k) (by omega)
  have h0_le : ‖(0 : ℂ)‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
    rw [norm_zero]
    positivity
  have h := solver_outputs_word_width_bounds p K t1 r ht1 hr hsize c1 c0 hc1_ge hc1_le1 hc01 hDq
    (bwdRevRHS t1 Y) hY_rev 0 h0_le (t1 - 1 - u1) (by omega)
  exact ⟨h.2.1, h.2.2.2.2.1⟩

/-- **Raw Unrounded Spread Coordinate Word-Width Theorem (`raw_spread_coord_mem_six_mul_pChild_word`, `[MS]` §6.2)**:
At any recursive step `(p, K, t1, r)` with `0 < t1`, `0 < r`, `t1 * r = 2 ^ K`, and
`∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p`, if `uRaw : ℤ × ℤ` is the unrounded integer spread pair
at scale `2^(2 * pSub) = 2^(4 * pChild p K)` produced by `computableSpreadRowContiguousWithCost`
or `computableSpreadRowExact` before `gPreTwistU`
(`stepSpread p K t1 r x j1 k2 = ⟨uRaw.1 / (2^pSub * 2^pSub), uRaw.2 / (2^pSub * 2^pSub)⟩`),
then its integer coordinates satisfy:
`|uRaw.1| < (2 : ℤ) ^ (6 * pChild p K - 1)` and `|uRaw.2| < (2 : ℤ) ^ (6 * pChild p K - 1)`,
fitting strictly inside a signed integer word of width `6 * pChild p K` bits (`O(p')` bits). -/
theorem raw_spread_coord_mem_six_mul_pChild_word
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (uRaw : ℤ × ℤ)
    (huRaw :
      (⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ (2 * pChild p K) * (2 : ℝ) ^ (2 * pChild p K)),
        (uRaw.2 : ℝ) / ((2 : ℝ) ^ (2 * pChild p K) * (2 : ℝ) ^ (2 * pChild p K))⟩ : ℂ) =
        stepSpread p K t1 r x j1 k2) :
    |uRaw.1| < (2 : ℤ) ^ (6 * pChild p K - 1) ∧
    |uRaw.2| < (2 : ℤ) ^ (6 * pChild p K - 1) := by
  set p' := pChild p K
  have hp'_ge12 : 12 ≤ p' := by
    dsimp [p']
    rw [pChild_eq_additive]
    omega
  have hnorm : ‖stepSpread p K t1 r x j1 k2‖ ≤ (2 : ℝ) ^ p' :=
    (step_intermediate_word_width_bounds p K t1 r ht1 hr hsize x hx j1 0 k2 0 hj1 hk2 (Nat.zero_le _)).1
  rw [← huRaw] at hnorm
  have hre := (Complex.abs_re_le_norm
    (⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ (2 * p') * (2 : ℝ) ^ (2 * p')),
      (uRaw.2 : ℝ) / ((2 : ℝ) ^ (2 * p') * (2 : ℝ) ^ (2 * p'))⟩ : ℂ)).trans hnorm
  have him := (Complex.abs_im_le_norm
    (⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ (2 * p') * (2 : ℝ) ^ (2 * p')),
      (uRaw.2 : ℝ) / ((2 : ℝ) ^ (2 * p') * (2 : ℝ) ^ (2 * p'))⟩ : ℂ)).trans hnorm
  dsimp only at hre him
  have hscale_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * p') * (2 : ℝ) ^ (2 * p') := by positivity
  rw [abs_div, abs_of_pos hscale_pos, div_le_iff₀ hscale_pos] at hre him
  have hscale_combine :
      (2 : ℝ) ^ p' * ((2 : ℝ) ^ (2 * p') * (2 : ℝ) ^ (2 * p')) = (2 : ℝ) ^ (5 * p') := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  rw [hscale_combine] at hre him
  have h5_lt : (2 : ℝ) ^ (5 * p') < (2 : ℝ) ^ (6 * p' - 1) :=
    pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)
  have hre_lt : |(uRaw.1 : ℝ)| < (2 : ℝ) ^ (6 * p' - 1) := hre.trans_lt h5_lt
  have him_lt : |(uRaw.2 : ℝ)| < (2 : ℝ) ^ (6 * p' - 1) := him.trans_lt h5_lt
  rw [← Int.cast_abs] at hre_lt him_lt
  exact ⟨by exact_mod_cast hre_lt, by exact_mod_cast him_lt⟩

/-- **Pre-Twist `gPreTwistU` Raw Temporaries Word-Width Bound (`gPreTwistU_raw_temporaries_word_width_bound`, `[MS]` §3.2)**:
When the quantized twiddle `tw : ℤ × ℤ` fits in `4 * pChild p K` signed bits
(`|tw.1|, |tw.2| < 2^(4 * pChild p K - 1)`) and the raw spread pair `uRaw : ℤ × ℤ` fits in
`6 * pChild p K` signed bits (`|uRaw.1|, |uRaw.2| < 2^(6 * pChild p K - 1)`), the unrounded
numerator temporaries `tw.1 * uRaw.1 - tw.2 * uRaw.2` and `tw.1 * uRaw.2 + tw.2 * uRaw.1`
inside `gPreTwistU` satisfy `< 2^(10 * pChild p K - 1)` (`10 * pChild p K` signed bits, `O(p')` bits). -/
theorem gPreTwistU_raw_temporaries_word_width_bound
    (p K : ℕ) (tw uRaw : ℤ × ℤ)
    (htw1 : |tw.1| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (htw2 : |tw.2| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hu1 : |uRaw.1| < (2 : ℤ) ^ (6 * pChild p K - 1))
    (hu2 : |uRaw.2| < (2 : ℤ) ^ (6 * pChild p K - 1)) :
    |tw.1 * uRaw.1 - tw.2 * uRaw.2| < (2 : ℤ) ^ (10 * pChild p K - 1) ∧
    |tw.1 * uRaw.2 + tw.2 * uRaw.1| < (2 : ℤ) ^ (10 * pChild p K - 1) := by
  set p' := pChild p K
  have hp'_ge12 : 12 ≤ p' := by
    dsimp [p']
    rw [pChild_eq_additive]
    omega
  set A : ℤ := (2 : ℤ) ^ (4 * p' - 1)
  set B : ℤ := (2 : ℤ) ^ (6 * p' - 1)
  have h2AB : 2 * (A * B) = (2 : ℤ) ^ (10 * p' - 1) := by
    dsimp [A, B]
    have h2 : (2 : ℤ) * ((2 : ℤ) ^ (4 * p' - 1) * (2 : ℤ) ^ (6 * p' - 1)) =
        (2 : ℤ) ^ 1 * (2 : ℤ) ^ (4 * p' - 1) * (2 : ℤ) ^ (6 * p' - 1) := by ring
    rw [h2, ← pow_add, ← pow_add]
    congr 1
    omega
  have hm11 : |tw.1 * uRaw.1| < A * B := by
    rw [abs_mul]
    exact mul_lt_mul'' htw1 hu1 (abs_nonneg _) (abs_nonneg _)
  have hm22 : |tw.2 * uRaw.2| < A * B := by
    rw [abs_mul]
    exact mul_lt_mul'' htw2 hu2 (abs_nonneg _) (abs_nonneg _)
  have hm12 : |tw.1 * uRaw.2| < A * B := by
    rw [abs_mul]
    exact mul_lt_mul'' htw1 hu2 (abs_nonneg _) (abs_nonneg _)
  have hm21 : |tw.2 * uRaw.1| < A * B := by
    rw [abs_mul]
    exact mul_lt_mul'' htw2 hu1 (abs_nonneg _) (abs_nonneg _)
  have hsub := abs_sub (tw.1 * uRaw.1) (tw.2 * uRaw.2)
  have hadd := abs_add_le (tw.1 * uRaw.2) (tw.2 * uRaw.1)
  exact ⟨by linarith, by linarith⟩

/-- **Solver `gRatioQuantize` & `gDivQuantizeUnscaled` Raw Temporaries Word-Width Bound
(`gRatioQuantize_raw_temporaries_word_width_bound`, `[MS]` §3.2)**:
When all 6 input pairs `y, c1, zPart, c0, d1, zHom : ℤ × ℤ` to `gRatioQuantize (2 * pChild p K)`
fit in `4 * pChild p K` signed bits (`|coord| < 2^(4 * pChild p K - 1)`), the intermediate
numerator/denominator pairs `N, D : ℤ × ℤ` in `gRatioQuantize` satisfy
`|N.1|, |N.2|, |D.1|, |D.2| < 2^(9 * pChild p K - 1)` (`9 * p'` signed bits) and the unrounded
division temporaries `numRe, numIm, den` in `gDivQuantizeUnscaled` satisfy
`|numRe|, |numIm|, |den| < 2^(22 * pChild p K - 1)` (`O(p')` signed bits, matching `mulBitCost (4 * p')`
up to a constant factor). -/
theorem gRatioQuantize_raw_temporaries_word_width_bound
    (p K : ℕ) (y c1 zPart c0 d1 zHom : ℤ × ℤ)
    (hy1 : |y.1| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hy2 : |y.2| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hc1_1 : |c1.1| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hc1_2 : |c1.2| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hzP1 : |zPart.1| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hzP2 : |zPart.2| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hc0_1 : |c0.1| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hc0_2 : |c0.2| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hd1_1 : |d1.1| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hd1_2 : |d1.2| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hzH1 : |zHom.1| < (2 : ℤ) ^ (4 * pChild p K - 1))
    (hzH2 : |zHom.2| < (2 : ℤ) ^ (4 * pChild p K - 1)) :
    let p' := pChild p K
    let S : ℤ := (2 : ℤ) ^ (2 * p' + 2)
    let N1 : ℤ := y.1 * S - (c1.1 * zPart.1 - c1.2 * zPart.2)
    let N2 : ℤ := y.2 * S - (c1.1 * zPart.2 + c1.2 * zPart.1)
    let D1 : ℤ := c0.1 * S + (d1.1 * zHom.1 - d1.2 * zHom.2)
    let D2 : ℤ := c0.2 * S + (d1.1 * zHom.2 + d1.2 * zHom.1)
    let numRe : ℤ := (N1 * D1 + N2 * D2) * S
    let numIm : ℤ := (N2 * D1 - N1 * D2) * S
    let den : ℤ := D1 * D1 + D2 * D2
    |N1| < (2 : ℤ) ^ (9 * p' - 1) ∧
    |N2| < (2 : ℤ) ^ (9 * p' - 1) ∧
    |D1| < (2 : ℤ) ^ (9 * p' - 1) ∧
    |D2| < (2 : ℤ) ^ (9 * p' - 1) ∧
    |numRe| < (2 : ℤ) ^ (22 * p' - 1) ∧
    |numIm| < (2 : ℤ) ^ (22 * p' - 1) ∧
    |den| < (2 : ℤ) ^ (22 * p' - 1) := by
  dsimp only
  set p' := pChild p K
  have hp'_ge12 : 12 ≤ p' := by
    dsimp [p']
    rw [pChild_eq_additive]
    omega
  set A : ℤ := (2 : ℤ) ^ (4 * p' - 1)
  set S : ℤ := (2 : ℤ) ^ (2 * p' + 2)
  have hS_pos : 0 < S := by positivity
  have hS_le_A : S ≤ A := by
    dsimp [S, A]
    exact_mod_cast Nat.pow_le_pow_right zero_lt_two (by omega)
  have h3AA_lt : 3 * (A * A) < (2 : ℤ) ^ (9 * p' - 1) := by
    have h4 : 4 * (A * A) = (2 : ℤ) ^ (8 * p') := by
      dsimp [A]
      have h4_eq : (4 : ℤ) * ((2 : ℤ) ^ (4 * p' - 1) * (2 : ℤ) ^ (4 * p' - 1)) =
          (2 : ℤ) ^ 2 * (2 : ℤ) ^ (4 * p' - 1) * (2 : ℤ) ^ (4 * p' - 1) := by ring
      rw [h4_eq, ← pow_add, ← pow_add]
      congr 1
      omega
    have hpow_lt : (2 : ℤ) ^ (8 * p') < (2 : ℤ) ^ (9 * p' - 1) := by
      exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hAA_pos : 0 < A * A := by positivity
    linarith
  have hprod_lt (u v : ℤ) (hu : |u| < A) (hv : |v| < A) : |u * v| < A * A := by
    rw [abs_mul]
    exact mul_lt_mul'' hu hv (abs_nonneg _) (abs_nonneg _)
  have hS_abs : |S| < A := by
    rw [abs_of_pos hS_pos]
    dsimp [S, A]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  have hN1 : |y.1 * S - (c1.1 * zPart.1 - c1.2 * zPart.2)| < (2 : ℤ) ^ (9 * p' - 1) := by
    have h1 := hprod_lt y.1 S hy1 hS_abs
    have h2 := hprod_lt c1.1 zPart.1 hc1_1 hzP1
    have h3 := hprod_lt c1.2 zPart.2 hc1_2 hzP2
    have h4 := abs_sub (y.1 * S) (c1.1 * zPart.1 - c1.2 * zPart.2)
    have h5 := abs_sub (c1.1 * zPart.1) (c1.2 * zPart.2)
    linarith
  have hN2 : |y.2 * S - (c1.1 * zPart.2 + c1.2 * zPart.1)| < (2 : ℤ) ^ (9 * p' - 1) := by
    have h1 := hprod_lt y.2 S hy2 hS_abs
    have h2 := hprod_lt c1.1 zPart.2 hc1_1 hzP2
    have h3 := hprod_lt c1.2 zPart.1 hc1_2 hzP1
    have h4 := abs_sub (y.2 * S) (c1.1 * zPart.2 + c1.2 * zPart.1)
    have h5 := abs_add_le (c1.1 * zPart.2) (c1.2 * zPart.1)
    linarith
  have hD1 : |c0.1 * S + (d1.1 * zHom.1 - d1.2 * zHom.2)| < (2 : ℤ) ^ (9 * p' - 1) := by
    have h1 := hprod_lt c0.1 S hc0_1 hS_abs
    have h2 := hprod_lt d1.1 zHom.1 hd1_1 hzH1
    have h3 := hprod_lt d1.2 zHom.2 hd1_2 hzH2
    have h4 := abs_add_le (c0.1 * S) (d1.1 * zHom.1 - d1.2 * zHom.2)
    have h5 := abs_sub (d1.1 * zHom.1) (d1.2 * zHom.2)
    linarith
  have hD2 : |c0.2 * S + (d1.1 * zHom.2 + d1.2 * zHom.1)| < (2 : ℤ) ^ (9 * p' - 1) := by
    have h1 := hprod_lt c0.2 S hc0_2 hS_abs
    have h2 := hprod_lt d1.1 zHom.2 hd1_1 hzH2
    have h3 := hprod_lt d1.2 zHom.1 hd1_2 hzH1
    have h4 := abs_add_le (c0.2 * S) (d1.1 * zHom.2 + d1.2 * zHom.1)
    have h5 := abs_add_le (d1.1 * zHom.2) (d1.2 * zHom.1)
    linarith
  set B : ℤ := (2 : ℤ) ^ (9 * p' - 1)
  set N1 := y.1 * S - (c1.1 * zPart.1 - c1.2 * zPart.2)
  set N2 := y.2 * S - (c1.1 * zPart.2 + c1.2 * zPart.1)
  set D1 := c0.1 * S + (d1.1 * zHom.1 - d1.2 * zHom.2)
  set D2 := c0.2 * S + (d1.1 * zHom.2 + d1.2 * zHom.1)
  have h2BBS_lt : 2 * (B * B) * S < (2 : ℤ) ^ (22 * p' - 1) := by
    have hcomb : 2 * (B * B) * S = (2 : ℤ) ^ (20 * p' + 1) := by
      dsimp [B, S]
      have h1 : (2 : ℤ) * ((2 : ℤ) ^ (9 * p' - 1) * (2 : ℤ) ^ (9 * p' - 1)) * (2 : ℤ) ^ (2 * p' + 2) =
          (2 : ℤ) ^ 1 * (2 : ℤ) ^ (9 * p' - 1) * (2 : ℤ) ^ (9 * p' - 1) * (2 : ℤ) ^ (2 * p' + 2) := by ring
      rw [h1, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [hcomb]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  have hND11 : |N1 * D1| < B * B := by rw [abs_mul]; exact mul_lt_mul'' hN1 hD1 (abs_nonneg _) (abs_nonneg _)
  have hND22 : |N2 * D2| < B * B := by rw [abs_mul]; exact mul_lt_mul'' hN2 hD2 (abs_nonneg _) (abs_nonneg _)
  have hND21 : |N2 * D1| < B * B := by rw [abs_mul]; exact mul_lt_mul'' hN2 hD1 (abs_nonneg _) (abs_nonneg _)
  have hND12 : |N1 * D2| < B * B := by rw [abs_mul]; exact mul_lt_mul'' hN1 hD2 (abs_nonneg _) (abs_nonneg _)
  have hDD11 : |D1 * D1| < B * B := by rw [abs_mul]; exact mul_lt_mul'' hD1 hD1 (abs_nonneg _) (abs_nonneg _)
  have hDD22 : |D2 * D2| < B * B := by rw [abs_mul]; exact mul_lt_mul'' hD2 hD2 (abs_nonneg _) (abs_nonneg _)
  have hnumRe : |(N1 * D1 + N2 * D2) * S| < (2 : ℤ) ^ (22 * p' - 1) := by
    rw [abs_mul, abs_of_pos hS_pos]
    have hadd := abs_add_le (N1 * D1) (N2 * D2)
    have hlt : |N1 * D1 + N2 * D2| * S < 2 * (B * B) * S :=
      mul_lt_mul_of_pos_right (by linarith) hS_pos
    linarith
  have hnumIm : |(N2 * D1 - N1 * D2) * S| < (2 : ℤ) ^ (22 * p' - 1) := by
    rw [abs_mul, abs_of_pos hS_pos]
    have hsub := abs_sub (N2 * D1) (N1 * D2)
    have hlt : |N2 * D1 - N1 * D2| * S < 2 * (B * B) * S :=
      mul_lt_mul_of_pos_right (by linarith) hS_pos
    linarith
  have hden : |D1 * D1 + D2 * D2| < (2 : ℤ) ^ (22 * p' - 1) := by
    have hadd := abs_add_le (D1 * D1) (D2 * D2)
    have h1_le_S : 1 ≤ S := by
      dsimp [S]
      exact one_le_pow₀ (by decide : (1 : ℤ) ≤ 2)
    have hBB_pos : 0 < B * B := by positivity
    nlinarith
  exact ⟨hN1, hN2, hD1, hD2, hnumRe, hnumIm, hden⟩

/-- **Packed Signed-Kronecker Integer Word-Width Bound (`packSignedKronecker_word_width_bound`, `[MS]` §6.2)**:
For any bit-stride `s ≥ 1` and coefficient list `f : List ℤ` with `∀ c ∈ f, |c| ≤ 2^(s - 1)`,
the packed Kronecker integer `packSignedKronecker (2^s) f` has magnitude bounded by
`|packSignedKronecker (2^s) f| ≤ (2 ^ s) ^ f.length - 1 < (2 ^ s) ^ f.length = 2 ^ (f.length * s)`,
fitting in `f.length * s` bits (at most `W_eff * (6 * p')` bits in `kroneckerSpreadStepBitCost`). -/
theorem packSignedKronecker_word_width_bound
    (s : ℕ) (hs : 1 ≤ s) (f : List ℤ) (hf : ∀ c ∈ f, |c| ≤ (2 : ℤ) ^ (s - 1)) :
    |packSignedKronecker ((2 : ℤ) ^ s) f| ≤ ((2 : ℤ) ^ s) ^ f.length - 1 := by
  have hH_le : (2 : ℤ) ^ (s - 1) ≤ (2 : ℤ) ^ s - 1 := by
    have h2 : 2 * (2 : ℤ) ^ (s - 1) = (2 : ℤ) ^ s := by
      rcases s with _ | s'
      · omega
      · simp [pow_succ']
    have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ (s - 1) := one_le_pow₀ (by decide : (1 : ℤ) ≤ 2)
    linarith
  have h2s_pos : (0 : ℤ) ≤ (2 : ℤ) ^ s := by positivity
  induction f with
  | nil =>
    simp [packSignedKronecker]
  | cons c cs ih =>
    simp only [packSignedKronecker, List.length_cons, pow_succ']
    have hc : |c| ≤ (2 : ℤ) ^ s - 1 := (hf c List.mem_cons_self).trans hH_le
    have hcs : |packSignedKronecker ((2 : ℤ) ^ s) cs| ≤ ((2 : ℤ) ^ s) ^ cs.length - 1 :=
      ih (fun x hx => hf x (List.mem_cons_of_mem c hx))
    have htri := abs_add_le c ((2 : ℤ) ^ s * packSignedKronecker ((2 : ℤ) ^ s) cs)
    rw [abs_mul, abs_of_nonneg h2s_pos] at htri
    have hmul : (2 : ℤ) ^ s * |packSignedKronecker ((2 : ℤ) ^ s) cs| ≤
        (2 : ℤ) ^ s * (((2 : ℤ) ^ s) ^ cs.length - 1) :=
      mul_le_mul_of_nonneg_left hcs h2s_pos
    linarith

/-- For any natural numbers `a, b`, `Nat.log2 (a * b) + 1 ≤ (Nat.log2 a + 2) * (Nat.log2 b + 1)`. -/
theorem log2_mul_add_one_le (a b : ℕ) :
    Nat.log2 (a * b) + 1 ≤ (Nat.log2 a + 2) * (Nat.log2 b + 1) := by
  have hsum : Nat.log2 (a * b) + 1 ≤ (Nat.log2 a + 1) + (Nat.log2 b + 1) := by
    by_cases hab : a * b = 0
    · rw [hab]
      have : Nat.log2 0 = 0 := by decide
      omega
    · have ha : a < 2 ^ (Nat.log2 a + 1) := lt_two_pow_log2_succ a
      have hb : b < 2 ^ (Nat.log2 b + 1) := lt_two_pow_log2_succ b
      have hprod : a * b < 2 ^ ((Nat.log2 a + 1) + (Nat.log2 b + 1)) := by
        rw [pow_add]
        exact Nat.mul_lt_mul'' ha hb
      have hlt : Nat.log2 (a * b) < (Nat.log2 a + 1) + (Nat.log2 b + 1) :=
        (Nat.log2_lt hab).mpr hprod
      omega
  have hmul : (Nat.log2 a + 1) + (Nat.log2 b + 1) ≤ (Nat.log2 a + 2) * (Nat.log2 b + 1) := by
    nlinarith
  exact hsum.trans hmul

/-- Constant-factor multiplier for `mulBitCost (c * w)` relative to `mulBitCost w`. -/
def mulBitCostScaleFactor (c : ℕ) : ℕ :=
  c * (Nat.log2 c + 2) * (Nat.log2 (Nat.log2 c + 2) + 2)

/-- **Constant-Factor Scaling of `mulBitCost` (`mulBitCost_mul_le`, `[MS]` §7)**:
For all `c, w : ℕ`, `mulBitCost (c * w) ≤ mulBitCostScaleFactor c * mulBitCost w`. -/
theorem mulBitCost_mul_le (c w : ℕ) :
    mulBitCost (c * w) ≤ mulBitCostScaleFactor c * mulBitCost w := by
  unfold mulBitCost mulBitCostScaleFactor
  have h1 : Nat.log2 (c * w) + 1 ≤ (Nat.log2 c + 2) * (Nat.log2 w + 1) :=
    log2_mul_add_one_le c w
  have h2 : Nat.log2 (Nat.log2 (c * w) + 1) + 1 ≤
      (Nat.log2 (Nat.log2 c + 2) + 2) * (Nat.log2 (Nat.log2 w + 1) + 1) := by
    calc Nat.log2 (Nat.log2 (c * w) + 1) + 1
        ≤ Nat.log2 ((Nat.log2 c + 2) * (Nat.log2 w + 1)) + 1 :=
          Nat.add_le_add_right (nat_log2_mono h1) 1
      _ ≤ (Nat.log2 (Nat.log2 c + 2) + 2) * (Nat.log2 (Nat.log2 w + 1) + 1) :=
          log2_mul_add_one_le (Nat.log2 c + 2) (Nat.log2 w + 1)
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul (le_refl (c * w)) h1) h2
  calc c * w * (Nat.log2 (c * w) + 1) * (Nat.log2 (Nat.log2 (c * w) + 1) + 1)
      ≤ c * w * ((Nat.log2 c + 2) * (Nat.log2 w + 1)) *
          ((Nat.log2 (Nat.log2 c + 2) + 2) * (Nat.log2 (Nat.log2 w + 1) + 1)) := hprod
    _ = c * (Nat.log2 c + 2) * (Nat.log2 (Nat.log2 c + 2) + 2) *
          (w * (Nat.log2 w + 1) * (Nat.log2 (Nat.log2 w + 1) + 1)) := by ring

/-- **Constant-Factor `mulBitCost` Bounds for Raw Temporary Word Widths `6p'`, `10p'`, and `22p'`
Relative to `mulBitCost (4 * p')` (`mulBitCost_raw_temporaries_le_four_mul_pChild`, `[MS]` §3.2)**:
Closes the constant-factor gap between the unrounded intermediate temporary bit-widths
(`6 * p'` in `raw_spread_coord_mem_six_mul_pChild_word`, `10 * p'` in
`gPreTwistU_raw_temporaries_word_width_bound`, and `22 * p'` in
`gRatioQuantize_raw_temporaries_word_width_bound`) and the nominal `mulBitCost (4 * p')` unit:
- `mulBitCost (6 * p') ≤ 18 * mulBitCost (4 * p')`,
- `mulBitCost (10 * p') ≤ 27 * mulBitCost (4 * p')`,
- `mulBitCost (22 * p') ≤ 96 * mulBitCost (4 * p')`. -/
theorem mulBitCost_raw_temporaries_le_four_mul_pChild (p' : ℕ) :
    mulBitCost (6 * p') ≤ 18 * mulBitCost (4 * p') ∧
    mulBitCost (10 * p') ≤ 27 * mulBitCost (4 * p') ∧
    mulBitCost (22 * p') ≤ 96 * mulBitCost (4 * p') := by
  have h6 : mulBitCost (6 * p') ≤ 18 * mulBitCost (4 * p') := by
    calc mulBitCost (6 * p')
        ≤ mulBitCost (2 * (4 * p')) := mulBitCost_mono (by omega)
      _ ≤ mulBitCostScaleFactor 2 * mulBitCost (4 * p') := mulBitCost_mul_le 2 (4 * p')
      _ = 18 * mulBitCost (4 * p') := by
        have : mulBitCostScaleFactor 2 = 18 := by decide
        rw [this]
  have h10 : mulBitCost (10 * p') ≤ 27 * mulBitCost (4 * p') := by
    calc mulBitCost (10 * p')
        ≤ mulBitCost (3 * (4 * p')) := mulBitCost_mono (by omega)
      _ ≤ mulBitCostScaleFactor 3 * mulBitCost (4 * p') := mulBitCost_mul_le 3 (4 * p')
      _ = 27 * mulBitCost (4 * p') := by
        have : mulBitCostScaleFactor 3 = 27 := by decide
        rw [this]
  have h22 : mulBitCost (22 * p') ≤ 96 * mulBitCost (4 * p') := by
    calc mulBitCost (22 * p')
        ≤ mulBitCost (6 * (4 * p')) := mulBitCost_mono (by omega)
      _ ≤ mulBitCostScaleFactor 6 * mulBitCost (4 * p') := mulBitCost_mul_le 6 (4 * p')
      _ = 96 * mulBitCost (4 * p') := by
        have : mulBitCostScaleFactor 6 = 96 := by decide
        rw [this]
  exact ⟨h6, h10, h22⟩

end IntMul
