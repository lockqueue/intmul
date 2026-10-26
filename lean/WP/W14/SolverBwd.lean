import WP.W14.Solver

/-!
# W14: backward solver branch at any grid (FTP:2093–2195)

The backward (c1-dominant) branch solves the reversed system `bwdRevRHS` (T3:2578), i.e. it uses the
index `Y_{u1+1+s}` of `[MS]` Section 5.1, Theorem 5.1(2), eq. (23) (correcting `Y_{u1∓s}` in an earlier `[MS]` draft).
-/

namespace WP.W14

open IntMul Complex Real

/-- Backward (c1-dominant, `r < 2 u2`) solver branch at grid `pSub` (FTP:2093–2195). -/
theorem solver_bwd_at {p K t1 r pSub : ℕ} (hp_work : 8 ≤ pWork p K)
    (ht1 : 0 < t1) (hr : 0 < r) (hr_le : r ≤ 2 * t1)
    (hq : realQuantizeMaxErr pSub ≤ (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ))
    (ht1q : (t1 : ℝ) * (10 * realQuantizeMaxErr pSub) ≤ (0.0001 : ℝ))
    (ht1c : (t1 : ℝ) * complexQuantizeMaxErr pSub ≤ (0.001 : ℝ))
    (c0Table c1Table : Array (ℤ × ℤ)) (u2 u1 : ℕ) (hu2 : u2 < r) (hu1 : u1 < t1)
    (hC01 : C01Clause pSub p K r c0Table c1Table u2) (h_bwd : r < 2 * u2)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (Ycol : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hεM : (2.36 : ℝ) * (t1 : ℝ) * ε ≤ M)
    (hY : ∀ (m : ℕ) (z : ℂ), ‖z - Ycol m‖ ≤ complexQuantizeMaxErr pSub →
      ‖z - passbandRHS t1 (toScaledComplex pSub (read1D c0Table u2))
        (toScaledComplex pSub (read1D c1Table u2)) (dft1DGrid t1 r x u2) m‖ ≤ ε) :
    ‖solveBidiagonalBwdQuantized pSub t1 (toScaledComplex pSub (read1D c0Table u2))
        (toScaledComplex pSub (read1D c1Table u2)) Ycol u1 - dft1DGrid t1 r x u2 u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε + (2.001 : ℝ) * complexQuantizeMaxErr pSub +
        8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
  have hM_pos : 0 < M := by linarith
  obtain ⟨hc0_err, hc1_err, hc0_qR_nonneg, _hc0_qR_le1, _hc1_qR_nonneg, hc1_qR_le1,
    _, hc01_bwd, _, hc0_q_eq, hc1_q_eq⟩ := c01Clause_facts hC01
  set α := alphaSchedule (pWork p K) with hα_def
  have hα : 0 < α := alphaSchedule_pos (pWork p K) (by omega)
  set y := (u2 : ℝ) / (r : ℝ) with hy_def
  set c0R := c0Coeff (realErfScaled α) y
  set c1R := c1Coeff (realErfScaled α) y
  set c0_qR : ℝ := ((read1D c0Table u2).1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
  set c1_qR : ℝ := ((read1D c1Table u2).1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
  set c0_q : ℂ := toScaledComplex pSub (read1D c0Table u2)
  set c1_q : ℂ := toScaledComplex pSub (read1D c1Table u2)
  have hqSub_nonneg := cqme_nonneg pSub
  let X : ℕ → ℂ := dft1DGrid t1 r x u2
  let Y_ideal_q : ℕ → ℂ := passbandRHS t1 c0_q c1_q X
  have hX_norm : ∀ v : ℕ, ‖X v‖ ≤ M := norm_dft1DGrid_le t1 r ht1 hr x M hx u2 hu2
  have h_bnd_q : Y_ideal_q 0 = c0_q * X 0 + c1_q * X (t1 - 1) := by
    dsimp only [Y_ideal_q, passbandRHS]
    rw [emod_sub_zero_toNat t1 0 ht1, emod_zero_sub_one_toNat t1 ht1]
  have h_int_q : ∀ v : ℕ, v + 1 < t1 → Y_ideal_q (v + 1) = c0_q * X (v + 1) + c1_q * X v := by
    intro v hv
    dsimp only [Y_ideal_q, passbandRHS]
    rw [emod_sub_zero_toNat t1 (v + 1) hv, emod_succ_sub_one_toNat t1 v hv]
  have h_eff_ideal_q : ∀ (m : ℕ) (z : ℂ), ‖z - Ycol m‖ ≤ complexQuantizeMaxErr pSub →
      ‖z - Y_ideal_q m‖ ≤ ε := hY
  have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
  have hc1R_pos : 0 < c1R := c1Coeff_realErfScaled_pos α y hα
  have hc01_sum : c0R + c1R ≤ 1 := c0_add_c1_realErfScaled_le_one α y hα
  have hc1R_le1 : c1R ≤ 1 := by linarith
  have hr_pos_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy1 : y ≤ 1 := (div_le_one hr_pos_real).mpr (by exact_mod_cast hu2.le)
  have hy_half : 1 / 2 ≤ y := by
    rw [hy_def, le_div_iff₀ hr_pos_real]
    have : (r : ℝ) ≤ 2 * (u2 : ℝ) := by exact_mod_cast h_bwd.le
    linarith
  have hc1R_gt : (0.49999999 : ℝ) ≤ c1R :=
    (c1Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy_half hy1).le
  have hc01R : c0R ≤ c1R := c0Coeff_le_c1Coeff_of_ge_half α y hα hy_half hy1
  have hratioR : (c0R / c1R) ^ t1 ≤ (0.15 : ℝ) :=
    c0_div_c1_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1 hr hr_le h_bwd hu2
  obtain ⟨hc1_q_ge, hc1_q_le1, hc0_q_nonneg, hc01_q, hratio_q⟩ :=
    faithful_coeff_ratio_pow_le_at pSub t1 hq ht1q c1R c0R c1_qR c0_qR
      hc1R_gt hc1R_le1 hc0R_pos.le hc01R hratioR
      hc0_qR_nonneg (hc01_bwd h_bwd) hc1_qR_le1 hc1_err hc0_err
  have hnorm_c1_q : ‖c1_q‖ = c1_qR := by
    rw [hc1_q_eq, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
    rw [hc0_q_eq, Complex.norm_real, Real.norm_of_nonneg hc0_q_nonneg]
  have hc1_q_pos : 0 < ‖c1_q‖ := by linarith
  have hc1_q_ne : c1_q ≠ 0 := norm_pos_iff.mp hc1_q_pos
  have hc1_q_le1_norm : ‖c1_q‖ ≤ 1 := by linarith
  have hc01_q_norm : ‖c0_q‖ ≤ ‖c1_q‖ := by linarith
  have hratio_q_norm : (‖c0_q‖ / ‖c1_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
    rw [hnorm_c0_q, hnorm_c1_q]; exact hratio_q
  have hdenom_bwd_q : c1_q + c0_q * zHomBwd c0_q c1_q (t1 - 1) ≠ 0 :=
    denom_ne_zero_of_relaxed t1 c1_q c0_q (0.4999 : ℝ) (0.1501 : ℝ)
      le_rfl (by linarith) hratio_q_norm le_rfl
  have hrec_q := solveBidiagonalBwd_recover_exact t1 c0_q c1_q ht1 hc1_q_ne hdenom_bwd_q
    X Y_ideal_q h_bnd_q h_int_q u1 hu1
  have ht1_sub_lt : t1 - 1 < t1 := Nat.sub_lt ht1 Nat.zero_lt_one
  have hrec_last := solveBidiagonalBwd_recover_exact t1 c0_q c1_q ht1 hc1_q_ne hdenom_bwd_q
    X Y_ideal_q h_bnd_q h_int_q (t1 - 1) ht1_sub_lt
  rw [solveBidiagonalBwd_eq_solveBidiagonalFwd_rev, Nat.sub_self] at hrec_last
  change ‖solveBidiagonalBwdQuantized pSub t1 c0_q c1_q Ycol u1 - X u1‖ ≤ _
  rw [← hrec_q,
      solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev,
      solveBidiagonalBwd_eq_solveBidiagonalFwd_rev]
  set d := t1 - 1 - u1
  have hd_lt : d < t1 :=
    Nat.lt_of_le_of_lt (Nat.sub_le (t1 - 1) u1) (Nat.sub_lt ht1 Nat.zero_lt_one)
  have h_eff := norm_solveBidiagonalFwdQuantized_sub_effRHS_le
    pSub t1 ht1 c1_q c0_q (by linarith) hc1_q_le1_norm hc01_q_norm hratio_q_norm
    ht1c (bwdRevRHS t1 Ycol) d hd_lt
  have h_rev_rhs :
      ∀ k : ℕ,
        ‖zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol) k -
            bwdRevRHS t1 Y_ideal_q k‖ ≤ ε := by
    intro k
    have h_eff_step := norm_zPartFwdEffRHS_sub_le pSub c1_q c0_q hc1_q_ne hc1_q_le1_norm
      (bwdRevRHS t1 Ycol) k
    by_cases hk0 : k = 0
    · subst hk0
      have h1 : bwdRevRHS t1 Ycol 0 = Ycol 0 := rfl
      have h2 : bwdRevRHS t1 Y_ideal_q 0 = Y_ideal_q 0 := rfl
      rw [h1] at h_eff_step; rw [h2]
      exact h_eff_ideal_q 0 _ h_eff_step
    · have h1 : bwdRevRHS t1 Ycol k = Ycol (t1 - k) := if_neg hk0
      have h2 : bwdRevRHS t1 Y_ideal_q k = Y_ideal_q (t1 - k) := if_neg hk0
      rw [h1] at h_eff_step; rw [h2]
      exact h_eff_ideal_q (t1 - k) _ h_eff_step
  have h_cyc := solveBidiagonalFwd_cyclic_error_bound_relaxed
    t1 ht1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q)
    (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol))
    (0.4999 : ℝ) (0.1501 : ℝ) ε le_rfl (by linarith) hc01_q_norm hratio_q_norm le_rfl
    hε h_rev_rhs d hd_lt
  have h_cyc_0 := solveBidiagonalFwd_cyclic_error_bound_relaxed
    t1 ht1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q)
    (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol))
    (0.4999 : ℝ) (0.1501 : ℝ) ε le_rfl (by linarith) hc01_q_norm hratio_q_norm le_rfl
    hε h_rev_rhs 0 ht1
  have hZ0_le :
      ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) 0‖ ≤
        2 * M := by
    have htri0 := norm_add_le
      (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) 0 -
        solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) 0)
      (solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) 0)
    rw [sub_add_cancel, hrec_last] at htri0
    rw [hrec_last] at h_cyc_0
    have hXlast := hX_norm (t1 - 1)
    linarith
  have hmul_Z0 :
      4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
        ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) 0‖ ≤
        8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
    calc 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
          ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) 0‖
        ≤ 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * (2 * M) :=
          mul_le_mul_of_nonneg_left hZ0_le
            (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg))
      _ = 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by ring
  have hsplit :
      solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 Ycol) d -
        solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d =
      (solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 Ycol) d -
        solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) d) +
      (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) d -
        solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d) := by ring
  rw [hsplit]
  have htri := norm_add_le
    (solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 Ycol) d -
      solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) d)
    (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 Ycol)) d -
      solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d)
  linarith

#assert_std_axioms solver_bwd_at

end WP.W14
