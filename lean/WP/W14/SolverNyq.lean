import WP.W14.Solver

/-!
# W14: Nyquist solver branch at any grid (FTP:2021–2092)
-/

namespace WP.W14

open IntMul Complex Real

/-- Nyquist (`2 u2 = r`) solver branch at grid `pSub` (FTP:2021–2092). -/
theorem solver_nyq_at {p K t1 r pSub : ℕ} (hp_work : 8 ≤ pWork p K)
    (ht1 : 0 < t1) (hr : 0 < r) (heven : t1 % 2 = 0)
    (hq : realQuantizeMaxErr pSub ≤ (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ))
    (ht1q : (t1 : ℝ) * (10 * realQuantizeMaxErr pSub) ≤ (0.0001 : ℝ))
    (c0Table c1Table : Array (ℤ × ℤ)) (u2 u1 : ℕ) (hu2 : u2 < r) (hu1 : u1 < t1)
    (hC01 : C01Clause pSub p K r c0Table c1Table u2) (h_nyq : 2 * u2 = r)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (Ycol : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hY : ∀ (m : ℕ) (z : ℂ), ‖z - Ycol m‖ ≤ complexQuantizeMaxErr pSub →
      ‖z - passbandRHS t1 (toScaledComplex pSub (read1D c0Table u2))
        (toScaledComplex pSub (read1D c1Table u2)) (dft1DGrid t1 r x u2) m‖ ≤ ε) :
    ‖solveNyquistQuantized pSub t1 (toScaledComplex pSub (read1D c0Table u2)) Ycol
        (complexQuantize pSub (nyquistAltSum t1 r x)) u1 - dft1DGrid t1 r x u2 u1‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε + (2.001 : ℝ) * complexQuantizeMaxErr pSub +
        8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
  have hM_pos : 0 < M := by linarith
  obtain ⟨hc0_err, _hc1_err, hc0_qR_nonneg, hc0_qR_le1, _hc1_qR_nonneg, _hc1_qR_le1,
    _, _, hc10_nyq, hc0_q_eq, _hc1_q_eq⟩ := c01Clause_facts hC01
  set α := alphaSchedule (pWork p K) with hα_def
  have hα : 0 < α := alphaSchedule_pos (pWork p K) (by omega)
  set y := (u2 : ℝ) / (r : ℝ) with hy_def
  set c0R := c0Coeff (realErfScaled α) y
  set c0_qR : ℝ := ((read1D c0Table u2).1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
  set c0_q : ℂ := toScaledComplex pSub (read1D c0Table u2)
  set c1_q : ℂ := toScaledComplex pSub (read1D c1Table u2)
  set alt_q : ℂ := complexQuantize pSub (nyquistAltSum t1 r x)
  have hqSub_nonneg := cqme_nonneg pSub
  let X : ℕ → ℂ := dft1DGrid t1 r x u2
  let Y_ideal_q : ℕ → ℂ := passbandRHS t1 c0_q c1_q X
  have h_int_q : ∀ v : ℕ, v + 1 < t1 → Y_ideal_q (v + 1) = c0_q * X (v + 1) + c1_q * X v := by
    intro v hv
    dsimp only [Y_ideal_q, passbandRHS]
    rw [emod_sub_zero_toNat t1 (v + 1) hv, emod_succ_sub_one_toNat t1 v hv]
  have h_eff_ideal_q : ∀ (m : ℕ) (z : ℂ), ‖z - Ycol m‖ ≤ complexQuantizeMaxErr pSub →
      ‖z - Y_ideal_q m‖ ≤ ε := hY
  have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
  have hc1R_pos : 0 < c1Coeff (realErfScaled α) y := c1Coeff_realErfScaled_pos α y hα
  have hc01_sum : c0R + c1Coeff (realErfScaled α) y ≤ 1 := c0_add_c1_realErfScaled_le_one α y hα
  have hc0R_le1 : c0R ≤ 1 := by linarith
  have hr_pos_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hy_eq : y = 1 / 2 := by
    rw [hy_def, div_eq_iff hr_pos_real.ne']
    have : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast h_nyq
    linarith
  have hc1_q_eq_c0_q : c1_q = c0_q := hc10_nyq h_nyq
  have hy_half : y ≤ 1 / 2 := by linarith
  have hc0R_gt : (0.49999999 : ℝ) ≤ c0R :=
    (c0Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy0 hy_half).le
  have hzero_ratio : ((0 : ℝ) / c0R) ^ t1 ≤ (0.15 : ℝ) := by
    rw [zero_div, zero_pow ht1.ne']; norm_num
  have hzero_err : |(0 : ℝ) - 0| ≤ 2 * realQuantizeMaxErr pSub := by
    rw [sub_self, abs_zero, realQuantizeMaxErr_eq]; positivity
  obtain ⟨hc0_q_ge, hc0_q_le1, _, _, _⟩ :=
    faithful_coeff_ratio_pow_le_at pSub t1 hq ht1q c0R 0 c0_qR 0
      hc0R_gt hc0R_le1 le_rfl hc0R_pos.le hzero_ratio
      le_rfl hc0_qR_nonneg hc0_qR_le1 hc0_err hzero_err
  have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
    rw [hc0_q_eq, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hc0_q_pos : 0 < ‖c0_q‖ := by linarith
  have hc0_q_ne : c0_q ≠ 0 := norm_pos_iff.mp hc0_q_pos
  have hc0_q_le1_norm : ‖c0_q‖ ≤ 1 := by linarith
  have h_alt := (dft1DGrid_alternating_sum_nyquist_eq t1 r u2 ht1 hr heven h_nyq x).symm
  have h_int_nyq : ∀ v : ℕ, v + 1 < t1 → Y_ideal_q (v + 1) = c0_q * X (v + 1) + c0_q * X v := by
    intro v hv
    rw [h_int_q v hv, hc1_q_eq_c0_q]
  have hrec_q := solveNyquist_recover_exact t1 ht1 c0_q hc0_q_ne
    X Y_ideal_q h_int_nyq (nyquistAltSum t1 r x) h_alt u1 hu1
  have h_eff := norm_solveNyquistQuantized_sub_effRHS_le
    pSub t1 c0_q hc0_q_ne Ycol alt_q u1
  have h_nyq_cyc := solveNyquist_error_bound_relaxed
    t1 ht1 c0_q Y_ideal_q (zPartNyqEffRHS pSub c0_q Ycol)
    (nyquistAltSum t1 r x) alt_q (0.4999 : ℝ) ε (complexQuantizeMaxErr pSub)
    le_rfl (by linarith) hε
    (fun k => h_eff_ideal_q k _
      (norm_zPartNyqEffRHS_sub_le pSub c0_q hc0_q_ne hc0_q_le1_norm Ycol k))
    (norm_complexQuantize_sub_le pSub (nyquistAltSum t1 r x))
    u1 hu1
  have ht1_ge1 : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1
  have hqSub_le_8 :
      complexQuantizeMaxErr pSub / (t1 : ℝ) ≤
        (0.001 : ℝ) * complexQuantizeMaxErr pSub +
          8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
    have hdiv : complexQuantizeMaxErr pSub / (t1 : ℝ) ≤ complexQuantizeMaxErr pSub :=
      div_le_self hqSub_nonneg ht1_ge1
    have h1 : complexQuantizeMaxErr pSub ≤ (t1 : ℝ) * complexQuantizeMaxErr pSub := by
      calc complexQuantizeMaxErr pSub = 1 * complexQuantizeMaxErr pSub := (one_mul _).symm
        _ ≤ (t1 : ℝ) * complexQuantizeMaxErr pSub :=
            mul_le_mul_of_nonneg_right ht1_ge1 hqSub_nonneg
    have h2 : (t1 : ℝ) * complexQuantizeMaxErr pSub ≤
        ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
      calc (t1 : ℝ) * complexQuantizeMaxErr pSub
          = ((t1 : ℝ) * complexQuantizeMaxErr pSub) * 1 := (mul_one _).symm
        _ ≤ ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M :=
            mul_le_mul_of_nonneg_left hM1 (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg)
    have h3 : 0 ≤ ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg) hM_pos.le
    linarith
  change ‖solveNyquistQuantized pSub t1 c0_q Ycol alt_q u1 - X u1‖ ≤ _
  rw [← hrec_q]
  have hsplit :
      solveNyquistQuantized pSub t1 c0_q Ycol alt_q u1 -
        solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1 =
      (solveNyquistQuantized pSub t1 c0_q Ycol alt_q u1 -
        solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q Ycol) alt_q u1) +
      (solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q Ycol) alt_q u1 -
        solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1) := by ring
  rw [hsplit]
  have htri := norm_add_le
    (solveNyquistQuantized pSub t1 c0_q Ycol alt_q u1 -
      solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q Ycol) alt_q u1)
    (solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q Ycol) alt_q u1 -
      solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1)
  linarith

#assert_std_axioms solver_nyq_at

end WP.W14
