import WP.W14.Front
import WP.W14.SolverFwd
import WP.W14.SolverNyq
import WP.W14.SolverBwd

/-!
# W14: the single-step error closure at any schedule node

`step_error_le_at` is FTP:1505 (`sincGaussianFastDFTOfTables_step_error_le`) with the sub-step grid
`pSub` and the window `m1` as parameters, re-proved with errors measured in `eUnit p K =
2^-(p+K+10)` (`StepSlots`). Final budget (units `2^-p M`): term A `< 0.003`, terms B+C `< 0.036`,
solver-internal rounding `< 0.003`, output rounding `< 0.354`; total `< 0.396 < 1`.
-/

namespace WP.W14

open IntMul Complex Real

/-- **Single-step error closure at a node satisfying `StepSlots`** (FTP:1505 generalized). -/
theorem step_error_le_at
    {p K t1 r c1 pSub m1 : ℕ} {v1Of : ℕ → ℕ → ℕ}
    (hp : 8 ≤ p) (hK : 2 ≤ K)
    (ht1 : 0 < t1) (ht1_le : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (hr_le : r ≤ 2 * t1)
    (hsize : t1 * r = 2 ^ K)
    (hc1 : c1 * t1 = r)
    (heven : t1 % 2 = 0)
    (hv1 : ∀ u2 < r, ∀ u1 : ℕ, ∃ q : ℤ,
      (2 * (u2 : ℤ) - 1) * (v1Of u2 u1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ))
    (hv1_eq : ∀ u2 u1 : ℕ, v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1)
    (hS : StepSlots pSub m1 p K)
    (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth m1 r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u),
            G s) ∧
      (∀ s < 2 * m1 + 1,
        |((G s : ℝ) / (2 : ℝ) ^ pSub) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((m1 : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((pSub : ℕ) : ℤ))) ∧
      (∀ s < 2 * m1 + 1, (G s).natAbs ≤ 2 ^ pSub + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex pSub (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr pSub)
    (hPost : ∀ k2 < r,
      ‖toScaledComplex pSub (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))‖ ≤
        2 * complexQuantizeMaxErr pSub)
    (hC01 : ∀ u2 < r, C01Clause pSub p K r c0Table c1Table u2)
    (childDFT : (ℕ → ℂ) → ℕ → ℂ)
    (hchild_err : ∀ (x' : ℕ → ℂ) (M' : ℝ), 1 ≤ M' →
      (∀ k < r, ‖x' k‖ ≤ M') → ∀ u' < r,
      ‖childDFT x' u' - dft1D r x' u'‖ ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * M')
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < t1 * r) :
    let U : ℕ → ℕ → ℂ := fun j1 k2 =>
      kroneckerSpreadOfFoldedTaps pSub m1 t1 r (filterTaps.getD j1 []) x j1 k2
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => childDFT (qPost v1) u2
    let v1Of' : ℕ → ℕ → ℕ := fun u2 u1 =>
      oddStrideInvPow2 (Nat.log2 t1) u2 u1
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of' u2 u1) u2)
    let u2 := u % r
    let u1_tilde := u / r
    let c0_q : ℂ := toScaledComplex pSub (read1D c0Table u2)
    let c1_q : ℂ := toScaledComplex pSub (read1D c1Table u2)
    let alt_q : ℂ := complexQuantize pSub (nyquistAltSum t1 r x)
    let z_sub : ℂ :=
      if 2 * u2 < r then
        solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde
      else
        solveBidiagonalBwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
    ‖complexQuantize p z_sub - dft1D (t1 * r) x u‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) * M := by
  intro U P Q qPost qHat v1Of' Y u2 u1_tilde c0_q c1_q alt_q z_sub
  have hM_pos : 0 < M := by linarith
  have hp_work : 8 ≤ pWork p K := by unfold pWork; omega
  have hu2 : u2 < r := Nat.mod_lt u hr
  have hu1_tilde : u1_tilde < t1 := by
    rw [mul_comm] at hu; exact Nat.div_lt_of_lt_mul hu
  have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_right t1 hr
  have hc0 := cqme_nonneg pSub
  have he0 := eUnit_pos p K
  have hpc0 : (0 : ℝ) < (2 : ℝ) ^ (-(pChild p K : ℤ)) := zpow_pos (by norm_num) _
  have hpw0 : (0 : ℝ) < (2 : ℝ) ^ (-(pWork p K : ℤ)) := zpow_pos (by norm_num) _
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  -- front half (FTP:1586–1816)
  have hfront : ∀ k : ℕ, ‖Y u2 k -
      dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2‖ ≤
      2.1 * eUnit p K * M + (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M) :=
    fun k => step_front_at ht1 hr hsize hc1 hv1 hv1_eq hS filterTaps preTwiddles postTwiddles
      hTaps hPre hPost childDFT hchild_err x M hM1 hx U P Q qPost Y
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      u2 hu2 k
  -- passband conditioning (term A) and table rounding of c0/c1
  set c0R := c0Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) with hc0R
  set c1R := c1Coeff (realErfScaled (alphaSchedule (pWork p K))) ((u2 : ℝ) / (r : ℝ)) with hc1R
  have h_spread_ideal : ∀ k : ℕ,
      ‖dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2 -
        passbandRHS t1 (c0R : ℂ) (c1R : ℂ) (dft1DGrid t1 r x u2) k‖ ≤
        (0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M :=
    fun k => theorem2_sincGaussian_dft2D_sub_passband_norm_le
      (pWork p K) t1 r hp_work ht1 hr k u2 hu2 x M hM_pos.le hx
  obtain ⟨hc0_err, hc1_err, _, _, _, _, _, _, _, hc0_q_eq, hc1_q_eq⟩ :=
    c01Clause_facts (hC01 u2 hu2)
  have hrq_le_cq : realQuantizeMaxErr pSub ≤ complexQuantizeMaxErr pSub := by
    unfold realQuantizeMaxErr complexQuantizeMaxErr
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((pSub : ℤ) + 2)) := zpow_pos (by norm_num) _
    nlinarith
  have hX_norm : ∀ v : ℕ, ‖dft1DGrid t1 r x u2 v‖ ≤ M :=
    norm_dft1DGrid_le t1 r ht1 hr x M hx u2 hu2
  have hcM : complexQuantizeMaxErr pSub ≤ 0.1 * eUnit p K * M := by
    have := hS.hc; nlinarith
  have h_ideal_q_err : ∀ k : ℕ,
      ‖passbandRHS t1 (c0R : ℂ) (c1R : ℂ) (dft1DGrid t1 r x u2) k -
        passbandRHS t1 c0_q c1_q (dft1DGrid t1 r x u2) k‖ ≤ 0.4 * eUnit p K * M := by
    intro k
    unfold passbandRHS
    set v0 := (((k : ℤ) - 0).emod (t1 : ℤ)).toNat
    set v1 := (((k : ℤ) - 1).emod (t1 : ℤ)).toNat
    have hsplit : (c0R : ℂ) * dft1DGrid t1 r x u2 v0 + (c1R : ℂ) * dft1DGrid t1 r x u2 v1 -
        (c0_q * dft1DGrid t1 r x u2 v0 + c1_q * dft1DGrid t1 r x u2 v1) =
        ((c0R : ℂ) - c0_q) * dft1DGrid t1 r x u2 v0 +
          ((c1R : ℂ) - c1_q) * dft1DGrid t1 r x u2 v1 := by ring
    rw [hsplit]
    have htri := norm_add_le (((c0R : ℂ) - c0_q) * dft1DGrid t1 r x u2 v0)
      (((c1R : ℂ) - c1_q) * dft1DGrid t1 r x u2 v1)
    have hc0_diff : ‖(c0R : ℂ) - c0_q‖ ≤ 2 * complexQuantizeMaxErr pSub := by
      change ‖(c0R : ℂ) - toScaledComplex pSub (read1D c0Table u2)‖ ≤ _
      rw [hc0_q_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      linarith
    have hc1_diff : ‖(c1R : ℂ) - c1_q‖ ≤ 2 * complexQuantizeMaxErr pSub := by
      change ‖(c1R : ℂ) - toScaledComplex pSub (read1D c1Table u2)‖ ≤ _
      rw [hc1_q_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      linarith
    have h1 : ‖((c0R : ℂ) - c0_q) * dft1DGrid t1 r x u2 v0‖ ≤ 2 * complexQuantizeMaxErr pSub * M := by
      rw [norm_mul]; exact mul_le_mul hc0_diff (hX_norm v0) (norm_nonneg _) (by positivity)
    have h2 : ‖((c1R : ℂ) - c1_q) * dft1DGrid t1 r x u2 v1‖ ≤ 2 * complexQuantizeMaxErr pSub * M := by
      rw [norm_mul]; exact mul_le_mul hc1_diff (hX_norm v1) (norm_nonneg _) (by positivity)
    have h3 : complexQuantizeMaxErr pSub * M ≤ 0.1 * eUnit p K * M :=
      mul_le_mul_of_nonneg_right hS.hc hM_pos.le
    linarith
  -- the right-hand-side error seen by the solver
  set ε_rhs : ℝ := (0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M +
    ((2.6 : ℝ) * eUnit p K * M + (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) with hε_rhs
  have hε_rhs_nonneg : 0 ≤ ε_rhs := by rw [hε_rhs]; positivity
  have h_eff_ideal_q : ∀ (m : ℕ) (z : ℂ), ‖z - Y u2 m‖ ≤ complexQuantizeMaxErr pSub →
      ‖z - passbandRHS t1 (toScaledComplex pSub (read1D c0Table u2))
        (toScaledComplex pSub (read1D c1Table u2)) (dft1DGrid t1 r x u2) m‖ ≤ ε_rhs := by
    intro m z hz
    change ‖z - passbandRHS t1 c0_q c1_q (dft1DGrid t1 r x u2) m‖ ≤ ε_rhs
    have hsplit : z - passbandRHS t1 c0_q c1_q (dft1DGrid t1 r x u2) m =
        (z - Y u2 m) +
          (Y u2 m - dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) m u2) +
          (dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) m u2 -
            passbandRHS t1 (c0R : ℂ) (c1R : ℂ) (dft1DGrid t1 r x u2) m) +
          (passbandRHS t1 (c0R : ℂ) (c1R : ℂ) (dft1DGrid t1 r x u2) m -
            passbandRHS t1 c0_q c1_q (dft1DGrid t1 r x u2) m) := by ring
    rw [hsplit]
    have htri1 := norm_add_le
      ((z - Y u2 m) +
        (Y u2 m - dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) m u2) +
        (dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) m u2 -
          passbandRHS t1 (c0R : ℂ) (c1R : ℂ) (dft1DGrid t1 r x u2) m))
      (passbandRHS t1 (c0R : ℂ) (c1R : ℂ) (dft1DGrid t1 r x u2) m -
        passbandRHS t1 c0_q c1_q (dft1DGrid t1 r x u2) m)
    have htri2 := norm_add_le
      ((z - Y u2 m) +
        (Y u2 m - dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) m u2))
      (dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) m u2 -
        passbandRHS t1 (c0R : ℂ) (c1R : ℂ) (dft1DGrid t1 r x u2) m)
    have htri3 := norm_add_le (z - Y u2 m)
      (Y u2 m - dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) m u2)
    have h2 := hfront m
    have h3 := h_spread_ideal m
    have h4 := h_ideal_q_err m
    rw [hε_rhs]
    linarith
  -- amplification of terms A, B, C
  have hA_lt :
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M) <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have h1 := mul_lt_mul_of_pos_right (lemma2_termA_conditioning_mul_zpow_lt p K t1 hK ht1_le)
      hM_pos
    linarith
  have hBC_lt := amplification_at p K t1 r M hK hr hM_pos hsize
  have hrhs_expand :
      (2.36 : ℝ) * (t1 : ℝ) * ε_rhs =
        (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M) +
          (2.36 : ℝ) * (t1 : ℝ) * ((2.6 : ℝ) * eUnit p K * M +
            (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) := by
    rw [hε_rhs]; ring
  have hp_le1 := two_zpow_neg_le_one p
  have h_cyc_le_M : (2.36 : ℝ) * (t1 : ℝ) * ε_rhs ≤ M := by
    have hsum_lt : (2.36 : ℝ) * (t1 : ℝ) * ε_rhs < (0.039 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      linarith
    nlinarith
  -- solver stage (FTP:1922–2195)
  have hz_sub_err :
      ‖z_sub - dft1DGrid t1 r x u2 u1_tilde‖ ≤
        (2.36 : ℝ) * (t1 : ℝ) * ε_rhs + (2.001 : ℝ) * complexQuantizeMaxErr pSub +
          8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
    dsimp only [z_sub]
    split_ifs with h_fwd h_nyq
    · exact solver_fwd_at hp_work ht1 hr hr_le hS.hq (hS.hratio_le ht1_le_2K)
        (hS.ht1c_le ht1_le_2K) c0Table c1Table u2 u1_tilde hu2 hu1_tilde (hC01 u2 hu2) h_fwd
        x M hM1 hx (Y u2) ε_rhs hε_rhs_nonneg h_cyc_le_M h_eff_ideal_q
    · exact solver_nyq_at hp_work ht1 hr heven hS.hq (hS.hratio_le ht1_le_2K)
        c0Table c1Table u2 u1_tilde hu2 hu1_tilde (hC01 u2 hu2) h_nyq
        x M hM1 hx (Y u2) ε_rhs hε_rhs_nonneg h_eff_ideal_q
    · exact solver_bwd_at hp_work ht1 hr hr_le hS.hq (hS.hratio_le ht1_le_2K)
        (hS.ht1c_le ht1_le_2K) c0Table c1Table u2 u1_tilde hu2 hu1_tilde (hC01 u2 hu2)
        (by omega) x M hM1 hx (Y u2) ε_rhs hε_rhs_nonneg h_cyc_le_M h_eff_ideal_q
  have hgrid : dft1DGrid t1 r x u2 u1_tilde = dft1D (t1 * r) x u := dft1DGrid_eq_dft1D t1 r x u
  rw [hgrid] at hz_sub_err
  -- solver-internal rounding and output rounding
  have hD_lt := termD_at p K t1 pSub M hM1 hS.hc (hS.hsolve_le ht1_le_2K)
  have hQ_lt : ‖complexQuantize p z_sub - z_sub‖ < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hq_nonneg := cqme_nonneg p
    calc ‖complexQuantize p z_sub - z_sub‖
        ≤ complexQuantizeMaxErr p := norm_complexQuantize_sub_le p z_sub
      _ = complexQuantizeMaxErr p * 1 := (mul_one _).symm
      _ ≤ complexQuantizeMaxErr p * M := mul_le_mul_of_nonneg_left hM1 hq_nonneg
      _ < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
          mul_lt_mul_of_pos_right (complexQuantizeMaxErr_lt p) hM_pos
  have htri_final :
      ‖complexQuantize p z_sub - dft1D (t1 * r) x u‖ ≤
        ‖z_sub - dft1D (t1 * r) x u‖ + ‖complexQuantize p z_sub - z_sub‖ := by
    have hsplit : complexQuantize p z_sub - dft1D (t1 * r) x u =
        (z_sub - dft1D (t1 * r) x u) + (complexQuantize p z_sub - z_sub) := by ring
    rw [hsplit]; exact norm_add_le _ _
  have hpM : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M := mul_pos hp0 hM_pos
  linarith

#assert_std_axioms step_error_le_at

end WP.W14
