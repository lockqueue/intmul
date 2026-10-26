import IntMul.MaterializedAndComputable.FaithfulTablesPerturbation
import WP.W14.Slots

/-!
# W14: schedule-generic spread, passband-table and leaf lemmas

Generalizations of snapshot lemmas whose statements hard-wire the snapshot schedule:

* `norm_windowedSincGaussianSpreadArray_sub_le_at`: spatial tail at any window obeying
  `WindowRules` (T3:3942 generalized; uses the generic tail lemma T3:1886);
* `norm_kroneckerSpreadOfFoldedTaps_sub_le_at`, `norm_dft2D_kroneckerSpreadOfFoldedTaps_sub_le_at`,
  `norm_kroneckerSpreadOfFoldedTaps_le_at`: spread error and norm at any `(q, m1)`
  (FTP:762/810/836 generalized; the B2 lemma FTP:705 is already generic);
* `faithful_coeff_ratio_pow_le_at`: c0/c1 perturbation at any grid (FTP:946 generalized);
* `norm_baseRadix2FFTOfTwiddlesAt_sub_dft1D_le`: leaf closure at any internal grid satisfying
  `LeafSlot` (FTP:452 generalized).
-/

namespace WP.W14

open IntMul Complex Real

/-- Spatial tail at any window satisfying `WindowRules` (T3:3942 generalized). -/
theorem norm_windowedSincGaussianSpreadArray_sub_le_at
    (p K m1 t1 r : ℕ) (hw : WindowRules m1 p K) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) :
    ‖windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) m1 t1 r x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2‖ ≤
      (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  obtain ⟨hα, hm1_ge8, h_win, h_step⟩ := hw
  have hδ0 : 0 ≤ (j1 : ℝ) / (t1 : ℝ) := div_nonneg (Nat.cast_nonneg j1) (Nat.cast_nonneg t1)
  have hδ1 : (j1 : ℝ) / (t1 : ℝ) ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr ht1)).mpr (by exact_mod_cast hj1.le)
  have h_le_tails := norm_windowedSincGaussianSpreadArray_sub_le_tails
    (alphaSchedule (pWork p K)) hα m1 t1 r ht1 hr (by omega) x M hM hx j1 k2 hj1
  have h_tail := (lemma2_sincGaussian_spatial_tail_bound
    (alphaSchedule (pWork p K)) ((j1 : ℝ) / (t1 : ℝ)) m1 (pChild p K) hα hδ0 hδ1 hm1_ge8
    h_win h_step).1
  exact h_le_tails.trans (mul_le_mul_of_nonneg_right h_tail hM)

/-- Spread error at any `(q, m1)` (FTP:762 generalized): tail plus quantization. -/
theorem norm_kroneckerSpreadOfFoldedTaps_sub_le_at
    (p K q m1 t1 r : ℕ) (hw : WindowRules m1 p K) (ht1 : 0 < t1) (hr : 0 < r)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth m1 r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u),
          G s))
    (hG_err : ∀ s < 2 * m1 + 1,
      |((G s : ℝ) / (2 : ℝ) ^ q) -
          sincGaussian (alphaSchedule (pWork p K)) (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
        (2 : ℝ) ^ (-(q : ℤ)))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M) :
    ‖kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 -
        sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2‖ ≤
      ((6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) +
        (2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ))) * M := by
  have hB2 := norm_kroneckerSpreadOfFoldedTaps_sub_windowed_le
    (alphaSchedule (pWork p K)) q m1 t1 r ht1 hr j1 k2 hj1 hk2 gTapFold G hFold hG_err x M hM1 hx
  have hB1 := norm_windowedSincGaussianSpreadArray_sub_le_at p K m1 t1 r hw ht1 hr x M
    (by linarith) hx j1 k2 hj1
  have hsplit :
      kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 -
          sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2 =
        (kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 -
          windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) m1 t1 r x j1 k2) +
        (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) m1 t1 r x j1 k2 -
          sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2) := by ring
  rw [hsplit]
  have htri := norm_add_le
    (kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 -
      windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) m1 t1 r x j1 k2)
    (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) m1 t1 r x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
  linarith

/-- `dft2D` of the spread error (FTP:810 generalized). -/
theorem norm_dft2D_kroneckerSpreadOfFoldedTaps_sub_le_at
    (p K q m1 t1 r : ℕ) (hw : WindowRules m1 p K) (ht1 : 0 < t1) (hr : 0 < r)
    (filterTaps : Array (List ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth m1 r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u),
            G s) ∧
      (∀ s < 2 * m1 + 1,
        |((G s : ℝ) / (2 : ℝ) ^ q) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((m1 : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((q : ℕ) : ℤ))) ∧
      (∀ s < 2 * m1 + 1, (G s).natAbs ≤ 2 ^ q + 1))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u1 u2 : ℕ) :
    ‖dft2D t1 r (fun j1 k2 =>
          kroneckerSpreadOfFoldedTaps q m1 t1 r (filterTaps.getD j1 []) x j1 k2) u1 u2 -
        dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖ ≤
      ((6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) +
        (2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ))) * M := by
  rw [← dft2D_sub]
  refine dft2D_norm_le t1 r ht1 hr _ _ (fun j1 hj1 k2 hk2 => ?_) u1 u2
  rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
  exact norm_kroneckerSpreadOfFoldedTaps_sub_le_at p K q m1 t1 r hw ht1 hr j1 k2 hj1 hk2 _ G hFold
    hG_err x M hM1 hx

/-- Spread norm `‖U‖ ≤ (r + 1/2) M` once the spread error coefficient is `≤ 1/2`
(FTP:836 generalized). -/
theorem norm_kroneckerSpreadOfFoldedTaps_le_at
    (p K q m1 t1 r : ℕ) (hw : WindowRules m1 p K) (ht1 : 0 < t1) (hr : 0 < r)
    (hcoef : (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) +
        (2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 / 2)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth m1 r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u),
          G s))
    (hG_err : ∀ s < 2 * m1 + 1,
      |((G s : ℝ) / (2 : ℝ) ^ q) -
          sincGaussian (alphaSchedule (pWork p K)) (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
        (2 : ℝ) ^ (-(q : ℤ)))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M) :
    ‖kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
  have hα : 0 < alphaSchedule (pWork p K) := hw.1
  have hdiff := norm_kroneckerSpreadOfFoldedTaps_sub_le_at p K q m1 t1 r hw ht1 hr j1 k2 hj1 hk2
    gTapFold G hFold hG_err x M hM1 hx
  have hinf := norm_sincGaussianSpreadArray_le
    (alphaSchedule (pWork p K)) hα t1 r hr x M hx j1 k2 hj1 hk2
  have htri := norm_add_le
    (kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
    (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
  rw [sub_add_cancel] at htri
  have hM0 : 0 ≤ M := by linarith
  have h1 : ((6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) +
        (2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ))) * M ≤ (1 / 2) * M :=
    mul_le_mul_of_nonneg_right hcoef hM0
  linarith

/-- FTP:946 with the grid as a parameter: the hypotheses `rqme(q) ≤ 0.125 · 2^-24` and
`t1 · 10 · rqme(q) ≤ 10^-4` replace the snapshot's `q = 2 · pChild`, `t1 ≤ 2^K`. -/
theorem faithful_coeff_ratio_pow_le_at
    (q t1 : ℕ) (h_qerr_small : realQuantizeMaxErr q ≤ (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ))
    (ht1_err : (t1 : ℝ) * (10 * realQuantizeMaxErr q) ≤ (0.0001 : ℝ))
    (a b a_q b_q : ℝ)
    (ha_gt : (0.49999999 : ℝ) ≤ a) (_ha_le : a ≤ 1)
    (hb_nonneg : 0 ≤ b) (hba : b ≤ a)
    (hratio : (b / a) ^ t1 ≤ (0.15 : ℝ))
    (hb_q_nonneg : 0 ≤ b_q) (hba_q : b_q ≤ a_q) (ha_q_le1 : a_q ≤ 1)
    (h_err_a : |a_q - a| ≤ 2 * realQuantizeMaxErr q)
    (h_err_b : |b_q - b| ≤ 2 * realQuantizeMaxErr q) :
    (0.4999 : ℝ) ≤ a_q ∧ a_q ≤ 1 ∧ 0 ≤ b_q ∧ b_q ≤ a_q ∧
      (b_q / a_q) ^ t1 ≤ (0.1501 : ℝ) := by
  have h_a_q_ge : (0.4999 : ℝ) ≤ a_q := by
    have h1 := (abs_le.mp h_err_a).1
    linarith
  refine ⟨h_a_q_ge, ha_q_le1, hb_q_nonneg, hba_q, ?_⟩
  have ha_pos : 0 < a := by linarith
  have ha_q_pos : 0 < a_q := by linarith
  have hdiv_q_abs : |b_q / a_q| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hb_q_nonneg ha_q_pos.le)]
    exact (div_le_one ha_q_pos).mpr hba_q
  have hdiv_abs : |b / a| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hb_nonneg ha_pos.le)]
    exact (div_le_one ha_pos).mpr hba
  have hdiv_diff : |b_q / a_q - b / a| ≤ 10 * realQuantizeMaxErr q := by
    have h1 := abs_div_sub_div_le a b a_q b_q (0.4999 : ℝ)
      (by norm_num) (by linarith) h_a_q_ge hb_nonneg hba
    have h2 : (|b_q - b| + |a_q - a|) / (0.4999 : ℝ) ≤ (4 * realQuantizeMaxErr q) / (0.4999 : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have hq_nonneg : 0 ≤ realQuantizeMaxErr q := rqme_nonneg q
    have h3 : (4 * realQuantizeMaxErr q) / (0.4999 : ℝ) ≤ 10 * realQuantizeMaxErr q := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.4999)]
      linarith
    linarith
  have hpow_diff := abs_pow_sub_pow_le (b_q / a_q) (b / a) hdiv_q_abs hdiv_abs t1
  have hpow_sub : (b_q / a_q) ^ t1 - (b / a) ^ t1 ≤ (t1 : ℝ) * |b_q / a_q - b / a| :=
    (le_abs_self _).trans hpow_diff
  have hmul_le : (t1 : ℝ) * |b_q / a_q - b / a| ≤ (t1 : ℝ) * (10 * realQuantizeMaxErr q) :=
    mul_le_mul_of_nonneg_left hdiv_diff (Nat.cast_nonneg t1)
  linarith

/-- Leaf closure (FTP:452 with the leaf grid `q_leaf` and the slot `LeafSlot` replacing
`q_leaf = 2p + K + 8`). -/
theorem norm_baseRadix2FFTOfTwiddlesAt_sub_dft1D_le
    (q_leaf p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex q_leaf (read1D (twiddles.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤
        2 * complexQuantizeMaxErr q_leaf)
    (hslot : LeafSlot q_leaf p K)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < 2 ^ K, ‖x k‖ ≤ M) (u : ℕ) :
    ‖complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u) - dft1D (2 ^ K) x u‖ ≤
      (2 : ℝ) ^ (-(p : ℤ)) * M := by
  unfold LeafSlot at hslot
  have hpow_le_one := two_zpow_neg_le_one p
  have hq_cond : ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf ≤ 1 := by linarith
  have hcore := norm_baseRadix2FFTCoreOfTwiddles_sub_exact_le q_leaf K twiddles htw hq_cond x M hM1
    hx u
  rw [baseRadix2FFTExact_eq_dft1D] at hcore
  have hM_pos : 0 < M := by linarith
  set z := baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u
  have hcore_le : ‖z - dft1D (2 ^ K) x u‖ ≤ (0.6 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    hcore.trans (mul_le_mul_of_nonneg_right hslot hM_pos.le)
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hout_le : ‖complexQuantize p z - z‖ ≤ (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have h1 := norm_complexQuantize_sub_le p z
    have h2 := (complexQuantizeMaxErr_lt p).le
    have h3 : (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) ≤ (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      nlinarith
    linarith
  have hsplit : complexQuantize p z - dft1D (2 ^ K) x u =
      (complexQuantize p z - z) + (z - dft1D (2 ^ K) x u) := by ring
  have htri := norm_add_le (complexQuantize p z - z) (z - dft1D (2 ^ K) x u)
  rw [← hsplit] at htri
  have hpM : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M := mul_pos hp0 hM_pos
  linarith

#assert_std_axioms norm_windowedSincGaussianSpreadArray_sub_le_at
  norm_kroneckerSpreadOfFoldedTaps_sub_le_at norm_dft2D_kroneckerSpreadOfFoldedTaps_sub_le_at
  norm_kroneckerSpreadOfFoldedTaps_le_at faithful_coeff_ratio_pow_le_at
  norm_baseRadix2FFTOfTwiddlesAt_sub_dft1D_le

end WP.W14
