import WP.W14.Spread

/-!
# W14: the front half of the step closure, at any schedule node

FTP:1586–1816 (spread, pre-twist, synthetic FFT, post-twist, child, odd-stride routing) with the
snapshot's absolute slots `κ · 2^-pChild` replaced by slots in the unit `eUnit p K = 2^-(p+K+10)`
(`StepSlots`). The intermediate arrays are abstract functions with defining equations, so the lemma
applies verbatim to the `let`-bound arrays of `sincGaussianFastDFTOfTablesAt`.

Budget (units `e M`): pre-twist `≤ 0.5`, synthetic FFT `≤ 1.0`, post-twist `≤ 1.5`, `Y` rounding
`≤ 0.1`, spread (tail + taps) `≤ 0.5`; total `2.1 e M + 2^-pChild (r+1) M` (the last term is the
child's own error).
-/

namespace WP.W14

open IntMul Complex Real

/-- Front half of the step closure (FTP:1586–1816) at a node satisfying `StepSlots`. -/
theorem step_front_at
    {p K t1 r c1 pSub m1 : ℕ} {v1Of : ℕ → ℕ → ℕ}
    (ht1 : 0 < t1) (hr : 0 < r)
    (hsize : t1 * r = 2 ^ K) (hc1 : c1 * t1 = r)
    (hv1 : ∀ u2 < r, ∀ u1 : ℕ, ∃ q : ℤ,
      (2 * (u2 : ℤ) - 1) * (v1Of u2 u1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ))
    (hv1_eq : ∀ u2 u1 : ℕ, v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1)
    (hS : StepSlots pSub m1 p K)
    (filterTaps : Array (List ℤ)) (preTwiddles postTwiddles : Array (ℤ × ℤ))
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
    (childDFT : (ℕ → ℂ) → ℕ → ℂ)
    (hchild_err : ∀ (x' : ℕ → ℂ) (M' : ℝ), 1 ≤ M' →
      (∀ k < r, ‖x' k‖ ≤ M') → ∀ u' < r,
      ‖childDFT x' u' - dft1D r x' u'‖ ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * M')
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (U P Q qPost Y : ℕ → ℕ → ℂ)
    (hU : ∀ j1 k2, U j1 k2 =
      kroneckerSpreadOfFoldedTaps pSub m1 t1 r (filterTaps.getD j1 []) x j1 k2)
    (hP : ∀ j1 k2, P j1 k2 =
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2))
    (hQ : ∀ v1 k2, Q v1 k2 =
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2))
    (hqPost : ∀ v1 k2, qPost v1 k2 =
      complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2))
    (hY : ∀ u2 u1, Y u2 u1 =
      complexQuantize pSub (childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 u1)) u2))
    (u2 : ℕ) (hu2 : u2 < r) (k : ℕ) :
    ‖Y u2 k - dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2‖ ≤
      2.1 * eUnit p K * M + (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M) := by
  have hM_pos : 0 < M := by linarith
  have hc0 := cqme_nonneg pSub
  have he0 := eUnit_pos p K
  have he_small := eUnit_le_small p K
  have hr_le_2K : r ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_left r ht1
  obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  have hcr := hS.hcr_le hr_le_2K
  have hclog := hS.hclog_le hlog_le_2K
  have hc_le := hS.hc
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hMr_ge1 : 1 ≤ ((r : ℝ) + 1) * M := by nlinarith
  have heM : eUnit p K ≤ eUnit p K * M := by nlinarith
  have hU_norm : ∀ j1 < t1, ∀ k2 < r, ‖U j1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
    intro j1 hj1 k2 hk2
    rw [hU]
    rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
    exact norm_kroneckerSpreadOfFoldedTaps_le_at p K pSub m1 t1 r hS.window ht1 hr hS.hcoef
      j1 k2 hj1 hk2 _ G hFold hG_err x M hM1 hx
  have htw_coef : complexQuantizeMaxErr pSub +
      2 * complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) ≤ 0.5 * eUnit p K * M := by
    have h1 : complexQuantizeMaxErr pSub ≤ complexQuantizeMaxErr pSub * M := by nlinarith
    nlinarith
  let P_unq : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
  have hP_err : ∀ j1 < t1, ∀ k2 < r, ‖P j1 k2 - P_unq j1 k2‖ ≤ 0.5 * eUnit p K * M := by
    intro j1 hj1 k2 hk2
    have hsplit : P j1 k2 - P_unq j1 k2 =
        (P j1 k2 - toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2) +
          (toScaledComplex pSub (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)) * U j1 k2 := by
      dsimp only [P_unq]; ring
    rw [hsplit]
    have h1 : ‖P j1 k2 - toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2‖ ≤
        complexQuantizeMaxErr pSub := by
      rw [hP]; exact norm_complexQuantize_sub_le pSub _
    have h2_U : ‖U j1 k2‖ ≤ ((r : ℝ) + 1) * M := by have := hU_norm j1 hj1 k2 hk2; linarith
    have h2 : ‖(toScaledComplex pSub (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)) * U j1 k2‖ ≤
        2 * complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) := by
      rw [norm_mul]; exact mul_le_mul (hPre k2 hk2) h2_U (norm_nonneg _) (by positivity)
    have htri := norm_add_le
      (P j1 k2 - toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
      ((toScaledComplex pSub (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)) * U j1 k2)
    linarith
  have hQ_err : ∀ v1 : ℕ, ∀ k2 < r,
      ‖Q v1 k2 - syntheticDFT t1 r P_unq v1 k2‖ ≤ 1.0 * eUnit p K * M := by
    intro v1 k2 hk2
    have h1 := norm_syntheticFFTRadix2Quantized_sub_syntheticDFT_le pSub t1 r ht1_pow hr
      P P_unq (0.5 * eUnit p K * M) hP_err v1 k2 hk2
    rw [← hQ] at h1
    have h2 : ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub ≤ 0.5 * eUnit p K * M := by
      nlinarith
    linarith
  have hQ_unq_norm : ∀ v1 : ℕ, ∀ k2 < r,
      ‖syntheticDFT t1 r P_unq v1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
    intro v1 k2 hk2
    refine norm_syntheticDFT_le t1 r ht1 hr P_unq (((r : ℝ) + (0.5 : ℝ)) * M) ?_ v1 k2 hk2
    intro j1 hj1 m hm
    dsimp only [P_unq]
    rw [norm_mul, norm_zetaRoot, one_mul]
    exact hU_norm j1 hj1 m hm
  have hQ_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖Q v1 k2‖ ≤ ((r : ℝ) + 1) * M := by
    intro v1 k2 hk2
    have htri := norm_add_le (Q v1 k2 - syntheticDFT t1 r P_unq v1 k2)
      (syntheticDFT t1 r P_unq v1 k2)
    rw [sub_add_cancel] at htri
    have h1 := hQ_err v1 k2 hk2
    have h2 := hQ_unq_norm v1 k2 hk2
    have h3 : 1.0 * eUnit p K * M ≤ 0.5 * M := by nlinarith
    linarith
  let qPost_unq : ℕ → ℕ → ℂ := fun v1 k2 =>
    zetaRoot r (-(k2 : ℝ)) * syntheticDFT t1 r P_unq v1 k2
  have hqPost_err : ∀ v1 : ℕ, ∀ k2 < r,
      ‖qPost v1 k2 - qPost_unq v1 k2‖ ≤ 1.5 * eUnit p K * M := by
    intro v1 k2 hk2
    have hsplit : qPost v1 k2 - qPost_unq v1 k2 =
        (qPost v1 k2 - toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2) +
          (toScaledComplex pSub (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))) * Q v1 k2 +
          zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - syntheticDFT t1 r P_unq v1 k2) := by
      dsimp only [qPost_unq]; ring
    rw [hsplit]
    have h1 : ‖qPost v1 k2 - toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2‖ ≤
        complexQuantizeMaxErr pSub := by
      rw [hqPost]; exact norm_complexQuantize_sub_le pSub _
    have h2 : ‖(toScaledComplex pSub (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))) *
        Q v1 k2‖ ≤ 2 * complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) := by
      rw [norm_mul]
      exact mul_le_mul (hPost k2 hk2) (hQ_norm v1 k2 hk2) (norm_nonneg _) (by positivity)
    have h3 : ‖zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - syntheticDFT t1 r P_unq v1 k2)‖ ≤
        1.0 * eUnit p K * M := by
      rw [norm_mul, norm_zetaRoot, one_mul]; exact hQ_err v1 k2 hk2
    have htri1 := norm_add_le
      ((qPost v1 k2 - toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2) +
        (toScaledComplex pSub (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
      (zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - syntheticDFT t1 r P_unq v1 k2))
    have htri2 := norm_add_le
      (qPost v1 k2 - toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
      ((toScaledComplex pSub (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    linarith
  have hqPost_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖qPost v1 k2‖ ≤ ((r : ℝ) + 1) * M := by
    intro v1 k2 hk2
    have htri := norm_add_le (qPost v1 k2 - qPost_unq v1 k2) (qPost_unq v1 k2)
    rw [sub_add_cancel] at htri
    have h1 := hqPost_err v1 k2 hk2
    have h2 : ‖qPost_unq v1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
      dsimp only [qPost_unq]
      rw [norm_mul, norm_zetaRoot, one_mul]
      exact hQ_unq_norm v1 k2 hk2
    have h3 : 1.5 * eUnit p K * M ≤ 0.5 * M := by nlinarith
    linarith
  -- child, rounding and odd-stride routing
  rcases hv1 u2 hu2 k with ⟨q, hq⟩
  have hq' : (2 * (u2 : ℤ) - 1) * ((oddStrideInvPow2 (Nat.log2 t1) u2 k : ℕ) : ℤ) =
      (k : ℤ) + q * (t1 : ℤ) := by rw [← hv1_eq u2 k]; exact hq
  have hpipe := theorem1_pipeline_computes_dft2D t1 r c1 ht1 hr hc1 U
    (oddStrideInvPow2 (Nat.log2 t1) u2 k) k u2 q hq'
  dsimp only at hpipe
  have hpipe_eq : dft1D r (qPost_unq (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 =
      dft2D t1 r U k u2 := hpipe
  have hih := hchild_err (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) (((r : ℝ) + 1) * M)
    hMr_ge1 (hqPost_norm (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 hu2
  have h_dft1D_sub :
      ‖dft1D r (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 -
        dft1D r (qPost_unq (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2‖ ≤ 1.5 * eUnit p K * M :=
    norm_dft1D_sub_le r hr _ _ (1.5 * eUnit p K * M)
      (hqPost_err (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2
  have h_Y_round : ‖Y u2 k - childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2‖ ≤
      complexQuantizeMaxErr pSub := by
    rw [hY]; exact norm_complexQuantize_sub_le pSub _
  have hY_win_err : ‖Y u2 k - dft2D t1 r U k u2‖ ≤
      1.6 * eUnit p K * M + (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M) := by
    have hsplit : Y u2 k - dft2D t1 r U k u2 =
        (Y u2 k - childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2) +
          (childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 -
            dft1D r (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2) +
          (dft1D r (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 -
            dft1D r (qPost_unq (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2) := by
      rw [← hpipe_eq]; ring
    rw [hsplit]
    have htri1 := norm_add_le
      ((Y u2 k - childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2) +
        (childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 -
          dft1D r (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2))
      (dft1D r (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 -
        dft1D r (qPost_unq (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2)
    have htri2 := norm_add_le
      (Y u2 k - childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2)
      (childDFT (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2 -
        dft1D r (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 k)) u2)
    have hcM : complexQuantizeMaxErr pSub ≤ 0.1 * eUnit p K * M := by nlinarith
    linarith
  -- spread error (tail + tap quantization)
  have hUeq : U = fun j1 k2 =>
      kroneckerSpreadOfFoldedTaps pSub m1 t1 r (filterTaps.getD j1 []) x j1 k2 :=
    funext fun j1 => funext fun k2 => hU j1 k2
  have hB12_err : ‖dft2D t1 r U k u2 -
      dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2‖ ≤
      0.5 * eUnit p K * M := by
    have h1 := norm_dft2D_kroneckerSpreadOfFoldedTaps_sub_le_at p K pSub m1 t1 r hS.window ht1 hr
      filterTaps hTaps x M hM1 hx k u2
    rw [hUeq]
    exact h1.trans (mul_le_mul_of_nonneg_right hS.hB12 hM_pos.le)
  have hsplit : Y u2 k -
      dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2 =
      (Y u2 k - dft2D t1 r U k u2) +
        (dft2D t1 r U k u2 -
          dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2) := by ring
  rw [hsplit]
  have htri := norm_add_le (Y u2 k - dft2D t1 r U k u2)
    (dft2D t1 r U k u2 -
      dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) k u2)
  linarith

#assert_std_axioms step_front_at

end WP.W14
