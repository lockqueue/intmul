import WP.W11b.Main

/-!
# WP.W11b.Root — the root clauses of `RootOK` (`RootStmt`)

Replays the root part of the snapshot's `programCost_root_pipeline_widths_sound_of_faithful`
(CSWS:2100-2246) on W9's root stages:
* the packed input dequantizes to the normalized chunks, of norm `≤ √2` (so `NodeInv` at `b`);
* the forward transform has norm `≤ 4`, so the squared and conjugated values have norm `≤ 17`
  (so `NodeInv` at `p0`);
* both transform outputs have width `2·p0 + 4 ≤ 4·p0` (`dft_out`);
* each digit is `(divRoundPow2 (-z.2) 9).toNat ≤ |z.2|` (`W8_extractRootSlot_shift_holds`).
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

theorem size_rootPackV (b K0 k1 k2 A B : ℕ) : (rootPackV b K0 k1 k2 A B).size = 2 ^ K0 := by
  unfold rootPackV
  simp [size_runSequentialScanSteps]

theorem size_rootSquareV (p0 K0 : ℕ) (y : Array (ℤ × ℤ)) : (rootSquareV p0 K0 y).size = 2 ^ K0 := by
  unfold rootSquareV
  simp [size_runSequentialScanSteps]

theorem digit_le_natAbs (a : ℤ) : (divRoundPow2 (-a) 9).toNat ≤ a.natAbs := by
  have h : divRoundPow2 (-a) 9 = (-a + 256) / 512 := by
    unfold divRoundPow2
    rw [if_neg (by norm_num)]
    norm_num
  rw [h, Int.toNat_le, ← Int.abs_eq_natAbs]
  have h1 := le_abs_self a
  have h2 := neg_le_abs a
  omega

theorem bitLen_digit_le {w W : ℕ} {z : ℤ × ℤ} (hz : EntryW w z) (hW : w ≤ W) :
    bitLen (divRoundPow2 (-z.2) 9).toNat ≤ W := by
  rw [bitLen_le_iff]
  have h2 : z.2.natAbs < 2 ^ w := (bitLen_le_iff _ _).mp hz.2
  have hpow : 2 ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have := digit_le_natAbs z.2
  omega

theorem root_parts : RootStmt := by
  intro n A B cSpec hfaith
  dsimp only
  have hp0 : 8 ≤ rootPrecision (IntMulTM.Contracts.W8.hB n) (IntMulTM.Contracts.W8.hK0 n) :=
    (W7.headline_pre n).1
  have hvalid : (IntMulTM.Contracts.W8.hSpec n).Valid := buildQuantizedSpecPaperStop_valid _ _ _ hp0
  have hsize : (IntMulTM.Contracts.W8.hSpec n).size = 2 ^ IntMulTM.Contracts.W8.hK0 n :=
    buildQuantizedSpecPaperStop_size _ _ _
  have hsp : (IntMulTM.Contracts.W8.hSpec n).p =
      rootPrecision (IntMulTM.Contracts.W8.hB n) (IntMulTM.Contracts.W8.hK0 n) :=
    buildQuantizedSpecPaperStop_p _ _ _
  set b := IntMulTM.Contracts.W8.hB n
  set K0 := IntMulTM.Contracts.W8.hK0 n
  set k := IntMulTM.Contracts.W8.hK n
  set spec := IntMulTM.Contracts.W8.hSpec n
  set p0 := rootPrecision b K0 with hp0_def
  have hwR : wRHead n = 4 * p0 := rfl
  have hbp : b ≤ p0 := by rw [hp0_def]; unfold rootPrecision; omega
  have hsp' : spec.p = p0 := hsp
  have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_le2 : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ p0 := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ p0 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq_err : complexQuantizeMaxErr p0 ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt p0
    have hpow_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    nlinarith
  -- the packed input
  set x0 := rootPackV b K0 k k A B with hx0_def
  have hx_pack : ∀ j < spec.size, packNormalizedChunks b k k A B j = toScaledComplex b (read1D x0 j) :=
    fun j hj => (toScaledComplex_computablePackChunksExact_eq b k k (2 ^ K0) A B j (hsize ▸ hj)).symm
  have hN0 : NodeInv spec b x0 := by
    refine ⟨by rw [hsize]; exact size_rootPackV _ _ _ _ _ _, fun j hj => ?_⟩
    rw [← hx_pack j hj, hsp]
    exact (norm_packNormalizedChunks_le_sqrt_two b k k A B j).trans (hsqrt2_le2.trans (by linarith))
  -- the forward transform
  set y := computablePaperFastDFT b cSpec x0 with hy_def
  have hyo := dft_out hvalid hfaith hN0.2
  have hy : ∀ u < spec.size, toScaledComplex p0 (read1D y u) =
      sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u := by
    intro u hu
    rw [← hsp]
    exact toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith b x0 _ hx_pack u hu
  have hy4 : ∀ u < spec.size, ‖sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u‖ ≤ 4 := by
    intro u hu
    have herr := sincGaussianFastDFTOfTables_error_le spec hvalid cSpec hfaith _ (Real.sqrt 2)
      hsqrt2_ge1 (fun j _ => norm_packNormalizedChunks_le_sqrt_two b k k A B j) u hu
    have hdft := dft1D_norm_le spec.size (by omega) (packNormalizedChunks b k k A B) (Real.sqrt 2)
      (fun j _ => norm_packNormalizedChunks_le_sqrt_two b k k A B j) u
    have hpow : (2 : ℝ) ^ (-(spec.p : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hm := mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ Real.sqrt 2) hpow
    have htri := norm_add_le
      (sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u -
        dft1D spec.size (packNormalizedChunks b k k A B) u)
      (dft1D spec.size (packNormalizedChunks b k k A B) u)
    rw [sub_add_cancel] at htri
    linarith
  -- the squared and conjugated values
  set z := rootSquareV p0 K0 y with hz_def
  have hz17 : ∀ u < spec.size, ‖toScaledComplex p0 (read1D z u)‖ ≤ 17 := by
    intro u hu
    have hu' : u < 2 ^ K0 := hsize ▸ hu
    rw [hz_def]
    unfold rootSquareV
    rw [read1D_runSequentialScanSteps_eq _ _ u hu', toScaledComplex_gConj,
      toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu, norm_star]
    have h4 := hy4 u hu
    have hsq : ‖sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u *
        sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u‖ ≤ 16 := by
      rw [norm_mul]
      nlinarith [norm_nonneg (sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u)]
    have h1 := norm_complexQuantize_le p0
      (sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u *
        sincGaussianFastDFTOfTables cSpec (packNormalizedChunks b k k A B) u)
    linarith
  have hNz : NodeInv spec p0 z := by
    refine ⟨by rw [hsize]; exact size_rootSquareV _ _ _, fun u hu => ?_⟩
    rw [hsp]
    exact (hz17 u hu).trans (by linarith)
  -- the inverse transform
  have hvo := dft_out hvalid hfaith hNz.2
  have hw2 : 2 * spec.p + 4 ≤ wRHead n := by omega
  have hwz : ArrW (wRHead n) z := arrW_input hNz.1 hNz.2 (by omega)
  refine ⟨hN0, hNz, by rw [hyo.1, hsize], arrW_input hN0.1 hN0.2 (by omega),
    arrW_mono hyo.2 hw2, hwz, by rw [hvo.1, hsize], arrW_mono hvo.2 hw2, ?_⟩
  intro c hc
  simp only [rootDigits, List.mem_map, List.mem_range] at hc
  obtain ⟨j, -, rfl⟩ := hc
  unfold rootExtractV
  by_cases hj : j < 2 ^ K0
  · rw [read1D_runSequentialScanSteps_eq _ _ j hj, IntMulTM.Contracts.W8_extractRootSlot_shift_holds]
    exact bitLen_digit_le (entryW_read1D_of_arrW (arrW_mono hvo.2 hw2) j) le_rfl
  · have hz0 : read1D (runSequentialScanSteps (fun j =>
        (costedExtractRootSlot p0 b K0 (read1D (computablePaperFastDFT p0 cSpec z) j)).1)
        (2 ^ K0)).outTape j = 0 := by
      unfold read1D
      rw [dif_neg (by simpa [size_runSequentialScanSteps] using hj)]
    rw [hz0, bitLen_zero]
    exact Nat.zero_le _

#assert_std_axioms size_rootPackV size_rootSquareV digit_le_natAbs bitLen_digit_le root_parts

end WP.W11b
