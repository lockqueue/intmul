import IntMul.MaterializedAndComputable.ComputableTableBuilder

/-!
# Part 3 — Per-Call-Site Value-Level Operand Width Soundness (`programCost_widths_sound`) & Headline Theorem
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-- Signed two's-complement word-width predicate on a Gaussian-integer pair `z : ℤ × ℤ`
(`FitsSignedWord`, `[MS]` §3.2): both coordinates fit strictly inside a signed `w`-bit word,
i.e., `|z.1| < 2 ^ (w - 1) ∧ |z.2| < 2 ^ (w - 1)`. -/
def FitsSignedWord (w : ℕ) (z : ℤ × ℤ) : Prop :=
  |z.1| < (2 : ℤ) ^ (w - 1) ∧ |z.2| < (2 : ℤ) ^ (w - 1)

theorem fitsSignedWord_mono {w1 w2 : ℕ} {z : ℤ × ℤ}
    (h : FitsSignedWord w1 z) (hw : w1 ≤ w2) :
    FitsSignedWord w2 z := by
  have hpow : (2 : ℤ) ^ (w1 - 1) ≤ (2 : ℤ) ^ (w2 - 1) := by
    exact_mod_cast Nat.pow_le_pow_right zero_lt_two (by omega)
  exact ⟨h.1.trans_le hpow, h.2.trans_le hpow⟩

/-- Bridge lemma from Euclidean norm of `toScaledComplex q z` to `FitsSignedWord w z` (`[MS]` §3.2). -/
theorem fitsSignedWord_of_norm_toScaledComplex_le
    (q M w : ℕ) (z : ℤ × ℤ)
    (hnorm : ‖toScaledComplex q z‖ ≤ (2 : ℝ) ^ M)
    (hw : M + q + 2 < w - 1) :
    FitsSignedWord w z := by
  unfold FitsSignedWord
  have hre : |(toScaledComplex q z).re| ≤ (2 : ℝ) ^ M :=
    (Complex.abs_re_le_norm (toScaledComplex q z)).trans hnorm
  have him : |(toScaledComplex q z).im| ≤ (2 : ℝ) ^ M :=
    (Complex.abs_im_le_norm (toScaledComplex q z)).trans hnorm
  dsimp only [toScaledComplex] at hre him
  have hscale_pos : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
  rw [abs_div, abs_of_pos hscale_pos, div_le_iff₀ hscale_pos, ← pow_add] at hre him
  have hpow_lt : (2 : ℝ) ^ (M + (q + 2)) < (2 : ℝ) ^ (w - 1) :=
    pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)
  have hre_lt : |(z.1 : ℝ)| < (2 : ℝ) ^ (w - 1) := hre.trans_lt hpow_lt
  have him_lt : |(z.2 : ℝ)| < (2 : ℝ) ^ (w - 1) := him.trans_lt hpow_lt
  rw [← Int.cast_abs] at hre_lt him_lt
  exact ⟨by exact_mod_cast hre_lt, by exact_mod_cast him_lt⟩

theorem fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le
    (p K : ℕ) (z : ℤ × ℤ)
    (hnorm : ‖toScaledComplex (2 * pChild p K) z‖ ≤ (2 : ℝ) ^ (pChild p K)) :
    FitsSignedWord (4 * pChild p K) z := by
  have hp'_ge12 : 12 ≤ pChild p K := by
    rw [pChild_eq_additive]
    omega
  exact fitsSignedWord_of_norm_toScaledComplex_le
    (2 * pChild p K) (pChild p K) (4 * pChild p K) z hnorm (by omega)

/-- **Call-Site Width Soundness 1 — Spread (`programCost_spread_widths_sound`, `[MS]` §3.2)**:
Every output bucket entry of `computableSpreadRowContiguousWithProgramCost` fits in a signed word of
width `6 * pChild p K` bits (`FitsSignedWord (6 * pChild p K)`), matching the width `6 * p'` passed
to `overlapAddBucketsSinglePassWithCost` and `costedGPreTwistU`. -/
theorem programCost_spread_widths_sound
    (p_in p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (x : ℕ → ℂ) (hx_norm : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (xRow : Array (ℤ × ℤ))
    (hxRow : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) :
    let p' := pChild p K
    let pSub := 2 * p'
    let α := alphaSchedule (pWork p K)
    let taps := kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1
    FitsSignedWord (6 * p')
      (read1D (computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r taps xRow).1 k2) := by
  dsimp only
  rw [computableSpreadRowContiguousWithProgramCost_fst]
  have huRaw := computableSpreadRowContiguousWithCost_eq_kroneckerSincGaussianSpreadArray
    (alphaSchedule (pWork p K)) p_in (2 * pChild p K) (2 * pChild p K) t1 r xRow x j1 k2 hxRow hk2
  exact raw_spread_coord_mem_six_mul_pChild_word p K t1 r ht1 hr hsize x hx_norm j1 k2 hj1 hk2 _ huRaw

/-- Multi-stage norm bound for `computableSyntheticFFTRadix2`: for any `p V r m c1 : ℕ` (`0 < r`)
and 2D array `P : Array (Array (ℤ × ℤ))`, if `∀ j1 < 2 ^ m, ∀ k2 < r, ‖toScaledComplex p ((P.getD j1 #[]).getD k2 (0, 0))‖ ≤ M_P`,
then for all `v1 < 2 ^ m` and `k2 < r`,
`‖toScaledComplex p (((computableSyntheticFFTRadix2 V r m c1 P).getD v1 #[]).getD k2 (0, 0))‖ ≤ M_P + (m : ℝ) * complexQuantizeMaxErr p`. -/
theorem norm_toScaledComplex_computableSyntheticFFTRadix2_le
    (p V r m c1 : ℕ) (hr : 0 < r)
    (P : Array (Array (ℤ × ℤ))) (M_P : ℝ)
    (hP : ∀ j1 < 2 ^ m, ∀ k2 < r, ‖toScaledComplex p ((P.getD j1 #[]).getD k2 (0, 0))‖ ≤ M_P)
    (v1 k2 : ℕ) (hv1 : v1 < 2 ^ m) (hk2 : k2 < r) :
    ‖toScaledComplex p (((computableSyntheticFFTRadix2 V r m c1 P).getD v1 #[]).getD k2 (0, 0))‖ ≤
      M_P + (m : ℝ) * complexQuantizeMaxErr p := by
  induction m generalizing c1 P v1 k2 with
  | zero =>
    dsimp only [computableSyntheticFFTRadix2]
    have hv0 : v1 < 1 := by simpa using hv1
    rw [array_getD_ofFn_of_lt 1 _ #[] v1 hv0, array_getD_ofFn_of_lt r _ (0, 0) k2 hk2]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact hP 0 (by simp) k2 hk2
  | succ m ih =>
    dsimp only [computableSyntheticFFTRadix2]
    set Peven := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val) #[])
    set Podd := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val + 1) #[])
    set Y0 := computableSyntheticFFTRadix2 V r m (2 * c1) Peven
    set Y1 := computableSyntheticFFTRadix2 V r m (2 * c1) Podd
    rw [array_getD_ofFn_of_lt (2 ^ (m + 1)) _ #[] v1 hv1, array_getD_ofFn_of_lt r _ (0, 0) k2 hk2]
    dsimp only
    rw [toScaledComplex_divRoundPow2_one_eq_complexQuantize_avg]
    have hv1_mod : v1 % 2 ^ m < 2 ^ m := Nat.mod_lt v1 (pow_pos zero_lt_two m)
    have hY0 : ‖toScaledComplex p ((Y0.getD (v1 % 2 ^ m) #[]).getD k2 (0, 0))‖ ≤
        M_P + (m : ℝ) * complexQuantizeMaxErr p := by
      refine ih (2 * c1) Peven (fun j1 hj1 m' hm' => ?_) (v1 % 2 ^ m) k2 hv1_mod hk2
      dsimp only [Peven]
      rw [array_getD_ofFn_of_lt (2 ^ m) _ #[] j1 hj1]
      exact hP (2 * j1) (by rw [pow_succ']; omega) m' hm'
    have hY1_all : ∀ m' < r,
        ‖toScaledComplex p ((Y1.getD (v1 % 2 ^ m) #[]).getD m' (0, 0))‖ ≤
          M_P + (m : ℝ) * complexQuantizeMaxErr p := by
      intro m' hm'
      refine ih (2 * c1) Podd (fun j1 hj1 k'' hk'' => ?_) (v1 % 2 ^ m) m' hv1_mod hm'
      dsimp only [Podd]
      rw [array_getD_ofFn_of_lt (2 ^ m) _ #[] j1 hj1]
      exact hP (2 * j1 + 1) (by rw [pow_succ']; omega) k'' hk''
    have hY1_shift :
        ‖toScaledComplex p ((computableNegacyclicDirect r (2 * c1 * v1) (Y1.getD (v1 % 2 ^ m) #[])).getD k2 (0, 0))‖ ≤
          M_P + (m : ℝ) * complexQuantizeMaxErr p := by
      rw [toScaledComplex_computableNegacyclicDirect_eq p r (2 * c1 * v1) (Y1.getD (v1 % 2 ^ m) #[]) k2 hk2]
      exact norm_negacyclicShiftIter_le r (2 * c1 * v1) hr _ _ hY1_all k2 hk2
    set avg := (toScaledComplex p ((Y0.getD (v1 % 2 ^ m) #[]).getD k2 (0, 0)) +
      toScaledComplex p ((computableNegacyclicDirect r (2 * c1 * v1) (Y1.getD (v1 % 2 ^ m) #[])).getD k2 (0, 0))) / 2
    have havg : ‖avg‖ ≤ M_P + (m : ℝ) * complexQuantizeMaxErr p := by
      dsimp [avg]
      rw [norm_div, Complex.norm_ofNat]
      have htri := norm_add_le
        (toScaledComplex p ((Y0.getD (v1 % 2 ^ m) #[]).getD k2 (0, 0)))
        (toScaledComplex p ((computableNegacyclicDirect r (2 * c1 * v1) (Y1.getD (v1 % 2 ^ m) #[])).getD k2 (0, 0)))
      linarith
    have hq := norm_complexQuantize_le p avg
    push_cast
    linarith

/-- **Call-Site Width Soundness 2 — Pre-Twist, Synthetic FFT Butterfly Stages, Rescale, and Post-Twist
(`programCost_twist_and_syntheticFFT_widths_sound`, `[MS]` §3.2)**:
Stated directly over the computable intermediate `Array (Array (ℤ × ℤ))` matrices `U_mat`, `P_mat`,
`computableSyntheticFFTRadix2WithProgramCost` at every stage `s ≤ Nat.log2 t1`, `Q_mat`, and `qPost_mat`
of `computablePaperFastDFTWithProgramCost`:
- `read2D U_mat j1 k2` satisfies `FitsSignedWord (6 * pChild p K)` (`costedGPreTwistU pSub (6 * p')`),
- `read2D P_mat j1 k2` satisfies `FitsSignedWord (4 * pChild p K)`,
- `read2D (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1 v1 k2` satisfies
  `FitsSignedWord (4 * pChild p K)` at every stage `s ≤ Nat.log2 t1` (`costedButterflyAvg (4 * p')`
  and `costedGRescale pSub pSub (4 * p')`),
- `read2D Q_mat v1 k2` satisfies `FitsSignedWord (4 * pChild p K)` and `FitsSignedWord (6 * pChild p K)`
  (`costedGMulScaled (pSub + 2) (6 * p')`), and
- `read2D qPost_mat v1 k2` satisfies `FitsSignedWord (4 * pChild p K)`. -/
theorem programCost_twist_and_syntheticFFT_widths_sound
    (p_in p K t1 r c1 : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K) (hc1 : c1 * t1 = r)
    (x : ℕ → ℂ) (hx_norm : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (xRows : Array (Array (ℤ × ℤ)))
    (hxRows : ∀ j1 < t1, ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i))
    (j1 v1 k2 s : ℕ) (hj1 : j1 < t1) (hv1 : v1 < t1) (hk2 : k2 < r) (hs : s ≤ Nat.log2 t1) :
    let p' := pChild p K
    let pSub := 2 * p'
    let α := alphaSchedule (pWork p K)
    let filterTaps : Array (List ℤ) :=
      Array.ofFn (fun j1' : Fin t1 => kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1'.val)
    let preTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2' : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (k2'.val : ℝ)).re,
         realQuantizeInt pSub (zetaRoot r (k2'.val : ℝ)).im))
    let postTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2' : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (-(k2'.val : ℝ))).re,
         realQuantizeInt pSub (zetaRoot r (-(k2'.val : ℝ))).im))
    let U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun j1' : Fin t1 =>
        computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
          (filterTaps.getD j1'.val []) (xRows.getD j1'.val #[]))
    let U_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun j1' : Fin t1 => if h : j1'.val < U_rows.size then U_rows[j1'.val].1 else #[])
    let P_mat : Array (Array (ℤ × ℤ)) :=
      (runScan2DCostedWithSteps t1 r (fun j1' k2' =>
        costedGPreTwistU pSub (6 * p') (read1D preTwiddles k2') (read2D U_mat j1' k2'))).1
    let syn_stage : Array (Array (ℤ × ℤ)) :=
      (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1
    let syn_out : Array (Array (ℤ × ℤ)) :=
      (computableSyntheticFFTRadix2WithProgramCost p' t1 r (Nat.log2 t1) (r / t1) P_mat).1
    let Q_mat : Array (Array (ℤ × ℤ)) :=
      (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
        costedGRescale pSub pSub (4 * p') (read2D syn_out v1' k2'))).1
    let qPost_mat : Array (Array (ℤ × ℤ)) :=
      (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
        costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2') (read2D Q_mat v1' k2'))).1
    FitsSignedWord (6 * p') (read2D U_mat j1 k2) ∧
    FitsSignedWord (4 * p') (read2D P_mat j1 k2) ∧
    (∀ v1_s < 2 ^ s, FitsSignedWord (4 * p') (read2D syn_stage v1_s k2)) ∧
    FitsSignedWord (4 * p') (read2D Q_mat v1 k2) ∧
    FitsSignedWord (6 * p') (read2D Q_mat v1 k2) ∧
    FitsSignedWord (4 * p') (read2D qPost_mat v1 k2) := by
  dsimp only
  obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  set p' := pChild p K
  set pSub := 2 * p'
  set α := alphaSchedule (pWork p K)
  set filterTaps : Array (List ℤ) :=
    Array.ofFn (fun j1' : Fin t1 => kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1'.val)
  set preTwiddles : Array (ℤ × ℤ) :=
    Array.ofFn (fun k2' : Fin r =>
      (realQuantizeInt pSub (zetaRoot r (k2'.val : ℝ)).re,
       realQuantizeInt pSub (zetaRoot r (k2'.val : ℝ)).im))
  set postTwiddles : Array (ℤ × ℤ) :=
    Array.ofFn (fun k2' : Fin r =>
      (realQuantizeInt pSub (zetaRoot r (-(k2'.val : ℝ))).re,
       realQuantizeInt pSub (zetaRoot r (-(k2'.val : ℝ))).im))
  set U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
    Array.ofFn (fun j1' : Fin t1 =>
      computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
        (filterTaps.getD j1'.val []) (xRows.getD j1'.val #[]))
  set U_mat : Array (Array (ℤ × ℤ)) :=
    Array.ofFn (fun j1' : Fin t1 => if h : j1'.val < U_rows.size then U_rows[j1'.val].1 else #[])
  set P_mat : Array (Array (ℤ × ℤ)) :=
    (runScan2DCostedWithSteps t1 r (fun j1' k2' =>
      costedGPreTwistU pSub (6 * p') (read1D preTwiddles k2') (read2D U_mat j1' k2'))).1
  set syn_stage : Array (Array (ℤ × ℤ)) :=
    (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1
  set syn_out : Array (Array (ℤ × ℤ)) :=
    (computableSyntheticFFTRadix2WithProgramCost p' t1 r (Nat.log2 t1) (r / t1) P_mat).1
  set Q_mat : Array (Array (ℤ × ℤ)) :=
    (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
      costedGRescale pSub pSub (4 * p') (read2D syn_out v1' k2'))).1
  set qPost_mat : Array (Array (ℤ × ℤ)) :=
    (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
      costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2') (read2D Q_mat v1' k2'))).1
  have hU_entry : FitsSignedWord (6 * p') (read2D U_mat j1 k2) := by
    dsimp only [U_mat, U_rows, filterTaps]
    rw [read2D_ofFn_of_lt t1 _ hj1 k2]
    simp only [Array.size_ofFn, hj1, ↓reduceDIte, Array.getElem_ofFn,
      array_getD_ofFn_of_lt t1 _ [] j1 hj1]
    exact programCost_spread_widths_sound p_in p K t1 r ht1 hr hsize x hx_norm j1 k2 hj1 hk2
      (xRows.getD j1 #[]) (hxRows j1 hj1)
  have hP_eq : ∀ j1' < t1, ∀ k2' < r,
      toScaledComplex pSub (read2D P_mat j1' k2') = stepPreTwist p K t1 r x j1' k2' := by
    intro j1' hj1' k2' hk2'
    dsimp only [P_mat, runScan2DCostedWithSteps, costedGPreTwistU, stepPreTwist, stepSpread]
    rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1' hk2']
    have htw : toScaledComplex pSub (read1D preTwiddles k2') =
        complexQuantize pSub (zetaRoot r (k2' : ℝ)) := by
      dsimp only [preTwiddles]
      rw [read1D_ofFn_of_lt r _ hk2']
      exact toScaledComplex_realQuantizeInt_pair pSub (zetaRoot r (k2' : ℝ))
    have hU_row : read2D U_mat j1' k2' =
        read1D (computableSpreadRowContiguousWithCost p_in pSub pSub r
          (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1') (xRows.getD j1' #[])).1 k2' := by
      dsimp only [U_mat, U_rows, filterTaps]
      rw [read2D_ofFn_of_lt t1 _ hj1' k2']
      simp only [Array.size_ofFn, hj1', ↓reduceDIte, Array.getElem_ofFn,
        array_getD_ofFn_of_lt t1 _ [] j1' hj1',
        computableSpreadRowContiguousWithProgramCost_fst]
    rw [hU_row, ← htw]
    exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2') _ _
      (computableSpreadRowContiguousWithCost_eq_kroneckerSincGaussianSpreadArray
        α p_in pSub pSub t1 r (xRows.getD j1' #[]) x j1' k2' (hxRows j1' hj1') hk2').symm
  have hbounds := step_intermediate_word_width_bounds p K t1 r ht1 hr hsize x hx_norm j1 v1 k2 s hj1 hk2 hs
  have hP_entry : FitsSignedWord (4 * p') (read2D P_mat j1 k2) := by
    refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K (read2D P_mat j1 k2) ?_
    rw [hP_eq j1 hj1 k2 hk2]
    exact hbounds.2.1
  have h2s_le_t1 : 2 ^ s ≤ t1 := by
    rw [← ht1_pow]
    exact Nat.pow_le_pow_right zero_lt_two hs
  have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
    rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
  have hsyn_stage_entry : ∀ v1_s < 2 ^ s, FitsSignedWord (4 * p') (read2D syn_stage v1_s k2) := by
    intro v1_s hv1_s
    refine fitsSignedWord_of_norm_toScaledComplex_le pSub (p' + 1) (4 * p') (read2D syn_stage v1_s k2) ?_
      (by dsimp [pSub, p', pChild, pWork]; omega)
    dsimp only [syn_stage]
    rw [computableSyntheticFFTRadix2WithProgramCost_fst,
        ← array_getD_getD_eq_read2D_pair _ v1_s k2]
    have hnorm_stage := norm_toScaledComplex_computableSyntheticFFTRadix2_le pSub t1 r s (r / t1) hr
      P_mat ((2 : ℝ) ^ p')
      (fun j hj m hm => by
        rw [array_getD_getD_eq_read2D_pair, hP_eq j (hj.trans_le h2s_le_t1) m hm]
        exact (step_intermediate_word_width_bounds p K t1 r ht1 hr hsize x hx_norm
          j v1 m s (hj.trans_le h2s_le_t1) hm hs).2.1)
      v1_s k2 hv1_s hk2
    have hpow_le1 : (2 : ℝ) ^ (-(p' : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hlog_err : complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤ (0.01 : ℝ) := by
      have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
      dsimp only [pSub, p']
      nlinarith
    have hs_err : (s : ℝ) * complexQuantizeMaxErr pSub ≤ 1 := by
      have hs_real : (s : ℝ) ≤ (Nat.log2 t1 : ℝ) := by exact_mod_cast hs
      have hq_nonneg : 0 ≤ complexQuantizeMaxErr pSub := by unfold complexQuantizeMaxErr; positivity
      nlinarith
    have h1_le_p' : (1 : ℝ) ≤ (2 : ℝ) ^ p' := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    rw [pow_succ']
    linarith
  have hQ_eq : ∀ v1' < t1, ∀ k2' < r,
      toScaledComplex pSub (read2D Q_mat v1' k2') = stepSyntheticOut p K t1 r x v1' k2' := by
    intro v1' hv1' k2' hk2'
    dsimp only [Q_mat, runScan2DCostedWithSteps, costedGRescale, stepSyntheticOut, stepSyntheticStage, syn_out]
    rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1' hk2', toScaledComplex_gRescale_eq]
    apply congrArg (complexQuantize pSub)
    rw [computableSyntheticFFTRadix2WithProgramCost_fst,
        ← array_getD_getD_eq_read2D_pair _ v1' k2',
        toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1' k2' (ht1_pow.symm ▸ hv1') hk2']
    refine syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ _ (fun j hj m hm => ?_) v1' k2' hk2'
    rw [array_getD_getD_eq_read2D_pair]
    exact hP_eq j (ht1_pow ▸ hj) m hm
  have hQ_entry4 : FitsSignedWord (4 * p') (read2D Q_mat v1 k2) := by
    refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K (read2D Q_mat v1 k2) ?_
    rw [hQ_eq v1 hv1 k2 hk2]
    exact hbounds.2.2.2.1
  have hQ_entry6 : FitsSignedWord (6 * p') (read2D Q_mat v1 k2) :=
    fitsSignedWord_mono hQ_entry4 (by omega)
  have hqPost_eq : toScaledComplex pSub (read2D qPost_mat v1 k2) = stepPostTwist p K t1 r x v1 k2 := by
    dsimp only [qPost_mat, runScan2DCostedWithSteps, costedGMulScaled, stepPostTwist]
    rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
    have htw : toScaledComplex pSub (read1D postTwiddles k2) =
        complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) := by
      dsimp only [postTwiddles]
      rw [read1D_ofFn_of_lt r _ hk2]
      exact toScaledComplex_realQuantizeInt_pair pSub (zetaRoot r (-(k2 : ℝ)))
    rw [htw]
  have hqPost_entry : FitsSignedWord (4 * p') (read2D qPost_mat v1 k2) := by
    refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K (read2D qPost_mat v1 k2) ?_
    rw [hqPost_eq]
    exact hbounds.2.2.2.2.1
  exact ⟨hU_entry, hP_entry, hsyn_stage_entry, hQ_entry4, hQ_entry6, hqPost_entry⟩

/-- **Call-Site Width Soundness 3 — Nyquist Alternating Sum (`programCost_nyquist_altSum_widths_sound`, `[MS]` §3.2)**:
The computable Nyquist alternating sum `(computableNyquistAltSumContiguousWithProgramCost p_in (2 * pChild p K) (pChild p K) r xRow).1`
fits in `4 * pChild p K` signed bits (`FitsSignedWord (4 * pChild p K)`). -/
theorem programCost_nyquist_altSum_widths_sound
    (p_in p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (x : ℕ → ℂ) (hx_norm : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (xRow : Array (ℤ × ℤ))
    (hxRow : ∀ i < r, x (t1 / 2 + t1 * i) = toScaledComplex p_in (read1D xRow i)) :
    let p' := pChild p K
    let pSub := 2 * p'
    FitsSignedWord (4 * p')
      (computableNyquistAltSumContiguousWithProgramCost p_in pSub p' r xRow).1 := by
  dsimp only
  refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
  rw [computableNyquistAltSumContiguousWithProgramCost_fst,
      toScaledComplex_computableNyquistAltSumContiguous_eq p_in (2 * pChild p K) t1 r hr xRow x hxRow]
  have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
  have hsum_le : ‖nyquistAltSum t1 r x‖ ≤ (2 : ℝ) ^ p := by
    unfold nyquistAltSum
    have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
    have hinner : ‖∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖ ≤ (r : ℝ) * (2 : ℝ) ^ p := by
      calc ‖∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖
          ≤ ∑ j2 ∈ Finset.range r, ‖(-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖ := norm_sum_le _ _
        _ ≤ ∑ _j2 ∈ Finset.range r, (2 : ℝ) ^ p := by
            refine Finset.sum_le_sum fun j2 hj2_mem => ?_
            have hj2 : j2 < r := Finset.mem_range.mp hj2_mem
            rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
            have hidx_lt : t1 / 2 + t1 * j2 < t1 * r := by
              have hj2_le : j2 + 1 ≤ r := hj2
              calc t1 / 2 + t1 * j2 < t1 + t1 * j2 := Nat.add_lt_add_right hhalf_lt _
                _ = t1 * (j2 + 1) := by ring
                _ ≤ t1 * r := Nat.mul_le_mul_left t1 hj2_le
            exact hx_norm _ hidx_lt
        _ = (r : ℝ) * (2 : ℝ) ^ p := by simp
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_natCast]
    calc 1 / (r : ℝ) * ‖∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖
        ≤ 1 / (r : ℝ) * ((r : ℝ) * (2 : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (2 : ℝ) ^ p := by field_simp
  have hq := norm_complexQuantize_le (2 * pChild p K) (nyquistAltSum t1 r x)
  have hq_le1 : complexQuantizeMaxErr (2 * pChild p K) ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt (2 * pChild p K)
    have hp_le1 : (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    nlinarith
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hM_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hr_le : r ≤ 2 ^ K := by
    rw [← hsize]
    exact Nat.le_mul_of_pos_left r ht1
  have hr1_nat : r + 1 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : r + 1 ≤ 2 ^ (K + 1) := by rw [pow_succ]; omega
    exact h2.trans (Nat.pow_le_pow_right zero_lt_two (by omega))
  have hr1_real : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast hr1_nat
  have hr_pos_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  calc ‖complexQuantize (2 * pChild p K) (nyquistAltSum t1 r x)‖
      ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by nlinarith
    _ ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p := mul_le_mul_of_nonneg_right hr1_real hM_nonneg
    _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
    _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]

/-- **Call-Site Width Soundness 4 — Forward, Nyquist, and Backward Solvers
(`programCost_solvers_widths_sound`, `[MS]` §3.2)**:
Stated directly over the computable recurrence arrays `buildComputableZPartFwdWithProgramCost`,
`buildComputableZHomFwdWithProgramCost`, `buildComputableZPartNyqWithProgramCost` and the computable solver output
arrays `computableSolveBidiagonalFwdWithProgramCost`, `computableSolveNyquistWithProgramCost`, and
`computableSolveBidiagonalBwdWithProgramCost`: every recurrence state and every solver output fits in
`4 * pChild p K` signed bits (`FitsSignedWord (4 * pChild p K)`), and hence also in the `10 * p'` and
`22 * p'` temporary widths passed to `costedGCombineQuantize` and `costedGRatioQuantize`. -/
theorem programCost_solvers_widths_sound
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (c0 c1 c0_bwd c1_bwd alt_q : ℤ × ℤ) (Y_col : Array (ℤ × ℤ))
    (hc0_ge : (0.4999 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c0‖)
    (hc0_le1 : ‖toScaledComplex (2 * pChild p K) c0‖ ≤ 1)
    (hc10 : ‖toScaledComplex (2 * pChild p K) c1‖ ≤ ‖toScaledComplex (2 * pChild p K) c0‖)
    (hDq_fwd : (0.4 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c0 +
      toScaledComplex (2 * pChild p K) c1 *
        zHomFwdQuantized (2 * pChild p K) (toScaledComplex (2 * pChild p K) c0)
          (toScaledComplex (2 * pChild p K) c1) (t1 - 1)‖)
    (hc1_bwd_ge : (0.4999 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c1_bwd‖)
    (hc1_bwd_le1 : ‖toScaledComplex (2 * pChild p K) c1_bwd‖ ≤ 1)
    (hc01_bwd : ‖toScaledComplex (2 * pChild p K) c0_bwd‖ ≤ ‖toScaledComplex (2 * pChild p K) c1_bwd‖)
    (hDq_bwd : (0.4 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c1_bwd +
      toScaledComplex (2 * pChild p K) c0_bwd *
        zHomBwdQuantized (2 * pChild p K) (toScaledComplex (2 * pChild p K) c0_bwd)
          (toScaledComplex (2 * pChild p K) c1_bwd) (t1 - 1)‖)
    (hY : ∀ k < t1, ‖toScaledComplex (2 * pChild p K) (read1D Y_col k)‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (halt_q : ‖toScaledComplex (2 * pChild p K) alt_q‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (n u1 : ℕ) (hn : n < t1) (hu1_le_n : u1 ≤ n) :
    let p' := pChild p K
    let pSub := 2 * p'
    FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c0 c1 Y_col n).1 u1) ∧
    FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c0 c1 n).1 u1) ∧
    FitsSignedWord (4 * p') (read1D (buildComputableZPartNyqWithProgramCost pSub (10 * p') c0 Y_col n).1 u1) ∧
    FitsSignedWord (4 * p') (read1D (computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1 Y_col).1 u1) ∧
    FitsSignedWord (4 * p') (read1D (computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q).1 u1) ∧
    FitsSignedWord (4 * p') (read1D (computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0_bwd c1_bwd Y_col).1 u1) := by
  dsimp only
  have hu1 : u1 < t1 := hu1_le_n.trans_lt hn
  have hrec := solver_recurrence_word_width_bounds p K t1 r ht1 hr hsize
    (toScaledComplex (2 * pChild p K) c0) (toScaledComplex (2 * pChild p K) c1)
    hc0_ge hc10 (fun k => toScaledComplex (2 * pChild p K) (read1D Y_col k)) hY u1 hu1
  have hout := solver_outputs_word_width_bounds p K t1 r ht1 hr hsize
    (toScaledComplex (2 * pChild p K) c0) (toScaledComplex (2 * pChild p K) c1)
    hc0_ge hc0_le1 hc10 hDq_fwd
    (fun k => toScaledComplex (2 * pChild p K) (read1D Y_col k)) hY
    (toScaledComplex (2 * pChild p K) alt_q) halt_q u1 hu1
  have hbwd := solveBidiagonalBwdQuantized_word_width_bounds p K t1 r ht1 hr hsize
    (toScaledComplex (2 * pChild p K) c0_bwd) (toScaledComplex (2 * pChild p K) c1_bwd)
    hc1_bwd_ge hc1_bwd_le1 hc01_bwd hDq_bwd
    (fun k => toScaledComplex (2 * pChild p K) (read1D Y_col k)) hY u1 hu1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
    rw [buildComputableZPartFwdWithProgramCost_fst,
        toScaledComplex_read1D_buildComputableZPartFwdExact_eq _ _ _ _ n u1 hu1_le_n]
    exact hrec.2.1
  · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
    rw [buildComputableZHomFwdWithProgramCost_fst,
        toScaledComplex_read1D_buildComputableZHomFwdExact_eq _ _ _ n u1 hu1_le_n]
    exact hrec.1
  · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
    rw [buildComputableZPartNyqWithProgramCost_fst,
        toScaledComplex_read1D_buildComputableZPartNyqExact_eq _ _ _ n u1 hu1_le_n]
    exact hrec.2.2.1
  · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
    rw [computableSolveBidiagonalFwdWithProgramCost_fst,
        toScaledComplex_computableSolveBidiagonalFwdExact_eq _ t1 _ _ _ u1 hu1]
    exact hout.2.1
  · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
    rw [computableSolveNyquistWithProgramCost_fst,
        toScaledComplex_computableSolveNyquistExact_eq _ t1 _ _ _ u1 hu1]
    exact hout.2.2.2.1
  · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
    rw [computableSolveBidiagonalBwdWithProgramCost_fst,
        toScaledComplex_computableSolveBidiagonalBwdExact_eq _ t1 _ _ _ u1 hu1]
    exact hbwd.1

/-- **Call-Site Width Soundness 5 — Leaf `BaseRadix2FFT`
(`programCost_leaf_baseRadix2FFT_widths_sound`, `[MS]` §3.2)**:
At any leaf `(p, K)` with `8 ≤ p`, `q_leaf = 2 * p + K + 8`, and `∀ k < 2 ^ K, ‖x k‖ ≤ (2 : ℝ) ^ p`,
every intermediate butterfly stage `s ≤ K` of `computableBaseRadix2FFTCoreWithProgramCost` and every
leaf output of `computableBaseRadix2FFTWithProgramCost` fits in `4 * q_leaf` signed bits
(`FitsSignedWord (4 * q_leaf)`), matching the width `4 * q_leaf` passed to `costedGMulScaled`,
`costedButterflyAvg`, and `costedGRescale`. -/
theorem programCost_leaf_baseRadix2FFT_widths_sound
    (p_in p K : ℕ) (hp : 8 ≤ p)
    (twiddles : Array (Array (ℤ × ℤ)))
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      read1D (twiddles.getD s #[]) u =
        (realQuantizeInt (2 * p + K + 8) (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).re,
         realQuantizeInt (2 * p + K + 8) (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).im))
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < 2 ^ K, x k = toScaledComplex p_in (read1D xArr k))
    (hx_norm : ∀ k < 2 ^ K, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (s u : ℕ) (hs : s ≤ K) (hu_s : u < 2 ^ s) :
    let q_leaf := 2 * p + K + 8
    FitsSignedWord (4 * q_leaf)
      (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).1 u) ∧
    FitsSignedWord (4 * q_leaf)
      (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u) := by
  dsimp only
  set q_leaf := 2 * p + K + 8
  have h2s_le_2K : 2 ^ s ≤ 2 ^ K := Nat.pow_le_pow_right zero_lt_two hs
  have hu_K : u < 2 ^ K := hu_s.trans_le h2s_le_2K
  have hx_s : ∀ k < 2 ^ s, x k = toScaledComplex p_in (read1D xArr k) :=
    fun k hk => hx k (hk.trans_le h2s_le_2K)
  have hx_norm_s : ∀ k < 2 ^ s, ‖x k‖ ≤ (2 : ℝ) ^ p :=
    fun k hk => hx_norm k (hk.trans_le h2s_le_2K)
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hpow_neg_le1 : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hfactor_K : ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf ≤ 1 := by
    have h1 := baseRadix2FFTQuantized_core_err_factor_le p K
    dsimp [q_leaf]
    nlinarith
  have hfactor_s : ((s + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf ≤ 1 := by
    have hs_le_K : ((s + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hs 1
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr q_leaf := by unfold complexQuantizeMaxErr; positivity
    nlinarith
  have hcore_norm : ‖baseRadix2FFTQuantizedCore q_leaf s x u‖ ≤ (2 : ℝ) ^ (p + 1) := by
    have herr := norm_baseRadix2FFTQuantizedCore_sub_exact_le q_leaf s hfactor_s x ((2 : ℝ) ^ p) hM1 hx_norm_s u
    have hexact : ‖baseRadix2FFTExact s x u‖ ≤ (2 : ℝ) ^ p := by
      rw [baseRadix2FFTExact_eq_dft1D]
      exact dft1D_norm_le (2 ^ s) (pow_pos zero_lt_two s) x ((2 : ℝ) ^ p)
        (fun k hk => hx_norm_s k (Finset.mem_range.mp hk)) u
    have htri := norm_add_le (baseRadix2FFTQuantizedCore q_leaf s x u - baseRadix2FFTExact s x u)
      (baseRadix2FFTExact s x u)
    rw [sub_add_cancel] at htri
    rw [pow_succ']
    nlinarith
  have hcore_fit :
      FitsSignedWord (4 * q_leaf)
        (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le q_leaf (p + 1) (4 * q_leaf) _ ?_ (by dsimp [q_leaf]; omega)
    rw [toScaledComplex_computableBaseRadix2FFTCoreWithProgramCost_eq p_in q_leaf K twiddles htw s hs xArr x hx_s u hu_s]
    exact hcore_norm
  have hout_norm : ‖baseRadix2FFTQuantized p K x u‖ ≤ (2 : ℝ) ^ (p + 1) := by
    have herr := norm_baseRadix2FFTQuantized_sub_dft1D_le p K x ((2 : ℝ) ^ p) hM1 hx_norm u
    have hexact : ‖dft1D (2 ^ K) x u‖ ≤ (2 : ℝ) ^ p :=
      dft1D_norm_le (2 ^ K) (pow_pos zero_lt_two K) x ((2 : ℝ) ^ p)
        (fun k hk => hx_norm k (Finset.mem_range.mp hk)) u
    have htri := norm_add_le (baseRadix2FFTQuantized p K x u - dft1D (2 ^ K) x u) (dft1D (2 ^ K) x u)
    rw [sub_add_cancel] at htri
    rw [pow_succ']
    nlinarith
  have hout_fit :
      FitsSignedWord (4 * q_leaf)
        (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le p (p + 1) (4 * q_leaf) _ ?_ (by dsimp [q_leaf]; omega)
    rw [toScaledComplex_computableBaseRadix2FFTWithProgramCost_eq p_in p K twiddles htw xArr x hx u hu_K]
    exact hout_norm
  exact ⟨hcore_fit, hout_fit⟩

/-- **Call-Site Width Soundness 6 — Root Pipeline (`programCost_root_pipeline_widths_sound`, `[MS]` §3.2)**:
In `computablePaperFastDFTMultiplyWithProgramCost (idealRoundedPaperTables spec) b K0 k1 k2 A B`,
every packed input `read1D stPack.outTape u`, every forward transform output `read1D fwd.1 u`, and every
squared-and-conjugated frequency entry `read1D stSq.1 u` (`u < 2 ^ K0`) satisfies `FitsSignedWord (4 * p0)`,
matching the width `4 * p0` passed to `costedGMulScaled (p0 + 2) (4 * p0)` in `stSq`. -/
theorem programCost_root_pipeline_widths_sound
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (u : ℕ) (hu : u < 2 ^ K0) :
    let R0 := 2 ^ K0
    let p0 := rootPrecision b K0
    let cSpec := idealRoundedPaperTables spec
    let asArr := (splitChunksTreeWithProgramCost b k1 A).1.toArray
    let bsArr := (splitChunksTreeWithProgramCost b k2 B).1.toArray
    let stPack := runSequentialScanSteps (fun j =>
      (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
    let fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
    let stSq := runSequentialScanCostedSteps (fun u' =>
      let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u') (read1D fwd.1 u')
      (gConj m.1, m.2 + addBitCost (8 * p0))) R0
    FitsSignedWord (4 * p0) (read1D stPack.outTape u) ∧
    FitsSignedWord (4 * p0) (read1D fwd.1 u) ∧
    FitsSignedWord (4 * p0) (read1D stSq.1 u) := by
  dsimp only
  rw [splitChunksTreeWithProgramCost_fst, splitChunksTreeWithProgramCost_fst]
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set cSpec := idealRoundedPaperTables spec
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
  set stSq := runSequentialScanCostedSteps (fun u' =>
    let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u') (read1D fwd.1 u')
    (gConj m.1, m.2 + addBitCost (8 * p0))) R0
  have hp0_ge6 : 6 ≤ p0 := by dsimp [p0, rootPrecision]; omega
  have hb_le_p0 : b ≤ p0 := by dsimp [p0, rootPrecision]; omega
  have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_le2 : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpack_eq : toScaledComplex b (read1D stPack.outTape u) = x_AB u :=
    toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B u hu
  have hpack_fit : FitsSignedWord (4 * p0) (read1D stPack.outTape u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le b 1 (4 * p0) _ ?_ (by omega)
    rw [hpack_eq, pow_one]
    exact (norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B u).trans hsqrt2_le2
  have hy : ∀ u' < R0, toScaledComplex p0 (read1D fwd.1 u') = sincGaussianFastDFTRadix2Leaf spec x_AB u' := by
    intro u' hu'
    rw [← hp0]
    exact toScaledComplex_computablePaperFastDFT_eq spec hvalid hexec b stPack.outTape x_AB
      (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
      u' (hsize.symm ▸ hu')
  have hu_spec : u < spec.size := hsize.symm ▸ hu
  have herr := sincGaussianFastDFTRadix2Leaf_error_le spec hvalid hexec.toBasePow2 x_AB (Real.sqrt 2) hsqrt2_ge1
    (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u hu_spec
  have hpow_neg_le1 : (2 : ℝ) ^ (-(spec.p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have herr_le2 : ‖sincGaussianFastDFTRadix2Leaf spec x_AB u - dft1D spec.size x_AB u‖ ≤ 2 := by
    nlinarith
  have hdft_le : ‖dft1D spec.size x_AB u‖ ≤ 2 := by
    have hpos : 0 < spec.size := by rw [hsize]; exact pow_pos zero_lt_two K0
    have h1 := dft1D_norm_le spec.size hpos x_AB (Real.sqrt 2)
      (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u
    linarith
  have hnorm_le4 : ‖sincGaussianFastDFTRadix2Leaf spec x_AB u‖ ≤ 4 := by
    have htri := norm_add_le (sincGaussianFastDFTRadix2Leaf spec x_AB u - dft1D spec.size x_AB u)
      (dft1D spec.size x_AB u)
    rw [sub_add_cancel] at htri
    linarith
  have hfwd_fit : FitsSignedWord (4 * p0) (read1D fwd.1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le p0 2 (4 * p0) _ ?_ (by omega)
    rw [hy u hu]
    calc ‖sincGaussianFastDFTRadix2Leaf spec x_AB u‖ ≤ 4 := hnorm_le4
      _ = (2 : ℝ) ^ 2 := by norm_num
  have hsq_le16 : ‖(sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2‖ ≤ 16 := by
    rw [norm_pow]
    nlinarith [norm_nonneg (sincGaussianFastDFTRadix2Leaf spec x_AB u)]
  have hq_err : complexQuantizeMaxErr p0 ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt p0
    have hpow_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    nlinarith
  have hS_le17 : ‖complexQuantize p0 ((sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2)‖ ≤ 17 := by
    have h1 := norm_complexQuantize_le p0 ((sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2)
    linarith
  have hsq_fit : FitsSignedWord (4 * p0) (read1D stSq.1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le p0 5 (4 * p0) _ ?_ (by omega)
    dsimp only [stSq, runSequentialScanCostedSteps, costedGMulScaled]
    rw [read1D_runSequentialScanSteps_eq _ R0 u hu, toScaledComplex_gConj,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu, ← sq, norm_star]
    calc ‖complexQuantize p0 ((sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2)‖ ≤ 17 := hS_le17
      _ ≤ (32 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ 5 := by norm_num
  exact ⟨hpack_fit, hfwd_fit, hsq_fit⟩

/-- **Master Computable-Array Operand Width Soundness Bundle (`programCost_widths_sound`, `[MS]` §3.2)**:
Bundles the value-level `FitsSignedWord` operand width soundness theorems across all 6 priced passes
of `computablePaperFastDFTWithProgramCost` and `computablePaperFastDFTMultiplyWithProgramCost`:
1. `programCost_spread_widths_sound` (`6 * p'` for `computableSpreadRowContiguousWithProgramCost`),
2. `programCost_twist_and_syntheticFFT_widths_sound` (`6 * p'` and `4 * p'` for `U_mat`, `P_mat`,
   every stage `s ≤ Nat.log2 t1` of `computableSyntheticFFTRadix2WithProgramCost`, `Q_mat`, `qPost_mat`),
3. `programCost_nyquist_altSum_widths_sound` (`4 * p'` for `computableNyquistAltSumContiguousWithProgramCost`),
4. `programCost_solvers_widths_sound` (`4 * p'` for all recurrence arrays `buildComputableZPartFwdWithProgramCost`,
   `buildComputableZHomFwdWithProgramCost`, `buildComputableZPartNyqWithProgramCost` and solver outputs
   `computableSolveBidiagonalFwdWithProgramCost`, `computableSolveNyquistWithProgramCost`,
   `computableSolveBidiagonalBwdWithProgramCost`),
5. `programCost_leaf_baseRadix2FFT_widths_sound` (`4 * q_leaf` for `computableBaseRadix2FFTCoreWithProgramCost`
   and `computableBaseRadix2FFTWithProgramCost`), and
6. `programCost_root_pipeline_widths_sound` (`4 * p0` for `stPack`, `fwd`, and `stSq`). -/
theorem programCost_widths_sound :
    (∀ (p_in p K t1 r : ℕ), 0 < t1 → 0 < r → t1 * r = 2 ^ K →
      ∀ (x : ℕ → ℂ), (∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p) →
      ∀ (j1 k2 : ℕ), j1 < t1 → k2 < r →
      ∀ (xRow : Array (ℤ × ℤ)),
        (∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) →
        FitsSignedWord (6 * pChild p K)
          (read1D (computableSpreadRowContiguousWithProgramCost p_in (2 * pChild p K) (pChild p K)
            (2 * pChild p K) r (kroneckerSpreadFilterTapsFolded (alphaSchedule (pWork p K))
              (2 * pChild p K) (2 * pChild p K) t1 r j1) xRow).1 k2)) ∧
    (∀ (p_in p K t1 r c1 : ℕ), 0 < t1 → 0 < r → t1 * r = 2 ^ K → c1 * t1 = r →
      ∀ (x : ℕ → ℂ), (∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p) →
      ∀ (xRows : Array (Array (ℤ × ℤ))),
        (∀ j1 < t1, ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i)) →
      ∀ (j1 v1 k2 s : ℕ), j1 < t1 → v1 < t1 → k2 < r → s ≤ Nat.log2 t1 →
        let p' := pChild p K
        let pSub := 2 * p'
        let α := alphaSchedule (pWork p K)
        let filterTaps : Array (List ℤ) :=
          Array.ofFn (fun j1' : Fin t1 => kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1'.val)
        let preTwiddles : Array (ℤ × ℤ) :=
          Array.ofFn (fun k2' : Fin r =>
            (realQuantizeInt pSub (zetaRoot r (k2'.val : ℝ)).re,
             realQuantizeInt pSub (zetaRoot r (k2'.val : ℝ)).im))
        let postTwiddles : Array (ℤ × ℤ) :=
          Array.ofFn (fun k2' : Fin r =>
            (realQuantizeInt pSub (zetaRoot r (-(k2'.val : ℝ))).re,
             realQuantizeInt pSub (zetaRoot r (-(k2'.val : ℝ))).im))
        let U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
          Array.ofFn (fun j1' : Fin t1 =>
            computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
              (filterTaps.getD j1'.val []) (xRows.getD j1'.val #[]))
        let U_mat : Array (Array (ℤ × ℤ)) :=
          Array.ofFn (fun j1' : Fin t1 => if h : j1'.val < U_rows.size then U_rows[j1'.val].1 else #[])
        let P_mat : Array (Array (ℤ × ℤ)) :=
          (runScan2DCostedWithSteps t1 r (fun j1' k2' =>
            costedGPreTwistU pSub (6 * p') (read1D preTwiddles k2') (read2D U_mat j1' k2'))).1
        let syn_stage : Array (Array (ℤ × ℤ)) :=
          (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1
        let syn_out : Array (Array (ℤ × ℤ)) :=
          (computableSyntheticFFTRadix2WithProgramCost p' t1 r (Nat.log2 t1) (r / t1) P_mat).1
        let Q_mat : Array (Array (ℤ × ℤ)) :=
          (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
            costedGRescale pSub pSub (4 * p') (read2D syn_out v1' k2'))).1
        let qPost_mat : Array (Array (ℤ × ℤ)) :=
          (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
            costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2') (read2D Q_mat v1' k2'))).1
        FitsSignedWord (6 * p') (read2D U_mat j1 k2) ∧
        FitsSignedWord (4 * p') (read2D P_mat j1 k2) ∧
        (∀ v1_s < 2 ^ s, FitsSignedWord (4 * p') (read2D syn_stage v1_s k2)) ∧
        FitsSignedWord (4 * p') (read2D Q_mat v1 k2) ∧
        FitsSignedWord (6 * p') (read2D Q_mat v1 k2) ∧
        FitsSignedWord (4 * p') (read2D qPost_mat v1 k2)) ∧
    (∀ (p_in p K t1 r : ℕ), 0 < t1 → 0 < r → t1 * r = 2 ^ K →
      ∀ (x : ℕ → ℂ), (∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p) →
      ∀ (xRow : Array (ℤ × ℤ)),
        (∀ i < r, x (t1 / 2 + t1 * i) = toScaledComplex p_in (read1D xRow i)) →
        FitsSignedWord (4 * pChild p K)
          (computableNyquistAltSumContiguousWithProgramCost p_in (2 * pChild p K) (pChild p K) r xRow).1) ∧
    (∀ (p K t1 r : ℕ), 0 < t1 → 0 < r → t1 * r = 2 ^ K →
      ∀ (c0 c1 c0_bwd c1_bwd alt_q : ℤ × ℤ) (Y_col : Array (ℤ × ℤ)),
        (0.4999 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c0‖ →
        ‖toScaledComplex (2 * pChild p K) c0‖ ≤ 1 →
        ‖toScaledComplex (2 * pChild p K) c1‖ ≤ ‖toScaledComplex (2 * pChild p K) c0‖ →
        (0.4 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c0 +
          toScaledComplex (2 * pChild p K) c1 *
            zHomFwdQuantized (2 * pChild p K) (toScaledComplex (2 * pChild p K) c0)
              (toScaledComplex (2 * pChild p K) c1) (t1 - 1)‖ →
        (0.4999 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c1_bwd‖ →
        ‖toScaledComplex (2 * pChild p K) c1_bwd‖ ≤ 1 →
        ‖toScaledComplex (2 * pChild p K) c0_bwd‖ ≤ ‖toScaledComplex (2 * pChild p K) c1_bwd‖ →
        (0.4 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) c1_bwd +
          toScaledComplex (2 * pChild p K) c0_bwd *
            zHomBwdQuantized (2 * pChild p K) (toScaledComplex (2 * pChild p K) c0_bwd)
              (toScaledComplex (2 * pChild p K) c1_bwd) (t1 - 1)‖ →
        (∀ k < t1, ‖toScaledComplex (2 * pChild p K) (read1D Y_col k)‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p) →
        ‖toScaledComplex (2 * pChild p K) alt_q‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p →
      ∀ (n u1 : ℕ), n < t1 → u1 ≤ n →
        let p' := pChild p K
        let pSub := 2 * p'
        FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c0 c1 Y_col n).1 u1) ∧
        FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c0 c1 n).1 u1) ∧
        FitsSignedWord (4 * p') (read1D (buildComputableZPartNyqWithProgramCost pSub (10 * p') c0 Y_col n).1 u1) ∧
        FitsSignedWord (4 * p') (read1D (computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1 Y_col).1 u1) ∧
        FitsSignedWord (4 * p') (read1D (computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q).1 u1) ∧
        FitsSignedWord (4 * p') (read1D (computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0_bwd c1_bwd Y_col).1 u1)) ∧
    (∀ (p_in p K : ℕ), 8 ≤ p →
      ∀ (twiddles : Array (Array (ℤ × ℤ))),
        (∀ s < K, ∀ u < 2 ^ (s + 1),
          read1D (twiddles.getD s #[]) u =
            (realQuantizeInt (2 * p + K + 8) (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).re,
             realQuantizeInt (2 * p + K + 8) (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).im)) →
      ∀ (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ),
        (∀ k < 2 ^ K, x k = toScaledComplex p_in (read1D xArr k)) →
        (∀ k < 2 ^ K, ‖x k‖ ≤ (2 : ℝ) ^ p) →
      ∀ (s u : ℕ), s ≤ K → u < 2 ^ s →
        FitsSignedWord (4 * (2 * p + K + 8))
          (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in (2 * p + K + 8) twiddles s xArr).1 u) ∧
        FitsSignedWord (4 * (2 * p + K + 8))
          (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u)) ∧
    (∀ (spec : QuantizedFastDFTSpec), spec.Valid → spec.PaperExecutableValid →
      ∀ (b K0 k1 k2 A B u : ℕ),
        spec.size = 2 ^ K0 → spec.p = rootPrecision b K0 → u < 2 ^ K0 →
        let R0 := 2 ^ K0
        let p0 := rootPrecision b K0
        let cSpec := idealRoundedPaperTables spec
        let asArr := (splitChunksTreeWithProgramCost b k1 A).1.toArray
        let bsArr := (splitChunksTreeWithProgramCost b k2 B).1.toArray
        let stPack := runSequentialScanSteps (fun j =>
          (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
        let fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
        let stSq := runSequentialScanCostedSteps (fun u' =>
          let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u') (read1D fwd.1 u')
          (gConj m.1, m.2 + addBitCost (8 * p0))) R0
        FitsSignedWord (4 * p0) (read1D stPack.outTape u) ∧
        FitsSignedWord (4 * p0) (read1D fwd.1 u) ∧
        FitsSignedWord (4 * p0) (read1D stSq.1 u)) :=
  ⟨fun p_in p K t1 r ht1 hr hsize x hx j1 k2 hj1 hk2 xRow hxRow =>
     programCost_spread_widths_sound p_in p K t1 r ht1 hr hsize x hx j1 k2 hj1 hk2 xRow hxRow,
   fun p_in p K t1 r c1 ht1 hr hsize hc1 x hx xRows hxRows j1 v1 k2 s hj1 hv1 hk2 hs =>
     programCost_twist_and_syntheticFFT_widths_sound p_in p K t1 r c1 ht1 hr hsize hc1 x hx xRows hxRows j1 v1 k2 s hj1 hv1 hk2 hs,
   fun p_in p K t1 r ht1 hr hsize x hx xRow hxRow =>
     programCost_nyquist_altSum_widths_sound p_in p K t1 r ht1 hr hsize x hx xRow hxRow,
   fun p K t1 r ht1 hr hsize c0 c1 c0_bwd c1_bwd alt_q Y_col hc0_ge hc0_le1 hc10 hDq_fwd
       hc1_bwd_ge hc1_bwd_le1 hc01_bwd hDq_bwd hY halt_q n u1 hn hu1_le =>
     programCost_solvers_widths_sound p K t1 r ht1 hr hsize c0 c1 c0_bwd c1_bwd alt_q Y_col
       hc0_ge hc0_le1 hc10 hDq_fwd hc1_bwd_ge hc1_bwd_le1 hc01_bwd hDq_bwd hY halt_q n u1 hn hu1_le,
   fun p_in p K hp twiddles htw xArr x hx hx_norm s u hs hu =>
     programCost_leaf_baseRadix2FFT_widths_sound p_in p K hp twiddles htw xArr x hx hx_norm s u hs hu,
   fun spec hvalid hexec b K0 k1 k2 A B u hsize hp0 hu =>
     programCost_root_pipeline_widths_sound spec hvalid hexec b K0 k1 k2 A B hsize hp0 u hu⟩

/-! ### Part 3b: Width Soundness under `TablesFaithful` and Recursive-Tree Chaining (`AllCallSitesWidthSound`) -/

/-- General bridge lemma from raw spread pair norm `‖z‖ ≤ (2 : ℝ) ^ (pChild p K)` at scale
`2^(2 * pSub) = 2^(4 * pChild p K)` to `FitsSignedWord (6 * pChild p K)`. -/
theorem fitsSignedWord_six_mul_pChild_of_raw_spread_norm_le
    (p K : ℕ) (uRaw : ℤ × ℤ) (z : ℂ)
    (huRaw :
      (⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ (2 * pChild p K) * (2 : ℝ) ^ (2 * pChild p K)),
        (uRaw.2 : ℝ) / ((2 : ℝ) ^ (2 * pChild p K) * (2 : ℝ) ^ (2 * pChild p K))⟩ : ℂ) = z)
    (hnorm : ‖z‖ ≤ (2 : ℝ) ^ (pChild p K)) :
    FitsSignedWord (6 * pChild p K) uRaw := by
  set p' := pChild p K
  have hp'_ge12 : 12 ≤ p' := by
    dsimp [p']
    rw [pChild_eq_additive]
    omega
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

/-- **Faithful-Table Call-Site Width Soundness 1 — Spread (`programCost_spread_widths_sound_of_faithful`, `[MS]` §3.2)**:
For any folded tap list `gTapFold : List ℤ` satisfying the `TablesFaithful` T3 condition, every
output bucket entry of `computableSpreadRowContiguousWithProgramCost` satisfies
`FitsSignedWord (6 * pChild p K)`. -/
theorem programCost_spread_widths_sound_of_faithful
    (p_in p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (x : ℕ → ℂ) (hx_norm : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
          G s))
    (hG_err : ∀ s < 2 * (2 * pChild p K) + 1,
      |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
          sincGaussian (alphaSchedule (pWork p K))
            (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
        (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)))
    (xRow : Array (ℤ × ℤ))
    (hxRow : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) :
    let p' := pChild p K
    let pSub := 2 * p'
    FitsSignedWord (6 * p')
      (read1D (computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r gTapFold xRow).1 k2) := by
  dsimp only
  rw [computableSpreadRowContiguousWithProgramCost_fst]
  have huRaw := computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps
    p_in (2 * pChild p K) (2 * pChild p K) t1 r gTapFold xRow x j1 k2 hxRow hk2
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hU := norm_kroneckerSpreadOfFoldedTaps_le p K t1 r ht1 hr j1 k2 hj1 hk2
    gTapFold G hFold hG_err x ((2 : ℝ) ^ p) hM1 hx_norm
  have hr_le : r ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_left r ht1
  have hr1_nat : r + 1 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : r + 1 ≤ 2 ^ (K + 1) := by rw [pow_succ]; omega
    exact h2.trans (Nat.pow_le_pow_right zero_lt_two (by omega))
  have hr1_real : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast hr1_nat
  have hU_p' :
      ‖kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2‖ ≤
        (2 : ℝ) ^ (pChild p K) := by
    calc ‖kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2‖
        ≤ ((r : ℝ) + (0.5 : ℝ)) * (2 : ℝ) ^ p := hU
      _ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by nlinarith
      _ ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right hr1_real (by positivity)
      _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
      _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]
  exact fitsSignedWord_six_mul_pChild_of_raw_spread_norm_le p K _ _ huRaw hU_p'

/-- Stronger intermediate bound `‖qPost v1 k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p` under `TablesFaithful`,
used to bound the child DFT outputs `Y_mat` by `(2 * (r : ℝ) + 3) * (2 : ℝ) ^ p`. -/
theorem norm_qPost_of_faithful_le_r_add_one
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hPost : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    let pSub := 2 * pChild p K
    let U : ℕ → ℕ → ℂ := fun j1 m =>
      kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 m
    let P : ℕ → ℕ → ℂ := fun j1 m =>
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles m) * U j1 m)
    let Q : ℕ → ℕ → ℂ := fun v m =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
    let qPost : ℕ → ℕ → ℂ := fun v m =>
      complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles m) * Q v m)
    ‖qPost v1 k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by
  dsimp only
  set pSub := 2 * pChild p K
  set M : ℝ := (2 : ℝ) ^ p
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr_le : r ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_left r ht1
  let U : ℕ → ℕ → ℂ := fun j1 m =>
    kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 m
  let P : ℕ → ℕ → ℂ := fun j1 m =>
    complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles m) * U j1 m)
  let Q : ℕ → ℕ → ℂ := fun v m =>
    complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
  have hP : ∀ j1 < t1, ∀ m < r, ‖P j1 m‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M := by
    intro j1 hj1 m hm
    rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
    have hU := norm_kroneckerSpreadOfFoldedTaps_le p K t1 r ht1 hr j1 m hj1 hm
      (filterTaps.getD j1 []) G hFold hG_err x M hM1 hx
    have h := norm_complexQuantize_approx_zetaRoot_mul_le p K r hr_le (m : ℝ)
      (toScaledComplex pSub (read1D preTwiddles m)) (U j1 m) (0.5 : ℝ) M
      (by norm_num) hM1 (hPre m hm) hU
    dsimp only at h
    linarith
  have hQ : ‖Q v1 k2‖ ≤ ((r : ℝ) + (0.53 : ℝ)) * M := by
    obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    set w := syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2
    have hsyn : ‖w‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M + (Nat.log2 t1 : ℝ) * complexQuantizeMaxErr pSub :=
      norm_syntheticFFTRadix2Quantized_le pSub r (Nat.log2 t1) (r / t1) hr P
        (((r : ℝ) + (0.52 : ℝ)) * M) (fun j1 hj1 m hm => hP j1 (ht1_pow ▸ hj1) m hm) v1 k2 hk2
    have hquant := norm_complexQuantize_le pSub w
    have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hlog_err : complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤ (0.01 : ℝ) := by
      have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
      nlinarith
    dsimp only [Q]
    nlinarith
  have h := norm_complexQuantize_approx_zetaRoot_mul_le p K r hr_le (-(k2 : ℝ))
    (toScaledComplex pSub (read1D postTwiddles k2)) (Q v1 k2) (0.53 : ℝ) M
    (by norm_num) hM1 (hPost k2 hk2) hQ
  dsimp only at h
  linarith

/-- Norm bounds `‖P j1 m‖ ≤ (2 : ℝ) ^ (pChild p K)` and `‖Q v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K)`
under `TablesFaithful`. -/
theorem norm_P_and_Q_of_faithful_le_two_pow_pChild
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (filterTaps : Array (List ℤ))
    (preTwiddles : Array (ℤ × ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    let pSub := 2 * pChild p K
    let U : ℕ → ℕ → ℂ := fun j1 m =>
      kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 m
    let P : ℕ → ℕ → ℂ := fun j1 m =>
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles m) * U j1 m)
    let Q : ℕ → ℕ → ℂ := fun v m =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
    (∀ j1 < t1, ∀ m < r, ‖P j1 m‖ ≤ (2 : ℝ) ^ (pChild p K)) ∧
    ‖Q v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) := by
  dsimp only
  set pSub := 2 * pChild p K
  set M : ℝ := (2 : ℝ) ^ p
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr_le : r ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_left r ht1
  have hr1_nat : r + 1 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : r + 1 ≤ 2 ^ (K + 1) := by rw [pow_succ]; omega
    exact h2.trans (Nat.pow_le_pow_right zero_lt_two (by omega))
  have hr1_real : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast hr1_nat
  have hr1_mul_le_p' : ((r : ℝ) + 1) * M ≤ (2 : ℝ) ^ (pChild p K) := by
    calc ((r : ℝ) + 1) * M
        ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p := mul_le_mul_of_nonneg_right hr1_real (by positivity)
      _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
      _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]
  let U : ℕ → ℕ → ℂ := fun j1 m =>
    kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 m
  let P : ℕ → ℕ → ℂ := fun j1 m =>
    complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles m) * U j1 m)
  let Q : ℕ → ℕ → ℂ := fun v m =>
    complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
  have hP : ∀ j1 < t1, ∀ m < r, ‖P j1 m‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M := by
    intro j1 hj1 m hm
    rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
    have hU := norm_kroneckerSpreadOfFoldedTaps_le p K t1 r ht1 hr j1 m hj1 hm
      (filterTaps.getD j1 []) G hFold hG_err x M hM1 hx
    have h := norm_complexQuantize_approx_zetaRoot_mul_le p K r hr_le (m : ℝ)
      (toScaledComplex pSub (read1D preTwiddles m)) (U j1 m) (0.5 : ℝ) M
      (by norm_num) hM1 (hPre m hm) hU
    dsimp only at h
    linarith
  have hP_p' : ∀ j1 < t1, ∀ m < r, ‖P j1 m‖ ≤ (2 : ℝ) ^ (pChild p K) := by
    intro j1 hj1 m hm
    have h1 := hP j1 hj1 m hm
    nlinarith
  have hQ : ‖Q v1 k2‖ ≤ ((r : ℝ) + (0.53 : ℝ)) * M := by
    obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    set w := syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2
    have hsyn : ‖w‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M + (Nat.log2 t1 : ℝ) * complexQuantizeMaxErr pSub :=
      norm_syntheticFFTRadix2Quantized_le pSub r (Nat.log2 t1) (r / t1) hr P
        (((r : ℝ) + (0.52 : ℝ)) * M) (fun j1 hj1 m hm => hP j1 (ht1_pow ▸ hj1) m hm) v1 k2 hk2
    have hquant := norm_complexQuantize_le pSub w
    have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hlog_err : complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤ (0.01 : ℝ) := by
      have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
      nlinarith
    dsimp only [Q]
    nlinarith
  exact ⟨hP_p', by nlinarith⟩

/-- **Faithful-Table Call-Site Width Soundness 2 — Pre-Twist, Synthetic FFT Butterfly Stages,
Rescale, and Post-Twist (`programCost_twist_and_syntheticFFT_widths_sound_of_faithful`, `[MS]` §3.2)**:
For any `filterTaps`, `preTwiddles`, and `postTwiddles` satisfying the `TablesFaithful` conditions,
the intermediate matrices `U_mat`, `P_mat`, `computableSyntheticFFTRadix2WithProgramCost` at every
stage `s ≤ Nat.log2 t1`, `Q_mat`, and `qPost_mat` satisfy `FitsSignedWord`. -/
theorem programCost_twist_and_syntheticFFT_widths_sound_of_faithful
    (p_in p K t1 r c1 : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K) (hc1 : c1 * t1 = r)
    (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hPost : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (x : ℕ → ℂ) (hx_norm : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (xRows : Array (Array (ℤ × ℤ)))
    (hxRows : ∀ j1 < t1, ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i))
    (j1 v1 k2 s : ℕ) (hj1 : j1 < t1) (hv1 : v1 < t1) (hk2 : k2 < r) (hs : s ≤ Nat.log2 t1) :
    let p' := pChild p K
    let pSub := 2 * p'
    let U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun j1' : Fin t1 =>
        computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
          (filterTaps.getD j1'.val []) (xRows.getD j1'.val #[]))
    let U_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun j1' : Fin t1 => if h : j1'.val < U_rows.size then U_rows[j1'.val].1 else #[])
    let P_mat : Array (Array (ℤ × ℤ)) :=
      (runScan2DCostedWithSteps t1 r (fun j1' k2' =>
        costedGPreTwistU pSub (6 * p') (read1D preTwiddles k2') (read2D U_mat j1' k2'))).1
    let syn_stage : Array (Array (ℤ × ℤ)) :=
      (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1
    let syn_out : Array (Array (ℤ × ℤ)) :=
      (computableSyntheticFFTRadix2WithProgramCost p' t1 r (Nat.log2 t1) (r / t1) P_mat).1
    let Q_mat : Array (Array (ℤ × ℤ)) :=
      (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
        costedGRescale pSub pSub (4 * p') (read2D syn_out v1' k2'))).1
    let qPost_mat : Array (Array (ℤ × ℤ)) :=
      (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
        costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2') (read2D Q_mat v1' k2'))).1
    FitsSignedWord (6 * p') (read2D U_mat j1 k2) ∧
    FitsSignedWord (4 * p') (read2D P_mat j1 k2) ∧
    (∀ v1_s < 2 ^ s, FitsSignedWord (4 * p') (read2D syn_stage v1_s k2)) ∧
    FitsSignedWord (4 * p') (read2D Q_mat v1 k2) ∧
    FitsSignedWord (6 * p') (read2D Q_mat v1 k2) ∧
    FitsSignedWord (4 * p') (read2D qPost_mat v1 k2) := by
  dsimp only
  obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  have hPQ_bounds := norm_P_and_Q_of_faithful_le_two_pow_pChild p K t1 r ht1 hr hsize
    filterTaps preTwiddles hTaps hPre x hx_norm v1 k2 hk2
  set p' := pChild p K
  set pSub := 2 * p'
  have hpow_le1 : (2 : ℝ) ^ (-(p' : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hs_err : (s : ℝ) * complexQuantizeMaxErr pSub ≤ 1 := by
    have hlog_err : ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub ≤ (0.01 : ℝ) := by
      rw [mul_comm]
      exact (complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K).trans
        (mul_le_of_le_one_right (by norm_num) hpow_le1)
    have hs_real : (s : ℝ) ≤ (Nat.log2 t1 : ℝ) + 1 := by
      have : s ≤ Nat.log2 t1 + 1 := by omega
      exact_mod_cast this
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr pSub := by unfold complexQuantizeMaxErr; positivity
    have hmul := mul_le_mul_of_nonneg_right hs_real hq_nonneg
    linarith
  set U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
    Array.ofFn (fun j1' : Fin t1 =>
      computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
        (filterTaps.getD j1'.val []) (xRows.getD j1'.val #[]))
  set U_mat : Array (Array (ℤ × ℤ)) :=
    Array.ofFn (fun j1' : Fin t1 => if h : j1'.val < U_rows.size then U_rows[j1'.val].1 else #[])
  set P_mat : Array (Array (ℤ × ℤ)) :=
    (runScan2DCostedWithSteps t1 r (fun j1' k2' =>
      costedGPreTwistU pSub (6 * p') (read1D preTwiddles k2') (read2D U_mat j1' k2'))).1
  set syn_stage : Array (Array (ℤ × ℤ)) :=
    (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1
  set syn_out : Array (Array (ℤ × ℤ)) :=
    (computableSyntheticFFTRadix2WithProgramCost p' t1 r (Nat.log2 t1) (r / t1) P_mat).1
  set Q_mat : Array (Array (ℤ × ℤ)) :=
    (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
      costedGRescale pSub pSub (4 * p') (read2D syn_out v1' k2'))).1
  set qPost_mat : Array (Array (ℤ × ℤ)) :=
    (runScan2DCostedWithSteps t1 r (fun v1' k2' =>
      costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2') (read2D Q_mat v1' k2'))).1
  set U : ℕ → ℕ → ℂ := fun j1' m =>
    kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1' []) x j1' m
  set P : ℕ → ℕ → ℂ := fun j1' m =>
    complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles m) * U j1' m)
  set Q : ℕ → ℕ → ℂ := fun v1' m =>
    complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1' m)
  set qPost : ℕ → ℕ → ℂ := fun v1' m =>
    complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles m) * Q v1' m)
  have hP_norm_p' : ∀ j1' < t1, ∀ m < r, ‖P j1' m‖ ≤ (2 : ℝ) ^ p' := hPQ_bounds.1
  have hQ_norm_p' : ‖Q v1 k2‖ ≤ (2 : ℝ) ^ p' := hPQ_bounds.2
  have hU_entry : FitsSignedWord (6 * p') (read2D U_mat j1 k2) := by
    dsimp only [U_mat, U_rows]
    rw [read2D_ofFn_of_lt t1 _ hj1 k2]
    simp only [Array.size_ofFn, hj1, ↓reduceDIte, Array.getElem_ofFn]
    rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
    exact programCost_spread_widths_sound_of_faithful p_in p K t1 r ht1 hr hsize x hx_norm j1 k2 hj1 hk2
      (filterTaps.getD j1 []) G hFold hG_err (xRows.getD j1 #[]) (hxRows j1 hj1)
  have hP_eq : ∀ j1' < t1, ∀ k2' < r,
      toScaledComplex pSub (read2D P_mat j1' k2') = P j1' k2' := by
    intro j1' hj1' k2' hk2'
    dsimp only [P_mat, runScan2DCostedWithSteps, costedGPreTwistU, P]
    rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1' hk2']
    have hU_row : read2D U_mat j1' k2' =
        read1D (computableSpreadRowContiguousWithCost p_in pSub pSub r
          (filterTaps.getD j1' []) (xRows.getD j1' #[])).1 k2' := by
      dsimp only [U_mat, U_rows]
      rw [read2D_ofFn_of_lt t1 _ hj1' k2']
      simp only [Array.size_ofFn, hj1', ↓reduceDIte, Array.getElem_ofFn,
        computableSpreadRowContiguousWithProgramCost_fst]
    rw [hU_row]
    exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2') _ (U j1' k2')
      (computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps
        p_in pSub pSub t1 r (filterTaps.getD j1' []) (xRows.getD j1' #[]) x j1' k2'
        (hxRows j1' hj1') hk2').symm
  have hP_entry : FitsSignedWord (4 * p') (read2D P_mat j1 k2) := by
    refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K (read2D P_mat j1 k2) ?_
    rw [hP_eq j1 hj1 k2 hk2]
    exact hP_norm_p' j1 hj1 k2 hk2
  have h2s_le_t1 : 2 ^ s ≤ t1 := by
    rw [← ht1_pow]
    exact Nat.pow_le_pow_right zero_lt_two hs
  have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
    rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
  have hsyn_stage_entry : ∀ v1_s < 2 ^ s, FitsSignedWord (4 * p') (read2D syn_stage v1_s k2) := by
    intro v1_s hv1_s
    refine fitsSignedWord_of_norm_toScaledComplex_le pSub (p' + 1) (4 * p') (read2D syn_stage v1_s k2) ?_
      (by dsimp [pSub, p', pChild, pWork]; omega)
    dsimp only [syn_stage]
    rw [computableSyntheticFFTRadix2WithProgramCost_fst,
        ← array_getD_getD_eq_read2D_pair _ v1_s k2]
    have hnorm_stage := norm_toScaledComplex_computableSyntheticFFTRadix2_le pSub t1 r s (r / t1) hr
      P_mat ((2 : ℝ) ^ p')
      (fun j hj m hm => by
        rw [array_getD_getD_eq_read2D_pair, hP_eq j (hj.trans_le h2s_le_t1) m hm]
        exact hP_norm_p' j (hj.trans_le h2s_le_t1) m hm)
      v1_s k2 hv1_s hk2
    have h1_le_p' : (1 : ℝ) ≤ (2 : ℝ) ^ p' := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    rw [pow_succ']
    linarith
  have hQ_eq : ∀ v1' < t1, ∀ k2' < r,
      toScaledComplex pSub (read2D Q_mat v1' k2') = Q v1' k2' := by
    intro v1' hv1' k2' hk2'
    dsimp only [Q_mat, runScan2DCostedWithSteps, costedGRescale, Q, syn_out]
    rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1' hk2', toScaledComplex_gRescale_eq]
    apply congrArg (complexQuantize pSub)
    rw [computableSyntheticFFTRadix2WithProgramCost_fst,
        ← array_getD_getD_eq_read2D_pair _ v1' k2',
        toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1' k2' (ht1_pow.symm ▸ hv1') hk2']
    refine syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P (fun j hj m hm => ?_) v1' k2' hk2'
    rw [array_getD_getD_eq_read2D_pair]
    exact hP_eq j (ht1_pow ▸ hj) m hm
  have hQ_entry4 : FitsSignedWord (4 * p') (read2D Q_mat v1 k2) := by
    refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K (read2D Q_mat v1 k2) ?_
    rw [hQ_eq v1 hv1 k2 hk2]
    exact hQ_norm_p'
  have hQ_entry6 : FitsSignedWord (6 * p') (read2D Q_mat v1 k2) :=
    fitsSignedWord_mono hQ_entry4 (by omega)
  have hqPost_eq : toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
    dsimp only [qPost_mat, runScan2DCostedWithSteps, costedGMulScaled, qPost]
    rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
  have hqPost_entry : FitsSignedWord (4 * p') (read2D qPost_mat v1 k2) := by
    refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K (read2D qPost_mat v1 k2) ?_
    rw [hqPost_eq]
    exact norm_qPost_of_faithful_le_two_pow_pChild p K t1 r ht1 hr hsize
      filterTaps preTwiddles postTwiddles hTaps hPre hPost x hx_norm v1 k2 hk2
  exact ⟨hU_entry, hP_entry, hsyn_stage_entry, hQ_entry4, hQ_entry6, hqPost_entry⟩

/-- **Faithful-Table Call-Site Width Soundness 4 — Forward, Nyquist, and Backward Solvers
(`programCost_solvers_widths_sound_of_faithful`, `[MS]` §3.2)**:
Under the `TablesFaithful` T4 condition (`hC01`) on `c0Table` and `c1Table`, for every column `u2 < r`,
step `n < t1`, and index `u1 ≤ n`, in the active solver regime (`2 * u2 < r`, `2 * u2 = r`, or `r < 2 * u2`),
all recurrence states (`buildComputableZPartFwdWithProgramCost`, `buildComputableZHomFwdWithProgramCost`,
`buildComputableZPartNyqWithProgramCost`, including the backward-reversed recurrence on `runBwdRevSteps`)
and solver outputs (`computableSolveBidiagonalFwdWithProgramCost`, `computableSolveNyquistWithProgramCost`,
`computableSolveBidiagonalBwdWithProgramCost`) fit in `4 * pChild p K` signed bits (`FitsSignedWord (4 * p')`),
and the dequantized solver output has norm `≤ (2 : ℝ) ^ (pChild p K)`. -/
theorem programCost_solvers_widths_sound_of_faithful
    (p K t1 r : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K)
    (ht1 : 0 < t1) (hr : 0 < r) (hr_le : r ≤ 2 * t1) (hsize : t1 * r = 2 ^ K)
    (c0Table c1Table : Array (ℤ × ℤ))
    (hC01 : ∀ u2 < r,
      let pSub := 2 * pChild p K
      let y := (u2 : ℝ) / (r : ℝ)
      let α := alphaSchedule (pWork p K)
      let c0_pair := read1D c0Table u2
      let c1_pair := read1D c1Table u2
      c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
      0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
      0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
      |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
        2 * realQuantizeMaxErr pSub ∧
      |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
        2 * realQuantizeMaxErr pSub ∧
      (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
      (2 * u2 = r → c1_pair = c0_pair) ∧
      (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1))
    (Y_col : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ)
    (hY : ∀ k < t1, ‖toScaledComplex (2 * pChild p K) (read1D Y_col k)‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (halt_q : ‖toScaledComplex (2 * pChild p K) alt_q‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p)
    (u2 n u1 : ℕ) (hu2 : u2 < r) (hn : n < t1) (hu1_le_n : u1 ≤ n) :
    let p' := pChild p K
    let pSub := 2 * p'
    let c0 := read1D c0Table u2
    let c1_pass := read1D c1Table u2
    let Y_rev := (runBwdRevSteps t1 (read1D Y_col) t1).outTape
    let z_out :=
      if 2 * u2 < r then
        read1D (computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1
      else if 2 * u2 = r then
        read1D (computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q).1 u1
      else
        read1D (computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1
    (2 * u2 < r →
      FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c0 c1_pass Y_col n).1 u1) ∧
      FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c0 c1_pass n).1 u1)) ∧
    (2 * u2 = r →
      FitsSignedWord (4 * p') (read1D (buildComputableZPartNyqWithProgramCost pSub (10 * p') c0 Y_col n).1 u1)) ∧
    (r < 2 * u2 →
      FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c1_pass c0 Y_rev n).1 u1) ∧
      FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c1_pass c0 n).1 u1)) ∧
    FitsSignedWord (4 * p') z_out ∧
    ‖toScaledComplex pSub z_out‖ ≤ (2 : ℝ) ^ p' := by
  dsimp only
  set p' := pChild p K
  set pSub := 2 * p'
  set c0 := read1D c0Table u2
  set c1_pass := read1D c1Table u2
  set c0_q := toScaledComplex pSub c0
  set c1_q := toScaledComplex pSub c1_pass
  set Y_rev := (runBwdRevSteps t1 (read1D Y_col) t1).outTape
  have hu1 : u1 < t1 := hu1_le_n.trans_lt hn
  obtain ⟨hfwd_pre, hnyq_pre, hbwd_pre⟩ :=
    faithful_c0_c1_solver_preconditions p K t1 r hp hK ht1 hr hr_le hsize c0Table c1Table hC01 u2 hu2
  have hY_rev : ∀ k < t1, ‖toScaledComplex pSub (read1D Y_rev k)‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
    intro k hk
    dsimp only [Y_rev]
    rw [read1D_runBwdRevSteps_eq t1 (read1D Y_col) t1 k hk]
    split_ifs with hk0
    · exact hY 0 ht1
    · exact hY (t1 - k) (by omega)
  have hf_fwd : 2 * u2 < r →
      FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c0 c1_pass Y_col n).1 u1) ∧
      FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c0 c1_pass n).1 u1) ∧
      FitsSignedWord (4 * p') (read1D (computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1) ∧
      ‖toScaledComplex pSub (read1D (computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1)‖ ≤
        (2 : ℝ) ^ p' := by
    intro h_fwd
    obtain ⟨hc0_ge, hc0_le1, hc10, hDq⟩ := hfwd_pre h_fwd
    have hrec := solver_recurrence_word_width_bounds p K t1 r ht1 hr hsize c0_q c1_q hc0_ge hc10
      (fun k => toScaledComplex pSub (read1D Y_col k)) hY u1 hu1
    have hout := solver_outputs_word_width_bounds p K t1 r ht1 hr hsize c0_q c1_q hc0_ge hc0_le1 hc10 hDq
      (fun k => toScaledComplex pSub (read1D Y_col k)) hY (toScaledComplex pSub alt_q) halt_q u1 hu1
    have hout_norm :
        ‖toScaledComplex pSub (read1D (computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1)‖ ≤
          (2 : ℝ) ^ p' := by
      rw [computableSolveBidiagonalFwdWithProgramCost_fst,
          toScaledComplex_computableSolveBidiagonalFwdExact_eq _ t1 _ _ _ u1 hu1]
      exact hout.2.1
    refine ⟨?_, ?_, ?_, hout_norm⟩
    · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
      rw [buildComputableZPartFwdWithProgramCost_fst,
          toScaledComplex_read1D_buildComputableZPartFwdExact_eq _ _ _ _ n u1 hu1_le_n]
      exact hrec.2.1
    · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
      rw [buildComputableZHomFwdWithProgramCost_fst,
          toScaledComplex_read1D_buildComputableZHomFwdExact_eq _ _ _ n u1 hu1_le_n]
      exact hrec.1
    · exact fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ hout_norm
  have hf_nyq : 2 * u2 = r →
      FitsSignedWord (4 * p') (read1D (buildComputableZPartNyqWithProgramCost pSub (10 * p') c0 Y_col n).1 u1) ∧
      FitsSignedWord (4 * p') (read1D (computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q).1 u1) ∧
      ‖toScaledComplex pSub (read1D (computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q).1 u1)‖ ≤
        (2 : ℝ) ^ p' := by
    intro h_nyq
    obtain ⟨hc0_ge, hc0_le1⟩ := hnyq_pre h_nyq
    have h0_le : ‖(0 : ℂ)‖ ≤ ‖c0_q‖ := by rw [norm_zero]; linarith
    have hratio0 : (‖(0 : ℂ)‖ / ‖c0_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
      rw [norm_zero, zero_div, zero_pow ht1.ne']; norm_num
    have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_right t1 hr
    have ht1_qSub := (t1_mul_complexQuantizeMaxErr_two_mul_pChild_le p K t1 ht1_le_2K).2
    have hDq0 : (0.4 : ℝ) ≤ ‖c0_q + 0 * zHomFwdQuantized pSub c0_q 0 (t1 - 1)‖ :=
      norm_denom_zHomFwdQuantized_ge_04 pSub t1 ht1 c0_q 0 hc0_ge hc0_le1 h0_le hratio0 (by linarith)
    have hrec := solver_recurrence_word_width_bounds p K t1 r ht1 hr hsize c0_q 0 hc0_ge h0_le
      (fun k => toScaledComplex pSub (read1D Y_col k)) hY u1 hu1
    have hout := solver_outputs_word_width_bounds p K t1 r ht1 hr hsize c0_q 0 hc0_ge hc0_le1 h0_le hDq0
      (fun k => toScaledComplex pSub (read1D Y_col k)) hY (toScaledComplex pSub alt_q) halt_q u1 hu1
    have hout_norm :
        ‖toScaledComplex pSub (read1D (computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q).1 u1)‖ ≤
          (2 : ℝ) ^ p' := by
      rw [computableSolveNyquistWithProgramCost_fst,
          toScaledComplex_computableSolveNyquistExact_eq _ t1 _ _ _ u1 hu1]
      exact hout.2.2.2.1
    refine ⟨?_, ?_, hout_norm⟩
    · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
      rw [buildComputableZPartNyqWithProgramCost_fst,
          toScaledComplex_read1D_buildComputableZPartNyqExact_eq _ _ _ n u1 hu1_le_n]
      exact hrec.2.2.1
    · exact fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ hout_norm
  have hf_bwd : r < 2 * u2 →
      FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c1_pass c0 Y_rev n).1 u1) ∧
      FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c1_pass c0 n).1 u1) ∧
      FitsSignedWord (4 * p') (read1D (computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1) ∧
      ‖toScaledComplex pSub (read1D (computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1)‖ ≤
        (2 : ℝ) ^ p' := by
    intro h_bwd
    obtain ⟨hc1_ge, hc1_le1, hc01, hDq⟩ := hbwd_pre h_bwd
    have hrec := solver_recurrence_word_width_bounds p K t1 r ht1 hr hsize c1_q c0_q hc1_ge hc01
      (fun k => toScaledComplex pSub (read1D Y_rev k)) hY_rev u1 hu1
    have hbwd := solveBidiagonalBwdQuantized_word_width_bounds p K t1 r ht1 hr hsize c0_q c1_q
      hc1_ge hc1_le1 hc01 hDq (fun k => toScaledComplex pSub (read1D Y_col k)) hY u1 hu1
    have hout_norm :
        ‖toScaledComplex pSub (read1D (computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col).1 u1)‖ ≤
          (2 : ℝ) ^ p' := by
      rw [computableSolveBidiagonalBwdWithProgramCost_fst,
          toScaledComplex_computableSolveBidiagonalBwdExact_eq _ t1 _ _ _ u1 hu1]
      exact hbwd.1
    refine ⟨?_, ?_, ?_, hout_norm⟩
    · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
      rw [buildComputableZPartFwdWithProgramCost_fst,
          toScaledComplex_read1D_buildComputableZPartFwdExact_eq _ _ _ _ n u1 hu1_le_n]
      exact hrec.2.1
    · refine fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ ?_
      rw [buildComputableZHomFwdWithProgramCost_fst,
          toScaledComplex_read1D_buildComputableZHomFwdExact_eq _ _ _ n u1 hu1_le_n]
      exact hrec.1
    · exact fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K _ hout_norm
  refine ⟨fun h => ⟨(hf_fwd h).1, (hf_fwd h).2.1⟩,
          fun h => (hf_nyq h).1,
          fun h => ⟨(hf_bwd h).1, (hf_bwd h).2.1⟩, ?_⟩
  split_ifs with h1 h2
  · exact ⟨(hf_fwd h1).2.2.1, (hf_fwd h1).2.2.2⟩
  · exact ⟨(hf_nyq h2).2.1, (hf_nyq h2).2.2⟩
  · have h_bwd : r < 2 * u2 := by omega
    exact ⟨(hf_bwd h_bwd).2.2.1, (hf_bwd h_bwd).2.2.2⟩

/-- **Faithful-Table Call-Site Width Soundness 5 — Leaf `BaseRadix2FFT`
(`programCost_leaf_baseRadix2FFT_widths_sound_of_faithful`, `[MS]` §3.2)**:
At any leaf `(p, K)` with `8 ≤ p`, `q_leaf = 2 * p + K + 8`, and any `twiddles` satisfying the
`TablesFaithful` T1 condition (`≤ 2 * complexQuantizeMaxErr q_leaf`), every intermediate butterfly
stage `s ≤ K` of `computableBaseRadix2FFTCoreWithProgramCost` and every leaf output of
`computableBaseRadix2FFTWithProgramCost` fits in `4 * q_leaf` signed bits (`FitsSignedWord (4 * q_leaf)`). -/
theorem programCost_leaf_baseRadix2FFT_widths_sound_of_faithful
    (p_in p K : ℕ) (hp : 8 ≤ p)
    (twiddles : Array (Array (ℤ × ℤ)))
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex (2 * p + K + 8) (read1D (twiddles.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * p + K + 8))
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < 2 ^ K, x k = toScaledComplex p_in (read1D xArr k))
    (hx_norm : ∀ k < 2 ^ K, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (s u : ℕ) (hs : s ≤ K) (hu_s : u < 2 ^ s) :
    let q_leaf := 2 * p + K + 8
    FitsSignedWord (4 * q_leaf)
      (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).1 u) ∧
    FitsSignedWord (4 * q_leaf)
      (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u) := by
  dsimp only
  set q_leaf := 2 * p + K + 8
  have h2s_le_2K : 2 ^ s ≤ 2 ^ K := Nat.pow_le_pow_right zero_lt_two hs
  have hu_K : u < 2 ^ K := hu_s.trans_le h2s_le_2K
  have hx_s : ∀ k < 2 ^ s, x k = toScaledComplex p_in (read1D xArr k) :=
    fun k hk => hx k (hk.trans_le h2s_le_2K)
  have hx_norm_s : ∀ k < 2 ^ s, ‖x k‖ ≤ (2 : ℝ) ^ p :=
    fun k hk => hx_norm k (hk.trans_le h2s_le_2K)
  have htw_s : ∀ s' < s, ∀ u' < 2 ^ (s' + 1),
      ‖toScaledComplex q_leaf (read1D (twiddles.getD s' #[]) u') -
          stdChar ((u' : ℝ) / ((2 ^ (s' + 1) : ℕ) : ℝ))‖ ≤
        2 * complexQuantizeMaxErr q_leaf :=
    fun s' hs' u' hu' => htw s' (hs'.trans_le hs) u' hu'
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hpow_neg_le1 : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hfactor_K : ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf ≤ 1 := by
    have h1 := baseRadix2FFTOfTwiddles_core_err_factor_le p K
    dsimp [q_leaf]
    nlinarith
  have hfactor_s : ((s + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf ≤ 1 := by
    have hs_le_K : ((s + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hs 1
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr q_leaf := by unfold complexQuantizeMaxErr; positivity
    nlinarith
  have hcore_norm : ‖baseRadix2FFTCoreOfTwiddles q_leaf twiddles s x u‖ ≤ (2 : ℝ) ^ (p + 1) := by
    have herr := norm_baseRadix2FFTCoreOfTwiddles_sub_exact_le q_leaf s twiddles htw_s hfactor_s
      x ((2 : ℝ) ^ p) hM1 hx_norm_s u
    have herr_le : ‖baseRadix2FFTCoreOfTwiddles q_leaf twiddles s x u - baseRadix2FFTExact s x u‖ ≤ (2 : ℝ) ^ p :=
      herr.trans (mul_le_of_le_one_left (by positivity) hfactor_s)
    have hexact : ‖baseRadix2FFTExact s x u‖ ≤ (2 : ℝ) ^ p := by
      rw [baseRadix2FFTExact_eq_dft1D]
      exact dft1D_norm_le (2 ^ s) (pow_pos zero_lt_two s) x ((2 : ℝ) ^ p)
        (fun k hk => hx_norm_s k (Finset.mem_range.mp hk)) u
    have htri := norm_add_le
      (baseRadix2FFTCoreOfTwiddles q_leaf twiddles s x u - baseRadix2FFTExact s x u)
      (baseRadix2FFTExact s x u)
    rw [sub_add_cancel] at htri
    rw [pow_succ']
    linarith
  have hcore_fit :
      FitsSignedWord (4 * q_leaf)
        (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le q_leaf (p + 1) (4 * q_leaf) _ ?_ (by dsimp [q_leaf]; omega)
    rw [toScaledComplex_computableBaseRadix2FFTCoreWithProgramCost_eq_ofTwiddles p_in q_leaf twiddles s xArr x hx_s u hu_s]
    exact hcore_norm
  have hout_norm : ‖baseRadix2FFTOfTwiddles p K twiddles x u‖ ≤ (2 : ℝ) ^ (p + 1) := by
    have herr := norm_baseRadix2FFTOfTwiddles_sub_dft1D_le p K twiddles htw x ((2 : ℝ) ^ p) hM1 hx_norm u
    have hexact : ‖dft1D (2 ^ K) x u‖ ≤ (2 : ℝ) ^ p :=
      dft1D_norm_le (2 ^ K) (pow_pos zero_lt_two K) x ((2 : ℝ) ^ p)
        (fun k hk => hx_norm k (Finset.mem_range.mp hk)) u
    have htri := norm_add_le
      (baseRadix2FFTOfTwiddles p K twiddles x u - dft1D (2 ^ K) x u)
      (dft1D (2 ^ K) x u)
    rw [sub_add_cancel] at htri
    rw [pow_succ']
    nlinarith
  have hout_fit :
      FitsSignedWord (4 * q_leaf)
        (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le p (p + 1) (4 * q_leaf) _ ?_ (by dsimp [q_leaf]; omega)
    rw [toScaledComplex_computableBaseRadix2FFTWithProgramCost_eq_ofTwiddles p_in p K twiddles xArr x hx u hu_K]
    exact hout_norm
  exact ⟨hcore_fit, hout_fit⟩

/-- **Recursive-Tree Call-Site Operand Width Soundness (`AllCallSitesWidthSound`, `[MS]` §3.2)**:
Certifies by structural recursion on `cSpec : ComputablePaperFastDFTSpec` that at every recursive
step and every leaf reached during execution of `computablePaperFastDFTWithProgramCost p_in cSpec xArr`:
- At a `.basePow2 p K twiddles` leaf (`q_leaf = 2 * p + K + 8`), for every stage `s ≤ K` and index
  `u < 2 ^ s`, the intermediate butterfly stage entry of `computableBaseRadix2FFTCoreWithProgramCost`
  and the leaf output entry of `computableBaseRadix2FFTWithProgramCost` satisfy `FitsSignedWord (4 * q_leaf)`.
- At a `.step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child` node
  (`p' = pSub / 2`):
  1. Every spread bucket output `read2D U_mat j1 k2` (`j1 < t1`, `k2 < r`) satisfies `FitsSignedWord (6 * p')`,
  2. Every pre-twisted entry `read2D P_mat j1 k2` (`j1 < t1`, `k2 < r`) satisfies `FitsSignedWord (4 * p')`,
  3. At every stage `s ≤ m_t1` of `computableSyntheticFFTRadix2WithProgramCost`, every entry
     `read2D (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1 v1_s k2`
     (`v1_s < 2 ^ s`, `k2 < r`) satisfies `FitsSignedWord (4 * p')`,
  4. Every rescaled Synthetic FFT output `read2D Q_mat v1 k2` (`v1 < t1`, `k2 < r`) satisfies
     `FitsSignedWord (4 * p')` and `FitsSignedWord (6 * p')`,
  5. Every post-twisted child-input entry `read2D qPost_mat v1 k2` (`v1 < t1`, `k2 < r`) satisfies
     `FitsSignedWord (4 * p')`,
  6. **Recursive Child Call Soundness**: For every `v1 < t1`, the recursive child call on
     `qPost_mat.getD v1 #[]` satisfies `AllCallSitesWidthSound pSub child (qPost_mat.getD v1 #[])`,
  7. Every routed child output `read2D Y_mat u2 u1` (`u2 < r`, `u1 < t1`) and the Nyquist alternating
     sum `alt_q` satisfy `FitsSignedWord (4 * p')`,
  8. For every `u2 < r`, `n < t1`, and `u1 ≤ n`, in the active solver regime (`2 * u2 < r`,
     `2 * u2 = r`, or `r < 2 * u2`), every recurrence state (`buildComputableZPartFwdWithProgramCost`,
     `buildComputableZHomFwdWithProgramCost`, `buildComputableZPartNyqWithProgramCost`, including on
     the backward-reversed input `(runBwdRevSteps t1 (read1D Y_col) t1).outTape`) and every
     solver output entry `read2D Z_cols_mat u2 u1` satisfies `FitsSignedWord (4 * p')`, and
  9. Every final rescaled output entry `read1D outScan.1 u` (`u < t1 * r`) satisfies `FitsSignedWord (4 * p')`. -/
def AllCallSitesWidthSound : ℕ → ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Prop
  | p_in, .basePow2 p K twiddles, xArr =>
    let q_leaf := 2 * p + K + 8
    ∀ s ≤ K, ∀ u < 2 ^ s,
      FitsSignedWord (4 * q_leaf)
        (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).1 u) ∧
      FitsSignedWord (4 * q_leaf)
        (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u)
  | p_in, .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, xArr =>
    let p' := pSub / 2
    let m_t1 := natLog2Fuel t1 t1
    let m_r := natLog2Fuel r r
    let xRoutedRes := runMultiTapeTransposeFullSteps m_t1 r (read1D xArr)
    let xRows_res :=
      runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
    let xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
    let U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        computableSpreadRowContiguousWithProgramCost p_in pSub p' m1 r
          (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
    let U_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
    let P_res :=
      runScan2DCostedWithSteps t1 r (fun j1 k2 =>
        costedGPreTwistU pSub (6 * p') (read1D preTwiddles k2) (read2D U_mat j1 k2))
    let P_mat : Array (Array (ℤ × ℤ)) := P_res.1
    let syn_res :=
      computableSyntheticFFTRadix2WithProgramCost p' t1 r m_t1 (r / t1) P_mat
    let Q_res :=
      runScan2DCostedWithSteps t1 r (fun v1 k2 =>
        costedGRescale pSub pSub (4 * p') (read2D syn_res.1 v1 k2))
    let Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
    let qPost_res :=
      runScan2DCostedWithSteps t1 r (fun v1 k2 =>
        costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2) (read2D Q_mat v1 k2))
    let qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
    let qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun v1 : Fin t1 =>
        computablePaperFastDFTWithProgramCost pSub child (qPost_mat.getD v1.val #[]))
    let qHat_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
    let stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
    let qHat_T_res := runMultiTapeTransposeFullSteps m_r t1 (read1D stFlatQ.outTape)
    let pChild_val := child.p
    let colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        runMultiTapeAffineOddRouteFullSteps m_t1
          (computableOddStrideFactor m_t1 u2.val) 0
          (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
    let Y_res :=
      runScan2DCostedWithSteps r t1 (fun u2 u1 =>
        let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
        costedGRescale pChild_val pSub (4 * p') (read1D colArr u1))
    let Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
    let altRes :=
      computableNyquistAltSumContiguousWithProgramCost p_in pSub p' r (xRows.getD (t1 / 2) #[])
    let alt_q : ℤ × ℤ := altRes.1
    let Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        let c0 := read1D c0Table u2.val
        let c1_pass := read1D c1Table u2.val
        let Y_col := Y_mat.getD u2.val #[]
        if 2 * u2.val < r then
          computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col
        else if 2 * u2.val = r then
          computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q
        else
          computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col)
    let Z_cols_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
    let stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
    let Z_flat_res := runMultiTapeTransposeFullSteps m_t1 r (read1D stFlatZ.outTape)
    let outScan := runSequentialScanCostedSteps (fun u =>
      costedGRescale pSub p (4 * p') (read1D Z_flat_res.1 u)) (t1 * r)
    (∀ j1 < t1, ∀ k2 < r,
      FitsSignedWord (6 * p') (read2D U_mat j1 k2) ∧
      FitsSignedWord (4 * p') (read2D P_mat j1 k2)) ∧
    (∀ s ≤ m_t1, ∀ v1_s < 2 ^ s, ∀ k2 < r,
      FitsSignedWord (4 * p')
        (read2D (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1 v1_s k2)) ∧
    (∀ v1 < t1, ∀ k2 < r,
      FitsSignedWord (4 * p') (read2D Q_mat v1 k2) ∧
      FitsSignedWord (6 * p') (read2D Q_mat v1 k2) ∧
      FitsSignedWord (4 * p') (read2D qPost_mat v1 k2)) ∧
    (∀ v1 < t1, AllCallSitesWidthSound pSub child (qPost_mat.getD v1 #[])) ∧
    FitsSignedWord (4 * p') alt_q ∧
    (∀ u2 < r, ∀ u1 < t1, FitsSignedWord (4 * p') (read2D Y_mat u2 u1)) ∧
    (∀ u2 < r, ∀ n < t1, ∀ u1 ≤ n,
      let c0 := read1D c0Table u2
      let c1_pass := read1D c1Table u2
      let Y_col := Y_mat.getD u2 #[]
      let Y_rev := (runBwdRevSteps t1 (read1D Y_col) t1).outTape
      (2 * u2 < r →
        FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c0 c1_pass Y_col n).1 u1) ∧
        FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c0 c1_pass n).1 u1)) ∧
      (2 * u2 = r →
        FitsSignedWord (4 * p') (read1D (buildComputableZPartNyqWithProgramCost pSub (10 * p') c0 Y_col n).1 u1)) ∧
      (r < 2 * u2 →
        FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c1_pass c0 Y_rev n).1 u1) ∧
        FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c1_pass c0 n).1 u1)) ∧
      FitsSignedWord (4 * p') (read2D Z_cols_mat u2 u1)) ∧
    (∀ u < t1 * r, FitsSignedWord (4 * p') (read1D outScan.1 u))
termination_by structural _ cSpec _ => cSpec

/-- Norm bound `‖toScaledComplex (2 * pChild p K) alt_q‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p`
for the Nyquist alternating sum `computableNyquistAltSumContiguousWithProgramCost`. -/
theorem norm_toScaledComplex_nyquistAltSumContiguous_le
    (p_in p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (hx_norm : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (xRow : Array (ℤ × ℤ))
    (hxRow : ∀ i < r, x (t1 / 2 + t1 * i) = toScaledComplex p_in (read1D xRow i)) :
    let p' := pChild p K
    let pSub := 2 * p'
    ‖toScaledComplex pSub
      (computableNyquistAltSumContiguousWithProgramCost p_in pSub p' r xRow).1‖ ≤
      (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
  dsimp only
  set p' := pChild p K
  set pSub := 2 * p'
  have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
  rw [computableNyquistAltSumContiguousWithProgramCost_fst,
      toScaledComplex_computableNyquistAltSumContiguous_eq p_in pSub t1 r hr xRow x hxRow]
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hinner : ‖∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖ ≤ (r : ℝ) * (2 : ℝ) ^ p := by
    calc ‖∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖
        ≤ ∑ j2 ∈ Finset.range r, ‖(-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖ := norm_sum_le _ _
      _ ≤ ∑ _j2 ∈ Finset.range r, (2 : ℝ) ^ p := by
          refine Finset.sum_le_sum fun j2 hj2_mem => ?_
          have hj2 : j2 < r := Finset.mem_range.mp hj2_mem
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          have hidx_lt : t1 / 2 + t1 * j2 < t1 * r := by
            have hj2_le : j2 + 1 ≤ r := hj2
            calc t1 / 2 + t1 * j2 < t1 + t1 * j2 := Nat.add_lt_add_right hhalf_lt _
              _ = t1 * (j2 + 1) := by ring
              _ ≤ t1 * r := Nat.mul_le_mul_left t1 hj2_le
          exact hx_norm _ hidx_lt
      _ = (r : ℝ) * (2 : ℝ) ^ p := by simp
  have hsum_le : ‖nyquistAltSum t1 r x‖ ≤ (2 : ℝ) ^ p := by
    unfold nyquistAltSum
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_natCast]
    calc 1 / (r : ℝ) * ‖∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)‖
        ≤ 1 / (r : ℝ) * ((r : ℝ) * (2 : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (2 : ℝ) ^ p := by field_simp
  have hq := norm_complexQuantize_le pSub (nyquistAltSum t1 r x)
  have hq_le1 : complexQuantizeMaxErr pSub ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt pSub
    have hp_le1 : (2 : ℝ) ^ (-(pSub : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    nlinarith
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith

/-- Norm and `FitsSignedWord (4 * pChild p K)` bounds for routed child DFT outputs under `TablesFaithful`. -/
theorem norm_and_fitsSignedWord_routed_child_output_of_faithful
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (child : QuantizedFastDFTSpec) (hchild_size : child.size = r) (hchild_p : child.p = pChild p K)
    (hchild : child.Valid)
    (cChild : ComputablePaperFastDFTSpec) (hchild_faith : TablesFaithful cChild child)
    (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hPost : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (x : ℕ → ℂ) (hx_norm : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (v1_target u2 : ℕ) (hu2 : u2 < r) (w : ℤ × ℤ)
    (hw :
      let pSub := 2 * pChild p K
      let U : ℕ → ℕ → ℂ := fun j1 k2 =>
        kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 k2
      let P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
      let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
      toScaledComplex pSub w =
        complexQuantize pSub (sincGaussianFastDFTOfTables cChild (qPost v1_target) u2)) :
    ‖toScaledComplex (2 * pChild p K) w‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p ∧
    FitsSignedWord (4 * pChild p K) w := by
  dsimp only at hw
  set p' := pChild p K
  set pSub := 2 * p'
  set U : ℕ → ℕ → ℂ := fun j1 k2 =>
    kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 k2
  set P : ℕ → ℕ → ℂ := fun j1 k2 =>
    complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
  set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
    complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
  set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
    complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hMr_ge1 : 1 ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by nlinarith
  have hqPost_r1 : ∀ k < child.size, ‖qPost v1_target k‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p := by
    intro k hk
    exact norm_qPost_of_faithful_le_r_add_one p K t1 r ht1 hr hsize
      filterTaps preTwiddles postTwiddles hTaps hPre hPost x hx_norm v1_target k (hchild_size ▸ hk)
  have herr := sincGaussianFastDFTOfTables_error_le child hchild cChild hchild_faith
    (qPost v1_target) (((r : ℝ) + 1) * (2 : ℝ) ^ p) hMr_ge1 hqPost_r1 u2 (hchild_size.symm ▸ hu2)
  rw [hchild_size, hchild_p] at herr
  have hdft := dft1D_norm_le r hr (qPost v1_target) (((r : ℝ) + 1) * (2 : ℝ) ^ p)
    (fun k hk => hqPost_r1 k (hchild_size.symm ▸ Finset.mem_range.mp hk)) u2
  have hpow_le1 : (2 : ℝ) ^ (-(p' : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hqHat_le :
      ‖sincGaussianFastDFTOfTables cChild (qPost v1_target) u2‖ ≤
        (2 * (r : ℝ) + 2) * (2 : ℝ) ^ p := by
    have htri := norm_add_le
      (sincGaussianFastDFTOfTables cChild (qPost v1_target) u2 - dft1D r (qPost v1_target) u2)
      (dft1D r (qPost v1_target) u2)
    rw [sub_add_cancel] at htri
    nlinarith
  have hquant := norm_complexQuantize_le pSub (sincGaussianFastDFTOfTables cChild (qPost v1_target) u2)
  have hq_le1 : complexQuantizeMaxErr pSub ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt pSub
    have hp_le1 : (2 : ℝ) ^ (-(pSub : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    nlinarith
  have hnorm : ‖toScaledComplex pSub w‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
    rw [hw]
    nlinarith
  have h2r3_le_p' : (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p ≤ (2 : ℝ) ^ p' := by
    have hr_le : r ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_left r ht1
    have h2r3_nat : 2 * r + 3 ≤ 2 ^ (2 * K + 12) := by
      have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
      have h2 : 2 * r + 3 ≤ 2 ^ (K + 3) := by rw [pow_add]; change 2 * r + 3 ≤ 2 ^ K * 8; omega
      exact h2.trans (Nat.pow_le_pow_right zero_lt_two (by omega))
    have h2r3_real : 2 * (r : ℝ) + 3 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast h2r3_nat
    calc (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p
        ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p := mul_le_mul_of_nonneg_right h2r3_real (by positivity)
      _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
      _ = (2 : ℝ) ^ p' := by dsimp [p']; rw [pChild_eq_additive]
  exact ⟨hnorm, fitsSignedWord_four_mul_pChild_of_norm_toScaledComplex_le p K w (hnorm.trans h2r3_le_p')⟩

/-- Bridge from `toScaledComplex p w = complexQuantize p z` and `‖z‖ ≤ (2 : ℝ) ^ (pChild p K)`
to `FitsSignedWord (4 * pChild p K) w`. -/
theorem fitsSignedWord_four_mul_pChild_of_toScaledComplex_eq_complexQuantize
    (p K : ℕ) (w : ℤ × ℤ) (z : ℂ)
    (hw : toScaledComplex p w = complexQuantize p z)
    (hz : ‖z‖ ≤ (2 : ℝ) ^ (pChild p K)) :
    FitsSignedWord (4 * pChild p K) w := by
  set p' := pChild p K
  refine fitsSignedWord_of_norm_toScaledComplex_le p (p' + 1) (4 * p') w ?_
    (by dsimp [p', pChild, pWork]; omega)
  rw [hw]
  have hquant := norm_complexQuantize_le p z
  have hq_le1 : complexQuantizeMaxErr p ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt p
    have hp_le1 : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    nlinarith
  have h1_le_p' : (1 : ℝ) ≤ (2 : ℝ) ^ p' := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  rw [pow_succ']
  linarith

/-- **Recursive-Tree Call-Site Width Soundness Theorem under `TablesFaithful`
(`allCallSitesWidthSound_of_faithful`, `[MS]` §3.2)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`), any faithful
table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`hfaith : TablesFaithful cSpec spec`), and
any input array `xArr` dequantizing to `x` with `∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p`,
every priced call site across the entire recursive execution tree of
`computablePaperFastDFTWithProgramCost p_in cSpec xArr` satisfies `FitsSignedWord` (`AllCallSitesWidthSound p_in cSpec xArr`). -/
theorem allCallSitesWidthSound_of_faithful
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (hx_norm : ∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p) :
    AllCallSitesWidthSound p_in cSpec xArr := by
  induction hvalid generalizing cSpec p_in xArr x with
  | base p R =>
    cases hfaith with
    | @base p K twiddles hp _hK_le htw =>
      dsimp only [AllCallSitesWidthSound]
      dsimp only [QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx hx_norm
      intro s hs u hu_s
      exact programCost_leaf_baseRadix2FFT_widths_sound_of_faithful
        p_in p K hp twiddles htw xArr x hx hx_norm s u hs hu_s
  | @step p K t1 r c1 v1Of child hp hK ht1 _ht1_le hr hr_le hsize hc1 _heven hchild_size hchild_p hchild _hv1 _hv1_lt ih =>
    cases hfaith with
    | @step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        _hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      dsimp only [AllCallSitesWidthSound]
      dsimp only [QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx hx_norm
      have hp'_div : (2 * pChild p K) / 2 = pChild p K := Nat.mul_div_right (pChild p K) zero_lt_two
      have hm_t1 : natLog2Fuel t1 t1 = Nat.log2 t1 := natLog2Fuel_self t1
      have hm_r : natLog2Fuel r r = Nat.log2 r := natLog2Fuel_self r
      have hcChild_p : cChild.p = pChild p K := (hchild_faith.p_eq).trans hchild_p
      rw [hp'_div, hm_t1, hm_r, hcChild_p]
      obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
      obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
      set p' := pChild p K
      set pSub := 2 * p'
      set xRoutedRes := runMultiTapeTransposeFullSteps (Nat.log2 t1) r (read1D xArr)
      set xRows_res :=
        runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
      set xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
      have hxRow_eq : ∀ j1 < t1, ∀ i < r,
          x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i) := by
        intro j1 hj1 i hi
        dsimp only [xRows, xRows_res, xRoutedRes]
        have hj1_m : j1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hj1
        rw [read1D_array_getD_eq_read2D,
            read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi,
            runMultiTapeTransposeFullSteps_fst,
            read1D_runMultiTapeTranspose_index_eq (Nat.log2 t1) r hr (read1D xArr) j1 i hj1_m hi,
            ht1_pow]
        have hidx_lt : j1 + t1 * i < t1 * r := by
          have hi_le : i + 1 ≤ r := hi
          calc j1 + t1 * i < t1 + t1 * i := Nat.add_lt_add_right hj1 _
            _ = t1 * (i + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hi_le
        have hcomm : i * t1 + j1 = j1 + t1 * i := by ring
        rw [hcomm, hx (j1 + t1 * i) hidx_lt]
      set U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun j1 : Fin t1 =>
          computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
            (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
      set U_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
      set P_res :=
        runScan2DCostedWithSteps t1 r (fun j1 k2 =>
          costedGPreTwistU pSub (6 * p') (read1D preTwiddles k2) (read2D U_mat j1 k2))
      set P_mat : Array (Array (ℤ × ℤ)) := P_res.1
      set syn_res := computableSyntheticFFTRadix2WithProgramCost p' t1 r (Nat.log2 t1) (r / t1) P_mat
      set Q_res :=
        runScan2DCostedWithSteps t1 r (fun v1 k2 =>
          costedGRescale pSub pSub (4 * p') (read2D syn_res.1 v1 k2))
      set Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
      set qPost_res :=
        runScan2DCostedWithSteps t1 r (fun v1 k2 =>
          costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2) (read2D Q_mat v1 k2))
      set qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
      set qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun v1 : Fin t1 =>
          computablePaperFastDFTWithProgramCost pSub cChild (qPost_mat.getD v1.val #[]))
      set qHat_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
      set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
      set qHat_T_res := runMultiTapeTransposeFullSteps (Nat.log2 r) t1 (read1D stFlatQ.outTape)
      set colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          runMultiTapeAffineOddRouteFullSteps (Nat.log2 t1)
            (computableOddStrideFactor (Nat.log2 t1) u2.val) 0
            (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
      set Y_res :=
        runScan2DCostedWithSteps r t1 (fun u2 u1 =>
          let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
          costedGRescale p' pSub (4 * p') (read1D colArr u1))
      set Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
      set altRes :=
        computableNyquistAltSumContiguousWithProgramCost p_in pSub p' r (xRows.getD (t1 / 2) #[])
      set alt_q : ℤ × ℤ := altRes.1
      set Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          let c0 := read1D c0Table u2.val
          let c1_pass := read1D c1Table u2.val
          let Y_col := Y_mat.getD u2.val #[]
          if 2 * u2.val < r then
            computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col
          else if 2 * u2.val = r then
            computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q
          else
            computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col)
      set Z_cols_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
      set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
      set Z_flat_res := runMultiTapeTransposeFullSteps (Nat.log2 t1) r (read1D stFlatZ.outTape)
      set outScan := runSequentialScanCostedSteps (fun u =>
        costedGRescale pSub p (4 * p') (read1D Z_flat_res.1 u)) (t1 * r)
      set U : ℕ → ℕ → ℂ := fun j1 k2 =>
        kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 k2
      set P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
      set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
      have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r,
          toScaledComplex pSub ((P_mat.getD j1 #[]).getD k2 (0, 0)) = P j1 k2 := by
        intro j1 hj1 k2 hk2
        have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
        rw [array_getD_getD_eq_read2D_pair]
        dsimp only [P_mat, P_res, runScan2DCostedWithSteps, costedGPreTwistU, P]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2]
        have hU_row : read2D U_mat j1 k2 =
            read1D (computableSpreadRowContiguousWithCost p_in pSub pSub r
              (filterTaps.getD j1 []) (xRows.getD j1 #[])).1 k2 := by
          dsimp only [U_mat, U_rows]
          rw [read2D_ofFn_of_lt t1 _ hj1_t1 k2]
          simp only [Array.size_ofFn, hj1_t1, ↓reduceDIte, Array.getElem_ofFn,
            computableSpreadRowContiguousWithProgramCost_fst]
        rw [hU_row]
        exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2) _ (U j1 k2)
          (computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps
            p_in pSub pSub t1 r (filterTaps.getD j1 []) (xRows.getD j1 #[]) x j1 k2
            (hxRow_eq j1 hj1_t1) hk2).symm
      have hQ_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D Q_mat v1 k2) = Q v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [Q_mat, Q_res, runScan2DCostedWithSteps, costedGRescale, Q, syn_res]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize pSub)
        have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
          rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
        rw [computableSyntheticFFTRadix2WithProgramCost_fst,
            ← array_getD_getD_eq_read2D_pair _ v1 k2,
            toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1 k2 (ht1_pow.symm ▸ hv1) hk2]
        exact syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P hP_eq v1 k2 hk2
      have hqPost_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [qPost_mat, qPost_res, runScan2DCostedWithSteps, costedGMulScaled, qPost]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
      have htw_syn := fun j1 v1 k2 s (hj1 : j1 < t1) (hv1 : v1 < t1) (hk2 : k2 < r) (hs : s ≤ Nat.log2 t1) =>
        programCost_twist_and_syntheticFFT_widths_sound_of_faithful
          p_in p K t1 r c1 ht1 hr hsize hc1 filterTaps preTwiddles postTwiddles
          hTaps hPre hPost x hx_norm xRows hxRow_eq j1 v1 k2 s hj1 hv1 hk2 hs
      -- 1, 2, 3: U_mat, P_mat, syn_stage, Q_mat, qPost_mat
      have hUP : ∀ j1 < t1, ∀ k2 < r,
          FitsSignedWord (6 * p') (read2D U_mat j1 k2) ∧
          FitsSignedWord (4 * p') (read2D P_mat j1 k2) := by
        intro j1 hj1 k2 hk2
        have h := htw_syn j1 0 k2 0 hj1 ht1 hk2 (Nat.zero_le _)
        exact ⟨h.1, h.2.1⟩
      have hsyn_all : ∀ s ≤ Nat.log2 t1, ∀ v1_s < 2 ^ s, ∀ k2 < r,
          FitsSignedWord (4 * p')
            (read2D (computableSyntheticFFTRadix2WithProgramCost p' t1 r s (r / t1) P_mat).1 v1_s k2) := by
        intro s hs v1_s hv1_s k2 hk2
        have h := htw_syn 0 0 k2 s ht1 ht1 hk2 hs
        exact h.2.2.1 v1_s hv1_s
      have hQqP : ∀ v1 < t1, ∀ k2 < r,
          FitsSignedWord (4 * p') (read2D Q_mat v1 k2) ∧
          FitsSignedWord (6 * p') (read2D Q_mat v1 k2) ∧
          FitsSignedWord (4 * p') (read2D qPost_mat v1 k2) := by
        intro v1 hv1 k2 hk2
        have h := htw_syn 0 v1 k2 (Nat.log2 t1) ht1 hv1 hk2 le_rfl
        exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
      -- 4: Recursive child calls
      have hchild_sound : ∀ v1 < t1, AllCallSitesWidthSound pSub cChild (qPost_mat.getD v1 #[]) := by
        intro v1 hv1
        refine ih cChild hchild_faith pSub (qPost_mat.getD v1 #[]) (qPost v1)
          (fun k hk => ?_) (fun k hk => ?_)
        · have hk_r : k < r := hchild_size ▸ hk
          rw [read1D_array_getD_eq_read2D]
          exact (hqPost_eq v1 hv1 k hk_r).symm
        · have hk_r : k < r := hchild_size ▸ hk
          rw [hchild_p]
          exact norm_qPost_of_faithful_le_two_pow_pChild p K t1 r ht1 hr hsize
            filterTaps preTwiddles postTwiddles hTaps hPre hPost x hx_norm v1 k hk_r
      -- 5: Nyquist alternating sum alt_q
      have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
      have halt_sound : FitsSignedWord (4 * p') alt_q :=
        programCost_nyquist_altSum_widths_sound p_in p K t1 r ht1 hr hsize x hx_norm
          (xRows.getD (t1 / 2) #[]) (hxRow_eq (t1 / 2) hhalf_lt)
      have halt_norm : ‖toScaledComplex pSub alt_q‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p :=
        norm_toScaledComplex_nyquistAltSumContiguous_le p_in p K t1 r ht1 hr x hx_norm
          (xRows.getD (t1 / 2) #[]) (hxRow_eq (t1 / 2) hhalf_lt)
      -- 6: Routed child outputs Y_mat
      have hY_eq : ∀ u2 < r, ∀ u1 < t1,
          toScaledComplex pSub (read2D Y_mat u2 u1) =
            complexQuantize pSub
              (sincGaussianFastDFTOfTables cChild
                (qPost (oddStrideInvPow2 (Nat.log2 t1) u2 u1)) u2) := by
        intro u2 hu2 u1 hu1
        have hu1_m : u1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hu1
        set v1_target := oddStrideInvPow2 (Nat.log2 t1) u2 u1
        have hv1_lt : v1_target < t1 := by
          dsimp [v1_target]
          rw [← _hv1_eq u2 u1]
          exact _hv1_lt u2 hu2 u1 hu1
        dsimp only [Y_mat, Y_res, runScan2DCostedWithSteps, costedGRescale, colRoutes, qHat_T_res, stFlatQ, qHat_mat, qHat_res]
        rw [read2D_runScan2DWithSteps_of_lt r t1 _ hu2 hu1]
        simp only [Array.size_ofFn, hu2, ↓reduceDIte, Array.getElem_ofFn, toScaledComplex_gRescale_eq]
        rw [runMultiTapeAffineOddRouteFullSteps_fst, computableOddStrideFactor_eq_oddStrideFactor,
            read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq (Nat.log2 t1) u2 u1 _ hu1_m,
            runMultiTapeTransposeFullSteps_fst,
            read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 r) r t1 hr_pow ht1 _ u2 v1_target hu2 hv1_lt,
            read2D_ofFn_of_lt t1 _ hv1_lt u2]
        simp only [hv1_lt, ↓reduceDIte]
        apply congrArg (complexQuantize pSub)
        rw [← hchild_p]
        exact toScaledComplex_computablePaperFastDFT_eq_ofTables
          child hchild cChild hchild_faith pSub
          (qPost_mat.getD v1_target #[]) (qPost v1_target)
          (fun k hk => by
            rw [read1D_array_getD_eq_read2D]
            exact (hqPost_eq v1_target hv1_lt k (hchild_size ▸ hk)).symm)
          u2 (hchild_size.symm ▸ hu2)
      have hY_both : ∀ u2 < r, ∀ u1 < t1,
          ‖toScaledComplex pSub (read2D Y_mat u2 u1)‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p ∧
          FitsSignedWord (4 * p') (read2D Y_mat u2 u1) :=
        fun u2 hu2 u1 hu1 =>
          norm_and_fitsSignedWord_routed_child_output_of_faithful p K t1 r ht1 hr hsize
            child hchild_size hchild_p hchild cChild hchild_faith
            filterTaps preTwiddles postTwiddles hTaps hPre hPost x hx_norm
            (oddStrideInvPow2 (Nat.log2 t1) u2 u1) u2 hu2 (read2D Y_mat u2 u1)
            (hY_eq u2 hu2 u1 hu1)
      have hY_sound : ∀ u2 < r, ∀ u1 < t1, FitsSignedWord (4 * p') (read2D Y_mat u2 u1) :=
        fun u2 hu2 u1 hu1 => (hY_both u2 hu2 u1 hu1).2
      -- 7: Solvers (recurrence states and Z_cols_mat)
      have hsolvers_all :
          ∀ u2 < r, ∀ n < t1, ∀ u1 ≤ n,
            let c0 := read1D c0Table u2
            let c1_pass := read1D c1Table u2
            let Y_col := Y_mat.getD u2 #[]
            let Y_rev := (runBwdRevSteps t1 (read1D Y_col) t1).outTape
            (2 * u2 < r →
              FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c0 c1_pass Y_col n).1 u1) ∧
              FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c0 c1_pass n).1 u1)) ∧
            (2 * u2 = r →
              FitsSignedWord (4 * p') (read1D (buildComputableZPartNyqWithProgramCost pSub (10 * p') c0 Y_col n).1 u1)) ∧
            (r < 2 * u2 →
              FitsSignedWord (4 * p') (read1D (buildComputableZPartFwdWithProgramCost pSub (10 * p') c1_pass c0 Y_rev n).1 u1) ∧
              FitsSignedWord (4 * p') (read1D (buildComputableZHomFwdWithProgramCost pSub (10 * p') c1_pass c0 n).1 u1)) ∧
            FitsSignedWord (4 * p') (read2D Z_cols_mat u2 u1) ∧
            ‖toScaledComplex pSub (read2D Z_cols_mat u2 u1)‖ ≤ (2 : ℝ) ^ p' := by
        intro u2 hu2 n hn u1 hu1_le_n
        dsimp only
        have hY_col : ∀ k < t1, ‖toScaledComplex pSub (read1D (Y_mat.getD u2 #[]) k)‖ ≤ (2 * (r : ℝ) + 3) * (2 : ℝ) ^ p := by
          intro k hk
          rw [read1D_array_getD_eq_read2D]
          exact (hY_both u2 hu2 k hk).1
        have hsol := programCost_solvers_widths_sound_of_faithful p K t1 r hp hK ht1 hr hr_le hsize
          c0Table c1Table hC01 (Y_mat.getD u2 #[]) alt_q hY_col halt_norm u2 n u1 hu2 hn hu1_le_n
        have hZ_eq :
            read2D Z_cols_mat u2 u1 =
              if 2 * u2 < r then
                read1D (computableSolveBidiagonalFwdWithProgramCost pSub p' t1 (read1D c0Table u2) (read1D c1Table u2) (Y_mat.getD u2 #[])).1 u1
              else if 2 * u2 = r then
                read1D (computableSolveNyquistWithProgramCost pSub p' t1 (read1D c0Table u2) (Y_mat.getD u2 #[]) alt_q).1 u1
              else
                read1D (computableSolveBidiagonalBwdWithProgramCost pSub p' t1 (read1D c0Table u2) (read1D c1Table u2) (Y_mat.getD u2 #[])).1 u1 := by
          dsimp only [Z_cols_mat, Z_cols_res]
          rw [read2D_ofFn_of_lt r _ hu2 u1]
          simp only [Array.size_ofFn, hu2, ↓reduceDIte, Array.getElem_ofFn]
          split_ifs <;> rfl
        rw [hZ_eq]
        exact hsol
      -- 8: Final rescaled output outScan.1
      have hout_sound : ∀ u < t1 * r, FitsSignedWord (4 * p') (read1D outScan.1 u) := by
        intro u hu
        have hu2 : u % r < r := Nat.mod_lt u hr
        have hu1_tilde : u / r < t1 := by rw [Nat.div_lt_iff_lt_mul hr]; linarith
        have hu_decomp : (u / r) * r + u % r = u := by rw [mul_comm, Nat.div_add_mod]
        refine fitsSignedWord_four_mul_pChild_of_toScaledComplex_eq_complexQuantize p K
          (read1D outScan.1 u) (toScaledComplex pSub (read2D Z_cols_mat (u % r) (u / r))) ?_
          (hsolvers_all (u % r) hu2 (u / r) hu1_tilde (u / r) le_rfl).2.2.2.2
        dsimp only [outScan, runSequentialScanCostedSteps, costedGRescale, Z_flat_res, stFlatZ]
        rw [read1D_runSequentialScanSteps_eq _ (t1 * r) u hu,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize p)
        apply congrArg (toScaledComplex pSub)
        rw [runMultiTapeTransposeFullSteps_fst]
        conv_lhs => rw [← hu_decomp]
        exact read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 t1) t1 r ht1_pow hr Z_cols_mat (u / r) (u % r) hu1_tilde hu2
      exact ⟨hUP, hsyn_all, hQqP, hchild_sound, halt_sound, hY_sound,
        fun u2 hu2 n hn u1 hu1_le =>
          let h := hsolvers_all u2 hu2 n hn u1 hu1_le
          ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩,
        hout_sound⟩

/-- **Faithful-Table Call-Site Width Soundness 6 — Root Pipeline and Full Recursive Call Trees
(`programCost_root_pipeline_widths_sound_of_faithful`, `[MS]` §3.2)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) and any faithful
table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`hfaith : TablesFaithful cSpec spec`) with
`spec.size = 2 ^ K0` and `spec.p = rootPrecision b K0`:
1. Every root chunk entry `read1D stPack.outTape u`, `read1D fwd.1 u`, `read1D stSq.1 u`, and
   `read1D inv.1 u` (`u < 2 ^ K0`) satisfies `FitsSignedWord (4 * p0)`,
2. Every priced call site reached across the **entire recursive forward `FastDFT` call tree**
   satisfies `AllCallSitesWidthSound b cSpec stPack.outTape`, and
3. Every priced call site reached across the **entire recursive inverse `FastDFT` call tree**
   satisfies `AllCallSitesWidthSound p0 cSpec stSq.1`. -/
theorem programCost_root_pipeline_widths_sound_of_faithful
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0) :
    let R0 := 2 ^ K0
    let p0 := rootPrecision b K0
    let asArr := (splitChunksTreeWithProgramCost b k1 A).1.toArray
    let bsArr := (splitChunksTreeWithProgramCost b k2 B).1.toArray
    let stPack := runSequentialScanSteps (fun j =>
      (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
    let fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
    let stSq := runSequentialScanCostedSteps (fun u' =>
      let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u') (read1D fwd.1 u')
      (gConj m.1, m.2 + addBitCost (8 * p0))) R0
    let inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.1
    (∀ u < R0,
      FitsSignedWord (4 * p0) (read1D stPack.outTape u) ∧
      FitsSignedWord (4 * p0) (read1D fwd.1 u) ∧
      FitsSignedWord (4 * p0) (read1D stSq.1 u) ∧
      FitsSignedWord (4 * p0) (read1D inv.1 u)) ∧
    AllCallSitesWidthSound b cSpec stPack.outTape ∧
    AllCallSitesWidthSound p0 cSpec stSq.1 := by
  dsimp only
  rw [splitChunksTreeWithProgramCost_fst, splitChunksTreeWithProgramCost_fst]
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
  set stSq := runSequentialScanCostedSteps (fun u' =>
    let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u') (read1D fwd.1 u')
    (gConj m.1, m.2 + addBitCost (8 * p0))) R0
  set inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.1
  have hp0_ge6 : 6 ≤ p0 := by dsimp [p0, rootPrecision]; omega
  have hb_le_p0 : b ≤ p0 := by dsimp [p0, rootPrecision]; omega
  have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_le2 : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hx_pack : ∀ k < spec.size, x_AB k = toScaledComplex b (read1D stPack.outTape k) :=
    fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm
  have hx_pack_norm_p : ∀ k < spec.size, ‖x_AB k‖ ≤ (2 : ℝ) ^ spec.p := by
    intro k _
    rw [hp0]
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ p0 := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ p0 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    exact ((norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k).trans hsqrt2_le2).trans h1
  have hfwd_tree : AllCallSitesWidthSound b cSpec stPack.outTape :=
    allCallSitesWidthSound_of_faithful spec hvalid cSpec hfaith b stPack.outTape x_AB hx_pack hx_pack_norm_p
  have hy : ∀ u' < R0, toScaledComplex p0 (read1D fwd.1 u') = sincGaussianFastDFTOfTables cSpec x_AB u' := by
    intro u' hu'
    rw [← hp0]
    exact toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith b stPack.outTape x_AB
      hx_pack u' (hsize.symm ▸ hu')
  have hpow_neg_le1 : (2 : ℝ) ^ (-(spec.p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hq_err : complexQuantizeMaxErr p0 ≤ 1 := by
    have hlt := complexQuantizeMaxErr_lt p0
    have hpow_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    nlinarith
  have hfwd_norm4 : ∀ u' < R0, ‖sincGaussianFastDFTOfTables cSpec x_AB u'‖ ≤ 4 := by
    intro u' hu'
    have hu_spec : u' < spec.size := hsize.symm ▸ hu'
    have herr := sincGaussianFastDFTOfTables_error_le spec hvalid cSpec hfaith x_AB (Real.sqrt 2) hsqrt2_ge1
      (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u' hu_spec
    have hdft_le : ‖dft1D spec.size x_AB u'‖ ≤ 2 := by
      have hpos : 0 < spec.size := by rw [hsize]; exact pow_pos zero_lt_two K0
      have h1 := dft1D_norm_le spec.size hpos x_AB (Real.sqrt 2)
        (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u'
      linarith
    have htri := norm_add_le (sincGaussianFastDFTOfTables cSpec x_AB u' - dft1D spec.size x_AB u')
      (dft1D spec.size x_AB u')
    rw [sub_add_cancel] at htri
    nlinarith
  set sConj : ℕ → ℂ := fun u' => star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u') ^ 2))
  have hsConj_eq : ∀ u' < spec.size, sConj u' = toScaledComplex p0 (read1D stSq.1 u') := by
    intro u' hu'
    have hu_R0 : u' < R0 := hsize ▸ hu'
    dsimp only [sConj, stSq, runSequentialScanCostedSteps, costedGMulScaled]
    rw [read1D_runSequentialScanSteps_eq _ R0 u' hu_R0, toScaledComplex_gConj,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u' hu_R0, sq]
  have hsConj_norm17 : ∀ u' < R0, ‖sConj u'‖ ≤ 17 := by
    intro u' hu'
    dsimp only [sConj]
    rw [norm_star]
    have h4 := hfwd_norm4 u' hu'
    have hsq_le16 : ‖(sincGaussianFastDFTOfTables cSpec x_AB u') ^ 2‖ ≤ 16 := by
      rw [norm_pow]
      nlinarith [norm_nonneg (sincGaussianFastDFTOfTables cSpec x_AB u')]
    have h1 := norm_complexQuantize_le p0 ((sincGaussianFastDFTOfTables cSpec x_AB u') ^ 2)
    linarith
  have hsConj_norm_p : ∀ u' < spec.size, ‖sConj u'‖ ≤ (2 : ℝ) ^ spec.p := by
    intro u' hu'
    rw [hp0]
    have h17 := hsConj_norm17 u' (hsize ▸ hu')
    have h64 : (17 : ℝ) ≤ (2 : ℝ) ^ 6 := by norm_num
    have hpow : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ p0 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp0_ge6
    linarith
  have hinv_tree : AllCallSitesWidthSound p0 cSpec stSq.1 :=
    allCallSitesWidthSound_of_faithful spec hvalid cSpec hfaith p0 stSq.1 sConj hsConj_eq hsConj_norm_p
  refine ⟨fun u hu => ?_, hfwd_tree, hinv_tree⟩
  have hpack_fit : FitsSignedWord (4 * p0) (read1D stPack.outTape u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le b 1 (4 * p0) _ ?_ (by omega)
    rw [← hx_pack u (hsize.symm ▸ hu), pow_one]
    exact (norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B u).trans hsqrt2_le2
  have hfwd_fit : FitsSignedWord (4 * p0) (read1D fwd.1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le p0 2 (4 * p0) _ ?_ (by omega)
    rw [hy u hu]
    calc ‖sincGaussianFastDFTOfTables cSpec x_AB u‖ ≤ 4 := hfwd_norm4 u hu
      _ = (2 : ℝ) ^ 2 := by norm_num
  have hsq_fit : FitsSignedWord (4 * p0) (read1D stSq.1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le p0 5 (4 * p0) _ ?_ (by omega)
    rw [← hsConj_eq u (hsize.symm ▸ hu)]
    calc ‖sConj u‖ ≤ 17 := hsConj_norm17 u hu
      _ ≤ (32 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ 5 := by norm_num
  have hinv_fit : FitsSignedWord (4 * p0) (read1D inv.1 u) := by
    refine fitsSignedWord_of_norm_toScaledComplex_le p0 6 (4 * p0) _ ?_ (by omega)
    have hz : toScaledComplex p0 (read1D inv.1 u) = sincGaussianFastDFTOfTables cSpec sConj u := by
      rw [← hp0]
      exact toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith p0 stSq.1
        sConj hsConj_eq u (hsize.symm ▸ hu)
    rw [hz]
    have hu_spec : u < spec.size := hsize.symm ▸ hu
    have herr := sincGaussianFastDFTOfTables_error_le spec hvalid cSpec hfaith sConj 17 (by norm_num)
      (fun k hk => hsConj_norm17 k (hsize ▸ hk)) u hu_spec
    have hdft : ‖dft1D spec.size sConj u‖ ≤ 17 := by
      have hpos : 0 < spec.size := by rw [hsize]; exact pow_pos zero_lt_two K0
      exact dft1D_norm_le spec.size hpos sConj 17
        (fun k hk => hsConj_norm17 k (hsize ▸ Finset.mem_range.mp hk)) u
    have htri := norm_add_le (sincGaussianFastDFTOfTables cSpec sConj u - dft1D spec.size sConj u)
      (dft1D spec.size sConj u)
    rw [sub_add_cancel] at htri
    have h34 : ‖sincGaussianFastDFTOfTables cSpec sConj u‖ ≤ 34 := by nlinarith
    calc ‖sincGaussianFastDFTOfTables cSpec sConj u‖ ≤ 34 := h34
      _ ≤ (64 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ 6 := by norm_num
  exact ⟨hpack_fit, hfwd_fit, hsq_fit, hinv_fit⟩

/-! ### 4. Oracle-Free 100% Computable End-to-End Multiplier (`computablePaperMultiplyOfBitLength`) -/

/-- **Oracle-Free 100% Computable Paper-Faithful Integer Multiplier with Program-Derived Cost
(`computablePaperMultiplyOfBitLength`, `[MS]` §7)**:
100% computable (`def`, zero `noncomputable`, zero `Real`, zero `Complex`, zero table oracle)
end-to-end integer multiplier returning `(product, totalBitCost) : ℕ × ℕ`:
1. Constructs the paper's adaptive stopping schedule `spec := buildQuantizedSpecPaperStop L p0 K0`
   ($R_\ell \le 4 p_\ell^2$ with `BaseRadix2FFT` leaves),
2. Compiles all four fixed-point table families (`T1`–`T4`: leaf `twiddles`, chirp
   `preTwiddles`/`postTwiddles`, modulo-`W_eff` folded `filterTaps`, and passband `c0Table`/`c1Table`)
   from scratch via fixed-point `BitCostM` series primitives in
   `cSpecRes := buildComputablePaperTablesWithProgramCost spec`, and
3. Executes the fixed-point Gaussian-integer (`ℤ × ℤ`) multiplier
   `mulRes := computablePaperFastDFTMultiplyWithProgramCost cSpecRes.1 b K0 k k A B`,
   returning `(mulRes.1, mulRes.2 + cSpecRes.2) : ℕ × ℕ`. -/
def computablePaperMultiplyOfBitLength (n A B : ℕ) : ℕ × ℕ :=
  let b := max 1 (Nat.log2 n)
  let k := n / b + 1
  let K0 := max 4 (Nat.log2 (2 * k) + 2)
  let L := Nat.log2 (K0 - 1)
  let p0 := rootPrecision b K0
  let spec := buildQuantizedSpecPaperStop L p0 K0
  let cSpecRes := buildComputablePaperTablesWithProgramCost spec
  let mulRes := computablePaperFastDFTMultiplyWithProgramCost cSpecRes.1 b K0 k k A B
  (mulRes.1, mulRes.2 + cSpecRes.2)

/-- **Headline Correctness, Recursive Call-Site Operand-Width Soundness, and Program-Derived
$O(n \log n)$ Complexity Theorem for the Oracle-Free Computable Multiplier
(`computablePaperMultiplyOfBitLength_correct_and_isBigO`, `[MS]` §7)**:
In the bit-cost RAM / sequential record-level array transducer model (with primitive operations
priced at `addBitCost w = w` and the non-circular Schönhage-Strassen rate `mulBitCost w`, and
with all precomputed tables constructed from scratch by `buildComputablePaperTablesWithProgramCost`):
1. **Exact Product Recovery**: For all `n, A, B : ℕ` with `A < 2 ^ n` and `B < 2 ^ n`,
   `(computablePaperMultiplyOfBitLength n A B).1 = A * B`,
2. **Program-to-Formula Upper-Bound Inequality**: For all `n, A, B : ℕ`, the program's accumulated
   integer bit-operation and tape-step cost (including series-table construction) satisfies
   `((computablePaperMultiplyOfBitLength n A B).2 : ℝ) ≤
     8192 * (quantizedMultiplyOfBitLengthPaperStopSeries n A B).2`,
3. **Explicit $O(n \log n)$ Upper Bound (`256 ≤ Nat.log2 n`)**: For all `n, A, B : ℕ` with `256 ≤ Nat.log2 n`,
   `((computablePaperMultiplyOfBitLength n A B).2 : ℝ) ≤
     (64552834170880 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))`,
4. **Asymptotic $O(n \log n)$ Bit Complexity**: For any operand sequences `A, B : ℕ → ℕ`,
   `(fun n : ℕ => ((computablePaperMultiplyOfBitLength n (A n) (B n)).2 : ℝ))
     =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))`, and
5. **Full Recursive Call-Site Operand Width Soundness (`AllCallSitesWidthSound`, `TableBuilderCallSitesWidthSound` & `FitsSignedWord`)**:
   For all `n, A, B : ℕ`, every root chunk entry (`stPack.outTape`, `fwd.1`, `stSq.1`, `inv.1`) fits in
   `4 * p0` signed bits, every priced call site reached across the **entire forward and inverse
   `FastDFT` recursion trees** (`AllCallSitesWidthSound b cSpec stPack.outTape` and
   `AllCallSitesWidthSound p0 cSpec stSq.1`), AND every priced call site inside the table builder
   (`TableBuilderCallSitesWidthSound spec`) fits within its declared bit-width parameter `w`. -/
theorem computablePaperMultiplyOfBitLength_correct_and_isBigO :
    (∀ n A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      (computablePaperMultiplyOfBitLength n A B).1 = A * B) ∧
    (∀ n A B : ℕ,
      ((computablePaperMultiplyOfBitLength n A B).2 : ℝ) ≤
        8192 * (quantizedMultiplyOfBitLengthPaperStopSeries n A B).2) ∧
    (∀ n A B : ℕ, 256 ≤ Nat.log2 n →
      ((computablePaperMultiplyOfBitLength n A B).2 : ℝ) ≤
        (64552834170880 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) ∧
    (∀ A B : ℕ → ℕ,
      (fun n : ℕ => ((computablePaperMultiplyOfBitLength n (A n) (B n)).2 : ℝ)) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))) ∧
    (∀ n A B : ℕ,
      let b := max 1 (Nat.log2 n)
      let k := n / b + 1
      let K0 := max 4 (Nat.log2 (2 * k) + 2)
      let L := Nat.log2 (K0 - 1)
      let p0 := rootPrecision b K0
      let spec := buildQuantizedSpecPaperStop L p0 K0
      let cSpec := (buildComputablePaperTablesWithProgramCost spec).1
      let R0 := 2 ^ K0
      let asArr := (splitChunksTreeWithProgramCost b k A).1.toArray
      let bsArr := (splitChunksTreeWithProgramCost b k B).1.toArray
      let stPack := runSequentialScanSteps (fun j =>
        (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
      let fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
      let stSq := runSequentialScanCostedSteps (fun u' =>
        let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u') (read1D fwd.1 u')
        (gConj m.1, m.2 + addBitCost (8 * p0))) R0
      let inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.1
      (∀ u < R0,
        FitsSignedWord (4 * p0) (read1D stPack.outTape u) ∧
        FitsSignedWord (4 * p0) (read1D fwd.1 u) ∧
        FitsSignedWord (4 * p0) (read1D stSq.1 u) ∧
        FitsSignedWord (4 * p0) (read1D inv.1 u)) ∧
      AllCallSitesWidthSound b cSpec stPack.outTape ∧
      AllCallSitesWidthSound p0 cSpec stSq.1 ∧
      TableBuilderCallSitesWidthSound spec) := by
  have hcost :
      ∀ n A B : ℕ,
        ((computablePaperMultiplyOfBitLength n A B).2 : ℝ) ≤
          8192 * (quantizedMultiplyOfBitLengthPaperStopSeries n A B).2 := by
    intro n A B
    unfold computablePaperMultiplyOfBitLength quantizedMultiplyOfBitLengthPaperStopSeries
    dsimp only
    set b := max 1 (Nat.log2 n)
    set k := n / b + 1
    set K0 := max 4 (Nat.log2 (2 * k) + 2)
    set L := Nat.log2 (K0 - 1)
    set p0 := rootPrecision b K0
    set spec := buildQuantizedSpecPaperStop L p0 K0
    have hK0_ge4 : 4 ≤ K0 := le_max_left 4 (Nat.log2 (2 * k) + 2)
    have hp0 : 8 ≤ p0 := by dsimp [p0, rootPrecision]; omega
    have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
      have hlt : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
      omega
    have hvalid : spec.Valid := buildQuantizedSpecPaperStop_valid L p0 K0 hp0
    have hexec : spec.PaperExecutableValid :=
      buildQuantizedSpecPaperStop_paperExecutableValid L p0 K0 hp0 hK0_le_2L1
    have hsize : spec.size = 2 ^ K0 := buildQuantizedSpecPaperStop_size L p0 K0
    have hspec_p : spec.p = p0 := buildQuantizedSpecPaperStop_p L p0 K0
    have hk : k + k ≤ 2 ^ K0 := by
      have hlt := lt_two_pow_log2_succ (2 * k)
      have hle_exp : Nat.log2 (2 * k) + 1 ≤ K0 := by
        have : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
        omega
      have hpow_le : 2 ^ (Nat.log2 (2 * k) + 1) ≤ 2 ^ K0 :=
        Nat.pow_le_pow_right zero_lt_two hle_exp
      omega
    exact computablePaperFastDFTMultiplyWithTables_snd_le spec hvalid hexec b K0 k k A B hsize hspec_p hk
  refine ⟨?_, hcost, ?_, ?_, ?_⟩
  · intro n A B hA hB
    unfold computablePaperMultiplyOfBitLength
    dsimp only
    set b := max 1 (Nat.log2 n)
    set k := n / b + 1
    set K0 := max 4 (Nat.log2 (2 * k) + 2)
    set L := Nat.log2 (K0 - 1)
    set p0 := rootPrecision b K0
    set spec := buildQuantizedSpecPaperStop L p0 K0
    have hb_pos : 1 ≤ b := le_max_left 1 (Nat.log2 n)
    have hK0_ge4 : 4 ≤ K0 := le_max_left 4 (Nat.log2 (2 * k) + 2)
    have hp0 : 8 ≤ p0 := by dsimp [p0, rootPrecision]; omega
    have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
      have hlt : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
      omega
    have hvalid : spec.Valid := buildQuantizedSpecPaperStop_valid L p0 K0 hp0
    have hexec : spec.PaperExecutableValid :=
      buildQuantizedSpecPaperStop_paperExecutableValid L p0 K0 hp0 hK0_le_2L1
    have hfaith : TablesFaithful (buildComputablePaperTablesWithProgramCost spec).1 spec :=
      buildComputablePaperTablesWithProgramCost_faithful spec hvalid hexec
    have hsize : spec.size = 2 ^ K0 := buildQuantizedSpecPaperStop_size L p0 K0
    have hspec_p : spec.p = p0 := buildQuantizedSpecPaperStop_p L p0 K0
    have hk : k + k ≤ 2 ^ K0 := by
      have hlt := lt_two_pow_log2_succ (2 * k)
      have hle_exp : Nat.log2 (2 * k) + 1 ≤ K0 := by
        have : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
        omega
      have hpow_le : 2 ^ (Nat.log2 (2 * k) + 1) ≤ 2 ^ K0 :=
        Nat.pow_le_pow_right zero_lt_two hle_exp
      omega
    have hbk : n ≤ b * k := by
      dsimp [k]
      have hdiv := Nat.div_add_mod n b
      have hmod : n % b < b := Nat.mod_lt n (by omega)
      have hmul : b * (n / b + 1) = b * (n / b) + b := by ring
      omega
    have hpow_bk : 2 ^ n ≤ (2 ^ b) ^ k := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right zero_lt_two hbk
    change computablePaperFastDFTMultiply (buildComputablePaperTablesWithProgramCost spec).1 b K0 k k A B = A * B
    exact computablePaperFastDFTMultiply_faithful_eq_mul spec hvalid
      (buildComputablePaperTablesWithProgramCost spec).1 hfaith b K0 k k hsize hspec_p hk
      A B (hA.trans_le hpow_bk) (hB.trans_le hpow_bk)
  · intro n A B hb256
    have hle1 := hcost n A B
    have hle2 := quantizedMultiplyOfBitLengthPaperStopSeries_snd_le_n_log_n_of_log2_ge_256 n A B hb256
    calc ((computablePaperMultiplyOfBitLength n A B).2 : ℝ)
        ≤ 8192 * (quantizedMultiplyOfBitLengthPaperStopSeries n A B).2 := hle1
      _ ≤ 8192 * ((7879984640 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hle2 (by positivity)
      _ = (64552834170880 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by ring
  · intro A B
    rw [Asymptotics.isBigO_iff]
    set E : ℕ := 256
    have hE : E = 256 := rfl
    have hE_ge1 : 1 ≤ E := by decide
    clear_value E
    refine ⟨(64552834170880 : ℝ), Filter.eventually_atTop.mpr ⟨2 ^ E, fun n hn => ?_⟩⟩
    have hpos : 0 < 2 ^ E := pow_pos zero_lt_two E
    have hn_ne : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le hpos hn)
    have hbE : E ≤ Nat.log2 n := (Nat.le_log2 hn_ne).mpr hn
    have hb256 : 256 ≤ Nat.log2 n := hE ▸ hbE
    have hle1 := hcost n (A n) (B n)
    have hle2 := quantizedMultiplyOfBitLengthPaperStopSeries_snd_le_n_log_n_of_log2_ge_256 n (A n) (B n) hb256
    have hnonneg : (0 : ℝ) ≤ ((computablePaperMultiplyOfBitLength n (A n) (B n)).2 : ℝ) :=
      Nat.cast_nonneg _
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by
      have h2_le_n : 2 ^ 1 ≤ n := (Nat.le_log2 hn_ne).mp (hE_ge1.trans hbE)
      exact_mod_cast h2_le_n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hrhs_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg (by positivity) hlog_nonneg
    rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hrhs_nonneg]
    calc ((computablePaperMultiplyOfBitLength n (A n) (B n)).2 : ℝ)
        ≤ 8192 * (quantizedMultiplyOfBitLengthPaperStopSeries n (A n) (B n)).2 := hle1
      _ ≤ 8192 * ((7879984640 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hle2 (by positivity)
      _ = (64552834170880 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by ring
  · intro n A B
    dsimp only
    set b := max 1 (Nat.log2 n)
    set k := n / b + 1
    set K0 := max 4 (Nat.log2 (2 * k) + 2)
    set L := Nat.log2 (K0 - 1)
    set p0 := rootPrecision b K0
    set spec := buildQuantizedSpecPaperStop L p0 K0
    have hK0_ge4 : 4 ≤ K0 := le_max_left 4 (Nat.log2 (2 * k) + 2)
    have hp0 : 8 ≤ p0 := by dsimp [p0, rootPrecision]; omega
    have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
      have hlt : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
      omega
    have hvalid : spec.Valid := buildQuantizedSpecPaperStop_valid L p0 K0 hp0
    have hexec : spec.PaperExecutableValid :=
      buildQuantizedSpecPaperStop_paperExecutableValid L p0 K0 hp0 hK0_le_2L1
    have hfaith : TablesFaithful (buildComputablePaperTablesWithProgramCost spec).1 spec :=
      buildComputablePaperTablesWithProgramCost_faithful spec hvalid hexec
    have hsize : spec.size = 2 ^ K0 := buildQuantizedSpecPaperStop_size L p0 K0
    have hspec_p : spec.p = p0 := buildQuantizedSpecPaperStop_p L p0 K0
    have hroot_ws := programCost_root_pipeline_widths_sound_of_faithful spec hvalid
      (buildComputablePaperTablesWithProgramCost spec).1 hfaith b K0 k k A B hsize hspec_p
    exact ⟨hroot_ws.1, hroot_ws.2.1, hroot_ws.2.2, tableBuilder_widths_sound spec hvalid⟩

-- Executable Smoke Test 1 (`#eval`) for `computablePaperMultiplyOfBitLength` (leaf level):
/-- info: (63, 815105780) -/
#guard_msgs in
#eval computablePaperMultiplyOfBitLength 4 7 9

attribute [irreducible] computablePaperMultiplyOfBitLength

/-- Theorem-level smoke test confirming `(computablePaperMultiplyOfBitLength 4 7 9).1 = 63`. -/
theorem computablePaperMultiplyOfBitLength_smoke_test :
    (computablePaperMultiplyOfBitLength 4 7 9).1 = 63 := by
  have h := computablePaperMultiplyOfBitLength_correct_and_isBigO.1 4 7 9 (by decide) (by decide)
  exact h

/-- Concrete `.step` specification (`K0 = 2`, `t1 = 2`, `r = 2`, `p0 = rootPrecision 1 2 = 12`,
`p' = pChild 12 2 = 28`, `p_work = pWork 12 2 = 20`, `pSub = 56`) exercising all four table families
(`T1`–`T4`) and the full `.step` spread, pre-twist, synthetic FFT, child leaf FFT, odd-stride routing,
passband bidiagonal/Nyquist solvers, and post-transpose pipeline. -/
def computableStepSmokeSpec : QuantizedFastDFTSpec :=
  let p0 := rootPrecision 1 2
  quantizedBoxGaussianStepSpec p0 2 (.base (pChild p0 2) 2)

/-- 100% computable multiplier executing `buildComputablePaperTablesWithProgramCost` and
`computablePaperFastDFTMultiplyWithProgramCost` on a given `spec : QuantizedFastDFTSpec`. -/
def computableStepSmokeMultiplyGivenSpec
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ × ℕ :=
  let cSpecRes := buildComputablePaperTablesWithProgramCost spec
  let mulRes := computablePaperFastDFTMultiplyWithProgramCost cSpecRes.1 b K0 k1 k2 A B
  (mulRes.1, mulRes.2 + cSpecRes.2)

/-- Exact correctness and table-builder width soundness for `computableStepSmokeMultiplyGivenSpec`
over any valid, executable `spec : QuantizedFastDFTSpec`. -/
theorem computableStepSmokeMultiplyGivenSpec_correct
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (b K0 k1 k2 : ℕ) (hsize : spec.size = 2 ^ K0) (hp : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    (computableStepSmokeMultiplyGivenSpec spec b K0 k1 k2 A B).1 = A * B ∧
    TableBuilderCallSitesWidthSound spec := by
  have hfaith : TablesFaithful (buildComputablePaperTablesWithProgramCost spec).1 spec :=
    buildComputablePaperTablesWithProgramCost_faithful spec hvalid hexec
  refine ⟨?_, tableBuilder_widths_sound spec hvalid⟩
  unfold computableStepSmokeMultiplyGivenSpec
  dsimp only
  change computablePaperFastDFTMultiply (buildComputablePaperTablesWithProgramCost spec).1 b K0 k1 k2 A B = A * B
  exact computablePaperFastDFTMultiply_faithful_eq_mul spec hvalid
    (buildComputablePaperTablesWithProgramCost spec).1 hfaith b K0 k1 k2 hsize hp hk A B hA hB

attribute [irreducible] computableStepSmokeMultiplyGivenSpec

/-- 100% computable `.step`-level multiplier executing `buildComputablePaperTablesWithProgramCost`
and `computablePaperFastDFTMultiplyWithProgramCost` on `computableStepSmokeSpec`. -/
abbrev computableStepSmokeMultiply (A B : ℕ) : ℕ × ℕ :=
  computableStepSmokeMultiplyGivenSpec computableStepSmokeSpec 1 2 2 2 A B

-- Executable Smoke Test 2 (`#eval`) for `computableStepSmokeMultiply` (`.step` + `.basePow2` two-level pipeline):
-- Exercises `buildComputablePaperTablesWithProgramCost` (`T1`–`T4` series evaluators) and
-- `computablePaperFastDFTMultiplyWithProgramCost` on a genuine `.step` node in the Lean VM.
/-- info: (6, 2855326743294) -/
#guard_msgs in
#eval computableStepSmokeMultiply 2 3

/-- Exact correctness and table-builder width soundness theorem for `computableStepSmokeMultiply`. -/
theorem computableStepSmokeMultiply_correct (A B : ℕ) (hA : A < 4) (hB : B < 4) :
    (computableStepSmokeMultiplyGivenSpec computableStepSmokeSpec 1 2 2 2 A B).1 = A * B ∧
    TableBuilderCallSitesWidthSound computableStepSmokeSpec := by
  have hp0 : 8 ≤ rootPrecision 1 2 := by decide
  have hp' : 8 ≤ pChild (rootPrecision 1 2) 2 := by decide
  have hvalid : computableStepSmokeSpec.Valid :=
    quantizedBoxGaussianStepSpec_valid (rootPrecision 1 2) 2 hp0 (by decide)
      (.base (pChild (rootPrecision 1 2) 2) 2) rfl rfl
      (QuantizedFastDFTSpec.Valid.base (pChild (rootPrecision 1 2) 2) 2)
  have hexec : computableStepSmokeSpec.PaperExecutableValid :=
    QuantizedFastDFTSpec.PaperExecutableValid.step
      (fun u2 u1 => routedOddStrideIndex_eq_oddStrideInvPow2 1 u2 u1)
      (QuantizedFastDFTSpec.PaperExecutableValid.base (p := pChild (rootPrecision 1 2) 2) (K := 1) hp' (by decide))
  have hA' : A < (2 ^ 1) ^ 2 := hA
  have hB' : B < (2 ^ 1) ^ 2 := hB
  exact computableStepSmokeMultiplyGivenSpec_correct
    computableStepSmokeSpec hvalid hexec 1 2 2 2 rfl rfl (by decide) A B hA' hB'

/-- Theorem-level `.step` smoke test confirming `(computableStepSmokeMultiply 2 3).1 = 6`. -/
theorem computableStepSmokeMultiply_smoke_test :
    (computableStepSmokeMultiplyGivenSpec computableStepSmokeSpec 1 2 2 2 2 3).1 = 6 := by
  have h := (computableStepSmokeMultiply_correct 2 3 (by decide) (by decide)).1
  exact h

/-- Verification that `buildQuantizedSpecPaperStop 1 8 9` takes the `.step` branch (`2 ^ 9 = 512 > 4 * 8 ^ 2 = 256`). -/
theorem buildQuantizedSpecPaperStop_one_eight_nine_eq_step :
    buildQuantizedSpecPaperStop 1 8 9 =
      quantizedBoxGaussianStepSpec 8 9 (.base 38 32) := rfl

/-- Single-row `.step` spread execution on any `QuantizedFastDFTSpec` (`computablePaperStopStepRowSpread`, `[MS]` §7.1):
when `spec` is a `.step p K t1 r c1 v1Of child` node (such as `buildQuantizedSpecPaperStop 1 8 9`,
where $2^9 = 512 > 4 \cdot 8^2 = 256$), constructs row `j1 = 0`'s modulo-`W_eff` folded Sinc-Gaussian
filter taps via `computablePiScaledWithCost`, `computableLog2ScaledWithCost`, and
`computableSincGaussianTapGivenPiLog2`, and executes `computableSpreadRowContiguousWithProgramCost`
(including balanced divide-and-conquer `polyMulKroneckerSignedTreeWithCost` and single-pass
`overlapAddBucketsSinglePassWithCost`) on an impulse row of length `r`. -/
def computablePaperStopStepRowSpread : QuantizedFastDFTSpec → (ℤ × ℤ) × ℕ
  | .base _ _ => ((0, 0), 0)
  | .step p K t1 r _c1 _v1Of _child =>
    let p' := pChild p K
    let p_work := pWork p K
    let pSub := 2 * p'
    let W_eff := effectiveFilterWidth pSub r
    let B_tap := pSub + 2
    let M_θ_tap := 4 * (pSub + 1)
    let N_tap := 4 * M_θ_tap + B_tap + 4
    let B_c_tap := B_tap + N_tap + 3 * M_θ_tap + 6
    let piTapRes := computablePiScaledWithCost B_c_tap
    let log2TapRes := computableLog2ScaledWithCost B_c_tap
    let rawScan := runSequentialScanCostedSteps
      (fun s => computableSincGaussianTapGivenPiLog2 p_work pSub t1 piTapRes log2TapRes 0 s)
      (2 * pSub + 1)
    let folded : List ℤ :=
      (List.range W_eff).map (fun u =>
        ∑ s ∈ (Finset.range (2 * pSub + 1)).filter (fun s => s % W_eff = u),
          read1D rawScan.1 s)
    let foldCost : ℕ := (2 * pSub + 1) * addBitCost (4 * p')
    let tapCost : ℕ := rawScan.2.2 + rawScan.2.1 * addBitCost (4 * p') + foldCost
    let xRow : Array (ℤ × ℤ) :=
      Array.ofFn (fun i : Fin r => if i.val = 0 then (((2 ^ p : ℕ) : ℤ), 0) else (0, 0))
    let spreadRes := computableSpreadRowContiguousWithProgramCost p pSub p' pSub r folded xRow
    (read1D spreadRes.1 0, tapCost + spreadRes.2)

/-- Executable Smoke Test 3 (`computablePaperStopStepRowSmoke`):
executes `computablePaperStopStepRowSpread` on `buildQuantizedSpecPaperStop 1 8 9`
(an actual `PaperStop` `.step` node where $2^9 = 512 > 4 \cdot 8^2 = 256$, so `t1 = 16`, `r = 32`,
`p' = 38`, `pSub = 76`). -/
def computablePaperStopStepRowSmoke : (ℤ × ℤ) × ℕ :=
  computablePaperStopStepRowSpread (buildQuantizedSpecPaperStop 1 8 9)

/-- info: ((1427247692705959881058285969449495136382746624, 0), 3346445172156) -/
#guard_msgs in
#eval computablePaperStopStepRowSmoke

/-- Verification that the pinned output `1427247692705959881058285969449495136382746624` of
`computablePaperStopStepRowSmoke` equals the exact scaled center tap `2 ^ (2 * pSub - 2) = (2 : ℤ) ^ 150`
for `pSub = 76` (`sincGaussian α 0 = 1` quantized at `2 ^ 76` multiplied by the impulse `2 ^ 74`). -/
theorem computablePaperStopStepRowSmoke_expected_eq :
    (1427247692705959881058285969449495136382746624 : ℤ) = (2 : ℤ) ^ 150 := by
  decide

/-- Executable Smoke Test 4 (`computablePaperStopStepRow1CenterTap`):
evaluates the non-trivial fractional-shiftSinc-Gaussian tap `j1 = 1, s = 76`
($x = -1/16 \notin \mathbb{Z}$, exercising the full fixed-point `π`, `ln 2`, Taylor `sin`, and
`exp` series) on the `PaperStop` `.step` node `buildQuantizedSpecPaperStop 1 8 9`
(`p_work = 23`, `pSub = 76`, `t1 = 16`). -/
def computablePaperStopStepRow1CenterTap : BitCostM ℤ :=
  computableSincGaussianTapWithProgramCost 23 76 16 1 76

/-- info: (75027926561319384437867, 30738054260) -/
#guard_msgs in
#eval computablePaperStopStepRow1CenterTap

/-- Formal 1-ULP accuracy certificate for `computablePaperStopStepRow1CenterTap` against the
mathematical `sincGaussian (alphaSchedule 23) (-1 / 16)` kernel at scale `2 ^ 76`. -/
theorem computablePaperStopStepRow1CenterTap_spec :
    |((computablePaperStopStepRow1CenterTap.1 : ℝ) / (2 : ℝ) ^ 76) -
      sincGaussian (alphaSchedule 23) (-(1 : ℝ) / (16 : ℝ))| ≤
      (2 : ℝ) ^ (-(76 : ℤ)) ∧
    computablePaperStopStepRow1CenterTap.1.natAbs ≤ 2 ^ 76 + 1 := by
  simpa [computablePaperStopStepRow1CenterTap, neg_div] using
    computableSincGaussianTapWithProgramCost_spec 23 76 16 1 76
      (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Exhaustive `.step`-level multiplication smoke test across all 16 input pairs `A, B ∈ {0, 1, 2, 3}`
on `computableStepSmokeSpec`, compiling the `.step` table hierarchy once via
`buildComputablePaperTablesWithProgramCost` and verifying
`(computablePaperFastDFTMultiplyWithProgramCost cSpec 1 2 2 2 A B).1 == A * B` for every pair. -/
def computableStepSmokeAllPairsExact : Bool × ℕ :=
  let cSpecRes := buildComputablePaperTablesWithProgramCost computableStepSmokeSpec
  let allOk := (List.range 4).all (fun A =>
    (List.range 4).all (fun B =>
      (computablePaperFastDFTMultiplyWithProgramCost cSpecRes.1 1 2 2 2 A B).1 == A * B))
  let sample3x3 := computablePaperFastDFTMultiplyWithProgramCost cSpecRes.1 1 2 2 2 3 3
  (allOk && (sample3x3.1 == 9), sample3x3.2 + cSpecRes.2)

/-- info: (true, 2855326737948) -/
#guard_msgs in
#eval computableStepSmokeAllPairsExact

/-- **`PaperStop` `.step`-Branch Schedule Unfolding & Exactness Corollary
(`computablePaperMultiplyOfBitLength_paperStop_step_exact`, `[MS]` §7)**:
At bit-length `n = 65536` (`b = 16`, `k = 4097`, `K0 = 15`, `L = 3`, `p0 = rootPrecision 16 15 = 68`),
the first (`rfl`) conjunct proves by kernel reduction that the paper's adaptive stopping schedule
`buildQuantizedSpecPaperStop 3 68 15` genuinely takes the `.step` branch
(`2 ^ 15 = 32768 > 4 * 68 ^ 2 = 18496`, stepping with `t1 = 128`, `r = 256` to the leaf
`.base 110 256`), and the remaining conjuncts instantiate the general theorem
`computablePaperMultiplyOfBitLength_correct_and_isBigO.1` at `n = 65536` as a theorem-level
exactness corollary (confirming `(computablePaperMultiplyOfBitLength 65536 A B).1 = A * B` for all
`A, B < 2 ^ 65536`, including `(computablePaperMultiplyOfBitLength 65536 1234567 7654321).1 = 9449772114007`,
without `#eval`-executing the 65536-bit pipeline in the VM). -/
theorem computablePaperMultiplyOfBitLength_paperStop_step_exact :
    buildQuantizedSpecPaperStop (Nat.log2 (15 - 1)) (rootPrecision 16 15) 15 =
      quantizedBoxGaussianStepSpec 68 15 (.base 110 256) ∧
    (∀ A B : ℕ, A < 2 ^ 65536 → B < 2 ^ 65536 →
      (computablePaperMultiplyOfBitLength 65536 A B).1 = A * B) ∧
    (computablePaperMultiplyOfBitLength 65536 1234567 7654321).1 = 9449772114007 := by
  refine ⟨rfl, fun A B hA hB =>
    computablePaperMultiplyOfBitLength_correct_and_isBigO.1 65536 A B hA hB, ?_⟩
  have hpow : 2 ^ 24 ≤ 2 ^ 65536 := Nat.pow_le_pow_right (by decide) (by decide)
  have hA : 1234567 < 2 ^ 65536 := lt_of_lt_of_le (by decide : 1234567 < 2 ^ 24) hpow
  have hB : 7654321 < 2 ^ 65536 := lt_of_lt_of_le (by decide : 7654321 < 2 ^ 24) hpow
  exact computablePaperMultiplyOfBitLength_correct_and_isBigO.1 65536 1234567 7654321 hA hB

end IntMul
