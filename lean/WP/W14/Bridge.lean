import WP.W14.Faithful
import WP.W14.Pipeline

/-!
# W14 (4/11): parametric semantics and the integer-to-complex bridge

* `sincGaussianFastDFTOfTablesAt qL`: the snapshot's table semantics (FTP:1251) with the leaf internal
  grid `qL p K` (the snapshot hard-codes `2 * p + K + 8`, FTP:251).
* `toScaledComplex_computablePaperFastDFTAt_eq`: the parametric integer pipeline computes, exactly, the
  parametric semantics under `TablesFaithfulAt S` (copy of FTP:1288–1497; only structural facts are used).
-/

namespace WP.W14

open IntMul Complex Real

attribute [local instance 10000] instZeroIntElementary

/-- Leaf semantics at an explicit internal grid (FTP:249 with `q_leaf` a parameter). -/
noncomputable def baseRadix2FFTOfTwiddlesAt
    (q_leaf p K : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (x : ℕ → ℂ) (u : ℕ) : ℂ :=
  complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u)

/-- **Schedule-parametric semantics** (FTP:1251 with the leaf grid `qL p K`). -/
noncomputable def sincGaussianFastDFTOfTablesAt (qL : ℕ → ℕ → ℕ) :
    ComputablePaperFastDFTSpec → (ℕ → ℂ) → ℕ → ℂ
  | .basePow2 p K twiddles, x, u =>
    baseRadix2FFTOfTwiddlesAt (qL p K) p K twiddles x u
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, x, u =>
    let U : ℕ → ℕ → ℂ := fun j1 k2 =>
      kroneckerSpreadOfFoldedTaps pSub m1 t1 r (filterTaps.getD j1 []) x j1 k2
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTOfTablesAt qL child (qPost v1) u2
    let v1Of : ℕ → ℕ → ℕ := fun u2 u1 =>
      oddStrideInvPow2 (Nat.log2 t1) u2 u1
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
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
    complexQuantize p z_sub

/-- The snapshot instance of the parametric semantics is the snapshot's semantics. -/
theorem sincGaussianFastDFTOfTablesAt_snapshot :
    sincGaussianFastDFTOfTablesAt snapshotQLeaf = sincGaussianFastDFTOfTables := by
  funext cSpec x u
  induction cSpec generalizing x u with
  | basePow2 p K twiddles => rfl
  | step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child ih =>
    simp only [sincGaussianFastDFTOfTablesAt, sincGaussianFastDFTOfTables, ih]

/-- Leaf bridge at an explicit internal grid (FTP:317 with `q_leaf` a parameter). -/
theorem toScaledComplex_computableBaseRadix2FFTAt_eq
    (q_leaf p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < 2 ^ K, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < 2 ^ K) :
    toScaledComplex p (read1D (computableBaseRadix2FFTAt q_leaf p_in p K twiddles xArr).1 u) =
      baseRadix2FFTOfTwiddlesAt q_leaf p K twiddles x u := by
  unfold computableBaseRadix2FFTAt baseRadix2FFTOfTwiddlesAt
  dsimp only [costedGRescale, runSequentialScanCostedSteps, Bind.bind, Pure.pure, BitCostM.tick]
  rw [read1D_runSequentialScanSteps_eq _ (2 ^ K) u hu,
      toScaledComplex_gRescale_eq,
      toScaledComplex_computableBaseRadix2FFTCoreWithProgramCost_eq_ofTwiddles p_in q_leaf
        twiddles K xArr x hx u hu]

set_option backward.dsimp.instances true in
/-- **Bridge.** Under `TablesFaithfulAt S`, the parametric integer pipeline computes the parametric
semantics exactly (FTP:1288 with the schedule `S`). -/
theorem toScaledComplex_computablePaperFastDFTAt_eq (S : StepSchedule)
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithfulAt S cSpec spec)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < spec.size) :
    toScaledComplex spec.p
      (read1D (computablePaperFastDFTValAt S.qLeaf p_in cSpec xArr) u) =
      sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x u := by
  unfold computablePaperFastDFTValAt
  induction hvalid generalizing cSpec p_in xArr x u with
  | base p R =>
    cases hfaith with
    | @base p K twiddles hp hK_le htw =>
      dsimp only [computablePaperFastDFTAt, sincGaussianFastDFTOfTablesAt,
        QuantizedFastDFTSpec.p]
      dsimp only [QuantizedFastDFTSpec.size] at hx hu
      exact toScaledComplex_computableBaseRadix2FFTAt_eq (S.qLeaf p K) p_in p K twiddles xArr x hx u hu
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hfaith with
    | @step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      dsimp only [sincGaussianFastDFTOfTablesAt, QuantizedFastDFTSpec.p]
      dsimp only [QuantizedFastDFTSpec.size] at hx hu
      obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
      obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
      dsimp only [computablePaperFastDFTAt, runScan2DCostedWithSteps,
        runSequentialScanCostedSteps, costedGPreTwistU, costedGRescale, costedGMulScaled]
      set pSub := S.pSub p K
      set m1 := S.m1 p K
      set p' := pSub / 2
      set m_t1 := natLog2Fuel t1 t1
      set m_r := natLog2Fuel r r
      have hm_t1 : m_t1 = Nat.log2 t1 := natLog2Fuel_self t1
      have hm_r : m_r = Nat.log2 r := natLog2Fuel_self r
      set xRoutedRes := runMultiTapeTransposeFullSteps m_t1 r (read1D xArr)
      set xRows_res :=
        runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
      set xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
      have hxRow_eq : ∀ j1 < t1, ∀ i < r,
          x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i) := by
        intro j1 hj1 i hi
        dsimp only [xRows, xRows_res, xRoutedRes]
        have hj1_m : j1 < 2 ^ m_t1 := by rw [hm_t1]; exact ht1_pow.symm ▸ hj1
        rw [read1D_array_getD_eq_read2D,
            read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi,
            runMultiTapeTransposeFullSteps_fst,
            read1D_runMultiTapeTranspose_index_eq m_t1 r hr (read1D xArr) j1 i hj1_m hi,
            hm_t1, ht1_pow]
        have hidx_lt : j1 + t1 * i < t1 * r := by
          have hi_le : i + 1 ≤ r := hi
          calc j1 + t1 * i < t1 + t1 * i := Nat.add_lt_add_right hj1 _
            _ = t1 * (i + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hi_le
        have hcomm : i * t1 + j1 = j1 + t1 * i := by ring
        rw [hcomm, hx (j1 + t1 * i) hidx_lt]
      set U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun j1 : Fin t1 =>
          computableSpreadRowContiguousWithProgramCost p_in pSub p' m1 r
            (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
      set U_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
      set P_res :=
        runScan2DWithSteps t1 r (fun j1 k2 =>
          gPreTwistU pSub (read1D preTwiddles k2) (read2D U_mat j1 k2))
      set P_mat : Array (Array (ℤ × ℤ)) := P_res.1
      set syn_res := computableSyntheticFFTRadix2WithProgramCost p' t1 r m_t1 (r / t1) P_mat
      set Q_res :=
        runScan2DWithSteps t1 r (fun v1 k2 =>
          gRescale pSub pSub (read2D syn_res.1 v1 k2))
      set Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
      set qPost_res :=
        runScan2DWithSteps t1 r (fun v1 k2 =>
          gMulScaled (pSub + 2) (read1D postTwiddles k2) (read2D Q_mat v1 k2))
      set qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
      set qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun v1 : Fin t1 =>
          computablePaperFastDFTAt S.qLeaf pSub cChild (qPost_mat.getD v1.val #[]))
      set qHat_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
      set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
      set qHat_T_res := runMultiTapeTransposeFullSteps m_r t1 (read1D stFlatQ.outTape)
      set colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          runMultiTapeAffineOddRouteFullSteps m_t1
            (computableOddStrideFactor m_t1 u2.val) 0
            (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
      set Y_res :=
        runScan2DWithSteps r t1 (fun u2 u1 =>
          let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
          gRescale cChild.p pSub (read1D colArr u1))
      set Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
      set alt_q : ℤ × ℤ :=
        (computableNyquistAltSumContiguousWithProgramCost p_in pSub p' r (xRows.getD (t1 / 2) #[])).1
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
      set Z_flat_res := runMultiTapeTransposeFullSteps m_t1 r (read1D stFlatZ.outTape)
      rw [read1D_runSequentialScanSteps_eq _ (t1 * r) u hu, toScaledComplex_gRescale_eq]
      apply congrArg (complexQuantize p)
      set U : ℕ → ℕ → ℂ := fun j1 k2 =>
        kroneckerSpreadOfFoldedTaps pSub m1 t1 r (filterTaps.getD j1 []) x j1 k2
      set P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
      set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
      set qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTOfTablesAt S.qLeaf cChild (qPost v1) u2
      set v1Of' : ℕ → ℕ → ℕ := fun u2 u1 =>
        oddStrideInvPow2 (Nat.log2 t1) u2 u1
      set Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of' u2 u1) u2)
      have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r,
          toScaledComplex pSub ((P_mat.getD j1 #[]).getD k2 (0, 0)) = P j1 k2 := by
        intro j1 hj1 k2 hk2
        have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
        rw [array_getD_getD_eq_read2D_pair]
        dsimp only [P_mat, P_res, P]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2]
        have hU_row : read2D U_mat j1 k2 =
            read1D (computableSpreadRowContiguousWithCost p_in pSub m1 r
              (filterTaps.getD j1 []) (xRows.getD j1 #[])).1 k2 := by
          dsimp only [U_mat, U_rows]
          rw [read2D_ofFn_of_lt t1 _ hj1_t1 k2]
          simp only [Array.size_ofFn, hj1_t1, ↓reduceDIte, Array.getElem_ofFn,
            computableSpreadRowContiguousWithProgramCost_fst]
        rw [hU_row]
        exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2) _ (U j1 k2)
          (computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps
            p_in pSub m1 t1 r (filterTaps.getD j1 []) (xRows.getD j1 #[]) x j1 k2
            (hxRow_eq j1 hj1_t1) hk2).symm
      have hQ_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D Q_mat v1 k2) = Q v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [Q_mat, Q_res, Q, syn_res]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize pSub)
        have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
          rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
        rw [computableSyntheticFFTRadix2WithProgramCost_fst, hm_t1,
            ← array_getD_getD_eq_read2D_pair _ v1 k2,
            toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow
              P_mat v1 k2 (ht1_pow.symm ▸ hv1) hk2]
        exact syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P hP_eq v1 k2 hk2
      have hqPost_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [qPost_mat, qPost_res, qPost]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
      have hqHat_eq : ∀ v1 < t1, ∀ u2 < r,
          toScaledComplex child.p (read2D qHat_mat v1 u2) = qHat v1 u2 := by
        intro v1 hv1 u2 hu2
        dsimp only [qHat_mat, qHat_res, qHat]
        rw [read2D_ofFn_of_lt t1 _ hv1 u2]
        simp only [Array.size_ofFn, hv1, ↓reduceDIte, Array.getElem_ofFn]
        exact ih cChild hchild_faith pSub (qPost_mat.getD v1 #[]) (qPost v1)
          (fun k hk => by
            have hk_r : k < r := hchild_size ▸ hk
            rw [read1D_array_getD_eq_read2D]
            exact (hqPost_eq v1 hv1 k hk_r).symm)
          u2 (hchild_size.symm ▸ hu2)
      have hY_eq : ∀ u2 < r, ∀ u1 < t1,
          toScaledComplex pSub (read2D Y_mat u2 u1) = Y u2 u1 := by
        intro u2 hu2 u1 hu1
        dsimp only [Y_mat, Y_res, colRoutes, qHat_T_res, stFlatQ, Y, v1Of']
        rw [read2D_runScan2DWithSteps_of_lt r t1 _ hu2 hu1]
        simp only [Array.size_ofFn, hu2, ↓reduceDIte, Array.getElem_ofFn, toScaledComplex_gRescale_eq]
        have hu1_m : u1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hu1
        have hv1_t1 : oddStrideInvPow2 (Nat.log2 t1) u2 u1 < t1 := by
          rw [← hv1_eq u2 u1]; exact hv1_lt u2 hu2 u1 hu1
        have hcChild_p : cChild.p = child.p := hchild_faith.p_eq
        rw [runMultiTapeAffineOddRouteFullSteps_fst, computableOddStrideFactor_eq_oddStrideFactor, hm_t1,
            read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq (Nat.log2 t1) u2 u1 _ hu1_m,
            runMultiTapeTransposeFullSteps_fst, hm_r,
            read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 r) r t1 hr_pow ht1 qHat_mat u2
              (oddStrideInvPow2 (Nat.log2 t1) u2 u1) hu2 hv1_t1,
            hcChild_p, hqHat_eq _ hv1_t1 u2 hu2]
      have hu2_lt : u % r < r := Nat.mod_lt u hr
      have hu1_lt : u / r < t1 := by rw [Nat.div_lt_iff_lt_mul hr]; linarith
      have hu_decomp : (u / r) * r + u % r = u := by rw [mul_comm, Nat.div_add_mod]
      have hZ_flat : read1D Z_flat_res.1 u = read2D Z_cols_mat (u % r) (u / r) := by
        dsimp only [Z_flat_res, stFlatZ]
        rw [runMultiTapeTransposeFullSteps_fst, hm_t1]
        conv_lhs => rw [← hu_decomp]
        exact read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 t1) t1 r ht1_pow hr Z_cols_mat
          (u / r) (u % r) hu1_lt hu2_lt
      rw [hZ_flat]
      have halt_eq : toScaledComplex pSub alt_q = complexQuantize pSub (nyquistAltSum t1 r x) := by
        dsimp only [alt_q]
        rw [computableNyquistAltSumContiguousWithProgramCost_fst]
        have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
        exact toScaledComplex_computableNyquistAltSumContiguous_eq p_in pSub t1 r hr
          (xRows.getD (t1 / 2) #[]) x (hxRow_eq (t1 / 2) hhalf_lt)
      exact toScaledComplex_Z_cols_paper_step_eq pSub p' t1 r c0Table c1Table Y_mat alt_q
        (toScaledComplex pSub (read1D c0Table (u % r)))
        (toScaledComplex pSub (read1D c1Table (u % r)))
        (complexQuantize pSub (nyquistAltSum t1 r x))
        (Y (u % r)) (u % r) (u / r) hu2_lt hu1_lt rfl rfl halt_eq
        (fun k hk => hY_eq (u % r) hu2_lt k hk)

#assert_std_axioms sincGaussianFastDFTOfTablesAt_snapshot toScaledComplex_computableBaseRadix2FFTAt_eq
  toScaledComplex_computablePaperFastDFTAt_eq

end WP.W14
