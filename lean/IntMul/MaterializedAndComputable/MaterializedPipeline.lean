import IntMul.MaterializedAndComputable.SequentialTransducers

/-!
# Part 2 — End-to-End Materialized `Array` FastDFT & Multiplier Pipeline with Annotated Runtime Cost
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-- **Runtime-Cost-Instrumented Materialized Multi-Level Sinc-Gaussian `FastDFT` (`sincGaussianFastDFTMaterializedWithCost`, `[MS]` §7)**:
Executes the materialized array transform while accumulating its runtime bit-operation and tape-head-step
cost bottom-up directly from the executed array operations and state-machine `.steps` counters:
1. Transposes the input array `xArr` into row-contiguous layout via `runMultiTapeTransposeWithSteps (Nat.log2 t1) r`
   (`xRoutedRes.2` head steps accumulated from `stU.steps` and `stI.steps`) and slices it into `t1`
   contiguous rows `xRows` via `runScan2DWithSteps` (`xRows_res.2` steps) so both the spread and
   `nyquistAltSumContiguous` read contiguous length-`r` rows with zero stride-`t1` random access,
2. Computes `U_rows` via `kroneckerSincGaussianSpreadRowContiguousWithCost` on each contiguous row and
   sums the per-block Kronecker multiplication/addition costs via `sumArrayCosts U_rows`,
3. Executes the pre-twist scan `P_res` (`P_res.2` steps), `syntheticFFTRadix2MaterializedWithCost` (`syn_res.2`),
   the post-Synthetic-FFT quantization scan `Q_res` (`Q_res.2` steps), and the post-twist scan `qPost_res`
   (`qPost_res.2` steps),
4. Runs the recursive child transforms `sincGaussianFastDFTMaterializedWithCost child` and sums their
   returned runtime costs over `v1 < t1`,
5. Flattens `qHat_mat` sequentially via `runFlatten2DSteps` (`stFlatQ.steps`), transposes via
   `runMultiTapeTransposeWithSteps` (`qHat_T_res.2`), routes columns via `routeMaterializedColumnWithSteps`
   (`oddRouteSteps = sumArrayCosts colRoutes`), and quantizes the routed columns via `runScan2DWithSteps` (`Y_res.2`),
6. Runs the step-instrumented column solvers `solveBidiagonalFwdMaterializedWithSteps`,
   `solveNyquistMaterializedWithSteps`, and `solveBidiagonalBwdMaterializedWithSteps` (using
   `runBwdRevSteps` and `runReverseSteps`) and accumulates `solverSteps = sumArrayCosts Z_cols_res`,
7. Flattens `Z_cols_mat` sequentially via `runFlatten2DSteps` (`stFlatZ.steps`), transposes via
   `runMultiTapeTransposeWithSteps` (`Z_flat_res.2`), and quantizes the output via `runSequentialScanSteps` (`outScan.steps`). -/
noncomputable def sincGaussianFastDFTMaterializedWithCost :
    QuantizedFastDFTSpec → Array ℂ → Array ℂ × ℝ
  | .base p R, xArr =>
    let rowScans : Array (ℂ × ℕ) := Array.ofFn (fun u : Fin R =>
      let st := runSequentialScanSteps (fun j =>
        read1D xArr j * stdChar (((j * u.val : ℕ) : ℝ) / (R : ℝ))) R
      (complexQuantize p (dft1D R (read1D xArr) u.val), st.steps * addBitCost p))
    (Array.ofFn (fun u : Fin R => (if h : u.val < rowScans.size then rowScans[u.val].1 else 0)),
     ((sumArrayCosts rowScans : ℕ) : ℝ))
  | .step p K t1 r _c1 v1Of child, xArr =>
    let α := alphaSchedule (pWork p K)
    let p' := pChild p K
    let pSub := 2 * p'
    let xRoutedRes := runMultiTapeTransposeWithSteps (Nat.log2 t1) r (read1D xArr)
    let useRouted : Bool := (2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r) && (0 < r)
    let xRows_res :=
      runScan2DWithSteps t1 r (fun j1 i =>
        if useRouted then
          read1D xRoutedRes.1 (j1 * r + i)
        else
          read1D xArr (j1 + t1 * i))
    let xRows : Array (Array ℂ) := xRows_res.1
    let U_rows : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        kroneckerSincGaussianSpreadRowContiguousWithCost α pSub (2 * p') t1 r
          (read1D (xRows.getD j1.val #[])) j1.val)
    let U_mat : Array (Array ℂ) :=
      Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
    let P_res :=
      runScan2DWithSteps t1 r (fun j1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * read2D U_mat j1 k2))
    let P_mat : Array (Array ℂ) := P_res.1
    let syn_res :=
      syntheticFFTRadix2MaterializedWithCost pSub p' t1 r (Nat.log2 t1) (r / t1) (read2D P_mat)
    let Q_res :=
      runScan2DWithSteps t1 r (fun v1 k2 => complexQuantize pSub (read2D syn_res.1 v1 k2))
    let Q_mat : Array (Array ℂ) := Q_res.1
    let qPost_res :=
      runScan2DWithSteps t1 r (fun v1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * read2D Q_mat v1 k2))
    let qPost_mat : Array (Array ℂ) := qPost_res.1
    let qHat_res : Array (Array ℂ × ℝ) :=
      Array.ofFn (fun v1 : Fin t1 =>
        sincGaussianFastDFTMaterializedWithCost child (qPost_mat.getD v1.val #[]))
    let qHat_mat : Array (Array ℂ) :=
      Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
    let childCostSum : ℝ :=
      ∑ v1 ∈ Finset.range t1, if h : v1 < qHat_res.size then qHat_res[v1].2 else 0
    let stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
    let qHat_T_res := runMultiTapeTransposeWithSteps (Nat.log2 r) t1 (read1D stFlatQ.outTape)
    let colRoutes : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        routeMaterializedColumnWithSteps t1 t1 v1Of qHat_T_res.1 u2.val)
    let Y_res :=
      runScan2DWithSteps r t1 (fun u2 u1 =>
        let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
        complexQuantize pSub (read1D colArr u1))
    let Y_mat : Array (Array ℂ) := Y_res.1
    let xMidRow : ℕ → ℂ :=
      if useRouted ∧ 0 < t1 then
        read1D (xRows.getD (t1 / 2) #[])
      else
        fun j2 => read1D xArr (t1 / 2 + t1 * j2)
    let alt_q : ℂ := complexQuantize pSub (nyquistAltSumContiguous r xMidRow)
    let Z_cols_res : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        let y := (u2.val : ℝ) / (r : ℝ)
        let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
        let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
        if 2 * u2.val < r then
          solveBidiagonalFwdMaterializedWithSteps pSub t1 c0 c1_pass (read2D Y_mat u2.val)
        else if 2 * u2.val = r then
          solveNyquistMaterializedWithSteps pSub t1 c0 (read2D Y_mat u2.val) alt_q
        else
          solveBidiagonalBwdMaterializedWithSteps pSub t1 c0 c1_pass (read2D Y_mat u2.val))
    let Z_cols_mat : Array (Array ℂ) :=
      Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
    let stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
    let Z_flat_res := runMultiTapeTransposeWithSteps (Nat.log2 t1) r (read1D stFlatZ.outTape)
    let outScan := runSequentialScanSteps (fun u => complexQuantize p (read1D Z_flat_res.1 u)) (t1 * r)
    let spreadCost : ℕ := sumArrayCosts U_rows
    let solverSteps : ℕ := sumArrayCosts Z_cols_res
    let twistAndSolverCost : ℕ :=
      solverSteps * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))
    let oddRouteSteps : ℕ := sumArrayCosts colRoutes
    let linearScanSteps : ℕ :=
      xRows_res.2 + P_res.2 + Q_res.2 + qPost_res.2 +
        stFlatQ.steps + Y_res.2 + stFlatZ.steps + outScan.steps
    let routingSteps : ℕ :=
      if useRouted then
        xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + oddRouteSteps + linearScanSteps
      else
        2 * (2 * Nat.log2 t1) * (t1 * r) + (2 * Nat.log2 r) * (r * t1) +
          (2 * Nat.log2 t1) * (t1 * r) + 8 * (t1 * r)
    let routingCost : ℕ := routingSteps * addBitCost (8 * p')
    (outScan.outTape,
     ((syn_res.2 : ℕ) : ℝ) + ((spreadCost : ℕ) : ℝ) +
       ((twistAndSolverCost : ℕ) : ℝ) + ((routingCost : ℕ) : ℝ) + childCostSum)

/-- **Materialized Multi-Level Sinc-Gaussian `FastDFT` (`sincGaussianFastDFTMaterialized`, `[MS]` §7)**:
First projection of `sincGaussianFastDFTMaterializedWithCost`. -/
noncomputable def sincGaussianFastDFTMaterialized
    (spec : QuantizedFastDFTSpec) (xArr : Array ℂ) : Array ℂ :=
  (sincGaussianFastDFTMaterializedWithCost spec xArr).1

/-- Backward solver wrapper (`solveBidiagonalBwdMaterialized`) using `solveBidiagonalBwdMaterializedWithSteps`. -/
noncomputable def solveBidiagonalBwdMaterialized
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : Array ℂ :=
  (solveBidiagonalBwdMaterializedWithSteps q t1 c0 c1 Y).1

theorem read1D_solveBidiagonalBwdMaterialized_eq
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    read1D (solveBidiagonalBwdMaterialized q t1 c0 c1 Y) u1 =
      solveBidiagonalBwdQuantized q t1 c0 c1 Y u1 :=
  read1D_solveBidiagonalBwdMaterializedWithSteps_eq q t1 c0 c1 Y u1 hu1

/-- **Exact Pointwise Equivalence of `sincGaussianFastDFTMaterialized` and `sincGaussianFastDFTQuantized`**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`), any materialized
input `xArr : Array ℂ` and functional input `x : ℕ → ℂ` agreeing on `0 .. spec.size - 1`, and any
output frequency index `u < spec.size`,
`read1D (sincGaussianFastDFTMaterialized spec xArr) u = sincGaussianFastDFTQuantized spec x u`. -/
theorem read1D_sincGaussianFastDFTMaterialized_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (xArr : Array ℂ) (x : ℕ → ℂ) (hx : ∀ k < spec.size, read1D xArr k = x k)
    (u : ℕ) (hu : u < spec.size) :
    read1D (sincGaussianFastDFTMaterialized spec xArr) u =
      sincGaussianFastDFTQuantized spec x u := by
  unfold sincGaussianFastDFTMaterialized
  induction hvalid generalizing xArr x u with
  | base p R =>
    dsimp only [sincGaussianFastDFTMaterializedWithCost, sincGaussianFastDFTQuantized]
    dsimp only [QuantizedFastDFTSpec.size] at hx hu
    rw [read1D_ofFn_of_lt R _ hu]
    simp only [Array.size_ofFn, hu, ↓reduceDIte, Array.getElem_ofFn,
      dft1D_congr_lt R (read1D xArr) x hx u]
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    dsimp only [sincGaussianFastDFTMaterializedWithCost, sincGaussianFastDFTQuantized]
    dsimp only [QuantizedFastDFTSpec.size] at hx hu
    rw [read1D_runSequentialScanSteps_eq _ (t1 * r) u hu]
    congr 1
    obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
    set α := alphaSchedule (pWork p K)
    set p' := pChild p K
    set pSub := 2 * p'
    have huse : (((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true := by
      simp [ht1_pow, hr_pow, hr]
    set xRoutedRes := runMultiTapeTransposeWithSteps (Nat.log2 t1) r (read1D xArr)
    set xRows_res :=
      runScan2DWithSteps t1 r (fun j1 i =>
        if (((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true then
          read1D xRoutedRes.1 (j1 * r + i)
        else
          read1D xArr (j1 + t1 * i))
    set xRows : Array (Array ℂ) := xRows_res.1
    have hxRow_eq : ∀ j1 < t1, ∀ i < r,
        read1D (xRows.getD j1 #[]) i = x (j1 + t1 * i) := by
      intro j1 hj1 i hi
      dsimp only [xRows, xRows_res]
      rw [read1D_array_getD_eq_read2D, read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi, if_pos huse]
      dsimp only [xRoutedRes]
      have hj1_m : j1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hj1
      rw [runMultiTapeTransposeWithSteps_fst,
          read1D_runMultiTapeTranspose_index_eq (Nat.log2 t1) r hr (read1D xArr) j1 i hj1_m hi,
          ht1_pow]
      have hidx_lt : i * t1 + j1 < t1 * r := by
        have hi_le : i + 1 ≤ r := hi
        calc i * t1 + j1 < i * t1 + t1 := Nat.add_lt_add_left hj1 _
          _ = t1 * (i + 1) := by ring
          _ ≤ t1 * r := Nat.mul_le_mul_left t1 hi_le
      have hcomm : i * t1 + j1 = j1 + t1 * i := by ring
      rw [hcomm, hx (j1 + t1 * i) (hcomm ▸ hidx_lt)]
    set U_rows : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        kroneckerSincGaussianSpreadRowContiguousWithCost α pSub (2 * p') t1 r
          (read1D (xRows.getD j1.val #[])) j1.val)
    set U_mat : Array (Array ℂ) :=
      Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
    set P_res :=
      runScan2DWithSteps t1 r (fun j1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * read2D U_mat j1 k2))
    set P_mat := P_res.1
    set syn_res := syntheticFFTRadix2MaterializedWithCost pSub p' t1 r (Nat.log2 t1) (r / t1) (read2D P_mat)
    set Q_res := runScan2DWithSteps t1 r (fun v1 k2 => complexQuantize pSub (read2D syn_res.1 v1 k2))
    set Q_mat := Q_res.1
    set qPost_res :=
      runScan2DWithSteps t1 r (fun v1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * read2D Q_mat v1 k2))
    set qPost_mat := qPost_res.1
    set qHat_res : Array (Array ℂ × ℝ) :=
      Array.ofFn (fun v1 : Fin t1 =>
        sincGaussianFastDFTMaterializedWithCost child (qPost_mat.getD v1.val #[]))
    set qHat_mat : Array (Array ℂ) :=
      Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
    set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
    set qHat_T_res := runMultiTapeTransposeWithSteps (Nat.log2 r) t1 (read1D stFlatQ.outTape)
    set colRoutes : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        routeMaterializedColumnWithSteps t1 t1 v1Of qHat_T_res.1 u2.val)
    set Y_res :=
      runScan2DWithSteps r t1 (fun u2 u1 =>
        let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
        complexQuantize pSub (read1D colArr u1))
    set Y_mat : Array (Array ℂ) := Y_res.1
    set xMidRow : ℕ → ℂ :=
      if ((((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true) ∧ 0 < t1 then
        read1D (xRows.getD (t1 / 2) #[])
      else
        fun j2 => read1D xArr (t1 / 2 + t1 * j2)
    set alt_q : ℂ := complexQuantize pSub (nyquistAltSumContiguous r xMidRow)
    set Z_cols_res : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        let y := (u2.val : ℝ) / (r : ℝ)
        let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
        let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
        if 2 * u2.val < r then
          solveBidiagonalFwdMaterializedWithSteps pSub t1 c0 c1_pass (read2D Y_mat u2.val)
        else if 2 * u2.val = r then
          solveNyquistMaterializedWithSteps pSub t1 c0 (read2D Y_mat u2.val) alt_q
        else
          solveBidiagonalBwdMaterializedWithSteps pSub t1 c0 c1_pass (read2D Y_mat u2.val))
    set Z_cols_mat : Array (Array ℂ) :=
      Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
    set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
    set Z_flat_res := runMultiTapeTransposeWithSteps (Nat.log2 t1) r (read1D stFlatZ.outTape)
    set U := kroneckerSincGaussianSpreadArray α pSub (2 * p') t1 r x
    set P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    set qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTQuantized child (qPost v1) u2
    set Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
    have hU_eq : ∀ j1 < t1, ∀ k2 < r, read2D U_mat j1 k2 = U j1 k2 := by
      intro j1 hj1 k2 hk2
      dsimp only [U_mat, U_rows, U]
      rw [read2D_ofFn_of_lt t1 _ hj1 k2]
      simp only [Array.size_ofFn, hj1, ↓reduceDIte, Array.getElem_ofFn]
      exact read1D_kroneckerSincGaussianSpreadRowContiguousWithCost_eq α pSub (2 * p') t1 r
        (read1D (xRows.getD j1 #[])) x j1 k2 (hxRow_eq j1 hj1) hk2
    have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r, read2D P_mat j1 k2 = P j1 k2 := by
      intro j1 hj1 k2 hk2
      have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
      dsimp only [P_mat, P_res, P]
      rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2, hU_eq j1 hj1_t1 k2 hk2]
    have hc1_div : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
      rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
    have hQ_eq : ∀ v1 < t1, ∀ k2 < r, read2D Q_mat v1 k2 = Q v1 k2 := by
      intro v1 hv1 k2 hk2
      dsimp only [Q_mat, Q_res, Q, syn_res]
      rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
          syntheticFFTRadix2MaterializedWithCost_fst,
          read2D_syntheticFFTRadix2Materialized_eq pSub t1 r (Nat.log2 t1) (r / t1) hr hc1_div
            (read2D P_mat) P hP_eq v1 k2 (ht1_pow.symm ▸ hv1) hk2]
    have hqPost_eq : ∀ v1 < t1, ∀ k2 < r, read2D qPost_mat v1 k2 = qPost v1 k2 := by
      intro v1 hv1 k2 hk2
      dsimp only [qPost_mat, qPost_res, qPost]
      rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2, hQ_eq v1 hv1 k2 hk2]
    have hqHat_eq : ∀ v1 < t1, ∀ u2 < r, read2D qHat_mat v1 u2 = qHat v1 u2 := by
      intro v1 hv1 u2 hu2
      dsimp only [qHat_mat, qHat_res, qHat]
      rw [read2D_ofFn_of_lt t1 _ hv1 u2]
      simp only [Array.size_ofFn, hv1, ↓reduceDIte, Array.getElem_ofFn]
      exact ih (qPost_mat.getD v1 #[]) (qPost v1)
        (fun k hk => by
          have hk_r : k < r := hchild_size ▸ hk
          rw [read1D_array_getD_eq_read2D]
          exact hqPost_eq v1 hv1 k hk_r)
        u2 (hchild_size.symm ▸ hu2)
    have hY_eq : ∀ u2 < r, ∀ u1 < t1, read2D Y_mat u2 u1 = Y u2 u1 := by
      intro u2 hu2 u1 hu1
      dsimp only [Y_mat, Y_res, colRoutes, qHat_T_res, Y]
      have hv1_t1 : v1Of u2 u1 < t1 := hv1_lt u2 hu2 u1 hu1
      rw [read2D_runScan2DWithSteps_of_lt r t1 _ hu2 hu1]
      simp only [Array.size_ofFn, hu2, ↓reduceDIte, Array.getElem_ofFn]
      rw [read1D_routeMaterializedColumnWithSteps_eq t1 t1 v1Of _ u2 u1 hu1,
          runMultiTapeTransposeWithSteps_fst,
          read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 r) r t1 hr_pow ht1 qHat_mat
            u2 (v1Of u2 u1) hu2 hv1_t1,
          hqHat_eq (v1Of u2 u1) hv1_t1 u2 hu2]
    have hu2_lt : u % r < r := Nat.mod_lt u hr
    have hu1_lt : u / r < t1 := by
      rw [Nat.div_lt_iff_lt_mul hr]
      linarith
    have hu_split : (u / r) * r + u % r = u := by
      rw [mul_comm, Nat.div_add_mod]
    dsimp only [Z_flat_res]
    rw [runMultiTapeTransposeWithSteps_fst]
    conv_lhs => rw [← hu_split]
    rw [read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 t1) t1 r ht1_pow hr Z_cols_mat
          (u / r) (u % r) hu1_lt hu2_lt]
    dsimp only [Z_cols_mat, Z_cols_res]
    rw [read2D_ofFn_of_lt r _ hu2_lt (u / r)]
    simp only [Array.size_ofFn, hu2_lt, ↓reduceDIte, Array.getElem_ofFn]
    split_ifs with h1 h2
    · rw [read1D_solveBidiagonalFwdMaterializedWithSteps_eq pSub t1 _ _ _ (u / r) hu1_lt]
      exact solveBidiagonalFwdQuantized_congr_lt pSub t1 _ _
        (read2D Y_mat (u % r)) (Y (u % r)) (fun k hk => hY_eq (u % r) hu2_lt k hk) (u / r) hu1_lt
    · dsimp only [alt_q, xMidRow]
      have hmid_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
      have halt_eq : nyquistAltSumContiguous r
          (if ((((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true) ∧ 0 < t1 then
            read1D (xRows.getD (t1 / 2) #[])
          else
            fun j2 => read1D xArr (t1 / 2 + t1 * j2)) = nyquistAltSum t1 r x := by
        rw [if_pos ⟨huse, ht1⟩]
        exact nyquistAltSumContiguous_eq t1 r _ x (hxRow_eq (t1 / 2) hmid_lt)
      rw [read1D_solveNyquistMaterializedWithSteps_eq pSub t1 _ _ _ (u / r) hu1_lt, halt_eq]
      exact solveNyquistQuantized_congr_lt pSub t1 _
        (read2D Y_mat (u % r)) (Y (u % r)) _ (fun k hk => hY_eq (u % r) hu2_lt k hk) (u / r) hu1_lt
    · rw [read1D_solveBidiagonalBwdMaterializedWithSteps_eq pSub t1 _ _ _ (u / r) hu1_lt]
      exact solveBidiagonalBwdQuantized_congr_lt pSub t1 _ _
        (read2D Y_mat (u % r)) (Y (u % r)) (fun k hk => hY_eq (u % r) hu2_lt k hk) (u / r) hu1_lt

/-- **Exact Runtime Cost Equivalence of `sincGaussianFastDFTMaterializedWithCost` and `sincGaussianFastDFTQuantizedIntrinsicCost` (`[MS]` §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) and any
`xArr : Array ℂ` and `x : ℕ → ℂ` agreeing on `0 .. spec.size - 1`, the bottom-up runtime cost
`(sincGaussianFastDFTMaterializedWithCost spec xArr).2` accumulated directly from the materialized
array passes and `.steps`-instrumented multitape machines equals
`(sincGaussianFastDFTQuantizedIntrinsicCost spec x).2`. -/
theorem sincGaussianFastDFTMaterializedWithCost_snd_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (xArr : Array ℂ) (x : ℕ → ℂ) (hx : ∀ k < spec.size, read1D xArr k = x k) :
    (sincGaussianFastDFTMaterializedWithCost spec xArr).2 =
      (sincGaussianFastDFTQuantizedIntrinsicCost spec x).2 := by
  induction hvalid generalizing xArr x with
  | base p R =>
    dsimp only [sincGaussianFastDFTMaterializedWithCost, sincGaussianFastDFTQuantizedIntrinsicCost]
    have hbase :
        sumArrayCosts
          (Array.ofFn (fun u : Fin R =>
            let st := runSequentialScanSteps (fun j =>
              read1D xArr j * stdChar (((j * u.val : ℕ) : ℝ) / (R : ℝ))) R
            (complexQuantize p (dft1D R (read1D xArr) u.val), st.steps * addBitCost p))) =
          R * (R * addBitCost p) := by
      refine sumArrayCosts_ofFn_const R _ (R * addBitCost p) (fun u _ => ?_)
      simp [runSequentialScanSteps_steps]
    rw [hbase]
    push_cast
    ring
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    dsimp only [sincGaussianFastDFTMaterializedWithCost, sincGaussianFastDFTQuantizedIntrinsicCost]
    dsimp only [QuantizedFastDFTSpec.size] at hx
    obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
    set α := alphaSchedule (pWork p K)
    set p' := pChild p K
    set pSub := 2 * p'
    have huse : (((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true := by
      simp [ht1_pow, hr_pow, hr]
    set xRoutedRes := runMultiTapeTransposeWithSteps (Nat.log2 t1) r (read1D xArr)
    set xRows_res :=
      runScan2DWithSteps t1 r (fun j1 i =>
        if (((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true then
          read1D xRoutedRes.1 (j1 * r + i)
        else
          read1D xArr (j1 + t1 * i))
    set xRows : Array (Array ℂ) := xRows_res.1
    have hxRow_eq : ∀ j1 < t1, ∀ i < r,
        read1D (xRows.getD j1 #[]) i = routedInputGather t1 r x (j1 + t1 * i) := by
      intro j1 hj1 i hi
      rw [routedInputGather_eq]
      dsimp only [xRows, xRows_res]
      rw [read1D_array_getD_eq_read2D, read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi, if_pos huse]
      dsimp only [xRoutedRes]
      have hj1_m : j1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hj1
      rw [runMultiTapeTransposeWithSteps_fst,
          read1D_runMultiTapeTranspose_index_eq (Nat.log2 t1) r hr (read1D xArr) j1 i hj1_m hi,
          ht1_pow]
      have hidx_lt : i * t1 + j1 < t1 * r := by
        have hi_le : i + 1 ≤ r := hi
        calc i * t1 + j1 < i * t1 + t1 := Nat.add_lt_add_left hj1 _
          _ = t1 * (i + 1) := by ring
          _ ≤ t1 * r := Nat.mul_le_mul_left t1 hi_le
      have hcomm : i * t1 + j1 = j1 + t1 * i := by ring
      rw [hcomm, hx (j1 + t1 * i) (hcomm ▸ hidx_lt)]
    set U_rows : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        kroneckerSincGaussianSpreadRowContiguousWithCost α pSub (2 * p') t1 r
          (read1D (xRows.getD j1.val #[])) j1.val)
    set U_mat : Array (Array ℂ) :=
      Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
    set P_res :=
      runScan2DWithSteps t1 r (fun j1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * read2D U_mat j1 k2))
    set P_mat := P_res.1
    set syn_res := syntheticFFTRadix2MaterializedWithCost pSub p' t1 r (Nat.log2 t1) (r / t1) (read2D P_mat)
    set Q_res := runScan2DWithSteps t1 r (fun v1 k2 => complexQuantize pSub (read2D syn_res.1 v1 k2))
    set Q_mat := Q_res.1
    set qPost_res :=
      runScan2DWithSteps t1 r (fun v1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * read2D Q_mat v1 k2))
    set qPost_mat := qPost_res.1
    set qHat_res : Array (Array ℂ × ℝ) :=
      Array.ofFn (fun v1 : Fin t1 =>
        sincGaussianFastDFTMaterializedWithCost child (qPost_mat.getD v1.val #[]))
    set qHat_mat : Array (Array ℂ) :=
      Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
    set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
    set qHat_T_res := runMultiTapeTransposeWithSteps (Nat.log2 r) t1 (read1D stFlatQ.outTape)
    set colRoutes : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        routeMaterializedColumnWithSteps t1 t1 v1Of qHat_T_res.1 u2.val)
    set Y_res :=
      runScan2DWithSteps r t1 (fun u2 u1 =>
        let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
        complexQuantize pSub (read1D colArr u1))
    set Y_mat : Array (Array ℂ) := Y_res.1
    set xMidRow : ℕ → ℂ :=
      if ((((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true) ∧ 0 < t1 then
        read1D (xRows.getD (t1 / 2) #[])
      else
        fun j2 => read1D xArr (t1 / 2 + t1 * j2)
    set alt_q : ℂ := complexQuantize pSub (nyquistAltSumContiguous r xMidRow)
    set Z_cols_res : Array (Array ℂ × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        let y := (u2.val : ℝ) / (r : ℝ)
        let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
        let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
        if 2 * u2.val < r then
          solveBidiagonalFwdMaterializedWithSteps pSub t1 c0 c1_pass (read2D Y_mat u2.val)
        else if 2 * u2.val = r then
          solveNyquistMaterializedWithSteps pSub t1 c0 (read2D Y_mat u2.val) alt_q
        else
          solveBidiagonalBwdMaterializedWithSteps pSub t1 c0 c1_pass (read2D Y_mat u2.val))
    set Z_cols_mat : Array (Array ℂ) :=
      Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
    set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
    set Z_flat_res := runMultiTapeTransposeWithSteps (Nat.log2 t1) r (read1D stFlatZ.outTape)
    set outScan := runSequentialScanSteps (fun u => complexQuantize p (read1D Z_flat_res.1 u)) (t1 * r)
    set U := kroneckerSincGaussianSpreadArray α pSub (2 * p') t1 r (routedInputGather t1 r x)
    set P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    have hU_eq : ∀ j1 < t1, ∀ k2 < r, read2D U_mat j1 k2 = U j1 k2 := by
      intro j1 hj1 k2 hk2
      dsimp only [U_mat, U_rows, U]
      rw [read2D_ofFn_of_lt t1 _ hj1 k2]
      simp only [Array.size_ofFn, hj1, ↓reduceDIte, Array.getElem_ofFn]
      exact read1D_kroneckerSincGaussianSpreadRowContiguousWithCost_eq α pSub (2 * p') t1 r
        (read1D (xRows.getD j1 #[])) (routedInputGather t1 r x) j1 k2 (hxRow_eq j1 hj1) hk2
    have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r, read2D P_mat j1 k2 = P j1 k2 := by
      intro j1 hj1 k2 hk2
      have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
      dsimp only [P_mat, P_res, P]
      rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2, hU_eq j1 hj1_t1 k2 hk2]
    have hc1_div : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
      rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
    have hQ_eq : ∀ v1 < t1, ∀ k2 < r, read2D Q_mat v1 k2 = Q v1 k2 := by
      intro v1 hv1 k2 hk2
      dsimp only [Q_mat, Q_res, Q, syn_res]
      rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
          syntheticFFTRadix2MaterializedWithCost_fst,
          read2D_syntheticFFTRadix2Materialized_eq pSub t1 r (Nat.log2 t1) (r / t1) hr hc1_div
            (read2D P_mat) P hP_eq v1 k2 (ht1_pow.symm ▸ hv1) hk2]
    have hqPost_eq : ∀ v1 < t1, ∀ k2 < r, read2D qPost_mat v1 k2 = qPost v1 k2 := by
      intro v1 hv1 k2 hk2
      dsimp only [qPost_mat, qPost_res, qPost]
      rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2, hQ_eq v1 hv1 k2 hk2]
    have hsyn_cost : syn_res.2 = syntheticFFTStepBitCost t1 r p' := by
      dsimp only [syn_res, syntheticFFTStepBitCost]
      rw [syntheticFFTRadix2MaterializedWithCost_snd]
    have hspread_cost : sumArrayCosts U_rows =
        executedKroneckerSpreadStepBitCost α p K t1 r (routedInputGather t1 r x) := by
      dsimp only [U_rows, executedKroneckerSpreadStepBitCost]
      refine sumArrayCosts_ofFn_eq_sum t1 _ _ (fun j1 hj1 => ?_)
      exact kroneckerSincGaussianSpreadRowContiguousWithCost_snd_eq α pSub (2 * p') t1 r
        (read1D (xRows.getD j1 #[])) (routedInputGather t1 r x) j1
        (hxRow_eq j1 hj1)
    have hsolver_steps : sumArrayCosts Z_cols_res = t1 * r := by
      dsimp only [Z_cols_res]
      rw [mul_comm t1 r]
      refine sumArrayCosts_ofFn_const r _ t1 (fun u2 _ => ?_)
      dsimp only
      split_ifs <;> simp
    have hodd_steps : sumArrayCosts colRoutes = (2 * Nat.log2 t1) * (t1 * r) := by
      dsimp only [colRoutes]
      have h0 :
          sumArrayCosts
            (Array.ofFn (fun u2 : Fin r =>
              routeMaterializedColumnWithSteps t1 t1 v1Of qHat_T_res.1 u2.val)) =
            r * ((2 * Nat.log2 t1) * 2 ^ (Nat.log2 t1)) := by
        refine sumArrayCosts_ofFn_const r _ _ (fun u2 _ => ?_)
        simp
      rw [h0, ht1_pow]
      ring
    have hrouting_cost :
        (if (((2 ^ (Nat.log2 t1) == t1) && (2 ^ (Nat.log2 r) == r)) && (0 < r)) = true then
          xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
            (xRows_res.2 + P_res.2 + Q_res.2 + qPost_res.2 +
              stFlatQ.steps + Y_res.2 + stFlatZ.steps + outScan.steps)
        else
          2 * (2 * Nat.log2 t1) * (t1 * r) + (2 * Nat.log2 r) * (r * t1) +
            (2 * Nat.log2 t1) * (t1 * r) + 8 * (t1 * r)) *
          addBitCost (8 * p') =
        routingAndStreamingStepBitCost t1 r p' := by
      rw [if_pos huse]
      dsimp only [xRoutedRes, qHat_T_res, Z_flat_res, xRows_res, P_res, Q_res, qPost_res,
        stFlatQ, Y_res, stFlatZ, outScan]
      rw [runMultiTapeTransposeWithSteps_snd, runMultiTapeTransposeWithSteps_snd,
          runMultiTapeTransposeWithSteps_snd, hodd_steps,
          runScan2DWithSteps_snd, runScan2DWithSteps_snd,
          runScan2DWithSteps_snd, runScan2DWithSteps_snd,
          runFlatten2DSteps_steps, runScan2DWithSteps_snd,
          runFlatten2DSteps_steps, runSequentialScanSteps_steps,
          ht1_pow, hr_pow]
      unfold routingAndStreamingStepBitCost sequentialTransposeBitCost
        sequentialColumnMergeSortBitCost sequentialLinearScanBitCost sequentialPassBitCost
      rw [sequentialTapeTransposeWithPasses_snd, sequentialTapeTransposeWithPasses_snd,
          sequentialAffineOddRouteWithPasses_snd]
      ring
    have hchild_sum :
        (∑ v1 ∈ Finset.range t1,
          if h : v1 < qHat_res.size then qHat_res[v1].2 else 0) =
        ∑ v1 ∈ Finset.range t1,
          (sincGaussianFastDFTQuantizedIntrinsicCost child (qPost v1)).2 := by
      dsimp only [qHat_res]
      refine Finset.sum_congr rfl fun v1 hv1_mem => ?_
      have hv1_t1 : v1 < t1 := Finset.mem_range.mp hv1_mem
      simp only [Array.size_ofFn, hv1_t1, ↓reduceDIte, Array.getElem_ofFn]
      exact ih (qPost_mat.getD v1 #[]) (qPost v1)
        (fun k hk => by
          have hk_r : k < r := hchild_size ▸ hk
          rw [read1D_array_getD_eq_read2D]
          exact hqPost_eq v1 hv1_t1 k hk_r)
    rw [hsyn_cost, hspread_cost, hsolver_steps, hrouting_cost, hchild_sum]
    rfl

/-- Materializes the raw Sinc-Gaussian window taps and the 4 twiddle/passband arrays (`zetaRoot r k2`,
`zetaRoot r (-k2)`, `c0Coeff`, `c1Coeff`) across all levels of a `QuantizedFastDFTSpec` using
`runSequentialScanSteps`, accumulating the annotated series-evaluation and tap-folding bit-operation
cost directly from the `.steps` counters of the executed scan machines. -/
noncomputable def materializeSpecRawTablesWithCost : QuantizedFastDFTSpec → Array (Array ℝ) × ℝ
  | .base _ _ => (#[], 0)
  | .step p K t1 r _c1 _v1Of child =>
    let p' := pChild p K
    let α := alphaSchedule (pWork p K)
    let rawCount := t1 * (4 * p' + 1)
    let stRawTaps := runSequentialScanSteps (fun idx =>
      let j1 := idx / (4 * p' + 1)
      let m : ℤ := ((idx % (4 * p' + 1) : ℕ) : ℤ) - (2 * p' : ℤ)
      sincGaussian α ((m : ℝ) + (j1 : ℝ) / (t1 : ℝ))) rawCount
    let stPre := runSequentialScanSteps (fun k2 => zetaRoot r (k2 : ℝ)) r
    let stPost := runSequentialScanSteps (fun k2 => zetaRoot r (-(k2 : ℝ))) r
    let stC0 := runSequentialScanSteps (fun u2 => c0Coeff (realErfScaled α) ((u2 : ℝ) / (r : ℝ))) r
    let stC1 := runSequentialScanSteps (fun u2 => c1Coeff (realErfScaled α) ((u2 : ℝ) / (r : ℝ))) r
    let twiddleSteps := stPre.steps + stPost.steps + stC0.steps + stC1.steps
    let childTables := materializeSpecRawTablesWithCost child
    let stepCost : ℕ :=
      (stRawTaps.steps + twiddleSteps) * (4 * p' + 1) *
        (mulBitCost (4 * p') + addBitCost (4 * p')) +
      stRawTaps.steps * addBitCost (4 * p')
    (childTables.1.push stRawTaps.outTape, ((stepCost : ℕ) : ℝ) + childTables.2)

@[simp]
theorem materializeSpecRawTablesWithCost_snd_eq (spec : QuantizedFastDFTSpec) :
    (materializeSpecRawTablesWithCost spec).2 = spec.precomputeRawTapCost := by
  induction spec with
  | base p R => rfl
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [materializeSpecRawTablesWithCost, QuantizedFastDFTSpec.precomputeRawTapCost,
      precomputeStepRawTapBitCost]
    simp only [runSequentialScanSteps_steps, ih]
    have h4r : r + r + r + r = 4 * r := by ring
    rw [h4r]

/-- **Runtime-Cost-Instrumented Materialized Integer Multiplication (`quantizedFastDFTMultiplyMaterializedWithCost`, `[MS]` §7)**:
Executes the materialized array multiplication pipeline while accumulating its total runtime bit-operation
and tape-head-step cost directly from:
- `stPack := runSequentialScanSteps (packNormalizedChunks b k1 k2 A B) R0` (`stPack.steps * addBitCost p0`),
- `fwd := sincGaussianFastDFTMaterializedWithCost spec stPack.outTape` (`fwd.2`),
- `stSq := runSequentialScanSteps ... R0` (`stSq.steps * mulBitCost p0`),
- `inv := sincGaussianFastDFTMaterializedWithCost spec stSq.outTape` (`inv.2`),
- `stExt := runSequentialScanSteps ... R0` (`2 * stExt.steps * addBitCost p0`),
- and `tableRes := materializeSpecRawTablesWithCost spec` (`tableRes.2`),
with **zero** reference to `sincGaussianFastDFTQuantizedIntrinsicCost` or `quantizedMultiplyOfBitLength`. -/
noncomputable def quantizedFastDFTMultiplyMaterializedWithCost
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ × ℝ :=
  let R0 := 2 ^ K0
  let p0 := rootPrecision b K0
  let stPack := runSequentialScanSteps (packNormalizedChunks b k1 k2 A B) R0
  let fwd := sincGaussianFastDFTMaterializedWithCost spec stPack.outTape
  let stSq := runSequentialScanSteps (fun u =>
    star (complexQuantize p0 ((read1D fwd.1 u) ^ 2))) R0
  let inv := sincGaussianFastDFTMaterializedWithCost spec stSq.outTape
  let stExt := runSequentialScanSteps (fun j =>
    let z_tilde : ℂ := star (read1D inv.1 j)
    let c_approx : ℝ := (z_tilde.im) * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)
    ⌊c_approx + (1 / 2 : ℝ)⌋.toNat) R0
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j => read1D stExt.outTape j)
  let tableRes := materializeSpecRawTablesWithCost spec
  let rootCost : ℕ :=
    stSq.steps * mulBitCost p0 + (stPack.steps + 2 * stExt.steps) * addBitCost p0
  (reconstructChunks b convNat,
   fwd.2 + inv.2 + tableRes.2 + ((rootCost : ℕ) : ℝ))

/-- **Materialized Multi-Level Sinc-Gaussian `FastDFT` Integer Multiplication (`quantizedFastDFTMultiplyMaterialized`, `[MS]` §7)**:
First projection of `quantizedFastDFTMultiplyMaterializedWithCost`. -/
noncomputable def quantizedFastDFTMultiplyMaterialized
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ :=
  (quantizedFastDFTMultiplyMaterializedWithCost spec b K0 k1 k2 A B).1

/-- `quantizedFastDFTMultiplyMaterialized` produces the exact same output as `quantizedFastDFTMultiply`. -/
theorem quantizedFastDFTMultiplyMaterialized_eq_quantizedFastDFTMultiply
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (b K0 k1 k2 A B : ℕ) (hsize : spec.size = 2 ^ K0) (hk : k1 + k2 ≤ 2 ^ K0) :
    quantizedFastDFTMultiplyMaterialized spec b K0 k1 k2 A B =
      quantizedFastDFTMultiply spec b K0 k1 k2 A B := by
  unfold quantizedFastDFTMultiplyMaterialized quantizedFastDFTMultiplyMaterializedWithCost
    quantizedFastDFTMultiply
  dsimp only
  congr 1
  refine List.map_congr_left fun j hj_mem => ?_
  have hj_lt : j < k1 + k2 := List.mem_range.mp hj_mem
  have hj_R0 : j < 2 ^ K0 := by omega
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set x_AB := packNormalizedChunks b k1 k2 A B
  set stPack := runSequentialScanSteps x_AB R0
  set fwd := sincGaussianFastDFTMaterializedWithCost spec stPack.outTape
  set stSq := runSequentialScanSteps (fun u => star (complexQuantize p0 ((read1D fwd.1 u) ^ 2))) R0
  set inv := sincGaussianFastDFTMaterializedWithCost spec stSq.outTape
  rw [read1D_runSequentialScanSteps_eq _ R0 j hj_R0]
  have hy : ∀ u < R0, read1D fwd.1 u = sincGaussianFastDFTQuantized spec x_AB u := by
    intro u hu
    exact read1D_sincGaussianFastDFTMaterialized_eq spec hvalid stPack.outTape x_AB
      (fun k hk => read1D_runSequentialScanSteps_eq x_AB R0 k (hsize ▸ hk)) u (hsize.symm ▸ hu)
  have hz : read1D inv.1 j =
      sincGaussianFastDFTQuantized spec
        (fun u => star (complexQuantize p0 ((sincGaussianFastDFTQuantized spec x_AB u) ^ 2))) j := by
    refine read1D_sincGaussianFastDFTMaterialized_eq spec hvalid stSq.outTape
      (fun u => star (complexQuantize p0 ((sincGaussianFastDFTQuantized spec x_AB u) ^ 2)))
      (fun u hu => ?_) j (hsize.symm ▸ hj_R0)
    have hu_R0 : u < R0 := hsize ▸ hu
    dsimp only [stSq]
    rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, hy u hu_R0]
  unfold quantizedFastDFTConvApprox
  dsimp only
  rw [hz]

/-- **Exact Runtime Cost Equivalence of `quantizedFastDFTMultiplyMaterializedWithCost` and `quantizedFastDFTMultiplyIntrinsicCost` (`[MS]` §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) with `spec.size = 2 ^ K0`,
the runtime cost `(quantizedFastDFTMultiplyMaterializedWithCost spec b K0 k1 k2 A B).2` accumulated
bottom-up from the materialized array program and its `.steps`-instrumented multitape machines equals
`(quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2`. -/
theorem quantizedFastDFTMultiplyMaterializedWithCost_snd_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (b K0 k1 k2 A B : ℕ) (hsize : spec.size = 2 ^ K0) :
    (quantizedFastDFTMultiplyMaterializedWithCost spec b K0 k1 k2 A B).2 =
      (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2 := by
  unfold quantizedFastDFTMultiplyMaterializedWithCost quantizedFastDFTMultiplyIntrinsicCost
  dsimp only
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set x_AB := packNormalizedChunks b k1 k2 A B
  set stPack := runSequentialScanSteps x_AB R0
  set fwd := sincGaussianFastDFTMaterializedWithCost spec stPack.outTape
  set stSq := runSequentialScanSteps (fun u => star (complexQuantize p0 ((read1D fwd.1 u) ^ 2))) R0
  set inv := sincGaussianFastDFTMaterializedWithCost spec stSq.outTape
  set stExt := runSequentialScanSteps (fun j =>
    let z_tilde : ℂ := star (read1D inv.1 j)
    let c_approx : ℝ := (z_tilde.im) * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)
    ⌊c_approx + (1 / 2 : ℝ)⌋.toNat) R0
  have hfwd_cost : fwd.2 = (sincGaussianFastDFTQuantizedIntrinsicCost spec x_AB).2 :=
    sincGaussianFastDFTMaterializedWithCost_snd_eq spec hvalid stPack.outTape x_AB
      (fun k hk => read1D_runSequentialScanSteps_eq x_AB R0 k (hsize ▸ hk))
  have hy : ∀ u < R0, read1D fwd.1 u = sincGaussianFastDFTQuantized spec x_AB u := by
    intro u hu
    exact read1D_sincGaussianFastDFTMaterialized_eq spec hvalid stPack.outTape x_AB
      (fun k hk => read1D_runSequentialScanSteps_eq x_AB R0 k (hsize ▸ hk)) u (hsize.symm ▸ hu)
  have hinv_cost :
      inv.2 =
        (sincGaussianFastDFTQuantizedIntrinsicCost spec
          (fun u => star (complexQuantize p0 (((sincGaussianFastDFTQuantizedIntrinsicCost spec x_AB).1 u) ^ 2)))).2 := by
    refine sincGaussianFastDFTMaterializedWithCost_snd_eq spec hvalid stSq.outTape _ (fun u hu => ?_)
    have hu_R0 : u < R0 := hsize ▸ hu
    dsimp only [stSq]
    rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, hy u hu_R0,
        sincGaussianFastDFTQuantizedIntrinsicCost_fst_eq]
  have hroot :
      stSq.steps * mulBitCost p0 + (stPack.steps + 2 * stExt.steps) * addBitCost p0 =
        rootPipelineBitCost R0 p0 := by
    dsimp only [stSq, stPack, stExt, rootPipelineBitCost]
    rw [runSequentialScanSteps_steps, runSequentialScanSteps_steps, runSequentialScanSteps_steps]
    ring
  rw [hfwd_cost, hinv_cost, materializeSpecRawTablesWithCost_snd_eq, hroot]

/-- **Master Correctness Theorem for Materialized `quantizedFastDFTMultiplyMaterialized` (`[MS]` §7)**:
For any valid multi-level specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) with
`spec.size = 2 ^ K0` and `spec.p = rootPrecision b K0`, any `k1 + k2 ≤ 2 ^ K0`, and any natural
numbers `A < (2 ^ b) ^ k1` and `B < (2 ^ b) ^ k2`, the materialized array pipeline
`quantizedFastDFTMultiplyMaterialized spec b K0 k1 k2 A B` equals the exact product `A * B`. -/
theorem quantizedFastDFTMultiplyMaterialized_eq_mul
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    quantizedFastDFTMultiplyMaterialized spec b K0 k1 k2 A B = A * B := by
  rw [quantizedFastDFTMultiplyMaterialized_eq_quantizedFastDFTMultiply spec hvalid b K0 k1 k2 A B hsize hk]
  exact quantizedFastDFTMultiply_eq_mul spec hvalid b K0 k1 k2 hsize hp0 hk A B hA hB

/-- **Parameter-Free Materialized Integer Multiplier with Execution-Accumulated Runtime Cost (`quantizedMultiplyOfBitLengthMaterialized`, `[MS]` §7)**:
Directly executes `quantizedFastDFTMultiplyMaterializedWithCost` on the parameter-free schedule
`buildQuantizedSpec L p0 K0`, returning `(product, runtimeCost)` where **both** the product `.1` and
the runtime cost `.2` are produced directly by the materialized array program and its `.steps`-instrumented
multitape state machines (with zero copying from `quantizedMultiplyOfBitLength`). -/
noncomputable def quantizedMultiplyOfBitLengthMaterialized (n A B : ℕ) : ℕ × ℝ :=
  let b := max 1 (Nat.log2 n)
  let k := n / b + 1
  let K0 := max 4 (Nat.log2 (2 * k) + 2)
  let L := Nat.log2 (K0 - 1)
  let p0 := rootPrecision b K0
  let spec := buildQuantizedSpec L p0 K0
  quantizedFastDFTMultiplyMaterializedWithCost spec b K0 k k A B

/-- **Exact Equivalence of `quantizedMultiplyOfBitLengthMaterialized` and `quantizedMultiplyOfBitLength`**:
Proves that both the product `.1` and the bottom-up runtime cost `.2` accumulated by
`quantizedMultiplyOfBitLengthMaterialized` equal `quantizedMultiplyOfBitLength n A B`. -/
theorem quantizedMultiplyOfBitLengthMaterialized_eq_quantizedMultiplyOfBitLength (n A B : ℕ) :
    quantizedMultiplyOfBitLengthMaterialized n A B = quantizedMultiplyOfBitLength n A B := by
  unfold quantizedMultiplyOfBitLengthMaterialized quantizedMultiplyOfBitLength
  dsimp only
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set spec := buildQuantizedSpec L p0 K0
  have hb_pos : 1 ≤ b := le_max_left 1 (Nat.log2 n)
  have hK0_ge4 : 4 ≤ K0 := le_max_left 4 (Nat.log2 (2 * k) + 2)
  have hp0 : 8 ≤ p0 := by dsimp [p0, rootPrecision]; omega
  have h2L_le_K0 : 2 ^ L ≤ K0 :=
    (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
  have hvalid : spec.Valid := buildQuantizedSpec_valid L p0 K0 hp0 h2L_le_K0
  have hsize : spec.size = 2 ^ K0 := buildQuantizedSpec_size L p0 K0
  have hk : k + k ≤ 2 ^ K0 := by
    have hlt := lt_two_pow_log2_succ (2 * k)
    have hle_exp : Nat.log2 (2 * k) + 1 ≤ K0 := by
      have : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
      omega
    have hpow_le : 2 ^ (Nat.log2 (2 * k) + 1) ≤ 2 ^ K0 :=
      Nat.pow_le_pow_right zero_lt_two hle_exp
    omega
  ext
  · change quantizedFastDFTMultiplyMaterialized spec b K0 k k A B =
      (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k k A B).1
    rw [quantizedFastDFTMultiplyMaterialized_eq_quantizedFastDFTMultiply spec hvalid b K0 k k A B hsize hk,
        ← quantizedFastDFTMultiplyIntrinsicCost_fst_eq spec b K0 k k A B]
  · exact quantizedFastDFTMultiplyMaterializedWithCost_snd_eq spec hvalid b K0 k k A B hsize

/-- **Master Correctness and `O(n log n)` Bit-Complexity Theorem for `quantizedMultiplyOfBitLengthMaterialized`**:
1. For all `n : ℕ` and `A, B < 2 ^ n`, `(quantizedMultiplyOfBitLengthMaterialized n A B).1 = A * B`.
2. For all `n` with `96 ≤ Nat.log2 n`, `(quantizedMultiplyOfBitLengthMaterialized n A B).2 ≤ 7840335360 * (n * log n)`.
3. For all `16 ≤ n`, `(quantizedMultiplyOfBitLengthMaterialized n A B).2 ≤ 54317320874319360 * (n * log n)`.
4. For any `A, B : ℕ → ℕ`, `(fun n => (quantizedMultiplyOfBitLengthMaterialized n (A n) (B n)).2) =O[atTop] (fun n => n * log n)`. -/
theorem quantizedMultiplyOfBitLengthMaterialized_correct_and_isBigO :
    (∀ n A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      (quantizedMultiplyOfBitLengthMaterialized n A B).1 = A * B) ∧
    (∀ n A B : ℕ, 96 ≤ Nat.log2 n →
      (quantizedMultiplyOfBitLengthMaterialized n A B).2 ≤
        (7840335360 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) ∧
    (∀ n A B : ℕ, 16 ≤ n →
      (quantizedMultiplyOfBitLengthMaterialized n A B).2 ≤
        (54317320874319360 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) ∧
    (∀ A B : ℕ → ℕ,
      (fun n : ℕ => (quantizedMultiplyOfBitLengthMaterialized n (A n) (B n)).2) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))) := by
  refine ⟨fun n A B hA hB => ?_, fun n A B hb96 => ?_, fun n A B hn => ?_, fun A B => ?_⟩
  · rw [quantizedMultiplyOfBitLengthMaterialized_eq_quantizedMultiplyOfBitLength]
    exact quantizedMultiplyOfBitLength_fst_eq_mul n A B hA hB
  · rw [quantizedMultiplyOfBitLengthMaterialized_eq_quantizedMultiplyOfBitLength]
    exact quantizedMultiplyOfBitLength_snd_le_n_log_n_of_log2_ge_96 n A B hb96
  · rw [quantizedMultiplyOfBitLengthMaterialized_eq_quantizedMultiplyOfBitLength]
    exact quantizedMultiplyOfBitLength_snd_le_n_log_n n A B hn
  · simp_rw [quantizedMultiplyOfBitLengthMaterialized_eq_quantizedMultiplyOfBitLength]
    exact quantizedMultiplyOfBitLength_snd_isBigO_n_log_n A B

end IntMul
