-- Level-synchronous factorization of the recursive synthetic-FFT pipeline (`IntMul` reference).
import IntMul.MaterializedAndComputable.PaperHeadlinePipeline

/-!
# Level-synchronous evaluation, part 1: per-node factorization (W9-L strategy B spike)

The snapshot's recursive node function `computablePaperFastDFTWithProgramCost`
(`PaperHeadlinePipeline.lean:137-226`) is split at a `.step` node into

* `preNode`  : node input ↦ the `t1 × r` matrix `qPost_mat`; its rows are the children's inputs;
* `altNode`  : node input ↦ the retained Nyquist scalar `alt_q` (the only value the post-phase
  needs from the pre-phase);
* `postNode` : (retained `alt_q`, the array of the `t1` children outputs) ↦ node output.

The three definitions copy the snapshot's `let` chain verbatim and keep only value components
(`.1`), so the factorization is definitional except for the bookkeeping of the children array
(`qHat_mat`), which needs `preNode_size`.
-/

namespace IntMul.LevelSync

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- Pre-phase of a `.step` node (PHP:142-171): input transpose, Kronecker spread, pre-twist,
synthetic FFT, rescale and post-twist. Returns `qPost_mat` (`t1` rows of length `r`). -/
def preNode (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xArr : Array (ℤ × ℤ)) :
    Array (Array (ℤ × ℤ)) :=
  let p' := pSub / 2
  let m_t1 := natLog2Fuel t1 t1
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
  qPost_res.1

/-- The retained value of a `.step` node: the Nyquist alternating sum of row `t1 / 2` of the
transposed input (PHP:145-148, 192-194). -/
def altNode (p_in pSub t1 r : ℕ) (xArr : Array (ℤ × ℤ)) : ℤ × ℤ :=
  let p' := pSub / 2
  let m_t1 := natLog2Fuel t1 t1
  let xRoutedRes := runMultiTapeTransposeFullSteps m_t1 r (read1D xArr)
  let xRows_res :=
    runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
  let xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
  (computableNyquistAltSumContiguousWithProgramCost p_in pSub p' r (xRows.getD (t1 / 2) #[])).1

/-- Post-phase of a `.step` node (PHP:178-211): flatten and transpose the children outputs,
odd-stride column routes, rescale, column solvers (Nyquist column uses the retained `alt_q`),
transpose and rescale. `qHat_mat` holds the `t1` children outputs. -/
def postNode (p pSub t1 r : ℕ) (c0Table c1Table : Array (ℤ × ℤ)) (pChild_val : ℕ)
    (alt_q : ℤ × ℤ) (qHat_mat : Array (Array (ℤ × ℤ))) : Array (ℤ × ℤ) :=
  let p' := pSub / 2
  let m_t1 := natLog2Fuel t1 t1
  let m_r := natLog2Fuel r r
  let stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
  let qHat_T_res := runMultiTapeTransposeFullSteps m_r t1 (read1D stFlatQ.outTape)
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
    Array.ofFn (fun u2 : Fin r =>
      if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
  let stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
  let Z_flat_res := runMultiTapeTransposeFullSteps m_t1 r (read1D stFlatZ.outTape)
  let outScan := runSequentialScanCostedSteps (fun u =>
    costedGRescale pSub p (4 * p') (read1D Z_flat_res.1 u)) (t1 * r)
  outScan.1

/-- **Factorization, snapshot form** (definitional): the children array is exactly the
snapshot's `qHat_mat` bookkeeping. -/
theorem computablePaperFastDFT_step_snap (p_in p pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
    (child : ComputablePaperFastDFTSpec) (xArr : Array (ℤ × ℤ)) :
    computablePaperFastDFT p_in
        (.step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child) xArr =
      postNode p pSub t1 r c0Table c1Table child.p (altNode p_in pSub t1 r xArr)
        (let qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
          Array.ofFn (fun v1 : Fin t1 =>
            computablePaperFastDFTWithProgramCost pSub child
              ((preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xArr).getD
                v1.val #[]))
         Array.ofFn (fun v1 : Fin t1 =>
            if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])) := by
  rfl

/-- Size of a `runScan2DWithSteps` matrix (missing in the snapshot). -/
theorem runScan2DWithSteps_fst_size {α : Type*} (n1 n2 : ℕ) (f : ℕ → ℕ → α) :
    (runScan2DWithSteps n1 n2 f).1.size = n1 := by
  simp [runScan2DWithSteps]

/-- Row sizes of a `runScan2DWithSteps` matrix (missing in the snapshot). -/
theorem runScan2DWithSteps_row_size {α : Type*} (n1 n2 : ℕ) (f : ℕ → ℕ → α) (i : ℕ)
    (hi : i < n1) : ((runScan2DWithSteps n1 n2 f).1.getD i #[]).size = n2 := by
  simp [runScan2DWithSteps, Array.getD, hi]

/-- `preNode` always has exactly `t1` rows. -/
theorem preNode_size (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xArr : Array (ℤ × ℤ)) :
    (preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xArr).size = t1 := by
  simp only [preNode, runScan2DCostedWithSteps_fst, runScan2DWithSteps_fst_size]

/-- Every row of `preNode` (= a child input) has exactly `r` entries. Not needed for the
unrolling lemma; needed by the machine encoding (one node = exactly `N` entries). -/
theorem preNode_row_size (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xArr : Array (ℤ × ℤ)) (v1 : ℕ) (hv1 : v1 < t1) :
    ((preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xArr).getD v1 #[]).size
      = r := by
  simp only [preNode, runScan2DCostedWithSteps_fst]
  exact runScan2DWithSteps_row_size _ _ _ v1 hv1

/-- The snapshot's children bookkeeping is `Array.map` over the rows of `preNode`. -/
theorem qHat_snap_eq {β : Type} (t1 : ℕ) (f : Array (ℤ × ℤ) → Array (ℤ × ℤ) × β)
    (A : Array (Array (ℤ × ℤ))) (hA : A.size = t1) :
    (let qHat_res : Array (Array (ℤ × ℤ) × β) :=
        Array.ofFn (fun v1 : Fin t1 => f (A.getD v1.val #[]))
     Array.ofFn (fun v1 : Fin t1 =>
        if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])) =
      A.map (fun a => (f a).1) := by
  subst hA
  apply Array.ext
  · simp
  · intro i _ _
    simp [Array.getD]

/-- **Per-node factorization** of the snapshot's node function into pre-phase, children and
post-phase. -/
theorem computablePaperFastDFT_step_eq (p_in p pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
    (child : ComputablePaperFastDFTSpec) (xArr : Array (ℤ × ℤ)) :
    computablePaperFastDFT p_in
        (.step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child) xArr =
      postNode p pSub t1 r c0Table c1Table child.p (altNode p_in pSub t1 r xArr)
        ((preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xArr).map
          (computablePaperFastDFT pSub child)) := by
  rw [computablePaperFastDFT_step_snap]
  congr 1
  exact qHat_snap_eq t1 (computablePaperFastDFTWithProgramCost pSub child) _
    (preNode_size p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xArr)

/-- Leaf case (definitional). -/
theorem computablePaperFastDFT_basePow2_eq (p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (xArr : Array (ℤ × ℤ)) :
    computablePaperFastDFT p_in (.basePow2 p K twiddles) xArr =
      (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 := by
  rfl

/-- Every step-node output has exactly `t1 * r` entries (machine encoding). -/
theorem postNode_size (p pSub t1 r : ℕ) (c0Table c1Table : Array (ℤ × ℤ)) (pChild_val : ℕ)
    (alt_q : ℤ × ℤ) (qHat_mat : Array (Array (ℤ × ℤ))) :
    (postNode p pSub t1 r c0Table c1Table pChild_val alt_q qHat_mat).size = t1 * r := by
  simp only [postNode, runSequentialScanCostedSteps_fst, size_runSequentialScanSteps]

end IntMul.LevelSync
