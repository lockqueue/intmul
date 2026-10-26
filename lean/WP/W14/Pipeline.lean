import IntMul.MaterializedAndComputable.PaperHeadlinePipeline
import IntMulTM.Framework.AxiomGuard

/-!
# W14 (2/11): the schedule-parametric computable pipeline

The snapshot's integer pipeline `computablePaperFastDFTWithProgramCost` (PHP:137) already reads the
sub-step grid `pSub` and the window `m1` from its `ComputablePaperFastDFTSpec.step` nodes; only the leaf
precision is hard-coded (`q_leaf := 2 * p + K + 8`, PCP:2193). This module makes the leaf precision a
parameter `qL : ℕ → ℕ → ℕ` and proves that the instance `qL p K = 2 * p + K + 8` is the snapshot's
pipeline and multiplier, definitionally up to unfolding (`computablePaperFastDFTAt_snapshot`,
`computablePaperFastDFTMultiplyAt_snapshot`).

The bodies below are verbatim copies of PHP:137–226 and PHP:1084–1114 except for the leaf call and the
recursive call. Costs are kept (they are not used by W14) so that the snapshot instance is literally the
snapshot's function.
-/

namespace WP.W14

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- The leaf `BaseRadix2FFT` at an explicit internal grid `q_leaf` (copy of PCP:2190 with `q_leaf` a
parameter). -/
def computableBaseRadix2FFTAt
    (q_leaf p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (xArr : Array (ℤ × ℤ)) :
    BitCostM (Array (ℤ × ℤ)) := do
  let R := 2 ^ K
  let coreArr ← computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles K xArr
  let outScan := runSequentialScanCostedSteps (fun u =>
    costedGRescale q_leaf p (4 * q_leaf) (read1D coreArr u)) R
  BitCostM.tick outScan.2.2
  pure outScan.1

theorem computableBaseRadix2FFTAt_snapshot (p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (xArr : Array (ℤ × ℤ)) :
    computableBaseRadix2FFTAt (2 * p + K + 8) p_in p K twiddles xArr =
      computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr := rfl

/-- **Schedule-parametric pipeline.** `computablePaperFastDFTWithProgramCost` (PHP:137) with the leaf
internal grid given by `qL p K`. -/
def computablePaperFastDFTAt (qL : ℕ → ℕ → ℕ) :
    ℕ → ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) × ℕ
  | p_in, .basePow2 p K twiddles, xArr =>
    computableBaseRadix2FFTAt (qL p K) p_in p K twiddles xArr
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
    let P_cost := P_res.2.2
    let P_mat : Array (Array (ℤ × ℤ)) := P_res.1
    let syn_res :=
      computableSyntheticFFTRadix2WithProgramCost p' t1 r m_t1 (r / t1) P_mat
    let Q_res :=
      runScan2DCostedWithSteps t1 r (fun v1 k2 =>
        costedGRescale pSub pSub (4 * p') (read2D syn_res.1 v1 k2))
    let Q_cost := Q_res.2.2
    let Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
    let qPost_res :=
      runScan2DCostedWithSteps t1 r (fun v1 k2 =>
        costedGMulScaled (pSub + 2) (6 * p') (read1D postTwiddles k2) (read2D Q_mat v1 k2))
    let qPost_cost := qPost_res.2.2
    let qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
    let qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun v1 : Fin t1 =>
        computablePaperFastDFTAt qL pSub child (qPost_mat.getD v1.val #[]))
    let qHat_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
    let childCostSum : ℕ := sumArrayCosts qHat_res
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
    let Y_cost := Y_res.2.2
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
    let out_cost := outScan.2.2
    let spreadCost : ℕ := sumArrayCosts U_rows
    let solverCost : ℕ := sumArrayCosts Z_cols_res
    let twistAndSolverCost : ℕ :=
      P_cost + Q_cost + qPost_cost + Y_cost + altRes.2 + solverCost + out_cost
    let oddRouteSteps : ℕ := sumArrayCosts colRoutes
    let linearScanSteps : ℕ :=
      xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
        stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1
    let routingSteps : ℕ :=
      xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + oddRouteSteps + linearScanSteps
    let routingCost : ℕ := routingSteps * addBitCost (8 * p')
    (outScan.1,
     syn_res.2 + spreadCost + twistAndSolverCost + routingCost + childCostSum)
termination_by structural _ cSpec _ => cSpec

/-- The snapshot's leaf grid. -/
def snapshotQLeaf : ℕ → ℕ → ℕ := fun p K => 2 * p + K + 8

/-- The snapshot instance of the parametric pipeline is the snapshot's pipeline. -/
theorem computablePaperFastDFTAt_snapshot :
    computablePaperFastDFTAt snapshotQLeaf = computablePaperFastDFTWithProgramCost := by
  funext p_in cSpec xArr
  induction cSpec generalizing p_in xArr with
  | basePow2 p K twiddles => rfl
  | step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child ih =>
    simp only [computablePaperFastDFTAt, computablePaperFastDFTWithProgramCost, ih]

/-- The parametric pipeline's first projection. -/
def computablePaperFastDFTValAt (qL : ℕ → ℕ → ℕ)
    (p_in : ℕ) (cSpec : ComputablePaperFastDFTSpec) (xArr : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (computablePaperFastDFTAt qL p_in cSpec xArr).1

/-- **Schedule-parametric multiplier.** PHP:1084 with the parametric pipeline. -/
def computablePaperFastDFTMultiplyAtWithProgramCost (qL : ℕ → ℕ → ℕ)
    (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ × ℕ :=
  let R0 := 2 ^ K0
  let p0 := rootPrecision b K0
  let splitA := splitChunksTreeWithProgramCost b k1 A
  let splitB := splitChunksTreeWithProgramCost b k2 B
  let asArr := splitA.1.toArray
  let bsArr := splitB.1.toArray
  let stPack := runSequentialScanSteps (fun j =>
    (costedPackRootChunkPair (read1D asArr j) (read1D bsArr j)).1) R0
  let packCost := stPack.steps * (2 * addBitCost (4 * p0))
  let fwd := computablePaperFastDFTAt qL b cSpec stPack.outTape
  let stSq := runSequentialScanCostedSteps (fun u =>
    let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u) (read1D fwd.1 u)
    (gConj m.1, m.2 + addBitCost (8 * p0))) R0
  let sqCost := stSq.2.2
  let inv := computablePaperFastDFTAt qL p0 cSpec stSq.1
  let stExt := runSequentialScanCostedSteps (fun j =>
    let e := costedExtractRootSlot p0 b K0 (read1D inv.1 j)
    (e.1, e.2)) R0
  let extCost := stExt.2.2
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j => read1D stExt.1 j)
  let recon := reconstructChunksTreeWithProgramCost b convNat
  let rootCost : ℕ := splitA.2 + splitB.2 + packCost + sqCost + extCost + recon.2
  (recon.1, fwd.2 + inv.2 + rootCost)

/-- First projection of the parametric multiplier. -/
def computablePaperFastDFTMultiplyAt (qL : ℕ → ℕ → ℕ)
    (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ :=
  (computablePaperFastDFTMultiplyAtWithProgramCost qL cSpec b K0 k1 k2 A B).1

theorem computablePaperFastDFTMultiplyAtWithProgramCost_snapshot
    (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) :
    computablePaperFastDFTMultiplyAtWithProgramCost snapshotQLeaf cSpec b K0 k1 k2 A B =
      computablePaperFastDFTMultiplyWithProgramCost cSpec b K0 k1 k2 A B := by
  simp only [computablePaperFastDFTMultiplyAtWithProgramCost,
    computablePaperFastDFTMultiplyWithProgramCost, computablePaperFastDFTAt_snapshot]

/-- The snapshot instance of the parametric multiplier is the snapshot's multiplier. -/
theorem computablePaperFastDFTMultiplyAt_snapshot
    (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) :
    computablePaperFastDFTMultiplyAt snapshotQLeaf cSpec b K0 k1 k2 A B =
      computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B := by
  unfold computablePaperFastDFTMultiplyAt computablePaperFastDFTMultiply
  rw [computablePaperFastDFTMultiplyAtWithProgramCost_snapshot]

#assert_std_axioms computableBaseRadix2FFTAt_snapshot computablePaperFastDFTAt_snapshot
  computablePaperFastDFTMultiplyAtWithProgramCost_snapshot computablePaperFastDFTMultiplyAt_snapshot

end WP.W14
