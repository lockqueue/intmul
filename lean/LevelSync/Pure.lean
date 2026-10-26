import LevelSync.Unroll

/-!
# Level-synchronous evaluation, part 5: cost-erased (pure) node functions

`preNodeV`, `altNodeV`, `postNodeV` restate the three phases with the snapshot's pure value
functions (`runMultiTapeTranspose`, `computableSpreadRowContiguous`, `gPreTwistU`,
`computableSyntheticFFTRadix2`, `gRescale`, `gMulScaled`, `runMultiTapeAffineOddRoute`, the
`…Exact` solvers, `computableNyquistAltSumContiguous`). They are proved equal to the `.1`-based
definitions through the snapshot's own `_fst` lemmas, so `levelEvalV` (all-pure) satisfies the same
unrolling lemma. This shows that erasing the cost counters is mechanical.
-/

namespace IntMul.LevelSync

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- The snapshot's `if h : i < (Array.ofFn f).size then (Array.ofFn f)[i].1 else d` bookkeeping. -/
theorem ofFn_dite_fst {β γ : Type} (n : ℕ) (f : Fin n → β × γ) (d : β) :
    Array.ofFn (fun i : Fin n =>
        if h : i.val < (Array.ofFn f).size then ((Array.ofFn f)[i.val]).1 else d) =
      Array.ofFn (fun i => (f i).1) := by
  congr 1
  funext i
  simp

/-- The same bookkeeping at a natural-number index. -/
theorem dite_ofFn_fst_eq_getD {β γ : Type} (n : ℕ) (f : Fin n → β × γ) (d : β) (i : ℕ) :
    (if h : i < (Array.ofFn f).size then ((Array.ofFn f)[i]).1 else d) =
      (Array.ofFn (fun j => (f j).1)).getD i d := by
  by_cases hi : i < n <;> simp [Array.getD, hi]

theorem ofFn_getD_ofFn {β : Type} (n : ℕ) (g : Fin n → β) (d : β) :
    Array.ofFn (fun i : Fin n => (Array.ofFn g).getD i.val d) = Array.ofFn g := by
  congr 1
  funext i
  exact array_getD_ofFn_of_lt n g d i.val i.isLt

theorem fst_ite3 {α β : Type} (c1 c2 : Prop) [Decidable c1] [Decidable c2] (a b c : α × β) :
    (if c1 then a else if c2 then b else c).1 = if c1 then a.1 else if c2 then b.1 else c.1 := by
  split_ifs <;> rfl

/-- Pure pre-phase. -/
def preNodeV (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xArr : Array (ℤ × ℤ)) :
    Array (Array (ℤ × ℤ)) :=
  let m_t1 := natLog2Fuel t1 t1
  let xRouted := runMultiTapeTranspose m_t1 r (read1D xArr)
  let xRows := (runScan2DWithSteps t1 r (fun j1 i => read1D xRouted (j1 * r + i))).1
  let U_mat : Array (Array (ℤ × ℤ)) := Array.ofFn (fun j1 : Fin t1 =>
    computableSpreadRowContiguous p_in pSub m1 r (filterTaps.getD j1.val [])
      (xRows.getD j1.val #[]))
  let P_mat := (runScan2DWithSteps t1 r (fun j1 k2 =>
    gPreTwistU pSub (read1D preTwiddles k2) (read2D U_mat j1 k2))).1
  let syn := computableSyntheticFFTRadix2 t1 r m_t1 (r / t1) P_mat
  let Q_mat := (runScan2DWithSteps t1 r (fun v1 k2 => gRescale pSub pSub (read2D syn v1 k2))).1
  (runScan2DWithSteps t1 r (fun v1 k2 =>
    gMulScaled (pSub + 2) (read1D postTwiddles k2) (read2D Q_mat v1 k2))).1

/-- Pure retained value. -/
def altNodeV (p_in pSub t1 r : ℕ) (xArr : Array (ℤ × ℤ)) : ℤ × ℤ :=
  let m_t1 := natLog2Fuel t1 t1
  let xRouted := runMultiTapeTranspose m_t1 r (read1D xArr)
  let xRows := (runScan2DWithSteps t1 r (fun j1 i => read1D xRouted (j1 * r + i))).1
  computableNyquistAltSumContiguous p_in pSub r (xRows.getD (t1 / 2) #[])

/-- Pure post-phase. -/
def postNodeV (p pSub t1 r : ℕ) (c0Table c1Table : Array (ℤ × ℤ)) (pChild_val : ℕ)
    (alt_q : ℤ × ℤ) (qHat_mat : Array (Array (ℤ × ℤ))) : Array (ℤ × ℤ) :=
  let m_t1 := natLog2Fuel t1 t1
  let m_r := natLog2Fuel r r
  let stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
  let qHat_T := runMultiTapeTranspose m_r t1 (read1D stFlatQ.outTape)
  let colRoutes : Array (Array (ℤ × ℤ)) := Array.ofFn (fun u2 : Fin r =>
    runMultiTapeAffineOddRoute m_t1 (computableOddStrideFactor m_t1 u2.val) 0
      (fun v1 => read1D qHat_T (u2.val * t1 + v1)))
  let Y_mat := (runScan2DWithSteps r t1 (fun u2 u1 =>
    gRescale pChild_val pSub (read1D (colRoutes.getD u2 #[]) u1))).1
  let Z_cols_mat : Array (Array (ℤ × ℤ)) := Array.ofFn (fun u2 : Fin r =>
    if 2 * u2.val < r then
      computableSolveBidiagonalFwdExact pSub t1 (read1D c0Table u2.val) (read1D c1Table u2.val)
        (Y_mat.getD u2.val #[])
    else if 2 * u2.val = r then
      computableSolveNyquistExact pSub t1 (read1D c0Table u2.val) (Y_mat.getD u2.val #[]) alt_q
    else
      computableSolveBidiagonalBwdExact pSub t1 (read1D c0Table u2.val) (read1D c1Table u2.val)
        (Y_mat.getD u2.val #[]))
  let stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
  let Z_flat := runMultiTapeTranspose m_t1 r (read1D stFlatZ.outTape)
  (runSequentialScanSteps (fun u => gRescale pSub p (read1D Z_flat u)) (t1 * r)).outTape

theorem preNode_eq_V (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xArr : Array (ℤ × ℤ)) :
    preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xArr =
      preNodeV p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xArr := by
  simp only [preNode, preNodeV, runMultiTapeTransposeFullSteps_fst, runScan2DCostedWithSteps_fst,
    ofFn_dite_fst, computableSpreadRowContiguousWithProgramCost_fst,
    computableSyntheticFFTRadix2WithProgramCost_fst, costedGPreTwistU, costedGRescale,
    costedGMulScaled, computableSpreadRowContiguous]

theorem altNode_eq_V (p_in pSub t1 r : ℕ) (xArr : Array (ℤ × ℤ)) :
    altNode p_in pSub t1 r xArr = altNodeV p_in pSub t1 r xArr := by
  simp only [altNode, altNodeV, runMultiTapeTransposeFullSteps_fst,
    computableNyquistAltSumContiguousWithProgramCost_fst]

theorem postNode_eq_V (p pSub t1 r : ℕ) (c0Table c1Table : Array (ℤ × ℤ)) (pChild_val : ℕ)
    (alt_q : ℤ × ℤ) (qHat_mat : Array (Array (ℤ × ℤ))) :
    postNode p pSub t1 r c0Table c1Table pChild_val alt_q qHat_mat =
      postNodeV p pSub t1 r c0Table c1Table pChild_val alt_q qHat_mat := by
  simp only [postNode, postNodeV, runMultiTapeTransposeFullSteps_fst, runScan2DCostedWithSteps_fst,
    runSequentialScanCostedSteps_fst, runMultiTapeAffineOddRouteFullSteps_fst,
    dite_ofFn_fst_eq_getD, ofFn_getD_ofFn, fst_ite3, costedGRescale,
    computableSolveBidiagonalFwdWithProgramCost_fst, computableSolveNyquistWithProgramCost_fst,
    computableSolveBidiagonalBwdWithProgramCost_fst]

/-- All-pure level evaluation. -/
def levelEvalV : ComputablePaperFastDFTSpec → ℕ → List (Array (ℤ × ℤ)) → List (Array (ℤ × ℤ))
  | .basePow2 p K twiddles, p_in, xs =>
      xs.map (fun x => (computableBaseRadix2FFTWithProgramCost p_in p K twiddles x).1)
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, p_in, xs =>
      postLevel (postNodeV p pSub t1 r c0Table c1Table child.p) t1
        (xs.map (altNodeV p_in pSub t1 r))
        (levelEvalV child pSub
          (xs.flatMap (fun x =>
            (preNodeV p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x).toList)))

theorem levelEvalV_eq_levelEval : ∀ (spec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))), levelEvalV spec p_in xs = levelEval spec p_in xs
  | .basePow2 p K twiddles, p_in, xs => rfl
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, p_in, xs => by
    have hpre : (fun x =>
          (preNodeV p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x).toList) =
        (fun x => (preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x).toList) := by
      funext x
      rw [preNode_eq_V]
    have halt : altNodeV p_in pSub t1 r = altNode p_in pSub t1 r := by
      funext x
      rw [altNode_eq_V]
    have hpost : postNodeV p pSub t1 r c0Table c1Table child.p =
        postNode p pSub t1 r c0Table c1Table child.p := by
      funext a qs
      rw [postNode_eq_V]
    simp only [levelEvalV, levelEval, preLevel, altLevel]
    rw [hpre, halt, hpost, levelEvalV_eq_levelEval child pSub]

/-- **Unrolling lemma, all-pure form.** -/
theorem levelEvalV_eq_map (spec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))) :
    levelEvalV spec p_in xs = xs.map (computablePaperFastDFT p_in spec) := by
  rw [levelEvalV_eq_levelEval, levelEval_eq_map]

end IntMul.LevelSync

#print axioms IntMul.LevelSync.preNode_eq_V
#print axioms IntMul.LevelSync.altNode_eq_V
#print axioms IntMul.LevelSync.postNode_eq_V
#print axioms IntMul.LevelSync.levelEvalV_eq_map
