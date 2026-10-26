import IntMul.MaterializedAndComputable.MaterializedPipeline
import IntMul.MaterializedAndComputable.ComputableExactSolvers

/-!
# Part 3 — Legacy Intermediate Pipeline (`ComputableExactFastDFTSpec`, $R_{\text{leaf}} \mid 4$), Table-Perturbation Bounds, & Kernel `decide` Tests

> **Legacy Intermediate Pipeline Notice**: This module (`ComputableExactFastDFTSpec` /
> `computableExactFastDFT` / `computableExactMultiplyOfBitLengthWithCost`) represents an earlier
> intermediate stage of the formalization that recursed all the way down to $R_{\text{leaf}} \in \{1, 2, 4\}$
> using `computableBaseDFTExact` (`step := 4 / R`) and pre-supplied tables.
> It is **superseded by the paper-faithful headline pipeline** in `PaperHeadlinePipeline.lean`,
> `FaithfulTablesPerturbation.lean`, `ComputableTableBuilder.lean`, and `CallSiteWidthSoundness.lean`
> (`computablePaperMultiplyOfBitLength_correct_and_isBigO`), which uses the paper's stopping rule
> $R \le 4 p^2$ (`buildQuantizedSpecPaperStop`), general power-of-two `BaseRadix2FFT` leaves
> (`computableBaseRadix2FFTWithProgramCost`), and 100% computable series-evaluated tables
> (`buildComputablePaperTablesWithProgramCost`).
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-- Structural predicate certifying that a `QuantizedFastDFTSpec` uses the canonical odd-stride
routing `v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1` at internal steps and has leaf size
`0 < R` dividing `4` (`R ∈ {1, 2, 4}`) at `.base p R`. -/
inductive QuantizedFastDFTSpec.ExecutableValid : QuantizedFastDFTSpec → Prop where
  | base {p R : ℕ} (hR : 0 < R) (hdvd : R ∣ 4) :
      QuantizedFastDFTSpec.ExecutableValid (.base p R)
  | step {p K t1 r c1 : ℕ} {v1Of : ℕ → ℕ → ℕ} {child : QuantizedFastDFTSpec}
      (hv1_eq : ∀ u2 u1 : ℕ, v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1)
      (hchild : child.ExecutableValid) :
      QuantizedFastDFTSpec.ExecutableValid (.step p K t1 r c1 v1Of child)

/-- Every schedule built by `buildQuantizedSpec L p K` with `K ≤ 2 ^ (L + 1)` satisfies
`QuantizedFastDFTSpec.ExecutableValid`. -/
theorem buildQuantizedSpec_executableValid (L p K : ℕ) (hK : K ≤ 2 ^ (L + 1)) :
    (buildQuantizedSpec L p K).ExecutableValid := by
  induction L generalizing p K with
  | zero =>
    dsimp only [buildQuantizedSpec]
    have hK_le : K ≤ 2 := by simpa using hK
    refine QuantizedFastDFTSpec.ExecutableValid.base (pow_pos zero_lt_two K) ?_
    interval_cases K <;> decide
  | succ L ih =>
    dsimp only [buildQuantizedSpec, quantizedBoxGaussianStepSpec]
    have hpow : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
    refine QuantizedFastDFTSpec.ExecutableValid.step
      (fun u2 u1 => by
        rw [Nat.log2_two_pow, routedOddStrideIndex_eq_oddStrideInvPow2])
      (ih (pChild p K) (K - K / 2) (by omega))

/-- Pure-integer multi-level specification (`ComputableExactFastDFTSpec`):
carries the exact per-level output precision `p`, sub-operation precision `pSub = 2 * pChild p K`,
window half-width `m1`, grid dimensions `(t1, r)`, pre-folded integer Sinc-Gaussian filter taps
`filterTaps : Array (List ℤ)`, quantized pre/post-twiddles `preTwiddles, postTwiddles : Array (ℤ × ℤ)`,
and quantized Box-Gaussian passband tables `c0Table, c1Table : Array (ℤ × ℤ)`.
Contains zero `Real` or `Complex` fields. -/
inductive ComputableExactFastDFTSpec where
  | base (p R : ℕ) : ComputableExactFastDFTSpec
  | step (p pSub m1 t1 r : ℕ)
      (filterTaps : Array (List ℤ))
      (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
      (child : ComputableExactFastDFTSpec) : ComputableExactFastDFTSpec

/-- Target output precision `p` of a `ComputableExactFastDFTSpec`. -/
def ComputableExactFastDFTSpec.p : ComputableExactFastDFTSpec → ℕ
  | .base p _ => p
  | .step p _ _ _ _ _ _ _ _ _ _ => p

/-- Compiler extracting the pure-integer `ComputableExactFastDFTSpec` tables from a
`QuantizedFastDFTSpec` (`toComputableExactFastDFTSpec`). -/
noncomputable def toComputableExactFastDFTSpec : QuantizedFastDFTSpec → ComputableExactFastDFTSpec
  | .base p R => .base p R
  | .step p K t1 r _c1 _v1Of child =>
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * pChild p K
    let filterTaps : Array (List ℤ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1.val)
    let preTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2 : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).re,
         realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).im))
    let postTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2 : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).re,
         realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).im))
    let c0Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r =>
        (realQuantizeInt pSub (c0Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
    let c1Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r =>
        (realQuantizeInt pSub (c1Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
    .step p pSub pSub t1 r filterTaps preTwiddles postTwiddles c0Table c1Table
      (toComputableExactFastDFTSpec child)

@[simp]
theorem toComputableExactFastDFTSpec_p (spec : QuantizedFastDFTSpec) :
    (toComputableExactFastDFTSpec spec).p = spec.p := by
  cases spec <;> rfl

/-- **Runtime-Cost-Instrumented Pure-Integer Computable `FastDFT` (`computableExactFastDFTWithCost`, `[MS]` §7)**:
100% computable (`def`, zero `noncomputable`, zero `Real`, zero `Complex`) recursive fixed-point
Gaussian integer (`ℤ × ℤ`) transform that executes the multitape array pipeline while accumulating its
runtime bit-operation and tape-head-step cost bottom-up directly from the executed array operations and
state-machine `.steps` counters:
1. Transposes the input array `xArr` into row-contiguous layout via `runMultiTapeTransposeWithSteps m_t1 r`
   (`xRoutedRes.2` head steps accumulated from `stU.steps` and `stI.steps`) and slices it into `t1`
   contiguous rows `xRows` via `runSequentialScanSteps` so both the spread and `computableNyquistAltSumContiguous`
   read contiguous length-`r` rows with zero stride-`t1` random access,
2. Computes `U_rows` via `computableSpreadRowContiguousWithCost` on each contiguous row and sums the
   per-block Kronecker multiplication/addition costs via `sumArrayCosts U_rows`,
3. Computes `syn_res` via `computableSyntheticFFTRadix2WithCost` and accumulates `syn_res.2`,
4. Runs the recursive child transforms `computableExactFastDFTWithCost pSub child` and sums their
   returned runtime costs via `sumArrayCosts qHat_res`,
5. Flattens `qHat_mat` sequentially via `runFlatten2DSteps` (zero `/` or `%`), transposes via
   `runMultiTapeTransposeWithSteps`, and routes columns via `runMultiTapeAffineOddRouteWithSteps`
   (accumulating `oddRouteSteps = sumArrayCosts colRoutes` from `stU.steps` and `stI.steps`),
6. Runs the step-instrumented column solvers `computableSolveBidiagonalFwdExactWithSteps`,
   `computableSolveNyquistExactWithSteps`, and `computableSolveBidiagonalBwdExactWithSteps` (using
   `runBwdRevSteps` and `runReverseSteps`) and accumulates `solverSteps = sumArrayCosts Z_cols_res`,
7. Flattens `Z_cols_mat` sequentially via `runFlatten2DSteps` (`stFlatZ.steps`), transposes via
   `runMultiTapeTransposeWithSteps` (`Z_flat_res.2`), and rescales the output via `runSequentialScanSteps` (`outScan.steps`). -/
def computableExactFastDFTWithCost :
    ℕ → ComputableExactFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) × ℕ
  | p_in, .base p R, xArr =>
    let baseArr := computableBaseDFTExact p_in p R xArr
    let rowScans : Array ((ℤ × ℤ) × ℕ) := Array.ofFn (fun u : Fin R =>
      let st := runSequentialScanSteps
        (fun j => gMulUnit (read1D xArr j) (unitFourthRoot (j * u.val * (4 / R)))) R
      (read1D baseArr u.val, st.steps * addBitCost p))
    (Array.ofFn (fun u : Fin R => if h : u.val < rowScans.size then rowScans[u.val].1 else (0, 0)),
     sumArrayCosts rowScans)
  | p_in, .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, xArr =>
    let p' := pSub / 2
    let m_t1 := natLog2Fuel t1 t1
    let m_r := natLog2Fuel r r
    let xRoutedRes := runMultiTapeTransposeWithSteps m_t1 r (read1D xArr)
    let xRows_res :=
      runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
    let xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
    let U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        computableSpreadRowContiguousWithCost p_in pSub m1 r
          (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
    let U_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
    let P_res :=
      runScan2DWithSteps t1 r (fun j1 k2 =>
        gPreTwistU pSub (read1D preTwiddles k2) (read2D U_mat j1 k2))
    let P_mat : Array (Array (ℤ × ℤ)) := P_res.1
    let syn_res :=
      computableSyntheticFFTRadix2WithCost p' t1 r m_t1 (r / t1) P_mat
    let Q_res :=
      runScan2DWithSteps t1 r (fun v1 k2 =>
        gRescale pSub pSub (read2D syn_res.1 v1 k2))
    let Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
    let qPost_res :=
      runScan2DWithSteps t1 r (fun v1 k2 =>
        gMulScaled (pSub + 2) (read1D postTwiddles k2) (read2D Q_mat v1 k2))
    let qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
    let qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun v1 : Fin t1 =>
        computableExactFastDFTWithCost pSub child (qPost_mat.getD v1.val #[]))
    let qHat_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
    let childCostSum : ℕ := sumArrayCosts qHat_res
    let stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
    let qHat_T_res := runMultiTapeTransposeWithSteps m_r t1 (read1D stFlatQ.outTape)
    let pChild_val := child.p
    let colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        runMultiTapeAffineOddRouteWithSteps m_t1
          (computableOddStrideFactor m_t1 u2.val) 0
          (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
    let Y_res :=
      runScan2DWithSteps r t1 (fun u2 u1 =>
        let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
        gRescale pChild_val pSub (read1D colArr u1))
    let Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
    let alt_q : ℤ × ℤ :=
      computableNyquistAltSumContiguous p_in pSub r (xRows.getD (t1 / 2) #[])
    let Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun u2 : Fin r =>
        let c0 := read1D c0Table u2.val
        let c1_pass := read1D c1Table u2.val
        let Y_col := Y_mat.getD u2.val #[]
        if 2 * u2.val < r then
          computableSolveBidiagonalFwdExactWithSteps pSub t1 c0 c1_pass Y_col
        else if 2 * u2.val = r then
          computableSolveNyquistExactWithSteps pSub t1 c0 Y_col alt_q
        else
          computableSolveBidiagonalBwdExactWithSteps pSub t1 c0 c1_pass Y_col)
    let Z_cols_mat : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
    let stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
    let Z_flat_res := runMultiTapeTransposeWithSteps m_t1 r (read1D stFlatZ.outTape)
    let outScan := runSequentialScanSteps (fun u => gRescale pSub p (read1D Z_flat_res.1 u)) (t1 * r)
    let spreadCost : ℕ := sumArrayCosts U_rows
    let solverSteps : ℕ := sumArrayCosts Z_cols_res
    let twistAndSolverCost : ℕ :=
      solverSteps * (16 * computableMulBitCost (4 * p') + 16 * addBitCost (4 * p'))
    let oddRouteSteps : ℕ := sumArrayCosts colRoutes
    let linearScanSteps : ℕ :=
      xRows_res.2 + P_res.2 + Q_res.2 + qPost_res.2 +
        stFlatQ.steps + Y_res.2 + stFlatZ.steps + outScan.steps
    let routingSteps : ℕ :=
      xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + oddRouteSteps + linearScanSteps
    let routingCost : ℕ := routingSteps * addBitCost (8 * p')
    (outScan.outTape,
     syn_res.2 + spreadCost + twistAndSolverCost + routingCost + childCostSum)
termination_by structural _ cSpec _ => cSpec

/-- **Pure-Integer Multi-Level Computable `FastDFT` (`computableExactFastDFT`, `[MS]` §7)**:
First projection of `computableExactFastDFTWithCost`. -/
def computableExactFastDFT
    (p_in : ℕ) (cSpec : ComputableExactFastDFTSpec) (xArr : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (computableExactFastDFTWithCost p_in cSpec xArr).1

theorem toScaledComplex_Z_cols_step_eq
    (pSub t1 r : ℕ) (c0Table c1Table : Array (ℤ × ℤ)) (Y_mat : Array (Array (ℤ × ℤ)))
    (alt_q : ℤ × ℤ) (c0_c c1_c alt_c : ℂ) (Y_c : ℕ → ℂ)
    (u2 u1 : ℕ) (hu2 : u2 < r) (hu1 : u1 < t1)
    (hc0 : toScaledComplex pSub (read1D c0Table u2) = c0_c)
    (hc1 : toScaledComplex pSub (read1D c1Table u2) = c1_c)
    (halt : toScaledComplex pSub alt_q = alt_c)
    (hY : ∀ k < t1, toScaledComplex pSub (read2D Y_mat u2 k) = Y_c k) :
    let Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun u2' : Fin r =>
        let c0 := read1D c0Table u2'.val
        let c1_pass := read1D c1Table u2'.val
        let Y_col := Y_mat.getD u2'.val #[]
        if 2 * u2'.val < r then
          computableSolveBidiagonalFwdExactWithSteps pSub t1 c0 c1_pass Y_col
        else if 2 * u2'.val = r then
          computableSolveNyquistExactWithSteps pSub t1 c0 Y_col alt_q
        else
          computableSolveBidiagonalBwdExactWithSteps pSub t1 c0 c1_pass Y_col)
    toScaledComplex pSub
      (read2D
        (Array.ofFn (fun u2' : Fin r =>
          if h : u2'.val < Z_cols_res.size then Z_cols_res[u2'.val].1 else #[]))
        u2 u1) =
    (if 2 * u2 < r then
      solveBidiagonalFwdQuantized pSub t1 c0_c c1_c Y_c u1
    else if 2 * u2 = r then
      solveNyquistQuantized pSub t1 c0_c Y_c alt_c u1
    else
      solveBidiagonalBwdQuantized pSub t1 c0_c c1_c Y_c u1) := by
  dsimp only
  rw [read2D_ofFn_of_lt r _ hu2 u1]
  simp only [Array.size_ofFn, hu2, ↓reduceDIte, Array.getElem_ofFn]
  split_ifs with h1 h2
  · rw [computableSolveBidiagonalFwdExactWithSteps_fst,
        toScaledComplex_computableSolveBidiagonalFwdExact_eq pSub t1 _ _ _ u1 hu1, hc0, hc1]
    refine solveBidiagonalFwdQuantized_congr_lt pSub t1 c0_c c1_c _ Y_c (fun k hk => ?_) u1 hu1
    rw [read1D_array_getD_eq_read2D]
    exact hY k hk
  · rw [computableSolveNyquistExactWithSteps_fst,
        toScaledComplex_computableSolveNyquistExact_eq pSub t1 _ _ _ u1 hu1, hc0, halt]
    refine solveNyquistQuantized_congr_lt pSub t1 c0_c _ Y_c alt_c (fun k hk => ?_) u1 hu1
    rw [read1D_array_getD_eq_read2D]
    exact hY k hk
  · rw [computableSolveBidiagonalBwdExactWithSteps_fst,
        toScaledComplex_computableSolveBidiagonalBwdExact_eq pSub t1 _ _ _ u1 hu1, hc0, hc1]
    refine solveBidiagonalBwdQuantized_congr_lt pSub t1 c0_c c1_c _ Y_c (fun k hk => ?_) u1 hu1
    rw [read1D_array_getD_eq_read2D]
    exact hY k hk

/-- **Master End-to-End Semantic Equivalence of `computableExactFastDFT` and `sincGaussianFastDFTQuantized`**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`, `hexec : spec.ExecutableValid`),
any input precision `p_in : ℕ`, any integer array `xArr : Array (ℤ × ℤ)` and functional input
`x : ℕ → ℂ` with `∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k)`, and any output
frequency `u < spec.size`, dequantizing the pure-integer output of `computableExactFastDFT` equals
`sincGaussianFastDFTQuantized spec x u` identically. -/
theorem toScaledComplex_computableExactFastDFT_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.ExecutableValid)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < spec.size) :
    toScaledComplex spec.p
      (read1D (computableExactFastDFT p_in (toComputableExactFastDFTSpec spec) xArr) u) =
      sincGaussianFastDFTQuantized spec x u := by
  unfold computableExactFastDFT
  induction hvalid generalizing p_in xArr x u with
  | base p R =>
    cases hexec with
    | base hR hdvd =>
      dsimp only [toComputableExactFastDFTSpec, computableExactFastDFTWithCost,
        sincGaussianFastDFTQuantized, QuantizedFastDFTSpec.p]
      dsimp only [QuantizedFastDFTSpec.size] at hx hu
      rw [read1D_ofFn_of_lt R _ hu]
      simp only [Array.size_ofFn, hu, ↓reduceDIte, Array.getElem_ofFn]
      exact toScaledComplex_computableBaseDFTExact_eq p_in p R hR hdvd xArr x hx u hu
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hexec with
    | step hv1_eq hchild_exec =>
      dsimp only [toComputableExactFastDFTSpec, sincGaussianFastDFTQuantized, QuantizedFastDFTSpec.p]
      dsimp only [QuantizedFastDFTSpec.size] at hx hu
      obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
      obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
      set α := alphaSchedule (pWork p K)
      set pSub := 2 * pChild p K
      set filterTaps : Array (List ℤ) :=
        Array.ofFn (fun j1 : Fin t1 =>
          kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1.val)
      set preTwiddles : Array (ℤ × ℤ) :=
        Array.ofFn (fun k2 : Fin r =>
          (realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).re,
           realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).im))
      set postTwiddles : Array (ℤ × ℤ) :=
        Array.ofFn (fun k2 : Fin r =>
          (realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).re,
           realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).im))
      set c0Table : Array (ℤ × ℤ) :=
        Array.ofFn (fun u2 : Fin r =>
          (realQuantizeInt pSub (c0Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
      set c1Table : Array (ℤ × ℤ) :=
        Array.ofFn (fun u2 : Fin r =>
          (realQuantizeInt pSub (c1Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
      set cChild := toComputableExactFastDFTSpec child
      dsimp only [computableExactFastDFTWithCost]
      set p' := pSub / 2
      set m_t1 := natLog2Fuel t1 t1
      set m_r := natLog2Fuel r r
      have hm_t1 : m_t1 = Nat.log2 t1 := natLog2Fuel_self t1
      have hm_r : m_r = Nat.log2 r := natLog2Fuel_self r
      set xRoutedRes := runMultiTapeTransposeWithSteps m_t1 r (read1D xArr)
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
            runMultiTapeTransposeWithSteps_fst,
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
          computableSpreadRowContiguousWithCost p_in pSub pSub r
            (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
      set U_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
      set P_res :=
        runScan2DWithSteps t1 r (fun j1 k2 =>
          gPreTwistU pSub (read1D preTwiddles k2) (read2D U_mat j1 k2))
      set P_mat : Array (Array (ℤ × ℤ)) := P_res.1
      set syn_res := computableSyntheticFFTRadix2WithCost p' t1 r m_t1 (r / t1) P_mat
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
          computableExactFastDFTWithCost pSub cChild (qPost_mat.getD v1.val #[]))
      set qHat_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
      set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
      set qHat_T_res := runMultiTapeTransposeWithSteps m_r t1 (read1D stFlatQ.outTape)
      set colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          runMultiTapeAffineOddRouteWithSteps m_t1
            (computableOddStrideFactor m_t1 u2.val) 0
            (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
      set Y_res :=
        runScan2DWithSteps r t1 (fun u2 u1 =>
          let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
          gRescale cChild.p pSub (read1D colArr u1))
      set Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
      set alt_q : ℤ × ℤ :=
        computableNyquistAltSumContiguous p_in pSub r (xRows.getD (t1 / 2) #[])
      set Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          let c0 := read1D c0Table u2.val
          let c1_pass := read1D c1Table u2.val
          let Y_col := Y_mat.getD u2.val #[]
          if 2 * u2.val < r then
            computableSolveBidiagonalFwdExactWithSteps pSub t1 c0 c1_pass Y_col
          else if 2 * u2.val = r then
            computableSolveNyquistExactWithSteps pSub t1 c0 Y_col alt_q
          else
            computableSolveBidiagonalBwdExactWithSteps pSub t1 c0 c1_pass Y_col)
      set Z_cols_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
      set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
      set Z_flat_res := runMultiTapeTransposeWithSteps m_t1 r (read1D stFlatZ.outTape)
      rw [read1D_runSequentialScanSteps_eq _ (t1 * r) u hu, toScaledComplex_gRescale_eq]
      apply congrArg (complexQuantize p)
      set U := kroneckerSincGaussianSpreadArray α pSub pSub t1 r x
      set P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
      set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
      set qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTQuantized child (qPost v1) u2
      set Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
      have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r,
          toScaledComplex pSub ((P_mat.getD j1 #[]).getD k2 (0, 0)) = P j1 k2 := by
        intro j1 hj1 k2 hk2
        have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
        rw [array_getD_getD_eq_read2D_pair]
        dsimp only [P_mat, P_res, P]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2]
        have htw : toScaledComplex pSub (read1D preTwiddles k2) =
            complexQuantize pSub (zetaRoot r (k2 : ℝ)) := by
          dsimp only [preTwiddles]
          rw [read1D_ofFn_of_lt r _ hk2]
          exact toScaledComplex_realQuantizeInt_pair pSub (zetaRoot r (k2 : ℝ))
        have hU_row : read2D U_mat j1 k2 =
            read1D (computableSpreadRowContiguousWithCost p_in pSub pSub r
              (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1) (xRows.getD j1 #[])).1 k2 := by
          dsimp only [U_mat, U_rows, filterTaps]
          rw [read2D_ofFn_of_lt t1 _ hj1_t1 k2]
          simp only [Array.size_ofFn, hj1_t1, ↓reduceDIte, Array.getElem_ofFn,
            array_getD_ofFn_of_lt t1 _ [] j1 hj1_t1]
        rw [hU_row, ← htw]
        exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2) _ (U j1 k2)
          (computableSpreadRowContiguousWithCost_eq_kroneckerSincGaussianSpreadArray
            α p_in pSub pSub t1 r (xRows.getD j1 #[]) x j1 k2 (hxRow_eq j1 hj1_t1) hk2).symm
      have hQ_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D Q_mat v1 k2) = Q v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [Q_mat, Q_res, Q, syn_res]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize pSub)
        have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
          rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
        rw [computableSyntheticFFTRadix2WithCost_fst, hm_t1,
            ← array_getD_getD_eq_read2D_pair _ v1 k2,
            toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1 k2 (ht1_pow.symm ▸ hv1) hk2]
        exact syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P hP_eq v1 k2 hk2
      have hqPost_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [qPost_mat, qPost_res, qPost]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
        have htw : toScaledComplex pSub (read1D postTwiddles k2) =
            complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) := by
          dsimp only [postTwiddles]
          rw [read1D_ofFn_of_lt r _ hk2]
          exact toScaledComplex_realQuantizeInt_pair pSub (zetaRoot r (-(k2 : ℝ)))
        rw [htw]
      have hqHat_eq : ∀ v1 < t1, ∀ u2 < r,
          toScaledComplex child.p (read2D qHat_mat v1 u2) = qHat v1 u2 := by
        intro v1 hv1 u2 hu2
        dsimp only [qHat_mat, qHat_res, qHat]
        rw [read2D_ofFn_of_lt t1 _ hv1 u2]
        simp only [Array.size_ofFn, hv1, ↓reduceDIte, Array.getElem_ofFn]
        exact ih hchild_exec pSub (qPost_mat.getD v1 #[]) (qPost v1)
          (fun k hk => by
            have hk_r : k < r := hchild_size ▸ hk
            rw [read1D_array_getD_eq_read2D]
            exact (hqPost_eq v1 hv1 k hk_r).symm)
          u2 (hchild_size.symm ▸ hu2)
      have hY_eq : ∀ u2 < r, ∀ u1 < t1,
          toScaledComplex pSub (read2D Y_mat u2 u1) = Y u2 u1 := by
        intro u2 hu2 u1 hu1
        dsimp only [Y_mat, Y_res, colRoutes, qHat_T_res, stFlatQ, Y]
        rw [read2D_runScan2DWithSteps_of_lt r t1 _ hu2 hu1]
        simp only [Array.size_ofFn, hu2, ↓reduceDIte, Array.getElem_ofFn, toScaledComplex_gRescale_eq]
        have hu1_m : u1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hu1
        have hv1_t1 : v1Of u2 u1 < t1 := hv1_lt u2 hu2 u1 hu1
        have hcChild_p : cChild.p = child.p := toComputableExactFastDFTSpec_p child
        rw [runMultiTapeAffineOddRouteWithSteps_fst, computableOddStrideFactor_eq_oddStrideFactor, hm_t1,
            read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq (Nat.log2 t1) u2 u1 _ hu1_m,
            ← hv1_eq u2 u1,
            runMultiTapeTransposeWithSteps_fst, hm_r,
            read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 r) r t1 hr_pow ht1 qHat_mat u2 (v1Of u2 u1) hu2 hv1_t1,
            hcChild_p, hqHat_eq (v1Of u2 u1) hv1_t1 u2 hu2]
      have hu2_lt : u % r < r := Nat.mod_lt u hr
      have hu1_lt : u / r < t1 := by
        rw [Nat.div_lt_iff_lt_mul hr]
        linarith
      have hu_decomp : (u / r) * r + u % r = u := by
        rw [mul_comm, Nat.div_add_mod]
      have hZ_flat : read1D Z_flat_res.1 u = read2D Z_cols_mat (u % r) (u / r) := by
        dsimp only [Z_flat_res, stFlatZ]
        rw [runMultiTapeTransposeWithSteps_fst, hm_t1]
        conv_lhs => rw [← hu_decomp]
        exact read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 t1) t1 r ht1_pow hr Z_cols_mat (u / r) (u % r) hu1_lt hu2_lt
      rw [hZ_flat]
      have hc0_eq : toScaledComplex pSub (read1D c0Table (u % r)) =
          (realQuantize pSub (c0Coeff (realErfScaled α) (((u % r : ℕ) : ℝ) / (r : ℝ))) : ℂ) := by
        dsimp only [c0Table]
        rw [read1D_ofFn_of_lt r _ hu2_lt]
        exact toScaledComplex_realQuantizeInt_real pSub _
      have hc1_eq : toScaledComplex pSub (read1D c1Table (u % r)) =
          (realQuantize pSub (c1Coeff (realErfScaled α) (((u % r : ℕ) : ℝ) / (r : ℝ))) : ℂ) := by
        dsimp only [c1Table]
        rw [read1D_ofFn_of_lt r _ hu2_lt]
        exact toScaledComplex_realQuantizeInt_real pSub _
      have halt_eq : toScaledComplex pSub alt_q = complexQuantize pSub (nyquistAltSum t1 r x) := by
        dsimp only [alt_q]
        have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
        exact toScaledComplex_computableNyquistAltSumContiguous_eq p_in pSub t1 r hr
          (xRows.getD (t1 / 2) #[]) x (hxRow_eq (t1 / 2) hhalf_lt)
      exact toScaledComplex_Z_cols_step_eq pSub t1 r c0Table c1Table Y_mat alt_q
        (realQuantize pSub (c0Coeff (realErfScaled α) (((u % r : ℕ) : ℝ) / (r : ℝ))) : ℂ)
        (realQuantize pSub (c1Coeff (realErfScaled α) (((u % r : ℕ) : ℝ) / (r : ℝ))) : ℂ)
        (complexQuantize pSub (nyquistAltSum t1 r x))
        (Y (u % r)) (u % r) (u / r) hu2_lt hu1_lt hc0_eq hc1_eq halt_eq
        (fun k hk => hY_eq (u % r) hu2_lt k hk)

/-- **Exact Runtime Cost Equivalence of `computableExactFastDFTWithCost` and `sincGaussianFastDFTQuantizedIntrinsicCost` (`[MS]` §§3.2, 3.4)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`, `hexec : spec.ExecutableValid`)
and any `xArr : Array (ℤ × ℤ)` and `x : ℕ → ℂ` with `∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k)`,
the bottom-up integer runtime cost `((computableExactFastDFTWithCost p_in (toComputableExactFastDFTSpec spec) xArr).2 : ℝ)`
accumulated directly from the executed `ℤ × ℤ` array passes and `.steps`-instrumented multitape machines
equals `(sincGaussianFastDFTQuantizedIntrinsicCost spec x).2`. -/
theorem computableExactFastDFTWithCost_snd_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.ExecutableValid)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k)) :
    ((computableExactFastDFTWithCost p_in (toComputableExactFastDFTSpec spec) xArr).2 : ℝ) =
      (sincGaussianFastDFTQuantizedIntrinsicCost spec x).2 := by
  induction hvalid generalizing p_in xArr x with
  | base p R =>
    cases hexec with
    | base hR hdvd =>
      dsimp only [toComputableExactFastDFTSpec, computableExactFastDFTWithCost,
        sincGaussianFastDFTQuantizedIntrinsicCost]
      have hbase :
          sumArrayCosts
            (Array.ofFn (fun u : Fin R =>
              let st := runSequentialScanSteps
                (fun j => gMulUnit (read1D xArr j) (unitFourthRoot (j * u.val * (4 / R)))) R
              (read1D (computableBaseDFTExact p_in p R xArr) u.val, st.steps * addBitCost p))) =
            R * (R * addBitCost p) := by
        refine sumArrayCosts_ofFn_const R _ (R * addBitCost p) (fun u _ => ?_)
        simp [runSequentialScanSteps_steps]
      rw [hbase]
      push_cast
      ring
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hexec with
    | step hv1_eq hchild_exec =>
      dsimp only [toComputableExactFastDFTSpec, sincGaussianFastDFTQuantizedIntrinsicCost]
      dsimp only [QuantizedFastDFTSpec.size] at hx
      obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
      obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
      set α := alphaSchedule (pWork p K)
      set pSub := 2 * pChild p K
      set p' := pChild p K
      have hp'_div : pSub / 2 = p' := Nat.mul_div_right p' zero_lt_two
      set filterTaps : Array (List ℤ) :=
        Array.ofFn (fun j1 : Fin t1 =>
          kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1.val)
      set preTwiddles : Array (ℤ × ℤ) :=
        Array.ofFn (fun k2 : Fin r =>
          (realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).re,
           realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).im))
      set postTwiddles : Array (ℤ × ℤ) :=
        Array.ofFn (fun k2 : Fin r =>
          (realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).re,
           realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).im))
      set c0Table : Array (ℤ × ℤ) :=
        Array.ofFn (fun u2 : Fin r =>
          (realQuantizeInt pSub (c0Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
      set c1Table : Array (ℤ × ℤ) :=
        Array.ofFn (fun u2 : Fin r =>
          (realQuantizeInt pSub (c1Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
      set cChild := toComputableExactFastDFTSpec child
      dsimp only [computableExactFastDFTWithCost]
      set m_t1 := natLog2Fuel t1 t1
      set m_r := natLog2Fuel r r
      have hm_t1 : m_t1 = Nat.log2 t1 := natLog2Fuel_self t1
      have hm_r : m_r = Nat.log2 r := natLog2Fuel_self r
      set xRoutedRes := runMultiTapeTransposeWithSteps m_t1 r (read1D xArr)
      set xRows_res :=
        runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
      set xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
      have hxRow_eq : ∀ j1 < t1, ∀ i < r,
          routedInputGather t1 r x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i) := by
        intro j1 hj1 i hi
        rw [routedInputGather_eq]
        dsimp only [xRows, xRows_res, xRoutedRes]
        have hj1_m : j1 < 2 ^ m_t1 := by rw [hm_t1]; exact ht1_pow.symm ▸ hj1
        rw [read1D_array_getD_eq_read2D,
            read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi,
            runMultiTapeTransposeWithSteps_fst,
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
          computableSpreadRowContiguousWithCost p_in pSub pSub r
            (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
      set U_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
      set P_res :=
        runScan2DWithSteps t1 r (fun j1 k2 =>
          gPreTwistU pSub (read1D preTwiddles k2) (read2D U_mat j1 k2))
      set P_mat : Array (Array (ℤ × ℤ)) := P_res.1
      set syn_res := computableSyntheticFFTRadix2WithCost (pSub / 2) t1 r m_t1 (r / t1) P_mat
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
          computableExactFastDFTWithCost pSub cChild (qPost_mat.getD v1.val #[]))
      set qHat_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
      set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
      set qHat_T_res := runMultiTapeTransposeWithSteps m_r t1 (read1D stFlatQ.outTape)
      set colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          runMultiTapeAffineOddRouteWithSteps m_t1
            (computableOddStrideFactor m_t1 u2.val) 0
            (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
      set Y_res :=
        runScan2DWithSteps r t1 (fun u2 u1 =>
          let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
          gRescale cChild.p pSub (read1D colArr u1))
      set Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
      set alt_q : ℤ × ℤ :=
        computableNyquistAltSumContiguous p_in pSub r (xRows.getD (t1 / 2) #[])
      set Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          let c0 := read1D c0Table u2.val
          let c1_pass := read1D c1Table u2.val
          let Y_col := Y_mat.getD u2.val #[]
          if 2 * u2.val < r then
            computableSolveBidiagonalFwdExactWithSteps pSub t1 c0 c1_pass Y_col
          else if 2 * u2.val = r then
            computableSolveNyquistExactWithSteps pSub t1 c0 Y_col alt_q
          else
            computableSolveBidiagonalBwdExactWithSteps pSub t1 c0 c1_pass Y_col)
      set Z_cols_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
      set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
      set Z_flat_res := runMultiTapeTransposeWithSteps m_t1 r (read1D stFlatZ.outTape)
      set outScan := runSequentialScanSteps (fun u => gRescale pSub p (read1D Z_flat_res.1 u)) (t1 * r)
      set U := kroneckerSincGaussianSpreadArray α pSub pSub t1 r (routedInputGather t1 r x)
      set P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
      set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
      have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r,
          toScaledComplex pSub ((P_mat.getD j1 #[]).getD k2 (0, 0)) = P j1 k2 := by
        intro j1 hj1 k2 hk2
        have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
        rw [array_getD_getD_eq_read2D_pair]
        dsimp only [P_mat, P_res, P]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2]
        have htw : toScaledComplex pSub (read1D preTwiddles k2) =
            complexQuantize pSub (zetaRoot r (k2 : ℝ)) := by
          dsimp only [preTwiddles]
          rw [read1D_ofFn_of_lt r _ hk2]
          exact toScaledComplex_realQuantizeInt_pair pSub (zetaRoot r (k2 : ℝ))
        have hU_row : read2D U_mat j1 k2 =
            read1D (computableSpreadRowContiguousWithCost p_in pSub pSub r
              (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1) (xRows.getD j1 #[])).1 k2 := by
          dsimp only [U_mat, U_rows, filterTaps]
          rw [read2D_ofFn_of_lt t1 _ hj1_t1 k2]
          simp only [Array.size_ofFn, hj1_t1, ↓reduceDIte, Array.getElem_ofFn,
            array_getD_ofFn_of_lt t1 _ [] j1 hj1_t1]
        rw [hU_row, ← htw]
        exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2) _ (U j1 k2)
          (computableSpreadRowContiguousWithCost_eq_kroneckerSincGaussianSpreadArray
            α p_in pSub pSub t1 r (xRows.getD j1 #[]) (routedInputGather t1 r x) j1 k2 (hxRow_eq j1 hj1_t1) hk2).symm
      have hQ_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D Q_mat v1 k2) = Q v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [Q_mat, Q_res, Q, syn_res]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize pSub)
        have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
          rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
        rw [computableSyntheticFFTRadix2WithCost_fst, hm_t1,
            ← array_getD_getD_eq_read2D_pair _ v1 k2,
            toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1 k2 (ht1_pow.symm ▸ hv1) hk2]
        exact syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P hP_eq v1 k2 hk2
      have hqPost_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [qPost_mat, qPost_res, qPost]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
        have htw : toScaledComplex pSub (read1D postTwiddles k2) =
            complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) := by
          dsimp only [postTwiddles]
          rw [read1D_ofFn_of_lt r _ hk2]
          exact toScaledComplex_realQuantizeInt_pair pSub (zetaRoot r (-(k2 : ℝ)))
        rw [htw]
      have hsyn_cost : syn_res.2 = syntheticFFTStepBitCost t1 r p' := by
        dsimp only [syn_res, syntheticFFTStepBitCost]
        rw [computableSyntheticFFTRadix2WithCost_snd, hm_t1, hp'_div]
      have hspread_cost : sumArrayCosts U_rows =
          executedKroneckerSpreadStepBitCost α p K t1 r (routedInputGather t1 r x) := by
        dsimp only [U_rows, filterTaps, executedKroneckerSpreadStepBitCost]
        refine sumArrayCosts_ofFn_eq_sum t1 _ _ (fun j1 hj1 => ?_)
        rw [array_getD_ofFn_of_lt t1 _ [] j1 hj1]
        exact computableSpreadRowContiguousWithCost_snd_eq α p_in pSub pSub t1 r
          (xRows.getD j1 #[]) (routedInputGather t1 r x) j1 (hxRow_eq j1 hj1)
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
                runMultiTapeAffineOddRouteWithSteps m_t1
                  (computableOddStrideFactor m_t1 u2.val) 0
                  (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))) =
              r * ((2 * m_t1) * 2 ^ m_t1) := by
          refine sumArrayCosts_ofFn_const r _ _ (fun u2 _ => ?_)
          simp
        rw [h0, hm_t1, ht1_pow]
        ring
      have hrouting_cost :
          (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
            (xRows_res.2 + P_res.2 + Q_res.2 + qPost_res.2 +
              stFlatQ.steps + Y_res.2 + stFlatZ.steps + outScan.steps)) *
            addBitCost (8 * (pSub / 2)) =
          routingAndStreamingStepBitCost t1 r p' := by
        dsimp only [xRoutedRes, qHat_T_res, Z_flat_res, xRows_res, P_res, Q_res, qPost_res,
          stFlatQ, Y_res, stFlatZ, outScan]
        rw [runMultiTapeTransposeWithSteps_snd, runMultiTapeTransposeWithSteps_snd,
            runMultiTapeTransposeWithSteps_snd, hodd_steps,
            runScan2DWithSteps_snd, runScan2DWithSteps_snd,
            runScan2DWithSteps_snd, runScan2DWithSteps_snd,
            runFlatten2DSteps_steps, runScan2DWithSteps_snd,
            runFlatten2DSteps_steps, runSequentialScanSteps_steps,
            hm_t1, hm_r, ht1_pow, hr_pow, hp'_div]
        unfold routingAndStreamingStepBitCost sequentialTransposeBitCost
          sequentialColumnMergeSortBitCost sequentialLinearScanBitCost sequentialPassBitCost
        rw [sequentialTapeTransposeWithPasses_snd, sequentialTapeTransposeWithPasses_snd,
            sequentialAffineOddRouteWithPasses_snd]
        ring
      have hchild_sum :
          ((sumArrayCosts qHat_res : ℕ) : ℝ) =
            ∑ v1 ∈ Finset.range t1,
              (sincGaussianFastDFTQuantizedIntrinsicCost child (qPost v1)).2 := by
        dsimp only [qHat_res]
        have hnat :
            sumArrayCosts
              (Array.ofFn (fun v1 : Fin t1 =>
                computableExactFastDFTWithCost pSub cChild (qPost_mat.getD v1.val #[]))) =
            ∑ v1 ∈ Finset.range t1,
              (computableExactFastDFTWithCost pSub cChild (qPost_mat.getD v1 #[])).2 := by
          refine sumArrayCosts_ofFn_eq_sum t1 _ _ (fun v1 _ => rfl)
        rw [hnat, Nat.cast_sum]
        refine Finset.sum_congr rfl fun v1 hv1_mem => ?_
        have hv1 : v1 < t1 := Finset.mem_range.mp hv1_mem
        exact ih hchild_exec pSub (qPost_mat.getD v1 #[]) (qPost v1)
          (fun k hk => by
            have hk_r : k < r := hchild_size ▸ hk
            rw [read1D_array_getD_eq_read2D]
            exact (hqPost_eq v1 hv1 k hk_r).symm)
      have htwist :
          (t1 * r) * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) =
            twistAndSolverStepBitCost t1 r p' := rfl
      rw [hsyn_cost, hspread_cost, hsolver_steps, computableMulBitCost_eq, hrouting_cost, hp'_div, htwist]
      push_cast
      rw [hchild_sum]

/-- **Runtime-Cost-Instrumented Pure-Integer Computable End-to-End `FastDFT` Multiplier
(`computableExactFastDFTMultiplyWithCost`, `[MS]` §7)**:
100% computable (`def`, zero `noncomputable`, zero `Real`, zero `Complex`) integer multiplier
that splits the inputs via balanced binary-tree `splitChunksTree` into `Array ℕ` for $O(1)$ lookup,
executes the fixed-point `ℤ × ℤ` pipeline while accumulating its runtime bit-operation and
tape-head-step cost `(prod, cost) : ℕ × ℕ` directly from:
- `stPack := runSequentialScanSteps ... R0` (`stPack.steps * addBitCost p0`),
- `fwd := computableExactFastDFTWithCost b cSpec stPack.outTape` (`fwd.2`),
- `stSq := runSequentialScanSteps ... R0` (`stSq.steps * computableMulBitCost p0`),
- `inv := computableExactFastDFTWithCost p0 cSpec stSq.outTape` (`inv.2`),
- and `stExt := runSequentialScanSteps ... R0` (`2 * stExt.steps * addBitCost p0`),
and reconstructs the output via balanced binary-tree `reconstructChunksTree`. -/
def computableExactFastDFTMultiplyWithCost
    (cSpec : ComputableExactFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ × ℕ :=
  let R0 := 2 ^ K0
  let p0 := rootPrecision b K0
  let asArr := (splitChunksTree b k1 A).toArray
  let bsArr := (splitChunksTree b k2 B).toArray
  let stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  let fwd := computableExactFastDFTWithCost b cSpec stPack.outTape
  let stSq := runSequentialScanSteps (fun u =>
    gConj (gMulScaled (p0 + 2) (read1D fwd.1 u) (read1D fwd.1 u))) R0
  let inv := computableExactFastDFTWithCost p0 cSpec stSq.outTape
  let numScale : ℤ := ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ)
  let denScale : ℤ := 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ)
  let stExt := runSequentialScanSteps (fun j =>
    let imInt : ℤ := -(read1D inv.1 j).2
    (divRoundRatInt (imInt * numScale) denScale).toNat) R0
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j => read1D stExt.outTape j)
  let rootCost : ℕ :=
    stSq.steps * computableMulBitCost p0 + (stPack.steps + 2 * stExt.steps) * addBitCost p0
  (reconstructChunksTree b convNat, fwd.2 + inv.2 + rootCost)

/-- **Pure-Integer Computable End-to-End `FastDFT` Multiplier (`computableExactFastDFTMultiply`, `[MS]` §7)**:
First projection of `computableExactFastDFTMultiplyWithCost`. -/
def computableExactFastDFTMultiply
    (cSpec : ComputableExactFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ :=
  (computableExactFastDFTMultiplyWithCost cSpec b K0 k1 k2 A B).1

/-- **Exact Equivalence of `computableExactFastDFTMultiply` and `quantizedFastDFTMultiply`**: -/
theorem computableExactFastDFTMultiply_eq_quantizedFastDFTMultiply
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.ExecutableValid)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) :
    computableExactFastDFTMultiply (toComputableExactFastDFTSpec spec) b K0 k1 k2 A B =
      quantizedFastDFTMultiply spec b K0 k1 k2 A B := by
  unfold computableExactFastDFTMultiply computableExactFastDFTMultiplyWithCost quantizedFastDFTMultiply
  dsimp only
  rw [reconstructChunksTree_eq_reconstructChunks]
  apply congrArg (reconstructChunks b)
  refine List.map_congr_left fun j hj_mem => ?_
  have hj_lt : j < k1 + k2 := List.mem_range.mp hj_mem
  have hj_R0 : j < 2 ^ K0 := by omega
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set cSpec := toComputableExactFastDFTSpec spec
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computableExactFastDFTWithCost b cSpec stPack.outTape
  set stSq := runSequentialScanSteps (fun u =>
    gConj (gMulScaled (p0 + 2) (read1D fwd.1 u) (read1D fwd.1 u))) R0
  set inv := computableExactFastDFTWithCost p0 cSpec stSq.outTape
  rw [read1D_runSequentialScanSteps_eq _ R0 j hj_R0]
  have hy : ∀ u < R0, toScaledComplex p0 (read1D fwd.1 u) = sincGaussianFastDFTQuantized spec x_AB u := by
    intro u hu
    rw [← hp0]
    exact toScaledComplex_computableExactFastDFT_eq spec hvalid hexec b stPack.outTape x_AB
      (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
      u (hsize.symm ▸ hu)
  have hsConj : ∀ u < spec.size,
      star (complexQuantize p0 ((sincGaussianFastDFTQuantized spec x_AB u) ^ 2)) =
        toScaledComplex p0 (read1D stSq.outTape u) := by
    intro u hu
    have hu_R0 : u < R0 := hsize ▸ hu
    dsimp only [stSq]
    rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, toScaledComplex_gConj,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu_R0, sq]
  have hz : toScaledComplex p0 (read1D inv.1 j) =
      sincGaussianFastDFTQuantized spec
        (fun u => star (complexQuantize p0 ((sincGaussianFastDFTQuantized spec x_AB u) ^ 2))) j := by
    have h := toScaledComplex_computableExactFastDFT_eq spec hvalid hexec p0 stSq.outTape
      (fun u => star (complexQuantize p0 ((sincGaussianFastDFTQuantized spec x_AB u) ^ 2)))
      hsConj j (hsize.symm ▸ hj_R0)
    rwa [hp0] at h
  have hzim :
      (star (sincGaussianFastDFTQuantized spec
        (fun u => star (complexQuantize p0 ((sincGaussianFastDFTQuantized spec x_AB u) ^ 2))) j)).im =
      ((-(read1D inv.1 j).2 : ℤ) : ℝ) / (2 : ℝ) ^ (p0 + 2) := by
    rw [← hz, ← toScaledComplex_gConj]
    simp [toScaledComplex, gConj]
  unfold quantizedFastDFTConvApprox
  dsimp only
  rw [hzim]
  have hden_pos : (0 : ℤ) < 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ) := by positivity
  rw [divRoundRatInt_eq_floor _ _ hden_pos]
  congr 2
  have hzpow :
      (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) =
        (((2 ^ (2 * b + 2 * K0) : ℕ) : ℝ) / 2) := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    have hcast : (2 : ℤ) * (b : ℤ) + 2 * (K0 : ℤ) = ((2 * b + 2 * K0 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast, zpow_natCast]
    push_cast
    rfl
  rw [hzpow]
  have hpow_ne : (2 : ℝ) ^ (p0 + 2) ≠ 0 := by positivity
  push_cast
  field_simp [hpow_ne]

/-- **Exact Runtime Cost Equivalence of `computableExactFastDFTMultiplyWithCost` and `quantizedFastDFTMultiplyIntrinsicCost` (`[MS]` §§3.2, 3.4)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`, `hexec : spec.ExecutableValid`)
with `spec.size = 2 ^ K0` and `spec.p = rootPrecision b K0`, the integer runtime cost
`((computableExactFastDFTMultiplyWithCost (toComputableExactFastDFTSpec spec) b K0 k1 k2 A B).2 : ℝ)`
plus `(materializeSpecRawTablesWithCost spec).2` equals
`(quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2`. -/
theorem computableExactFastDFTMultiplyWithCost_snd_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.ExecutableValid)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0) :
    ((computableExactFastDFTMultiplyWithCost (toComputableExactFastDFTSpec spec) b K0 k1 k2 A B).2 : ℝ) +
      (materializeSpecRawTablesWithCost spec).2 =
      (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2 := by
  unfold computableExactFastDFTMultiplyWithCost quantizedFastDFTMultiplyIntrinsicCost
  dsimp only
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set cSpec := toComputableExactFastDFTSpec spec
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computableExactFastDFTWithCost b cSpec stPack.outTape
  set stSq := runSequentialScanSteps (fun u =>
    gConj (gMulScaled (p0 + 2) (read1D fwd.1 u) (read1D fwd.1 u))) R0
  set inv := computableExactFastDFTWithCost p0 cSpec stSq.outTape
  set numScale : ℤ := ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ)
  set denScale : ℤ := 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ)
  set stExt := runSequentialScanSteps (fun j =>
    let imInt : ℤ := -(read1D inv.1 j).2
    (divRoundRatInt (imInt * numScale) denScale).toNat) R0
  have hfwd_cost : (fwd.2 : ℝ) = (sincGaussianFastDFTQuantizedIntrinsicCost spec x_AB).2 :=
    computableExactFastDFTWithCost_snd_eq spec hvalid hexec b stPack.outTape x_AB
      (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
  have hy : ∀ u < R0, toScaledComplex p0 (read1D fwd.1 u) = sincGaussianFastDFTQuantized spec x_AB u := by
    intro u hu
    rw [← hp0]
    exact toScaledComplex_computableExactFastDFT_eq spec hvalid hexec b stPack.outTape x_AB
      (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
      u (hsize.symm ▸ hu)
  have hinv_cost :
      (inv.2 : ℝ) =
        (sincGaussianFastDFTQuantizedIntrinsicCost spec
          (fun u => star (complexQuantize p0 (((sincGaussianFastDFTQuantizedIntrinsicCost spec x_AB).1 u) ^ 2)))).2 := by
    refine computableExactFastDFTWithCost_snd_eq spec hvalid hexec p0 stSq.outTape _ (fun u hu => ?_)
    have hu_R0 : u < R0 := hsize ▸ hu
    dsimp only [stSq]
    rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, toScaledComplex_gConj,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu_R0, sq,
        sincGaussianFastDFTQuantizedIntrinsicCost_fst_eq]
  have hroot :
      stSq.steps * computableMulBitCost p0 + (stPack.steps + 2 * stExt.steps) * addBitCost p0 =
        rootPipelineBitCost R0 p0 := by
    dsimp only [stSq, stPack, stExt, rootPipelineBitCost]
    rw [computableMulBitCost_eq,
        runSequentialScanSteps_steps, runSequentialScanSteps_steps, runSequentialScanSteps_steps]
    ring
  rw [hroot]
  push_cast
  rw [hfwd_cost, hinv_cost, materializeSpecRawTablesWithCost_snd_eq]
  ring

/-- **Master End-to-End Correctness Theorem for `computableExactFastDFTMultiply` (`[MS]` §7)**:
For any valid multi-level specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`,
`hexec : spec.ExecutableValid`) with `spec.size = 2 ^ K0` and `spec.p = rootPrecision b K0`,
any `k1 + k2 ≤ 2 ^ K0`, and any natural numbers `A < (2 ^ b) ^ k1` and `B < (2 ^ b) ^ k2`,
the pure-integer computable pipeline `computableExactFastDFTMultiply` returns the exact product `A * B`. -/
theorem computableExactFastDFTMultiply_eq_mul
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.ExecutableValid)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    computableExactFastDFTMultiply (toComputableExactFastDFTSpec spec) b K0 k1 k2 A B = A * B := by
  rw [computableExactFastDFTMultiply_eq_quantizedFastDFTMultiply spec hvalid hexec b K0 k1 k2 A B hsize hp0 hk]
  exact quantizedFastDFTMultiply_eq_mul spec hvalid b K0 k1 k2 hsize hp0 hk A B hA hB

/-- **Cost-Instrumented Table Compiler (`toComputableExactFastDFTSpecWithCost`, `[MS]` §3.3 (Lemma 3.2, eq. (8)) & §6.1)**:
Compiles a `QuantizedFastDFTSpec` into its pure-integer `ComputableExactFastDFTSpec` tables while
accumulating the table-generation and tap-folding bit-operation cost directly from the `.steps`
counters of the executed `runSequentialScanSteps` machines for the raw window taps (`t1 * (4 * p' + 1)`
evaluations) and the 4 length-`r` twiddle/passband tables (`preTwiddles`, `postTwiddles`, `c0Table`,
`c1Table`, totaling `4 * r` evaluations). -/
noncomputable def toComputableExactFastDFTSpecWithCost :
    QuantizedFastDFTSpec → ComputableExactFastDFTSpec × ℝ
  | .base p R => (.base p R, 0)
  | .step p K t1 r _c1 _v1Of child =>
    let p' := pChild p K
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * p'
    let filterTaps : Array (List ℤ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1.val)
    let preTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2 : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).re,
         realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).im))
    let postTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2 : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).re,
         realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).im))
    let c0Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r =>
        (realQuantizeInt pSub (c0Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
    let c1Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r =>
        (realQuantizeInt pSub (c1Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
    let stRawTaps := runSequentialScanSteps (fun idx =>
      let j1 := idx / (4 * p' + 1)
      let m : ℤ := ((idx % (4 * p' + 1) : ℕ) : ℤ) - (2 * p' : ℤ)
      quantizeInt pSub (sincGaussian α ((m : ℝ) + (j1 : ℝ) / (t1 : ℝ)))) (t1 * (4 * p' + 1))
    let stPre := runSequentialScanSteps (read1D preTwiddles) r
    let stPost := runSequentialScanSteps (read1D postTwiddles) r
    let stC0 := runSequentialScanSteps (read1D c0Table) r
    let stC1 := runSequentialScanSteps (read1D c1Table) r
    let twiddleSteps := stPre.steps + stPost.steps + stC0.steps + stC1.steps
    let stepCost : ℕ :=
      (stRawTaps.steps + twiddleSteps) * (4 * p' + 1) *
        (mulBitCost (4 * p') + addBitCost (4 * p')) +
      stRawTaps.steps * addBitCost (4 * p')
    let childRes := toComputableExactFastDFTSpecWithCost child
    (.step p pSub pSub t1 r filterTaps preTwiddles postTwiddles c0Table c1Table childRes.1,
     ((stepCost : ℕ) : ℝ) + childRes.2)

@[simp]
theorem toComputableExactFastDFTSpecWithCost_fst_eq (spec : QuantizedFastDFTSpec) :
    (toComputableExactFastDFTSpecWithCost spec).1 = toComputableExactFastDFTSpec spec := by
  induction spec with
  | base p R => rfl
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [toComputableExactFastDFTSpecWithCost, toComputableExactFastDFTSpec]
    rw [ih]

@[simp]
theorem toComputableExactFastDFTSpecWithCost_snd_eq (spec : QuantizedFastDFTSpec) :
    (toComputableExactFastDFTSpecWithCost spec).2 = spec.precomputeRawTapCost := by
  induction spec with
  | base p R => rfl
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [toComputableExactFastDFTSpecWithCost, QuantizedFastDFTSpec.precomputeRawTapCost,
      precomputeStepRawTapBitCost]
    simp only [runSequentialScanSteps_steps, ih]
    have h4r : r + r + r + r = 4 * r := by ring
    rw [h4r]

/-- **Parameter-Free Runtime-Cost-Instrumented Pure-Integer Multiplication Wrapper
(`computableExactMultiplyOfBitLengthWithCost`, `[MS]` §7)**:
Compiles `(cSpec, tableCost) := toComputableExactFastDFTSpecWithCost (buildQuantizedSpec L p0 K0)`
and executes `computableExactFastDFTMultiplyWithCost cSpec` on that exact compiled `cSpec`,
accumulating `(mulRes.2 : ℝ) + tableCost` directly from `computableExactFastDFTMultiplyWithCost`
and `toComputableExactFastDFTSpecWithCost` (with zero discarded `.1` and zero reference to
`quantizedMultiplyOfBitLength`). -/
noncomputable def computableExactMultiplyOfBitLengthWithCost (n A B : ℕ) : ℕ × ℝ :=
  let b := max 1 (Nat.log2 n)
  let k := n / b + 1
  let K0 := max 4 (Nat.log2 (2 * k) + 2)
  let L := Nat.log2 (K0 - 1)
  let p0 := rootPrecision b K0
  let spec := buildQuantizedSpec L p0 K0
  let cSpecRes := toComputableExactFastDFTSpecWithCost spec
  let mulRes := computableExactFastDFTMultiplyWithCost cSpecRes.1 b K0 k k A B
  (mulRes.1, (mulRes.2 : ℝ) + cSpecRes.2)

/-- **Parameter-Free Pure-Integer Multiplication Wrapper (`computableExactMultiplyOfBitLength`, `[MS]` §7)**:
First projection of `computableExactMultiplyOfBitLengthWithCost`. -/
noncomputable def computableExactMultiplyOfBitLength (n A B : ℕ) : ℕ :=
  (computableExactMultiplyOfBitLengthWithCost n A B).1

theorem computableExactMultiplyOfBitLengthWithCost_eq_quantizedMultiplyOfBitLength
    (n A B : ℕ) :
    computableExactMultiplyOfBitLengthWithCost n A B =
      quantizedMultiplyOfBitLength n A B := by
  unfold computableExactMultiplyOfBitLengthWithCost quantizedMultiplyOfBitLength
  dsimp only
  rw [toComputableExactFastDFTSpecWithCost_fst_eq, toComputableExactFastDFTSpecWithCost_snd_eq]
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set spec := buildQuantizedSpec L p0 K0
  have hK0_ge4 : 4 ≤ K0 := le_max_left 4 (Nat.log2 (2 * k) + 2)
  have hp0 : 8 ≤ p0 := by dsimp [p0, rootPrecision]; omega
  have h2L_le_K0 : 2 ^ L ≤ K0 :=
    (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
  have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
    have hlt : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
    omega
  have hvalid : spec.Valid := buildQuantizedSpec_valid L p0 K0 hp0 h2L_le_K0
  have hexec : spec.ExecutableValid := buildQuantizedSpec_executableValid L p0 K0 hK0_le_2L1
  have hsize : spec.size = 2 ^ K0 := buildQuantizedSpec_size L p0 K0
  have hspec_p : spec.p = p0 := buildQuantizedSpec_p L p0 K0
  have hk : k + k ≤ 2 ^ K0 := by
    have hlt := lt_two_pow_log2_succ (2 * k)
    have hle_exp : Nat.log2 (2 * k) + 1 ≤ K0 := by
      have : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
      omega
    have hpow_le : 2 ^ (Nat.log2 (2 * k) + 1) ≤ 2 ^ K0 :=
      Nat.pow_le_pow_right zero_lt_two hle_exp
    omega
  ext
  · change computableExactFastDFTMultiply (toComputableExactFastDFTSpec spec) b K0 k k A B = _
    rw [computableExactFastDFTMultiply_eq_quantizedFastDFTMultiply spec hvalid hexec b K0 k k A B hsize hspec_p hk,
        quantizedFastDFTMultiplyIntrinsicCost_fst_eq]
  · rw [← materializeSpecRawTablesWithCost_snd_eq]
    exact computableExactFastDFTMultiplyWithCost_snd_eq spec hvalid hexec b K0 k k A B hsize hspec_p

/-- **Master Correctness Theorem for `computableExactMultiplyOfBitLength` (`[MS]` §7)**:
For all `n, A, B : ℕ` with `A < 2 ^ n` and `B < 2 ^ n`,
`computableExactMultiplyOfBitLength n A B = A * B`. -/
theorem computableExactMultiplyOfBitLength_eq_mul (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableExactMultiplyOfBitLength n A B = A * B := by
  unfold computableExactMultiplyOfBitLength
  rw [computableExactMultiplyOfBitLengthWithCost_eq_quantizedMultiplyOfBitLength]
  exact quantizedMultiplyOfBitLength_fst_eq_mul n A B hA hB

/-- **Unified Correctness and $O(n \log n)$ Runtime Complexity of the Pure-Integer Computable Multiplier
(`computableExactMultiplyOfBitLengthWithCost_correct_and_isBigO`, `[MS]` §7)**:
1. For all `n, A, B : ℕ` with `A < 2 ^ n` and `B < 2 ^ n`,
   `(computableExactMultiplyOfBitLengthWithCost n A B).1 = A * B`,
2. For all `n` with `96 ≤ Nat.log2 n`,
   `(computableExactMultiplyOfBitLengthWithCost n A B).2 ≤ 7840335360 * (n * log n)`,
3. For all `16 ≤ n`,
   `(computableExactMultiplyOfBitLengthWithCost n A B).2 ≤ 54317320874319360 * (n * log n)`,
4. For any `A, B : ℕ → ℕ`, the runtime bit-operation and tape-head-step cost
   `(computableExactMultiplyOfBitLengthWithCost n (A n) (B n)).2` accumulated bottom-up from the
   100% computable fixed-point `ℤ × ℤ` array program and its `.steps`-instrumented multitape state
   machines is $O(n \log n)$ as $n \to \infty$. -/
theorem computableExactMultiplyOfBitLengthWithCost_correct_and_isBigO :
    (∀ n A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      (computableExactMultiplyOfBitLengthWithCost n A B).1 = A * B) ∧
    (∀ n A B : ℕ, 96 ≤ Nat.log2 n →
      (computableExactMultiplyOfBitLengthWithCost n A B).2 ≤
        (7840335360 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) ∧
    (∀ n A B : ℕ, 16 ≤ n →
      (computableExactMultiplyOfBitLengthWithCost n A B).2 ≤
        (54317320874319360 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) ∧
    (∀ A B : ℕ → ℕ,
      (fun n : ℕ => (computableExactMultiplyOfBitLengthWithCost n (A n) (B n)).2) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))) := by
  simp only [computableExactMultiplyOfBitLengthWithCost_eq_quantizedMultiplyOfBitLength,
    ← quantizedMultiplyOfBitLengthMaterialized_eq_quantizedMultiplyOfBitLength]
  exact quantizedMultiplyOfBitLengthMaterialized_correct_and_isBigO

/-! ### Table-Perturbation Stability Bound (`[MS]` §3.3, Lemma 3.2) -/

/-- **Twiddle-Table Perturbation Operator Bound (`norm_twiddle_table_perturbation_le`, `[MS]` §3.3, Lemma 3.2)**:
For any spread/butterfly entry `u : ℂ` with `‖u‖ ≤ ((r : ℝ) + 1) * M` and any approximate vs. exact
twiddle factor `ζ_approx, ζ_exact : ℂ` with `‖ζ_approx - ζ_exact‖ ≤ ε_tab`, the perturbed product
satisfies `‖u * ζ_approx - u * ζ_exact‖ ≤ ((r : ℝ) + 1) * M * ε_tab`. -/
theorem norm_twiddle_table_perturbation_le
    (r : ℕ) (M ε_tab : ℝ) (u ζ_approx ζ_exact : ℂ)
    (hM : 0 ≤ M) (hu : ‖u‖ ≤ ((r : ℝ) + 1) * M) (hζ : ‖ζ_approx - ζ_exact‖ ≤ ε_tab) :
    ‖u * ζ_approx - u * ζ_exact‖ ≤ ((r : ℝ) + 1) * M * ε_tab := by
  have hsub : u * ζ_approx - u * ζ_exact = u * (ζ_approx - ζ_exact) := by ring
  rw [hsub, norm_mul]
  exact mul_le_mul hu hζ (norm_nonneg _) (by positivity)

/-- **Folded-Spread-Tap Table Perturbation Operator Bound (`norm_spread_row_table_perturbation_le`, `[MS]` §3.3, Lemma 3.2)**:
For any row `x : ℕ → ℂ` bounded by `∀ m < r, ‖x m‖ ≤ M` and any approximate vs. exact folded filter
taps `g_approx, g_exact : ℕ → ℂ` with `∀ m < r, ‖g_approx m - g_exact m‖ ≤ ε_tab`, the perturbed
row spread sum satisfies
`‖∑ m ∈ Finset.range r, x m * g_approx m - ∑ m ∈ Finset.range r, x m * g_exact m‖ ≤ (r : ℝ) * M * ε_tab`. -/
theorem norm_spread_row_table_perturbation_le
    (r : ℕ) (M ε_tab : ℝ) (x g_approx g_exact : ℕ → ℂ)
    (hM : 0 ≤ M)
    (hx : ∀ m < r, ‖x m‖ ≤ M)
    (hg : ∀ m < r, ‖g_approx m - g_exact m‖ ≤ ε_tab) :
    ‖∑ m ∈ Finset.range r, x m * g_approx m - ∑ m ∈ Finset.range r, x m * g_exact m‖ ≤
      (r : ℝ) * M * ε_tab := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ m ∈ Finset.range r, (x m * g_approx m - x m * g_exact m)‖
      ≤ ∑ m ∈ Finset.range r, ‖x m * g_approx m - x m * g_exact m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range r, (M * ε_tab) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hm_lt : m < r := Finset.mem_range.mp hm
        have hsub : x m * g_approx m - x m * g_exact m = x m * (g_approx m - g_exact m) := by ring
        rw [hsub, norm_mul]
        exact mul_le_mul (hx m hm_lt) (hg m hm_lt) (norm_nonneg _) hM
    _ = (r : ℝ) * M * ε_tab := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- **Single-Step Table-Perturbation Arithmetic Bound (`table_perturbation_single_step_bound`, `[MS]` §3.3, Lemma 3.2)**:
For $t_1, r \le 2^K$ and $p' = p_{\text{child}}(p, K) \ge 2 K + 8$, the exponent scaling identity
$$((r : \mathbb{R}) + 8 t_1^2) \cdot (2 : \mathbb{R})^{-(2 p' : \mathbb{Z})} \le \frac{1}{8} (2 : \mathbb{R})^{-(p' : \mathbb{Z})}$$
holds unconditionally. -/
theorem table_perturbation_single_step_bound
    (K p' t1 r : ℕ) (ht1 : t1 ≤ 2 ^ K) (hr : r ≤ 2 ^ K) (hp' : 2 * K + 8 ≤ p') :
    ((r : ℝ) + 8 * (t1 : ℝ) ^ 2) * (2 : ℝ) ^ (-(2 * p' : ℤ)) ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(p' : ℤ)) := by
  have hr_r : (r : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast hr
  have ht1_r : (t1 : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast ht1
  have h2K_pos : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
  have ht1_sq : (t1 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * K) := by
    calc (t1 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ K) ^ 2 := sq_le_sq' (by linarith) ht1_r
      _ = (2 : ℝ) ^ (2 * K) := by rw [← pow_mul, mul_comm]
  have hr_le_2K : (r : ℝ) ≤ (2 : ℝ) ^ (2 * K) := by
    calc (r : ℝ) ≤ (2 : ℝ) ^ K := hr_r
      _ ≤ (2 : ℝ) ^ (2 * K) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum_le : (r : ℝ) + 8 * (t1 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * K + 4) := by
    have hpow4 : (2 : ℝ) ^ (2 * K + 4) = 16 * (2 : ℝ) ^ (2 * K) := by
      rw [pow_add]
      norm_num
      ring
    linarith
  have hexp_le : (2 * K + 4 : ℤ) - (2 * p' : ℤ) ≤ -(p' : ℤ) - 3 := by omega
  calc ((r : ℝ) + 8 * (t1 : ℝ) ^ 2) * (2 : ℝ) ^ (-(2 * p' : ℤ))
      ≤ (2 : ℝ) ^ (2 * K + 4) * (2 : ℝ) ^ (-(2 * p' : ℤ)) := by
        exact mul_le_mul_of_nonneg_right hsum_le (by positivity)
    _ = (2 : ℝ) ^ ((2 * K + 4 : ℤ) - (2 * p' : ℤ)) := by
        rw [← zpow_natCast (2 : ℝ) (2 * K + 4), ← zpow_add₀ (by norm_num)]
        push_cast
        ring_nf
    _ ≤ (2 : ℝ) ^ (-(p' : ℤ) - 3) :=
        zpow_le_zpow_right₀ (by norm_num) hexp_le
    _ = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(p' : ℤ)) := by
        rw [zpow_sub₀ (by norm_num)]
        norm_num
        ring

/-- **Conditional Triangle-Inequality Closure for Table Perturbation
(`table_perturbation_absorbed_by_step_error_closure`, `[MS]` §3.3, Lemma 3.2)**:
Assuming (`hpert`) that a perturbed step output `Z_pert` deviates from the unperturbed quantized
step output `Z_quant` by at most `((r : ℝ) + 8 * (t1 : ℝ) ^ 2) * 2 ^ (-(2 * pChild p K : ℤ)) * M`,
and given `‖Z_quant - dft_exact‖ < 0.394 * 2^(-p) * M` (`hquant`), `Z_pert` satisfies
`‖Z_pert - dft_exact‖ < (0.519 : ℝ) * 2 ^ (-(p : ℤ)) * M < 2 ^ (-(p : ℤ)) * M`. -/
theorem table_perturbation_absorbed_by_step_error_closure
    (p K t1 r : ℕ) (M : ℝ) (Z_pert Z_quant dft_exact : ℂ)
    (ht1 : t1 ≤ 2 ^ K) (hr : r ≤ 2 ^ K) (hM : 0 < M)
    (hquant : ‖Z_quant - dft_exact‖ < (0.394 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M)
    (hpert : ‖Z_pert - Z_quant‖ ≤
      (((r : ℝ) + 8 * (t1 : ℝ) ^ 2) * (2 : ℝ) ^ (-(2 * (pChild p K : ℤ)))) * M) :
    ‖Z_pert - dft_exact‖ < (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hp' : 2 * K + 8 ≤ pChild p K := by unfold pChild pWork; omega
  have hp_le_p' : p ≤ pChild p K := by unfold pChild pWork; omega
  have htab := table_perturbation_single_step_bound K (pChild p K) t1 r ht1 hr hp'
  have hzpow_le : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ (2 : ℝ) ^ (-(p : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpert_le : ‖Z_pert - Z_quant‖ ≤ (0.125 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    calc ‖Z_pert - Z_quant‖
        ≤ (((r : ℝ) + 8 * (t1 : ℝ) ^ 2) * (2 : ℝ) ^ (-(2 * (pChild p K : ℤ)))) * M := hpert
      _ ≤ ((1 / 8 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) * M :=
          mul_le_mul_of_nonneg_right htab hM.le
      _ ≤ ((1 / 8 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzpow_le (by norm_num)) hM.le
      _ = (0.125 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by ring
  have htri : ‖Z_pert - dft_exact‖ ≤ ‖Z_pert - Z_quant‖ + ‖Z_quant - dft_exact‖ := by
    simpa using norm_add_le (Z_pert - Z_quant) (Z_quant - dft_exact)
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M :=
    mul_pos (zpow_pos (by norm_num) _) hM
  linarith

/-- Kernel-verified check that `rootPrecision 4 3 = 20`. -/
theorem rootPrecision_four_three_eq : rootPrecision 4 3 = 20 := rfl

/-- Concrete 2-level `ComputableExactFastDFTSpec` at root length `R0 = 8` (`b = 4`, `K0 = 3`,
`p = rootPrecision 4 3 = 20`, `pSub = 28`, `m1 = 24`, `t1 = 2`, `r = 4`, `α = 4`), carrying the
pre-folded Sinc-Gaussian filter taps and quantized passband coefficients `c0`, `c1`, and exercising
the verified `computableExactFastDFTWithCost` pipeline (`computableSpreadRowContiguousWithCost`,
`computableSyntheticFFTRadix2WithCost`, `runFlatten2DSteps`, `runMultiTapeTransposeWithSteps`,
`runMultiTapeAffineOddRouteWithSteps`, `computableBaseDFTExact`, and all three solver regimes
`computableSolveBidiagonalFwdExactWithSteps`, `computableSolveNyquistExactWithSteps`,
`computableSolveBidiagonalBwdExactWithSteps`). -/
def demoTwoLevelComputableExactSpec : ComputableExactFastDFTSpec :=
  let p0 := rootPrecision 4 3
  let pSub := 28
  let s2 : ℤ := 759250125 -- round(2^(pSub + 2) * √2 / 2) at pSub + 2 = 30
  let childSpec := ComputableExactFastDFTSpec.base pSub 4
  let filterTaps : Array (List ℤ) :=
    #[[268435456, 0, 0, 0],
      [160858257, 160858257, -26640672, -26640672]]
  let preTwiddles : Array (ℤ × ℤ) :=
    Array.ofFn (fun k2 : Fin 4 => eighthRootScaled (pSub + 2) s2 k2.val)
  let postTwiddles : Array (ℤ × ℤ) :=
    Array.ofFn (fun k2 : Fin 4 => eighthRootScaled (pSub + 2) s2 (8 - k2.val))
  let c0Table : Array (ℤ × ℤ) :=
    #[(1073741249, 0), (1067197968, 0), (536870912, 0), (6543856, 0)]
  let c1Table : Array (ℤ × ℤ) :=
    #[(287, 0), (6543856, 0), (536870912, 0), (1067197968, 0)]
  ComputableExactFastDFTSpec.step p0 pSub 24 2 4 filterTaps preTwiddles postTwiddles c0Table c1Table childSpec

/-- **Kernel-Verified Execution Test 2 (`computableExactSolvers_three_regimes_test`)**:
Verifies `computableSolveBidiagonalFwdExactWithSteps`, `computableSolveNyquistExactWithSteps`, and
`computableSolveBidiagonalBwdExactWithSteps` (and their `.steps` counters) in the Lean kernel via `decide`. -/
theorem computableExactSolvers_three_regimes_test :
    let q := 8 -- scale = 2^(q + 2) = 1024
    let S : ℤ := 1024
    let c0 : ℤ × ℤ := (S, 0)
    let c1_fwd : ℤ × ℤ := (S / 2, 0)
    let c0_bwd : ℤ × ℤ := (S / 2, 0)
    let c1_bwd : ℤ × ℤ := (S, 0)
    let Z_true : Array (ℤ × ℤ) := #[(2048, 0), (1024, 0)]
    let Y_fwd : Array (ℤ × ℤ) := #[(2560, 0), (2048, 0)]
    let Y_nyq : Array (ℤ × ℤ) := #[(3072, 0), (3072, 0)]
    let Y_bwd : Array (ℤ × ℤ) := #[(2048, 0), (2560, 0)]
    computableSolveBidiagonalFwdExactWithSteps q 2 c0 c1_fwd Y_fwd = (Z_true, 2) ∧
    computableSolveNyquistExactWithSteps q 2 c0 Y_nyq (1024, 0) = (Z_true, 2) ∧
    computableSolveBidiagonalBwdExactWithSteps q 2 c0_bwd c1_bwd Y_bwd = (Z_true, 2) := by
  decide

set_option maxRecDepth 200000 in
/-- **Kernel-Verified Execution Test 3 (`computableExactFastDFTMultiply_two_level_test`)**:
Executes the verified `computableExactFastDFTMultiplyWithCost` on the 2-level `demoTwoLevelComputableExactSpec`
(`t1 = 2, r = 4, R0 = 8`, exercising `computableSpreadRowContiguousWithCost`, `computableSyntheticFFTRadix2WithCost`,
`runFlatten2DSteps`, `runMultiTapeTransposeWithSteps`, `runMultiTapeAffineOddRouteWithSteps`,
`computableBaseDFTExact`, and all 3 solver regimes `computableSolveBidiagonalFwdExactWithSteps`,
`computableSolveNyquistExactWithSteps`, `computableSolveBidiagonalBwdExactWithSteps`)
on multi-chunk integer multiplications and verifies both exact product recovery and positive bottom-up
runtime cost accumulation in the Lean kernel via `decide`. -/
theorem computableExactFastDFTMultiply_two_level_test :
    computableExactFastDFTMultiply demoTwoLevelComputableExactSpec 4 3 4 4 12345 56789 = 12345 * 56789 ∧
    computableExactFastDFTMultiply demoTwoLevelComputableExactSpec 4 3 4 4 54321 9876 = 54321 * 9876 ∧
    computableExactFastDFTMultiply demoTwoLevelComputableExactSpec 4 3 4 4 65535 65535 = 65535 * 65535 ∧
    0 < (computableExactFastDFTMultiplyWithCost demoTwoLevelComputableExactSpec 4 3 4 4 12345 56789).2 := by
  decide

end IntMul
