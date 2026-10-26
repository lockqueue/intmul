import IntMul.MaterializedAndComputable.ProgramCostPrimitives

/-!
# Part 2 — Paper-Stop `BaseRadix2FFT` Computable Pipeline
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance 10000] instZeroIntElementary

/-- Structural predicate certifying that a `QuantizedFastDFTSpec` uses the canonical odd-stride
routing `v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1` at internal steps and has power-of-two
leaf size `R = 2 ^ K` with `8 ≤ p` and `K ≤ 5 * p` at `.base p (2 ^ K)` (`PaperExecutableValid`). -/
inductive QuantizedFastDFTSpec.PaperExecutableValid : QuantizedFastDFTSpec → Prop where
  | base {p K : ℕ} (hp : 8 ≤ p) (hK : K ≤ 5 * p) :
      QuantizedFastDFTSpec.PaperExecutableValid (.base p (2 ^ K))
  | step {p K t1 r c1 : ℕ} {v1Of : ℕ → ℕ → ℕ} {child : QuantizedFastDFTSpec}
      (hv1_eq : ∀ u2 u1 : ℕ, v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1)
      (hchild : child.PaperExecutableValid) :
      QuantizedFastDFTSpec.PaperExecutableValid (.step p K t1 r c1 v1Of child)

theorem QuantizedFastDFTSpec.PaperExecutableValid.toBasePow2
    {spec : QuantizedFastDFTSpec} (hexec : spec.PaperExecutableValid) :
    spec.BasePow2 := by
  induction hexec with
  | @base p K _ _ =>
    dsimp [QuantizedFastDFTSpec.BasePow2]
    rw [nat_log2_two_pow]
  | step _ _ ih =>
    exact ih

/-- Every schedule built by the paper's stopping rule `buildQuantizedSpecPaperStop L p K`
(`2 ^ K ≤ 4 * p ^ 2`) with `8 ≤ p` and `K ≤ 2 ^ (L + 1)` satisfies `PaperExecutableValid`. -/
theorem buildQuantizedSpecPaperStop_paperExecutableValid
    (L p K : ℕ) (hp : 8 ≤ p) (hK : K ≤ 2 ^ (L + 1)) :
    (buildQuantizedSpecPaperStop L p K).PaperExecutableValid := by
  induction L generalizing p K with
  | zero =>
    dsimp only [buildQuantizedSpecPaperStop]
    have hK_le : K ≤ 2 := by simpa using hK
    exact QuantizedFastDFTSpec.PaperExecutableValid.base hp (by omega)
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · have hK_bound := log_len_add_one_le_of_two_pow_le_four_mul_sq K p hstop
      have hlog_le_p : Nat.log2 p ≤ p := by
        have h1 : Nat.log2 p < 2 ^ (Nat.log2 p) := Nat.lt_two_pow_self
        have h2 : 2 ^ (Nat.log2 p) ≤ p := two_pow_log2_le p (by omega)
        omega
      exact QuantizedFastDFTSpec.PaperExecutableValid.base hp (by omega)
    · dsimp only [quantizedBoxGaussianStepSpec]
      have hpow : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
      have hp_child : 8 ≤ pChild p K := by unfold pChild pWork; omega
      refine QuantizedFastDFTSpec.PaperExecutableValid.step
        (fun u2 u1 => by
          rw [Nat.log2_two_pow, routedOddStrideIndex_eq_oddStrideInvPow2])
        (ih (pChild p K) (K - K / 2) hp_child (by omega))

/-- Pure-integer multi-level specification for the paper-stopping `BaseRadix2FFT` pipeline
(`ComputablePaperFastDFTSpec`, `[MS]` §7):
carries precomputed radix-2 Cooley-Tukey leaf twiddle tables `twiddles : Array (Array (ℤ × ℤ))`
at `.basePow2 p K twiddles` and the pre-folded integer Sinc-Gaussian filter taps, pre/post-twiddles,
and passband tables `c0Table, c1Table` at `.step`. Contains zero `Real` or `Complex` fields. -/
inductive ComputablePaperFastDFTSpec where
  | basePow2 (p K : ℕ) (twiddles : Array (Array (ℤ × ℤ))) : ComputablePaperFastDFTSpec
  | step (p pSub m1 t1 r : ℕ)
      (filterTaps : Array (List ℤ))
      (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
      (child : ComputablePaperFastDFTSpec) : ComputablePaperFastDFTSpec

/-- Target output precision `p` of a `ComputablePaperFastDFTSpec`. -/
def ComputablePaperFastDFTSpec.p : ComputablePaperFastDFTSpec → ℕ
  | .basePow2 p _ _ => p
  | .step p _ _ _ _ _ _ _ _ _ _ => p

/-- Mathematical reference table specification (`idealRoundedPaperTables`, `[MS]` §§3.3, 6.1 & 7):
populates the exact-rounded `ComputablePaperFastDFTSpec` tables via `realQuantizeInt`.
This `noncomputable` reference is never executed; it serves purely as the zero-perturbation
reference instance of `TablesFaithful` (`idealRoundedPaperTables_faithful`). -/
noncomputable def idealRoundedPaperTables : QuantizedFastDFTSpec → ComputablePaperFastDFTSpec
  | .base p R =>
    let K := Nat.log2 R
    let q_leaf := 2 * p + K + 8
    let twiddles : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun s : Fin K =>
        Array.ofFn (fun u : Fin (2 ^ (s.val + 1)) =>
          (realQuantizeInt q_leaf (stdChar ((u.val : ℝ) / ((2 ^ (s.val + 1) : ℕ) : ℝ))).re,
           realQuantizeInt q_leaf (stdChar ((u.val : ℝ) / ((2 ^ (s.val + 1) : ℕ) : ℝ))).im)))
    .basePow2 p K twiddles
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
      (idealRoundedPaperTables child)

@[simp]
theorem idealRoundedPaperTables_p (spec : QuantizedFastDFTSpec) :
    (idealRoundedPaperTables spec).p = spec.p := by
  cases spec <;> rfl

/-- **Program-Cost-Accumulating Pure-Integer Computable `FastDFT` with `BaseRadix2FFT` Leaves
(`computablePaperFastDFTWithProgramCost`, `[MS]` §7)**:
100% computable (`def`, zero `noncomputable`, zero `Real`, zero `Complex`) recursive fixed-point
Gaussian-integer (`ℤ × ℤ`) transform that:
1. Executes `computableBaseRadix2FFTWithProgramCost` at `.basePow2 p K twiddles` leaves,
2. Executes `runMultiTapeTransposeFullSteps` and `runMultiTapeAffineOddRouteFullSteps` (including
   the `m = 0` base scan steps) for all 2D transposes and odd-stride column routes,
3. Executes `computableSpreadRowContiguousWithProgramCost` (including input block quantization and
   single-pass `overlapAddBucketsSinglePass` bucket accumulation),
4. Charges pre-twist (`costedGPreTwistU`) and post-twist (`costedGMulScaled`) at their true operand
   width `6 * p'`,
5. Executes `computableNyquistAltSumContiguousWithProgramCost` and the full internal solver
   routines `computableSolveBidiagonalFwdWithProgramCost`, `computableSolveNyquistWithProgramCost`,
   and `computableSolveBidiagonalBwdWithProgramCost` (at their true operand widths `10 * p'` and
   `22 * p'` and including all reversal/seek steps in `runBwdRevSteps` and `runReverseSteps`),
accumulating every subroutine's runtime cost directly into `.2`. -/
def computablePaperFastDFTWithProgramCost :
    ℕ → ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) × ℕ
  | p_in, .basePow2 p K twiddles, xArr =>
    computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr
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
        computablePaperFastDFTWithProgramCost pSub child (qPost_mat.getD v1.val #[]))
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

/-- First projection of `computablePaperFastDFTWithProgramCost` (`computablePaperFastDFT`, `[MS]` §7). -/
def computablePaperFastDFT
    (p_in : ℕ) (cSpec : ComputablePaperFastDFTSpec) (xArr : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (computablePaperFastDFTWithProgramCost p_in cSpec xArr).1

theorem toScaledComplex_Z_cols_paper_step_eq
    (pSub p' t1 r : ℕ) (c0Table c1Table : Array (ℤ × ℤ)) (Y_mat : Array (Array (ℤ × ℤ)))
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
          computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col
        else if 2 * u2'.val = r then
          computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q
        else
          computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col)
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
  · rw [computableSolveBidiagonalFwdWithProgramCost_fst,
        toScaledComplex_computableSolveBidiagonalFwdExact_eq pSub t1 _ _ _ u1 hu1, hc0, hc1]
    refine solveBidiagonalFwdQuantized_congr_lt pSub t1 c0_c c1_c _ Y_c (fun k hk => ?_) u1 hu1
    rw [read1D_array_getD_eq_read2D]
    exact hY k hk
  · rw [computableSolveNyquistWithProgramCost_fst,
        toScaledComplex_computableSolveNyquistExact_eq pSub t1 _ _ _ u1 hu1, hc0, halt]
    refine solveNyquistQuantized_congr_lt pSub t1 c0_c _ Y_c alt_c (fun k hk => ?_) u1 hu1
    rw [read1D_array_getD_eq_read2D]
    exact hY k hk
  · rw [computableSolveBidiagonalBwdWithProgramCost_fst,
        toScaledComplex_computableSolveBidiagonalBwdExact_eq pSub t1 _ _ _ u1 hu1, hc0, hc1]
    refine solveBidiagonalBwdQuantized_congr_lt pSub t1 c0_c c1_c _ Y_c (fun k hk => ?_) u1 hu1
    rw [read1D_array_getD_eq_read2D]
    exact hY k hk

set_option backward.dsimp.instances true in
/-- **Master End-to-End Semantic Equivalence of `computablePaperFastDFT` and `sincGaussianFastDFTRadix2Leaf`
(`toScaledComplex_computablePaperFastDFT_eq`, `[MS]` §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`, `hexec : spec.PaperExecutableValid`),
any input precision `p_in : ℕ`, any integer array `xArr : Array (ℤ × ℤ)` and functional input
`x : ℕ → ℂ` with `∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k)`, and any output
frequency `u < spec.size`, dequantizing the pure-integer output of `computablePaperFastDFT` equals
`sincGaussianFastDFTRadix2Leaf spec x u` identically. -/
theorem toScaledComplex_computablePaperFastDFT_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < spec.size) :
    toScaledComplex spec.p
      (read1D (computablePaperFastDFT p_in (idealRoundedPaperTables spec) xArr) u) =
      sincGaussianFastDFTRadix2Leaf spec x u := by
  unfold computablePaperFastDFT
  induction hvalid generalizing p_in xArr x u with
  | base p R =>
    cases hexec with
    | @base p K hp hK_le =>
      dsimp only [idealRoundedPaperTables, computablePaperFastDFTWithProgramCost,
        sincGaussianFastDFTRadix2Leaf, QuantizedFastDFTSpec.p]
      dsimp only [QuantizedFastDFTSpec.size] at hx hu
      rw [nat_log2_two_pow]
      refine toScaledComplex_computableBaseRadix2FFTWithProgramCost_eq p_in p K _ ?_
        xArr x hx u hu
      intro s hs u' hu'
      rw [array_getD_ofFn_of_lt K _ #[] s hs, read1D_ofFn_of_lt (2 ^ (s + 1)) _ hu']
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hexec with
    | step hv1_eq hchild_exec =>
      dsimp only [idealRoundedPaperTables, sincGaussianFastDFTRadix2Leaf, QuantizedFastDFTSpec.p]
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
      set cChild := idealRoundedPaperTables child
      dsimp only [computablePaperFastDFTWithProgramCost, runScan2DCostedWithSteps,
        runSequentialScanCostedSteps, costedGPreTwistU, costedGRescale, costedGMulScaled]
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
          computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
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
          computablePaperFastDFTWithProgramCost pSub cChild (qPost_mat.getD v1.val #[]))
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
      set U := kroneckerSincGaussianSpreadArray α pSub pSub t1 r x
      set P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
      set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
      set qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTRadix2Leaf child (qPost v1) u2
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
            array_getD_ofFn_of_lt t1 _ [] j1 hj1_t1,
            computableSpreadRowContiguousWithProgramCost_fst]
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
        rw [computableSyntheticFFTRadix2WithProgramCost_fst, hm_t1,
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
        have hcChild_p : cChild.p = child.p := idealRoundedPaperTables_p child
        rw [runMultiTapeAffineOddRouteFullSteps_fst, computableOddStrideFactor_eq_oddStrideFactor, hm_t1,
            read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq (Nat.log2 t1) u2 u1 _ hu1_m,
            ← hv1_eq u2 u1,
            runMultiTapeTransposeFullSteps_fst, hm_r,
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
        rw [runMultiTapeTransposeFullSteps_fst, hm_t1]
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
        rw [computableNyquistAltSumContiguousWithProgramCost_fst]
        have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
        exact toScaledComplex_computableNyquistAltSumContiguous_eq p_in pSub t1 r hr
          (xRows.getD (t1 / 2) #[]) x (hxRow_eq (t1 / 2) hhalf_lt)
      exact toScaledComplex_Z_cols_paper_step_eq pSub p' t1 r c0Table c1Table Y_mat alt_q
        (realQuantize pSub (c0Coeff (realErfScaled α) (((u % r : ℕ) : ℝ) / (r : ℝ))) : ℂ)
        (realQuantize pSub (c1Coeff (realErfScaled α) (((u % r : ℕ) : ℝ) / (r : ℝ))) : ℂ)
        (complexQuantize pSub (nyquistAltSum t1 r x))
        (Y (u % r)) (u % r) (u / r) hu2_lt hu1_lt hc0_eq hc1_eq halt_eq
        (fun k hk => hY_eq (u % r) hu2_lt k hk)

/-- Tighter `7000 * spec.intrinsicCostRadix2Leaf` upper bound on `computablePaperFastDFTWithProgramCost`. -/
theorem computablePaperFastDFTWithProgramCost_snd_le_7000
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (hM : ∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p) :
    ((computablePaperFastDFTWithProgramCost p_in (idealRoundedPaperTables spec) xArr).2 : ℝ) ≤
      7000 * spec.intrinsicCostRadix2Leaf := by
  induction hvalid generalizing p_in xArr x with
  | base p R =>
    cases hexec with
    | @base p K hp hK_le =>
      dsimp only [idealRoundedPaperTables, computablePaperFastDFTWithProgramCost]
      rw [nat_log2_two_pow]
      refine (computableBaseRadix2FFTWithProgramCost_snd_le p_in p K hp hK_le _ xArr).trans ?_
      have hpos : 0 ≤ (QuantizedFastDFTSpec.base p (2 ^ K)).intrinsicCostRadix2Leaf := by
        dsimp [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
        positivity
      linarith
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hexec with
    | step hv1_eq hchild_exec =>
      dsimp only [idealRoundedPaperTables, QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
      dsimp only [QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx hM
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
      set cChild := idealRoundedPaperTables child
      dsimp only [computablePaperFastDFTWithProgramCost]
      set m_t1 := natLog2Fuel t1 t1
      set m_r := natLog2Fuel r r
      have hm_t1 : m_t1 = Nat.log2 t1 := natLog2Fuel_self t1
      have hm_r : m_r = Nat.log2 r := natLog2Fuel_self r
      set xRoutedRes := runMultiTapeTransposeFullSteps m_t1 r (read1D xArr)
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
          computableSpreadRowContiguousWithProgramCost p_in pSub (pSub / 2) pSub r
            (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
      set U_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
      set P_res :=
        runScan2DCostedWithSteps t1 r (fun j1 k2 =>
          costedGPreTwistU pSub (6 * (pSub / 2)) (read1D preTwiddles k2) (read2D U_mat j1 k2))
      set P_mat : Array (Array (ℤ × ℤ)) := P_res.1
      set syn_res := computableSyntheticFFTRadix2WithProgramCost (pSub / 2) t1 r m_t1 (r / t1) P_mat
      set Q_res :=
        runScan2DCostedWithSteps t1 r (fun v1 k2 =>
          costedGRescale pSub pSub (4 * (pSub / 2)) (read2D syn_res.1 v1 k2))
      set Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
      set qPost_res :=
        runScan2DCostedWithSteps t1 r (fun v1 k2 =>
          costedGMulScaled (pSub + 2) (6 * (pSub / 2)) (read1D postTwiddles k2) (read2D Q_mat v1 k2))
      set qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
      set qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun v1 : Fin t1 =>
          computablePaperFastDFTWithProgramCost pSub cChild (qPost_mat.getD v1.val #[]))
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
        runScan2DCostedWithSteps r t1 (fun u2 u1 =>
          let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
          costedGRescale cChild.p pSub (4 * (pSub / 2)) (read1D colArr u1))
      set Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
      set altRes :=
        computableNyquistAltSumContiguousWithProgramCost p_in pSub (pSub / 2) r (xRows.getD (t1 / 2) #[])
      set alt_q : ℤ × ℤ := altRes.1
      set Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          let c0 := read1D c0Table u2.val
          let c1_pass := read1D c1Table u2.val
          let Y_col := Y_mat.getD u2.val #[]
          if 2 * u2.val < r then
            computableSolveBidiagonalFwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col
          else if 2 * u2.val = r then
            computableSolveNyquistWithProgramCost pSub (pSub / 2) t1 c0 Y_col alt_q
          else
            computableSolveBidiagonalBwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col)
      set Z_cols_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
      set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
      set Z_flat_res := runMultiTapeTransposeFullSteps m_t1 r (read1D stFlatZ.outTape)
      set outScan := runSequentialScanCostedSteps (fun u =>
        costedGRescale pSub p (4 * (pSub / 2)) (read1D Z_flat_res.1 u)) (t1 * r)
      set U := kroneckerSincGaussianSpreadArray α pSub pSub t1 r x
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
        dsimp only [P_mat, P_res, runScan2DCostedWithSteps, costedGPreTwistU, P]
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
            array_getD_ofFn_of_lt t1 _ [] j1 hj1_t1,
            computableSpreadRowContiguousWithProgramCost_fst]
        rw [hU_row, ← htw]
        have hxRow' : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i) := by
          intro i hi
          have h := hxRow_eq j1 hj1_t1 i hi
          rwa [routedInputGather_eq] at h
        exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2) _ (U j1 k2)
          (computableSpreadRowContiguousWithCost_eq_kroneckerSincGaussianSpreadArray
            α p_in pSub pSub t1 r (xRows.getD j1 #[]) x j1 k2 hxRow' hk2).symm
      have hQ_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D Q_mat v1 k2) = Q v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [Q_mat, Q_res, runScan2DCostedWithSteps, costedGRescale, Q, syn_res]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize pSub)
        have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
          rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
        rw [computableSyntheticFFTRadix2WithProgramCost_fst, hm_t1,
            ← array_getD_getD_eq_read2D_pair _ v1 k2,
            toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1 k2 (ht1_pow.symm ▸ hv1) hk2]
        exact syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P hP_eq v1 k2 hk2
      have hqPost_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [qPost_mat, qPost_res, runScan2DCostedWithSteps, costedGMulScaled, qPost]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
        have htw : toScaledComplex pSub (read1D postTwiddles k2) =
            complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) := by
          dsimp only [postTwiddles]
          rw [read1D_ofFn_of_lt r _ hk2]
          exact toScaledComplex_realQuantizeInt_pair pSub (zetaRoot r (-(k2 : ℝ)))
        rw [htw]
      -- 1. Bound `syn_res.2`:
      have hsyn_cost : syn_res.2 = 2 * syntheticFFTStepBitCost t1 r p' := by
        dsimp only [syn_res, syntheticFFTStepBitCost]
        rw [computableSyntheticFFTRadix2WithProgramCost_snd, hm_t1, hp'_div]
      -- 2. Bound `spreadCost = sumArrayCosts U_rows`:
      have hspread_le :
          sumArrayCosts U_rows ≤
            17 * kroneckerSpreadStepBitCost t1 r p' + 7 * twistAndSolverStepBitCost t1 r p' := by
        have hsum_le :
            sumArrayCosts U_rows ≤
              17 * executedKroneckerSpreadStepBitCost α p K t1 r (routedInputGather t1 r x) +
                t1 * (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                  r * (2 * addBitCost (6 * p'))) := by
          dsimp only [U_rows, executedKroneckerSpreadStepBitCost]
          rw [sumArrayCosts_ofFn_eq_sum t1 _
            (fun j1 =>
              if hj1 : j1 < t1 then
                (computableSpreadRowContiguousWithProgramCost p_in pSub (pSub / 2) pSub r
                  (filterTaps.getD j1 []) (xRows.getD j1 #[])).2
              else 0)
            (fun j1 hj1 => by simp [hj1])]
          have hterm_le :
              ∑ j1 ∈ Finset.range t1,
                (if hj1 : j1 < t1 then
                  (computableSpreadRowContiguousWithProgramCost p_in pSub (pSub / 2) pSub r
                    (filterTaps.getD j1 []) (xRows.getD j1 #[])).2
                else 0) ≤
              ∑ j1 ∈ Finset.range t1,
                (17 * (computableSpreadRowContiguousWithCost p_in pSub pSub r
                    (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1) (xRows.getD j1 #[])).2 +
                  (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                    r * (2 * addBitCost (6 * p')))) := by
            refine Finset.sum_le_sum fun j1 hj1 => ?_
            have hj1_t1 : j1 < t1 := Finset.mem_range.mp hj1
            rw [dif_pos hj1_t1, array_getD_ofFn_of_lt t1 _ [] j1 hj1_t1, hp'_div]
            have hg_len :
                (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1).length ≤
                  effectiveFilterWidth pSub r := by
              dsimp [kroneckerSpreadFilterTapsFolded]
              simp
            exact computableSpreadRowContiguousWithProgramCost_snd_le p_in pSub p' pSub r
              (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1) hg_len (xRows.getD j1 #[])
          have hsum_cost_eq :
              ∑ j1 ∈ Finset.range t1,
                (computableSpreadRowContiguousWithCost p_in pSub pSub r
                  (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1) (xRows.getD j1 #[])).2 =
              executedKroneckerSpreadStepBitCost α p K t1 r (routedInputGather t1 r x) := by
            dsimp only [executedKroneckerSpreadStepBitCost]
            refine Finset.sum_congr rfl fun j1 hj1 => ?_
            have hj1_t1 : j1 < t1 := Finset.mem_range.mp hj1
            exact computableSpreadRowContiguousWithCost_snd_eq α p_in pSub pSub t1 r
              (xRows.getD j1 #[]) (routedInputGather t1 r x) j1 (hxRow_eq j1 hj1_t1)
          calc ∑ j1 ∈ Finset.range t1,
                (if hj1 : j1 < t1 then
                  (computableSpreadRowContiguousWithProgramCost p_in pSub (pSub / 2) pSub r
                    (filterTaps.getD j1 []) (xRows.getD j1 #[])).2
                else 0)
              ≤ ∑ j1 ∈ Finset.range t1,
                (17 * (computableSpreadRowContiguousWithCost p_in pSub pSub r
                    (kroneckerSpreadFilterTapsFolded α pSub pSub t1 r j1) (xRows.getD j1 #[])).2 +
                  (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                    r * (2 * addBitCost (6 * p')))) := hterm_le
            _ = 17 * executedKroneckerSpreadStepBitCost α p K t1 r (routedInputGather t1 r x) +
                t1 * (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                  r * (2 * addBitCost (6 * p'))) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_cost_eq, Finset.sum_const,
                    Finset.card_range, smul_eq_mul]
        have hp_le_p' : p ≤ p' := (fixedPointWordBits_le_four_mul_pChild p K).1
        have hx_p' : ∀ k < t1 * r, ‖routedInputGather t1 r x k‖ ≤ (2 : ℝ) ^ p' := by
          intro k hk
          rw [routedInputGather_eq]
          exact (hM k hk).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp_le_p')
        have hexec_le :=
          executed_kronecker_spread_cost_le_kroneckerSpreadStepBitCost α p K t1 r hp hK hr
            (routedInputGather t1 r x) hx_p'
        have hextra_row := computableSpreadRowContiguousWithProgramCost_extra_le p' r
        have hextra_t1 :
            t1 * (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
              r * (2 * addBitCost (6 * p'))) ≤
              7 * twistAndSolverStepBitCost t1 r p' := by
          calc t1 * (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                r * (2 * addBitCost (6 * p')))
              ≤ t1 * (7 * (r * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')))) :=
                Nat.mul_le_mul_left t1 hextra_row
            _ = 7 * twistAndSolverStepBitCost t1 r p' := by
                dsimp [twistAndSolverStepBitCost]; ring
        exact hsum_le.trans (Nat.add_le_add (Nat.mul_le_mul_left 17 hexec_le) hextra_t1)
      -- 3. Bound `solverCost = sumArrayCosts Z_cols_res`:
      have hsolver_le :
          sumArrayCosts Z_cols_res ≤ 81 * twistAndSolverStepBitCost t1 r p' := by
        have hcol := sumArrayCosts_ofFn_le_const r
          (fun u2 : Fin r =>
            let c0 := read1D c0Table u2.val
            let c1_pass := read1D c1Table u2.val
            let Y_col := Y_mat.getD u2.val #[]
            if 2 * u2.val < r then
              computableSolveBidiagonalFwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col
            else if 2 * u2.val = r then
              computableSolveNyquistWithProgramCost pSub (pSub / 2) t1 c0 Y_col alt_q
            else
              computableSolveBidiagonalBwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col)
          (81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')))
          (fun u2 _ => by
            dsimp only
            rw [hp'_div]
            split_ifs with h1 h2
            · exact computableSolveBidiagonalFwdWithProgramCost_snd_le pSub p' t1 ht1 _ _ _
            · exact computableSolveNyquistWithProgramCost_snd_le pSub p' t1 ht1 _ _ _
            · exact computableSolveBidiagonalBwdWithProgramCost_snd_le pSub p' t1 ht1 _ _ _)
        calc sumArrayCosts Z_cols_res
            ≤ r * (81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) := hcol
          _ = 81 * twistAndSolverStepBitCost t1 r p' := by
              dsimp [twistAndSolverStepBitCost]; ring
      -- 4. Bound `twistAndSolverCost`:
      have hP_cost_eq :
          P_res.2.2 = (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) := by
        dsimp only [P_res]
        refine runScan2DCostedWithSteps_cost_const t1 r _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGPreTwistU]
        rw [hp'_div, computableMulBitCost_eq]
      have hQ_cost_eq :
          Q_res.2.2 = (t1 * r) * (2 * addBitCost (4 * p')) := by
        dsimp only [Q_res]
        refine runScan2DCostedWithSteps_cost_const t1 r _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGRescale]
        rw [hp'_div]
      have hqPost_cost_eq :
          qPost_res.2.2 = (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) := by
        dsimp only [qPost_res]
        refine runScan2DCostedWithSteps_cost_const t1 r _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGMulScaled]
        rw [hp'_div, computableMulBitCost_eq]
      have hY_cost_eq :
          Y_res.2.2 = (r * t1) * (2 * addBitCost (4 * p')) := by
        dsimp only [Y_res]
        refine runScan2DCostedWithSteps_cost_const r t1 _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGRescale]
        rw [hp'_div]
      have hout_eq :
          outScan.2.2 = (t1 * r) * (2 * addBitCost (4 * p')) := by
        dsimp only [outScan]
        refine runSequentialScanCostedSteps_cost_const _ (t1 * r) _ (fun _ _ => ?_)
        dsimp only [costedGRescale]
        rw [hp'_div]
      have htwist_le :
          P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
            altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2 ≤
            96 * twistAndSolverStepBitCost t1 r p' := by
        rw [hP_cost_eq, hQ_cost_eq, hqPost_cost_eq, hY_cost_eq, hout_eq]
        obtain ⟨h6, _, _⟩ := mulBitCost_raw_temporaries_le_four_mul_pChild p'
        have halt_le :
            altRes.2 ≤ 5 * twistAndSolverStepBitCost t1 r p' := by
          dsimp only [altRes, twistAndSolverStepBitCost]
          rw [hp'_div]
          exact computableNyquistAltSumContiguousWithProgramCost_snd_le p_in pSub p' t1 r ht1 hr _
        have hscans_le :
            (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (t1 * r) * (2 * addBitCost (4 * p')) +
              (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (r * t1) * (2 * addBitCost (4 * p')) ≤
              9 * twistAndSolverStepBitCost t1 r p' := by
          have hstep :
              2 * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) + 4 * addBitCost (4 * p') ≤
                9 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by
            dsimp [addBitCost]; omega
          calc (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
                (t1 * r) * (2 * addBitCost (4 * p')) +
                (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
                (r * t1) * (2 * addBitCost (4 * p'))
              = (t1 * r) * (2 * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) + 4 * addBitCost (4 * p')) := by ring
            _ ≤ (t1 * r) * (9 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) :=
                Nat.mul_le_mul_left (t1 * r) hstep
            _ = 9 * twistAndSolverStepBitCost t1 r p' := by
                dsimp [twistAndSolverStepBitCost]; ring
        have hout_le :
            (t1 * r) * (2 * addBitCost (4 * p')) ≤ 1 * twistAndSolverStepBitCost t1 r p' := by
          dsimp [twistAndSolverStepBitCost, addBitCost]
          rw [Nat.one_mul]
          refine Nat.mul_le_mul_left (t1 * r) ?_
          omega
        calc (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (t1 * r) * (2 * addBitCost (4 * p')) +
              (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (r * t1) * (2 * addBitCost (4 * p')) +
              altRes.2 + sumArrayCosts Z_cols_res + (t1 * r) * (2 * addBitCost (4 * p'))
            ≤ 9 * twistAndSolverStepBitCost t1 r p' +
              5 * twistAndSolverStepBitCost t1 r p' +
              81 * twistAndSolverStepBitCost t1 r p' +
              1 * twistAndSolverStepBitCost t1 r p' :=
              Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hscans_le halt_le) hsolver_le) hout_le
          _ = 96 * twistAndSolverStepBitCost t1 r p' := by ring
      -- 5. Bound `routingCost`:
      have hrouting_le :
          (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
            (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
              stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
            addBitCost (8 * (pSub / 2)) ≤
          2 * routingAndStreamingStepBitCost t1 r p' := by
        have hcol_sum : sumArrayCosts colRoutes = r * ((2 * m_t1 + 1) * 2 ^ m_t1) := by
          dsimp only [colRoutes]
          refine sumArrayCosts_ofFn_const r _ ((2 * m_t1 + 1) * 2 ^ m_t1) (fun u2 _ => ?_)
          exact runMultiTapeAffineOddRouteFullSteps_snd m_t1 _ 0 _
        have hlhs_eq :
            (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
              (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
              addBitCost (8 * (pSub / 2)) =
            (2 * ((2 * Nat.log2 t1) * (t1 * r)) + (2 * Nat.log2 r) * (r * t1) +
              (2 * Nat.log2 t1) * (t1 * r) + 12 * (t1 * r)) * addBitCost (8 * p') := by
          dsimp only [xRoutedRes, qHat_T_res, Z_flat_res, xRows_res, P_res, Q_res, qPost_res,
            stFlatQ, Y_res, stFlatZ, outScan]
          rw [runMultiTapeTransposeFullSteps_snd, runMultiTapeTransposeFullSteps_snd,
              runMultiTapeTransposeFullSteps_snd, hcol_sum,
              runScan2DWithSteps_snd,
              runScan2DCostedWithSteps_steps, runScan2DCostedWithSteps_steps,
              runScan2DCostedWithSteps_steps, runScan2DCostedWithSteps_steps,
              runFlatten2DSteps_steps, runFlatten2DSteps_steps,
              runSequentialScanCostedSteps_steps,
              hm_t1, hm_r, ht1_pow, hr_pow, hp'_div]
          ring
        have hrhs_eq :
            2 * routingAndStreamingStepBitCost t1 r p' =
              (2 * (2 * ((2 * Nat.log2 t1) * (t1 * r)) + (2 * Nat.log2 r) * (r * t1) +
                (2 * Nat.log2 t1) * (t1 * r)) + 16 * (t1 * r)) * addBitCost (8 * p') := by
          unfold routingAndStreamingStepBitCost sequentialTransposeBitCost
            sequentialColumnMergeSortBitCost sequentialLinearScanBitCost sequentialPassBitCost
          rw [sequentialTapeTransposeWithPasses_snd, sequentialTapeTransposeWithPasses_snd,
              sequentialAffineOddRouteWithPasses_snd]
          ring
        rw [hlhs_eq, hrhs_eq]
        refine Nat.mul_le_mul_right (addBitCost (8 * p')) ?_
        omega
      -- 6. Bound `childCostSum = sumArrayCosts qHat_res`:
      have hchild_sum :
          ((sumArrayCosts qHat_res : ℕ) : ℝ) ≤
            (t1 : ℝ) * (7000 * child.intrinsicCostRadix2Leaf) := by
        dsimp only [qHat_res]
        refine sumArrayCosts_ofFn_cast_le_const t1 _ (7000 * child.intrinsicCostRadix2Leaf)
          (fun v1 hv1 => ?_)
        refine ih hchild_exec pSub (qPost_mat.getD v1 #[]) (qPost v1)
          (fun k hk => ?_) (fun k hk => ?_)
        · have hk_r : k < r := hchild_size ▸ hk
          rw [read1D_array_getD_eq_read2D]
          exact (hqPost_eq v1 hv1 k hk_r).symm
        · have hk_r : k < r := hchild_size ▸ hk
          rw [hchild_p]
          exact norm_qPost_le_two_pow_pChild p K t1 r ht1 hr hsize x hM v1 k hk_r
      -- Combine all 6 bounds into `≤ 7000 * (...)`:
      have hlocal_nat :
          syn_res.2 + sumArrayCosts U_rows +
            (P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
              altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2) +
            (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
              (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
              addBitCost (8 * (pSub / 2)) ≤
          7000 * (syntheticFFTStepBitCost t1 r p' + kroneckerSpreadStepBitCost t1 r p' +
            twistAndSolverStepBitCost t1 r p' + routingAndStreamingStepBitCost t1 r p') := by
        have h1 : syn_res.2 ≤ 2 * syntheticFFTStepBitCost t1 r p' := le_of_eq hsyn_cost
        calc syn_res.2 + sumArrayCosts U_rows +
              (P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
                altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2) +
              (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
                (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                  stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
                addBitCost (8 * (pSub / 2))
            ≤ 2 * syntheticFFTStepBitCost t1 r p' +
              (17 * kroneckerSpreadStepBitCost t1 r p' + 7 * twistAndSolverStepBitCost t1 r p') +
              96 * twistAndSolverStepBitCost t1 r p' +
              2 * routingAndStreamingStepBitCost t1 r p' :=
              Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 hspread_le) htwist_le) hrouting_le
          _ ≤ 7000 * (syntheticFFTStepBitCost t1 r p' + kroneckerSpreadStepBitCost t1 r p' +
              twistAndSolverStepBitCost t1 r p' + routingAndStreamingStepBitCost t1 r p') := by
              omega
      have hlocal_real :
          ((syn_res.2 + sumArrayCosts U_rows +
            (P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
              altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2) +
            (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
              (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
              addBitCost (8 * (pSub / 2)) : ℕ) : ℝ) ≤
          7000 * (((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ) +
            ((kroneckerSpreadStepBitCost t1 r p' : ℕ) : ℝ) +
            ((twistAndSolverStepBitCost t1 r p' : ℕ) : ℝ) +
            ((routingAndStreamingStepBitCost t1 r p' : ℕ) : ℝ)) := by
        exact_mod_cast hlocal_nat
      have hcomb := add_le_add hlocal_real hchild_sum
      push_cast at hcomb ⊢
      calc ((syn_res.2 : ℝ) + (sumArrayCosts U_rows : ℝ) +
            ((P_res.2.2 : ℝ) + (Q_res.2.2 : ℝ) + (qPost_res.2.2 : ℝ) + (Y_res.2.2 : ℝ) +
              (altRes.2 : ℝ) + (sumArrayCosts Z_cols_res : ℝ) + (outScan.2.2 : ℝ)) +
            ((xRoutedRes.2 : ℝ) + (qHat_T_res.2 : ℝ) + (Z_flat_res.2 : ℝ) + (sumArrayCosts colRoutes : ℝ) +
              ((xRows_res.2 : ℝ) + (P_res.2.1 : ℝ) + (Q_res.2.1 : ℝ) + (qPost_res.2.1 : ℝ) +
                (stFlatQ.steps : ℝ) + (Y_res.2.1 : ℝ) + (stFlatZ.steps : ℝ) + (outScan.2.1 : ℝ))) *
              (addBitCost (8 * (pSub / 2)) : ℝ) +
            (sumArrayCosts qHat_res : ℝ))
          ≤ 7000 * ((syntheticFFTStepBitCost t1 r p' : ℝ) +
              (kroneckerSpreadStepBitCost t1 r p' : ℝ) +
              (twistAndSolverStepBitCost t1 r p' : ℝ) +
              (routingAndStreamingStepBitCost t1 r p' : ℝ)) +
            (t1 : ℝ) * (7000 * child.intrinsicCostRadix2Leaf) := hcomb
        _ = 7000 * (((syntheticFFTStepBitCost t1 r p' : ℝ) +
              (kroneckerSpreadStepBitCost t1 r p' : ℝ) +
              (twistAndSolverStepBitCost t1 r p' : ℝ) +
              (routingAndStreamingStepBitCost t1 r p' : ℝ)) +
            (t1 : ℝ) * child.intrinsicCostRadix2Leaf) := by ring

/-- **Program-Derived Upper-Bound Inequality Theorem for `computablePaperFastDFTWithProgramCost`
(`computablePaperFastDFTWithProgramCost_snd_le`, `[MS]` §7.2)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`, `hexec : spec.PaperExecutableValid`),
any input precision `p_in : ℕ`, and any input `xArr : Array (ℤ × ℤ)` and `x : ℕ → ℂ` satisfying
`∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k)` and `∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p`,
the integer bit-operation and tape-head-step cost `.2` accumulated bottom-up by
`computablePaperFastDFTWithProgramCost` satisfies the **inequality upper bound**:
`((computablePaperFastDFTWithProgramCost p_in (idealRoundedPaperTables spec) xArr).2 : ℝ) ≤
  8192 * spec.intrinsicCostRadix2Leaf`. -/
theorem computablePaperFastDFTWithProgramCost_snd_le
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (hM : ∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p) :
    ((computablePaperFastDFTWithProgramCost p_in (idealRoundedPaperTables spec) xArr).2 : ℝ) ≤
      8192 * spec.intrinsicCostRadix2Leaf := by
  have h7000 := computablePaperFastDFTWithProgramCost_snd_le_7000 spec hvalid hexec p_in xArr x hx hM
  have hnonneg := QuantizedFastDFTSpec.intrinsicCostRadix2Leaf_nonneg spec
  linarith

/-- Normalized root chunk pair `(4 * a, 4 * b)` on the `toScaledComplex b` grid (`costedPackRootChunkPair`). -/
abbrev costedPackRootChunkPair (a b : ℕ) : BitCostM (ℤ × ℤ) :=
  ((4 * (a : ℤ), 4 * (b : ℤ)), 0)

/-- Root-level rounded convolution digit extraction from inverse transform slot `z : ℤ × ℤ`
(`costedExtractRootSlot`). -/
abbrev costedExtractRootSlot (p0 b K0 : ℕ) (z : ℤ × ℤ) : BitCostM ℕ :=
  let numScale : ℤ := ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ)
  let denScale : ℤ := 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ)
  let imInt : ℤ := -z.2
  let d := costedDivRoundRatInt (4 * p0) (imInt * numScale) denScale
  (d.1.toNat, d.2 + addBitCost (4 * p0))

/-- **Program-Cost-Accumulating Computable End-to-End `FastDFT` Multiplier with `BaseRadix2FFT` Leaves
(`computablePaperFastDFTMultiplyWithProgramCost`, `[MS]` §7)**:
100% computable (`def`, zero `noncomputable`, zero `Real`, zero `Complex`) integer multiplier that:
- splits `A` and `B` via `splitChunksTreeWithProgramCost` (`splitA.2 + splitB.2`),
- packs the normalized chunks via `runSequentialScanSteps` (`packCost`),
- runs the forward transform `fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape` (`fwd.2`),
- squares and conjugates pointwise via `costedGMulScaled (p0 + 2) (4 * p0)` (`sqCost`),
- runs the inverse transform `inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.outTape` (`inv.2`),
- extracts the rounded convolution digits via `costedDivRoundRatInt (4 * p0)` (`extCost`), and
- reconstructs the integer product via `reconstructChunksTreeWithProgramCost` (`recon.2`),
accumulating every subroutine's runtime cost directly into `.2`. -/
def computablePaperFastDFTMultiplyWithProgramCost
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
  let fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
  let stSq := runSequentialScanCostedSteps (fun u =>
    let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u) (read1D fwd.1 u)
    (gConj m.1, m.2 + addBitCost (8 * p0))) R0
  let sqCost := stSq.2.2
  let inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.1
  let stExt := runSequentialScanCostedSteps (fun j =>
    let e := costedExtractRootSlot p0 b K0 (read1D inv.1 j)
    (e.1, e.2)) R0
  let extCost := stExt.2.2
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j => read1D stExt.1 j)
  let recon := reconstructChunksTreeWithProgramCost b convNat
  let rootCost : ℕ := splitA.2 + splitB.2 + packCost + sqCost + extCost + recon.2
  (recon.1, fwd.2 + inv.2 + rootCost)

/-- First projection of `computablePaperFastDFTMultiplyWithProgramCost` (`computablePaperFastDFTMultiply`, `[MS]` §7). -/
def computablePaperFastDFTMultiply
    (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ :=
  (computablePaperFastDFTMultiplyWithProgramCost cSpec b K0 k1 k2 A B).1

/-- Parameter-free computable integer multiplier given a precompiled `cSpec : ComputablePaperFastDFTSpec`
(`computablePaperMultiplyOfBitLengthGivenSpecWithProgramCost`, `[MS]` §7). -/
def computablePaperMultiplyOfBitLengthGivenSpecWithProgramCost
    (cSpec : ComputablePaperFastDFTSpec) (n A B : ℕ) : ℕ × ℕ :=
  let b := max 1 (Nat.log2 n)
  let k := n / b + 1
  let K0 := max 4 (Nat.log2 (2 * k) + 2)
  computablePaperFastDFTMultiplyWithProgramCost cSpec b K0 k k A B

theorem computablePaperFastDFTMultiply_eq_quantizedFastDFTMultiplyRadix2Leaf
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) :
    computablePaperFastDFTMultiply (idealRoundedPaperTables spec) b K0 k1 k2 A B =
      quantizedFastDFTMultiplyRadix2Leaf spec b K0 k1 k2 A B := by
  unfold computablePaperFastDFTMultiply computablePaperFastDFTMultiplyWithProgramCost
    quantizedFastDFTMultiplyRadix2Leaf
  dsimp only [runSequentialScanCostedSteps, costedGMulScaled, costedDivRoundRatInt]
  rw [reconstructChunksTreeWithProgramCost_fst, reconstructChunksTree_eq_reconstructChunks,
      splitChunksTreeWithProgramCost_fst, splitChunksTreeWithProgramCost_fst]
  apply congrArg (reconstructChunks b)
  refine List.map_congr_left fun j hj_mem => ?_
  have hj_lt : j < k1 + k2 := List.mem_range.mp hj_mem
  have hj_R0 : j < 2 ^ K0 := by omega
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set cSpec := idealRoundedPaperTables spec
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
  set stSq := runSequentialScanSteps (fun u =>
    gConj (gMulScaled (p0 + 2) (read1D fwd.1 u) (read1D fwd.1 u))) R0
  set inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.outTape
  rw [read1D_runSequentialScanSteps_eq _ R0 j hj_R0]
  have hy : ∀ u < R0, toScaledComplex p0 (read1D fwd.1 u) = sincGaussianFastDFTRadix2Leaf spec x_AB u := by
    intro u hu
    rw [← hp0]
    exact toScaledComplex_computablePaperFastDFT_eq spec hvalid hexec b stPack.outTape x_AB
      (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
      u (hsize.symm ▸ hu)
  have hsConj : ∀ u < spec.size,
      star (complexQuantize p0 ((sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2)) =
        toScaledComplex p0 (read1D stSq.outTape u) := by
    intro u hu
    have hu_R0 : u < R0 := hsize ▸ hu
    dsimp only [stSq]
    rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, toScaledComplex_gConj,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu_R0, sq]
  have hz : toScaledComplex p0 (read1D inv.1 j) =
      sincGaussianFastDFTRadix2Leaf spec
        (fun u => star (complexQuantize p0 ((sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2))) j := by
    have h := toScaledComplex_computablePaperFastDFT_eq spec hvalid hexec p0 stSq.outTape
      (fun u => star (complexQuantize p0 ((sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2)))
      hsConj j (hsize.symm ▸ hj_R0)
    rwa [hp0] at h
  have hzim :
      (star (sincGaussianFastDFTRadix2Leaf spec
        (fun u => star (complexQuantize p0 ((sincGaussianFastDFTRadix2Leaf spec x_AB u) ^ 2))) j)).im =
      ((-(read1D inv.1 j).2 : ℤ) : ℝ) / (2 : ℝ) ^ (p0 + 2) := by
    rw [← hz, ← toScaledComplex_gConj]
    simp [toScaledComplex, gConj]
  unfold quantizedFastDFTConvApproxRadix2Leaf
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

/-- **Master End-to-End Correctness Theorem for `computablePaperFastDFTMultiply` (`[MS]` §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`, `hexec : spec.PaperExecutableValid`)
with `spec.size = 2 ^ K0` and `spec.p = rootPrecision b K0`, any `k1 + k2 ≤ 2 ^ K0`, and any
`A < (2 ^ b) ^ k1`, `B < (2 ^ b) ^ k2`, `computablePaperFastDFTMultiply` returns the exact product `A * B`. -/
theorem computablePaperFastDFTMultiply_eq_mul
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    computablePaperFastDFTMultiply (idealRoundedPaperTables spec) b K0 k1 k2 A B = A * B := by
  rw [computablePaperFastDFTMultiply_eq_quantizedFastDFTMultiplyRadix2Leaf spec hvalid hexec b K0 k1 k2 A B hsize hp0 hk]
  exact quantizedFastDFTMultiplyRadix2Leaf_eq_mul spec hvalid hexec.toBasePow2 b K0 k1 k2 hsize hp0 hk A B hA hB

end IntMul
