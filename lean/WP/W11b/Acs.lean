import WP.W11b.Defs

/-!
# WP.W11b.Acs — the snapshot's per-node width certificate in W9's phase forms

`AllCallSitesWidthSound p_in cSpec x` (CSWS:1507) states `FitsSignedWord` bounds on every
intermediate array of one step node, written with the cost-carrying `let` chain of
`computablePaperFastDFTWithProgramCost`. `acsV` restates the clauses W9 needs with the pure phase
helpers of `Contracts.W9.Pre`/`Post` (the same `_fst` erasure as levelsync's `preNode_eq_V`,
`postNode_eq_V`). The children outputs appear as `qHatV` (the snapshot's own bookkeeping).
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- The children outputs of a step node, in the snapshot's bookkeeping. -/
def qHatV (p_in pSub t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (cChild : ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ)) : Array (Array (ℤ × ℤ)) :=
  Array.ofFn (fun v1 : Fin t1 =>
    computablePaperFastDFT pSub cChild ((preNodeV p_in pSub pSub t1 r ft preTw postTw x).getD v1.val #[]))

/-- The routed and rescaled children outputs `Y` of a step node. -/
def yV (p_in pSub t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (cChild : ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ)) : Array (Array (ℤ × ℤ)) :=
  w9Y pSub t1 r cChild.p (w9ColRoutes t1 r (w9QHatT t1 r (qHatV p_in pSub t1 r ft preTw postTw cChild x)))

theorem acsV (p_in p K t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw c0T c1T : Array (ℤ × ℤ))
    (cChild : ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : AllCallSitesWidthSound p_in
      (.step p (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw c0T c1T cChild) x) :
    (∀ j1 < t1, ∀ k2 < r,
        FitsSignedWord (6 * pChild p K)
          (read2D (w9U p_in (2 * pChild p K) (2 * pChild p K) t1 r ft (w9XRows t1 r x)) j1 k2) ∧
        FitsSignedWord (4 * pChild p K) (read2D (w9P (2 * pChild p K) t1 r preTw
          (w9U p_in (2 * pChild p K) (2 * pChild p K) t1 r ft (w9XRows t1 r x))) j1 k2)) ∧
      (∀ v1 < t1, ∀ k2 < r,
        FitsSignedWord (4 * pChild p K) (read2D (w9Q (2 * pChild p K) t1 r (w9Syn t1 r
          (w9P (2 * pChild p K) t1 r preTw
            (w9U p_in (2 * pChild p K) (2 * pChild p K) t1 r ft (w9XRows t1 r x))))) v1 k2) ∧
        FitsSignedWord (4 * pChild p K)
          (read2D (preNodeV p_in (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw x) v1 k2)) ∧
      FitsSignedWord (4 * pChild p K) (altNodeV p_in (2 * pChild p K) t1 r x) ∧
      (∀ u2 < r, ∀ u1 < t1, FitsSignedWord (4 * pChild p K)
        (read2D (yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x) u2 u1)) ∧
      (∀ u2 < r, ∀ n < t1, ∀ u1 ≤ n,
        (2 * u2 < r →
          FitsSignedWord (4 * pChild p K) (read1D (buildComputableZPartFwdExact (2 * pChild p K)
            (read1D c0T u2) (read1D c1T u2)
            ((yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x).getD u2 #[]) n) u1) ∧
          FitsSignedWord (4 * pChild p K) (read1D (buildComputableZHomFwdExact (2 * pChild p K)
            (read1D c0T u2) (read1D c1T u2) n) u1)) ∧
        (2 * u2 = r →
          FitsSignedWord (4 * pChild p K) (read1D (buildComputableZPartNyqExact (2 * pChild p K)
            (read1D c0T u2)
            ((yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x).getD u2 #[]) n) u1)) ∧
        (r < 2 * u2 →
          FitsSignedWord (4 * pChild p K) (read1D (buildComputableZPartFwdExact (2 * pChild p K)
            (read1D c1T u2) (read1D c0T u2)
            (runBwdRevSteps t1
              (read1D ((yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x).getD u2 #[])) t1).outTape
            n) u1) ∧
          FitsSignedWord (4 * pChild p K) (read1D (buildComputableZHomFwdExact (2 * pChild p K)
            (read1D c1T u2) (read1D c0T u2) n) u1)) ∧
        FitsSignedWord (4 * pChild p K) (read2D (w9ZExact (2 * pChild p K) t1 r c0T c1T
          (altNodeV p_in (2 * pChild p K) t1 r x)
          (yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x)) u2 u1)) ∧
      (∀ u < t1 * r, FitsSignedWord (4 * pChild p K) (read1D (w9Out p (2 * pChild p K) t1 r
        (w9ZExact (2 * pChild p K) t1 r c0T c1T (altNodeV p_in (2 * pChild p K) t1 r x)
          (yV p_in (2 * pChild p K) t1 r ft preTw postTw cChild x))) u)) := by
  have hdiv : 2 * pChild p K / 2 = pChild p K := Nat.mul_div_cancel_left _ (by norm_num)
  simp only [AllCallSitesWidthSound, hdiv, runMultiTapeTransposeFullSteps_fst,
    runScan2DCostedWithSteps_fst, ofFn_dite_fst, computableSpreadRowContiguousWithProgramCost_fst,
    computableSyntheticFFTRadix2WithProgramCost_fst, costedGPreTwistU, costedGRescale,
    costedGMulScaled, runSequentialScanCostedSteps_fst, runMultiTapeAffineOddRouteFullSteps_fst,
    dite_ofFn_fst_eq_getD, ofFn_getD_ofFn, fst_ite3,
    computableSolveBidiagonalFwdWithProgramCost_fst, computableSolveNyquistWithProgramCost_fst,
    computableSolveBidiagonalBwdWithProgramCost_fst, computableNyquistAltSumContiguousWithProgramCost_fst,
    buildComputableZPartFwdWithProgramCost_fst, buildComputableZHomFwdWithProgramCost_fst,
    buildComputableZPartNyqWithProgramCost_fst] at h
  obtain ⟨hUP, -, hQ, -, halt, hY, hsol, hout⟩ := h
  refine ⟨hUP, fun v1 hv1 k2 hk2 => ⟨(hQ v1 hv1 k2 hk2).1, (hQ v1 hv1 k2 hk2).2.2⟩, halt, hY, hsol, hout⟩

#assert_std_axioms acsV

end WP.W11b
