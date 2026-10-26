import WP.W7k2.Canon.Series
import Contracts.W7.Tables

/-!
# WP.W7k2.Canon.Tape — canonical form of the snapshot table tape

Step (1) of W7k2, builder part. The contract tape
`W7.tape W7.snapshotFormat (buildComputablePaperTables (buildQuantizedSpecPaperStop L p K))`
(`Contracts/W7/Format.lean`, CTB:92-151, PSR:43) is restated as an explicit recursion over the
schedule `(L, p, K)` whose segments list the **kernel reference values** directly (no arrays):

* `stdV q num den neg` — the `W7_stdChar` value; `tapV` — the `W7_sincGaussianTap` value;
  `c0V`, `c1V` — the two `W7_c0c1` values; `W7.colRecip` — the `W7_colRecip` value;
* `foldV` — a folded tap: the sum of the raw taps `s < 2·pSub + 1` with `s % W_eff = u` (CTB:35);
* `preSegC`, `postSegC`, `leafSegC` — one segment each, with the header fields of `Format.lean`;
* `tapeFromC pIn L p K` — `pre ++ tape(child) ++ post`, or the leaf (the stop test of PSR:46).

**Main theorem** `tape_ref_eq`: the contract's tape of the reference tables is
`tapeFromC 0 L p K`. This is the specification the builder machine is proved against.

The proof goes through generic *explicit-segment* forms (`preSegE`, `postSegE`, `leafSegE`), which
take the entries as functions of the index, and congruence lemmas (`preSeg_eq_E`, …): a segment only
reads entries with index below the canonical length, where the snapshot arrays agree with the
kernel values (`read1D_runSequentialScanSteps_eq`, `array_getD_ofFn_of_lt`).
-/

namespace WP.W7k2

open IntMul TMFw TMFw.Contracts

/-! ## Kernel reference values -/

/-- The `W7_stdChar` value. -/
abbrev stdV (q num den : ℕ) (neg : Bool) : ℤ × ℤ := (computableStdCharWithProgramCost q num den neg).1

/-- The `W7_sincGaussianTap` value (raw tap). -/
abbrev tapV (pw pSub t1 j1 s : ℕ) : ℤ := (computableSincGaussianTapWithProgramCost pw pSub t1 j1 s).1

/-- The `c0` value of `W7_c0c1`. -/
abbrev c0V (pw pSub r u2 : ℕ) : ℤ := (computableC0C1WithProgramCost pw pSub r u2).1.1.1

/-- The `c1` value of `W7_c0c1`. -/
abbrev c1V (pw pSub r u2 : ℕ) : ℤ := (computableC0C1WithProgramCost pw pSub r u2).1.2.1

/-- Folded tap `u` of row `j1` (CTB:35-39). -/
def foldV (pw pSub t1 W j1 u : ℕ) : ℤ :=
  ∑ s ∈ (Finset.range (2 * pSub + 1)).filter (fun s => s % W = u), tapV pw pSub t1 j1 s

/-! ## Explicit segments (entries given as functions of the index) -/

/-- A pre segment with rows `T j1`, pre-twiddles `P k2` and post-twiddles `Q k2`. -/
def preSegE (pIn p pSub m1 t1 r childP : ℕ) (T : ℕ → List ℤ) (P Q : ℕ → ℤ × ℤ) : List Sym :=
  W7.tagPre :: (W7.header [p, pSub, m1, t1, r, Nat.log2 t1, Nat.log2 r,
      effectiveFilterWidth m1 r, kroneckerSpreadNumBlocks m1 r, childP, pIn] ++
    (((List.range t1).map fun j1 => ((T j1).map W7.realRec).flatten ++ [W7.tagRow]).flatten ++
      [W7.tagSub] ++
      (((List.range r).map fun k2 => W7.cplxRec (P k2)).flatten ++ [W7.tagSub]) ++
      (((List.range r).map fun k2 => W7.cplxRec (Q k2)).flatten ++ [W7.tagSub])))

/-- A post segment with coefficients `C0 u2`, `C1 u2`. -/
def postSegE (p pSub t1 r childP H : ℕ) (C0 C1 : ℕ → ℤ) : List Sym :=
  W7.tagPost :: (W7.header [p, pSub, t1, r, Nat.log2 t1, Nat.log2 r, childP, H] ++
    (((List.range r).map fun u2 =>
        W7.postRec (C0 u2) (C1 u2) (W7.colRecip H r u2 (C0 u2) (C1 u2))).flatten ++ [W7.tagSub]))

/-- A leaf segment with twiddles `TW s u`. -/
def leafSegE (pIn p K q : ℕ) (TW : ℕ → ℕ → ℤ × ℤ) : List Sym :=
  W7.tagLeaf :: (W7.header [p, K, q, pIn] ++
    ((List.range K).map fun s =>
      ((List.range (2 ^ (s + 1))).map fun u => W7.cplxRec (TW s u)).flatten ++
        [W7.tagSub]).flatten)

theorem preSeg_eq_E (pIn p pSub m1 t1 r childP : ℕ) (taps : Array (List ℤ))
    (pre post : Array (ℤ × ℤ)) (T : ℕ → List ℤ) (P Q : ℕ → ℤ × ℤ)
    (hT : ∀ j1 < t1, taps.getD j1 [] = T j1) (hP : ∀ k2 < r, read1D pre k2 = P k2)
    (hQ : ∀ k2 < r, read1D post k2 = Q k2) :
    W7.preSeg pIn p pSub m1 t1 r childP taps pre post = preSegE pIn p pSub m1 t1 r childP T P Q := by
  have e1 : (List.range t1).map (fun j1 => ((taps.getD j1 []).map W7.realRec).flatten ++ [W7.tagRow]) =
      (List.range t1).map (fun j1 => ((T j1).map W7.realRec).flatten ++ [W7.tagRow]) :=
    List.map_congr_left (fun j1 hj1 => by rw [hT j1 (List.mem_range.mp hj1)])
  have e2 : (List.range r).map (fun k2 => W7.cplxRec (read1D pre k2)) =
      (List.range r).map (fun k2 => W7.cplxRec (P k2)) :=
    List.map_congr_left (fun k2 hk2 => by rw [hP k2 (List.mem_range.mp hk2)])
  have e3 : (List.range r).map (fun k2 => W7.cplxRec (read1D post k2)) =
      (List.range r).map (fun k2 => W7.cplxRec (Q k2)) :=
    List.map_congr_left (fun k2 hk2 => by rw [hQ k2 (List.mem_range.mp hk2)])
  unfold W7.preSeg preSegE
  rw [e1, e2, e3]

theorem postSeg_eq_E (p pSub t1 r childP H : ℕ) (c0 c1 : Array (ℤ × ℤ)) (C0 C1 : ℕ → ℤ)
    (h0 : ∀ u2 < r, (read1D c0 u2).1 = C0 u2) (h1 : ∀ u2 < r, (read1D c1 u2).1 = C1 u2) :
    W7.postSeg p pSub t1 r childP H c0 c1 = postSegE p pSub t1 r childP H C0 C1 := by
  have e : (List.range r).map (fun u2 =>
        W7.postRec (read1D c0 u2).1 (read1D c1 u2).1
          (W7.colRecip H r u2 (read1D c0 u2).1 (read1D c1 u2).1)) =
      (List.range r).map (fun u2 =>
        W7.postRec (C0 u2) (C1 u2) (W7.colRecip H r u2 (C0 u2) (C1 u2))) :=
    List.map_congr_left (fun u2 hu2 => by
      rw [h0 u2 (List.mem_range.mp hu2), h1 u2 (List.mem_range.mp hu2)])
  unfold W7.postSeg postSegE
  rw [e]

theorem leafSeg_eq_E (pIn p K q : ℕ) (tw : Array (Array (ℤ × ℤ))) (TW : ℕ → ℕ → ℤ × ℤ)
    (h : ∀ s < K, ∀ u < 2 ^ (s + 1), read1D (tw.getD s #[]) u = TW s u) :
    W7.leafSeg pIn p K q tw = leafSegE pIn p K q TW := by
  have e : (List.range K).map (fun s =>
        ((List.range (2 ^ (s + 1))).map fun u => W7.cplxRec (read1D (tw.getD s #[]) u)).flatten ++
          [W7.tagSub]) =
      (List.range K).map (fun s =>
        ((List.range (2 ^ (s + 1))).map fun u => W7.cplxRec (TW s u)).flatten ++ [W7.tagSub]) := by
    refine List.map_congr_left (fun s hs => ?_)
    have e' : (List.range (2 ^ (s + 1))).map (fun u => W7.cplxRec (read1D (tw.getD s #[]) u)) =
        (List.range (2 ^ (s + 1))).map (fun u => W7.cplxRec (TW s u)) :=
      List.map_congr_left (fun u hu => by
        rw [h s (List.mem_range.mp hs) u (List.mem_range.mp hu)])
    rw [e']
  unfold W7.leafSeg leafSegE
  rw [e]

/-! ## Canonical segments of the snapshot schedule -/

/-- Leaf segment of `.base p (2^K)`: `K` stages at `q_leaf = 2p + K + 8`. -/
def leafSegC (pIn p K : ℕ) : List Sym :=
  leafSegE pIn p K (2 * p + K + 8) (fun s u => stdV (2 * p + K + 8) u (2 ^ (s + 1)) false)

/-- Pre segment of the step node `(p, K)`. -/
def preSegC (pIn p K : ℕ) : List Sym :=
  let pSub := 2 * pChild p K
  let t1 := 2 ^ (K / 2)
  let r := 2 ^ (K - K / 2)
  preSegE pIn p pSub pSub t1 r (pChild p K)
    (fun j1 => (List.range (effectiveFilterWidth pSub r)).map
      (foldV (pWork p K) pSub t1 (effectiveFilterWidth pSub r) j1))
    (fun k2 => stdV pSub k2 (2 * r) false) (fun k2 => stdV pSub k2 (2 * r) true)

/-- Post segment of the step node `(p, K)`, with `H = 3·pSub + 2`. -/
def postSegC (p K : ℕ) : List Sym :=
  let pSub := 2 * pChild p K
  let r := 2 ^ (K - K / 2)
  postSegE p pSub (2 ^ (K / 2)) r (pChild p K) (3 * pSub + 2)
    (fun u2 => c0V (pWork p K) pSub r u2) (fun u2 => c1V (pWork p K) pSub r u2)

/-- **Canonical tape** of the snapshot schedule, from the parent sub-step precision `pIn`. -/
def tapeFromC : ℕ → ℕ → ℕ → ℕ → List Sym
  | pIn, 0, p, K => leafSegC pIn p K
  | pIn, L + 1, p, K =>
    if 2 ^ K ≤ 4 * p * p then leafSegC pIn p K
    else preSegC pIn p K ++ tapeFromC (2 * pChild p K) L (pChild p K) (K - K / 2) ++ postSegC p K

/-! ## The snapshot builder's arrays, read at used indices -/

/-- The leaf twiddle array of `buildComputablePaperTables (.base p R)`. -/
def leafTw (p R : ℕ) : Array (Array (ℤ × ℤ)) :=
  match buildComputablePaperTables (.base p R) with
  | .basePow2 _ _ tw => tw
  | .step .. => #[]

theorem build_base (p R : ℕ) :
    buildComputablePaperTables (.base p R) = .basePow2 p (Nat.log2 R) (leafTw p R) := rfl

theorem leafTw_read (p R s u : ℕ) (hs : s < Nat.log2 R) (hu : u < 2 ^ (s + 1)) :
    read1D ((leafTw p R).getD s #[]) u = stdV (2 * p + Nat.log2 R + 8) u (2 ^ (s + 1)) false := by
  simp only [leafTw, buildComputablePaperTables, buildComputablePaperTablesWithProgramCost]
  rw [array_getD_ofFn_of_lt _ _ #[] s hs, array_getD_ofFn_of_lt _ _ (#[], 0) s hs]
  dsimp only [runSequentialScanCostedSteps]
  rw [read1D_runSequentialScanSteps_eq _ _ u hu]

/-- The five table arrays of a step node (they depend only on `p, K, t1, r`). -/
def stepArrs (p K t1 r : ℕ) :
    Array (List ℤ) × Array (ℤ × ℤ) × Array (ℤ × ℤ) × Array (ℤ × ℤ) × Array (ℤ × ℤ) :=
  match buildComputablePaperTables (.step p K t1 r 0 (fun _ _ => 0) (.base 0 0)) with
  | .step _ _ _ _ _ taps pre post c0 c1 _ => (taps, pre, post, c0, c1)
  | .basePow2 .. => (#[], #[], #[], #[], #[])

theorem build_step (p K t1 r c1 : ℕ) (v1Of : ℕ → ℕ → ℕ) (child : QuantizedFastDFTSpec) :
    buildComputablePaperTables (.step p K t1 r c1 v1Of child) =
      .step p (2 * pChild p K) (2 * pChild p K) t1 r (stepArrs p K t1 r).1
        (stepArrs p K t1 r).2.1 (stepArrs p K t1 r).2.2.1 (stepArrs p K t1 r).2.2.2.1
        (stepArrs p K t1 r).2.2.2.2 (buildComputablePaperTables child) := rfl

theorem stepTaps_getD (p K t1 r j1 : ℕ) (hj1 : j1 < t1) :
    (stepArrs p K t1 r).1.getD j1 [] =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map
        (foldV (pWork p K) (2 * pChild p K) t1 (effectiveFilterWidth (2 * pChild p K) r) j1) := by
  simp only [stepArrs, buildComputablePaperTables, buildComputablePaperTablesWithProgramCost,
    computableSincGaussianTapGivenPiLog2_eq]
  rw [array_getD_ofFn_of_lt t1 _ [] j1 hj1, array_getD_ofFn_of_lt t1 _ ([], 0) j1 hj1]
  dsimp only [runSequentialScanCostedSteps]
  apply List.map_congr_left
  intro u _
  unfold foldV
  refine Finset.sum_congr rfl fun s hs_mem => ?_
  have hs_lt : s < 2 * (2 * pChild p K) + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hs_mem).1
  exact read1D_runSequentialScanSteps_eq _ (2 * (2 * pChild p K) + 1) s hs_lt

theorem stepPre_read (p K t1 r k2 : ℕ) (hk2 : k2 < r) :
    read1D (stepArrs p K t1 r).2.1 k2 = stdV (2 * pChild p K) k2 (2 * r) false := by
  simp only [stepArrs, buildComputablePaperTables, buildComputablePaperTablesWithProgramCost]
  dsimp only [runSequentialScanCostedSteps]
  rw [read1D_runSequentialScanSteps_eq _ r k2 hk2]

theorem stepPost_read (p K t1 r k2 : ℕ) (hk2 : k2 < r) :
    read1D (stepArrs p K t1 r).2.2.1 k2 = stdV (2 * pChild p K) k2 (2 * r) true := by
  simp only [stepArrs, buildComputablePaperTables, buildComputablePaperTablesWithProgramCost]
  dsimp only [runSequentialScanCostedSteps]
  rw [read1D_runSequentialScanSteps_eq _ r k2 hk2]

theorem stepC0_read (p K t1 r u2 : ℕ) (hu2 : u2 < r) :
    (read1D (stepArrs p K t1 r).2.2.2.1 u2).1 = c0V (pWork p K) (2 * pChild p K) r u2 := by
  simp only [stepArrs, buildComputablePaperTables, buildComputablePaperTablesWithProgramCost]
  dsimp only [runSequentialScanCostedSteps]
  rw [read1D_ofFn_of_lt r _ hu2]
  dsimp only
  rw [read1D_runSequentialScanSteps_eq _ r u2 hu2]

theorem stepC1_read (p K t1 r u2 : ℕ) (hu2 : u2 < r) :
    (read1D (stepArrs p K t1 r).2.2.2.2 u2).1 = c1V (pWork p K) (2 * pChild p K) r u2 := by
  simp only [stepArrs, buildComputablePaperTables, buildComputablePaperTablesWithProgramCost]
  dsimp only [runSequentialScanCostedSteps]
  rw [read1D_ofFn_of_lt r _ hu2]
  dsimp only
  rw [read1D_runSequentialScanSteps_eq _ r u2 hu2]

/-! ## Segment and tape equalities -/

theorem tapeFrom_base (pIn p R : ℕ) :
    W7.tapeFrom W7.snapshotFormat pIn (buildComputablePaperTables (.base p R)) =
      leafSegC pIn p (Nat.log2 R) := by
  rw [build_base]
  exact leafSeg_eq_E _ _ _ _ _ _ (fun s hs u hu => leafTw_read p R s u hs hu)

theorem tapeFrom_step (pIn p K : ℕ) (ch : QuantizedFastDFTSpec) (hch : ch.p = pChild p K) :
    W7.tapeFrom W7.snapshotFormat pIn (buildComputablePaperTables (quantizedBoxGaussianStepSpec p K ch)) =
      preSegC pIn p K ++ W7.tapeFrom W7.snapshotFormat (2 * pChild p K) (buildComputablePaperTables ch) ++
        postSegC p K := by
  rw [quantizedBoxGaussianStepSpec, build_step]
  simp only [W7.tapeFrom, buildComputablePaperTables_p, hch]
  rw [preSeg_eq_E _ _ _ _ _ _ _ _ _ _ _ _ _ (fun j1 hj1 => stepTaps_getD p K _ _ j1 hj1)
      (fun k2 hk2 => stepPre_read p K _ _ k2 hk2) (fun k2 hk2 => stepPost_read p K _ _ k2 hk2),
    postSeg_eq_E _ _ _ _ _ _ _ _ _ _ (fun u2 hu2 => stepC0_read p K _ _ u2 hu2)
      (fun u2 hu2 => stepC1_read p K _ _ u2 hu2)]
  rfl

theorem tapeFromC_eq (L : ℕ) : ∀ pIn p K : ℕ,
    W7.tapeFrom W7.snapshotFormat pIn (buildComputablePaperTables (buildQuantizedSpecPaperStop L p K)) =
      tapeFromC pIn L p K := by
  induction L with
  | zero =>
    intro pIn p K
    rw [show buildQuantizedSpecPaperStop 0 p K = .base p (2 ^ K) from rfl, tapeFrom_base,
      nat_log2_two_pow]
    rfl
  | succ L ih =>
    intro pIn p K
    rw [show buildQuantizedSpecPaperStop (L + 1) p K =
        if 2 ^ K ≤ 4 * p * p then .base p (2 ^ K)
        else quantizedBoxGaussianStepSpec p K (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2))
        from rfl]
    by_cases h : 2 ^ K ≤ 4 * p * p
    · rw [if_pos h, tapeFrom_base, nat_log2_two_pow, tapeFromC, if_pos h]
    · rw [if_neg h, tapeFrom_step _ _ _ _ (buildQuantizedSpecPaperStop_p L (pChild p K) (K - K / 2)),
        ih, tapeFromC, if_neg h]

/-- **The contract's reference tape is the canonical tape.** -/
theorem tape_ref_eq (L p K : ℕ) :
    W7.tape W7.snapshotSchedule.toTapeFormat
        (W7.snapshotSchedule.ref (buildQuantizedSpecPaperStop L p K)) = tapeFromC 0 L p K :=
  tapeFromC_eq L 0 p K

#assert_std_axioms preSeg_eq_E postSeg_eq_E leafSeg_eq_E build_base leafTw_read build_step
  stepTaps_getD stepPre_read stepPost_read stepC0_read stepC1_read tapeFrom_base tapeFrom_step
  tapeFromC_eq tape_ref_eq

end WP.W7k2
