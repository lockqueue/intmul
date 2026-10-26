import IntMul.MaterializedAndComputable.FaithfulTablesPerturbation
import IntMul.MaterializedAndComputable.ComputableTranscendentals

/-!
# Part 2c — Computable Costed Table Builder (`buildComputablePaperTablesWithProgramCost`)

This module implements the 100% computable (`def`, zero `noncomputable`, zero `Real`, zero `Complex`)
table hierarchy builder `buildComputablePaperTablesWithProgramCost : QuantizedFastDFTSpec → ComputablePaperFastDFTSpec × ℕ`
that constructs all four table families (`T1`: leaf `twiddles`, `T2`: `preTwiddles`/`postTwiddles`,
`T3`: modulo-`W_eff` folded `filterTaps`, `T4`: passband `c0Table`/`c1Table`) from the fixed-point
`BitCostM` Taylor/series primitives in `ComputableTranscendentals.lean` while accumulating every
primitive's bit-operation and sequential scan cost into `.2 : ℕ`.

We prove:
1. `buildComputablePaperTablesWithProgramCost_faithful`:
   `TablesFaithful (buildComputablePaperTablesWithProgramCost spec).1 spec` for every valid
   executable specification `spec`, and
2. `buildComputablePaperTablesWithProgramCost_snd_le` (aliased as `tableBuilderWithProgramCost_snd_le`):
   `(buildComputablePaperTablesWithProgramCost spec).2 ≤ spec.precomputeSeriesTableCost`, together with
   explicit sublinear $O(\sqrt{n / \log n} \cdot \operatorname{polylog} n) \le O(n \log n)$ bounds
   along `buildQuantizedSpecPaperStop`.
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance 10000] instZeroIntElementary

/-! ### 1. Sequential Scan Cost Upper Bound Helper -/

/-- Modulo-`W_eff` folding of `2 * pSub + 1` raw Sinc-Gaussian filter taps into `W_eff` folded taps,
charged at `(2 * pSub + 1) * addBitCost (4 * p')` (`costedFoldRawTapRow`). -/
abbrev costedFoldRawTapRow (p' pSub W_eff : ℕ) (rawArr : Array ℤ) : BitCostM (List ℤ) :=
  ((List.range W_eff).map (fun u =>
    ∑ s ∈ (Finset.range (2 * pSub + 1)).filter (fun s => s % W_eff = u),
      read1D rawArr s),
   (2 * pSub + 1) * addBitCost (4 * p'))

/-- Upper bound for `(runSequentialScanCostedSteps f n).2.2` when every element cost is `≤ c`. -/
theorem runSequentialScanCostedSteps_cost_le_const {α : Type}
    (f : ℕ → BitCostM α) (n c : ℕ)
    (hc : ∀ i, i < n → (f i).2 ≤ c) :
    (runSequentialScanCostedSteps f n).2.2 ≤ n * c :=
  sumArrayCosts_ofFn_le_const n (fun i : Fin n => f i.val) c (fun i hi => hc i hi)

/-! ### 2. Computable Costed Table Hierarchy Builder (`buildComputablePaperTablesWithProgramCost`) -/

/-- Evaluates `computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s` given pre-evaluated
`(piRes, log2Res)` at `B_c = (pSub + 2) + (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 3 * (4 * (pSub + 1)) + 6`.
When `piRes = computablePiScaledWithCost B_c` and `log2Res = computableLog2ScaledWithCost B_c`,
this is definitionally equal (`rfl`) to `computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s`,
while avoiding redundant recomputation of `π` and `ln 2` across all `t1 * (2 * pSub + 1)` taps in the VM. -/
def computableSincGaussianTapGivenPiLog2
    (p_work pSub t1 : ℕ) (piRes log2Res : BitCostM ℤ) (j1 s : ℕ) : BitCostM ℤ :=
  let B := pSub + 2
  let M_θ := 4 * (pSub + 1)
  let N := 4 * M_θ + B + 4
  let B_c := B + N + 3 * M_θ + 6
  let Bint := B + 2 * N + 2 * M_θ + 6
  let w := Bint + 4 * N + 2 * M_θ + 2 * B_c + 2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 40
  let diffSRes := costedSubNatToInt0 s pSub
  let diffS : ℤ := diffSRes.1
  let prodTRes := costedMulInt w diffS (t1 : ℤ)
  let numTRes := costedSubNatAbsInt0 prodTRes.1 j1
  let numT : ℕ := numTRes.1
  let innerRes := computableSincGaussianTapInner p_work pSub B N B_c Bint w t1
    piRes.1.toNat log2Res.1.toNat numT
  (innerRes.1, piRes.2 + log2Res.2 + prodTRes.2 + addBitCost w + innerRes.2)

@[simp]
theorem computableSincGaussianTapGivenPiLog2_eq
    (p_work pSub t1 j1 s : ℕ) :
    computableSincGaussianTapGivenPiLog2 p_work pSub t1
      (computablePiScaledWithCost ((pSub + 2) + (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 3 * (4 * (pSub + 1)) + 6))
      (computableLog2ScaledWithCost ((pSub + 2) + (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 3 * (4 * (pSub + 1)) + 6))
      j1 s =
    computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s := rfl

/-- **100% Computable Costed Table Builder (`buildComputablePaperTablesWithProgramCost`, `[MS]` §3.3 (Lemma 3.2, eq. (7)) & §7)**:
Compiles a `QuantizedFastDFTSpec` schedule into its pure-integer `ComputablePaperFastDFTSpec` table
hierarchy while accumulating the exact integer `BitCostM` and sequential-scan runtime cost `.2 : ℕ`
of evaluating all four table families (`T1`–`T4`) via fixed-point series primitives:
- At `.base p R`: builds `K = Nat.log2 R` stages of leaf `BaseRadix2FFT` twiddles at precision
  `q_leaf = 2 * p + K + 8` via `computableStdCharWithProgramCost`.
- At `.step p K t1 r _c1 _v1Of child`: builds `t1` rows of modulo-`W_eff` folded `sincGaussian`
  spread taps from `2 * pSub + 1` raw taps via `computableSincGaussianTapWithProgramCost`,
  length-`r` chirp `preTwiddles`/`postTwiddles` via `computableStdCharWithProgramCost`, and
  length-`r` passband `c0Table`/`c1Table` via `computableC0C1WithProgramCost`, then recurses once
  on the shared child specification `child`. -/
def buildComputablePaperTablesWithProgramCost :
    QuantizedFastDFTSpec → ComputablePaperFastDFTSpec × ℕ
  | .base p R =>
    let K := Nat.log2 R
    let q_leaf := 2 * p + K + 8
    let stageRes : Array (Array (ℤ × ℤ) × ℕ) :=
      Array.ofFn (fun s : Fin K =>
        let st := runSequentialScanCostedSteps
          (fun u => computableStdCharWithProgramCost q_leaf u (2 ^ (s.val + 1)) false)
          (2 ^ (s.val + 1))
        (st.1, st.2.2 + st.2.1 * addBitCost (4 * p)))
    let twiddles : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun s : Fin K => (stageRes.getD s.val (#[], 0)).1)
    let leafCost : ℕ := sumArrayCosts stageRes
    (.basePow2 p K twiddles, leafCost)
  | .step p K t1 r _c1 _v1Of child =>
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
    let rowTapRes : Array (List ℤ × ℕ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        let rawScan := runSequentialScanCostedSteps
          (fun s => computableSincGaussianTapGivenPiLog2 p_work pSub t1 piTapRes log2TapRes j1.val s)
          (2 * pSub + 1)
        let foldRes := costedFoldRawTapRow p' pSub W_eff rawScan.1
        let folded : List ℤ := foldRes.1
        let foldCost : ℕ := foldRes.2
        (folded, rawScan.2.2 + rawScan.2.1 * addBitCost (4 * p') + foldCost))
    let filterTaps : Array (List ℤ) :=
      Array.ofFn (fun j1 : Fin t1 => (rowTapRes.getD j1.val ([], 0)).1)
    let stPre := runSequentialScanCostedSteps
      (fun k2 => computableStdCharWithProgramCost pSub k2 (2 * r) false) r
    let stPost := runSequentialScanCostedSteps
      (fun k2 => computableStdCharWithProgramCost pSub k2 (2 * r) true) r
    let preTwiddles : Array (ℤ × ℤ) := stPre.1
    let postTwiddles : Array (ℤ × ℤ) := stPost.1
    let stC01 := runSequentialScanCostedSteps
      (fun u2 => computableC0C1WithProgramCost p_work pSub r u2) r
    let c0Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r => (read1D stC01.1 u2.val).1)
    let c1Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r => (read1D stC01.1 u2.val).2)
    let stepCost : ℕ :=
      sumArrayCosts rowTapRes +
        stPre.2.2 + stPost.2.2 + stC01.2.2 +
        (stPre.2.1 + stPost.2.1 + 2 * stC01.2.1) * addBitCost (4 * p')
    let childRes := buildComputablePaperTablesWithProgramCost child
    (.step p pSub pSub t1 r filterTaps preTwiddles postTwiddles c0Table c1Table childRes.1,
     stepCost + childRes.2)

/-- First projection of `buildComputablePaperTablesWithProgramCost` (`buildComputablePaperTables`, `[MS]` §3.3, Lemma 3.2). -/
def buildComputablePaperTables (spec : QuantizedFastDFTSpec) : ComputablePaperFastDFTSpec :=
  (buildComputablePaperTablesWithProgramCost spec).1

@[simp]
theorem buildComputablePaperTablesWithProgramCost_fst_eq (spec : QuantizedFastDFTSpec) :
    (buildComputablePaperTablesWithProgramCost spec).1 = buildComputablePaperTables spec := rfl

@[simp]
theorem buildComputablePaperTables_p (spec : QuantizedFastDFTSpec) :
    (buildComputablePaperTables spec).p = spec.p := by
  cases spec <;> rfl

/-! ### 3. Faithfulness of `buildComputablePaperTablesWithProgramCost` (`TablesFaithful`) -/

/-- Accuracy, range, and dominance theorem for `computableC0C1WithProgramCost` under `0 < p_work`. -/
theorem computableC0C1WithProgramCost_spec_of_pos
    (p_work pSub r u2 : ℕ)
    (hp_work : 0 < p_work) (hr : 0 < r) (hu2 : u2 < r) :
    let res := (computableC0C1WithProgramCost p_work pSub r u2).1
    let c0_pair := res.1
    let c1_pair := res.2
    let α := alphaSchedule p_work
    let y : ℝ := (u2 : ℝ) / (r : ℝ)
    c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
    0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
    (2 * u2 = r → c1_pair = c0_pair) ∧
    (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1) :=
  computableC0C1Core_spec p_work pSub
    (pSub + 2)
    ((pSub + 2) + 2)
    (8 * p_work + 1)
    (32 * p_work + 1)
    (((pSub + 2) + 2) + 2 * (8 * p_work + 1) + 6)
    (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4)
    (((pSub + 2) + 2) + 2 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6)
    ((((pSub + 2) + 2) + 2 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6) +
      4 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) +
      2 * (((pSub + 2) + 2) + 2 * (8 * p_work + 1) + 6) +
      ((pSub + 2) + 2) + 2 * p_work + 2 * Nat.log2 r + 40)
    r u2 rfl rfl rfl rfl le_rfl le_rfl (by omega) hp_work hr hu2

/-- **Master Table-Builder Faithfulness Theorem (`buildComputablePaperTablesWithProgramCost_faithful`, `[MS]` §3.3 (Lemma 3.2, eq. (7)) & §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`, `hexec : spec.PaperExecutableValid`),
the computable table hierarchy `(buildComputablePaperTablesWithProgramCost spec).1` satisfies `TablesFaithful`. -/
theorem buildComputablePaperTablesWithProgramCost_faithful
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid) :
    TablesFaithful (buildComputablePaperTablesWithProgramCost spec).1 spec := by
  induction hvalid with
  | base p R =>
    cases hexec with
    | @base p K hp hK =>
      dsimp only [buildComputablePaperTablesWithProgramCost]
      rw [nat_log2_two_pow]
      refine TablesFaithful.base p K _ hp hK (fun s hs u hu => ?_)
      rw [array_getD_ofFn_of_lt K _ #[] s hs,
          array_getD_ofFn_of_lt K _ (#[], 0) s hs]
      dsimp only [runSequentialScanCostedSteps]
      rw [read1D_runSequentialScanSteps_eq _ (2 ^ (s + 1)) u hu]
      have hden : 0 < 2 ^ (s + 1) := pow_pos zero_lt_two (s + 1)
      have herr := computableStdCharWithProgramCost_error_le (2 * p + K + 8) u (2 ^ (s + 1)) false hden hu.le
      simpa using herr
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hexec with
    | step hv1_eq hchild_exec =>
      dsimp only [buildComputablePaperTablesWithProgramCost, computableSincGaussianTapGivenPiLog2_eq]
      have hp_work_pos : 0 < pWork p K := by unfold pWork; omega
      have hpSub_pos : 0 < 2 * pChild p K := by unfold pChild pWork; omega
      refine TablesFaithful.step p K t1 r c1 v1Of _ _ _ _ _ _ child hv1_eq
        (fun j1 hj1 => ?_) (fun k2 hk2 => ?_) (fun k2 hk2 => ?_) (fun u2 hu2 => ?_)
        (ih hchild_exec)
      · refine ⟨fun s => (computableSincGaussianTapWithProgramCost (pWork p K) (2 * pChild p K) t1 j1 s).1,
          ?_, ?_, ?_⟩
        · rw [array_getD_ofFn_of_lt t1 _ [] j1 hj1,
              array_getD_ofFn_of_lt t1 _ ([], 0) j1 hj1]
          dsimp only [runSequentialScanCostedSteps]
          apply List.map_congr_left
          intro u _
          refine Finset.sum_congr rfl fun s hs_mem => ?_
          have hs_lt : s < 2 * (2 * pChild p K) + 1 :=
            Finset.mem_range.mp (Finset.mem_filter.mp hs_mem).1
          exact read1D_runSequentialScanSteps_eq _ (2 * (2 * pChild p K) + 1) s hs_lt
        · intro s hs
          exact (computableSincGaussianTapWithProgramCost_spec
            (pWork p K) (2 * pChild p K) t1 j1 s hp_work_pos hpSub_pos ht1 hj1 hs).1
        · intro s hs
          exact (computableSincGaussianTapWithProgramCost_spec
            (pWork p K) (2 * pChild p K) t1 j1 s hp_work_pos hpSub_pos ht1 hj1 hs).2
      · dsimp only [runSequentialScanCostedSteps]
        rw [read1D_runSequentialScanSteps_eq _ r k2 hk2]
        have herr := computableStdCharWithProgramCost_error_le
          (2 * pChild p K) k2 (2 * r) false (by omega) (by omega)
        have hzeta : stdChar ((if false then -(k2 : ℝ) else (k2 : ℝ)) / ((2 * r : ℕ) : ℝ)) =
            zetaRoot r (k2 : ℝ) := by
          unfold zetaRoot
          push_cast
          rfl
        rwa [hzeta] at herr
      · dsimp only [runSequentialScanCostedSteps]
        rw [read1D_runSequentialScanSteps_eq _ r k2 hk2]
        have herr := computableStdCharWithProgramCost_error_le
          (2 * pChild p K) k2 (2 * r) true (by omega) (by omega)
        have hzeta : stdChar ((if true then -(k2 : ℝ) else (k2 : ℝ)) / ((2 * r : ℕ) : ℝ)) =
            zetaRoot r (-(k2 : ℝ)) := by
          unfold zetaRoot
          push_cast
          rfl
        rwa [hzeta] at herr
      · dsimp only [runSequentialScanCostedSteps]
        rw [read1D_ofFn_of_lt r _ hu2,
            read1D_ofFn_of_lt r _ hu2,
            read1D_runSequentialScanSteps_eq _ r u2 hu2]
        exact computableC0C1WithProgramCost_spec_of_pos
          (pWork p K) (2 * pChild p K) r u2 hp_work_pos hr hu2

/-- Alias of `buildComputablePaperTablesWithProgramCost_faithful` for `buildComputablePaperTables`. -/
theorem buildComputablePaperTables_faithful
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid) :
    TablesFaithful (buildComputablePaperTables spec) spec :=
  buildComputablePaperTablesWithProgramCost_faithful spec hvalid hexec

/-! ### 3b. Table-Builder Call-Site Operand Width Soundness (`TableBuilderCallSitesWidthSound`) -/

/-- **Table-Builder Call-Site Operand Width Soundness Predicate
(`TableBuilderCallSitesWidthSound`, `[MS]` §3.3 (Lemma 3.2, eq. (8)) & §7.2)**:
Certifies across every level of `buildComputablePaperTablesWithProgramCost spec` that:
- At a `.base p R` leaf (`K = Nat.log2 R`, `q_leaf = 2 * p + K + 8`), for every stage `s < K`
  and index `u < 2 ^ (s + 1)`, every priced primitive inside
  `computableStdCharWithProgramCost q_leaf u (2 ^ (s + 1)) false` fits in its declared bit-width
  (`StdCharWidthSound q_leaf u (2 ^ (s + 1))`).
- At a `.step p K t1 r _c1 _v1Of child` node (`p' = pChild p K`, `p_work = pWork p K`,
  `pSub = 2 * p'`, `W_eff = effectiveFilterWidth pSub r`):
  1. For every `j1 < t1` and `s < 2 * pSub + 1`, every priced primitive inside
     `computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s` fits in its declared bit-width
     (`SincGaussianTapWidthSound p_work pSub t1 j1 s`), and its output tap fits in `4 * p'` signed bits,
  2. For every `j1 < t1` and `u < W_eff`, the modulo-`W_eff` folded tap sum fits in `4 * p'` signed
     bits (`FitsSignedScalarWord (4 * p')`), matching `foldCost = (2 * pSub + 1) * addBitCost (4 * p')`,
  3. For every `k2 < r`, every priced primitive inside `computableStdCharWithProgramCost pSub k2 (2 * r)`
     fits in its declared bit-width (`StdCharWidthSound pSub k2 (2 * r)`),
  4. For every `u2 < r`, every priced primitive inside `computableC0C1WithProgramCost p_work pSub r u2`
     fits in its declared bit-width (`C0C1WidthSound p_work pSub r u2`), and
  5. Recursively, `TableBuilderCallSitesWidthSound child`. -/
def TableBuilderCallSitesWidthSound : QuantizedFastDFTSpec → Prop
  | .base p R =>
    let K := Nat.log2 R
    let q_leaf := 2 * p + K + 8
    ∀ s < K, ∀ u < 2 ^ (s + 1), StdCharWidthSound q_leaf u (2 ^ (s + 1))
  | .step p K t1 r _c1 _v1Of child =>
    let p' := pChild p K
    let p_work := pWork p K
    let pSub := 2 * p'
    let W_eff := effectiveFilterWidth pSub r
    (∀ j1 < t1, ∀ s < 2 * pSub + 1,
      SincGaussianTapWidthSound p_work pSub t1 j1 s ∧
      FitsSignedScalarWord (4 * p') (computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1) ∧
    (∀ j1 < t1, ∀ u < W_eff,
      FitsSignedScalarWord (4 * p')
        (∑ s ∈ (Finset.range (2 * pSub + 1)).filter (fun s => s % W_eff = u),
          (computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1)) ∧
    (∀ k2 < r, StdCharWidthSound pSub k2 (2 * r)) ∧
    (∀ u2 < r, C0C1WidthSound p_work pSub r u2) ∧
    TableBuilderCallSitesWidthSound child

/-- If `G s` satisfies `(G s).natAbs ≤ 2 ^ pSub + 1` for all `s < 2 * pSub + 1`, where
`pSub = 2 * p'` and `12 ≤ p'`, then the folded sum over `s ∈ (Finset.range (2 * pSub + 1)).filter ...`
fits in `4 * p'` signed bits (`FitsSignedScalarWord (4 * p')`). -/
theorem fitsSignedScalarWord_fold_sum
    (p' pSub W_eff u : ℕ) (G : ℕ → ℤ)
    (hp' : 12 ≤ p') (hpSub : pSub = 2 * p')
    (hG : ∀ s < 2 * pSub + 1, (G s).natAbs ≤ 2 ^ pSub + 1) :
    FitsSignedScalarWord (4 * p')
      (∑ s ∈ (Finset.range (2 * pSub + 1)).filter (fun s => s % W_eff = u), G s) := by
  refine fitsSignedScalarWord_of_abs_le_two_pow (4 * p') _ ?_
  set S := (Finset.range (2 * pSub + 1)).filter (fun s => s % W_eff = u)
  push_cast
  have h1_le : 1 ≤ 2 ^ pSub := Nat.one_le_two_pow
  have hsum_le :
      |∑ s ∈ S, (G s : ℝ)| ≤ (S.card : ℝ) * (2 : ℝ) ^ (pSub + 1) := by
    calc |∑ s ∈ S, (G s : ℝ)|
        ≤ ∑ s ∈ S, |(G s : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ S, (2 : ℝ) ^ (pSub + 1) := by
          refine Finset.sum_le_sum fun s hs_mem => ?_
          have hs_lt : s < 2 * pSub + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hs_mem).1
          have hGs : (G s).natAbs ≤ 2 ^ pSub + 1 := hG s hs_lt
          have hnatAbs : (G s).natAbs ≤ 2 ^ (pSub + 1) := by rw [pow_succ]; omega
          have hcast : |(G s : ℝ)| = ((G s).natAbs : ℝ) := by
            rw [← Int.cast_abs, ← Nat.cast_natAbs]
          rw [hcast]
          exact_mod_cast hnatAbs
      _ = (S.card : ℝ) * (2 : ℝ) ^ (pSub + 1) := by simp
  have hp1_pow : p' + 1 ≤ 2 ^ p' := add_one_le_two_pow p'
  have hcard_nat : S.card ≤ 2 ^ (p' + 2) := by
    have h1 : S.card ≤ 2 * pSub + 1 := (Finset.card_filter_le _ _).trans (by simp)
    have h2 : 2 * pSub + 1 ≤ 4 * (p' + 1) := by omega
    have h3 : 4 * (p' + 1) ≤ 4 * 2 ^ p' := Nat.mul_le_mul_left 4 hp1_pow
    have h4 : 4 * 2 ^ p' = 2 ^ (p' + 2) := by rw [pow_add]; ring
    omega
  have hcard_r : (S.card : ℝ) ≤ (2 : ℝ) ^ (p' + 2) := by exact_mod_cast hcard_nat
  calc |∑ s ∈ S, (G s : ℝ)|
      ≤ (S.card : ℝ) * (2 : ℝ) ^ (pSub + 1) := hsum_le
    _ ≤ (2 : ℝ) ^ (p' + 2) * (2 : ℝ) ^ (pSub + 1) :=
        mul_le_mul_of_nonneg_right hcard_r (by positivity)
    _ = (2 : ℝ) ^ (p' + 2 + (pSub + 1)) := (pow_add (2 : ℝ) _ _).symm
    _ ≤ (2 : ℝ) ^ (4 * p' - 2) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

/-- If `z : ℤ` satisfies `z.natAbs ≤ 2 ^ pSub + 1` where `pSub = 2 * p'` and `12 ≤ p'`,
then `z` fits in `4 * p'` signed bits (`FitsSignedScalarWord (4 * p') z`). -/
theorem fitsSignedScalarWord_tap_of_natAbs_le
    (p' pSub : ℕ) (z : ℤ)
    (hp' : 12 ≤ p') (hpSub : pSub = 2 * p')
    (hz : z.natAbs ≤ 2 ^ pSub + 1) :
    FitsSignedScalarWord (4 * p') z := by
  have h1_le : 1 ≤ 2 ^ pSub := Nat.one_le_two_pow
  have hnatAbs : z.natAbs ≤ 2 ^ (pSub + 1) := by
    rw [pow_succ]
    omega
  exact fitsSignedScalarWord_of_natAbs_le_two_pow (4 * p') (pSub + 1) z hnatAbs (by omega)

/-- **Table-Builder Call-Site Operand Width Soundness Theorem
(`tableBuilder_widths_sound`, `[MS]` §3.3 (Lemma 3.2, eq. (8)) & §7.2)**:
For every valid specification `spec : QuantizedFastDFTSpec`, all priced call sites inside
`buildComputablePaperTablesWithProgramCost spec` and `ComputableTranscendentals.lean` fit within
their declared bit-width parameters (`TableBuilderCallSitesWidthSound spec`). -/
theorem tableBuilder_widths_sound
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) :
    TableBuilderCallSitesWidthSound spec := by
  induction hvalid with
  | base p R =>
    dsimp only [TableBuilderCallSitesWidthSound]
    intro s _hs u hu
    exact computableStdCharWithProgramCost_widths_sound
      (2 * p + Nat.log2 R + 8) u (2 ^ (s + 1)) (pow_pos zero_lt_two (s + 1)) hu.le
  | @step p K t1 r c1 v1Of child _hp _hK ht1 _ht1_le hr _hr_le _hsize _hc1 _heven _hchild_size _hchild_p _hchild _hv1 _hv1_lt ih =>
    dsimp only [TableBuilderCallSitesWidthSound]
    have hp'_eq : pChild p K = p + 2 * K + 12 := pChild_eq_additive p K
    have hp'_ge12 : 12 ≤ pChild p K := by omega
    have hp_work_pos : 0 < pWork p K := by dsimp [pWork]; omega
    have hpSub_pos : 0 < 2 * pChild p K := by omega
    refine ⟨?_, ?_, ?_, ?_, ih⟩
    · intro j1 hj1 s hs
      refine ⟨computableSincGaussianTapWithProgramCost_widths_sound
        (pWork p K) (2 * pChild p K) t1 j1 s hp_work_pos hpSub_pos ht1 hj1 hs, ?_⟩
      exact fitsSignedScalarWord_tap_of_natAbs_le (pChild p K) (2 * pChild p K)
        (computableSincGaussianTapWithProgramCost (pWork p K) (2 * pChild p K) t1 j1 s).1
        hp'_ge12 rfl
        (computableSincGaussianTapWithProgramCost_spec
          (pWork p K) (2 * pChild p K) t1 j1 s hp_work_pos hpSub_pos ht1 hj1 hs).2
    · intro j1 hj1 u _hu
      refine fitsSignedScalarWord_fold_sum (pChild p K) (2 * pChild p K)
        (effectiveFilterWidth (2 * pChild p K) r) u
        (fun s => (computableSincGaussianTapWithProgramCost (pWork p K) (2 * pChild p K) t1 j1 s).1)
        hp'_ge12 rfl (fun s hs_lt => ?_)
      exact (computableSincGaussianTapWithProgramCost_spec
        (pWork p K) (2 * pChild p K) t1 j1 s hp_work_pos hpSub_pos ht1 hj1 hs_lt).2
    · intro k2 hk2
      exact computableStdCharWithProgramCost_widths_sound (2 * pChild p K) k2 (2 * r) (by omega) (by omega)
    · intro u2 hu2
      exact computableC0C1WithProgramCost_widths_sound (pWork p K) (2 * pChild p K) r u2 hp_work_pos hr hu2

/-! ### 4. Program-Derived Cost Bound for `buildComputablePaperTablesWithProgramCost` -/

/-- Per-level series-table precomputation bit-operation bound at a `.base p R` leaf (`T1`). -/
def precomputeLeafSeriesTableBitCost (p R : ℕ) : ℕ :=
  let K := Nat.log2 R
  let M := 2 * p + 2 * K + 40
  K * R * (18000 * M ^ 4 + addBitCost (4 * p))

/-- Per-level series-table precomputation bit-operation bound at a `.step` node `(p, K, t1, r)` (`T2`–`T4`). -/
def precomputeStepSeriesTableBitCost (p K t1 r : ℕ) : ℕ :=
  let p' := pChild p K
  let rawTaps := t1 * (4 * p' + 1)
  let M := 1050 * (pWork p K + 2 * p' + Nat.log2 t1 + Nat.log2 (2 * r) + 21)
  (rawTaps + 4 * r) * (18000 * M ^ 4 + 2 * addBitCost (4 * p'))

/-- Schedule-level series-evaluation table precomputation bit-operation cost across all levels
of a `QuantizedFastDFTSpec` (`QuantizedFastDFTSpec.precomputeSeriesTableCost`, `[MS]` §3.3 (Lemma 3.2, eq. (8)) & §7.2). -/
def QuantizedFastDFTSpec.precomputeSeriesTableCost : QuantizedFastDFTSpec → ℕ
  | .base p R => precomputeLeafSeriesTableBitCost p R
  | .step p K t1 r _c1 _v1Of child =>
    precomputeStepSeriesTableBitCost p K t1 r + child.precomputeSeriesTableCost

/-- **Program-Derived Cost Bound for `buildComputablePaperTablesWithProgramCost`
(`buildComputablePaperTablesWithProgramCost_snd_le`, `[MS]` §3.3 (Lemma 3.2, eq. (8)) & §7.2)**:
For every `spec : QuantizedFastDFTSpec`, the integer runtime cost `.2` accumulated bottom-up
by `buildComputablePaperTablesWithProgramCost spec` from the `BitCostM` series evaluators and
sequential scans is bounded by `spec.precomputeSeriesTableCost`. -/
theorem buildComputablePaperTablesWithProgramCost_snd_le (spec : QuantizedFastDFTSpec) :
    (buildComputablePaperTablesWithProgramCost spec).2 ≤
      spec.precomputeSeriesTableCost := by
  induction spec with
  | base p R =>
    dsimp only [buildComputablePaperTablesWithProgramCost,
      QuantizedFastDFTSpec.precomputeSeriesTableCost, precomputeLeafSeriesTableBitCost]
    set K := Nat.log2 R
    set q_leaf := 2 * p + K + 8
    set M := 2 * p + 2 * K + 40
    rw [Nat.mul_assoc]
    refine sumArrayCosts_ofFn_le_const K _ (R * (18000 * M ^ 4 + addBitCost (4 * p))) (fun s hs_lt => ?_)
    dsimp only
    rw [runSequentialScanCostedSteps_steps]
    have hR_pos : 1 ≤ R := by
      by_contra h0
      have : R = 0 := by omega
      subst this
      simp [K] at hs_lt
    have h2s_le_R : 2 ^ (s + 1) ≤ R :=
      (Nat.pow_le_pow_right zero_lt_two hs_lt).trans (two_pow_log2_le R hR_pos)
    have hscan_le :
        (runSequentialScanCostedSteps
          (fun u => computableStdCharWithProgramCost q_leaf u (2 ^ (s + 1)) false)
          (2 ^ (s + 1))).2.2 ≤
        2 ^ (s + 1) * (18000 * M ^ 4) := by
      refine runSequentialScanCostedSteps_cost_le_const _ (2 ^ (s + 1)) (18000 * M ^ 4) (fun u _ => ?_)
      have h1 := computableStdCharWithProgramCost_snd_le q_leaf u (2 ^ (s + 1)) false
      dsimp only at h1
      rw [nat_log2_two_pow] at h1
      have hM : q_leaf + (s + 1) + 1 + 30 ≤ M := by dsimp [q_leaf, M]; omega
      exact h1.trans (Nat.mul_le_mul_left 18000 (Nat.pow_le_pow_left hM 4))
    calc (runSequentialScanCostedSteps
            (fun u => computableStdCharWithProgramCost q_leaf u (2 ^ (s + 1)) false)
            (2 ^ (s + 1))).2.2 + 2 ^ (s + 1) * addBitCost (4 * p)
        ≤ 2 ^ (s + 1) * (18000 * M ^ 4) + 2 ^ (s + 1) * addBitCost (4 * p) :=
          Nat.add_le_add_right hscan_le _
      _ = 2 ^ (s + 1) * (18000 * M ^ 4 + addBitCost (4 * p)) := by ring
      _ ≤ R * (18000 * M ^ 4 + addBitCost (4 * p)) := Nat.mul_le_mul_right _ h2s_le_R
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [buildComputablePaperTablesWithProgramCost, computableSincGaussianTapGivenPiLog2_eq,
      QuantizedFastDFTSpec.precomputeSeriesTableCost, precomputeStepSeriesTableBitCost]
    set p' := pChild p K
    set p_work := pWork p K
    set pSub := 2 * p'
    set M := 1050 * (p_work + 2 * p' + Nat.log2 t1 + Nat.log2 (2 * r) + 21)
    set E := 18000 * M ^ 4 + 2 * addBitCost (4 * p')
    have h2pSub_eq : 2 * pSub + 1 = 4 * p' + 1 := by dsimp [pSub]; ring
    have hrow_le :
        sumArrayCosts (Array.ofFn (fun j1 : Fin t1 =>
          let rawScan := runSequentialScanCostedSteps
            (fun s => computableSincGaussianTapWithProgramCost p_work pSub t1 j1.val s)
            (2 * pSub + 1)
          let folded : List ℤ :=
            (List.range (effectiveFilterWidth pSub r)).map (fun u =>
              ∑ s ∈ (Finset.range (2 * pSub + 1)).filter (fun s => s % effectiveFilterWidth pSub r = u),
                read1D rawScan.1 s)
          let foldCost : ℕ := (2 * pSub + 1) * addBitCost (4 * p')
          (folded, rawScan.2.2 + rawScan.2.1 * addBitCost (4 * p') + foldCost))) ≤
        (t1 * (4 * p' + 1)) * E := by
      rw [Nat.mul_assoc]
      refine sumArrayCosts_ofFn_le_const t1 _ ((4 * p' + 1) * E) (fun j1 _ => ?_)
      dsimp only
      rw [runSequentialScanCostedSteps_steps, h2pSub_eq]
      have hraw_le :
          (runSequentialScanCostedSteps
            (fun s => computableSincGaussianTapWithProgramCost p_work pSub t1 j1 (s : ℕ))
            (4 * p' + 1)).2.2 ≤
          (4 * p' + 1) * (18000 * M ^ 4) := by
        refine runSequentialScanCostedSteps_cost_le_const _ (4 * p' + 1) (18000 * M ^ 4) (fun s _ => ?_)
        have h1 := computableSincGaussianTapWithProgramCost_snd_le p_work pSub t1 j1 s
        dsimp only at h1
        have hM_le : 200 * (p_work + pSub + Nat.log2 t1 + 1 + 20) ≤ M := by dsimp [pSub, M]; omega
        calc (computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).2
            ≤ 7000 * (200 * (p_work + pSub + Nat.log2 t1 + 1 + 20)) ^ 4 := h1
          _ ≤ 18000 * M ^ 4 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hM_le 4)
      calc (runSequentialScanCostedSteps
              (fun s => computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s)
              (4 * p' + 1)).2.2 +
            (4 * p' + 1) * addBitCost (4 * p') + (4 * p' + 1) * addBitCost (4 * p')
          ≤ (4 * p' + 1) * (18000 * M ^ 4) +
            (4 * p' + 1) * addBitCost (4 * p') + (4 * p' + 1) * addBitCost (4 * p') :=
            Nat.add_le_add_right (Nat.add_le_add_right hraw_le _) _
        _ = (4 * p' + 1) * E := by
            dsimp [E]
            generalize 18000 * M ^ 4 = C_M
            generalize addBitCost (4 * p') = A
            ring
    have hpre_le :
        (runSequentialScanCostedSteps
          (fun k2 => computableStdCharWithProgramCost pSub k2 (2 * r) false) r).2.2 ≤
        r * (18000 * M ^ 4) := by
      refine runSequentialScanCostedSteps_cost_le_const _ r (18000 * M ^ 4) (fun k2 _ => ?_)
      have h1 := computableStdCharWithProgramCost_snd_le pSub k2 (2 * r) false
      dsimp only at h1
      have hM_le : pSub + Nat.log2 (2 * r) + 1 + 30 ≤ M := by dsimp [pSub, M]; omega
      exact h1.trans (Nat.mul_le_mul_left 18000 (Nat.pow_le_pow_left hM_le 4))
    have hpost_le :
        (runSequentialScanCostedSteps
          (fun k2 => computableStdCharWithProgramCost pSub k2 (2 * r) true) r).2.2 ≤
        r * (18000 * M ^ 4) := by
      refine runSequentialScanCostedSteps_cost_le_const _ r (18000 * M ^ 4) (fun k2 _ => ?_)
      have h1 := computableStdCharWithProgramCost_snd_le pSub k2 (2 * r) true
      dsimp only at h1
      have hM_le : pSub + Nat.log2 (2 * r) + 1 + 30 ≤ M := by dsimp [pSub, M]; omega
      exact h1.trans (Nat.mul_le_mul_left 18000 (Nat.pow_le_pow_left hM_le 4))
    have hc01_le :
        (runSequentialScanCostedSteps
          (fun u2 => computableC0C1WithProgramCost p_work pSub r u2) r).2.2 ≤
        r * (18000 * M ^ 4) := by
      refine runSequentialScanCostedSteps_cost_le_const _ r (18000 * M ^ 4) (fun u2 _ => ?_)
      have h1 := computableC0C1WithProgramCost_snd_le p_work pSub r u2
      dsimp only at h1
      have hlog_le : Nat.log2 r ≤ Nat.log2 (2 * r) := nat_log2_mono (by omega)
      have hM_le : 1050 * (p_work + pSub + Nat.log2 r + 1 + 10) ≤ M := by dsimp [pSub, M]; omega
      calc (computableC0C1WithProgramCost p_work pSub r u2).2
          ≤ 7000 * (1050 * (p_work + pSub + Nat.log2 r + 1 + 10)) ^ 4 := h1
        _ ≤ 18000 * M ^ 4 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hM_le 4)
    rw [runSequentialScanCostedSteps_steps,
        runSequentialScanCostedSteps_steps,
        runSequentialScanCostedSteps_steps]
    have hstep_le :
        sumArrayCosts (Array.ofFn (fun j1 : Fin t1 =>
          let rawScan := runSequentialScanCostedSteps
            (fun s => computableSincGaussianTapWithProgramCost p_work pSub t1 j1.val s)
            (2 * pSub + 1)
          let folded : List ℤ :=
            (List.range (effectiveFilterWidth pSub r)).map (fun u =>
              ∑ s ∈ (Finset.range (2 * pSub + 1)).filter (fun s => s % effectiveFilterWidth pSub r = u),
                read1D rawScan.1 s)
          let foldCost : ℕ := (2 * pSub + 1) * addBitCost (4 * p')
          (folded, rawScan.2.2 + rawScan.2.1 * addBitCost (4 * p') + foldCost))) +
          (runSequentialScanCostedSteps
            (fun k2 => computableStdCharWithProgramCost pSub k2 (2 * r) false) r).2.2 +
          (runSequentialScanCostedSteps
            (fun k2 => computableStdCharWithProgramCost pSub k2 (2 * r) true) r).2.2 +
          (runSequentialScanCostedSteps
            (fun u2 => computableC0C1WithProgramCost p_work pSub r u2) r).2.2 +
          (r + r + 2 * r) * addBitCost (4 * p') ≤
        (t1 * (4 * p' + 1) + 4 * r) * E := by
      have hsum4 :
          (t1 * (4 * p' + 1)) * E +
            r * (18000 * M ^ 4) + r * (18000 * M ^ 4) + r * (18000 * M ^ 4) +
            (r + r + 2 * r) * addBitCost (4 * p') ≤
          (t1 * (4 * p' + 1) + 4 * r) * E := by
        dsimp [E]
        generalize 18000 * M ^ 4 = C_M
        generalize addBitCost (4 * p') = A
        have h_lhs :
            (t1 * (4 * p' + 1)) * (C_M + 2 * A) +
              r * C_M + r * C_M + r * C_M + (r + r + 2 * r) * A =
            (t1 * (4 * p' + 1)) * (C_M + 2 * A) + 3 * (r * C_M) + 4 * (r * A) := by ring
        have h_rhs :
            (t1 * (4 * p' + 1) + 4 * r) * (C_M + 2 * A) =
            (t1 * (4 * p' + 1)) * (C_M + 2 * A) + 4 * (r * C_M) + 8 * (r * A) := by ring
        rw [h_lhs, h_rhs]
        generalize r * C_M = RC
        generalize r * A = RA
        omega
      exact (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrow_le hpre_le) hpost_le) hc01_le) _).trans hsum4
    exact Nat.add_le_add hstep_le ih

/-- Alias of `buildComputablePaperTablesWithProgramCost_snd_le` (`tableBuilderWithProgramCost_snd_le`). -/
theorem tableBuilderWithProgramCost_snd_le (spec : QuantizedFastDFTSpec) :
    (buildComputablePaperTablesWithProgramCost spec).2 ≤
      spec.precomputeSeriesTableCost :=
  buildComputablePaperTablesWithProgramCost_snd_le spec

/-! ### 5. Sublinear $O(\sqrt{n / \log n} \cdot \operatorname{polylog} n)$ Bound Along `buildQuantizedSpecPaperStop` -/

/-- At a `.base p (2 ^ K)` leaf with `1 ≤ P`, `p ≤ P`, `2 ^ K ≤ 4 * P * P`, and `K ≤ 4 * P + 4`,
`precomputeLeafSeriesTableBitCost p (2 ^ K) ≤ 2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6)`. -/
theorem precomputeLeafSeriesTableBitCost_le_of_stop
    (p K P : ℕ) (hP : 1 ≤ P) (hp_le : p ≤ P) (h2K : 2 ^ K ≤ 4 * P * P) (hK : K ≤ 4 * P + 4) :
    precomputeLeafSeriesTableBitCost p (2 ^ K) ≤
      2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6) := by
  dsimp only [precomputeLeafSeriesTableBitCost, addBitCost]
  rw [nat_log2_two_pow]
  have hK_le : K ≤ 8 * P := by omega
  have hM_le : 2 * p + 2 * K + 40 ≤ 58 * P := by omega
  have hhalf_sq : (2 ^ (K / 2)) ^ 2 ≤ (2 * P) ^ 2 := by
    have hmul : K / 2 * 2 ≤ K := Nat.div_mul_le_self K 2
    calc (2 ^ (K / 2)) ^ 2 = 2 ^ (K / 2 * 2) := (pow_mul 2 (K / 2) 2).symm
      _ ≤ 2 ^ K := Nat.pow_le_pow_right zero_lt_two hmul
      _ ≤ 4 * P * P := h2K
      _ = (2 * P) ^ 2 := by ring
  have hhalf_le : 2 ^ (K / 2) ≤ 2 * P :=
    (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hhalf_sq
  have h2K_split : 2 ^ K ≤ 2 ^ (K - K / 2) * (2 * P) := by
    have hsplit : 2 ^ K = 2 ^ (K - K / 2) * 2 ^ (K / 2) := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.div_le_self K 2)]
    rw [hsplit]
    exact Nat.mul_le_mul_left _ hhalf_le
  have h4p_le : 4 * p ≤ 4 * P ^ 4 := by
    have hp_le4 : P ≤ P ^ 4 := Nat.le_self_pow (by decide) P
    exact (Nat.mul_le_mul_left 4 hp_le).trans (Nat.mul_le_mul_left 4 hp_le4)
  have hterm : 18000 * (2 * p + 2 * K + 40) ^ 4 + 4 * p ≤ (18000 * 58 ^ 4 + 4) * P ^ 4 := by
    have hpow : (2 * p + 2 * K + 40) ^ 4 ≤ (58 * P) ^ 4 := Nat.pow_le_pow_left hM_le 4
    have hpow_eq : (58 * P) ^ 4 = 58 ^ 4 * P ^ 4 := mul_pow 58 P 4
    have h1 : 18000 * (2 * p + 2 * K + 40) ^ 4 ≤ 18000 * (58 ^ 4 * P ^ 4) :=
      Nat.mul_le_mul_left 18000 (hpow.trans_eq hpow_eq)
    have h2 : 18000 * (58 ^ 4 * P ^ 4) + 4 * P ^ 4 = (18000 * 58 ^ 4 + 4) * P ^ 4 := by ring
    exact (Nat.add_le_add h1 h4p_le).trans_eq h2
  calc K * 2 ^ K * (18000 * (2 * p + 2 * K + 40) ^ 4 + 4 * p)
      ≤ (8 * P) * (2 ^ (K - K / 2) * (2 * P)) * ((18000 * 58 ^ 4 + 4) * P ^ 4) :=
        Nat.mul_le_mul (Nat.mul_le_mul hK_le h2K_split) hterm
    _ = 2 ^ (K - K / 2) * ((16 * (18000 * 58 ^ 4 + 4)) * P ^ 6) := by ring
    _ ≤ 2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right (P ^ 6) (by decide))

/-- At a `.step` node `(p, K, 2 ^ (K / 2), 2 ^ (K - K / 2))` with `pChild p K ≤ P`,
`precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) ≤
  2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6)`. -/
theorem precomputeStepSeriesTableBitCost_le_of_step
    (p K P : ℕ) (hp'_le : pChild p K ≤ P) :
    precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) ≤
      2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6) := by
  dsimp only [precomputeStepSeriesTableBitCost, addBitCost]
  set p' := pChild p K
  set K' := K - K / 2
  have hp'_eq : p' = p + 2 * K + 12 := pChild_eq_additive p K
  have hp_work_eq : pWork p K = p + K + 6 := rfl
  have hP_ge12 : 12 ≤ P := by omega
  have h2_pow_r : 2 * 2 ^ K' = 2 ^ (K' + 1) := by rw [pow_succ']
  rw [nat_log2_two_pow, h2_pow_r, nat_log2_two_pow]
  have hM_le : 1050 * (pWork p K + 2 * p' + K / 2 + (K' + 1) + 21) ≤ 5250 * P := by
    dsimp [K']
    omega
  have h2_div : 2 ^ (K / 2) ≤ 2 ^ K' :=
    Nat.pow_le_pow_right zero_lt_two (by dsimp [K']; omega)
  have hentries_le :
      2 ^ (K / 2) * (4 * p' + 1) + 4 * 2 ^ K' ≤ 2 ^ K' * (5 * P) := by
    have h4p' : 4 * p' + 5 ≤ 5 * P := by omega
    calc 2 ^ (K / 2) * (4 * p' + 1) + 4 * 2 ^ K'
        ≤ 2 ^ K' * (4 * p' + 1) + 4 * 2 ^ K' :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ h2_div) _
      _ = 2 ^ K' * (4 * p' + 5) := by ring
      _ ≤ 2 ^ K' * (5 * P) := Nat.mul_le_mul_left (2 ^ K') h4p'
  have h8p'_le : 2 * (4 * p') ≤ 8 * P ^ 4 := by
    have hp_le4 : P ≤ P ^ 4 := Nat.le_self_pow (by decide) P
    have h1 : 2 * (4 * p') ≤ 8 * P := by omega
    exact h1.trans (Nat.mul_le_mul_left 8 hp_le4)
  have hcost_per_entry :
      18000 * (1050 * (pWork p K + 2 * p' + K / 2 + (K' + 1) + 21)) ^ 4 + 2 * (4 * p') ≤
        (18000 * 5250 ^ 4 + 8) * P ^ 4 := by
    have hpow : (1050 * (pWork p K + 2 * p' + K / 2 + (K' + 1) + 21)) ^ 4 ≤ (5250 * P) ^ 4 :=
      Nat.pow_le_pow_left hM_le 4
    have hpow_eq : (5250 * P) ^ 4 = 5250 ^ 4 * P ^ 4 := mul_pow 5250 P 4
    have h1 : 18000 * (1050 * (pWork p K + 2 * p' + K / 2 + (K' + 1) + 21)) ^ 4 ≤
        18000 * (5250 ^ 4 * P ^ 4) :=
      Nat.mul_le_mul_left 18000 (hpow.trans_eq hpow_eq)
    have h2 : 18000 * (5250 ^ 4 * P ^ 4) + 8 * P ^ 4 = (18000 * 5250 ^ 4 + 8) * P ^ 4 := by ring
    exact (Nat.add_le_add h1 h8p'_le).trans_eq h2
  have hP5_le_6 : P ^ 5 ≤ P ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  calc (2 ^ (K / 2) * (4 * p' + 1) + 4 * 2 ^ K') *
        (18000 * (1050 * (pWork p K + 2 * p' + K / 2 + (K' + 1) + 21)) ^ 4 + 2 * (4 * p'))
      ≤ (2 ^ K' * (5 * P)) * ((18000 * 5250 ^ 4 + 8) * P ^ 4) :=
        Nat.mul_le_mul hentries_le hcost_per_entry
    _ = 2 ^ K' * ((5 * (18000 * 5250 ^ 4 + 8)) * P ^ 5) := by ring
    _ ≤ 2 ^ K' * (2 ^ 67 * P ^ 6) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by decide) hP5_le_6)

/-- **Inductive Sublinear Series-Table Precomputation Bound for `buildQuantizedSpecPaperStop`
(`buildQuantizedSpecPaperStop_precomputeSeriesTableCost_le`, `[MS]` §3.3 (Lemma 3.2, eq. (8)) & §7.2)**:
For any `L, p, K : ℕ` with `1 ≤ p` and `K ≤ 2 ^ (L + 1)`, with `P := leafPrecision L p K`,
the total series-table precomputation cost across all levels of `buildQuantizedSpecPaperStop L p K`
satisfies:
`(buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost ≤
  (L + 1) * 2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6)`. -/
theorem buildQuantizedSpecPaperStop_precomputeSeriesTableCost_le
    (L p K : ℕ) (hp : 1 ≤ p) (hK_high : K ≤ 2 ^ (L + 1)) :
    let P := leafPrecision L p K
    (buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost ≤
      (L + 1) * 2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6) := by
  induction L generalizing p K with
  | zero =>
    dsimp only [buildQuantizedSpecPaperStop, QuantizedFastDFTSpec.precomputeSeriesTableCost,
      leafPrecision]
    rw [Nat.zero_add, Nat.one_mul]
    have hK_le2 : K ≤ 2 := by simpa using hK_high
    have h2K : 2 ^ K ≤ 4 * p * p := by
      have h1 : 2 ^ K ≤ 2 ^ 2 := Nat.pow_le_pow_right zero_lt_two hK_le2
      have h2 : 4 ≤ 4 * p * p := by nlinarith
      exact h1.trans h2
    exact precomputeLeafSeriesTableBitCost_le_of_stop p K p hp le_rfl h2K (by omega)
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop, leafPrecision]
    set p' := pChild p K
    set K' := K - K / 2
    set P := leafPrecision L p' K'
    have hp'_le : p' ≤ P := le_leafPrecision L p' K'
    have hp_le : p ≤ P := by
      have hp_p' : p ≤ p' := by dsimp [p']; rw [pChild_eq_additive]; omega
      exact hp_p'.trans hp'_le
    have hP_pos : 1 ≤ P := hp.trans hp_le
    split_ifs with hstop
    · dsimp only [QuantizedFastDFTSpec.precomputeSeriesTableCost]
      have h2K_P : 2 ^ K ≤ 4 * P * P :=
        hstop.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp_le) hp_le)
      have hK_bound : K + 1 ≤ 4 * (Nat.log2 P + 1) :=
        log_len_add_one_le_of_two_pow_le_four_mul_sq K P h2K_P
      have hlog_P : Nat.log2 P ≤ P :=
        (nat_log2_mono (Nat.le_succ P)).trans (log2_add_one_le_self P)
      have hbase := precomputeLeafSeriesTableBitCost_le_of_stop p K P hP_pos hp_le h2K_P (by omega)
      calc precomputeLeafSeriesTableBitCost p (2 ^ K)
          ≤ 1 * (2 ^ K' * (2 ^ 67 * P ^ 6)) := by rw [Nat.one_mul]; exact hbase
        _ ≤ (L + 1 + 1) * (2 ^ K' * (2 ^ 67 * P ^ 6)) := Nat.mul_le_mul_right _ (by omega)
        _ = (L + 1 + 1) * 2 ^ K' * (2 ^ 67 * P ^ 6) := by ring
    · dsimp only [quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.precomputeSeriesTableCost]
      have hstep := precomputeStepSeriesTableBitCost_le_of_step p K P hp'_le
      have hp'_pos : 1 ≤ p' := by dsimp [p']; rw [pChild_eq_additive]; omega
      have hK'_high : K' ≤ 2 ^ (L + 1) := by
        have hpow : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by rw [pow_succ']
        dsimp [K']
        omega
      have hchild := ih p' K' hp'_pos hK'_high
      have hK'_mono : 2 ^ (K' - K' / 2) ≤ 2 ^ K' :=
        Nat.pow_le_pow_right zero_lt_two (by omega)
      have hchild2 :
          (buildQuantizedSpecPaperStop L p' K').precomputeSeriesTableCost ≤
            (L + 1) * 2 ^ K' * (2 ^ 67 * P ^ 6) := by
        calc (buildQuantizedSpecPaperStop L p' K').precomputeSeriesTableCost
            ≤ (L + 1) * 2 ^ (K' - K' / 2) * (2 ^ 67 * P ^ 6) := hchild
          _ ≤ (L + 1) * 2 ^ K' * (2 ^ 67 * P ^ 6) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (L + 1) hK'_mono)
      calc precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ K') +
            (buildQuantizedSpecPaperStop L p' K').precomputeSeriesTableCost
          ≤ 2 ^ K' * (2 ^ 67 * P ^ 6) + (L + 1) * 2 ^ K' * (2 ^ 67 * P ^ 6) :=
            Nat.add_le_add hstep hchild2
        _ = (L + 1 + 1) * 2 ^ K' * (2 ^ 67 * P ^ 6) := by ring

/-- When `1 ≤ p`, `K ≤ 2 ^ (L + 1)`, and `P := leafPrecision L p K` satisfies
`2 ^ 52 * P ^ 5 ≤ 2 ^ (K / 2)`, the series-table precomputation cost satisfies:
`(buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost ≤ 32768 * 2 ^ K * P * P`. -/
theorem buildQuantizedSpecPaperStop_precomputeSeriesTableCost_le_quad
    (L p K : ℕ) (hp : 1 ≤ p) (hK_high : K ≤ 2 ^ (L + 1))
    (hsqrt : 2 ^ 52 * (leafPrecision L p K) ^ 5 ≤ 2 ^ (K / 2)) :
    let P := leafPrecision L p K
    (buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost ≤
      32768 * 2 ^ K * P * P := by
  intro P
  have h1 := buildQuantizedSpecPaperStop_precomputeSeriesTableCost_le L p K hp hK_high
  dsimp only at h1
  have hP_eq : P = p + 2 * sumLogLen L K + 12 * L := leafPrecision_eq L p K
  have hL1_le_P : L + 1 ≤ P := by omega
  have hP6 : P ^ 6 = P ^ 5 * P := pow_succ P 5
  have hpow67 : 2 ^ 67 = 32768 * 2 ^ 52 := by decide
  have hpow_split : 2 ^ (K / 2) * 2 ^ (K - K / 2) = 2 ^ K := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
  calc (buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost
      ≤ (L + 1) * 2 ^ (K - K / 2) * (2 ^ 67 * P ^ 6) := h1
    _ = 2 ^ (K - K / 2) * ((L + 1) * (32768 * 2 ^ 52 * (P ^ 5 * P))) := by
        rw [hpow67, hP6]; ring
    _ ≤ 2 ^ (K - K / 2) * (P * (32768 * 2 ^ 52 * (P ^ 5 * P))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hL1_le_P)
    _ = 32768 * (2 ^ 52 * P ^ 5) * 2 ^ (K - K / 2) * P * P := by ring
    _ ≤ 32768 * 2 ^ (K / 2) * 2 ^ (K - K / 2) * P * P :=
        Nat.mul_le_mul_right P
          (Nat.mul_le_mul_right P
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32768 hsqrt)))
    _ = 32768 * (2 ^ (K / 2) * 2 ^ (K - K / 2)) * P * P := by ring
    _ = 32768 * 2 ^ K * P * P := by rw [hpow_split]

/-- **Discharge of `2^52 * P^5 ≤ 2^(K0 / 2)` for `256 ≤ Nat.log2 n`
(`quantizedMultiplyOfBitLength_leafPrecision_pow5_le_two_pow_half_K0`, `[MS]` §7.2)**:
For every bit-length `n` with `256 ≤ Nat.log2 n`, the schedule parameters satisfy
`2 ^ 52 * P ^ 5 ≤ 2 ^ (K0 / 2)`. -/
theorem quantizedMultiplyOfBitLength_leafPrecision_pow5_le_two_pow_half_K0
    (n : ℕ) (hb256 : 256 ≤ Nat.log2 n) :
    let b := max 1 (Nat.log2 n)
    let k := n / b + 1
    let K0 := max 4 (Nat.log2 (2 * k) + 2)
    let L := Nat.log2 (K0 - 1)
    let p0 := rootPrecision b K0
    let P := leafPrecision L p0 K0
    2 ^ 52 * P ^ 5 ≤ 2 ^ (K0 / 2) := by
  dsimp only
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set P := leafPrecision L p0 K0
  have hb_eq : b = Nat.log2 n := Nat.max_eq_right (by omega)
  have hb_ge : 256 ≤ b := by omega
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    simp at hb256
  have h2b_le_n : 2 ^ b ≤ n := by
    rw [hb_eq]
    exact two_pow_log2_le n (by omega)
  have hn_lt_bk : n < b * k := by
    dsimp [k]
    have hdiv := Nat.div_add_mod n b
    have hmod : n % b < b := Nat.mod_lt n (by omega)
    have hmul : b * (n / b + 1) = b * (n / b) + b := by ring
    omega
  have h2b_lt_bk : 2 ^ b < b * k := lt_of_le_of_lt h2b_le_n hn_lt_bk
  have h2k_lt : 2 * k < 2 ^ (Nat.log2 (2 * k) + 1) := lt_two_pow_log2_succ (2 * k)
  have hK0_ge : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
  have h4k_lt_2K0 : 4 * k < 2 ^ K0 := by
    have h1 : 4 * k < 2 * 2 ^ (Nat.log2 (2 * k) + 1) := by omega
    have h2 : 2 * 2 ^ (Nat.log2 (2 * k) + 1) = 2 ^ (Nat.log2 (2 * k) + 2) := by ring
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right zero_lt_two hK0_ge)
  have hq_pow : (b / 64 - 2) + 1 ≤ 2 ^ (b / 64 - 2) := add_one_le_two_pow (b / 64 - 2)
  have hb64_pow : b / 64 + 1 ≤ 2 ^ (b / 64 - 1) := by
    have h1 : b / 64 + 1 ≤ 2 * ((b / 64 - 2) + 1) := by omega
    have h2 : 2 * ((b / 64 - 2) + 1) ≤ 2 * 2 ^ (b / 64 - 2) := Nat.mul_le_mul_left 2 hq_pow
    have h3 : 2 * 2 ^ (b / 64 - 2) = 2 ^ (b / 64 - 1) := by
      have : b / 64 - 1 = (b / 64 - 2) + 1 := by omega
      rw [this, pow_succ']
    omega
  have hb_lt_pow : b < 2 ^ (b / 64 + 5) := by
    have h1 : b < 64 * (b / 64 + 1) := by omega
    have h2 : 64 * (b / 64 + 1) ≤ 64 * 2 ^ (b / 64 - 1) := Nat.mul_le_mul_left 64 hb64_pow
    have h3 : 64 * 2 ^ (b / 64 - 1) = 2 ^ (b / 64 + 5) := by
      have : (64 : ℕ) = 2 ^ 6 := by decide
      rw [this, ← pow_add]
      congr 1
      omega
    omega
  have hpow_b2_lt : 2 ^ (b + 2) < 2 ^ (b / 64 + 5 + K0) := by
    calc 2 ^ (b + 2) = 4 * 2 ^ b := by ring
      _ < 4 * (b * k) := by omega
      _ = b * (4 * k) := by ring
      _ < 2 ^ (b / 64 + 5) * 2 ^ K0 := Nat.mul_lt_mul_of_lt_of_lt hb_lt_pow h4k_lt_2K0
      _ = 2 ^ (b / 64 + 5 + K0) := by rw [← pow_add]
  have hexp_K0 : b + 2 < b / 64 + 5 + K0 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_b2_lt
  have hK0_lower : b - b / 64 - 2 ≤ K0 := by omega
  have hK0_le_b3 : K0 ≤ b + 3 := by
    have hk_pos : 0 < k := Nat.succ_pos (n / b)
    have hk_le_n : k ≤ n := by
      dsimp [k]
      have hdiv_le : n / b ≤ n / 4 := Nat.div_le_div_left (by omega) (by decide)
      have hb_le_n : b ≤ n := by
        have := add_one_le_two_pow b
        omega
      omega
    have hn_lt : n < 2 ^ (b + 1) := by
      rw [hb_eq]
      exact lt_two_pow_log2_succ n
    have h2k_lt_b2 : 2 * k < 2 ^ (b + 2) := by
      have hpow_b2 : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by ring
      omega
    have hlog_lt : Nat.log2 (2 * k) < b + 2 := (Nat.log2_lt (by omega)).mpr h2k_lt_b2
    dsimp [K0]
    omega
  have hL_le_K0 : L ≤ K0 := by
    have h2L_le_K0 : 2 ^ L ≤ K0 :=
      (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
    have := add_one_le_two_pow L
    omega
  have hp0_eq : p0 = 2 * b + 2 * K0 + 6 := rfl
  have hP_le_23b : P ≤ 23 * b := by
    have h1 : P ≤ p0 + 4 * K0 + 14 * L := leafPrecision_le L p0 K0
    omega
  have h23b_le_pow : 23 * b ≤ 2 ^ (b / 64 + 10) := by
    have h1 : 23 * b ≤ 32 * 2 ^ (b / 64 + 5) := by omega
    have h2 : 32 * 2 ^ (b / 64 + 5) = 2 ^ (b / 64 + 10) := by
      have : (32 : ℕ) = 2 ^ 5 := by decide
      rw [this, ← pow_add]
      congr 1
      omega
    omega
  have hP_le_pow : P ≤ 2 ^ (b / 64 + 10) := hP_le_23b.trans h23b_le_pow
  have hP5_le : P ^ 5 ≤ 2 ^ ((b / 64 + 10) * 5) := by
    calc P ^ 5 ≤ (2 ^ (b / 64 + 10)) ^ 5 := Nat.pow_le_pow_left hP_le_pow 5
      _ = 2 ^ ((b / 64 + 10) * 5) := by rw [← pow_mul]
  have h52_P5 : 2 ^ 52 * P ^ 5 ≤ 2 ^ (52 + (b / 64 + 10) * 5) := by
    calc 2 ^ 52 * P ^ 5
        ≤ 2 ^ 52 * 2 ^ ((b / 64 + 10) * 5) := Nat.mul_le_mul_left (2 ^ 52) hP5_le
      _ = 2 ^ (52 + (b / 64 + 10) * 5) := by rw [← pow_add]
  have hexp_le : 52 + (b / 64 + 10) * 5 ≤ K0 / 2 := by omega
  exact h52_P5.trans (Nat.pow_le_pow_right zero_lt_two hexp_le)

/-! ### 6. Schedule Formula Cost with `precomputeSeriesTableCost` (`quantizedMultiplyOfBitLengthPaperStopSeries`) -/

/-- Pairs `quantizedFastDFTMultiplyRadix2Leaf` with its `[MS]` Theorem 1 `intrinsicCostRadix2Leaf` +
series-table precomputation cost `spec.precomputeSeriesTableCost` + root pipeline cost. -/
noncomputable def quantizedFastDFTMultiplyPaperSeriesCost
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ × ℝ :=
  (quantizedFastDFTMultiplyRadix2Leaf spec b K0 k1 k2 A B,
    2 * spec.intrinsicCostRadix2Leaf + (spec.precomputeSeriesTableCost : ℝ) +
      ((rootPipelineBitCost (2 ^ K0) (rootPrecision b K0) : ℕ) : ℝ))

/-- Parameter-free multiplier cost formula under the paper's stopping rule `buildQuantizedSpecPaperStop`
with `spec.precomputeSeriesTableCost` in place of `spec.precomputeRawTapCost`
(`quantizedMultiplyOfBitLengthPaperStopSeries`, `[MS]` §7). -/
noncomputable def quantizedMultiplyOfBitLengthPaperStopSeries (n A B : ℕ) : ℕ × ℝ :=
  let b := max 1 (Nat.log2 n)
  let k := n / b + 1
  let K0 := max 4 (Nat.log2 (2 * k) + 2)
  let L := Nat.log2 (K0 - 1)
  let p0 := rootPrecision b K0
  let spec := buildQuantizedSpecPaperStop L p0 K0
  quantizedFastDFTMultiplyPaperSeriesCost spec b K0 k k A B

@[simp]
theorem quantizedMultiplyOfBitLengthPaperStopSeries_fst_eq (n A B : ℕ) :
    (quantizedMultiplyOfBitLengthPaperStopSeries n A B).1 =
      (quantizedMultiplyOfBitLengthPaperStop n A B).1 := rfl

theorem quantizedMultiplyOfBitLengthPaperStopSeries_fst_eq_mul
    (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    (quantizedMultiplyOfBitLengthPaperStopSeries n A B).1 = A * B :=
  quantizedMultiplyOfBitLengthPaperStop_fst_eq_mul n A B hA hB

/-- **Explicit $O(n \log n)$ Upper Bound for `quantizedMultiplyOfBitLengthPaperStopSeries`
(`quantizedMultiplyOfBitLengthPaperStopSeries_snd_le_n_log_n_of_log2_ge_256`, `[MS]` §7)**:
For all `n, A, B : ℕ` with `256 ≤ Nat.log2 n`,
`(quantizedMultiplyOfBitLengthPaperStopSeries n A B).2 ≤
  (7879984640 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))`. -/
theorem quantizedMultiplyOfBitLengthPaperStopSeries_snd_le_n_log_n_of_log2_ge_256
    (n A B : ℕ) (hb256 : 256 ≤ Nat.log2 n) :
    (quantizedMultiplyOfBitLengthPaperStopSeries n A B).2 ≤
      (7879984640 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
  dsimp only [quantizedMultiplyOfBitLengthPaperStopSeries, quantizedFastDFTMultiplyPaperSeriesCost]
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set spec := buildQuantizedSpecPaperStop L p0 K0
  set P := leafPrecision L p0 K0
  have hn : 16 ≤ n := by
    have hb4 : 4 ≤ Nat.log2 n := by omega
    have h1 : 2 ^ 4 ≤ 2 ^ (Nat.log2 n) := Nat.pow_le_pow_right zero_lt_two hb4
    have hn_pos : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      simp at hb256
    have h2 : 2 ^ (Nat.log2 n) ≤ n := two_pow_log2_le n hn_pos
    have h3 : 16 = 2 ^ 4 := by decide
    omega
  have hb_eq : b = Nat.log2 n := Nat.max_eq_right (by omega)
  have hb_ge4 : 4 ≤ b := by omega
  have h2b_le_n : 2 ^ b ≤ n := by rw [hb_eq]; exact two_pow_log2_le n (by omega)
  have hb_le_n : b ≤ n := by have := add_one_le_two_pow b; omega
  have hdiv_pos : 1 ≤ n / b := Nat.div_pos hb_le_n (by omega)
  have hk_ge2 : 2 ≤ k := by dsimp [k]; omega
  have hbk_le : b * k ≤ 2 * n := by
    have hk_le : k ≤ 2 * (n / b) := by dsimp [k]; omega
    have hmul_div : b * (n / b) ≤ n := Nat.mul_div_le n b
    calc b * k ≤ b * (2 * (n / b)) := Nat.mul_le_mul_left b hk_le
      _ = 2 * (b * (n / b)) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hmul_div
  have hk_le_n : k ≤ n := by
    dsimp [k]
    have hdiv_le : n / b ≤ n / 4 := Nat.div_le_div_left hb_ge4 (by decide)
    omega
  have hlog_2k_ge2 : 2 ≤ Nat.log2 (2 * k) := by
    refine (Nat.le_log2 (by omega)).mpr ?_
    calc 2 ^ 2 = 4 := by decide
      _ ≤ 2 * k := by omega
  have hK0_eq : K0 = Nat.log2 (2 * k) + 2 := Nat.max_eq_right (by omega)
  have hK0_ge4 : 4 ≤ K0 := by omega
  have h2K0_le : 2 ^ K0 ≤ 8 * k := by
    rw [hK0_eq, pow_add]
    have hpow_2k : 2 ^ (Nat.log2 (2 * k)) ≤ 2 * k := two_pow_log2_le (2 * k) (by omega)
    calc 2 ^ (Nat.log2 (2 * k)) * 2 ^ 2
        ≤ (2 * k) * 4 := Nat.mul_le_mul_right 4 hpow_2k
      _ = 8 * k := by ring
  have hK0_le_2b : K0 ≤ 2 * b := by
    have hn_lt : n < 2 ^ (b + 1) := by rw [hb_eq]; exact lt_two_pow_log2_succ n
    have h2k_lt : 2 * k < 2 ^ (b + 2) := by
      have hpow_b2 : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by ring
      omega
    have hlog_lt : Nat.log2 (2 * k) < b + 2 := (Nat.log2_lt (by omega)).mpr h2k_lt
    omega
  have h2L_le_K0 : 2 ^ L ≤ K0 :=
    (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
  have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
    have h : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
    omega
  have hL_le_K0 : L ≤ K0 := by have := add_one_le_two_pow L; omega
  have hp0_eq : p0 = 2 * b + 2 * K0 + 6 := rfl
  have hp0_pos : 1 ≤ p0 := by omega
  have hp0_le_P : p0 ≤ P := le_leafPrecision L p0 K0
  have hP_le : P ≤ 44 * b := by
    have h1 : P ≤ p0 + 4 * K0 + 14 * L := leafPrecision_le L p0 K0
    omega
  have hP_pow5 : 2 ^ 52 * P ^ 5 ≤ 2 ^ (K0 / 2) :=
    quantizedMultiplyOfBitLength_leafPrecision_pow5_le_two_pow_half_K0 n hb256
  have hcost_spec : spec.intrinsicCostRadix2Leaf ≤ ((39024 * 2 ^ K0 * P * P : ℕ) : ℝ) :=
    buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le_quad L p0 K0 hp0_pos h2L_le_K0 hK0_le_2L1
  have hpre_nat : spec.precomputeSeriesTableCost ≤ 49140 * 2 ^ K0 * P * P := by
    have h1 := buildQuantizedSpecPaperStop_precomputeSeriesTableCost_le_quad
      L p0 K0 hp0_pos hK0_le_2L1 hP_pow5
    calc spec.precomputeSeriesTableCost
        ≤ 32768 * 2 ^ K0 * P * P := h1
      _ ≤ 49140 * 2 ^ K0 * P * P :=
          Nat.mul_le_mul_right P (Nat.mul_le_mul_right P (Nat.mul_le_mul_right _ (by decide)))
  have hpre_spec : (spec.precomputeSeriesTableCost : ℝ) ≤ ((49140 * 2 ^ K0 * P * P : ℕ) : ℝ) := by
    exact_mod_cast hpre_nat
  have hroot_nat : rootPipelineBitCost (2 ^ K0) p0 ≤ 7 * 2 ^ K0 * P * P :=
    rootPipelineBitCost_le_quad (2 ^ K0) p0 P hp0_pos hp0_le_P
  have hroot_real : ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) ≤ ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) := by
    exact_mod_cast hroot_nat
  have hquad_nat : 127195 * 2 ^ K0 * P * P ≤ 3939992320 * n * b := by
    have h1 : 127195 * 2 ^ K0 * P * P ≤ 127195 * (8 * k) * (44 * b) * (44 * b) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left 127195 h2K0_le) hP_le)
        hP_le
    calc 127195 * 2 ^ K0 * P * P
        ≤ 127195 * (8 * k) * (44 * b) * (44 * b) := h1
      _ = 1969996160 * (b * k) * b := by ring
      _ ≤ 1969996160 * (2 * n) * b :=
          Nat.mul_le_mul_right b (Nat.mul_le_mul_left 1969996160 hbk_le)
      _ = 3939992320 * n * b := by ring
  have hquad_real :
       2 * (((39024 * 2 ^ K0 * P * P : ℕ) : ℝ)) +
        ((49140 * 2 ^ K0 * P * P : ℕ) : ℝ) +
        ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) ≤
        ((3939992320 * n * b : ℕ) : ℝ) := by
    have hcomb :
        2 * (39024 * 2 ^ K0 * P * P) + 49140 * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P =
          127195 * 2 ^ K0 * P * P := by ring
    have hle :
        2 * (39024 * 2 ^ K0 * P * P) + 49140 * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P ≤
          3939992320 * n * b := by
      rw [hcomb]
      exact hquad_nat
    exact_mod_cast hle
  have htotal_le :
      2 * spec.intrinsicCostRadix2Leaf + (spec.precomputeSeriesTableCost : ℝ) +
        ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) ≤
        (3939992320 : ℝ) * (n : ℝ) * (b : ℝ) := by
    have hcast : ((3939992320 * n * b : ℕ) : ℝ) = (3939992320 : ℝ) * (n : ℝ) * (b : ℝ) := by
      push_cast
      ring
    linarith
  have hb_real : (b : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    rw [hb_eq]
    exact nat_log2_real_le_two_mul_log n (by omega)
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_nonneg : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  nlinarith

theorem size_mul_log2_add_one_mul_addBitCost_le_intrinsicCostRadix2Leaf
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) :
    ((spec.size * (Nat.log2 spec.size + 1) * addBitCost spec.p : ℕ) : ℝ) ≤
      spec.intrinsicCostRadix2Leaf := by
  induction hvalid with
  | @base p R =>
    dsimp [QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p,
      QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
    have hnat :
        R * (Nat.log2 R + 1) * addBitCost p ≤
          R * (Nat.log2 R + 1) * (mulBitCost p + addBitCost p) := by
      refine Nat.mul_le_mul_left _ ?_
      omega
    exact_mod_cast hnat
  | @step p K t1 r c1 v1Of child _hp _hK _ht1 _ht1_le _hr _hr_le hsize _hc1 _heven
      hchild_size hchild_p _hchild _hv1 _hv1_lt ih =>
    dsimp only [QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p,
      QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
    set p' := pChild p K
    obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by linarith)
    have hlog_prod : Nat.log2 (t1 * r) = Nat.log2 t1 + Nat.log2 r := by
      have hpow : t1 * r = 2 ^ (Nat.log2 t1 + Nat.log2 r) := by
        rw [pow_add, ht1_pow, hr_pow]
      rw [hpow, nat_log2_two_pow]
    have hp_le_p' : p ≤ p' := by
      dsimp [p', pChild, pWork]
      omega
    have hadd_le1 : addBitCost p ≤ 2 * addBitCost (4 * p') := by
      dsimp [addBitCost]
      omega
    have hadd_le2 : addBitCost p ≤ addBitCost p' := by
      dsimp [addBitCost]
      exact hp_le_p'
    have hsyn_eq :
        syntheticFFTStepBitCost t1 r p' =
          (Nat.log2 t1 * t1 * r) * (2 * addBitCost (4 * p')) := by
      dsimp only [syntheticFFTStepBitCost]
      rw [(syntheticFFTRadix2Ops_closed_form r (Nat.log2 t1)).2.1, ht1_pow]
      ring
    have hnat :
        (t1 * r) * (Nat.log2 (t1 * r) + 1) * addBitCost p ≤
          syntheticFFTStepBitCost t1 r p' +
            t1 * (r * (Nat.log2 r + 1) * addBitCost p') := by
      rw [hlog_prod, hsyn_eq]
      have hsplit :
          (t1 * r) * (Nat.log2 t1 + Nat.log2 r + 1) * addBitCost p =
            (Nat.log2 t1 * t1 * r) * addBitCost p +
              (t1 * (r * (Nat.log2 r + 1))) * addBitCost p := by
        ring
      rw [hsplit]
      refine Nat.add_le_add (Nat.mul_le_mul_left _ hadd_le1) ?_
      calc (t1 * (r * (Nat.log2 r + 1))) * addBitCost p
          ≤ (t1 * (r * (Nat.log2 r + 1))) * addBitCost p' := Nat.mul_le_mul_left _ hadd_le2
        _ = t1 * (r * (Nat.log2 r + 1) * addBitCost p') := by ring
    have hreal :
        (((t1 * r) * (Nat.log2 (t1 * r) + 1) * addBitCost p : ℕ) : ℝ) ≤
          ((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ) +
            (t1 : ℝ) * ((r * (Nat.log2 r + 1) * addBitCost p' : ℕ) : ℝ) := by
      have hcast :
          (((syntheticFFTStepBitCost t1 r p' +
            t1 * (r * (Nat.log2 r + 1) * addBitCost p') : ℕ) : ℝ)) =
          ((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ) +
            (t1 : ℝ) * ((r * (Nat.log2 r + 1) * addBitCost p' : ℕ) : ℝ) := by
        push_cast
        ring
      rw [← hcast]
      exact_mod_cast hnat
    rw [hchild_size, hchild_p] at ih
    have ht1_ih :
        (t1 : ℝ) * ((r * (Nat.log2 r + 1) * addBitCost p' : ℕ) : ℝ) ≤
          (t1 : ℝ) * child.intrinsicCostRadix2Leaf :=
      mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg t1)
    have hnonneg1 : (0 : ℝ) ≤ ((kroneckerSpreadStepBitCost t1 r p' : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnonneg2 : (0 : ℝ) ≤ ((twistAndSolverStepBitCost t1 r p' : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnonneg3 : (0 : ℝ) ≤ ((routingAndStreamingStepBitCost t1 r p' : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- **Program-Derived Upper-Bound Inequality for `computablePaperFastDFTMultiplyWithProgramCost`
Plus `buildComputablePaperTablesWithProgramCost`
(`computablePaperFastDFTMultiplyWithTables_snd_le`, `[MS]` §7.2)**:
For any valid executable specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`,
`hexec : spec.PaperExecutableValid`) with `spec.size = 2 ^ K0`, `spec.p = rootPrecision b K0`, and
`k1 + k2 ≤ 2 ^ K0`, the integer runtime cost `.2` of `computablePaperFastDFTMultiplyWithProgramCost`
plus the integer series-table construction cost `(buildComputablePaperTablesWithProgramCost spec).2`
is bounded by `8192 * (quantizedFastDFTMultiplyPaperSeriesCost spec b K0 k1 k2 A B).2`. -/
theorem computablePaperFastDFTMultiplyWithTables_snd_le
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) :
    let cSpecRes := buildComputablePaperTablesWithProgramCost spec
    let mulRes := computablePaperFastDFTMultiplyWithProgramCost cSpecRes.1 b K0 k1 k2 A B
    ((mulRes.2 + cSpecRes.2 : ℕ) : ℝ) ≤
      8192 * (quantizedFastDFTMultiplyPaperSeriesCost spec b K0 k1 k2 A B).2 := by
  dsimp only
  have hfaith : TablesFaithful (buildComputablePaperTablesWithProgramCost spec).1 spec :=
    buildComputablePaperTablesWithProgramCost_faithful spec hvalid hexec
  unfold computablePaperFastDFTMultiplyWithProgramCost quantizedFastDFTMultiplyPaperSeriesCost
  dsimp only
  rw [splitChunksTreeWithProgramCost_fst, splitChunksTreeWithProgramCost_fst]
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set cSpec := (buildComputablePaperTablesWithProgramCost spec).1
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
  set stSq := runSequentialScanCostedSteps (fun u =>
    let m := costedGMulScaled (p0 + 2) (4 * p0) (read1D fwd.1 u) (read1D fwd.1 u)
    (gConj m.1, m.2 + addBitCost (8 * p0))) R0
  set inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.1
  set numScale : ℤ := ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ)
  set denScale : ℤ := 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ)
  set stExt := runSequentialScanCostedSteps (fun j =>
    let imInt : ℤ := -(read1D inv.1 j).2
    let d := costedDivRoundRatInt (4 * p0) (imInt * numScale) denScale
    (d.1.toNat, d.2 + addBitCost (4 * p0))) R0
  set convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j => read1D stExt.1 j)
  have hp0_ge6 : 6 ≤ spec.p := by rw [hp0]; dsimp [p0, rootPrecision]; omega
  have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_le2 : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hx_AB_norm : ∀ k < spec.size, ‖x_AB k‖ ≤ (2 : ℝ) ^ spec.p := by
    intro k _
    have h1 := norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ spec.p := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ spec.p := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    linarith
  have hfwd_le : (fwd.2 : ℝ) ≤ 7000 * spec.intrinsicCostRadix2Leaf :=
    computablePaperFastDFTWithProgramCost_faithful_snd_le_7000 spec hvalid cSpec hfaith b stPack.outTape x_AB
      (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
      hx_AB_norm
  have hy : ∀ u < R0, toScaledComplex p0 (read1D fwd.1 u) = sincGaussianFastDFTOfTables cSpec x_AB u := by
    intro u hu
    rw [← hp0]
    exact toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith b stPack.outTape x_AB
      (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
      u (hsize.symm ▸ hu)
  have hsConj_eq : ∀ u < spec.size,
      star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2)) =
        toScaledComplex p0 (read1D stSq.1 u) := by
    intro u hu
    have hu_R0 : u < R0 := hsize ▸ hu
    dsimp only [stSq, runSequentialScanCostedSteps, costedGMulScaled]
    rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, toScaledComplex_gConj,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu_R0, sq]
  have hsConj_norm : ∀ u < spec.size,
      ‖star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2))‖ ≤ (2 : ℝ) ^ spec.p := by
    intro u hu
    rw [norm_star]
    have herr := sincGaussianFastDFTOfTables_error_le spec hvalid cSpec hfaith x_AB (Real.sqrt 2) hsqrt2_ge1
      (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u hu
    have hpow_neg_le1 : (2 : ℝ) ^ (-(spec.p : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hdft_le : ‖dft1D spec.size x_AB u‖ ≤ 2 := by
      have hpos : 0 < spec.size := by rw [hsize]; exact pow_pos zero_lt_two K0
      have h1 := dft1D_norm_le spec.size hpos x_AB (Real.sqrt 2)
        (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u
      linarith
    have hnorm_le4 : ‖sincGaussianFastDFTOfTables cSpec x_AB u‖ ≤ 4 := by
      have htri := norm_add_le (sincGaussianFastDFTOfTables cSpec x_AB u - dft1D spec.size x_AB u) (dft1D spec.size x_AB u)
      rw [sub_add_cancel] at htri
      nlinarith
    have hsq_le16 : ‖(sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2‖ ≤ 16 := by
      rw [norm_pow]
      nlinarith [norm_nonneg (sincGaussianFastDFTOfTables cSpec x_AB u)]
    have hq_err : complexQuantizeMaxErr p0 ≤ 1 := by
      have hlt := complexQuantizeMaxErr_lt p0
      have hpow_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      nlinarith
    have hS_le17 : ‖complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2)‖ ≤ 17 := by
      have h1 := norm_complexQuantize_le p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2)
      linarith
    have h17_le : (17 : ℝ) ≤ (2 : ℝ) ^ spec.p := by
      calc (17 : ℝ) ≤ (64 : ℝ) := by norm_num
        _ = (2 : ℝ) ^ 6 := by norm_num
        _ ≤ (2 : ℝ) ^ spec.p := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp0_ge6
    linarith
  have hinv_le : (inv.2 : ℝ) ≤ 7000 * spec.intrinsicCostRadix2Leaf :=
    computablePaperFastDFTWithProgramCost_faithful_snd_le_7000 spec hvalid cSpec hfaith p0 stSq.1
      (fun u => star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2)))
      hsConj_eq hsConj_norm
  have hsplitA_le :
      (splitChunksTreeWithProgramCost b k1 A).2 ≤
        2 * (R0 * (K0 + 1) * addBitCost p0) := by
    have h1 := splitChunksTreeWithProgramCost_snd_le b k1 A
    have hk1_le : k1 ≤ R0 := by dsimp [R0]; omega
    have hlog1 : Nat.log2 k1 ≤ K0 := by
      have hm := nat_log2_mono hk1_le
      dsimp [R0] at hm
      rwa [nat_log2_two_pow] at hm
    have hlog1_2 : Nat.log2 k1 + 2 ≤ 2 * (K0 + 1) := by omega
    have hb_le : addBitCost b ≤ addBitCost p0 := by dsimp [addBitCost, p0, rootPrecision]; omega
    calc (splitChunksTreeWithProgramCost b k1 A).2
        ≤ (Nat.log2 k1 + 2) * k1 * addBitCost b := h1
      _ ≤ (2 * (K0 + 1)) * R0 * addBitCost p0 :=
          Nat.mul_le_mul (Nat.mul_le_mul hlog1_2 hk1_le) hb_le
      _ = 2 * (R0 * (K0 + 1) * addBitCost p0) := by ring
  have hsplitB_le :
      (splitChunksTreeWithProgramCost b k2 B).2 ≤
        2 * (R0 * (K0 + 1) * addBitCost p0) := by
    have h1 := splitChunksTreeWithProgramCost_snd_le b k2 B
    have hk2_le : k2 ≤ R0 := by dsimp [R0]; omega
    have hlog2 : Nat.log2 k2 ≤ K0 := by
      have hm := nat_log2_mono hk2_le
      dsimp [R0] at hm
      rwa [nat_log2_two_pow] at hm
    have hlog2_2 : Nat.log2 k2 + 2 ≤ 2 * (K0 + 1) := by omega
    have hb_le : addBitCost b ≤ addBitCost p0 := by dsimp [addBitCost, p0, rootPrecision]; omega
    calc (splitChunksTreeWithProgramCost b k2 B).2
        ≤ (Nat.log2 k2 + 2) * k2 * addBitCost b := h1
      _ ≤ (2 * (K0 + 1)) * R0 * addBitCost p0 :=
          Nat.mul_le_mul (Nat.mul_le_mul hlog2_2 hk2_le) hb_le
      _ = 2 * (R0 * (K0 + 1) * addBitCost p0) := by ring
  have hrecon_le :
      (reconstructChunksTreeWithProgramCost b convNat).2 ≤
        6 * (R0 * (K0 + 1) * addBitCost p0) := by
    have h1 := reconstructChunksTreeWithProgramCost_snd_le b convNat
    have hlen : convNat.length = k1 + k2 := by simp [convNat]
    rw [hlen] at h1
    have hlog_k : Nat.log2 (k1 + k2) ≤ K0 := by
      have hm := nat_log2_mono hk
      rwa [nat_log2_two_pow] at hm
    have hlog_k2 : 3 * (Nat.log2 (k1 + k2) + 2) ≤ 6 * (K0 + 1) := by omega
    have hb_le : addBitCost b ≤ addBitCost p0 := by dsimp [addBitCost, p0, rootPrecision]; omega
    calc (reconstructChunksTreeWithProgramCost b convNat).2
        ≤ 3 * (Nat.log2 (k1 + k2) + 2) * (k1 + k2) * addBitCost b := h1
      _ ≤ (6 * (K0 + 1)) * R0 * addBitCost p0 :=
          Nat.mul_le_mul (Nat.mul_le_mul hlog_k2 hk) hb_le
      _ = 6 * (R0 * (K0 + 1) * addBitCost p0) := by ring
  have htree_nat :
      (splitChunksTreeWithProgramCost b k1 A).2 +
        (splitChunksTreeWithProgramCost b k2 B).2 +
        (reconstructChunksTreeWithProgramCost b convNat).2 ≤
      10 * (R0 * (K0 + 1) * addBitCost p0) := by omega
  have htree_real :
      (((splitChunksTreeWithProgramCost b k1 A).2 +
        (splitChunksTreeWithProgramCost b k2 B).2 +
        (reconstructChunksTreeWithProgramCost b convNat).2 : ℕ) : ℝ) ≤
      10 * spec.intrinsicCostRadix2Leaf := by
    have h1 :
        (((splitChunksTreeWithProgramCost b k1 A).2 +
          (splitChunksTreeWithProgramCost b k2 B).2 +
          (reconstructChunksTreeWithProgramCost b convNat).2 : ℕ) : ℝ) ≤
        ((10 * (R0 * (K0 + 1) * addBitCost p0) : ℕ) : ℝ) := by
      exact_mod_cast htree_nat
    have hcast :
        ((10 * (R0 * (K0 + 1) * addBitCost p0) : ℕ) : ℝ) =
          10 * ((R0 * (K0 + 1) * addBitCost p0 : ℕ) : ℝ) := by
      push_cast; ring
    have h2 := size_mul_log2_add_one_mul_addBitCost_le_intrinsicCostRadix2Leaf spec hvalid
    have hlog_R0 : Nat.log2 spec.size = K0 := by rw [hsize, nat_log2_two_pow]
    rw [hlog_R0, hsize, hp0] at h2
    linarith
  have hmul4_64 : mulBitCost (4 * p0) ≤ 64 * mulBitCost p0 := by
    have h := mulBitCost_mul_le 4 p0
    have hconst : mulBitCostScaleFactor 4 = 64 := by decide
    rw [hconst] at h
    exact h
  have hsq_cost_eq :
      stSq.2.2 = R0 * (4 * mulBitCost (4 * p0) + 4 * addBitCost (4 * p0) + addBitCost (8 * p0)) := by
    dsimp only [stSq]
    refine runSequentialScanCostedSteps_cost_const _ R0 _ (fun _ _ => ?_)
    dsimp only [costedGMulScaled]
    rw [computableMulBitCost_eq]
  have hext_cost_eq :
      stExt.2.2 = R0 * (2 * mulBitCost (4 * p0) + 2 * addBitCost (4 * p0) + addBitCost (4 * p0)) := by
    dsimp only [stExt]
    refine runSequentialScanCostedSteps_cost_const _ R0 _ (fun _ _ => ?_)
    dsimp only [costedDivRoundRatInt]
    rw [computableMulBitCost_eq]
  have hroot_nat :
      stPack.steps * (2 * addBitCost (4 * p0)) +
        stSq.2.2 + stExt.2.2 ≤
      8192 * rootPipelineBitCost R0 p0 := by
    rw [hsq_cost_eq, hext_cost_eq]
    dsimp only [stPack, rootPipelineBitCost]
    rw [runSequentialScanSteps_steps]
    have hsq_ext :
        R0 * (4 * mulBitCost (4 * p0) + 4 * addBitCost (4 * p0) + addBitCost (8 * p0)) +
          R0 * (2 * mulBitCost (4 * p0) + 2 * addBitCost (4 * p0) + addBitCost (4 * p0)) ≤
          R0 * (384 * mulBitCost p0 + 36 * addBitCost p0) := by
      have hstep :
          (4 * mulBitCost (4 * p0) + 4 * addBitCost (4 * p0) + addBitCost (8 * p0)) +
            (2 * mulBitCost (4 * p0) + 2 * addBitCost (4 * p0) + addBitCost (4 * p0)) ≤
          384 * mulBitCost p0 + 36 * addBitCost p0 := by
        dsimp [addBitCost]; omega
      calc R0 * (4 * mulBitCost (4 * p0) + 4 * addBitCost (4 * p0) + addBitCost (8 * p0)) +
            R0 * (2 * mulBitCost (4 * p0) + 2 * addBitCost (4 * p0) + addBitCost (4 * p0))
          = R0 * ((4 * mulBitCost (4 * p0) + 4 * addBitCost (4 * p0) + addBitCost (8 * p0)) +
              (2 * mulBitCost (4 * p0) + 2 * addBitCost (4 * p0) + addBitCost (4 * p0))) := by ring
        _ ≤ R0 * (384 * mulBitCost p0 + 36 * addBitCost p0) := Nat.mul_le_mul_left R0 hstep
    have hpack_eq : R0 * (2 * addBitCost (4 * p0)) = 8 * R0 * addBitCost p0 := by
      dsimp [addBitCost]; ring
    calc R0 * (2 * addBitCost (4 * p0)) +
          R0 * (4 * mulBitCost (4 * p0) + 4 * addBitCost (4 * p0) + addBitCost (8 * p0)) +
          R0 * (2 * mulBitCost (4 * p0) + 2 * addBitCost (4 * p0) + addBitCost (4 * p0))
        ≤ 8 * R0 * addBitCost p0 +
          R0 * (384 * mulBitCost p0 + 36 * addBitCost p0) := by omega
      _ = R0 * (384 * mulBitCost p0 + 44 * addBitCost p0) := by ring
      _ ≤ R0 * (8192 * mulBitCost p0 + 24576 * addBitCost p0) := by
          refine Nat.mul_le_mul_left R0 ?_
          omega
      _ = 8192 * (R0 * (mulBitCost p0 + 3 * addBitCost p0)) := by ring
  have hroot_real :
      ((stPack.steps * (2 * addBitCost (4 * p0)) +
        stSq.2.2 + stExt.2.2 : ℕ) : ℝ) ≤
      8192 * ((rootPipelineBitCost R0 p0 : ℕ) : ℝ) := by
    exact_mod_cast hroot_nat
  have htable_nat := buildComputablePaperTablesWithProgramCost_snd_le spec
  have htable_real : ((buildComputablePaperTablesWithProgramCost spec).2 : ℝ) ≤
      (spec.precomputeSeriesTableCost : ℝ) := by
    exact_mod_cast htable_nat
  have hpre_nonneg : (0 : ℝ) ≤ (spec.precomputeSeriesTableCost : ℝ) := Nat.cast_nonneg _
  have hint_nonneg : 0 ≤ spec.intrinsicCostRadix2Leaf :=
    QuantizedFastDFTSpec.intrinsicCostRadix2Leaf_nonneg spec
  push_cast at htree_real hroot_real ⊢
  linarith

end IntMul
