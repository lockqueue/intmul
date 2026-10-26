import IntMul.TMScheduleTree

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# Uniform 8-Stack `Turing.FinTM2` Block-Pass FFT, Gather/Transpose/Scatter, Leaf FFT, Step 2 & Step 1 Stages (`IntMul.TMSpreadFFT`)

This module constructs and proves linear/quasi-linear `ComputesInTime` / `StageEval` theorems for
the uniform 8-stack binary machine (`Turing.FinTM2`) stages executing:
1. **Part 1 (Streaming List & Block-Pass Combinators)**:
   - `bmReplicateList`: $O(N \cdot L)$ list replication `List.replicate N x`.
   - `bmDropList` & `bmTakeByDrop` & `bmSplitAtList`: $O(|xs| \cdot L)$ prefix/suffix list splitting
     `(xs.take M, xs.drop M)` without random indexing.
   - `bmSliceListBlocks`: $O(B \cdot M \cdot L)$ single-pass contiguous block partitioning
     `(List.range B).map (fun b => (xs.drop (b * M)).take M)`.
   - `StageEval.flattenList`, `bmInterleaveList`, `bmSplitBlocks`, `bmPairBlocks`, and
     `bmNaturalSplitBlocks`: $O(\sum |b|)$ radix-2 block-splitting and block-pairing passes.
2. **Part 2 (Multi-Pass Gather, Matrix Transpose, Frequency Scatter & Nyquist Mode Sum)**:
   - `bmNaturalSplitPasses`: $k$ passes of `bmNaturalSplitBlocks` transforming a flat list of
     length $2^k \cdot M$ into the $2^k \times M$ stride-$2^k$ matrix in $O((k + 1) \cdot 2^k \cdot M \cdot L)$ steps.
   - `bmOddStrideGather`: Step 1 input gather + precision rescaling to `qChildEll K p`.
   - `bmTransposeMatrix`: $O((k + 1) \cdot 2^K \cdot L)$ matrix transpose ($t_1 \times r \leftrightarrow r \times t_1$).
   - `bmFreqScatter`: Step 3 output frequency scatter + precision rescaling to `p + 2`.
   - `bmNyquistModeSum`: Nyquist alternating mode sum `nyquistModeSumFixed K p xFixed` extracted from
     row `t1Ell K / 2` via deinterleaved even-minus-odd summation.
3. **Part 3 (Leaf Cooley–Tukey Radix-2 Butterfly FFT Stages)**:
   - `bmRadix2FFT1DWith` and `bmBaseRadix2FFTWith`: top-down split and bottom-up butterfly combine
     stages at internal precision `qBaseEll K p` (Lemma 6.5(2) (`lem:forward`)).

All machines have $O(1)$ finite control and state cardinality (`IsUniformFinTM2`) independent of
$n, K, p, R, A, B$ (see Lemma 3.3 (`lem:routing`), equation (25) (`eq:nyquist-id`), and
Section 8 (`sec:lean`)).
-/

namespace IntMul

open Turing StageEval

/-! ## 1. Streaming List & Block-Pass Combinators (`bmReplicateList`, `bmDropList`, `bmTakeByDrop`, `bmSplitAtList`, `bmSliceListBlocks`, `bmInterleaveList`, `bmSplitBlocks`, `bmPairBlocks`, `bmNaturalSplitBlocks`) -/

/-- Pure step for `bmReplicateList`: prepends `x` to `acc`. -/
def replicateListStep {α : Type} (x : α) (acc : List α) : List α :=
  x :: acc

theorem loopFinalState_replicateListStep {α : Type} (x : α) :
    ∀ (cnt : List Bool) (acc : List α),
      loopFinalState (replicateListStep x) cnt acc =
        List.replicate cnt.length x ++ acc
  | [], acc => by simp [loopFinalState]
  | _ :: cnt, acc => by
    rw [loopFinalState_cons, replicateListStep, List.length_cons,
      loopFinalState_replicateListStep x cnt (x :: acc),
      List.replicate_succ', List.append_assoc, List.singleton_append]

theorem loopStepsAux_replicateListStep_le {α : Type} (x : α) (L : ℕ) :
    ∀ (cnt : List Bool) (acc : List α),
      loopStepsAux (replicateListStep x) (fun _ => 5 * L + 9) cnt acc ≤
        cnt.length * (5 * L + 10) + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: cnt, acc => by
    simp only [loopStepsAux_cons, List.length_cons]
    have ih := loopStepsAux_replicateListStep_le x L cnt (replicateListStep x acc)
    nlinarith

/-- **Uniform List Replication (`bmReplicateList`)**:
Consumes `encPair encUnary encElem (N, x)` on `kIO` and emits `encList encElem (List.replicate N x)`
on `kIO` in $O(N \cdot |x|)$ `TM2.step` transitions (`≤ 6 * N * ((encElem x).length + 3) + 10 * (encElem x).length + 35`). -/
def bmReplicateList : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kSched).seq
      ((tmPopFirstSubwordRev kIO kWork2).seq
        ((tmDropWord kIO).seq
          ((tmPushEmpty kIO).seq
            ((((tmDupWord kWork2 kWork1 kWork0).seq
                (tmPrependRevWord kWork0 kIO)).loopDelimWord kSched).seq
              (tmDropWord kWork2))))))

theorem bmReplicateList_computesInTime {α : Type} (encElem : α → List Bool)
    (N : ℕ) (x : α) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 6 * N * ((encElem x).length + 3) + 10 * (encElem x).length + 35,
      bmReplicateList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encElem (N, x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem (List.replicate N x)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary N) ++ encodeDelimWord (encElem x)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append, length_encUnary] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kSched (by decide)
    (encUnary N).reverse [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encElem x))) [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kSched, List.length_reverse,
    List.reverse_reverse, length_encUnary, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork2 (by decide)
    (encodeDelimWord (encElem x)) [] tW2
    (mkTapes8 [] [] [] [] tW3 tW4 tW5 (encodeDelimWord (encUnary N) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork2, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encElem x).reverse ++ tW2)
      tW3 tW4 tW5 (encodeDelimWord (encUnary N) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] (encodeDelimWord (encElem x).reverse ++ tW2) tW3 tW4 tW5
      (encodeDelimWord (encUnary N) ++ tSch))
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s5
  let stkOf : List α → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun acc =>
    mkTapes8 (encodeDelimWord (encList encElem acc)) [] []
      (encodeDelimWord (encElem x).reverse ++ tW2) tW3 tW4 tW5 []
  rcases BitMachine.ComputesInTime.loopDelimWord_state_le kSched
    (replicateListStep x) (fun _ => 5 * (encElem x).length + 9) stkOf
    (fun acc tailSch => by
      dsimp only [stkOf, replicateListStep]
      simp only [update_mkTapes8_kSched]
      have b1 := tmDupWord_computesInTime kWork2 kWork1 kWork0 (by decide) (by decide) (by decide)
        (encElem x).reverse tW2 [] []
        (mkTapes8 (encodeDelimWord (encList encElem acc)) [] [] [] tW3 tW4 tW5 tailSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
        List.length_reverse, List.append_nil] at b1
      have b2 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
        (encElem x).reverse (encList encElem acc) [] []
        (mkTapes8 [] [] [] (encodeDelimWord (encElem x).reverse ++ tW2) tW3 tW4 tW5 tailSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2
      simp only [encList_cons]
      refine ⟨_, ?_, b1.seq b2⟩
      omega)
    (encUnary N) tSch [] with ⟨tL, htL, s6⟩
  dsimp only [stkOf] at htL s6
  simp only [update_mkTapes8_kSched, encList_nil, loopFinalState_replicateListStep,
    List.append_nil, length_encUnary] at s6
  have hbL := loopStepsAux_replicateListStep_le x (encElem x).length (encUnary N) []
  simp only [length_encUnary] at hbL
  have s7 := tmDropWord_computesInTime kWork2 (encElem x).reverse tW2
    (mkTapes8 (encodeDelimWord (encList encElem (List.replicate N x))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, List.length_reverse] at s7
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))⟩
  nlinarith

/-- **Linear-Time List Drop (`bmDropList`)**:
Consumes `encPair encUnary (encList encElem) (M, xs)` on `kIO` and emits
`encList encElem (xs.drop M)` on `kIO` in `≤ M * (L + 5) + 2 * (encList encElem xs).length + 10` steps. -/
def bmDropList : BitMachine :=
  bmIterLoop (tmTailWords kIO)

theorem bmDropList_computesInTime {α : Type} (encElem : α → List Bool)
    (M : ℕ) (xs : List α) (L : ℕ) (hL : ∀ x ∈ xs, (encElem x).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ M * (L + 5) + 2 * (encList encElem xs).length + 10,
      bmDropList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encList encElem) (M, xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem (xs.drop M)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have hdrop : StageEval (S := S) (bmIterLoop (tmTailWords kIO))
      (encDepPair (fun _ => encUnary M) (fun _ => encList encElem (xs.drop 0)))
      (fun _ => encList encElem (xs.drop M))
      (fun _ => M * (L + 5) + 2 * (encList encElem xs).length + 10) := by
    refine StageEval.iterLoop_idx
      (u := fun _ i => encList encElem (xs.drop i))
      (B := fun _ => L + 2) ?_
    intro ⟨⟨_, i⟩, _⟩ u2 u3 u4 u5 uS
    dsimp only [id]
    have htail_drop : (xs.drop i).tail = xs.drop (i + 1) := by
      rw [← List.drop_drop, List.drop_one]
    rw [← htail_drop]
    exact tmTailWords_encList_computesInTime encElem (xs.drop i) L
      (fun y hy => hL y (List.mem_of_mem_drop hy)) u2 u3 u4 u5 uS
  rcases hdrop () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  simpa [List.drop_zero] using ⟨t, ht, hcomp⟩

/-- **Linear-Time List Take via Reverse-Drop (`bmTakeByDrop`)**:
Consumes `encPair encUnary (encList encElem) (D, xs)` on `kIO` (where `D = xs.length - M` and
`M ≤ xs.length`) and emits `encList encElem (xs.take M)` on `kIO` in $O(|xs| \cdot L)$ steps. -/
def bmTakeByDrop : BitMachine :=
  bmSeq (bmMapSnd bmRevList) (bmSeq bmDropList bmRevList)

theorem bmTakeByDrop_computesInTime {α : Type} (encElem : α → List Bool)
    (M : ℕ) (xs : List α) (hM : M ≤ xs.length) (L : ℕ)
    (hL : ∀ x ∈ xs, (encElem x).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (xs.length - M) * (L + 5) + 50 * (encList encElem xs).length +
          20 * (xs.length - M) + 100,
      bmTakeByDrop.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encList encElem) (xs.length - M, xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem (xs.take M)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.mapSnd (u1 := fun _ : S => encUnary (xs.length - M))
    (StageEval.revList (fun _ => encElem) (fun _ => xs))
  have p2 := StageEval.const (S := S)
    (bmDropList_computesInTime encElem (xs.length - M) xs.reverse L
      (fun x hx => hL x (List.mem_reverse.mp hx)))
  have p3 := StageEval.revList (fun _ : S => encElem)
    (fun _ => xs.reverse.drop (xs.length - M))
  have htake : (xs.reverse.drop (xs.length - M)).reverse = xs.take M := by
    rw [List.drop_reverse, Nat.sub_sub_self hM, List.reverse_reverse]
  rcases (StageEval.seq p1 (StageEval.seq p2 p3)) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair, id] at ht hcomp
  rw [htake] at hcomp
  have hlen_rev : (encList encElem xs.reverse).length = (encList encElem xs).length :=
    length_encList_reverse encElem xs
  have hlen_drop : (encList encElem (xs.reverse.drop (xs.length - M))).length ≤
      (encList encElem xs).length := by
    rw [← hlen_rev]
    exact length_encList_drop_le encElem (xs.length - M) xs.reverse
  simp only [length_encUnary, hlen_rev] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Pure step for `bmSplitAtList` inner loop: pops head of `st.1` and prepends to `st.2`. -/
def splitAtInnerStep {α : Type} (defVal : α) (st : List α × List α) : List α × List α :=
  (st.1.tail, st.1.headD defVal :: st.2)

theorem loopFinalState_splitAtInnerStep {α : Type} (defVal : α) :
    ∀ (cnt : List Bool) (rem acc : List α),
      cnt.length ≤ rem.length →
      loopFinalState (splitAtInnerStep defVal) cnt (rem, acc) =
        (rem.drop cnt.length, (rem.take cnt.length).reverse ++ acc)
  | [], rem, acc, _ => by simp [loopFinalState]
  | _ :: cnt, [], _, hlen => by simp at hlen
  | _ :: cnt, x :: rem, acc, hlen => by
    have hlen' : cnt.length ≤ rem.length := Nat.le_of_succ_le_succ hlen
    simp only [loopFinalState_cons, splitAtInnerStep, List.tail_cons, List.headD_cons,
      List.length_cons, List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append]
    exact loopFinalState_splitAtInnerStep defVal cnt rem (x :: acc) hlen'

theorem loopStepsAux_splitAtInnerStep_le {α : Type} (defVal : α) (L : ℕ) :
    ∀ (cnt : List Bool) (st : List α × List α),
      loopStepsAux (splitAtInnerStep defVal) (fun _ => 2 * L + 6) cnt st ≤
        cnt.length * (2 * L + 7) + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: cnt, st => by
    simp only [loopStepsAux_cons, List.length_cons]
    have ih := loopStepsAux_splitAtInnerStep_le defVal L cnt (splitAtInnerStep defVal st)
    nlinarith

/-- **Linear-Time Prefix/Suffix List Split (`bmSplitAtList`)**:
Consumes `encPair encUnary (encList encElem) (M, xs)` on `kIO` (with `M ≤ xs.length`) and emits
`encPair (encList encElem) (encList encElem) (xs.take M, xs.drop M)` on `kIO` in **strictly linear**
$O(M \cdot L + |xs|)$ `TM2.step` transitions (`≤ M * (2 * L + 8) + 22 * (encList encElem xs).length + 4 * M + 50`). -/
def bmSplitAtList : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork1).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kWork2).seq
            ((tmPushEmpty kWork3).seq
              ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                  (tmPrependRevWord kWork0 kWork3)).loopDelimWord kWork1).seq
                ((tmMoveWord kWork3 kWork0 kIO).seq
                  (bmRevList.seq
                    ((tmRevMoveWord kIO kWork0).seq
                      ((tmMoveWord kWork2 kWork1 kIO).seq
                        tmPackPairFromRev))))))))))

theorem length_encList_take_add_drop {α : Type} (encElem : α → List Bool) :
    ∀ (M : ℕ) (xs : List α),
      (encList encElem (xs.take M)).length + (encList encElem (xs.drop M)).length =
        (encList encElem xs).length
  | 0, xs => by simp
  | _ + 1, [] => by simp
  | M + 1, x :: xs => by
    have ih := length_encList_take_add_drop encElem M xs
    simp only [List.take_succ_cons, List.drop_succ_cons, encList_cons, List.length_append]
    omega

theorem bmSplitAtList_computesInTime {α : Type} [Inhabited α] (encElem : α → List Bool)
    (M : ℕ) (xs : List α) (hM : M ≤ xs.length) (L : ℕ)
    (hL : ∀ x ∈ xs, (encElem x).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ M * (2 * L + 8) + 22 * (encList encElem xs).length + 4 * M + 50,
      bmSplitAtList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encList encElem) (M, xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encList encElem) (encList encElem) (xs.take M, xs.drop M)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary M) ++ encodeDelimWord (encList encElem xs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append, length_encUnary] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
    (encUnary M).reverse [] []
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encElem xs))) [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.length_reverse,
    List.reverse_reverse, length_encUnary, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encElem xs)) [] []
    (mkTapes8 [] [] (encodeDelimWord (encUnary M)) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encElem xs).reverse)
      (encodeDelimWord (encUnary M)) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encElem xs).reverse [] tW2
    (mkTapes8 [] [] (encodeDelimWord (encUnary M)) [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 [] [] (encodeDelimWord (encUnary M))
      (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s6
  -- Instead of loopDelimWord_state_le without length invariant, prove the inner loop by induction on M:
  have hloop : ∀ (k : ℕ) (rem acc : List α),
      k ≤ rem.length → (∀ x ∈ rem, (encElem x).length ≤ L) →
      ∃ tL ≤ k * (2 * L + 7) + 1,
        (((tmPopFirstSubwordRev kWork2 kWork0).seq
            (tmPrependRevWord kWork0 kWork3)).loopDelimWord kWork1).ComputesInTime
          (mkTapes8 [] [] (encodeDelimWord (encUnary k))
            (encodeDelimWord (encList encElem rem) ++ tW2)
            (encodeDelimWord (encList encElem acc) ++ tW3) tW4 tW5 tSch)
          (mkTapes8 [] [] []
            (encodeDelimWord (encList encElem (rem.drop k)) ++ tW2)
            (encodeDelimWord (encList encElem ((rem.take k).reverse ++ acc)) ++ tW3) tW4 tW5 tSch) tL := by
    intro k
    induction k with
    | zero =>
      intro rem acc _ _
      simp only [Nat.zero_mul, Nat.zero_add, List.drop_zero, List.take_zero, List.reverse_nil,
        List.nil_append, encUnary, List.replicate_zero]
      refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
      simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, mkTapes8_kWork1,
        update_mkTapes8_kWork1, List.head?_cons, List.tail_cons, Option.getD_some, cond_true]
    | succ k ih =>
      intro rem acc hk hremL
      rcases rem with _ | ⟨x, rem'⟩
      · simp at hk
      · have hk' : k ≤ rem'.length := Nat.le_of_succ_le_succ hk
        have hxL : (encElem x).length ≤ L := hremL x List.mem_cons_self
        have hremL' : ∀ y ∈ rem', (encElem y).length ≤ L :=
          fun y hy => hremL y (List.mem_cons_of_mem x hy)
        let body := (tmPopFirstSubwordRev kWork2 kWork0).seq (tmPrependRevWord kWork0 kWork3)
        have hpop : (body.loopDelimWord kWork1).toFinTM2.step
            ⟨some none, default,
              mkTapes8 [] [] (encodeDelimWord (encUnary (k + 1)))
                (encodeDelimWord (encList encElem (x :: rem')) ++ tW2)
                (encodeDelimWord (encList encElem acc) ++ tW3) tW4 tW5 tSch⟩ =
            some ⟨some (some body.main), default,
              mkTapes8 [] [] (encodeDelimWord (encUnary k))
                (encodeDelimWord (encList encElem (x :: rem')) ++ tW2)
                (encodeDelimWord (encList encElem acc) ++ tW3) tW4 tW5 tSch⟩ := by
          simp only [encUnary, List.replicate_succ, BitMachine.loopDelimWord, BitMachine.toFinTM2,
            mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
            encodeDelimWord_cons, mkTapes8_kWork1,
            update_mkTapes8_kWork1, List.head?_cons, List.tail_cons, Option.getD_some, cond_false]
        have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
          (encodeDelimWord (encElem x) ++ encList encElem rem') tW2 []
          (mkTapes8 [] [] (encodeDelimWord (encUnary k)) []
            (encodeDelimWord (encList encElem acc) ++ tW3) tW4 tW5 tSch)
        simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
          unconsDelimWord_encodeDelimWord_append] at b1
        have b2 := tmPrependRevWord_computesInTime kWork0 kWork3 (by decide)
          (encElem x).reverse (encList encElem acc) [] tW3
          (mkTapes8 [] [] (encodeDelimWord (encUnary k))
            (encodeDelimWord (encList encElem rem') ++ tW2) [] tW4 tW5 tSch)
        simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
          List.reverse_reverse, List.append_nil] at b2
        have ⟨hb⟩ := b1.seq b2
        simp only [← encList_cons] at hb
        have hb_lifted := BitMachine.loopDelimWord_body_evalsToInTime_concrete kWork1 body hb
        rcases ih rem' (x :: acc) hk' hremL' with ⟨t2, ht2, ⟨hih⟩⟩
        simp only [List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append] at hih ⊢
        have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hb_lifted) hih
        refine ⟨_, ?_, ⟨hcomb⟩⟩
        nlinarith
  rcases hloop M xs [] hM hL with ⟨tL, htL, s7⟩
  simp only [encList_nil, List.append_nil] at s7
  have s8 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encList encElem (xs.take M).reverse) tW3 [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem (xs.drop M)) ++ tW2) [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s8
  rcases bmRevList_computesStageLe encElem (xs.take M).reverse
    (encodeDelimWord (encList encElem (xs.drop M)) ++ tW2) tW3 tW4 tW5 tSch with ⟨tR, htR, s9⟩
  dsimp only at htR
  simp only [List.reverse_reverse] at s9
  have s10 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
    (encList encElem (xs.take M)) [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem (xs.drop M)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at s10
  have s11 := tmMoveWord_computesInTime kWork2 kWork1 kIO (by decide) (by decide) (by decide)
    (encList encElem (xs.drop M)) tW2 [] []
    (mkTapes8 [] (encodeDelimWord (encList encElem (xs.take M)).reverse) [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork1, update_mkTapes8_kIO,
    List.append_nil] at s11
  have s12 := tmPackPairFromRev_computesInTime
    (encList encElem (xs.take M)) (encList encElem (xs.drop M))
    tW2 tW3 tW4 tW5 tSch
  have hlen_rev := length_encList_reverse encElem (xs.take M)
  have hlen_sum := length_encList_take_add_drop encElem M xs
  simp only [hlen_rev] at s8 htR
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq s12))))))))))⟩
  nlinarith

/-- **Single-Pass Contiguous Block Slicer (`bmSliceListBlocks`)**:
Consumes `encPair (encPair encUnary encUnary) (encList encElem) ((B, M), xs)` on `kIO`
(with `B * M ≤ xs.length` and `∀ x ∈ xs, (encElem x).length ≤ L`) and slices `xs` into `B`
contiguous blocks of length `M`:
`encList (encList encElem) ((List.range B).map (fun b => (xs.drop (b * M)).take M))`
in $O(B \cdot M \cdot L + |xs|)$ `TM2.step` transitions without copying the remaining tail `xs.drop (b * M)` at each step. -/
def bmSliceListBlocks : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kIO).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmRevMoveWord kWork0 kSched).seq
          ((tmPopFirstSubwordRev kIO kWork0).seq
            ((tmDropWord kIO).seq
              ((tmRevMoveWord kWork0 kWork3).seq
                ((tmPopFirstSubwordRev kIO kWork0).seq
                  ((tmDropWord kIO).seq
                    ((tmRevMoveWord kWork0 kWork2).seq
                      ((tmPushEmpty kWork4).seq
                        ((((tmDupWord kWork3 kWork0 kWork1).seq
                            ((tmPushEmpty kWork5).seq
                              ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                                  (tmPrependRevWord kWork0 kWork5)).loopDelimWord kWork1).seq
                                ((tmMoveWord kWork5 kWork0 kIO).seq
                                  (bmRevList.seq
                                    ((tmRevMoveWord kIO kWork0).seq
                                      (tmPrependRevWord kWork0 kWork4))))))).loopDelimWord kSched).seq
                          ((tmDropWord kWork2).seq
                            ((tmDropWord kWork3).seq
                              ((tmMoveWord kWork4 kWork0 kIO).seq bmRevList))))))))))))))

theorem bmSliceListBlocks_computesInTime {α : Type} [Inhabited α] (encElem : α → List Bool)
    (B M : ℕ) (xs : List α) (hBM : B * M ≤ xs.length) (L : ℕ)
    (hL : ∀ x ∈ xs, (encElem x).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ B * (M * (80 * L + 100) + 100) + 40 * (encList encElem xs).length +
          20 * B + 20 * M + 100,
      bmSliceListBlocks.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encList encElem) ((B, M), xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList encElem) ((List.range B).map (fun b => (xs.drop (b * M)).take M))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encPair encUnary encUnary (B, M)) ++ encodeDelimWord (encList encElem xs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encPair encUnary encUnary (B, M)).reverse []
    (encodeDelimWord (encodeDelimWord (encList encElem xs)))
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary B) ++ encodeDelimWord (encUnary M))
    (encodeDelimWord (encodeDelimWord (encList encElem xs))) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append, length_encUnary] at s3
  have s4 := tmRevMoveWord_computesInTime kWork0 kSched (by decide)
    (encUnary B).reverse [] tSch
    (mkTapes8
      (encodeDelimWord (encodeDelimWord (encUnary M)) ++
        encodeDelimWord (encodeDelimWord (encList encElem xs)))
      [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kSched, List.length_reverse,
    List.reverse_reverse, length_encUnary, List.append_nil] at s4
  have s5 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary M))
    (encodeDelimWord (encodeDelimWord (encList encElem xs))) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary B) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord, length_encUnary] at s5
  have s6 := tmDropWord_computesInTime kIO []
    (encodeDelimWord (encodeDelimWord (encList encElem xs)))
    (mkTapes8 [] (encodeDelimWord (encUnary M).reverse) []
      tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary B) ++ tSch))
  simp only [update_mkTapes8_kIO, List.length_nil] at s6
  have s7 := tmRevMoveWord_computesInTime kWork0 kWork3 (by decide)
    (encUnary M).reverse [] tW3
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encElem xs))) [] [] tW2 [] tW4 tW5
      (encodeDelimWord (encUnary B) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
    List.reverse_reverse, length_encUnary, List.append_nil] at s7
  have s8 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encElem xs)) [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord (encUnary M) ++ tW3) tW4 tW5
      (encodeDelimWord (encUnary B) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s8
  have s9 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encElem xs).reverse) [] tW2
      (encodeDelimWord (encUnary M) ++ tW3) tW4 tW5 (encodeDelimWord (encUnary B) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s9
  have s10 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encElem xs).reverse [] tW2
    (mkTapes8 [] [] [] [] (encodeDelimWord (encUnary M) ++ tW3) tW4 tW5
      (encodeDelimWord (encUnary B) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s10
  have s11 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2)
      (encodeDelimWord (encUnary M) ++ tW3) tW4 tW5 (encodeDelimWord (encUnary B) ++ tSch))
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s11
  have hinner : ∀ (k : ℕ) (rem blkAcc : List α) (restW3 restW4 restSch : List Bool),
      k ≤ rem.length → (∀ x ∈ rem, (encElem x).length ≤ L) →
      ∃ tI ≤ k * (2 * L + 7) + 1,
        (((tmPopFirstSubwordRev kWork2 kWork0).seq
            (tmPrependRevWord kWork0 kWork5)).loopDelimWord kWork1).ComputesInTime
          (mkTapes8 [] [] (encodeDelimWord (encUnary k))
            (encodeDelimWord (encList encElem rem) ++ tW2)
            restW3 restW4 (encodeDelimWord (encList encElem blkAcc) ++ tW5) restSch)
          (mkTapes8 [] [] []
            (encodeDelimWord (encList encElem (rem.drop k)) ++ tW2)
            restW3 restW4
            (encodeDelimWord (encList encElem ((rem.take k).reverse ++ blkAcc)) ++ tW5) restSch) tI := by
    intro k
    induction k with
    | zero =>
      intro rem blkAcc restW3 restW4 restSch _ _
      simp only [Nat.zero_mul, Nat.zero_add, List.drop_zero, List.take_zero, List.reverse_nil,
        List.nil_append, encUnary, List.replicate_zero]
      refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
      simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, mkTapes8_kWork1,
        update_mkTapes8_kWork1, List.head?_cons, List.tail_cons, Option.getD_some, cond_true]
    | succ k ih =>
      intro rem blkAcc restW3 restW4 restSch hk hremL
      rcases rem with _ | ⟨x, rem'⟩
      · simp at hk
      · have hk' : k ≤ rem'.length := Nat.le_of_succ_le_succ hk
        have hxL : (encElem x).length ≤ L := hremL x List.mem_cons_self
        have hremL' : ∀ y ∈ rem', (encElem y).length ≤ L :=
          fun y hy => hremL y (List.mem_cons_of_mem x hy)
        let body := (tmPopFirstSubwordRev kWork2 kWork0).seq (tmPrependRevWord kWork0 kWork5)
        have hpop : (body.loopDelimWord kWork1).toFinTM2.step
            ⟨some none, default,
              mkTapes8 [] [] (encodeDelimWord (encUnary (k + 1)))
                (encodeDelimWord (encList encElem (x :: rem')) ++ tW2)
                restW3 restW4 (encodeDelimWord (encList encElem blkAcc) ++ tW5) restSch⟩ =
            some ⟨some (some body.main), default,
              mkTapes8 [] [] (encodeDelimWord (encUnary k))
                (encodeDelimWord (encList encElem (x :: rem')) ++ tW2)
                restW3 restW4 (encodeDelimWord (encList encElem blkAcc) ++ tW5) restSch⟩ := by
          simp only [encUnary, List.replicate_succ, BitMachine.loopDelimWord, BitMachine.toFinTM2,
            mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
            encodeDelimWord_cons, mkTapes8_kWork1,
            update_mkTapes8_kWork1, List.head?_cons, List.tail_cons, Option.getD_some, cond_false]
        have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
          (encodeDelimWord (encElem x) ++ encList encElem rem') tW2 []
          (mkTapes8 [] [] (encodeDelimWord (encUnary k)) []
            restW3 restW4 (encodeDelimWord (encList encElem blkAcc) ++ tW5) restSch)
        simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
          unconsDelimWord_encodeDelimWord_append] at b1
        have b2 := tmPrependRevWord_computesInTime kWork0 kWork5 (by decide)
          (encElem x).reverse (encList encElem blkAcc) [] tW5
          (mkTapes8 [] [] (encodeDelimWord (encUnary k))
            (encodeDelimWord (encList encElem rem') ++ tW2) restW3 restW4 [] restSch)
        simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork5, List.length_reverse,
          List.reverse_reverse, List.append_nil] at b2
        have ⟨hb⟩ := b1.seq b2
        simp only [← encList_cons] at hb
        have hb_lifted := BitMachine.loopDelimWord_body_evalsToInTime_concrete kWork1 body hb
        rcases ih rem' (x :: blkAcc) restW3 restW4 restSch hk' hremL' with ⟨t2, ht2, ⟨hih⟩⟩
        simp only [List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append] at hih ⊢
        have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hb_lifted) hih
        refine ⟨_, ?_, ⟨hcomb⟩⟩
        nlinarith
  have houter : ∀ (b : ℕ) (rem : List α) (accBlks : List (List α)),
      b * M ≤ rem.length → (∀ x ∈ rem, (encElem x).length ≤ L) →
      ∃ tO ≤ b * (M * (30 * L + 40) + 60) + 1,
        (((tmDupWord kWork3 kWork0 kWork1).seq
            ((tmPushEmpty kWork5).seq
              ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                  (tmPrependRevWord kWork0 kWork5)).loopDelimWord kWork1).seq
                ((tmMoveWord kWork5 kWork0 kIO).seq
                  (bmRevList.seq
                    ((tmRevMoveWord kIO kWork0).seq
                      (tmPrependRevWord kWork0 kWork4))))))).loopDelimWord kSched).ComputesInTime
          (mkTapes8 [] [] []
            (encodeDelimWord (encList encElem rem) ++ tW2)
            (encodeDelimWord (encUnary M) ++ tW3)
            (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
            tW5 (encodeDelimWord (encUnary b) ++ tSch))
          (mkTapes8 [] [] []
            (encodeDelimWord (encList encElem (rem.drop (b * M))) ++ tW2)
            (encodeDelimWord (encUnary M) ++ tW3)
            (encodeDelimWord (encList (encList encElem)
              (((List.range b).map (fun i => (rem.drop (i * M)).take M)).reverse ++ accBlks)) ++ tW4)
            tW5 tSch) tO := by
    intro b
    induction b with
    | zero =>
      intro rem accBlks _ _
      simp only [Nat.zero_mul, List.drop_zero, List.range_zero, List.map_nil, List.reverse_nil,
        List.nil_append, encUnary, List.replicate_zero]
      refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
      simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
        List.nil_append, mkTapes8_kSched, update_mkTapes8_kSched, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_true]
    | succ b ih =>
      intro rem accBlks hbM hremL
      have hM_le : M ≤ rem.length := by
        have : 1 * M ≤ (b + 1) * M := Nat.mul_le_mul_right M (Nat.succ_pos b)
        omega
      have hbM' : b * M ≤ (rem.drop M).length := by
        rw [List.length_drop]
        have : (b + 1) * M = b * M + M := Nat.succ_mul b M
        omega
      have hremL' : ∀ x ∈ rem.drop M, (encElem x).length ≤ L :=
        fun x hx => hremL x (List.mem_of_mem_drop hx)
      let obody :=
        (tmDupWord kWork3 kWork0 kWork1).seq
          ((tmPushEmpty kWork5).seq
            ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                (tmPrependRevWord kWork0 kWork5)).loopDelimWord kWork1).seq
              ((tmMoveWord kWork5 kWork0 kIO).seq
                (bmRevList.seq
                  ((tmRevMoveWord kIO kWork0).seq
                    (tmPrependRevWord kWork0 kWork4))))))
      have hpop : (obody.loopDelimWord kSched).toFinTM2.step
          ⟨some none, default,
            mkTapes8 [] [] []
              (encodeDelimWord (encList encElem rem) ++ tW2)
              (encodeDelimWord (encUnary M) ++ tW3)
              (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
              tW5 (encodeDelimWord (encUnary (b + 1)) ++ tSch)⟩ =
          some ⟨some (some obody.main), default,
            mkTapes8 [] [] []
              (encodeDelimWord (encList encElem rem) ++ tW2)
              (encodeDelimWord (encUnary M) ++ tW3)
              (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
              tW5 (encodeDelimWord (encUnary b) ++ tSch)⟩ := by
        simp only [encUnary, List.replicate_succ, BitMachine.loopDelimWord, BitMachine.toFinTM2,
          mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
          encodeDelimWord_cons, List.cons_append, mkTapes8_kSched,
          update_mkTapes8_kSched, List.head?_cons, List.tail_cons, Option.getD_some, cond_false]
      have o1 := tmDupWord_computesInTime kWork3 kWork0 kWork1 (by decide) (by decide) (by decide)
        (encUnary M) tW3 [] []
        (mkTapes8 [] [] [] (encodeDelimWord (encList encElem rem) ++ tW2) []
          (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
          tW5 (encodeDelimWord (encUnary b) ++ tSch))
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
        List.append_nil, length_encUnary] at o1
      have o2 := tmPushEmpty_computesInTime kWork5
        (mkTapes8 [] [] (encodeDelimWord (encUnary M))
          (encodeDelimWord (encList encElem rem) ++ tW2)
          (encodeDelimWord (encUnary M) ++ tW3)
          (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
          tW5 (encodeDelimWord (encUnary b) ++ tSch))
      simp only [update_mkTapes8_kWork5, mkTapes8_kWork5] at o2
      rcases hinner M rem [] (encodeDelimWord (encUnary M) ++ tW3)
        (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
        (encodeDelimWord (encUnary b) ++ tSch) hM_le hremL with ⟨tI, htI, o3⟩
      simp only [encList_nil, List.append_nil] at o3
      have o4 := tmMoveWord_computesInTime kWork5 kWork0 kIO (by decide) (by decide) (by decide)
        (encList encElem (rem.take M).reverse) tW5 [] []
        (mkTapes8 [] [] [] (encodeDelimWord (encList encElem (rem.drop M)) ++ tW2)
          (encodeDelimWord (encUnary M) ++ tW3)
          (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
          [] (encodeDelimWord (encUnary b) ++ tSch))
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kIO,
        List.append_nil] at o4
      rcases bmRevList_computesStageLe encElem (rem.take M).reverse
        (encodeDelimWord (encList encElem (rem.drop M)) ++ tW2)
        (encodeDelimWord (encUnary M) ++ tW3)
        (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
        tW5 (encodeDelimWord (encUnary b) ++ tSch) with ⟨tR, htR, o5⟩
      dsimp only at htR
      simp only [List.reverse_reverse] at o5
      have o6 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
        (encList encElem (rem.take M)) [] []
        (mkTapes8 [] [] [] (encodeDelimWord (encList encElem (rem.drop M)) ++ tW2)
          (encodeDelimWord (encUnary M) ++ tW3)
          (encodeDelimWord (encList (encList encElem) accBlks) ++ tW4)
          tW5 (encodeDelimWord (encUnary b) ++ tSch))
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at o6
      have o7 := tmPrependRevWord_computesInTime kWork0 kWork4 (by decide)
        (encList encElem (rem.take M)).reverse (encList (encList encElem) accBlks) [] tW4
        (mkTapes8 [] [] [] (encodeDelimWord (encList encElem (rem.drop M)) ++ tW2)
          (encodeDelimWord (encUnary M) ++ tW3) [] tW5 (encodeDelimWord (encUnary b) ++ tSch))
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork4, List.length_reverse,
        List.reverse_reverse, List.append_nil] at o7
      have ⟨hob⟩ := o1.seq (o2.seq (o3.seq (o4.seq (o5.seq (o6.seq o7)))))
      simp only [← encList_cons] at hob
      have hob_lifted := BitMachine.loopDelimWord_body_evalsToInTime_concrete kSched obody hob
      rcases ih (rem.drop M) (rem.take M :: accBlks) hbM' hremL' with ⟨t2, ht2, ⟨hih⟩⟩
      have hdrop_mul : (rem.drop M).drop (b * M) = rem.drop ((b + 1) * M) := by
        rw [List.drop_drop, Nat.add_comm M (b * M), ← Nat.succ_mul]
      have hmap_range :
          ((List.range b).map (fun i => ((rem.drop M).drop (i * M)).take M)).reverse ++
            (rem.take M :: accBlks) =
          ((List.range (b + 1)).map (fun i => (rem.drop (i * M)).take M)).reverse ++ accBlks := by
        rw [List.range_succ_eq_map, List.map_cons, Nat.zero_mul, List.drop_zero,
          List.reverse_cons, List.append_assoc, List.singleton_append, List.map_map]
        congr 2
        congr 1
        funext i
        dsimp only [Function.comp]
        rw [List.drop_drop, Nat.add_comm M (i * M), ← Nat.succ_mul]
      rw [hdrop_mul, hmap_range] at hih
      have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hob_lifted) hih
      have hlen_take_rev := length_encList_reverse encElem (rem.take M)
      have hlen_take_le : (encList encElem (rem.take M)).length ≤ M * (2 * L + 2) := by
        have h := length_encList_le_of_forall_le encElem L (rem.take M)
          (fun x hx => hremL x (List.mem_of_mem_take hx))
        have htl : (rem.take M).length = M := List.length_take_of_le hM_le
        rwa [htl] at h
      simp only [hlen_take_rev] at o4 htR
      refine ⟨_, ?_, ⟨hcomb⟩⟩
      nlinarith
  rcases houter B xs [] hBM hL with ⟨tO, htO, s12⟩
  simp only [List.append_nil] at s12
  have s13 := tmDropWord_computesInTime kWork2 (encList encElem (xs.drop (B * M))) tW2
    (mkTapes8 [] [] [] [] (encodeDelimWord (encUnary M) ++ tW3)
      (encodeDelimWord (encList (encList encElem)
        ((List.range B).map (fun i => (xs.drop (i * M)).take M)).reverse) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork2] at s13
  have s14 := tmDropWord_computesInTime kWork3 (encUnary M) tW3
    (mkTapes8 [] [] [] tW2 []
      (encodeDelimWord (encList (encList encElem)
        ((List.range B).map (fun i => (xs.drop (i * M)).take M)).reverse) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3, length_encUnary] at s14
  have s15 := tmMoveWord_computesInTime kWork4 kWork0 kIO (by decide) (by decide) (by decide)
    (encList (encList encElem)
      ((List.range B).map (fun i => (xs.drop (i * M)).take M)).reverse) tW4 [] []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s15
  rcases bmRevList_computesStageLe (encList encElem)
    ((List.range B).map (fun i => (xs.drop (i * M)).take M)).reverse
    tW2 tW3 tW4 tW5 tSch with ⟨tR, htR, s16⟩
  dsimp only at htR
  simp only [List.reverse_reverse] at s16
  have hlen_drop_le := length_encList_drop_le encElem (B * M) xs
  have hlen_blks_rev := length_encList_reverse (encList encElem)
    ((List.range B).map (fun i => (xs.drop (i * M)).take M))
  have hlen_blks_le :
      (encList (encList encElem)
        ((List.range B).map (fun i => (xs.drop (i * M)).take M))).length ≤
      B * (2 * (M * (2 * L + 2)) + 2) := by
    have h := length_encList_le_of_forall_le (encList encElem) (M * (2 * L + 2))
      ((List.range B).map (fun i => (xs.drop (i * M)).take M))
      (fun blk hblk => by
        rcases List.mem_map.mp hblk with ⟨i, hi, rfl⟩
        have hi_lt : i < B := List.mem_range.mp hi
        have h := length_encList_le_of_forall_le encElem L ((xs.drop (i * M)).take M)
          (fun x hx => hL x (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
        have htl : ((xs.drop (i * M)).take M).length ≤ M := List.length_take_le M _
        exact le_trans h (Nat.mul_le_mul_right _ htl))
    simpa [List.length_map, List.length_range] using h
  simp only [hlen_blks_rev] at s15 htR
  simp only [encPair, List.length_append, length_encodeDelimWord, length_encUnary] at s1 s2 ⊢
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12.seq (s13.seq (s14.seq (s15.seq s16))))))))))))))⟩
  nlinarith

/-! ### `StageEval.flattenList`, `bmInterleaveList`, `bmSplitBlocks`, `bmPairBlocks`, and `bmNaturalSplitBlocks` -/

theorem encPair_eq_encList_two {α : Type} (encElem : α → List Bool) (x y : α) :
    encPair encElem encElem (x, y) = encList encElem [x, y] := by
  simp [encPair, encList, encodeWordStack]

theorem encList_append_eq {α : Type} (encElem : α → List Bool) (xs ys : List α) :
    encList encElem (xs ++ ys) = encList encElem xs ++ encList encElem ys := by
  simp [encList, encodeWordStack_append]

theorem flatten_map_encList {α : Type} (encElem : α → List Bool) :
    ∀ (xss : List (List α)),
      (xss.map (encList encElem)).flatten = encList encElem xss.flatten
  | [] => rfl
  | xs :: xss => by
    simp only [List.map_cons, List.flatten_cons, flatten_map_encList encElem xss,
      encList_append_eq]

theorem encList_encList_eq_encBits {α : Type} (encElem : α → List Bool) (xss : List (List α)) :
    encList (encList encElem) xss = encList encBits (xss.map (encList encElem)) := by
  simp [encList, encBits, List.map_map]

/-- **`StageEval.flattenList`**:
`bmFlattenBits` flattens `encList (encList encElem) xss` into `encList encElem xss.flatten` in
`≤ 11 * (encList (encList encElem) xss).length + 18` `TM2.step` transitions. -/
theorem StageEval.flattenList {S α : Type} (encElem : S → α → List Bool)
    (xss : S → List (List α)) :
    StageEval bmFlattenBits
      (fun s => encList (encList (encElem s)) (xss s))
      (fun s => encList (encElem s) (xss s).flatten)
      (fun s => 11 * (encList (encList (encElem s)) (xss s)).length + 18) := by
  refine (StageEval.congr_in
    (StageEval.congr_out (StageEval.flattenBits (fun s => (xss s).map (encList (encElem s))))
      (fun s => flatten_map_encList (encElem s) (xss s)))
    (fun s => (encList_encList_eq_encBits (encElem s) (xss s)).symm)).mono (fun s => ?_)
  rw [← encList_encList_eq_encBits]

/-- Pure list interleaving `[x_0, y_0, x_1, y_1, ...]`. -/
def interleaveList {α : Type} : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => x :: y :: interleaveList xs ys

@[simp]
theorem interleaveList_nil_left {α : Type} (ys : List α) :
    interleaveList [] ys = [] := rfl

@[simp]
theorem interleaveList_nil_right {α : Type} (xs : List α) :
    interleaveList xs [] = [] := by
  cases xs <;> rfl

@[simp]
theorem interleaveList_cons_cons {α : Type} (x y : α) (xs ys : List α) :
    interleaveList (x :: xs) (y :: ys) = x :: y :: interleaveList xs ys := rfl

theorem flatten_map_pair_zip_eq_interleaveList {α : Type} :
    ∀ (xs ys : List α),
      ((List.zip xs ys).map (fun p => [p.1, p.2])).flatten = interleaveList xs ys
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    simp [flatten_map_pair_zip_eq_interleaveList xs ys]

theorem length_interleaveList {α : Type} :
    ∀ (xs ys : List α), xs.length = ys.length →
      (interleaveList xs ys).length = 2 * xs.length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := length_interleaveList xs ys (Nat.succ.inj h)
    simp only [interleaveList_cons_cons, List.length_cons, ih]
    omega

theorem getElem_interleaveList_even {α : Type} :
    ∀ (xs ys : List α) (hlen : xs.length = ys.length) (i : ℕ) (hi : i < xs.length),
      (interleaveList xs ys)[2 * i]'(by rw [length_interleaveList xs ys hlen]; omega) = xs[i]
  | x :: xs, y :: ys, hlen, 0, _ => rfl
  | x :: xs, y :: ys, hlen, i + 1, hi => by
    have hstep : 2 * (i + 1) = (2 * i) + 2 := by omega
    simp only [interleaveList_cons_cons, hstep, List.getElem_cons_succ]
    exact getElem_interleaveList_even xs ys (Nat.succ.inj hlen) i (Nat.lt_of_succ_lt_succ hi)

theorem getElem_interleaveList_odd {α : Type} :
    ∀ (xs ys : List α) (hlen : xs.length = ys.length) (i : ℕ) (hi : i < xs.length),
      (interleaveList xs ys)[2 * i + 1]'(by rw [length_interleaveList xs ys hlen]; omega) =
        ys[i]'(hlen ▸ hi)
  | x :: xs, y :: ys, hlen, 0, _ => rfl
  | x :: xs, y :: ys, hlen, i + 1, hi => by
    have hstep : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
    simp only [interleaveList_cons_cons, hstep, List.getElem_cons_succ]
    exact getElem_interleaveList_odd xs ys (Nat.succ.inj hlen) i (Nat.lt_of_succ_lt_succ hi)

theorem deinterleaveList_interleaveList {α : Type} :
    ∀ (xs ys : List α), xs.length = ys.length →
      deinterleaveList (interleaveList xs ys) = (xs, ys)
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [interleaveList_cons_cons, deinterleaveList_cons_cons,
      deinterleaveList_interleaveList xs ys (Nat.succ.inj h)]

theorem deinterleaveList_map_range {α : Type} :
    ∀ (M : ℕ) (f : ℕ → α),
      deinterleaveList ((List.range (2 * M)).map f) =
        ((List.range M).map (fun m => f (2 * m)),
         (List.range M).map (fun m => f (2 * m + 1)))
  | 0, _ => rfl
  | M + 1, f => by
    have h2 : 2 * (M + 1) = (2 * M) + 1 + 1 := by omega
    rw [h2, List.range_succ_eq_map, List.map_cons, List.range_succ_eq_map,
      List.map_cons, List.map_cons, List.map_map, List.map_map, deinterleaveList_cons_cons]
    have ih := deinterleaveList_map_range M (fun k => f (k + 2))
    have hfun : ((f ∘ Nat.succ) ∘ Nat.succ) = fun k => f (k + 2) := rfl
    rw [hfun, ih]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero, Nat.zero_add]
    refine Prod.ext (congrArg (List.cons _) (List.map_congr_left fun m _ => rfl))
      (congrArg (List.cons _) (List.map_congr_left fun m _ => rfl))

/-- **Linear-Time List Interleaving (`bmInterleaveList`)**:
Consumes `encPair (encList encElem) (encList encElem) (xs, ys)` (`xs.length = ys.length`) and emits
`encList encElem (interleaveList xs ys)` in $O(|xs| + |ys|)$ `TM2.step` transitions. -/
def bmInterleaveList : BitMachine :=
  bmSeq bmZipList bmFlattenBits

theorem StageEval.interleaveList_stage {S α : Type} (encElem : S → α → List Bool)
    (xs ys : S → List α) (hlen : ∀ s : S, (xs s).length = (ys s).length) :
    StageEval bmInterleaveList
      (encDepPair (fun s => encList (encElem s) (xs s)) (fun s => encList (encElem s) (ys s)))
      (fun s => encList (encElem s) (interleaveList (xs s) (ys s)))
      (fun s => 150 * (encList (encElem s) (xs s)).length +
                150 * (encList (encElem s) (ys s)).length + 250) := by
  have p1 := StageEval.congr_out
    (v2 := fun s => encList (encList (encElem s))
      ((List.zip (xs s) (ys s)).map (fun p => [p.1, p.2])))
    (StageEval.zipList encElem encElem xs ys hlen)
    (fun s => by
      simp only [encList, List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      exact encPair_eq_encList_two (encElem s) p.1 p.2)
  have p2 := StageEval.congr_out
    (v2 := fun s => encList (encElem s) (interleaveList (xs s) (ys s)))
    (StageEval.flattenList encElem (fun s => (List.zip (xs s) (ys s)).map (fun p => [p.1, p.2])))
    (fun s => by rw [flatten_map_pair_zip_eq_interleaveList])
  refine (StageEval.seq p1 p2).mono (fun s => ?_)
  have hzip_eq :
      (encList (encList (encElem s))
        ((List.zip (xs s) (ys s)).map (fun p => [p.1, p.2]))).length =
      (encList (encPair (encElem s) (encElem s)) (List.zip (xs s) (ys s))).length := by
    congr 1
    simp only [encList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (encPair_eq_encList_two (encElem s) p.1 p.2).symm
  rw [hzip_eq, length_encList_zip_eq (encElem s) (encElem s) (xs s) (ys s) (hlen s)]
  have hge := length_encList_ge_two_mul_length (encElem s) (xs s)
  simp only [encPair, List.length_append, length_encodeDelimWord]
  omega

/-- Pure block-splitting pass: replaces each block `b` in `blks` with
`[(deinterleaveList b).1, (deinterleaveList b).2]`. -/
def splitBlocks {α : Type} (blks : List (List α)) : List (List α) :=
  blks.flatMap (fun b => [(deinterleaveList b).1, (deinterleaveList b).2])

theorem flatten_map_deinterleave_eq_splitBlocks {α : Type} :
    ∀ (blks : List (List α)),
      (blks.map (fun b => [(deinterleaveList b).1, (deinterleaveList b).2])).flatten =
        splitBlocks blks
  | [] => rfl
  | b :: blks => by
    simp [splitBlocks, flatten_map_deinterleave_eq_splitBlocks blks]

theorem length_encList_splitBlocks {α : Type} (encElem : α → List Bool) :
    ∀ (blks : List (List α)),
      (encList (encList encElem) (splitBlocks blks)).length =
        (encList (encList encElem) blks).length + 2 * blks.length
  | [] => rfl
  | b :: blks => by
    have ih := length_encList_splitBlocks encElem blks
    have hsum := length_encList_deinterleaveList encElem b
    simp only [splitBlocks, List.flatMap_cons, List.cons_append, List.nil_append,
      encList_cons, List.length_append, length_encodeDelimWord, List.length_cons] at ih ⊢
    omega

/-- **Radix-2 Block-Splitting Pass (`bmSplitBlocks`)**:
Splits every block `b ∈ blks` into `(deinterleaveList b).1` and `(deinterleaveList b).2` in linear time. -/
def bmSplitBlocks : BitMachine :=
  bmSeq (bmFanout bmConstEmpty bmId)
    (bmSeq (bmMapWithCtx (bmSeq bmSnd bmDeinterleaveList)) bmFlattenBits)

theorem StageEval.splitBlocks_stage {S α : Type} (encElem : S → α → List Bool)
    (blks : S → List (List α)) (L_blk : S → ℕ)
    (hL : ∀ (s : S) (b : List α), b ∈ blks s → (encList (encElem s) b).length ≤ L_blk s) :
    StageEval bmSplitBlocks
      (fun s => encList (encList (encElem s)) (blks s))
      (fun s => encList (encList (encElem s)) (splitBlocks (blks s)))
      (fun s => (blks s).length * (200 * L_blk s + 400) + 200) := by
  have pInit := StageEval.fanout
    (StageEval.constEmpty (fun s => encList (encList (encElem s)) (blks s)))
    (StageEval.id_stage (fun s => encList (encList (encElem s)) (blks s)))
  let SubS := { p : S × List α // p.2 ∈ blks p.1 }
  have pBody : StageEval (S := SubS) (bmSeq bmSnd bmDeinterleaveList)
      (encDepPair (fun _ => []) (fun p => encList (encElem p.val.1) p.val.2))
      (fun p => encList (encList (encElem p.val.1))
        [(deinterleaveList p.val.2).1, (deinterleaveList p.val.2).2])
      (fun p => 30 * L_blk p.val.1 + 80) := by
    have b1 := StageEval.snd (fun _ : SubS => ([] : List Bool))
      (fun p => encList (encElem p.val.1) p.val.2)
    have b2 := StageEval.congr_out
      (v2 := fun p : SubS => encList (encList (encElem p.val.1))
        [(deinterleaveList p.val.2).1, (deinterleaveList p.val.2).2])
      (StageEval.deinterleaveList_stage (fun p : SubS => encElem p.val.1) (fun p => p.val.2))
      (fun p => encPair_eq_encList_two (encList (encElem p.val.1))
        (deinterleaveList p.val.2).1 (deinterleaveList p.val.2).2)
    refine (StageEval.seq b1 b2).mono (fun p => ?_)
    have hb := hL p.val.1 p.val.2 p.property
    simp only [List.length_nil]
    omega
  have pMap := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := blks)
    (encA := fun s => encList (encElem s))
    (encB := fun s => encList (encList (encElem s)))
    (fn := fun _ b => [(deinterleaveList b).1, (deinterleaveList b).2])
    (B := fun s => 30 * L_blk s + 80)
    (L_A := L_blk)
    (L_B := fun s => 2 * L_blk s + 4)
    pBody hL
    (fun s b hb => by
      rw [← encPair_eq_encList_two]
      simp only [length_encPair]
      have hsum := length_encList_deinterleaveList (encElem s) b
      have hb' := hL s b hb
      omega)
  have pFlat := StageEval.congr_out
    (v2 := fun s => encList (encList (encElem s)) (splitBlocks (blks s)))
    (StageEval.flattenList (fun s => encList (encElem s))
      (fun s => (blks s).map (fun b => [(deinterleaveList b).1, (deinterleaveList b).2])))
    (fun s => by rw [flatten_map_deinterleave_eq_splitBlocks])
  refine (StageEval.seq pInit (StageEval.seq pMap pFlat)).mono (fun s => ?_)
  have hlen_in : (encList (encList (encElem s)) (blks s)).length ≤
      (blks s).length * (2 * L_blk s + 2) :=
    length_encList_le_of_forall_le (encList (encElem s)) (L_blk s) (blks s) (hL s)
  have hlen_mid :
      (encList (encList (encList (encElem s)))
        ((blks s).map (fun b => [(deinterleaveList b).1, (deinterleaveList b).2]))).length ≤
      (blks s).length * (2 * (2 * L_blk s + 4) + 2) := by
    have h := length_encList_le_of_forall_le (encList (encList (encElem s))) (2 * L_blk s + 4)
      ((blks s).map (fun b => [(deinterleaveList b).1, (deinterleaveList b).2]))
      (fun pair hp => by
        rcases List.mem_map.mp hp with ⟨b, hb, rfl⟩
        rw [← encPair_eq_encList_two]
        simp only [length_encPair]
        have hsum := length_encList_deinterleaveList (encElem s) b
        have hb' := hL s b hb
        omega)
    simpa [List.length_map] using h
  simp only [List.length_nil]
  nlinarith

theorem deinterleaveList_flatMap_two {α β : Type} (f g : α → β) :
    ∀ (xs : List α),
      deinterleaveList (xs.flatMap (fun x => [f x, g x])) = (xs.map f, xs.map g)
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      deinterleaveList_cons_cons, deinterleaveList_flatMap_two f g xs, List.map_cons]

/-- **Radix-2 Block-Pairing Pass (`bmPairBlocks`)**:
Pairs adjacent blocks `[E_0, O_0, E_1, O_1, ...]` into `[(E_0, O_0), (E_1, O_1), ...]`. -/
def bmPairBlocks : BitMachine :=
  bmSeq bmDeinterleaveList bmZipList

theorem StageEval.pairBlocks_stage {S α β : Type} (encElem : S → β → List Bool)
    (xs : S → List α) (f g : S → α → List β) :
    StageEval bmPairBlocks
      (fun s => encList (encList (encElem s)) ((xs s).flatMap (fun x => [f s x, g s x])))
      (fun s => encList (encPair (encList (encElem s)) (encList (encElem s)))
        ((xs s).map (fun x => (f s x, g s x))))
      (fun s => 150 * (encList (encList (encElem s))
        ((xs s).flatMap (fun x => [f s x, g s x]))).length + 250) := by
  have p1 : StageEval bmDeinterleaveList
      (fun s => encList (encList (encElem s)) ((xs s).flatMap (fun x => [f s x, g s x])))
      (encDepPair (fun s => encList (encList (encElem s)) ((xs s).map (f s)))
                  (fun s => encList (encList (encElem s)) ((xs s).map (g s))))
      (fun s => 24 * (encList (encList (encElem s))
        ((xs s).flatMap (fun x => [f s x, g s x]))).length + 55) := by
    refine StageEval.congr_out
      (v2 := encDepPair (fun s => encList (encList (encElem s)) ((xs s).map (f s)))
                        (fun s => encList (encList (encElem s)) ((xs s).map (g s))))
      (StageEval.deinterleaveList_stage (fun s => encList (encElem s))
        (fun s => (xs s).flatMap (fun x => [f s x, g s x])))
      (fun s => by simp [encDepPair, deinterleaveList_flatMap_two])
  have p2 := StageEval.congr_out
    (v2 := fun s => encList (encPair (encList (encElem s)) (encList (encElem s)))
      ((xs s).map (fun x => (f s x, g s x))))
    (StageEval.zipList (fun s => encList (encElem s)) (fun s => encList (encElem s))
      (fun s => (xs s).map (f s)) (fun s => (xs s).map (g s))
      (fun s => by simp))
    (fun s => by
      congr 1
      induction (xs s) with
      | nil => rfl
      | cons x l ih => simp [ih])
  refine (StageEval.seq p1 p2).mono (fun s => ?_)
  have hsum :
      (encList (encList (encElem s)) ((xs s).map (f s))).length +
      (encList (encList (encElem s)) ((xs s).map (g s))).length =
      (encList (encList (encElem s)) ((xs s).flatMap (fun x => [f s x, g s x]))).length := by
    have h := length_encList_deinterleaveList (encList (encElem s))
      ((xs s).flatMap (fun x => [f s x, g s x]))
    simpa [deinterleaveList_flatMap_two] using h
  simp only [encPair, List.length_append, length_encodeDelimWord]
  omega

/-- Pure natural block-splitting pass: puts all even sub-blocks first and all odd sub-blocks second. -/
def naturalSplitBlocks {α : Type} (blks : List (List α)) : List (List α) :=
  blks.map (fun b => (deinterleaveList b).1) ++ blks.map (fun b => (deinterleaveList b).2)

/-- **Natural-Order Radix-2 Block-Splitting Pass (`bmNaturalSplitBlocks`)**:
Transforms `blks` into `blks.map (·.1) ++ blks.map (·.2)` in $O(\sum |b|)$ steps. -/
def bmNaturalSplitBlocks : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq (bmFanout bmConstEmpty bmId)
        (bmMapWithCtx (bmSeq bmSnd (bmSeq bmDeinterleaveList bmFst))))
      (bmSeq (bmFanout bmConstEmpty bmId)
        (bmMapWithCtx (bmSeq bmSnd (bmSeq bmDeinterleaveList bmSnd)))))
    bmAppendList

theorem StageEval.naturalSplitBlocks_stage {S α : Type} (encElem : S → α → List Bool)
    (blks : S → List (List α)) (L_blk : S → ℕ)
    (hL : ∀ (s : S) (b : List α), b ∈ blks s → (encList (encElem s) b).length ≤ L_blk s) :
    StageEval bmNaturalSplitBlocks
      (fun s => encList (encList (encElem s)) (blks s))
      (fun s => encList (encList (encElem s)) (naturalSplitBlocks (blks s)))
      (fun s => (blks s).length * (220 * L_blk s + 400) + 250) := by
  let SubS := { p : S × List α // p.2 ∈ blks p.1 }
  have pInit := StageEval.fanout
    (StageEval.constEmpty (fun s => encList (encList (encElem s)) (blks s)))
    (StageEval.id_stage (fun s => encList (encList (encElem s)) (blks s)))
  have pBody1 : StageEval (S := SubS) (bmSeq bmSnd (bmSeq bmDeinterleaveList bmFst))
      (encDepPair (fun _ => []) (fun p => encList (encElem p.val.1) p.val.2))
      (fun p => encList (encElem p.val.1) (deinterleaveList p.val.2).1)
      (fun p => 32 * L_blk p.val.1 + 80) := by
    have b1 := StageEval.snd (fun _ : SubS => ([] : List Bool))
      (fun p => encList (encElem p.val.1) p.val.2)
    have b2 := StageEval.deinterleaveList_stage (fun p : SubS => encElem p.val.1) (fun p => p.val.2)
    have b3 := StageEval.fst
      (fun p : SubS => encList (encElem p.val.1) (deinterleaveList p.val.2).1)
      (fun p : SubS => encList (encElem p.val.1) (deinterleaveList p.val.2).2)
    refine (StageEval.seq b1 (StageEval.seq b2 b3)).mono (fun p => ?_)
    have hsum := length_encList_deinterleaveList (encElem p.val.1) p.val.2
    have hb := hL p.val.1 p.val.2 p.property
    simp only [List.length_nil]
    omega
  have pBody2 : StageEval (S := SubS) (bmSeq bmSnd (bmSeq bmDeinterleaveList bmSnd))
      (encDepPair (fun _ => []) (fun p => encList (encElem p.val.1) p.val.2))
      (fun p => encList (encElem p.val.1) (deinterleaveList p.val.2).2)
      (fun p => 32 * L_blk p.val.1 + 80) := by
    have b1 := StageEval.snd (fun _ : SubS => ([] : List Bool))
      (fun p => encList (encElem p.val.1) p.val.2)
    have b2 := StageEval.deinterleaveList_stage (fun p : SubS => encElem p.val.1) (fun p => p.val.2)
    have b3 := StageEval.snd
      (fun p : SubS => encList (encElem p.val.1) (deinterleaveList p.val.2).1)
      (fun p : SubS => encList (encElem p.val.1) (deinterleaveList p.val.2).2)
    refine (StageEval.seq b1 (StageEval.seq b2 b3)).mono (fun p => ?_)
    have hsum := length_encList_deinterleaveList (encElem p.val.1) p.val.2
    have hb := hL p.val.1 p.val.2 p.property
    simp only [List.length_nil]
    omega
  have pMap1 := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := blks)
    (encA := fun s => encList (encElem s))
    (encB := fun s => encList (encElem s))
    (fn := fun _ b => (deinterleaveList b).1)
    (B := fun s => 32 * L_blk s + 80)
    (L_A := L_blk)
    (L_B := L_blk)
    pBody1 hL
    (fun s b hb => by
      have hsum := length_encList_deinterleaveList (encElem s) b
      have hb' := hL s b hb
      omega)
  have pMap2 := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := blks)
    (encA := fun s => encList (encElem s))
    (encB := fun s => encList (encElem s))
    (fn := fun _ b => (deinterleaveList b).2)
    (B := fun s => 32 * L_blk s + 80)
    (L_A := L_blk)
    (L_B := L_blk)
    pBody2 hL
    (fun s b hb => by
      have hsum := length_encList_deinterleaveList (encElem s) b
      have hb' := hL s b hb
      omega)
  have pApp := StageEval.appendList (fun s => encList (encElem s))
    (fun s => (blks s).map (fun b => (deinterleaveList b).1))
    (fun s => (blks s).map (fun b => (deinterleaveList b).2))
  refine (StageEval.seq (StageEval.fanout (StageEval.seq pInit pMap1) (StageEval.seq pInit pMap2))
    pApp).mono (fun s => ?_)
  have hlen_in : (encList (encList (encElem s)) (blks s)).length ≤
      (blks s).length * (2 * L_blk s + 2) :=
    length_encList_le_of_forall_le (encList (encElem s)) (L_blk s) (blks s) (hL s)
  have hlen_m1 :
      (encList (encList (encElem s)) ((blks s).map (fun b => (deinterleaveList b).1))).length ≤
      (blks s).length * (2 * L_blk s + 2) := by
    have h := length_encList_le_of_forall_le (encList (encElem s)) (L_blk s)
      ((blks s).map (fun b => (deinterleaveList b).1))
      (fun y hy => by
        rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
        have hsum := length_encList_deinterleaveList (encElem s) b
        have hb' := hL s b hb
        omega)
    simpa [List.length_map] using h
  have hlen_m2 :
      (encList (encList (encElem s)) ((blks s).map (fun b => (deinterleaveList b).2))).length ≤
      (blks s).length * (2 * L_blk s + 2) := by
    have h := length_encList_le_of_forall_le (encList (encElem s)) (L_blk s)
      ((blks s).map (fun b => (deinterleaveList b).2))
      (fun y hy => by
        rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
        have hsum := length_encList_deinterleaveList (encElem s) b
        have hb' := hL s b hb
        omega)
    simpa [List.length_map] using h
  simp only [List.length_nil]
  nlinarith

/-! ## 2. Multi-Pass Gather, Matrix Transpose, Frequency Scatter & Nyquist Mode Sum (`bmNaturalSplitPasses`, `bmOddStrideGather`, `bmTransposeMatrix`, `bmFreqScatter`, `bmNyquistModeSum`) -/

/-- Exact invariant of `d` passes of `naturalSplitBlocks` on `[(List.range (2^k * M)).map f]`. -/
theorem naturalSplitBlocks_map_range {α : Type} (k M : ℕ) (f : ℕ → α) (d : ℕ) (hd : d < k) :
    naturalSplitBlocks
      ((List.range (2 ^ d)).map (fun j1 =>
        (List.range (2 ^ (k - d) * M)).map (fun j2 => f (j1 + 2 ^ d * j2)))) =
    (List.range (2 ^ (d + 1))).map (fun j1 =>
      (List.range (2 ^ (k - (d + 1)) * M)).map (fun j2 => f (j1 + 2 ^ (d + 1) * j2))) := by
  unfold naturalSplitBlocks
  have hpow_sub : 2 ^ (k - d) * M = 2 * (2 ^ (k - (d + 1)) * M) := by
    rw [show k - d = (k - (d + 1)) + 1 by omega, Nat.pow_succ', Nat.mul_assoc]
  have hpow_d : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
    rw [Nat.pow_succ', Nat.two_mul]
  rw [hpow_d, List.range_add, List.map_append, List.map_map, List.map_map, List.map_map]
  congr 1
  · congr 1
    funext j1
    dsimp only [Function.comp]
    rw [hpow_sub, deinterleaveList_map_range]
    dsimp only
    congr 1
    funext m
    congr 1
    ring
  · congr 1
    funext j1
    dsimp only [Function.comp]
    rw [hpow_sub, deinterleaveList_map_range]
    dsimp only
    congr 1
    funext m
    congr 1
    ring

/-- **Multi-Pass Stride-$2^k$ Gather (`bmNaturalSplitPasses`)**:
Consumes `encPair encUnary (encList encElem) (k, (List.range (2^k * M)).map f)` on `kIO` and emits
`encList (encList encElem) ((List.range (2^k)).map (fun j1 => (List.range M).map (fun j2 => f (j1 + 2^k * j2))))`
in $O((k + 1) \cdot 2^k \cdot M \cdot L)$ `TM2.step` transitions. -/
def bmNaturalSplitPasses : BitMachine :=
  bmSeq (bmMapSnd bmSingletonList) (bmIterLoop bmNaturalSplitBlocks)

theorem bmNaturalSplitPasses_computesInTime {α : Type} (encElem : α → List Bool)
    (k M : ℕ) (hM : 1 ≤ M) (f : ℕ → α) (L : ℕ) (hL : ∀ i < 2 ^ k * M, (encElem (f i)).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (k + 1) * (1000 * (2 ^ k * M) * (L + 2)),
      bmNaturalSplitPasses.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encList encElem) (k, (List.range (2 ^ k * M)).map f)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList encElem)
            ((List.range (2 ^ k)).map (fun j1 =>
              (List.range M).map (fun j2 => f (j1 + 2 ^ k * j2))))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uStage : ℕ → List Bool := fun d =>
    encList (encList encElem)
      ((List.range (2 ^ d)).map (fun j1 =>
        (List.range (2 ^ (k - d) * M)).map (fun j2 => f (j1 + 2 ^ d * j2))))
  have p1 : StageEval (S := S) (bmMapSnd bmSingletonList)
      (fun _ => encPair encUnary (encList encElem) (k, (List.range (2 ^ k * M)).map f))
      (encDepPair (fun _ => encUnary k) (fun _ => uStage 0))
      (fun _ => 30 * k + 30 * (encList encElem ((List.range (2 ^ k * M)).map f)).length + 100) := by
    have h0 : uStage 0 = encList (encList encElem) [(List.range (2 ^ k * M)).map f] := by
      dsimp [uStage]
      simp
    rw [h0]
    exact (StageEval.mapSnd (u1 := fun _ : S => encUnary k)
      (StageEval.of_computesStageLe (bmSingletonList_computesStageLe (encList encElem))
        (fun _ => (List.range (2 ^ k * M)).map f))).mono (fun _ => by
      simp only [length_encUnary, encList_cons, encList_nil, List.append_nil, length_encodeDelimWord]
      omega)
  let LoopS := { p : S × ℕ // p.2 < k }
  have pStep : StageEval (S := LoopS) bmNaturalSplitBlocks
      (fun p => uStage p.val.2)
      (fun p => uStage (p.val.2 + 1))
      (fun _ => 450 * (2 ^ k * M) * (L + 2) + 500) := by
    intro ⟨⟨_, d⟩, hd⟩ u2 u3 u4 u5 uS
    dsimp only [id, LoopS] at hd ⊢
    have hpow_eq : 2 ^ d * (2 ^ (k - d) * M) = 2 ^ k * M := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le (le_of_lt hd)]
    have hstep := StageEval.congr_out
      (v2 := fun _ : Unit => uStage (d + 1))
      (StageEval.naturalSplitBlocks_stage (S := Unit) (fun _ => encElem)
        (fun _ => (List.range (2 ^ d)).map (fun j1 =>
          (List.range (2 ^ (k - d) * M)).map (fun j2 => f (j1 + 2 ^ d * j2))))
        (fun _ => (2 ^ (k - d) * M) * (2 * L + 2))
        (fun _ b hb => by
          rcases List.mem_map.mp hb with ⟨j1, hj1, rfl⟩
          have hj1_lt : j1 < 2 ^ d := List.mem_range.mp hj1
          have h := length_encList_le_of_forall_le encElem L
            ((List.range (2 ^ (k - d) * M)).map (fun j2 => f (j1 + 2 ^ d * j2)))
            (fun y hy => by
              rcases List.mem_map.mp hy with ⟨j2, hj2, rfl⟩
              have hj2_lt : j2 < 2 ^ (k - d) * M := List.mem_range.mp hj2
              apply hL
              calc j1 + 2 ^ d * j2 < 2 ^ d + 2 ^ d * j2 := Nat.add_lt_add_right hj1_lt _
                _ = 2 ^ d * (j2 + 1) := by ring
                _ ≤ 2 ^ d * (2 ^ (k - d) * M) := Nat.mul_le_mul_left _ hj2_lt
                _ = 2 ^ k * M := hpow_eq)
          simpa [List.length_map, List.length_range] using h))
      (fun _ => by dsimp only [uStage]; rw [naturalSplitBlocks_map_range k M f d hd])
    rcases hstep () u2 u3 u4 u5 uS with ⟨t, ht, hcomp⟩
    dsimp only at ht hcomp
    simp only [List.length_map, List.length_range] at ht
    have h2d_le : 2 ^ d ≤ 2 ^ k * M := by
      calc 2 ^ d ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (le_of_lt hd)
        _ ≤ 2 ^ k * M := Nat.le_mul_of_pos_right _ hM
    refine ⟨t, ?_, hcomp⟩
    have hprod : 2 ^ d * (220 * (2 ^ (k - d) * M * (2 * L + 2)) + 400) =
        440 * (2 ^ d * (2 ^ (k - d) * M)) * (L + 1) + 400 * 2 ^ d := by ring
    rw [hprod, hpow_eq] at ht
    nlinarith
  have p2 := StageEval.congr_out
    (v2 := fun _ : S => encList (encList encElem)
      ((List.range (2 ^ k)).map (fun j1 =>
        (List.range M).map (fun j2 => f (j1 + 2 ^ k * j2)))))
    (StageEval.iterLoop_idx (k := fun _ : S => k) (u := fun _ => uStage)
      (B := fun _ => 450 * (2 ^ k * M) * (L + 2) + 500) pStep)
    (fun _ => by
      dsimp only [uStage]
      simp)
  rcases (StageEval.seq p1 p2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uStage, id] at ht hcomp
  have hlen_in : (encList encElem ((List.range (2 ^ k * M)).map f)).length ≤
      (2 ^ k * M) * (2 * L + 2) := by
    have h := length_encList_le_of_forall_le encElem L ((List.range (2 ^ k * M)).map f)
      (fun y hy => by
        rcases List.mem_map.mp hy with ⟨i, hi, rfl⟩
        exact hL i (List.mem_range.mp hi))
    simpa [List.length_map, List.length_range] using h
  have hlen_u0 :
      (encList (encList encElem)
        ((List.range (2 ^ 0)).map (fun j1 =>
          (List.range (2 ^ (k - 0) * M)).map (fun j2 => f (j1 + 2 ^ 0 * j2))))).length =
      2 * (encList encElem ((List.range (2 ^ k * M)).map f)).length + 2 := by
    simp [encList]
  rw [hlen_u0] at ht
  have h2kM_pos : 1 ≤ 2 ^ k * M := Nat.mul_pos (Nat.two_pow_pos k) hM
  refine ⟨t, ?_, hcomp⟩
  nlinarith

theorem map_finRange_eq_map_range_of_eq {n : ℕ} {α : Type*} (f : Fin n → α) (g : ℕ → α)
    (hfg : ∀ i : Fin n, f i = g i.val) :
    (List.finRange n).map f = (List.range n).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    exact hfg ⟨i, by simpa using h1⟩

theorem flatten_matrix_eq_map_range {N M : ℕ} {α : Type*} (mat : Fin N → Fin M → α)
    (hN : 0 < N) (hM : 0 < M) :
    ((List.finRange N).map (fun i => (List.finRange M).map (fun j => mat i j))).flatten =
      (List.range (N * M)).map (fun u =>
        mat ⟨(u / M) % N, Nat.mod_lt _ hN⟩ ⟨u % M, Nat.mod_lt _ hM⟩) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.finRange_succ, List.map_cons, List.flatten_cons, List.map_map]
    rcases Nat.eq_zero_or_pos N with rfl | hN_pos
    · simp only [List.finRange_zero, List.map_nil, List.flatten_nil, List.append_nil,
        Nat.zero_add, Nat.one_mul]
      refine map_finRange_eq_map_range_of_eq (fun j => mat 0 j) _ (fun j => ?_)
      have hdiv : j.val / M = 0 := Nat.div_eq_of_lt j.isLt
      have hmod : j.val % M = j.val := Nat.mod_eq_of_lt j.isLt
      exact congrArg₂ mat (Fin.ext (by simp [hdiv])) (Fin.ext hmod.symm)
    · have ih' := ih (fun i j => mat i.succ j) hN_pos
      have hfun : ((fun i => (List.finRange M).map (fun j => mat i j)) ∘ Fin.succ) =
          fun i : Fin N => (List.finRange M).map (fun j => mat i.succ j) := rfl
      rw [hfun, ih', show (N + 1) * M = M + N * M by ring, List.range_add, List.map_append]
      congr 1
      · refine map_finRange_eq_map_range_of_eq (fun j => mat 0 j) _ (fun j => ?_)
        have hdiv : j.val / M = 0 := Nat.div_eq_of_lt j.isLt
        have hmod : j.val % M = j.val := Nat.mod_eq_of_lt j.isLt
        exact congrArg₂ mat (Fin.ext (by simp [hdiv])) (Fin.ext hmod.symm)
      · rw [List.map_map]
        apply List.map_congr_left
        intro u hu
        have hu_lt : u < N * M := List.mem_range.mp hu
        dsimp only [Function.comp]
        have hdiv : (M + u) / M = u / M + 1 := by
          rw [Nat.add_comm M u, Nat.add_div_right u hM]
        have hmod : (M + u) % M = u % M := by
          rw [Nat.add_comm M u, Nat.add_mod_right]
        have hu_div_lt : u / M < N := (Nat.div_lt_iff_lt_mul hM).mpr hu_lt
        have hdiv_mod : (u / M + 1) % (N + 1) = u / M + 1 :=
          Nat.mod_eq_of_lt (Nat.succ_lt_succ hu_div_lt)
        have hu_div_mod : (u / M) % N = u / M := Nat.mod_eq_of_lt hu_div_lt
        exact congrArg₂ mat (Fin.ext (by simp [hdiv, hdiv_mod, hu_div_mod])) (Fin.ext hmod.symm)

/-- **Uniform Matrix Transpose (`bmTransposeMatrix`)**:
Consumes `encPair encUnary (encList (encList encElem)) (k, (List.finRange N).map (fun i => (List.finRange (2^k)).map (fun j => mat i j)))`
on `kIO` (`N ≥ 1`) and transposes the $N \times 2^k$ matrix into the $2^k \times N$ matrix
`encList (encList encElem) ((List.finRange (2^k)).map (fun j => (List.finRange N).map (fun i => mat i j)))`
in $O((k + 1) \cdot 2^k \cdot N \cdot L)$ `TM2.step` transitions via `bmFlattenBits` followed by `bmNaturalSplitPasses`. -/
def bmTransposeMatrix : BitMachine :=
  bmSeq (bmMapSnd bmFlattenBits) bmNaturalSplitPasses

theorem bmTransposeMatrix_computesInTime {α : Type} (encElem : α → List Bool)
    (k N : ℕ) (hN : 1 ≤ N) (mat : Fin N → Fin (2 ^ k) → α)
    (L : ℕ) (hL : ∀ i j, (encElem (mat i j)).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (k + 1) * (1500 * (2 ^ k * N) * (L + 2)),
      bmTransposeMatrix.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encList (encList encElem))
            (k, (List.finRange N).map (fun i => (List.finRange (2 ^ k)).map (fun j => mat i j)))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList encElem)
            ((List.finRange (2 ^ k)).map (fun j => (List.finRange N).map (fun i => mat i j)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let f : ℕ → α := fun u =>
    mat ⟨(u / 2 ^ k) % N, Nat.mod_lt _ hN⟩ ⟨u % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  have hflat :
      ((List.finRange N).map (fun i => (List.finRange (2 ^ k)).map (fun j => mat i j))).flatten =
        (List.range (2 ^ k * N)).map f := by
    rw [Nat.mul_comm (2 ^ k) N]
    exact flatten_matrix_eq_map_range mat hN (Nat.two_pow_pos k)
  have p1 := StageEval.congr_out
    (v2 := fun _ : S => encPair encUnary (encList encElem) (k, (List.range (2 ^ k * N)).map f))
    (StageEval.mapSnd (u1 := fun _ : S => encUnary k)
      (StageEval.flattenList (fun _ => encElem)
        (fun _ => (List.finRange N).map (fun i => (List.finRange (2 ^ k)).map (fun j => mat i j)))))
    (fun _ => by dsimp only [encDepPair, encPair]; rw [hflat])
  have p2 := StageEval.congr_out
    (v2 := fun _ : S => encList (encList encElem)
      ((List.finRange (2 ^ k)).map (fun j => (List.finRange N).map (fun i => mat i j))))
    (StageEval.const (S := S) (bmNaturalSplitPasses_computesInTime encElem k N hN f L
      (fun u _ => hL _ _)))
    (fun _ => by
      congr 1
      refine (map_finRange_eq_map_range_of_eq
        (fun j : Fin (2 ^ k) => (List.finRange N).map (fun i => mat i j))
        (fun j1 => (List.range N).map (fun j2 => f (j1 + 2 ^ k * j2)))
        (fun j => ?_)).symm
      refine map_finRange_eq_map_range_of_eq (fun i => mat i j)
        (fun j2 => f (j.val + 2 ^ k * j2)) (fun i => ?_)
      dsimp only [f]
      have hdiv : (j.val + 2 ^ k * i.val) / 2 ^ k = i.val := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt j.isLt, Nat.zero_add]
      have hmod1 : ((j.val + 2 ^ k * i.val) / 2 ^ k) % N = i.val := by
        rw [hdiv, Nat.mod_eq_of_lt i.isLt]
      have hmod2 : (j.val + 2 ^ k * i.val) % 2 ^ k = j.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
      exact congrArg₂ mat (Fin.ext (by simp [hmod1])) (Fin.ext hmod2.symm))
  rcases (StageEval.seq p1 p2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair, id] at ht hcomp
  have hlen_mat :
      (encList (encList encElem)
        ((List.finRange N).map (fun i => (List.finRange (2 ^ k)).map (fun j => mat i j)))).length ≤
      N * (2 * (2 ^ k * (2 * L + 2)) + 2) := by
    have h := length_encList_le_of_forall_le (encList encElem) (2 ^ k * (2 * L + 2))
      ((List.finRange N).map (fun i => (List.finRange (2 ^ k)).map (fun j => mat i j)))
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨i, _, rfl⟩
        have hr := length_encList_le_of_forall_le encElem L
          ((List.finRange (2 ^ k)).map (fun j => mat i j))
          (fun x hx => by
            rcases List.mem_map.mp hx with ⟨j, _, rfl⟩
            exact hL i j)
        simpa [List.length_map, List.length_finRange] using hr)
    simpa [List.length_map, List.length_finRange] using h
  have hlen_flat :
      (encList encElem
        ((List.finRange N).map (fun i => (List.finRange (2 ^ k)).map (fun j => mat i j))).flatten).length ≤
      (2 ^ k * N) * (2 * L + 2) := by
    rw [hflat]
    have h := length_encList_le_of_forall_le encElem L ((List.range (2 ^ k * N)).map f)
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
        exact hL _ _)
    simpa [List.length_map, List.length_range] using h
  have h2k_pos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
  simp only [length_encUnary] at ht
  refine ⟨t, ?_, hcomp⟩
  have hmat_bound :
      N * (2 * (2 ^ k * (2 * L + 2)) + 2) ≤ 6 * (2 ^ k * N) * (L + 2) := by
    have h1 : 2 ≤ 2 * 2 ^ k := by omega
    calc N * (2 * (2 ^ k * (2 * L + 2)) + 2)
        ≤ N * (2 * (2 ^ k * (2 * L + 2)) + 2 * 2 ^ k) :=
          Nat.mul_le_mul_left N (Nat.add_le_add_left h1 _)
      _ = 2 * (2 ^ k * N) * (2 * L + 3) := by ring
      _ ≤ 6 * (2 ^ k * N) * (L + 2) := by
          have : 2 * (2 * L + 3) ≤ 6 * (L + 2) := by omega
          calc 2 * (2 ^ k * N) * (2 * L + 3)
              = (2 ^ k * N) * (2 * (2 * L + 3)) := by ring
            _ ≤ (2 ^ k * N) * (6 * (L + 2)) := Nat.mul_le_mul_left _ this
            _ = 6 * (2 ^ k * N) * (L + 2) := by ring
  have hk_bound : k ≤ (k + 1) * ((2 ^ k * N) * (L + 2)) := by
    have : 1 ≤ (2 ^ k * N) * (L + 2) := Nat.mul_pos (Nat.mul_pos h2k_pos hN) (by omega)
    calc k ≤ k + 1 := Nat.le_succ k
      _ ≤ (k + 1) * ((2 ^ k * N) * (L + 2)) := Nat.le_mul_of_pos_right _ this
  have hterm_le : (2 ^ k * N) * (L + 2) ≤ (k + 1) * ((2 ^ k * N) * (L + 2)) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  nlinarith

/-- **Step 1 Input Gather & Rescale (`bmOddStrideGather`)**:
Consumes `encPair (encPair encUnary (encPair encUnary (encPair encUnary encUnary))) (encList (encComplex W_in)) ((k1, (W_out, (q_in, q_out))), (List.finRange (2^K)).map xFixed)`
on `kIO` and emits
`encList (encList (encComplex W_out)) ((List.finRange (t1Ell K)).map (fun j1 => (List.finRange (rEll K)).map (fun j2 => FixedComplex.rescale q_out (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K) xFixed j1 j2))))`
in $O((k_{1,\ell} + 1) \cdot 2^K \cdot (W_{\text{in}} + W_{\text{out}} + q_{\text{in}} + q_{\text{out}}))$ `TM2.step` transitions. -/
def bmOddStrideGather : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq bmFst bmFst)
      (bmSeq (bmMapFst bmSnd) (bmMapWithCtx bmComplexRescale)))
    bmNaturalSplitPasses

theorem bmOddStrideGather_computesInTime (K W_in W_out q_in q_out : ℕ)
    (xFixed : Fin (2 ^ K) → FixedComplex q_in)
    (hx_in : ∀ j, WordWidthBounds W_in (xFixed j))
    (hx_out : ∀ j, WordWidthBounds W_out (FixedComplex.rescale q_out (xFixed j)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (k1Ell K + 1) *
          (60000 * 2 ^ K * (W_in + W_out + q_in + q_out + 4)),
      bmOddStrideGather.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
            (encList (encComplex W_in))
            ((k1Ell K, (W_out, (q_in, q_out))), (List.finRange (2 ^ K)).map xFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encComplex W_out))
            ((List.finRange (t1Ell K)).map (fun j1 =>
              (List.finRange (rEll K)).map (fun j2 =>
                FixedComplex.rescale q_out
                  (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K) xFixed j1 j2))))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let k1 := k1Ell K
  let t1 := t1Ell K
  let r := rEll K
  let rsCtx := encPair encUnary (encPair encUnary encUnary) (W_out, (q_in, q_out))
  let u1 : S → List Bool := fun _ => encPair encUnary (fun _ => rsCtx) (k1, ())
  let u2 : S → List Bool := fun _ => encList (encComplex W_in) ((List.finRange (2 ^ K)).map xFixed)
  let uIn : S → List Bool := encDepPair u1 u2
  have pK1 : StageEval (S := S) (bmSeq bmFst bmFst) uIn (fun _ => encUnary k1)
      (fun s => 20 * (uIn s).length + 100) := by
    refine (StageEval.seq (StageEval.fst u1 u2)
      (StageEval.fst (fun _ : S => encUnary k1) (fun _ => rsCtx))).mono (fun _ => ?_)
    dsimp only [uIn, u1, encDepPair]
    simp only [length_encPair, List.length_append, length_encodeDelimWord]
    omega
  let SubS := { p : S × FixedComplex q_in // p.2 ∈ (List.finRange (2 ^ K)).map xFixed }
  have pRescaleElem : StageEval (S := SubS) bmComplexRescale
      (encDepPair (fun _ => rsCtx) (fun p => encComplex W_in p.val.2))
      (fun p => encComplex W_out (FixedComplex.rescale q_out p.val.2))
      (fun _ => 16000 * W_in + 3000 * W_out + 30000 * q_in + 30000 * q_out + 65000) := by
    intro ⟨⟨_, z⟩, hzMem⟩ u2' u3' u4' u5' uS'
    rcases List.mem_map.mp hzMem with ⟨j, _, rfl⟩
    exact bmComplexRescale_computesInTime W_in W_out q_in q_out (xFixed j) (hx_in j) (hx_out j)
      u2' u3' u4' u5' uS'
  have pMapRescale := StageEval.seq
    (StageEval.mapFst (u2 := u2)
      (StageEval.snd (fun _ : S => encUnary k1) (fun _ => rsCtx)))
    (StageEval.mapWithCtx_uniform
      (ctx := fun _ : S => rsCtx)
      (xs := fun _ => (List.finRange (2 ^ K)).map xFixed)
      (encA := fun _ => encComplex W_in)
      (encB := fun _ => encComplex W_out)
      (fn := fun _ z => FixedComplex.rescale q_out z)
      (B := fun _ => 16000 * W_in + 3000 * W_out + 30000 * q_in + 30000 * q_out + 65000)
      (L_A := fun _ => 4 * W_in + 8)
      (L_B := fun _ => 4 * W_out + 8)
      pRescaleElem
      (fun _ z _ => by simp)
      (fun _ z _ => by simp))
  let f : ℕ → FixedComplex q_out := fun j =>
    FixedComplex.rescale q_out (xFixed ⟨j % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩)
  have hmap_eq :
      ((List.finRange (2 ^ K)).map xFixed).map (FixedComplex.rescale q_out) =
        (List.range (2 ^ k1 * r)).map f := by
    rw [List.map_map, show 2 ^ k1 * r = 2 ^ K from t1Ell_mul_rEll K]
    refine map_finRange_eq_map_range_of_eq (fun j => FixedComplex.rescale q_out (xFixed j)) f (fun j => ?_)
    dsimp [f]
    congr 2
    exact Fin.ext (Nat.mod_eq_of_lt j.isLt).symm
  have pPass := StageEval.congr_out
    (v2 := fun _ : S => encList (encList (encComplex W_out))
      ((List.finRange t1).map (fun j1 =>
        (List.finRange r).map (fun j2 =>
          FixedComplex.rescale q_out
            (oddStrideGather t1 r (Nat.two_pow_pos K) xFixed j1 j2)))))
    (StageEval.const (S := S)
      (bmNaturalSplitPasses_computesInTime (encComplex W_out) k1 r (rEll_pos K) f (4 * W_out + 8)
        (fun _ _ => by simp)))
    (fun _ => by
      congr 1
      refine (map_finRange_eq_map_range_of_eq
        (fun j1 : Fin t1 => (List.finRange r).map (fun j2 =>
          FixedComplex.rescale q_out
            (oddStrideGather t1 r (Nat.two_pow_pos K) xFixed j1 j2)))
        (fun j1 => (List.range r).map (fun j2 => f (j1 + 2 ^ k1 * j2)))
        (fun j1 => ?_)).symm
      refine map_finRange_eq_map_range_of_eq _ _ (fun j2 => ?_)
      dsimp [f, oddStrideGather, strideModIndex, t1, k1]
      congr 2
      exact Fin.ext (by simp [t1Ell, Nat.mul_comm]))
  have p12 := StageEval.congr_out
    (v2 := fun _ : S => encPair encUnary (encList (encComplex W_out))
      (k1, (List.range (2 ^ k1 * r)).map f))
    (StageEval.fanout pK1 pMapRescale)
    (fun _ => by dsimp only [encDepPair, encPair]; rw [hmap_eq])
  rcases (StageEval.seq p12 pPass) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2, rsCtx, id] at ht hcomp
  have hlen_u2 :
      (encList (encComplex W_in) ((List.finRange (2 ^ K)).map xFixed)).length ≤
      2 ^ K * (2 * (4 * W_in + 8) + 2) := by
    have h := length_encList_le_of_forall_le (encComplex W_in) (4 * W_in + 8)
      ((List.finRange (2 ^ K)).map xFixed) (fun _ _ => by simp)
    simpa [List.length_map, List.length_finRange] using h
  have hlen_out :
      (encList (encComplex W_out)
        (List.map (fun z => FixedComplex.rescale q_out z)
          ((List.finRange (2 ^ K)).map xFixed))).length ≤
      2 ^ K * (2 * (4 * W_out + 8) + 2) := by
    have h := length_encList_le_of_forall_le (encComplex W_out) (4 * W_out + 8)
      (List.map (fun z => FixedComplex.rescale q_out z)
        ((List.finRange (2 ^ K)).map xFixed)) (fun _ _ => by simp)
    simpa [List.length_map, List.length_finRange] using h
  have hk1_le : k1 ≤ 2 ^ K := by
    unfold k1 k1Ell
    exact le_trans (Nat.div_le_self K 2) (le_of_lt (Nat.lt_two_pow_self))
  have ht1r : 2 ^ k1 * r = 2 ^ K := t1Ell_mul_rEll K
  rw [ht1r] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, List.length_map,
    List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  have h2K_pos : 1 ≤ 2 ^ K := Nat.two_pow_pos K
  have hpart2 :
      (k1 + 1) * (1000 * 2 ^ K * (4 * W_out + 8 + 2)) ≤
      (k1 + 1) * (10000 * 2 ^ K * (W_in + W_out + q_in + q_out + 4)) := by
    refine Nat.mul_le_mul_left (k1 + 1) ?_
    nlinarith
  have hterm_le :
      50000 * 2 ^ K * (W_in + W_out + q_in + q_out + 4) ≤
      (k1 + 1) * (50000 * 2 ^ K * (W_in + W_out + q_in + q_out + 4)) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos k1)
  nlinarith

/-- **Step 3 Frequency Scatter & Rescale (`bmFreqScatter`)**:
Consumes `encPair (encPair encUnary (encPair encUnary encUnary)) (encList (encList (encComplex W_in))) ((W_out, (q_in, q_out)), (List.finRange (t1Ell K)).map (fun u1 => (List.finRange (rEll K)).map (fun u2 => Z_mat u1 u2)))`
on `kIO` and emits
`encList (encComplex W_out) ((List.finRange (2^K)).map (fun u => FixedComplex.rescale q_out (freqScatter (t1Ell K) (rEll K) (t1Ell_mul_rEll K).symm Z_mat u)))`
in $O(2^K \cdot (W_{\text{in}} + W_{\text{out}} + q_{\text{in}} + q_{\text{out}}))$ `TM2.step` transitions. -/
def bmFreqScatter : BitMachine :=
  bmSeq (bmMapSnd bmFlattenBits) (bmMapWithCtx bmComplexRescale)

theorem bmFreqScatter_computesInTime (K W_in W_out q_in q_out : ℕ)
    (Z_mat : Fin (t1Ell K) → Fin (rEll K) → FixedComplex q_in)
    (hZ_in : ∀ u1 u2, WordWidthBounds W_in (Z_mat u1 u2))
    (hZ_out : ∀ u1 u2, WordWidthBounds W_out (FixedComplex.rescale q_out (Z_mat u1 u2)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 60000 * 2 ^ K * (W_in + W_out + q_in + q_out + 4),
      bmFreqScatter.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary (encPair encUnary encUnary))
            (encList (encList (encComplex W_in)))
            ((W_out, (q_in, q_out)),
              (List.finRange (t1Ell K)).map (fun u1 =>
                (List.finRange (rEll K)).map (fun u2 => Z_mat u1 u2)))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W_out)
            ((List.finRange (2 ^ K)).map (fun u =>
              FixedComplex.rescale q_out
                (freqScatter (t1Ell K) (rEll K) (t1Ell_mul_rEll K).symm Z_mat u)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let t1 := t1Ell K
  let r := rEll K
  let rsCtx := encPair encUnary (encPair encUnary encUnary) (W_out, (q_in, q_out))
  have hflat :
      ((List.finRange t1).map (fun u1 => (List.finRange r).map (fun u2 => Z_mat u1 u2))).flatten =
        (List.finRange (2 ^ K)).map (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat) := by
    rw [flatten_matrix_eq_map_range Z_mat (t1Ell_pos K) (rEll_pos K)]
    refine Eq.trans (congrArg (List.map _) (congrArg List.range (t1Ell_mul_rEll K))) ?_
    refine (map_finRange_eq_map_range_of_eq
      (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat) _ (fun u => ?_)).symm
    unfold freqScatter
    dsimp only
    have hu1 : u.val / r < t1 := by
      rw [Nat.div_lt_iff_lt_mul (rEll_pos K), show t1 * r = 2 ^ K from t1Ell_mul_rEll K]
      exact u.isLt
    exact congrArg₂ Z_mat (Fin.ext (Nat.mod_eq_of_lt hu1).symm) rfl
  have p1 := StageEval.congr_out
    (v2 := encDepPair (fun _ : S => rsCtx)
      (fun _ => encList (encComplex W_in)
        ((List.finRange (2 ^ K)).map (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat))))
    (StageEval.mapSnd (u1 := fun _ : S => rsCtx)
      (StageEval.flattenList (fun _ => encComplex W_in)
        (fun _ => (List.finRange t1).map (fun u1 =>
          (List.finRange r).map (fun u2 => Z_mat u1 u2)))))
    (fun _ => by dsimp only [encDepPair]; rw [hflat])
  let SubS := { p : S × FixedComplex q_in //
    p.2 ∈ (List.finRange (2 ^ K)).map (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat) }
  have pRescaleElem : StageEval (S := SubS) bmComplexRescale
      (encDepPair (fun _ => rsCtx) (fun p => encComplex W_in p.val.2))
      (fun p => encComplex W_out (FixedComplex.rescale q_out p.val.2))
      (fun _ => 16000 * W_in + 3000 * W_out + 30000 * q_in + 30000 * q_out + 65000) := by
    intro ⟨⟨_, z⟩, hzMem⟩ u2' u3' u4' u5' uS'
    rcases List.mem_map.mp hzMem with ⟨u, _, rfl⟩
    unfold freqScatter
    exact bmComplexRescale_computesInTime W_in W_out q_in q_out _ (hZ_in _ _) (hZ_out _ _)
      u2' u3' u4' u5' uS'
  have p2 := StageEval.congr_out
    (v2 := fun _ : S => encList (encComplex W_out)
      ((List.finRange (2 ^ K)).map (fun u =>
        FixedComplex.rescale q_out
          (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat u))))
    (StageEval.mapWithCtx_uniform
      (ctx := fun _ : S => rsCtx)
      (xs := fun _ => (List.finRange (2 ^ K)).map (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat))
      (encA := fun _ => encComplex W_in)
      (encB := fun _ => encComplex W_out)
      (fn := fun _ z => FixedComplex.rescale q_out z)
      (B := fun _ => 16000 * W_in + 3000 * W_out + 30000 * q_in + 30000 * q_out + 65000)
      (L_A := fun _ => 4 * W_in + 8)
      (L_B := fun _ => 4 * W_out + 8)
      pRescaleElem
      (fun _ _ _ => by simp)
      (fun _ _ _ => by simp))
    (fun _ => by rw [List.map_map]; rfl)
  rcases (StageEval.seq p1 p2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [rsCtx, id] at ht hcomp
  have hlen_mat :
      (encList (encList (encComplex W_in))
        ((List.finRange t1).map (fun u1 => (List.finRange r).map (fun u2 => Z_mat u1 u2)))).length ≤
      t1 * (2 * (r * (2 * (4 * W_in + 8) + 2)) + 2) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W_in))
      (r * (2 * (4 * W_in + 8) + 2))
      ((List.finRange t1).map (fun u1 => (List.finRange r).map (fun u2 => Z_mat u1 u2)))
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨u1, _, rfl⟩
        have hr := length_encList_le_of_forall_le (encComplex W_in) (4 * W_in + 8)
          ((List.finRange r).map (fun u2 => Z_mat u1 u2)) (fun _ _ => by simp)
        simpa [List.length_map, List.length_finRange] using hr)
    simpa [List.length_map, List.length_finRange] using h
  have hlen_flat :
      (encList (encComplex W_in)
        ((List.finRange t1).map (fun u1 => (List.finRange r).map (fun u2 => Z_mat u1 u2))).flatten).length ≤
      2 ^ K * (2 * (4 * W_in + 8) + 2) := by
    rw [hflat]
    have h := length_encList_le_of_forall_le (encComplex W_in) (4 * W_in + 8)
      ((List.finRange (2 ^ K)).map (freqScatter t1 r (t1Ell_mul_rEll K).symm Z_mat))
      (fun _ _ => by simp)
    simpa [List.length_map, List.length_finRange] using h
  have ht1r : t1 * r = 2 ^ K := t1Ell_mul_rEll K
  have hmat_le : t1 * (2 * (r * (2 * (4 * W_in + 8) + 2)) + 2) ≤ 2 ^ K * (16 * W_in + 38) := by
    have hr_pos : 1 ≤ r := rEll_pos K
    calc t1 * (2 * (r * (2 * (4 * W_in + 8) + 2)) + 2)
        ≤ t1 * (2 * (r * (2 * (4 * W_in + 8) + 2)) + 2 * r) :=
          Nat.mul_le_mul_left t1 (Nat.add_le_add_left (by omega) _)
      _ = (t1 * r) * (16 * W_in + 38) := by ring
      _ = 2 ^ K * (16 * W_in + 38) := by rw [ht1r]
  have h2K_pos : 1 ≤ 2 ^ K := Nat.two_pow_pos K
  simp only [length_encPair, length_encUnary, List.length_map, List.length_finRange] at ht
  refine ⟨t, ?_, hcomp⟩
  nlinarith

/-! ### Deinterleaved Alternating Sum & `bmNyquistModeSum` -/

theorem sum_even_sub_odd_eq_sum_altSign (M : ℕ) (f : ℕ → ℤ) :
    (∑ m ∈ Finset.range M, (f (2 * m) - f (2 * m + 1))) =
      ∑ j ∈ Finset.range (2 * M), altSign j * f j := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h2 : 2 * (M + 1) = (2 * M) + 1 + 1 := by omega
    rw [Finset.sum_range_succ, ih, h2, Finset.sum_range_succ, Finset.sum_range_succ]
    have hev : altSign (2 * M) = 1 := by
      unfold altSign
      simp
    have hod : altSign (2 * M + 1) = -1 := by
      unfold altSign
      rw [Nat.add_mod]
      simp
    rw [hev, hod]
    ring

/-- Sum a list of `FixedComplex q` words at width `W` starting from `0`:
`(encUnary W, encList (encComplex W) xs) ↦ encComplex W (∑ x ∈ xs)`. -/
def bmSumComplexList : BitMachine :=
  bmSeq (bmPairMap bmComplexZero bmId)
    (bmSeq bmSwap (bmFoldList bmComplexAdd))

theorem StageEval.sumComplexList_stage {S : Type} {q : ℕ} (W M : S → ℕ)
    (g : S → ℕ → FixedComplex q)
    (hg : ∀ (s : S) (m : ℕ), m < M s → WordWidthBounds (W s) (g s m))
    (hpart : ∀ (s : S) (i : ℕ), i ≤ M s →
      WordWidthBounds (W s)
        (⟨∑ m ∈ Finset.range i, (g s m).re, ∑ m ∈ Finset.range i, (g s m).im⟩ : FixedComplex q)) :
    StageEval bmSumComplexList
      (encDepPair (fun s => encUnary (W s))
        (fun s => encList (encComplex (W s)) ((List.range (M s)).map (g s))))
      (fun s => encComplex (W s)
        (⟨∑ m ∈ Finset.range (M s), (g s m).re, ∑ m ∈ Finset.range (M s), (g s m).im⟩ :
          FixedComplex q))
      (fun s => (M s) * (2000 * W s + 5000) + 100 * W s + 300) := by
  let uAcc : S → ℕ → List Bool := fun s i =>
    encComplex (W s)
      (⟨∑ m ∈ Finset.range i, (g s m).re, ∑ m ∈ Finset.range i, (g s m).im⟩ : FixedComplex q)
  have pZero : StageEval bmComplexZero (fun s : S => encUnary (W s))
      (fun s => uAcc s 0) (fun s => 30 * W s + 80) := by
    intro s tW2 tW3 tW4 tW5 tSch
    exact bmComplexZero_computesInTime (W s) q tW2 tW3 tW4 tW5 tSch
  have p1 := StageEval.pairMap pZero
    (StageEval.id_stage (fun s : S => encList (encComplex (W s)) ((List.range (M s)).map (g s))))
  have p2 := StageEval.swap (fun s : S => uAcc s 0)
    (fun s : S => encList (encComplex (W s)) ((List.range (M s)).map (g s)))
  let SubS := { p : S × ℕ // p.2 < ((List.range (M p.1)).map (g p.1)).length }
  have pStep : StageEval (S := SubS) bmComplexAdd
      (encDepPair
        (fun p => encComplex (W p.val.1) (((List.range (M p.val.1)).map (g p.val.1))[p.val.2]'p.property))
        (fun p => uAcc p.val.1 p.val.2))
      (fun p => uAcc p.val.1 (p.val.2 + 1))
      (fun p => 1800 * W p.val.1 + 4500) := by
    intro ⟨⟨s, i⟩, hi⟩ tW2 tW3 tW4 tW5 tSch
    have hiM : i < M s := by simpa using hi
    have hget : ((List.range (M s)).map (g s))[i]'hi = g s i := by simp
    have hnext :
        (⟨∑ m ∈ Finset.range (i + 1), (g s m).re,
          ∑ m ∈ Finset.range (i + 1), (g s m).im⟩ : FixedComplex q) =
        (g s i).add ⟨∑ m ∈ Finset.range i, (g s m).re, ∑ m ∈ Finset.range i, (g s m).im⟩ := by
      ext <;> simp [Finset.sum_range_succ, FixedComplex.add, add_comm]
    dsimp only [uAcc, encDepPair, id]
    rw [hget, hnext]
    exact bmComplexAdd_computesInTime (W s) (g s i)
      ⟨∑ m ∈ Finset.range i, (g s m).re, ∑ m ∈ Finset.range i, (g s m).im⟩
      (hg s i hiM) (hpart s i (le_of_lt hiM)) (hnext ▸ hpart s (i + 1) hiM)
      tW2 tW3 tW4 tW5 tSch
  have p3 := StageEval.congr_out
    (v2 := fun s : S => uAcc s (M s))
    (StageEval.foldList_idx
      (encElem := fun s => encComplex (W s))
      (xs := fun s => (List.range (M s)).map (g s))
      (uAcc := uAcc)
      (B := fun s => 1800 * W s + 4500)
      (L_elem := fun s => 4 * W s + 8)
      (L_acc := fun s => 4 * W s + 8)
      pStep
      (fun s i _ => by simp)
      (fun s i _ => by simp [uAcc]))
    (fun s => by simp [uAcc])
  refine (StageEval.seq p1 (StageEval.seq p2 p3)).mono (fun s => ?_)
  dsimp only [uAcc]
  have hlen :
      (encList (encComplex (W s)) ((List.range (M s)).map (g s))).length ≤
      (M s) * (2 * (4 * W s + 8) + 2) := by
    have h := length_encList_le_of_forall_le (encComplex (W s)) (4 * W s + 8)
      ((List.range (M s)).map (g s)) (fun _ _ => by simp)
    simpa [List.length_map, List.length_range] using h
  simp only [length_encUnary, length_encComplex, List.length_map, List.length_range]
  nlinarith

/-- Elementwise complex subtraction of two equal-length lists at width `W`:
`(encList (encComplex W) xs, encList (encComplex W) ys) ↦ encList (encComplex W) (List.zipWith FixedComplex.sub xs ys)`. -/
def bmDiffComplexLists : BitMachine :=
  bmSeq bmZipList
    (bmSeq (bmFanout bmConstEmpty bmId)
      (bmMapWithCtx (bmSeq bmSnd bmComplexSub)))

theorem zip_map_range_eq {α β : Type} (M : ℕ) (f : ℕ → α) (g : ℕ → β) :
    List.zip ((List.range M).map f) ((List.range M).map g) =
      (List.range M).map (fun m => (f m, g m)) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
      List.zip_append (by simp), ih, List.map_append, List.map_singleton]
    rfl

theorem StageEval.diffComplexLists_stage {S : Type} {q : ℕ} (W M : S → ℕ)
    (fE fO : S → ℕ → FixedComplex q)
    (hE : ∀ (s : S) (m : ℕ), m < M s → WordWidthBounds (W s) (fE s m))
    (hO : ∀ (s : S) (m : ℕ), m < M s → WordWidthBounds (W s) (fO s m))
    (hsub : ∀ (s : S) (m : ℕ), m < M s → WordWidthBounds (W s) ((fE s m).sub (fO s m))) :
    StageEval bmDiffComplexLists
      (encDepPair
        (fun s => encList (encComplex (W s)) ((List.range (M s)).map (fE s)))
        (fun s => encList (encComplex (W s)) ((List.range (M s)).map (fO s))))
      (fun s => encList (encComplex (W s))
        ((List.range (M s)).map (fun m => (fE s m).sub (fO s m))))
      (fun s => (M s) * (4000 * W s + 10000) + 500) := by
  have pZip := StageEval.congr_out
    (v2 := fun s : S => encList (encPair (encComplex (W s)) (encComplex (W s)))
      ((List.range (M s)).map (fun m => (fE s m, fO s m))))
    (StageEval.zipList (fun s => encComplex (W s)) (fun s => encComplex (W s))
      (fun s => (List.range (M s)).map (fE s))
      (fun s => (List.range (M s)).map (fO s))
      (fun s => by simp))
    (fun s => by rw [zip_map_range_eq])
  have pInit := StageEval.fanout
    (StageEval.constEmpty (fun s : S =>
      encList (encPair (encComplex (W s)) (encComplex (W s)))
        ((List.range (M s)).map (fun m => (fE s m, fO s m)))))
    (StageEval.id_stage (fun s : S =>
      encList (encPair (encComplex (W s)) (encComplex (W s)))
        ((List.range (M s)).map (fun m => (fE s m, fO s m)))))
  let SubS := { p : S × (FixedComplex q × FixedComplex q) //
    p.2 ∈ (List.range (M p.1)).map (fun m => (fE p.1 m, fO p.1 m)) }
  have pSubBody : StageEval (S := SubS) (bmSeq bmSnd bmComplexSub)
      (encDepPair (fun _ => [])
        (fun p => encPair (encComplex (W p.val.1)) (encComplex (W p.val.1)) p.val.2))
      (fun p => encComplex (W p.val.1) (p.val.2.1.sub p.val.2.2))
      (fun p => 1900 * W p.val.1 + 4800) := by
    have b1 := StageEval.snd (fun _ : SubS => ([] : List Bool))
      (fun p => encPair (encComplex (W p.val.1)) (encComplex (W p.val.1)) p.val.2)
    have b2 : StageEval (S := SubS) bmComplexSub
        (fun p => encPair (encComplex (W p.val.1)) (encComplex (W p.val.1)) p.val.2)
        (fun p => encComplex (W p.val.1) (p.val.2.1.sub p.val.2.2))
        (fun p => 1800 * W p.val.1 + 4500) := by
      intro ⟨⟨s, pair⟩, hmem⟩ tW2 tW3 tW4 tW5 tSch
      dsimp only [id] at hmem ⊢
      rcases List.mem_map.mp hmem with ⟨m, hm, hpair⟩
      rw [← hpair]
      have hm_lt : m < M s := List.mem_range.mp hm
      exact bmComplexSub_computesInTime (W s) (fE s m) (fO s m)
        (hE s m hm_lt) (hO s m hm_lt) (hsub s m hm_lt) tW2 tW3 tW4 tW5 tSch
    refine (StageEval.seq b1 b2).mono (fun p => ?_)
    simp only [List.length_nil, length_encPair, length_encComplex]
    omega
  have pMap := StageEval.congr_out
    (v2 := fun s : S => encList (encComplex (W s))
      ((List.range (M s)).map (fun m => (fE s m).sub (fO s m))))
    (StageEval.mapWithCtx_uniform
      (ctx := fun _ : S => ([] : List Bool))
      (xs := fun s => (List.range (M s)).map (fun m => (fE s m, fO s m)))
      (encA := fun s => encPair (encComplex (W s)) (encComplex (W s)))
      (encB := fun s => encComplex (W s))
      (fn := fun _ p => p.1.sub p.2)
      (B := fun s => 1900 * W s + 4800)
      (L_A := fun s => 16 * W s + 36)
      (L_B := fun s => 4 * W s + 8)
      pSubBody
      (fun _ _ _ => by simp only [length_encPair, length_encComplex]; omega)
      (fun _ _ _ => by simp))
    (fun _ => by rw [List.map_map]; rfl)
  refine (StageEval.seq pZip (StageEval.seq pInit pMap)).mono (fun s => ?_)
  have hlen1 :
      (encList (encComplex (W s)) ((List.range (M s)).map (fE s))).length ≤
      (M s) * (2 * (4 * W s + 8) + 2) := by
    have h := length_encList_le_of_forall_le (encComplex (W s)) (4 * W s + 8)
      ((List.range (M s)).map (fE s)) (fun _ _ => by simp)
    simpa [List.length_map, List.length_range] using h
  have hlen2 :
      (encList (encComplex (W s)) ((List.range (M s)).map (fO s))).length ≤
      (M s) * (2 * (4 * W s + 8) + 2) := by
    have h := length_encList_le_of_forall_le (encComplex (W s)) (4 * W s + 8)
      ((List.range (M s)).map (fO s)) (fun _ _ => by simp)
    simpa [List.length_map, List.length_range] using h
  have hlenZ :
      (encList (encPair (encComplex (W s)) (encComplex (W s)))
        ((List.range (M s)).map (fun m => (fE s m, fO s m)))).length ≤
      (M s) * (2 * (16 * W s + 36) + 2) := by
    have h := length_encList_le_of_forall_le
      (encPair (encComplex (W s)) (encComplex (W s))) (16 * W s + 36)
      ((List.range (M s)).map (fun m => (fE s m, fO s m)))
      (fun _ _ => by simp only [length_encPair, length_encComplex]; omega)
    simpa [List.length_map, List.length_range] using h
  simp only [length_encPair, List.length_nil, List.length_map, List.length_range]
  nlinarith

/-- Alternating sum of an even-length complex list `(List.range (2 * M)).map f` at word width `W`:
deinterleaves into even and odd sublists, subtracts elementwise via `bmDiffComplexLists`, and sums via
`bmSumComplexList`. -/
def bmAltSumComplexList : BitMachine :=
  bmSeq (bmPairMap bmId (bmSeq bmDeinterleaveList bmDiffComplexLists)) bmSumComplexList

theorem StageEval.altSumComplexList_stage {S : Type} {q : ℕ} (W M : S → ℕ)
    (f : S → ℕ → FixedComplex q)
    (hf : ∀ (s : S) (j : ℕ), j < 2 * M s → WordWidthBounds (W s - 1) (f s j))
    (hW : ∀ s : S, 1 ≤ W s)
    (hpart : ∀ (s : S) (i : ℕ), i ≤ M s →
      WordWidthBounds (W s)
        (⟨∑ m ∈ Finset.range i, ((f s (2 * m)).re - (f s (2 * m + 1)).re),
          ∑ m ∈ Finset.range i, ((f s (2 * m)).im - (f s (2 * m + 1)).im)⟩ : FixedComplex q)) :
    StageEval bmAltSumComplexList
      (encDepPair (fun s => encUnary (W s))
        (fun s => encList (encComplex (W s)) ((List.range (2 * M s)).map (f s))))
      (fun s => encComplex (W s)
        (⟨∑ j ∈ Finset.range (2 * M s), altSign j * (f s j).re,
          ∑ j ∈ Finset.range (2 * M s), altSign j * (f s j).im⟩ : FixedComplex q))
      (fun s => (M s) * (7000 * W s + 18000) + 200 * W s + 1000) := by
  have hfW : ∀ (s : S) (j : ℕ), j < 2 * M s → WordWidthBounds (W s) (f s j) :=
    fun s j hj => (hf s j hj).mono (Nat.sub_le (W s) 1)
  have hsubW : ∀ (s : S) (m : ℕ), m < M s →
      WordWidthBounds (W s) ((f s (2 * m)).sub (f s (2 * m + 1))) := by
    intro s m hm
    have h1 := hf s (2 * m) (by omega)
    have h2 := hf s (2 * m + 1) (by omega)
    have hsub := h1.sub h2
    rwa [Nat.sub_add_cancel (hW s)] at hsub
  have pDeint : StageEval bmDeinterleaveList
      (fun s : S => encList (encComplex (W s)) ((List.range (2 * M s)).map (f s)))
      (encDepPair
        (fun s => encList (encComplex (W s)) ((List.range (M s)).map (fun m => f s (2 * m))))
        (fun s => encList (encComplex (W s)) ((List.range (M s)).map (fun m => f s (2 * m + 1)))))
      (fun s => 24 * (encList (encComplex (W s)) ((List.range (2 * M s)).map (f s))).length + 55) :=
    StageEval.congr_out
      (v2 := encDepPair
        (fun s => encList (encComplex (W s)) ((List.range (M s)).map (fun m => f s (2 * m))))
        (fun s => encList (encComplex (W s)) ((List.range (M s)).map (fun m => f s (2 * m + 1)))))
      (StageEval.deinterleaveList_stage (fun s => encComplex (W s))
        (fun s => (List.range (2 * M s)).map (f s)))
      (fun s => by simp [encDepPair, deinterleaveList_map_range])
  have pDiff := StageEval.diffComplexLists_stage W M
    (fun s m => f s (2 * m)) (fun s m => f s (2 * m + 1))
    (fun s m hm => hfW s (2 * m) (by omega))
    (fun s m hm => hfW s (2 * m + 1) (by omega))
    hsubW
  have p1 := StageEval.pairMap
    (StageEval.id_stage (fun s : S => encUnary (W s)))
    (StageEval.seq pDeint pDiff)
  have p2 := StageEval.congr_out
    (v2 := fun s : S => encComplex (W s)
      (⟨∑ j ∈ Finset.range (2 * M s), altSign j * (f s j).re,
        ∑ j ∈ Finset.range (2 * M s), altSign j * (f s j).im⟩ : FixedComplex q))
    (StageEval.sumComplexList_stage W M (fun s m => (f s (2 * m)).sub (f s (2 * m + 1)))
      hsubW hpart)
    (fun s => by
      congr 1
      ext
      · exact sum_even_sub_odd_eq_sum_altSign (M s) (fun j => (f s j).re)
      · exact sum_even_sub_odd_eq_sum_altSign (M s) (fun j => (f s j).im))
  refine (StageEval.seq p1 p2).mono (fun s => ?_)
  have hlen :
      (encList (encComplex (W s)) ((List.range (2 * M s)).map (f s))).length ≤
      (M s) * (16 * W s + 36) := by
    have h := length_encList_le_of_forall_le (encComplex (W s)) (4 * W s + 8)
      ((List.range (2 * M s)).map (f s)) (fun _ _ => by simp)
    simp only [List.length_map, List.length_range] at h
    nlinarith
  have hlenD :
      (encList (encComplex (W s))
        ((List.range (M s)).map (fun m => (f s (2 * m)).sub (f s (2 * m + 1))))).length ≤
      (M s) * (8 * W s + 18) := by
    have h := length_encList_le_of_forall_le (encComplex (W s)) (4 * W s + 8)
      ((List.range (M s)).map (fun m => (f s (2 * m)).sub (f s (2 * m + 1))))
      (fun _ _ => by simp)
    simp only [List.length_map, List.length_range] at h
    nlinarith
  simp only [length_encUnary]
  nlinarith

/-- Multiply a fixed-point complex number by $i$: `z = ⟨re, im⟩ ↦ ⟨-im, re⟩`. -/
def bmComplexMulI : BitMachine :=
  bmSeq bmSwap (bmPairMap bmSignedNeg bmId)

theorem bmComplexMulI_computesInTime {q1 q2 : ℕ} (W : ℕ) (z : FixedComplex q1)
    (hz : WordWidthBounds W z) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 800 * W + 2000,
      bmComplexMulI.ComputesInTime
        (mkTapes8 (encodeDelimWord (encComplex W z)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W (⟨-z.im, z.re⟩ : FixedComplex q2)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.swap
    (fun _ : S => encodeSignedWord W z.re)
    (fun _ : S => encodeSignedWord W z.im)
  have p2 := StageEval.pairMap
    (StageEval.const (S := S) (bmSignedNeg_computesInTime W z.im hz.2))
    (StageEval.id_stage (fun _ : S => encodeSignedWord W z.re))
  rcases (StageEval.seq p1 p2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair] at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Extract the head element `x` from a non-empty encoded list `encList encElem (x :: xs)` on `kIO`
using `bmFst`. -/
theorem bmFst_encList_cons_computesInTime {α : Type} (encElem : α → List Bool)
    (x : α) (xs : List α) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * (encElem x).length + (encList encElem xs).length + 6,
      bmFst.ComputesInTime
        (mkTapes8 (encodeDelimWord (encList encElem (x :: xs))) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encElem x)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  rw [encList_cons]
  have f1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encElem x) ++ encList encElem xs) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at f1
  have f2 := tmDropWord_computesInTime kIO (encList encElem xs) []
    (mkTapes8 [] (encodeDelimWord (encElem x).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil] at f2
  have f3 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encElem x).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at f3
  refine ⟨_, ?_, f1.seq (f2.seq f3)⟩
  omega

/-- Sub-stage 1 of `bmNyquistModeSum`: extracts `(k1, xs)` and runs `bmNaturalSplitPasses`. -/
def bmNyqMat : BitMachine :=
  bmSeq (bmFanout (bmSeq bmFst bmFst) bmSnd) bmNaturalSplitPasses

/-- Sub-stage 2 of `bmNyquistModeSum`: drops `t1 / 2` rows and takes the head row. -/
def bmNyqRow : BitMachine :=
  bmSeq (bmFanout (bmSeq (bmSeq bmFst bmSnd) bmFst) bmNyqMat) (bmSeq bmDropList bmFst)

/-- Sub-stage 3 of `bmNyquistModeSum`: resizes row `t1 / 2` to width `W_acc`. -/
def bmNyqWide : BitMachine :=
  bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmFst) bmNyqRow)
    (bmMapWithCtx bmResizeComplex)

/-- Sub-stage 4 of `bmNyquistModeSum`: alternating sum + multiply by $i$ at width `W_acc`. -/
def bmNyqSumI : BitMachine :=
  bmSeq (bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmFst) bmNyqWide)
    bmAltSumComplexList) bmComplexMulI

/-- **Step 3 Nyquist Mode Alternating Sum (`bmNyquistModeSum`)**:
Consumes
`encPair (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))))) (encList (encComplex W_x))`
encoding `((k1Ell K, (t1Ell K / 2, (W_acc, (W_out, (p + 2 + k2Ell K, qChildEll K p))))), (List.finRange (2^K)).map xFixed)`
and emits `encComplex W_out (nyquistModeSumFixed K p xFixed)` in $O((k_1 \cdot 2^K + r) \cdot W + q_{\text{child}})$ `TM2.step` transitions. -/
def bmNyquistModeSum : BitMachine :=
  bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmSnd) bmNyqSumI) bmComplexRescale

theorem bmNyquistModeSum_computesInTime (K p W_x W_acc W_out : ℕ) (hK : 1 ≤ K)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : ∀ j : Fin (2 ^ K), WordWidthBounds W_x (xFixed j))
    (hW_acc : W_x + k2Ell K + 2 ≤ W_acc)
    (hout : WordWidthBounds W_out (nyquistModeSumFixed K p xFixed))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (k1Ell K + 1) * 2 ^ K * (6400 * W_x + 16000) +
          rEll K * (18000 * W_x + 18000 * W_acc + 60000) +
          20000 * W_acc + 6000 * W_out +
          40000 * (p + 2 + k2Ell K) + 40000 * qChildEll K p + 250000,
      bmNyquistModeSum.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary
              (encPair encUnary
                (encPair encUnary
                  (encPair encUnary (encPair encUnary encUnary)))))
            (encList (encComplex W_x))
            ((k1Ell K, (t1Ell K / 2, (W_acc, (W_out, (p + 2 + k2Ell K, qChildEll K p))))),
              (List.finRange (2 ^ K)).map xFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W_out (nyquistModeSumFixed K p xFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let k1 := k1Ell K
  let k2 := k2Ell K
  let t1 := t1Ell K
  let r := rEll K
  let N_split := (k1 + 1) * (2 ^ K)
  have h2K_le_N : 2 ^ K ≤ N_split := Nat.le_mul_of_pos_left (2 ^ K) (Nat.succ_pos k1)
  have h2K_Wx : 2 ^ K * W_x ≤ N_split * W_x := Nat.mul_le_mul_right W_x h2K_le_N
  have hN_pos : 1 ≤ N_split := le_trans (Nat.two_pow_pos K) h2K_le_N
  let q_sum := p + 2 + k2
  let q_out := qChildEll K p
  let rsCtx := encPair encUnary (encPair encUnary encUnary) (W_out, (q_sum, q_out))
  let restCtx := encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
    (t1 / 2, (W_acc, (W_out, (q_sum, q_out))))
  let hdrCtx := encPair encUnary
    (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encUnary))))
    (k1, (t1 / 2, (W_acc, (W_out, (q_sum, q_out)))))
  let uHdr : S → List Bool := fun _ => hdrCtx
  let uXs : S → List Bool := fun _ => encList (encComplex W_x) ((List.finRange (2 ^ K)).map xFixed)
  let L_hdr := 2 * k1 + 4 * (t1 / 2) + 8 * W_acc + 16 * W_out + 32 * q_sum + 32 * q_out + 124
  have hlen_hdr : hdrCtx.length = L_hdr := by
    dsimp only [hdrCtx, restCtx, rsCtx, L_hdr]
    simp only [length_encPair, length_encUnary]
    omega
  have hlen_rest : restCtx.length ≤ L_hdr := by
    dsimp only [hdrCtx, restCtx, rsCtx, L_hdr]
    simp only [length_encPair, length_encUnary]
    omega
  have hlen_wacc_rs :
      (encPair encUnary (encPair encUnary (encPair encUnary encUnary))
        (W_acc, (W_out, (q_sum, q_out)))).length ≤ L_hdr := by
    dsimp only [hdrCtx, restCtx, rsCtx, L_hdr]
    simp only [length_encPair, length_encUnary]
    omega
  have hlen_rs_le : rsCtx.length ≤ L_hdr := by
    dsimp only [hdrCtx, restCtx, rsCtx, L_hdr]
    simp only [length_encPair, length_encUnary]
    omega
  have hk1_le_hdr : k1 ≤ L_hdr := by dsimp [L_hdr]; omega
  have ht1_le_hdr : t1 / 2 ≤ L_hdr := by dsimp [L_hdr]; omega
  have hW_le_hdr : W_acc ≤ L_hdr := by dsimp [L_hdr]; omega
  have hlen_xs :
      (encList (encComplex W_x) ((List.finRange (2 ^ K)).map xFixed)).length ≤
      2 ^ K * (8 * W_x + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W_x) (4 * W_x + 8)
      ((List.finRange (2 ^ K)).map xFixed) (fun _ _ => by simp)
    simp only [List.length_map, List.length_finRange] at h
    exact h.trans (le_of_eq (by ring))
  have pFst := StageEval.fst uHdr uXs
  have pSnd := StageEval.snd uHdr uXs
  have pK1 : StageEval (bmSeq bmFst bmFst) (encDepPair uHdr uXs)
      (fun _ => encUnary k1)
      (fun _ => 6 * L_hdr + 2 * (2 ^ K * (8 * W_x + 18)) + 20) := by
    refine (StageEval.seq pFst
      (StageEval.fst (fun _ : S => encUnary k1) (fun _ : S => restCtx))).mono (fun _ => ?_)
    dsimp only [uHdr, uXs]
    simp only [length_encUnary, hlen_hdr]
    linarith [hlen_xs, hlen_rest, hk1_le_hdr]
  have pRest : StageEval (bmSeq bmFst bmSnd) (encDepPair uHdr uXs)
      (fun _ => restCtx)
      (fun _ => 6 * L_hdr + 2 * (2 ^ K * (8 * W_x + 18)) + 20) := by
    refine (StageEval.seq pFst
      (StageEval.snd (fun _ : S => encUnary k1) (fun _ : S => restCtx))).mono (fun _ => ?_)
    dsimp only [uHdr, uXs]
    simp only [length_encUnary, hlen_hdr]
    linarith [hlen_xs, hlen_rest, hk1_le_hdr]
  have pHalfT1 : StageEval (bmSeq (bmSeq bmFst bmSnd) bmFst) (encDepPair uHdr uXs)
      (fun _ => encUnary (t1 / 2))
      (fun _ => 10 * L_hdr + 2 * (2 ^ K * (8 * W_x + 18)) + 30) := by
    refine (StageEval.seq pRest
      (StageEval.fst (fun _ : S => encUnary (t1 / 2))
        (fun _ : S => encPair encUnary (encPair encUnary (encPair encUnary encUnary))
          (W_acc, (W_out, (q_sum, q_out)))))).mono (fun _ => ?_)
    simp only [length_encUnary]
    linarith [hlen_rest, hlen_wacc_rs, ht1_le_hdr]
  have pWAccRS : StageEval (bmSeq (bmSeq bmFst bmSnd) bmSnd) (encDepPair uHdr uXs)
      (fun _ => encPair encUnary (encPair encUnary (encPair encUnary encUnary))
        (W_acc, (W_out, (q_sum, q_out))))
      (fun _ => 10 * L_hdr + 2 * (2 ^ K * (8 * W_x + 18)) + 30) := by
    refine (StageEval.seq pRest
      (StageEval.snd (fun _ : S => encUnary (t1 / 2))
        (fun _ : S => encPair encUnary (encPair encUnary (encPair encUnary encUnary))
          (W_acc, (W_out, (q_sum, q_out)))))).mono (fun _ => ?_)
    simp only [length_encUnary]
    linarith [hlen_rest, hlen_wacc_rs, ht1_le_hdr]
  have pWAcc : StageEval (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmFst) (encDepPair uHdr uXs)
      (fun _ => encUnary W_acc)
      (fun _ => 14 * L_hdr + 2 * (2 ^ K * (8 * W_x + 18)) + 40) := by
    refine (StageEval.seq pWAccRS
      (StageEval.fst (fun _ : S => encUnary W_acc) (fun _ : S => rsCtx))).mono (fun _ => ?_)
    simp only [length_encUnary]
    linarith [hlen_wacc_rs, hlen_rs_le, hW_le_hdr]
  have pRS : StageEval (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmSnd) (encDepPair uHdr uXs)
      (fun _ => rsCtx)
      (fun _ => 14 * L_hdr + 2 * (2 ^ K * (8 * W_x + 18)) + 40) := by
    refine (StageEval.seq pWAccRS
      (StageEval.snd (fun _ : S => encUnary W_acc) (fun _ : S => rsCtx))).mono (fun _ => ?_)
    simp only [length_encUnary]
    linarith [hlen_wacc_rs, hlen_rs_le, hW_le_hdr]
  -- Step 1: bmNaturalSplitPasses
  let fx : ℕ → FixedComplex (p + 2) := fun i =>
    if h : i < 2 ^ K then xFixed ⟨i, h⟩ else 0
  let rowFn : ℕ → List (FixedComplex (p + 2)) := fun j1 =>
    (List.range r).map (fun j2 => fx (j1 + t1 * j2))
  have hxs_eq : (List.finRange (2 ^ K)).map xFixed = (List.range (2 ^ K)).map fx := by
    refine map_finRange_eq_map_range_of_eq xFixed fx (fun j => ?_)
    simp [fx, j.isLt]
  have h2K : 2 ^ k1 * r = 2 ^ K := t1Ell_mul_rEll K
  have pSplit : StageEval bmNaturalSplitPasses
      (encDepPair (fun _ : S => encUnary k1) uXs)
      (fun _ => encList (encList (encComplex W_x)) ((List.range t1).map rowFn))
      (fun _ => N_split * (4000 * W_x + 10000) + 1000) := by
    intro _ u2 u3 u4 u5 uS
    have h := bmNaturalSplitPasses_computesInTime (encComplex W_x) k1 r (rEll_pos K) fx
      (4 * W_x + 8) (fun _ _ => by simp) u2 u3 u4 u5 uS
    rcases h with ⟨t, ht, hcomp⟩
    rw [h2K, ← hxs_eq] at hcomp
    dsimp only
    refine ⟨t, ?_, hcomp⟩
    rw [h2K] at ht
    have h_eq : (k1 + 1) * (1000 * 2 ^ K * (4 * W_x + 8 + 2)) =
        N_split * (4000 * W_x + 10000) := by
      dsimp only [N_split]; ring
    omega
  have pMat : StageEval bmNyqMat
      (encDepPair uHdr uXs)
      (fun _ => encList (encList (encComplex W_x)) ((List.range t1).map rowFn))
      (fun _ => N_split * (4200 * W_x + 10500) + 25 * L_hdr + 2000) := by
    refine (StageEval.seq (StageEval.fanout pK1 pSnd) pSplit).mono (fun _ => ?_)
    dsimp only [uHdr, uXs]
    simp only [length_encDepPair, length_encUnary, hlen_hdr]
    linarith [hlen_xs, hk1_le_hdr, h2K_le_N, h2K_Wx]
  -- Step 2: Drop t1 / 2 rows and extract head row
  have ht1_half : t1 / 2 < t1 := Nat.div_lt_self (t1Ell_pos K) (by decide)
  have hdrop_eq :
      ((List.range t1).map rowFn).drop (t1 / 2) =
        rowFn (t1 / 2) :: ((List.range t1).map rowFn).drop (t1 / 2 + 1) := by
    have hlt : t1 / 2 < ((List.range t1).map rowFn).length := by simp [ht1_half]
    have hcons := List.drop_eq_getElem_cons hlt
    simpa using hcons
  have hlen_mat :
      (encList (encList (encComplex W_x)) ((List.range t1).map rowFn)).length ≤
      2 ^ K * (16 * W_x + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W_x))
      (r * (2 * (4 * W_x + 8) + 2))
      ((List.range t1).map rowFn)
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
        have hr := length_encList_le_of_forall_le (encComplex W_x) (4 * W_x + 8)
          (rowFn j1) (fun _ _ => by simp)
        simpa [rowFn, List.length_map, List.length_range] using hr)
    simp only [List.length_map, List.length_range] at h
    have hr_pos : 1 ≤ r := rEll_pos K
    have hmat_le : t1 * (2 * (r * (2 * (4 * W_x + 8) + 2)) + 2) ≤ 2 ^ K * (16 * W_x + 38) := by
      calc t1 * (2 * (r * (2 * (4 * W_x + 8) + 2)) + 2)
          ≤ t1 * (2 * (r * (2 * (4 * W_x + 8) + 2)) + 2 * r) :=
            Nat.mul_le_mul_left t1 (Nat.add_le_add_left (by omega) _)
        _ = (t1 * r) * (16 * W_x + 38) := by ring
        _ = 2 ^ K * (16 * W_x + 38) := by rw [t1Ell_mul_rEll K]
    exact h.trans hmat_le
  have hlen_drop :
      (encList (encList (encComplex W_x)) (((List.range t1).map rowFn).drop (t1 / 2 + 1))).length ≤
      2 ^ K * (16 * W_x + 38) :=
    (length_encList_drop_le _ _ _).trans hlen_mat
  have hdrop_cost : (t1 / 2) * (r * (2 * (4 * W_x + 8) + 2) + 5) ≤ 2 ^ K * (8 * W_x + 23) := by
    have hr_pos : 1 ≤ r := rEll_pos K
    have ht1_div : t1 / 2 ≤ t1 := Nat.div_le_self t1 2
    calc (t1 / 2) * (r * (2 * (4 * W_x + 8) + 2) + 5)
        ≤ t1 * (r * (2 * (4 * W_x + 8) + 2) + 5 * r) :=
          Nat.mul_le_mul ht1_div (Nat.add_le_add_left (by omega) _)
      _ = (t1 * r) * (8 * W_x + 23) := by ring
      _ = 2 ^ K * (8 * W_x + 23) := by rw [t1Ell_mul_rEll K]
  have hlen_row :
      (encList (encComplex W_x) (rowFn (t1 / 2))).length ≤ r * (8 * W_x + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W_x) (4 * W_x + 8)
      (rowFn (t1 / 2)) (fun _ _ => by simp)
    simp only [rowFn, List.length_map, List.length_range] at h
    exact h.trans (le_of_eq (by ring))
  have pDropHead : StageEval (bmSeq bmDropList bmFst)
      (encDepPair (fun _ : S => encUnary (t1 / 2))
        (fun _ => encList (encList (encComplex W_x)) ((List.range t1).map rowFn)))
      (fun _ => encList (encComplex W_x) (rowFn (t1 / 2)))
      (fun _ => 2 ^ K * (56 * W_x + 137) + r * (16 * W_x + 36) + 16) := by
    intro _ u2 u3 u4 u5 uS
    dsimp only [encDepPair, id]
    rcases bmDropList_computesInTime (encList (encComplex W_x)) (t1 / 2)
      ((List.range t1).map rowFn) (r * (2 * (4 * W_x + 8) + 2))
      (fun row hrow => by
        rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
        have hr := length_encList_le_of_forall_le (encComplex W_x) (4 * W_x + 8)
          (rowFn j1) (fun _ _ => by simp)
        simpa [rowFn, List.length_map, List.length_range] using hr)
      u2 u3 u4 u5 uS with ⟨t1', ht1', hc1⟩
    rw [hdrop_eq] at hc1
    rcases bmFst_encList_cons_computesInTime (encList (encComplex W_x))
      (rowFn (t1 / 2)) (((List.range t1).map rowFn).drop (t1 / 2 + 1))
      u2 u3 u4 u5 uS with ⟨t2', ht2', hc2⟩
    refine ⟨t1' + t2', ?_, hc1.seq hc2⟩
    linarith [ht1', ht2', hdrop_cost, hlen_mat, hlen_drop, hlen_row]
  have pRowNyq : StageEval bmNyqRow
      (encDepPair uHdr uXs)
      (fun _ => encList (encComplex W_x) (rowFn (t1 / 2)))
      (fun _ => N_split * (4900 * W_x + 12500) +
        r * (16 * W_x + 40) + 60 * L_hdr + 3000) := by
    refine (StageEval.seq (StageEval.fanout pHalfT1 pMat) pDropHead).mono (fun _ => ?_)
    dsimp only [uHdr, uXs]
    simp only [length_encDepPair, length_encUnary, hlen_hdr]
    linarith [hlen_xs, hlen_mat, ht1_le_hdr, h2K_le_N, h2K_Wx]
  -- Step 3: Resize elements of rowFn (t1 / 2) from W_x to W_acc
  let nyqElem : ℕ → FixedComplex (p + 2) := fun j2 =>
    xFixed ⟨(t1 / 2 + t1 * j2) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩
  have hrow_eq : rowFn (t1 / 2) = (List.range r).map nyqElem := by
    dsimp only [rowFn, nyqElem, fx]
    refine List.map_congr_left (fun j2 hj2 => ?_)
    have hj2_lt : j2 < r := List.mem_range.mp hj2
    have hlt : t1 / 2 + t1 * j2 < 2 ^ K := by
      calc t1 / 2 + t1 * j2 < t1 + t1 * j2 := Nat.add_lt_add_right ht1_half _
        _ = t1 * (j2 + 1) := by ring
        _ ≤ t1 * r := Nat.mul_le_mul_left t1 (Nat.succ_le_of_lt hj2_lt)
        _ = 2 ^ K := t1Ell_mul_rEll K
    simp [hlt, Nat.mod_eq_of_lt hlt]
  let SubW := { p : S × FixedComplex (p + 2) // p.2 ∈ rowFn (t1 / 2) }
  have pResizeBody : StageEval (S := SubW) bmResizeComplex
      (encDepPair (fun _ => encUnary W_acc) (fun p => encComplex W_x p.val.2))
      (fun p => encComplex W_acc p.val.2)
      (fun _ => 2500 * W_x + 2500 * W_acc + 12000) := by
    intro ⟨⟨_, z⟩, hzMem⟩ u2 u3 u4 u5 uS
    rw [hrow_eq] at hzMem
    rcases List.mem_map.mp hzMem with ⟨j2, _, rfl⟩
    exact bmResizeComplex_computesInTime W_x W_acc (nyqElem j2) (hx _)
      ((hx _).mono (by omega)) u2 u3 u4 u5 uS
  have hk2_pos : 1 ≤ k2 := by unfold k2 k2Ell; omega
  let M_nyq := 2 ^ (k2 - 1)
  have hr_even : 2 * M_nyq = r := by
    change 2 * 2 ^ (k2 - 1) = 2 ^ k2
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hk2_pos]
  have pRowWideEven : StageEval bmNyqWide
      (encDepPair uHdr uXs)
      (fun _ => encList (encComplex W_acc) ((List.range (2 * M_nyq)).map nyqElem))
      (fun _ => N_split * (5100 * W_x + 13000) +
        r * (2600 * W_x + 2600 * W_acc + 13000) + 100 * L_hdr + 4000) := by
    refine (StageEval.congr_out
      (v2 := fun _ : S => encList (encComplex W_acc) ((List.range (2 * M_nyq)).map nyqElem))
      (StageEval.seq (StageEval.fanout pWAcc pRowNyq)
        (StageEval.mapWithCtx_uniform
          (ctx := fun _ : S => encUnary W_acc)
          (xs := fun _ => rowFn (t1 / 2))
          (encA := fun _ => encComplex W_x)
          (encB := fun _ => encComplex W_acc)
          (fn := fun _ z => z)
          (B := fun _ => 2500 * W_x + 2500 * W_acc + 12000)
          (L_A := fun _ => 4 * W_x + 8)
          (L_B := fun _ => 4 * W_acc + 8)
          pResizeBody
          (fun _ _ _ => by simp)
          (fun _ _ _ => by simp)))
      (fun _ => by simp only [List.map_id', hrow_eq, hr_even])).mono (fun _ => ?_)
    dsimp only [uHdr, uXs]
    have hrowFn_len : (rowFn (t1 / 2)).length = r := by simp [rowFn]
    rw [hrowFn_len]
    have hr_pos : 1 ≤ r := rEll_pos K
    have hW_acc_r : W_acc ≤ r * W_acc := Nat.le_mul_of_pos_left W_acc hr_pos
    simp only [length_encDepPair, length_encUnary, hlen_hdr]
    linarith [hlen_xs, hlen_row, hW_le_hdr, h2K_le_N, h2K_Wx, hW_acc_r]
  -- Step 4: bmAltSumComplexList + bmComplexMulI
  have hpart_nyq : ∀ (s : S) (i : ℕ), i ≤ M_nyq →
      WordWidthBounds W_acc
        (⟨∑ m ∈ Finset.range i, ((nyqElem (2 * m)).re - (nyqElem (2 * m + 1)).re),
          ∑ m ∈ Finset.range i, ((nyqElem (2 * m)).im - (nyqElem (2 * m + 1)).im)⟩ :
          FixedComplex (p + 2)) := by
    intro _ i hi
    have hi_pow : i ≤ 2 ^ k2 :=
      hi.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le k2 1))
    refine ⟨?_, ?_⟩
    · exact (fitsSignedWord_sum_range i hi_pow
        (fun m => (nyqElem (2 * m)).re - (nyqElem (2 * m + 1)).re)
        (fun m _ => (hx _).1.sub (hx _).1)).mono (by omega)
    · exact (fitsSignedWord_sum_range i hi_pow
        (fun m => (nyqElem (2 * m)).im - (nyqElem (2 * m + 1)).im)
        (fun m _ => (hx _).2.sub (hx _).2)).mono (by omega)
  let S_nyq : FixedComplex (p + 2) :=
    ⟨∑ j ∈ Finset.range r, altSign j * (nyqElem j).re,
     ∑ j ∈ Finset.range r, altSign j * (nyqElem j).im⟩
  have hS_bds : WordWidthBounds W_acc S_nyq := by
    have h := hpart_nyq () M_nyq (le_refl M_nyq)
    rw [sum_even_sub_odd_eq_sum_altSign M_nyq (fun j => (nyqElem j).re),
      sum_even_sub_odd_eq_sum_altSign M_nyq (fun j => (nyqElem j).im), hr_even] at h
    exact h
  let S_mulI : FixedComplex q_sum := ⟨-S_nyq.im, S_nyq.re⟩
  have hS_mulI_bds : WordWidthBounds W_acc S_mulI := ⟨hS_bds.2.neg, hS_bds.1⟩
  have hlen_wide :
      (encList (encComplex W_acc) ((List.range (2 * M_nyq)).map nyqElem)).length ≤
      r * (8 * W_acc + 18) := by
    rw [hr_even]
    have h := length_encList_le_of_forall_le (encComplex W_acc) (4 * W_acc + 8)
      ((List.range r).map nyqElem) (fun _ _ => by simp)
    simp only [List.length_map, List.length_range] at h
    exact h.trans (le_of_eq (by ring))
  have pAltSum : StageEval
      (bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmFst) bmNyqWide) bmAltSumComplexList)
      (encDepPair uHdr uXs)
      (fun _ => encComplex W_acc S_nyq)
      (fun _ => N_split * (5300 * W_x + 13500) +
        r * (2600 * W_x + 9700 * W_acc + 32000) + 1000 * W_acc + 140 * L_hdr + 7000) := by
    refine (StageEval.congr_out
      (v2 := fun _ : S => encComplex W_acc S_nyq)
      (StageEval.seq (StageEval.fanout pWAcc pRowWideEven)
        (StageEval.altSumComplexList_stage (fun _ : S => W_acc) (fun _ : S => M_nyq)
          (fun _ => nyqElem)
          (fun _ _ _ => by exact (hx _).mono (by omega))
          (fun _ => by omega)
          hpart_nyq))
      (fun _ => by dsimp only [S_nyq]; rw [hr_even])).mono (fun _ => ?_)
    dsimp only [uHdr, uXs]
    have hM_le_r : M_nyq ≤ r := by omega
    have hMW_le_rW : M_nyq * W_acc ≤ r * W_acc := Nat.mul_le_mul_right W_acc hM_le_r
    simp only [length_encDepPair, length_encUnary, hlen_hdr]
    linarith [hlen_xs, hlen_wide, hW_le_hdr, h2K_le_N, h2K_Wx, hM_le_r, hMW_le_rW]
  have pSumI : StageEval bmNyqSumI
      (encDepPair uHdr uXs)
      (fun _ => encComplex W_acc S_mulI)
      (fun _ => N_split * (5300 * W_x + 13500) +
        r * (2600 * W_x + 9700 * W_acc + 32000) + 1800 * W_acc + 140 * L_hdr + 9000) := by
    refine (StageEval.seq pAltSum
      (StageEval.const (S := S)
        (bmComplexMulI_computesInTime (q1 := p + 2) (q2 := q_sum) W_acc S_nyq hS_bds))).mono
      (fun _ => ?_)
    omega
  -- Step 5: bmComplexRescale from q_sum to q_out at width W_out
  have hnyq_eq : FixedComplex.rescale q_out S_mulI = nyquistModeSumFixed K p xFixed := by
    unfold nyquistModeSumFixed S_mulI S_nyq nyqElem
    dsimp only
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  have pFinal : StageEval bmNyquistModeSum
      (encDepPair uHdr uXs)
      (fun _ => encComplex W_out (nyquistModeSumFixed K p xFixed))
      (fun _ => N_split * (5500 * W_x + 14000) +
        r * (2600 * W_x + 9700 * W_acc + 32000) +
        18500 * W_acc + 3000 * W_out + 30000 * q_sum + 30000 * q_out +
        170 * L_hdr + 80000) := by
    refine (StageEval.congr_out
      (v2 := fun _ : S => encComplex W_out (nyquistModeSumFixed K p xFixed))
      (StageEval.seq (StageEval.fanout pRS pSumI)
        (StageEval.const (S := S)
          (bmComplexRescale_computesInTime W_acc W_out q_sum q_out S_mulI
            hS_mulI_bds (hnyq_eq.symm ▸ hout))))
      (fun _ => by rw [hnyq_eq])).mono (fun _ => ?_)
    dsimp only [uHdr, uXs]
    simp only [length_encDepPair, length_encComplex, hlen_hdr]
    linarith [hlen_xs, hlen_rs_le, h2K_le_N, h2K_Wx]
  rcases pFinal () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uHdr, uXs, encDepPair, id] at ht hcomp
  have ht1_le_N : t1 / 2 ≤ N_split :=
    ((Nat.div_le_self t1 2).trans (t1Ell_le_two_pow K)).trans h2K_le_N
  have hk1_le_N : k1 ≤ N_split :=
    ((le_of_lt (Nat.lt_two_pow_self (n := k1))).trans (t1Ell_le_two_pow K)).trans h2K_le_N
  have hr_sub : r * (2600 * W_x + 9700 * W_acc + 32000) ≤
      r * (18000 * W_x + 18000 * W_acc + 60000) :=
    Nat.mul_le_mul_left r (by linarith only)
  have hN_sub : N_split * (5500 * W_x + 14000) + 170 * (2 * k1 + 4 * (t1 / 2)) ≤
      N_split * (6400 * W_x + 16000) := by
    calc N_split * (5500 * W_x + 14000) + 170 * (2 * k1 + 4 * (t1 / 2))
        ≤ N_split * (5500 * W_x + 14000) + 170 * (2 * N_split + 4 * N_split) := by linarith only [hk1_le_N, ht1_le_N]
      _ = N_split * (5500 * W_x + 15020) := by ring
      _ ≤ N_split * (6400 * W_x + 16000) := Nat.mul_le_mul_left N_split (by linarith only)
  dsimp only [L_hdr, q_sum, q_out] at ht
  refine ⟨t, ?_, hcomp⟩
  change t ≤ N_split * (6400 * W_x + 16000) +
    r * (18000 * W_x + 18000 * W_acc + 60000) +
    20000 * W_acc + 6000 * W_out +
    40000 * (p + 2 + k2) + 40000 * qChildEll K p + 250000
  linarith [ht, hr_sub, hN_sub]

/-! ## 3. Prefix Zip, Unzip-Append, Butterfly Blocks & Leaf Radix-2 FFT (`bmZipListPrefix`, `bmUnzipAppendList`, `bmButterflyPair`, `bmButterflyBlock`, `bmRadix2FFT1DWith`, `bmBaseRadix2FFTWith`) -/

theorem loopListFinalState_zipWordsRevStep_le {α β : Type}
    (encA : α → List Bool) (encB : β → List Bool) :
    ∀ (xs : List α) (ys : List β) (acc : List (List Bool)),
      xs.length ≤ ys.length →
      loopListFinalState (zipWordsRevStep encA) xs (ys.map encB, acc) =
        ((ys.drop xs.length).map encB, ((List.zip xs ys).reverse).map (encPair encA encB) ++ acc)
  | [], ys, acc, _ => by simp [loopListFinalState]
  | _ :: _, [], _, hlen => by simp at hlen
  | x :: xs, y :: ys, acc, hlen => by
    have hlen' : xs.length ≤ ys.length := Nat.le_of_succ_le_succ hlen
    simp only [loopListFinalState_cons, zipWordsRevStep, List.map_cons, List.headD_cons,
      List.tail_cons, List.zip_cons_cons, List.reverse_cons, List.map_append,
      List.append_assoc, List.length_cons, List.drop_succ_cons]
    exact loopListFinalState_zipWordsRevStep_le encA encB xs ys
      (encPair encA encB (x, y) :: acc) hlen'

theorem length_encList_zip_le {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ∀ (xs : List α) (ys : List β),
      xs.length ≤ ys.length →
      (encList (encPair encA encB) (List.zip xs ys)).length ≤
        2 * (encList encA xs).length + 2 * (encList encB ys).length + 2 * xs.length
  | [], _, _ => by simp
  | _ :: _, [], hlen => by simp at hlen
  | x :: xs, y :: ys, hlen => by
    have ih := length_encList_zip_le encA encB xs ys (Nat.le_of_succ_le_succ hlen)
    simp only [List.zip_cons_cons, encList_cons, List.length_append,
      length_encodeDelimWord, length_encPair, List.length_cons]
    omega

theorem loopListStepsAux_zipWordsRevStep_le_of_le {α β : Type}
    (encA : α → List Bool) (encB : β → List Bool) :
    ∀ (xs : List α) (ys : List β) (acc : List (List Bool)),
      xs.length ≤ ys.length →
      loopListStepsAux (zipWordsRevStep encA)
        (fun x _ st => 8 * (encA x).length + 8 * (st.1.headD []).length + 30)
        xs (ys.map encB, acc) ≤
      8 * (encList encA xs).length + 8 * (encList encB ys).length + 1
  | [], _, _, _ => by simp [loopListStepsAux]
  | _ :: _, [], _, hlen => by simp at hlen
  | x :: xs, y :: ys, acc, hlen => by
    have ih := loopListStepsAux_zipWordsRevStep_le_of_le encA encB xs ys
      ((encodeDelimWord (encA x) ++ encodeDelimWord (encB y)) :: acc) (Nat.le_of_succ_le_succ hlen)
    simp only [loopListStepsAux_cons, zipWordsRevStep, List.map_cons, List.headD_cons,
      List.tail_cons, encList_cons, List.length_append, length_encodeDelimWord] at ih ⊢
    omega

/-- **Prefix-Length List Zip (`bmZipListPrefix`)**:
Consumes `encPair (encList encA) (encList encB) (xs, ys)` on `kIO` (where `xs.length ≤ ys.length`),
zips `xs` with the first `xs.length` elements of `ys`, drops the remaining tail `ys.drop xs.length`,
and emits `encList (encPair encA encB) (List.zip xs ys)` in linear time. -/
def bmZipListPrefix : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork2).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kWork3).seq
            ((tmPushEmpty kWork4).seq
              ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                  ((tmPopFirstSubwordRev kWork3 kWork1).seq
                    ((tmRevMoveWord kWork1 kIO).seq
                      (tmPackPairFromRev.seq
                        ((tmRevMoveWord kIO kWork0).seq
                          (tmPrependRevWord kWork0 kWork4)))))).loopNonEmptyWord kWork2).seq
                ((tmDropWord kWork3).seq
                  ((tmMoveWord kWork4 kWork0 kIO).seq bmRevList))))))))

theorem bmZipListPrefix_computesInTime {α β : Type} (encA : α → List Bool) (encB : β → List Bool)
    (xs : List α) (ys : List β) (hlen : xs.length ≤ ys.length)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 28 * (encPair (encList encA) (encList encB) (xs, ys)).length + 55,
      bmZipListPrefix.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encList encA) (encList encB) (xs, ys)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encPair encA encB) (List.zip xs ys)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encA xs) ++ encodeDelimWord (encList encB ys)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encA xs).reverse [] tW2
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encB ys))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encB ys)) [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encA xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encB ys).reverse) []
      (encodeDelimWord (encList encA xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kWork3 (by decide)
    (encList encB ys).reverse [] tW3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encA xs) ++ tW2) [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord (encList encA xs) ++ tW2)
      (encodeDelimWord (encList encB ys) ++ tW3) tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s6
  let stepBound : α → List α → List (List Bool) × List (List Bool) → ℕ :=
    fun x _ st => 8 * (encA x).length + 8 * (st.1.headD []).length + 30
  let stkOf : List (List Bool) × List (List Bool) → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] []
      (encodeDelimWord (encodeWordStack st.1) ++ tW3)
      (encodeDelimWord (encodeWordStack st.2) ++ tW4)
      tW5 tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encA
    (zipWordsRevStep encA) stepBound stkOf
    (fun x rem st restW2 => by
      rcases st with ⟨ws, acc⟩
      dsimp only [stkOf, zipWordsRevStep, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encA x) ++ encodeWordStack (rem.map encA)) restW2 []
        (mkTapes8 [] [] [] []
          (encodeDelimWord (encodeWordStack ws) ++ tW3)
          (encodeDelimWord (encodeWordStack acc) ++ tW4) tW5 tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmPopFirstSubwordRev_computesInTime kWork3 kWork1 (by decide)
        (encodeWordStack ws) tW3 []
        (mkTapes8 [] (encodeDelimWord (encA x).reverse) []
          (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
          [] (encodeDelimWord (encodeWordStack acc) ++ tW4) tW5 tSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, List.append_nil,
        unconsDelimWord_encodeWordStack] at b2
      have b2b := tmRevMoveWord_computesInTime kWork1 kIO (by decide)
        (ws.headD []).reverse [] []
        (mkTapes8 [] (encodeDelimWord (encA x).reverse) []
          (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
          (encodeDelimWord (encodeWordStack ws.tail) ++ tW3)
          (encodeDelimWord (encodeWordStack acc) ++ tW4) tW5 tSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2b
      have b3 := tmPackPairFromRev_computesInTime (encA x) (ws.headD [])
        (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
        (encodeDelimWord (encodeWordStack ws.tail) ++ tW3)
        (encodeDelimWord (encodeWordStack acc) ++ tW4) tW5 tSch
      have b4 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
        (encPair encA id (x, ws.headD [])) [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
          (encodeDelimWord (encodeWordStack ws.tail) ++ tW3)
          (encodeDelimWord (encodeWordStack acc) ++ tW4) tW5 tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at b4
      have b5 := tmPrependRevWord_computesInTime kWork0 kWork4 (by decide)
        (encPair encA id (x, ws.headD [])).reverse (encodeWordStack acc) [] tW4
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
          (encodeDelimWord (encodeWordStack ws.tail) ++ tW3) [] tW5 tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork4, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b5
      simp only [encPair, id, List.length_append, length_encodeDelimWord] at b3 b4 b5
      simp only [encodeWordStack_cons]
      refine ⟨_, ?_, b1.seq (b2.seq (b2b.seq (b3.seq (b4.seq b5))))⟩
      omega)
    xs tW2 (ys.map encB, []) with ⟨tL, htL, s7⟩
  dsimp only [stkOf, stepBound] at htL s7
  simp only [update_mkTapes8_kWork2] at s7
  have hfin := loopListFinalState_zipWordsRevStep_le encA encB xs ys [] hlen
  rw [List.append_nil] at hfin
  rw [hfin] at s7
  change ( _ : BitMachine).ComputesInTime _
    (mkTapes8 [] [] [] tW2
      (encodeDelimWord (encList encB (ys.drop xs.length)) ++ tW3)
      (encodeDelimWord (encList (encPair encA encB) (List.zip xs ys).reverse) ++ tW4) tW5 tSch) tL at s7
  have s8 := tmDropWord_computesInTime kWork3
    (encList encB (ys.drop xs.length)) tW3
    (mkTapes8 [] [] [] tW2 []
      (encodeDelimWord (encList (encPair encA encB) (List.zip xs ys).reverse) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3] at s8
  have s9 := tmMoveWord_computesInTime kWork4 kWork0 kIO (by decide) (by decide) (by decide)
    (encList (encPair encA encB) (List.zip xs ys).reverse) tW4 [] []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s9
  rcases bmRevList_computesStageLe (encPair encA encB) (List.zip xs ys).reverse
    tW2 tW3 tW4 tW5 tSch with ⟨tR, htR, s10⟩
  dsimp only at htR
  simp only [List.reverse_reverse] at s10
  have hlen_rev := length_encList_reverse (encPair encA encB) (List.zip xs ys)
  have hlen_zip := length_encList_zip_le encA encB xs ys hlen
  have hlen_drop := length_encList_drop_le encB xs.length ys
  have hlen_ge := length_encList_ge_two_mul_length encA xs
  have hbL := loopListStepsAux_zipWordsRevStep_le_of_le encA encB xs ys [] hlen
  simp only [hlen_rev] at s9 htR
  simp only [encPair, List.length_append, length_encodeDelimWord] at s1 ⊢
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq s10))))))))⟩
  omega

theorem StageEval.zipListPrefix {S α β : Type} (encA : S → α → List Bool) (encB : S → β → List Bool)
    (xs : S → List α) (ys : S → List β) (hlen : ∀ s, (xs s).length ≤ (ys s).length) :
    StageEval bmZipListPrefix
      (encDepPair (fun s => encList (encA s) (xs s)) (fun s => encList (encB s) (ys s)))
      (fun s => encList (encPair (encA s) (encB s)) (List.zip (xs s) (ys s)))
      (fun s => 28 * (encDepPair (fun s => encList (encA s) (xs s))
        (fun s => encList (encB s) (ys s)) s).length + 55) := by
  intro s tW2 tW3 tW4 tW5 tSch
  exact bmZipListPrefix_computesInTime (encA s) (encB s) (xs s) (ys s) (hlen s)
    tW2 tW3 tW4 tW5 tSch

/-- Concatenates the first projections and second projections of a list of pairs:
`ps ↦ ps.map Prod.fst ++ ps.map Prod.snd`. -/
def unzipAppendList {α : Type} (ps : List (α × α)) : List α :=
  ps.map Prod.fst ++ ps.map Prod.snd

@[simp]
theorem length_unzipAppendList {α : Type} (ps : List (α × α)) :
    (unzipAppendList ps).length = 2 * ps.length := by
  unfold unzipAppendList
  simp
  omega

/-- **Linear-Time Pair-List Unzip-Append (`bmUnzipAppendList`)**:
Consumes `encList (encPair encElem encElem) ps` on `kIO` and emits
`encList encElem (unzipAppendList ps)` on `kIO` in linear `TM2.step` transitions. -/
def bmUnzipAppendList : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq (bmFanout bmConstEmpty bmId) (bmMapWithCtx (bmSeq bmSnd bmFst)))
      (bmSeq (bmFanout bmConstEmpty bmId) (bmMapWithCtx (bmSeq bmSnd bmSnd))))
    bmAppendList

theorem StageEval.unzipAppendList_stage {S α : Type} (encElem : S → α → List Bool)
    (ps : S → List (α × α)) (L : S → ℕ)
    (hL1 : ∀ (s : S) (p : α × α), p ∈ ps s → (encElem s p.1).length ≤ L s)
    (hL2 : ∀ (s : S) (p : α × α), p ∈ ps s → (encElem s p.2).length ≤ L s) :
    StageEval bmUnzipAppendList
      (fun s => encList (encPair (encElem s) (encElem s)) (ps s))
      (fun s => encList (encElem s) (unzipAppendList (ps s)))
      (fun s => (ps s).length * (500 * L s + 1000) + 300) := by
  let SubS := { q : S × (α × α) // q.2 ∈ ps q.1 }
  have hLP : ∀ (s : S) (p : α × α), p ∈ ps s →
      (encPair (encElem s) (encElem s) p).length ≤ 4 * L s + 4 := by
    intro s p hp
    have h1 := hL1 s p hp
    have h2 := hL2 s p hp
    simp only [length_encPair]
    omega
  have pInit := StageEval.fanout
    (StageEval.constEmpty (fun s => encList (encPair (encElem s) (encElem s)) (ps s)))
    (StageEval.id_stage (fun s => encList (encPair (encElem s) (encElem s)) (ps s)))
  have pBody1 : StageEval (S := SubS) (bmSeq bmSnd bmFst)
      (encDepPair (fun _ => []) (fun q => encPair (encElem q.val.1) (encElem q.val.1) q.val.2))
      (fun q => encElem q.val.1 q.val.2.1)
      (fun q => 20 * L q.val.1 + 40) := by
    have b1 := StageEval.snd (fun _ : SubS => ([] : List Bool))
      (fun q => encPair (encElem q.val.1) (encElem q.val.1) q.val.2)
    have b2 := StageEval.fst
      (fun q : SubS => encElem q.val.1 q.val.2.1)
      (fun q : SubS => encElem q.val.1 q.val.2.2)
    refine (StageEval.seq b1 b2).mono (fun q => ?_)
    have h1 := hL1 q.val.1 q.val.2 q.property
    have h2 := hL2 q.val.1 q.val.2 q.property
    simp only [List.length_nil, length_encPair]
    omega
  have pBody2 : StageEval (S := SubS) (bmSeq bmSnd bmSnd)
      (encDepPair (fun _ => []) (fun q => encPair (encElem q.val.1) (encElem q.val.1) q.val.2))
      (fun q => encElem q.val.1 q.val.2.2)
      (fun q => 20 * L q.val.1 + 40) := by
    have b1 := StageEval.snd (fun _ : SubS => ([] : List Bool))
      (fun q => encPair (encElem q.val.1) (encElem q.val.1) q.val.2)
    have b2 := StageEval.snd
      (fun q : SubS => encElem q.val.1 q.val.2.1)
      (fun q : SubS => encElem q.val.1 q.val.2.2)
    refine (StageEval.seq b1 b2).mono (fun q => ?_)
    have h1 := hL1 q.val.1 q.val.2 q.property
    have h2 := hL2 q.val.1 q.val.2 q.property
    simp only [List.length_nil, length_encPair]
    omega
  have pMap1 := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := ps)
    (encA := fun s => encPair (encElem s) (encElem s))
    (encB := encElem)
    (fn := fun _ p => p.1)
    (B := fun s => 20 * L s + 40)
    (L_A := fun s => 4 * L s + 4)
    (L_B := L)
    pBody1 hLP hL1
  have pMap2 := StageEval.mapWithCtx_uniform
    (ctx := fun _ : S => ([] : List Bool))
    (xs := ps)
    (encA := fun s => encPair (encElem s) (encElem s))
    (encB := encElem)
    (fn := fun _ p => p.2)
    (B := fun s => 20 * L s + 40)
    (L_A := fun s => 4 * L s + 4)
    (L_B := L)
    pBody2 hLP hL2
  have pBranch1 := StageEval.seq pInit pMap1
  have pBranch2 := StageEval.seq pInit pMap2
  have pApp := StageEval.appendList encElem
    (fun s => (ps s).map Prod.fst) (fun s => (ps s).map Prod.snd)
  refine (StageEval.seq (StageEval.fanout pBranch1 pBranch2) pApp).mono (fun s => ?_)
  have hlen_in : (encList (encPair (encElem s) (encElem s)) (ps s)).length ≤
      (ps s).length * (2 * (4 * L s + 4) + 2) :=
    length_encList_le_of_forall_le _ (4 * L s + 4) (ps s) (hLP s)
  have hlen_1 : (encList (encElem s) ((ps s).map Prod.fst)).length ≤
      (ps s).length * (2 * L s + 2) := by
    have h := length_encList_le_of_forall_le (encElem s) (L s) ((ps s).map Prod.fst)
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
        exact hL1 s p hp)
    simpa [List.length_map] using h
  have hlen_2 : (encList (encElem s) ((ps s).map Prod.snd)).length ≤
      (ps s).length * (2 * L s + 2) := by
    have h := length_encList_le_of_forall_le (encElem s) (L s) ((ps s).map Prod.snd)
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
        exact hL2 s p hp)
    simpa [List.length_map] using h
  simp only [List.length_nil]
  nlinarith

theorem zip_map_range_le {α β : Type} (f : ℕ → α) (g : ℕ → β) (M N : ℕ) (hMN : M ≤ N) :
    List.zip ((List.range M).map f) ((List.range N).map g) =
      (List.range M).map (fun i => (f i, g i)) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hMN]
  · intro i h1 h2
    simp

theorem unzipAppendList_map_range {α : Type} (M : ℕ) (topFn botFn : ℕ → α) :
    unzipAppendList ((List.range M).map (fun v => (topFn v, botFn v))) =
      (List.range (2 * M)).map (fun u => if u < M then topFn (u % M) else botFn (u % M)) := by
  unfold unzipAppendList
  rw [List.map_map, List.map_map]
  apply List.ext_getElem
  · simp [Nat.two_mul]
  · intro u h1 h2
    simp only [List.getElem_map, List.getElem_range]
    by_cases hu : u < M
    · rw [List.getElem_append_left (by simp [hu])]
      simp [hu, Nat.mod_eq_of_lt hu]
    · rw [List.getElem_append_right (by simp; omega)]
      have hlen1 : ((List.range M).map (Prod.fst ∘ fun v => (topFn v, botFn v))).length = M := by
        simp
      have hu_lt : u < 2 * M := by simpa using h2
      have hmod : u % M = u - M := by
        have h_eq : u = M + (u - M) := by omega
        have h_sub : u - M < M := by omega
        conv_lhs => rw [h_eq, Nat.add_mod_left, Nat.mod_eq_of_lt h_sub]
      simp [hu, hlen1, hmod]

/-- Pure Cooley–Tukey radix-2 butterfly on `((e, o), w)`. -/
def fftButterflyPair {q : ℕ} (p : (FixedComplex q × FixedComplex q) × FixedComplex q) :
    FixedComplex q × FixedComplex q :=
  let e := p.1.1
  let o := p.1.2
  let w := p.2
  let t := FixedComplex.mulRounded w o
  ((e + t).halfRounded, (e - t).halfRounded)

/-- Sub-stage of `bmButterflyPair`: computes `t = FixedComplex.mulRounded w o` from `((W, q), ((e, o), w))`. -/
def bmBflyT (bmMul : BitMachine) : BitMachine :=
  bmSeq
    (bmFanout bmFst (bmFanout (bmSeq bmSnd bmSnd) (bmSeq (bmSeq bmSnd bmFst) bmSnd)))
    (bmComplexMulWith bmMul)

/-- Sub-stage of `bmButterflyPair`: pairs `(e, t)` from `((W, q), ((e, o), w))`. -/
def bmBflyET (bmMul : BitMachine) : BitMachine :=
  bmFanout (bmSeq (bmSeq bmSnd bmFst) bmFst) (bmBflyT bmMul)

/-- **Cooley–Tukey Radix-2 Butterfly Pair (`bmButterflyPair bmMul`)**:
Consumes `encPair (encPair encUnary encUnary) (encPair (encPair (encComplex W) (encComplex W)) (encComplex W)) ((W, q), ((e, o), w))`
and emits `encPair (encComplex W) (encComplex W) (fftButterflyPair ((e, o), w))`. -/
def bmButterflyPair (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmBflyET bmMul) (bmFanout bmComplexAvgAdd bmComplexAvgSub)

theorem bmButterflyPair_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W q : ℕ) (e o w : FixedComplex q)
    (he : WordWidthBounds W e) (ho : WordWidthBounds W o) (hw : WordWidthBounds W w)
    (ht : WordWidthBounds W (FixedComplex.mulRounded w o))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 8 * mulTime W + 100000 * W + 15000 * q + 300000,
      (bmButterflyPair bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encPair (encComplex W) (encComplex W)) (encComplex W))
            ((W, q), ((e, o), w))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encComplex W) (encComplex W) (fftButterflyPair ((e, o), w))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uCtx : S → List Bool := fun _ => encPair encUnary encUnary (W, q)
  let uEO : S → List Bool := fun _ => encPair (encComplex W) (encComplex W) (e, o)
  let uW : S → List Bool := fun _ => encComplex W w
  let uVal : S → List Bool := encDepPair uEO uW
  let uIn : S → List Bool := encDepPair uCtx uVal
  have pCtx := StageEval.fst uCtx uVal
  have pVal := StageEval.snd uCtx uVal
  have pEO := StageEval.seq pVal (StageEval.fst uEO uW)
  have pW := StageEval.seq pVal (StageEval.snd uEO uW)
  have pE : StageEval (bmSeq (bmSeq bmSnd bmFst) bmFst) uIn
      (fun _ => encComplex W e)
      (fun _ => 200 * W + 20 * q + 500) := by
    refine (StageEval.seq pEO
      (StageEval.fst (fun _ : S => encComplex W e) (fun _ : S => encComplex W o))).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uVal, uEO, uW]
    simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex]
    omega
  have pO : StageEval (bmSeq (bmSeq bmSnd bmFst) bmSnd) uIn
      (fun _ => encComplex W o)
      (fun _ => 200 * W + 20 * q + 500) := by
    refine (StageEval.seq pEO
      (StageEval.snd (fun _ : S => encComplex W e) (fun _ : S => encComplex W o))).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uVal, uEO, uW]
    simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex]
    omega
  have pMulIn : StageEval
      (bmFanout bmFst (bmFanout (bmSeq bmSnd bmSnd) (bmSeq (bmSeq bmSnd bmFst) bmSnd))) uIn
      (fun _ => encPair (encPair encUnary encUnary)
        (encPair (encComplex W) (encComplex W)) ((W, q), (w, o)))
      (fun _ => 1200 * W + 100 * q + 3000) := by
    refine (StageEval.fanout pCtx (StageEval.fanout pW pO)).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uVal, uEO, uW]
    simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex]
    omega
  have pT : StageEval (bmBflyT bmMul) uIn
      (fun _ => encComplex W (FixedComplex.mulRounded w o))
      (fun _ => 8 * mulTime W + 65000 * W + 13000 * q + 125000) := by
    refine (StageEval.seq pMulIn
      (StageEval.const (S := S) (bmComplexMulWith_computesInTime hmul W W q w o hw ho ht))).mono
      (fun _ => ?_)
    omega
  have pET : StageEval (bmBflyET bmMul) uIn
      (fun _ => encPair (encComplex W) (encComplex W) (e, FixedComplex.mulRounded w o))
      (fun _ => 8 * mulTime W + 66000 * W + 13500 * q + 130000) := by
    refine (StageEval.fanout pE pT).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uVal, uEO, uW]
    simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex]
    omega
  have pAddSub : StageEval (bmFanout bmComplexAvgAdd bmComplexAvgSub)
      (fun _ : S => encPair (encComplex W) (encComplex W) (e, FixedComplex.mulRounded w o))
      (fun _ => encPair (encComplex W) (encComplex W) (fftButterflyPair ((e, o), w)))
      (fun _ => 31000 * W + 160000) := by
    refine (StageEval.fanout
      (StageEval.const (S := S) (bmComplexAvgAdd_computesInTime W e (FixedComplex.mulRounded w o) he ht))
      (StageEval.const (S := S) (bmComplexAvgSub_computesInTime W e (FixedComplex.mulRounded w o) he ht))).mono
      (fun _ => ?_)
    simp only [length_encPair, length_encComplex]
    omega
  rcases (StageEval.seq pET pAddSub) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uCtx, uVal, uEO, uW, encDepPair, id] at ht_step hcomp
  exact ⟨t, by linarith only [ht_step], hcomp⟩

/-- Pure Cooley–Tukey radix-2 butterfly combine on a block pair `(E, O)` with twiddle list `tw`. -/
def fftButterflyBlock {q : ℕ} (tw : List (FixedComplex q))
    (eo : List (FixedComplex q) × List (FixedComplex q)) : List (FixedComplex q) :=
  unzipAppendList ((List.zip (List.zip eo.1 eo.2) tw).map fftButterflyPair)

/-- Sub-stage 1 of `bmButterflyBlock`: zips `(E, O)` and prefix-zips with `tw`. -/
def bmBflyZipEO : BitMachine :=
  bmSeq (bmFanout (bmSeq bmSnd bmZipList) (bmSeq bmFst bmSnd)) bmZipListPrefix

/-- Sub-stage 2 of `bmButterflyBlock`: maps `bmButterflyPair bmMul` over the zipped triples. -/
def bmBflyMapPairs (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmFanout (bmSeq bmFst bmFst) bmBflyZipEO) (bmMapWithCtx (bmButterflyPair bmMul))

/-- **Cooley–Tukey Radix-2 Butterfly Block Stage (`bmButterflyBlock bmMul`)**:
Consumes `(((W, q), tw), (E, O))` on `kIO` (`E.length = M`, `O.length = M`, `M ≤ tw.length ≤ 2 * M`)
and emits `encList (encComplex W) (fftButterflyBlock tw (E, O))`. -/
def bmButterflyBlock (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmBflyMapPairs bmMul) bmUnzipAppendList

theorem bmButterflyBlock_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W q M : ℕ) (hM : 1 ≤ M)
    (tw E O : List (FixedComplex q))
    (hE_len : E.length = M) (hO_len : O.length = M)
    (htw_ge : M ≤ tw.length) (htw_le : tw.length ≤ 2 * M)
    (hE_bds : ∀ e ∈ E, WordWidthBounds W e)
    (hO_bds : ∀ o ∈ O, WordWidthBounds W o)
    (htw_bds : ∀ w ∈ tw, WordWidthBounds W w)
    (hmul_bds : ∀ o ∈ O, ∀ w ∈ tw, WordWidthBounds W (FixedComplex.mulRounded w o))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ M * (8 * mulTime W + 115000 * W + 18000 * q + 330000) + 3000 * (W + q) + 10000,
      (bmButterflyBlock bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary encUnary) (encList (encComplex W)))
            (encPair (encList (encComplex W)) (encList (encComplex W)))
            (((W, q), tw), (E, O))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encComplex W) (fftButterflyBlock tw (E, O))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uWQ : S → List Bool := fun _ => encPair encUnary encUnary (W, q)
  let uTw : S → List Bool := fun _ => encList (encComplex W) tw
  let uCtx : S → List Bool := encDepPair uWQ uTw
  let uEO : S → List Bool := fun _ =>
    encPair (encList (encComplex W)) (encList (encComplex W)) (E, O)
  let uIn : S → List Bool := encDepPair uCtx uEO
  have hlen_E : (encList (encComplex W) E).length ≤ M * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) E (fun _ _ => by simp)
    rw [hE_len] at h; exact h.trans (le_of_eq (by ring))
  have hlen_O : (encList (encComplex W) O).length ≤ M * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) O (fun _ _ => by simp)
    rw [hO_len] at h; exact h.trans (le_of_eq (by ring))
  have hlen_tw : (encList (encComplex W) tw).length ≤ M * (16 * W + 36) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) tw (fun _ _ => by simp)
    have h2 : tw.length * (2 * (4 * W + 8) + 2) ≤ (2 * M) * (2 * (4 * W + 8) + 2) :=
      Nat.mul_le_mul_right _ htw_le
    exact (h.trans h2).trans (le_of_eq (by ring))
  have hlen_zipEO :
      (encList (encPair (encComplex W) (encComplex W)) (List.zip E O)).length ≤
      M * (32 * W + 74) := by
    have h := length_encList_le_of_forall_le (encPair (encComplex W) (encComplex W))
      (16 * W + 36) (List.zip E O) (fun _ _ => by simp [length_encPair]; omega)
    have hlen : (List.zip E O).length = M := by simp [hE_len, hO_len]
    rw [hlen] at h; exact h.trans (le_of_eq (by ring))
  have hlen_triples :
      (encList (encPair (encPair (encComplex W) (encComplex W)) (encComplex W))
        (List.zip (List.zip E O) tw)).length ≤ M * (80 * W + 186) := by
    have h := length_encList_le_of_forall_le
      (encPair (encPair (encComplex W) (encComplex W)) (encComplex W))
      (40 * W + 92) (List.zip (List.zip E O) tw) (fun _ _ => by simp [length_encPair]; omega)
    have hlen : (List.zip (List.zip E O) tw).length = M := by
      simp [hE_len, hO_len, Nat.min_eq_left htw_ge]
    rw [hlen] at h; exact h.trans (le_of_eq (by ring))
  have hW_le_MW : W ≤ M * W := Nat.le_mul_of_pos_left W hM
  have hq_le_Mq : q ≤ M * q := Nat.le_mul_of_pos_left q hM
  have pFst := StageEval.fst uCtx uEO
  have pSnd := StageEval.snd uCtx uEO
  have pWQ : StageEval (bmSeq bmFst bmFst) uIn uWQ
      (fun _ => M * (260 * W + 600) + 30 * (W + q) + 100) := by
    refine (StageEval.seq pFst (StageEval.fst uWQ uTw)).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uWQ, uTw, uEO]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_E, hlen_O, hlen_tw, hM]
  have pTw : StageEval (bmSeq bmFst bmSnd) uIn uTw
      (fun _ => M * (260 * W + 600) + 30 * (W + q) + 100) := by
    refine (StageEval.seq pFst (StageEval.snd uWQ uTw)).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uWQ, uTw, uEO]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_E, hlen_O, hlen_tw, hM]
  have pZipEO : StageEval (bmSeq bmSnd bmZipList) uIn
      (fun _ => encList (encPair (encComplex W) (encComplex W)) (List.zip E O))
      (fun _ => M * (1100 * W + 2500) + 20 * (W + q) + 200) := by
    refine (StageEval.seq pSnd
      (StageEval.zipList (fun _ : S => encComplex W) (fun _ : S => encComplex W)
        (fun _ => E) (fun _ => O) (fun _ => by rw [hE_len, hO_len]))).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uWQ, uTw, uEO]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_E, hlen_O, hlen_tw, hM]
  have pTriples : StageEval bmBflyZipEO uIn
      (fun _ => encList (encPair (encPair (encComplex W) (encComplex W)) (encComplex W))
        (List.zip (List.zip E O) tw))
      (fun _ => M * (5000 * W + 11500) + 100 * (W + q) + 800) := by
    refine (StageEval.seq (StageEval.fanout pZipEO pTw)
      (StageEval.zipListPrefix
        (fun _ : S => encPair (encComplex W) (encComplex W))
        (fun _ : S => encComplex W)
        (fun _ => List.zip E O) (fun _ => tw)
        (fun _ => by simp [hE_len, hO_len, htw_ge]))).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uWQ, uTw, uEO]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_E, hlen_O, hlen_tw, hlen_zipEO, hM]
  let SubT := { p : S × ((FixedComplex q × FixedComplex q) × FixedComplex q) //
    p.2 ∈ List.zip (List.zip E O) tw }
  have pPairBody : StageEval (S := SubT) (bmButterflyPair bmMul)
      (encDepPair (fun _ => encPair encUnary encUnary (W, q))
        (fun p => encPair (encPair (encComplex W) (encComplex W)) (encComplex W) p.val.2))
      (fun p => encPair (encComplex W) (encComplex W) (fftButterflyPair p.val.2))
      (fun _ => 8 * mulTime W + 100000 * W + 15000 * q + 300000) := by
    intro ⟨⟨_, ⟨⟨e, o⟩, w⟩⟩, hmem⟩ u2 u3 u4 u5 uS
    have hmem1 := List.of_mem_zip hmem
    have hmem2 := List.of_mem_zip hmem1.1
    exact bmButterflyPair_computesInTime hmul W q e o w
      (hE_bds e hmem2.1) (hO_bds o hmem2.2) (htw_bds w hmem1.2)
      (hmul_bds o hmem2.2 w hmem1.2) u2 u3 u4 u5 uS
  have pMapPairs : StageEval (bmBflyMapPairs bmMul) uIn
      (fun _ => encList (encPair (encComplex W) (encComplex W))
        ((List.zip (List.zip E O) tw).map fftButterflyPair))
      (fun _ => M * (8 * mulTime W + 108000 * W + 16000 * q + 315000) +
        500 * (W + q) + 2000) := by
    refine (StageEval.seq (StageEval.fanout pWQ pTriples)
      (StageEval.mapWithCtx_uniform
        (ctx := uWQ)
        (xs := fun _ => List.zip (List.zip E O) tw)
        (encA := fun _ => encPair (encPair (encComplex W) (encComplex W)) (encComplex W))
        (encB := fun _ => encPair (encComplex W) (encComplex W))
        (fn := fun _ p => fftButterflyPair p)
        (B := fun _ => 8 * mulTime W + 100000 * W + 15000 * q + 300000)
        (L_A := fun _ => 40 * W + 92)
        (L_B := fun _ => 16 * W + 36)
        pPairBody
        (fun _ _ _ => by simp [length_encPair]; omega)
        (fun _ _ _ => by simp [length_encPair]; omega))).mono (fun _ => ?_)
    dsimp only [uIn, uCtx, uWQ, uTw, uEO]
    have hlen : (List.zip (List.zip E O) tw).length = M := by
      simp [hE_len, hO_len, Nat.min_eq_left htw_ge]
    rw [hlen]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_E, hlen_O, hlen_tw, hlen_triples, hM, hW_le_MW, hq_le_Mq]
  have pUnzip : StageEval bmUnzipAppendList
      (fun _ : S => encList (encPair (encComplex W) (encComplex W))
        ((List.zip (List.zip E O) tw).map fftButterflyPair))
      (fun _ => encList (encComplex W) (fftButterflyBlock tw (E, O)))
      (fun _ => M * (2000 * W + 5000) + 300) := by
    refine (StageEval.unzipAppendList_stage (fun _ : S => encComplex W)
      (fun _ => (List.zip (List.zip E O) tw).map fftButterflyPair)
      (fun _ => 4 * W + 8)
      (fun _ _ _ => by simp)
      (fun _ _ _ => by simp)).mono (fun _ => ?_)
    have hlen : ((List.zip (List.zip E O) tw).map fftButterflyPair).length = M := by
      simp [hE_len, hO_len, Nat.min_eq_left htw_ge]
    rw [hlen]
    exact le_of_eq (by ring)
  have hlen_mapped :
      (encList (encPair (encComplex W) (encComplex W))
        ((List.zip (List.zip E O) tw).map fftButterflyPair)).length ≤ M * (32 * W + 74) := by
    have h := length_encList_le_of_forall_le (encPair (encComplex W) (encComplex W))
      (16 * W + 36) ((List.zip (List.zip E O) tw).map fftButterflyPair)
      (fun _ _ => by simp [length_encPair]; omega)
    have hlen : ((List.zip (List.zip E O) tw).map fftButterflyPair).length = M := by
      simp [hE_len, hO_len, Nat.min_eq_left htw_ge]
    rw [hlen] at h; exact h.trans (le_of_eq (by ring))
  rcases (StageEval.seq pMapPairs pUnzip) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uCtx, uWQ, uTw, uEO, encDepPair, id] at ht_step hcomp
  refine ⟨t, ?_, hcomp⟩
  linarith [ht_step, hlen_mapped, hM]

/-! ### Top-Down Split / Bottom-Up Combine Loops for `bmRadix2FFT1DWith` and `bmBaseRadix2FFTWith` -/

/-- Even-index specialization of a vector `x : Fin (2 ^ (m + 1)) → α`. -/
def eFn {α : Type} (m : ℕ) (x : Fin (2 ^ (m + 1)) → α) : Fin (2 ^ m) → α :=
  fun j => x (evenSubIndex m j)

/-- Odd-index specialization of a vector `x : Fin (2 ^ (m + 1)) → α`. -/
def oFn {α : Type} (m : ℕ) (x : Fin (2 ^ (m + 1)) → α) : Fin (2 ^ m) → α :=
  fun j => x (oddSubIndex m j)

theorem deinterleaveList_map_finRange_succ {α : Type} (m : ℕ) (x : Fin (2 ^ (m + 1)) → α) :
    deinterleaveList ((List.finRange (2 ^ (m + 1))).map x) =
      ((List.finRange (2 ^ m)).map (eFn m x), (List.finRange (2 ^ m)).map (oFn m x)) := by
  have h1 : (List.finRange (2 ^ (m + 1))).map x =
      (List.range (2 * 2 ^ m)).map
        (fun k => x ⟨k % 2 ^ (m + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩) := by
    rw [← Nat.pow_succ']
    exact map_finRange_eq_map_range_of_eq x _ (fun i => by simp [Nat.mod_eq_of_lt i.isLt])
  rw [h1, deinterleaveList_map_range]
  refine Prod.ext ?_ ?_
  · symm
    exact map_finRange_eq_map_range_of_eq (eFn m x) _ (fun j => by
      dsimp only [eFn, evenSubIndex]
      congr 1
      ext
      exact (Nat.mod_eq_of_lt (by
        have hj := j.isLt
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
        omega)).symm)
  · symm
    exact map_finRange_eq_map_range_of_eq (oFn m x) _ (fun j => by
      dsimp only [oFn, oddSubIndex]
      congr 1
      ext
      exact (Nat.mod_eq_of_lt (by
        have hj := j.isLt
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
        omega)).symm)

/-- Splits each vector `f : Fin (2 ^ (m + 1)) → α` in `fs` into `[eFn m f, oFn m f]`. -/
def splitFnList {α : Type} (m : ℕ) (fs : List (Fin (2 ^ (m + 1)) → α)) :
    List (Fin (2 ^ m) → α) :=
  fs.flatMap (fun f => [eFn m f, oFn m f])

theorem length_splitFnList {α : Type} (m : ℕ) :
    ∀ (fs : List (Fin (2 ^ (m + 1)) → α)),
      (splitFnList m fs).length = 2 * fs.length
  | [] => rfl
  | f :: fs => by
    have ih := length_splitFnList m fs
    simp only [splitFnList, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem forall_mem_splitFnList {α : Type} {P : α → Prop} (m : ℕ)
    (fs : List (Fin (2 ^ (m + 1)) → α))
    (hfs : ∀ f ∈ fs, ∀ j : Fin (2 ^ (m + 1)), P (f j)) :
    ∀ g ∈ splitFnList m fs, ∀ j : Fin (2 ^ m), P (g j) := by
  intro g hg j
  unfold splitFnList at hg
  rcases List.mem_flatMap.mp hg with ⟨f, hf, hg_in⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg_in
  rcases hg_in with rfl | rfl
  · exact hfs f hf (evenSubIndex m j)
  · exact hfs f hf (oddSubIndex m j)

theorem splitBlocks_map_finRange_eq_splitFnList {α : Type} (m : ℕ) :
    ∀ (fs : List (Fin (2 ^ (m + 1)) → α)),
      splitBlocks (fs.map (fun f => (List.finRange (2 ^ (m + 1))).map f)) =
        (splitFnList m fs).map (fun g => (List.finRange (2 ^ m)).map g)
  | [] => rfl
  | f :: fs => by
    have ih := splitBlocks_map_finRange_eq_splitFnList m fs
    simp only [List.map_cons, splitBlocks, List.flatMap_cons,
      deinterleaveList_map_finRange_succ, splitFnList] at ih ⊢
    exact congrArg (fun tl => _ :: _ :: tl) ih

theorem map_splitFnList {α β : Type} (m : ℕ) (h : (Fin (2 ^ m) → α) → β) :
    ∀ (fs : List (Fin (2 ^ (m + 1)) → α)),
      (splitFnList m fs).map h =
        fs.flatMap (fun f => [h (eFn m f), h (oFn m f)])
  | [] => rfl
  | f :: fs => by
    have ih := map_splitFnList m h fs
    simp only [splitFnList, List.flatMap_cons] at ih ⊢
    exact congrArg (fun tl => _ :: _ :: tl) ih

/-- Pure block-pairing helper: pairs `[E_0, O_0, E_1, O_1, ...]` into `[(E_0, O_0), (E_1, O_1), ...]`. -/
def pairBlocks {α : Type} (blks : List (List α)) : List (List α × List α) :=
  List.zip (deinterleaveList blks).1 (deinterleaveList blks).2

theorem pairBlocks_flatMap_two {α β : Type} (f g : α → List β) (xs : List α) :
    pairBlocks (xs.flatMap (fun x => [f x, g x])) = xs.map (fun x => (f x, g x)) := by
  unfold pairBlocks
  rw [deinterleaveList_flatMap_two]
  induction xs with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- Stage-$d$ twiddle list of length $2^{K - d}$ for radix-2 FFT of depth $K$. -/
def twStage {q : ℕ} (K : ℕ) (leafTwiddles : Fin (2 ^ K) → FixedComplex q) (d : ℕ) :
    List (FixedComplex q) :=
  (List.range (2 ^ (K - d))).map (fun v =>
    leafTwiddles ⟨(v * 2 ^ d) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩)

@[simp]
theorem length_twStage {q : ℕ} (K : ℕ) (leafTwiddles : Fin (2 ^ K) → FixedComplex q) (d : ℕ) :
    (twStage K leafTwiddles d).length = 2 ^ (K - d) := by
  simp [twStage]

theorem mem_twStage_bounds {q W : ℕ} (K : ℕ) (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (htw : ∀ u : Fin (2 ^ K), WordWidthBounds W (leafTwiddles u))
    (d : ℕ) :
    ∀ w ∈ twStage K leafTwiddles d, WordWidthBounds W w := by
  intro w hw
  unfold twStage at hw
  rcases List.mem_map.mp hw with ⟨v, _, rfl⟩
  exact htw _

theorem twStage_zero {q : ℕ} (K : ℕ) (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    (List.finRange (2 ^ K)).map leafTwiddles = twStage K leafTwiddles 0 := by
  unfold twStage
  simp only [Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
  exact map_finRange_eq_map_range_of_eq leafTwiddles _ (fun i => by simp [Nat.mod_eq_of_lt i.isLt])

theorem deinterleaveList_fst_twStage {q : ℕ} (K : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) (d : ℕ) (hd : d < K) :
    (deinterleaveList (twStage K leafTwiddles d)).1 = twStage K leafTwiddles (d + 1) := by
  unfold twStage
  have hsub : K - d = (K - (d + 1)) + 1 := by omega
  rw [hsub, Nat.pow_succ', deinterleaveList_map_range]
  apply List.map_congr_left
  intro v _
  congr 1
  ext
  simp only [Nat.pow_succ']
  have hmul : 2 * v * 2 ^ d = v * (2 * 2 ^ d) := by ring
  rw [hmul]

theorem fftButterflyBlock_eq_radix2FFT1DFixed {K q : ℕ}
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (m : ℕ) (hm : m + 1 ≤ K) (x : Fin (2 ^ (m + 1)) → FixedComplex q) :
    fftButterflyBlock (twStage K leafTwiddles (K - (m + 1)))
      ((List.finRange (2 ^ m)).map (radix2FFT1DFixed K q leafTwiddles m (Nat.le_of_succ_le hm) (eFn m x)),
       (List.finRange (2 ^ m)).map (radix2FFT1DFixed K q leafTwiddles m (Nat.le_of_succ_le hm) (oFn m x))) =
      (List.finRange (2 ^ (m + 1))).map (radix2FFT1DFixed K q leafTwiddles (m + 1) hm x) := by
  set hm' : m ≤ K := Nat.le_of_succ_le hm
  set ef := radix2FFT1DFixed K q leafTwiddles m hm' (eFn m x)
  set of := radix2FFT1DFixed K q leafTwiddles m hm' (oFn m x)
  have hE : (List.finRange (2 ^ m)).map ef =
      (List.range (2 ^ m)).map (fun v => ef ⟨v % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩) :=
    map_finRange_eq_map_range_of_eq ef _ (fun j => by simp [Nat.mod_eq_of_lt j.isLt])
  have hO : (List.finRange (2 ^ m)).map of =
      (List.range (2 ^ m)).map (fun v => of ⟨v % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩) :=
    map_finRange_eq_map_range_of_eq of _ (fun j => by simp [Nat.mod_eq_of_lt j.isLt])
  unfold fftButterflyBlock twStage
  dsimp only
  have hsubK : K - (K - (m + 1)) = m + 1 := by omega
  have hle_tw : 2 ^ m ≤ 2 ^ (K - (K - (m + 1))) := by
    rw [hsubK, Nat.pow_succ']; omega
  rw [hE, hO, zip_map_range_le _ _ _ _ le_rfl, zip_map_range_le _ _ _ _ hle_tw, List.map_map,
    unzipAppendList_map_range]
  have hRHS : (List.finRange (2 ^ (m + 1))).map (radix2FFT1DFixed K q leafTwiddles (m + 1) hm x) =
      (List.range (2 * 2 ^ m)).map (fun u =>
        radix2FFT1DFixed K q leafTwiddles (m + 1) hm x
          ⟨u % 2 ^ (m + 1), Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩) := by
    have hpow2 : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
    exact (map_finRange_eq_map_range_of_eq (radix2FFT1DFixed K q leafTwiddles (m + 1) hm x)
      (fun u => radix2FFT1DFixed K q leafTwiddles (m + 1) hm x
        ⟨u % 2 ^ (m + 1), Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩)
      (fun u => by simp [Nat.mod_eq_of_lt u.isLt])).trans (by rw [← hpow2])
  rw [hRHS]
  apply List.map_congr_left
  intro u hu
  have hu_lt : u < 2 ^ (m + 1) := by
    rw [Nat.pow_succ']
    exact List.mem_range.mp hu
  have hmod2 : u % 2 ^ (m + 1) = u := Nat.mod_eq_of_lt hu_lt
  dsimp only [Function.comp, fftButterflyPair]
  unfold radix2FFT1DFixed radix2FFT1DFixedWithMul
  simp only [memoizeFin_eq, hmod2,
    FixedComplex.mulRoundedWith_eq_mulRounded (· * ·) (fun _ _ => rfl),
    radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl)]
  have hv_lt : u % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  have hwIdx : ((u % 2 ^ m) * 2 ^ (K - (m + 1))) % 2 ^ K = (u % 2 ^ m) * 2 ^ (K - (m + 1)) :=
    Nat.mod_eq_of_lt (mul_two_pow_sub_lt hm ⟨u % 2 ^ m, hv_lt⟩)
  simp only [hwIdx, Nat.mod_mod]
  rfl

/-- Pure stage-combine pass across all block pairs in `blks` with stage twiddle list `tw`. -/
def fftCombineBlocks {q : ℕ} (tw : List (FixedComplex q))
    (blks : List (List (FixedComplex q))) : List (List (FixedComplex q)) :=
  (pairBlocks blks).map (fftButterflyBlock tw)

/-- Pure state of the top-down split loop: `(blks, (tw, stk))`. -/
abbrev SplitState (q : ℕ) :=
  List (List (FixedComplex q)) × (List (FixedComplex q) × List (List (FixedComplex q)))

/-- Pure single step of the top-down split loop: splits `blks`, pushes `tw` onto `stk`,
and halves `tw` via `(deinterleaveList tw).1`. -/
def fftSplitStep {q : ℕ} (st : SplitState q) : SplitState q :=
  (splitBlocks st.1, ((deinterleaveList st.2.1).1, st.2.1 :: st.2.2))

/-- Pure state of the bottom-up combine loop: `(stk, blks)`. -/
abbrev CombState (q : ℕ) :=
  List (List (FixedComplex q)) × List (List (FixedComplex q))

/-- Pure single step of the bottom-up combine loop: pops `tw := stk.headD []` from `stk`
and combines adjacent block pairs in `blks` using `fftCombineBlocks tw blks`. -/
def fftCombineStep {q : ℕ} (st : CombState q) : CombState q :=
  (st.1.tail, fftCombineBlocks (st.1.headD []) st.2)

theorem fst_fftCombineStep_iterate {q : ℕ} :
    ∀ (i : ℕ) (stk : List (List (FixedComplex q))) (blks : List (List (FixedComplex q))),
      ((fftCombineStep^[i]) (stk, blks)).1 = stk.drop i
  | 0, _, _ => rfl
  | i + 1, stk, blks => by
    rw [Function.iterate_succ_apply, fst_fftCombineStep_iterate i]
    dsimp only [fftCombineStep]
    rw [← List.drop_one, List.drop_drop, Nat.add_comm 1 i]

theorem fftCombineStep_iterate_fftSplitStep_iterate {K q : ℕ}
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    ∀ (m : ℕ) (hm : m ≤ K) (d : ℕ) (_hd : m + d = K)
      (fs : List (Fin (2 ^ m) → FixedComplex q))
      (stk : List (List (FixedComplex q))),
      let splitOut := (fftSplitStep^[m])
        (fs.map (fun f => (List.finRange (2 ^ m)).map f),
         (twStage K leafTwiddles d, stk))
      (fftCombineStep^[m]) (splitOut.2.2, splitOut.1) =
        (stk,
         fs.map (fun f =>
           (List.finRange (2 ^ m)).map (radix2FFT1DFixed K q leafTwiddles m hm f)))
  | 0, _, _, _, _, _ => rfl
  | m + 1, hm, d, hd, fs, stk => by
    have hm' : m ≤ K := Nat.le_of_succ_le hm
    have hd_lt : d < K := by omega
    have hd' : m + (d + 1) = K := by omega
    rw [Function.iterate_succ_apply]
    dsimp only [fftSplitStep]
    rw [splitBlocks_map_finRange_eq_splitFnList, deinterleaveList_fst_twStage K leafTwiddles d hd_lt]
    have ih := fftCombineStep_iterate_fftSplitStep_iterate leafTwiddles m hm' (d + 1) hd'
      (splitFnList m fs) (twStage K leafTwiddles d :: stk)
    dsimp only at ih
    rw [Function.iterate_succ_apply', ih]
    dsimp only [fftCombineStep, List.tail_cons, List.headD_cons, fftCombineBlocks]
    congr 1
    rw [map_splitFnList, pairBlocks_flatMap_two, List.map_map]
    apply List.map_congr_left
    intro f _
    dsimp only [Function.comp]
    have htw_eq : d = K - (m + 1) := by omega
    rw [htw_eq]
    exact fftButterflyBlock_eq_radix2FFT1DFixed leafTwiddles m hm f

theorem fftSplitStep_iterate_spec {K q W0 W : ℕ}
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    ∀ (d m d0 : ℕ) (_hd_le : d ≤ m) (_hmd0 : m + d0 = K)
      (fs : List (Fin (2 ^ m) → FixedComplex q))
      (_hfs : ∀ f ∈ fs, ∀ j : Fin (2 ^ m), WordWidthBounds W0 (f j))
      (stk : List (List (FixedComplex q))),
      ∃ (fs_d : List (Fin (2 ^ (m - d)) → FixedComplex q))
        (stk_d : List (List (FixedComplex q))),
        (fftSplitStep^[d])
          (fs.map (fun f => (List.finRange (2 ^ m)).map f),
           (twStage K leafTwiddles d0, stk)) =
          (fs_d.map (fun g => (List.finRange (2 ^ (m - d))).map g),
           (twStage K leafTwiddles (d0 + d), stk_d)) ∧
        fs_d.length = 2 ^ d * fs.length ∧
        (∀ g ∈ fs_d, ∀ j : Fin (2 ^ (m - d)), WordWidthBounds W0 (g j)) ∧
        (encList (encList (encComplex W)) stk_d).length ≤
          (encList (encList (encComplex W)) stk).length +
          (2 ^ (K - d0) - 2 ^ (K - d0 - d)) * (32 * W + 76)
  | 0, m, d0, _, _, fs, hfs, stk => by
    refine ⟨fs, stk, ?_, by simp, hfs, by simp⟩
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero, Nat.add_zero]
  | d + 1, 0, d0, hd_le, _, _, _, _ => by omega
  | d + 1, m + 1, d0, hd_le, hmd0, fs, hfs, stk => by
    have hd_le' : d ≤ m := Nat.le_of_succ_le_succ hd_le
    have hd0_lt : d0 < K := by omega
    have hmd0' : m + (d0 + 1) = K := by omega
    rw [Function.iterate_succ_apply]
    dsimp only [fftSplitStep]
    rw [splitBlocks_map_finRange_eq_splitFnList,
      deinterleaveList_fst_twStage K leafTwiddles d0 hd0_lt]
    rcases fftSplitStep_iterate_spec (W := W) leafTwiddles d m (d0 + 1) hd_le' hmd0'
      (splitFnList m fs) (forall_mem_splitFnList m fs hfs)
      (twStage K leafTwiddles d0 :: stk) with
      ⟨fs_d, stk_d, heq, hlen_fs, hbds_fs, hlen_stk⟩
    have hadd : d0 + 1 + d = d0 + (d + 1) := by omega
    rw [hadd] at heq
    rw [Nat.add_sub_add_right m 1 d]
    refine ⟨fs_d, stk_d, heq, ?_, hbds_fs, ?_⟩
    · rw [hlen_fs, length_splitFnList, Nat.pow_succ 2 d]
      ring
    · have htw_len :
          (encList (encComplex W) (twStage K leafTwiddles d0)).length ≤
          2 ^ (K - d0) * (8 * W + 18) := by
        have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          (twStage K leafTwiddles d0) (fun _ _ => by simp)
        rw [length_twStage] at h
        exact h.trans (le_of_eq (by ring))
      have hpow_step : 2 ^ (K - d0) = 2 * 2 ^ (K - (d0 + 1)) := by
        have hsub : K - d0 = (K - (d0 + 1)) + 1 := by omega
        rw [hsub, Nat.pow_succ']
      have hpos : 1 ≤ 2 ^ (K - (d0 + 1)) := Nat.one_le_two_pow
      have hcons_len :
          (encList (encList (encComplex W)) (twStage K leafTwiddles d0 :: stk)).length ≤
          (encList (encList (encComplex W)) stk).length +
          (2 ^ (K - d0) - 2 ^ (K - (d0 + 1))) * (32 * W + 76) := by
        simp only [encList_cons, List.length_append, length_encodeDelimWord]
        have hsub2 : 2 * 2 ^ (K - (d0 + 1)) - 2 ^ (K - (d0 + 1)) = 2 ^ (K - (d0 + 1)) := by omega
        rw [hpow_step] at htw_len
        rw [hpow_step, hsub2]
        nlinarith [htw_len, hpos]
      have hsub_tel :
          (2 ^ (K - d0) - 2 ^ (K - (d0 + 1))) +
          (2 ^ (K - (d0 + 1)) - 2 ^ (K - (d0 + 1) - d)) =
          2 ^ (K - d0) - 2 ^ (K - d0 - (d + 1)) := by
        have hle1 : 2 ^ (K - (d0 + 1) - d) ≤ 2 ^ (K - (d0 + 1)) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hle2 : 2 ^ (K - (d0 + 1)) ≤ 2 ^ (K - d0) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hsub_eq : K - (d0 + 1) - d = K - d0 - (d + 1) := by omega
        rw [hsub_eq] at hle1 ⊢
        omega
      calc (encList (encList (encComplex W)) stk_d).length
          ≤ (encList (encList (encComplex W)) stk).length +
            (2 ^ (K - d0) - 2 ^ (K - (d0 + 1))) * (32 * W + 76) +
            (2 ^ (K - (d0 + 1)) - 2 ^ (K - (d0 + 1) - d)) * (32 * W + 76) := by
              linarith [hlen_stk, hcons_len]
        _ = (encList (encList (encComplex W)) stk).length +
            ((2 ^ (K - d0) - 2 ^ (K - (d0 + 1))) +
             (2 ^ (K - (d0 + 1)) - 2 ^ (K - (d0 + 1) - d))) * (32 * W + 76) := by ring
        _ = (encList (encList (encComplex W)) stk).length +
            (2 ^ (K - d0) - 2 ^ (K - d0 - (d + 1))) * (32 * W + 76) := by rw [hsub_tel]

theorem fftCombineStep_iterate_lt_spec {K q W0 : ℕ}
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    ∀ (m : ℕ) (hm : m ≤ K) (d : ℕ) (_hd : m + d = K)
      (fs : List (Fin (2 ^ m) → FixedComplex q))
      (_hfs : ∀ f ∈ fs, ∀ j : Fin (2 ^ m), WordWidthBounds W0 (f j))
      (stk : List (List (FixedComplex q)))
      (i : ℕ) (hi : i < m),
      let splitOut := (fftSplitStep^[m])
        (fs.map (fun f => (List.finRange (2 ^ m)).map f),
         (twStage K leafTwiddles d, stk))
      ∃ (gs : List (Fin (2 ^ (i + 1)) → FixedComplex q))
        (stk_rest : List (List (FixedComplex q))),
        (fftCombineStep^[i]) (splitOut.2.2, splitOut.1) =
          (twStage K leafTwiddles (K - 1 - i) :: stk_rest,
           gs.flatMap (fun g =>
             [(List.finRange (2 ^ i)).map
                (radix2FFT1DFixed K q leafTwiddles i (Nat.le_of_lt (lt_of_lt_of_le hi hm)) (eFn i g)),
              (List.finRange (2 ^ i)).map
                (radix2FFT1DFixed K q leafTwiddles i (Nat.le_of_lt (lt_of_lt_of_le hi hm)) (oFn i g))])) ∧
        gs.length = 2 ^ (m - 1 - i) * fs.length ∧
        ∀ g ∈ gs, ∀ j : Fin (2 ^ (i + 1)), WordWidthBounds W0 (g j)
  | 0, _, _, _, _, _, _, _, hi => by omega
  | m + 1, hm, d, hd, fs, hfs, stk, i, hi => by
    have hm' : m ≤ K := Nat.le_of_succ_le hm
    have hd_lt : d < K := by omega
    have hd' : m + (d + 1) = K := by omega
    rw [Function.iterate_succ_apply]
    dsimp only [fftSplitStep]
    rw [splitBlocks_map_finRange_eq_splitFnList,
      deinterleaveList_fst_twStage K leafTwiddles d hd_lt]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | h_eq
    · rcases fftCombineStep_iterate_lt_spec leafTwiddles m hm' (d + 1) hd'
        (splitFnList m fs) (forall_mem_splitFnList m fs hfs)
        (twStage K leafTwiddles d :: stk) i hi_lt with
        ⟨gs, stk_rest, heq, hlen_gs, hbds_gs⟩
      refine ⟨gs, stk_rest, heq, ?_, hbds_gs⟩
      rw [hlen_gs, length_splitFnList]
      calc 2 ^ (m - 1 - i) * (2 * fs.length)
          = (2 ^ (m - 1 - i) * 2) * fs.length := by ring
        _ = 2 ^ ((m - 1 - i) + 1) * fs.length := by rw [← Nat.pow_succ]
        _ = 2 ^ ((m + 1) - 1 - i) * fs.length := by
            rw [show (m - 1 - i) + 1 = (m + 1) - 1 - i by omega]
    · cases h_eq
      refine ⟨fs, stk, ?_, by simp, hfs⟩
      have heq := fftCombineStep_iterate_fftSplitStep_iterate leafTwiddles m hm' (d + 1) hd'
        (splitFnList m fs) (twStage K leafTwiddles d :: stk)
      dsimp only at heq
      rw [heq, map_splitFnList]
      have hd_eq : d = K - 1 - m := by omega
      rw [hd_eq]

/-- Prepend a single encoded element `encElem x` onto an encoded list `encList encElem xs`. -/
def bmConsList : BitMachine :=
  bmSeq (bmMapFst bmSingletonList) bmAppendList

theorem StageEval.consList {S α : Type} (encElem : S → α → List Bool)
    (x : S → α) (xs : S → List α) :
    StageEval bmConsList
      (encDepPair (fun s => encElem s (x s)) (fun s => encList (encElem s) (xs s)))
      (fun s => encList (encElem s) (x s :: xs s))
      (fun s => 60 * (encElem s (x s)).length + 30 * (encList (encElem s) (xs s)).length + 100) := by
  have pSing : StageEval bmSingletonList
      (fun s => encElem s (x s))
      (fun s => encList (encElem s) [x s])
      (fun s => 2 * (encElem s (x s)).length + 5) := by
    intro s tW2 tW3 tW4 tW5 tSch
    exact StageEval.of_computesStageLe (bmSingletonList_computesStageLe (encElem s))
      x s tW2 tW3 tW4 tW5 tSch
  have p1 := StageEval.mapFst (u2 := fun s => encList (encElem s) (xs s)) pSing
  have p2 := StageEval.congr_out
    (v2 := fun s => encList (encElem s) (x s :: xs s))
    (StageEval.appendList encElem (fun s => [x s]) xs)
    (fun _ => rfl)
  refine (StageEval.seq p1 p2).mono (fun s => ?_)
  simp only [encList_cons, encList_nil, List.append_nil, length_encodeDelimWord]
  omega

theorem tmTailWords_encList_cons_computesInTime {α : Type} (encElem : α → List Bool)
    (x : α) (xs : List α) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * (encElem x).length + 4,
      (tmTailWords kIO).ComputesInTime
        (mkTapes8 (encodeDelimWord (encList encElem (x :: xs))) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem xs)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have h1 := tmTailWords_computesInTime kIO (encList encElem (x :: xs)) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, encList_cons,
    unconsDelimWord_encodeDelimWord_append] at h1
  exact ⟨(encElem x).length + 1, by omega, h1⟩

/-- Encoding of `SplitState q` at word-width `W`. -/
def encSplitState (W : ℕ) {q : ℕ} (st : SplitState q) : List Bool :=
  encPair (encList (encList (encComplex W)))
    (encPair (encList (encComplex W)) (encList (encList (encComplex W)))) st

/-- **Top-Down Radix-2 FFT Split Step (`bmFFTSplitStep`)**:
Consumes `encSplitState W (blks, (tw, stk))` and emits
`encSplitState W (splitBlocks blks, ((deinterleaveList tw).1, tw :: stk))`. -/
def bmFFTSplitStep : BitMachine :=
  bmFanout
    (bmSeq bmFst bmSplitBlocks)
    (bmFanout
      (bmSeq (bmSeq bmSnd bmFst) (bmSeq bmDeinterleaveList bmFst))
      (bmSeq (bmFanout (bmSeq bmSnd bmFst) (bmSeq bmSnd bmSnd)) bmConsList))

theorem bmFFTSplitStep_computesInTime {K q W : ℕ}
    (blks : List (List (FixedComplex q)))
    (tw : List (FixedComplex q))
    (stk : List (List (FixedComplex q)))
    (d : ℕ) (hd : d < K)
    (hblks_len : blks.length = 2 ^ d)
    (hblk_each : ∀ b ∈ blks, b.length = 2 ^ (K - d))
    (htw_len : tw.length = 2 ^ (K - d))
    (hstk_len : (encList (encList (encComplex W)) stk).length ≤ 2 ^ K * (32 * W + 76))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 ^ K * (15000 * W + 35000) + 5000,
      bmFFTSplitStep.ComputesInTime
        (mkTapes8 (encodeDelimWord (encSplitState W (blks, (tw, stk))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encSplitState W (fftSplitStep (blks, (tw, stk)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uBlks : S → List Bool := fun _ => encList (encList (encComplex W)) blks
  let uTw : S → List Bool := fun _ => encList (encComplex W) tw
  let uStk : S → List Bool := fun _ => encList (encList (encComplex W)) stk
  let uTwStk : S → List Bool := encDepPair uTw uStk
  let uIn : S → List Bool := encDepPair uBlks uTwStk
  have hpow_split : 2 ^ d * 2 ^ (K - d) = 2 ^ K := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hd)]
  have h2d_le : 2 ^ d ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hd)
  have h2Kd_le : 2 ^ (K - d) ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) (Nat.sub_le K d)
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hL_blk : ∀ b ∈ blks, (encList (encComplex W) b).length ≤ 2 ^ (K - d) * (8 * W + 18) := by
    intro b hb
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) b (fun _ _ => by simp)
    rw [hblk_each b hb] at h
    exact h.trans (le_of_eq (by ring))
  have hlen_blks : (encList (encList (encComplex W)) blks).length ≤ 2 ^ K * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W))
      (2 ^ (K - d) * (8 * W + 18)) blks hL_blk
    rw [hblks_len] at h
    have h2 : 2 ^ d * (2 * (2 ^ (K - d) * (8 * W + 18)) + 2) =
        (2 ^ d * 2 ^ (K - d)) * (16 * W + 36) + 2 ^ d * 2 := by ring
    rw [h2, hpow_split] at h
    linarith [h, h2d_le]
  have hlen_tw : (encList (encComplex W) tw).length ≤ 2 ^ K * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) tw (fun _ _ => by simp)
    rw [htw_len] at h
    have h2 : 2 ^ (K - d) * (2 * (4 * W + 8) + 2) ≤ 2 ^ K * (2 * (4 * W + 8) + 2) :=
      Nat.mul_le_mul_right _ h2Kd_le
    exact (h.trans h2).trans (le_of_eq (by ring))
  have pFst := StageEval.fst uBlks uTwStk
  have pSnd := StageEval.snd uBlks uTwStk
  have pTw := StageEval.seq pSnd (StageEval.fst uTw uStk)
  have pStk := StageEval.seq pSnd (StageEval.snd uTw uStk)
  have pSplitBlks : StageEval (bmSeq bmFst bmSplitBlocks) uIn
      (fun _ => encList (encList (encComplex W)) (splitBlocks blks))
      (fun _ => 2 ^ K * (1800 * W + 4500) + 500) := by
    refine (StageEval.seq pFst
      (StageEval.splitBlocks_stage (fun _ : S => encComplex W)
        (fun _ => blks) (fun _ => 2 ^ (K - d) * (8 * W + 18))
        (fun _ => hL_blk))).mono (fun _ => ?_)
    dsimp only [uIn, uBlks, uTwStk, uTw, uStk]
    rw [hblks_len]
    have hmul : 2 ^ d * (200 * (2 ^ (K - d) * (8 * W + 18)) + 400) =
        (2 ^ d * 2 ^ (K - d)) * (1600 * W + 3600) + 400 * 2 ^ d := by ring
    rw [hmul, hpow_split]
    simp only [length_encDepPair]
    linarith [hlen_blks, hlen_tw, hstk_len, h2d_le, h2K_pos]
  have pDeintTw : StageEval (bmSeq (bmSeq bmSnd bmFst) (bmSeq bmDeinterleaveList bmFst)) uIn
      (fun _ => encList (encComplex W) (deinterleaveList tw).1)
      (fun _ => 2 ^ K * (600 * W + 1500) + 300) := by
    have pD := StageEval.seq
      (StageEval.deinterleaveList_stage (fun _ : S => encComplex W) (fun _ => tw))
      (StageEval.fst
        (fun _ : S => encList (encComplex W) (deinterleaveList tw).1)
        (fun _ : S => encList (encComplex W) (deinterleaveList tw).2))
    refine (StageEval.seq pTw pD).mono (fun _ => ?_)
    dsimp only [uIn, uBlks, uTwStk, uTw, uStk]
    have hsum := length_encList_deinterleaveList (encComplex W) tw
    simp only [length_encDepPair]
    linarith [hlen_blks, hlen_tw, hstk_len, hsum, h2K_pos]
  have pConsStk : StageEval
      (bmSeq (bmFanout (bmSeq bmSnd bmFst) (bmSeq bmSnd bmSnd)) bmConsList) uIn
      (fun _ => encList (encList (encComplex W)) (tw :: stk))
      (fun _ => 2 ^ K * (3000 * W + 7000) + 300) := by
    refine (StageEval.seq (StageEval.fanout pTw pStk)
      (StageEval.consList (fun _ : S => encList (encComplex W))
        (fun _ => tw) (fun _ => stk))).mono (fun _ => ?_)
    dsimp only [uIn, uBlks, uTwStk, uTw, uStk]
    simp only [length_encDepPair]
    have h2KW_nonneg : 0 ≤ 2 ^ K * W := Nat.zero_le _
    linarith [hlen_blks, hlen_tw, hstk_len, h2K_pos, h2KW_nonneg]
  have pAll := StageEval.fanout pSplitBlks (StageEval.fanout pDeintTw pConsStk)
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uBlks, uTwStk, uTw, uStk, id] at ht_step
  simp only [length_encDepPair] at ht_step
  dsimp only [uIn, uBlks, uTwStk, uTw, uStk, encDepPair, id] at hcomp
  refine ⟨t, ?_, hcomp⟩
  have hsplit_len : (encList (encList (encComplex W)) (splitBlocks blks)).length ≤
      2 ^ K * (32 * W + 76) := by
    rw [length_encList_splitBlocks, hblks_len]
    have h2KW_nonneg : 0 ≤ 2 ^ K * W := Nat.zero_le _
    linarith [hlen_blks, h2d_le, h2KW_nonneg]
  have hdeint_len : (encList (encComplex W) (deinterleaveList tw).1).length ≤
      2 ^ K * (8 * W + 18) := by
    have hsum := length_encList_deinterleaveList (encComplex W) tw
    linarith [hsum, hlen_tw]
  have hcons_stk_len : (encList (encList (encComplex W)) (tw :: stk)).length ≤
      2 ^ K * (48 * W + 114) := by
    simp only [encList_cons, List.length_append, length_encodeDelimWord]
    have h2KW_nonneg : 0 ≤ 2 ^ K * W := Nat.zero_le _
    linarith [hlen_tw, hstk_len, h2K_pos, h2KW_nonneg]
  have h2KW_nonneg : 0 ≤ 2 ^ K * W := Nat.zero_le _
  linarith [ht_step, hlen_blks, hlen_tw, hstk_len, hsplit_len, hdeint_len, hcons_stk_len, h2K_pos, h2KW_nonneg]

/-- Encoding of `((W, q), (stk, blks))` for the bottom-up combine loop. -/
def encCombLoopState (W q : ℕ) (st : CombState q) : List Bool :=
  encPair (encPair encUnary encUnary)
    (encPair (encList (encList (encComplex W))) (encList (encList (encComplex W))))
    ((W, q), st)

/-- Sub-stage of `bmFFTCombineStep`: maps `bmButterflyBlock bmMul` over `pairBlocks blks`
with context `((W, q), tw)`. -/
def bmFFTCombineBlocks (bmMul : BitMachine) : BitMachine :=
  bmSeq
    (bmFanout
      (bmFanout bmFst (bmSeq (bmSeq bmSnd bmFst) bmFst))
      (bmSeq (bmSeq bmSnd bmSnd) bmPairBlocks))
    (bmMapWithCtx (bmButterflyBlock bmMul))

/-- **Bottom-Up Radix-2 FFT Combine Step (`bmFFTCombineStep bmMul`)**:
Consumes `encCombLoopState W q (stk, blks)` on `kIO` and emits
`encCombLoopState W q (fftCombineStep (stk, blks))`. -/
def bmFFTCombineStep (bmMul : BitMachine) : BitMachine :=
  bmFanout
    bmFst
    (bmFanout
      (bmSeq (bmSeq bmSnd bmFst) (tmTailWords kIO))
      (bmFFTCombineBlocks bmMul))

theorem bmFFTCombineStep_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    {K q W0 W : ℕ}
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (htw : ∀ u : Fin (2 ^ K), WordWidthBounds (q + 2) (leafTwiddles u))
    (hW0 : 1 ≤ W0) (hqW : q + 2 ≤ W) (hKW : W0 + 4 * K ≤ W)
    (i : ℕ) (hi : i < K)
    (gs : List (Fin (2 ^ (i + 1)) → FixedComplex q))
    (hgs_len : gs.length = 2 ^ (K - 1 - i))
    (hgs_bds : ∀ g ∈ gs, ∀ j : Fin (2 ^ (i + 1)), WordWidthBounds W0 (g j))
    (stk_rest : List (List (FixedComplex q)))
    (hstk_len : (encList (encList (encComplex W))
      (twStage K leafTwiddles (K - 1 - i) :: stk_rest)).length ≤ 2 ^ K * (32 * W + 76))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let hi_le : i ≤ K := Nat.le_of_lt hi
    let tw := twStage K leafTwiddles (K - 1 - i)
    let stk := tw :: stk_rest
    let fE : (Fin (2 ^ (i + 1)) → FixedComplex q) → List (FixedComplex q) :=
      fun g => (List.finRange (2 ^ i)).map (radix2FFT1DFixed K q leafTwiddles i hi_le (eFn i g))
    let fO : (Fin (2 ^ (i + 1)) → FixedComplex q) → List (FixedComplex q) :=
      fun g => (List.finRange (2 ^ i)).map (radix2FFT1DFixed K q leafTwiddles i hi_le (oFn i g))
    let blks := gs.flatMap (fun g => [fE g, fO g])
    ∃ t ≤ 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600000),
      (bmFFTCombineStep bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encCombLoopState W q (stk, blks)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encCombLoopState W q (fftCombineStep (stk, blks))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro hi_le tw stk fE fO blks
  let S := Unit
  let M := 2 ^ i
  let B := 2 ^ (K - 1 - i)
  have hM_pos : 1 ≤ M := Nat.one_le_two_pow
  have hB_pos : 1 ≤ B := Nat.one_le_two_pow
  have hBM_pow : B * M = 2 ^ (K - 1) := by
    dsimp only [B, M]
    rw [← Nat.pow_add, show K - 1 - i + i = K - 1 by omega]
  have hBM_le : B * M ≤ 2 ^ K := by
    rw [hBM_pow]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2BM : 2 * (B * M) = 2 ^ K := by
    rw [hBM_pow]
    conv_rhs => rw [show K = (K - 1) + 1 by omega, Nat.pow_succ']
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hW_le_2KW : W ≤ 2 ^ K * W := Nat.le_mul_of_pos_left W h2K_pos
  have hq_le_2Kq : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have htw_len : tw.length = 2 * M := by
    dsimp only [tw, M]
    rw [length_twStage, show K - (K - 1 - i) = i + 1 by omega, Nat.pow_succ']
  have htw_bds : ∀ w ∈ tw, WordWidthBounds W w :=
    mem_twStage_bounds K leafTwiddles (fun u => (htw u).mono hqW) (K - 1 - i)
  have hfE_bds : ∀ g ∈ gs, ∀ e ∈ fE g, WordWidthBounds (W0 + 4 * i) e := by
    intro g hg e he
    rcases List.mem_map.mp he with ⟨u, _, rfl⟩
    exact (radix2FFT1DFixedWithMul_eq_and_bounds (· * ·) K q W0 (W0 + 4 * i + q + 2)
      (fun _ _ _ _ => rfl) leafTwiddles htw (by omega) i hi_le (eFn i g)
      (fun j => hgs_bds g hg (evenSubIndex i j)) hW0 (by omega)).2 u
  have hfO_bds : ∀ g ∈ gs, ∀ o ∈ fO g, WordWidthBounds (W0 + 4 * i) o := by
    intro g hg o ho
    rcases List.mem_map.mp ho with ⟨u, _, rfl⟩
    exact (radix2FFT1DFixedWithMul_eq_and_bounds (· * ·) K q W0 (W0 + 4 * i + q + 2)
      (fun _ _ _ _ => rfl) leafTwiddles htw (by omega) i hi_le (oFn i g)
      (fun j => hgs_bds g hg (oddSubIndex i j)) hW0 (by omega)).2 u
  let uWQ : S → List Bool := fun _ => encPair encUnary encUnary (W, q)
  let uStk : S → List Bool := fun _ => encList (encList (encComplex W)) stk
  let uBlks : S → List Bool := fun _ => encList (encList (encComplex W)) blks
  let uComb : S → List Bool := encDepPair uStk uBlks
  let uIn : S → List Bool := encDepPair uWQ uComb
  have hlen_tw : (encList (encComplex W) tw).length ≤ 2 ^ K * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) tw (fun _ _ => by simp)
    rw [htw_len] at h
    have h2M_le : 2 * M ≤ 2 ^ K := by
      have : 2 * (1 * M) ≤ 2 * (B * M) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right M hB_pos)
      omega
    have h2 : (2 * M) * (2 * (4 * W + 8) + 2) ≤ 2 ^ K * (2 * (4 * W + 8) + 2) :=
      Nat.mul_le_mul_right _ h2M_le
    exact (h.trans h2).trans (le_of_eq (by ring))
  have hlen_stk_rest :
      (encList (encList (encComplex W)) stk_rest).length ≤ 2 ^ K * (32 * W + 76) := by
    have h := length_encList_drop_le (encList (encComplex W)) 1 stk
    exact h.trans hstk_len
  have hblks_len : blks.length = 2 * B := by
    have h : ∀ l : List (Fin (2 ^ (i + 1)) → FixedComplex q),
        (l.flatMap (fun g => [fE g, fO g])).length = 2 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons g tl ih => simp [ih]; omega
    rw [h gs, hgs_len]
  have hblk_each : ∀ b ∈ blks, (encList (encComplex W) b).length ≤ M * (8 * W + 18) := by
    intro b hb
    rcases List.mem_flatMap.mp hb with ⟨g, _, hb_in⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_in
    rcases hb_in with rfl | rfl
    · have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) (fE g) (fun _ _ => by simp)
      have hl : (fE g).length = M := by simp [fE, M]
      rw [hl] at h; exact h.trans (le_of_eq (by ring))
    · have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) (fO g) (fun _ _ => by simp)
      have hl : (fO g).length = M := by simp [fO, M]
      rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have hlen_blks : (encList (encList (encComplex W)) blks).length ≤ 2 ^ K * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W))
      (M * (8 * W + 18)) blks hblk_each
    rw [hblks_len] at h
    have h2 : (2 * B) * (2 * (M * (8 * W + 18)) + 2) =
        (2 * (B * M)) * (16 * W + 36) + (2 * B) * 2 := by ring
    rw [h2, h2BM] at h
    have h2B_le : 2 * B ≤ 2 ^ K := by
      have : 2 * (B * 1) ≤ 2 * (B * M) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left B hM_pos)
      omega
    linarith [h, h2B_le]
  have pFst := StageEval.fst uWQ uComb
  have pSnd := StageEval.snd uWQ uComb
  have pStk := StageEval.seq pSnd (StageEval.fst uStk uBlks)
  have pBlks := StageEval.seq pSnd (StageEval.snd uStk uBlks)
  have pTailStk : StageEval (bmSeq (bmSeq bmSnd bmFst) (tmTailWords kIO)) uIn
      (fun _ => encList (encList (encComplex W)) stk.tail)
      (fun _ => 2 ^ K * (400 * W + 1000) + 30 * (W + q) + 200) := by
    refine (StageEval.seq pStk
      (StageEval.const (S := S) (tmTailWords_encList_cons_computesInTime
        (encList (encComplex W)) tw stk_rest))).mono (fun _ => ?_)
    dsimp only [uIn, uWQ, uComb, uStk, uBlks, stk]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hstk_len, hlen_blks, hlen_tw, h2K_pos]
  have pHeadTw : StageEval (bmSeq (bmSeq bmSnd bmFst) bmFst) uIn
      (fun _ => encList (encComplex W) tw)
      (fun _ => 2 ^ K * (400 * W + 1000) + 30 * (W + q) + 200) := by
    refine (StageEval.seq pStk
      (StageEval.const (S := S) (bmFst_encList_cons_computesInTime
        (encList (encComplex W)) tw stk_rest))).mono (fun _ => ?_)
    dsimp only [uIn, uWQ, uComb, uStk, uBlks, stk]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hstk_len, hlen_stk_rest, hlen_blks, hlen_tw, h2K_pos]
  have pCtx : StageEval (bmFanout bmFst (bmSeq (bmSeq bmSnd bmFst) bmFst)) uIn
      (fun _ => encPair (encPair encUnary encUnary) (encList (encComplex W)) ((W, q), tw))
      (fun _ => 2 ^ K * (2000 * W + 5000) + 100 * (W + q) + 600) := by
    refine (StageEval.fanout pFst pHeadTw).mono (fun _ => ?_)
    dsimp only [uIn, uWQ, uComb, uStk, uBlks, stk]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hstk_len, hlen_blks, hlen_tw, h2K_pos]
  have pPairs : StageEval (bmSeq (bmSeq bmSnd bmSnd) bmPairBlocks) uIn
      (fun _ => encList (encPair (encList (encComplex W)) (encList (encComplex W)))
        (pairBlocks blks))
      (fun _ => 2 ^ K * (3000 * W + 7000) + 30 * (W + q) + 500) := by
    have pPB := StageEval.congr_out
      (v2 := fun _ : S => encList (encPair (encList (encComplex W)) (encList (encComplex W)))
        (pairBlocks blks))
      (StageEval.pairBlocks_stage (fun _ : S => encComplex W)
        (fun _ => gs) (fun _ => fE) (fun _ => fO))
      (fun _ => by dsimp only [blks]; rw [pairBlocks_flatMap_two])
    refine (StageEval.seq pBlks pPB).mono (fun _ => ?_)
    dsimp only [uIn, uWQ, uComb, uStk, uBlks, stk, blks]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hstk_len, hlen_blks, h2K_pos]
  let SubP := { p : S × (List (FixedComplex q) × List (FixedComplex q)) //
    p.2 ∈ pairBlocks blks }
  have pBflyBody : StageEval (S := SubP) (bmButterflyBlock bmMul)
      (encDepPair
        (fun _ => encPair (encPair encUnary encUnary) (encList (encComplex W)) ((W, q), tw))
        (fun p => encPair (encList (encComplex W)) (encList (encComplex W)) p.val.2))
      (fun p => encList (encComplex W) (fftButterflyBlock tw p.val.2))
      (fun _ => M * (8 * mulTime W + 115000 * W + 18000 * q + 330000) + 3000 * (W + q) + 10000) := by
    intro ⟨⟨_, ⟨E, O⟩⟩, hmem⟩ u2 u3 u4 u5 uS
    have hmem' : (E, O) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, hg, hpair_eq⟩
    cases hpair_eq
    have hE_len : (fE g).length = M := by simp [fE, M]
    have hO_len : (fO g).length = M := by simp [fO, M]
    have hE_bds : ∀ e ∈ fE g, WordWidthBounds W e :=
      fun e he => (hfE_bds g hg e he).mono (by omega)
    have hO_bds : ∀ o ∈ fO g, WordWidthBounds W o :=
      fun o ho => (hfO_bds g hg o ho).mono (by omega)
    have hmul_bds : ∀ o ∈ fO g, ∀ w ∈ tw, WordWidthBounds W (FixedComplex.mulRounded w o) := by
      intro o ho w hw
      have ho' := hfO_bds g hg o ho
      have hw' : WordWidthBounds (q + 2) w :=
        mem_twStage_bounds K leafTwiddles htw (K - 1 - i) w hw
      exact (WordWidthBounds.mulRounded_sub_left hw' ho').mono (by omega)
    exact bmButterflyBlock_computesInTime hmul W q M hM_pos tw (fE g) (fO g)
      hE_len hO_len (by omega) (by omega) hE_bds hO_bds htw_bds hmul_bds u2 u3 u4 u5 uS
  have hpair_len : (pairBlocks blks).length = B := by
    dsimp only [blks]
    rw [pairBlocks_flatMap_two, List.length_map, hgs_len]
  have hLA : ∀ (s : S) (eo : List (FixedComplex q) × List (FixedComplex q)),
      eo ∈ pairBlocks blks →
      (encPair (encList (encComplex W)) (encList (encComplex W)) eo).length ≤
        M * (32 * W + 76) := by
    intro _ ⟨E, O⟩ hmem
    have hmem' : (E, O) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, _, hpair_eq⟩
    cases hpair_eq
    have hE := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) (fE g) (fun _ _ => by simp)
    have hO := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) (fO g) (fun _ _ => by simp)
    have hEl : (fE g).length = M := by simp [fE, M]
    have hOl : (fO g).length = M := by simp [fO, M]
    rw [hEl] at hE; rw [hOl] at hO
    simp only [length_encPair]
    linarith [hE, hO, hM_pos]
  have hLB : ∀ (s : S) (eo : List (FixedComplex q) × List (FixedComplex q)),
      eo ∈ pairBlocks blks →
      (encList (encComplex W) (fftButterflyBlock tw eo)).length ≤ M * (16 * W + 36) := by
    intro _ ⟨E, O⟩ hmem
    have hmem' : (E, O) ∈ gs.map (fun g => (fE g, fO g)) := by
      simpa [blks, pairBlocks_flatMap_two] using hmem
    rcases List.mem_map.mp hmem' with ⟨g, _, hpair_eq⟩
    cases hpair_eq
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      (fftButterflyBlock tw (fE g, fO g)) (fun _ _ => by simp)
    have hlen_bfly : (fftButterflyBlock tw (fE g, fO g)).length = 2 * M := by
      unfold fftButterflyBlock
      rw [length_unzipAppendList]
      simp [fE, fO, M, htw_len]
    rw [hlen_bfly] at h
    exact h.trans (le_of_eq (by ring))
  have hlen_pairs :
      (encList (encPair (encList (encComplex W)) (encList (encComplex W)))
        (pairBlocks blks)).length ≤ 2 ^ K * (32 * W + 78) := by
    have h := length_encList_le_of_forall_le
      (encPair (encList (encComplex W)) (encList (encComplex W)))
      (M * (32 * W + 76)) (pairBlocks blks) (hLA ())
    rw [hpair_len] at h
    have h2 : B * (2 * (M * (32 * W + 76)) + 2) =
        (B * M) * (64 * W + 152) + B * 2 := by ring
    rw [h2, hBM_pow] at h
    have h2K1 : 2 * 2 ^ (K - 1) = 2 ^ K := by
      conv_rhs => rw [show K = (K - 1) + 1 by omega, Nat.pow_succ']
    have hB_le : B ≤ 2 ^ (K - 1) := by
      have : B * 1 ≤ B * M := Nat.mul_le_mul_left B hM_pos
      omega
    nlinarith [h, h2K1, hB_le]
  have pCombineBlks : StageEval (bmFFTCombineBlocks bmMul) uIn
      (fun _ => encList (encList (encComplex W)) (fftCombineBlocks tw blks))
      (fun _ => 2 ^ K * (8 * mulTime W + 140000 * W + 24000 * q + 380000)) := by
    refine (StageEval.seq (StageEval.fanout pCtx pPairs)
      (StageEval.mapWithCtx_uniform
        (ctx := fun _ : S => encPair (encPair encUnary encUnary) (encList (encComplex W)) ((W, q), tw))
        (xs := fun _ => pairBlocks blks)
        (encA := fun _ => encPair (encList (encComplex W)) (encList (encComplex W)))
        (encB := fun _ => encList (encComplex W))
        (fn := fun _ eo => fftButterflyBlock tw eo)
        (B := fun _ => M * (8 * mulTime W + 115000 * W + 18000 * q + 330000) + 3000 * (W + q) + 10000)
        (L_A := fun _ => M * (32 * W + 76))
        (L_B := fun _ => M * (16 * W + 36))
        pBflyBody hLA hLB)).mono (fun _ => ?_)
    dsimp only [uIn, uWQ, uComb, uStk, uBlks, stk]
    rw [hpair_len]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have hBM_expand :
        B * (M * (8 * mulTime W + 115000 * W + 18000 * q + 330000) + 3000 * (W + q) + 10000 +
          4 * (2 * (2 * W + 2 * q + 4) + 2 * (encList (encComplex W) tw).length + 4) +
          6 * (M * (32 * W + 76)) + 20 * (M * (16 * W + 36)) + 40) =
        (B * M) * (8 * mulTime W + 115512 * W + 18000 * q + 331176) +
        B * (3016 * W + 3016 * q + 10088 + 8 * (encList (encComplex W) tw).length) := by ring
    rw [hBM_expand]
    have htw_2M : (encList (encComplex W) tw).length ≤ M * (16 * W + 36) := by
      have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) tw (fun _ _ => by simp)
      rw [htw_len] at h
      exact h.trans (le_of_eq (by ring))
    have hB_tw : B * (3016 * W + 3016 * q + 10088 + 8 * (encList (encComplex W) tw).length) ≤
        (B * M) * (4500 * W + 3200 * q + 14000) := by
      have h1 : 3016 * W + 3016 * q + 10088 + 8 * (encList (encComplex W) tw).length ≤
          M * (4500 * W + 3200 * q + 14000) := by
        have hM1 : 1 * (3016 * W + 3016 * q + 10088) ≤ M * (3016 * W + 3016 * q + 10088) :=
          Nat.mul_le_mul_right _ hM_pos
        have hM2 : 8 * (encList (encComplex W) tw).length ≤ M * (128 * W + 288) :=
          (Nat.mul_le_mul_left 8 htw_2M).trans (le_of_eq (by ring))
        have hM3 : M * (3016 * W + 3016 * q + 10088) + M * (128 * W + 288) ≤
            M * (4500 * W + 3200 * q + 14000) := by
          calc M * (3016 * W + 3016 * q + 10088) + M * (128 * W + 288)
              = M * (3144 * W + 3016 * q + 10376) := by ring
            _ ≤ M * (4500 * W + 3200 * q + 14000) := Nat.mul_le_mul_left M (by linarith only)
        linarith [hM1, hM2, hM3]
      exact (Nat.mul_le_mul_left B h1).trans (le_of_eq (by ring))
    have hBM_tot :
        (B * M) * (8 * mulTime W + 115512 * W + 18000 * q + 331176) +
        (B * M) * (4500 * W + 3200 * q + 14000) ≤
        2 ^ K * (8 * mulTime W + 122220 * W + 21200 * q + 350400) := by
      calc (B * M) * (8 * mulTime W + 115512 * W + 18000 * q + 331176) +
           (B * M) * (4500 * W + 3200 * q + 14000)
          = (B * M) * (8 * mulTime W + 120012 * W + 21200 * q + 345176) := by ring
        _ ≤ 2 ^ K * (8 * mulTime W + 122220 * W + 21200 * q + 350400) :=
            Nat.mul_le_mul hBM_le (by linarith only)
    linarith [hB_tw, hBM_tot, hstk_len, hlen_blks, hlen_tw, hlen_pairs, h2K_pos, hW_le_2KW, hq_le_2Kq]
  have hlen_comb_blks :
      (encList (encList (encComplex W)) (fftCombineBlocks tw blks)).length ≤
      2 ^ K * (16 * W + 38) := by
    have h := length_encList_le_of_forall_le (encList (encComplex W))
      (M * (16 * W + 36)) (fftCombineBlocks tw blks)
      (fun b hb => by
        unfold fftCombineBlocks at hb
        rcases List.mem_map.mp hb with ⟨eo, heo, rfl⟩
        exact hLB () eo heo)
    have hl : (fftCombineBlocks tw blks).length = B := by
      unfold fftCombineBlocks; rw [List.length_map, hpair_len]
    rw [hl] at h
    have h2 : B * (2 * (M * (16 * W + 36)) + 2) =
        (B * M) * (32 * W + 72) + B * 2 := by ring
    rw [h2, hBM_pow] at h
    have h2K1 : 2 * 2 ^ (K - 1) = 2 ^ K := by
      conv_rhs => rw [show K = (K - 1) + 1 by omega, Nat.pow_succ']
    have hB_le : B ≤ 2 ^ (K - 1) := by
      have : B * 1 ≤ B * M := Nat.mul_le_mul_left B hM_pos
      omega
    have h3 : 2 ^ (K - 1) * (32 * W + 72) + B * 2 ≤ 2 ^ K * (16 * W + 38) := by
      calc 2 ^ (K - 1) * (32 * W + 72) + B * 2
          ≤ 2 ^ (K - 1) * (32 * W + 72) + 2 ^ (K - 1) * 4 := by omega
        _ = (2 * 2 ^ (K - 1)) * (16 * W + 38) := by ring
        _ = 2 ^ K * (16 * W + 38) := by rw [h2K1]
    exact h.trans h3
  have pAll := StageEval.fanout pFst (StageEval.fanout pTailStk pCombineBlks)
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uWQ, uComb, uStk, uBlks, stk, id] at ht_step
  simp only [length_encDepPair, length_encPair, length_encUnary, List.tail_cons] at ht_step
  dsimp only [uIn, uWQ, uComb, uStk, uBlks, stk, encDepPair, id] at hcomp
  refine ⟨t, ?_, hcomp⟩
  have h2K_mul :
      2 ^ K * (8 * mulTime W + 140000 * W + 24000 * q + 380000) +
      2 ^ K * (100000 * W + 5000 * q + 200000) ≤
      2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600000) := by
    calc 2 ^ K * (8 * mulTime W + 140000 * W + 24000 * q + 380000) +
         2 ^ K * (100000 * W + 5000 * q + 200000)
        = 2 ^ K * (8 * mulTime W + 240000 * W + 29000 * q + 580000) := by ring
      _ ≤ 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600000) :=
          Nat.mul_le_mul_left _ (by omega)
  linarith [ht_step, h2K_mul, hstk_len, hlen_stk_rest, hlen_blks, hlen_comb_blks, h2K_pos, hW_le_2KW, hq_le_2Kq]

theorem StageEval.singletonList {S α : Type} (encElem : S → α → List Bool)
    (xs : S → List α) :
    StageEval bmSingletonList
      (fun s => encList (encElem s) (xs s))
      (fun s => encList (encList (encElem s)) [xs s])
      (fun s => 15 * (encList (encElem s) (xs s)).length + 40) := by
  intro s tW2 tW3 tW4 tW5 tSch
  rcases StageEval.of_computesStageLe
    (bmSingletonList_computesStageLe (encList (encElem s)))
    xs s tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht ⊢
  exact ⟨t, ht.trans (by omega), hcomp⟩

/-- Prepares `(K, ([xs0], (tw0, [])))` from `((K, (W, q)), (tw0, xs0))`. -/
def bmFFTSplitInit : BitMachine :=
  bmFanout
    (bmSeq bmFst bmFst)
    (bmFanout
      (bmSeq (bmSeq bmSnd bmSnd) bmSingletonList)
      (bmFanout (bmSeq bmSnd bmFst) bmConstEmpty))

/-- Runs the $K$-stage top-down split loop on `((K, (W, q)), (tw0, xs0))`. -/
def bmFFTSplitRun : BitMachine :=
  bmSeq bmFFTSplitInit (bmIterLoop bmFFTSplitStep)

/-- Prepares `(K, ((W, q), (splitOut.2.2, splitOut.1)))` from `((K, (W, q)), (tw0, xs0))`. -/
def bmFFTCombineInit : BitMachine :=
  bmSeq
    (bmFanout bmFst bmFFTSplitRun)
    (bmFanout
      (bmSeq bmFst bmFst)
      (bmFanout
        (bmSeq bmFst bmSnd)
        (bmFanout (bmSeq (bmSeq bmSnd bmSnd) bmSnd) (bmSeq bmSnd bmFst))))

/-- **1D $K$-Stage Cooley–Tukey Radix-2 Butterfly FFT (`bmRadix2FFT1DWith bmMul`)**:
Consumes `((K, (W, q)), (tw0, xs0))` on `kIO` and emits
`encList (encComplex W) ((List.finRange (2 ^ K)).map (radix2FFT1DFixed K q leafTwiddles K (le_refl K) x))`. -/
def bmRadix2FFT1DWith (bmMul : BitMachine) : BitMachine :=
  bmSeq
    (bmSeq bmFFTCombineInit (bmIterLoop (bmFFTCombineStep bmMul)))
    (bmSeq bmSnd (bmSeq bmSnd bmFst))

theorem bmRadix2FFT1DWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K q W0 W : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (htw : ∀ u : Fin (2 ^ K), WordWidthBounds (q + 2) (leafTwiddles u))
    (x : Fin (2 ^ K) → FixedComplex q)
    (hx : ∀ j : Fin (2 ^ K), WordWidthBounds W0 (x j))
    (hW0 : 1 ≤ W0) (hqW : q + 2 ≤ W) (hKW : W0 + 4 * K ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (K + 1) * 2 ^ K * (8 * mulTime W + 300000 * W + 40000 * q + 800000),
      (bmRadix2FFT1DWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary (encPair encUnary encUnary))
            (encPair (encList (encComplex W)) (encList (encComplex W)))
            ((K, (W, q)),
             ((List.finRange (2 ^ K)).map leafTwiddles,
              (List.finRange (2 ^ K)).map x))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W)
            ((List.finRange (2 ^ K)).map (radix2FFT1DFixed K q leafTwiddles K (le_refl K) x))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let tw0 := (List.finRange (2 ^ K)).map leafTwiddles
  let xs0 := (List.finRange (2 ^ K)).map x
  let splitSt0 : SplitState q := ([xs0], (twStage K leafTwiddles 0, []))
  let splitOut : SplitState q := (fftSplitStep^[K]) splitSt0
  let combSt0 : CombState q := (splitOut.2.2, splitOut.1)
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hK1_pos : 1 ≤ (K + 1) * 2 ^ K := Nat.mul_pos (Nat.succ_pos K) h2K_pos
  have hK_le : K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
  have hW_le : W ≤ 2 ^ K * W := Nat.le_mul_of_pos_left W h2K_pos
  have hq_le : q ≤ 2 ^ K * q := Nat.le_mul_of_pos_left q h2K_pos
  have hlen_tw0 : (encList (encComplex W) tw0).length ≤ 2 ^ K * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) tw0 (fun _ _ => by simp)
    have hl : tw0.length = 2 ^ K := by simp [tw0]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have hlen_xs0 : (encList (encComplex W) xs0).length ≤ 2 ^ K * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) xs0 (fun _ _ => by simp)
    have hl : xs0.length = 2 ^ K := by simp [xs0]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  let uK : S → List Bool := fun _ => encUnary K
  let uWQ : S → List Bool := fun _ => encPair encUnary encUnary (W, q)
  let uHdr : S → List Bool := encDepPair uK uWQ
  let uTw0 : S → List Bool := fun _ => encList (encComplex W) tw0
  let uXs0 : S → List Bool := fun _ => encList (encComplex W) xs0
  let uPay : S → List Bool := encDepPair uTw0 uXs0
  let uIn : S → List Bool := encDepPair uHdr uPay
  have pHdr := StageEval.fst uHdr uPay
  have pPay := StageEval.snd uHdr uPay
  have pK := StageEval.seq pHdr (StageEval.fst uK uWQ)
  have pTw0 := StageEval.seq pPay (StageEval.fst uTw0 uXs0)
  have pXs0 := StageEval.seq pPay (StageEval.snd uTw0 uXs0)
  have pSplitInit : StageEval bmFFTSplitInit uIn
      (encDepPair uK (fun _ => encSplitState W splitSt0))
      (fun _ => 2 ^ K * (1500 * W + 4000) + 200 * (W + q) + 1000) := by
    have pSing := StageEval.seq pXs0
      (StageEval.singletonList (fun _ : S => encComplex W) (fun _ => xs0))
    have pTwInit := StageEval.fanout
      (StageEval.congr_out (v2 := fun _ : S => encList (encComplex W) (twStage K leafTwiddles 0))
        pTw0 (fun _ => congrArg (encList (encComplex W)) (twStage_zero K leafTwiddles)))
      (StageEval.constEmpty uIn)
    refine (StageEval.fanout pK (StageEval.fanout pSing pTwInit)).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uPay, uK, uWQ, uTw0, uXs0]
    have htw_eq : (encList (encComplex W) (twStage K leafTwiddles 0)).length =
        (encList (encComplex W) tw0).length := by rw [← twStage_zero]
    simp only [length_encDepPair, length_encPair, length_encUnary, encList_cons, encList_nil,
      List.append_nil, length_encodeDelimWord, List.length_nil, htw_eq]
    linarith [hlen_tw0, hlen_xs0, hK_le, h2K_pos]
  let uSplitStage : ℕ → List Bool := fun d => encSplitState W ((fftSplitStep^[d]) splitSt0)
  have pSplitStep : StageEval (S := { p : S × ℕ // p.2 < K }) bmFFTSplitStep
      (fun p => uSplitStage p.val.2)
      (fun p => uSplitStage (p.val.2 + 1))
      (fun _ => 2 ^ K * (15000 * W + 35000) + 5000) := by
    intro ⟨⟨_, d⟩, hd⟩ u2 u3 u4 u5 uS
    dsimp only [uSplitStage, id]
    rw [Function.iterate_succ_apply']
    rcases fftSplitStep_iterate_spec (W := W) leafTwiddles d K 0 (Nat.le_of_lt hd) (by omega)
      [x] (fun f hf j => by simp at hf; subst hf; exact hx j) [] with
      ⟨fs_d, stk_d, heq, hlen_fs, _, hlen_stk⟩
    simp only [List.map, Nat.zero_add] at heq
    change (fftSplitStep^[d]) splitSt0 =
      (fs_d.map (fun g => (List.finRange (2 ^ (K - d))).map g),
       (twStage K leafTwiddles d, stk_d)) at heq
    rw [heq]
    have hblks_len : (fs_d.map (fun g => (List.finRange (2 ^ (K - d))).map g)).length = 2 ^ d := by
      simp [hlen_fs]
    have hblk_each : ∀ b ∈ fs_d.map (fun g => (List.finRange (2 ^ (K - d))).map g),
        b.length = 2 ^ (K - d) := by
      intro b hb
      rcases List.mem_map.mp hb with ⟨g, _, rfl⟩
      simp
    have hstk_le : (encList (encList (encComplex W)) stk_d).length ≤ 2 ^ K * (32 * W + 76) := by
      simp only [encList_nil, List.length_nil, Nat.zero_add, Nat.sub_zero] at hlen_stk
      exact hlen_stk.trans (Nat.mul_le_mul_right _ (Nat.sub_le (2 ^ K) _))
    exact bmFFTSplitStep_computesInTime _ _ _ d hd hblks_len hblk_each
      (length_twStage K leafTwiddles d) hstk_le u2 u3 u4 u5 uS
  have pSplitRun : StageEval bmFFTSplitRun uIn
      (fun _ => encSplitState W splitOut)
      (fun _ => (K + 1) * 2 ^ K * (17000 * W + 45000) + 200 * (W + q) + 2000) := by
    refine (StageEval.seq pSplitInit
      (StageEval.iterLoop_idx (k := fun _ : S => K) (u := fun _ => uSplitStage)
        (B := fun _ => 2 ^ K * (15000 * W + 35000) + 5000) pSplitStep)).mono (fun _ => ?_)
    dsimp only [uSplitStage, splitSt0]
    have htw_eq : (encList (encComplex W) (twStage K leafTwiddles 0)).length =
        (encList (encComplex W) tw0).length := by rw [← twStage_zero]
    simp only [encSplitState, length_encPair, encList_cons, encList_nil, List.append_nil,
      length_encodeDelimWord, List.length_nil, Function.iterate_zero, id_eq, htw_eq]
    have hmulK : K * (2 ^ K * (15000 * W + 35000) + 5000 + 3) ≤
        K * 2 ^ K * (15000 * W + 40003) := by
      have h1 : 2 ^ K * (15000 * W + 35000) + 5000 + 3 ≤ 2 ^ K * (15000 * W + 40003) := by
        nlinarith [h2K_pos]
      exact (Nat.mul_le_mul_left K h1).trans (le_of_eq (by ring))
    have hK1 : K * 2 ^ K * (15000 * W + 40003) + 2 ^ K * (1800 * W + 5000) ≤
        (K + 1) * 2 ^ K * (17000 * W + 45000) := by
      calc K * 2 ^ K * (15000 * W + 40003) + 2 ^ K * (1800 * W + 5000)
          ≤ K * 2 ^ K * (17000 * W + 45000) + 1 * 2 ^ K * (17000 * W + 45000) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (by simp; nlinarith [h2K_pos])
        _ = (K + 1) * 2 ^ K * (17000 * W + 45000) := by ring
    linarith [hmulK, hK1, hlen_tw0, hlen_xs0, h2K_pos]
  rcases fftSplitStep_iterate_spec (W := W) leafTwiddles K K 0 (le_refl K) (by omega)
    [x] (fun f hf j => by simp at hf; subst hf; exact hx j) [] with
    ⟨fs_K, stk_K, heq_K, hlen_fsK, _, hlen_stkK⟩
  have hsplitOut_1 : splitOut.1 = fs_K.map (fun g => (List.finRange (2 ^ (K - K))).map g) :=
    congrArg Prod.fst heq_K
  have hsplitOut_21 : splitOut.2.1 = twStage K leafTwiddles (0 + K) :=
    congrArg (fun p => p.2.1) heq_K
  have hsplitOut_22 : splitOut.2.2 = stk_K :=
    congrArg (fun p => p.2.2) heq_K
  have hlen_split1 : (encList (encList (encComplex W)) splitOut.1).length ≤
      2 ^ K * (16 * W + 38) := by
    rw [hsplitOut_1]
    have h := length_encList_le_of_forall_le (encList (encComplex W)) (8 * W + 18)
      (fs_K.map (fun g => (List.finRange (2 ^ (K - K))).map g))
      (fun b hb => by
        rcases List.mem_map.mp hb with ⟨g, _, rfl⟩
        have h1 := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
          ((List.finRange (2 ^ (K - K))).map g) (fun _ _ => by simp)
        simp only [List.length_map, List.length_finRange, Nat.sub_self, Nat.pow_zero,
          Nat.one_mul] at h1
        omega)
    have hl : (fs_K.map (fun g => (List.finRange (2 ^ (K - K))).map g)).length = 2 ^ K := by
      simp [hlen_fsK]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have hlen_split21 : (encList (encComplex W) splitOut.2.1).length ≤ 2 ^ K * (8 * W + 18) := by
    rw [hsplitOut_21, Nat.zero_add]
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8)
      (twStage K leafTwiddles K) (fun _ _ => by simp)
    rw [length_twStage, Nat.sub_self, Nat.pow_zero] at h
    have h2 : 1 * (2 * (4 * W + 8) + 2) ≤ 2 ^ K * (8 * W + 18) := by
      calc 1 * (2 * (4 * W + 8) + 2)
          ≤ 2 ^ K * (2 * (4 * W + 8) + 2) := Nat.mul_le_mul_right _ h2K_pos
        _ = 2 ^ K * (8 * W + 18) := by ring
    exact h.trans h2
  have hlen_split22 : (encList (encList (encComplex W)) splitOut.2.2).length ≤
      2 ^ K * (32 * W + 76) := by
    rw [hsplitOut_22]
    simp only [encList_nil, List.length_nil, Nat.zero_add, Nat.sub_zero] at hlen_stkK
    exact hlen_stkK.trans (Nat.mul_le_mul_right _ (Nat.sub_le (2 ^ K) _))
  have h2KW_nonneg : 0 ≤ 2 ^ K * W := Nat.zero_le _
  have h2Kq_nonneg : 0 ≤ 2 ^ K * q := Nat.zero_le _
  have hK2K_nonneg : 0 ≤ K * 2 ^ K := Nat.zero_le _
  have hK2KW_nonneg : 0 ≤ K * 2 ^ K * W := Nat.zero_le _
  have hK2Kq_nonneg : 0 ≤ K * 2 ^ K * q := Nat.zero_le _
  have pCombineInit : StageEval bmFFTCombineInit uIn
      (encDepPair uK (fun _ => encCombLoopState W q combSt0))
      (fun _ => (K + 1) * 2 ^ K * (28000 * W + 500 * q + 75000)) := by
    have pFan := StageEval.fanout pHdr pSplitRun
    let uMid := encDepPair uHdr (fun _ : S => encSplitState W splitOut)
    have mHdr := StageEval.fst uHdr (fun _ : S => encSplitState W splitOut)
    have mSp := StageEval.snd uHdr (fun _ : S => encSplitState W splitOut)
    have mK := StageEval.seq mHdr (StageEval.fst uK uWQ)
    have mWQ := StageEval.seq mHdr (StageEval.snd uK uWQ)
    have mB1 := StageEval.seq mSp
      (StageEval.fst (fun _ : S => encList (encList (encComplex W)) splitOut.1)
        (fun _ : S => encPair (encList (encComplex W)) (encList (encList (encComplex W))) splitOut.2))
    have mB2 := StageEval.seq mSp
      (StageEval.snd (fun _ : S => encList (encList (encComplex W)) splitOut.1)
        (fun _ : S => encPair (encList (encComplex W)) (encList (encList (encComplex W))) splitOut.2))
    have mB22 := StageEval.seq mB2
      (StageEval.snd (fun _ : S => encList (encComplex W) splitOut.2.1)
        (fun _ : S => encList (encList (encComplex W)) splitOut.2.2))
    have pRearr := StageEval.fanout mK (StageEval.fanout mWQ (StageEval.fanout mB22 mB1))
    refine (StageEval.seq pFan pRearr).mono (fun _ => ?_)
    dsimp only [uIn, uHdr, uPay, uK, uWQ, uTw0, uXs0, encSplitState]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_tw0, hlen_xs0, hlen_split1, hlen_split21, hlen_split22, hK_le, hW_le, hq_le,
      h2K_pos, h2KW_nonneg, h2Kq_nonneg, hK2K_nonneg, hK2KW_nonneg, hK2Kq_nonneg]
  let uCombStage : ℕ → List Bool := fun i => encCombLoopState W q ((fftCombineStep^[i]) combSt0)
  have pCombStep : StageEval (S := { p : S × ℕ // p.2 < K }) (bmFFTCombineStep bmMul)
      (fun p => uCombStage p.val.2)
      (fun p => uCombStage (p.val.2 + 1))
      (fun _ => 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600000)) := by
    intro ⟨⟨_, i⟩, hi⟩ u2 u3 u4 u5 uS
    dsimp only [uCombStage, id]
    rw [Function.iterate_succ_apply']
    rcases fftCombineStep_iterate_lt_spec leafTwiddles K (le_refl K) 0 (by omega)
      [x] (fun f hf j => by simp at hf; subst hf; exact hx j) [] i hi with
      ⟨gs, stk_rest, heq_i, hlen_gs, hbds_gs⟩
    dsimp only [List.map] at heq_i
    have hcomb_eq : (fftCombineStep^[i]) combSt0 =
        (twStage K leafTwiddles (K - 1 - i) :: stk_rest,
         gs.flatMap (fun g =>
           [(List.finRange (2 ^ i)).map
              (radix2FFT1DFixed K q leafTwiddles i (by omega) (eFn i g)),
            (List.finRange (2 ^ i)).map
              (radix2FFT1DFixed K q leafTwiddles i (by omega) (oFn i g))])) := heq_i
    rw [hcomb_eq]
    have hstk_i_eq :
        twStage K leafTwiddles (K - 1 - i) :: stk_rest = splitOut.2.2.drop i := by
      have h1 := congrArg Prod.fst hcomb_eq
      rw [fst_fftCombineStep_iterate] at h1
      exact h1.symm
    have hstk_i_len :
        (encList (encList (encComplex W))
          (twStage K leafTwiddles (K - 1 - i) :: stk_rest)).length ≤
        2 ^ K * (32 * W + 76) := by
      rw [hstk_i_eq]
      exact (length_encList_drop_le (encList (encComplex W)) i splitOut.2.2).trans hlen_split22
    exact bmFFTCombineStep_computesInTime hmul leafTwiddles htw hW0 hqW hKW i hi
      gs (by simpa using hlen_gs) hbds_gs stk_rest hstk_i_len u2 u3 u4 u5 uS
  let outList := (List.finRange (2 ^ K)).map (radix2FFT1DFixed K q leafTwiddles K (le_refl K) x)
  have hcomb_K : (fftCombineStep^[K]) combSt0 = ([], [outList]) := by
    simpa [combSt0, splitOut, splitSt0, xs0, outList] using
      fftCombineStep_iterate_fftSplitStep_iterate leafTwiddles K (le_refl K) 0 (by omega) [x] []
  have pCombRun : StageEval (bmSeq bmFFTCombineInit (bmIterLoop (bmFFTCombineStep bmMul))) uIn
      (fun _ => encCombLoopState W q ([], [outList]))
      (fun _ => (K + 1) * 2 ^ K * (8 * mulTime W + 280000 * W + 35000 * q + 700000)) := by
    refine (StageEval.seq pCombineInit
      (StageEval.congr_out
        (v2 := fun _ : S => encCombLoopState W q ([], [outList]))
        (StageEval.iterLoop_idx (k := fun _ : S => K) (u := fun _ => uCombStage)
          (B := fun _ => 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600000)) pCombStep)
        (fun _ => by dsimp only [uCombStage]; rw [hcomb_K]))).mono (fun _ => ?_)
    dsimp only [uCombStage, combSt0, encCombLoopState]
    simp only [Function.iterate_zero, id_eq, length_encPair, length_encUnary]
    have hmulK :
        K * (2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600000) + 3) ≤
        K * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) := by
      have h1 : 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600000) + 3 ≤
          2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) := by
        nlinarith [h2K_pos]
      exact (Nat.mul_le_mul_left K h1).trans (le_of_eq (by ring))
    have hK1 :
        (K + 1) * 2 ^ K * (28000 * W + 500 * q + 75000) +
        K * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) +
        2 ^ K * (2000 * W + 2000 * q + 10000) ≤
        (K + 1) * 2 ^ K * (8 * mulTime W + 280000 * W + 35000 * q + 700000) := by
      have hA : K * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) +
          2 ^ K * (2000 * W + 2000 * q + 10000) ≤
          (K + 1) * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) := by
        calc K * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) +
             2 ^ K * (2000 * W + 2000 * q + 10000)
            ≤ K * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) +
              1 * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) :=
                Nat.add_le_add le_rfl (by simp; nlinarith [h2K_pos])
          _ = (K + 1) * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) := by ring
      calc (K + 1) * 2 ^ K * (28000 * W + 500 * q + 75000) +
           K * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) +
           2 ^ K * (2000 * W + 2000 * q + 10000)
          = (K + 1) * 2 ^ K * (28000 * W + 500 * q + 75000) +
            (K * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) +
             2 ^ K * (2000 * W + 2000 * q + 10000)) := by ring
        _ ≤ (K + 1) * 2 ^ K * (28000 * W + 500 * q + 75000) +
            (K + 1) * 2 ^ K * (8 * mulTime W + 250000 * W + 30000 * q + 600003) :=
              Nat.add_le_add le_rfl hA
        _ = (K + 1) * 2 ^ K * (8 * mulTime W + 278000 * W + 30500 * q + 675003) := by ring
        _ ≤ (K + 1) * 2 ^ K * (8 * mulTime W + 280000 * W + 35000 * q + 700000) :=
              Nat.mul_le_mul_left _ (by omega)
    linarith [hmulK, hK1, hlen_split1, hlen_split22, hK_le, h2K_pos, h2KW_nonneg, h2Kq_nonneg, hW_le, hq_le]
  have hlen_out : (encList (encComplex W) outList).length ≤ 2 ^ K * (8 * W + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W) (4 * W + 8) outList (fun _ _ => by simp)
    have hl : outList.length = 2 ^ K := by simp [outList]
    rw [hl] at h; exact h.trans (le_of_eq (by ring))
  have pExtract : StageEval (bmSeq bmSnd (bmSeq bmSnd bmFst))
      (fun _ : S => encCombLoopState W q ([], [outList]))
      (fun _ => encList (encComplex W) outList)
      (fun _ => 2 ^ K * (200 * W + 500) + 50 * (W + q) + 200) := by
    have e1 := StageEval.snd
      (fun _ : S => encPair encUnary encUnary (W, q))
      (fun _ : S => encPair (encList (encList (encComplex W)))
        (encList (encList (encComplex W))) (([] : List (List (FixedComplex q))), [outList]))
    have e2 := StageEval.snd
      (fun _ : S => encList (encList (encComplex W)) ([] : List (List (FixedComplex q))))
      (fun _ : S => encList (encList (encComplex W)) [outList])
    have e3 := StageEval.const (S := S)
      (bmFst_encList_cons_computesInTime (encList (encComplex W)) outList [])
    refine (StageEval.seq e1 (StageEval.seq e2 e3)).mono (fun _ => ?_)
    simp only [length_encPair, length_encUnary, encList_cons, encList_nil,
      List.append_nil, length_encodeDelimWord, List.length_nil]
    linarith [hlen_out, h2K_pos]
  rcases (StageEval.seq pCombRun pExtract) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uHdr, uPay, uK, uWQ, uTw0, uXs0, encDepPair, id] at ht_step hcomp
  refine ⟨t, ?_, hcomp⟩
  have hdom : 2 ^ K * (300 * W + 800) + 100 * (W + q) + 400 ≤
      (K + 1) * 2 ^ K * (20000 * W + 5000 * q + 100000) := by
    have h1 : 2 ^ K * (300 * W + 800) + 100 * (W + q) + 400 ≤
        1 * (2 ^ K * (20000 * W + 5000 * q + 100000)) := by
      simp only [Nat.one_mul]
      have h2KW_nonneg : 0 ≤ 2 ^ K * W := Nat.zero_le _
      have h2Kq_nonneg : 0 ≤ 2 ^ K * q := Nat.zero_le _
      linarith [h2K_pos, hW_le, hq_le, h2KW_nonneg, h2Kq_nonneg]
    exact h1.trans ((Nat.mul_le_mul_right _ (Nat.le_add_left 1 K)).trans (le_of_eq (by ring)))
  have htot :
      (K + 1) * 2 ^ K * (8 * mulTime W + 280000 * W + 35000 * q + 700000) +
      (K + 1) * 2 ^ K * (20000 * W + 5000 * q + 100000) =
      (K + 1) * 2 ^ K * (8 * mulTime W + 300000 * W + 40000 * q + 800000) := by ring
  linarith [ht_step, hlen_out, hdom, htot]

/-! ### `bmRescaleComplexList` and `bmBaseRadix2FFTWith` -/

/-- **Linear-Time Complex List Precision Rescaling (`bmRescaleComplexList`)**:
Consumes `((W2, (q1, q2)), xs)` where `xs : List (FixedComplex q1)` is encoded at width `W1`,
and emits `encList (encComplex W2) (xs.map (FixedComplex.rescale q2))`. -/
def bmRescaleComplexList : BitMachine :=
  bmMapWithCtx bmComplexRescale

theorem bmRescaleComplexList_computesInTime (W1 W2 q1 q2 : ℕ)
    (xs : List (FixedComplex q1))
    (hxs1 : ∀ z ∈ xs, WordWidthBounds W1 z)
    (hxs2 : ∀ z ∈ xs, WordWidthBounds W2 (FixedComplex.rescale q2 z))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ xs.length * (18000 * W1 + 5000 * W2 + 32000 * q1 + 32000 * q2 + 70000) +
          50 * (W2 + q1 + q2) + 300,
      bmRescaleComplexList.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encList (encComplex W1))
            ((W2, (q1, q2)), xs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W2) (xs.map (FixedComplex.rescale q2))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uCtx : S → List Bool := fun _ =>
    encPair encUnary (encPair encUnary encUnary) (W2, (q1, q2))
  let SubZ := { p : S × FixedComplex q1 // p.2 ∈ xs }
  have pBody : StageEval (S := SubZ) bmComplexRescale
      (encDepPair (fun _ => uCtx ()) (fun p => encComplex W1 p.val.2))
      (fun p => encComplex W2 (FixedComplex.rescale q2 p.val.2))
      (fun _ => 16000 * W1 + 3000 * W2 + 30000 * q1 + 30000 * q2 + 65000) := by
    intro ⟨⟨_, z⟩, hz⟩ u2 u3 u4 u5 uS
    exact bmComplexRescale_computesInTime W1 W2 q1 q2 z (hxs1 z hz) (hxs2 z hz) u2 u3 u4 u5 uS
  have pMap := StageEval.mapWithCtx_uniform
    (ctx := uCtx)
    (xs := fun _ => xs)
    (encA := fun _ => encComplex W1)
    (encB := fun _ => encComplex W2)
    (fn := fun _ z => FixedComplex.rescale q2 z)
    (B := fun _ => 16000 * W1 + 3000 * W2 + 30000 * q1 + 30000 * q2 + 65000)
    (L_A := fun _ => 4 * W1 + 8)
    (L_B := fun _ => 4 * W2 + 8)
    pBody
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
  rcases pMap () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uCtx, encDepPair, id] at ht_step hcomp
  refine ⟨t, ?_, hcomp⟩
  simp only [length_encPair, length_encUnary] at ht_step
  have h1 :
      xs.length * (16000 * W1 + 3000 * W2 + 30000 * q1 + 30000 * q2 + 65000 +
        4 * (2 * W2 + 2 * (2 * q1 + 2 * q2 + 4) + 4) +
        6 * (4 * W1 + 8) + 20 * (4 * W2 + 8) + 40) ≤
      xs.length * (18000 * W1 + 5000 * W2 + 32000 * q1 + 32000 * q2 + 70000) :=
    Nat.mul_le_mul_left _ (by omega)
  linarith [ht_step, h1]

/-- Sub-stage 1 of `bmBaseRadix2FFTWith`: rescales input list from `(10 * (p + 2), p + 2)` to
`(6 * qBaseEll K p, qBaseEll K p)`. -/
def bmBaseFFTInRescale : BitMachine :=
  let bmKP := bmFst
  let bmP := bmSeq bmKP bmSnd
  let bmQIn := bmSeq (bmFanout bmP (bmUnaryConst 2)) bmUnaryAdd
  let bmQBase := bmSeq bmKP bmQBaseEll
  let bmWBase := bmSeq (bmFanout (bmUnaryConst 6) bmQBase) bmUnaryMul
  let bmCtxIn := bmFanout bmWBase (bmFanout bmQIn bmQBase)
  bmSeq (bmFanout bmCtxIn (bmSeq bmSnd bmSnd)) bmRescaleComplexList

/-- Sub-stage 2 of `bmBaseRadix2FFTWith`: runs `bmRadix2FFT1DWith bmMul` at `(6 * qBaseEll K p, qBaseEll K p)`. -/
def bmBaseFFTCoreWith (bmMul : BitMachine) : BitMachine :=
  let bmKP := bmFst
  let bmK := bmSeq bmKP bmFst
  let bmQBase := bmSeq bmKP bmQBaseEll
  let bmWBase := bmSeq (bmFanout (bmUnaryConst 6) bmQBase) bmUnaryMul
  let bmHdr := bmFanout bmK (bmFanout bmWBase bmQBase)
  bmSeq
    (bmFanout bmHdr (bmFanout (bmSeq bmSnd bmFst) bmBaseFFTInRescale))
    (bmRadix2FFT1DWith bmMul)

/-- **Leaf $K$-Stage Cooley–Tukey Radix-2 FFT (`bmBaseRadix2FFTWith bmMul`)**:
Consumes `((K, p), (tw0, xs0))` where `tw0 = (List.finRange (2 ^ K)).map leafTwiddles` at width
`6 * qBaseEll K p` and `xs0 = (List.finRange (2 ^ K)).map xFixed` at width `10 * (p + 2)`, and emits
`encList (encComplex (10 * (p + 2))) ((List.finRange (2 ^ K)).map (baseRadix2FFTFixed K p leafTwiddles xFixed))`. -/
def bmBaseRadix2FFTWith (bmMul : BitMachine) : BitMachine :=
  let bmKP := bmFst
  let bmP := bmSeq bmKP bmSnd
  let bmQIn := bmSeq (bmFanout bmP (bmUnaryConst 2)) bmUnaryAdd
  let bmWOut := bmSeq (bmFanout (bmUnaryConst 10) bmQIn) bmUnaryMul
  let bmQBase := bmSeq bmKP bmQBaseEll
  let bmCtxOut := bmFanout bmWOut (bmFanout bmQBase bmQIn)
  bmSeq (bmFanout bmCtxOut (bmBaseFFTCoreWith bmMul)) bmRescaleComplexList

theorem bmBaseRadix2FFTWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (htw : ∀ u : Fin (2 ^ K), WordWidthBounds (qBaseEll K p + 2) (leafTwiddles u))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx1 : ∀ j : Fin (2 ^ K), WordWidthBounds (10 * (p + 2)) (xFixed j))
    (hx_base : ∀ j : Fin (2 ^ K),
      WordWidthBounds (2 * qBaseEll K p) (FixedComplex.rescale (qBaseEll K p) (xFixed j)))
    (hout : ∀ u : Fin (2 ^ K),
      WordWidthBounds (10 * (p + 2)) (baseRadix2FFTFixed K p leafTwiddles xFixed u))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let qBase := qBaseEll K p
    let W_base := 6 * qBase
    let W_io := 10 * (p + 2)
    ∃ t ≤ (K + 1) * 2 ^ K * (8 * mulTime W_base + 2500000 * qBase + 1500000),
      (bmBaseRadix2FFTWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encList (encComplex W_base)) (encList (encComplex W_io)))
            ((K, p),
             ((List.finRange (2 ^ K)).map leafTwiddles,
              (List.finRange (2 ^ K)).map xFixed))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W_io)
            ((List.finRange (2 ^ K)).map (baseRadix2FFTFixed K p leafTwiddles xFixed))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro qBase W_base W_io
  let S := Unit
  let q_in := p + 2
  let tw0 := (List.finRange (2 ^ K)).map leafTwiddles
  let xs0 := (List.finRange (2 ^ K)).map xFixed
  let xBase : Fin (2 ^ K) → FixedComplex qBase :=
    fun j => FixedComplex.rescale qBase (xFixed j)
  let yBase : Fin (2 ^ K) → FixedComplex qBase :=
    radix2FFT1DFixed K qBase leafTwiddles K (le_refl K) xBase
  have hqBase_def : qBase = p + K + 4 := rfl
  have hW_base_def : W_base = 6 * qBase := rfl
  have hW_io_def : W_io = 10 * (p + 2) := rfl
  have hq_in_def : q_in = p + 2 := rfl
  have hqBase_pos : 4 ≤ qBase := by omega
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have h2Kq_nonneg : 0 ≤ 2 ^ K * qBase := Nat.zero_le _
  have hqBase_le_2K : qBase ≤ 2 ^ K * qBase := Nat.le_mul_of_pos_left qBase h2K_pos
  have hp_le_2K : p ≤ 2 ^ K * qBase := by linarith [hqBase_le_2K, hqBase_def]
  have hK_le_2K : K ≤ 2 ^ K * qBase := by linarith [hqBase_le_2K, hqBase_def]
  have hlen_tw0 : (encList (encComplex W_base) tw0).length ≤ 2 ^ K * (48 * qBase + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W_base) (4 * W_base + 8) tw0 (fun _ _ => by simp)
    have hl : tw0.length = 2 ^ K := by simp [tw0]
    rw [hl] at h
    exact h.trans (le_of_eq (by dsimp [W_base]; ring))
  have hlen_xs0 : (encList (encComplex W_io) xs0).length ≤ 2 ^ K * (80 * qBase + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W_io) (4 * W_io + 8) xs0 (fun _ _ => by simp)
    have hl : xs0.length = 2 ^ K := by simp [xs0]
    rw [hl] at h
    have hW_le : 2 * (4 * W_io + 8) + 2 ≤ 80 * qBase + 18 := by
      dsimp only [W_io]; omega
    exact (h.trans (Nat.mul_le_mul_left _ hW_le))
  let uKP : S → List Bool := fun _ => encPair encUnary encUnary (K, p)
  let uTw0 : S → List Bool := fun _ => encList (encComplex W_base) tw0
  let uXs0 : S → List Bool := fun _ => encList (encComplex W_io) xs0
  let uPay : S → List Bool := encDepPair uTw0 uXs0
  let uIn : S → List Bool := encDepPair uKP uPay
  have pKP := StageEval.fst uKP uPay
  have pPay := StageEval.snd uKP uPay
  have pK := StageEval.seq pKP (StageEval.fst (fun _ : S => encUnary K) (fun _ : S => encUnary p))
  have pP := StageEval.seq pKP (StageEval.snd (fun _ : S => encUnary K) (fun _ : S => encUnary p))
  have pTw0 := StageEval.seq pPay (StageEval.fst uTw0 uXs0)
  have pXs0 := StageEval.seq pPay (StageEval.snd uTw0 uXs0)
  have pQIn : StageEval (bmSeq (bmFanout (bmSeq bmFst bmSnd) (bmUnaryConst 2)) bmUnaryAdd) uIn
      (fun _ => encUnary q_in)
      (fun _ => 2 ^ K * (5000 * qBase + 2000)) := by
    refine (StageEval.seq
      (StageEval.fanout pP (StageEval.unaryConst 2 uIn))
      (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (p, 2)))).mono
      (fun _ => ?_)
    dsimp only [uIn, uKP, uPay, uTw0, uXs0]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_tw0, hlen_xs0, h2K_pos, h2Kq_nonneg, hqBase_le_2K, hp_le_2K, hK_le_2K]
  have pQBase : StageEval (bmSeq bmFst bmQBaseEll) uIn
      (fun _ => encUnary qBase)
      (fun _ => 2 ^ K * (5000 * qBase + 2000)) := by
    refine (StageEval.seq pKP
      (StageEval.of_computesStageLe bmQBaseEll_computesStageLe (fun _ : S => (K, p)))).mono
      (fun _ => ?_)
    dsimp only [uIn, uKP, uPay, uTw0, uXs0]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_tw0, hlen_xs0, h2K_pos, h2Kq_nonneg, hqBase_le_2K, hp_le_2K, hK_le_2K]
  have pWBase : StageEval
      (bmSeq (bmFanout (bmUnaryConst 6) (bmSeq bmFst bmQBaseEll)) bmUnaryMul) uIn
      (fun _ => encUnary W_base)
      (fun _ => 2 ^ K * (12000 * qBase + 4000)) := by
    refine (StageEval.seq
      (StageEval.fanout (StageEval.unaryConst 6 uIn) pQBase)
      (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (6, qBase)))).mono
      (fun _ => ?_)
    dsimp only [uIn, uKP, uPay, uTw0, uXs0]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_tw0, hlen_xs0, h2K_pos, h2Kq_nonneg, hqBase_le_2K, hp_le_2K, hK_le_2K]
  have pWOut : StageEval
      (bmSeq (bmFanout (bmUnaryConst 10)
        (bmSeq (bmFanout (bmSeq bmFst bmSnd) (bmUnaryConst 2)) bmUnaryAdd)) bmUnaryMul) uIn
      (fun _ => encUnary W_io)
      (fun _ => 2 ^ K * (15000 * qBase + 5000)) := by
    refine (StageEval.seq
      (StageEval.fanout (StageEval.unaryConst 10 uIn) pQIn)
      (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (10, q_in)))).mono
      (fun _ => ?_)
    dsimp only [uIn, uKP, uPay, uTw0, uXs0, q_in]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    linarith [hlen_tw0, hlen_xs0, h2K_pos, h2Kq_nonneg, hqBase_le_2K, hp_le_2K, hK_le_2K]
  have hx0_bds1 : ∀ z ∈ xs0, WordWidthBounds W_io z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨j, _, rfl⟩
    exact hx1 j
  have hx0_bds2 : ∀ z ∈ xs0, WordWidthBounds W_base (FixedComplex.rescale qBase z) := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨j, _, rfl⟩
    exact (hx_base j).mono (by dsimp [W_base]; omega)
  have pInRescale : StageEval bmBaseFFTInRescale uIn
      (fun _ => encList (encComplex W_base) ((List.finRange (2 ^ K)).map xBase))
      (fun _ => 2 ^ K * (310000 * qBase + 100000)) := by
    have pCtxIn := StageEval.fanout pWBase (StageEval.fanout pQIn pQBase)
    have pRes := StageEval.congr_out
      (v2 := fun _ : S => encList (encComplex W_base) ((List.finRange (2 ^ K)).map xBase))
      (StageEval.const (S := S)
        (bmRescaleComplexList_computesInTime W_io W_base q_in qBase xs0 hx0_bds1 hx0_bds2))
      (fun _ => by dsimp only [xs0, xBase]; rw [List.map_map]; rfl)
    refine (StageEval.seq (StageEval.fanout pCtxIn pXs0) pRes).mono (fun _ => ?_)
    dsimp only [uIn, uKP, uPay, uTw0, uXs0]
    have hl : xs0.length = 2 ^ K := by simp [xs0]
    rw [hl]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have hcoeff :
        2 ^ K * (18000 * W_io + 5000 * W_base + 32000 * q_in + 32000 * qBase + 70000) ≤
        2 ^ K * (274000 * qBase + 70000) :=
      Nat.mul_le_mul_left _ (by dsimp [W_io, W_base, q_in]; omega)
    linarith [hcoeff, hlen_tw0, hlen_xs0, h2K_pos, h2Kq_nonneg, hqBase_le_2K, hp_le_2K, hK_le_2K,
      hW_base_def, hW_io_def, hq_in_def, hqBase_def]
  have hlen_xBase :
      (encList (encComplex W_base) ((List.finRange (2 ^ K)).map xBase)).length ≤
      2 ^ K * (48 * qBase + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W_base) (4 * W_base + 8)
      ((List.finRange (2 ^ K)).map xBase) (fun _ _ => by simp)
    simp only [List.length_map, List.length_finRange] at h
    exact h.trans (le_of_eq (by dsimp [W_base]; ring))
  have pCore : StageEval (bmBaseFFTCoreWith bmMul) uIn
      (fun _ => encList (encComplex W_base) ((List.finRange (2 ^ K)).map yBase))
      (fun _ => (K + 1) * 2 ^ K * (8 * mulTime W_base + 2200000 * qBase + 1200000)) := by
    have pHdr := StageEval.fanout pK (StageEval.fanout pWBase pQBase)
    have pCoreIn := StageEval.fanout pHdr (StageEval.fanout pTw0 pInRescale)
    have pFFT := StageEval.const (S := S)
      (bmRadix2FFT1DWith_computesInTime hmul K qBase (2 * qBase) W_base leafTwiddles htw
        xBase hx_base (by omega) (by dsimp [W_base]; omega) (by dsimp [W_base]; omega))
    refine (StageEval.seq pCoreIn pFFT).mono (fun _ => ?_)
    dsimp only [uIn, uKP, uPay, uTw0, uXs0]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have h1 : 2 ^ K * (350000 * qBase + 130000) ≤
        (K + 1) * 2 ^ K * (350000 * qBase + 130000) := by
      have : 1 * (2 ^ K * (350000 * qBase + 130000)) ≤
          (K + 1) * (2 ^ K * (350000 * qBase + 130000)) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left 1 K)
      linarith
    have h2 :
        (K + 1) * 2 ^ K * (8 * mulTime W_base + 300000 * W_base + 40000 * qBase + 800000) =
        (K + 1) * 2 ^ K * (8 * mulTime W_base + 1840000 * qBase + 800000) := by
      dsimp only [W_base]; ring
    have h3 :
        (K + 1) * 2 ^ K * (350000 * qBase + 130000) +
        (K + 1) * 2 ^ K * (8 * mulTime W_base + 1840000 * qBase + 800000) ≤
        (K + 1) * 2 ^ K * (8 * mulTime W_base + 2200000 * qBase + 1200000) := by
      calc (K + 1) * 2 ^ K * (350000 * qBase + 130000) +
           (K + 1) * 2 ^ K * (8 * mulTime W_base + 1840000 * qBase + 800000)
          = (K + 1) * 2 ^ K * (8 * mulTime W_base + 2190000 * qBase + 930000) := by ring
        _ ≤ (K + 1) * 2 ^ K * (8 * mulTime W_base + 2200000 * qBase + 1200000) :=
            Nat.mul_le_mul_left _ (by omega)
    linarith [h1, h2, h3, hlen_tw0, hlen_xs0, hlen_xBase, h2K_pos, h2Kq_nonneg, hqBase_le_2K, hp_le_2K, hK_le_2K,
      hW_base_def, hW_io_def, hq_in_def, hqBase_def]
  have hyBase_bds1 : ∀ z ∈ (List.finRange (2 ^ K)).map yBase, WordWidthBounds W_base z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨u, _, rfl⟩
    have hy := (radix2FFT1DFixedWithMul_eq_and_bounds (· * ·) K qBase (2 * qBase) W_base
      (fun _ _ _ _ => rfl) leafTwiddles htw (by dsimp [W_base]; omega) K (le_refl K)
      xBase hx_base (by omega) (by dsimp [W_base]; omega)).2 u
    exact hy.mono (by dsimp [W_base]; omega)
  have hyBase_bds2 : ∀ z ∈ (List.finRange (2 ^ K)).map yBase,
      WordWidthBounds W_io (FixedComplex.rescale q_in z) := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨u, _, rfl⟩
    have heq : FixedComplex.rescale q_in (yBase u) = baseRadix2FFTFixed K p leafTwiddles xFixed u := by
      unfold baseRadix2FFTFixed baseRadix2FFTFixedWithMul
      simp only [memoizeFin_eq]
      rw [radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl)]
    rw [heq]
    exact hout u
  have hlen_yBase :
      (encList (encComplex W_base) ((List.finRange (2 ^ K)).map yBase)).length ≤
      2 ^ K * (48 * qBase + 18) := by
    have h := length_encList_le_of_forall_le (encComplex W_base) (4 * W_base + 8)
      ((List.finRange (2 ^ K)).map yBase) (fun _ _ => by simp)
    simp only [List.length_map, List.length_finRange] at h
    exact h.trans (le_of_eq (by dsimp [W_base]; ring))
  have pOut : StageEval (bmBaseRadix2FFTWith bmMul) uIn
      (fun _ => encList (encComplex W_io)
        ((List.finRange (2 ^ K)).map (baseRadix2FFTFixed K p leafTwiddles xFixed)))
      (fun _ => (K + 1) * 2 ^ K * (8 * mulTime W_base + 2500000 * qBase + 1500000)) := by
    have pCtxOut := StageEval.fanout pWOut (StageEval.fanout pQBase pQIn)
    have pResOut := StageEval.congr_out
      (v2 := fun _ : S => encList (encComplex W_io)
        ((List.finRange (2 ^ K)).map (baseRadix2FFTFixed K p leafTwiddles xFixed)))
      (StageEval.const (S := S)
        (bmRescaleComplexList_computesInTime W_base W_io qBase q_in
          ((List.finRange (2 ^ K)).map yBase) hyBase_bds1 hyBase_bds2))
      (fun _ => by
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro u _
        dsimp only [Function.comp]
        unfold baseRadix2FFTFixed baseRadix2FFTFixedWithMul
        simp only [memoizeFin_eq]
        rw [radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl)])
    refine (StageEval.seq (StageEval.fanout pCtxOut pCore) pResOut).mono (fun _ => ?_)
    dsimp only [uIn, uKP, uPay, uTw0, uXs0]
    have hl : ((List.finRange (2 ^ K)).map yBase).length = 2 ^ K := by simp
    rw [hl]
    simp only [length_encDepPair, length_encPair, length_encUnary]
    have hcoeff :
        2 ^ K * (18000 * W_base + 5000 * W_io + 32000 * qBase + 32000 * q_in + 70000) ≤
        2 ^ K * (222000 * qBase + 70000) :=
      Nat.mul_le_mul_left _ (by dsimp [W_io, W_base, q_in]; omega)
    have hdom : 2 ^ K * (270000 * qBase + 150000) ≤
        (K + 1) * 2 ^ K * (270000 * qBase + 150000) := by
      have : 1 * (2 ^ K * (270000 * qBase + 150000)) ≤
          (K + 1) * (2 ^ K * (270000 * qBase + 150000)) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left 1 K)
      linarith
    have htot :
        (K + 1) * 2 ^ K * (8 * mulTime W_base + 2200000 * qBase + 1200000) +
        (K + 1) * 2 ^ K * (270000 * qBase + 150000) ≤
        (K + 1) * 2 ^ K * (8 * mulTime W_base + 2500000 * qBase + 1500000) := by
      calc (K + 1) * 2 ^ K * (8 * mulTime W_base + 2200000 * qBase + 1200000) +
           (K + 1) * 2 ^ K * (270000 * qBase + 150000)
          = (K + 1) * 2 ^ K * (8 * mulTime W_base + 2470000 * qBase + 1350000) := by ring
        _ ≤ (K + 1) * 2 ^ K * (8 * mulTime W_base + 2500000 * qBase + 1500000) :=
            Nat.mul_le_mul_left _ (by omega)
    linarith [hcoeff, hdom, htot, hlen_tw0, hlen_xs0, hlen_yBase, h2K_pos, h2Kq_nonneg, hqBase_le_2K,
      hp_le_2K, hK_le_2K, hW_base_def, hW_io_def, hq_in_def, hqBase_def]
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht_step, hcomp⟩
  dsimp only [uIn, uKP, uPay, uTw0, uXs0, encDepPair, id] at ht_step hcomp
  exact ⟨t, ht_step, hcomp⟩

end IntMul
