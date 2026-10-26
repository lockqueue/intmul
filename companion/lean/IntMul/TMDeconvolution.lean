import IntMul.TMFastDFT

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# Uniform 8-Stack `Turing.FinTM2` Stages for Step 3 Cyclic Bidiagonal & Nyquist Deconvolution (`IntMul.TMDeconvolution`)

This module implements the uniform 8-stack `BitMachine` (`Turing.FinTM2`) stages and proves their
output-equivalence and explicit `ComputesInTime` step-count bounds for Step 3 of
`computableFastDFTRecursive` (Theorem 5.1 (`thm:deconv`), Section 5.2 (`sec:solvers`), and
Section 8 (`sec:lean`)):
1. **Part 1 (Linear-Time Prefix Scan & Cyclic Index Permutation Combinators)**:
   - `bmScanlList` and `StageEval.scanlList_idx` (single-pass $O(t_1)$ recurrence trajectory builder)
   - `bmRotateOneList` and cyclic permutation lemmas for `cyclicNext`, `reverse`, and `(t1 - u1) % t1`
2. **Part 2 (Fixed-Point Complex Scalar & Natural Division Stages)**:
   - `bmDivScalarFixed` (`divScalarFixed`)
   - `bmDivNatFixed` (`divNatFixed`)
3. **Part 3 (Single-Pass $O(t_1)$ Bidiagonal Recurrence Sweep Stage)**:
   - `bmBidiagScaleEntryWith`, `bmBidiagStepWith`, `bmBidiagReconEntryWith`, `bmBidiagSweepCoreWith`
4. **Part 4 (Forward & Backward Cyclic Bidiagonal Column Solvers)**:
   - `bmCyclicBidiagSolveWith`, `bmCyclicBidiagPrevSolveWith`
5. **Part 5 (Column-Level $O(t_1)$ Nyquist Open-Chain + Rank-1 Correction Solver)**:
   - `bmNyquistColumnSolveWith`
6. **Part 6 (Multi-Column Step 3 Deconvolution Stage)**:
   - `bmStep3ColDispatchWith`, `bmStep3DeconvolveColsWith`

All machines have $O(1)$ state space independent of $n, K, p, R, A, B$ and execute step-by-step
bit-level operations on the uniform 8-stack machine model.
-/

namespace IntMul

open Turing StageEval

/-! ## 1. Linear-Time Prefix Scan (`bmScanlList`) & Cyclic List Permutations -/

/-- **Linear-Time Prefix Scan Combinator (`bmScanlList stepM`)**:
Consumes `encPair (encList encElem) encAcc (xs, acc_0)` on `kIO`, iterates `stepM`
(`encPair encElem encAcc (x_i, acc_i) ↦ encAcc acc_{i+1}`) across `xs = [x_0, ..., x_{k-1}]` while
recording the prefix state trajectory `[acc_0, acc_1, ..., acc_{k-1}]` on `kWork3`, and emits
`encPair (encList encAcc) encAcc ([acc_0, ..., acc_{k-1}], acc_k)` on `kIO` in strictly linear time. -/
def bmScanlList (stepM : BitMachine) : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork2).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kIO).seq
            ((tmPushEmpty kWork3).seq
              ((((tmDupWord kIO kWork0 kWork1).seq
                  ((tmRevMoveWord kWork1 kWork0).seq
                    ((tmPrependRevWord kWork0 kWork3).seq
                      ((tmPopFirstSubwordRev kWork2 kWork0).seq
                        (tmPackPairFromRev.seq stepM))))).loopNonEmptyWord kWork2).seq
                ((tmRevMoveWord kIO kWork2).seq
                  ((tmMoveWord kWork3 kWork0 kIO).seq
                    (bmRevList.seq
                      ((tmMoveWord kWork2 kWork1 kWork0).seq
                        tmPackPairFromRevSwapped))))))))))

/-- Direct induction for `bmScanlList`'s inner `loopNonEmptyWord kWork2` over remaining suffix `rem`. -/
theorem scanlList_indexed_loop_le {S α β : Type} {stepM : BitMachine}
    {encElem : S → α → List Bool} {encAcc : S → β → List Bool}
    {xs : S → List α} {st : S → ℕ → β}
    {B L_elem L_acc : S → ℕ}
    (hstep : StageEval (S := { p : S × ℕ // p.2 < (xs p.1).length }) stepM
      (encDepPair (fun p => encElem p.val.1 ((xs p.val.1)[p.val.2]'p.property))
        (fun p => encAcc p.val.1 (st p.val.1 p.val.2)))
      (fun p => encAcc p.val.1 (st p.val.1 (p.val.2 + 1)))
      (fun p => B p.val.1))
    (hL_elem : ∀ (s : S) (i : ℕ) (hi : i < (xs s).length),
      (encElem s ((xs s)[i]'hi)).length ≤ L_elem s)
    (hL_acc : ∀ (s : S) (i : ℕ), i ≤ (xs s).length → (encAcc s (st s i)).length ≤ L_acc s)
    (s : S) :
    ∀ (rem : List α) (i : ℕ) (_hrem : (xs s).drop i = rem)
      (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ rem.length * (B s + 2 * L_elem s + 7 * L_acc s + 18) + 1,
        (((tmDupWord kIO kWork0 kWork1).seq
            ((tmRevMoveWord kWork1 kWork0).seq
              ((tmPrependRevWord kWork0 kWork3).seq
                ((tmPopFirstSubwordRev kWork2 kWork0).seq
                  (tmPackPairFromRev.seq stepM))))).loopNonEmptyWord kWork2).ComputesInTime
          (mkTapes8 (encodeDelimWord (encAcc s (st s i))) [] []
            (encodeDelimWord (encList (encElem s) rem) ++ tW2)
            (encodeDelimWord (encList (encAcc s) (((List.range i).map (st s)).reverse)) ++ tW3)
            tW4 tW5 tSch)
          (mkTapes8 (encodeDelimWord (encAcc s (st s (i + rem.length)))) [] []
            tW2
            (encodeDelimWord (encList (encAcc s) (((List.range (i + rem.length)).map (st s)).reverse)) ++ tW3)
            tW4 tW5 tSch) t
  | [], i, _, tW2, tW3, tW4, tW5, tSch => by
    simp only [List.length_nil, Nat.add_zero, Nat.zero_mul, encList_nil]
    refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopNonEmptyWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, mkTapes8_kWork2, update_mkTapes8_kWork2, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | x :: rem, i, hrem, tW2, tW3, tW4, tW5, tSch => by
    have hi : i < (xs s).length := by
      by_contra hge
      have hd : (xs s).drop i = [] := List.drop_eq_nil_of_le (by omega)
      rw [hrem] at hd
      cases hd
    have hx_eq : (xs s)[i]'hi = x := by
      have hd := List.drop_eq_getElem_cons hi
      rw [hrem] at hd
      exact (List.cons.inj hd).1.symm
    have hrem' : (xs s).drop (i + 1) = rem := by
      have hd := List.drop_eq_getElem_cons hi
      rw [hrem] at hd
      exact (List.cons.inj hd).2.symm
    let body :=
      (tmDupWord kIO kWork0 kWork1).seq
        ((tmRevMoveWord kWork1 kWork0).seq
          ((tmPrependRevWord kWork0 kWork3).seq
            ((tmPopFirstSubwordRev kWork2 kWork0).seq
              (tmPackPairFromRev.seq stepM))))
    let acc := ((List.range i).map (st s)).reverse
    have hpop : (body.loopNonEmptyWord kWork2).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord (encAcc s (st s i))) [] []
            (encodeDelimWord (encList (encElem s) (x :: rem)) ++ tW2)
            (encodeDelimWord (encList (encAcc s) acc) ++ tW3) tW4 tW5 tSch⟩ =
        some ⟨some (some body.main), default,
          mkTapes8 (encodeDelimWord (encAcc s (st s i))) [] []
            (encodeDelimWord (encList (encElem s) (x :: rem)) ++ tW2)
            (encodeDelimWord (encList (encAcc s) acc) ++ tW3) tW4 tW5 tSch⟩ := by
      simp only [encList_cons,
        encodeDelimWord_append_eq_head_tail (encElem s x) (encList (encElem s) rem),
        encodeDelimWord_cons, List.cons_append, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, mkTapes8_kWork2,
        update_mkTapes8_kWork2, List.head?_cons, List.tail_cons, Option.getD_some, cond_false]
    have d1 := tmDupWord_computesInTime kIO kWork0 kWork1 (by decide) (by decide) (by decide)
      (encAcc s (st s i)) [] [] []
      (mkTapes8 [] [] [] (encodeDelimWord (encList (encElem s) (x :: rem)) ++ tW2)
        (encodeDelimWord (encList (encAcc s) acc) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
      List.append_nil] at d1
    have d2 := tmRevMoveWord_computesInTime kWork1 kWork0 (by decide)
      (encAcc s (st s i)) [] []
      (mkTapes8 (encodeDelimWord (encAcc s (st s i))) [] []
        (encodeDelimWord (encList (encElem s) (x :: rem)) ++ tW2)
        (encodeDelimWord (encList (encAcc s) acc) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, List.append_nil] at d2
    have d3 := tmPrependRevWord_computesInTime kWork0 kWork3 (by decide)
      (encAcc s (st s i)).reverse (encList (encAcc s) acc) [] tW3
      (mkTapes8 (encodeDelimWord (encAcc s (st s i))) [] []
        (encodeDelimWord (encList (encElem s) (x :: rem)) ++ tW2) [] tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
      List.reverse_reverse, List.append_nil] at d3
    have hacc_next : st s i :: acc = ((List.range (i + 1)).map (st s)).reverse := by
      dsimp only [acc]
      rw [List.range_succ, List.map_append, List.map_singleton, List.reverse_append,
        List.reverse_singleton, List.singleton_append]
    have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
      (encodeDelimWord (encElem s x) ++ encList (encElem s) rem) tW2 []
      (mkTapes8 (encodeDelimWord (encAcc s (st s i))) [] [] []
        (encodeDelimWord (encList (encAcc s) (st s i :: acc)) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
      unconsDelimWord_encodeDelimWord_append] at b1
    have b2 := tmPackPairFromRev_computesInTime (encElem s x) (encAcc s (st s i))
      (encodeDelimWord (encList (encElem s) rem) ++ tW2)
      (encodeDelimWord (encList (encAcc s) (st s i :: acc)) ++ tW3) tW4 tW5 tSch
    rcases hstep ⟨(s, i), hi⟩ (encodeDelimWord (encList (encElem s) rem) ++ tW2)
      (encodeDelimWord (encList (encAcc s) (st s i :: acc)) ++ tW3) tW4 tW5 tSch
      with ⟨ts, hts, b3⟩
    dsimp only [id, encDepPair] at hts b3
    rw [hx_eq] at b3
    have ⟨hbody⟩ := d1.seq (d2.seq (d3.seq (b1.seq (b2.seq b3))))
    rw [hacc_next] at hbody
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete kWork2 body hbody
    rcases scanlList_indexed_loop_le hstep hL_elem hL_acc s rem (i + 1) hrem' tW2 tW3 tW4 tW5 tSch
      with ⟨t2, ht2, ⟨hih⟩⟩
    have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hbody_lifted) hih
    rw [show (i + 1) + rem.length = i + (x :: rem).length by simp [Nat.add_assoc, Nat.add_comm 1]]
      at hcomb
    have hle_e : (encElem s x).length ≤ L_elem s := by
      rw [← hx_eq]
      exact hL_elem s i hi
    have hle_a : (encAcc s (st s i)).length ≤ L_acc s := hL_acc s i (le_of_lt hi)
    refine ⟨_, ?_, ⟨hcomb⟩⟩
    simp only [List.length_cons]
    calc (((2 * (encAcc s (st s i)).length + 4 +
              (((encAcc s (st s i)).length + 2) +
                (((encAcc s (st s i)).length + 2) +
                  (((encElem s x).length + 2) +
                    (((encAcc s (st s i)).length + 2 +
                        (1 + ((encAcc s (st s i)).length + 2 + ((encElem s x).length + 2)))) +
                      ts))))) + 1)) + t2
        ≤ (B s + 2 * L_elem s + 7 * L_acc s + 18) +
          (rem.length * (B s + 2 * L_elem s + 7 * L_acc s + 18) + 1) := by omega
      _ = (rem.length + 1) * (B s + 2 * L_elem s + 7 * L_acc s + 18) + 1 := by ring

/-- **Indexed List Scan Theorem (`StageEval.scanlList_idx`)**:
If `stepM` advances `(encElem s ((xs s)[i]), encAcc s (st s i))` to `encAcc s (st s (i + 1))`
in `≤ B s` steps for all `i < (xs s).length`, then `bmScanlList stepM` transforms
`encDepPair (encList (encElem s) (xs s)) (encAcc s (st s 0))` into
`encPair (encList (encAcc s)) (encAcc s) ((List.range (xs s).length).map (st s), st s (xs s).length)`
in linear time. -/
theorem StageEval.scanlList_idx {S α β : Type} {stepM : BitMachine}
    {encElem : S → α → List Bool} {encAcc : S → β → List Bool}
    {xs : S → List α} {st : S → ℕ → β}
    {B L_elem L_acc : S → ℕ}
    (hstep : StageEval (S := { p : S × ℕ // p.2 < (xs p.1).length }) stepM
      (encDepPair (fun p => encElem p.val.1 ((xs p.val.1)[p.val.2]'p.property))
        (fun p => encAcc p.val.1 (st p.val.1 p.val.2)))
      (fun p => encAcc p.val.1 (st p.val.1 (p.val.2 + 1)))
      (fun p => B p.val.1))
    (hL_elem : ∀ (s : S) (i : ℕ) (hi : i < (xs s).length),
      (encElem s ((xs s)[i]'hi)).length ≤ L_elem s)
    (hL_acc : ∀ (s : S) (i : ℕ), i ≤ (xs s).length → (encAcc s (st s i)).length ≤ L_acc s) :
    StageEval (bmScanlList stepM)
      (encDepPair (fun s => encList (encElem s) (xs s)) (fun s => encAcc s (st s 0)))
      (fun s => encPair (encList (encAcc s)) (encAcc s)
        ((List.range (xs s).length).map (st s), st s (xs s).length))
      (fun s =>
        (xs s).length * (B s + 2 * L_elem s + 30 * L_acc s + 50) +
        2 * (encList (encElem s) (xs s)).length + 6 * L_acc s + 60) := by
  intro s tW2 tW3 tW4 tW5 tSch
  dsimp only [id]
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList (encElem s) (xs s)) ++ encodeDelimWord (encAcc s (st s 0))) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList (encElem s) (xs s)).reverse [] tW2
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encAcc s (st s 0)))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encAcc s (st s 0))) [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList (encElem s) (xs s)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encAcc s (st s 0)).reverse) []
      (encodeDelimWord (encList (encElem s) (xs s)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encAcc s (st s 0)).reverse [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList (encElem s) (xs s)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 (encodeDelimWord (encAcc s (st s 0))) [] []
      (encodeDelimWord (encList (encElem s) (xs s)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s6
  rcases scanlList_indexed_loop_le hstep hL_elem hL_acc s (xs s) 0 (by simp) tW2 tW3 tW4 tW5 tSch
    with ⟨tL, htL, s7⟩
  simp only [List.range_zero, List.map_nil, List.reverse_nil, encList_nil, Nat.zero_add] at s7
  let k := (xs s).length
  let fwdStates := (List.range k).map (st s)
  let revStates := fwdStates.reverse
  have s8 := tmRevMoveWord_computesInTime kIO kWork2 (by decide)
    (encAcc s (st s k)) [] tW2
    (mkTapes8 [] [] [] [] (encodeDelimWord (encList (encAcc s) revStates) ++ tW3) tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork2, List.append_nil] at s8
  have s9 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encList (encAcc s) revStates) tW3 [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encAcc s (st s k)).reverse ++ tW2) [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s9
  rcases bmRevList_computesStageLe (encAcc s) revStates
    (encodeDelimWord (encAcc s (st s k)).reverse ++ tW2) tW3 tW4 tW5 tSch with ⟨tR, htR, s10⟩
  dsimp only at htR
  simp only [revStates, List.reverse_reverse] at s10
  have s11 := tmMoveWord_computesInTime kWork2 kWork1 kWork0 (by decide) (by decide) (by decide)
    (encAcc s (st s k)).reverse tW2 [] []
    (mkTapes8 (encodeDelimWord (encList (encAcc s) fwdStates)) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
    List.length_reverse, List.append_nil] at s11
  have s12 := tmPackPairFromRevSwapped_computesInTime
    (encList (encAcc s) fwdStates) (encAcc s (st s k)) tW2 tW3 tW4 tW5 tSch
  have hlen_rev : (encList (encAcc s) revStates).length = (encList (encAcc s) fwdStates).length :=
    length_encList_reverse (encAcc s) fwdStates
  have hlen_fwd : (encList (encAcc s) fwdStates).length ≤ k * (2 * L_acc s + 2) := by
    have h := length_encList_le_of_forall_le (encAcc s) (L_acc s) fwdStates
      (fun y hy => by
        rcases List.mem_map.mp hy with ⟨i, hi, rfl⟩
        exact hL_acc s i (le_of_lt (List.mem_range.mp hi)))
    simpa [fwdStates, List.length_map, List.length_range] using h
  have h0_le : (encAcc s (st s 0)).length ≤ L_acc s := hL_acc s 0 (Nat.zero_le k)
  have hk_le : (encAcc s (st s k)).length ≤ L_acc s := hL_acc s k (le_refl k)
  rw [hlen_rev] at s9 htR
  have hrun := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq
    (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq s12))))))))))
  refine ⟨_, ?_, hrun⟩
  have hmul :
      k * (B s + 2 * L_elem s + 7 * L_acc s + 18) + 11 * (k * (2 * L_acc s + 2)) ≤
      k * (B s + 2 * L_elem s + 30 * L_acc s + 50) := by
    nlinarith
  dsimp only [k] at hmul hlen_fwd hk_le s8 s11 s12 ⊢
  omega

/-- Bridge between `(List.range k).map (fun i => (buildRecurrenceArray init step i).2)` and
`(List.finRange k).map (fun u1 => (buildRecurrenceArray init step k).1.getD u1.val init)`. -/
theorem map_range_buildRecurrenceArray_snd {α : Type*} (init : α) (step : ℕ → α → α) (k : ℕ) :
    (List.range k).map (fun i => (buildRecurrenceArray init step i).2) =
      (List.finRange k).map (fun u1 : Fin k =>
        (buildRecurrenceArray init step k).1.getD u1.val init) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.val_cast]
    have hi : i < k := by simpa using h1
    exact (getD_buildRecurrenceArray init step (le_of_lt hi)).symm

/-- **Cyclic Left-Rotate-by-1 List Stage (`bmRotateOneList`)**:
Consumes `encList encElem xs` on `kIO` (`1 ≤ xs.length`) and emits
`encList encElem (rotateList 1 xs)` in linear time. -/
def bmRotateOneList : BitMachine :=
  bmSeq (bmFanout (bmUnaryConst 1) bmId) bmRotateList

theorem bmRotateOneList_computesInTime {α : Type} [Inhabited α] (encElem : α → List Bool)
    (L : ℕ) (hL : ∀ x : α, (encElem x).length ≤ L)
    (xs : List α) (hxs_pos : 1 ≤ xs.length)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 400 * xs.length * (L + 1) + 500,
      bmRotateOneList.ComputesInTime
        (mkTapes8 (encodeDelimWord (encList encElem xs)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem (rotateList 1 xs)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encList encElem xs
  have pOne := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 1 id) uIn
  have pPair := StageEval.fanout pOne (StageEval.id_stage uIn)
  have pRot := StageEval.seq pPair
    (StageEval.const (S := S) (bmRotateList_computesInTime encElem L hL 1 xs hxs_pos))
  rcases pRot () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht
  have hlen_xs : (encList encElem xs).length ≤ xs.length * (2 * L + 2) :=
    length_encList_le_of_forall_le encElem L xs (fun x _ => hL x)
  simp only [length_encUnary] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- **Unary List Length Stage (`bmListLengthUnary`)**:
Consumes `encList encElem xs` on `kIO`, maps each element to `[]` via `bmMapNoCtx bmUnaryZero`
(producing `encList encUnary (xs.map (fun _ => 0))` of bit-length `2 * xs.length`), and runs
`bmHalfLenUnary` to emit `encUnary xs.length` in $O(|xs| \cdot L)$ steps. -/
def bmListLengthUnary : BitMachine :=
  bmSeq (bmMapNoCtx bmUnaryZero) bmHalfLenUnary

theorem bmListLengthUnary_computesInTime {α : Type} (encElem : α → List Bool)
    (L : ℕ) (hL : ∀ x : α, (encElem x).length ≤ L) (xs : List α)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ xs.length * (100 * L + 200) + 120,
      bmListLengthUnary.ComputesInTime
        (mkTapes8 (encodeDelimWord (encList encElem xs)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encUnary xs.length)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let SubM := { p : S × α // p.2 ∈ xs }
  have hStep : StageEval (S := SubM) bmUnaryZero
      (fun p => encElem p.val.2) (fun _ => encUnary 0) (fun _ => L + 2) :=
    (StageEval.constEmpty (fun p : SubM => encElem p.val.2)).mono
      (fun p => Nat.add_le_add_right (hL p.val.2) 2)
  have pMap := StageEval.mapNoCtx (S := S)
    (encA := fun _ => encElem) (encB := fun _ => encUnary)
    (xs := fun _ => xs) (fn := fun _ _ => 0)
    (B_step := fun _ => L + 2) (L_A := fun _ => L) (L_B := fun _ => 0)
    hStep (fun _ x _ => hL x) (fun _ _ _ => by simp [length_encUnary])
  have hlen_zeros : (encList encUnary (xs.map (fun _ => 0))).length = 2 * xs.length := by
    rw [length_encList_eq_of_forall_eq encUnary 0 (xs.map (fun _ => 0))
      (fun x hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; simp [length_encUnary])]
    simp only [List.length_map]
    ring
  have pHalfRaw := StageEval.seq pMap
    (StageEval.of_computesStageLe (bmHalfLenUnary_computesStageLe (encList encUnary))
      (fun _ : S => xs.map (fun _ => 0)))
  have pHalf := StageEval.congr_out (v2 := fun _ : S => encUnary xs.length) pHalfRaw
    (fun _ => by
      rw [hlen_zeros, Nat.mul_div_right _ (by decide)])
  rcases pHalf () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_xs : (encList encElem xs).length ≤ xs.length * (2 * L + 2) :=
    length_encList_le_of_forall_le encElem L xs (fun x _ => hL x)
  dsimp only [id] at ht hcomp
  rw [hlen_zeros] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- Rotating `(List.finRange t1).map f` left by `1` produces
`(List.finRange t1).map (fun m => f (cyclicNext m))`. -/
theorem rotateOne_map_finRange_eq_cyclicNext {α : Type} {t1 : ℕ} [NeZero t1] (f : Fin t1 → α) :
    rotateList 1 ((List.finRange t1).map f) =
      (List.finRange t1).map (fun m : Fin t1 => f (cyclicNext m)) := by
  have ht1 : 1 ≤ t1 := NeZero.pos t1
  rw [rotateList_map_finRange 1 ht1 f]
  rfl

/-- Reversing `(List.finRange t1).map Y` produces
`(List.finRange t1).map (fun s => Y ⟨(t1 - 1 - s.val % t1) % t1, ...⟩)`. -/
theorem reverse_map_finRange_eq {α : Type*} {t1 : ℕ} (ht1 : 0 < t1) (Y : Fin t1 → α) :
    ((List.finRange t1).map Y).reverse =
      (List.finRange t1).map (fun s : Fin t1 =>
        Y ⟨(t1 - 1 - s.val % t1) % t1, Nat.mod_lt _ ht1⟩) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < t1 := by simpa using h1
    simp only [List.getElem_reverse, List.length_map, List.length_finRange,
      List.getElem_map, List.getElem_finRange, Fin.val_cast]
    congr 1
    ext
    simp only [Fin.val_cast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : t1 - 1 - i < t1)]

/-- Rotating `(List.finRange t1).map F` left by `1` and reversing produces
`(List.finRange t1).map (fun u1 => F ⟨(t1 - u1.val) % t1, ...⟩)`. -/
theorem reverse_rotateOne_map_finRange_eq {α : Type} {t1 : ℕ} [NeZero t1] (F : Fin t1 → α) :
    (rotateList 1 ((List.finRange t1).map F)).reverse =
      (List.finRange t1).map (fun u1 : Fin t1 =>
        F ⟨(t1 - u1.val) % t1, Nat.mod_lt _ (NeZero.pos t1)⟩) := by
  have ht1 : 0 < t1 := NeZero.pos t1
  rw [rotateOne_map_finRange_eq_cyclicNext F, reverse_map_finRange_eq ht1]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < t1 := by simpa using h1
    simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, cyclicNext]
    congr 1
    ext
    simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : t1 - 1 - i < t1)]
    by_cases hi0 : i = 0
    · subst hi0
      have h1 : t1 - 1 - 0 + 1 = t1 := by omega
      rw [h1, Nat.sub_zero, Nat.mod_self]
    · have h1 : t1 - 1 - i + 1 = t1 - i := by omega
      rw [h1]

/-! ## 2. Fixed-Point Complex Division Stages (`bmDivScalarFixed` & `bmDivNatFixed`) -/

/-- **Fixed-Point Complex Division by a Signed Integer Mantissa (`bmDivScalarFixed`)**:
Consumes `encPair (encPair encUnary encUnary) (encPair (encComplex W) (encodeSignedWord W)) ((WOut, q2), (z, b))`
on `kIO` (`WordWidthBounds W z`, `FitsSignedWord W b`, `WordWidthBounds WOut (divScalarFixed q1 q2 z b)`)
and emits `encComplex WOut (divScalarFixed q1 q2 z b)` in $O((W + q_2)^2 + W_{\text{out}})$ steps. -/
def bmDivScalarFixed : BitMachine :=
  let bmWOut := bmSeq bmFst bmFst
  let bmQ2 := bmSeq bmFst bmSnd
  let bmZ := bmSeq bmSnd bmFst
  let bmB := bmSeq bmSnd bmSnd
  let bmZRe := bmSeq bmZ bmFst
  let bmZIm := bmSeq bmZ bmSnd
  let bmNumRe := bmSeq (bmFanout bmQ2 bmZRe) bmShiftLeftSigned
  let bmNumIm := bmSeq (bmFanout bmQ2 bmZIm) bmShiftLeftSigned
  let bmWQ := bmSeq bmNumRe bmSignedWidth
  let bmDen := bmSeq (bmFanout bmWQ bmB) bmResizeSignedWord
  let bmQRe := bmSeq (bmFanout bmNumRe bmDen) bmRoundDivInt
  let bmQIm := bmSeq (bmFanout bmNumIm bmDen) bmRoundDivInt
  bmFanout
    (bmSeq (bmFanout bmWOut bmQRe) bmResizeSignedWord)
    (bmSeq (bmFanout bmWOut bmQIm) bmResizeSignedWord)

theorem bmDivScalarFixed_computesInTime (W WOut q1 q2 : ℕ) (z : FixedComplex q1) (b : ℤ)
    (hz : WordWidthBounds W z) (hb : FitsSignedWord W b)
    (hout : WordWidthBounds WOut (divScalarFixed q1 q2 z b))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 600 * (q2 + W) * (q2 + W) + 200000 * (q2 + W) + 8000 * WOut + 500000,
      bmDivScalarFixed.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encComplex W) (encodeSignedWord W)) ((WOut, q2), (z, b))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex WOut (divScalarFixed q1 q2 z b)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encPair encUnary encUnary (WOut, q2)
  let u2 : S → List Bool := fun _ => encPair (encComplex W) (encodeSignedWord W) (z, b)
  let uIn : S → List Bool := encDepPair u1 u2
  have pFst := StageEval.fst u1 u2
  have pSnd := StageEval.snd u1 u2
  have pWOut := StageEval.seq pFst
    (StageEval.fst (fun _ : S => encUnary WOut) (fun _ : S => encUnary q2))
  have pQ2 := StageEval.seq pFst
    (StageEval.snd (fun _ : S => encUnary WOut) (fun _ : S => encUnary q2))
  have pZ := StageEval.seq pSnd
    (StageEval.fst (fun _ : S => encComplex W z) (fun _ : S => encodeSignedWord W b))
  have pB := StageEval.seq pSnd
    (StageEval.snd (fun _ : S => encComplex W z) (fun _ : S => encodeSignedWord W b))
  have pZRe := StageEval.seq pZ
    (StageEval.fst (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pZIm := StageEval.seq pZ
    (StageEval.snd (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pNumRe := StageEval.seq (StageEval.fanout pQ2 pZRe)
    (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime q2 W z.re hz.1))
  have pNumIm := StageEval.seq (StageEval.fanout pQ2 pZIm)
    (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime q2 W z.im hz.2))
  have hnum_re : FitsSignedWord (q2 + W) (z.re * (2 : ℤ) ^ q2) := by
    simpa [Nat.add_comm] using hz.1.mul_two_pow q2
  have hnum_im : FitsSignedWord (q2 + W) (z.im * (2 : ℤ) ^ q2) := by
    simpa [Nat.add_comm] using hz.2.mul_two_pow q2
  have hb_wq : FitsSignedWord (q2 + W) b := hb.mono (by omega)
  have pWQ := StageEval.seq pNumRe
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe (q2 + W))
      (fun _ : S => z.re * (2 : ℤ) ^ q2))
  have pDen := StageEval.seq (StageEval.fanout pWQ pB)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W (q2 + W) b hb hb_wq))
  have pQRe := StageEval.seq (StageEval.fanout pNumRe pDen)
    (StageEval.const (S := S) (bmRoundDivInt_computesInTime (q2 + W)
      (z.re * (2 : ℤ) ^ q2) b hnum_re hb_wq))
  have pQIm := StageEval.seq (StageEval.fanout pNumIm pDen)
    (StageEval.const (S := S) (bmRoundDivInt_computesInTime (q2 + W)
      (z.im * (2 : ℤ) ^ q2) b hnum_im hb_wq))
  have hq_re : FitsSignedWord (q2 + W) (roundDivInt (z.re * (2 : ℤ) ^ q2) b) :=
    FitsSignedWord.roundDivInt b hnum_re
  have hq_im : FitsSignedWord (q2 + W) (roundDivInt (z.im * (2 : ℤ) ^ q2) b) :=
    FitsSignedWord.roundDivInt b hnum_im
  have pOut1 := StageEval.seq (StageEval.fanout pWOut pQRe)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime (q2 + W) WOut
      (roundDivInt (z.re * (2 : ℤ) ^ q2) b) hq_re hout.1))
  have pOut2 := StageEval.seq (StageEval.fanout pWOut pQIm)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime (q2 + W) WOut
      (roundDivInt (z.im * (2 : ℤ) ^ q2) b) hq_im hout.2))
  rcases (StageEval.fanout pOut1 pOut2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- **Fixed-Point Complex Division by a Natural Number (`bmDivNatFixed`)**:
Consumes `encPair (encPair encUnary encUnary) (encComplex W) ((WOut, n), z)` on `kIO`
(`1 ≤ W`, `n < 2 ^ W`, `WordWidthBounds W z`, `WordWidthBounds WOut (divNatFixed z n)`)
and emits `encComplex WOut (divNatFixed z n)` in $O(n \cdot W + W^2 + W_{\text{out}})$ steps. -/
def bmDivNatFixed : BitMachine :=
  let bmWOut := bmSeq bmFst bmFst
  let bmN := bmSeq bmFst bmSnd
  let bmZ := bmSnd
  let bmZRe := bmSeq bmZ bmFst
  let bmZIm := bmSeq bmZ bmSnd
  let bmW := bmSeq bmZRe bmSignedWidth
  let bmNSigned := bmSeq (bmFanout bmW bmN) bmUnaryToSigned
  let bmQRe := bmSeq (bmFanout bmZRe bmNSigned) bmRoundDivInt
  let bmQIm := bmSeq (bmFanout bmZIm bmNSigned) bmRoundDivInt
  bmFanout
    (bmSeq (bmFanout bmWOut bmQRe) bmResizeSignedWord)
    (bmSeq (bmFanout bmWOut bmQIm) bmResizeSignedWord)

theorem bmDivNatFixed_computesInTime {q : ℕ} (W WOut n : ℕ) (z : FixedComplex q)
    (hW : 1 ≤ W) (hn : n < 2 ^ W)
    (hz : WordWidthBounds W z) (hout : WordWidthBounds WOut (divNatFixed z n))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ n * (1800 * W + 4500) + 600 * W * W + 160000 * W + 8000 * WOut + 500000,
      bmDivNatFixed.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encComplex W) ((WOut, n), z)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex WOut (divNatFixed z n)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encPair encUnary encUnary (WOut, n)
  let u2 : S → List Bool := fun _ => encComplex W z
  let uIn : S → List Bool := encDepPair u1 u2
  have pFst := StageEval.fst u1 u2
  have pZ := StageEval.snd u1 u2
  have pWOut := StageEval.seq pFst
    (StageEval.fst (fun _ : S => encUnary WOut) (fun _ : S => encUnary n))
  have pN := StageEval.seq pFst
    (StageEval.snd (fun _ : S => encUnary WOut) (fun _ : S => encUnary n))
  have pZRe := StageEval.seq pZ
    (StageEval.fst (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pZIm := StageEval.seq pZ
    (StageEval.snd (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pW := StageEval.seq pZRe
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => z.re))
  have pNSigned := StageEval.seq (StageEval.fanout pW pN)
    (StageEval.const (S := S) (bmUnaryToSigned_computesInTime W n hW hn))
  have hn_fits : FitsSignedWord W (n : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact hn
  have pQRe := StageEval.seq (StageEval.fanout pZRe pNSigned)
    (StageEval.const (S := S) (bmRoundDivInt_computesInTime W z.re (n : ℤ) hz.1 hn_fits))
  have pQIm := StageEval.seq (StageEval.fanout pZIm pNSigned)
    (StageEval.const (S := S) (bmRoundDivInt_computesInTime W z.im (n : ℤ) hz.2 hn_fits))
  have hq_re : FitsSignedWord W (roundDivInt z.re (n : ℤ)) :=
    FitsSignedWord.roundDivInt (n : ℤ) hz.1
  have hq_im : FitsSignedWord W (roundDivInt z.im (n : ℤ)) :=
    FitsSignedWord.roundDivInt (n : ℤ) hz.2
  have pOut1 := StageEval.seq (StageEval.fanout pWOut pQRe)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W WOut
      (roundDivInt z.re (n : ℤ)) hq_re hout.1))
  have pOut2 := StageEval.seq (StageEval.fanout pWOut pQIm)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W WOut
      (roundDivInt z.im (n : ℤ)) hq_im hout.2))
  rcases (StageEval.fanout pOut1 pOut2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-! ## 3. Single-Pass $O(t_1)$ Bidiagonal Recurrence Sweep Stage (`bmBidiagSweepCoreWith`) -/

/-- **Bidiagonal RHS Entry Scaling & Context Tagging (`bmBidiagScaleEntryWith bmMul`)**:
Consumes `encPair (encPair (encPair encUnary encUnary) (encPair (encodeSignedWord W) (encodeSignedWord W))) (encComplex W) (((q, qWork), (invA_m, ratio_m)), y)`
where `W = 10 * q`, rescales `y` from `q` to `qWork` at width `W`, scales by `invA_m` via
`bmComplexScaleRoundedWith bmMul`, and emits
`encPair (encPair encUnary (encodeSignedWord W)) (encComplex W) ((qWork, ratio_m), FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork y))`. -/
def bmBidiagScaleEntryWith (bmMul : BitMachine) : BitMachine :=
  let bmCtx := bmFst
  let bmQ := bmSeq (bmSeq bmCtx bmFst) bmFst
  let bmQWork := bmSeq (bmSeq bmCtx bmFst) bmSnd
  let bmInvA := bmSeq (bmSeq bmCtx bmSnd) bmFst
  let bmRatio := bmSeq (bmSeq bmCtx bmSnd) bmSnd
  let bmW := bmSeq bmInvA bmSignedWidth
  let bmY := bmSnd
  let bmRescaled :=
    bmSeq (bmFanout (bmFanout bmW (bmFanout bmQ bmQWork)) bmY) bmComplexRescale
  let bmScaled :=
    bmSeq (bmFanout (bmFanout bmW bmQWork) (bmFanout bmInvA bmRescaled))
      (bmComplexScaleRoundedWith bmMul)
  bmFanout (bmFanout bmQWork bmRatio) bmScaled

theorem bmBidiagScaleEntryWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (q : ℕ) (hq : 14 ≤ q) (invA_m ratio_m : ℤ) (y : FixedComplex q)
    (hinv : FitsSignedWord (3 * q) invA_m) (_hratio : FitsSignedWord (10 * q) ratio_m)
    (hy : WordWidthBounds (3 * q) y)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let qWork := q + 9
    let W := 10 * q
    let B_s := FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork y)
    ∃ t ≤ 4 * mulTime W + 1200000 * q + 600000,
      (bmBidiagScaleEntryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary encUnary)
              (encPair (encodeSignedWord W) (encodeSignedWord W)))
            (encComplex W)
            (((q, qWork), (invA_m, ratio_m)), y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encodeSignedWord W)) (encComplex W)
            ((qWork, ratio_m), B_s)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro qWork W B_s
  let S := Unit
  let uQQ : S → List Bool := fun _ => encPair encUnary encUnary (q, qWork)
  let uIR : S → List Bool := fun _ => encPair (encodeSignedWord W) (encodeSignedWord W) (invA_m, ratio_m)
  let uCtx : S → List Bool := encDepPair uQQ uIR
  let uY : S → List Bool := fun _ => encComplex W y
  let uIn : S → List Bool := encDepPair uCtx uY
  have pCtx := StageEval.fst uCtx uY
  have pY := StageEval.snd uCtx uY
  have pQQ := StageEval.seq pCtx (StageEval.fst uQQ uIR)
  have pIR := StageEval.seq pCtx (StageEval.snd uQQ uIR)
  have pQ := StageEval.seq pQQ
    (StageEval.fst (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pQWork := StageEval.seq pQQ
    (StageEval.snd (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pInvA := StageEval.seq pIR
    (StageEval.fst (fun _ : S => encodeSignedWord W invA_m) (fun _ : S => encodeSignedWord W ratio_m))
  have pRatio := StageEval.seq pIR
    (StageEval.snd (fun _ : S => encodeSignedWord W invA_m) (fun _ : S => encodeSignedWord W ratio_m))
  have pW := StageEval.seq pInvA
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => invA_m))
  have hrs_bds4 : WordWidthBounds (4 * q) (FixedComplex.rescale qWork y) := by
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 9 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact (hy.1.mul_two_pow 9).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact (hy.2.mul_two_pow 9).mono (by omega)
  have hrs_bdsW : WordWidthBounds W (FixedComplex.rescale qWork y) :=
    hrs_bds4.mono (by omega)
  have hinvW : FitsSignedWord W invA_m := hinv.mono (by omega)
  have hB_bds6 : WordWidthBounds (6 * q) B_s := by
    exact ⟨(FitsSignedWord.roundShiftInt_sub (w := 6 * q - 1) (k := qWork)
              ((hinv.mul hrs_bds4.1).mono (by omega))).mono (by omega),
           (FitsSignedWord.roundShiftInt_sub (w := 6 * q - 1) (k := qWork)
              ((hinv.mul hrs_bds4.2).mono (by omega))).mono (by omega)⟩
  have hB_bdsW : WordWidthBounds W B_s := hB_bds6.mono (by omega)
  have pRescaled := StageEval.seq
    (StageEval.fanout (StageEval.fanout pW (StageEval.fanout pQ pQWork)) pY)
    (StageEval.const (S := S) (bmComplexRescale_computesInTime W W q qWork y (hy.mono (by omega)) hrs_bdsW))
  have pScaled := StageEval.congr_out
    (v2 := fun _ => encComplex W B_s)
    (StageEval.seq
      (StageEval.fanout (StageEval.fanout pW pQWork) (StageEval.fanout pInvA pRescaled))
      (StageEval.const (S := S)
        (bmComplexScaleRoundedWith_computesInTime hmul W W qWork invA_m
          (FixedComplex.rescale qWork y) hinvW hrs_bdsW hB_bdsW)))
    (fun _ => rfl)
  have pAll := StageEval.fanout (StageEval.fanout pQWork pRatio) pScaled
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uCtx, uQQ, uIR, uY, W, qWork] at ht ⊢
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- **Single Step of the Non-Nyquist Bidiagonal Recurrence (`bmBidiagStepWith bmMul`)**:
Consumes `encPair (encPair (encPair encUnary (encodeSignedWord W)) (encComplex W)) (encPair (encComplex W) (encodeSignedWord W)) (((qWork, ratio_m), B_s), (zp, zh))`
and computes `encPair (encComplex W) (encodeSignedWord W) (B_s + FixedComplex.scaleRounded ratio_m zp, roundShiftInt (ratio_m * zh) qWork)`. -/
def bmBidiagStepWith (bmMul : BitMachine) : BitMachine :=
  let bmElem := bmFst
  let bmSt := bmSnd
  let bmQWork := bmSeq (bmSeq bmElem bmFst) bmFst
  let bmRatio := bmSeq (bmSeq bmElem bmFst) bmSnd
  let bmB := bmSeq bmElem bmSnd
  let bmZp := bmSeq bmSt bmFst
  let bmZh := bmSeq bmSt bmSnd
  let bmW := bmSeq bmRatio bmSignedWidth
  let bmScaledZp :=
    bmSeq (bmFanout (bmFanout bmW bmQWork) (bmFanout bmRatio bmZp))
      (bmComplexScaleRoundedWith bmMul)
  let bmNextZp := bmSeq (bmFanout bmB bmScaledZp) bmComplexAdd
  let bmProdZh := bmSeq (bmFanout bmRatio bmZh) (bmSignedMulWith bmMul)
  let bmShiftedZh := bmSeq (bmFanout bmQWork bmProdZh) bmRoundShiftSigned
  let bmNextZh := bmSeq (bmFanout bmW bmShiftedZh) bmResizeSignedWord
  bmFanout bmNextZp bmNextZh

theorem bmBidiagStepWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W qWork : ℕ) (ratio_m : ℤ) (B_s : FixedComplex qWork)
    (st nextSt : FixedComplex qWork × ℤ)
    (hnext : nextSt = (B_s + FixedComplex.scaleRounded ratio_m st.1, roundShiftInt (ratio_m * st.2) qWork))
    (hratio : FitsSignedWord W ratio_m) (hB : WordWidthBounds W B_s)
    (hst1 : WordWidthBounds W st.1) (hst2 : FitsSignedWord W st.2)
    (hscale_zp : WordWidthBounds W (FixedComplex.scaleRounded ratio_m st.1))
    (hnext1 : WordWidthBounds W nextSt.1) (hnext2 : FitsSignedWord W nextSt.2)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 6 * mulTime W + 100000 * W + 20000 * qWork + 200000,
      (bmBidiagStepWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary (encodeSignedWord W)) (encComplex W))
            (encPair (encComplex W) (encodeSignedWord W))
            (((qWork, ratio_m), B_s), st)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encComplex W) (encodeSignedWord W) nextSt))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uQR : S → List Bool := fun _ => encPair encUnary (encodeSignedWord W) (qWork, ratio_m)
  let uElem : S → List Bool := encDepPair uQR (fun _ => encComplex W B_s)
  let uSt : S → List Bool := fun _ => encPair (encComplex W) (encodeSignedWord W) st
  let uIn : S → List Bool := encDepPair uElem uSt
  have pElem := StageEval.fst uElem uSt
  have pSt := StageEval.snd uElem uSt
  have pQR := StageEval.seq pElem (StageEval.fst uQR (fun _ => encComplex W B_s))
  have pB := StageEval.seq pElem (StageEval.snd uQR (fun _ => encComplex W B_s))
  have pQWork := StageEval.seq pQR
    (StageEval.fst (fun _ : S => encUnary qWork) (fun _ : S => encodeSignedWord W ratio_m))
  have pRatio := StageEval.seq pQR
    (StageEval.snd (fun _ : S => encUnary qWork) (fun _ : S => encodeSignedWord W ratio_m))
  have pZp := StageEval.seq pSt
    (StageEval.fst (fun _ : S => encComplex W st.1) (fun _ : S => encodeSignedWord W st.2))
  have pZh := StageEval.seq pSt
    (StageEval.snd (fun _ : S => encComplex W st.1) (fun _ : S => encodeSignedWord W st.2))
  have pW := StageEval.seq pRatio
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => ratio_m))
  have pScaledZp := StageEval.congr_out
    (v2 := fun _ => encComplex W (FixedComplex.scaleRounded ratio_m st.1))
    (StageEval.seq
      (StageEval.fanout (StageEval.fanout pW pQWork) (StageEval.fanout pRatio pZp))
      (StageEval.const (S := S)
        (bmComplexScaleRoundedWith_computesInTime hmul W W qWork ratio_m st.1 hratio hst1 hscale_zp)))
    (fun _ => rfl)
  have hnext1_eq : B_s.add (FixedComplex.scaleRounded ratio_m st.1) = nextSt.1 := by
    rw [hnext]; rfl
  have hnext2_eq : roundShiftInt (ratio_m * st.2) qWork = nextSt.2 := by
    rw [hnext]
  have pNextZp := StageEval.congr_out
    (v2 := fun _ => encComplex W nextSt.1)
    (StageEval.seq (StageEval.fanout pB pScaledZp)
      (StageEval.const (S := S)
        (bmComplexAdd_computesInTime W B_s (FixedComplex.scaleRounded ratio_m st.1)
          hB hscale_zp (by rw [hnext1_eq]; exact hnext1))))
    (fun _ => by rw [hnext1_eq])
  have hprod_zh : FitsSignedWord (2 * W) (ratio_m * st.2) := by
    simpa [Nat.two_mul] using hratio.mul hst2
  have pProdZh := StageEval.seq (StageEval.fanout pRatio pZh)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W ratio_m st.2 hratio hst2))
  have pShiftedZh := StageEval.seq (StageEval.fanout pQWork pProdZh)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime (2 * W) qWork (ratio_m * st.2) hprod_zh))
  have pNextZh := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W nextSt.2)
    (StageEval.seq (StageEval.fanout pW pShiftedZh)
      (StageEval.const (S := S)
        (bmResizeSignedWord_computesInTime (2 * W) W (roundShiftInt (ratio_m * st.2) qWork)
          (hprod_zh.roundShiftInt qWork) (by rw [hnext2_eq]; exact hnext2))))
    (fun _ => by rw [hnext2_eq])
  have pPair := StageEval.congr_out
    (v2 := fun _ => encPair (encComplex W) (encodeSignedWord W) nextSt)
    (StageEval.fanout pNextZp pNextZh)
    (fun _ => rfl)
  rcases pPair () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uElem, uQR, uSt] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- **Bidiagonal Row Reconstruction Stage (`bmBidiagReconEntryWith bmMul`)**:
Consumes `encPair (encPair (encPair encUnary encUnary) (encComplex W)) (encPair (encComplex W) (encodeSignedWord W)) (((q, qWork), Z0), (zp, zh))`
and computes `encComplex W (FixedComplex.rescale q (zp + FixedComplex.scaleRounded zh Z0))`. -/
def bmBidiagReconEntryWith (bmMul : BitMachine) : BitMachine :=
  let bmCtx := bmFst
  let bmSt := bmSnd
  let bmQ := bmSeq (bmSeq bmCtx bmFst) bmFst
  let bmQWork := bmSeq (bmSeq bmCtx bmFst) bmSnd
  let bmZ0 := bmSeq bmCtx bmSnd
  let bmZp := bmSeq bmSt bmFst
  let bmZh := bmSeq bmSt bmSnd
  let bmW := bmSeq bmZh bmSignedWidth
  let bmScaled :=
    bmSeq (bmFanout (bmFanout bmW bmQWork) (bmFanout bmZh bmZ0))
      (bmComplexScaleRoundedWith bmMul)
  let bmSum := bmSeq (bmFanout bmZp bmScaled) bmComplexAdd
  bmSeq (bmFanout (bmFanout bmW (bmFanout bmQWork bmQ)) bmSum) bmComplexRescale

theorem bmBidiagReconEntryWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W q qWork : ℕ) (Z0 : FixedComplex qWork) (st : FixedComplex qWork × ℤ)
    (hZ0 : WordWidthBounds W Z0) (hst1 : WordWidthBounds W st.1) (hst2 : FitsSignedWord W st.2)
    (hscaled : WordWidthBounds W (FixedComplex.scaleRounded st.2 Z0))
    (hsum : WordWidthBounds W (st.1 + FixedComplex.scaleRounded st.2 Z0))
    (hout : WordWidthBounds W (FixedComplex.rescale q (st.1 + FixedComplex.scaleRounded st.2 Z0)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 4 * mulTime W + 90000 * W + 50000 * q + 50000 * qWork + 200000,
      (bmBidiagReconEntryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary encUnary) (encComplex W))
            (encPair (encComplex W) (encodeSignedWord W))
            (((q, qWork), Z0), st)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encComplex W (FixedComplex.rescale q (st.1 + FixedComplex.scaleRounded st.2 Z0))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uQQ : S → List Bool := fun _ => encPair encUnary encUnary (q, qWork)
  let uCtx : S → List Bool := encDepPair uQQ (fun _ => encComplex W Z0)
  let uSt : S → List Bool := fun _ => encPair (encComplex W) (encodeSignedWord W) st
  let uIn : S → List Bool := encDepPair uCtx uSt
  have pCtx := StageEval.fst uCtx uSt
  have pSt := StageEval.snd uCtx uSt
  have pQQ := StageEval.seq pCtx (StageEval.fst uQQ (fun _ => encComplex W Z0))
  have pZ0 := StageEval.seq pCtx (StageEval.snd uQQ (fun _ => encComplex W Z0))
  have pQ := StageEval.seq pQQ
    (StageEval.fst (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pQWork := StageEval.seq pQQ
    (StageEval.snd (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pZp := StageEval.seq pSt
    (StageEval.fst (fun _ : S => encComplex W st.1) (fun _ : S => encodeSignedWord W st.2))
  have pZh := StageEval.seq pSt
    (StageEval.snd (fun _ : S => encComplex W st.1) (fun _ : S => encodeSignedWord W st.2))
  have pW := StageEval.seq pZh
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => st.2))
  have pScaled := StageEval.congr_out
    (v2 := fun _ => encComplex W (FixedComplex.scaleRounded st.2 Z0))
    (StageEval.seq
      (StageEval.fanout (StageEval.fanout pW pQWork) (StageEval.fanout pZh pZ0))
      (StageEval.const (S := S)
        (bmComplexScaleRoundedWith_computesInTime hmul W W qWork st.2 Z0 hst2 hZ0 hscaled)))
    (fun _ => rfl)
  have hsum_eq : st.1.add (FixedComplex.scaleRounded st.2 Z0) = st.1 + FixedComplex.scaleRounded st.2 Z0 := rfl
  have pSum := StageEval.congr_out
    (v2 := fun _ => encComplex W (st.1 + FixedComplex.scaleRounded st.2 Z0))
    (StageEval.seq (StageEval.fanout pZp pScaled)
      (StageEval.const (S := S)
        (bmComplexAdd_computesInTime W st.1 (FixedComplex.scaleRounded st.2 Z0)
          hst1 hscaled (by rw [hsum_eq]; exact hsum))))
    (fun _ => by rw [hsum_eq])
  have pOut := StageEval.seq
    (StageEval.fanout (StageEval.fanout pW (StageEval.fanout pQWork pQ)) pSum)
    (StageEval.const (S := S)
      (bmComplexRescale_computesInTime W W qWork q
        (st.1 + FixedComplex.scaleRounded st.2 Z0) hsum hout))
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uCtx, uQQ, uSt] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by linarith only [ht], hcomp⟩

/-- **Sub-stage 3A (`bmBidiagSweepPrepWith bmMul`)**:
Consumes `encPair (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W))) (encList (encComplex W)) ((q, (a_max, a_min)), Y_list)`
and prepares `((q, qWork), (B_ctx_list, ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)))` at width `W = 10 * q`. -/
def bmBidiagSweepPrepWith (bmMul : BitMachine) : BitMachine :=
  let bmQ := bmSeq bmFst bmFst
  let bmAMax := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmAMin := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmYList := bmSnd
  let bmQWork := bmSeq (bmFanout bmQ (bmUnaryConst 9)) bmUnaryAdd
  let bmW := bmSeq (bmFanout (bmUnaryConst 10) bmQ) bmUnaryMul
  let bmQQWork := bmSeq (bmFanout bmQ bmQWork) bmUnaryAdd
  let bmPowQQ := bmSeq (bmFanout bmW bmQQWork) bmSignedTwoPow
  let bmAMaxW := bmSeq (bmFanout bmW bmAMax) bmResizeSignedWord
  let bmInvA := bmSeq (bmFanout bmPowQQ bmAMaxW) bmRoundDivInt
  let bmNegAMin := bmSeq bmAMin bmSignedNeg
  let bmShiftAMin := bmSeq (bmFanout bmQWork bmNegAMin) bmShiftLeftSigned
  let bmNumRatio := bmSeq (bmFanout bmW bmShiftAMin) bmResizeSignedWord
  let bmRatio := bmSeq (bmFanout bmNumRatio bmAMaxW) bmRoundDivInt
  let bmScaleCtx := bmFanout (bmFanout bmQ bmQWork) (bmFanout bmInvA bmRatio)
  let bmBCtxList := bmSeq (bmFanout bmScaleCtx bmYList) (bmMapWithCtx (bmBidiagScaleEntryWith bmMul))
  let bmZeroZ := bmSeq bmW bmComplexZero
  let bmTwoPowQW := bmSeq (bmFanout bmW bmQWork) bmSignedTwoPow
  let bmSt0 := bmFanout bmZeroZ bmTwoPowQW
  bmFanout (bmFanout bmQ bmQWork) (bmFanout bmBCtxList bmSt0)

theorem bmBidiagSweepPrepWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (t1 q : ℕ) (hq : 14 ≤ q) (a_max a_min : ℤ)
    (ha_max : FitsSignedWord (3 * q) a_max) (ha_min : FitsSignedWord (3 * q) a_min)
    (ha_nn : 0 ≤ a_min) (ha_le : a_max ≥ a_min)
    (Y_seq : ℕ → FixedComplex q)
    (hY : ∀ s : ℕ, WordWidthBounds (3 * q) (Y_seq s))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let qWork := q + 9
    let W := 10 * q
    let invA_m := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
    let ratio_m := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
    let Y_list := (List.finRange t1).map (fun s => Y_seq s.val)
    let B_ctx_list := (List.finRange t1).map (fun s =>
      ((qWork, ratio_m), FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq s.val))))
    let st0 : FixedComplex qWork × ℤ := ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    ∃ t ≤ t1 * (4 * mulTime W + 1500000 * q + 1000000) + 3000000 * q * q + 1500000 * q + 1000000,
      (bmBidiagSweepPrepWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W)))
            (encList (encComplex W))
            ((q, (a_max, a_min)), Y_list)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair
              (encList (encPair (encPair encUnary (encodeSignedWord W)) (encComplex W)))
              (encPair (encComplex W) (encodeSignedWord W)))
            ((q, qWork), (B_ctx_list, st0))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro qWork W invA_m ratio_m Y_list B_ctx_list st0
  let S := Unit
  let uAB : S → List Bool := fun _ =>
    encPair (encodeSignedWord W) (encodeSignedWord W) (a_max, a_min)
  let uLhs : S → List Bool := encDepPair (fun _ => encUnary q) uAB
  let uYList : S → List Bool := fun _ => encList (encComplex W) Y_list
  let uIn : S → List Bool := encDepPair uLhs uYList
  have pLhs := StageEval.fst uLhs uYList
  have pYList := StageEval.snd uLhs uYList
  have pQ := StageEval.seq pLhs (StageEval.fst (fun _ : S => encUnary q) uAB)
  have pAB := StageEval.seq pLhs (StageEval.snd (fun _ : S => encUnary q) uAB)
  have pAMax := StageEval.seq pAB
    (StageEval.fst (fun _ : S => encodeSignedWord W a_max)
      (fun _ : S => encodeSignedWord W a_min))
  have pAMin := StageEval.seq pAB
    (StageEval.snd (fun _ : S => encodeSignedWord W a_max)
      (fun _ : S => encodeSignedWord W a_min))
  have p9 := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 9 id) uIn
  have pQWork := StageEval.seq (StageEval.fanout pQ p9)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (q, 9)))
  have p10 := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 10 id) uIn
  have pW := StageEval.seq (StageEval.fanout p10 pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (10, q)))
  have pQQWork := StageEval.seq (StageEval.fanout pQ pQWork)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (q, qWork)))
  have hW_pos : 1 ≤ W := by omega
  have hqq_lt : q + qWork < W := by omega
  have hqw_lt : qWork < W := by omega
  have pPowQQ := StageEval.seq (StageEval.fanout pW pQQWork)
    (StageEval.const (S := S) (bmSignedTwoPow_computesInTime W (q + qWork) hW_pos hqq_lt))
  have ha_maxW : FitsSignedWord W a_max := ha_max.mono (by omega)
  have ha_minW : FitsSignedWord W a_min := ha_min.mono (by omega)
  have pAMaxW := StageEval.seq (StageEval.fanout pW pAMax)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W W a_max ha_maxW ha_maxW))
  have hpow_qq : FitsSignedWord W ((2 : ℤ) ^ (q + qWork)) :=
    (FitsSignedWord.two_pow (q + qWork)).mono (by omega)
  have pInvA := StageEval.seq (StageEval.fanout pPowQQ pAMaxW)
    (StageEval.const (S := S) (bmRoundDivInt_computesInTime W ((2 : ℤ) ^ (q + qWork)) a_max hpow_qq ha_maxW))
  have hinv_bds3 : FitsSignedWord (3 * q) invA_m :=
    ((FitsSignedWord.two_pow (q + qWork)).roundDivInt a_max).mono (by omega)
  have pNegAMin := StageEval.seq pAMin
    (StageEval.const (S := S) (bmSignedNeg_computesInTime W a_min ha_minW))
  have hneg_aminW : FitsSignedWord W (-a_min) := ha_minW.neg
  have pShiftAMin := StageEval.seq (StageEval.fanout pQWork pNegAMin)
    (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime qWork W (-a_min) hneg_aminW))
  have hshift_aminW : FitsSignedWord (qWork + W) (-a_min * (2 : ℤ) ^ qWork) := by
    simpa [Nat.add_comm] using hneg_aminW.mul_two_pow qWork
  have hnum_ratioW : FitsSignedWord W (-a_min * (2 : ℤ) ^ qWork) :=
    (ha_min.neg.mul_two_pow qWork).mono (by omega)
  have pNumRatio := StageEval.seq (StageEval.fanout pW pShiftAMin)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime (qWork + W) W (-a_min * (2 : ℤ) ^ qWork) hshift_aminW hnum_ratioW))
  have pRatio := StageEval.seq (StageEval.fanout pNumRatio pAMaxW)
    (StageEval.const (S := S)
      (bmRoundDivInt_computesInTime W (-a_min * (2 : ℤ) ^ qWork) a_max hnum_ratioW ha_maxW))
  have hratio_le : |ratio_m| ≤ (2 : ℤ) ^ qWork := by
    by_cases hmax0 : a_max = 0
    · simp [ratio_m, hmax0, roundDivInt]
    · apply abs_roundDivInt_le_of_abs_le_mul (by positivity)
      rw [abs_mul, abs_neg, abs_of_nonneg ha_nn, abs_of_nonneg (by omega : 0 ≤ a_max),
        abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ qWork), mul_comm ((2 : ℤ) ^ qWork) a_max]
      exact mul_le_mul_of_nonneg_right ha_le (by positivity)
  have hratio_fitsW : FitsSignedWord W ratio_m := by
    rw [fitsSignedWord_iff_abs_lt]
    exact lt_of_le_of_lt hratio_le (pow_lt_pow_right₀ (by decide) hqw_lt)
  have pScaleCtx := StageEval.fanout (StageEval.fanout pQ pQWork) (StageEval.fanout pInvA pRatio)
  let encScaleCtx := encPair (encPair encUnary encUnary)
    (encPair (encodeSignedWord W) (encodeSignedWord W))
  let scaleCtxVal := ((q, qWork), (invA_m, ratio_m))
  let encBCtx := encPair (encPair encUnary (encodeSignedWord W)) (encComplex W (q := qWork))
  let SubS := { p : S × Fin t1 // p.2 ∈ List.finRange t1 }
  have hScaleStep : StageEval (S := SubS) (bmBidiagScaleEntryWith bmMul)
      (encDepPair (fun _ => encScaleCtx scaleCtxVal)
        (fun p => encComplex W (Y_seq p.val.2.val)))
      (fun p => encBCtx
        ((qWork, ratio_m), FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq p.val.2.val))))
      (fun _ => 4 * mulTime W + 1200000 * q + 600000) := by
    intro p u2 u3 u4 u5 uS
    rcases bmBidiagScaleEntryWith_computesInTime hmul q hq invA_m ratio_m (Y_seq p.val.2.val)
      hinv_bds3 hratio_fitsW (hY p.val.2.val) u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, encScaleCtx, scaleCtxVal, encBCtx, W, qWork, id] at ht hc ⊢
    exact ⟨t, ht, hc⟩
  have pMapB := StageEval.congr_out
    (v2 := fun _ : S => encList encBCtx B_ctx_list)
    (StageEval.congr_in
      (u2 := encDepPair (fun _ : S => encScaleCtx scaleCtxVal) uYList)
      (StageEval.mapWithCtx_uniform (S := S)
        (ctx := fun _ => encScaleCtx scaleCtxVal)
        (xs := fun _ => List.finRange t1)
        (encA := fun _ s => encComplex W (Y_seq s.val))
        (encB := fun _ => encBCtx)
        (fn := fun _ s =>
          ((qWork, ratio_m), FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq s.val))))
        (B := fun _ => 4 * mulTime W + 1200000 * q + 600000)
        (L_A := fun _ => 40 * q + 8)
        (L_B := fun _ => 124 * q + 68)
        hScaleStep
        (fun _ _ _ => by
          rw [length_encComplex W]
          omega)
        (fun _ _ _ => by
          dsimp only [encBCtx, W, qWork]
          simp only [length_encPair, length_encUnary, length_encodeSignedWord, length_encComplex]
          linarith))
      (fun _ => by simp only [encDepPair, uYList, Y_list, encList, List.map_map, Function.comp_def]))
    (fun _ => rfl)
  have pBCtxList := StageEval.seq (StageEval.fanout pScaleCtx pYList) pMapB
  have pZeroZ := StageEval.seq pW (StageEval.const (S := S) (bmComplexZero_computesInTime W qWork))
  have pTwoPowQW := StageEval.seq (StageEval.fanout pW pQWork)
    (StageEval.const (S := S) (bmSignedTwoPow_computesInTime W qWork hW_pos hqw_lt))
  have pSt0 := StageEval.fanout pZeroZ pTwoPowQW
  have pAll := StageEval.fanout (StageEval.fanout pQ pQWork) (StageEval.fanout pBCtxList pSt0)
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_Y : (encList (encComplex W) Y_list).length = t1 * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq (encComplex W (q := q)) (40 * q + 8) Y_list
      (fun y _ => by rw [length_encComplex W]; omega)]
    simp only [Y_list, List.length_map, List.length_finRange]
    ring
  have hlen_B : (encList encBCtx B_ctx_list).length = t1 * (248 * q + 138) := by
    rw [length_encList_eq_of_forall_eq encBCtx (124 * q + 68) B_ctx_list
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨s, _, rfl⟩
        dsimp only [encBCtx, W, qWork]
        simp only [length_encPair, length_encUnary, length_encodeSignedWord, length_encComplex]
        ring)]
    simp only [B_ctx_list, List.length_map, List.length_finRange]
    ring
  dsimp only [uIn, uLhs, uAB, uYList, encScaleCtx, scaleCtxVal, id] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord, List.length_finRange, hlen_Y, hlen_B] at ht
  dsimp only [W, qWork] at ht
  dsimp only [uIn, uLhs, uAB, uYList, encScaleCtx, scaleCtxVal, encBCtx, W, qWork, id] at hcomp ⊢
  refine ⟨t, ?_, hcomp⟩
  clear hcomp pAll pSt0 pTwoPowQW pZeroZ pBCtxList pMapB hScaleStep pScaleCtx pRatio pNumRatio
    pShiftAMin pNegAMin pInvA pAMaxW pPowQQ pQQWork pW pQWork
  ring_nf at ht ⊢
  omega

/-- **Sub-stage 3B (`bmBidiagSweepFinishWith bmMul`)**:
Consumes `((q, qWork), (B_ctx_list, st_0))` on `kIO`, runs `bmScanlList (bmBidiagStepWith bmMul)` to
build the recurrence trajectory `(traj_list, lastSt)`, solves the periodic boundary condition `Z0`,
and maps `bmBidiagReconEntryWith bmMul` over `traj_list`. -/
def bmBidiagSweepFinishWith (bmMul : BitMachine) : BitMachine :=
  let bmScanStage := bmMapSnd (bmScanlList (bmBidiagStepWith bmMul))
  let bmQQ := bmFst
  let bmQWork := bmSeq bmQQ bmSnd
  let bmTrajList := bmSeq bmSnd bmFst
  let bmLastSt := bmSeq bmSnd bmSnd
  let bmLastZp := bmSeq bmLastSt bmFst
  let bmLastZh := bmSeq bmLastSt bmSnd
  let bmW := bmSeq bmLastZh bmSignedWidth
  let bmTwoPowQW := bmSeq (bmFanout bmW bmQWork) bmSignedTwoPow
  let bmDenom := bmSeq (bmFanout bmTwoPowQW bmLastZh) bmSignedSub
  let bmZ0 := bmSeq (bmFanout (bmFanout bmW bmQWork) (bmFanout bmLastZp bmDenom)) bmDivScalarFixed
  let bmReconCtx := bmFanout bmQQ bmZ0
  bmSeq bmScanStage
    (bmSeq (bmFanout bmReconCtx bmTrajList) (bmMapWithCtx (bmBidiagReconEntryWith bmMul)))

/-- **Complete Single-Pass $O(t_1)$ Bidiagonal Recurrence Sweep Stage (`bmBidiagSweepCoreWith bmMul`)**:
Consumes `encPair (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W))) (encList (encComplex W)) ((q, (a_max, a_min)), Y_list)`
where `Y_list = (List.finRange t1).map (fun s => Y_seq s.val)` and emits
`encList (encComplex (10 * q)) ((List.finRange t1).map (bidiagSweepFixed t1 q a_max a_min Y_seq (fun u1 => u1.val)))`
in $O(t_1 \cdot (M(10 q) + q) + q^2)$ `TM2.step` transitions. -/
def bmBidiagSweepCoreWith (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmBidiagSweepPrepWith bmMul) (bmBidiagSweepFinishWith bmMul)

theorem wordWidthBounds_scaleRounded_right {w1 w2 q : ℕ} {m : ℤ} {z : FixedComplex q}
    (hm : FitsSignedWord w1 m) (hz : WordWidthBounds (w2 + q) z) :
    WordWidthBounds (w1 + w2 + 1) (FixedComplex.scaleRounded m z) := by
  refine ⟨?_, ?_⟩
  · have hmul : FitsSignedWord ((w1 + w2) + q) (m * z.re) := (hm.mul hz.1).mono (by omega)
    exact hmul.roundShiftInt_sub
  · have hmul : FitsSignedWord ((w1 + w2) + q) (m * z.im) := (hm.mul hz.2).mono (by omega)
    exact hmul.roundShiftInt_sub

set_option maxHeartbeats 800000 in
theorem wordWidthBounds_bidiagSweepFixed (t1 q : ℕ) (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (a_max a_min : ℤ) (ha_nn : 0 ≤ a_min) (ha_le : a_max ≥ a_min)
    (Y_seq : ℕ → FixedComplex q) (hY : ∀ s : ℕ, WordWidthBounds (3 * q) (Y_seq s))
    (idx : Fin t1 → ℕ) (hidx : ∀ u1 : Fin t1, idx u1 ≤ t1) (u1 : Fin t1) :
    WordWidthBounds (10 * q) (bidiagSweepFixed t1 q a_max a_min Y_seq idx u1) := by
  unfold bidiagSweepFixed
  dsimp only
  rw [memoizeFin_eq]
  set qWork : ℕ := q + 9
  have hpow_fits : FitsSignedWord (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) :=
    (FitsSignedWord.two_pow (q + qWork)).mono (by omega)
  set invA := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
  have hinv_bds : FitsSignedWord (3 * q) invA :=
    (FitsSignedWord.roundDivInt a_max hpow_fits).mono (by omega)
  have hrs_bds : ∀ s : ℕ, WordWidthBounds (4 * q) (FixedComplex.rescale qWork (Y_seq s)) := by
    intro s
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 9 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY s).1.mul_two_pow 9).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY s).2.mul_two_pow 9).mono (by omega)
  have hratio_le : |roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max| ≤ (2 : ℤ) ^ qWork := by
    by_cases hmax0 : a_max = 0
    · simp [hmax0, roundDivInt]
    · apply abs_roundDivInt_le_of_abs_le_mul (by positivity)
      rw [abs_mul, abs_neg, abs_of_nonneg ha_nn, abs_of_nonneg (by omega : 0 ≤ a_max),
        abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ qWork), mul_comm ((2 : ℤ) ^ qWork) a_max]
      exact mul_le_mul_of_nonneg_right ha_le (by positivity)
  set B_sc := memoizeRange t1 (fun s =>
    FixedComplex.scaleRounded invA (FixedComplex.rescale qWork (Y_seq s)))
  have hB_bds : ∀ s : ℕ, WordWidthBounds (7 * q) (B_sc s) := by
    intro s
    dsimp [B_sc]
    rw [memoizeRange_eq]
    exact ⟨((hinv_bds.mul (hrs_bds s).1).roundShiftInt qWork).mono (by omega),
           ((hinv_bds.mul (hrs_bds s).2).roundShiftInt qWork).mono (by omega)⟩
  set ratio_val := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
  have hst_bds : ∀ s ≤ t1,
      let st := (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
        (bidiagSweepStepFixed qWork ratio_val B_sc) s).2
      WordWidthBounds (8 * q + 1) st.1 ∧ FitsSignedWord (qWork + 1) st.2 := by
    intro s hs
    have habs := abs_buildRecurrenceArray_bidiagSweepStepFixed_le qWork (7 * q)
      ratio_val hratio_le B_sc hB_bds s
    have hs_pow : (s : ℤ) * (2 : ℤ) ^ (7 * q) < (2 : ℤ) ^ (8 * q + 1) := by
      have hs_le : (s : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast (hs.trans ht1)
      calc (s : ℤ) * (2 : ℤ) ^ (7 * q)
          ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ (7 * q) := mul_le_mul_of_nonneg_right hs_le (by positivity)
        _ = (2 : ℤ) ^ (8 * q) := by rw [← pow_add, show q + 7 * q = 8 * q by ring]
        _ < (2 : ℤ) ^ (8 * q + 1) := pow_lt_pow_right₀ (by decide) (by omega)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [fitsSignedWord_iff_abs_lt]; exact lt_of_le_of_lt habs.1 hs_pow
    · rw [fitsSignedWord_iff_abs_lt]; exact lt_of_le_of_lt habs.2.1 hs_pow
    · rw [fitsSignedWord_iff_abs_lt]
      exact lt_of_le_of_lt habs.2.2 (pow_lt_pow_right₀ (by decide) (by omega))
  set recVal := buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    (bidiagSweepStepFixed qWork ratio_val B_sc) t1
  have hlast_bds : WordWidthBounds (8 * q + 1) recVal.2.1 := (hst_bds t1 (le_refl t1)).1
  set Z0_val := divScalarFixed qWork qWork recVal.2.1 ((2 : ℤ) ^ qWork - recVal.2.2)
  have hZ0_bds : WordWidthBounds ((8 * q + 1) + qWork) Z0_val :=
    ⟨FitsSignedWord.roundDivInt _ (hlast_bds.1.mul_two_pow qWork),
     FitsSignedWord.roundDivInt _ (hlast_bds.2.mul_two_pow qWork)⟩
  rw [getD_buildRecurrenceArray _ _ (hidx u1)]
  have hst_u1 := hst_bds (idx u1) (hidx u1)
  have hsc_bds : WordWidthBounds ((qWork + 1) + (8 * q + 1) + 1)
      (FixedComplex.scaleRounded
        (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
          (bidiagSweepStepFixed qWork ratio_val B_sc) (idx u1)).2.2 Z0_val) :=
    wordWidthBounds_scaleRounded_right hst_u1.2 hZ0_bds
  have hsum_bds : WordWidthBounds (9 * q + 13)
      ((buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
          (bidiagSweepStepFixed qWork ratio_val B_sc) (idx u1)).2.1 +
        FixedComplex.scaleRounded
          (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
            (bidiagSweepStepFixed qWork ratio_val B_sc) (idx u1)).2.2 Z0_val) :=
    ⟨FitsSignedWord.add (hst_u1.1.1.mono (by omega)) (hsc_bds.1.mono (by omega)),
     FitsSignedWord.add (hst_u1.1.2.mono (by omega)) (hsc_bds.2.mono (by omega))⟩
  have hsub1 : q - qWork = 0 := by omega
  have hsub2 : qWork - q = 9 := by omega
  refine ⟨?_, ?_⟩
  · simp only [FixedComplex.rescale, hsub1, hsub2, pow_zero, mul_one]
    exact (hsum_bds.1.roundShiftInt 9).mono (by omega)
  · simp only [FixedComplex.rescale, hsub1, hsub2, pow_zero, mul_one]
    exact (hsum_bds.2.roundShiftInt 9).mono (by omega)

set_option maxHeartbeats 800000 in
theorem bmBidiagSweepCoreWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (t1 q : ℕ) (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (a_max a_min : ℤ)
    (ha_max : FitsSignedWord (3 * q) a_max) (ha_min : FitsSignedWord (3 * q) a_min)
    (ha_nn : 0 ≤ a_min) (ha_le : a_max ≥ a_min)
    (Y_seq : ℕ → FixedComplex q)
    (hY : ∀ s : ℕ, WordWidthBounds (3 * q) (Y_seq s))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W := 10 * q
    let Y_list := (List.finRange t1).map (fun s => Y_seq s.val)
    ∃ t ≤ t1 * (14 * mulTime W + 5000000 * q + 3500000) + 10000000 * q * q + 5000000 * q + 3000000,
      (bmBidiagSweepCoreWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W)))
            (encList (encComplex W))
            ((q, (a_max, a_min)), Y_list)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W)
            ((List.finRange t1).map (bidiagSweepFixed t1 q a_max a_min Y_seq (fun u1 => u1.val)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro W Y_list
  let S := Unit
  let qWork := q + 9
  let invA_m := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
  let ratio_m := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
  let B_sc := memoizeRange t1 (fun s =>
    FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq s)))
  let B_ctx_list := (List.finRange t1).map (fun s =>
    ((qWork, ratio_m), FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq s.val))))
  let st0 : FixedComplex qWork × ℤ := ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
  let stFn : ℕ → FixedComplex qWork × ℤ := fun s =>
    (buildRecurrenceArray st0 (bidiagSweepStepFixed qWork ratio_m B_sc) s).2
  have hpow_fits : FitsSignedWord (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) :=
    (FitsSignedWord.two_pow (q + qWork)).mono (by omega)
  have hinv_bds : FitsSignedWord (3 * q) invA_m :=
    (FitsSignedWord.roundDivInt a_max hpow_fits).mono (by omega)
  have hrs_bds : ∀ s : ℕ, WordWidthBounds (4 * q) (FixedComplex.rescale qWork (Y_seq s)) := by
    intro s
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 9 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY s).1.mul_two_pow 9).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY s).2.mul_two_pow 9).mono (by omega)
  have hratio_le : |ratio_m| ≤ (2 : ℤ) ^ qWork := by
    by_cases hmax0 : a_max = 0
    · simp [ratio_m, hmax0, roundDivInt]
    · apply abs_roundDivInt_le_of_abs_le_mul (by positivity)
      rw [abs_mul, abs_neg, abs_of_nonneg ha_nn, abs_of_nonneg (by omega : 0 ≤ a_max),
        abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ qWork), mul_comm ((2 : ℤ) ^ qWork) a_max]
      exact mul_le_mul_of_nonneg_right ha_le (by positivity)
  have hratio_fits1 : FitsSignedWord (qWork + 1) ratio_m := by
    rw [fitsSignedWord_iff_abs_lt]
    exact lt_of_le_of_lt hratio_le (pow_lt_pow_right₀ (by decide) (by omega))
  have hratio_fitsW : FitsSignedWord W ratio_m := hratio_fits1.mono (by omega)
  have hB_bds : ∀ s : ℕ, WordWidthBounds (7 * q) (B_sc s) := by
    intro s
    dsimp [B_sc]
    rw [memoizeRange_eq]
    exact ⟨((hinv_bds.mul (hrs_bds s).1).roundShiftInt qWork).mono (by omega),
           ((hinv_bds.mul (hrs_bds s).2).roundShiftInt qWork).mono (by omega)⟩
  have hst_bds : ∀ s ≤ t1,
      WordWidthBounds (8 * q + 1) (stFn s).1 ∧ FitsSignedWord (qWork + 1) (stFn s).2 := by
    intro s hs
    have habs := abs_buildRecurrenceArray_bidiagSweepStepFixed_le qWork (7 * q)
      ratio_m hratio_le B_sc hB_bds s
    have hs_pow : (s : ℤ) * (2 : ℤ) ^ (7 * q) < (2 : ℤ) ^ (8 * q + 1) := by
      have hs_le : (s : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast (hs.trans ht1)
      calc (s : ℤ) * (2 : ℤ) ^ (7 * q)
          ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ (7 * q) := mul_le_mul_of_nonneg_right hs_le (by positivity)
        _ = (2 : ℤ) ^ (8 * q) := by rw [← pow_add, show q + 7 * q = 8 * q by ring]
        _ < (2 : ℤ) ^ (8 * q + 1) := pow_lt_pow_right₀ (by decide) (by omega)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [fitsSignedWord_iff_abs_lt]; exact lt_of_le_of_lt habs.1 hs_pow
    · rw [fitsSignedWord_iff_abs_lt]; exact lt_of_le_of_lt habs.2.1 hs_pow
    · rw [fitsSignedWord_iff_abs_lt]
      exact lt_of_le_of_lt habs.2.2 (pow_lt_pow_right₀ (by decide) (by omega))
  have pPrep := StageEval.const (S := S)
    (bmBidiagSweepPrepWith_computesInTime hmul t1 q hq a_max a_min ha_max ha_min ha_nn ha_le Y_seq hY)
  let encBCtx := encPair (encPair encUnary (encodeSignedWord W)) (encComplex W (q := qWork))
  let encSt := encPair (encComplex W (q := qWork)) (encodeSignedWord W)
  let uQQ : S → List Bool := fun _ => encPair encUnary encUnary (q, qWork)
  have hStepEval : StageEval (S := { p : S × ℕ // p.2 < B_ctx_list.length }) (bmBidiagStepWith bmMul)
      (encDepPair (fun p => encBCtx (B_ctx_list[p.val.2]'p.property))
        (fun p => encSt (stFn p.val.2)))
      (fun p => encSt (stFn (p.val.2 + 1)))
      (fun _ => 6 * mulTime W + 100000 * W + 20000 * qWork + 200000) := by
    intro ⟨⟨_, s⟩, hs⟩ u2 u3 u4 u5 uS
    have hs_lt : s < t1 := by simpa [B_ctx_list] using hs
    have hget : B_ctx_list[s]'hs = ((qWork, ratio_m), B_sc s) := by
      simp only [B_ctx_list, B_sc, List.getElem_map, List.getElem_finRange, Fin.val_cast, memoizeRange_eq]
    have hst_s := hst_bds s (le_of_lt hs_lt)
    have hst_s1 := hst_bds (s + 1) hs_lt
    have hsc_zp : WordWidthBounds W (FixedComplex.scaleRounded ratio_m (stFn s).1) :=
      ⟨((hratio_fits1.mul hst_s.1.1).roundShiftInt qWork).mono (by omega),
       ((hratio_fits1.mul hst_s.1.2).roundShiftInt qWork).mono (by omega)⟩
    rcases bmBidiagStepWith_computesInTime hmul W qWork ratio_m (B_sc s) (stFn s) (stFn (s + 1))
      rfl hratio_fitsW ((hB_bds s).mono (by omega))
      (hst_s.1.mono (by omega)) (hst_s.2.mono (by omega)) hsc_zp
      (hst_s1.1.mono (by omega)) (hst_s1.2.mono (by omega)) u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, id] at ht hc ⊢
    rw [hget]
    exact ⟨t, ht, hc⟩
  have pScan := StageEval.scanlList_idx (S := S)
    (encElem := fun _ => encBCtx) (encAcc := fun _ => encSt)
    (xs := fun _ => B_ctx_list) (st := fun _ => stFn)
    (B := fun _ => 6 * mulTime W + 100000 * W + 20000 * qWork + 200000)
    (L_elem := fun _ => 124 * q + 68)
    (L_acc := fun _ => 100 * q + 22)
    hStepEval
    (fun _ i hi => by
      simp only [B_ctx_list, List.getElem_map, List.getElem_finRange]
      dsimp only [encBCtx, W, qWork]
      simp only [length_encPair, length_encUnary, length_encodeSignedWord, length_encComplex]
      omega)
    (fun _ i hi => by
      dsimp only [encSt, W]
      simp only [length_encPair, length_encComplex, length_encodeSignedWord]
      omega)
  have htraj_eq :
      (List.range B_ctx_list.length).map stFn = (List.finRange t1).map (fun u1 => stFn u1.val) := by
    have hlen : B_ctx_list.length = t1 := by simp [B_ctx_list]
    rw [hlen, ← map_finRange_eq_map_range t1 stFn]
  let traj_list := (List.finRange t1).map (fun u1 => stFn u1.val)
  let lastSt := stFn t1
  have pScanStage := StageEval.congr_out
    (v2 := encDepPair uQQ (fun _ => encPair (encList encSt) encSt (traj_list, lastSt)))
    (StageEval.mapSnd (u1 := uQQ) pScan)
    (fun _ => by
      have hlen : B_ctx_list.length = t1 := by simp [B_ctx_list]
      dsimp only [encDepPair, traj_list, lastSt]
      rw [htraj_eq, hlen])
  let uTrajLast : S → List Bool := fun _ => encPair (encList encSt) encSt (traj_list, lastSt)
  let uMid : S → List Bool := encDepPair uQQ uTrajLast
  have pQQ := StageEval.fst uQQ uTrajLast
  have pTL := StageEval.snd uQQ uTrajLast
  have pQWork := StageEval.seq pQQ
    (StageEval.snd (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pTrajList := StageEval.seq pTL
    (StageEval.fst (fun _ : S => encList encSt traj_list) (fun _ : S => encSt lastSt))
  have pLastSt := StageEval.seq pTL
    (StageEval.snd (fun _ : S => encList encSt traj_list) (fun _ : S => encSt lastSt))
  have pLastZp := StageEval.seq pLastSt
    (StageEval.fst (fun _ : S => encComplex W lastSt.1) (fun _ : S => encodeSignedWord W lastSt.2))
  have pLastZh := StageEval.seq pLastSt
    (StageEval.snd (fun _ : S => encComplex W lastSt.1) (fun _ : S => encodeSignedWord W lastSt.2))
  have pW := StageEval.seq pLastZh
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => lastSt.2))
  have pTwoPowQW := StageEval.seq (StageEval.fanout pW pQWork)
    (StageEval.const (S := S) (bmSignedTwoPow_computesInTime W qWork (by omega) (by omega)))
  have hlast_bds := hst_bds t1 (le_refl t1)
  have h2qw_fits : FitsSignedWord (qWork + 1) ((2 : ℤ) ^ qWork) :=
    FitsSignedWord.two_pow qWork
  have hdenom_fits : FitsSignedWord W ((2 : ℤ) ^ qWork - lastSt.2) :=
    (h2qw_fits.sub hlast_bds.2).mono (by omega)
  have pDenom := StageEval.seq (StageEval.fanout pTwoPowQW pLastZh)
    (StageEval.const (S := S)
      (bmSignedSub_computesInTime W ((2 : ℤ) ^ qWork) lastSt.2
        (h2qw_fits.mono (by omega)) (hlast_bds.2.mono (by omega)) hdenom_fits))
  let Z0 := divScalarFixed qWork qWork lastSt.1 ((2 : ℤ) ^ qWork - lastSt.2)
  have hZ0_bds8 : WordWidthBounds ((8 * q + 1) + qWork) Z0 :=
    ⟨FitsSignedWord.roundDivInt _ (hlast_bds.1.1.mul_two_pow qWork),
     FitsSignedWord.roundDivInt _ (hlast_bds.1.2.mul_two_pow qWork)⟩
  have hZ0_bdsW : WordWidthBounds W Z0 := hZ0_bds8.mono (by omega)
  have pZ0 := StageEval.seq
    (StageEval.fanout (StageEval.fanout pW pQWork) (StageEval.fanout pLastZp pDenom))
    (StageEval.const (S := S)
      (bmDivScalarFixed_computesInTime W W qWork qWork lastSt.1 ((2 : ℤ) ^ qWork - lastSt.2)
        (hlast_bds.1.mono (by omega)) hdenom_fits hZ0_bdsW))
  have pReconCtx := StageEval.fanout pQQ pZ0
  let encReconCtx := encPair (encPair encUnary encUnary) (encComplex W (q := qWork))
  let reconCtxVal := ((q, qWork), Z0)
  let SubU := { p : S × Fin t1 // p.2 ∈ List.finRange t1 }
  have hReconStep : StageEval (S := SubU) (bmBidiagReconEntryWith bmMul)
      (encDepPair (fun _ => encReconCtx reconCtxVal)
        (fun p => encSt (stFn p.val.2.val)))
      (fun p => encComplex W (bidiagSweepFixed t1 q a_max a_min Y_seq (fun u1 => u1.val) p.val.2))
      (fun _ => 4 * mulTime W + 90000 * W + 50000 * q + 50000 * qWork + 200000) := by
    intro p u2 u3 u4 u5 uS
    have hu1_le : p.val.2.val ≤ t1 := le_of_lt p.val.2.isLt
    have hst_u := hst_bds p.val.2.val hu1_le
    have hsc_u : WordWidthBounds ((qWork + 1) + (8 * q + 1) + 1)
        (FixedComplex.scaleRounded (stFn p.val.2.val).2 Z0) :=
      wordWidthBounds_scaleRounded_right hst_u.2 hZ0_bds8
    have hsum_u : WordWidthBounds (9 * q + 13)
        ((stFn p.val.2.val).1 + FixedComplex.scaleRounded (stFn p.val.2.val).2 Z0) :=
      ⟨FitsSignedWord.add (hst_u.1.1.mono (by omega)) (hsc_u.1.mono (by omega)),
       FitsSignedWord.add (hst_u.1.2.mono (by omega)) (hsc_u.2.mono (by omega))⟩
    have hout_u : WordWidthBounds W
        (bidiagSweepFixed t1 q a_max a_min Y_seq (fun u1 => u1.val) p.val.2) :=
      wordWidthBounds_bidiagSweepFixed t1 q hq ht1 a_max a_min ha_nn ha_le Y_seq hY
        (fun u1 => u1.val) (fun u1 => le_of_lt u1.isLt) p.val.2
    have hval_eq :
        FixedComplex.rescale q ((stFn p.val.2.val).1 + FixedComplex.scaleRounded (stFn p.val.2.val).2 Z0) =
          bidiagSweepFixed t1 q a_max a_min Y_seq (fun u1 => u1.val) p.val.2 := by
      unfold bidiagSweepFixed
      dsimp only
      rw [memoizeFin_eq]
      dsimp only [stFn, B_sc, invA_m, ratio_m, qWork, Z0]
      rw [getD_buildRecurrenceArray _ _ hu1_le]
    rcases bmBidiagReconEntryWith_computesInTime hmul W q qWork Z0 (stFn p.val.2.val)
      hZ0_bdsW (hst_u.1.mono (by omega)) (hst_u.2.mono (by omega))
      (hsc_u.mono (by omega)) (hsum_u.mono (by omega))
      (by rw [hval_eq]; exact hout_u) u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, encReconCtx, reconCtxVal, encSt, id] at ht hc ⊢
    rw [hval_eq] at hc
    exact ⟨t, ht, hc⟩
  have pMapRecon := StageEval.congr_in
    (u2 := encDepPair (fun _ : S => encReconCtx reconCtxVal)
      (fun _ : S => encList encSt traj_list))
    (StageEval.mapWithCtx_uniform (S := S)
      (ctx := fun _ => encReconCtx reconCtxVal)
      (xs := fun _ => List.finRange t1)
      (encA := fun _ u1 => encSt (stFn u1.val))
      (encB := fun _ => encComplex W)
      (fn := fun _ u1 => bidiagSweepFixed t1 q a_max a_min Y_seq (fun v => v.val) u1)
      (B := fun _ => 4 * mulTime W + 90000 * W + 50000 * q + 50000 * qWork + 200000)
      (L_A := fun _ => 100 * q + 22)
      (L_B := fun _ => 40 * q + 8)
      hReconStep
      (fun _ _ _ => by
        dsimp only [encSt, W]
        simp only [length_encPair, length_encComplex, length_encodeSignedWord]
        linarith)
      (fun _ _ _ => by
        rw [length_encComplex W]
        omega))
    (fun _ => by simp only [encDepPair, traj_list, encList, List.map_map, Function.comp_def])
  have pFinish := StageEval.seq pScanStage (StageEval.seq (StageEval.fanout pReconCtx pTrajList) pMapRecon)
  have pAll := StageEval.seq pPrep pFinish
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_B : (encList encBCtx B_ctx_list).length = t1 * (248 * q + 138) := by
    rw [length_encList_eq_of_forall_eq encBCtx (124 * q + 68) B_ctx_list
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨s, _, rfl⟩
        dsimp only [encBCtx, W, qWork]
        simp only [length_encPair, length_encUnary, length_encodeSignedWord, length_encComplex]
        ring)]
    simp only [B_ctx_list, List.length_map, List.length_finRange]
    ring
  have hlen_traj : (encList encSt traj_list).length = t1 * (200 * q + 46) := by
    rw [length_encList_eq_of_forall_eq encSt (100 * q + 22) traj_list
      (fun x _ => by
        dsimp only [encSt, W]
        simp only [length_encPair, length_encComplex, length_encodeSignedWord]
        ring)]
    simp only [traj_list, List.length_map, List.length_finRange]
    ring
  have hlen_B_len : B_ctx_list.length = t1 := by simp [B_ctx_list]
  dsimp only [uQQ, uMid, uTrajLast, encReconCtx, reconCtxVal, id] at ht
  rw [htraj_eq] at ht
  dsimp only [traj_list] at ht hlen_traj
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord, List.length_finRange, hlen_B, hlen_traj, hlen_B_len] at ht
  dsimp only [encSt, encBCtx, W, qWork] at ht
  simp only [length_encPair, length_encComplex, length_encodeSignedWord] at ht
  dsimp only [uQQ, uMid, uTrajLast, encReconCtx, reconCtxVal, encSt, encBCtx, W, qWork, id] at hcomp ⊢
  refine ⟨t, ?_, hcomp⟩
  clear hcomp pAll pFinish pMapRecon hReconStep pReconCtx pZ0 pDenom pTwoPowQW pW pLastZh pLastZp
    pLastSt pTrajList pQWork pTL pQQ pScanStage pScan hStepEval pPrep
  ring_nf at ht ⊢
  omega

/-! ## 4. Non-Nyquist Cyclic Bidiagonal Solvers (`bmCyclicBidiagSolveWith`, `bmCyclicBidiagPrevSolveWith`) -/

lemma bidiagSweepFixed_idx_comp (t1 q : ℕ) (a_max a_min : ℤ)
    (Y_seq : ℕ → FixedComplex q) (idx : Fin t1 → ℕ) (f : Fin t1 → Fin t1) (u1 : Fin t1) :
    bidiagSweepFixed t1 q a_max a_min Y_seq (fun v => idx (f v)) u1 =
      bidiagSweepFixed t1 q a_max a_min Y_seq idx (f u1) := by
  unfold bidiagSweepFixed
  dsimp only
  rw [memoizeFin_eq, memoizeFin_eq]

theorem wordWidthBounds_cyclicBidiagSolveFixed {t1 q : ℕ} [NeZero t1]
    (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (a b : ℤ) (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (_ha_le : a ≤ 2 ^ (2 * q)) (_hb_le : b ≤ 2 ^ (2 * q))
    (Y : Fin t1 → FixedComplex q) (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (u1 : Fin t1) :
    WordWidthBounds (10 * q) (cyclicBidiagSolveFixed a b Y u1) := by
  have ht1_pos : 0 < t1 := NeZero.pos t1
  unfold cyclicBidiagSolveFixed
  split_ifs with hba
  · exact wordWidthBounds_bidiagSweepFixed t1 q hq ht1 a b hb_nn hba
      (fun s => Y ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1_pos⟩) (fun _ => hY _)
      (fun v => (t1 - v.val) % t1) (fun v => le_of_lt (Nat.mod_lt _ ht1_pos)) u1
  · exact wordWidthBounds_bidiagSweepFixed t1 q hq ht1 b a ha_nn (by omega)
      (fun s => Y ⟨s % t1, Nat.mod_lt _ ht1_pos⟩) (fun _ => hY _)
      (fun v => v.val) (fun v => le_of_lt v.isLt) u1

theorem wordWidthBounds_cyclicBidiagPrevSolveFixed {t1 q : ℕ} [NeZero t1]
    (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (a b : ℤ) (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (ha_le : a ≤ 2 ^ (2 * q)) (hb_le : b ≤ 2 ^ (2 * q))
    (Y : Fin t1 → FixedComplex q) (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (u1 : Fin t1) :
    WordWidthBounds (10 * q) (cyclicBidiagPrevSolveFixed a b Y u1) :=
  wordWidthBounds_cyclicBidiagSolveFixed hq ht1 b a hb_nn ha_nn hb_le ha_le
    (fun m => Y (cyclicNext m)) (fun _ => hY _) u1

/-- **Uniform Forward-Shift Cyclic Bidiagonal Solver (`bmCyclicBidiagSolveWith bmMul`)**:
Consumes `((q, (a, b)), Y_list)` on `kIO` and emits
`encList (encComplex (10 * q)) ((List.finRange t1).map (cyclicBidiagSolveFixed a b Y))`. -/
def bmCyclicBidiagSolveWith (bmMul : BitMachine) : BitMachine :=
  let bmCond := bmSeq (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSignedSub) bmSignedIsNeg) bmBoolNot
  let bmThen := bmSeq (bmSeq (bmSeq (bmMapSnd bmRevList) (bmBidiagSweepCoreWith bmMul)) bmRotateOneList) bmRevList
  let bmElse := bmSeq (bmMapFst (bmMapSnd (bmFanout bmSnd bmFst)))
    (bmBidiagSweepCoreWith bmMul)
  bmIte bmCond bmThen bmElse

theorem bmCyclicBidiagSolveWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (t1 q : ℕ) [NeZero t1] (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (a b : ℤ) (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (ha_le : a ≤ 2 ^ (2 * q)) (hb_le : b ≤ 2 ^ (2 * q))
    (Y : Fin t1 → FixedComplex q)
    (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W := 10 * q
    ∃ t ≤ (t1 + 1) * (14 * mulTime W + 5500000 * q + 4000000) +
          12000000 * q * q,
      (bmCyclicBidiagSolveWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W)))
            (encList (encComplex W))
            ((q, (a, b)), (List.finRange t1).map Y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W)
            ((List.finRange t1).map (cyclicBidiagSolveFixed a b Y))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro W
  have ht1_pos : 0 < t1 := NeZero.pos t1
  let S := Unit
  let Y_list := (List.finRange t1).map Y
  let uCtx : S → List Bool := fun _ =>
    encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W)) (q, (a, b))
  let uY : S → List Bool := fun _ => encList (encComplex W) Y_list
  let uIn : S → List Bool := encDepPair uCtx uY
  have ha_fits3 : FitsSignedWord (3 * q) a := by
    rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg ha_nn]
    exact lt_of_le_of_lt ha_le (pow_lt_pow_right₀ (by decide) (by omega))
  have hb_fits3 : FitsSignedWord (3 * q) b := by
    rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg hb_nn]
    exact lt_of_le_of_lt hb_le (pow_lt_pow_right₀ (by decide) (by omega))
  have ha_fits : FitsSignedWord W a := ha_fits3.mono (by omega)
  have hb_fits : FitsSignedWord W b := hb_fits3.mono (by omega)
  have hab_sub_fits : FitsSignedWord W (a - b) :=
    (ha_fits3.sub hb_fits3).mono (by omega)
  have pAB := StageEval.seq (StageEval.fst uCtx uY)
    (StageEval.snd (fun _ : S => encUnary q)
      (fun _ : S => encPair (encodeSignedWord W) (encodeSignedWord W) (a, b)))
  have pSub := StageEval.seq pAB
    (StageEval.const (S := S) (bmSignedSub_computesInTime W a b ha_fits hb_fits hab_sub_fits))
  have pNeg := StageEval.seq pSub
    (StageEval.const (S := S) (bmSignedIsNeg_computesInTime W (a - b) hab_sub_fits))
  have pCondRaw := StageEval.seq pNeg
    (StageEval.of_computesStageLe bmBoolNot_computesStageLe (fun _ : S => decide (a - b < 0)))
  have pCond := StageEval.congr_out (v2 := fun _ : S => encBool (decide (b ≤ a))) pCondRaw
    (fun _ => by
      congr 1
      by_cases h : b ≤ a
      · have hnot : ¬(a - b < 0) := by omega
        simp [h, hnot]
      · have hlt : a - b < 0 := by omega
        simp [h, hlt])
  have hlen_Y : (encList (encComplex W) Y_list).length = t1 * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8) Y_list
      (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [Y_list, List.length_map, List.length_finRange]
    ring
  let B_branch := (t1 + 1) * (14 * mulTime W + 5200000 * q + 3700000) +
    12000000 * q * q
  have pIte := StageEval.ite (S := S)
    (v := fun _ => encList (encComplex W)
      ((List.finRange t1).map (cyclicBidiagSolveFixed a b Y)))
    (bTrue := fun _ => B_branch)
    (bFalse := fun _ => B_branch)
    pCond
    (fun _ hs u2 u3 u4 u5 uS => by
      have hba : b ≤ a := of_decide_eq_true hs
      let Y_seq1 : ℕ → FixedComplex q :=
        fun s => Y ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1_pos⟩
      have hrev_eq : Y_list.reverse = (List.finRange t1).map (fun m : Fin t1 => Y_seq1 m.val) :=
        reverse_map_finRange_eq ht1_pos Y
      have pRev := StageEval.congr_out
        (v2 := encDepPair uCtx (fun _ => encList (encComplex W)
          ((List.finRange t1).map (fun m : Fin t1 => Y_seq1 m.val))))
        (StageEval.mapSnd (u1 := uCtx)
          (StageEval.of_computesStageLe (bmRevList_computesStageLe (encComplex W))
            (fun _ : S => Y_list)))
        (fun _ => by simp only [encDepPair, hrev_eq])
      have pSweep := StageEval.seq pRev
        (StageEval.const (S := S)
          (bmBidiagSweepCoreWith_computesInTime hmul t1 q hq ht1 a b
            ha_fits3 hb_fits3 hb_nn hba Y_seq1 (fun _ => hY _)))
      let sweepFn := bidiagSweepFixed t1 q a b Y_seq1 (fun v => v.val)
      have pRot := StageEval.seq pSweep
        (StageEval.const (S := S)
          (bmRotateOneList_computesInTime (encComplex W) (40 * q + 8)
            (fun x => by rw [length_encComplex W]; omega)
            ((List.finRange t1).map sweepFn) (by simp; omega)))
      have pRevOut := StageEval.seq pRot
        (StageEval.of_computesStageLe (bmRevList_computesStageLe (encComplex W))
          (fun _ : S => rotateList 1 ((List.finRange t1).map sweepFn)))
      have hout_eq :
          (rotateList 1 ((List.finRange t1).map sweepFn)).reverse =
            (List.finRange t1).map (cyclicBidiagSolveFixed a b Y) := by
        rw [reverse_rotateOne_map_finRange_eq]
        unfold cyclicBidiagSolveFixed
        rw [if_pos hba]
        apply List.map_congr_left
        intro u1 _
        exact (bidiagSweepFixed_idx_comp t1 q a b Y_seq1 (fun v => v.val)
          (fun v => ⟨(t1 - v.val) % t1, Nat.mod_lt _ ht1_pos⟩) u1).symm
      have pThen := StageEval.congr_out
        (v2 := fun _ : S => encList (encComplex W)
          ((List.finRange t1).map (cyclicBidiagSolveFixed a b Y)))
        pRevOut (fun _ => by rw [hout_eq])
      rcases pThen () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
      have hlen_Y_rev : (encList (encComplex W) Y_list.reverse).length = t1 * (80 * q + 18) := by
        rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8) Y_list.reverse
          (fun x _ => by rw [length_encComplex W]; omega)]
        simp only [List.length_reverse, Y_list, List.length_map, List.length_finRange]
        ring
      have hlen_rot : (encList (encComplex W) (rotateList 1 ((List.finRange t1).map sweepFn))).length =
          t1 * (80 * q + 18) := by
        rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8)
          (rotateList 1 ((List.finRange t1).map sweepFn)) (fun x _ => by rw [length_encComplex W]; omega)]
        simp only [length_rotateList, List.length_map, List.length_finRange]
        ring
      dsimp only [uCtx, uY, id] at ht
      simp only [length_encPair, length_encUnary, length_encodeSignedWord,
        List.length_map, List.length_finRange, hlen_Y, hlen_Y_rev, hlen_rot] at ht
      dsimp only [W] at ht
      refine ⟨t, ?_, hc⟩
      dsimp only [B_branch, W]
      ring_nf at ht ⊢
      omega)
    (fun _ hs u2 u3 u4 u5 uS => by
      have hba : ¬(b ≤ a) := of_decide_eq_false hs
      let Y_seq2 : ℕ → FixedComplex q := fun s => Y ⟨s % t1, Nat.mod_lt _ ht1_pos⟩
      have hY_eq : Y_list = (List.finRange t1).map (fun m : Fin t1 => Y_seq2 m.val) := by
        apply List.ext_getElem
        · simp [Y_list]
        · intro i h1 h2
          have hi : i < t1 := by simpa [Y_list] using h2
          simp only [Y_list, List.getElem_map, List.getElem_finRange]
          congr 1
          ext
          dsimp only [Fin.val_cast]
          exact (Nat.mod_eq_of_lt hi).symm
      let uA : S → List Bool := fun _ => encodeSignedWord W a
      let uB : S → List Bool := fun _ => encodeSignedWord W b
      have pSwapAB := StageEval.fanout (StageEval.snd uA uB) (StageEval.fst uA uB)
      have pSwapCtx := StageEval.mapSnd (u1 := fun _ : S => encUnary q) pSwapAB
      have pSwapIn := StageEval.congr_out
        (v2 := fun _ : S =>
          encPair (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W)))
            (encList (encComplex W))
            ((q, (b, a)), (List.finRange t1).map (fun m : Fin t1 => Y_seq2 m.val)))
        (StageEval.mapFst (u2 := uY) pSwapCtx)
        (fun _ => by simp only [encDepPair, encPair, uY, hY_eq, uA, uB])
      have pSweep := StageEval.seq pSwapIn
        (StageEval.const (S := S)
          (bmBidiagSweepCoreWith_computesInTime hmul t1 q hq ht1 b a
            hb_fits3 ha_fits3 ha_nn (by omega) Y_seq2 (fun _ => hY _)))
      have hout_eq :
          (List.finRange t1).map (bidiagSweepFixed t1 q b a Y_seq2 (fun v => v.val)) =
            (List.finRange t1).map (cyclicBidiagSolveFixed a b Y) := by
        unfold cyclicBidiagSolveFixed
        rw [if_neg hba]
      have pElse := StageEval.congr_out
        (v2 := fun _ : S => encList (encComplex W)
          ((List.finRange t1).map (cyclicBidiagSolveFixed a b Y)))
        pSweep (fun _ => by dsimp only [W]; rw [hout_eq])
      rcases pElse () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
      dsimp only [uCtx, uY, uA, uB, id] at ht
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord, hlen_Y] at ht
      dsimp only [W] at ht
      refine ⟨t, ?_, hc⟩
      dsimp only [B_branch, W]
      ring_nf at ht ⊢
      omega)
  rcases pIte () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hite_eq : (if decide (b ≤ a) = true then B_branch else B_branch) = B_branch := by
    split_ifs <;> rfl
  dsimp only [uIn, uCtx, uY, id] at ht hcomp
  rw [hite_eq] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encodeSignedWord,
    hlen_Y] at ht
  dsimp only [B_branch, W] at ht
  change (bmCyclicBidiagSolveWith bmMul).ComputesInTime _ _ t at hcomp
  refine ⟨t, ?_, hcomp⟩
  dsimp only [W]
  ring_nf at ht ⊢
  omega

/-- **Uniform Backward-Shift Cyclic Bidiagonal Solver (`bmCyclicBidiagPrevSolveWith bmMul`)**:
Consumes `((q, (a, b)), Y_list)` on `kIO` and emits
`encList (encComplex (10 * q)) ((List.finRange t1).map (cyclicBidiagPrevSolveFixed a b Y))`. -/
def bmCyclicBidiagPrevSolveWith (bmMul : BitMachine) : BitMachine :=
  bmSeq
    (bmPairMap (bmMapSnd (bmFanout bmSnd bmFst)) bmRotateOneList)
    (bmCyclicBidiagSolveWith bmMul)

theorem bmCyclicBidiagPrevSolveWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (t1 q : ℕ) [NeZero t1] (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (a b : ℤ) (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (ha_le : a ≤ 2 ^ (2 * q)) (hb_le : b ≤ 2 ^ (2 * q))
    (Y : Fin t1 → FixedComplex q)
    (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W := 10 * q
    ∃ t ≤ (t1 + 1) * (14 * mulTime W + 6000000 * q + 4500000) +
          12000000 * q * q,
      (bmCyclicBidiagPrevSolveWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W)))
            (encList (encComplex W))
            ((q, (a, b)), (List.finRange t1).map Y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W)
            ((List.finRange t1).map (cyclicBidiagPrevSolveFixed a b Y))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro W
  have ht1_pos : 0 < t1 := NeZero.pos t1
  let S := Unit
  let Y_list := (List.finRange t1).map Y
  let uA : S → List Bool := fun _ => encodeSignedWord W a
  let uB : S → List Bool := fun _ => encodeSignedWord W b
  have pSwapAB := StageEval.fanout (StageEval.snd uA uB) (StageEval.fst uA uB)
  have pSwapCtx := StageEval.mapSnd (u1 := fun _ : S => encUnary q) pSwapAB
  have pRotY := StageEval.const (S := S)
    (bmRotateOneList_computesInTime (encComplex W) (40 * q + 8)
      (fun x => by rw [length_encComplex W]; omega) Y_list (by simp [Y_list]; omega))
  have hrot_eq : rotateList 1 Y_list = (List.finRange t1).map (fun m : Fin t1 => Y (cyclicNext m)) :=
    rotateOne_map_finRange_eq_cyclicNext Y
  have pPrep := StageEval.congr_out
    (v2 := fun _ : S =>
      encPair (encPair encUnary (encPair (encodeSignedWord W) (encodeSignedWord W)))
        (encList (encComplex W))
        ((q, (b, a)), (List.finRange t1).map (fun m : Fin t1 => Y (cyclicNext m))))
    (StageEval.pairMap pSwapCtx pRotY)
    (fun _ => by simp only [encDepPair, encPair, uA, uB, hrot_eq])
  have pSolve := StageEval.seq pPrep
    (StageEval.const (S := S)
      (bmCyclicBidiagSolveWith_computesInTime hmul t1 q hq ht1 b a hb_nn ha_nn hb_le ha_le
        (fun m => Y (cyclicNext m)) (fun _ => hY _)))
  rcases pSolve () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_Y : (encList (encComplex W) Y_list).length = t1 * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8) Y_list
      (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [Y_list, List.length_map, List.length_finRange]
    ring
  have hlen_rot : (encList (encComplex W) (rotateList 1 Y_list)).length = t1 * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8) (rotateList 1 Y_list)
      (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [length_rotateList, Y_list, List.length_map, List.length_finRange]
    ring
  have hlen_Y_len : Y_list.length = t1 := by simp [Y_list]
  dsimp only [uA, uB, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord,
    hlen_Y, hlen_rot, hlen_Y_len] at ht
  dsimp only [W] at ht
  change (bmCyclicBidiagPrevSolveWith bmMul).ComputesInTime _ _ t at hcomp
  refine ⟨t, ?_, hcomp⟩
  dsimp only [W]
  ring_nf at ht ⊢
  omega

/-! ## 5. Single-Pass Open-Chain + Cyclic Rank-1 Correction Nyquist Solver (`bmNyquistColumnSolveWith`) -/

lemma ite_even_add_sub_eq_add_altSign {q : ℕ} (k : ℕ) (a b : FixedComplex q) :
    (if decide (k % 2 = 0) = true then a + b else a - b) =
      a + ⟨altSign k * b.re, altSign k * b.im⟩ := by
  rcases a with ⟨are, aim⟩
  rcases b with ⟨bre, bim⟩
  unfold altSign
  by_cases h : k % 2 = 0
  · simp only [h, decide_true, ↓reduceIte]
    change (⟨are + bre, aim + bim⟩ : FixedComplex q) = ⟨are + 1 * bre, aim + 1 * bim⟩
    ext <;> ring
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    change (⟨are - bre, aim - bim⟩ : FixedComplex q) = ⟨are + -1 * bre, aim + -1 * bim⟩
    ext <;> ring

lemma decide_add_one_mod_two_eq_not (k : ℕ) :
    decide ((k + 1) % 2 = 0) = !decide (k % 2 = 0) := by
  by_cases h : k % 2 = 0
  · have h1 : (k + 1) % 2 = 1 := by omega
    simp [h, h1]
  · have h1 : (k + 1) % 2 = 0 := by omega
    simp [h, h1]

lemma getElem_rotateList_one_finRange {α : Type} {t1 : ℕ} (f : Fin t1 → α)
    (s : ℕ) (hs : s + 1 < t1) (h_in : s < (rotateList 1 ((List.finRange t1).map f)).length) :
    (rotateList 1 ((List.finRange t1).map f))[s]'h_in = f ⟨s + 1, hs⟩ := by
  have ht1 : 1 ≤ t1 := by omega
  have hrot := rotateList_map_finRange 1 ht1 f
  have hlen : (rotateList 1 ((List.finRange t1).map f)).length = t1 := by
    simp [length_rotateList]
  have hs_t1 : s < t1 := by omega
  have h1 : (rotateList 1 ((List.finRange t1).map f))[s]'h_in =
      ((List.finRange t1).map (fun i : Fin t1 => f ⟨(i.val + 1) % t1, Nat.mod_lt _ ht1⟩))[s]'(by simp [hs_t1]) := by
    congr 1
  rw [h1, List.getElem_map, List.getElem_finRange]
  congr 1
  ext
  dsimp only [Fin.val_cast]
  exact Nat.mod_eq_of_lt hs

lemma wordWidthBounds_getElem_rotateList_one_finRange {t1 q w : ℕ}
    (f : Fin t1 → FixedComplex q) (hf : ∀ m : Fin t1, WordWidthBounds w (f m))
    (s : ℕ) (h_in : s < (rotateList 1 ((List.finRange t1).map f)).length) :
    WordWidthBounds w ((rotateList 1 ((List.finRange t1).map f))[s]'h_in) := by
  have hmem : (rotateList 1 ((List.finRange t1).map f))[s]'h_in ∈
      rotateList 1 ((List.finRange t1).map f) := List.getElem_mem h_in
  unfold rotateList at hmem
  rw [List.mem_append] at hmem
  have hmem2 : (rotateList 1 ((List.finRange t1).map f))[s]'h_in ∈ (List.finRange t1).map f := by
    rcases hmem with h1 | h2
    · exact List.mem_of_mem_drop h1
    · exact List.mem_of_mem_take h2
  rw [List.mem_map] at hmem2
  rcases hmem2 with ⟨m, _, hm_eq⟩
  rw [← hm_eq]
  exact hf m

/-- **Nyquist Entry Scaling (`bmNyquistScaleEntryWith bmMul`)**:
Consumes `(((q, qWork), invC0_m), y_m)` and computes
`FixedComplex.scaleRounded invC0_m (FixedComplex.rescale qWork y_m)`. -/
def bmNyquistScaleEntryWith (bmMul : BitMachine) : BitMachine :=
  let bmQ := bmSeq (bmSeq bmFst bmFst) bmFst
  let bmQW := bmSeq (bmSeq bmFst bmFst) bmSnd
  let bmInv := bmSeq bmFst bmSnd
  let bmW := bmSeq bmInv bmSignedWidth
  let bmY := bmSnd
  let bmResc := bmSeq (bmFanout (bmFanout bmW (bmFanout bmQ bmQW)) bmY) bmComplexRescale
  bmSeq (bmFanout (bmFanout bmW bmQW) (bmFanout bmInv bmResc)) (bmComplexScaleRoundedWith bmMul)

theorem bmNyquistScaleEntryWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W q qWork : ℕ) (invC0_m : ℤ) (y_m : FixedComplex q)
    (hinv : FitsSignedWord W invC0_m)
    (hy : WordWidthBounds W y_m)
    (hresc : WordWidthBounds W (FixedComplex.rescale qWork y_m))
    (hout : WordWidthBounds W (FixedComplex.scaleRounded invC0_m (FixedComplex.rescale qWork y_m)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 4 * mulTime W + 120000 * W + 60000 * qWork + 60000 * q + 250000,
      (bmNyquistScaleEntryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (encPair encUnary encUnary) (encodeSignedWord W)) (encComplex W)
            (((q, qWork), invC0_m), y_m)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encComplex W
            (FixedComplex.scaleRounded invC0_m (FixedComplex.rescale qWork y_m))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uQQ : S → List Bool := fun _ => encPair encUnary encUnary (q, qWork)
  let uCtx : S → List Bool := encDepPair uQQ (fun _ => encodeSignedWord W invC0_m)
  let uY : S → List Bool := fun _ => encComplex W y_m
  have pQQ := StageEval.seq (StageEval.fst uCtx uY)
    (StageEval.fst uQQ (fun _ : S => encodeSignedWord W invC0_m))
  have pQ := StageEval.seq pQQ
    (StageEval.fst (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pQW := StageEval.seq pQQ
    (StageEval.snd (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pInv := StageEval.seq (StageEval.fst uCtx uY)
    (StageEval.snd uQQ (fun _ : S => encodeSignedWord W invC0_m))
  have pW := StageEval.seq pInv
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => invC0_m))
  have pY := StageEval.snd uCtx uY
  have pResc := StageEval.seq (StageEval.fanout (StageEval.fanout pW (StageEval.fanout pQ pQW)) pY)
    (StageEval.const (S := S) (bmComplexRescale_computesInTime W W q qWork y_m hy hresc))
  have pScale := StageEval.seq (StageEval.fanout (StageEval.fanout pW pQW) (StageEval.fanout pInv pResc))
    (StageEval.const (S := S)
      (bmComplexScaleRoundedWith_computesInTime hmul W W qWork invC0_m
        (FixedComplex.rescale qWork y_m) hinv hresc hout))
  rcases pScale () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uCtx, uQQ, uY, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encodeSignedWord,
    length_encComplex] at ht
  exact ⟨t, by linarith only [ht], hcomp⟩

/-- Pure step function for the single-pass Nyquist open-chain + alternating-sum scan. -/
def nyquistScanStepFn {qWork : ℕ} (b_next : FixedComplex qWork)
    (st : Bool × (FixedComplex qWork × FixedComplex qWork)) :
    Bool × (FixedComplex qWork × FixedComplex qWork) :=
  (!st.1, (b_next - st.2.1, if st.1 then st.2.2 + st.2.1 else st.2.2 - st.2.1))

/-- **Single-Pass Nyquist Open-Chain + Alternating Sum Scan Step (`bmNyquistStep`)**:
Consumes `(b_next, (evenFlag, (zpart, altAcc)))` and emits
`(!evenFlag, (b_next - zpart, if evenFlag then altAcc + zpart else altAcc - zpart))`. -/
def bmNyquistStep : BitMachine :=
  let bmB := bmFst
  let bmFlag := bmSeq bmSnd bmFst
  let bmZp := bmSeq (bmSeq bmSnd bmSnd) bmFst
  let bmAlt := bmSeq (bmSeq bmSnd bmSnd) bmSnd
  let bmNextFlag := bmSeq bmFlag bmBoolNot
  let bmNextZp := bmSeq (bmFanout bmB bmZp) bmComplexSub
  let bmNextAlt := bmIte bmFlag
    (bmSeq (bmFanout bmAlt bmZp) bmComplexAdd)
    (bmSeq (bmFanout bmAlt bmZp) bmComplexSub)
  bmFanout bmNextFlag (bmFanout bmNextZp bmNextAlt)

theorem bmNyquistStep_computesInTime (W qWork : ℕ) (b_next : FixedComplex qWork)
    (st : Bool × (FixedComplex qWork × FixedComplex qWork))
    (hb : WordWidthBounds W b_next)
    (hzp : WordWidthBounds W st.2.1)
    (halt : WordWidthBounds W st.2.2)
    (hnext_zp : WordWidthBounds W (b_next - st.2.1))
    (hnext_alt_add : WordWidthBounds W (st.2.2 + st.2.1))
    (hnext_alt_sub : WordWidthBounds W (st.2.2 - st.2.1))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let encSt := encPair encBool (encPair (encComplex W (q := qWork)) (encComplex W (q := qWork)))
    ∃ t ≤ 120000 * W + 150000,
      bmNyquistStep.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encComplex W) encSt (b_next, st)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encSt (nyquistScanStepFn b_next st)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro encSt
  let S := Unit
  let uB : S → List Bool := fun _ => encComplex W b_next
  let uSt : S → List Bool := fun _ => encSt st
  have pB := StageEval.fst uB uSt
  have pSt := StageEval.snd uB uSt
  have pFlag := StageEval.seq pSt
    (StageEval.fst (fun _ : S => encBool st.1)
      (fun _ : S => encPair (encComplex W) (encComplex W) st.2))
  have pSt2 := StageEval.seq pSt
    (StageEval.snd (fun _ : S => encBool st.1)
      (fun _ : S => encPair (encComplex W) (encComplex W) st.2))
  have pZp := StageEval.seq pSt2
    (StageEval.fst (fun _ : S => encComplex W st.2.1) (fun _ : S => encComplex W st.2.2))
  have pAlt := StageEval.seq pSt2
    (StageEval.snd (fun _ : S => encComplex W st.2.1) (fun _ : S => encComplex W st.2.2))
  have pNextFlag := StageEval.seq pFlag
    (StageEval.of_computesStageLe bmBoolNot_computesStageLe (fun _ : S => st.1))
  have pNextZp := StageEval.seq (StageEval.fanout pB pZp)
    (StageEval.const (S := S)
      (bmComplexSub_computesInTime W b_next st.2.1 hb hzp hnext_zp))
  have pAddAlt := StageEval.seq (StageEval.fanout pAlt pZp)
    (StageEval.const (S := S)
      (bmComplexAdd_computesInTime W st.2.2 st.2.1 halt hzp hnext_alt_add))
  have pSubAlt := StageEval.seq (StageEval.fanout pAlt pZp)
    (StageEval.const (S := S)
      (bmComplexSub_computesInTime W st.2.2 st.2.1 halt hzp hnext_alt_sub))
  have pNextAltRaw := StageEval.ite_stage pFlag pAddAlt pSubAlt
  have pNextAlt := StageEval.congr_out
    (v2 := fun _ : S => encComplex W (if st.1 then st.2.2 + st.2.1 else st.2.2 - st.2.1))
    pNextAltRaw
    (fun _ => by cases st.1 <;> rfl)
  have pAll := StageEval.fanout pNextFlag (StageEval.fanout pNextZp pNextAlt)
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uB, uSt, encSt, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, encBool, List.length_singleton, length_encComplex] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- **Nyquist Row Reconstruction (`bmNyquistReconEntry`)**:
Consumes `(((q, qWork), corr), (evenFlag, (zpart, altAcc)))` and emits
`FixedComplex.rescale q (if evenFlag then zpart + corr else zpart - corr)`. -/
def bmNyquistReconEntry : BitMachine :=
  let bmQ := bmSeq (bmSeq bmFst bmFst) bmFst
  let bmQW := bmSeq (bmSeq bmFst bmFst) bmSnd
  let bmCorr := bmSeq bmFst bmSnd
  let bmW := bmSeq (bmSeq bmCorr bmFst) bmSignedWidth
  let bmFlag := bmSeq bmSnd bmFst
  let bmZp := bmSeq (bmSeq bmSnd bmSnd) bmFst
  let bmSum := bmIte bmFlag
    (bmSeq (bmFanout bmZp bmCorr) bmComplexAdd)
    (bmSeq (bmFanout bmZp bmCorr) bmComplexSub)
  bmSeq (bmFanout (bmFanout bmW (bmFanout bmQW bmQ)) bmSum) bmComplexRescale

theorem bmNyquistReconEntry_computesInTime (W q qWork : ℕ)
    (corr : FixedComplex qWork)
    (st : Bool × (FixedComplex qWork × FixedComplex qWork))
    (hcorr : WordWidthBounds W corr)
    (hzp : WordWidthBounds W st.2.1)
    (hadd : WordWidthBounds W (st.2.1 + corr))
    (hsub : WordWidthBounds W (st.2.1 - corr))
    (hout : WordWidthBounds W
      (FixedComplex.rescale q (if st.1 then st.2.1 + corr else st.2.1 - corr)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let encSt := encPair encBool (encPair (encComplex W (q := qWork)) (encComplex W (q := qWork)))
    ∃ t ≤ 160000 * W + 60000 * q + 60000 * qWork + 250000,
      bmNyquistReconEntry.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (encPair encUnary encUnary) (encComplex W)) encSt
            (((q, qWork), corr), st)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encComplex W
            (FixedComplex.rescale q (if st.1 then st.2.1 + corr else st.2.1 - corr))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro encSt
  let S := Unit
  let uQQ : S → List Bool := fun _ => encPair encUnary encUnary (q, qWork)
  let uCtx : S → List Bool := encDepPair uQQ (fun _ => encComplex W corr)
  let uSt : S → List Bool := fun _ => encSt st
  have pQQ := StageEval.seq (StageEval.fst uCtx uSt)
    (StageEval.fst uQQ (fun _ : S => encComplex W corr))
  have pQ := StageEval.seq pQQ
    (StageEval.fst (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pQW := StageEval.seq pQQ
    (StageEval.snd (fun _ : S => encUnary q) (fun _ : S => encUnary qWork))
  have pCorr := StageEval.seq (StageEval.fst uCtx uSt)
    (StageEval.snd uQQ (fun _ : S => encComplex W corr))
  have pW := StageEval.seq
    (StageEval.seq pCorr
      (StageEval.fst (fun _ : S => encodeSignedWord W corr.re)
        (fun _ : S => encodeSignedWord W corr.im)))
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => corr.re))
  have pSt := StageEval.snd uCtx uSt
  have pFlag := StageEval.seq pSt
    (StageEval.fst (fun _ : S => encBool st.1)
      (fun _ : S => encPair (encComplex W) (encComplex W) st.2))
  have pSt2 := StageEval.seq pSt
    (StageEval.snd (fun _ : S => encBool st.1)
      (fun _ : S => encPair (encComplex W) (encComplex W) st.2))
  have pZp := StageEval.seq pSt2
    (StageEval.fst (fun _ : S => encComplex W st.2.1) (fun _ : S => encComplex W st.2.2))
  have pAdd := StageEval.seq (StageEval.fanout pZp pCorr)
    (StageEval.const (S := S) (bmComplexAdd_computesInTime W st.2.1 corr hzp hcorr hadd))
  have pSub := StageEval.seq (StageEval.fanout pZp pCorr)
    (StageEval.const (S := S) (bmComplexSub_computesInTime W st.2.1 corr hzp hcorr hsub))
  have pSumRaw := StageEval.ite_stage pFlag pAdd pSub
  have pSum := StageEval.congr_out
    (v2 := fun _ : S => encComplex W (if st.1 then st.2.1 + corr else st.2.1 - corr))
    pSumRaw
    (fun _ => by cases st.1 <;> rfl)
  have pAll := StageEval.seq (StageEval.fanout (StageEval.fanout pW (StageEval.fanout pQW pQ)) pSum)
    (StageEval.const (S := S)
      (bmComplexRescale_computesInTime W W qWork q
        (if st.1 then st.2.1 + corr else st.2.1 - corr)
        (by cases st.1 <;> [exact hsub; exact hadd]) hout))
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uCtx, uQQ, uSt, encSt, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, encBool, List.length_singleton,
    length_encodeSignedWord, length_encComplex] at ht
  split_ifs at ht <;> exact ⟨t, by linarith only [ht], hcomp⟩

/-- **Nyquist Column Solver Preparation (`bmNyquistPrepWith bmMul`)**:
Consumes `((q, (a, altFixed)), Y_list)` on `kIO` and computes
`(((q, qWork), (t1, altWork)), (initSt, B_rot))`, where `qWork = q + 4`,
`altWork = FixedComplex.rescale qWork altFixed`, `initSt = (true, (0, 0))`, and
`B_rot = rotateList 1 ((List.finRange t1).map B_sc)`. -/
def bmNyquistPrepWith (bmMul : BitMachine) : BitMachine :=
  let bmQ := bmSeq bmFst bmFst
  let bmA := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmAlt := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmYList := bmSnd
  let bmQWork := bmSeq (bmFanout bmQ (bmUnaryConst 4)) bmUnaryAdd
  let bmW := bmSeq bmA bmSignedWidth
  let bmQQWork := bmSeq (bmFanout bmQ bmQWork) bmUnaryAdd
  let bmTwoPowQQW := bmSeq (bmFanout bmW bmQQWork) bmSignedTwoPow
  let bmInvC0 := bmSeq (bmFanout bmTwoPowQQW bmA) bmRoundDivInt
  let bmBList := bmSeq
    (bmFanout (bmFanout (bmFanout bmQ bmQWork) bmInvC0) bmYList)
    (bmMapWithCtx (bmNyquistScaleEntryWith bmMul))
  let bmBRot := bmSeq bmBList bmRotateOneList
  let bmZeroC := bmSeq bmW bmComplexZero
  let bmInitSt := bmFanout (bmConstBool true) (bmFanout bmZeroC bmZeroC)
  let bmT1 := bmSeq bmYList bmListLengthUnary
  let bmAltWork := bmSeq (bmFanout (bmFanout bmW (bmFanout bmQ bmQWork)) bmAlt) bmComplexRescale
  bmFanout
    (bmFanout (bmFanout bmQ bmQWork) (bmFanout bmT1 bmAltWork))
    (bmFanout bmBRot bmInitSt)

/-- **Nyquist Column Solver Finish (`bmNyquistFinish`)**:
Consumes `(((q, qWork), (t1, altWork)), (B_rot, initSt))` on `kIO`, runs
`bmScanlList bmNyquistStep` on `(B_rot, initSt)`, computes `corr := divNatFixed (altWork - altPart) t1`,
and maps `bmNyquistReconEntry` across `traj_list`. -/
def bmNyquistFinish : BitMachine :=
  let bmScan := bmMapSnd (bmScanlList bmNyquistStep)
  let bmQQ := bmSeq bmFst bmFst
  let bmT1 := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmAltWork := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmW := bmSeq (bmSeq bmAltWork bmFst) bmSignedWidth
  let bmTrajList := bmSeq bmSnd bmFst
  let bmLastSt := bmSeq bmSnd bmSnd
  let bmAltPart := bmSeq (bmSeq bmLastSt bmSnd) bmSnd
  let bmDiff := bmSeq (bmFanout bmAltWork bmAltPart) bmComplexSub
  let bmCorr := bmSeq (bmFanout (bmFanout bmW bmT1) bmDiff) bmDivNatFixed
  let bmReconCtx := bmFanout bmQQ bmCorr
  bmSeq bmScan
    (bmSeq (bmFanout bmReconCtx bmTrajList)
      (bmMapWithCtx bmNyquistReconEntry))

/-- **Uniform Single-Pass Nyquist Column Solver (`bmNyquistColumnSolveWith bmMul`)**:
Consumes `((q, (a, altFixed)), Y_list)` on `kIO` and emits
`encList (encComplex (10 * q)) ((List.finRange t1).map (nyquistColumnSolveFixed a Y altFixed))`
in $O(t_1 \cdot (\text{mulTime}(10 q) + q) + q^2)$ `TM2.step` transitions. -/
def bmNyquistColumnSolveWith (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmNyquistPrepWith bmMul) bmNyquistFinish

/-- Pure-integer trajectory state helper for `bmNyquistColumnSolveWith`'s `bmScanlList` pass. -/
def nyqStFnAux {qWork : ℕ} (initSt : Bool × (FixedComplex qWork × FixedComplex qWork))
    (B_rot : List (FixedComplex qWork)) :
    ℕ → Bool × (FixedComplex qWork × FixedComplex qWork)
  | 0 => initSt
  | i + 1 =>
    if h : i < B_rot.length then
      nyquistScanStepFn (B_rot[i]'h) (nyqStFnAux initSt B_rot i)
    else
      nyqStFnAux initSt B_rot i

theorem wordWidthBounds_nyquistColumnSolveFixed {t1 q : ℕ}
    (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (a : ℤ) (_ha_nn : 0 ≤ a) (_ha_le : a ≤ 2 ^ (2 * q))
    (Y : Fin t1 → FixedComplex q) (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (altFixed : FixedComplex q) (halt : WordWidthBounds (3 * q) altFixed)
    (u1 : Fin t1) :
    WordWidthBounds (10 * q) (nyquistColumnSolveFixed a Y altFixed u1) := by
  unfold nyquistColumnSolveFixed
  rw [memoizeFin_eq]
  set qWork : ℕ := q + 4
  set invC0_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a
  have hpow_fits : FitsSignedWord (2 * q + 5) ((2 : ℤ) ^ (q + qWork)) :=
    (FitsSignedWord.two_pow (q + qWork)).mono (by omega)
  have hinv_fits : FitsSignedWord (2 * q + 5) invC0_m :=
    FitsSignedWord.roundDivInt a hpow_fits
  have hrs_bds : ∀ m : Fin t1, WordWidthBounds (2 * q + qWork) (FixedComplex.rescale qWork (Y m)) := by
    intro m
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 4 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY m).1.mul_two_pow 4).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY m).2.mul_two_pow 4).mono (by omega)
  set B_sc : Fin t1 → FixedComplex qWork :=
    memoizeFin (fun m => FixedComplex.scaleRounded invC0_m (FixedComplex.rescale qWork (Y m)))
  have hB_bds : ∀ m : Fin t1, WordWidthBounds (7 * q) (B_sc m) := by
    intro m
    dsimp only [B_sc]
    rw [memoizeFin_eq]
    exact ⟨((hinv_fits.mul (hrs_bds m).1).roundShiftInt qWork).mono (by omega),
           ((hinv_fits.mul (hrs_bds m).2).roundShiftInt qWork).mono (by omega)⟩
  set zArr := (buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_sc) t1).1
  have hzpart_bds : ∀ m : Fin t1, WordWidthBounds (8 * q + 1) (zArr.getD m.val 0) := by
    intro m
    dsimp only [zArr]
    rw [getD_default_buildRecurrenceArray _ _ _ (le_of_lt m.isLt)]
    have habs := abs_buildRecurrenceArray_nyquistOpenChainStep_le B_sc hB_bds m.val
    have hm_pow : (m.val : ℤ) * (2 : ℤ) ^ (7 * q) < (2 : ℤ) ^ (8 * q + 1) := by
      have hm_le : (m.val : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast (le_of_lt m.isLt).trans ht1
      calc (m.val : ℤ) * (2 : ℤ) ^ (7 * q)
          ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ (7 * q) := mul_le_mul_of_nonneg_right hm_le (by positivity)
        _ = (2 : ℤ) ^ (8 * q) := by rw [← pow_add, show q + 7 * q = 8 * q by ring]
        _ < (2 : ℤ) ^ (8 * q + 1) := pow_lt_pow_right₀ (by decide) (by omega)
    exact ⟨(fitsSignedWord_iff_abs_lt _ _).mpr (lt_of_le_of_lt habs.1 hm_pow),
           (fitsSignedWord_iff_abs_lt _ _).mpr (lt_of_le_of_lt habs.2 hm_pow)⟩
  have halt_re_bds :
      FitsSignedWord (9 * q + 1) (∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).re) := by
    have h := fitsSignedWord_sum_fin ht1 (fun m : Fin t1 => altSign m.val * (zArr.getD m.val 0).re)
      (fun m => by
        rcases altSign_eq_one_or_neg_one m.val with h1 | h1
        · rw [h1, one_mul]; exact (hzpart_bds m).1
        · rw [h1, neg_one_mul]; exact (hzpart_bds m).1.neg)
    exact h.mono (by omega)
  have halt_im_bds :
      FitsSignedWord (9 * q + 1) (∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).im) := by
    have h := fitsSignedWord_sum_fin ht1 (fun m : Fin t1 => altSign m.val * (zArr.getD m.val 0).im)
      (fun m => by
        rcases altSign_eq_one_or_neg_one m.val with h1 | h1
        · rw [h1, one_mul]; exact (hzpart_bds m).2
        · rw [h1, neg_one_mul]; exact (hzpart_bds m).2.neg)
    exact h.mono (by omega)
  have haltWork_bds : WordWidthBounds (4 * q) (FixedComplex.rescale qWork altFixed) := by
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 4 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact (halt.1.mul_two_pow 4).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact (halt.2.mul_two_pow 4).mono (by omega)
  set altPart : FixedComplex qWork :=
    ⟨∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).re,
     ∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).im⟩
  set diff : FixedComplex qWork := FixedComplex.rescale qWork altFixed - altPart
  have hdiff_bds : WordWidthBounds (9 * q + 2) diff :=
    ⟨FitsSignedWord.sub (haltWork_bds.1.mono (by omega)) halt_re_bds,
     FitsSignedWord.sub (haltWork_bds.2.mono (by omega)) halt_im_bds⟩
  set corr : FixedComplex qWork := divNatFixed diff t1
  have hcorr_bds : WordWidthBounds (9 * q + 2) corr :=
    ⟨FitsSignedWord.roundDivInt _ hdiff_bds.1,
     FitsSignedWord.roundDivInt _ hdiff_bds.2⟩
  have hcorr_signed :
      WordWidthBounds (9 * q + 2) (⟨altSign u1.val * corr.re, altSign u1.val * corr.im⟩ : FixedComplex qWork) := by
    rcases altSign_eq_one_or_neg_one u1.val with h1 | h1
    · rw [h1]; simpa using hcorr_bds
    · rw [h1, neg_one_mul, neg_one_mul]
      exact ⟨hcorr_bds.1.neg, hcorr_bds.2.neg⟩
  have hsum_bds :
      WordWidthBounds (9 * q + 3)
        (zArr.getD u1.val 0 + ⟨altSign u1.val * corr.re, altSign u1.val * corr.im⟩) :=
    ⟨FitsSignedWord.add ((hzpart_bds u1).1.mono (by omega)) hcorr_signed.1,
     FitsSignedWord.add ((hzpart_bds u1).2.mono (by omega)) hcorr_signed.2⟩
  have hsub1 : q - qWork = 0 := by omega
  have hsub2 : qWork - q = 4 := by omega
  refine ⟨?_, ?_⟩
  · simp only [FixedComplex.rescale, hsub1, hsub2, pow_zero, mul_one]
    exact (hsum_bds.1.roundShiftInt 4).mono (by omega)
  · simp only [FixedComplex.rescale, hsub1, hsub2, pow_zero, mul_one]
    exact (hsum_bds.2.roundShiftInt 4).mono (by omega)

set_option maxHeartbeats 800000 in
theorem bmNyquistColumnSolveWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (t1 q : ℕ) (hq : 14 ≤ q) (ht1_pos : 0 < t1) (ht1 : t1 ≤ 2 ^ q)
    (a : ℤ) (ha_nn : 0 ≤ a) (ha_le : a ≤ 2 ^ (2 * q))
    (altFixed : FixedComplex q) (halt : WordWidthBounds (3 * q) altFixed)
    (Y : Fin t1 → FixedComplex q)
    (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W := 10 * q
    ∃ t ≤ (t1 + 1) * (4 * mulTime W + 5500000 * q + 3500000) +
          12000000 * q * q,
      (bmNyquistColumnSolveWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair (encodeSignedWord W) (encComplex W)))
            (encList (encComplex W))
            ((q, (a, altFixed)), (List.finRange t1).map Y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W)
            ((List.finRange t1).map (nyquistColumnSolveFixed a Y altFixed))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro W
  set qWork : ℕ := q + 4
  let invC0_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a
  let B_sc : Fin t1 → FixedComplex qWork :=
    fun m => FixedComplex.scaleRounded invC0_m (FixedComplex.rescale qWork (Y m))
  let B_list := (List.finRange t1).map B_sc
  let B_rot := rotateList 1 B_list
  let initSt : Bool × (FixedComplex qWork × FixedComplex qWork) :=
    (true, ((0 : FixedComplex qWork), (0 : FixedComplex qWork)))
  let altWork : FixedComplex qWork := FixedComplex.rescale qWork altFixed
  let encSt := encPair encBool (encPair (encComplex W (q := qWork)) (encComplex W (q := qWork)))
  have ha_fits : FitsSignedWord W a := by
    rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg ha_nn]
    exact lt_of_le_of_lt ha_le (pow_lt_pow_right₀ (by decide) (by omega))
  have h2pow_fits : FitsSignedWord (2 * q + 5) ((2 : ℤ) ^ (q + qWork)) :=
    (FitsSignedWord.two_pow (q + qWork)).mono (by omega)
  have hinv_fits5 : FitsSignedWord (2 * q + 5) invC0_m :=
    FitsSignedWord.roundDivInt a h2pow_fits
  have hinv_fits : FitsSignedWord W invC0_m := hinv_fits5.mono (by omega)
  have hrs_bds : ∀ m : Fin t1, WordWidthBounds (2 * q + qWork) (FixedComplex.rescale qWork (Y m)) := by
    intro m
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 4 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY m).1.mul_two_pow 4).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY m).2.mul_two_pow 4).mono (by omega)
  have hB_bds7 : ∀ m : Fin t1, WordWidthBounds (7 * q) (B_sc m) := by
    intro m
    exact ⟨((hinv_fits5.mul (hrs_bds m).1).roundShiftInt qWork).mono (by omega),
           ((hinv_fits5.mul (hrs_bds m).2).roundShiftInt qWork).mono (by omega)⟩
  have haltWork_bds : WordWidthBounds (4 * q) altWork := by
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 4 := by omega
    refine ⟨?_, ?_⟩
    · simp only [altWork, FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact (halt.1.mul_two_pow 4).mono (by omega)
    · simp only [altWork, FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact (halt.2.mul_two_pow 4).mono (by omega)
  let S := Unit
  let Y_list := (List.finRange t1).map Y
  let uCtxIn : S → List Bool := fun _ =>
    encPair encUnary (encPair (encodeSignedWord W) (encComplex W)) (q, (a, altFixed))
  let uYIn : S → List Bool := fun _ => encList (encComplex W) Y_list
  let uIn : S → List Bool := encDepPair uCtxIn uYIn
  have pQIn := StageEval.seq (StageEval.fst uCtxIn uYIn)
    (StageEval.fst (fun _ : S => encUnary q)
      (fun _ : S => encPair (encodeSignedWord W) (encComplex W) (a, altFixed)))
  have pAAlt := StageEval.seq (StageEval.fst uCtxIn uYIn)
    (StageEval.snd (fun _ : S => encUnary q)
      (fun _ : S => encPair (encodeSignedWord W) (encComplex W) (a, altFixed)))
  have pA := StageEval.seq pAAlt
    (StageEval.fst (fun _ : S => encodeSignedWord W a) (fun _ : S => encComplex W altFixed))
  have pAltIn := StageEval.seq pAAlt
    (StageEval.snd (fun _ : S => encodeSignedWord W a) (fun _ : S => encComplex W altFixed))
  have pYList := StageEval.snd uCtxIn uYIn
  have p4 := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 4 id) uIn
  have pQWork := StageEval.seq (StageEval.fanout pQIn p4)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (q, 4)))
  have pW := StageEval.seq pA
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => a))
  have pQQWork := StageEval.seq (StageEval.fanout pQIn pQWork)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (q, qWork)))
  have pTwoPowQQW := StageEval.seq (StageEval.fanout pW pQQWork)
    (StageEval.const (S := S)
      (bmSignedTwoPow_computesInTime W (q + qWork) (by omega) (by omega)))
  have pInvC0 := StageEval.seq (StageEval.fanout pTwoPowQQW pA)
    (StageEval.const (S := S)
      (bmRoundDivInt_computesInTime W ((2 : ℤ) ^ (q + qWork)) a
        (h2pow_fits.mono (by omega)) ha_fits))
  let encScaleCtx := encPair (encPair encUnary encUnary) (encodeSignedWord W)
  let scaleCtxVal := ((q, qWork), invC0_m)
  let SubM := { p : S × Fin t1 // p.2 ∈ List.finRange t1 }
  have hScaleStep : StageEval (S := SubM) (bmNyquistScaleEntryWith bmMul)
      (encDepPair
        (fun _ => encScaleCtx scaleCtxVal)
        (fun p => encComplex W (Y p.val.2)))
      (fun p => encComplex W (B_sc p.val.2))
      (fun _ => 4 * mulTime W + 120000 * W + 60000 * qWork + 60000 * q + 250000) := by
    intro p u2 u3 u4 u5 uS
    exact bmNyquistScaleEntryWith_computesInTime hmul W q qWork invC0_m (Y p.val.2)
      hinv_fits ((hY p.val.2).mono (by omega))
      ((hrs_bds p.val.2).mono (by omega)) ((hB_bds7 p.val.2).mono (by omega)) u2 u3 u4 u5 uS
  have pBList := StageEval.congr_in
    (u2 := encDepPair
      (fun _ : S => encScaleCtx scaleCtxVal)
      (fun _ : S => encList (encComplex W) Y_list))
    (StageEval.mapWithCtx_uniform (S := S)
      (ctx := fun _ => encScaleCtx scaleCtxVal)
      (xs := fun _ => List.finRange t1)
      (encA := fun _ m => encComplex W (Y m))
      (encB := fun _ => encComplex W)
      (fn := fun _ m => B_sc m)
      (B := fun _ => 4 * mulTime W + 120000 * W + 60000 * qWork + 60000 * q + 250000)
      (L_A := fun _ => 40 * q + 8)
      (L_B := fun _ => 40 * q + 8)
      hScaleStep
      (fun _ _ _ => by rw [length_encComplex W]; omega)
      (fun _ _ _ => by rw [length_encComplex W]; omega))
    (fun _ => by simp only [encDepPair, Y_list, encList, List.map_map, Function.comp_def])
  have pBListSeq := StageEval.seq
    (StageEval.fanout (StageEval.fanout (StageEval.fanout pQIn pQWork) pInvC0) pYList) pBList
  have pBRot := StageEval.seq pBListSeq
    (StageEval.const (S := S)
      (bmRotateOneList_computesInTime (encComplex W) (40 * q + 8)
        (fun x => by rw [length_encComplex W]; omega) B_list (by simp [B_list]; omega)))
  have pZeroC := StageEval.seq pW
    (StageEval.const (S := S) (bmComplexZero_computesInTime W qWork))
  have pTrue := StageEval.of_computesStageLe
    (bmConstBool_computesStageLe true id) uIn
  have pInitSt := StageEval.fanout pTrue (StageEval.fanout pZeroC pZeroC)
  have pT1Raw := StageEval.seq pYList
    (StageEval.const (S := S)
      (bmListLengthUnary_computesInTime (encComplex W) (40 * q + 8)
        (fun x => by rw [length_encComplex W]; omega) Y_list))
  have pT1 := StageEval.congr_out (v2 := fun _ : S => encUnary t1) pT1Raw
    (fun _ => by simp [Y_list])
  have pAltWork := StageEval.seq
    (StageEval.fanout (StageEval.fanout pW (StageEval.fanout pQIn pQWork)) pAltIn)
    (StageEval.const (S := S)
      (bmComplexRescale_computesInTime W W q qWork altFixed
        (halt.mono (by omega)) (haltWork_bds.mono (by omega))))
  let uTopCtx : S → List Bool := fun _ =>
    encPair (encPair encUnary encUnary) (encPair encUnary (encComplex W))
      ((q, qWork), (t1, altWork))
  have pPrep := StageEval.congr_out
    (v2 := encDepPair uTopCtx
      (encDepPair (fun _ : S => encList (encComplex W) B_rot) (fun _ : S => encSt initSt)))
    (StageEval.fanout
      (StageEval.fanout (StageEval.fanout pQIn pQWork) (StageEval.fanout pT1 pAltWork))
      (StageEval.fanout pBRot pInitSt))
    (fun _ => rfl)
  let nyqStFn : ℕ → Bool × (FixedComplex qWork × FixedComplex qWork) :=
    nyqStFnAux initSt B_rot
  have hlen_Brot : B_rot.length = t1 := by simp [B_rot, B_list, length_rotateList]
  have hst_flag : ∀ s ≤ t1, (nyqStFn s).1 = decide (s % 2 = 0) := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih =>
      have hs_lt : s < B_rot.length := by rw [hlen_Brot]; omega
      dsimp only [nyqStFn, nyqStFnAux]
      rw [dif_pos hs_lt]
      dsimp only [nyquistScanStepFn]
      rw [ih (by omega), decide_add_one_mod_two_eq_not]
  have hst_zp : ∀ s < t1,
      (nyqStFn s).2.1 =
        (buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_sc) s).2 := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih =>
      have hs_lt : s < B_rot.length := by rw [hlen_Brot]; omega
      have hs1 : s + 1 < t1 := hs
      have hB_eq : B_rot[s]'hs_lt = B_sc ⟨s + 1, hs1⟩ :=
        getElem_rotateList_one_finRange B_sc s hs1 hs_lt
      dsimp only [nyqStFn, nyqStFnAux]
      rw [dif_pos hs_lt]
      dsimp only [nyquistScanStepFn]
      rw [hB_eq, ih (by omega)]
      simp only [buildRecurrenceArray, nyquistOpenChainStep, dif_pos hs1]
  set zArr := (buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_sc) t1).1
  have hst_zp_getD : ∀ s < t1, (nyqStFn s).2.1 = zArr.getD s 0 := by
    intro s hs
    dsimp only [zArr]
    rw [getD_buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_sc) (le_of_lt hs)]
    exact hst_zp s hs
  have hzArr_bds : ∀ s < t1, WordWidthBounds (8 * q + 1) (zArr.getD s 0) := by
    intro s hs
    dsimp only [zArr]
    rw [getD_default_buildRecurrenceArray _ _ _ (le_of_lt hs)]
    have habs := abs_buildRecurrenceArray_nyquistOpenChainStep_le B_sc hB_bds7 s
    have hs_pow : (s : ℤ) * (2 : ℤ) ^ (7 * q) < (2 : ℤ) ^ (8 * q + 1) := by
      have hs_le : (s : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast (le_of_lt hs).trans ht1
      calc (s : ℤ) * (2 : ℤ) ^ (7 * q)
          ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ (7 * q) := mul_le_mul_of_nonneg_right hs_le (by positivity)
        _ = (2 : ℤ) ^ (8 * q) := by rw [← pow_add, show q + 7 * q = 8 * q by ring]
        _ < (2 : ℤ) ^ (8 * q + 1) := pow_lt_pow_right₀ (by decide) (by omega)
    exact ⟨(fitsSignedWord_iff_abs_lt _ _).mpr (lt_of_le_of_lt habs.1 hs_pow),
           (fitsSignedWord_iff_abs_lt _ _).mpr (lt_of_le_of_lt habs.2 hs_pow)⟩
  have hst_alt : ∀ s ≤ t1,
      (nyqStFn s).2.2 =
        ⟨∑ m ∈ Finset.range s, altSign m * (zArr.getD m 0).re,
         ∑ m ∈ Finset.range s, altSign m * (zArr.getD m 0).im⟩ := by
    intro s hs
    induction s with
    | zero =>
      ext <;> rfl
    | succ s ih =>
      have hs_t1 : s < t1 := by omega
      have hs_lt : s < B_rot.length := by rw [hlen_Brot]; exact hs_t1
      dsimp only [nyqStFn, nyqStFnAux]
      rw [dif_pos hs_lt]
      dsimp only [nyquistScanStepFn]
      rw [hst_flag s (by omega), hst_zp_getD s hs_t1, ite_even_add_sub_eq_add_altSign,
        ih (by omega)]
      simp only [Finset.sum_range_succ]
      rfl
  have hst_zp_bds : ∀ s ≤ t1, WordWidthBounds (8 * q + 2) (nyqStFn s).2.1 := by
    intro s hs
    by_cases hs_lt : s < t1
    · rw [hst_zp_getD s hs_lt]
      exact (hzArr_bds s hs_lt).mono (by omega)
    · have hs_eq : s = (t1 - 1) + 1 := by omega
      rw [hs_eq]
      have hpred_lt : t1 - 1 < B_rot.length := by rw [hlen_Brot]; omega
      dsimp only [nyqStFn, nyqStFnAux]
      rw [dif_pos hpred_lt]
      dsimp only [nyquistScanStepFn]
      have hB_pred : WordWidthBounds (7 * q) (B_rot[t1 - 1]'hpred_lt) :=
        wordWidthBounds_getElem_rotateList_one_finRange B_sc hB_bds7 (t1 - 1) hpred_lt
      have hzp_pred : WordWidthBounds (8 * q + 1) (nyqStFn (t1 - 1)).2.1 := by
        rw [hst_zp_getD (t1 - 1) (by omega)]
        exact hzArr_bds (t1 - 1) (by omega)
      exact ⟨FitsSignedWord.sub (hB_pred.1.mono (by omega)) hzp_pred.1,
             FitsSignedWord.sub (hB_pred.2.mono (by omega)) hzp_pred.2⟩
  have hst_alt_bds : ∀ s ≤ t1, WordWidthBounds (9 * q + 1) (nyqStFn s).2.2 := by
    intro s hs
    rw [hst_alt s hs]
    have hterm_re : ∀ m ∈ Finset.range s, |altSign m * (zArr.getD m 0).re| < (2 : ℤ) ^ (8 * q + 1) := by
      intro m hm
      have hm_lt : m < t1 := lt_of_lt_of_le (Finset.mem_range.mp hm) hs
      rw [← fitsSignedWord_iff_abs_lt]
      rcases altSign_eq_one_or_neg_one m with h1 | h1
      · rw [h1, one_mul]; exact (hzArr_bds m hm_lt).1
      · rw [h1, neg_one_mul]; exact (hzArr_bds m hm_lt).1.neg
    have hterm_im : ∀ m ∈ Finset.range s, |altSign m * (zArr.getD m 0).im| < (2 : ℤ) ^ (8 * q + 1) := by
      intro m hm
      have hm_lt : m < t1 := lt_of_lt_of_le (Finset.mem_range.mp hm) hs
      rw [← fitsSignedWord_iff_abs_lt]
      rcases altSign_eq_one_or_neg_one m with h1 | h1
      · rw [h1, one_mul]; exact (hzArr_bds m hm_lt).2
      · rw [h1, neg_one_mul]; exact (hzArr_bds m hm_lt).2.neg
    have hs_pow : (s : ℤ) * (2 : ℤ) ^ (8 * q + 1) ≤ (2 : ℤ) ^ (9 * q + 1) := by
      have hs_le : (s : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast hs.trans ht1
      calc (s : ℤ) * (2 : ℤ) ^ (8 * q + 1)
          ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ (8 * q + 1) := mul_le_mul_of_nonneg_right hs_le (by positivity)
        _ = (2 : ℤ) ^ (9 * q + 1) := by rw [← pow_add, show q + (8 * q + 1) = 9 * q + 1 by ring]
    refine ⟨(fitsSignedWord_iff_abs_lt _ _).mpr ?_, (fitsSignedWord_iff_abs_lt _ _).mpr ?_⟩
    · dsimp only
      by_cases hs0 : s = 0
      · subst hs0; simp
      · have hsum_lt :
            ∑ m ∈ Finset.range s, |altSign m * (zArr.getD m 0).re| <
              ∑ _m ∈ Finset.range s, (2 : ℤ) ^ (8 * q + 1) :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hs0) hterm_re
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_lt
        exact lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) (lt_of_lt_of_le hsum_lt hs_pow)
    · dsimp only
      by_cases hs0 : s = 0
      · subst hs0; simp
      · have hsum_lt :
            ∑ m ∈ Finset.range s, |altSign m * (zArr.getD m 0).im| <
              ∑ _m ∈ Finset.range s, (2 : ℤ) ^ (8 * q + 1) :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hs0) hterm_im
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_lt
        exact lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) (lt_of_lt_of_le hsum_lt hs_pow)
  let SubScan := { p : S × ℕ // p.2 < B_rot.length }
  have hScanStep : StageEval (S := SubScan) bmNyquistStep
      (encDepPair (fun p => encComplex W (B_rot[p.val.2]'p.property))
        (fun p => encSt (nyqStFn p.val.2)))
      (fun p => encSt (nyqStFn (p.val.2 + 1)))
      (fun _ => 120000 * W + 150000) := by
    intro p u2 u3 u4 u5 uS
    have hi_lt : p.val.2 < B_rot.length := p.property
    have hi_t1 : p.val.2 < t1 := by simpa [hlen_Brot] using hi_lt
    have hB_i : WordWidthBounds (7 * q) (B_rot[p.val.2]'hi_lt) :=
      wordWidthBounds_getElem_rotateList_one_finRange B_sc hB_bds7 p.val.2 hi_lt
    have hzp_i := hst_zp_bds p.val.2 (by omega)
    have halt_i := hst_alt_bds p.val.2 (by omega)
    have hnext_zp : WordWidthBounds (8 * q + 3) ((B_rot[p.val.2]'hi_lt) - (nyqStFn p.val.2).2.1) :=
      ⟨FitsSignedWord.sub (hB_i.1.mono (by omega)) hzp_i.1,
       FitsSignedWord.sub (hB_i.2.mono (by omega)) hzp_i.2⟩
    have hnext_alt_add : WordWidthBounds (9 * q + 2) ((nyqStFn p.val.2).2.2 + (nyqStFn p.val.2).2.1) :=
      ⟨FitsSignedWord.add halt_i.1 (hzp_i.1.mono (by omega)),
       FitsSignedWord.add halt_i.2 (hzp_i.2.mono (by omega))⟩
    have hnext_alt_sub : WordWidthBounds (9 * q + 2) ((nyqStFn p.val.2).2.2 - (nyqStFn p.val.2).2.1) :=
      ⟨FitsSignedWord.sub halt_i.1 (hzp_i.1.mono (by omega)),
       FitsSignedWord.sub halt_i.2 (hzp_i.2.mono (by omega))⟩
    have hstep_eq : nyqStFn (p.val.2 + 1) =
        nyquistScanStepFn (B_rot[p.val.2]'hi_lt) (nyqStFn p.val.2) := by
      dsimp only [nyqStFn, nyqStFnAux]
      rw [dif_pos hi_lt]
    rcases bmNyquistStep_computesInTime W qWork (B_rot[p.val.2]'hi_lt) (nyqStFn p.val.2)
      (hB_i.mono (by omega)) (hzp_i.mono (by omega)) (halt_i.mono (by omega))
      (hnext_zp.mono (by omega)) (hnext_alt_add.mono (by omega)) (hnext_alt_sub.mono (by omega))
      u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, id] at ht hc ⊢
    rw [← hstep_eq] at hc
    exact ⟨t, ht, hc⟩
  have pScan := StageEval.scanlList_idx (S := S)
    (encElem := fun _ => encComplex W)
    (encAcc := fun _ => encSt)
    (xs := fun _ => B_rot)
    (st := fun _ => nyqStFn)
    (B := fun _ => 120000 * W + 150000)
    (L_elem := fun _ => 40 * q + 8)
    (L_acc := fun _ => 320 * q + 78)
    hScanStep
    (fun _ _ _ => by dsimp only [W]; rw [length_encComplex]; omega)
    (fun _ _ _ => by
      dsimp only [encSt, W]
      simp only [length_encPair, encBool, List.length_singleton, length_encComplex]
      omega)
  let traj_list := (List.finRange t1).map (fun u1 => nyqStFn u1.val)
  let lastSt := nyqStFn t1
  have htraj_eq :
      (List.range B_rot.length).map nyqStFn = traj_list := by
    rw [hlen_Brot, ← map_finRange_eq_map_range t1 nyqStFn]
  have pScanStage := StageEval.congr_out
    (v2 := encDepPair uTopCtx (fun _ => encPair (encList encSt) encSt (traj_list, lastSt)))
    (StageEval.mapSnd (u1 := uTopCtx) pScan)
    (fun _ => by
      dsimp only [encDepPair, traj_list, lastSt]
      rw [htraj_eq, hlen_Brot])
  let uTL : S → List Bool := fun _ => encPair (encList encSt) encSt (traj_list, lastSt)
  have pTopCtx := StageEval.fst uTopCtx uTL
  have pTL := StageEval.snd uTopCtx uTL
  have pQQ := StageEval.seq pTopCtx
    (StageEval.fst (fun _ : S => encPair encUnary encUnary (q, qWork))
      (fun _ : S => encPair encUnary (encComplex W) (t1, altWork)))
  have pT1AltW := StageEval.seq pTopCtx
    (StageEval.snd (fun _ : S => encPair encUnary encUnary (q, qWork))
      (fun _ : S => encPair encUnary (encComplex W) (t1, altWork)))
  have pT1Mid := StageEval.seq pT1AltW
    (StageEval.fst (fun _ : S => encUnary t1) (fun _ : S => encComplex W altWork))
  have pAltWMid := StageEval.seq pT1AltW
    (StageEval.snd (fun _ : S => encUnary t1) (fun _ : S => encComplex W altWork))
  have pWMid := StageEval.seq
    (StageEval.seq pAltWMid
      (StageEval.fst (fun _ : S => encodeSignedWord W altWork.re)
        (fun _ : S => encodeSignedWord W altWork.im)))
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => altWork.re))
  have pTrajList := StageEval.seq pTL
    (StageEval.fst (fun _ : S => encList encSt traj_list) (fun _ : S => encSt lastSt))
  have pLastSt := StageEval.seq pTL
    (StageEval.snd (fun _ : S => encList encSt traj_list) (fun _ : S => encSt lastSt))
  have pLastSt2 := StageEval.seq pLastSt
    (StageEval.snd (fun _ : S => encBool lastSt.1)
      (fun _ : S => encPair (encComplex W) (encComplex W) lastSt.2))
  have pAltPart := StageEval.seq pLastSt2
    (StageEval.snd (fun _ : S => encComplex W lastSt.2.1) (fun _ : S => encComplex W lastSt.2.2))
  let altPart := lastSt.2.2
  have haltPart_eq :
      altPart =
        ⟨∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).re,
         ∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).im⟩ := by
    dsimp only [altPart, lastSt]
    rw [hst_alt t1 (le_refl t1)]
    ext <;> exact (Fin.sum_univ_eq_sum_range _ t1).symm
  have haltPart_bds : WordWidthBounds (9 * q + 1) altPart := hst_alt_bds t1 (le_refl t1)
  let diff := altWork - altPart
  have hdiff_bds : WordWidthBounds (9 * q + 2) diff :=
    ⟨FitsSignedWord.sub (haltWork_bds.1.mono (by omega)) haltPart_bds.1,
     FitsSignedWord.sub (haltWork_bds.2.mono (by omega)) haltPart_bds.2⟩
  have pDiff := StageEval.seq (StageEval.fanout pAltWMid pAltPart)
    (StageEval.const (S := S)
      (bmComplexSub_computesInTime W altWork altPart
        (haltWork_bds.mono (by omega)) (haltPart_bds.mono (by omega))
        (hdiff_bds.mono (by omega))))
  let corr := divNatFixed diff t1
  have hcorr_bds : WordWidthBounds (9 * q + 2) corr :=
    ⟨FitsSignedWord.roundDivInt _ hdiff_bds.1,
     FitsSignedWord.roundDivInt _ hdiff_bds.2⟩
  have pCorr := StageEval.seq
    (StageEval.fanout (StageEval.fanout pWMid pT1Mid) pDiff)
    (StageEval.const (S := S)
      (bmDivNatFixed_computesInTime W W t1 diff (by omega)
        (by rw [show W = 10 * q from rfl]; exact lt_of_le_of_lt ht1 (pow_lt_pow_right₀ (by decide) (by omega)))
        (hdiff_bds.mono (by omega)) (hcorr_bds.mono (by omega))))
  have pReconCtx := StageEval.fanout pQQ pCorr
  let encReconCtx := encPair (encPair encUnary encUnary) (encComplex W (q := qWork))
  let reconCtxVal := ((q, qWork), corr)
  let SubU := { p : S × Fin t1 // p.2 ∈ List.finRange t1 }
  have hReconStep : StageEval (S := SubU) bmNyquistReconEntry
      (encDepPair (fun _ => encReconCtx reconCtxVal)
        (fun p => encSt (nyqStFn p.val.2.val)))
      (fun p => encComplex W (nyquistColumnSolveFixed a Y altFixed p.val.2))
      (fun _ => 160000 * W + 60000 * q + 60000 * qWork + 250000) := by
    intro p u2 u3 u4 u5 uS
    have hu1_lt : p.val.2.val < t1 := p.val.2.isLt
    have hzp_u := hst_zp_bds p.val.2.val (le_of_lt hu1_lt)
    have hadd_u : WordWidthBounds (9 * q + 3) ((nyqStFn p.val.2.val).2.1 + corr) :=
      ⟨FitsSignedWord.add (hzp_u.1.mono (by omega)) hcorr_bds.1,
       FitsSignedWord.add (hzp_u.2.mono (by omega)) hcorr_bds.2⟩
    have hsub_u : WordWidthBounds (9 * q + 3) ((nyqStFn p.val.2.val).2.1 - corr) :=
      ⟨FitsSignedWord.sub (hzp_u.1.mono (by omega)) hcorr_bds.1,
       FitsSignedWord.sub (hzp_u.2.mono (by omega)) hcorr_bds.2⟩
    have hout_u : WordWidthBounds W (nyquistColumnSolveFixed a Y altFixed p.val.2) :=
      wordWidthBounds_nyquistColumnSolveFixed hq ht1 a ha_nn ha_le Y hY altFixed halt p.val.2
    have hval_eq :
        FixedComplex.rescale q
          (if (nyqStFn p.val.2.val).1 then (nyqStFn p.val.2.val).2.1 + corr
           else (nyqStFn p.val.2.val).2.1 - corr) =
          nyquistColumnSolveFixed a Y altFixed p.val.2 := by
      rw [hst_flag p.val.2.val (le_of_lt hu1_lt), hst_zp_getD p.val.2.val hu1_lt,
        ite_even_add_sub_eq_add_altSign]
      unfold nyquistColumnSolveFixed
      rw [memoizeFin_eq]
      have hB_memo : memoizeFin B_sc = B_sc := memoizeFin_eq B_sc
      dsimp only [corr, diff, altWork, qWork, invC0_m, zArr, B_sc] at haltPart_eq ⊢
      rw [hB_memo, haltPart_eq]
    rcases bmNyquistReconEntry_computesInTime W q qWork corr (nyqStFn p.val.2.val)
      (hcorr_bds.mono (by omega)) (hzp_u.mono (by omega))
      (hadd_u.mono (by omega)) (hsub_u.mono (by omega))
      (by rw [hval_eq]; exact hout_u) u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, encReconCtx, reconCtxVal, encSt, id] at ht hc ⊢
    rw [hval_eq] at hc
    exact ⟨t, ht, hc⟩
  have pMapRecon := StageEval.congr_in
    (u2 := encDepPair (fun _ : S => encReconCtx reconCtxVal)
      (fun _ : S => encList encSt traj_list))
    (StageEval.mapWithCtx_uniform (S := S)
      (ctx := fun _ => encReconCtx reconCtxVal)
      (xs := fun _ => List.finRange t1)
      (encA := fun _ u1 => encSt (nyqStFn u1.val))
      (encB := fun _ => encComplex W)
      (fn := fun _ u1 => nyquistColumnSolveFixed a Y altFixed u1)
      (B := fun _ => 160000 * W + 60000 * q + 60000 * qWork + 250000)
      (L_A := fun _ => 320 * q + 78)
      (L_B := fun _ => 40 * q + 8)
      hReconStep
      (fun _ _ _ => by
        dsimp only [encSt, W]
        simp only [length_encPair, encBool, List.length_singleton, length_encComplex]
        omega)
      (fun _ _ _ => by
        rw [length_encComplex W]
        omega))
    (fun _ => by simp only [encDepPair, traj_list, encList, List.map_map, Function.comp_def])
  have pFinish := StageEval.seq pScanStage (StageEval.seq (StageEval.fanout pReconCtx pTrajList) pMapRecon)
  have pAll := StageEval.seq pPrep pFinish
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_Y : (encList (encComplex W) Y_list).length = t1 * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8) Y_list
      (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [Y_list, List.length_map, List.length_finRange]
    ring
  have hlen_Brot_enc : (encList (encComplex W) B_rot).length = t1 * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8) B_rot
      (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [B_rot, B_list, length_rotateList, List.length_map, List.length_finRange]
    ring
  have hlen_traj : (encList encSt traj_list).length = t1 * (640 * q + 158) := by
    rw [length_encList_eq_of_forall_eq encSt (320 * q + 78) traj_list
      (fun x _ => by
        dsimp only [encSt, W]
        simp only [length_encPair, encBool, List.length_singleton, length_encComplex]
        ring)]
    simp only [traj_list, List.length_map, List.length_finRange]
    ring
  have hlen_Y_len : Y_list.length = t1 := by simp [Y_list]
  have hlen_B_len : B_list.length = t1 := by simp [B_list]
  dsimp only [uIn, uCtxIn, uYIn, uTopCtx, uTL, encScaleCtx, scaleCtxVal, encReconCtx, reconCtxVal, id] at ht
  rw [htraj_eq] at ht
  dsimp only [B_rot, traj_list] at ht hlen_Brot_enc hlen_Brot hlen_traj
  simp only [length_encDepPair, length_encPair, length_encUnary, encBool, List.length_singleton,
    length_encodeSignedWord, length_encComplex, List.length_finRange,
    hlen_Y, hlen_Brot_enc, hlen_traj, hlen_Y_len, hlen_B_len, hlen_Brot] at ht
  dsimp only [encSt, W, qWork] at ht
  simp only [length_encPair, encBool, List.length_singleton, length_encComplex] at ht
  dsimp only [uIn, uCtxIn, uYIn, uTopCtx, uTL, encScaleCtx, scaleCtxVal, encReconCtx, reconCtxVal, encSt, W, qWork, id] at hcomp ⊢
  change (bmNyquistColumnSolveWith bmMul).ComputesInTime _ _ t at hcomp
  refine ⟨t, ?_, hcomp⟩
  clear hcomp pAll pFinish pMapRecon hReconStep pReconCtx pCorr pDiff pAltPart pLastSt2 pLastSt
    pTrajList pWMid pAltWMid pT1Mid pT1AltW pQQ pTL pTopCtx pScanStage pScan hScanStep
    pPrep pAltWork pT1 pT1Raw pInitSt pTrue pZeroC pBRot pBListSeq pBList hScaleStep
    pInvC0 pTwoPowQQW pQQWork pW pQWork p4 pYList pAltIn pA pAAlt pQIn
  ring_nf at ht ⊢
  omega

/-! ## 6. Step 3 Column Dispatch & Multi-Column Deconvolution (`bmStep3ColDispatchWith`, `bmStep3DeconvolveColsWith`) -/

/-- **Single-Column Step 3 Dispatcher (`bmStep3ColDispatchWith bmMul`)**:
Consumes `((q, altFixed), ((isNyq, (c0_u2, c1_u2)), Y_col_list))` on `kIO`:
- If `isNyq = true`, runs `bmNyquistColumnSolveWith bmMul` on `((q, (c0_u2, altFixed)), Y_col_list)`.
- If `isNyq = false`, runs `bmCyclicBidiagPrevSolveWith bmMul` on `((q, (c0_u2, c1_u2)), Y_col_list)`. -/
def bmStep3ColDispatchWith (bmMul : BitMachine) : BitMachine :=
  let bmQ := bmSeq bmFst bmFst
  let bmAlt := bmSeq bmFst bmSnd
  let bmIsNyq := bmSeq (bmSeq bmSnd bmFst) bmFst
  let bmC01 := bmSeq (bmSeq bmSnd bmFst) bmSnd
  let bmC0 := bmSeq bmC01 bmFst
  let bmYCol := bmSeq bmSnd bmSnd
  let bmThen := bmSeq
    (bmFanout (bmFanout bmQ (bmFanout bmC0 bmAlt)) bmYCol)
    (bmNyquistColumnSolveWith bmMul)
  let bmElse := bmSeq
    (bmFanout (bmFanout bmQ bmC01) bmYCol)
    (bmCyclicBidiagPrevSolveWith bmMul)
  bmIte bmIsNyq bmThen bmElse

theorem bmStep3ColDispatchWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (t1 q : ℕ) [NeZero t1] (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (isNyq : Bool) (c0_u2 c1_u2 : ℤ)
    (hc0_nn : 0 ≤ c0_u2) (hc1_nn : 0 ≤ c1_u2)
    (hc0_le : c0_u2 ≤ 2 ^ (2 * q)) (hc1_le : c1_u2 ≤ 2 ^ (2 * q))
    (altFixed : FixedComplex q) (halt : WordWidthBounds (3 * q) altFixed)
    (Y_col : Fin t1 → FixedComplex q)
    (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y_col m))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W := 10 * q
    let encHdr := encPair encBool (encPair (encodeSignedWord W) (encodeSignedWord W))
    ∃ t ≤ (t1 + 1) * (14 * mulTime W + 6500000 * q + 5000000) +
          12000000 * q * q,
      (bmStep3ColDispatchWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encComplex W))
            (encPair encHdr (encList (encComplex W)))
            ((q, altFixed), ((isNyq, (c0_u2, c1_u2)), (List.finRange t1).map Y_col))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encComplex W)
            ((List.finRange t1).map
              (if isNyq then nyquistColumnSolveFixed c0_u2 Y_col altFixed
               else cyclicBidiagPrevSolveFixed c0_u2 c1_u2 Y_col))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro W encHdr
  have ht1_pos : 0 < t1 := NeZero.pos t1
  let S := Unit
  let Y_list := (List.finRange t1).map Y_col
  let uCtx : S → List Bool := fun _ => encPair encUnary (encComplex W) (q, altFixed)
  let uHdr : S → List Bool := fun _ => encHdr (isNyq, (c0_u2, c1_u2))
  let uY : S → List Bool := fun _ => encList (encComplex W) Y_list
  let uRhs : S → List Bool := encDepPair uHdr uY
  have pQ := StageEval.seq (StageEval.fst uCtx uRhs)
    (StageEval.fst (fun _ : S => encUnary q) (fun _ : S => encComplex W altFixed))
  have pAlt := StageEval.seq (StageEval.fst uCtx uRhs)
    (StageEval.snd (fun _ : S => encUnary q) (fun _ : S => encComplex W altFixed))
  have pHdr := StageEval.seq (StageEval.snd uCtx uRhs) (StageEval.fst uHdr uY)
  have pYCol := StageEval.seq (StageEval.snd uCtx uRhs) (StageEval.snd uHdr uY)
  have pIsNyq := StageEval.seq pHdr
    (StageEval.fst (fun _ : S => encBool isNyq)
      (fun _ : S => encPair (encodeSignedWord W) (encodeSignedWord W) (c0_u2, c1_u2)))
  have pC01 := StageEval.seq pHdr
    (StageEval.snd (fun _ : S => encBool isNyq)
      (fun _ : S => encPair (encodeSignedWord W) (encodeSignedWord W) (c0_u2, c1_u2)))
  have pC0 := StageEval.seq pC01
    (StageEval.fst (fun _ : S => encodeSignedWord W c0_u2)
      (fun _ : S => encodeSignedWord W c1_u2))
  have pThenIn := StageEval.fanout (StageEval.fanout pQ (StageEval.fanout pC0 pAlt)) pYCol
  have pThen := StageEval.seq pThenIn
    (StageEval.const (S := S)
      (bmNyquistColumnSolveWith_computesInTime hmul t1 q hq ht1_pos ht1 c0_u2 hc0_nn hc0_le
        altFixed halt Y_col hY))
  have pElseIn := StageEval.fanout (StageEval.fanout pQ pC01) pYCol
  have pElse := StageEval.seq pElseIn
    (StageEval.const (S := S)
      (bmCyclicBidiagPrevSolveWith_computesInTime hmul t1 q hq ht1 c0_u2 c1_u2
        hc0_nn hc1_nn hc0_le hc1_le Y_col hY))
  have pIteRaw := StageEval.ite_stage pIsNyq pThen pElse
  have pIte := StageEval.congr_out
    (v2 := fun _ : S =>
      encList (encComplex W)
        ((List.finRange t1).map
          (if isNyq then nyquistColumnSolveFixed c0_u2 Y_col altFixed
           else cyclicBidiagPrevSolveFixed c0_u2 c1_u2 Y_col)))
    pIteRaw
    (fun _ => by cases isNyq <;> rfl)
  rcases pIte () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_Y : (encList (encComplex W) Y_list).length = t1 * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8) Y_list
      (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [Y_list, List.length_map, List.length_finRange]
    ring
  dsimp only [uCtx, uRhs, uHdr, uY, encHdr, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, encBool, List.length_singleton,
    length_encodeSignedWord, length_encComplex, hlen_Y] at ht
  dsimp only [W] at ht
  change (bmStep3ColDispatchWith bmMul).ComputesInTime _ _ t at hcomp
  refine ⟨t, ?_, hcomp⟩
  dsimp only [W]
  split_ifs at ht <;> { ring_nf at ht ⊢; omega }

/-- **Uniform Multi-Column Step 3 Deconvolution (`bmStep3DeconvolveColsWith bmMul`)**:
Consumes `((q, altFixed), ((c0_list, c1_list), Y_cols_list))` on `kIO`, where
`Y_cols_list` is the $r \times t_1$ column-major matrix `(List.finRange r).map (fun u2 => (List.finRange t1).map (Y_cols u2))`,
and emits `encList (encList (encComplex (10 * q))) ((List.finRange r).map (fun u2 => (List.finRange t1).map (Z_colsFixed u2)))`,
where column `u2 = r / 2` is solved by `nyquistColumnSolveFixed` and all other columns `u2 ≠ r / 2`
are solved by `cyclicBidiagPrevSolveFixed`. -/
def bmStep3DeconvolveColsWith (bmMul : BitMachine) : BitMachine :=
  let bmCtx := bmFst
  let bmC01Lists := bmSeq bmSnd bmFst
  let bmC0List := bmSeq bmC01Lists bmFst
  let bmYCols := bmSeq bmSnd bmSnd
  let bmR := bmSeq bmC0List bmListLengthUnary
  let bmHalfR := bmSeq bmR bmHalfLenUnary
  let bmRangeR := bmSeq bmR bmRangeList
  let bmIsNyqList := bmSeq (bmFanout bmHalfR bmRangeR) (bmMapWithCtx bmUnaryEq)
  let bmC01Zip := bmSeq bmC01Lists bmZipList
  let bmHdrZip := bmSeq (bmFanout bmIsNyqList bmC01Zip) bmZipList
  let bmColInputs := bmSeq (bmFanout bmHdrZip bmYCols) bmZipList
  bmSeq (bmFanout bmCtx bmColInputs) (bmMapWithCtx (bmStep3ColDispatchWith bmMul))

set_option maxHeartbeats 800000 in
theorem bmStep3DeconvolveColsWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (r t1 q : ℕ) [NeZero t1] (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (c0Mantissa c1Mantissa : Fin r → ℤ)
    (hc0_nn : ∀ u2 : Fin r, 0 ≤ c0Mantissa u2)
    (hc1_nn : ∀ u2 : Fin r, 0 ≤ c1Mantissa u2)
    (hc0_le : ∀ u2 : Fin r, c0Mantissa u2 ≤ 2 ^ (2 * q))
    (hc1_le : ∀ u2 : Fin r, c1Mantissa u2 ≤ 2 ^ (2 * q))
    (altFixed : FixedComplex q) (halt : WordWidthBounds (3 * q) altFixed)
    (Y_cols : Fin r → Fin t1 → FixedComplex q)
    (hY : ∀ u2 : Fin r, ∀ m : Fin t1, WordWidthBounds (3 * q) (Y_cols u2 m))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W := 10 * q
    let Z_cols : Fin r → Fin t1 → FixedComplex q := fun u2 =>
      if u2.val = r / 2 then
        nyquistColumnSolveFixed (c0Mantissa u2) (Y_cols u2) altFixed
      else
        cyclicBidiagPrevSolveFixed (c0Mantissa u2) (c1Mantissa u2) (Y_cols u2)
    ∃ t ≤ (r + 1) *
            ((t1 + 1) * (14 * mulTime W + 7000000 * q + 5500000) +
              12000000 * q * q) +
          2000 * r * r,
      (bmStep3DeconvolveColsWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encComplex W))
            (encPair (encPair (encList (encodeSignedWord W)) (encList (encodeSignedWord W)))
              (encList (encList (encComplex W))))
            ((q, altFixed),
              (((List.finRange r).map c0Mantissa, (List.finRange r).map c1Mantissa),
                (List.finRange r).map (fun u2 => (List.finRange t1).map (Y_cols u2))))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encList (encList (encComplex W))
            ((List.finRange r).map (fun u2 => (List.finRange t1).map (Z_cols u2)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro W Z_cols
  let S := Unit
  let c0_list := (List.finRange r).map c0Mantissa
  let c1_list := (List.finRange r).map c1Mantissa
  let Y_cols_list := (List.finRange r).map (fun u2 => (List.finRange t1).map (Y_cols u2))
  let encSW := encodeSignedWord W
  let encCol := encList (encComplex W (q := q))
  let uCtx : S → List Bool := fun _ => encPair encUnary (encComplex W) (q, altFixed)
  let uC01 : S → List Bool := fun _ =>
    encPair (encList encSW) (encList encSW) (c0_list, c1_list)
  let uYCols : S → List Bool := fun _ => encList encCol Y_cols_list
  let uRhs : S → List Bool := encDepPair uC01 uYCols
  have pCtx := StageEval.fst uCtx uRhs
  have pRhs := StageEval.snd uCtx uRhs
  have pC01Lists := StageEval.seq pRhs (StageEval.fst uC01 uYCols)
  have pC0List := StageEval.seq pC01Lists
    (StageEval.fst (fun _ : S => encList encSW c0_list) (fun _ : S => encList encSW c1_list))
  have pYCols := StageEval.seq pRhs (StageEval.snd uC01 uYCols)
  have pRRaw := StageEval.seq pC0List
    (StageEval.const (S := S)
      (bmListLengthUnary_computesInTime encSW (10 * q + 1)
        (fun x => by dsimp only [encSW, W]; rw [length_encodeSignedWord]) c0_list))
  have pR := StageEval.congr_out (v2 := fun _ : S => encUnary r) pRRaw
    (fun _ => by simp [c0_list])
  have pHalfRRaw := StageEval.seq pR
    (StageEval.of_computesStageLe (bmHalfLenUnary_computesStageLe encUnary) (fun _ : S => r))
  have pHalfR := StageEval.congr_out (v2 := fun _ : S => encUnary (r / 2)) pHalfRRaw
    (fun _ => by simp [length_encUnary])
  have pRangeR := StageEval.seq pR
    (StageEval.of_computesStageLe bmRangeList_computesStageLe (fun _ : S => r))
  let SubEq := { p : S × Fin r // p.2 ∈ List.finRange r }
  have hEqStep : StageEval (S := SubEq) bmUnaryEq
      (encDepPair (fun _ => encUnary (r / 2)) (fun p => encUnary p.val.2.val))
      (fun p => encBool (decide (p.val.2.val = r / 2)))
      (fun _ => 500 * r + 300) := by
    intro p u2 u3 u4 u5 uS
    have hu2_lt : p.val.2.val < r := p.val.2.isLt
    rcases bmUnaryEq_computesStageLe (r / 2, p.val.2.val) u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, id] at ht hc ⊢
    have hcomm : decide (r / 2 = p.val.2.val) = decide (p.val.2.val = r / 2) := by
      simp [eq_comm]
    rw [hcomm] at hc
    exact ⟨t, by omega, hc⟩
  have pMapEq := StageEval.congr_in
    (u2 := encDepPair (fun _ : S => encUnary (r / 2))
      (fun _ : S => encList encUnary (List.range r)))
    (StageEval.mapWithCtx_uniform (S := S)
      (ctx := fun _ => encUnary (r / 2))
      (xs := fun _ => List.finRange r)
      (encA := fun _ u2 => encUnary u2.val)
      (encB := fun _ => encBool)
      (fn := fun _ u2 => decide (u2.val = r / 2))
      (B := fun _ => 500 * r + 300)
      (L_A := fun _ => r)
      (L_B := fun _ => 1)
      hEqStep
      (fun _ u2 _ => by rw [length_encUnary]; exact le_of_lt u2.isLt)
      (fun _ _ _ => by dsimp only [encBool, List.length_singleton]; omega))
    (fun _ => by
      dsimp only [encDepPair, encList]
      rw [map_finRange_eq_map_range r encUnary])
  have pIsNyqList := StageEval.seq (StageEval.fanout pHalfR pRangeR) pMapEq
  let isNyq_list := (List.finRange r).map (fun u2 => decide (u2.val = r / 2))
  let c01_list := (List.finRange r).map (fun u2 => (c0Mantissa u2, c1Mantissa u2))
  let hdr_list := (List.finRange r).map
    (fun u2 => (decide (u2.val = r / 2), (c0Mantissa u2, c1Mantissa u2)))
  let col_inputs := (List.finRange r).map
    (fun u2 => ((decide (u2.val = r / 2), (c0Mantissa u2, c1Mantissa u2)),
      (List.finRange t1).map (Y_cols u2)))
  let encC01 := encPair encSW encSW
  let encHdr := encPair encBool encC01
  let encColIn := encPair encHdr encCol
  have hzip1_len : c0_list.length = c1_list.length := by simp [c0_list, c1_list]
  have hzip1_eq : List.zip c0_list c1_list = c01_list :=
    zip_map_eq (List.finRange r) c0Mantissa c1Mantissa
  have hzip1_stage : StageEval bmZipList uC01 (fun _ : S => encList encC01 c01_list)
      (fun s => 26 * (uC01 s).length + 50) := by
    intro _ u2 u3 u4 u5 uS
    rcases bmZipList_computesStageLe encSW encSW ⟨(c0_list, c1_list), hzip1_len⟩ u2 u3 u4 u5 uS
      with ⟨t, ht, hc⟩
    dsimp only [uC01] at ht hc ⊢
    rw [hzip1_eq] at hc
    exact ⟨t, ht, hc⟩
  have pC01Zip := StageEval.seq pC01Lists hzip1_stage
  have hzip2_len : isNyq_list.length = c01_list.length := by simp [isNyq_list, c01_list]
  have hzip2_eq : List.zip isNyq_list c01_list = hdr_list :=
    zip_map_eq (List.finRange r) _ _
  let uZip2In : S → List Bool :=
    encDepPair (fun _ => encList encBool isNyq_list) (fun _ => encList encC01 c01_list)
  have hzip2_stage : StageEval bmZipList uZip2In (fun _ : S => encList encHdr hdr_list)
      (fun s => 26 * (uZip2In s).length + 50) := by
    intro _ u2 u3 u4 u5 uS
    rcases bmZipList_computesStageLe encBool encC01 ⟨(isNyq_list, c01_list), hzip2_len⟩ u2 u3 u4 u5 uS
      with ⟨t, ht, hc⟩
    dsimp only [uZip2In, encDepPair] at ht hc ⊢
    rw [hzip2_eq] at hc
    exact ⟨t, ht, hc⟩
  have pHdrZip := StageEval.seq (StageEval.fanout pIsNyqList pC01Zip) hzip2_stage
  have hzip3_len : hdr_list.length = Y_cols_list.length := by simp [hdr_list, Y_cols_list]
  have hzip3_eq : List.zip hdr_list Y_cols_list = col_inputs :=
    zip_map_eq (List.finRange r) _ _
  let uZip3In : S → List Bool :=
    encDepPair (fun _ => encList encHdr hdr_list) uYCols
  have hzip3_stage : StageEval bmZipList uZip3In (fun _ : S => encList encColIn col_inputs)
      (fun s => 26 * (uZip3In s).length + 50) := by
    intro _ u2 u3 u4 u5 uS
    rcases bmZipList_computesStageLe encHdr encCol ⟨(hdr_list, Y_cols_list), hzip3_len⟩ u2 u3 u4 u5 uS
      with ⟨t, ht, hc⟩
    dsimp only [uZip3In, uYCols, encDepPair] at ht hc ⊢
    rw [hzip3_eq] at hc
    exact ⟨t, ht, hc⟩
  have pColInputs := StageEval.seq (StageEval.fanout pHdrZip pYCols) hzip3_stage
  let B_col := (t1 + 1) * (14 * mulTime W + 6500000 * q + 5000000) +
    12000000 * q * q
  let SubCol := { p : S × Fin r // p.2 ∈ List.finRange r }
  have hColStep : StageEval (S := SubCol) (bmStep3ColDispatchWith bmMul)
      (encDepPair (fun p => uCtx p.val.1)
        (fun p => encColIn
          ((decide (p.val.2.val = r / 2), (c0Mantissa p.val.2, c1Mantissa p.val.2)),
            (List.finRange t1).map (Y_cols p.val.2))))
      (fun p => encCol ((List.finRange t1).map (Z_cols p.val.2)))
      (fun _ => B_col) := by
    intro p u2 u3 u4 u5 uS
    have hZ_eq :
        (if decide (p.val.2.val = r / 2) = true then
          nyquistColumnSolveFixed (c0Mantissa p.val.2) (Y_cols p.val.2) altFixed
         else
          cyclicBidiagPrevSolveFixed (c0Mantissa p.val.2) (c1Mantissa p.val.2) (Y_cols p.val.2)) =
        Z_cols p.val.2 := by
      dsimp only [Z_cols]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (of_decide_eq_true h1) h2
      · exact absurd (decide_eq_true h2) h1
      · rfl
    rcases bmStep3ColDispatchWith_computesInTime hmul t1 q hq ht1
      (decide (p.val.2.val = r / 2)) (c0Mantissa p.val.2) (c1Mantissa p.val.2)
      (hc0_nn p.val.2) (hc1_nn p.val.2) (hc0_le p.val.2) (hc1_le p.val.2)
      altFixed halt (Y_cols p.val.2) (hY p.val.2) u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
    dsimp only [encDepPair, uCtx, encColIn, encHdr, encC01, encSW, encCol, id] at ht hc ⊢
    rw [hZ_eq] at hc
    exact ⟨t, ht, hc⟩
  have hlen_col : ∀ u2 : Fin r,
      (encCol ((List.finRange t1).map (Y_cols u2))).length = t1 * (80 * q + 18) := by
    intro u2
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8)
      ((List.finRange t1).map (Y_cols u2)) (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [List.length_map, List.length_finRange]
    ring
  have hlen_Zcol : ∀ u2 : Fin r,
      (encCol ((List.finRange t1).map (Z_cols u2))).length = t1 * (80 * q + 18) := by
    intro u2
    rw [length_encList_eq_of_forall_eq (encComplex W) (40 * q + 8)
      ((List.finRange t1).map (Z_cols u2)) (fun x _ => by rw [length_encComplex W]; omega)]
    simp only [List.length_map, List.length_finRange]
    ring
  have pMapCols := StageEval.congr_in
    (u2 := encDepPair uCtx (fun _ : S => encList encColIn col_inputs))
    (StageEval.mapWithCtx_uniform (S := S)
      (ctx := uCtx)
      (xs := fun _ => List.finRange r)
      (encA := fun _ u2 => encColIn
        ((decide (u2.val = r / 2), (c0Mantissa u2, c1Mantissa u2)),
          (List.finRange t1).map (Y_cols u2)))
      (encB := fun _ => encCol)
      (fn := fun _ u2 => (List.finRange t1).map (Z_cols u2))
      (B := fun _ => B_col)
      (L_A := fun _ => 2 * t1 * (80 * q + 18) + 160 * q + 48)
      (L_B := fun _ => t1 * (80 * q + 18))
      hColStep
      (fun _ u2 _ => by
        dsimp only [encColIn, encHdr, encC01, encSW]
        simp only [length_encPair, encBool, List.length_singleton, length_encodeSignedWord, hlen_col u2]
        dsimp only [W]
        linarith)
      (fun _ u2 _ => by
        rw [hlen_Zcol u2]))
    (fun _ => by simp only [encDepPair, col_inputs, encList, List.map_map, Function.comp_def])
  have pAll := StageEval.seq (StageEval.fanout pCtx pColInputs) pMapCols
  rcases pAll () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hlen_c0 : (encList encSW c0_list).length = r * (20 * q + 4) := by
    rw [length_encList_eq_of_forall_eq encSW (10 * q + 1) c0_list
      (fun x _ => by dsimp only [encSW, W]; rw [length_encodeSignedWord])]
    simp only [c0_list, List.length_map, List.length_finRange]
    ring
  have hlen_c1 : (encList encSW c1_list).length = r * (20 * q + 4) := by
    rw [length_encList_eq_of_forall_eq encSW (10 * q + 1) c1_list
      (fun x _ => by dsimp only [encSW, W]; rw [length_encodeSignedWord])]
    simp only [c1_list, List.length_map, List.length_finRange]
    ring
  have hlen_c01 : (encList encC01 c01_list).length = r * (80 * q + 18) := by
    rw [length_encList_eq_of_forall_eq encC01 (40 * q + 8) c01_list
      (fun x _ => by
        dsimp only [encC01, encSW, W]
        simp only [length_encPair, length_encodeSignedWord]
        ring)]
    simp only [c01_list, List.length_map, List.length_finRange]
    ring
  have hlen_isNyq : (encList encBool isNyq_list).length = 4 * r := by
    rw [length_encList_eq_of_forall_eq encBool 1 isNyq_list
      (fun x _ => by simp [encBool])]
    simp only [isNyq_list, List.length_map, List.length_finRange]
    ring
  have hlen_hdr : (encList encHdr hdr_list).length = r * (160 * q + 46) := by
    rw [length_encList_eq_of_forall_eq encHdr (80 * q + 22) hdr_list
      (fun x _ => by
        dsimp only [encHdr, encC01, encSW, W]
        simp only [length_encPair, encBool, List.length_singleton, length_encodeSignedWord]
        ring)]
    simp only [hdr_list, List.length_map, List.length_finRange]
    ring
  have hlen_YCols : (encList encCol Y_cols_list).length = r * (2 * t1 * (80 * q + 18) + 2) := by
    rw [length_encList_eq_of_forall_eq encCol (t1 * (80 * q + 18)) Y_cols_list
      (fun x hx => by
        rw [List.mem_map] at hx
        rcases hx with ⟨u2, _, rfl⟩
        exact hlen_col u2)]
    simp only [Y_cols_list, List.length_map, List.length_finRange]
    ring
  have hlen_colIn : (encList encColIn col_inputs).length =
      r * (4 * t1 * (80 * q + 18) + 320 * q + 98) := by
    rw [length_encList_eq_of_forall_eq encColIn (2 * t1 * (80 * q + 18) + 160 * q + 48) col_inputs
      (fun x hx => by
        rw [List.mem_map] at hx
        rcases hx with ⟨u2, _, rfl⟩
        dsimp only [encColIn, encHdr, encC01, encSW]
        simp only [length_encPair, encBool, List.length_singleton, length_encodeSignedWord, hlen_col u2]
        dsimp only [W]
        ring)]
    simp only [col_inputs, List.length_map, List.length_finRange]
    ring
  have hlen_rangeR : (encList encUnary (List.range r)).length ≤ r * (2 * r + 2) := by
    have h := length_encList_le_of_forall_le encUnary r (List.range r) (fun x hx => by
      rw [List.mem_range] at hx
      rw [length_encUnary]
      omega)
    simpa [List.length_range] using h
  have hc0_len : c0_list.length = r := by simp [c0_list]
  have hhalf_le : r / 2 ≤ r := Nat.div_le_self r 2
  have hmul_half_le : r * (r / 2) ≤ r ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left r hhalf_le
  dsimp only [uCtx, uRhs, uC01, uYCols, uZip2In, uZip3In, id] at ht hcomp
  dsimp only [isNyq_list] at ht hlen_isNyq
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    List.length_finRange, hlen_c0, hlen_c1, hlen_c01, hlen_isNyq, hlen_hdr, hlen_YCols,
    hlen_colIn, hc0_len] at ht
  dsimp only [B_col, W] at ht
  change (bmStep3DeconvolveColsWith bmMul).ComputesInTime _ _ t at hcomp
  refine ⟨t, ?_, hcomp⟩
  dsimp only [W]
  clear hcomp pAll pMapCols hColStep pColInputs hzip3_stage pHdrZip hzip2_stage
    pC01Zip hzip1_stage pIsNyqList pMapEq hEqStep pRangeR pHalfR pHalfRRaw pR pRRaw
    pYCols pC0List pC01Lists pRhs pCtx
  ring_nf at ht hlen_rangeR ⊢
  omega

end IntMul
