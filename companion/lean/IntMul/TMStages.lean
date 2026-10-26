import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives
import IntMul.TMComposition
import IntMul.TMCompiler
import IntMul.FastDFT
import IntMul.ComputableSchedule
import IntMul.ComputableCore
import IntMul.TrackedCore

set_option backward.isDefEq.respectTransparency false

/-!
# Compositional Uniform `BitMachine` Stage Algebra & Linear-Time Combinators (`IntMul.TMStages`)

This module builds the compositional stage algebra (`ComputesStage`, `ComputesStageLe`),
the non-empty delimited-word loop combinator (`BitMachine.loopNonEmptyWord`), the $O(b)$
head-slicing gadget (`tmPopBitOrZero`, `bmSliceDropBits`), the linear-time list combinators
(`bmFoldList`, `bmRevList`, `bmMapWithCtx`, `bmAppendList`), and the delimited-frame
arithmetic stages (`bmRippleAdd`, `bmUnsignedButterfly`, `bmSignedButterfly`, `bmCondSubStep`)
for the uniform 8-stack binary machine (`Turing.FinTM2`, Section 8 (`sec:lean`)):

1. **Parameter-Free `BitMachine` Terms**:
   Every `bm* : BitMachine` combinator is a concrete 1-bit stack machine over `DelimReg`
   (`|σ| = 32`, `|Γ k| = 2`, `TapeIdx = Fin 8`) with no type arguments `α, β`, no
   encoding functions `encA, encB`, no mathematical specification functions `fn`, and no step-bound
   functions in its machine definition. All mathematical specifications live exclusively in `Prop`
   via `ComputesStage` and `ComputesStageLe`.
2. **Non-Empty Word Loop (`BitMachine.loopNonEmptyWord`)**:
   Iterates while the top delimited word on `kList : TapeIdx` is non-empty, halting in 1 step
   when `encodeDelimWord []` is reached and leaving the underlying stack intact. This enables
   linear $O(\sum |e|)$ list folds, reversals, maps, and bucket splits without length
   prefixes or quadratic tail copies.
3. **$O(b)$ Head-Slicing Gadget (`tmPopBitOrZero`, `bmSliceDropBits`)**:
   Pops `b` bits (padding with `false` if the source word is shorter than `b`) from the head of
   `encodeDelimWord bs` in `2 * b + 1` loop steps independent of `bs.length`, ensuring
   that `sliceBitChunks`, `unpackSignedSlotsBits`, and `carrySaveEmitBits` run in linear
   $O(R \cdot b)$ steps.
-/

namespace IntMul

open Turing

/-! ## 1. Non-Empty Delimited Word Loop (`BitMachine.loopNonEmptyWord`) & State-Indexed Loop Lemmas -/

/-- First bit of `encodeDelimWord u ++ s`: `true` if `u = []`, `false` if `u = b :: u'`. -/
def delimWordHead (u : List Bool) : Bool :=
  match u with
  | [] => true
  | _ :: _ => false

/-- Tail of `encodeDelimWord u ++ s` after the first bit `delimWordHead u`. -/
def delimWordTail (u s : List Bool) : List Bool :=
  match u with
  | [] => false :: s
  | b :: u' => b :: (encodeDelimWord u' ++ s)

theorem encodeDelimWord_append_eq_head_tail (u s : List Bool) :
    encodeDelimWord u ++ s = delimWordHead u :: delimWordTail u s := by
  cases u <;> rfl

@[simp]
theorem unconsDelimWord_encodeDelimWord (u : List Bool) :
    unconsDelimWord (encodeDelimWord u) = (u, []) := by
  simpa using unconsDelimWord_encodeDelimWord_append u []

namespace BitMachine

/-- **Non-Empty Delimited Word Loop (`BitMachine.loopNonEmptyWord`)**:
Inspects the top delimited word `encodeDelimWord w` on `kList : TapeIdx`:
- If `w = []` (`encodeDelimWord [] = [true, false]`), pops `[true, false]` from `kList` and halts
  in `1` step, leaving `restList` on `kList`.
- If `w = b :: w'` (`encodeDelimWord (b :: w') = false :: b :: encodeDelimWord w'`), pops `false`
  and `b`, pushes `b` and `false` back onto `kList` (restoring `encodeDelimWord w ++ restList`
  untouched), and transitions to `some body.main` in `1` step; when `body` halts, returns to `none`. -/
def loopNonEmptyWord (kList : TapeIdx) (body : BitMachine) : BitMachine where
  Λ := Option body.Λ
  main := none
  m := fun lbl =>
    match lbl with
    | none =>
      Turing.TM2.Stmt.pop kList
        (fun _ bOpt => (default, bOpt.getD true))
        (Turing.TM2.Stmt.pop kList
          (fun rv bOpt => ({ rv.1 with bitA := bOpt.getD false }, rv.2))
          (Turing.TM2.Stmt.branch (fun rv => rv.2)
            (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
            (Turing.TM2.Stmt.push kList (fun rv => rv.1.bitA)
              (Turing.TM2.Stmt.push kList (fun _ => false)
                (Turing.TM2.Stmt.load (fun _ => default)
                  (Turing.TM2.Stmt.goto (fun _ => some body.main)))))))
    | some l => redirectLoopBodyStmt default (body.m l)

@[simp]
theorem numLabels_loopNonEmptyWord (kList : TapeIdx) (body : BitMachine) :
    (body.loopNonEmptyWord kList).numLabels = body.numLabels + 1 :=
  Fintype.card_option

theorem step_loopNonEmptyWord_body (kList : TapeIdx) (body : BitMachine)
    (x y : body.toFinTM2.Cfg)
    (h : body.toFinTM2.step x = some y) :
    (body.loopNonEmptyWord kList).toFinTM2.step (mapLoopBodyCfg default x) =
      some (mapLoopBodyCfg default y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [loopNonEmptyWord, toFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      mapLoopBodyCfg]
    exact congrArg some (stepAux_redirectLoopBodyStmt default (body.m l) v stk)

def loopNonEmptyWord_body_evalsToInTime_concrete (kList : TapeIdx) (body : BitMachine)
    {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {B : ℕ}
    (hbody : Turing.EvalsToInTime body.toFinTM2.step
      ⟨some body.main, default, T₁⟩ (some ⟨none, default, T₂⟩) B) :
    Turing.EvalsToInTime (body.loopNonEmptyWord kList).toFinTM2.step
      ⟨some (some body.main), default, T₁⟩ (some ⟨some none, default, T₂⟩) B :=
  EvalsToInTime.map_simulation (mapLoopBodyCfg default)
    (step_loopNonEmptyWord_body kList body) hbody

/-- Upper-bounded state-indexed loop theorem for `BitMachine.loopDelimWord` in `Prop` (zero `Classical.choice`). -/
theorem ComputesInTime.loopDelimWord_state_le {α : Type} (kCnt : TapeIdx) {body : BitMachine}
    (nextSt : α → α) (stepBound : α → ℕ)
    (stkOf : α → (∀ k : TapeIdx, List (BitTapeAlphabet k)))
    (hpass : ∀ (st : α) (tailCnt : List Bool),
      ∃ t ≤ stepBound st,
        body.ComputesInTime
          (Function.update (stkOf st) kCnt tailCnt)
          (Function.update (stkOf (nextSt st)) kCnt tailCnt) t) :
    ∀ (cnt : List Bool) (restCnt : List Bool) (st : α),
      ∃ t ≤ loopStepsAux nextSt stepBound cnt st,
        (body.loopDelimWord kCnt).ComputesInTime
          (Function.update (stkOf st) kCnt (encodeDelimWord cnt ++ restCnt))
          (Function.update (stkOf (loopFinalState nextSt cnt st)) kCnt restCnt) t
  | [], restCnt, st => by
    refine ⟨1, by simp [loopStepsAux], ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, Function.update_self, Function.update_idem, List.head?_cons,
      List.tail_cons, Option.getD_some, cond_true, loopFinalState_nil]
  | b :: cnt, restCnt, st => by
    have hpop : (body.loopDelimWord kCnt).toFinTM2.step
        ⟨some none, default,
          Function.update (stkOf st) kCnt (encodeDelimWord (b :: cnt) ++ restCnt)⟩ =
        some ⟨some (some body.main), default,
          Function.update (stkOf st) kCnt (encodeDelimWord cnt ++ restCnt)⟩ := by
      simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons, List.cons_append,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    rcases hpass st (encodeDelimWord cnt ++ restCnt) with ⟨t1, ht1, ⟨hbody⟩⟩
    have hbody_lifted := BitMachine.loopDelimWord_body_evalsToInTime_concrete kCnt body hbody
    rcases ComputesInTime.loopDelimWord_state_le kCnt nextSt stepBound stkOf hpass
      cnt restCnt (nextSt st) with ⟨t2, ht2, ⟨hih⟩⟩
    have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
    have hcomb := EvalsToInTime.trans' hstep1 hih
    refine ⟨(t1 + 1) + t2, ?_, ⟨hcomb⟩⟩
    simp only [loopStepsAux_cons]
    omega

end BitMachine

/-- Final state reached by iterating `nextSt : α → β → β` over a list `xs : List α`. -/
def loopListFinalState {α β : Type} (nextSt : α → β → β) : List α → β → β
  | [], st => st
  | x :: xs, st => loopListFinalState nextSt xs (nextSt x st)

@[simp]
theorem loopListFinalState_nil {α β : Type} (nextSt : α → β → β) (st : β) :
    loopListFinalState nextSt [] st = st := rfl

@[simp]
theorem loopListFinalState_cons {α β : Type} (nextSt : α → β → β) (x : α) (xs : List α) (st : β) :
    loopListFinalState nextSt (x :: xs) st = loopListFinalState nextSt xs (nextSt x st) := rfl

/-- Total step bound of `body.loopNonEmptyWord kList` over `xs : List α`. -/
def loopListStepsAux {α β : Type} (nextSt : α → β → β) (stepBound : α → List α → β → ℕ) :
    List α → β → ℕ
  | [], _ => 1
  | x :: xs, st => 1 + stepBound x xs st + loopListStepsAux nextSt stepBound xs (nextSt x st)

@[simp]
theorem loopListStepsAux_nil {α β : Type} (nextSt : α → β → β)
    (stepBound : α → List α → β → ℕ) (st : β) :
    loopListStepsAux nextSt stepBound [] st = 1 := rfl

@[simp]
theorem loopListStepsAux_cons {α β : Type} (nextSt : α → β → β)
    (stepBound : α → List α → β → ℕ) (x : α) (xs : List α) (st : β) :
    loopListStepsAux nextSt stepBound (x :: xs) st =
      1 + stepBound x xs st + loopListStepsAux nextSt stepBound xs (nextSt x st) := rfl

/-- Upper-bounded list-iteration theorem for `BitMachine.loopNonEmptyWord` over an encoded
word-stack `encodeDelimWord (encodeWordStack (xs.map encElem))` on `kList : TapeIdx`. -/
theorem BitMachine.ComputesInTime.loopNonEmptyWord_list_le {α β : Type} (kList : TapeIdx)
    {body : BitMachine} (encElem : α → List Bool)
    (nextSt : α → β → β) (stepBound : α → List α → β → ℕ)
    (stkOf : β → (∀ k : TapeIdx, List (BitTapeAlphabet k)))
    (hpass : ∀ (x : α) (xs : List α) (st : β) (restList : List Bool),
      ∃ t ≤ stepBound x xs st,
        body.ComputesInTime
          (Function.update (stkOf st) kList
            (encodeDelimWord (encodeDelimWord (encElem x) ++ encodeWordStack (xs.map encElem)) ++ restList))
          (Function.update (stkOf (nextSt x st)) kList
            (encodeDelimWord (encodeWordStack (xs.map encElem)) ++ restList)) t) :
    ∀ (xs : List α) (restList : List Bool) (st : β),
      ∃ t ≤ loopListStepsAux nextSt stepBound xs st,
        (body.loopNonEmptyWord kList).ComputesInTime
          (Function.update (stkOf st) kList
            (encodeDelimWord (encodeWordStack (xs.map encElem)) ++ restList))
          (Function.update (stkOf (loopListFinalState nextSt xs st)) kList restList) t
  | [], restList, st => by
    refine ⟨1, by simp [loopListStepsAux], ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopNonEmptyWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, List.map_nil, encodeWordStack_nil, encodeDelimWord_nil,
      List.cons_append, List.nil_append, Function.update_self, Function.update_idem,
      List.head?_cons, List.tail_cons, Option.getD_some, cond_true, loopListFinalState_nil]
  | x :: xs, restList, st => by
    have hpop : (body.loopNonEmptyWord kList).toFinTM2.step
        ⟨some none, default,
          Function.update (stkOf st) kList
            (encodeDelimWord (encodeWordStack ((x :: xs).map encElem)) ++ restList)⟩ =
        some ⟨some (some body.main), default,
          Function.update (stkOf st) kList
            (encodeDelimWord (encodeDelimWord (encElem x) ++ encodeWordStack (xs.map encElem)) ++ restList)⟩ := by
      simp only [List.map_cons, encodeWordStack_cons,
        encodeDelimWord_append_eq_head_tail (encElem x) (encodeWordStack (xs.map encElem)),
        encodeDelimWord_cons, List.cons_append, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
        Function.update_self, Function.update_idem, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    rcases hpass x xs st restList with ⟨t1, ht1, ⟨hbody⟩⟩
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete kList body hbody
    rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kList encElem nextSt stepBound stkOf
      hpass xs restList (nextSt x st) with ⟨t2, ht2, ⟨hih⟩⟩
    have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
    have hcomb := EvalsToInTime.trans' hstep1 hih
    refine ⟨(t1 + 1) + t2, ?_, ⟨hcomb⟩⟩
    simp only [loopListStepsAux_cons]
    omega

/-- Constant-per-iteration upper bound for `loopStepsAux`. -/
theorem loopStepsAux_le_of_const {α : Type} (nextSt : α → α) (stepBound : α → ℕ) (B : ℕ)
    (hB : ∀ st : α, stepBound st ≤ B) :
    ∀ (cnt : List Bool) (st : α),
      loopStepsAux nextSt stepBound cnt st ≤ cnt.length * (B + 1) + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: cnt, st => by
    simp only [loopStepsAux_cons, List.length_cons]
    have h1 := hB st
    have h2 := loopStepsAux_le_of_const nextSt stepBound B hB cnt (nextSt st)
    calc 1 + stepBound st + loopStepsAux nextSt stepBound cnt (nextSt st)
        ≤ 1 + B + (cnt.length * (B + 1) + 1) := by omega
      _ = (cnt.length + 1) * (B + 1) + 1 := by ring

/-! ## 2. Frame Gadgets (`tmFramePush5`, `tmFramePop6`), Pair-Packing Gadgets (`tmPackPairFromRev`, `tmPackPairFromRevSwapped`), & $O(b)$ Head-Slicing Gadget (`tmPopBitOrZero`) -/

/-- **Gadget 26 (`tmFramePush5`)**: Pushes `encodeDelimWord []` (`[true, false]`) onto the 6 stacks
`kIO`, `kWork2`, `kWork3`, `kWork4`, `kWork5`, and `kSched` in `1` step (`|Λ| = 1`), framing a
2-operand machine whose inputs sit on `kWork0` and `kWork1` (`threeTapeWorkStk [] xs ys`). -/
def tmFramePush5 : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.push kIO (fun _ => false)
      (Turing.TM2.Stmt.push kIO (fun _ => true)
        (Turing.TM2.Stmt.push kWork2 (fun _ => false)
          (Turing.TM2.Stmt.push kWork2 (fun _ => true)
            (Turing.TM2.Stmt.push kWork3 (fun _ => false)
              (Turing.TM2.Stmt.push kWork3 (fun _ => true)
                (Turing.TM2.Stmt.push kWork4 (fun _ => false)
                  (Turing.TM2.Stmt.push kWork4 (fun _ => true)
                    (Turing.TM2.Stmt.push kWork5 (fun _ => false)
                      (Turing.TM2.Stmt.push kWork5 (fun _ => true)
                        (Turing.TM2.Stmt.push kSched (fun _ => false)
                          (Turing.TM2.Stmt.push kSched (fun _ => true)
                            Turing.TM2.Stmt.halt)))))))))))

@[simp] theorem numLabels_tmFramePush5 : tmFramePush5.numLabels = 1 := rfl

theorem tmFramePush5_computesInTime (xs ys tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmFramePush5.ComputesInTime
      (mkTapes8 tIO (encodeDelimWord xs ++ tW0) (encodeDelimWord ys ++ tW1) tW2 tW3 tW4 tW5 tSch)
      (embedDelimFrame (threeTapeWorkStk [] xs ys) (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch))
      1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp only [tmFramePush5, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, Option.some.injEq, Turing.TM2.Cfg.mk.injEq,
    true_and]
  funext k; fin_cases k <;> rfl

/-- **Gadget 27 (`tmFramePop6`)**: Pops `encodeDelimWord []` (`[true, false]`) from the 6 non-output
stacks `kWork1`, `kWork2`, `kWork3`, `kWork4`, `kWork5`, and `kSched` in `1` step (`|Λ| = 1`),
leaving the two output words on `kIO` and `kWork0` (`twoTapeStk outIO outW0`). -/
def tmFramePop6 : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kWork1 (fun r _ => r)
      (Turing.TM2.Stmt.pop kWork1 (fun r _ => r)
        (Turing.TM2.Stmt.pop kWork2 (fun r _ => r)
          (Turing.TM2.Stmt.pop kWork2 (fun r _ => r)
            (Turing.TM2.Stmt.pop kWork3 (fun r _ => r)
              (Turing.TM2.Stmt.pop kWork3 (fun r _ => r)
                (Turing.TM2.Stmt.pop kWork4 (fun r _ => r)
                  (Turing.TM2.Stmt.pop kWork4 (fun r _ => r)
                    (Turing.TM2.Stmt.pop kWork5 (fun r _ => r)
                      (Turing.TM2.Stmt.pop kWork5 (fun r _ => r)
                        (Turing.TM2.Stmt.pop kSched (fun r _ => r)
                          (Turing.TM2.Stmt.pop kSched (fun _ _ => default)
                            Turing.TM2.Stmt.halt)))))))))))

@[simp] theorem numLabels_tmFramePop6 : tmFramePop6.numLabels = 1 := rfl

theorem tmFramePop6_computesInTime (outIO outW0 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmFramePop6.ComputesInTime
      (embedDelimFrame (twoTapeStk outIO outW0) (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch))
      (mkTapes8 (encodeDelimWord outIO ++ tIO) (encodeDelimWord outW0 ++ tW0) tW1 tW2 tW3 tW4 tW5 tSch)
      1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp only [tmFramePop6, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, Option.some.injEq, Turing.TM2.Cfg.mk.injEq,
    true_and]
  funext k; fin_cases k <;> rfl

/-- **Gadget 28 (`tmPackPairFromRev`)**:
Given `encodeDelimWord v1.reverse` on `kWork0` and `encodeDelimWord v2` on `kIO`, produces
`encodeDelimWord (encodeDelimWord v1 ++ encodeDelimWord v2)` on `kIO` (and empties `kWork0, kWork1`)
in `(v2.length + 2) + (1 + ((v2.length + 2) + (v1.length + 2)))` steps. -/
def tmPackPairFromRev : BitMachine :=
  (tmRevMoveWord kIO kWork1).seq
    ((tmPushEmpty kIO).seq
      ((tmPrependRevWord kWork1 kIO).seq
        (tmPrependRevWord kWork0 kIO)))

theorem tmPackPairFromRev_computesInTime (v1 v2 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmPackPairFromRev.ComputesInTime
      (mkTapes8 (encodeDelimWord v2) (encodeDelimWord v1.reverse) [] tW2 tW3 tW4 tW5 tSch)
      (mkTapes8 (encodeDelimWord (encodeDelimWord v1 ++ encodeDelimWord v2)) [] [] tW2 tW3 tW4 tW5 tSch)
      ((v2.length + 2) + (1 + ((v2.length + 2) + (v1.length + 2)))) := by
  have h1 := tmRevMoveWord_computesInTime kIO kWork1 (by decide)
    v2 [] [] (mkTapes8 [] (encodeDelimWord v1.reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil] at h1
  have h2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] (encodeDelimWord v1.reverse) (encodeDelimWord v2.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at h2
  have h3 := tmPrependRevWord_computesInTime kWork1 kIO (by decide)
    v2.reverse [] [] [] (mkTapes8 [] (encodeDelimWord v1.reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h3
  have h4 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
    v1.reverse (encodeDelimWord v2) [] [] (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h4
  exact h1.seq (h2.seq (h3.seq h4))

/-- **Gadget 29 (`tmPackPairFromRevSwapped`)**:
Given `encodeDelimWord v1` on `kIO` and `encodeDelimWord v2.reverse` on `kWork0`, produces
`encodeDelimWord (encodeDelimWord v1 ++ encodeDelimWord v2)` on `kIO` (and empties `kWork0, kWork1`)
in `(v1.length + 2) + (1 + ((v2.length + 2) + (v1.length + 2)))` steps. -/
def tmPackPairFromRevSwapped : BitMachine :=
  (tmRevMoveWord kIO kWork1).seq
    ((tmPushEmpty kIO).seq
      ((tmPrependRevWord kWork0 kIO).seq
        (tmPrependRevWord kWork1 kIO)))

theorem tmPackPairFromRevSwapped_computesInTime (v1 v2 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmPackPairFromRevSwapped.ComputesInTime
      (mkTapes8 (encodeDelimWord v1) (encodeDelimWord v2.reverse) [] tW2 tW3 tW4 tW5 tSch)
      (mkTapes8 (encodeDelimWord (encodeDelimWord v1 ++ encodeDelimWord v2)) [] [] tW2 tW3 tW4 tW5 tSch)
      ((v1.length + 2) + (1 + ((v2.length + 2) + (v1.length + 2)))) := by
  have h1 := tmRevMoveWord_computesInTime kIO kWork1 (by decide)
    v1 [] [] (mkTapes8 [] (encodeDelimWord v2.reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil] at h1
  have h2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] (encodeDelimWord v2.reverse) (encodeDelimWord v1.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at h2
  have h3 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
    v2.reverse [] [] [] (mkTapes8 [] [] (encodeDelimWord v1.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h3
  have h4 := tmPrependRevWord_computesInTime kWork1 kIO (by decide)
    v1.reverse (encodeDelimWord v2) [] [] (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h4
  exact h1.seq (h2.seq (h3.seq h4))

/-- **Gadget 30 (`tmPopBitOrZero kSrc kDst`)**:
In a **single `TM2.step` transition** (`|Λ| = 1`), pops one bit from the top delimited word `encodeDelimWord bs`
on `kSrc` (or leaves `encodeDelimWord []` on `kSrc` if `bs = []`) and prepends `bs.headD false`
onto the top delimited word `encodeDelimWord acc` on `kDst`, producing `encodeDelimWord bs.tail`
on `kSrc` and `encodeDelimWord (bs.headD false :: acc)` on `kDst`. -/
def tmPopBitOrZero (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kSrc
      (fun _ bOpt => (default, bOpt.getD true))
      (Turing.TM2.Stmt.pop kSrc
        (fun rv bOpt => ({ rv.1 with bitA := bOpt.getD false }, rv.2))
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.push kSrc (fun _ => false)
            (Turing.TM2.Stmt.push kSrc (fun _ => true)
              (Turing.TM2.Stmt.push kDst (fun _ => false)
                (Turing.TM2.Stmt.push kDst (fun _ => false)
                  (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))))
          (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitA)
            (Turing.TM2.Stmt.push kDst (fun _ => false)
              (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)))))

@[simp]
theorem numLabels_tmPopBitOrZero (kSrc kDst : TapeIdx) :
    (tmPopBitOrZero kSrc kDst).numLabels = 1 := rfl

theorem tmPopBitOrZero_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (bs acc restSrc restDst : List Bool)
    (T : ∀ k : TapeIdx, List (BitTapeAlphabet k)) :
    (tmPopBitOrZero kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc (encodeDelimWord bs ++ restSrc))
        kDst (encodeDelimWord acc ++ restDst))
      (Function.update (Function.update T kSrc (encodeDelimWord bs.tail ++ restSrc))
        kDst (encodeDelimWord (bs.headD false :: acc) ++ restDst))
      1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  cases bs with
  | nil =>
    simp only [tmPopBitOrZero, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, encodeDelimWord_cons,
      List.cons_append, List.nil_append, List.tail_nil, List.headD_nil,
      Function.update_of_ne hne.symm, Function.update_self, Function.update_idem,
      Function.update_comm hne, List.head?_cons, List.tail_cons, Option.getD_some, cond_true]
  | cons b bs' =>
    simp only [tmPopBitOrZero, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons,
      List.cons_append, List.tail_cons, List.headD_cons,
      Function.update_of_ne hne.symm, Function.update_self, Function.update_idem,
      Function.update_comm hne, List.head?_cons, Option.getD_some, cond_false]

/-- One step of `tmPopBitOrZero` on `(bs, acc)`: advances to `(bs.tail, bs.headD false :: acc)`. -/
def popBitStep (st : List Bool × List Bool) : List Bool × List Bool :=
  (st.1.tail, st.1.headD false :: st.2)

/-- Zero-padded prefix of length `b` of `bs : List Bool`, matching `bs.take b` padded with `false`
to length `b` (or `encodeNatBits b (decodeNatBits (bs.take b))`). -/
def takePadBits : ℕ → List Bool → List Bool
  | 0, _ => []
  | b + 1, bs => bs.headD false :: takePadBits b bs.tail

@[simp]
theorem takePadBits_zero (bs : List Bool) : takePadBits 0 bs = [] := rfl

@[simp]
theorem takePadBits_succ (b : ℕ) (bs : List Bool) :
    takePadBits (b + 1) bs = bs.headD false :: takePadBits b bs.tail := rfl

@[simp]
theorem length_takePadBits (b : ℕ) (bs : List Bool) :
    (takePadBits b bs).length = b := by
  induction b generalizing bs with
  | zero => rfl
  | succ b ih => simp [takePadBits, ih]

@[simp]
theorem decodeNatBits_takePadBits (b : ℕ) (bs : List Bool) :
    decodeNatBits (takePadBits b bs) = decodeNatBits (bs.take b) := by
  induction b generalizing bs with
  | zero => simp [takePadBits, decodeNatBits]
  | succ b ih =>
    cases bs with
    | nil => simp [takePadBits, decodeNatBits, ih]
    | cons x xs => simp [takePadBits, decodeNatBits, ih]

@[simp]
theorem encodeNatBits_decodeNatBits_takePadBits (b : ℕ) (bs : List Bool) :
    encodeNatBits b (decodeNatBits (bs.take b)) = takePadBits b bs := by
  rw [← decodeNatBits_takePadBits]
  have h := encodeNatBits_decodeNatBits (takePadBits b bs)
  rwa [length_takePadBits] at h

@[simp]
theorem takePadBits_eq_take_of_le :
    ∀ (b : ℕ) (bs : List Bool), b ≤ bs.length → takePadBits b bs = bs.take b
  | 0, _, _ => rfl
  | b + 1, [], h => by simp at h
  | b + 1, x :: xs, h => by
    simp only [takePadBits_succ, List.headD_cons, List.tail_cons, List.take_succ_cons]
    rw [takePadBits_eq_take_of_le b xs (by simpa using h)]

theorem loopFinalState_popBitStep :
    ∀ (cnt : List Bool) (bs acc : List Bool),
      loopFinalState popBitStep cnt (bs, acc) =
        (bs.drop cnt.length, (takePadBits cnt.length bs).reverse ++ acc)
  | [], bs, acc => by simp [loopFinalState]
  | _ :: cnt, bs, acc => by
    simp only [loopFinalState_cons, popBitStep, List.length_cons, takePadBits_succ,
      List.reverse_cons, List.append_assoc]
    rw [loopFinalState_popBitStep cnt bs.tail (bs.headD false :: acc)]
    congr 1
    cases bs <;> simp

theorem loopStepsAux_popBitStep (cnt : List Bool) (bs acc : List Bool) :
    loopStepsAux popBitStep (fun _ => 1) cnt (bs, acc) = 2 * cnt.length + 1 := by
  induction cnt generalizing bs acc with
  | nil => rfl
  | cons _ cnt ih =>
    simp only [loopStepsAux_cons, List.length_cons, ih]
    ring

/-! ## 3. Compositional Stage Specifications (`ComputesStage`, `ComputesStageLe`, `bmRunRaw`) -/

/-- Exact compositional stage specification: `m : BitMachine` transforms `encodeDelimWord (encA x)`
on `kIO` into `encodeDelimWord (encB (fn x))` on `kIO` in `steps x` steps while preserving
stacks `kWork2..kWork5` and `kSched` (and leaving `kWork0, kWork1` empty). -/
def ComputesStage {α β : Type} (m : BitMachine)
    (encA : α → List Bool) (encB : β → List Bool)
    (fn : α → β) (steps : α → ℕ) : Prop :=
  ∀ (x : α) (tW2 tW3 tW4 tW5 tSch : List Bool),
    m.ComputesInTime
      (mkTapes8 (encodeDelimWord (encA x)) [] [] tW2 tW3 tW4 tW5 tSch)
      (mkTapes8 (encodeDelimWord (encB (fn x))) [] [] tW2 tW3 tW4 tW5 tSch)
      (steps x)

/-- Upper-bounded compositional stage specification: `m : BitMachine` transforms
`encodeDelimWord (encA x)` on `kIO` into `encodeDelimWord (encB (fn x))` on `kIO` in `t ≤ bound x`
steps while preserving stacks `kWork2..kWork5` and `kSched`. -/
def ComputesStageLe {α β : Type} (m : BitMachine)
    (encA : α → List Bool) (encB : β → List Bool)
    (fn : α → β) (bound : α → ℕ) : Prop :=
  ∀ (x : α) (tW2 tW3 tW4 tW5 tSch : List Bool),
    ∃ t ≤ bound x,
      m.ComputesInTime
        (mkTapes8 (encodeDelimWord (encA x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encB (fn x))) [] [] tW2 tW3 tW4 tW5 tSch)
        t

theorem ComputesStage.toLe {α β : Type} {m : BitMachine}
    {encA : α → List Bool} {encB : β → List Bool}
    {fn : α → β} {steps : α → ℕ}
    (h : ComputesStage m encA encB fn steps) :
    ComputesStageLe m encA encB fn steps :=
  fun x tW2 tW3 tW4 tW5 tSch => ⟨steps x, le_rfl, h x tW2 tW3 tW4 tW5 tSch⟩

theorem ComputesStageLe.mono {α β : Type} {m : BitMachine}
    {encA : α → List Bool} {encB : β → List Bool}
    {fn : α → β} {b1 b2 : α → ℕ}
    (h : ComputesStageLe m encA encB fn b1)
    (hle : ∀ x : α, b1 x ≤ b2 x) :
    ComputesStageLe m encA encB fn b2 := by
  intro x tW2 tW3 tW4 tW5 tSch
  rcases h x tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  exact ⟨t, le_trans ht (hle x), hcomp⟩

theorem ComputesStageLe.congr_fn {α β : Type} {m : BitMachine}
    {encA : α → List Bool} {encB : β → List Bool}
    {fn1 fn2 : α → β} {bound : α → ℕ}
    (h : ComputesStageLe m encA encB fn1 bound)
    (heq : ∀ x : α, encB (fn1 x) = encB (fn2 x)) :
    ComputesStageLe m encA encB fn2 bound := by
  intro x tW2 tW3 tW4 tW5 tSch
  rw [← heq x]
  exact h x tW2 tW3 tW4 tW5 tSch

/-- Wrap a delimited-I/O `BitMachine` `m` into a top-level raw-I/O `BitMachine`
(`Turing.initList` $\mapsto$ `Turing.haltList`). -/
def bmRunRaw (m : BitMachine) : BitMachine :=
  (tmRawToDelimRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kIO).seq
      (m.seq tmDelimIOToRawIO))

@[simp]
theorem numLabels_bmRunRaw (m : BitMachine) :
    (bmRunRaw m).numLabels = 2 + (2 + (m.numLabels + 3)) := by
  simp [bmRunRaw, BitMachine.numLabels_seq]

/-- **Top-Level Raw-I/O Execution Theorem (`bmRunRaw_evalsToInTime`)**:
If `ComputesStageLe m id id fn bound`, then for any raw input `xs : List Bool`,
`(bmRunRaw m).toFinTM2` evaluates `Turing.initList _ xs` to `some (Turing.haltList _ (fn xs))`
in `t ≤ bound xs + 2 * xs.length + 2 * (fn xs).length + 7` steps. -/
theorem bmRunRaw_evalsToInTime {m : BitMachine} {fn : List Bool → List Bool}
    {bound : List Bool → ℕ}
    (hm : ComputesStageLe m id id fn bound) (xs : List Bool) :
    ∃ t ≤ bound xs + 2 * xs.length + 2 * (fn xs).length + 7,
      Turing.EvalsToInTime (bmRunRaw m).toFinTM2.step
        (Turing.initList (bmRunRaw m).toFinTM2 xs)
        (some (Turing.haltList (bmRunRaw m).toFinTM2 (fn xs))) t := by
  have h1 := tmRawToDelimRev_computesInTime kIO kWork0 (by decide) xs []
    (mkTapes8 [] [] [] [] [] [] [] [])
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at h1
  have h2 := tmRevMoveWord_computesInTime kWork0 kIO (by decide) xs.reverse [] []
    (mkTapes8 [] [] [] [] [] [] [] [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h2
  rcases hm xs [] [] [] [] [] with ⟨tm, htm, h3⟩
  have h4 := tmDelimIOToRawIO_computesInTime (fn xs)
  have hall := h1.seq (h2.seq (h3.seq h4))
  rw [← initList_stk_eq_mkTapes8 (bmRunRaw m) xs,
    ← haltList_stk_eq_mkTapes8 (bmRunRaw m) (fn xs)] at hall
  rcases hall with ⟨heval⟩
  refine ⟨(xs.length + 2) + ((xs.length + 2) + (tm + (2 * (fn xs).length + 3))), ?_, ⟨heval⟩⟩
  omega

/-! ## 4. Standard Data Encodings & Structural Combinators (`bmId`, `bmSeq`, `bmFst`, `bmSnd`, `bmSwap`, `bmDup`, `bmFanout`, `bmIte`, `bmIterLoop`) -/

/-- Encoding of `Unit` as the empty bit-word `[]`. -/
def encUnit : Unit → List Bool := fun _ => []

/-- Encoding of `Bool` as a 1-bit word `[b]`. -/
def encBool : Bool → List Bool := fun b => [b]

/-- Identity encoding of a bit-word `List Bool`. -/
def encBits : List Bool → List Bool := id

/-- Unary encoding of a natural number `n : ℕ` as `n` `false` bits (`(encUnary n).length = n`). -/
def encUnary (n : ℕ) : List Bool := List.replicate n false

@[simp] theorem length_encUnary (n : ℕ) : (encUnary n).length = n := List.length_replicate

/-- Encoding of a pair `(a, b) : α × β` as a 2-word delimited stack
`encodeDelimWord (encA a) ++ encodeDelimWord (encB b)`. -/
def encPair {α β : Type} (encA : α → List Bool) (encB : β → List Bool) (p : α × β) : List Bool :=
  encodeDelimWord (encA p.1) ++ encodeDelimWord (encB p.2)

@[simp]
theorem length_encPair {α β : Type} (encA : α → List Bool) (encB : β → List Bool) (p : α × β) :
    (encPair encA encB p).length = 2 * (encA p.1).length + 2 * (encB p.2).length + 4 := by
  simp [encPair]
  omega

/-- Encoding of a homogeneous list `xs : List α` as a delimited word-stack
`encodeWordStack (xs.map encElem)`. -/
def encList {α : Type} (encElem : α → List Bool) (xs : List α) : List Bool :=
  encodeWordStack (xs.map encElem)

@[simp]
theorem encList_nil {α : Type} (encElem : α → List Bool) :
    encList encElem ([] : List α) = [] := rfl

@[simp]
theorem encList_cons {α : Type} (encElem : α → List Bool) (x : α) (xs : List α) :
    encList encElem (x :: xs) = encodeDelimWord (encElem x) ++ encList encElem xs := rfl

/-- **Combinator 1 (`bmId`)**: 1-step identity stage on `kIO` (`|Λ| = 1`). -/
def bmId : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ => Turing.TM2.Stmt.halt

@[simp] theorem numLabels_bmId : bmId.numLabels = 1 := rfl

theorem bmId_computesStage {α : Type} (encA : α → List Bool) :
    ComputesStage bmId encA encA id (fun _ => 1) := by
  intro x tW2 tW3 tW4 tW5 tSch
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp [bmId, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux]

theorem bmId_computesStageLe {α : Type} (encA : α → List Bool) :
    ComputesStageLe bmId encA encA id (fun _ => 1) :=
  (bmId_computesStage encA).toLe

/-- **Combinator 2 (`bmConstEmpty`)**: Drops the input word on `kIO` and pushes `encodeDelimWord []`. -/
def bmConstEmpty : BitMachine :=
  (tmDropWord kIO).seq (tmPushEmpty kIO)

theorem bmConstEmpty_computesStageLe {α : Type} (encA : α → List Bool) :
    ComputesStageLe bmConstEmpty encA encUnit (fun _ => ())
      (fun x => (encA x).length + 2) := by
  intro x tW2 tW3 tW4 tW5 tSch
  have h1 := tmDropWord_computesInTime kIO (encA x) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil] at h1
  have h2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at h2
  exact ⟨(encA x).length + 1 + 1, le_rfl, h1.seq h2⟩

/-- **Combinator 3 (`bmSeq m1 m2`)**: Sequential composition `m1.seq m2`. -/
def bmSeq (m1 m2 : BitMachine) : BitMachine :=
  m1.seq m2

@[simp] theorem numLabels_bmSeq (m1 m2 : BitMachine) :
    (bmSeq m1 m2).numLabels = m1.numLabels + m2.numLabels := by
  simp [bmSeq]

theorem bmSeq_computesStageLe {α β γ : Type} {m1 m2 : BitMachine}
    {encA : α → List Bool} {encB : β → List Bool} {encC : γ → List Bool}
    {f : α → β} {g : β → γ} {b1 : α → ℕ} {b2 : β → ℕ}
    (h1 : ComputesStageLe m1 encA encB f b1)
    (h2 : ComputesStageLe m2 encB encC g b2) :
    ComputesStageLe (bmSeq m1 m2) encA encC (fun x => g (f x))
      (fun x => b1 x + b2 (f x)) := by
  intro x tW2 tW3 tW4 tW5 tSch
  rcases h1 x tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, hc1⟩
  rcases h2 (f x) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, hc2⟩
  exact ⟨t1 + t2, Nat.add_le_add ht1 ht2, hc1.seq hc2⟩

/-- **Combinator 4 (`bmFst`)**: Extracts the first component `p.1` from `encPair encA encB p` on `kIO`. -/
def bmFst : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmDropWord kIO).seq
      (tmRevMoveWord kWork0 kIO))

theorem bmFst_computesStageLe {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ComputesStageLe bmFst (encPair encA encB) encA Prod.fst
      (fun p => 2 * (encA p.1).length + 2 * (encB p.2).length + 7) := by
  intro p tW2 tW3 tW4 tW5 tSch
  dsimp only
  have h1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encA p.1) ++ encodeDelimWord (encB p.2)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at h1
  have h2 := tmDropWord_computesInTime kIO (encodeDelimWord (encB p.2)) []
    (mkTapes8 [] (encodeDelimWord (encA p.1).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, length_encodeDelimWord] at h2
  have h3 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encA p.1).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h3
  refine ⟨_, ?_, h1.seq (h2.seq h3)⟩
  omega

/-- **Combinator 5 (`bmSnd`)**: Extracts the second component `p.2` from `encPair encA encB p` on `kIO`. -/
def bmSnd : BitMachine :=
  (tmTailWords kIO).seq
    ((tmPopFirstSubwordRev kIO kWork0).seq
      ((tmDropWord kIO).seq
        (tmRevMoveWord kWork0 kIO)))

theorem bmSnd_computesStageLe {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ComputesStageLe bmSnd (encPair encA encB) encB Prod.snd
      (fun p => (encA p.1).length + 2 * (encB p.2).length + 6) := by
  intro p tW2 tW3 tW4 tW5 tSch
  dsimp only
  have h1 := tmTailWords_computesInTime kIO
    (encodeDelimWord (encA p.1) ++ encodeDelimWord (encB p.2)) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at h1
  have h2 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encB p.2)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at h2
  have h3 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encB p.2).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at h3
  have h4 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encB p.2).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h4
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq h4))⟩
  omega

/-- **Combinator 6 (`bmDup`)**: Duplicates `encodeDelimWord (encA x)` on `kIO` into
`encodeDelimWord (encPair encA encA (x, x))` on `kIO`. -/
def bmDup : BitMachine :=
  (tmRevDupWord kIO kWork0 kWork1).seq
    ((tmPushEmpty kIO).seq
      ((tmPrependRevWord kWork1 kIO).seq
        (tmPrependRevWord kWork0 kIO)))

theorem bmDup_computesStageLe {α : Type} (encA : α → List Bool) :
    ComputesStageLe bmDup encA (encPair encA encA) (fun x => (x, x))
      (fun x => 3 * (encA x).length + 7) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  have h1 := tmRevDupWord_computesInTime kIO kWork0 kWork1 (by decide) (by decide) (by decide)
    (encA x) [] [] [] (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
    List.append_nil] at h1
  have h2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] (encodeDelimWord (encA x).reverse) (encodeDelimWord (encA x).reverse)
      tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at h2
  have h3 := tmPrependRevWord_computesInTime kWork1 kIO (by decide)
    (encA x).reverse [] [] []
    (mkTapes8 [] (encodeDelimWord (encA x).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h3
  have h4 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
    (encA x).reverse (encodeDelimWord (encA x)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h4
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq h4))⟩
  omega

/-- **Combinator 7 (`bmFanout m1 m2`)**: Evaluates `m1` and `m2` on the same input `x : α` and
packs their outputs into `encPair encB encC (f x, g x)` on `kIO`. -/
def bmFanout (m1 m2 : BitMachine) : BitMachine :=
  (tmDupWord kIO kWork0 kWork5).seq
    (m1.seq
      ((tmRevMoveWord kIO kWork4).seq
        ((tmMoveWord kWork5 kWork0 kIO).seq
          (m2.seq
            ((tmMoveWord kWork4 kWork1 kWork0).seq tmPackPairFromRev)))))

theorem bmFanout_computesStageLe {α β γ : Type} {m1 m2 : BitMachine}
    {encA : α → List Bool} {encB : β → List Bool} {encC : γ → List Bool}
    {f : α → β} {g : α → γ} {b1 b2 : α → ℕ}
    (h1 : ComputesStageLe m1 encA encB f b1)
    (h2 : ComputesStageLe m2 encA encC g b2) :
    ComputesStageLe (bmFanout m1 m2) encA (encPair encB encC) (fun x => (f x, g x))
      (fun x => b1 x + b2 x + 4 * (encA x).length + 4 * (encB (f x)).length +
        2 * (encC (g x)).length + 21) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmDupWord_computesInTime kIO kWork0 kWork5 (by decide) (by decide) (by decide)
    (encA x) [] [] tW5 (mkTapes8 [] [] [] tW2 tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork5,
    List.append_nil] at s1
  rcases h1 x tW2 tW3 tW4 (encodeDelimWord (encA x) ++ tW5) tSch with ⟨t1, ht1, s2⟩
  have s3 := tmRevMoveWord_computesInTime kIO kWork4 (by decide)
    (encB (f x)) [] tW4
    (mkTapes8 [] [] [] tW2 tW3 [] (encodeDelimWord (encA x) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork4, List.append_nil] at s3
  have s4 := tmMoveWord_computesInTime kWork5 kWork0 kIO (by decide) (by decide) (by decide)
    (encA x) tW5 [] []
    (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord (encB (f x)).reverse ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s4
  rcases h2 x tW2 tW3 (encodeDelimWord (encB (f x)).reverse ++ tW4) tW5 tSch with ⟨t2, ht2, s5⟩
  have s6 := tmMoveWord_computesInTime kWork4 kWork1 kWork0 (by decide) (by decide) (by decide)
    (encB (f x)).reverse tW4 [] []
    (mkTapes8 (encodeDelimWord (encC (g x))) [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
    List.length_reverse, List.append_nil] at s6
  have s7 := tmPackPairFromRev_computesInTime (encB (f x)) (encC (g x)) tW2 tW3 tW4 tW5 tSch
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))⟩
  omega

/-- **Combinator 8 (`bmPairMap m1 m2`)**: Maps `m1` on `p.1` and `m2` on `p.2` for a pair
`encPair encA1 encA2 p` on `kIO`. -/
def bmPairMap (m1 m2 : BitMachine) : BitMachine :=
  bmFanout (bmSeq bmFst m1) (bmSeq bmSnd m2)

theorem bmPairMap_computesStageLe {α1 α2 β1 β2 : Type} {m1 m2 : BitMachine}
    {encA1 : α1 → List Bool} {encA2 : α2 → List Bool}
    {encB1 : β1 → List Bool} {encB2 : β2 → List Bool}
    {f1 : α1 → β1} {f2 : α2 → β2} {b1 : α1 → ℕ} {b2 : α2 → ℕ}
    (h1 : ComputesStageLe m1 encA1 encB1 f1 b1)
    (h2 : ComputesStageLe m2 encA2 encB2 f2 b2) :
    ComputesStageLe (bmPairMap m1 m2) (encPair encA1 encA2) (encPair encB1 encB2)
      (fun p => (f1 p.1, f2 p.2))
      (fun p => b1 p.1 + b2 p.2 + 11 * (encA1 p.1).length + 12 * (encA2 p.2).length +
        4 * (encB1 (f1 p.1)).length + 2 * (encB2 (f2 p.2)).length + 50) := by
  have hf1 := bmSeq_computesStageLe (bmFst_computesStageLe encA1 encA2) h1
  have hf2 := bmSeq_computesStageLe (bmSnd_computesStageLe encA1 encA2) h2
  refine (bmFanout_computesStageLe hf1 hf2).mono (fun p => ?_)
  simp only [length_encPair]
  omega

/-- **Combinator 9 (`bmSwap`)**: Swaps `encPair encA encB (a, b)` into `encPair encB encA (b, a)`. -/
def bmSwap : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmPopFirstSubwordRev kIO kWork1).seq
      ((tmPrependRevWord kWork0 kIO).seq
        (tmPrependRevWord kWork1 kIO)))

theorem bmSwap_computesStageLe {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ComputesStageLe bmSwap (encPair encA encB) (encPair encB encA) Prod.swap
      (fun p => 2 * (encA p.1).length + 2 * (encB p.2).length + 8) := by
  intro p tW2 tW3 tW4 tW5 tSch
  dsimp only
  have h1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encA p.1) ++ encodeDelimWord (encB p.2)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at h1
  have h2 := tmPopFirstSubwordRev_computesInTime kIO kWork1 (by decide)
    (encodeDelimWord (encB p.2)) [] []
    (mkTapes8 [] (encodeDelimWord (encA p.1).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
    unconsDelimWord_encodeDelimWord] at h2
  have h3 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
    (encA p.1).reverse [] [] []
    (mkTapes8 [] [] (encodeDelimWord (encB p.2).reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h3
  have h4 := tmPrependRevWord_computesInTime kWork1 kIO (by decide)
    (encB p.2).reverse (encodeDelimWord (encA p.1)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h4
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq h4))⟩
  omega

/-- **Combinator 10 (`bmIte mCond mTrue mFalse`)**: Evaluates `mCond` on `x` to produce a boolean
`encBool (cond x)`, then executes `mTrue` on `x` if `cond x = true` and `mFalse` on `x` otherwise. -/
def bmIte (mCond mTrue mFalse : BitMachine) : BitMachine :=
  (tmDupWord kIO kWork0 kWork5).seq
    (mCond.seq
      ((tmMoveWord kIO kWork0 kWork4).seq
        ((tmMoveWord kWork5 kWork0 kIO).seq
          (BitMachine.branchDelimBit kWork4 mFalse mTrue))))

theorem bmIte_computesStageLe {α β : Type} {mCond mTrue mFalse : BitMachine}
    {encA : α → List Bool} {encB : β → List Bool}
    {condFn : α → Bool} {fTrue fFalse : α → β}
    {bCond bTrue bFalse : α → ℕ}
    (hCond : ComputesStageLe mCond encA encBool condFn bCond)
    (hTrue : ComputesStageLe mTrue encA encB fTrue bTrue)
    (hFalse : ComputesStageLe mFalse encA encB fFalse bFalse) :
    ComputesStageLe (bmIte mCond mTrue mFalse) encA encB
      (fun x => if condFn x then fTrue x else fFalse x)
      (fun x => bCond x + (if condFn x then bTrue x else bFalse x) +
        4 * (encA x).length + 15) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmDupWord_computesInTime kIO kWork0 kWork5 (by decide) (by decide) (by decide)
    (encA x) [] [] tW5 (mkTapes8 [] [] [] tW2 tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork5,
    List.append_nil] at s1
  rcases hCond x tW2 tW3 tW4 (encodeDelimWord (encA x) ++ tW5) tSch with ⟨tC, htC, s2⟩
  have s3 := tmMoveWord_computesInTime kIO kWork0 kWork4 (by decide) (by decide) (by decide)
    (encBool (condFn x)) [] [] tW4
    (mkTapes8 [] [] [] tW2 tW3 [] (encodeDelimWord (encA x) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork4,
    List.append_nil] at s3
  have s4 := tmMoveWord_computesInTime kWork5 kWork0 kIO (by decide) (by decide) (by decide)
    (encA x) tW5 [] []
    (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord (encBool (condFn x)) ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s4
  cases hcf : condFn x with
  | false =>
    rcases hFalse x tW2 tW3 tW4 tW5 tSch with ⟨tF, htF, sF⟩
    have s5 := BitMachine.ComputesInTime.branchDelimBit kWork4
      (M_false := mFalse) (M_true := mTrue) false tW4
      (T₁ := mkTapes8 (encodeDelimWord (encA x)) [] [] tW2 tW3 [] tW5 tSch)
      (by simpa [update_mkTapes8_kWork4] using sF)
    simp only [update_mkTapes8_kWork4] at s5
    simp only [hcf, encBool, Bool.false_eq_true, ↓reduceIte] at s2 s3 s4 ⊢
    refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq s5)))⟩
    simp only [List.length_singleton]
    omega
  | true =>
    rcases hTrue x tW2 tW3 tW4 tW5 tSch with ⟨tT, htT, sT⟩
    have s5 := BitMachine.ComputesInTime.branchDelimBit kWork4
      (M_false := mFalse) (M_true := mTrue) true tW4
      (T₁ := mkTapes8 (encodeDelimWord (encA x)) [] [] tW2 tW3 [] tW5 tSch)
      (by simpa [update_mkTapes8_kWork4] using sT)
    simp only [update_mkTapes8_kWork4] at s5
    simp only [hcf, encBool, ↓reduceIte] at s2 s3 s4 ⊢
    refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq s5)))⟩
    simp only [List.length_singleton]
    omega

/-- **Combinator 11 (`bmIterLoop body`)**:
Consumes `encPair encUnary encA (k, st0)` on `kIO`, iterates `body` `k` times on `kIO` (using
`kSched` for the unary counter `encUnary k`), and leaves `encodeDelimWord (encA (step^[k] st0))`
on `kIO`. -/
def bmIterLoop (body : BitMachine) : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kSched).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kIO).seq
            (body.loopDelimWord kSched)))))

theorem loopFinalState_replicate_eq_iterate {α : Type} (step : α → α) :
    ∀ (k : ℕ) (b : Bool) (st : α),
      loopFinalState step (List.replicate k b) st = step^[k] st
  | 0, _, st => rfl
  | k + 1, b, st => by
    simp only [List.replicate_succ, loopFinalState_cons, Function.iterate_succ_apply]
    exact loopFinalState_replicate_eq_iterate step k b (step st)

theorem bmIterLoop_computesStageLe {α : Type} {body : BitMachine}
    {encA : α → List Bool} {step : α → α} {bStep : α → ℕ}
    (hbody : ComputesStageLe body encA encA step bStep) :
    ComputesStageLe (bmIterLoop body) (encPair encUnary encA) encA
      (fun p => step^[p.1] p.2)
      (fun p => loopStepsAux step bStep (encUnary p.1) p.2 +
        2 * p.1 + 2 * (encA p.2).length + 9) := by
  intro ⟨k, st0⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary k) ++ encodeDelimWord (encA st0)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kSched (by decide)
    (encUnary k).reverse [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encA st0))) [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kSched, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encA st0)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary k) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encA st0).reverse) [] tW2 tW3 tW4 tW5
      (encodeDelimWord (encUnary k) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encA st0).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary k) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  let stkOf : α → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 (encodeDelimWord (encA st)) [] [] tW2 tW3 tW4 tW5 []
  rcases BitMachine.ComputesInTime.loopDelimWord_state_le kSched step bStep stkOf
    (fun st tailSch => by
      dsimp only [stkOf]
      simp only [update_mkTapes8_kSched]
      exact hbody st tW2 tW3 tW4 tW5 tailSch)
    (encUnary k) tSch st0 with ⟨tL, htL, s6⟩
  dsimp only [stkOf] at s6
  simp only [update_mkTapes8_kSched, encUnary, loopFinalState_replicate_eq_iterate] at s6
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))⟩
  simp only [encUnary, List.length_replicate] at s1 s2 htL ⊢
  omega

/-! ## 5. Linear-Time List Combinators (`bmRevList`, `bmFoldList`, `bmMapWithCtx`, `bmAppendList`) -/

/-- **Combinator 12 (`bmRevList`)**: Reverses an encoded list `encList encElem xs` on `kIO` into
`encList encElem xs.reverse` in **strictly linear** $O(\sum |e|)$ `TM2.step` transitions using `loopNonEmptyWord`. -/
def bmRevList : BitMachine :=
  (tmMoveWord kIO kWork0 kWork2).seq
    ((tmPushEmpty kWork3).seq
      ((((tmPopFirstSubwordRev kWork2 kWork0).seq
          (tmPrependRevWord kWork0 kWork3)).loopNonEmptyWord kWork2).seq
        (tmMoveWord kWork3 kWork0 kIO)))

theorem loopListFinalState_revAux {α : Type} (encElem : α → List Bool) :
    ∀ (xs : List α) (acc : List Bool),
      loopListFinalState (fun x s => encodeDelimWord (encElem x) ++ s) xs acc =
        encList encElem xs.reverse ++ acc
  | [], acc => by simp [loopListFinalState, encList]
  | x :: xs, acc => by
    simp only [loopListFinalState_cons, List.reverse_cons, List.map_append, List.map_singleton,
      encList, encodeWordStack_append, encodeWordStack_cons, encodeWordStack_nil,
      List.append_nil, List.append_assoc]
    exact loopListFinalState_revAux encElem xs (encodeDelimWord (encElem x) ++ acc)

theorem loopListStepsAux_revAux_le {α : Type} (encElem : α → List Bool) :
    ∀ (xs : List α) (acc : List Bool),
      loopListStepsAux (fun x s => encodeDelimWord (encElem x) ++ s)
        (fun x _ _ => 2 * (encElem x).length + 4) xs acc ≤
        3 * (encList encElem xs).length + 1
  | [], _ => by simp [loopListStepsAux]
  | x :: xs, acc => by
    simp only [loopListStepsAux_cons, encList_cons, List.length_append, length_encodeDelimWord]
    have ih := loopListStepsAux_revAux_le encElem xs (encodeDelimWord (encElem x) ++ acc)
    omega

theorem length_encList_reverse {α : Type} (encElem : α → List Bool) (xs : List α) :
    (encList encElem xs.reverse).length = (encList encElem xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, encList, List.map_append, List.map_cons, List.map_nil,
      encodeWordStack_append, encodeWordStack_cons, encodeWordStack_nil,
      List.length_append, List.length_nil] at ih ⊢
    omega

theorem bmRevList_computesStageLe {α : Type} (encElem : α → List Bool) :
    ComputesStageLe bmRevList (encList encElem) (encList encElem) List.reverse
      (fun xs => 7 * (encList encElem xs).length + 12) := by
  intro xs tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmMoveWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
    (encList encElem xs) [] [] tW2 (mkTapes8 [] [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
    List.append_nil] at s1
  have s2 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s2
  let nextSt : α → List Bool → List Bool := fun x acc => encodeDelimWord (encElem x) ++ acc
  let stepBound : α → List α → List Bool → ℕ := fun x _ _ => 2 * (encElem x).length + 4
  let stkOf : List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun acc =>
    mkTapes8 [] [] [] [] (encodeDelimWord acc ++ tW3) tW4 tW5 tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encElem nextSt stepBound stkOf
    (fun x rem acc restW2 => by
      dsimp only [stkOf, nextSt, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encElem x) ++ encodeWordStack (rem.map encElem)) restW2 []
        (mkTapes8 [] [] [] [] (encodeDelimWord acc ++ tW3) tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmPrependRevWord_computesInTime kWork0 kWork3 (by decide)
        (encElem x).reverse acc [] tW3
        (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2) [] tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2
      exact ⟨_, by omega, b1.seq b2⟩)
    xs tW2 [] with ⟨tL, htL, s3⟩
  dsimp only [stkOf, nextSt] at s3
  simp only [update_mkTapes8_kWork2] at s3
  rw [loopListFinalState_revAux, List.append_nil] at s3
  have s4 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encList encElem xs.reverse) tW3 [] []
    (mkTapes8 [] [] [] tW2 [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s4
  have hbound := loopListStepsAux_revAux_le encElem xs []
  have hlen := length_encList_reverse encElem xs
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq s4))⟩
  dsimp only [nextSt, stepBound] at htL
  omega

/-- **Combinator 13 (`bmFoldList stepM`)**:
Consumes `encPair (encList encElem) encAcc (xs, acc0)` on `kIO` and folds `stepM`
(`encPair encElem encAcc (x, acc) ↦ encAcc (stepFn (x, acc))`) across `xs` in **strictly linear**
time using `loopNonEmptyWord` and `tmPackPairFromRev`. -/
def bmFoldList (stepM : BitMachine) : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork2).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kIO).seq
            (((tmPopFirstSubwordRev kWork2 kWork0).seq
                (tmPackPairFromRev.seq stepM)).loopNonEmptyWord kWork2)))))

theorem loopListFinalState_foldl {α β : Type} (f : α × β → β) :
    ∀ (xs : List α) (acc : β),
      loopListFinalState (fun x a => f (x, a)) xs acc =
        xs.foldl (fun a x => f (x, a)) acc
  | [], _ => rfl
  | x :: xs, acc => loopListFinalState_foldl f xs (f (x, acc))

theorem bmFoldList_computesStageLe {α β : Type} {stepM : BitMachine}
    {encElem : α → List Bool} {encAcc : β → List Bool}
    {stepFn : α × β → β} {bStep : α × β → ℕ}
    (hstep : ComputesStageLe stepM (encPair encElem encAcc) encAcc stepFn bStep) :
    ComputesStageLe (bmFoldList stepM) (encPair (encList encElem) encAcc) encAcc
      (fun p => p.1.foldl (fun a x => stepFn (x, a)) p.2)
      (fun p =>
        loopListStepsAux (fun x a => stepFn (x, a))
          (fun x _ a => bStep (x, a) + 2 * (encElem x).length + 2 * (encAcc a).length + 9) p.1 p.2 +
        2 * (encList encElem p.1).length + 2 * (encAcc p.2).length + 9) := by
  intro ⟨xs, acc0⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encElem xs) ++ encodeDelimWord (encAcc acc0)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encElem xs).reverse [] tW2
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encAcc acc0))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encAcc acc0)) [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encAcc acc0).reverse) []
      (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encAcc acc0).reverse [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  let nextSt : α → β → β := fun x a => stepFn (x, a)
  let stepBound : α → List α → β → ℕ :=
    fun x _ a => bStep (x, a) + 2 * (encElem x).length + 2 * (encAcc a).length + 9
  let stkOf : β → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun a =>
    mkTapes8 (encodeDelimWord (encAcc a)) [] [] [] tW3 tW4 tW5 tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encElem nextSt stepBound stkOf
    (fun x rem a restW2 => by
      dsimp only [stkOf, nextSt, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encElem x) ++ encodeWordStack (rem.map encElem)) restW2 []
        (mkTapes8 (encodeDelimWord (encAcc a)) [] [] [] tW3 tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmPackPairFromRev_computesInTime (encElem x) (encAcc a)
        (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2) tW3 tW4 tW5 tSch
      rcases hstep (x, a) (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2) tW3 tW4 tW5 tSch
        with ⟨ts, hts, b3⟩
      refine ⟨_, ?_, b1.seq (b2.seq b3)⟩
      omega)
    xs tW2 acc0 with ⟨tL, htL, s6⟩
  dsimp only [stkOf, nextSt, stepBound] at htL s6
  simp only [update_mkTapes8_kWork2] at s6
  rw [loopListFinalState_foldl] at s6
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))⟩
  omega

/-- **Combinator 14 (`bmAppendList`)**:
Consumes `encPair (encList encElem) (encList encElem) (xs, ys)` on `kIO` and produces
`encList encElem (xs ++ ys)` on `kIO` in linear $O(\sum |x| + \sum |y|)$ `TM2.step` transitions
(reversing `xs` onto `kWork3` and prepending each element onto `encList encElem ys` on `kIO`
without rescanning `ys`). -/
def bmAppendList : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork2).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kIO).seq
            ((tmPushEmpty kWork3).seq
              ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                  (tmPrependRevWord kWork0 kWork3)).loopNonEmptyWord kWork2).seq
                (((tmPopFirstSubwordRev kWork3 kWork0).seq
                    (tmPrependRevWord kWork0 kIO)).loopNonEmptyWord kWork3)))))))

theorem bmAppendList_computesStageLe {α : Type} (encElem : α → List Bool) :
    ComputesStageLe bmAppendList
      (encPair (encList encElem) (encList encElem)) (encList encElem)
      (fun p => p.1 ++ p.2)
      (fun p => 8 * (encList encElem p.1).length + 2 * (encList encElem p.2).length + 14) := by
  intro ⟨xs, ys⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encElem xs) ++ encodeDelimWord (encList encElem ys)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encElem xs).reverse [] tW2
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encElem ys))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encElem ys)) [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encElem ys).reverse) []
      (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encList encElem ys).reverse [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 (encodeDelimWord (encList encElem ys)) [] []
      (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s6
  let nextSt : α → List Bool → List Bool := fun x acc => encodeDelimWord (encElem x) ++ acc
  let stepBound : α → List α → List Bool → ℕ := fun x _ _ => 2 * (encElem x).length + 4
  let stkOf1 : List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun acc =>
    mkTapes8 (encodeDelimWord (encList encElem ys)) [] [] [] (encodeDelimWord acc ++ tW3) tW4 tW5 tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encElem nextSt stepBound stkOf1
    (fun x rem acc restW2 => by
      dsimp only [stkOf1, nextSt, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encElem x) ++ encodeWordStack (rem.map encElem)) restW2 []
        (mkTapes8 (encodeDelimWord (encList encElem ys)) [] [] []
          (encodeDelimWord acc ++ tW3) tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmPrependRevWord_computesInTime kWork0 kWork3 (by decide)
        (encElem x).reverse acc [] tW3
        (mkTapes8 (encodeDelimWord (encList encElem ys)) [] []
          (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2) [] tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2
      exact ⟨_, by omega, b1.seq b2⟩)
    xs tW2 [] with ⟨tL1, htL1, s7⟩
  dsimp only [stkOf1, nextSt, stepBound] at htL1 s7
  simp only [update_mkTapes8_kWork2] at s7
  rw [loopListFinalState_revAux, List.append_nil] at s7
  let stkOf2 : List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun acc =>
    mkTapes8 (encodeDelimWord acc) [] [] tW2 [] tW4 tW5 tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork3 encElem nextSt stepBound stkOf2
    (fun x rem acc restW3 => by
      dsimp only [stkOf2, nextSt, stepBound]
      simp only [update_mkTapes8_kWork3]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork3 kWork0 (by decide)
        (encodeDelimWord (encElem x) ++ encodeWordStack (rem.map encElem)) restW3 []
        (mkTapes8 (encodeDelimWord acc) [] [] tW2 [] tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
        (encElem x).reverse acc [] []
        (mkTapes8 [] [] [] tW2
          (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW3) tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2
      exact ⟨_, by omega, b1.seq b2⟩)
    xs.reverse tW3 (encList encElem ys) with ⟨tL2, htL2, s8⟩
  dsimp only [stkOf2, nextSt, stepBound] at htL2 s8
  simp only [update_mkTapes8_kWork3] at s8
  have hfinal : loopListFinalState (fun x s => encodeDelimWord (encElem x) ++ s)
      xs.reverse (encList encElem ys) = encList encElem (xs ++ ys) := by
    rw [loopListFinalState_revAux, List.reverse_reverse]
    simp [encList, List.map_append, encodeWordStack_append]
  rw [hfinal] at s8
  have hb1 := loopListStepsAux_revAux_le encElem xs []
  have hb2 := loopListStepsAux_revAux_le encElem xs.reverse (encList encElem ys)
  rw [length_encList_reverse] at hb2
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq s8))))))⟩
  omega

/-- **Combinator 15 (`bmMapWithCtx bodyM`)**:
Consumes `encPair encCtx (encList encA) (ctx, xs)` on `kIO`, maps `bodyM`
(`encPair encCtx encA (ctx, x) ↦ encB (fn (ctx, x))`) across every `x ∈ xs`, and emits
`encList encB (xs.map (fun x => fn (ctx, x)))` on `kIO` in linear time. -/
def bmMapWithCtx (bodyM : BitMachine) : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork5).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kWork2).seq
            ((tmPushEmpty kWork3).seq
              ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                  ((tmDupWord kWork5 kWork1 kIO).seq
                    (tmPackPairFromRevSwapped.seq
                      (bodyM.seq
                        ((tmRevMoveWord kIO kWork0).seq
                          (tmPrependRevWord kWork0 kWork3)))))).loopNonEmptyWord kWork2).seq
                ((tmDropWord kWork5).seq
                  ((tmMoveWord kWork3 kWork0 kIO).seq bmRevList))))))))

theorem loopListFinalState_mapRev {α β : Type} (f : α → β) :
    ∀ (xs : List α) (acc : List β),
      loopListFinalState (fun x a => f x :: a) xs acc =
        (xs.map f).reverse ++ acc
  | [], acc => by simp [loopListFinalState]
  | x :: xs, acc => by
    simp only [loopListFinalState_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    exact loopListFinalState_mapRev f xs (f x :: acc)

theorem bmMapWithCtx_computesStageLe {γ α β : Type} {bodyM : BitMachine}
    {encCtx : γ → List Bool} {encA : α → List Bool} {encB : β → List Bool}
    {fn : γ × α → β} {bBody : γ × α → ℕ}
    (hbody : ComputesStageLe bodyM (encPair encCtx encA) encB fn bBody) :
    ComputesStageLe (bmMapWithCtx bodyM) (encPair encCtx (encList encA)) (encList encB)
      (fun p => p.2.map (fun x => fn (p.1, x)))
      (fun p =>
        loopListStepsAux (fun x (a : List β) => fn (p.1, x) :: a)
          (fun x _ _ =>
            bBody (p.1, x) + 4 * (encCtx p.1).length + 2 * (encA x).length +
              2 * (encB (fn (p.1, x))).length + 17)
          p.2 [] +
        3 * (encCtx p.1).length + 2 * (encList encA p.2).length +
        9 * (encList encB (p.2.map (fun x => fn (p.1, x)))).length + 27) := by
  intro ⟨ctx, xs⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encCtx ctx) ++ encodeDelimWord (encList encA xs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork5 (by decide)
    (encCtx ctx).reverse [] tW5
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encA xs))) [] [] tW2 tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork5, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encA xs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 (encodeDelimWord (encCtx ctx) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encA xs).reverse) [] tW2 tW3 tW4
      (encodeDelimWord (encCtx ctx) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encA xs).reverse [] tW2
    (mkTapes8 [] [] [] [] tW3 tW4 (encodeDelimWord (encCtx ctx) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encA xs) ++ tW2) tW3 tW4
      (encodeDelimWord (encCtx ctx) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s6
  let nextSt : α → List β → List β := fun x a => fn (ctx, x) :: a
  let stepBound : α → List α → List β → ℕ :=
    fun x _ _ =>
      bBody (ctx, x) + 4 * (encCtx ctx).length + 2 * (encA x).length +
        2 * (encB (fn (ctx, x))).length + 17
  let stkOf : List β → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun a =>
    mkTapes8 [] [] [] [] (encodeDelimWord (encList encB a) ++ tW3) tW4
      (encodeDelimWord (encCtx ctx) ++ tW5) tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encA nextSt stepBound stkOf
    (fun x rem a restW2 => by
      dsimp only [stkOf, nextSt, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encA x) ++ encodeWordStack (rem.map encA)) restW2 []
        (mkTapes8 [] [] [] [] (encodeDelimWord (encList encB a) ++ tW3) tW4
          (encodeDelimWord (encCtx ctx) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmDupWord_computesInTime kWork5 kWork1 kIO (by decide) (by decide) (by decide)
        (encCtx ctx) tW5 [] []
        (mkTapes8 [] (encodeDelimWord (encA x).reverse) []
          (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
          (encodeDelimWord (encList encB a) ++ tW3) tW4 [] tSch)
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork1, update_mkTapes8_kIO,
        List.append_nil] at b2
      have b3 := tmPackPairFromRevSwapped_computesInTime (encCtx ctx) (encA x)
        (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
        (encodeDelimWord (encList encB a) ++ tW3) tW4
        (encodeDelimWord (encCtx ctx) ++ tW5) tSch
      rcases hbody (ctx, x)
        (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
        (encodeDelimWord (encList encB a) ++ tW3) tW4
        (encodeDelimWord (encCtx ctx) ++ tW5) tSch with ⟨tb, htb, b4⟩
      have b5 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
        (encB (fn (ctx, x))) [] []
        (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
          (encodeDelimWord (encList encB a) ++ tW3) tW4
          (encodeDelimWord (encCtx ctx) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at b5
      have b6 := tmPrependRevWord_computesInTime kWork0 kWork3 (by decide)
        (encB (fn (ctx, x))).reverse (encList encB a) [] tW3
        (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encA)) ++ restW2)
          [] tW4 (encodeDelimWord (encCtx ctx) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b6
      refine ⟨_, ?_, b1.seq (b2.seq (b3.seq (b4.seq (b5.seq b6))))⟩
      omega)
    xs tW2 [] with ⟨tL, htL, s7⟩
  dsimp only [stkOf, nextSt, stepBound] at htL s7
  simp only [update_mkTapes8_kWork2, encList_nil] at s6 s7
  rw [loopListFinalState_mapRev, List.append_nil] at s7
  have s8 := tmDropWord_computesInTime kWork5 (encCtx ctx) tW5
    (mkTapes8 [] [] [] tW2
      (encodeDelimWord (encList encB (xs.map (fun x => fn (ctx, x))).reverse) ++ tW3)
      tW4 [] tSch)
  simp only [update_mkTapes8_kWork5] at s8
  have s9 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encList encB (xs.map (fun x => fn (ctx, x))).reverse) tW3 [] []
    (mkTapes8 [] [] [] tW2 [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s9
  rcases bmRevList_computesStageLe encB (xs.map (fun x => fn (ctx, x))).reverse
    tW2 tW3 tW4 tW5 tSch with ⟨tR, htR, s10⟩
  dsimp only at htR
  simp only [List.reverse_reverse] at s10
  have hlen_rev := length_encList_reverse encB (xs.map (fun x => fn (ctx, x)))
  simp only [hlen_rev] at s9 htR ⊢
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq s10))))))))⟩
  omega

/-! ## 6. $O(b)$ Head-Slicing Stage (`bmSliceDropBits`, `bmTakePadBits`, `bmDropBits`) -/

/-- **Stage 16 (`bmSliceDropBits`)**:
Consumes `encPair encUnary encBits (b, bs)` on `kIO`, slices `bs` at bit-offset `b` by looping
`tmPopBitOrZero kIO kWork3` `b` times over `encUnary b` on `kSched` (and then packing
`(takePadBits b bs, bs.drop b)` onto `kIO`). -/
def bmSliceDropBits : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kSched).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kIO).seq
            ((tmPushEmpty kWork3).seq
              (((tmPopBitOrZero kIO kWork3).loopDelimWord kSched).seq
                ((tmMoveWord kWork3 kWork1 kWork0).seq tmPackPairFromRev)))))))

theorem bmSliceDropBits_computesStageLe :
    ComputesStageLe bmSliceDropBits (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => (takePadBits p.1 p.2, p.2.drop p.1))
      (fun p => 7 * p.1 + 4 * p.2.length + 22) := by
  intro ⟨b, bs⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary b) ++ encodeDelimWord bs) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kSched (by decide)
    (encUnary b).reverse [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord bs)) [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kSched, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord bs) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary b) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord bs.reverse) [] tW2 tW3 tW4 tW5
      (encodeDelimWord (encUnary b) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    bs.reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary b) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 (encodeDelimWord bs) [] [] tW2 tW3 tW4 tW5
      (encodeDelimWord (encUnary b) ++ tSch))
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s6
  let stkOf : List Bool × List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 (encodeDelimWord st.1) [] [] tW2 (encodeDelimWord st.2 ++ tW3) tW4 tW5 []
  have hloop := BitMachine.ComputesInTime.loopDelimWord_state kSched popBitStep (fun _ => 1) stkOf
    (fun st tailSch => by
      dsimp only [stkOf, popBitStep]
      simp only [update_mkTapes8_kSched]
      have hp := tmPopBitOrZero_computesInTime kIO kWork3 (by decide)
        st.1 st.2 [] tW3 (mkTapes8 [] [] [] tW2 [] tW4 tW5 tailSch)
      simpa only [update_mkTapes8_kIO, update_mkTapes8_kWork3, List.append_nil] using hp)
    (encUnary b) tSch (bs, [])
  dsimp only [stkOf] at hloop
  simp only [update_mkTapes8_kSched, List.append_nil, loopFinalState_popBitStep,
    loopStepsAux_popBitStep, length_encUnary] at hloop
  have s7 := tmMoveWord_computesInTime kWork3 kWork1 kWork0 (by decide) (by decide) (by decide)
    (takePadBits b bs).reverse tW3 [] []
    (mkTapes8 (encodeDelimWord (bs.drop b)) [] [] tW2 [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
    List.length_reverse, length_takePadBits, List.append_nil] at s7
  have s8 := tmPackPairFromRev_computesInTime (takePadBits b bs) (bs.drop b)
    tW2 tW3 tW4 tW5 tSch
  simp only [length_takePadBits] at s8
  have hdrop_len : (bs.drop b).length ≤ bs.length := by simp [List.length_drop]
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (hloop.seq (s7.seq s8)))))))⟩
  simp only [encUnary, List.length_replicate] at s1 s2 ⊢
  omega

/-- **Stage 17 (`bmTakePadBits`)**:
Consumes `encPair encUnary encBits (b, bs)` on `kIO` and emits `takePadBits b bs` on `kIO`. -/
def bmTakePadBits : BitMachine :=
  bmSeq bmSliceDropBits bmFst

theorem bmTakePadBits_computesStageLe :
    ComputesStageLe bmTakePadBits (encPair encUnary encBits) encBits
      (fun p => takePadBits p.1 p.2)
      (fun p => 9 * p.1 + 6 * p.2.length + 29) := by
  refine (bmSeq_computesStageLe bmSliceDropBits_computesStageLe
    (bmFst_computesStageLe encBits encBits)).mono (fun ⟨b, bs⟩ => ?_)
  dsimp only [encBits, id]
  have h1 : (takePadBits b bs).length = b := length_takePadBits b bs
  have h2 : (bs.drop b).length ≤ bs.length := by simp [List.length_drop]
  omega

/-- **Stage 18 (`bmDropBits`)**:
Consumes `encPair encUnary encBits (b, bs)` on `kIO` and emits `bs.drop b` on `kIO`. -/
def bmDropBits : BitMachine :=
  bmSeq bmSliceDropBits bmSnd

theorem bmDropBits_computesStageLe :
    ComputesStageLe bmDropBits (encPair encUnary encBits) encBits
      (fun p => p.2.drop p.1)
      (fun p => 8 * p.1 + 6 * p.2.length + 28) := by
  refine (bmSeq_computesStageLe bmSliceDropBits_computesStageLe
    (bmSnd_computesStageLe encBits encBits)).mono (fun ⟨b, bs⟩ => ?_)
  dsimp only [encBits, id]
  have h1 : (takePadBits b bs).length = b := length_takePadBits b bs
  have h2 : (bs.drop b).length ≤ bs.length := by simp [List.length_drop]
  omega

/-! ## 7. Uniform Delimited-Frame Arithmetic Stages (`bmTwoTapeUniform`, `bmTwoTapeButterflyPair`, `bmRippleAdd`, `bmUnsignedButterfly`, `bmSignedButterfly`, `bmCondSubStep`) -/

/-- Lift any 2-operand `threeTapeWorkStk [] v1 v2 ↦ singleTapeStk (fn (v1, v2))` uniform machine
over `UniformReg` into a delimited-frame `BitMachine` consuming `encPair encBits encBits (v1, v2)`
on `kIO`. -/
def bmTwoTapeUniform (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg) : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork1).seq
    ((tmRevMoveWord kWork1 kWork0).seq
      ((tmPopFirstSubwordRev kIO kWork2).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork2 kWork1).seq
            (tmFramePush5.seq
              ((BitMachine.ofUniformDelim Λ main m).seq tmFramePop7))))))

theorem bmTwoTapeUniform_computesStageLe
    (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg)
    {α β : Type} (encA : α → List Bool × List Bool) (encB : β → List Bool)
    (fn : α → β) (steps : α → ℕ)
    (heval : ∀ x : α,
      Turing.EvalsToInTime (mkBitFinTM2 Λ main UniformReg default m).step
        ⟨some main, default, threeTapeWorkStk [] (encA x).1 (encA x).2⟩
        (some ⟨none, default, singleTapeStk (encB (fn x))⟩)
        (steps x)) :
    ComputesStageLe (bmTwoTapeUniform Λ main m)
      (fun x => encPair encBits encBits (encA x)) encB fn
      (fun x => steps x + 2 * (encA x).1.length + 2 * (encA x).2.length + 11) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  set v1 := (encA x).1
  set v2 := (encA x).2
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork1 (by decide)
    (encodeDelimWord v1 ++ encodeDelimWord v2) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork1 kWork0 (by decide)
    v1.reverse [] []
    (mkTapes8 (encodeDelimWord (encodeDelimWord v2)) [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork2 (by decide)
    (encodeDelimWord v2) [] tW2
    (mkTapes8 [] (encodeDelimWord v1) [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork2, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord v1) [] (encodeDelimWord v2.reverse ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork2 kWork1 (by decide)
    v2.reverse tW2 []
    (mkTapes8 [] (encodeDelimWord v1) [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork1, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmFramePush5_computesInTime v1 v2 [] [] [] tW2 tW3 tW4 tW5 tSch
  simp only [List.append_nil] at s6
  have s7 := BitMachine.ofUniformDelim_computesInTime main m
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch) (heval x)
  have s8 := tmFramePop7_computesInTime (encB (fn x)) [] [] [] tW2 tW3 tW4 tW5 tSch
  simp only [List.append_nil] at s8
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq s8))))))⟩
  omega

/-- Lift any 2-operand `threeTapeWorkStk [] v1 v2 ↦ twoTapeStk outIO outW0` uniform machine over
`ButterflyReg` into a delimited-frame `BitMachine` consuming `encPair encBits encBits (v1, v2)` on
`kIO` and producing `encPair encBits encBits (outIO, outW0)` on `kIO`. -/
def bmTwoTapeButterflyPair (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg) : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork1).seq
    ((tmRevMoveWord kWork1 kWork0).seq
      ((tmPopFirstSubwordRev kIO kWork2).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork2 kWork1).seq
            (tmFramePush5.seq
              ((BitMachine.ofButterflyDelim Λ main m).seq
                (tmFramePop6.seq
                  ((tmRevMoveWord kWork0 kWork1).seq
                    ((tmRevMoveWord kIO kWork0).seq
                      ((tmPushEmpty kIO).seq
                        ((tmPrependRevWord kWork1 kIO).seq
                          (tmPrependRevWord kWork0 kIO))))))))))))

theorem bmTwoTapeButterflyPair_computesStageLe
    (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg)
    {α β : Type} (encA : α → List Bool × List Bool)
    (out1 out2 : β → List Bool)
    (fn : α → β) (steps : α → ℕ)
    (heval : ∀ x : α,
      Turing.EvalsToInTime (mkBitFinTM2 Λ main ButterflyReg default m).step
        ⟨some main, default, threeTapeWorkStk [] (encA x).1 (encA x).2⟩
        (some ⟨none, default, twoTapeStk (out1 (fn x)) (out2 (fn x))⟩)
        (steps x)) :
    ComputesStageLe (bmTwoTapeButterflyPair Λ main m)
      (fun x => encPair encBits encBits (encA x))
      (fun y => encPair encBits encBits (out1 y, out2 y))
      fn
      (fun x => steps x + 2 * (encA x).1.length + 2 * (encA x).2.length +
        2 * (out1 (fn x)).length + 2 * (out2 (fn x)).length + 20) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  set v1 := (encA x).1
  set v2 := (encA x).2
  set w1 := out1 (fn x)
  set w2 := out2 (fn x)
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork1 (by decide)
    (encodeDelimWord v1 ++ encodeDelimWord v2) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork1 kWork0 (by decide)
    v1.reverse [] []
    (mkTapes8 (encodeDelimWord (encodeDelimWord v2)) [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork2 (by decide)
    (encodeDelimWord v2) [] tW2
    (mkTapes8 [] (encodeDelimWord v1) [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork2, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord v1) [] (encodeDelimWord v2.reverse ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork2 kWork1 (by decide)
    v2.reverse tW2 []
    (mkTapes8 [] (encodeDelimWord v1) [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork1, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmFramePush5_computesInTime v1 v2 [] [] [] tW2 tW3 tW4 tW5 tSch
  simp only [List.append_nil] at s6
  have s7 := BitMachine.ofButterflyDelim_computesInTime main m
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch) (heval x)
  have s8 := tmFramePop6_computesInTime w1 w2 [] [] [] tW2 tW3 tW4 tW5 tSch
  simp only [List.append_nil] at s8
  have s9 := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
    w2 [] [] (mkTapes8 (encodeDelimWord w1) [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.append_nil] at s9
  have s10 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
    w1 [] [] (mkTapes8 [] [] (encodeDelimWord w2.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at s10
  have s11 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] (encodeDelimWord w1.reverse) (encodeDelimWord w2.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s11
  have s12 := tmPrependRevWord_computesInTime kWork1 kIO (by decide)
    w2.reverse [] [] []
    (mkTapes8 [] (encodeDelimWord w1.reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s12
  have s13 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
    w1.reverse (encodeDelimWord w2) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s13
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12.seq s13)))))))))))⟩
  omega

/-- **Stage 19 (`bmRippleAdd`)**:
Uniform delimited-frame ripple-carry adder (`tmUniformRippleAdd` wrapped via `bmTwoTapeUniform`),
which simultaneously realizes both:
- Unsigned `w`-bit addition: `(encodeNatBits w A, encodeNatBits w B) ↦ encodeNatBits (w + 1) (A + B)`
  in `≤ 9 * w + 16` steps.
- Signed offset-binary addition: `(encodeSignedWord w x, encodeSignedWord w y) ↦ encodeSignedWord (w + 1) (x + y)`
  in `≤ 9 * w + 25` steps. -/
def bmRippleAdd : BitMachine :=
  bmTwoTapeUniform RippleAddLabel .popA tmUniformRippleAdd.m

theorem bmRippleAdd_unsigned_computesInTime (w A B : ℕ) (hA : A < 2 ^ w) (hB : B < 2 ^ w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 9 * w + 16,
      bmRippleAdd.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encBits encBits (encodeNatBits w A, encodeNatBits w B)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 1) (A + B)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := { p : ℕ × ℕ // p.1 < 2 ^ w ∧ p.2 < 2 ^ w }
  have hstage := bmTwoTapeUniform_computesStageLe RippleAddLabel .popA tmUniformRippleAdd.m
    (α := S) (β := ℕ)
    (fun s => (encodeNatBits w s.1.1, encodeNatBits w s.1.2))
    (encodeNatBits (w + 1))
    (fun s => s.1.1 + s.1.2)
    (fun _ => 5 * w + 5)
    (fun s => tmUniformRippleAdd_encodeNatBits_evalsToInTime_concrete w s.1.1 s.1.2 s.2.1 s.2.2)
  rcases hstage ⟨(A, B), hA, hB⟩ tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  simp only [encodeNatBits_length] at ht
  omega

theorem bmRippleAdd_signed_computesInTime (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 9 * w + 25,
      bmRippleAdd.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encBits encBits (encodeSignedWord w x, encodeSignedWord w y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (w + 1) (x + y)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := { p : ℤ × ℤ // FitsSignedWord w p.1 ∧ FitsSignedWord w p.2 }
  have hstage := bmTwoTapeUniform_computesStageLe RippleAddLabel .popA tmUniformRippleAdd.m
    (α := S) (β := ℤ)
    (fun s => (encodeSignedWord w s.1.1, encodeSignedWord w s.1.2))
    (encodeSignedWord (w + 1))
    (fun s => s.1.1 + s.1.2)
    (fun _ => 5 * w + 10)
    (fun s => tmUniformRippleAdd_encodeSignedWord_evalsToInTime_concrete w s.1.1 s.1.2 s.2.1 s.2.2)
  rcases hstage ⟨(x, y), hx, hy⟩ tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  simp only [encodeSignedWord, encodeNatBits_length] at ht
  omega

/-- **Stage 20 (`bmUnsignedButterfly`)**:
Uniform delimited-frame unsigned butterfly (`tmUniformButterflyAddSub` wrapped via
`bmTwoTapeButterflyPair`), computing `encPair encBits encBits (encodeNatBits (w + 1) (A + B), encodeNatBits w (A - B))`
in `≤ 16 * w + 28` steps for all `B ≤ A < 2 ^ w`. -/
def bmUnsignedButterfly : BitMachine :=
  bmTwoTapeButterflyPair ButterflyAddSubLabel .popA butterflyAddSubStmt

theorem bmUnsignedButterfly_computesInTime (w A B : ℕ)
    (hBA : B ≤ A) (hA : A < 2 ^ w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 16 * w + 28,
      bmUnsignedButterfly.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encBits encBits (encodeNatBits w A, encodeNatBits w B)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair encBits encBits
          (encodeNatBits (w + 1) (A + B), encodeNatBits w (A - B))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := { p : ℕ × ℕ // p.2 ≤ p.1 ∧ p.1 < 2 ^ w }
  have hstage := bmTwoTapeButterflyPair_computesStageLe
    ButterflyAddSubLabel .popA butterflyAddSubStmt
    (α := S) (β := ℕ × ℕ)
    (fun s => (encodeNatBits w s.1.1, encodeNatBits w s.1.2))
    (fun p => encodeNatBits (w + 1) p.1)
    (fun p => encodeNatBits w p.2)
    (fun s => (s.1.1 + s.1.2, s.1.1 - s.1.2))
    (fun _ => 8 * w + 6)
    (fun s => tmUniformButterflyAddSub_encodeNatBits_evalsToInTime_concrete w s.1.1 s.1.2 s.2.1 s.2.2)
  rcases hstage ⟨(A, B), hBA, hA⟩ tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  simp only [encodeNatBits_length] at ht
  omega

/-- **Stage 21 (`bmSignedButterfly`)**:
Uniform delimited-frame signed butterfly (`tmUniformSignedButterflyAddSub` wrapped via
`bmTwoTapeButterflyPair`), computing `encPair encBits encBits (encodeSignedWord (w + 1) (x + y), encodeSignedWord (w + 1) (x - y))`
in `≤ 16 * w + 49` steps for all `FitsSignedWord w x` and `FitsSignedWord w y`. -/
def bmSignedButterfly : BitMachine :=
  bmTwoTapeButterflyPair SignedButterflyLabel .initBorrow tmUniformSignedButterflyAddSub.m

theorem bmSignedButterfly_computesInTime (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 16 * w + 49,
      bmSignedButterfly.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encBits encBits (encodeSignedWord w x, encodeSignedWord w y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair encBits encBits
          (encodeSignedWord (w + 1) (x + y), encodeSignedWord (w + 1) (x - y))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := { p : ℤ × ℤ // FitsSignedWord w p.1 ∧ FitsSignedWord w p.2 }
  have hstage := bmTwoTapeButterflyPair_computesStageLe
    SignedButterflyLabel .initBorrow tmUniformSignedButterflyAddSub.m
    (α := S) (β := ℤ × ℤ)
    (fun s => (encodeSignedWord w s.1.1, encodeSignedWord w s.1.2))
    (fun p => encodeSignedWord (w + 1) p.1)
    (fun p => encodeSignedWord (w + 1) p.2)
    (fun s => (s.1.1 + s.1.2, s.1.1 - s.1.2))
    (fun _ => 8 * w + 17)
    (fun s => tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime_concrete w s.1.1 s.1.2 s.2.1 s.2.2)
  rcases hstage ⟨(x, y), hx, hy⟩ tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  simp only [encodeSignedWord, encodeNatBits_length] at ht
  omega

/-- **Stage 22 (`bmCondSubStep`)**:
Uniform delimited-frame conditional subtract-mux step for restoring division and square root
(`tmUniformCondSubStep` wrapped via `bmTwoTapeButterflyPair`), computing
`encPair encBits encBool (encodeNatBits w (if D ≤ R then R - D else R), decide (D ≤ R))`
in `≤ 13 * w + 25` steps for all `R, D < 2 ^ w`. -/
def bmCondSubStep : BitMachine :=
  bmTwoTapeButterflyPair CondSubStepLabel .popA tmUniformCondSubStep.m

theorem bmCondSubStep_computesInTime (w R D : ℕ) (hR : R < 2 ^ w) (hD : D < 2 ^ w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 13 * w + 25,
      bmCondSubStep.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encBits encBits (encodeNatBits w R, encodeNatBits w D)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair encBits encBool
          (encodeNatBits w (if D ≤ R then R - D else R), decide (D ≤ R))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := { p : ℕ × ℕ // p.1 < 2 ^ w ∧ p.2 < 2 ^ w }
  have hstage := bmTwoTapeButterflyPair_computesStageLe
    CondSubStepLabel .popA tmUniformCondSubStep.m
    (α := S) (β := ℕ × Bool)
    (fun s => (encodeNatBits w s.1.1, encodeNatBits w s.1.2))
    (fun p => encodeNatBits w p.1)
    (fun p => encBool p.2)
    (fun s => (if s.1.2 ≤ s.1.1 then s.1.1 - s.1.2 else s.1.1, decide (s.1.2 ≤ s.1.1)))
    (fun _ => 7 * w + 3)
    (fun s => tmUniformCondSubStep_encodeNatBits_evalsToInTime_concrete w s.1.1 s.1.2 s.2.1 s.2.2)
  rcases hstage ⟨(R, D), hR, hD⟩ tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  simp only [encodeNatBits_length, encBool, List.length_singleton] at ht
  omega

/-! ## 8. Bit-Stream Concatenation (`tmConcatRevWord`, `bmAppendBits`, `bmFlattenBits`) & Linear-Time Deinterleaving (`bmDeinterleaveList`, via `BitMachine.branchDelimBit` and `BitMachine.loopNonEmptyWord`) -/

/-- **Gadget 31 (`tmConcatRevWord kSrc kDst`)**:
Pops `encodeDelimWord u` from `kSrc` and prepends `u.reverse` directly onto the top delimited word
`encodeDelimWord v` on `kDst` (without pushing a `[true, false]` delimiter between `u.reverse` and `v`),
producing `encodeDelimWord (u.reverse ++ v)` on `kDst` in `u.length + 1` steps (`|Λ| = 1`,
independent of `v.length`). -/
def tmConcatRevWord (kSrc kDst : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.pop kSrc
      (fun _ bOpt => (default, bOpt.getD true))
      (Turing.TM2.Stmt.pop kSrc
        (fun rv bOpt => ({ rv.1 with bitA := bOpt.getD false }, rv.2))
        (Turing.TM2.Stmt.branch (fun rv => rv.2)
          (Turing.TM2.Stmt.load (fun _ => default) Turing.TM2.Stmt.halt)
          (Turing.TM2.Stmt.push kDst (fun rv => rv.1.bitA)
            (Turing.TM2.Stmt.push kDst (fun _ => false)
              (Turing.TM2.Stmt.load (fun _ => default)
                (Turing.TM2.Stmt.goto (fun _ => ())))))))

@[simp]
theorem numLabels_tmConcatRevWord (kSrc kDst : TapeIdx) :
    (tmConcatRevWord kSrc kDst).numLabels = 1 := rfl

def tmConcatRevWord_evalsToInTime_concrete (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst) :
    ∀ (u v restSrc restDst : List Bool)
      (T : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.EvalsToInTime (tmConcatRevWord kSrc kDst).toFinTM2.step
        ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
            kDst (encodeDelimWord v ++ restDst)⟩
        (some ⟨none, default,
          Function.update (Function.update T kSrc restSrc)
            kDst (encodeDelimWord (u.reverse ++ v) ++ restDst)⟩)
        (u.length + 1)
  | [], v, restSrc, restDst, T => by
    refine EvalsToInTime.step_one ?_
    simp only [tmConcatRevWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, List.reverse_nil, Function.update_of_ne hne.symm, Function.update_self,
      Function.update_idem, Function.update_comm hne, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | b :: u, v, restSrc, restDst, T => by
    have hstep : (tmConcatRevWord kSrc kDst).toFinTM2.step
        ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord (b :: u) ++ restSrc))
            kDst (encodeDelimWord v ++ restDst)⟩ =
        some ⟨some (), default,
          Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
            kDst (encodeDelimWord (b :: v) ++ restDst)⟩ := by
      simp only [tmConcatRevWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons, List.cons_append,
        Function.update_of_ne hne.symm, Function.update_self, Function.update_idem,
        Function.update_comm hne, List.head?_cons, List.tail_cons, Option.getD_some, cond_false]
    have ih := tmConcatRevWord_evalsToInTime_concrete kSrc kDst hne u (b :: v) restSrc restDst T
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons] at ih ⊢
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep ih) (by omega)

theorem tmConcatRevWord_computesInTime (kSrc kDst : TapeIdx) (hne : kSrc ≠ kDst)
    (u v restSrc restDst : List Bool)
    (T : ∀ k : TapeIdx, List (BitTapeAlphabet k)) :
    (tmConcatRevWord kSrc kDst).ComputesInTime
      (Function.update (Function.update T kSrc (encodeDelimWord u ++ restSrc))
        kDst (encodeDelimWord v ++ restDst))
      (Function.update (Function.update T kSrc restSrc)
        kDst (encodeDelimWord (u.reverse ++ v) ++ restDst))
      (u.length + 1) :=
  ⟨tmConcatRevWord_evalsToInTime_concrete kSrc kDst hne u v restSrc restDst T⟩

/-- **Stage 23 (`bmAppendBits`)**:
Consumes `encPair encBits encBits (u, v)` on `kIO` and produces `encodeDelimWord (u ++ v)` on `kIO`
in `3 * u.length + 2 * v.length + 9` steps. -/
def bmAppendBits : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork1).seq
    ((tmPopFirstSubwordRev kIO kWork0).seq
      ((tmDropWord kIO).seq
        ((tmRevMoveWord kWork0 kIO).seq
          (tmConcatRevWord kWork1 kIO))))

theorem bmAppendBits_computesStageLe :
    ComputesStageLe bmAppendBits (encPair encBits encBits) encBits
      (fun p => p.1 ++ p.2)
      (fun p => 2 * p.1.length + 2 * p.2.length + 8) := by
  intro ⟨u, v⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only [encBits, id]
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork1 (by decide)
    (encodeDelimWord u ++ encodeDelimWord v) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord v) [] []
    (mkTapes8 [] [] (encodeDelimWord u.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s2
  have s3 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord v.reverse) (encodeDelimWord u.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s3
  have s4 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    v.reverse [] []
    (mkTapes8 [] [] (encodeDelimWord u.reverse) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s4
  have s5 := tmConcatRevWord_computesInTime kWork1 kIO (by decide)
    u.reverse v [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq s5)))⟩
  omega

/-- **Stage 24 (`bmFlattenBits`)**:
Consumes `encList encBits xss` (`xss : List (List Bool)`) on `kIO` and flattens it into a single
bit-word `xss.flatten` on `kIO` in **strictly linear** $O(\sum |xs|)$ `TM2.step` transitions using `tmConcatRevWord`. -/
def bmFlattenBits : BitMachine :=
  bmRevList.seq
    ((tmMoveWord kIO kWork0 kWork2).seq
      ((tmPushEmpty kIO).seq
        (((tmPopFirstSubwordRev kWork2 kWork0).seq
            (tmConcatRevWord kWork0 kIO)).loopNonEmptyWord kWork2)))

theorem loopListFinalState_flattenAux :
    ∀ (xss : List (List Bool)) (acc : List Bool),
      loopListFinalState (fun xs a => xs ++ a) xss acc =
        xss.reverse.flatten ++ acc
  | [], acc => by simp [loopListFinalState]
  | xs :: xss, acc => by
    simp only [loopListFinalState_cons, List.reverse_cons, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    exact loopListFinalState_flattenAux xss (xs ++ acc)

theorem loopListStepsAux_flattenAux_le :
    ∀ (xss : List (List Bool)) (acc : List Bool),
      loopListStepsAux (fun xs a => xs ++ a)
        (fun xs _ _ => 2 * xs.length + 3) xss acc ≤
        2 * (encList encBits xss).length + 1
  | [], _ => by simp [loopListStepsAux]
  | xs :: xss, acc => by
    simp only [loopListStepsAux_cons, encList_cons, List.length_append,
      length_encodeDelimWord]
    have hxs : (encBits xs).length = xs.length := rfl
    have ih := loopListStepsAux_flattenAux_le xss (xs ++ acc)
    omega

theorem bmFlattenBits_computesStageLe :
    ComputesStageLe bmFlattenBits (encList encBits) encBits List.flatten
      (fun xss => 11 * (encList encBits xss).length + 18) := by
  intro xss tW2 tW3 tW4 tW5 tSch
  dsimp only
  rcases bmRevList_computesStageLe encBits xss tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  dsimp only at ht1
  have s2 := tmMoveWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
    (encList encBits xss.reverse) [] [] tW2
    (mkTapes8 [] [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
    List.append_nil] at s2
  have s3 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] (encodeDelimWord (encList encBits xss.reverse) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s3
  let nextSt : List Bool → List Bool → List Bool := fun xs a => xs ++ a
  let stepBound : List Bool → List (List Bool) → List Bool → ℕ := fun xs _ _ => 2 * xs.length + 3
  let stkOf : List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun a =>
    mkTapes8 (encodeDelimWord a) [] [] [] tW3 tW4 tW5 tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encBits nextSt stepBound stkOf
    (fun xs rem a restW2 => by
      dsimp only [stkOf, nextSt, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encBits xs) ++ encodeWordStack (rem.map encBits)) restW2 []
        (mkTapes8 (encodeDelimWord a) [] [] [] tW3 tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmConcatRevWord_computesInTime kWork0 kIO (by decide)
        (encBits xs).reverse a [] []
        (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encBits)) ++ restW2)
          tW3 tW4 tW5 tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2
      have hxs : (encBits xs).length = xs.length := rfl
      have hxs_eq : encBits xs = xs := rfl
      rw [hxs_eq] at b2
      exact ⟨_, by omega, b1.seq b2⟩)
    xss.reverse tW2 [] with ⟨tL, htL, s4⟩
  dsimp only [stkOf, nextSt, stepBound] at htL s4
  simp only [update_mkTapes8_kWork2] at s4
  rw [loopListFinalState_flattenAux, List.reverse_reverse, List.append_nil] at s4
  have hlen := length_encList_reverse encBits xss
  have hb := loopListStepsAux_flattenAux_le xss.reverse []
  rw [hlen] at s2 hb
  have hout : encBits xss.flatten = xss.flatten := rfl
  rw [← hout] at s4
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq s4))⟩
  omega

/-- Single-pass structural deinterleaving of `xs : List α` into `(evens, odds)`:
`deinterleaveList (x0 :: x1 :: xs) = (x0 :: (deinterleaveList xs).1, x1 :: (deinterleaveList xs).2)`. -/
def deinterleaveList {α : Type} : List α → List α × List α
  | [] => ([], [])
  | x :: xs =>
    let p := deinterleaveList xs
    (x :: p.2, p.1)

@[simp]
theorem deinterleaveList_nil {α : Type} :
    deinterleaveList ([] : List α) = ([], []) := rfl

@[simp]
theorem deinterleaveList_cons {α : Type} (x : α) (xs : List α) :
    deinterleaveList (x :: xs) = (x :: (deinterleaveList xs).2, (deinterleaveList xs).1) := rfl

theorem deinterleaveList_cons_cons {α : Type} (x y : α) (xs : List α) :
    deinterleaveList (x :: y :: xs) =
      (x :: (deinterleaveList xs).1, y :: (deinterleaveList xs).2) := rfl

/-- Step function for `bmDeinterleaveList` over `xs : List α` with parity flag `st.1 : Bool`
and reversed accumulators `(st.2.1, st.2.2) : List α × List α`. -/
def deinterleaveRevStep {α : Type} (x : α) (st : Bool × List α × List α) :
    Bool × List α × List α :=
  if st.1 then (false, st.2.1, x :: st.2.2) else (true, x :: st.2.1, st.2.2)

theorem loopListFinalState_deinterleaveRevStep {α : Type} :
    ∀ (xs : List α) (p : Bool) (acc0 acc1 : List α),
      ((loopListFinalState deinterleaveRevStep xs (p, acc0, acc1)).2.1.reverse,
       (loopListFinalState deinterleaveRevStep xs (p, acc0, acc1)).2.2.reverse) =
      if p then
        (acc0.reverse ++ (deinterleaveList xs).2, acc1.reverse ++ (deinterleaveList xs).1)
      else
        (acc0.reverse ++ (deinterleaveList xs).1, acc1.reverse ++ (deinterleaveList xs).2)
  | [], p, acc0, acc1 => by
    cases p <;> simp [loopListFinalState]
  | x :: xs, false, acc0, acc1 => by
    have ih := loopListFinalState_deinterleaveRevStep xs true (x :: acc0) acc1
    simp only [loopListFinalState_cons, deinterleaveRevStep, Bool.false_eq_true, ↓reduceIte,
      List.reverse_cons, List.append_assoc, List.singleton_append, deinterleaveList_cons] at ih ⊢
    exact ih
  | x :: xs, true, acc0, acc1 => by
    have ih := loopListFinalState_deinterleaveRevStep xs false acc0 (x :: acc1)
    simp only [loopListFinalState_cons, deinterleaveRevStep, Bool.false_eq_true, ↓reduceIte,
      List.reverse_cons, List.append_assoc, List.singleton_append, deinterleaveList_cons] at ih ⊢
    exact ih

theorem length_encList_deinterleaveList {α : Type} (encElem : α → List Bool) :
    ∀ (xs : List α),
      (encList encElem (deinterleaveList xs).1).length +
        (encList encElem (deinterleaveList xs).2).length =
      (encList encElem xs).length
  | [] => rfl
  | x :: xs => by
    have ih := length_encList_deinterleaveList encElem xs
    simp only [deinterleaveList_cons, encList_cons, List.length_append]
    omega

theorem loopListStepsAux_deinterleaveRevStep_le {α : Type} (encElem : α → List Bool) :
    ∀ (xs : List α) (st : Bool × List α × List α),
      loopListStepsAux deinterleaveRevStep
        (fun x _ _ => 2 * (encElem x).length + 7) xs st ≤
        4 * (encList encElem xs).length + 1
  | [], _ => by simp [loopListStepsAux]
  | x :: xs, st => by
    simp only [loopListStepsAux_cons, encList_cons, List.length_append, length_encodeDelimWord]
    have ih := loopListStepsAux_deinterleaveRevStep_le encElem xs (deinterleaveRevStep x st)
    omega

/-- Pushes the 1-bit delimited word `encodeDelimWord [b] = [false, b, true, false]` onto stack `k`
in 1 step (`|Λ| = 1`, `|σ| = 32`). -/
def tmPushBitWord (b : Bool) (k : TapeIdx) : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.push k (fun _ => false)
      (Turing.TM2.Stmt.push k (fun _ => true)
        (Turing.TM2.Stmt.push k (fun _ => b)
          (Turing.TM2.Stmt.push k (fun _ => false) Turing.TM2.Stmt.halt)))

@[simp]
theorem numLabels_tmPushBitWord (b : Bool) (k : TapeIdx) :
    (tmPushBitWord b k).numLabels = 1 := rfl

theorem tmPushBitWord_computesInTime (b : Bool) (k : TapeIdx)
    (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    (tmPushBitWord b k).ComputesInTime T
      (Function.update T k (encodeDelimWord [b] ++ T k)) 1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp [tmPushBitWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux]

/-- **Stage 25 (`bmDeinterleaveList`)**:
Consumes `encList encElem xs` on `kIO` and splits `xs` into even-indexed and odd-indexed sublists
`encPair (encList encElem) (encList encElem) (deinterleaveList xs)` on `kIO` in **strictly linear**
$O(\sum |x|)$ `TM2.step` transitions (`≤ 22 * (encList encElem xs).length + 45` steps). -/
def bmDeinterleaveList : BitMachine :=
  (tmMoveWord kIO kWork0 kWork2).seq
    ((tmPushEmpty kWork3).seq
      ((tmPushEmpty kWork4).seq
        ((tmPushBitWord false kSched).seq
          ((((tmPopFirstSubwordRev kWork2 kWork0).seq
              (BitMachine.branchDelimBit kSched
                ((tmPrependRevWord kWork0 kWork3).seq (tmPushBitWord true kSched))
                ((tmPrependRevWord kWork0 kWork4).seq (tmPushBitWord false kSched)))).loopNonEmptyWord kWork2).seq
            ((tmDropWord kSched).seq
              ((tmMoveWord kWork3 kWork0 kIO).seq
                (bmRevList.seq
                  ((tmRevMoveWord kIO kWork3).seq
                    ((tmMoveWord kWork4 kWork0 kIO).seq
                      (bmRevList.seq
                        ((tmMoveWord kWork3 kWork1 kWork0).seq tmPackPairFromRev)))))))))))

theorem bmDeinterleaveList_computesStageLe {α : Type} (encElem : α → List Bool) :
    ComputesStageLe bmDeinterleaveList
      (encList encElem) (encPair (encList encElem) (encList encElem))
      deinterleaveList
      (fun xs => 24 * (encList encElem xs).length + 55) := by
  intro xs tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmMoveWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
    (encList encElem xs) [] [] tW2 (mkTapes8 [] [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
    List.append_nil] at s1
  have s2 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s2
  have s3 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2)
      (encodeDelimWord [] ++ tW3) tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s3
  have s4 := tmPushBitWord_computesInTime false kSched
    (mkTapes8 [] [] [] (encodeDelimWord (encList encElem xs) ++ tW2)
      (encodeDelimWord [] ++ tW3) (encodeDelimWord [] ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kSched, mkTapes8_kSched] at s4
  let stepBound : α → List α → Bool × List α × List α → ℕ :=
    fun x _ _ => 2 * (encElem x).length + 7
  let stkOf : Bool × List α × List α → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] []
      (encodeDelimWord (encList encElem st.2.1) ++ tW3)
      (encodeDelimWord (encList encElem st.2.2) ++ tW4)
      tW5
      (encodeDelimWord [st.1] ++ tSch)
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encElem
    deinterleaveRevStep stepBound stkOf
    (fun x rem st restW2 => by
      rcases st with ⟨p, acc0, acc1⟩
      dsimp only [stkOf, deinterleaveRevStep, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encElem x) ++ encodeWordStack (rem.map encElem)) restW2 []
        (mkTapes8 [] [] [] []
          (encodeDelimWord (encList encElem acc0) ++ tW3)
          (encodeDelimWord (encList encElem acc1) ++ tW4)
          tW5 (encodeDelimWord [p] ++ tSch))
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      cases p with
      | false =>
        have c1 := tmPrependRevWord_computesInTime kWork0 kWork3 (by decide)
          (encElem x).reverse (encList encElem acc0) [] tW3
          (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2)
            [] (encodeDelimWord (encList encElem acc1) ++ tW4) tW5 tSch)
        simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
          List.reverse_reverse, List.append_nil] at c1
        have c2 := tmPushBitWord_computesInTime true kSched
          (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2)
            (encodeDelimWord (encodeDelimWord (encElem x) ++ encList encElem acc0) ++ tW3)
            (encodeDelimWord (encList encElem acc1) ++ tW4) tW5 tSch)
        simp only [update_mkTapes8_kSched, mkTapes8_kSched] at c2
        have br := BitMachine.ComputesInTime.branchDelimBit kSched
          (M_false := (tmPrependRevWord kWork0 kWork3).seq (tmPushBitWord true kSched))
          (M_true := (tmPrependRevWord kWork0 kWork4).seq (tmPushBitWord false kSched))
          false tSch
          (T₁ := mkTapes8 [] (encodeDelimWord (encElem x).reverse) []
            (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2)
            (encodeDelimWord (encList encElem acc0) ++ tW3)
            (encodeDelimWord (encList encElem acc1) ++ tW4) tW5 [])
          (by simpa only [update_mkTapes8_kSched, Bool.false_eq_true, ↓reduceIte] using c1.seq c2)
        simp only [update_mkTapes8_kSched, Bool.false_eq_true, ↓reduceIte, encList_cons] at br ⊢
        exact ⟨_, by omega, b1.seq br⟩
      | true =>
        have c1 := tmPrependRevWord_computesInTime kWork0 kWork4 (by decide)
          (encElem x).reverse (encList encElem acc1) [] tW4
          (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2)
            (encodeDelimWord (encList encElem acc0) ++ tW3) [] tW5 tSch)
        simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork4, List.length_reverse,
          List.reverse_reverse, List.append_nil] at c1
        have c2 := tmPushBitWord_computesInTime false kSched
          (mkTapes8 [] [] [] (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2)
            (encodeDelimWord (encList encElem acc0) ++ tW3)
            (encodeDelimWord (encodeDelimWord (encElem x) ++ encList encElem acc1) ++ tW4) tW5 tSch)
        simp only [update_mkTapes8_kSched, mkTapes8_kSched] at c2
        have br := BitMachine.ComputesInTime.branchDelimBit kSched
          (M_false := (tmPrependRevWord kWork0 kWork3).seq (tmPushBitWord true kSched))
          (M_true := (tmPrependRevWord kWork0 kWork4).seq (tmPushBitWord false kSched))
          true tSch
          (T₁ := mkTapes8 [] (encodeDelimWord (encElem x).reverse) []
            (encodeDelimWord (encodeWordStack (rem.map encElem)) ++ restW2)
            (encodeDelimWord (encList encElem acc0) ++ tW3)
            (encodeDelimWord (encList encElem acc1) ++ tW4) tW5 [])
          (by simpa only [update_mkTapes8_kSched, ↓reduceIte] using c1.seq c2)
        simp only [update_mkTapes8_kSched, ↓reduceIte, encList_cons] at br ⊢
        exact ⟨_, by omega, b1.seq br⟩)
    xs tW2 (false, [], []) with ⟨tL, htL, s5⟩
  dsimp only [stkOf, stepBound] at htL s5
  simp only [update_mkTapes8_kWork2, encList_nil] at s5
  set stF := loopListFinalState deinterleaveRevStep xs (false, [], [])
  have hrev := loopListFinalState_deinterleaveRevStep xs false [] []
  simp only [Bool.false_eq_true, ↓reduceIte, List.reverse_nil, List.nil_append] at hrev
  have hrev1 : stF.2.1.reverse = (deinterleaveList xs).1 := congrArg Prod.fst hrev
  have hrev2 : stF.2.2.reverse = (deinterleaveList xs).2 := congrArg Prod.snd hrev
  have s6 := tmDropWord_computesInTime kSched [stF.1] tSch
    (mkTapes8 [] [] [] tW2
      (encodeDelimWord (encList encElem stF.2.1) ++ tW3)
      (encodeDelimWord (encList encElem stF.2.2) ++ tW4) tW5 [])
  simp only [update_mkTapes8_kSched, List.length_singleton] at s6
  have s7 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encList encElem stF.2.1) tW3 [] []
    (mkTapes8 [] [] [] tW2 [] (encodeDelimWord (encList encElem stF.2.2) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s7
  rcases bmRevList_computesStageLe encElem stF.2.1
    tW2 tW3 (encodeDelimWord (encList encElem stF.2.2) ++ tW4) tW5 tSch with ⟨tR1, htR1, s8⟩
  dsimp only at htR1
  rw [hrev1] at s8
  have s9 := tmRevMoveWord_computesInTime kIO kWork3 (by decide)
    (encList encElem (deinterleaveList xs).1) [] tW3
    (mkTapes8 [] [] [] tW2 [] (encodeDelimWord (encList encElem stF.2.2) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork3, List.append_nil] at s9
  have s10 := tmMoveWord_computesInTime kWork4 kWork0 kIO (by decide) (by decide) (by decide)
    (encList encElem stF.2.2) tW4 [] []
    (mkTapes8 [] [] [] tW2
      (encodeDelimWord (encList encElem (deinterleaveList xs).1).reverse ++ tW3) [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s10
  rcases bmRevList_computesStageLe encElem stF.2.2 tW2
    (encodeDelimWord (encList encElem (deinterleaveList xs).1).reverse ++ tW3)
    tW4 tW5 tSch with ⟨tR2, htR2, s11⟩
  dsimp only at htR2
  rw [hrev2] at s11
  have s12 := tmMoveWord_computesInTime kWork3 kWork1 kWork0 (by decide) (by decide) (by decide)
    (encList encElem (deinterleaveList xs).1).reverse tW3 [] []
    (mkTapes8 (encodeDelimWord (encList encElem (deinterleaveList xs).2)) [] []
      tW2 [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
    List.length_reverse, List.append_nil] at s12
  have s13 := tmPackPairFromRev_computesInTime
    (encList encElem (deinterleaveList xs).1)
    (encList encElem (deinterleaveList xs).2)
    tW2 tW3 tW4 tW5 tSch
  have hlen1 : (encList encElem stF.2.1).length = (encList encElem (deinterleaveList xs).1).length := by
    rw [← length_encList_reverse encElem stF.2.1, hrev1]
  have hlen2 : (encList encElem stF.2.2).length = (encList encElem (deinterleaveList xs).2).length := by
    rw [← length_encList_reverse encElem stF.2.2, hrev2]
  have hsum := length_encList_deinterleaveList encElem xs
  have hbL := loopListStepsAux_deinterleaveRevStep_le encElem xs (false, [], [])
  simp only [hlen1, hlen2] at s7 s10 htR1 htR2
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12.seq s13)))))))))))⟩
  omega

/-! ## 9. Linear List Zipping, Bit-Chunk Slicing, & Carry-Save Emission (`bmZipList`, `bmZipWithCtx`, `bmSliceBitChunks`, `bmCarrySaveEmitBits`) -/

/-- Fixed-width unsigned bit-word encoding `encodeNatBits w x`. -/
def encNatWord (w : ℕ) (x : ℕ) : List Bool :=
  encodeNatBits w x

@[simp]
theorem length_encNatWord (w x : ℕ) : (encNatWord w x).length = w :=
  encodeNatBits_length w x

@[simp]
theorem unconsDelimWord_encodeWordStack (ws : List (List Bool)) :
    unconsDelimWord (encodeWordStack ws) = (ws.headD [], encodeWordStack ws.tail) := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    simp [encodeWordStack, unconsDelimWord_encodeDelimWord_append]

/-- Step function for `bmZipList` over `xs : List α` with remaining raw words `st.1 : List (List Bool)`
and reversed zipped pair words `st.2 : List (List Bool)`. -/
def zipWordsRevStep {α : Type} (encA : α → List Bool) (x : α)
    (st : List (List Bool) × List (List Bool)) : List (List Bool) × List (List Bool) :=
  (st.1.tail, (encodeDelimWord (encA x) ++ encodeDelimWord (st.1.headD [])) :: st.2)

theorem loopListFinalState_zipWordsRevStep {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ∀ (xs : List α) (ys : List β) (acc : List (List Bool)),
      xs.length = ys.length →
      loopListFinalState (zipWordsRevStep encA) xs (ys.map encB, acc) =
        ([], ((List.zip xs ys).reverse).map (encPair encA encB) ++ acc)
  | [], [], acc, _ => by simp [loopListFinalState]
  | x :: xs, y :: ys, acc, hlen => by
    have hlen' : xs.length = ys.length := Nat.succ.inj hlen
    simp only [loopListFinalState_cons, zipWordsRevStep, List.map_cons, List.headD_cons,
      List.tail_cons, List.zip_cons_cons, List.reverse_cons, List.map_append,
      List.append_assoc]
    exact loopListFinalState_zipWordsRevStep encA encB xs ys
      (encPair encA encB (x, y) :: acc) hlen'

theorem length_encList_zip_eq {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ∀ (xs : List α) (ys : List β),
      xs.length = ys.length →
      (encList (encPair encA encB) (List.zip xs ys)).length =
        2 * (encList encA xs).length + 2 * (encList encB ys).length + 2 * xs.length
  | [], [], _ => rfl
  | x :: xs, y :: ys, hlen => by
    have ih := length_encList_zip_eq encA encB xs ys (Nat.succ.inj hlen)
    simp only [List.zip_cons_cons, encList_cons, List.length_append,
      length_encodeDelimWord, length_encPair, List.length_cons, ih]
    omega

theorem length_encList_ge_two_mul_length {α : Type} (encElem : α → List Bool) :
    ∀ (xs : List α), 2 * xs.length ≤ (encList encElem xs).length
  | [] => by simp
  | x :: xs => by
    have ih := length_encList_ge_two_mul_length encElem xs
    simp only [encList_cons, List.length_append, length_encodeDelimWord, List.length_cons]
    omega

theorem loopListStepsAux_zipWordsRevStep_le {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ∀ (xs : List α) (ys : List β) (acc : List (List Bool)),
      xs.length = ys.length →
      loopListStepsAux (zipWordsRevStep encA)
        (fun x _ st => 8 * (encA x).length + 8 * (st.1.headD []).length + 30)
        xs (ys.map encB, acc) ≤
      8 * (encList encA xs).length + 8 * (encList encB ys).length + 1
  | [], [], _, _ => by simp [loopListStepsAux]
  | x :: xs, y :: ys, acc, hlen => by
    have ih := loopListStepsAux_zipWordsRevStep_le encA encB xs ys
      ((encodeDelimWord (encA x) ++ encodeDelimWord (encB y)) :: acc) (Nat.succ.inj hlen)
    simp only [loopListStepsAux_cons, zipWordsRevStep, List.map_cons, List.headD_cons,
      List.tail_cons, encList_cons, List.length_append, length_encodeDelimWord] at ih ⊢
    omega

/-- **Stage 26 (`bmZipList`)**:
Consumes `encPair (encList encA) (encList encB) (xs, ys)` on `kIO` (where `xs.length = ys.length`)
and produces `encList (encPair encA encB) (List.zip xs ys)` on `kIO` in **strictly linear**
$O(\sum |x| + \sum |y|)$ `TM2.step` transitions (`≤ 26 * (encPair (encList encA) (encList encB) (xs, ys)).length + 50`). -/
def bmZipList : BitMachine :=
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
                ((tmPopEmpty kWork3).seq
                  ((tmMoveWord kWork4 kWork0 kIO).seq bmRevList))))))))

theorem bmZipList_computesStageLe {α β : Type} (encA : α → List Bool) (encB : β → List Bool) :
    ComputesStageLe bmZipList
      (fun s : { p : List α × List β // p.1.length = p.2.length } =>
        encPair (encList encA) (encList encB) s.1)
      (encList (encPair encA encB))
      (fun s => List.zip s.1.1 s.1.2)
      (fun s => 26 * (encPair (encList encA) (encList encB) s.1).length + 50) := by
  rintro ⟨⟨xs, ys⟩, hlen⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
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
  have hfin := loopListFinalState_zipWordsRevStep encA encB xs ys [] hlen
  rw [List.append_nil] at hfin
  rw [hfin] at s7
  change ( _ : BitMachine).ComputesInTime _
    (mkTapes8 [] [] [] tW2 (encodeDelimWord [] ++ tW3)
      (encodeDelimWord (encList (encPair encA encB) (List.zip xs ys).reverse) ++ tW4) tW5 tSch) tL at s7
  have s8 := tmPopEmpty_computesInTime kWork3
    (mkTapes8 [] [] [] tW2 (encodeDelimWord [] ++ tW3)
      (encodeDelimWord (encList (encPair encA encB) (List.zip xs ys).reverse) ++ tW4) tW5 tSch)
    tW3 (by simp)
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
  have hlen_zip := length_encList_zip_eq encA encB xs ys hlen
  have hlen_ge := length_encList_ge_two_mul_length encA xs
  have hbL := loopListStepsAux_zipWordsRevStep_le encA encB xs ys [] hlen
  simp only [hlen_rev, hlen_zip] at s9 htR
  simp only [encPair, List.length_append, length_encodeDelimWord] at s1 ⊢
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq s10))))))))⟩
  omega

theorem map_zip_eq_zipWith {α β δ : Type} (f : α → β → δ) :
    ∀ (xs : List α) (ys : List β),
      (List.zip xs ys).map (fun p => f p.1 p.2) = List.zipWith f xs ys
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by simp [map_zip_eq_zipWith f xs ys]

/-- **Stage 27 (`bmZipWithCtx body`)**:
Consumes `encPair encCtx (encPair (encList encA) (encList encB)) (ctx, (xs, ys))` on `kIO`
(with `xs.length = ys.length`), zips `xs` and `ys` in linear time via `bmZipList`, and maps `body`
with shared context `ctx` over `List.zip xs ys` via `bmMapWithCtx body`. -/
def bmZipWithCtx (body : BitMachine) : BitMachine :=
  bmSeq (bmPairMap bmId bmZipList) (bmMapWithCtx body)

theorem bmZipWithCtx_computesStageLe {α β γ δ : Type} {body : BitMachine}
    {encCtx : γ → List Bool} {encA : α → List Bool} {encB : β → List Bool} {encD : δ → List Bool}
    {fn : γ → α → β → δ} {stepB : γ → α → β → ℕ}
    (hbody : ComputesStageLe body (encPair encCtx (encPair encA encB)) encD
      (fun p => fn p.1 p.2.1 p.2.2) (fun p => stepB p.1 p.2.1 p.2.2)) :
    ComputesStageLe (bmZipWithCtx body)
      (fun s : { q : γ × (List α × List β) // q.2.1.length = q.2.2.length } =>
        encPair encCtx (encPair (encList encA) (encList encB)) s.1)
      (encList encD)
      (fun s => List.zipWith (fn s.1.1) s.1.2.1 s.1.2.2)
      (fun s =>
        let ctx := s.1.1
        let xs := s.1.2.1
        let ys := s.1.2.2
        let zipped := List.zip xs ys
        30 * (encPair encCtx (encPair (encList encA) (encList encB)) s.1).length +
          9 * (encList (encPair encA encB) zipped).length +
          11 * (encList encD (List.zipWith (fn ctx) xs ys)).length +
          loopListStepsAux (fun p a => fn ctx p.1 p.2 :: a)
            (fun p _ _ => stepB ctx p.1 p.2 + 4 * (encCtx ctx).length +
              2 * (encPair encA encB p).length +
              2 * (encD (fn ctx p.1 p.2)).length + 17) zipped [] + 95) := by
  rintro ⟨⟨ctx, ⟨xs, ys⟩⟩, hlen⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  let S_pair := { p : List α × List β // p.1.length = p.2.length }
  have h1 := bmPairMap_computesStageLe (bmId_computesStageLe encCtx) (bmZipList_computesStageLe encA encB)
    (ctx, (⟨(xs, ys), hlen⟩ : S_pair)) tW2 tW3 tW4 tW5 tSch
  rcases h1 with ⟨t1, ht1, s1⟩
  dsimp only [id] at ht1 s1
  rcases bmMapWithCtx_computesStageLe hbody (ctx, List.zip xs ys) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  dsimp only at ht2 s2
  rw [map_zip_eq_zipWith (fn ctx) xs ys] at ht2 s2
  simp only [encPair, List.length_append, length_encodeDelimWord] at ht1 ht2 ⊢
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

theorem sliceBitChunks_zero (b : ℕ) (bs : List Bool) :
    sliceBitChunks b 0 bs = [] := rfl

theorem sliceBitChunks_succ (b R : ℕ) (bs : List Bool) :
    sliceBitChunks b (R + 1) bs = decodeNatBits (bs.take b) :: sliceBitChunks b R (bs.drop b) := rfl

/-- Step function for `bmSliceBitChunks` over `R` chunks of width `b`. -/
def sliceChunkRevStep (b : ℕ) (st : List Bool × List ℕ) : List Bool × List ℕ :=
  (st.1.drop b, decodeNatBits (st.1.take b) :: st.2)

theorem loopFinalState_sliceChunkRevStep (b : ℕ) :
    ∀ (cnt : List Bool) (bs : List Bool) (acc : List ℕ),
      (loopFinalState (sliceChunkRevStep b) cnt (bs, acc)).2 =
        (sliceBitChunks b cnt.length bs).reverse ++ acc
  | [], bs, acc => by
    rw [List.length_nil, sliceBitChunks_zero]
    rfl
  | _ :: cnt, bs, acc => by
    rw [loopFinalState_cons, sliceChunkRevStep, List.length_cons, sliceBitChunks_succ,
      List.reverse_cons, List.append_assoc, List.singleton_append]
    exact loopFinalState_sliceChunkRevStep b cnt (bs.drop b) (decodeNatBits (bs.take b) :: acc)

theorem length_loopFinalState_sliceChunkRevStep_fst_le (b : ℕ) :
    ∀ (cnt : List Bool) (bs : List Bool) (acc : List ℕ),
      (loopFinalState (sliceChunkRevStep b) cnt (bs, acc)).1.length ≤ bs.length
  | [], bs, _ => le_rfl
  | _ :: cnt, bs, acc => by
    simp only [loopFinalState_cons, sliceChunkRevStep]
    refine le_trans (length_loopFinalState_sliceChunkRevStep_fst_le b cnt (bs.drop b)
      (decodeNatBits (bs.take b) :: acc)) ?_
    simp [List.length_drop]

theorem loopStepsAux_sliceChunkRevStep_le (b : ℕ) :
    ∀ (cnt : List Bool) (st : List Bool × List ℕ),
      loopStepsAux (sliceChunkRevStep b) (fun _ => 6 * b + 9) cnt st ≤
        cnt.length * (6 * b + 10) + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: cnt, st => by
    simp only [loopStepsAux_cons, List.length_cons]
    have ih := loopStepsAux_sliceChunkRevStep_le b cnt (sliceChunkRevStep b st)
    nlinarith

theorem length_encList_sliceBitChunks (b : ℕ) :
    ∀ (R : ℕ) (bs : List Bool),
      (encList (encNatWord b) (sliceBitChunks b R bs)).length = R * (2 * b + 2)
  | 0, bs => by rw [sliceBitChunks_zero, encList_nil, List.length_nil, Nat.zero_mul]
  | R + 1, bs => by
    rw [sliceBitChunks_succ, encList_cons, List.length_append,
      length_encodeDelimWord, length_encNatWord, length_encList_sliceBitChunks b R (bs.drop b)]
    ring

/-- **Stage 28 (`bmSliceBitChunks`)**:
Consumes `encPair encUnary (encPair encUnary encBits) (R, (b, bs))` on `kIO` and slices `bs` into
`R` chunks of `b` bits `encList (encNatWord b) (sliceBitChunks b R bs)` on `kIO` in **strictly
linear** $O(R \cdot b + |bs|)$ `TM2.step` transitions (`≤ 26 * R * (b + 1) + 7 * bs.length + 12 * b + 55`). -/
def bmSliceBitChunks : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kSched).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kIO).seq
            ((tmPopFirstSubwordRev kIO kWork0).seq
              ((tmRevMoveWord kWork0 kWork3).seq
                ((tmPopFirstSubwordRev kIO kWork0).seq
                  ((tmDropWord kIO).seq
                    ((tmRevMoveWord kWork0 kWork2).seq
                      ((tmPushEmpty kWork4).seq
                        ((((tmDupWord kWork3 kWork0 kWork1).seq
                            ((tmPushEmpty kWork0).seq
                              (((tmPopBitOrZero kWork2 kWork0).loopDelimWord kWork1).seq
                                (tmPrependRevWord kWork0 kWork4)))).loopDelimWord kSched).seq
                          ((tmDropWord kWork2).seq
                            ((tmDropWord kWork3).seq
                              ((tmMoveWord kWork4 kWork0 kIO).seq bmRevList))))))))))))))

theorem bmSliceBitChunks_computesInTime (R b : ℕ) (bs : List Bool)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 30 * R * (b + 1) + 7 * bs.length + 12 * b + 55,
      bmSliceBitChunks.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encPair encUnary encBits) (R, (b, bs))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encNatWord b) (sliceBitChunks b R bs)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary R) ++ encodeDelimWord (encPair encUnary encBits (b, bs))) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kSched (by decide)
    (encUnary R).reverse [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encPair encUnary encBits (b, bs))))
      [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kSched, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encPair encUnary encBits (b, bs))) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encPair encUnary encBits (b, bs)).reverse) []
      tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encPair encUnary encBits (b, bs)).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary b) ++ encodeDelimWord bs) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s6
  have s7 := tmRevMoveWord_computesInTime kWork0 kWork3 (by decide)
    (encUnary b).reverse [] tW3
    (mkTapes8 (encodeDelimWord (encodeDelimWord bs)) [] [] tW2 [] tW4 tW5
      (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s7
  have s8 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord bs) [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5
      (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s8
  have s9 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord bs.reverse) [] tW2
      (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s9
  have s10 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    bs.reverse [] tW2
    (mkTapes8 [] [] [] [] (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5
      (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s10
  have s11 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord bs ++ tW2)
      (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 (encodeDelimWord (encUnary R) ++ tSch))
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s11
  let stkOf : List Bool × List ℕ → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] (encodeDelimWord st.1 ++ tW2)
      (encodeDelimWord (encUnary b) ++ tW3)
      (encodeDelimWord (encList (encNatWord b) st.2) ++ tW4) tW5 []
  rcases BitMachine.ComputesInTime.loopDelimWord_state_le kSched
    (sliceChunkRevStep b) (fun _ => 6 * b + 9) stkOf
    (fun st tailSch => by
      rcases st with ⟨remBits, accChunks⟩
      dsimp only [stkOf, sliceChunkRevStep]
      simp only [update_mkTapes8_kSched]
      have b1 := tmDupWord_computesInTime kWork3 kWork0 kWork1 (by decide) (by decide) (by decide)
        (encUnary b) tW3 [] []
        (mkTapes8 [] [] [] (encodeDelimWord remBits ++ tW2) []
          (encodeDelimWord (encList (encNatWord b) accChunks) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
        List.append_nil, length_encUnary] at b1
      have b2 := tmPushEmpty_computesInTime kWork0
        (mkTapes8 [] [] (encodeDelimWord (encUnary b))
          (encodeDelimWord remBits ++ tW2) (encodeDelimWord (encUnary b) ++ tW3)
          (encodeDelimWord (encList (encNatWord b) accChunks) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork0, mkTapes8_kWork0, List.append_nil] at b2
      let innerStk : List Bool × List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun ist =>
        mkTapes8 [] (encodeDelimWord ist.2) [] (encodeDelimWord ist.1 ++ tW2)
          (encodeDelimWord (encUnary b) ++ tW3)
          (encodeDelimWord (encList (encNatWord b) accChunks) ++ tW4) tW5 tailSch
      have b3 := BitMachine.ComputesInTime.loopDelimWord_state kWork1
        popBitStep (fun _ => 1) innerStk
        (fun ist tailW1 => by
          dsimp only [innerStk, popBitStep]
          simp only [update_mkTapes8_kWork1]
          have hp := tmPopBitOrZero_computesInTime kWork2 kWork0 (by decide)
            ist.1 ist.2 tW2 []
            (mkTapes8 [] [] tailW1 [] (encodeDelimWord (encUnary b) ++ tW3)
              (encodeDelimWord (encList (encNatWord b) accChunks) ++ tW4) tW5 tailSch)
          simpa only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil] using hp)
        (encUnary b) [] (remBits, [])
      dsimp only [innerStk] at b3
      simp only [update_mkTapes8_kWork1, List.append_nil, loopFinalState_popBitStep,
        loopStepsAux_popBitStep, length_encUnary,
        ← encodeNatBits_decodeNatBits_takePadBits] at b3
      have b4 := tmPrependRevWord_computesInTime kWork0 kWork4 (by decide)
        (encodeNatBits b (decodeNatBits (remBits.take b))).reverse
        (encList (encNatWord b) accChunks) [] tW4
        (mkTapes8 [] [] [] (encodeDelimWord (remBits.drop b) ++ tW2)
          (encodeDelimWord (encUnary b) ++ tW3) [] tW5 tailSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork4, List.length_reverse,
        List.reverse_reverse, encodeNatBits_length, List.append_nil] at b4
      simp only [encList_cons, encNatWord]
      exact ⟨_, by omega, b1.seq (b2.seq (b3.seq b4))⟩)
    (encUnary R) tSch (bs, []) with ⟨tL, htL, s12⟩
  dsimp only [stkOf] at htL s12
  simp only [update_mkTapes8_kSched, encList_nil] at s12
  set stF := loopFinalState (sliceChunkRevStep b) (encUnary R) (bs, [])
  have hstF2 : stF.2 = (sliceBitChunks b R bs).reverse := by
    have h := loopFinalState_sliceChunkRevStep b (encUnary R) bs []
    simpa [stF, length_encUnary] using h
  have hstF1 : stF.1.length ≤ bs.length :=
    length_loopFinalState_sliceChunkRevStep_fst_le b (encUnary R) bs []
  rw [hstF2] at s12
  have s13 := tmDropWord_computesInTime kWork2 stF.1 tW2
    (mkTapes8 [] [] [] [] (encodeDelimWord (encUnary b) ++ tW3)
      (encodeDelimWord (encList (encNatWord b) (sliceBitChunks b R bs).reverse) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork2] at s13
  have s14 := tmDropWord_computesInTime kWork3 (encUnary b) tW3
    (mkTapes8 [] [] [] tW2 []
      (encodeDelimWord (encList (encNatWord b) (sliceBitChunks b R bs).reverse) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3, length_encUnary] at s14
  have s15 := tmMoveWord_computesInTime kWork4 kWork0 kIO (by decide) (by decide) (by decide)
    (encList (encNatWord b) (sliceBitChunks b R bs).reverse) tW4 [] []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s15
  rcases bmRevList_computesStageLe (encNatWord b) (sliceBitChunks b R bs).reverse
    tW2 tW3 tW4 tW5 tSch with ⟨tR, htR, s16⟩
  dsimp only at htR
  simp only [List.reverse_reverse] at s16
  have hlen_rev := length_encList_reverse (encNatWord b) (sliceBitChunks b R bs)
  have hlen_ch := length_encList_sliceBitChunks b R bs
  have hbL := loopStepsAux_sliceChunkRevStep_le b (encUnary R) (bs, [])
  simp only [length_encUnary] at hbL
  simp only [hlen_rev, hlen_ch] at s15 htR
  simp only [encPair, encBits, id, length_encUnary, List.length_append,
    length_encodeDelimWord] at s1 s2 s3 s5 s6 s7 ⊢
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
      (s11.seq (s12.seq (s13.seq (s14.seq (s15.seq s16))))))))))))))⟩
  nlinarith

/-- Universal prefix/zero-extension identity for `takePadBits`: for any `outLen, m, q : ℕ` with
`q < 2 ^ m`, `takePadBits outLen (encodeNatBits m q) = encodeNatBits outLen q`. -/
theorem takePadBits_encodeNatBits_of_lt :
    ∀ (outLen m q : ℕ), q < 2 ^ m →
      takePadBits outLen (encodeNatBits m q) = encodeNatBits outLen q
  | 0, _, _, _ => rfl
  | outLen + 1, 0, q, hq => by
    have hq0 : q = 0 := by omega
    subst hq0
    have h0 : encodeNatBits 0 0 = [] := rfl
    rw [h0, takePadBits_succ, List.headD_nil, List.tail_nil, encodeNatBits_succ_eq]
    congr 1
    simpa [h0] using takePadBits_encodeNatBits_of_lt outLen 0 0 (by decide)
  | outLen + 1, m + 1, q, hq => by
    have hq2 : q / 2 < 2 ^ m := by
      rw [Nat.pow_succ] at hq
      omega
    rw [encodeNatBits_succ_eq, takePadBits_succ, List.headD_cons, List.tail_cons,
      encodeNatBits_succ_eq, takePadBits_encodeNatBits_of_lt outLen m (q / 2) hq2]

/-- Single step of `bmCarrySaveEmitBits`: consumes `((b, W), (encodeNatBits W c, encodeNatBits W carry))`
on `kIO` and produces `(encodeNatBits b ((c + carry) % 2 ^ b), encodeNatBits W ((c + carry) / 2 ^ b))`
on `kIO` in `O(W)` steps (`1 ≤ b ≤ W`). -/
def bmCarrySaveStep : BitMachine :=
  bmSeq (bmPairMap bmId bmRippleAdd)
    (bmSeq
      (bmFanout (bmSeq bmFst bmSnd) (bmSeq (bmPairMap bmFst bmId) bmSliceDropBits))
      (bmFanout (bmSeq bmSnd bmFst) (bmSeq (bmPairMap bmId bmSnd) bmTakePadBits)))

theorem bmCarrySaveStep_computesInTime {b W : ℕ} (hb1 : 1 ≤ b) (hbW : b ≤ W)
    (c carry : ℕ) (hc : c < 2 ^ W) (hcarry : carry < 2 ^ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 350 * W + 800,
      bmCarrySaveStep.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) (encPair encBits encBits)
          ((b, W), (encodeNatBits W c, encodeNatBits W carry))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair encBits encBits
          (encodeNatBits b ((c + carry) % 2 ^ b), encodeNatBits W ((c + carry) / 2 ^ b))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S_add := { p : ℕ × ℕ // p.1 < 2 ^ W ∧ p.2 < 2 ^ W }
  have hadd_stage : ComputesStageLe bmRippleAdd
      (fun s : S_add => encPair encBits encBits (encodeNatBits W s.1.1, encodeNatBits W s.1.2))
      (encodeNatBits (W + 1))
      (fun s : S_add => s.1.1 + s.1.2)
      (fun _ => 9 * W + 16) := by
    intro ⟨⟨x, y⟩, hx, hy⟩ u2 u3 u4 u5 uS
    exact bmRippleAdd_unsigned_computesInTime W x y hx hy u2 u3 u4 u5 uS
  have p1 := bmPairMap_computesStageLe
    (bmId_computesStageLe (encPair encUnary encUnary))
    hadd_stage
  have p2 := bmFanout_computesStageLe
    (bmSeq_computesStageLe
      (bmFst_computesStageLe (encPair encUnary encUnary) encBits)
      (bmSnd_computesStageLe encUnary encUnary))
    (bmSeq_computesStageLe
      (bmPairMap_computesStageLe
        (bmFst_computesStageLe encUnary encUnary)
        (bmId_computesStageLe encBits))
      bmSliceDropBits_computesStageLe)
  have p3 := bmFanout_computesStageLe
    (bmSeq_computesStageLe
      (bmSnd_computesStageLe encUnary (encPair encBits encBits))
      (bmFst_computesStageLe encBits encBits))
    (bmSeq_computesStageLe
      (bmPairMap_computesStageLe
        (bmId_computesStageLe encUnary)
        (bmSnd_computesStageLe encBits encBits))
      bmTakePadBits_computesStageLe)
  rcases p1 ((b, W), (⟨(c, carry), hc, hcarry⟩ : S_add)) tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  dsimp only [id] at ht1 s1
  rcases p2 ((b, W), encodeNatBits (W + 1) (c + carry)) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  dsimp only [id] at ht2 s2
  rcases p3 (W, (takePadBits b (encodeNatBits (W + 1) (c + carry)),
    (encodeNatBits (W + 1) (c + carry)).drop b)) tW2 tW3 tW4 tW5 tSch with ⟨t3, ht3, s3⟩
  dsimp only [id] at ht3 s3
  have hdecomp : encodeNatBits (W + 1) (c + carry) =
      encodeNatBits b ((c + carry) % 2 ^ b) ++
        encodeNatBits (W + 1 - b) ((c + carry) / 2 ^ b) := by
    have hW1 : W + 1 = b + (W + 1 - b) := by omega
    conv_lhs => rw [hW1, encodeNatBits_add b (W + 1 - b) (c + carry)]
    rw [encodeNatBits_mod_two_pow_of_le (le_refl b) (c + carry)]
  have htake : takePadBits b (encodeNatBits (W + 1) (c + carry)) =
      encodeNatBits b ((c + carry) % 2 ^ b) := by
    rw [hdecomp, takePadBits_eq_take_of_le b _ (by simp),
      List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  have hdrop : (encodeNatBits (W + 1) (c + carry)).drop b =
      encodeNatBits (W + 1 - b) ((c + carry) / 2 ^ b) := by
    rw [hdecomp, List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append,
      encodeNatBits_length, Nat.sub_self, List.drop]
  have hcarry'_lt : (c + carry) / 2 ^ b < 2 ^ (W + 1 - b) := by
    have hsum : c + carry < 2 ^ (W + 1) := by
      rw [Nat.pow_succ']
      omega
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      Nat.sub_add_cancel (by omega)]
    exact hsum
  have hpad : takePadBits W ((encodeNatBits (W + 1) (c + carry)).drop b) =
      encodeNatBits W ((c + carry) / 2 ^ b) := by
    rw [hdrop]
    exact takePadBits_encodeNatBits_of_lt W (W + 1 - b) ((c + carry) / 2 ^ b) hcarry'_lt
  rw [htake] at s2
  rw [htake, hpad] at s3
  simp only [encPair, encBits, id, length_encUnary, encodeNatBits_length, length_takePadBits,
    List.length_drop, List.length_append, length_encodeDelimWord] at ht1 ht2 ht3
  exact ⟨t1 + (t2 + t3), by omega, s1.seq (s2.seq s3)⟩

@[simp]
theorem encodeNatBits_zero (w : ℕ) :
    encodeNatBits w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [encodeNatBits_succ_eq, Nat.zero_div, ih, List.replicate_succ]
    rfl

theorem carry_div_two_pow_lt {b W c carry : ℕ} (hb1 : 1 ≤ b)
    (hc : c < 2 ^ W) (hcarry : carry < 2 ^ W) :
    (c + carry) / 2 ^ b < 2 ^ W := by
  have h2b : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb1
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  nlinarith

/-- Step function for `bmCarrySaveLoop` over bounded chunks `{ c : ℕ // c < 2 ^ W }`. -/
def carrySaveSubStep {b W : ℕ} (hb1 : 1 ≤ b) (c : { x : ℕ // x < 2 ^ W })
    (st : { q : ℕ // q < 2 ^ W } × List Bool) : { q : ℕ // q < 2 ^ W } × List Bool :=
  (⟨(c.1 + st.1.1) / 2 ^ b, carry_div_two_pow_lt hb1 c.2 st.1.2⟩,
   (encodeNatBits b ((c.1 + st.1.1) % 2 ^ b)).reverse ++ st.2)

theorem loopListFinalState_carrySaveSubStep_spec {b W : ℕ} (hb1 : 1 ≤ b) :
    ∀ (cs : List { x : ℕ // x < 2 ^ W }) (carry : { q : ℕ // q < 2 ^ W }) (accRev : List Bool),
      let stF := loopListFinalState (carrySaveSubStep hb1) cs (carry, accRev)
      ((encodeNatBits W stF.1.1).reverse ++ stF.2).reverse =
        accRev.reverse ++ encodeNatBits (cs.length * b + W)
          (carry.1 + evalBaseChunks b (cs.map Subtype.val)) ∧
      carry.1 + evalBaseChunks b (cs.map Subtype.val) < 2 ^ (cs.length * b + W)
  | [], carry, accRev => by
    simp only [loopListFinalState_nil, List.length_nil, Nat.zero_mul, Nat.zero_add,
      List.map_nil, evalBaseChunks, Nat.add_zero, List.reverse_append, List.reverse_reverse,
      true_and]
    exact carry.2
  | c :: cs, carry, accRev => by
    let carry' : { q : ℕ // q < 2 ^ W } :=
      ⟨(c.1 + carry.1) / 2 ^ b, carry_div_two_pow_lt hb1 c.2 carry.2⟩
    let chunk := encodeNatBits b ((c.1 + carry.1) % 2 ^ b)
    rcases loopListFinalState_carrySaveSubStep_spec hb1 cs carry' (chunk.reverse ++ accRev)
      with ⟨heq, hlt⟩
    simp only [loopListFinalState_cons, carrySaveSubStep]
    rw [heq]
    simp only [List.reverse_append, List.reverse_reverse, List.append_assoc,
      List.length_cons, List.map_cons, evalBaseChunks]
    have htotal : carry.1 + (c.1 + 2 ^ b * evalBaseChunks b (cs.map Subtype.val)) =
        (c.1 + carry.1) + 2 ^ b * evalBaseChunks b (cs.map Subtype.val) := by ring
    have hdiv_mod : (c.1 + carry.1) % 2 ^ b + 2 ^ b * carry'.1 = c.1 + carry.1 :=
      Nat.mod_add_div (c.1 + carry.1) (2 ^ b)
    have hval : (c.1 + carry.1) + 2 ^ b * evalBaseChunks b (cs.map Subtype.val) =
        (c.1 + carry.1) % 2 ^ b + 2 ^ b * (carry'.1 + evalBaseChunks b (cs.map Subtype.val)) := by
      linarith
    have hlen_eq : (cs.length + 1) * b + W = b + (cs.length * b + W) := by ring
    have hbits : chunk ++ encodeNatBits (cs.length * b + W)
          (carry'.1 + evalBaseChunks b (cs.map Subtype.val)) =
        encodeNatBits ((cs.length + 1) * b + W)
          (carry.1 + (c.1 + 2 ^ b * evalBaseChunks b (cs.map Subtype.val))) := by
      rw [htotal, hlen_eq,
        encodeNatBits_add b (cs.length * b + W)
          ((c.1 + carry.1) + 2 ^ b * evalBaseChunks b (cs.map Subtype.val))]
      congr 1
      · rw [encodeNatBits_add_mul_two_pow]
        exact encodeNatBits_mod_two_pow_of_le (le_refl b) (c.1 + carry.1)
      · congr 1
        rw [mul_comm (2 ^ b), Nat.add_mul_div_right _ _ (by positivity)]
    rw [hbits]
    refine ⟨rfl, ?_⟩
    have hrem_lt : (c.1 + carry.1) % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
    rw [htotal, hval, hlen_eq, pow_add]
    nlinarith

theorem loopListStepsAux_carrySaveSubStep_le {b W : ℕ} (hb1 : 1 ≤ b) :
    ∀ (cs : List { x : ℕ // x < 2 ^ W }) (st : { q : ℕ // q < 2 ^ W } × List Bool),
      loopListStepsAux (carrySaveSubStep hb1)
        (fun _ _ _ => 385 * W + 860) cs st ≤
      cs.length * (385 * W + 861) + 1
  | [], _ => by simp [loopListStepsAux]
  | c :: cs, st => by
    simp only [loopListStepsAux_cons, List.length_cons]
    have ih := loopListStepsAux_carrySaveSubStep_le hb1 cs (carrySaveSubStep hb1 c st)
    nlinarith

theorem loopFinalState_consBit (b : Bool) :
    ∀ (cnt acc : List Bool),
      loopFinalState (fun xs => b :: xs) cnt acc = List.replicate cnt.length b ++ acc
  | [], acc => rfl
  | _ :: cnt, acc => by
    rw [loopFinalState_cons, loopFinalState_consBit b cnt (b :: acc), List.length_cons,
      List.replicate_succ', List.append_assoc, List.singleton_append]

theorem loopStepsAux_consBit (b : Bool) :
    ∀ (cnt acc : List Bool),
      loopStepsAux (fun xs => b :: xs) (fun _ => 1) cnt acc = 2 * cnt.length + 1
  | [], _ => rfl
  | _ :: cnt, acc => by
    rw [loopStepsAux_cons, loopStepsAux_consBit b cnt (b :: acc), List.length_cons]
    ring

theorem consBit_loopDelimWord_computesInTime (b : Bool) (kCnt kDst : TapeIdx) (hne : kCnt ≠ kDst)
    (cnt restCnt acc restDst : List Bool) (T : ∀ j : TapeIdx, List (BitTapeAlphabet j)) :
    ((tmConsBit b kDst).loopDelimWord kCnt).ComputesInTime
      (Function.update (Function.update T kDst (encodeDelimWord acc ++ restDst))
        kCnt (encodeDelimWord cnt ++ restCnt))
      (Function.update (Function.update T kDst
        (encodeDelimWord (List.replicate cnt.length b ++ acc) ++ restDst))
        kCnt restCnt)
      (2 * cnt.length + 1) := by
  let stkOf : List Bool → (∀ j : TapeIdx, List (BitTapeAlphabet j)) := fun xs =>
    Function.update T kDst (encodeDelimWord xs ++ restDst)
  have h := BitMachine.ComputesInTime.loopDelimWord_state kCnt
    (fun xs => b :: xs) (fun _ => 1) stkOf
    (fun xs tailCnt => by
      dsimp only [stkOf]
      have h1 := tmConsBit_computesInTime b kDst
        (Function.update (Function.update T kDst (encodeDelimWord xs ++ restDst)) kCnt tailCnt)
        xs restDst (by simp [Function.update_of_ne hne.symm])
      simpa only [Function.update_comm hne, Function.update_idem] using h1)
    cnt restCnt acc
  dsimp only [stkOf] at h
  rwa [loopFinalState_consBit, loopStepsAux_consBit] at h

theorem length_encList_encNatWord {α : Type} (W : ℕ) (f : α → ℕ) :
    ∀ (cs : List α), (encList (fun c => encNatWord W (f c)) cs).length = cs.length * (2 * W + 2)
  | [] => by simp
  | c :: cs => by
    simp only [encList_cons, List.length_append, length_encodeDelimWord,
      length_encNatWord, List.length_cons, length_encList_encNatWord W f cs]
    ring

/-- Inner loop of `bmCarrySaveEmitBits`: consumes `((b, W), cs)` and produces
`encodeNatBits (cs.length * b + W) (evalBaseChunks b cs)` on `kIO`. -/
def bmCarrySaveLoop : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork5).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kWork2).seq
            ((tmDupWord kWork5 kWork0 kIO).seq
              (bmSnd.seq
                ((tmPushEmpty kWork3).seq
                  (((tmConsBit false kWork3).loopDelimWord kIO).seq
                    ((tmPushEmpty kWork4).seq
                      ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                          ((tmMoveWord kWork3 kWork1 kIO).seq
                            (tmPackPairFromRev.seq
                              ((tmDupWord kWork5 kWork0 kWork1).seq
                                ((tmRevMoveWord kWork1 kWork0).seq
                                  (tmPackPairFromRev.seq
                                    (bmCarrySaveStep.seq
                                      ((tmPopFirstSubwordRev kIO kWork0).seq
                                        ((tmRevMoveWord kWork0 kWork1).seq
                                          ((tmConcatRevWord kWork1 kWork4).seq
                                            ((tmPopFirstSubwordRev kIO kWork0).seq
                                              ((tmDropWord kIO).seq
                                                (tmRevMoveWord kWork0 kWork3))))))))))))).loopNonEmptyWord kWork2).seq
                        ((tmDropWord kWork5).seq
                          ((tmConcatRevWord kWork3 kWork4).seq
                            (tmRevMoveWord kWork4 kIO)))))))))))))

theorem bmCarrySaveLoop_computesInTime {b W : ℕ} (hb1 : 1 ≤ b) (hbW : b ≤ W)
    (cs : List { x : ℕ // x < 2 ^ W })
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ cs.length * (400 * W + 890) + 45 * W + 95,
      bmCarrySaveLoop.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary)
          (encList (fun c : { x : ℕ // x < 2 ^ W } => encNatWord W c.1)) ((b, W), cs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeNatBits (cs.length * b + W)
          (evalBaseChunks b (cs.map Subtype.val))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let encC : { x : ℕ // x < 2 ^ W } → List Bool := fun c => encNatWord W c.1
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encPair encUnary encUnary (b, W)) ++
      encodeDelimWord (encList encC cs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork5 (by decide)
    (encPair encUnary encUnary (b, W)).reverse [] tW5
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encC cs))) [] [] tW2 tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork5, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encC cs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4
      (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encC cs).reverse) [] tW2 tW3 tW4
      (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encC cs).reverse [] tW2
    (mkTapes8 [] [] [] [] tW3 tW4
      (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmDupWord_computesInTime kWork5 kWork0 kIO (by decide) (by decide) (by decide)
    (encPair encUnary encUnary (b, W)) tW5 [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encC cs) ++ tW2) tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s6
  rcases bmSnd_computesStageLe (encA := encUnary) (encB := encUnary) (b, W)
    (encodeDelimWord (encList encC cs) ++ tW2) tW3 tW4
    (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch with ⟨tSnd, htSnd, s7⟩
  dsimp only at htSnd s7
  have s8 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 (encodeDelimWord (encUnary W)) [] []
      (encodeDelimWord (encList encC cs) ++ tW2) tW3 tW4
      (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s8
  have s9 := consBit_loopDelimWord_computesInTime false kIO kWork3 (by decide)
    (encUnary W) [] [] tW3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encC cs) ++ tW2) [] tW4
      (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kIO, List.append_nil,
    length_encUnary, ← encodeNatBits_zero] at s9
  have s10 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord (encList encC cs) ++ tW2)
      (encodeDelimWord (encodeNatBits W 0) ++ tW3) tW4
      (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s10
  let stepBound : { x : ℕ // x < 2 ^ W } → List { x : ℕ // x < 2 ^ W } →
      { q : ℕ // q < 2 ^ W } × List Bool → ℕ :=
    fun _ _ _ => 385 * W + 860
  let stkOf : { q : ℕ // q < 2 ^ W } × List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] []
      (encodeDelimWord (encodeNatBits W st.1.1) ++ tW3)
      (encodeDelimWord st.2 ++ tW4)
      (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encC
    (carrySaveSubStep hb1) stepBound stkOf
    (fun c rem st restW2 => by
      rcases st with ⟨carry, accRev⟩
      dsimp only [stkOf, carrySaveSubStep, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encC c) ++ encodeWordStack (rem.map encC)) restW2 []
        (mkTapes8 [] [] [] []
          (encodeDelimWord (encodeNatBits W carry.1) ++ tW3)
          (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      change (tmPopFirstSubwordRev kWork2 kWork0).ComputesInTime _
        (mkTapes8 [] (encodeDelimWord (encodeNatBits W c.1).reverse) []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          (encodeDelimWord (encodeNatBits W carry.1) ++ tW3)
          (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
        ((encodeNatBits W c.1).length + 2) at b1
      have b2 := tmMoveWord_computesInTime kWork3 kWork1 kIO (by decide) (by decide) (by decide)
        (encodeNatBits W carry.1) tW3 [] []
        (mkTapes8 [] (encodeDelimWord (encodeNatBits W c.1).reverse) []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          [] (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, update_mkTapes8_kIO,
        List.append_nil] at b2
      have b3 := tmPackPairFromRev_computesInTime
        (encodeNatBits W c.1) (encodeNatBits W carry.1)
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord accRev ++ tW4)
        (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch
      have b4 := tmDupWord_computesInTime kWork5 kWork0 kWork1 (by decide) (by decide) (by decide)
        (encPair encUnary encUnary (b, W)) tW5 [] []
        (mkTapes8 (encodeDelimWord (encPair encBits encBits (encodeNatBits W c.1, encodeNatBits W carry.1)))
          [] [] (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4) [] tSch)
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
        List.append_nil] at b4
      have b5 := tmRevMoveWord_computesInTime kWork1 kWork0 (by decide)
        (encPair encUnary encUnary (b, W)) [] []
        (mkTapes8 (encodeDelimWord (encPair encBits encBits (encodeNatBits W c.1, encodeNatBits W carry.1)))
          [] [] (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, List.append_nil] at b5
      have b6 := tmPackPairFromRev_computesInTime
        (encPair encUnary encUnary (b, W))
        (encPair encBits encBits (encodeNatBits W c.1, encodeNatBits W carry.1))
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord accRev ++ tW4)
        (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch
      rcases bmCarrySaveStep_computesInTime hb1 hbW c.1 carry.1 c.2 carry.2
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord accRev ++ tW4)
        (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch with ⟨tStep, htStep, b7⟩
      let lowBits := encodeNatBits b ((c.1 + carry.1) % 2 ^ b)
      let nextCarryBits := encodeNatBits W ((c.1 + carry.1) / 2 ^ b)
      have b8 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
        (encodeDelimWord lowBits ++ encodeDelimWord nextCarryBits) [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b8
      have b9 := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
        lowBits.reverse [] []
        (mkTapes8 (encodeDelimWord (encodeDelimWord nextCarryBits)) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b9
      have b10 := tmConcatRevWord_computesInTime kWork1 kWork4 (by decide)
        lowBits accRev [] tW4
        (mkTapes8 (encodeDelimWord (encodeDelimWord nextCarryBits)) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 [] (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork4, List.append_nil] at b10
      have b11 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
        (encodeDelimWord nextCarryBits) [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord (lowBits.reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord] at b11
      have b12 := tmDropWord_computesInTime kIO [] []
        (mkTapes8 [] (encodeDelimWord nextCarryBits.reverse) []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord (lowBits.reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at b12
      have b13 := tmRevMoveWord_computesInTime kWork0 kWork3 (by decide)
        nextCarryBits.reverse [] tW3
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          [] (encodeDelimWord (lowBits.reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encPair encUnary encUnary (b, W)) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b13
      have hseq := b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (b6.seq (b7.seq
        (b8.seq (b9.seq (b10.seq (b11.seq (b12.seq b13)))))))))))
      simp only [lowBits, nextCarryBits, encPair, encBits, id, length_encUnary,
        encodeNatBits_length, List.length_append, length_encodeDelimWord] at hseq
      exact ⟨_, by omega, hseq⟩)
    cs tW2 (⟨0, by positivity⟩, []) with ⟨tL, htL, s11⟩
  dsimp only [stkOf, stepBound] at htL s11
  simp only [update_mkTapes8_kWork2] at s11
  set stF := loopListFinalState (carrySaveSubStep hb1) cs (⟨0, by positivity⟩, [])
  rcases loopListFinalState_carrySaveSubStep_spec hb1 cs ⟨0, by positivity⟩ [] with ⟨hbitsF, _⟩
  simp only [List.reverse_nil, List.nil_append, zero_add] at hbitsF
  have hbitsF' : ((encodeNatBits W stF.1.1).reverse ++ stF.2).reverse =
      encodeNatBits (cs.length * b + W) (evalBaseChunks b (cs.map Subtype.val)) := hbitsF
  have s12 := tmDropWord_computesInTime kWork5 (encPair encUnary encUnary (b, W)) tW5
    (mkTapes8 [] [] [] tW2
      (encodeDelimWord (encodeNatBits W stF.1.1) ++ tW3)
      (encodeDelimWord stF.2 ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5] at s12
  have s13 := tmConcatRevWord_computesInTime kWork3 kWork4 (by decide)
    (encodeNatBits W stF.1.1) stF.2 tW3 tW4
    (mkTapes8 [] [] [] tW2 [] [] tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork4, encodeNatBits_length] at s13
  have s14 := tmRevMoveWord_computesInTime kWork4 kIO (by decide)
    ((encodeNatBits W stF.1.1).reverse ++ stF.2) tW4 []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kIO, List.append_nil] at s14
  have hlen_stF : ((encodeNatBits W stF.1.1).reverse ++ stF.2).length = cs.length * b + W := by
    rw [← List.length_reverse, hbitsF', encodeNatBits_length]
  rw [hbitsF', hlen_stF] at s14
  have hlen_cs : (encList encC cs).length = cs.length * (2 * W + 2) :=
    length_encList_encNatWord W Subtype.val cs
  have hbL := loopListStepsAux_carrySaveSubStep_le hb1 cs (⟨0, by positivity⟩, [])
  simp only [encPair, length_encUnary, hlen_cs, List.length_append,
    length_encodeDelimWord] at s1 s2 s3 s5 s6 s12 htSnd ⊢
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
      (s11.seq (s12.seq (s13.seq s14))))))))))))⟩
  nlinarith

/-- **Stage 29 (`bmCarrySaveEmitBits`)**:
Consumes `(outLen, ((b, W), cs))` on `kIO` (where `1 ≤ b ≤ W` and each `c ∈ cs` is `< 2 ^ W`)
and produces `carrySaveEmitBits b outLen cs 0 = encodeNatBits outLen (evalBaseChunks b cs)` on
`kIO` in $O(|cs| \cdot W + \text{outLen})$ `TM2.step` transitions. -/
def bmCarrySaveEmitBits : BitMachine :=
  bmSeq (bmPairMap bmId bmCarrySaveLoop) bmTakePadBits

theorem bmCarrySaveEmitBits_computesInTime {b W : ℕ} (hb1 : 1 ≤ b) (hbW : b ≤ W)
    (outLen : ℕ) (cs : List { x : ℕ // x < 2 ^ W })
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ cs.length * (460 * W + 950) + 160 * W + 25 * outLen + 360,
      bmCarrySaveEmitBits.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary
          (encPair (encPair encUnary encUnary)
            (encList (fun c : { x : ℕ // x < 2 ^ W } => encNatWord W c.1)))
          (outLen, ((b, W), cs))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (carrySaveEmitBits b outLen (cs.map Subtype.val) 0))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S_loop := Unit
  have hloop_stage : ComputesStageLe bmCarrySaveLoop
      (fun _ : S_loop => encPair (encPair encUnary encUnary)
        (encList (fun c : { x : ℕ // x < 2 ^ W } => encNatWord W c.1)) ((b, W), cs))
      (fun _ : S_loop => encodeNatBits (cs.length * b + W)
        (evalBaseChunks b (cs.map Subtype.val)))
      (fun _ => ())
      (fun _ => cs.length * (400 * W + 890) + 45 * W + 95) := by
    intro _ u2 u3 u4 u5 uS
    exact bmCarrySaveLoop_computesInTime hb1 hbW cs u2 u3 u4 u5 uS
  have p1 := bmPairMap_computesStageLe
    (bmId_computesStageLe encUnary)
    hloop_stage
  rcases p1 (outLen, ()) tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  dsimp only [id] at ht1 s1
  rcases bmTakePadBits_computesStageLe
    (outLen, encodeNatBits (cs.length * b + W) (evalBaseChunks b (cs.map Subtype.val)))
    tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  dsimp only [id] at ht2 s2
  rcases loopListFinalState_carrySaveSubStep_spec hb1 cs ⟨0, by positivity⟩ [] with ⟨_, hlt⟩
  simp only [zero_add] at hlt
  have hpad : takePadBits outLen
      (encodeNatBits (cs.length * b + W) (evalBaseChunks b (cs.map Subtype.val))) =
      carrySaveEmitBits b outLen (cs.map Subtype.val) 0 := by
    rw [takePadBits_encodeNatBits_of_lt _ _ _ hlt,
      carrySaveEmitBits_eq_encodeNatBits, zero_add]
  rw [hpad] at s2
  have hlen_cs : (encList (fun c : { x : ℕ // x < 2 ^ W } => encNatWord W c.1) cs).length =
      cs.length * (2 * W + 2) :=
    length_encList_encNatWord W Subtype.val cs
  simp only [encPair, length_encUnary, encodeNatBits_length, hlen_cs,
    List.length_append, length_encodeDelimWord] at ht1 ht2
  have hb_le : cs.length * b ≤ cs.length * W := Nat.mul_le_mul_left cs.length hbW
  exact ⟨t1 + t2, by nlinarith, s1.seq s2⟩

end IntMul

#print axioms IntMul.bmRunRaw_evalsToInTime
#print axioms IntMul.bmSeq_computesStageLe
#print axioms IntMul.bmFanout_computesStageLe
#print axioms IntMul.bmPairMap_computesStageLe
#print axioms IntMul.bmIte_computesStageLe
#print axioms IntMul.bmIterLoop_computesStageLe
#print axioms IntMul.bmRevList_computesStageLe
#print axioms IntMul.bmFoldList_computesStageLe
#print axioms IntMul.bmAppendList_computesStageLe
#print axioms IntMul.bmMapWithCtx_computesStageLe
#print axioms IntMul.bmDeinterleaveList_computesStageLe
#print axioms IntMul.bmZipList_computesStageLe
#print axioms IntMul.bmZipWithCtx_computesStageLe
#print axioms IntMul.bmRippleAdd_unsigned_computesInTime
#print axioms IntMul.bmRippleAdd_signed_computesInTime
#print axioms IntMul.bmUnsignedButterfly_computesInTime
#print axioms IntMul.bmSignedButterfly_computesInTime
#print axioms IntMul.bmCondSubStep_computesInTime
#print axioms IntMul.bmSliceBitChunks_computesInTime
#print axioms IntMul.bmCarrySaveEmitBits_computesInTime

