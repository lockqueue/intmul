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
import IntMul.TMStages
import IntMul.TMArithStages

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# Dependent-Context Stage Evaluation (`StageEval`), Unary Schedule Arithmetic, & Fixed-Point Complex Stages (`IntMul.TMStageEval`)

This module builds the dependent-context evaluation algebra (`StageEval`, `encDepPair`) on top of
`ComputesStageLe` (`IntMul.TMStages`) and `IntMul.TMArithStages`, together with linear-time unary
arithmetic stages (`bmLenUnary`, `bmHalfLenUnary`, `bmUnaryBitLength`, `bmUnaryLog2`,
`bmUnaryClog2`, `bmUnaryCeilDiv`, `bmUnaryDiv`, `bmUnaryMul`, `bmUnaryTwoPow`, `bmRangeList`,
`bmListGetD`), fixed-width signed integer stages, and fixed-point complex stages on the uniform 8-stack binary machine (`Turing.FinTM2`, Section 8 (`sec:lean`)).
-/

namespace IntMul

open Turing

/-! ## 1. Dependent-Context Stage Algebra (`encDepPair`, `StageEval`) & Indexed Loop/Fold/Map/Zip Lemmas -/

/-- Dependent pair encoding over a shared ambient context `s : S`. -/
def encDepPair {S : Type} (u1 u2 : S → List Bool) (s : S) : List Bool :=
  encodeDelimWord (u1 s) ++ encodeDelimWord (u2 s)

@[simp]
theorem encDepPair_eq_encPair {S : Type} (u1 u2 : S → List Bool) (s : S) :
    encDepPair u1 u2 s = encPair id id (u1 s, u2 s) := rfl

@[simp]
theorem length_encDepPair {S : Type} (u1 u2 : S → List Bool) (s : S) :
    (encDepPair u1 u2 s).length = 2 * (u1 s).length + 2 * (u2 s).length + 4 := by
  simp [encDepPair]
  omega

/-- Dependent-context stage evaluation: for every ambient state `s : S`, `m : BitMachine`
transforms `encodeDelimWord (u s)` on `kIO` into `encodeDelimWord (v s)` on `kIO` in `t ≤ b s`
steps while preserving stacks `kWork2..kWork5` and `kSched`. -/
def StageEval {S : Type} (m : BitMachine) (u v : S → List Bool) (b : S → ℕ) : Prop :=
  ComputesStageLe m u v id b

namespace StageEval

theorem mono {S : Type} {m : BitMachine} {u v : S → List Bool} {b1 b2 : S → ℕ}
    (h : StageEval m u v b1) (hle : ∀ s : S, b1 s ≤ b2 s) :
    StageEval m u v b2 :=
  ComputesStageLe.mono h hle

theorem congr_in {S : Type} {m : BitMachine} {u1 u2 v : S → List Bool} {b : S → ℕ}
    (h : StageEval m u1 v b) (heq : ∀ s : S, u1 s = u2 s) :
    StageEval m u2 v b := by
  intro s tW2 tW3 tW4 tW5 tSch
  rw [← heq s]
  exact h s tW2 tW3 tW4 tW5 tSch

theorem congr_out {S : Type} {m : BitMachine} {u v1 v2 : S → List Bool} {b : S → ℕ}
    (h : StageEval m u v1 b) (heq : ∀ s : S, v1 s = v2 s) :
    StageEval m u v2 b := by
  intro s tW2 tW3 tW4 tW5 tSch
  dsimp only [id]
  rw [← heq s]
  exact h s tW2 tW3 tW4 tW5 tSch

theorem pullback {S S' : Type} (f : S' → S) {m : BitMachine}
    {u v : S → List Bool} {b : S → ℕ}
    (h : StageEval m u v b) :
    StageEval m (fun s' => u (f s')) (fun s' => v (f s')) (fun s' => b (f s')) :=
  fun s' tW2 tW3 tW4 tW5 tSch => h (f s') tW2 tW3 tW4 tW5 tSch

theorem of_computesStageLe {S α β : Type} {m : BitMachine}
    {encA : α → List Bool} {encB : β → List Bool}
    {fn : α → β} {bound : α → ℕ}
    (h : ComputesStageLe m encA encB fn bound) (x : S → α) :
    StageEval m (fun s => encA (x s)) (fun s => encB (fn (x s))) (fun s => bound (x s)) :=
  fun s tW2 tW3 tW4 tW5 tSch => h (x s) tW2 tW3 tW4 tW5 tSch

theorem const {S : Type} {m : BitMachine} {u0 v0 : List Bool} {b0 : ℕ}
    (h : ∀ tW2 tW3 tW4 tW5 tSch : List Bool,
      ∃ t ≤ b0,
        m.ComputesInTime
          (mkTapes8 (encodeDelimWord u0) [] [] tW2 tW3 tW4 tW5 tSch)
          (mkTapes8 (encodeDelimWord v0) [] [] tW2 tW3 tW4 tW5 tSch) t) :
    StageEval (S := S) m (fun _ => u0) (fun _ => v0) (fun _ => b0) :=
  fun _ => h

theorem id_stage {S : Type} (u : S → List Bool) :
    StageEval bmId u u (fun _ => 1) :=
  bmId_computesStageLe u

theorem constEmpty {S : Type} (u : S → List Bool) :
    StageEval bmConstEmpty u (fun _ => []) (fun s => (u s).length + 2) :=
  bmConstEmpty_computesStageLe u

theorem seq {S : Type} {m1 m2 : BitMachine}
    {u v w : S → List Bool} {b1 b2 : S → ℕ}
    (h1 : StageEval m1 u v b1) (h2 : StageEval m2 v w b2) :
    StageEval (bmSeq m1 m2) u w (fun s => b1 s + b2 s) :=
  bmSeq_computesStageLe h1 h2

theorem fst {S : Type} (u1 u2 : S → List Bool) :
    StageEval bmFst (encDepPair u1 u2) u1
      (fun s => 2 * (u1 s).length + 2 * (u2 s).length + 7) := by
  intro s tW2 tW3 tW4 tW5 tSch
  exact bmFst_computesStageLe id id (u1 s, u2 s) tW2 tW3 tW4 tW5 tSch

theorem snd {S : Type} (u1 u2 : S → List Bool) :
    StageEval bmSnd (encDepPair u1 u2) u2
      (fun s => (u1 s).length + 2 * (u2 s).length + 6) := by
  intro s tW2 tW3 tW4 tW5 tSch
  exact bmSnd_computesStageLe id id (u1 s, u2 s) tW2 tW3 tW4 tW5 tSch

theorem dup {S : Type} (u : S → List Bool) :
    StageEval bmDup u (encDepPair u u)
      (fun s => 3 * (u s).length + 7) :=
  bmDup_computesStageLe u

theorem swap {S : Type} (u1 u2 : S → List Bool) :
    StageEval bmSwap (encDepPair u1 u2) (encDepPair u2 u1)
      (fun s => 2 * (u1 s).length + 2 * (u2 s).length + 8) := by
  intro s tW2 tW3 tW4 tW5 tSch
  exact bmSwap_computesStageLe id id (u1 s, u2 s) tW2 tW3 tW4 tW5 tSch

theorem fanout {S : Type} {m1 m2 : BitMachine}
    {u v1 v2 : S → List Bool} {b1 b2 : S → ℕ}
    (h1 : StageEval m1 u v1 b1) (h2 : StageEval m2 u v2 b2) :
    StageEval (bmFanout m1 m2) u (encDepPair v1 v2)
      (fun s => b1 s + b2 s + 4 * (u s).length + 4 * (v1 s).length + 2 * (v2 s).length + 21) :=
  bmFanout_computesStageLe h1 h2

theorem pairMap {S : Type} {m1 m2 : BitMachine}
    {u1 u2 v1 v2 : S → List Bool} {b1 b2 : S → ℕ}
    (h1 : StageEval m1 u1 v1 b1) (h2 : StageEval m2 u2 v2 b2) :
    StageEval (bmPairMap m1 m2) (encDepPair u1 u2) (encDepPair v1 v2)
      (fun s => b1 s + b2 s + 11 * (u1 s).length + 12 * (u2 s).length +
        4 * (v1 s).length + 2 * (v2 s).length + 50) := by
  have hf1 := seq (fst u1 u2) h1
  have hf2 := seq (snd u1 u2) h2
  refine (fanout hf1 hf2).mono (fun s => ?_)
  simp only [length_encDepPair]
  omega

theorem ite {S : Type} {mCond mTrue mFalse : BitMachine}
    {u v : S → List Bool} {condFn : S → Bool} {bCond bTrue bFalse : S → ℕ}
    (hCond : StageEval mCond u (fun s => encBool (condFn s)) bCond)
    (hTrue : ∀ s : S, condFn s = true →
      ∀ tW2 tW3 tW4 tW5 tSch : List Bool,
        ∃ t ≤ bTrue s,
          mTrue.ComputesInTime
            (mkTapes8 (encodeDelimWord (u s)) [] [] tW2 tW3 tW4 tW5 tSch)
            (mkTapes8 (encodeDelimWord (v s)) [] [] tW2 tW3 tW4 tW5 tSch) t)
    (hFalse : ∀ s : S, condFn s = false →
      ∀ tW2 tW3 tW4 tW5 tSch : List Bool,
        ∃ t ≤ bFalse s,
          mFalse.ComputesInTime
            (mkTapes8 (encodeDelimWord (u s)) [] [] tW2 tW3 tW4 tW5 tSch)
            (mkTapes8 (encodeDelimWord (v s)) [] [] tW2 tW3 tW4 tW5 tSch) t) :
    StageEval (bmIte mCond mTrue mFalse) u v
      (fun s => bCond s + (if condFn s then bTrue s else bFalse s) + 4 * (u s).length + 15) := by
  intro s tW2 tW3 tW4 tW5 tSch
  dsimp only [id]
  have s1 := tmDupWord_computesInTime kIO kWork0 kWork5 (by decide) (by decide) (by decide)
    (u s) [] [] tW5 (mkTapes8 [] [] [] tW2 tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork5,
    List.append_nil] at s1
  rcases hCond s tW2 tW3 tW4 (encodeDelimWord (u s) ++ tW5) tSch with ⟨tC, htC, s2⟩
  dsimp only [id] at s2
  have s3 := tmMoveWord_computesInTime kIO kWork0 kWork4 (by decide) (by decide) (by decide)
    (encBool (condFn s)) [] [] tW4
    (mkTapes8 [] [] [] tW2 tW3 [] (encodeDelimWord (u s) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork4,
    List.append_nil] at s3
  have s4 := tmMoveWord_computesInTime kWork5 kWork0 kIO (by decide) (by decide) (by decide)
    (u s) tW5 [] []
    (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord (encBool (condFn s)) ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s4
  cases hcf : condFn s with
  | false =>
    rcases hFalse s hcf tW2 tW3 tW4 tW5 tSch with ⟨tF, htF, sF⟩
    have s5 := BitMachine.ComputesInTime.branchDelimBit kWork4
      (M_false := mFalse) (M_true := mTrue) false tW4
      (T₁ := mkTapes8 (encodeDelimWord (u s)) [] [] tW2 tW3 [] tW5 tSch)
      (by simpa [update_mkTapes8_kWork4] using sF)
    simp only [update_mkTapes8_kWork4] at s5
    simp only [hcf, encBool, Bool.false_eq_true, ↓reduceIte] at s2 s3 s4 ⊢
    refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq s5)))⟩
    simp only [List.length_singleton]
    omega
  | true =>
    rcases hTrue s hcf tW2 tW3 tW4 tW5 tSch with ⟨tT, htT, sT⟩
    have s5 := BitMachine.ComputesInTime.branchDelimBit kWork4
      (M_false := mFalse) (M_true := mTrue) true tW4
      (T₁ := mkTapes8 (encodeDelimWord (u s)) [] [] tW2 tW3 [] tW5 tSch)
      (by simpa [update_mkTapes8_kWork4] using sT)
    simp only [update_mkTapes8_kWork4] at s5
    simp only [hcf, encBool, ↓reduceIte] at s2 s3 s4 ⊢
    refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq s5)))⟩
    simp only [List.length_singleton]
    omega

theorem ite_stage {S : Type} {mCond mTrue mFalse : BitMachine}
    {u vTrue vFalse : S → List Bool} {condFn : S → Bool} {bCond bTrue bFalse : S → ℕ}
    (hCond : StageEval mCond u (fun s => encBool (condFn s)) bCond)
    (hTrue : StageEval mTrue u vTrue bTrue)
    (hFalse : StageEval mFalse u vFalse bFalse) :
    StageEval (bmIte mCond mTrue mFalse) u
      (fun s => if condFn s then vTrue s else vFalse s)
      (fun s => bCond s + (if condFn s then bTrue s else bFalse s) + 4 * (u s).length + 15) := by
  refine ite hCond (fun s hs tW2 tW3 tW4 tW5 tSch => ?_) (fun s hs tW2 tW3 tW4 tW5 tSch => ?_)
  · simp only [hs, ↓reduceIte]
    exact hTrue s tW2 tW3 tW4 tW5 tSch
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact hFalse s tW2 tW3 tW4 tW5 tSch

end StageEval

/-- Keep the input context `u s` as the first element of a pair while evaluating `m` into the second. -/
def bmKeepCtx (m : BitMachine) : BitMachine :=
  bmFanout bmId m

/-- Evaluate `m` on the first component of a pair while keeping the second unchanged. -/
def bmMapFst (m : BitMachine) : BitMachine :=
  bmPairMap m bmId

/-- Evaluate `m` on the second component of a pair while keeping the first unchanged. -/
def bmMapSnd (m : BitMachine) : BitMachine :=
  bmPairMap bmId m

/-- Reassociate `(a, (b, c)) ↦ ((a, b), c)`. -/
def bmAssocL : BitMachine :=
  bmFanout (bmFanout bmFst (bmSeq bmSnd bmFst)) (bmSeq bmSnd bmSnd)

/-- Reassociate `((a, b), c) ↦ (a, (b, c))`. -/
def bmAssocR : BitMachine :=
  bmFanout (bmSeq bmFst bmFst) (bmFanout (bmSeq bmFst bmSnd) bmSnd)

namespace StageEval

theorem keepCtx {S : Type} {m : BitMachine} {u v : S → List Bool} {b : S → ℕ}
    (hm : StageEval m u v b) :
    StageEval (bmKeepCtx m) u (encDepPair u v)
      (fun s => b s + 8 * (u s).length + 2 * (v s).length + 22) :=
  (fanout (id_stage u) hm).mono (fun _ => by omega)

theorem mapFst {S : Type} {m : BitMachine} {u1 u2 v1 : S → List Bool} {b1 : S → ℕ}
    (hm : StageEval m u1 v1 b1) :
    StageEval (bmMapFst m) (encDepPair u1 u2) (encDepPair v1 u2)
      (fun s => b1 s + 11 * (u1 s).length + 14 * (u2 s).length + 4 * (v1 s).length + 51) :=
  (pairMap hm (id_stage u2)).mono (fun _ => by omega)

theorem mapSnd {S : Type} {m : BitMachine} {u1 u2 v2 : S → List Bool} {b2 : S → ℕ}
    (hm : StageEval m u2 v2 b2) :
    StageEval (bmMapSnd m) (encDepPair u1 u2) (encDepPair u1 v2)
      (fun s => b2 s + 15 * (u1 s).length + 12 * (u2 s).length + 2 * (v2 s).length + 51) :=
  (pairMap (id_stage u1) hm).mono (fun _ => by omega)

theorem assocL {S : Type} (u1 u2 u3 : S → List Bool) :
    StageEval bmAssocL (encDepPair u1 (encDepPair u2 u3)) (encDepPair (encDepPair u1 u2) u3)
      (fun s => 60 * (u1 s).length + 60 * (u2 s).length + 60 * (u3 s).length + 220) := by
  have p1 := fst u1 (encDepPair u2 u3)
  have p2 := seq (snd u1 (encDepPair u2 u3)) (fst u2 u3)
  have p3 := seq (snd u1 (encDepPair u2 u3)) (snd u2 u3)
  refine (fanout (fanout p1 p2) p3).mono (fun s => ?_)
  simp only [length_encDepPair]
  omega

theorem assocR {S : Type} (u1 u2 u3 : S → List Bool) :
    StageEval bmAssocR (encDepPair (encDepPair u1 u2) u3) (encDepPair u1 (encDepPair u2 u3))
      (fun s => 60 * (u1 s).length + 60 * (u2 s).length + 60 * (u3 s).length + 220) := by
  have p1 := seq (fst (encDepPair u1 u2) u3) (fst u1 u2)
  have p2 := seq (fst (encDepPair u1 u2) u3) (snd u1 u2)
  have p3 := snd (encDepPair u1 u2) u3
  refine (fanout p1 (fanout p2 p3)).mono (fun s => ?_)
  simp only [length_encDepPair]
  omega

/-! ### Indexed Counter Loop (`StageEval.iterLoop_idx`) & List Combinators in `StageEval` -/

/-- Direct induction for `body.loopDelimWord kSched` over `rem` unary steps starting at index `i`. -/
theorem loopDelimWord_indexed_le {S : Type} {body : BitMachine}
    {k : S → ℕ} {u : S → ℕ → List Bool} {B : S → ℕ}
    (hbody : StageEval (S := { p : S × ℕ // p.2 < k p.1 }) body
      (fun p => u p.val.1 p.val.2) (fun p => u p.val.1 (p.val.2 + 1)) (fun p => B p.val.1))
    (s : S) :
    ∀ (rem i : ℕ) (_hle : i + rem ≤ k s) (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ rem * (B s + 1) + 1,
        (body.loopDelimWord kSched).ComputesInTime
          (mkTapes8 (encodeDelimWord (u s i)) [] [] tW2 tW3 tW4 tW5
            (encodeDelimWord (encUnary rem) ++ tSch))
          (mkTapes8 (encodeDelimWord (u s (i + rem))) [] [] tW2 tW3 tW4 tW5 tSch) t
  | 0, i, _, tW2, tW3, tW4, tW5, tSch => by
    simp only [Nat.add_zero, Nat.zero_mul, encUnary, List.replicate_zero]
    refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, mkTapes8_kSched, update_mkTapes8_kSched, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | rem + 1, i, hle, tW2, tW3, tW4, tW5, tSch => by
    have hi : i < k s := by omega
    have hle' : (i + 1) + rem ≤ k s := by omega
    have hpop : (body.loopDelimWord kSched).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord (u s i)) [] [] tW2 tW3 tW4 tW5
            (encodeDelimWord (encUnary (rem + 1)) ++ tSch)⟩ =
        some ⟨some (some body.main), default,
          mkTapes8 (encodeDelimWord (u s i)) [] [] tW2 tW3 tW4 tW5
            (encodeDelimWord (encUnary rem) ++ tSch)⟩ := by
      simp only [encUnary, List.replicate_succ, BitMachine.loopDelimWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons,
        List.cons_append, mkTapes8_kSched, update_mkTapes8_kSched, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    rcases hbody ⟨(s, i), hi⟩ tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary rem) ++ tSch) with
      ⟨t1, ht1, ⟨hb1⟩⟩
    dsimp only [id] at ht1 hb1
    have hb_lifted := BitMachine.loopDelimWord_body_evalsToInTime_concrete kSched body hb1
    rcases loopDelimWord_indexed_le hbody s rem (i + 1) hle' tW2 tW3 tW4 tW5 tSch with
      ⟨t2, ht2, ⟨hb2⟩⟩
    have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hb_lifted) hb2
    rw [show (i + 1) + rem = i + (rem + 1) by omega] at hcomb
    refine ⟨(t1 + 1) + t2, ?_, ⟨hcomb⟩⟩
    calc (t1 + 1) + t2 ≤ (B s + 1) + (rem * (B s + 1) + 1) := by omega
      _ = (rem + 1) * (B s + 1) + 1 := by ring

/-- **Indexed Counter Loop Theorem (`StageEval.iterLoop_idx`)**:
If `body` advances `u s i` to `u s (i + 1)` in `≤ B s` steps for every `i < k s`, then
`bmIterLoop body` transforms `encDepPair (encUnary (k s)) (u s 0)` into `u s (k s)` in
`≤ k s * (B s + 3) + 2 * (u s 0).length + 10` steps. -/
theorem iterLoop_idx {S : Type} {body : BitMachine}
    {k : S → ℕ} {u : S → ℕ → List Bool} {B : S → ℕ}
    (hbody : StageEval (S := { p : S × ℕ // p.2 < k p.1 }) body
      (fun p => u p.val.1 p.val.2) (fun p => u p.val.1 (p.val.2 + 1)) (fun p => B p.val.1)) :
    StageEval (bmIterLoop body)
      (encDepPair (fun s => encUnary (k s)) (fun s => u s 0))
      (fun s => u s (k s))
      (fun s => k s * (B s + 3) + 2 * (u s 0).length + 10) := by
  intro s tW2 tW3 tW4 tW5 tSch
  dsimp only [id]
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary (k s)) ++ encodeDelimWord (u s 0)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kSched (by decide)
    (encUnary (k s)).reverse [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord (u s 0))) [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kSched, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (u s 0)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary (k s)) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (u s 0).reverse) [] tW2 tW3 tW4 tW5
      (encodeDelimWord (encUnary (k s)) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (u s 0).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary (k s)) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  rcases loopDelimWord_indexed_le hbody s (k s) 0 (by omega) tW2 tW3 tW4 tW5 tSch with
    ⟨tL, htL, s6⟩
  simp only [Nat.zero_add] at s6
  simp only [length_encUnary] at s1 s2
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))⟩
  nlinarith

/-- Direct induction for `bmFoldList`'s inner `loopNonEmptyWord kWork2` over remaining list suffix `rem`. -/
theorem foldList_indexed_loop_le {S α : Type} {stepM : BitMachine}
    {encElem : S → α → List Bool} {xs : S → List α}
    {uAcc : S → ℕ → List Bool} {B L_elem L_acc : S → ℕ}
    (hstep : StageEval (S := { p : S × ℕ // p.2 < (xs p.1).length }) stepM
      (encDepPair (fun p => encElem p.val.1 ((xs p.val.1)[p.val.2]'p.property))
        (fun p => uAcc p.val.1 p.val.2))
      (fun p => uAcc p.val.1 (p.val.2 + 1))
      (fun p => B p.val.1))
    (hL_elem : ∀ (s : S) (i : ℕ) (hi : i < (xs s).length),
      (encElem s ((xs s)[i]'hi)).length ≤ L_elem s)
    (hL_acc : ∀ (s : S) (i : ℕ), i < (xs s).length → (uAcc s i).length ≤ L_acc s)
    (s : S) :
    ∀ (rem : List α) (i : ℕ) (_hrem : (xs s).drop i = rem)
      (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ rem.length * (B s + 2 * L_elem s + 2 * L_acc s + 10) + 1,
        (((tmPopFirstSubwordRev kWork2 kWork0).seq
            (tmPackPairFromRev.seq stepM)).loopNonEmptyWord kWork2).ComputesInTime
          (mkTapes8 (encodeDelimWord (uAcc s i)) [] []
            (encodeDelimWord (encList (encElem s) rem) ++ tW2) tW3 tW4 tW5 tSch)
          (mkTapes8 (encodeDelimWord (uAcc s (i + rem.length))) [] []
            tW2 tW3 tW4 tW5 tSch) t
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
    let body := (tmPopFirstSubwordRev kWork2 kWork0).seq (tmPackPairFromRev.seq stepM)
    have hpop : (body.loopNonEmptyWord kWork2).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord (uAcc s i)) [] []
            (encodeDelimWord (encList (encElem s) (x :: rem)) ++ tW2) tW3 tW4 tW5 tSch⟩ =
        some ⟨some (some body.main), default,
          mkTapes8 (encodeDelimWord (uAcc s i)) [] []
            (encodeDelimWord (encList (encElem s) (x :: rem)) ++ tW2) tW3 tW4 tW5 tSch⟩ := by
      simp only [encList_cons,
        encodeDelimWord_append_eq_head_tail (encElem s x) (encList (encElem s) rem),
        encodeDelimWord_cons, List.cons_append, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, mkTapes8_kWork2,
        update_mkTapes8_kWork2, List.head?_cons, List.tail_cons, Option.getD_some, cond_false]
    have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
      (encodeDelimWord (encElem s x) ++ encList (encElem s) rem) tW2 []
      (mkTapes8 (encodeDelimWord (uAcc s i)) [] [] [] tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
      unconsDelimWord_encodeDelimWord_append] at b1
    have b2 := tmPackPairFromRev_computesInTime (encElem s x) (uAcc s i)
      (encodeDelimWord (encList (encElem s) rem) ++ tW2) tW3 tW4 tW5 tSch
    rcases hstep ⟨(s, i), hi⟩ (encodeDelimWord (encList (encElem s) rem) ++ tW2) tW3 tW4 tW5 tSch
      with ⟨ts, hts, b3⟩
    dsimp only [id, encDepPair] at hts b3
    rw [hx_eq] at b3
    have ⟨hbody⟩ := b1.seq (b2.seq b3)
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete kWork2 body hbody
    rcases foldList_indexed_loop_le hstep hL_elem hL_acc s rem (i + 1) hrem' tW2 tW3 tW4 tW5 tSch
      with ⟨t2, ht2, ⟨hih⟩⟩
    have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hbody_lifted) hih
    rw [show (i + 1) + rem.length = i + (x :: rem).length by simp [Nat.add_assoc, Nat.add_comm 1]]
      at hcomb
    have hle_e : (encElem s x).length ≤ L_elem s := by
      rw [← hx_eq]
      exact hL_elem s i hi
    have hle_a : (uAcc s i).length ≤ L_acc s := hL_acc s i hi
    refine ⟨_, ?_, ⟨hcomb⟩⟩
    simp only [List.length_cons]
    calc (((encElem s x).length + 2 +
            ((uAcc s i).length + 2 + (1 + ((uAcc s i).length + 2 + ((encElem s x).length + 2))) +
              ts)) + 1) + t2
        ≤ (B s + 2 * L_elem s + 2 * L_acc s + 10) +
          (rem.length * (B s + 2 * L_elem s + 2 * L_acc s + 10) + 1) := by omega
      _ = (rem.length + 1) * (B s + 2 * L_elem s + 2 * L_acc s + 10) + 1 := by ring

/-- **Indexed List Fold Theorem (`StageEval.foldList_idx`)**:
If `stepM` advances `(encElem s ((xs s)[i]), uAcc s i)` to `uAcc s (i + 1)` in `≤ B s` steps for
all `i < (xs s).length`, then `bmFoldList stepM` transforms
`encDepPair (encList (encElem s) (xs s)) (uAcc s 0)` into `uAcc s (xs s).length` in linear time. -/
theorem foldList_idx {S α : Type} {stepM : BitMachine}
    {encElem : S → α → List Bool} {xs : S → List α}
    {uAcc : S → ℕ → List Bool} {B L_elem L_acc : S → ℕ}
    (hstep : StageEval (S := { p : S × ℕ // p.2 < (xs p.1).length }) stepM
      (encDepPair (fun p => encElem p.val.1 ((xs p.val.1)[p.val.2]'p.property))
        (fun p => uAcc p.val.1 p.val.2))
      (fun p => uAcc p.val.1 (p.val.2 + 1))
      (fun p => B p.val.1))
    (hL_elem : ∀ (s : S) (i : ℕ) (hi : i < (xs s).length),
      (encElem s ((xs s)[i]'hi)).length ≤ L_elem s)
    (hL_acc : ∀ (s : S) (i : ℕ), i < (xs s).length → (uAcc s i).length ≤ L_acc s) :
    StageEval (bmFoldList stepM)
      (encDepPair (fun s => encList (encElem s) (xs s)) (fun s => uAcc s 0))
      (fun s => uAcc s (xs s).length)
      (fun s =>
        (xs s).length * (B s + 2 * L_elem s + 2 * L_acc s + 10) +
        2 * (encList (encElem s) (xs s)).length + 2 * (uAcc s 0).length + 10) := by
  intro s tW2 tW3 tW4 tW5 tSch
  dsimp only [id]
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList (encElem s) (xs s)) ++ encodeDelimWord (uAcc s 0)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList (encElem s) (xs s)).reverse [] tW2
    (mkTapes8 (encodeDelimWord (encodeDelimWord (uAcc s 0))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (uAcc s 0)) [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList (encElem s) (xs s)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (uAcc s 0).reverse) []
      (encodeDelimWord (encList (encElem s) (xs s)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (uAcc s 0).reverse [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList (encElem s) (xs s)) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  rcases foldList_indexed_loop_le hstep hL_elem hL_acc s (xs s) 0 rfl tW2 tW3 tW4 tW5 tSch
    with ⟨tL, htL, s6⟩
  simp only [Nat.zero_add] at s6
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))⟩
  omega

/-- Direct bound on `loopListStepsAux` when every element step is bounded by `C`. -/
theorem loopListStepsAux_le_length_mul {α β : Type} (nextSt : α → β → β)
    (stepBound : α → List α → β → ℕ) (C : ℕ) :
    ∀ (xs : List α) (st : β),
      (∀ x ∈ xs, ∀ rem st', stepBound x rem st' ≤ C) →
      loopListStepsAux nextSt stepBound xs st ≤ xs.length * (C + 1) + 1
  | [], _, _ => by simp [loopListStepsAux]
  | x :: xs, st, hC => by
    simp only [loopListStepsAux_cons, List.length_cons]
    have hx : stepBound x xs st ≤ C := hC x List.mem_cons_self xs st
    have ih := loopListStepsAux_le_length_mul nextSt stepBound C xs (nextSt x st)
      (fun y hy rem st' => hC y (List.mem_cons_of_mem x hy) rem st')
    calc 1 + stepBound x xs st + loopListStepsAux nextSt stepBound xs (nextSt x st)
        ≤ 1 + C + (xs.length * (C + 1) + 1) := by omega
      _ = (xs.length + 1) * (C + 1) + 1 := by ring

theorem length_encList_le_of_forall_le {α : Type} (encElem : α → List Bool) (L : ℕ) :
    ∀ (xs : List α), (∀ x ∈ xs, (encElem x).length ≤ L) →
      (encList encElem xs).length ≤ xs.length * (2 * L + 2)
  | [], _ => by simp
  | x :: xs, hL => by
    simp only [encList_cons, List.length_append, length_encodeDelimWord, List.length_cons]
    have hx := hL x List.mem_cons_self
    have ih := length_encList_le_of_forall_le encElem L xs
      (fun y hy => hL y (List.mem_cons_of_mem x hy))
    calc 2 * (encElem x).length + 2 + (encList encElem xs).length
        ≤ 2 * L + 2 + xs.length * (2 * L + 2) := by omega
      _ = (xs.length + 1) * (2 * L + 2) := by ring

/-- Attach membership proofs `x ∈ xs` to a sublist `l`. -/
def attachSublist {α : Type} (xs : List α) :
    ∀ (l : List α), (∀ x ∈ l, x ∈ xs) → List { x : α // x ∈ xs }
  | [], _ => []
  | x :: l, hl =>
    ⟨x, hl x List.mem_cons_self⟩ ::
      attachSublist xs l (fun y hy => hl y (List.mem_cons_of_mem x hy))

theorem map_AttachSublist {α β : Type} (xs : List α) (f : α → β) :
    ∀ (l : List α) (hl : ∀ x ∈ l, x ∈ xs),
      (attachSublist xs l hl).map (fun e => f e.val) = l.map f
  | [], _ => rfl
  | x :: l, _ => congrArg (f x :: ·) (map_AttachSublist xs f l _)

theorem length_attachSublist {α : Type} (xs : List α) :
    ∀ (l : List α) (hl : ∀ x ∈ l, x ∈ xs),
      (attachSublist xs l hl).length = l.length
  | [], _ => rfl
  | _ :: l, _ => congrArg Nat.succ (length_attachSublist xs l _)

theorem mem_of_mem_zip {α β : Type} :
    ∀ {xs : List α} {ys : List β} {p : α × β},
      p ∈ List.zip xs ys → p.1 ∈ xs ∧ p.2 ∈ ys
  | [], _, _, hp => by cases hp
  | _, [], _, hp => by rw [List.zip_nil_right] at hp; cases hp
  | x :: xs, y :: ys, p, hp => by
    rw [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
    · rcases mem_of_mem_zip hp' with ⟨h1, h2⟩
      exact ⟨List.mem_cons_of_mem x h1, List.mem_cons_of_mem y h2⟩

/-- **Context-Preserving List Map Theorem (`StageEval.mapWithCtx_uniform`)**:
If `bodyM` maps `(ctx s, encA s x)` to `encB s (fn s x)` in `≤ B s` steps for every `x ∈ xs s`,
then `bmMapWithCtx bodyM` transforms `(ctx s, encList (encA s) (xs s))` into
`encList (encB s) ((xs s).map (fn s))` in linear time. -/
theorem mapWithCtx_uniform {S α β : Type} {bodyM : BitMachine}
    {ctx : S → List Bool} {xs : S → List α}
    {encA : S → α → List Bool} {encB : S → β → List Bool}
    {fn : S → α → β} {B L_A L_B : S → ℕ}
    (hbody : StageEval (S := { p : S × α // p.2 ∈ xs p.1 }) bodyM
      (encDepPair (fun p => ctx p.val.1) (fun p => encA p.val.1 p.val.2))
      (fun p => encB p.val.1 (fn p.val.1 p.val.2))
      (fun p => B p.val.1))
    (hLA : ∀ (s : S) (x : α), x ∈ xs s → (encA s x).length ≤ L_A s)
    (hLB : ∀ (s : S) (x : α), x ∈ xs s → (encB s (fn s x)).length ≤ L_B s) :
    StageEval (bmMapWithCtx bodyM)
      (encDepPair ctx (fun s => encList (encA s) (xs s)))
      (fun s => encList (encB s) ((xs s).map (fn s)))
      (fun s =>
        (xs s).length * (B s + 4 * (ctx s).length + 6 * L_A s + 20 * L_B s + 40) +
        3 * (ctx s).length + 28) := by
  intro s tW2 tW3 tW4 tW5 tSch
  dsimp only [id]
  let ElemS := { x : α // x ∈ xs s }
  let xsSub : List ElemS := attachSublist (xs s) (xs s) (fun _ hx => hx)
  have henc_xsSub : encList (fun e : ElemS => encA s e.val) xsSub = encList (encA s) (xs s) := by
    dsimp [encList, xsSub]
    rw [map_AttachSublist]
  have hmap_fn : xsSub.map (fun e : ElemS => fn s e.val) = (xs s).map (fn s) :=
    map_AttachSublist (xs s) (fn s) (xs s) (fun _ hx => hx)
  have hxsSub_len : xsSub.length = (xs s).length :=
    length_attachSublist (xs s) (xs s) (fun _ hx => hx)
  have hsub_stage : ComputesStageLe bodyM
      (encPair (fun (_ : Unit) => ctx s) (fun e : ElemS => encA s e.val))
      (encB s)
      (fun p : Unit × ElemS => fn s p.2.val)
      (fun _ => B s) := by
    intro ⟨_, ⟨x, hx⟩⟩ u2 u3 u4 u5 uS
    exact hbody ⟨(s, x), hx⟩ u2 u3 u4 u5 uS
  rcases bmMapWithCtx_computesStageLe hsub_stage ((), xsSub) tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht, hcomp⟩
  dsimp only at ht
  change (bmMapWithCtx bodyM).ComputesInTime
    (mkTapes8 (encodeDelimWord (encodeDelimWord (ctx s) ++
      encodeDelimWord (encList (fun e : ElemS => encA s e.val) xsSub)))
      [] [] tW2 tW3 tW4 tW5 tSch)
    (mkTapes8 (encodeDelimWord (encList (encB s) (xsSub.map (fun e : ElemS => fn s e.val))))
      [] [] tW2 tW3 tW4 tW5 tSch) t at hcomp
  rw [henc_xsSub, hmap_fn] at ht hcomp
  have hloop_le := loopListStepsAux_le_length_mul
    (fun (e : ElemS) (a : List β) => fn s e.val :: a)
    (fun (e : ElemS) _ _ =>
      B s + 4 * (ctx s).length + 2 * (encA s e.val).length +
        2 * (encB s (fn s e.val)).length + 17)
    (B s + 4 * (ctx s).length + 2 * L_A s + 2 * L_B s + 17)
    xsSub []
    (fun e _ _ => by
      have ha := hLA s e.val e.property
      have hb := hLB s e.val e.property
      omega)
  have hlenA_le : (encList (encA s) (xs s)).length ≤ (xs s).length * (2 * L_A s + 2) :=
    length_encList_le_of_forall_le (encA s) (L_A s) (xs s) (hLA s)
  have hlenB_le : (encList (encB s) ((xs s).map (fn s))).length ≤
      (xs s).length * (2 * L_B s + 2) := by
    have h := length_encList_le_of_forall_le (encB s) (L_B s) ((xs s).map (fn s))
      (fun y hy => by
        rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
        exact hLB s x hx)
    simpa [List.length_map] using h
  rw [hxsSub_len] at hloop_le
  refine ⟨t, ?_, hcomp⟩
  nlinarith

/-- **Context-Preserving List ZipWith Theorem (`StageEval.zipWithCtx_uniform`)**:
If `bodyM` maps `(ctx s, (encA s x, encB s y))` to `encD s (fn s x y)` in `≤ B s` steps for every
`(x, y) ∈ List.zip (xs s) (ys s)`, then `bmZipWithCtx bodyM` transforms
`(ctx s, (encList (encA s) (xs s), encList (encB s) (ys s)))` into
`encList (encD s) (List.zipWith (fn s) (xs s) (ys s))` in linear time. -/
theorem zipWithCtx_uniform {S α β δ : Type} {bodyM : BitMachine}
    {ctx : S → List Bool} {xs : S → List α} {ys : S → List β}
    (hlen : ∀ s : S, (xs s).length = (ys s).length)
    {encA : S → α → List Bool} {encB : S → β → List Bool} {encD : S → δ → List Bool}
    {fn : S → α → β → δ} {B L_A L_B L_D : S → ℕ}
    (hbody : StageEval (S := { p : S × (α × β) // p.2 ∈ List.zip (xs p.1) (ys p.1) }) bodyM
      (encDepPair (fun p => ctx p.val.1)
        (encDepPair (fun p => encA p.val.1 p.val.2.1) (fun p => encB p.val.1 p.val.2.2)))
      (fun p => encD p.val.1 (fn p.val.1 p.val.2.1 p.val.2.2))
      (fun p => B p.val.1))
    (hLA : ∀ (s : S) (x : α), x ∈ xs s → (encA s x).length ≤ L_A s)
    (hLB : ∀ (s : S) (y : β), y ∈ ys s → (encB s y).length ≤ L_B s)
    (hLD : ∀ (s : S) (p : α × β), p ∈ List.zip (xs s) (ys s) →
      (encD s (fn s p.1 p.2)).length ≤ L_D s) :
    StageEval (bmZipWithCtx bodyM)
      (encDepPair ctx
        (encDepPair (fun s => encList (encA s) (xs s)) (fun s => encList (encB s) (ys s))))
      (fun s => encList (encD s) (List.zipWith (fn s) (xs s) (ys s)))
      (fun s =>
        (xs s).length * (B s + 4 * (ctx s).length + 340 * L_A s + 340 * L_B s + 24 * L_D s + 600) +
        60 * (ctx s).length + 450) := by
  have hzip : StageEval bmZipList
      (encDepPair (fun s => encList (encA s) (xs s)) (fun s => encList (encB s) (ys s)))
      (fun s => encList (encPair (encA s) (encB s)) (List.zip (xs s) (ys s)))
      (fun s => 26 * (encPair (encList (encA s)) (encList (encB s)) (xs s, ys s)).length + 50) := by
    intro s tW2 tW3 tW4 tW5 tSch
    exact bmZipList_computesStageLe (encA s) (encB s) ⟨(xs s, ys s), hlen s⟩ tW2 tW3 tW4 tW5 tSch
  have hp1 := mapSnd (u1 := ctx) hzip
  have hp2 := mapWithCtx_uniform
    (ctx := ctx)
    (xs := fun s => List.zip (xs s) (ys s))
    (encA := fun s p => encPair (encA s) (encB s) p)
    (encB := encD)
    (fn := fun s p => fn s p.1 p.2)
    (B := B)
    (L_A := fun s => 2 * L_A s + 2 * L_B s + 4)
    (L_B := L_D)
    hbody
    (fun s p hp => by
      simp only [length_encPair]
      rcases mem_of_mem_zip hp with ⟨hxMem, hyMem⟩
      have hx := hLA s p.1 hxMem
      have hy := hLB s p.2 hyMem
      omega)
    hLD
  refine (congr_out (seq hp1 hp2) (fun s => by rw [map_zip_eq_zipWith])).mono (fun s => ?_)
  have hlenA_le : (encList (encA s) (xs s)).length ≤ (xs s).length * (2 * L_A s + 2) :=
    length_encList_le_of_forall_le (encA s) (L_A s) (xs s) (hLA s)
  have hlenB_le : (encList (encB s) (ys s)).length ≤ (xs s).length * (2 * L_B s + 2) := by
    rw [hlen s]
    exact length_encList_le_of_forall_le (encB s) (L_B s) (ys s) (hLB s)
  have hlen_zip : (List.zip (xs s) (ys s)).length = (xs s).length := by
    simp [hlen s]
  have hlen_encZip := length_encList_zip_eq (encA s) (encB s) (xs s) (ys s) (hlen s)
  simp only [encDepPair, encPair, List.length_append, length_encodeDelimWord,
    hlen_zip, hlen_encZip]
  nlinarith

theorem revList {S α : Type} (encElem : S → α → List Bool) (xs : S → List α) :
    StageEval bmRevList (fun s => encList (encElem s) (xs s))
      (fun s => encList (encElem s) (xs s).reverse)
      (fun s => 7 * (encList (encElem s) (xs s)).length + 12) :=
  fun s tW2 tW3 tW4 tW5 tSch => bmRevList_computesStageLe (encElem s) (xs s) tW2 tW3 tW4 tW5 tSch

theorem appendList {S α : Type} (encElem : S → α → List Bool) (xs ys : S → List α) :
    StageEval bmAppendList
      (encDepPair (fun s => encList (encElem s) (xs s)) (fun s => encList (encElem s) (ys s)))
      (fun s => encList (encElem s) (xs s ++ ys s))
      (fun s => 8 * (encList (encElem s) (xs s)).length +
        2 * (encList (encElem s) (ys s)).length + 14) :=
  fun s tW2 tW3 tW4 tW5 tSch =>
    bmAppendList_computesStageLe (encElem s) (xs s, ys s) tW2 tW3 tW4 tW5 tSch

theorem deinterleaveList_stage {S α : Type} (encElem : S → α → List Bool) (xs : S → List α) :
    StageEval bmDeinterleaveList
      (fun s => encList (encElem s) (xs s))
      (encDepPair (fun s => encList (encElem s) (deinterleaveList (xs s)).1)
                  (fun s => encList (encElem s) (deinterleaveList (xs s)).2))
      (fun s => 24 * (encList (encElem s) (xs s)).length + 55) :=
  fun s tW2 tW3 tW4 tW5 tSch =>
    bmDeinterleaveList_computesStageLe (encElem s) (xs s) tW2 tW3 tW4 tW5 tSch

theorem zipList {S α β : Type} (encA : S → α → List Bool) (encB : S → β → List Bool)
    (xs : S → List α) (ys : S → List β) (hlen : ∀ s : S, (xs s).length = (ys s).length) :
    StageEval bmZipList
      (encDepPair (fun s => encList (encA s) (xs s)) (fun s => encList (encB s) (ys s)))
      (fun s => encList (encPair (encA s) (encB s)) (List.zip (xs s) (ys s)))
      (fun s => 26 * (encPair (encList (encA s)) (encList (encB s)) (xs s, ys s)).length + 50) :=
  fun s tW2 tW3 tW4 tW5 tSch =>
    bmZipList_computesStageLe (encA s) (encB s) ⟨(xs s, ys s), hlen s⟩ tW2 tW3 tW4 tW5 tSch

theorem flattenBits {S : Type} (xss : S → List (List Bool)) :
    StageEval bmFlattenBits
      (fun s => encList encBits (xss s))
      (fun s => (xss s).flatten)
      (fun s => 11 * (encList encBits (xss s)).length + 18) :=
  fun s tW2 tW3 tW4 tW5 tSch => bmFlattenBits_computesStageLe (xss s) tW2 tW3 tW4 tW5 tSch

theorem takePadBits_stage {S : Type} (b : S → ℕ) (bs : S → List Bool) :
    StageEval bmTakePadBits
      (encDepPair (fun s => encUnary (b s)) bs)
      (fun s => takePadBits (b s) (bs s))
      (fun s => 9 * b s + 6 * (bs s).length + 29) :=
  fun s tW2 tW3 tW4 tW5 tSch => bmTakePadBits_computesStageLe (b s, bs s) tW2 tW3 tW4 tW5 tSch

theorem dropBits {S : Type} (b : S → ℕ) (bs : S → List Bool) :
    StageEval bmDropBits
      (encDepPair (fun s => encUnary (b s)) bs)
      (fun s => (bs s).drop (b s))
      (fun s => 8 * b s + 6 * (bs s).length + 28) :=
  fun s tW2 tW3 tW4 tW5 tSch => bmDropBits_computesStageLe (b s, bs s) tW2 tW3 tW4 tW5 tSch

theorem appendBits {S : Type} (u1 u2 : S → List Bool) :
    StageEval bmAppendBits (encDepPair u1 u2) (fun s => u1 s ++ u2 s)
      (fun s => 2 * (u1 s).length + 2 * (u2 s).length + 8) :=
  fun s tW2 tW3 tW4 tW5 tSch => bmAppendBits_computesStageLe (u1 s, u2 s) tW2 tW3 tW4 tW5 tSch

end StageEval

/-! ## 2. Linear-Time Unary Arithmetic & Schedule Parameter Primitives (`bmLenUnary`, `bmHalfLenUnary`, `bmUnaryBitLength`, `bmUnaryLog2`, `bmUnaryClog2`, `bmUnaryCeilDiv`, `bmUnaryDiv`, `bmUnaryMul`, `bmUnaryTwoPow`, `bmRangeList`, `bmListGetD`) -/

/-- Constant boolean stage: drops input on `kIO` and pushes `encBool b = [b]`. -/
def bmConstBool (b : Bool) : BitMachine :=
  (tmDropWord kIO).seq (tmPushBitWord b kIO)

theorem bmConstBool_computesStageLe {α : Type} (b : Bool) (encA : α → List Bool) :
    ComputesStageLe (bmConstBool b) encA encBool (fun _ => b)
      (fun x => (encA x).length + 2) := by
  intro x tW2 tW3 tW4 tW5 tSch
  have s1 := tmDropWord_computesInTime kIO (encA x) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil] at s1
  have s2 := tmPushBitWord_computesInTime b kIO
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s2
  exact ⟨_, le_rfl, s1.seq s2⟩

/-- Logical NOT on `encBool`: branches on `kWork4` via `bmIte bmId (bmConstBool false) (bmConstBool true)`. -/
def bmBoolNot : BitMachine :=
  bmIte bmId (bmConstBool false) (bmConstBool true)

theorem bmBoolNot_computesStageLe :
    ComputesStageLe bmBoolNot encBool encBool Bool.not (fun _ => 25) := by
  have h := bmIte_computesStageLe (bmId_computesStageLe encBool)
    (bmConstBool_computesStageLe false encBool)
    (bmConstBool_computesStageLe true encBool)
  refine (ComputesStageLe.congr_fn h (fun b => by cases b <;> rfl)).mono (fun b => ?_)
  cases b <;> decide

/-- Logical OR on `encPair encBool encBool`. -/
def bmBoolOr : BitMachine :=
  bmIte bmFst (bmConstBool true) bmSnd

theorem bmBoolOr_computesStageLe :
    ComputesStageLe bmBoolOr (encPair encBool encBool) encBool
      (fun p => p.1 || p.2) (fun _ => 100) := by
  have h := bmIte_computesStageLe (bmFst_computesStageLe encBool encBool)
    (bmConstBool_computesStageLe true (encPair encBool encBool))
    (bmSnd_computesStageLe encBool encBool)
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => by cases a <;> rfl)).mono (fun ⟨a, b⟩ => ?_)
  cases a <;> cases b <;> decide

/-- Logical XOR (`!=`) on `encPair encBool encBool`. -/
def bmBoolXor : BitMachine :=
  bmIte bmFst (bmSeq bmSnd bmBoolNot) bmSnd

theorem bmBoolXor_computesStageLe :
    ComputesStageLe bmBoolXor (encPair encBool encBool) encBool
      (fun p => p.1 != p.2) (fun _ => 100) := by
  have h := bmIte_computesStageLe (bmFst_computesStageLe encBool encBool)
    (bmSeq_computesStageLe (bmSnd_computesStageLe encBool encBool) bmBoolNot_computesStageLe)
    (bmSnd_computesStageLe encBool encBool)
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => by cases a <;> cases b <;> rfl)).mono
    (fun ⟨a, b⟩ => ?_)
  cases a <;> cases b <;> decide

/-- **Unary Length (`bmLenUnary`)**:
Converts any bit-word `bs` on `kIO` into `encUnary bs.length = List.replicate bs.length false`
in `≤ 4 * bs.length + 6` `TM2.step` transitions. -/
def bmLenUnary : BitMachine :=
  (tmMoveWord kIO kWork0 kSched).seq
    ((tmPushEmpty kIO).seq
      ((tmConsBit false kIO).loopDelimWord kSched))

theorem bmLenUnary_computesStageLe {α : Type} (encA : α → List Bool) :
    ComputesStageLe bmLenUnary encA encUnary (fun x => (encA x).length)
      (fun x => 4 * (encA x).length + 6) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmMoveWord_computesInTime kIO kWork0 kSched (by decide) (by decide) (by decide)
    (encA x) [] [] tSch (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kSched,
    List.append_nil] at s1
  have s2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encA x) ++ tSch))
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s2
  have s3 := consBit_loopDelimWord_computesInTime false kSched kIO (by decide)
    (encA x) tSch [] [] (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kIO, update_mkTapes8_kSched, List.append_nil] at s3
  change ((tmConsBit false kIO).loopDelimWord kSched).ComputesInTime _
    (mkTapes8 (encodeDelimWord (encUnary (encA x).length)) [] [] tW2 tW3 tW4 tW5 tSch) _ at s3
  refine ⟨_, ?_, s1.seq (s2.seq s3)⟩
  omega

/-- Pure step for `bmHalfLenUnary`: toggles parity `st.1 : Bool` and increments `st.2 : ℕ` on odd steps. -/
def halfLenPureStep (st : Bool × ℕ) : Bool × ℕ :=
  if st.1 then (false, st.2 + 1) else (true, st.2)

theorem loopFinalState_halfLenPureStep :
    ∀ (bs : List Bool) (q : ℕ),
      (loopFinalState halfLenPureStep bs (false, q)).2 = q + bs.length / 2 ∧
      (loopFinalState halfLenPureStep bs (true, q)).2 = q + (bs.length + 1) / 2
  | [], q => by simp [loopFinalState]
  | _ :: bs, q => by
    rcases loopFinalState_halfLenPureStep bs q with ⟨_, h1⟩
    rcases loopFinalState_halfLenPureStep bs (q + 1) with ⟨h0', _⟩
    simp only [loopFinalState_cons, halfLenPureStep, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, h1, h0']
    refine ⟨trivial, ?_⟩
    omega

theorem loopStepsAux_halfLenPureStep_le :
    ∀ (bs : List Bool) (st : Bool × ℕ),
      loopStepsAux halfLenPureStep (fun _ => 3) bs st ≤ 4 * bs.length + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: bs, st => by
    simp only [loopStepsAux_cons, List.length_cons]
    have ih := loopStepsAux_halfLenPureStep_le bs (halfLenPureStep st)
    omega

/-- **Unary Halving of Bit-Word Length (`bmHalfLenUnary`)**:
Consumes any bit-word `bs` on `kIO` (including `encUnary m`) and emits `encUnary (bs.length / 2)`
on `kIO` in `≤ 6 * bs.length + 12` `TM2.step` transitions. -/
def bmHalfLenUnary : BitMachine :=
  (tmMoveWord kIO kWork0 kSched).seq
    ((tmPushEmpty kIO).seq
      ((tmPushBitWord false kWork2).seq
        (((BitMachine.branchDelimBit kWork2
            (tmPushBitWord true kWork2)
            ((tmConsBit false kIO).seq (tmPushBitWord false kWork2))).loopDelimWord kSched).seq
          (tmDropWord kWork2))))

theorem bmHalfLenUnary_computesStageLe {α : Type} (encA : α → List Bool) :
    ComputesStageLe bmHalfLenUnary encA encUnary (fun x => (encA x).length / 2)
      (fun x => 6 * (encA x).length + 12) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmMoveWord_computesInTime kIO kWork0 kSched (by decide) (by decide) (by decide)
    (encA x) [] [] tSch (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kSched,
    List.append_nil] at s1
  have s2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encA x) ++ tSch))
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s2
  have s3 := tmPushBitWord_computesInTime false kWork2
    (mkTapes8 (encodeDelimWord []) [] [] tW2 tW3 tW4 tW5 (encodeDelimWord (encA x) ++ tSch))
  simp only [update_mkTapes8_kWork2, mkTapes8_kWork2] at s3
  let stkOf : Bool × ℕ → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 (encodeDelimWord (encUnary st.2)) [] []
      (encodeDelimWord [st.1] ++ tW2) tW3 tW4 tW5 []
  rcases BitMachine.ComputesInTime.loopDelimWord_state_le kSched
    halfLenPureStep (fun _ => 3) stkOf
    (fun ⟨p, q⟩ tailSch => by
      dsimp only [stkOf, halfLenPureStep]
      simp only [update_mkTapes8_kSched]
      cases p with
      | false =>
        have c1 := tmPushBitWord_computesInTime true kWork2
          (mkTapes8 (encodeDelimWord (encUnary q)) [] [] tW2 tW3 tW4 tW5 tailSch)
        simp only [update_mkTapes8_kWork2, mkTapes8_kWork2] at c1
        have br := BitMachine.ComputesInTime.branchDelimBit kWork2
          (M_false := tmPushBitWord true kWork2)
          (M_true := (tmConsBit false kIO).seq (tmPushBitWord false kWork2))
          false tW2
          (T₁ := mkTapes8 (encodeDelimWord (encUnary q)) [] [] [] tW3 tW4 tW5 tailSch)
          (by simpa only [update_mkTapes8_kWork2, Bool.false_eq_true, ↓reduceIte] using c1)
        simp only [update_mkTapes8_kWork2, Bool.false_eq_true, ↓reduceIte] at br ⊢
        exact ⟨2, by omega, br⟩
      | true =>
        have c1 := tmConsBit_computesInTime false kIO
          (mkTapes8 (encodeDelimWord (encUnary q)) [] [] tW2 tW3 tW4 tW5 tailSch)
          (encUnary q) [] (by simp)
        simp only [update_mkTapes8_kIO, List.append_nil] at c1
        have hq_succ : false :: encUnary q = encUnary (q + 1) := rfl
        rw [hq_succ] at c1
        have c2 := tmPushBitWord_computesInTime false kWork2
          (mkTapes8 (encodeDelimWord (encUnary (q + 1))) [] [] tW2 tW3 tW4 tW5 tailSch)
        simp only [update_mkTapes8_kWork2, mkTapes8_kWork2] at c2
        have br := BitMachine.ComputesInTime.branchDelimBit kWork2
          (M_false := tmPushBitWord true kWork2)
          (M_true := (tmConsBit false kIO).seq (tmPushBitWord false kWork2))
          true tW2
          (T₁ := mkTapes8 (encodeDelimWord (encUnary q)) [] [] [] tW3 tW4 tW5 tailSch)
          (by simpa only [update_mkTapes8_kWork2, ↓reduceIte] using c1.seq c2)
        simp only [update_mkTapes8_kWork2, ↓reduceIte] at br ⊢
        exact ⟨3, by omega, br⟩)
    (encA x) tSch (false, 0) with ⟨tL, htL, s4⟩
  dsimp only [stkOf] at htL s4
  simp only [update_mkTapes8_kSched] at s4
  set stF := loopFinalState halfLenPureStep (encA x) (false, 0)
  have hstF2 : stF.2 = (encA x).length / 2 := by
    have h := (loopFinalState_halfLenPureStep (encA x) 0).1
    simpa [stF] using h
  rw [hstF2] at s4
  have s5 := tmDropWord_computesInTime kWork2 [stF.1] tW2
    (mkTapes8 (encodeDelimWord (encUnary ((encA x).length / 2))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, List.length_singleton] at s5
  have hbL := loopStepsAux_halfLenPureStep_le (encA x) (false, 0)
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq s5)))⟩
  omega

/-- **Unary Zero (`bmUnaryZero`)**: drops input on `kIO` and pushes `encUnary 0 = []`. -/
def bmUnaryZero : BitMachine :=
  bmConstEmpty

/-- **Unary Successor (`bmUnarySucc`)**: `encUnary n ↦ encUnary (n + 1)` in 1 step. -/
def bmUnarySucc : BitMachine :=
  tmConsBit false kIO

theorem bmUnarySucc_computesStageLe :
    ComputesStageLe bmUnarySucc encUnary encUnary (fun n => n + 1) (fun _ => 1) := by
  intro n tW2 tW3 tW4 tW5 tSch
  have h := tmConsBit_computesInTime false kIO
    (mkTapes8 (encodeDelimWord (encUnary n)) [] [] tW2 tW3 tW4 tW5 tSch)
    (encUnary n) [] (by simp)
  simp only [update_mkTapes8_kIO, List.append_nil] at h
  exact ⟨1, le_rfl, h⟩

/-- **Unary Constant (`bmUnaryConst c`)**: drops input on `kIO` and pushes `encUnary c`. -/
def bmUnaryConst : ℕ → BitMachine
  | 0 => bmUnaryZero
  | c + 1 => bmSeq (bmUnaryConst c) bmUnarySucc

theorem bmUnaryConst_computesStageLe {α : Type} (c : ℕ) (encA : α → List Bool) :
    ComputesStageLe (bmUnaryConst c) encA encUnary (fun _ => c)
      (fun x => (encA x).length + c + 2) := by
  induction c with
  | zero =>
    simpa [ComputesStageLe, bmUnaryConst, bmUnaryZero, encUnit, encUnary] using bmConstEmpty_computesStageLe encA
  | succ c ih =>
    exact (bmSeq_computesStageLe ih bmUnarySucc_computesStageLe).mono (fun _ => by omega)

/-- **Unary Predecessor (`bmUnaryPred`)**: `encUnary n ↦ encUnary (n - 1)` in 4 steps. -/
def bmUnaryPred : BitMachine :=
  (tmPushEmpty kWork0).seq
    ((tmPopBitOrZero kIO kWork0).seq (tmDropWord kWork0))

theorem bmUnaryPred_computesStageLe :
    ComputesStageLe bmUnaryPred encUnary encUnary (fun n => n - 1) (fun _ => 4) := by
  intro n tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s0 := tmPushEmpty_computesInTime kWork0
    (mkTapes8 (encodeDelimWord (encUnary n)) [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, mkTapes8_kWork0, List.append_nil] at s0
  have s1 := tmPopBitOrZero_computesInTime kIO kWork0 (by decide)
    (encUnary n) [] [] [] (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at s1
  have htail : (encUnary n).tail = encUnary (n - 1) := by
    cases n <;> rfl
  rw [htail] at s1
  have s2 := tmDropWord_computesInTime kWork0 [(encUnary n).headD false] []
    (mkTapes8 (encodeDelimWord (encUnary (n - 1))) [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, List.append_nil, List.length_singleton] at s2
  exact ⟨1 + (1 + (1 + 1)), le_rfl, s0.seq (s1.seq s2)⟩

/-- **Unary Addition (`bmUnaryAdd`)**: `encPair encUnary encUnary (a, b) ↦ encUnary (a + b)` in `2a + 2b + 8` steps. -/
def bmUnaryAdd : BitMachine :=
  bmAppendBits

theorem bmUnaryAdd_computesStageLe :
    ComputesStageLe bmUnaryAdd (encPair encUnary encUnary) encUnary
      (fun p => p.1 + p.2) (fun p => 2 * p.1 + 2 * p.2 + 8) := by
  intro ⟨a, b⟩ tW2 tW3 tW4 tW5 tSch
  rcases bmAppendBits_computesStageLe (encUnary a, encUnary b) tW2 tW3 tW4 tW5 tSch with
    ⟨t, ht, hcomp⟩
  dsimp only [encBits, id] at ht hcomp
  simp only [length_encUnary] at ht
  have hrep : encUnary a ++ encUnary b = encUnary (a + b) := by
    simp only [encUnary, ← List.replicate_add]
  rw [hrep] at hcomp
  exact ⟨t, ht, hcomp⟩

/-- **Unary Subtraction (`bmUnarySub`)**: `encPair encUnary encUnary (a, b) ↦ encUnary (a - b)` in `8a + 10b + 36` steps. -/
def bmUnarySub : BitMachine :=
  bmSeq bmSwap bmDropBits

theorem bmUnarySub_computesStageLe :
    ComputesStageLe bmUnarySub (encPair encUnary encUnary) encUnary
      (fun p => p.1 - p.2) (fun p => 8 * p.1 + 10 * p.2 + 36) := by
  intro ⟨a, b⟩ tW2 tW3 tW4 tW5 tSch
  rcases bmSwap_computesStageLe encUnary encUnary (a, b) tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmDropBits_computesStageLe (b, encUnary a) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  dsimp only [Prod.swap, encBits, id] at ht1 ht2 s1 s2 ⊢
  simp only [length_encUnary] at ht1 ht2
  have hdrop : (encUnary a).drop b = encUnary (a - b) := by
    simp [encUnary, List.drop_replicate]
  rw [hdrop] at s2
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

/-- **Unary Doubling (`bmUnaryDouble`)**: `encUnary n ↦ encUnary (2 * n)` in `7n + 15` steps. -/
def bmUnaryDouble : BitMachine :=
  bmSeq bmDup bmUnaryAdd

theorem bmUnaryDouble_computesStageLe :
    ComputesStageLe bmUnaryDouble encUnary encUnary (fun n => 2 * n) (fun n => 7 * n + 15) := by
  have h := bmSeq_computesStageLe (bmDup_computesStageLe encUnary) bmUnaryAdd_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun n => by rw [Nat.two_mul])).mono (fun n => ?_)
  simp only [length_encUnary]
  omega

/-- **Unary Zero-Test (`bmUnaryIsZero`)**: `encUnary n ↦ encBool (decide (n = 0))` in `O(n)` steps. -/
def bmUnaryIsZero : BitMachine :=
  bmSeq (bmFanout bmId (bmConstBool true)) (bmIterLoop (bmConstBool false))

theorem bmUnaryIsZero_computesStageLe :
    ComputesStageLe bmUnaryIsZero encUnary encBool (fun n => decide (n = 0))
      (fun n => 16 * n + 40) := by
  have h1 := bmFanout_computesStageLe (bmId_computesStageLe encUnary)
    (bmConstBool_computesStageLe true encUnary)
  have h2 := bmIterLoop_computesStageLe (bmConstBool_computesStageLe false encBool)
  have h := bmSeq_computesStageLe h1 h2
  have hiter : ∀ n : ℕ, (fun _ : Bool => false)^[n] true = decide (n = 0)
    | 0 => rfl
    | n + 1 => by
      rw [Function.iterate_succ_apply']
      rfl
  refine (ComputesStageLe.congr_fn h (fun n => by dsimp only [id]; rw [hiter])).mono (fun n => ?_)
  have hloop := loopStepsAux_le_of_const (fun _ : Bool => false)
    (fun b : Bool => (encBool b).length + 2) 3 (fun b => by simp [encBool]) (encUnary n) true
  dsimp only [id, encBool] at hloop ⊢
  simp only [List.length_singleton, length_encUnary] at hloop ⊢
  omega

/-- **Unary `≤` Comparison (`bmUnaryLe`)**: `encPair encUnary encUnary (a, b) ↦ encBool (decide (a ≤ b))`. -/
def bmUnaryLe : BitMachine :=
  bmSeq bmUnarySub bmUnaryIsZero

theorem bmUnaryLe_computesStageLe :
    ComputesStageLe bmUnaryLe (encPair encUnary encUnary) encBool
      (fun p => decide (p.1 ≤ p.2)) (fun p => 140 * p.1 + 10 * p.2 + 80) := by
  have h := bmSeq_computesStageLe bmUnarySub_computesStageLe bmUnaryIsZero_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => ?_)).mono (fun ⟨a, b⟩ => ?_)
  · simp [Nat.sub_eq_zero_iff_le]
  · dsimp only
    omega

/-- **Unary `<` Comparison (`bmUnaryLt`)**: `encPair encUnary encUnary (a, b) ↦ encBool (decide (a < b))`. -/
def bmUnaryLt : BitMachine :=
  bmSeq (bmMapFst bmUnarySucc) bmUnaryLe

theorem bmUnaryLt_computesStageLe :
    ComputesStageLe bmUnaryLt (encPair encUnary encUnary) encBool
      (fun p => decide (p.1 < p.2)) (fun p => 160 * p.1 + 25 * p.2 + 280) := by
  have h := bmSeq_computesStageLe
    (bmPairMap_computesStageLe bmUnarySucc_computesStageLe (bmId_computesStageLe encUnary))
    bmUnaryLe_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => rfl)).mono (fun ⟨a, b⟩ => ?_)
  simp only [id, length_encUnary]
  omega

/-- **Unary `=` Comparison (`bmUnaryEq`)**: `encPair encUnary encUnary (a, b) ↦ encBool (decide (a = b))`. -/
def bmUnaryEq : BitMachine :=
  bmSeq (bmFanout bmUnarySub (bmSeq bmSwap bmUnarySub)) (bmSeq bmUnaryAdd bmUnaryIsZero)

theorem bmUnaryEq_computesStageLe :
    ComputesStageLe bmUnaryEq (encPair encUnary encUnary) encBool
      (fun p => decide (p.1 = p.2)) (fun p => 250 * p.1 + 250 * p.2 + 300) := by
  have h1 := bmFanout_computesStageLe bmUnarySub_computesStageLe
    (bmSeq_computesStageLe (bmSwap_computesStageLe encUnary encUnary) bmUnarySub_computesStageLe)
  have h2 := bmSeq_computesStageLe bmUnaryAdd_computesStageLe bmUnaryIsZero_computesStageLe
  have h := bmSeq_computesStageLe h1 h2
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => ?_)).mono (fun ⟨a, b⟩ => ?_)
  · dsimp only [Prod.swap]
    exact congrArg encBool (decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩)
  · dsimp only [Prod.swap]
    have hsub1 : a - b ≤ a := Nat.sub_le a b
    have hsub2 : b - a ≤ b := Nat.sub_le b a
    simp only [length_encPair, length_encUnary]
    omega

/-- **Unary Maximum (`bmUnaryMax`)**: `encPair encUnary encUnary (a, b) ↦ encUnary (max a b)`. -/
def bmUnaryMax : BitMachine :=
  bmIte bmUnaryLe bmSnd bmFst

theorem bmUnaryMax_computesStageLe :
    ComputesStageLe bmUnaryMax (encPair encUnary encUnary) encUnary
      (fun p => max p.1 p.2) (fun p => 160 * p.1 + 25 * p.2 + 120) := by
  have h := bmIte_computesStageLe bmUnaryLe_computesStageLe
    (bmSnd_computesStageLe encUnary encUnary)
    (bmFst_computesStageLe encUnary encUnary)
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => ?_)).mono (fun ⟨a, b⟩ => ?_)
  · dsimp only
    split_ifs with hle <;> simp only [decide_eq_true_eq] at hle <;> congr 1 <;> omega
  · dsimp only
    simp only [length_encPair, length_encUnary]
    split_ifs <;> omega

/-- **Unary Minimum (`bmUnaryMin`)**: `encPair encUnary encUnary (a, b) ↦ encUnary (min a b)`. -/
def bmUnaryMin : BitMachine :=
  bmIte bmUnaryLe bmFst bmSnd

theorem bmUnaryMin_computesStageLe :
    ComputesStageLe bmUnaryMin (encPair encUnary encUnary) encUnary
      (fun p => min p.1 p.2) (fun p => 160 * p.1 + 25 * p.2 + 120) := by
  have h := bmIte_computesStageLe bmUnaryLe_computesStageLe
    (bmFst_computesStageLe encUnary encUnary)
    (bmSnd_computesStageLe encUnary encUnary)
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => ?_)).mono (fun ⟨a, b⟩ => ?_)
  · dsimp only
    split_ifs with hle <;> simp only [decide_eq_true_eq] at hle <;> congr 1 <;> omega
  · dsimp only
    simp only [length_encPair, length_encUnary]
    split_ifs <;> omega

/-- **Unary Multiplication (`bmUnaryMul`)**: `encPair encUnary encUnary (a, b) ↦ encUnary (a * b)`. -/
def bmUnaryMul : BitMachine :=
  bmSeq
    (bmFanout bmFst (bmFanout bmSnd bmUnaryZero))
    (bmSeq (bmIterLoop (bmFanout bmFst bmUnaryAdd)) bmSnd)

theorem bmUnaryMul_computesStageLe :
    ComputesStageLe bmUnaryMul (encPair encUnary encUnary) encUnary
      (fun p => p.1 * p.2)
      (fun p => 40 * p.1 * p.1 * p.2 + 80 * p.1 * p.2 + 100 * p.1 + 50 * p.2 + 200) := by
  intro ⟨a, b⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  let S := Unit
  have hinit : StageEval (S := S)
      (bmFanout bmFst (bmFanout bmSnd bmUnaryZero))
      (fun _ => encPair encUnary encUnary (a, b))
      (encDepPair (fun _ => encUnary a)
        (fun _ => encPair encUnary encUnary (b, 0 * b)))
      (fun _ => 35 * a + 35 * b + 120) := by
    have p1 := StageEval.fst (fun _ : S => encUnary a) (fun _ : S => encUnary b)
    have p2 := StageEval.snd (fun _ : S => encUnary a) (fun _ : S => encUnary b)
    have p3 := StageEval.constEmpty (encDepPair (fun _ : S => encUnary a) (fun _ : S => encUnary b))
    have p123 : StageEval (S := S)
        (bmFanout bmFst (bmFanout bmSnd bmUnaryZero))
        (fun _ => encPair encUnary encUnary (a, b))
        (encDepPair (fun _ => encUnary a)
          (encDepPair (fun _ => encUnary b) (fun _ => [])))
        (fun _ => 35 * a + 35 * b + 120) :=
      (StageEval.fanout p1 (StageEval.fanout p2 p3)).mono (fun _ => by
        simp only [length_encDepPair, length_encUnary, List.length_nil]
        omega)
    exact StageEval.congr_out p123 (fun _ => by simp [encDepPair, encPair, encUnary])
  have hloop : StageEval (S := S)
      (bmIterLoop (bmFanout bmFst bmUnaryAdd))
      (encDepPair (fun _ => encUnary a)
        (fun _ => encPair encUnary encUnary (b, 0 * b)))
      (fun _ => encPair encUnary encUnary (b, a * b))
      (fun _ => a * (30 * (a * b) + 20 * b + 65) + 4 * b + 18) := by
    refine (StageEval.iterLoop_idx
      (u := fun _ i => encPair encUnary encUnary (b, i * b))
      (B := fun _ => 30 * (a * b) + 20 * b + 60) ?_).mono (fun _ => by
      simp only [length_encPair, length_encUnary, Nat.zero_mul]
      have hring : a * (30 * (a * b) + 20 * b + 60 + 3) =
          a * (30 * (a * b) + 20 * b + 63) := rfl
      nlinarith)
    have b1 := StageEval.fst
      (fun p : { p : S × ℕ // p.2 < a } => encUnary b)
      (fun p : { p : S × ℕ // p.2 < a } => encUnary (p.val.2 * b))
    have b2 : StageEval (S := { p : S × ℕ // p.2 < a }) bmUnaryAdd
        (encDepPair (fun _ => encUnary b) (fun p => encUnary (p.val.2 * b)))
        (fun p => encUnary ((p.val.2 + 1) * b))
        (fun p => 2 * b + 2 * (p.val.2 * b) + 8) := by
      refine StageEval.congr_out
        (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe
          (fun p : { p : S × ℕ // p.2 < a } => (b, p.val.2 * b)))
        (fun p => by dsimp only; rw [Nat.succ_mul, Nat.add_comm])
    refine (StageEval.fanout b1 b2).mono (fun p => ?_)
    have hi : p.val.2 ≤ a := Nat.le_of_lt p.property
    have hm : p.val.2 * b ≤ a * b := Nat.mul_le_mul_right b hi
    have hm1 : (p.val.2 + 1) * b ≤ a * b := Nat.mul_le_mul_right b p.property
    simp only [length_encDepPair, length_encUnary]
    omega
  have hfin := StageEval.snd (fun _ : S => encUnary b) (fun _ : S => encUnary (a * b))
  have hall := StageEval.seq hinit (StageEval.seq hloop hfin)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  refine ⟨t, ?_, hcomp⟩
  dsimp only at ht
  simp only [length_encUnary] at ht
  have hexp : a * (30 * (a * b) + 20 * b + 65) = 30 * (a * a * b) + 20 * (a * b) + 65 * a := by
    ring
  have hassoc : 40 * a * a * b = 40 * (a * a * b) := by ring
  have hassoc2 : 80 * a * b = 80 * (a * b) := by ring
  rw [hexp] at ht
  rw [hassoc, hassoc2]
  omega

/-- **Unary Power of Two (`bmUnaryTwoPow`)**: `encUnary k ↦ encUnary (2 ^ k)` in `O(k * 2^k)` steps. -/
def bmUnaryTwoPow : BitMachine :=
  bmSeq (bmFanout bmId (bmUnaryConst 1)) (bmIterLoop bmUnaryDouble)

theorem bmUnaryTwoPow_computesStageLe :
    ComputesStageLe bmUnaryTwoPow encUnary encUnary (fun k => 2 ^ k)
      (fun k => 10 * k * 2 ^ k + 30 * k + 60) := by
  intro k tW2 tW3 tW4 tW5 tSch
  dsimp only
  let S := Unit
  have h1 : StageEval (S := S) (bmFanout bmId (bmUnaryConst 1))
      (fun _ => encUnary k)
      (encDepPair (fun _ => encUnary k) (fun _ => encUnary (2 ^ 0)))
      (fun _ => 9 * k + 35) := by
    exact (StageEval.fanout (StageEval.id_stage (fun _ : S => encUnary k))
      (StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 1 encUnary) (fun _ => k))).mono
      (fun _ => by simp only [length_encUnary]; omega)
  have h2 : StageEval (S := S) (bmIterLoop bmUnaryDouble)
      (encDepPair (fun _ => encUnary k) (fun _ => encUnary (2 ^ 0)))
      (fun _ => encUnary (2 ^ k))
      (fun _ => k * (7 * 2 ^ k + 18) + 12) := by
    refine (StageEval.iterLoop_idx
      (u := fun _ i => encUnary (2 ^ i))
      (B := fun _ => 7 * 2 ^ k + 15) ?_).mono (fun _ => by
      simp only [Nat.pow_zero, length_encUnary]
      rfl)
    refine (StageEval.congr_out
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe
        (fun p : { p : S × ℕ // p.2 < k } => 2 ^ p.val.2))
      (fun p => by rw [Nat.pow_succ'])).mono (fun p => ?_)
    have hpow : 2 ^ p.val.2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt p.property)
    omega
  rcases StageEval.seq h1 h2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht
  have hk7 : k * (7 * 2 ^ k + 18) = 7 * (k * 2 ^ k) + 18 * k := by ring
  have hk10 : 10 * k * 2 ^ k = 10 * (k * 2 ^ k) := by ring
  rw [hk7] at ht
  rw [hk10]
  exact ⟨t, by omega, hcomp⟩

/-- **Unary Right Shift `a / 2 ^ k` (`bmUnaryShiftRight`)**:
Consumes `encPair encUnary encUnary (k, a)` and emits `encUnary (a / 2 ^ k)` in `O(k * a)` steps. -/
def bmUnaryShiftRight : BitMachine :=
  bmIterLoop bmHalfLenUnary

theorem bmUnaryShiftRight_computesStageLe :
    ComputesStageLe bmUnaryShiftRight (encPair encUnary encUnary) encUnary
      (fun p => p.2 / 2 ^ p.1)
      (fun p => p.1 * (6 * p.2 + 15) + 2 * p.2 + 10) := by
  intro ⟨k, a⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  let S := Unit
  have hloop : StageEval (S := S) (bmIterLoop bmHalfLenUnary)
      (encDepPair (fun _ => encUnary k) (fun _ => encUnary (a / 2 ^ 0)))
      (fun _ => encUnary (a / 2 ^ k))
      (fun _ => k * (6 * a + 15) + 2 * a + 10) := by
    refine (StageEval.iterLoop_idx
      (u := fun _ i => encUnary (a / 2 ^ i))
      (B := fun _ => 6 * a + 12) ?_).mono (fun _ => by
      simp only [Nat.pow_zero, Nat.div_one, length_encUnary]
      rfl)
    refine (StageEval.congr_out
      (StageEval.of_computesStageLe (bmHalfLenUnary_computesStageLe encUnary)
        (fun p : { p : S × ℕ // p.2 < k } => a / 2 ^ p.val.2))
      (fun p => by
        simp only [length_encUnary, Nat.div_div_eq_div_mul, ← Nat.pow_succ])).mono (fun p => ?_)
    simp only [length_encUnary]
    have hdiv : a / 2 ^ p.val.2 ≤ a := Nat.div_le_self a _
    omega
  rcases hloop () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair, id] at ht hcomp
  simp only [Nat.pow_zero, Nat.div_one] at hcomp
  change bmUnaryShiftRight.ComputesInTime
    (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (k, a))) [] [] tW2 tW3 tW4 tW5 tSch)
    (mkTapes8 (encodeDelimWord (encUnary (a / 2 ^ k))) [] [] tW2 tW3 tW4 tW5 tSch) t at hcomp
  exact ⟨t, ht, hcomp⟩

/-! ### Linear-Time Unary Bit-Length, `Nat.log 2`, `Nat.clog 2`, `ceilDiv`, and `a / b` -/

/-- Binary bit-length of `m : ℕ`: `0` if `m = 0`, else `1 + bitLength (m / 2)`. -/
def bitLength (m : ℕ) : ℕ :=
  if m = 0 then 0 else 1 + bitLength (m / 2)
termination_by m
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹m ≠ 0›) (by decide)

@[simp] theorem bitLength_zero : bitLength 0 = 0 := by rw [bitLength]; rfl

theorem bitLength_pos {m : ℕ} (hm : 0 < m) :
    bitLength m = 1 + bitLength (m / 2) := by
  rw [bitLength, if_neg (ne_of_gt hm)]

theorem clog2_succ_eq_bitLength : ∀ m : ℕ, Nat.clog 2 (m + 1) = bitLength m
  | 0 => by simp
  | m + 1 => by
    rw [bitLength_pos (Nat.succ_pos m),
      Nat.clog_of_one_lt (by decide) (by omega)]
    have hdiv : (m + 1 + 1 + 2 - 1) / 2 = (m + 1) / 2 + 1 := by omega
    rw [hdiv, clog2_succ_eq_bitLength ((m + 1) / 2), Nat.add_comm]
termination_by m => m
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos m) (by decide)

theorem clog2_eq_bitLength_pred (a : ℕ) : Nat.clog 2 a = bitLength (a - 1) := by
  cases a with
  | zero => simp
  | succ m => exact clog2_succ_eq_bitLength m

theorem log2_eq_bitLength_half : ∀ a : ℕ, Nat.log 2 a = bitLength (a / 2)
  | 0 => by simp
  | 1 => by simp
  | a + 2 => by
    have hge2 : 2 ≤ a + 2 := by omega
    have hhalf_pos : 0 < (a + 2) / 2 := by omega
    rw [Nat.log_of_one_lt_of_le (by decide) hge2,
      bitLength_pos hhalf_pos, log2_eq_bitLength_half ((a + 2) / 2), Nat.add_comm]
termination_by a => a
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

/-- **Linear-Time Unary Bit-Length (`bmUnaryBitLength`)**:
Consumes `encUnary m` on `kIO` and emits `encUnary (bitLength m)` on `kIO` in `≤ 42 * m + 10` steps
by repeatedly halving `m` on `kWork2` (`loopNonEmptyWord kWork2`) until `m = 0`. -/
def bmUnaryBitLength : BitMachine :=
  (tmMoveWord kIO kWork0 kWork2).seq
    ((tmPushEmpty kIO).seq
      ((((tmMoveWord kWork2 kWork0 kWork3).seq
          ((tmRevMoveWord kIO kWork4).seq
            ((tmMoveWord kWork3 kWork0 kIO).seq
              (bmHalfLenUnary.seq
                ((tmMoveWord kIO kWork0 kWork2).seq
                  ((tmRevMoveWord kWork4 kIO).seq bmUnarySucc)))))).loopNonEmptyWord kWork2)))

theorem bmUnaryBitLength_loop_le :
    ∀ (m : ℕ) (acc : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ 90 * m + 4 * (m * acc) + 1,
        (((tmMoveWord kWork2 kWork0 kWork3).seq
            ((tmRevMoveWord kIO kWork4).seq
              ((tmMoveWord kWork3 kWork0 kIO).seq
                (bmHalfLenUnary.seq
                  ((tmMoveWord kIO kWork0 kWork2).seq
                    ((tmRevMoveWord kWork4 kIO).seq bmUnarySucc)))))).loopNonEmptyWord kWork2).ComputesInTime
          (mkTapes8 (encodeDelimWord (encUnary acc)) [] []
            (encodeDelimWord (encUnary m) ++ tW2) tW3 tW4 tW5 tSch)
          (mkTapes8 (encodeDelimWord (encUnary (acc + bitLength m))) [] []
            tW2 tW3 tW4 tW5 tSch) t
  | 0, acc, tW2, tW3, tW4, tW5, tSch => by
    simp only [bitLength_zero, Nat.add_zero, Nat.mul_zero, Nat.zero_mul, encUnary,
      List.replicate_zero]
    refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopNonEmptyWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, mkTapes8_kWork2, update_mkTapes8_kWork2, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | m + 1, acc, tW2, tW3, tW4, tW5, tSch => by
    let body :=
      (tmMoveWord kWork2 kWork0 kWork3).seq
        ((tmRevMoveWord kIO kWork4).seq
          ((tmMoveWord kWork3 kWork0 kIO).seq
            (bmHalfLenUnary.seq
              ((tmMoveWord kIO kWork0 kWork2).seq
                ((tmRevMoveWord kWork4 kIO).seq bmUnarySucc)))))
    have hpop : (body.loopNonEmptyWord kWork2).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord (encUnary acc)) [] []
            (encodeDelimWord (encUnary (m + 1)) ++ tW2) tW3 tW4 tW5 tSch⟩ =
        some ⟨some (some body.main), default,
          mkTapes8 (encodeDelimWord (encUnary acc)) [] []
            (encodeDelimWord (encUnary (m + 1)) ++ tW2) tW3 tW4 tW5 tSch⟩ := by
      simp only [encUnary, List.replicate_succ, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons,
        List.cons_append, mkTapes8_kWork2, update_mkTapes8_kWork2, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    have b1 := tmMoveWord_computesInTime kWork2 kWork0 kWork3 (by decide) (by decide) (by decide)
      (encUnary (m + 1)) tW2 [] tW3
      (mkTapes8 (encodeDelimWord (encUnary acc)) [] [] [] [] tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
      length_encUnary] at b1
    have b2 := tmRevMoveWord_computesInTime kIO kWork4 (by decide)
      (encUnary acc) [] tW4
      (mkTapes8 [] [] [] tW2 (encodeDelimWord (encUnary (m + 1)) ++ tW3) [] tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork4, List.append_nil,
      length_encUnary] at b2
    have b3 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
      (encUnary (m + 1)) tW3 [] []
      (mkTapes8 [] [] [] tW2 [] (encodeDelimWord (encUnary acc).reverse ++ tW4) tW5 tSch)
    simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
      List.append_nil, length_encUnary] at b3
    rcases bmHalfLenUnary_computesStageLe encUnary (m + 1) tW2 tW3
      (encodeDelimWord (encUnary acc).reverse ++ tW4) tW5 tSch with ⟨th, hth, b4⟩
    simp only [length_encUnary] at hth b4
    have b5 := tmMoveWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
      (encUnary ((m + 1) / 2)) [] [] tW2
      (mkTapes8 [] [] [] [] tW3 (encodeDelimWord (encUnary acc).reverse ++ tW4) tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
      List.append_nil, length_encUnary] at b5
    have b6 := tmRevMoveWord_computesInTime kWork4 kIO (by decide)
      (encUnary acc).reverse tW4 []
      (mkTapes8 [] [] [] (encodeDelimWord (encUnary ((m + 1) / 2)) ++ tW2) tW3 [] tW5 tSch)
    simp only [update_mkTapes8_kWork4, update_mkTapes8_kIO, List.length_reverse,
      List.reverse_reverse, length_encUnary, List.append_nil] at b6
    rcases bmUnarySucc_computesStageLe acc
      (encodeDelimWord (encUnary ((m + 1) / 2)) ++ tW2) tW3 tW4 tW5 tSch with ⟨ts, hts, b7⟩
    dsimp only at hts b7
    have ⟨hbody⟩ := b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (b6.seq b7)))))
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete kWork2 body hbody
    rcases bmUnaryBitLength_loop_le ((m + 1) / 2) (acc + 1) tW2 tW3 tW4 tW5 tSch with
      ⟨t2, ht2, ⟨hih⟩⟩
    have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hbody_lifted) hih
    have hbit : (acc + 1) + bitLength ((m + 1) / 2) = acc + bitLength (m + 1) := by
      have hp := bitLength_pos (Nat.succ_pos m)
      simp only [Nat.succ_eq_add_one] at hp ⊢
      omega
    rw [hbit] at hcomb
    refine ⟨_, ?_, ⟨hcomb⟩⟩
    have h1 : (m + 1) / 2 ≤ m := by omega
    have h2 : 2 * ((m + 1) / 2) ≤ m + 1 := by omega
    have h3 : ((m + 1) / 2) * (acc + 1) ≤ m * acc + m := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right acc h1) h1
    have h4 : (m + 1) * acc = m * acc + acc := Nat.succ_mul m acc
    rw [h4]
    omega

theorem bmUnaryBitLength_computesStageLe :
    ComputesStageLe bmUnaryBitLength encUnary encUnary bitLength
      (fun m => 92 * m + 10) := by
  intro m tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmMoveWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
    (encUnary m) [] [] tW2 (mkTapes8 [] [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
    List.append_nil, length_encUnary] at s1
  have s2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] (encodeDelimWord (encUnary m) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s2
  rcases bmUnaryBitLength_loop_le m 0 tW2 tW3 tW4 tW5 tSch with ⟨tL, htL, s3⟩
  simp only [Nat.zero_add, Nat.mul_zero] at htL s3
  refine ⟨_, ?_, s1.seq (s2.seq s3)⟩
  omega

/-- **Linear-Time Unary Floor Log2 (`bmUnaryLog2`)**:
`encUnary a ↦ encUnary (Nat.log 2 a)` in `≤ 60 * a + 25` `TM2.step` transitions. -/
def bmUnaryLog2 : BitMachine :=
  bmSeq bmHalfLenUnary bmUnaryBitLength

theorem bmUnaryLog2_computesStageLe :
    ComputesStageLe bmUnaryLog2 encUnary encUnary (Nat.log 2)
      (fun a => 60 * a + 25) := by
  have h := bmSeq_computesStageLe (bmHalfLenUnary_computesStageLe encUnary)
    bmUnaryBitLength_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun a => by
    simp [length_encUnary, log2_eq_bitLength_half])).mono (fun a => ?_)
  simp only [length_encUnary]
  omega

/-- **Linear-Time Unary Ceiling Log2 (`bmUnaryClog2`)**:
`encUnary a ↦ encUnary (Nat.clog 2 a)` in `≤ 92 * a + 15` `TM2.step` transitions. -/
def bmUnaryClog2 : BitMachine :=
  bmSeq bmUnaryPred bmUnaryBitLength

theorem bmUnaryClog2_computesStageLe :
    ComputesStageLe bmUnaryClog2 encUnary encUnary (Nat.clog 2)
      (fun a => 92 * a + 15) := by
  have h := bmSeq_computesStageLe bmUnaryPred_computesStageLe
    bmUnaryBitLength_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun a => by
    simp [clog2_eq_bitLength_pred])).mono (fun a => ?_)
  omega

/-- Ceiling division `(a + b - 1) / b` for `b > 0`. -/
def ceilDiv (a b : ℕ) : ℕ :=
  (a + b - 1) / b

@[simp]
theorem ceilDiv_zero (b : ℕ) : ceilDiv 0 b = 0 := by
  unfold ceilDiv
  cases b with
  | zero => rfl
  | succ b' =>
    simp [Nat.div_eq_of_lt (Nat.lt_succ_self b')]

theorem ceilDiv_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ceilDiv a b = 1 + ceilDiv (a - b) b := by
  unfold ceilDiv
  by_cases hab : a < b
  · have hsub : a - b = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hab)
    rw [hsub]
    have h0 : (0 + b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0, Nat.add_zero]
    have h1 : a + b - 1 = (a - 1) + b := by omega
    rw [h1, Nat.add_div_right _ hb, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · have h1 : a + b - 1 = (a - b + b - 1) + b := by omega
    rw [h1, Nat.add_div_right _ hb, Nat.add_comm]

theorem div_eq_ceilDiv_sub {a b : ℕ} (hb : 0 < b) :
    a / b = ceilDiv (a + 1 - b) b := by
  by_cases hab : a < b
  · have hsub : a + 1 - b = 0 := by omega
    rw [hsub, ceilDiv_zero, Nat.div_eq_of_lt hab]
  · unfold ceilDiv
    have heq : a + 1 - b + b - 1 = a := by omega
    rw [heq]

/-- **Linear-Time Unary Ceiling Division (`bmUnaryCeilDiv`)**:
Consumes `encPair encUnary encUnary (a, b)` (`b > 0`) on `kIO` and emits
`encUnary ((a + b - 1) / b)` on `kIO` in **strictly linear** $O(a + b)$ `TM2.step` transitions. -/
def bmUnaryCeilDiv : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork2).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kWork3).seq
            ((tmPushEmpty kIO).seq
              ((((tmDupWord kWork3 kWork0 kWork1).seq
                  ((tmPushEmpty kWork0).seq
                    (((tmPopBitOrZero kWork2 kWork0).loopDelimWord kWork1).seq
                      ((tmDropWord kWork0).seq bmUnarySucc)))).loopNonEmptyWord kWork2).seq
                (tmDropWord kWork3)))))))

theorem bmUnaryCeilDiv_loop_le {b : ℕ} (hb : 0 < b) :
    ∀ (a acc : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ ceilDiv a b * (6 * b + 11) + 1,
        (((tmDupWord kWork3 kWork0 kWork1).seq
            ((tmPushEmpty kWork0).seq
              (((tmPopBitOrZero kWork2 kWork0).loopDelimWord kWork1).seq
                ((tmDropWord kWork0).seq bmUnarySucc)))).loopNonEmptyWord kWork2).ComputesInTime
          (mkTapes8 (encodeDelimWord (encUnary acc)) [] []
            (encodeDelimWord (encUnary a) ++ tW2)
            (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch)
          (mkTapes8 (encodeDelimWord (encUnary (acc + ceilDiv a b))) [] []
            tW2 (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch) t
  | 0, acc, tW2, tW3, tW4, tW5, tSch => by
    simp only [ceilDiv_zero, Nat.add_zero, Nat.zero_mul, encUnary, List.replicate_zero]
    refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopNonEmptyWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, mkTapes8_kWork2, update_mkTapes8_kWork2, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | a + 1, acc, tW2, tW3, tW4, tW5, tSch => by
    let body :=
      (tmDupWord kWork3 kWork0 kWork1).seq
        ((tmPushEmpty kWork0).seq
          (((tmPopBitOrZero kWork2 kWork0).loopDelimWord kWork1).seq
            ((tmDropWord kWork0).seq bmUnarySucc)))
    have hpop : (body.loopNonEmptyWord kWork2).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord (encUnary acc)) [] []
            (encodeDelimWord (encUnary (a + 1)) ++ tW2)
            (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch⟩ =
        some ⟨some (some body.main), default,
          mkTapes8 (encodeDelimWord (encUnary acc)) [] []
            (encodeDelimWord (encUnary (a + 1)) ++ tW2)
            (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch⟩ := by
      simp only [encUnary, List.replicate_succ, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons,
        List.cons_append, mkTapes8_kWork2, update_mkTapes8_kWork2, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    have b1 := tmDupWord_computesInTime kWork3 kWork0 kWork1 (by decide) (by decide) (by decide)
      (encUnary b) tW3 [] []
      (mkTapes8 (encodeDelimWord (encUnary acc)) [] []
        (encodeDelimWord (encUnary (a + 1)) ++ tW2) [] tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
      List.append_nil, length_encUnary] at b1
    have b2 := tmPushEmpty_computesInTime kWork0
      (mkTapes8 (encodeDelimWord (encUnary acc)) [] (encodeDelimWord (encUnary b))
        (encodeDelimWord (encUnary (a + 1)) ++ tW2)
        (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, mkTapes8_kWork0, List.append_nil] at b2
    let innerStk : List Bool × List Bool → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun ist =>
      mkTapes8 (encodeDelimWord (encUnary acc)) (encodeDelimWord ist.2) []
        (encodeDelimWord ist.1 ++ tW2)
        (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch
    have b3 := BitMachine.ComputesInTime.loopDelimWord_state kWork1
      popBitStep (fun _ => 1) innerStk
      (fun ist tailW1 => by
        dsimp only [innerStk, popBitStep]
        simp only [update_mkTapes8_kWork1]
        have hp := tmPopBitOrZero_computesInTime kWork2 kWork0 (by decide)
          ist.1 ist.2 tW2 []
          (mkTapes8 (encodeDelimWord (encUnary acc)) [] tailW1 []
            (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch)
        simpa only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil] using hp)
      (encUnary b) [] (encUnary (a + 1), [])
    dsimp only [innerStk] at b3
    simp only [update_mkTapes8_kWork1, List.append_nil, loopFinalState_popBitStep,
      loopStepsAux_popBitStep, length_encUnary] at b3
    have hdrop : (encUnary (a + 1)).drop b = encUnary ((a + 1) - b) := by
      simp [encUnary, List.drop_replicate]
    rw [hdrop] at b3
    have b4 := tmDropWord_computesInTime kWork0
      (takePadBits b (encUnary (a + 1))).reverse []
      (mkTapes8 (encodeDelimWord (encUnary acc)) [] []
        (encodeDelimWord (encUnary ((a + 1) - b)) ++ tW2)
        (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, List.append_nil, List.length_reverse,
      length_takePadBits] at b4
    rcases bmUnarySucc_computesStageLe acc
      (encodeDelimWord (encUnary ((a + 1) - b)) ++ tW2)
      (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch with ⟨ts, hts, b5⟩
    dsimp only at hts b5
    have ⟨hbody⟩ := b1.seq (b2.seq (b3.seq (b4.seq b5)))
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete kWork2 body hbody
    rcases bmUnaryCeilDiv_loop_le hb ((a + 1) - b) (acc + 1) tW2 tW3 tW4 tW5 tSch with
      ⟨t2, ht2, ⟨hih⟩⟩
    have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hbody_lifted) hih
    have hceil : (acc + 1) + ceilDiv ((a + 1) - b) b = acc + ceilDiv (a + 1) b := by
      have hp := ceilDiv_pos (Nat.succ_pos a) hb
      simp only [Nat.succ_eq_add_one] at hp ⊢
      omega
    rw [hceil] at hcomb
    refine ⟨_, ?_, ⟨hcomb⟩⟩
    have hpos_step := ceilDiv_pos (Nat.succ_pos a) hb
    simp only [Nat.succ_eq_add_one] at hpos_step ⊢
    nlinarith
termination_by a => a
decreasing_by
  exact Nat.sub_lt (Nat.succ_pos a) hb

theorem ceilDiv_mul_le (a b : ℕ) (hb : 0 < b) :
    ceilDiv a b * b ≤ a + b := by
  unfold ceilDiv
  have h := Nat.div_mul_le_self (a + b - 1) b
  omega

theorem ceilDiv_le_self (a b : ℕ) : ceilDiv a b ≤ a := by
  unfold ceilDiv
  cases b with
  | zero => simp
  | succ b' =>
    rcases a with _ | a'
    · simp [Nat.div_eq_of_lt (Nat.lt_succ_self b')]
    · have hring : (b' + 1) * (a' + 1) = b' * a' + b' + a' + 1 := by ring
      have h1 : a' + 1 + (b' + 1) - 1 ≤ (b' + 1) * (a' + 1) := by omega
      exact Nat.div_le_of_le_mul h1

theorem bmUnaryCeilDiv_computesInTime (a b : ℕ) (hb : 0 < b)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 20 * a + 10 * b + 25,
      bmUnaryCeilDiv.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (a, b)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encUnary (ceilDiv a b)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary a) ++ encodeDelimWord (encUnary b)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append, length_encUnary] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encUnary a).reverse [] tW2
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encUnary b))) [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, length_encUnary, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary b)) [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encUnary a) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord, length_encUnary] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encUnary b).reverse) []
      (encodeDelimWord (encUnary a) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kWork3 (by decide)
    (encUnary b).reverse [] tW3
    (mkTapes8 [] [] [] (encodeDelimWord (encUnary a) ++ tW2) [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork3, List.length_reverse,
    List.reverse_reverse, length_encUnary, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] (encodeDelimWord (encUnary a) ++ tW2)
      (encodeDelimWord (encUnary b) ++ tW3) tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s6
  rcases bmUnaryCeilDiv_loop_le hb a 0 tW2 tW3 tW4 tW5 tSch with ⟨tL, htL, s7⟩
  simp only [Nat.zero_add] at s7
  have s8 := tmDropWord_computesInTime kWork3 (encUnary b) tW3
    (mkTapes8 (encodeDelimWord (encUnary (ceilDiv a b))) [] [] tW2 [] tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork3, length_encUnary] at s8
  have hmul := ceilDiv_mul_le a b hb
  have hle := ceilDiv_le_self a b
  refine ⟨_, ?_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq s8))))))⟩
  nlinarith

/-- **Linear-Time Unary Floor Division (`bmUnaryDiv`)**:
Consumes `encPair encUnary encUnary (a, b)` (`b > 0`) on `kIO` and emits `encUnary (a / b)` on
`kIO` in **strictly linear** $O(a + b)$ `TM2.step` transitions. -/
def bmUnaryDiv : BitMachine :=
  bmSeq (bmFanout (bmSeq (bmMapFst bmUnarySucc) bmUnarySub) bmSnd) bmUnaryCeilDiv

theorem bmUnaryDiv_computesInTime (a b : ℕ) (hb : 0 < b)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 65 * a + 65 * b + 180,
      bmUnaryDiv.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (a, b)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encUnary (a / b)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have h1 : StageEval (S := S) (bmFanout (bmSeq (bmMapFst bmUnarySucc) bmUnarySub) bmSnd)
      (fun _ => encPair encUnary encUnary (a, b))
      (fun _ => encPair encUnary encUnary (a + 1 - b, b))
      (fun _ => 40 * a + 50 * b + 150) := by
    have p1 := StageEval.mapFst (u2 := fun _ : S => encUnary b)
      (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ => a))
    have p2 := StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (a + 1, b))
    have p3 := StageEval.snd (fun _ : S => encUnary a) (fun _ : S => encUnary b)
    refine (StageEval.fanout (StageEval.seq p1 p2) p3).mono (fun _ => ?_)
    dsimp only
    have hsub : a + 1 - b ≤ a + 1 := Nat.sub_le (a + 1) b
    simp only [length_encDepPair, length_encUnary]
    omega
  rcases h1 () tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  dsimp only at ht1
  rcases bmUnaryCeilDiv_computesInTime (a + 1 - b) b hb tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  rw [← div_eq_ceilDiv_sub hb] at s2
  have hsub : a + 1 - b ≤ a := by omega
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

/-! ### `bmRangeList` (`m ↦ List.range m`) & `bmListGetD` (`(idx, (xs, defVal)) ↦ xs.getD idx defVal`) -/

/-- **Unary Range List (`bmRangeList`)**:
Consumes `encUnary m` on `kIO` and emits `encList encUnary (List.range m)` on `kIO` in $O(m^2)$
`TM2.step` transitions (`≤ 5 * m * m + 12 * m + 6`). -/
def bmRangeList : BitMachine :=
  (tmMoveWord kIO kWork0 kWork2).seq
    ((tmPushEmpty kIO).seq
      ((((tmPushEmpty kWork0).seq
          ((tmPopBitOrZero kWork2 kWork0).seq
            ((tmDropWord kWork0).seq
              ((tmDupWord kWork2 kWork1 kWork0).seq
                (tmPrependRevWord kWork0 kIO))))).loopNonEmptyWord kWork2)))

theorem bmRangeList_loop_le :
    ∀ (k : ℕ) (acc : List ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ 5 * k * k + 10 * k + 1,
        (((tmPushEmpty kWork0).seq
            ((tmPopBitOrZero kWork2 kWork0).seq
              ((tmDropWord kWork0).seq
                ((tmDupWord kWork2 kWork1 kWork0).seq
                  (tmPrependRevWord kWork0 kIO))))).loopNonEmptyWord kWork2).ComputesInTime
          (mkTapes8 (encodeDelimWord (encList encUnary acc)) [] []
            (encodeDelimWord (encUnary k) ++ tW2) tW3 tW4 tW5 tSch)
          (mkTapes8 (encodeDelimWord (encList encUnary (List.range k ++ acc))) [] []
            tW2 tW3 tW4 tW5 tSch) t
  | 0, acc, tW2, tW3, tW4, tW5, tSch => by
    simp only [List.range_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, encUnary,
      List.replicate_zero]
    refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopNonEmptyWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, mkTapes8_kWork2, update_mkTapes8_kWork2, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | k + 1, acc, tW2, tW3, tW4, tW5, tSch => by
    let body :=
      (tmPushEmpty kWork0).seq
        ((tmPopBitOrZero kWork2 kWork0).seq
          ((tmDropWord kWork0).seq
            ((tmDupWord kWork2 kWork1 kWork0).seq
              (tmPrependRevWord kWork0 kIO))))
    have hpop : (body.loopNonEmptyWord kWork2).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord (encList encUnary acc)) [] []
            (encodeDelimWord (encUnary (k + 1)) ++ tW2) tW3 tW4 tW5 tSch⟩ =
        some ⟨some (some body.main), default,
          mkTapes8 (encodeDelimWord (encList encUnary acc)) [] []
            (encodeDelimWord (encUnary (k + 1)) ++ tW2) tW3 tW4 tW5 tSch⟩ := by
      simp only [encUnary, List.replicate_succ, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons,
        List.cons_append, mkTapes8_kWork2, update_mkTapes8_kWork2, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    have b0 := tmPushEmpty_computesInTime kWork0
      (mkTapes8 (encodeDelimWord (encList encUnary acc)) [] []
        (encodeDelimWord (encUnary (k + 1)) ++ tW2) tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, mkTapes8_kWork0, List.append_nil] at b0
    have b1 := tmPopBitOrZero_computesInTime kWork2 kWork0 (by decide)
      (encUnary (k + 1)) [] tW2 []
      (mkTapes8 (encodeDelimWord (encList encUnary acc)) [] [] [] tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil] at b1
    have htail : (encUnary (k + 1)).tail = encUnary k := rfl
    rw [htail] at b1
    have b2 := tmDropWord_computesInTime kWork0 [(encUnary (k + 1)).headD false] []
      (mkTapes8 (encodeDelimWord (encList encUnary acc)) [] []
        (encodeDelimWord (encUnary k) ++ tW2) tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, List.append_nil, List.length_singleton] at b2
    have b3 := tmDupWord_computesInTime kWork2 kWork1 kWork0 (by decide) (by decide) (by decide)
      (encUnary k) tW2 [] []
      (mkTapes8 (encodeDelimWord (encList encUnary acc)) [] [] [] tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
      List.append_nil, length_encUnary] at b3
    have hrev_k : (encUnary k).reverse = encUnary k := by simp [encUnary]
    have b4 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
      (encUnary k).reverse (encList encUnary acc) [] []
      (mkTapes8 [] [] [] (encodeDelimWord (encUnary k) ++ tW2) tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
      List.reverse_reverse, length_encUnary, List.append_nil] at b4
    rw [hrev_k] at b4
    have ⟨hbody⟩ := b0.seq (b1.seq (b2.seq (b3.seq b4)))
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete kWork2 body hbody
    rcases bmRangeList_loop_le k (k :: acc) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, ⟨hih⟩⟩
    have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hbody_lifted) hih
    have hrange : List.range k ++ (k :: acc) = List.range (k + 1) ++ acc := by
      rw [List.range_succ, List.append_assoc, List.singleton_append]
    rw [hrange] at hcomb
    refine ⟨_, ?_, ⟨hcomb⟩⟩
    nlinarith

theorem bmRangeList_computesStageLe :
    ComputesStageLe bmRangeList encUnary (encList encUnary) List.range
      (fun m => 5 * m * m + 12 * m + 6) := by
  intro m tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmMoveWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
    (encUnary m) [] [] tW2 (mkTapes8 [] [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
    List.append_nil, length_encUnary] at s1
  have s2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] (encodeDelimWord (encUnary m) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s2
  rcases bmRangeList_loop_le m [] tW2 tW3 tW4 tW5 tSch with ⟨tL, htL, s3⟩
  simp only [List.append_nil, encList_nil] at s3
  refine ⟨_, ?_, s1.seq (s2.seq s3)⟩
  nlinarith

/-- Wrap a single encoded element `encElem x` on `kIO` into a 1-element list
`encList encElem [x] = encodeDelimWord (encElem x)`. -/
def bmSingletonList : BitMachine :=
  (tmRevMoveWord kIO kWork0).seq
    ((tmPushEmpty kIO).seq
      (tmPrependRevWord kWork0 kIO))

theorem bmSingletonList_computesStageLe {α : Type} (encElem : α → List Bool) :
    ComputesStageLe bmSingletonList encElem (encList encElem) (fun x => [x])
      (fun x => 2 * (encElem x).length + 5) := by
  intro x tW2 tW3 tW4 tW5 tSch
  dsimp only
  have s1 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
    (encElem x) [] [] (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at s1
  have s2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] (encodeDelimWord (encElem x).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at s2
  have s3 := tmPrependRevWord_computesInTime kWork0 kIO (by decide)
    (encElem x).reverse [] [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s3
  have hsing : encodeDelimWord (encodeDelimWord (encElem x)) =
      encodeDelimWord (encList encElem [x]) := by
    simp [encList]
  rw [hsing] at s3
  have hall := s1.seq (s2.seq s3)
  refine ⟨_, by omega, hall⟩

/-- Extract the head of a list `encList encElem ys` with default `encElem defVal`:
consumes `encPair (encList encElem) encElem (ys, defVal)` and outputs `encElem (ys.headD defVal)`. -/
def bmListHeadD : BitMachine :=
  bmSeq (bmSeq (bmMapSnd bmSingletonList) bmAppendList) bmFst

theorem bmListHeadD_computesStageLe {α : Type} (encElem : α → List Bool) :
    ComputesStageLe bmListHeadD (encPair (encList encElem) encElem) encElem
      (fun p => p.1.headD p.2)
      (fun p => 30 * (encList encElem p.1).length + 30 * (encElem p.2).length + 100) := by
  intro ⟨ys, defVal⟩ tW2 tW3 tW4 tW5 tSch
  dsimp only
  have h1 := bmPairMap_computesStageLe (bmId_computesStageLe (encList encElem))
    (bmSingletonList_computesStageLe encElem)
  have h2 := bmAppendList_computesStageLe encElem
  rcases bmSeq_computesStageLe h1 h2 (ys, defVal) tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  dsimp only [id] at ht1 s1
  have hnonempty : ys ++ [defVal] = (ys.headD defVal) :: (ys ++ [defVal]).tail := by
    cases ys <;> rfl
  have henc_cons : encList encElem (ys ++ [defVal]) =
      encodeDelimWord (encElem (ys.headD defVal)) ++ encList encElem (ys ++ [defVal]).tail := by
    conv_lhs => rw [hnonempty]
    simp [encList_cons]
  rw [henc_cons] at s1
  have f1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encElem (ys.headD defVal)) ++ encList encElem (ys ++ [defVal]).tail) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at f1
  have f2 := tmDropWord_computesInTime kIO (encList encElem (ys ++ [defVal]).tail) []
    (mkTapes8 [] (encodeDelimWord (encElem (ys.headD defVal)).reverse) [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil] at f2
  have f3 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encElem (ys.headD defVal)).reverse [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at f3
  have s2 := f1.seq (f2.seq f3)
  have hlen_app : (encList encElem (ys ++ [defVal])).length =
      (encList encElem ys).length + 2 * (encElem defVal).length + 2 := by
    simp [encList, List.map_append, encodeWordStack_append]
    omega
  have hlen_split : 2 * (encElem (ys.headD defVal)).length + 2 +
      (encList encElem (ys ++ [defVal]).tail).length =
      (encList encElem (ys ++ [defVal])).length := by
    conv_rhs => rw [hnonempty]
    simp [encList_cons, length_encodeDelimWord]
  simp only [encList_cons, encList_nil, List.append_nil, length_encodeDelimWord] at ht1
  have hall := s1.seq s2
  refine ⟨_, ?_, hall⟩
  omega

/-- Drop the head of an encoded list `encList encElem ys ↦ encList encElem ys.tail` in
`≤ L + 2` steps using `tmTailWords kIO`. -/
theorem tmTailWords_encList_computesInTime {α : Type} (encElem : α → List Bool)
    (ys : List α) (L : ℕ) (hL : ∀ y ∈ ys, (encElem y).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ L + 2,
      (tmTailWords kIO).ComputesInTime
        (mkTapes8 (encodeDelimWord (encList encElem ys)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList encElem ys.tail)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have h1 := tmTailWords_computesInTime kIO (encList encElem ys) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil] at h1
  cases ys with
  | nil =>
    simp only [encList_nil, unconsDelimWord, List.length_nil] at h1
    exact ⟨1, by omega, h1⟩
  | cons y ys' =>
    simp only [encList_cons, unconsDelimWord_encodeDelimWord_append] at h1
    have hy := hL y List.mem_cons_self
    exact ⟨(encElem y).length + 1, by omega, h1⟩

theorem headD_drop_eq_getD {α : Type} :
    ∀ (idx : ℕ) (xs : List α) (d : α), (xs.drop idx).headD d = xs.getD idx d
  | 0, [], _ => rfl
  | 0, _ :: _, _ => rfl
  | _ + 1, [], _ => rfl
  | idx + 1, _ :: xs, d => headD_drop_eq_getD idx xs d

theorem length_encList_drop_le {α : Type} (encElem : α → List Bool) :
    ∀ (idx : ℕ) (xs : List α),
      (encList encElem (xs.drop idx)).length ≤ (encList encElem xs).length
  | 0, _ => le_rfl
  | _ + 1, [] => le_rfl
  | idx + 1, x :: xs => by
    have ih := length_encList_drop_le encElem idx xs
    simp only [List.drop_succ_cons, encList_cons, List.length_append]
    omega

/-- **Linear-Time Indexed List Lookup (`bmListGetD`)**:
Consumes `encPair encUnary (encPair (encList encElem) encElem) (idx, (xs, defVal))` on `kIO` and
emits `encElem (xs.getD idx defVal)` on `kIO` in $O(\text{idx} \cdot L + |xs| + |defVal|)$ steps. -/
def bmListGetD : BitMachine :=
  bmSeq bmAssocL (bmSeq (bmMapFst (bmIterLoop (tmTailWords kIO))) bmListHeadD)

theorem bmListGetD_computesInTime {α : Type} (encElem : α → List Bool)
    (idx : ℕ) (xs : List α) (defVal : α) (L : ℕ)
    (hL : ∀ x ∈ xs, (encElem x).length ≤ L)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ idx * (L + 100) + 150 * (encList encElem xs).length + 120 * (encElem defVal).length + 600,
      bmListGetD.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair (encList encElem) encElem) (idx, (xs, defVal))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encElem (xs.getD idx defVal)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have h1 := StageEval.assocL
    (fun _ : S => encUnary idx)
    (fun _ : S => encList encElem xs)
    (fun _ : S => encElem defVal)
  have hdrop : StageEval (S := S) (bmIterLoop (tmTailWords kIO))
      (encDepPair (fun _ => encUnary idx) (fun _ => encList encElem (xs.drop 0)))
      (fun _ => encList encElem (xs.drop idx))
      (fun _ => idx * (L + 5) + 2 * (encList encElem xs).length + 10) := by
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
  have h2 := StageEval.mapFst (u2 := fun _ : S => encElem defVal) hdrop
  have h3 : StageEval (S := S) bmListHeadD
      (encDepPair (fun _ => encList encElem (xs.drop idx)) (fun _ => encElem defVal))
      (fun _ => encElem (xs.getD idx defVal))
      (fun _ => 30 * (encList encElem (xs.drop idx)).length + 30 * (encElem defVal).length + 100) := by
    refine StageEval.congr_out
      (StageEval.of_computesStageLe (bmListHeadD_computesStageLe encElem)
        (fun _ => (xs.drop idx, defVal)))
      (fun _ => by
        dsimp only
        rw [headD_drop_eq_getD])
  have hall := StageEval.seq h1 (StageEval.seq h2 h3)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  simp only [List.drop_zero] at ht hcomp
  have hdrop_len := length_encList_drop_le encElem idx xs
  simp only [length_encDepPair, length_encUnary] at ht
  have hidx_le : idx * (L + 5) + 82 * idx ≤ idx * (L + 100) := by nlinarith
  exact ⟨t, by omega, hcomp⟩

/-! ## 3. Fixed-Width Signed Integer Arithmetic Stages (`encodeSignedWord W`) -/

@[simp]
theorem encodeNatBits_zero_val (W : ℕ) : encodeNatBits W 0 = encUnary W := by
  rw [encodeNatBits_zero]
  rfl

theorem takePadBits_append_of_length_eq (bs1 bs2 : List Bool) :
    takePadBits bs1.length (bs1 ++ bs2) = bs1 := by
  rw [takePadBits_eq_take_of_le bs1.length (bs1 ++ bs2) (by simp),
    List.take_append_of_le_length (le_refl _), List.take_of_length_le (le_refl _)]

theorem takePadBits_encodeNatBits :
    ∀ {W1 W2 m : ℕ}, m < 2 ^ W1 → takePadBits W2 (encodeNatBits W1 m) = encodeNatBits W2 m
  | _, 0, _, _ => rfl
  | 0, W2 + 1, m, hm => by
    have hm0 : m = 0 := by omega
    subst hm0
    rw [takePadBits_succ, encodeNatBits_succ_eq,
      show (encodeNatBits 0 0).headD false = (0 : ℕ).testBit 0 from rfl,
      show (encodeNatBits 0 0).tail = encodeNatBits 0 0 from rfl,
      Nat.zero_div, @takePadBits_encodeNatBits 0 W2 0 (by decide)]
  | W1 + 1, W2 + 1, m, hm => by
    rw [encodeNatBits_succ_eq, encodeNatBits_succ_eq, takePadBits_succ,
      List.headD_cons, List.tail_cons,
      takePadBits_encodeNatBits (by rw [Nat.pow_succ] at hm; omega)]

/-- Extract the magnitude bit-width `encUnary W` from `encodeSignedWord W x` in `≤ 4 * W + 14` steps. -/
def bmSignedWidth : BitMachine :=
  bmSeq bmLenUnary bmUnaryPred

theorem bmSignedWidth_computesStageLe (W : ℕ) :
    ComputesStageLe bmSignedWidth (encodeSignedWord W) encUnary (fun _ => W)
      (fun _ => 4 * W + 14) := by
  have h := bmSeq_computesStageLe (bmLenUnary_computesStageLe (encodeSignedWord W))
    bmUnaryPred_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun x => by
    simp [length_encodeSignedWord])).mono (fun x => ?_)
  simp only [length_encodeSignedWord]
  omega

theorem encodeSignedWord_zero (W : ℕ) :
    encUnary W ++ [true] = encodeSignedWord W 0 := by
  unfold encodeSignedWord
  have hto : (0 + (2 : ℤ) ^ W).toNat = 2 ^ W := by
    have hp : (0 : ℤ) ≤ (2 : ℤ) ^ W := by positivity
    zify; rw [Int.toNat_of_nonneg (by omega), zero_add]
  rw [hto, encodeNatBits_add_mod_div W 1 (2 ^ W), Nat.mod_self,
    Nat.div_self (Nat.two_pow_pos W), encodeNatBits_zero]
  rfl

/-- Emit `encodeSignedWord W 0 = encUnary W ++ [true]` from `encUnary W` on `kIO`. -/
def bmSignedZero : BitMachine :=
  bmSeq (bmFanout bmId (bmConstBool true)) bmAppendBits

theorem bmSignedZero_computesInTime (W : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 15 * W + 45,
      bmSignedZero.ComputesInTime
        (mkTapes8 (encodeDelimWord (encUnary W)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W 0)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have h1 := StageEval.fanout (StageEval.id_stage (fun _ : S => encUnary W))
    (StageEval.of_computesStageLe (bmConstBool_computesStageLe true encUnary) (fun _ => W))
  have h2 := StageEval.appendBits (fun _ : S => encUnary W) (fun _ : S => [true])
  have hall := StageEval.congr_out (v2 := fun _ => encodeSignedWord W 0)
    (StageEval.seq h1 h2) (fun _ => encodeSignedWord_zero W)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encBool, id] at ht hcomp
  simp only [length_encUnary, List.length_singleton] at ht
  exact ⟨t, by omega, hcomp⟩

theorem encodeSignedWord_of_nat (W m : ℕ) (hm : m < 2 ^ W) :
    encodeNatBits W m ++ [true] = encodeSignedWord W (m : ℤ) := by
  unfold encodeSignedWord
  have hto : ((m : ℤ) + (2 : ℤ) ^ W).toNat = m + 2 ^ W := by
    zify; rw [Int.toNat_of_nonneg (by positivity)]
  have hdiv : (m + 2 ^ W) / 2 ^ W = 1 := by
    have : m + 2 ^ W = m + 2 ^ W * 1 := by ring
    rw [this, Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt hm, Nat.zero_add]
  rw [hto, encodeNatBits_add_mod_div W 1 (m + 2 ^ W), Nat.add_mod_right,
    Nat.mod_eq_of_lt hm, hdiv]
  rfl

/-- Convert an unsigned bit-word `encodeNatBits b m` (`m < 2^b`, `m < 2^W`) and target width `encUnary W`
into `encodeSignedWord W (m : ℤ) = takePadBits W (encodeNatBits b m) ++ [true]`. -/
def bmNatToSigned : BitMachine :=
  bmSeq (bmFanout bmTakePadBits (bmConstBool true)) bmAppendBits

theorem bmNatToSigned_computesInTime (W b m : ℕ) (hm : m < 2 ^ b) (hmW : m < 2 ^ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 45 * W + 35 * b + 120,
      bmNatToSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encBits (W, encodeNatBits b m)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (m : ℤ)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.takePadBits_stage (fun _ : S => W) (fun _ : S => encodeNatBits b m)
  have p2 := StageEval.of_computesStageLe
    (bmConstBool_computesStageLe true (encPair encUnary encBits))
    (fun _ : S => (W, encodeNatBits b m))
  have h1 := StageEval.fanout p1 p2
  have h2 := StageEval.appendBits
    (fun _ : S => takePadBits W (encodeNatBits b m))
    (fun _ : S => [true])
  have hall := StageEval.congr_out (v2 := fun _ => encodeSignedWord W (m : ℤ))
    (StageEval.seq h1 h2) (fun _ => by
      rw [takePadBits_encodeNatBits hm, encodeSignedWord_of_nat W m hmW])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  simp only [encBool, encBits, id_eq, length_encDepPair, length_encPair, length_encUnary,
    encodeNatBits_length, length_takePadBits, List.length_singleton] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Shift a signed word `encodeSignedWord W x` left by `s` bits:
`encUnary s ++ encodeSignedWord W x = encodeSignedWord (s + W) (x * 2 ^ s)`. -/
def bmShiftLeftSigned : BitMachine :=
  bmAppendBits

theorem encodeSignedWord_mul_two_pow (s W : ℕ) (x : ℤ) (hx : FitsSignedWord W x) :
    encUnary s ++ encodeSignedWord W x =
      encodeSignedWord (s + W) (x * (2 : ℤ) ^ s) := by
  unfold encodeSignedWord
  have hx_pos : 0 ≤ x + (2 : ℤ) ^ W := by
    have := abs_lt.mp hx; omega
  have hto : (x * (2 : ℤ) ^ s + (2 : ℤ) ^ (s + W)).toNat =
      2 ^ s * (x + (2 : ℤ) ^ W).toNat := by
    have hring : x * (2 : ℤ) ^ s + (2 : ℤ) ^ (s + W) = (2 : ℤ) ^ s * (x + (2 : ℤ) ^ W) := by
      rw [pow_add]; ring
    rw [hring]
    zify
    rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) hx_pos),
      Int.toNat_of_nonneg hx_pos]
  rw [show s + W + 1 = s + (W + 1) by omega, hto,
    encodeNatBits_add_mod_div s (W + 1) (2 ^ s * (x + (2 : ℤ) ^ W).toNat),
    Nat.mul_mod_right, Nat.mul_div_right _ (Nat.two_pow_pos s), encodeNatBits_zero]
  rfl

theorem bmShiftLeftSigned_computesInTime (s W : ℕ) (x : ℤ) (hx : FitsSignedWord W x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * s + 2 * W + 10,
      bmShiftLeftSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encodeSignedWord W) (s, x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (s + W) (x * (2 : ℤ) ^ s)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  rcases bmAppendBits_computesStageLe (encUnary s, encodeSignedWord W x)
    tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encBits, id] at ht hcomp
  simp only [length_encUnary, length_encodeSignedWord] at ht
  rw [encodeSignedWord_mul_two_pow s W x hx] at hcomp
  exact ⟨t, by omega, hcomp⟩

theorem drop_encodeSignedWord_eq_sign (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x) :
    (encodeSignedWord W x).drop W = [decide (0 ≤ x)] := by
  unfold encodeSignedWord
  have hx_bounds := abs_lt.mp hx
  have hnonneg : 0 ≤ x + (2 : ℤ) ^ W := by omega
  set U := (x + (2 : ℤ) ^ W).toNat
  have hU_lt : U < 2 * 2 ^ W := by
    dsimp [U]; zify; rw [Int.toNat_of_nonneg hnonneg]; omega
  have hdiv_eq : decide ((U / 2 ^ W) % 2 = 1) = decide (0 ≤ x) := by
    by_cases hx0 : 0 ≤ x
    · have hU_ge : 2 ^ W ≤ U := by
        dsimp [U]; zify; rw [Int.toNat_of_nonneg hnonneg]; omega
      have hdiv1 : U / 2 ^ W = 1 := by
        have h1 : 1 ≤ U / 2 ^ W := (Nat.le_div_iff_mul_le (Nat.two_pow_pos W)).mpr (by omega)
        have h2 : U / 2 ^ W < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos W)).mpr hU_lt
        omega
      simp [hx0, hdiv1]
    · have hU_ltW : U < 2 ^ W := by
        dsimp [U]; zify; rw [Int.toNat_of_nonneg hnonneg]; omega
      have hdiv0 : U / 2 ^ W = 0 := Nat.div_eq_of_lt hU_ltW
      simp [hx0, hdiv0]
  rw [encodeNatBits_add_mod_div W 1 U,
    List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp), List.nil_append,
    encodeNatBits_succ_mod_div 0 (U / 2 ^ W), hdiv_eq]
  rfl

theorem shrink_encodeSignedWord_succ (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x) :
    takePadBits W (encodeSignedWord (W + 1) x) ++
      (encodeSignedWord (W + 1) x).drop (W + 1) = encodeSignedWord W x := by
  have hx1 : FitsSignedWord (W + 1) x := hx.mono (Nat.le_succ W)
  rw [drop_encodeSignedWord_eq_sign (W + 1) x hx1]
  have hsplitW : encodeSignedWord W x =
      takePadBits W (encodeSignedWord W x) ++ [decide (0 ≤ x)] := by
    have h1 := (List.take_append_drop W (encodeSignedWord W x)).symm
    rwa [← takePadBits_eq_take_of_le W (encodeSignedWord W x) (by simp [length_encodeSignedWord]),
      drop_encodeSignedWord_eq_sign W x hx] at h1
  rw [hsplitW]
  congr 1
  unfold encodeSignedWord
  have hx_bounds := abs_lt.mp hx
  have hnonneg : 0 ≤ x + (2 : ℤ) ^ W := by omega
  have hto : (x + (2 : ℤ) ^ (W + 1)).toNat = (x + (2 : ℤ) ^ W).toNat + 2 ^ W := by
    have hring : x + (2 : ℤ) ^ (W + 1) = (x + (2 : ℤ) ^ W) + (2 : ℤ) ^ W := by
      rw [pow_succ']; ring
    rw [hring]
    zify
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hnonneg]
  rw [hto, show W + 1 + 1 = W + 2 from rfl,
    encodeNatBits_add_mod_div W 2 ((x + (2 : ℤ) ^ W).toNat + 2 ^ W),
    encodeNatBits_add_mod_div W 1 (x + (2 : ℤ) ^ W).toNat,
    Nat.add_mod_right]
  have htake := takePadBits_append_of_length_eq (encodeNatBits W ((x + (2 : ℤ) ^ W).toNat % 2 ^ W))
  simp only [encodeNatBits_length] at htake
  rw [htake, htake]

/-- Shrink `encodeSignedWord (W + 1) x` to `encodeSignedWord W x` when `FitsSignedWord W x`. -/
def bmShrinkSigned1 : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq (bmFanout (bmSeq bmSignedWidth bmUnaryPred) bmId) bmTakePadBits)
      (bmSeq (bmFanout bmSignedWidth bmId) bmDropBits))
    bmAppendBits

theorem bmShrinkSigned1_computesInTime (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 450 * W + 1100,
      bmShrinkSigned1.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord (W + 1) x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encodeSignedWord (W + 1) x
  have pW1 := StageEval.of_computesStageLe (bmSignedWidth_computesStageLe (W + 1)) (fun _ : S => x)
  have pW := StageEval.congr_out (v2 := fun _ => encUnary W)
    (StageEval.seq pW1 (StageEval.of_computesStageLe bmUnaryPred_computesStageLe (fun _ : S => W + 1)))
    (fun _ => by simp)
  have pLo := StageEval.seq (StageEval.fanout pW (StageEval.id_stage uIn))
    (StageEval.takePadBits_stage (fun _ : S => W) uIn)
  have pHi := StageEval.seq (StageEval.fanout pW1 (StageEval.id_stage uIn))
    (StageEval.dropBits (fun _ : S => W + 1) uIn)
  have hall := StageEval.congr_out (v2 := fun _ => encodeSignedWord W x)
    (StageEval.seq (StageEval.fanout pLo pHi)
      (StageEval.appendBits
        (fun _ : S => takePadBits W (encodeSignedWord (W + 1) x))
        (fun _ : S => (encodeSignedWord (W + 1) x).drop (W + 1))))
    (fun _ => shrink_encodeSignedWord_succ W x hx)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encodeSignedWord, length_encUnary, length_takePadBits,
    List.length_drop] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Extended signed addition: `(encodeSignedWord W x, encodeSignedWord W y) ↦ encodeSignedWord (W + 1) (x + y)`. -/
def bmSignedAddExt : BitMachine :=
  bmSeq bmSignedButterfly bmFst

theorem bmSignedAddExt_computesInTime (W : ℕ) (x y : ℤ)
    (hx : FitsSignedWord W x) (hy : FitsSignedWord W y)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 130 * W + 180,
      bmSignedAddExt.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (W + 1) (x + y)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  rcases bmSignedButterfly_computesInTime W x y hx hy tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmFst_computesStageLe (encodeSignedWord (W + 1)) (encodeSignedWord (W + 1))
    (x + y, x - y) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  dsimp only at ht2 s2
  simp only [length_encodeSignedWord] at ht2
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

/-- Extended signed subtraction: `(encodeSignedWord W x, encodeSignedWord W y) ↦ encodeSignedWord (W + 1) (x - y)`. -/
def bmSignedSubExt : BitMachine :=
  bmSeq bmSignedButterfly bmSnd

theorem bmSignedSubExt_computesInTime (W : ℕ) (x y : ℤ)
    (hx : FitsSignedWord W x) (hy : FitsSignedWord W y)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 130 * W + 180,
      bmSignedSubExt.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (W + 1) (x - y)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  rcases bmSignedButterfly_computesInTime W x y hx hy tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmSnd_computesStageLe (encodeSignedWord (W + 1)) (encodeSignedWord (W + 1))
    (x + y, x - y) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  dsimp only at ht2 s2
  simp only [length_encodeSignedWord] at ht2
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

/-- Fixed-width signed addition: `(encodeSignedWord W x, encodeSignedWord W y) ↦ encodeSignedWord W (x + y)`
when `FitsSignedWord W x`, `FitsSignedWord W y`, and `FitsSignedWord W (x + y)`. -/
def bmSignedAdd : BitMachine :=
  bmSeq bmSignedAddExt bmShrinkSigned1

theorem bmSignedAdd_computesInTime (W : ℕ) (x y : ℤ)
    (hx : FitsSignedWord W x) (hy : FitsSignedWord W y) (hxy : FitsSignedWord W (x + y))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 580 * W + 1300,
      bmSignedAdd.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (x + y)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  rcases bmSignedAddExt_computesInTime W x y hx hy tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmShrinkSigned1_computesInTime W (x + y) hxy tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

/-- Fixed-width signed subtraction: `(encodeSignedWord W x, encodeSignedWord W y) ↦ encodeSignedWord W (x - y)`
when `FitsSignedWord W x`, `FitsSignedWord W y`, and `FitsSignedWord W (x - y)`. -/
def bmSignedSub : BitMachine :=
  bmSeq bmSignedSubExt bmShrinkSigned1

theorem bmSignedSub_computesInTime (W : ℕ) (x y : ℤ)
    (hx : FitsSignedWord W x) (hy : FitsSignedWord W y) (hxy : FitsSignedWord W (x - y))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 580 * W + 1300,
      bmSignedSub.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (x - y)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  rcases bmSignedSubExt_computesInTime W x y hx hy tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmShrinkSigned1_computesInTime W (x - y) hxy tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

/-- Fixed-width signed negation: `encodeSignedWord W x ↦ encodeSignedWord W (-x)` when `FitsSignedWord W x`. -/
def bmSignedNeg : BitMachine :=
  bmSeq (bmFanout (bmSeq bmSignedWidth bmSignedZero) bmId) bmSignedSub

theorem bmSignedNeg_computesInTime (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 620 * W + 1500,
      bmSignedNeg.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (-x))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.seq
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => x))
    (StageEval.const (bmSignedZero_computesInTime W))
  have p2 := StageEval.id_stage (fun _ : S => encodeSignedWord W x)
  have h1 := StageEval.fanout p1 p2
  have h2 := StageEval.congr_out (v2 := fun _ => encodeSignedWord W (-x))
    (StageEval.const (S := S) (bmSignedSub_computesInTime W 0 x (FitsSignedWord.zero W) hx
      (by simpa using hx.neg)))
    (fun _ => by simp)
  rcases StageEval.seq h1 h2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Test whether `x < 0` from `encodeSignedWord W x` (`FitsSignedWord W x`): emits `encBool (decide (x < 0))`. -/
def bmSignedIsNeg : BitMachine :=
  bmSeq (bmSeq (bmFanout bmSignedWidth bmId) bmDropBits) bmBoolNot

theorem bmSignedIsNeg_computesInTime (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 40 * W + 125,
      bmSignedIsNeg.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encBool (decide (x < 0)))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => x)
  have p2 := StageEval.id_stage (fun _ : S => encodeSignedWord W x)
  have h1 := StageEval.fanout p1 p2
  have h2 := StageEval.dropBits (fun _ : S => W) (fun _ : S => encodeSignedWord W x)
  have h12 := StageEval.congr_out (v2 := fun _ => encBool (decide (0 ≤ x)))
    (StageEval.seq h1 h2)
    (fun _ => drop_encodeSignedWord_eq_sign W x hx)
  have h3 := StageEval.of_computesStageLe bmBoolNot_computesStageLe
    (fun _ : S => decide (0 ≤ x))
  have hall := StageEval.congr_out (v2 := fun _ => encBool (decide (x < 0)))
    (StageEval.seq h12 h3) (fun _ => by
      congr 1
      by_cases h : x < 0
      · simp [h, not_le.mpr h]
      · simp [h, not_lt.mp h])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  simp only [length_encodeSignedWord, length_encUnary] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Extract the unsigned magnitude bits `encodeNatBits W x.natAbs` from `encodeSignedWord W x`
(`FitsSignedWord W x`). -/
def bmSignedMagBits : BitMachine :=
  bmSeq (bmIte bmSignedIsNeg bmSignedNeg bmId)
    (bmSeq (bmFanout bmSignedWidth bmId) bmTakePadBits)

theorem bmSignedMagBits_computesInTime (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 700 * W + 1800,
      bmSignedMagBits.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeNatBits W x.natAbs)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encodeSignedWord W x
  have hx_nat : x.natAbs < 2 ^ W := (fitsSignedWord_iff_natAbs_lt W x).mp hx
  have pAbs : StageEval (S := S) (bmIte bmSignedIsNeg bmSignedNeg bmId)
      uIn (fun _ => encodeSignedWord W (x.natAbs : ℤ))
      (fun _ => 670 * W + 1650) := by
    have pCond := StageEval.const (S := S) (bmSignedIsNeg_computesInTime W x hx)
    have pNeg := StageEval.const (S := S) (bmSignedNeg_computesInTime W x hx)
    have pId := StageEval.id_stage uIn
    refine StageEval.congr_out (v2 := fun _ => encodeSignedWord W (x.natAbs : ℤ))
      ((StageEval.ite_stage pCond pNeg pId).mono (fun _ => by
        simp only [length_encodeSignedWord]
        split_ifs <;> omega))
      (fun _ => by
        dsimp only [uIn]
        by_cases hneg : x < 0
        · rw [if_pos (decide_eq_true hneg), Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)]
        · rw [if_neg (by simp [hneg]), Int.natAbs_of_nonneg (not_lt.mp hneg)])
  have pW := StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W)
    (fun _ : S => (x.natAbs : ℤ))
  have pTake := StageEval.congr_out (v2 := fun _ => encodeNatBits W x.natAbs)
    (StageEval.seq
      (StageEval.fanout pW (StageEval.id_stage (fun _ : S => encodeSignedWord W (x.natAbs : ℤ))))
      (StageEval.takePadBits_stage (fun _ : S => W)
        (fun _ : S => encodeSignedWord W (x.natAbs : ℤ))))
    (fun _ => by
      rw [← encodeSignedWord_of_nat W x.natAbs hx_nat]
      have htake := takePadBits_append_of_length_eq (encodeNatBits W x.natAbs) [true]
      simpa only [encodeNatBits_length] using htake)
  rcases StageEval.seq pAbs pTake () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encodeSignedWord, length_encUnary] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Resize `encodeSignedWord W1 x` to `encodeSignedWord W2 x` given
`encPair encUnary (encodeSignedWord W1) (W2, x)` when `FitsSignedWord W1 x` and `FitsSignedWord W2 x`. -/
def bmResizeSignedWord : BitMachine :=
  let bmPos := bmSeq (bmMapSnd bmSignedMagBits) bmNatToSigned
  bmIte (bmSeq bmSnd bmSignedIsNeg) (bmSeq bmPos bmSignedNeg) bmPos

theorem bmResizeSignedWord_computesInTime (W1 W2 : ℕ) (x : ℤ)
    (hx1 : FitsSignedWord W1 x) (hx2 : FitsSignedWord W2 x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 1000 * W1 + 1000 * W2 + 5000,
      bmResizeSignedWord.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encodeSignedWord W1) (W2, x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W2 x))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encPair encUnary (encodeSignedWord W1) (W2, x)
  have hx1_nat : x.natAbs < 2 ^ W1 := (fitsSignedWord_iff_natAbs_lt W1 x).mp hx1
  have hx2_nat : x.natAbs < 2 ^ W2 := (fitsSignedWord_iff_natAbs_lt W2 x).mp hx2
  have hpos_fits : FitsSignedWord W2 (x.natAbs : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact hx2_nat
  have pMag := StageEval.mapSnd (u1 := fun _ : S => encUnary W2)
    (StageEval.const (S := S) (bmSignedMagBits_computesInTime W1 x hx1))
  have pPos := StageEval.seq pMag
    (StageEval.const (S := S) (bmNatToSigned_computesInTime W2 W1 x.natAbs hx1_nat hx2_nat))
  have pNeg := StageEval.seq pPos
    (StageEval.const (S := S) (bmSignedNeg_computesInTime W2 (x.natAbs : ℤ) hpos_fits))
  have pCond := StageEval.seq
    (StageEval.snd (fun _ : S => encUnary W2) (fun _ : S => encodeSignedWord W1 x))
    (StageEval.const (S := S) (bmSignedIsNeg_computesInTime W1 x hx1))
  have hall := StageEval.congr_out (v2 := fun _ => encodeSignedWord W2 x)
    (StageEval.ite_stage pCond pNeg pPos) (fun _ => by
      by_cases hneg : x < 0
      · rw [if_pos (decide_eq_true hneg), Int.ofNat_natAbs_of_nonpos (le_of_lt hneg), neg_neg]
      · rw [if_neg (by simp [hneg]), Int.natAbs_of_nonneg (not_lt.mp hneg)])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord,
    encodeNatBits_length] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- Extend `encodeSignedWord W x` to `encodeSignedWord (W + 1) x` when `FitsSignedWord W x`. -/
def bmExtendSigned1 : BitMachine :=
  bmSeq (bmFanout (bmSeq bmSignedWidth bmUnarySucc) bmId) bmResizeSignedWord

theorem bmExtendSigned1_computesInTime (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2200 * W + 7000,
      bmExtendSigned1.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (W + 1) x)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.seq
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => x))
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => W))
  have p2 := StageEval.id_stage (fun _ : S => encodeSignedWord W x)
  have h1 := StageEval.fanout p1 p2
  have h2 := StageEval.const (S := S)
    (bmResizeSignedWord_computesInTime W (W + 1) x hx (hx.mono (Nat.le_succ W)))
  rcases StageEval.seq h1 h2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  simp only [length_encodeSignedWord, length_encUnary] at ht
  exact ⟨t, by linarith only [ht], hcomp⟩

theorem encodeSignedWord_one (w : ℕ) (hw : 1 ≤ w) :
    [true] ++ encodeSignedWord (w - 1) 0 = encodeSignedWord w 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0) with ⟨w', rfl⟩
  rw [Nat.succ_sub_one, ← encodeSignedWord_zero w']
  unfold encodeSignedWord
  have hto : (1 + (2 : ℤ) ^ (w' + 1)).toNat = 1 + 2 * 2 ^ w' := by
    have hring : 1 + (2 : ℤ) ^ (w' + 1) = 1 + 2 * (2 : ℤ) ^ w' := by rw [pow_succ']
    rw [hring]
    zify
    rw [Int.toNat_of_nonneg (by positivity)]
  have htb : (1 + 2 * 2 ^ w').testBit 0 = true := by
    rw [Nat.testBit_zero, decide_eq_true_iff]
    omega
  have hdiv : (1 + 2 * 2 ^ w') / 2 = 2 ^ w' := by omega
  rw [hto, encodeNatBits_succ_eq (w' + 1) (1 + 2 * 2 ^ w'), htb, hdiv,
    encodeNatBits_add_mod_div w' 1 (2 ^ w'), Nat.mod_self,
    Nat.div_self (Nat.two_pow_pos w'), encodeNatBits_zero]
  rfl

/-! ### Branch-Free Linear-Time `bmRoundShiftSigned` (`(k, encodeSignedWord W m) ↦ encodeSignedWord W (roundShiftInt m k)`) -/

theorem drop_encodeSignedWord_roundShiftInt (W k : ℕ) {m : ℤ} (hm : FitsSignedWord W m) :
    (encodeSignedWord (k + (W + 1)) (2 * m + (2 : ℤ) ^ k)).drop (k + 1) =
      encodeSignedWord W (roundShiftInt m k) := by
  unfold encodeSignedWord
  have hm_bounds := abs_lt.mp hm
  have h2k_pos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  have hpow_split : (2 : ℤ) ^ (k + (W + 1)) = (2 : ℤ) ^ W * (2 : ℤ) ^ (k + 1) := by
    rw [show k + (W + 1) = W + (k + 1) by omega, pow_add]
  have h2W_le : 2 * (2 : ℤ) ^ W ≤ (2 : ℤ) ^ (k + (W + 1)) := by
    have : (2 : ℤ) ^ (1 + W) ≤ (2 : ℤ) ^ (k + (W + 1)) :=
      pow_le_pow_right₀ (by decide) (by omega)
    simpa [pow_add] using this
  have hnum_nonneg : 0 ≤ 2 * m + (2 : ℤ) ^ k + (2 : ℤ) ^ (k + (W + 1)) := by omega
  have hq_nonneg : 0 ≤ roundShiftInt m k + (2 : ℤ) ^ W := by
    have := abs_lt.mp (hm.roundShiftInt k); omega
  have hdiv_int :
      (2 * m + (2 : ℤ) ^ k + (2 : ℤ) ^ (k + (W + 1))) / (2 : ℤ) ^ (k + 1) =
        roundShiftInt m k + (2 : ℤ) ^ W := by
    rw [hpow_split, Int.add_mul_ediv_right _ _ (by positivity)]
    congr 1
    unfold roundShiftInt
    split_ifs with hk0
    · subst hk0
      simp only [pow_zero, zero_add, pow_one]
      have hcomm : 2 * m + 1 = 1 + m * 2 := by ring
      rw [hcomm, Int.add_mul_ediv_right _ _ (by decide)]
      have h12 : (1 : ℤ) / 2 = 0 := rfl
      omega
    · have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)).symm
      have hnum : 2 * m + (2 : ℤ) ^ k = 2 * (m + (2 : ℤ) ^ (k - 1)) := by
        conv_lhs => rw [hk1, pow_succ']
        ring
      have hden : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by rw [pow_succ']
      rw [hnum, hden, Int.mul_ediv_mul_of_pos _ _ (by decide)]
  have hdiv_nat :
      (2 * m + (2 : ℤ) ^ k + (2 : ℤ) ^ (k + (W + 1))).toNat / 2 ^ (k + 1) =
        (roundShiftInt m k + (2 : ℤ) ^ W).toNat := by
    zify
    rw [Int.toNat_of_nonneg hnum_nonneg, Int.toNat_of_nonneg hq_nonneg, hdiv_int]
  rw [show k + (W + 1) + 1 = (k + 1) + (W + 1) by omega,
    encodeNatBits_add_mod_div (k + 1) (W + 1),
    List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp),
    List.nil_append, hdiv_nat]

/-- **Branch-Free Linear-Time Rounded Right-Shift (`bmRoundShiftSigned`)**:
Consumes `encPair encUnary (encodeSignedWord W) (k, m)` (`FitsSignedWord W m`) on `kIO` and emits
`encodeSignedWord W (roundShiftInt m k)` on `kIO` in **strictly linear** $O(W + k)$ `TM2.step` transitions. -/
def bmRoundShiftSigned : BitMachine :=
  let bmTargetW : BitMachine := bmSeq (bmMapSnd bmLenUnary) bmUnaryAdd
  let bmTerm1 : BitMachine :=
    bmSeq (bmFanout bmTargetW (bmSeq bmSnd (tmConsBit false kIO))) bmResizeSignedWord
  let bmOneW1 : BitMachine :=
    bmSeq (bmSeq (bmSeq bmSnd bmSignedWidth) bmSignedZero) (tmConsBit true kIO)
  let bmTerm2 : BitMachine := bmSeq (bmFanout bmFst bmOneW1) bmShiftLeftSigned
  let bmSum : BitMachine := bmSeq (bmFanout bmTerm1 bmTerm2) bmSignedAdd
  bmSeq (bmFanout (bmSeq bmFst bmUnarySucc) bmSum) bmDropBits

theorem bmRoundShiftSigned_computesInTime (W k : ℕ) (m : ℤ) (hm : FitsSignedWord W m)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 5000 * W + 5000 * k + 18000,
      bmRoundShiftSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encodeSignedWord W) (k, m)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (roundShiftInt m k)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encPair encUnary (encodeSignedWord W) (k, m)
  have pK := StageEval.fst (fun _ : S => encUnary k) (fun _ : S => encodeSignedWord W m)
  have pM := StageEval.snd (fun _ : S => encUnary k) (fun _ : S => encodeSignedWord W m)
  have pTargetW : StageEval (S := S) (bmSeq (bmMapSnd bmLenUnary) bmUnaryAdd)
      uIn (fun _ => encUnary (k + (W + 1)))
      (fun _ => 25 * k + 35 * W + 120) := by
    have pLen := StageEval.congr_out (v2 := fun _ => encUnary (W + 1))
      (StageEval.of_computesStageLe (bmLenUnary_computesStageLe (encodeSignedWord W))
        (fun _ : S => m))
      (fun _ => by simp [length_encodeSignedWord])
    exact (StageEval.seq (StageEval.mapSnd (u1 := fun _ : S => encUnary k) pLen)
      (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (k, W + 1)))).mono
      (fun _ => by simp only [length_encUnary, length_encodeSignedWord]; omega)
  have hcons0 : StageEval (S := S) (tmConsBit false kIO)
      (fun _ => encodeSignedWord W m)
      (fun _ => encodeSignedWord (1 + W) (2 * m))
      (fun _ => 1) := by
    intro _ u2 u3 u4 u5 uS
    have hc := tmConsBit_computesInTime false kIO
      (mkTapes8 (encodeDelimWord (encodeSignedWord W m)) [] [] u2 u3 u4 u5 uS)
      (encodeSignedWord W m) [] (by simp)
    simp only [update_mkTapes8_kIO, List.append_nil] at hc
    have heq : false :: encodeSignedWord W m = encodeSignedWord (1 + W) (2 * m) := by
      simpa [encUnary, mul_comm] using encodeSignedWord_mul_two_pow 1 W m hm
    rw [heq] at hc
    exact ⟨1, le_rfl, hc⟩
  have p2m := StageEval.seq pM hcons0
  have h2m_fits1 : FitsSignedWord (1 + W) (2 * m) := by
    simpa [Nat.add_comm 1 W, mul_comm 2 m] using hm.mul_two_pow 1
  have h2m_fitsTarget : FitsSignedWord (k + (W + 1)) (2 * m) :=
    h2m_fits1.mono (by omega)
  have pTerm1 := StageEval.seq (StageEval.fanout pTargetW p2m)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime (1 + W) (k + (W + 1)) (2 * m) h2m_fits1 h2m_fitsTarget))
  have hcons1 : StageEval (S := S) (tmConsBit true kIO)
      (fun _ => encodeSignedWord W 0)
      (fun _ => encodeSignedWord (W + 1) 1)
      (fun _ => 1) := by
    intro _ u2 u3 u4 u5 uS
    have hc := tmConsBit_computesInTime true kIO
      (mkTapes8 (encodeDelimWord (encodeSignedWord W 0)) [] [] u2 u3 u4 u5 uS)
      (encodeSignedWord W 0) [] (by simp)
    simp only [update_mkTapes8_kIO, List.append_nil] at hc
    have heq : true :: encodeSignedWord W 0 = encodeSignedWord (W + 1) 1 := by
      simpa using encodeSignedWord_one (W + 1) (by omega)
    rw [heq] at hc
    exact ⟨1, le_rfl, hc⟩
  have pW := StageEval.seq pM
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => m))
  have pZeroW := StageEval.seq pW (StageEval.const (S := S) (bmSignedZero_computesInTime W))
  have pOneW1 := StageEval.seq pZeroW hcons1
  have h1_fits : FitsSignedWord (W + 1) 1 := by
    unfold FitsSignedWord
    rw [abs_one]
    exact one_lt_pow₀ (by decide : (1 : ℤ) < 2) (by omega)
  have pTerm2 := StageEval.congr_out (v2 := fun _ => encodeSignedWord (k + (W + 1)) ((2 : ℤ) ^ k))
    (StageEval.seq (StageEval.fanout pK pOneW1)
      (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime k (W + 1) 1 h1_fits)))
    (fun _ => by rw [one_mul])
  have h2k_fitsTarget : FitsSignedWord (k + (W + 1)) ((2 : ℤ) ^ k) :=
    (FitsSignedWord.two_pow k).mono (by omega)
  have hSum_fitsTarget : FitsSignedWord (k + (W + 1)) (2 * m + (2 : ℤ) ^ k) := by
    have hm_abs := abs_lt.mp hm
    have h2m_abs : |2 * m| ≤ 2 * (2 : ℤ) ^ W - 2 := by
      rw [abs_le]; constructor <;> omega
    have htri := abs_add_le (2 * m) ((2 : ℤ) ^ k)
    have h2k_abs : |(2 : ℤ) ^ k| = (2 : ℤ) ^ k := abs_of_pos (by positivity)
    unfold FitsSignedWord
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp only [Nat.zero_add, pow_zero, pow_succ'] at htri h2k_abs ⊢
      omega
    · have h1 : 2 * (2 : ℤ) ^ W ≤ (2 : ℤ) ^ (k + W) := by
        have : (2 : ℤ) ^ (1 + W) ≤ (2 : ℤ) ^ (k + W) :=
          pow_le_pow_right₀ (by decide) (by omega)
        simpa [pow_add] using this
      have h2 : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ (k + W) :=
        pow_le_pow_right₀ (by decide) (by omega)
      have h3 : (2 : ℤ) ^ (k + (W + 1)) = 2 * (2 : ℤ) ^ (k + W) := by
        rw [show k + (W + 1) = (k + W) + 1 by omega, pow_succ']
      omega
  have pSum := StageEval.seq (StageEval.fanout pTerm1 pTerm2)
    (StageEval.const (S := S)
      (bmSignedAdd_computesInTime (k + (W + 1)) (2 * m) ((2 : ℤ) ^ k)
        h2m_fitsTarget h2k_fitsTarget hSum_fitsTarget))
  have pK1 := StageEval.seq pK
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => k))
  have hall := StageEval.congr_out (v2 := fun _ => encodeSignedWord W (roundShiftInt m k))
    (StageEval.seq (StageEval.fanout pK1 pSum)
      (StageEval.dropBits (fun _ : S => k + 1)
        (fun _ : S => encodeSignedWord (k + (W + 1)) (2 * m + (2 : ℤ) ^ k))))
    (fun _ => drop_encodeSignedWord_roundShiftInt W k hm)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Division by 2 with round-half-up on `encodeSignedWord W x`:
`encodeSignedWord W x ↦ encodeSignedWord W (roundShiftInt x 1)`. -/
def bmHalfRoundedSigned : BitMachine :=
  bmSeq (bmFanout (bmUnaryConst 1) bmId) bmRoundShiftSigned

theorem bmHalfRoundedSigned_computesInTime (W : ℕ) (x : ℤ) (hx : FitsSignedWord W x)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 5010 * W + 24000,
      bmHalfRoundedSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (roundShiftInt x 1)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.of_computesStageLe
    (bmUnaryConst_computesStageLe 1 (encodeSignedWord W)) (fun _ : S => x)
  have p2 := StageEval.id_stage (fun _ : S => encodeSignedWord W x)
  have h1 := StageEval.fanout p1 p2
  have h2 := StageEval.const (S := S) (bmRoundShiftSigned_computesInTime W 1 x hx)
  rcases StageEval.seq h1 h2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  simp only [length_encodeSignedWord, length_encUnary] at ht
  exact ⟨t, by linarith only [ht], hcomp⟩

/-! ### Parameterized Bit-List Multiplier Interface (`IsBitMulMachine`) & `bmSignedMulWith` -/

/-- Specification for a uniform `BitMachine` implementing bit-list unsigned multiplication:
consumes `encPair encUnary (encPair encBits encBits) (w, (aBits, bBits))` (with `aBits.length = w`
and `bBits.length = w`) on `kIO` and emits `encodeNatBits (2 * w) (decodeNatBits aBits * decodeNatBits bBits)`
on `kIO` in `≤ mulTime w` `TM2.step` transitions. -/
def IsBitMulMachine (bmMul : BitMachine) (mulTime : ℕ → ℕ) : Prop :=
  ∀ (w : ℕ) (aBits bBits : List Bool),
    aBits.length = w → bBits.length = w →
    ∀ (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ mulTime w,
        bmMul.ComputesInTime
          (mkTapes8 (encodeDelimWord
            (encPair encUnary (encPair encBits encBits) (w, (aBits, bBits))))
            [] [] tW2 tW3 tW4 tW5 tSch)
          (mkTapes8 (encodeDelimWord
            (encodeNatBits (2 * w) (decodeNatBits aBits * decodeNatBits bBits)))
            [] [] tW2 tW3 tW4 tW5 tSch) t

/-- Base-case shift-and-add multiplier `bmShiftAddMulBits` satisfies `IsBitMulMachine`. -/
theorem isBitMulMachine_bmShiftAddMulBits :
    IsBitMulMachine bmShiftAddMulBits (fun w => 11 * w * w + 750 * w + 1300) := by
  intro w aBits bBits ha hb tW2 tW3 tW4 tW5 tSch
  rcases bmShiftAddMulBits_computesInTime w aBits bBits tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  rw [binaryShiftAddMulBitsTracked_fst,
    List.take_of_length_le (by omega : aBits.length ≤ w),
    List.take_of_length_le (by omega : bBits.length ≤ w)] at hcomp
  simp only [ha, hb] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- **Parameterized Signed Word Multiplication (`bmSignedMulWith bmMul`)**:
Consumes `encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)` on `kIO` and emits
`encodeSignedWord (2 * W) (x * y)` on `kIO` using `bmMul` on `(W, (x.natAbs, y.natAbs))`
and sign-XOR negation (`bmSignedNeg`). -/
def bmSignedMulWith (bmMul : BitMachine) : BitMachine :=
  let bmW := bmSeq bmFst bmSignedWidth
  let bmTwoW := bmSeq bmW bmUnaryDouble
  let bmMagPair := bmPairMap bmSignedMagBits bmSignedMagBits
  let bmProdBits := bmSeq (bmFanout bmW bmMagPair) bmMul
  let bmPosProd := bmSeq (bmFanout bmTwoW bmProdBits) bmNatToSigned
  let bmSignXor := bmSeq (bmPairMap bmSignedIsNeg bmSignedIsNeg) bmBoolXor
  bmIte bmSignXor (bmSeq bmPosProd bmSignedNeg) bmPosProd

theorem signed_mul_eq_ite_natAbs (x y : ℤ) :
    (if (decide (x < 0) != decide (y < 0)) = true then
      -(((x.natAbs * y.natAbs : ℕ) : ℤ))
    else
      (((x.natAbs * y.natAbs : ℕ) : ℤ))) = x * y := by
  rw [← Int.natAbs_mul]
  rcases lt_or_ge x 0 with hx | hx <;> rcases lt_or_ge y 0 with hy | hy
  · have hxy : 0 ≤ x * y := le_of_lt (mul_pos_of_neg_of_neg hx hy)
    simp [hx, hy, Int.natAbs_of_nonneg hxy]
  · have hxy : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hx) hy
    simp [hx, not_lt.mpr hy, Int.ofNat_natAbs_of_nonpos hxy]
  · have hxy : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (le_of_lt hy)
    simp [not_lt.mpr hx, hy, Int.ofNat_natAbs_of_nonpos hxy]
  · have hxy : 0 ≤ x * y := mul_nonneg hx hy
    simp [not_lt.mpr hx, not_lt.mpr hy, Int.natAbs_of_nonneg hxy]

theorem bmSignedMulWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W : ℕ) (x y : ℤ) (hx : FitsSignedWord W x) (hy : FitsSignedWord W y)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * mulTime W + 5000 * W + 12000,
      (bmSignedMulWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (2 * W) (x * y)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)
  have hx_nat : x.natAbs < 2 ^ W := (fitsSignedWord_iff_natAbs_lt W x).mp hx
  have hy_nat : y.natAbs < 2 ^ W := (fitsSignedWord_iff_natAbs_lt W y).mp hy
  have hprod_nat : x.natAbs * y.natAbs < 2 ^ (2 * W) := by
    rw [Nat.two_mul, pow_add]
    exact Nat.mul_lt_mul'' hx_nat hy_nat
  have pW := StageEval.seq
    (StageEval.fst (fun _ : S => encodeSignedWord W x) (fun _ : S => encodeSignedWord W y))
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ => x))
  have pTwoW := StageEval.seq pW
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ => W))
  have pMagX := StageEval.const (S := S) (bmSignedMagBits_computesInTime W x hx)
  have pMagY := StageEval.const (S := S) (bmSignedMagBits_computesInTime W y hy)
  have pMagPair := StageEval.pairMap pMagX pMagY
  have pMul : StageEval (S := S) bmMul
      (encDepPair (fun _ => encUnary W)
        (encDepPair (fun _ => encodeNatBits W x.natAbs) (fun _ => encodeNatBits W y.natAbs)))
      (fun _ => encodeNatBits (2 * W) (x.natAbs * y.natAbs))
      (fun _ => mulTime W) := by
    intro _ u2 u3 u4 u5 uS
    have hm := hmul W (encodeNatBits W x.natAbs) (encodeNatBits W y.natAbs)
      (encodeNatBits_length W x.natAbs) (encodeNatBits_length W y.natAbs) u2 u3 u4 u5 uS
    simpa only [encDepPair, encPair, encBits, id,
      decodeNatBits_encodeNatBits W x.natAbs hx_nat,
      decodeNatBits_encodeNatBits W y.natAbs hy_nat] using hm
  have pProdBits := StageEval.seq (StageEval.fanout pW pMagPair) pMul
  have pNatToSigned := StageEval.const (S := S)
    (bmNatToSigned_computesInTime (2 * W) (2 * W) (x.natAbs * y.natAbs) hprod_nat hprod_nat)
  have pPosProd := StageEval.seq (StageEval.fanout pTwoW pProdBits) pNatToSigned
  have pNegX := StageEval.const (S := S) (bmSignedIsNeg_computesInTime W x hx)
  have pNegY := StageEval.const (S := S) (bmSignedIsNeg_computesInTime W y hy)
  have pSignXor := StageEval.seq (StageEval.pairMap pNegX pNegY)
    (StageEval.of_computesStageLe bmBoolXor_computesStageLe
      (fun _ : S => (decide (x < 0), decide (y < 0))))
  have hpos_fits : FitsSignedWord (2 * W) ((x.natAbs * y.natAbs : ℕ) : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact hprod_nat
  have pNegProd := StageEval.seq pPosProd
    (StageEval.const (S := S)
      (bmSignedNeg_computesInTime (2 * W) ((x.natAbs * y.natAbs : ℕ) : ℤ) hpos_fits))
  have hall := StageEval.congr_out (v2 := fun _ => encodeSignedWord (2 * W) (x * y))
    (StageEval.ite_stage pSignXor pNegProd pPosProd)
    (fun _ => by
      dsimp only [id]
      split_ifs with hcond
      · rw [← signed_mul_eq_ite_natAbs x y, if_pos hcond]
      · rw [← signed_mul_eq_ite_natAbs x y, if_neg hcond])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord,
    encodeNatBits_length, encBool, List.length_singleton] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-! ### Signed Restoring Division (`bmRoundDivInt`) -/

/-- Test whether an unsigned bit-word `encodeNatBits w r` (`r < 2^w`) on `kIO` represents `0`:
`encodeNatBits w r ↦ encBool (decide (r = 0))` in `≤ 800 * w + 2000` steps. -/
def bmBitsIsZero : BitMachine :=
  bmSeq
    (bmSeq
      (bmSeq (bmSeq (bmFanout bmLenUnary bmId) bmNatToSigned) bmSignedNeg)
      bmSignedIsNeg)
    bmBoolNot

theorem bmBitsIsZero_computesInTime (w r : ℕ) (hr : r < 2 ^ w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 800 * w + 2000,
      bmBitsIsZero.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeNatBits w r)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encBool (decide (r = 0)))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encodeNatBits w r
  have hr_fits : FitsSignedWord w (r : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact hr
  have pLen := StageEval.congr_out (v2 := fun _ => encUnary w)
    (StageEval.of_computesStageLe (bmLenUnary_computesStageLe encBits) (fun _ : S => encodeNatBits w r))
    (fun _ => by simp [encBits])
  have pSigned := StageEval.seq (StageEval.fanout pLen (StageEval.id_stage uIn))
    (StageEval.const (S := S) (bmNatToSigned_computesInTime w w r hr hr))
  have pNeg := StageEval.seq pSigned
    (StageEval.const (S := S) (bmSignedNeg_computesInTime w (r : ℤ) hr_fits))
  have pIsNeg := StageEval.seq pNeg
    (StageEval.const (S := S) (bmSignedIsNeg_computesInTime w (-(r : ℤ)) hr_fits.neg))
  have hall := StageEval.congr_out (v2 := fun _ => encBool (decide (r = 0)))
    (StageEval.seq pIsNeg
      (StageEval.of_computesStageLe bmBoolNot_computesStageLe (fun _ : S => decide (-(r : ℤ) < 0))))
    (fun _ => by
      dsimp only [encBool, id]
      congr 1
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · simp
      · simp [hr_pos, ne_of_gt hr_pos])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, encBits, id] at ht hcomp
  simp only [encodeNatBits_length, length_encUnary] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Signed Euclidean division by a positive natural number `b > 0` (`edivPosByRestoringTracked`):
consumes `encPair (encodeSignedWord w) encBits (a, encodeNatBits w b)` (`FitsSignedWord w a`, `b < 2^w`, `0 < b`)
and emits `encodeSignedWord w (a / (b : ℤ))` in $O(w^2)$ `TM2.step` transitions. -/
def bmEdivPosByRestoring : BitMachine :=
  let bmW := bmSeq bmFst bmSignedWidth
  let bmQR := bmSeq (bmFanout bmW (bmMapFst bmSignedMagBits)) bmRestoringDivMod
  let bmQSigned := bmSeq (bmFanout bmW (bmSeq bmQR bmFst)) bmNatToSigned
  let bmNegQ := bmSeq bmQSigned bmSignedNeg
  let bmOne := bmSeq bmW
    (bmSeq (bmFanout (bmConstBool true) (bmSeq bmUnaryPred bmSignedZero)) bmAppendBits)
  let bmNegQSub1 := bmSeq (bmFanout bmNegQ bmOne) bmSignedSub
  let bmRemZero := bmSeq (bmSeq bmQR bmSnd) bmBitsIsZero
  bmIte (bmSeq bmFst bmSignedIsNeg)
    (bmIte bmRemZero bmNegQ bmNegQSub1)
    bmQSigned

theorem bmEdivPosByRestoring_computesInTime (w : ℕ) (hw : 1 ≤ w) (a : ℤ) (b : ℕ)
    (ha : FitsSignedWord w a) (hb_lt : b < 2 ^ w) (hb_pos : 0 < b)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 150 * w * w + 15000 * w + 35000,
      bmEdivPosByRestoring.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord w) encBits (a, encodeNatBits w b)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord w (a / (b : ℤ))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encPair (encodeSignedWord w) encBits (a, encodeNatBits w b)
  have ha_nat : a.natAbs < 2 ^ w := (fitsSignedWord_iff_natAbs_lt w a).mp ha
  have hq_lt : a.natAbs / b < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_nat
  have hr_lt : a.natAbs % b < 2 ^ w := Nat.lt_trans (Nat.mod_lt _ hb_pos) hb_lt
  have hq_fits : FitsSignedWord w ((a.natAbs / b : ℕ) : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact hq_lt
  have h1_fits : FitsSignedWord w 1 := by
    unfold FitsSignedWord
    rw [abs_one]
    exact one_lt_pow₀ (by decide : (1 : ℤ) < 2) (by omega)
  have pW := StageEval.seq
    (StageEval.fst (fun _ : S => encodeSignedWord w a) (fun _ : S => encodeNatBits w b))
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe w) (fun _ => a))
  have pMagPair := StageEval.mapFst (u2 := fun _ : S => encodeNatBits w b)
    (StageEval.const (S := S) (bmSignedMagBits_computesInTime w a ha))
  have pDiv : StageEval (S := S) bmRestoringDivMod
      (encDepPair (fun _ => encUnary w)
        (encDepPair (fun _ => encodeNatBits w a.natAbs) (fun _ => encodeNatBits w b)))
      (encDepPair (fun _ => encodeNatBits w (a.natAbs / b))
        (fun _ => encodeNatBits w (a.natAbs % b)))
      (fun _ => 13 * w * w + 75 * w + 65) :=
    StageEval.const (S := S) (bmRestoringDivMod_computesInTime w a.natAbs b ha_nat hb_pos hb_lt)
  have pQR := StageEval.seq (StageEval.fanout pW pMagPair) pDiv
  have pQBits := StageEval.seq pQR
    (StageEval.fst (fun _ : S => encodeNatBits w (a.natAbs / b))
      (fun _ : S => encodeNatBits w (a.natAbs % b)))
  have pQSigned := StageEval.seq (StageEval.fanout pW pQBits)
    (StageEval.const (S := S) (bmNatToSigned_computesInTime w w (a.natAbs / b) hq_lt hq_lt))
  have pNegQ := StageEval.seq pQSigned
    (StageEval.const (S := S) (bmSignedNeg_computesInTime w ((a.natAbs / b : ℕ) : ℤ) hq_fits))
  have pOne : StageEval (S := S)
      (bmSeq (bmSeq bmFst bmSignedWidth)
        (bmSeq (bmFanout (bmConstBool true) (bmSeq bmUnaryPred bmSignedZero)) bmAppendBits))
      uIn (fun _ => encodeSignedWord w 1)
      (fun _ => 60 * w + 220) := by
    have c1 := StageEval.of_computesStageLe (bmConstBool_computesStageLe true encUnary)
      (fun _ : S => w)
    have c2 := StageEval.seq
      (StageEval.of_computesStageLe bmUnaryPred_computesStageLe (fun _ : S => w))
      (StageEval.const (S := S) (bmSignedZero_computesInTime (w - 1)))
    have c12 := StageEval.congr_out
      (v2 := fun _ => encodeSignedWord w 1)
      (StageEval.seq (StageEval.fanout c1 c2)
        (StageEval.appendBits (fun _ : S => [true]) (fun _ : S => encodeSignedWord (w - 1) 0)))
      (fun _ => encodeSignedWord_one w hw)
    exact (StageEval.seq pW c12).mono (fun _ => by
      simp only [encBool, length_encodeSignedWord, encodeNatBits_length,
        length_encUnary, List.length_singleton]
      omega)
  have pR := StageEval.seq pQR
    (StageEval.snd (fun _ : S => encodeNatBits w (a.natAbs / b))
      (fun _ : S => encodeNatBits w (a.natAbs % b)))
  have pRemZero := StageEval.seq pR
    (StageEval.const (S := S) (bmBitsIsZero_computesInTime w (a.natAbs % b) hr_lt))
  have pIsNeg := StageEval.seq
    (StageEval.fst (fun _ : S => encodeSignedWord w a) (fun _ : S => encodeNatBits w b))
    (StageEval.const (S := S) (bmSignedIsNeg_computesInTime w a ha))
  have hall : StageEval (S := S) bmEdivPosByRestoring uIn
      (fun _ => encodeSignedWord w (a / (b : ℤ)))
      (fun _ => 150 * w * w + 15000 * w + 35000) := by
    refine (StageEval.ite pIsNeg
      (bTrue := fun _ => 90 * w * w + 9000 * w + 22000)
      (bFalse := fun _ => 40 * w * w + 3000 * w + 8000)
      (fun _ hneg u2 u3 u4 u5 uS => ?_)
      (fun _ hnonneg u2 u3 u4 u5 uS => ?_)).mono (fun _ => by
        simp only [length_encDepPair, length_encodeSignedWord, encodeNatBits_length]
        split_ifs <;> nlinarith)
    · have ha_neg : a < 0 := of_decide_eq_true hneg
      have pInner : StageEval (S := S)
          (bmIte
            (bmSeq (bmSeq (bmSeq (bmFanout (bmSeq bmFst bmSignedWidth) (bmMapFst bmSignedMagBits))
              bmRestoringDivMod) bmSnd) bmBitsIsZero)
            (bmSeq (bmSeq (bmFanout (bmSeq bmFst bmSignedWidth)
              (bmSeq (bmSeq (bmFanout (bmSeq bmFst bmSignedWidth) (bmMapFst bmSignedMagBits))
                bmRestoringDivMod) bmFst)) bmNatToSigned) bmSignedNeg)
            (bmSeq (bmFanout
              (bmSeq (bmSeq (bmFanout (bmSeq bmFst bmSignedWidth)
                (bmSeq (bmSeq (bmFanout (bmSeq bmFst bmSignedWidth) (bmMapFst bmSignedMagBits))
                  bmRestoringDivMod) bmFst)) bmNatToSigned) bmSignedNeg)
              (bmSeq (bmSeq bmFst bmSignedWidth)
                (bmSeq (bmFanout (bmConstBool true) (bmSeq bmUnaryPred bmSignedZero)) bmAppendBits)))
              bmSignedSub))
          uIn (fun _ => encodeSignedWord w (a / (b : ℤ)))
          (fun _ => 90 * w * w + 9000 * w + 22000) := by
        refine (StageEval.ite pRemZero
          (bTrue := fun _ => 30 * w * w + 3500 * w + 8000)
          (bFalse := fun _ => 40 * w * w + 5000 * w + 12000)
          (fun _ hrem u2' u3' u4' u5' uS' => ?_)
          (fun _ hrem u2' u3' u4' u5' uS' => ?_)).mono (fun _ => by
            simp only [length_encDepPair, length_encUnary,
              length_encodeSignedWord, encodeNatBits_length]
            split_ifs <;> nlinarith)
        · have hrem0 : a.natAbs % b = 0 := of_decide_eq_true hrem
          have hediv_eq : a / (b : ℤ) = -((a.natAbs / b : ℕ) : ℤ) := by
            have h := edivPosByRestoringTracked_fst ha_nat hb_pos
            unfold edivPosByRestoringTracked at h
            rw [if_neg (not_le.mpr ha_neg)] at h
            dsimp only at h
            rw [Int.natAbs_neg a, binaryRestoringDivModRegTracked_fst b ha_nat, if_pos hrem0] at h
            exact h.symm
          rcases pNegQ () u2' u3' u4' u5' uS' with ⟨t, ht, hc⟩
          dsimp only [uIn, id] at ht hc
          simp only [length_encDepPair, length_encUnary,
            length_encodeSignedWord, encodeNatBits_length] at ht
          rw [← hediv_eq] at hc
          exact ⟨t, by nlinarith, hc⟩
        · have hrem0 : a.natAbs % b ≠ 0 := of_decide_eq_false hrem
          have hediv_eq : a / (b : ℤ) = -((a.natAbs / b : ℕ) : ℤ) - 1 := by
            have h := edivPosByRestoringTracked_fst ha_nat hb_pos
            unfold edivPosByRestoringTracked at h
            rw [if_neg (not_le.mpr ha_neg)] at h
            dsimp only at h
            rw [Int.natAbs_neg a, binaryRestoringDivModRegTracked_fst b ha_nat, if_neg hrem0] at h
            exact h.symm
          have hq1_lt : a.natAbs / b + 1 < 2 ^ w := by
            have hdiv_mod := Nat.div_add_mod a.natAbs b
            have hrem_pos : 0 < a.natAbs % b := Nat.pos_of_ne_zero hrem0
            have hmul : 1 * (a.natAbs / b) ≤ b * (a.natAbs / b) :=
              Nat.mul_le_mul_right (a.natAbs / b) hb_pos
            omega
          have hsub1_fits : FitsSignedWord w (-((a.natAbs / b : ℕ) : ℤ) - 1) := by
            rw [show -((a.natAbs / b : ℕ) : ℤ) - 1 = -(((a.natAbs / b + 1 : ℕ) : ℤ)) by
              push_cast; ring]
            apply FitsSignedWord.neg
            rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact hq1_lt
          have pSub := StageEval.seq (StageEval.fanout pNegQ pOne)
            (StageEval.const (S := S)
              (bmSignedSub_computesInTime w (-((a.natAbs / b : ℕ) : ℤ)) 1
                hq_fits.neg h1_fits hsub1_fits))
          rcases pSub () u2' u3' u4' u5' uS' with ⟨t, ht, hc⟩
          dsimp only [uIn, id] at ht hc
          simp only [length_encDepPair, length_encUnary,
            length_encodeSignedWord, encodeNatBits_length] at ht
          rw [← hediv_eq] at hc
          exact ⟨t, by nlinarith, hc⟩
      exact pInner () u2 u3 u4 u5 uS
    · have ha_nonneg : 0 ≤ a := not_lt.mp (of_decide_eq_false hnonneg)
      have hediv_eq : a / (b : ℤ) = ((a.natAbs / b : ℕ) : ℤ) := by
        have h := edivPosByRestoringTracked_fst ha_nat hb_pos
        unfold edivPosByRestoringTracked at h
        rw [if_pos ha_nonneg] at h
        dsimp only at h
        rw [binaryRestoringDivModRegTracked_fst b ha_nat] at h
        exact h.symm
      rcases pQSigned () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
      dsimp only [uIn, id] at ht hc
      simp only [length_encDepPair, length_encUnary,
        length_encodeSignedWord, encodeNatBits_length] at ht
      rw [← hediv_eq] at hc
      exact ⟨t, by nlinarith, hc⟩
  exact hall () tW2 tW3 tW4 tW5 tSch

/-- **Signed Rounded Integer Division (`bmRoundDivInt`)**:
Consumes `encPair (encodeSignedWord w) (encodeSignedWord w) (num, den)` (`FitsSignedWord w num`, `FitsSignedWord w den`)
and emits `encodeSignedWord w (roundDivInt num den)` in $O(w^2)$ `TM2.step` transitions. -/
def bmRoundDivInt : BitMachine :=
  let bmW := bmSeq bmFst bmSignedWidth
  let bmDenZero := bmSeq (bmSeq bmSnd bmSignedMagBits) bmBitsIsZero
  let bmTwoNum := bmSeq bmFst (tmConsBit false kIO)
  let bmAdjNum := bmIte (bmSeq bmSnd bmSignedIsNeg) (bmSeq bmTwoNum bmSignedNeg) bmTwoNum
  let bmExtDen := bmSeq (bmFanout (bmSeq bmW bmUnarySucc) (bmSeq bmSnd bmSignedMagBits)) bmTakePadBits
  let bmDivStep := bmSeq (bmFanout bmAdjNum bmExtDen) bmEdivPosByRestoring
  let bmRounded := bmSeq (bmSeq bmDivStep bmHalfRoundedSigned) bmShrinkSigned1
  bmIte bmDenZero (bmSeq bmW bmSignedZero) bmRounded

theorem bmRoundDivInt_computesInTime (w : ℕ) (num den : ℤ)
    (hnum : FitsSignedWord w num) (hden : FitsSignedWord w den)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 250 * w * w + 60000 * w + 150000,
      bmRoundDivInt.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord w) (encodeSignedWord w) (num, den)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord w (roundDivInt num den)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encPair (encodeSignedWord w) (encodeSignedWord w) (num, den)
  have hden_nat : den.natAbs < 2 ^ w := (fitsSignedWord_iff_natAbs_lt w den).mp hden
  have pW := StageEval.seq
    (StageEval.fst (fun _ : S => encodeSignedWord w num) (fun _ : S => encodeSignedWord w den))
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe w) (fun _ => num))
  have pDenMag := StageEval.seq
    (StageEval.snd (fun _ : S => encodeSignedWord w num) (fun _ : S => encodeSignedWord w den))
    (StageEval.const (S := S) (bmSignedMagBits_computesInTime w den hden))
  have pDenZero := StageEval.seq pDenMag
    (StageEval.const (S := S) (bmBitsIsZero_computesInTime w den.natAbs hden_nat))
  have pZeroBr := StageEval.seq pW (StageEval.const (S := S) (bmSignedZero_computesInTime w))
  have hall : StageEval (S := S) bmRoundDivInt uIn
      (fun _ => encodeSignedWord w (roundDivInt num den))
      (fun _ => 250 * w * w + 60000 * w + 150000) := by
    refine (StageEval.ite pDenZero
      (bTrue := fun _ => 200 * w + 1000)
      (bFalse := fun _ => 200 * w * w + 50000 * w + 120000)
      (fun _ hdz u2 u3 u4 u5 uS => ?_)
      (fun _ hdnz u2 u3 u4 u5 uS => ?_)).mono (fun _ => by
        simp only [length_encDepPair, length_encodeSignedWord]
        split_ifs <;> nlinarith)
    · have hden0 : den = 0 := Int.natAbs_eq_zero.mp (of_decide_eq_true hdz)
      subst hden0
      have hround0 : roundDivInt num 0 = 0 := by simp [roundDivInt]
      rcases pZeroBr () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
      dsimp only [uIn, id] at ht hc ⊢
      simp only [length_encodeSignedWord] at ht
      rw [← hround0] at hc
      exact ⟨t, by omega, hc⟩
    · have hb_pos : 0 < den.natAbs := Nat.pos_of_ne_zero (of_decide_eq_false hdnz)
      have hb_lt1 : den.natAbs < 2 ^ (w + 1) :=
        Nat.lt_trans hden_nat (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self w))
      have h2num_fits : FitsSignedWord (w + 1) (2 * num) := by
        simpa [mul_comm 2 num, Nat.add_comm 1 w] using hnum.mul_two_pow 1
      set adjNum : ℤ := if den < 0 then -(2 * num) else 2 * num
      have hadj_fits : FitsSignedWord (w + 1) adjNum := by
        dsimp [adjNum]; split_ifs <;> [exact h2num_fits.neg; exact h2num_fits]
      have hcons : StageEval (S := S) (tmConsBit false kIO)
          (fun _ => encodeSignedWord w num)
          (fun _ => encodeSignedWord (w + 1) (2 * num))
          (fun _ => 1) := by
        intro _ u2' u3' u4' u5' uS'
        have hc := tmConsBit_computesInTime false kIO
          (mkTapes8 (encodeDelimWord (encodeSignedWord w num)) [] [] u2' u3' u4' u5' uS')
          (encodeSignedWord w num) [] (by simp)
        simp only [update_mkTapes8_kIO, List.append_nil] at hc
        have heq : false :: encodeSignedWord w num = encodeSignedWord (w + 1) (2 * num) := by
          simpa [encUnary, mul_comm, Nat.add_comm 1 w] using encodeSignedWord_mul_two_pow 1 w num hnum
        rw [heq] at hc
        exact ⟨1, le_rfl, hc⟩
      have pTwoNum := StageEval.seq
        (StageEval.fst (fun _ : S => encodeSignedWord w num) (fun _ : S => encodeSignedWord w den))
        hcons
      have pDenNeg := StageEval.seq
        (StageEval.snd (fun _ : S => encodeSignedWord w num) (fun _ : S => encodeSignedWord w den))
        (StageEval.const (S := S) (bmSignedIsNeg_computesInTime w den hden))
      have pNeg2Num := StageEval.seq pTwoNum
        (StageEval.const (S := S) (bmSignedNeg_computesInTime (w + 1) (2 * num) h2num_fits))
      have pAdjNum := StageEval.congr_out
        (v2 := fun _ => encodeSignedWord (w + 1) adjNum)
        (StageEval.ite_stage pDenNeg pNeg2Num pTwoNum)
        (fun _ => by dsimp [adjNum]; split_ifs <;> simp_all)
      have pW1 := StageEval.seq pW
        (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => w))
      have pExtDen := StageEval.congr_out
        (v2 := fun _ => encodeNatBits (w + 1) den.natAbs)
        (StageEval.seq (StageEval.fanout pW1 pDenMag)
          (StageEval.takePadBits_stage (fun _ : S => w + 1)
            (fun _ : S => encodeNatBits w den.natAbs)))
        (fun _ => takePadBits_encodeNatBits hden_nat)
      have pDivStep := StageEval.seq (StageEval.fanout pAdjNum pExtDen)
        (StageEval.const (S := S)
          (bmEdivPosByRestoring_computesInTime (w + 1) (by omega) adjNum den.natAbs
            hadj_fits hb_lt1 hb_pos))
      have hden0 : den ≠ 0 := Int.natAbs_ne_zero.mp (of_decide_eq_false hdnz)
      have hround_eq : roundShiftInt (adjNum / (den.natAbs : ℤ)) 1 = roundDivInt num den := by
        have htr := roundDivIntTracked_fst den hnum
        unfold roundDivIntTracked at htr
        by_cases hpos : 0 < den
        · have hnot_neg : ¬ den < 0 := by omega
          rw [if_pos hpos] at htr
          dsimp only at htr
          dsimp only [adjNum]
          rw [if_neg hnot_neg]
          have ha_nat : (2 * num).natAbs < 2 ^ (w + 1) :=
            (fitsSignedWord_iff_natAbs_lt (w + 1) (2 * num)).mp h2num_fits
          rw [edivPosByRestoringTracked_fst ha_nat hb_pos] at htr
          exact htr
        · have hneg : den < 0 := by omega
          rw [if_neg hpos, if_pos hneg] at htr
          dsimp only at htr
          dsimp only [adjNum]
          rw [if_pos hneg]
          have ha_nat : (-(2 * num)).natAbs < 2 ^ (w + 1) :=
            (fitsSignedWord_iff_natAbs_lt (w + 1) (-(2 * num))).mp h2num_fits.neg
          have h2neg : -2 * num = -(2 * num) := by ring
          rw [h2neg, Int.natAbs_neg den, edivPosByRestoringTracked_fst ha_nat hb_pos] at htr
          exact htr
      have hdiv_fits : FitsSignedWord (w + 1) (adjNum / (den.natAbs : ℤ)) := by
        unfold FitsSignedWord
        exact lt_of_le_of_lt (Int.abs_ediv_le_abs adjNum (den.natAbs : ℤ)) hadj_fits
      have pHalf := StageEval.congr_out
        (v2 := fun _ => encodeSignedWord (w + 1) (roundDivInt num den))
        (StageEval.seq pDivStep
          (StageEval.const (S := S)
            (bmHalfRoundedSigned_computesInTime (w + 1)
              (adjNum / (den.natAbs : ℤ)) hdiv_fits)))
        (fun _ => by rw [hround_eq])
      have pRounded := StageEval.seq pHalf
        (StageEval.const (S := S)
          (bmShrinkSigned1_computesInTime w (roundDivInt num den)
            (hnum.roundDivInt den)))
      rcases pRounded () u2 u3 u4 u5 uS with ⟨t, ht, hc⟩
      dsimp only [uIn, id] at ht hc ⊢
      simp only [length_encDepPair, length_encUnary,
        length_encodeSignedWord, encodeNatBits_length] at ht
      split_ifs at ht <;> exact ⟨t, by nlinarith, hc⟩
  exact hall () tW2 tW3 tW4 tW5 tSch

/-! ### Fixed-Point Square Root (`bmApproxSqrtFixed`) -/

theorem drop_encodeNatBits_eq (W k m : ℕ) :
    (encodeNatBits W m).drop k = encodeNatBits (W - k) (m / 2 ^ k) := by
  by_cases hk : k ≤ W
  · have hW : W = k + (W - k) := (Nat.add_sub_of_le hk).symm
    conv_lhs => rw [hW]
    rw [encodeNatBits_add_mod_div k (W - k) m,
      List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp), List.nil_append]
  · have hsub : W - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hsub, List.drop_eq_nil_of_le (by simp; omega)]
    rfl

/-- **Fixed-Point Square Root (`bmApproxSqrtFixed`)**:
Consumes `encPair (encPair encUnary (encPair encUnary encUnary)) (encodeSignedWord WIn) ((WOut, (w, k)), num)`
(`FitsSignedWord WIn num`, `(max 0 num).toNat / 2 ^ k < 4 ^ w`, `approxSqrtFixed k num < 2 ^ WOut`)
and emits `encodeSignedWord WOut (approxSqrtFixed k num)` in $O(w^2 + W_{\text{in}} + W_{\text{out}} + k)$ steps. -/
def bmApproxSqrtFixed : BitMachine :=
  let bmWOut := bmSeq bmFst bmFst
  let bmW := bmSeq (bmSeq bmFst bmSnd) bmFst
  let bmK := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmNum := bmSnd
  let bmPosBits := bmSeq bmNum (bmIte bmSignedIsNeg bmSignedWidth bmSignedMagBits)
  let bmShifted := bmSeq (bmFanout bmK bmPosBits) bmDropBits
  let bmPadded := bmSeq (bmFanout (bmSeq bmW bmUnaryDouble) bmShifted) bmTakePadBits
  let bmSqrtBits := bmSeq (bmSeq (bmFanout bmW bmPadded) bmRestoringSqrt) bmFst
  bmSeq (bmFanout bmWOut bmSqrtBits) bmNatToSigned

theorem bmApproxSqrtFixed_computesInTime (WIn WOut w k : ℕ) (num : ℤ)
    (hnum : FitsSignedWord WIn num)
    (h_lt4w : (max 0 num).toNat / 2 ^ k < 4 ^ w)
    (h_out : (approxSqrtFixed k num).natAbs < 2 ^ WOut)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 30 * w * w + 3000 * w + 2500 * WIn + 1500 * WOut + 1000 * k + 15000,
      bmApproxSqrtFixed.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary)) (encodeSignedWord WIn)
            ((WOut, (w, k)), num)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord WOut (approxSqrtFixed k num)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uWK : S → List Bool := fun _ => encPair encUnary encUnary (w, k)
  let u1 : S → List Bool := encDepPair (fun _ => encUnary WOut) uWK
  let u2 : S → List Bool := fun _ => encodeSignedWord WIn num
  let uIn : S → List Bool := encDepPair u1 u2
  have pFst := StageEval.fst u1 u2
  have pNum := StageEval.snd u1 u2
  have pWOut := StageEval.seq pFst (StageEval.fst (fun _ : S => encUnary WOut) uWK)
  have pWK := StageEval.seq pFst (StageEval.snd (fun _ : S => encUnary WOut) uWK)
  have pW := StageEval.seq pWK (StageEval.fst (fun _ : S => encUnary w) (fun _ : S => encUnary k))
  have pK := StageEval.seq pWK (StageEval.snd (fun _ : S => encUnary w) (fun _ : S => encUnary k))
  have pPosBranch : StageEval (S := S)
      (bmIte bmSignedIsNeg bmSignedWidth bmSignedMagBits)
      u2 (fun _ => encodeNatBits WIn (max 0 num).toNat)
      (fun _ => 800 * WIn + 2200) := by
    have cCond := StageEval.const (S := S) (bmSignedIsNeg_computesInTime WIn num hnum)
    have cTrue := StageEval.of_computesStageLe (bmSignedWidth_computesStageLe WIn) (fun _ : S => num)
    have cFalse := StageEval.const (S := S) (bmSignedMagBits_computesInTime WIn num hnum)
    refine (StageEval.congr_out
      (v2 := fun _ => encodeNatBits WIn (max 0 num).toNat)
      (StageEval.ite_stage cCond cTrue cFalse) (fun _ => ?_)).mono
      (fun _ => by simp only [length_encodeSignedWord]; split_ifs <;> omega)
    rcases lt_or_ge num 0 with hneg | hnonneg
    · simp only [hneg, decide_true, ↓reduceIte, max_eq_left (le_of_lt hneg), Int.toNat_zero,
        encodeNatBits_zero]
      rfl
    · have hto : num.natAbs = num.toNat := by omega
      simp only [not_lt.mpr hnonneg, decide_false, Bool.false_eq_true, ↓reduceIte,
        max_eq_right hnonneg, hto]
  have pPosBits := StageEval.seq pNum pPosBranch
  have pShifted := StageEval.congr_out
    (v2 := fun _ => encodeNatBits (WIn - k) ((max 0 num).toNat / 2 ^ k))
    (StageEval.seq (StageEval.fanout pK pPosBits)
      (StageEval.dropBits (fun _ : S => k) (fun _ : S => encodeNatBits WIn (max 0 num).toNat)))
    (fun _ => drop_encodeNatBits_eq WIn k (max 0 num).toNat)
  have hm_lt : (max 0 num).toNat < 2 ^ WIn := by
    rcases lt_or_ge num 0 with hneg | hnonneg
    · rw [max_eq_left (le_of_lt hneg)]; exact Nat.two_pow_pos WIn
    · have hto : num.toNat = num.natAbs := by omega
      rw [max_eq_right hnonneg, hto]
      exact (fitsSignedWord_iff_natAbs_lt WIn num).mp hnum
  have hdiv_lt1 : (max 0 num).toNat / 2 ^ k < 2 ^ (WIn - k) := by
    by_cases hk : k ≤ WIn
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add, Nat.sub_add_cancel hk]
      exact hm_lt
    · have hle : 2 ^ WIn ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hm_lt hle)]
      exact Nat.two_pow_pos _
  have pTwoW := StageEval.seq pW
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : S => w))
  have pPadded := StageEval.congr_out
    (v2 := fun _ => encodeNatBits (2 * w) ((max 0 num).toNat / 2 ^ k))
    (StageEval.seq (StageEval.fanout pTwoW pShifted)
      (StageEval.takePadBits_stage (fun _ : S => 2 * w)
        (fun _ : S => encodeNatBits (WIn - k) ((max 0 num).toNat / 2 ^ k))))
    (fun _ => takePadBits_encodeNatBits hdiv_lt1)
  have pSqrtPair := StageEval.seq (StageEval.fanout pW pPadded)
    (StageEval.const (S := S)
      (bmRestoringSqrt_computesInTime w ((max 0 num).toNat / 2 ^ k) h_lt4w))
  set sF := (binaryRestoringSqrtRegTracked w ((max 0 num).toNat / 2 ^ k)).1.1
  set rF := (binaryRestoringSqrtRegTracked w ((max 0 num).toNat / 2 ^ k)).1.2
  have hsF_eq : sF = (approxSqrtFixed k num).natAbs := by
    unfold sF approxSqrtFixed
    rw [binaryRestoringSqrtRegTracked_fst_fst h_lt4w, Int.natAbs_natCast]
  have hsF_lt_w1 : sF < 2 ^ (w + 1) :=
    lt_of_lt_of_le (binaryRestoringSqrtRegAux_lt w h_lt4w).1
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ w))
  have hsF_lt_out : sF < 2 ^ WOut := by rwa [hsF_eq]
  have pSqrtBits := StageEval.seq pSqrtPair
    (StageEval.fst (fun _ : S => encodeNatBits (w + 1) sF)
      (fun _ : S => encodeNatBits (w + 1) rF))
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord WOut (approxSqrtFixed k num))
    (StageEval.seq (StageEval.fanout pWOut pSqrtBits)
      (StageEval.const (S := S)
        (bmNatToSigned_computesInTime WOut (w + 1) sF hsF_lt_w1 hsF_lt_out)))
    (fun _ => by
      congr 1
      unfold sF approxSqrtFixed
      rw [binaryRestoringSqrtRegTracked_fst_fst h_lt4w])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2, uWK, id] at ht hcomp
  have hsub : WIn - k ≤ WIn := Nat.sub_le WIn k
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encodeSignedWord,
    encodeNatBits_length] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-! ## 4. Fixed-Point Complex Arithmetic Stages (`encComplex W`) -/

/-- Encode `z : FixedComplex q` at signed word width `W`:
`encComplex W z = encPair (encodeSignedWord W) (encodeSignedWord W) (z.re, z.im)`. -/
def encComplex (W : ℕ) {q : ℕ} (z : FixedComplex q) : List Bool :=
  encPair (encodeSignedWord W) (encodeSignedWord W) (z.re, z.im)

@[simp]
theorem length_encComplex (W : ℕ) {q : ℕ} (z : FixedComplex q) :
    (encComplex W z).length = 4 * W + 8 := by
  simp only [encComplex, length_encPair, length_encodeSignedWord]
  omega

/-- Extract `encUnary W` from `encComplex W z` in `≤ 10 * W + 30` steps. -/
def bmComplexWidth : BitMachine :=
  bmSeq bmFst bmSignedWidth

theorem bmComplexWidth_computesStageLe (W q : ℕ) :
    ComputesStageLe bmComplexWidth (encComplex W (q := q)) encUnary (fun _ => W)
      (fun _ => 10 * W + 30) := by
  intro z tW2 tW3 tW4 tW5 tSch
  rcases (bmSeq_computesStageLe
    (bmFst_computesStageLe (encodeSignedWord W) (encodeSignedWord W))
    (bmSignedWidth_computesStageLe W)) (z.re, z.im) tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht ⊢
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Emit `encComplex W (0 : FixedComplex q)` from `encUnary W` on `kIO`. -/
def bmComplexZero : BitMachine :=
  bmSeq bmSignedZero bmDup

theorem bmComplexZero_computesInTime (W q : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 30 * W + 80,
      bmComplexZero.ComputesInTime
        (mkTapes8 (encodeDelimWord (encUnary W)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W (0 : FixedComplex q)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  rcases bmSignedZero_computesInTime W tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmDup_computesStageLe (encodeSignedWord W) 0 tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  simp only [length_encodeSignedWord] at ht2
  exact ⟨t1 + t2, by omega, s1.seq s2⟩

/-- Resize `encComplex W1 z` to `encComplex W2 z` given `encPair encUnary (encComplex W1) (W2, z)`. -/
def bmResizeComplex : BitMachine :=
  bmFanout
    (bmSeq (bmMapSnd bmFst) bmResizeSignedWord)
    (bmSeq (bmMapSnd bmSnd) bmResizeSignedWord)

theorem bmResizeComplex_computesInTime {q : ℕ} (W1 W2 : ℕ) (z : FixedComplex q)
    (hz1 : WordWidthBounds W1 z) (hz2 : WordWidthBounds W2 z)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2500 * W1 + 2500 * W2 + 12000,
      bmResizeComplex.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encComplex W1) (W2, z)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W2 z))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have pRe := StageEval.seq
    (StageEval.mapSnd (u1 := fun _ : S => encUnary W2)
      (StageEval.fst (fun _ : S => encodeSignedWord W1 z.re)
        (fun _ : S => encodeSignedWord W1 z.im)))
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W1 W2 z.re hz1.1 hz2.1))
  have pIm := StageEval.seq
    (StageEval.mapSnd (u1 := fun _ : S => encUnary W2)
      (StageEval.snd (fun _ : S => encodeSignedWord W1 z.re)
        (fun _ : S => encodeSignedWord W1 z.im)))
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W1 W2 z.im hz1.2 hz2.2))
  rcases (StageEval.fanout pRe pIm) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Complex negation: `encComplex W z ↦ encComplex W z.neg`. -/
def bmComplexNeg : BitMachine :=
  bmPairMap bmSignedNeg bmSignedNeg

theorem bmComplexNeg_computesInTime {q : ℕ} (W : ℕ) (z : FixedComplex q)
    (hz : WordWidthBounds W z) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 1300 * W + 3200,
      bmComplexNeg.ComputesInTime
        (mkTapes8 (encodeDelimWord (encComplex W z)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W z.neg)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.const (S := S) (bmSignedNeg_computesInTime W z.re hz.1)
  have p2 := StageEval.const (S := S) (bmSignedNeg_computesInTime W z.im hz.2)
  rcases StageEval.pairMap p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Complex conjugation: `encComplex W z ↦ encComplex W z.conj`. -/
def bmComplexConj : BitMachine :=
  bmPairMap bmId bmSignedNeg

theorem bmComplexConj_computesInTime {q : ℕ} (W : ℕ) (z : FixedComplex q)
    (hz : WordWidthBounds W z) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 660 * W + 1600,
      bmComplexConj.ComputesInTime
        (mkTapes8 (encodeDelimWord (encComplex W z)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W z.conj)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.id_stage (fun _ : S => encodeSignedWord W z.re)
  have p2 := StageEval.const (S := S) (bmSignedNeg_computesInTime W z.im hz.2)
  rcases StageEval.pairMap p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Complex division by 2 with round-half-up: `encComplex W z ↦ encComplex W z.halfRounded`. -/
def bmComplexHalfRounded : BitMachine :=
  bmPairMap bmHalfRoundedSigned bmHalfRoundedSigned

theorem bmComplexHalfRounded_computesInTime {q : ℕ} (W : ℕ) (z : FixedComplex q)
    (hz : WordWidthBounds W z) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 11000 * W + 50000,
      bmComplexHalfRounded.ComputesInTime
        (mkTapes8 (encodeDelimWord (encComplex W z)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W z.halfRounded)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.const (S := S) (bmHalfRoundedSigned_computesInTime W z.re hz.1)
  have p2 := StageEval.const (S := S) (bmHalfRoundedSigned_computesInTime W z.im hz.2)
  rcases StageEval.pairMap p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Transpose a pair of pairs `((a, b), (c, d))` into `((a, c), (b, d))`. -/
def bmPairTranspose : BitMachine :=
  bmFanout
    (bmPairMap bmFst bmFst)
    (bmPairMap bmSnd bmSnd)

theorem bmPairTranspose_computesInTime {S : Type} (u1 u2 u3 u4 : S → List Bool) :
    StageEval bmPairTranspose
      (encDepPair (encDepPair u1 u2) (encDepPair u3 u4))
      (encDepPair (encDepPair u1 u3) (encDepPair u2 u4))
      (fun s => 80 * ((u1 s).length + (u2 s).length + (u3 s).length + (u4 s).length) + 500) := by
  have p1 := StageEval.pairMap (StageEval.fst u1 u2) (StageEval.fst u3 u4)
  have p2 := StageEval.pairMap (StageEval.snd u1 u2) (StageEval.snd u3 u4)
  refine (StageEval.fanout p1 p2).mono (fun s => ?_)
  simp only [length_encDepPair]
  omega

/-- Extended complex addition: `(encComplex W z, encComplex W w) ↦ encComplex (W + 1) (z.add w)`. -/
def bmComplexAddExt : BitMachine :=
  bmSeq bmPairTranspose (bmPairMap bmSignedAddExt bmSignedAddExt)

theorem bmComplexAddExt_computesInTime {q : ℕ} (W : ℕ) (z w : FixedComplex q)
    (hz : WordWidthBounds W z) (hw : WordWidthBounds W w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 800 * W + 2000,
      bmComplexAddExt.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encComplex W) (encComplex W) (z, w)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex (W + 1) (z.add w)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := bmPairTranspose_computesInTime
    (fun _ : S => encodeSignedWord W z.re)
    (fun _ : S => encodeSignedWord W z.im)
    (fun _ : S => encodeSignedWord W w.re)
    (fun _ : S => encodeSignedWord W w.im)
  have p2 := StageEval.pairMap
    (StageEval.const (S := S) (bmSignedAddExt_computesInTime W z.re w.re hz.1 hw.1))
    (StageEval.const (S := S) (bmSignedAddExt_computesInTime W z.im w.im hz.2 hw.2))
  rcases StageEval.seq p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair] at ht
  simp only [length_encPair, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Extended complex subtraction: `(encComplex W z, encComplex W w) ↦ encComplex (W + 1) (z.sub w)`. -/
def bmComplexSubExt : BitMachine :=
  bmSeq bmPairTranspose (bmPairMap bmSignedSubExt bmSignedSubExt)

theorem bmComplexSubExt_computesInTime {q : ℕ} (W : ℕ) (z w : FixedComplex q)
    (hz : WordWidthBounds W z) (hw : WordWidthBounds W w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 800 * W + 2000,
      bmComplexSubExt.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encComplex W) (encComplex W) (z, w)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex (W + 1) (z.sub w)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := bmPairTranspose_computesInTime
    (fun _ : S => encodeSignedWord W z.re)
    (fun _ : S => encodeSignedWord W z.im)
    (fun _ : S => encodeSignedWord W w.re)
    (fun _ : S => encodeSignedWord W w.im)
  have p2 := StageEval.pairMap
    (StageEval.const (S := S) (bmSignedSubExt_computesInTime W z.re w.re hz.1 hw.1))
    (StageEval.const (S := S) (bmSignedSubExt_computesInTime W z.im w.im hz.2 hw.2))
  rcases StageEval.seq p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair] at ht
  simp only [length_encPair, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Fixed-width complex addition: `(encComplex W z, encComplex W w) ↦ encComplex W (z.add w)`
when `WordWidthBounds W z`, `WordWidthBounds W w`, and `WordWidthBounds W (z.add w)`. -/
def bmComplexAdd : BitMachine :=
  bmSeq bmPairTranspose (bmPairMap bmSignedAdd bmSignedAdd)

theorem bmComplexAdd_computesInTime {q : ℕ} (W : ℕ) (z w : FixedComplex q)
    (hz : WordWidthBounds W z) (hw : WordWidthBounds W w) (hzw : WordWidthBounds W (z.add w))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 1800 * W + 4500,
      bmComplexAdd.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encComplex W) (encComplex W) (z, w)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W (z.add w)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := bmPairTranspose_computesInTime
    (fun _ : S => encodeSignedWord W z.re)
    (fun _ : S => encodeSignedWord W z.im)
    (fun _ : S => encodeSignedWord W w.re)
    (fun _ : S => encodeSignedWord W w.im)
  have p2 := StageEval.pairMap
    (StageEval.const (S := S) (bmSignedAdd_computesInTime W z.re w.re hz.1 hw.1 hzw.1))
    (StageEval.const (S := S) (bmSignedAdd_computesInTime W z.im w.im hz.2 hw.2 hzw.2))
  rcases StageEval.seq p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair] at ht
  simp only [length_encPair, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Fixed-width complex subtraction: `(encComplex W z, encComplex W w) ↦ encComplex W (z.sub w)`
when `WordWidthBounds W z`, `WordWidthBounds W w`, and `WordWidthBounds W (z.sub w)`. -/
def bmComplexSub : BitMachine :=
  bmSeq bmPairTranspose (bmPairMap bmSignedSub bmSignedSub)

theorem bmComplexSub_computesInTime {q : ℕ} (W : ℕ) (z w : FixedComplex q)
    (hz : WordWidthBounds W z) (hw : WordWidthBounds W w) (hzw : WordWidthBounds W (z.sub w))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 1800 * W + 4500,
      bmComplexSub.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encComplex W) (encComplex W) (z, w)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W (z.sub w)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := bmPairTranspose_computesInTime
    (fun _ : S => encodeSignedWord W z.re)
    (fun _ : S => encodeSignedWord W z.im)
    (fun _ : S => encodeSignedWord W w.re)
    (fun _ : S => encodeSignedWord W w.im)
  have p2 := StageEval.pairMap
    (StageEval.const (S := S) (bmSignedSub_computesInTime W z.re w.re hz.1 hw.1 hzw.1))
    (StageEval.const (S := S) (bmSignedSub_computesInTime W z.im w.im hz.2 hw.2 hzw.2))
  rcases StageEval.seq p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [encDepPair] at ht
  simp only [length_encPair, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Averaging complex addition `(z.add w).halfRounded` preserving word width `W` without overflow:
`(encComplex W z, encComplex W w) ↦ encComplex W (z.add w).halfRounded`. -/
def bmComplexAvgAdd : BitMachine :=
  bmSeq bmComplexAddExt
    (bmSeq bmComplexHalfRounded (bmPairMap bmShrinkSigned1 bmShrinkSigned1))

theorem bmComplexAvgAdd_computesInTime {q : ℕ} (W : ℕ) (z w : FixedComplex q)
    (hz : WordWidthBounds W z) (hw : WordWidthBounds W w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 15000 * W + 78000,
      bmComplexAvgAdd.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encComplex W) (encComplex W) (z, w)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W (z.add w).halfRounded))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.const (S := S) (bmComplexAddExt_computesInTime W z w hz hw)
  have p2 := StageEval.const (S := S) (bmComplexHalfRounded_computesInTime (W + 1) (z.add w) (hz.add hw))
  have p3 := StageEval.pairMap
    (StageEval.const (S := S) (bmShrinkSigned1_computesInTime W (roundShiftInt (z.re + w.re) 1)
      (hz.1.halfRounded_add hw.1)))
    (StageEval.const (S := S) (bmShrinkSigned1_computesInTime W (roundShiftInt (z.im + w.im) 1)
      (hz.2.halfRounded_add hw.2)))
  rcases StageEval.seq p1 (StageEval.seq p2 p3) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Averaging complex subtraction `(z.sub w).halfRounded` preserving word width `W` without overflow:
`(encComplex W z, encComplex W w) ↦ encComplex W (z.sub w).halfRounded`. -/
def bmComplexAvgSub : BitMachine :=
  bmSeq bmComplexSubExt
    (bmSeq bmComplexHalfRounded (bmPairMap bmShrinkSigned1 bmShrinkSigned1))

theorem bmComplexAvgSub_computesInTime {q : ℕ} (W : ℕ) (z w : FixedComplex q)
    (hz : WordWidthBounds W z) (hw : WordWidthBounds W w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 15000 * W + 78000,
      bmComplexAvgSub.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encComplex W) (encComplex W) (z, w)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W (z.sub w).halfRounded))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1' := StageEval.const (S := S) (bmComplexSubExt_computesInTime W z w hz hw)
  have p2 := StageEval.const (S := S) (bmComplexHalfRounded_computesInTime (W + 1) (z.sub w) (hz.sub hw))
  have p3 := StageEval.pairMap
    (StageEval.const (S := S) (bmShrinkSigned1_computesInTime W (roundShiftInt (z.re - w.re) 1)
      (hz.1.halfRounded_sub hw.1)))
    (StageEval.const (S := S) (bmShrinkSigned1_computesInTime W (roundShiftInt (z.im - w.im) 1)
      (hz.2.halfRounded_sub hw.2)))
  rcases StageEval.seq p1' (StageEval.seq p2 p3) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- **Parameterized Fixed-Point Complex Multiplication (`bmComplexMulWith bmMul`)**:
Consumes `encPair (encPair encUnary encUnary) (encPair (encComplex W) (encComplex W)) ((WOut, q), (z, w))`
on `kIO` (`WordWidthBounds W z`, `WordWidthBounds W w`, `WordWidthBounds WOut (FixedComplex.mulRounded z w)`)
and emits `encComplex WOut (FixedComplex.mulRounded z w)` in $O(M(W) + W + W_{\text{out}} + q)$ steps. -/
def bmComplexMulWith (bmMul : BitMachine) : BitMachine :=
  let bmWOut := bmSeq bmFst bmFst
  let bmQ := bmSeq bmFst bmSnd
  let bmZ := bmSeq bmSnd bmFst
  let bmW := bmSeq bmSnd bmSnd
  let bmZRe := bmSeq bmZ bmFst
  let bmZIm := bmSeq bmZ bmSnd
  let bmWRe := bmSeq bmW bmFst
  let bmWIm := bmSeq bmW bmSnd
  let bmP1 := bmSeq (bmFanout bmZRe bmWRe) (bmSignedMulWith bmMul)
  let bmP2 := bmSeq (bmFanout bmZIm bmWIm) (bmSignedMulWith bmMul)
  let bmP3 := bmSeq (bmFanout bmZRe bmWIm) (bmSignedMulWith bmMul)
  let bmP4 := bmSeq (bmFanout bmZIm bmWRe) (bmSignedMulWith bmMul)
  let bmDiff := bmSeq (bmFanout bmP1 bmP2) bmSignedSubExt
  let bmSum := bmSeq (bmFanout bmP3 bmP4) bmSignedAddExt
  let bmR1 := bmSeq (bmFanout bmQ bmDiff) bmRoundShiftSigned
  let bmR2 := bmSeq (bmFanout bmQ bmSum) bmRoundShiftSigned
  bmFanout
    (bmSeq (bmFanout bmWOut bmR1) bmResizeSignedWord)
    (bmSeq (bmFanout bmWOut bmR2) bmResizeSignedWord)

theorem bmComplexMulWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W WOut q : ℕ) (z w : FixedComplex q)
    (hz : WordWidthBounds W z) (hw : WordWidthBounds W w)
    (hout : WordWidthBounds WOut (FixedComplex.mulRounded z w))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 8 * mulTime W + 60000 * W + 12000 * q + 3000 * WOut + 120000,
      (bmComplexMulWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encComplex W) (encComplex W)) ((WOut, q), (z, w))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex WOut (FixedComplex.mulRounded z w)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encPair encUnary encUnary (WOut, q)
  let u2 : S → List Bool := fun _ => encPair (encComplex W) (encComplex W) (z, w)
  let uIn : S → List Bool := encDepPair u1 u2
  have pFst := StageEval.fst u1 u2
  have pSnd := StageEval.snd u1 u2
  have pWOut := StageEval.seq pFst
    (StageEval.fst (fun _ : S => encUnary WOut) (fun _ : S => encUnary q))
  have pQ := StageEval.seq pFst
    (StageEval.snd (fun _ : S => encUnary WOut) (fun _ : S => encUnary q))
  have pZ := StageEval.seq pSnd
    (StageEval.fst (fun _ : S => encComplex W z) (fun _ : S => encComplex W w))
  have pW := StageEval.seq pSnd
    (StageEval.snd (fun _ : S => encComplex W z) (fun _ : S => encComplex W w))
  have pZRe := StageEval.seq pZ
    (StageEval.fst (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pZIm := StageEval.seq pZ
    (StageEval.snd (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pWRe := StageEval.seq pW
    (StageEval.fst (fun _ : S => encodeSignedWord W w.re) (fun _ : S => encodeSignedWord W w.im))
  have pWIm := StageEval.seq pW
    (StageEval.snd (fun _ : S => encodeSignedWord W w.re) (fun _ : S => encodeSignedWord W w.im))
  have pP1 := StageEval.seq (StageEval.fanout pZRe pWRe)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W z.re w.re hz.1 hw.1))
  have pP2 := StageEval.seq (StageEval.fanout pZIm pWIm)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W z.im w.im hz.2 hw.2))
  have pP3 := StageEval.seq (StageEval.fanout pZRe pWIm)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W z.re w.im hz.1 hw.2))
  have pP4 := StageEval.seq (StageEval.fanout pZIm pWRe)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W z.im w.re hz.2 hw.1))
  have hp1_fits : FitsSignedWord (2 * W) (z.re * w.re) := by
    simpa [Nat.two_mul] using hz.1.mul hw.1
  have hp2_fits : FitsSignedWord (2 * W) (z.im * w.im) := by
    simpa [Nat.two_mul] using hz.2.mul hw.2
  have hp3_fits : FitsSignedWord (2 * W) (z.re * w.im) := by
    simpa [Nat.two_mul] using hz.1.mul hw.2
  have hp4_fits : FitsSignedWord (2 * W) (z.im * w.re) := by
    simpa [Nat.two_mul] using hz.2.mul hw.1
  have pDiff := StageEval.seq (StageEval.fanout pP1 pP2)
    (StageEval.const (S := S) (bmSignedSubExt_computesInTime (2 * W) (z.re * w.re) (z.im * w.im)
      hp1_fits hp2_fits))
  have pSum := StageEval.seq (StageEval.fanout pP3 pP4)
    (StageEval.const (S := S) (bmSignedAddExt_computesInTime (2 * W) (z.re * w.im) (z.im * w.re)
      hp3_fits hp4_fits))
  have hdiff_fits : FitsSignedWord (2 * W + 1) (z.re * w.re - z.im * w.im) :=
    hp1_fits.sub hp2_fits
  have hsum_fits : FitsSignedWord (2 * W + 1) (z.re * w.im + z.im * w.re) :=
    hp3_fits.add hp4_fits
  have pR1 := StageEval.seq (StageEval.fanout pQ pDiff)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime (2 * W + 1) q
      (z.re * w.re - z.im * w.im) hdiff_fits))
  have pR2 := StageEval.seq (StageEval.fanout pQ pSum)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime (2 * W + 1) q
      (z.re * w.im + z.im * w.re) hsum_fits))
  have pOut1 := StageEval.seq (StageEval.fanout pWOut pR1)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime (2 * W + 1) WOut
      (roundShiftInt (z.re * w.re - z.im * w.im) q) (hdiff_fits.roundShiftInt q) hout.1))
  have pOut2 := StageEval.seq (StageEval.fanout pWOut pR2)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime (2 * W + 1) WOut
      (roundShiftInt (z.re * w.im + z.im * w.re) q) (hsum_fits.roundShiftInt q) hout.2))
  rcases (StageEval.fanout pOut1 pOut2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- **Parameterized Fixed-Point Real-Mantissa Scaling (`bmComplexScaleRoundedWith bmMul`)**:
Consumes `encPair (encPair encUnary encUnary) (encPair (encodeSignedWord W) (encComplex W)) ((WOut, q), (m, z))`
on `kIO` (`FitsSignedWord W m`, `WordWidthBounds W z`, `WordWidthBounds WOut (FixedComplex.scaleRoundedWith (· * ·) m z)`)
and emits `encComplex WOut (FixedComplex.scaleRoundedWith (· * ·) m z)` in $O(M(W) + W + W_{\text{out}} + q)$ steps. -/
def bmComplexScaleRoundedWith (bmMul : BitMachine) : BitMachine :=
  let bmWOut := bmSeq bmFst bmFst
  let bmQ := bmSeq bmFst bmSnd
  let bmM := bmSeq bmSnd bmFst
  let bmZ := bmSeq bmSnd bmSnd
  let bmZRe := bmSeq bmZ bmFst
  let bmZIm := bmSeq bmZ bmSnd
  let bmP1 := bmSeq (bmFanout bmM bmZRe) (bmSignedMulWith bmMul)
  let bmP2 := bmSeq (bmFanout bmM bmZIm) (bmSignedMulWith bmMul)
  let bmR1 := bmSeq (bmFanout bmQ bmP1) bmRoundShiftSigned
  let bmR2 := bmSeq (bmFanout bmQ bmP2) bmRoundShiftSigned
  bmFanout
    (bmSeq (bmFanout bmWOut bmR1) bmResizeSignedWord)
    (bmSeq (bmFanout bmWOut bmR2) bmResizeSignedWord)

theorem bmComplexScaleRoundedWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W WOut q : ℕ) (m : ℤ) (z : FixedComplex q)
    (hm : FitsSignedWord W m) (hz : WordWidthBounds W z)
    (hout : WordWidthBounds WOut (FixedComplex.scaleRoundedWith (· * ·) m z))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 4 * mulTime W + 45000 * W + 12000 * q + 3000 * WOut + 80000,
      (bmComplexScaleRoundedWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encodeSignedWord W) (encComplex W)) ((WOut, q), (m, z))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encComplex WOut (FixedComplex.scaleRoundedWith (· * ·) m z)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encPair encUnary encUnary (WOut, q)
  let u2 : S → List Bool := fun _ => encPair (encodeSignedWord W) (encComplex W) (m, z)
  let uIn : S → List Bool := encDepPair u1 u2
  have pFst := StageEval.fst u1 u2
  have pSnd := StageEval.snd u1 u2
  have pWOut := StageEval.seq pFst
    (StageEval.fst (fun _ : S => encUnary WOut) (fun _ : S => encUnary q))
  have pQ := StageEval.seq pFst
    (StageEval.snd (fun _ : S => encUnary WOut) (fun _ : S => encUnary q))
  have pM := StageEval.seq pSnd
    (StageEval.fst (fun _ : S => encodeSignedWord W m) (fun _ : S => encComplex W z))
  have pZ := StageEval.seq pSnd
    (StageEval.snd (fun _ : S => encodeSignedWord W m) (fun _ : S => encComplex W z))
  have pZRe := StageEval.seq pZ
    (StageEval.fst (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pZIm := StageEval.seq pZ
    (StageEval.snd (fun _ : S => encodeSignedWord W z.re) (fun _ : S => encodeSignedWord W z.im))
  have pP1 := StageEval.seq (StageEval.fanout pM pZRe)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W m z.re hm hz.1))
  have pP2 := StageEval.seq (StageEval.fanout pM pZIm)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W m z.im hm hz.2))
  have hp1_fits : FitsSignedWord (2 * W) (m * z.re) := by
    simpa [Nat.two_mul] using hm.mul hz.1
  have hp2_fits : FitsSignedWord (2 * W) (m * z.im) := by
    simpa [Nat.two_mul] using hm.mul hz.2
  have pR1 := StageEval.seq (StageEval.fanout pQ pP1)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime (2 * W) q (m * z.re) hp1_fits))
  have pR2 := StageEval.seq (StageEval.fanout pQ pP2)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime (2 * W) q (m * z.im) hp2_fits))
  have pOut1 := StageEval.seq (StageEval.fanout pWOut pR1)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime (2 * W) WOut
      (roundShiftInt (m * z.re) q) (hp1_fits.roundShiftInt q) hout.1))
  have pOut2 := StageEval.seq (StageEval.fanout pWOut pR2)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime (2 * W) WOut
      (roundShiftInt (m * z.im) q) (hp2_fits.roundShiftInt q) hout.2))
  rcases (StageEval.fanout pOut1 pOut2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- **Fixed-Point Complex Precision Rescaling (`bmComplexRescale`)**:
Consumes `encPair (encPair encUnary (encPair encUnary encUnary)) (encComplex W1) ((W2, (q1, q2)), z)`
(`WordWidthBounds W1 z`, `WordWidthBounds W2 (FixedComplex.rescale q2 z)`) and emits
`encComplex W2 (FixedComplex.rescale q2 z)`. -/
def bmComplexRescale : BitMachine :=
  let bmW2 := bmSeq bmFst bmFst
  let bmQPair := bmSeq bmFst bmSnd
  let bmShiftL := bmSeq (bmSeq bmQPair bmSwap) bmUnarySub
  let bmShiftR := bmSeq bmQPair bmUnarySub
  let bmZRe := bmSeq bmSnd bmFst
  let bmZIm := bmSeq bmSnd bmSnd
  let bmRe1 := bmSeq (bmFanout bmShiftL bmZRe) bmShiftLeftSigned
  let bmIm1 := bmSeq (bmFanout bmShiftL bmZIm) bmShiftLeftSigned
  let bmRe2 := bmSeq (bmFanout bmShiftR bmRe1) bmRoundShiftSigned
  let bmIm2 := bmSeq (bmFanout bmShiftR bmIm1) bmRoundShiftSigned
  bmFanout
    (bmSeq (bmFanout bmW2 bmRe2) bmResizeSignedWord)
    (bmSeq (bmFanout bmW2 bmIm2) bmResizeSignedWord)

theorem bmComplexRescale_computesInTime (W1 W2 q1 q2 : ℕ) (z : FixedComplex q1)
    (hz1 : WordWidthBounds W1 z) (hz2 : WordWidthBounds W2 (FixedComplex.rescale q2 z))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 16000 * W1 + 3000 * W2 + 30000 * q1 + 30000 * q2 + 65000,
      bmComplexRescale.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary)) (encComplex W1)
            ((W2, (q1, q2)), z)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W2 (FixedComplex.rescale q2 z)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uQ : S → List Bool := fun _ => encPair encUnary encUnary (q1, q2)
  let u1 : S → List Bool := encDepPair (fun _ => encUnary W2) uQ
  let u2 : S → List Bool := fun _ => encComplex W1 z
  let uIn : S → List Bool := encDepPair u1 u2
  have pFst := StageEval.fst u1 u2
  have pSnd := StageEval.snd u1 u2
  have pW2 := StageEval.seq pFst (StageEval.fst (fun _ : S => encUnary W2) uQ)
  have pQPair := StageEval.seq pFst (StageEval.snd (fun _ : S => encUnary W2) uQ)
  have pShiftL : StageEval (S := S) (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSwap) bmUnarySub)
      uIn (fun _ => encUnary (q2 - q1))
      (fun _ => 20 * W2 + 40 * q1 + 40 * q2 + 40 * W1 + 200) := by
    have pSw := StageEval.seq pQPair
      (StageEval.swap (fun _ : S => encUnary q1) (fun _ : S => encUnary q2))
    exact (StageEval.seq pSw
      (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (q2, q1)))).mono
      (fun _ => by
        dsimp only [uIn, u1, u2, uQ]
        simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex]
        omega)
  have pShiftR : StageEval (S := S) (bmSeq (bmSeq bmFst bmSnd) bmUnarySub)
      uIn (fun _ => encUnary (q1 - q2))
      (fun _ => 20 * W2 + 40 * q1 + 40 * q2 + 40 * W1 + 200) := by
    exact (StageEval.seq pQPair
      (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (q1, q2)))).mono
      (fun _ => by
        dsimp only [uIn, u1, u2, uQ]
        simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex]
        omega)
  have pZRe := StageEval.seq pSnd
    (StageEval.fst (fun _ : S => encodeSignedWord W1 z.re) (fun _ : S => encodeSignedWord W1 z.im))
  have pZIm := StageEval.seq pSnd
    (StageEval.snd (fun _ : S => encodeSignedWord W1 z.re) (fun _ : S => encodeSignedWord W1 z.im))
  have pRe1 := StageEval.seq (StageEval.fanout pShiftL pZRe)
    (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime (q2 - q1) W1 z.re hz1.1))
  have pIm1 := StageEval.seq (StageEval.fanout pShiftL pZIm)
    (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime (q2 - q1) W1 z.im hz1.2))
  have hre1_fits : FitsSignedWord ((q2 - q1) + W1) (z.re * (2 : ℤ) ^ (q2 - q1)) := by
    simpa [Nat.add_comm] using hz1.1.mul_two_pow (q2 - q1)
  have him1_fits : FitsSignedWord ((q2 - q1) + W1) (z.im * (2 : ℤ) ^ (q2 - q1)) := by
    simpa [Nat.add_comm] using hz1.2.mul_two_pow (q2 - q1)
  have pRe2 := StageEval.seq (StageEval.fanout pShiftR pRe1)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime ((q2 - q1) + W1) (q1 - q2)
      (z.re * (2 : ℤ) ^ (q2 - q1)) hre1_fits))
  have pIm2 := StageEval.seq (StageEval.fanout pShiftR pIm1)
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime ((q2 - q1) + W1) (q1 - q2)
      (z.im * (2 : ℤ) ^ (q2 - q1)) him1_fits))
  have pOut1 := StageEval.seq (StageEval.fanout pW2 pRe2)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime ((q2 - q1) + W1) W2
      (roundShiftInt (z.re * (2 : ℤ) ^ (q2 - q1)) (q1 - q2))
      (hre1_fits.roundShiftInt (q1 - q2)) hz2.1))
  have pOut2 := StageEval.seq (StageEval.fanout pW2 pIm2)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime ((q2 - q1) + W1) W2
      (roundShiftInt (z.im * (2 : ℤ) ^ (q2 - q1)) (q1 - q2))
      (him1_fits.roundShiftInt (q1 - q2)) hz2.2))
  rcases (StageEval.fanout pOut1 pOut2) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2, uQ] at ht
  have hsub1 : q2 - q1 ≤ q2 := Nat.sub_le q2 q1
  have hsub2 : q1 - q2 ≤ q1 := Nat.sub_le q1 q2
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

end IntMul
