/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanSetup

/-!
# `SubNLogN.Machine.Walsh.CnotScanShift`: the split of the shift templates and generic kernel parts

Paper: Lemma 5.1 (`lem:walsh-select`) and Proposition 5.5 (`prop:cnot-batch`). Plan: top of
`Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** `splitP` (`e` units on `n3` become `tz = td = uSym^{min e W}`,
`tcc = uSym^{W - min e W}`) and small `RunsR` helpers; no contract is proved here.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift Computability

/-- One split step: take a unit from `tcc` (if any) and put one on `td` and `tz`. -/
def splitStep : EProg SK :=
  .seq (popS (.inr .tcc)) (.seq (.ite (fun r => r.s.isSome)
    (.seq (pushK (.inr .td) uSym) (pushK (.inr .tz) uSym)) (.load id)) (popT (.inr .n3)))

/-- Move `min e a` units from `tcc` (`a` units) to `td` and `tz`, `e` the units on `n3`. -/
def splitP : EProg SK := .seq (popT (.inr .n3)) (.loop tSome splitStep)

theorem closed_splitP : splitP.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, splitP, splitStep, popS, popT, pushK]

theorem splitP_loop (A : ER → Prop) (hA : ∀ r v w, A r → A { r with t := v, s := w }) :
    ∀ (e a b : ℕ) (r : ER) (S : SK → List Sym), A r →
      r.t = (List.replicate e uSym).head? → S (.inr .n3) = (List.replicate e uSym).tail →
      S (.inr .tcc) = List.replicate a uSym → S (.inr .td) = List.replicate b uSym →
      S (.inr .tz) = List.replicate b uSym →
      ∃ r' t, Eval [] (.loop tSome splitStep) ⟨r, S⟩
        ⟨r', Function.update (Function.update (Function.update (Function.update S (.inr .n3) [])
          (.inr .tcc) (List.replicate (a - min e a) uSym)) (.inr .td)
          (List.replicate (b + min e a) uSym)) (.inr .tz) (List.replicate (b + min e a) uSym)⟩
          t ∧ A r' ∧ t ≤ 6 * e + 1
  | 0, a, b, r, S, hr, ht, hn, hc, hd, hz => by
    have ht' : r.t = none := by simpa using ht
    have hn' : S (.inr .n3) = [] := by simpa using hn
    refine ⟨r, 1, (Eval.loop_false (by simp [tSome, ht'])).of_eq ?_ rfl, hr, by omega⟩
    congr 1
    funext j
    rcases j with i | e
    · simp
    · cases e <;> simp [hn', hc, hd, hz]
  | e + 1, a, b, r, S, hr, ht, hn, hc, hd, hz => by
    have ht' : r.t = some uSym := by simpa [List.replicate_succ] using ht
    have hn' : S (.inr .n3) = List.replicate e uSym := by simpa [List.replicate_succ] using hn
    rcases a with _ | a
    · -- `tcc` is empty: nothing is moved
      have e1 := eval_popS (.inr .tcc : SK) r [] S (by simpa using hc)
      have e2 : Eval [] (.ite (fun r : ER => r.s.isSome)
          (.seq (pushK (.inr .td) uSym) (pushK (.inr .tz) uSym)) (.load id))
          ⟨{ r with s := ([] : List Sym).head? }, Function.update S (.inr .tcc) ([] : List Sym).tail⟩
          ⟨{ r with s := ([] : List Sym).head? }, Function.update S (.inr .tcc) ([] : List Sym).tail⟩
          2 := Eval.ite_false rfl (Eval.load [] id _ _)
      have e3 := eval_popT (.inr .n3 : SK) { r with s := ([] : List Sym).head? }
        (List.replicate e uSym) (Function.update S (.inr .tcc) ([] : List Sym).tail)
        (by simp [hn'])
      obtain ⟨r', t, e4, hr', ht4⟩ := splitP_loop A hA e 0 b
        { r with t := (List.replicate e uSym).head?, s := ([] : List Sym).head? }
        (Function.update (Function.update S (.inr .tcc) ([] : List Sym).tail) (.inr .n3)
          (List.replicate e uSym).tail) (hA r _ _ hr) rfl
        (Function.update_self _ _ _) (by simp) (by simp [hd]) (by simp [hz])
      refine ⟨r', _, (Eval.loop_true (by simp [tSome, ht']) (Eval.seq e1 (Eval.seq e2 e3))
        e4).of_eq ?_ rfl, hr', by omega⟩
      congr 1
      funext j
      rcases j with i | e
      · simp
      · cases e <;> simp
    · -- one unit moves
      have e1 := eval_popS (.inr .tcc : SK) r (uSym :: List.replicate a uSym) S
        (by rw [hc, List.replicate_succ])
      set S1 := Function.update S (.inr .tcc) (uSym :: List.replicate a uSym).tail with hS1
      have e2 := eval_pushK (.inr .td : SK) uSym { r with s := some uSym } S1
      have e3 := eval_pushK (.inr .tz : SK) uSym { r with s := some uSym }
        (Function.update S1 (.inr .td) (uSym :: S1 (.inr .td)))
      have e23 : Eval [] (.ite (fun r : ER => r.s.isSome)
          (.seq (pushK (.inr .td) uSym) (pushK (.inr .tz) uSym)) (.load id))
          ⟨{ r with s := some uSym }, S1⟩ _ 3 := Eval.ite_true rfl (Eval.seq e2 e3)
      set S3 := Function.update (Function.update S1 (.inr .td) (uSym :: S1 (.inr .td))) (.inr .tz)
        (uSym :: Function.update S1 (.inr .td) (uSym :: S1 (.inr .td)) (.inr .tz)) with hS3
      have e4 := eval_popT (.inr .n3 : SK) { r with s := some uSym } (List.replicate e uSym) S3
        (by simp [hS3, hS1, hn'])
      obtain ⟨r', t, e5, hr', ht5⟩ := splitP_loop A hA e a (b + 1)
        { r with t := (List.replicate e uSym).head?, s := some uSym }
        (Function.update S3 (.inr .n3) (List.replicate e uSym).tail) (hA r _ _ hr) rfl
        (Function.update_self _ _ _) (by simp [hS3, hS1]) (by simp [hS3, hS1, hd,
          List.replicate_succ]) (by simp [hS3, hS1, hz, List.replicate_succ])
      refine ⟨r', _, (Eval.loop_true (by simp [tSome, ht']) (Eval.seq e1 (Eval.seq e23 e4))
        e5).of_eq ?_ rfl, hr', by omega⟩
      congr 1
      funext j
      rcases j with i | e'
      · simp [hS3, hS1]
      · cases e' <;> simp [hS3, hS1] <;> omega

theorem runsR_splitP (A : ER → Prop) (hA : ∀ r v w, A r → A { r with t := v, s := w })
    (e a : ℕ) (S : SK → List Sym) (hn : S (.inr .n3) = List.replicate e uSym)
    (hc : S (.inr .tcc) = List.replicate a uSym) (hd : S (.inr .td) = [])
    (hz : S (.inr .tz) = []) :
    RunsR splitP S
      (Function.update (Function.update (Function.update (Function.update S (.inr .n3) [])
        (.inr .tcc) (List.replicate (a - min e a) uSym)) (.inr .td)
        (List.replicate (min e a) uSym)) (.inr .tz) (List.replicate (min e a) uSym))
      A A (6 * e + 2) := by
  intro r hr
  have e1 := eval_popT (.inr .n3 : SK) r _ S hn
  obtain ⟨r', t, e2, hr', ht⟩ := splitP_loop A hA e a 0
    { r with t := (List.replicate e uSym).head? }
    (Function.update S (.inr .n3) (List.replicate e uSym).tail) (hA r _ r.s hr) rfl
    (Function.update_self _ _ _) (by simp [hc]) (by simp [hd]) (by simp [hz])
  refine ⟨r', _, (Eval.seq e1 e2).of_eq ?_ rfl, hr', by omega⟩
  congr 1
  funext j
  rcases j with i | e
  · simp
  · cases e <;> simp

/-! ## Small `RunsR` helpers -/

theorem runsR_pushK (k : SK) (x : Sym) (S : SK → List Sym) (A : ER → Prop) :
    RunsR (pushK k x) S (Function.update S k (x :: S k)) A A 1 :=
  fun r hr => ⟨r, 1, eval_pushK k x r S, hr, le_rfl⟩

theorem runsR_load (f : ER → ER) (S : SK → List Sym) (A B : ER → Prop) (h : ∀ r, A r → B (f r)) :
    RunsR (.load f) S S A B 1 :=
  fun r hr => ⟨f r, 1, Eval.load [] f r S, h r hr, le_rfl⟩

theorem recLoopS_runs (kR incR : EProg SK) (kfun : ℕ → Fin 4) (idx : ℕ → List Sym)
    (stat : (SK → List Sym) → Prop) (ck ci : ℕ) (hkR : KRSpec kR kfun idx stat ck)
    (hinc : IncSpec incR idx stat ci) (hstat : StatFrame stat) (n1 n2 : ℕ) (hW : 1 ≤ n1 + n2)
    (mu : Bool) (rest : List Sym) (hrest : BlkTerm rest)
    (recs : List (List (List Bool × List Bool))) (x0 : ℕ) (S : SK → List Sym)
    (hrecs : ∀ cs ∈ recs, ∀ c ∈ cs, c.1.length = n1 + n2 ∧ c.2.length = n1 + n2)
    (hT : TplB n1 n2 S) (hst : stat S) (hx : S (.inr .x) = idx x0)
    (hA : S (.inl 0) = arrSyms (recs.map fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest) :
    RunsR (recLoopS kR incR) S
      (Function.update (Function.update (Function.update S (.inl 0) rest) (.inr .o)
        ((arrSyms (outRecs mu kfun n1 n2 x0 recs)).reverse ++ S (.inr .o))) (.inr .x)
        (idx (x0 + recs.length)))
      (fun r => r.mu = mu) (fun r => r.mu = mu)
      ((recs.map fun cs => ck + cs.length * (coefCost n1 n2 + 2) + ci + 7).sum + 2) := by
  intro r hr
  have e1 := eval_peekT (.inl 0) r S
  obtain ⟨r', t, e2, hr', ht⟩ := recLoopS_loop kR incR kfun idx stat ck ci hkR hinc hstat n1 n2
    hW mu rest hrest recs x0 S hrecs hT hst hx hA { r with t := (S (.inl 0)).head? } ⟨hr, rfl⟩
  exact ⟨r', 1 + t, Eval.seq e1 e2, hr', by omega⟩

end SubNLogN.Machine.WalshScanAux
