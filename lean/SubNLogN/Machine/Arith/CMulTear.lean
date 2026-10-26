/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulDrv
import SubNLogN.Machine.Arith.CMulSetup

/-!
# AR4, products: teardown and the kernel program (`Arith/CMulTear.lean`)

**Scope (honest summary).** The teardown `cmulTeardown`, the kernel program `cmulKernel`, the
teardown lemma `cmulTeardown_eval` (exact), and shape lemmas used for the cost. Everything is
proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-- Teardown: output onto the destination, clear the rulers. -/
def cmulTeardown : AProg CK :=
  .seq ((WP.W9comp.rewindTo (cs .T) (.inl 2) .mark).liftRegs lensO)
  (.seq (clearMarks (cs .R1)) (.seq (clearMarks (cs .Rt)) (.seq (clearMarks (cs .R2))
  (.seq (clearMarks (cs .RW)) (.seq (clearMarks (cs .Rs)) (clearMarks (cs .Rh)))))))

/-- **The product kernel.** -/
def cmulKernel {Rm : Type} (Pm : Prog MBLoc (fun _ => Sym) Rm) :
    Prog CK (fun _ => Sym) (AReg × Rm) :=
  .seq (cmulSetup.liftRegs (Lens.fst AReg Rm))
  (.seq ((peekO (.inl 0)).liftRegs (Lens.fst AReg Rm))
  (.seq (recLoopC (coefProg Pm)) (cmulTeardown.liftRegs (Lens.fst AReg Rm))))

set_option maxHeartbeats 8000000 in
theorem cmulTeardown_eval (w1 w2 w3 s : ℕ) (OUT rz rθ : List Sym) (hOUT : Sym.mark ∉ OUT)
    (v : AReg) (S : CK → List Sym) (hKC : KClean S) :
    ∃ v' : AReg, Eval [] cmulTeardown
      ⟨v, Function.update (Function.update (Function.update (setupSt w1 w2 w3 s S) (.inl 0) rz)
        (.inl 1) rθ) (cs .T) (OUT.reverse ++ setupSt w1 w2 w3 s S (cs .T))⟩
      ⟨v', Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
        (OUT ++ S (.inl 2))⟩
      (3 * OUT.length + 2 + (3 * w1 + 2) + (3 * w2 + 2) + (3 * w3 + 2) +
        (3 * (2 * max w1 w2 + 1) + 2) + (3 * min s (2 * max w1 w2 + 1) + 2) +
        (3 * (2 * max w1 w2 + 1 - min s (2 * max w1 w2 + 1)) + 2)) := by
  have hK : ∀ c : CS, S (cs c) = [] := fun c => hKC (.inl c)
  set Q0 := Function.update (Function.update (Function.update (setupSt w1 w2 w3 s S) (.inl 0) rz)
    (.inl 1) rθ) (cs .T) (OUT.reverse ++ setupSt w1 w2 w3 s S (cs .T)) with hQ0
  have hT : Q0 (cs .T) = OUT.reverse ++ Sym.mark :: [] := by simp [hQ0, setupSt, hK]
  have e1 := Eval.liftRegs lensO (WP.W9comp.rewindTo_eval (src := cs .T) (dst := (.inl 2 : CK))
    (by decide) .mark (lensO.get v) OUT.reverse [] Q0 (by simpa using hOUT) hT) v rfl
  set Q1 := Function.update (Function.update Q0 (cs .T) []) (.inl 2)
    (OUT.reverse.reverse ++ Q0 (.inl 2)) with hQ1
  obtain ⟨u2, e2⟩ : ∃ u, Eval [] (clearMarks (cs .R1)) ⟨lensO.set v (some .mark), Q1⟩
      ⟨u, Function.update Q1 (cs .R1) []⟩ (3 * w1 + 2) :=
    ⟨_, clearMarks_eval (R := cs .R1) w1 [] _ Q1 aHead_nil (by simp [hQ1, hQ0, setupSt])⟩
  set Q2 := Function.update Q1 (cs .R1) [] with hQ2
  obtain ⟨u3, e3⟩ : ∃ u, Eval [] (clearMarks (cs .Rt)) ⟨u2, Q2⟩
      ⟨u, Function.update Q2 (cs .Rt) []⟩ (3 * w2 + 2) :=
    ⟨_, clearMarks_eval (R := cs .Rt) w2 [] _ Q2 aHead_nil (by simp [hQ2, hQ1, hQ0, setupSt])⟩
  set Q3 := Function.update Q2 (cs .Rt) [] with hQ3
  obtain ⟨u4, e4⟩ : ∃ u, Eval [] (clearMarks (cs .R2)) ⟨u3, Q3⟩
      ⟨u, Function.update Q3 (cs .R2) []⟩ (3 * w3 + 2) :=
    ⟨_, clearMarks_eval (R := cs .R2) w3 [] _ Q3 aHead_nil
      (by simp [hQ3, hQ2, hQ1, hQ0, setupSt])⟩
  set Q4 := Function.update Q3 (cs .R2) [] with hQ4
  obtain ⟨u5, e5⟩ : ∃ u, Eval [] (clearMarks (cs .RW)) ⟨u4, Q4⟩
      ⟨u, Function.update Q4 (cs .RW) []⟩ (3 * (2 * max w1 w2 + 1) + 2) :=
    ⟨_, clearMarks_eval (R := cs .RW) (2 * max w1 w2 + 1) [] _ Q4 aHead_nil
      (by simp [hQ4, hQ3, hQ2, hQ1, hQ0, setupSt])⟩
  set Q5 := Function.update Q4 (cs .RW) [] with hQ5
  obtain ⟨u6, e6⟩ : ∃ u, Eval [] (clearMarks (cs .Rs)) ⟨u5, Q5⟩
      ⟨u, Function.update Q5 (cs .Rs) []⟩ (3 * min s (2 * max w1 w2 + 1) + 2) :=
    ⟨_, clearMarks_eval (R := cs .Rs) (min s (2 * max w1 w2 + 1)) [] _ Q5 aHead_nil
      (by simp [hQ5, hQ4, hQ3, hQ2, hQ1, hQ0, setupSt])⟩
  set Q6 := Function.update Q5 (cs .Rs) [] with hQ6
  obtain ⟨u7, e7⟩ : ∃ u, Eval [] (clearMarks (cs .Rh)) ⟨u6, Q6⟩
      ⟨u, Function.update Q6 (cs .Rh) []⟩
      (3 * (2 * max w1 w2 + 1 - min s (2 * max w1 w2 + 1)) + 2) :=
    ⟨_, clearMarks_eval (R := cs .Rh) (2 * max w1 w2 + 1 - min s (2 * max w1 w2 + 1)) [] _ Q6
      aHead_nil (by simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hQ0, setupSt])⟩
  refine ⟨u7, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    e7)))))).of_eq ?_ ?_⟩
  · congr 1
    funext k
    rcases k with i | c | g
    · fin_cases i <;> simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hQ0, setupSt]
    · cases c <;> simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hQ0, setupSt, hK]
    · simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hQ0, setupSt]
  · simp only [List.length_reverse]
    ring

/-! ## Shapes -/

theorem zipC_shape (f : CInt → CInt → CInt) {z θ : List (List CInt)} (h : CAligned z θ) :
    (zipC f z θ).length = z.length ∧ ncoef (zipC f z θ) = ncoef z := by
  unfold CAligned at h
  induction h with
  | nil => simp [zipC, ncoef]
  | @cons x y z θ hxy _ ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [zipC, ncoef] at h1 h2 ⊢
    simp only [List.zipWith_cons_cons, List.length_cons, List.map_cons, List.sum_cons, h1, h2,
      List.length_zipWith, hxy, min_self, and_self]

theorem aligned_shape {z θ : List (List CInt)} (h : CAligned z θ) :
    θ.length = z.length ∧ ncoef θ = ncoef z := by
  unfold CAligned at h
  induction h with
  | nil => simp [ncoef]
  | @cons x y z θ hxy _ ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [ncoef] at h2 ⊢
    simp only [List.length_cons, List.map_cons, List.sum_cons, h1, h2, hxy, and_self]

theorem mark_not_mem_carrSyms (w : ℕ) (v : List (List CInt)) : Sym.mark ∉ carrSyms w v := by
  simp [carrSyms, arrSyms, blk, recSyms]

theorem setupSt_work {w1 w2 w3 s : ℕ} {S : CK → List Sym} (hKC : KClean S) :
    ∀ c, isWork c = true → setupSt w1 w2 w3 s S (cs c) = [] := by
  intro c hc
  have hK : S (cs c) = [] := hKC (.inl c)
  cases c <;> simp_all [setupSt, isWork]

end SubNLogN.Machine.Arith
