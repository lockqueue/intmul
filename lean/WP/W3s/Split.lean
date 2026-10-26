import WP.W3s.SplitCore

/-!
# WP.W3s.Split — `W3_splitAt` and `W3_shrVar`

* `splitAtProg` on `Loc 3 3`: `x = .inl 0`, `c = .inl 1`, `y = .inl 2`; scratch `t = .inr 0`,
  `kc = .inr 1`, `u = .inr 2`. It is `splitCore` itself; `C = 30`.
* `shrVarProg` on `Loc 2 4`: guard the fourth scratch stack `w = .inr 3` with a `mark`, run
  `splitCore` with the low part sent to `w`, then pop the low part and the mark (`dropBits w`);
  `C = 33`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b Computability

/-- The `W3_splitAt` program. -/
def splitAtProg : SProg (Loc 3 3) :=
  splitCore (.inl 0) (.inl 1) (.inl 2) (.inr 1) (.inr 2) (.inr 0)

theorem W3_splitAt_holds : W3_splitAt := by
  refine ⟨30, fun _ => ⟨3, Option Sym, fun _ => (), splitAtProg, by decide, inferInstance, ⟨none⟩,
    splitCore_closed _ _ _ _ _ _, ?_⟩⟩
  intro a n rx rc S hrx hrc hx hc
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := splitCore_eval (x := .inl 0) (c := .inl 1) (y := .inl 2) (kc := .inr 1)
    (u := .inr 2) (t := .inr 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [] v a n rx
    rc hrx hrc S hx hc
  exact ⟨v', t, e, trivial, ht⟩

/-- The `W3_shrVar` program: split into the guarded scratch stack `.inr 3`, then drop it. -/
def shrVarProg : SProg (Loc 2 4) :=
  .seq (pushC (.inr 3) .mark)
    (.seq (splitCore (.inl 0) (.inl 1) (.inr 3) (.inr 1) (.inr 2) (.inr 0)) (dropBits (.inr 3)))

theorem shrVarProg_closed : shrVarProg.Closed := by
  have h := splitCore_closed (.inl 0 : Loc 2 4) (.inl 1) (.inr 3) (.inr 1) (.inr 2) (.inr 0)
  unfold Prog.Closed at h
  simp [Prog.Closed, Prog.FreeBelow, shrVarProg, dropBits, dropLoop, pushC, popR, h]

theorem W3_shrVar_holds : W3_shrVar := by
  refine ⟨33, fun _ => ⟨4, Option Sym, fun _ => (), shrVarProg, le_refl _, inferInstance, ⟨none⟩,
    shrVarProg_closed, ?_⟩⟩
  intro a n rx rc S hrx hrc hx hc
  refine Runs.of_eval fun v => ?_
  have e1 : Eval [] (pushC (.inr 3 : Loc 2 4) .mark) ⟨v, S⟩
      ⟨v, Function.update S (.inr 3) (.mark :: S (.inr 3))⟩ 1 :=
    eval_push_eq [] (.inr 3 : Loc 2 4) (fun _ => Sym.mark) v S Sym.mark (S (.inr 3)) rfl rfl
  set S1 := Function.update S (.inr 3) (Sym.mark :: S (.inr 3)) with hS1
  have hx1 : S1 (.inl 0) = natSyms a ++ rx := by
    rw [hS1, Function.update_of_ne (by decide), hx]
  have hc1 : S1 (.inl 1) = natSyms n ++ rc := by
    rw [hS1, Function.update_of_ne (by decide), hc]
  obtain ⟨v2, t2, e2, ht2⟩ := splitCore_eval (x := .inl 0) (c := .inl 1) (y := .inr 3)
    (kc := .inr 1) (u := .inr 2) (t := .inr 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    [] v a n rx rc hrx hrc S1 hx1 hc1
  set S2 := Function.update (Function.update S1 (.inl 0) (natSyms (a / 2 ^ n) ++ rx)) (.inr 3)
    (natSyms (a % 2 ^ n) ++ S1 (.inr 3)) with hS2
  have hS2w : S2 (.inr 3) = (encodeNat (a % 2 ^ n)).map Sym.bit ++ (Sym.mark :: S (.inr 3)) := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
    rfl
  have e3 := dropBits_eval [] v2 (encodeNat (a % 2 ^ n)) (Sym.mark :: S (.inr 3)) S2
    (TermOK.cons rfl _) hS2w
  refine ⟨(Sym.mark :: S (.inr 3)).head?, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, trivial,
    ?_⟩
  · congr 1
    funext j
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · have hb := bitLen_mod_le a n
    simp only [bitLen] at hb ht2 ⊢
    omega

#assert_std_axioms W3_splitAt_holds shrVarProg_closed W3_shrVar_holds

end TMFw.W3s
