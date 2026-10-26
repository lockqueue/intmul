import WP.W3s.ConcatCore

/-!
# WP.W3s.Concat — `W3_concatAt` and `W3_shlVar`

* `concatAtProg` on `Loc 3 3`: `x = .inl 0`, `c = .inl 1`, `y = .inl 2`; scratch `t = .inr 0`,
  `kc = .inr 1`, `u = .inr 2`. It is `concatCore` itself; `C = 30`.
* `shlVarProg` on `Loc 2 4`: `a·2^c = 0 + a·2^c` is a concatenation with an empty low part: push a
  `mark` on the fourth scratch stack `w = .inr 3` (so `w` holds `natSyms 0` above a terminator),
  run `concatCore` with `y = w`, then pop the mark; `C = 32`.
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts TMFw.W3b Computability

/-- The `W3_concatAt` program. -/
def concatAtProg : SProg (Loc 3 3) :=
  concatCore (.inl 0) (.inl 1) (.inl 2) (.inr 1) (.inr 2) (.inr 0)

theorem W3_concatAt_holds : W3_concatAt := by
  refine ⟨30, fun _ => ⟨3, Option Sym, fun _ => (), concatAtProg, by decide, inferInstance,
    ⟨none⟩, concatCore_closed _ _ _ _ _ _, ?_⟩⟩
  intro hi lo n rx rc ry S hrx hrc hry hlo hx hc hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := concatCore_eval (x := .inl 0) (c := .inl 1) (y := .inl 2)
    (kc := .inr 1) (u := .inr 2) (t := .inr 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    [] v hi lo n rx rc ry hrx hrc hry hlo S hx hc hy
  exact ⟨v', t, e, trivial, ht⟩

/-- The `W3_shlVar` program: concatenate an empty low part held on the guarded scratch `.inr 3`. -/
def shlVarProg : SProg (Loc 2 4) :=
  .seq (pushC (.inr 3) .mark)
    (.seq (concatCore (.inl 0) (.inl 1) (.inr 3) (.inr 1) (.inr 2) (.inr 0)) (popR (.inr 3)))

theorem shlVarProg_closed : shlVarProg.Closed := by
  have h := concatCore_closed (.inl 0 : Loc 2 4) (.inl 1) (.inr 3) (.inr 1) (.inr 2) (.inr 0)
  unfold Prog.Closed at h
  simp [Prog.Closed, Prog.FreeBelow, shlVarProg, pushC, popR, h]

theorem W3_shlVar_holds : W3_shlVar := by
  refine ⟨32, fun _ => ⟨4, Option Sym, fun _ => (), shlVarProg, le_refl _, inferInstance, ⟨none⟩,
    shlVarProg_closed, ?_⟩⟩
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
  have hw1 : S1 (.inr 3) = natSyms 0 ++ (Sym.mark :: S (.inr 3)) := by
    rw [hS1, Function.update_self, natSyms_zero, List.nil_append]
  obtain ⟨v2, t2, e2, ht2⟩ := concatCore_eval (x := .inl 0) (c := .inl 1) (y := .inr 3)
    (kc := .inr 1) (u := .inr 2) (t := .inr 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    [] v a 0 n rx rc (Sym.mark :: S (.inr 3)) hrx hrc (TermOK.cons rfl _) (Nat.two_pow_pos n) S1
    hx1 hc1 hw1
  set S2 := Function.update (Function.update S1 (.inl 0) (natSyms (0 + a * 2 ^ n) ++ rx)) (.inr 3)
    (Sym.mark :: S (.inr 3)) with hS2
  have e3 := eval_pop_eq [] (.inr 3 : Loc 2 4) (fun _ o => o) v2 S2 Sym.mark (S (.inr 3))
    (by rw [hS2, Function.update_self])
  refine ⟨some Sym.mark, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, trivial, ?_⟩
  · congr 1
    funext j
    simp only [hS2, hS1, Nat.zero_add, Function.update_apply]
    split_ifs <;> simp_all
  · omega

#assert_std_axioms W3_concatAt_holds shlVarProg_closed W3_shlVar_holds

end TMFw.W3s
