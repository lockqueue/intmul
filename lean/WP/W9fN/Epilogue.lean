import WP.W9fN.PrologueRun
import WP.W9fN.FinCall

/-!
# WP.W9fN.Epilogue — after the loop: the Nyquist finish, then cleanup

* `RunsS.lift`, `tripleS_lift`: exact-stacks runs and stack-predicate triples lift to bigger
  register types through any lens (the finish's registers sit next to `GReg I`).
* `Lay.popR_runs`; `dCost_le`, `βstep_le`: the cleanup cost is at most `dMax H`.
* `epi I IF = finish; pop ZS's mark; drop all variables`; `epi_runs`: from the loop state after
  `t1 − 1` steps to the contract's final stacks.
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts
  WP.W7k2

theorem RunsS.lift {K σ τ : Type} [DecidableEq K] (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {T : ℕ} (h : RunsS P S S' T) : RunsS (P.liftRegs l) S S' T := by
  rintro ⟨w, S0⟩ hs
  change S0 = S at hs
  subst hs
  obtain ⟨s', t, e, hs', ht⟩ := h ⟨l.get w, S0⟩ rfl
  exact ⟨⟨l.set w s'.var, s'.stk⟩, t, Eval.liftRegs l e w rfl, hs', ht⟩

theorem tripleS_lift {K σ τ : Type} [DecidableEq K] (l : Lens σ τ)
    {P Q : (K → List Sym) → Prop} {p : Prog K (fun _ => Sym) τ} {T : ℕ}
    (h : Triple [] (fun s => P s.stk) p (fun s => Q s.stk) T) :
    Triple [] (fun s => P s.stk) (p.liftRegs l) (fun s => Q s.stk) T := by
  rintro ⟨w, S0⟩ hs
  obtain ⟨s', t, e, hq, ht⟩ := h ⟨l.get w, S0⟩ hs
  exact ⟨⟨l.set w s'.var, s'.stk⟩, t, Eval.liftRegs l e w rfl, hq, ht⟩

theorem Lay.popR_runs {K : Type} [DecidableEq K] (L : Lay K) {O : Type} [DecidableEq O]
    (I : O → OpImpl) {k : K} (hk : ∀ v, L.varLoc v ≠ k) (S0 X : K → List Sym) (env : V → ℤ)
    (x : Sym) (rest : List Sym) (hX : X k = x :: rest) :
    RunsS (hM I (popR k)) (L.hst S0 X env) (L.hst S0 (Function.update X k rest) env) 1 := by
  refine RunsS.of_eq (hM_runs I (fun r => ⟨some x, popR_eval' [] k r (L.hst S0 X env) x rest
    (by rw [L.hst_other S0 X env hk]; exact hX)⟩) le_rfl) ?_ le_rfl
  rw [L.hst_upd_X S0 X env hk]

theorem βstep_le (H : ℕ) (v : V) : βstep H v ≤ WP.W9f.solW H := by
  cases v <;> simp only [βstep, WP.W9f.solW] <;> omega

theorem dCost_le (env : V → ℤ) (W : ℕ) (h : ∀ v, bitLen (env v).natAbs ≤ W) :
    ∀ vs : List V, dCost env vs ≤ vs.length * (2 * W + 6) + 1
  | [] => by simp [dCost]
  | v :: vs => by
    have ih := dCost_le env W h vs
    have hv := h v
    simp only [dCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have e : (vs.length + 1) * (2 * W + 6) = vs.length * (2 * W + 6) + (2 * W + 6) := by ring
    rw [e]
    omega

/-- Cleanup cost cap. -/
def dMax (H : ℕ) : ℕ := V.all.length * (2 * WP.W9f.solW H + 6) + 1

theorem notEntry_mark' (l : List Sym) : WP.W9f.NotEntry (Sym.mark :: l) := by
  intro s h
  cases h
  exact ⟨by decide, by decide⟩

theorem vL_ne_OUT (v : V) : LN.varLoc v ≠ kOUT := vL_ne_inl v 1
theorem vL_ne_PK (v : V) : LN.varLoc v ≠ kPK := vL_ne_inl v 5
theorem vL_ne_PALT (v : V) : LN.varLoc v ≠ kPALT := vL_ne_inl v 7

#assert_std_axioms RunsS.lift tripleS_lift Lay.popR_runs βstep_le dCost_le notEntry_mark'
  vL_ne_OUT vL_ne_PK vL_ne_PALT

end WP.W9fN
