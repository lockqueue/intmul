import WP.W9fN.SL
import WP.W7k2.Call

/-!
# WP.W9fN.HostL — host layout for compiled straight-line code (generic in the host stacks)

Shared with S1 (`wp/W9fF`): everything here is generic in the host stack type `K`.
* `Lay K`: where the variables (`varLoc : V → K`) and the 20 IntLang scratch stacks
  (`ilScr : Fin 20 → K`) live; both injective, disjoint. `Lay.emb : IStk V → K`.
* `Lay.hst S0 X env`: host stacks in which variable `v` sits at `varLoc v` as
  `intSyms (env v) ++ mark :: S0 (varLoc v)` (mark-guarded on top of the old content) and every
  other stack `k` holds `X k`. Update lemmas `hst_var`, `hst_other`, `hst_upd_env`, `hst_upd_X`.
* `hM I p`: a macro (`SProg K`, one `Option Sym` register) run inside a compiled program
  (registers `GReg I`, through `macroLens I`); `hM_runs`.
* **`hst_compile`**: a compiled `SL` program, embedded along `Lay.emb`, maps `hst S0 X env` to
  `hst S0 X (ev p env)` within `p.cost Op.sem κ env` steps (IntLang's `compile_runs` + `Runs.embed`).
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts WP.W9fN.IL

/-- Host layout of the variables and of IntLang's scratch stacks. -/
structure Lay (K : Type) where
  /-- stack of variable `v` -/
  varLoc : V → K
  /-- IntLang scratch stack `j` -/
  ilScr : Fin 20 → K
  var_inj : Function.Injective varLoc
  scr_inj : Function.Injective ilScr
  disj : ∀ v j, varLoc v ≠ ilScr j

namespace Lay

variable {K : Type} [DecidableEq K] (L : Lay K)

/-- Embedding of IntLang's stacks into the host. -/
def emb : IStk V → K
  | .inl v => L.varLoc v
  | .inr j => L.ilScr j

omit [DecidableEq K] in
theorem emb_injective : Function.Injective L.emb := by
  rintro (v | j) (v' | j') h <;> simp only [emb] at h
  · rw [L.var_inj h]
  · exact absurd h (L.disj v j')
  · exact absurd h.symm (L.disj v' j)
  · rw [L.scr_inj h]

/-- The variable stored at a host stack, if any. -/
def varOf (k : K) : Option V := V.all.find? (fun v => decide (L.varLoc v = k))

theorem varOf_loc (v : V) : L.varOf (L.varLoc v) = some v := by
  unfold varOf
  cases h : V.all.find? (fun w => decide (L.varLoc w = L.varLoc v)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (decide_eq_true rfl) (h v (V.mem_all v))
  | some w =>
    have hw := List.find?_some h
    simp only [decide_eq_true_eq] at hw
    rw [L.var_inj hw]

theorem loc_of_varOf {k : K} {v : V} (h : L.varOf k = some v) : L.varLoc v = k := by
  have := List.find?_some h
  simpa using this

theorem varOf_none {k : K} (h : L.varOf k = none) (v : V) : L.varLoc v ≠ k := by
  intro e
  subst e
  rw [L.varOf_loc] at h
  cases h

/-- Host stacks: variable `v` at `varLoc v` (mark-guarded above `S0`), `X k` elsewhere. -/
def hst (S0 X : K → List Sym) (env : V → ℤ) (k : K) : List Sym :=
  match L.varOf k with
  | some v => intSyms (env v) ++ Sym.mark :: S0 k
  | none => X k

@[simp] theorem hst_var (S0 X : K → List Sym) (env : V → ℤ) (v : V) :
    L.hst S0 X env (L.varLoc v) = intSyms (env v) ++ Sym.mark :: S0 (L.varLoc v) := by
  simp [hst, L.varOf_loc]

theorem hst_other (S0 X : K → List Sym) (env : V → ℤ) {k : K} (h : ∀ v, L.varLoc v ≠ k) :
    L.hst S0 X env k = X k := by
  unfold hst
  cases hk : L.varOf k with
  | none => rfl
  | some v => exact absurd (L.loc_of_varOf hk) (h v)

theorem hst_upd_env (S0 X : K → List Sym) (env : V → ℤ) (v : V) (c : ℤ) :
    L.hst S0 X (Function.update env v c) =
      Function.update (L.hst S0 X env) (L.varLoc v) (intSyms c ++ Sym.mark :: S0 (L.varLoc v)) := by
  funext k
  by_cases hk : ∃ w, L.varLoc w = k
  · obtain ⟨w, rfl⟩ := hk
    rw [hst_var]
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hwv, Function.update_of_ne (L.var_inj.ne hwv), hst_var]
  · push_neg at hk
    rw [L.hst_other _ _ _ hk, Function.update_of_ne (fun e => hk v e.symm), L.hst_other _ _ _ hk]

theorem hst_upd_X (S0 X : K → List Sym) (env : V → ℤ) {k : K} (h : ∀ v, L.varLoc v ≠ k)
    (l : List Sym) :
    Function.update (L.hst S0 X env) k l = L.hst S0 (Function.update X k l) env := by
  funext k'
  by_cases hk : ∃ w, L.varLoc w = k'
  · obtain ⟨w, rfl⟩ := hk
    rw [Function.update_of_ne (h w), hst_var, hst_var]
  · push_neg at hk
    rw [L.hst_other _ _ _ hk]
    by_cases e : k' = k
    · subst e
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne e, Function.update_of_ne e, L.hst_other _ _ _ hk]

end Lay

/-! ## Macros inside compiled programs -/

section Macro

variable {K : Type} [DecidableEq K] {O : Type} [DecidableEq O] (I : O → OpImpl)

/-- Run a macro (one `Option Sym` register) with the registers of a compiled program. -/
def hM (p : SProg K) : Prog K (fun _ => Sym) (GReg I) := p.liftRegs (macroLens I)

omit [DecidableEq O] in
theorem hM_runs {p : SProg K} {S S' : K → List Sym} {t T : ℕ}
    (h : ∀ v, ∃ v', Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t) (ht : t ≤ T) : RunsS (hM I p) S S' T := by
  rintro ⟨w, S0⟩ hs
  change S0 = S at hs
  subst hs
  obtain ⟨v', e⟩ := h ((macroLens I).get w)
  exact ⟨_, t, Eval.liftRegs (macroLens I) e w rfl, rfl, ht⟩

omit [DecidableEq K] [DecidableEq O] in
theorem hM_closed (p : SProg K) (hp : p.Closed) : (hM I p).Closed :=
  WP.W7k2.freeBelow_liftRegs (macroLens I) p 0 hp

end Macro

/-! ## Compiled straight-line code on the host -/

namespace Lay

variable {K : Type} [DecidableEq K] (L : Lay K)

/-- **Embedding of compiled code.** -/
theorem hst_compile (I : Op → OpImpl) (κ : Op → ℤ → ℤ → ℕ)
    (hok : ∀ o, BinOK (I o) (Op.sem o) (κ o)) (p : SL) (S0 X : K → List Sym) (env : V → ℤ) :
    RunsS ((p.compile I).mapStk L.emb) (L.hst S0 X env) (L.hst S0 X (ev p env))
      (p.cost Op.sem κ env) := by
  have hR : ∀ v, TermOK ((fun v => Sym.mark :: S0 (L.varLoc v)) v) := fun v => TermOK.cons rfl _
  have hc := compile_runs I Op.sem κ hok (fun v => Sym.mark :: S0 (L.varLoc v)) hR p
    (fun j => X (L.ilScr j)) env
  have hB : ∀ l, L.hst S0 X env (L.emb l) =
      enc (fun v => Sym.mark :: S0 (L.varLoc v)) (fun j => X (L.ilScr j)) env l := by
    rintro (v | j)
    · show L.hst S0 X env (L.varLoc v) = intSyms (env v) ++ Sym.mark :: S0 (L.varLoc v)
      exact L.hst_var S0 X env v
    · show L.hst S0 X env (L.ilScr j) = X (L.ilScr j)
      exact L.hst_other S0 X env (fun v => L.disj v j)
  have hE := Runs.embed L.emb_injective hc (L.hst S0 X env) hB
  refine Triple.post hE (fun s hs => ?_)
  obtain ⟨h1, h2, -⟩ := hs
  funext k
  by_cases hk : ∃ w, L.varLoc w = k
  · obtain ⟨w, rfl⟩ := hk
    have e := h1 (.inl w)
    simp only [emb, enc] at e
    rw [e, hst_var]
  · push_neg at hk
    rw [L.hst_other S0 X _ hk]
    by_cases hj : ∃ j, L.ilScr j = k
    · obtain ⟨j, rfl⟩ := hj
      have e := h1 (.inr j)
      simp only [emb, enc] at e
      exact e
    · push_neg at hj
      have e := h2 k (by
        rintro (v | j) e
        · exact hk v e
        · exact hj j e)
      rw [e, L.hst_other S0 X env hk]

end Lay

#assert_std_axioms Lay.emb_injective Lay.varOf_loc Lay.loc_of_varOf Lay.varOf_none Lay.hst_var
  Lay.hst_other Lay.hst_upd_env Lay.hst_upd_X hM_runs hM_closed Lay.hst_compile

end WP.W9fN
