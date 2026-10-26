/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.SafeTransport
import SubNLogN.Machine.Contracts.Family

/-!
# Framed procedure calculus: safety from the read footprint (`Calculus/SafeFootprint.lean`)

`SafeEval` adds side conditions only to `peek`/`pop` of *framed* stacks. A program whose `peek`s and
`pop`s (and those of its procedure environment) all target unframed stacks therefore has a
boundary-safe run whenever it has a run. Pushes onto framed stacks are always safe.

* `ReadsIn A p`: every `peek k` / `pop k` occurring in `p` has `A k`.
* `SafeEval.of_eval_readsIn`: an `Eval` run of such a program is a `SafeEval` run, for every
  `framed` disjoint from `A`, provided the environment programs satisfy the same condition.
* `SafeRunsIn.of_runsIn_readsIn` and `SafeRunsIn.of_runs_readsIn` are the judgment-level
  bridges. Legacy `Runs`/`RunsIn` kernels (for example the `Hdr` header programs) can enter a
  `SafeRunsIn` proof unchanged if they read only unframed stacks, such as the C-core `io`/`desc`.
* `readsIn_mono`, `readsIn_liftRegs`, `readsIn_mapStk`, `readsIn_forEachProg` are closure rules.

This provides a direct operational safety certificate (without `Runs`-to-safety lifting) for kernels
whose reads are confined to unframed stacks.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section Footprint

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- Every `peek k` and `pop k` of the program satisfies `A k`. Pushes, loads and control structure
are unrestricted; a `recur` is checked through the environment. -/
def ReadsIn (A : K → Prop) : Prog K Γ σ → Prop
  | .push _ _ => True
  | .peek k _ => A k
  | .pop k _ => A k
  | .load _ => True
  | .seq p q => ReadsIn A p ∧ ReadsIn A q
  | .ite _ p q => ReadsIn A p ∧ ReadsIn A q
  | .loop _ p => ReadsIn A p
  | .fix b => ReadsIn A b
  | .recur _ => True

theorem readsIn_mono {A B : K → Prop} (hAB : ∀ k, A k → B k) :
    ∀ p : Prog K Γ σ, ReadsIn A p → ReadsIn B p
  | .push _ _, _ => trivial
  | .peek k _, h => hAB k h
  | .pop k _, h => hAB k h
  | .load _, _ => trivial
  | .seq p q, h => ⟨readsIn_mono hAB p h.1, readsIn_mono hAB q h.2⟩
  | .ite _ p q, h => ⟨readsIn_mono hAB p h.1, readsIn_mono hAB q h.2⟩
  | .loop _ p, h => readsIn_mono hAB p h
  | .fix b, h => readsIn_mono hAB b h
  | .recur _, _ => trivial

theorem readsIn_liftRegs {τ : Type} (l : Lens σ τ) (A : K → Prop) :
    ∀ p : Prog K Γ τ, ReadsIn A p → ReadsIn A (p.liftRegs l)
  | .push _ _, _ => trivial
  | .peek _ _, h => h
  | .pop _ _, h => h
  | .load _, _ => trivial
  | .seq p q, h => ⟨readsIn_liftRegs l A p h.1, readsIn_liftRegs l A q h.2⟩
  | .ite _ p q, h => ⟨readsIn_liftRegs l A p h.1, readsIn_liftRegs l A q h.2⟩
  | .loop _ p, h => readsIn_liftRegs l A p h
  | .fix b, h => readsIn_liftRegs l A b h
  | .recur _, _ => trivial

theorem readsIn_mapStk {K' α : Type} (ι : K → K') (B : K' → Prop) :
    ∀ p : Prog K (fun _ => α) σ, ReadsIn (fun k => B (ι k)) p → ReadsIn B (p.mapStk ι)
  | .push _ _, _ => trivial
  | .peek _ _, h => h
  | .pop _ _, h => h
  | .load _, _ => trivial
  | .seq p q, h => ⟨readsIn_mapStk ι B p h.1, readsIn_mapStk ι B q h.2⟩
  | .ite _ p q, h => ⟨readsIn_mapStk ι B p h.1, readsIn_mapStk ι B q h.2⟩
  | .loop _ p, h => readsIn_mapStk ι B p h
  | .fix b, h => readsIn_mapStk ι B b h
  | .recur _, _ => trivial

theorem readsIn_forEachProg {α : Type} (A : K → Prop) (f : α → Prog K Γ σ) :
    ∀ l : List α, (∀ a ∈ l, ReadsIn A (f a)) → ReadsIn A (forEachProg l f)
  | [], _ => trivial
  | a :: l, h => ⟨h a List.mem_cons_self,
      readsIn_forEachProg A f l (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

end Footprint

section Bridge

variable {K σ : Type} [DecidableEq K]

/-- **Safety from the read footprint.** If `p` and every program of the environment read only
unframed stacks, an `Eval` run of `p` is a boundary-safe run (same states, same cost). -/
theorem SafeEval.of_eval_readsIn {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {p : Prog K (fun _ => Sym) σ} {s s' : St K (fun _ => Sym) σ} {t : ℕ}
    (h : Eval ρ p s s' t) :
    ReadsIn (fun k => ¬ framed k) p → (∀ b ∈ ρ, ReadsIn (fun k => ¬ framed k) b) →
      SafeEval framed ρ p s s' t := by
  induction h with
  | push ρ k f v S => intro _ _; exact SafeEval.push ρ k f v S
  | peek ρ k f v S => intro hp _; exact SafeEval.peek ρ k f v S (fun hk => absurd hk hp)
  | pop ρ k f v S => intro hp _; exact SafeEval.pop ρ k f v S (fun hk => absurd hk hp)
  | load ρ f v S => intro _ _; exact SafeEval.load ρ f v S
  | seq _ _ ih₁ ih₂ => intro hp hρ; exact SafeEval.seq (ih₁ hp.1 hρ) (ih₂ hp.2 hρ)
  | ite_true hc _ ih => intro hp hρ; exact SafeEval.ite_true hc (ih hp.1 hρ)
  | ite_false hc _ ih => intro hp hρ; exact SafeEval.ite_false hc (ih hp.2 hρ)
  | loop_true hc _ _ ih₁ ih₂ =>
    intro hp hρ; exact SafeEval.loop_true hc (ih₁ hp hρ) (ih₂ hp hρ)
  | loop_false hc => intro _ _; exact SafeEval.loop_false hc
  | @fix ρ b s s' t _ ih =>
    intro hp hρ
    refine SafeEval.fix (ih hp ?_)
    intro b' hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact hp
    · exact hρ b' hb'
  | @recur ρ n b s s' t hb _ ih =>
    intro _ hρ
    exact SafeEval.recur hb (ih (hρ b (getElem?_mem' hb))
      (fun b' hb' => hρ b' (mem_of_mem_drop' hb')))

/-- Judgment-level bridge: a `RunsIn` fact of a program that reads only unframed stacks (with
such an environment) is a safe run with the same stacks, postcondition and cost. -/
theorem SafeRunsIn.of_runsIn_readsIn {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : RunsIn ρ P S S' Q T) (hP : ReadsIn (fun k => ¬ framed k) P)
    (hρ : ∀ b ∈ ρ, ReadsIn (fun k => ¬ framed k) b) : SafeRunsIn framed ρ P S S' Q T := by
  intro v
  obtain ⟨⟨w, U⟩, t, e, ⟨hU, hq⟩, ht⟩ := h ⟨v, S⟩ rfl
  change U = S' at hU
  subst hU
  exact ⟨w, t, SafeEval.of_eval_readsIn e hP hρ, hq, ht⟩

/-- Closed-kernel form: a closed program's `Runs` fact, if it reads only unframed stacks, is a
safe run in any environment. -/
theorem SafeRunsIn.of_runs_readsIn {framed : K → Prop} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : Runs P S S' Q T) (hc : P.Closed)
    (hP : ReadsIn (fun k => ¬ framed k) P) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framed ρ P S S' Q T :=
  SafeRunsIn.env_irrel hc
    (SafeRunsIn.of_runsIn_readsIn (RunsIn.iff_runs.mpr h) hP (fun _ hb => by simp at hb)) ρ

end Bridge

#assert_std_axioms readsIn_mono readsIn_liftRegs readsIn_mapStk readsIn_forEachProg
  SafeEval.of_eval_readsIn SafeRunsIn.of_runsIn_readsIn SafeRunsIn.of_runs_readsIn

end SubNLogN.Machine.Calculus
