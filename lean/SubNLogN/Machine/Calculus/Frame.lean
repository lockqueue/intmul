/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Basic

/-!
# Framed procedure calculus, frames (`Calculus/Frame.lean`): protected tails and boundary-safe evaluation

A bare `Runs` fact does not survive appending content below the stacks: a program run on an empty
stack may pop (and so consume) whatever is appended below it. This file
provides both extensional protected-tail framing and operational boundary-safe evaluation.

* `appendTail S τ` (stack `k` holds `S k ++ τ k`) and its algebra (`appendTail_update`, …).
* **The protected-tail judgment** `FramedRunsIn G ρ P S S' Q T`: for *every* tail assignment `τ` in
  the tail class `G` (`∀ k, G k (τ k)`), `RunsIn ρ P (appendTail S τ) (appendTail S' τ) Q T`. The
  cost `T` and the register postcondition `Q` do not depend on the tails. The class
  `protTails framed` allows arbitrary tails on the stacks in `framed` and none elsewhere;
  `fun _ => FrameTail` is the mark discipline of `Calculus/Park.lean`. **Note
  (extensionality):** this judgment is *extensional* — correctness and cost for
  every admissible tail. It does **not** certify that the program never reads the tails (e.g.
  `peek k` on an empty visible prefix is correct for every tail). Access safety is `SafeEval` /
  `SafeRunsIn` below, which imply the judgment (`SafeRunsIn.framedRunsIn`), not conversely.
* **The frame lemma** `FramedRunsIn.runsIn` and its closure rules (`seq`, `ite_true`, `ite_false`,
  `seq_loop`, `liftRegs`, `of_callInj`, `recur0`, `fix_of_body`, `fix`, nesting `append`,
  `mono_class`), all with **exactly** the costs of the corresponding `RunsIn` rules (no overhead).
* **Boundary-safe evaluation** `SafeEval framed ρ p s s' t`: `Eval` with the extra side condition
  that every `peek`/`pop` of a stack in `framed` finds it non-empty. `SafeEval.append_tail` is the
  simulation theorem (same final registers, same cost, tails carried along), and
  `SafeRunsIn.framedRunsIn` turns a safe run into the protected-tail judgment.
* Adapter from tail-generic `Runs` facts of closed programs: `FramedRunsIn.of_runs`.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

variable {K σ : Type}

/-! ## Appending tails -/

/-- Stack `k` of `appendTail S τ` holds `S k` above the tail `τ k`. -/
def appendTail (S τ : K → List Sym) : K → List Sym := fun k => S k ++ τ k

@[simp] theorem appendTail_apply (S τ : K → List Sym) (k : K) :
    appendTail S τ k = S k ++ τ k := rfl

/-- Empty tails change nothing. -/
@[simp] theorem appendTail_nil (S : K → List Sym) : appendTail S (fun _ => []) = S := by
  funext k
  simp

/-- Appending twice is appending the concatenated tails. -/
theorem appendTail_assoc (S τ₀ τ : K → List Sym) :
    appendTail (appendTail S τ₀) τ = appendTail S (appendTail τ₀ τ) := by
  funext k
  simp

/-- Restriction along a stack map commutes with appending tails (definitionally). -/
theorem appendTail_comp {L : Type} (S τ : K → List Sym) (ι : L → K) :
    appendTail S τ ∘ ι = appendTail (S ∘ ι) (τ ∘ ι) := rfl

variable [DecidableEq K]

/-- Updating one stack, then appending tails. -/
theorem appendTail_update (S τ : K → List Sym) (k : K) (l : List Sym) :
    appendTail (Function.update S k l) τ = Function.update (appendTail S τ) k (l ++ τ k) := by
  funext j
  by_cases h : j = k
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-! ## Boundary-safe evaluation -/

/-- **Boundary-safe evaluation.** The constructors and costs are those of
`TMFw.Eval`; in addition every `peek k` and `pop k` with `framed k` requires the stack `k` to be
non-empty. Such a run never inspects what lies below the current content of a framed stack. -/
inductive SafeEval (framed : K → Prop) :
    List (Prog K (fun _ => Sym) σ) → Prog K (fun _ => Sym) σ → St K (fun _ => Sym) σ →
      St K (fun _ => Sym) σ → ℕ → Prop where
  | push (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Sym) (v : σ) (S : K → List Sym) :
      SafeEval framed ρ (.push k f) ⟨v, S⟩ ⟨v, Function.update S k (f v :: S k)⟩ 1
  | peek (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ) (v : σ)
      (S : K → List Sym) :
      (framed k → S k ≠ []) → SafeEval framed ρ (.peek k f) ⟨v, S⟩ ⟨f v (S k).head?, S⟩ 1
  | pop (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ) (v : σ)
      (S : K → List Sym) :
      (framed k → S k ≠ []) →
      SafeEval framed ρ (.pop k f) ⟨v, S⟩ ⟨f v (S k).head?, Function.update S k (S k).tail⟩ 1
  | load (ρ : List (Prog K (fun _ => Sym) σ)) (f : σ → σ) (v : σ) (S : K → List Sym) :
      SafeEval framed ρ (.load f) ⟨v, S⟩ ⟨f v, S⟩ 1
  | seq {ρ : List (Prog K (fun _ => Sym) σ)} {p q : Prog K (fun _ => Sym) σ}
      {s₁ s₂ s₃ : St K (fun _ => Sym) σ} {t₁ t₂ : ℕ} :
      SafeEval framed ρ p s₁ s₂ t₁ → SafeEval framed ρ q s₂ s₃ t₂ →
        SafeEval framed ρ (.seq p q) s₁ s₃ (t₁ + t₂)
  | ite_true {ρ : List (Prog K (fun _ => Sym) σ)} {c : σ → Bool} {p q : Prog K (fun _ => Sym) σ}
      {s s' : St K (fun _ => Sym) σ} {t : ℕ} :
      c s.var = true → SafeEval framed ρ p s s' t → SafeEval framed ρ (.ite c p q) s s' (t + 1)
  | ite_false {ρ : List (Prog K (fun _ => Sym) σ)} {c : σ → Bool} {p q : Prog K (fun _ => Sym) σ}
      {s s' : St K (fun _ => Sym) σ} {t : ℕ} :
      c s.var = false → SafeEval framed ρ q s s' t → SafeEval framed ρ (.ite c p q) s s' (t + 1)
  | loop_true {ρ : List (Prog K (fun _ => Sym) σ)} {c : σ → Bool} {p : Prog K (fun _ => Sym) σ}
      {s s₁ s₂ : St K (fun _ => Sym) σ} {t₁ t₂ : ℕ} :
      c s.var = true → SafeEval framed ρ p s s₁ t₁ → SafeEval framed ρ (.loop c p) s₁ s₂ t₂ →
        SafeEval framed ρ (.loop c p) s s₂ (t₁ + t₂ + 1)
  | loop_false {ρ : List (Prog K (fun _ => Sym) σ)} {c : σ → Bool} {p : Prog K (fun _ => Sym) σ}
      {s : St K (fun _ => Sym) σ} :
      c s.var = false → SafeEval framed ρ (.loop c p) s s 1
  | fix {ρ : List (Prog K (fun _ => Sym) σ)} {b : Prog K (fun _ => Sym) σ}
      {s s' : St K (fun _ => Sym) σ} {t : ℕ} :
      SafeEval framed (b :: ρ) b s s' t → SafeEval framed ρ (.fix b) s s' (t + 2)
  | recur {ρ : List (Prog K (fun _ => Sym) σ)} {n : ℕ} {b : Prog K (fun _ => Sym) σ}
      {s s' : St K (fun _ => Sym) σ} {t : ℕ} :
      ρ[n]? = some b → SafeEval framed (ρ.drop n) b s s' t → SafeEval framed ρ (.recur n) s s' (t + 2)

namespace SafeEval

variable {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
  {s s' : St K (fun _ => Sym) σ} {t : ℕ}

/-- A boundary-safe run is a run. -/
theorem eval (h : SafeEval framed ρ p s s' t) : Eval ρ p s s' t := by
  induction h with
  | push ρ k f v S => exact Eval.push ρ k f v S
  | peek ρ k f v S _ => exact Eval.peek ρ k f v S
  | pop ρ k f v S _ => exact Eval.pop ρ k f v S
  | load ρ f v S => exact Eval.load ρ f v S
  | seq _ _ ih₁ ih₂ => exact Eval.seq ih₁ ih₂
  | ite_true hc _ ih => exact Eval.ite_true hc ih
  | ite_false hc _ ih => exact Eval.ite_false hc ih
  | loop_true hc _ _ ih₁ ih₂ => exact Eval.loop_true hc ih₁ ih₂
  | loop_false hc => exact Eval.loop_false hc
  | fix _ ih => exact Eval.fix ih
  | recur hb _ ih => exact Eval.recur hb ih

/-- With nothing framed, every run is boundary-safe (`SafeEval` strengthens `Eval` only at framed
stacks). -/
theorem of_eval (h : Eval ρ p s s' t) : SafeEval (fun _ => False) ρ p s s' t := by
  induction h with
  | push ρ k f v S => exact SafeEval.push ρ k f v S
  | peek ρ k f v S => exact SafeEval.peek ρ k f v S (fun h => h.elim)
  | pop ρ k f v S => exact SafeEval.pop ρ k f v S (fun h => h.elim)
  | load ρ f v S => exact SafeEval.load ρ f v S
  | seq _ _ ih₁ ih₂ => exact SafeEval.seq ih₁ ih₂
  | ite_true hc _ ih => exact SafeEval.ite_true hc ih
  | ite_false hc _ ih => exact SafeEval.ite_false hc ih
  | loop_true hc _ _ ih₁ ih₂ => exact SafeEval.loop_true hc ih₁ ih₂
  | loop_false hc => exact SafeEval.loop_false hc
  | fix _ ih => exact SafeEval.fix ih
  | recur hb _ ih => exact SafeEval.recur hb ih

/-- Safety for fewer framed stacks. -/
theorem mono_framed {framed' : K → Prop} (h : SafeEval framed ρ p s s' t)
    (hf : ∀ k, framed' k → framed k) : SafeEval framed' ρ p s s' t := by
  induction h with
  | push ρ k f v S => exact SafeEval.push ρ k f v S
  | peek ρ k f v S hS => exact SafeEval.peek ρ k f v S (fun h => hS (hf k h))
  | pop ρ k f v S hS => exact SafeEval.pop ρ k f v S (fun h => hS (hf k h))
  | load ρ f v S => exact SafeEval.load ρ f v S
  | seq _ _ ih₁ ih₂ => exact SafeEval.seq ih₁ ih₂
  | ite_true hc _ ih => exact SafeEval.ite_true hc ih
  | ite_false hc _ ih => exact SafeEval.ite_false hc ih
  | loop_true hc _ _ ih₁ ih₂ => exact SafeEval.loop_true hc ih₁ ih₂
  | loop_false hc => exact SafeEval.loop_false hc
  | fix _ ih => exact SafeEval.fix ih
  | recur hb _ ih => exact SafeEval.recur hb ih

/-- **The simulation theorem for boundary-safe runs.** A boundary-safe run, with
arbitrary tails appended below the framed stacks (and nothing appended elsewhere), is a run from
the extended state to the extended final state with the same final registers and the **same
cost**. -/
theorem append_tail (h : SafeEval framed ρ p s s' t) (τ : K → List Sym)
    (hτ : ∀ k, ¬ framed k → τ k = []) :
    Eval ρ p ⟨s.var, appendTail s.stk τ⟩ ⟨s'.var, appendTail s'.stk τ⟩ t := by
  induction h with
  | push ρ k f v S =>
    refine Eval.of_eq (Eval.push ρ k f v (appendTail S τ)) ?_ rfl
    show (⟨v, _⟩ : St K (fun _ => Sym) σ) = ⟨v, _⟩
    rw [appendTail_update]
    rfl
  | peek ρ k f v S hS =>
    have key : (S k ++ τ k).head? = (S k).head? := by
      by_cases hk : framed k
      · obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (hS hk)
        simp [hl]
      · rw [hτ k hk, List.append_nil]
    refine Eval.of_eq (Eval.peek ρ k f v (appendTail S τ)) ?_ rfl
    show (⟨f v (S k ++ τ k).head?, _⟩ : St K (fun _ => Sym) σ) = ⟨f v (S k).head?, _⟩
    rw [key]
  | pop ρ k f v S hS =>
    have key : (S k ++ τ k).head? = (S k).head? ∧ (S k ++ τ k).tail = (S k).tail ++ τ k := by
      by_cases hk : framed k
      · obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (hS hk)
        simp [hl]
      · rw [hτ k hk, List.append_nil, List.append_nil]
        exact ⟨rfl, rfl⟩
    refine Eval.of_eq (Eval.pop ρ k f v (appendTail S τ)) ?_ rfl
    show (⟨f v (S k ++ τ k).head?, Function.update (appendTail S τ) k (S k ++ τ k).tail⟩ :
      St K (fun _ => Sym) σ) = ⟨f v (S k).head?, appendTail (Function.update S k (S k).tail) τ⟩
    rw [key.1, key.2, appendTail_update]
  | load ρ f v S => exact Eval.load ρ f v (appendTail S τ)
  | seq _ _ ih₁ ih₂ => exact Eval.seq ih₁ ih₂
  | ite_true hc _ ih => exact Eval.ite_true hc ih
  | ite_false hc _ ih => exact Eval.ite_false hc ih
  | loop_true hc _ _ ih₁ ih₂ => exact Eval.loop_true hc ih₁ ih₂
  | loop_false hc => exact Eval.loop_false hc
  | fix _ ih => exact Eval.fix ih
  | recur hb _ ih => exact Eval.recur hb ih

end SafeEval

/-! ## The protected-tail judgment -/

/-- **Safe runs** (boundary-safe execution in a procedure environment `ρ`): from stacks `S` and
every register value, a boundary-safe run (with respect to `framed`) reaches stacks `S'` with
register in `Q`, within `T` steps. -/
def SafeRunsIn (framed : K → Prop) (ρ : List (Prog K (fun _ => Sym) σ))
    (P : Prog K (fun _ => Sym) σ) (S S' : K → List Sym) (Q : σ → Prop) (T : ℕ) : Prop :=
  ∀ v : σ, ∃ v' t, SafeEval framed ρ P ⟨v, S⟩ ⟨v', S'⟩ t ∧ Q v' ∧ t ≤ T

/-- The tail class of `framed`: any tail below a framed stack, none below the others. -/
def protTails (framed : K → Prop) : K → List Sym → Prop := fun k tl => ¬ framed k → tl = []

/-- **The protected-tail judgment** `FramedRunsIn G ρ P S S' Q T`: for every tail assignment `τ`
in the class `G` (`∀ k, G k (τ k)`), `P` runs in the environment `ρ` from `appendTail S τ` to
`appendTail S' τ` with register in `Q`, within `T` steps. This is an extensional statement: it
does not say that the tails are never read; for operational access safety use `SafeRunsIn`. -/
def FramedRunsIn (G : K → List Sym → Prop) (ρ : List (Prog K (fun _ => Sym) σ))
    (P : Prog K (fun _ => Sym) σ) (S S' : K → List Sym) (Q : σ → Prop) (T : ℕ) : Prop :=
  ∀ τ : K → List Sym, (∀ k, G k (τ k)) → RunsIn ρ P (appendTail S τ) (appendTail S' τ) Q T

/-- **Safe runs are framed** (at the judgment level): a safe run gives the
protected-tail judgment for the class `protTails framed`. -/
theorem SafeRunsIn.framedRunsIn {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : SafeRunsIn framed ρ P S S' Q T) : FramedRunsIn (protTails framed) ρ P S S' Q T := by
  intro τ hτ s hs
  obtain ⟨v', t, e, hq, ht⟩ := h s.var
  refine ⟨⟨v', appendTail S' τ⟩, t, ?_, ⟨rfl, hq⟩, ht⟩
  obtain ⟨var, stk⟩ := s
  change stk = appendTail S τ at hs
  subst hs
  exact e.append_tail τ hτ

namespace FramedRunsIn

variable {G G' : K → List Sym → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
  {P P' : Prog K (fun _ => Sym) σ} {S S₁ S₂ S₃ S' : K → List Sym} {Q Q₁ Q₂ Q' : σ → Prop}
  {T T₁ T₂ T₃ T' : ℕ}

/-- **The frame lemma**: the judgment, at one admissible tail assignment. -/
theorem runsIn (h : FramedRunsIn G ρ P S S' Q T) (τ : K → List Sym) (hτ : ∀ k, G k (τ k)) :
    RunsIn ρ P (appendTail S τ) (appendTail S' τ) Q T :=
  h τ hτ

/-- **The frame lemma, `framed` form**: arbitrary tails below the framed stacks. -/
theorem runsIn_prot {framed : K → Prop} (h : FramedRunsIn (protTails framed) ρ P S S' Q T)
    (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    RunsIn ρ P (appendTail S τ) (appendTail S' τ) Q T :=
  h τ hτ

/-- With empty tails (when admissible) the judgment gives the plain `RunsIn` fact. -/
theorem runsIn_self (h : FramedRunsIn G ρ P S S' Q T) (hG : ∀ k, G k []) :
    RunsIn ρ P S S' Q T := by
  simpa using h (fun _ => []) hG

/-- A smaller tail class. -/
theorem mono_class (h : FramedRunsIn G ρ P S S' Q T) (hG : ∀ k tl, G' k tl → G k tl) :
    FramedRunsIn G' ρ P S S' Q T :=
  fun τ hτ => h τ fun k => hG k _ (hτ k)

/-- **Nesting**: prepend fixed tails `τ₀` (e.g. a parent's parked data) to the admissible
tails. -/
theorem append (h : FramedRunsIn G ρ P S S' Q T) (τ₀ : K → List Sym)
    (hG : ∀ k tl, G' k tl → G k (τ₀ k ++ tl)) :
    FramedRunsIn G' ρ P (appendTail S τ₀) (appendTail S' τ₀) Q T := by
  intro τ hτ
  rw [appendTail_assoc, appendTail_assoc]
  exact h (appendTail τ₀ τ) fun k => hG k _ (hτ k)

theorem seq (h₁ : FramedRunsIn G ρ P S₁ S₂ Q₁ T₁) (h₂ : FramedRunsIn G ρ P' S₂ S₃ Q₂ T₂) :
    FramedRunsIn G ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) :=
  fun τ hτ => RunsIn.seq (h₁ τ hτ) (h₂ τ hτ)

theorem mono (h : FramedRunsIn G ρ P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') :
    FramedRunsIn G ρ P S S' Q' T' :=
  fun τ hτ => RunsIn.mono (h τ hτ) hQ hT

/-- Rewrite the final stacks and weaken the cost. -/
theorem congr (h : FramedRunsIn G ρ P S S₁ Q T) (e : S₁ = S₂) (hT : T ≤ T') :
    FramedRunsIn G ρ P S S₂ Q T' := by
  subst e
  exact mono h (fun _ h => h) hT

theorem ite_true {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : FramedRunsIn G ρ P S₁ S₂ (fun v => c v = true) T₁)
    (h₂ : FramedRunsIn G ρ Pt S₂ S₃ Q T₂) :
    FramedRunsIn G ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) :=
  fun τ hτ => RunsIn.ite_true (h₁ τ hτ) (h₂ τ hτ)

theorem ite_false {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : FramedRunsIn G ρ P S₁ S₂ (fun v => c v = false) T₁)
    (h₂ : FramedRunsIn G ρ Pf S₂ S₃ Q T₂) :
    FramedRunsIn G ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) :=
  fun τ hτ => RunsIn.ite_false (h₁ τ hτ) (h₂ τ hτ)

/-- **Branch on a known flag**: the test leaves the flag equal to `b`; cost of the taken branch. -/
theorem seq_ite {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool} (b : Bool)
    (h₁ : FramedRunsIn G ρ P S₁ S₂ (fun v => c v = b) T₁)
    (ht : b = true → FramedRunsIn G ρ Pt S₂ S₃ Q T₂)
    (hf : b = false → FramedRunsIn G ρ Pf S₂ S₃ Q T₃) :
    FramedRunsIn G ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + ((if b then T₂ else T₃) + 1)) := by
  cases b
  · exact ite_false h₁ (hf rfl)
  · exact ite_true h₁ (ht rfl)

/-- **Counted loop** (`RunsIn.seq_loop` with protected tails; same cost
`T₀ + loopCost B N`). -/
theorem seq_loop {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {B : ℕ → ℕ} {N T₀ : ℕ}
    (h₀ : FramedRunsIn G ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N →
      FramedRunsIn G ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    FramedRunsIn G ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + loopCost B N) :=
  fun τ hτ => RunsIn.seq_loop (st := fun n => appendTail (st n) τ) (h₀ τ hτ)
    (fun n hn => hstep n hn τ hτ)

/-- A component through a register lens (the environment is lifted along). -/
theorem liftRegs {ν : Type} (l : Lens σ ν) {ρ' : List (Prog K (fun _ => Sym) ν)}
    {p : Prog K (fun _ => Sym) ν} {Q : ν → Prop} (h : FramedRunsIn G ρ' p S S' Q T) :
    FramedRunsIn G (ρ'.map (Prog.liftRegs l)) (p.liftRegs l) S S' (fun v => Q (l.get v)) T :=
  fun τ hτ => RunsIn.liftRegs l (h τ hτ)

/-- **Adapter**: a closed program with a `Runs` fact for every admissible tail assignment satisfies
the judgment in every environment. (Extensional, as the judgment: it yields no access-safety
certificate.) -/
theorem of_runs (hc : P.Closed)
    (h : ∀ τ : K → List Sym, (∀ k, G k (τ k)) →
      Runs P (appendTail S τ) (appendTail S' τ) Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) : FramedRunsIn G ρ P S S' Q T :=
  fun τ hτ => RunsIn.of_runs (h τ hτ) hc ρ

/-- A closed program's judgment does not depend on the environment. -/
theorem env_irrel (h : FramedRunsIn G ρ P S S' Q T) (hc : P.Closed)
    (ρ' : List (Prog K (fun _ => Sym) σ)) : FramedRunsIn G ρ' P S S' Q T :=
  fun τ hτ => RunsIn.of_runs (RunsIn.to_runs (h τ hτ) hc) hc ρ'

/-- **Call along an injective sub-layout** (`callInj`) with protected tails: the component's tail
class is pulled back along `ι`; stacks outside the image may carry any tail. -/
theorem of_callInj {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {GL : L → List Sym → Prop}
    {B B' : K → List Sym} {Q : R → Prop}
    (hP : FramedRunsIn GL [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    FramedRunsIn (fun k tl => ∀ x, ι x = k → GL x tl) ρ (callInj ι l P) B B' (fun _ => True) T := by
  intro τ hτ
  refine RunsIn.of_callInj hι l hcl (B := appendTail B τ) (B' := appendTail B' τ) (Q := Q) ?_ ?_ ρ
  · exact hP (τ ∘ ι) fun x => hτ (ι x) x rfl
  · intro k hk
    simp [hout k hk]

/-! ### Recursion with protected tails -/

/-- A recursive call `recur 0` behaves as the body, plus `2`. -/
theorem recur0 {b : Prog K (fun _ => Sym) σ} (h : FramedRunsIn G (b :: ρ) b S S' Q T) :
    FramedRunsIn G (b :: ρ) (.recur 0) S S' Q (T + 2) :=
  fun τ hτ => RunsIn.recur0 (h τ hτ)

/-- `fix b` behaves as its body (in environment `b :: ρ`), plus `2`. -/
theorem fix_of_body {b : Prog K (fun _ => Sym) σ} (h : FramedRunsIn G (b :: ρ) b S S' Q T) :
    FramedRunsIn G ρ (.fix b) S S' Q (T + 2) :=
  fun τ hτ => RunsIn.fix_of_body (h τ hτ)

/-- **The recursion rule with protected tails.** As `RunsIn.fix`, for the protected-tail
judgment: the induction hypothesis on the recursive call holds for **every** admissible tail, so a
parent may call its children with its own parked data in their tails. -/
theorem fix {X : Type} {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym}
    {Q : X → σ → Prop} {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x → FramedRunsIn G (b :: ρ) (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      FramedRunsIn G (b :: ρ) b (S x) (S' x) (Q x) (T x)) :
    ∀ x, FramedRunsIn G ρ (.fix b) (S x) (S' x) (Q x) (T x + 2) := by
  intro x τ hτ
  let Y := {q : X × (K → List Sym) // ∀ k, G k (q.2 k)}
  have key := RunsIn.fix (ρ := ρ) (b := b) (X := Y) (fun q => μ q.1.1)
    (S := fun q => appendTail (S q.1.1) q.1.2) (S' := fun q => appendTail (S' q.1.1) q.1.2)
    (Q := fun q => Q q.1.1) (T := fun q => T q.1.1)
    (fun q ih => h q.1.1 (fun y hy τ' hτ' => ih ⟨(y, τ'), hτ'⟩ hy) q.1.2 q.2)
  exact key ⟨(x, τ), hτ⟩

end FramedRunsIn

#assert_std_axioms appendTail_nil appendTail_assoc appendTail_update SafeEval.eval
  SafeEval.of_eval SafeEval.mono_framed SafeEval.append_tail SafeRunsIn.framedRunsIn FramedRunsIn.runsIn_self FramedRunsIn.append
  FramedRunsIn.seq FramedRunsIn.seq_ite FramedRunsIn.seq_loop FramedRunsIn.liftRegs
  FramedRunsIn.of_runs FramedRunsIn.env_irrel FramedRunsIn.of_callInj FramedRunsIn.recur0
  FramedRunsIn.fix_of_body FramedRunsIn.fix

end SubNLogN.Machine.Calculus
