/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Layout
import WP.W0m.Kit

/-!
# Framed procedure calculus, layer 1 (`Calculus/Basic.lean`): `RunsIn`, frame tails, recursion

The machine model's procedures are `Prog.fix b` (define body `b`, call it) and `Prog.recur n` (call
the body of the `n`-th enclosing `fix`); `Eval ρ` carries the bodies of the enclosing `fix`es in the
environment `ρ` (`IntMulTM/Framework/Eval.lean`). The contract form `Runs` of the machine contracts
(`Contracts/Machine/Common.lean`) fixes the empty environment. This file lifts `Runs` to an
arbitrary environment and proves the rules needed to specify and verify **recursive** kernels.

* `RunsIn ρ P S S' Q T`: from every state with stacks exactly `S` (any register), `P` run in
  environment `ρ` reaches stacks exactly `S'` with register in `Q`, within `T` steps.
  `RunsIn [] = Runs` (`RunsIn.iff_runs`, by `Iff.rfl`).
* Composition: `RunsIn.seq`, `mono`, `congr`, `ite_true`, `ite_false`, the counted loop
  `seq_loop`, register lenses `liftRegs`.
* Closed components (every proved kernel, `callInj` embeddings, library macros): `RunsIn.of_runs`,
  `of_runs_liftRegs`, `of_callInj` transport a `Runs` fact to **any** environment, so they can be used
  inside a procedure body.
* Recursion: `RunsIn.recur0`, `fix_of_body`, and the induction rule `RunsIn.fix` (well-founded
  measure on ghost data). A spec family indexed by ghost data `x` — which may include **all** stack
  tails — is proved for `fix b` by proving the body under the hypothesis that `recur 0` meets the
  spec at every `y` with smaller measure. `runs_fix` is the closed (empty-environment) form.
* Frame tails: `FrameTail tl` (empty, or starts with `mark`) and `MarkFree` blocks, the vocabulary
  of the protected-tail discipline (`Calculus/Frame.lean`, `Calculus/Park.lean`).
* `unitKernel_iff`: for `Par := Unit` contracts, the witness can be chosen before the runtime
  data.

Paper: the nested fixed-tape recursion of Proposition A.7 (`prop:transfer11`),
Section A.2 (`sec:transfer-power`).
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Frame tails and mark-free blocks -/

/-- **A frame tail**: the content below the current frame is empty or starts with `mark`.
A spec quantified over all frame tails proves that the tail is restored at the end. When its
budget does not depend on the tail, it also proves a tail-independent **upper bound** on the cost.
It does **not** prove equal actual running times or equal final registers for different tails. Nor
does it prove that the program never reads the tail: a program may pop and restore the `mark`.
Operational boundary safety is the separate judgment `SafeEval` of
`Calculus/Frame.lean`. -/
def FrameTail (tl : List Sym) : Prop := tl = [] ∨ tl.head? = some Sym.mark

theorem FrameTail.nil : FrameTail [] := Or.inl rfl

theorem FrameTail.mark (l : List Sym) : FrameTail (Sym.mark :: l) := Or.inr rfl

/-- A frame tail is a valid number terminator. -/
theorem FrameTail.termOK {tl : List Sym} (h : FrameTail tl) : TermOK tl := by
  rcases h with rfl | h
  · exact TermOK.nil
  · intro d hd
    rw [h] at hd
    cases hd
    rfl

/-- A block with no `mark` symbol. -/
def MarkFree (l : List Sym) : Prop := ∀ d ∈ l, d ≠ Sym.mark

theorem MarkFree.nil : MarkFree [] := fun _ h => absurd h List.not_mem_nil

theorem MarkFree.reverse {l : List Sym} (h : MarkFree l) : MarkFree l.reverse :=
  fun d hd => h d (List.mem_reverse.mp hd)

theorem MarkFree.append {l l' : List Sym} (h : MarkFree l) (h' : MarkFree l') :
    MarkFree (l ++ l') := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact h d hd
  · exact h' d hd

/-- Bit blocks are mark-free. -/
theorem MarkFree.bits (es : List Bool) : MarkFree (es.map Sym.bit) := by
  intro d hd
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hd
  exact fun h => Sym.noConfusion h

/-! ## `RunsIn`: `Runs` in a procedure environment -/

section RunsIn

variable {K σ : Type} [DecidableEq K]

/-- **`RunsIn ρ P S S' Q T`**: from every state whose stacks are exactly `S` (any register value),
`P`, evaluated in the procedure environment `ρ`, reaches a state whose stacks are exactly `S'` and
whose register satisfies `Q`, within `T` steps. -/
def RunsIn (ρ : List (Prog K (fun _ => Sym) σ)) (P : Prog K (fun _ => Sym) σ)
    (S S' : K → List Sym) (Q : σ → Prop) (T : ℕ) : Prop :=
  Triple ρ (fun s => s.stk = S) P (fun s => s.stk = S' ∧ Q s.var) T

namespace RunsIn

variable {ρ : List (Prog K (fun _ => Sym) σ)} {P P' : Prog K (fun _ => Sym) σ}
  {S S₁ S₂ S₃ S' : K → List Sym} {Q Q₁ Q₂ Q' : σ → Prop} {T T₁ T₂ T' : ℕ}

/-- In the empty environment, `RunsIn` is `Runs`. -/
theorem iff_runs : RunsIn [] P S S' Q T ↔ Runs P S S' Q T := Iff.rfl

/-- A closed program's `Runs` holds in every environment. -/
theorem of_runs (h : Runs P S S' Q T) (hc : P.Closed) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ P S S' Q T :=
  Triple.env_irrel h hc ρ

/-- A closed program's `RunsIn` in any environment gives its `Runs`. -/
theorem to_runs (h : RunsIn ρ P S S' Q T) (hc : P.Closed) : Runs P S S' Q T :=
  Triple.env_irrel h hc []

theorem seq (h₁ : RunsIn ρ P S₁ S₂ Q₁ T₁) (h₂ : RunsIn ρ P' S₂ S₃ Q₂ T₂) :
    RunsIn ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) :=
  Triple.seq (Triple.post h₁ fun _ hs => hs.1) h₂

theorem mono (h : RunsIn ρ P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') :
    RunsIn ρ P S S' Q' T' :=
  Triple.cost_mono (Triple.post h fun _ hs => ⟨hs.1, hQ _ hs.2⟩) hT

/-- Rewrite the final stacks and weaken the cost. -/
theorem congr (h : RunsIn ρ P S S₁ Q T) (e : S₁ = S₂) (hT : T ≤ T') : RunsIn ρ P S S₂ Q T' := by
  subst e
  exact mono h (fun _ h => h) hT

theorem ite_true {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : RunsIn ρ P S₁ S₂ (fun v => c v = true) T₁) (h₂ : RunsIn ρ Pt S₂ S₃ Q T₂) :
    RunsIn ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) := by
  intro s hs
  obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc⟩, ht₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := h₂ s₁ hs₁
  exact ⟨s₂, t₁ + (t₂ + 1), Eval.seq e₁ (Eval.ite_true hc e₂), hq, by omega⟩

theorem ite_false {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : RunsIn ρ P S₁ S₂ (fun v => c v = false) T₁) (h₂ : RunsIn ρ Pf S₂ S₃ Q T₂) :
    RunsIn ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) := by
  intro s hs
  obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc⟩, ht₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := h₂ s₁ hs₁
  exact ⟨s₂, t₁ + (t₂ + 1), Eval.seq e₁ (Eval.ite_false hc e₂), hq, by omega⟩

/-- The loop from a state with stacks `st n` whose register says whether `n > 0`. -/
theorem loop_aux {p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {B : ℕ → ℕ} {N : ℕ}
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    ∀ n, n ≤ N → ∀ s : St K (fun _ => Sym) σ, s.stk = st n → c s.var = decide (0 < n) →
      ∃ s' t, Eval ρ (.loop c p) s s' t ∧ (s'.stk = st 0 ∧ c s'.var = false) ∧
        t ≤ loopCost B n
  | 0, _, s, hs, hc => ⟨s, 1, Eval.loop_false (by simpa using hc), ⟨hs, by simpa using hc⟩,
      by simp [loopCost]⟩
  | n + 1, hn, s, hs, hc => by
    have hc' : c s.var = true := by simpa using hc
    obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc₁⟩, ht₁⟩ := hstep n (by omega) s hs
    obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := loop_aux hstep n (by omega) s₁ hs₁ hc₁
    refine ⟨s₂, t₁ + t₂ + 1, Eval.loop_true hc' e₁ e₂, hq, ?_⟩
    simp only [loopCost]
    omega

/-- **Counted loop.** `P₀` sets up `st N` and the loop flag (`c = true` iff iterations remain);
the body takes `st (n + 1)` to `st n` and updates the flag. The loop ends in `st 0` with the flag
off, within `T₀ + loopCost B N` (`loopCost B N = Σ_{n<N} (B n + 1) + 1`). -/
theorem seq_loop {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {B : ℕ → ℕ} {N T₀ : ℕ}
    (h₀ : RunsIn ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N → RunsIn ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    RunsIn ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false) (T₀ + loopCost B N) := by
  intro s hs
  obtain ⟨s₁, t₁, e₁, ⟨hs₁, hc₁⟩, ht₁⟩ := h₀ s hs
  obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := loop_aux hstep N le_rfl s₁ hs₁ hc₁
  exact ⟨s₂, t₁ + t₂, Eval.seq e₁ e₂, hq, by omega⟩

/-- A component through a register lens (the environment is lifted along). -/
theorem liftRegs {τ : Type} (l : Lens σ τ) {ρ' : List (Prog K (fun _ => Sym) τ)}
    {p : Prog K (fun _ => Sym) τ} {Q : τ → Prop} (h : RunsIn ρ' p S S' Q T) :
    RunsIn (ρ'.map (Prog.liftRegs l)) (p.liftRegs l) S S' (fun v => Q (l.get v)) T := by
  have h2 := Triple.liftRegs l h (fun _ => True) (fun _ _ _ => trivial)
  intro s hs
  obtain ⟨s', t, e, ⟨⟨hs1, hq⟩, -⟩, ht⟩ := h2 s ⟨hs, trivial⟩
  exact ⟨s', t, e, ⟨hs1, hq⟩, ht⟩

/-- **A closed component with its own registers**, lifted through a lens, in any environment. -/
theorem of_runs_liftRegs {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ} {Q : τ → Prop}
    (h : Runs p S S' Q T) (hc : p.Closed) (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (p.liftRegs l) S S' (fun v => Q (l.get v)) T :=
  of_runs (WP.W0m.runs_liftRegs l h) (WP.W9comp.closed_liftRegs l hc) ρ

/-- **A closed kernel on an injective sub-layout** (`callInj`), in any environment. -/
theorem of_callInj {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {B B' : K → List Sym}
    {Q : R → Prop} (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    RunsIn ρ (callInj ι l P) B B' (fun _ => True) T :=
  of_runs (runs_callInj hι l hP hout) (closed_callInj ι l hcl) ρ

/-! ### Recursion -/

/-- **A recursive call** `recur 0` inside the body `b` (environment `b :: ρ`) behaves as `b`, plus
the call/return cost `2`. -/
theorem recur0 {b : Prog K (fun _ => Sym) σ} (h : RunsIn (b :: ρ) b S S' Q T) :
    RunsIn (b :: ρ) (.recur 0) S S' Q (T + 2) :=
  Triple.recur_of_body (n := 0) rfl h

/-- `fix b` behaves as its body (run in environment `b :: ρ`), plus `2`. -/
theorem fix_of_body {b : Prog K (fun _ => Sym) σ} (h : RunsIn (b :: ρ) b S S' Q T) :
    RunsIn ρ (.fix b) S S' Q (T + 2) :=
  Triple.fix_of_body h

/-- **The recursion rule.** Let `x` range over ghost data (it may contain all stack tails), with a
measure `μ`. If the body `b` meets the spec at `x` whenever the recursive call `recur 0` meets it
at every `y` of smaller measure, then `fix b` meets the spec at every `x`. -/
theorem fix {X : Type} {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym}
    {Q : X → σ → Prop} {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x → RunsIn (b :: ρ) (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      RunsIn (b :: ρ) b (S x) (S' x) (Q x) (T x)) :
    ∀ x, RunsIn ρ (.fix b) (S x) (S' x) (Q x) (T x + 2) :=
  Triple.fix (P := fun x s => s.stk = S x) (Q := fun x s => s.stk = S' x ∧ Q x s.var) μ h

end RunsIn

/-- **The recursion rule, closed form**: the conclusion is a family of ordinary `Runs` facts. -/
theorem runs_fix {X : Type} {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym}
    {Q : X → σ → Prop} {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x → RunsIn [b] (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      RunsIn [b] b (S x) (S' x) (Q x) (T x)) :
    ∀ x, Runs (.fix b) (S x) (S' x) (Q x) (T x + 2) :=
  RunsIn.fix (ρ := []) μ h

end RunsIn

#assert_std_axioms FrameTail.termOK MarkFree.reverse MarkFree.append MarkFree.bits RunsIn.of_runs
  RunsIn.to_runs RunsIn.seq RunsIn.mono RunsIn.congr RunsIn.ite_true RunsIn.ite_false
  RunsIn.seq_loop RunsIn.liftRegs RunsIn.of_runs_liftRegs RunsIn.of_callInj RunsIn.recur0
  RunsIn.fix_of_body RunsIn.fix runs_fix

/-! ## Uniform witnesses for `Unit`-parameter contracts -/

universe u

/-- **Unit witness extraction.** This is a purely logical fact. When the
contract parameter is `Unit`, a pointwise witness is a single witness chosen before any runtime
data. At export, `a` must bundle the whole implementation choice: scratch count, extra-stack type
and its instances, register type, and the closed program. Runtime data are quantified inside
`spec C () a`. The lemma does not make a contract with a runtime-dependent parameter uniform. -/
theorem unitKernel_iff (A : ℕ → Type u) (spec : (C : ℕ) → Unit → A C → Prop) :
    (∃ C : ℕ, ∀ p : Unit, ∃ a : A C, spec C p a) ↔ ∃ C : ℕ, ∃ a : A C, ∀ p : Unit, spec C p a := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨a, ha⟩ := hC ()
    refine ⟨C, a, ?_⟩
    intro p
    cases p
    exact ha
  · rintro ⟨C, a, ha⟩
    exact ⟨C, fun p => ⟨a, ha p⟩⟩

#assert_std_axioms unitKernel_iff

end SubNLogN.Machine.Calculus
