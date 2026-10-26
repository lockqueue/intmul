/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Frame

/-!
# Framed procedure calculus (`Calculus/Safe.lean`): composition rules for boundary-safe runs

`SafeEval framed ρ p s s' t` and `SafeRunsIn framed ρ P S S' Q T` (`Calculus/Frame.lean`) are the
**certified** form of protected-tail execution: every `peek`/`pop` on a framed
stack happens while its visible content is non-empty, so the run never reads below the visible
content, and `SafeEval.append_tail` extends it to any tails with the same cost. This file proves
the composition rules of `SafeRunsIn`, mirroring the
`RunsIn` rules of `Calculus/Basic.lean`:
* `SafeRunsIn.seq`, `mono`, `congr`, `ite_true`, `ite_false`, the counted loop `seq_loop`;
* recursion: `recur0`, `recur`, `fix_of_body`, `fix` (measure on ghost data);
* forgetting: `SafeRunsIn.runsIn` (a safe run is a `RunsIn` fact), `SafeRunsIn.framedRunsIn`
  (`Frame.lean`).

Rules that need a transport of `SafeEval` along register lenses, stack renamings or environment
changes (`liftRegs`, `callInj`, closed components in another environment) are stated as
`…Stmt : Prop` here and proved in `Calculus/SafeTransport.lean`.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section SafeRules

variable {K σ : Type} [DecidableEq K] {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
  {P P' : Prog K (fun _ => Sym) σ} {S S₁ S₂ S₃ S' : K → List Sym} {Q Q₁ Q₂ Q' : σ → Prop}
  {T T₁ T₂ T' : ℕ}

namespace SafeRunsIn

/-- A safe run is a run (forgetting safety). -/
theorem runsIn (h : SafeRunsIn framed ρ P S S' Q T) : RunsIn ρ P S S' Q T := by
  intro s hs
  obtain ⟨v', t, e, hq, ht⟩ := h s.var
  refine ⟨⟨v', S'⟩, t, ?_, ⟨rfl, hq⟩, ht⟩
  obtain ⟨var, stk⟩ := s
  change stk = S at hs
  subst hs
  exact e.eval

theorem seq (h₁ : SafeRunsIn framed ρ P S₁ S₂ Q₁ T₁) (h₂ : SafeRunsIn framed ρ P' S₂ S₃ Q₂ T₂) :
    SafeRunsIn framed ρ (.seq P P') S₁ S₃ Q₂ (T₁ + T₂) := by
  intro v
  obtain ⟨v₁, t₁, e₁, -, ht₁⟩ := h₁ v
  obtain ⟨v₂, t₂, e₂, hq, ht₂⟩ := h₂ v₁
  exact ⟨v₂, t₁ + t₂, SafeEval.seq e₁ e₂, hq, by omega⟩

theorem mono (h : SafeRunsIn framed ρ P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') :
    SafeRunsIn framed ρ P S S' Q' T' := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨v', t, e, hQ _ hq, le_trans ht hT⟩

theorem congr (h : SafeRunsIn framed ρ P S S₁ Q T) (e : S₁ = S₂) (hT : T ≤ T') :
    SafeRunsIn framed ρ P S S₂ Q T' := by
  subst e
  exact mono h (fun _ h => h) hT

theorem ite_true {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : SafeRunsIn framed ρ P S₁ S₂ (fun v => c v = true) T₁)
    (h₂ : SafeRunsIn framed ρ Pt S₂ S₃ Q T₂) :
    SafeRunsIn framed ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) := by
  intro v
  obtain ⟨v₁, t₁, e₁, hc, ht₁⟩ := h₁ v
  obtain ⟨v₂, t₂, e₂, hq, ht₂⟩ := h₂ v₁
  exact ⟨v₂, t₁ + (t₂ + 1), SafeEval.seq e₁ (SafeEval.ite_true hc e₂), hq, by omega⟩

theorem ite_false {Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    (h₁ : SafeRunsIn framed ρ P S₁ S₂ (fun v => c v = false) T₁)
    (h₂ : SafeRunsIn framed ρ Pf S₂ S₃ Q T₂) :
    SafeRunsIn framed ρ (.seq P (.ite c Pt Pf)) S₁ S₃ Q (T₁ + (T₂ + 1)) := by
  intro v
  obtain ⟨v₁, t₁, e₁, hc, ht₁⟩ := h₁ v
  obtain ⟨v₂, t₂, e₂, hq, ht₂⟩ := h₂ v₁
  exact ⟨v₂, t₁ + (t₂ + 1), SafeEval.seq e₁ (SafeEval.ite_false hc e₂), hq, by omega⟩

theorem loop_aux {p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {B : ℕ → ℕ} {N : ℕ}
    (hstep : ∀ n, n < N →
      SafeRunsIn framed ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    ∀ n, n ≤ N → ∀ v : σ, c v = decide (0 < n) →
      ∃ v' t, SafeEval framed ρ (.loop c p) ⟨v, st n⟩ ⟨v', st 0⟩ t ∧ c v' = false ∧
        t ≤ loopCost B n
  | 0, _, v, hc => ⟨v, 1, SafeEval.loop_false (by simpa using hc), by simpa using hc,
      by simp [loopCost]⟩
  | n + 1, hn, v, hc => by
    have hc' : c v = true := by simpa using hc
    obtain ⟨v₁, t₁, e₁, hc₁, ht₁⟩ := hstep n (by omega) v
    obtain ⟨v₂, t₂, e₂, hq, ht₂⟩ := loop_aux hstep n (by omega) v₁ hc₁
    refine ⟨v₂, t₁ + t₂ + 1, SafeEval.loop_true hc' e₁ e₂, hq, ?_⟩
    simp only [loopCost]
    omega

/-- **Counted loop** (safe form of `RunsIn.seq_loop`). -/
theorem seq_loop {P₀ p : Prog K (fun _ => Sym) σ} {c : σ → Bool} {st : ℕ → K → List Sym}
    {B : ℕ → ℕ} {N T₀ : ℕ}
    (h₀ : SafeRunsIn framed ρ P₀ S (st N) (fun v => c v = decide (0 < N)) T₀)
    (hstep : ∀ n, n < N →
      SafeRunsIn framed ρ p (st (n + 1)) (st n) (fun v => c v = decide (0 < n)) (B n)) :
    SafeRunsIn framed ρ (.seq P₀ (.loop c p)) S (st 0) (fun v => c v = false)
      (T₀ + loopCost B N) := by
  intro v
  obtain ⟨v₁, t₁, e₁, hc₁, ht₁⟩ := h₀ v
  obtain ⟨v₂, t₂, e₂, hq, ht₂⟩ := loop_aux hstep N le_rfl v₁ hc₁
  exact ⟨v₂, t₁ + t₂, SafeEval.seq e₁ e₂, hq, by omega⟩

/-- A recursive call `recur 0` inside the body `b`. -/
theorem recur0 {b : Prog K (fun _ => Sym) σ} (h : SafeRunsIn framed (b :: ρ) b S S' Q T) :
    SafeRunsIn framed (b :: ρ) (.recur 0) S S' Q (T + 2) := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨v', t + 2, SafeEval.recur (n := 0) rfl e, hq, by omega⟩

/-- A call `recur n` to the body of the `n`-th enclosing `fix`. -/
theorem recur {n : ℕ} {b : Prog K (fun _ => Sym) σ} (hb : ρ[n]? = some b)
    (h : SafeRunsIn framed (ρ.drop n) b S S' Q T) :
    SafeRunsIn framed ρ (.recur n) S S' Q (T + 2) := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨v', t + 2, SafeEval.recur hb e, hq, by omega⟩

/-- `fix b` behaves as its body, plus `2`. -/
theorem fix_of_body {b : Prog K (fun _ => Sym) σ} (h : SafeRunsIn framed (b :: ρ) b S S' Q T) :
    SafeRunsIn framed ρ (.fix b) S S' Q (T + 2) := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨v', t + 2, SafeEval.fix e, hq, by omega⟩

/-- **The recursion rule for safe runs** (measure `μ` on ghost data). -/
theorem fix {X : Type} {b : Prog K (fun _ => Sym) σ} (μ : X → ℕ) {S S' : X → K → List Sym}
    {Q : X → σ → Prop} {T : X → ℕ}
    (h : ∀ x, (∀ y, μ y < μ x →
        SafeRunsIn framed (b :: ρ) (.recur 0) (S y) (S' y) (Q y) (T y + 2)) →
      SafeRunsIn framed (b :: ρ) b (S x) (S' x) (Q x) (T x)) :
    ∀ x, SafeRunsIn framed ρ (.fix b) (S x) (S' x) (Q x) (T x + 2) := by
  have key : ∀ n, ∀ x, μ x = n → SafeRunsIn framed (b :: ρ) b (S x) (S' x) (Q x) (T x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      exact h x (fun y hy => recur0 (ih (μ y) (hx ▸ hy) y rfl))
  intro x
  exact fix_of_body (key (μ x) x rfl)

end SafeRunsIn

end SafeRules

/-! ## Transport rule contracts (proved in `SafeTransport.lean`) -/

/-- [CONTRACT] Closed safe components in any environment. -/
def SafeEnvIrrelStmt : Prop :=
  ∀ {K σ : Type} [DecidableEq K] (framed : K → Prop) (P : Prog K (fun _ => Sym) σ)
    (S S' : K → List Sym) (Q : σ → Prop) (T : ℕ), P.Closed →
    SafeRunsIn framed [] P S S' Q T → ∀ ρ : List (Prog K (fun _ => Sym) σ),
      SafeRunsIn framed ρ P S S' Q T

/-- [CONTRACT] Safe runs through a register lens (closed component with its own registers). -/
def SafeLiftRegsStmt : Prop :=
  ∀ {K σ τ : Type} [DecidableEq K] (framed : K → Prop) (l : Lens σ τ)
    (p : Prog K (fun _ => Sym) τ) (S S' : K → List Sym) (Q : τ → Prop) (T : ℕ), p.Closed →
    SafeRunsIn framed [] p S S' Q T → ∀ ρ : List (Prog K (fun _ => Sym) σ),
      SafeRunsIn framed ρ (p.liftRegs l) S S' (fun v => Q (l.get v)) T

/-- [CONTRACT] A safe closed kernel on an injective sub-layout (`callInj`); framed big stacks in the
image must be framed in the kernel. -/
def SafeCallInjStmt : Prop :=
  ∀ {L K σ R : Type} [DecidableEq L] [DecidableEq K] (framedL : L → Prop) (framedK : K → Prop)
    (ι : L → K), Function.Injective ι → (∀ x, framedK (ι x) → framedL x) →
    ∀ (l : Lens σ R) (P : Prog L (fun _ => Sym) R) (B B' : K → List Sym) (Q : R → Prop) (T : ℕ),
      P.Closed → SafeRunsIn framedL [] P (B ∘ ι) (B' ∘ ι) Q T →
      (∀ k, (∀ x, ι x ≠ k) → B' k = B k) → ∀ ρ : List (Prog K (fun _ => Sym) σ),
        SafeRunsIn framedK ρ (callInj ι l P) B B' (fun _ => True) T

#assert_std_axioms SafeRunsIn.runsIn SafeRunsIn.seq SafeRunsIn.mono SafeRunsIn.congr
  SafeRunsIn.ite_true SafeRunsIn.ite_false SafeRunsIn.seq_loop SafeRunsIn.recur0 SafeRunsIn.recur
  SafeRunsIn.fix_of_body SafeRunsIn.fix

end SubNLogN.Machine.Calculus
