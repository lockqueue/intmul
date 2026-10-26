import IntMulTM.Framework.Eval

/-!
# IntMulTM.Framework.Triple — total-correctness triples with cost

`Triple ρ P p Q T` : from every state satisfying `P`, `p` (in environment `ρ`) terminates in a
state satisfying `Q` with cost at most `T`. Logical ("ghost") variables are bound *outside* the
triple, so `T` is a number (it may depend on ghost variables, not on the state).

Why this form (and not a functional `DetSpec ρ p dom next cost`):
* `seq` composes with no side condition and costs simply add (`Triple.seq`), because the cost is
  not a function of an existential intermediate state;
* costs are upper bounds, so data-dependent or amortised costs need no exact closed form;
* postconditions may be partial, so footprint/lens/renaming frame rules compose with them;
* exactness is still available: `Triple.exact` turns an exact `Eval` fact into a triple, and
  determinism (`Eval.det`) gives `Triple.and` and the lower-bound lemma `Triple.cost_ge` (used by
  mutation tests).
-/

namespace TMFw

open Turing

section Triple

variable {K : Type} {Γ : K → Type} {σ : Type} [DecidableEq K]

/-- Total correctness with cost. -/
def Triple (ρ : List (Prog K Γ σ)) (P : St K Γ σ → Prop) (p : Prog K Γ σ)
    (Q : St K Γ σ → Prop) (T : ℕ) : Prop :=
  ∀ s, P s → ∃ s' t, Eval ρ p s s' t ∧ Q s' ∧ t ≤ T

/-- Cost of a counted loop with `N` iterations; `B i` bounds the iteration after which `i`
iterations remain; one unit per test. `loopCost B N = Σ_{i<N} (B i + 1) + 1`. -/
def loopCost (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => B n + 1 + loopCost B n

theorem loopCost_const (b : ℕ) : ∀ N, loopCost (fun _ => b) N = N * (b + 1) + 1
  | 0 => by simp [loopCost]
  | N + 1 => by
    rw [loopCost, loopCost_const b N, Nat.succ_mul]
    omega

theorem loopCost_mono {B B' : ℕ → ℕ} (h : ∀ i, B i ≤ B' i) : ∀ N, loopCost B N ≤ loopCost B' N
  | 0 => le_rfl
  | N + 1 => by
    have := loopCost_mono h N
    have := h N
    simp only [loopCost]
    omega

namespace Triple

variable {ρ : List (Prog K Γ σ)} {P P' Q Q' Q₁ Q₂ R : St K Γ σ → Prop} {p q : Prog K Γ σ}
  {T T' T₁ T₂ : ℕ}

theorem of_eval (h : ∀ s, P s → ∃ s' t, Eval ρ p s s' t ∧ Q s' ∧ t ≤ T) : Triple ρ P p Q T := h

/-- An exact evaluation is a triple. -/
theorem exact {s s' : St K Γ σ} {t : ℕ} (h : Eval ρ p s s' t) :
    Triple ρ (· = s) p (· = s') t := by
  rintro _ rfl
  exact ⟨s', t, h, rfl, le_rfl⟩

theorem conseq (h : Triple ρ P p Q T) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hT : T ≤ T') : Triple ρ P' p Q' T' := by
  intro s hs
  obtain ⟨s', t, he, hq, ht⟩ := h s (hP s hs)
  exact ⟨s', t, he, hQ s' hq, ht.trans hT⟩

theorem pre (h : Triple ρ P p Q T) (hP : ∀ s, P' s → P s) : Triple ρ P' p Q T :=
  h.conseq hP (fun _ h => h) le_rfl

theorem post (h : Triple ρ P p Q T) (hQ : ∀ s, Q s → Q' s) : Triple ρ P p Q' T :=
  h.conseq (fun _ h => h) hQ le_rfl

theorem cost_mono (h : Triple ρ P p Q T) (hT : T ≤ T') : Triple ρ P p Q T' :=
  h.conseq (fun _ h => h) (fun _ h => h) hT

theorem exists_pre {X : Type} {P : X → St K Γ σ → Prop} (h : ∀ x, Triple ρ (P x) p Q T) :
    Triple ρ (fun s => ∃ x, P x s) p Q T := by
  rintro s ⟨x, hx⟩
  exact h x s hx

theorem pure_pre {φ : Prop} (h : φ → Triple ρ P p Q T) : Triple ρ (fun s => φ ∧ P s) p Q T := by
  rintro s ⟨hφ, hs⟩
  exact h hφ s hs

theorem false_pre : Triple ρ (fun _ => False) p Q T := fun _ h => h.elim

/-- Determinism: two triples for the same program and precondition combine. -/
theorem and (h₁ : Triple ρ P p Q₁ T₁) (h₂ : Triple ρ P p Q₂ T₂) :
    Triple ρ P p (fun s => Q₁ s ∧ Q₂ s) (min T₁ T₂) := by
  intro s hs
  obtain ⟨s₁, t₁, e₁, hq₁, ht₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, e₂, hq₂, ht₂⟩ := h₂ s hs
  obtain ⟨rfl, rfl⟩ := e₁.det e₂
  exact ⟨s₁, t₁, e₁, ⟨hq₁, hq₂⟩, le_min ht₁ ht₂⟩

/-- Lower bound (mutation tests): if `p` provably takes exactly `t` steps from some `s` with
`P s`, then no triple can promise less than `t`. -/
theorem cost_ge (h : Triple ρ P p Q T) {s s' : St K Γ σ} {t : ℕ} (hs : P s)
    (he : Eval ρ p s s' t) : t ≤ T := by
  obtain ⟨s₂, t₂, e₂, _, ht₂⟩ := h s hs
  obtain ⟨-, rfl⟩ := he.det e₂
  exact ht₂

/-! ### Atoms (weakest-precondition form) -/

theorem push (k : K) (f : σ → Γ k) (Q : St K Γ σ → Prop) :
    Triple ρ (fun s => Q ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩) (.push k f) Q 1 := by
  rintro ⟨v, S⟩ hs
  exact ⟨_, 1, Eval.push ρ k f v S, hs, le_rfl⟩

theorem peek (k : K) (f : σ → Option (Γ k) → σ) (Q : St K Γ σ → Prop) :
    Triple ρ (fun s => Q ⟨f s.var (s.stk k).head?, s.stk⟩) (.peek k f) Q 1 := by
  rintro ⟨v, S⟩ hs
  exact ⟨_, 1, Eval.peek ρ k f v S, hs, le_rfl⟩

theorem pop (k : K) (f : σ → Option (Γ k) → σ) (Q : St K Γ σ → Prop) :
    Triple ρ (fun s => Q ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩)
      (.pop k f) Q 1 := by
  rintro ⟨v, S⟩ hs
  exact ⟨_, 1, Eval.pop ρ k f v S, hs, le_rfl⟩

theorem load (f : σ → σ) (Q : St K Γ σ → Prop) :
    Triple ρ (fun s => Q ⟨f s.var, s.stk⟩) (.load f) Q 1 := by
  rintro ⟨v, S⟩ hs
  exact ⟨_, 1, Eval.load ρ f v S, hs, le_rfl⟩

/-! ### Control -/

theorem seq (h₁ : Triple ρ P p R T₁) (h₂ : Triple ρ R q Q T₂) :
    Triple ρ P (.seq p q) Q (T₁ + T₂) := by
  intro s hs
  obtain ⟨s₁, t₁, e₁, hr, ht₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, e₂, hq, ht₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, Eval.seq e₁ e₂, hq, Nat.add_le_add ht₁ ht₂⟩

theorem ite {c : σ → Bool} (h₁ : Triple ρ (fun s => P s ∧ c s.var = true) p Q T)
    (h₂ : Triple ρ (fun s => P s ∧ c s.var = false) q Q T) :
    Triple ρ P (.ite c p q) Q (T + 1) := by
  intro s hs
  cases hc : c s.var
  · obtain ⟨s', t, e, hq, ht⟩ := h₂ s ⟨hs, hc⟩
    exact ⟨s', t + 1, Eval.ite_false hc e, hq, Nat.succ_le_succ ht⟩
  · obtain ⟨s', t, e, hq, ht⟩ := h₁ s ⟨hs, hc⟩
    exact ⟨s', t + 1, Eval.ite_true hc e, hq, Nat.succ_le_succ ht⟩

/-- **Counted loop**: invariant `I n` with `n` = remaining iterations; total cost
`loopCost B N` = sum of the iteration bounds plus one per test. -/
theorem loop {c : σ → Bool} {I : ℕ → St K Γ σ → Prop} {B : ℕ → ℕ}
    (hstep : ∀ n, Triple ρ (I (n + 1)) p (I n) (B n))
    (hcont : ∀ n s, I (n + 1) s → c s.var = true)
    (hstop : ∀ s, I 0 s → c s.var = false) :
    ∀ N, Triple ρ (I N) (.loop c p) (I 0) (loopCost B N) := by
  intro N
  induction N with
  | zero =>
    intro s hs
    exact ⟨s, 1, Eval.loop_false (hstop s hs), hs, le_rfl⟩
  | succ n ih =>
    intro s hs
    obtain ⟨s₁, t₁, e₁, h₁, ht₁⟩ := hstep n s hs
    obtain ⟨s₂, t₂, e₂, h₂, ht₂⟩ := ih s₁ h₁
    refine ⟨s₂, t₁ + t₂ + 1, Eval.loop_true (hcont n s hs) e₁ e₂, h₂, ?_⟩
    show t₁ + t₂ + 1 ≤ B n + 1 + loopCost B n
    omega

/-- **Loop with invariant and variant**: `μ` strictly decreases per iteration and is positive
while the loop runs; each iteration costs at most `B`. -/
theorem loop_var {c : σ → Bool} {J : St K Γ σ → Prop} {μ : St K Γ σ → ℕ} {B : ℕ}
    (hstep : ∀ n, Triple ρ (fun s => J s ∧ c s.var = true ∧ μ s = n) p
      (fun s => J s ∧ μ s < n) B)
    (hpos : ∀ s, J s → c s.var = true → 0 < μ s) :
    ∀ N, Triple ρ (fun s => J s ∧ μ s ≤ N) (.loop c p) (fun s => J s ∧ c s.var = false)
      (N * (B + 1) + 1) := by
  intro N
  induction N with
  | zero =>
    rintro s ⟨hJ, hμ⟩
    cases hc : c s.var
    · exact ⟨s, 1, Eval.loop_false hc, ⟨hJ, hc⟩, by omega⟩
    · have := hpos s hJ hc
      omega
  | succ N ih =>
    rintro s ⟨hJ, hμ⟩
    cases hc : c s.var
    · exact ⟨s, 1, Eval.loop_false hc, ⟨hJ, hc⟩, by omega⟩
    · obtain ⟨s₁, t₁, e₁, ⟨hJ₁, hμ₁⟩, ht₁⟩ := hstep (μ s) s ⟨hJ, hc, rfl⟩
      obtain ⟨s₂, t₂, e₂, h₂, ht₂⟩ := ih s₁ ⟨hJ₁, by omega⟩
      refine ⟨s₂, t₁ + t₂ + 1, Eval.loop_true hc e₁ e₂, h₂, ?_⟩
      rw [Nat.succ_mul]
      omega

/-! ### Recursion -/

theorem fix_of_body {b : Prog K Γ σ} (h : Triple (b :: ρ) P b Q T) :
    Triple ρ P (.fix b) Q (T + 2) := by
  intro s hs
  obtain ⟨s', t, e, hq, ht⟩ := h s hs
  exact ⟨s', t + 2, Eval.fix e, hq, by omega⟩

theorem recur_of_body {n : ℕ} {b : Prog K Γ σ} (hb : ρ[n]? = some b)
    (h : Triple (ρ.drop n) P b Q T) : Triple ρ P (.recur n) Q (T + 2) := by
  intro s hs
  obtain ⟨s', t, e, hq, ht⟩ := h s hs
  exact ⟨s', t + 2, Eval.recur hb e, hq, by omega⟩

/-- **Recursion rule** (well-founded measure `μ` on ghost variables `x`): to prove the body,
assume the recursive call `recur 0` meets the spec for all strictly smaller ghost values. -/
theorem fix {X : Type} {b : Prog K Γ σ} {P Q : X → St K Γ σ → Prop} {T : X → ℕ} (μ : X → ℕ)
    (h : ∀ x, (∀ y, μ y < μ x → Triple (b :: ρ) (P y) (.recur 0) (Q y) (T y + 2)) →
      Triple (b :: ρ) (P x) b (Q x) (T x)) :
    ∀ x, Triple ρ (P x) (.fix b) (Q x) (T x + 2) := by
  have key : ∀ n, ∀ x, μ x = n → Triple (b :: ρ) (P x) b (Q x) (T x) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih x hx
    apply h x
    intro y hy
    exact recur_of_body (n := 0) rfl (ih (μ y) (hx ▸ hy) y rfl)
  intro x
  exact fix_of_body (key (μ x) x rfl)

/-! ### Frames and environments -/

/-- **Footprint frame rule**: any property `F` that only depends on stacks neither `p` nor the
enclosing bodies write is preserved. -/
theorem frame {F : St K Γ σ → Prop} (h : Triple ρ P p Q T)
    (hF : ∀ s s', F s → (∀ k, ¬ p.Writes k → (∀ b ∈ ρ, ¬ b.Writes k) → s'.stk k = s.stk k) →
      F s') :
    Triple ρ (fun s => P s ∧ F s) p (fun s => Q s ∧ F s) T := by
  rintro s ⟨hp, hf⟩
  obtain ⟨s', t, e, hq, ht⟩ := h s hp
  exact ⟨s', t, e, ⟨hq, hF s s' hf (fun k hk hρ => e.stk_eq_of_not_writes hk hρ)⟩, ht⟩

/-- Single-stack frame. -/
theorem frame_stk (h : Triple ρ P p Q T) (k : K) (L : List (Γ k)) (hp : ¬ p.Writes k)
    (hρ : ∀ b ∈ ρ, ¬ b.Writes k) :
    Triple ρ (fun s => P s ∧ s.stk k = L) p (fun s => Q s ∧ s.stk k = L) T :=
  h.frame (F := fun s => s.stk k = L) (fun _ _ hs hagree => (hagree k hp hρ).trans hs)

/-- Closed programs: triples transfer to any environment. -/
theorem env_irrel (h : Triple ρ P p Q T) (hc : p.Closed) (ρ' : List (Prog K Γ σ)) :
    Triple ρ' P p Q T := by
  intro s hs
  obtain ⟨s', t, e, hq, ht⟩ := h s hs
  exact ⟨s', t, e.env_irrel hc ρ', hq, ht⟩

end Triple

end Triple

end TMFw
