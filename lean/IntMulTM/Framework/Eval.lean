import IntMulTM.Framework.Prog

/-!
# IntMulTM.Framework.Eval — big-step semantics with cost

* `Eval ρ p s s' t` : `p` runs from `s` to `s'` with cost `t` (= number of TM2 steps of the
  compiled code, see `IntMulTM.Framework.Sim`); `ρ` lists the bodies of the enclosing `fix`es,
  innermost first.
* `Eval.det` : determinism (final state and cost).
* `Prog.Writes`, `Eval.stk_eq_of_not_writes` : syntactic footprint; stacks a program never pushes
  to or pops from are unchanged (frame property).
* `Prog.FreeBelow`, `Prog.Closed`, `Eval.env_congr`, `Eval.env_irrel` : a closed program (no free
  `recur`) evaluates identically under any environment.
-/

namespace TMFw

open Turing

section Footprint

variable {K : Type} {Γ : K → Type} {σ : Type}

namespace Prog

/-- `p` may modify stack `k`: it contains a `push k` or a `pop k`. -/
def Writes (k : K) : Prog K Γ σ → Prop
  | .push k' _ => k' = k
  | .pop k' _ => k' = k
  | .seq p q => Writes k p ∨ Writes k q
  | .ite _ p q => Writes k p ∨ Writes k q
  | .loop _ p => Writes k p
  | .fix b => Writes k b
  | _ => False

/-- All free `recur n` of `p` have `n < d` (indices `≥ d` would escape `d` enclosing `fix`es). -/
def FreeBelow : ℕ → Prog K Γ σ → Prop
  | d, .seq p q => FreeBelow d p ∧ FreeBelow d q
  | d, .ite _ p q => FreeBelow d p ∧ FreeBelow d q
  | d, .loop _ p => FreeBelow d p
  | d, .fix b => FreeBelow (d + 1) b
  | d, .recur n => n < d
  | _, _ => True

/-- No free `recur`: every `recur` refers to a `fix` inside `p`. -/
def Closed (p : Prog K Γ σ) : Prop := p.FreeBelow 0

end Prog

end Footprint

/-! ## List helpers -/

theorem getElem?_mem' {α : Type} : ∀ {l : List α} {n : ℕ} {a : α}, l[n]? = some a → a ∈ l
  | [], _, _, h => by simp at h
  | x :: l, 0, a, h => by simp at h; simp [h]
  | _ :: l, n + 1, a, h => List.mem_cons_of_mem _ (getElem?_mem' (l := l) (n := n) (by simpa using h))

theorem mem_of_mem_drop' {α : Type} : ∀ {l : List α} {n : ℕ} {a : α}, a ∈ l.drop n → a ∈ l
  | _, 0, _, h => by simpa using h
  | [], _ + 1, _, h => by simp at h
  | _ :: l, n + 1, a, h => List.mem_cons_of_mem _ (mem_of_mem_drop' (l := l) (n := n) (by simpa using h))

theorem getElem?_drop' {α : Type} : ∀ (l : List α) (n i : ℕ), (l.drop n)[i]? = l[n + i]?
  | _, 0, i => by simp
  | [], _ + 1, _ => by simp
  | x :: l, n + 1, i => by
    rw [List.drop_succ_cons, getElem?_drop' l n i, show n + 1 + i = (n + i) + 1 by omega,
      List.getElem?_cons_succ]

theorem drop_eq_cons_of_getElem? {α : Type} : ∀ {l : List α} {n : ℕ} {a : α}, l[n]? = some a →
    l.drop n = a :: l.drop (n + 1)
  | [], _, _, h => by simp at h
  | x :: l, 0, a, h => by simp at h; subst h; rfl
  | _ :: l, n + 1, _, h => drop_eq_cons_of_getElem? (l := l) (n := n) (by simpa using h)

theorem getD_eq_of_drop_eq_cons {α : Type} : ∀ {l : List α} {n : ℕ} {a d : α} {l' : List α},
    l.drop n = a :: l' → l.getD n d = a
  | [], 0, _, _, _, h => by simp at h
  | [], _ + 1, _, _, _, h => by simp at h
  | x :: l, 0, a, d, l', h => by simp at h; simp [h.1]
  | _ :: l, n + 1, _, _, _, h => by
    simp only [List.drop_succ_cons] at h
    simpa using getD_eq_of_drop_eq_cons (l := l) (n := n) h

section Semantics

variable {K : Type} {Γ : K → Type} {σ : Type} [DecidableEq K]

/-- Big-step semantics with cost. `ρ` = bodies of the enclosing `fix`es, innermost first. -/
inductive Eval : List (Prog K Γ σ) → Prog K Γ σ → St K Γ σ → St K Γ σ → ℕ → Prop where
  | push (ρ : List (Prog K Γ σ)) (k : K) (f : σ → Γ k) (v : σ) (S : ∀ k, List (Γ k)) :
      Eval ρ (.push k f) ⟨v, S⟩ ⟨v, Function.update S k (f v :: S k)⟩ 1
  | peek (ρ : List (Prog K Γ σ)) (k : K) (f : σ → Option (Γ k) → σ) (v : σ)
      (S : ∀ k, List (Γ k)) :
      Eval ρ (.peek k f) ⟨v, S⟩ ⟨f v (S k).head?, S⟩ 1
  | pop (ρ : List (Prog K Γ σ)) (k : K) (f : σ → Option (Γ k) → σ) (v : σ)
      (S : ∀ k, List (Γ k)) :
      Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (S k).head?, Function.update S k (S k).tail⟩ 1
  | load (ρ : List (Prog K Γ σ)) (f : σ → σ) (v : σ) (S : ∀ k, List (Γ k)) :
      Eval ρ (.load f) ⟨v, S⟩ ⟨f v, S⟩ 1
  | seq {ρ : List (Prog K Γ σ)} {p q : Prog K Γ σ} {s₁ s₂ s₃ : St K Γ σ} {t₁ t₂ : ℕ} :
      Eval ρ p s₁ s₂ t₁ → Eval ρ q s₂ s₃ t₂ → Eval ρ (.seq p q) s₁ s₃ (t₁ + t₂)
  | ite_true {ρ : List (Prog K Γ σ)} {c : σ → Bool} {p q : Prog K Γ σ} {s s' : St K Γ σ}
      {t : ℕ} :
      c s.var = true → Eval ρ p s s' t → Eval ρ (.ite c p q) s s' (t + 1)
  | ite_false {ρ : List (Prog K Γ σ)} {c : σ → Bool} {p q : Prog K Γ σ} {s s' : St K Γ σ}
      {t : ℕ} :
      c s.var = false → Eval ρ q s s' t → Eval ρ (.ite c p q) s s' (t + 1)
  | loop_true {ρ : List (Prog K Γ σ)} {c : σ → Bool} {p : Prog K Γ σ} {s s₁ s₂ : St K Γ σ}
      {t₁ t₂ : ℕ} :
      c s.var = true → Eval ρ p s s₁ t₁ → Eval ρ (.loop c p) s₁ s₂ t₂ →
        Eval ρ (.loop c p) s s₂ (t₁ + t₂ + 1)
  | loop_false {ρ : List (Prog K Γ σ)} {c : σ → Bool} {p : Prog K Γ σ} {s : St K Γ σ} :
      c s.var = false → Eval ρ (.loop c p) s s 1
  | fix {ρ : List (Prog K Γ σ)} {b : Prog K Γ σ} {s s' : St K Γ σ} {t : ℕ} :
      Eval (b :: ρ) b s s' t → Eval ρ (.fix b) s s' (t + 2)
  | recur {ρ : List (Prog K Γ σ)} {n : ℕ} {b : Prog K Γ σ} {s s' : St K Γ σ} {t : ℕ} :
      ρ[n]? = some b → Eval (ρ.drop n) b s s' t → Eval ρ (.recur n) s s' (t + 2)

/-- Rewrite the final state and the cost of an evaluation. -/
theorem Eval.of_eq {ρ : List (Prog K Γ σ)} {p : Prog K Γ σ} {s s₁ s₂ : St K Γ σ} {t₁ t₂ : ℕ}
    (h : Eval ρ p s s₁ t₁) (hs : s₁ = s₂) (ht : t₁ = t₂) : Eval ρ p s s₂ t₂ := by
  subst hs; subst ht; exact h

/-- **Determinism**: final state and cost are unique. -/
theorem Eval.det {ρ : List (Prog K Γ σ)} {p : Prog K Γ σ} {s s₁ s₂ : St K Γ σ} {t₁ t₂ : ℕ}
    (h₁ : Eval ρ p s s₁ t₁) (h₂ : Eval ρ p s s₂ t₂) : s₁ = s₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing s₂ t₂ with
  | push => cases h₂; exact ⟨rfl, rfl⟩
  | peek => cases h₂; exact ⟨rfl, rfl⟩
  | pop => cases h₂; exact ⟨rfl, rfl⟩
  | load => cases h₂; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂a h₂b =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₂a
      obtain ⟨rfl, rfl⟩ := ih₂ h₂b
      exact ⟨rfl, rfl⟩
  | ite_true hc _ ih =>
    cases h₂ with
    | ite_true _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
    | ite_false hc' _ => rw [hc] at hc'; cases hc'
  | ite_false hc _ ih =>
    cases h₂ with
    | ite_true hc' _ => rw [hc] at hc'; cases hc'
    | ite_false _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | loop_true hc _ _ ih₁ ih₂ =>
    cases h₂ with
    | loop_true _ h₂a h₂b =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₂a
      obtain ⟨rfl, rfl⟩ := ih₂ h₂b
      exact ⟨rfl, rfl⟩
    | loop_false hc' => rw [hc] at hc'; cases hc'
  | loop_false hc =>
    cases h₂ with
    | loop_true hc' _ _ => rw [hc] at hc'; cases hc'
    | loop_false _ => exact ⟨rfl, rfl⟩
  | fix _ ih =>
    cases h₂ with
    | fix h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | recur hb _ ih =>
    cases h₂ with
    | recur hb' h =>
      rw [hb] at hb'
      cases hb'
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

/-- **Frame property**: a stack that neither `p` nor the enclosing bodies write is unchanged. -/
theorem Eval.stk_eq_of_not_writes {ρ : List (Prog K Γ σ)} {p : Prog K Γ σ} {s s' : St K Γ σ}
    {t : ℕ} (h : Eval ρ p s s' t) {k : K} (hp : ¬ p.Writes k) (hρ : ∀ b ∈ ρ, ¬ b.Writes k) :
    s'.stk k = s.stk k := by
  induction h with
  | push _ k' f v S => exact Function.update_of_ne (fun e => hp e.symm) _ _
  | peek => rfl
  | pop _ k' f v S => exact Function.update_of_ne (fun e => hp e.symm) _ _
  | load => rfl
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ (fun h => hp (Or.inr h)) hρ).trans (ih₁ (fun h => hp (Or.inl h)) hρ)
  | ite_true _ _ ih => exact ih (fun h => hp (Or.inl h)) hρ
  | ite_false _ _ ih => exact ih (fun h => hp (Or.inr h)) hρ
  | loop_true _ _ _ ih₁ ih₂ => exact (ih₂ hp hρ).trans (ih₁ hp hρ)
  | loop_false => rfl
  | fix _ ih =>
    refine ih hp ?_
    intro b' hb'
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact hp
    · exact hρ b' hb'
  | recur hb _ ih =>
    exact ih (hρ _ (getElem?_mem' hb)) (fun b' hb' => hρ b' (mem_of_mem_drop' hb'))

/-- Environments agree on their first `d` entries, and those entries only refer to entries below
`d` (so that evaluation of a `FreeBelow d` program never looks further). -/
def EnvAgree (d : ℕ) (ρ ρ' : List (Prog K Γ σ)) : Prop :=
  ∀ i < d, ρ[i]? = ρ'[i]? ∧ ∀ b, ρ[i]? = some b → b.FreeBelow (d - i)

/-- **Environment congruence.** -/
theorem Eval.env_congr {ρ : List (Prog K Γ σ)} {p : Prog K Γ σ} {s s' : St K Γ σ} {t : ℕ}
    (h : Eval ρ p s s' t) :
    ∀ {d : ℕ} {ρ' : List (Prog K Γ σ)}, p.FreeBelow d → EnvAgree d ρ ρ' → Eval ρ' p s s' t := by
  induction h with
  | push _ k f v S => intro d ρ' _ _; exact Eval.push ρ' k f v S
  | peek _ k f v S => intro d ρ' _ _; exact Eval.peek ρ' k f v S
  | pop _ k f v S => intro d ρ' _ _; exact Eval.pop ρ' k f v S
  | load _ f v S => intro d ρ' _ _; exact Eval.load ρ' f v S
  | seq _ _ ih₁ ih₂ =>
    intro d ρ' hp hA
    obtain ⟨hp₁, hp₂⟩ := hp
    exact Eval.seq (ih₁ hp₁ hA) (ih₂ hp₂ hA)
  | ite_true hc _ ih =>
    intro d ρ' hp hA
    obtain ⟨hp₁, -⟩ := hp
    exact Eval.ite_true hc (ih hp₁ hA)
  | ite_false hc _ ih =>
    intro d ρ' hp hA
    obtain ⟨-, hp₂⟩ := hp
    exact Eval.ite_false hc (ih hp₂ hA)
  | loop_true hc _ _ ih₁ ih₂ =>
    intro d ρ' hp hA
    exact Eval.loop_true hc (ih₁ hp hA) (ih₂ hp hA)
  | loop_false hc => intro d ρ' _ _; exact Eval.loop_false hc
  | @fix ρ b s s' t _ ih =>
    intro d ρ' hp hA
    refine Eval.fix (ih (d := d + 1) hp ?_)
    intro i hi
    cases i with
    | zero =>
      refine ⟨rfl, fun b' hb' => ?_⟩
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb'
      subst hb'
      simpa [Prog.FreeBelow] using hp
    | succ i =>
      obtain ⟨h1, h2⟩ := hA i (by omega)
      simp only [List.getElem?_cons_succ]
      refine ⟨h1, fun b' hb' => ?_⟩
      have := h2 b' hb'
      simpa using this
  | @recur ρ n b s s' t hb _ ih =>
    intro d ρ' hp hA
    have hn : n < d := hp
    obtain ⟨heq, hfb⟩ := hA n hn
    have hb' : ρ'[n]? = some b := by rw [← heq]; exact hb
    refine Eval.recur hb' (ih (d := d - n) (hfb b hb) ?_)
    intro i hi
    obtain ⟨h1, h2⟩ := hA (n + i) (by omega)
    rw [getElem?_drop', getElem?_drop']
    refine ⟨h1, fun b' hb' => ?_⟩
    have := h2 b' hb'
    rwa [show d - (n + i) = d - n - i by omega] at this

/-- **Closed programs ignore the environment.** -/
theorem Eval.env_irrel {ρ : List (Prog K Γ σ)} {p : Prog K Γ σ} {s s' : St K Γ σ} {t : ℕ}
    (h : Eval ρ p s s' t) (hc : p.Closed) (ρ' : List (Prog K Γ σ)) : Eval ρ' p s s' t :=
  h.env_congr (d := 0) hc (fun _ hi => absurd hi (Nat.not_lt_zero _))

end Semantics

end TMFw
