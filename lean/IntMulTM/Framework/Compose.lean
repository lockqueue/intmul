import IntMulTM.Framework.Triple

/-!
# IntMulTM.Framework.Compose — composing components with different registers and stacks

* `Lens σ τ` (+ `Lens.fst`, `Lens.snd`, `Lens.comp`) and `Prog.liftRegs` : run a component written
  over registers `τ` inside a program over registers `σ`; `Eval.liftRegs`, `Triple.liftRegs`
  (registers outside the lens are preserved: a register frame rule).
* `Prog.mapStk` : rename the stacks of a uniform-alphabet component along an injection `K → K'`;
  `Eval.mapStk`, `Triple.mapStk` (stacks outside the image are untouched: a stack frame rule).
* Both preserve cost exactly.
-/

namespace TMFw

open Turing

/-! ## List helpers -/

theorem getElem?_map' {α β : Type} (f : α → β) : ∀ (l : List α) (n : ℕ),
    (l.map f)[n]? = (l[n]?).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => getElem?_map' f l n

theorem drop_map' {α β : Type} (f : α → β) : ∀ (l : List α) (n : ℕ),
    (l.map f).drop n = (l.drop n).map f
  | _, 0 => rfl
  | [], _ + 1 => rfl
  | _ :: l, n + 1 => drop_map' f l n

/-! ## Register lenses -/

/-- A lens focusing the registers `τ` of a component inside the registers `σ` of a program. -/
structure Lens (σ τ : Type) where
  get : σ → τ
  set : σ → τ → σ
  get_set : ∀ v w, get (set v w) = w
  set_get : ∀ v, set v (get v) = v
  set_set : ∀ v w w', set (set v w) w' = set v w'

/-- First component of a register pair. -/
def Lens.fst (σ τ : Type) : Lens (σ × τ) σ where
  get := Prod.fst
  set v w := (w, v.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Second component of a register pair. -/
def Lens.snd (σ τ : Type) : Lens (σ × τ) τ where
  get := Prod.snd
  set v w := (v.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens composition. -/
def Lens.comp {σ τ υ : Type} (l₁ : Lens σ τ) (l₂ : Lens τ υ) : Lens σ υ where
  get v := l₂.get (l₁.get v)
  set v w := l₁.set v (l₂.set (l₁.get v) w)
  get_set v w := by simp only [l₁.get_set, l₂.get_set]
  set_get v := by simp only [l₂.set_get, l₁.set_get]
  set_set v w w' := by simp only [l₁.get_set, l₂.set_set, l₁.set_set]

section LiftRegs

variable {K : Type} {Γ : K → Type} {σ τ : Type}

/-- Run a component over registers `τ` inside registers `σ`. -/
def Prog.liftRegs (l : Lens σ τ) : Prog K Γ τ → Prog K Γ σ
  | .push k f => .push k (fun v => f (l.get v))
  | .peek k f => .peek k (fun v o => l.set v (f (l.get v) o))
  | .pop k f => .pop k (fun v o => l.set v (f (l.get v) o))
  | .load f => .load (fun v => l.set v (f (l.get v)))
  | .seq p q => .seq (Prog.liftRegs l p) (Prog.liftRegs l q)
  | .ite c p q => .ite (fun v => c (l.get v)) (Prog.liftRegs l p) (Prog.liftRegs l q)
  | .loop c p => .loop (fun v => c (l.get v)) (Prog.liftRegs l p)
  | .fix b => .fix (Prog.liftRegs l b)
  | .recur n => .recur n

variable [DecidableEq K]

/-- **Register transport.** Same stacks, same cost; registers outside the lens are preserved. -/
theorem Eval.liftRegs (l : Lens σ τ) {ρ : List (Prog K Γ τ)} {p : Prog K Γ τ}
    {s s' : St K Γ τ} {t : ℕ} (h : Eval ρ p s s' t) :
    ∀ v : σ, l.get v = s.var →
      Eval (ρ.map (Prog.liftRegs l)) (Prog.liftRegs l p) ⟨v, s.stk⟩ ⟨l.set v s'.var, s'.stk⟩ t := by
  induction h with
  | push ρ k f w S =>
    intro v hv
    refine (Eval.push (ρ.map (Prog.liftRegs l)) k (fun v => f (l.get v)) v S).of_eq ?_ rfl
    have hv' : l.get v = w := hv
    subst hv'
    show (⟨v, Function.update S k (f (l.get v) :: S k)⟩ : St K Γ σ) =
      ⟨l.set v (l.get v), Function.update S k (f (l.get v) :: S k)⟩
    rw [l.set_get]
  | peek ρ k f w S =>
    intro v hv
    refine (Eval.peek (ρ.map (Prog.liftRegs l)) k (fun v o => l.set v (f (l.get v) o)) v S).of_eq
      ?_ rfl
    have hv' : l.get v = w := hv
    subst hv'
    rfl
  | pop ρ k f w S =>
    intro v hv
    refine (Eval.pop (ρ.map (Prog.liftRegs l)) k (fun v o => l.set v (f (l.get v) o)) v S).of_eq
      ?_ rfl
    have hv' : l.get v = w := hv
    subst hv'
    rfl
  | load ρ f w S =>
    intro v hv
    refine (Eval.load (ρ.map (Prog.liftRegs l)) (fun v => l.set v (f (l.get v))) v S).of_eq ?_ rfl
    have hv' : l.get v = w := hv
    subst hv'
    rfl
  | @seq ρ p q s₁ s₂ s₃ t₁ t₂ _ _ ih₁ ih₂ =>
    intro v hv
    have h₁ := ih₁ v hv
    have h₂ := ih₂ (l.set v s₂.var) (l.get_set _ _)
    rw [l.set_set] at h₂
    exact Eval.seq h₁ h₂
  | @ite_true ρ c p q s s' t hc _ ih =>
    intro v hv
    exact Eval.ite_true (ρ := ρ.map (Prog.liftRegs l)) (c := fun v => c (l.get v))
      (p := Prog.liftRegs l p) (q := Prog.liftRegs l q) (s := ⟨v, s.stk⟩)
      (by show c (l.get v) = true; rw [hv]; exact hc) (ih v hv)
  | @ite_false ρ c p q s s' t hc _ ih =>
    intro v hv
    exact Eval.ite_false (ρ := ρ.map (Prog.liftRegs l)) (c := fun v => c (l.get v))
      (p := Prog.liftRegs l p) (q := Prog.liftRegs l q) (s := ⟨v, s.stk⟩)
      (by show c (l.get v) = false; rw [hv]; exact hc) (ih v hv)
  | @loop_true ρ c p s s₁ s₂ t₁ t₂ hc _ _ ih₁ ih₂ =>
    intro v hv
    have h₁ := ih₁ v hv
    have h₂ := ih₂ (l.set v s₁.var) (l.get_set _ _)
    rw [l.set_set] at h₂
    exact Eval.loop_true (ρ := ρ.map (Prog.liftRegs l)) (c := fun v => c (l.get v))
      (p := Prog.liftRegs l p) (s := ⟨v, s.stk⟩)
      (by show c (l.get v) = true; rw [hv]; exact hc) h₁ h₂
  | @loop_false ρ c p s hc =>
    intro v hv
    have h := Eval.loop_false (ρ := ρ.map (Prog.liftRegs l)) (c := fun v => c (l.get v))
      (p := Prog.liftRegs l p) (s := ⟨v, s.stk⟩) (by show c (l.get v) = false; rw [hv]; exact hc)
    refine h.of_eq ?_ rfl
    rw [← hv, l.set_get]
  | fix _ ih =>
    intro v hv
    exact Eval.fix (ih v hv)
  | @recur ρ n b s s' t hb _ ih =>
    intro v hv
    have hb' : (ρ.map (Prog.liftRegs l))[n]? = some (Prog.liftRegs l b) := by
      rw [getElem?_map', hb]; rfl
    refine Eval.recur hb' ?_
    rw [drop_map']
    exact ih v hv

/-- **Register frame rule** (Triple level). `G` must be insensitive to the lens focus. -/
theorem Triple.liftRegs (l : Lens σ τ) {ρ : List (Prog K Γ τ)} {P Q : St K Γ τ → Prop}
    {p : Prog K Γ τ} {T : ℕ} (h : Triple ρ P p Q T) (G : σ → Prop)
    (hG : ∀ v w, G v → G (l.set v w)) :
    Triple (ρ.map (Prog.liftRegs l)) (fun s => P ⟨l.get s.var, s.stk⟩ ∧ G s.var)
      (Prog.liftRegs l p) (fun s => Q ⟨l.get s.var, s.stk⟩ ∧ G s.var) T := by
  rintro ⟨v, S⟩ ⟨hP, hGv⟩
  obtain ⟨s', t, e, hq, ht⟩ := h ⟨l.get v, S⟩ hP
  refine ⟨⟨l.set v s'.var, s'.stk⟩, t, e.liftRegs l v rfl, ⟨?_, hG v _ hGv⟩, ht⟩
  show Q ⟨l.get (l.set v s'.var), s'.stk⟩
  rw [l.get_set]
  exact hq

end LiftRegs

/-! ## Stack renaming (uniform alphabet) -/

section MapStk

variable {K K' A σ : Type}

/-- Rename the stacks of a uniform-alphabet program along `ι`. -/
def Prog.mapStk (ι : K → K') : Prog K (fun _ => A) σ → Prog K' (fun _ => A) σ
  | .push k f => .push (ι k) f
  | .peek k f => .peek (ι k) f
  | .pop k f => .pop (ι k) f
  | .load f => .load f
  | .seq p q => .seq (Prog.mapStk ι p) (Prog.mapStk ι q)
  | .ite c p q => .ite c (Prog.mapStk ι p) (Prog.mapStk ι q)
  | .loop c p => .loop c (Prog.mapStk ι p)
  | .fix b => .fix (Prog.mapStk ι b)
  | .recur n => .recur n

/-- View a big state through the renaming. -/
def St.comap (ι : K → K') (s : St K' (fun _ => A) σ) : St K (fun _ => A) σ :=
  ⟨s.var, fun k => s.stk (ι k)⟩

variable [DecidableEq K] [DecidableEq K']

theorem update_comp_inj {ι : K → K'} (hι : Function.Injective ι) (T : K' → List A)
    (S : K → List A) (hT : ∀ k, T (ι k) = S k) (k : K) (x : List A) :
    ∀ k₂, Function.update T (ι k) x (ι k₂) = Function.update S k x k₂ := by
  intro k₂
  by_cases h : k₂ = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (hι.ne h), Function.update_of_ne h, hT]

/-- **Stack transport.** -/
theorem Eval.mapStk {ι : K → K'} (hι : Function.Injective ι)
    {ρ : List (Prog K (fun _ => A) σ)} {p : Prog K (fun _ => A) σ}
    {s s' : St K (fun _ => A) σ} {t : ℕ} (h : Eval ρ p s s' t) :
    ∀ T : K' → List A, (∀ k, T (ι k) = s.stk k) →
      ∃ T' : K' → List A, (∀ k, T' (ι k) = s'.stk k) ∧ (∀ k', (∀ k, ι k ≠ k') → T' k' = T k') ∧
        Eval (ρ.map (Prog.mapStk ι)) (Prog.mapStk ι p) ⟨s.var, T⟩ ⟨s'.var, T'⟩ t := by
  induction h with
  | push _ k f v S =>
    intro T hT
    have hk : T (ι k) = S k := hT k
    refine ⟨Function.update T (ι k) (f v :: T (ι k)), ?_, ?_, Eval.push _ (ι k) f v T⟩
    · intro k₂
      rw [hk]
      exact update_comp_inj hι T S hT k _ k₂
    · intro k' hk'
      exact Function.update_of_ne (Ne.symm (hk' k)) _ _
  | peek _ k f v S =>
    intro T hT
    have hk : T (ι k) = S k := hT k
    refine ⟨T, hT, fun _ _ => rfl, (Eval.peek _ (ι k) f v T).of_eq ?_ rfl⟩
    show (⟨f v (T (ι k)).head?, T⟩ : St K' (fun _ => A) σ) = ⟨f v (S k).head?, T⟩
    rw [hk]
  | pop _ k f v S =>
    intro T hT
    have hk : T (ι k) = S k := hT k
    refine ⟨Function.update T (ι k) (T (ι k)).tail, ?_, ?_,
      (Eval.pop _ (ι k) f v T).of_eq ?_ rfl⟩
    · intro k₂
      rw [hk]
      exact update_comp_inj hι T S hT k _ k₂
    · intro k' hk'
      exact Function.update_of_ne (Ne.symm (hk' k)) _ _
    · show (⟨f v (T (ι k)).head?, Function.update T (ι k) (T (ι k)).tail⟩ :
          St K' (fun _ => A) σ) = ⟨f v (S k).head?, Function.update T (ι k) (T (ι k)).tail⟩
      rw [hk]
  | load _ f v S =>
    intro T hT
    exact ⟨T, hT, fun _ _ => rfl, Eval.load _ f v T⟩
  | seq _ _ ih₁ ih₂ =>
    intro T hT
    obtain ⟨T₁, h₁a, h₁b, e₁⟩ := ih₁ T hT
    obtain ⟨T₂, h₂a, h₂b, e₂⟩ := ih₂ T₁ h₁a
    exact ⟨T₂, h₂a, fun k' hk' => (h₂b k' hk').trans (h₁b k' hk'), Eval.seq e₁ e₂⟩
  | ite_true hc _ ih =>
    intro T hT
    obtain ⟨T', a, b, e⟩ := ih T hT
    exact ⟨T', a, b, Eval.ite_true hc e⟩
  | ite_false hc _ ih =>
    intro T hT
    obtain ⟨T', a, b, e⟩ := ih T hT
    exact ⟨T', a, b, Eval.ite_false hc e⟩
  | loop_true hc _ _ ih₁ ih₂ =>
    intro T hT
    obtain ⟨T₁, h₁a, h₁b, e₁⟩ := ih₁ T hT
    obtain ⟨T₂, h₂a, h₂b, e₂⟩ := ih₂ T₁ h₁a
    exact ⟨T₂, h₂a, fun k' hk' => (h₂b k' hk').trans (h₁b k' hk'), Eval.loop_true hc e₁ e₂⟩
  | loop_false hc =>
    intro T hT
    exact ⟨T, hT, fun _ _ => rfl, Eval.loop_false hc⟩
  | fix _ ih =>
    intro T hT
    obtain ⟨T', a, b, e⟩ := ih T hT
    exact ⟨T', a, b, Eval.fix e⟩
  | @recur ρ n b s s' t hb _ ih =>
    intro T hT
    obtain ⟨T', a, b', e⟩ := ih T hT
    have hb' : (ρ.map (Prog.mapStk ι))[n]? = some (Prog.mapStk ι b) := by
      rw [getElem?_map', hb]; rfl
    refine ⟨T', a, b', Eval.recur hb' ?_⟩
    rw [drop_map']
    exact e

/-- **Stack frame rule** (Triple level): run a component on a subset of the stacks; `F` may only
depend on stacks outside the image of `ι`. -/
theorem Triple.mapStk {ι : K → K'} (hι : Function.Injective ι)
    {ρ : List (Prog K (fun _ => A) σ)} {P Q : St K (fun _ => A) σ → Prop}
    {p : Prog K (fun _ => A) σ} {T : ℕ} (h : Triple ρ P p Q T) (F : St K' (fun _ => A) σ → Prop)
    (hF : ∀ s s', F s → (∀ k', (∀ k, ι k ≠ k') → s'.stk k' = s.stk k') → F s') :
    Triple (ρ.map (Prog.mapStk ι)) (fun s => P (s.comap ι) ∧ F s) (Prog.mapStk ι p)
      (fun s => Q (s.comap ι) ∧ F s) T := by
  rintro ⟨v, Tk⟩ ⟨hP, hF'⟩
  obtain ⟨s', t, e, hq, ht⟩ := h ⟨v, fun k => Tk (ι k)⟩ hP
  obtain ⟨T', ha, hb, e'⟩ := e.mapStk hι Tk (fun _ => rfl)
  refine ⟨⟨s'.var, T'⟩, t, e', ⟨?_, hF _ _ hF' hb⟩, ht⟩
  have hs : (⟨s'.var, fun k => T' (ι k)⟩ : St K (fun _ => A) σ) = s' := by
    cases s'
    simp only [St.mk.injEq, true_and]
    funext k
    exact ha k
  show Q ⟨s'.var, fun k => T' (ι k)⟩
  rw [hs]
  exact hq

end MapStk

end TMFw
