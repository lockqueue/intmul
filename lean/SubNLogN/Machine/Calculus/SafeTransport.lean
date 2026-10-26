/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Safe

/-!
# Framed procedure calculus (`Calculus/SafeTransport.lean`): transport of boundary-safe runs

This file proves the transport rules that `Calculus/Safe.lean` states as interface propositions
`…Stmt : Prop`. The `SafeEval` proofs mirror the `TMFw.Eval`
transport proofs `Eval.env_congr` (`IntMulTM/Framework/Eval.lean`), `Eval.liftRegs` and
`Eval.mapStk` (`IntMulTM/Framework/Compose.lean`) constructor by constructor. The extra
`peek`/`pop` side condition is carried along in each case.

* `SafeEval.env_congr`, `SafeEval.env_irrel`: change of environment (closed programs).
* `SafeEval.liftRegs`: register lens. The stacks and the side conditions are unchanged.
* `SafeEval.mapStk`: injective stack renaming `ι : L → K`. Every big stack in the image that is
  framed for the caller must be framed for the component (`∀ x, framedK (ι x) → framedL x`).
* `SafeEval.append_safe`: the frame rule *inside* safe evaluation. Appending tails below framed
  stacks (and nothing below the other stacks) keeps the run boundary-safe for the **same**
  framed set. (`SafeEval.append_tail` of `Frame.lean` only yields an `Eval`.)
* Judgment level: `SafeRunsIn.env_irrel`, `liftRegs`, `callInj`, `frame_tail`, `mono_framed`,
  and `SafeRunsIn.of_runsIn_unframed`. The last one applies only when nothing is framed.
* `safeEnvIrrelStmt_holds`, `safeLiftRegsStmt_holds`, `safeCallInjStmt_holds` discharge the three
  transport statements of `Safe.lean` verbatim.

Every rule preserves the cost exactly.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

namespace SafeEval

section Env

variable {K σ : Type} [DecidableEq K] {framed : K → Prop}

/-- Rewriting the final state of a safe run. -/
theorem of_final_eq {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s₁ s₂ : St K (fun _ => Sym) σ} {t : ℕ} (h : SafeEval framed ρ p s s₁ t) (e : s₁ = s₂) :
    SafeEval framed ρ p s s₂ t := e ▸ h

/-- **Environment congruence** for safe runs (mirror of `TMFw.Eval.env_congr`). -/
theorem env_congr {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s' : St K (fun _ => Sym) σ} {t : ℕ} (h : SafeEval framed ρ p s s' t) :
    ∀ {d : ℕ} {ρ' : List (Prog K (fun _ => Sym) σ)}, p.FreeBelow d → EnvAgree d ρ ρ' →
      SafeEval framed ρ' p s s' t := by
  induction h with
  | push _ k f v S => intro d ρ' _ _; exact SafeEval.push ρ' k f v S
  | peek _ k f v S hS => intro d ρ' _ _; exact SafeEval.peek ρ' k f v S hS
  | pop _ k f v S hS => intro d ρ' _ _; exact SafeEval.pop ρ' k f v S hS
  | load _ f v S => intro d ρ' _ _; exact SafeEval.load ρ' f v S
  | seq _ _ ih₁ ih₂ =>
    intro d ρ' hp hA
    obtain ⟨hp₁, hp₂⟩ := hp
    exact SafeEval.seq (ih₁ hp₁ hA) (ih₂ hp₂ hA)
  | ite_true hc _ ih =>
    intro d ρ' hp hA
    obtain ⟨hp₁, -⟩ := hp
    exact SafeEval.ite_true hc (ih hp₁ hA)
  | ite_false hc _ ih =>
    intro d ρ' hp hA
    obtain ⟨-, hp₂⟩ := hp
    exact SafeEval.ite_false hc (ih hp₂ hA)
  | loop_true hc _ _ ih₁ ih₂ =>
    intro d ρ' hp hA
    exact SafeEval.loop_true hc (ih₁ hp hA) (ih₂ hp hA)
  | loop_false hc => intro d ρ' _ _; exact SafeEval.loop_false hc
  | @fix ρ b s s' t _ ih =>
    intro d ρ' hp hA
    refine SafeEval.fix (ih (d := d + 1) hp ?_)
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
    refine SafeEval.recur hb' (ih (d := d - n) (hfb b hb) ?_)
    intro i hi
    obtain ⟨h1, h2⟩ := hA (n + i) (by omega)
    rw [getElem?_drop', getElem?_drop']
    refine ⟨h1, fun b' hb' => ?_⟩
    have := h2 b' hb'
    rwa [show d - (n + i) = d - n - i by omega] at this

/-- **Closed programs ignore the environment** (safe runs). -/
theorem env_irrel {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s' : St K (fun _ => Sym) σ} {t : ℕ} (h : SafeEval framed ρ p s s' t) (hc : p.Closed)
    (ρ' : List (Prog K (fun _ => Sym) σ)) : SafeEval framed ρ' p s s' t :=
  h.env_congr (d := 0) hc (fun _ hi => absurd hi (Nat.not_lt_zero _))

end Env

section Lift

variable {K σ τ : Type} [DecidableEq K] {framed : K → Prop}

/-- **Register transport** for safe runs (mirror of `TMFw.Eval.liftRegs`): same stacks, same
side conditions, same cost; registers outside the lens are preserved. -/
theorem liftRegs (l : Lens σ τ) {ρ : List (Prog K (fun _ => Sym) τ)}
    {p : Prog K (fun _ => Sym) τ} {s s' : St K (fun _ => Sym) τ} {t : ℕ}
    (h : SafeEval framed ρ p s s' t) :
    ∀ v : σ, l.get v = s.var →
      SafeEval framed (ρ.map (Prog.liftRegs l)) (Prog.liftRegs l p) ⟨v, s.stk⟩
        ⟨l.set v s'.var, s'.stk⟩ t := by
  induction h with
  | push ρ k f w S =>
    intro v hv
    refine (SafeEval.push (framed := framed) (ρ.map (Prog.liftRegs l)) k
      (fun v => f (l.get v)) v S).of_final_eq ?_
    have hv' : l.get v = w := hv
    subst hv'
    show (⟨v, Function.update S k (f (l.get v) :: S k)⟩ : St K (fun _ => Sym) σ) =
      ⟨l.set v (l.get v), Function.update S k (f (l.get v) :: S k)⟩
    rw [l.set_get]
  | peek ρ k f w S hS =>
    intro v hv
    refine (SafeEval.peek (ρ.map (Prog.liftRegs l)) k (fun v o => l.set v (f (l.get v) o)) v S
      hS).of_final_eq ?_
    have hv' : l.get v = w := hv
    subst hv'
    rfl
  | pop ρ k f w S hS =>
    intro v hv
    refine (SafeEval.pop (ρ.map (Prog.liftRegs l)) k (fun v o => l.set v (f (l.get v) o)) v S
      hS).of_final_eq ?_
    have hv' : l.get v = w := hv
    subst hv'
    rfl
  | load ρ f w S =>
    intro v hv
    refine (SafeEval.load (framed := framed) (ρ.map (Prog.liftRegs l))
      (fun v => l.set v (f (l.get v))) v S).of_final_eq ?_
    have hv' : l.get v = w := hv
    subst hv'
    rfl
  | @seq ρ p q s₁ s₂ s₃ t₁ t₂ _ _ ih₁ ih₂ =>
    intro v hv
    have h₁ := ih₁ v hv
    have h₂ := ih₂ (l.set v s₂.var) (l.get_set _ _)
    rw [l.set_set] at h₂
    exact SafeEval.seq h₁ h₂
  | @ite_true ρ c p q s s' t hc _ ih =>
    intro v hv
    exact SafeEval.ite_true (ρ := ρ.map (Prog.liftRegs l)) (c := fun v => c (l.get v))
      (p := Prog.liftRegs l p) (q := Prog.liftRegs l q) (s := ⟨v, s.stk⟩)
      (by show c (l.get v) = true; rw [hv]; exact hc) (ih v hv)
  | @ite_false ρ c p q s s' t hc _ ih =>
    intro v hv
    exact SafeEval.ite_false (ρ := ρ.map (Prog.liftRegs l)) (c := fun v => c (l.get v))
      (p := Prog.liftRegs l p) (q := Prog.liftRegs l q) (s := ⟨v, s.stk⟩)
      (by show c (l.get v) = false; rw [hv]; exact hc) (ih v hv)
  | @loop_true ρ c p s s₁ s₂ t₁ t₂ hc _ _ ih₁ ih₂ =>
    intro v hv
    have h₁ := ih₁ v hv
    have h₂ := ih₂ (l.set v s₁.var) (l.get_set _ _)
    rw [l.set_set] at h₂
    exact SafeEval.loop_true (ρ := ρ.map (Prog.liftRegs l)) (c := fun v => c (l.get v))
      (p := Prog.liftRegs l p) (s := ⟨v, s.stk⟩)
      (by show c (l.get v) = true; rw [hv]; exact hc) h₁ h₂
  | @loop_false ρ c p s hc =>
    intro v hv
    have h := SafeEval.loop_false (framed := framed) (ρ := ρ.map (Prog.liftRegs l))
      (c := fun v => c (l.get v)) (p := Prog.liftRegs l p) (s := ⟨v, s.stk⟩)
      (by show c (l.get v) = false; rw [hv]; exact hc)
    refine h.of_final_eq ?_
    rw [← hv, l.set_get]
  | fix _ ih =>
    intro v hv
    exact SafeEval.fix (ih v hv)
  | @recur ρ n b s s' t hb _ ih =>
    intro v hv
    have hb' : (ρ.map (Prog.liftRegs l))[n]? = some (Prog.liftRegs l b) := by
      rw [getElem?_map', hb]; rfl
    refine SafeEval.recur hb' ?_
    rw [drop_map']
    exact ih v hv

end Lift

section Map

variable {L K σ : Type} [DecidableEq L] [DecidableEq K] {framedL : L → Prop} {framed : K → Prop}

/-- **Stack transport** for safe runs (mirror of `TMFw.Eval.mapStk`). The caller's framed stacks
in the image of `ι` must be framed for the component (`hF`): their non-emptiness side conditions
then come from the component's run. Stacks outside the image are untouched. -/
theorem mapStk {ι : L → K} (hι : Function.Injective ι) (hF : ∀ x, framed (ι x) → framedL x)
    {ρ : List (Prog L (fun _ => Sym) σ)} {p : Prog L (fun _ => Sym) σ}
    {s s' : St L (fun _ => Sym) σ} {t : ℕ} (h : SafeEval framedL ρ p s s' t) :
    ∀ T : K → List Sym, (∀ x, T (ι x) = s.stk x) →
      ∃ T' : K → List Sym, (∀ x, T' (ι x) = s'.stk x) ∧ (∀ k, (∀ x, ι x ≠ k) → T' k = T k) ∧
        SafeEval framed (ρ.map (Prog.mapStk ι)) (Prog.mapStk ι p) ⟨s.var, T⟩ ⟨s'.var, T'⟩ t := by
  induction h with
  | push _ k f v S =>
    intro T hT
    have hk : T (ι k) = S k := hT k
    refine ⟨Function.update T (ι k) (f v :: T (ι k)), ?_, ?_, SafeEval.push _ (ι k) f v T⟩
    · intro k₂
      rw [hk]
      exact update_comp_inj hι T S hT k _ k₂
    · intro k' hk'
      exact Function.update_of_ne (Ne.symm (hk' k)) _ _
  | peek _ k f v S hS =>
    intro T hT
    have hk : T (ι k) = S k := hT k
    have hne : framed (ι k) → T (ι k) ≠ [] := fun hfr => by rw [hk]; exact hS (hF k hfr)
    refine ⟨T, hT, fun _ _ => rfl, (SafeEval.peek _ (ι k) f v T hne).of_final_eq ?_⟩
    show (⟨f v (T (ι k)).head?, T⟩ : St K (fun _ => Sym) σ) = ⟨f v (S k).head?, T⟩
    rw [hk]
  | pop _ k f v S hS =>
    intro T hT
    have hk : T (ι k) = S k := hT k
    have hne : framed (ι k) → T (ι k) ≠ [] := fun hfr => by rw [hk]; exact hS (hF k hfr)
    refine ⟨Function.update T (ι k) (T (ι k)).tail, ?_, ?_,
      (SafeEval.pop _ (ι k) f v T hne).of_final_eq ?_⟩
    · intro k₂
      rw [hk]
      exact update_comp_inj hι T S hT k _ k₂
    · intro k' hk'
      exact Function.update_of_ne (Ne.symm (hk' k)) _ _
    · show (⟨f v (T (ι k)).head?, Function.update T (ι k) (T (ι k)).tail⟩ :
          St K (fun _ => Sym) σ) = ⟨f v (S k).head?, Function.update T (ι k) (T (ι k)).tail⟩
      rw [hk]
  | load _ f v S =>
    intro T hT
    exact ⟨T, hT, fun _ _ => rfl, SafeEval.load _ f v T⟩
  | seq _ _ ih₁ ih₂ =>
    intro T hT
    obtain ⟨T₁, h₁a, h₁b, e₁⟩ := ih₁ T hT
    obtain ⟨T₂, h₂a, h₂b, e₂⟩ := ih₂ T₁ h₁a
    exact ⟨T₂, h₂a, fun k' hk' => (h₂b k' hk').trans (h₁b k' hk'), SafeEval.seq e₁ e₂⟩
  | ite_true hc _ ih =>
    intro T hT
    obtain ⟨T', a, b, e⟩ := ih T hT
    exact ⟨T', a, b, SafeEval.ite_true hc e⟩
  | ite_false hc _ ih =>
    intro T hT
    obtain ⟨T', a, b, e⟩ := ih T hT
    exact ⟨T', a, b, SafeEval.ite_false hc e⟩
  | loop_true hc _ _ ih₁ ih₂ =>
    intro T hT
    obtain ⟨T₁, h₁a, h₁b, e₁⟩ := ih₁ T hT
    obtain ⟨T₂, h₂a, h₂b, e₂⟩ := ih₂ T₁ h₁a
    exact ⟨T₂, h₂a, fun k' hk' => (h₂b k' hk').trans (h₁b k' hk'),
      SafeEval.loop_true hc e₁ e₂⟩
  | loop_false hc =>
    intro T hT
    exact ⟨T, hT, fun _ _ => rfl, SafeEval.loop_false hc⟩
  | fix _ ih =>
    intro T hT
    obtain ⟨T', a, b, e⟩ := ih T hT
    exact ⟨T', a, b, SafeEval.fix e⟩
  | @recur ρ n b s s' t hb _ ih =>
    intro T hT
    obtain ⟨T', a, b', e⟩ := ih T hT
    have hb' : (ρ.map (Prog.mapStk ι))[n]? = some (Prog.mapStk ι b) := by
      rw [getElem?_map', hb]; rfl
    refine ⟨T', a, b', SafeEval.recur hb' ?_⟩
    rw [drop_map']
    exact e

end Map

section Append

variable {K σ : Type} [DecidableEq K] {framed : K → Prop}

/-- **Safety-preserving append.** Take a boundary-safe run, and append
tails `τ` below the framed stacks only (`τ k = []` when `k` is not framed). The result is a
boundary-safe run for the **same** framed set, from the extended state to the extended final
state, with the same final registers and the same cost. -/
theorem append_safe {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s' : St K (fun _ => Sym) σ} {t : ℕ} (h : SafeEval framed ρ p s s' t)
    (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    SafeEval framed ρ p ⟨s.var, appendTail s.stk τ⟩ ⟨s'.var, appendTail s'.stk τ⟩ t := by
  induction h with
  | push ρ k f v S =>
    refine (SafeEval.push (framed := framed) ρ k f v (appendTail S τ)).of_final_eq ?_
    show (⟨v, _⟩ : St K (fun _ => Sym) σ) = ⟨v, _⟩
    rw [appendTail_update]
    rfl
  | peek ρ k f v S hS =>
    have key : (S k ++ τ k).head? = (S k).head? := by
      by_cases hk : framed k
      · obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (hS hk)
        simp [hl]
      · rw [hτ k hk, List.append_nil]
    have hne : framed k → appendTail S τ k ≠ [] := by
      intro hk he
      apply hS hk
      simp only [appendTail_apply, List.append_eq_nil_iff] at he
      exact he.1
    refine (SafeEval.peek ρ k f v (appendTail S τ) hne).of_final_eq ?_
    show (⟨f v (S k ++ τ k).head?, _⟩ : St K (fun _ => Sym) σ) = ⟨f v (S k).head?, _⟩
    rw [key]
  | pop ρ k f v S hS =>
    have key : (S k ++ τ k).head? = (S k).head? ∧ (S k ++ τ k).tail = (S k).tail ++ τ k := by
      by_cases hk : framed k
      · obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (hS hk)
        simp [hl]
      · rw [hτ k hk, List.append_nil, List.append_nil]
        exact ⟨rfl, rfl⟩
    have hne : framed k → appendTail S τ k ≠ [] := by
      intro hk he
      apply hS hk
      simp only [appendTail_apply, List.append_eq_nil_iff] at he
      exact he.1
    refine (SafeEval.pop ρ k f v (appendTail S τ) hne).of_final_eq ?_
    show (⟨f v (S k ++ τ k).head?, Function.update (appendTail S τ) k (S k ++ τ k).tail⟩ :
      St K (fun _ => Sym) σ) = ⟨f v (S k).head?, appendTail (Function.update S k (S k).tail) τ⟩
    rw [key.1, key.2, appendTail_update]
  | load ρ f v S => exact SafeEval.load ρ f v (appendTail S τ)
  | seq _ _ ih₁ ih₂ => exact SafeEval.seq ih₁ ih₂
  | ite_true hc _ ih => exact SafeEval.ite_true hc ih
  | ite_false hc _ ih => exact SafeEval.ite_false hc ih
  | loop_true hc _ _ ih₁ ih₂ => exact SafeEval.loop_true hc ih₁ ih₂
  | loop_false hc => exact SafeEval.loop_false hc
  | fix _ ih => exact SafeEval.fix ih
  | recur hb _ ih => exact SafeEval.recur hb ih

end Append

end SafeEval

/-! ## Judgment-level transport rules -/

namespace SafeRunsIn

section Rules

variable {K σ : Type} [DecidableEq K] {framed : K → Prop}

/-- A closed safe component runs safely in any environment. -/
theorem env_irrel {ρ₀ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (hc : P.Closed)
    (h : SafeRunsIn framed ρ₀ P S S' Q T) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framed ρ P S S' Q T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨v', t, e.env_irrel hc ρ, hq, ht⟩

/-- **Safe register transport**: a closed safe component over registers `τ`, run through a lens,
in any environment. -/
theorem liftRegs {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ} {S S' : K → List Sym}
    {Q : τ → Prop} {T : ℕ} (hc : p.Closed) (h : SafeRunsIn framed [] p S S' Q T)
    (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framed ρ (p.liftRegs l) S S' (fun v => Q (l.get v)) T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h (l.get v)
  have e' := e.liftRegs l v rfl
  refine ⟨l.set v v', t, e'.env_irrel (WP.W9comp.closed_liftRegs l hc) ρ, ?_, ht⟩
  show Q (l.get (l.set v v'))
  rw [l.get_set]
  exact hq

/-- **Safe component call along an injective sub-layout** (`callInj`). The caller's framed stacks
in the image of `ι` must be framed for the component. The big final stacks agree with the
initial ones outside the image. -/
theorem callInj {L R : Type} [DecidableEq L] {framedL : L → Prop} {ι : L → K}
    (hι : Function.Injective ι) (hF : ∀ x, framed (ι x) → framedL x) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hc : P.Closed) (h : SafeRunsIn framedL [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framed ρ (SubNLogN.Machine.callInj ι l P) B B' (fun _ => True) T := by
  intro v
  obtain ⟨v', t, e, -, ht⟩ := h (l.get v)
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι hF B (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact h1 x
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  have e'' := e'.liftRegs l v rfl
  exact ⟨l.set v v', t, e''.env_irrel (closed_callInj ι l hc) ρ, trivial, ht⟩

/-- **Safe frame rule** (`frame_tail`). Tails appended
below the framed stacks only keep a safe run safe, for the same framed set and the same cost. -/
theorem frame_tail {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : SafeRunsIn framed ρ P S S' Q T)
    (τ : K → List Sym) (hτ : ∀ k, ¬ framed k → τ k = []) :
    SafeRunsIn framed ρ P (appendTail S τ) (appendTail S' τ) Q T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨v', t, e.append_safe τ hτ, hq, ht⟩

/-- Safety for fewer framed stacks. -/
theorem mono_framed {framed' : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : SafeRunsIn framed ρ P S S' Q T) (hf : ∀ k, framed' k → framed k) :
    SafeRunsIn framed' ρ P S S' Q T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨v', t, e.mono_framed hf, hq, ht⟩

/-- Any `RunsIn` fact is a safe run **with nothing framed**. This gives no access guarantee: it
only lets legacy facts be used where no stack is framed. -/
theorem of_runsIn_unframed {ρ : List (Prog K (fun _ => Sym) σ)} {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (h : RunsIn ρ P S S' Q T) :
    SafeRunsIn (fun _ => False) ρ P S S' Q T := by
  intro v
  obtain ⟨⟨v', S''⟩, t, e, ⟨hs', hq⟩, ht⟩ := h ⟨v, S⟩ rfl
  change S'' = S' at hs'
  subst hs'
  exact ⟨v', t, SafeEval.of_eval e, hq, ht⟩

end Rules

end SafeRunsIn

/-! ## The transport statements of `Safe.lean`, proved -/

/-- `SafeEnvIrrelStmt` holds. -/
theorem safeEnvIrrelStmt_holds : SafeEnvIrrelStmt := by
  intro K σ _ framed P S S' Q T hc h ρ
  exact SafeRunsIn.env_irrel hc h ρ

/-- `SafeLiftRegsStmt` holds. -/
theorem safeLiftRegsStmt_holds : SafeLiftRegsStmt := by
  intro K σ τ _ framed l p S S' Q T hc h ρ
  exact SafeRunsIn.liftRegs l hc h ρ

/-- `SafeCallInjStmt` holds. -/
theorem safeCallInjStmt_holds : SafeCallInjStmt := by
  intro L K σ R _ _ framedL framedK ι hι hF l P B B' Q T hc h hout ρ
  exact SafeRunsIn.callInj hι hF l hc h hout ρ

#assert_std_axioms SafeEval.env_congr SafeEval.env_irrel SafeEval.liftRegs SafeEval.mapStk
  SafeEval.append_safe SafeRunsIn.env_irrel SafeRunsIn.liftRegs SafeRunsIn.callInj
  SafeRunsIn.frame_tail SafeRunsIn.mono_framed SafeRunsIn.of_runsIn_unframed
  safeEnvIrrelStmt_holds safeLiftRegsStmt_holds safeCallInjStmt_holds

/-! ## Native safety certificates -/

section Native

variable {K σ : Type} [DecidableEq K]

/-- Safe runs are deterministic, even for different framed sets: final state and cost are
unique. -/
theorem SafeEval.det {framed framed' : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {p : Prog K (fun _ => Sym) σ} {s s₁ s₂ : St K (fun _ => Sym) σ} {t₁ t₂ : ℕ}
    (h₁ : SafeEval framed ρ p s s₁ t₁) (h₂ : SafeEval framed' ρ p s s₂ t₂) :
    s₁ = s₂ ∧ t₁ = t₂ :=
  h₁.eval.det h₂.eval

/-- **Safety-only witness.** From stacks `S` and every register value, `P`
has a boundary-safe run for `framed` in the environment `ρ`. This is a native operational
certificate. It does not follow from tail-polymorphic correctness. -/
def SafeOn (framed : K → Prop) (ρ : List (Prog K (fun _ => Sym) σ))
    (P : Prog K (fun _ => Sym) σ) (S : K → List Sym) : Prop :=
  ∀ v : σ, ∃ s' t, SafeEval framed ρ P ⟨v, S⟩ s' t

/-- A safe run carries its safety witness. -/
theorem SafeRunsIn.safeOn {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : SafeRunsIn framed ρ P S S' Q T) : SafeOn framed ρ P S := by
  intro v
  obtain ⟨v', t, e, -, -⟩ := h v
  exact ⟨_, _, e⟩

/-- **Native bridge.** Correctness (`RunsIn`) together with a native
safety witness gives a safe run with the same final stacks, postcondition and cost bound. The
proof uses determinism. -/
theorem SafeRunsIn.of_runsIn_safe {framed : K → Prop} {ρ : List (Prog K (fun _ => Sym) σ)}
    {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (h : RunsIn ρ P S S' Q T) (hsafe : SafeOn framed ρ P S) :
    SafeRunsIn framed ρ P S S' Q T := by
  intro v
  obtain ⟨⟨w, U⟩, t, e, ⟨hU, hq⟩, ht⟩ := h ⟨v, S⟩ rfl
  change U = S' at hU
  subst hU
  obtain ⟨z, u, ez⟩ := hsafe v
  obtain ⟨rfl, rfl⟩ := ez.eval.det e
  exact ⟨w, _, ez, hq, ht⟩

/-- **Native safe call.** A closed kernel with a `Runs` fact on the
restricted stacks and a native safety witness there gives a safe call along an injective
sub-layout. The hypothesis `hsafe` cannot be dropped: a `Runs` fact alone certifies no access
safety. -/
theorem SafeRunsIn.callInj_of_runs_safe {L R : Type} [DecidableEq L] {framedL : L → Prop}
    {framed : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framed (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    (hc : P.Closed) {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hsafe : SafeOn framedL [] P (B ∘ ι))
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    SafeRunsIn framed ρ (SubNLogN.Machine.callInj ι l P) B B' (fun _ => True) T :=
  SafeRunsIn.callInj hι hF l hc (SafeRunsIn.of_runsIn_safe (RunsIn.iff_runs.mpr hP) hsafe) hout ρ

end Native

#assert_std_axioms SafeEval.det SafeRunsIn.safeOn SafeRunsIn.of_runsIn_safe
  SafeRunsIn.callInj_of_runs_safe

end SubNLogN.Machine.Calculus
