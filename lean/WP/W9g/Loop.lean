import WP.W9g.Base

/-!
# WP.W9g.Loop — structural rules for `whileTop`

`whileTop_done` (the test fails: two steps) and `whileTop_step` (the test passes: one body run, then
the rest of the loop). Loop specifications are then proved by induction on the data the loop walks
over, with states written in terms of that data.
-/

namespace WP.W9g

open TMFw TMFw.Lib

section Loop

variable {K τ : Type} [DecidableEq K] {X : K} {c : Option Sym → Bool} {body : MProg K τ}
  {ρ : List (MProg K τ)}

theorem eval_seq_inv {p q : MProg K τ} {s s'' : St K (fun _ => Sym) (Option Sym × τ)} {t : ℕ}
    (h : Eval ρ (.seq p q) s s'' t) :
    ∃ s' t₁ t₂, Eval ρ p s s' t₁ ∧ Eval ρ q s' s'' t₂ ∧ t = t₁ + t₂ := by
  cases h with
  | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

/-- The test fails: the loop is done (one peek, one test). -/
theorem whileTop_done {S : K → List Sym} (hc : c (S X).head? = false) :
    RS ρ (whileTop X c body) S S 2 := by
  refine RS.of_eval fun v => ?_
  have e1 : Eval ρ (peekG X) ⟨v, S⟩ ⟨((S X).head?, v.2), S⟩ 1 := Eval.peek ρ X _ v S
  exact ⟨_, 2, Eval.seq e1 (Eval.loop_false (c := fun v : Option Sym × τ => c v.1) hc), le_rfl⟩

/-- The test passes: run the body once, then the rest of the loop. -/
theorem whileTop_step {S S' S'' : K → List Sym} {T₁ T₂ : ℕ} (hc : c (S X).head? = true)
    (hb : RS ρ body S S' T₁) (hl : RS ρ (whileTop X c body) S' S'' T₂) :
    RS ρ (whileTop X c body) S S'' (T₁ + T₂ + 2) := by
  refine RS.of_eval fun v => ?_
  have e1 : Eval ρ (peekG X) ⟨v, S⟩ ⟨((S X).head?, v.2), S⟩ 1 := Eval.peek ρ X _ v S
  obtain ⟨v1, t1, eb, ht1⟩ := hb.eval ((S X).head?, v.2)
  have ep : Eval ρ (peekG X) ⟨v1, S'⟩ ⟨((S' X).head?, v1.2), S'⟩ 1 := Eval.peek ρ X _ v1 S'
  obtain ⟨v2, t2, el, ht2⟩ := hl.eval v1
  obtain ⟨s', ta, tb, epk, eloop, hteq⟩ := eval_seq_inv el
  have hs' : s' = ⟨((S' X).head?, v1.2), S'⟩ := (epk.det (Eval.peek ρ X _ v1 S')).1
  have hta : ta = 1 := (epk.det (Eval.peek ρ X _ v1 S')).2
  subst hs'
  refine ⟨v2, 1 + (t1 + 1 + tb + 1), Eval.seq e1
    (Eval.loop_true (c := fun v : Option Sym × τ => c v.1) hc (Eval.seq eb ep) eloop), ?_⟩
  omega

/-- The test passes, with an explicit total bound. -/
theorem whileTop_step' {S S' S'' : K → List Sym} {T₁ T₂ T : ℕ} (hc : c (S X).head? = true)
    (hb : RS ρ body S S' T₁) (hl : RS ρ (whileTop X c body) S' S'' T₂)
    (hT : T₁ + T₂ + 2 ≤ T) : RS ρ (whileTop X c body) S S'' T :=
  (whileTop_step hc hb hl).mono hT

end Loop

#assert_std_axioms eval_seq_inv whileTop_done whileTop_step whileTop_step'

end WP.W9g
