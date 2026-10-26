import WP.W4.Steps

/-!
# WP.W9cS.Kernel — run a contract component inside the driver

`embedP ι lens P`: the component `P` (stacks `L`, registers `R`) with its stacks renamed along an
injective `ι : L → K` and its registers seen through `lens`. `embedP_runs` transports a `Runs`
triple (exact final stacks): stacks in the image of `ι` behave as in the component, all others are
unchanged, and the cost bound is the component's.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.W4

theorem freeBelow_liftRegs' {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), (p.liftRegs l).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_liftRegs' l p d) (freeBelow_liftRegs' l q d)
  | .ite _ p q, d => and_congr (freeBelow_liftRegs' l p d) (freeBelow_liftRegs' l q d)
  | .loop _ p, d => freeBelow_liftRegs' l p d
  | .fix b, d => freeBelow_liftRegs' l b (d + 1)
  | .recur _, _ => Iff.rfl

theorem freeBelow_mapStk' {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), (p.mapStk ι).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_mapStk' ι p d) (freeBelow_mapStk' ι q d)
  | .ite _ p q, d => and_congr (freeBelow_mapStk' ι p d) (freeBelow_mapStk' ι q d)
  | .loop _ p, d => freeBelow_mapStk' ι p d
  | .fix b, d => freeBelow_mapStk' ι b (d + 1)
  | .recur _, _ => Iff.rfl

/-- A component with renamed stacks and lensed registers. -/
def embedP {L K R σ : Type} (ι : L → K) (lens : Lens σ R) (P : Prog L (fun _ => Sym) R) :
    Prog K (fun _ => Sym) σ :=
  (P.mapStk ι).liftRegs lens

theorem embedP_closed {L K R σ : Type} (ι : L → K) (lens : Lens σ R)
    {P : Prog L (fun _ => Sym) R} (hc : P.Closed) : (embedP ι lens P).Closed :=
  (freeBelow_liftRegs' lens _ 0).2 ((freeBelow_mapStk' ι P 0).2 hc)

/-- **Transport of a component triple.** -/
theorem embedP_runs {L K R σ : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (lens : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {S S' : L → List Sym} {T : ℕ} (h : Runs P S S' (fun _ => True) T) (B B' : K → List Sym)
    (hB : ∀ l, B (ι l) = S l) (hB'1 : ∀ l, B' (ι l) = S' l)
    (hB'2 : ∀ k, (∀ l, ι l ≠ k) → B' k = B k) :
    RunsIn [] (embedP ι lens P) B B' T := by
  intro v
  obtain ⟨s', t, e, ⟨h1, h2, -⟩, ht⟩ := Runs.embed hι h B hB ⟨lens.get v, B⟩ rfl
  have hs' : s'.stk = B' := by
    funext k
    by_cases hk : ∃ l, ι l = k
    · obtain ⟨l, rfl⟩ := hk
      rw [h1 l, hB'1 l]
    · have hk' : ∀ l, ι l ≠ k := fun l hl => hk ⟨l, hl⟩
      rw [h2 k hk', hB'2 k hk']
  have e' := Eval.liftRegs lens e v rfl
  rw [hs'] at e'
  exact ⟨lens.set v s'.var, t, e', ht⟩

#assert_std_axioms freeBelow_liftRegs' freeBelow_mapStk' embedP_closed embedP_runs

end WP.W9c
