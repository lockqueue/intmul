import WP.W9g.Base

/-!
# WP.W9g.Embed — running a kernel proved on local stacks `Loc n m` inside a host

Kernels that are used at several host positions (the rounding shift) are proved once on concrete
local stacks `Loc n m` (so every stack equality is decided by `simp`), then renamed into the host
along `locMap f pool` (`Prog.mapStk`), which is injective when `f` and `pool` are injective with
disjoint ranges (`locMap_inj`). `rs_mapStk` transports the exact-stack spec.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts

/-- Host placement of local stacks: named stacks along `f`, scratch along `pool`. -/
def locMap {K : Type} {n m : ℕ} (f : Fin n → K) (pool : Fin m → K) : Loc n m → K
  | .inl i => f i
  | .inr j => pool j

theorem locMap_inj {K : Type} {n m : ℕ} {f : Fin n → K} {pool : Fin m → K}
    (hf : ∀ i j, f i = f j → i = j) (hp : ∀ i j, pool i = pool j → i = j)
    (hd : ∀ i j, f i ≠ pool j) : Function.Injective (locMap f pool) := by
  rintro (i | j) (i' | j') h <;> simp only [locMap] at h
  · rw [hf i i' h]
  · exact absurd h (hd i j')
  · exact absurd h.symm (hd i' j)
  · rw [hp j j' h]

theorem mapStk_closed {L K A σ : Type} (ι : L → K) {p : Prog L (fun _ => A) σ} (h : p.Closed) :
    (p.mapStk ι).Closed :=
  (WP.W6a.freeBelow_mapStk ι p 0).2 h

section Rs

variable {L K σ : Type} [DecidableEq L] [DecidableEq K]

/-- **Transport of an exact-stack spec along an injective renaming.** -/
theorem rs_mapStk {ι : L → K} (hι : Function.Injective ι) {p : Prog L (fun _ => Sym) σ}
    {B B' : K → List Sym} {T : ℕ} (h : RS [] p (B ∘ ι) (B' ∘ ι) T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) : RS [] (p.mapStk ι) B B' T := by
  refine RS.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := h.eval v
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι B (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      rw [h1 x]
      rfl
    · push_neg at hk
      rw [h2 k hk, hout k hk]
  subst hT'
  exact ⟨v', t, e', ht⟩

/-- Single-update form. -/
theorem rs_mapStk_upd {ι : L → K} (hι : Function.Injective ι) {p : Prog L (fun _ => Sym) σ}
    {B : K → List Sym} (z : L) (x : List Sym) {T : ℕ}
    (h : RS [] p (B ∘ ι) (Function.update (B ∘ ι) z x) T) :
    RS [] (p.mapStk ι) B (Function.update B (ι z) x) T := by
  refine rs_mapStk hι ?_ ?_
  · rw [Function.update_comp_eq_of_injective B hι z x]
    exact h
  · intro k hk
    exact Function.update_of_ne (fun e => hk z e.symm) _ _

end Rs

#assert_std_axioms locMap_inj mapStk_closed rs_mapStk rs_mapStk_upd

end WP.W9g
