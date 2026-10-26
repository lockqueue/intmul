import WP.W9g.Stk
import Contracts.W9.Common

/-!
# WP.W9gx.Embed — the leaf machine's stacks inside `BLoc 56`

`embS : Stk → BLoc 56` places `W0 TL TR C0 C1` on the named stacks of `BLoc` and the 56 other
stacks of W9g's leaf machine on the scratch stacks. It is injective (`unS` is a left inverse).
`rs_embS`: an exact-stack run on `Stk` that only changes `W0` is a `Runs` of the embedded program
on every `BLoc 56` state (stacks outside the image are untouched).
-/

namespace WP.W9gx

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9g

/-- Scratch index of the non-named stacks. -/
def embS : Stk → BLoc 56
  | .W0 => .inl .W0 | .TL => .inl .TL | .TR => .inl .TR | .C0 => .inl .C0 | .C1 => .inl .C1
  | .R => .inr 0 | .A => .inr 1 | .B => .inr 2 | .A2 => .inr 3 | .B2 => .inr 4 | .E => .inr 5
  | .O => .inr 6 | .Om => .inr 7 | .T1 => .inr 8 | .T2 => .inr 9 | .CS => .inr 10
  | .CK => .inr 11 | .CT => .inr 12 | .Q2 => .inr 13 | .ONE => .inr 14 | .SH => .inr 15
  | .DIR => .inr 16 | .HP => .inr 17 | .HK => .inr 18 | .HQ => .inr 19 | .HPin => .inr 20
  | .Na => .inr 21 | .Nb => .inr 22 | .Nc => .inr 23 | .Nd => .inr 24 | .Ne => .inr 25
  | .Nf => .inr 26 | .X1 => .inr 27 | .X2 => .inr 28 | .X3 => .inr 29 | .X4 => .inr 30
  | .X5 => .inr 31 | .X6 => .inr 32 | .X7 => .inr 33 | .X8 => .inr 34 | .X9 => .inr 35
  | .X10 => .inr 36 | .X11 => .inr 37 | .X12 => .inr 38 | .U1 => .inr 39 | .U2 => .inr 40
  | .U3 => .inr 41 | .RI => .inr 42 | .RO => .inr 43 | .Ra => .inr 44 | .Rc => .inr 45
  | .Rd => .inr 46 | .Sg => .inr 47
  | .pool i => .inr ⟨48 + i.val, by omega⟩

/-- The non-named stacks by scratch index (`< 48`). -/
def unIdx : ℕ → Stk
  | 0 => .R | 1 => .A | 2 => .B | 3 => .A2 | 4 => .B2 | 5 => .E | 6 => .O | 7 => .Om | 8 => .T1
  | 9 => .T2 | 10 => .CS | 11 => .CK | 12 => .CT | 13 => .Q2 | 14 => .ONE | 15 => .SH
  | 16 => .DIR | 17 => .HP | 18 => .HK | 19 => .HQ | 20 => .HPin | 21 => .Na | 22 => .Nb
  | 23 => .Nc | 24 => .Nd | 25 => .Ne | 26 => .Nf | 27 => .X1 | 28 => .X2 | 29 => .X3
  | 30 => .X4 | 31 => .X5 | 32 => .X6 | 33 => .X7 | 34 => .X8 | 35 => .X9 | 36 => .X10
  | 37 => .X11 | 38 => .X12 | 39 => .U1 | 40 => .U2 | 41 => .U3 | 42 => .RI | 43 => .RO
  | 44 => .Ra | 45 => .Rc | 46 => .Rd | _ => .Sg

/-- A left inverse of `embS`. -/
def unS : BLoc 56 → Stk
  | .inl .W0 => .W0
  | .inl .TL => .TL
  | .inl .TR => .TR
  | .inl .C0 => .C0
  | .inl .C1 => .C1
  | .inl _ => .W0
  | .inr j => if h : j.val < 48 then unIdx j.val else .pool ⟨j.val - 48, by omega⟩

theorem unS_embS : ∀ k : Stk, unS (embS k) = k
  | .pool i => by
    simp only [embS, unS]
    rw [dif_neg (by omega)]
    congr 1
    ext
    simp
  | .W0 => rfl | .TL => rfl | .TR => rfl | .C0 => rfl | .C1 => rfl
  | .R => rfl | .A => rfl | .B => rfl | .A2 => rfl | .B2 => rfl | .E => rfl | .O => rfl
  | .Om => rfl | .T1 => rfl | .T2 => rfl | .CS => rfl | .CK => rfl | .CT => rfl | .Q2 => rfl
  | .ONE => rfl | .SH => rfl | .DIR => rfl | .HP => rfl | .HK => rfl | .HQ => rfl | .HPin => rfl
  | .Na => rfl | .Nb => rfl | .Nc => rfl | .Nd => rfl | .Ne => rfl | .Nf => rfl | .X1 => rfl
  | .X2 => rfl | .X3 => rfl | .X4 => rfl | .X5 => rfl | .X6 => rfl | .X7 => rfl | .X8 => rfl
  | .X9 => rfl | .X10 => rfl | .X11 => rfl | .X12 => rfl | .U1 => rfl | .U2 => rfl | .U3 => rfl
  | .RI => rfl | .RO => rfl | .Ra => rfl | .Rc => rfl | .Rd => rfl | .Sg => rfl

theorem embS_injective : Function.Injective embS := fun a b h => by
  rw [← unS_embS a, ← unS_embS b, h]

/-- **Transport.** An exact run on `Stk` that only sets `W0` is a `Runs` on `BLoc 56`. -/
theorem rs_embS {R : Type} {P : Prog Stk (fun _ => Sym) R} {T : ℕ} (σ : BLoc 56 → List Sym)
    (v : List Sym) (h : RS [] P (σ ∘ embS) (Function.update (σ ∘ embS) .W0 v) T) :
    Runs (P.mapStk embS) σ (Function.update σ (.inl .W0) v) (fun _ => True) T := by
  have hrun : Runs P (σ ∘ embS) (Function.update (σ ∘ embS) .W0 v) (fun _ => True) T := by
    intro s hs
    obtain ⟨s', t, e, h1, ht⟩ := h s hs
    exact ⟨s', t, e, ⟨h1, trivial⟩, ht⟩
  have h2 := Runs.embed embS_injective hrun σ (fun _ => rfl)
  intro s hs
  obtain ⟨s', t, e, ⟨ha, hb, -⟩, ht⟩ := h2 s hs
  refine ⟨s', t, e, ⟨?_, trivial⟩, ht⟩
  funext k
  by_cases hk : ∃ l, embS l = k
  · obtain ⟨l, rfl⟩ := hk
    rw [ha l]
    by_cases hl : l = .W0
    · subst hl
      show Function.update (σ ∘ embS) Stk.W0 v Stk.W0 =
        Function.update σ (.inl .W0) v (.inl .W0)
      rw [Function.update_self, Function.update_self]
    · have hne : embS l ≠ (.inl .W0 : BLoc 56) := fun e =>
        hl (embS_injective (a₁ := l) (a₂ := .W0) e)
      rw [Function.update_of_ne hl, Function.update_of_ne hne]
      rfl
  · simp only [not_exists] at hk
    have hne : k ≠ (.inl .W0 : BLoc 56) := fun e => hk .W0 (by rw [e]; rfl)
    rw [hb k hk, Function.update_of_ne hne]

/-- Weaken the cost of a `Runs`. -/
theorem runs_mono {K R : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) R} {S S' : K → List Sym}
    {Q : R → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hT : T ≤ T') : Runs P S S' Q T' := by
  intro s hs
  obtain ⟨s', t, e, hq, ht⟩ := h s hs
  exact ⟨s', t, e, hq, ht.trans hT⟩

#assert_std_axioms unS_embS embS_injective rs_embS runs_mono

end WP.W9gx
