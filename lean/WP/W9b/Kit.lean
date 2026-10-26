import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Basic

/-!
# WP.W9b.Kit — composing components in `Runs` form

Every component of the W9b programs is specified by a `Runs P S S' Q T` statement
(`Contracts.Machine.Common`): exact stacks before and after, any register value on entry, a register
property `Q` afterwards, cost at most `T`. This file provides the combinators. The `runs_*`
combinators follow `WP.W0m.Kit` and the closedness lemmas follow `WP.W6a.Basic` (both are other
work packages; the statements are re-proved here so that W9b does not depend on them).

* `runs_seq`, `runs_mono`, `runs_post`, `runs_ite_true`, `runs_ite_false`;
* `runs_liftMacro`, `runs_liftRegs`: a component run through a register lens; `idLens`;
* `runs_embed`, `runs_embed_upd`, `runs_embed_upd2`: a component over local stacks, renamed along
  an injective stack map; `embL`, `embL_inj`: call-site stack maps of contract instances;
* `closed_liftRegs`, `closed_mapStk`: closedness is preserved by both renamings.
-/

namespace WP.W9b

open TMFw TMFw.Contracts

/-- The identity register lens. -/
def idLens (σ : Type) : Lens σ σ where
  get := id
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

section Kit

variable {K σ : Type} [DecidableEq K]

theorem runs_seq {P Q : Prog K (fun _ => Sym) σ} {S1 S2 S3 : K → List Sym} {Q1 Q2 : σ → Prop}
    {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1) (h2 : Runs Q S2 S3 Q2 T2) :
    Runs (.seq P Q) S1 S3 Q2 (T1 + T2) :=
  Triple.seq (Triple.post h1 fun _ hs => hs.1) h2

theorem runs_mono {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q Q' : σ → Prop}
    {T T' : ℕ} (h : Runs P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') : Runs P S S' Q' T' :=
  Triple.cost_mono (Triple.post h fun _ hs => ⟨hs.1, hQ _ hs.2⟩) hT

theorem runs_post {P : Prog K (fun _ => Sym) σ} {S S1 S2 : K → List Sym} {Q : σ → Prop}
    {T T' : ℕ} (h : Runs P S S1 Q T) (e : S1 = S2) (hT : T ≤ T') : Runs P S S2 Q T' := by
  subst e
  exact runs_mono h (fun _ h => h) hT

theorem runs_pre {P : Prog K (fun _ => Sym) σ} {S S0 S' : K → List Sym} {Q : σ → Prop}
    {T : ℕ} (h : Runs P S0 S' Q T) (e : S = S0) : Runs P S S' Q T := by
  subst e
  exact h

theorem runs_ite_true {P Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ}
    (h1 : Runs P S1 S2 (fun v => c v = true) T1) (h2 : Runs Pt S2 S3 Q T2) :
    Runs (.seq P (.ite c Pt Pf)) S1 S3 Q (T1 + (T2 + 1)) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc⟩, ht1⟩ := h1 s hs
  obtain ⟨s2, t2, e2, hq, ht2⟩ := h2 s1 hs1
  exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true hc e2), hq, by omega⟩

theorem runs_ite_false {P Pt Pf : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ}
    (h1 : Runs P S1 S2 (fun v => c v = false) T1) (h2 : Runs Pf S2 S3 Q T2) :
    Runs (.seq P (.ite c Pt Pf)) S1 S3 Q (T1 + (T2 + 1)) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc⟩, ht1⟩ := h1 s hs
  obtain ⟨s2, t2, e2, hq, ht2⟩ := h2 s1 hs1
  exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false hc e2), hq, by omega⟩

/-- A library macro (exact `Eval` for every register value) through a register lens. -/
theorem runs_liftMacro {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Qr : τ → Prop} {T : ℕ}
    (h : ∀ r : τ, ∃ r' t, Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t ∧ Qr r' ∧ t ≤ T) :
    Runs (p.liftRegs l) S S' (fun v => Qr (l.get v)) T := by
  intro s hs
  obtain ⟨r', t, e, hq, ht⟩ := h (l.get s.var)
  refine ⟨⟨l.set s.var r', S'⟩, t, ?_, ⟨rfl, ?_⟩, ht⟩
  · obtain ⟨v, stk⟩ := s
    change stk = S at hs
    subst hs
    exact Eval.liftRegs l e v rfl
  · show Qr (l.get (l.set s.var r'))
    rw [l.get_set]
    exact hq

/-- A `Runs` component through a register lens. -/
theorem runs_liftRegs {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs p S S' Q T) :
    Runs (p.liftRegs l) S S' (fun v => Q (l.get v)) T := by
  have h2 := Triple.liftRegs l h (fun _ => True) (fun _ _ _ => trivial)
  intro s hs
  obtain ⟨s', t, e, ⟨⟨hs1, hq⟩, -⟩, ht⟩ := h2 s ⟨hs, trivial⟩
  exact ⟨s', t, e, ⟨hs1, hq⟩, ht⟩

/-- `runs_liftRegs` with a trivial postcondition. -/
theorem runs_lift {τ : Type} (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs p S S' Q T) :
    Runs (p.liftRegs l) S S' (fun _ => True) T :=
  runs_mono (runs_liftRegs l h) (fun _ _ => trivial) le_rfl

/-- A local component renamed along an injective `ι`, with the big post-state given exactly. -/
theorem runs_embed {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {S S' : L → List Sym} {Q : R → Prop} {T : ℕ}
    (h : Runs P S S' Q T) (B B' : K → List Sym) (hB : ∀ x, B (ι x) = S x)
    (hB' : ∀ x, B' (ι x) = S' x) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (P.mapStk ι) B B' Q T := by
  have h2 := Runs.embed hι h B hB
  intro s hs
  obtain ⟨s', t, e, ⟨hin, hfr, hq⟩, ht⟩ := h2 s hs
  refine ⟨s', t, e, ⟨?_, hq⟩, ht⟩
  funext k
  by_cases hk : ∃ x, ι x = k
  · obtain ⟨x, rfl⟩ := hk
    rw [hin x, hB' x]
  · simp only [not_exists] at hk
    rw [hfr k hk, hout k hk]

theorem runs_embed_upd {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x0 : L)
    (v : List Sym)
    (h : Runs P (fun x => B (ι x)) (Function.update (fun x => B (ι x)) x0 v) Q T) :
    Runs (P.mapStk ι) B (Function.update B (ι x0) v) Q T := by
  refine runs_embed hι h B _ (fun _ => rfl) (fun x => ?_) (fun k hk => ?_)
  · by_cases hx : x = x0
    · subst hx
      simp
    · rw [Function.update_of_ne (hι.ne hx), Function.update_of_ne hx]
  · exact Function.update_of_ne (Ne.symm (hk x0)) _ _

theorem runs_embed_upd2 {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x0 x1 : L)
    (v0 v1 : List Sym)
    (h : Runs P (fun x => B (ι x))
      (Function.update (Function.update (fun x => B (ι x)) x0 v0) x1 v1) Q T) :
    Runs (P.mapStk ι) B (Function.update (Function.update B (ι x0) v0) (ι x1) v1) Q T := by
  refine runs_embed hι h B _ (fun _ => rfl) (fun x => ?_) (fun k hk => ?_)
  · by_cases hx1 : x = x1
    · subst hx1
      simp
    · rw [Function.update_of_ne (hι.ne hx1), Function.update_of_ne hx1]
      by_cases hx0 : x = x0
      · subst hx0
        simp
      · rw [Function.update_of_ne (hι.ne hx0), Function.update_of_ne hx0]
  · rw [Function.update_of_ne (Ne.symm (hk x1)), Function.update_of_ne (Ne.symm (hk x0))]

theorem runs_embed_same {L R : Type} [DecidableEq L] {ι : L → K} (hι : Function.Injective ι)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym)
    (h : Runs P (fun x => B (ι x)) (fun x => B (ι x)) Q T) : Runs (P.mapStk ι) B B Q T :=
  runs_embed hι h B B (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

end Kit

/-! ## Call-site stack maps -/

/-- Call-site stack map: named stacks via `named`, scratch stacks via `scr`. -/
def embL {K : Type} {n m : ℕ} (named : Fin n → K) (scr : Fin m → K) : Loc n m → K :=
  Sum.elim named scr

theorem embL_inj {K : Type} {n m : ℕ} {named : Fin n → K} {scr : Fin m → K}
    (h1 : Function.Injective named) (h2 : Function.Injective scr) (h3 : ∀ i j, named i ≠ scr j) :
    Function.Injective (embL named scr) := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (h1 h)
  · exact absurd h (h3 i j)
  · exact absurd h.symm (h3 j i)
  · exact congrArg Sum.inr (h2 h)

/-! ## Closedness -/

theorem freeBelow_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), (p.liftRegs l).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .ite _ p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .loop _ p, d => freeBelow_liftRegs l p d
  | .fix b, d => freeBelow_liftRegs l b (d + 1)
  | .recur _, _ => Iff.rfl

theorem freeBelow_mapStk {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), (p.mapStk ι).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .ite _ p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .loop _ p, d => freeBelow_mapStk ι p d
  | .fix b, d => freeBelow_mapStk ι b (d + 1)
  | .recur _, _ => Iff.rfl

theorem closed_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) {p : Prog K Γ τ}
    (h : p.Closed) : (p.liftRegs l).Closed :=
  (freeBelow_liftRegs l p 0).2 h

theorem closed_mapStk {K K' A σ : Type} (ι : K → K') {p : Prog K (fun _ => A) σ}
    (h : p.Closed) : (p.mapStk ι).Closed :=
  (freeBelow_mapStk ι p 0).2 h

#assert_std_axioms runs_seq runs_mono runs_post runs_pre runs_ite_true runs_ite_false
  runs_liftMacro runs_liftRegs runs_lift runs_embed runs_embed_upd runs_embed_upd2 runs_embed_same
  embL_inj freeBelow_liftRegs freeBelow_mapStk closed_liftRegs closed_mapStk

end WP.W9b
