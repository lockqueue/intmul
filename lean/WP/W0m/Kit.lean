import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Basic

/-!
# WP.W0m.Kit — composing components in `Runs` form

Every step of the input stage is a `Runs P S S' Q T` statement (`Contracts.Machine.Common`):
* exact stacks before and after;
* any register value on entry;
* a register property `Q` afterwards;
* cost at most `T`.

This file provides the combinators:
* `runs_seq`, `runs_ite_true`, `runs_ite_false`, `runs_mono`;
* `runs_liftMacro`: a library macro with an exact `Eval` lemma, run through a register lens;
* `runs_liftRegs`: a `Runs` component run through a register lens;
* `runs_embed`, `runs_embed_upd`, `runs_embed_upd2`, `runs_embed_same`: a contract instance over
  local stacks, renamed into the input stage's stacks.
-/

namespace WP.W0m

open TMFw TMFw.Contracts

section Kit

variable {K σ : Type} [DecidableEq K]

theorem runs_seq {P Q : Prog K (fun _ => Sym) σ} {S1 S2 S3 : K → List Sym} {Q1 Q2 : σ → Prop}
    {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1) (h2 : Runs Q S2 S3 Q2 T2) :
    Runs (.seq P Q) S1 S3 Q2 (T1 + T2) :=
  Triple.seq (Triple.post h1 fun _ hs => hs.1) h2

theorem runs_mono {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q Q' : σ → Prop}
    {T T' : ℕ} (h : Runs P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') : Runs P S S' Q' T' :=
  Triple.cost_mono (Triple.post h fun _ hs => ⟨hs.1, hQ _ hs.2⟩) hT

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

#assert_std_axioms runs_seq runs_mono runs_ite_true runs_ite_false runs_liftMacro runs_liftRegs
  runs_embed runs_embed_upd runs_embed_upd2 runs_embed_same

end WP.W0m
