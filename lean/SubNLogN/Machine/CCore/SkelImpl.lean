/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelLayout
import SubNLogN.Machine.CCore.PartsDefs

/-!
# C-core skeleton: the implementation from the leaf kernels (`CCore/SkelImpl.lean`)

`skelImpl_of_leaves : CCoreLeaves p βn βd → SkelImpl p βn βd`. One implementation is chosen per
kernel family (`KImpl.nonempty`), and they are bundled (`KBundle`). The big layout is then built
from the bundle:
* scratch = the sum of the families' Σ-scratch (one copy per static instance);
* registers = the product of the families' Π-registers;
* every kernel program is embedded by `callInj (embL ι) l`.
The big-layout specifications (`CoreTopSpecs`, `NodeSpecs`) follow from the leaf specifications by
`bigCall`/`bigCallQ`. The header test keeps its register flag through the lens.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-! ## Calls that keep the register postcondition -/

section CallQ

variable {K σ : Type} [DecidableEq K]

/-- `SafeRunsIn.callInj` that keeps the component's register postcondition through the lens. -/
theorem safeRunsIn_callInjQ {L R : Type} [DecidableEq L] {framedL : L → Prop}
    {framed : K → Prop} {ι : L → K} (hι : Function.Injective ι)
    (hF : ∀ x, framed (ι x) → framedL x) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ} (hc : P.Closed)
    (h : Calculus.SafeRunsIn framedL [] P (B ∘ ι) (B' ∘ ι) Q T)
    (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (ρ : List (Prog K (fun _ => Sym) σ)) :
    Calculus.SafeRunsIn framed ρ (callInj ι l P) B B' (fun v => Q (l.get v)) T := by
  intro v
  obtain ⟨v', t, e, hq, ht⟩ := h (l.get v)
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
  refine ⟨l.set v v', t, e''.env_irrel (closed_callInj ι l hc) ρ, ?_, ht⟩
  show Q (l.get (l.set v v'))
  rw [l.get_set]
  exact hq

end CallQ

/-- `bigCall`, keeping the register postcondition through the lens. -/
theorem bigCallQ {Eb : Type} [DecidableEq Eb] {Es : Type} [DecidableEq Es] {R σ : Type}
    {ι : Es → Eb} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog (KLoc (CCoreN Wn) Es) (fun _ => Sym) R} (hc : P.Closed) {B B' : CL Eb → List Sym}
    {Q : R → Prop} {T : ℕ}
    (h : Calculus.SafeRunsIn ccoreFramed [] P (B ∘ embL ι) (B' ∘ embL ι) Q T)
    (hout : ∀ e, B' (.inr e) = B (.inr e)) (ρ : List (Prog (CL Eb) (fun _ => Sym) σ)) :
    Calculus.SafeRunsIn ccoreFramed ρ (callInj (embL ι) l P) B B' (fun v => Q (l.get v)) T :=
  safeRunsIn_callInjQ (embL_injective hι) (framed_embL ι) l hc h
    (fun k hk => by
      rcases k with n | e
      · exact absurd rfl (hk (.inl n))
      · exact hout e) ρ

/-! ## The bundle of kernel implementations -/

/-- The type of a kernel specification with named stacks `CCoreN W`. -/
abbrev KSpec (Par : Type) : Type 1 :=
  Par → (E : Type) → [Fintype E] → [DecidableEq E] → (R : Type) → ℕ →
    Prog (KLoc (CCoreN Wn) E) (fun _ => Sym) R → Prop

/-- The eleven chosen kernel implementations, and the header test's flag. -/
structure KBundle (sh sl ss sd : KSpec Unit) (sc : KSpec (Equiv.Perm (Fin Wn)))
    (sph : KSpec (Fin Wn × PhaseKind)) (sra : KSpec (Fin Wn × Fin mn × Fin mn))
    (sg : KSpec (Stage × Fix 100 × Fin 8)) (sr si : KSpec (Fin Wn)) (sp : KSpec (Fin mn)) where
  /-- header test -/
  hdr : KImpl Unit sh
  /-- leaf kernel -/
  leaf : KImpl Unit sl
  /-- split -/
  split : KImpl Unit ss
  /-- collect -/
  coll : KImpl (Equiv.Perm (Fin Wn)) sc
  /-- phases -/
  phase : KImpl (Fin Wn × PhaseKind) sph
  /-- Lemma A.9 row additions -/
  rowAdd : KImpl (Fin Wn × Fin mn × Fin mn) sra
  /-- scalar rows -/
  gate : KImpl (Stage × Fix 100 × Fin 8) sg
  /-- role to io -/
  r2i : KImpl (Fin Wn) sr
  /-- push child header -/
  push : KImpl (Fin mn) sp
  /-- drop header -/
  drop : KImpl Unit sd
  /-- io to role -/
  i2r : KImpl (Fin Wn) si
  /-- the header test's flag -/
  obs : hdr.R () → Bool

namespace KBundle

variable {sh sl ss sd : KSpec Unit} {sc : KSpec (Equiv.Perm (Fin Wn))}
  {sph : KSpec (Fin Wn × PhaseKind)} {sra : KSpec (Fin Wn × Fin mn × Fin mn)}
  {sg : KSpec (Stage × Fix 100 × Fin 8)} {sr si : KSpec (Fin Wn)} {sp : KSpec (Fin mn)}
  (K : KBundle sh sl ss sd sc sph sra sg sr si sp)

/-- The big scratch: one region per kernel family, one copy per static instance. -/
abbrev E : Type :=
  K.hdr.E () ⊕ (K.leaf.E () ⊕ (K.split.E () ⊕ (K.coll.E collectPerm ⊕
    ((Σ q, K.phase.E q) ⊕ ((Σ q, K.rowAdd.E q) ⊕ ((Σ q, K.gate.E q) ⊕
      ((Σ u, K.r2i.E u) ⊕ ((Σ a, K.push.E a) ⊕ (K.drop.E () ⊕ (Σ u, K.i2r.E u))))))))))

/-- The big registers: one component per kernel family, one register file per static instance. -/
abbrev R : Type :=
  K.hdr.R () × (K.leaf.R () × (K.split.R () × (K.coll.R collectPerm ×
    ((∀ q, K.phase.R q) × ((∀ q, K.rowAdd.R q) × ((∀ q, K.gate.R q) ×
      ((∀ u, K.r2i.R u) × ((∀ a, K.push.R a) × (K.drop.R () × (∀ u, K.i2r.R u))))))))))

/-- Scratch injections. -/
def ιh : K.hdr.E () → K.E := fun e => Sum.inl e
def ιl : K.leaf.E () → K.E := fun e => Sum.inr (Sum.inl e)
def ιs : K.split.E () → K.E := fun e => Sum.inr (Sum.inr (Sum.inl e))
def ιc : K.coll.E collectPerm → K.E := fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))
def ιph (q : Fin Wn × PhaseKind) : K.phase.E q → K.E := fun e =>
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨q, e⟩))))
def ιra (q : Fin Wn × Fin mn × Fin mn) : K.rowAdd.E q → K.E := fun e =>
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨q, e⟩)))))
def ιg (q : Stage × Fix 100 × Fin 8) : K.gate.E q → K.E := fun e =>
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨q, e⟩))))))
def ιr (u : Fin Wn) : K.r2i.E u → K.E := fun e =>
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨u, e⟩)))))))
def ιp (a : Fin mn) : K.push.E a → K.E := fun e =>
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨a, e⟩))))))))
def ιd : K.drop.E () → K.E := fun e =>
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inl e)))))))))
def ιi (u : Fin Wn) : K.i2r.E u → K.E := fun e =>
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr ⟨u, e⟩)))))))))

theorem ιh_inj : Function.Injective K.ιh := fun a b h => by simpa [ιh] using h
theorem ιl_inj : Function.Injective K.ιl := fun a b h => by simpa [ιl] using h
theorem ιs_inj : Function.Injective K.ιs := fun a b h => by simpa [ιs] using h
theorem ιc_inj : Function.Injective K.ιc := fun a b h => by simpa [ιc] using h
theorem ιph_inj (q) : Function.Injective (K.ιph q) := fun a b h => by simpa [ιph] using h
theorem ιra_inj (q) : Function.Injective (K.ιra q) := fun a b h => by simpa [ιra] using h
theorem ιg_inj (q) : Function.Injective (K.ιg q) := fun a b h => by simpa [ιg] using h
theorem ιr_inj (u) : Function.Injective (K.ιr u) := fun a b h => by simpa [ιr] using h
theorem ιp_inj (a) : Function.Injective (K.ιp a) := fun a b h => by simpa [ιp] using h
theorem ιd_inj : Function.Injective K.ιd := fun a b h => by simpa [ιd] using h
theorem ιi_inj (u) : Function.Injective (K.ιi u) := fun a b h => by simpa [ιi] using h

/-- Register lenses. -/
def lh : Lens K.R (K.hdr.R ()) := Lens.fst _ _
def ll : Lens K.R (K.leaf.R ()) := (Lens.snd _ _).comp (Lens.fst _ _)
def ls : Lens K.R (K.split.R ()) := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lc : Lens K.R (K.coll.R collectPerm) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lph (q : Fin Wn × PhaseKind) : Lens K.R (K.phase.R q) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.fst _ _).comp (piLens q)))))
def lra (q : Fin Wn × Fin mn × Fin mn) : Lens K.R (K.rowAdd.R q) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.fst _ _).comp (piLens q))))))
def lg (q : Stage × Fix 100 × Fin 8) : Lens K.R (K.gate.R q) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.fst _ _).comp (piLens q)))))))
def lr (u : Fin Wn) : Lens K.R (K.r2i.R u) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      ((Lens.fst _ _).comp (piLens u))))))))
def lp (a : Fin mn) : Lens K.R (K.push.R a) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      ((Lens.fst _ _).comp (piLens a)))))))))
def ld : Lens K.R (K.drop.R ()) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      ((Lens.snd _ _).comp (Lens.fst _ _)))))))))
def li (u : Fin Wn) : Lens K.R (K.i2r.R u) :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      ((Lens.snd _ _).comp ((Lens.snd _ _).comp (piLens u))))))))))

/-- **The big C-core programs** of the bundle. -/
noncomputable def L : CoreProgs K.E K.R where
  hdr := callInj (embL K.ιh) K.lh (K.hdr.P ())
  obs := fun v => K.obs (K.lh.get v)
  leaf := callInj (embL K.ιl) K.ll (K.leaf.P ())
  split := callInj (embL K.ιs) K.ls (K.split.P ())
  coll := callInj (embL K.ιc) K.lc (K.coll.P collectPerm)
  phase := fun u κ => callInj (embL (K.ιph (u, κ))) (K.lph (u, κ)) (K.phase.P (u, κ))
  rowAdd := fun u p₁ p₂ =>
    callInj (embL (K.ιra (u, p₁, p₂))) (K.lra (u, p₁, p₂)) (K.rowAdd.P (u, p₁, p₂))
  gate := fun j ι r => callInj (embL (K.ιg (j, ι, r))) (K.lg (j, ι, r)) (K.gate.P (j, ι, r))
  r2i := fun u => callInj (embL (K.ιr u)) (K.lr u) (K.r2i.P u)
  push := fun a => callInj (embL (K.ιp a)) (K.lp a) (K.push.P a)
  drop := callInj (embL K.ιd) K.ld (K.drop.P ())
  i2r := fun u => callInj (embL (K.ιi u)) (K.li u) (K.i2r.P u)

theorem closed_L : K.L.Closed :=
  ⟨closed_callInj _ _ (K.hdr.closed ()), closed_callInj _ _ (K.leaf.closed ()),
    closed_callInj _ _ (K.split.closed ()), closed_callInj _ _ (K.coll.closed collectPerm),
    fun u κ => closed_callInj _ _ (K.phase.closed (u, κ)),
    fun u p₁ p₂ => closed_callInj _ _ (K.rowAdd.closed (u, p₁, p₂)),
    fun j ι r => closed_callInj _ _ (K.gate.closed (j, ι, r)),
    fun u => closed_callInj _ _ (K.r2i.closed u), fun a => closed_callInj _ _ (K.push.closed a),
    closed_callInj _ _ (K.drop.closed ()), fun u => closed_callInj _ _ (K.i2r.closed u)⟩

end KBundle

theorem framed_embL' {Eb Es : Type} (ι : Es → Eb) : ∀ x, ccoreFramed x → ccoreFramed (embL ι x)
  | .inl n, h => by cases n <;> exact h
  | .inr _, h => h.elim

/-- **The skeleton implementation from the leaf kernels** (`SkelImpl`, `CCore/PartsDefs.lean`). -/
theorem skelImpl_of_leaves (p : LayerParams) (βn βd : ℕ) (hL : CCoreLeaves p βn βd) :
    SkelImpl p βn βd := by
  obtain ⟨⟨P₀h, hH⟩, ⟨P₀p, hP⟩, hD, hR, hI, ⟨P₀s, hSp⟩, ⟨P₀c, hC⟩, ⟨P₀ph, hPh⟩, ⟨P₀ra, hRA⟩,
    ⟨P₀g, hG⟩, ⟨P₀l, hLf⟩⟩ := hL
  obtain ⟨Kh⟩ := KImpl.nonempty hH
  obtain ⟨Kp⟩ := KImpl.nonempty hP
  obtain ⟨Kd⟩ := KImpl.nonempty hD
  obtain ⟨Kr⟩ := KImpl.nonempty hR
  obtain ⟨Ki⟩ := KImpl.nonempty hI
  obtain ⟨Ks⟩ := KImpl.nonempty hSp
  obtain ⟨Kc⟩ := KImpl.nonempty hC
  obtain ⟨Kph⟩ := KImpl.nonempty hPh
  obtain ⟨Kra⟩ := KImpl.nonempty hRA
  obtain ⟨Kg⟩ := KImpl.nonempty hG
  obtain ⟨Kl⟩ := KImpl.nonempty hLf
  obtain ⟨obsH, hobsH⟩ := Kh.spec ()
  choose Erow hErow using Kg.spec
  let K : KBundle _ _ _ _ _ _ _ _ _ _ _ :=
    { hdr := Kh, leaf := Kl, split := Ks, coll := Kc, phase := Kph, rowAdd := Kra, gate := Kg,
      r2i := Kr, push := Kp, drop := Kd, i2r := Ki, obs := obsH }
  -- (instance search on the full nested sum `K.E` fails; its components are decidable)
  have instKE : DecidableEq K.E := Classical.decEq _
  refine ⟨K.E, inferInstance, instKE, K.R, inferInstance, inferInstance, K.L,
    P₀h + P₀p + P₀s + P₀c + P₀ph + P₀ra + P₀g + P₀l, Erow,
    Kh.C, Kl.C, Ks.C, Kc.C, Kph.C, Kra.C, Kg.C, Kr.C, Kp.C, Kd.C, Ki.C, K.closed_L, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro ρ t tdesc S hB hcl hdesc
      exact bigCallQ K.ιh_inj K.lh (Kh.closed ())
        (hobsH t tdesc _ (bands_mono (by omega) hB) (kclean_comp_embL _ hcl) hdesc)
        (fun _ => rfl) ρ
    · intro ρ t hA hS hρ hg z tio tdesc S hB hgr hdep hleaf htio hio hdesc hfr hcl
      refine bigCall (Q := fun _ => True) K.ιl_inj K.ll (Kl.closed ()) ?_ ?_ ρ
      · rw [update_comp_embL K.ιl_inj]
        exact Kl.spec () t hA hS hρ hg z tio tdesc _ (bands_mono (by omega) hB) hgr hdep hleaf
          htio hio hdesc (fun k hk => hfr _ (framed_embL' _ k hk)) (kclean_comp_embL _ hcl)
      · intro e
        exact Function.update_of_ne (by intro h; cases h) _ _
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- split
      intro ρ t hA hS hA' z tio tdesc S hB hW hcl htio hio hdesc hroles
      refine bigCall (Q := fun _ => True) K.ιs_inj K.ls (Ks.closed ()) ?_ ?_ ρ
      · rw [setRoles_comp_embL, update_comp_embL K.ιs_inj]
        exact Ks.spec () t hA hS hA' z tio tdesc _ (bands_mono (by omega) hB) hW
          (kclean_comp_embL _ hcl) htio hio hdesc hroles
      · intro e
        show Function.update S ioL _ (.inr e) = S (.inr e)
        exact Function.update_of_ne (by intro h; cases h) _ _
    · -- collect
      intro ρ t hA hS hA' z' tio tdesc S hB hW hcl htio hio hdesc hroles
      refine bigCall (Q := fun _ => True) K.ιc_inj K.lc (Kc.closed collectPerm) ?_ ?_ ρ
      · rw [setRoles_comp_embL, update_comp_embL K.ιc_inj]
        exact Kc.spec collectPerm t hA hS hA' z' tio tdesc _ (bands_mono (by omega) hB) hW
          (kclean_comp_embL _ hcl) htio hio hdesc hroles
      · intro e
        show Function.update S ioL _ (.inr e) = S (.inr e)
        exact Function.update_of_ne (by intro h; cases h) _ _
    · -- phase
      intro u κ ρ t hA' hS w b tdesc S hB hk hgr hb hcl hdesc hrole
      refine bigCall (Q := fun _ => True) (K.ιph_inj (u, κ)) (K.lph (u, κ)) (Kph.closed (u, κ)) ?_ ?_ ρ
      · rw [update_comp_embL (K.ιph_inj (u, κ))]
        exact Kph.spec (u, κ) t hA' hS w b tdesc _ (bands_mono (by omega) hB) hk hgr hb
          (kclean_comp_embL _ hcl) hdesc hrole
      · intro e
        exact Function.update_of_ne (by intro h; cases h) _ _
    · -- Lemma A.9 row addition
      intro u p₁ p₂ ρ t hA' hS w tdesc S hB hk hK6 hne hcl hdesc hrole
      refine bigCall (Q := fun _ => True) (K.ιra_inj (u, p₁, p₂)) (K.lra (u, p₁, p₂)) (Kra.closed (u, p₁, p₂)) ?_ ?_ ρ
      · rw [update_comp_embL (K.ιra_inj (u, p₁, p₂))]
        exact Kra.spec (u, p₁, p₂) t hA' hS w tdesc _ (bands_mono (by omega) hB) hk hK6 hne
          (kclean_comp_embL _ hcl) hdesc hrole
      · intro e
        exact Function.update_of_ne (by intro h; cases h) _ _
    · -- scalar row
      intro j ι r ρ t hA' hS w b tdesc S hB hgr hb hcl hdesc hroles
      refine bigCall (Q := fun _ => True) (K.ιg_inj (j, ι, r)) (K.lg (j, ι, r)) (Kg.closed (j, ι, r)) ?_ ?_ ρ
      · rw [setRoles_comp_embL]
        exact hErow (j, ι, r) t hA' hS w b tdesc _ (bands_mono (by omega) hB) hgr hb
          (kclean_comp_embL _ hcl) hdesc hroles
      · intro e
        rfl
    · -- role to io
      intro u ρ v tio S hcl hrole hio
      refine bigCall (Q := fun _ => True) (K.ιr_inj u) (K.lr u) (Kr.closed u) ?_ ?_ ρ
      · rw [update_comp_embL (K.ιr_inj u), update_comp_embL (K.ιr_inj u)]
        exact Kr.spec u v tio _ (kclean_comp_embL _ hcl) hrole hio
      · intro e
        rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h)]
    · -- push child header
      intro a ρ t tdesc S hB hk hcl hdesc
      refine bigCall (Q := fun _ => True) (K.ιp_inj a) (K.lp a) (Kp.closed a) ?_ ?_ ρ
      · rw [update_comp_embL (K.ιp_inj a)]
        exact Kp.spec a t tdesc _ (bands_mono (by omega) hB) hk (kclean_comp_embL _ hcl) hdesc
      · intro e
        exact Function.update_of_ne (by intro h; cases h) _ _
    · -- drop header
      intro ρ fs rest S hlen hcl hdesc
      refine bigCall (Q := fun _ => True) K.ιd_inj K.ld (Kd.closed ()) ?_ ?_ ρ
      · rw [update_comp_embL K.ιd_inj]
        exact Kd.spec () fs rest _ hlen (kclean_comp_embL _ hcl) hdesc
      · intro e
        exact Function.update_of_ne (by intro h; cases h) _ _
    · -- io to role
      intro u ρ v tio S hcl htio hio hrole
      refine bigCall (Q := fun _ => True) (K.ιi_inj u) (K.li u) (Ki.closed u) ?_ ?_ ρ
      · rw [update_comp_embL (K.ιi_inj u), update_comp_embL (K.ιi_inj u)]
        exact Ki.spec u v tio _ (kclean_comp_embL _ hcl) htio hio hrole
      · intro e
        rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h)]

#assert_std_axioms safeRunsIn_callInjQ bigCallQ skelImpl_of_leaves

end SubNLogN.Machine.CCore
