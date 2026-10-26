/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.PartsCost
import SubNLogN.Machine.CCore.NodeFacts

/-!
# C-core reduction: the `fix` induction (`CCore/Parts.lean`)

`PartsAux.core_fix_spec`: the C-core program `L.prog cdat` of the skeleton satisfies the C-core
specification at every call, with cost `Tm(V_g, k) + 2`. The proof is `SafeRunsIn.fix` on the
depth `k`. Its hypotheses:
* `NodeRunStmt` (the node run, `SkelNode.lean`);
* the big-layout kernel specifications `CoreTopSpecs`, `NodeSpecs`;
* the mathematical leaves in instantiated form: node values (M1), node growth (M2), child bands
  (M4), the child count (M5), encoding and header lengths (M6), `K ≥ 6` above the cutoff, and
  distinct slots of the Lemma A.9 row additions.

Child calls use the induction hypothesis at the child context `childRT t (k-1) a b'`, on the
visible part of the child's state, lifted to the full state by `SafeRunsIn.frame_tail` (the frame
tails are the content of `park` and the role stacks).
-/

namespace SubNLogN.Machine.CCore.PartsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks SubNLogN.Machine SubNLogN.Machine.CCore

variable {E σ : Type} [DecidableEq E]

/-- **The `fix` induction of the C-core.** -/
theorem core_fix_spec (hNR : NodeRunStmt) {p : LayerParams} {P₀ βn βd Estar : ℕ}
    {Erow : Stage × Fix 100 × Fin 8 → ℕ} {cH cL cS cC cPh cRA cG cR2I cPush cDrop cI2R : ℕ}
    (L : CoreProgs E σ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hTop : CoreTopSpecs p P₀ βn βd L cH cL)
    (hNode : NodeSpecs p P₀ L Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R)
    (hM1 : ∀ (t : CCoreRT) (hρ : t.ρ < t.K) (hg : t.j0 + t.e ≤ t.D)
      (z : RArr (LayerAddr t.A t.K t.D t.S) t.r), 1 ≤ t.k → 6 ≤ t.K → Wn ^ t.k ∣ t.A →
      ∀ u, restrictRole t u (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z) =
        mopsVal t (nodeCode cdat) (fun u' => restrictRole t u' z) (collectPerm u))
    (hM2 : ∀ (t : CCoreRT) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
      1 ≤ t.k → ¬ (mn ^ t.k) ^ βd < t.d ^ βn → Wn ^ t.k ∣ t.A →
      ArrGrowth t.P t.b z → t.b + cDepth t.d βn βd Estar t.k ≤ t.Δ →
      ∃ bs : ℕ → ℕ, ∀ (i : ℕ) (hi : i < (nodeCode cdat).length),
        opReq βn βd Estar Erow t (bs i) ((nodeCode cdat)[i])
          (mopsVal t ((nodeCode cdat).take i) (fun u => restrictRole t u z)))
    (hM4 : ChildBandsStmt p)
    (hM5 : ((nodeCode cdat).filter MOp.isChild).length = sn)
    (hM6a : ∀ (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
      (z : RArr (LayerAddr t.A t.K t.D t.S) t.r),
      CCoreBands p P₀ t → (Enc t hA hS z).length + 1 ≤ 2 * t.volG)
    (hM6b : ∀ t : CCoreRT, CCoreBands p P₀ t → t.hdr.length + 1 ≤ t.volG)
    (hK6 : ∀ t : CCoreRT, CCoreBands p P₀ t → 6 ≤ t.K)
    (hdist : ∀ u p₁ p₂, MOp.rowAdd u p₁ p₂ ∈ nodeCode cdat → p₁ ≠ p₂)
    (ρ : List (Prog (CL E) (fun _ => Sym) σ)) :
    ∀ x : {x : CallData E // x.Good p P₀ βn βd Estar},
      Calculus.SafeRunsIn ccoreFramed ρ (L.prog cdat) x.1.S x.1.out (fun _ => True)
        (Tm p.τ βn βd cH cL (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length)
          cRA ((nodeCode cdat).filter isRowAdd).length x.1.t.d x.1.t.K x.1.t.volG x.1.t.k + 2) := by
  refine Calculus.SafeRunsIn.fix (X := {x : CallData E // x.Good p P₀ βn βd Estar})
    (b := L.body cdat) (fun x => x.1.t.k) (S := fun x => x.1.S)
    (S' := fun x => x.1.out) (Q := fun _ _ => True)
    (T := fun x => Tm p.τ βn βd cH cL
      (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length) cRA
      ((nodeCode cdat).filter isRowAdd).length x.1.t.d x.1.t.K x.1.t.volG x.1.t.k) ?_
  intro x ih
  obtain ⟨⟨t, hA, hS, hρ, hg, z, tio, tdesc, S⟩, hband, hgr, hguard, hrest, hio, hdesc, hfr, hK⟩ := x
  dsimp only at hband hgr hguard hrest hio hdesc hfr hK
  show Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ)
    (.seq L.hdr (.ite L.obs L.leaf (L.nodeProg cdat))) S
    (Function.update S ioL (Enc t hA hS (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z) ++ tio))
    (fun _ => True)
    (Tm p.τ βn βd cH cL (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length) cRA
      ((nodeCode cdat).filter isRowAdd).length t.d t.K t.volG t.k)
  have hhdr := hTop.hdr (L.body cdat :: ρ) t tdesc S hband hK hdesc
  by_cases hleaf : t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn
  · -- a leaf: the leaf kernel
    have hh := Calculus.SafeRunsIn.mono (Q' := fun v => L.obs v = true) hhdr
      (fun v (hv : L.obs v = decide (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn)) => by
        rw [hv]; exact decide_eq_true hleaf) le_rfl
    have hg8 : t.b + 8 * t.e ≤ t.Δ := by
      have h8 := cDepth_leaf t.d βn βd Estar t.k hleaf
      rw [h8] at hguard
      exact hguard
    have hl := hTop.leaf (L.body cdat :: ρ) t hA hS hρ hg z tio tdesc S hband hgr hg8 hleaf hrest
      hio hdesc hfr hK
    exact Calculus.SafeRunsIn.mono (Calculus.SafeRunsIn.ite_true hh hl) (fun _ _ => trivial)
      (leaf_cost p.τ βn βd cH cL _ _ _ t.d t.K t.volG t.k hleaf)
  · -- an internal node: the node run
    have hk1 : 1 ≤ t.k := by
      rcases Nat.eq_zero_or_pos t.k with h | h
      · exact absurd (Or.inl h) hleaf
      · exact h
    have hnl : ¬ (mn ^ t.k) ^ βd < t.d ^ βn := fun h => hleaf (Or.inr h)
    have hh := Calculus.SafeRunsIn.mono (Q' := fun v => L.obs v = false) hhdr
      (fun v (hv : L.obs v = decide (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn)) => by
        rw [hv]; exact decide_eq_false hleaf) le_rfl
    have hWkA : Wn ^ t.k ∣ t.A := bands_dvd hband
    have hWA : Wn ∣ t.A := dvd_trans (dvd_pow_self Wn (by omega)) hWkA
    have hA' : 0 < t.A / Wn := Nat.div_pos (Nat.le_of_dvd hA hWA) Wn_pos
    have hK6' := hK6 t hband
    obtain ⟨bs, hbs⟩ := hM2 t z hk1 hnl hWkA hgr hguard
    have hV : 1 ≤ t.volG := volG_pos hband
    have hVcle : (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0).volG ≤ t.volG := by
      rw [childRT_volG t (t.k - 1) ⟨0, mn_pos⟩ 0 hWA]
      exact Nat.div_le_self _ _
    have hLenc : ∀ w, (Enc (compactRT t) hA' hS w).length + 1 ≤
        2 * (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0).volG := fun w =>
      hM6a (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0) hA' hS w
        (hM4 P₀ t (t.k - 1) ⟨0, mn_pos⟩ 0 hband (by omega))
    have hLhdr : ∀ a, (childHdr t a).length + 1 ≤ (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0).volG :=
      fun a => (hM6b (childRT t (t.k - 1) a 0) (hM4 P₀ t (t.k - 1) a 0 hband (by omega))).trans_eq
        (childRT_volG_indep t (t.k - 1) a ⟨0, mn_pos⟩ 0 0)
    have hIH : ∀ (u : Fin Wn) (a : Fin mn) (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r)
        (b' : ℕ) (Sc : CL E → List Sym),
        ArrGrowth t.P b' w → b' + cDepth t.d βn βd Estar (t.k - 1) ≤ t.Δ → KClean Sc →
        Sc ioL = Enc (compactRT t) hA' hS w ++ tio →
        Sc descL = childHdr t a ++ (t.hdr ++ tdesc) →
        Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ) (.recur 0) Sc
          (Function.update Sc ioL (Enc (compactRT t) hA' hS (childVal t a w) ++ tio))
          (fun _ => True)
          (Tm p.τ βn βd cH cL (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length)
            cRA ((nodeCode cdat).filter isRowAdd).length t.d t.K (t.volG / Wn) (t.k - 1) + 2) := by
      intro u a w b' Sc hgw hgd hKc hioc hdescc
      have hfit := child_fit t a hk1 hg
      have hb' := hM4 P₀ t (t.k - 1) a b' hband (by omega)
      have hy : CallData.Good p P₀ βn βd Estar
          (⟨childRT t (t.k - 1) a b', hA', hS, hρ, hfit, w, tio, t.hdr ++ tdesc, visC Sc⟩ :
            CallData E) :=
        ⟨hb', hgw, hgd, hrest, hioc, hdescc, visC_framed Sc, fun e => hKc e⟩
      have h : Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ) (.recur 0) (visC Sc)
          (CallData.out (⟨childRT t (t.k - 1) a b', hA', hS, hρ, hfit, w, tio, t.hdr ++ tdesc,
            visC Sc⟩ : CallData E)) (fun _ => True)
          (Tm p.τ βn βd cH cL (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length)
            cRA ((nodeCode cdat).filter isRowAdd).length t.d t.K
            (childRT t (t.k - 1) a b').volG (t.k - 1) + 2) :=
        ih ⟨_, hy⟩ (by show t.k - 1 < t.k; omega)
      have h2 := Calculus.SafeRunsIn.frame_tail h (tailC Sc) (tailC_unframed Sc)
      rw [appendTail_visC] at h2
      have hcv : childVal t a w = cCoreVal ⟨t.ρ, hρ⟩ (t.j0 + a.val * mn ^ (t.k - 1))
          (mn ^ (t.k - 1)) hfit w := by
        unfold childVal
        rw [dif_pos ⟨hρ, hfit⟩]
      have hout : Calculus.appendTail
          (CallData.out (⟨childRT t (t.k - 1) a b', hA', hS, hρ, hfit, w, tio, t.hdr ++ tdesc,
            visC Sc⟩ : CallData E)) (tailC Sc) =
          Function.update Sc ioL (Enc (compactRT t) hA' hS (childVal t a w) ++ tio) := by
        rw [hcv]
        exact appendTail_visC_update Sc _
      exact Calculus.SafeRunsIn.congr h2 hout (le_of_eq (congrArg (fun V => Tm p.τ βn βd cH cL
        (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length) cRA
        ((nodeCode cdat).filter isRowAdd).length t.d t.K V (t.k - 1) + 2)
        (childRT_volG t (t.k - 1) a b' hWA)))
    have hnode := hNR p P₀ βn βd Estar Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R L cdat hNode ρ t
      hA hS hA' z (cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z) tio tdesc S bs
      (2 * (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0).volG) (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0).volG
      (Tm p.τ βn βd cH cL (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length)
        cRA ((nodeCode cdat).filter isRowAdd).length t.d t.K (t.volG / Wn) (t.k - 1))
      hband hk1 hK6' hWA hdist hrest hio hdesc hfr hK hbs hLenc hLhdr hIH
      (hM1 t hρ hg z hk1 hK6' hWkA)
    refine Calculus.SafeRunsIn.mono (Calculus.SafeRunsIn.ite_false hh hnode) (fun _ _ => trivial) ?_
    have hS := sum_le_counts (nodeCode cdat)
      (nodeOpCost p.τ t cPh cRA cG cR2I cPush cDrop cI2R
        (2 * (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0).volG) (childRT t (t.k - 1) ⟨0, mn_pos⟩ 0).volG
        (Tm p.τ βn βd cH cL (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length)
          cRA ((nodeCode cdat).filter isRowAdd).length t.d t.K (t.volG / Wn) (t.k - 1)))
      (opC cPh cG cR2I cPush cDrop cI2R * t.volG) (cRA * (t.volG * (Utau p.τ (t.e * t.K) + 1)))
      (Tm p.τ βn βd cH cL (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length)
          cRA ((nodeCode cdat).filter isRowAdd).length t.d t.K (t.volG / Wn) (t.k - 1) + 2)
      (nodeOpCost_le p.τ t cPh cRA cG cR2I cPush cDrop cI2R _ _ _ (by omega) hVcle)
    rw [hM5] at hS
    rw [Tm_node p.τ βn βd cH cL _ cRA _ t.d t.K t.volG t.k hk1 hnl]
    exact node_arith cH cS cC t.volG _ (nodeCode cdat).length (opC cPh cG cR2I cPush cDrop cI2R)
      _ _ sn _ hV hS

/-- Bands are monotone in the cutoff. -/
theorem bandsMono {p : LayerParams} {P₀ P₁ : ℕ} {t : CCoreRT} (h : P₀ ≤ P₁)
    (hb : CCoreBands p P₁ t) : CCoreBands p P₀ t :=
  ⟨le_trans h hb.1, hb.2⟩

/-- `CoreTopSpecs` at a larger cutoff. -/
theorem topSpecs_mono {p : LayerParams} {P₀ P₁ βn βd : ℕ} {L : CoreProgs E σ} {cH cL : ℕ}
    (h : CoreTopSpecs p P₁ βn βd L cH cL) (hle : P₁ ≤ P₀) : CoreTopSpecs p P₀ βn βd L cH cL where
  hdr := fun ρ t tdesc S hb => h.hdr ρ t tdesc S (bandsMono hle hb)
  leaf := fun ρ t hA hS hρ hg z tio tdesc S hb =>
    h.leaf ρ t hA hS hρ hg z tio tdesc S (bandsMono hle hb)

/-- `NodeSpecs` at a larger cutoff. -/
theorem nodeSpecs_mono {p : LayerParams} {P₀ P₁ : ℕ} {L : CoreProgs E σ}
    {Erow : Stage × Fix 100 × Fin 8 → ℕ} {cS cC cPh cRA cG cR2I cPush cDrop cI2R : ℕ}
    (h : NodeSpecs p P₁ L Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R) (hle : P₁ ≤ P₀) :
    NodeSpecs p P₀ L Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R where
  split := fun ρ t hA hS hA' z tio tdesc S hb =>
    h.split ρ t hA hS hA' z tio tdesc S (bandsMono hle hb)
  coll := fun ρ t hA hS hA' z' tio tdesc S hb =>
    h.coll ρ t hA hS hA' z' tio tdesc S (bandsMono hle hb)
  phase := fun u κ ρ t hA' hS w b tdesc S hb =>
    h.phase u κ ρ t hA' hS w b tdesc S (bandsMono hle hb)
  rowAdd := fun u p₁ p₂ ρ t hA' hS w tdesc S hb =>
    h.rowAdd u p₁ p₂ ρ t hA' hS w tdesc S (bandsMono hle hb)
  gate := fun j ι r ρ t hA' hS w b tdesc S hb =>
    h.gate j ι r ρ t hA' hS w b tdesc S (bandsMono hle hb)
  r2i := h.r2i
  push := fun a ρ t tdesc S hb => h.push a ρ t tdesc S (bandsMono hle hb)
  drop := h.drop
  i2r := h.i2r

end SubNLogN.Machine.CCore.PartsAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks SubNLogN.Machine SubNLogN.Machine.CCore.PartsAux

/-- **The C-core contract from the skeleton parts.** Let `cdat` be valid complex edge data.
Assume the node run (`NodeRunStmt`), the layout plumbing (`SkelImpl`: programs for every kernel
instance on one big layout with their big-layout specifications), the mathematical leaves
`CCoreMathLeaves` and the value-level network premises of the node value statement (`ComplexNetCert`,
`RunEightSpecStmt`, `PackedAgreeStmt`, `PackedProcCorrectStmt`, `TranslationConjStmt`). Then
`CCoreStmt p βn βd` holds: the program is the skeleton's `L.prog cdat`, `E_*` comes from the
growth leaf (M2), the constant from the cost recursion (M3), and the cutoff is the maximum of
the cutoffs of the parts. -/
theorem cCore_of_parts (p : LayerParams) (βn βd : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hNR : NodeRunStmt) (himpl : SkelImpl p βn βd) (hmath : CCoreMathLeaves p βn βd cdat)
    (hnet : ComplexNetCert) (h8 : RunEightSpecStmt) (hpa : PackedAgreeStmt)
    (hpp : PackedProcCorrectStmt) (htc : TranslationConjStmt) (hval : ValidCdat cdat) :
    CCoreStmt p βn βd := by
  intro hβd hβn hOK hτ
  obtain ⟨hM1, hM2, hM3, hM4, hM5, hM6a, hM6b⟩ := hmath
  obtain ⟨E, iF, iD, σ, iFin, iNe, L, P₁, Erow, cH, cL, cS, cC, cPh, cRA, cG, cR2I, cPush, cDrop,
    cI2R, hcl, hTop, hNode⟩ := himpl
  have hM5' := hM5 hnet hval
  obtain ⟨Estar, hM2'⟩ := hM2 hval (le_of_eq hM5') Erow
  obtain ⟨C, P₃, hcost⟩ := hM3 hβd hβn hOK hτ cH cL
    (nodeCN cS cC cPh cG cR2I cPush cDrop cI2R (nodeCode cdat).length) cRA
    ((nodeCode cdat).filter isRowAdd).length
  obtain ⟨P₄, hEnc⟩ := hM6a
  obtain ⟨P₅, hHdr⟩ := hM6b
  obtain ⟨P₆, hK6⟩ := exists_K_ge p hOK 6
  have h1 : P₁ ≤ max (max P₁ P₃) (max (max P₄ P₅) P₆) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have h3 : P₃ ≤ max (max P₁ P₃) (max (max P₄ P₅) P₆) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have h4 : P₄ ≤ max (max P₁ P₃) (max (max P₄ P₅) P₆) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have h5 : P₅ ≤ max (max P₁ P₃) (max (max P₄ P₅) P₆) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have h6 : P₆ ≤ max (max P₁ P₃) (max (max P₄ P₅) P₆) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Estar, max (max P₁ P₃) (max (max P₄ P₅) P₆), C, fun _ => ⟨E, iF, iD, σ, L.prog cdat,
    iFin, iNe, CoreProgs.closed_prog L hcl cdat, ?_⟩⟩
  intro t hA hS hρ hg z tio tdesc S hband hgr hguard hrest hio hdesc hfr hK
  have key := core_fix_spec hNR L cdat (topSpecs_mono hTop h1) (nodeSpecs_mono hNode h1)
    (hM1 hnet h8 hpa hpp htc hval) hM2' hM4 hM5'
    (fun t' hA' hS' z' hb => hEnc t' hA' hS' z' (bandsMono h4 hb))
    (fun t' hb => hHdr t' (bandsMono h5 hb))
    (fun t' hb => hK6 _ t' h6 hb)
    (nodeCode_rowAdd_ne cdat hval) []
    ⟨⟨t, hA, hS, hρ, hg, z, tio, tdesc, S⟩, hband, hgr, hguard, hrest, hio, hdesc, hfr, hK⟩
  exact Calculus.SafeRunsIn.mono key (fun _ _ => trivial) (hcost t (bandsMono h3 hband))

/-- **The C-core contract from the node run, the layout plumbing and the mathematical inputs**
(`cCore_of_parts` with the inputs bundled). -/
theorem cCore_of_inputs (p : LayerParams) (βn βd : ℕ) (hNR : NodeRunStmt)
    (himpl : SkelImpl p βn βd) (hin : CCoreMathInputs p βn βd) : CCoreStmt p βn βd := by
  obtain ⟨cdat, hval, hmath, hnet, h8, hpa, hpp, htc⟩ := hin
  exact cCore_of_parts p βn βd cdat hNR himpl hmath hnet h8 hpa hpp htc hval

end SubNLogN.Machine.CCore
