/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelNode

/-!
# C-core skeleton: proof of the node run (`CCore/SkelNodeRun.lean`)

`nodeRun_holds : NodeRunStmt`. The node state `nodeSt` describes the stacks during the node code:
* `io` holds its tail;
* role `u` holds `Enc (compactRT t) (w u) ++ [mark]`;
* every other stack is as at entry.

Each machine operation moves the node state from `w` to `mopVal t o w` (`opStep`): a role kernel
directly, a child operation through its five calls and the child oracle. The fixed node code is
then a safe fold (`SafeRunsIn.forEachProg`). Split enters the node state and collect leaves it.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

namespace NodeRunAux

variable {E : Type}

theorem setRoles_io (S : CL E → List Sym) (g : Fin Wn → List Sym) : setRoles S g ioL = S ioL := rfl
theorem setRoles_desc (S : CL E → List Sym) (g : Fin Wn → List Sym) :
    setRoles S g descL = S descL := rfl
theorem setRoles_park (S : CL E → List Sym) (g : Fin Wn → List Sym) :
    setRoles S g parkL = S parkL := rfl
theorem setRoles_role (S : CL E → List Sym) (g : Fin Wn → List Sym) (u : Fin Wn) :
    setRoles S g (roleL u) = g u := rfl
theorem setRoles_inr (S : CL E → List Sym) (g : Fin Wn → List Sym) (e : E) :
    setRoles S g (.inr e) = S (.inr e) := rfl

variable [DecidableEq E]

/-- The node state. -/
noncomputable def nodeSt (S : CL E → List Sym) (tio : List Sym) (t : CCoreRT)
    (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) : CL E → List Sym :=
  setRoles (Function.update S ioL tio) (fun u => Enc (compactRT t) hA' hS (w u) ++ [Sym.mark])

section NodeSt

variable (S : CL E → List Sym) (tio : List Sym) (t : CCoreRT) (hA' : 0 < t.A / Wn)
  (hS : 0 < t.S) (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r)

theorem nodeSt_io : nodeSt S tio t hA' hS w ioL = tio := by
  show Function.update S ioL tio ioL = tio
  exact Function.update_self _ _ _

theorem nodeSt_desc : nodeSt S tio t hA' hS w descL = S descL := by
  show Function.update S ioL tio descL = S descL
  exact Function.update_of_ne (by intro h; cases h) _ _

theorem nodeSt_park : nodeSt S tio t hA' hS w parkL = S parkL := by
  show Function.update S ioL tio parkL = S parkL
  exact Function.update_of_ne (by intro h; cases h) _ _

theorem nodeSt_role (u : Fin Wn) :
    nodeSt S tio t hA' hS w (roleL u) = Enc (compactRT t) hA' hS (w u) ++ [Sym.mark] := rfl

theorem nodeSt_inr (e : E) : nodeSt S tio t hA' hS w (.inr e) = S (.inr e) := by
  show Function.update S ioL tio (.inr e) = S (.inr e)
  exact Function.update_of_ne (by intro h; cases h) _ _

theorem kclean_nodeSt (hcl : KClean S) : KClean (nodeSt S tio t hA' hS w) := by
  intro e
  rw [nodeSt_inr]
  exact hcl e

/-- A role kernel's output on role `u` is the node state of the updated role arrays. -/
theorem nodeSt_update_role (u : Fin Wn) (v : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    Function.update (nodeSt S tio t hA' hS w) (roleL u)
        (Enc (compactRT t) hA' hS v ++ [Sym.mark]) =
      nodeSt S tio t hA' hS (Function.update w u v) := by
  funext k
  rcases k with ((_ | _ | _ | u') | e)
  · rw [Function.update_of_ne (by intro h; cases h)]; rfl
  · rw [Function.update_of_ne (by intro h; cases h)]; rfl
  · rw [Function.update_of_ne (by intro h; cases h)]; rfl
  · by_cases h : u' = u
    · subst h
      rw [Function.update_self]
      show _ = Enc (compactRT t) hA' hS (Function.update w u' v u') ++ [Sym.mark]
      rw [Function.update_self]
    · rw [Function.update_of_ne (by intro h'; cases h'; exact h rfl)]
      show Enc (compactRT t) hA' hS (w u') ++ [Sym.mark] =
        Enc (compactRT t) hA' hS (Function.update w u v u') ++ [Sym.mark]
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by intro h; cases h)]; rfl

/-- A kernel writing every role stream yields the node state of the new role arrays. -/
theorem setRoles_nodeSt (w' : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    setRoles (nodeSt S tio t hA' hS w) (fun u => Enc (compactRT t) hA' hS (w' u) ++ [Sym.mark]) =
      nodeSt S tio t hA' hS w' := by
  funext k
  rcases k with ((_ | _ | _ | u') | e) <;> rfl

end NodeSt

end NodeRunAux

namespace NodeRunAux

variable {E σ : Type} [DecidableEq E]

/-- **One machine operation** moves the node state from `w` to `mopVal t o w`, at the charged
cost `nodeOpCost`. -/
theorem opStep {p : LayerParams} {P₀ βn βd Estar : ℕ} {Erow : Stage × Fix 100 × Fin 8 → ℕ}
    {cS cC cPh cRA cG cR2I cPush cDrop cI2R : ℕ} {L : CoreProgs E σ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData}
    (hN : NodeSpecs p P₀ L Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R)
    (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (S : CL E → List Sym) (tio tdesc : List Sym) (Lenc Lhdr Tc : ℕ)
    (hB : CCoreBands p P₀ t) (hk : 1 ≤ t.k) (hK6 : 6 ≤ t.K) (htio : BlkTerm tio)
    (hdesc : S descL = t.hdr ++ tdesc) (hcl : KClean S)
    (hLenc : ∀ w, (Enc (compactRT t) hA' hS w).length + 1 ≤ Lenc)
    (hLhdr : ∀ a, (childHdr t a).length + 1 ≤ Lhdr)
    (IHk : ∀ (_u : Fin Wn) (a : Fin mn) (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r)
        (b' : ℕ) (Sc : CL E → List Sym),
        ArrGrowth t.P b' w → b' + cDepth t.d βn βd Estar (t.k - 1) ≤ t.Δ → KClean Sc →
        Sc ioL = Enc (compactRT t) hA' hS w ++ tio →
        Sc descL = childHdr t a ++ (t.hdr ++ tdesc) →
        Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ) (.recur 0) Sc
          (Function.update Sc ioL (Enc (compactRT t) hA' hS (childVal t a w) ++ tio))
          (fun _ => True) (Tc + 2))
    (o : MOp) (hdist : ∀ u p₁ p₂, o = MOp.rowAdd u p₁ p₂ → p₁ ≠ p₂) (b : ℕ)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r)
    (hreq : opReq βn βd Estar Erow t b o w) :
    Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ) (L.opProg o) (nodeSt S tio t hA' hS w)
      (nodeSt S tio t hA' hS (mopVal t o w)) (fun _ => True)
      (nodeOpCost p.τ t cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc o) := by
  have hdescN : nodeSt S tio t hA' hS w descL = t.hdr ++ tdesc := by
    rw [nodeSt_desc]; exact hdesc
  have hclN := kclean_nodeSt S tio t hA' hS w hcl
  cases o with
  | phase u κ =>
    obtain ⟨hg, hb⟩ := hreq
    have h := hN.phase u κ (L.body cdat :: ρ) t hA' hS (w u) b tdesc (nodeSt S tio t hA' hS w)
      hB hk hg hb hclN hdescN (nodeSt_role S tio t hA' hS w u)
    exact Calculus.SafeRunsIn.congr h (nodeSt_update_role S tio t hA' hS w u _) le_rfl
  | rowAdd u p₁ p₂ =>
    have h := hN.rowAdd u p₁ p₂ (L.body cdat :: ρ) t hA' hS (w u) tdesc
      (nodeSt S tio t hA' hS w) hB hk hK6 (hdist u p₁ p₂ rfl) hclN hdescN
      (nodeSt_role S tio t hA' hS w u)
    exact Calculus.SafeRunsIn.congr h (nodeSt_update_role S tio t hA' hS w u _) le_rfl
  | gate j ι r =>
    obtain ⟨hg, hb⟩ := hreq
    have h := hN.gate j ι r (L.body cdat :: ρ) t hA' hS w b tdesc (nodeSt S tio t hA' hS w)
      hB hg hb hclN hdescN (fun u => nodeSt_role S tio t hA' hS w u)
    exact Calculus.SafeRunsIn.congr h (setRoles_nodeSt S tio t hA' hS w _) le_rfl
  | child u a =>
    obtain ⟨hg, hb⟩ := hreq
    -- the record lists of the role stream before and after the child
    have hEv : Enc (compactRT t) hA' hS (w u) = arrSyms ((encArr (t.P + t.Δ)
        (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) (w u)).map (crecBits t.wg)) := rfl
    have hEv' : Enc (compactRT t) hA' hS (childVal t a (w u)) = arrSyms ((encArr (t.P + t.Δ)
        (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) (childVal t a (w u))).map
          (crecBits t.wg)) := rfl
    generalize hv : ((encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS)
      (w u)).map (crecBits t.wg)) = v at hEv
    generalize hv' : ((encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS)
      (childVal t a (w u))).map (crecBits t.wg)) = v' at hEv'
    have hne1 : (ioL : CL E) ≠ roleL u := by intro h; cases h
    have hne2 : (descL : CL E) ≠ roleL u := by intro h; cases h
    have hne3 : (descL : CL E) ≠ ioL := by intro h; cases h
    -- 1. role u → io
    have e1 := hN.r2i u (L.body cdat :: ρ) v tio (nodeSt S tio t hA' hS w) hclN
      ((nodeSt_role S tio t hA' hS w u).trans (congrArg (· ++ [Sym.mark]) hEv))
      (nodeSt_io S tio t hA' hS w)
    -- 2. push the child header
    have e2 := hN.push a (L.body cdat :: ρ) t tdesc
      (Function.update (Function.update (nodeSt S tio t hA' hS w) (roleL u) [Sym.mark]) ioL
        (arrSyms v ++ tio)) hB hk
      (by
        intro e
        rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h)]
        exact hclN e)
      (by
        rw [Function.update_of_ne hne3, Function.update_of_ne hne2]
        exact hdescN)
    -- 3. the child
    have e3 := IHk u a (w u) b
      (Function.update (Function.update (Function.update (nodeSt S tio t hA' hS w) (roleL u)
        [Sym.mark]) ioL (arrSyms v ++ tio)) descL (childHdr t a ++ (t.hdr ++ tdesc))) hg hb
      (by
        intro e
        rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h)]
        exact hclN e)
      ((Function.update_of_ne (Ne.symm hne3) _ _).trans
        ((Function.update_self _ _ _).trans (congrArg (· ++ tio) hEv.symm)))
      (Function.update_self _ _ _)
    -- 4. drop the child header (12 fields)
    have e4 := hN.drop (L.body cdat :: ρ)
      [t.P, t.d, t.r, t.Δ, t.A / Wn, t.R / Wn, t.K, t.D, t.S, t.j0 + a.val * mn ^ (t.k - 1),
        t.k - 1, t.ρ] (t.hdr ++ tdesc)
      (Function.update (Function.update (Function.update (Function.update
        (nodeSt S tio t hA' hS w) (roleL u) [Sym.mark]) ioL (arrSyms v ++ tio)) descL
          (childHdr t a ++ (t.hdr ++ tdesc))) ioL
        (Enc (compactRT t) hA' hS (childVal t a (w u)) ++ tio)) rfl
      (by
        intro e
        rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h)]
        exact hclN e)
      ((Function.update_of_ne hne3 _ _).trans (Function.update_self _ _ _))
    -- 5. io → role u
    have e5 := hN.i2r u (L.body cdat :: ρ) v' tio
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (nodeSt S tio t hA' hS w) (roleL u) [Sym.mark]) ioL (arrSyms v ++ tio)) descL
          (childHdr t a ++ (t.hdr ++ tdesc))) ioL
        (Enc (compactRT t) hA' hS (childVal t a (w u)) ++ tio)) descL (t.hdr ++ tdesc))
      (by
        intro e
        rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h)]
        exact hclN e)
      htio
      ((Function.update_of_ne (Ne.symm hne3) _ _).trans
        ((Function.update_self _ _ _).trans (congrArg (· ++ tio) hEv')))
      ((Function.update_of_ne (Ne.symm hne2) _ _).trans
        ((Function.update_of_ne (Ne.symm hne1) _ _).trans
          ((Function.update_of_ne (Ne.symm hne2) _ _).trans
            ((Function.update_of_ne (Ne.symm hne1) _ _).trans (Function.update_self _ _ _)))))
    have hc := Calculus.SafeRunsIn.seq e1 (Calculus.SafeRunsIn.seq e2
      (Calculus.SafeRunsIn.seq e3 (Calculus.SafeRunsIn.seq e4 e5)))
    refine Calculus.SafeRunsIn.congr hc ?_ ?_
    · funext k
      rcases k with ((_ | _ | _ | u') | e)
      · rw [Function.update_of_ne hne1, Function.update_self]
        exact (nodeSt_io S tio t hA' hS _).symm
      · rw [Function.update_of_ne hne2, Function.update_of_ne hne3, Function.update_self,
          nodeSt_desc]
        exact hdesc.symm
      · rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), nodeSt_park, nodeSt_park]
      · by_cases h : u' = u
        · subst h
          rw [Function.update_self]
          show arrSyms v' ++ [Sym.mark] =
            Enc (compactRT t) hA' hS (Function.update w u' (childVal t a (w u')) u') ++ [Sym.mark]
          rw [Function.update_self]
          exact congrArg (· ++ [Sym.mark]) hEv'.symm
        · have hr : (roleL u' : CL E) ≠ roleL u := by intro h'; cases h'; exact h rfl
          rw [Function.update_of_ne hr, Function.update_of_ne (by intro h; cases h),
            Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
            Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
            Function.update_of_ne hr]
          show Enc (compactRT t) hA' hS (w u') ++ [Sym.mark] =
            Enc (compactRT t) hA' hS (Function.update w u (childVal t a (w u)) u') ++ [Sym.mark]
          rw [Function.update_of_ne h]
      · rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h), nodeSt_inr, nodeSt_inr]
    · have h1 : (arrSyms v).length + 1 ≤ Lenc := by rw [← hEv]; exact hLenc (w u)
      have h2 : (arrSyms v').length + 1 ≤ Lenc := by rw [← hEv']; exact hLenc _
      have h3 : (hdrSyms [t.P, t.d, t.r, t.Δ, t.A / Wn, t.R / Wn, t.K, t.D, t.S,
          t.j0 + a.val * mn ^ (t.k - 1), t.k - 1, t.ρ]).length + 1 ≤ Lhdr := hLhdr a
      have m1 := Nat.mul_le_mul_left cR2I h1
      have m2 := Nat.mul_le_mul_left cI2R h2
      have m3 := Nat.mul_le_mul_left cDrop h3
      show _ ≤ cR2I * Lenc + cPush * t.volG + (Tc + 2) + cDrop * Lhdr + cI2R * Lenc
      omega

end NodeRunAux

/-- **The node run** (`NodeRunStmt`). -/
theorem nodeRun_holds : NodeRunStmt := by
  intro E σ _ p P₀ βn βd Estar Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R L cdat hN ρ t hA hS
    hA' z z' tio tdesc S bs Lenc Lhdr Tc hB hk hK6 hW hdist htio hio hdesc hfr hcl hreq hLenc
    hLhdr IHk hz'
  have hroles : ∀ u, S (roleL u) = [] := fun u => hfr (roleL u) trivial
  -- 1. split
  have e1 := hN.split (L.body cdat :: ρ) t hA hS hA' z tio tdesc S hB hW hcl htio hio hdesc hroles
  -- 2. the fixed node code
  have e2 : Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ)
      (forEachProg (nodeCode cdat) L.opProg)
      (NodeRunAux.nodeSt S tio t hA' hS
        (mopsVal t ((nodeCode cdat).take 0) (fun u => restrictRole t u z)))
      (NodeRunAux.nodeSt S tio t hA' hS
        (mopsVal t ((nodeCode cdat).take (nodeCode cdat).length) (fun u => restrictRole t u z)))
      (fun _ => True)
      (((nodeCode cdat).map
        (nodeOpCost p.τ t cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc)).sum + 1) := by
    refine Calculus.SafeRunsIn.forEachProg L.opProg
      (nodeOpCost p.τ t cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc) (nodeCode cdat)
      (fun i => NodeRunAux.nodeSt S tio t hA' hS
        (mopsVal t ((nodeCode cdat).take i) (fun u => restrictRole t u z))) ?_
    intro i hi
    have hstep := NodeRunAux.opStep hN ρ t hA' hS S tio tdesc Lenc Lhdr Tc hB hk hK6 htio hdesc
      hcl hLenc hLhdr IHk (nodeCode cdat)[i]
      (fun u p₁ p₂ h => hdist u p₁ p₂ (h ▸ List.getElem_mem hi)) (bs i)
      (mopsVal t ((nodeCode cdat).take i) (fun u => restrictRole t u z)) (hreq i hi)
    have htake : mopsVal t ((nodeCode cdat).take (i + 1)) (fun u => restrictRole t u z) =
        mopVal t (nodeCode cdat)[i]
          (mopsVal t ((nodeCode cdat).take i) (fun u => restrictRole t u z)) := by
      unfold mopsVal
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    show Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ) (L.opProg (nodeCode cdat)[i])
      (NodeRunAux.nodeSt S tio t hA' hS
        (mopsVal t ((nodeCode cdat).take i) (fun u => restrictRole t u z)))
      (NodeRunAux.nodeSt S tio t hA' hS
        (mopsVal t ((nodeCode cdat).take (i + 1)) (fun u => restrictRole t u z)))
      (fun _ => True) (nodeOpCost p.τ t cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc
        (nodeCode cdat)[i])
    rw [htake]
    exact hstep
  rw [List.take_length] at e2
  -- 3. collect
  have e3 := hN.coll (L.body cdat :: ρ) t hA hS hA' z' tio tdesc
    (NodeRunAux.nodeSt S tio t hA' hS (mopsVal t (nodeCode cdat) (fun u => restrictRole t u z)))
    hB hW (NodeRunAux.kclean_nodeSt S tio t hA' hS _ hcl) htio
    (NodeRunAux.nodeSt_io S tio t hA' hS _)
    (by rw [NodeRunAux.nodeSt_desc]; exact hdesc)
    (fun u => by rw [NodeRunAux.nodeSt_role, hz' u])
  have hc := Calculus.SafeRunsIn.seq e1 (Calculus.SafeRunsIn.seq e2 e3)
  refine Calculus.SafeRunsIn.congr hc ?_ (le_of_eq (by ring))
  funext k
  rcases k with ((_ | _ | _ | u) | e)
  · rfl
  · show Function.update (NodeRunAux.nodeSt S tio t hA' hS _) ioL _ descL =
      Function.update S ioL _ descL
    rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
      NodeRunAux.nodeSt_desc]
  · show Function.update (NodeRunAux.nodeSt S tio t hA' hS _) ioL _ parkL =
      Function.update S ioL _ parkL
    rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
      NodeRunAux.nodeSt_park]
  · show ([] : List Sym) = Function.update S ioL _ (roleL u)
    rw [Function.update_of_ne (by intro h; cases h), hroles u]
  · show Function.update (NodeRunAux.nodeSt S tio t hA' hS _) ioL _ (.inr e) =
      Function.update S ioL _ (.inr e)
    rw [Function.update_of_ne (by intro h; cases h), Function.update_of_ne (by intro h; cases h),
      NodeRunAux.nodeSt_inr]

#assert_std_axioms NodeRunAux.opStep nodeRun_holds

end SubNLogN.Machine.CCore
