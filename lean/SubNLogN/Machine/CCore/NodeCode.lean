/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.NodeCodeRow

/-!
# C-core node code (III): the node code realizes `cxNodeOps` on role arrays (`CCore/NodeCode.lean`)

`nodeCode_transport`: at an internal node of the call `t` (`f = m^(t.k-1)`), running the value-level
`cxNodeOps` in the whole array (top class) with a child runner satisfying `IdealCrun` acts on the
compact role arrays (`Φ`) as the skeleton's value semantics `mopsVal t (nodeCode cdat)`, followed by
the relabel of `collect` (class `u` reads physical role `collectPerm u`).

Proof: the final relabel of `cxNodeOps` is `relabel_Φ`; the rest is simulated constructor by
constructor (`Sim crun … (nodeCode cdat)`), from the cases of `NodeCodeBase`/`NodeCodeRow`
(phases, Lemma A.9 row additions, child calls, scalar rows) and `sim_edge`/`sim_edgeAt` below.
Helpers are in `SubNLogN.Machine.CCore.NodeCodeAux`.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks Model

namespace NodeCodeAux

section Edges

variable {t : CCoreRT} {crun : Crun t}

theorem slotOf_eq {s : ℕ} (hs : s < mn) : slotOf s = ⟨s, hs⟩ := Fin.ext (Nat.mod_eq_of_lt hs)

/-- The kernel operations of one residual vector (slot `p.1`, sign `p.2`). -/
theorem sim_kern (hρ : t.ρ < t.K) (hcrun : IdealCrun t crun) (k : Fin Wc) (p : ℕ × ℤ)
    (hp : p.1 < mn) :
    Sim crun (CCoreEdgeAux.kernOps (A := t.A) (D := t.D) (S := t.S) (rr := t.r) ⟨t.ρ, hρ⟩
        (mn ^ (t.k - 1)) t.j0 id k p)
      (if p.2 = 1 then [MOp.child (toN k) (slotOf p.1)]
      else [MOp.phase (toN k) (.zSlot (slotOf p.1)), MOp.child (toN k) (slotOf p.1),
        MOp.phase (toN k) (.zSlot (slotOf p.1)), MOp.phase (toN k) .negIPow]) := by
  rw [slotOf_eq hp]
  unfold CCoreEdgeAux.kernOps
  by_cases h1 : p.2 = 1
  · rw [if_pos h1, if_pos h1]
    exact sim_call hcrun k p.1 hp
  · rw [if_neg h1, if_neg h1]
    refine sim_cons (sim_zSlot k ⟨p.1, hp⟩) (sim_cons (sim_call hcrun k p.1 hp)
      (sim_cons (sim_zSlot k ⟨p.1, hp⟩) (sim_cons (sim_recMap k _ .negIPow rfl) sim_nil)))

/-- The edge program of one edge (`coreEdgeOps`) is the skeleton's `edgeCode`. -/
theorem sim_edge (hρ : t.ρ < t.K) (hcrun : IdealCrun t crun) (hR8 : RunEightSpecStmt)
    (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt) (hK : 6 ≤ t.K)
    (hfit : t.j0 + mH * mn ^ (t.k - 1) ≤ t.D) (e : Vertex .complex 100 × Vertex .complex 100)
    (Dd : CxEdgeData) (hV : Dd.Valid e) (k : Fin Wc) :
    Sim crun (coreEdgeOps (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r) t.ρ
        (mn ^ (t.k - 1)) t.j0 Dd id k) (edgeCode Dd (toN k)) := by
  obtain ⟨hONB, heps, hdist, -, -, -⟩ := hV
  have hlen : Dd.basis.length ≤ mn := (CCoreEdgeAux.isONB_length_le' hONB).trans
    (le_of_eq mH_eq_mn)
  rw [show coreEdgeOps (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r) t.ρ
      (mn ^ (t.k - 1)) t.j0 Dd id k =
    coreEdgeOps (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r)
      (⟨t.ρ, hρ⟩ : Fin t.K).val (mn ^ (t.k - 1)) t.j0 Dd id k from rfl,
    CCoreEdgeAux.coreEdgeOps_eq]
  unfold edgeCode
  refine sim_append (sim_append ?_ ?_) ?_
  · exact sim_flatMap_map _ _ _ (fun p hp => sim_rowAdd hρ hR8 hPA hPP hK hfit k p
      (hdist p (List.mem_append_left _ hp)))
  · refine sim_flatMap _ _ _ (fun p hp => sim_kern hρ hcrun k p ?_)
    have := (List.of_mem_zip hp).1
    rw [List.mem_range] at this
    omega
  · exact sim_flatMap_map _ _ _ (fun p hp => sim_rowAdd hρ hR8 hPA hPP hK hfit k p
      (hdist p (List.mem_append_right _ hp)))

theorem edgeInto_mem'' {w : Role .complex 100} {v : Vertex .complex 100}
    {e : Vertex .complex 100 × Vertex .complex 100} (he : edgeInto w v = some e) : e ∈ edges w := by
  unfold edgeInto at he
  exact List.mem_of_find?_eq_some he

/-- The edge of wire `w` entering `v` (`coreEdgeOpsAt`) is the skeleton's `edgeCodeAt`. -/
theorem sim_edgeAt (hρ : t.ρ < t.K) (hcrun : IdealCrun t crun) (hR8 : RunEightSpecStmt)
    (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt) (hK : 6 ≤ t.K)
    (hfit : t.j0 + mH * mn ^ (t.k - 1) ≤ t.D)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (hval : ValidCdat cdat)
    (w : Role .complex 100) (v : Vertex .complex 100) :
    Sim crun (coreEdgeOpsAt (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r) t.ρ
        (mn ^ (t.k - 1)) t.j0 cdat id w v) (edgeCodeAt cdat w v) := by
  unfold coreEdgeOpsAt edgeCodeAt
  rcases he : edgeInto w v with _ | e
  · exact sim_nil
  · rw [roleIdxN_eq]
    exact sim_edge hρ hcrun hR8 hPA hPP hK hfit e (cdat e) (hval w e (edgeInto_mem'' he))
      (roleIdxC w)

end Edges

end NodeCodeAux

open NodeCodeAux in
/-- **Node-code transport** (C-core skeleton, node step). At an internal node of the call `t`
(`1 ≤ t.k`, `f = m^(t.k-1)`, `6 ≤ K`, `W ∣ A`, the group fits), with valid complex edge data, the Lemma A.9
statements, and a child runner that computes `childVal` on its slot (`IdealCrun`): running
node operations `cxNodeOps` in the whole array and reading role array `u` of the result is the
skeleton's value semantics `mopsVal t (nodeCode cdat)` on the role arrays, read at physical role
`collectPerm u` (the relabel fused into `collect`). (The divisibility hypothesis `W ∣ A` is part of the agreed interface but not needed by the proof.) -/
theorem nodeCode_transport (t : CCoreRT) (hρ : t.ρ < t.K) (h1 : 1 ≤ t.k) (hK : 6 ≤ t.K)
    (_hdiv : Wn ∣ t.A) (hg : t.j0 + t.e ≤ t.D) (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt)
    (hPP : PackedProcCorrectStmt) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ValidCdat cdat) (crun : Crun t) (hcrun : IdealCrun t crun)
    (Arr : (FL t).Addr → (Fin t.r → ℂ)) (u : Fin Wn) :
    Φ t (CCoreNode.runOps crun (topC t)
        (cxNodeOps (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r) t.ρ (mn ^ (t.k - 1))
          t.j0 cdat id) Arr) u =
      mopsVal t (nodeCode cdat) (Φ t Arr) (collectPerm u) := by
  have hfit : t.j0 + mH * mn ^ (t.k - 1) ≤ t.D := by
    have he : t.e = mH * mn ^ (t.k - 1) := by
      rw [CCoreRT.e, mH_eq_mn, ← pow_succ', Nat.sub_add_cancel h1]
    rw [← he]
    exact hg
  rw [cxNodeOps, nodeCode]
  simp only [roleIdxN_eq]
  rw [Φ_runOps_relabel]
  apply sim_apply
  refine sim_append (sim_append (sim_append ?_ ?_) ?_) ?_
  · exact sim_map _ _ _ (fun a _ => sim_zMask _ a)
  · refine sim_flatMap _ _ _ (fun j _ => sim_flatMap _ _ _ (fun ι _ => sim_flatMap _ _ _
      (fun r _ => sim_append (sim_flatMap _ _ _ (fun w _ => ?_)) (sim_gate j ι r))))
    cases gateAt j ι r w with
    | none => exact sim_nil
    | some g => exact sim_edgeAt hρ hcrun hR8 hPA hPP hK hfit cdat hval w _
  · exact sim_flatMap _ _ _ (fun w _ => sim_edgeAt hρ hcrun hR8 hPA hPP hK hfit cdat hval w _)
  · exact sim_flatMap _ _ _ (fun a _ => sim_cons (sim_zMask _ a)
      (sim_cons (sim_recMap _ _ .iPow27 rfl) (sim_cons (sim_recMap _ _ .neg rfl) sim_nil)))

end SubNLogN.Machine.CCore
