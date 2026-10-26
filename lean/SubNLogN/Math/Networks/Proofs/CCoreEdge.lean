import SubNLogN.Math.Networks.Proofs.CCoreEdgeTot
import SubNLogN.Math.Networks.Proofs.CCoreEdgeBits2
import SubNLogN.Math.Networks.Proofs.CCoreEdgeMat
import SubNLogN.Math.Networks.Proofs.CCoreEdgeChild
import SubNLogN.Math.Networks.Proofs.CCoreEdgeRole

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations, part 4: kernels, whole edge programs, and `CoreEdgeRoleSpecStmt`

Proof of `CCoreNode.CoreEdgeRoleSpecStmt` (`Proofs/CCoreRole.lean`): for valid edge data and children
computing `C^{⊗f}` on their slots, the edge program `coreEdgeOps` of every edge `e ∈ edges w` acts on
the role states as `cxEdgeOps f` (that is, `(C_V C_U⁻¹)^{⊗f}` on the columns of role `w`), leaves
the other roles unchanged and changes no address outside the node's class.

Files: `CCoreEdgeBits` (bit-level `addrXorAll`), `CCoreEdgeBits2`
(`addrXorAll_encode_holds`), `CCoreEdgeCore` (core coordinates, `opL`, `Realizes`, packed row words),
`CCoreEdgeTot` (total matrix), `CCoreEdgeMat` (`kv_conj_Z`), `CCoreEdgeChild`
(`cCoreVal_eq_core`), `CCoreEdgeRole` (`roleSpec_of_realizes`: a realized matrix
`T = (C_V C_U⁻¹)^{⊗f}` on role `w` is `cxEdgeOps f` on role states), this file (kernels, the whole
edge program, and the final theorem). Helpers in `SubNLogN.Math.Networks.CCoreEdgeAux`.

## Kernels
* `ε = 1`: one child; by `ChildSpecC` and the child conversion (`hcv`, `cCoreVal_eq_core`) it
  realizes `K_{e_t}^{⊗f}`;
* `ε ≠ 1`: `Z^{⊗f}` on slot `t` (`zSlot`, a diagonal sign), the child, `Z^{⊗f}`, and the scalar
  `(−i)^f`: the product is `(K_{e_t}^{-1})^{⊗f}` (`kv_conj_Z`).
-/

namespace SubNLogN.Math.Networks

namespace CCoreEdgeAux

open Model SubNLogN.Math.Walsh

variable {A K D S rr : ℕ} {Child : Type} {f j0 : ℕ}
variable {crun : Child → RowClass (layerLayout A K D S) →
  ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ))}

/-! ## 12. Kernel operations -/

/-- The kernel operations of `coreEdgeOps` for `(slot, sign)` (as in `AppCCore.lean`). -/
noncomputable def kernOps (ρ : Fin K) (f j0 : ℕ) (childOf : ℕ → Child) (k : Fin Wc) (p : ℕ × ℤ) :
    List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  if p.2 = 1 then [.call k (childOf p.1)]
  else [.prim k (zSlot ρ.val f j0 p.1), .call k (childOf p.1), .prim k (zSlot ρ.val f j0 p.1),
    .prim k (.recMap fun v => ((-Complex.I) ^ f) • v)]

theorem coreEdgeOps_eq (ρ : Fin K) (Dd : CxEdgeData) (childOf : ℕ → Child) (k : Fin Wc) :
    coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ.val f j0 Dd childOf k =
      Dd.rowsInv.flatMap (rowAddOps ρ f j0 k) ++
        ((List.range Dd.basis.length).zip Dd.eps).flatMap (kernOps ρ f j0 childOf k) ++
        Dd.rowsM.flatMap (rowAddOps ρ f j0 k) := rfl

/-- The sign of `zSlot` in core coordinates. -/
theorem zSlot_sign (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (t : ℕ) (ht : t < mH)
    (x : LayerAddr A K D S) :
    (-1 : ℂ) ^ (∑ col ∈ Finset.range f,
        slotBit (A := A) (D := D) (S := S) K ρ.val f j0 t col (encodeAddr x)) =
      ∏ col : Fin f, (-1 : ℂ) ^ (coreX ρ f j0 x col (cubeEquiv.symm ⟨t, ht⟩)).val := by
  rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_range]
  refine Finset.prod_congr rfl fun col _ => ?_
  have hlt : j0 + t * f + col.val < D := by
    have := tf_lt ht col.isLt
    omega
  rw [slotBit_encode ρ f j0 t col.val hlt x, coreX_apply ρ x col t ht]
  have hxb : xbit x (j0 + t * f + col.val) ρ.val = x.2.1 ⟨j0 + t * f + col.val, hlt⟩ ρ := by
    unfold xbit
    rw [dif_pos ⟨hlt, ρ.isLt⟩, Fin.eta]
  rw [hxb]
  cases x.2.1 ⟨j0 + t * f + col.val, hlt⟩ ρ <;> rfl

theorem realizes_zSlot {ρ : Fin K} {c : RowClass (layerLayout A K D S)}
    (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) (k : Fin Wc) (t : ℕ) (ht : t < mH) :
    Realizes crun c k ρ f j0 [RoleOp.prim k (zSlot ρ.val f j0 t)]
      (Matrix.diagonal fun X : Fin f → Pt 100 =>
        ∏ col, (-1 : ℂ) ^ (X col (cubeEquiv.symm ⟨t, ht⟩)).val) := by
  intro Arr
  rw [opL_diag _ hN.fits]
  funext x
  show (if (c.sub Wc Wc_pos k).mem (encodeAddr x) then
      (zSlot (A := A) (D := D) (S := S) (rr := rr) ρ.val f j0 t).run Arr (encodeAddr x)
      else Arr (encodeAddr x)) = _
  by_cases h : roleP c k x
  · rw [if_pos (show (c.sub Wc Wc_pos k).mem (encodeAddr x) from h), if_pos h]
    show ((-1 : ℂ) ^ (∑ col ∈ Finset.range f,
        slotBit (A := A) (D := D) (S := S) K ρ.val f j0 t col (encodeAddr x))) •
        Arr (encodeAddr x) = _
    rw [zSlot_sign hN.fits ρ t ht x]
    rfl
  · rw [if_neg (show ¬ (c.sub Wc Wc_pos k).mem (encodeAddr x) from h), if_neg h]
    rfl

theorem realizes_recMap {ρ : Fin K} {c : RowClass (layerLayout A K D S)}
    (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) (k : Fin Wc) (a : ℂ) :
    Realizes crun c k ρ f j0 [RoleOp.prim k (Step.recMap fun v => a • v)]
      (Matrix.diagonal fun _ : Fin f → Pt 100 => a) := by
  intro Arr
  rw [opL_diag _ hN.fits]
  funext x
  show (if (c.sub Wc Wc_pos k).mem (encodeAddr x) then a • Arr (encodeAddr x)
      else Arr (encodeAddr x)) = _
  by_cases h : roleP c k x
  · rw [if_pos (show (c.sub Wc Wc_pos k).mem (encodeAddr x) from h), if_pos h]
    rfl
  · rw [if_neg (show ¬ (c.sub Wc Wc_pos k).mem (encodeAddr x) from h), if_neg h]
    rfl

/-- The child conversion: `C^{⊗f}` on slot `t`, in core coordinates, is `K_{e_t}^{⊗f}`
(proved as `cCoreVal_eq_core` in `CCoreEdgeChild.lean`). -/
def ChildConvStmt (A K D S rr f j0 : ℕ) (hfit : j0 + mH * f ≤ D) (ρ : Fin K) : Prop :=
  ∀ (t : ℕ) (ht : t < mH) (z : RArr (LayerAddr A K D S) rr) (x : LayerAddr A K D S),
    cCoreVal ρ (j0 + t * f) f (CCoreNode.slot_le hfit ht) z x =
      ∑ Y, tpow f (Kv (Pi.single (cubeEquiv.symm ⟨t, ht⟩) 1) 1) (coreX ρ f j0 x) Y •
        z (coreSet ρ f j0 x Y)

theorem realizes_call {ρ : Fin K} {c : RowClass (layerLayout A K D S)}
    (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) {childOf : ℕ → Child}
    (hchild : CCoreNode.ChildSpecC c ρ f j0 hN.fits crun childOf)
    (hcv : ChildConvStmt A K D S rr f j0 hN.fits ρ) (k : Fin Wc) (t : ℕ) (ht : t < mH) :
    Realizes crun c k ρ f j0 [RoleOp.call k (childOf t)]
      (tpow f (Kv (Pi.single (cubeEquiv.symm ⟨t, ht⟩) 1) 1)) := by
  intro Arr
  have hrt : encodeArr (decodeArr Arr) = Arr := by
    funext y
    show Arr (encodeAddr (decodeAddr y)) = Arr y
    rw [CCoreNode.encodeAddr_decodeAddr]
  show decodeArr (crun (childOf t) (c.sub Wc Wc_pos k) Arr) = _
  conv_lhs => rw [← hrt]
  rw [hchild k t ht (decodeArr Arr)]
  funext x
  simp only [opL]
  by_cases h : roleP c k x
  · rw [if_pos h, if_pos (show (c.sub Wc Wc_pos k).mem (encodeAddr x) from h), hcv]
  · rw [if_neg h, if_neg (show ¬ (c.sub Wc Wc_pos k).mem (encodeAddr x) from h)]

theorem realizes_kern {ρ : Fin K} {c : RowClass (layerLayout A K D S)}
    (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) {childOf : ℕ → Child}
    (hchild : CCoreNode.ChildSpecC c ρ f j0 hN.fits crun childOf)
    (hcv : ChildConvStmt A K D S rr f j0 hN.fits ρ) (k : Fin Wc) (p : ℕ × ℤ) (hp : p.1 < mH) :
    Realizes crun c k ρ f j0 (kernOps ρ f j0 childOf k p)
      (tpow f (Kv (Pi.single (slotCoord p.1) 1) p.2)) := by
  rw [slotCoord_of_lt hp]
  unfold kernOps
  by_cases h1 : p.2 = 1
  · rw [if_pos h1, h1]
    exact realizes_call hN hchild hcv k p.1 hp
  · rw [if_neg h1, ← kv_conj_Z (cubeEquiv.symm ⟨p.1, hp⟩) p.2 h1 f]
    exact (((realizes_zSlot hN k p.1 hp).append hN.fits hN.row0
      (realizes_call hN hchild hcv k p.1 hp)).append hN.fits hN.row0
      (realizes_zSlot hN k p.1 hp)).append hN.fits hN.row0 (realizes_recMap hN k _)

/-! ## 13. The whole edge program -/

/-- The edge program of `e ∈ edges w` realizes `(C_V C_U⁻¹)^{⊗f}` on role `w`. -/
theorem realizes_edge (hcert : ComplexNetCert) (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt)
    (hPP : PackedProcCorrectStmt) {ρ : Fin K} {c : RowClass (layerLayout A K D S)}
    (hN : CCoreNode.NodeHypC A K D S ρ f j0 c)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) {childOf : ℕ → Child}
    (hchild : CCoreNode.ChildSpecC c ρ f j0 hN.fits crun childOf)
    (hcv : ChildConvStmt A K D S rr f j0 hN.fits ρ)
    (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100) (he : e ∈ edges w) :
    Realizes crun c (roleIdxC w) ρ f j0 (coreEdgeOps ρ.val f j0 (cdat e) childOf (roleIdxC w))
      (tpow f (frameC e.2) * (tpow f (frameC e.1))⁻¹) := by
  obtain ⟨hONB, heps, hdist, -, -, M, M', hMM', hcol, hM, hM'⟩ := hval w e he
  have hlen := isONB_length_le' hONB
  have hP8 := hcert.edge w e he (cdat e).basis hONB
  rw [coreEdgeOps_eq, heps]
  have h1 := realizes_word_perm (crun := crun) hPP hR8 hPA addrXorAll_encode_holds hN (roleIdxC w)
    (cdat e).rowsInv (fun p hp => hdist p (List.mem_append_left _ hp)) M M' hMM' hM'
  have h2 := realizes_word_perm (crun := crun) hPP hR8 hPA addrXorAll_encode_holds hN (roleIdxC w)
    (cdat e).rowsM (fun p hp => hdist p (List.mem_append_right _ hp)) M' M (cube_mul_comm hMM') hM
  have h3 := Realizes.flatMap hN.fits hN.row0
    ((List.range (cdat e).basis.length).zip ((cdat e).basis.map (epsC e)))
    (kernOps ρ f j0 childOf (roleIdxC w))
    (fun p => tpow f (Kv (Pi.single (slotCoord p.1) 1) p.2))
    (fun p hp => realizes_kern hN hchild hcv (roleIdxC w) p (by
      have := (List.of_mem_zip hp).1
      rw [List.mem_range] at this
      omega))
  have htot := (h1.append hN.fits hN.row0 h3).append hN.fits hN.row0 h2
  rw [← edge_total e (cdat e).basis hlen hP8 M M' hMM' hcol f]
  exact htot

end CCoreEdgeAux

/-- **Lemma A.10 (`lem:transfer-phase`) edge interface** (`CCoreNode.CoreEdgeRoleSpecStmt`, `Proofs/CCoreRole.lean`): under the
certificate ([OAI26] Prop. 8 for the edge frames), the Lemma A.9 (`lem:transfer13`) statements (`RunEightSpecStmt`, `PackedAgreeStmt`,
`PackedProcCorrectStmt`), the node hypotheses `NodeHypC`, valid edge data and children computing
`C^{⊗f}` on their slots (`ChildSpecC`), the edge program of every edge `e ∈ edges w` acts on role
`w` as `cxEdgeOps f` (`(C_V C_U⁻¹)^{⊗f}` on the columns), leaves the other roles unchanged and changes
no address outside the node's class. -/
theorem coreEdgeRoleSpec_holds : CCoreNode.CoreEdgeRoleSpecStmt := by
  intro hcert hR8 hPA hPP A K D S rr ρ f j0 c hN cdat hval Child crun childOf hchild w e he Arr
  exact CCoreEdgeRoleAux.roleSpec_of_realizes hN w e _
    (CCoreEdgeAux.realizes_edge hcert hR8 hPA hPP hN cdat hval hchild
      (fun t ht z x => cCoreVal_eq_core hN.fits ρ t ht z x) w e he) Arr

end SubNLogN.Math.Networks
