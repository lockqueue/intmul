import SubNLogN.Math.Networks.Proofs.CCoreEdgeCore

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations, part 3: from `Realizes` to the role-state interface `EdgeRoleSpec`

For the proof of `CCoreNode.CoreEdgeRoleSpecStmt` (`Proofs/CCoreRole.lean`). If an operation list
`ops` of the node in class `c` *realizes* (`CCoreEdgeAux.Realizes`, `Proofs/CCoreEdgeCore.lean`) the
edge matrix `T = (C_V C_U⁻¹)^{⊗f}` on role `roleIdxC w`, then `ops` changes the role state
(`CCoreNode.roleStateC`) of `w` by `cxEdgeOps f w e`, leaves the other role states unchanged, and
changes no address outside `c` (`roleSpec_of_realizes`). Helpers live in
`SubNLogN.Math.Networks.CCoreEdgeRoleAux`.

## Proof
* Role `w' ≠ w`: role addresses of `w'` lie in the role class of `w'` (`roleAddrC_mem`), which is
  disjoint from that of `w` (`sub_mem_unique`), so `opL` is the identity there.
* Role `w`: role addresses are `coreSet (alignL c k y) X`, and `coreX_coreSet`, `coreSet_coreSet`
  turn `opL T` into `applyCol T`.
* Outside `c`: every layout address is `encodeAddr (decodeAddr x)`, and a role class is contained
  in the node class (`mem_of_sub_mem`).
-/

namespace SubNLogN.Math.Networks

namespace CCoreEdgeRoleAux

open Model SubNLogN.Math.Walsh CCoreEdgeAux

/-- Distinct roles of a node have disjoint classes. -/
theorem sub_mem_unique {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k k' : Fin W)
    (x : L.Addr) (hk : (c.sub W hW k).mem x) (hk' : (c.sub W hW k').mem x) : k = k' := by
  rw [CCoreNode.sub_mem_iff] at hk hk'
  have hμ := c.hμ
  apply Fin.ext
  have h : c.μ * k.val = c.μ * k'.val := by omega
  exact Nat.eq_of_mul_eq_mul_left hμ h

/-- A role class is contained in the class of its node. -/
theorem mem_of_sub_mem {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W)
    (x : L.Addr) (hk : (c.sub W hW k).mem x) : c.mem x := by
  rw [CCoreNode.sub_mem_iff] at hk
  unfold RowClass.mem
  have hres := c.hres
  rw [← Nat.mod_mod_of_dvd _ (Dvd.intro W rfl), hk, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hres]

variable {A K D S rr : ℕ}

theorem roleAddrC_eq (c : RowClass (layerLayout A K D S)) (ρ : Fin K) (f j0 : ℕ) (k : Fin Wc)
    (X : Fin f → Pt 100) (y : LayerAddr A K D S) :
    CCoreNode.roleAddrC c ρ f j0 k X y = coreSet ρ f j0 (CCoreNode.alignL c k y) X := rfl

/-- **Role-state translation.** An operation list realizing `T = (C_V C_U⁻¹)^{⊗f}` on role
`roleIdxC w` acts on role states as `cxEdgeOps f w e` on `w`, as the identity on the other roles,
and changes no address outside `c`. -/
theorem roleSpec_of_realizes {ρ : Fin K} {f j0 : ℕ} {c : RowClass (layerLayout A K D S)}
    (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) {Child : Type}
    {crun : Child → RowClass (layerLayout A K D S) →
      ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ))}
    (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100)
    (ops : List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child))
    (hR : Realizes crun c (roleIdxC w) ρ f j0 ops
      (tpow f (frameC e.2) * (tpow f (frameC e.1))⁻¹))
    (Arr : (layerLayout A K D S).Addr → (Fin rr → ℂ)) :
    CCoreNode.roleStateC c ρ f j0 (CCoreNode.runOps crun c ops Arr) =
        Function.update (CCoreNode.roleStateC c ρ f j0 Arr) w
          (cxEdgeOps f w e (CCoreNode.roleStateC c ρ f j0 Arr w)) ∧
      ∀ x, ¬ c.mem x → CCoreNode.runOps crun c ops Arr x = Arr x := by
  have hpt : ∀ y : LayerAddr A K D S, CCoreNode.runOps crun c ops Arr (encodeAddr y) =
      opL ρ f j0 (roleP c (roleIdxC w)) (tpow f (frameC e.2) * (tpow f (frameC e.1))⁻¹)
        (decodeArr Arr) y := fun y => congrFun (hR Arr) y
  constructor
  · funext w' p
    obtain ⟨X, y, i⟩ := p
    by_cases hw : w' = w
    · subst hw
      rw [Function.update_self]
      simp only [CCoreNode.roleStateC, cxEdgeOps, applyCol]
      rw [hpt]
      have hmem : roleP c (roleIdxC w') (CCoreNode.roleAddrC c ρ f j0 (roleIdxC w') X y) :=
        CCoreNode.roleAddrC_mem hN (roleIdxC w') X y
      simp only [opL]
      rw [if_pos hmem, roleAddrC_eq, coreX_coreSet hN.fits]
      simp only [coreSet_coreSet, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    · rw [Function.update_of_ne hw]
      simp only [CCoreNode.roleStateC]
      rw [hpt]
      have hnot : ¬ roleP c (roleIdxC w) (CCoreNode.roleAddrC c ρ f j0 (roleIdxC w') X y) := by
        intro hP
        have h' : roleP c (roleIdxC w') (CCoreNode.roleAddrC c ρ f j0 (roleIdxC w') X y) :=
          CCoreNode.roleAddrC_mem hN (roleIdxC w') X y
        exact hw (roleIdxC.injective (sub_mem_unique c Wc Wc_pos _ _ _ h' hP))
      simp only [opL]
      rw [if_neg hnot]
      rfl
  · intro x hx
    have hx' : x = encodeAddr (decodeAddr x) := (CCoreNode.encodeAddr_decodeAddr x).symm
    rw [hx', hpt]
    have hnot : ¬ roleP c (roleIdxC w) (decodeAddr x) := by
      intro hP
      apply hx
      have h' := mem_of_sub_mem c Wc Wc_pos _ _ hP
      rwa [CCoreNode.encodeAddr_decodeAddr] at h'
    simp only [opL]
    rw [if_neg hnot]
    rfl

end CCoreEdgeRoleAux

end SubNLogN.Math.Networks
