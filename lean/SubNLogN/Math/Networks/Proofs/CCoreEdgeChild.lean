import SubNLogN.Math.Networks.Proofs.CCoreEdgeCore

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations: one child call in core coordinates (`cCoreVal_eq_core`)

The child `C^{⊗f}` on slot `t` of a Lemma A.10 (`lem:transfer-phase`) node (chunks `j0 + t f, …, j0 + t f + f − 1`, selected bit
`ρ`), written in the core coordinates of the node (`CCoreEdgeAux.coreX`, `coreSet`: column `col`,
coordinate `p` = bit `ρ` of chunk `j0 + (cubeEquiv p) f + col`), is the coordinate kernel
`(aI + bX_{e_t})^{⊗f}` with `e_t = cubeEquiv.symm t` (Lemma A.10 (`lem:transfer-phase`)). No hypotheses
beyond the fit `j0 + m f ≤ D` and `t < m`.

Proof. By `kernelSlot_holds`, the kernel entries vanish unless `Y` agrees with `coreX x` off the
coordinate `e_t`, and then they are `C^{⊗f}` on the bits of `e_t`. Such `Y` correspond bijectively to
the bit vectors `bs` of the slot (`Yof`, inverse `Y ↦ (Y col e_t = 1)`), and
`coreSet x (Yof bs) = groupSel ρ (j0 + t f) f x bs` (`coreSet_Yof`, by `layerAddr_ext`).
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh

namespace CCoreEdgeChildAux

open CCoreEdgeAux

variable {A K D S : ℕ}

/-- The core point of `x` with the coordinate `e` of every column replaced by the bits `bs`. -/
def Yof (ρ : Fin K) (f j0 : ℕ) (x : LayerAddr A K D S) (e : Cube 100) (bs : Fin f → Bool) :
    Fin f → Pt 100 :=
  fun c p => if p = e then (if bs c then 1 else 0) else coreX ρ f j0 x c p

/-- Overwriting the core bits by `Yof bs` is overwriting the slot `t` by `bs`. -/
theorem coreSet_Yof {f j0 : ℕ} (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (t : ℕ) (ht : t < mH)
    (x : LayerAddr A K D S) (bs : Fin f → Bool) :
    coreSet ρ f j0 x (Yof ρ f j0 x (cubeEquiv.symm ⟨t, ht⟩) bs) = groupSel ρ (j0 + t * f) f x bs := by
  have htf : t * f + f ≤ mH * f := by
    have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt ht)
    rwa [Nat.succ_mul] at this
  refine layerAddr_ext ?_ ?_ ?_
  · rfl
  · rfl
  intro ch t'
  by_cases hg : t' = ρ.val ∧ j0 ≤ ch ∧ ch < j0 + mH * f
  · obtain ⟨rfl, h1, h2⟩ := hg
    obtain ⟨t2, col, ht2, hcol, rfl⟩ := group_decomp h1 h2
    rw [xbit_coreSet_sel hfit ρ x _ t2 col ht2 hcol]
    by_cases htt : t2 = t
    · have htf2 : t2 * f = t * f := by rw [htt]
      have hee : cubeEquiv.symm (⟨t2, ht2⟩ : Fin mH) = cubeEquiv.symm ⟨t, ht⟩ := by
        congr 1
        exact Fin.ext htt
      rw [xbit_groupSel_sel ρ (j0 + t * f) f x bs (j0 + t2 * f + col) (by omega) (by omega)
        (by omega)]
      simp only [Yof, hee, if_true]
      rw [decide_ite_bool]
      congr 1
      apply Fin.ext
      simp only
      omega
    · have hne : cubeEquiv.symm (⟨t2, ht2⟩ : Fin mH) ≠ cubeEquiv.symm ⟨t, ht⟩ := by
        intro h
        exact htt (congrArg Fin.val (cubeEquiv.symm.injective h))
      simp only [Yof, if_neg hne]
      rw [coreX_apply ρ x ⟨col, hcol⟩ t2 ht2, decide_ite_bool]
      symm
      apply xbit_groupSel_other
      rintro ⟨_, h1', h2'⟩
      exact htt ((slot_mem_iff hcol).1 ⟨by omega, by omega⟩)
  · rw [xbit_coreSet_other ρ x _ ch t' hg]
    symm
    apply xbit_groupSel_other
    rintro ⟨h1, h2, h3⟩
    exact hg ⟨h1, by omega, by omega⟩

end CCoreEdgeChildAux

open CCoreEdgeAux CCoreEdgeChildAux in
/-- **One child call in core coordinates**: `C^{⊗f}` on slot `t` (`cCoreVal`) is the coordinate
kernel `(aI + bX_{e_t})^{⊗f}` acting on the core coordinates of the node. -/
theorem cCoreVal_eq_core {A K D S rr f j0 : ℕ} (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (t : ℕ)
    (ht : t < mH) (z : RArr (LayerAddr A K D S) rr) (x : LayerAddr A K D S) :
    cCoreVal ρ (j0 + t * f) f (CCoreNode.slot_le hfit ht) z x =
      ∑ Y, tpow f (Kv (Pi.single (cubeEquiv.symm ⟨t, ht⟩) 1) 1) (CCoreEdgeAux.coreX ρ f j0 x) Y •
        z (CCoreEdgeAux.coreSet ρ f j0 x Y) := by
  funext kk
  have hkern := kernelSlot_holds 100 f (cubeEquiv.symm ⟨t, ht⟩)
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, hkern, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [cCoreVal, CD]
  refine Finset.sum_nbij' (Yof ρ f j0 x (cubeEquiv.symm ⟨t, ht⟩))
    (fun Y c => decide (Y c (cubeEquiv.symm ⟨t, ht⟩) = 1)) ?_ ?_ ?_ ?_ ?_
  · intro bs _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro c p hp
    simp only [Yof, if_neg hp]
  · intro Y _
    exact Finset.mem_univ _
  · intro bs _
    funext c
    simp only [Yof, if_true]
    exact decide_ite_bool _
  · intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
    funext c p
    by_cases hp : p = cubeEquiv.symm ⟨t, ht⟩
    · subst hp
      exact (if_pos rfl).trans (zmod2_ite_decide _)
    · exact (if_neg hp).trans (hY c p hp)
  · intro bs _
    rw [coreSet_Yof hfit ρ t ht x bs]
    congr 1
    unfold tpow C2
    refine Finset.prod_congr rfl fun c _ => ?_
    have hxb : xbit x (j0 + t * f + c.val) ρ.val =
        groupBits ρ (j0 + t * f) f (CCoreNode.slot_le hfit ht) x c := by
      have hc := c.isLt
      have hsl := CCoreNode.slot_le hfit ht
      unfold xbit groupBits
      rw [dif_pos ⟨by omega, ρ.isLt⟩, Fin.eta]
    simp only [Yof, if_true, coreX_apply ρ x c t ht, hxb]
    generalize groupBits ρ (j0 + t * f) f (CCoreNode.slot_le hfit ht) x c = B
    generalize bs c = b
    cases B <;> cases b <;> simp

end SubNLogN.Math.Networks
