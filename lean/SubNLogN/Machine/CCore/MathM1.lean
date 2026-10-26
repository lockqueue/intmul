/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.MathM1Defs
import SubNLogN.Math.Networks.Proofs.CCoreNode
import SubNLogN.Math.Networks.Proofs.CCoreEdge
import SubNLogN.Math.Networks.Proofs.Serial

/-!
# M1: node value correctness, compact form (`CCore/MathM1.lean`)

Proves (using the op-by-op transport `NodeCodeAux.nodeCode_transport` of `CCore/NodeCode.lean`,
plugged in by `CCore/MathM1Holds.lean`):

* `M1Aux.restrictRole_cCoreVal`: the **compact identity** `restrict_u (C_group z) = C_group (restrict_u z)`
  (`cCoreVal` reads and writes only the selected bits of chunks, `roleEmb` only the row field);
* `M1Aux.idealCrun_crunI`: the ideal children `crunI` (`CCore/MathM1Defs.lean`) have the child property
  `M1Aux.IdealCrunP` (definitionally `NodeCodeAux.IdealCrun`, stated here without its
  abbreviations `Φ`, `topC`, `toN`);
* `M1Aux.childSpec_crunI`: they satisfy `ChildSpecC` at the top class;
* `M1Aux.nodeValue_of_transport`: `NodeValueStmt cdat` from the transport statement `TransportHyp`
  (the statement of `NodeCodeAux.nodeCode_transport`, unfolded), the Lemma A.10 (`lem:transfer-phase`) node lemma
  `cxNode_correct_holds`, `coreEdgeRoleSpec_holds` and `serialEqFramed_holds`.

Pitfall: `Wc = Fintype.card (Role .complex 100)` and `Wn = tripleWc 100` are only propositionally equal
(`M1Aux.Wc_eq_Wn`). Nothing here compares `Fin Wc`- and `Fin Wn`-typed terms definitionally (that
would evaluate the cardinality): role indices are compared through `.val` (`finCongr_val`, proved for
variable `m n` by `subst`).
-/

namespace SubNLogN.Machine.CCore

namespace M1Aux

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh

/-! ### Role counts and role membership -/

/-- `W_c = W` (`cardRole_holds`). -/
theorem Wc_eq_Wn : Wc = Wn := (cardRole_holds 100).2

/-- `finCongr` keeps the value (proved for variable bounds, so no cardinality is evaluated). -/
theorem finCongr_val {m n : ℕ} (h : m = n) (k : Fin m) : (finCongr h k).val = k.val := by
  subst h
  rfl

theorem finCongr_eq_iff (k : Fin Wc) (u : Fin Wn) : finCongr Wc_eq_Wn k = u ↔ k.val = u.val := by
  rw [Fin.ext_iff, finCongr_val]

/-- The top class contains every address. -/
theorem topClass_mem (A K D S : ℕ) (y : (layerLayout A K D S).Addr) : (topClass A K D S).mem y := by
  show (y (topClass A K D S).row).val % 1 = 0
  exact Nat.mod_one _

/-- Residue arithmetic of the top class, for **variable** `W = N` (so that the kernel never compares
closed terms such as `1 * Wc`, which would make it evaluate `Wc`). -/
theorem top_res_iff {W N a b k : ℕ} (hW : W = N) (hb : b < N) :
    (a * N + b) % (1 * W) = 0 + 1 * k ↔ k = b := by
  subst hW
  rw [one_mul, zero_add, one_mul, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  exact eq_comm

/-- The top class has modulus `1`, so `W ∣ A` gives the node divisibility (variable `W`). -/
theorem top_div {A K D S W : ℕ} (h : W ∣ A) : (topClass A K D S).μ * W ∣ A := by
  show 1 * W ∣ A
  rw [one_mul]
  exact h

/-- Role class `k` of the top class contains the addresses of role stream `u` iff `k = u`. -/
theorem sub_mem_roleEmb (t : CCoreRT) (k : Fin Wc) (u : Fin Wn)
    (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    ((topClass t.A t.K t.D t.S).sub Wc Wc_pos k).mem (encodeAddr (roleEmb t u x)) ↔
      k.val = u.val := by
  have h0 : (encodeAddr (roleEmb t u x) (topClass t.A t.K t.D t.S).row).val =
      x.1.val * Wn + u.val := CCoreNode.encodeAddr_zero _ _ rfl
  rw [CCoreNode.sub_mem_iff, h0]
  exact top_res_iff Wc_eq_Wn u.isLt

/-! ### The compact identity -/

/-- `groupSel` (selected bits of chunks) commutes with the row embedding. -/
theorem groupSel_roleEmb (t : CCoreRT) (u : Fin Wn) (ρ : Fin t.K) (j0 e : ℕ)
    (x : LayerAddr (t.A / Wn) t.K t.D t.S) (bs : Fin e → Bool) :
    groupSel ρ j0 e (roleEmb t u x) bs = roleEmb t u (groupSel ρ j0 e x bs) := rfl

/-- `groupBits` does not read the row field. -/
theorem groupBits_roleEmb (t : CCoreRT) (u : Fin Wn) (ρ : Fin t.K) (j0 e : ℕ) (h : j0 + e ≤ t.D)
    (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    groupBits ρ j0 e h (roleEmb t u x) = groupBits ρ j0 e h x := rfl

/-- **Compact identity**: row class `u` of `C^{⊗e}` on a group is `C^{⊗e}` on row class `u`. -/
theorem restrictRole_cCoreVal (t : CCoreRT) (u : Fin Wn) (ρ : Fin t.K) (j0 e : ℕ)
    (h : j0 + e ≤ t.D) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    restrictRole t u (cCoreVal ρ j0 e h z) = cCoreVal ρ j0 e h (restrictRole t u z) := by
  funext x k
  show CD e (fun bs => z (groupSel ρ j0 e (roleEmb t u x) bs) k) (groupBits ρ j0 e h (roleEmb t u x)) =
    CD e (fun bs => z (roleEmb t u (groupSel ρ j0 e x bs)) k) (groupBits ρ j0 e h x)
  rw [groupBits_roleEmb]
  rfl

/-! ### The ideal children -/

/-- The child property of a child runner at a node of the call `t` (`NodeCodeAux.IdealCrun`,
unfolded): a call on slot `sl` in role class `k` of the top class applies
`childVal` to role stream `k` and changes no other role stream. -/
def IdealCrunP (t : CCoreRT)
    (crun : ℕ → RowClass (layerLayout t.A t.K t.D t.S) →
      ((layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ)) →
      ((layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ))) : Prop :=
  ∀ (sl : ℕ) (hsl : sl < mn) (k : Fin Wc) (Arr : (layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ))
    (u : Fin Wn),
    restrictRole t u (decodeArr (crun sl ((topClass t.A t.K t.D t.S).sub Wc Wc_pos k) Arr)) =
      if finCongr Wc_eq_Wn k = u then childVal t ⟨sl, hsl⟩ (restrictRole t u (decodeArr Arr))
      else restrictRole t u (decodeArr Arr)

/-- **The ideal children have the child property.** -/
theorem idealCrun_crunI (t : CCoreRT) (hρ : t.ρ < t.K) : IdealCrunP t (crunI t hρ) := by
  intro sl hsl k Arr u
  by_cases hku : finCongr Wc_eq_Wn k = u
  · rw [if_pos hku]
    have hku' : k.val = u.val := (finCongr_eq_iff k u).1 hku
    funext x
    show crunI t hρ sl ((topClass t.A t.K t.D t.S).sub Wc Wc_pos k) Arr (encodeAddr (roleEmb t u x)) =
      childVal t ⟨sl, hsl⟩ (restrictRole t u (decodeArr Arr)) x
    unfold crunI
    by_cases hs : t.j0 + sl * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D
    · rw [dif_pos hs]
      simp only [encodeArr, CCoreNode.decodeAddr_encodeAddr]
      rw [if_pos ((sub_mem_roleEmb t k u x).2 hku')]
      unfold childVal
      rw [dif_pos (And.intro hρ hs)]
      exact congrFun (restrictRole_cCoreVal t u ⟨t.ρ, hρ⟩ _ _ hs (decodeArr Arr)) x
    · rw [dif_neg hs]
      unfold childVal
      rw [dif_neg (show ¬ (t.ρ < t.K ∧ t.j0 + sl * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D) from
        fun h => hs h.2)]
      rfl
  · rw [if_neg hku]
    have hku' : ¬ k.val = u.val := fun h => hku ((finCongr_eq_iff k u).2 h)
    funext x
    show crunI t hρ sl ((topClass t.A t.K t.D t.S).sub Wc Wc_pos k) Arr (encodeAddr (roleEmb t u x)) =
      restrictRole t u (decodeArr Arr) x
    unfold crunI
    by_cases hs : t.j0 + sl * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D
    · rw [dif_pos hs]
      simp only [encodeArr, CCoreNode.decodeAddr_encodeAddr]
      rw [if_neg (fun h => hku' ((sub_mem_roleEmb t k u x).1 h))]
      rfl
    · rw [dif_neg hs]
      rfl

/-- **The value-level child interface** `ChildSpecC` holds for the ideal children at the top class. -/
theorem childSpec_crunI (t : CCoreRT) (hρ : t.ρ < t.K) (hfit : t.j0 + mH * mn ^ (t.k - 1) ≤ t.D) :
    CCoreNode.ChildSpecC (topClass t.A t.K t.D t.S) ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0 hfit
      (crunI t hρ) id := by
  intro k s hs z
  have hs' : t.j0 + s * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D := CCoreNode.slot_le hfit hs
  have hde : decodeArr (encodeArr z) = z := by
    funext y
    exact congrArg z (CCoreNode.decodeAddr_encodeAddr y)
  show decodeArr (crunI t hρ s ((topClass t.A t.K t.D t.S).sub Wc Wc_pos k) (encodeArr z)) = _
  unfold crunI
  rw [dif_pos hs', hde]
  funext x
  simp only [decodeArr, encodeArr, CCoreNode.decodeAddr_encodeAddr]

/-! ### Assembly -/

/-- The statement of `NodeCodeAux.nodeCode_transport` (unfolded): the value-level run of `cxNodeOps`
at the top class with a child runner having the child property, restricted to row class `u`, is the
node code run on the compact role arrays, read at physical role `collectPerm u`. -/
def TransportHyp (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) : Prop :=
  ∀ (t : CCoreRT) (_hρ : t.ρ < t.K), 1 ≤ t.k → 6 ≤ t.K → Wn ∣ t.A → t.j0 + t.e ≤ t.D →
    RunEightSpecStmt → PackedAgreeStmt → PackedProcCorrectStmt → ValidCdat cdat →
    ∀ (crun : ℕ → RowClass (layerLayout t.A t.K t.D t.S) →
        ((layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ)) →
        ((layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ))), IdealCrunP t crun →
    ∀ (Arr : (layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ)) (u : Fin Wn),
      restrictRole t u (decodeArr (CCoreNode.runOps crun (topClass t.A t.K t.D t.S)
        (cxNodeOps (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r) t.ρ (mn ^ (t.k - 1))
          t.j0 cdat id) Arr)) =
      mopsVal t (nodeCode cdat) (fun u' => restrictRole t u' (decodeArr Arr)) (collectPerm u)

/-- `e = m^k = m · m^(k-1)` for `k ≥ 1`. -/
theorem e_eq (t : CCoreRT) (hk : 1 ≤ t.k) : t.e = mH * mn ^ (t.k - 1) := by
  rw [mH_eq_mn, ← pow_succ', Nat.sub_add_cancel hk]
  rfl

/-- **M1 from the transport.** -/
theorem nodeValue_of_transport (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hT : TransportHyp cdat) : NodeValueStmt cdat := by
  intro hcert hR8 hPA hPP _hTC hval t hρ hg z hk hK hdiv u
  have hWA : Wn ∣ t.A := dvd_trans (dvd_pow_self Wn (by omega)) hdiv
  have he : t.e = mH * mn ^ (t.k - 1) := e_eq t hk
  have hfit : t.j0 + mH * mn ^ (t.k - 1) ≤ t.D := by rw [← he]; exact hg
  have hmn : 0 < mn := by norm_num [mn, tripleM]
  have hN : CCoreNode.NodeHypC t.A t.K t.D t.S ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0
      (topClass t.A t.K t.D t.S) :=
    { K6 := hK
      f1 := Nat.one_le_pow _ _ hmn
      fits := hfit
      row0 := rfl
      div := top_div (Wc_eq_Wn ▸ hWA) }
  have hedge := coreEdgeRoleSpec_holds hcert hR8 hPA hPP ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0
    (topClass t.A t.K t.D t.S) hN cdat hval (crunI t hρ) id (childSpec_crunI t hρ hfit)
  have hnode := CCoreNode.cxNode_correct_holds hcert (serialEqFramed_holds 100) ⟨t.ρ, hρ⟩
    (mn ^ (t.k - 1)) t.j0 (topClass t.A t.K t.D t.S) hN cdat (crunI t hρ) id hedge t.e he hg z
  have hdec : decodeArr (CCoreNode.runOps (crunI t hρ) (topClass t.A t.K t.D t.S)
      (cxNodeOps (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r) t.ρ (mn ^ (t.k - 1))
        t.j0 cdat id) (encodeArr z)) = cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z := by
    refine hnode.trans ?_
    funext x
    exact if_pos (topClass_mem _ _ _ _ _)
  have htr := hT t hρ hk hK hWA hg hR8 hPA hPP hval (crunI t hρ) (idealCrun_crunI t hρ)
    (encodeArr z) u
  have hde : decodeArr (encodeArr z) = z := by
    funext x
    exact congrArg z (CCoreNode.decodeAddr_encodeAddr x)
  rw [hdec, hde] at htr
  exact htr

end M1Aux

end SubNLogN.Machine.CCore
