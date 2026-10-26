import SubNLogN.Math.Networks.Proofs.CCoreRole

/-!
# Lemma A.10 (`lem:transfer-phase`) node, step 4: `tpow f Cfull` read through `slotBits` is `C^{⊗(mH·f)}` (`CD`)

At a node with `f` columns, a column state `X : Fin f → Pt 100` is the vector `slotBits f X` of the
`mH·f` selected bits of the group (index `t·f + col` holds `X col (cubeEquiv.symm t)`).

* `slotEquiv f`: `slotBits f` is a bijection `(Fin f → Pt 100) ≃ (Fin (mH·f) → Bool)`;
* `tpow_Cfull_eq_prod`: the product kernel `∏_{c,p} C2 (X c p) (X' c p)` of `tpow f Cfull` is the kernel
  `∏_j (if e j = e' j then ka else kb)` of `CD (mH·f)` at `e = slotBits f X`, `e' = slotBits f X'`;
* `tpow_Cfull_slotBits`: `∑_{X'} tpow f Cfull X X' · F (slotBits f X') = CD (mH·f) F (slotBits f X)`;
* `roleAddrC_self`, `cCoreVal_eq_applyCol`: an address `x` of the class `c` is the point
  `(slotBits⁻¹ (groupBits x), x)` of its own role, and `cCoreVal` at `x` is `applyCol (tpow f Cfull)` of
  the role state of the input there (step 4 of the node proof, `CCoreNode.lean`).

Public statements live in `CCoreNode` (used in `Proofs/CCoreNode.lean`); helpers in `CCoreNode.Reindex`.
-/

namespace SubNLogN.Math.Networks

namespace CCoreNode

open SubNLogN.Math.Walsh

namespace Reindex

/-- Column `c`, cube point `p` ↦ the selected-bit index `t·f + c` with slot `t = cubeEquiv p`. -/
def idxEquiv (f : ℕ) : Fin f × Cube 100 ≃ Fin (mH * f) :=
  ((Equiv.prodComm _ _).trans (Equiv.prodCongr cubeEquiv (Equiv.refl _))).trans finProdFinEquiv

theorem idxEquiv_val (f : ℕ) (c : Fin f) (p : Cube 100) :
    (idxEquiv f (c, p) : ℕ) = c.val + f * (cubeEquiv p).val := rfl

/-- The selected bit of index `t·f + c` is coordinate `p = cubeEquiv.symm t` of column `c`. -/
theorem slotBits_idx (f : ℕ) (X : Fin f → Pt 100) (c : Fin f) (p : Cube 100) :
    slotBits f X (idxEquiv f (c, p)) = decide (X c p = 1) := by
  have hf : 0 < f := c.pos
  have h1 : (⟨(idxEquiv f (c, p) : ℕ) % f,
      Nat.mod_lt _ (pos_of_lt_mul (idxEquiv f (c, p)).isLt)⟩ : Fin f) = c := by
    apply Fin.ext
    show (idxEquiv f (c, p) : ℕ) % f = c.val
    rw [idxEquiv_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]
  have h2 : (⟨(idxEquiv f (c, p) : ℕ) / f, div_lt_of_lt_mul' (idxEquiv f (c, p)).isLt⟩ : Fin mH) =
      cubeEquiv p := by
    apply Fin.ext
    show (idxEquiv f (c, p) : ℕ) / f = (cubeEquiv p).val
    rw [idxEquiv_val, Nat.add_mul_div_left _ _ hf, Nat.div_eq_of_lt c.isLt, zero_add]
  unfold slotBits
  rw [h1, h2, Equiv.symm_apply_apply]

theorem zmod2_decide_eq_iff (a b : ZMod 2) : (decide (a = 1) = decide (b = 1)) ↔ a = b := by
  revert a b
  decide

theorem ite_decide_zmod2 (a : ZMod 2) :
    (if decide (a = 1) = true then (1 : ZMod 2) else 0) = a := by
  revert a
  decide

end Reindex

open Reindex

/-- `slotBits f` as an equivalence. -/
def slotEquiv (f : ℕ) : (Fin f → Pt 100) ≃ (Fin (mH * f) → Bool) where
  toFun := slotBits f
  invFun e := fun c p => if e (idxEquiv f (c, p)) then 1 else 0
  left_inv X := by
    funext c p
    show (if slotBits f X (idxEquiv f (c, p)) then (1 : ZMod 2) else 0) = X c p
    rw [slotBits_idx]
    exact ite_decide_zmod2 (X c p)
  right_inv e := by
    funext i
    obtain ⟨⟨c, p⟩, rfl⟩ := (idxEquiv f).surjective i
    show slotBits f (fun c p => if e (idxEquiv f (c, p)) then (1 : ZMod 2) else 0) (idxEquiv f (c, p)) =
      e (idxEquiv f (c, p))
    rw [slotBits_idx]
    cases e (idxEquiv f (c, p)) <;> decide

theorem slotEquiv_apply (f : ℕ) (X : Fin f → Pt 100) : slotEquiv f X = slotBits f X := rfl

namespace Reindex

/-- The kernel of `tpow f Cfull` is the kernel of `CD (mH·f)` read through `slotBits`. -/
theorem tpow_Cfull_eq_prod (f : ℕ) (X X' : Fin f → Pt 100) :
    tpow f Cfull X X' =
      ∏ j : Fin (mH * f), (if slotBits f X j = slotBits f X' j then ka else kb) := by
  rw [← (idxEquiv f).prod_comp, Fintype.prod_prod_type]
  unfold tpow Cfull
  refine Finset.prod_congr rfl (fun c _ => Finset.prod_congr rfl (fun p _ => ?_))
  rw [slotBits_idx, slotBits_idx]
  unfold C2
  by_cases h : X c p = X' c p
  · rw [if_pos h, if_pos ((zmod2_decide_eq_iff _ _).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((zmod2_decide_eq_iff _ _).1 h'))]

/-- `roleIdx` for an arbitrary number of roles (stated generically, so that `rfl` never evaluates
`W_c`). -/
theorem roleIdx_val {L : Model.Layout} (c : Model.RowClass L) (W : ℕ) (hW : 0 < W) (x : L.Addr) :
    (Model.roleIdx c W hW x).val = ((x c.row).val / c.μ) % W := rfl

/-- A `dite` all of whose branches equal `v` (no case split on a concrete condition, which could
make Lean evaluate `W_c`). -/
theorem dite_eq_of {α : Sort*} {p : Prop} [Decidable p] {t : p → α} {e : ¬p → α} {v : α}
    (ht : ∀ h, t h = v) (he : ∀ h, e h = v) : dite p t e = v := by
  by_cases h : p
  · rw [dif_pos h]
    exact ht h
  · rw [dif_neg h]
    exact he h

/-- `cCoreVal` unfolded (stated for an arbitrary group length `e`). -/
theorem cCoreVal_apply' {r A K D S : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (z : RArr (LayerAddr A K D S) r) (x : LayerAddr A K D S) (k : Fin r) :
    cCoreVal ρ j0 e h z x k = CD e (fun bs => z (groupSel ρ j0 e x bs) k) (groupBits ρ j0 e h x) :=
  rfl

theorem recompose (v μ W res : ℕ) (hm : v % μ = res) :
    res + μ * ((v / μ) % W + W * ((v / μ) / W)) = v := by
  rw [Nat.mod_add_div (v / μ) W, ← hm, Nat.mod_add_div v μ]

/-- `alignL` changes only the prefix (proved without unfolding the prefix `dite`, whose condition
mentions `W_c`). -/
theorem alignL_snd {A K D S : ℕ} (c : Model.RowClass (layerLayout A K D S)) (k : Fin Wc)
    (y : LayerAddr A K D S) : (alignL c k y).2 = y.2 := by
  unfold alignL
  exact Prod.mk.eta

/-- `alignL` moves an address of `c` to its own role: the identity. -/
theorem alignL_self {A K D S : ℕ} {ρ : Fin K} {f j0 : ℕ} {c : Model.RowClass (layerLayout A K D S)}
    (hN : NodeHypC A K D S ρ f j0 c) (x : LayerAddr A K D S) (hx : c.mem (encodeAddr x)) :
    alignL c (Model.roleIdx c Wc Wc_pos (encodeAddr x)) x = x := by
  have hrow : (encodeAddr x c.row).val = x.1.val := encodeAddr_zero x c.row hN.row0
  have hm : x.1.val % c.μ = c.res := by
    have h1 : (encodeAddr x c.row).val % c.μ = c.res := hx
    rwa [hrow] at h1
  have hk : (Model.roleIdx c Wc Wc_pos (encodeAddr x)).val = (x.1.val / c.μ) % Wc := by
    rw [roleIdx_val, hrow]
  refine Prod.ext ?_ (alignL_snd c _ x)
  unfold alignL
  exact dite_eq_of (fun hv => Fin.ext ((Fin.val_mk hv).trans
    (by rw [hk]; exact recompose x.1.val c.μ Wc c.res hm))) (fun _ => rfl)

theorem groupBits_eq {A K D S : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (x : LayerAddr A K D S) (i : Fin e) (j : Fin D) (hij : j0 + i.val = j.val) :
    groupBits ρ j0 e h x i = x.2.1 j ρ := by
  unfold groupBits
  have hj : (⟨j0 + i.val, by omega⟩ : Fin D) = j := Fin.ext hij
  rw [hj]

/-- Overwriting the selected bits of a group by their own values changes nothing. -/
theorem groupSel_groupBits {A K D S : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (x : LayerAddr A K D S) : groupSel ρ j0 e x (groupBits ρ j0 e h x) = x := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  simp only [groupSel]
  split_ifs with hj
  · rw [groupBits_eq ρ j0 e h x ⟨(j : ℕ) - j0, by omega⟩ j (by show j0 + ((j : ℕ) - j0) = j; omega),
      Function.update_eq_self]
  · rfl

end Reindex

/-- **Reindexing**: `tpow f Cfull` acting on functions of the column state, read through
`slotBits`, is `C^{⊗(mH·f)}` (`CD`). -/
theorem tpow_Cfull_slotBits (f : ℕ) (F : (Fin (mH * f) → Bool) → ℂ) (X : Fin f → Pt 100) :
    ∑ X', tpow f Cfull X X' * F (slotBits f X') = CD (mH * f) F (slotBits f X) := by
  unfold CD
  rw [← (slotEquiv f).sum_comp]
  refine Finset.sum_congr rfl (fun X' _ => ?_)
  rw [tpow_Cfull_eq_prod]
  rfl

/-- An address `x` of `c` is the point `(slotBits⁻¹ (groupBits x), x)` of its own role. -/
theorem roleAddrC_self {A K D S : ℕ} {ρ : Fin K} {f j0 : ℕ}
    {c : Model.RowClass (layerLayout A K D S)} (hN : NodeHypC A K D S ρ f j0 c)
    (x : LayerAddr A K D S) (hx : c.mem (encodeAddr x)) :
    roleAddrC c ρ f j0 (Model.roleIdx c Wc Wc_pos (encodeAddr x))
      ((slotEquiv f).symm (groupBits ρ j0 (mH * f) hN.fits x)) x = x := by
  have hX : slotBits f ((slotEquiv f).symm (groupBits ρ j0 (mH * f) hN.fits x)) =
      groupBits ρ j0 (mH * f) hN.fits x := by
    rw [← slotEquiv_apply, Equiv.apply_symm_apply]
  unfold roleAddrC
  rw [alignL_self hN x hx, hX, groupSel_groupBits]

/-- **Read-back** (step 4 of the node proof): `cCoreVal` at an address `x` of `c` is
`applyCol (tpow f Cfull)` of the role state of the input array at the point of `x` in its own role. -/
theorem cCoreVal_eq_applyCol {A K D S rr : ℕ} {ρ : Fin K} {f j0 : ℕ}
    {c : Model.RowClass (layerLayout A K D S)} (hN : NodeHypC A K D S ρ f j0 c)
    (h : j0 + mH * f ≤ D) (z : RArr (LayerAddr A K D S) rr) (x : LayerAddr A K D S)
    (hx : c.mem (encodeAddr x)) (i : Fin rr) :
    cCoreVal ρ j0 (mH * f) h z x i =
      applyCol (tpow f Cfull) (roleStateC c ρ f j0 (encodeArr z)
        (roleIdxC.symm (Model.roleIdx c Wc Wc_pos (encodeAddr x))))
        ((slotEquiv f).symm (groupBits ρ j0 (mH * f) h x), (x, i)) := by
  have hX : slotBits f ((slotEquiv f).symm (groupBits ρ j0 (mH * f) h x)) =
      groupBits ρ j0 (mH * f) h x := by
    rw [← slotEquiv_apply, Equiv.apply_symm_apply]
  have hrole : ∀ X' : Fin f → Pt 100,
      roleStateC c ρ f j0 (encodeArr z) (roleIdxC.symm (Model.roleIdx c Wc Wc_pos (encodeAddr x)))
          (X', (x, i)) = z (groupSel ρ j0 (mH * f) x (slotBits f X')) i := by
    intro X'
    simp only [roleStateC, Equiv.apply_symm_apply, encodeArr, decodeAddr_encodeAddr]
    unfold roleAddrC
    rw [alignL_self hN x hx]
  rw [cCoreVal_apply']
  unfold applyCol
  simp only [hrole]
  rw [tpow_Cfull_slotBits f (fun bs => z (groupSel ρ j0 (mH * f) x bs) i), hX]

end CCoreNode

end SubNLogN.Math.Networks
