import SubNLogN.Math.Networks.Proofs.CCoreRole

/-!
# Lemma A.10 (`lem:transfer-phase`) node: the mask `zMask` on role states (for `CxNodeCorrectStmt`)

Facts used in the node proof (`Proofs/CCoreNode.lean`):
* `blockVal_single`: a one-field block holds the value of that field;
* `groupSel_bit`: the selected bit of chunk `j0 + i` after `groupSel` is `bs i`;
* `slotBit_roleAddrC`: the selected bit of slot `t`, column `col` of a role address is
  `X col (cubeEquiv.symm t)`;
* `dotC_val`: the value of the `𝔽₂` dot product as a natural number;
* `zMask_sign`: the sign applied by `zMask` at a role address is `∏_col (−1)^{u_a · X_col}`, the
  diagonal entry of `Z_{a,f}` at its core point;
* `applyCol_diagonal`: a diagonal matrix acts on the column index pointwise.
All sums over `Cube 100` are handled symbolically (no enumeration of the cube).
-/

namespace SubNLogN.Math.Networks

namespace CCoreNode

namespace Masks

open Model SubNLogN.Math.Walsh

variable {A K D S rr : ℕ}

/-! ### Masks: `zMask` acts on a role state as `Z_{a,f}` -/

/-- A one-field block holds the value of that field. -/
theorem blockVal_single (L : Model.Layout) (s : ℕ) (hs : s < L.n) (x : L.Addr) :
    L.blockVal s (s + 1) x = (x ⟨s, hs⟩).val := by
  unfold Model.Layout.blockVal
  have hfil : Finset.univ.filter (Model.inBlock s (s + 1) (n := L.n)) = {⟨s, hs⟩} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Model.inBlock]
    constructor
    · intro hj
      exact Fin.ext (show j.val = s by omega)
    · intro hj
      rw [hj]
      exact ⟨le_refl _, Nat.lt_succ_self _⟩
  rw [hfil, Finset.sum_singleton]
  have hplace : L.place (s + 1) ⟨s, hs⟩ = 1 := by
    unfold Model.Layout.place
    have h0 : Finset.univ.filter (fun j' : Fin L.n => (⟨s, hs⟩ : Fin L.n) < j' ∧ j'.val < s + 1) =
        ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j' _ hj'
      have h1 : s < j'.val := hj'.1
      have h2 := hj'.2
      omega
    rw [h0, Finset.prod_empty]
  rw [hplace, Nat.mul_one]

/-- The selected bit of chunk `J = j0 + i` after `groupSel` is `bs i`. -/
theorem groupSel_bit {ρ : Fin K} {j0 e : ℕ} (x : LayerAddr A K D S) (bs : Fin e → Bool) (J : Fin D)
    (i : ℕ) (hi : i < e) (hJ : J.val = j0 + i) : (groupSel ρ j0 e x bs).2.1 J ρ = bs ⟨i, hi⟩ := by
  unfold groupSel
  dsimp only
  rw [dif_pos (by omega : j0 ≤ J.val ∧ J.val < j0 + e), Function.update_self]
  congr 1
  exact Fin.ext (show J.val - j0 = i by omega)

theorem zmod2_ite_val (z : ZMod 2) : (if z = 1 then 1 else 0) = z.val := by
  fin_cases z <;> rfl

section Masks

variable {ρ : Fin K} {f j0 : ℕ} {c : Model.RowClass (layerLayout A K D S)}

/-- The selected bit of slot `t`, column `col` of a role address is `X col (cubeEquiv.symm t)`. -/
theorem slotBit_roleAddrC (hN : NodeHypC A K D S ρ f j0 c) (k : Fin Wc) (X : Fin f → Pt 100)
    (y : LayerAddr A K D S) (t : Fin mH) (col : Fin f) :
    slotBit (A := A) (D := D) (S := S) K ρ.val f j0 t.val col.val
        (encodeAddr (roleAddrC c ρ f j0 k X y)) = (X col (cubeEquiv.symm t)).val := by
  have hcol := col.isLt
  have hj : j0 + t.val * f + col.val < D := by
    have := slot_le hN.fits t.isLt
    omega
  have hi : t.val * f + col.val < mH * f := by
    have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt t.isLt)
    rw [Nat.succ_mul] at this
    omega
  have hs : selField K ρ.val (j0 + t.val * f + col.val) < (layerLayout A K D S).n :=
    bitField_lt (A := A) (S := S) ⟨_, hj⟩ ρ
  unfold slotBit
  rw [blockVal_single _ _ hs]
  have key := encodeAddr_bit (roleAddrC c ρ f j0 k X y) ⟨j0 + t.val * f + col.val, hj⟩ ρ
  have hb : (roleAddrC c ρ f j0 k X y).2.1 ⟨j0 + t.val * f + col.val, hj⟩ ρ =
      slotBits f X ⟨t.val * f + col.val, hi⟩ :=
    groupSel_bit _ _ _ _ hi (show j0 + t.val * f + col.val = j0 + (t.val * f + col.val) by omega)
  have hmod : (t.val * f + col.val) % f = col.val := by
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hcol]
  have hdiv : (t.val * f + col.val) / f = t.val := by
    have hf : 0 < f := Nat.lt_of_le_of_lt (Nat.zero_le _) hcol
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hf, Nat.div_eq_of_lt hcol, zero_add]
  have hX : slotBits f X ⟨t.val * f + col.val, hi⟩ = decide (X col (cubeEquiv.symm t) = 1) := by
    unfold slotBits
    have e1 : (⟨(t.val * f + col.val) % f, Nat.mod_lt _ (pos_of_lt_mul hi)⟩ : Fin f) = col :=
      Fin.ext hmod
    have e2 : (⟨(t.val * f + col.val) / f, div_lt_of_lt_mul' hi⟩ : Fin mH) = t := Fin.ext hdiv
    simp only [e1, e2]
  rw [hb, hX] at key
  simp only [decide_eq_true_eq] at key
  rw [← zmod2_ite_val]
  exact key

theorem dotC_val (u x : Pt 100) : (dotC u x).val = (∑ p, (u p).val * (x p).val) % 2 := by
  have : dotC u x = ((∑ p, (u p).val * (x p).val : ℕ) : ZMod 2) := by
    unfold dotC
    push_cast
    simp only [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast]

/-- The sign of `zMask` at a role address is the diagonal entry of `Z_{a,f}` at its core point. -/
theorem zMask_sign (hN : NodeHypC A K D S ρ f j0 c) (a : Addr 100) (k : Fin Wc)
    (X : Fin f → Pt 100) (y : LayerAddr A K D S) :
    ((-1 : ℂ) ^ (∑ col ∈ Finset.range f, ∑ p : Cube 100,
      (ua a p).val * slotBit (A := A) (D := D) (S := S) K ρ.val f j0 (cubeEquiv p) col
        (encodeAddr (roleAddrC c ρ f j0 k X y)))) =
      ∏ col : Fin f, (-1 : ℂ) ^ (dotC (ua a) (X col)).val := by
  rw [Finset.sum_range, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun col _ => ?_)
  have hsb : ∀ p : Cube 100, slotBit (A := A) (D := D) (S := S) K ρ.val f j0 (cubeEquiv p) col.val
      (encodeAddr (roleAddrC c ρ f j0 k X y)) = (X col p).val := fun p => by
    rw [slotBit_roleAddrC hN k X y (cubeEquiv p) col, Equiv.symm_apply_apply]
  simp only [hsb]
  rw [dotC_val]
  conv_lhs => rw [neg_one_pow_eq_pow_mod_two]

theorem applyCol_diagonal {ι σ : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (g : ι × σ → ℂ)
    (p : ι × σ) : applyCol (Matrix.diagonal d) g p = d p.1 * g p := by
  unfold applyCol
  simp [Matrix.diagonal_apply]

end Masks

end Masks

end CCoreNode

end SubNLogN.Math.Networks
