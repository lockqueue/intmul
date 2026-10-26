import SubNLogN.Math.Networks.Proofs.CCoreEdgeBits
import SubNLogN.Math.Networks.Proofs.CCoreRole
import SubNLogN.Math.Networks.Proofs.KernelFacts
import SubNLogN.Math.Networks.Proofs.EdgeRealization
import SubNLogN.Math.Networks.Proofs.ComplexCorollary
import SubNLogN.Math.Networks.Proofs.Endpoints

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations, part 2: core coordinates, matrices on core coordinates, packed row words

API for the proof of `CCoreNode.CoreEdgeRoleSpecStmt` (`Proofs/CCoreRole.lean`; final theorem in
`Proofs/CCoreEdge.lean`). Everything is in the `LayerAddr` world:
* core coordinates of a node (`coreX`, `coreSet = groupSel … (slotBits f ·)`): column `col`,
  coordinate `p` = bit `ρ` of chunk `j0 + (cubeEquiv p) f + col`; role addresses are
  `coreSet (alignL c k y) X`;
* `opL P T z`: the matrix `T` on the core coordinates of the addresses with `P` (identity
  elsewhere), with `opL T₂ ∘ opL T₁ = opL (T₂ T₁)`; `Realizes … ops T`: the operation list `ops`, run
  at the node, acts on role `k` as `opL T`; `Realizes` is closed under `++` and `flatMap`;
* packed row additions (`PackedProcCorrectStmt` + `AddrXorAllEncodeStmt`) are pulls by the
  column-wise row operation (`realizes_rowAdd`), so a row word `l` with `rowsMove l = N'` realizes
  `(P_{N'})^{⊗f}` (`realizes_word_perm`).
Helpers are in the namespace `SubNLogN.Math.Networks.CCoreEdgeAux`.
-/

namespace SubNLogN.Math.Networks

namespace CCoreEdgeAux

open Model SubNLogN.Math.Walsh

variable {A K D S : ℕ}

/-! ## 4. Core coordinates of a node -/

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zmod2_ite_decide : ∀ a : ZMod 2, (if decide (a = 1) = true then (1 : ZMod 2) else 0) = a := by
  decide

theorem decide_ite_bool : ∀ b : Bool, decide ((if b = true then (1 : ZMod 2) else 0) = 1) = b := by
  decide

/-- Slot index arithmetic. -/
theorem slot_idx {f t col : ℕ} (hcol : col < f) :
    (t * f + col) % f = col ∧ (t * f + col) / f = t := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcol]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hcol, zero_add]

theorem tf_lt {f t col : ℕ} (ht : t < mH) (hcol : col < f) : t * f + col < mH * f := by
  have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt ht)
  rw [Nat.succ_mul] at this
  omega

theorem slotBits_apply (f : ℕ) (Y : Fin f → Pt 100) {t col : ℕ} (ht : t < mH) (hcol : col < f)
    (h : t * f + col < mH * f) :
    CCoreNode.slotBits f Y ⟨t * f + col, h⟩ = decide (Y ⟨col, hcol⟩ (cubeEquiv.symm ⟨t, ht⟩) = 1) := by
  obtain ⟨h1, h2⟩ := slot_idx (t := t) hcol
  simp only [CCoreNode.slotBits, h1, h2]

theorem xbit_groupSel_sel (ρ : Fin K) (j0 e : ℕ) (x : LayerAddr A K D S) (bs : Fin e → Bool)
    (ch : ℕ) (hD : ch < D) (h1 : j0 ≤ ch) (h2 : ch < j0 + e) :
    xbit (groupSel ρ j0 e x bs) ch ρ.val = bs ⟨ch - j0, by omega⟩ := by
  unfold xbit groupSel
  rw [dif_pos ⟨hD, ρ.isLt⟩]
  dsimp only
  rw [dif_pos ⟨h1, h2⟩, Fin.eta, Function.update_self]

theorem xbit_groupSel_other (ρ : Fin K) (j0 e : ℕ) (x : LayerAddr A K D S) (bs : Fin e → Bool)
    (ch t : ℕ) (h : ¬ (t = ρ.val ∧ j0 ≤ ch ∧ ch < j0 + e)) :
    xbit (groupSel ρ j0 e x bs) ch t = xbit x ch t := by
  unfold xbit groupSel
  by_cases hb : ch < D ∧ t < K
  · rw [dif_pos hb, dif_pos hb]
    dsimp only
    by_cases hr : j0 ≤ ch ∧ ch < j0 + e
    · rw [dif_pos hr, Function.update_of_ne]
      intro heq
      exact h ⟨congrArg Fin.val heq, hr⟩
    · rw [dif_neg hr]
  · rw [dif_neg hb, dif_neg hb]

theorem groupSel_groupSel (ρ : Fin K) (j0 e : ℕ) (x : LayerAddr A K D S) (bs bs' : Fin e → Bool) :
    groupSel ρ j0 e (groupSel ρ j0 e x bs) bs' = groupSel ρ j0 e x bs' := by
  unfold groupSel
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext ch
  dsimp only
  split_ifs with h
  · exact Function.update_idem _ _ _
  · rfl

/-- Core coordinates of a layer address at a node with `f` columns and group start `j0`:
column `col`, coordinate `p` = bit `ρ` of chunk `j0 + (cubeEquiv p) f + col`. -/
def coreX (ρ : Fin K) (f j0 : ℕ) (x : LayerAddr A K D S) : Fin f → Pt 100 :=
  fun col p => if xbit x (j0 + (cubeEquiv p).val * f + col.val) ρ.val then 1 else 0

/-- Overwrite the core bits by `Y` (role addresses are `coreSet (alignL c k y) X`). -/
def coreSet (ρ : Fin K) (f j0 : ℕ) (x : LayerAddr A K D S) (Y : Fin f → Pt 100) :
    LayerAddr A K D S :=
  groupSel ρ j0 (mH * f) x (CCoreNode.slotBits f Y)

variable {f j0 : ℕ}

theorem coreSet_fst (ρ : Fin K) (x : LayerAddr A K D S) (Y : Fin f → Pt 100) :
    (coreSet ρ f j0 x Y).1 = x.1 := rfl

theorem coreX_coreSet (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (x : LayerAddr A K D S)
    (Y : Fin f → Pt 100) : coreX ρ f j0 (coreSet ρ f j0 x Y) = Y := by
  funext col p
  have hp := (cubeEquiv p).isLt
  have hlt := tf_lt hp col.isLt
  unfold coreX coreSet
  rw [xbit_groupSel_sel ρ j0 (mH * f) x _ _ (by omega) (by omega) (by omega)]
  have e1 : j0 + (cubeEquiv p).val * f + col.val - j0 = (cubeEquiv p).val * f + col.val := by omega
  simp only [e1]
  rw [slotBits_apply f Y hp col.isLt hlt, Fin.eta, Fin.eta, Equiv.symm_apply_apply,
    zmod2_ite_decide]

theorem coreSet_coreSet (ρ : Fin K) (x : LayerAddr A K D S) (Y Y' : Fin f → Pt 100) :
    coreSet ρ f j0 (coreSet ρ f j0 x Y) Y' = coreSet ρ f j0 x Y' :=
  groupSel_groupSel ρ j0 (mH * f) x _ _

theorem coreSet_coreX (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (x : LayerAddr A K D S) :
    coreSet ρ f j0 x (coreX ρ f j0 x) = x := by
  unfold coreSet groupSel
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext ch
  dsimp only
  split_ifs with h
  · apply Function.update_eq_self_iff.mpr
    have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
    set i := ch.val - j0 with hi
    have hdm := Nat.div_add_mod' i f
    have hidx : j0 + (i / f) * f + i % f = ch.val := by omega
    unfold CCoreNode.slotBits coreX
    dsimp only
    rw [Equiv.apply_symm_apply]
    dsimp only
    rw [hidx, decide_ite_bool]
    unfold xbit
    rw [dif_pos ⟨ch.isLt, ρ.isLt⟩, Fin.eta, Fin.eta]
  · rfl

theorem xbit_coreSet_other (ρ : Fin K) (x : LayerAddr A K D S) (Y : Fin f → Pt 100) (ch t : ℕ)
    (h : ¬ (t = ρ.val ∧ j0 ≤ ch ∧ ch < j0 + mH * f)) :
    xbit (coreSet ρ f j0 x Y) ch t = xbit x ch t :=
  xbit_groupSel_other ρ j0 (mH * f) x _ ch t h

theorem xbit_coreSet_sel (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (x : LayerAddr A K D S)
    (Y : Fin f → Pt 100) (t col : ℕ) (ht : t < mH) (hcol : col < f) :
    xbit (coreSet ρ f j0 x Y) (j0 + t * f + col) ρ.val =
      decide (Y ⟨col, hcol⟩ (cubeEquiv.symm ⟨t, ht⟩) = 1) := by
  have hlt := tf_lt ht hcol
  unfold coreSet
  rw [xbit_groupSel_sel ρ j0 (mH * f) x _ _ (by omega) (by omega) (by omega)]
  have e1 : j0 + t * f + col - j0 = t * f + col := by omega
  simp only [e1]
  exact slotBits_apply f Y ht hcol hlt

theorem coreX_apply (ρ : Fin K) (x : LayerAddr A K D S) (col : Fin f) (t : ℕ) (ht : t < mH) :
    coreX ρ f j0 x col (cubeEquiv.symm ⟨t, ht⟩) =
      if xbit x (j0 + t * f + col.val) ρ.val then 1 else 0 := by
  unfold coreX
  rw [Equiv.apply_symm_apply]

/-! ## 5. Matrices acting on the core coordinates -/

section OpL

variable {rr : ℕ}

/-- The matrix `T` applied on the core coordinates of the addresses satisfying `P`
(identity on the other addresses). -/
noncomputable def opL (ρ : Fin K) (f j0 : ℕ) (P : LayerAddr A K D S → Prop) [DecidablePred P]
    (T : Matrix (Fin f → Pt 100) (Fin f → Pt 100) ℂ) (z : RArr (LayerAddr A K D S) rr) :
    RArr (LayerAddr A K D S) rr :=
  fun x => if P x then ∑ Y, T (coreX ρ f j0 x) Y • z (coreSet ρ f j0 x Y) else z x

variable (P : LayerAddr A K D S → Prop) [DecidablePred P]

theorem opL_comp (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (hP : ∀ x Y, P (coreSet ρ f j0 x Y) ↔ P x)
    (T₁ T₂ : Matrix (Fin f → Pt 100) (Fin f → Pt 100) ℂ) (z : RArr (LayerAddr A K D S) rr) :
    opL ρ f j0 P T₂ (opL ρ f j0 P T₁ z) = opL ρ f j0 P (T₂ * T₁) z := by
  funext x
  by_cases hx : P x
  · simp only [opL, if_pos hx, hP, coreX_coreSet hfit, coreSet_coreSet]
    simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  · simp only [opL, if_neg hx]

theorem opL_one (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (z : RArr (LayerAddr A K D S) rr) :
    opL ρ f j0 P 1 z = z := by
  funext x
  by_cases hx : P x
  · simp only [opL, if_pos hx, Matrix.one_apply]
    rw [Finset.sum_eq_single (coreX ρ f j0 x)]
    · rw [if_pos rfl, one_smul, coreSet_coreX hfit]
    · intro Y _ hY
      rw [if_neg (Ne.symm hY), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [opL, if_neg hx]

theorem opL_diag (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (d : (Fin f → Pt 100) → ℂ)
    (z : RArr (LayerAddr A K D S) rr) :
    opL ρ f j0 P (Matrix.diagonal d) z =
      fun x => if P x then d (coreX ρ f j0 x) • z x else z x := by
  funext x
  by_cases hx : P x
  · simp only [opL, if_pos hx, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (coreX ρ f j0 x)]
    · rw [if_pos rfl, coreSet_coreX hfit]
    · intro Y _ hY
      rw [if_neg (Ne.symm hY), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [opL, if_neg hx]

theorem opL_perm (ρ : Fin K) (g g' : (Fin f → Pt 100) → (Fin f → Pt 100))
    (h1 : ∀ X, g' (g X) = X) (h2 : ∀ Y, g (g' Y) = Y) (z : RArr (LayerAddr A K D S) rr) :
    opL ρ f j0 P (fun X Y => if X = g' Y then 1 else 0) z =
      fun x => if P x then z (coreSet ρ f j0 x (g (coreX ρ f j0 x))) else z x := by
  funext x
  by_cases hx : P x
  · simp only [opL, if_pos hx]
    rw [Finset.sum_eq_single (g (coreX ρ f j0 x))]
    · rw [if_pos (h1 _).symm, one_smul]
    · intro Y _ hY
      rw [if_neg, zero_smul]
      intro hXY
      exact hY (by rw [hXY, h2])
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [opL, if_neg hx]

end OpL

/-! ## 6. Operation lists realizing matrices on a role -/

section Realize

variable {rr : ℕ} {Child : Type}

/-- Role `k` of the node in class `c`, as a predicate on layer addresses. -/
def roleP (c : RowClass (layerLayout A K D S)) (k : Fin Wc) (x : LayerAddr A K D S) : Prop :=
  (c.sub Wc Wc_pos k).mem (encodeAddr x)

noncomputable instance (c : RowClass (layerLayout A K D S)) (k : Fin Wc) :
    DecidablePred (roleP c k) := fun x => by
  unfold roleP
  infer_instance

theorem sub_row {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).row = c.row := rfl

theorem roleP_iff (c : RowClass (layerLayout A K D S)) (hrow : c.row.val = 0) (k : Fin Wc)
    (x : LayerAddr A K D S) : roleP c k x ↔ x.1.val % (c.μ * Wc) = c.res + c.μ * k.val := by
  unfold roleP
  rw [CCoreNode.sub_mem_iff, encode_zero _ _ hrow]

theorem roleP_coreSet (c : RowClass (layerLayout A K D S)) (hrow : c.row.val = 0) (k : Fin Wc)
    (ρ : Fin K) (x : LayerAddr A K D S) (Y : Fin f → Pt 100) :
    roleP c k (coreSet ρ f j0 x Y) ↔ roleP c k x := by
  rw [roleP_iff c hrow, roleP_iff c hrow, coreSet_fst]

variable (crun : Child → RowClass (layerLayout A K D S) →
  ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ)))

/-- `ops`, run at the node in class `c`, act on role `k` as the matrix `T` on core coordinates. -/
def Realizes (c : RowClass (layerLayout A K D S)) (k : Fin Wc) (ρ : Fin K) (f j0 : ℕ)
    (ops : List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child))
    (T : Matrix (Fin f → Pt 100) (Fin f → Pt 100) ℂ) : Prop :=
  ∀ Arr, decodeArr (CCoreNode.runOps crun c ops Arr) = opL ρ f j0 (roleP c k) T (decodeArr Arr)

variable {crun}

theorem Realizes.nil (hfit : j0 + mH * f ≤ D) (c : RowClass (layerLayout A K D S)) (k : Fin Wc)
    (ρ : Fin K) : Realizes crun c k ρ f j0 [] 1 := by
  intro Arr
  rw [opL_one _ hfit]
  rfl

theorem Realizes.append (hfit : j0 + mH * f ≤ D) {c : RowClass (layerLayout A K D S)}
    (hrow : c.row.val = 0) {k : Fin Wc} {ρ : Fin K} {ops₁ ops₂} {T₁ T₂}
    (h₁ : Realizes crun c k ρ f j0 ops₁ T₁) (h₂ : Realizes crun c k ρ f j0 ops₂ T₂) :
    Realizes crun c k ρ f j0 (ops₁ ++ ops₂) (T₂ * T₁) := by
  intro Arr
  have : CCoreNode.runOps crun c (ops₁ ++ ops₂) Arr =
      CCoreNode.runOps crun c ops₂ (CCoreNode.runOps crun c ops₁ Arr) := List.foldl_append ..
  rw [this, h₂, h₁, opL_comp _ hfit ρ (roleP_coreSet c hrow k ρ)]

theorem Realizes.flatMap (hfit : j0 + mH * f ≤ D) {c : RowClass (layerLayout A K D S)}
    (hrow : c.row.val = 0) {k : Fin Wc} {ρ : Fin K} {α : Type*} (l : List α)
    (g : α → List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child))
    (T : α → Matrix (Fin f → Pt 100) (Fin f → Pt 100) ℂ)
    (h : ∀ a ∈ l, Realizes crun c k ρ f j0 (g a) (T a)) :
    Realizes crun c k ρ f j0 (l.flatMap g) ((l.map T).reverse.prod) := by
  induction l with
  | nil => exact Realizes.nil hfit c k ρ
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
    exact (h a (by simp)).append hfit hrow (ih fun b hb => h b (by simp [hb]))

/-- A list of role primitives is a depth-0 procedure run in the role class. -/
theorem runOps_prims (c : RowClass (layerLayout A K D S)) (k : Fin Wc)
    (l : List (Step (layerLayout A K D S) (Fin rr → ℂ)))
    (Arr : (layerLayout A K D S).Addr → (Fin rr → ℂ)) :
    CCoreNode.runOps crun c (l.map (RoleOp.prim k)) Arr = ProcK.run 0 l (c.sub Wc Wc_pos k) Arr := by
  simp only [CCoreNode.runOps, List.foldl_map]
  rfl

end Realize

/-! ## 7. Packed row additions -/

section Rows

variable {rr : ℕ} {Child : Type}

theorem layerAddr_ext {x y : LayerAddr A K D S} (h1 : x.1 = y.1) (h3 : x.2.2 = y.2.2)
    (h2 : ∀ ch t, xbit x ch t = xbit y ch t) : x = y := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  simp only at h1 h3
  subst h1 h3
  congr
  funext ch t
  have := h2 ch.val t.val
  unfold xbit at this
  rwa [dif_pos ⟨ch.isLt, t.isLt⟩, dif_pos ⟨ch.isLt, t.isLt⟩, Fin.eta, Fin.eta] at this

theorem slot_mem_iff {f i t col : ℕ} (hcol : col < f) :
    (i * f ≤ t * f + col ∧ t * f + col < i * f + f) ↔ t = i := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_trichotomy t i with h | h | h
    · have : (t + 1) * f ≤ i * f := Nat.mul_le_mul_right f h
      rw [add_one_mul] at this
      omega
    · exact h
    · have : (i + 1) * f ≤ t * f := Nat.mul_le_mul_right f h
      rw [add_one_mul] at this
      omega
  · rintro rfl
    omega

/-- Decomposition of a chunk index of the group into slot and column. -/
theorem group_decomp {f j0 ch : ℕ} (h1 : j0 ≤ ch) (h2 : ch < j0 + mH * f) :
    ∃ t col, t < mH ∧ col < f ∧ ch = j0 + t * f + col := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at h2; omega)
  refine ⟨(ch - j0) / f, (ch - j0) % f, ?_, Nat.mod_lt _ hf, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  · have := Nat.div_add_mod' (ch - j0) f
    omega

theorem decide_add_bool : ∀ a b : Bool,
    decide (((if a = true then (1 : ZMod 2) else 0) + (if b = true then 1 else 0)) = 1) = xor a b := by
  decide

/-- One row addition on a point: coordinate `cubeEquiv.symm i` += coordinate `cubeEquiv.symm j`. -/
def rowPt (p : Fin mH × Fin mH) (v : Pt 100) : Pt 100 :=
  Function.update v (cubeEquiv.symm p.1) (v (cubeEquiv.symm p.1) + v (cubeEquiv.symm p.2))

/-- Column-wise row addition. -/
def rowX {f : ℕ} (p : Fin mH × Fin mH) (X : Fin f → Pt 100) : Fin f → Pt 100 :=
  fun col => rowPt p (X col)

theorem rowPt_rowPt (p : Fin mH × Fin mH) (hp : p.1 ≠ p.2) (v : Pt 100) :
    rowPt p (rowPt p v) = v := by
  have hne : cubeEquiv.symm p.2 ≠ cubeEquiv.symm p.1 := fun h => hp (cubeEquiv.symm.injective h).symm
  unfold rowPt
  rw [Function.update_self, Function.update_of_ne hne, Function.update_idem]
  have : v (cubeEquiv.symm p.1) + v (cubeEquiv.symm p.2) + v (cubeEquiv.symm p.2) =
      v (cubeEquiv.symm p.1) := by
    have h2 : ∀ a b : ZMod 2, a + b + b = a := by decide
    exact h2 _ _
  rw [this, Function.update_eq_self]

/-- The packed row addition `rowAddL` in core coordinates. -/
theorem rowAddL_eq (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (p : Fin mH × Fin mH)
    (x : LayerAddr A K D S) :
    rowAddL ρ f j0 p.1.val p.2.val x = coreSet ρ f j0 x (rowX p (coreX ρ f j0 x)) := by
  refine layerAddr_ext rfl rfl fun ch t => ?_
  by_cases hb : ch < D ∧ t < K
  · by_cases hg : t = ρ.val ∧ j0 ≤ ch ∧ ch < j0 + mH * f
    · obtain ⟨ht, hg1, hg2⟩ := hg
      subst ht
      obtain ⟨t', col, ht', hcol, rfl⟩ := group_decomp hg1 hg2
      rw [xbit_coreSet_sel hfit ρ x _ t' col ht' hcol]
      unfold rowX rowPt
      rw [Function.update_apply]
      have hrow : (rowAddL ρ f j0 p.1.val p.2.val x).2.1 ⟨j0 + t' * f + col, hb.1⟩ ρ =
          if t' = p.1.val then xor (x.2.1 ⟨j0 + t' * f + col, hb.1⟩ ρ)
            (xbit x (j0 + p.2.val * f + col) ρ.val) else x.2.1 ⟨j0 + t' * f + col, hb.1⟩ ρ := by
        unfold rowAddL
        dsimp only
        have hiff := slot_mem_iff (i := p.1.val) (t := t') hcol
        by_cases hti : t' = p.1.val
        · rw [if_pos ⟨rfl, by subst hti; omega, by subst hti; omega⟩, if_pos hti]
          have e1 : j0 + t' * f + col - p.1.val * f + p.2.val * f = j0 + p.2.val * f + col := by
            subst hti
            omega
          rw [e1]
        · rw [if_neg (fun h => hti (hiff.mp ⟨by omega, by omega⟩)), if_neg hti]
      have hxb : ∀ y : LayerAddr A K D S, xbit y (j0 + t' * f + col) ρ.val =
          y.2.1 ⟨j0 + t' * f + col, hb.1⟩ ρ := by
        intro y
        unfold xbit
        rw [dif_pos ⟨hb.1, ρ.isLt⟩, Fin.eta]
      rw [hxb, hrow, ← hxb x]
      by_cases hti : t' = p.1.val
      · have hsym : cubeEquiv.symm ⟨t', ht'⟩ = cubeEquiv.symm p.1 := by
          congr 1
          exact Fin.ext hti
        rw [if_pos hti, if_pos hsym, coreX_apply ρ x _ p.1.val p.1.isLt,
          coreX_apply ρ x _ p.2.val p.2.isLt]
        have e2 : j0 + p.1.val * f + col = j0 + t' * f + col := by rw [hti]
        rw [e2, decide_add_bool]
      · have hsym : cubeEquiv.symm ⟨t', ht'⟩ ≠ cubeEquiv.symm p.1 := by
          intro h
          exact hti (congrArg Fin.val (cubeEquiv.symm.injective h))
        rw [if_neg hti, if_neg hsym, coreX_apply ρ x _ t' ht', decide_ite_bool]
    · rw [xbit_coreSet_other ρ x _ ch t hg]
      unfold xbit rowAddL
      rw [dif_pos hb, dif_pos hb]
      dsimp only
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      apply hg
      refine ⟨congrArg Fin.val h1, by omega, ?_⟩
      have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt p.1.isLt)
      rw [Nat.succ_mul] at this
      omega
  · unfold xbit
    rw [dif_neg hb, dif_neg hb]

end Rows

/-! ## 8. Words of row additions realize move operators -/

section Words

variable {rr : ℕ} {Child : Type}

/-- Pull by a map of core coordinates, on the addresses satisfying `P`. -/
def pullL (ρ : Fin K) (f j0 : ℕ) (P : LayerAddr A K D S → Prop) [DecidablePred P]
    (g : (Fin f → Pt 100) → (Fin f → Pt 100)) (z : RArr (LayerAddr A K D S) rr) :
    RArr (LayerAddr A K D S) rr :=
  fun x => if P x then z (coreSet ρ f j0 x (g (coreX ρ f j0 x))) else z x

theorem pullL_comp (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (P : LayerAddr A K D S → Prop)
    [DecidablePred P] (hP : ∀ x Y, P (coreSet ρ f j0 x Y) ↔ P x)
    (g₁ g₂ : (Fin f → Pt 100) → (Fin f → Pt 100)) (z : RArr (LayerAddr A K D S) rr) :
    pullL ρ f j0 P g₂ (pullL ρ f j0 P g₁ z) = pullL ρ f j0 P (g₁ ∘ g₂) z := by
  funext x
  by_cases hx : P x
  · simp only [pullL, if_pos hx, hP, coreX_coreSet hfit, coreSet_coreSet, Function.comp_apply]
  · simp only [pullL, if_neg hx]

theorem pullL_id (hfit : j0 + mH * f ≤ D) (ρ : Fin K) (P : LayerAddr A K D S → Prop)
    [DecidablePred P] (z : RArr (LayerAddr A K D S) rr) : pullL ρ f j0 P id z = z := by
  funext x
  by_cases hx : P x
  · simp only [pullL, if_pos hx, id, coreSet_coreX hfit]
  · simp only [pullL, if_neg hx]

/-- The row operations of one packed row addition of `coreEdgeOps` (slot `p.2` into `p.1`). -/
noncomputable def rowAddOps (ρ : Fin K) (f j0 : ℕ) (k : Fin Wc) (p : Fin mH × Fin mH) :
    List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  (packedAddProc (Ly := layerLayout A K D S) (β := Fin rr → ℂ) (f * K) K ρ.val f
    ⟨1 + (j0 + p.2.val * f) * K, 1 + (j0 + p.1.val * f) * K,
      1 + (j0 + (thirdSlot p.1.val p.2.val) * f) * K⟩ :
      List (Step (layerLayout A K D S) (Fin rr → ℂ))).map (.prim k)

theorem thirdSlot_spec (i j : ℕ) :
    thirdSlot i j ≠ i ∧ thirdSlot i j ≠ j ∧ thirdSlot i j < 3 := by
  unfold thirdSlot
  split_ifs <;> omega

/-- The Lemma A.9 (`lem:transfer13`) layout hypotheses for three distinct slots of a node. -/
theorem packedHyps_slots {ρ : Fin K} {c : RowClass (layerLayout A K D S)}
    (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) (i j t3 : ℕ) (hi : i < mH) (hj : j < mH)
    (ht3 : t3 < mH) (hij : i ≠ j) (hit : i ≠ t3) (hjt : j ≠ t3) :
    PackedHyps (layerLayout A K D S) (f * K) K ρ.val f
      ⟨1 + (j0 + j * f) * K, 1 + (j0 + i * f) * K, 1 + (j0 + t3 * f) * K⟩ := by
  have hs : ∀ s, s < mH → 1 + (j0 + s * f) * K + f * K ≤ D * K + 1 := by
    intro s hsm
    have h1 := CCoreNode.slot_le hN.fits hsm
    have h2 : (j0 + s * f + f) * K ≤ D * K := Nat.mul_le_mul_right K h1
    have h3 : (j0 + s * f + f) * K = (j0 + s * f) * K + f * K := by ring
    omega
  have hdisj : ∀ s s', s ≠ s' → 1 + (j0 + s * f) * K + f * K ≤ 1 + (j0 + s' * f) * K ∨
      1 + (j0 + s' * f) * K + f * K ≤ 1 + (j0 + s * f) * K := by
    intro s s' hss'
    rcases Nat.lt_or_gt_of_ne hss' with h | h
    · left
      have h1 : (s + 1) * f ≤ s' * f := Nat.mul_le_mul_right f h
      have h2 : (j0 + (s + 1) * f) * K ≤ (j0 + s' * f) * K := Nat.mul_le_mul_right K (by omega)
      have h3 : (j0 + (s + 1) * f) * K = (j0 + s * f) * K + f * K := by ring
      omega
    · right
      have h1 : (s' + 1) * f ≤ s * f := Nat.mul_le_mul_right f h
      have h2 : (j0 + (s' + 1) * f) * K ≤ (j0 + s * f) * K := Nat.mul_le_mul_right K (by omega)
      have h3 : (j0 + (s' + 1) * f) * K = (j0 + s' * f) * K + f * K := by ring
      omega
  have hn : (layerLayout A K D S).n = D * K + 2 := rfl
  refine ⟨hN.K6, rfl, ρ.isLt, hN.f1, ?_, ?_, ?_, hdisj j i (Ne.symm hij), hdisj j t3 hjt,
    hdisj i t3 hit, ?_⟩
  · have := hs j hj
    simp only [hn]
    omega
  · have := hs i hi
    simp only [hn]
    omega
  · have := hs t3 ht3
    simp only [hn]
    omega
  · intro m hm
    apply layer_r_mid
    · rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only at h1 <;> omega
    · have := hs j hj
      have := hs i hi
      have := hs t3 ht3
      rcases hm with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ <;> simp only at h2 <;> omega

variable {crun : Child → RowClass (layerLayout A K D S) →
  ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ))}

/-- One packed row addition is the pull by the column-wise row operation. -/
theorem realizes_rowAdd (hPP : PackedProcCorrectStmt) (hR8 : RunEightSpecStmt)
    (hPA : PackedAgreeStmt) (hXor : AddrXorAllEncodeStmt) {ρ : Fin K}
    {c : RowClass (layerLayout A K D S)} (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) (k : Fin Wc)
    (p : Fin mH × Fin mH) (hp : p.1 ≠ p.2) (Arr : (layerLayout A K D S).Addr → (Fin rr → ℂ)) :
    decodeArr (CCoreNode.runOps crun c (rowAddOps ρ f j0 k p) Arr) =
      pullL ρ f j0 (roleP c k) (rowX p) (decodeArr Arr) := by
  have hp' : p.1.val ≠ p.2.val := fun h => hp (Fin.ext h)
  obtain ⟨h3i, h3j, h3⟩ := thirdSlot_spec p.1.val p.2.val
  have hPH := packedHyps_slots hN p.1.val p.2.val (thirdSlot p.1.val p.2.val) p.1.isLt p.2.isLt
    (by norm_num at h3 ⊢; omega) hp' (Ne.symm h3i) (Ne.symm h3j)
  have hrow : (c.sub Wc Wc_pos k).row.val = 0 := by rw [sub_row]; exact hN.row0
  unfold rowAddOps
  have hpr := runOps_prims (crun := crun) c k (packedAddProc (Ly := layerLayout A K D S)
    (β := Fin rr → ℂ) (f * K) K ρ.val f ⟨1 + (j0 + p.2.val * f) * K, 1 + (j0 + p.1.val * f) * K,
      1 + (j0 + (thirdSlot p.1.val p.2.val) * f) * K⟩) Arr
  rw [hpr, hPP hR8 hPA (layerLayout A K D S) (Fin rr → ℂ) (f * K) K ρ.val f _ hPH
    (c.sub Wc Wc_pos k) (Or.inl (by simp only [hrow]; omega)) (Or.inl (by simp only [hrow]; omega))
    (Or.inl (by simp only [hrow]; omega)) Arr]
  funext x
  simp only [decodeArr, pullL]
  by_cases h : roleP c k x
  · rw [if_pos h, if_pos (show (c.sub Wc Wc_pos k).mem (encodeAddr x) from h),
      hXor A K D S ρ f j0 p.1.val p.2.val _ hN.f1 p.1.isLt p.2.isLt hN.fits x,
      rowAddL_eq hN.fits ρ p x]
  · rw [if_neg h, if_neg (show ¬ (c.sub Wc Wc_pos k).mem (encodeAddr x) from h)]

/-- `N N' = 1 → N' N = 1` for binary matrices on the cube (stated for a general `h`, so that the
instance search does not run at `h = 100`). -/
theorem cube_mul_comm {h : ℕ} {N N' : Matrix (Cube h) (Cube h) (ZMod 2)} (hNN' : N * N' = 1) :
    N' * N = 1 :=
  mul_eq_one_comm.mp hNN'

/-- The pull of a word of row additions (time order). -/
def wordPt (l : List (Fin mH × Fin mH)) : Pt 100 → Pt 100 := l.foldr (fun p g => rowPt p ∘ g) id

theorem wordPt_rowsMove (l : List (Fin mH × Fin mH)) (hl : ∀ p ∈ l, p.1 ≠ p.2) (v : Pt 100) :
    wordPt l (rowsMove l v) = v := by
  induction l generalizing v with
  | nil => rfl
  | cons p l ih =>
    show rowPt p (wordPt l (rowsMove l (rowPt p v))) = v
    rw [ih (fun q hq => hl q (by simp [hq])), rowPt_rowPt p (hl p (by simp))]

theorem wordPt_eq (l : List (Fin mH × Fin mH)) (hl : ∀ p ∈ l, p.1 ≠ p.2)
    (N N' : Matrix (Cube 100) (Cube 100) (ZMod 2)) (hNN' : N * N' = 1)
    (hmove : ∀ v, rowsMove l v = N'.mulVec v) (v : Pt 100) : wordPt l v = N.mulVec v := by
  have h1 : N' * N = 1 := cube_mul_comm hNN'
  have h2 : rowsMove l (N.mulVec v) = v := by
    rw [hmove, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  calc wordPt l v = wordPt l (rowsMove l (N.mulVec v)) := by rw [h2]
    _ = N.mulVec v := wordPt_rowsMove l hl _

theorem realizes_word (hPP : PackedProcCorrectStmt) (hR8 : RunEightSpecStmt)
    (hPA : PackedAgreeStmt) (hXor : AddrXorAllEncodeStmt) {ρ : Fin K}
    {c : RowClass (layerLayout A K D S)} (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) (k : Fin Wc)
    (l : List (Fin mH × Fin mH)) (hl : ∀ p ∈ l, p.1 ≠ p.2)
    (Arr : (layerLayout A K D S).Addr → (Fin rr → ℂ)) :
    decodeArr (CCoreNode.runOps crun c (l.flatMap (rowAddOps ρ f j0 k)) Arr) =
      pullL ρ f j0 (roleP c k) (fun X col => wordPt l (X col)) (decodeArr Arr) := by
  induction l generalizing Arr with
  | nil => exact (pullL_id hN.fits ρ _ _).symm
  | cons p l ih =>
    rw [List.flatMap_cons]
    have hsplit : CCoreNode.runOps crun c (rowAddOps ρ f j0 k p ++ l.flatMap (rowAddOps ρ f j0 k))
        Arr = CCoreNode.runOps crun c (l.flatMap (rowAddOps ρ f j0 k))
          (CCoreNode.runOps crun c (rowAddOps ρ f j0 k p) Arr) := List.foldl_append ..
    rw [hsplit, ih (fun q hq => hl q (by simp [hq])),
      realizes_rowAdd hPP hR8 hPA hXor hN k p (hl p (by simp)) Arr,
      pullL_comp hN.fits ρ _ (roleP_coreSet c hN.row0 k ρ)]
    rfl

theorem tpow_permOp_eq (N : Matrix (Cube 100) (Cube 100) (ZMod 2)) (f : ℕ) :
    tpow f (permOp N) = fun X Y => if X = (fun col => N.mulVec (Y col)) then 1 else 0 := by
  funext X Y
  simp only [tpow, permOp]
  by_cases h : X = fun col => N.mulVec (Y col)
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro col _
    rw [if_pos (congrFun h col)]
  · rw [if_neg h]
    have : ∃ col, X col ≠ N.mulVec (Y col) := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    obtain ⟨col, hcol⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ col) (if_neg hcol)

/-- A word of row additions with `rowsMove l = N'` realizes the move operator `P_{N'}^{⊗f}`. -/
theorem realizes_word_perm (hPP : PackedProcCorrectStmt) (hR8 : RunEightSpecStmt)
    (hPA : PackedAgreeStmt) (hXor : AddrXorAllEncodeStmt) {ρ : Fin K}
    {c : RowClass (layerLayout A K D S)} (hN : CCoreNode.NodeHypC A K D S ρ f j0 c) (k : Fin Wc)
    (l : List (Fin mH × Fin mH)) (hl : ∀ p ∈ l, p.1 ≠ p.2)
    (N N' : Matrix (Cube 100) (Cube 100) (ZMod 2)) (hNN' : N * N' = 1)
    (hmove : ∀ v, rowsMove l v = N'.mulVec v) :
    Realizes crun c k ρ f j0 (l.flatMap (rowAddOps ρ f j0 k)) (tpow f (permOp N')) := by
  intro Arr
  have h1 : N' * N = 1 := cube_mul_comm hNN'
  rw [realizes_word hPP hR8 hPA hXor hN k l hl Arr, tpow_permOp_eq,
    opL_perm (roleP c k) ρ (fun X col => N.mulVec (X col)) (fun Y col => N'.mulVec (Y col))
      (fun X => by funext col; simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec])
      (fun Y => by funext col; simp only [Matrix.mulVec_mulVec, hNN', Matrix.one_mulVec])]
  have hw : (fun (X : Fin f → Pt 100) col => wordPt l (X col)) =
      fun (X : Fin f → Pt 100) col => N.mulVec (X col) := by
    funext X col
    exact wordPt_eq l hl N N' hNN' hmove (X col)
  rw [hw]
  rfl

end Words

/-! ## 9. Slot coordinates -/

/-- The coordinate of slot `t` of a node (`cubeEquiv.symm t` for `t < mH`; total). -/
noncomputable def slotCoord (t : ℕ) : Cube 100 :=
  if h : t < mH then cubeEquiv.symm ⟨t, h⟩ else cubeEquiv.symm ⟨0, by norm_num⟩

theorem slotCoord_of_lt {t : ℕ} (h : t < mH) : slotCoord t = cubeEquiv.symm ⟨t, h⟩ := dif_pos h

end CCoreEdgeAux

end SubNLogN.Math.Networks
