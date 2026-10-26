import SubNLogN.Math.Networks.AppCCore
import SubNLogN.Math.Networks.AppCFun
import SubNLogN.Math.Networks.AppCFun3

/-!
# Lemma A.10 (`lem:transfer-phase`) node/edge interface (shared across the node, edge and recursion proofs of `CCoreProcCorrectStmt`)

Definitions for one internal node of `cCoreProc` (`AppCCore.lean`), run in a class `c` of
`layerLayout A K D S`, with `f` columns and group start `j0`: slot `t < mH` consists of the chunks
`j0 + t·f + col` (`col < f`), and slot `t` corresponds to the coordinate `cubeEquiv.symm t` of `𝔽₂^m`.

* `NodeHypC`: layout hypotheses of the node;
* `runOps`: the fold of a node over its role operations
  (`ProcK.run (k+1) [.node Wc Wc_pos ops] c = runOps (ProcK.run k) c ops`);
* `slotBits`, `alignL`, `roleAddrC`, `roleStateC`: the *role state* of a layout array. Role `w` holds
  the array `(X, y, i) ↦ Arr (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w) X y)) i` on
  `(Fin f → Pt 100) × (LayerAddr A K D S × Fin rr)`; the spectator `y` supplies every field other than
  the `mH·f` selected bits of the group, and its prefix is moved to role `w` (same role position);
* `EdgeRoleSpec`: the edge operations of an edge `e ∈ edges w` act on role states as `cxEdgeOps f`
  (proved in `Proofs/CCoreEdge.lean`);
* `ChildSpecC`: child `t`, run in a role class of the node, computes `C^{⊗f}` on slot `t` (the shape
  of the recursion hypothesis of `CCoreProcCorrectStmt`);
* basic facts (proved here): `decodeAddr_encodeAddr` (hence `decodeEncodeAddr_holds`),
  `encodeAddr_decodeAddr`, `encodeAddr_bit`, `alignL_fst_val`, `roleAddrC_mem`;
* `CxNodeCorrectStmt` (`Proofs/CCoreNode.lean`) and `CoreEdgeRoleSpecStmt` (`Proofs/CCoreEdge.lean`):
  the node and edge contract statements.
-/

namespace SubNLogN.Math.Networks

namespace CCoreNode

open Model SubNLogN.Math.Walsh

variable {A K D S rr : ℕ}

/-- Layout hypotheses of one internal node with `f` columns and group start `j0` in class `c`. -/
structure NodeHypC (A K D S : ℕ) (ρ : Fin K) (f j0 : ℕ) (c : RowClass (layerLayout A K D S)) :
    Prop where
  K6 : 6 ≤ K
  f1 : 1 ≤ f
  fits : j0 + mH * f ≤ D
  row0 : c.row.val = 0
  div : c.μ * Wc ∣ A

/-- The fold of a `W_c`-node over its role operations in class `c`. -/
noncomputable abbrev runOps {L : Layout} {β Child : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L)
    (ops : List (RoleOp L β Wc Child)) (Arr : L.Addr → β) : L.Addr → β :=
  ops.foldl (fun A o => o.run crun c Wc_pos A) Arr

theorem pos_of_lt_mul {i n f : ℕ} (hi : i < n * f) : 0 < f :=
  Nat.pos_of_ne_zero (by rintro rfl; simp at hi)

theorem div_lt_of_lt_mul' {i n f : ℕ} (hi : i < n * f) : i / f < n :=
  Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)

/-- The bound of slot `t`: chunks `j0 + t·f, …, j0 + t·f + f − 1` lie below `D`. -/
theorem slot_le {D f j0 t : ℕ} (h : j0 + mH * f ≤ D) (ht : t < mH) : j0 + t * f + f ≤ D := by
  have : t * f + f ≤ mH * f := by
    have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt ht)
    rw [Nat.succ_mul] at this
    exact this
  omega

/-- `X : Fin f → Pt 100` as the `mH·f` selected bits of the group: index `t·f + col` holds
`X col (cubeEquiv.symm t)`. -/
def slotBits (f : ℕ) (X : Fin f → Pt 100) : Fin (mH * f) → Bool := fun i =>
  decide (X ⟨i.val % f, Nat.mod_lt _ (pos_of_lt_mul i.isLt)⟩
    (cubeEquiv.symm ⟨i.val / f, div_lt_of_lt_mul' i.isLt⟩) = 1)

/-- The prefix (row field `0`) of `y` moved to role `k` of a node in class `c`, at the same role
position: the layout's `aligned c Wc · k` on the prefix field. -/
noncomputable def alignL (c : RowClass (layerLayout A K D S)) (k : Fin Wc) (y : LayerAddr A K D S) :
    LayerAddr A K D S :=
  (if hv : c.res + c.μ * (k.val + Wc * ((y.1.val / c.μ) / Wc)) < A then
      ⟨c.res + c.μ * (k.val + Wc * ((y.1.val / c.μ) / Wc)), hv⟩ else y.1, y.2.1, y.2.2)

/-- The address of the point `(X, y)` of role `k`: `y` moved to role `k`, with the selected bits of the
group overwritten by `X`. -/
noncomputable def roleAddrC (c : RowClass (layerLayout A K D S)) (ρ : Fin K) (f j0 : ℕ) (k : Fin Wc)
    (X : Fin f → Pt 100) (y : LayerAddr A K D S) : LayerAddr A K D S :=
  groupSel ρ j0 (mH * f) (alignL c k y) (slotBits f X)

/-- The role state of a layout array at the node: role `w` holds
`(X, y, i) ↦ Arr (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w) X y)) i`. -/
noncomputable def roleStateC (c : RowClass (layerLayout A K D S)) (ρ : Fin K) (f j0 : ℕ)
    (Arr : (layerLayout A K D S).Addr → (Fin rr → ℂ)) :
    Role .complex 100 → ((Fin f → Pt 100) × (LayerAddr A K D S × Fin rr) → ℂ) :=
  fun w z => Arr (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w) z.1 z.2.1)) z.2.2

/-- **Edge interface.** For every wire `w` and edge `e ∈ edges w`, running the edge operations
`coreEdgeOps … (cdat e) … (roleIdxC w)` of the node changes the role state of `w` by the edge operator
`cxEdgeOps f` (that is, `(C_V C_U⁻¹)^{⊗f}` on the columns), leaves the other role states unchanged, and
changes no address outside `c`. -/
def EdgeRoleSpec (c : RowClass (layerLayout A K D S)) (ρ : Fin K) (f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) {Child : Type}
    (crun : Child → RowClass (layerLayout A K D S) →
      ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ)))
    (childOf : ℕ → Child) : Prop :=
  ∀ (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100), e ∈ edges w →
    ∀ Arr : (layerLayout A K D S).Addr → (Fin rr → ℂ),
      roleStateC c ρ f j0 (runOps crun c (coreEdgeOps ρ.val f j0 (cdat e) childOf (roleIdxC w)) Arr) =
        Function.update (roleStateC c ρ f j0 Arr) w (cxEdgeOps f w e (roleStateC c ρ f j0 Arr w)) ∧
      ∀ x, ¬ c.mem x →
        runOps crun c (coreEdgeOps ρ.val f j0 (cdat e) childOf (roleIdxC w)) Arr x = Arr x

/-- **Child interface** (the shape of the recursion hypothesis): child `t < mH`, run in the role
class `c.sub Wc Wc_pos k` of the node, computes `C^{⊗f}` on the selected bits of slot `t` of the
addresses of that class and leaves all other addresses unchanged. -/
def ChildSpecC (c : RowClass (layerLayout A K D S)) (ρ : Fin K) (f j0 : ℕ) (h : j0 + mH * f ≤ D)
    {Child : Type}
    (crun : Child → RowClass (layerLayout A K D S) →
      ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ)))
    (childOf : ℕ → Child) : Prop :=
  ∀ (k : Fin Wc) (t : ℕ) (ht : t < mH) (z : RArr (LayerAddr A K D S) rr),
    decodeArr (crun (childOf t) (c.sub Wc Wc_pos k) (encodeArr z)) =
      fun x => if (c.sub Wc Wc_pos k).mem (encodeAddr x) then
        cCoreVal ρ (j0 + t * f) f (slot_le h ht) z x else z x

/-! ## Basic facts: the layout round trip, field values, role membership -/

section Facts

variable {A K D S : ℕ}

theorem layer_r_mid (i : Fin (layerLayout A K D S).n) (h0 : i.val ≠ 0) (h1 : i.val ≤ D * K) :
    (layerLayout A K D S).r i = 2 := by
  simp [layerLayout, h0, h1]

theorem encodeAddr_zero (x : LayerAddr A K D S) (i : Fin (layerLayout A K D S).n)
    (hi : i.val = 0) : (encodeAddr x i).val = x.1.val := by
  unfold encodeAddr
  rw [dif_pos hi]

theorem encodeAddr_top (x : LayerAddr A K D S) (i : Fin (layerLayout A K D S).n)
    (h0 : i.val ≠ 0) (h1 : ¬ i.val ≤ D * K) : (encodeAddr x i).val = x.2.2.val := by
  unfold encodeAddr
  rw [dif_neg h0, dif_neg h1]

/-- Field of bit `t` of chunk `j` (`1 + jK + (K−1−t)`) lies in the layout. -/
theorem bitField_lt (j : Fin D) (t : Fin K) :
    1 + j.val * K + (K - 1 - t.val) < (layerLayout A K D S).n := by
  have h1 : j.val * K + K ≤ D * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at this
    exact this
  have := t.isLt
  show 1 + j.val * K + (K - 1 - t.val) < D * K + 2
  omega

/-- The encoded value of bit `t` of chunk `j`. -/
theorem encodeAddr_bit (x : LayerAddr A K D S) (j : Fin D) (t : Fin K) :
    (encodeAddr x ⟨1 + j.val * K + (K - 1 - t.val), bitField_lt j t⟩).val =
      if x.2.1 j t then 1 else 0 := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
  have ht := t.isLt
  have h0 : 1 + j.val * K + (K - 1 - t.val) ≠ 0 := by omega
  have h1 : 1 + j.val * K + (K - 1 - t.val) ≤ D * K := by
    have : j.val * K + K ≤ D * K := by
      have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at this
      exact this
    omega
  have hsub : 1 + j.val * K + (K - 1 - t.val) - 1 = (K - 1 - t.val) + j.val * K := by omega
  have hdiv : (1 + j.val * K + (K - 1 - t.val) - 1) / K = j.val := by
    rw [hsub, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (by omega), zero_add]
  have hmod : K - 1 - (1 + j.val * K + (K - 1 - t.val) - 1) % K = t.val := by
    rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold encodeAddr
  simp only [Fin.val_mk, dif_neg h0, dif_pos h1, dif_pos hK]
  have hj : (⟨(1 + j.val * K + (K - 1 - t.val) - 1) / K, by rw [hdiv]; exact j.isLt⟩ : Fin D) = j :=
    Fin.ext hdiv
  have ht' : (⟨K - 1 - (1 + j.val * K + (K - 1 - t.val) - 1) % K, by omega⟩ : Fin K) = t :=
    Fin.ext hmod
  simp only [hj, ht']

/-- `DecodeEncodeAddrStmt`: `decodeAddr ∘ encodeAddr = id`. -/
theorem decodeAddr_encodeAddr (x : LayerAddr A K D S) : decodeAddr (encodeAddr x) = x := by
  obtain ⟨a, bits, s⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    exact encodeAddr_zero _ _ rfl
  · funext j t
    show decide ((encodeAddr (a, bits, s) ⟨1 + j.val * K + (K - 1 - t.val), _⟩).val = 1) = bits j t
    rw [encodeAddr_bit]
    cases hb : bits j t <;> simp [hb]
  · apply Fin.ext
    exact encodeAddr_top _ _ (by simp) (by simp)

theorem decodeEncodeAddr_holds : DecodeEncodeAddrStmt := fun _ _ _ _ x => decodeAddr_encodeAddr x

/-- `encodeAddr ∘ decodeAddr = id` (every binary field holds `0` or `1`). -/
theorem encodeAddr_decodeAddr (y : (layerLayout A K D S).Addr) : encodeAddr (decodeAddr y) = y := by
  funext i
  apply Fin.ext
  by_cases h0 : i.val = 0
  · rw [encodeAddr_zero _ i h0]
    exact congrArg (fun j => (y j).val) (Fin.ext h0.symm)
  · by_cases h1 : i.val ≤ D * K
    · have hK : 0 < K := by
        rcases Nat.eq_zero_or_pos K with h | h
        · have h2 : D * K = 0 := by simp [h]
          omega
        · exact h
      have hm := Nat.mod_lt (i.val - 1) hK
      have hidx : 1 + (i.val - 1) / K * K + (K - 1 - (K - 1 - (i.val - 1) % K)) = i.val := by
        have := Nat.div_add_mod' (i.val - 1) K
        have h2 : K - 1 - (K - 1 - (i.val - 1) % K) = (i.val - 1) % K := by omega
        rw [h2]
        omega
      have hlt : (y i).val < 2 := by
        have h2 := (y i).isLt
        have h3 := layer_r_mid i h0 h1
        omega
      unfold encodeAddr
      rw [dif_neg h0, dif_pos h1]
      simp only [dif_pos hK]
      have hyi : ∀ hh, (y ⟨1 + (i.val - 1) / K * K + (K - 1 - (K - 1 - (i.val - 1) % K)), hh⟩).val =
          (y i).val := fun hh =>
        congrArg (fun j => (y j).val) (Fin.ext hidx : (⟨_, hh⟩ : Fin (layerLayout A K D S).n) = i)
      show (if decide ((y ⟨1 + (i.val - 1) / K * K + (K - 1 - (K - 1 - (i.val - 1) % K)), _⟩).val
          = 1) = true then 1 else 0) = (y i).val
      rw [hyi]
      by_cases hv : (y i).val = 1
      · simp [hv]
      · simp only [hv, decide_false, Bool.false_eq_true, if_false]
        omega
    · rw [encodeAddr_top _ i h0 h1]
      have : i.val = D * K + 1 := by
        have := i.isLt
        change i.val < D * K + 2 at this
        omega
      exact congrArg (fun j => (y j).val) (Fin.ext this.symm)

/-- Membership in a role class (stated for an arbitrary `W`, to be applied by unification). -/
theorem sub_mem_iff {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) (x : L.Addr) :
    (c.sub W hW k).mem x ↔ (x c.row).val % (c.μ * W) = c.res + c.μ * k.val := Iff.rfl

/-- The prefix of `alignL c k y` when `c.μ · W_c ∣ A`: the aligned row value of role `k`. -/
theorem alignL_fst_val (c : RowClass (layerLayout A K D S)) (hdiv : c.μ * Wc ∣ A) (k : Fin Wc)
    (y : LayerAddr A K D S) :
    (alignL c k y).1.val = c.res + c.μ * (k.val + Wc * ((y.1.val / c.μ) / Wc)) := by
  obtain ⟨m', hm'⟩ := hdiv
  have hμ := c.hμ
  have hres := c.hres
  have hk := k.isLt
  have hy := y.1.isLt
  have hpos : (y.1.val / c.μ) / Wc < m' := by
    rw [Nat.div_lt_iff_lt_mul Wc_pos, Nat.div_lt_iff_lt_mul hμ]
    calc y.1.val < A := hy
      _ = m' * Wc * c.μ := by rw [show m' * Wc * c.μ = c.μ * Wc * m' by ring]; exact hm'
  have hv : c.res + c.μ * (k.val + Wc * ((y.1.val / c.μ) / Wc)) < A := by
    set p := (y.1.val / c.μ) / Wc
    have h1 : k.val + 1 ≤ Wc := hk
    have h2 : p + 1 ≤ m' := hpos
    calc c.res + c.μ * (k.val + Wc * p) < c.μ + c.μ * (k.val + Wc * p) := by omega
      _ = c.μ * (k.val + 1) + c.μ * Wc * p := by ring
      _ ≤ c.μ * Wc + c.μ * Wc * p := by
          have := Nat.mul_le_mul_left c.μ h1
          omega
      _ = c.μ * Wc * (p + 1) := by ring
      _ ≤ c.μ * Wc * m' := Nat.mul_le_mul_left _ h2
      _ = A := hm'.symm
  unfold alignL
  rw [dif_pos hv]

/-- The prefix of a role address is the aligned row value of its role. -/
theorem roleAddrC_fst_val (c : RowClass (layerLayout A K D S)) (hdiv : c.μ * Wc ∣ A) (ρ : Fin K)
    (f j0 : ℕ) (k : Fin Wc) (X : Fin f → Pt 100) (y : LayerAddr A K D S) :
    (roleAddrC c ρ f j0 k X y).1.val = c.res + c.μ * (k.val + Wc * ((y.1.val / c.μ) / Wc)) :=
  alignL_fst_val c hdiv k y

/-- **Role addresses lie in their role class.** -/
theorem roleAddrC_mem {ρ : Fin K} {f j0 : ℕ} {c : RowClass (layerLayout A K D S)}
    (hN : NodeHypC A K D S ρ f j0 c) (k : Fin Wc) (X : Fin f → Pt 100) (y : LayerAddr A K D S) :
    (c.sub Wc Wc_pos k).mem (encodeAddr (roleAddrC c ρ f j0 k X y)) := by
  rw [sub_mem_iff]
  rw [encodeAddr_zero _ _ hN.row0, roleAddrC_fst_val c hN.div]
  have hres := c.hres
  have hk := k.isLt
  have hlt : c.res + c.μ * k.val < c.μ * Wc := by
    have : c.μ * (k.val + 1) ≤ c.μ * Wc := Nat.mul_le_mul_left _ hk
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  rw [Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt]

end Facts

/-! ## Node and edge contract statements for the Lemma A.10 (`lem:transfer-phase`) complex core -/

/-- CONTRACT (`Proofs/CCoreNode.lean`). One internal node of `cCoreProc` (`cxNodeOps`, `f` columns,
group start `j0`, class `c`) computes `C^{⊗(mH·f)}` on the selected bits `ρ` of the chunks
`j0, …, j0 + mH·f − 1` of every address of `c` and leaves the other addresses unchanged, for every
array, provided its edge operations satisfy the edge interface `EdgeRoleSpec`. -/
def CxNodeCorrectStmt : Prop :=
  ComplexNetCert → SerialEqFramedStmt 100 →
  ∀ {A K D S rr : ℕ} (ρ : Fin K) (f j0 : ℕ) (c : RowClass (layerLayout A K D S)),
    NodeHypC A K D S ρ f j0 c →
    ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) {Child : Type}
      (crun : Child → RowClass (layerLayout A K D S) →
        ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ)))
      (childOf : ℕ → Child), EdgeRoleSpec c ρ f j0 cdat crun childOf →
    ∀ (e : ℕ), e = mH * f → ∀ (h : j0 + e ≤ D) (z : RArr (LayerAddr A K D S) rr),
      decodeArr (runOps crun c (cxNodeOps ρ.val f j0 cdat childOf) (encodeArr z)) =
        fun x => if c.mem (encodeAddr x) then cCoreVal ρ j0 e h z x else z x

/-- CONTRACT (`Proofs/CCoreEdge.lean`). For valid edge data and children computing `C^{⊗f}` on their
slots, the edge operations of every edge realize `cxEdgeOps f` on role states (`EdgeRoleSpec`). -/
def CoreEdgeRoleSpecStmt : Prop :=
  ComplexNetCert → RunEightSpecStmt → PackedAgreeStmt → PackedProcCorrectStmt →
  ∀ {A K D S rr : ℕ} (ρ : Fin K) (f j0 : ℕ) (c : RowClass (layerLayout A K D S))
    (hN : NodeHypC A K D S ρ f j0 c)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
    (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ {Child : Type}
      (crun : Child → RowClass (layerLayout A K D S) →
        ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ)))
      (childOf : ℕ → Child), ChildSpecC c ρ f j0 hN.fits crun childOf →
    EdgeRoleSpec c ρ f j0 cdat crun childOf

end CCoreNode

end SubNLogN.Math.Networks
