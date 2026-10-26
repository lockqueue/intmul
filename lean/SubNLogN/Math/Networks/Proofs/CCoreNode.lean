import SubNLogN.Math.Networks.Proofs.CCoreRole
import SubNLogN.Math.Networks.Proofs.CCoreNatural
import SubNLogN.Math.Networks.Proofs.CCoreMasks
import SubNLogN.Math.Networks.Proofs.CCoreFolds
import SubNLogN.Math.Networks.Proofs.CCoreReindex

/-!
# Lemma A.10 (`lem:transfer-phase`): one internal node of `cCoreProc` computes `C^{⊗(m·f)}` (`CxNodeCorrectStmt`)

Proof plan (helpers in `SubNLogN.Math.Networks.CCoreNode.Node`). Fix a node in class `c` with `f` columns
and group start `j0` (`NodeHypC`); role states are `roleStateC` (`CCoreRole.lean`).
1. *Role classes*: a role address lies in `c` and in exactly one role class; its `roleIdx` is its role;
   `aligned` moves it to another role, keeping `(X, y)`.
2. *Transport* (`Transports ops F`: running `ops` maps role states by `F` and fixes every address outside
   `c`), closed under `++` and `flatMap`. Per operation of `cxNodeOps`:
   * source masks `zMask` on `X_a`: `applyCol (Zk f (u_a))`, so all of them give `cxPre f`;
   * edges: `EdgeRoleSpec` (hypothesis) gives `Function.update s w (cxEdgeOps f w e (s w))`, i.e. the
     `NodeEvent.edge` step; gates `gateOpC`: the scalar row `rowUpd` (naturality of `rowUpd` under the
     evaluation maps), i.e. the `NodeEvent.row` step; so the body and the sink edges run `nodeEvents`;
   * corrections (`zMask`, `i^{27f}` on `Y_a`, `−1` on `X_a`): `cxPost f`; relabel: `s ↦ s ∘ ρ`.
3. `SerialEqFramedStmt 100` turns `runEvents (nodeEvents …)` into `framedNet`; the array corollary of
   `ComplexNetCert` gives `C^{⊗mf}` on every role state: `applyCol (tpow f Cfull)`.
4. Reading the role state back at `(bits of x, x, i)` and reindexing `tpow f Cfull` as `CD (mH·f)` through
   `slotBits` gives `cCoreVal`.
-/

namespace SubNLogN.Math.Networks

namespace CCoreNode

namespace Node

open SubNLogN.Math.Walsh

variable {A K D S rr : ℕ}

/-! ### 1. Role classes -/

theorem sub_mem_c {L : Model.Layout} (c : Model.RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W)
    (x : L.Addr) (hx : (c.sub W hW k).mem x) : c.mem x := by
  rw [sub_mem_iff] at hx
  show (x c.row).val % c.μ = c.res
  have h1 : (x c.row).val % (c.μ * W) % c.μ = (x c.row).val % c.μ := Nat.mod_mul_right_mod _ _ _
  rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.hres] at h1
  exact h1.symm

theorem sub_mem_unique {L : Model.Layout} (c : Model.RowClass L) (W : ℕ) (hW : 0 < W)
    (k k' : Fin W) (x : L.Addr) (hx : (c.sub W hW k).mem x) (hx' : (c.sub W hW k').mem x) :
    k = k' := by
  rw [sub_mem_iff] at hx hx'
  have : c.μ * k.val = c.μ * k'.val := by omega
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left c.hμ this)

theorem roleIdx_of_sub_mem {L : Model.Layout} (c : Model.RowClass L) (W : ℕ) (hW : 0 < W)
    (k : Fin W) (x : L.Addr) (hx : (c.sub W hW k).mem x) : Model.roleIdx c W hW x = k := by
  have h2 : (x c.row).val % c.μ = c.res := sub_mem_c c W hW k x hx
  rw [sub_mem_iff] at hx
  apply Fin.ext
  show (x c.row).val / c.μ % W = k.val
  have h1 : (x c.row).val % (c.μ * W) = (x c.row).val % c.μ + c.μ * ((x c.row).val / c.μ % W) :=
    Nat.mod_mul
  rw [hx, h2] at h1
  have : c.μ * k.val = c.μ * ((x c.row).val / c.μ % W) := by omega
  exact (Nat.eq_of_mul_eq_mul_left c.hμ this).symm

theorem sub_mem_of_roleIdx {L : Model.Layout} (c : Model.RowClass L) (W : ℕ) (hW : 0 < W)
    (x : L.Addr) (hx : c.mem x) : (c.sub W hW (Model.roleIdx c W hW x)).mem x := by
  rw [sub_mem_iff]
  have h2 : (x c.row).val % c.μ = c.res := hx
  have h1 : (x c.row).val % (c.μ * W) = (x c.row).val % c.μ + c.μ * ((x c.row).val / c.μ % W) :=
    Nat.mod_mul
  rw [h1, h2]
  rfl

/-- The aligned prefix value of role `k` is below `A`. -/
theorem align_bound (c : Model.RowClass (layerLayout A K D S)) (hdiv : c.μ * Wc ∣ A) (k : Fin Wc)
    (y : LayerAddr A K D S) : c.res + c.μ * (k.val + Wc * ((y.1.val / c.μ) / Wc)) < A := by
  obtain ⟨m', hm'⟩ := hdiv
  have hμ := c.hμ
  have hres := c.hres
  have hk := k.isLt
  have hy := y.1.isLt
  have hpos : (y.1.val / c.μ) / Wc < m' := by
    rw [Nat.div_lt_iff_lt_mul Wc_pos, Nat.div_lt_iff_lt_mul hμ]
    calc y.1.val < A := hy
      _ = m' * Wc * c.μ := by rw [show m' * Wc * c.μ = c.μ * Wc * m' by ring]; exact hm'
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

section RoleAddr

variable {ρ : Fin K} {f j0 : ℕ} {c : Model.RowClass (layerLayout A K D S)}

theorem roleAddrC_mem_c (hN : NodeHypC A K D S ρ f j0 c) (k : Fin Wc) (X : Fin f → Pt 100)
    (y : LayerAddr A K D S) : c.mem (encodeAddr (roleAddrC c ρ f j0 k X y)) :=
  sub_mem_c c Wc Wc_pos k _ (roleAddrC_mem hN k X y)

theorem roleIdx_roleAddrC (hN : NodeHypC A K D S ρ f j0 c) (k : Fin Wc) (X : Fin f → Pt 100)
    (y : LayerAddr A K D S) :
    Model.roleIdx c Wc Wc_pos (encodeAddr (roleAddrC c ρ f j0 k X y)) = k :=
  roleIdx_of_sub_mem c Wc Wc_pos k _ (roleAddrC_mem hN k X y)

theorem eq_of_sub_mem_roleAddrC (hN : NodeHypC A K D S ρ f j0 c) (k k' : Fin Wc)
    (X : Fin f → Pt 100) (y : LayerAddr A K D S)
    (hm : (c.sub Wc Wc_pos k').mem (encodeAddr (roleAddrC c ρ f j0 k X y))) : k' = k :=
  sub_mem_unique c Wc Wc_pos k' k _ hm (roleAddrC_mem hN k X y)

theorem encodeAddr_congr_snd {x x' : LayerAddr A K D S} (h : x.2 = x'.2)
    (i : Fin (layerLayout A K D S).n) (hi : i.val ≠ 0) : encodeAddr x i = encodeAddr x' i := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := x'
  simp only at h
  subst h
  unfold encodeAddr
  rw [dif_neg hi, dif_neg hi]

/-- (Proved by `simp`, not `rfl`: a `rfl` here first tries `alignL c k y =?= y`, which evaluates
the `Decidable` instance of the prefix bound and hence `Wc = Fintype.card (Role …)`.) -/
theorem alignL_snd (k : Fin Wc) (y : LayerAddr A K D S) : (alignL c k y).2 = y.2 := by
  simp only [alignL, Prod.mk.eta]

theorem groupSel_snd_congr {e : ℕ} {x x' : LayerAddr A K D S} (h : x.2 = x'.2)
    (bs : Fin e → Bool) : (groupSel ρ j0 e x bs).2 = (groupSel ρ j0 e x' bs).2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := x'
  simp only at h
  subst h
  rfl

theorem roleAddrC_snd (k k' : Fin Wc) (X : Fin f → Pt 100) (y : LayerAddr A K D S) :
    (roleAddrC c ρ f j0 k X y).2 = (roleAddrC c ρ f j0 k' X y).2 :=
  groupSel_snd_congr ((alignL_snd k y).trans (alignL_snd k' y).symm) _

theorem rolePos_roleAddrC (hN : NodeHypC A K D S ρ f j0 c) (k : Fin Wc) (X : Fin f → Pt 100)
    (y : LayerAddr A K D S) :
    Model.rolePos c Wc (encodeAddr (roleAddrC c ρ f j0 k X y)) = (y.1.val / c.μ) / Wc := by
  unfold Model.rolePos
  rw [encodeAddr_zero _ _ hN.row0, roleAddrC_fst_val c hN.div,
    Nat.add_mul_div_left _ _ c.hμ, Nat.div_eq_of_lt c.hres, zero_add,
    Nat.add_mul_div_left _ _ Wc_pos, Nat.div_eq_of_lt k.isLt, zero_add]

/-- `aligned` moves a role address to another role, keeping `(X, y)`. -/
theorem aligned_roleAddrC (hN : NodeHypC A K D S ρ f j0 c) (k k' : Fin Wc) (X : Fin f → Pt 100)
    (y : LayerAddr A K D S) :
    Model.aligned c Wc (encodeAddr (roleAddrC c ρ f j0 k X y)) k' =
      encodeAddr (roleAddrC c ρ f j0 k' X y) := by
  unfold Model.aligned
  rw [rolePos_roleAddrC hN]
  have hrow : (layerLayout A K D S).r c.row = A := by simp [layerLayout, hN.row0]
  have hv : c.res + c.μ * (k'.val + Wc * ((y.1.val / c.μ) / Wc)) < (layerLayout A K D S).r c.row := by
    rw [hrow]
    exact align_bound c hN.div k' y
  unfold Model.withRow
  rw [dif_pos hv]
  funext i
  by_cases hi : i = c.row
  · subst hi
    rw [Function.update_self]
    apply Fin.ext
    rw [encodeAddr_zero _ _ hN.row0, roleAddrC_fst_val c hN.div]
  · rw [Function.update_of_ne hi]
    exact encodeAddr_congr_snd (roleAddrC_snd k k' X y) i
      (fun h => hi (Fin.ext (h.trans hN.row0.symm)))

end RoleAddr

/-! ### 2. Transport of role operations to role states -/

/-- Role states of the node. -/
abbrev RSt (A K D S rr f : ℕ) : Type :=
  Role .complex 100 → ((Fin f → Pt 100) × (LayerAddr A K D S × Fin rr) → ℂ)

section Transport

variable {ρ : Fin K} {f j0 : ℕ} {c : Model.RowClass (layerLayout A K D S)} {Child : Type}
  {crun : Child → Model.RowClass (layerLayout A K D S) →
    ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ))}

/-- Running `ops` maps role states by `F` and fixes every address outside `c`. -/
def Transports (c : Model.RowClass (layerLayout A K D S)) (ρ : Fin K) (f j0 : ℕ)
    (crun : Child → Model.RowClass (layerLayout A K D S) →
      ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ)))
    (ops : List (Model.RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child))
    (F : RSt A K D S rr f → RSt A K D S rr f) : Prop :=
  ∀ Arr, roleStateC c ρ f j0 (runOps crun c ops Arr) = F (roleStateC c ρ f j0 Arr) ∧
    ∀ x, ¬ c.mem x → runOps crun c ops Arr x = Arr x

theorem transports_nil : Transports c ρ f j0 crun [] id := fun _ => ⟨rfl, fun _ _ => rfl⟩

theorem transports_append {o₁ o₂ : List (Model.RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child)}
    {F₁ F₂ : RSt A K D S rr f → RSt A K D S rr f}
    (h₁ : Transports c ρ f j0 crun o₁ F₁) (h₂ : Transports c ρ f j0 crun o₂ F₂) :
    Transports c ρ f j0 crun (o₁ ++ o₂) (F₂ ∘ F₁) := by
  intro Arr
  have e : runOps crun c (o₁ ++ o₂) Arr = runOps crun c o₂ (runOps crun c o₁ Arr) :=
    List.foldl_append
  obtain ⟨h1a, h1b⟩ := h₁ Arr
  obtain ⟨h2a, h2b⟩ := h₂ (runOps crun c o₁ Arr)
  refine ⟨?_, ?_⟩
  · rw [e, h2a, h1a]
    rfl
  · intro x hx
    rw [e, h2b x hx, h1b x hx]

theorem transports_congr {o : List (Model.RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child)}
    {F G : RSt A K D S rr f → RSt A K D S rr f} (h : Transports c ρ f j0 crun o F)
    (hFG : ∀ s, F s = G s) : Transports c ρ f j0 crun o G :=
  fun Arr => ⟨(h Arr).1.trans (hFG _), (h Arr).2⟩

theorem transports_flatMap {α : Type*} (l : List α)
    (g : α → List (Model.RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child))
    (F : α → RSt A K D S rr f → RSt A K D S rr f)
    (h : ∀ a ∈ l, Transports c ρ f j0 crun (g a) (F a)) :
    Transports c ρ f j0 crun (l.flatMap g) (fun s => l.foldl (fun s a => F a s) s) := by
  induction l with
  | nil => exact transports_nil
  | cons a l ih =>
    rw [List.flatMap_cons]
    exact transports_congr (transports_append (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))) (fun s => rfl)

theorem transports_map {α : Type*} (l : List α)
    (g : α → Model.RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child)
    (F : α → RSt A K D S rr f → RSt A K D S rr f)
    (h : ∀ a ∈ l, Transports c ρ f j0 crun [g a] (F a)) :
    Transports c ρ f j0 crun (l.map g) (fun s => l.foldl (fun s a => F a s) s) := by
  induction l with
  | nil => exact transports_nil
  | cons a l ih =>
    rw [List.map_cons, show g a :: l.map g = [g a] ++ l.map g from rfl]
    exact transports_congr (transports_append (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))) (fun s => rfl)

/-- A primitive step on role `w0` changes only the role state of `w0`. -/
theorem transports_prim (hN : NodeHypC A K D S ρ f j0 c) (w0 : Role .complex 100)
    (st : Model.Step (layerLayout A K D S) (Fin rr → ℂ))
    (G : ((Fin f → Pt 100) × (LayerAddr A K D S × Fin rr) → ℂ) →
      ((Fin f → Pt 100) × (LayerAddr A K D S × Fin rr) → ℂ))
    (hG : ∀ Arr X y i, st.run Arr (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w0) X y)) i =
      G (roleStateC c ρ f j0 Arr w0) (X, y, i)) :
    Transports c ρ f j0 crun [.prim (roleIdxC w0) st]
      (fun s => Function.update s w0 (G (s w0))) := by
  intro Arr
  refine ⟨?_, ?_⟩
  · funext w z
    obtain ⟨X, y, i⟩ := z
    show Model.Step.runIn (c.sub Wc Wc_pos (roleIdxC w0)) st Arr
      (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w) X y)) i = _
    unfold Model.Step.runIn
    beta_reduce
    by_cases hw : w = w0
    · subst hw
      rw [if_pos (roleAddrC_mem hN _ X y), Function.update_self]
      exact hG Arr X y i
    · rw [if_neg (fun hm => hw (roleIdxC.injective
        (eq_of_sub_mem_roleAddrC hN _ _ X y hm)).symm), Function.update_of_ne hw]
      rfl
  · intro x hx
    show Model.Step.runIn (c.sub Wc Wc_pos (roleIdxC w0)) st Arr x = Arr x
    unfold Model.Step.runIn
    rw [if_neg (fun hm => hx (sub_mem_c c Wc Wc_pos _ x hm))]

/-- A scalar `recMap` on role `w0` multiplies its role state. -/
theorem transports_smul (hN : NodeHypC A K D S ρ f j0 c) (w0 : Role .complex 100) (a : ℂ) :
    Transports c ρ f j0 crun [.prim (roleIdxC w0) (.recMap fun v => a • v)]
      (fun s => Function.update s w0 (a • s w0)) :=
  transports_prim hN w0 _ (fun g => a • g) (fun _ _ _ _ => rfl)

end Transport

/-! ### Gates, relabel, edges -/

theorem rhoPermC_symm_apply (w : Role .complex 100) : rhoPermC.symm (roleIdxC w) = roleIdxC w.rho := by
  simp only [rhoPermC, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rfl

theorem edgeInto_mem' {w : Role .complex 100} {v : Vertex .complex 100}
    {e : Vertex .complex 100 × Vertex .complex 100} (he : edgeInto w v = some e) : e ∈ edges w := by
  unfold edgeInto at he
  exact List.mem_of_find?_eq_some he

section Ops

variable {ρ : Fin K} {f j0 : ℕ} {c : Model.RowClass (layerLayout A K D S)} {Child : Type}
  {crun : Child → Model.RowClass (layerLayout A K D S) →
    ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ))}

theorem transports_zMask (hN : NodeHypC A K D S ρ f j0 c) (w0 : Role .complex 100) (a : Addr 100) :
    Transports c ρ f j0 crun [.prim (roleIdxC w0) (zMask ρ.val f j0 a)]
      (fun s => Function.update s w0 (applyCol (Zk f (ua a)) (s w0))) := by
  refine transports_prim hN w0 _ _ (fun Arr X y i => ?_)
  show ((-1 : ℂ) ^ (∑ col ∈ Finset.range f, ∑ p : Cube 100,
      (ua a p).val * slotBit (A := A) (D := D) (S := S) K ρ.val f j0 (cubeEquiv p) col
        (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w0) X y)))) *
      Arr (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w0) X y)) i = _
  rw [Masks.zMask_sign hN a, Zk, Masks.applyCol_diagonal]
  rfl

theorem transports_gate (hN : NodeHypC A K D S ρ f j0 c) (j : Stage) (ι : Fix 100) (r : Fin 8) :
    Transports c ρ f j0 crun [gateOpC j ι r]
      (rowUpd .complex (2⁻¹ : ℂ) j ι (rowOp j r) ((rowSign j r : ℤ) : ℂ)) := by
  intro Arr
  refine ⟨?_, ?_⟩
  · funext w z
    obtain ⟨X, y, i⟩ := z
    show Model.gateRun c Wc Wc_pos (fun vals idx => rowUpd .complex (2⁻¹ : ℂ) j ι (rowOp j r)
        ((rowSign j r : ℤ) : ℂ) (fun w => vals (roleIdxC w)) (roleIdxC.symm idx)) Arr
        (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w) X y)) i = _
    unfold Model.gateRun
    rw [if_pos (roleAddrC_mem_c hN _ X y), roleIdx_roleAddrC hN]
    beta_reduce
    rw [Equiv.symm_apply_apply]
    simp only [aligned_roleAddrC hN]
    have e1 := Natural.rowUpd_natural (LinearMap.proj i : (Fin rr → ℂ) →ₗ[ℂ] ℂ) (2⁻¹ : ℂ) j ι (rowOp j r)
      ((rowSign j r : ℤ) : ℂ) (fun w' => Arr (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w') X y))) w
    have e2 := Natural.rowUpd_natural
      (LinearMap.proj (X, y, i) : ((Fin f → Pt 100) × (LayerAddr A K D S × Fin rr) → ℂ) →ₗ[ℂ] ℂ)
      (2⁻¹ : ℂ) j ι (rowOp j r) ((rowSign j r : ℤ) : ℂ) (roleStateC c ρ f j0 Arr) w
    simp only [LinearMap.proj_apply] at e1 e2
    rw [e1, e2]
    rfl
  · intro x hx
    show Model.gateRun c Wc Wc_pos (fun vals idx => rowUpd .complex (2⁻¹ : ℂ) j ι (rowOp j r)
        ((rowSign j r : ℤ) : ℂ) (fun w => vals (roleIdxC w)) (roleIdxC.symm idx)) Arr x = Arr x
    unfold Model.gateRun
    rw [if_neg hx]

theorem transports_relabel (hN : NodeHypC A K D S ρ f j0 c) :
    Transports c ρ f j0 crun [.relabel rhoPermC] (fun s w => s w.rho) := by
  intro Arr
  refine ⟨?_, ?_⟩
  · funext w z
    obtain ⟨X, y, i⟩ := z
    show Model.relabelRun c Wc Wc_pos rhoPermC Arr
      (encodeAddr (roleAddrC c ρ f j0 (roleIdxC w) X y)) i = _
    unfold Model.relabelRun
    rw [if_pos (roleAddrC_mem_c hN _ X y), roleIdx_roleAddrC hN, rhoPermC_symm_apply,
      aligned_roleAddrC hN]
    rfl
  · intro x hx
    show Model.relabelRun c Wc Wc_pos rhoPermC Arr x = Arr x
    unfold Model.relabelRun
    rw [if_neg hx]

theorem transports_edgeAt {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData}
    {childOf : ℕ → Child} (hedge : EdgeRoleSpec c ρ f j0 cdat crun childOf)
    (w : Role .complex 100) (v : Vertex .complex 100) :
    Transports c ρ f j0 crun (coreEdgeOpsAt ρ.val f j0 cdat childOf w v)
      (fun s => (NodeEvent.edge w v).run .complex (2⁻¹ : ℂ) (cxEdgeOps f) s) := by
  unfold coreEdgeOpsAt
  rcases he : edgeInto w v with _ | e
  · refine transports_congr transports_nil (fun s => ?_)
    simp only [NodeEvent.run, he, id, Function.update_eq_self]
  · intro Arr
    obtain ⟨h1, h2⟩ := hedge w e (edgeInto_mem' he) Arr
    refine ⟨?_, h2⟩
    rw [h1]
    simp only [NodeEvent.run, he]

end Ops

/-! ### 3. The node body runs the event list `nodeEvents`; assembly -/

theorem foldl_filterMap {α β γ : Type*} (h : α → Option β) (g : γ → β → γ) :
    ∀ (l : List α) (s : γ), (l.filterMap h).foldl g s = l.foldl (fun s a => (h a).toList.foldl g s) s
  | [], _ => rfl
  | a :: l, s => by
    rw [List.filterMap_cons]
    cases ha : h a with
    | none =>
      simp only [List.foldl_cons, ha, Option.toList, List.foldl_nil]
      exact foldl_filterMap h g l s
    | some b =>
      simp only [List.foldl_cons, ha, Option.toList, List.foldl_nil]
      exact foldl_filterMap h g l (g s b)

section Assembly

variable {ρ : Fin K} {f j0 : ℕ} {c : Model.RowClass (layerLayout A K D S)} {Child : Type}
  {crun : Child → Model.RowClass (layerLayout A K D S) →
    ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ))}
  {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {childOf : ℕ → Child}

/-- One event of the serialized framed network on role states. -/
noncomputable abbrev evRun (f : ℕ) (s : RSt A K D S rr f) (ev : NodeEvent .complex 100) :
    RSt A K D S rr f :=
  ev.run .complex (2⁻¹ : ℂ) (cxEdgeOps f) s

/-- The time block `(j, ι, r)`: edges of the touched wires, then the gate. -/
theorem transports_time (hN : NodeHypC A K D S ρ f j0 c)
    (hedge : EdgeRoleSpec c ρ f j0 cdat crun childOf) (j : Stage) (ι : Fix 100) (r : Fin 8) :
    Transports c ρ f j0 crun
      (((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
        match gateAt j ι r w with
        | some g => coreEdgeOpsAt ρ.val f j0 cdat childOf w (.gate g)
        | none => []) ++ [gateOpC j ι r])
      (fun s => (((Finset.univ : Finset (Role .complex 100)).toList.filterMap fun w =>
        (gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)) ++
          [NodeEvent.row j ι r]).foldl (evRun f) s) := by
  have h1 := transports_flatMap (c := c) (ρ := ρ) (j0 := j0) (crun := crun)
    (Finset.univ : Finset (Role .complex 100)).toList
    (fun w => match gateAt j ι r w with
      | some g => coreEdgeOpsAt ρ.val f j0 cdat childOf w (.gate g)
      | none => [])
    (fun w s => ((gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)).toList.foldl (evRun f) s)
    (fun w _ => by
      cases hg : gateAt j ι r w with
      | none => exact transports_nil
      | some g =>
        exact transports_congr (transports_edgeAt hedge w (.gate g)) (fun s => rfl))
  have h2 := transports_gate (crun := crun) hN j ι r
  refine transports_congr (transports_append h1 h2) (fun s => ?_)
  rw [List.foldl_append, foldl_filterMap]
  rfl

/-- The three stages of the node body. -/
theorem transports_body (hN : NodeHypC A K D S ρ f j0 c)
    (hedge : EdgeRoleSpec c ρ f j0 cdat crun childOf) :
    Transports c ρ f j0 crun
      ([Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix 100)).toList.flatMap fun ι =>
        (List.finRange 8).flatMap fun r =>
          ((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
            match gateAt j ι r w with
            | some g => coreEdgeOpsAt ρ.val f j0 cdat childOf w (.gate g)
            | none => []) ++ [gateOpC j ι r])
      (fun s => ([Stage.one, .two, .three].flatMap fun j =>
        (Finset.univ : Finset (Fix 100)).toList.flatMap fun ι =>
          (List.finRange 8).flatMap fun r =>
            ((Finset.univ : Finset (Role .complex 100)).toList.filterMap fun w =>
              (gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)) ++
                [NodeEvent.row j ι r]).foldl (evRun f) s) := by
  refine transports_congr (transports_flatMap _ _ _ (fun j _ =>
    transports_flatMap _ _ _ (fun ι _ =>
      transports_flatMap _ _ _ (fun r _ => transports_time hN hedge j ι r)))) (fun s => ?_)
  simp only [List.foldl_flatMap]

/-- The sink edges of the node. -/
theorem transports_sinks (hedge : EdgeRoleSpec c ρ f j0 cdat crun childOf) :
    Transports c ρ f j0 crun
      ((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
        coreEdgeOpsAt ρ.val f j0 cdat childOf w (.sink w))
      (fun s => ((Finset.univ : Finset (Role .complex 100)).toList.map fun w =>
        NodeEvent.edge w (.sink w)).foldl (evRun f) s) := by
  refine transports_congr (transports_flatMap _ _ (fun w s => evRun f s (NodeEvent.edge w (.sink w)))
    (fun w _ => transports_edgeAt hedge w (.sink w))) (fun s => ?_)
  rw [List.foldl_map]

end Assembly

/-! ### 4. Assembly -/

section Final

variable {ρ : Fin K} {f j0 : ℕ} {c : Model.RowClass (layerLayout A K D S)} {Child : Type}
  {crun : Child → Model.RowClass (layerLayout A K D S) →
    ((layerLayout A K D S).Addr → (Fin rr → ℂ)) → ((layerLayout A K D S).Addr → (Fin rr → ℂ))}
  {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {childOf : ℕ → Child}

/-- The corrections of one address `a`: `zMask` and `i^{27f}` on `Y_a`, `−1` on `X_a`. -/
theorem transports_postA (hN : NodeHypC A K D S ρ f j0 c) (a : Addr 100) :
    Transports c ρ f j0 crun
      [.prim (roleIdxC (.Y a)) (zMask ρ.val f j0 a),
       .prim (roleIdxC (.Y a)) (.recMap fun v => (Complex.I ^ (27 * f)) • v),
       .prim (roleIdxC (.X a)) (.recMap fun v => (-1 : ℂ) • v)]
      (fun s => Function.update (Function.update s (Role.Y a)
        ((Complex.I ^ (27 * f)) • applyCol (Zk f (ua a)) (s (Role.Y a)))) (Role.X a)
          ((-1 : ℂ) • s (Role.X a))) := by
  have h1 := transports_zMask (crun := crun) hN (.Y a) a
  have h2 := transports_smul (crun := crun) hN (.Y a) (Complex.I ^ (27 * f))
  have h3 := transports_smul (crun := crun) hN (.X a) (-1 : ℂ)
  refine transports_congr (transports_append (transports_append h1 h2) h3) (fun s => ?_)
  have hXY : (Role.X a : Role .complex 100) ≠ Role.Y a := fun h => by cases h
  simp only [Function.comp, Function.update_self, Function.update_idem,
    Function.update_of_ne hXY]

/-- **The node on role states**: every role state is mapped by `C^{⊗mf}` (`applyCol (tpow f Cfull)`),
and nothing outside `c` changes. -/
theorem node_transports (hcert : ComplexNetCert) (hser : SerialEqFramedStmt 100)
    (hN : NodeHypC A K D S ρ f j0 c) (hedge : EdgeRoleSpec c ρ f j0 cdat crun childOf) :
    Transports c ρ f j0 crun (cxNodeOps ρ.val f j0 cdat childOf)
      (fun s w => applyCol (tpow f Cfull) (s w)) := by
  have tPre := transports_map (c := c) (ρ := ρ) (j0 := j0) (crun := crun)
    (Finset.univ : Finset (Addr 100)).toList (fun a => .prim (roleIdxC (.X a)) (zMask ρ.val f j0 a))
    (fun a s => Function.update s (Role.X a) (applyCol (Zk f (ua a)) (s (Role.X a))))
    (fun a _ => transports_zMask hN (.X a) a)
  have tBody := transports_body (crun := crun) (cdat := cdat) (childOf := childOf) hN hedge
  have tSinks := transports_sinks (c := c) (ρ := ρ) (j0 := j0) (crun := crun) hedge
  have tPost := transports_flatMap (c := c) (ρ := ρ) (j0 := j0) (crun := crun)
    (Finset.univ : Finset (Addr 100)).toList
    (fun a => [.prim (roleIdxC (.Y a)) (zMask ρ.val f j0 a),
       .prim (roleIdxC (.Y a)) (.recMap fun v => (Complex.I ^ (27 * f)) • v),
       .prim (roleIdxC (.X a)) (.recMap fun v => (-1 : ℂ) • v)])
    _ (fun a _ => transports_postA hN a)
  have tRel := transports_relabel (crun := crun) hN
  refine transports_congr (transports_append (transports_append (transports_append
    (transports_append tPre tBody) tSinks) tPost) tRel) (fun s => ?_)
  funext w
  simp only [Function.comp]
  rw [fold_pre_eq f s, ← List.foldl_append, fold_post_eq]
  exact (congrArg (fun t => cxPost f t w.rho) (hser .complex (2⁻¹ : ℂ) (cxEdgeOps f) (cxPre f s))).trans
    (hcert.array_corollary (LayerAddr A K D S × Fin rr) f hN.f1 s w)

end Final

end Node

/-- **One internal node of `cCoreProc` computes `C^{⊗(mH·f)}`** (`CxNodeCorrectStmt`): from the edge
interface, `SerialEqFramedStmt 100` and the array corollary of `ComplexNetCert`. -/
theorem cxNode_correct_holds : CxNodeCorrectStmt := by
  intro hcert hser A K D S rr ρ f j0 c hN cdat Child crun childOf hedge e he h z
  subst he
  obtain ⟨hRS, hout⟩ := Node.node_transports hcert hser hN hedge (encodeArr z)
  funext x i
  show runOps crun c (cxNodeOps ρ.val f j0 cdat childOf) (encodeArr z) (encodeAddr x) i =
    (if c.mem (encodeAddr x) then cCoreVal ρ j0 (mH * f) h z x else z x) i
  split_ifs with hx
  · have e1 : runOps crun c (cxNodeOps ρ.val f j0 cdat childOf) (encodeArr z) (encodeAddr x) i =
        roleStateC c ρ f j0 (runOps crun c (cxNodeOps ρ.val f j0 cdat childOf) (encodeArr z))
          (roleIdxC.symm (Model.roleIdx c Wc Wc_pos (encodeAddr x)))
          ((slotEquiv f).symm (groupBits ρ j0 (mH * f) hN.fits x), x, i) := by
      show _ = runOps crun c (cxNodeOps ρ.val f j0 cdat childOf) (encodeArr z)
        (encodeAddr (roleAddrC c ρ f j0
          (roleIdxC (roleIdxC.symm (Model.roleIdx c Wc Wc_pos (encodeAddr x))))
          ((slotEquiv f).symm (groupBits ρ j0 (mH * f) hN.fits x)) x)) i
      rw [Equiv.apply_symm_apply, roleAddrC_self hN x hx]
    rw [e1, hRS, cCoreVal_eq_applyCol hN h z x hx i]
  · rw [hout _ hx]
    show z (decodeAddr (encodeAddr x)) i = z x i
    rw [decodeAddr_encodeAddr]

end CCoreNode

end SubNLogN.Math.Networks
