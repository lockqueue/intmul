/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs
import SubNLogN.Math.Networks.Proofs.CCoreEdge

/-!
# C-core node code (I): value-level role operations on compact role arrays (`CCore/NodeCodeBase.lean`)

Transport of the value-level node semantics (`Model.RoleOp.run` of `cxNodeOps`, run on the whole array of a
call, class `topC t`) to the skeleton's value semantics (`mopVal` of `nodeCode`, on the `W` compact
role arrays `restrictRole t u`). Role `u` of the skeleton is row class `u` of the cyclic split
`a = a'·W + u` (`roleEmb`); the network role indices `Fin W_c` are transported by `toN = finCongr`
(`W_c = W`, `cardRole_holds`), never unfolding `W_c`.

* `Φ t Arr u = restrictRole t u (decodeArr Arr)`: the role arrays of a full array;
* `Sim crun ops mops`: `Φ ∘ runOps ops = mopsVal mops ∘ Φ`; closed under `++`, `map`, `flatMap`;
* membership, `aligned`, `roleIdx` of `encodeAddr (roleEmb t u x)` in the top class;
* the generic primitive case `sim_prim`, the scalar row `sim_gate`, the final relabel
  (`relabel_Φ`: class `u` reads physical role `collectPerm u`), child calls `sim_call`.

Implementation note: terms of types `Fin W_c` and `Fin W` are never compared by unification at
default transparency (that would unfold `W_c = Fintype.card (Role .complex 100)`); all such steps
go through `rw`/`simp only` with the transport lemmas `toN_val`, `roleIdxN_eq`, `roleIdxN_symm_eq`.

Helpers are in `SubNLogN.Machine.CCore.NodeCodeAux`.
-/

namespace SubNLogN.Machine.CCore

namespace NodeCodeAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks Model

/-- `W_c = W` (`cardRole_holds`). -/
theorem Wc_eq_Wn : Wc = Wn := (cardRole_holds 100).2

theorem Wn_pos : 0 < Wn := lt_of_lt_of_eq Wc_pos Wc_eq_Wn

/-- Complex-network role indices `Fin W_c` as skeleton role indices `Fin W`. -/
noncomputable def toN : Fin Wc ≃ Fin Wn := finCongr Wc_eq_Wn

theorem toN_val (k : Fin Wc) : (toN k).val = k.val := finCongr_apply_coe Wc_eq_Wn k

theorem toN_symm_val (u : Fin Wn) : (toN.symm u).val = u.val := by
  unfold toN
  rw [finCongr_symm]
  exact finCongr_apply_coe _ _

theorem roleIdxN_eq (w : Role .complex 100) : roleIdxN w = toN (roleIdxC w) := by
  unfold roleIdxN toN
  rw [Equiv.trans_apply]

theorem roleIdxN_symm_eq (u : Fin Wn) : roleIdxN.symm u = roleIdxC.symm (toN.symm u) := by
  unfold roleIdxN toN
  rw [Equiv.symm_trans_apply]

/-- The full layout of a call. -/
abbrev FL (t : CCoreRT) : Model.Layout := layerLayout t.A t.K t.D t.S

/-- The compact (role) layout of a call. -/
abbrev CLy (t : CCoreRT) : Model.Layout := layerLayout (t.A / Wn) t.K t.D t.S

/-- The row field (field `0`). -/
def row0 (t : CCoreRT) : Fin (FL t).n := ⟨0, by show 0 < t.D * t.K + 2; omega⟩

/-- The whole array as a class. -/
def topC (t : CCoreRT) : RowClass (FL t) := RowClass.top (row0 t)

/-- The role arrays of a full array. -/
noncomputable def Φ (t : CCoreRT) (Arr : (FL t).Addr → (Fin t.r → ℂ)) :
    Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r :=
  fun u => restrictRole t u (decodeArr Arr)

theorem Φ_apply (t : CCoreRT) (Arr : (FL t).Addr → (Fin t.r → ℂ)) (u : Fin Wn)
    (x : LayerAddr (t.A / Wn) t.K t.D t.S) : Φ t Arr u x = Arr (encodeAddr (roleEmb t u x)) := rfl

/-- The type of child runners at a node of the call `t`. -/
abbrev Crun (t : CCoreRT) : Type :=
  ℕ → RowClass (FL t) → ((FL t).Addr → (Fin t.r → ℂ)) → ((FL t).Addr → (Fin t.r → ℂ))

/-- `ops` (value-level operations run at the node in the whole array) act on the role arrays as `mops`. -/
def Sim {t : CCoreRT} (crun : Crun t) (ops : List (RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ))
    (mops : List MOp) : Prop :=
  ∀ Arr, Φ t (CCoreNode.runOps crun (topC t) ops Arr) = mopsVal t mops (Φ t Arr)

section SimAlg

variable {t : CCoreRT} {crun : Crun t}

theorem sim_nil : Sim crun [] [] := fun _ => rfl

theorem mopsVal_append (m₁ m₂ : List MOp)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    mopsVal t (m₁ ++ m₂) w = mopsVal t m₂ (mopsVal t m₁ w) := List.foldl_append ..

theorem sim_append {o₁ o₂ : List (RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ)} {m₁ m₂ : List MOp}
    (h₁ : Sim crun o₁ m₁) (h₂ : Sim crun o₂ m₂) : Sim crun (o₁ ++ o₂) (m₁ ++ m₂) := by
  intro Arr
  have e1 : CCoreNode.runOps crun (topC t) (o₁ ++ o₂) Arr =
      CCoreNode.runOps crun (topC t) o₂ (CCoreNode.runOps crun (topC t) o₁ Arr) :=
    List.foldl_append ..
  rw [e1, h₂, h₁, mopsVal_append]

theorem sim_flatMap {α : Type*} (l : List α) (g : α → List (RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ))
    (g' : α → List MOp) (h : ∀ a ∈ l, Sim crun (g a) (g' a)) :
    Sim crun (l.flatMap g) (l.flatMap g') := by
  induction l with
  | nil => exact sim_nil
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact sim_append (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem sim_flatMap_map {α : Type*} (l : List α) (g : α → List (RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ))
    (g' : α → MOp) (h : ∀ a ∈ l, Sim crun (g a) [g' a]) :
    Sim crun (l.flatMap g) (l.map g') := by
  rw [← List.flatMap_pure_eq_map]
  exact sim_flatMap l g _ h

theorem sim_map {α : Type*} (l : List α) (g : α → RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ)
    (g' : α → MOp) (h : ∀ a ∈ l, Sim crun [g a] [g' a]) :
    Sim crun (l.map g) (l.map g') := by
  rw [← List.flatMap_pure_eq_map, ← List.flatMap_pure_eq_map]
  exact sim_flatMap l _ _ h

theorem sim_cons {o : RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ} {os : List (RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ)}
    {m : MOp} {ms : List MOp} (h₁ : Sim crun [o] [m]) (h₂ : Sim crun os ms) :
    Sim crun (o :: os) (m :: ms) :=
  sim_append (o₁ := [o]) (m₁ := [m]) h₁ h₂

end SimAlg

/-! ## Row classes of the top class, for a general number of roles `W`

Stated for a variable `W` so that instantiating at `W_c` never asks the kernel to compute with
`W_c`. -/

section Top

variable {L : Layout} (row : Fin L.n) (W : ℕ) (hW : 0 < W)

theorem top_sub_mem_iff (k : Fin W) (a : L.Addr) :
    ((RowClass.top row).sub W hW k).mem a ↔ (a row).val % W = k.val := by
  rw [CCoreNode.sub_mem_iff]
  show (a row).val % (1 * W) = 0 + 1 * k.val ↔ _
  rw [Nat.one_mul, Nat.zero_add, Nat.one_mul]

theorem top_roleIdx_val (a : L.Addr) :
    (roleIdx (RowClass.top row) W hW a).val = (a row).val % W := by
  show ((a row).val / 1) % W = _
  rw [Nat.div_one]

theorem top_aligned (a : L.Addr) (k' : ℕ) :
    aligned (RowClass.top row) W a k' = withRow row a (k' + W * ((a row).val / W)) := by
  show withRow row a (0 + 1 * (k' + W * (((a row).val / 1) / W))) = _
  rw [Nat.zero_add, Nat.one_mul, Nat.div_one]

theorem top_mem (a : L.Addr) : (RowClass.top row).mem a := Nat.mod_one _

end Top

theorem mod_aux {W a v : ℕ} (hv : v < W) : (a * W + v) % W = v := Nat.mul_add_mod_of_lt hv

theorem div_aux {W a v : ℕ} (hv : v < W) : (a * W + v) / W = a := by
  have hW : 0 < W := by omega
  rw [Nat.mul_comm, Nat.mul_add_div hW, Nat.div_eq_of_lt hv, Nat.add_zero]

theorem lt_aux {A W a v : ℕ} (ha : a < A / W) (hv : v < W) : a * W + v < A := by
  have h3 : A / W * W ≤ A := Nat.div_mul_le_self A W
  have h4 : (a + 1) * W ≤ A / W * W := Nat.mul_le_mul_right _ ha
  have h5 : (a + 1) * W = a * W + W := Nat.succ_mul a W
  omega

/-! ## Addresses of role arrays in the top class -/

section Addr

variable (t : CCoreRT)

theorem topC_eq : topC t = RowClass.top (row0 t) := rfl

theorem roleEmb_fst_val (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    (roleEmb t u x).1.val = x.1.val * Wn + u.val := rfl

theorem roleEmb_snd (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    (roleEmb t u x).2 = x.2 := rfl

theorem row_roleEmb (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    (encodeAddr (roleEmb t u x) (row0 t)).val = x.1.val * Wn + u.val :=
  CCoreEdgeAux.encode_zero _ _ rfl

theorem mod_Wc_roleEmb (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    (x.1.val * Wn + u.val) % Wc = u.val := by
  rw [show Wc = Wn from Wc_eq_Wn]
  exact mod_aux u.isLt

theorem div_Wc_roleEmb (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    (x.1.val * Wn + u.val) / Wc = x.1.val := by
  rw [show Wc = Wn from Wc_eq_Wn]
  exact div_aux u.isLt

/-- Role class `k` of the top class contains exactly the addresses of role array `toN k`. -/
theorem sub_mem_roleEmb (k : Fin Wc) (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    ((topC t).sub Wc Wc_pos k).mem (encodeAddr (roleEmb t u x)) ↔ toN k = u := by
  rw [topC_eq, top_sub_mem_iff, row_roleEmb, mod_Wc_roleEmb]
  constructor
  · intro h
    exact Fin.ext (by rw [toN_val]; exact h.symm)
  · intro h
    rw [← h, toN_val]

theorem topC_mem (a : (FL t).Addr) : (topC t).mem a := top_mem (row0 t) a

theorem roleIdx_roleEmb (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    roleIdx (topC t) Wc Wc_pos (encodeAddr (roleEmb t u x)) = toN.symm u := by
  apply Fin.ext
  rw [topC_eq, top_roleIdx_val, row_roleEmb, mod_Wc_roleEmb, toN_symm_val]

/-- Two encoded addresses with the same non-row part agree on every non-row field, across
layouts that differ only in the row range. -/
theorem encodeAddr_val_congr {A A' K D S : ℕ} (x : LayerAddr A K D S) (x' : LayerAddr A' K D S)
    (h : x.2 = x'.2) (i : ℕ) (hi : i < D * K + 2) (h0 : i ≠ 0) :
    (encodeAddr x ⟨i, hi⟩).val = (encodeAddr x' ⟨i, hi⟩).val := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨x1', x2'⟩ := x'
  simp only at h
  subst h
  unfold encodeAddr
  simp only [dif_neg h0]
  split_ifs <;> rfl

theorem fv_encode_congr {A A' K D S : ℕ} (x : LayerAddr A K D S) (x' : LayerAddr A' K D S)
    (h : x.2 = x'.2) (s : ℕ) (hs : s ≠ 0) :
    CCoreEdgeAux.fv (encodeAddr x) s = CCoreEdgeAux.fv (encodeAddr x') s := by
  unfold CCoreEdgeAux.fv
  by_cases hn : s < D * K + 2
  · rw [dif_pos (show s < (layerLayout A K D S).n from hn),
      dif_pos (show s < (layerLayout A' K D S).n from hn)]
    exact encodeAddr_val_congr x x' h s hn hs
  · rw [dif_neg (show ¬ s < (layerLayout A K D S).n from hn),
      dif_neg (show ¬ s < (layerLayout A' K D S).n from hn)]

/-- `slotBit` does not see the row field. -/
theorem slotBit_roleEmb (u : Fin Wn) (x : LayerAddr (t.A / Wn) t.K t.D t.S) (K' ρ f j0 tt c : ℕ) :
    slotBit (A := t.A) (D := t.D) (S := t.S) K' ρ f j0 tt c (encodeAddr (roleEmb t u x)) =
      slotBit (A := t.A / Wn) (D := t.D) (S := t.S) K' ρ f j0 tt c (encodeAddr x) := by
  unfold slotBit
  rw [CCoreEdgeAux.blockVal_single, CCoreEdgeAux.blockVal_single]
  exact fv_encode_congr (roleEmb t u x) x rfl (selField K' ρ (j0 + tt * f + c))
    (by unfold selField; omega)

/-- `aligned` in the top class moves a role address to another role, same position. -/
theorem aligned_roleEmb (u : Fin Wn) (k' : Fin Wc) (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    aligned (topC t) Wc (encodeAddr (roleEmb t u x)) k'.val = encodeAddr (roleEmb t (toN k') x) := by
  rw [topC_eq, top_aligned, row_roleEmb, div_Wc_roleEmb]
  have hv : k'.val + Wc * x.1.val = x.1.val * Wn + (toN k').val := by
    rw [toN_val]
    generalize k'.val = m
    rw [show Wc = Wn from Wc_eq_Wn, Nat.add_comm m, Nat.mul_comm Wn]
  have hlt : x.1.val * Wn + (toN k').val < (FL t).r (row0 t) :=
    lt_aux x.1.isLt (toN k').isLt
  rw [hv]
  unfold withRow
  rw [dif_pos hlt]
  funext i
  by_cases hi : i = row0 t
  · subst hi
    rw [Function.update_self]
    apply Fin.ext
    exact (row_roleEmb t (toN k') x).symm
  · rw [Function.update_of_ne hi]
    apply Fin.ext
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    exact encodeAddr_val_congr (roleEmb t u x) (roleEmb t (toN k') x) rfl i.val i.isLt hi0

end Addr

/-! ## Unfolding lemmas (stated generically, used by `rw`)

The kernel check of a `show` that unfolds `Φ`/`runOps`/`mopsVal` at a concrete call hits deep
recursion; rewriting with these generic `rfl` lemmas keeps every kernel check syntactic. -/

section Unfold

theorem runOps_single {L : Layout} {β Ch : Type}
    (crun : Ch → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L)
    (o : RoleOp L β Wc Ch) (Arr : L.Addr → β) :
    CCoreNode.runOps crun c [o] Arr = o.run crun c Wc_pos Arr := rfl

theorem roleOp_run_prim {L : Layout} {β Ch : Type} {W : ℕ}
    (crun : Ch → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (hW : 0 < W)
    (k : Fin W) (s : Step L β) (A : L.Addr → β) :
    (RoleOp.prim k s : RoleOp L β W Ch).run crun c hW A = s.runIn (c.sub W hW k) A := rfl

theorem roleOp_run_gate {L : Layout} {β Ch : Type} {W : ℕ}
    (crun : Ch → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (hW : 0 < W)
    (G : (Fin W → β) → (Fin W → β)) (tch : Finset (Fin W)) (A : L.Addr → β) :
    (RoleOp.gate G tch : RoleOp L β W Ch).run crun c hW A = gateRun c W hW G A := rfl

theorem roleOp_run_relabel {L : Layout} {β Ch : Type} {W : ℕ}
    (crun : Ch → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (hW : 0 < W)
    (π : Equiv.Perm (Fin W)) (A : L.Addr → β) :
    (RoleOp.relabel π : RoleOp L β W Ch).run crun c hW A = relabelRun c W hW π A := rfl

theorem roleOp_run_call {L : Layout} {β Ch : Type} {W : ℕ}
    (crun : Ch → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (hW : 0 < W)
    (k : Fin W) (ch : Ch) (A : L.Addr → β) :
    (RoleOp.call k ch : RoleOp L β W Ch).run crun c hW A = crun ch (c.sub W hW k) A := rfl

theorem runIn_apply {L : Layout} {β : Type} (c : RowClass L) (s : Step L β) (A : L.Addr → β)
    (a : L.Addr) : s.runIn c A a = if c.mem a then s.run A a else A a := rfl

theorem gateRun_apply {L : Layout} {β : Type} (c : RowClass L) (W : ℕ) (hW : 0 < W)
    (G : (Fin W → β) → (Fin W → β)) (A : L.Addr → β) (a : L.Addr) :
    gateRun c W hW G A a =
      if c.mem a then G (fun k' => A (aligned c W a k')) (roleIdx c W hW a) else A a := rfl

theorem relabelRun_apply {L : Layout} {β : Type} (c : RowClass L) (W : ℕ) (hW : 0 < W)
    (π : Equiv.Perm (Fin W)) (A : L.Addr → β) (a : L.Addr) :
    relabelRun c W hW π A a =
      if c.mem a then A (aligned c W a (π.symm (roleIdx c W hW a))) else A a := rfl

theorem mopsVal_single (t : CCoreRT) (o : MOp)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    mopsVal t [o] w = mopVal t o w := rfl

theorem mopVal_phase (t : CCoreRT) (u : Fin Wn) (κ : PhaseKind)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    mopVal t (.phase u κ) w = Function.update w u (runSteps [phaseStep t κ] (w u)) := rfl

theorem mopVal_rowAdd (t : CCoreRT) (u : Fin Wn) (p₁ p₂ : Fin mn)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    mopVal t (.rowAdd u p₁ p₂) w = Function.update w u (runSteps (rowAddSteps t p₁ p₂) (w u)) :=
  rfl

theorem mopVal_child (t : CCoreRT) (u : Fin Wn) (a : Fin mn)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    mopVal t (.child u a) w = Function.update w u (childVal t a (w u)) := rfl

theorem mopVal_gate (t : CCoreRT) (j : Stage) (ι : Fix 100) (r : Fin 8)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    mopVal t (.gate j ι r) w = gateVal j ι r w := rfl

theorem runSteps_apply {A K D S r : ℕ} (ss : List (Step (layerLayout A K D S) (Fin r → ℂ)))
    (w : RArr (LayerAddr A K D S) r) (x : LayerAddr A K D S) :
    runSteps ss w x = ss.foldl (fun B s => s.run B) (encodeArr w) (encodeAddr x) := rfl

theorem runSteps_single {A K D S r : ℕ} (s : Step (layerLayout A K D S) (Fin r → ℂ))
    (w : RArr (LayerAddr A K D S) r) (x : LayerAddr A K D S) :
    runSteps [s] w x = s.run (encodeArr w) (encodeAddr x) := rfl

theorem recMap_run {L : Layout} {β : Type} (g : β → β) (B : L.Addr → β) (a : L.Addr) :
    (Step.recMap g).run B a = g (B a) := rfl

theorem addrMap_run {L : Layout} {β : Type} (g : L.Addr → β → β) (B : L.Addr → β) (a : L.Addr) :
    (Step.addrMap g).run B a = g a (B a) := rfl

end Unfold

/-! ## Primitive steps, the scalar row, the relabel -/

section Ops

variable {t : CCoreRT} {crun : Crun t}

/-- A T2 primitive on role `k` whose step agrees with the phase step `κ` through `roleEmb`. -/
theorem sim_prim (k : Fin Wc) (s : Step (FL t) (Fin t.r → ℂ)) (κ : PhaseKind)
    (hs : ∀ (Arr : (FL t).Addr → (Fin t.r → ℂ)) (x : LayerAddr (t.A / Wn) t.K t.D t.S),
      s.run Arr (encodeAddr (roleEmb t (toN k) x)) =
        (phaseStep t κ).run (encodeArr (Φ t Arr (toN k))) (encodeAddr x)) :
    Sim crun [RoleOp.prim k s] [MOp.phase (toN k) κ] := by
  intro Arr
  funext u x
  rw [Φ_apply, runOps_single, roleOp_run_prim, runIn_apply, mopsVal_single, mopVal_phase]
  by_cases hu : u = toN k
  · subst hu
    rw [if_pos ((sub_mem_roleEmb t k _ x).mpr rfl), Function.update_self, hs, runSteps_single]
  · rw [if_neg (fun h => hu ((sub_mem_roleEmb t k u x).mp h).symm), Function.update_of_ne hu,
      Φ_apply]

/-- The scalar row of T2 (`gateOpC`) is the skeleton's `gateVal` on the role arrays. -/
theorem sim_gate (j : Stage) (ι : Fix 100) (r : Fin 8) :
    Sim crun [gateOpC j ι r] [MOp.gate j ι r] := by
  intro Arr
  funext u x
  rw [Φ_apply, runOps_single, mopsVal_single, mopVal_gate]
  unfold gateOpC
  rw [roleOp_run_gate, gateRun_apply, if_pos (topC_mem t _), roleIdx_roleEmb]
  simp only [aligned_roleEmb t, gateVal, gateFn, roleIdxN_eq, roleIdxN_symm_eq, Φ_apply]

theorem toN_rhoPermC_symm (u : Fin Wn) : toN (rhoPermC.symm (toN.symm u)) = collectPerm u := by
  unfold collectPerm rhoPermC
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, roleIdxN_eq, roleIdxN_symm_eq]

/-- The final relabel of T2 (`rhoPermC`): class `u` reads physical role `collectPerm u`. -/
theorem relabel_Φ (Arr : (FL t).Addr → (Fin t.r → ℂ)) (u : Fin Wn) :
    Φ t (CCoreNode.runOps crun (topC t) [RoleOp.relabel rhoPermC] Arr) u =
      Φ t Arr (collectPerm u) := by
  funext x
  rw [Φ_apply, runOps_single, roleOp_run_relabel, relabelRun_apply, if_pos (topC_mem t _),
    roleIdx_roleEmb, aligned_roleEmb t, toN_rhoPermC_symm, Φ_apply]

theorem sim_apply {ops : List (RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ)} {mops : List MOp}
    (h : Sim crun ops mops) (Arr : (FL t).Addr → (Fin t.r → ℂ)) (u : Fin Wn) :
    Φ t (CCoreNode.runOps crun (topC t) ops Arr) u = mopsVal t mops (Φ t Arr) u :=
  congrFun (h Arr) u

theorem Φ_runOps_relabel (ops : List (RoleOp (FL t) (Fin t.r → ℂ) Wc ℕ))
    (Arr : (FL t).Addr → (Fin t.r → ℂ)) (u : Fin Wn) :
    Φ t (CCoreNode.runOps crun (topC t) (ops ++ [RoleOp.relabel rhoPermC]) Arr) u =
      Φ t (CCoreNode.runOps crun (topC t) ops Arr) (collectPerm u) := by
  have e : CCoreNode.runOps crun (topC t) (ops ++ [RoleOp.relabel rhoPermC]) Arr =
      CCoreNode.runOps crun (topC t) [RoleOp.relabel rhoPermC]
        (CCoreNode.runOps crun (topC t) ops Arr) := List.foldl_append ..
  rw [e, relabel_Φ]

theorem encodeArr_encodeAddr {A K D S r : ℕ} (z : RArr (LayerAddr A K D S) r)
    (x : LayerAddr A K D S) : encodeArr z (encodeAddr x) = z x := by
  unfold encodeArr
  rw [CCoreNode.decodeAddr_encodeAddr]

end Ops

/-! ## Child calls -/

/-- **The child property of a child runner** (proved for the ideal runner `crunI` in
`CCore/MathM1*.lean`): a call on slot `sl` in role class `k` of the top class applies `childVal`
(`cCoreVal` on the slot) to role array `toN k` and changes no other role array. -/
def IdealCrun (t : CCoreRT) (crun : Crun t) : Prop :=
  ∀ (sl : ℕ) (hsl : sl < mn) (k : Fin Wc) (Arr : (FL t).Addr → (Fin t.r → ℂ)) (u : Fin Wn),
    Φ t (crun sl ((topC t).sub Wc Wc_pos k) Arr) u =
      if toN k = u then childVal t ⟨sl, hsl⟩ (Φ t Arr u) else Φ t Arr u

theorem sim_call {t : CCoreRT} {crun : Crun t} (hcrun : IdealCrun t crun) (k : Fin Wc) (sl : ℕ)
    (hsl : sl < mn) : Sim crun [RoleOp.call k sl] [MOp.child (toN k) ⟨sl, hsl⟩] := by
  intro Arr
  funext u
  rw [runOps_single, roleOp_run_call, mopsVal_single, mopVal_child, hcrun sl hsl k Arr u]
  by_cases hu : toN k = u
  · subst hu
    rw [if_pos rfl, Function.update_self]
  · rw [if_neg hu, Function.update_of_ne (Ne.symm hu)]

end NodeCodeAux

end SubNLogN.Machine.CCore
