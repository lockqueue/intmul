/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimShape
import SubNLogN.Machine.AppC.C5NetSimSteps

/-!
# Proposition A.7 network simulation, part 7: the node (`AppC/C5NetSimNode.lean`)

The role lists of the list-level machine schedule simulate the pure-network node. `Sim W S A us`: the role lists `us` are
those of the array `A` (rows of `S` records, roles = row index mod `W`, records as bit lists).
* `roleBlocks_pull`: an address map inside role `w` with a row-local index map `f` changes only role
  `w`'s list, by `permByInv f`;
* `sim_gate`: a gate equal to an XOR list acts on the role lists as `gateApply`;
* `RelOp`: the leaf relation between the pure-network role operations and raw entries; `sim_step`, `sim_list`;
* `node_rel`: at level `k' + 1` on `nodeLayout`, the pure-network node operations (`evOps` over `nodeEvents`,
  children `interchangeProc … k'`) are entrywise related to `rawMain fac` — under the pure-network Proposition A.7 correctness
  (`InterchangeProcCorrectStmt`, an explicit hypothesis, for the children) and the parameter
  hypotheses; `node_sim` is the resulting simulation of the node. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step RoleOp ProcK Elem RowClass)

/-- The role lists `us` (rows of `S` records, `W` roles) are those of the array `A`. -/
def Sim {L : Layout} {wd : ℕ} (W S : ℕ) (A : L.Addr → Rec wd) (us : Fin W → List (List Bool)) :
    Prop :=
  ∀ r : Fin W, us r = (roleBlocks W r.val S (L.enc A)).map ofRec

theorem RowPerm.lt_mul {S : ℕ} {f : ℕ → ℕ} (h : RowPerm S f) (n y : ℕ) (hy : y < n * S) :
    f y < n * S := by
  have hS : 0 < S := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h1 := h.local_eq (y / S) (y % S) (Nat.mod_lt _ hS)
  rw [Nat.div_add_mod'] at h1
  have h2 := h.lt (y % S) (Nat.mod_lt _ hS)
  have h3 : y / S < n := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hy)
  rw [h1]
  calc y / S * S + f (y % S) < y / S * S + S := by omega
    _ = (y / S + 1) * S := by ring
    _ ≤ n * S := Nat.mul_le_mul_right _ h3

theorem roleBlocks_enc_length {β : Type} (L : Layout) (ℓ : Fin L.n) {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (A : L.Addr → β) (r : Fin W) :
    (roleBlocks W r.val (L.place L.n ℓ) (L.enc A)).length =
      L.blockRange 0 ℓ.val * (L.r ℓ / W) * L.place L.n ℓ := by
  rw [roleBlocks_eq_model, L.roleBlocks_enc A ℓ hW hWr r, Model.Layout.enc_length,
    Model.Layout.roleLayout_card]

/-- **Role-local address maps.** -/
theorem roleBlocks_pull {β : Type} [Inhabited β] (L : Layout) (ℓ : Fin L.n) {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (p : L.Addr → L.Addr) (f : ℕ → ℕ) (hpm : PullMatch L p f)
    (hrow : RowPerm (L.place L.n ℓ) f) (w : Fin W) (A : L.Addr → β) (r : Fin W) :
    roleBlocks W r.val (L.place L.n ℓ)
        (L.enc (A ∘ fun x => if ((Model.RowClass.top ℓ).sub W hW w).mem x then p x else x)) =
      if r = w then permByInv f (roleBlocks W w.val (L.place L.n ℓ) (L.enc A))
      else roleBlocks W r.val (L.place L.n ℓ) (L.enc A) := by
  have hg : ∀ y (h : y < L.card),
      (fun y => if y / L.place L.n ℓ % W = w.val then f y else y) y =
        (L.lexEquiv ((fun x => if ((Model.RowClass.top ℓ).sub W hW w).mem x then p x else x)
          (L.lexEquiv.symm ⟨y, h⟩))).val := by
    intro y h
    have hmem := Model.RowClass.top_sub_mem_iff ℓ W hW hWr w (L.lexEquiv.symm ⟨y, h⟩)
    rw [Equiv.apply_symm_apply] at hmem
    by_cases hm : y / L.place L.n ℓ % W = w.val
    · simp only [if_pos hm, if_pos (hmem.2 hm)]
      exact (hpm y h).symm
    · simp only [if_neg hm, if_neg (fun h' => hm (hmem.1 h')), Equiv.apply_symm_apply]
  rw [L.enc_comp A _ _ hg, ← permByInv_eq_model]
  have key := roleBlocks_restrict (L.blockRange 0 ℓ.val * L.r ℓ) (L.place L.n ℓ) W hW
    (Dvd.dvd.mul_left hWr _) (L.enc A) (by rw [Model.Layout.enc_length, L.card_eq_split ℓ])
    f hrow.local_eq hrow.lt w.val r.val w.isLt r.isLt
  rw [key]
  by_cases hrw : r = w
  · subst hrw
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (fun h => hrw (Fin.ext h)), if_neg hrw]

/-- **Gates.** A gate equal to an XOR list acts on the role lists as `gateApply`. -/
theorem sim_gate {L : Layout} {wd : ℕ} (ℓ : Fin L.n) (S : ℕ) (hS : L.place L.n ℓ = S)
    (hWr : Wb ∣ L.r ℓ) (G : (Fin Wb → Rec wd) → Fin Wb → Rec wd) (xs : List (Fin Wb × Fin Wb))
    (hG : ∀ vals idx, G vals idx = scalarGate xs vals idx) (A : L.Addr → Rec wd)
    (us : Fin Wb → List (List Bool)) (hsim : Sim Wb S A us) :
    Sim Wb S (Model.gateRun (Model.RowClass.top ℓ) Wb Wb_pos G A) (gateApply xs us) := by
  subst hS
  have hlen : ∀ r : Fin Wb, (roleBlocks Wb r.val (L.place L.n ℓ) (L.enc A)).length =
      (L.roleLayout ℓ Wb).card := fun r => by
    rw [roleBlocks_eq_model, L.roleBlocks_enc A ℓ Wb_pos hWr r, Model.Layout.enc_length]
  have hus : us = fun r => (List.range (L.roleLayout ℓ Wb).card).map fun y =>
      ofRec ((roleBlocks Wb r.val (L.place L.n ℓ) (L.enc A)).getD y default) := by
    funext r
    rw [hsim r]
    conv_lhs => rw [list_eq_map_range (roleBlocks Wb r.val (L.place L.n ℓ) (L.enc A)) default]
    rw [List.map_map, hlen r]
    rfl
  intro r
  rw [hus, gateApply_range xs _
      (fun y k' => (roleBlocks Wb k'.val (L.place L.n ℓ) (L.enc A)).getD y default),
    roleBlocks_eq_model, L.enc_gateRun A ℓ Wb_pos hWr G r, List.map_map]
  refine List.map_congr_left fun y _ => ?_
  exact congrArg ofRec (hG _ r).symm

/-- The leaf relation between the pure-network role operations and raw entries at a node on field `ℓ`. -/
def RelOp {L : Layout} {wd : ℕ} {Child : Type} (ℓ : Fin L.n) (S : ℕ)
    (crun : Child → RowClass L → (L.Addr → Rec wd) → (L.Addr → Rec wd))
    (sm : StreamOp mH → ℕ → ℕ) (cm : Fin mH → Fin mH → ℕ → ℕ) :
    RoleOp L (Rec wd) Wb Child → RawOp Wb mH → Prop
  | .prim w s, .stream w' op => w = w' ∧ ∃ p : L.Addr → L.Addr,
      (∀ A, s.run A = A ∘ p) ∧ PullMatch L p (sm op) ∧ RowPerm S (sm op)
  | .gate G _, .gate xs => ∀ vals idx, G vals idx = scalarGate xs vals idx
  | .call w ch, .call w' i j => w = w' ∧ ∃ p : L.Addr → L.Addr,
      (∀ A, crun ch ((Model.RowClass.top ℓ).sub Wb Wb_pos w) A =
        A ∘ fun x => if ((Model.RowClass.top ℓ).sub Wb Wb_pos w).mem x then p x else x) ∧
      PullMatch L p (cm i j) ∧ RowPerm S (cm i j)
  | _, _ => False

theorem sim_step {L : Layout} {wd : ℕ} {Child : Type} (ℓ : Fin L.n) (S : ℕ)
    (hS : L.place L.n ℓ = S) (hWr : Wb ∣ L.r ℓ)
    (crun : Child → RowClass L → (L.Addr → Rec wd) → (L.Addr → Rec wd))
    (sm : StreamOp mH → ℕ → ℕ) (cm : Fin mH → Fin mH → ℕ → ℕ)
    (o : RoleOp L (Rec wd) Wb Child) (x : RawOp Wb mH) (hrel : RelOp ℓ S crun sm cm o x)
    (A : L.Addr → Rec wd) (us : Fin Wb → List (List Bool)) (hsim : Sim Wb S A us) :
    Sim Wb S (o.run crun (Model.RowClass.top ℓ) Wb_pos A) (x.run sm cm us) := by
  subst hS
  have hperm : ∀ (w : Fin Wb) (p : L.Addr → L.Addr) (f : ℕ → ℕ), PullMatch L p f →
      RowPerm (L.place L.n ℓ) f →
      Sim Wb (L.place L.n ℓ)
        (A ∘ fun x => if ((Model.RowClass.top ℓ).sub Wb Wb_pos w).mem x then p x else x)
        (Function.update us w (permByInv f (us w))) := by
    intro w p f hpm hrow r
    rw [roleBlocks_pull L ℓ Wb_pos hWr p f hpm hrow w A r]
    by_cases hrw : r = w
    · subst hrw
      rw [Function.update_self, if_pos rfl, hsim r, permByInv_map]
      intro y hy
      rw [roleBlocks_enc_length L ℓ Wb_pos hWr A r] at hy ⊢
      exact hrow.lt_mul _ y hy
    · rw [Function.update_of_ne hrw, if_neg hrw, hsim r]
  have hA : ∀ (c : RowClass L) (s : Step L (Rec wd)) (p : L.Addr → L.Addr),
      (∀ A, s.run A = A ∘ p) →
        Model.Step.runIn c s A = A ∘ fun x => if c.mem x then p x else x := by
    intro c s p hp
    funext x
    simp only [Model.Step.runIn, hp, Function.comp]
    split_ifs <;> rfl
  rcases o with ⟨w, s⟩ | ⟨G, t⟩ | ⟨w, ch⟩ | π <;> rcases x with ⟨w', op⟩ | xs | ⟨w', i, j⟩ <;>
    try exact (hrel : False).elim
  · obtain ⟨rfl, p, hp, hpm, hrow⟩ := hrel
    show Sim Wb _ (Model.Step.runIn _ s A) _
    rw [hA _ s p hp]
    exact hperm _ p (sm op) hpm hrow
  · exact sim_gate ℓ _ rfl hWr G xs hrel A us hsim
  · obtain ⟨rfl, p, hp, hpm, hrow⟩ := hrel
    show Sim Wb _ (crun ch _ A) _
    rw [hp]
    exact hperm _ p (cm i j) hpm hrow

theorem sim_list {L : Layout} {wd : ℕ} {Child : Type} (ℓ : Fin L.n) (S : ℕ)
    (hS : L.place L.n ℓ = S) (hWr : Wb ∣ L.r ℓ)
    (crun : Child → RowClass L → (L.Addr → Rec wd) → (L.Addr → Rec wd))
    (sm : StreamOp mH → ℕ → ℕ) (cm : Fin mH → Fin mH → ℕ → ℕ)
    {os : List (RoleOp L (Rec wd) Wb Child)} {xs : List (RawOp Wb mH)}
    (h : List.Forall₂ (RelOp ℓ S crun sm cm) os xs) :
    ∀ (A : L.Addr → Rec wd) (us : Fin Wb → List (List Bool)), Sim Wb S A us →
      Sim Wb S (os.foldl (fun A o => o.run crun (Model.RowClass.top ℓ) Wb_pos A) A)
        (xs.foldl (fun us x => x.run sm cm us) us) := by
  induction h with
  | nil => exact fun A us hsim => hsim
  | cons hab _ ih =>
    intro A us hsim
    exact ih _ _ (sim_step ℓ S hS hWr crun sm cm _ _ hab A us hsim)

/-! ## The node of `interchangeProc (k' + 1)` on `nodeLayout` -/

section Node

variable (q k' N0 R N1 G B : ℕ)

/-- The child interchange maps at level `k' + 1` (the level-`k'` `swapMap`, written out). -/
def childMap (i j : Fin mH) : ℕ → ℕ :=
  swapFieldsInv (q ^ mH ^ k') (q ^ ((mH - 1 - i) * mH ^ k') * G * q ^ (j * mH ^ k')) (q ^ mH ^ k')
    (q ^ ((mH - 1 - j) * mH ^ k') * B)

theorem childMap_eq (i j : Fin mH) :
    swapMap q mH (k' + 1 - 1) (cG q mH (k' + 1) G i j) (cB q mH (k' + 1) B j) =
      childMap q k' G B i j := by
  simp only [swapMap, cG, cB, Nat.add_sub_cancel, childMap]

/-- The pull map of the child interchange of `H_i` and `D_j` (`Model.Step.swapBlocks`). -/
def childPull (i j : Fin mH) (x : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr) :
    (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr :=
  (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockSet (4 + mH ^ (k' + 1) + ↑j * mH ^ k')
    (4 + mH ^ (k' + 1) + ↑j * mH ^ k' + mH ^ k')
    ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockSet (3 + ↑i * mH ^ k')
      (3 + ↑i * mH ^ k' + mH ^ k') x
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal (4 + mH ^ (k' + 1) + ↑j * mH ^ k')
        (4 + mH ^ (k' + 1) + ↑j * mH ^ k' + mH ^ k') x))
    ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal (3 + ↑i * mH ^ k')
      (3 + ↑i * mH ^ k' + mH ^ k') x)

variable {q k' N0 R N1 G B}

theorem child_hyps (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (hq : q.Prime) (hq2 : q ≠ 2)
    (hint : ∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j))
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    (hR : Wb ^ (k' + 1) ∣ R) (i j : Fin mH) (w : Fin Wb) :
    InterchangeHyps (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) q fac k' (3 + ↑i * mH ^ k')
      (4 + mH ^ (k' + 1) + ↑j * mH ^ k')
      ((Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)).sub Wb Wb_pos w) := by
  have he := he_level k'
  have hi1 : ↑i * mH ^ k' + mH ^ k' ≤ mH * mH ^ k' := by
    have h : (↑i + 1) * mH ^ k' ≤ mH * mH ^ k' := Nat.mul_le_mul_right _ i.isLt
    rwa [Nat.add_mul, Nat.one_mul] at h
  have hj1 : ↑j * mH ^ k' + mH ^ k' ≤ mH * mH ^ k' := by
    have h : (↑j + 1) * mH ^ k' ≤ mH * mH ^ k' := Nat.mul_le_mul_right _ j.isLt
    rwa [Nat.add_mul, Nat.one_mul] at h
  refine ⟨hq, hq2, hint, hfac, fun i' hi' => ?_, by omega, ?_, ?_, ?_⟩
  · show nodeR q (mH ^ (k' + 1)) N0 R N1 G B i'.val = q
    exact nodeR_q (by omega)
  · show 4 + mH ^ (k' + 1) + ↑j * mH ^ k' + mH ^ k' ≤ 5 + 2 * mH ^ (k' + 1)
    omega
  · show 1 < 3 + ↑i * mH ^ k'
    omega
  · show 1 * Wb * Wb ^ k' ∣ (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).r
      (rowF q (mH ^ (k' + 1)) N0 R N1 G B)
    rw [nl_r_row, show 1 * Wb * Wb ^ k' = Wb ^ (k' + 1) by ring]
    exact hR

theorem row_dvd (hR : Wb ^ (k' + 1) ∣ R) :
    Wb ∣ (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).r (rowF q (mH ^ (k' + 1)) N0 R N1 G B) := by
  rw [nl_r_row]
  exact (dvd_pow_self Wb (Nat.succ_ne_zero k')).trans hR

/-- **The node's operations are entrywise related to the raw schedule** (children by pure-network Proposition A.7
correctness at depth `k'`). -/
theorem node_rel {wd : ℕ} (hIC : InterchangeProcCorrectStmt) (hcert : BitNetCert)
    (hshear : ShearFacts) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (hq : q.Prime)
    (hq2 : q ≠ 2) (hint : ∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j))
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    (hG : 0 < G) (hB : 0 < B) (hR : Wb ^ (k' + 1) ∣ R) :
    List.Forall₂ (RelOp (wd := wd) (rowF q (mH ^ (k' + 1)) N0 R N1 G B)
        (rowSize q mH (k' + 1) N1 G B) (ProcK.run k') (fun op => streamMap q mH op (k' + 1) N1 G B)
        (childMap q k' G B))
      ((nodeEvents .bit 100).flatMap (InterchangeCorrect.evOps
        (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd) (q ^ mH ^ k') 3
        (4 + mH ^ (k' + 1)) (mH ^ k') fac
        (fun i j => interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd)
          q fac k' (3 + i.val * mH ^ k') (4 + mH ^ (k' + 1) + j.val * mH ^ k'))))
      (rawMain fac) := by
  have hq0 : 0 < q := hq.pos
  have hq1 : 1 ≤ q := hq.one_lt.le
  refine forall₂_main _ _ _ _ _ fac _ (fun w F => forall₂_shear _ _ _ _ _ _ F _
    (fun E => forall₂_lower _ _ _ _ _ .D E
      (fun i => ⟨rfl, _, fun _ => rfl, pm_lowUnit q k' N0 R N1 G B hq0 .D E i,
        streamMap_rowPerm q k' N1 G B hq1 _⟩)
      (fun i => ⟨rfl, _, fun _ => rfl, pm_lowShift q k' N0 R N1 G B hq0 .D E i,
        streamMap_rowPerm q k' N1 G B hq1 _⟩))
    (fun E => forall₂_lower _ _ _ _ _ .H E
      (fun i => ⟨rfl, _, fun _ => rfl, pm_lowUnit q k' N0 R N1 G B hq0 .H E i,
        streamMap_rowPerm q k' N1 G B hq1 _⟩)
      (fun i => ⟨rfl, _, fun _ => rfl, pm_lowShift q k' N0 R N1 G B hq0 .H E i,
        streamMap_rowPerm q k' N1 G B hq1 _⟩))
    (fun p => ⟨rfl, _, fun _ => rfl, pm_hdPlus q k' N0 R N1 G B hq0 p.1 p.2,
      streamMap_rowPerm q k' N1 G B hq1 _⟩)
    (fun p => ⟨rfl, childPull q k' N0 R N1 G B p.1 p.2, fun A => ?_,
      pm_swap q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') hq0 hG hB p.1 p.2 p.1.isLt
        p.2.isLt,
      swap_rowPerm q (mH ^ (k' + 1)) N1 G B mH (mH ^ k') (he_level k') p.1 p.2 p.1.isLt
        p.2.isLt⟩)
    (fun p => ⟨rfl, _, fun _ => rfl, pm_negD q k' N0 R N1 G B hq0 p.2,
      streamMap_rowPerm q k' N1 G B hq1 _⟩))
    (fun j ι r vals idx => gate_eq j ι r vals idx)
  beta_reduce
  rw [hIC hcert hshear _ (Rec wd) q fac k' _ _ _
    (child_hyps fac hq hq2 hint hfac hR p.1 p.2 (roleIdxB w)) A]
  funext x
  simp only [Model.Step.runIn, Model.Step.run, Function.comp, childPull]
  split_ifs <;> rfl

/-- **Node simulation**: the raw machine schedule on the role lists simulates the pure-network node operations
(minus the final relabelling) at level `k' + 1`. -/
theorem node_sim {wd : ℕ} (hIC : InterchangeProcCorrectStmt) (hcert : BitNetCert)
    (hshear : ShearFacts) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (hq : q.Prime)
    (hq2 : q ≠ 2) (hint : ∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j))
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    (hG : 0 < G) (hB : 0 < B) (hR : Wb ^ (k' + 1) ∣ R)
    (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec wd)
    (us : Fin Wb → List (List Bool)) (hsim : Sim Wb (rowSize q mH (k' + 1) N1 G B) A us) :
    Sim Wb (rowSize q mH (k' + 1) N1 G B)
      (((nodeEvents .bit 100).flatMap (InterchangeCorrect.evOps
        (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd) (q ^ mH ^ k') 3
        (4 + mH ^ (k' + 1)) (mH ^ k') fac
        (fun i j => interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd)
          q fac k' (3 + i.val * mH ^ k') (4 + mH ^ (k' + 1) + j.val * mH ^ k')))).foldl
        (fun A o => o.run (ProcK.run k') (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B))
          Wb_pos A) A)
      ((rawMain fac).foldl (fun us x => x.run (fun op => streamMap q mH op (k' + 1) N1 G B)
        (childMap q k' G B) us) us) :=
  sim_list _ (rowSize q mH (k' + 1) N1 G B) (nl_place q (mH ^ (k' + 1)) N0 R N1 G B) (row_dvd hR)
    _ _ _ (node_rel hIC hcert hshear fac hq hq2 hint hfac hG hB hR) A us hsim

end Node

end SubNLogN.Machine.C5.NetAux
