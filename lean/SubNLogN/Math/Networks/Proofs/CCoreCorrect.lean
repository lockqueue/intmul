import SubNLogN.Math.Networks.Proofs.CCoreRole
import SubNLogN.Math.Networks.Proofs.CDon
import SubNLogN.Math.Networks.Proofs.Serial
import SubNLogN.Math.Networks.Proofs.CCoreNode
import SubNLogN.Math.Networks.Proofs.CCoreEdge

/-!
# Lemma A.10 (`lem:transfer-phase`) exactness (`CCoreProcCorrectStmt`): recursion and assembly

Statement in `SubNLogN/Math/Networks/AppCCore.lean`; paper Lemma A.10 (`lem:transfer-phase`),
Appendix A.5 (`sec:transfer-frames`). Helpers live in `SubNLogN.Math.Networks.CCoreAux`.

## Plan
Induction on the depth `k` of `cCoreProc … k j0`, for all `j0` and all classes `c` satisfying
`CCoreHyps` (row field `0`, `μ · W_c^k ∣ A`), in the decoded form of the contract.
* **Leaves** (`k = 0`, and `k + 1 < kLeaf`): a list of individual kernels `dgate` on the selected
  fields of the chunks `j0, …, j0+e−1`. On decoded arrays one `digitGate` with `cGate` is
  `gateR` (`a·z(x) + b·z(x with the selected bit of chunk j flipped)` on the addresses of `c`):
  the flipped address is `Function.update (encodeAddr x) i v` (`update_encodeAddr_flip`). Along
  the fibres `b ↦ setSelBits ρ x b` (closed under the class since the row field is `0`),
  `gateR` is `CDon {j}` (`cdon_single`), the kernels compose by `cdon_union` (`cdonR_comp`), and
  `CDon` on the group `grpSet j0 e` is `cCoreVal` (reindexing `cdon_grp_eq`).
* **Internal nodes** (`k + 1 ≥ kLeaf`): the node theorem of `CCoreNode.lean` (`CCoreRole.lean`), whose
  child hypothesis `ChildSpecC` is the induction hypothesis at the role classes `c.sub W_c k'`
  and whose edge hypothesis `EdgeRoleSpec` is the edge theorem of `CCoreEdge.lean`.
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh

namespace CCoreAux

/-! ## Selected bits of layer addresses -/

section Sel

variable {A K D S : ℕ}

/-- All selected bits `ρ` of an address. -/
def sel (ρ : Fin K) (x : LayerAddr A K D S) : Fin D → Bool := fun j => x.2.1 j ρ

theorem setSelBits_sel_self (ρ : Fin K) (x : LayerAddr A K D S) : setSelBits ρ x (sel ρ x) = x := by
  rcases x with ⟨a, c, s⟩
  simp [setSelBits, sel]

theorem sel_setSelBits (ρ : Fin K) (x : LayerAddr A K D S) (b : Fin D → Bool) :
    sel ρ (setSelBits ρ x b) = b := by
  funext j
  simp [sel, setSelBits]

theorem setSelBits_setSelBits (ρ : Fin K) (x : LayerAddr A K D S) (b b' : Fin D → Bool) :
    setSelBits ρ (setSelBits ρ x b) b' = setSelBits ρ x b' := by
  simp [setSelBits]

/-- `x` with bit `ρ` of chunk `j` negated. -/
def flipSel (ρ : Fin K) (j : Fin D) (x : LayerAddr A K D S) : LayerAddr A K D S :=
  setSelBits ρ x (Function.update (sel ρ x) j (!(x.2.1 j ρ)))

theorem flipSel_bit (ρ : Fin K) (j j' : Fin D) (t' : Fin K) (x : LayerAddr A K D S) :
    (flipSel ρ j x).2.1 j' t' = if j' = j ∧ t' = ρ then !(x.2.1 j ρ) else x.2.1 j' t' := by
  simp only [flipSel, setSelBits, sel, Function.update_apply]
  by_cases ht : t' = ρ <;> by_cases hj : j' = j <;> simp [ht, hj]

end Sel

/-! ## The address encoding -/

section Encode

variable {A K D S : ℕ}

theorem encodeAddr_row {c : RowClass (layerLayout A K D S)} (h0 : c.row.val = 0)
    {x x' : LayerAddr A K D S} (h : x.1 = x'.1) : encodeAddr x c.row = encodeAddr x' c.row := by
  simp only [encodeAddr, dif_pos h0, h]

theorem mem_encodeAddr_iff {c : RowClass (layerLayout A K D S)} (h0 : c.row.val = 0)
    {x x' : LayerAddr A K D S} (h : x.1 = x'.1) : c.mem (encodeAddr x) ↔ c.mem (encodeAddr x') := by
  unfold RowClass.mem
  rw [encodeAddr_row h0 h]

/-- `encodeAddr x i` only depends on the components of `x` read at field `i`. -/
theorem encodeAddr_congr {x x' : LayerAddr A K D S} (h1 : x.1 = x'.1) (h3 : x.2.2 = x'.2.2)
    (i : Fin (layerLayout A K D S).n)
    (h2 : ∀ (j : Fin D) (t : Fin K), i.val = 1 + j.val * K + (K - 1 - t.val) →
      x.2.1 j t = x'.2.1 j t) :
    encodeAddr x i = encodeAddr x' i := by
  by_cases h0 : i.val = 0
  · simp only [encodeAddr, dif_pos h0, h1]
  · by_cases hle : i.val ≤ D * K
    · have hK : 0 < K := by
        rcases Nat.eq_zero_or_pos K with hK | hK
        · exfalso
          have hDK : D * K = 0 := by rw [hK, Nat.mul_zero]
          omega
        · exact hK
      have hdm := Nat.div_add_mod' (i.val - 1) K
      have hmod := Nat.mod_lt (i.val - 1) hK
      apply Fin.ext
      simp only [encodeAddr, dif_neg h0, dif_pos hle, dif_pos hK]
      rw [h2 ⟨(i.val - 1) / K, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)⟩
        ⟨K - 1 - (i.val - 1) % K, by omega⟩ (by simp only; omega)]
    · simp only [encodeAddr, dif_neg h0, dif_neg hle, h3]

theorem selField_lt (ρ : Fin K) (j : Fin D) : selField K ρ.val j.val < (layerLayout A K D S).n := by
  have hj := j.isLt
  have hρ := ρ.isLt
  have : j.val * K + K ≤ D * K := by nlinarith
  simp only [layerLayout, selField]
  omega

theorem selField_le (ρ : Fin K) (j : Fin D) : 1 + j.val * K + (K - 1 - ρ.val) ≤ D * K := by
  have hj := j.isLt
  have hρ := ρ.isLt
  have : j.val * K + K ≤ D * K := by nlinarith
  omega

theorem layerLayout_r_sel (ρ : Fin K) (j : Fin D) :
    (layerLayout A K D S).r ⟨selField K ρ.val j.val, selField_lt ρ j⟩ = 2 := by
  have hle := selField_le ρ j
  simp only [layerLayout, selField] at hle ⊢
  rw [if_neg (by omega), if_pos hle]

/-- The value of `encodeAddr y` at the selected field of chunk `j`. -/
theorem encodeAddr_sel_val (ρ : Fin K) (j : Fin D) (y : LayerAddr A K D S) :
    (encodeAddr y ⟨selField K ρ.val j.val, selField_lt ρ j⟩).val = if y.2.1 j ρ then 1 else 0 := by
  exact CCoreNode.encodeAddr_bit y j ρ

/-- Updating the selected field of chunk `j` to the other value flips that bit. -/
theorem update_encodeAddr_flip (ρ : Fin K) (j : Fin D) (x : LayerAddr A K D S)
    (p : 1 - (encodeAddr x ⟨selField K ρ.val j.val, selField_lt ρ j⟩).val <
      (layerLayout A K D S).r ⟨selField K ρ.val j.val, selField_lt ρ j⟩) :
    Function.update (encodeAddr x) ⟨selField K ρ.val j.val, selField_lt ρ j⟩
        ⟨1 - (encodeAddr x ⟨selField K ρ.val j.val, selField_lt ρ j⟩).val, p⟩ =
      encodeAddr (flipSel ρ j x) := by
  funext i'
  by_cases hii : i' = ⟨selField K ρ.val j.val, selField_lt ρ j⟩
  · subst hii
    rw [Function.update_self]
    apply Fin.ext
    show 1 - (encodeAddr x ⟨selField K ρ.val j.val, selField_lt ρ j⟩).val = _
    rw [encodeAddr_sel_val, encodeAddr_sel_val, flipSel_bit]
    cases x.2.1 j ρ <;> simp
  · rw [Function.update_of_ne hii]
    refine encodeAddr_congr (x := x) (x' := flipSel ρ j x) rfl rfl i' fun j' t' hjt => ?_
    rw [flipSel_bit, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hii (Fin.ext hjt)

theorem decodeArr_encodeArr {rr : ℕ} (z : RArr (LayerAddr A K D S) rr) :
    decodeArr (encodeArr z) = z := by
  funext x
  simp only [decodeArr, encodeArr, CCoreNode.decodeAddr_encodeAddr]

end Encode

/-! ## One individual kernel on decoded arrays -/

section Gate

variable {A K D S : ℕ}

theorem sum_erase_two {β : Type*} [AddCommMonoid β] {n : ℕ} (hn : n = 2) (t : Fin n)
    (w : Fin n → β) :
    ∑ t' ∈ Finset.univ.erase t, w t' = w ⟨1 - t.val, by have := t.isLt; omega⟩ := by
  subst hn
  have key : ∀ t : Fin 2, Finset.univ.erase t = {⟨1 - t.val, by have := t.isLt; omega⟩} := by
    decide
  rw [key t, Finset.sum_singleton]

theorem cGate_eq {rr n : ℕ} (hn : n = 2) (w : Fin n → (Fin rr → ℂ)) (t : Fin n) :
    cGate w t = ka • w t + kb • w ⟨1 - t.val, by have := t.isLt; omega⟩ := by
  unfold cGate
  rw [sum_erase_two hn]

/-- One individual kernel on chunk `j`, on decoded arrays: `a z(x) + b z(x')` on the addresses
of `c`, `x'` = `x` with the selected bit of chunk `j` flipped. -/
noncomputable def gateR {rr : ℕ} (ρ : Fin K) (j : Fin D) (c : RowClass (layerLayout A K D S))
    (z : RArr (LayerAddr A K D S) rr) : RArr (LayerAddr A K D S) rr :=
  fun x => if c.mem (encodeAddr x) then ka • z x + kb • z (flipSel ρ j x) else z x

theorem decodeArr_runIn_digitGate {rr : ℕ} (ρ : Fin K) (j : Fin D)
    (c : RowClass (layerLayout A K D S)) (Y : (layerLayout A K D S).Addr → (Fin rr → ℂ)) :
    decodeArr (Step.runIn c (Step.digitGate ⟨selField K ρ.val j.val, selField_lt ρ j⟩ cGate) Y) =
      gateR ρ j c (decodeArr Y) := by
  funext x
  simp only [decodeArr, Step.runIn, Step.run, gateR]
  split_ifs with hmem
  · rw [cGate_eq (layerLayout_r_sel ρ j)]
    simp only [Function.update_eq_self]
    rw [update_encodeAddr_flip]
  · rfl

/-- `C` on the selected bits in `T`, along the fibres `b ↦ setSelBits ρ x b`, on the addresses
of `c` (decoded arrays). -/
noncomputable def cdonR {rr : ℕ} (ρ : Fin K) (T : Finset (Fin D))
    (c : RowClass (layerLayout A K D S)) (z : RArr (LayerAddr A K D S) rr) :
    RArr (LayerAddr A K D S) rr :=
  fun x kk => if c.mem (encodeAddr x) then CDon T (fun b => z (setSelBits ρ x b) kk) (sel ρ x)
    else z x kk

/-- `CDon {j}` at a point: `a F(e) + b F(e with bit j flipped)`. -/
theorem cdon_single' {D : ℕ} (F : (Fin D → Bool) → ℂ) (e : Fin D → Bool) (j : Fin D) :
    CDon {j} F e = ka * F e + kb * F (Function.update e j (!e j)) := by
  rw [CDonAux.cdon_single]
  cases hej : e j
  · have h1 : Function.update e j false = e := by
      rw [← hej]
      exact Function.update_eq_self j e
    simp only [h1, Bool.not_false, if_true]
    simp only [ka, kb]
    ring
  · have h1 : Function.update e j true = e := by
      rw [← hej]
      exact Function.update_eq_self j e
    simp only [h1, Bool.not_true, Bool.true_eq_false, if_false]
    simp only [ka, kb]
    ring

theorem gateR_eq_cdonR {rr : ℕ} (ρ : Fin K) (j : Fin D) (c : RowClass (layerLayout A K D S))
    (z : RArr (LayerAddr A K D S) rr) : gateR ρ j c z = cdonR ρ {j} c z := by
  funext x kk
  simp only [gateR, cdonR]
  split_ifs with hmem
  · rw [cdon_single', setSelBits_sel_self]
    rfl
  · rfl

theorem cdonR_empty {rr : ℕ} (ρ : Fin K) (c : RowClass (layerLayout A K D S))
    (z : RArr (LayerAddr A K D S) rr) : cdonR ρ ∅ c z = z := by
  funext x kk
  simp only [cdonR, CDonAux.cdon_empty, setSelBits_sel_self, ite_self]

theorem cdonR_comp {rr : ℕ} (ρ : Fin K) {c : RowClass (layerLayout A K D S)} (h0 : c.row.val = 0)
    {S' T : Finset (Fin D)} (hST : Disjoint S' T) (z : RArr (LayerAddr A K D S) rr) :
    cdonR ρ S' c (cdonR ρ T c z) = cdonR ρ (S' ∪ T) c z := by
  funext x kk
  simp only [cdonR]
  split_ifs with hmem
  · rw [← CDonAux.cdon_union D S' T _ hST]
    congr 1
    funext b
    rw [if_pos ((mem_encodeAddr_iff (x := setSelBits ρ x b) (x' := x) h0 rfl).mpr hmem)]
    simp only [setSelBits_setSelBits, sel_setSelBits]
  · rfl

end Gate

/-! ## `CDon` on a group of chunks is `cCoreVal` -/

section Group

variable {A K D S : ℕ}

/-- The chunks `j0, …, j0+e−1`. -/
def grpSet (D j0 e : ℕ) : Finset (Fin D) := Finset.univ.filter fun j => j0 ≤ j.val ∧ j.val < j0 + e

/-- Selected bits with the group overwritten by `bs`. -/
def mergeG (ρ : Fin K) (x : LayerAddr A K D S) (j0 e : ℕ) (bs : Fin e → Bool) : Fin D → Bool :=
  fun j => if hj : j0 ≤ j.val ∧ j.val < j0 + e then bs ⟨j.val - j0, by omega⟩ else sel ρ x j

/-- The group part of a selected-bit vector. -/
def restrictG {D : ℕ} (j0 e : ℕ) (h : j0 + e ≤ D) (b : Fin D → Bool) : Fin e → Bool :=
  fun i => b ⟨j0 + i.val, by have := i.isLt; omega⟩

theorem setSelBits_mergeG (ρ : Fin K) (x : LayerAddr A K D S) (j0 e : ℕ) (bs : Fin e → Bool) :
    setSelBits ρ x (mergeG ρ x j0 e bs) = groupSel ρ j0 e x bs := by
  simp only [setSelBits, groupSel, mergeG, sel]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  by_cases hj : j0 ≤ j.val ∧ j.val < j0 + e
  · simp only [dif_pos hj]
  · simp only [dif_neg hj, Function.update_eq_self]

theorem mergeG_off (ρ : Fin K) (x : LayerAddr A K D S) (j0 e : ℕ) (bs : Fin e → Bool) (j : Fin D)
    (hj : j ∉ grpSet D j0 e) : sel ρ x j = mergeG ρ x j0 e bs j := by
  simp only [grpSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [mergeG, dif_neg hj]

theorem restrictG_mergeG (ρ : Fin K) (x : LayerAddr A K D S) (j0 e : ℕ) (h : j0 + e ≤ D)
    (bs : Fin e → Bool) : restrictG j0 e h (mergeG ρ x j0 e bs) = bs := by
  funext i
  have hi := i.isLt
  have hc : j0 ≤ j0 + i.val ∧ j0 + i.val < j0 + e := ⟨Nat.le_add_right _ _, by omega⟩
  simp only [restrictG, mergeG]
  rw [dif_pos hc]
  congr 1
  apply Fin.ext
  show j0 + i.val - j0 = i.val
  omega

theorem mergeG_restrictG (ρ : Fin K) (x : LayerAddr A K D S) (j0 e : ℕ) (h : j0 + e ≤ D)
    (b : Fin D → Bool) (hb : ∀ j, j ∉ grpSet D j0 e → sel ρ x j = b j) :
    mergeG ρ x j0 e (restrictG j0 e h b) = b := by
  funext j
  simp only [mergeG, restrictG]
  by_cases hj : j0 ≤ j.val ∧ j.val < j0 + e
  · rw [dif_pos hj]
    congr 1
    apply Fin.ext
    simp only []
    omega
  · rw [dif_neg hj]
    exact hb j (by simp only [grpSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj)

theorem prod_grpSet (j0 e : ℕ) (h : j0 + e ≤ D) (F : Fin D → ℂ) :
    ∏ i : Fin e, F ⟨j0 + i.val, by have := i.isLt; omega⟩ = ∏ j ∈ grpSet D j0 e, F j := by
  refine Finset.prod_bij (fun i _ => ⟨j0 + i.val, by have := i.isLt; omega⟩) ?_ ?_ ?_ ?_
  · intro i _
    simp only [grpSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have := i.isLt
    omega
  · intro i₁ _ i₂ _ hi
    apply Fin.ext
    have := congrArg Fin.val hi
    simp only [] at this
    omega
  · intro j hj
    simp only [grpSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j.val - j0, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only []
    omega
  · intro i _
    rfl

/-- `CDon` on the group, along the fibre of `x`, is `cCoreVal`. -/
theorem cdon_grp_eq {rr : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (z : RArr (LayerAddr A K D S) rr) (x : LayerAddr A K D S) (kk : Fin rr) :
    CDon (grpSet D j0 e) (fun b => z (setSelBits ρ x b) kk) (sel ρ x) = cCoreVal ρ j0 e h z x kk := by
  unfold CDon cCoreVal CD
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (mergeG ρ x j0 e) (restrictG j0 e h) ?_ ?_ ?_ ?_ ?_
  · intro bs _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun j hj => mergeG_off ρ x j0 e bs j hj
  · intro b _
    exact Finset.mem_univ _
  · intro bs _
    exact restrictG_mergeG ρ x j0 e h bs
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact mergeG_restrictG ρ x j0 e h b hb
  · intro bs _
    rw [setSelBits_mergeG, ← prod_grpSet j0 e h]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi := i.isLt
    have hm : mergeG ρ x j0 e bs ⟨j0 + i.val, by omega⟩ = bs i := by
      have hc : j0 ≤ j0 + i.val ∧ j0 + i.val < j0 + e := ⟨Nat.le_add_right _ _, by omega⟩
      simp only [mergeG]
      rw [dif_pos hc]
      congr 1
      apply Fin.ext
      show j0 + i.val - j0 = i.val
      omega
    rw [hm]
    rfl

theorem cdonR_grp {rr : ℕ} (ρ : Fin K) (c : RowClass (layerLayout A K D S)) (j0 e : ℕ)
    (h : j0 + e ≤ D) (z : RArr (LayerAddr A K D S) rr) :
    cdonR ρ (grpSet D j0 e) c z =
      fun x => if c.mem (encodeAddr x) then cCoreVal ρ j0 e h z x else z x := by
  funext x kk
  simp only [cdonR]
  split_ifs with hmem
  · exact cdon_grp_eq ρ j0 e h z x kk
  · rfl

end Group

/-! ## Leaves: lists of individual kernels -/

section Leaves

variable {A K D S : ℕ}

theorem dgate_eq {rr : ℕ} (ρ : Fin K) (j : Fin D) :
    (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ.val j.val)) =
      [Step.digitGate ⟨selField K ρ.val j.val, selField_lt ρ j⟩ cGate] := by
  unfold dgate
  rw [dif_pos (selField_lt ρ j)]

theorem op_run_prim {L : Layout} {β Child : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (s : Step L β)
    (Y : L.Addr → β) : Op.run crun c (Op.prim s) Y = s.runIn c Y := rfl

theorem grpSet_succ (j0 n : ℕ) (hj : j0 + n < D) :
    ({⟨j0 + n, hj⟩} : Finset (Fin D)) ∪ grpSet D j0 n = grpSet D j0 (n + 1) := by
  ext j
  simp only [grpSet, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.ext_iff]
  omega

theorem disjoint_grpSet (j0 n : ℕ) (hj : j0 + n < D) :
    Disjoint ({⟨j0 + n, hj⟩} : Finset (Fin D)) (grpSet D j0 n) := by
  rw [Finset.disjoint_singleton_left]
  simp only [grpSet, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- The leaf list of `n` kernels on the chunks `j0, …, j0+n−1` is `CDon` on that group. -/
theorem run_dgates {rr k : ℕ} (ρ : Fin K) {c : RowClass (layerLayout A K D S)}
    (h0 : c.row.val = 0) (j0 : ℕ) :
    ∀ n, j0 + n ≤ D → ∀ Y : (layerLayout A K D S).Addr → (Fin rr → ℂ),
      decodeArr (List.foldl (fun A o => Op.run (ProcK.run k) c o A) Y
        ((List.range n).flatMap fun t =>
          (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ.val (j0 + t))).map
            Op.prim)) = cdonR ρ (grpSet D j0 n) c (decodeArr Y)
  | 0, _, Y => by
    have : grpSet D j0 0 = ∅ := by
      ext j
      simp only [grpSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      omega
    rw [this, cdonR_empty]
    rfl
  | n + 1, hn, Y => by
    have hj : j0 + n < D := by omega
    rw [List.range_succ, List.flatMap_append, List.foldl_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [dgate_eq ρ ⟨j0 + n, hj⟩]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [op_run_prim, decodeArr_runIn_digitGate ρ ⟨j0 + n, hj⟩, run_dgates ρ h0 j0 n (by omega) Y,
      gateR_eq_cdonR,
      cdonR_comp ρ h0 (disjoint_grpSet j0 n hj), grpSet_succ j0 n hj]

end Leaves

/-! ## The induction -/

section Induction

variable {A K D S : ℕ}

theorem procK_run_zero {L : Layout} {β : Type} (p : ProcK L β 0) (c : RowClass L)
    (Y : L.Addr → β) : ProcK.run 0 p c Y = List.foldl (fun A s => Step.runIn c s A) Y p := rfl

theorem procK_run_succ {L : Layout} {β : Type} (k : ℕ) (p : ProcK L β (k + 1)) (c : RowClass L)
    (Y : L.Addr → β) :
    ProcK.run (k + 1) p c Y = List.foldl (fun A o => Op.run (ProcK.run k) c o A) Y p := rfl

theorem op_run_node {L : Layout} {β Child : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (W : ℕ)
    (hW : 0 < W) (ops : List (RoleOp L β W Child)) (Y : L.Addr → β) :
    Op.run crun c (Op.node W hW ops) Y = ops.foldl (fun A o => o.run crun c hW A) Y := rfl

theorem sub_row {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).row = c.row := rfl

theorem sub_mu {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).μ = c.μ * W := rfl

theorem cCoreProc_zero {rr ρ kLeaf : ℕ}
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (j0 : ℕ) :
    cCoreProc A K D S rr ρ kLeaf cdat 0 j0 = dgate (selField K ρ j0) := by
  rw [cCoreProc]

theorem cCoreProc_leaf {rr ρ kLeaf : ℕ}
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (k j0 : ℕ)
    (hleaf : k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      (List.range (mH ^ (k + 1))).flatMap fun t => (dgate (selField K ρ (j0 + t))).map .prim := by
  rw [cCoreProc]
  exact if_pos hleaf

theorem cCoreProc_node {rr ρ kLeaf : ℕ}
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (k j0 : ℕ)
    (hleaf : ¬ k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      [.node Wc Wc_pos (cxNodeOps ρ (mH ^ k) j0 cdat
        (fun t => cCoreProc A K D S rr ρ kLeaf cdat k (j0 + t * mH ^ k)))] := by
  rw [cCoreProc]
  exact if_neg hleaf

end Induction

/-- **Lemma A.10 (`lem:transfer-phase`) exactness by induction on the depth**, given the node and edge theorems. -/
theorem core_ind (hcert : ComplexNetCert) (h8 : RunEightSpecStmt) (hag : PackedAgreeStmt)
    (hpc : PackedProcCorrectStmt) (hnode : CCoreNode.CxNodeCorrectStmt)
    (hedge : CCoreNode.CoreEdgeRoleSpecStmt) (hser : SerialEqFramedStmt 100)
    {A K D S rr kLeaf : ℕ} (ρ : Fin K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    ∀ (k j0 : ℕ) (c : RowClass (layerLayout A K D S)) (h : j0 + mH ^ k ≤ D),
      CCoreHyps A K D S ρ.val cdat k j0 c → ∀ z : RArr (LayerAddr A K D S) rr,
        decodeArr (ProcK.run k (cCoreProc A K D S rr ρ.val kLeaf cdat k j0) c (encodeArr z)) =
          fun x => if c.mem (encodeAddr x) then cCoreVal ρ j0 (mH ^ k) h z x else z x
  | 0, j0, c, h, hc, z => by
    obtain ⟨_, _, _, hrow, _, _⟩ := hc
    have hj : j0 < D := by rw [pow_zero] at h; omega
    have hset : ({⟨j0, hj⟩} : Finset (Fin D)) = grpSet D j0 (mH ^ 0) := by
      ext j
      simp only [grpSet, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.ext_iff, pow_zero]
      omega
    rw [procK_run_zero, cCoreProc_zero, dgate_eq ρ ⟨j0, hj⟩]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [decodeArr_runIn_digitGate ρ ⟨j0, hj⟩, decodeArr_encodeArr, gateR_eq_cdonR, hset, cdonR_grp]
  | k + 1, j0, c, h, hc, z => by
    obtain ⟨hK6, hρ, _, hrow, hdiv, hval⟩ := hc
    by_cases hleaf : k + 1 < kLeaf
    · rw [procK_run_succ, cCoreProc_leaf cdat k j0 hleaf, run_dgates ρ hrow j0 _ h,
        decodeArr_encodeArr, cdonR_grp]
    · have he : mH ^ (k + 1) = mH * mH ^ k := pow_succ' mH k
      have hdiv1 : c.μ * Wc ∣ A :=
        dvd_trans (Nat.mul_dvd_mul_left c.μ (dvd_pow_self Wc (Nat.succ_ne_zero k))) hdiv
      have hN : CCoreNode.NodeHypC A K D S ρ (mH ^ k) j0 c :=
        { K6 := hK6, f1 := Nat.one_le_pow _ _ (by norm_num [mH]), fits := he ▸ h, row0 := hrow,
          div := hdiv1 }
      have hchild : CCoreNode.ChildSpecC c ρ (mH ^ k) j0 hN.fits (ProcK.run k)
          (fun t => cCoreProc A K D S rr ρ.val kLeaf cdat k (j0 + t * mH ^ k)) := by
        intro k' t ht z'
        have hsub : CCoreHyps A K D S ρ.val cdat k (j0 + t * mH ^ k) (c.sub Wc Wc_pos k') := by
          refine ⟨hK6, hρ, CCoreNode.slot_le hN.fits ht, ?_, ?_, hval⟩
          · rw [sub_row]
            exact hrow
          · rw [sub_mu, Nat.mul_assoc, ← pow_succ']
            exact hdiv
        exact core_ind hcert h8 hag hpc hnode hedge hser ρ cdat k (j0 + t * mH ^ k)
          (c.sub Wc Wc_pos k') (CCoreNode.slot_le hN.fits ht) hsub z'
      have hE := hedge hcert h8 hag hpc ρ (mH ^ k) j0 c hN cdat hval (ProcK.run k) _ hchild
      rw [procK_run_succ, cCoreProc_node cdat k j0 hleaf]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [op_run_node]
      exact hnode hcert hser ρ (mH ^ k) j0 c hN cdat (ProcK.run k) _ hE (mH ^ (k + 1)) he h z

end CCoreAux

open CCoreAux in
/-- **Lemma A.10 (`lem:transfer-phase`) exactness from the node and edge theorems**: `CCoreProcCorrectStmt` given the node
theorem (`CCoreNode.CxNodeCorrectStmt`, `Proofs/CCoreNode.lean`) and the edge theorem
(`CCoreNode.CoreEdgeRoleSpecStmt`, `Proofs/CCoreEdge.lean`). `SerialEqFramedStmt 100` is supplied by
`serialEqFramed_holds`. -/
theorem cCoreProcCorrect_of_node_edge (hnode : CCoreNode.CxNodeCorrectStmt)
    (hedge : CCoreNode.CoreEdgeRoleSpecStmt) : CCoreProcCorrectStmt := by
  intro hcert h8 hag hpc _htc A K D S rr kLeaf ρ cdat k j0 c h hc z
  exact core_ind hcert h8 hag hpc hnode hedge (serialEqFramed_holds 100) ρ cdat k j0 c h hc z

/-- **Lemma A.10 (`lem:transfer-phase`) exactness** (`CCoreProcCorrectStmt`,
Appendix A.5 (`sec:transfer-frames`)), with no hypotheses beyond those inside the statement: the node
theorem `CCoreNode.cxNode_correct_holds` (`Proofs/CCoreNode.lean`) and the edge theorem
`coreEdgeRoleSpec_holds` (`Proofs/CCoreEdge.lean`) discharge the two premises of
`cCoreProcCorrect_of_node_edge`. -/
theorem cCoreProcCorrect_holds : CCoreProcCorrectStmt :=
  cCoreProcCorrect_of_node_edge CCoreNode.cxNode_correct_holds coreEdgeRoleSpec_holds

end SubNLogN.Math.Networks
