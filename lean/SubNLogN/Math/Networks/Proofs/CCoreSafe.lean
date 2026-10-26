import SubNLogN.Math.Networks.AppCSafe
import SubNLogN.Math.Networks.Proofs.PackedSafe

/-!
# Class safety of the Lemma A.10 (`lem:transfer-phase`) core procedure (`CCoreProcClassSafeStmt`)

Statement in `SubNLogN/Math/Networks/AppCSafe.lean`. We prove
`cCoreProcClassSafe_holds : CCoreProcClassSafeStmt`: under `CCoreHyps`, every primitive of
`cCoreProc … k j0`, run in its class (children in their role classes), reads only addresses of
that class, and every node has a complete role split. Helpers live in
`SubNLogN.Math.Networks.CCoreSafeAux`.

Only three parts of `CCoreHyps` are used: the row field of the class is field `0`,
`μ · W_c^k ∣ A`, and `ρ < K`. The edge data and the chunk range play no role, because
addressing never depends on them.
* An individual kernel (`digitGate` on the selected field `selField K ρ j ≥ 1`) changes a field
  other than `0`, so its fibres stay in the class (`dgate_safe`).
* Masks, phases (`addrMap`, `recMap`), gates and the final role permutation impose nothing.
* The Lemma A.9 (`lem:transfer13`) row additions run on slot positions `1 + (j0 + t f) K ≥ 1`; all their pulls fix field
  `0` (`PackedSafeAux` lemmas in `Proofs/PackedSafe.lean`; `topBitSteps_safe'` needs only `L = fK`, `ρ < K`,
  `f ≥ 1`).
* A node in a class with `μ · W_c^{k+1} ∣ A` has a complete split (`μ W_c ∣ A = r_0`). Its
  children run in `c.sub W_c k'`, with `(μ W_c) · W_c^k = μ W_c^{k+1}`, by induction on `k`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace CCoreSafeAux

open PackedSafeAux

/-! ## Unfolding lemmas (for abstract lists) -/

theorem procK_safe_zero_iff {L : Layout} {β : Type} (p : List (Step L β)) (c : RowClass L) :
    ProcK.ClassSafe 0 p c ↔ ∀ s ∈ p, Step.ClassSafe c s :=
  List.forall_iff_forall_mem

theorem procK_safe_succ_iff {L : Layout} {β : Type} (k : ℕ)
    (p : List (Model.Op L β (ProcK L β k))) (c : RowClass L) :
    ProcK.ClassSafe (k + 1) p c ↔ ∀ o ∈ p, Model.Op.ClassSafe (ProcK.ClassSafe k) c o :=
  List.forall_iff_forall_mem

theorem op_safe_node {L : Layout} {β Child : Type} (csafe : Child → RowClass L → Prop)
    (c : RowClass L) (W : ℕ) (hW : 0 < W) (ops : List (RoleOp L β W Child)) :
    Model.Op.ClassSafe csafe c (.node W hW ops) ↔
      (0 < W ∧ c.μ * W ∣ L.r c.row) ∧ ∀ o ∈ ops, RoleOp.ClassSafe csafe c hW o :=
  Iff.rfl

theorem sub_row {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).row = c.row := rfl

theorem sub_mu {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).μ = c.μ * W := rfl

/-! ## Individual kernels -/

section Leaves

variable {A K D S rr : ℕ}

/-- A digit gate on a field other than the row field `0` keeps its fibres in the class. -/
theorem digitGate_safe (c : RowClass (layerLayout A K D S)) (hrow : c.row.val = 0)
    (i : Fin (layerLayout A K D S).n) (hi : i.val ≠ 0)
    (G : (Fin ((layerLayout A K D S).r i) → (Fin rr → ℂ)) →
      (Fin ((layerLayout A K D S).r i) → (Fin rr → ℂ))) :
    Step.ClassSafe c (Step.digitGate i G) := by
  intro x v hx
  have hne : c.row ≠ i := fun h => hi (by rw [← h]; exact hrow)
  show (Function.update x i v c.row).val % c.μ = c.res
  rw [Function.update_of_ne hne]
  exact hx

theorem dgate_safe (c : RowClass (layerLayout A K D S)) (hrow : c.row.val = 0) (ρ j : ℕ) :
    ∀ s ∈ dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ j),
      Step.ClassSafe c s := by
  intro s hs
  unfold dgate at hs
  split_ifs at hs with hi
  · rw [List.mem_singleton] at hs
    subst hs
    exact digitGate_safe c hrow _ (by simp only [selField]; omega) cGate
  · simp at hs

end Leaves

/-! ## The Lemma A.9 (`lem:transfer13`) row additions -/

section Packed

variable {Ly : Layout}

/-- The top selected-bit flip is class safe (only `L = fK`, `ρ < K`, `f ≥ 1` are needed). -/
theorem topBitSteps_safe' {β : Type} {L K ρ f : ℕ} {C : Chunks3} (hL : L = f * K) (hρ : ρ < K)
    (hf : 1 ≤ f) (c : RowClass Ly) (hx : c.row.val < C.px ∨ C.px + L ≤ c.row.val)
    (hy : c.row.val < C.py ∨ C.py + L ≤ c.row.val) (hz : c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) :
    ∀ s ∈ topBitSteps (Ly := Ly) (β := β) L K ρ f C, Step.ClassSafe c s := by
  have hr := row_out_right hx hy hz
  have hj : ρ + (f - 1) * K < L := by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    rw [hL, Nat.add_sub_cancel, add_mul, one_mul]
    omega
  intro s hs
  simp only [topBitSteps, List.mem_append, List.mem_singleton] at hs
  rcases hs with (hs | rfl) | hs
  · exact swp_safe c hy hr s hs
  · exact shift_safe c _ (by omega)
  · exact swp_safe c hy hr s hs

/-- Every step of the Lemma A.9 (`lem:transfer13`) procedure is class safe when the row field precedes the three chunks
(no disjointness or range hypothesis is needed). -/
theorem packed_safe {β : Type} {L K ρ f : ℕ} {C : Chunks3} (hL : L = f * K) (hρ : ρ < K)
    (hf : 1 ≤ f) (c : RowClass Ly) (hx : c.row.val < C.px) (hy : c.row.val < C.py)
    (hz : c.row.val < C.pz) :
    ∀ s ∈ @id (List (Step Ly β)) (packedAddProc (Ly := Ly) (β := β) L K ρ f C),
      Step.ClassSafe c s := by
  intro s hs
  have hs' : s ∈ eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) ++
      [repairStep L K ρ f C] ++ topBitSteps L K ρ f C := hs
  rcases List.mem_append.mp hs' with hs1 | hs3
  · rcases List.mem_append.mp hs1 with hs1 | hs2
    · obtain ⟨op, -, hop⟩ := List.mem_flatMap.mp hs1
      exact lineSteps_safe c (Or.inl hx) (Or.inl hy) (Or.inl hz) op s hop
    · rw [List.mem_singleton] at hs2
      subst hs2
      exact repair_safe c (Or.inl hy) (Or.inl hz)
  · exact topBitSteps_safe' hL hρ hf c (Or.inl hx) (Or.inl hy) (Or.inl hz) s hs3

end Packed

/-! ## Edge operations and nodes -/

section Node

variable {A K D S rr : ℕ}

theorem coreEdgeOps_safe {Child : Type} (csafe : Child → RowClass (layerLayout A K D S) → Prop)
    (c : RowClass (layerLayout A K D S)) (hrow : c.row.val = 0) (ρ f j0 : ℕ) (hρ : ρ < K)
    (hf : 1 ≤ f) (Dd : CxEdgeData) (childOf : ℕ → Child) (kidx : Fin Wc)
    (hchild : ∀ t, csafe (childOf t) (c.sub Wc Wc_pos kidx)) :
    ∀ o ∈ coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 Dd childOf kidx,
      RoleOp.ClassSafe csafe c Wc_pos o := by
  have hrow' : (c.sub Wc Wc_pos kidx).row.val = 0 := by rw [sub_row]; exact hrow
  intro o ho
  simp only [coreEdgeOps, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · obtain ⟨p, -, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
    exact packed_safe (C := ⟨1 + (j0 + p.2.val * f) * K, 1 + (j0 + p.1.val * f) * K,
      1 + (j0 + thirdSlot p.1.val p.2.val * f) * K⟩) rfl hρ hf (c.sub Wc Wc_pos kidx)
      (by simp only; omega) (by simp only; omega) (by simp only; omega) s hs
  · obtain ⟨⟨t, ε⟩, -, ho⟩ := List.mem_flatMap.1 ho
    dsimp only at ho
    split_ifs at ho
    · rw [List.mem_singleton] at ho
      subst ho
      exact hchild t
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact trivial
      · exact hchild t
      · exact trivial
      · exact trivial
  · obtain ⟨p, -, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
    exact packed_safe (C := ⟨1 + (j0 + p.2.val * f) * K, 1 + (j0 + p.1.val * f) * K,
      1 + (j0 + thirdSlot p.1.val p.2.val * f) * K⟩) rfl hρ hf (c.sub Wc Wc_pos kidx)
      (by simp only; omega) (by simp only; omega) (by simp only; omega) s hs

theorem coreEdgeOpsAt_safe {Child : Type} (csafe : Child → RowClass (layerLayout A K D S) → Prop)
    (c : RowClass (layerLayout A K D S)) (hrow : c.row.val = 0) (ρ f j0 : ℕ) (hρ : ρ < K)
    (hf : 1 ≤ f) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (childOf : ℕ → Child) (hchild : ∀ kidx t, csafe (childOf t) (c.sub Wc Wc_pos kidx))
    (w : Role .complex 100) (v : Vertex .complex 100) :
    ∀ o ∈ coreEdgeOpsAt (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf w v,
      RoleOp.ClassSafe csafe c Wc_pos o := by
  intro o ho
  unfold coreEdgeOpsAt at ho
  split at ho
  · next e he =>
    exact coreEdgeOps_safe csafe c hrow ρ f j0 hρ hf (cdat e) childOf (roleIdxC w)
      (hchild (roleIdxC w)) o ho
  · simp at ho

theorem cxNodeOps_safe {Child : Type} (csafe : Child → RowClass (layerLayout A K D S) → Prop)
    (c : RowClass (layerLayout A K D S)) (hrow : c.row.val = 0) (ρ f j0 : ℕ) (hρ : ρ < K)
    (hf : 1 ≤ f) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (childOf : ℕ → Child) (hchild : ∀ kidx t, csafe (childOf t) (c.sub Wc Wc_pos kidx)) :
    ∀ o ∈ cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf,
      RoleOp.ClassSafe csafe c Wc_pos o := by
  intro o ho
  unfold cxNodeOps at ho
  rcases List.mem_append.1 ho with ho | ho
  rcases List.mem_append.1 ho with ho | ho
  rcases List.mem_append.1 ho with ho | ho
  rcases List.mem_append.1 ho with ho | ho
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 ho
    exact trivial
  · obtain ⟨j, -, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨ι, -, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨r, -, ho⟩ := List.mem_flatMap.1 ho
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
      split at ho
      · exact coreEdgeOpsAt_safe csafe c hrow ρ f j0 hρ hf cdat childOf hchild w _ o ho
      · simp at ho
    · rw [List.mem_singleton] at ho
      subst ho
      exact trivial
  · obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
    exact coreEdgeOpsAt_safe csafe c hrow ρ f j0 hρ hf cdat childOf hchild w _ o ho
  · obtain ⟨a, -, ho⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> exact trivial
  · rw [List.mem_singleton] at ho
    subst ho
    exact trivial

end Node

/-! ## The recursion -/

theorem cCoreProc_succ_of_lt {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {k j0 : ℕ}
    (h : k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      (List.range (mH ^ (k + 1))).flatMap fun t =>
        (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ (j0 + t))).map
          Op.prim := by
  simp only [cCoreProc]
  exact if_pos h

theorem cCoreProc_succ_of_not_lt {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {k j0 : ℕ}
    (h : ¬ k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      [.node Wc Wc_pos (cxNodeOps ρ (mH ^ k) j0 cdat
        (fun t => cCoreProc A K D S rr ρ kLeaf cdat k (j0 + t * mH ^ k)))] := by
  simp only [cCoreProc]
  exact if_neg h

/-- Class safety of `cCoreProc … k j0` in every class with row field `0` and `μ · W_c^k ∣ A`
(given `ρ < K`; no range or edge-data hypothesis). -/
theorem safe_main {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} (hρ : ρ < K) :
    ∀ (k j0 : ℕ) (c : RowClass (layerLayout A K D S)), c.row.val = 0 → c.μ * Wc ^ k ∣ A →
      ProcK.ClassSafe k (cCoreProc A K D S rr ρ kLeaf cdat k j0) c := by
  intro k
  induction k with
  | zero =>
    intro j0 c hrow _
    simp only [cCoreProc]
    exact (procK_safe_zero_iff _ c).2 (dgate_safe c hrow ρ j0)
  | succ k ih =>
    intro j0 c hrow hdiv
    by_cases hleaf : k + 1 < kLeaf
    · rw [cCoreProc_succ_of_lt hleaf]
      refine (procK_safe_succ_iff k _ c).2 ?_
      intro o ho
      obtain ⟨t, -, ho⟩ := List.mem_flatMap.1 ho
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
      exact dgate_safe c hrow ρ (j0 + t) s hs
    · rw [cCoreProc_succ_of_not_lt hleaf]
      refine (procK_safe_succ_iff k _ c).2 ?_
      intro o ho
      rw [List.mem_singleton] at ho
      subst ho
      refine (op_safe_node _ c Wc Wc_pos _).2 ⟨⟨Wc_pos, ?_⟩, ?_⟩
      · have hr : (layerLayout A K D S).r c.row = A := by
          show (if c.row.val = 0 then A else if c.row.val ≤ D * K then 2 else S) = A
          rw [if_pos hrow]
        rw [hr]
        exact dvd_trans (Nat.mul_dvd_mul_left c.μ (dvd_pow_self Wc (Nat.succ_ne_zero k))) hdiv
      · refine cxNodeOps_safe (ProcK.ClassSafe k) c hrow ρ (mH ^ k) j0 hρ
          (Nat.one_le_pow _ _ (by decide)) cdat _ ?_
        intro kidx t
        apply ih (j0 + t * mH ^ k) (c.sub Wc Wc_pos kidx)
        · rw [sub_row]
          exact hrow
        · rw [sub_mu, Nat.mul_assoc, ← pow_succ']
          exact hdiv

end CCoreSafeAux

/-- **Class safety of the Lemma A.10 (`lem:transfer-phase`) core procedure** (`CCoreProcClassSafeStmt`). Under
`CCoreHyps`, `cCoreProc … k j0` is class safe in `c`: every primitive (in its class, children in
their role classes) reads only addresses of that class, and every node has a complete role split.
Only the row field `0`, `μ · W_c^k ∣ A` and `ρ < K` are used. -/
theorem cCoreProcClassSafe_holds : CCoreProcClassSafeStmt := by
  intro A K D S rr ρ kLeaf cdat k j0 c hH
  obtain ⟨-, hρ, -, hrow, hdiv, -⟩ := hH
  exact CCoreSafeAux.safe_main hρ k j0 c hrow hdiv

end SubNLogN.Math.Networks
