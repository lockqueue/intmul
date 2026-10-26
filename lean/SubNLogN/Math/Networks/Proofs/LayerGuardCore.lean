import SubNLogN.Math.Networks.Proofs.LayerGuardSteps

/-!
# Guard charges of the Lemma A.10 (`lem:transfer-phase`) core procedure (helper for `Prop71GuardStmt`)

`chargeOK_cCoreProc`: every step and gate of `cCoreProc … k j0` respects the charges `cs2` (one per
individual kernel `digitGate`, zero for all other steps) and `gateCharge` (complex scalar rows), for
the pointwise guard `ptG P` of `LayerGuardSteps`, provided the piece lies in the chunk range
(`j0 + m^k ≤ D`), `ρ < K`, and the edge data are valid. Route: induction on `k`; leaves are
individual kernels on selected-bit fields (range `2`); a node consists of address-sign masks
(`zMask`, `zSlot`: phases `(−1)^n`), the complex scalar rows (`gateOpC`), edge operations
(`coreEdgeOps`: Lemma A.9 (`lem:transfer13`) row additions = address moves of charge `0`, children on pieces inside the
range since a valid residual basis has at most `m` vectors, inverse-kernel phases `(−i)^f`), the sink
corrections (phases `i^{27f}`, `−1`) and a relabelling.
-/

namespace SubNLogN.Math.Networks.LayerGuardCore

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh
  SubNLogN.Math.Networks.LayerGuardRun SubNLogN.Math.Networks.LayerGuardSteps

/-- Step charges: one per individual kernel, zero otherwise. -/
def cs2 {L : Layout} {rr : ℕ} : Step L (Fin rr → ℂ) → ℕ
  | .digitGate _ _ => 1
  | _ => 0

/-! ## Valid residual bases are short -/

theorem dotC_comm {h : ℕ} (x y : Pt h) : dotC x y = dotC y x := by
  unfold dotC
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem dotC_sum_smul_left {h n : ℕ} (g : Fin n → ZMod 2) (v : Fin n → Pt h) (y : Pt h) :
    dotC (∑ i, g i • v i) y = ∑ i, g i * dotC (v i) y := by
  unfold dotC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- A valid edge datum has at most `m` residual basis vectors (an orthonormal list is linearly
independent in `𝔽₂^m`). -/
theorem valid_basis_length_le {e : Vertex .complex 100 × Vertex .complex 100} {Dd : CxEdgeData}
    (hv : Dd.Valid e) : Dd.basis.length ≤ mH := by
  obtain ⟨⟨hnorm, hpair, -⟩, -⟩ := hv
  have hpair' : ∀ i j : Fin Dd.basis.length, i ≠ j →
      dotC (Dd.basis.get i) (Dd.basis.get j) = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact List.pairwise_iff_get.mp hpair i j h
    · rw [dotC_comm]
      exact List.pairwise_iff_get.mp hpair j i h
  have hli : LinearIndependent (ZMod 2) (fun i : Fin Dd.basis.length => Dd.basis.get i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have key : dotC (∑ i, g i • Dd.basis.get i) (Dd.basis.get j) = g j := by
      rw [dotC_sum_smul_left, Finset.sum_eq_single j]
      · rw [hnorm _ (List.get_mem ..), mul_one]
      · intro i _ hij
        rw [hpair' i j hij, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hg] at key
    rw [← key]
    simp [dotC]
  have h := hli.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] using h

/-! ## Address moves -/

/-- Steps that only move records (address bijections). -/
def IsMove {L : Layout} {β : Type} : Step L β → Prop
  | .elem _ => True
  | .sparsePerm _ _ => True
  | .swapBlocks _ _ _ => True
  | _ => False

theorem stepOK_of_isMove {L : Layout} {β : Type} (pt : ℕ → β → Prop) {s : Step L β}
    (hs : IsMove s) : StepOK pt s 0 := by
  cases s with
  | elem e => exact stepOK_elem pt e
  | sparsePerm pull supp => exact stepOK_sparsePerm pt pull supp
  | swapBlocks t₀ s₀ len => exact stepOK_swapBlocks pt t₀ s₀ len
  | recMap f => exact hs.elim
  | addrMap f => exact hs.elim
  | digitGate i G => exact hs.elim

theorem cs2_of_isMove {L : Layout} {rr : ℕ} {s : Step L (Fin rr → ℂ)} (hs : IsMove s) :
    cs2 s = 0 := by
  cases s <;> first | rfl | exact hs.elim

theorem isMove_of_mem_ite {Ly : Layout} {β : Type} {c : Prop} [Decidable c] (a b L : ℕ)
    {s : Step Ly β} (h : s ∈ (if c then [] else [Step.swapBlocks a b L])) : IsMove s := by
  split_ifs at h
  · simp at h
  · rw [List.mem_singleton] at h
    subst h
    trivial

theorem isMove_lineSteps {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3)
    (op : Bool × ℤ × ℕ) : ∀ s ∈ lineSteps (Ly := Ly) (β := β) L K ρ f C op, IsMove s := by
  intro s hs
  simp only [lineSteps, List.mem_append, List.mem_singleton] at hs
  rcases hs with (h | h) | h
  · exact isMove_of_mem_ite _ _ _ h
  · subst h
    trivial
  · exact isMove_of_mem_ite _ _ _ h

theorem isMove_topBitSteps {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) :
    ∀ s ∈ topBitSteps (Ly := Ly) (β := β) L K ρ f C, IsMove s := by
  intro s hs
  simp only [topBitSteps, List.mem_append, List.mem_singleton] at hs
  rcases hs with (h | h) | h
  · exact isMove_of_mem_ite _ _ _ h
  · subst h
    trivial
  · exact isMove_of_mem_ite _ _ _ h

theorem isMove_packed {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) :
    ∀ s ∈ @id (List (Step Ly β)) (packedAddProc (Ly := Ly) (β := β) L K ρ f C), IsMove s := by
  intro s hs
  have hs' : s ∈ eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) ++
      [repairStep L K ρ f C] ++ topBitSteps L K ρ f C := hs
  rcases List.mem_append.mp hs' with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨op, -, h⟩ := List.mem_flatMap.mp h
      exact isMove_lineSteps L K ρ f C op s h
    · rw [List.mem_singleton] at h
      subst h
      trivial
  · exact isMove_topBitSteps L K ρ f C s h

/-! ## Individual kernels on selected-bit fields -/

theorem selField_r {A K D S ρ j : ℕ} (hρ : ρ < K) (hj : j < D)
    (h : selField K ρ j < (layerLayout A K D S).n) :
    (layerLayout A K D S).r ⟨selField K ρ j, h⟩ = 2 := by
  have h1 : (j + 1) * K ≤ D * K := Nat.mul_le_mul_right K hj
  have h2 : (j + 1) * K = j * K + K := Nat.succ_mul j K
  simp only [layerLayout, selField]
  rw [if_neg (by omega), if_pos (by omega)]

theorem chargeOK_dgate (P : ℕ) {A K D S rr : ℕ} (ρ j : ℕ) (hρ : ρ < K) (hj : j < D) :
    ∀ s ∈ (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ j)),
      StepOK (ptG (rr := rr) P) s (cs2 s) := by
  intro s hs
  unfold dgate at hs
  split_ifs at hs with h
  · rw [List.mem_singleton] at hs
    subst hs
    exact stepOK_digitGate_cGate P _ (selField_r hρ hj h)
  · simp at hs

/-! ## Phases -/

theorem stepOK_zMask (P : ℕ) {A K D S rr : ℕ} (ρ f j0 : ℕ) (a : Addr 100) :
    StepOK (ptG (rr := rr) P) (zMask (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 a) 0 := by
  unfold zMask
  exact stepOK_addrMap_phase P _ (fun _ => phase_neg_one_pow _)

theorem stepOK_zSlot (P : ℕ) {A K D S rr : ℕ} (ρ f j0 t : ℕ) :
    StepOK (ptG (rr := rr) P) (zSlot (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 t) 0 := by
  unfold zSlot
  exact stepOK_addrMap_phase P _ (fun _ => phase_neg_one_pow _)

/-! ## Edge operations and nodes -/

theorem chgOK_coreEdgeOps (P : ℕ) {A K D S rr : ℕ} {Child : Type} (ρ f j0 : ℕ) (Dd : CxEdgeData)
    (childOf : ℕ → Child) (k : Fin Wc) (cok : Child → Prop)
    (hchild : ∀ t < Dd.basis.length, cok (childOf t)) :
    ∀ ro ∈ coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 Dd childOf k,
      RoleOp.chgOK (ptG (rr := rr) P) cs2 gateCharge cok ro := by
  intro ro hro
  simp only [coreEdgeOps] at hro
  rcases List.mem_append.mp hro with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨p, -, h⟩ := List.mem_flatMap.mp h
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
      have hm := isMove_packed _ _ _ _ _ s hs
      show StepOK (ptG P) s (cs2 s)
      rw [cs2_of_isMove hm]
      exact stepOK_of_isMove _ hm
    · obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp h
      have hp1 : p.1 < Dd.basis.length := List.mem_range.mp (List.of_mem_zip hp).1
      split_ifs at h
      · rw [List.mem_singleton] at h
        subst h
        exact hchild p.1 hp1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl
        · exact stepOK_zSlot P ρ f j0 p.1
        · exact hchild p.1 hp1
        · exact stepOK_zSlot P ρ f j0 p.1
        · exact stepOK_recMap_phase P _ (phase_neg_I_pow f)
  · obtain ⟨p, -, h⟩ := List.mem_flatMap.mp h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    have hm := isMove_packed _ _ _ _ _ s hs
    show StepOK (ptG P) s (cs2 s)
    rw [cs2_of_isMove hm]
    exact stepOK_of_isMove _ hm

theorem chgOK_coreEdgeOpsAt (P : ℕ) {A K D S rr : ℕ} {Child : Type} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Child)
    (cok : Child → Prop) (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (hchild : ∀ t < mH, cok (childOf t)) (w : Role .complex 100) (v : Vertex .complex 100) :
    ∀ ro ∈ coreEdgeOpsAt (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf w v,
      RoleOp.chgOK (ptG (rr := rr) P) cs2 gateCharge cok ro := by
  intro ro hro
  unfold coreEdgeOpsAt at hro
  split at hro
  · rename_i e he
    have hmem : e ∈ edges w := List.mem_of_find?_eq_some he
    have hlen := valid_basis_length_le (hval w e hmem)
    exact chgOK_coreEdgeOps P ρ f j0 (cdat e) childOf (roleIdxC w) cok
      (fun t ht => hchild t (lt_of_lt_of_le ht hlen)) ro hro
  · simp at hro

theorem chgOK_cxNodeOps (P : ℕ) {A K D S rr : ℕ} {Child : Type} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Child)
    (cok : Child → Prop) (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (hchild : ∀ t < mH, cok (childOf t)) :
    ∀ ro ∈ cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf,
      RoleOp.chgOK (ptG (rr := rr) P) cs2 gateCharge cok ro := by
  intro ro hro
  simp only [cxNodeOps] at hro
  rcases List.mem_append.mp hro with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
          exact stepOK_zMask P ρ f j0 a
        · obtain ⟨j, -, h⟩ := List.mem_flatMap.mp h
          obtain ⟨ι, -, h⟩ := List.mem_flatMap.mp h
          obtain ⟨r, -, h⟩ := List.mem_flatMap.mp h
          rcases List.mem_append.mp h with h | h
          · obtain ⟨w, -, h⟩ := List.mem_flatMap.mp h
            split at h
            · exact chgOK_coreEdgeOpsAt P ρ f j0 cdat childOf cok hval hchild w _ ro h
            · simp at h
          · rw [List.mem_singleton] at h
            subst h
            exact gateOK_rowUpd P j ι r
      · obtain ⟨w, -, h⟩ := List.mem_flatMap.mp h
        exact chgOK_coreEdgeOpsAt P ρ f j0 cdat childOf cok hval hchild w _ ro h
    · obtain ⟨a, -, h⟩ := List.mem_flatMap.mp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact stepOK_zMask P ρ f j0 a
      · exact stepOK_recMap_phase P _ (phase_I_pow (27 * f))
      · exact stepOK_recMap_phase P _ phase_neg_one
  · rw [List.mem_singleton] at h
    subst h
    trivial

/-! ## The core procedure -/

/-- **Charges of the Lemma A.10 (`lem:transfer-phase`) core.** For `ρ < K`, valid edge data and a piece inside the chunk range
(`j0 + m^k ≤ D`), every step and gate of `cCoreProc … k j0` (children included) respects the
charges `cs2` (one per individual kernel) and `gateCharge` for the guard `ptG P`. -/
theorem chargeOK_cCoreProc (P A K D S rr ρ kLeaf : ℕ) (hρ : ρ < K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) :
    ∀ (k j0 : ℕ), j0 + mH ^ k ≤ D →
      ChargeOK (ptG (rr := rr) P) cs2 gateCharge k (cCoreProc A K D S rr ρ kLeaf cdat k j0) := by
  intro k
  induction k with
  | zero =>
    intro j0 hj0
    rw [pow_zero] at hj0
    exact chargeOK_dgate P ρ j0 hρ (by omega)
  | succ k ih =>
    intro j0 hj0
    by_cases hleaf : k + 1 < kLeaf
    · have heq : cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
          (List.range (mH ^ (k + 1))).flatMap fun t => (dgate (selField K ρ (j0 + t))).map .prim := by
        rw [cCoreProc]
        exact if_pos hleaf
      rw [heq]
      intro o ho
      obtain ⟨t, ht, ho⟩ := List.mem_flatMap.mp ho
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ho
      have ht' := List.mem_range.mp ht
      exact chargeOK_dgate P ρ (j0 + t) hρ (by omega) s hs
    · have heq : cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
          [.node Wc Wc_pos (cxNodeOps ρ (mH ^ k) j0 cdat
            (fun t => cCoreProc A K D S rr ρ kLeaf cdat k (j0 + t * mH ^ k)))] := by
        rw [cCoreProc]
        exact if_neg hleaf
      rw [heq]
      intro o ho
      have ho' : o = .node Wc Wc_pos (cxNodeOps ρ (mH ^ k) j0 cdat
          (fun t => cCoreProc A K D S rr ρ kLeaf cdat k (j0 + t * mH ^ k))) := List.mem_singleton.mp ho
      subst ho'
      refine chgOK_cxNodeOps P ρ (mH ^ k) j0 cdat _ (ChargeOK (ptG (rr := rr) P) cs2 gateCharge k)
        hval (fun t ht => ih (j0 + t * mH ^ k) ?_)
      have h1 : (t + 1) * mH ^ k ≤ mH * mH ^ k := Nat.mul_le_mul_right _ ht
      have h2 : (t + 1) * mH ^ k = t * mH ^ k + mH ^ k := Nat.succ_mul t (mH ^ k)
      have h3 : mH ^ (k + 1) = mH * mH ^ k := pow_succ' mH k
      omega

end SubNLogN.Math.Networks.LayerGuardCore
