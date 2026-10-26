import SubNLogN.Math.Networks.AppCCore
import SubNLogN.Math.Networks.Proofs.FrameInvariant
import SubNLogN.Math.Networks.Proofs.PackedProcWF

/-!
# Networks: well-formedness of the Lemma A.10 (`lem:transfer-phase`) core procedure

Proof of the structural side conditions `CCoreProcWFStmt` (`AppCCore.lean`) of the explicit Lemma A.10 (`lem:transfer-phase`)
core procedure `cCoreProc`: `cCoreProcWF_holds : CCoreProcWFStmt`, from
`CCoreWFAux.cCoreProcWF_of_packedWF : PackedProcWFStmt → CCoreProcWFStmt` and the Lemma A.9 (`lem:transfer13`)
well-formedness `packedProcWF_holds` (`Proofs/PackedProcWF.lean`).

* the individual kernels `digitGate` act on binary fields: every chunk index used is `< D`
  (`j0 + m^k ≤ D`), so the selected-bit field `selField K ρ j` lies in `[1, D K]`;
* masks `zMask`, `zSlot` (`addrMap`), phases (`recMap`) and the relabelling have no side condition;
* the gates `gateOpC` read and change only their touched roles (`FI.rowUpd_untouched`,
  `FI.rowUpd_local`);
* the packed row additions are `packedAddProc` on three distinct slots of the node, which satisfy
  `PackedHyps` (so `PackedProcWFStmt` applies);
* children: by induction on the depth; a residual orthonormal basis has at most `mH` vectors
  (orthonormal families are linearly independent), so every child `j0 + t m^k` (`t < |basis|`)
  stays inside the chunk range.

All helpers are in `SubNLogN.Math.Networks.CCoreWFAux`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace CCoreWFAux

/-! ## Arithmetic of slots and fields -/

/-- The third slot differs from both slots and is `< 3`. -/
theorem thirdSlot_spec (i j : ℕ) : thirdSlot i j ≠ i ∧ thirdSlot i j ≠ j ∧ thirdSlot i j < 3 := by
  unfold thirdSlot
  split_ifs <;> omega

/-- For slots `a < b`, the chunk of slot `a` ends before the chunk of slot `b` starts. -/
theorem slot_disj {j0 f K a b : ℕ} (hab : a < b) :
    1 + (j0 + a * f) * K + f * K ≤ 1 + (j0 + b * f) * K := by
  have h1 : (j0 + a * f) * K + f * K = (j0 + (a + 1) * f) * K := by ring
  have h2 : (a + 1) * f ≤ b * f := Nat.mul_le_mul_right f hab
  have h3 : (j0 + (a + 1) * f) * K ≤ (j0 + b * f) * K := Nat.mul_le_mul_right K (by omega)
  omega

/-- The chunk of a slot `a < mH` ends at most at field `D K` (when `j0 + mH f ≤ D`). -/
theorem slot_in_range {j0 f K a D : ℕ} (ha : a < mH) (hD : j0 + mH * f ≤ D) :
    1 + (j0 + a * f) * K + f * K ≤ D * K + 1 := by
  have h1 : (j0 + a * f) * K + f * K = (j0 + (a + 1) * f) * K := by ring
  have h2 : (a + 1) * f ≤ mH * f := Nat.mul_le_mul_right f ha
  have h3 : (j0 + (a + 1) * f) * K ≤ D * K := Nat.mul_le_mul_right K (by omega)
  omega

/-- The fields `1, …, D K` of `layerLayout` are binary. -/
theorem layer_r_eq_two {A K D S : ℕ} (i : Fin (layerLayout A K D S).n) (h1 : 1 ≤ i.val)
    (h2 : i.val ≤ D * K) : (layerLayout A K D S).r i = 2 := by
  show (if i.val = 0 then A else if i.val ≤ D * K then 2 else S) = 2
  rw [if_neg (by omega), if_pos h2]

/-- An individual kernel on the selected bit of a chunk `j < D` is well formed. -/
theorem dgate_wf {A K D S rr ρ j : ℕ} (hK : 0 < K) (hj : j < D) :
    ∀ s ∈ dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ j), Step.WF 2 s := by
  intro s hs
  unfold dgate at hs
  split_ifs at hs with hi
  · rw [List.mem_singleton] at hs
    subst hs
    have h1 : (j + 1) * K ≤ D * K := Nat.mul_le_mul_right K hj
    have h2 : (j + 1) * K = j * K + K := by ring
    show (layerLayout A K D S).r ⟨selField K ρ j, hi⟩ ≤ 2
    rw [layer_r_eq_two _ (by simp only [selField]; omega) (by simp only [selField]; omega)]
  · simp at hs

/-- `PackedHyps` for three distinct slots `a, b, c < mH` of a node at depth with `f` chunks per
slot. -/
theorem packedHyps_slots {A K D S ρ f j0 a b c : ℕ} (hK : 6 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f)
    (ha : a < mH) (hb : b < mH) (hc : c < mH) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hD : j0 + mH * f ≤ D) :
    PackedHyps (layerLayout A K D S) (f * K) K ρ f
      ⟨1 + (j0 + a * f) * K, 1 + (j0 + b * f) * K, 1 + (j0 + c * f) * K⟩ := by
  have hdisj : ∀ x y, x ≠ y → (1 + (j0 + x * f) * K + f * K ≤ 1 + (j0 + y * f) * K ∨
      1 + (j0 + y * f) * K + f * K ≤ 1 + (j0 + x * f) * K) := by
    intro x y hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact Or.inl (slot_disj h)
    · exact Or.inr (slot_disj h)
  have hra := slot_in_range (K := K) ha hD
  have hrb := slot_in_range (K := K) hb hD
  have hrc := slot_in_range (K := K) hc hD
  refine ⟨hK, rfl, hρ, hf, ?_, ?_, ?_, hdisj a b hab, hdisj a c hac, hdisj b c hbc, ?_⟩
  · show 1 + (j0 + a * f) * K + f * K ≤ D * K + 2
    omega
  · show 1 + (j0 + b * f) * K + f * K ≤ D * K + 2
    omega
  · show 1 + (j0 + c * f) * K + f * K ≤ D * K + 2
    omega
  · intro i hi
    dsimp only at hi
    apply layer_r_eq_two
    · rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    · rcases hi with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega

/-! ## Orthonormal bases have at most `mH` vectors -/

theorem dotC_comm (u v : Pt 100) : dotC u v = dotC v u := by
  unfold dotC
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem dotC_zero_left (u : Pt 100) : dotC 0 u = 0 := by
  unfold dotC
  simp

theorem dotC_sum_smul {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) (v : ι → Pt 100) (u : Pt 100) :
    dotC (∑ i ∈ s, g i • v i) u = ∑ i ∈ s, g i * dotC (v i) u := by
  unfold dotC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

/-- An orthonormal list is linearly independent. -/
theorem isONB_linearIndependent {E : Submodule (ZMod 2) (Pt 100)} {B : List (Pt 100)}
    (hB : IsONB E B) : LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i) := by
  obtain ⟨hnorm, hpair, -⟩ := hB
  have horth : ∀ i j : Fin B.length, i ≠ j → dotC (B.get i) (B.get j) = 0 := by
    intro i j hij
    have hp := List.pairwise_iff_getElem.1 hpair
    rcases lt_or_gt_of_ne hij with h | h
    · simpa [List.get_eq_getElem] using hp i.val j.val i.isLt j.isLt h
    · rw [dotC_comm]
      simpa [List.get_eq_getElem] using hp j.val i.val j.isLt i.isLt h
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have h : dotC (∑ j ∈ s, g j • B.get j) (B.get i) = dotC 0 (B.get i) :=
    congrArg (fun x => dotC x (B.get i)) hsum
  rw [dotC_sum_smul, Finset.sum_eq_single i, hnorm _ (List.get_mem _ _), mul_one,
    dotC_zero_left] at h
  · exact h
  · intro j _ hji
    rw [horth j i hji, mul_zero]
  · intro his
    exact absurd hi his

/-- An orthonormal basis of a subspace of `𝔽₂^{mH}` has at most `mH` vectors. -/
theorem isONB_length_le {E : Submodule (ZMod 2) (Pt 100)} {B : List (Pt 100)} (hB : IsONB E B) :
    B.length ≤ mH := by
  have h := (isONB_linearIndependent hB).fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h
  simpa [Cube] using h

/-! ## Gates read and change only touched roles -/

/-- On a wire touched at `(j, ι, r)`, the row depends only on the wires touched at `(j, ι, r)`. -/
theorem rowUpd_congr' {κ : Kind} {h : ℕ} {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (half : R) (j : Stage) (ι : Fix h) (r : Fin 8) (ε : R) {s s' : Role κ h → M}
    (hss : ∀ w', (gateAt j ι r w').isSome → s w' = s' w') {w : Role κ h}
    (hw : (gateAt j ι r w).isSome) :
    rowUpd κ half j ι (rowOp j r) ε s w = rowUpd κ half j ι (rowOp j r) ε s' w := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hw
  obtain ⟨-, hgs, hgi, hgt⟩ := FI.gateAt_spec hg
  refine FI.rowUpd_local half j ι r ε g s s' (fun w' hw' => hss w' ?_) w hg
  rw [FI.gateAt_of_mem hw' hgs hgi hgt]
  rfl

/-- Membership in the touched set of `gateOpC j ι r`. -/
theorem mem_touched_iff (j : Stage) (ι : Fix 100) (r : Fin 8) (k : Fin Wc) :
    k ∈ (Finset.univ.filter fun w : Role .complex 100 => (gateAt j ι r w).isSome).map
        roleIdxC.toEmbedding ↔ (gateAt j ι r (roleIdxC.symm k)).isSome := by
  rw [Finset.mem_map_equiv, Finset.mem_filter_univ]

/-- A gate whose touched set is described by a predicate `P` is well formed as soon as it reads
and changes only the roles satisfying `P`. (Stated for an abstract touched set, so that no local
hypothesis mentions membership in a concrete enumerated `Finset`.) -/
theorem gate_wf_of {L : Layout} {β : Type} {W : ℕ} {Child : Type} (cwf : Child → Prop)
    (G : (Fin W → β) → (Fin W → β)) (t : Finset (Fin W)) (P : Fin W → Prop)
    (ht : ∀ k, k ∈ t ↔ P k)
    (h1 : ∀ v v' : Fin W → β, (∀ k, P k → v k = v' k) → ∀ k, P k → G v k = G v' k)
    (h2 : ∀ (v : Fin W → β) k, ¬ P k → G v k = v k) :
    RoleOp.WF (L := L) cwf 2 (RoleOp.gate G t) := by
  refine ⟨fun v v' hvv k hk => ?_, fun v k hk => ?_⟩
  · exact h1 v v' (fun k' hk' => hvv k' ((ht k').2 hk')) k ((ht k).1 hk)
  · exact h2 v k (fun hk' => hk ((ht k).2 hk'))

/-- The gate `gateOpC j ι r` reads and changes only its touched roles. -/
theorem gateOpC_wf {A K D S rr : ℕ} {Child : Type} (cwf : Child → Prop) (j : Stage)
    (ι : Fix 100) (r : Fin 8) :
    RoleOp.WF cwf 2
      (gateOpC (A := A) (K := K) (D := D) (S := S) (rr := rr) (Child := Child) j ι r) := by
  refine gate_wf_of cwf _ _ (fun k => (gateAt j ι r (roleIdxC.symm k)).isSome)
    (mem_touched_iff j ι r) (fun v v' hvv k hk => ?_) (fun v k hk => ?_)
  · refine rowUpd_congr' (2⁻¹ : ℂ) j ι r _ (fun w' hw' => hvv _ ?_) hk
    rw [Equiv.symm_apply_apply]
    exact hw'
  · have hnone : gateAt j ι r (roleIdxC.symm k) = none := by
      cases hg : gateAt j ι r (roleIdxC.symm k) with
      | none => rfl
      | some g =>
        rw [hg] at hk
        exact absurd rfl hk
    change rowUpd _ _ _ _ _ _ (fun w => v (roleIdxC w)) (roleIdxC.symm k) = v k
    rw [FI.rowUpd_untouched _ j ι r _ _ _ hnone, Equiv.apply_symm_apply]

/-! ## Edge operations and nodes -/

/-- The operations of one edge are well formed, given Lemma A.9 (`lem:transfer13`) well-formedness for the row additions
(`hpack`: `PackedHyps` for every row-addition pair) and well-formed children (`hchild`). -/
theorem coreEdgeOps_wf {A K D S rr : ℕ} {Child : Type} (cwf : Child → Prop)
    (hP : PackedProcWFStmt) (hA : PackedAgreeStmt) (ρ f j0 : ℕ) (Dd : CxEdgeData)
    (childOf : ℕ → Child) (kidx : Fin Wc)
    (hpack : ∀ p ∈ Dd.rowsInv ++ Dd.rowsM, PackedHyps (layerLayout A K D S) (f * K) K ρ f
      ⟨1 + (j0 + p.2.val * f) * K, 1 + (j0 + p.1.val * f) * K,
        1 + (j0 + thirdSlot p.1.val p.2.val * f) * K⟩)
    (hchild : ∀ t < Dd.basis.length, cwf (childOf t)) :
    ∀ o ∈ coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 Dd childOf kidx,
      RoleOp.WF cwf 2 o := by
  intro o ho
  simp only [coreEdgeOps, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · obtain ⟨p, hp, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
    exact hP hA _ _ _ _ _ _ _ (hpack p (List.mem_append_left _ hp)) s hs
  · obtain ⟨⟨t, ε⟩, hp, ho⟩ := List.mem_flatMap.1 ho
    have ht : t < Dd.basis.length := List.mem_range.1 (List.of_mem_zip hp).1
    dsimp only at ho
    split_ifs at ho
    · rw [List.mem_singleton] at ho
      subst ho
      exact hchild t ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact trivial
      · exact hchild t ht
      · exact trivial
      · exact trivial
  · obtain ⟨p, hp, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
    exact hP hA _ _ _ _ _ _ _ (hpack p (List.mem_append_right _ hp)) s hs

/-- The operations of the edge entering a vertex are well formed. -/
theorem coreEdgeOpsAt_wf {A K D S rr : ℕ} {Child : Type} (cwf : Child → Prop) (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Child)
    (hedge : ∀ (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100),
      e ∈ edges w → ∀ o ∈ coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0
        (cdat e) childOf (roleIdxC w), RoleOp.WF cwf 2 o)
    (w : Role .complex 100) (v : Vertex .complex 100) :
    ∀ o ∈ coreEdgeOpsAt (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf w v,
      RoleOp.WF cwf 2 o := by
  intro o ho
  unfold coreEdgeOpsAt at ho
  split at ho
  · next e he => exact hedge w e (FI.edgeInto_mem he) o ho
  · simp at ho

/-- The role operations of a complex-network node are well formed. -/
theorem cxNodeOps_wf {A K D S rr : ℕ} {Child : Type} (cwf : Child → Prop) (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Child)
    (hedge : ∀ (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100),
      e ∈ edges w → ∀ o ∈ coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0
        (cdat e) childOf (roleIdxC w), RoleOp.WF cwf 2 o) :
    ∀ o ∈ cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf,
      RoleOp.WF cwf 2 o := by
  intro o ho
  unfold cxNodeOps at ho
  rcases List.mem_append.1 ho with ho | ho
  rcases List.mem_append.1 ho with ho | ho
  rcases List.mem_append.1 ho with ho | ho
  rcases List.mem_append.1 ho with ho | ho
  · -- source masks
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 ho
    exact trivial
  · -- incoming edges and gates
    obtain ⟨j, -, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨ι, -, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨r, -, ho⟩ := List.mem_flatMap.1 ho
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
      split at ho
      · exact coreEdgeOpsAt_wf cwf ρ f j0 cdat childOf hedge w _ o ho
      · simp at ho
    · rw [List.mem_singleton] at ho
      subst ho
      exact gateOpC_wf cwf j ι r
  · -- sink edges
    obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
    exact coreEdgeOpsAt_wf cwf ρ f j0 cdat childOf hedge w _ o ho
  · -- sink corrections
    obtain ⟨a, -, ho⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> exact trivial
  · -- relabelling
    rw [List.mem_singleton] at ho
    subst ho
    exact trivial

/-! ## The recursion -/

/-- Unfolding of `ProcK.WF` at depth `0`, for an abstract list (so that the kernel never compares
an `id`-wrapped concrete list with its unwrapped form, which is very slow here). -/
theorem procK_WF_zero_iff {L : Layout} {β : Type} (B : ℕ) (p : List (Step L β)) :
    ProcK.WF B 0 p ↔ ∀ s ∈ p, Step.WF B s :=
  Iff.rfl

/-- Unfolding of `ProcK.WF` at a successor depth, for an abstract list (see `procK_WF_zero_iff`). -/
theorem procK_WF_succ_iff {L : Layout} {β : Type} (B k : ℕ)
    (p : List (Model.Op L β (ProcK L β k))) :
    ProcK.WF B (k + 1) p ↔ ∀ o ∈ p, Model.Op.WF (ProcK.WF B k) B o :=
  Iff.rfl

/-- `cCoreProc` at depth `k + 1` below the leaf threshold: individual kernels. -/
theorem cCoreProc_succ_of_lt {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {k j0 : ℕ}
    (h : k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      (List.range (mH ^ (k + 1))).flatMap fun t =>
        (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ (j0 + t))).map
          Op.prim := by
  simp only [cCoreProc]
  exact if_pos h

/-- `cCoreProc` at depth `k + 1` at or above the leaf threshold: one network node. -/
theorem cCoreProc_succ_of_not_lt {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {k j0 : ℕ}
    (h : ¬ k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      [.node Wc Wc_pos (cxNodeOps ρ (mH ^ k) j0 cdat
        (fun t => cCoreProc A K D S rr ρ kLeaf cdat k (j0 + t * mH ^ k)))] := by
  simp only [cCoreProc]
  exact if_neg h

/-- Well-formedness of `cCoreProc … k j0` for every depth `k` and every start chunk `j0` with
`j0 + m^k ≤ D` (given Lemma A.9 (`lem:transfer13`) well-formedness, `K ≥ 6`, `ρ < K` and valid edge data). -/
theorem wf_main (hP : PackedProcWFStmt) (hA : PackedAgreeStmt) {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} (hK : 6 ≤ K) (hρ : ρ < K)
    (hV : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) :
    ∀ k j0, j0 + mH ^ k ≤ D → ProcK.WF 2 k (cCoreProc A K D S rr ρ kLeaf cdat k j0) := by
  intro k
  induction k with
  | zero =>
    intro j0 hD
    rw [pow_zero] at hD
    simp only [cCoreProc]
    refine (procK_WF_zero_iff 2 _).2 ?_
    intro s hs
    exact dgate_wf (by omega) (by omega) s hs
  | succ k ih =>
    intro j0 hD
    have hpow : mH ^ (k + 1) = mH * mH ^ k := pow_succ' mH k
    have hf : 1 ≤ mH ^ k := Nat.one_le_pow _ _ (by decide)
    by_cases hleaf : k + 1 < kLeaf
    · rw [cCoreProc_succ_of_lt hleaf]
      refine (procK_WF_succ_iff 2 k _).2 ?_
      intro o ho
      obtain ⟨t, ht, ho⟩ := List.mem_flatMap.1 ho
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
      have ht' := List.mem_range.1 ht
      exact dgate_wf (by omega) (by omega) s hs
    · rw [cCoreProc_succ_of_not_lt hleaf]
      refine (procK_WF_succ_iff 2 k _).2 ?_
      intro o ho
      have ho' := List.mem_singleton.1 ho
      subst ho'
      intro o ho
      refine cxNodeOps_wf (ProcK.WF 2 k) ρ (mH ^ k) j0 cdat _ ?_ o ho
      intro w e he
      obtain ⟨hONB, -, hrows, -⟩ := hV w e he
      have hlen := isONB_length_le hONB
      refine coreEdgeOps_wf (ProcK.WF 2 k) hP hA ρ (mH ^ k) j0 (cdat e) _ (roleIdxC w) ?_ ?_
      · intro p hp
        have hne : p.1 ≠ p.2 := hrows p hp
        have hne' : p.2.val ≠ p.1.val := fun h => hne (Fin.ext h.symm)
        obtain ⟨h3a, h3b, h3c⟩ := thirdSlot_spec p.1.val p.2.val
        exact packedHyps_slots hK hρ hf p.2.isLt p.1.isLt (lt_of_lt_of_le h3c (by decide)) hne'
          (Ne.symm h3b) (Ne.symm h3a) (by omega)
      · intro t ht
        apply ih
        have h1 : (t + 1) * mH ^ k ≤ mH * mH ^ k := Nat.mul_le_mul_right _ (by omega)
        have h2 : (t + 1) * mH ^ k = t * mH ^ k + mH ^ k := by ring
        omega

/-- Lemma A.10 (`lem:transfer-phase`) well-formedness from Lemma A.9 (`lem:transfer13`) well-formedness: `PackedProcWFStmt → CCoreProcWFStmt`. -/
theorem cCoreProcWF_of_packedWF (hP : PackedProcWFStmt) : CCoreProcWFStmt := by
  intro _ hA A K D S rr ρ kLeaf cdat k j0 c hH
  obtain ⟨hK, hρ, hD, -, -, hV⟩ := hH
  exact wf_main hP hA hK hρ hV k j0 hD

end CCoreWFAux

/-- CONTRACT `CCoreProcWFStmt` (Lemma A.10 (`lem:transfer-phase`) well-formedness, radix bound 2): every primitive of the Lemma A.10
core procedure satisfies its side condition. -/
theorem cCoreProcWF_holds : CCoreProcWFStmt :=
  CCoreWFAux.cCoreProcWF_of_packedWF packedProcWF_holds

end SubNLogN.Math.Networks
