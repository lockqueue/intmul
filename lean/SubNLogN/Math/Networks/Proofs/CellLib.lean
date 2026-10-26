import SubNLogN.Math.Networks.Labels
import SubNLogN.Math.Networks.BitFrames

/-!
# Generic tensor-cell library ([OAI26, §3.3, Lemma 6], cell calculus)

Generic linear algebra behind [OAI26, §3.3, Lemma 6] and the name-level cell calculus of
`CellCalc.lean`. Nothing here is specific to `h = 100` or to a network.

## Plan
* **Part A (any f.d. space `V`).** `IsOrthDecomp β s W`: `β` symmetric and nondegenerate, the
  pieces `W i` (`i ∈ s`, a `Finset`) pairwise `β`-orthogonal and spanning `V`. For `S ⊆ s` write
  `⨆ S = ⨆ i ∈ S, W i`. Then `β.orthogonal (⨆ S) = ⨆ (s \ S)`, `IsCompl (⨆ S) (β.orthogonal (⨆ S))`,
  `(⨆ S) ⊓ (⨆ T) = ⨆ (S ∩ T)`, `(⨆ S) ≤ (⨆ T) ↔ ∀ i ∈ S, i ∉ T → W i = ⊥`,
  `finrank (⨆ S) = Σ_{i ∈ S} finrank (W i)`, `projAlong β (⨆ S) = Σ_{i ∈ S} projAlong β (W i)`,
  `rank (Σ_i c_i P_i) = Σ_{c_i ≠ 0} finrank (W i)`, and `residual β (⨆ S) (⨆ T)` is the sum of the
  difference pieces. Proofs: split `x = u + u'` along `⨆ S ⊔ ⨆ (s \ S) = ⊤`; nondegeneracy kills a
  vector orthogonal to both parts; finrank by `Finset` induction (`finrank_sup_add_finrank_inf_eq`);
  linear maps are compared piece by piece (`eqLocus`).
* **Part B (cube `[h]³`).** `tspan A B C = span {pure3 u v w | u ∈ A, v ∈ B, w ∈ C}` (so
  `summandSub β σ = tspan (tokSub β σ.1) (tokSub β σ.2.1) (tokSub β σ.2.2)` by `rfl`).
  `tspan` is monotone and additive in each factor (`Finset` sups), `tspan ⊤ ⊤ ⊤ = ⊤` (delta
  functions are pure tensors), `tspan` of spans is the span of the pure tensors of generators, and
  `finrank (tspan A B C) = finrank A * finrank B * finrank C` (bases of the factors give a linearly
  independent family of pure tensors, by slicing one coordinate at a time).
  `toBilin' (kron3 G₁ G₂ G₃) (pure3 u v w) (pure3 u' v' w') = Π_k toBilin' G_k (·) (·)`; hence the
  cells `tspan (A₁ a) (A₂ b) (A₃ c)` of three factor decompositions form an `IsOrthDecomp` of the
  cube space (`IsOrthDecomp.tensor`). `kron3 G G G` is symmetric / nondegenerate when `G` is.
-/

namespace SubNLogN.Math.Networks.CellLib

open Module

variable {K : Type*} [Field K]

/-! ## Part A: orthogonal decompositions -/

section Generic

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- An orthogonal decomposition of `V` for the symmetric nondegenerate form `β`: the pieces
`W i`, `i ∈ s`, are pairwise `β`-orthogonal and span `V`. -/
structure IsOrthDecomp {ι : Type*} (β : LinearMap.BilinForm K V) (s : Finset ι)
    (W : ι → Submodule K V) : Prop where
  symm : ∀ x y, β x y = β y x
  nondeg : ∀ x, (∀ y, β x y = 0) → x = 0
  orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, β x y = 0
  top : (⨆ i ∈ s, W i) = ⊤

variable {β : LinearMap.BilinForm K V} {ι : Type*} {s : Finset ι} {W : ι → Submodule K V}

theorem biSup_mono_finset {S T : Finset ι} (hST : S ⊆ T) : (⨆ i ∈ S, W i) ≤ ⨆ i ∈ T, W i :=
  biSup_mono fun _ hi => hST hi

theorem piece_le_biSup {S : Finset ι} {i : ι} (hi : i ∈ S) : W i ≤ ⨆ j ∈ S, W j :=
  le_iSup₂ (f := fun j (_ : j ∈ S) => W j) i hi

theorem projAlong_bot : projAlong β (⊥ : Submodule K V) = 0 := by
  unfold projAlong
  split_ifs with hU
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact (Submodule.mem_bot K).mp (Submodule.projection_apply_mem hU x)
  · rfl

namespace IsOrthDecomp

variable (hD : IsOrthDecomp β s W)
include hD

theorem isRefl : β.IsRefl := fun x y hxy => (hD.symm y x).trans hxy

theorem nondegenerate : β.Nondegenerate :=
  ⟨hD.nondeg, fun y hy => hD.nondeg y fun x => (hD.symm y x).trans (hy x)⟩

theorem piece_le_orthogonal {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    W i ≤ β.orthogonal (W j) := fun x hx =>
  LinearMap.BilinForm.mem_orthogonal_iff.mpr fun y hy =>
    hD.orth j hj i hi (Ne.symm hij) y hy x hx

theorem le_orthogonal_symm {M N : Submodule K V} (hle : M ≤ β.orthogonal N) :
    N ≤ β.orthogonal M := fun x hx =>
  LinearMap.BilinForm.mem_orthogonal_iff.mpr fun y hy =>
    (hD.symm y x).trans (LinearMap.BilinForm.mem_orthogonal_iff.mp (hle hy) x hx)

theorem le_orthogonal_biSup {S T : Finset ι} (hS : S ⊆ s) (hT : T ⊆ s) (hST : Disjoint S T) :
    (⨆ i ∈ S, W i) ≤ β.orthogonal (⨆ i ∈ T, W i) := by
  refine iSup₂_le fun i hi => hD.le_orthogonal_symm (iSup₂_le fun j hj => ?_)
  exact hD.piece_le_orthogonal (hT hj) (hS hi) fun hji =>
    Finset.disjoint_left.mp hST hi (hji ▸ hj)

theorem eq_zero_of_mem_orthogonal {M N : Submodule K V} (hMN : M ⊔ N = ⊤) {x : V}
    (hxM : x ∈ β.orthogonal M) (hxN : x ∈ β.orthogonal N) : x = 0 := by
  refine hD.nondeg x fun y => ?_
  have hy : y ∈ M ⊔ N := by rw [hMN]; exact Submodule.mem_top
  obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, hD.symm x m, hD.symm x n, LinearMap.BilinForm.mem_orthogonal_iff.mp hxM m hm,
    LinearMap.BilinForm.mem_orthogonal_iff.mp hxN n hn, add_zero]

variable [DecidableEq ι]

theorem sup_eq_top {S : Finset ι} (hS : S ⊆ s) : (⨆ i ∈ S, W i) ⊔ (⨆ i ∈ s \ S, W i) = ⊤ := by
  rw [← Finset.iSup_union, Finset.union_sdiff_of_subset hS, hD.top]

theorem orthogonal_biSup {S : Finset ι} (hS : S ⊆ s) :
    β.orthogonal (⨆ i ∈ S, W i) = ⨆ i ∈ s \ S, W i := by
  have hSc : s \ S ⊆ s := Finset.sdiff_subset
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (⨆ i ∈ S, W i) ⊔ (⨆ i ∈ s \ S, W i) := by
      rw [hD.sup_eq_top hS]; exact Submodule.mem_top
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hx'
    have hu'o : u' ∈ β.orthogonal (⨆ i ∈ S, W i) :=
      hD.le_orthogonal_biSup hSc hS disjoint_sdiff_self_left hu'
    have huo : u ∈ β.orthogonal (⨆ i ∈ S, W i) := by
      simpa using Submodule.sub_mem _ hx hu'o
    have huo' : u ∈ β.orthogonal (⨆ i ∈ s \ S, W i) :=
      hD.le_orthogonal_biSup hS hSc disjoint_sdiff_self_right hu
    rw [hD.eq_zero_of_mem_orthogonal (hD.sup_eq_top hS) huo huo', zero_add]
    exact hu'
  · exact hD.le_orthogonal_biSup hSc hS disjoint_sdiff_self_left

theorem isCompl {S : Finset ι} (hS : S ⊆ s) :
    IsCompl (⨆ i ∈ S, W i) (β.orthogonal (⨆ i ∈ S, W i)) := by
  have hSc : s \ S ⊆ s := Finset.sdiff_subset
  rw [hD.orthogonal_biSup hS]
  refine ⟨Submodule.disjoint_def.mpr fun x hx1 hx2 => ?_, codisjoint_iff.mpr (hD.sup_eq_top hS)⟩
  exact hD.eq_zero_of_mem_orthogonal (hD.sup_eq_top hS)
    (hD.le_orthogonal_biSup hSc hS disjoint_sdiff_self_left hx2)
    (hD.le_orthogonal_biSup hS hSc disjoint_sdiff_self_right hx1)

theorem isCompl_piece {i : ι} (hi : i ∈ s) : IsCompl (W i) (β.orthogonal (W i)) := by
  have h := hD.isCompl (S := {i}) (Finset.singleton_subset_iff.mpr hi)
  simpa using h

theorem biSup_inf_biSup {S T : Finset ι} (hS : S ⊆ s) (hT : T ⊆ s) :
    (⨆ i ∈ S, W i) ⊓ (⨆ i ∈ T, W i) = ⨆ i ∈ S ∩ T, W i := by
  apply le_antisymm
  · rintro x ⟨hxS, hxT⟩
    have hsplit : (⨆ i ∈ S, W i) = (⨆ i ∈ S ∩ T, W i) ⊔ (⨆ i ∈ S \ T, W i) := by
      rw [← Finset.iSup_union, Finset.union_comm, Finset.sdiff_union_inter]
    rw [hsplit] at hxS
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxS
    have hzT : z ∈ ⨆ i ∈ T, W i := by
      simpa using Submodule.sub_mem _ hxT (biSup_mono_finset Finset.inter_subset_right hy)
    have hzO : z ∈ β.orthogonal (⨆ i ∈ T, W i) :=
      hD.le_orthogonal_biSup (Finset.sdiff_subset.trans hS) hT disjoint_sdiff_self_left hz
    rw [Submodule.disjoint_def.mp (hD.isCompl hT).disjoint z hzT hzO, add_zero]
    exact hy
  · exact le_inf (biSup_mono_finset Finset.inter_subset_left)
      (biSup_mono_finset Finset.inter_subset_right)

theorem inf_orthogonal {S T : Finset ι} (hS : S ⊆ s) (hT : T ⊆ s) :
    (⨆ i ∈ T, W i) ⊓ β.orthogonal (⨆ i ∈ S, W i) = ⨆ i ∈ T \ S, W i := by
  rw [hD.orthogonal_biSup hS, hD.biSup_inf_biSup hT Finset.sdiff_subset]
  have hTS : T ∩ (s \ S) = T \ S := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hT h.1, h.2⟩⟩
  rw [hTS]

theorem biSup_le_biSup_iff {S T : Finset ι} (hS : S ⊆ s) (hT : T ⊆ s) :
    (⨆ i ∈ S, W i) ≤ (⨆ i ∈ T, W i) ↔ ∀ i ∈ S, i ∉ T → W i = ⊥ := by
  constructor
  · intro hle i hiS hiT
    have h1 : W i ≤ ⨆ j ∈ T, W j := (piece_le_biSup hiS).trans hle
    have h2 : (⨆ j ∈ T, W j) ≤ β.orthogonal (W i) := by
      have := hD.le_orthogonal_biSup hT (Finset.singleton_subset_iff.mpr (hS hiS))
        (Finset.disjoint_singleton_right.mpr hiT)
      simpa using this
    exact (hD.isCompl_piece (hS hiS)).disjoint.eq_bot_of_le (h1.trans h2)
  · intro hW
    refine iSup₂_le fun i hi => ?_
    by_cases hiT : i ∈ T
    · exact piece_le_biSup hiT
    · rw [hW i hi hiT]; exact bot_le

theorem residual_of_subset {S T : Finset ι} (hS : S ⊆ s) (hT : T ⊆ s) (hST : S ⊆ T) :
    residual β (⨆ i ∈ S, W i) (⨆ i ∈ T, W i) = ⨆ i ∈ T \ S, W i := by
  rw [residual, if_pos (biSup_mono_finset hST)]
  exact hD.inf_orthogonal hS hT

theorem residual_of_not_le {S T : Finset ι} (hS : S ⊆ s) (hT : T ⊆ s)
    (hle : ¬ (⨆ i ∈ S, W i) ≤ (⨆ i ∈ T, W i)) :
    residual β (⨆ i ∈ S, W i) (⨆ i ∈ T, W i) = ⨆ i ∈ S \ T, W i := by
  rw [residual, if_neg hle]
  exact hD.inf_orthogonal hT hS

theorem projAlong_apply_of_mem {S : Finset ι} (hS : S ⊆ s) {j : ι} (hj : j ∈ s) {x : V}
    (hx : x ∈ W j) : projAlong β (⨆ i ∈ S, W i) x = if j ∈ S then x else 0 := by
  rw [projAlong, dif_pos (hD.isCompl hS)]
  split_ifs with hjS
  · exact Submodule.projection_apply_of_mem_left _ (piece_le_biSup hjS hx)
  · refine (Submodule.projection_apply_eq_zero_iff _).mpr ?_
    rw [hD.orthogonal_biSup hS]
    exact piece_le_biSup (Finset.mem_sdiff.mpr ⟨hj, hjS⟩) hx

theorem projAlong_piece_apply_of_mem {i j : ι} (hi : i ∈ s) (hj : j ∈ s) {x : V} (hx : x ∈ W j) :
    projAlong β (W i) x = if i = j then x else 0 := by
  have h := hD.projAlong_apply_of_mem (Finset.singleton_subset_iff.mpr hi) hj hx
  have h1 : (⨆ k ∈ ({i} : Finset ι), W k) = W i := by simp
  rw [h1] at h
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

omit [DecidableEq ι] in
theorem ext_of_pieces {V' : Type*} [AddCommGroup V'] [Module K V'] {f g : V →ₗ[K] V'}
    (hfg : ∀ i ∈ s, ∀ x ∈ W i, f x = g x) : f = g := by
  have hle : (⨆ i ∈ s, W i) ≤ LinearMap.eqLocus f g :=
    iSup₂_le fun i hi x hx => LinearMap.mem_eqLocus.mpr (hfg i hi x hx)
  rw [hD.top] at hle
  exact LinearMap.eqLocus_eq_top.mp (eq_top_iff.mpr hle)

theorem projAlong_biSup {S : Finset ι} (hS : S ⊆ s) :
    projAlong β (⨆ i ∈ S, W i) = ∑ i ∈ S, projAlong β (W i) := by
  refine hD.ext_of_pieces fun j hj x hx => ?_
  rw [hD.projAlong_apply_of_mem hS hj hx, LinearMap.sum_apply,
    Finset.sum_congr rfl fun i hi => hD.projAlong_piece_apply_of_mem (hS hi) hj hx,
    Finset.sum_ite_eq']

theorem projAlong_mem {i : ι} (hi : i ∈ s) (x : V) : projAlong β (W i) x ∈ W i := by
  rw [projAlong, dif_pos (hD.isCompl_piece hi)]
  exact Submodule.projection_apply_mem _ x

theorem range_sum_of_subset [DecidableEq K] {S : Finset ι} (hS : S ⊆ s) (c : ι → K) :
    LinearMap.range (∑ i ∈ S, c i • projAlong β (W i)) =
      ⨆ i ∈ S.filter (fun i => c i ≠ 0), W i := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [LinearMap.smul_apply]
    by_cases hci : c i = 0
    · rw [hci, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _
        (piece_le_biSup (Finset.mem_filter.mpr ⟨hi, hci⟩) (hD.projAlong_mem (hS hi) x))
  · refine iSup₂_le fun i hi y hy => ?_
    obtain ⟨hiS, hci⟩ := Finset.mem_filter.mp hi
    refine ⟨(c i)⁻¹ • y, ?_⟩
    have hsum : ∀ k ∈ S, (c k • projAlong β (W k)) y = if k = i then c k • y else 0 := by
      intro k hk
      rw [LinearMap.smul_apply, hD.projAlong_piece_apply_of_mem (hS hk) (hS hiS) hy]
      split_ifs <;> simp
    rw [map_smul, LinearMap.sum_apply, Finset.sum_congr rfl hsum, Finset.sum_ite_eq', if_pos hiS,
      smul_smul, inv_mul_cancel₀ hci, one_smul]

variable [FiniteDimensional K V]

theorem finrank_biSup {S : Finset ι} (hS : S ⊆ s) :
    finrank K ↥(⨆ i ∈ S, W i) = ∑ i ∈ S, finrank K ↥(W i) := by
  revert hS
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert a S ha ih =>
    intro hS
    have hS' : S ⊆ s := (Finset.subset_insert a S).trans hS
    have haS : a ∈ s := hS (Finset.mem_insert_self a S)
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih hS']
    have hdisj : W a ⊓ (⨆ i ∈ S, W i) = ⊥ := by
      have h1 : (⨆ i ∈ S, W i) ≤ β.orthogonal (W a) := by
        have := hD.le_orthogonal_biSup hS' (Finset.singleton_subset_iff.mpr haS)
          (Finset.disjoint_singleton_right.mpr ha)
        simpa using this
      exact disjoint_iff.mp ((hD.isCompl_piece haS).disjoint.mono_right h1)
    have := Submodule.finrank_sup_add_finrank_inf_eq (W a) (⨆ i ∈ S, W i)
    rw [hdisj, finrank_bot, add_zero] at this
    exact this

theorem finrank_range_sum_of_subset [DecidableEq K] {S : Finset ι} (hS : S ⊆ s) (c : ι → K) :
    finrank K ↥(LinearMap.range (∑ i ∈ S, c i • projAlong β (W i))) =
      ∑ i ∈ S with c i ≠ 0, finrank K ↥(W i) := by
  rw [hD.range_sum_of_subset hS c, hD.finrank_biSup ((Finset.filter_subset _ _).trans hS)]

theorem finrank_range_sum [DecidableEq K] (c : ι → K) :
    finrank K ↥(LinearMap.range (∑ i ∈ s, c i • projAlong β (W i))) =
      ∑ i ∈ s with c i ≠ 0, finrank K ↥(W i) :=
  hD.finrank_range_sum_of_subset (Finset.Subset.refl s) c

theorem finrank_range_smul_sub [DecidableEq K] {S T : Finset ι} (hS : S ⊆ s) (hT : T ⊆ s)
    (a b : K) :
    finrank K ↥(LinearMap.range (a • projAlong β (⨆ i ∈ S, W i) - b • projAlong β (⨆ i ∈ T, W i))) =
      ∑ i ∈ S ∪ T with a * (if i ∈ S then 1 else 0) - b * (if i ∈ T then 1 else 0) ≠ 0,
        finrank K ↥(W i) := by
  have hST : S ∪ T ⊆ s := Finset.union_subset hS hT
  have key : a • projAlong β (⨆ i ∈ S, W i) - b • projAlong β (⨆ i ∈ T, W i) =
      ∑ i ∈ S ∪ T, (a * (if i ∈ S then 1 else 0) - b * (if i ∈ T then 1 else 0)) •
        projAlong β (W i) := by
    refine hD.ext_of_pieces fun j hj x hx => ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      hD.projAlong_apply_of_mem hS hj hx, hD.projAlong_apply_of_mem hT hj hx, LinearMap.sum_apply]
    have hsum : ∀ k ∈ S ∪ T,
        ((a * (if k ∈ S then 1 else 0) - b * (if k ∈ T then 1 else 0)) • projAlong β (W k)) x =
          if k = j then (a * (if k ∈ S then 1 else 0) - b * (if k ∈ T then 1 else 0)) • x
          else 0 := by
      intro k hk
      rw [LinearMap.smul_apply, hD.projAlong_piece_apply_of_mem (hST hk) hj hx]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hsum, Finset.sum_ite_eq']
    by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;> simp [hjS, hjT, sub_smul]
  rw [key]
  exact hD.finrank_range_sum_of_subset hST _

end IsOrthDecomp

end Generic

/-! ## Part B: tensor spans in `K^{[h]³}` -/

section Cube

variable {h : ℕ}

/-- The tensor span `A ⊗ B ⊗ C ⊂ K^{[h]³}`: the span of the pure tensors `pure3 u v w`. -/
def tspan (A B C : Submodule K (Fin h → K)) : Submodule K (Cube h → K) :=
  Submodule.span K {x | ∃ u ∈ A, ∃ v ∈ B, ∃ w ∈ C, x = pure3 u v w}

theorem summandSub_eq_tspan (β : LinearMap.BilinForm K (Fin h → K)) (σ : Summand h) :
    summandSub β σ = tspan (tokSub β σ.1) (tokSub β σ.2.1) (tokSub β σ.2.2) := rfl

theorem labelSub_nil (β : LinearMap.BilinForm K (Fin h → K)) :
    labelSub β ([] : SymLabel h) = ⊥ := rfl

theorem labelSub_cons (β : LinearMap.BilinForm K (Fin h → K)) (σ : Summand h) (L : SymLabel h) :
    labelSub β (σ :: L) = summandSub β σ ⊔ labelSub β L := rfl

theorem labelSub_append (β : LinearMap.BilinForm K (Fin h → K)) (L L' : SymLabel h) :
    labelSub β (L ++ L') = labelSub β L ⊔ labelSub β L' := by
  induction L with
  | nil => simp [labelSub_nil]
  | cons σ L ih => rw [List.cons_append, labelSub_cons, labelSub_cons, ih, sup_assoc]

theorem labelSub_eq_biSup (β : LinearMap.BilinForm K (Fin h → K)) (L : SymLabel h) :
    labelSub β L = ⨆ σ ∈ L.toFinset, summandSub β σ := by
  induction L with
  | nil => simp [labelSub_nil]
  | cons σ L ih => rw [labelSub_cons, ih, List.toFinset_cons, Finset.iSup_insert]

/-! ### Multilinearity of `pure3` -/

theorem pure3_add_left (u u' v w : Fin h → K) :
    pure3 (u + u') v w = pure3 u v w + pure3 u' v w := by
  funext p; simp only [pure3, Pi.add_apply]; ring
theorem pure3_add_mid (u v v' w : Fin h → K) :
    pure3 u (v + v') w = pure3 u v w + pure3 u v' w := by
  funext p; simp only [pure3, Pi.add_apply]; ring
theorem pure3_add_right (u v w w' : Fin h → K) :
    pure3 u v (w + w') = pure3 u v w + pure3 u v w' := by
  funext p; simp only [pure3, Pi.add_apply]; ring
theorem pure3_smul_left (a : K) (u v w : Fin h → K) : pure3 (a • u) v w = a • pure3 u v w := by
  funext p; simp only [pure3, Pi.smul_apply, smul_eq_mul]; ring
theorem pure3_smul_mid (a : K) (u v w : Fin h → K) : pure3 u (a • v) w = a • pure3 u v w := by
  funext p; simp only [pure3, Pi.smul_apply, smul_eq_mul]; ring
theorem pure3_smul_right (a : K) (u v w : Fin h → K) : pure3 u v (a • w) = a • pure3 u v w := by
  funext p; simp only [pure3, Pi.smul_apply, smul_eq_mul]; ring
theorem pure3_zero_left (v w : Fin h → K) : pure3 (0 : Fin h → K) v w = 0 := by
  funext p; simp [pure3]
theorem pure3_zero_mid (u w : Fin h → K) : pure3 u (0 : Fin h → K) w = 0 := by
  funext p; simp [pure3]
theorem pure3_zero_right (u v : Fin h → K) : pure3 u v (0 : Fin h → K) = 0 := by
  funext p; simp [pure3]

/-- `u ↦ pure3 u v w` as a linear map. -/
def pure3L₁ (v w : Fin h → K) : (Fin h → K) →ₗ[K] (Cube h → K) where
  toFun u := pure3 u v w
  map_add' u u' := pure3_add_left u u' v w
  map_smul' a u := pure3_smul_left a u v w

/-- `v ↦ pure3 u v w` as a linear map. -/
def pure3L₂ (u w : Fin h → K) : (Fin h → K) →ₗ[K] (Cube h → K) where
  toFun v := pure3 u v w
  map_add' v v' := pure3_add_mid u v v' w
  map_smul' a v := pure3_smul_mid a u v w

/-- `w ↦ pure3 u v w` as a linear map. -/
def pure3L₃ (u v : Fin h → K) : (Fin h → K) →ₗ[K] (Cube h → K) where
  toFun w := pure3 u v w
  map_add' w w' := pure3_add_right u v w w'
  map_smul' a w := pure3_smul_right a u v w

/-! ### Lattice properties of `tspan` -/

theorem pure3_mem_tspan {A B C : Submodule K (Fin h → K)} {u v w : Fin h → K} (hu : u ∈ A)
    (hv : v ∈ B) (hw : w ∈ C) : pure3 u v w ∈ tspan A B C :=
  Submodule.subset_span ⟨u, hu, v, hv, w, hw, rfl⟩

theorem tspan_le_iff {A B C : Submodule K (Fin h → K)} {P : Submodule K (Cube h → K)} :
    tspan A B C ≤ P ↔ ∀ u ∈ A, ∀ v ∈ B, ∀ w ∈ C, pure3 u v w ∈ P := by
  constructor
  · intro hle u hu v hv w hw
    exact hle (pure3_mem_tspan hu hv hw)
  · intro H
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu, v, hv, w, hw, rfl⟩
    exact H u hu v hv w hw

theorem tspan_mono {A B C A' B' C' : Submodule K (Fin h → K)} (hA : A ≤ A') (hB : B ≤ B')
    (hC : C ≤ C') : tspan A B C ≤ tspan A' B' C' :=
  tspan_le_iff.mpr fun _ hu _ hv _ hw => pure3_mem_tspan (hA hu) (hB hv) (hC hw)

theorem tspan_sup_left (A A' B C : Submodule K (Fin h → K)) :
    tspan (A ⊔ A') B C = tspan A B C ⊔ tspan A' B C := by
  refine le_antisymm (tspan_le_iff.mpr fun u hu v hv w hw => ?_)
    (sup_le (tspan_mono le_sup_left le_rfl le_rfl) (tspan_mono le_sup_right le_rfl le_rfl))
  obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hu
  rw [pure3_add_left]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (pure3_mem_tspan ha hv hw))
    (Submodule.mem_sup_right (pure3_mem_tspan ha' hv hw))

theorem tspan_sup_mid (A B B' C : Submodule K (Fin h → K)) :
    tspan A (B ⊔ B') C = tspan A B C ⊔ tspan A B' C := by
  refine le_antisymm (tspan_le_iff.mpr fun u hu v hv w hw => ?_)
    (sup_le (tspan_mono le_rfl le_sup_left le_rfl) (tspan_mono le_rfl le_sup_right le_rfl))
  obtain ⟨b, hb, b', hb', rfl⟩ := Submodule.mem_sup.mp hv
  rw [pure3_add_mid]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (pure3_mem_tspan hu hb hw))
    (Submodule.mem_sup_right (pure3_mem_tspan hu hb' hw))

theorem tspan_sup_right (A B C C' : Submodule K (Fin h → K)) :
    tspan A B (C ⊔ C') = tspan A B C ⊔ tspan A B C' := by
  refine le_antisymm (tspan_le_iff.mpr fun u hu v hv w hw => ?_)
    (sup_le (tspan_mono le_rfl le_rfl le_sup_left) (tspan_mono le_rfl le_rfl le_sup_right))
  obtain ⟨c, hc, c', hc', rfl⟩ := Submodule.mem_sup.mp hw
  rw [pure3_add_right]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (pure3_mem_tspan hu hv hc))
    (Submodule.mem_sup_right (pure3_mem_tspan hu hv hc'))

theorem tspan_bot_left (B C : Submodule K (Fin h → K)) : tspan ⊥ B C = ⊥ :=
  eq_bot_iff.mpr (tspan_le_iff.mpr fun u hu v _ w _ => by
    rw [(Submodule.mem_bot K).mp hu, pure3_zero_left]; exact Submodule.zero_mem _)
theorem tspan_bot_mid (A C : Submodule K (Fin h → K)) : tspan A ⊥ C = ⊥ :=
  eq_bot_iff.mpr (tspan_le_iff.mpr fun u _ v hv w _ => by
    rw [(Submodule.mem_bot K).mp hv, pure3_zero_mid]; exact Submodule.zero_mem _)
theorem tspan_bot_right (A B : Submodule K (Fin h → K)) : tspan A B ⊥ = ⊥ :=
  eq_bot_iff.mpr (tspan_le_iff.mpr fun u _ v _ w hw => by
    rw [(Submodule.mem_bot K).mp hw, pure3_zero_right]; exact Submodule.zero_mem _)

theorem tspan_biSup_left {α : Type*} (s : Finset α) (A : α → Submodule K (Fin h → K))
    (B C : Submodule K (Fin h → K)) : tspan (⨆ a ∈ s, A a) B C = ⨆ a ∈ s, tspan (A a) B C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tspan_bot_left]
  | insert a s ha ih => rw [Finset.iSup_insert, Finset.iSup_insert, tspan_sup_left, ih]

theorem tspan_biSup_mid {α : Type*} (s : Finset α) (A : Submodule K (Fin h → K))
    (B : α → Submodule K (Fin h → K)) (C : Submodule K (Fin h → K)) :
    tspan A (⨆ b ∈ s, B b) C = ⨆ b ∈ s, tspan A (B b) C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tspan_bot_mid]
  | insert a s ha ih => rw [Finset.iSup_insert, Finset.iSup_insert, tspan_sup_mid, ih]

theorem tspan_biSup_right {α : Type*} (s : Finset α) (A B : Submodule K (Fin h → K))
    (C : α → Submodule K (Fin h → K)) : tspan A B (⨆ c ∈ s, C c) = ⨆ c ∈ s, tspan A B (C c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tspan_bot_right]
  | insert a s ha ih => rw [Finset.iSup_insert, Finset.iSup_insert, tspan_sup_right, ih]

theorem tspan_biSup {α₁ α₂ α₃ : Type*} (A : α₁ → Submodule K (Fin h → K))
    (B : α₂ → Submodule K (Fin h → K)) (C : α₃ → Submodule K (Fin h → K))
    (s₁ : Finset α₁) (s₂ : Finset α₂) (s₃ : Finset α₃) :
    tspan (⨆ i ∈ s₁, A i) (⨆ j ∈ s₂, B j) (⨆ k ∈ s₃, C k) =
      ⨆ c ∈ s₁ ×ˢ s₂ ×ˢ s₃, tspan (A c.1) (B c.2.1) (C c.2.2) := by
  rw [tspan_biSup_left]
  simp_rw [tspan_biSup_mid, tspan_biSup_right]
  apply le_antisymm
  · refine iSup₂_le fun i hi => iSup₂_le fun j hj => iSup₂_le fun k hk => ?_
    exact le_iSup₂ (f := fun c (_ : c ∈ s₁ ×ˢ s₂ ×ˢ s₃) => tspan (A c.1) (B c.2.1) (C c.2.2))
      (i, j, k) (Finset.mem_product.mpr ⟨hi, Finset.mem_product.mpr ⟨hj, hk⟩⟩)
  · refine iSup₂_le fun c hc => ?_
    obtain ⟨h1, h23⟩ := Finset.mem_product.mp hc
    obtain ⟨h2, h3⟩ := Finset.mem_product.mp h23
    refine le_trans ?_ (le_iSup₂ (f := fun i (_ : i ∈ s₁) =>
      ⨆ j ∈ s₂, ⨆ k ∈ s₃, tspan (A i) (B j) (C k)) c.1 h1)
    refine le_trans ?_ (le_iSup₂ (f := fun j (_ : j ∈ s₂) =>
      ⨆ k ∈ s₃, tspan (A c.1) (B j) (C k)) c.2.1 h2)
    exact le_iSup₂ (f := fun k (_ : k ∈ s₃) => tspan (A c.1) (B c.2.1) (C k)) c.2.2 h3

theorem tspan_top : tspan (⊤ : Submodule K (Fin h → K)) ⊤ ⊤ = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
  have hp : (fun q : Cube h => if p = q then (1 : K) else 0) =
      pure3 (fun j => if p.1 = j then 1 else 0) (fun j => if p.2.1 = j then 1 else 0)
        (fun j => if p.2.2 = j then 1 else 0) := by
    funext q
    obtain ⟨p1, p2, p3⟩ := p
    obtain ⟨q1, q2, q3⟩ := q
    simp only [pure3, Prod.mk.injEq]
    by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> by_cases h3 : p3 = q3 <;> simp [h1, h2, h3]
  rw [hp]
  exact pure3_mem_tspan Submodule.mem_top Submodule.mem_top Submodule.mem_top

theorem tspan_span (s₁ s₂ s₃ : Set (Fin h → K)) :
    tspan (Submodule.span K s₁) (Submodule.span K s₂) (Submodule.span K s₃) =
      Submodule.span K {x | ∃ u ∈ s₁, ∃ v ∈ s₂, ∃ w ∈ s₃, x = pure3 u v w} := by
  set P := Submodule.span K {x | ∃ u ∈ s₁, ∃ v ∈ s₂, ∃ w ∈ s₃, x = pure3 u v w} with hP
  refine le_antisymm (tspan_le_iff.mpr fun u hu v hv w hw => ?_)
    (Submodule.span_mono fun x ⟨u, hu, v, hv, w, hw, hx⟩ =>
      ⟨u, Submodule.subset_span hu, v, Submodule.subset_span hv, w, Submodule.subset_span hw, hx⟩)
  have h0 : ∀ u ∈ s₁, ∀ v ∈ s₂, ∀ w ∈ s₃, pure3 u v w ∈ P := fun u hu v hv w hw =>
    Submodule.subset_span ⟨u, hu, v, hv, w, hw, rfl⟩
  have h1 : ∀ u ∈ Submodule.span K s₁, ∀ v ∈ s₂, ∀ w ∈ s₃, pure3 u v w ∈ P := by
    intro u hu v hv w hw
    have hle : Submodule.span K s₁ ≤ P.comap (pure3L₁ v w) :=
      Submodule.span_le.mpr fun u' hu' => h0 u' hu' v hv w hw
    exact hle hu
  have h2 : ∀ u ∈ Submodule.span K s₁, ∀ v ∈ Submodule.span K s₂, ∀ w ∈ s₃,
      pure3 u v w ∈ P := by
    intro u hu v hv w hw
    have hle : Submodule.span K s₂ ≤ P.comap (pure3L₂ u w) :=
      Submodule.span_le.mpr fun v' hv' => h1 u hu v' hv' w hw
    exact hle hv
  have hle : Submodule.span K s₃ ≤ P.comap (pure3L₃ u v) :=
    Submodule.span_le.mpr fun w' hw' => h2 u hu v hv w' hw'
  exact hle hw

/-! ### Dimension of a tensor span -/

/-- Products of linearly independent families of functions are linearly independent. -/
theorem linearIndependent_mul_prod {α β ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → α → K} {b : κ → β → K} (ha : LinearIndependent K a) (hb : LinearIndependent K b) :
    LinearIndependent K (fun p : ι × κ => fun x : α × β => a p.1 x.1 * b p.2 x.2) := by
  rw [Fintype.linearIndependent_iff] at ha hb ⊢
  intro g hg ij
  have h1 : ∀ y : β, ∀ i, ∑ j, g (i, j) * b j y = 0 := by
    intro y
    refine ha (fun i => ∑ j, g (i, j) * b j y) ?_
    funext x
    have hx := congr_fun hg (x, y)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_prod_type] at hx ⊢
    rw [← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∀ i j, g (i, j) = 0 := by
    intro i
    refine hb (fun j => g (i, j)) ?_
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h1 y i
  exact h2 ij.1 ij.2

theorem finrank_tspan (A B C : Submodule K (Fin h → K)) :
    finrank K ↥(tspan A B C) = finrank K ↥A * finrank K ↥B * finrank K ↥C := by
  have hspan : ∀ (D : Submodule K (Fin h → K)) (b : Basis (Fin (finrank K D)) K D),
      Submodule.span K (Set.range fun i => (b i : Fin h → K)) = D := by
    intro D b
    rw [show (fun i => (b i : Fin h → K)) = D.subtype ∘ b from rfl, Set.range_comp,
      Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hli : ∀ (D : Submodule K (Fin h → K)) (b : Basis (Fin (finrank K D)) K D),
      LinearIndependent K (fun i => (b i : Fin h → K)) := fun D b =>
    b.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  set bA := Module.finBasis K A
  set bB := Module.finBasis K B
  set bC := Module.finBasis K C
  set f : Fin (finrank K A) × Fin (finrank K B) × Fin (finrank K C) → (Cube h → K) :=
    fun c => pure3 (bA c.1) (bB c.2.1) (bC c.2.2) with hf_def
  have hf : LinearIndependent K f := by
    have key := linearIndependent_mul_prod (hli A bA)
      (linearIndependent_mul_prod (hli B bB) (hli C bC))
    convert key using 1
    funext c x
    simp only [hf_def, pure3]
    ring
  have hrange : Submodule.span K (Set.range f) = tspan A B C := by
    have h1 := tspan_span (Set.range fun i => (bA i : Fin h → K))
      (Set.range fun i => (bB i : Fin h → K)) (Set.range fun i => (bC i : Fin h → K))
    rw [hspan A bA, hspan B bB, hspan C bC] at h1
    rw [h1]
    congr 1
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, ⟨c.1, rfl⟩, _, ⟨c.2.1, rfl⟩, _, ⟨c.2.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
      exact ⟨(i, j, k), rfl⟩
  rw [← hrange, finrank_span_eq_card hf]
  simp [Fintype.card_prod, Fintype.card_fin, mul_assoc]

theorem tspan_eq_bot_iff (A B C : Submodule K (Fin h → K)) :
    tspan A B C = ⊥ ↔ A = ⊥ ∨ B = ⊥ ∨ C = ⊥ := by
  rw [← Submodule.finrank_eq_zero, finrank_tspan, mul_eq_zero, mul_eq_zero,
    Submodule.finrank_eq_zero, Submodule.finrank_eq_zero, Submodule.finrank_eq_zero, or_assoc]

/-! ### Labels as sums of cells -/

theorem summandSub_eq_cells {α₁ α₂ α₃ : Type*} (A₁ : α₁ → Submodule K (Fin h → K))
    (A₂ : α₂ → Submodule K (Fin h → K)) (A₃ : α₃ → Submodule K (Fin h → K))
    (β : LinearMap.BilinForm K (Fin h → K)) (σ : Summand h)
    (s₁ : Finset α₁) (s₂ : Finset α₂) (s₃ : Finset α₃)
    (h₁ : tokSub β σ.1 = ⨆ a ∈ s₁, A₁ a) (h₂ : tokSub β σ.2.1 = ⨆ b ∈ s₂, A₂ b)
    (h₃ : tokSub β σ.2.2 = ⨆ c ∈ s₃, A₃ c) :
    summandSub β σ = ⨆ x ∈ s₁ ×ˢ s₂ ×ˢ s₃, tspan (A₁ x.1) (A₂ x.2.1) (A₃ x.2.2) := by
  rw [summandSub_eq_tspan, h₁, h₂, h₃, tspan_biSup]

theorem labelSub_eq_cells {α₁ α₂ α₃ : Type*} [DecidableEq α₁] [DecidableEq α₂] [DecidableEq α₃]
    (A₁ : α₁ → Submodule K (Fin h → K)) (A₂ : α₂ → Submodule K (Fin h → K))
    (A₃ : α₃ → Submodule K (Fin h → K))
    (β : LinearMap.BilinForm K (Fin h → K)) (L : SymLabel h)
    (s : Summand h → Finset (α₁ × α₂ × α₃))
    (hs : ∀ σ ∈ L, summandSub β σ = ⨆ x ∈ s σ, tspan (A₁ x.1) (A₂ x.2.1) (A₃ x.2.2)) :
    labelSub β L = ⨆ x ∈ L.toFinset.biUnion s, tspan (A₁ x.1) (A₂ x.2.1) (A₃ x.2.2) := by
  rw [labelSub_eq_biSup, Finset.iSup_biUnion]
  exact iSup_congr fun σ => iSup_congr fun hσ => hs σ (List.mem_toFinset.mp hσ)

/-! ### Forms on the cube -/

theorem sum_cube_mul (f g k : Fin h → K) :
    ∑ p : Cube h, f p.1 * g p.2.1 * k p.2.2 = (∑ i, f i) * (∑ j, g j) * (∑ l, k l) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.mul_sum]

theorem toBilin'_kron3_pure3 (A B C : Matrix (Fin h) (Fin h) K) (u v w u' v' w' : Fin h → K) :
    Matrix.toBilin' (kron3 A B C) (pure3 u v w) (pure3 u' v' w') =
      Matrix.toBilin' A u u' * Matrix.toBilin' B v v' * Matrix.toBilin' C w w' := by
  simp only [Matrix.toBilin'_apply]
  rw [← sum_cube_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sum_cube_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [pure3, kron3]
  ring

theorem tspan_le_orthogonal {β : LinearMap.BilinForm K (Fin h → K)}
    {β3 : LinearMap.BilinForm K (Cube h → K)}
    (hβ3 : ∀ u v w u' v' w', β3 (pure3 u v w) (pure3 u' v' w') = β u u' * β v v' * β w w')
    {A B C A' B' C' : Submodule K (Fin h → K)}
    (horth : (∀ x ∈ A, ∀ y ∈ A', β y x = 0) ∨ (∀ x ∈ B, ∀ y ∈ B', β y x = 0) ∨
      (∀ x ∈ C, ∀ y ∈ C', β y x = 0)) :
    tspan A B C ≤ β3.orthogonal (tspan A' B' C') := by
  refine tspan_le_iff.mpr fun u hu v hv w hw => ?_
  have hle : tspan A' B' C' ≤ LinearMap.ker (LinearMap.flip β3 (pure3 u v w)) := by
    refine tspan_le_iff.mpr fun u' hu' v' hv' w' hw' => ?_
    rw [LinearMap.mem_ker, LinearMap.flip_apply, hβ3]
    rcases horth with h | h | h
    · rw [h u hu u' hu', zero_mul, zero_mul]
    · rw [h v hv v' hv', mul_zero, zero_mul]
    · rw [h w hw w' hw', mul_zero]
  refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => ?_
  have := hle hn
  rwa [LinearMap.mem_ker, LinearMap.flip_apply] at this

/-- The cells of three factor orthogonal decompositions form an orthogonal decomposition of the
cube space, for any cube form `β3` that is symmetric, nondegenerate and multiplicative on pure
tensors (e.g. `β3 = toBilin' (kron3 G G G)`, `β = toBilin' G`, by `toBilin'_kron3_pure3`). -/
theorem IsOrthDecomp.tensor {β : LinearMap.BilinForm K (Fin h → K)}
    {β3 : LinearMap.BilinForm K (Cube h → K)}
    (hβ3 : ∀ u v w u' v' w', β3 (pure3 u v w) (pure3 u' v' w') = β u u' * β v v' * β w w')
    (h3symm : ∀ x y, β3 x y = β3 y x) (h3nd : ∀ x, (∀ y, β3 x y = 0) → x = 0)
    {α₁ α₂ α₃ : Type*} [DecidableEq α₁] [DecidableEq α₂] [DecidableEq α₃]
    {s₁ : Finset α₁} {s₂ : Finset α₂} {s₃ : Finset α₃} {A₁ : α₁ → Submodule K (Fin h → K)}
    {A₂ : α₂ → Submodule K (Fin h → K)} {A₃ : α₃ → Submodule K (Fin h → K)}
    (h₁ : IsOrthDecomp β s₁ A₁) (h₂ : IsOrthDecomp β s₂ A₂) (h₃ : IsOrthDecomp β s₃ A₃) :
    IsOrthDecomp β3 (s₁ ×ˢ s₂ ×ˢ s₃) (fun c => tspan (A₁ c.1) (A₂ c.2.1) (A₃ c.2.2)) := by
  refine ⟨h3symm, h3nd, ?_, ?_⟩
  · rintro ⟨c1, c2, c3⟩ hc ⟨d1, d2, d3⟩ hd hcd x hx y hy
    simp only [Finset.mem_product] at hc hd
    have key : tspan (A₁ d1) (A₂ d2) (A₃ d3) ≤ β3.orthogonal (tspan (A₁ c1) (A₂ c2) (A₃ c3)) := by
      apply tspan_le_orthogonal hβ3
      by_cases e1 : c1 = d1
      · by_cases e2 : c2 = d2
        · have e3 : c3 ≠ d3 := fun e3 => hcd (by rw [e1, e2, e3])
          exact Or.inr (Or.inr fun x' hx' y' hy' => h₃.orth c3 hc.2.2 d3 hd.2.2 e3 y' hy' x' hx')
        · exact Or.inr (Or.inl fun x' hx' y' hy' => h₂.orth c2 hc.2.1 d2 hd.2.1 e2 y' hy' x' hx')
      · exact Or.inl fun x' hx' y' hy' => h₁.orth c1 hc.1 d1 hd.1 e1 y' hy' x' hx'
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp (key hy) x hx
  · show (⨆ c ∈ s₁ ×ˢ s₂ ×ˢ s₃, tspan (A₁ c.1) (A₂ c.2.1) (A₃ c.2.2)) = ⊤
    rw [← tspan_biSup, h₁.top, h₂.top, h₃.top, tspan_top]

/-! ### Kronecker cubes of factor Gram matrices -/

theorem kron3_one : kron3 (1 : Matrix (Fin h) (Fin h) K) 1 1 = 1 := by
  ext ⟨p1, p2, p3⟩ ⟨q1, q2, q3⟩
  simp only [kron3, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> by_cases h3 : p3 = q3 <;> simp [h1, h2, h3]

theorem kron3_transpose (A B C : Matrix (Fin h) (Fin h) K) :
    (kron3 A B C).transpose = kron3 A.transpose B.transpose C.transpose := by
  ext p q
  simp [kron3, Matrix.transpose_apply]

theorem kron3_isSymm {A B C : Matrix (Fin h) (Fin h) K} (hA : A.IsSymm) (hB : B.IsSymm)
    (hC : C.IsSymm) : (Matrix.toBilin' (kron3 A B C)).IsSymm := by
  refine Matrix.isSymm_toBilin'_iff_isSymm.mpr ?_
  show (kron3 A B C).transpose = kron3 A B C
  rw [kron3_transpose, hA.eq, hB.eq, hC.eq]

theorem kron3_eq_kroneckerMap (A B C : Matrix (Fin h) (Fin h) K) :
    kron3 A B C = Matrix.kroneckerMap (· * ·) A (Matrix.kroneckerMap (· * ·) B C) := by
  ext p q
  simp [kron3, Matrix.kroneckerMap_apply, mul_assoc]

theorem kron3_nondegenerate {A B C : Matrix (Fin h) (Fin h) K}
    (hA : (Matrix.toBilin' A).Nondegenerate) (hB : (Matrix.toBilin' B).Nondegenerate)
    (hC : (Matrix.toBilin' C).Nondegenerate) :
    (Matrix.toBilin' (kron3 A B C)).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero] at hA hB hC ⊢
  rw [kron3_eq_kroneckerMap, Matrix.det_kronecker, Matrix.det_kronecker]
  exact mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hB)
    (pow_ne_zero _ hC)))

end Cube

end SubNLogN.Math.Networks.CellLib
