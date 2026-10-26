import SubNLogN.Math.Networks.Proofs.CellLib

/-!
# Generic tensor-cell library, part 2: orthonormal lists, factor lines, and `𝔽₂` orthonormal bases

* **Part C.** Form-generic orthonormal bases (`IsONBFor β E L`: norm one, pairwise orthogonal,
  spanning `E`), their concatenation over distinct pieces of an orthogonal decomposition
  (`IsOrthDecomp.isONBFor_biSup`), and tensor products of factor orthonormal bases
  (`IsONBFor.tensor`, via a cube form multiplicative on pure tensors
  on pure tensors).
* **Part D.** One or two orthogonal anisotropic vectors: the span of a pair is complementary to
  its orthogonal complement (symmetric form), has dimension `2`, and its complement has dimension
  `dim V − 2` (`dim V − 1` for one vector), for a nondegenerate form.
* **Part E.** [OAI26, §3.3, Lemma 6] over `𝔽₂`: a subspace `E` with `E ⊓ E^⊥ = ⊥` (symmetric form)
  that is zero or contains a vector of norm one has an orthonormal basis
  (`exists_isONBFor_zmod2`; unit-line splitting and absorption of alternating planes).
-/

namespace SubNLogN.Math.Networks.CellLib

open Module

variable {K : Type*} [Field K]

/-! ## Part C: orthonormal lists (form-generic; for the binary residual bases) -/

section ONB

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `L` is an orthonormal basis of `E` for `β`: norm one, pairwise orthogonal, spanning `E`
(the form-generic version of `IsONB` in `PhaseFrames.lean`). -/
def IsONBFor (β : LinearMap.BilinForm K V) (E : Submodule K V) (L : List V) : Prop :=
  (∀ v ∈ L, β v v = 1) ∧ L.Pairwise (fun u v => β u v = 0) ∧ Submodule.span K {v | v ∈ L} = E

variable {β : LinearMap.BilinForm K V}

theorem isONBFor_nil : IsONBFor β ⊥ [] := by
  refine ⟨by simp, List.Pairwise.nil, by simp⟩

theorem isONBFor_singleton {t : V} (ht : β t t = 1) : IsONBFor β (K ∙ t) [t] := by
  refine ⟨by simpa using ht, List.pairwise_singleton _ _, by simp⟩

theorem IsONBFor.mem {E : Submodule K V} {L : List V} (hE : IsONBFor β E L) {v : V}
    (hv : v ∈ L) : v ∈ E := by
  rw [← hE.2.2]
  exact Submodule.subset_span hv

theorem IsONBFor.append {E₁ E₂ : Submodule K V} {L₁ L₂ : List V} (h₁ : IsONBFor β E₁ L₁)
    (h₂ : IsONBFor β E₂ L₂) (horth : E₂ ≤ β.orthogonal E₁) :
    IsONBFor β (E₁ ⊔ E₂) (L₁ ++ L₂) := by
  refine ⟨fun v hv => ?_, List.pairwise_append.mpr ⟨h₁.2.1, h₂.2.1, fun a ha b hb => ?_⟩, ?_⟩
  · rcases List.mem_append.mp hv with hv | hv
    · exact h₁.1 v hv
    · exact h₂.1 v hv
  · exact LinearMap.BilinForm.mem_orthogonal_iff.mp (horth (h₂.mem hb)) a (h₁.mem ha)
  · rw [← h₁.2.2, ← h₂.2.2, ← Submodule.span_union]
    congr 1
    ext v
    simp [List.mem_append]

/-- Concatenating orthonormal bases of distinct pieces of an orthogonal decomposition gives an
orthonormal basis of their sum. -/
theorem IsOrthDecomp.isONBFor_biSup_list {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {W : ι → Submodule K V} (hD : IsOrthDecomp β s W) (L : ι → List V) (l : List ι)
    (hl : l.Nodup) (hls : ∀ i ∈ l, i ∈ s) (hL : ∀ i ∈ l, IsONBFor β (W i) (L i)) :
    IsONBFor β (⨆ i ∈ l.toFinset, W i) (l.flatMap L) := by
  induction l with
  | nil => simpa using (isONBFor_nil (β := β))
  | cons i l ih =>
    rw [List.flatMap_cons, List.toFinset_cons, Finset.iSup_insert]
    have hl' := List.nodup_cons.mp hl
    have hi : i ∈ i :: l := List.mem_cons.mpr (Or.inl rfl)
    refine (hL i hi).append (ih hl'.2 (fun j hj => hls j (List.mem_cons_of_mem _ hj))
      (fun j hj => hL j (List.mem_cons_of_mem _ hj))) ?_
    have hsub : l.toFinset ⊆ s := fun j hj => hls j (List.mem_cons_of_mem _ (List.mem_toFinset.mp hj))
    have h := hD.le_orthogonal_biSup hsub (Finset.singleton_subset_iff.mpr (hls i hi))
      (Finset.disjoint_singleton_right.mpr fun hmem => hl'.1 (List.mem_toFinset.mp hmem))
    simpa using h

theorem IsOrthDecomp.isONBFor_biSup {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {W : ι → Submodule K V} (hD : IsOrthDecomp β s W) (L : ι → List V) {S : Finset ι}
    (hS : S ⊆ s) (hL : ∀ i ∈ S, IsONBFor β (W i) (L i)) :
    IsONBFor β (⨆ i ∈ S, W i) (S.toList.flatMap L) := by
  have h := hD.isONBFor_biSup_list L S.toList (Finset.nodup_toList S)
    (fun i hi => hS (Finset.mem_toList.mp hi)) (fun i hi => hL i (Finset.mem_toList.mp hi))
  rwa [Finset.toList_toFinset] at h

end ONB

section ONBCube

variable {h : ℕ}

/-- Pure tensors of orthonormal bases of the factors form an orthonormal basis of the tensor span
(for a cube form multiplicative on pure tensors). -/
theorem IsONBFor.tensor {β : LinearMap.BilinForm K (Fin h → K)}
    {β3 : LinearMap.BilinForm K (Cube h → K)}
    (hβ3 : ∀ u v w u' v' w', β3 (pure3 u v w) (pure3 u' v' w') = β u u' * β v v' * β w w')
    {A B C : Submodule K (Fin h → K)} {L₁ L₂ L₃ : List (Fin h → K)}
    (h₁ : IsONBFor β A L₁) (h₂ : IsONBFor β B L₂) (h₃ : IsONBFor β C L₃) :
    IsONBFor β3 (tspan A B C)
      (L₁.flatMap fun u => L₂.flatMap fun v => L₃.map fun w => pure3 u v w) := by
  have hmem : ∀ x, x ∈ (L₁.flatMap fun u => L₂.flatMap fun v => L₃.map fun w => pure3 u v w) ↔
      ∃ u ∈ L₁, ∃ v ∈ L₂, ∃ w ∈ L₃, x = pure3 u v w := by
    intro x
    simp only [List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨u, hu, v, hv, w, hw, rfl⟩
      exact ⟨u, hu, v, hv, w, hw, rfl⟩
    · rintro ⟨u, hu, v, hv, w, hw, rfl⟩
      exact ⟨u, hu, v, hv, w, hw, rfl⟩
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := (hmem x).mp hx
    rw [hβ3, h₁.1 u hu, h₂.1 v hv, h₃.1 w hw, one_mul, one_mul]
  · refine List.pairwise_flatMap.mpr ⟨fun u _ => List.pairwise_flatMap.mpr ⟨fun v _ => ?_, ?_⟩, ?_⟩
    · refine List.pairwise_map.mpr (h₃.2.1.imp fun hww' => ?_)
      rw [hβ3, hww', mul_zero]
    · refine h₂.2.1.imp fun hvv' => ?_
      intro x hx y hy
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨w', _, rfl⟩ := List.mem_map.mp hy
      rw [hβ3, hvv', mul_zero, zero_mul]
    · refine h₁.2.1.imp fun huu' => ?_
      intro x hx y hy
      obtain ⟨v, _, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v', _, hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨w', _, rfl⟩ := List.mem_map.mp hy
      rw [hβ3, huu', zero_mul, zero_mul]
  · have hset : {x | x ∈ (L₁.flatMap fun u => L₂.flatMap fun v => L₃.map fun w => pure3 u v w)} =
        {x | ∃ u ∈ {v | v ∈ L₁}, ∃ v ∈ {v | v ∈ L₂}, ∃ w ∈ {v | v ∈ L₃}, x = pure3 u v w} := by
      ext x
      exact hmem x
    rw [hset, ← tspan_span, h₁.2.2, h₂.2.2, h₃.2.2]

end ONBCube

/-! ## Part D: one or two orthogonal anisotropic lines and their complement -/

section Lines

variable {V : Type*} [AddCommGroup V] [Module K V] {β : LinearMap.BilinForm K V}

theorem disjoint_span_pair_orthogonal (hsymm : ∀ a b, β a b = β b a) {x y : V}
    (hx : β x x ≠ 0) (hy : β y y ≠ 0) (hxy : β x y = 0) :
    Disjoint (Submodule.span K {x, y}) (β.orthogonal (Submodule.span K {x, y})) := by
  refine Submodule.disjoint_def.mpr fun z hz hzo => ?_
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
  have h1 := LinearMap.BilinForm.mem_orthogonal_iff.mp hzo x (Submodule.subset_span (by simp))
  have h2 := LinearMap.BilinForm.mem_orthogonal_iff.mp hzo y (Submodule.subset_span (by simp))
  simp only [map_add, map_smul, smul_eq_mul] at h1 h2
  rw [hxy, mul_zero, add_zero] at h1
  rw [hsymm y x, hxy, mul_zero, zero_add] at h2
  have ha : a = 0 := (mul_eq_zero.mp h1).resolve_right hx
  have hb : b = 0 := (mul_eq_zero.mp h2).resolve_right hy
  simp [ha, hb]

theorem isCompl_span_pair_orthogonal [FiniteDimensional K V] (hsymm : ∀ a b, β a b = β b a)
    {x y : V} (hx : β x x ≠ 0) (hy : β y y ≠ 0) (hxy : β x y = 0) :
    IsCompl (Submodule.span K {x, y}) (β.orthogonal (Submodule.span K {x, y})) :=
  (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (fun a b hab => (hsymm b a).trans hab)).mpr (disjoint_span_pair_orthogonal hsymm hx hy hxy)

theorem finrank_span_pair [FiniteDimensional K V] {x y : V} (hx : β x x ≠ 0) (hy : β y y ≠ 0)
    (hxy : β x y = 0) : finrank K ↥(Submodule.span K {x, y}) = 2 := by
  have hx0 : x ≠ 0 := fun h0 => hx (by simp [h0])
  have hy0 : y ≠ 0 := fun h0 => hy (by simp [h0])
  have hdisj : K ∙ x ⊓ K ∙ y = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun z hz => ?_
    obtain ⟨hzx, hzy⟩ := Submodule.mem_inf.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hzx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hzy
    have h1 : β x (a • x) = β x (b • y) := by rw [hb]
    simp only [map_smul, smul_eq_mul, hxy, mul_zero] at h1
    rw [(mul_eq_zero.mp h1).resolve_right hx, zero_smul]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ x) (K ∙ y)
  rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hx0, finrank_span_singleton hy0] at h
  rw [Submodule.span_insert, h]

theorem finrank_orthogonal_span_pair [FiniteDimensional K V] (hN : β.Nondegenerate) {x y : V}
    (hx : β x x ≠ 0) (hy : β y y ≠ 0) (hxy : β x y = 0) :
    finrank K ↥(β.orthogonal (Submodule.span K {x, y})) = finrank K V - 2 := by
  rw [LinearMap.BilinForm.finrank_orthogonal hN, finrank_span_pair hx hy hxy]

theorem finrank_orthogonal_span_singleton [FiniteDimensional K V] (hN : β.Nondegenerate) {x : V}
    (hx : β x x ≠ 0) : finrank K ↥(β.orthogonal (K ∙ x)) = finrank K V - 1 := by
  rw [LinearMap.BilinForm.finrank_orthogonal hN,
    finrank_span_singleton (fun h0 => hx (by simp [h0]))]

end Lines

/-! ## Part E: orthonormal bases over `𝔽₂` ([OAI26, §3.3, Lemma 6])

A nondegenerate symmetric `𝔽₂`-space with a vector of norm one has an orthonormal basis: split
off a unit line `⟨x⟩`; if the complement still has a unit vector, recurse; if it is zero, stop;
otherwise it is alternating, so pick `a, b` in it with `a·b = 1` and absorb the plane:
`x + a, x + b` are orthonormal, and `x + a + b` is a unit vector orthogonal to both; recurse on
the orthogonal complement of `⟨x + a, x + b⟩` inside the space. -/

section Split

variable {V : Type*} [AddCommGroup V] [Module K V] {β : LinearMap.BilinForm K V}

/-- Splitting a nondegenerate subspace `P ≤ E` off `E`. -/
theorem split_nondeg [FiniteDimensional K V] (hsymm : ∀ x y, β x y = β y x)
    {P E : Submodule K V} (hPE : P ≤ E) (hP : P ⊓ β.orthogonal P = ⊥) :
    P ⊔ (E ⊓ β.orthogonal P) = E ∧ P ⊓ (E ⊓ β.orthogonal P) = ⊥ ∧
      (E ⊓ β.orthogonal E = ⊥ →
        (E ⊓ β.orthogonal P) ⊓ β.orthogonal (E ⊓ β.orthogonal P) = ⊥) := by
  have hR : β.IsRefl := fun a b hab => (hsymm b a).trans hab
  have hc : IsCompl P (β.orthogonal P) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hR).mpr (disjoint_iff.mpr hP)
  have hsup : P ⊔ (E ⊓ β.orthogonal P) = E := by
    refine le_antisymm (sup_le hPE inf_le_left) fun z hz => ?_
    have hz' : z ∈ P ⊔ β.orthogonal P := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hz'
    have hqE : q ∈ E := by simpa using E.sub_mem hz (hPE hp)
    exact Submodule.mem_sup.mpr ⟨p, hp, q, ⟨hqE, hq⟩, rfl⟩
  refine ⟨hsup, eq_bot_iff.mpr (le_trans (inf_le_inf_left P inf_le_right) hP.le), fun hE => ?_⟩
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨⟨hzE, hzP⟩, hzo⟩ := hz
  have hzEo : z ∈ β.orthogonal E := by
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => ?_
    rw [← hsup] at hn
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hn
    rw [map_add, LinearMap.add_apply, LinearMap.BilinForm.mem_orthogonal_iff.mp hzP p hp,
      LinearMap.BilinForm.mem_orthogonal_iff.mp hzo q hq, add_zero]
  have h : z ∈ E ⊓ β.orthogonal E := ⟨hzE, hzEo⟩
  rw [hE] at h
  exact h

theorem finrank_lt_of_split [FiniteDimensional K V] {P E : Submodule K V}
    (hsup : P ⊔ (E ⊓ β.orthogonal P) = E) (hinf : P ⊓ (E ⊓ β.orthogonal P) = ⊥) (hP0 : P ≠ ⊥) :
    finrank K ↥(E ⊓ β.orthogonal P) < finrank K ↥E := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq P (E ⊓ β.orthogonal P)
  rw [hsup, hinf, finrank_bot, add_zero] at h
  have hpos : 0 < finrank K ↥P := Nat.pos_of_ne_zero fun h0 => hP0 (Submodule.finrank_eq_zero.mp h0)
  omega

end Split

section F2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  revert a; decide

omit [FiniteDimensional (ZMod 2) V] in
/-- Absorbing an alternating plane into a unit vector ([OAI26, §3.3, Lemma 6]): with `x·x = 1`, `x ⊥ a, b`,
`a·a = b·b = 0`, `a·b = 1`, the vectors `x + a`, `x + b` are orthonormal and `x + a + b` is a unit
vector orthogonal to both. -/
theorem absorb_plane (hsymm : ∀ x y, β x y = β y x) {x a b : V} (hxx : β x x = 1)
    (hxa : β x a = 0) (hxb : β x b = 0) (haa : β a a = 0) (hbb : β b b = 0) (hab : β a b = 1) :
    β (x + a) (x + a) = 1 ∧ β (x + b) (x + b) = 1 ∧ β (x + a) (x + b) = 0 ∧
      β (x + a) (x + a + b) = 0 ∧ β (x + b) (x + a + b) = 0 ∧ β (x + a + b) (x + a + b) = 1 := by
  have hax : β a x = 0 := (hsymm a x).trans hxa
  have hbx : β b x = 0 := (hsymm b x).trans hxb
  have hba : β b a = 1 := (hsymm b a).trans hab
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [map_add, LinearMap.add_apply, hxx, hxa, hxb, hax, hbx, haa, hbb, hab, hba,
      add_zero, zero_add, h11]

/-- [OAI26, §3.3, Lemma 6]: a nondegenerate (`E ⊓ E^⊥ = ⊥`) subspace of a symmetric bilinear
`𝔽₂`-space that is zero or contains a vector of norm one has an orthonormal basis. -/
theorem exists_isONBFor_zmod2 (hsymm : ∀ x y, β x y = β y x) (E : Submodule (ZMod 2) V)
    (hE : E ⊓ β.orthogonal E = ⊥) (hx : E = ⊥ ∨ ∃ x ∈ E, β x x ≠ 0) :
    ∃ L, IsONBFor β E L := by
  suffices H : ∀ n (E : Submodule (ZMod 2) V), finrank (ZMod 2) ↥E = n →
      E ⊓ β.orthogonal E = ⊥ → (E = ⊥ ∨ ∃ x ∈ E, β x x ≠ 0) → ∃ L, IsONBFor β E L from
    H _ E rfl hE hx
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro E hn hE hx
  rcases hx with hbot | ⟨x, hxE, hxx⟩
  · exact ⟨[], by rw [hbot]; exact isONBFor_nil⟩
  have hxx1 : β x x = 1 := zmod2_eq_one_of_ne_zero hxx
  have hx0 : x ≠ 0 := fun h0 => hxx (by simp [h0])
  have hP1 : (ZMod 2 ∙ x) ⊓ β.orthogonal (ZMod 2 ∙ x) = ⊥ :=
    LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot hxx
  have hP1E : (ZMod 2 ∙ x) ≤ E := (Submodule.span_singleton_le_iff_mem x E).mpr hxE
  obtain ⟨hsup1, hinf1, hnd1⟩ := split_nondeg hsymm hP1E hP1
  have hP1ne : (ZMod 2 ∙ x) ≠ ⊥ := fun h => hx0 (Submodule.span_singleton_eq_bot.mp h)
  have hlt1 : finrank (ZMod 2) ↥(E ⊓ β.orthogonal (ZMod 2 ∙ x)) < n := by
    rw [← hn]; exact finrank_lt_of_split hsup1 hinf1 hP1ne
  by_cases hcase : ∃ y ∈ E ⊓ β.orthogonal (ZMod 2 ∙ x), β y y ≠ 0
  · obtain ⟨L, hL⟩ := ih _ hlt1 _ rfl (hnd1 hE) (Or.inr hcase)
    refine ⟨[x] ++ L, ?_⟩
    have h := (isONBFor_singleton hxx1).append hL inf_le_right
    rwa [hsup1] at h
  push Not at hcase
  by_cases hE1 : E ⊓ β.orthogonal (ZMod 2 ∙ x) = ⊥
  · refine ⟨[x], ?_⟩
    have hEx : E = ZMod 2 ∙ x := by rw [← hsup1, hE1, sup_bot_eq]
    rw [hEx]
    exact isONBFor_singleton hxx1
  obtain ⟨a, haE1, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE1
  obtain ⟨b, hbE1, hab⟩ : ∃ b ∈ E ⊓ β.orthogonal (ZMod 2 ∙ x), β a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have ha : a ∈ (E ⊓ β.orthogonal (ZMod 2 ∙ x)) ⊓
        β.orthogonal (E ⊓ β.orthogonal (ZMod 2 ∙ x)) :=
      ⟨haE1, LinearMap.BilinForm.mem_orthogonal_iff.mpr fun m hm =>
        (hsymm m a).trans (hcon m hm)⟩
    rw [hnd1 hE] at ha
    exact ha0 ha
  have hxa : β x a = 0 :=
    LinearMap.BilinForm.mem_orthogonal_iff.mp haE1.2 x (Submodule.mem_span_singleton_self x)
  have hxb : β x b = 0 :=
    LinearMap.BilinForm.mem_orthogonal_iff.mp hbE1.2 x (Submodule.mem_span_singleton_self x)
  obtain ⟨hw1, hw2, hw12, hw13, hw23, hw3⟩ := absorb_plane hsymm hxx1 hxa hxb (hcase a haE1)
    (hcase b hbE1) (zmod2_eq_one_of_ne_zero hab)
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hP2E : Submodule.span (ZMod 2) {x + a, x + b} ≤ E := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact E.add_mem hxE haE1.1
    · exact E.add_mem hxE hbE1.1
  have hP2 : Submodule.span (ZMod 2) {x + a, x + b} ⊓
      β.orthogonal (Submodule.span (ZMod 2) {x + a, x + b}) = ⊥ :=
    disjoint_iff.mp (disjoint_span_pair_orthogonal hsymm (by rw [hw1]; exact h10)
      (by rw [hw2]; exact h10) hw12)
  obtain ⟨hsup2, hinf2, hnd2⟩ := split_nondeg hsymm hP2E hP2
  have hP2ne : Submodule.span (ZMod 2) {x + a, x + b} ≠ ⊥ := by
    intro h0
    have hmem : x + a ∈ Submodule.span (ZMod 2) {x + a, x + b} := Submodule.subset_span (by simp)
    rw [h0, Submodule.mem_bot] at hmem
    rw [hmem, map_zero] at hw1
    exact h10 hw1.symm
  have hlt2 : finrank (ZMod 2) ↥(E ⊓ β.orthogonal (Submodule.span (ZMod 2) {x + a, x + b})) < n := by
    rw [← hn]; exact finrank_lt_of_split hsup2 hinf2 hP2ne
  have hw3E : x + a + b ∈ E ⊓ β.orthogonal (Submodule.span (ZMod 2) {x + a, x + b}) := by
    refine ⟨E.add_mem (E.add_mem hxE haE1.1) hbE1.1,
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun m hm => ?_⟩
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hm
    rw [map_add β (c • (x + a)) (d • (x + b)), LinearMap.add_apply, map_smul β c (x + a),
      map_smul β d (x + b), LinearMap.smul_apply, LinearMap.smul_apply, hw13, hw23, smul_zero,
      smul_zero, add_zero]
  obtain ⟨L, hL⟩ := ih _ hlt2 _ rfl (hnd2 hE) (Or.inr ⟨x + a + b, hw3E, by rw [hw3]; exact h10⟩)
  refine ⟨[x + a, x + b] ++ L, ?_⟩
  have hpair : IsONBFor β (Submodule.span (ZMod 2) {x + a, x + b}) [x + a, x + b] := by
    have horth : (ZMod 2 ∙ (x + b)) ≤ β.orthogonal (ZMod 2 ∙ (x + a)) := by
      intro z hz
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun m hm => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
      simp only [map_smul, LinearMap.smul_apply, hw12, smul_zero]
    have h := (isONBFor_singleton hw1).append (isONBFor_singleton hw2) horth
    rw [← Submodule.span_insert] at h
    exact h
  have h := hpair.append hL inf_le_right
  rwa [hsup2] at h

end F2

end SubNLogN.Math.Networks.CellLib
