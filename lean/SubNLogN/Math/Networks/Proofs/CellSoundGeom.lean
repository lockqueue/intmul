import SubNLogN.Math.Networks.Proofs.CellSoundCommon
import SubNLogN.Math.Networks.Proofs.CellLib

/-!
# Cell soundness, geometric part: labels as unions of cells

Generic over a label field `K` with factor form `β` on `K^h` and ambient form `β3` on `K^{[h]³}`
satisfying `AGeom β β3` (both symmetric and nondegenerate, triple lines anisotropic, `β3` the tensor
cube of `β` on pure tensors). Both networks instantiate this (`Lemma6Bit*.lean`, `Lemma6C*.lean`).

* Atoms of one coordinate (CellCalc's `Atom`): the mentioned lines `⟨t_{nm i}⟩` and their joint
  `β`-orthogonal complement (`atomSub`). If the mentioned lines are orthogonal (`Good`), the atoms form
  an orthogonal decomposition of `K^h` (`atom_decomp`), of dimensions `1` and `h − |R|`.
* Tokens and labels: `tokSub β (trTok nm τ)` is the sum of the atoms `tokAtoms R τ`, and
  `labelSub β (trLabel nm L)` is the sum of the cells `Cell.cells R L` (`labelSub_tr`), provided every
  name of `L` is in `R` (`NamesIn`).
* Cells (`cellSub`, tensor spans of atoms) form an orthogonal decomposition of `K^{[h]³}`
  (`cell_decomp`), with `finrank = Cell.cellDim` (`finrank_cell`).
* Per name-level edge (`EdgeOK`): nondegeneracy, nesting, label dimensions as cell sums, residual
  dimension `= Cell.edgeDim`, and (char 0) rank of `P_head − s P_tail` `= Cell.edgeRank`.
-/

namespace SubNLogN.Math.Networks.WP6b

open Cell CellLib Module

variable {K : Type*} [Field K] {h : ℕ}

/-- Factor geometry of a label field: `β` symmetric and nondegenerate, triple lines anisotropic. -/
structure FGeom (β : LinearMap.BilinForm K (Fin h → K)) : Prop where
  symm : ∀ x y, β x y = β y x
  nondeg : ∀ x, (∀ y, β x y = 0) → x = 0
  self : ∀ t : Tri h, β (ind t) (ind t) ≠ 0

/-- Geometry of a label field: factor geometry, and `β3` symmetric, nondegenerate and the tensor
cube of `β` on pure tensors. -/
structure AGeom (β : LinearMap.BilinForm K (Fin h → K)) (β3 : LinearMap.BilinForm K (Cube h → K)) : Prop
    extends FGeom β where
  symm3 : ∀ x y, β3 x y = β3 y x
  nondeg3 : ∀ x, (∀ y, β3 x y = 0) → x = 0
  pure : ∀ u v w u' v' w', β3 (pure3 u v w) (pure3 u' v' w') = β u u' * β v v' * β w w'

/-! ### Atoms of one coordinate -/

section Factor

/-- Atoms of a coordinate with name assignment `nm` and mentioned names `R`: the lines
`⟨t_{nm i}⟩` and the joint `β`-orthogonal complement of the mentioned lines. -/
def atomSub (β : LinearMap.BilinForm K (Fin h → K)) (nm : Fin 2 → Tri h) (R : List (Fin 2)) :
    Atom → Submodule K (Fin h → K)
  | .L i => K ∙ (ind (nm i) : Fin h → K)
  | .C => β.orthogonal (Submodule.span K {x | ∃ i ∈ R, x = (ind (nm i) : Fin h → K)})

/-- The mentioned lines of a coordinate are orthogonal. -/
def Good (β : LinearMap.BilinForm K (Fin h → K)) (nm : Fin 2 → Tri h) (R : List (Fin 2)) : Prop :=
  0 ∈ R → 1 ∈ R → β (ind (nm 0)) (ind (nm 1)) = 0

variable {β : LinearMap.BilinForm K (Fin h → K)} {nm : Fin 2 → Tri h} {R : List (Fin 2)}

theorem good_orth (hsymm : ∀ x y, β x y = β y x) (hgood : Good β nm R) {i j : Fin 2} (hi : i ∈ R)
    (hj : j ∈ R) (hij : i ≠ j) : β (ind (nm i)) (ind (nm j)) = 0 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hgood hi hj
  · rw [hsymm]; exact hgood hj hi
  · exact absurd rfl hij

theorem good_of_not_mem (h1 : (1 : Fin 2) ∉ R) : Good β nm R := fun _ h => absurd h h1

theorem mem_atomC_iff {x : Fin h → K} :
    x ∈ atomSub β nm R .C ↔ ∀ j ∈ R, β (ind (nm j)) x = 0 := by
  constructor
  · intro hx j hj
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hx) _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · intro hx
    show x ∈ β.orthogonal _
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have hle : Submodule.span K {x | ∃ i ∈ R, x = (ind (nm i) : Fin h → K)} ≤
        LinearMap.ker (β.flip x) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      exact hx j hj
    have h2 := hle hn
    simp only [LinearMap.mem_ker] at h2
    exact h2

theorem sub_mem_atomC (hG : FGeom β) (hgood : Good β nm R) (x : Fin h → K) :
    x - ∑ i ∈ R.toFinset, (β (ind (nm i)) x / β (ind (nm i)) (ind (nm i))) • (ind (nm i) : Fin h → K)
      ∈ atomSub β nm R .C := by
  rw [mem_atomC_iff]
  intro j hj
  rw [map_sub, map_sum, Finset.sum_eq_single j]
  · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (hG.self _), sub_self]
  · intro i hi hij
    rw [map_smul, smul_eq_mul, good_orth hG.symm hgood hj (List.mem_toFinset.1 hi) (Ne.symm hij),
      mul_zero]
  · intro hj'
    exact absurd (List.mem_toFinset.2 hj) hj'

theorem mem_atoms_L {i : Fin 2} : Atom.L i ∈ atoms R ↔ i ∈ R := by
  simp [atoms]

theorem mem_atoms_C : Atom.C ∈ atoms R := by
  simp [atoms]

theorem atoms_nodup (hR : R.Nodup) : (atoms R).Nodup := by
  unfold atoms
  rw [List.nodup_append]
  refine ⟨hR.map (fun a b hab => by cases hab; rfl), List.nodup_singleton _, ?_⟩
  intro a ha b hb
  simp only [List.mem_map, List.mem_singleton] at ha hb
  obtain ⟨i, _, rfl⟩ := ha
  subst hb
  nofun

theorem mem_biSup_of_mem' {ι M : Type*} [AddCommGroup M] [Module K M] {W : ι → Submodule K M}
    {s : Finset ι} {i : ι} (hi : i ∈ s) {x : M} (hx : x ∈ W i) : x ∈ ⨆ j ∈ s, W j :=
  (le_iSup₂ (f := fun j (_ : j ∈ s) => W j) i hi) hx

/-- The atoms of a coordinate form an orthogonal decomposition of `K^h`. -/
theorem atom_decomp (hG : FGeom β) (hgood : Good β nm R) :
    IsOrthDecomp β (atoms R).toFinset (atomSub β nm R) where
  symm := hG.symm
  nondeg := hG.nondeg
  orth := by
    intro a ha b hb hab x hx y hy
    rw [List.mem_toFinset] at ha hb
    cases a with
    | L i =>
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      cases b with
      | L j =>
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
        have hij : i ≠ j := fun h => hab (h ▸ rfl)
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
          good_orth hG.symm hgood (mem_atoms_L.1 ha) (mem_atoms_L.1 hb) hij, mul_zero]
      | C =>
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
          (mem_atomC_iff.1 hy) i (mem_atoms_L.1 ha), mul_zero]
    | C =>
      cases b with
      | L j =>
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
        rw [map_smul, smul_eq_mul, hG.symm, (mem_atomC_iff.1 hx) j (mem_atoms_L.1 hb), mul_zero]
      | C => exact absurd rfl hab
  top := by
    rw [eq_top_iff]
    intro x _
    have hx : x = (∑ i ∈ R.toFinset,
        (β (ind (nm i)) x / β (ind (nm i)) (ind (nm i))) • (ind (nm i) : Fin h → K)) +
        (x - ∑ i ∈ R.toFinset,
          (β (ind (nm i)) x / β (ind (nm i)) (ind (nm i))) • (ind (nm i) : Fin h → K)) := by
      abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i hi => ?_) ?_
    · exact mem_biSup_of_mem' (List.mem_toFinset.2 (mem_atoms_L.2 (List.mem_toFinset.1 hi)))
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · exact mem_biSup_of_mem' (List.mem_toFinset.2 mem_atoms_C) (sub_mem_atomC hG hgood x)

theorem ind_ne_zero (hG : FGeom β) (t : Tri h) : (ind t : Fin h → K) ≠ 0 := by
  intro h0
  apply hG.self t
  rw [h0, map_zero]

theorem finrank_atom_L (hG : FGeom β) (i : Fin 2) : finrank K (atomSub β nm R (.L i)) = 1 :=
  finrank_span_singleton (ind_ne_zero hG (nm i))

theorem finrank_atom_C (hG : FGeom β) (hR : R.Nodup) (hgood : Good β nm R) :
    finrank K (atomSub β nm R .C) = h - R.length := by
  have h1 := (atom_decomp hG hgood).finrank_biSup (subset_refl _)
  rw [(atom_decomp hG hgood).top, finrank_top, Module.finrank_fin_fun,
    List.sum_toFinset _ (atoms_nodup hR)] at h1
  have h2 : ((atoms R).map fun a => finrank K (atomSub β nm R a)) =
      R.map (fun _ => 1) ++ [finrank K (atomSub β nm R .C)] := by
    simp only [atoms, List.map_append, List.map_map, List.map_cons, List.map_nil]
    congr 1
    exact List.map_congr_left fun i _ => finrank_atom_L hG i
  rw [h2, List.sum_append, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
    List.sum_singleton] at h1
  omega

theorem finrank_atom (hG : FGeom β) (hR : R.Nodup) (hgood : Good β nm R) (a : Atom) :
    finrank K (atomSub β nm R a) = atomDim h R a := by
  cases a with
  | L i => exact finrank_atom_L hG i
  | C => exact finrank_atom_C hG hR hgood

/-! ### Tokens -/

theorem biSup_singleton' {ι M : Type*} [CompleteLattice M] (f : ι → M) (b : ι) :
    ⨆ a ∈ ({b} : Finset ι), f a = f b := by
  simp

/-- An instantiated token is the sum of its atoms. -/
theorem tokSub_tr (hG : FGeom β) (hgood : Good β nm R) (τ : ATok) (hτ : ∀ i ∈ tokNames τ, i ∈ R) :
    tokSub β (trTok nm τ) = ⨆ a ∈ (tokAtoms R τ).toFinset, atomSub β nm R a := by
  have hD := atom_decomp hG hgood
  cases τ with
  | zero =>
    show (⊥ : Submodule K (Fin h → K)) = _
    simp [tokAtoms]
  | full =>
    show (⊤ : Submodule K (Fin h → K)) = _
    rw [← hD.top]
    rfl
  | line i =>
    show K ∙ (ind (nm i) : Fin h → K) = _
    simp only [tokAtoms, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, biSup_singleton']
    rfl
  | perp i =>
    have hi : i ∈ R := hτ i (by simp [tokNames])
    have hS : ({Atom.L i} : Finset Atom) ⊆ (atoms R).toFinset := by
      simp [mem_atoms_L, hi]
    have h1 := hD.orthogonal_biSup hS
    rw [biSup_singleton'] at h1
    have hfs : (tokAtoms R (.perp i)).toFinset = (atoms R).toFinset \ {Atom.L i} := by
      ext a
      simp [tokAtoms]
    rw [hfs, ← h1]
    rfl
  | perp2 =>
    have h0 : (0 : Fin 2) ∈ R := hτ 0 (by simp [tokNames])
    have h1' : (1 : Fin 2) ∈ R := hτ 1 (by simp [tokNames])
    have hS : ({Atom.L 0, Atom.L 1} : Finset Atom) ⊆ (atoms R).toFinset := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp [mem_atoms_L, h0, h1']
    have h1 := hD.orthogonal_biSup hS
    rw [Finset.iSup_insert, biSup_singleton'] at h1
    have hfs : (tokAtoms R .perp2).toFinset = (atoms R).toFinset \ {Atom.L 0, Atom.L 1} := by
      ext a
      simp [tokAtoms]
    rw [hfs, ← h1]
    show β.orthogonal (Submodule.span K {ind (nm 0), ind (nm 1)}) = _
    rw [Submodule.span_insert]
    rfl

end Factor

/-! ### Labels as sums of cells -/

section Labels

variable {β : LinearMap.BilinForm K (Fin h → K)}

/-- Cells: tensor spans of atoms of the three coordinates. -/
def cellSub (β : LinearMap.BilinForm K (Fin h → K)) (nm : Fin 3 → Fin 2 → Tri h)
    (R : Fin 3 → List (Fin 2)) (c : Atom × Atom × Atom) : Submodule K (Cube h → K) :=
  tspan (atomSub β (nm 0) (R 0) c.1) (atomSub β (nm 1) (R 1) c.2.1) (atomSub β (nm 2) (R 2) c.2.2)

/-- The mentioned lines are orthogonal at every coordinate. -/
def GoodAll (β : LinearMap.BilinForm K (Fin h → K)) (nm : Fin 3 → Fin 2 → Tri h)
    (R : Fin 3 → List (Fin 2)) : Prop :=
  ∀ k, Good β (nm k) (R k)

/-- Every name used by `L` at coordinate `k` lies in `R k`. -/
def NamesIn (R : Fin 3 → List (Fin 2)) (L : ALabel) : Prop :=
  ∀ σ ∈ L, (∀ i ∈ tokNames σ.1, i ∈ R 0) ∧ (∀ i ∈ tokNames σ.2.1, i ∈ R 1) ∧
    (∀ i ∈ tokNames σ.2.2, i ∈ R 2)

/-- All cells of the atoms of the three coordinates. -/
def validCells (R : Fin 3 → List (Fin 2)) : Finset (Atom × Atom × Atom) :=
  (atoms (R 0)).toFinset ×ˢ (atoms (R 1)).toFinset ×ˢ (atoms (R 2)).toFinset

theorem namesIn_coordNames {Ls : List ALabel} {L : ALabel} (hL : L ∈ Ls) :
    NamesIn (coordNames Ls) L := by
  intro σ hσ
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
  · simp only [coordNames, List.mem_dedup, List.mem_flatMap, id]
    exact ⟨σ, ⟨L, hL, hσ⟩, by simpa using hi⟩

theorem tokAtoms_sub {R : List (Fin 2)} {τ : ATok} (hτ : ∀ i ∈ tokNames τ, i ∈ R) :
    ∀ a ∈ tokAtoms R τ, a ∈ atoms R := by
  intro a ha
  cases τ with
  | zero => simp [tokAtoms] at ha
  | full => exact ha
  | line i =>
    simp only [tokAtoms, List.mem_singleton] at ha
    subst ha
    exact mem_atoms_L.2 (hτ i (by simp [tokNames]))
  | perp i => exact (List.mem_filter.1 ha).1
  | perp2 => exact (List.mem_filter.1 ha).1

theorem cells_sub_valid {R : Fin 3 → List (Fin 2)} {L : ALabel} (hL : NamesIn R L) :
    (cells R L).toFinset ⊆ validCells R := by
  intro c hc
  simp only [List.mem_toFinset, cells, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨σ, hσ, x, hx, y, hy, z, hz, rfl⟩ := hc
  obtain ⟨h0, h1, h2⟩ := hL σ hσ
  simp only [validCells, Finset.mem_product, List.mem_toFinset]
  exact ⟨tokAtoms_sub h0 x hx, tokAtoms_sub h1 y hy, tokAtoms_sub h2 z hz⟩

theorem cells_cons (R : Fin 3 → List (Fin 2)) (σ : ATok × ATok × ATok) (L : ALabel) :
    cells R (σ :: L) = cells R [σ] ++ cells R L := by
  simp [cells]

theorem cells_singleton_toFinset (R : Fin 3 → List (Fin 2)) (σ : ATok × ATok × ATok) :
    (cells R [σ]).toFinset = (tokAtoms (R 0) σ.1).toFinset ×ˢ (tokAtoms (R 1) σ.2.1).toFinset ×ˢ
      (tokAtoms (R 2) σ.2.2).toFinset := by
  ext ⟨x, y, z⟩
  simp [cells, List.mem_flatMap]

/-- **Label semantics**: an instantiated name-level label is the sum of its cells. -/
theorem labelSub_tr (hG : FGeom β) {nm : Fin 3 → Fin 2 → Tri h} {R : Fin 3 → List (Fin 2)}
    (hgood : GoodAll β nm R) (L : ALabel) (hL : NamesIn R L) :
    labelSub β (trLabel nm L) = ⨆ c ∈ (cells R L).toFinset, cellSub β nm R c := by
  induction L with
  | nil => simp [trLabel, labelSub, cells]
  | cons σ L ih =>
    obtain ⟨h0, h1, h2⟩ := hL σ List.mem_cons_self
    have hL' : NamesIn R L := fun σ' h' => hL σ' (List.mem_cons_of_mem _ h')
    rw [show trLabel nm (σ :: L) = trSummand nm σ :: trLabel nm L from rfl, labelSub_cons, ih hL',
      cells_cons, List.toFinset_append, Finset.iSup_union, summandSub_eq_tspan]
    congr 1
    rw [show (trSummand nm σ).1 = trTok (nm 0) σ.1 from rfl,
      show (trSummand nm σ).2.1 = trTok (nm 1) σ.2.1 from rfl,
      show (trSummand nm σ).2.2 = trTok (nm 2) σ.2.2 from rfl,
      tokSub_tr hG (hgood 0) σ.1 h0, tokSub_tr hG (hgood 1) σ.2.1 h1,
      tokSub_tr hG (hgood 2) σ.2.2 h2, tspan_biSup, cells_singleton_toFinset]
    rfl

variable {β3 : LinearMap.BilinForm K (Cube h → K)}

/-- The cells form an orthogonal decomposition of `K^{[h]³}`. -/
theorem cell_decomp (hG : AGeom β β3) {nm : Fin 3 → Fin 2 → Tri h} {R : Fin 3 → List (Fin 2)}
    (hgood : GoodAll β nm R) : IsOrthDecomp β3 (validCells R) (cellSub β nm R) :=
  IsOrthDecomp.tensor hG.pure hG.symm3 hG.nondeg3 (atom_decomp hG.toFGeom (hgood 0))
    (atom_decomp hG.toFGeom (hgood 1)) (atom_decomp hG.toFGeom (hgood 2))

theorem finrank_cell (hG : FGeom β) {nm : Fin 3 → Fin 2 → Tri h} {R : Fin 3 → List (Fin 2)}
    (hR : ∀ k, (R k).Nodup) (hgood : GoodAll β nm R) (c : Atom × Atom × Atom) :
    finrank K (cellSub β nm R c) = cellDim h R c := by
  rw [cellSub, finrank_tspan, finrank_atom hG (hR 0) (hgood 0), finrank_atom hG (hR 1) (hgood 1),
    finrank_atom hG (hR 2) (hgood 2)]
  rfl

/-- Instantiated labels are nondegenerate. -/
theorem isCompl_tr (hG : AGeom β β3) {nm : Fin 3 → Fin 2 → Tri h} {R : Fin 3 → List (Fin 2)}
    (hgood : GoodAll β nm R) (L : ALabel) (hL : NamesIn R L) :
    IsCompl (labelSub β (trLabel nm L)) (β3.orthogonal (labelSub β (trLabel nm L))) := by
  rw [labelSub_tr hG.toFGeom hgood L hL]
  exact (cell_decomp hG hgood).isCompl (cells_sub_valid hL)

/-- Every vertex label is nondegenerate (also at gates touched by no role). -/
theorem isCompl_vertex (hG : AGeom β β3) {κ : Kind} (v : Vertex κ h) :
    IsCompl (labelSub β (vlabel v)) (β3.orthogonal (labelSub β (vlabel v))) := by
  obtain ⟨AL, nm, hv, h1⟩ := vlabel_single v
  rw [hv]
  exact isCompl_tr hG (fun k => good_of_not_mem (h1 k)) AL
    (namesIn_coordNames (List.mem_singleton_self _))

/-- The name assignment of a role is `Good` on its class edges. -/
theorem goodAll_role {κ : Kind} (hnbr : ∀ S T : Tri h, Nbr κ S T → β (ind S) (ind T) = 0)
    (w : Role κ h) {e : ALabel × ALabel} (he : e ∈ classEdges (classOf w)) :
    GoodAll β (roleNames w) (eR e) :=
  fun k _ h1 => hnbr _ _ (roleNames_one w he k h1)

end Labels

/-! ### Per name-level edge -/

section Edge

variable {β : LinearMap.BilinForm K (Fin h → K)} {β3 : LinearMap.BilinForm K (Cube h → K)}

theorem eR_nodup (e : ALabel × ALabel) (k : Fin 3) : (eR e k).Nodup := List.nodup_dedup _

theorem namesIn_tail (e : ALabel × ALabel) : NamesIn (eR e) e.1 :=
  namesIn_coordNames (by simp)

theorem namesIn_head (e : ALabel × ALabel) : NamesIn (eR e) e.2 :=
  namesIn_coordNames (by simp)

theorem edge_tail (hG : FGeom β) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) :
    labelSub β (trLabel nm e.1) = ⨆ c ∈ (cT e).toFinset, cellSub β nm (eR e) c :=
  labelSub_tr hG hgood e.1 (namesIn_tail e)

theorem edge_head (hG : FGeom β) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) :
    labelSub β (trLabel nm e.2) = ⨆ c ∈ (cH e).toFinset, cellSub β nm (eR e) c :=
  labelSub_tr hG hgood e.2 (namesIn_head e)

theorem toFinset_sub_of {l l' : List (Atom × Atom × Atom)} (h : ∀ x ∈ l, x ∈ l') :
    l.toFinset ⊆ l'.toFinset :=
  fun c hc => List.mem_toFinset.2 (h c (List.mem_toFinset.1 hc))

/-- Nested cell lists give nested labels. -/
theorem edge_nested (hG : FGeom β) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) (hok : EdgeOK e) :
    labelSub β (trLabel nm e.1) ≤ labelSub β (trLabel nm e.2) ∨
      labelSub β (trLabel nm e.2) ≤ labelSub β (trLabel nm e.1) := by
  rw [edge_tail hG hgood, edge_head hG hgood]
  rcases hok.2.2 with h1 | h1
  · exact Or.inl (biSup_mono_finset (toFinset_sub_of h1))
  · exact Or.inr (biSup_mono_finset (toFinset_sub_of h1))

/-- Increasing cell lists give increasing labels. -/
theorem edge_inc (hG : FGeom β) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) (hinc : ∀ x ∈ cT e, x ∈ cH e) :
    labelSub β (trLabel nm e.1) ≤ labelSub β (trLabel nm e.2) := by
  rw [edge_tail hG hgood, edge_head hG hgood]
  exact biSup_mono_finset (toFinset_sub_of hinc)

theorem edge_finrank_tail (hG : AGeom β β3) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) (hok : EdgeOK e) :
    finrank K (labelSub β (trLabel nm e.1)) = ((cT e).map (cellDim h (eR e))).sum := by
  have hA : (cT e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_tail e)
  rw [edge_tail hG.toFGeom hgood, (cell_decomp hG hgood).finrank_biSup hA, List.sum_toFinset _ hok.1]
  exact congrArg List.sum
    (List.map_congr_left fun c _ => finrank_cell hG.toFGeom (eR_nodup e) hgood c)

theorem edge_finrank_head (hG : AGeom β β3) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) (hok : EdgeOK e) :
    finrank K (labelSub β (trLabel nm e.2)) = ((cH e).map (cellDim h (eR e))).sum := by
  have hB : (cH e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_head e)
  rw [edge_head hG.toFGeom hgood, (cell_decomp hG hgood).finrank_biSup hB,
    List.sum_toFinset _ hok.2.1]
  exact congrArg List.sum
    (List.map_congr_left fun c _ => finrank_cell hG.toFGeom (eR_nodup e) hgood c)

theorem foldr_add_eq_sum {α : Type*} (f : α → ℕ) (l : List α) :
    l.foldr (fun c acc => f c + acc) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem edgeDim_eq (e : ALabel × ALabel) (hok : EdgeOK e) :
    edgeDim h e.1 e.2 = ∑ c ∈ (cH e).toFinset \ (cT e).toFinset, cellDim h (eR e) c +
      ∑ c ∈ (cT e).toFinset \ (cH e).toFinset, cellDim h (eR e) c := by
  simp only [edgeDim, foldr_add_eq_sum, List.map_append, List.sum_append]
  rw [← List.sum_toFinset _ (hok.2.1.filter _), ← List.sum_toFinset _ (hok.1.filter _)]
  congr 2 <;> ext c <;> simp

/-- The orthogonal residual of a nested name-level edge is the sum of the cells of the symmetric
difference of its two cell sets. -/
theorem edge_residual_eq (hG : AGeom β β3) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) (hok : EdgeOK e) :
    residual β3 (labelSub β (trLabel nm e.1)) (labelSub β (trLabel nm e.2)) =
      ⨆ c ∈ (cH e).toFinset \ (cT e).toFinset ∪ (cT e).toFinset \ (cH e).toFinset,
        cellSub β nm (eR e) c := by
  have hD := cell_decomp hG hgood
  have hA : (cT e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_tail e)
  have hB : (cH e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_head e)
  rw [edge_tail hG.toFGeom hgood, edge_head hG.toFGeom hgood, Finset.iSup_union]
  by_cases hle : (⨆ c ∈ (cT e).toFinset, cellSub β nm (eR e) c) ≤
      ⨆ c ∈ (cH e).toFinset, cellSub β nm (eR e) c
  · rw [residual, if_pos hle, hD.inf_orthogonal hA hB]
    have h0 : (⨆ c ∈ (cT e).toFinset \ (cH e).toFinset, cellSub β nm (eR e) c) = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun c hc => ?_)
      rw [(hD.biSup_le_biSup_iff hA hB).1 hle c (Finset.mem_sdiff.1 hc).1 (Finset.mem_sdiff.1 hc).2]
    rw [h0, sup_bot_eq]
  · rw [residual, if_neg hle, hD.inf_orthogonal hB hA]
    have hBA : (cH e).toFinset ⊆ (cT e).toFinset := by
      rcases hok.2.2 with h1 | h1
      · exact (hle (biSup_mono_finset (toFinset_sub_of h1))).elim
      · exact toFinset_sub_of h1
    rw [Finset.sdiff_eq_empty_iff_subset.2 hBA]
    simp

/-- The orthogonal residual of a name-level edge has dimension `Cell.edgeDim`. -/
theorem edge_residual (hG : AGeom β β3) {e : ALabel × ALabel} {nm : Fin 3 → Fin 2 → Tri h}
    (hgood : GoodAll β nm (eR e)) (hok : EdgeOK e) :
    finrank K (residual β3 (labelSub β (trLabel nm e.1)) (labelSub β (trLabel nm e.2))) =
      edgeDim h e.1 e.2 := by
  have hD := cell_decomp hG hgood
  have hA : (cT e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_tail e)
  have hB : (cH e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_head e)
  have hsub : (cH e).toFinset \ (cT e).toFinset ∪ (cT e).toFinset \ (cH e).toFinset ⊆
      validCells (eR e) :=
    Finset.union_subset (Finset.sdiff_subset.trans hB) (Finset.sdiff_subset.trans hA)
  rw [edge_residual_eq hG hgood hok, hD.finrank_biSup hsub,
    Finset.sum_union disjoint_sdiff_sdiff, edgeDim_eq e hok]
  congr 1 <;> exact Finset.sum_congr rfl fun c _ => finrank_cell hG.toFGeom (eR_nodup e) hgood c

theorem one_eq_intCast_iff [CharZero K] (s : ℤ) : (1 : K) = (s : K) ↔ 1 = s := by
  constructor
  · intro hs; exact_mod_cast hs
  · intro hs; rw [← hs]; simp

/-- In characteristic `0`, the rank of `P_head − s P_tail` is `Cell.edgeRank`. -/
theorem edge_rank [CharZero K] [DecidableEq K] (hG : AGeom β β3) {e : ALabel × ALabel}
    {nm : Fin 3 → Fin 2 → Tri h} (hgood : GoodAll β nm (eR e)) (hok : EdgeOK e) (s : ℤ) :
    finrank K (LinearMap.range (projAlong β3 (labelSub β (trLabel nm e.2)) -
      (s : K) • projAlong β3 (labelSub β (trLabel nm e.1)))) = edgeRank h s 1 e.1 e.2 := by
  have hD := cell_decomp hG hgood
  have hA : (cT e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_tail e)
  have hB : (cH e).toFinset ⊆ validCells (eR e) := cells_sub_valid (namesIn_head e)
  have hf : ∀ c, finrank K (cellSub β nm (eR e) c) = cellDim h (eR e) c :=
    finrank_cell hG.toFGeom (eR_nodup e) hgood
  rw [edge_tail hG.toFGeom hgood, edge_head hG.toFGeom hgood]
  have hsmul : ∀ P Q : Module.End K (Cube h → K), P - (s : K) • Q = (1 : K) • P - (s : K) • Q :=
    fun P Q => by rw [one_smul]
  rw [hsmul, hD.finrank_range_smul_sub hB hA]
  simp only [edgeRank, foldr_add_eq_sum]
  rw [← List.sum_toFinset _ ?hnd]
  · refine Finset.sum_congr ?_ fun c _ => hf c
    ext c
    simp only [Finset.mem_filter, Finset.mem_union, List.mem_toFinset, List.mem_filter,
      List.mem_append, decide_eq_true_eq]
    by_cases h1 : c ∈ cH e <;> by_cases h2 : c ∈ cT e <;> simp [h1, h2] <;>
      simp only [sub_eq_zero, one_eq_intCast_iff]
  · refine List.Nodup.filter _ (List.Nodup.append hok.2.1 (hok.1.filter _) ?_)
    intro a ha hb
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    exact hb.2 ha

end Edge

end SubNLogN.Math.Networks.WP6b
