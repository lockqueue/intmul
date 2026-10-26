import SubNLogN.Math.Networks.GeneralH
import SubNLogN.Math.Networks.Proofs.CellLib2
import SubNLogN.Math.Networks.Proofs.CellSoundInst

/-!
# Complex network: orthonormal bases of the complex residuals ([OAI26] Lemma 6, last part)

[OAI26, §3.3, Lemma 6] (last part): for every `h ≥ 7` the residual of every edge of the
complex network has an orthonormal basis for the dot product over `𝔽₂` (`lemma6OnbGen_holds`,
the contract `Lemma6OnbGenStmt h` of `GeneralH.lean`); at `h = 100` this is the contract
`Lemma6OnbStmt` of `PhaseFrames.lean` (`lemma6Onb_holds`).

## Proof
For a role edge `e` let `e'` be its name-level edge (`WP6b.mem_edges_labels`). Then:
1. The residual is the sum of the difference cells `D` of `e'` (`WP6b.edge_residual_eq`). These
   are distinct pieces of the cell decomposition of `𝔽₂^{[h]³}` (`WP6b.cell_decomp`), so the
   residual is nondegenerate for the dot product (`CellLib.IsOrthDecomp.isCompl`).
2. Every cell contains a vector of norm one (`exists_unit_cell`): the pure tensor of norm-one
   vectors of its three atoms. For a line atom take `t_S` (`|S| = 3` is odd). For a complement atom
   take a unit vector `e_o` with `o` outside the at most two mentioned triples, which needs `h ≥ 7`.
3. A nondegenerate `𝔽₂`-space that is zero or contains a vector of norm one has an orthonormal
   basis (`CellLib.exists_isONBFor_zmod2`, [OAI26, §3.3, Lemma 6]). It is an `IsONB`, because `betaC3 h` is
   the dot product `dotC` (`isONB_of_isONBFor`).
-/

namespace SubNLogN.Math.Networks.WP6c

open Cell CellLib WP6b Module

variable {h : ℕ}

/-- An orthonormal basis for `betaC3 h` is an orthonormal basis for the dot product `dotC`. -/
theorem isONB_of_isONBFor {E : Submodule (ZMod 2) (Pt h)} {L : List (Pt h)}
    (hL : IsONBFor (betaC3 h) E L) : IsONB E L := by
  have hdot : ∀ x y : Pt h, betaC3 h x y = dotC x y := fun x y => by
    rw [betaC3_apply]; rfl
  obtain ⟨h1, h2, h3⟩ := hL
  exact ⟨fun v hv => (hdot v v).symm.trans (h1 v hv),
    h2.imp fun huv => (hdot _ _).symm.trans huv, h3⟩

/-- `x · e_o = x_o` for the unit vector `e_o = Pi.single o 1`. -/
theorem betaC_single_right (x : Fin h → ZMod 2) (o : Fin h) :
    betaC h x (Pi.single o 1) = x o := by
  rw [betaC_apply, Finset.sum_eq_single o]
  · simp
  · intro i _ hi
    simp [hi]
  · intro ho
    exact absurd (Finset.mem_univ o) ho

/-- A finset of `Fin h` with fewer than `h` elements misses some point. -/
theorem exists_not_mem_finset (Y : Finset (Fin h)) (hY : Y.card < h) : ∃ o, o ∉ Y := by
  by_contra hcon
  push Not at hcon
  have hY' : Y = Finset.univ := Finset.eq_univ_of_forall hcon
  rw [hY', Finset.card_univ, Fintype.card_fin] at hY
  exact lt_irrefl _ hY

/-- Every atom contains a vector of norm one (`h ≥ 7`): `t_{nm i}` for the line `.L i`, and a
unit vector `e_o`, `o` outside the triples `nm 0`, `nm 1`, for the complement `.C`. -/
theorem exists_unit_atom (h7 : 7 ≤ h) (nm : Fin 2 → Tri h) (R : List (Fin 2)) (a : Atom) :
    ∃ v ∈ atomSub (betaC h) nm R a, betaC h v v = 1 := by
  cases a with
  | L i =>
    refine ⟨ind (nm i), Submodule.mem_span_singleton_self _, ?_⟩
    rw [betaC_ind, inter_self]
    decide
  | C =>
    have hcard : ((nm 0).1 ∪ (nm 1).1).card < h := by
      calc ((nm 0).1 ∪ (nm 1).1).card ≤ (nm 0).1.card + (nm 1).1.card :=
            Finset.card_union_le _ _
        _ < h := by rw [(nm 0).2, (nm 1).2]; omega
    obtain ⟨o, ho⟩ := exists_not_mem_finset _ hcard
    refine ⟨Pi.single o 1, ?_, ?_⟩
    · rw [mem_atomC_iff]
      intro j _
      have hj : o ∉ (nm j).1 := by
        intro hmem
        apply ho
        fin_cases j
        · exact Finset.mem_union_left _ hmem
        · exact Finset.mem_union_right _ hmem
      rw [betaC_single_right]
      show (if o ∈ (nm j).1 then (1 : ZMod 2) else 0) = 0
      rw [if_neg hj]
    · rw [betaC_single_right]
      simp

/-- Every cell contains a vector of norm one (`h ≥ 7`): a pure tensor of norm-one atom vectors. -/
theorem exists_unit_cell (h7 : 7 ≤ h) (nm : Fin 3 → Fin 2 → Tri h) (R : Fin 3 → List (Fin 2))
    (c : Atom × Atom × Atom) : ∃ x ∈ cellSub (betaC h) nm R c, betaC3 h x x = 1 := by
  obtain ⟨u, hu, huu⟩ := exists_unit_atom h7 (nm 0) (R 0) c.1
  obtain ⟨v, hv, hvv⟩ := exists_unit_atom h7 (nm 1) (R 1) c.2.1
  obtain ⟨w, hw, hww⟩ := exists_unit_atom h7 (nm 2) (R 2) c.2.2
  refine ⟨pure3 u v w, pure3_mem_tspan hu hv hw, ?_⟩
  rw [betaC3_pure, huu, hvv, hww, one_mul, one_mul]

/-- The residual of an instantiated name-level edge (`EdgeOK`, orthogonal mentioned lines) has
an orthonormal basis for the dot product (`h ≥ 7`). -/
theorem exists_isONB_residual (h7 : 7 ≤ h) {nm : Fin 3 → Fin 2 → Tri h} {e : ALabel × ALabel}
    (hgood : GoodAll (betaC h) nm (eR e)) (hok : EdgeOK e) :
    ∃ L, IsONB (residual (betaC3 h) (labelSub (betaC h) (trLabel nm e.1))
      (labelSub (betaC h) (trLabel nm e.2))) L := by
  rw [edge_residual_eq agComplex hgood hok]
  have hD := cell_decomp (agComplex (h := h)) hgood
  have hsub : (cH e).toFinset \ (cT e).toFinset ∪ (cT e).toFinset \ (cH e).toFinset ⊆
      validCells (eR e) :=
    Finset.union_subset (Finset.sdiff_subset.trans (cells_sub_valid (namesIn_head e)))
      (Finset.sdiff_subset.trans (cells_sub_valid (namesIn_tail e)))
  have hx : (⨆ c ∈ (cH e).toFinset \ (cT e).toFinset ∪ (cT e).toFinset \ (cH e).toFinset,
      cellSub (betaC h) nm (eR e) c) = ⊥ ∨
      ∃ x ∈ (⨆ c ∈ (cH e).toFinset \ (cT e).toFinset ∪ (cT e).toFinset \ (cH e).toFinset,
        cellSub (betaC h) nm (eR e) c), betaC3 h x x ≠ 0 := by
    rcases Finset.eq_empty_or_nonempty
      ((cH e).toFinset \ (cT e).toFinset ∪ (cT e).toFinset \ (cH e).toFinset) with hE | ⟨c, hc⟩
    · left
      rw [hE]
      simp
    · right
      obtain ⟨x, hx, hxx⟩ := exists_unit_cell h7 nm (eR e) c
      exact ⟨x, piece_le_biSup hc hx, by rw [hxx]; decide⟩
  obtain ⟨L, hL⟩ := exists_isONBFor_zmod2 betaC3_symm _ (hD.isCompl hsub).inf_eq_bot hx
  exact ⟨L, isONB_of_isONBFor hL⟩

/-- [OAI26, §3.3, Lemma 6] (last part), every `h ≥ 7`: the residual of every edge of the
complex network has an orthonormal basis (the contract `Lemma6OnbGenStmt h`). -/
theorem lemma6OnbGen_holds (h : ℕ) (h7 : 7 ≤ h) : Lemma6OnbGenStmt h := by
  intro w e he
  obtain ⟨e', he', h1, h2⟩ := mem_edges_labels w he
  have hgood : GoodAll (betaC h) (roleNames w) (eR e') :=
    goodAll_role (fun S T hST => betaC_nbr hST) w he'
  have hres : residC e = residual (betaC3 h) (labelSub (betaC h) (trLabel (roleNames w) e'.1))
      (labelSub (betaC h) (trLabel (roleNames w) e'.2)) := by
    show residual (betaC3 h) (labelSub (betaC h) (vlabel e.1))
      (labelSub (betaC h) (vlabel e.2)) = _
    rw [h1, h2]
  rw [hres]
  exact exists_isONB_residual h7 hgood (classEdges_ok _ e' he')

/-- The contract `Lemma6OnbStmt` (`PhaseFrames.lean`, [OAI26] Lemma 6, last part, `h = 100`):
the residual of every edge of the complex network has an orthonormal basis. -/
theorem lemma6Onb_holds : Lemma6OnbStmt :=
  lemma6OnbGen_holds 100 (by norm_num)

end SubNLogN.Math.Networks.WP6c
