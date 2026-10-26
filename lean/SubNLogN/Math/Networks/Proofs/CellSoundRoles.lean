import SubNLogN.Math.Networks.Proofs.CellSoundInst

/-!
# Cell soundness: role-level consequences

Generic over a label field with `AGeom β β3` in which neighbouring triple lines are orthogonal
(`hnbr`), for either network `κ`:
* `role_nested`: every edge of every role joins nested labels ([OAI26] Lemma 6);
* `role_residual_sum`: the orthogonal residual dimensions along a role sum to
  `Cell.classDimSum h (classOf w)`;
* `role_absDim_sum`: the absolute label-dimension changes along a role sum to the corresponding
  name-level cell sums;
* `role_decreasing_gen` (every `h > 0`, given the name-level loss `hcd` of the centre edge
  `3 → 4`, supplied by `center_dec_gen`) and `role_decreasing` (`h = 100`, `hcd` by `decide`): the
  decreasing edges are exactly the central edges `3 → 4`, each losing dimension `h` (iff form).
-/

namespace SubNLogN.Math.Networks.WP6b

open Cell CellLib Module

variable {K : Type*} [Field K]

section General

variable {h : ℕ} {β : LinearMap.BilinForm K (Fin h → K)} {β3 : LinearMap.BilinForm K (Cube h → K)}
  {κ : Kind}

/-- Every edge of a role joins nested labels. -/
theorem role_nested (hG : AGeom β β3) (hnbr : ∀ S T : Tri h, Nbr κ S T → β (ind S) (ind T) = 0)
    (w : Role κ h) {e : Vertex κ h × Vertex κ h} (he : e ∈ edges w) :
    labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2) ∨
      labelSub β (vlabel e.2) ≤ labelSub β (vlabel e.1) := by
  obtain ⟨e', he', h1, h2⟩ := mem_edges_labels w he
  rw [h1, h2]
  exact edge_nested hG.toFGeom (goodAll_role hnbr w he') (classEdges_ok _ e' he')

/-- The orthogonal residual dimensions along a role sum to `Cell.classDimSum`. -/
theorem role_residual_sum (hG : AGeom β β3)
    (hnbr : ∀ S T : Tri h, Nbr κ S T → β (ind S) (ind T) = 0) (w : Role κ h) :
    ((edges w).map fun e =>
        finrank K (residual β3 (labelSub β (vlabel e.1)) (labelSub β (vlabel e.2)))).sum =
      classDimSum h (classOf w) := by
  refine (sum_edges_labels w
    (fun U V => finrank K (residual β3 (labelSub β U) (labelSub β V)))).trans ?_
  show _ = ((classEdges (classOf w)).map fun e => edgeDim h e.1 e.2).sum
  exact congrArg List.sum (List.map_congr_left fun e he =>
    edge_residual hG (goodAll_role hnbr w he) (classEdges_ok _ e he))

/-- The absolute label-dimension changes along a role are the name-level cell sums. -/
theorem role_absDim_sum (hG : AGeom β β3)
    (hnbr : ∀ S T : Tri h, Nbr κ S T → β (ind S) (ind T) = 0) (w : Role κ h) :
    ((edges w).map fun e =>
        Int.natAbs ((finrank K (labelSub β (vlabel e.2)) : ℤ) - finrank K (labelSub β (vlabel e.1)))).sum =
      ((classEdges (classOf w)).map fun e =>
        Int.natAbs ((((cH e).map (cellDim h (eR e))).sum : ℤ) - ((cT e).map (cellDim h (eR e))).sum)).sum := by
  refine (sum_edges_labels w (fun U V =>
    Int.natAbs ((finrank K (labelSub β V) : ℤ) - finrank K (labelSub β U)))).trans ?_
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  have hg := goodAll_role hnbr w he
  have hok := classEdges_ok _ e he
  simp only [edge_finrank_head hG hg hok, edge_finrank_tail hG hg hok]

end General

/-- The only decreasing edges are the central edges from time `3` to time `4`, and each loses
dimension `h`, given the name-level loss `hcd` of the centre edge `3 → 4` (`center_dec` at
`h = 100`) and `0 < h`. -/
theorem role_decreasing_gen {h : ℕ} (hh : 0 < h) {κ : Kind} {β : LinearMap.BilinForm K (Fin h → K)}
    {β3 : LinearMap.BilinForm K (Cube h → K)} (hG : AGeom β β3)
    (hnbr : ∀ S T : Tri h, Nbr κ S T → β (ind S) (ind T) = 0)
    (hcd : ∀ j : Stage,
      ((cT (aCenter j 3, aCenter j 4)).map (cellDim h (eR (aCenter j 3, aCenter j 4)))).sum =
        ((cH (aCenter j 3, aCenter j 4)).map (cellDim h (eR (aCenter j 3, aCenter j 4)))).sum + h)
    (w : Role κ h) (e : Vertex κ h × Vertex κ h) (he : e ∈ edges w) :
    ((¬ labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2)) ↔
      ∃ j ι c, w = .center j ι c ∧ e = (.gate (.center j ι 3), .gate (.center j ι 4))) ∧
    (¬ labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2) →
      finrank K (labelSub β (vlabel e.1)) = finrank K (labelSub β (vlabel e.2)) + h) := by
  -- an increasing edge of a non-central role
  have inc : ∀ (hle : labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2)),
      (∀ j ι c, w = .center j ι c → e ≠ (.gate (.center j ι 3), .gate (.center j ι 4))) →
      ((¬ labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2)) ↔
        ∃ j ι c, w = .center j ι c ∧ e = (.gate (.center j ι 3), .gate (.center j ι 4))) ∧
      (¬ labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2) →
        finrank K (labelSub β (vlabel e.1)) = finrank K (labelSub β (vlabel e.2)) + h) := by
    intro hle hne
    refine ⟨⟨fun h' => (h' hle).elim, ?_⟩, fun h' => (h' hle).elim⟩
    rintro ⟨j, ι, c, hw, he'⟩
    exact (hne j ι c hw he').elim
  cases w with
  | X a =>
    obtain ⟨e', he', h1, h2⟩ := mem_edges_labels _ he
    refine inc ?_ (fun j ι c hw => by cases hw)
    rw [h1, h2]
    exact edge_inc hG.toFGeom (goodAll_role hnbr _ he') (classEdges_inc_X e' he')
  | Y a =>
    obtain ⟨e', he', h1, h2⟩ := mem_edges_labels _ he
    refine inc ?_ (fun j ι c hw => by cases hw)
    rw [h1, h2]
    exact edge_inc hG.toFGeom (goodAll_role hnbr _ he') (classEdges_inc_Y e' he')
  | side j ι p =>
    obtain ⟨e', he', h1, h2⟩ := mem_edges_labels _ he
    refine inc ?_ (fun j ι c hw => by cases hw)
    rw [h1, h2]
    exact edge_inc hG.toFGeom (goodAll_role hnbr _ he') (classEdges_inc_side j e' he')
  | center j ι c =>
    have hg : ∀ r, vlabel (Vertex.gate (κ := κ) (Gate.center j ι r)) =
        trLabel (roleNames (Role.center j ι c)) (aCenter j r) :=
      fun r => (trLabel_aCenter j ι r (fun _ => ι.1)).symm
    have hs : vlabel (Vertex.source (Role.center j ι c)) =
        trLabel (roleNames (Role.center j ι c)) [] := rfl
    have hk : vlabel (Vertex.sink (Role.center j ι c)) =
        trLabel (roleNames (Role.center j ι c)) [(.full, .full, .full)] := rfl
    have hmem : ∀ e' ∈ [(([] : ALabel), aCenter j 1), (aCenter j 1, aCenter j 3),
        (aCenter j 3, aCenter j 4), (aCenter j 4, aCenter j 6), (aCenter j 6, [(.full, .full, .full)])],
        GoodAll β (roleNames (Role.center j ι c)) (eR e') ∧ EdgeOK e' := by
      intro e' he'
      rw [← classEdges_center] at he'
      exact ⟨goodAll_role hnbr (Role.center j ι c) he', classEdges_ok _ e' he'⟩
    rw [edges_center] at he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · refine inc ?_ (fun j' ι' c' _ he' => by simp at he')
      rw [hs, hg]
      exact edge_inc hG.toFGeom (hmem (([] : ALabel), aCenter j 1) (by simp)).1
        (center_inc j (([] : ALabel), aCenter j 1) (by simp))
    · refine inc ?_ (fun j' ι' c' _ he' => by simp at he')
      rw [hg, hg]
      exact edge_inc hG.toFGeom (hmem (aCenter j 1, aCenter j 3) (by simp)).1
        (center_inc j (aCenter j 1, aCenter j 3) (by simp))
    · obtain ⟨hgd, hok⟩ := hmem (aCenter j 3, aCenter j 4) (by simp)
      have hfr : finrank K (labelSub β (vlabel (Vertex.gate (κ := κ) (Gate.center j ι 3)))) =
          finrank K (labelSub β (vlabel (Vertex.gate (κ := κ) (Gate.center j ι 4)))) + h := by
        rw [hg, hg, edge_finrank_tail hG hgd hok, edge_finrank_head hG hgd hok]
        exact hcd j
      have hnle : ¬ labelSub β (vlabel (Vertex.gate (κ := κ) (Gate.center j ι 3))) ≤
          labelSub β (vlabel (Vertex.gate (κ := κ) (Gate.center j ι 4))) := by
        intro hle
        have := Submodule.finrank_mono hle
        omega
      exact ⟨⟨fun _ => ⟨j, ι, c, rfl, rfl⟩, fun _ => hnle⟩, fun _ => hfr⟩
    · refine inc ?_ (fun j' ι' c' _ he' => by simp at he')
      rw [hg, hg]
      exact edge_inc hG.toFGeom (hmem (aCenter j 4, aCenter j 6) (by simp)).1
        (center_inc j (aCenter j 4, aCenter j 6) (by simp))
    · refine inc ?_ (fun j' ι' c' _ he' => by simp at he')
      rw [hg, hk]
      exact edge_inc hG.toFGeom (hmem (aCenter j 6, [(.full, .full, .full)]) (by simp)).1
        (center_inc j (aCenter j 6, [(.full, .full, .full)]) (by simp))

/-- At `h = 100`: the only decreasing edges are the central edges from time `3` to time `4`, and
each loses dimension `100` (the name-level loss is `center_dec`, by `decide`). -/
theorem role_decreasing {κ : Kind} {β : LinearMap.BilinForm K (Fin 100 → K)}
    {β3 : LinearMap.BilinForm K (Cube 100 → K)} (hG : AGeom β β3)
    (hnbr : ∀ S T : Tri 100, Nbr κ S T → β (ind S) (ind T) = 0)
    (w : Role κ 100) (e : Vertex κ 100 × Vertex κ 100) (he : e ∈ edges w) :
    ((¬ labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2)) ↔
      ∃ j ι c, w = .center j ι c ∧ e = (.gate (.center j ι 3), .gate (.center j ι 4))) ∧
    (¬ labelSub β (vlabel e.1) ≤ labelSub β (vlabel e.2) →
      finrank K (labelSub β (vlabel e.1)) = finrank K (labelSub β (vlabel e.2)) + 100) :=
  role_decreasing_gen (by norm_num) hG hnbr (fun j => (center_dec j).2) w e he

end SubNLogN.Math.Networks.WP6b
