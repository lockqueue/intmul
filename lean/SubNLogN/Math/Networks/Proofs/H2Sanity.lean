import SubNLogN.Math.Networks.Proofs.TotalsGen
import SubNLogN.Math.Networks.Proofs.Counting
import SubNLogN.Math.Networks.Proofs.CellSoundBit
import SubNLogN.Math.Networks.Proofs.Lemma6Bit
import SubNLogN.Math.Networks.Proofs.Lemma6CCor
import SubNLogN.S1.Params

/-!
# Network-certificate statement-fidelity self-checks at `h = 100` (`H2` reflects earlier-draft naming)

These checks confirm that the network-certificate statements at `h = 100` (the fields of `BitNetCert` and
`ComplexNetCert`, `Cert.lean`) are not vacuous:
* both role types are nonempty (`role_nonempty`), so the `∀ w` statements say something;
* every role has at least one edge. More precisely `(edges w).length = (touch w).length + 1`, which
  is `13` for bank roles and `5` for scratch roles (`length_edges`, `length_touch`, `edges_ne_nil`);
  every centre role has its edge `3 → 4` (`center_edge_mem`);
* the role counts are the exact integers `W_b`, `W_c` (`card_role_bit_100`, `card_role_complex_100`,
  from `cardRole_holds` and `S1.tripleWb_100`/`S1.tripleWc_100`);
* the deficits `s_b < W_b m` and `s_c < W_c m` are genuine strict inequalities (`deficit_*_100`);
* the name-level class sums at `h = 100` are the exact values `10⁶`, `10⁶ − 1` and `10⁶ + 200`
  (`classRankSum_100_*`, `classDimSum_100_*`, via `TotalsGenAux`), in particular positive;
* hence, given cell soundness (`Cell.SoundBitStmt`, `Cell.SoundComplexStmt`), every role has an
  edge of positive rational rank, resp. of positive residual dimension, and that residual is not
  `⊥` (`exists_pos_rank_of`, `exists_pos_resid_of`, `exists_resid_ne_bot_of`). The unconditional
  versions use the proved soundness theorems `Cell.soundBit_holds` and
  `WP6c.soundComplex_holds` (`exists_pos_rank_100`, `exists_pos_resid_100`, `exists_resid_ne_bot_100`).
  So the ONB statement `Lemma6OnbStmt` and the edge factorization `Prop8EdgeStmt` are not satisfied
  by empty bases alone;
* the `h = 100` [OAI26] Lemma 6 "decreasing" contracts (implication form) are not vacuous: some edges are
  decreasing, namely the centre edges `3 → 4` (`decreasing_bit_exists`,
  `decreasing_complex_exists`). This uses the iff-form general-`h` theorems
  `lemma6DecreasingBitGen_holds` and `WP6c.lemma6DecreasingComplexGen_holds` at `h = 100`.

No hypotheses are hidden: each statement lists exactly the contracts it is conditional on, and the
unconditional versions instantiate them with proved theorems.
-/

namespace SubNLogN.Math.Networks.H2Sanity

open Cell

/-! ### Roles and edges -/

/-- The triple `{0, 1, 2}` of `[100]`. -/
def tri0 : Tri 100 := ⟨{0, 1, 2}, by decide⟩

/-- The data index `({0,1,2}, {0,1,2}, {0,1,2})`. -/
def addr0 : Addr 100 := (tri0, tri0, tri0)

/-- Both role types at `h = 100` are nonempty. -/
theorem role_nonempty (κ : Kind) : Nonempty (Role κ 100) := ⟨.X addr0⟩

/-- Both role types at `h = 100` have positive cardinality. -/
theorem card_role_pos (κ : Kind) : 0 < Fintype.card (Role κ 100) :=
  @Fintype.card_pos _ _ (role_nonempty κ)

/-- Number of gates touching a role: `12` for bank roles, `4` for scratch roles. -/
theorem length_touch {κ : Kind} {h : ℕ} (w : Role κ h) :
    (touch w).length = (match w with | .X _ => 12 | .Y _ => 12 | _ => 4) := by
  cases w <;> simp [touch]

/-- Number of edges of a role: one more than the number of gates touching it. -/
theorem length_edges {κ : Kind} {h : ℕ} (w : Role κ h) :
    (edges w).length = (touch w).length + 1 := by
  simp [edges, vertices, List.length_zip]

/-- Every role has at least one edge. -/
theorem edges_ne_nil {κ : Kind} {h : ℕ} (w : Role κ h) : edges w ≠ [] := by
  intro h0
  have := length_edges w
  rw [h0, List.length_nil] at this
  omega

/-- Every centre role has the edge from its gate at time `3` to its gate at time `4`. -/
theorem center_edge_mem {κ : Kind} {h : ℕ} (j : Stage) (ι : Fix h) (c : Center κ h) :
    (Vertex.gate (.center j ι 3), Vertex.gate (.center j ι 4)) ∈
      edges (Role.center (κ := κ) j ι c) := by
  simp [edges, vertices, touch]

/-! ### Exact integers -/

/-- `|Role .bit 100| = W_b = 177176569091445000000`. -/
theorem card_role_bit_100 : Fintype.card (Role .bit 100) = 177176569091445000000 := by
  rw [(cardRole_holds 100).1, SubNLogN.S1.tripleWb_100]

/-- `|Role .complex 100| = W_c = 1873807244643542670000`. -/
theorem card_role_complex_100 : Fintype.card (Role .complex 100) = 1873807244643542670000 := by
  rw [(cardRole_holds 100).2, SubNLogN.S1.tripleWc_100]

/-- The bit deficit is a strict inequality: `s_b < W_b m`. -/
theorem deficit_bit_100 : tripleSb 100 < tripleWb 100 * tripleM 100 := by decide

/-- The complex deficit is a strict inequality: `s_c < W_c m`. -/
theorem deficit_complex_100 : tripleSc 100 < tripleWc 100 * tripleM 100 := by decide

/-! ### Class sums at `h = 100` (`m = 10⁶`, via the cubics of `TotalsGenAux`, `n = 98`) -/

section ClassSums

open TotalsGenAux

theorem classRankSum_100_X : classRankSum 100 .X = 1000000 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classRankSum_eq, classRankC_X]; rfl

theorem classRankSum_100_Y : classRankSum 100 .Y = 999999 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classRankSum_eq, classRankC_Y]; rfl

theorem classRankSum_100_side (j : Stage) : classRankSum 100 (.side j) = 1000000 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classRankSum_eq, classRankC_side]; rfl

theorem classRankSum_100_center (j : Stage) : classRankSum 100 (.center j) = 1000200 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classRankSum_eq, classRankC_center]; rfl

theorem classDimSum_100_X : classDimSum 100 .X = 999999 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classDimSum_eq, classDimC_X]; rfl

theorem classDimSum_100_Y : classDimSum 100 .Y = 999999 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classDimSum_eq, classDimC_Y]; rfl

theorem classDimSum_100_side (j : Stage) : classDimSum 100 (.side j) = 1000000 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classDimSum_eq, classDimC_side]; rfl

theorem classDimSum_100_center (j : Stage) : classDimSum 100 (.center j) = 1000200 := by
  rw [show (100 : ℕ) = 98 + 2 from rfl, classDimSum_eq, classDimC_center]; rfl

end ClassSums

theorem classRankSum_100_pos (c : RClass) : 0 < classRankSum 100 c := by
  cases c with
  | X => rw [classRankSum_100_X]; norm_num
  | Y => rw [classRankSum_100_Y]; norm_num
  | side j => rw [classRankSum_100_side]; norm_num
  | center j => rw [classRankSum_100_center]; norm_num

theorem classDimSum_100_pos (c : RClass) : 0 < classDimSum 100 c := by
  cases c with
  | X => rw [classDimSum_100_X]; norm_num
  | Y => rw [classDimSum_100_Y]; norm_num
  | side j => rw [classDimSum_100_side]; norm_num
  | center j => rw [classDimSum_100_center]; norm_num

/-! ### Edges of positive rank / positive residual dimension -/

/-- Given cell soundness (bit), every role at `h = 100` has an edge of positive rational rank. -/
theorem exists_pos_rank_of (hS : Cell.SoundBitStmt) (w : Role .bit 100) :
    ∃ e ∈ edges w, 0 < rankQ (edgeMatB e) := by
  by_contra hne
  push Not at hne
  have hzero : ((edges w).map fun e => rankQ (edgeMatB e)).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact Nat.le_zero.1 (hne e he)
  have hsum := hS w
  rw [hzero] at hsum
  exact (classRankSum_100_pos (classOf w)).ne hsum

/-- Given cell soundness (complex), every role at `h = 100` has an edge whose orthogonal residual
has positive dimension. -/
theorem exists_pos_resid_of (hS : Cell.SoundComplexStmt) (w : Role .complex 100) :
    ∃ e ∈ edges w, 0 < Module.finrank (ZMod 2) (residC e) := by
  by_contra hne
  push Not at hne
  have hzero : ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact Nat.le_zero.1 (hne e he)
  have hsum := hS w
  rw [hzero] at hsum
  exact (classDimSum_100_pos (classOf w)).ne hsum

/-- Given cell soundness (complex), every role at `h = 100` has an edge with nonzero residual (so
its orthonormal bases are nonempty). -/
theorem exists_resid_ne_bot_of (hS : Cell.SoundComplexStmt) (w : Role .complex 100) :
    ∃ e ∈ edges w, residC e ≠ ⊥ := by
  obtain ⟨e, he, hpos⟩ := exists_pos_resid_of hS w
  refine ⟨e, he, fun hbot => ?_⟩
  rw [hbot, finrank_bot] at hpos
  exact lt_irrefl 0 hpos

/-- Unconditional (proved bit soundness `Cell.soundBit_holds`): every bit role at `h = 100` has
an edge of positive rational rank. -/
theorem exists_pos_rank_100 (w : Role .bit 100) : ∃ e ∈ edges w, 0 < rankQ (edgeMatB e) :=
  exists_pos_rank_of Cell.soundBit_holds w

/-- Unconditional (proved complex soundness `WP6c.soundComplex_holds`): every complex role at
`h = 100` has an edge whose residual has positive dimension. -/
theorem exists_pos_resid_100 (w : Role .complex 100) :
    ∃ e ∈ edges w, 0 < Module.finrank (ZMod 2) (residC e) :=
  exists_pos_resid_of WP6c.soundComplex_holds w

/-- Unconditional: every complex role at `h = 100` has an edge with nonzero residual. -/
theorem exists_resid_ne_bot_100 (w : Role .complex 100) : ∃ e ∈ edges w, residC e ≠ ⊥ :=
  exists_resid_ne_bot_of WP6c.soundComplex_holds w

/-! ### The [OAI26] Lemma 6 "decreasing" contracts are not vacuous -/

/-- Some bit edges at `h = 100` are decreasing: the centre edges `3 → 4` (by the proved iff form
`lemma6DecreasingBitGen_holds` at `h = 100`). -/
theorem decreasing_bit_exists :
    ∃ (w : Role .bit 100) (e : Vertex .bit 100 × Vertex .bit 100),
      e ∈ edges w ∧ ¬ labB e.1 ≤ labB e.2 :=
  ⟨.center .one (tri0, tri0) (.inl 0), _, center_edge_mem .one (tri0, tri0) (.inl 0),
    ((lemma6DecreasingBitGen_holds 100 (by norm_num) (by norm_num) _ _
      (center_edge_mem .one (tri0, tri0) (.inl 0))).1).2 ⟨.one, (tri0, tri0), .inl 0, rfl, rfl⟩⟩

/-- Some complex edges at `h = 100` are decreasing: the centre edges `3 → 4` (by the proved iff
form `WP6c.lemma6DecreasingComplexGen_holds` at `h = 100`). -/
theorem decreasing_complex_exists :
    ∃ (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100),
      e ∈ edges w ∧ ¬ labC e.1 ≤ labC e.2 :=
  ⟨.center .one (tri0, tri0) (.inl 0), _, center_edge_mem .one (tri0, tri0) (.inl 0),
    ((WP6c.lemma6DecreasingComplexGen_holds 100 (by norm_num) _ _
      (center_edge_mem .one (tri0, tri0) (.inl 0))).1).2 ⟨.one, (tri0, tri0), .inl 0, rfl, rfl⟩⟩

end SubNLogN.Math.Networks.H2Sanity
