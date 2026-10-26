import SubNLogN.Math.Networks.GateValid
import SubNLogN.Math.Networks.Instances
import SubNLogN.Math.Networks.Proofs.FrameInvariant

/-!
# Networks: the gate-wire incidence library

Shared lemmas about the ordered gate lists `touch w`, the wire graphs (`vertices`, `edges`,
`edgeInto`), the row lookup `gateAt`, the declared incidence of the actual gates and the locality of
the scalar rows, for every `κ` and `h`. It builds on the incidence facts already proved in
`Proofs/FrameInvariant.lean` (namespace `FI`: `touch_pairwise`, `touch_inv`, `touch_unique`,
`gateAt_eq_some_iff`, `edgeInto_gate`, `edgeInto_sink`, `rowUpd_untouched`, `rowUpd_local`, ...),
which are not repeated here.

* (a) `touch_sorted` (ordered by (stage, time)), `touch_nodup`, `vertices_nodup`, `edges_nodup`;
* (b) `gateAt_eq_none_iff`, `gateAt_isSome_iff`, `invOf_of_gateAt_isSome`, explicit `gateAt_X/Y/side/center`;
* (c) `edges_eq`, `mem_edges_iff`, `edgeInto_eq_some_iff`, `sum_edges`, the previous vertex
  (`vtxAt_clk_of_head`, `vtxAt_clk_of_consec`, `vtxAt_24_of_last`), literal `touch_X_eq`, ...,
  `edges_side`, `edges_center`;
* (d) `Incident` (the declared gate-wire incidence predicate) and `mem_touch_iff`; the supports `supp` explicitly;
* (e) locality of the rows; invocations of one stage touch disjoint roles;
* (f) counts: `|touch w| ∈ {12, 4}`, `|edges w| = |touch w| + 1 ≤ 13`, `Σ_w |touch w| = Σ_g |supp g|`;
* (g) invocations and stages: locality, and the sequential (fold) forms of the simultaneous
  definitions (`framedStage_eq_foldl`, `preEdges_eq_foldl`, `sinkEdges_eq_foldl`, ...).
-/

namespace SubNLogN.Math.Networks.Incidence

variable {κ : Kind} {h : ℕ}

/-! ## (a) Order and duplicate-freeness -/

/-- The circuit order of gates, by (stage, time). -/
def StageTimeLT (a b : Gate h) : Prop :=
  FI.stIdx a.stage < FI.stIdx b.stage ∨ (a.stage = b.stage ∧ a.time < b.time)

/-- The clock order `FI.clk` is the (stage, time) order. -/
theorem clk_lt_iff (a b : Gate h) : FI.clk a < FI.clk b ↔ StageTimeLT a b := by
  have ha := a.time.isLt
  have hb := b.time.isLt
  unfold FI.clk StageTimeLT
  constructor
  · intro hlt
    by_cases hs : a.stage = b.stage
    · refine Or.inr ⟨hs, ?_⟩
      rw [hs] at hlt
      exact Fin.lt_def.2 (by omega)
    · refine Or.inl ?_
      have hne : FI.stIdx a.stage ≠ FI.stIdx b.stage := fun h' => hs (FI.stIdx_inj h')
      omega
  · rintro (hlt | ⟨hs, ht⟩)
    · omega
    · rw [hs]
      have := Fin.lt_def.1 ht
      omega

/-- `touch w` is ordered by (stage, time) (the circuit dependency order of the wire). -/
theorem touch_sorted (w : Role κ h) : (touch w).Pairwise StageTimeLT :=
  (FI.touch_pairwise w).imp fun hab => (clk_lt_iff _ _).1 hab

/-- `touch w` is duplicate-free. -/
theorem touch_nodup (w : Role κ h) : (touch w).Nodup :=
  (FI.touch_pairwise w).imp fun hab heq => by subst heq; exact lt_irrefl _ hab

/-- `vertices w` is duplicate-free. -/
theorem vertices_nodup (w : Role κ h) : (vertices w).Nodup := by
  have hg : ((touch w).map (Vertex.gate (κ := κ))).Nodup := by
    refine (touch_nodup w).map ?_
    intro a b hab
    exact Vertex.gate.inj hab
  rw [FI.vertices_eq, List.nodup_cons, List.nodup_append]
  refine ⟨?_, hg, List.nodup_singleton _, ?_⟩
  · simp
  · simp

/-- The heads of the edges of `w` are the vertices of `w` after its source. -/
theorem edges_map_snd (w : Role κ h) : (edges w).map Prod.snd = (vertices w).tail := by
  unfold edges
  exact List.map_snd_zip (by simp)

/-- `edges w` is duplicate-free (its heads already are). -/
theorem edges_nodup (w : Role κ h) : (edges w).Nodup := by
  have hn : ((edges w).map Prod.snd).Nodup := by
    rw [edges_map_snd]
    exact (vertices_nodup w).sublist (List.tail_sublist _)
  exact hn.of_map _

/-- Two edges of `w` with the same head are equal. -/
theorem eq_of_mem_edges {w : Role κ h} {e e' : Vertex κ h × Vertex κ h} (he : e ∈ edges w)
    (he' : e' ∈ edges w) (h2 : e.2 = e'.2) : e = e' := by
  have hn : ((edges w).map Prod.snd).Nodup := by
    rw [edges_map_snd]
    exact (vertices_nodup w).sublist (List.tail_sublist _)
  exact List.inj_on_of_nodup_map hn he he' h2

/-! ## (b) The row lookup `gateAt` (see also `FI.gateAt_eq_some_iff`) -/

theorem gateAt_eq_none_iff {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h} :
    gateAt j ι r w = none ↔ ∀ g ∈ touch w, ¬ (g.stage = j ∧ g.inv = ι ∧ g.time = r) := by
  refine ⟨FI.gateAt_none, fun hno => ?_⟩
  unfold gateAt
  rw [List.find?_eq_none]
  intro g hg hc
  exact hno g hg (by simpa using hc)

theorem gateAt_isSome_iff {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h} :
    (gateAt j ι r w).isSome ↔ ∃ g ∈ touch w, g.stage = j ∧ g.inv = ι ∧ g.time = r := by
  constructor
  · intro hs
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨g, (FI.gateAt_spec hg).1, (FI.gateAt_spec hg).2⟩
  · rintro ⟨g, hm, hs, hi, ht⟩
    rw [FI.gateAt_of_mem hm hs hi ht]
    rfl

/-- A wire with a gate at `(j, ι, r)` belongs to invocation `ι` of stage `j`. -/
theorem invOf_of_gateAt_eq_some {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h} {g : Gate h}
    (hg : gateAt j ι r w = some g) : invOf j w = some ι := by
  obtain ⟨hm, hs, hi, -⟩ := FI.gateAt_spec hg
  rw [← hs, ← hi]
  exact FI.touch_inv w g hm

theorem invOf_of_gateAt_isSome {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h}
    (hw : (gateAt j ι r w).isSome) : invOf j w = some ι := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hw
  exact invOf_of_gateAt_eq_some hg

theorem gateAt_eq_none_of_invOf_ne {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h}
    (hw : invOf j w ≠ some ι) : gateAt j ι r w = none := by
  cases hg : gateAt j ι r w with
  | none => rfl
  | some g => exact absurd (invOf_of_gateAt_eq_some hg) hw

/-! ## (d) Declared incidence and the supports of the actual gates -/

/-- The physical `Y` triple of a side wire at stage `j` (the triple of its `Y`-side gates). -/
def sideY (j : Stage) (p : SideIdx κ h) : Tri h := if j.isInverse then p.1.2 else p.1.1

/-- The physical `X` triple of a side wire at stage `j` (the triple of its `X`-side gates). -/
def sideX (j : Stage) (p : SideIdx κ h) : Tri h := if j.isInverse then p.1.1 else p.1.2

theorem mk_fix_var (j : Stage) (a : Addr h) : Addr.mk j (a.fix j) (a.var j) = a := by
  cases j <;> rfl

theorem eq_mk_iff {j : Stage} {ι : Fix h} {t : Tri h} {a : Addr h} :
    a = Addr.mk j ι t ↔ a.fix j = ι ∧ a.var j = t := by
  constructor
  · rintro rfl
    exact ⟨FI.fix_mk j ι t, FI.var_mk j ι t⟩
  · rintro ⟨rfl, rfl⟩
    exact (mk_fix_var j a).symm

/-! ### Physical incidence: which gates touch a given role -/

theorem side_mem_touch_X {j : Stage} {ι : Fix h} {r : Fin 8} {t : Tri h} {a : Addr h} :
    Gate.side j ι r t ∈ touch (.X a : Role κ h) ↔ a.fix j = ι ∧ a.var j = t ∧ (r = 2 ∨ r = 7) := by
  constructor
  · intro hm
    simp only [touch, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨j', -, hj'⟩ := hm
    rcases hj' with h1 | h1 | h1 | h1 <;> simp only [Gate.side.injEq, reduceCtorEq] at h1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, rfl, Or.inl rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, rfl, Or.inr rfl⟩
  · rintro ⟨hι, ht, hr⟩
    exact FI.mem_touch_X hι ht r hr

theorem center_mem_touch_X {j : Stage} {ι : Fix h} {r : Fin 8} {a : Addr h} :
    Gate.center j ι r ∈ touch (.X a : Role κ h) ↔ a.fix j = ι ∧ (r = 3 ∨ r = 6) := by
  constructor
  · intro hm
    simp only [touch, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨j', -, hj'⟩ := hm
    rcases hj' with h1 | h1 | h1 | h1 <;> simp only [Gate.center.injEq, reduceCtorEq] at h1
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inl rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inr rfl⟩
  · rintro ⟨hι, hr⟩
    exact FI.mem_touch_X_center hι r hr

theorem side_mem_touch_Y {j : Stage} {ι : Fix h} {r : Fin 8} {t : Tri h} {a : Addr h} :
    Gate.side j ι r t ∈ touch (.Y a : Role κ h) ↔ a.fix j = ι ∧ a.var j = t ∧ (r = 0 ∨ r = 5) := by
  constructor
  · intro hm
    simp only [touch, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨j', -, hj'⟩ := hm
    rcases hj' with h1 | h1 | h1 | h1 <;> simp only [Gate.side.injEq, reduceCtorEq] at h1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, rfl, Or.inl rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, rfl, Or.inr rfl⟩
  · rintro ⟨hι, ht, hr⟩
    exact FI.mem_touch_Y hι ht r hr

theorem center_mem_touch_Y {j : Stage} {ι : Fix h} {r : Fin 8} {a : Addr h} :
    Gate.center j ι r ∈ touch (.Y a : Role κ h) ↔ a.fix j = ι ∧ (r = 1 ∨ r = 4) := by
  constructor
  · intro hm
    simp only [touch, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨j', -, hj'⟩ := hm
    rcases hj' with h1 | h1 | h1 | h1 <;> simp only [Gate.center.injEq, reduceCtorEq] at h1
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inl rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨rfl, Or.inr rfl⟩
  · rintro ⟨hι, hr⟩
    exact FI.mem_touch_Y_center hι r hr

theorem side_mem_touch_side {j j' : Stage} {ι ι' : Fix h} {r : Fin 8} {t : Tri h}
    {p : SideIdx κ h} :
    Gate.side j ι r t ∈ touch (.side j' ι' p : Role κ h) ↔
      j' = j ∧ ι' = ι ∧ (((r = 0 ∨ r = 5) ∧ sideY j p = t) ∨ ((r = 2 ∨ r = 7) ∧ sideX j p = t)) := by
  simp only [touch, List.mem_cons, List.not_mem_nil, or_false, Gate.side.injEq, sideY, sideX]
  constructor
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · exact ⟨rfl, rfl, Or.inl ⟨Or.inl rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, Or.inr ⟨Or.inl rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, Or.inl ⟨Or.inr rfl, rfl⟩⟩
    · exact ⟨rfl, rfl, Or.inr ⟨Or.inr rfl, rfl⟩⟩
  · rintro ⟨rfl, rfl, (⟨rfl | rfl, rfl⟩ | ⟨rfl | rfl, rfl⟩)⟩
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))

theorem center_mem_touch_center {j j' : Stage} {ι ι' : Fix h} {r : Fin 8} {c : Center κ h} :
    Gate.center j ι r ∈ touch (.center j' ι' c : Role κ h) ↔
      j' = j ∧ ι' = ι ∧ (r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 6) := by
  simp only [touch, List.mem_cons, List.not_mem_nil, or_false, Gate.center.injEq]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact ⟨rfl, rfl, Or.inl rfl⟩
    · exact ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨rfl, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨rfl, rfl, Or.inr (Or.inr (Or.inr rfl))⟩
  · rintro ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))

theorem center_not_mem_touch_side {j j' : Stage} {ι ι' : Fix h} {r : Fin 8} {p : SideIdx κ h} :
    Gate.center j ι r ∉ touch (.side j' ι' p : Role κ h) := by
  simp [touch]

theorem side_not_mem_touch_center {j j' : Stage} {ι ι' : Fix h} {r : Fin 8} {t : Tri h}
    {c : Center κ h} : Gate.side j ι r t ∉ touch (.center j' ι' c : Role κ h) := by
  simp [touch]

/-- **Physical incidence**: a side gate at a `Y`-side row (`0, 5`) touches the data role
`Y_{(j, ι, t)}` and the side roles of `(j, ι)` with physical `Y` triple `t`; at an `X`-side row
(`2, 7`) the same with `X`; a centre gate at a `Y`-centre row (`1, 4`) touches the whole `Y` bank of
`(j, ι)` and all its centres; at an `X`-centre row (`3, 6`) the same with `X`. Other gates touch
nothing. -/
def IncidentPhys (κ : Kind) : Gate h → Role κ h → Prop
  | .side j ι r t, w =>
      ((r = 0 ∨ r = 5) ∧
        (w = .Y (Addr.mk j ι t) ∨ ∃ p : SideIdx κ h, sideY j p = t ∧ w = .side j ι p)) ∨
      ((r = 2 ∨ r = 7) ∧
        (w = .X (Addr.mk j ι t) ∨ ∃ p : SideIdx κ h, sideX j p = t ∧ w = .side j ι p))
  | .center j ι r, w =>
      ((r = 1 ∨ r = 4) ∧ ((∃ S, w = .Y (Addr.mk j ι S)) ∨ ∃ c, w = .center j ι c)) ∨
      ((r = 3 ∨ r = 6) ∧ ((∃ S, w = .X (Addr.mk j ι S)) ∨ ∃ c, w = .center j ι c))

/-- Incidence completeness, physical form: `touch` lists exactly the physically incident gates. -/
theorem mem_touch_iff_phys {g : Gate h} {w : Role κ h} : g ∈ touch w ↔ IncidentPhys κ g w := by
  cases g with
  | side j ι r t =>
    cases w with
    | X a =>
      rw [side_mem_touch_X]
      constructor
      · rintro ⟨hι, ht, hr⟩
        exact Or.inr ⟨hr, Or.inl (by rw [← hι, ← ht, mk_fix_var])⟩
      · rintro (⟨-, hw | ⟨p, -, hw⟩⟩ | ⟨hr, hw | ⟨p, -, hw⟩⟩)
        · cases hw
        · cases hw
        · cases hw
          exact ⟨FI.fix_mk j ι t, FI.var_mk j ι t, hr⟩
        · cases hw
    | Y a =>
      rw [side_mem_touch_Y]
      constructor
      · rintro ⟨hι, ht, hr⟩
        exact Or.inl ⟨hr, Or.inl (by rw [← hι, ← ht, mk_fix_var])⟩
      · rintro (⟨hr, hw | ⟨p, -, hw⟩⟩ | ⟨-, hw | ⟨p, -, hw⟩⟩)
        · cases hw
          exact ⟨FI.fix_mk j ι t, FI.var_mk j ι t, hr⟩
        · cases hw
        · cases hw
        · cases hw
    | side j' ι' p =>
      rw [side_mem_touch_side]
      constructor
      · rintro ⟨rfl, rfl, (⟨hr, ht⟩ | ⟨hr, ht⟩)⟩
        · exact Or.inl ⟨hr, Or.inr ⟨p, ht, rfl⟩⟩
        · exact Or.inr ⟨hr, Or.inr ⟨p, ht, rfl⟩⟩
      · rintro (⟨hr, hw | ⟨q, ht, hw⟩⟩ | ⟨hr, hw | ⟨q, ht, hw⟩⟩)
        · cases hw
        · cases hw
          exact ⟨rfl, rfl, Or.inl ⟨hr, ht⟩⟩
        · cases hw
        · cases hw
          exact ⟨rfl, rfl, Or.inr ⟨hr, ht⟩⟩
    | center j' ι' c =>
      refine iff_of_false side_not_mem_touch_center ?_
      rintro (⟨-, hw | ⟨p, -, hw⟩⟩ | ⟨-, hw | ⟨p, -, hw⟩⟩) <;> cases hw
  | center j ι r =>
    cases w with
    | X a =>
      rw [center_mem_touch_X]
      constructor
      · rintro ⟨hι, hr⟩
        exact Or.inr ⟨hr, Or.inl ⟨a.var j, by rw [← hι, mk_fix_var]⟩⟩
      · rintro (⟨-, ⟨S, hw⟩ | ⟨c, hw⟩⟩ | ⟨hr, ⟨S, hw⟩ | ⟨c, hw⟩⟩)
        · cases hw
        · cases hw
        · cases hw
          exact ⟨FI.fix_mk j ι S, hr⟩
        · cases hw
    | Y a =>
      rw [center_mem_touch_Y]
      constructor
      · rintro ⟨hι, hr⟩
        exact Or.inl ⟨hr, Or.inl ⟨a.var j, by rw [← hι, mk_fix_var]⟩⟩
      · rintro (⟨hr, ⟨S, hw⟩ | ⟨c, hw⟩⟩ | ⟨-, ⟨S, hw⟩ | ⟨c, hw⟩⟩)
        · cases hw
          exact ⟨FI.fix_mk j ι S, hr⟩
        · cases hw
        · cases hw
        · cases hw
    | side j' ι' p =>
      refine iff_of_false center_not_mem_touch_side ?_
      rintro (⟨-, ⟨S, hw⟩ | ⟨c, hw⟩⟩ | ⟨-, ⟨S, hw⟩ | ⟨c, hw⟩⟩) <;> cases hw
    | center j' ι' c =>
      rw [center_mem_touch_center]
      constructor
      · rintro ⟨rfl, rfl, hr⟩
        rcases hr with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨Or.inl rfl, Or.inr ⟨c, rfl⟩⟩
        · exact Or.inr ⟨Or.inl rfl, Or.inr ⟨c, rfl⟩⟩
        · exact Or.inl ⟨Or.inr rfl, Or.inr ⟨c, rfl⟩⟩
        · exact Or.inr ⟨Or.inr rfl, Or.inr ⟨c, rfl⟩⟩
      · rintro (⟨hr, ⟨S, hw⟩ | ⟨c', hw⟩⟩ | ⟨hr, ⟨S, hw⟩ | ⟨c', hw⟩⟩)
        · cases hw
        · cases hw
          rcases hr with rfl | rfl
          · exact ⟨rfl, rfl, Or.inl rfl⟩
          · exact ⟨rfl, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
        · cases hw
        · cases hw
          rcases hr with rfl | rfl
          · exact ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩
          · exact ⟨rfl, rfl, Or.inr (Or.inr (Or.inr rfl))⟩

theorem fwdOp_eq_J_iff (r : Fin 8) : fwdOp r = .J ↔ r = 0 ∨ r = 5 := by revert r; decide
theorem fwdOp_eq_V_iff (r : Fin 8) : fwdOp r = .V ↔ r = 2 ∨ r = 7 := by revert r; decide
theorem fwdOp_eq_R_iff (r : Fin 8) : fwdOp r = .R ↔ r = 1 ∨ r = 4 := by revert r; decide
theorem fwdOp_eq_G_iff (r : Fin 8) : fwdOp r = .G ↔ r = 3 ∨ r = 6 := by revert r; decide
theorem fwdOp_rev_eq_J_iff (r : Fin 8) : fwdOp r.rev = .J ↔ r = 2 ∨ r = 7 := by revert r; decide
theorem fwdOp_rev_eq_V_iff (r : Fin 8) : fwdOp r.rev = .V ↔ r = 0 ∨ r = 5 := by revert r; decide
theorem fwdOp_rev_eq_R_iff (r : Fin 8) : fwdOp r.rev = .R ↔ r = 3 ∨ r = 6 := by revert r; decide
theorem fwdOp_rev_eq_G_iff (r : Fin 8) : fwdOp r.rev = .G ↔ r = 1 ∨ r = 4 := by revert r; decide

/-- **Declared incidence** (with the logical banks of `srcRole`/`tgtRole`): a
`J`-gate indexed by `S` (side gate at a `J` row) touches the logical target `y_S` and exactly the side
roles `A_{ST}`; a `V`-gate indexed by `T` touches the logical source `x_T` and exactly the side roles
`A_{ST}`; an `R`-gate (centre gate at an `R` row) touches the whole logical target bank and all
centres; a `G`-gate touches the whole logical source bank and all centres. Side gates at centre rows
and centre gates at side rows (not actual gates) touch nothing. -/
def Incident (κ : Kind) : Gate h → Role κ h → Prop
  | .side j ι r t, w =>
      (rowOp j r = .J ∧ (w = tgtRole j ι t ∨ ∃ p : SideIdx κ h, p.1.1 = t ∧ w = .side j ι p)) ∨
      (rowOp j r = .V ∧ (w = srcRole j ι t ∨ ∃ p : SideIdx κ h, p.1.2 = t ∧ w = .side j ι p))
  | .center j ι r, w =>
      (rowOp j r = .R ∧ ((∃ S, w = tgtRole j ι S) ∨ ∃ c, w = .center j ι c)) ∨
      (rowOp j r = .G ∧ ((∃ S, w = srcRole j ι S) ∨ ∃ c, w = .center j ι c))

theorem incidentPhys_iff_incident {g : Gate h} {w : Role κ h} :
    IncidentPhys κ g w ↔ Incident κ g w := by
  cases g with
  | side j ι r t =>
    cases hj : j.isInverse
    · simp only [IncidentPhys, Incident, rowOp, tgtRole, srcRole, sideY, sideX, hj,
        Bool.false_eq_true, ↓reduceIte, fwdOp_eq_J_iff, fwdOp_eq_V_iff]
    · simp only [IncidentPhys, Incident, rowOp, tgtRole, srcRole, sideY, sideX, hj, ↓reduceIte,
        fwdOp_rev_eq_J_iff, fwdOp_rev_eq_V_iff]
      exact or_comm
  | center j ι r =>
    cases hj : j.isInverse
    · simp only [IncidentPhys, Incident, rowOp, tgtRole, srcRole, hj, Bool.false_eq_true,
        ↓reduceIte, fwdOp_eq_R_iff, fwdOp_eq_G_iff]
    · simp only [IncidentPhys, Incident, rowOp, tgtRole, srcRole, hj, ↓reduceIte,
        fwdOp_rev_eq_R_iff, fwdOp_rev_eq_G_iff]
      exact or_comm

/-- **Incidence theorem** (matching the gate touch lists): `touch w` lists exactly the gates declared incident
to `w`. -/
theorem mem_touch_iff {g : Gate h} {w : Role κ h} : g ∈ touch w ↔ Incident κ g w :=
  mem_touch_iff_phys.trans incidentPhys_iff_incident

/-- Incidence theorem, with validity: `g ∈ touch w ↔ g.Valid ∧ Incident κ g w`. -/
theorem mem_touch_iff_valid {g : Gate h} {w : Role κ h} :
    g ∈ touch w ↔ g.Valid ∧ Incident κ g w :=
  ⟨fun hm => ⟨touch_valid w g hm, mem_touch_iff.1 hm⟩, fun hi => mem_touch_iff.2 hi.2⟩

theorem Incident.valid {g : Gate h} {w : Role κ h} (hi : Incident κ g w) : g.Valid :=
  touch_valid w g (mem_touch_iff.2 hi)

/-! ### Supports -/

/-- The support of a gate: the roles it touches. -/
def supp (κ : Kind) (g : Gate h) : Finset (Role κ h) := Finset.univ.filter fun w => g ∈ touch w

theorem mem_supp {g : Gate h} {w : Role κ h} : w ∈ supp κ g ↔ g ∈ touch w := by
  simp [supp]

theorem tgtRole_injective (j : Stage) (ι : Fix h) : Function.Injective (tgtRole (κ := κ) j ι) := by
  intro S S' hS
  have hmk : Addr.mk j ι S = Addr.mk j ι S' := by
    unfold tgtRole at hS
    split_ifs at hS
    · exact Role.X.inj hS
    · exact Role.Y.inj hS
  simpa [FI.var_mk] using congrArg (Addr.var j) hmk

theorem srcRole_injective (j : Stage) (ι : Fix h) : Function.Injective (srcRole (κ := κ) j ι) := by
  intro S S' hS
  have hmk : Addr.mk j ι S = Addr.mk j ι S' := by
    unfold srcRole at hS
    split_ifs at hS
    · exact Role.Y.inj hS
    · exact Role.X.inj hS
  simpa [FI.var_mk] using congrArg (Addr.var j) hmk

/-- The logical target data roles of invocation `(j, ι)`. -/
def tgtEmb (j : Stage) (ι : Fix h) : Tri h ↪ Role κ h := ⟨tgtRole j ι, tgtRole_injective j ι⟩

/-- The logical source data roles of invocation `(j, ι)`. -/
def srcEmb (j : Stage) (ι : Fix h) : Tri h ↪ Role κ h := ⟨srcRole j ι, srcRole_injective j ι⟩

/-- The side roles of invocation `(j, ι)`. -/
def sideEmb (j : Stage) (ι : Fix h) : SideIdx κ h ↪ Role κ h :=
  ⟨fun p => .side j ι p, fun _ _ hpq => (Role.side.inj hpq).2.2⟩

/-- The central roles of invocation `(j, ι)`. -/
def centerEmb (j : Stage) (ι : Fix h) : Center κ h ↪ Role κ h :=
  ⟨fun c => .center j ι c, fun _ _ hcd => (Role.center.inj hcd).2.2⟩

/-- Support of a `J`-gate: `y_t` and the side roles `A_{t·}`. -/
theorem supp_side_of_J {j : Stage} {ι : Fix h} {r : Fin 8} {t : Tri h} (hr : rowOp j r = .J) :
    supp κ (.side j ι r t) = insert (tgtRole j ι t)
      ((Finset.univ.filter fun p : SideIdx κ h => p.1.1 = t).map (sideEmb j ι)) := by
  ext w
  rw [mem_supp, mem_touch_iff, Finset.mem_insert, Finset.mem_map]
  simp only [Incident, hr, true_and, reduceCtorEq, false_and, or_false, Finset.mem_filter,
    Finset.mem_univ, sideEmb]
  constructor
  · rintro (hw | ⟨p, hp, rfl⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (hw | ⟨p, hp, rfl⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨p, hp, rfl⟩

/-- Support of a `V`-gate: `x_t` and the side roles `A_{·t}`. -/
theorem supp_side_of_V {j : Stage} {ι : Fix h} {r : Fin 8} {t : Tri h} (hr : rowOp j r = .V) :
    supp κ (.side j ι r t) = insert (srcRole j ι t)
      ((Finset.univ.filter fun p : SideIdx κ h => p.1.2 = t).map (sideEmb j ι)) := by
  ext w
  rw [mem_supp, mem_touch_iff, Finset.mem_insert, Finset.mem_map]
  simp only [Incident, hr, true_and, reduceCtorEq, false_and, false_or, Finset.mem_filter,
    Finset.mem_univ, sideEmb]
  constructor
  · rintro (hw | ⟨p, hp, rfl⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (hw | ⟨p, hp, rfl⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨p, hp, rfl⟩

/-- Support of an `R`-gate: the whole logical target bank and all centres of `(j, ι)`. -/
theorem supp_center_of_R {j : Stage} {ι : Fix h} {r : Fin 8} (hr : rowOp j r = .R) :
    supp κ (.center j ι r) = Finset.univ.map (tgtEmb j ι) ∪ Finset.univ.map (centerEmb j ι) := by
  ext w
  rw [mem_supp, mem_touch_iff, Finset.mem_union, Finset.mem_map, Finset.mem_map]
  simp only [Incident, hr, true_and, reduceCtorEq, false_and, or_false, Finset.mem_univ,
    tgtEmb, centerEmb, Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨S, rfl⟩ | ⟨c, rfl⟩)
    · exact Or.inl ⟨S, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨S, rfl⟩ | ⟨c, rfl⟩)
    · exact Or.inl ⟨S, rfl⟩
    · exact Or.inr ⟨c, rfl⟩

/-- Support of a `G`-gate: the whole logical source bank and all centres of `(j, ι)`. -/
theorem supp_center_of_G {j : Stage} {ι : Fix h} {r : Fin 8} (hr : rowOp j r = .G) :
    supp κ (.center j ι r) = Finset.univ.map (srcEmb j ι) ∪ Finset.univ.map (centerEmb j ι) := by
  ext w
  rw [mem_supp, mem_touch_iff, Finset.mem_union, Finset.mem_map, Finset.mem_map]
  simp only [Incident, hr, true_and, reduceCtorEq, false_and, false_or, Finset.mem_univ,
    srcEmb, centerEmb, Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨S, rfl⟩ | ⟨c, rfl⟩)
    · exact Or.inl ⟨S, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨S, rfl⟩ | ⟨c, rfl⟩)
    · exact Or.inl ⟨S, rfl⟩
    · exact Or.inr ⟨c, rfl⟩

/-- A gate that is not an actual gate touches nothing. -/
theorem supp_eq_empty {g : Gate h} (hg : ¬ g.Valid) : supp κ g = ∅ := by
  ext w
  rw [mem_supp]
  constructor
  · intro hm
    exact absurd (touch_valid w g hm) hg
  · intro hm
    simp at hm

/-- Gates of different invocations of one stage have disjoint supports. -/
theorem disjoint_supp_of_inv_ne {g g' : Gate h} (hs : g.stage = g'.stage) (hi : g.inv ≠ g'.inv) :
    Disjoint (supp κ g) (supp κ g') := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  have h1 := FI.touch_inv w g (mem_supp.1 hw)
  have h2 := FI.touch_inv w g' (mem_supp.1 hw')
  rw [hs, h2] at h1
  exact hi (Option.some.inj h1).symm

/-- Distinct gates of one stage and time (in particular distinct gates of one row) have disjoint
supports. -/
theorem disjoint_supp_of_ne {g g' : Gate h} (hs : g.stage = g'.stage) (ht : g.time = g'.time)
    (hne : g ≠ g') : Disjoint (supp κ g) (supp κ g') := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  exact hne (FI.touch_unique (mem_supp.1 hw) (mem_supp.1 hw') hs ht)

/-! ## (b') Explicit values of `gateAt` -/

theorem gateAt_X {j : Stage} {ι : Fix h} {r : Fin 8} {a : Addr h} :
    gateAt j ι r (.X a : Role κ h) =
      if a.fix j = ι ∧ (r = 2 ∨ r = 7) then some (.side j ι r (a.var j))
      else if a.fix j = ι ∧ (r = 3 ∨ r = 6) then some (.center j ι r) else none := by
  split_ifs with h1 h2
  · exact FI.gateAt_of_mem (side_mem_touch_X.2 ⟨h1.1, rfl, h1.2⟩) rfl rfl rfl
  · exact FI.gateAt_of_mem (center_mem_touch_X.2 h2) rfl rfl rfl
  · rw [gateAt_eq_none_iff]
    rintro (⟨j', ι', r', t'⟩ | ⟨j', ι', r'⟩) hg ⟨hs, hi, ht⟩
    · simp only [Gate.stage, Gate.inv, Gate.time] at hs hi ht
      subst hs hi ht
      exact h1 ⟨(side_mem_touch_X.1 hg).1, (side_mem_touch_X.1 hg).2.2⟩
    · simp only [Gate.stage, Gate.inv, Gate.time] at hs hi ht
      subst hs hi ht
      exact h2 (center_mem_touch_X.1 hg)

theorem gateAt_Y {j : Stage} {ι : Fix h} {r : Fin 8} {a : Addr h} :
    gateAt j ι r (.Y a : Role κ h) =
      if a.fix j = ι ∧ (r = 0 ∨ r = 5) then some (.side j ι r (a.var j))
      else if a.fix j = ι ∧ (r = 1 ∨ r = 4) then some (.center j ι r) else none := by
  split_ifs with h1 h2
  · exact FI.gateAt_of_mem (side_mem_touch_Y.2 ⟨h1.1, rfl, h1.2⟩) rfl rfl rfl
  · exact FI.gateAt_of_mem (center_mem_touch_Y.2 h2) rfl rfl rfl
  · rw [gateAt_eq_none_iff]
    rintro (⟨j', ι', r', t'⟩ | ⟨j', ι', r'⟩) hg ⟨hs, hi, ht⟩
    · simp only [Gate.stage, Gate.inv, Gate.time] at hs hi ht
      subst hs hi ht
      exact h1 ⟨(side_mem_touch_Y.1 hg).1, (side_mem_touch_Y.1 hg).2.2⟩
    · simp only [Gate.stage, Gate.inv, Gate.time] at hs hi ht
      subst hs hi ht
      exact h2 (center_mem_touch_Y.1 hg)

theorem gateAt_side {j j' : Stage} {ι ι' : Fix h} {r : Fin 8} {p : SideIdx κ h} :
    gateAt j ι r (.side j' ι' p : Role κ h) =
      if j' = j ∧ ι' = ι ∧ (r = 0 ∨ r = 5) then some (.side j ι r (sideY j p))
      else if j' = j ∧ ι' = ι ∧ (r = 2 ∨ r = 7) then some (.side j ι r (sideX j p))
      else none := by
  split_ifs with h1 h2
  · exact FI.gateAt_of_mem (side_mem_touch_side.2 ⟨h1.1, h1.2.1, Or.inl ⟨h1.2.2, rfl⟩⟩) rfl rfl rfl
  · exact FI.gateAt_of_mem (side_mem_touch_side.2 ⟨h2.1, h2.2.1, Or.inr ⟨h2.2.2, rfl⟩⟩) rfl rfl rfl
  · rw [gateAt_eq_none_iff]
    rintro (⟨j'', ι'', r'', t''⟩ | ⟨j'', ι'', r''⟩) hg ⟨hs, hi, ht⟩
    · simp only [Gate.stage, Gate.inv, Gate.time] at hs hi ht
      subst hs hi ht
      obtain ⟨hj, hι, (⟨hr, -⟩ | ⟨hr, -⟩)⟩ := side_mem_touch_side.1 hg
      · exact h1 ⟨hj, hι, hr⟩
      · exact h2 ⟨hj, hι, hr⟩
    · exact absurd hg center_not_mem_touch_side

theorem gateAt_center {j j' : Stage} {ι ι' : Fix h} {r : Fin 8} {c : Center κ h} :
    gateAt j ι r (.center j' ι' c : Role κ h) =
      if j' = j ∧ ι' = ι ∧ (r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 6) then some (.center j ι r) else none := by
  split_ifs with h1
  · exact FI.gateAt_of_mem (center_mem_touch_center.2 h1) rfl rfl rfl
  · rw [gateAt_eq_none_iff]
    rintro (⟨j'', ι'', r'', t''⟩ | ⟨j'', ι'', r''⟩) hg ⟨hs, hi, ht⟩
    · exact absurd hg side_not_mem_touch_center
    · simp only [Gate.stage, Gate.inv, Gate.time] at hs hi ht
      subst hs hi ht
      exact h1 (center_mem_touch_center.1 hg)

/-! ## (c) The edges of a wire

The vertex preceding `.gate g` on wire `w` is `FI.vtxAt w (FI.clk g)` (the source, or the previous
gate of `w`), and the last vertex is `FI.vtxAt w 24`; see `FI.edgeInto_gate`, `FI.edgeInto_sink` and
the explicit `vtxAt_clk_of_head`, `vtxAt_clk_of_consec`, `vtxAt_24_of_last` below. -/

theorem zip_lastBefore (t : Vertex κ h) :
    ∀ (gs : List (Gate h)) (v0 : Vertex κ h), gs.Pairwise (fun a b => FI.clk a < FI.clk b) →
      List.zip (v0 :: (gs.map Vertex.gate ++ [t])) (gs.map Vertex.gate ++ [t]) =
        gs.map (fun g => (FI.lastBefore (FI.clk g) v0 gs, Vertex.gate g)) ++
          [(FI.lastBefore 24 v0 gs, t)]
  | [], _, _ => rfl
  | g' :: gs, v0, hpw => by
    rw [List.pairwise_cons] at hpw
    have ih := zip_lastBefore t gs (.gate g') hpw.2
    simp only [List.map_cons, List.cons_append, List.zip_cons_cons, ih, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · simp only [FI.lastBefore, lt_irrefl, if_false]
    · congr 1
      · refine List.map_congr_left (fun g hg => ?_)
        simp only [FI.lastBefore, if_pos (hpw.1 g hg)]
      · simp only [FI.lastBefore, if_pos (FI.clk_lt g')]

/-- The edges of `w`: one edge into each gate of `w` (from the previous vertex), then the edge into
the sink (from the last vertex). -/
theorem edges_eq (w : Role κ h) :
    edges w = (touch w).map (fun g => (FI.vtxAt w (FI.clk g), Vertex.gate g)) ++
      [(FI.vtxAt w 24, Vertex.sink w)] := by
  unfold edges
  rw [FI.vertices_eq, List.tail_cons]
  exact zip_lastBefore _ _ _ (FI.touch_pairwise w)

theorem mem_edges_iff {w : Role κ h} {e : Vertex κ h × Vertex κ h} :
    e ∈ edges w ↔
      (∃ g ∈ touch w, e = (FI.vtxAt w (FI.clk g), .gate g)) ∨ e = (FI.vtxAt w 24, .sink w) := by
  rw [edges_eq]
  simp only [List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro (⟨g, hg, rfl⟩ | rfl)
    · exact Or.inl ⟨g, hg, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨g, hg, rfl⟩ | rfl)
    · exact Or.inl ⟨g, hg, rfl⟩
    · exact Or.inr rfl

theorem edgeInto_snd {w : Role κ h} {v : Vertex κ h} {e : Vertex κ h × Vertex κ h}
    (he : edgeInto w v = some e) : e.2 = v := by
  unfold edgeInto at he
  have := List.find?_some he
  simpa using this

/-- `edgeInto w v` is the (unique) edge of `w` with head `v`. -/
theorem edgeInto_eq_some_iff {w : Role κ h} {v : Vertex κ h} {e : Vertex κ h × Vertex κ h} :
    edgeInto w v = some e ↔ e ∈ edges w ∧ e.2 = v := by
  constructor
  · intro he
    exact ⟨FI.edgeInto_mem he, edgeInto_snd he⟩
  · rintro ⟨he, rfl⟩
    rcases mem_edges_iff.1 he with ⟨g, hg, rfl⟩ | rfl
    · exact FI.edgeInto_gate w g hg
    · exact FI.edgeInto_sink w

theorem edgeInto_eq_none_iff {w : Role κ h} {v : Vertex κ h} :
    edgeInto w v = none ↔ ∀ e ∈ edges w, e.2 ≠ v := by
  constructor
  · intro hn e he hev
    have := edgeInto_eq_some_iff.2 ⟨he, hev⟩
    rw [hn] at this
    cases this
  · intro hno
    cases hv : edgeInto w v with
    | none => rfl
    | some e => exact absurd (edgeInto_eq_some_iff.1 hv).2 (hno e (edgeInto_eq_some_iff.1 hv).1)

/-- No edge enters a source. -/
theorem edgeInto_source (w w' : Role κ h) : edgeInto w (.source w') = none := by
  rw [edgeInto_eq_none_iff]
  intro e he
  rcases mem_edges_iff.1 he with ⟨g, -, rfl⟩ | rfl <;> simp

/-- No edge of `w` enters a gate that does not touch `w`. -/
theorem edgeInto_gate_of_not_mem {w : Role κ h} {g : Gate h} (hg : g ∉ touch w) :
    edgeInto w (.gate g) = none := by
  rw [edgeInto_eq_none_iff]
  intro e he
  rcases mem_edges_iff.1 he with ⟨g', hg', rfl⟩ | rfl
  · intro h'
    simp only [Vertex.gate.injEq] at h'
    exact hg (h' ▸ hg')
  · simp

/-- No edge of `w` enters the sink of another wire. -/
theorem edgeInto_sink_of_ne {w w' : Role κ h} (hw : w' ≠ w) : edgeInto w (.sink w') = none := by
  rw [edgeInto_eq_none_iff]
  intro e he
  rcases mem_edges_iff.1 he with ⟨g, -, rfl⟩ | rfl
  · simp
  · intro h'
    simp only [Vertex.sink.injEq] at h'
    exact hw h'.symm

/-- Summing over the edges of a wire. -/
theorem sum_edges {M : Type*} [AddCommMonoid M] (f : Vertex κ h × Vertex κ h → M) (w : Role κ h) :
    ((edges w).map f).sum =
      ((touch w).map fun g => f (FI.vtxAt w (FI.clk g), .gate g)).sum +
        f (FI.vtxAt w 24, .sink w) := by
  rw [edges_eq, List.map_append, List.sum_append, List.map_map]
  simp [Function.comp_def]

theorem lastBefore_consec (g g' : Gate h) (l₂ : List (Gate h)) :
    ∀ (l₁ : List (Gate h)) (v : Vertex κ h),
      (l₁ ++ g' :: g :: l₂).Pairwise (fun a b => FI.clk a < FI.clk b) →
      FI.lastBefore (FI.clk g) v (l₁ ++ g' :: g :: l₂) = .gate g'
  | [], v, hpw => by
    rw [List.nil_append, List.pairwise_cons] at hpw
    simp only [List.nil_append, FI.lastBefore, if_pos (hpw.1 g List.mem_cons_self), lt_irrefl,
      if_false]
  | a :: l₁, v, hpw => by
    rw [List.cons_append, List.pairwise_cons] at hpw
    have hag : FI.clk a < FI.clk g := hpw.1 g (by simp)
    simp only [List.cons_append, FI.lastBefore, if_pos hag]
    exact lastBefore_consec g g' l₂ l₁ (.gate a) hpw.2

theorem lastBefore_last (g : Gate h) :
    ∀ (l : List (Gate h)) (v : Vertex κ h), FI.lastBefore 24 v (l ++ [g]) = .gate g
  | [], v => by simp only [List.nil_append, FI.lastBefore, if_pos (FI.clk_lt g)]
  | a :: l, v => by
    simp only [List.cons_append, FI.lastBefore, if_pos (FI.clk_lt a)]
    exact lastBefore_last g l (.gate a)

/-- The vertex preceding the first gate of `w` is its source. -/
theorem vtxAt_clk_of_head {w : Role κ h} {g : Gate h} {l : List (Gate h)} (hw : touch w = g :: l) :
    FI.vtxAt w (FI.clk g) = .source w := by
  unfold FI.vtxAt
  rw [hw]
  simp only [FI.lastBefore, lt_irrefl, if_false]

/-- The vertex preceding a gate of `w` is the previous gate of `w`. -/
theorem vtxAt_clk_of_consec {w : Role κ h} {g g' : Gate h} {l₁ l₂ : List (Gate h)}
    (hw : touch w = l₁ ++ g' :: g :: l₂) : FI.vtxAt w (FI.clk g) = .gate g' := by
  have hpw := FI.touch_pairwise w
  rw [hw] at hpw
  unfold FI.vtxAt
  rw [hw]
  exact lastBefore_consec g g' l₂ l₁ _ hpw

/-- The vertex preceding the sink of `w` is its last gate. -/
theorem vtxAt_24_of_last {w : Role κ h} {g : Gate h} {l : List (Gate h)} (hw : touch w = l ++ [g]) :
    FI.vtxAt w 24 = .gate g := by
  unfold FI.vtxAt
  rw [hw]
  exact lastBefore_last g l _

/-! ### Literal gate and edge lists -/

theorem touch_X_eq (a : Addr h) : touch (.X a : Role κ h) =
    [.side .one (a.fix .one) 2 (a.var .one), .center .one (a.fix .one) 3,
      .center .one (a.fix .one) 6, .side .one (a.fix .one) 7 (a.var .one),
      .side .two (a.fix .two) 2 (a.var .two), .center .two (a.fix .two) 3,
      .center .two (a.fix .two) 6, .side .two (a.fix .two) 7 (a.var .two),
      .side .three (a.fix .three) 2 (a.var .three), .center .three (a.fix .three) 3,
      .center .three (a.fix .three) 6, .side .three (a.fix .three) 7 (a.var .three)] := rfl

theorem touch_Y_eq (a : Addr h) : touch (.Y a : Role κ h) =
    [.side .one (a.fix .one) 0 (a.var .one), .center .one (a.fix .one) 1,
      .center .one (a.fix .one) 4, .side .one (a.fix .one) 5 (a.var .one),
      .side .two (a.fix .two) 0 (a.var .two), .center .two (a.fix .two) 1,
      .center .two (a.fix .two) 4, .side .two (a.fix .two) 5 (a.var .two),
      .side .three (a.fix .three) 0 (a.var .three), .center .three (a.fix .three) 1,
      .center .three (a.fix .three) 4, .side .three (a.fix .three) 5 (a.var .three)] := rfl

theorem touch_side_eq (j : Stage) (ι : Fix h) (p : SideIdx κ h) : touch (.side j ι p) =
    [.side j ι 0 (sideY j p), .side j ι 2 (sideX j p), .side j ι 5 (sideY j p),
      .side j ι 7 (sideX j p)] := rfl

theorem touch_center_eq (j : Stage) (ι : Fix h) (c : Center κ h) : touch (.center j ι c) =
    [.center j ι 1, .center j ι 3, .center j ι 4, .center j ι 6] := rfl

theorem edges_side (j : Stage) (ι : Fix h) (p : SideIdx κ h) :
    edges (.side j ι p) =
      [(.source (.side j ι p), .gate (.side j ι 0 (sideY j p))),
        (.gate (.side j ι 0 (sideY j p)), .gate (.side j ι 2 (sideX j p))),
        (.gate (.side j ι 2 (sideX j p)), .gate (.side j ι 5 (sideY j p))),
        (.gate (.side j ι 5 (sideY j p)), .gate (.side j ι 7 (sideX j p))),
        (.gate (.side j ι 7 (sideX j p)), .sink (.side j ι p))] := rfl

theorem edges_center (j : Stage) (ι : Fix h) (c : Center κ h) :
    edges (.center j ι c) =
      [(.source (.center j ι c), .gate (.center j ι 1)),
        (.gate (.center j ι 1), .gate (.center j ι 3)),
        (.gate (.center j ι 3), .gate (.center j ι 4)),
        (.gate (.center j ι 4), .gate (.center j ι 6)),
        (.gate (.center j ι 6), .sink (.center j ι c))] := rfl

/-! ## (e) Locality of the rows; disjointness of invocations

See also `FI.rowUpd_untouched` (a wire without a gate at `(j, ι, r)` is unchanged by that row) and
`FI.rowUpd_local` (on a wire touched by the gate `g`, the row reads only the wires touched by `g`). -/

/-- A role meets at most one invocation per stage: invocations of one stage touch disjoint roles. -/
theorem inv_eq_of_mem_touch {w : Role κ h} {g g' : Gate h} (hg : g ∈ touch w) (hg' : g' ∈ touch w)
    (hs : g.stage = g'.stage) : g.inv = g'.inv := by
  have h1 := FI.touch_inv w g hg
  have h2 := FI.touch_inv w g' hg'
  rw [hs, h2] at h1
  exact (Option.some.inj h1).symm

section Rows

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The rows of invocation `ι` leave the roles of other invocations (and other stages) unchanged. -/
theorem rowUpd_eq_self_of_invOf_ne (half : R) {j : Stage} {ι : Fix h} (r : Fin 8) (ε : R)
    (s : Role κ h → M) {w : Role κ h} (hw : invOf j w ≠ some ι) :
    rowUpd κ half j ι (rowOp j r) ε s w = s w :=
  FI.rowUpd_untouched half j ι r ε s w (gateAt_eq_none_of_invOf_ne hw)

/-- On a wire touched at `(j, ι, r)`, the row at `(j, ι, r)` depends only on the values of the
wires touched at `(j, ι, r)`. -/
theorem rowUpd_congr (half : R) (j : Stage) (ι : Fix h) (r : Fin 8) (ε : R) {s s' : Role κ h → M}
    (hss : ∀ w', (gateAt j ι r w').isSome → s w' = s' w') {w : Role κ h}
    (hw : (gateAt j ι r w).isSome) :
    rowUpd κ half j ι (rowOp j r) ε s w = rowUpd κ half j ι (rowOp j r) ε s' w := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hw
  obtain ⟨-, hgs, hgi, hgt⟩ := FI.gateAt_spec hg
  refine FI.rowUpd_local half j ι r ε g s s' (fun w' hw' => hss w' ?_) w hg
  rw [FI.gateAt_of_mem hw' hgs hgi hgt]
  rfl

/-- On a role of invocation `ι`, the row at `(j, ι, r)` depends only on the roles of `ι`. -/
theorem rowUpd_congr_inv (half : R) (j : Stage) (ι : Fix h) (r : Fin 8) (ε : R)
    {s s' : Role κ h → M} (hss : ∀ w', invOf j w' = some ι → s w' = s' w') {w : Role κ h}
    (hw : invOf j w = some ι) :
    rowUpd κ half j ι (rowOp j r) ε s w = rowUpd κ half j ι (rowOp j r) ε s' w := by
  cases hg : gateAt j ι r w with
  | none =>
    rw [FI.rowUpd_untouched half j ι r ε s w hg, FI.rowUpd_untouched half j ι r ε s' w hg]
    exact hss w hw
  | some g =>
    exact rowUpd_congr half j ι r ε (fun w' hw' => hss w' (invOf_of_gateAt_isSome hw'))
      (by rw [hg]; rfl)

end Rows

/-! ## (g) Invocations and stages: locality and sequential forms -/

section Fold

variable {α β A : Type*}

/-- A fold of maps that all fix the coordinate `a` fixes it. -/
theorem foldl_apply_of_forall {f : (α → A) → β → (α → A)} {a : α}
    (hf : ∀ s x, f s x a = s a) : ∀ (xs : List β) (s : α → A), xs.foldl f s a = s a
  | [], _ => rfl
  | x :: xs, s => by rw [List.foldl_cons, foldl_apply_of_forall hf xs, hf]

/-- A fold of maps that preserve agreement on `P` preserves agreement on `P`. -/
theorem foldl_congr_on {f : (α → A) → β → (α → A)} (P : α → Prop)
    (hf : ∀ s s' x, (∀ a, P a → s a = s' a) → ∀ a, P a → f s x a = f s' x a) :
    ∀ (xs : List β) (s s' : α → A), (∀ a, P a → s a = s' a) →
      ∀ a, P a → xs.foldl f s a = xs.foldl f s' a
  | [], _, _, hss => hss
  | x :: xs, s, s', hss => by
    simp only [List.foldl_cons]
    exact foldl_congr_on P hf xs _ _ (hf s s' x hss)

/-- Disjoint blocks, outside coordinates: if every block map `F i` fixes the coordinates outside
block `i`, a coordinate in none of the blocks of `l` is fixed by the fold over `l`. -/
theorem foldl_blocks_of_forall {ι' : Type*} {blk : α → Option ι'} {F : ι' → (α → A) → (α → A)}
    (hout : ∀ i s a, blk a ≠ some i → F i s a = s a) :
    ∀ (l : List ι') (s : α → A) (a : α), (∀ i ∈ l, blk a ≠ some i) →
      l.foldl (fun s i => F i s) s a = s a
  | [], _, _, _ => rfl
  | i :: l, s, a, ha => by
    rw [List.foldl_cons, foldl_blocks_of_forall hout l _ a
      (fun i' hi' => ha i' (List.mem_cons_of_mem _ hi')), hout i s a (ha i List.mem_cons_self)]

/-- Disjoint blocks: if every block map `F i` fixes the coordinates outside block `i` and reads only
the coordinates of block `i`, then on block `i₀` the fold over a duplicate-free list containing `i₀`
is `F i₀`. -/
theorem foldl_blocks_of_mem {ι' : Type*} {blk : α → Option ι'} {F : ι' → (α → A) → (α → A)}
    (hout : ∀ i s a, blk a ≠ some i → F i s a = s a)
    (hin : ∀ i s s', (∀ a, blk a = some i → s a = s' a) → ∀ a, blk a = some i → F i s a = F i s' a)
    {l : List ι'} (hl : l.Nodup) {i₀ : ι'} (hi₀ : i₀ ∈ l) (s : α → A) {a : α}
    (ha : blk a = some i₀) : l.foldl (fun s i => F i s) s a = F i₀ s a := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hi₀
  have hnd := (List.nodup_cons.1 (List.nodup_middle.1 hl)).1
  have h₁ : i₀ ∉ l₁ := fun hm => hnd (List.mem_append_left _ hm)
  have h₂ : i₀ ∉ l₂ := fun hm => hnd (List.mem_append_right _ hm)
  have hne : ∀ (l' : List ι'), i₀ ∉ l' → ∀ a', blk a' = some i₀ → ∀ i ∈ l', blk a' ≠ some i := by
    intro l' hl' a' ha' i hi hb
    rw [ha'] at hb
    exact hl' (Option.some.inj hb ▸ hi)
  simp only [List.foldl_append, List.foldl_cons]
  rw [foldl_blocks_of_forall hout l₂ _ a (hne l₂ h₂ a ha)]
  exact hin i₀ _ _ (fun a' ha' => foldl_blocks_of_forall hout l₁ s a' (hne l₁ h₁ a' ha')) a ha

/-- The value of a fold of single-coordinate updates, each reading only its own coordinate. -/
theorem foldl_update_apply [DecidableEq α] (F : α → A → A) :
    ∀ (l : List α), l.Nodup → ∀ (s : α → A) (a : α),
      l.foldl (fun s b => Function.update s b (F b (s b))) s a = if a ∈ l then F a (s a) else s a
  | [], _, s, a => by simp
  | b :: l, hl, s, a => by
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons, foldl_update_apply F l hl.2]
    by_cases hal : a ∈ l
    · have hab : a ≠ b := fun h' => hl.1 (h' ▸ hal)
      simp [hal, Function.update_of_ne hab]
    · by_cases hab : a = b
      · subst hab
        simp [hal]
      · simp [hal, hab]

/-- A pointwise map `a ↦ F a (s a)` is the fold, over any duplicate-free complete list, of the
single-coordinate updates. -/
theorem pointwise_eq_foldl [DecidableEq α] (F : α → A → A) (l : List α) (hl : l.Nodup)
    (hall : ∀ a, a ∈ l) (s : α → A) :
    (fun a => F a (s a)) = l.foldl (fun s a => Function.update s a (F a (s a))) s := by
  funext a
  rw [foldl_update_apply F l hl s a, if_pos (hall a)]

end Fold

section EdgeMaps

variable {A : Type*}

/-- The sink-edge operator of wire `w` (the last step of `framedNet`, see `framedNet_apply`). -/
noncomputable def sinkEdgeMap (E : EdgeOps κ h A) (w : Role κ h) (x : A) : A :=
  match edgeInto w (.sink w) with
  | some e => E w e x
  | none => x

/-- (g5) The simultaneous sink-edge step is the fold of single-wire updates. -/
theorem sinkEdges_eq_foldl (E : EdgeOps κ h A) (l : List (Role κ h)) (hl : l.Nodup)
    (hall : ∀ w, w ∈ l) (t : Role κ h → A) :
    (fun w => sinkEdgeMap E w (t w)) =
      l.foldl (fun s w => Function.update s w (sinkEdgeMap E w (s w))) t :=
  pointwise_eq_foldl _ l hl hall t

/-- (g5') `sinkEdges_eq_foldl` with the update written out as a match. -/
theorem sinkEdges_eq_foldl' (E : EdgeOps κ h A) (l : List (Role κ h)) (hl : l.Nodup)
    (hall : ∀ w, w ∈ l) (t : Role κ h → A) :
    (fun w => match edgeInto w (.sink w) with | some e => E w e (t w) | none => t w) =
      l.foldl (fun s w => match edgeInto w (.sink w) with
        | some e => Function.update s w (E w e (s w))
        | none => s) t := by
  have h1 : (fun w => match edgeInto w (.sink w) with | some e => E w e (t w) | none => t w) =
      fun w => sinkEdgeMap E w (t w) := by
    funext w
    unfold sinkEdgeMap
    cases edgeInto w (.sink w) <;> rfl
  rw [h1, sinkEdges_eq_foldl E l hl hall t]
  congr 1
  funext s w
  unfold sinkEdgeMap
  cases edgeInto w (.sink w) with
  | none => exact Function.update_eq_self w s
  | some e => rfl

/-- The incoming-edge operator applied to wire `w` at `(j, ι, r)` (the identity if `w` has no gate
there); `preEdges_apply : preEdges E j ι r s w = preEdgeMap E j ι r w (s w)`. -/
noncomputable def preEdgeMap (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    (w : Role κ h) (x : A) : A :=
  preEdges E j ι r (fun _ => x) w

theorem preEdges_apply (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    (s : Role κ h → A) (w : Role κ h) : preEdges E j ι r s w = preEdgeMap E j ι r w (s w) := by
  show preEdges E j ι r s w = preEdges E j ι r (fun _ => s w) w
  unfold preEdges
  rfl

theorem preEdges_eq_self (E : EdgeOps κ h A) {j : Stage} {ι : Fix h} {r : Fin 8}
    (s : Role κ h → A) {w : Role κ h} (hw : gateAt j ι r w = none) : preEdges E j ι r s w = s w := by
  unfold preEdges
  simp only [hw]

theorem preEdges_congr (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    {s s' : Role κ h → A} {w : Role κ h} (hw : s w = s' w) :
    preEdges E j ι r s w = preEdges E j ι r s' w := by
  unfold preEdges
  rw [hw]

/-- (g4) The simultaneous incoming-edge step is the fold of single-wire updates. -/
theorem preEdges_eq_foldl (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    (l : List (Role κ h)) (hl : l.Nodup) (hall : ∀ w, w ∈ l) (s : Role κ h → A) :
    preEdges E j ι r s =
      l.foldl (fun s w => Function.update s w (preEdgeMap E j ι r w (s w))) s :=
  (funext fun w => preEdges_apply E j ι r s w).trans (pointwise_eq_foldl _ l hl hall s)

/-- (g4') `preEdges_eq_foldl` with the update written out as nested matches. -/
theorem preEdges_eq_foldl' (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    (l : List (Role κ h)) (hl : l.Nodup) (hall : ∀ w, w ∈ l) (s : Role κ h → A) :
    preEdges E j ι r s = l.foldl (fun s w => match gateAt j ι r w with
      | some g => (match edgeInto w (.gate g) with
          | some e => Function.update s w (E w e (s w))
          | none => s)
      | none => s) s := by
  rw [preEdges_eq_foldl E j ι r l hl hall s]
  congr 1
  funext s w
  unfold preEdgeMap preEdges
  cases gateAt j ι r w with
  | none => exact Function.update_eq_self w s
  | some g =>
    dsimp only
    cases edgeInto w (.gate g) with
    | none => exact Function.update_eq_self w s
    | some e => rfl

end EdgeMaps

section Framed

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

theorem framedNet_apply (half : R) (E : EdgeOps κ h A) (s : Role κ h → A) (w : Role κ h) :
    framedNet κ half E s w = sinkEdgeMap E w
      (framedStage κ half E .three (framedStage κ half E .two (framedStage κ half E .one s)) w) := by
  unfold framedNet sinkEdgeMap
  cases edgeInto w (.sink w) <;> rfl

/-- (g1) A framed invocation leaves the roles of other invocations unchanged. -/
theorem framedInvocation_eq_self (half : R) (E : EdgeOps κ h A) {j : Stage} {ι : Fix h}
    (s : Role κ h → A) {w : Role κ h} (hw : invOf j w ≠ some ι) :
    framedInvocation κ half E j ι s w = s w := by
  unfold framedInvocation
  refine foldl_apply_of_forall (fun s r => ?_) _ _
  rw [rowUpd_eq_self_of_invOf_ne half r _ _ hw,
    preEdges_eq_self E s (gateAt_eq_none_of_invOf_ne hw)]

/-- (g2) On the roles of invocation `ι`, a framed invocation reads only the roles of `ι`. -/
theorem framedInvocation_congr (half : R) (E : EdgeOps κ h A) {j : Stage} {ι : Fix h}
    {s s' : Role κ h → A} (hss : ∀ w', invOf j w' = some ι → s w' = s' w') {w : Role κ h}
    (hw : invOf j w = some ι) :
    framedInvocation κ half E j ι s w = framedInvocation κ half E j ι s' w := by
  unfold framedInvocation
  refine foldl_congr_on (fun w' => invOf j w' = some ι) (fun t t' r htt w' hw' => ?_) _ s s'
    hss w hw
  exact rowUpd_congr_inv half j ι r _ (fun w'' hw'' => preEdges_congr E j ι r (htt w'' hw'')) hw'

/-- (g3) A framed stage is the fold of its framed invocations over any duplicate-free complete
list of invocations (they act on disjoint role sets). -/
theorem framedStage_eq_foldl (half : R) (E : EdgeOps κ h A) (j : Stage) (l : List (Fix h))
    (hl : l.Nodup) (hall : ∀ ι, ι ∈ l) (s : Role κ h → A) :
    framedStage κ half E j s = l.foldl (fun s ι => framedInvocation κ half E j ι s) s := by
  funext w
  rcases hb : invOf j w with _ | ι₀
  · simp only [framedStage, hb]
    exact (foldl_blocks_of_forall (blk := invOf j)
      (fun ι s w hw => framedInvocation_eq_self half E s hw) l s w
      (fun ι _ => by simp [hb])).symm
  · simp only [framedStage, hb]
    exact (foldl_blocks_of_mem (blk := invOf j)
      (fun ι s w hw => framedInvocation_eq_self half E s hw)
      (fun ι s s' hss w hw => framedInvocation_congr half E hss hw) hl (hall ι₀) s hb).symm

/-- An (unframed) invocation leaves the roles of other invocations unchanged. -/
theorem invocation_eq_self (half : R) {j : Stage} {ι : Fix h} (s : Role κ h → A) {w : Role κ h}
    (hw : invOf j w ≠ some ι) : invocation κ half j ι s w = s w := by
  unfold invocation
  exact foldl_apply_of_forall (fun s r => rowUpd_eq_self_of_invOf_ne half r _ _ hw) _ _

/-- On the roles of invocation `ι`, an (unframed) invocation reads only the roles of `ι`. -/
theorem invocation_congr (half : R) {j : Stage} {ι : Fix h} {s s' : Role κ h → A}
    (hss : ∀ w', invOf j w' = some ι → s w' = s' w') {w : Role κ h} (hw : invOf j w = some ι) :
    invocation κ half j ι s w = invocation κ half j ι s' w := by
  unfold invocation
  refine foldl_congr_on (fun w' => invOf j w' = some ι) (fun t t' r htt w' hw' => ?_) _ s s'
    hss w hw
  exact rowUpd_congr_inv half j ι r _ htt hw'

/-- A stage is the fold of its invocations over any duplicate-free complete list of invocations. -/
theorem stageMap_eq_foldl (half : R) (j : Stage) (l : List (Fix h)) (hl : l.Nodup)
    (hall : ∀ ι, ι ∈ l) (s : Role κ h → A) :
    stageMap κ half j s = l.foldl (fun s ι => invocation κ half j ι s) s := by
  funext w
  rcases hb : invOf j w with _ | ι₀
  · simp only [stageMap, hb]
    exact (foldl_blocks_of_forall (blk := invOf j)
      (fun ι s w hw => invocation_eq_self half s hw) l s w (fun ι _ => by simp [hb])).symm
  · simp only [stageMap, hb]
    exact (foldl_blocks_of_mem (blk := invOf j) (fun ι s w hw => invocation_eq_self half s hw)
      (fun ι s s' hss w hw => invocation_congr half hss hw) hl (hall ι₀) s hb).symm

end Framed

/-! ## (f) Counts -/

theorem length_touch_X (a : Addr h) : (touch (.X a : Role κ h)).length = 12 := rfl

theorem length_touch_Y (a : Addr h) : (touch (.Y a : Role κ h)).length = 12 := rfl

theorem length_touch_side (j : Stage) (ι : Fix h) (p : SideIdx κ h) :
    (touch (.side j ι p)).length = 4 := rfl

theorem length_touch_center (j : Stage) (ι : Fix h) (c : Center κ h) :
    (touch (.center j ι c)).length = 4 := rfl

/-- Scratch roles have 4 incident gates (data roles have 12: `length_touch_X`, `length_touch_Y`). -/
theorem length_touch_of_scratch {w : Role κ h} (hw : w.IsScratch) : (touch w).length = 4 := by
  cases w with
  | X a => exact False.elim hw
  | Y a => exact False.elim hw
  | side j ι p => rfl
  | center j ι c => rfl

theorem length_touch_le (w : Role κ h) : (touch w).length ≤ 12 := by
  cases w with
  | X a => exact (length_touch_X a).le
  | Y a => exact (length_touch_Y a).le
  | side j ι p => rw [length_touch_side]; omega
  | center j ι c => rw [length_touch_center]; omega

theorem length_vertices (w : Role κ h) : (vertices w).length = (touch w).length + 2 := by
  simp only [vertices, List.length_append, List.length_singleton, List.length_map]
  omega

theorem length_edges (w : Role κ h) : (edges w).length = (touch w).length + 1 := by
  rw [edges_eq]
  simp only [List.length_append, List.length_map, List.length_singleton]

theorem length_edges_le (w : Role κ h) : (edges w).length ≤ 13 := by
  rw [length_edges]
  have := length_touch_le w
  omega

theorem length_touch_eq_card (w : Role κ h) :
    (touch w).length = (Finset.univ.filter fun g : Gate h => g ∈ touch w).card := by
  rw [← List.toFinset_card_of_nodup (touch_nodup w)]
  congr 1
  ext g
  simp

/-- Double counting of incidences: `Σ_w |touch w| = Σ_g |supp g|`. -/
theorem sum_length_touch :
    ∑ w : Role κ h, (touch w).length = ∑ g : Gate h, (supp κ g).card := by
  simp only [length_touch_eq_card, supp, Finset.card_filter]
  exact Finset.sum_comm

instance decidableValid : DecidablePred (Gate.Valid (h := h)) := fun g => by
  cases g <;> unfold Gate.Valid <;> infer_instance

/-- Double counting over the actual gates: `Σ_w |touch w| = Σ_{g actual} |supp g|`. -/
theorem sum_length_touch_actual :
    ∑ w : Role κ h, (touch w).length = ∑ g : ActualGate h, (supp κ g.1).card := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype Gate.Valid
    (fun g : Gate h => (supp κ g).card)
  have h0 : ∑ g : {g : Gate h // ¬ g.Valid}, (supp κ g.1).card = 0 :=
    Finset.sum_eq_zero (fun g _ => by simp [supp_eq_empty g.2])
  rw [sum_length_touch, ← hsplit, h0, add_zero]

end SubNLogN.Math.Networks.Incidence
