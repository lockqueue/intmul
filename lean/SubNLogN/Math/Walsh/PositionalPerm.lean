import SubNLogN.Math.Walsh.Exact

/-!
# Walsh: positional permutations (Definition 5.6, eq. (`eq:walsh-slices`), Theorem 5.8)

Paper: Definition 5.6 (`def:walsh-positional`), the slice count
eq. (`eq:walsh-slices`), and Theorem 5.8 (`thm:positional-perm`)
in Section 5.3 (`sec:walsh-perm`).

The procedure of Theorem 5.8 as a program: for each of the two involutions of Lemma 5.7 and
each of its three stages, the pairs of the stage are batched by the slice containing their target
(`stageProg`); every nonempty batch is one `cnotBatchProg` (Proposition 5.5); a pair whose target
is a leftover position (one of the last `m₀ - JK < K` positions) is one `cnot1` step (two-digit
permutation of Lemma A.4(1)). Value and count part only; the time bound
`O(V[(m₀/d + K) d^{λ'} + K])` follows at machine level from the counts and Proposition A.11.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-- The program for one stage (a valid batch `pairs` of disjoint controlled flips): one
slice-batched call per nonempty slice `(g, ρ)` (group `g < ⌈J/d⌉`, offset `ρ < K`), then one
two-digit permutation per pair with a leftover target. -/
noncomputable def stageProg {m₀ : ℕ} (P d K : ℕ) (pairs : List (Fin m₀ × Fin m₀)) :
    List (WStep m₀) :=
  ((List.range (numGroups m₀ K d)).flatMap fun g =>
      (List.finRange K).flatMap fun ρ : Fin K =>
        let j₀ := groupStart K d g
        let D := groupSize m₀ K d g
        let ps := pairs.filter (fun p => decide (p.2 ∈ slicePos m₀ K j₀ D (ρ : ℕ)))
        if ps.isEmpty then [] else cnotBatchProg P d K j₀ D (m₀ - j₀ - D * K) ρ ps) ++
    ((pairs.filter (fun p => decide (numChunks m₀ K * K ≤ (p.2 : ℕ)))).map
      fun p => WStep.cnot1 p.1 p.2)

/-- The program for one involution `I`: its three stages (Theorem 5.8 (`thm:positional-perm`)). -/
noncomputable def involProg {m₀ : ℕ} (P d K : ℕ) (I : Fin m₀ → Fin m₀) : List (WStep m₀) :=
  stageProg P d K (stageA I) ++ stageProg P d K (stageB I) ++ stageProg P d K (stageA I)

/-- The program of Theorem 5.8 for a positional map `π`: `I_0` first, then `I_1`. -/
noncomputable def posPermProg {m₀ : ℕ} (P d K : ℕ) (π : Fin m₀ → Fin m₀) : List (WStep m₀) :=
  involProg P d K (invol0 π) ++ involProg P d K (invol1 π)

/-! ## Proof helpers

All helpers live in the namespace `PosPermAux`. Plan of the proof of Theorem 5.8:
* a stage program `stageProg P d K pairs` is the concatenation, over the slices `(g, ρ)`, of the
  batch programs (`batchProg`), followed by one `cnot1` step per leftover pair (`stageProg_eq`);
* on disk arrays on the `P`-grid every batch program performs `CNOT` of its batch exactly
  (Proposition 5.5, `cnot_batch`; an empty batch is the empty program), and so does every `cnot1`;
* consecutive `CNOT` batches compose to the `CNOT` of the concatenated list provided no control of
  an earlier batch is a target of a later one and targets are distinct (`cnotArr_cnotArr`);
* every target position lies in exactly one slice or is a leftover position (`exists_slice`,
  `slice_unique`, `lt_of_mem_slice`), so the batches of a stage, followed by its leftover pairs,
  are a permutation of the pairs of the stage (`slicePairs_append_leftPairs_perm`); hence a stage
  program performs `CNOT` of the whole (valid) stage (`stageProg_run`);
* Lemma 5.7 (`walsh_involutions`, `involution_three_stages`, `posPermArr_eq_invol`) assembles the
  six stages into `posPermArr π`;
* counts: a batch program has `≤ 6` layer calls and `≤ 12` passes, there are
  `K ⌈J/d⌉ = N_slice` slices, and a valid stage has at most `m₀ - JK < K` leftover pairs
  (distinct targets in `[JK, m₀)`). -/

namespace PosPermAux

/-! ### Running and counting programs -/

theorem runProg_cons (layer : LayerOracle) (r : ℕ) {m : ℕ} (s : WStep m) (l : List (WStep m))
    (z : RArr (Cube m) r) : runProg layer r (s :: l) z = runProg layer r l (s.run layer r z) :=
  rfl

theorem runProg_append (layer : LayerOracle) (r : ℕ) {m : ℕ} (l₁ l₂ : List (WStep m))
    (z : RArr (Cube m) r) :
    runProg layer r (l₁ ++ l₂) z = runProg layer r l₂ (runProg layer r l₁ z) := by
  simp only [runProg, List.foldl_append]

theorem progLayerCalls_cons {m : ℕ} (s : WStep m) (l : List (WStep m)) :
    progLayerCalls (s :: l) = s.layerCalls + progLayerCalls l := by
  simp only [progLayerCalls, List.map_cons, List.sum_cons]

theorem progPasses_cons {m : ℕ} (s : WStep m) (l : List (WStep m)) :
    progPasses (s :: l) = s.passes + progPasses l := by
  simp only [progPasses, List.map_cons, List.sum_cons]

theorem progLayerCalls_append {m : ℕ} (l₁ l₂ : List (WStep m)) :
    progLayerCalls (l₁ ++ l₂) = progLayerCalls l₁ + progLayerCalls l₂ := by
  simp only [progLayerCalls, List.map_append, List.sum_append]

theorem progPasses_append {m : ℕ} (l₁ l₂ : List (WStep m)) :
    progPasses (l₁ ++ l₂) = progPasses l₁ + progPasses l₂ := by
  simp only [progPasses, List.map_append, List.sum_append]

theorem progLayerCalls_flatMap {m : ℕ} {ι : Type} (l : List ι) (f : ι → List (WStep m)) :
    progLayerCalls (l.flatMap f) = (l.map fun i => progLayerCalls (f i)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, progLayerCalls_append, ih, List.map_cons, List.sum_cons]

theorem progPasses_flatMap {m : ℕ} {ι : Type} (l : List ι) (f : ι → List (WStep m)) :
    progPasses (l.flatMap f) = (l.map fun i => progPasses (f i)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, progPasses_append, ih, List.map_cons, List.sum_cons]

theorem progLayerCalls_map_cnot1 {m : ℕ} (l : List (Fin m × Fin m)) :
    progLayerCalls (l.map fun p => WStep.cnot1 p.1 p.2) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, progLayerCalls_cons, ih]; rfl

theorem progPasses_map_cnot1 {m : ℕ} (l : List (Fin m × Fin m)) :
    progPasses (l.map fun p => WStep.cnot1 p.1 p.2) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, progPasses_cons, ih, List.length_cons]
    show 1 + l.length = l.length + 1
    omega

theorem progLayerCalls_nil {m : ℕ} : progLayerCalls ([] : List (WStep m)) = 0 := by
  simp only [progLayerCalls, List.map_nil, List.sum_nil]

theorem progPasses_nil {m : ℕ} : progPasses ([] : List (WStep m)) = 0 := by
  simp only [progPasses, List.map_nil, List.sum_nil]

/-- The batch program of Proposition 5.5 has six completed layer calls (unconditionally; this is
also part of the conclusion of `cnot_batch`). -/
theorem progLayerCalls_cnotBatchProg {m : ℕ} (P d K j₀ D nS : ℕ) (ρ : Fin K)
    (pairs : List (Fin m × Fin m)) :
    progLayerCalls (cnotBatchProg (m := m) P d K j₀ D nS ρ pairs) = 6 := by
  simp only [cnotBatchProg, gadgetProg, List.cons_append, List.nil_append,
    progLayerCalls_cons, progLayerCalls_nil, WStep.layerCalls]

/-- The batch program of Proposition 5.5 has twelve passes (unconditionally). -/
theorem progPasses_cnotBatchProg {m : ℕ} (P d K j₀ D nS : ℕ) (ρ : Fin K)
    (pairs : List (Fin m × Fin m)) :
    progPasses (cnotBatchProg (m := m) P d K j₀ D nS ρ pairs) = 12 := by
  simp only [cnotBatchProg, gadgetProg, List.cons_append, List.nil_append,
    progPasses_cons, progPasses_nil, WStep.passes]

/-! ### Controlled flips -/

theorem cnotAddr_nil {m : ℕ} (y : Cube m) : cnotAddr [] y = y := by
  funext p
  simp [cnotAddr]

theorem cnotArr_nil {m r : ℕ} (z : RArr (Cube m) r) : cnotArr [] z = z := by
  funext y k
  simp only [cnotArr, cnotAddr_nil]

theorem arrOnDiskGrid_cnotArr {m r P : ℕ} (pairs : List (Fin m × Fin m)) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid P z) : ArrOnDiskGrid P (cnotArr pairs z) :=
  fun _ k => hz _ k

theorem arrOnDiskGrid_posPermArr {m r P : ℕ} (π : Fin m → Fin m) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid P z) : ArrOnDiskGrid P (posPermArr π z) :=
  fun _ k => hz _ k

/-- `CNOT` of a list of pairs depends only on the members of the list. -/
theorem cnotArr_congr {m r : ℕ} {l l' : List (Fin m × Fin m)} (h : ∀ q, q ∈ l ↔ q ∈ l')
    (z : RArr (Cube m) r) : cnotArr l z = cnotArr l' z := by
  have haddr : cnotAddr l = cnotAddr l' := by
    funext x p
    have hany : (l.any fun q => decide (q.2 = p) && x q.1) =
        (l'.any fun q => decide (q.2 = p) && x q.1) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      exact ⟨fun ⟨q, hq, h'⟩ => ⟨q, (h q).1 hq, h'⟩, fun ⟨q, hq, h'⟩ => ⟨q, (h q).2 hq, h'⟩⟩
    show xor (x p) _ = xor (x p) _
    rw [hany]
  funext y k
  show z (cnotAddr l y) k = z (cnotAddr l' y) k
  rw [haddr]

theorem valid_of_sublist {m : ℕ} {l l' : List (Fin m × Fin m)} (hv : CnotPairsValid l)
    (h : List.Sublist l' l) : CnotPairsValid l' :=
  List.Nodup.sublist ((h.map Prod.fst).append (h.map Prod.snd)) hv

theorem valid_of_perm {m : ℕ} {l l' : List (Fin m × Fin m)} (hv : CnotPairsValid l)
    (h : l.Perm l') : CnotPairsValid l' :=
  ((h.map Prod.fst).append (h.map Prod.snd)).nodup_iff.1 hv

theorem nodup_of_valid {m : ℕ} {l : List (Fin m × Fin m)} (hv : CnotPairsValid l) : l.Nodup :=
  List.Nodup.of_map Prod.fst (List.nodup_append.1 hv).1

/-- In a valid concatenation, no control of the first part is a target of the second part, and
the targets of the two parts are distinct. -/
theorem valid_cross {m : ℕ} {l₁ l₂ : List (Fin m × Fin m)} (hv : CnotPairsValid (l₁ ++ l₂)) :
    ∀ q ∈ l₁, ∀ q' ∈ l₂, q.1 ≠ q'.2 ∧ q.2 ≠ q'.2 := by
  intro q hq q' hq'
  have hv' := List.nodup_append.1 hv
  refine ⟨hv'.2.2 _ (List.mem_map.2 ⟨q, List.mem_append_left _ hq, rfl⟩) _
    (List.mem_map.2 ⟨q', List.mem_append_right _ hq', rfl⟩), ?_⟩
  have h2 := hv'.2.1
  rw [List.map_append] at h2
  exact (List.nodup_append.1 h2).2.2 _ (List.mem_map.2 ⟨q, hq, rfl⟩) _
    (List.mem_map.2 ⟨q', hq', rfl⟩)

/-- Two consecutive `CNOT` batches (first `ps₁`, then `ps₂`) are the `CNOT` of `ps₁ ++ ps₂`,
provided no control of `ps₁` is a target of `ps₂` and the targets of `ps₁` and `ps₂` are
distinct. -/
theorem cnotArr_cnotArr {m r : ℕ} (ps₁ ps₂ : List (Fin m × Fin m))
    (h : ∀ q ∈ ps₁, ∀ q' ∈ ps₂, q.1 ≠ q'.2 ∧ q.2 ≠ q'.2) (z : RArr (Cube m) r) :
    cnotArr ps₂ (cnotArr ps₁ z) = cnotArr (ps₁ ++ ps₂) z := by
  have haddr : ∀ y : Cube m, cnotAddr ps₁ (cnotAddr ps₂ y) = cnotAddr (ps₁ ++ ps₂) y := by
    intro y
    funext p
    have hctl : ∀ q ∈ ps₁, cnotAddr ps₂ y q.1 = y q.1 := by
      intro q hq
      have hf : (ps₂.any fun q' => decide (q'.2 = q.1) && y q'.1) = false := by
        rw [List.any_eq_false]
        intro q' hq'
        have hne := (h q hq q' hq').1
        simp [Ne.symm hne]
      show xor (y q.1) (ps₂.any fun q' => decide (q'.2 = q.1) && y q'.1) = y q.1
      rw [hf, Bool.xor_false]
    have hA1 : (ps₁.any fun q => decide (q.2 = p) && cnotAddr ps₂ y q.1) =
        (ps₁.any fun q => decide (q.2 = p) && y q.1) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, hq, by rwa [hctl q hq] at hq'⟩
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, hq, by rwa [hctl q hq]⟩
    have hdisj : ¬((ps₁.any fun q => decide (q.2 = p) && y q.1) = true ∧
        (ps₂.any fun q => decide (q.2 = p) && y q.1) = true) := by
      rintro ⟨h1, h2⟩
      rw [List.any_eq_true] at h1 h2
      obtain ⟨q, hq, hq1⟩ := h1
      obtain ⟨q', hq', hq2⟩ := h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq1 hq2
      exact (h q hq q' hq').2 (hq1.1.trans hq2.1.symm)
    show xor (cnotAddr ps₂ y p) (ps₁.any fun q => decide (q.2 = p) && cnotAddr ps₂ y q.1) =
      xor (y p) ((ps₁ ++ ps₂).any fun q => decide (q.2 = p) && y q.1)
    rw [hA1, List.any_append]
    show xor (xor (y p) (ps₂.any fun q => decide (q.2 = p) && y q.1)) _ = _
    revert hdisj
    generalize (ps₁.any fun q => decide (q.2 = p) && y q.1) = A₁
    generalize (ps₂.any fun q => decide (q.2 = p) && y q.1) = A₂
    generalize y p = a
    cases A₁ <;> cases A₂ <;> cases a <;> simp
  funext y k
  show z (cnotAddr ps₁ (cnotAddr ps₂ y)) k = z (cnotAddr (ps₁ ++ ps₂) y) k
  rw [haddr]

/-- Running a concatenation of programs, each of which performs the `CNOT` of its own list of
pairs on disk arrays on the `P`-grid, performs the `CNOT` of the concatenated list, provided that
list is valid. -/
theorem runProg_flatMap {ι : Type} (layer : LayerOracle) {m r : ℕ} (P : ℕ) (items : List ι)
    (prog : ι → List (WStep m)) (ps : ι → List (Fin m × Fin m))
    (hprog : ∀ i ∈ items, CnotPairsValid (ps i) → ∀ z : RArr (Cube m) r, ArrOnDiskGrid P z →
      runProg layer r (prog i) z = cnotArr (ps i) z)
    (hv : CnotPairsValid (items.flatMap ps)) (z : RArr (Cube m) r) (hz : ArrOnDiskGrid P z) :
    runProg layer r (items.flatMap prog) z = cnotArr (items.flatMap ps) z := by
  induction items generalizing z with
  | nil => simp only [List.flatMap_nil]; rw [cnotArr_nil]; rfl
  | cons i rest ih =>
    simp only [List.flatMap_cons] at hv ⊢
    have hv₁ : CnotPairsValid (ps i) := valid_of_sublist hv (List.sublist_append_left _ _)
    have hv₂ : CnotPairsValid (rest.flatMap ps) :=
      valid_of_sublist hv (List.sublist_append_right _ _)
    rw [runProg_append, hprog i (by simp) hv₁ z hz,
      ih (fun j hj => hprog j (by simp [hj])) hv₂ _ (arrOnDiskGrid_cnotArr _ hz),
      cnotArr_cnotArr _ _ (valid_cross hv)]

/-- A list of single controlled flips (`cnot1` steps) performs the `CNOT` of the list. -/
theorem runProg_map_cnot1 (layer : LayerOracle) {m r : ℕ} (l : List (Fin m × Fin m))
    (hv : CnotPairsValid l) (z : RArr (Cube m) r) :
    runProg layer r (l.map fun p => WStep.cnot1 p.1 p.2) z = cnotArr l z := by
  induction l generalizing z with
  | nil => rw [List.map_nil, cnotArr_nil]; rfl
  | cons q l ih =>
    rw [List.map_cons, runProg_cons, ih (valid_of_sublist hv (List.sublist_cons_self _ _))]
    show cnotArr l (cnotArr [(q.1, q.2)] z) = cnotArr (q :: l) z
    rw [cnotArr_cnotArr [(q.1, q.2)] l (valid_cross (l₁ := [(q.1, q.2)]) (l₂ := l) hv)]
    rfl

/-! ### Slices: every position below `JK` lies in exactly one slice -/

theorem mem_slicePos_iff {m K j₀ D ρ : ℕ} {p : Fin m} :
    p ∈ slicePos m K j₀ D ρ ↔
      j₀ ≤ (p : ℕ) ∧ (p : ℕ) < j₀ + D * K ∧ ((p : ℕ) - j₀) % K = K - 1 - ρ := by
  simp [slicePos]

theorem groupSize_le (m₀ K d g : ℕ) : groupSize m₀ K d g ≤ d := min_le_left _ _

theorem groupSize_le_sub (m₀ K d g : ℕ) : groupSize m₀ K d g ≤ numChunks m₀ K - g * d :=
  min_le_right _ _

theorem lt_numGroups_iff {m₀ K d g : ℕ} (hd : 1 ≤ d) :
    g < numGroups m₀ K d ↔ g * d < numChunks m₀ K := by
  unfold numGroups
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.add_mul, one_mul]
  omega

theorem groupEnd_le {m₀ K d g : ℕ} (hg : g * d ≤ numChunks m₀ K) :
    groupStart K d g + groupSize m₀ K d g * K ≤ numChunks m₀ K * K := by
  unfold groupStart
  have h1 := groupSize_le_sub m₀ K d g
  calc g * d * K + groupSize m₀ K d g * K = (g * d + groupSize m₀ K d g) * K := by ring
    _ ≤ numChunks m₀ K * K := Nat.mul_le_mul_right _ (by omega)

theorem one_le_groupSize {m₀ K d g : ℕ} (hd : 1 ≤ d) (hg : g < numGroups m₀ K d) :
    1 ≤ groupSize m₀ K d g := by
  have := (lt_numGroups_iff hd).1 hg
  exact le_min hd (by omega)

theorem groupEnd_le_m₀ {m₀ K d g : ℕ} (hd : 1 ≤ d) (hg : g < numGroups m₀ K d) :
    groupStart K d g + groupSize m₀ K d g * K ≤ m₀ := by
  have h1 := groupEnd_le (m₀ := m₀) (K := K) (d := d) ((lt_numGroups_iff hd).1 hg).le
  have h2 : numChunks m₀ K * K ≤ m₀ := Nat.div_mul_le_self m₀ K
  omega

/-- Slice positions are not leftover positions. -/
theorem lt_of_mem_slice {m₀ K d g ρ : ℕ} {p : Fin m₀}
    (h : p ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) ρ) :
    (p : ℕ) < numChunks m₀ K * K := by
  rw [mem_slicePos_iff] at h
  obtain ⟨h1, h2, -⟩ := h
  have hD : groupSize m₀ K d g ≠ 0 := by
    intro h0
    rw [h0, zero_mul, add_zero] at h2
    omega
  have hg : g * d ≤ numChunks m₀ K := by
    have := groupSize_le_sub m₀ K d g
    omega
  have := groupEnd_le (m₀ := m₀) (K := K) (d := d) hg
  omega

/-- The group of a slice position `p` is `⌊p / (dK)⌋`. -/
theorem group_eq_div {m₀ K d g ρ : ℕ} {p : Fin m₀}
    (h : p ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) ρ) :
    g = (p : ℕ) / (d * K) := by
  rw [mem_slicePos_iff] at h
  obtain ⟨h1, h2, -⟩ := h
  have h3 : groupSize m₀ K d g * K ≤ d * K := Nat.mul_le_mul_right _ (groupSize_le m₀ K d g)
  unfold groupStart at h1 h2
  symm
  apply Nat.div_eq_of_lt_le
  · rw [← Nat.mul_assoc]
    exact h1
  · rw [Nat.add_mul, one_mul, ← Nat.mul_assoc]
    omega

/-- Within one group, the offset of a slice position is determined by the position. -/
theorem rho_eq {m₀ K d g : ℕ} {ρ ρ' : Fin K} {p : Fin m₀}
    (h : p ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) ρ)
    (h' : p ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) ρ') : ρ = ρ' := by
  rw [mem_slicePos_iff] at h h'
  have := ρ.isLt
  have := ρ'.isLt
  apply Fin.ext
  omega

/-- A position lies in at most one slice. -/
theorem slice_unique {m₀ K d g g' : ℕ} {ρ ρ' : Fin K} {p : Fin m₀}
    (h : p ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) ρ)
    (h' : p ∈ slicePos m₀ K (groupStart K d g') (groupSize m₀ K d g') ρ') :
    g = g' ∧ ρ = ρ' := by
  have hg : g = g' := (group_eq_div h).trans (group_eq_div h').symm
  subst hg
  exact ⟨rfl, rho_eq h h'⟩

/-- Every position below `JK` lies in some slice `(g, ρ)` with `g < ⌈J/d⌉`. -/
theorem exists_slice {m₀ K d : ℕ} (hK : 1 ≤ K) (hd : 1 ≤ d) (p : Fin m₀)
    (hp : (p : ℕ) < numChunks m₀ K * K) :
    ∃ g < numGroups m₀ K d, ∃ ρ : Fin K,
      p ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) ρ := by
  have hdK : 0 < d * K := Nat.mul_pos (by omega) (by omega)
  have hg1 : (p : ℕ) / (d * K) * (d * K) ≤ p := Nat.div_mul_le_self _ _
  have hg2 : (p : ℕ) < (d * K) * ((p : ℕ) / (d * K) + 1) := Nat.lt_mul_div_succ _ hdK
  have hgJ : (p : ℕ) / (d * K) * d < numChunks m₀ K := by
    have : (p : ℕ) / (d * K) * d * K < numChunks m₀ K * K := by
      rw [Nat.mul_assoc]
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hmodK := Nat.mod_lt (p : ℕ) (show 0 < K by omega)
  refine ⟨(p : ℕ) / (d * K), (lt_numGroups_iff hd).2 hgJ, ⟨K - 1 - (p : ℕ) % K, by omega⟩, ?_⟩
  rw [mem_slicePos_iff]
  unfold groupStart
  refine ⟨by rw [Nat.mul_assoc]; exact hg1, ?_, ?_⟩
  · unfold groupSize
    rcases le_total d (numChunks m₀ K - (p : ℕ) / (d * K) * d) with hle | hle
    · rw [min_eq_left hle]
      have : (d * K) * ((p : ℕ) / (d * K) + 1) = (p : ℕ) / (d * K) * d * K + d * K := by ring
      omega
    · rw [min_eq_right hle]
      have : (p : ℕ) / (d * K) * d * K + (numChunks m₀ K - (p : ℕ) / (d * K) * d) * K =
          numChunks m₀ K * K := by
        rw [← Nat.add_mul, Nat.add_sub_cancel' hgJ.le]
      omega
  · show ((p : ℕ) - (p : ℕ) / (d * K) * d * K) % K = K - 1 - (K - 1 - (p : ℕ) % K)
    have hle : K * ((p : ℕ) / (d * K) * d) ≤ p := by
      have : K * ((p : ℕ) / (d * K) * d) = (p : ℕ) / (d * K) * (d * K) := by ring
      omega
    rw [show (p : ℕ) / (d * K) * d * K = K * ((p : ℕ) / (d * K) * d) by ring,
      Nat.sub_mul_mod hle]
    omega

/-! ### One stage -/

/-- The pairs of batch `(g, ρ)` of a stage: those whose target lies in slice `(g, ρ)`. -/
def batchPairs {m₀ : ℕ} (K d g : ℕ) (ρ : Fin K) (pairs : List (Fin m₀ × Fin m₀)) :
    List (Fin m₀ × Fin m₀) :=
  pairs.filter fun p =>
    decide (p.2 ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) (ρ : ℕ))

/-- The pairs of a stage with a leftover target (position `≥ JK`). -/
def leftPairs {m₀ : ℕ} (K : ℕ) (pairs : List (Fin m₀ × Fin m₀)) : List (Fin m₀ × Fin m₀) :=
  pairs.filter fun p => decide (numChunks m₀ K * K ≤ (p.2 : ℕ))

/-- The slice batches of a stage, concatenated in program order. -/
def slicePairs {m₀ : ℕ} (K d : ℕ) (pairs : List (Fin m₀ × Fin m₀)) : List (Fin m₀ × Fin m₀) :=
  (List.range (numGroups m₀ K d)).flatMap fun g =>
    (List.finRange K).flatMap fun ρ => batchPairs K d g ρ pairs

/-- The program of batch `(g, ρ)` of a stage (as in `stageProg`). -/
noncomputable def batchProg {m₀ : ℕ} (P d K g : ℕ) (ρ : Fin K)
    (pairs : List (Fin m₀ × Fin m₀)) : List (WStep m₀) :=
  if (batchPairs K d g ρ pairs).isEmpty then [] else
    cnotBatchProg P d K (groupStart K d g) (groupSize m₀ K d g)
      (m₀ - groupStart K d g - groupSize m₀ K d g * K) ρ (batchPairs K d g ρ pairs)

theorem stageProg_eq {m₀ : ℕ} (P d K : ℕ) (pairs : List (Fin m₀ × Fin m₀)) :
    stageProg P d K pairs =
      ((List.range (numGroups m₀ K d)).flatMap fun g =>
        (List.finRange K).flatMap fun ρ => batchProg P d K g ρ pairs) ++
      (leftPairs K pairs).map (fun p => WStep.cnot1 p.1 p.2) := rfl

theorem mem_batchPairs {m₀ K d g : ℕ} {ρ : Fin K} {pairs : List (Fin m₀ × Fin m₀)}
    {q : Fin m₀ × Fin m₀} :
    q ∈ batchPairs K d g ρ pairs ↔
      q ∈ pairs ∧ q.2 ∈ slicePos m₀ K (groupStart K d g) (groupSize m₀ K d g) (ρ : ℕ) := by
  simp [batchPairs]

theorem mem_leftPairs {m₀ K : ℕ} {pairs : List (Fin m₀ × Fin m₀)} {q : Fin m₀ × Fin m₀} :
    q ∈ leftPairs K pairs ↔ q ∈ pairs ∧ numChunks m₀ K * K ≤ (q.2 : ℕ) := by
  simp [leftPairs]

theorem mem_slicePairs {m₀ K d : ℕ} {pairs : List (Fin m₀ × Fin m₀)} {q : Fin m₀ × Fin m₀} :
    q ∈ slicePairs K d pairs ↔
      ∃ g < numGroups m₀ K d, ∃ ρ : Fin K, q ∈ batchPairs K d g ρ pairs := by
  simp [slicePairs]

/-- The slice batches of a stage followed by its leftover pairs are a permutation of the pairs
of the stage (for a duplicate-free list of pairs). -/
theorem slicePairs_append_leftPairs_perm {m₀ : ℕ} (K d : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (pairs : List (Fin m₀ × Fin m₀)) (hnd : pairs.Nodup) :
    (slicePairs K d pairs ++ leftPairs K pairs).Perm pairs := by
  refine (List.perm_ext_iff_of_nodup ?_ hnd).2 ?_
  · rw [List.nodup_append]
    refine ⟨?_, hnd.filter _, ?_⟩
    · unfold slicePairs
      rw [List.nodup_flatMap]
      refine ⟨fun g _ => ?_, ?_⟩
      · rw [List.nodup_flatMap]
        refine ⟨fun ρ _ => hnd.filter _, ?_⟩
        apply (List.nodup_finRange K).pairwise_of_forall_ne
        intro ρ _ ρ' _ hne q hq hq'
        exact hne (rho_eq (mem_batchPairs.1 hq).2 (mem_batchPairs.1 hq').2)
      · apply List.nodup_range.pairwise_of_forall_ne
        intro g _ g' _ hne q hq hq'
        simp only [List.mem_flatMap] at hq hq'
        obtain ⟨ρ, -, hq⟩ := hq
        obtain ⟨ρ', -, hq'⟩ := hq'
        exact hne (slice_unique (mem_batchPairs.1 hq).2 (mem_batchPairs.1 hq').2).1
    · intro a ha b hb hab
      subst hab
      obtain ⟨g, -, ρ, hb'⟩ := mem_slicePairs.1 ha
      have h1 := lt_of_mem_slice (mem_batchPairs.1 hb').2
      have h2 := (mem_leftPairs.1 hb).2
      omega
  · intro q
    constructor
    · intro hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨g, -, ρ, hb⟩ := mem_slicePairs.1 hq
        exact (mem_batchPairs.1 hb).1
      · exact (mem_leftPairs.1 hq).1
    · intro hq
      by_cases hlt : numChunks m₀ K * K ≤ (q.2 : ℕ)
      · exact List.mem_append_right _ (mem_leftPairs.2 ⟨hq, hlt⟩)
      · obtain ⟨g, hg, ρ, hs⟩ := exists_slice hK hd q.2 (by omega)
        exact List.mem_append_left _ (mem_slicePairs.2 ⟨g, hg, ρ, mem_batchPairs.2 ⟨hq, hs⟩⟩)

/-- One batch program performs the `CNOT` of its batch (Proposition 5.5; an empty batch is the
empty program). -/
theorem batchProg_run (layer : LayerOracle) {m₀ r : ℕ} (P d K : ℕ) (hd : 1 ≤ d)
    (hspec : ∀ (j₀ D nS : ℕ) (ρ : Fin K), j₀ + D * K + nS = m₀ → 1 ≤ D → D ≤ d →
      LayerSpec (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ
        (layer (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ))
    {g : ℕ} (hg : g < numGroups m₀ K d) (ρ : Fin K) (pairs : List (Fin m₀ × Fin m₀))
    (hv : CnotPairsValid (batchPairs K d g ρ pairs)) (z : RArr (Cube m₀) r)
    (hz : ArrOnDiskGrid P z) :
    runProg layer r (batchProg P d K g ρ pairs) z = cnotArr (batchPairs K d g ρ pairs) z := by
  unfold batchProg
  split_ifs with hE
  · rw [List.isEmpty_iff.1 hE, cnotArr_nil]
    rfl
  · have hend := groupEnd_le_m₀ (m₀ := m₀) (K := K) hd hg
    refine (cnot_batch layer P d K (groupStart K d g) (groupSize m₀ K d g)
      (m₀ - groupStart K d g - groupSize m₀ K d g * K) ρ (batchPairs K d g ρ pairs)
      (by omega) (groupSize_le m₀ K d g) hv ?_
      (hspec _ _ _ ρ (by omega) (one_le_groupSize hd hg) (groupSize_le m₀ K d g)) z hz).1
    intro p hp
    simp only [targets, List.mem_toFinset, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (mem_batchPairs.1 hq).2

/-- **One stage**: on disk arrays on the `P`-grid, the program of a valid stage performs the
`CNOT` of the whole stage. -/
theorem stageProg_run (layer : LayerOracle) {m₀ r : ℕ} (P d K : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (hspec : ∀ (j₀ D nS : ℕ) (ρ : Fin K), j₀ + D * K + nS = m₀ → 1 ≤ D → D ≤ d →
      LayerSpec (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ
        (layer (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ))
    (pairs : List (Fin m₀ × Fin m₀)) (hv : CnotPairsValid pairs) (z : RArr (Cube m₀) r)
    (hz : ArrOnDiskGrid P z) :
    runProg layer r (stageProg P d K pairs) z = cnotArr pairs z := by
  have hperm := slicePairs_append_leftPairs_perm K d hK hd pairs (nodup_of_valid hv)
  have hvB : CnotPairsValid (slicePairs K d pairs ++ leftPairs K pairs) :=
    valid_of_perm hv hperm.symm
  have hvS : CnotPairsValid (slicePairs K d pairs) :=
    valid_of_sublist hvB (List.sublist_append_left _ _)
  have hvL : CnotPairsValid (leftPairs K pairs) :=
    valid_of_sublist hvB (List.sublist_append_right _ _)
  have hS : runProg layer r ((List.range (numGroups m₀ K d)).flatMap fun g =>
        (List.finRange K).flatMap fun ρ => batchProg P d K g ρ pairs) z =
      cnotArr (slicePairs K d pairs) z :=
    runProg_flatMap layer P (List.range (numGroups m₀ K d))
      (fun g => (List.finRange K).flatMap fun ρ => batchProg P d K g ρ pairs)
      (fun g => (List.finRange K).flatMap fun ρ => batchPairs K d g ρ pairs)
      (fun g hg hv' z' hz' =>
        runProg_flatMap layer P (List.finRange K) (fun ρ => batchProg P d K g ρ pairs)
          (fun ρ => batchPairs K d g ρ pairs)
          (fun ρ _ hv'' z'' hz'' =>
            batchProg_run layer P d K hd hspec (List.mem_range.1 hg) ρ pairs hv'' z'' hz'')
          hv' z' hz')
      hvS z hz
  rw [stageProg_eq, runProg_append, hS, runProg_map_cnot1 layer _ hvL,
    cnotArr_cnotArr _ _ (valid_cross hvB)]
  exact cnotArr_congr (fun q => hperm.mem_iff) z

theorem batchProg_layerCalls_le {m₀ : ℕ} (P d K g : ℕ) (ρ : Fin K)
    (pairs : List (Fin m₀ × Fin m₀)) : progLayerCalls (batchProg P d K g ρ pairs) ≤ 6 := by
  unfold batchProg
  split_ifs
  · exact Nat.zero_le _
  · rw [progLayerCalls_cnotBatchProg]

theorem batchProg_passes_le {m₀ : ℕ} (P d K g : ℕ) (ρ : Fin K)
    (pairs : List (Fin m₀ × Fin m₀)) : progPasses (batchProg P d K g ρ pairs) ≤ 12 := by
  unfold batchProg
  split_ifs
  · exact Nat.zero_le _
  · rw [progPasses_cnotBatchProg]

/-- A valid stage has at most `m₀ - JK < K` leftover pairs (their targets are distinct positions
in `[JK, m₀)`). -/
theorem leftPairs_length_le {m₀ : ℕ} (K : ℕ) (hK : 1 ≤ K) (pairs : List (Fin m₀ × Fin m₀))
    (hv : CnotPairsValid pairs) : (leftPairs K pairs).length ≤ K := by
  have hvL : CnotPairsValid (leftPairs K pairs) := valid_of_sublist hv (List.filter_sublist)
  have hnd : ((leftPairs K pairs).map fun q => (q.2 : ℕ)).Nodup := by
    have h2 : ((leftPairs K pairs).map Prod.snd).Nodup := (List.nodup_append.1 hvL).2.1
    have := h2.map Fin.val_injective
    simpa [List.map_map, Function.comp_def] using this
  have hsub : ((leftPairs K pairs).map fun q => (q.2 : ℕ)).toFinset ⊆
      Finset.Ico (numChunks m₀ K * K) m₀ := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact Finset.mem_Ico.2 ⟨(mem_leftPairs.1 hq).2, q.2.isLt⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Nat.card_Ico] at hcard
  have hmod : m₀ - numChunks m₀ K * K < K := by
    unfold numChunks
    have := Nat.div_add_mod' m₀ K
    have := Nat.mod_lt m₀ (show 0 < K by omega)
    omega
  omega

theorem stageProg_layerCalls_le {m₀ : ℕ} (P d K : ℕ) (pairs : List (Fin m₀ × Fin m₀)) :
    progLayerCalls (stageProg P d K pairs) ≤ 6 * nSlice m₀ K d := by
  rw [stageProg_eq, progLayerCalls_append, progLayerCalls_map_cnot1, add_zero,
    progLayerCalls_flatMap]
  have h1 : ∀ g, progLayerCalls ((List.finRange K).flatMap fun ρ => batchProg P d K g ρ pairs)
      ≤ K * 6 := by
    intro g
    rw [progLayerCalls_flatMap]
    have := List.sum_le_card_nsmul
      ((List.finRange K).map fun ρ => progLayerCalls (batchProg P d K g ρ pairs)) 6 (by
        intro x hx
        obtain ⟨ρ, -, rfl⟩ := List.mem_map.1 hx
        exact batchProg_layerCalls_le P d K g ρ pairs)
    simpa using this
  have h2 := List.sum_le_card_nsmul
    ((List.range (numGroups m₀ K d)).map fun g =>
      progLayerCalls ((List.finRange K).flatMap fun ρ => batchProg P d K g ρ pairs)) (K * 6) (by
        intro x hx
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
        exact h1 g)
  simp only [List.length_map, List.length_range, smul_eq_mul] at h2
  unfold nSlice
  calc _ ≤ numGroups m₀ K d * (K * 6) := h2
    _ = 6 * (K * numGroups m₀ K d) := by ring

theorem stageProg_passes_le {m₀ : ℕ} (P d K : ℕ) (hK : 1 ≤ K) (pairs : List (Fin m₀ × Fin m₀))
    (hv : CnotPairsValid pairs) :
    progPasses (stageProg P d K pairs) ≤ 12 * nSlice m₀ K d + K := by
  rw [stageProg_eq, progPasses_append, progPasses_map_cnot1, progPasses_flatMap]
  have h1 : ∀ g, progPasses ((List.finRange K).flatMap fun ρ => batchProg P d K g ρ pairs)
      ≤ K * 12 := by
    intro g
    rw [progPasses_flatMap]
    have := List.sum_le_card_nsmul
      ((List.finRange K).map fun ρ => progPasses (batchProg P d K g ρ pairs)) 12 (by
        intro x hx
        obtain ⟨ρ, -, rfl⟩ := List.mem_map.1 hx
        exact batchProg_passes_le P d K g ρ pairs)
    simpa using this
  have h2 := List.sum_le_card_nsmul
    ((List.range (numGroups m₀ K d)).map fun g =>
      progPasses ((List.finRange K).flatMap fun ρ => batchProg P d K g ρ pairs)) (K * 12) (by
        intro x hx
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
        exact h1 g)
  simp only [List.length_map, List.length_range, smul_eq_mul] at h2
  have h3 := leftPairs_length_le K hK pairs hv
  have h4 : numGroups m₀ K d * (K * 12) = 12 * nSlice m₀ K d := by unfold nSlice; ring
  omega

end PosPermAux

/-- **Slice count** (eq. (`eq:walsh-slices`)): `N_slice = K ⌈J/d⌉ ≤ m₀/d + K`.
CONTRACT. -/
theorem nSlice_le (m₀ K d : ℕ) (hd : 1 ≤ d) :
    (nSlice m₀ K d : ℝ) ≤ (m₀ : ℝ) / d + K := by
  have hnat : nSlice m₀ K d * d ≤ m₀ + K * d := by
    unfold nSlice numGroups
    have h1 : (numChunks m₀ K + d - 1) / d * d ≤ numChunks m₀ K + d - 1 :=
      Nat.div_mul_le_self _ _
    have h2 : K * numChunks m₀ K ≤ m₀ := Nat.mul_div_le m₀ K
    calc K * ((numChunks m₀ K + d - 1) / d) * d
        = K * ((numChunks m₀ K + d - 1) / d * d) := by ring
      _ ≤ K * (numChunks m₀ K + d - 1) := Nat.mul_le_mul_left _ h1
      _ ≤ K * (numChunks m₀ K + d) := Nat.mul_le_mul_left _ (by omega)
      _ = K * numChunks m₀ K + K * d := by ring
      _ ≤ m₀ + K * d := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_add' _ _ _ hd'.ne', le_div_iff₀ hd']
  exact_mod_cast hnat

/-- **Theorem 5.8** (positional permutations, `thm:positional-perm`), value and count part. Let
`1 ≤ K`, `1 ≤ d`, and let the oracle satisfy `LayerSpec` at `P_* = P + 8d` for every slice shape
`[2^{j₀}] × [2^K]^D × [2^{nS}]` of the complete `m₀`-bit cube with `1 ≤ D ≤ d`. For every
positional map `π`, on disk arrays on the `P`-grid with records of `r` coefficients, the program
performs the induced record permutation exactly (output in the original grid), with at most
`36 N_slice` completed layer calls and at most `72 N_slice + 6K` passes. CONTRACT. -/
theorem positional_perm (layer : LayerOracle) {m₀ r : ℕ} (P d K : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d) (hspec : ∀ (j₀ D nS : ℕ) (ρ : Fin K), j₀ + D * K + nS = m₀ → 1 ≤ D → D ≤ d →
      LayerSpec (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ (layer (P + 8 * d) r (2 ^ j₀) K D (2 ^ nS) ρ)) (π : Equiv.Perm (Fin m₀)) :
    (∀ z : RArr (Cube m₀) r, ArrOnDiskGrid P z →
        runProg layer r (posPermProg P d K π) z = posPermArr π z) ∧
      progLayerCalls (posPermProg (m₀ := m₀) P d K π) ≤ 36 * nSlice m₀ K d ∧
      progPasses (posPermProg (m₀ := m₀) P d K π) ≤ 72 * nSlice m₀ K d + 6 * K := by
  obtain ⟨hI0, hI1, -⟩ := walsh_involutions π
  obtain ⟨hA0, hB0, h30⟩ := involution_three_stages (r := r) (invol0 ⇑π) hI0
  obtain ⟨hA1, hB1, h31⟩ := involution_three_stages (r := r) (invol1 ⇑π) hI1
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · -- value: each involution program performs `posPermArr I` (three valid stages)
    have hinv : ∀ I : Fin m₀ → Fin m₀, CnotPairsValid (stageA I) → CnotPairsValid (stageB I) →
        (∀ z : RArr (Cube m₀) r,
          posPermArr I z = cnotArr (stageA I) (cnotArr (stageB I) (cnotArr (stageA I) z))) →
        ∀ z : RArr (Cube m₀) r, ArrOnDiskGrid P z →
          runProg layer r (involProg P d K I) z = posPermArr I z := by
      intro I hA hB h3 z hz
      unfold involProg
      rw [PosPermAux.runProg_append, PosPermAux.runProg_append,
        PosPermAux.stageProg_run layer P d K hK hd hspec _ hA z hz,
        PosPermAux.stageProg_run layer P d K hK hd hspec _ hB (cnotArr (stageA I) z)
          (PosPermAux.arrOnDiskGrid_cnotArr _ hz),
        PosPermAux.stageProg_run layer P d K hK hd hspec _ hA
          (cnotArr (stageB I) (cnotArr (stageA I) z))
          (PosPermAux.arrOnDiskGrid_cnotArr _ (PosPermAux.arrOnDiskGrid_cnotArr _ hz)),
        h3 z]
    unfold posPermProg
    rw [PosPermAux.runProg_append, hinv _ hA0 hB0 h30 z hz,
      hinv _ hA1 hB1 h31 _ (PosPermAux.arrOnDiskGrid_posPermArr _ hz), posPermArr_eq_invol π z]
  · -- layer calls: six stages, each with at most `6 N_slice`
    unfold posPermProg involProg
    simp only [PosPermAux.progLayerCalls_append]
    have h := PosPermAux.stageProg_layerCalls_le (m₀ := m₀) P d K
    have := h (stageA (invol0 ⇑π))
    have := h (stageB (invol0 ⇑π))
    have := h (stageA (invol1 ⇑π))
    have := h (stageB (invol1 ⇑π))
    omega
  · -- passes: six stages, each with at most `12 N_slice + K`
    unfold posPermProg involProg
    simp only [PosPermAux.progPasses_append]
    have h := PosPermAux.stageProg_passes_le (m₀ := m₀) P d K hK
    have := h _ hA0
    have := h _ hB0
    have := h _ hA1
    have := h _ hB1
    omega

end SubNLogN.Math.Walsh
