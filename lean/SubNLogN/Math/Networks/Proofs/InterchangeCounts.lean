import SubNLogN.Math.Networks.AppCCounts
import SubNLogN.Math.Networks.Proofs.Incidence
import SubNLogN.Math.Networks.Proofs.C4Specialize
import SubNLogN.Math.Networks.Proofs.Counting
import SubNLogN.Math.Networks.Proofs.CellSoundBit

/-!
# Child-call counts of the Proposition A.7 (`prop:transfer11`) recursion

Proves the two `interchangeProc` contracts of `SubNLogN/Math/Networks/AppCCounts.lean`:
* `interchangeCallCount_holds : InterchangeCallCountStmt`: under `C5Params q fac`, one level of
  `interchangeProc q fac (k + 1) h₀ d₀` performs exactly `tripleSb 100` child calls;
* `interchangeNonCallBound_holds : InterchangeNonCallBoundStmt`: one level has at most
  `E = mH + B + 2 mH` non-call operations, where
  `B = |Stage| (|Fix 100| (8 (|Role .bit 100| · 11 mH + 1))) + |Role .bit 100| · 11 mH + 1`
  (`nonCalls_bitNodeOps_le`); `E` does not depend on the layout, `k`, the positions, `q` or `fac`.

Kernel note: the bound is written out as an expression everywhere (no named constant). A kernel
check that unfolds a closed `ℕ`-valued constant containing `Fintype.card (Fix 100)` tries to
evaluate that cardinality (observed: deterministic timeout at 41 GiB), so every step is arranged
to match syntactically.

Route. The primitives `subHSteps`/`hMinusDSteps` of one level perform no calls; all calls are in
the bit-network node `bitNodeOps`. The edge program `edgeOpsB` of an edge is `shearOps` of its
factorization data and performs one call per pivot (`calls_shearOps`). Summing over the rows
`(j, ι, r)` of `bitNodeOps` counts every gate of `touch w` exactly once (`gateAt` returns the unique
gate of `w` in a row, `FI.touch_unique`; `sum_rows_eq_sum_touch`), so the total is
`Σ_w Σ_{e ∈ edges w} |piv (fac A_e)|` (`Incidence.sum_edges`). By `FacData.Valid`
(`|piv| = rank A_e`), `edgeMatFin_rank` and the bit certificate total (B4, the `rank_sum` field of
`bitNetCert_holds`: `Cell.prop7_rank_sum Cell.soundBit_holds Cell.sumClassOfBit_holds`), this is
`tripleSb 100`. The non-call bound uses `|piv| ≤ mH`
(distinct pivot rows). No enumeration of `Role .bit 100`, `Fix 100` or `Fin mH` is evaluated: all
counts go through generic `flatMap`/`length`/`Finset.sum` lemmas.

All helpers are in the namespace `SubNLogN.Math.Networks.InterchangeCountsAux`.
-/

namespace SubNLogN.Math.Networks
namespace InterchangeCountsAux
open Model

/-! ## Counting role operations -/

/-- Child calls among a list of role operations (the `Model.Op.callCount` of a node). -/
def calls {L : Layout} {β : Type} {W : ℕ} {Child : Type} (l : List (RoleOp L β W Child)) : ℕ :=
  (l.filter RoleOp.isCall).length

/-- Non-call role operations of a list (the `Model.Op.nonCallCount` of a node). -/
def nonCalls {L : Layout} {β : Type} {W : ℕ} {Child : Type} (l : List (RoleOp L β W Child)) : ℕ :=
  (l.filter fun o => !o.isCall).length

section Counting
variable {L : Layout} {β : Type} {W : ℕ} {Child : Type}

theorem calls_nil : calls ([] : List (RoleOp L β W Child)) = 0 := rfl
theorem nonCalls_nil : nonCalls ([] : List (RoleOp L β W Child)) = 0 := rfl

theorem calls_append (l₁ l₂ : List (RoleOp L β W Child)) :
    calls (l₁ ++ l₂) = calls l₁ + calls l₂ := by
  simp only [calls, List.filter_append, List.length_append]

theorem nonCalls_append (l₁ l₂ : List (RoleOp L β W Child)) :
    nonCalls (l₁ ++ l₂) = nonCalls l₁ + nonCalls l₂ := by
  simp only [nonCalls, List.filter_append, List.length_append]

theorem calls_prim_cons (k : Fin W) (s : Step L β) (l : List (RoleOp L β W Child)) :
    calls (RoleOp.prim k s :: l) = calls l := rfl

theorem nonCalls_prim_cons (k : Fin W) (s : Step L β) (l : List (RoleOp L β W Child)) :
    nonCalls (RoleOp.prim k s :: l) = nonCalls l + 1 := rfl

theorem calls_call_cons (k : Fin W) (c : Child) (l : List (RoleOp L β W Child)) :
    calls (RoleOp.call k c :: l) = calls l + 1 := rfl

theorem nonCalls_call_cons (k : Fin W) (c : Child) (l : List (RoleOp L β W Child)) :
    nonCalls (RoleOp.call k c :: l) = nonCalls l := rfl

theorem calls_flatMap {ι : Type*} (l : List ι) (f : ι → List (RoleOp L β W Child)) :
    calls (l.flatMap f) = (l.map fun a => calls (f a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, calls_append, ih, List.map_cons, List.sum_cons]

theorem nonCalls_flatMap {ι : Type*} (l : List ι) (f : ι → List (RoleOp L β W Child)) :
    nonCalls (l.flatMap f) = (l.map fun a => nonCalls (f a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, nonCalls_append, ih, List.map_cons, List.sum_cons]

theorem calls_map_prim (k : Fin W) (l : List (Step L β)) :
    calls (l.map (RoleOp.prim k) : List (RoleOp L β W Child)) = 0 := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [List.map_cons, calls_prim_cons, ih]

theorem nonCalls_map_prim (k : Fin W) (l : List (Step L β)) :
    nonCalls (l.map (RoleOp.prim k) : List (RoleOp L β W Child)) = l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [List.map_cons, nonCalls_prim_cons, ih, List.length_cons]

end Counting

/-- Length of a `flatMap` all of whose pieces are pairs. -/
theorem length_flatMap_pair {α γ : Type*} (l : List α) (g₁ g₂ : α → γ) :
    (l.flatMap fun a => [g₁ a, g₂ a]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [List.length_cons, List.length_nil]
    omega

theorem length_lowerSteps {L : Layout} {β : Type} (R t₀ b : ℕ) (E : Matrix (Fin mH) (Fin mH) ℚ) :
    (lowerSteps (L := L) (β := β) R t₀ b E).length = 2 * mH := by
  unfold lowerSteps
  rw [length_flatMap_pair, List.length_reverse, List.length_finRange]

theorem length_subHSteps {L : Layout} {β : Type} (R h₀ d₀ b : ℕ) :
    (subHSteps (L := L) (β := β) R h₀ d₀ b).length = mH := by
  unfold subHSteps
  rw [List.length_map, List.length_finRange]

theorem length_hMinusDSteps {L : Layout} {β : Type} (R h₀ d₀ b : ℕ) :
    (hMinusDSteps (L := L) (β := β) R h₀ d₀ b).length = 2 * mH := by
  unfold hMinusDSteps
  rw [length_flatMap_pair, List.length_finRange]

/-! ## Edge programs -/

/-- The Lemma A.6 (`lem:transfer-shear`) shear program of an edge performs one child call per pivot. -/
theorem calls_shearOps {L : Layout} {β : Type} {W : ℕ} {Child : Type} (R h₀ d₀ b : ℕ) (k : Fin W)
    (F : FacData) (childOf : Fin mH → Fin mH → Child) :
    calls (shearOps (L := L) (β := β) R h₀ d₀ b k F childOf) = F.piv.length := by
  simp only [shearOps, calls_append, calls_map_prim, calls_flatMap, calls_prim_cons,
    calls_call_cons, calls_nil, List.map_const', List.sum_replicate_nat]
  omega

/-- The Lemma A.6 (`lem:transfer-shear`) shear program of an edge has `8 mH` triangular steps and three further steps per pivot. -/
theorem nonCalls_shearOps {L : Layout} {β : Type} {W : ℕ} {Child : Type} (R h₀ d₀ b : ℕ)
    (k : Fin W) (F : FacData) (childOf : Fin mH → Fin mH → Child) :
    nonCalls (shearOps (L := L) (β := β) R h₀ d₀ b k F childOf) = 8 * mH + 3 * F.piv.length := by
  simp only [shearOps, nonCalls_append, nonCalls_map_prim, length_lowerSteps, nonCalls_flatMap,
    nonCalls_prim_cons, nonCalls_call_cons, nonCalls_nil, List.map_const', List.sum_replicate_nat]
  omega

/-- The pivot count of the edge of `w` entering `v` (`0` if there is none). -/
noncomputable def pivOf (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (w : Role .bit 100)
    (v : Vertex .bit 100) : ℕ :=
  ((edgeInto w v).map fun e => (fac (edgeMatFin e)).piv.length).getD 0

theorem calls_edgeOpsB {L : Layout} {β : Type} {Child : Type} (R h₀ d₀ b : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (childOf : Fin mH → Fin mH → Child)
    (w : Role .bit 100) (v : Vertex .bit 100) :
    calls (edgeOpsB (L := L) (β := β) R h₀ d₀ b fac childOf w v) = pivOf fac w v := by
  unfold edgeOpsB pivOf
  split
  · rename_i e he
    simp only [he, calls_shearOps, Option.map_some, Option.getD_some]
  · rename_i he
    simp only [he, calls_nil, Option.map_none, Option.getD_none]

/-- Each edge program has at most `11 mH` non-call operations (at most `mH` pivots, since the
pivot rows are distinct). -/
theorem nonCalls_edgeOpsB_le {L : Layout} {β : Type} {Child : Type} {q : ℕ}
    {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    (R h₀ d₀ b : ℕ) (childOf : Fin mH → Fin mH → Child) (w : Role .bit 100)
    (v : Vertex .bit 100) :
    nonCalls (edgeOpsB (L := L) (β := β) R h₀ d₀ b fac childOf w v) ≤ 11 * mH := by
  unfold edgeOpsB
  split
  · rename_i e he
    rw [nonCalls_shearOps]
    obtain ⟨-, -, -, -, -, -, hnd, -⟩ := hfac w e (FI.edgeInto_mem he)
    have hle := hnd.length_le_card
    rw [List.length_map, Fintype.card_fin] at hle
    omega
  · exact Nat.zero_le _

/-- For an edge `e` of `w` entering `v`, the pivot count is the rank of the edge map. -/
theorem pivOf_eq_rankQ {q : ℕ} {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    {w : Role .bit 100} {v : Vertex .bit 100} {e : Vertex .bit 100 × Vertex .bit 100}
    (he : edgeInto w v = some e) : pivOf fac w v = rankQ (edgeMatB e) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlen, -⟩ := hfac w e (FI.edgeInto_mem he)
  simp only [pivOf, he, Option.map_some, Option.getD_some]
  rw [hlen, edgeMatFin_rank]

/-- Per role: the gate edges and the sink edge carry `Σ_{e ∈ edges w} rank_ℚ A_e` pivots. -/
theorem sum_pivOf_eq_rank {q : ℕ} {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    (w : Role .bit 100) :
    ((touch w).map fun g => pivOf fac w (.gate g)).sum + pivOf fac w (.sink w) =
      ((edges w).map fun e => rankQ (edgeMatB e)).sum := by
  rw [Incidence.sum_edges]
  exact congrArg₂ (· + ·)
    (congrArg List.sum
      (List.map_congr_left fun g hg => pivOf_eq_rankQ hfac (FI.edgeInto_gate w g hg)))
    (pivOf_eq_rankQ hfac (FI.edgeInto_sink w))

/-! ## Rows of the bit-network node versus gates of a role -/

theorem sum_stages {M : Type*} [AddCommMonoid M] (f : Stage → M) :
    ([Stage.one, .two, .three].map f).sum = ∑ j : Stage, f j := by
  have hu : (Finset.univ : Finset Stage) = {Stage.one, Stage.two, Stage.three} := by
    ext j; cases j <;> simp
  rw [hu, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  simp

/-- Only the coordinates of `g` contribute. -/
theorem sum_coords {h : ℕ} (g : Gate h) (x : ℕ) :
    (∑ j : Stage, ∑ ι : Fix h, ∑ r : Fin 8,
      if g.stage = j ∧ g.inv = ι ∧ g.time = r then x else 0) = x := by
  rw [Finset.sum_eq_single_of_mem g.stage (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem g.inv (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem g.time (Finset.mem_univ _)]
      · simp
      · intro r _ hr
        exact if_neg fun hc => hr hc.2.2.symm
    · intro ι _ hι
      exact Finset.sum_eq_zero fun r _ => if_neg fun hc => hι hc.2.1.symm
  · intro j _ hj
    exact Finset.sum_eq_zero fun ι _ => Finset.sum_eq_zero fun r _ => if_neg fun hc => hj hc.1.symm

/-- **Bridge**: summing a gate-indexed count over all rows `(j, ι, r)` (`0` where `w` has no gate)
gives the sum over the gates of `w`, with multiplicity. -/
theorem sum_rows_eq_sum_touch {κ : Kind} {h : ℕ} (w : Role κ h) (F : Gate h → ℕ)
    (cnt : Stage → Fix h → Fin 8 → ℕ)
    (hsome : ∀ j ι r g, gateAt j ι r w = some g → cnt j ι r = F g)
    (hnone : ∀ j ι r, gateAt j ι r w = none → cnt j ι r = 0) :
    ∑ j : Stage, ∑ ι : Fix h, ∑ r : Fin 8, cnt j ι r = ((touch w).map F).sum := by
  have hpt : ∀ j ι r, cnt j ι r = ∑ g ∈ (touch w).toFinset,
      if g.stage = j ∧ g.inv = ι ∧ g.time = r then F g else 0 := by
    intro j ι r
    cases hga : gateAt j ι r w with
    | none =>
      rw [hnone j ι r hga]
      symm
      refine Finset.sum_eq_zero fun g hg => if_neg fun hc => ?_
      have hgs := FI.gateAt_of_mem (List.mem_toFinset.1 hg) hc.1 hc.2.1 hc.2.2
      rw [hga] at hgs
      cases hgs
    | some g₀ =>
      rw [hsome j ι r g₀ hga]
      obtain ⟨hm, hs, hi, ht⟩ := FI.gateAt_spec hga
      rw [Finset.sum_eq_single_of_mem g₀ (List.mem_toFinset.2 hm)]
      · rw [if_pos ⟨hs, hi, ht⟩]
      · intro g hg hne
        refine if_neg fun hc => hne ?_
        exact FI.touch_unique (List.mem_toFinset.1 hg) hm (hc.1.trans hs.symm)
          (hc.2.2.trans ht.symm)
  calc ∑ j : Stage, ∑ ι : Fix h, ∑ r : Fin 8, cnt j ι r
      = ∑ j : Stage, ∑ ι : Fix h, ∑ r : Fin 8, ∑ g ∈ (touch w).toFinset,
          (if g.stage = j ∧ g.inv = ι ∧ g.time = r then F g else 0) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ι _ =>
          Finset.sum_congr rfl fun r _ => hpt j ι r
    _ = ∑ j : Stage, ∑ ι : Fix h, ∑ g ∈ (touch w).toFinset, ∑ r : Fin 8,
          (if g.stage = j ∧ g.inv = ι ∧ g.time = r then F g else 0) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ι _ => Finset.sum_comm
    _ = ∑ j : Stage, ∑ g ∈ (touch w).toFinset, ∑ ι : Fix h, ∑ r : Fin 8,
          (if g.stage = j ∧ g.inv = ι ∧ g.time = r then F g else 0) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ g ∈ (touch w).toFinset, ∑ j : Stage, ∑ ι : Fix h, ∑ r : Fin 8,
          (if g.stage = j ∧ g.inv = ι ∧ g.time = r then F g else 0) := Finset.sum_comm
    _ = ∑ g ∈ (touch w).toFinset, F g := Finset.sum_congr rfl fun g _ => sum_coords g (F g)
    _ = ((touch w).map F).sum := List.sum_toFinset F (Incidence.touch_nodup w)

/-- Moving the role sum outermost. -/
theorem sum_swap4 {M : Type*} [AddCommMonoid M] (X : Stage → Fix 100 → Fin 8 → Role .bit 100 → M) :
    ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .bit 100, X j ι r w =
      ∑ w : Role .bit 100, ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, X j ι r w := by
  calc _ = ∑ j : Stage, ∑ ι : Fix 100, ∑ w : Role .bit 100, ∑ r : Fin 8, X j ι r w :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ι _ => Finset.sum_comm
    _ = ∑ j : Stage, ∑ w : Role .bit 100, ∑ ι : Fix 100, ∑ r : Fin 8, X j ι r w :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-! ## The node of the bit network -/

section Shape
variable {L : Layout} {β : Type} {W : ℕ} {Child : Type}

/-- A count of role operations that is additive along `++`, on a `flatMap`. -/
theorem count_flatMap (cntL : List (RoleOp L β W Child) → ℕ) (hnil : cntL [] = 0)
    (happ : ∀ l₁ l₂, cntL (l₁ ++ l₂) = cntL l₁ + cntL l₂) {ι : Type*} (l : List ι)
    (f : ι → List (RoleOp L β W Child)) : cntL (l.flatMap f) = (l.map fun a => cntL (f a)).sum := by
  induction l with
  | nil => exact hnil
  | cons a l ih => rw [List.flatMap_cons, happ, ih, List.map_cons, List.sum_cons]

/-- An additive count over the shape of `bitNodeOps`. -/
theorem count_nodeShape (cntL : List (RoleOp L β W Child) → ℕ) (hnil : cntL [] = 0)
    (happ : ∀ l₁ l₂, cntL (l₁ ++ l₂) = cntL l₁ + cntL l₂)
    (E : Stage → Fix 100 → Fin 8 → Role .bit 100 → List (RoleOp L β W Child))
    (G : Stage → Fix 100 → Fin 8 → RoleOp L β W Child)
    (Sk : Role .bit 100 → List (RoleOp L β W Child)) (o : RoleOp L β W Child) :
    cntL (([Stage.one, .two, .three].flatMap fun j =>
        (Finset.univ : Finset (Fix 100)).toList.flatMap fun ι =>
          (List.finRange 8).flatMap fun r =>
            ((Finset.univ : Finset (Role .bit 100)).toList.flatMap fun w => E j ι r w) ++
              [G j ι r]) ++
        ((Finset.univ : Finset (Role .bit 100)).toList.flatMap fun w => Sk w) ++ [o]) =
      (∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8,
        ((∑ w : Role .bit 100, cntL (E j ι r w)) + cntL [G j ι r])) +
        (∑ w : Role .bit 100, cntL (Sk w)) + cntL [o] := by
  simp only [happ, count_flatMap cntL hnil happ, Finset.sum_map_toList, sum_stages,
    ← Fin.sum_univ_def]

end Shape

/-- An upper bound for a sum of the shape produced by `count_nodeShape`. -/
theorem sumShape_le (a : Stage → Fix 100 → Fin 8 → Role .bit 100 → ℕ)
    (bG : Stage → Fix 100 → Fin 8 → ℕ) (s : Role .bit 100 → ℕ) (o c : ℕ)
    (hE : ∀ j ι r w, a j ι r w ≤ c) (hG : ∀ j ι r, bG j ι r ≤ 1) (hSk : ∀ w, s w ≤ c)
    (ho : o ≤ 1) :
    (∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ((∑ w : Role .bit 100, a j ι r w) + bG j ι r)) +
        (∑ w : Role .bit 100, s w) + o ≤
      Fintype.card Stage * (Fintype.card (Fix 100) *
        (8 * (Fintype.card (Role .bit 100) * c + 1))) +
        Fintype.card (Role .bit 100) * c + 1 := by
  have h1 : ∀ j ι r, (∑ w : Role .bit 100, a j ι r w) + bG j ι r ≤
      Fintype.card (Role .bit 100) * c + 1 := by
    intro j ι r
    refine Nat.add_le_add ?_ (hG j ι r)
    calc (∑ w : Role .bit 100, a j ι r w) ≤ ∑ _w : Role .bit 100, c :=
          Finset.sum_le_sum fun w _ => hE j ι r w
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h2 : (∑ w : Role .bit 100, s w) ≤ Fintype.card (Role .bit 100) * c := by
    calc (∑ w : Role .bit 100, s w) ≤ ∑ _w : Role .bit 100, c :=
          Finset.sum_le_sum fun w _ => hSk w
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h3 : (∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8,
      ((∑ w : Role .bit 100, a j ι r w) + bG j ι r)) ≤
      Fintype.card Stage * (Fintype.card (Fix 100) *
        (8 * (Fintype.card (Role .bit 100) * c + 1))) := by
    calc _ ≤ ∑ _j : Stage, ∑ _ι : Fix 100, ∑ _r : Fin 8, (Fintype.card (Role .bit 100) * c + 1) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ι _ =>
            Finset.sum_le_sum fun r _ => h1 j ι r
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
  exact Nat.add_le_add (Nat.add_le_add h3 h2) ho

/-- `bitNodeOps` has `Σ_w (Σ_{g ∈ touch w} piv(gate g) + piv(sink w))` child calls. -/
theorem calls_bitNodeOps {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    {Child : Type} (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) :
    calls (bitNodeOps (L := L) (β := β) R h₀ d₀ b fac childOf) =
      ∑ w : Role .bit 100, (((touch w).map fun g => pivOf fac w (.gate g)).sum +
        pivOf fac w (.sink w)) := by
  unfold bitNodeOps
  rw [count_nodeShape calls calls_nil calls_append]
  have hG : ∀ (j : Stage) (ι : Fix 100) (r : Fin 8),
      calls [(gateOpB (L := L) (β := β) (Child := Child) j ι r)] = 0 := fun _ _ _ => rfl
  have ho : calls [(RoleOp.relabel rhoPerm : RoleOp L β Wb Child)] = 0 := rfl
  simp only [hG, ho, add_zero]
  rw [sum_swap4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [calls_edgeOpsB, sum_rows_eq_sum_touch w (fun g => pivOf fac w (.gate g)) _ ?_ ?_]
  · intro j ι r g hg
    simp only [hg, calls_edgeOpsB]
  · intro j ι r hg
    simp only [hg, calls_nil]

/-- `bitNodeOps` has a bounded number of non-call operations: `8 |Stage| |Fix 100|` row blocks of
at most `|Role .bit 100|` edge programs (`≤ 11 mH` each) and one gate, the sink edge programs and
the relabelling. (The bound is kept as an explicit expression, not a named constant, so that no
kernel check ever has to unfold it.) -/
theorem nonCalls_bitNodeOps_le {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    {Child : Type} {q : ℕ} {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData}
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    (R h₀ d₀ b : ℕ) (childOf : Fin mH → Fin mH → Child) :
    nonCalls (bitNodeOps (L := L) (β := β) R h₀ d₀ b fac childOf) ≤
      Fintype.card Stage * (Fintype.card (Fix 100) *
        (8 * (Fintype.card (Role .bit 100) * (11 * mH) + 1))) +
        Fintype.card (Role .bit 100) * (11 * mH) + 1 := by
  unfold bitNodeOps
  rw [count_nodeShape nonCalls nonCalls_nil nonCalls_append]
  refine sumShape_le _ _ _ _ (11 * mH) ?_ ?_ ?_ ?_
  · intro j ι r w
    split
    · exact nonCalls_edgeOpsB_le hfac R h₀ d₀ b childOf w _
    · exact Nat.zero_le _
  · intro j ι r
    exact le_of_eq rfl
  · intro w
    exact nonCalls_edgeOpsB_le hfac R h₀ d₀ b childOf w _
  · exact le_of_eq rfl

/-! ## One level of `interchangeProc` -/

section Level
variable {L : Layout} {β : Type} {Child : Type}

theorem callCount_prim (s : Step L β) :
    Model.Op.callCount (Model.Op.prim s : Model.Op L β Child) = 0 := rfl

theorem nonCallCount_prim (s : Step L β) :
    Model.Op.nonCallCount (Model.Op.prim s : Model.Op L β Child) = 1 := rfl

theorem sum_callCount_map_prim (l : List (Step L β)) :
    ((l.map (Model.Op.prim : Step L β → Model.Op L β Child)).map Model.Op.callCount).sum = 0 := by
  induction l with
  | nil => rfl
  | cons s l ih => simp only [List.map_cons, List.sum_cons, ih, callCount_prim, Nat.add_zero]

theorem sum_nonCallCount_map_prim (l : List (Step L β)) :
    ((l.map (Model.Op.prim : Step L β → Model.Op L β Child)).map Model.Op.nonCallCount).sum =
      l.length := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.length_cons, nonCallCount_prim,
      Nat.add_comm]

theorem callCount_node (W : ℕ) (hW : 0 < W) (ops : List (RoleOp L β W Child)) :
    Model.Op.callCount (Model.Op.node W hW ops) = calls ops := rfl

theorem nonCallCount_node (W : ℕ) (hW : 0 < W) (ops : List (RoleOp L β W Child)) :
    Model.Op.nonCallCount (Model.Op.node W hW ops) = nonCalls ops := rfl

end Level

/-- The unfolding of one level of `interchangeProc`. -/
theorem interchangeProc_succ {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) :
    interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀ =
      ((subHSteps (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim ++
        [Model.Op.node Wb Wb_pos (bitNodeOps (q ^ mH ^ k) h₀ d₀ (mH ^ k) fac
          (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
            (d₀ + j.val * mH ^ k)))] ++
        (hMinusDSteps (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim :
          List (Model.Op L β (ProcK L β k))) := rfl

/-- The child calls of one level of `interchangeProc` are those of its bit-network node. -/
theorem callCount_interchangeProc {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) :
    ProcK.callCount k (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀) =
      calls (bitNodeOps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k) fac
        (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
          (d₀ + j.val * mH ^ k))) := by
  unfold ProcK.callCount
  rw [interchangeProc_succ]
  simp only [List.map_append, List.sum_append, sum_callCount_map_prim, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, callCount_node, Nat.add_zero, Nat.zero_add]

/-- The non-call operations of one level of `interchangeProc`. -/
theorem nonCallCount_interchangeProc {L : Layout} {β : Type} [AddCommGroup β]
    [Module (ZMod 2) β] (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) :
    ProcK.nonCallCount k (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀) =
      mH + nonCalls (bitNodeOps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k) fac
        (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
          (d₀ + j.val * mH ^ k))) + 2 * mH := by
  unfold ProcK.nonCallCount
  rw [interchangeProc_succ]
  simp only [List.map_append, List.sum_append, sum_nonCallCount_map_prim, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, nonCallCount_node, Nat.add_zero, length_subHSteps,
    length_hMinusDSteps]


end InterchangeCountsAux

open Model InterchangeCountsAux

/-- **Proposition A.7 (`prop:transfer11`) child count.** Under `C5Params q fac`, one level of `interchangeProc q fac (k + 1) h₀ d₀`
performs exactly `s_b = tripleSb 100` child calls. -/
theorem interchangeCallCount_holds : InterchangeCallCountStmt := by
  intro L β _ _ q fac k h₀ d₀ hC
  obtain ⟨-, -, -, hfac⟩ := hC
  rw [callCount_interchangeProc, calls_bitNodeOps,
    Finset.sum_congr rfl fun w _ => sum_pivOf_eq_rank hfac w,
    Cell.prop7_rank_sum Cell.soundBit_holds Cell.sumClassOfBit_holds]

/-- **Proposition A.7 (`prop:transfer11`) non-call operations.** One level of `interchangeProc` has at most
`mH + B + 2 mH` non-call operations (`B` as in `nonCalls_bitNodeOps_le`): `mH` steps of
`subHSteps`, at most `B` in the bit-network node, `2 mH` steps of `hMinusDSteps`. -/
theorem interchangeNonCallBound_holds : InterchangeNonCallBoundStmt := by
  refine ⟨mH + (Fintype.card Stage * (Fintype.card (Fix 100) *
      (8 * (Fintype.card (Role .bit 100) * (11 * mH) + 1))) +
      Fintype.card (Role .bit 100) * (11 * mH) + 1) + 2 * mH, ?_⟩
  intro L β _ _ q fac k h₀ d₀ hC
  obtain ⟨-, -, -, hfac⟩ := hC
  rw [nonCallCount_interchangeProc]
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (nonCalls_bitNodeOps_le (L := L) (β := β) hfac (q ^ mH ^ k) h₀ d₀ (mH ^ k)
      (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
        (d₀ + j.val * mH ^ k))) mH) (2 * mH)

end SubNLogN.Math.Networks
