import WP.W11b.PostOK
import Contracts.W7.Shapes

/-!
# WP.W11b.Chain — `ChainOK` along any valid schedule with faithful, canonical tables

`chainOK_of`: if every root node satisfies `NodeInv` and the width profile dominates `reqW` at every
level, then `ChainOK wd cSpec p_in ℓ xs` holds. Induction on `spec.Valid`, mirroring the snapshot's
`allCallSitesWidthSound_of_faithful` (CSWS:1787): the PRE clauses by `preNodeOK_of`, the POST
clauses by `postNodeOK_of` (with `qHat_eq_qHatV`), the tables by `W7.EntryWidths`/`W7.Canonical`,
and the next level by the children's node invariant (`preNode_children`). The leaf clause is the
hypothesis `LeafStmt` (proved in `WP.W11b.Leaf`).

`reqW_le`: on faithful hierarchies `reqW` is bounded by the schedule-side `specW`.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- The leaf clause of `ChainOK` (proved in `WP.W11b.Leaf`). -/
def LeafStmt : Prop :=
  ∀ (wd : ℕ → ℕ) (ℓ p K p_in : ℕ) (tw : Array (Array (ℤ × ℤ))), 8 ≤ p →
    (∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex (2 * p + K + 8) (read1D (tw.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤ 2 * complexQuantizeMaxErr (2 * p + K + 8)) →
    W7.EntryWidths W7.snapshotFormat (.basePow2 p K tw) →
    reqW (.basePow2 p K tw) p_in ≤ wd ℓ →
    ∀ xs : List (Array (ℤ × ℤ)), (∀ x ∈ xs, NodeInv (.base p (2 ^ K)) p_in x) →
      ChainOK wd (.basePow2 p K tw) p_in ℓ xs

theorem preDims_of {K t1 r : ℕ} (ht1 : 0 < t1) (ht1_le : t1 ≤ 2 ^ (K / 2))
    (hsize : t1 * r = 2 ^ K) (heven : t1 % 2 = 0) (p_in pSub m1 : ℕ) :
    PreDims ⟨p_in, pSub, m1, t1, r⟩ := by
  obtain ⟨ht1_pow, -⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  obtain ⟨hr_pow, -⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
  have htr : t1 ≤ r := by
    have h1 : t1 * t1 ≤ 2 ^ (K / 2) * 2 ^ (K / 2) := Nat.mul_le_mul ht1_le ht1_le
    have h2 : 2 ^ (K / 2) * 2 ^ (K / 2) ≤ 2 ^ K := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : t1 * t1 ≤ t1 * r := by rw [hsize]; exact h1.trans h2
    exact Nat.le_of_mul_le_mul_left h3 ht1
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t1 = 2 ^ natLog2Fuel t1 t1
    rw [natLog2Fuel_self]
    exact ht1_pow.symm
  · show r = 2 ^ natLog2Fuel r r
    rw [natLog2Fuel_self]
    exact hr_pow.symm
  · show 1 ≤ natLog2Fuel t1 t1
    rw [natLog2Fuel_self]
    by_contra hcon
    have h0 : Nat.log2 t1 = 0 := by omega
    rw [h0, pow_zero] at ht1_pow
    omega
  · show natLog2Fuel t1 t1 ≤ natLog2Fuel r r
    rw [natLog2Fuel_self, natLog2Fuel_self]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [ht1_pow, hr_pow]; exact htr)

theorem exists_getD_of_mem {A : Array (Array (ℤ × ℤ))} {y : Array (ℤ × ℤ)} (h : y ∈ A.toList) :
    ∃ v1 < A.size, A.getD v1 #[] = y := by
  obtain ⟨v1, hv1, rfl⟩ := List.getElem_of_mem h
  have hv1' : v1 < A.size := by simpa using hv1
  exact ⟨v1, hv1', by simp [Array.getD, hv1']⟩

theorem chainOK_of (hleaf : LeafStmt) (wd : ℕ → ℕ) {spec : QuantizedFastDFTSpec}
    (hvalid : spec.Valid) :
    ∀ (cSpec : ComputablePaperFastDFTSpec), TablesFaithful cSpec spec → W7.Canonical cSpec →
      W7.EntryWidths W7.snapshotFormat cSpec → ∀ (p_in ℓ : ℕ) (xs : List (Array (ℤ × ℤ))),
      (∀ ℓ', reqW cSpec p_in ≤ wd ℓ') → (∀ x ∈ xs, NodeInv spec p_in x) →
      ChainOK wd cSpec p_in ℓ xs := by
  induction hvalid with
  | base p R =>
    intro cSpec hfaith _ hew p_in ℓ xs hw hxs
    cases hfaith with
    | base p K tw hp _ htw => exact hleaf wd ℓ p K p_in tw hp htw hew (hw ℓ) xs hxs
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p
      hchild hv1 hv1_lt ih =>
    intro cSpec hfaith hcan hew p_in ℓ xs hw hxs
    cases hfaith with
    | step _ _ _ _ _ _ ft preTw postTw c0T c1T cChild _ hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      have hvs : (QuantizedFastDFTSpec.step p K t1 r c1 v1Of child).Valid :=
        .step hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt
      have hfs : TablesFaithful
          (.step p (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw c0T c1T cChild)
          (.step p K t1 r c1 v1Of child) :=
        .step p K t1 r c1 v1Of ft preTw postTw c0T c1T cChild child hv1_eq hTaps hPre hPost hC01
          hchild_faith
      obtain ⟨-, hcanTaps, -, -, -, -, hcanChild⟩ := hcan
      obtain ⟨hewTaps, hewTw, hewC, hewChild⟩ := hew
      have hpc12 : 12 ≤ pChild p K := by rw [pChild_eq_additive]; omega
      have hwℓ := hw ℓ
      simp only [reqW] at hwℓ
      have hw1 : p + p_in + 3 ≤ wd ℓ := by omega
      have hw2 : 3 * (2 * pChild p K) + 3 ≤ wd ℓ := by omega
      have hacs : ∀ x ∈ xs, AllCallSitesWidthSound p_in
          (.step p (2 * pChild p K) (2 * pChild p K) t1 r ft preTw postTw c0T c1T cChild) x :=
        fun x hx => allCallSitesWidthSound_of_faithful _ hvs _ hfs p_in x (xOf p_in x)
          (fun k _ => rfl) (hxs x hx).2
      have hC : ∀ u2 < r, (read1D c0T u2).2 = 0 ∧ (read1D c1T u2).2 = 0 ∧
          0 ≤ (read1D c0T u2).1 ∧ (read1D c0T u2).1 ≤ (2 : ℤ) ^ (2 * pChild p K + 2) ∧
          0 ≤ (read1D c1T u2).1 ∧ (read1D c1T u2).1 ≤ (2 : ℤ) ^ (2 * pChild p K + 2) := by
        intro u2 hu2
        obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := hC01 u2 hu2
        exact ⟨h0, h1, h2, h3, h4, h5⟩
      have hdiv : ∀ u2 < r,
          0 < IntMulTM.Contracts.W8.columnDivisor r u2 (read1D c0T u2).1 (read1D c1T u2).1 :=
        fun u2 hu2 => (hewC u2 hu2).2.2.2.2.2.2
      refine ⟨preDims_of ht1 ht1_le hsize heven _ _ _, ?_, ?_, fun x hx => ⟨(hxs x hx).1, ?_⟩,
        fun i hi => ?_, ?_⟩
      · refine ⟨fun j hj => ⟨fun g hg => (hewTaps j hj g hg).trans (by omega), ?_⟩,
          fun k hk => ?_, fun k hk => ?_⟩
        · rw [hcanTaps j hj]
        · exact ⟨(hewTw k hk).1.trans (by omega), (hewTw k hk).2.1.trans (by omega)⟩
        · exact ⟨(hewTw k hk).2.2.1.trans (by omega), (hewTw k hk).2.2.2.trans (by omega)⟩
      · intro u2 hu2
        obtain ⟨h0, h1, -, hb0, -, hb1, -⟩ := hewC u2 hu2
        exact ⟨h0, h1, hb0.trans (by unfold barrettH; omega), hb1.trans (by unfold barrettH; omega)⟩
      · exact preNodeOK_of hp hK hr hsize hTaps hw1 hw2 (hxs x hx).1 (hxs x hx).2 (hacs x hx)
      · have hmem : xs.getD i #[] ∈ xs := by
          rw [List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem hi
        rw [qHat_eq_qHatV p_in (2 * pChild p K) t1 r ft preTw postTw cChild xs hi]
        exact postNodeOK_of hchild hchild_size hchild_p ht1 hr hsize hc1 hchild_faith hTaps hPre hPost
          hC hdiv hw2 (hxs _ hmem).2 (hacs _ hmem)
      · refine ih cChild hchild_faith hcanChild hewChild (2 * pChild p K) (ℓ + 1) _
          (fun ℓ' => ?_) ?_
        · have h := hw ℓ'
          simp only [reqW] at h
          omega
        · intro y hy
          rw [List.mem_flatMap] at hy
          obtain ⟨x, hx, hyx⟩ := hy
          obtain ⟨v1, hv1, rfl⟩ := exists_getD_of_mem hyx
          rw [size_preNodeV] at hv1
          have hc := preNode_children ht1 hr hsize hc1 hTaps hPre hPost (hxs x hx).2 v1 hv1
          refine ⟨by rw [hchild_size]; exact hc.1, fun k hk => ?_⟩
          rw [hchild_p]
          exact hc.2 k (hchild_size ▸ hk)

#assert_std_axioms preDims_of exists_getD_of_mem chainOK_of

end WP.W11b
