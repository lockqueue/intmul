import WP.W11b.Chain
import WP.W11b.Width
import WP.Top.Obligations

/-!
# WP.W11b.Main — `W9RootOK` and the width bound at the headline

Width profiles (functions of the bit length `n` only):
* `wdF n ℓ = wdI n ℓ = wdHead n = 2·p0 + 3 + 4·specW (hSpec n)` at every level `ℓ`;
* `wR n = wRHead n = 4·p0`.

`w9RootOK_of` derives `WP.Top.W9RootOK` from `chainOK_of` (both transforms), `reqW_le` and the root
clauses `RootStmt` (`WP.W11b.Root`); the leaf clause `LeafStmt` is in `WP.W11b.Leaf`. `width_bound` gives
`hw`. `w11b_main` packages both hypotheses of `intMul_TM2_nlogn_current2`.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- The root clauses of `RootOK` (proved in `WP.W11b.Root`). -/
def RootStmt : Prop :=
  ∀ (n A B : ℕ) (cSpec : ComputablePaperFastDFTSpec),
    TablesFaithful cSpec (IntMulTM.Contracts.W8.hSpec n) →
    let b := IntMulTM.Contracts.W8.hB n
    let K0 := IntMulTM.Contracts.W8.hK0 n
    let k := IntMulTM.Contracts.W8.hK n
    let p0 := rootPrecision b K0
    let x0 := rootPackV b K0 k k A B
    let y := computablePaperFastDFT b cSpec x0
    let z := rootSquareV p0 K0 y
    let v := computablePaperFastDFT p0 cSpec z
    NodeInv (IntMulTM.Contracts.W8.hSpec n) b x0 ∧ NodeInv (IntMulTM.Contracts.W8.hSpec n) p0 z ∧
      y.size = 2 ^ K0 ∧ ArrW (wRHead n) x0 ∧ ArrW (wRHead n) y ∧ ArrW (wRHead n) z ∧
      v.size = 2 ^ K0 ∧ ArrW (wRHead n) v ∧ ∀ c ∈ rootDigits b K0 k k v, bitLen c ≤ wRHead n

/-- On faithful hierarchies the chain's width requirement is bounded by the schedule. -/
theorem reqW_le {spec : QuantizedFastDFTSpec} (hvalid : spec.Valid) :
    ∀ {cSpec : ComputablePaperFastDFTSpec}, TablesFaithful cSpec spec → ∀ p_in : ℕ,
      reqW cSpec p_in ≤ max (spec.p + p_in + 3) (4 * specW spec) := by
  induction hvalid with
  | base p R =>
    intro cSpec hfaith p_in
    cases hfaith with
    | base p K tw _ _ _ =>
      simp only [reqW, specW, QuantizedFastDFTSpec.p, Nat.log2_two_pow]
      omega
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p
      hchild hv1 hv1_lt ih =>
    intro cSpec hfaith p_in
    cases hfaith with
    | step _ _ _ _ _ _ ft preTw postTw c0T c1T cChild _ _ _ _ _ _ hchild_faith =>
      have h := ih hchild_faith (2 * pChild p K)
      rw [hchild_p] at h
      have hpc : 12 ≤ pChild p K := by rw [pChild_eq_additive]; omega
      simp only [reqW, specW, QuantizedFastDFTSpec.p]
      omega

theorem w9RootOK_of (hleaf : LeafStmt) (hroot : RootStmt) :
    WP.Top.W9RootOK (fun n _ => wdHead n) (fun n _ => wdHead n) wRHead := by
  intro n A B cSpec _ _ _ hj
  have hfaith : TablesFaithful cSpec (IntMulTM.Contracts.W8.hSpec n) := hj.faithful
  obtain ⟨hx0, hz, hy, hwx0, hwy, hwz, hv, hwv, hdig⟩ := hroot n A B cSpec hfaith
  have hp0 : 8 ≤ IntMulTM.Contracts.W8.hP0 n := (W7.headline_pre n).1
  have hvalid : (IntMulTM.Contracts.W8.hSpec n).Valid := buildQuantizedSpecPaperStop_valid _ _ _ hp0
  have hsp : (IntMulTM.Contracts.W8.hSpec n).p = IntMulTM.Contracts.W8.hP0 n :=
    buildQuantizedSpecPaperStop_p _ _ _
  have hb : IntMulTM.Contracts.W8.hB n ≤ IntMulTM.Contracts.W8.hP0 n := by
    unfold IntMulTM.Contracts.W8.hP0 rootPrecision
    omega
  have hreq : ∀ p_in ≤ IntMulTM.Contracts.W8.hP0 n, ∀ ℓ' : ℕ, reqW cSpec p_in ≤ wdHead n := by
    intro p_in hpin _
    refine (reqW_le hvalid hfaith p_in).trans ?_
    rw [hsp]
    unfold wdHead
    omega
  refine ⟨chainOK_of hleaf _ hvalid cSpec hfaith hj.canonical hj.widths _ 0 _ (hreq _ hb)
      (by simpa using hx0),
    chainOK_of hleaf _ hvalid cSpec hfaith hj.canonical hj.widths _ 0 _ (hreq _ le_rfl)
      (by simpa using hz), hy, hwx0, hwy, hwz, hv, hwv, hdig⟩

/-- Both W11b hypotheses of `intMul_TM2_nlogn_current2`, from the leaf and root clauses. -/
theorem w11b_main (hleaf : LeafStmt) (hroot : RootStmt) :
    WP.Top.W9RootOK (fun n _ => wdHead n) (fun n _ => wdHead n) wRHead ∧
      ∃ cw, ∀ n ≥ 1, ∀ ℓ : ℕ, (fun n (_ : ℕ) => wdHead n) n ℓ ≤ cw * (Nat.log2 n + 1) ∧
        (fun n (_ : ℕ) => wdHead n) n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wRHead n ≤ cw * (Nat.log2 n + 1) := by
  refine ⟨w9RootOK_of hleaf hroot, ?_⟩
  obtain ⟨cw, h⟩ := width_bound
  exact ⟨cw, fun n hn _ => ⟨(h n hn).1, (h n hn).1, (h n hn).2⟩⟩

#assert_std_axioms reqW_le w9RootOK_of w11b_main

end WP.W11b
