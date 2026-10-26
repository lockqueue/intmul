import WP.W14.Step
import WP.W14.Bridge

/-!
# W14: admissible schedules and the multi-level error bound

* `StepsSatisfy P spec`: every step node `(p, K)` of `spec` satisfies `P`.
* `Admissible S P`: the schedule `S` meets `StepSlots` at every step node satisfying `P` (with
  `8 ≤ p`, `2 ≤ K`, which `Valid` guarantees) and `LeafSlot` at every leaf.
* `sincGaussianFastDFTOfTablesAt_error_le`: FTP:2250 for any admissible schedule.
* `computablePaperFastDFTAt_faithful_error_le`: FTP:2285 for the parametric integer pipeline.
-/

namespace WP.W14

open IntMul Complex Real

/-- Every step node `(p, K)` of a schedule satisfies `P`. -/
def StepsSatisfy (P : ℕ → ℕ → Prop) : QuantizedFastDFTSpec → Prop
  | .base _ _ => True
  | .step p K _ _ _ _ child => P p K ∧ StepsSatisfy P child

/-- A schedule is admissible on the step nodes satisfying `P`: `StepSlots` holds there, and
`LeafSlot` holds at every leaf. -/
structure Admissible (S : StepSchedule) (P : ℕ → ℕ → Prop) : Prop where
  step : ∀ p K, 8 ≤ p → 2 ≤ K → P p K → StepSlots (S.pSub p K) (S.m1 p K) p K
  leaf : ∀ p K, 8 ≤ p → K ≤ 5 * p → LeafSlot (S.qLeaf p K) p K

/-- **Multi-level error bound at an admissible schedule** (FTP:2250 generalized). -/
theorem sincGaussianFastDFTOfTablesAt_error_le
    (S : StepSchedule) (P : ℕ → ℕ → Prop) (hS : Admissible S P)
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hP : StepsSatisfy P spec)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithfulAt S cSpec spec)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < spec.size, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < spec.size) :
    ‖sincGaussianFastDFTOfTablesAt S.qLeaf cSpec x u - dft1D spec.size x u‖ ≤
      (2 : ℝ) ^ (-(spec.p : ℤ)) * M := by
  induction hvalid generalizing cSpec x M u with
  | base p R =>
    cases hfaith with
    | @base p K twiddles hp hK_le htw =>
      dsimp only [sincGaussianFastDFTOfTablesAt, baseRadix2FFTOfTwiddlesAt,
        QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx ⊢
      exact norm_baseRadix2FFTOfTwiddlesAt_sub_dft1D_le (S.qLeaf p K) p K twiddles htw
        (hS.leaf p K hp hK_le) x M hM1 hx u
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p
      _hchild hv1 _hv1_lt ih =>
    cases hfaith with
    | @step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      obtain ⟨hPpK, hPchild⟩ := hP
      dsimp only [sincGaussianFastDFTOfTablesAt, QuantizedFastDFTSpec.size,
        QuantizedFastDFTSpec.p] at hx hu ⊢
      exact step_error_le_at hp hK ht1 ht1_le hr hr_le hsize hc1 heven hv1 hv1_eq
        (hS.step p K hp hK hPpK)
        filterTaps preTwiddles postTwiddles c0Table c1Table
        hTaps hPre hPost (fun u2 hu2 => hC01 u2 hu2)
        (sincGaussianFastDFTOfTablesAt S.qLeaf cChild)
        (fun x' M' hM1' hx' u' hu' => by
          rw [← hchild_p, ← hchild_size]
          exact ih hPchild cChild hchild_faith x' M' hM1' (by rwa [hchild_size]) u'
            (by rwa [hchild_size]))
        x M hM1 hx u hu

/-- **Error bound for the parametric integer pipeline** (FTP:2285 generalized). -/
theorem computablePaperFastDFTAt_faithful_error_le
    (S : StepSchedule) (P : ℕ → ℕ → Prop) (hS : Admissible S P)
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hP : StepsSatisfy P spec)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithfulAt S cSpec spec)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ k < spec.size, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < spec.size) :
    ‖toScaledComplex spec.p (read1D (computablePaperFastDFTValAt S.qLeaf p_in cSpec xArr) u) -
        dft1D spec.size x u‖ ≤
      (2 : ℝ) ^ (-(spec.p : ℤ)) * M := by
  rw [toScaledComplex_computablePaperFastDFTAt_eq S spec hvalid cSpec hfaith p_in xArr x hx u hu]
  exact sincGaussianFastDFTOfTablesAt_error_le S P hS spec hvalid hP cSpec hfaith x M hM1 hM u hu

#assert_std_axioms sincGaussianFastDFTOfTablesAt_error_le computablePaperFastDFTAt_faithful_error_le

end WP.W14
