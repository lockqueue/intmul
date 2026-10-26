import WP.W14.Admissible

/-!
# W14: the paper's stop rule as a schedule invariant

* `PaperStopRule p K`: `[MS]` recurses at a node only while `R = 2^K > 4 p²` (`[MS]`, §7.1, Listing 1; Theorem 1, §7.2).
* `PaperStopValid spec`: `spec.Valid` and every step node satisfies `PaperStopRule` (deviation D13:
  the snapshot's step lemma has no stop-rule hypothesis; the paper-schedule closure needs it for the
  raw-tap B2 bound).
* `buildQuantizedSpecPaperStop_paperStopValid`: the snapshot's paper-stop builder (PSR:43) satisfies it.
* `paperStop_window_budget`: under the stop rule, `5 (2 m1Paper + 1) + 1 ≤ 2^(K+1)`.
-/

namespace WP.W14

open IntMul

/-- The paper's stop rule at a step node: `4 p² < 2^K`. -/
def PaperStopRule (p K : ℕ) : Prop := 4 * p * p < 2 ^ K

/-- `Valid`, and every step node satisfies the paper's stop rule. -/
def PaperStopValid (spec : QuantizedFastDFTSpec) : Prop :=
  spec.Valid ∧ StepsSatisfy PaperStopRule spec

theorem buildQuantizedSpecPaperStop_stepsSatisfy (L p K : ℕ) :
    StepsSatisfy PaperStopRule (buildQuantizedSpecPaperStop L p K) := by
  induction L generalizing p K with
  | zero => simp only [buildQuantizedSpecPaperStop, StepsSatisfy]
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · simp only [StepsSatisfy]
    · simp only [quantizedBoxGaussianStepSpec, StepsSatisfy]
      exact ⟨not_le.mp hstop, ih _ _⟩

/-- The paper-stop builder satisfies `PaperStopValid` (for `8 ≤ p`). -/
theorem buildQuantizedSpecPaperStop_paperStopValid (L p K : ℕ) (hp : 8 ≤ p) :
    PaperStopValid (buildQuantizedSpecPaperStop L p K) :=
  ⟨buildQuantizedSpecPaperStop_valid L p K hp, buildQuantizedSpecPaperStop_stepsSatisfy L p K⟩

/-- Under the stop rule with `8 ≤ p`, `K ≥ 9`. -/
theorem nine_le_of_paperStop {p K : ℕ} (hp : 8 ≤ p) (h : PaperStopRule p K) : 9 ≤ K := by
  unfold PaperStopRule at h
  by_contra hK
  push_neg at hK
  have h1 : 2 ^ K ≤ 256 :=
    calc 2 ^ K ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 256 := by norm_num
  have h2 : 256 ≤ 4 * p * p := by nlinarith
  omega

theorem ten_mul_add_le_two_pow {K : ℕ} (hK : 9 ≤ K) : 10 * K + 61 ≤ 2 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

/-- **Stop-rule geometry.** Under the paper's stop rule, the folded window width is tiny compared
with the transform length: `5 (2 m1Paper + 1) + 1 ≤ 2^(K+1)`. -/
theorem paperStop_window_budget {p K : ℕ} (hp : 8 ≤ p) (h : PaperStopRule p K) :
    5 * (2 * m1Paper p K + 1) + 1 ≤ 2 ^ (K + 1) := by
  have hK9 := nine_le_of_paperStop hp h
  have hpc_eq := pChild_eq_additive p K
  have hpc : 26 ≤ pChild p K := by omega
  have hm := m1Paper_upper p K hpc
  have h32 : 32 * p ≤ 4 * p * p := by nlinarith
  have h10 := ten_mul_add_le_two_pow hK9
  unfold PaperStopRule at h
  rw [pow_succ]
  omega

#assert_std_axioms buildQuantizedSpecPaperStop_stepsSatisfy buildQuantizedSpecPaperStop_paperStopValid
  nine_le_of_paperStop ten_mul_add_le_two_pow paperStop_window_budget

end WP.W14
