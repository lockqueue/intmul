import WP.W14.Exact
import WP.W14.PaperSlots

/-!
# W14 headline: exact multiplication at the paper's schedule, stop rule and root

* `paperSpec n`: the paper's recursion for `n`-bit operands — the snapshot's paper-stop builder
  (`R ≤ 4 p²` at leaves, PSR:43) at the paper's root `paperRoot n` (`b = max 4 ⌊log₂ n⌋`,
  `N = max 1 ⌈n/b⌉`, `K0 = ⌈log₂ 2N⌉`) and root precision `p0 = 2b + 2K0 + 6` (T5:41).
* `computablePaperFastDFTMultiply_faithful_eq_mul_paper`: for any tables faithful at
  `paperSchedule` (sub-step grid `pChild`, window `m1Paper`, leaf grid `p + K + 2`), the
  schedule-parametric integer multiplier returns `A * B` for all `A, B < 2^n`.
* Non-vacuity: the round-to-nearest paper tables are faithful
  (`idealRoundedTablesAt_paperSpec_faithful`), giving the unconditional corollary
  `paperMultiply_idealTables_eq_mul`.
-/

namespace WP.W14

open IntMul

/-- The paper's recursion fuel `⌊log₂ (K0 - 1)⌋` (as in the snapshot, CSWS:2267; it never binds
before the stop rule). -/
def paperFuel (n : ℕ) : ℕ := Nat.log2 ((paperRoot n).K0 - 1)

/-- The paper's recursion for `n`-bit operands. -/
def paperSpec (n : ℕ) : QuantizedFastDFTSpec :=
  buildQuantizedSpecPaperStop (paperFuel n)
    (rootPrecision (paperRoot n).b (paperRoot n).K0) (paperRoot n).K0

theorem paperSpec_size (n : ℕ) : (paperSpec n).size = 2 ^ (paperRoot n).K0 :=
  buildQuantizedSpecPaperStop_size _ _ _

theorem paperSpec_p (n : ℕ) :
    (paperSpec n).p = rootPrecision (paperRoot n).b (paperRoot n).K0 :=
  buildQuantizedSpecPaperStop_p _ _ _

theorem paperSpec_paperStopValid (n : ℕ) : PaperStopValid (paperSpec n) :=
  buildQuantizedSpecPaperStop_paperStopValid _ _ _ (paperRoot_p0_ge n)

theorem paperSpec_paperExecutableValid (n : ℕ) : (paperSpec n).PaperExecutableValid := by
  apply buildQuantizedSpecPaperStop_paperExecutableValid _ _ _ (paperRoot_p0_ge n)
  have hlt : (paperRoot n).K0 - 1 < 2 ^ (paperFuel n + 1) := lt_two_pow_log2_succ _
  omega

/-- **Schedule-parametric exactness** (the `[MS]` §7 contract `computablePaperFastDFTMultiply_faithful_eq_mul_at`):
any admissible schedule, any `Valid` recursion whose step nodes satisfy the admissibility
predicate, any tables faithful at the schedule. -/
theorem computablePaperFastDFTMultiply_faithful_eq_mul_at
    (S : StepSchedule) (P : ℕ → ℕ → Prop) (hS : Admissible S P)
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hP : StepsSatisfy P spec)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithfulAt S cSpec spec)
    (b K0 k1 k2 : ℕ) (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    computablePaperFastDFTMultiplyAt S.qLeaf cSpec b K0 k1 k2 A B = A * B :=
  computablePaperFastDFTMultiplyAt_faithful_eq_mul S P hS spec hvalid hP cSpec hfaith
    b K0 k1 k2 hsize hp0 hk A B hA hB

/-- **W14 headline.** Exactness at the paper's schedule (`pSub = pChild`, `m1 = m1Paper`,
`q_leaf = p + K + 2`), the paper's stop rule and the paper's root (limb count `⌈n/b⌉`). -/
theorem computablePaperFastDFTMultiply_faithful_eq_mul_paper (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (cSpec : ComputablePaperFastDFTSpec)
    (hfaith : TablesFaithfulAt paperSchedule cSpec (paperSpec n)) :
    computablePaperFastDFTMultiplyAt paperSchedule.qLeaf cSpec (paperRoot n).b (paperRoot n).K0
      (paperRoot n).k (paperRoot n).k A B = A * B :=
  computablePaperFastDFTMultiplyAt_faithful_eq_mul paperSchedule PaperStopRule
    paperSchedule_admissible (paperSpec n) (paperSpec_paperStopValid n).1
    (paperSpec_paperStopValid n).2 cSpec hfaith
    (paperRoot n).b (paperRoot n).K0 (paperRoot n).k (paperRoot n).k
    (paperSpec_size n) (paperSpec_p n) (paperRoot_hk n) A B
    (paperRoot_lt_of_lt n A hA) (paperRoot_lt_of_lt n B hB)

/-- **Non-vacuity.** The round-to-nearest tables at the paper's schedule are faithful. -/
theorem idealRoundedTablesAt_paperSpec_faithful (n : ℕ) :
    TablesFaithfulAt paperSchedule (idealRoundedTablesAt paperSchedule (paperSpec n)) (paperSpec n) :=
  idealRoundedTablesAt_faithful paperSchedule (paperSpec n) (paperSpec_paperStopValid n).1
    (paperSpec_paperExecutableValid n)

/-- Unconditional corollary with the (noncomputable) round-to-nearest paper tables. -/
theorem paperMultiply_idealTables_eq_mul (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computablePaperFastDFTMultiplyAt paperSchedule.qLeaf
      (idealRoundedTablesAt paperSchedule (paperSpec n)) (paperRoot n).b (paperRoot n).K0
      (paperRoot n).k (paperRoot n).k A B = A * B :=
  computablePaperFastDFTMultiply_faithful_eq_mul_paper n A B hA hB _
    (idealRoundedTablesAt_paperSpec_faithful n)

#assert_std_axioms paperSpec_size paperSpec_p paperSpec_paperStopValid paperSpec_paperExecutableValid
  computablePaperFastDFTMultiply_faithful_eq_mul_at computablePaperFastDFTMultiply_faithful_eq_mul_paper
  idealRoundedTablesAt_paperSpec_faithful paperMultiply_idealTables_eq_mul

end WP.W14
