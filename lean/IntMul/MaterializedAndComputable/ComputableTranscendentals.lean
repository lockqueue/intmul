import IntMul.MaterializedAndComputable.PaperHeadlinePipeline

/-!
# Part 2b — Computable Fixed-Point Series Evaluators in `BitCostM`

This module implements 100% computable (`def`, zero `noncomputable`) fixed-point series evaluators
for `π`, `ln 2`, `stdChar(±num/den)`, `sincGaussian`, and `c0Coeff`/`c1Coeff` of `realErfScaled`,
with accumulated `BitCostM` bit-complexity accounting and proven `1`-ULP accuracy bounds.
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

attribute [local instance 10000] instZeroIntElementary

/-! ### 1. Universal Fixed-Point Rounding, Clamping, and `BitCostM` Recurrence-Series Primitives -/

/-- Signed two's-complement word-width predicate on a scalar integer `z : ℤ` (`FitsSignedScalarWord`, `[MS]` §3.2). -/
def FitsSignedScalarWord (w : ℕ) (z : ℤ) : Prop :=
  |z| < (2 : ℤ) ^ (w - 1)

theorem fitsSignedScalarWord_mono {w1 w2 : ℕ} {z : ℤ}
    (h : FitsSignedScalarWord w1 z) (hw : w1 ≤ w2) :
    FitsSignedScalarWord w2 z := by
  unfold FitsSignedScalarWord at h ⊢
  have hpow : (2 : ℤ) ^ (w1 - 1) ≤ (2 : ℤ) ^ (w2 - 1) := by
    exact_mod_cast Nat.pow_le_pow_right zero_lt_two (by omega)
  exact h.trans_le hpow

theorem fitsSignedScalarWord_of_abs_le_two_pow (w : ℕ) (z : ℤ)
    (hz : |(z : ℝ)| ≤ (2 : ℝ) ^ (w - 2)) (hw : 2 ≤ w := by omega) :
    FitsSignedScalarWord w z := by
  unfold FitsSignedScalarWord
  have hlt : (2 : ℝ) ^ (w - 2) < (2 : ℝ) ^ (w - 1) :=
    pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)
  have h1 : |(z : ℝ)| < (2 : ℝ) ^ (w - 1) := hz.trans_lt hlt
  rw [← Int.cast_abs] at h1
  exact_mod_cast h1

theorem fitsSignedScalarWord_of_nat_le_two_pow (w n : ℕ)
    (hn : n ≤ 2 ^ (w - 2)) (hw : 2 ≤ w := by omega) :
    FitsSignedScalarWord w (n : ℤ) := by
  refine fitsSignedScalarWord_of_abs_le_two_pow w (n : ℤ) ?_ hw
  rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
  exact_mod_cast hn

theorem fitsSignedScalarWord_of_natAbs_le_two_pow (w E : ℕ) (z : ℤ)
    (hz : z.natAbs ≤ 2 ^ E) (hw : E + 2 ≤ w) :
    FitsSignedScalarWord w z := by
  refine fitsSignedScalarWord_of_abs_le_two_pow w z ?_ (by omega)
  have h1 : |(z : ℝ)| ≤ (2 : ℝ) ^ E := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hz
  exact h1.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))

/-- Costed integer square root `Nat.sqrt n` charged at operand bit-width `w`
(`2 * computableMulBitCost w + 2 * addBitCost w`). -/
def costedNatSqrt (w n : ℕ) : BitCostM ℕ :=
  (Nat.sqrt n, 2 * computableMulBitCost w + 2 * addBitCost w)

/-- Costed integer clamping `max lo (min hi x)` charged at bit-width `w` (`2 * addBitCost w`). -/
def costedClampInt (w : ℕ) (lo hi x : ℤ) : BitCostM ℤ :=
  (max lo (min hi x), 2 * addBitCost w)

/-- Costed power-of-two left shift `x * 2^s` on `ℕ` charged at bit-width `w` (`addBitCost w`). -/
abbrev costedShiftLeftNat (w x s : ℕ) : BitCostM ℕ :=
  (x * 2 ^ s, addBitCost w)

/-- Costed power-of-two left shift `x * 2^s` on `ℤ` charged at bit-width `w` (`addBitCost w`). -/
abbrev costedShiftLeftInt (w : ℕ) (x : ℤ) (s : ℕ) : BitCostM ℤ :=
  (x * ((2 ^ s : ℕ) : ℤ), addBitCost w)

/-- Sign-negated integer `-x` for alternating Taylor series step numerators (`-num^2`, `-numY`). -/
abbrev costedNegInt0 (x : ℤ) : BitCostM ℤ :=
  (-x, 0)

/-- Conditional sign application `if neg then -x else x` on `ℤ` (billed in the caller's `addBitCost w` budget). -/
abbrev costedCondNegInt0 (neg : Bool) (x : ℤ) : BitCostM ℤ :=
  (if neg then -x else x, 0)

/-- Costed symmetric power-of-two clamping `max (-2^B) (min (2^B) x)` charged at bit-width `w`
(`2 * addBitCost w`). -/
abbrev costedSymmClampPow2Int (w B : ℕ) (x : ℤ) : BitCostM ℤ :=
  (max (-((2 ^ B : ℕ) : ℤ)) (min ((2 ^ B : ℕ) : ℤ) x), 2 * addBitCost w)

/-- Costed integer sum shifted left by `2^B`: `((a + b) * 2^B, addBitCost w)`. -/
abbrev costedAddShiftLeftInt (w : ℕ) (a b : ℤ) (B : ℕ) : BitCostM ℤ :=
  ((a + b) * ((2 ^ B : ℕ) : ℤ), addBitCost w)

/-- Costed integer difference shifted left by `2^B`: `((a - b) * 2^B, addBitCost w)`. -/
abbrev costedSubShiftLeftInt (w : ℕ) (a b : ℤ) (B : ℕ) : BitCostM ℤ :=
  ((a - b) * ((2 ^ B : ℕ) : ℤ), addBitCost w)

/-- Signed integer index difference `(a : ℤ) - (b : ℤ)` for tap offset setup. -/
abbrev costedSubNatToInt0 (a b : ℕ) : BitCostM ℤ :=
  ((a : ℤ) - (b : ℤ), 0)

/-- Absolute tap offset numerator `(prodT - (j1 : ℤ)).natAbs` (billed in the caller's `addBitCost w` budget). -/
abbrev costedSubNatAbsInt0 (prodT : ℤ) (j1 : ℕ) : BitCostM ℕ :=
  ((prodT - (j1 : ℤ)).natAbs, 0)

/-- One step of the fixed-point rounded Taylor recurrence at operand width `w` (`recurrenceStepCosted`):
given state `(a_k, s_k)` where `a_k` is the `k`-th scaled term and `s_k` is the partial sum of
the first `k` terms:
- accumulates `s_{k+1} = s_k + a_k` (charging `addBitCost w`),
- computes `num_{k+1} = (a_k * stepNum) * stepNumFactor k` via `costedMulInt w`,
- computes `den_{k+1} = stepDenFactor k * baseDen` via `costedMulInt w` (plus `computableMulBitCost w`
  for forming `stepDenFactor k`), and
- computes `a_{k+1} = divRoundRatInt num_{k+1} den_{k+1}` via `costedDivRoundRatInt w`. -/
def recurrenceStepCosted (w : ℕ) (stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (k : ℕ) (state : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  let a_k := state.1
  let s_k := state.2
  let s_next := s_k + a_k
  let num1Res := costedMulInt w a_k stepNum
  let num2Res := costedMulInt w num1Res.1 ((stepNumFactor k : ℕ) : ℤ)
  let denRes := costedMulInt w ((stepDenFactor k : ℕ) : ℤ) (baseDen : ℤ)
  let a_nextRes := costedDivRoundRatInt w num2Res.1 denRes.1
  ((a_nextRes.1, s_next),
    addBitCost w + num1Res.2 + num2Res.2 + computableMulBitCost w + denRes.2 + a_nextRes.2)

/-- Structural-recursion fixed-point Taylor series evaluator (`runRecurrenceSeriesCosted`):
starting from initial scaled term `a0` and partial sum `0`, runs `n` steps of `recurrenceStepCosted`. -/
def runRecurrenceSeriesCosted (w : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) : ℕ → BitCostM (ℤ × ℤ)
  | 0 => ((a0, 0), 0)
  | n + 1 =>
    let prev := runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor n
    let step := recurrenceStepCosted w stepNum baseDen stepNumFactor stepDenFactor n prev.1
    (step.1, prev.2 + step.2)

@[simp]
theorem runRecurrenceSeriesCosted_snd (w : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (n : ℕ) :
    (runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor n).2 =
      n * (6 * computableMulBitCost w + 3 * addBitCost w) := by
  induction n with
  | zero => simp [runRecurrenceSeriesCosted]
  | succ n ih =>
    dsimp only [runRecurrenceSeriesCosted, recurrenceStepCosted, costedDivRoundRatInt, costedMulInt]
    rw [ih]
    ring

theorem runRecurrenceSeriesCosted_fst_fst_indep_w (w1 w2 : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (n : ℕ) :
    (runRecurrenceSeriesCosted w1 a0 stepNum baseDen stepNumFactor stepDenFactor n).1 =
      (runRecurrenceSeriesCosted w2 a0 stepNum baseDen stepNumFactor stepDenFactor n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [runRecurrenceSeriesCosted, recurrenceStepCosted, costedDivRoundRatInt, costedMulInt]
    rw [ih]

theorem runRecurrenceSeriesCosted_fst_snd_eq_sum (w : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (n : ℕ) :
    (runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor n).1.2 =
      ∑ k ∈ Finset.range n,
        (runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [runRecurrenceSeriesCosted, recurrenceStepCosted]
    rw [ih, Finset.sum_range_succ,
        runRecurrenceSeriesCosted_fst_fst_indep_w w 0 a0 stepNum baseDen stepNumFactor stepDenFactor n]

/-- Per-call-site operand width soundness for all `N` steps of `runRecurrenceSeriesCosted`:
every call to `costedDivRoundRatInt w` and `costedMulInt w` at every step `k < N` has both
operands fitting strictly inside a signed `w`-bit word (`FitsSignedScalarWord w`), and the
running partial sum `s_k` also fits in `w` bits. -/
def RecurrenceCallSitesWidthSound (w : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (N : ℕ) : Prop :=
  FitsSignedScalarWord w stepNum ∧
  FitsSignedScalarWord w (baseDen : ℤ) ∧
  ∀ k < N,
    let st := (runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor k).1
    let a_k := st.1
    let s_k := st.2
    FitsSignedScalarWord w a_k ∧
    FitsSignedScalarWord w s_k ∧
    FitsSignedScalarWord w ((stepNumFactor k : ℕ) : ℤ) ∧
    FitsSignedScalarWord w ((stepDenFactor k : ℕ) : ℤ) ∧
    FitsSignedScalarWord w (a_k * stepNum) ∧
    FitsSignedScalarWord w (a_k * stepNum * ((stepNumFactor k : ℕ) : ℤ)) ∧
    FitsSignedScalarWord w (((stepDenFactor k : ℕ) : ℤ) * (baseDen : ℤ))

/-- Nearest-integer rounding `divRoundRatInt num den` is within `1 / 2` of `num / den` for `0 < den`. -/
theorem abs_divRoundRatInt_sub_le (num den : ℤ) (hden : 0 < den) :
    |(divRoundRatInt num den : ℝ) - (num : ℝ) / (den : ℝ)| ≤ 1 / 2 := by
  rw [divRoundRatInt_eq_floor num den hden]
  set x : ℝ := (num : ℝ) / (den : ℝ)
  have h1 : (⌊x + 1 / 2⌋ : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have h2 : x + 1 / 2 - 1 < (⌊x + 1 / 2⌋ : ℝ) := Int.sub_one_lt_floor (x + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

theorem abs_divRoundRatInt_sub_div_le (num den : ℤ) (hden : 0 < den) :
    |(divRoundRatInt num den : ℝ) - (num : ℝ) / (den : ℝ)| ≤ 1 / 2 :=
  abs_divRoundRatInt_sub_le num den hden

theorem abs_divRoundRatInt_le (num den : ℤ) (hden : 0 < den) :
    |(divRoundRatInt num den : ℝ)| ≤ |(num : ℝ)| / (den : ℝ) + 1 / 2 := by
  have h1 := abs_divRoundRatInt_sub_le num den hden
  have hden_r : (0 : ℝ) < (den : ℝ) := Int.cast_pos.mpr hden
  have h2 : |(num : ℝ) / (den : ℝ)| = |(num : ℝ)| / (den : ℝ) := by
    rw [abs_div, abs_of_pos hden_r]
  have htri := abs_add_le
    ((divRoundRatInt num den : ℝ) - (num : ℝ) / (den : ℝ))
    ((num : ℝ) / (den : ℝ))
  rw [sub_add_cancel, h2] at htri
  linarith

/-- Monotonicity of `divRoundRatInt`: if `0 ≤ num` and `0 < den`, then `0 ≤ divRoundRatInt num den`. -/
theorem divRoundRatInt_nonneg (num den : ℤ) (hnum : 0 ≤ num) (hden : 0 < den) :
    0 ≤ divRoundRatInt num den := by
  rw [divRoundRatInt_eq_floor num den hden]
  exact Int.floor_nonneg.mpr (by positivity)

/-- Monotonicity of `divRoundRatInt` in the numerator for `0 < den`. -/
theorem divRoundRatInt_mono_left (num1 num2 den : ℤ) (h : num1 ≤ num2) (hden : 0 < den) :
    divRoundRatInt num1 den ≤ divRoundRatInt num2 den := by
  rw [divRoundRatInt_eq_floor num1 den hden, divRoundRatInt_eq_floor num2 den hden]
  apply Int.floor_mono
  have hden_r : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hnum_r : (num1 : ℝ) ≤ (num2 : ℝ) := by exact_mod_cast h
  linarith [div_le_div_of_nonneg_right hnum_r hden_r.le]

/-- Scaled rational rounding error: for `0 < den` and any scale exponent `B : ℕ`,
`divRoundRatInt (rawNum * 2^B) den / 2^B` is within `(1 / 2) * 2^(-B) ≤ 2^(-B)` of `rawNum / den`. -/
theorem abs_divRoundRatInt_mul_two_pow_div_sub_le (B : ℕ) (rawNum den : ℤ) (hden : 0 < den) :
    |((divRoundRatInt (rawNum * ((2 ^ B : ℕ) : ℤ)) den : ℝ) / (2 : ℝ) ^ B) -
      (rawNum : ℝ) / (den : ℝ)| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hbase := abs_divRoundRatInt_sub_le (rawNum * ((2 ^ B : ℕ) : ℤ)) den hden
  have hcast : ((rawNum * ((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ) / (den : ℝ) =
      ((rawNum : ℝ) / (den : ℝ)) * (2 : ℝ) ^ B := by
    push_cast
    ring
  rw [hcast] at hbase
  have hdiv :
      ((divRoundRatInt (rawNum * ((2 ^ B : ℕ) : ℤ)) den : ℝ) / (2 : ℝ) ^ B) -
        (rawNum : ℝ) / (den : ℝ) =
      ((divRoundRatInt (rawNum * ((2 ^ B : ℕ) : ℤ)) den : ℝ) -
        ((rawNum : ℝ) / (den : ℝ)) * (2 : ℝ) ^ B) / (2 : ℝ) ^ B := by
    field_simp [hpow_pos.ne']
  rw [hdiv, abs_div, abs_of_pos hpow_pos, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hbase hpow_pos.le

/-- Linear exponential upper bound `M^m / m! ≤ e^M ≤ 2^(2 * M)` for all `M, m : ℕ`. -/
theorem pow_div_factorial_le_two_pow_linear (M m : ℕ) :
    (M : ℝ) ^ m / (m.factorial : ℝ) ≤ (2 : ℝ) ^ (2 * M) := by
  have h1 : (M : ℝ) ^ m / (m.factorial : ℝ) ≤ Real.exp (M : ℝ) :=
    Real.pow_div_factorial_le_exp (M : ℝ) (Nat.cast_nonneg M) m
  have hlog2 : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hle : (M : ℝ) ≤ ((2 * M : ℕ) : ℝ) * Real.log 2 := by
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    push_cast
    nlinarith
  have h2 : Real.exp (M : ℝ) ≤ (2 : ℝ) ^ (2 * M) := by
    calc Real.exp (M : ℝ)
        ≤ Real.exp (((2 * M : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hle
      _ = (Real.exp (Real.log 2)) ^ (2 * M) := Real.exp_nat_mul (Real.log 2) (2 * M)
      _ = (2 : ℝ) ^ (2 * M) := by rw [Real.exp_log zero_lt_two]
  exact h1.trans h2

/-- Cumulative product of recurrence step ratios from step `i` to step `k` (`prodStepRatio`). -/
noncomputable def prodStepRatio (stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (i : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    if k < i then 1
    else
      prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k *
        (|(stepNum : ℝ)| * (stepNumFactor k : ℝ) / ((stepDenFactor k : ℝ) * (baseDen : ℝ)))

theorem prodStepRatio_eq_one_of_le (stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (i k : ℕ) (hk : k ≤ i) :
    prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k = 1 := by
  induction k with
  | zero => rfl
  | succ k _ =>
    dsimp [prodStepRatio]
    rw [if_pos (by omega : k < i)]

theorem prodStepRatio_nonneg (stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (i k : ℕ) :
    0 ≤ prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    dsimp [prodStepRatio]
    split_ifs
    · exact zero_le_one
    · exact mul_nonneg ih (div_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

theorem prodStepRatio_le_one_of_step_le_one (stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (i k : ℕ)
    (hstep : ∀ j, |(stepNum : ℝ)| * (stepNumFactor j : ℝ) /
      ((stepDenFactor j : ℝ) * (baseDen : ℝ)) ≤ 1) :
    prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤ 1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    dsimp [prodStepRatio]
    split_ifs
    · exact le_rfl
    · calc prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k *
            (|(stepNum : ℝ)| * (stepNumFactor k : ℝ) / ((stepDenFactor k : ℝ) * (baseDen : ℝ)))
          ≤ 1 * 1 := mul_le_mul ih (hstep k)
            (div_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) zero_le_one
        _ = 1 := mul_one 1

theorem sum_prodStepRatio_mul_add_one_eq (stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k) *
      (|(stepNum : ℝ)| * (stepNumFactor k : ℝ) / ((stepDenFactor k : ℝ) * (baseDen : ℝ))) + 1 =
      ∑ i ∈ Finset.range (k + 2),
        prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i (k + 1) := by
  rw [Finset.sum_range_succ (fun i => prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i (k + 1)) (k + 1),
      prodStepRatio_eq_one_of_le _ _ _ _ (k + 1) (k + 1) le_rfl, Finset.sum_mul]
  refine congrArg (· + 1) (Finset.sum_congr rfl fun i hi => ?_)
  have hik : ¬ (k < i) := by
    have : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    omega
  dsimp [prodStepRatio]
  rw [if_neg hik]

theorem prodStepRatio_le_two_pow_of_linear_step
    (stepNum : ℤ) (baseDen : ℕ) (stepNumFactor stepDenFactor : ℕ → ℕ) (M i k : ℕ)
    (hden : 0 < baseDen)
    (hsf_pos : ∀ j, 0 < stepDenFactor j)
    (hratio : |(stepNum : ℝ)| / (baseDen : ℝ) ≤ (M : ℝ))
    (hfactor : ∀ j, (stepNumFactor j : ℝ) * ((j + 1 : ℕ) : ℝ) ≤ (stepDenFactor j : ℝ)) :
    prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤ (2 : ℝ) ^ (2 * M) := by
  by_cases hik : k ≤ i
  · rw [prodStepRatio_eq_one_of_le _ _ _ _ i k hik]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  · have hden_r : (0 : ℝ) < (baseDen : ℝ) := Nat.cast_pos.mpr hden
    have hk_eq : k = i + (k - i) := (Nat.add_sub_of_le (by omega)).symm
    rw [hk_eq]
    suffices hfact : ∀ m : ℕ,
        prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i (i + m) ≤
          (M : ℝ) ^ m / (m.factorial : ℝ) from
      (hfact (k - i)).trans (pow_div_factorial_le_two_pow_linear M (k - i))
    intro m
    induction m with
    | zero =>
      rw [Nat.add_zero, prodStepRatio_eq_one_of_le _ _ _ _ i i le_rfl]
      simp
    | succ m ih =>
      have hnot_lt : ¬ (i + m < i) := by omega
      have hsucc : i + (m + 1) = (i + m) + 1 := by omega
      rw [hsucc]
      dsimp [prodStepRatio]
      rw [if_neg hnot_lt]
      set j := i + m
      have hsf_j_pos : (0 : ℝ) < (stepDenFactor j : ℝ) := Nat.cast_pos.mpr (hsf_pos j)
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm1_le : ((m + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by dsimp [j]; omega : m + 1 ≤ j + 1)
      have hfac_m : (stepNumFactor j : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ (stepDenFactor j : ℝ) := by
        calc (stepNumFactor j : ℝ) * ((m + 1 : ℕ) : ℝ)
            ≤ (stepNumFactor j : ℝ) * ((j + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hm1_le (Nat.cast_nonneg _)
          _ ≤ (stepDenFactor j : ℝ) := hfactor j
      have hfac_div : (stepNumFactor j : ℝ) / (stepDenFactor j : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) :=
        (div_le_div_iff₀ hsf_j_pos hm1_pos).mpr (by linarith)
      have hstep :
          |(stepNum : ℝ)| * (stepNumFactor j : ℝ) / ((stepDenFactor j : ℝ) * (baseDen : ℝ)) ≤
            (M : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        have hsplit :
            |(stepNum : ℝ)| * (stepNumFactor j : ℝ) / ((stepDenFactor j : ℝ) * (baseDen : ℝ)) =
              (|(stepNum : ℝ)| / (baseDen : ℝ)) * ((stepNumFactor j : ℝ) / (stepDenFactor j : ℝ)) := by
          ring
        rw [hsplit]
        calc (|(stepNum : ℝ)| / (baseDen : ℝ)) * ((stepNumFactor j : ℝ) / (stepDenFactor j : ℝ))
            ≤ (M : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) :=
              mul_le_mul hratio hfac_div (by positivity) (Nat.cast_nonneg M)
          _ = (M : ℝ) / ((m + 1 : ℕ) : ℝ) := mul_one_div (M : ℝ) _
      calc prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i j *
            (|(stepNum : ℝ)| * (stepNumFactor j : ℝ) / ((stepDenFactor j : ℝ) * (baseDen : ℝ)))
          ≤ ((M : ℝ) ^ m / (m.factorial : ℝ)) * ((M : ℝ) / ((m + 1 : ℕ) : ℝ)) :=
            mul_le_mul ih hstep (by positivity) (by positivity)
        _ = (M : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
            rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, mul_comm ((m + 1 : ℕ) : ℝ), div_mul_div_comm]

theorem prodStepRatio_le_two_pow_of_quadratic_step
    (stepNum : ℤ) (baseDen : ℕ) (stepNumFactor stepDenFactor : ℕ → ℕ) (M i k : ℕ)
    (hden : 0 < baseDen)
    (hsf_pos : ∀ j, 0 < stepDenFactor j)
    (hratio : |(stepNum : ℝ)| / (baseDen : ℝ) ≤ (M : ℝ) ^ 2)
    (hfactor : ∀ j, (stepNumFactor j : ℝ) * (((2 * j + 1) * (2 * j + 2) : ℕ) : ℝ) ≤ (stepDenFactor j : ℝ)) :
    prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤ (2 : ℝ) ^ (2 * M) := by
  by_cases hik : k ≤ i
  · rw [prodStepRatio_eq_one_of_le _ _ _ _ i k hik]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  · have hden_r : (0 : ℝ) < (baseDen : ℝ) := Nat.cast_pos.mpr hden
    have hk_eq : k = i + (k - i) := (Nat.add_sub_of_le (by omega)).symm
    rw [hk_eq]
    suffices hfact : ∀ m : ℕ,
        prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i (i + m) ≤
          (M : ℝ) ^ (2 * m) / ((2 * m).factorial : ℝ) from
      (hfact (k - i)).trans (pow_div_factorial_le_two_pow_linear M (2 * (k - i)))
    intro m
    induction m with
    | zero =>
      rw [Nat.add_zero, prodStepRatio_eq_one_of_le _ _ _ _ i i le_rfl]
      simp
    | succ m ih =>
      have hnot_lt : ¬ (i + m < i) := by omega
      have hsucc : i + (m + 1) = (i + m) + 1 := by omega
      rw [hsucc]
      dsimp [prodStepRatio]
      rw [if_neg hnot_lt]
      set j := i + m
      have hsf_j_pos : (0 : ℝ) < (stepDenFactor j : ℝ) := Nat.cast_pos.mpr (hsf_pos j)
      have hm_pos : (0 : ℝ) < (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ) := by positivity
      have hm_le : (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ) ≤ (((2 * j + 1) * (2 * j + 2) : ℕ) : ℝ) := by
        have h1 : 2 * m + 1 ≤ 2 * j + 1 := by dsimp [j]; omega
        have h2 : 2 * m + 2 ≤ 2 * j + 2 := by dsimp [j]; omega
        exact_mod_cast Nat.mul_le_mul h1 h2
      have hfac_m :
          (stepNumFactor j : ℝ) * (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ) ≤ (stepDenFactor j : ℝ) := by
        calc (stepNumFactor j : ℝ) * (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ)
            ≤ (stepNumFactor j : ℝ) * (((2 * j + 1) * (2 * j + 2) : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hm_le (Nat.cast_nonneg _)
          _ ≤ (stepDenFactor j : ℝ) := hfactor j
      have hfac_div :
          (stepNumFactor j : ℝ) / (stepDenFactor j : ℝ) ≤
            1 / (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ) :=
        (div_le_div_iff₀ hsf_j_pos hm_pos).mpr (by linarith)
      have hstep :
          |(stepNum : ℝ)| * (stepNumFactor j : ℝ) / ((stepDenFactor j : ℝ) * (baseDen : ℝ)) ≤
            (M : ℝ) ^ 2 / (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ) := by
        have hsplit :
            |(stepNum : ℝ)| * (stepNumFactor j : ℝ) / ((stepDenFactor j : ℝ) * (baseDen : ℝ)) =
              (|(stepNum : ℝ)| / (baseDen : ℝ)) * ((stepNumFactor j : ℝ) / (stepDenFactor j : ℝ)) := by
          ring
        rw [hsplit]
        calc (|(stepNum : ℝ)| / (baseDen : ℝ)) * ((stepNumFactor j : ℝ) / (stepDenFactor j : ℝ))
            ≤ (M : ℝ) ^ 2 * (1 / (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ)) :=
              mul_le_mul hratio hfac_div (by positivity) (sq_nonneg _)
          _ = (M : ℝ) ^ 2 / (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ) := mul_one_div _ _
      calc prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i j *
            (|(stepNum : ℝ)| * (stepNumFactor j : ℝ) / ((stepDenFactor j : ℝ) * (baseDen : ℝ)))
          ≤ ((M : ℝ) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
              ((M : ℝ) ^ 2 / (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ)) :=
            mul_le_mul ih hstep (by positivity) (by positivity)
        _ = (M : ℝ) ^ (2 * (m + 1)) / ((2 * (m + 1)).factorial : ℝ) := by
            have h2m1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
            have hpow : (M : ℝ) ^ (2 * (m + 1)) = (M : ℝ) ^ (2 * m) * (M : ℝ) ^ 2 := by
              rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
            have hfac : ((2 * (m + 1)).factorial : ℝ) =
                ((2 * m).factorial : ℝ) * (((2 * m + 1) * (2 * m + 2) : ℕ) : ℝ) := by
              rw [h2m1, Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m)]
              push_cast
              ring
            rw [hpow, hfac, div_mul_div_comm]

/-- Unscaled recurrence error bound for `runRecurrenceSeriesCosted`:
bounds `|a_k - exactA k * 2^Bint|` by `(1 / 2) * 2^E0 * ∑_{i ≤ k} prodStepRatio ... i k`. -/
theorem runRecurrenceSeriesCosted_unscaled_bounds
    (Bint E0 w : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (exactA : ℕ → ℝ)
    (hden : 0 < baseDen)
    (hsf_pos : ∀ k, 0 < stepDenFactor k)
    (ha0 : |(a0 : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ E0)
    (hrec : ∀ k, exactA (k + 1) =
      exactA k * ((stepNum : ℝ) * (stepNumFactor k : ℝ)) /
        ((stepDenFactor k : ℝ) * (baseDen : ℝ)))
    (k : ℕ) :
    |((runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℝ) -
      exactA k * (2 : ℝ) ^ Bint| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ E0 *
        ∑ i ∈ Finset.range (k + 1),
          prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k := by
  have hden_r : (0 : ℝ) < (baseDen : ℝ) := Nat.cast_pos.mpr hden
  have h1_le_E0 : (1 : ℝ) ≤ (2 : ℝ) ^ E0 := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  induction k with
  | zero =>
    dsimp only [runRecurrenceSeriesCosted]
    rw [Finset.sum_range_one, prodStepRatio_eq_one_of_le _ _ _ _ 0 0 le_rfl, mul_one]
    exact ha0
  | succ k ih =>
    dsimp only [runRecurrenceSeriesCosted, recurrenceStepCosted, costedDivRoundRatInt, costedMulInt]
    set a_k := (runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1
    set num_k : ℤ := a_k * stepNum * ((stepNumFactor k : ℕ) : ℤ)
    set den_k : ℤ := ((stepDenFactor k : ℕ) : ℤ) * (baseDen : ℤ)
    have hsf_k_pos : (0 : ℝ) < (stepDenFactor k : ℝ) := Nat.cast_pos.mpr (hsf_pos k)
    have hden_k_pos : 0 < den_k :=
      mul_pos (Int.natCast_pos.mpr (hsf_pos k)) (Int.natCast_pos.mpr hden)
    have hround := abs_divRoundRatInt_sub_le num_k den_k hden_k_pos
    have habs_div :
        |((num_k : ℝ) / (den_k : ℝ) - exactA (k + 1) * (2 : ℝ) ^ Bint)| =
          |(a_k : ℝ) - exactA k * (2 : ℝ) ^ Bint| *
            (|(stepNum : ℝ)| * (stepNumFactor k : ℝ) / ((stepDenFactor k : ℝ) * (baseDen : ℝ))) := by
      have hsub :
          (num_k : ℝ) / (den_k : ℝ) - exactA (k + 1) * (2 : ℝ) ^ Bint =
            ((a_k : ℝ) - exactA k * (2 : ℝ) ^ Bint) *
              (((stepNum : ℝ) * (stepNumFactor k : ℝ)) / ((stepDenFactor k : ℝ) * (baseDen : ℝ))) := by
        rw [hrec k]
        dsimp [num_k, den_k]
        push_cast
        ring
      have h_abs_sf : |(stepNumFactor k : ℝ)| = (stepNumFactor k : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [hsub, abs_mul, abs_div,
          abs_mul (stepNum : ℝ) (stepNumFactor k : ℝ), h_abs_sf,
          abs_mul (stepDenFactor k : ℝ) (baseDen : ℝ),
          abs_of_pos hsf_k_pos, abs_of_pos hden_r]
    have hprop :
        |(num_k : ℝ) / (den_k : ℝ) - exactA (k + 1) * (2 : ℝ) ^ Bint| ≤
          ((1 / 2 : ℝ) * (2 : ℝ) ^ E0 *
            ∑ i ∈ Finset.range (k + 1),
              prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k) *
            (|(stepNum : ℝ)| * (stepNumFactor k : ℝ) / ((stepDenFactor k : ℝ) * (baseDen : ℝ))) := by
      rw [habs_div]
      exact mul_le_mul_of_nonneg_right ih (by positivity)
    have htri := abs_add_le
      ((divRoundRatInt num_k den_k : ℝ) - (num_k : ℝ) / (den_k : ℝ))
      ((num_k : ℝ) / (den_k : ℝ) - exactA (k + 1) * (2 : ℝ) ^ Bint)
    rw [sub_add_sub_cancel] at htri
    have hstep := sum_prodStepRatio_mul_add_one_eq stepNum baseDen stepNumFactor stepDenFactor k
    have hstep_scaled :
        ((1 / 2 : ℝ) * (2 : ℝ) ^ E0 *
            ∑ i ∈ Finset.range (k + 1),
              prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k) *
          (|(stepNum : ℝ)| * (stepNumFactor k : ℝ) / ((stepDenFactor k : ℝ) * (baseDen : ℝ))) +
          (1 / 2 : ℝ) * (2 : ℝ) ^ E0 =
        (1 / 2 : ℝ) * (2 : ℝ) ^ E0 *
          ∑ i ∈ Finset.range (k + 2),
            prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i (k + 1) := by
      rw [← hstep]
      ring
    linarith

/-- Universal scaled sum accuracy theorem for `runRecurrenceSeriesCosted`:
if `prodStepRatio ... i k ≤ 2^(2 * M)` for all `i ≤ k`, then the scaled partial sum
`(runRecurrenceSeriesCosted ... N).1.2 / 2^Bint` approximates `∑_{k < N} exactA k`
within `N^2 * 2^E0 * 2^(2 * M) * 2^(-Bint)`. -/
theorem abs_runRecurrenceSeriesCosted_div_sub_sum_le
    (Bint E0 M w : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (exactA : ℕ → ℝ) (N : ℕ)
    (hden : 0 < baseDen)
    (hsf_pos : ∀ k, 0 < stepDenFactor k)
    (ha0 : |(a0 : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ E0)
    (hrec : ∀ k, exactA (k + 1) =
      exactA k * ((stepNum : ℝ) * (stepNumFactor k : ℝ)) /
        ((stepDenFactor k : ℝ) * (baseDen : ℝ)))
    (hprod : ∀ i k, i ≤ k →
      prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤ (2 : ℝ) ^ (2 * M)) :
    |(((runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor N).1.2 : ℝ) /
        (2 : ℝ) ^ Bint) -
      ∑ k ∈ Finset.range N, exactA k| ≤
      (N : ℝ) ^ 2 * (2 : ℝ) ^ E0 * (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ (-(Bint : ℤ)) := by
  rw [runRecurrenceSeriesCosted_fst_snd_eq_sum]
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ Bint := by positivity
  have hunscaled :
      |((∑ k ∈ Finset.range N,
          (runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℤ) : ℝ) -
        (∑ k ∈ Finset.range N, exactA k) * (2 : ℝ) ^ Bint| ≤
      (N : ℝ) ^ 2 * (2 : ℝ) ^ E0 * (2 : ℝ) ^ (2 * M) := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.range N,
          (((runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℝ) -
            exactA k * (2 : ℝ) ^ Bint)|
        ≤ ∑ k ∈ Finset.range N,
            |((runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℝ) -
              exactA k * (2 : ℝ) ^ Bint| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range N, ((N : ℝ) * (2 : ℝ) ^ E0 * (2 : ℝ) ^ (2 * M)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < N := Finset.mem_range.mp hk
          have hak_err := runRecurrenceSeriesCosted_unscaled_bounds Bint E0 0 a0 stepNum baseDen
            stepNumFactor stepDenFactor exactA hden hsf_pos ha0 hrec k
          have hsum_le :
              ∑ i ∈ Finset.range (k + 1),
                prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤
              (N : ℝ) * (2 : ℝ) ^ (2 * M) := by
            calc ∑ i ∈ Finset.range (k + 1),
                  prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k
                ≤ ∑ _i ∈ Finset.range (k + 1), (2 : ℝ) ^ (2 * M) :=
                  Finset.sum_le_sum fun i hi =>
                    hprod i k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
              _ = ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * M) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              _ ≤ (N : ℝ) * (2 : ℝ) ^ (2 * M) :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hk_lt) (by positivity)
          have h1 :
              (1 / 2 : ℝ) * (2 : ℝ) ^ E0 *
                ∑ i ∈ Finset.range (k + 1),
                  prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤
              (1 / 2 : ℝ) * (2 : ℝ) ^ E0 * ((N : ℝ) * (2 : ℝ) ^ (2 * M)) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
          have h2 : (0 : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ E0 * (2 : ℝ) ^ (2 * M) := by positivity
          linarith
      _ = (N : ℝ) ^ 2 * (2 : ℝ) ^ E0 * (2 : ℝ) ^ (2 * M) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hdiv :
      (((∑ k ∈ Finset.range N,
          (runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℤ) : ℝ) /
          (2 : ℝ) ^ Bint) -
        (∑ k ∈ Finset.range N, exactA k) =
      (((∑ k ∈ Finset.range N,
          (runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℤ) : ℝ) -
        (∑ k ∈ Finset.range N, exactA k) * (2 : ℝ) ^ Bint) / (2 : ℝ) ^ Bint := by
    field_simp [hpow_pos.ne']
  rw [hdiv, abs_div, abs_of_pos hpow_pos, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hunscaled hpow_pos.le

/-- Universal recurrence rounding tail bound: when `B + 2 * N + 2 * E0 + 2 * M + 4 ≤ Bint`,
`N^2 * 2^E0 * 2^(2 * M) * 2^(-Bint) ≤ (1 / 8) * 2^(-B)`. -/
theorem recurrence_rounding_error_le_eighth (B N E0 M Bint : ℕ)
    (hBint : B + 2 * N + 2 * E0 + 2 * M + 4 ≤ Bint) :
    (N : ℝ) ^ 2 * (2 : ℝ) ^ E0 * (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ (-(Bint : ℤ)) ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
  have hN_pow : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast Nat.lt_two_pow_self.le
  have hN2_pow : (N : ℝ) ^ 2 ≤ (2 : ℝ) ^ ((2 * N : ℕ) : ℤ) := by
    rw [zpow_natCast, mul_comm 2 N, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hN_pow 2
  calc (N : ℝ) ^ 2 * (2 : ℝ) ^ E0 * (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ (-(Bint : ℤ))
      ≤ (2 : ℝ) ^ ((2 * N : ℕ) : ℤ) * (2 : ℝ) ^ ((E0 : ℕ) : ℤ) *
          (2 : ℝ) ^ ((2 * M : ℕ) : ℤ) * (2 : ℝ) ^ (-(Bint : ℤ)) := by
        rw [zpow_natCast (2 : ℝ) E0, zpow_natCast (2 : ℝ) (2 * M)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hN2_pow (by positivity))
            (by positivity))
          (by positivity)
    _ = (2 : ℝ) ^ (((2 * N : ℕ) : ℤ) + ((E0 : ℕ) : ℤ) + ((2 * M : ℕ) : ℤ) + -(Bint : ℤ)) := by
        simp only [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_assoc]
    _ ≤ (2 : ℝ) ^ ((-3 : ℤ) + -(B : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    _ = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num

/-- Universal width-soundness and sum-magnitude theorem for `runRecurrenceSeriesCosted`:
proves `RecurrenceCallSitesWidthSound` and bounds `|s_N| ≤ 2^(Bint + E0 + 2 * M + 2 * N + 3)`. -/
theorem recurrenceCallSitesWidthSound_of_bounds
    (Bint E0 M D w : ℕ) (a0 stepNum : ℤ) (baseDen : ℕ)
    (stepNumFactor stepDenFactor : ℕ → ℕ) (exactA : ℕ → ℝ) (N : ℕ)
    (hden : 0 < baseDen)
    (hsf_pos : ∀ k, 0 < stepDenFactor k)
    (ha0 : |(a0 : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ E0)
    (hrec : ∀ k, exactA (k + 1) =
      exactA k * ((stepNum : ℝ) * (stepNumFactor k : ℝ)) /
        ((stepDenFactor k : ℝ) * (baseDen : ℝ)))
    (hA_bound : ∀ k, |exactA k| ≤ (2 : ℝ) ^ (2 * M))
    (hprod : ∀ i k, i ≤ k →
      prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤ (2 : ℝ) ^ (2 * M))
    (hstepNum_le : |(stepNum : ℝ)| ≤ (2 : ℝ) ^ D)
    (hbaseDen_le : (baseDen : ℝ) ≤ (2 : ℝ) ^ D)
    (hnumFactor_le : ∀ k < N, (stepNumFactor k : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4))
    (hdenFactor_le : ∀ k < N, (stepDenFactor k : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4))
    (hw : Bint + E0 + 2 * M + 4 * N + D + 9 ≤ w) :
    RecurrenceCallSitesWidthSound w a0 stepNum baseDen stepNumFactor stepDenFactor N ∧
    |((runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor N).1.2 : ℝ)| ≤
      (2 : ℝ) ^ (Bint + E0 + 2 * M + 2 * N + 3) := by
  set E_a := Bint + E0 + 2 * M + N + 2
  have hak_le : ∀ w' : ℕ, ∀ k ≤ N,
      |((runRecurrenceSeriesCosted w' a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℝ)| ≤
        (2 : ℝ) ^ E_a := by
    intro w' k hk
    have herr_k := runRecurrenceSeriesCosted_unscaled_bounds Bint E0 w' a0 stepNum baseDen
      stepNumFactor stepDenFactor exactA hden hsf_pos ha0 hrec k
    have hA_scaled : |exactA k * (2 : ℝ) ^ Bint| ≤ (2 : ℝ) ^ (Bint + E0 + 2 * M) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ Bint)]
      have h1 : (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ Bint = (2 : ℝ) ^ (Bint + 2 * M) := by
        rw [← pow_add]; congr 1; omega
      have h2 : (2 : ℝ) ^ (Bint + 2 * M) ≤ (2 : ℝ) ^ (Bint + E0 + 2 * M) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact (mul_le_mul_of_nonneg_right (hA_bound k) (by positivity)).trans (h1.le.trans h2)
    have hsum_bound :
        (1 / 2 : ℝ) * (2 : ℝ) ^ E0 *
          ∑ i ∈ Finset.range (k + 1),
            prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤
        (2 : ℝ) ^ (Bint + E0 + 2 * M + N + 1) := by
      have hk1_pow : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
        have h1 : k + 1 ≤ N + 1 := Nat.add_le_add_right hk 1
        have h2 : N + 1 ≤ 2 ^ (N + 1) := Nat.lt_two_pow_self.le
        exact_mod_cast h1.trans h2
      have hsum_le :
          ∑ i ∈ Finset.range (k + 1),
            prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤
          (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (2 * M) := by
        calc ∑ i ∈ Finset.range (k + 1),
              prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k
            ≤ ∑ _i ∈ Finset.range (k + 1), (2 : ℝ) ^ (2 * M) :=
              Finset.sum_le_sum fun i hi =>
                hprod i k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
          _ = ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * M) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (2 * M) :=
              mul_le_mul_of_nonneg_right hk1_pow (by positivity)
      have hprod_pow :
          (2 : ℝ) ^ E0 * ((2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (2 * M)) ≤
            (2 : ℝ) ^ (Bint + E0 + 2 * M + N + 1) := by
        rw [← pow_add, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hmul_le :
          (1 / 2 : ℝ) * (2 : ℝ) ^ E0 *
            ∑ i ∈ Finset.range (k + 1),
              prodStepRatio stepNum baseDen stepNumFactor stepDenFactor i k ≤
          (2 : ℝ) ^ E0 * ((2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (2 * M)) := by
        have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ E0 * ((2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (2 * M)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hsum_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ E0)]
      exact hmul_le.trans hprod_pow
    have htri := abs_add_le
      (((runRecurrenceSeriesCosted w' a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1 : ℝ) -
        exactA k * (2 : ℝ) ^ Bint)
      (exactA k * (2 : ℝ) ^ Bint)
    rw [sub_add_cancel] at htri
    have h1 : (2 : ℝ) ^ (Bint + E0 + 2 * M) ≤ (2 : ℝ) ^ (Bint + E0 + 2 * M + N + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : 2 * (2 : ℝ) ^ (Bint + E0 + 2 * M + N + 1) = (2 : ℝ) ^ E_a :=
      (pow_succ' (2 : ℝ) (Bint + E0 + 2 * M + N + 1)).symm
    linarith
  have hsk_le : ∀ k ≤ N,
      |((runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor k).1.2 : ℝ)| ≤
        (2 : ℝ) ^ (Bint + E0 + 2 * M + 2 * N + 3) := by
    intro k hk
    rw [runRecurrenceSeriesCosted_fst_snd_eq_sum]
    push_cast
    calc |∑ j ∈ Finset.range k,
          ((runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor j).1.1 : ℝ)|
        ≤ ∑ j ∈ Finset.range k,
            |((runRecurrenceSeriesCosted 0 a0 stepNum baseDen stepNumFactor stepDenFactor j).1.1 : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range k, (2 : ℝ) ^ E_a :=
          Finset.sum_le_sum fun j hj =>
            hak_le 0 j ((Finset.mem_range.mp hj).le.trans hk)
      _ = (k : ℝ) * (2 : ℝ) ^ E_a := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ N * (2 : ℝ) ^ E_a := by
          have hk_pow : (k : ℝ) ≤ (2 : ℝ) ^ N := by
            have : k ≤ 2 ^ N := hk.trans Nat.lt_two_pow_self.le
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hk_pow (by positivity)
      _ ≤ (2 : ℝ) ^ (Bint + E0 + 2 * M + 2 * N + 3) := by
          dsimp [E_a]
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hbaseDen_abs : |((baseDen : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (w - 2) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hbaseDen_le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine ⟨⟨fitsSignedScalarWord_of_abs_le_two_pow w stepNum
      (hstepNum_le.trans (pow_le_pow_right₀ (by norm_num) (by omega))),
    fitsSignedScalarWord_of_abs_le_two_pow w (baseDen : ℤ) hbaseDen_abs,
    fun k hk => ?_⟩, hsk_le N le_rfl⟩
  dsimp only
  set a_k := (runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor k).1.1
  set s_k := (runRecurrenceSeriesCosted w a0 stepNum baseDen stepNumFactor stepDenFactor k).1.2
  have hnf_abs : |(((stepNumFactor k : ℕ) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (2 * N + 4) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hnumFactor_le k hk
  have hdf_abs : |(((stepDenFactor k : ℕ) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (2 * N + 4) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hdenFactor_le k hk
  have hak_prod1 : |((a_k * stepNum : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (E_a + D) := by
    push_cast
    rw [abs_mul, pow_add]
    exact mul_le_mul (hak_le w k hk.le) hstepNum_le (abs_nonneg _) (by positivity)
  have hak_prod2 :
      |((a_k * stepNum * ((stepNumFactor k : ℕ) : ℤ) : ℤ) : ℝ)| ≤
        (2 : ℝ) ^ (E_a + D + (2 * N + 4)) := by
    rw [Int.cast_mul, abs_mul, pow_add]
    exact mul_le_mul hak_prod1 hnf_abs (abs_nonneg _) (by positivity)
  have hden_prod :
      |((((stepDenFactor k : ℕ) : ℤ) * (baseDen : ℤ) : ℤ) : ℝ)| ≤
        (2 : ℝ) ^ ((2 * N + 4) + D) := by
    push_cast
    rw [abs_of_nonneg (by positivity), pow_add]
    exact mul_le_mul (hdenFactor_le k hk) hbaseDen_le (by positivity) (by positivity)
  exact ⟨fitsSignedScalarWord_of_abs_le_two_pow w a_k
      ((hak_le w k hk.le).trans (pow_le_pow_right₀ (by norm_num) (by dsimp [E_a]; omega))),
    fitsSignedScalarWord_of_abs_le_two_pow w s_k
      ((hsk_le k hk.le).trans (pow_le_pow_right₀ (by norm_num) (by omega))),
    fitsSignedScalarWord_of_abs_le_two_pow w ((stepNumFactor k : ℕ) : ℤ)
      (hnf_abs.trans (pow_le_pow_right₀ (by norm_num) (by omega))),
    fitsSignedScalarWord_of_abs_le_two_pow w ((stepDenFactor k : ℕ) : ℤ)
      (hdf_abs.trans (pow_le_pow_right₀ (by norm_num) (by omega))),
    fitsSignedScalarWord_of_abs_le_two_pow w (a_k * stepNum)
      (hak_prod1.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [E_a]; omega))),
    fitsSignedScalarWord_of_abs_le_two_pow w (a_k * stepNum * ((stepNumFactor k : ℕ) : ℤ))
      (hak_prod2.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [E_a]; omega))),
    fitsSignedScalarWord_of_abs_le_two_pow w (((stepDenFactor k : ℕ) : ℤ) * (baseDen : ℤ))
      (hden_prod.trans (pow_le_pow_right₀ (by norm_num) (by omega)))⟩

/-- Clamping an integer `G` to `[lo, hi]` never increases its distance to any real `x ∈ [lo, hi]`. -/
theorem abs_clampInt_sub_le (lo hi G : ℤ) (x : ℝ)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    |((max lo (min hi G) : ℤ) : ℝ) - x| ≤ |(G : ℝ) - x| := by
  push_cast
  rw [abs_le]
  have h1 : -( |(G : ℝ) - x| ) ≤ (G : ℝ) - x := neg_abs_le _
  have h2 : (G : ℝ) - x ≤ |(G : ℝ) - x| := le_abs_self _
  have hmin1 : min (hi : ℝ) (G : ℝ) ≤ (hi : ℝ) := min_le_left _ _
  have hmin2 : min (hi : ℝ) (G : ℝ) ≤ (G : ℝ) := min_le_right _ _
  constructor
  · rcases le_total (hi : ℝ) (G : ℝ) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]
      linarith
    · rw [min_eq_right h]
      rcases le_total (lo : ℝ) (G : ℝ) with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
  · rcases le_total (hi : ℝ) (G : ℝ) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]
      linarith
    · rw [min_eq_right h]
      rcases le_total (lo : ℝ) (G : ℝ) with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith

/-- Exact bounds on `Nat.sqrt n` cast to `ℝ`:
`(Nat.sqrt n : ℝ) ≤ Real.sqrt n` and `Real.sqrt n ≤ (Nat.sqrt n : ℝ) + 1`. -/
theorem natSqrt_le_realSqrt_and_le_succ (n : ℕ) :
    (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) ∧ Real.sqrt (n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
  have h1 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have h2 : n ≤ (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := (Nat.lt_succ_sqrt n).le
  have h1_r : ((Nat.sqrt n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith [sq (Nat.sqrt n : ℝ)]
  have h2_r : (n : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    have : (n : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) * ((Nat.sqrt n + 1 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith [sq ((Nat.sqrt n : ℝ) + 1)]
  refine ⟨?_, ?_⟩
  · rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt n))]
    exact Real.sqrt_le_sqrt h1_r
  · rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1)]
    exact Real.sqrt_le_sqrt h2_r

/-- For any `a, b ≥ 0`, `|√a - √b| ≤ √|a - b|`. -/
theorem abs_sqrt_sub_sqrt_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  have haux : ∀ u v : ℝ, 0 ≤ v → v ≤ u → Real.sqrt u - Real.sqrt v ≤ Real.sqrt (u - v) := by
    intro u v hv hvu
    have hu : 0 ≤ u := hv.trans hvu
    have hdiff_sqrt : 0 ≤ Real.sqrt u - Real.sqrt v := sub_nonneg.mpr (Real.sqrt_le_sqrt hvu)
    have hprod : 0 ≤ 2 * Real.sqrt v * (Real.sqrt u - Real.sqrt v) :=
      mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg v)) hdiff_sqrt
    have hsq : (Real.sqrt u - Real.sqrt v) ^ 2 ≤ u - v := by
      have h1 : (Real.sqrt u - Real.sqrt v) ^ 2 + 2 * Real.sqrt v * (Real.sqrt u - Real.sqrt v) =
          (Real.sqrt u) ^ 2 - (Real.sqrt v) ^ 2 := by ring
      rw [Real.sq_sqrt hu, Real.sq_sqrt hv] at h1
      linarith
    rw [← Real.sqrt_sq hdiff_sqrt]
    exact Real.sqrt_le_sqrt hsq
  rcases le_total b a with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hba)),
        abs_of_nonneg (sub_nonneg.mpr hba)]
    exact haux a b hb hba
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hab)),
        abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact haux b a ha hab

/-- Contraction property of `x ↦ √(2 + x)` on `[0, ∞)`:
for `0 ≤ a ≤ b`, `0 ≤ √(2 + b) - √(2 + a) ≤ (b - a) / 2`. -/
theorem sqrt_two_add_sub_le_half (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ Real.sqrt (2 + a) ∧
    0 ≤ Real.sqrt (2 + b) - Real.sqrt (2 + a) ∧
    Real.sqrt (2 + b) - Real.sqrt (2 + a) ≤ (b - a) / 2 := by
  have hb : 0 ≤ b := ha.trans hab
  have h1 : 1 ≤ Real.sqrt (2 + a) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : 1 ≤ Real.sqrt (2 + b) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hdiff_nonneg : 0 ≤ Real.sqrt (2 + b) - Real.sqrt (2 + a) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hprod :
      (Real.sqrt (2 + b) - Real.sqrt (2 + a)) * (Real.sqrt (2 + b) + Real.sqrt (2 + a)) =
        b - a := by
    have hsq :
        (Real.sqrt (2 + b) - Real.sqrt (2 + a)) * (Real.sqrt (2 + b) + Real.sqrt (2 + a)) =
          (Real.sqrt (2 + b)) ^ 2 - (Real.sqrt (2 + a)) ^ 2 := by ring
    rw [hsq, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring
  refine ⟨by linarith, hdiff_nonneg, ?_⟩
  nlinarith

/-! ### 2. Computable Fixed-Point Evaluator for `π` (`computablePiScaledWithCost`) -/

/-- Pure-integer Archimedes nested-radical iteration at scale `2^S`:
`A_0 = 0`, `A_{k+1} = Nat.sqrt (2 * 2^(2*S) + A_k * 2^S)`. -/
def sqrtTwoAddIntIter (S : ℕ) : ℕ → BitCostM ℕ
  | 0 => (0, 0)
  | k + 1 =>
    let prev := sqrtTwoAddIntIter S k
    let sqRes := costedNatSqrt (2 * S + 4) (2 * 2 ^ (2 * S) + prev.1 * 2 ^ S)
    (sqRes.1, prev.2 + sqRes.2 + addBitCost (2 * S + 4))

@[simp]
theorem sqrtTwoAddIntIter_snd (S k : ℕ) :
    (sqrtTwoAddIntIter S k).2 =
      k * (2 * computableMulBitCost (2 * S + 4) + 3 * addBitCost (2 * S + 4)) := by
  induction k with
  | zero => simp [sqrtTwoAddIntIter]
  | succ k ih =>
    dsimp only [sqrtTwoAddIntIter, costedNatSqrt]
    rw [ih]
    ring

/-- Inductive accuracy of `sqrtTwoAddIntIter S k`:
for every `k : ℕ`, `0 ≤ sqrtTwoAddSeries 0 k - (sqrtTwoAddIntIter S k).1 / 2^S ≤ 2 * 2^(-S)`. -/
theorem sqrtTwoAddIntIter_bounds (S k : ℕ) :
    ((sqrtTwoAddIntIter S k).1 : ℝ) / (2 : ℝ) ^ S ≤ Real.sqrtTwoAddSeries 0 k ∧
    Real.sqrtTwoAddSeries 0 k - ((sqrtTwoAddIntIter S k).1 : ℝ) / (2 : ℝ) ^ S ≤
      2 * (2 : ℝ) ^ (-(S : ℤ)) := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
  induction k with
  | zero =>
    dsimp [sqrtTwoAddIntIter, Real.sqrtTwoAddSeries]
    refine ⟨by simp, ?_⟩
    simp only [Nat.cast_zero, zero_div, sub_zero]
    positivity
  | succ k ih =>
    dsimp only [sqrtTwoAddIntIter, costedNatSqrt, Real.sqrtTwoAddSeries]
    generalize hAk : (sqrtTwoAddIntIter S k).1 = Ak at ih ⊢
    set M := 2 * 2 ^ (2 * S) + Ak * 2 ^ S
    have hsqrt_M := natSqrt_le_realSqrt_and_le_succ M
    have h2S : (2 : ℝ) ^ (2 * S) = ((2 : ℝ) ^ S) ^ 2 := by
      rw [mul_comm 2 S, pow_mul]
    have hM_eq : (M : ℝ) = (2 + (Ak : ℝ) / (2 : ℝ) ^ S) * ((2 : ℝ) ^ S) ^ 2 := by
      dsimp [M]
      push_cast
      rw [h2S]
      field_simp [hpow_pos.ne']
    have hsqrt_div : Real.sqrt (M : ℝ) / (2 : ℝ) ^ S = Real.sqrt (2 + (Ak : ℝ) / (2 : ℝ) ^ S) := by
      rw [hM_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq hpow_pos.le,
          mul_div_cancel_right₀ _ hpow_pos.ne']
    have hle1 : (Nat.sqrt M : ℝ) / (2 : ℝ) ^ S ≤ Real.sqrt (2 + (Ak : ℝ) / (2 : ℝ) ^ S) := by
      rw [← hsqrt_div]
      exact div_le_div_of_nonneg_right hsqrt_M.1 hpow_pos.le
    have hle2 : Real.sqrt (2 + (Ak : ℝ) / (2 : ℝ) ^ S) - (Nat.sqrt M : ℝ) / (2 : ℝ) ^ S ≤
        (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← hsqrt_div, zpow_neg, zpow_natCast, ← one_div]
      have hsub : Real.sqrt (M : ℝ) / (2 : ℝ) ^ S - (Nat.sqrt M : ℝ) / (2 : ℝ) ^ S =
          (Real.sqrt (M : ℝ) - (Nat.sqrt M : ℝ)) / (2 : ℝ) ^ S := by ring
      rw [hsub]
      exact div_le_div_of_nonneg_right (by linarith [hsqrt_M.2]) hpow_pos.le
    have hcontract := sqrt_two_add_sub_le_half ((Ak : ℝ) / (2 : ℝ) ^ S)
      (Real.sqrtTwoAddSeries 0 k) (by positivity) ih.1
    refine ⟨hle1.trans (by linarith [hcontract.2.1]), ?_⟩
    linarith [hcontract.2.2, ih.2, hle2]

/-- Core fixed-point evaluator for `π` given explicit iteration count `n`, internal scale `S`,
and output scale `B`. -/
def computablePiScaledCore (n S B : ℕ) : BitCostM ℤ :=
  let w := 2 * S + 4
  let aRes := sqrtTwoAddIntIter S n
  let aShiftRes := costedShiftLeftNat w aRes.1 S
  let dRes := costedNatSqrt w (2 * 2 ^ (2 * S) - aShiftRes.1)
  let qNumShiftRes := costedShiftLeftInt w ((2 ^ (n + 1) * dRes.1 : ℕ) : ℤ) B
  let qRes := costedDivRoundRatInt w qNumShiftRes.1 ((2 ^ S : ℕ) : ℤ)
  (qRes.1, aRes.2 + aShiftRes.2 + dRes.2 + qNumShiftRes.2 + qRes.2 + 2 * addBitCost w)

/-- Computable fixed-point evaluator for `π` at scale `2^B`:
uses `n = B + 4` Archimedes nested-radical steps at internal scale `S = 2 * (n + B + 6) = 4 * B + 20`. -/
def computablePiScaledWithCost (B : ℕ) : BitCostM ℤ :=
  let n := B + 4
  let M := n + B + 6
  computablePiScaledCore n (2 * M) B

/-- Accuracy theorem for `computablePiScaledCore`. -/
theorem computablePiScaledCore_error_le (n M S B : ℕ)
    (hn : n = B + 4) (hM : M = n + B + 6) (hS : S = 2 * M) :
    |(((computablePiScaledCore n S B).1 : ℝ) / (2 : ℝ) ^ B) - Real.pi| ≤
      (2 : ℝ) ^ (-(B : ℤ)) ∧
    0 ≤ (computablePiScaledCore n S B).1 := by
  dsimp only [computablePiScaledCore, costedNatSqrt, costedDivRoundRatInt]
  have hbounds := sqrtTwoAddIntIter_bounds S n
  generalize hAn : (sqrtTwoAddIntIter S n).1 = An at hbounds ⊢
  generalize hK_def : 2 * 2 ^ (2 * S) - An * 2 ^ S = K
  generalize hDn_def : Nat.sqrt K = Dn
  have hS_pos : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
  have hB_pos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hB_zpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(B : ℤ)) := by positivity
  obtain ⟨hAn_le, hAn_err⟩ := hbounds
  have hseries_lt2 : Real.sqrtTwoAddSeries 0 n < 2 := Real.sqrtTwoAddSeries_lt_two n
  have h2S : (2 : ℝ) ^ (2 * S) = ((2 : ℝ) ^ S) ^ 2 := by
    rw [mul_comm 2 S, pow_mul]
  have hAn_lt : An * 2 ^ S ≤ 2 * 2 ^ (2 * S) := by
    have h1 : (An : ℝ) ≤ 2 * (2 : ℝ) ^ S := by
      have := (div_le_iff₀ hS_pos).mp (hAn_le.trans hseries_lt2.le)
      linarith
    have h2 : (An : ℝ) * (2 : ℝ) ^ S ≤ 2 * (2 : ℝ) ^ (2 * S) := by
      calc (An : ℝ) * (2 : ℝ) ^ S ≤ (2 * (2 : ℝ) ^ S) * (2 : ℝ) ^ S :=
            mul_le_mul_of_nonneg_right h1 hS_pos.le
        _ = 2 * ((2 : ℝ) ^ S) ^ 2 := by ring
        _ = 2 * (2 : ℝ) ^ (2 * S) := by rw [← h2S]
    exact_mod_cast h2
  have hK_eq : (K : ℝ) = (2 - (An : ℝ) / (2 : ℝ) ^ S) * ((2 : ℝ) ^ S) ^ 2 := by
    rw [← hK_def, Nat.cast_sub hAn_lt]
    push_cast
    rw [h2S]
    field_simp [hS_pos.ne']
  have hsqrt_K := natSqrt_le_realSqrt_and_le_succ K
  rw [hDn_def] at hsqrt_K
  have hsqrt_K_div : Real.sqrt (K : ℝ) / (2 : ℝ) ^ S = Real.sqrt (2 - (An : ℝ) / (2 : ℝ) ^ S) := by
    rw [hK_eq, Real.sqrt_mul (by linarith), Real.sqrt_sq hS_pos.le,
        mul_div_cancel_right₀ _ hS_pos.ne']
  have hDn_err1 :
      |(Dn : ℝ) / (2 : ℝ) ^ S - Real.sqrt (2 - (An : ℝ) / (2 : ℝ) ^ S)| ≤
        (2 : ℝ) ^ (-(S : ℤ)) := by
    rw [← hsqrt_K_div, zpow_neg, zpow_natCast, ← one_div]
    have hsub : (Dn : ℝ) / (2 : ℝ) ^ S - Real.sqrt (K : ℝ) / (2 : ℝ) ^ S =
        ((Dn : ℝ) - Real.sqrt (K : ℝ)) / (2 : ℝ) ^ S := by ring
    rw [hsub, abs_div, abs_of_pos hS_pos]
    refine div_le_div_of_nonneg_right ?_ hS_pos.le
    rw [abs_le]
    constructor <;> linarith [hsqrt_K.1, hsqrt_K.2]
  have hDn_err2 :
      |Real.sqrt (2 - (An : ℝ) / (2 : ℝ) ^ S) - Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n)| ≤
        2 * (2 : ℝ) ^ (-(M : ℤ)) := by
    have h1 := abs_sqrt_sub_sqrt_le (2 - (An : ℝ) / (2 : ℝ) ^ S) (2 - Real.sqrtTwoAddSeries 0 n)
      (by linarith) (by linarith)
    have hdiff : |(2 - (An : ℝ) / (2 : ℝ) ^ S) - (2 - Real.sqrtTwoAddSeries 0 n)| ≤
        2 * (2 : ℝ) ^ (-(S : ℤ)) := by
      have heq : (2 - (An : ℝ) / (2 : ℝ) ^ S) - (2 - Real.sqrtTwoAddSeries 0 n) =
          Real.sqrtTwoAddSeries 0 n - (An : ℝ) / (2 : ℝ) ^ S := by ring
      rw [heq, abs_of_nonneg (by linarith)]
      exact hAn_err
    have hsqrt_bound : Real.sqrt (2 * (2 : ℝ) ^ (-(S : ℤ))) ≤ 2 * (2 : ℝ) ^ (-(M : ℤ)) := by
      have hS_eq : (2 : ℝ) ^ (-(S : ℤ)) = ((2 : ℝ) ^ (-(M : ℤ))) ^ 2 := by
        have h_exp : (-(S : ℤ)) = (-(M : ℤ)) + (-(M : ℤ)) := by omega
        rw [h_exp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), sq]
      rw [hS_eq, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
      have hsqrt2 : Real.sqrt 2 ≤ 2 := by linarith [sqrt_two_lt_1416]
      exact mul_le_mul_of_nonneg_right hsqrt2 (by positivity)
    exact h1.trans ((Real.sqrt_le_sqrt hdiff).trans hsqrt_bound)
  have hS_le_M : (2 : ℝ) ^ (-(S : ℤ)) ≤ (2 : ℝ) ^ (-(M : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hDn_total :
      |(Dn : ℝ) / (2 : ℝ) ^ S - Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n)| ≤
        3 * (2 : ℝ) ^ (-(M : ℤ)) := by
    have htri := abs_add_le ((Dn : ℝ) / (2 : ℝ) ^ S - Real.sqrt (2 - (An : ℝ) / (2 : ℝ) ^ S))
      (Real.sqrt (2 - (An : ℝ) / (2 : ℝ) ^ S) - Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))
    rw [sub_add_sub_cancel] at htri
    linarith
  have hscaled_err :
      |((2 : ℝ) ^ (n + 1) * (Dn : ℝ)) / (2 : ℝ) ^ S -
        (2 : ℝ) ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n)| ≤
      3 * (2 : ℝ) ^ (-(B + 5 : ℤ)) := by
    have heq : ((2 : ℝ) ^ (n + 1) * (Dn : ℝ)) / (2 : ℝ) ^ S -
        (2 : ℝ) ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) =
        (2 : ℝ) ^ (n + 1) * ((Dn : ℝ) / (2 : ℝ) ^ S - Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n)) := by
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    have hexp : ((n + 1 : ℕ) : ℤ) + -(M : ℤ) = -(B + 5 : ℤ) := by omega
    have hpow_eq : (2 : ℝ) ^ (n + 1) * (3 * (2 : ℝ) ^ (-(M : ℤ))) =
        3 * (2 : ℝ) ^ (-(B + 5 : ℤ)) := by
      rw [← zpow_natCast (2 : ℝ) (n + 1), mul_left_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), hexp]
    rw [← hpow_eq]
    exact mul_le_mul_of_nonneg_left hDn_total (by positivity)
  have hpi_gt := Real.pi_gt_sqrtTwoAddSeries n
  have hpi_lt := Real.pi_lt_sqrtTwoAddSeries n
  have h4n_le : 1 / (4 : ℝ) ^ n ≤ (2 : ℝ) ^ (-(B + 4 : ℤ)) := by
    have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
    have hinv : 1 / (4 : ℝ) ^ n = (2 : ℝ) ^ (-((2 * n : ℕ) : ℤ)) := by
      rw [h4, one_div, zpow_neg, zpow_natCast]
    rw [hinv]
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have harch_err :
      |(2 : ℝ) ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) - Real.pi| ≤
        (2 : ℝ) ^ (-(B + 4 : ℤ)) := by
    rw [abs_le]
    constructor <;> linarith
  generalize hNum : ((2 ^ (n + 1) * Dn : ℕ) : ℤ) = numInt
  generalize hDen : ((2 ^ S : ℕ) : ℤ) = denInt
  have hden_pos : 0 < denInt := by subst hDen; positivity
  have hnum_nonneg : 0 ≤ numInt * ((2 ^ B : ℕ) : ℤ) := by subst hNum; positivity
  have hq_err := abs_divRoundRatInt_mul_two_pow_div_sub_le B numInt denInt hden_pos
  have hcast_q :
      (numInt : ℝ) / (denInt : ℝ) =
        ((2 : ℝ) ^ (n + 1) * (Dn : ℝ)) / (2 : ℝ) ^ S := by
    subst hNum hDen
    push_cast
    rfl
  rw [hcast_q] at hq_err
  have hpow5 : (2 : ℝ) ^ (-(B + 5 : ℤ)) = (1 / 32 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have : (-(B + 5 : ℤ)) = (-5 : ℤ) + (-(B : ℤ)) := by omega
    rw [this, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hpow4 : (2 : ℝ) ^ (-(B + 4 : ℤ)) = (1 / 16 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have : (-(B + 4 : ℤ)) = (-4 : ℤ) + (-(B : ℤ)) := by omega
    rw [this, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  refine ⟨?_, divRoundRatInt_nonneg _ _ hnum_nonneg hden_pos⟩
  have htri1 := abs_add_le
    ((divRoundRatInt (numInt * ((2 ^ B : ℕ) : ℤ)) denInt : ℝ) /
      (2 : ℝ) ^ B - ((2 : ℝ) ^ (n + 1) * (Dn : ℝ)) / (2 : ℝ) ^ S)
    (((2 : ℝ) ^ (n + 1) * (Dn : ℝ)) / (2 : ℝ) ^ S - Real.pi)
  have htri2 := abs_add_le
    (((2 : ℝ) ^ (n + 1) * (Dn : ℝ)) / (2 : ℝ) ^ S -
      (2 : ℝ) ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))
    ((2 : ℝ) ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) - Real.pi)
  rw [sub_add_sub_cancel] at htri1 htri2
  linarith

/-- Accuracy theorem for `computablePiScaledWithCost`:
for every `B : ℕ`, `|(computablePiScaledWithCost B).1 / 2^B - π| ≤ 2^(-B)` and
`0 ≤ (computablePiScaledWithCost B).1`. -/
theorem computablePiScaledWithCost_error_le (B : ℕ) :
    |(((computablePiScaledWithCost B).1 : ℝ) / (2 : ℝ) ^ B) - Real.pi| ≤
      (2 : ℝ) ^ (-(B : ℤ)) ∧
    0 ≤ (computablePiScaledWithCost B).1 :=
  computablePiScaledCore_error_le (B + 4) (B + 4 + B + 6) (2 * (B + 4 + B + 6)) B rfl rfl rfl

theorem computablePiScaledWithCost_toNat_le (B : ℕ) :
    (computablePiScaledWithCost B).1.toNat ≤ 2 ^ (B + 2) := by
  obtain ⟨herr, h0⟩ := computablePiScaledWithCost_error_le B
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  rcases Nat.eq_zero_or_pos B with rfl | hB_pos
  · have h1 := (abs_le.mp herr).2
    simp only [pow_zero, div_one, Nat.cast_zero, neg_zero, zpow_zero] at h1
    have hlt : ((computablePiScaledWithCost 0).1 : ℝ) < ((5 : ℤ) : ℝ) := by
      push_cast; linarith
    have hlt_z : (computablePiScaledWithCost 0).1 < 5 := by exact_mod_cast hlt
    omega
  · have hpow_le : (2 : ℝ) ^ (-(B : ℤ)) ≤ 1 / 2 := by
      have : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℤ) := by norm_num
      rw [this]
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hdiv_le : ((computablePiScaledWithCost B).1 : ℝ) / (2 : ℝ) ^ B ≤ 4 := by
      have := (abs_le.mp herr).2
      linarith
    have hpos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
    have hle : ((computablePiScaledWithCost B).1 : ℝ) ≤ (2 : ℝ) ^ (B + 2) := by
      have h1 := (div_le_iff₀ hpos).mp hdiv_le
      have h2 : 4 * (2 : ℝ) ^ B = (2 : ℝ) ^ (B + 2) := by rw [pow_add]; ring
      linarith
    have hcast : ((computablePiScaledWithCost B).1.toNat : ℝ) = ((computablePiScaledWithCost B).1 : ℝ) := by
      have : ((computablePiScaledWithCost B).1.toNat : ℤ) = (computablePiScaledWithCost B).1 :=
        Int.toNat_of_nonneg h0
      exact_mod_cast this
    rw [← hcast] at hle
    exact_mod_cast hle

/-- Per-call-site operand width soundness for `computablePiScaledWithCost B`:
every `costedNatSqrt w` and `costedDivRoundRatInt w` call inside `sqrtTwoAddIntIter` and
`computablePiScaledCore` has operands fitting strictly inside a signed `w`-bit word. -/
def PiScaledWidthSound (B : ℕ) : Prop :=
  let n := B + 4
  let M := n + B + 6
  let S := 2 * M
  let w := 2 * S + 4
  (∀ k < n, FitsSignedScalarWord w ((2 * 2 ^ (2 * S) + (sqrtTwoAddIntIter S k).1 * 2 ^ S : ℕ) : ℤ)) ∧
  FitsSignedScalarWord w ((2 * 2 ^ (2 * S) - (sqrtTwoAddIntIter S n).1 * 2 ^ S : ℕ) : ℤ) ∧
  let dVal := Nat.sqrt (2 * 2 ^ (2 * S) - (sqrtTwoAddIntIter S n).1 * 2 ^ S)
  FitsSignedScalarWord w (((2 ^ (n + 1) * dVal : ℕ) : ℤ) * ((2 ^ B : ℕ) : ℤ)) ∧
  FitsSignedScalarWord w ((2 ^ S : ℕ) : ℤ)

theorem computablePiScaledWithCost_widths_sound (B : ℕ) : PiScaledWidthSound B := by
  dsimp only [PiScaledWidthSound]
  set n := B + 4
  set M := n + B + 6
  set S := 2 * M
  set w := 2 * S + 4
  have hAk_le : ∀ k : ℕ, (sqrtTwoAddIntIter S k).1 ≤ 2 ^ (S + 1) := by
    intro k
    have h1 := (sqrtTwoAddIntIter_bounds S k).1
    have h2 : Real.sqrtTwoAddSeries 0 k < 2 := Real.sqrtTwoAddSeries_lt_two k
    have hpos : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
    have hle : ((sqrtTwoAddIntIter S k).1 : ℝ) ≤ (2 : ℝ) ^ (S + 1) := by
      have := (div_le_iff₀ hpos).mp (h1.trans h2.le)
      rw [pow_succ']
      linarith
    exact_mod_cast hle
  refine ⟨fun k _ => ?_, ?_, ?_,
    fitsSignedScalarWord_of_nat_le_two_pow w (2 ^ S)
      (Nat.pow_le_pow_right zero_lt_two (by dsimp [w, S, M, n]; omega))⟩
  · refine fitsSignedScalarWord_of_nat_le_two_pow w _ ?_
    calc 2 * 2 ^ (2 * S) + (sqrtTwoAddIntIter S k).1 * 2 ^ S
        ≤ 2 * 2 ^ (2 * S) + 2 ^ (S + 1) * 2 ^ S :=
          Nat.add_le_add_left (Nat.mul_le_mul_right (2 ^ S) (hAk_le k)) _
      _ = 2 ^ (2 * S + 2) := by
          have : 2 ^ (S + 1) * 2 ^ S = 2 * 2 ^ (2 * S) := by
            rw [← pow_add, show S + 1 + S = 2 * S + 1 by omega, pow_succ']
          rw [this, show 2 * 2 ^ (2 * S) + 2 * 2 ^ (2 * S) = 2 ^ 2 * 2 ^ (2 * S) by ring,
              ← pow_add, show 2 + 2 * S = 2 * S + 2 by omega]
      _ ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right zero_lt_two (by dsimp [w]; omega)
  · refine fitsSignedScalarWord_of_nat_le_two_pow w _ ?_
    calc 2 * 2 ^ (2 * S) - (sqrtTwoAddIntIter S n).1 * 2 ^ S
        ≤ 2 * 2 ^ (2 * S) := Nat.sub_le _ _
      _ = 2 ^ (2 * S + 1) := (pow_succ' 2 (2 * S)).symm
      _ ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right zero_lt_two (by dsimp [w]; omega)
  · set K := 2 * 2 ^ (2 * S) - (sqrtTwoAddIntIter S n).1 * 2 ^ S
    have hK_le : K ≤ 2 ^ (2 * (S + 1)) := by
      calc K ≤ 2 * 2 ^ (2 * S) := Nat.sub_le _ _
        _ = 2 ^ (2 * S + 1) := (pow_succ' 2 (2 * S)).symm
        _ ≤ 2 ^ (2 * (S + 1)) := Nat.pow_le_pow_right zero_lt_two (by omega)
    have hd_le : Nat.sqrt K ≤ 2 ^ (S + 1) := by
      calc Nat.sqrt K ≤ Nat.sqrt (2 ^ (2 * (S + 1))) := Nat.sqrt_le_sqrt hK_le
        _ = 2 ^ (S + 1) := by rw [mul_comm 2 (S + 1), pow_mul, sq, Nat.sqrt_eq]
    have hprod_le : 2 ^ (n + 1) * Nat.sqrt K * 2 ^ B ≤ 2 ^ (w - 2) := by
      calc 2 ^ (n + 1) * Nat.sqrt K * 2 ^ B
          ≤ 2 ^ (n + 1) * 2 ^ (S + 1) * 2 ^ B :=
            Nat.mul_le_mul_right (2 ^ B) (Nat.mul_le_mul_left (2 ^ (n + 1)) hd_le)
        _ = 2 ^ (n + 1 + (S + 1) + B) := by simp only [← pow_add]
        _ ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right zero_lt_two (by dsimp [w, S, M, n]; omega)
    have hcast : (((2 ^ (n + 1) * Nat.sqrt K : ℕ) : ℤ) * ((2 ^ B : ℕ) : ℤ)) =
        ((2 ^ (n + 1) * Nat.sqrt K * 2 ^ B : ℕ) : ℤ) := by push_cast; rfl
    rw [hcast]
    exact fitsSignedScalarWord_of_nat_le_two_pow w _ hprod_le

/-! ### 3. Computable Fixed-Point Evaluator for `ln 2` (`computableLog2ScaledWithCost`) -/

/-- Computable fixed-point evaluator for `ln 2 = ∑_{k=0}^∞ 1 / ((k + 1) * 2^(k + 1))` at scale `2^B`:
evaluates `N = B + 2` terms by fixed-point recurrence (`runRecurrenceSeriesCosted`) at internal
scale `2^Bint` (`Bint = B + 2 * N + 8`) and rounds to `2^B`. -/
def computableLog2ScaledWithCost (B : ℕ) : BitCostM ℤ :=
  let N := B + 2
  let Bint := B + 2 * N + 8
  let w := Bint + 4 * N + 20
  let a0Res := costedDivRoundRatInt w ((2 ^ Bint : ℕ) : ℤ) 2
  let recRes := runRecurrenceSeriesCosted w a0Res.1 1 2
    (fun k => k + 1) (fun k => k + 2) N
  let qShiftRes := costedShiftLeftInt w recRes.1.2 B
  let qRes := costedDivRoundRatInt w qShiftRes.1 ((2 ^ Bint : ℕ) : ℤ)
  (qRes.1, a0Res.2 + recRes.2 + qShiftRes.2 + qRes.2)

/-- Accuracy theorem for `computableLog2ScaledWithCost`:
for every `B : ℕ`, `|(computableLog2ScaledWithCost B).1 / 2^B - Real.log 2| ≤ 2^(-B)`. -/
theorem computableLog2ScaledWithCost_error_le (B : ℕ) :
    |(((computableLog2ScaledWithCost B).1 : ℝ) / (2 : ℝ) ^ B) - Real.log 2| ≤
      (2 : ℝ) ^ (-(B : ℤ)) := by
  dsimp only [computableLog2ScaledWithCost]
  set N := B + 2 with hN_def
  set Bint := B + 2 * N + 8 with hBint_def
  set w := Bint + 4 * N + 20 with hw_def
  clear_value N Bint w
  set a0 := (costedDivRoundRatInt w ((2 ^ Bint : ℕ) : ℤ) 2).1
  let exactA : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
  have hB_zpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(B : ℤ)) := by positivity
  have ha0 : |(a0 : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 0 := by
    have h1 := abs_divRoundRatInt_sub_div_le ((2 ^ Bint : ℕ) : ℤ) 2 (by decide)
    have hcast : (((2 ^ Bint : ℕ) : ℤ) : ℝ) / ((2 : ℤ) : ℝ) = exactA 0 * (2 : ℝ) ^ Bint := by
      dsimp [exactA]; push_cast; ring
    rw [hcast] at h1
    dsimp [a0, costedDivRoundRatInt]
    simpa using h1
  have hrec_err := abs_runRecurrenceSeriesCosted_div_sub_sum_le Bint 0 1 w
    a0 1 2 (fun k => k + 1) (fun k => k + 2) exactA N
    (by decide) (fun k => Nat.succ_pos (k + 1))
    ha0
    (fun k => by
      dsimp [exactA]
      rw [pow_succ (1 / 2 : ℝ) (k + 1)]
      have hpos1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hpos2 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring)
    (fun i k _ => (prodStepRatio_le_one_of_step_le_one 1 2
      (fun k => k + 1) (fun k => k + 2) i k (fun j => by
        refine (div_le_one (by positivity)).mpr ?_
        push_cast
        rw [abs_one]
        linarith)).trans (by norm_num))
  generalize hSumVal : (runRecurrenceSeriesCosted w a0 1 2
    (fun k => k + 1) (fun k => k + 2) N).1.2 = sumVal at hrec_err ⊢
  have hsum_eq :
      (∑ k ∈ Finset.range N, exactA k) =
        ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [exactA]
    push_cast
    rfl
  rw [hsum_eq] at hrec_err
  have hN_pow := recurrence_rounding_error_le_eighth B N 0 1 Bint (by omega)
  have hlog_tail :
      |(∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) - Real.log 2| ≤
        (2 : ℝ) ^ (-(N : ℤ)) := by
    have h1 := Real.abs_log_sub_add_sum_range_le (x := (1 / 2 : ℝ))
      (by norm_num : |(1 / 2 : ℝ)| < 1) N
    have habs : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
    have hlog : Real.log (1 - (1 / 2 : ℝ)) = -Real.log 2 := by
      have : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
      rw [this, Real.log_inv]
    have hrhs : (1 / 2 : ℝ) ^ (N + 1) / (1 - (1 / 2 : ℝ)) = (2 : ℝ) ^ (-(N : ℤ)) := by
      have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [hsub, pow_succ, mul_div_cancel_right₀ _ (by norm_num), one_div_pow,
          zpow_neg, zpow_natCast, one_div]
    rw [habs, hlog, ← sub_eq_add_neg] at h1
    exact h1.trans_eq hrhs
  generalize hDenInt : ((2 ^ Bint : ℕ) : ℤ) = denInt
  have hden_pos : 0 < denInt := by subst hDenInt; positivity
  have hq_err := abs_divRoundRatInt_mul_two_pow_div_sub_le B sumVal denInt hden_pos
  have hcast_q : ((sumVal : ℝ) / (denInt : ℝ)) =
      (sumVal : ℝ) / (2 : ℝ) ^ Bint := by
    subst hDenInt; push_cast; rfl
  rw [hcast_q] at hq_err
  have htail_pow : (2 : ℝ) ^ (-(N : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have : (-(N : ℤ)) = (-2 : ℤ) + (-(B : ℤ)) := by omega
    rw [this, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  dsimp only [costedDivRoundRatInt]
  have htri1 := abs_add_le
    ((divRoundRatInt (sumVal * ((2 ^ B : ℕ) : ℤ)) denInt : ℝ) / (2 : ℝ) ^ B -
      (sumVal : ℝ) / (2 : ℝ) ^ Bint)
    ((sumVal : ℝ) / (2 : ℝ) ^ Bint - Real.log 2)
  have htri2 := abs_add_le
    ((sumVal : ℝ) / (2 : ℝ) ^ Bint -
      ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1))
    ((∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) - Real.log 2)
  rw [sub_add_sub_cancel] at htri1 htri2
  linarith

/-- Per-call-site operand width soundness for `computableLog2ScaledWithCost B`. -/
def Log2ScaledWidthSound (B : ℕ) : Prop :=
  let N := B + 2
  let Bint := B + 2 * N + 8
  let w := Bint + 4 * N + 20
  let a0Res := costedDivRoundRatInt w ((2 ^ Bint : ℕ) : ℤ) 2
  let recRes := runRecurrenceSeriesCosted w a0Res.1 1 2
    (fun k => k + 1) (fun k => k + 2) N
  FitsSignedScalarWord w ((2 ^ Bint : ℕ) : ℤ) ∧
  FitsSignedScalarWord w 2 ∧
  RecurrenceCallSitesWidthSound w a0Res.1 1 2 (fun k => k + 1) (fun k => k + 2) N ∧
  FitsSignedScalarWord w (recRes.1.2 * ((2 ^ B : ℕ) : ℤ))

theorem computableLog2ScaledWithCost_widths_sound (B : ℕ) : Log2ScaledWidthSound B := by
  dsimp only [Log2ScaledWidthSound]
  set N := B + 2 with hN_def
  set Bint := B + 2 * N + 8 with hBint_def
  set w := Bint + 4 * N + 20 with hw_def
  clear_value N Bint w
  set a0 := (costedDivRoundRatInt w ((2 ^ Bint : ℕ) : ℤ) 2).1
  let exactA : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
  have ha0 : |(a0 : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 0 := by
    have h1 := abs_divRoundRatInt_sub_div_le ((2 ^ Bint : ℕ) : ℤ) 2 (by decide)
    have hcast : (((2 ^ Bint : ℕ) : ℤ) : ℝ) / ((2 : ℤ) : ℝ) = exactA 0 * (2 : ℝ) ^ Bint := by
      dsimp [exactA]; push_cast; ring
    rw [hcast] at h1
    dsimp [a0, costedDivRoundRatInt]
    simpa using h1
  have hrec := recurrenceCallSitesWidthSound_of_bounds Bint 0 1 1 w
    a0 1 2 (fun k => k + 1) (fun k => k + 2) exactA N
    (by decide) (fun k => Nat.succ_pos (k + 1))
    ha0
    (fun k => by
      dsimp [exactA]
      rw [pow_succ (1 / 2 : ℝ) (k + 1)]
      have hpos1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hpos2 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring)
    (fun k => by
      dsimp [exactA]
      rw [abs_of_pos (by positivity)]
      have h1 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h2 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      have h3 : (1 / 2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ≤ 1 :=
        (div_le_one (by positivity)).mpr (h1.trans h2)
      linarith)
    (fun i k _ => (prodStepRatio_le_one_of_step_le_one 1 2
      (fun k => k + 1) (fun k => k + 2) i k (fun j => by
        refine (div_le_one (by positivity)).mpr ?_
        push_cast
        rw [abs_one]
        linarith)).trans (by norm_num))
    (by norm_num) (by norm_num)
    (fun k hk => by
      have h1 : k + 1 ≤ 2 * N + 4 := by omega
      have h2 : 2 * N + 4 ≤ 2 ^ (2 * N + 4) := Nat.lt_two_pow_self.le
      exact_mod_cast h1.trans h2)
    (fun k hk => by
      have h1 : k + 2 ≤ 2 * N + 4 := by omega
      have h2 : 2 * N + 4 ≤ 2 ^ (2 * N + 4) := Nat.lt_two_pow_self.le
      exact_mod_cast h1.trans h2)
    (by omega)
  refine ⟨fitsSignedScalarWord_of_nat_le_two_pow w _ (Nat.pow_le_pow_right zero_lt_two (by omega)),
    fitsSignedScalarWord_of_abs_le_two_pow w 2 (calc
      |((2 : ℤ) : ℝ)| = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)),
    hrec.1, ?_⟩
  refine fitsSignedScalarWord_of_abs_le_two_pow w _ ?_
  push_cast
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B)]
  calc |((runRecurrenceSeriesCosted w a0 1 2 (fun k => k + 1) (fun k => k + 2) N).1.2 : ℝ)| * (2 : ℝ) ^ B
      ≤ (2 : ℝ) ^ (Bint + 0 + 2 * 1 + 2 * N + 3) * (2 : ℝ) ^ B :=
        mul_le_mul_of_nonneg_right hrec.2 (by positivity)
    _ = (2 : ℝ) ^ (Bint + 0 + 2 * 1 + 2 * N + 3 + B) := (pow_add 2 _ B).symm
    _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)

/-! ### 4. Factorial Tail Bounds and FTC Taylor Remainder Bounds (`exp`, `cos`, `sin`, `normSinc`, `erf`) -/

/-- For `2 * M ≤ k`, each additional factorial step multiplies `M^k / k!` by at most `1 / 2`. -/
theorem pow_div_factorial_add_le (M k s : ℕ) (hk : 2 * M ≤ k) :
    (M : ℝ) ^ (k + s) / ((k + s).factorial : ℝ) ≤
      ((M : ℝ) ^ k / (k.factorial : ℝ)) * (1 / 2 : ℝ) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hstep_eq :
        (M : ℝ) ^ (k + (s + 1)) / ((k + (s + 1)).factorial : ℝ) =
          ((M : ℝ) ^ (k + s) / ((k + s).factorial : ℝ)) *
            ((M : ℝ) / ((k + s + 1 : ℕ) : ℝ)) := by
      rw [← add_assoc, pow_succ, Nat.factorial_succ, Nat.cast_mul,
          mul_comm ((k + s + 1 : ℕ) : ℝ), div_mul_div_comm]
    have hratio : (M : ℝ) / ((k + s + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
      have hpos : (0 : ℝ) < ((k + s + 1 : ℕ) : ℝ) := by positivity
      rw [div_le_iff₀ hpos]
      have hle : 2 * M ≤ k + s + 1 := by omega
      have hle_r : 2 * (M : ℝ) ≤ ((k + s + 1 : ℕ) : ℝ) := by exact_mod_cast hle
      linarith
    rw [hstep_eq, pow_succ]
    calc ((M : ℝ) ^ (k + s) / ((k + s).factorial : ℝ)) * ((M : ℝ) / ((k + s + 1 : ℕ) : ℝ))
        ≤ (((M : ℝ) ^ k / (k.factorial : ℝ)) * (1 / 2 : ℝ) ^ s) * (1 / 2 : ℝ) :=
          mul_le_mul ih hratio (by positivity) (by positivity)
      _ = ((M : ℝ) ^ k / (k.factorial : ℝ)) * ((1 / 2 : ℝ) ^ s * (1 / 2 : ℝ)) := by ring

/-- Master linear factorial tail bound: for `0 ≤ x ≤ M` and `N ≥ 4 * M + B`,
`x^N / N! ≤ 2^(-B)`. -/
theorem pow_div_factorial_le_two_zpow_neg (M B N : ℕ)
    (hN : 4 * M + B ≤ N) (x : ℝ) (hx0 : 0 ≤ x) (hxM : x ≤ (M : ℝ)) :
    x ^ N / (N.factorial : ℝ) ≤ (2 : ℝ) ^ (-(B : ℤ)) := by
  have hN_eq : N = 2 * M + (N - 2 * M) := by omega
  have h1 : x ^ N / (N.factorial : ℝ) ≤ (M : ℝ) ^ N / (N.factorial : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hxM N) (by positivity)
  have h2 : (M : ℝ) ^ N / (N.factorial : ℝ) ≤
      ((M : ℝ) ^ (2 * M) / ((2 * M).factorial : ℝ)) * (1 / 2 : ℝ) ^ (N - 2 * M) := by
    conv_lhs => rw [hN_eq]
    exact pow_div_factorial_add_le M (2 * M) (N - 2 * M) le_rfl
  have h3 := pow_div_factorial_le_two_pow_linear M (2 * M)
  have h4 : (1 / 2 : ℝ) ^ (N - 2 * M) ≤ (2 : ℝ) ^ (-((2 * M + B : ℕ) : ℤ)) := by
    rw [one_div_pow, one_div, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h5 : (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ (-((2 * M + B : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [← zpow_natCast (2 : ℝ) (2 * M), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  calc x ^ N / (N.factorial : ℝ)
      ≤ ((M : ℝ) ^ (2 * M) / ((2 * M).factorial : ℝ)) * (1 / 2 : ℝ) ^ (N - 2 * M) :=
        h1.trans h2
    _ ≤ (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ (-((2 * M + B : ℕ) : ℤ)) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (-(B : ℤ)) := h5

/-- Polynomial power Lipschitz bound on `[0, M]` (`1 ≤ M`):
for `0 ≤ a, b ≤ M` and any `m : ℕ`, `|a^m - b^m| ≤ m * M^m * |a - b|`. -/
theorem abs_pow_sub_pow_le_of_le (m : ℕ) (a b M : ℝ) (hM1 : 1 ≤ M)
    (ha0 : 0 ≤ a) (haM : a ≤ M) (hb0 : 0 ≤ b) (hbM : b ≤ M) :
    |a ^ m - b ^ m| ≤ (m : ℝ) * M ^ m * |a - b| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : a ^ (m + 1) - b ^ (m + 1) = (a - b) * a ^ m + b * (a ^ m - b ^ m) := by ring
    have ha_pow : a ^ m ≤ M ^ m := pow_le_pow_left₀ ha0 haM m
    have hM_step : M ^ m ≤ M ^ (m + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (by positivity) hM1
    rw [hsplit]
    have htri := abs_add_le ((a - b) * a ^ m) (b * (a ^ m - b ^ m))
    rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 m), abs_mul, abs_of_nonneg hb0] at htri
    have h1 : |a - b| * a ^ m ≤ M ^ (m + 1) * |a - b| := by
      calc |a - b| * a ^ m ≤ |a - b| * M ^ m := mul_le_mul_of_nonneg_left ha_pow (abs_nonneg _)
        _ ≤ |a - b| * M ^ (m + 1) := mul_le_mul_of_nonneg_left hM_step (abs_nonneg _)
        _ = M ^ (m + 1) * |a - b| := mul_comm _ _
    have h2 : b * |a ^ m - b ^ m| ≤ (m : ℝ) * M ^ (m + 1) * |a - b| := by
      calc b * |a ^ m - b ^ m| ≤ M * ((m : ℝ) * M ^ m * |a - b|) :=
            mul_le_mul hbM ih (abs_nonneg _) (by positivity)
        _ = (m : ℝ) * (M * M ^ m) * |a - b| := by ring
        _ = (m : ℝ) * M ^ (m + 1) * |a - b| := by rw [pow_succ']
    push_cast
    linarith

/-- Derivative of `t^(m + 1) / (m + 1)!` is `t^m / m!`. -/
theorem hasDerivAt_pow_succ_div_factorial (m : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (m + 1) / ((m + 1).factorial : ℝ))
      (t ^ m / (m.factorial : ℝ)) t := by
  have hd := (hasDerivAt_pow (m + 1) t).div_const ((m + 1).factorial : ℝ)
  refine hd.congr_deriv ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hne]

/-- Universal Fundamental-Theorem-of-Calculus remainder bound:
if `f 0 = 0`, `HasDerivAt f (f' t) t`, and `|f' t| ≤ t^m / m!` for `t ≥ 0`, then
`|f x| ≤ x^(m + 1) / (m + 1)!` for all `x ≥ 0`. -/
theorem abs_le_pow_div_factorial_of_hasDerivAt
    (f f' : ℝ → ℝ) (m : ℕ)
    (hf0 : f 0 = 0)
    (hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t)
    (hcont : Continuous f')
    (hbound : ∀ t : ℝ, 0 ≤ t → |f' t| ≤ t ^ m / (m.factorial : ℝ))
    (x : ℝ) (hx : 0 ≤ x) :
    |f x| ≤ x ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  let g : ℝ → ℝ := fun t => t ^ (m + 1) / ((m + 1).factorial : ℝ)
  let g' : ℝ → ℝ := fun t => t ^ m / (m.factorial : ℝ)
  have hcont_g' : Continuous g' := (continuous_pow m).div_const _
  have hint_f' : IntervalIntegrable f' volume 0 x := hcont.intervalIntegrable 0 x
  have hint_g' : IntervalIntegrable g' volume 0 x := hcont_g'.intervalIntegrable 0 x
  have hftc_f : (∫ t in (0 : ℝ)..x, f' t) = f x - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint_f'
  have hftc_g : (∫ t in (0 : ℝ)..x, g' t) = g x - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_pow_succ_div_factorial m t) hint_g'
  have hg0 : g 0 = 0 := by dsimp [g]; simp
  rw [hf0, sub_zero] at hftc_f
  rw [hg0, sub_zero] at hftc_g
  have hle_up : (∫ t in (0 : ℝ)..x, f' t) ≤ ∫ t in (0 : ℝ)..x, g' t :=
    intervalIntegral.integral_mono_on hx hint_f' hint_g' fun t ht =>
      (le_abs_self (f' t)).trans (hbound t ht.1)
  have hle_dn : (∫ t in (0 : ℝ)..x, -g' t) ≤ ∫ t in (0 : ℝ)..x, f' t :=
    intervalIntegral.integral_mono_on hx hint_g'.neg hint_f' fun t ht =>
      neg_le_of_abs_le (hbound t ht.1)
  rw [intervalIntegral.integral_neg, hftc_g, hftc_f] at hle_dn
  rw [hftc_f, hftc_g] at hle_up
  exact abs_le.mpr ⟨hle_dn, hle_up⟩

local notation "expNegTaylorSum" N:arg y:arg =>
  (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * (y : ℝ) ^ k / (Nat.factorial k : ℝ))

local notation "expNegTaylorRem" N:arg y:arg =>
  (Real.exp (-(y : ℝ)) - expNegTaylorSum N y)

theorem expNegTaylorRem_succ (N : ℕ) (y : ℝ) :
    expNegTaylorRem (N + 1) y =
      expNegTaylorRem N y - (-1 : ℝ) ^ N * y ^ N / (N.factorial : ℝ) := by
  rw [Finset.sum_range_succ]
  ring

theorem expNegTaylorRem_succ_zero (N : ℕ) : expNegTaylorRem (N + 1) (0 : ℝ) = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [expNegTaylorRem_succ, ih]
    simp

theorem continuous_expNegTaylorRem (N : ℕ) : Continuous (fun y : ℝ => expNegTaylorRem N y) := by
  refine (Real.continuous_exp.comp continuous_neg).sub ?_
  refine continuous_finset_sum _ fun k _ => ?_
  exact ((continuous_const.mul (continuous_pow k)).div_const _)

theorem hasDerivAt_expNegTaylorRem :
    ∀ (N : ℕ) (t : ℝ), HasDerivAt (fun y : ℝ => expNegTaylorRem (N + 1) y) (-expNegTaylorRem N t) t
  | 0, t => by
    have h1 : (fun x : ℝ => expNegTaylorRem 1 x) = fun x => Real.exp (-x) - 1 := by
      ext x; simp
    rw [h1]
    have hd := ((hasDerivAt_id t).neg.exp).sub_const 1
    refine hd.congr_deriv ?_
    simp
  | N + 1, t => by
    have h1 : (fun x : ℝ => expNegTaylorRem (N + 2) x) =
        fun x => expNegTaylorRem (N + 1) x - (-1 : ℝ) ^ (N + 1) * (x ^ (N + 1) / ((N + 1).factorial : ℝ)) := by
      ext x
      rw [expNegTaylorRem_succ (N + 1) x]
      ring
    rw [h1]
    have hd := (hasDerivAt_expNegTaylorRem N t).sub
      ((hasDerivAt_pow_succ_div_factorial N t).const_mul ((-1 : ℝ) ^ (N + 1)))
    refine hd.congr_deriv ?_
    rw [expNegTaylorRem_succ N t, pow_succ (-1 : ℝ) N]
    ring

/-- Taylor remainder bound for `exp(-y)`: for all `N : ℕ` and `y ≥ 0`,
`|exp(-y) - ∑_{k=0}^{N-1} (-1)^k y^k / k!| ≤ y^N / N!`. -/
theorem abs_expNegTaylorRem_le :
    ∀ (N : ℕ) (y : ℝ), 0 ≤ y → |expNegTaylorRem N y| ≤ y ^ N / (N.factorial : ℝ)
  | 0, y, hy => by
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  | N + 1, y, hy =>
    abs_le_pow_div_factorial_of_hasDerivAt
      (fun x => expNegTaylorRem (N + 1) x) (fun t => -expNegTaylorRem N t) N
      (expNegTaylorRem_succ_zero N)
      (hasDerivAt_expNegTaylorRem N)
      (continuous_expNegTaylorRem N).neg
      (fun t ht => by rw [abs_neg]; exact abs_expNegTaylorRem_le N t ht)
      y hy

/-- `exp(-y)` is `1`-Lipschitz on `[0, ∞)`: for `0 ≤ a` and `0 ≤ b`, `|exp(-a) - exp(-b)| ≤ |a - b|`. -/
theorem abs_exp_neg_sub_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have haux : ∀ u v : ℝ, 0 ≤ u → u ≤ v → Real.exp (-u) - Real.exp (-v) ≤ v - u := by
    intro u v hu huv
    have h1 := Real.add_one_le_exp (-(v - u))
    have hexp_u_le1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp_u_pos : 0 < Real.exp (-u) := Real.exp_pos (-u)
    have hmul := mul_le_mul_of_nonneg_left h1 hexp_u_pos.le
    have hprod : Real.exp (-u) * Real.exp (-(v - u)) = Real.exp (-v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hprod] at hmul
    nlinarith
  rcases le_total a b with hab | hba
  · have hge : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hge), abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact haux a b ha hab
  · have hge : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hge), abs_of_nonneg (sub_nonneg.mpr hba)]
    exact haux b a hb hba

local notation "cosTaylorSum" N:arg θ:arg =>
  (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * (θ : ℝ) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))

local notation "sinTaylorSum" N:arg θ:arg =>
  (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * (θ : ℝ) ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))

local notation "cosTaylorRem" N:arg θ:arg =>
  (Real.cos (θ : ℝ) - cosTaylorSum N θ)

local notation "sinTaylorRem" N:arg θ:arg =>
  (Real.sin (θ : ℝ) - sinTaylorSum N θ)

theorem cosTaylorRem_succ (N : ℕ) (θ : ℝ) :
    cosTaylorRem (N + 1) θ =
      cosTaylorRem N θ - (-1 : ℝ) ^ N * θ ^ (2 * N) / ((2 * N).factorial : ℝ) := by
  rw [Finset.sum_range_succ]
  ring

theorem sinTaylorRem_succ (N : ℕ) (θ : ℝ) :
    sinTaylorRem (N + 1) θ =
      sinTaylorRem N θ - (-1 : ℝ) ^ N * θ ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) := by
  rw [Finset.sum_range_succ]
  ring

theorem sinTaylorRem_zero_arg (N : ℕ) : sinTaylorRem N (0 : ℝ) = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sinTaylorRem_succ, ih]
    simp

theorem cosTaylorRem_succ_zero (N : ℕ) : cosTaylorRem (N + 1) (0 : ℝ) = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [cosTaylorRem_succ, ih]
    simp

theorem continuous_cosTaylorRem (N : ℕ) : Continuous (fun θ : ℝ => cosTaylorRem N θ) := by
  refine Real.continuous_cos.sub ?_
  refine continuous_finset_sum _ fun k _ => ?_
  exact ((continuous_const.mul (continuous_pow (2 * k))).div_const _)

theorem continuous_sinTaylorRem (N : ℕ) : Continuous (fun θ : ℝ => sinTaylorRem N θ) := by
  refine Real.continuous_sin.sub ?_
  refine continuous_finset_sum _ fun k _ => ?_
  exact ((continuous_const.mul (continuous_pow (2 * k + 1))).div_const _)

theorem hasDerivAt_sinTaylorRem :
    ∀ (N : ℕ) (t : ℝ), HasDerivAt (fun θ : ℝ => sinTaylorRem N θ) (cosTaylorRem N t) t
  | 0, t => by
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    exact Real.hasDerivAt_sin t
  | N + 1, t => by
    have h1 : (fun x : ℝ => sinTaylorRem (N + 1) x) =
        fun x => sinTaylorRem N x - (-1 : ℝ) ^ N * (x ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ)) := by
      ext x
      rw [sinTaylorRem_succ N x]
      ring
    rw [h1]
    have hd := (hasDerivAt_sinTaylorRem N t).sub
      ((hasDerivAt_pow_succ_div_factorial (2 * N) t).const_mul ((-1 : ℝ) ^ N))
    refine hd.congr_deriv ?_
    rw [cosTaylorRem_succ N t]
    ring

theorem hasDerivAt_cosTaylorRem :
    ∀ (N : ℕ) (t : ℝ), HasDerivAt (fun θ : ℝ => cosTaylorRem (N + 1) θ) (-sinTaylorRem N t) t
  | 0, t => by
    have h1 : (fun x : ℝ => cosTaylorRem 1 x) = fun x => Real.cos x - 1 := by
      ext x; simp
    rw [h1]
    have hd := (Real.hasDerivAt_cos t).sub_const 1
    refine hd.congr_deriv ?_
    simp
  | N + 1, t => by
    have h1 : (fun x : ℝ => cosTaylorRem (N + 2) x) =
        fun x => cosTaylorRem (N + 1) x - (-1 : ℝ) ^ (N + 1) * (x ^ (2 * N + 2) / ((2 * N + 2).factorial : ℝ)) := by
      ext x
      rw [cosTaylorRem_succ (N + 1) x]
      ring
    rw [h1]
    have hd := (hasDerivAt_cosTaylorRem N t).sub
      ((hasDerivAt_pow_succ_div_factorial (2 * N + 1) t).const_mul ((-1 : ℝ) ^ (N + 1)))
    refine hd.congr_deriv ?_
    rw [sinTaylorRem_succ N t, pow_succ (-1 : ℝ) N]
    ring

/-- Simultaneous Taylor remainder bounds for `cos θ` and `sin θ` on `θ ≥ 0`. -/
theorem abs_cosTaylorRem_and_sinTaylorRem_le :
    ∀ (N : ℕ),
      (∀ θ : ℝ, 0 ≤ θ → |cosTaylorRem N θ| ≤ θ ^ (2 * N) / ((2 * N).factorial : ℝ)) ∧
      (∀ θ : ℝ, 0 ≤ θ → |sinTaylorRem N θ| ≤ θ ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ))
  | 0 => by
    have hcos : ∀ θ : ℝ, 0 ≤ θ → |cosTaylorRem 0 θ| ≤ θ ^ 0 / ((0 : ℕ).factorial : ℝ) := by
      intro θ _
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one]
      exact Real.abs_cos_le_one θ
    refine ⟨hcos, fun θ hθ => ?_⟩
    exact abs_le_pow_div_factorial_of_hasDerivAt
      (fun x => sinTaylorRem 0 x) (fun x => cosTaylorRem 0 x) 0
      (sinTaylorRem_zero_arg 0)
      (hasDerivAt_sinTaylorRem 0)
      (continuous_cosTaylorRem 0)
      hcos θ hθ
  | N + 1 => by
    obtain ⟨_, hsin_prev⟩ := abs_cosTaylorRem_and_sinTaylorRem_le N
    have hcos_next : ∀ θ : ℝ, 0 ≤ θ →
        |cosTaylorRem (N + 1) θ| ≤ θ ^ (2 * (N + 1)) / ((2 * (N + 1)).factorial : ℝ) := by
      intro θ hθ
      have h := abs_le_pow_div_factorial_of_hasDerivAt
        (fun x => cosTaylorRem (N + 1) x) (fun t => -sinTaylorRem N t) (2 * N + 1)
        (cosTaylorRem_succ_zero N)
        (hasDerivAt_cosTaylorRem N)
        (continuous_sinTaylorRem N).neg
        (fun t ht => by rw [abs_neg]; exact hsin_prev t ht)
        θ hθ
      have heq : 2 * N + 1 + 1 = 2 * (N + 1) := by omega
      rwa [heq] at h
    refine ⟨hcos_next, fun θ hθ => ?_⟩
    exact abs_le_pow_div_factorial_of_hasDerivAt
      (fun x => sinTaylorRem (N + 1) x) (fun x => cosTaylorRem (N + 1) x) (2 * (N + 1))
      (sinTaylorRem_zero_arg (N + 1))
      (hasDerivAt_sinTaylorRem (N + 1))
      (continuous_cosTaylorRem (N + 1))
      hcos_next θ hθ

local notation "sincTaylorSum" N:arg θ:arg =>
  (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * (θ : ℝ) ^ (2 * k) / (Nat.factorial (2 * k + 1) : ℝ))

theorem mul_sincTaylorSum_eq_sinTaylorSum (N : ℕ) (θ : ℝ) :
    θ * sincTaylorSum N θ = sinTaylorSum N θ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ]
  ring

/-- Taylor remainder bound for `normSinc t` (`θ = π * |t|`):
for all `N ≥ 1` and all `t : ℝ`,
`|normSinc t - sincTaylorSum N (π * |t|)| ≤ (π * |t|) ^ (2 * N) / (2 * N)!`. -/
theorem abs_normSinc_sub_sincTaylorSum_le (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    |normSinc t - sincTaylorSum N (Real.pi * |t|)| ≤
      (Real.pi * |t|) ^ (2 * N) / ((2 * N).factorial : ℝ) := by
  by_cases ht : t = 0
  · subst ht
    have hN_eq : N = 1 + (N - 1) := by omega
    rw [normSinc_zero, abs_zero, mul_zero]
    have hsum0 : sincTaylorSum N (0 : ℝ) = 1 := by
      rw [hN_eq, Finset.sum_range_add, Finset.sum_range_one]
      simp only [mul_zero, pow_zero, mul_one, Nat.zero_add, Nat.factorial_one, Nat.cast_one,
        div_one]
      have hrest : ∑ x ∈ Finset.range (N - 1),
          (-1 : ℝ) ^ (1 + x) * (0 : ℝ) ^ (2 * (1 + x)) / ((2 * (1 + x) + 1).factorial : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        have hpos : 2 * (1 + x) ≠ 0 := by omega
        rw [zero_pow hpos, mul_zero, zero_div]
      rw [hrest, add_zero]
    rw [hsum0, sub_self, abs_zero]
    positivity
  · set θ := Real.pi * |t|
    have hθ_pos : 0 < θ := mul_pos Real.pi_pos (abs_pos.mpr ht)
    have hnorm_eq : normSinc t = Real.sin θ / θ := by
      have heven : normSinc t = normSinc |t| := by
        rcases le_or_gt 0 t with h0 | h0
        · rw [abs_of_nonneg h0]
        · rw [abs_of_neg h0, normSinc_even]
      rw [heven]
      unfold normSinc
      rw [if_neg (abs_ne_zero.mpr ht)]
    rw [hnorm_eq]
    have hsub : Real.sin θ / θ - sincTaylorSum N θ = (sinTaylorRem N θ) / θ := by
      rw [← mul_sincTaylorSum_eq_sinTaylorSum N θ]
      field_simp [hθ_pos.ne']
    rw [hsub, abs_div, abs_of_pos hθ_pos]
    have hsin_rem := (abs_cosTaylorRem_and_sinTaylorRem_le N).2 θ hθ_pos.le
    have hdiv_le : |sinTaylorRem N θ| / θ ≤ θ ^ (2 * N) / ((2 * N + 1).factorial : ℝ) := by
      calc |sinTaylorRem N θ| / θ
          ≤ (θ ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ)) / θ :=
            div_le_div_of_nonneg_right hsin_rem hθ_pos.le
        _ = θ ^ (2 * N) / ((2 * N + 1).factorial : ℝ) := by
            rw [pow_succ, mul_div_right_comm, mul_div_cancel_right₀ _ hθ_pos.ne']
    have hfact_le : ((2 * N).factorial : ℝ) ≤ ((2 * N + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    exact hdiv_le.trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hfact_le)

/-- Perturbation bound for `sincTaylorSum N`:
for `0 ≤ a, b ≤ M` (`1 ≤ M`),
`|sincTaylorSum N a - sincTaylorSum N b| ≤ N * 2^(2 * M) * |a - b|`. -/
theorem abs_sincTaylorSum_sub_le (N M : ℕ) (hM : 1 ≤ M) (a b : ℝ)
    (ha0 : 0 ≤ a) (haM : a ≤ (M : ℝ)) (hb0 : 0 ≤ b) (hbM : b ≤ (M : ℝ)) :
    |sincTaylorSum N a - sincTaylorSum N b| ≤
      (N : ℝ) * (2 : ℝ) ^ (2 * M) * |a - b| := by
  rw [← Finset.sum_sub_distrib]
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  calc |∑ k ∈ Finset.range N,
        ((-1 : ℝ) ^ k * a ^ (2 * k) / ((2 * k + 1).factorial : ℝ) -
          (-1 : ℝ) ^ k * b ^ (2 * k) / ((2 * k + 1).factorial : ℝ))|
      ≤ ∑ k ∈ Finset.range N,
          |(-1 : ℝ) ^ k * a ^ (2 * k) / ((2 * k + 1).factorial : ℝ) -
            (-1 : ℝ) ^ k * b ^ (2 * k) / ((2 * k + 1).factorial : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, ((2 : ℝ) ^ (2 * M) * |a - b|) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hterm : (-1 : ℝ) ^ k * a ^ (2 * k) / ((2 * k + 1).factorial : ℝ) -
            (-1 : ℝ) ^ k * b ^ (2 * k) / ((2 * k + 1).factorial : ℝ) =
            (-1 : ℝ) ^ k * ((a ^ (2 * k) - b ^ (2 * k)) / ((2 * k + 1).factorial : ℝ)) := by
          ring
        rw [hterm, abs_mul, abs_neg_one_pow, one_mul, abs_div,
            abs_of_pos (by positivity : (0 : ℝ) < ((2 * k + 1).factorial : ℝ))]
        have hpow_diff := abs_pow_sub_pow_le_of_le (2 * k) a b (M : ℝ) hM1 ha0 haM hb0 hbM
        have hfact_eq : ((2 * k + 1).factorial : ℝ) = ((2 * k + 1 : ℕ) : ℝ) * ((2 * k).factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; rfl
        have h2k_le : ((2 * k : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (2 * k)
        have hcoeff :
            ((2 * k : ℕ) : ℝ) * (M : ℝ) ^ (2 * k) / ((2 * k + 1).factorial : ℝ) ≤
              (2 : ℝ) ^ (2 * M) := by
          calc ((2 * k : ℕ) : ℝ) * (M : ℝ) ^ (2 * k) / ((2 * k + 1).factorial : ℝ)
              ≤ ((2 * k + 1 : ℕ) : ℝ) * (M : ℝ) ^ (2 * k) /
                  (((2 * k + 1 : ℕ) : ℝ) * ((2 * k).factorial : ℝ)) := by
                rw [← hfact_eq]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right h2k_le (by positivity)) (by positivity)
            _ = (M : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) :=
                mul_div_mul_left _ _ (by positivity)
            _ ≤ (2 : ℝ) ^ (2 * M) := pow_div_factorial_le_two_pow_linear M (2 * k)
        calc |a ^ (2 * k) - b ^ (2 * k)| / ((2 * k + 1).factorial : ℝ)
            ≤ (((2 * k : ℕ) : ℝ) * (M : ℝ) ^ (2 * k) * |a - b|) / ((2 * k + 1).factorial : ℝ) :=
              div_le_div_of_nonneg_right hpow_diff (by positivity)
          _ = (((2 * k : ℕ) : ℝ) * (M : ℝ) ^ (2 * k) / ((2 * k + 1).factorial : ℝ)) * |a - b| :=
              div_mul_eq_mul_div _ _ _ |>.symm
          _ ≤ (2 : ℝ) ^ (2 * M) * |a - b| :=
              mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
    _ = (N : ℝ) * (2 : ℝ) ^ (2 * M) * |a - b| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

local notation "erfIntegralTaylorSum" N:arg z:arg =>
  (∑ k ∈ Finset.range N,
    (-1 : ℝ) ^ k * (z : ℝ) ^ (2 * k + 1) / ((Nat.factorial k : ℝ) * (2 * (k : ℝ) + 1)))

theorem hasDerivAt_erfIntegralTaylorSum (N : ℕ) (t : ℝ) :
    HasDerivAt (fun z : ℝ => erfIntegralTaylorSum N z) (expNegTaylorSum N (t ^ 2)) t := by
  have hd : HasDerivAt
      (fun z : ℝ => ∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * z ^ (2 * k + 1) / ((k.factorial : ℝ) * (2 * (k : ℝ) + 1)))
      (∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * (((2 * k + 1 : ℕ) : ℝ) * t ^ (2 * k)) /
          ((k.factorial : ℝ) * (2 * (k : ℝ) + 1))) t := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := ((hasDerivAt_pow (2 * k + 1) t).const_mul ((-1 : ℝ) ^ k)).div_const
      ((k.factorial : ℝ) * (2 * (k : ℝ) + 1))
    simpa [Nat.add_sub_cancel] using h1
  refine hd.congr_deriv ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcast : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; rfl
  have hne : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hpow : (t ^ 2) ^ k = t ^ (2 * k) := (pow_mul t 2 k).symm
  rw [hcast, hpow]
  field_simp [hne]

/-- Taylor remainder bound for `∫_0^z exp(-t^2) dt`:
for all `N : ℕ` and `z ≥ 0`,
`|(∫ t in 0..z, exp(-t^2)) - erfIntegralTaylorSum N z| ≤ z * (z^2)^N / N!`. -/
theorem abs_erfIntegral_sub_taylorSum_le (N : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))) - erfIntegralTaylorSum N z| ≤
      z * (z ^ 2) ^ N / (N.factorial : ℝ) := by
  have hcont_exp : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Real.continuous_exp.comp (continuous_pow 2).neg
  have hcont_poly : Continuous (fun t : ℝ => expNegTaylorSum N (t ^ 2)) := by
    refine continuous_finset_sum _ fun k _ => ?_
    exact ((continuous_const.mul ((continuous_pow 2).pow k)).div_const _)
  have hftc : (∫ t in (0 : ℝ)..z, expNegTaylorSum N (t ^ 2)) =
      erfIntegralTaylorSum N z - erfIntegralTaylorSum N (0 : ℝ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_erfIntegralTaylorSum N t) (hcont_poly.intervalIntegrable 0 z)
  have h0 : erfIntegralTaylorSum N (0 : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    simp
  rw [h0, sub_zero] at hftc
  rw [← hftc, ← intervalIntegral.integral_sub (hcont_exp.intervalIntegrable 0 z)
        (hcont_poly.intervalIntegrable 0 z)]
  let B : ℝ := (z ^ 2) ^ N / (N.factorial : ℝ)
  have hcont_diff : Continuous (fun t : ℝ => Real.exp (-(t ^ 2)) - expNegTaylorSum N (t ^ 2)) :=
    hcont_exp.sub hcont_poly
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) z,
      |Real.exp (-(t ^ 2)) - expNegTaylorSum N (t ^ 2)| ≤ B := by
    intro t ht
    have hrem := abs_expNegTaylorRem_le N (t ^ 2) (sq_nonneg t)
    have ht_sq : t ^ 2 ≤ z ^ 2 := sq_le_sq.mpr (by rw [abs_of_nonneg ht.1, abs_of_nonneg hz]; exact ht.2)
    exact hrem.trans (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (sq_nonneg t) ht_sq N) (by positivity))
  have hle_up : (∫ t in (0 : ℝ)..z, (Real.exp (-(t ^ 2)) - expNegTaylorSum N (t ^ 2))) ≤
      ∫ _t in (0 : ℝ)..z, B :=
    intervalIntegral.integral_mono_on hz (hcont_diff.intervalIntegrable 0 z)
      intervalIntegrable_const fun t ht => (le_abs_self _).trans (hbound t ht)
  have hle_dn : (∫ _t in (0 : ℝ)..z, -B) ≤
      ∫ t in (0 : ℝ)..z, (Real.exp (-(t ^ 2)) - expNegTaylorSum N (t ^ 2)) :=
    intervalIntegral.integral_mono_on hz intervalIntegrable_const
      (hcont_diff.intervalIntegrable 0 z) fun t ht => neg_le_of_abs_le (hbound t ht)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle_up hle_dn
  have hB_eq : z * B = z * (z ^ 2) ^ N / (N.factorial : ℝ) := by dsimp [B]; ring
  have hB_neg : z * (-B) = -(z * (z ^ 2) ^ N / (N.factorial : ℝ)) := by dsimp [B]; ring
  rw [hB_eq] at hle_up
  rw [hB_neg] at hle_dn
  exact abs_le.mpr ⟨hle_dn, hle_up⟩

/-- `∫_0^z exp(-t^2) dt` is `1`-Lipschitz on `[0, ∞)`:
for `0 ≤ a` and `0 ≤ b`, `|(∫ t in 0..a, exp(-t^2)) - (∫ t in 0..b, exp(-t^2))| ≤ |a - b|`. -/
theorem abs_erfIntegral_sub_le (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    |(∫ t in (0 : ℝ)..a, Real.exp (-(t ^ 2))) - (∫ t in (0 : ℝ)..b, Real.exp (-(t ^ 2)))| ≤
      |a - b| := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
    Real.continuous_exp.comp (continuous_pow 2).neg
  have haux : ∀ u v : ℝ, u ≤ v →
      0 ≤ (∫ t in (0 : ℝ)..v, Real.exp (-(t ^ 2))) - (∫ t in (0 : ℝ)..u, Real.exp (-(t ^ 2))) ∧
      (∫ t in (0 : ℝ)..v, Real.exp (-(t ^ 2))) - (∫ t in (0 : ℝ)..u, Real.exp (-(t ^ 2))) ≤ v - u := by
    intro u v huv
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont.intervalIntegrable 0 u) (hcont.intervalIntegrable u v)
    have hsub : (∫ t in (0 : ℝ)..v, Real.exp (-(t ^ 2))) - (∫ t in (0 : ℝ)..u, Real.exp (-(t ^ 2))) =
        ∫ t in u..v, Real.exp (-(t ^ 2)) := by linarith
    rw [hsub]
    have hnonneg : 0 ≤ ∫ t in u..v, Real.exp (-(t ^ 2)) :=
      intervalIntegral.integral_nonneg huv fun t _ => (Real.exp_pos _).le
    have hle1 : (∫ t in u..v, Real.exp (-(t ^ 2))) ≤ ∫ _t in u..v, (1 : ℝ) :=
      intervalIntegral.integral_mono_on huv (hcont.intervalIntegrable u v)
        intervalIntegrable_const
        fun t _ => Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hle1
    exact ⟨hnonneg, hle1⟩
  rcases le_total a b with hab | hba
  · obtain ⟨h0, h1⟩ := haux a b hab
    rw [abs_sub_comm, abs_of_nonneg h0, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact h1
  · obtain ⟨h0, h1⟩ := haux b a hba
    rw [abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr hba)]
    exact h1

/-- `Real.sin` is `1`-Lipschitz on `ℝ`: `|Real.sin a - Real.sin b| ≤ |a - b|`. -/
theorem abs_sin_sub_le (a b : ℝ) : |Real.sin a - Real.sin b| ≤ |a - b| := by
  have haux : ∀ u v : ℝ, u ≤ v → |Real.sin v - Real.sin u| ≤ v - u := by
    intro u v huv
    have hint : IntervalIntegrable Real.cos volume u v := Real.continuous_cos.intervalIntegrable u v
    have hftc : (∫ t in u..v, Real.cos t) = Real.sin v - Real.sin u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => Real.hasDerivAt_sin t) hint
    have hup : (∫ t in u..v, Real.cos t) ≤ ∫ _t in u..v, (1 : ℝ) :=
      intervalIntegral.integral_mono_on huv hint intervalIntegrable_const
        fun t _ => (le_abs_self _).trans (Real.abs_cos_le_one t)
    have hdn : (∫ _t in u..v, (-1 : ℝ)) ≤ ∫ t in u..v, Real.cos t :=
      intervalIntegral.integral_mono_on huv intervalIntegrable_const hint
        fun t _ => neg_le_of_abs_le (Real.abs_cos_le_one t)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, mul_neg] at hup hdn
    rw [hftc] at hup hdn
    exact abs_le.mpr ⟨hdn, hup⟩
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact haux a b hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact haux b a hba

/-- `Real.cos` is `1`-Lipschitz on `ℝ`: `|Real.cos a - Real.cos b| ≤ |a - b|`. -/
theorem abs_cos_sub_le (a b : ℝ) : |Real.cos a - Real.cos b| ≤ |a - b| := by
  have haux : ∀ u v : ℝ, u ≤ v → |Real.cos v - Real.cos u| ≤ v - u := by
    intro u v huv
    have hint : IntervalIntegrable (fun t => -Real.sin t) volume u v :=
      Real.continuous_sin.neg.intervalIntegrable u v
    have hftc : (∫ t in u..v, -Real.sin t) = Real.cos v - Real.cos u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => Real.hasDerivAt_cos t) hint
    have hup : (∫ t in u..v, -Real.sin t) ≤ ∫ _t in u..v, (1 : ℝ) :=
      intervalIntegral.integral_mono_on huv hint intervalIntegrable_const
        fun t _ => (le_abs_self _).trans (by rw [abs_neg]; exact Real.abs_sin_le_one t)
    have hdn : (∫ _t in u..v, (-1 : ℝ)) ≤ ∫ t in u..v, -Real.sin t :=
      intervalIntegral.integral_mono_on huv intervalIntegrable_const hint
        fun t _ => neg_le_of_abs_le (by rw [abs_neg]; exact Real.abs_sin_le_one t)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, mul_neg] at hup hdn
    rw [hftc] at hup hdn
    exact abs_le.mpr ⟨hdn, hup⟩
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact haux a b hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact haux b a hba

/-- Reusable series-rounding error bound: when `B + N + 3 ≤ Bint`,
`N * 2^(-Bint) ≤ (1 / 8) * 2^(-B)`. -/
theorem nat_mul_two_zpow_neg_le_eighth (B N Bint : ℕ) (hBint : B + N + 3 ≤ Bint) :
    (N : ℝ) * (2 : ℝ) ^ (-(Bint : ℤ)) ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
  have hlt : N ≤ 2 ^ N := Nat.lt_two_pow_self.le
  have hlt_r : (N : ℝ) ≤ (2 : ℝ) ^ ((N : ℕ) : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast hlt
  calc (N : ℝ) * (2 : ℝ) ^ (-(Bint : ℤ))
      ≤ (2 : ℝ) ^ ((N : ℕ) : ℤ) * (2 : ℝ) ^ (-(Bint : ℤ)) :=
        mul_le_mul_of_nonneg_right hlt_r (by positivity)
    _ = (2 : ℝ) ^ (((N : ℕ) : ℤ) + -(Bint : ℤ)) :=
        (zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _).symm
    _ ≤ (2 : ℝ) ^ ((-3 : ℤ) + -(B : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    _ = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num

/-- Four-stage triangle inequality combining output rounding (`1/2`), per-term series rounding (`1/8`),
Taylor truncation (`1/8`), and argument perturbation (`1/8`) into `7/8 * δ ≤ δ`. -/
theorem abs_sub_le_of_four_step_approx (a b c d e δ : ℝ) (hδ : 0 ≤ δ)
    (h1 : |a - b| ≤ (1 / 2 : ℝ) * δ)
    (h2 : |b - c| ≤ (1 / 8 : ℝ) * δ)
    (h3 : |c - d| ≤ (1 / 8 : ℝ) * δ)
    (h4 : |d - e| ≤ (1 / 8 : ℝ) * δ) :
    |a - e| ≤ δ := by
  have ht1 := abs_add_le (a - b) (b - e)
  have ht2 := abs_add_le (b - c) (c - e)
  have ht3 := abs_add_le (c - d) (d - e)
  rw [sub_add_sub_cancel] at ht1 ht2 ht3
  linarith

/-! ### 5. Cost Helper Lemmas and Computable Evaluator for `stdChar (± num / den)` -/

/-- Cubic polynomial upper bound `computableMulBitCost w ≤ (w + 1) ^ 3` for all `w : ℕ`. -/
theorem computableMulBitCost_le_cube (w : ℕ) :
    computableMulBitCost w ≤ (w + 1) ^ 3 := by
  rw [computableMulBitCost_eq]
  unfold mulBitCost
  have hlog1 : Nat.log2 w ≤ w :=
    (nat_log2_mono (Nat.le_succ w)).trans (log2_add_one_le_self w)
  have hlog2 : Nat.log2 (Nat.log2 w + 1) ≤ Nat.log2 w :=
    log2_add_one_le_self (Nat.log2 w)
  have h1 : w ≤ w + 1 := Nat.le_succ w
  have h2 : Nat.log2 w + 1 ≤ w + 1 := Nat.add_le_add_right hlog1 1
  have h3 : Nat.log2 (Nat.log2 w + 1) + 1 ≤ w + 1 := Nat.add_le_add_right (hlog2.trans hlog1) 1
  calc w * (Nat.log2 w + 1) * (Nat.log2 (Nat.log2 w + 1) + 1)
      ≤ (w + 1) * (w + 1) * (w + 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    _ = (w + 1) ^ 3 := by ring

theorem addBitCost_le_cube (w : ℕ) :
    addBitCost w ≤ (w + 1) ^ 3 := by
  unfold addBitCost
  exact (Nat.le_succ w).trans (Nat.le_self_pow (by decide : 3 ≠ 0) (w + 1))

/-- Polynomial upper bound on `(computablePiScaledWithCost B).2`. -/
theorem computablePiScaledWithCost_snd_le (B : ℕ) :
    (computablePiScaledWithCost B).2 ≤ (B + 7) * 5 * (8 * B + 85) ^ 3 := by
  dsimp only [computablePiScaledWithCost, computablePiScaledCore,
    costedShiftLeftNat, costedShiftLeftInt, costedNatSqrt, costedDivRoundRatInt]
  set n := B + 4
  set M := n + B + 6
  set S := 2 * M
  set w := 2 * S + 4
  rw [sqrtTwoAddIntIter_snd S n]
  have hw_le : w + 1 ≤ 8 * B + 85 := by dsimp [w, S, M, n]; omega
  have hmul : computableMulBitCost w ≤ (8 * B + 85) ^ 3 :=
    (computableMulBitCost_le_cube w).trans (Nat.pow_le_pow_left hw_le 3)
  have hadd : addBitCost w ≤ (8 * B + 85) ^ 3 :=
    (addBitCost_le_cube w).trans (Nat.pow_le_pow_left hw_le 3)
  have hn_eq : n + 3 = B + 7 := rfl
  have hstep :
      n * (2 * computableMulBitCost w + 3 * addBitCost w) +
        addBitCost w +
        (2 * computableMulBitCost w + 2 * addBitCost w) +
        addBitCost w +
        (2 * computableMulBitCost w + 2 * addBitCost w) + 2 * addBitCost w ≤
      (n + 3) * (2 * computableMulBitCost w + 3 * addBitCost w) := by
    nlinarith
  calc n * (2 * computableMulBitCost w + 3 * addBitCost w) +
        addBitCost w +
        (2 * computableMulBitCost w + 2 * addBitCost w) +
        addBitCost w +
        (2 * computableMulBitCost w + 2 * addBitCost w) + 2 * addBitCost w
      ≤ (n + 3) * (2 * computableMulBitCost w + 3 * addBitCost w) := hstep
    _ = (B + 7) * (2 * computableMulBitCost w + 3 * addBitCost w) := by rw [hn_eq]
    _ ≤ (B + 7) * (2 * (8 * B + 85) ^ 3 + 3 * (8 * B + 85) ^ 3) :=
        Nat.mul_le_mul_left _ (by linarith)
    _ = (B + 7) * 5 * (8 * B + 85) ^ 3 := by ring

/-- Upper bound `d ≤ 2 ^ (Nat.log2 d + 1)` valid for all `d : ℕ` (including `d = 0`). -/
theorem nat_le_two_pow_log2_add_one (d : ℕ) : d ≤ 2 ^ (Nat.log2 d + 1) :=
  (lt_two_pow_log2_succ d).le

/-- Uniform power-of-two bounds on recurrence step multipliers and denominators for `k < N`. -/
theorem step_quad_le_two_pow (N k : ℕ) (hk : k < N) :
    (k + 1 : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4) ∧
    (2 * k + 1 : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4) ∧
    (2 * k + 3 : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4) ∧
    (((2 * k + 1) * (2 * k + 2) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4) ∧
    (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4) ∧
    (((k + 1) * (2 * k + 3) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * N + 4) := by
  have hN : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
  have hk1 : 2 * k + 3 ≤ 2 * (N + 1) := by omega
  have h2N : 2 * (N + 1) ≤ 2 ^ (N + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left 2 hN
  have hle : 2 * k + 3 ≤ 2 ^ (N + 1) := hk1.trans h2N
  have hlek : k + 1 ≤ 2 ^ (N + 1) := (by omega : k + 1 ≤ 2 * k + 3).trans hle
  have hle1 : 2 * k + 1 ≤ 2 ^ (N + 1) := (by omega : 2 * k + 1 ≤ 2 * k + 3).trans hle
  have hle2 : 2 * k + 2 ≤ 2 ^ (N + 1) := (by omega : 2 * k + 2 ≤ 2 * k + 3).trans hle
  have hpow_le : 2 ^ (N + 1) ≤ 2 ^ (2 * N + 4) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hmul_eq : 2 ^ (N + 1) * 2 ^ (N + 1) = 2 ^ (2 * N + 2) := by
    rw [← pow_add]; congr 1; omega
  have hpow22_le : 2 ^ (2 * N + 2) ≤ 2 ^ (2 * N + 4) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hq1 : (2 * k + 1) * (2 * k + 2) ≤ 2 ^ (2 * N + 4) :=
    (Nat.mul_le_mul hle1 hle2).trans (hmul_eq.le.trans hpow22_le)
  have hq2 : (2 * k + 2) * (2 * k + 3) ≤ 2 ^ (2 * N + 4) :=
    (Nat.mul_le_mul hle2 hle).trans (hmul_eq.le.trans hpow22_le)
  have hq3 : (k + 1) * (2 * k + 3) ≤ 2 ^ (2 * N + 4) :=
    (Nat.mul_le_mul hlek hle).trans (hmul_eq.le.trans hpow22_le)
  have h0k : k + 1 ≤ 2 ^ (2 * N + 4) := hlek.trans hpow_le
  have h01 : 2 * k + 1 ≤ 2 ^ (2 * N + 4) := hle1.trans hpow_le
  have h03 : 2 * k + 3 ≤ 2 ^ (2 * N + 4) := hle.trans hpow_le
  exact ⟨by exact_mod_cast h0k, by exact_mod_cast h01, by exact_mod_cast h03,
    by exact_mod_cast hq1, by exact_mod_cast hq2, by exact_mod_cast hq3⟩

/-- Polynomial upper bound on `(computableLog2ScaledWithCost B).2`. -/
theorem computableLog2ScaledWithCost_snd_le (B : ℕ) :
    (computableLog2ScaledWithCost B).2 ≤ (B + 4) * 9 * (7 * B + 45) ^ 3 := by
  dsimp only [computableLog2ScaledWithCost, costedShiftLeftInt, costedDivRoundRatInt]
  set N := B + 2 with hN_def
  set Bint := B + 2 * N + 8 with hBint_def
  set w := Bint + 4 * N + 20 with hw_def
  clear_value N Bint w
  rw [runRecurrenceSeriesCosted_snd]
  have hw_le : w + 1 ≤ 7 * B + 45 := by omega
  have hmul : computableMulBitCost w ≤ (7 * B + 45) ^ 3 :=
    (computableMulBitCost_le_cube w).trans (Nat.pow_le_pow_left hw_le 3)
  have hadd : addBitCost w ≤ (7 * B + 45) ^ 3 :=
    (addBitCost_le_cube w).trans (Nat.pow_le_pow_left hw_le 3)
  have hN_eq : N + 2 = B + 4 := by omega
  have hstep :
      (2 * computableMulBitCost w + 2 * addBitCost w) +
        (N * (6 * computableMulBitCost w + 3 * addBitCost w)) +
        addBitCost w +
        (2 * computableMulBitCost w + 2 * addBitCost w) ≤
      (N + 2) * (6 * computableMulBitCost w + 3 * addBitCost w) := by
    nlinarith
  calc (2 * computableMulBitCost w + 2 * addBitCost w) +
        (N * (6 * computableMulBitCost w + 3 * addBitCost w)) +
        addBitCost w +
        (2 * computableMulBitCost w + 2 * addBitCost w)
      ≤ (N + 2) * (6 * computableMulBitCost w + 3 * addBitCost w) := hstep
    _ = (B + 4) * (6 * computableMulBitCost w + 3 * addBitCost w) := by rw [hN_eq]
    _ ≤ (B + 4) * (6 * (7 * B + 45) ^ 3 + 3 * (7 * B + 45) ^ 3) :=
        Nat.mul_le_mul_left _ (by linarith)
    _ = (B + 4) * 9 * (7 * B + 45) ^ 3 := by ring

/-- Combined accuracy, call-site width soundness, and sum-magnitude bound for the
recurrence-based cosine Taylor series evaluator. -/
theorem cos_recurrence_spec_and_widths
    (Bint M D w N numTheta denTheta : ℕ)
    (hden : 0 < denTheta)
    (hθ_le : (numTheta : ℝ) / (denTheta : ℝ) ≤ (M : ℝ))
    (hnum_sq : ((numTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hden_sq : ((denTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hw : Bint + 2 * M + 4 * N + D + 9 ≤ w) :
    let seriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
      (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N
    |(seriesRes.1.2 : ℝ) / (2 : ℝ) ^ Bint - cosTaylorSum N ((numTheta : ℝ) / (denTheta : ℝ))| ≤
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ (-(Bint : ℤ)) ∧
    RecurrenceCallSitesWidthSound w ((2 ^ Bint : ℕ) : ℤ)
      (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N ∧
    |(seriesRes.1.2 : ℝ)| ≤ (2 : ℝ) ^ (Bint + 2 * M + 2 * N + 3) := by
  intro seriesRes
  set θ_hat : ℝ := (numTheta : ℝ) / (denTheta : ℝ)
  have hθ_nonneg : 0 ≤ θ_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set exactA : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * θ_hat ^ (2 * k) / ((2 * k).factorial : ℝ)
  have hden_sq_pos : 0 < denTheta ^ 2 := pow_pos hden 2
  have hsf_pos : ∀ k, 0 < (2 * k + 1) * (2 * k + 2) := fun k => by positivity
  have ha0 : |(((2 ^ Bint : ℕ) : ℤ) : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 0 := by
    dsimp [exactA]
    push_cast
    norm_num
  have hrec : ∀ k, exactA (k + 1) =
      exactA k * (((-((numTheta ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) * ((1 : ℕ) : ℝ)) /
        ((((2 * k + 1) * (2 * k + 2) : ℕ) : ℝ) * ((denTheta ^ 2 : ℕ) : ℝ)) := by
    intro k
    dsimp [exactA, θ_hat]
    have hfact : ((2 * (k + 1)).factorial : ℝ) =
        (((2 * k + 1) * (2 * k + 2) : ℕ) : ℝ) * ((2 * k).factorial : ℝ) := by
      have h2k : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [h2k, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hpow : θ_hat ^ (2 * (k + 1)) = θ_hat ^ (2 * k) * ((numTheta : ℝ) ^ 2 / (denTheta : ℝ) ^ 2) := by
      have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h2k, pow_add, div_pow (numTheta : ℝ) (denTheta : ℝ) 2]
    have hden_ne : (denTheta : ℝ) ≠ 0 := (Nat.cast_pos.mpr hden).ne'
    have hfact_ne : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
    have hsf_ne : (((2 * k + 1) * (2 * k + 2) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [pow_succ (-1 : ℝ), hpow, hfact]
    push_cast
    field_simp [hden_ne, hfact_ne, hsf_ne]
    ring
  have hA_bound : ∀ k, |exactA k| ≤ (2 : ℝ) ^ (2 * M) := by
    intro k
    dsimp [exactA]
    rw [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (pow_nonneg hθ_nonneg _),
        abs_of_pos (by positivity)]
    exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ_nonneg hθ_le _) (by positivity)).trans
      (pow_div_factorial_le_two_pow_linear M (2 * k))
  have hprod_bound : ∀ i k, i ≤ k →
      prodStepRatio (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
        (fun _ => 1) (fun j => (2 * j + 1) * (2 * j + 2)) i k ≤ (2 : ℝ) ^ (2 * M) := by
    intro i k hik
    refine prodStepRatio_le_two_pow_of_quadratic_step _ _ _ _ M i k hden_sq_pos hsf_pos ?_ ?_
    · rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      rw [← div_pow]
      exact pow_le_pow_left₀ hθ_nonneg hθ_le 2
    · intro j
      push_cast
      nlinarith
  have herr := abs_runRecurrenceSeriesCosted_div_sub_sum_le Bint 0 M w
    ((2 ^ Bint : ℕ) : ℤ) (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hprod_bound
  rw [pow_zero, mul_one] at herr
  have hw_sound := recurrenceCallSitesWidthSound_of_bounds Bint 0 M D w
    ((2 ^ Bint : ℕ) : ℤ) (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hA_bound hprod_bound
    (by rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; exact hnum_sq)
    hden_sq
    (fun k hk => by rw [Nat.cast_one]; exact one_le_pow₀ (by norm_num))
    (fun k hk => (step_quad_le_two_pow N k hk).2.2.2.1)
    (by omega)
  exact ⟨herr, hw_sound.1, hw_sound.2⟩

/-- Combined accuracy, call-site width soundness, and sum-magnitude bound for the
recurrence-based sine Taylor series evaluator. -/
theorem sin_recurrence_spec_and_widths
    (Bint M D w N numTheta denTheta : ℕ)
    (hden : 0 < denTheta)
    (hθ_le : (numTheta : ℝ) / (denTheta : ℝ) ≤ (M : ℝ))
    (hnum_sq : ((numTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hden_sq : ((denTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hw : Bint + 2 * M + 4 * N + D + 9 ≤ w) :
    let a0 := divRoundRatInt ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denTheta : ℤ)
    let seriesRes := runRecurrenceSeriesCosted w a0
      (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N
    |(seriesRes.1.2 : ℝ) / (2 : ℝ) ^ Bint - sinTaylorSum N ((numTheta : ℝ) / (denTheta : ℝ))| ≤
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (2 * M) * (2 : ℝ) ^ (-(Bint : ℤ)) ∧
    RecurrenceCallSitesWidthSound w a0
      (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N ∧
    |(seriesRes.1.2 : ℝ)| ≤ (2 : ℝ) ^ (Bint + 2 * M + 2 * N + 3) := by
  intro a0 seriesRes
  set θ_hat : ℝ := (numTheta : ℝ) / (denTheta : ℝ)
  have hθ_nonneg : 0 ≤ θ_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set exactA : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * θ_hat ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
  have hden_sq_pos : 0 < denTheta ^ 2 := pow_pos hden 2
  have hsf_pos : ∀ k, 0 < (2 * k + 2) * (2 * k + 3) := fun k => by positivity
  have ha0 : |(a0 : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 0 := by
    have hq := abs_divRoundRatInt_sub_div_le ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denTheta : ℤ)
      (by exact_mod_cast hden)
    have heq : (((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ) : ℤ) : ℝ) / ((denTheta : ℤ) : ℝ) =
        exactA 0 * (2 : ℝ) ^ Bint := by
      dsimp [exactA, θ_hat]
      push_cast
      ring
    rw [heq] at hq
    simpa [a0] using hq
  have hrec : ∀ k, exactA (k + 1) =
      exactA k * (((-((numTheta ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) * ((1 : ℕ) : ℝ)) /
        ((((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) * ((denTheta ^ 2 : ℕ) : ℝ)) := by
    intro k
    dsimp [exactA, θ_hat]
    have hfact : ((2 * (k + 1) + 1).factorial : ℝ) =
        (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) * ((2 * k + 1).factorial : ℝ) := by
      have h2k : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by omega
      rw [h2k, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hpow : θ_hat ^ (2 * (k + 1) + 1) =
        θ_hat ^ (2 * k + 1) * ((numTheta : ℝ) ^ 2 / (denTheta : ℝ) ^ 2) := by
      have h2k : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [h2k, pow_add, div_pow (numTheta : ℝ) (denTheta : ℝ) 2]
    have hden_ne : (denTheta : ℝ) ≠ 0 := (Nat.cast_pos.mpr hden).ne'
    have hfact_ne : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
    have hsf_ne : (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [pow_succ (-1 : ℝ), hpow, hfact]
    push_cast
    field_simp [hden_ne, hfact_ne, hsf_ne]
    ring
  have hA_bound : ∀ k, |exactA k| ≤ (2 : ℝ) ^ (2 * M) := by
    intro k
    dsimp [exactA]
    rw [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (pow_nonneg hθ_nonneg _),
        abs_of_pos (by positivity)]
    exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ_nonneg hθ_le _) (by positivity)).trans
      (pow_div_factorial_le_two_pow_linear M (2 * k + 1))
  have hprod_bound : ∀ i k, i ≤ k →
      prodStepRatio (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
        (fun _ => 1) (fun j => (2 * j + 2) * (2 * j + 3)) i k ≤ (2 : ℝ) ^ (2 * M) := by
    intro i k hik
    refine prodStepRatio_le_two_pow_of_quadratic_step _ _ _ _ M i k hden_sq_pos hsf_pos ?_ ?_
    · rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      rw [← div_pow]
      exact pow_le_pow_left₀ hθ_nonneg hθ_le 2
    · intro j
      push_cast
      nlinarith
  have herr := abs_runRecurrenceSeriesCosted_div_sub_sum_le Bint 0 M w
    a0 (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hprod_bound
  rw [pow_zero, mul_one] at herr
  have hw_sound := recurrenceCallSitesWidthSound_of_bounds Bint 0 M D w
    a0 (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hA_bound hprod_bound
    (by rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; exact hnum_sq)
    hden_sq
    (fun k hk => by rw [Nat.cast_one]; exact one_le_pow₀ (by norm_num))
    (fun k hk => (step_quad_le_two_pow N k hk).2.2.2.2.1)
    (by omega)
  exact ⟨herr, hw_sound.1, hw_sound.2⟩

/-- Core computable fixed-point evaluator for `stdChar ((if neg then -num else num) / den)`
parameterized by explicit precision/truncation parameters `(B B_pi N Bint w : ℕ)`.
All multi-precision multiplications (precomputing `numTheta`, `numTheta^2`, `denTheta^2`,
and running the cosine/sine term recurrences) go through `costedMulInt w` and `costedDivRoundRatInt w`. -/
def computableStdCharCore (B B_pi N Bint w num den : ℕ) (neg : Bool) : BitCostM (ℤ × ℤ) :=
  let piRes := computablePiScaledWithCost B_pi
  let piNat := piRes.1.toNat
  let numThetaRes := costedMulInt w ((2 * piNat : ℕ) : ℤ) (num : ℤ)
  let numTheta : ℕ := numThetaRes.1.toNat
  let denThetaRes := costedShiftLeftNat w den B_pi
  let denTheta : ℕ := denThetaRes.1
  let numThetaSqRes := costedMulInt w (numTheta : ℤ) (numTheta : ℤ)
  let negNumThetaSqRes := costedNegInt0 numThetaSqRes.1
  let negNumThetaSq : ℤ := negNumThetaSqRes.1
  let denThetaSqRes := costedMulInt w (denTheta : ℤ) (denTheta : ℤ)
  let denThetaSq : ℕ := denThetaSqRes.1.toNat
  let cosSeriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N
  let cosShiftRes := costedShiftLeftInt w cosSeriesRes.1.2 B
  let reRes := costedDivRoundRatInt w
    cosShiftRes.1
    ((2 ^ Bint : ℕ) : ℤ)
  let sinA0ShiftRes := costedShiftLeftInt w (numTheta : ℤ) Bint
  let sinA0Res := costedDivRoundRatInt w
    sinA0ShiftRes.1
    (denTheta : ℤ)
  let sinSeriesRes := runRecurrenceSeriesCosted w sinA0Res.1
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N
  let sinShiftRes := costedShiftLeftInt w sinSeriesRes.1.2 B
  let imPosRes := costedDivRoundRatInt w
    sinShiftRes.1
    ((2 ^ Bint : ℕ) : ℤ)
  let imIntRes := costedCondNegInt0 neg imPosRes.1
  let imInt : ℤ := imIntRes.1
  ((reRes.1, imInt),
    piRes.2 + numThetaRes.2 + denThetaRes.2 + numThetaSqRes.2 + denThetaSqRes.2 +
    cosSeriesRes.2 + cosShiftRes.2 + reRes.2 +
    sinA0ShiftRes.2 + sinA0Res.2 + sinSeriesRes.2 + sinShiftRes.2 + imPosRes.2 + 2 * addBitCost w)

/-- Computable fixed-point evaluator for `stdChar ((if neg then -num else num) / den)`
on the `toScaledComplex q` grid (`2^(q + 2)`). -/
def computableStdCharWithProgramCost (q num den : ℕ) (neg : Bool) : BitCostM (ℤ × ℤ) :=
  let B := q + 2
  let B_pi := B + 4
  let N := B + 25
  let Bint := B + 2 * N + 22
  let w := Bint + 4 * N + 2 * B_pi + 2 * Nat.log2 den + 40
  computableStdCharCore B B_pi N Bint w num den neg

/-- Helper bounding `‖toScaledComplex q (reInt, if neg then -imPosInt else imPosInt) - stdChar x‖`
from separate coordinate bounds on `Real.cos θ` and `Real.sin θ`. -/
theorem norm_toScaledComplex_sub_stdChar_le (q : ℕ) (reInt imPosInt : ℤ) (neg : Bool) (x θ : ℝ)
    (hx : 2 * Real.pi * x = if neg then -θ else θ)
    (hre : |(reInt : ℝ) / (2 : ℝ) ^ (q + 2) - Real.cos θ| ≤ (2 : ℝ) ^ (-(q + 2 : ℤ)))
    (him : |(imPosInt : ℝ) / (2 : ℝ) ^ (q + 2) - Real.sin θ| ≤ (2 : ℝ) ^ (-(q + 2 : ℤ))) :
    ‖toScaledComplex q (reInt, if neg then -imPosInt else imPosInt) - stdChar x‖ ≤
      2 * complexQuantizeMaxErr q := by
  have hnorm :
      ‖toScaledComplex q (reInt, if neg then -imPosInt else imPosInt) - stdChar x‖ =
        Real.sqrt
          ((toScaledComplex q (reInt, if neg then -imPosInt else imPosInt) - stdChar x).re ^ 2 +
           (toScaledComplex q (reInt, if neg then -imPosInt else imPosInt) - stdChar x).im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    ring
  have hstd_re : (stdChar x).re = Real.cos θ := by
    unfold stdChar
    rw [Complex.exp_ofReal_mul_I_re, hx]
    cases neg <;> simp [Real.cos_neg]
  have hstd_im : (stdChar x).im = if neg then -Real.sin θ else Real.sin θ := by
    unfold stdChar
    rw [Complex.exp_ofReal_mul_I_im, hx]
    cases neg <;> simp [Real.sin_neg]
  have hre_err :
      |(toScaledComplex q (reInt, if neg then -imPosInt else imPosInt) - stdChar x).re| ≤
        (2 : ℝ) ^ (-(q + 2 : ℤ)) := by
    change |(reInt : ℝ) / (2 : ℝ) ^ (q + 2) - (stdChar x).re| ≤ _
    rw [hstd_re]
    exact hre
  have him_err :
      |(toScaledComplex q (reInt, if neg then -imPosInt else imPosInt) - stdChar x).im| ≤
        (2 : ℝ) ^ (-(q + 2 : ℤ)) := by
    change |((if neg then -imPosInt else imPosInt : ℤ) : ℝ) / (2 : ℝ) ^ (q + 2) - (stdChar x).im| ≤ _
    rw [hstd_im]
    cases neg
    · simpa using him
    · simp only [↓reduceIte, Int.cast_neg, neg_div]
      have heq : -((imPosInt : ℝ) / (2 : ℝ) ^ (q + 2)) - -Real.sin θ =
          -((imPosInt : ℝ) / (2 : ℝ) ^ (q + 2) - Real.sin θ) := by ring
      rw [heq, abs_neg]
      exact him
  rw [hnorm]
  have hbound := complex_rounding_norm_le _ _ ((2 : ℝ) ^ (-(q + 2 : ℤ))) (by positivity) hre_err him_err
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr q := by unfold complexQuantizeMaxErr; positivity
  unfold complexQuantizeMaxErr at hq_nonneg ⊢
  linarith

/-- Helper identities and power-of-two bounds for `numTheta` and `denTheta` in `computableStdCharCore`. -/
theorem stdChar_theta_identities_and_bounds (B_pi num den : ℕ) (hnum : num ≤ den) :
    let piNat := (computablePiScaledWithCost B_pi).1.toNat
    let numTheta : ℕ := 2 * piNat * num
    let denTheta : ℕ := den * 2 ^ B_pi
    let D : ℕ := 2 * B_pi + 2 * Nat.log2 den + 10
    (((2 * piNat : ℕ) : ℤ) * (num : ℤ)).toNat = 2 * piNat * num ∧
    ((numTheta : ℤ) * (numTheta : ℤ)) = ((numTheta ^ 2 : ℕ) : ℤ) ∧
    ((denTheta : ℤ) * (denTheta : ℤ)).toNat = denTheta ^ 2 ∧
    2 * piNat ≤ 2 ^ (B_pi + 3) ∧
    num ≤ 2 ^ (Nat.log2 den + 1) ∧
    den ≤ 2 ^ (Nat.log2 den + 1) ∧
    numTheta ≤ 2 ^ (B_pi + Nat.log2 den + 4) ∧
    denTheta ≤ 2 ^ (B_pi + Nat.log2 den + 1) ∧
    ((numTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D ∧
    ((denTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D := by
  intro piNat numTheta denTheta D
  have hpi_le := computablePiScaledWithCost_toNat_le B_pi
  have h2pi_le : 2 * piNat ≤ 2 ^ (B_pi + 3) := by
    calc 2 * piNat ≤ 2 * 2 ^ (B_pi + 2) := Nat.mul_le_mul_left 2 hpi_le
      _ = 2 ^ (B_pi + 3) := by rw [← pow_succ']
  have hden_le : den ≤ 2 ^ (Nat.log2 den + 1) := nat_le_two_pow_log2_add_one den
  have hnum_le : num ≤ 2 ^ (Nat.log2 den + 1) := hnum.trans hden_le
  have hnumTheta_eq : (((2 * piNat : ℕ) : ℤ) * (num : ℤ)).toNat = 2 * piNat * num := by
    rw [← Nat.cast_mul, Int.toNat_natCast]
  have hnum_sq_eq : ((numTheta : ℤ) * (numTheta : ℤ)) = ((numTheta ^ 2 : ℕ) : ℤ) := by
    push_cast; ring
  have hden_sq_eq : ((denTheta : ℤ) * (denTheta : ℤ)).toNat = denTheta ^ 2 := by
    rw [← Nat.cast_mul, Int.toNat_natCast, sq]
  have hnumTheta_le : numTheta ≤ 2 ^ (B_pi + Nat.log2 den + 4) := by
    dsimp [numTheta]
    calc 2 * piNat * num
        ≤ 2 ^ (B_pi + 3) * 2 ^ (Nat.log2 den + 1) := Nat.mul_le_mul h2pi_le hnum_le
      _ = 2 ^ (B_pi + Nat.log2 den + 4) := by rw [← pow_add]; congr 1; omega
  have hdenTheta_le : denTheta ≤ 2 ^ (B_pi + Nat.log2 den + 1) := by
    dsimp [denTheta]
    calc den * 2 ^ B_pi
        ≤ 2 ^ (Nat.log2 den + 1) * 2 ^ B_pi := Nat.mul_le_mul_right _ hden_le
      _ = 2 ^ (B_pi + Nat.log2 den + 1) := by rw [← pow_add]; congr 1; omega
  have hnum_sq_le : numTheta ^ 2 ≤ 2 ^ D := by
    calc numTheta ^ 2
        ≤ (2 ^ (B_pi + Nat.log2 den + 4)) ^ 2 := Nat.pow_le_pow_left hnumTheta_le 2
      _ = 2 ^ ((B_pi + Nat.log2 den + 4) * 2) := (pow_mul 2 _ 2).symm
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega)
  have hden_sq_le : denTheta ^ 2 ≤ 2 ^ D := by
    calc denTheta ^ 2
        ≤ (2 ^ (B_pi + Nat.log2 den + 1)) ^ 2 := Nat.pow_le_pow_left hdenTheta_le 2
      _ = 2 ^ ((B_pi + Nat.log2 den + 1) * 2) := (pow_mul 2 _ 2).symm
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega)
  exact ⟨hnumTheta_eq, hnum_sq_eq, hden_sq_eq, h2pi_le, hnum_le, hden_le,
    hnumTheta_le, hdenTheta_le, by exact_mod_cast hnum_sq_le, by exact_mod_cast hden_sq_le⟩

/-- Accuracy theorem for `computableStdCharCore`. -/
theorem computableStdCharCore_error_le (q B B_pi N Bint w num den : ℕ) (neg : Bool)
    (hB : B = q + 2) (hB_pi : B_pi = B + 4) (hN : B + 25 ≤ N) (hBint : B + 2 * N + 22 ≤ Bint)
    (hw : Bint + 4 * N + 2 * B_pi + 2 * Nat.log2 den + 40 ≤ w)
    (hden : 0 < den) (hnum : num ≤ den) :
    ‖toScaledComplex q (computableStdCharCore B B_pi N Bint w num den neg).1 -
      stdChar ((if neg then -(num : ℝ) else (num : ℝ)) / (den : ℝ))‖ ≤
      2 * complexQuantizeMaxErr q := by
  dsimp only [computableStdCharCore, costedMulInt]
  have hident := stdChar_theta_identities_and_bounds B_pi num den hnum
  have hpi_spec := computablePiScaledWithCost_error_le B_pi
  generalize hPiInt : (computablePiScaledWithCost B_pi).1 = piInt at hpi_spec hident ⊢
  obtain ⟨hpi_err, hpi_nonneg⟩ := hpi_spec
  set piNat := piInt.toNat
  have hpiNat_cast : (piNat : ℝ) = (piInt : ℝ) := by
    have : (piNat : ℤ) = piInt := Int.toNat_of_nonneg hpi_nonneg
    exact_mod_cast this
  rw [hident.1, hident.2.1, hident.2.2.1]
  set numTheta : ℕ := 2 * piNat * num
  set denTheta : ℕ := den * 2 ^ B_pi
  set D : ℕ := 2 * B_pi + 2 * Nat.log2 den + 10
  have hdenTheta_pos : 0 < denTheta := Nat.mul_pos hden (pow_pos zero_lt_two B_pi)
  have hden_r : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have hB_zpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(B : ℤ)) := by positivity
  have hfrac_le1 : (num : ℝ) / (den : ℝ) ≤ 1 := by
    rw [div_le_one hden_r]
    exact_mod_cast hnum
  have hfrac_nonneg : 0 ≤ (num : ℝ) / (den : ℝ) := by positivity
  set θ : ℝ := 2 * Real.pi * (num : ℝ) / (den : ℝ)
  set θ_hat : ℝ := (numTheta : ℝ) / (denTheta : ℝ)
  have hθ_hat_eq : θ_hat = 2 * ((piInt : ℝ) / (2 : ℝ) ^ B_pi) * ((num : ℝ) / (den : ℝ)) := by
    dsimp [θ_hat, numTheta, denTheta]
    push_cast
    rw [hpiNat_cast]
    ring
  have hθ_hat_nonneg : 0 ≤ θ_hat := by positivity
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hBpi_le1 : (2 : ℝ) ^ (-(B_pi : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hpi_hat_le : (piInt : ℝ) / (2 : ℝ) ^ B_pi ≤ (4.15 : ℝ) := by
    have := (abs_le.mp hpi_err).2
    linarith
  have hθ_hat_le9 : θ_hat ≤ (9 : ℝ) := by
    rw [hθ_hat_eq]
    nlinarith
  have hBpi_pow : 2 * (2 : ℝ) ^ (-(B_pi : ℤ)) = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have : (-(B_pi : ℤ)) = (-4 : ℤ) + (-(B : ℤ)) := by omega
    rw [this, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  have hθ_diff : |θ_hat - θ| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have hsub : θ_hat - θ = 2 * ((num : ℝ) / (den : ℝ)) * ((piInt : ℝ) / (2 : ℝ) ^ B_pi - Real.pi) := by
      rw [hθ_hat_eq]
      dsimp [θ]
      ring
    rw [hsub, abs_mul, abs_of_nonneg (by positivity), ← hBpi_pow]
    calc 2 * ((num : ℝ) / (den : ℝ)) * |(piInt : ℝ) / (2 : ℝ) ^ B_pi - Real.pi|
        ≤ 2 * 1 * (2 : ℝ) ^ (-(B_pi : ℤ)) :=
          mul_le_mul (by linarith) hpi_err (abs_nonneg _) (by positivity)
      _ = 2 * (2 : ℝ) ^ (-(B_pi : ℤ)) := by ring
  have hB3_pow : (2 : ℝ) ^ (-(B + 3 : ℤ)) = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have : (-(B + 3 : ℤ)) = (-3 : ℤ) + (-(B : ℤ)) := by omega
    rw [this, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hN_Bint := recurrence_rounding_error_le_eighth B N 0 9 Bint (by omega)
  have hcos_spec := cos_recurrence_spec_and_widths Bint 9 D w N numTheta denTheta
    hdenTheta_pos (by exact_mod_cast hθ_hat_le9)
    hident.2.2.2.2.2.2.2.2.1 hident.2.2.2.2.2.2.2.2.2 (by dsimp [D]; omega)
  have hsin_spec := sin_recurrence_spec_and_widths Bint 9 D w N numTheta denTheta
    hdenTheta_pos (by exact_mod_cast hθ_hat_le9)
    hident.2.2.2.2.2.2.2.2.1 hident.2.2.2.2.2.2.2.2.2 (by dsimp [D]; omega)
  have hcos_rem : |cosTaylorSum N θ_hat - Real.cos θ_hat| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [abs_sub_comm, ← hB3_pow]
    exact ((abs_cosTaylorRem_and_sinTaylorRem_le N).1 θ_hat hθ_hat_nonneg).trans
      (pow_div_factorial_le_two_zpow_neg 9 (B + 3) (2 * N) (by omega) θ_hat hθ_hat_nonneg hθ_hat_le9)
  have hsin_rem : |sinTaylorSum N θ_hat - Real.sin θ_hat| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [abs_sub_comm, ← hB3_pow]
    exact ((abs_cosTaylorRem_and_sinTaylorRem_le N).2 θ_hat hθ_hat_nonneg).trans
      (pow_div_factorial_le_two_zpow_neg 9 (B + 3) (2 * N + 1) (by omega) θ_hat hθ_hat_nonneg hθ_hat_le9)
  dsimp only [costedDivRoundRatInt]
  set cosSumVal := (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N).1.2
  set sinSumVal := (runRecurrenceSeriesCosted w
    (divRoundRatInt ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denTheta : ℤ))
    (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N).1.2
  generalize hDenInt : ((2 ^ Bint : ℕ) : ℤ) = denInt
  have hdenInt_pos : 0 < denInt := by subst hDenInt; positivity
  have hre_q := abs_divRoundRatInt_mul_two_pow_div_sub_le B cosSumVal denInt hdenInt_pos
  have him_q := abs_divRoundRatInt_mul_two_pow_div_sub_le B sinSumVal denInt hdenInt_pos
  generalize hReInt : divRoundRatInt (cosSumVal * ((2 ^ B : ℕ) : ℤ)) denInt = reInt at hre_q ⊢
  generalize hImPosInt : divRoundRatInt (sinSumVal * ((2 ^ B : ℕ) : ℤ)) denInt = imPosInt at him_q ⊢
  have hcast_cos : (cosSumVal : ℝ) / (denInt : ℝ) = (cosSumVal : ℝ) / (2 : ℝ) ^ Bint := by
    subst hDenInt; push_cast; rfl
  have hcast_sin : (sinSumVal : ℝ) / (denInt : ℝ) = (sinSumVal : ℝ) / (2 : ℝ) ^ Bint := by
    subst hDenInt; push_cast; rfl
  rw [hcast_cos] at hre_q
  rw [hcast_sin] at him_q
  have hre_total : |(reInt : ℝ) / (2 : ℝ) ^ B - Real.cos θ| ≤ (2 : ℝ) ^ (-(B : ℤ)) :=
    abs_sub_le_of_four_step_approx _ _ _ _ _ ((2 : ℝ) ^ (-(B : ℤ))) hB_zpow
      hre_q (hcos_spec.1.trans (by simpa using hN_Bint)) hcos_rem ((abs_cos_sub_le θ_hat θ).trans hθ_diff)
  have him_total : |(imPosInt : ℝ) / (2 : ℝ) ^ B - Real.sin θ| ≤ (2 : ℝ) ^ (-(B : ℤ)) :=
    abs_sub_le_of_four_step_approx _ _ _ _ _ ((2 : ℝ) ^ (-(B : ℤ))) hB_zpow
      him_q (hsin_spec.1.trans (by simpa using hN_Bint)) hsin_rem ((abs_sin_sub_le θ_hat θ).trans hθ_diff)
  rw [hB] at hre_total him_total
  have hx_angle : 2 * Real.pi * ((if neg then -(num : ℝ) else (num : ℝ)) / (den : ℝ)) =
      if neg then -θ else θ := by
    cases neg <;> { dsimp [θ]; ring }
  exact norm_toScaledComplex_sub_stdChar_le q reInt imPosInt neg _ θ hx_angle hre_total him_total

/-- **Accuracy Theorem for `computableStdCharWithProgramCost` (`computableStdCharWithProgramCost_error_le`)**:
For `0 < den` and `num ≤ den`, `computableStdCharWithProgramCost q num den neg` approximates
`stdChar ((if neg then -num else num) / den)` on `toScaledComplex q` within `2 * complexQuantizeMaxErr q`. -/
theorem computableStdCharWithProgramCost_error_le
    (q num den : ℕ) (neg : Bool) (hden : 0 < den) (hnum : num ≤ den) :
    ‖toScaledComplex q (computableStdCharWithProgramCost q num den neg).1 -
      stdChar ((if neg then -(num : ℝ) else (num : ℝ)) / (den : ℝ))‖ ≤
      2 * complexQuantizeMaxErr q :=
  computableStdCharCore_error_le q (q + 2) (q + 2 + 4) (q + 2 + 25)
    ((q + 2) + 2 * (q + 2 + 25) + 22)
    (((q + 2) + 2 * (q + 2 + 25) + 22) + 4 * (q + 2 + 25) + 2 * (q + 2 + 4) + 2 * Nat.log2 den + 40)
    num den neg rfl rfl le_rfl le_rfl le_rfl hden hnum

/-- Call-site width soundness predicate for `computableStdCharWithProgramCost q num den neg`. -/
def StdCharWidthSound (q num den : ℕ) : Prop :=
  let B := q + 2
  let B_pi := B + 4
  let N := B + 25
  let Bint := B + 2 * N + 22
  let w := Bint + 4 * N + 2 * B_pi + 2 * Nat.log2 den + 40
  let piRes := computablePiScaledWithCost B_pi
  let piNat := piRes.1.toNat
  let numThetaRes := costedMulInt w ((2 * piNat : ℕ) : ℤ) (num : ℤ)
  let numTheta : ℕ := numThetaRes.1.toNat
  let denTheta : ℕ := den * 2 ^ B_pi
  let numThetaSqRes := costedMulInt w (numTheta : ℤ) (numTheta : ℤ)
  let negNumThetaSq : ℤ := -numThetaSqRes.1
  let denThetaSqRes := costedMulInt w (denTheta : ℤ) (denTheta : ℤ)
  let denThetaSq : ℕ := denThetaSqRes.1.toNat
  let cosSeriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N
  let sinA0Res := costedDivRoundRatInt w
    ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ))
    (denTheta : ℤ)
  let sinSeriesRes := runRecurrenceSeriesCosted w sinA0Res.1
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N
  PiScaledWidthSound B_pi ∧
  FitsSignedScalarWord w ((2 * piNat : ℕ) : ℤ) ∧
  FitsSignedScalarWord w (num : ℤ) ∧
  FitsSignedScalarWord w (numTheta : ℤ) ∧
  FitsSignedScalarWord w (denTheta : ℤ) ∧
  RecurrenceCallSitesWidthSound w ((2 ^ Bint : ℕ) : ℤ)
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N ∧
  FitsSignedScalarWord w (cosSeriesRes.1.2 * ((2 ^ B : ℕ) : ℤ)) ∧
  FitsSignedScalarWord w ((2 ^ Bint : ℕ) : ℤ) ∧
  FitsSignedScalarWord w ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) ∧
  RecurrenceCallSitesWidthSound w sinA0Res.1
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N ∧
  FitsSignedScalarWord w (sinSeriesRes.1.2 * ((2 ^ B : ℕ) : ℤ))

/-- **Call-Site Width Soundness for `computableStdCharWithProgramCost`**:
Every operand passed to `costedMulInt w` and `costedDivRoundRatInt w` inside
`computableStdCharWithProgramCost q num den neg` fits within `w` bits. -/
theorem computableStdCharWithProgramCost_widths_sound
    (q num den : ℕ) (hden : 0 < den) (hnum : num ≤ den) :
    StdCharWidthSound q num den := by
  dsimp only [StdCharWidthSound, costedMulInt, costedDivRoundRatInt]
  set B := q + 2 with hB_def
  set B_pi := B + 4 with hB_pi_def
  set N := B + 25 with hN_def
  set Bint := B + 2 * N + 22 with hBint_def
  set w := Bint + 4 * N + 2 * B_pi + 2 * Nat.log2 den + 40 with hw_def
  set D := 2 * B_pi + 2 * Nat.log2 den + 10 with hD_def
  clear_value B B_pi N Bint w D
  have hident := stdChar_theta_identities_and_bounds B_pi num den hnum
  have hpi_spec := computablePiScaledWithCost_error_le B_pi
  generalize hPiInt : (computablePiScaledWithCost B_pi).1 = piInt at hpi_spec hident ⊢
  obtain ⟨hpi_err, hpi_nonneg⟩ := hpi_spec
  set piNat := piInt.toNat
  have hpiNat_cast : (piNat : ℝ) = (piInt : ℝ) := by
    have : (piNat : ℤ) = piInt := Int.toNat_of_nonneg hpi_nonneg
    exact_mod_cast this
  rw [hident.1, hident.2.1, hident.2.2.1]
  set numTheta : ℕ := 2 * piNat * num
  set denTheta : ℕ := den * 2 ^ B_pi
  have hdenTheta_pos : 0 < denTheta := Nat.mul_pos hden (pow_pos zero_lt_two B_pi)
  have hden_r : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have hfrac_le1 : (num : ℝ) / (den : ℝ) ≤ 1 := (div_le_one hden_r).mpr (by exact_mod_cast hnum)
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hBpi_le1 : (2 : ℝ) ^ (-(B_pi : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hpi_hat_le : (piInt : ℝ) / (2 : ℝ) ^ B_pi ≤ (4.15 : ℝ) := by
    have := (abs_le.mp hpi_err).2
    linarith
  have hθ_hat_eq : (numTheta : ℝ) / (denTheta : ℝ) =
      2 * ((piInt : ℝ) / (2 : ℝ) ^ B_pi) * ((num : ℝ) / (den : ℝ)) := by
    dsimp [numTheta, denTheta]
    push_cast
    rw [hpiNat_cast]
    ring
  have hθ_hat_le9 : (numTheta : ℝ) / (denTheta : ℝ) ≤ (9 : ℝ) := by
    rw [hθ_hat_eq]
    have : 0 ≤ (num : ℝ) / (den : ℝ) := by positivity
    nlinarith
  have hcos_spec := cos_recurrence_spec_and_widths Bint 9 D w N numTheta denTheta
    hdenTheta_pos (by exact_mod_cast hθ_hat_le9)
    (hD_def ▸ hident.2.2.2.2.2.2.2.2.1) (hD_def ▸ hident.2.2.2.2.2.2.2.2.2) (by omega)
  have hsin_spec := sin_recurrence_spec_and_widths Bint 9 D w N numTheta denTheta
    hdenTheta_pos (by exact_mod_cast hθ_hat_le9)
    (hD_def ▸ hident.2.2.2.2.2.2.2.2.1) (hD_def ▸ hident.2.2.2.2.2.2.2.2.2) (by omega)
  dsimp only at hcos_spec hsin_spec
  generalize hCosVal : (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N).1.2 = cosSumVal at hcos_spec ⊢
  generalize hSinVal : (runRecurrenceSeriesCosted w
    (divRoundRatInt ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denTheta : ℤ))
    (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N).1.2 = sinSumVal at hsin_spec ⊢
  have hf_2pi : FitsSignedScalarWord w ((2 * piNat : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hident.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_num : FitsSignedScalarWord w (num : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hident.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_numT : FitsSignedScalarWord w (numTheta : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hident.2.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_denT : FitsSignedScalarWord w (denTheta : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hident.2.2.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_Bint : FitsSignedScalarWord w ((2 ^ Bint : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hf_sinA0_num : FitsSignedScalarWord w ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) := by
    rw [← Nat.cast_mul]
    refine fitsSignedScalarWord_of_nat_le_two_pow _ _ ?_
    calc numTheta * 2 ^ Bint
        ≤ 2 ^ (B_pi + Nat.log2 den + 4) * 2 ^ Bint :=
          Nat.mul_le_mul_right _ hident.2.2.2.2.2.2.1
      _ = 2 ^ (B_pi + Nat.log2 den + 4 + Bint) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hf_cos_out : FitsSignedScalarWord w (cosSumVal * ((2 ^ B : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_abs_le_two_pow _ _ ?_
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B)]
    calc |(cosSumVal : ℝ)| * (2 : ℝ) ^ B
        ≤ (2 : ℝ) ^ (Bint + 2 * 9 + 2 * N + 3) * (2 : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right hcos_spec.2.2 (by positivity)
      _ = (2 : ℝ) ^ (Bint + 2 * 9 + 2 * N + 3 + B) := (pow_add (2 : ℝ) _ _).symm
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hf_sin_out : FitsSignedScalarWord w (sinSumVal * ((2 ^ B : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_abs_le_two_pow _ _ ?_
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B)]
    calc |(sinSumVal : ℝ)| * (2 : ℝ) ^ B
        ≤ (2 : ℝ) ^ (Bint + 2 * 9 + 2 * N + 3) * (2 : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right hsin_spec.2.2 (by positivity)
      _ = (2 : ℝ) ^ (Bint + 2 * 9 + 2 * N + 3 + B) := (pow_add (2 : ℝ) _ _).symm
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨computablePiScaledWithCost_widths_sound B_pi,
    hf_2pi, hf_num, hf_numT, hf_denT, hcos_spec.2.1, hf_cos_out,
    hf_Bint, hf_sinA0_num, hsin_spec.2.1, hf_sin_out⟩

/-- **Bit-Operation Cost Bound for `computableStdCharWithProgramCost` (`computableStdCharWithProgramCost_snd_le`)**:
Bounded by an explicit degree-4 polynomial in `M = q + Nat.log2 den + 1`. -/
theorem computableStdCharWithProgramCost_snd_le (q num den : ℕ) (neg : Bool) :
    let M := q + Nat.log2 den + 1
    (computableStdCharWithProgramCost q num den neg).2 ≤
      18000 * (M + 30) ^ 4 := by
  intro M
  dsimp only [computableStdCharWithProgramCost, computableStdCharCore,
    costedShiftLeftNat, costedShiftLeftInt, costedMulInt, costedDivRoundRatInt]
  set B := q + 2 with hB_def
  set B_pi := B + 4 with hB_pi_def
  set N := B + 25 with hN_def
  set Bint := B + 2 * N + 22 with hBint_def
  set w := Bint + 4 * N + 2 * B_pi + 2 * Nat.log2 den + 40 with hw_def
  clear_value B B_pi N Bint w
  rw [runRecurrenceSeriesCosted_snd, runRecurrenceSeriesCosted_snd]
  have hpi_cost := computablePiScaledWithCost_snd_le B_pi
  have hBpi7_le : B_pi + 7 ≤ M + 30 := by dsimp [M]; omega
  have h8Bpi_le : 8 * B_pi + 85 ≤ 9 * (M + 30) := by dsimp [M]; omega
  have hpi_le : (computablePiScaledWithCost B_pi).2 ≤ 3645 * (M + 30) ^ 4 := by
    calc (computablePiScaledWithCost B_pi).2
        ≤ (B_pi + 7) * 5 * (8 * B_pi + 85) ^ 3 := hpi_cost
      _ ≤ (M + 30) * 5 * (9 * (M + 30)) ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_right 5 hBpi7_le) (Nat.pow_le_pow_left h8Bpi_le 3)
      _ = 3645 * (M + 30) ^ 4 := by ring
  have hw_le : w + 1 ≤ 9 * (M + 30) := by dsimp [M]; omega
  have hmul_w : computableMulBitCost w ≤ (9 * (M + 30)) ^ 3 :=
    (computableMulBitCost_le_cube w).trans (Nat.pow_le_pow_left hw_le 3)
  have hadd_w : addBitCost w ≤ (9 * (M + 30)) ^ 3 :=
    (addBitCost_le_cube w).trans (Nat.pow_le_pow_left hw_le 3)
  have hN_le : 2 * N + 4 ≤ 2 * (M + 30) := by dsimp [M]; omega
  generalize computableMulBitCost w = MulC at hmul_w ⊢
  generalize addBitCost w = AddC at hadd_w ⊢
  generalize hW3 : (9 * (M + 30)) ^ 3 = W3 at hmul_w hadd_w
  have hstep :
      (computablePiScaledWithCost B_pi).2 +
        MulC + AddC + MulC + MulC +
        (N * (6 * MulC + 3 * AddC)) +
        AddC + (2 * MulC + 2 * AddC) +
        AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) +
        AddC + (2 * MulC + 2 * AddC) + 2 * AddC ≤
      (computablePiScaledWithCost B_pi).2 +
        (2 * N + 4) * (6 * MulC + 3 * AddC) := by
    nlinarith
  calc (computablePiScaledWithCost B_pi).2 +
        MulC + AddC + MulC + MulC +
        (N * (6 * MulC + 3 * AddC)) +
        AddC + (2 * MulC + 2 * AddC) +
        AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) +
        AddC + (2 * MulC + 2 * AddC) + 2 * AddC
      ≤ (computablePiScaledWithCost B_pi).2 +
        (2 * N + 4) * (6 * MulC + 3 * AddC) := hstep
    _ ≤ 3645 * (M + 30) ^ 4 +
        (2 * (M + 30)) * (6 * W3 + 3 * W3) :=
        Nat.add_le_add hpi_le (Nat.mul_le_mul hN_le (by omega))
    _ = 16767 * (M + 30) ^ 4 := by subst hW3; ring
    _ ≤ 18000 * (M + 30) ^ 4 := Nat.mul_le_mul_right _ (by decide)

/-! ### 6. Computable Evaluator for `sincGaussian` Filter Taps -/

/-- For `3 ≤ B`, `(computableLog2ScaledWithCost B).1 / 2^B ≥ 1 / 2` and `0 ≤ (computableLog2ScaledWithCost B).1`. -/
theorem computableLog2ScaledWithCost_ge_half (B : ℕ) (hB : 3 ≤ B) :
    (1 / 2 : ℝ) ≤ ((computableLog2ScaledWithCost B).1 : ℝ) / (2 : ℝ) ^ B ∧
    0 ≤ (computableLog2ScaledWithCost B).1 := by
  have herr := computableLog2ScaledWithCost_error_le B
  have hlog2_gt := Real.log_two_gt_d9
  have hpow : (2 : ℝ) ^ (-(B : ℤ)) ≤ 1 / 8 := by
    calc (2 : ℝ) ^ (-(B : ℤ)) ≤ (2 : ℝ) ^ (-3 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = 1 / 8 := by norm_num
  have hge : (1 / 2 : ℝ) ≤ ((computableLog2ScaledWithCost B).1 : ℝ) / (2 : ℝ) ^ B := by
    have := (abs_le.mp herr).1
    linarith
  refine ⟨hge, ?_⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have h0 : (0 : ℝ) ≤ ((computableLog2ScaledWithCost B).1 : ℝ) := by
    have := (le_div_iff₀ hpos).mp ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hge)
    linarith
  exact_mod_cast h0

/-- Symmetric clamping `max (-(2^B)) (min (2^B) rawG)` preserves scaled accuracy for `|x| ≤ 1`. -/
theorem abs_clampInt_symm_scaled_sub_le (B : ℕ) (rawG : ℤ) (x δ : ℝ)
    (hx : |x| ≤ 1)
    (hraw : |(rawG : ℝ) / (2 : ℝ) ^ B - x| ≤ δ) :
    let G := max (-((2 ^ B : ℕ) : ℤ)) (min ((2 ^ B : ℕ) : ℤ) rawG)
    |(G : ℝ) / (2 : ℝ) ^ B - x| ≤ δ ∧
    G.natAbs ≤ 2 ^ B ∧
    |(G : ℝ) / (2 : ℝ) ^ B| ≤ 1 := by
  intro G
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  obtain ⟨hx_dn, hx_up⟩ := abs_le.mp hx
  have hlo : ((-((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ) ≤ x * (2 : ℝ) ^ B := by
    push_cast; nlinarith
  have hhi : x * (2 : ℝ) ^ B ≤ (((2 ^ B : ℕ) : ℤ) : ℝ) := by
    push_cast; nlinarith
  have hclamp := abs_clampInt_sub_le (-((2 ^ B : ℕ) : ℤ)) ((2 ^ B : ℕ) : ℤ) rawG
    (x * (2 : ℝ) ^ B) hlo hhi
  have hdiv1 : ((G : ℝ) - x * (2 : ℝ) ^ B) / (2 : ℝ) ^ B = (G : ℝ) / (2 : ℝ) ^ B - x := by
    field_simp [hpow_pos.ne']
  have hdiv2 : ((rawG : ℝ) - x * (2 : ℝ) ^ B) / (2 : ℝ) ^ B = (rawG : ℝ) / (2 : ℝ) ^ B - x := by
    field_simp [hpow_pos.ne']
  have herr : |(G : ℝ) / (2 : ℝ) ^ B - x| ≤ δ := by
    rw [← hdiv1, abs_div, abs_of_pos hpow_pos]
    have h2 : |(rawG : ℝ) - x * (2 : ℝ) ^ B| / (2 : ℝ) ^ B = |(rawG : ℝ) / (2 : ℝ) ^ B - x| := by
      rw [← hdiv2, abs_div, abs_of_pos hpow_pos]
    calc |(G : ℝ) - x * (2 : ℝ) ^ B| / (2 : ℝ) ^ B
        ≤ |(rawG : ℝ) - x * (2 : ℝ) ^ B| / (2 : ℝ) ^ B :=
          div_le_div_of_nonneg_right hclamp hpow_pos.le
      _ = |(rawG : ℝ) / (2 : ℝ) ^ B - x| := h2
      _ ≤ δ := hraw
  have h2B_z : (0 : ℤ) ≤ ((2 ^ B : ℕ) : ℤ) := Nat.cast_nonneg _
  have hG_dn : -((2 ^ B : ℕ) : ℤ) ≤ G := le_max_left _ _
  have hG_up : G ≤ ((2 ^ B : ℕ) : ℤ) :=
    max_le (neg_le_self h2B_z) (min_le_left _ _)
  have hG_natAbs : G.natAbs ≤ 2 ^ B := by
    generalize (G : ℤ) = g at hG_dn hG_up
    omega
  have hG_le1 : |(G : ℝ) / (2 : ℝ) ^ B| ≤ 1 := by
    rw [abs_div, abs_of_pos hpow_pos, div_le_one hpow_pos]
    have hcast : |(G : ℝ)| = (G.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
    rw [hcast]
    exact_mod_cast hG_natAbs
  exact ⟨herr, hG_natAbs, hG_le1⟩

/-- Rational representation and upper bound for the fractional-shift tap offset
`t = (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))`. -/
theorem tap_offset_abs_eq_and_le (pSub t1 j1 s : ℕ)
    (ht1 : 0 < t1) (hj1 : j1 < t1) (hs : s < 2 * pSub + 1) :
    let numT : ℕ := (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)).natAbs
    let t : ℝ := (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))
    |t| = (numT : ℝ) / (t1 : ℝ) ∧
    numT ≤ (pSub + 1) * t1 ∧
    |t| ≤ (pSub + 1 : ℝ) := by
  intro numT t
  set z : ℤ := ((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)
  have ht1_r : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1
  have ht_eq : t = (z : ℝ) / (t1 : ℝ) := by
    dsimp [t, z]
    push_cast
    field_simp [ht1_r.ne']
  have h_abs : |t| = (numT : ℝ) / (t1 : ℝ) := by
    rw [ht_eq, abs_div, abs_of_pos ht1_r]
    have hcast : (numT : ℝ) = |(z : ℝ)| := by
      change (z.natAbs : ℝ) = |(z : ℝ)|
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hcast]
  have hs_dn : -(pSub : ℤ) ≤ (s : ℤ) - (pSub : ℤ) := by omega
  have hs_up : (s : ℤ) - (pSub : ℤ) ≤ (pSub : ℤ) := by omega
  have ht1_z : (0 : ℤ) ≤ (t1 : ℤ) := by omega
  have hj1_0 : (0 : ℤ) ≤ (j1 : ℤ) := by omega
  have hj1_lt : (j1 : ℤ) ≤ (t1 : ℤ) := by omega
  have hz_up : z ≤ (((pSub + 1) * t1 : ℕ) : ℤ) := by
    push_cast
    dsimp [z]
    nlinarith
  have hz_dn : -(((pSub + 1) * t1 : ℕ) : ℤ) ≤ z := by
    push_cast
    dsimp [z]
    nlinarith
  have hnumT_le : numT ≤ (pSub + 1) * t1 := by
    dsimp [numT]
    omega
  have ht_le : |t| ≤ (pSub + 1 : ℝ) := by
    rw [h_abs, div_le_iff₀ ht1_r]
    exact_mod_cast hnumT_le
  exact ⟨h_abs, hnumT_le, ht_le⟩

/-- Quotient-of-squares perturbation bound:
for `0 ≤ a, b ≤ M` and `2 ≤ c, d`,
`|a^2 / c - b^2 / d| ≤ M * |a - b| + M^2 * |c - d|`. -/
theorem abs_sq_div_sub_sq_div_le (a b c d M : ℝ)
    (ha0 : 0 ≤ a) (haM : a ≤ M) (hb0 : 0 ≤ b) (hbM : b ≤ M)
    (hc : 2 ≤ c) (hd : 2 ≤ d) :
    |a ^ 2 / c - b ^ 2 / d| ≤ M * |a - b| + M ^ 2 * |c - d| := by
  have hc_pos : 0 < c := by linarith
  have hd_pos : 0 < d := by linarith
  have hsplit : a ^ 2 / c - b ^ 2 / d =
      ((a + b) / c) * (a - b) + (b ^ 2 / (c * d)) * (d - c) := by
    field_simp [hc_pos.ne', hd_pos.ne']
    ring
  rw [hsplit]
  have htri := abs_add_le (((a + b) / c) * (a - b)) ((b ^ 2 / (c * d)) * (d - c))
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a + b) / c),
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ b ^ 2 / (c * d)),
      abs_sub_comm d c] at htri
  have h1 : (a + b) / c ≤ M := by
    rw [div_le_iff₀ hc_pos]
    nlinarith
  have h2 : b ^ 2 / (c * d) ≤ M ^ 2 := by
    rw [div_le_iff₀ (mul_pos hc_pos hd_pos)]
    have hb_sq : b ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hb0 hbM 2
    have hcd : 4 ≤ c * d := by nlinarith
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (a - b))
  have hm2 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (c - d))
  linarith

/-- Upper bound `(computableLog2ScaledWithCost B).1.toNat ≤ 2 ^ (B + 1)` for all `B : ℕ`. -/
theorem computableLog2ScaledWithCost_toNat_le (B : ℕ) :
    (computableLog2ScaledWithCost B).1.toNat ≤ 2 ^ (B + 1) := by
  have herr := computableLog2ScaledWithCost_error_le B
  generalize (computableLog2ScaledWithCost B).1 = log2Int at herr ⊢
  rcases le_or_gt log2Int 0 with hle0 | hpos
  · rw [Int.toNat_of_nonpos hle0]
    exact Nat.zero_le _
  · have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hpow_le1 : (2 : ℝ) ^ (-(B : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hdiv_le : (log2Int : ℝ) / (2 : ℝ) ^ B ≤ 2 := by
      have := (abs_le.mp herr).2
      linarith
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
    have hle_r : (log2Int : ℝ) ≤ ((2 ^ (B + 1) : ℕ) : ℝ) := by
      have h1 := (div_le_iff₀ hpow_pos).mp hdiv_le
      push_cast
      rw [pow_succ']
      linarith
    have hle_z : log2Int ≤ ((2 ^ (B + 1) : ℕ) : ℤ) := by exact_mod_cast hle_r
    omega

/-- Argument perturbation tail bounds for `sinc` and `exp(-y)` when
`B + N + 3 * M + 6 ≤ B_c`. -/
theorem sinc_and_exp_arg_perturb_le_eighth (B N M B_c : ℕ)
    (hB_c : B + N + 3 * M + 6 ≤ B_c) :
    (N : ℝ) * (2 : ℝ) ^ (2 * M) * ((M : ℝ) * (2 : ℝ) ^ (-(B_c : ℤ))) ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) ∧
    5 * (M : ℝ) ^ 2 * (2 : ℝ) ^ (-(B_c : ℤ)) ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
  have hN_pow : (N : ℝ) ≤ (2 : ℝ) ^ ((N : ℕ) : ℤ) := by
    rw [zpow_natCast]; exact_mod_cast Nat.lt_two_pow_self.le
  have hM_pow : (M : ℝ) ≤ (2 : ℝ) ^ ((M : ℕ) : ℤ) := by
    rw [zpow_natCast]; exact_mod_cast Nat.lt_two_pow_self.le
  have h1 :
      (N : ℝ) * (2 : ℝ) ^ (2 * M) * ((M : ℝ) * (2 : ℝ) ^ (-(B_c : ℤ))) ≤
        (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    calc (N : ℝ) * (2 : ℝ) ^ (2 * M) * ((M : ℝ) * (2 : ℝ) ^ (-(B_c : ℤ)))
        ≤ (2 : ℝ) ^ ((N : ℕ) : ℤ) * (2 : ℝ) ^ ((2 * M : ℕ) : ℤ) *
            ((2 : ℝ) ^ ((M : ℕ) : ℤ) * (2 : ℝ) ^ (-(B_c : ℤ))) := by
          rw [zpow_natCast (2 : ℝ) (2 * M)]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hN_pow (by positivity))
            (mul_le_mul_of_nonneg_right hM_pow (by positivity)) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (((N : ℕ) : ℤ) + ((2 * M : ℕ) : ℤ) + ((M : ℕ) : ℤ) + -(B_c : ℤ)) := by
          simp only [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_assoc]
      _ ≤ (2 : ℝ) ^ ((-3 : ℤ) + -(B : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  have hM2_pow : (M : ℝ) ^ 2 ≤ (2 : ℝ) ^ ((2 * M : ℕ) : ℤ) := by
    rw [zpow_natCast, mul_comm 2 M, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg M) (by exact_mod_cast Nat.lt_two_pow_self.le) 2
  have h5_le : (5 : ℝ) ≤ (2 : ℝ) ^ (3 : ℤ) := by norm_num
  have h2 : 5 * (M : ℝ) ^ 2 * (2 : ℝ) ^ (-(B_c : ℤ)) ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    calc 5 * (M : ℝ) ^ 2 * (2 : ℝ) ^ (-(B_c : ℤ))
        ≤ (2 : ℝ) ^ (3 : ℤ) * (2 : ℝ) ^ ((2 * M : ℕ) : ℤ) * (2 : ℝ) ^ (-(B_c : ℤ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h5_le hM2_pow (by positivity) (by positivity)) (by positivity)
      _ = (2 : ℝ) ^ ((3 : ℤ) + ((2 * M : ℕ) : ℤ) + -(B_c : ℤ)) := by
          simp only [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_assoc]
      _ ≤ (2 : ℝ) ^ ((-3 : ℤ) + -(B : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  exact ⟨h1, h2⟩

/-- Product, rounding, and clamping accuracy for `sincGaussian α t = normSinc t * exp(-y)`. -/
theorem sincGaussian_mul_round_clamp_spec (pSub B : ℕ) (hB : B = pSub + 2)
    (sincInt expInt : ℤ) (α t y : ℝ) (hy : 0 ≤ y)
    (hsg : sincGaussian α t = normSinc t * Real.exp (-y))
    (hsinc_err : |(sincInt : ℝ) / (2 : ℝ) ^ B - normSinc t| ≤ (2 : ℝ) ^ (-(B : ℤ)))
    (hsinc_le1 : |(sincInt : ℝ) / (2 : ℝ) ^ B| ≤ 1)
    (hexp_err : |(expInt : ℝ) / (2 : ℝ) ^ B - Real.exp (-y)| ≤ (2 : ℝ) ^ (-(B : ℤ))) :
    let rawG := divRoundRatInt ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)) ((2 ^ (2 * B) : ℕ) : ℤ)
    let G := max (-((2 ^ pSub : ℕ) : ℤ)) (min ((2 ^ pSub : ℕ) : ℤ) rawG)
    |((G : ℝ) / (2 : ℝ) ^ pSub) - sincGaussian α t| ≤ (2 : ℝ) ^ (-(pSub : ℤ)) ∧
    G.natAbs ≤ 2 ^ pSub + 1 := by
  intro rawG G
  set s_hat : ℝ := (sincInt : ℝ) / (2 : ℝ) ^ B
  set e_hat : ℝ := (expInt : ℝ) / (2 : ℝ) ^ B
  have hexp_le1 : |Real.exp (-y)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hprod_split : s_hat * e_hat - sincGaussian α t =
      s_hat * (e_hat - Real.exp (-y)) + (s_hat - normSinc t) * Real.exp (-y) := by
    rw [hsg]; ring
  have hprod_err : |s_hat * e_hat - sincGaussian α t| ≤ 2 * (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [hprod_split]
    have htri := abs_add_le (s_hat * (e_hat - Real.exp (-y))) ((s_hat - normSinc t) * Real.exp (-y))
    rw [abs_mul, abs_mul] at htri
    have hm1 : |s_hat| * |e_hat - Real.exp (-y)| ≤ 1 * (2 : ℝ) ^ (-(B : ℤ)) :=
      mul_le_mul hsinc_le1 hexp_err (abs_nonneg _) zero_le_one
    have hm2 : |s_hat - normSinc t| * |Real.exp (-y)| ≤ (2 : ℝ) ^ (-(B : ℤ)) * 1 :=
      mul_le_mul hsinc_err hexp_le1 (abs_nonneg _) (by positivity)
    linarith
  have h2B_eq : 2 * (2 : ℝ) ^ (-(B : ℤ)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(pSub : ℤ)) := by
    have h1 : (-(B : ℤ)) = (-2 : ℤ) + (-(pSub : ℤ)) := by omega
    have h2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [h1, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h2]
    ring
  rw [h2B_eq] at hprod_err
  have hden2B_pos : (0 : ℤ) < ((2 ^ (2 * B) : ℕ) : ℤ) := by positivity
  have hround_err := abs_divRoundRatInt_mul_two_pow_div_sub_le pSub (sincInt * expInt)
    ((2 ^ (2 * B) : ℕ) : ℤ) hden2B_pos
  have hcast_prod : ((sincInt * expInt : ℤ) : ℝ) / (((2 ^ (2 * B) : ℕ) : ℤ) : ℝ) = s_hat * e_hat := by
    dsimp [s_hat, e_hat]
    push_cast
    rw [two_mul, pow_add, div_mul_div_comm]
  rw [hcast_prod] at hround_err
  have hraw_total : |(rawG : ℝ) / (2 : ℝ) ^ pSub - sincGaussian α t| ≤ (2 : ℝ) ^ (-(pSub : ℤ)) := by
    have htri := abs_add_le ((rawG : ℝ) / (2 : ℝ) ^ pSub - s_hat * e_hat)
      (s_hat * e_hat - sincGaussian α t)
    rw [sub_add_sub_cancel] at htri
    linarith
  have hsg_le1 : |sincGaussian α t| ≤ 1 := abs_sincGaussian_le_one α t
  have hclamp := abs_clampInt_symm_scaled_sub_le pSub rawG (sincGaussian α t)
    ((2 : ℝ) ^ (-(pSub : ℤ))) hsg_le1 hraw_total
  refine ⟨hclamp.1, ?_⟩
  have hG_abs : G.natAbs ≤ 2 ^ pSub := hclamp.2.1
  omega

/-- Accuracy of returning `0` when `(B + 2) * denY ≤ numY` (`y_hat ≥ B + 2`, so `y ≥ B + 1 ≥ pSub`
and `exp(-y) ≤ 2^(-pSub)`). -/
theorem sincGaussian_clamped_zero_spec (pSub B numY denY : ℕ) (α t y : ℝ)
    (hB : B = pSub + 2) (hdenY : 0 < denY)
    (hsg : sincGaussian α t = normSinc t * Real.exp (-y))
    (hy_diff : |(numY : ℝ) / (denY : ℝ) - y| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)))
    (hclamped : ((B + 2 : ℕ) : ℤ) * (denY : ℤ) ≤ (numY : ℤ)) :
    |(((0 : ℤ) : ℝ) / (2 : ℝ) ^ pSub) - sincGaussian α t| ≤ (2 : ℝ) ^ (-(pSub : ℤ)) ∧
    (0 : ℤ).natAbs ≤ 2 ^ pSub + 1 := by
  have hdenY_r : (0 : ℝ) < (denY : ℝ) := Nat.cast_pos.mpr hdenY
  have hclamped_r : ((B + 2 : ℕ) : ℝ) * (denY : ℝ) ≤ (numY : ℝ) := by exact_mod_cast hclamped
  have hy_hat_ge : ((B + 2 : ℕ) : ℝ) ≤ (numY : ℝ) / (denY : ℝ) :=
    (le_div_iff₀ hdenY_r).mpr hclamped_r
  have hB_pow_le1 : (2 : ℝ) ^ (-(B : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hy_ge_pSub : (pSub : ℝ) ≤ y := by
    have hd := (abs_le.mp hy_diff).2
    have hB_r : ((B + 2 : ℕ) : ℝ) = (pSub : ℝ) + 4 := by subst hB; push_cast; ring
    linarith
  have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpow_le_exp : (2 : ℝ) ^ pSub ≤ Real.exp y := by
    calc (2 : ℝ) ^ pSub
        ≤ (Real.exp 1) ^ pSub := pow_le_pow_left₀ (by norm_num) h2_le_exp1 pSub
      _ = Real.exp (pSub : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ Real.exp y := Real.exp_le_exp.mpr hy_ge_pSub
  have hexp_neg_y : Real.exp (-y) ≤ (2 : ℝ) ^ (-(pSub : ℤ)) := by
    rw [Real.exp_neg, zpow_neg, zpow_natCast]
    exact inv_anti₀ (by positivity) hpow_le_exp
  refine ⟨?_, by simp⟩
  rw [Int.cast_zero, zero_div, zero_sub, abs_neg, hsg, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |normSinc t| * Real.exp (-y)
      ≤ 1 * (2 : ℝ) ^ (-(pSub : ℤ)) :=
        mul_le_mul (abs_realSinc_le_one t) hexp_neg_y (Real.exp_pos _).le zero_le_one
    _ = (2 : ℝ) ^ (-(pSub : ℤ)) := one_mul _

/-- Combined accuracy, call-site width soundness, and sum-magnitude bound for the
recurrence-based `sinc` Taylor series evaluator. -/
theorem sinc_recurrence_spec_and_widths
    (Bint M_θ D w N numTheta denTheta : ℕ)
    (hden : 0 < denTheta)
    (hθ_le : (numTheta : ℝ) / (denTheta : ℝ) ≤ (M_θ : ℝ))
    (hnum_sq : ((numTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hden_sq : ((denTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hw : Bint + 2 * M_θ + 4 * N + D + 9 ≤ w) :
    let seriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
      (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N
    |(seriesRes.1.2 : ℝ) / (2 : ℝ) ^ Bint - sincTaylorSum N ((numTheta : ℝ) / (denTheta : ℝ))| ≤
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (2 * M_θ) * (2 : ℝ) ^ (-(Bint : ℤ)) ∧
    RecurrenceCallSitesWidthSound w ((2 ^ Bint : ℕ) : ℤ)
      (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N ∧
    |(seriesRes.1.2 : ℝ)| ≤ (2 : ℝ) ^ (Bint + 2 * M_θ + 2 * N + 3) := by
  intro seriesRes
  set θ_hat : ℝ := (numTheta : ℝ) / (denTheta : ℝ)
  have hθ_nonneg : 0 ≤ θ_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set exactA : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * θ_hat ^ (2 * k) / ((2 * k + 1).factorial : ℝ)
  have hden_sq_pos : 0 < denTheta ^ 2 := pow_pos hden 2
  have hsf_pos : ∀ k, 0 < (2 * k + 2) * (2 * k + 3) := fun k => by positivity
  have ha0 : |(((2 ^ Bint : ℕ) : ℤ) : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 0 := by
    dsimp [exactA]
    push_cast
    norm_num
  have hrec : ∀ k, exactA (k + 1) =
      exactA k * (((-((numTheta ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) * ((1 : ℕ) : ℝ)) /
        ((((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) * ((denTheta ^ 2 : ℕ) : ℝ)) := by
    intro k
    dsimp [exactA, θ_hat]
    have hfact : ((2 * (k + 1) + 1).factorial : ℝ) =
        (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) * ((2 * k + 1).factorial : ℝ) := by
      have h2k : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by omega
      rw [h2k, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hpow : θ_hat ^ (2 * (k + 1)) = θ_hat ^ (2 * k) * ((numTheta : ℝ) ^ 2 / (denTheta : ℝ) ^ 2) := by
      have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h2k, pow_add, div_pow (numTheta : ℝ) (denTheta : ℝ) 2]
    have hden_ne : (denTheta : ℝ) ≠ 0 := (Nat.cast_pos.mpr hden).ne'
    have hfact_ne : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
    have hsf_ne : (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [pow_succ (-1 : ℝ), hpow, hfact]
    push_cast
    field_simp [hden_ne, hfact_ne, hsf_ne]
    ring
  have hA_bound : ∀ k, |exactA k| ≤ (2 : ℝ) ^ (2 * M_θ) := by
    intro k
    dsimp [exactA]
    rw [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (pow_nonneg hθ_nonneg _),
        abs_of_pos (by positivity)]
    have hfact_le : ((2 * k).factorial : ℝ) ≤ ((2 * k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    calc θ_hat ^ (2 * k) / ((2 * k + 1).factorial : ℝ)
        ≤ θ_hat ^ (2 * k) / ((2 * k).factorial : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hfact_le
      _ ≤ (M_θ : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ_nonneg hθ_le _) (by positivity)
      _ ≤ (2 : ℝ) ^ (2 * M_θ) := pow_div_factorial_le_two_pow_linear M_θ (2 * k)
  have hprod_bound : ∀ i k, i ≤ k →
      prodStepRatio (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
        (fun _ => 1) (fun j => (2 * j + 2) * (2 * j + 3)) i k ≤ (2 : ℝ) ^ (2 * M_θ) := by
    intro i k hik
    refine prodStepRatio_le_two_pow_of_quadratic_step _ _ _ _ M_θ i k hden_sq_pos hsf_pos ?_ ?_
    · rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      rw [← div_pow]
      exact pow_le_pow_left₀ hθ_nonneg hθ_le 2
    · intro j
      push_cast
      nlinarith
  have herr := abs_runRecurrenceSeriesCosted_div_sub_sum_le Bint 0 M_θ w
    ((2 ^ Bint : ℕ) : ℤ) (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hprod_bound
  rw [pow_zero, mul_one] at herr
  have hw_sound := recurrenceCallSitesWidthSound_of_bounds Bint 0 M_θ D w
    ((2 ^ Bint : ℕ) : ℤ) (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hA_bound hprod_bound
    (by rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; exact hnum_sq)
    hden_sq
    (fun k hk => by rw [Nat.cast_one]; exact one_le_pow₀ (by norm_num))
    (fun k hk => (step_quad_le_two_pow N k hk).2.2.2.2.1)
    (by omega)
  exact ⟨herr, hw_sound.1, hw_sound.2⟩

/-- Combined accuracy, call-site width soundness, and sum-magnitude bound for the
recurrence-based `exp(-y)` Taylor series evaluator. -/
theorem expNeg_recurrence_spec_and_widths
    (Bint M_y D w N numY denY : ℕ)
    (hden : 0 < denY)
    (hy_le : (numY : ℝ) / (denY : ℝ) ≤ (M_y : ℝ))
    (hnum : (numY : ℝ) ≤ (2 : ℝ) ^ D)
    (hden_le : (denY : ℝ) ≤ (2 : ℝ) ^ D)
    (hw : Bint + 2 * M_y + 4 * N + D + 9 ≤ w) :
    let seriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
      (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N
    |(seriesRes.1.2 : ℝ) / (2 : ℝ) ^ Bint - expNegTaylorSum N ((numY : ℝ) / (denY : ℝ))| ≤
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (2 * M_y) * (2 : ℝ) ^ (-(Bint : ℤ)) ∧
    RecurrenceCallSitesWidthSound w ((2 ^ Bint : ℕ) : ℤ)
      (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N ∧
    |(seriesRes.1.2 : ℝ)| ≤ (2 : ℝ) ^ (Bint + 2 * M_y + 2 * N + 3) := by
  intro seriesRes
  set y_hat : ℝ := (numY : ℝ) / (denY : ℝ)
  have hy_nonneg : 0 ≤ y_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set exactA : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * y_hat ^ k / (k.factorial : ℝ)
  have hsf_pos : ∀ k, 0 < k + 1 := fun k => by omega
  have ha0 : |(((2 ^ Bint : ℕ) : ℤ) : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 0 := by
    dsimp [exactA]
    push_cast
    norm_num
  have hrec : ∀ k, exactA (k + 1) =
      exactA k * (((-(numY : ℤ) : ℤ) : ℝ) * ((1 : ℕ) : ℝ)) /
        (((k + 1 : ℕ) : ℝ) * (denY : ℝ)) := by
    intro k
    dsimp only [exactA]
    have hpow : y_hat ^ (k + 1) = y_hat ^ k * ((numY : ℝ) / (denY : ℝ)) := pow_succ y_hat k
    have hden_ne : (denY : ℝ) ≠ 0 := (Nat.cast_pos.mpr hden).ne'
    have hfact_ne : (k.factorial : ℝ) ≠ 0 := by positivity
    have hsf_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [pow_succ (-1 : ℝ), hpow, Nat.factorial_succ]
    push_cast
    field_simp [hden_ne, hfact_ne, hsf_ne]
  have hA_bound : ∀ k, |exactA k| ≤ (2 : ℝ) ^ (2 * M_y) := by
    intro k
    dsimp [exactA]
    rw [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (pow_nonneg hy_nonneg _),
        abs_of_pos (by positivity)]
    exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hy_nonneg hy_le _) (by positivity)).trans
      (pow_div_factorial_le_two_pow_linear M_y k)
  have hprod_bound : ∀ i k, i ≤ k →
      prodStepRatio (-(numY : ℤ)) denY
        (fun _ => 1) (fun j => j + 1) i k ≤ (2 : ℝ) ^ (2 * M_y) := by
    intro i k hik
    refine prodStepRatio_le_two_pow_of_linear_step _ _ _ _ M_y i k hden hsf_pos ?_ ?_
    · rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact hy_le
    · intro j
      push_cast
      linarith
  have herr := abs_runRecurrenceSeriesCosted_div_sub_sum_le Bint 0 M_y w
    ((2 ^ Bint : ℕ) : ℤ) (-(numY : ℤ)) denY
    (fun _ => 1) (fun k => k + 1) exactA N
    hden hsf_pos ha0 hrec hprod_bound
  rw [pow_zero, mul_one] at herr
  have hw_sound := recurrenceCallSitesWidthSound_of_bounds Bint 0 M_y D w
    ((2 ^ Bint : ℕ) : ℤ) (-(numY : ℤ)) denY
    (fun _ => 1) (fun k => k + 1) exactA N
    hden hsf_pos ha0 hrec hA_bound hprod_bound
    (by rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; exact hnum)
    hden_le
    (fun k hk => by rw [Nat.cast_one]; exact one_le_pow₀ (by norm_num))
    (fun k hk => by exact_mod_cast (step_quad_le_two_pow N k hk).1)
    (by omega)
  exact ⟨herr, hw_sound.1, hw_sound.2⟩

/-- Computable evaluator for `normSinc t` from rational approximation `θ_hat = numTheta / denTheta`
of `θ = π * |t|`, clamped to `[-2^B, 2^B]`.
All big-integer multiplications (`numTheta^2`, `denTheta^2`, and the series recurrence)
go through `costedMulInt w` and `costedDivRoundRatInt w`. -/
def computableSincRationalClamp (B N Bint w numTheta denTheta : ℕ) : BitCostM ℤ :=
  let numThetaSqRes := costedMulInt w (numTheta : ℤ) (numTheta : ℤ)
  let negNumThetaSqRes := costedNegInt0 numThetaSqRes.1
  let negNumThetaSq : ℤ := negNumThetaSqRes.1
  let denThetaSqRes := costedMulInt w (denTheta : ℤ) (denTheta : ℤ)
  let denThetaSq : ℕ := denThetaSqRes.1.toNat
  let sincSeriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N
  let sincShiftRes := costedShiftLeftInt w sincSeriesRes.1.2 B
  let sincRawRes := costedDivRoundRatInt w
    sincShiftRes.1
    ((2 ^ Bint : ℕ) : ℤ)
  let sincClampRes := costedSymmClampPow2Int w B sincRawRes.1
  (sincClampRes.1,
    numThetaSqRes.2 + denThetaSqRes.2 + sincSeriesRes.2 + sincShiftRes.2 + sincRawRes.2 + sincClampRes.2)

theorem computableSincRationalClamp_snd (B N Bint w numTheta denTheta : ℕ) :
    (computableSincRationalClamp B N Bint w numTheta denTheta).2 =
      computableMulBitCost w + computableMulBitCost w +
      (N * (6 * computableMulBitCost w + 3 * addBitCost w)) +
      addBitCost w + (2 * computableMulBitCost w + 2 * addBitCost w) + 2 * addBitCost w := by
  dsimp only [computableSincRationalClamp, costedShiftLeftInt, costedMulInt, costedDivRoundRatInt, costedClampInt]
  rw [runRecurrenceSeriesCosted_snd]

theorem computableSincRationalClamp_spec
    (B M_θ N Bint w numTheta denTheta : ℕ) (t : ℝ)
    (hN_ge1 : 1 ≤ N) (hMθ_ge1 : 1 ≤ M_θ) (hden : 0 < denTheta)
    (h2N : 4 * M_θ + (B + 3) ≤ 2 * N)
    (hBint : B + 2 * N + 2 * M_θ + 4 ≤ Bint)
    (hθ_le : Real.pi * |t| ≤ (M_θ : ℝ))
    (hθ_hat_le : (numTheta : ℝ) / (denTheta : ℝ) ≤ (M_θ : ℝ))
    (hθ_arg : (N : ℝ) * (2 : ℝ) ^ (2 * M_θ) *
      |(numTheta : ℝ) / (denTheta : ℝ) - Real.pi * (|t|)| ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ))) :
    let sincInt := (computableSincRationalClamp B N Bint w numTheta denTheta).1
    |(sincInt : ℝ) / (2 : ℝ) ^ B - normSinc t| ≤ (2 : ℝ) ^ (-(B : ℤ)) ∧
    |(sincInt : ℝ) / (2 : ℝ) ^ B| ≤ 1 := by
  dsimp only [computableSincRationalClamp, costedMulInt, costedClampInt]
  have hnum_sq_eq : ((numTheta : ℤ) * (numTheta : ℤ)) = ((numTheta ^ 2 : ℕ) : ℤ) := by push_cast; ring
  have hden_sq_eq : ((denTheta : ℤ) * (denTheta : ℤ)).toNat = denTheta ^ 2 := by
    rw [← Nat.cast_mul, Int.toNat_natCast, sq]
  rw [hnum_sq_eq, hden_sq_eq]
  set θ : ℝ := Real.pi * |t|
  set θ_hat : ℝ := (numTheta : ℝ) / (denTheta : ℝ)
  have hθ_nonneg : 0 ≤ θ := mul_nonneg Real.pi_pos.le (abs_nonneg t)
  have hθ_hat_nonneg : 0 ≤ θ_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hB_zpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(B : ℤ)) := by positivity
  have hB3_pow : (2 : ℝ) ^ (-(B + 3 : ℤ)) = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have : (-(B + 3 : ℤ)) = (-3 : ℤ) + (-(B : ℤ)) := by omega
    rw [this, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hN_Bint := recurrence_rounding_error_le_eighth B N 0 M_θ Bint (by omega)
  set D0 := numTheta ^ 2 + denTheta ^ 2
  have hnum_sq_D0 : ((numTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D0 := by
    exact_mod_cast (Nat.le_add_right _ _).trans Nat.lt_two_pow_self.le
  have hden_sq_D0 : ((denTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D0 := by
    exact_mod_cast (Nat.le_add_left _ _).trans Nat.lt_two_pow_self.le
  have hsinc_rec := sinc_recurrence_spec_and_widths Bint M_θ D0
    (max w (Bint + 2 * M_θ + 4 * N + D0 + 9)) N numTheta denTheta
    hden hθ_hat_le hnum_sq_D0 hden_sq_D0 (le_max_right _ _)
  have hfst_eq :
      (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
        (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
        (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N).1.2 =
      (runRecurrenceSeriesCosted (max w (Bint + 2 * M_θ + 4 * N + D0 + 9)) ((2 ^ Bint : ℕ) : ℤ)
        (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
        (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N).1.2 := by
    rw [runRecurrenceSeriesCosted_fst_snd_eq_sum, runRecurrenceSeriesCosted_fst_snd_eq_sum]
  have hsinc_sum_err :
      |((runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
          (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
          (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N).1.2 : ℝ) / (2 : ℝ) ^ Bint -
        sincTaylorSum N θ_hat| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [hfst_eq]
    exact hsinc_rec.1.trans (by simpa using hN_Bint)
  have hsinc_arg_err :
      |sincTaylorSum N θ_hat - sincTaylorSum N θ| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) :=
    (abs_sincTaylorSum_sub_le N M_θ hMθ_ge1 θ_hat θ hθ_hat_nonneg hθ_hat_le hθ_nonneg hθ_le).trans hθ_arg
  have hsinc_rem : |sincTaylorSum N θ - normSinc t| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [abs_sub_comm, ← hB3_pow]
    exact (abs_normSinc_sub_sincTaylorSum_le N hN_ge1 t).trans
      (pow_div_factorial_le_two_zpow_neg M_θ (B + 3) (2 * N) h2N θ hθ_nonneg hθ_le)
  dsimp only [costedDivRoundRatInt]
  set sincSumVal := (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2)
    (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N).1.2
  generalize hDenInt : ((2 ^ Bint : ℕ) : ℤ) = denInt
  have hdenInt_pos : 0 < denInt := by subst hDenInt; positivity
  have hsinc_q := abs_divRoundRatInt_mul_two_pow_div_sub_le B sincSumVal denInt hdenInt_pos
  generalize hSincRaw : divRoundRatInt (sincSumVal * ((2 ^ B : ℕ) : ℤ)) denInt = sincRawInt at hsinc_q ⊢
  have hcast_sinc : (sincSumVal : ℝ) / (denInt : ℝ) = (sincSumVal : ℝ) / (2 : ℝ) ^ Bint := by
    subst hDenInt; push_cast; rfl
  rw [hcast_sinc] at hsinc_q
  have hsinc_raw_err : |(sincRawInt : ℝ) / (2 : ℝ) ^ B - normSinc t| ≤ (2 : ℝ) ^ (-(B : ℤ)) :=
    abs_sub_le_of_four_step_approx _ _ _ _ _ ((2 : ℝ) ^ (-(B : ℤ))) hB_zpow
      hsinc_q hsinc_sum_err hsinc_arg_err hsinc_rem
  have hsinc_clamp := abs_clampInt_symm_scaled_sub_le B sincRawInt (normSinc t) ((2 : ℝ) ^ (-(B : ℤ)))
    (abs_realSinc_le_one t) hsinc_raw_err
  exact ⟨hsinc_clamp.1, hsinc_clamp.2.2⟩

/-- Computable evaluator for `Real.exp (-y)` from rational approximation `y_hat = numY / denY`
of `y ≥ 0`, clamped to `[-2^B, 2^B]`.
Uses the linear-step recurrence `(k + 1) * denY` via `runRecurrenceSeriesCosted`. -/
def computableExpNegRationalClamp (B N Bint w numY denY : ℕ) : BitCostM ℤ :=
  let negNumYRes := costedNegInt0 (numY : ℤ)
  let expSeriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    negNumYRes.1 denY (fun _ => 1) (fun k => k + 1) N
  let expShiftRes := costedShiftLeftInt w expSeriesRes.1.2 B
  let expRawRes := costedDivRoundRatInt w
    expShiftRes.1
    ((2 ^ Bint : ℕ) : ℤ)
  let expClampRes := costedSymmClampPow2Int w B expRawRes.1
  (expClampRes.1, expSeriesRes.2 + expShiftRes.2 + expRawRes.2 + expClampRes.2)

theorem computableExpNegRationalClamp_snd (B N Bint w numY denY : ℕ) :
    (computableExpNegRationalClamp B N Bint w numY denY).2 =
      (N * (6 * computableMulBitCost w + 3 * addBitCost w)) +
      addBitCost w + (2 * computableMulBitCost w + 2 * addBitCost w) + 2 * addBitCost w := by
  dsimp only [computableExpNegRationalClamp, costedShiftLeftInt, costedDivRoundRatInt, costedClampInt]
  rw [runRecurrenceSeriesCosted_snd]

theorem computableExpNegRationalClamp_spec
    (B M_y N Bint w numY denY : ℕ) (y : ℝ)
    (hden : 0 < denY) (hy_nonneg : 0 ≤ y)
    (hN : 4 * M_y + (B + 3) ≤ N)
    (hBint : B + 2 * N + 2 * M_y + 4 ≤ Bint)
    (hy_hat_le : (numY : ℝ) / (denY : ℝ) ≤ (M_y : ℝ))
    (hy_diff : |(numY : ℝ) / (denY : ℝ) - y| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ))) :
    let expInt := (computableExpNegRationalClamp B N Bint w numY denY).1
    |(expInt : ℝ) / (2 : ℝ) ^ B - Real.exp (-y)| ≤ (2 : ℝ) ^ (-(B : ℤ)) := by
  dsimp only [computableExpNegRationalClamp, costedClampInt]
  set y_hat : ℝ := (numY : ℝ) / (denY : ℝ)
  have hy_hat_nonneg : 0 ≤ y_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hB_zpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(B : ℤ)) := by positivity
  have hB3_pow : (2 : ℝ) ^ (-(B + 3 : ℤ)) = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have : (-(B + 3 : ℤ)) = (-3 : ℤ) + (-(B : ℤ)) := by omega
    rw [this, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hN_Bint := recurrence_rounding_error_le_eighth B N 0 M_y Bint (by omega)
  set D0 := numY + denY
  have hnum_D0 : (numY : ℝ) ≤ (2 : ℝ) ^ D0 := by
    exact_mod_cast (Nat.le_add_right _ _).trans Nat.lt_two_pow_self.le
  have hden_D0 : (denY : ℝ) ≤ (2 : ℝ) ^ D0 := by
    exact_mod_cast (Nat.le_add_left _ _).trans Nat.lt_two_pow_self.le
  have hexp_rec := expNeg_recurrence_spec_and_widths Bint M_y D0
    (max w (Bint + 2 * M_y + 4 * N + D0 + 9)) N numY denY
    hden hy_hat_le hnum_D0 hden_D0 (le_max_right _ _)
  have hfst_eq :
      (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
        (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N).1.2 =
      (runRecurrenceSeriesCosted (max w (Bint + 2 * M_y + 4 * N + D0 + 9)) ((2 ^ Bint : ℕ) : ℤ)
        (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N).1.2 := by
    rw [runRecurrenceSeriesCosted_fst_snd_eq_sum, runRecurrenceSeriesCosted_fst_snd_eq_sum]
  have hexp_sum_err :
      |((runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
          (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N).1.2 : ℝ) / (2 : ℝ) ^ Bint -
        expNegTaylorSum N y_hat| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [hfst_eq]
    exact hexp_rec.1.trans (by simpa using hN_Bint)
  have hexp_rem : |expNegTaylorSum N y_hat - Real.exp (-y_hat)| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    rw [abs_sub_comm, ← hB3_pow]
    exact (abs_expNegTaylorRem_le N y_hat hy_hat_nonneg).trans
      (pow_div_factorial_le_two_zpow_neg M_y (B + 3) N hN y_hat hy_hat_nonneg hy_hat_le)
  dsimp only [costedDivRoundRatInt]
  set expSumVal := (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N).1.2
  generalize hDenInt : ((2 ^ Bint : ℕ) : ℤ) = denInt
  have hdenInt_pos : 0 < denInt := by subst hDenInt; positivity
  have hexp_q := abs_divRoundRatInt_mul_two_pow_div_sub_le B expSumVal denInt hdenInt_pos
  generalize hExpRaw : divRoundRatInt (expSumVal * ((2 ^ B : ℕ) : ℤ)) denInt = expRawInt at hexp_q ⊢
  have hcast_exp : (expSumVal : ℝ) / (denInt : ℝ) = (expSumVal : ℝ) / (2 : ℝ) ^ Bint := by
    subst hDenInt; push_cast; rfl
  rw [hcast_exp] at hexp_q
  have hexp_raw_err : |(expRawInt : ℝ) / (2 : ℝ) ^ B - Real.exp (-y)| ≤ (2 : ℝ) ^ (-(B : ℤ)) :=
    abs_sub_le_of_four_step_approx _ _ _ _ _ ((2 : ℝ) ^ (-(B : ℤ))) hB_zpow
      hexp_q hexp_sum_err hexp_rem
      ((abs_exp_neg_sub_le y_hat y hy_hat_nonneg hy_nonneg).trans hy_diff)
  have hexp_le1 : |Real.exp (-y)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  exact (abs_clampInt_symm_scaled_sub_le B expRawInt (Real.exp (-y)) ((2 : ℝ) ^ (-(B : ℤ)))
    hexp_le1 hexp_raw_err).1

/-- Pure real-arithmetic bounds on the rational approximations `θ_hat` and `y_hat`
for `sincGaussian (alphaSchedule p_work) t`. -/
theorem sincGaussian_theta_and_y_bounds
    (p_work pSub B M_θ N B_c t1 piNat log2Nat numT : ℕ) (t : ℝ)
    (hM_θ : M_θ = 4 * (pSub + 1))
    (hB_c : B + N + 3 * M_θ + 6 ≤ B_c)
    (hp_work : 0 < p_work) (ht1 : 0 < t1)
    (ht_abs : |t| = (numT : ℝ) / (t1 : ℝ))
    (ht_le : |t| ≤ (pSub + 1 : ℝ))
    (hpi_err : |(piNat : ℝ) / (2 : ℝ) ^ B_c - Real.pi| ≤ (2 : ℝ) ^ (-(B_c : ℤ)))
    (hlog2_err : |(log2Nat : ℝ) / (2 : ℝ) ^ B_c - Real.log 2| ≤ (2 : ℝ) ^ (-(B_c : ℤ)))
    (hlog2_half : (1 / 2 : ℝ) ≤ (log2Nat : ℝ) / (2 : ℝ) ^ B_c)
    (hlog2_pos : 0 < log2Nat) :
    let numTheta : ℕ := piNat * numT
    let denTheta : ℕ := t1 * 2 ^ B_c
    let numY : ℕ := numTheta ^ 2
    let denY : ℕ := 4 * p_work * log2Nat * t1 ^ 2 * 2 ^ B_c
    let y : ℝ := (Real.pi / (alphaSchedule p_work) ^ 2) * t ^ 2
    Real.pi * |t| ≤ (M_θ : ℝ) ∧
    (numTheta : ℝ) / (denTheta : ℝ) ≤ (M_θ : ℝ) ∧
    (N : ℝ) * (2 : ℝ) ^ (2 * M_θ) *
      |(numTheta : ℝ) / (denTheta : ℝ) - Real.pi * (|t|)| ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) ∧
    |(numY : ℝ) / (denY : ℝ) - y| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
  intro numTheta denTheta numY denY y
  set θ : ℝ := Real.pi * |t|
  set θ_hat : ℝ := (numTheta : ℝ) / (denTheta : ℝ)
  have hθ_hat_eq : θ_hat = ((piNat : ℝ) / (2 : ℝ) ^ B_c) * |t| := by
    rw [ht_abs]
    dsimp [θ_hat, numTheta, denTheta]
    push_cast
    rw [div_mul_div_comm, mul_comm (t1 : ℝ)]
  have hθ_nonneg : 0 ≤ θ := mul_nonneg Real.pi_pos.le (abs_nonneg t)
  have hθ_hat_nonneg : 0 ≤ θ_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hBc_le_half : (2 : ℝ) ^ (-(B_c : ℤ)) ≤ 1 / 2 := by
    calc (2 : ℝ) ^ (-(B_c : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = 1 / 2 := by norm_num
  have hpi_hat_le4 : (piNat : ℝ) / (2 : ℝ) ^ B_c ≤ 4 := by
    have := (abs_le.mp hpi_err).2
    linarith
  have hMθ_r : 4 * (pSub + 1 : ℝ) = (M_θ : ℝ) := by rw [hM_θ]; push_cast; ring
  have hθ_le : θ ≤ (M_θ : ℝ) := by
    dsimp [θ]
    nlinarith [abs_nonneg t]
  have hθ_hat_le : θ_hat ≤ (M_θ : ℝ) := by
    rw [hθ_hat_eq]
    have hpi_hat_nonneg : 0 ≤ (piNat : ℝ) / (2 : ℝ) ^ B_c :=
      div_nonneg (Nat.cast_nonneg _) (by positivity)
    nlinarith [abs_nonneg t]
  have ht_le_Mθ : |t| ≤ (M_θ : ℝ) := by linarith
  have hθ_diff : |θ_hat - θ| ≤ (M_θ : ℝ) * (2 : ℝ) ^ (-(B_c : ℤ)) := by
    have hsub : θ_hat - θ = ((piNat : ℝ) / (2 : ℝ) ^ B_c - Real.pi) * |t| := by
      rw [hθ_hat_eq]; dsimp [θ]; ring
    rw [hsub, abs_mul, abs_of_nonneg (abs_nonneg t), mul_comm]
    exact mul_le_mul ht_le_Mθ hpi_err (abs_nonneg _) (Nat.cast_nonneg _)
  have hperturb := sinc_and_exp_arg_perturb_le_eighth B N M_θ B_c hB_c
  have hθ_arg :
      (N : ℝ) * (2 : ℝ) ^ (2 * M_θ) * |θ_hat - θ| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) :=
    (mul_le_mul_of_nonneg_left hθ_diff (by positivity)).trans hperturb.1
  set L : ℝ := 4 * Real.log 2
  set L_hat : ℝ := 4 * ((log2Nat : ℝ) / (2 : ℝ) ^ B_c)
  set y_hat : ℝ := (numY : ℝ) / (denY : ℝ)
  have hp_work_r : (1 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp_work
  have hp_work_pos : (0 : ℝ) < (p_work : ℝ) := Nat.cast_pos.mpr hp_work
  have hlog2_pos_r : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL_ge2 : 2 ≤ L := by
    dsimp [L]
    have := Real.log_two_gt_d9
    linarith
  have hL_hat_ge2 : 2 ≤ L_hat := by
    dsimp [L_hat]
    linarith
  have hy_eq : y = (1 / (p_work : ℝ)) * (θ ^ 2 / L) := by
    dsimp [y, θ, L]
    have hpi_sq := pi_mul_alphaSchedule_sq p_work hp_work
    have hα_pos := alphaSchedule_pos p_work hp_work
    have hpi_pos := Real.pi_pos
    rw [mul_pow, sq_abs]
    calc (Real.pi / (alphaSchedule p_work) ^ 2) * t ^ 2
        = (Real.pi ^ 2 * t ^ 2) / (Real.pi * (alphaSchedule p_work) ^ 2) := by
          field_simp [hpi_pos.ne', hα_pos.ne']
      _ = (Real.pi ^ 2 * t ^ 2) / (4 * (p_work : ℝ) * Real.log 2) := by rw [hpi_sq]
      _ = (1 / (p_work : ℝ)) * ((Real.pi ^ 2 * t ^ 2) / (4 * Real.log 2)) := by
          field_simp [hp_work_pos.ne', hlog2_pos_r.ne']
  have hy_hat_eq : y_hat = (1 / (p_work : ℝ)) * (θ_hat ^ 2 / L_hat) := by
    dsimp [y_hat, numY, denY, θ_hat, denTheta, L_hat]
    push_cast
    have ht1_r : (t1 : ℝ) ≠ 0 := (Nat.cast_pos.mpr ht1).ne'
    have hlog2_r : (log2Nat : ℝ) ≠ 0 := (Nat.cast_pos.mpr hlog2_pos).ne'
    have hpow_r : (2 : ℝ) ^ B_c ≠ 0 := by positivity
    field_simp [hp_work_pos.ne', ht1_r, hlog2_r, hpow_r]
  have h1_pwork : 1 / (p_work : ℝ) ≤ 1 := div_le_one_of_le₀ hp_work_r hp_work_pos.le
  have hy_diff : |y_hat - y| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have hsub : y_hat - y = (1 / (p_work : ℝ)) * (θ_hat ^ 2 / L_hat - θ ^ 2 / L) := by
      rw [hy_hat_eq, hy_eq, ← mul_sub]
    have hL_diff : |L_hat - L| ≤ 4 * (2 : ℝ) ^ (-(B_c : ℤ)) := by
      have : L_hat - L = 4 * ((log2Nat : ℝ) / (2 : ℝ) ^ B_c - Real.log 2) := by
        dsimp [L_hat, L]; ring
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact mul_le_mul_of_nonneg_left hlog2_err (by norm_num)
    have hquot := abs_sq_div_sub_sq_div_le θ_hat θ L_hat L (M_θ : ℝ)
      hθ_hat_nonneg hθ_hat_le hθ_nonneg hθ_le hL_hat_ge2 hL_ge2
    have h1_nonneg : 0 ≤ 1 / (p_work : ℝ) := div_nonneg zero_le_one hp_work_pos.le
    rw [hsub, abs_mul, abs_of_nonneg h1_nonneg]
    calc (1 / (p_work : ℝ)) * |θ_hat ^ 2 / L_hat - θ ^ 2 / L|
        ≤ 1 * ((M_θ : ℝ) * |θ_hat - θ| + (M_θ : ℝ) ^ 2 * |L_hat - L|) :=
          mul_le_mul h1_pwork hquot (abs_nonneg _) zero_le_one
      _ ≤ (M_θ : ℝ) * ((M_θ : ℝ) * (2 : ℝ) ^ (-(B_c : ℤ))) +
            (M_θ : ℝ) ^ 2 * (4 * (2 : ℝ) ^ (-(B_c : ℤ))) := by
          rw [one_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hθ_diff (Nat.cast_nonneg _))
            (mul_le_mul_of_nonneg_left hL_diff (sq_nonneg _))
      _ = 5 * (M_θ : ℝ) ^ 2 * (2 : ℝ) ^ (-(B_c : ℤ)) := by ring
      _ ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := hperturb.2
  exact ⟨hθ_le, hθ_hat_le, hθ_arg, hy_diff⟩

/-- Inner computable evaluator for `sincGaussian (alphaSchedule p_work) t`
taking precomputed `piNat`, `log2Nat`, and `numT` as free `ℕ` arguments.
All multi-precision multiplications go through `costedMulInt w`, and large `y_hat ≥ B + 2`
is clamped directly to `0` (`exp(-y) ≤ 2^(-pSub)`). -/
def computableSincGaussianTapInner
    (p_work pSub B N B_c Bint w t1 piNat log2Nat numT : ℕ) : BitCostM ℤ :=
  let numThetaRes := costedMulInt w (piNat : ℤ) (numT : ℤ)
  let numTheta : ℕ := numThetaRes.1.toNat
  let denThetaRes := costedShiftLeftNat w t1 B_c
  let denTheta : ℕ := denThetaRes.1
  let numYRes := costedMulInt w (numTheta : ℤ) (numTheta : ℤ)
  let numY : ℕ := numYRes.1.toNat
  let t1SqRes := costedMulInt w (t1 : ℤ) (t1 : ℤ)
  let pLogRes := costedMulInt w ((4 * p_work : ℕ) : ℤ) (log2Nat : ℤ)
  let denYBaseRes := costedMulInt w pLogRes.1 t1SqRes.1
  let denYRes := costedShiftLeftNat w denYBaseRes.1.toNat B_c
  let denY : ℕ := denYRes.1
  let thresholdRes := costedMulInt w ((B + 2 : ℕ) : ℤ) (denY : ℤ)
  let setupCost : ℕ :=
    numThetaRes.2 + denThetaRes.2 + numYRes.2 + t1SqRes.2 +
    pLogRes.2 + denYBaseRes.2 + denYRes.2 + thresholdRes.2 + addBitCost w
  if thresholdRes.1 ≤ (numY : ℤ) then
    (0, setupCost)
  else
    let sincClampRes := computableSincRationalClamp B N Bint w numTheta denTheta
    let expClampRes := computableExpNegRationalClamp B N Bint w numY denY
    let prodRes := costedMulInt w sincClampRes.1 expClampRes.1
    let prodShiftRes := costedShiftLeftInt w prodRes.1 pSub
    let prodRoundRes := costedDivRoundRatInt w
      prodShiftRes.1
      ((2 ^ (2 * B) : ℕ) : ℤ)
    let finalClampRes := costedSymmClampPow2Int w pSub prodRoundRes.1
    (finalClampRes.1,
      setupCost + sincClampRes.2 + expClampRes.2 + prodRes.2 +
      prodShiftRes.2 + prodRoundRes.2 + finalClampRes.2)

/-- Core computable evaluator for `sincGaussian (alphaSchedule p_work) t`
parameterized by explicit precision/truncation parameters `(B N B_c Bint w : ℕ)`. -/
def computableSincGaussianTapCore
    (p_work pSub B N B_c Bint w t1 j1 s : ℕ) : BitCostM ℤ :=
  let piRes := computablePiScaledWithCost B_c
  let log2Res := computableLog2ScaledWithCost B_c
  let diffSRes := costedSubNatToInt0 s pSub
  let diffS : ℤ := diffSRes.1
  let prodTRes := costedMulInt w diffS (t1 : ℤ)
  let numTRes := costedSubNatAbsInt0 prodTRes.1 j1
  let numT : ℕ := numTRes.1
  let innerRes := computableSincGaussianTapInner p_work pSub B N B_c Bint w t1
    piRes.1.toNat log2Res.1.toNat numT
  (innerRes.1, piRes.2 + log2Res.2 + prodTRes.2 + addBitCost w + innerRes.2)

/-- Computable fixed-point evaluator for the Sinc-Gaussian filter tap
`sincGaussian (alphaSchedule p_work) (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))`
at scale `2^pSub`. -/
def computableSincGaussianTapWithProgramCost (p_work pSub t1 j1 s : ℕ) : BitCostM ℤ :=
  let B := pSub + 2
  let M_θ := 4 * (pSub + 1)
  let N := 4 * M_θ + B + 4
  let B_c := B + N + 3 * M_θ + 6
  let Bint := B + 2 * N + 2 * M_θ + 6
  let w := Bint + 4 * N + 2 * M_θ + 2 * B_c + 2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 40
  computableSincGaussianTapCore p_work pSub B N B_c Bint w t1 j1 s

/-- Helper identities for the costed integer setup in `computableSincGaussianTapInner`. -/
theorem sincGaussian_inner_setup_identities
    (p_work B_c t1 piNat log2Nat numT : ℕ) :
    ((piNat : ℤ) * (numT : ℤ)).toNat = piNat * numT ∧
    (((piNat * numT : ℕ) : ℤ) * ((piNat * numT : ℕ) : ℤ)).toNat = (piNat * numT) ^ 2 ∧
    ((((4 * p_work : ℕ) : ℤ) * (log2Nat : ℤ)) * ((t1 : ℤ) * (t1 : ℤ))).toNat * 2 ^ B_c =
      4 * p_work * log2Nat * t1 ^ 2 * 2 ^ B_c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.cast_mul, Int.toNat_natCast]
  · rw [← Nat.cast_mul, Int.toNat_natCast, sq]
  · have h : (((4 * p_work : ℕ) : ℤ) * (log2Nat : ℤ)) * ((t1 : ℤ) * (t1 : ℤ)) =
        ((4 * p_work * log2Nat * t1 ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]

set_option backward.dsimp.instances true in
/-- Accuracy theorem for `computableSincGaussianTapInner`. -/
theorem computableSincGaussianTapInner_spec
    (p_work pSub B M_θ N B_c Bint w t1 piNat log2Nat numT : ℕ) (t : ℝ)
    (hB : B = pSub + 2) (hM_θ : M_θ = 4 * (pSub + 1))
    (hN : 4 * M_θ + B + 4 ≤ N)
    (hB_c : B + N + 3 * M_θ + 6 ≤ B_c)
    (hBint : B + 2 * N + 2 * M_θ + 6 ≤ Bint)
    (hp_work : 0 < p_work) (hpSub : 0 < pSub) (ht1 : 0 < t1)
    (ht_abs : |t| = (numT : ℝ) / (t1 : ℝ))
    (ht_le : |t| ≤ (pSub + 1 : ℝ))
    (hpi_err : |(piNat : ℝ) / (2 : ℝ) ^ B_c - Real.pi| ≤ (2 : ℝ) ^ (-(B_c : ℤ)))
    (hlog2_err : |(log2Nat : ℝ) / (2 : ℝ) ^ B_c - Real.log 2| ≤ (2 : ℝ) ^ (-(B_c : ℤ)))
    (hlog2_half : (1 / 2 : ℝ) ≤ (log2Nat : ℝ) / (2 : ℝ) ^ B_c)
    (hlog2_pos : 0 < log2Nat) :
    let G := (computableSincGaussianTapInner p_work pSub B N B_c Bint w t1 piNat log2Nat numT).1
    |((G : ℝ) / (2 : ℝ) ^ pSub) - sincGaussian (alphaSchedule p_work) t| ≤
      (2 : ℝ) ^ (-(pSub : ℤ)) ∧
    G.natAbs ≤ 2 ^ pSub + 1 := by
  dsimp only [computableSincGaussianTapInner, costedMulInt, costedClampInt, costedDivRoundRatInt]
  have hsetup := sincGaussian_inner_setup_identities p_work B_c t1 piNat log2Nat numT
  rw [hsetup.1, hsetup.2.1, hsetup.2.2]
  set numTheta : ℕ := piNat * numT
  set denTheta : ℕ := t1 * 2 ^ B_c
  set numY : ℕ := numTheta ^ 2
  set denY : ℕ := 4 * p_work * log2Nat * t1 ^ 2 * 2 ^ B_c
  set y : ℝ := (Real.pi / (alphaSchedule p_work) ^ 2) * t ^ 2
  have hsg_eq : sincGaussian (alphaSchedule p_work) t = normSinc t * Real.exp (-y) := by
    unfold sincGaussian
    dsimp [y]
    rw [neg_mul]
  have hdenTheta : 0 < denTheta := Nat.mul_pos ht1 (pow_pos zero_lt_two B_c)
  have hdenY : 0 < denY := by positivity
  have hbounds := sincGaussian_theta_and_y_bounds p_work pSub B M_θ N B_c t1
    piNat log2Nat numT t hM_θ hB_c hp_work ht1 ht_abs ht_le
    hpi_err hlog2_err hlog2_half hlog2_pos
  split_ifs with hclamped
  · exact sincGaussian_clamped_zero_spec pSub B numY denY (alphaSchedule p_work) t y
      hB hdenY hsg_eq hbounds.2.2.2 hclamped
  · push_neg at hclamped
    have hy_hat_le : (numY : ℝ) / (denY : ℝ) ≤ ((B + 2 : ℕ) : ℝ) := by
      have hdenY_r : (0 : ℝ) < (denY : ℝ) := Nat.cast_pos.mpr hdenY
      rw [div_le_iff₀ hdenY_r]
      exact_mod_cast hclamped.le
    have hsinc := computableSincRationalClamp_spec B M_θ N Bint w numTheta denTheta t
      (by omega) (by omega) hdenTheta (by omega) (by omega)
      hbounds.1 hbounds.2.1 hbounds.2.2.1
    have hy_nonneg : 0 ≤ y := mul_nonneg (div_nonneg Real.pi_pos.le (sq_nonneg _)) (sq_nonneg _)
    have hexp := computableExpNegRationalClamp_spec B (B + 2) N Bint w numY denY y
      hdenY hy_nonneg (by omega) (by omega) hy_hat_le hbounds.2.2.2
    exact sincGaussian_mul_round_clamp_spec pSub B hB
      (computableSincRationalClamp B N Bint w numTheta denTheta).1
      (computableExpNegRationalClamp B N Bint w numY denY).1
      (alphaSchedule p_work) t y hy_nonneg hsg_eq hsinc.1 hsinc.2 hexp

/-- Accuracy theorem for `computableSincGaussianTapCore`. -/
theorem computableSincGaussianTapCore_spec
    (p_work pSub B M_θ N B_c Bint w t1 j1 s : ℕ)
    (hB : B = pSub + 2) (hM_θ : M_θ = 4 * (pSub + 1))
    (hN : 4 * M_θ + B + 4 ≤ N)
    (hB_c : B + N + 3 * M_θ + 6 ≤ B_c)
    (hBint : B + 2 * N + 2 * M_θ + 6 ≤ Bint)
    (hp_work : 0 < p_work) (hpSub : 0 < pSub) (ht1 : 0 < t1)
    (hj1 : j1 < t1) (hs : s < 2 * pSub + 1) :
    let G := (computableSincGaussianTapCore p_work pSub B N B_c Bint w t1 j1 s).1
    |((G : ℝ) / (2 : ℝ) ^ pSub) -
      sincGaussian (alphaSchedule p_work) (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
      (2 : ℝ) ^ (-(pSub : ℤ)) ∧
    G.natAbs ≤ 2 ^ pSub + 1 := by
  dsimp only [computableSincGaussianTapCore, costedMulInt]
  have hBc_ge3 : 3 ≤ B_c := by omega
  have hpi_spec := computablePiScaledWithCost_error_le B_c
  have hlog2_err := computableLog2ScaledWithCost_error_le B_c
  have hlog2_ge := computableLog2ScaledWithCost_ge_half B_c hBc_ge3
  generalize hPiInt : (computablePiScaledWithCost B_c).1 = piInt at hpi_spec ⊢
  generalize hLog2Int : (computableLog2ScaledWithCost B_c).1 = log2Int at hlog2_err hlog2_ge ⊢
  obtain ⟨hpi_err, hpi_nonneg⟩ := hpi_spec
  obtain ⟨hlog2_half, hlog2_nonneg⟩ := hlog2_ge
  generalize hPiNat : piInt.toNat = piNat
  generalize hLog2Nat : log2Int.toNat = log2Nat
  have hpiNat_cast : (piNat : ℝ) = (piInt : ℝ) := by
    have : (piNat : ℤ) = piInt := by rw [← hPiNat]; exact Int.toNat_of_nonneg hpi_nonneg
    exact_mod_cast this
  have hlog2Nat_cast : (log2Nat : ℝ) = (log2Int : ℝ) := by
    have : (log2Nat : ℤ) = log2Int := by rw [← hLog2Nat]; exact Int.toNat_of_nonneg hlog2_nonneg
    exact_mod_cast this
  rw [← hpiNat_cast] at hpi_err
  rw [← hlog2Nat_cast] at hlog2_err hlog2_half
  have hlog2_pos : 0 < log2Nat := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ B_c := by positivity
    have hpos2 : (0 : ℝ) < (1 / 2 : ℝ) * (2 : ℝ) ^ B_c := by positivity
    have h1 := (le_div_iff₀ hpos).mp hlog2_half
    have hlt : (0 : ℝ) < (log2Nat : ℝ) := by linarith
    exact Nat.cast_pos.mp hlt
  have htap := tap_offset_abs_eq_and_le pSub t1 j1 s ht1 hj1 hs
  exact computableSincGaussianTapInner_spec p_work pSub B M_θ N B_c Bint w t1
    piNat log2Nat (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)).natAbs
    (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))
    hB hM_θ hN hB_c hBint hp_work hpSub ht1 htap.1 htap.2.2
    hpi_err hlog2_err hlog2_half hlog2_pos

/-- **Accuracy and Magnitude Theorem for `computableSincGaussianTapWithProgramCost`
(`computableSincGaussianTapWithProgramCost_spec`)**:
For `0 < p_work`, `0 < pSub`, `0 < t1`, `j1 < t1`, and `s < 2 * pSub + 1`,
`computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s` approximates
`sincGaussian (alphaSchedule p_work) (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))`
at scale `2^pSub` within `2^(-pSub)` with `G.natAbs ≤ 2^pSub + 1`. -/
theorem computableSincGaussianTapWithProgramCost_spec
    (p_work pSub t1 j1 s : ℕ)
    (hp_work : 0 < p_work) (hpSub : 0 < pSub) (ht1 : 0 < t1)
    (hj1 : j1 < t1) (hs : s < 2 * pSub + 1) :
    let G := (computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1
    |((G : ℝ) / (2 : ℝ) ^ pSub) -
      sincGaussian (alphaSchedule p_work) (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
      (2 : ℝ) ^ (-(pSub : ℤ)) ∧
    G.natAbs ≤ 2 ^ pSub + 1 :=
  computableSincGaussianTapCore_spec p_work pSub
    (pSub + 2)
    (4 * (pSub + 1))
    (4 * (4 * (pSub + 1)) + (pSub + 2) + 4)
    ((pSub + 2) + (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 3 * (4 * (pSub + 1)) + 6)
    ((pSub + 2) + 2 * (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 2 * (4 * (pSub + 1)) + 6)
    (((pSub + 2) + 2 * (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 2 * (4 * (pSub + 1)) + 6) +
      4 * (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 2 * (4 * (pSub + 1)) +
      2 * ((pSub + 2) + (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 3 * (4 * (pSub + 1)) + 6) +
      2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 40)
    t1 j1 s rfl rfl le_rfl le_rfl le_rfl hp_work hpSub ht1 hj1 hs

/-- Call-site width soundness predicate for `computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s`. -/
def SincGaussianTapWidthSound (p_work pSub t1 j1 s : ℕ) : Prop :=
  let B := pSub + 2
  let M_θ := 4 * (pSub + 1)
  let N := 4 * M_θ + B + 4
  let B_c := B + N + 3 * M_θ + 6
  let Bint := B + 2 * N + 2 * M_θ + 6
  let w := Bint + 4 * N + 2 * M_θ + 2 * B_c + 2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 40
  let piNat := (computablePiScaledWithCost B_c).1.toNat
  let log2Nat := (computableLog2ScaledWithCost B_c).1.toNat
  let diffS : ℤ := (s : ℤ) - (pSub : ℤ)
  let numT : ℕ := (diffS * (t1 : ℤ) - (j1 : ℤ)).natAbs
  let numTheta : ℕ := piNat * numT
  let denTheta : ℕ := t1 * 2 ^ B_c
  let numY : ℕ := numTheta ^ 2
  let denY : ℕ := 4 * p_work * log2Nat * t1 ^ 2 * 2 ^ B_c
  let sincSeriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N
  let sincRaw := divRoundRatInt (sincSeriesRes.1.2 * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  let sincInt := (costedClampInt w (-((2 ^ B : ℕ) : ℤ)) ((2 ^ B : ℕ) : ℤ) sincRaw).1
  let expSeriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N
  let expRaw := divRoundRatInt (expSeriesRes.1.2 * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  let expInt := (costedClampInt w (-((2 ^ B : ℕ) : ℤ)) ((2 ^ B : ℕ) : ℤ) expRaw).1
  let prodRound := divRoundRatInt ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)) ((2 ^ (2 * B) : ℕ) : ℤ)
  PiScaledWidthSound B_c ∧
  Log2ScaledWidthSound B_c ∧
  FitsSignedScalarWord w diffS ∧
  FitsSignedScalarWord w (t1 : ℤ) ∧
  FitsSignedScalarWord w (piNat : ℤ) ∧
  FitsSignedScalarWord w (numT : ℤ) ∧
  FitsSignedScalarWord w (numTheta : ℤ) ∧
  FitsSignedScalarWord w (denTheta : ℤ) ∧
  FitsSignedScalarWord w ((4 * p_work : ℕ) : ℤ) ∧
  FitsSignedScalarWord w (log2Nat : ℤ) ∧
  FitsSignedScalarWord w ((4 * p_work * log2Nat : ℕ) : ℤ) ∧
  FitsSignedScalarWord w ((t1 ^ 2 : ℕ) : ℤ) ∧
  FitsSignedScalarWord w ((B + 2 : ℕ) : ℤ) ∧
  FitsSignedScalarWord w (denY : ℤ) ∧
  (¬ (((B + 2 : ℕ) : ℤ) * (denY : ℤ) ≤ (numY : ℤ)) →
    RecurrenceCallSitesWidthSound w ((2 ^ Bint : ℕ) : ℤ)
      (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N ∧
    FitsSignedScalarWord w (sincSeriesRes.1.2 * ((2 ^ B : ℕ) : ℤ)) ∧
    FitsSignedScalarWord w ((2 ^ Bint : ℕ) : ℤ) ∧
    FitsSignedScalarWord w sincRaw ∧
    RecurrenceCallSitesWidthSound w ((2 ^ Bint : ℕ) : ℤ)
      (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N ∧
    FitsSignedScalarWord w (expSeriesRes.1.2 * ((2 ^ B : ℕ) : ℤ)) ∧
    FitsSignedScalarWord w expRaw ∧
    FitsSignedScalarWord w sincInt ∧
    FitsSignedScalarWord w expInt ∧
    FitsSignedScalarWord w ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)) ∧
    FitsSignedScalarWord w ((2 ^ (2 * B) : ℕ) : ℤ) ∧
    FitsSignedScalarWord w prodRound)

/-- Power-of-two bounds on the integer setup quantities in `computableSincGaussianTapWithProgramCost`. -/
theorem sincGaussian_tap_int_bounds
    (p_work pSub B_c t1 j1 s : ℕ)
    (ht1 : 0 < t1) (hj1 : j1 < t1) (hs : s < 2 * pSub + 1) :
    let piNat := (computablePiScaledWithCost B_c).1.toNat
    let log2Nat := (computableLog2ScaledWithCost B_c).1.toNat
    let diffS : ℤ := (s : ℤ) - (pSub : ℤ)
    let numT : ℕ := (diffS * (t1 : ℤ) - (j1 : ℤ)).natAbs
    let numTheta : ℕ := piNat * numT
    let denTheta : ℕ := t1 * 2 ^ B_c
    let numY : ℕ := numTheta ^ 2
    let denY : ℕ := 4 * p_work * log2Nat * t1 ^ 2 * 2 ^ B_c
    let D : ℕ := 2 * B_c + 2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 10
    diffS.natAbs ≤ 2 ^ pSub ∧
    t1 ≤ 2 ^ (Nat.log2 t1 + 1) ∧
    piNat ≤ 2 ^ (B_c + 2) ∧
    log2Nat ≤ 2 ^ (B_c + 1) ∧
    numT ≤ 2 ^ (pSub + Nat.log2 t1 + 2) ∧
    numTheta ≤ 2 ^ (B_c + pSub + Nat.log2 t1 + 4) ∧
    denTheta ≤ 2 ^ (B_c + Nat.log2 t1 + 1) ∧
    4 * p_work ≤ 2 ^ (p_work + 2) ∧
    4 * p_work * log2Nat ≤ 2 ^ (B_c + p_work + 3) ∧
    t1 ^ 2 ≤ 2 ^ (2 * Nat.log2 t1 + 2) ∧
    denY ≤ 2 ^ (2 * B_c + p_work + 2 * Nat.log2 t1 + 5) ∧
    ((numTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D ∧
    ((denTheta ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D ∧
    (numY : ℝ) ≤ (2 : ℝ) ^ D ∧
    (denY : ℝ) ≤ (2 : ℝ) ^ D := by
  intro piNat log2Nat diffS numT numTheta denTheta numY denY D
  have htap := tap_offset_abs_eq_and_le pSub t1 j1 s ht1 hj1 hs
  have hdiffS : diffS.natAbs ≤ 2 ^ pSub := by
    have h1 : diffS.natAbs ≤ pSub := by dsimp [diffS]; omega
    exact h1.trans Nat.lt_two_pow_self.le
  have ht1_le : t1 ≤ 2 ^ (Nat.log2 t1 + 1) := nat_le_two_pow_log2_add_one t1
  have hpi_le := computablePiScaledWithCost_toNat_le B_c
  have hlog2_le := computableLog2ScaledWithCost_toNat_le B_c
  have hpSub1_le : pSub + 1 ≤ 2 ^ (pSub + 1) := Nat.lt_two_pow_self.le
  have hnumT_le : numT ≤ 2 ^ (pSub + Nat.log2 t1 + 2) := by
    calc numT ≤ (pSub + 1) * t1 := htap.2.1
      _ ≤ 2 ^ (pSub + 1) * 2 ^ (Nat.log2 t1 + 1) := Nat.mul_le_mul hpSub1_le ht1_le
      _ = 2 ^ (pSub + Nat.log2 t1 + 2) := by rw [← pow_add]; congr 1; omega
  have hnumTheta_le : numTheta ≤ 2 ^ (B_c + pSub + Nat.log2 t1 + 4) := by
    dsimp [numTheta]
    calc piNat * numT
        ≤ 2 ^ (B_c + 2) * 2 ^ (pSub + Nat.log2 t1 + 2) := Nat.mul_le_mul hpi_le hnumT_le
      _ = 2 ^ (B_c + pSub + Nat.log2 t1 + 4) := by rw [← pow_add]; congr 1; omega
  have hdenTheta_le : denTheta ≤ 2 ^ (B_c + Nat.log2 t1 + 1) := by
    dsimp [denTheta]
    calc t1 * 2 ^ B_c
        ≤ 2 ^ (Nat.log2 t1 + 1) * 2 ^ B_c := Nat.mul_le_mul_right _ ht1_le
      _ = 2 ^ (B_c + Nat.log2 t1 + 1) := by rw [← pow_add]; congr 1; omega
  have h4p_le : 4 * p_work ≤ 2 ^ (p_work + 2) := by
    have hp : p_work ≤ 2 ^ p_work := Nat.lt_two_pow_self.le
    calc 4 * p_work = 2 ^ 2 * p_work := rfl
      _ ≤ 2 ^ 2 * 2 ^ p_work := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (p_work + 2) := by rw [← pow_add]; congr 1; omega
  have h4plog_le : 4 * p_work * log2Nat ≤ 2 ^ (B_c + p_work + 3) := by
    calc 4 * p_work * log2Nat
        ≤ 2 ^ (p_work + 2) * 2 ^ (B_c + 1) := Nat.mul_le_mul h4p_le hlog2_le
      _ = 2 ^ (B_c + p_work + 3) := by rw [← pow_add]; congr 1; omega
  have ht1_sq_le : t1 ^ 2 ≤ 2 ^ (2 * Nat.log2 t1 + 2) := by
    calc t1 ^ 2 ≤ (2 ^ (Nat.log2 t1 + 1)) ^ 2 := Nat.pow_le_pow_left ht1_le 2
      _ = 2 ^ ((Nat.log2 t1 + 1) * 2) := (pow_mul 2 _ 2).symm
      _ = 2 ^ (2 * Nat.log2 t1 + 2) := by congr 1; omega
  have hdenY_le : denY ≤ 2 ^ (2 * B_c + p_work + 2 * Nat.log2 t1 + 5) := by
    dsimp [denY]
    calc 4 * p_work * log2Nat * t1 ^ 2 * 2 ^ B_c
        ≤ 2 ^ (B_c + p_work + 3) * 2 ^ (2 * Nat.log2 t1 + 2) * 2 ^ B_c :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul h4plog_le ht1_sq_le)
      _ = 2 ^ (2 * B_c + p_work + 2 * Nat.log2 t1 + 5) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
  have hnum_sq_D : numTheta ^ 2 ≤ 2 ^ D := by
    calc numTheta ^ 2
        ≤ (2 ^ (B_c + pSub + Nat.log2 t1 + 4)) ^ 2 := Nat.pow_le_pow_left hnumTheta_le 2
      _ = 2 ^ ((B_c + pSub + Nat.log2 t1 + 4) * 2) := (pow_mul 2 _ 2).symm
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega)
  have hden_sq_D : denTheta ^ 2 ≤ 2 ^ D := by
    calc denTheta ^ 2
        ≤ (2 ^ (B_c + Nat.log2 t1 + 1)) ^ 2 := Nat.pow_le_pow_left hdenTheta_le 2
      _ = 2 ^ ((B_c + Nat.log2 t1 + 1) * 2) := (pow_mul 2 _ 2).symm
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega)
  have hdenY_D : denY ≤ 2 ^ D :=
    hdenY_le.trans (Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega))
  exact ⟨hdiffS, ht1_le, hpi_le, hlog2_le, hnumT_le, hnumTheta_le, hdenTheta_le,
    h4p_le, h4plog_le, ht1_sq_le, hdenY_le,
    by exact_mod_cast hnum_sq_D, by exact_mod_cast hden_sq_D,
    by exact_mod_cast hnum_sq_D, by exact_mod_cast hdenY_D⟩

/-- **Call-Site Width Soundness for `computableSincGaussianTapWithProgramCost`**:
Every operand passed to `costedMulInt w`, `costedDivRoundRatInt w`, and `costedClampInt w`
inside `computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s` fits within `w` bits. -/
theorem computableSincGaussianTapWithProgramCost_widths_sound
    (p_work pSub t1 j1 s : ℕ)
    (hp_work : 0 < p_work) (hpSub : 0 < pSub) (ht1 : 0 < t1)
    (hj1 : j1 < t1) (hs : s < 2 * pSub + 1) :
    SincGaussianTapWidthSound p_work pSub t1 j1 s := by
  dsimp only [SincGaussianTapWidthSound, costedClampInt]
  set B := pSub + 2 with hB_def
  set M_θ := 4 * (pSub + 1) with hM_θ_def
  set N := 4 * M_θ + B + 4 with hN_def
  set B_c := B + N + 3 * M_θ + 6 with hBc_def
  set Bint := B + 2 * N + 2 * M_θ + 6 with hBint_def
  set w := Bint + 4 * N + 2 * M_θ + 2 * B_c + 2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 40 with hw_def
  set D := 2 * B_c + 2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 10 with hD_def
  clear_value B M_θ N B_c Bint w D
  have hib := sincGaussian_tap_int_bounds p_work pSub B_c t1 j1 s ht1 hj1 hs
  have hBc_ge3 : 3 ≤ B_c := by omega
  have hpi_spec := computablePiScaledWithCost_error_le B_c
  have hlog2_err := computableLog2ScaledWithCost_error_le B_c
  have hlog2_ge := computableLog2ScaledWithCost_ge_half B_c hBc_ge3
  generalize hPiInt : (computablePiScaledWithCost B_c).1 = piInt at hpi_spec hib ⊢
  generalize hLog2Int : (computableLog2ScaledWithCost B_c).1 = log2Int at hlog2_err hlog2_ge hib ⊢
  set piNat := piInt.toNat
  set log2Nat := log2Int.toNat
  set diffS : ℤ := (s : ℤ) - (pSub : ℤ)
  set numT : ℕ := (diffS * (t1 : ℤ) - (j1 : ℤ)).natAbs
  set numTheta : ℕ := piNat * numT
  set denTheta : ℕ := t1 * 2 ^ B_c
  set numY : ℕ := numTheta ^ 2
  set denY : ℕ := 4 * p_work * log2Nat * t1 ^ 2 * 2 ^ B_c
  have hf_diffS : FitsSignedScalarWord w diffS :=
    fitsSignedScalarWord_of_natAbs_le_two_pow _ _ _ hib.1 (by omega)
  have hf_t1 : FitsSignedScalarWord w (t1 : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_pi : FitsSignedScalarWord w (piNat : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_numT : FitsSignedScalarWord w (numT : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_numTheta : FitsSignedScalarWord w (numTheta : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_denTheta : FitsSignedScalarWord w (denTheta : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_4p : FitsSignedScalarWord w ((4 * p_work : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_log2 : FitsSignedScalarWord w (log2Nat : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_4plog : FitsSignedScalarWord w ((4 * p_work * log2Nat : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_t1sq : FitsSignedScalarWord w ((t1 ^ 2 : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.2.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_B2 : FitsSignedScalarWord w ((B + 2 : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_denY : FitsSignedScalarWord w (denY : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hib.2.2.2.2.2.2.2.2.2.2.1.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  refine ⟨computablePiScaledWithCost_widths_sound B_c,
    computableLog2ScaledWithCost_widths_sound B_c,
    hf_diffS, hf_t1, hf_pi, hf_numT, hf_numTheta, hf_denTheta,
    hf_4p, hf_log2, hf_4plog, hf_t1sq, hf_B2, hf_denY, ?_⟩
  intro hnot_clamped
  push_neg at hnot_clamped
  have hpiNat_cast : (piNat : ℝ) = (piInt : ℝ) := by
    have : (piNat : ℤ) = piInt := Int.toNat_of_nonneg hpi_spec.2
    exact_mod_cast this
  have hlog2Nat_cast : (log2Nat : ℝ) = (log2Int : ℝ) := by
    have : (log2Nat : ℤ) = log2Int := Int.toNat_of_nonneg hlog2_ge.2
    exact_mod_cast this
  have hpi_err_nat : |(piNat : ℝ) / (2 : ℝ) ^ B_c - Real.pi| ≤ (2 : ℝ) ^ (-(B_c : ℤ)) := by
    rw [hpiNat_cast]; exact hpi_spec.1
  have hlog2_err_nat : |(log2Nat : ℝ) / (2 : ℝ) ^ B_c - Real.log 2| ≤ (2 : ℝ) ^ (-(B_c : ℤ)) := by
    rw [hlog2Nat_cast]; exact hlog2_err
  have hlog2_half_nat : (1 / 2 : ℝ) ≤ (log2Nat : ℝ) / (2 : ℝ) ^ B_c := by
    rw [hlog2Nat_cast]; exact hlog2_ge.1
  have hlog2_pos : 0 < log2Nat := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ B_c := by positivity
    have hpos2 : (0 : ℝ) < (1 / 2 : ℝ) * (2 : ℝ) ^ B_c := by positivity
    have h1 := (le_div_iff₀ hpos).mp hlog2_half_nat
    exact Nat.cast_pos.mp (by linarith : (0 : ℝ) < (log2Nat : ℝ))
  have htap := tap_offset_abs_eq_and_le pSub t1 j1 s ht1 hj1 hs
  have hbounds := sincGaussian_theta_and_y_bounds p_work pSub B M_θ N B_c t1
    piNat log2Nat numT (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))
    hM_θ_def (by omega) hp_work ht1 htap.1 htap.2.2 hpi_err_nat hlog2_err_nat hlog2_half_nat hlog2_pos
  have hdenTheta_pos : 0 < denTheta := Nat.mul_pos ht1 (pow_pos zero_lt_two B_c)
  have hdenY_pos : 0 < denY :=
    Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 4) hp_work) hlog2_pos)
        (pow_pos ht1 2))
      (pow_pos zero_lt_two B_c)
  have hy_hat_le : (numY : ℝ) / (denY : ℝ) ≤ ((B + 2 : ℕ) : ℝ) := by
    have hdenY_r : (0 : ℝ) < (denY : ℝ) := Nat.cast_pos.mpr hdenY_pos
    rw [div_le_iff₀ hdenY_r]
    exact_mod_cast hnot_clamped.le
  have hsinc_rec := sinc_recurrence_spec_and_widths Bint M_θ D w N numTheta denTheta
    hdenTheta_pos hbounds.2.1
    (hD_def ▸ hib.2.2.2.2.2.2.2.2.2.2.2.1) (hD_def ▸ hib.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (by omega)
  have hexp_rec := expNeg_recurrence_spec_and_widths Bint (B + 2) D w N numY denY
    hdenY_pos hy_hat_le
    (hD_def ▸ hib.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hD_def ▸ hib.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (by omega)
  dsimp only at hsinc_rec hexp_rec
  generalize hSincSeries : (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-((numTheta ^ 2 : ℕ) : ℤ)) (denTheta ^ 2) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N).1.2 =
    sincSumVal at hsinc_rec ⊢
  generalize hExpSeries : (runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    (-(numY : ℤ)) denY (fun _ => 1) (fun k => k + 1) N).1.2 =
    expSumVal at hexp_rec ⊢
  have hf_Bint : FitsSignedScalarWord w ((2 ^ Bint : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hsinc_num_abs : |((sincSumVal * ((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ)| ≤
      (2 : ℝ) ^ (Bint + 2 * M_θ + 2 * N + 3 + B) := by
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B), pow_add]
    exact mul_le_mul_of_nonneg_right hsinc_rec.2.2 (by positivity)
  have hf_sinc_num : FitsSignedScalarWord w (sincSumVal * ((2 ^ B : ℕ) : ℤ)) :=
    fitsSignedScalarWord_of_abs_le_two_pow _ _ (hsinc_num_abs.trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hf_sinc_raw : FitsSignedScalarWord w
      (divRoundRatInt (sincSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_abs_le_two_pow _ _ ?_
    have hq := abs_divRoundRatInt_le (sincSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ) (by positivity)
    have hden_ge1 : (1 : ℝ) ≤ (((2 ^ Bint : ℕ) : ℤ) : ℝ) := by push_cast; exact one_le_pow₀ (by norm_num)
    have hdiv_le : |((sincSumVal * ((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ)| / (((2 ^ Bint : ℕ) : ℤ) : ℝ) ≤
        (2 : ℝ) ^ (Bint + 2 * M_θ + 2 * N + 3 + B) :=
      (div_le_self (abs_nonneg _) hden_ge1).trans hsinc_num_abs
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (Bint + 2 * M_θ + 2 * N + 3 + B) := one_le_pow₀ (by norm_num)
    calc |(divRoundRatInt (sincSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ) : ℝ)|
        ≤ (2 : ℝ) ^ (Bint + 2 * M_θ + 2 * N + 3 + B) + (2 : ℝ) ^ (Bint + 2 * M_θ + 2 * N + 3 + B) := by linarith
      _ = (2 : ℝ) ^ (Bint + 2 * M_θ + 2 * N + 3 + B + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hexp_num_abs : |((expSumVal * ((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ)| ≤
      (2 : ℝ) ^ (Bint + 2 * (B + 2) + 2 * N + 3 + B) := by
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B), pow_add]
    exact mul_le_mul_of_nonneg_right hexp_rec.2.2 (by positivity)
  have hf_exp_num : FitsSignedScalarWord w (expSumVal * ((2 ^ B : ℕ) : ℤ)) :=
    fitsSignedScalarWord_of_abs_le_two_pow _ _ (hexp_num_abs.trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hf_exp_raw : FitsSignedScalarWord w
      (divRoundRatInt (expSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_abs_le_two_pow _ _ ?_
    have hq := abs_divRoundRatInt_le (expSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ) (by positivity)
    have hden_ge1 : (1 : ℝ) ≤ (((2 ^ Bint : ℕ) : ℤ) : ℝ) := by push_cast; exact one_le_pow₀ (by norm_num)
    have hdiv_le : |((expSumVal * ((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ)| / (((2 ^ Bint : ℕ) : ℤ) : ℝ) ≤
        (2 : ℝ) ^ (Bint + 2 * (B + 2) + 2 * N + 3 + B) :=
      (div_le_self (abs_nonneg _) hden_ge1).trans hexp_num_abs
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (Bint + 2 * (B + 2) + 2 * N + 3 + B) := one_le_pow₀ (by norm_num)
    calc |(divRoundRatInt (expSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ) : ℝ)|
        ≤ (2 : ℝ) ^ (Bint + 2 * (B + 2) + 2 * N + 3 + B) + (2 : ℝ) ^ (Bint + 2 * (B + 2) + 2 * N + 3 + B) := by linarith
      _ = (2 : ℝ) ^ (Bint + 2 * (B + 2) + 2 * N + 3 + B + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  set sincRaw := divRoundRatInt (sincSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  set expRaw := divRoundRatInt (expSumVal * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  set sincInt := max (-((2 ^ B : ℕ) : ℤ)) (min ((2 ^ B : ℕ) : ℤ) sincRaw)
  set expInt := max (-((2 ^ B : ℕ) : ℤ)) (min ((2 ^ B : ℕ) : ℤ) expRaw)
  have hsinc_natAbs : sincInt.natAbs ≤ 2 ^ B := by
    have h2B_z : (0 : ℤ) ≤ ((2 ^ B : ℕ) : ℤ) := Nat.cast_nonneg _
    have hdn : -((2 ^ B : ℕ) : ℤ) ≤ sincInt := le_max_left _ _
    have hup : sincInt ≤ ((2 ^ B : ℕ) : ℤ) := max_le (neg_le_self h2B_z) (min_le_left _ _)
    generalize (sincInt : ℤ) = g at hdn hup; omega
  have hexp_natAbs : expInt.natAbs ≤ 2 ^ B := by
    have h2B_z : (0 : ℤ) ≤ ((2 ^ B : ℕ) : ℤ) := Nat.cast_nonneg _
    have hdn : -((2 ^ B : ℕ) : ℤ) ≤ expInt := le_max_left _ _
    have hup : expInt ≤ ((2 ^ B : ℕ) : ℤ) := max_le (neg_le_self h2B_z) (min_le_left _ _)
    generalize (expInt : ℤ) = g at hdn hup; omega
  have hf_sincInt : FitsSignedScalarWord w sincInt :=
    fitsSignedScalarWord_of_natAbs_le_two_pow _ _ _ hsinc_natAbs (by omega)
  have hf_expInt : FitsSignedScalarWord w expInt :=
    fitsSignedScalarWord_of_natAbs_le_two_pow _ _ _ hexp_natAbs (by omega)
  have hprod_natAbs : ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)).natAbs ≤ 2 ^ (2 * B + pSub) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    calc sincInt.natAbs * expInt.natAbs * 2 ^ pSub
        ≤ 2 ^ B * 2 ^ B * 2 ^ pSub :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hsinc_natAbs hexp_natAbs)
      _ = 2 ^ (2 * B + pSub) := by rw [← pow_add, ← pow_add, show B + B + pSub = 2 * B + pSub by omega]
  have hf_prod_num : FitsSignedScalarWord w ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)) :=
    fitsSignedScalarWord_of_natAbs_le_two_pow _ _ _ hprod_natAbs (by omega)
  have hf_2B : FitsSignedScalarWord w ((2 ^ (2 * B) : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hf_prodRound : FitsSignedScalarWord w
      (divRoundRatInt ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)) ((2 ^ (2 * B) : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_abs_le_two_pow _ _ ?_
    have hq := abs_divRoundRatInt_le ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)) ((2 ^ (2 * B) : ℕ) : ℤ) (by positivity)
    have hnum_r : |(((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (2 * B + pSub) := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hprod_natAbs
    have hden_ge1 : (1 : ℝ) ≤ (((2 ^ (2 * B) : ℕ) : ℤ) : ℝ) := by push_cast; exact one_le_pow₀ (by norm_num)
    have hdiv_le : |(((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ) : ℤ) : ℝ)| / (((2 ^ (2 * B) : ℕ) : ℤ) : ℝ) ≤
        (2 : ℝ) ^ (2 * B + pSub) :=
      (div_le_self (abs_nonneg _) hden_ge1).trans hnum_r
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * B + pSub) := one_le_pow₀ (by norm_num)
    calc |(divRoundRatInt ((sincInt * expInt) * ((2 ^ pSub : ℕ) : ℤ)) ((2 ^ (2 * B) : ℕ) : ℤ) : ℝ)|
        ≤ (2 : ℝ) ^ (2 * B + pSub) + (2 : ℝ) ^ (2 * B + pSub) := by linarith
      _ = (2 : ℝ) ^ (2 * B + pSub + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨hsinc_rec.2.1, hf_sinc_num, hf_Bint, hf_sinc_raw,
    hexp_rec.2.1, hf_exp_num, hf_exp_raw,
    hf_sincInt, hf_expInt, hf_prod_num, hf_2B, hf_prodRound⟩

set_option backward.dsimp.instances true in
/-- Cost bound for `computableSincGaussianTapInner` when `N ≤ w`. -/
theorem computableSincGaussianTapInner_snd_le
    (p_work pSub B N B_c Bint w t1 piNat log2Nat numT : ℕ)
    (hN_le : N ≤ w) :
    (computableSincGaussianTapInner p_work pSub B N B_c Bint w t1 piNat log2Nat numT).2 ≤
      18 * (w + 10) ^ 4 := by
  dsimp only [computableSincGaussianTapInner, costedShiftLeftNat, costedShiftLeftInt,
    costedMulInt, costedDivRoundRatInt, costedClampInt]
  have hw1 : w + 1 ≤ w + 10 := by omega
  have hmul : computableMulBitCost w ≤ (w + 10) ^ 3 :=
    (computableMulBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hadd : addBitCost w ≤ (w + 10) ^ 3 :=
    (addBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hN7 : 2 * N + 7 ≤ 2 * (w + 10) := by omega
  split_ifs
  · generalize computableMulBitCost w = MulC at hmul ⊢
    generalize addBitCost w = AddC at hadd ⊢
    generalize hW3 : (w + 10) ^ 3 = W3 at hmul hadd
    have hpow3_le4 : W3 ≤ (w + 10) ^ 4 := by
      subst hW3
      exact Nat.pow_le_pow_right (by omega) (by decide)
    omega
  · rw [computableSincRationalClamp_snd, computableExpNegRationalClamp_snd]
    generalize computableMulBitCost w = MulC at hmul ⊢
    generalize addBitCost w = AddC at hadd ⊢
    generalize hW3 : (w + 10) ^ 3 = W3 at hmul hadd
    have h1 :
        (MulC + AddC + MulC + MulC + MulC + MulC + AddC + MulC + AddC) +
          (MulC + MulC + (N * (6 * MulC + 3 * AddC)) + AddC + (2 * MulC + 2 * AddC) + 2 * AddC) +
          ((N * (6 * MulC + 3 * AddC)) + AddC + (2 * MulC + 2 * AddC) + 2 * AddC) +
          MulC + AddC + (2 * MulC + 2 * AddC) + 2 * AddC ≤
        (2 * N + 7) * (6 * MulC + 3 * AddC) := by
      nlinarith
    calc (MulC + AddC + MulC + MulC + MulC + MulC + AddC + MulC + AddC) +
          (MulC + MulC + (N * (6 * MulC + 3 * AddC)) + AddC + (2 * MulC + 2 * AddC) + 2 * AddC) +
          ((N * (6 * MulC + 3 * AddC)) + AddC + (2 * MulC + 2 * AddC) + 2 * AddC) +
          MulC + AddC + (2 * MulC + 2 * AddC) + 2 * AddC
        ≤ (2 * N + 7) * (6 * MulC + 3 * AddC) := h1
      _ ≤ (2 * (w + 10)) * (6 * W3 + 3 * W3) := Nat.mul_le_mul hN7 (by omega)
      _ = 18 * (w + 10) ^ 4 := by subst hW3; ring

/-- Cost bound for `computableSincGaussianTapCore` in terms of `(w + 10) ^ 4` when `B_c ≤ w` and `N ≤ w`. -/
theorem computableSincGaussianTapCore_snd_le
    (p_work pSub B N B_c Bint w t1 j1 s : ℕ)
    (hBc_le : B_c ≤ w) (hN_le : N ≤ w) :
    (computableSincGaussianTapCore p_work pSub B N B_c Bint w t1 j1 s).2 ≤
      7000 * (w + 10) ^ 4 := by
  dsimp only [computableSincGaussianTapCore, costedMulInt]
  have hpi_cost := computablePiScaledWithCost_snd_le B_c
  have hlog2_cost := computableLog2ScaledWithCost_snd_le B_c
  have hBc7 : B_c + 7 ≤ w + 10 := by omega
  have h8Bc : 8 * B_c + 85 ≤ 9 * (w + 10) := by omega
  have hBc4 : B_c + 4 ≤ w + 10 := by omega
  have h7Bc : 7 * B_c + 45 ≤ 7 * (w + 10) := by omega
  have hpi_le : (computablePiScaledWithCost B_c).2 ≤ 3645 * (w + 10) ^ 4 := by
    calc (computablePiScaledWithCost B_c).2
        ≤ (B_c + 7) * 5 * (8 * B_c + 85) ^ 3 := hpi_cost
      _ ≤ (w + 10) * 5 * (9 * (w + 10)) ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_right 5 hBc7) (Nat.pow_le_pow_left h8Bc 3)
      _ = 3645 * (w + 10) ^ 4 := by ring
  have hlog2_le : (computableLog2ScaledWithCost B_c).2 ≤ 3087 * (w + 10) ^ 4 := by
    calc (computableLog2ScaledWithCost B_c).2
        ≤ (B_c + 4) * 9 * (7 * B_c + 45) ^ 3 := hlog2_cost
      _ ≤ (w + 10) * 9 * (7 * (w + 10)) ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_right 9 hBc4) (Nat.pow_le_pow_left h7Bc 3)
      _ = 3087 * (w + 10) ^ 4 := by ring
  have hw1 : w + 1 ≤ w + 10 := by omega
  have hmul : computableMulBitCost w ≤ (w + 10) ^ 3 :=
    (computableMulBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hadd : addBitCost w ≤ (w + 10) ^ 3 :=
    (addBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hprodT_le : computableMulBitCost w + addBitCost w ≤ 2 * (w + 10) ^ 4 := by
    have hpow3_le4 : (w + 10) ^ 3 ≤ (w + 10) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hinner_le := computableSincGaussianTapInner_snd_le p_work pSub B N B_c Bint w t1
    (computablePiScaledWithCost B_c).1.toNat (computableLog2ScaledWithCost B_c).1.toNat
    (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)).natAbs hN_le
  calc (computablePiScaledWithCost B_c).2 + (computableLog2ScaledWithCost B_c).2 +
        computableMulBitCost w + addBitCost w +
        (computableSincGaussianTapInner p_work pSub B N B_c Bint w t1
          (computablePiScaledWithCost B_c).1.toNat (computableLog2ScaledWithCost B_c).1.toNat
          (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)).natAbs).2
      ≤ 3645 * (w + 10) ^ 4 + 3087 * (w + 10) ^ 4 + 2 * (w + 10) ^ 4 + 18 * (w + 10) ^ 4 := by
        linarith
    _ = 6752 * (w + 10) ^ 4 := by ring
    _ ≤ 7000 * (w + 10) ^ 4 := Nat.mul_le_mul_right _ (by decide)

/-- **Bit-Operation Cost Bound for `computableSincGaussianTapWithProgramCost`
(`computableSincGaussianTapWithProgramCost_snd_le`)**:
Bounded by an explicit degree-4 polynomial in `M = p_work + pSub + Nat.log2 t1 + 1`. -/
theorem computableSincGaussianTapWithProgramCost_snd_le
    (p_work pSub t1 j1 s : ℕ) :
    let M := p_work + pSub + Nat.log2 t1 + 1
    (computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).2 ≤
      7000 * (200 * (M + 20)) ^ 4 := by
  intro M
  dsimp only [computableSincGaussianTapWithProgramCost]
  set B := pSub + 2 with hB_def
  set M_θ := 4 * (pSub + 1) with hM_θ_def
  set N := 4 * M_θ + B + 4 with hN_def
  set B_c := B + N + 3 * M_θ + 6 with hBc_def
  set Bint := B + 2 * N + 2 * M_θ + 6 with hBint_def
  set w := Bint + 4 * N + 2 * M_θ + 2 * B_c + 2 * p_work + 2 * pSub + 2 * Nat.log2 t1 + 40 with hw_def
  clear_value B M_θ N B_c Bint w
  have hBc_le : B_c ≤ w := by omega
  have hN_le : N ≤ w := by omega
  have hw10_le : w + 10 ≤ 200 * (M + 20) := by dsimp [M]; omega
  exact (computableSincGaussianTapCore_snd_le p_work pSub B N B_c Bint w t1 j1 s hBc_le hN_le).trans
    (Nat.mul_le_mul_left 7000 (Nat.pow_le_pow_left hw10_le 4))

/-! ### 7. Computable Evaluator for Passband Coefficients `(c_0, c_1)` -/

/-- Exact integral representation of `(1 / 2) * realErfScaled (alphaSchedule p_work) x` for `0 < p_work`. -/
theorem half_realErfScaled_alphaSchedule_eq (p_work : ℕ) (hp : 0 < p_work) (x : ℝ) :
    (1 / 2 : ℝ) * realErfScaled (alphaSchedule p_work) x =
      (∫ t in (0 : ℝ)..(Real.sqrt (4 * (p_work : ℝ) * Real.log 2) * x), Real.exp (-(t ^ 2))) /
        Real.sqrt Real.pi := by
  unfold realErfScaled realErf
  have hpi : 0 < Real.pi := Real.pi_pos
  have hα : 0 < alphaSchedule p_work := alphaSchedule_pos p_work hp
  have hprod_nonneg : 0 ≤ Real.sqrt Real.pi * alphaSchedule p_work :=
    mul_nonneg (Real.sqrt_nonneg _) hα.le
  have hsq : (Real.sqrt Real.pi * alphaSchedule p_work) ^ 2 = 4 * (p_work : ℝ) * Real.log 2 := by
    rw [mul_pow, Real.sq_sqrt hpi.le, pi_mul_alphaSchedule_sq p_work hp]
  have hsqrt_eq : Real.sqrt Real.pi * alphaSchedule p_work =
      Real.sqrt (4 * (p_work : ℝ) * Real.log 2) := by
    rw [← hsq, Real.sqrt_sq hprod_nonneg]
  rw [hsqrt_eq]
  ring

/-- Passband identities, range bounds `[0, 1]`, dominance `c1 ≤ c0` on `[0, 1/2]`,
and reflection symmetry `y ↦ 1 - y` for `c0Coeff` and `c1Coeff`. -/
theorem c0Coeff_and_c1Coeff_realErfScaled_bounds
    (α y : ℝ) (hα : 0 < α) (hy0 : 0 ≤ y) (hy_half : y ≤ 1 / 2) :
    let E : ℝ → ℝ := fun x => (1 / 2 : ℝ) * realErfScaled α x
    c0Coeff (realErfScaled α) y = E (y + 1 / 2) + E (1 / 2 - y) ∧
    c1Coeff (realErfScaled α) y = E (3 / 2 - y) - E (1 / 2 - y) ∧
    0 ≤ c0Coeff (realErfScaled α) y ∧
    c0Coeff (realErfScaled α) y ≤ 1 ∧
    0 ≤ c1Coeff (realErfScaled α) y ∧
    c1Coeff (realErfScaled α) y ≤ c0Coeff (realErfScaled α) y ∧
    c0Coeff (realErfScaled α) (1 - y) = c1Coeff (realErfScaled α) y ∧
    c1Coeff (realErfScaled α) (1 - y) = c0Coeff (realErfScaled α) y := by
  intro E
  have hc0_eq : c0Coeff (realErfScaled α) y = E (y + 1 / 2) + E (1 / 2 - y) := by
    unfold c0Coeff gHatBox
    dsimp [E]
    have hneg : y - 1 / 2 = -(1 / 2 - y) := by ring
    rw [hneg, realErfScaled_neg]
    ring
  have hc1_eq : c1Coeff (realErfScaled α) y = E (3 / 2 - y) - E (1 / 2 - y) := by
    unfold c1Coeff gHatBox
    dsimp [E]
    have h1 : 1 - y + 1 / 2 = 3 / 2 - y := by ring
    have h2 : 1 - y - 1 / 2 = 1 / 2 - y := by ring
    rw [h1, h2]
    ring
  have hc0_0 : 0 ≤ c0Coeff (realErfScaled α) y := (c0Coeff_realErfScaled_pos α y hα).le
  have hc0_1 : c0Coeff (realErfScaled α) y ≤ 1 := by
    unfold c0Coeff gHatBox
    have hsub := realErfScaled_sub_le_two α (y - 1 / 2) (y + 1 / 2) hα.le (by linarith)
    linarith
  have hc1_0 : 0 ≤ c1Coeff (realErfScaled α) y := (c1Coeff_realErfScaled_pos α y hα).le
  have hc1_le_c0 : c1Coeff (realErfScaled α) y ≤ c0Coeff (realErfScaled α) y :=
    c1Coeff_le_c0Coeff_of_le_half α y hα hy0 hy_half
  have hsym0 : c0Coeff (realErfScaled α) (1 - y) = c1Coeff (realErfScaled α) y := rfl
  have hsym1 : c1Coeff (realErfScaled α) (1 - y) = c0Coeff (realErfScaled α) y := by
    unfold c0Coeff c1Coeff
    congr 1
    ring
  exact ⟨hc0_eq, hc1_eq, hc0_0, hc0_1, hc1_0, hc1_le_c0, hsym0, hsym1⟩

/-- Unit-interval clamping `max 0 (min (2^B) rawG)` preserves scaled accuracy for `x ∈ [0, 1]`. -/
theorem abs_clampInt_unit_scaled_sub_le (B : ℕ) (rawG : ℤ) (x δ : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hraw : |(rawG : ℝ) / (2 : ℝ) ^ B - x| ≤ δ) :
    let G := max 0 (min ((2 ^ B : ℕ) : ℤ) rawG)
    |(G : ℝ) / (2 : ℝ) ^ B - x| ≤ δ ∧
    0 ≤ G ∧
    G ≤ ((2 ^ B : ℕ) : ℤ) := by
  intro G
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hlo : ((0 : ℤ) : ℝ) ≤ x * (2 : ℝ) ^ B := by push_cast; positivity
  have hhi : x * (2 : ℝ) ^ B ≤ (((2 ^ B : ℕ) : ℤ) : ℝ) := by push_cast; nlinarith
  have hclamp := abs_clampInt_sub_le 0 ((2 ^ B : ℕ) : ℤ) rawG (x * (2 : ℝ) ^ B) hlo hhi
  have hdiv1 : ((G : ℝ) - x * (2 : ℝ) ^ B) / (2 : ℝ) ^ B = (G : ℝ) / (2 : ℝ) ^ B - x := by
    field_simp [hpow_pos.ne']
  have hdiv2 : ((rawG : ℝ) - x * (2 : ℝ) ^ B) / (2 : ℝ) ^ B = (rawG : ℝ) / (2 : ℝ) ^ B - x := by
    field_simp [hpow_pos.ne']
  have herr : |(G : ℝ) / (2 : ℝ) ^ B - x| ≤ δ := by
    rw [← hdiv1, abs_div, abs_of_pos hpow_pos]
    have h2 : |(rawG : ℝ) - x * (2 : ℝ) ^ B| / (2 : ℝ) ^ B = |(rawG : ℝ) / (2 : ℝ) ^ B - x| := by
      rw [← hdiv2, abs_div, abs_of_pos hpow_pos]
    calc |(G : ℝ) - x * (2 : ℝ) ^ B| / (2 : ℝ) ^ B
        ≤ |(rawG : ℝ) - x * (2 : ℝ) ^ B| / (2 : ℝ) ^ B :=
          div_le_div_of_nonneg_right hclamp hpow_pos.le
      _ = |(rawG : ℝ) / (2 : ℝ) ^ B - x| := h2
      _ ≤ δ := hraw
  have h2B_z : (0 : ℤ) ≤ ((2 ^ B : ℕ) : ℤ) := Nat.cast_nonneg _
  have hG_0 : 0 ≤ G := le_max_left _ _
  have hG_up : G ≤ ((2 ^ B : ℕ) : ℤ) := max_le h2B_z (min_le_left _ _)
  exact ⟨herr, hG_0, hG_up⟩

/-- Combining, rounding from `2^B_e` to `2^B`, and clamping accuracy for `(hiInt, loInt)`
where `B = pSub + 2` and `B_e = B + 2`. -/
theorem c0_c1_combine_round_clamp_spec
    (pSub B B_e : ℕ) (hB : B = pSub + 2) (hBe : B_e = B + 2)
    (hPlus hMinus hThree : ℤ) (E_plus E_minus E_three c0 c1 : ℝ)
    (hc0_eq : c0 = E_plus + E_minus)
    (hc1_eq : c1 = E_three - E_minus)
    (hc0_0 : 0 ≤ c0) (hc0_1 : c0 ≤ 1)
    (hc1_0 : 0 ≤ c1) (hc1_le_c0 : c1 ≤ c0)
    (hP_err : |(hPlus : ℝ) / (2 : ℝ) ^ B_e - E_plus| ≤ (2 : ℝ) ^ (-(B_e : ℤ)))
    (hM_err : |(hMinus : ℝ) / (2 : ℝ) ^ B_e - E_minus| ≤ (2 : ℝ) ^ (-(B_e : ℤ)))
    (hT_err : |(hThree : ℝ) / (2 : ℝ) ^ B_e - E_three| ≤ (2 : ℝ) ^ (-(B_e : ℤ))) :
    let rawHi := divRoundRatInt ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ)
    let hiInt := max 0 (min ((2 ^ B : ℕ) : ℤ) rawHi)
    let rawLo := divRoundRatInt ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ)
    let loClamp := max 0 (min ((2 ^ B : ℕ) : ℤ) rawLo)
    let loInt := min loClamp hiInt
    0 ≤ hiInt ∧ hiInt ≤ (2 : ℤ) ^ (pSub + 2) ∧
    0 ≤ loInt ∧ loInt ≤ (2 : ℤ) ^ (pSub + 2) ∧
    loInt ≤ hiInt ∧
    |(hiInt : ℝ) / (2 : ℝ) ^ (pSub + 2) - c0| ≤ 2 * realQuantizeMaxErr pSub ∧
    |(loInt : ℝ) / (2 : ℝ) ^ (pSub + 2) - c1| ≤ 2 * realQuantizeMaxErr pSub := by
  intro rawHi hiInt rawLo loClamp loInt
  have h2Be_eq : 2 * (2 : ℝ) ^ (-(B_e : ℤ)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have h1 : (-(B_e : ℤ)) = (-2 : ℤ) + (-(B : ℤ)) := by omega
    have h2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [h1, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h2]
    ring
  have hdenBe_pos : (0 : ℤ) < ((2 ^ B_e : ℕ) : ℤ) := by positivity
  set sumHi : ℝ := ((hPlus + hMinus : ℤ) : ℝ) / (2 : ℝ) ^ B_e
  have hsumHi_err : |sumHi - c0| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have hsplit : sumHi - c0 =
        ((hPlus : ℝ) / (2 : ℝ) ^ B_e - E_plus) + ((hMinus : ℝ) / (2 : ℝ) ^ B_e - E_minus) := by
      dsimp [sumHi]; rw [hc0_eq]; push_cast; ring
    rw [hsplit, ← h2Be_eq]
    have htri := abs_add_le ((hPlus : ℝ) / (2 : ℝ) ^ B_e - E_plus) ((hMinus : ℝ) / (2 : ℝ) ^ B_e - E_minus)
    linarith
  have hroundHi := abs_divRoundRatInt_mul_two_pow_div_sub_le B (hPlus + hMinus) ((2 ^ B_e : ℕ) : ℤ) hdenBe_pos
  have hcastHi : ((hPlus + hMinus : ℤ) : ℝ) / (((2 ^ B_e : ℕ) : ℤ) : ℝ) = sumHi := by
    dsimp [sumHi]; push_cast; rfl
  rw [hcastHi] at hroundHi
  have hrawHi_err : |(rawHi : ℝ) / (2 : ℝ) ^ B - c0| ≤ (2 : ℝ) ^ (-(B : ℤ)) := by
    have htri := abs_add_le ((rawHi : ℝ) / (2 : ℝ) ^ B - sumHi) (sumHi - c0)
    rw [sub_add_sub_cancel] at htri
    linarith
  have hhi_clamp := abs_clampInt_unit_scaled_sub_le B rawHi c0 ((2 : ℝ) ^ (-(B : ℤ)))
    hc0_0 hc0_1 hrawHi_err
  set diffLo : ℝ := ((hThree - hMinus : ℤ) : ℝ) / (2 : ℝ) ^ B_e
  have hdiffLo_err : |diffLo - c1| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(B : ℤ)) := by
    have hsplit : diffLo - c1 =
        ((hThree : ℝ) / (2 : ℝ) ^ B_e - E_three) + -((hMinus : ℝ) / (2 : ℝ) ^ B_e - E_minus) := by
      dsimp [diffLo]; rw [hc1_eq]; push_cast; ring
    rw [hsplit, ← h2Be_eq]
    have htri := abs_add_le ((hThree : ℝ) / (2 : ℝ) ^ B_e - E_three) (-((hMinus : ℝ) / (2 : ℝ) ^ B_e - E_minus))
    rw [abs_neg] at htri
    linarith
  have hroundLo := abs_divRoundRatInt_mul_two_pow_div_sub_le B (hThree - hMinus) ((2 ^ B_e : ℕ) : ℤ) hdenBe_pos
  have hcastLo : ((hThree - hMinus : ℤ) : ℝ) / (((2 ^ B_e : ℕ) : ℤ) : ℝ) = diffLo := by
    dsimp [diffLo]; push_cast; rfl
  rw [hcastLo] at hroundLo
  have hc1_1 : c1 ≤ 1 := hc1_le_c0.trans hc0_1
  have hrawLo_err : |(rawLo : ℝ) / (2 : ℝ) ^ B - c1| ≤ (2 : ℝ) ^ (-(B : ℤ)) := by
    have htri := abs_add_le ((rawLo : ℝ) / (2 : ℝ) ^ B - diffLo) (diffLo - c1)
    rw [sub_add_sub_cancel] at htri
    linarith
  have hlo_clamp := abs_clampInt_unit_scaled_sub_le B rawLo c1 ((2 : ℝ) ^ (-(B : ℤ)))
    hc1_0 hc1_1 hrawLo_err
  have hlo_err_B : |(loInt : ℝ) / (2 : ℝ) ^ B - c1| ≤ (2 : ℝ) ^ (-(B : ℤ)) := by
    rcases le_total loClamp hiInt with hle | hle
    · have hmin : loInt = loClamp := min_eq_left hle
      rw [hmin]
      exact hlo_clamp.1
    · have hmin : loInt = hiInt := min_eq_right hle
      rw [hmin]
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
      have hle_r : (hiInt : ℝ) / (2 : ℝ) ^ B ≤ (loClamp : ℝ) / (2 : ℝ) ^ B :=
        div_le_div_of_nonneg_right (by exact_mod_cast hle) hpow_pos.le
      have h1 := abs_le.mp hhi_clamp.1
      have h2 := abs_le.mp hlo_clamp.1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hlo0 : 0 ≤ loInt := le_min hlo_clamp.2.1 hhi_clamp.2.1
  have hlo_le_hi : loInt ≤ hiInt := min_le_right _ _
  have hpowB_cast : ((2 ^ B : ℕ) : ℤ) = (2 : ℤ) ^ (pSub + 2) := by
    subst hB; push_cast; rfl
  have hhi_le : hiInt ≤ (2 : ℤ) ^ (pSub + 2) := hpowB_cast ▸ hhi_clamp.2.2
  have hlo_le : loInt ≤ (2 : ℤ) ^ (pSub + 2) := hlo_le_hi.trans hhi_le
  have hq_eq : (2 : ℝ) ^ (-(B : ℤ)) = 2 * realQuantizeMaxErr pSub := by
    unfold realQuantizeMaxErr
    subst hB
    push_cast
    ring
  have hhi_final : |(hiInt : ℝ) / (2 : ℝ) ^ (pSub + 2) - c0| ≤ 2 * realQuantizeMaxErr pSub := by
    rw [← hB, ← hq_eq]
    exact hhi_clamp.1
  have hlo_final : |(loInt : ℝ) / (2 : ℝ) ^ (pSub + 2) - c1| ≤ 2 * realQuantizeMaxErr pSub := by
    rw [← hB, ← hq_eq]
    exact hlo_err_B
  exact ⟨hhi_clamp.2.1, hhi_le, hlo0, hlo_le, hlo_le_hi, hhi_final, hlo_final⟩

/-- Scaled integer square-root accuracy: if `|(m : ℝ) / 2^(2*S) - u| ≤ K^2 * 2^(-2*S)` with `u ≥ 0` and `K ≥ 0`,
then `|(Nat.sqrt m : ℝ) / 2^S - √u| ≤ (K + 1) * 2^(-S)` and `(Nat.sqrt m : ℝ) / 2^S ≤ √u + K * 2^(-S)`. -/
theorem natSqrt_scaled_sub_sqrt_le (S m : ℕ) (u K : ℝ)
    (hu : 0 ≤ u) (hK : 0 ≤ K)
    (herr : |(m : ℝ) / (2 : ℝ) ^ (2 * S) - u| ≤ K ^ 2 * (2 : ℝ) ^ (-(2 * S : ℤ))) :
    |(Nat.sqrt m : ℝ) / (2 : ℝ) ^ S - Real.sqrt u| ≤ (K + 1) * (2 : ℝ) ^ (-(S : ℤ)) ∧
    (Nat.sqrt m : ℝ) / (2 : ℝ) ^ S ≤ Real.sqrt u + K * (2 : ℝ) ^ (-(S : ℤ)) := by
  set s : ℝ := (Nat.sqrt m : ℝ) / (2 : ℝ) ^ S
  set m_scaled : ℝ := (m : ℝ) / (2 : ℝ) ^ (2 * S)
  have hpowS_pos : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
  have hm_nonneg : 0 ≤ m_scaled := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hsqrt_m := natSqrt_le_realSqrt_and_le_succ m
  have hsqrt_scaled : Real.sqrt m_scaled = Real.sqrt (m : ℝ) / (2 : ℝ) ^ S := by
    dsimp [m_scaled]
    rw [two_mul, pow_add, ← sq, Real.sqrt_div (Nat.cast_nonneg m), Real.sqrt_sq hpowS_pos.le]
  have hs_le : s ≤ Real.sqrt m_scaled := by
    rw [hsqrt_scaled]
    exact div_le_div_of_nonneg_right hsqrt_m.1 hpowS_pos.le
  have hinv_S : 1 / (2 : ℝ) ^ S = (2 : ℝ) ^ (-(S : ℤ)) := by
    rw [one_div, zpow_neg, zpow_natCast]
  have hscaled_le : Real.sqrt m_scaled ≤ s + (2 : ℝ) ^ (-(S : ℤ)) := by
    rw [hsqrt_scaled, ← hinv_S]
    dsimp [s]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hsqrt_m.2 hpowS_pos.le
  have hs_diff : |s - Real.sqrt m_scaled| ≤ (2 : ℝ) ^ (-(S : ℤ)) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hpow2 : K ^ 2 * (2 : ℝ) ^ (-(2 * S : ℤ)) = (K * (2 : ℝ) ^ (-(S : ℤ))) ^ 2 := by
    rw [mul_pow, sq ((2 : ℝ) ^ (-(S : ℤ))), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 2
    omega
  have hK_nonneg : 0 ≤ K * (2 : ℝ) ^ (-(S : ℤ)) := mul_nonneg hK (by positivity)
  have hsqrt_diff : |Real.sqrt m_scaled - Real.sqrt u| ≤ K * (2 : ℝ) ^ (-(S : ℤ)) := by
    calc |Real.sqrt m_scaled - Real.sqrt u|
        ≤ Real.sqrt (|m_scaled - u|) := abs_sqrt_sub_sqrt_le m_scaled u hm_nonneg hu
      _ ≤ Real.sqrt (K ^ 2 * (2 : ℝ) ^ (-(2 * S : ℤ))) := Real.sqrt_le_sqrt herr
      _ = Real.sqrt ((K * (2 : ℝ) ^ (-(S : ℤ))) ^ 2) := by rw [hpow2]
      _ = K * (2 : ℝ) ^ (-(S : ℤ)) := Real.sqrt_sq hK_nonneg
  have htri := abs_add_le (s - Real.sqrt m_scaled) (Real.sqrt m_scaled - Real.sqrt u)
  rw [sub_add_sub_cancel] at htri
  have hsqrt_up : Real.sqrt m_scaled ≤ Real.sqrt u + K * (2 : ℝ) ^ (-(S : ℤ)) := by
    have := (abs_le.mp hsqrt_diff).2
    linarith
  refine ⟨?_, hs_le.trans hsqrt_up⟩
  linarith

/-- Quotient perturbation bound when both denominators are `≥ 1` and `0 ≤ I ≤ M`. -/
theorem abs_div_sub_div_of_ge_one (I_hat I p_hat p_true M : ℝ)
    (hp_hat : 1 ≤ p_hat) (hp_true : 1 ≤ p_true)
    (hI0 : 0 ≤ I) (hIM : I ≤ M) :
    |I_hat / p_hat - I / p_true| ≤ |I_hat - I| + M * |p_hat - p_true| := by
  have hp_hat_pos : 0 < p_hat := by linarith
  have hp_true_pos : 0 < p_true := by linarith
  have hsplit : I_hat / p_hat - I / p_true =
      (I_hat - I) / p_hat + (I / (p_hat * p_true)) * (p_true - p_hat) := by
    field_simp [hp_hat_pos.ne', hp_true_pos.ne']
    ring
  rw [hsplit]
  have htri := abs_add_le ((I_hat - I) / p_hat) ((I / (p_hat * p_true)) * (p_true - p_hat))
  have hprod_ge1 : 1 ≤ p_hat * p_true := by nlinarith
  have hdiv_nonneg : 0 ≤ I / (p_hat * p_true) := div_nonneg hI0 (by linarith)
  rw [abs_div, abs_of_pos hp_hat_pos, abs_mul, abs_of_nonneg hdiv_nonneg,
      abs_sub_comm p_true p_hat] at htri
  have h1 : |I_hat - I| / p_hat ≤ |I_hat - I| := div_le_self (abs_nonneg _) hp_hat
  have h2 : I / (p_hat * p_true) ≤ M := (div_le_self hI0 hprod_ge1).trans hIM
  have hm2 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (p_hat - p_true))
  linarith

/-- Bounds on the scaled square-root approximations `A = Nat.sqrt (4 * p_work * log2Nat)`
and `P = Nat.sqrt piNat` when `3 ≤ S`, including the quadratic bound
`((A : ℝ) / (2 : ℝ) ^ S) ^ 2 ≤ 8 * (p_work : ℝ)` from `Nat.sqrt_le`. -/
theorem natSqrt_pi_and_log2_bounds
    (p_work S piNat log2Nat A P : ℕ)
    (hp_work : 0 < p_work) (hS : 3 ≤ S)
    (hpi_err : |(piNat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.pi| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hlog2_err : |(log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.log 2| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hA : A = Nat.sqrt (4 * p_work * log2Nat))
    (hP : P = Nat.sqrt piNat) :
    0 < P ∧
    1 ≤ (P : ℝ) / (2 : ℝ) ^ S ∧
    1 ≤ Real.sqrt Real.pi ∧
    |(P : ℝ) / (2 : ℝ) ^ S - Real.sqrt Real.pi| ≤ 2 * (2 : ℝ) ^ (-(S : ℤ)) ∧
    |(A : ℝ) / (2 : ℝ) ^ S - Real.sqrt (4 * (p_work : ℝ) * Real.log 2)| ≤
      (2 * (p_work : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ)) ∧
    (A : ℝ) / (2 : ℝ) ^ S ≤ 4 * (p_work : ℝ) ∧
    ((A : ℝ) / (2 : ℝ) ^ S) ^ 2 ≤ 8 * (p_work : ℝ) ∧
    Real.sqrt (4 * (p_work : ℝ) * Real.log 2) ≤ 2 * (p_work : ℝ) := by
  have hpi_gt3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_ge_sq : (3 / 2 : ℝ) ^ 2 ≤ Real.pi := by linarith
  have hp_true_ge_32 : (3 / 2 : ℝ) ≤ Real.sqrt Real.pi := by
    have h := Real.sqrt_le_sqrt hpi_ge_sq
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  have hp_true_ge1 : 1 ≤ Real.sqrt Real.pi := by linarith
  have hpi_err1 : |(piNat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.pi| ≤ 1 ^ 2 * (2 : ℝ) ^ (-(2 * S : ℤ)) := by
    simpa using hpi_err
  have hP_sqrt := natSqrt_scaled_sub_sqrt_le S piNat Real.pi 1 Real.pi_pos.le zero_le_one hpi_err1
  rw [← hP] at hP_sqrt
  have hp_hat_diff : |(P : ℝ) / (2 : ℝ) ^ S - Real.sqrt Real.pi| ≤ 2 * (2 : ℝ) ^ (-(S : ℤ)) := by
    simpa [one_add_one_eq_two] using hP_sqrt.1
  have hS_pow_le : (2 : ℝ) ^ (-(S : ℤ)) ≤ 1 / 8 := by
    calc (2 : ℝ) ^ (-(S : ℤ)) ≤ (2 : ℝ) ^ (-3 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = 1 / 8 := by norm_num
  have hp_hat_ge1 : 1 ≤ (P : ℝ) / (2 : ℝ) ^ S := by
    have := (abs_le.mp hp_hat_diff).1
    linarith
  have hP_pos : 0 < P := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
    have h1 := (le_div_iff₀ hpow_pos).mp hp_hat_ge1
    have hlt : (0 : ℝ) < (P : ℝ) := by linarith
    exact Nat.cast_pos.mp hlt
  have hp_work_r : (1 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp_work
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hu_log_nonneg : 0 ≤ 4 * (p_work : ℝ) * Real.log 2 := by positivity
  have hsq_4p : 4 * (p_work : ℝ) ≤ (2 * (p_work : ℝ)) ^ 2 := by
    have heq : (2 * (p_work : ℝ)) ^ 2 = 4 * (p_work : ℝ) * (p_work : ℝ) := by ring
    rw [heq]
    exact le_mul_of_one_le_right (by positivity) hp_work_r
  have h4p_err :
      |((4 * p_work * log2Nat : ℕ) : ℝ) / (2 : ℝ) ^ (2 * S) - 4 * (p_work : ℝ) * Real.log 2| ≤
        (2 * (p_work : ℝ)) ^ 2 * (2 : ℝ) ^ (-(2 * S : ℤ)) := by
    have hsplit : ((4 * p_work * log2Nat : ℕ) : ℝ) / (2 : ℝ) ^ (2 * S) - 4 * (p_work : ℝ) * Real.log 2 =
        (4 * (p_work : ℝ)) * ((log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.log 2) := by
      push_cast; ring
    rw [hsplit, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * (p_work : ℝ))]
    exact (mul_le_mul_of_nonneg_left hlog2_err (by positivity)).trans
      (mul_le_mul_of_nonneg_right hsq_4p (by positivity))
  have hA_sqrt := natSqrt_scaled_sub_sqrt_le S (4 * p_work * log2Nat)
    (4 * (p_work : ℝ) * Real.log 2) (2 * (p_work : ℝ)) hu_log_nonneg (by positivity) h4p_err
  rw [← hA] at hA_sqrt
  have hsqrt_ulog_le : Real.sqrt (4 * (p_work : ℝ) * Real.log 2) ≤ 2 * (p_work : ℝ) := by
    have hle : 4 * (p_work : ℝ) * Real.log 2 ≤ (2 * (p_work : ℝ)) ^ 2 :=
      (mul_le_of_le_one_right (by positivity) hlog2_lt1.le).trans hsq_4p
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by positivity)] at h
  have hA_le : (A : ℝ) / (2 : ℝ) ^ S ≤ 4 * (p_work : ℝ) := by
    have h1 := hA_sqrt.2
    have h2 : 2 * (p_work : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) ≤ 2 * (p_work : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hA_sq_nat : A ^ 2 ≤ 4 * p_work * log2Nat := by
    rw [hA, sq]
    exact Nat.sqrt_le (4 * p_work * log2Nat)
  have h2S_pow_le1 : (2 : ℝ) ^ (-(2 * S : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hlog2_hat_le2 : (log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) ≤ 2 := by
    have := (abs_le.mp hlog2_err).2
    linarith
  have hA_sq_scaled : ((A : ℝ) / (2 : ℝ) ^ S) ^ 2 ≤ 8 * (p_work : ℝ) := by
    rw [div_pow, ← pow_mul, mul_comm S 2]
    have hpow2S_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * S) := by positivity
    calc (A : ℝ) ^ 2 / (2 : ℝ) ^ (2 * S)
        ≤ ((4 * p_work * log2Nat : ℕ) : ℝ) / (2 : ℝ) ^ (2 * S) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hA_sq_nat) hpow2S_pos.le
      _ = 4 * (p_work : ℝ) * ((log2Nat : ℝ) / (2 : ℝ) ^ (2 * S)) := by
          push_cast; ring
      _ ≤ 4 * (p_work : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left hlog2_hat_le2 (by positivity)
      _ = 8 * (p_work : ℝ) := by ring
  exact ⟨hP_pos, hp_hat_ge1, hp_true_ge1, hp_hat_diff, hA_sqrt.1, hA_le, hA_sq_scaled, hsqrt_ulog_le⟩

/-- Pure real-arithmetic bounds on the square-root and Taylor arguments for `computableHalfErfScaledInner`. -/
theorem erf_arg_and_sqrt_bounds
    (p_work B_e M_z M_z2 S N piNat log2Nat A P numX denX : ℕ)
    (hp_work : 0 < p_work) (hdenX : 0 < denX) (hnumX : numX ≤ 2 * denX)
    (hM_z : M_z = 8 * p_work + 1)
    (hM_z2 : M_z2 = 32 * p_work + 1)
    (hS : B_e + 2 * M_z + 6 ≤ S)
    (hN : 4 * M_z2 + B_e + M_z + 4 ≤ N)
    (hpi_err : |(piNat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.pi| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hlog2_err : |(log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.log 2| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hA : A = Nat.sqrt (4 * p_work * log2Nat))
    (hP : P = Nat.sqrt piNat) :
    let x : ℝ := (numX : ℝ) / (denX : ℝ)
    let z : ℝ := Real.sqrt (4 * (p_work : ℝ) * Real.log 2) * x
    let z_hat : ℝ := ((A * numX : ℕ) : ℝ) / ((denX * 2 ^ S : ℕ) : ℝ)
    let p_hat : ℝ := (P : ℝ) / (2 : ℝ) ^ S
    let p_true : ℝ := Real.sqrt Real.pi
    0 < P ∧
    1 ≤ p_hat ∧
    1 ≤ p_true ∧
    0 ≤ z_hat ∧
    z_hat ≤ (M_z : ℝ) ∧
    z_hat ^ 2 ≤ (M_z2 : ℝ) ∧
    z_hat * (z_hat ^ 2) ^ N / (N.factorial : ℝ) ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) ∧
    |(∫ t in (0 : ℝ)..z_hat, Real.exp (-(t ^ 2))) / p_hat -
      (∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))) / p_true| ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
  intro x z z_hat p_hat p_true
  obtain ⟨hP_pos, hp_hat_ge1, hp_true_ge1, hp_hat_diff, hA_diff, hA_le, hA_sq_scaled, hsqrt_ulog_le⟩ :=
    natSqrt_pi_and_log2_bounds p_work S piNat log2Nat A P hp_work (by omega) hpi_err hlog2_err hA hP
  clear hpi_err hlog2_err hA hP
  have hp_work_r : (1 : ℝ) ≤ (p_work : ℝ) := by exact_mod_cast hp_work
  have hx_nonneg : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hx_le2 : x ≤ 2 := by
    dsimp [x]
    rw [div_le_iff₀ (Nat.cast_pos.mpr hdenX)]
    exact_mod_cast hnumX
  have hz_hat_eq : z_hat = ((A : ℝ) / (2 : ℝ) ^ S) * x := by
    dsimp [z_hat, x]
    push_cast
    rw [div_mul_div_comm, mul_comm (denX : ℝ)]
  have hz_nonneg : 0 ≤ z := mul_nonneg (Real.sqrt_nonneg _) hx_nonneg
  have hz_hat_nonneg : 0 ≤ z_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hMz_r : 8 * (p_work : ℝ) + 1 = (M_z : ℝ) := by rw [hM_z]; push_cast; ring
  have hMz2_r : 32 * (p_work : ℝ) + 1 = (M_z2 : ℝ) := by rw [hM_z2]; push_cast; ring
  have hz_le_Mz : z ≤ (M_z : ℝ) := by
    have h1 : z ≤ (2 * (p_work : ℝ)) * 2 :=
      mul_le_mul hsqrt_ulog_le hx_le2 hx_nonneg (by positivity)
    linarith
  have hz_hat_le_Mz : z_hat ≤ (M_z : ℝ) := by
    have h1 : z_hat ≤ (4 * (p_work : ℝ)) * 2 := by
      rw [hz_hat_eq]
      exact mul_le_mul hA_le hx_le2 hx_nonneg (by positivity)
    linarith
  have hz_hat_sq_le : z_hat ^ 2 ≤ (M_z2 : ℝ) := by
    have hx_sq : x ^ 2 ≤ 4 := by nlinarith
    have h1 : z_hat ^ 2 ≤ (8 * (p_work : ℝ)) * 4 := by
      rw [hz_hat_eq, mul_pow]
      exact mul_le_mul hA_sq_scaled hx_sq (sq_nonneg x) (by positivity)
    linarith
  have hz_diff : |z_hat - z| ≤ (M_z : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hsub : z_hat - z = ((A : ℝ) / (2 : ℝ) ^ S - Real.sqrt (4 * (p_work : ℝ) * Real.log 2)) * x := by
      rw [hz_hat_eq]
      exact (sub_mul ((A : ℝ) / (2 : ℝ) ^ S) (Real.sqrt (4 * (p_work : ℝ) * Real.log 2)) x).symm
    rw [hsub, abs_mul, abs_of_nonneg hx_nonneg]
    calc |(A : ℝ) / (2 : ℝ) ^ S - Real.sqrt (4 * (p_work : ℝ) * Real.log 2)| * x
        ≤ ((2 * (p_work : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ))) * 2 :=
          mul_le_mul hA_diff hx_le2 hx_nonneg (by positivity)
      _ = (4 * (p_work : ℝ) + 2) * (2 : ℝ) ^ (-(S : ℤ)) := by ring
      _ ≤ (M_z : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hMz_pow : (M_z : ℝ) ≤ (2 : ℝ) ^ ((M_z : ℕ) : ℤ) := by
    rw [zpow_natCast]; exact_mod_cast Nat.lt_two_pow_self.le
  -- Taylor remainder bound at z_hat
  have htail_N := pow_div_factorial_le_two_zpow_neg M_z2 (B_e + M_z + 3) N (by omega)
    (z_hat ^ 2) (sq_nonneg _) hz_hat_sq_le
  have hz_hat_pow : z_hat ≤ (2 : ℝ) ^ ((M_z : ℕ) : ℤ) := hz_hat_le_Mz.trans hMz_pow
  have hrem_bound :
      z_hat * (z_hat ^ 2) ^ N / (N.factorial : ℝ) ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
    rw [mul_div_assoc]
    calc z_hat * ((z_hat ^ 2) ^ N / (N.factorial : ℝ))
        ≤ (2 : ℝ) ^ ((M_z : ℕ) : ℤ) * (2 : ℝ) ^ (-((B_e + M_z + 3 : ℕ) : ℤ)) :=
          mul_le_mul hz_hat_pow htail_N (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (((M_z : ℕ) : ℤ) + -((B_e + M_z + 3 : ℕ) : ℤ)) :=
          (zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _).symm
      _ ≤ (2 : ℝ) ^ ((-3 : ℤ) + -(B_e : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  -- Quotient perturbation bound between z_hat / p_hat and z / p_true
  set I_zhat : ℝ := ∫ t in (0 : ℝ)..z_hat, Real.exp (-(t ^ 2))
  set I_z : ℝ := ∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2))
  have hIz_nonneg : 0 ≤ I_z :=
    intervalIntegral.integral_nonneg hz_nonneg fun t _ => (Real.exp_pos _).le
  have hIz_le_z : I_z ≤ z := by
    have h0 := abs_erfIntegral_sub_le z 0 hz_nonneg le_rfl
    rw [intervalIntegral.integral_same, sub_zero, sub_zero,
        abs_of_nonneg hIz_nonneg, abs_of_nonneg hz_nonneg] at h0
    exact h0
  have hIz_le_Mz : I_z ≤ (M_z : ℝ) := hIz_le_z.trans hz_le_Mz
  have hI_diff : |I_zhat - I_z| ≤ (M_z : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) :=
    (abs_erfIntegral_sub_le z_hat z hz_hat_nonneg hz_nonneg).trans hz_diff
  have hquot := abs_div_sub_div_of_ge_one I_zhat I_z p_hat p_true (M_z : ℝ)
    hp_hat_ge1 hp_true_ge1 hIz_nonneg hIz_le_Mz
  have h3_le : (3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℤ) := by norm_num
  have hquot_bound : |I_zhat / p_hat - I_z / p_true| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
    calc |I_zhat / p_hat - I_z / p_true|
        ≤ |I_zhat - I_z| + (M_z : ℝ) * |p_hat - p_true| := hquot
      _ ≤ (M_z : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) +
            (M_z : ℝ) * (2 * (2 : ℝ) ^ (-(S : ℤ))) :=
          add_le_add hI_diff (mul_le_mul_of_nonneg_left hp_hat_diff (Nat.cast_nonneg _))
      _ = 3 * (M_z : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) := by ring
      _ ≤ (2 : ℝ) ^ (2 : ℤ) * (2 : ℝ) ^ ((M_z : ℕ) : ℤ) * (2 : ℝ) ^ (-(S : ℤ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h3_le hMz_pow (Nat.cast_nonneg _) (by positivity)) (by positivity)
      _ = (2 : ℝ) ^ ((2 : ℤ) + ((M_z : ℕ) : ℤ) + -(S : ℤ)) := by
          simp only [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_assoc]
      _ ≤ (2 : ℝ) ^ ((-3 : ℤ) + -(B_e : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  exact ⟨hP_pos, hp_hat_ge1, hp_true_ge1, hz_hat_nonneg, hz_hat_le_Mz, hz_hat_sq_le, hrem_bound, hquot_bound⟩

/-- Combined accuracy, call-site width soundness, and sum-magnitude bound for the
recurrence-based `erfIntegralTaylorSum` evaluator. -/
theorem erf_recurrence_spec_and_widths
    (Bint M_z M_z2 D w N numZ denZ : ℕ)
    (hden : 0 < denZ)
    (hz_le : (numZ : ℝ) / (denZ : ℝ) ≤ (M_z : ℝ))
    (hz_sq_le : ((numZ : ℝ) / (denZ : ℝ)) ^ 2 ≤ (M_z2 : ℝ))
    (hnum_sq : ((numZ ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hden_sq : ((denZ ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D)
    (hw : Bint + 2 * (M_z2 + M_z) + 4 * N + D + 9 ≤ w) :
    let a0 := divRoundRatInt ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denZ : ℤ)
    let seriesRes := runRecurrenceSeriesCosted w a0
      (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2) (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N
    |(seriesRes.1.2 : ℝ) / (2 : ℝ) ^ Bint - erfIntegralTaylorSum N ((numZ : ℝ) / (denZ : ℝ))| ≤
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (2 * (M_z2 + M_z)) * (2 : ℝ) ^ (-(Bint : ℤ)) ∧
    RecurrenceCallSitesWidthSound w a0
      (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2) (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N ∧
    |(seriesRes.1.2 : ℝ)| ≤ (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + 3) := by
  intro a0 seriesRes
  set z_hat : ℝ := (numZ : ℝ) / (denZ : ℝ)
  have hz_nonneg : 0 ≤ z_hat := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set exactA : ℕ → ℝ :=
    fun k => (-1 : ℝ) ^ k * z_hat ^ (2 * k + 1) / ((k.factorial : ℝ) * (2 * (k : ℝ) + 1))
  have hden_sq_pos : 0 < denZ ^ 2 := pow_pos hden 2
  have hsf_pos : ∀ k, 0 < (k + 1) * (2 * k + 3) := fun k => by positivity
  have ha0 : |(a0 : ℝ) - exactA 0 * (2 : ℝ) ^ Bint| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 0 := by
    have hq := abs_divRoundRatInt_sub_div_le ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denZ : ℤ)
      (by exact_mod_cast hden)
    have heq : (((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ) : ℤ) : ℝ) / ((denZ : ℤ) : ℝ) =
        exactA 0 * (2 : ℝ) ^ Bint := by
      dsimp [exactA, z_hat]
      push_cast
      ring
    rw [heq] at hq
    simpa [a0] using hq
  have hrec : ∀ k, exactA (k + 1) =
      exactA k * (((-((numZ ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) /
        ((((k + 1) * (2 * k + 3) : ℕ) : ℝ) * ((denZ ^ 2 : ℕ) : ℝ)) := by
    intro k
    dsimp [exactA, z_hat]
    have hpow : z_hat ^ (2 * (k + 1) + 1) =
        z_hat ^ (2 * k + 1) * ((numZ : ℝ) ^ 2 / (denZ : ℝ) ^ 2) := by
      have h2k : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [h2k, pow_add, div_pow (numZ : ℝ) (denZ : ℝ) 2]
    have h2k3 : 2 * ((k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 3 : ℕ) : ℝ) := by push_cast; ring
    have hden_ne : (denZ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hden).ne'
    have hfact_ne : (k.factorial : ℝ) ≠ 0 := by positivity
    have h2k1_ne : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have hsf_ne : (((k + 1) * (2 * k + 3) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [pow_succ (-1 : ℝ), hpow, Nat.factorial_succ, h2k3]
    push_cast
    field_simp [hden_ne, hfact_ne, h2k1_ne, hsf_ne]
    ring
  have hA_bound : ∀ k, |exactA k| ≤ (2 : ℝ) ^ (2 * (M_z2 + M_z)) := by
    intro k
    dsimp [exactA]
    rw [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (pow_nonneg hz_nonneg _),
        abs_of_pos (by positivity)]
    have hpow_split : z_hat ^ (2 * k + 1) = z_hat * (z_hat ^ 2) ^ k := by
      rw [pow_succ', ← pow_mul]
    have h2k1_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hden_ge : (k.factorial : ℝ) ≤ (k.factorial : ℝ) * (2 * (k : ℝ) + 1) :=
      le_mul_of_one_le_right (by positivity) h2k1_ge1
    have hz_pow : z_hat ≤ (2 : ℝ) ^ (2 * M_z) := by
      have h1 : (M_z : ℝ) ≤ (2 : ℝ) ^ M_z := by exact_mod_cast Nat.lt_two_pow_self.le
      have h2 : (2 : ℝ) ^ M_z ≤ (2 : ℝ) ^ (2 * M_z) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact hz_le.trans (h1.trans h2)
    have hsq_fact : (z_hat ^ 2) ^ k / (k.factorial : ℝ) ≤ (2 : ℝ) ^ (2 * M_z2) :=
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) hz_sq_le k) (by positivity)).trans
        (pow_div_factorial_le_two_pow_linear M_z2 k)
    calc z_hat ^ (2 * k + 1) / ((k.factorial : ℝ) * (2 * (k : ℝ) + 1))
        ≤ z_hat ^ (2 * k + 1) / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
      _ = z_hat * ((z_hat ^ 2) ^ k / (k.factorial : ℝ)) := by
          rw [hpow_split, mul_div_assoc]
      _ ≤ (2 : ℝ) ^ (2 * M_z) * (2 : ℝ) ^ (2 * M_z2) :=
          mul_le_mul hz_pow hsq_fact (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * (M_z2 + M_z)) := by rw [← pow_add, show 2 * M_z + 2 * M_z2 = 2 * (M_z2 + M_z) by omega]
  have hprod_bound : ∀ i k, i ≤ k →
      prodStepRatio (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2)
        (fun j => 2 * j + 1) (fun j => (j + 1) * (2 * j + 3)) i k ≤ (2 : ℝ) ^ (2 * (M_z2 + M_z)) := by
    intro i k hik
    refine prodStepRatio_le_two_pow_of_linear_step _ _ _ _ (M_z2 + M_z) i k hden_sq_pos hsf_pos ?_ ?_
    · rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      rw [← div_pow]
      exact hz_sq_le.trans (by exact_mod_cast Nat.le_add_right M_z2 M_z)
    · intro j
      push_cast
      nlinarith
  have herr := abs_runRecurrenceSeriesCosted_div_sub_sum_le Bint 0 (M_z2 + M_z) w
    a0 (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2)
    (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hprod_bound
  rw [pow_zero, mul_one] at herr
  have hw_sound := recurrenceCallSitesWidthSound_of_bounds Bint 0 (M_z2 + M_z) D w
    a0 (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2)
    (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) exactA N
    hden_sq_pos hsf_pos ha0 hrec hA_bound hprod_bound
    (by rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; exact hnum_sq)
    hden_sq
    (fun k hk => by exact_mod_cast (step_quad_le_two_pow N k hk).2.1)
    (fun k hk => by exact_mod_cast (step_quad_le_two_pow N k hk).2.2.2.2.2)
    (by omega)
  exact ⟨herr, hw_sound.1, hw_sound.2⟩

/-- Inner computable evaluator for `(1 / 2) * realErfScaled (alphaSchedule p_work) (numX / denX)`
at scale `2^B_e`, taking precomputed square-root approximations `A` and `P` as free `ℕ` variables.
All multi-precision multiplications (`A * numX`, `numZ^2`, `denZ^2`, and the series recurrence)
go through `costedMulInt w` and `costedDivRoundRatInt w`. -/
def computableHalfErfScaledInner (B_e S N Bint w A P numX denX : ℕ) : BitCostM ℤ :=
  let numZRes := costedMulInt w (A : ℤ) (numX : ℤ)
  let numZ : ℕ := numZRes.1.toNat
  let denZRes := costedShiftLeftNat w denX S
  let denZ : ℕ := denZRes.1
  let numZSqRes := costedMulInt w (numZ : ℤ) (numZ : ℤ)
  let negNumZSqRes := costedNegInt0 numZSqRes.1
  let negNumZSq : ℤ := negNumZSqRes.1
  let denZSqRes := costedMulInt w (denZ : ℤ) (denZ : ℤ)
  let denZSq : ℕ := denZSqRes.1.toNat
  let a0ShiftRes := costedShiftLeftInt w (numZ : ℤ) Bint
  let a0Res := costedDivRoundRatInt w a0ShiftRes.1 (denZ : ℤ)
  let erfSeriesRes := runRecurrenceSeriesCosted w a0Res.1
    negNumZSq denZSq (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N
  let outShift1Res := costedShiftLeftInt w erfSeriesRes.1.2 S
  let outShift2Res := costedShiftLeftInt w outShift1Res.1 B_e
  let outDenRes := costedShiftLeftNat w P Bint
  let outRes := costedDivRoundRatInt w outShift2Res.1 (outDenRes.1 : ℤ)
  (outRes.1,
    numZRes.2 + denZRes.2 + numZSqRes.2 + denZSqRes.2 +
    a0ShiftRes.2 + a0Res.2 + erfSeriesRes.2 +
    outShift1Res.2 + outShift2Res.2 + outDenRes.2 + outRes.2)

theorem computableHalfErfScaledInner_snd (B_e S N Bint w A P numX denX : ℕ) :
    (computableHalfErfScaledInner B_e S N Bint w A P numX denX).2 =
      computableMulBitCost w + addBitCost w + computableMulBitCost w + computableMulBitCost w +
      addBitCost w + (2 * computableMulBitCost w + 2 * addBitCost w) +
      (N * (6 * computableMulBitCost w + 3 * addBitCost w)) +
      addBitCost w + addBitCost w + addBitCost w +
      (2 * computableMulBitCost w + 2 * addBitCost w) := by
  dsimp only [computableHalfErfScaledInner, costedShiftLeftNat, costedShiftLeftInt, costedMulInt, costedDivRoundRatInt]
  rw [runRecurrenceSeriesCosted_snd]

/-- Accuracy theorem for `computableHalfErfScaledInner`. -/
theorem computableHalfErfScaledInner_spec
    (p_work B_e M_z M_z2 S N Bint w piNat log2Nat A P numX denX : ℕ)
    (hp_work : 0 < p_work) (hdenX : 0 < denX) (hnumX : numX ≤ 2 * denX)
    (hM_z : M_z = 8 * p_work + 1)
    (hM_z2 : M_z2 = 32 * p_work + 1)
    (hS : B_e + 2 * M_z + 6 ≤ S)
    (hN : 4 * M_z2 + B_e + M_z + 4 ≤ N)
    (hBint : B_e + 2 * N + 2 * (M_z2 + M_z) + 4 ≤ Bint)
    (hpi_err : |(piNat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.pi| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hlog2_err : |(log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.log 2| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hA : A = Nat.sqrt (4 * p_work * log2Nat))
    (hP : P = Nat.sqrt piNat) :
    let outInt := (computableHalfErfScaledInner B_e S N Bint w A P numX denX).1
    |(outInt : ℝ) / (2 : ℝ) ^ B_e -
      (1 / 2 : ℝ) * realErfScaled (alphaSchedule p_work) ((numX : ℝ) / (denX : ℝ))| ≤
      (2 : ℝ) ^ (-(B_e : ℤ)) := by
  dsimp only [computableHalfErfScaledInner, costedMulInt, costedDivRoundRatInt]
  have hnumZ_eq : ((A : ℤ) * (numX : ℤ)).toNat = A * numX := by
    rw [← Nat.cast_mul, Int.toNat_natCast]
  have hnumZ_sq_eq : (((A * numX : ℕ) : ℤ) * ((A * numX : ℕ) : ℤ)) = (((A * numX) ^ 2 : ℕ) : ℤ) := by
    push_cast; ring
  have hdenZ_sq_eq : (((denX * 2 ^ S : ℕ) : ℤ) * ((denX * 2 ^ S : ℕ) : ℤ)).toNat = (denX * 2 ^ S) ^ 2 := by
    rw [← Nat.cast_mul, Int.toNat_natCast, sq]
  rw [hnumZ_eq, hnumZ_sq_eq, hdenZ_sq_eq]
  have hbounds := erf_arg_and_sqrt_bounds p_work B_e M_z M_z2 S N piNat log2Nat A P numX denX
    hp_work hdenX hnumX hM_z hM_z2 hS hN hpi_err hlog2_err hA hP
  obtain ⟨hP_pos, hp_hat_ge1, _hp_true_ge1, hz_hat_nonneg, hz_hat_le, hz_hat_sq_le, hrem_bound, hquot_bound⟩ := hbounds
  set numZ : ℕ := A * numX
  set denZ : ℕ := denX * 2 ^ S
  have hdenZ_pos : 0 < denZ := Nat.mul_pos hdenX (pow_pos zero_lt_two S)
  set z_hat : ℝ := (numZ : ℝ) / (denZ : ℝ)
  set p_hat : ℝ := (P : ℝ) / (2 : ℝ) ^ S
  have hp_hat_pos : 0 < p_hat := by linarith
  have hBe_zpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(B_e : ℤ)) := by positivity
  have hN_Bint := recurrence_rounding_error_le_eighth B_e N 0 (M_z2 + M_z) Bint (by omega)
  set D0 := numZ ^ 2 + denZ ^ 2
  have hnum_sq_D0 : ((numZ ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D0 := by
    exact_mod_cast (Nat.le_add_right _ _).trans Nat.lt_two_pow_self.le
  have hden_sq_D0 : ((denZ ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D0 := by
    exact_mod_cast (Nat.le_add_left _ _).trans Nat.lt_two_pow_self.le
  have herf_rec := erf_recurrence_spec_and_widths Bint M_z M_z2 D0
    (max w (Bint + 2 * (M_z2 + M_z) + 4 * N + D0 + 9)) N numZ denZ
    hdenZ_pos hz_hat_le hz_hat_sq_le hnum_sq_D0 hden_sq_D0 (le_max_right _ _)
  set a0 := divRoundRatInt ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denZ : ℤ)
  have hfst_eq :
      (runRecurrenceSeriesCosted w a0
        (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2)
        (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N).1.2 =
      (runRecurrenceSeriesCosted (max w (Bint + 2 * (M_z2 + M_z) + 4 * N + D0 + 9)) a0
        (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2)
        (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N).1.2 := by
    rw [runRecurrenceSeriesCosted_fst_snd_eq_sum, runRecurrenceSeriesCosted_fst_snd_eq_sum]
  set erfSumVal := (runRecurrenceSeriesCosted w a0
    (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2)
    (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N).1.2
  have herf_sum_err :
      |(erfSumVal : ℝ) / (2 : ℝ) ^ Bint - erfIntegralTaylorSum N z_hat| ≤
        (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
    rw [hfst_eq]
    exact herf_rec.1.trans (by simpa using hN_Bint)
  set I_hat : ℝ := (erfSumVal : ℝ) / (2 : ℝ) ^ Bint
  set T_hat : ℝ := erfIntegralTaylorSum N z_hat
  set I_zhat : ℝ := ∫ t in (0 : ℝ)..z_hat, Real.exp (-(t ^ 2))
  have hstep2 : |I_hat / p_hat - T_hat / p_hat| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
    rw [← sub_div, abs_div, abs_of_pos hp_hat_pos]
    exact (div_le_self (abs_nonneg _) hp_hat_ge1).trans herf_sum_err
  have hstep3 : |T_hat / p_hat - I_zhat / p_hat| ≤ (1 / 8 : ℝ) * (2 : ℝ) ^ (-(B_e : ℤ)) := by
    rw [← sub_div, abs_div, abs_of_pos hp_hat_pos, abs_sub_comm]
    exact (div_le_self (abs_nonneg _) hp_hat_ge1).trans
      ((abs_erfIntegral_sub_taylorSum_le N z_hat hz_hat_nonneg).trans hrem_bound)
  generalize hDenOut : ((P * 2 ^ Bint : ℕ) : ℤ) = denOut
  have hdenOut_pos : 0 < denOut := by subst hDenOut; positivity
  have hout_q := abs_divRoundRatInt_mul_two_pow_div_sub_le B_e
    (erfSumVal * ((2 ^ S : ℕ) : ℤ)) denOut hdenOut_pos
  generalize hOutInt : divRoundRatInt ((erfSumVal * ((2 ^ S : ℕ) : ℤ)) * ((2 ^ B_e : ℕ) : ℤ)) denOut = outInt at hout_q ⊢
  have hcast_out : ((erfSumVal * ((2 ^ S : ℕ) : ℤ) : ℤ) : ℝ) / (denOut : ℝ) = I_hat / p_hat := by
    subst hDenOut
    dsimp [I_hat, p_hat]
    push_cast
    have hP_ne : (P : ℝ) ≠ 0 := (Nat.cast_pos.mpr hP_pos).ne'
    have hpowS_ne : (2 : ℝ) ^ S ≠ 0 := by positivity
    have hpowBint_ne : (2 : ℝ) ^ Bint ≠ 0 := by positivity
    field_simp [hP_ne, hpowS_ne, hpowBint_ne]
  rw [hcast_out] at hout_q
  rw [half_realErfScaled_alphaSchedule_eq p_work hp_work ((numX : ℝ) / (denX : ℝ))]
  exact abs_sub_le_of_four_step_approx _ _ _ _ _ ((2 : ℝ) ^ (-(B_e : ℤ))) hBe_zpow
    hout_q hstep2 hstep3 hquot_bound

/-- Branch dispatch for `(c0_pair, c1_pair)` across `2 * u2 < r`, `2 * u2 = r`, and `r < 2 * u2`. -/
theorem c0_c1_branch_dispatch_spec
    (pSub r u2 : ℕ) (hiInt loInt : ℤ) (α : ℝ)
    (hr : 0 < r) (hu2 : u2 < r) (_hα : 0 < α)
    (hhi0 : 0 ≤ hiInt) (hhiB : hiInt ≤ (2 : ℤ) ^ (pSub + 2))
    (hlo0 : 0 ≤ loInt) (hloB : loInt ≤ (2 : ℤ) ^ (pSub + 2))
    (hlo_le_hi : loInt ≤ hiInt)
    (hhi_err : |(hiInt : ℝ) / (2 : ℝ) ^ (pSub + 2) -
      c0Coeff (realErfScaled α) (((min u2 (r - u2) : ℕ) : ℝ) / (r : ℝ))| ≤
      2 * realQuantizeMaxErr pSub)
    (hlo_err : |(loInt : ℝ) / (2 : ℝ) ^ (pSub + 2) -
      c1Coeff (realErfScaled α) (((min u2 (r - u2) : ℕ) : ℝ) / (r : ℝ))| ≤
      2 * realQuantizeMaxErr pSub) :
    let res : (ℤ × ℤ) × (ℤ × ℤ) :=
      if 2 * u2 < r then ((hiInt, 0), (loInt, 0))
      else if 2 * u2 = r then ((hiInt, 0), (hiInt, 0))
      else ((loInt, 0), (hiInt, 0))
    let c0_pair := res.1
    let c1_pair := res.2
    let y : ℝ := (u2 : ℝ) / (r : ℝ)
    c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
    0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
    (2 * u2 = r → c1_pair = c0_pair) ∧
    (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1) := by
  intro res c0_pair c1_pair y
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  rcases lt_trichotomy (2 * u2) r with hlt | heq | hgt
  · have hmin : min u2 (r - u2) = u2 := Nat.min_eq_left (by omega)
    rw [hmin] at hhi_err hlo_err
    have hres : res = ((hiInt, 0), (loInt, 0)) := if_pos hlt
    dsimp [c0_pair, c1_pair]
    rw [hres]
    refine ⟨rfl, rfl, hhi0, hhiB, hlo0, hloB, hhi_err, hlo_err,
      fun _ => hlo_le_hi, fun h => by omega, fun h => by omega⟩
  · have hmin : min u2 (r - u2) = u2 := Nat.min_eq_left (by omega)
    rw [hmin] at hhi_err
    have hy_half : y = 1 / 2 := by
      dsimp [y]
      rw [div_eq_iff hr_pos.ne']
      have hr_eq : (r : ℝ) = 2 * (u2 : ℝ) := by exact_mod_cast heq.symm
      linarith
    have hnyq := theorem3_nyquist_passband_eq (realErfScaled α) (realErfScaled_zero α)
    have hc1_eq_c0 : c1Coeff (realErfScaled α) y = c0Coeff (realErfScaled α) y := by
      rw [hy_half]
      exact hnyq.2.trans hnyq.1.symm
    have hres : res = ((hiInt, 0), (hiInt, 0)) := by
      dsimp [res]
      rw [if_neg (by omega), if_pos heq]
    dsimp [c0_pair, c1_pair]
    rw [hres]
    refine ⟨rfl, rfl, hhi0, hhiB, hhi0, hhiB, hhi_err, ?_,
      fun h => by omega, fun _ => rfl, fun h => by omega⟩
    change |(hiInt : ℝ) / (2 : ℝ) ^ (pSub + 2) - c1Coeff (realErfScaled α) y| ≤ _
    rw [hc1_eq_c0]
    exact hhi_err
  · have hmin : min u2 (r - u2) = r - u2 := Nat.min_eq_right (by omega)
    rw [hmin] at hhi_err hlo_err
    have hy'_eq : (((r - u2 : ℕ) : ℝ) / (r : ℝ)) = 1 - y := by
      dsimp [y]
      rw [Nat.cast_sub hu2.le, sub_div, div_self hr_pos.ne']
    rw [hy'_eq] at hhi_err hlo_err
    have hsym0 : c0Coeff (realErfScaled α) (1 - y) = c1Coeff (realErfScaled α) y := rfl
    have hsym1 : c1Coeff (realErfScaled α) (1 - y) = c0Coeff (realErfScaled α) y := by
      unfold c0Coeff c1Coeff; congr 1; ring
    rw [hsym0] at hhi_err
    rw [hsym1] at hlo_err
    have hres : res = ((loInt, 0), (hiInt, 0)) := by
      dsimp [res]
      rw [if_neg (by omega), if_neg (by omega)]
    dsimp [c0_pair, c1_pair]
    rw [hres]
    exact ⟨rfl, rfl, hlo0, hloB, hhi0, hhiB, hlo_err, hhi_err,
      fun h => by omega, fun h => by omega, fun _ => hlo_le_hi⟩

/-- Inner computable evaluator for `(c0, c1)` taking precomputed square-root approximations `A` and `P`. -/
def computableC0C1Inner
    (_pSub B B_e S N Bint w r u2 A P : ℕ) : BitCostM ((ℤ × ℤ) × (ℤ × ℤ)) :=
  let u2' : ℕ := min u2 (r - u2)
  let denX : ℕ := 2 * r
  let hPlus := computableHalfErfScaledInner B_e S N Bint w A P (r + 2 * u2') denX
  let hMinus := computableHalfErfScaledInner B_e S N Bint w A P (r - 2 * u2') denX
  let hThree := computableHalfErfScaledInner B_e S N Bint w A P (3 * r - 2 * u2') denX
  let hiShift := costedAddShiftLeftInt w hPlus.1 hMinus.1 B
  let rawHi := costedDivRoundRatInt w hiShift.1 ((2 ^ B_e : ℕ) : ℤ)
  let hiClamp := costedClampInt w 0 ((2 ^ B : ℕ) : ℤ) rawHi.1
  let hiInt : ℤ := hiClamp.1
  let loShift := costedSubShiftLeftInt w hThree.1 hMinus.1 B
  let rawLo := costedDivRoundRatInt w loShift.1 ((2 ^ B_e : ℕ) : ℤ)
  let loClamp := costedClampInt w 0 ((2 ^ B : ℕ) : ℤ) rawLo.1
  let loInt : ℤ := min loClamp.1 hiInt
  let outPair : (ℤ × ℤ) × (ℤ × ℤ) :=
    if 2 * u2 < r then ((hiInt, 0), (loInt, 0))
    else if 2 * u2 = r then ((hiInt, 0), (hiInt, 0))
    else ((loInt, 0), (hiInt, 0))
  (outPair,
    hPlus.2 + hMinus.2 + hThree.2 +
    hiShift.2 + rawHi.2 + hiClamp.2 + loShift.2 + rawLo.2 + loClamp.2 + 4 * addBitCost w)

/-- Core computable evaluator for `(c0, c1)` parameterized by `(B B_e S N Bint w : ℕ)`.
The product `4 * p_work * log2Nat` before `costedNatSqrt w` is charged via `costedMulInt w`. -/
def computableC0C1Core
    (p_work pSub B B_e S N Bint w r u2 : ℕ) : BitCostM ((ℤ × ℤ) × (ℤ × ℤ)) :=
  let piRes := computablePiScaledWithCost (2 * S)
  let log2Res := computableLog2ScaledWithCost (2 * S)
  let pLogRes := costedMulInt w ((4 * p_work : ℕ) : ℤ) (log2Res.1.toNat : ℤ)
  let sqrtLogRes := costedNatSqrt w pLogRes.1.toNat
  let sqrtPiRes := costedNatSqrt w piRes.1.toNat
  let innerRes := computableC0C1Inner pSub B B_e S N Bint w r u2 sqrtLogRes.1 sqrtPiRes.1
  (innerRes.1,
    piRes.2 + log2Res.2 + pLogRes.2 + sqrtLogRes.2 + sqrtPiRes.2 + innerRes.2)

/-- Computable fixed-point evaluator for the primary and secondary passband coefficients
`(c0Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r), c1Coeff (realErfScaled (alphaSchedule p_work)) (u2 / r))`
represented as Gaussian integers at scale `2^(pSub + 2)` (`toScaledComplex pSub`). -/
def computableC0C1WithProgramCost (p_work pSub r u2 : ℕ) : BitCostM ((ℤ × ℤ) × (ℤ × ℤ)) :=
  let B := pSub + 2
  let B_e := B + 2
  let M_z := 8 * p_work + 1
  let M_z2 := 32 * p_work + 1
  let M_erf := M_z2 + M_z
  let S := B_e + 2 * M_z + 6
  let N := 4 * M_z2 + B_e + M_z + 4
  let Bint := B_e + 2 * N + 2 * M_erf + 6
  let w := Bint + 4 * N + 2 * M_erf + 2 * S + B_e + 2 * p_work + 2 * Nat.log2 r + 40
  computableC0C1Core p_work pSub B B_e S N Bint w r u2

/-- Accuracy theorem for `computableC0C1Inner`. -/
theorem computableC0C1Inner_spec
    (p_work pSub B B_e M_z M_z2 S N Bint w r u2 piNat log2Nat A P : ℕ)
    (hB : B = pSub + 2) (hBe : B_e = B + 2)
    (hM_z : M_z = 8 * p_work + 1) (hM_z2 : M_z2 = 32 * p_work + 1)
    (hS : B_e + 2 * M_z + 6 ≤ S)
    (hN : 4 * M_z2 + B_e + M_z + 4 ≤ N)
    (hBint : B_e + 2 * N + 2 * (M_z2 + M_z) + 4 ≤ Bint)
    (hp_work : 0 < p_work) (hr : 0 < r) (hu2 : u2 < r)
    (hpi_err : |(piNat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.pi| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hlog2_err : |(log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.log 2| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hA : A = Nat.sqrt (4 * p_work * log2Nat))
    (hP : P = Nat.sqrt piNat) :
    let res := (computableC0C1Inner pSub B B_e S N Bint w r u2 A P).1
    let c0_pair := res.1
    let c1_pair := res.2
    let α := alphaSchedule p_work
    let y : ℝ := (u2 : ℝ) / (r : ℝ)
    c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
    0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
    (2 * u2 = r → c1_pair = c0_pair) ∧
    (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1) := by
  dsimp only [computableC0C1Inner, costedClampInt, costedDivRoundRatInt]
  set u2' : ℕ := min u2 (r - u2)
  have hu2'_le : 2 * u2' ≤ r := by omega
  have hdenX : 0 < 2 * r := by omega
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  set y' : ℝ := (u2' : ℝ) / (r : ℝ)
  have hy'0 : 0 ≤ y' := div_nonneg (Nat.cast_nonneg _) hr_pos.le
  have hy'_half : y' ≤ 1 / 2 := by
    dsimp [y']
    rw [div_le_iff₀ hr_pos]
    have : 2 * (u2' : ℝ) ≤ (r : ℝ) := by exact_mod_cast hu2'_le
    linarith
  have harg_plus : ((r + 2 * u2' : ℕ) : ℝ) / ((2 * r : ℕ) : ℝ) = y' + 1 / 2 := by
    dsimp [y']; push_cast; field_simp [hr_pos.ne']; ring
  have harg_minus : ((r - 2 * u2' : ℕ) : ℝ) / ((2 * r : ℕ) : ℝ) = 1 / 2 - y' := by
    dsimp [y']; rw [Nat.cast_sub hu2'_le]; push_cast; field_simp [hr_pos.ne']
  have harg_three : ((3 * r - 2 * u2' : ℕ) : ℝ) / ((2 * r : ℕ) : ℝ) = 3 / 2 - y' := by
    dsimp [y']; rw [Nat.cast_sub (by omega : 2 * u2' ≤ 3 * r)]; push_cast; field_simp [hr_pos.ne']
  have hP_spec := computableHalfErfScaledInner_spec p_work B_e M_z M_z2 S N Bint w
    piNat log2Nat A P (r + 2 * u2') (2 * r) hp_work hdenX (by omega)
    hM_z hM_z2 hS hN hBint hpi_err hlog2_err hA hP
  have hM_spec := computableHalfErfScaledInner_spec p_work B_e M_z M_z2 S N Bint w
    piNat log2Nat A P (r - 2 * u2') (2 * r) hp_work hdenX (by omega)
    hM_z hM_z2 hS hN hBint hpi_err hlog2_err hA hP
  have hT_spec := computableHalfErfScaledInner_spec p_work B_e M_z M_z2 S N Bint w
    piNat log2Nat A P (3 * r - 2 * u2') (2 * r) hp_work hdenX (by omega)
    hM_z hM_z2 hS hN hBint hpi_err hlog2_err hA hP
  rw [harg_plus] at hP_spec
  rw [harg_minus] at hM_spec
  rw [harg_three] at hT_spec
  have hα_pos : 0 < alphaSchedule p_work := alphaSchedule_pos p_work hp_work
  have hc_bounds := c0Coeff_and_c1Coeff_realErfScaled_bounds (alphaSchedule p_work) y'
    hα_pos hy'0 hy'_half
  have hcomb := c0_c1_combine_round_clamp_spec pSub B B_e hB hBe
    (computableHalfErfScaledInner B_e S N Bint w A P (r + 2 * u2') (2 * r)).1
    (computableHalfErfScaledInner B_e S N Bint w A P (r - 2 * u2') (2 * r)).1
    (computableHalfErfScaledInner B_e S N Bint w A P (3 * r - 2 * u2') (2 * r)).1
    ((1 / 2 : ℝ) * realErfScaled (alphaSchedule p_work) (y' + 1 / 2))
    ((1 / 2 : ℝ) * realErfScaled (alphaSchedule p_work) (1 / 2 - y'))
    ((1 / 2 : ℝ) * realErfScaled (alphaSchedule p_work) (3 / 2 - y'))
    (c0Coeff (realErfScaled (alphaSchedule p_work)) y')
    (c1Coeff (realErfScaled (alphaSchedule p_work)) y')
    hc_bounds.1 hc_bounds.2.1 hc_bounds.2.2.1 hc_bounds.2.2.2.1
    hc_bounds.2.2.2.2.1 hc_bounds.2.2.2.2.2.1
    hP_spec hM_spec hT_spec
  exact c0_c1_branch_dispatch_spec pSub r u2 _ _ (alphaSchedule p_work)
    hr hu2 hα_pos hcomb.1 hcomb.2.1 hcomb.2.2.1 hcomb.2.2.2.1
    hcomb.2.2.2.2.1 hcomb.2.2.2.2.2.1 hcomb.2.2.2.2.2.2

/-- Accuracy theorem for `computableC0C1Core`. -/
theorem computableC0C1Core_spec
    (p_work pSub B B_e M_z M_z2 S N Bint w r u2 : ℕ)
    (hB : B = pSub + 2) (hBe : B_e = B + 2)
    (hM_z : M_z = 8 * p_work + 1) (hM_z2 : M_z2 = 32 * p_work + 1)
    (hS : B_e + 2 * M_z + 6 ≤ S)
    (hN : 4 * M_z2 + B_e + M_z + 4 ≤ N)
    (hBint : B_e + 2 * N + 2 * (M_z2 + M_z) + 4 ≤ Bint)
    (hp_work : 0 < p_work) (hr : 0 < r) (hu2 : u2 < r) :
    let res := (computableC0C1Core p_work pSub B B_e S N Bint w r u2).1
    let c0_pair := res.1
    let c1_pair := res.2
    let α := alphaSchedule p_work
    let y : ℝ := (u2 : ℝ) / (r : ℝ)
    c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
    0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
    (2 * u2 = r → c1_pair = c0_pair) ∧
    (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1) := by
  dsimp only [computableC0C1Core, costedMulInt, costedNatSqrt]
  have h2S_ge3 : 3 ≤ 2 * S := by omega
  have hpi_spec := computablePiScaledWithCost_error_le (2 * S)
  have hlog2_err := computableLog2ScaledWithCost_error_le (2 * S)
  have hlog2_ge := computableLog2ScaledWithCost_ge_half (2 * S) h2S_ge3
  generalize hPiInt : (computablePiScaledWithCost (2 * S)).1 = piInt at hpi_spec ⊢
  generalize hLog2Int : (computableLog2ScaledWithCost (2 * S)).1 = log2Int at hlog2_err hlog2_ge ⊢
  obtain ⟨hpi_err, hpi_nonneg⟩ := hpi_spec
  obtain ⟨_hlog2_half, hlog2_nonneg⟩ := hlog2_ge
  generalize hPiNat : piInt.toNat = piNat
  generalize hLog2Nat : log2Int.toNat = log2Nat
  have hpLog_eq : (((4 * p_work : ℕ) : ℤ) * (log2Nat : ℤ)).toNat = 4 * p_work * log2Nat := by
    rw [← Nat.cast_mul, Int.toNat_natCast]
  rw [hpLog_eq]
  have hpiNat_cast : (piNat : ℝ) = (piInt : ℝ) := by
    have : (piNat : ℤ) = piInt := by rw [← hPiNat]; exact Int.toNat_of_nonneg hpi_nonneg
    exact_mod_cast this
  have hlog2Nat_cast : (log2Nat : ℝ) = (log2Int : ℝ) := by
    have : (log2Nat : ℤ) = log2Int := by rw [← hLog2Nat]; exact Int.toNat_of_nonneg hlog2_nonneg
    exact_mod_cast this
  rw [← hpiNat_cast] at hpi_err
  rw [← hlog2Nat_cast] at hlog2_err
  exact computableC0C1Inner_spec p_work pSub B B_e M_z M_z2 S N Bint w r u2
    piNat log2Nat (Nat.sqrt (4 * p_work * log2Nat)) (Nat.sqrt piNat)
    hB hBe hM_z hM_z2 hS hN hBint hp_work hr hu2 hpi_err hlog2_err rfl rfl

/-- **Accuracy, Range, and Dominance Theorem for `computableC0C1WithProgramCost`
(`computableC0C1WithProgramCost_spec`)**:
For `24 ≤ p_work`, `24 ≤ pSub`, `0 < r`, and `u2 < r` (in fact valid for all `0 < p_work`),
`computableC0C1WithProgramCost p_work pSub r u2` computes Gaussian-integer pairs `(c0_pair, c1_pair)`
with zero imaginary parts, real parts in `[0, 2^(pSub + 2)]`, approximating `c0Coeff` and `c1Coeff`
within `2 * realQuantizeMaxErr pSub` and preserving the passband dominance ordering between `c0` and `c1`. -/
theorem computableC0C1WithProgramCost_spec
    (p_work pSub r u2 : ℕ)
    (hp_work : 24 ≤ p_work) (_hpSub : 24 ≤ pSub) (hr : 0 < r) (hu2 : u2 < r) :
    let res := (computableC0C1WithProgramCost p_work pSub r u2).1
    let c0_pair := res.1
    let c1_pair := res.2
    let α := alphaSchedule p_work
    let y : ℝ := (u2 : ℝ) / (r : ℝ)
    c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
    0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
    (2 * u2 = r → c1_pair = c0_pair) ∧
    (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1) :=
  computableC0C1Core_spec p_work pSub
    (pSub + 2)
    ((pSub + 2) + 2)
    (8 * p_work + 1)
    (32 * p_work + 1)
    (((pSub + 2) + 2) + 2 * (8 * p_work + 1) + 6)
    (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4)
    (((pSub + 2) + 2) + 2 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6)
    ((((pSub + 2) + 2) + 2 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6) +
      4 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) +
      2 * (((pSub + 2) + 2) + 2 * (8 * p_work + 1) + 6) +
      ((pSub + 2) + 2) + 2 * p_work + 2 * Nat.log2 r + 40)
    r u2 rfl rfl rfl rfl le_rfl le_rfl (by omega) (by omega) hr hu2

/-- Call-site width soundness predicate for a single `computableHalfErfScaledInner` evaluation. -/
def HalfErfScaledInnerWidthSound (B_e S N Bint w A P numX denX : ℕ) : Prop :=
  let numZ : ℕ := A * numX
  let denZ : ℕ := denX * 2 ^ S
  let a0 := divRoundRatInt ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denZ : ℤ)
  let erfSeriesRes := runRecurrenceSeriesCosted w a0
    (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2) (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N
  FitsSignedScalarWord w (A : ℤ) ∧
  FitsSignedScalarWord w (numX : ℤ) ∧
  FitsSignedScalarWord w (numZ : ℤ) ∧
  FitsSignedScalarWord w (denZ : ℤ) ∧
  FitsSignedScalarWord w ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) ∧
  RecurrenceCallSitesWidthSound w a0
    (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2) (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N ∧
  FitsSignedScalarWord w ((erfSeriesRes.1.2 * ((2 ^ S : ℕ) : ℤ)) * ((2 ^ B_e : ℕ) : ℤ)) ∧
  FitsSignedScalarWord w (((P * 2 ^ Bint : ℕ) : ℤ))

/-- Call-site width soundness predicate for `computableC0C1WithProgramCost p_work pSub r u2`. -/
def C0C1WidthSound (p_work pSub r u2 : ℕ) : Prop :=
  let B := pSub + 2
  let B_e := B + 2
  let M_z := 8 * p_work + 1
  let M_z2 := 32 * p_work + 1
  let M_erf := M_z2 + M_z
  let S := B_e + 2 * M_z + 6
  let N := 4 * M_z2 + B_e + M_z + 4
  let Bint := B_e + 2 * N + 2 * M_erf + 6
  let w := Bint + 4 * N + 2 * M_erf + 2 * S + B_e + 2 * p_work + 2 * Nat.log2 r + 40
  let piNat := (computablePiScaledWithCost (2 * S)).1.toNat
  let log2Nat := (computableLog2ScaledWithCost (2 * S)).1.toNat
  let A := Nat.sqrt (4 * p_work * log2Nat)
  let P := Nat.sqrt piNat
  let u2' : ℕ := min u2 (r - u2)
  let denX : ℕ := 2 * r
  let hPlus := (computableHalfErfScaledInner B_e S N Bint w A P (r + 2 * u2') denX).1
  let hMinus := (computableHalfErfScaledInner B_e S N Bint w A P (r - 2 * u2') denX).1
  let hThree := (computableHalfErfScaledInner B_e S N Bint w A P (3 * r - 2 * u2') denX).1
  let rawHi := divRoundRatInt ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ)
  let rawLo := divRoundRatInt ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ)
  PiScaledWidthSound (2 * S) ∧
  Log2ScaledWidthSound (2 * S) ∧
  FitsSignedScalarWord w ((4 * p_work : ℕ) : ℤ) ∧
  FitsSignedScalarWord w (log2Nat : ℤ) ∧
  4 * p_work * log2Nat ≤ 2 ^ w ∧
  piNat ≤ 2 ^ w ∧
  HalfErfScaledInnerWidthSound B_e S N Bint w A P (r + 2 * u2') denX ∧
  HalfErfScaledInnerWidthSound B_e S N Bint w A P (r - 2 * u2') denX ∧
  HalfErfScaledInnerWidthSound B_e S N Bint w A P (3 * r - 2 * u2') denX ∧
  FitsSignedScalarWord w ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) ∧
  FitsSignedScalarWord w ((2 ^ B_e : ℕ) : ℤ) ∧
  FitsSignedScalarWord w rawHi ∧
  FitsSignedScalarWord w ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) ∧
  FitsSignedScalarWord w rawLo

/-- Width soundness and output magnitude bound for a single `computableHalfErfScaledInner` call. -/
theorem halfErfScaledInner_widths_and_abs_le
    (p_work B_e M_z M_z2 S N Bint D w piNat log2Nat A P r numX denX : ℕ)
    (hp_work : 0 < p_work) (hr : 0 < r)
    (hdenX_eq : denX = 2 * r) (hnumX : numX ≤ 2 * denX)
    (hM_z : M_z = 8 * p_work + 1) (hM_z2 : M_z2 = 32 * p_work + 1)
    (hS : B_e + 2 * M_z + 6 ≤ S)
    (hN : 4 * M_z2 + B_e + M_z + 4 ≤ N)
    (hD : D = 2 * S + 2 * p_work + 2 * Nat.log2 r + 14)
    (hw : Bint + 4 * N + 2 * (M_z2 + M_z) + 2 * S + B_e + 2 * p_work + 2 * Nat.log2 r + 40 ≤ w)
    (hpi_err : |(piNat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.pi| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hlog2_err : |(log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.log 2| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)))
    (hpi_le : piNat ≤ 2 ^ (2 * S + 2))
    (hlog2_le : log2Nat ≤ 2 ^ (2 * S + 1))
    (hA : A = Nat.sqrt (4 * p_work * log2Nat))
    (hP : P = Nat.sqrt piNat) :
    HalfErfScaledInnerWidthSound B_e S N Bint w A P numX denX ∧
    |((computableHalfErfScaledInner B_e S N Bint w A P numX denX).1 : ℝ)| ≤
      (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + S + B_e + 4) := by
  dsimp only [HalfErfScaledInnerWidthSound, computableHalfErfScaledInner, costedMulInt, costedDivRoundRatInt]
  have hnumZ_eq : ((A : ℤ) * (numX : ℤ)).toNat = A * numX := by
    rw [← Nat.cast_mul, Int.toNat_natCast]
  have hnumZ_sq_eq : (((A * numX : ℕ) : ℤ) * ((A * numX : ℕ) : ℤ)) = (((A * numX) ^ 2 : ℕ) : ℤ) := by
    push_cast; ring
  have hdenZ_sq_eq : (((denX * 2 ^ S : ℕ) : ℤ) * ((denX * 2 ^ S : ℕ) : ℤ)).toNat = (denX * 2 ^ S) ^ 2 := by
    rw [← Nat.cast_mul, Int.toNat_natCast, sq]
  rw [hnumZ_eq, hnumZ_sq_eq, hdenZ_sq_eq]
  have hdenX_pos : 0 < denX := by omega
  have hbounds := erf_arg_and_sqrt_bounds p_work B_e M_z M_z2 S N piNat log2Nat A P numX denX
    hp_work hdenX_pos hnumX hM_z hM_z2 hS hN hpi_err hlog2_err hA hP
  obtain ⟨hP_pos, _hp_hat_ge1, _hp_true_ge1, _hz_hat_nonneg, hz_hat_le, hz_hat_sq_le, _hrem, _hquot⟩ := hbounds
  have hr_le : r ≤ 2 ^ (Nat.log2 r + 1) := nat_le_two_pow_log2_add_one r
  have hdenX_le : denX ≤ 2 ^ (Nat.log2 r + 2) := by
    rw [hdenX_eq, pow_succ']
    exact Nat.mul_le_mul_left 2 hr_le
  have hnumX_le : numX ≤ 2 ^ (Nat.log2 r + 3) := by
    calc numX ≤ 2 * denX := hnumX
      _ ≤ 2 * 2 ^ (Nat.log2 r + 2) := Nat.mul_le_mul_left 2 hdenX_le
      _ = 2 ^ (Nat.log2 r + 3) := (pow_succ' 2 _).symm
  have h4p_le : 4 * p_work ≤ 2 ^ (p_work + 2) := by
    have hp : p_work ≤ 2 ^ p_work := Nat.lt_two_pow_self.le
    calc 4 * p_work = 2 ^ 2 * p_work := rfl
      _ ≤ 2 ^ 2 * 2 ^ p_work := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (p_work + 2) := by rw [← pow_add]; congr 1; omega
  have h4plog_le : 4 * p_work * log2Nat ≤ 2 ^ (2 * S + p_work + 3) := by
    calc 4 * p_work * log2Nat
        ≤ 2 ^ (p_work + 2) * 2 ^ (2 * S + 1) := Nat.mul_le_mul h4p_le hlog2_le
      _ = 2 ^ (2 * S + p_work + 3) := by rw [← pow_add]; congr 1; omega
  have hA_le_pow : A ≤ 2 ^ (S + p_work + 2) := by
    rw [hA]
    have h1 : 4 * p_work * log2Nat ≤ (2 ^ (S + p_work + 2)) ^ 2 :=
      h4plog_le.trans ((Nat.pow_le_pow_right (by decide)
        (by omega : 2 * S + p_work + 3 ≤ (S + p_work + 2) * 2)).trans_eq (pow_mul 2 _ 2))
    simpa [sq] using Nat.sqrt_le_sqrt h1
  have hP_le_pow : P ≤ 2 ^ (S + 1) := by
    rw [hP]
    have h1 : piNat ≤ (2 ^ (S + 1)) ^ 2 :=
      hpi_le.trans_eq (( by congr 1; omega : 2 ^ (2 * S + 2) = 2 ^ ((S + 1) * 2)).trans (pow_mul 2 _ 2))
    simpa [sq] using Nat.sqrt_le_sqrt h1
  set numZ : ℕ := A * numX
  set denZ : ℕ := denX * 2 ^ S
  have hdenZ_pos : 0 < denZ := Nat.mul_pos hdenX_pos (pow_pos zero_lt_two S)
  have hnumZ_le : numZ ≤ 2 ^ (S + p_work + Nat.log2 r + 5) := by
    dsimp [numZ]
    calc A * numX
        ≤ 2 ^ (S + p_work + 2) * 2 ^ (Nat.log2 r + 3) := Nat.mul_le_mul hA_le_pow hnumX_le
      _ = 2 ^ (S + p_work + Nat.log2 r + 5) := by rw [← pow_add]; congr 1; omega
  have hdenZ_le : denZ ≤ 2 ^ (S + Nat.log2 r + 2) := by
    dsimp [denZ]
    calc denX * 2 ^ S
        ≤ 2 ^ (Nat.log2 r + 2) * 2 ^ S := Nat.mul_le_mul_right _ hdenX_le
      _ = 2 ^ (S + Nat.log2 r + 2) := by rw [← pow_add]; congr 1; omega
  have hnumZ_sq_D : numZ ^ 2 ≤ 2 ^ D := by
    calc numZ ^ 2
        ≤ (2 ^ (S + p_work + Nat.log2 r + 5)) ^ 2 := Nat.pow_le_pow_left hnumZ_le 2
      _ = 2 ^ ((S + p_work + Nat.log2 r + 5) * 2) := (pow_mul 2 _ 2).symm
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hdenZ_sq_D : denZ ^ 2 ≤ 2 ^ D := by
    calc denZ ^ 2
        ≤ (2 ^ (S + Nat.log2 r + 2)) ^ 2 := Nat.pow_le_pow_left hdenZ_le 2
      _ = 2 ^ ((S + Nat.log2 r + 2) * 2) := (pow_mul 2 _ 2).symm
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by omega)
  have herf_rec := erf_recurrence_spec_and_widths Bint M_z M_z2 D w N numZ denZ
    hdenZ_pos hz_hat_le hz_hat_sq_le
    (by exact_mod_cast hnumZ_sq_D) (by exact_mod_cast hdenZ_sq_D) (by omega)
  dsimp only at herf_rec
  have hf_A : FitsSignedScalarWord w (A : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hA_le_pow.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_numX : FitsSignedScalarWord w (numX : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hnumX_le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_numZ : FitsSignedScalarWord w (numZ : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hnumZ_le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_denZ : FitsSignedScalarWord w (denZ : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow _ _ (hdenZ_le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_a0_num : FitsSignedScalarWord w ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) := by
    rw [← Nat.cast_mul]
    refine fitsSignedScalarWord_of_nat_le_two_pow _ _ ?_
    calc numZ * 2 ^ Bint
        ≤ 2 ^ (S + p_work + Nat.log2 r + 5) * 2 ^ Bint := Nat.mul_le_mul_right _ hnumZ_le
      _ = 2 ^ (S + p_work + Nat.log2 r + 5 + Bint) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  generalize hErfVal : (runRecurrenceSeriesCosted w
      (divRoundRatInt ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denZ : ℤ))
      (-((numZ ^ 2 : ℕ) : ℤ)) (denZ ^ 2)
      (fun k => 2 * k + 1) (fun k => (k + 1) * (2 * k + 3)) N).1.2 = erfSumVal at herf_rec ⊢
  have hout_num_abs :
      |(((erfSumVal * ((2 ^ S : ℕ) : ℤ)) * ((2 ^ B_e : ℕ) : ℤ) : ℤ) : ℝ)| ≤
        (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + 3 + S + B_e) := by
    push_cast
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ S),
        abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B_e), pow_add, pow_add]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right herf_rec.2.2 (by positivity)) (by positivity)
  have hf_out_num : FitsSignedScalarWord w ((erfSumVal * ((2 ^ S : ℕ) : ℤ)) * ((2 ^ B_e : ℕ) : ℤ)) :=
    fitsSignedScalarWord_of_abs_le_two_pow _ _ (hout_num_abs.trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hf_out_den : FitsSignedScalarWord w (((P * 2 ^ Bint : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_nat_le_two_pow _ _ ?_
    calc P * 2 ^ Bint
        ≤ 2 ^ (S + 1) * 2 ^ Bint := Nat.mul_le_mul_right _ hP_le_pow
      _ = 2 ^ (S + 1 + Bint) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hout_abs :
      |(divRoundRatInt ((erfSumVal * ((2 ^ S : ℕ) : ℤ)) * ((2 ^ B_e : ℕ) : ℤ))
          (((P * 2 ^ Bint : ℕ) : ℤ)) : ℝ)| ≤
        (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + S + B_e + 4) := by
    have hq := abs_divRoundRatInt_le
      ((erfSumVal * ((2 ^ S : ℕ) : ℤ)) * ((2 ^ B_e : ℕ) : ℤ))
      (((P * 2 ^ Bint : ℕ) : ℤ)) (by positivity)
    have hden_ge1 : (1 : ℝ) ≤ (((P * 2 ^ Bint : ℕ) : ℤ) : ℝ) := by
      have : 1 ≤ P * 2 ^ Bint := Nat.mul_pos hP_pos (pow_pos zero_lt_two Bint)
      exact_mod_cast this
    have hdiv_le := (div_le_self (abs_nonneg _) hden_ge1).trans hout_num_abs
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + 3 + S + B_e) :=
      one_le_pow₀ (by norm_num)
    calc |(divRoundRatInt ((erfSumVal * ((2 ^ S : ℕ) : ℤ)) * ((2 ^ B_e : ℕ) : ℤ))
            (((P * 2 ^ Bint : ℕ) : ℤ)) : ℝ)|
        ≤ (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + 3 + S + B_e) +
            (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + 3 + S + B_e) := by linarith
      _ = (2 : ℝ) ^ (Bint + 2 * (M_z2 + M_z) + 2 * N + S + B_e + 4) := by
          have : Bint + 2 * (M_z2 + M_z) + 2 * N + S + B_e + 4 =
              (Bint + 2 * (M_z2 + M_z) + 2 * N + 3 + S + B_e) + 1 := by omega
          rw [this, pow_succ]
          ring
  exact ⟨⟨hf_A, hf_numX, hf_numZ, hf_denZ, hf_a0_num, herf_rec.2.1, hf_out_num, hf_out_den⟩, hout_abs⟩

/-- **Call-Site Width Soundness for `computableC0C1WithProgramCost`**:
Every operand passed to `costedMulInt w`, `costedNatSqrt w`, `costedDivRoundRatInt w`, and `costedClampInt w`
inside `computableC0C1WithProgramCost p_work pSub r u2` fits within `w` bits. -/
theorem computableC0C1WithProgramCost_widths_sound
    (p_work pSub r u2 : ℕ)
    (hp_work : 0 < p_work) (hr : 0 < r) (hu2 : u2 < r) :
    C0C1WidthSound p_work pSub r u2 := by
  dsimp only [C0C1WidthSound]
  set B := pSub + 2 with hB_def
  set B_e := B + 2 with hBe_def
  set M_z := 8 * p_work + 1 with hMz_def
  set M_z2 := 32 * p_work + 1 with hMz2_def
  set M_erf := M_z2 + M_z with hMerf_def
  set S := B_e + 2 * M_z + 6 with hS_def
  set N := 4 * M_z2 + B_e + M_z + 4 with hN_def
  set Bint := B_e + 2 * N + 2 * M_erf + 6 with hBint_def
  set w := Bint + 4 * N + 2 * M_erf + 2 * S + B_e + 2 * p_work + 2 * Nat.log2 r + 40 with hw_def
  set D := 2 * S + 2 * p_work + 2 * Nat.log2 r + 14 with hD_def
  clear_value B B_e M_z M_z2 M_erf S N Bint w D
  have h2S_ge3 : 3 ≤ 2 * S := by omega
  have hpi_spec := computablePiScaledWithCost_error_le (2 * S)
  have hlog2_err := computableLog2ScaledWithCost_error_le (2 * S)
  have hlog2_ge := computableLog2ScaledWithCost_ge_half (2 * S) h2S_ge3
  have hpi_le := computablePiScaledWithCost_toNat_le (2 * S)
  have hlog2_le := computableLog2ScaledWithCost_toNat_le (2 * S)
  have hpi_ws := computablePiScaledWithCost_widths_sound (2 * S)
  have hlog2_ws := computableLog2ScaledWithCost_widths_sound (2 * S)
  generalize hpi_val : (computablePiScaledWithCost (2 * S)).1 = piInt at hpi_spec hpi_le ⊢
  generalize hlog2_val : (computableLog2ScaledWithCost (2 * S)).1 = log2Int at hlog2_err hlog2_ge hlog2_le ⊢
  set piNat := piInt.toNat
  set log2Nat := log2Int.toNat
  set A := Nat.sqrt (4 * p_work * log2Nat) with hA_def
  set P := Nat.sqrt piNat with hP_def
  set u2' : ℕ := min u2 (r - u2) with hu2'_def
  set denX : ℕ := 2 * r with hdenX_def
  have hu2'_le : 2 * u2' ≤ r := by omega
  clear_value A P u2' denX
  have hpiNat_cast : (piNat : ℝ) = (piInt : ℝ) := by
    have : (piNat : ℤ) = piInt := Int.toNat_of_nonneg hpi_spec.2
    exact_mod_cast this
  have hlog2Nat_cast : (log2Nat : ℝ) = (log2Int : ℝ) := by
    have : (log2Nat : ℤ) = log2Int := Int.toNat_of_nonneg hlog2_ge.2
    exact_mod_cast this
  have hpi_err_nat : |(piNat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.pi| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)) := by
    rw [hpiNat_cast]; exact hpi_spec.1
  have hlog2_err_nat : |(log2Nat : ℝ) / (2 : ℝ) ^ (2 * S) - Real.log 2| ≤ (2 : ℝ) ^ (-(2 * S : ℤ)) := by
    rw [hlog2Nat_cast]; exact hlog2_err
  have h4p_le : 4 * p_work ≤ 2 ^ (p_work + 2) := by
    have hp : p_work ≤ 2 ^ p_work := Nat.lt_two_pow_self.le
    calc 4 * p_work = 2 ^ 2 * p_work := rfl
      _ ≤ 2 ^ 2 * 2 ^ p_work := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (p_work + 2) := by rw [← pow_add, show 2 + p_work = p_work + 2 by omega]
  have h4plog_le : 4 * p_work * log2Nat ≤ 2 ^ (2 * S + p_work + 3) := by
    calc 4 * p_work * log2Nat
        ≤ 2 ^ (p_work + 2) * 2 ^ (2 * S + 1) := Nat.mul_le_mul h4p_le hlog2_le
      _ = 2 ^ (2 * S + p_work + 3) := by rw [← pow_add, show p_work + 2 + (2 * S + 1) = 2 * S + p_work + 3 by omega]
  have hf_4p : FitsSignedScalarWord w ((4 * p_work : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow w _ (h4p_le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hf_log2 : FitsSignedScalarWord w (log2Nat : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow w _ (hlog2_le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have h4plog_w : 4 * p_work * log2Nat ≤ 2 ^ w :=
    h4plog_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hpi_w : piNat ≤ 2 ^ w :=
    hpi_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hP_w := halfErfScaledInner_widths_and_abs_le p_work B_e M_z M_z2 S N Bint D w
    piNat log2Nat A P r (r + 2 * u2') denX hp_work hr hdenX_def (by omega)
    hMz_def hMz2_def (by omega) (by omega) hD_def (by omega) hpi_err_nat hlog2_err_nat hpi_le hlog2_le hA_def hP_def
  have hM_w := halfErfScaledInner_widths_and_abs_le p_work B_e M_z M_z2 S N Bint D w
    piNat log2Nat A P r (r - 2 * u2') denX hp_work hr hdenX_def (by omega)
    hMz_def hMz2_def (by omega) (by omega) hD_def (by omega) hpi_err_nat hlog2_err_nat hpi_le hlog2_le hA_def hP_def
  have hT_w := halfErfScaledInner_widths_and_abs_le p_work B_e M_z M_z2 S N Bint D w
    piNat log2Nat A P r (3 * r - 2 * u2') denX hp_work hr hdenX_def (by omega)
    hMz_def hMz2_def (by omega) (by omega) hD_def (by omega) hpi_err_nat hlog2_err_nat hpi_le hlog2_le hA_def hP_def
  generalize hhP_val : (computableHalfErfScaledInner B_e S N Bint w A P (r + 2 * u2') denX).1 = hPlus at hP_w ⊢
  generalize hhM_val : (computableHalfErfScaledInner B_e S N Bint w A P (r - 2 * u2') denX).1 = hMinus at hM_w ⊢
  generalize hhT_val : (computableHalfErfScaledInner B_e S N Bint w A P (3 * r - 2 * u2') denX).1 = hThree at hT_w ⊢
  set E_out := Bint + 2 * (M_z2 + M_z) + 2 * N + S + B_e + 4 with hE_out_def
  clear_value E_out
  have hhi_num_abs : |(((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (E_out + 1 + B) := by
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B), pow_add, pow_succ]
    have htri := abs_add_le (hPlus : ℝ) (hMinus : ℝ)
    have hsum : |(hPlus : ℝ) + (hMinus : ℝ)| ≤ (2 : ℝ) ^ E_out * 2 := by
      linarith [hP_w.2, hM_w.2]
    exact mul_le_mul_of_nonneg_right hsum (by positivity)
  have hlo_num_abs : |(((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (E_out + 1 + B) := by
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ B), pow_add, pow_succ]
    have htri := abs_sub (hThree : ℝ) (hMinus : ℝ)
    have hsum : |(hThree : ℝ) - (hMinus : ℝ)| ≤ (2 : ℝ) ^ E_out * 2 := by
      linarith [hT_w.2, hM_w.2]
    exact mul_le_mul_of_nonneg_right hsum (by positivity)
  have hf_hi_num : FitsSignedScalarWord w ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) :=
    fitsSignedScalarWord_of_abs_le_two_pow w _ (hhi_num_abs.trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hf_lo_num : FitsSignedScalarWord w ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) :=
    fitsSignedScalarWord_of_abs_le_two_pow w _ (hlo_num_abs.trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hf_Be : FitsSignedScalarWord w ((2 ^ B_e : ℕ) : ℤ) :=
    fitsSignedScalarWord_of_nat_le_two_pow w _
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hf_rawHi : FitsSignedScalarWord w
      (divRoundRatInt ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_abs_le_two_pow w _ ?_
    have hq := abs_divRoundRatInt_le ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ) (by positivity)
    have hden_ge1 : (1 : ℝ) ≤ (((2 ^ B_e : ℕ) : ℤ) : ℝ) := by push_cast; exact one_le_pow₀ (by norm_num)
    have hdiv_le := (div_le_self (abs_nonneg _) hden_ge1).trans hhi_num_abs
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (E_out + 1 + B) := one_le_pow₀ (by norm_num)
    calc |(divRoundRatInt ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ) : ℝ)|
        ≤ (2 : ℝ) ^ (E_out + 1 + B) + (2 : ℝ) ^ (E_out + 1 + B) := by linarith
      _ = (2 : ℝ) ^ (E_out + 1 + B + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hf_rawLo : FitsSignedScalarWord w
      (divRoundRatInt ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ)) := by
    refine fitsSignedScalarWord_of_abs_le_two_pow w _ ?_
    have hq := abs_divRoundRatInt_le ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ) (by positivity)
    have hden_ge1 : (1 : ℝ) ≤ (((2 ^ B_e : ℕ) : ℤ) : ℝ) := by push_cast; exact one_le_pow₀ (by norm_num)
    have hdiv_le := (div_le_self (abs_nonneg _) hden_ge1).trans hlo_num_abs
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (E_out + 1 + B) := one_le_pow₀ (by norm_num)
    calc |(divRoundRatInt ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ B_e : ℕ) : ℤ) : ℝ)|
        ≤ (2 : ℝ) ^ (E_out + 1 + B) + (2 : ℝ) ^ (E_out + 1 + B) := by linarith
      _ = (2 : ℝ) ^ (E_out + 1 + B + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ (w - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨hpi_ws, hlog2_ws,
    hf_4p, hf_log2, h4plog_w, hpi_w,
    hP_w.1, hM_w.1, hT_w.1,
    hf_hi_num, hf_Be, hf_rawHi, hf_lo_num, hf_rawLo⟩

/-- Cost bound for `computableC0C1Inner` when `N ≤ w`. -/
theorem computableC0C1Inner_snd_le
    (pSub B B_e S N Bint w r u2 A P : ℕ)
    (hN_le : N ≤ w) :
    (computableC0C1Inner pSub B B_e S N Bint w r u2 A P).2 ≤
      36 * (w + 10) ^ 4 := by
  dsimp only [computableC0C1Inner, costedShiftLeftInt, costedDivRoundRatInt, costedClampInt]
  rw [computableHalfErfScaledInner_snd, computableHalfErfScaledInner_snd, computableHalfErfScaledInner_snd]
  have hw1 : w + 1 ≤ w + 10 := by omega
  have hmul : computableMulBitCost w ≤ (w + 10) ^ 3 :=
    (computableMulBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hadd : addBitCost w ≤ (w + 10) ^ 3 :=
    (addBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hN14 : 3 * N + 14 ≤ 4 * (w + 10) := by omega
  generalize computableMulBitCost w = MulC at hmul ⊢
  generalize addBitCost w = AddC at hadd ⊢
  generalize hW3 : (w + 10) ^ 3 = W3 at hmul hadd
  have h1 :
      (MulC + AddC + MulC + MulC + AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) + AddC + AddC + AddC + (2 * MulC + 2 * AddC)) +
      (MulC + AddC + MulC + MulC + AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) + AddC + AddC + AddC + (2 * MulC + 2 * AddC)) +
      (MulC + AddC + MulC + MulC + AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) + AddC + AddC + AddC + (2 * MulC + 2 * AddC)) +
      AddC + (2 * MulC + 2 * AddC) + 2 * AddC + AddC + (2 * MulC + 2 * AddC) + 2 * AddC + 4 * AddC ≤
      (3 * N + 14) * (6 * MulC + 3 * AddC) := by
    nlinarith
  calc (MulC + AddC + MulC + MulC + AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) + AddC + AddC + AddC + (2 * MulC + 2 * AddC)) +
      (MulC + AddC + MulC + MulC + AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) + AddC + AddC + AddC + (2 * MulC + 2 * AddC)) +
      (MulC + AddC + MulC + MulC + AddC + (2 * MulC + 2 * AddC) +
        (N * (6 * MulC + 3 * AddC)) + AddC + AddC + AddC + (2 * MulC + 2 * AddC)) +
      AddC + (2 * MulC + 2 * AddC) + 2 * AddC + AddC + (2 * MulC + 2 * AddC) + 2 * AddC + 4 * AddC
      ≤ (3 * N + 14) * (6 * MulC + 3 * AddC) := h1
    _ ≤ (4 * (w + 10)) * (6 * W3 + 3 * W3) := Nat.mul_le_mul hN14 (by omega)
    _ = 36 * (w + 10) ^ 4 := by subst hW3; ring

/-- Cost bound for `computableC0C1Core` in terms of `(w + 10) ^ 4` when `2 * S ≤ w` and `N ≤ w`. -/
theorem computableC0C1Core_snd_le
    (p_work pSub B B_e S N Bint w r u2 : ℕ)
    (h2S_le : 2 * S ≤ w) (hN_le : N ≤ w) :
    (computableC0C1Core p_work pSub B B_e S N Bint w r u2).2 ≤
      7000 * (w + 10) ^ 4 := by
  dsimp only [computableC0C1Core, costedMulInt, costedNatSqrt]
  have hpi_cost := computablePiScaledWithCost_snd_le (2 * S)
  have hlog2_cost := computableLog2ScaledWithCost_snd_le (2 * S)
  have h2S7 : 2 * S + 7 ≤ w + 10 := by omega
  have h16S : 8 * (2 * S) + 85 ≤ 9 * (w + 10) := by omega
  have h2S4 : 2 * S + 4 ≤ w + 10 := by omega
  have h14S : 7 * (2 * S) + 45 ≤ 7 * (w + 10) := by omega
  have hpi_le : (computablePiScaledWithCost (2 * S)).2 ≤ 3645 * (w + 10) ^ 4 := by
    calc (computablePiScaledWithCost (2 * S)).2
        ≤ (2 * S + 7) * 5 * (8 * (2 * S) + 85) ^ 3 := hpi_cost
      _ ≤ (w + 10) * 5 * (9 * (w + 10)) ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_right 5 h2S7) (Nat.pow_le_pow_left h16S 3)
      _ = 3645 * (w + 10) ^ 4 := by ring
  have hlog2_le : (computableLog2ScaledWithCost (2 * S)).2 ≤ 3087 * (w + 10) ^ 4 := by
    calc (computableLog2ScaledWithCost (2 * S)).2
        ≤ (2 * S + 4) * 9 * (7 * (2 * S) + 45) ^ 3 := hlog2_cost
      _ ≤ (w + 10) * 9 * (7 * (w + 10)) ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_right 9 h2S4) (Nat.pow_le_pow_left h14S 3)
      _ = 3087 * (w + 10) ^ 4 := by ring
  have hw1 : w + 1 ≤ w + 10 := by omega
  have hmul : computableMulBitCost w ≤ (w + 10) ^ 3 :=
    (computableMulBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hadd : addBitCost w ≤ (w + 10) ^ 3 :=
    (addBitCost_le_cube w).trans (Nat.pow_le_pow_left hw1 3)
  have hsqrt_le : computableMulBitCost w +
      (2 * computableMulBitCost w + 2 * addBitCost w) +
      (2 * computableMulBitCost w + 2 * addBitCost w) ≤ 9 * (w + 10) ^ 4 := by
    have hpow3_le4 : (w + 10) ^ 3 ≤ (w + 10) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hinner_le := computableC0C1Inner_snd_le pSub B B_e S N Bint w r u2
    (Nat.sqrt (((4 * p_work : ℕ) : ℤ) * ((computableLog2ScaledWithCost (2 * S)).1.toNat : ℤ)).toNat)
    (Nat.sqrt (computablePiScaledWithCost (2 * S)).1.toNat) hN_le
  calc (computablePiScaledWithCost (2 * S)).2 + (computableLog2ScaledWithCost (2 * S)).2 +
        computableMulBitCost w +
        (2 * computableMulBitCost w + 2 * addBitCost w) + (2 * computableMulBitCost w + 2 * addBitCost w) +
        (computableC0C1Inner pSub B B_e S N Bint w r u2
          (Nat.sqrt (((4 * p_work : ℕ) : ℤ) * ((computableLog2ScaledWithCost (2 * S)).1.toNat : ℤ)).toNat)
          (Nat.sqrt (computablePiScaledWithCost (2 * S)).1.toNat)).2
      ≤ 3645 * (w + 10) ^ 4 + 3087 * (w + 10) ^ 4 +
        9 * (w + 10) ^ 4 + 36 * (w + 10) ^ 4 := by
        linarith
    _ = 6777 * (w + 10) ^ 4 := by ring
    _ ≤ 7000 * (w + 10) ^ 4 := Nat.mul_le_mul_right _ (by decide)

/-- **Bit-Operation Cost Bound for `computableC0C1WithProgramCost`
(`computableC0C1WithProgramCost_snd_le`)**:
Bounded by an explicit degree-4 polynomial in `M = p_work + pSub + Nat.log2 r + 1`. -/
theorem computableC0C1WithProgramCost_snd_le
    (p_work pSub r u2 : ℕ) :
    let M := p_work + pSub + Nat.log2 r + 1
    (computableC0C1WithProgramCost p_work pSub r u2).2 ≤
      7000 * (1050 * (M + 10)) ^ 4 := by
  intro M
  dsimp only [computableC0C1WithProgramCost]
  set B := pSub + 2 with hB_def
  set B_e := B + 2 with hBe_def
  set M_z := 8 * p_work + 1 with hMz_def
  set M_z2 := 32 * p_work + 1 with hMz2_def
  set M_erf := M_z2 + M_z with hMerf_def
  set S := B_e + 2 * M_z + 6 with hS_def
  set N := 4 * M_z2 + B_e + M_z + 4 with hN_def
  set Bint := B_e + 2 * N + 2 * M_erf + 6 with hBint_def
  set w := Bint + 4 * N + 2 * M_erf + 2 * S + B_e + 2 * p_work + 2 * Nat.log2 r + 40 with hw_def
  clear_value B B_e M_z M_z2 M_erf S N Bint w
  have h2S_le : 2 * S ≤ w := by omega
  have hN_le : N ≤ w := by omega
  have hw10_le : w + 10 ≤ 1050 * (M + 10) := by
    dsimp [M]
    omega
  exact (computableC0C1Core_snd_le p_work pSub B B_e S N Bint w r u2 h2S_le hN_le).trans
    (Nat.mul_le_mul_left 7000 (Nat.pow_le_pow_left hw10_le 4))

end IntMul
