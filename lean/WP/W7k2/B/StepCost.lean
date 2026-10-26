import WP.W7k2.B.Roles
import WP.W7k2.B.Budget

/-!
# WP.W7k2.B.StepCost — the per-step-level cost bound (pure arithmetic)

Per-step-level cost bound for W7k2: `stepCostE` is verbatim the sum of the builder's
component cost bounds at one step level, and `stepCostE_le` bounds it by `2000·C·(KM+1)` times the
snapshot's per-level budget plus `3·|preSegC|`.

* `piScaled_bitLen_le`, `log2Scaled_bitLen_le`: widths of the hoisted `π`, `ln 2` (`≤ B + 3` bits),
  from the snapshot's accuracy theorems (CTr:1113, CTr:1234).
* Proof of `stepCostE_le`: every term is at most a constant times one of `X = C·Q⁴`, `KM·X`, `r·X`,
  `t1·(4p′+1)·X`; `step_budget_ge` turns `(t1(4p′+1) + 4r)·Q⁴` into the budget. The constant that
  comes out is below 400.
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open IntMul TMFw TMFw.Contracts

/-! ## Widths of the hoisted `π` and `ln 2` -/

/-- A scaled approximation `|z/2^B − c| ≤ 2^-B` of a constant `|c| ≤ 3.5` has at most `B + 3` bits. -/
theorem bitLen_natAbs_le_of_scaled (B : ℕ) (z : ℤ) (c : ℝ) (hc : |c| ≤ 3.5)
    (h : |(z : ℝ) / (2 : ℝ) ^ B - c| ≤ (2 : ℝ) ^ (-(B : ℤ))) : bitLen z.natAbs ≤ B + 3 := by
  apply bitLen_le_of_lt
  have hpos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hzpow : (2 : ℝ) ^ (-(B : ℤ)) * (2 : ℝ) ^ B = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ hpos.ne']
  have h1 : |(z : ℝ) / (2 : ℝ) ^ B| ≤ |c| + (2 : ℝ) ^ (-(B : ℤ)) := by
    have := abs_sub_abs_le_abs_sub ((z : ℝ) / (2 : ℝ) ^ B) c
    linarith
  have e : |(z : ℝ)| = |(z : ℝ) / (2 : ℝ) ^ B| * (2 : ℝ) ^ B := by
    rw [abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']
  have h2 : |(z : ℝ)| ≤ (|c| + (2 : ℝ) ^ (-(B : ℤ))) * (2 : ℝ) ^ B := by
    rw [e]; exact mul_le_mul_of_nonneg_right h1 hpos.le
  have h3 : (|c| + (2 : ℝ) ^ (-(B : ℤ))) * (2 : ℝ) ^ B = |c| * (2 : ℝ) ^ B + 1 := by
    rw [add_mul, hzpow]
  have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
  have h4' : |c| * (2 : ℝ) ^ B ≤ 3.5 * (2 : ℝ) ^ B := mul_le_mul_of_nonneg_right hc hpos.le
  have h5 : |(z : ℝ)| < 8 * (2 : ℝ) ^ B := by linarith
  have h6 : ((2 ^ (B + 3) : ℕ) : ℝ) = 8 * (2 : ℝ) ^ B := by push_cast; rw [pow_add]; norm_num; ring
  have h7 : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have h8 : ((z.natAbs : ℕ) : ℝ) < ((2 ^ (B + 3) : ℕ) : ℝ) := by rw [h7, h6]; exact h5
  exact_mod_cast h8

/-- `π·2^B` (CTr:968) has at most `B + 3` bits. -/
theorem piScaled_bitLen_le (B : ℕ) : bitLen (computablePiScaledWithCost B).1.natAbs ≤ B + 3 :=
  bitLen_natAbs_le_of_scaled B _ Real.pi
    (by rw [abs_of_pos Real.pi_pos]; linarith [Real.pi_lt_d2])
    (computablePiScaledWithCost_error_le B).1

/-- `ln 2·2^B` (CTr:1221) has at most `B + 3` bits. -/
theorem log2Scaled_bitLen_le (B : ℕ) :
    bitLen (computableLog2ScaledWithCost B).1.natAbs ≤ B + 3 :=
  bitLen_natAbs_le_of_scaled B _ (Real.log 2)
    (by rw [abs_of_pos (Real.log_pos one_lt_two)]; linarith [Real.log_two_lt_d9])
    (computableLog2ScaledWithCost_error_le B)

#assert_std_axioms bitLen_natAbs_le_of_scaled piScaled_bitLen_le log2Scaled_bitLen_le

/-! ## The per-step-level cost -/

/-- The builder's cost at one step level: verbatim sum of the component bounds (cvA…cvD, postSeg,
preSeg, advance, dropVals), as fixed by W7k2. -/
def stepCostE (C KM p K pIn Lc : ℕ) : ℕ :=
  let Q := 128 * (pWork p K + 1)
  let k1 := K / 2
  let k2 := K - K / 2
  let pc := pChild p K
  let ps := 2 * pc
  let W := effectiveFilterWidth ps (2 ^ k2)
  let NB := kroneckerSpreadNumBlocks ps (2 ^ k2)
  let piZ := (computablePiScaledWithCost (W7.tapPrec ps)).1
  let lnZ := (computableLog2ScaledWithCost (W7.tapPrec ps)).1
  (5 * (C * Q) + (12 * (C * Q) + 8) + (C * (Q * Q) + 20 * (C * Q) + 6) +
    (2 * (C * Q ^ 4) + 2 * (C * (KM * Q ^ 2)) + 30 * (C * Q) + 100)) +
  (2 ^ k2 * (C * Q ^ 4 + C * (Q * Q) + 12 * (C * Q) + 11) + 2 * (C * Q) +
    fieldsCost C [p, ps, 2 ^ k1, 2 ^ k2, k1, k2, pc, 3 * ps + 2] + 4) +
  (2 * (2 ^ k2 * (C * Q ^ 4 + 2 * (C * Q) + 1)) +
    2 ^ k1 * ((2 * ps + W) * (C * Q ^ 4 + 15 * (C * Q) + 6) + W * (9 * (C * Q) + 7) +
      4 * (C * Q) + 3) +
    6 * (C * Q) + fieldsCost C [p, ps, ps, 2 ^ k1, 2 ^ k2, k1, k2, W, NB, pc, pIn] +
    3 * (preSegC pIn p K).length + 11) +
  (C * (bitLen Lc + 1) + C * (bitLen pIn + 1) + C * (bitLen ps + 1) + C * (bitLen p + 1) +
    C * (bitLen pc + 1) + C * (bitLen K + 1) + C * (bitLen k2 + 1)) +
  (C * (bitLen k1 + 1) + C * (bitLen k2 + 1) + C * (bitLen (pWork p K) + 1) + C * (bitLen pc + 1) +
    C * (bitLen ps + 1) + C * (bitLen (2 ^ k1) + 1) + C * (bitLen (2 ^ k2) + 1) +
    C * (bitLen (2 * 2 ^ k2) + 1) + C * (bitLen (2 * ps + 1) + 1) + C * (bitLen W + 1) +
    C * (bitLen NB + 1) + C * (bitLen (3 * ps + 2) + 1) + C * (bitLen (W7.tapPrec ps) + 1) +
    (1 + C * (bitLen piZ.natAbs + 1)) + (1 + C * (bitLen lnZ.natAbs + 1)))

/-- **Per-step-level cost bound.** -/
theorem stepCostE_le (C KM p K pIn Lc : ℕ) (hC : 1 ≤ C) (hp : 8 ≤ p) (hK : ¬ 2 ^ K ≤ 4 * p * p)
    (hLc : Lc ≤ p + K) (hpIn : pIn ≤ 2 * p) :
    stepCostE C KM p K pIn Lc ≤
      2000 * (C * (KM + 1)) * precomputeStepSeriesTableBitCost p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) +
        3 * (preSegC pIn p K).length := by
  have hbud := step_budget_ge p K hp hK
  have hpc_val : pChild p K = p + 2 * K + 12 := pChild_eq_additive p K
  have hpw_val : pWork p K = p + K + 6 := rfl
  have hWr0 : effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2)) ≤ 2 ^ (K - K / 2) :=
    effectiveFilterWidth_le_r _ _
  have hNB0 : kroneckerSpreadNumBlocks (2 * pChild p K) (2 ^ (K - K / 2)) ≤ 2 * 2 ^ (K - K / 2) := by
    unfold kroneckerSpreadNumBlocks
    dsimp only
    exact le_trans (Nat.div_le_self _ _) (by omega)
  have hW0 : effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2)) ≤ 4 * pChild p K + 1 := by
    unfold effectiveFilterWidth; omega
  have hB0 : W7.tapPrec (2 * pChild p K) = 60 * pChild p K + 42 := by unfold W7.tapPrec; ring
  unfold stepCostE
  dsimp only
  set Q := 128 * (pWork p K + 1) with hQ
  set pc := pChild p K with hpc
  set t1 := 2 ^ (K / 2) with ht1
  set r := 2 ^ (K - K / 2) with hr
  set W := effectiveFilterWidth (2 * pc) r with hW
  set NB := kroneckerSpreadNumBlocks (2 * pc) r with hNB
  set B := W7.tapPrec (2 * pc) with hB
  set S := precomputeStepSeriesTableBitCost p K t1 r with hS
  set L := (preSegC pIn p K).length with hL
  have hQv : Q = 128 * (p + K + 7) := by rw [hQ, hpw_val]
  have hQpos : 0 < Q := by omega
  have ht1pos : 1 ≤ t1 := Nat.one_le_two_pow
  have hrpos : 1 ≤ r := Nat.one_le_two_pow
  -- the unit `X = C·Q⁴` and its elementary bounds
  set X := C * Q ^ 4 with hX
  have hQ4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQpos
  have hX1 : 1 ≤ X := by rw [hX]; simpa using Nat.mul_le_mul hC hQ4
  have hCX : C ≤ X := by
    rw [hX]; calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Q ^ 4 := Nat.mul_le_mul_left C hQ4
  have haX : C * Q ≤ X := by rw [hX]; exact Nat.mul_le_mul_left C (Nat.le_self_pow (by norm_num) Q)
  have hbX : C * (Q * Q) ≤ X := by
    rw [hX]; apply Nat.mul_le_mul_left C
    calc Q * Q = Q ^ 2 := (sq Q).symm
      _ ≤ Q ^ 4 := Nat.pow_le_pow_right hQpos (by norm_num)
  have hdX : C * (KM * Q ^ 2) ≤ KM * X := by
    rw [hX]
    calc C * (KM * Q ^ 2) = KM * (C * Q ^ 2) := by ring
      _ ≤ KM * (C * Q ^ 4) :=
          Nat.mul_le_mul_left KM (Nat.mul_le_mul_left C (Nat.pow_le_pow_right hQpos (by norm_num)))
  -- products with `t1`, `r`
  have htX : X ≤ t1 * X := by
    calc X = 1 * X := (one_mul X).symm
      _ ≤ t1 * X := Nat.mul_le_mul_right X ht1pos
  have hKMt : KM * X ≤ KM * (t1 * X) := Nat.mul_le_mul_left KM htX
  have hr1 : r ≤ r * X := by
    calc r = r * 1 := (mul_one r).symm
      _ ≤ r * X := Nat.mul_le_mul_left r hX1
  have hra : r * (C * Q) ≤ r * X := Nat.mul_le_mul_left r haX
  have hrb : r * (C * (Q * Q)) ≤ r * X := Nat.mul_le_mul_left r hbX
  have ht1X : t1 ≤ t1 * X := by
    calc t1 = t1 * 1 := (mul_one t1).symm
      _ ≤ t1 * X := Nat.mul_le_mul_left t1 hX1
  have hta : t1 * (C * Q) ≤ t1 * X := Nat.mul_le_mul_left t1 haX
  have htpc1 : t1 * pc ≤ t1 * pc * X := by
    calc t1 * pc = t1 * pc * 1 := (mul_one _).symm
      _ ≤ t1 * pc * X := Nat.mul_le_mul_left _ hX1
  have htpca : t1 * pc * (C * Q) ≤ t1 * pc * X := Nat.mul_le_mul_left _ haX
  have htW1 : t1 * W ≤ t1 * W * X := by
    calc t1 * W = t1 * W * 1 := (mul_one _).symm
      _ ≤ t1 * W * X := Nat.mul_le_mul_left _ hX1
  have htWa : t1 * W * (C * Q) ≤ t1 * W * X := Nat.mul_le_mul_left _ haX
  have htWX : t1 * W * X ≤ t1 * (4 * pc + 1) * X :=
    Nat.mul_le_mul_right X (Nat.mul_le_mul_left t1 hW0)
  -- the budget link (step_budget_ge)
  have hlink : (KM + 1) * (t1 * (4 * pc + 1) + 4 * r) * X ≤ C * (KM + 1) * S := by
    have h := Nat.mul_le_mul_left (C * (KM + 1)) hbud
    calc (KM + 1) * (t1 * (4 * pc + 1) + 4 * r) * X
        = C * (KM + 1) * ((t1 * (4 * pc + 1) + 4 * r) * Q ^ 4) := by rw [hX]; ring
      _ ≤ C * (KM + 1) * S := h
  -- widths
  have hself : ∀ v, v ≤ Q → bitLen v ≤ Q := fun v hv => le_trans (bitLen_le_self v) hv
  have hbl : ∀ v, bitLen v ≤ Q → C * (bitLen v + 1) ≤ C * Q + C := fun v hv => by
    calc C * (bitLen v + 1) ≤ C * (Q + 1) := Nat.mul_le_mul_left C (by omega)
      _ = C * Q + C := by ring
  have wLc : bitLen Lc ≤ Q := hself Lc (by omega)
  have wpIn : bitLen pIn ≤ Q := hself pIn (by omega)
  have wps : bitLen (2 * pc) ≤ Q := hself _ (by omega)
  have wp : bitLen p ≤ Q := hself p (by omega)
  have wpc : bitLen pc ≤ Q := hself pc (by omega)
  have wK : bitLen K ≤ Q := hself K (by omega)
  have wk1 : bitLen (K / 2) ≤ Q := hself _ (by omega)
  have wk2 : bitLen (K - K / 2) ≤ Q := hself _ (by omega)
  have wpw : bitLen (pWork p K) ≤ Q := hself _ (by omega)
  have wt1 : bitLen t1 ≤ Q := by rw [ht1, bitLen_two_pow]; omega
  have wr : bitLen r ≤ Q := by rw [hr, bitLen_two_pow]; omega
  have w2r : bitLen (2 * r) ≤ Q := by
    rw [hr, show 2 * 2 ^ (K - K / 2) = 2 ^ (K - K / 2 + 1) by ring, bitLen_two_pow]; omega
  have w4pc : bitLen (2 * (2 * pc) + 1) ≤ Q := hself _ (by omega)
  have wW : bitLen W ≤ Q := hself W (by omega)
  have wNB : bitLen NB ≤ Q := le_trans (bitLen_mono hNB0) w2r
  have w6pc : bitLen (3 * (2 * pc) + 2) ≤ Q := hself _ (by omega)
  have wB : bitLen B ≤ Q := hself B (by omega)
  have wpi : bitLen (computablePiScaledWithCost B).1.natAbs ≤ Q :=
    le_trans (piScaled_bitLen_le B) (by omega)
  have wln : bitLen (computableLog2ScaledWithCost B).1.natAbs ≤ Q :=
    le_trans (log2Scaled_bitLen_le B) (by omega)
  have e1 := hbl _ wLc
  have e2 := hbl _ wpIn
  have e3 := hbl _ wps
  have e4 := hbl _ wp
  have e5 := hbl _ wpc
  have e6 := hbl _ wK
  have e7 := hbl _ wk1
  have e8 := hbl _ wk2
  have e9 := hbl _ wpw
  have e10 := hbl _ wt1
  have e11 := hbl _ wr
  have e12 := hbl _ w2r
  have e13 := hbl _ w4pc
  have e14 := hbl _ wW
  have e15 := hbl _ wNB
  have e16 := hbl _ w6pc
  have e17 := hbl _ wB
  have e18 := hbl _ wpi
  have e19 := hbl _ wln
  -- header field costs
  have hF1 := fieldsCost_le C Q [p, 2 * pc, t1, r, K / 2, K - K / 2, pc, 3 * (2 * pc) + 2]
    (by
      intro v hv
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h | h | h | h <;> rw [h]
      exacts [wp, wps, wt1, wr, wk1, wk2, wpc, w6pc])
  have hF2 := fieldsCost_le C Q [p, 2 * pc, 2 * pc, t1, r, K / 2, K - K / 2, W, NB, pc, pIn]
    (by
      intro v hv
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
      exacts [wp, wps, wps, wt1, wr, wk1, wk2, wW, wNB, wpc, wpIn])
  simp only [List.length_cons, List.length_nil] at hF1 hF2
  -- nonnegativity of the monomials that carry slack (linarith only knows atoms are ≥ 0)
  have n1 : 0 ≤ t1 * X := Nat.zero_le _
  have n2 : 0 ≤ t1 * pc * X := Nat.zero_le _
  have n3 : 0 ≤ r * X := Nat.zero_le _
  have n4 : 0 ≤ KM * (t1 * X) := Nat.zero_le _
  have n5 : 0 ≤ KM * (t1 * (pc * X)) := Nat.zero_le _
  have n6 : 0 ≤ KM * (r * X) := Nat.zero_le _
  linarith

#assert_std_axioms stepCostE_le

end WP.W7k2
