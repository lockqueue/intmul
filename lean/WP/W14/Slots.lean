import IntMul.Theorem5ComplexityAndCorrectness
import WP.W14.Schedule

/-!
# W14: numeric slots in the `E_step` unit

The snapshot's step closure (FTP:1505) budgets every intermediate error in absolute slots of
`2^-pChild` (0.01, 0.02, 0.6, …), which forces `pSub ≈ 2 · pChild`. Here the slots are measured in
the unit `eUnit p K = 2^-(p+K+10) = 2^(K+2) · 2^-pChild` (the per-step error unit `E_step`), which absorbs the
`O(r)` coefficients that appear at `pSub = pChild`.

* `StepSlots pSub m1 p K`: the scalar inequalities a schedule must satisfy at a step node `(p, K)`;
  they are stated with `2^K` in place of `t1`, `r` and `log₂ t1` (all `≤ 2^K`).
* `LeafSlot q_leaf p K`: the leaf inequality.
* `amplification_at`, `termD_at`: the closing arithmetic of the step closure.
-/

namespace WP.W14

open IntMul Real

/-- The `E_step` error unit `2^-(p+K+10)`. -/
noncomputable def eUnit (p K : ℕ) : ℝ := (2 : ℝ) ^ (-((p + K + 10 : ℕ) : ℤ))

theorem eUnit_pos (p K : ℕ) : 0 < eUnit p K := zpow_pos (by norm_num) _

theorem natPow_two_eq_zpow (K : ℕ) : ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ (K : ℤ) := by
  push_cast; exact (zpow_natCast (2 : ℝ) K).symm

/-- `2^K · eUnit = 2^-10 · 2^-p`. -/
theorem natPow_mul_eUnit (p K : ℕ) :
    ((2 ^ K : ℕ) : ℝ) * eUnit p K = (1 / 1024 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  rw [natPow_two_eq_zpow]
  unfold eUnit
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h : (K : ℤ) + -((p + K + 10 : ℕ) : ℤ) = (-10 : ℤ) + (-(p : ℤ)) := by push_cast; ring
  rw [h, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

theorem eUnit_le_pow (p K : ℕ) : eUnit p K ≤ (1 / 1024 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  rw [← natPow_mul_eUnit p K]
  have h1 : (1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have h2 := eUnit_pos p K
  nlinarith

theorem two_zpow_neg_le_one (p : ℕ) : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
  zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

theorem eUnit_le_small (p K : ℕ) : eUnit p K ≤ 1 / 1024 := by
  have h1 := eUnit_le_pow p K
  have h2 := two_zpow_neg_le_one p
  nlinarith

/-- `2^-pChild = 2^-(K+2) · eUnit`. -/
theorem pow_pChild_eq (p K : ℕ) :
    (2 : ℝ) ^ (-(pChild p K : ℤ)) = (2 : ℝ) ^ (-((K : ℤ) + 2)) * eUnit p K := by
  unfold eUnit
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), pChild_eq_additive]
  congr 1
  push_cast; ring

/-- `2^K · 2^-pChild ≤ 2^-14 · 2^-p` for `K ≥ 2`. -/
theorem natPow_mul_pow_pChild_le (p K : ℕ) (hK : 2 ≤ K) :
    ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤
      (1 / 16384 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  rw [natPow_two_eq_zpow, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), pChild_eq_additive]
  have h16 : (1 / 16384 : ℝ) = (2 : ℝ) ^ (-14 : ℤ) := by norm_num
  rw [h16, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  push_cast; omega

theorem cqme_nonneg (q : ℕ) : 0 ≤ complexQuantizeMaxErr q := by
  unfold complexQuantizeMaxErr; positivity

theorem rqme_nonneg (q : ℕ) : 0 ≤ realQuantizeMaxErr q := by
  rw [realQuantizeMaxErr_eq]; positivity

/-- The numeric slots a schedule must provide at a step node `(p, K)` (`pSub` = sub-step and spread
grid, `m1` = window half-width). `t1`, `r` and `log₂ t1` are bounded by `2^K`. -/
structure StepSlots (pSub m1 p K : ℕ) : Prop where
  window : WindowRules m1 p K
  hc : complexQuantizeMaxErr pSub ≤ 0.1 * eUnit p K
  hcr : 2 * complexQuantizeMaxErr pSub * (((2 ^ K : ℕ) : ℝ) + 2) ≤ 0.5 * eUnit p K
  hclog : complexQuantizeMaxErr pSub * (((2 ^ K : ℕ) : ℝ) + 1) ≤ 0.5 * eUnit p K
  hB12 : (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) +
      (2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(pSub : ℤ)) ≤ 0.5 * eUnit p K
  hsolve : ((2 ^ K : ℕ) : ℝ) * complexQuantizeMaxErr pSub ≤ 0.0001 * (2 : ℝ) ^ (-(p : ℤ))
  hratio : ((2 ^ K : ℕ) : ℝ) * (10 * realQuantizeMaxErr pSub) ≤ 0.0001
  hq24 : 24 ≤ pSub

/-- The leaf slot (the leaf closure needs `(K+1) · 4 · cqme(q_leaf) ≤ 0.6 · 2^-p`). -/
def LeafSlot (q_leaf p K : ℕ) : Prop :=
  ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf ≤ 0.6 * (2 : ℝ) ^ (-(p : ℤ))

namespace StepSlots

variable {pSub m1 p K : ℕ}

theorem hcr_le (h : StepSlots pSub m1 p K) {r : ℕ} (hr : r ≤ 2 ^ K) :
    2 * complexQuantizeMaxErr pSub * ((r : ℝ) + 2) ≤ 0.5 * eUnit p K := by
  have hr' : (r : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hr
  have hc := cqme_nonneg pSub
  nlinarith [h.hcr]

theorem hclog_le (h : StepSlots pSub m1 p K) {t1 : ℕ} (ht : Nat.log2 t1 ≤ 2 ^ K) :
    complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤ 0.5 * eUnit p K := by
  have ht' : (Nat.log2 t1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast ht
  have hc := cqme_nonneg pSub
  nlinarith [h.hclog]

theorem hsolve_le (h : StepSlots pSub m1 p K) {t1 : ℕ} (ht : t1 ≤ 2 ^ K) :
    (t1 : ℝ) * complexQuantizeMaxErr pSub ≤ 0.0001 * (2 : ℝ) ^ (-(p : ℤ)) := by
  have ht' : (t1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast ht
  have hc := cqme_nonneg pSub
  nlinarith [h.hsolve]

theorem ht1c_le (h : StepSlots pSub m1 p K) {t1 : ℕ} (ht : t1 ≤ 2 ^ K) :
    (t1 : ℝ) * complexQuantizeMaxErr pSub ≤ 0.001 := by
  have h1 := h.hsolve_le ht
  have h2 := two_zpow_neg_le_one p
  nlinarith

theorem hratio_le (h : StepSlots pSub m1 p K) {t1 : ℕ} (ht : t1 ≤ 2 ^ K) :
    (t1 : ℝ) * (10 * realQuantizeMaxErr pSub) ≤ 0.0001 := by
  have ht' : (t1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast ht
  have hc := rqme_nonneg pSub
  nlinarith [h.hratio]

theorem hq (h : StepSlots pSub m1 p K) :
    realQuantizeMaxErr pSub ≤ (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by
  rw [realQuantizeMaxErr_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by have := h.hq24; omega)

theorem hcoef (h : StepSlots pSub m1 p K) :
    (6 / (8 * Real.pi)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) +
      (2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(pSub : ℤ)) ≤ 1 / 2 := by
  have h1 := h.hB12
  have h2 := eUnit_le_small p K
  linarith

end StepSlots

/-! ### Closing arithmetic -/

/-- Terms B + C (spread, twists, child) after the `2.36 t1` amplification, in the `E_step` unit
(replaces T3:5006): `2.36 t1 (2.6 e M + 2^-pChild (r+1) M) < 0.036 · 2^-p M`. -/
theorem amplification_at (p K t1 r : ℕ) (M : ℝ) (hK : 2 ≤ K) (hr : 0 < r) (hM : 0 < M)
    (hsize : t1 * r = 2 ^ K) :
    (2.36 : ℝ) * (t1 : ℝ) * ((2.6 : ℝ) * eUnit p K * M +
      (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) <
      (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have ht1_nat : t1 ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_right t1 hr
  have ht1 : (t1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast ht1_nat
  have htr : (t1 : ℝ) * (r : ℝ) = ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hsize
  have he0 := eUnit_pos p K
  have hpc0 : (0 : ℝ) < (2 : ℝ) ^ (-(pChild p K : ℤ)) := zpow_pos (by norm_num) _
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hA : (t1 : ℝ) * eUnit p K ≤ (1 / 1024 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [← natPow_mul_eUnit p K]; exact mul_le_mul_of_nonneg_right ht1 he0.le
  have hB0 := natPow_mul_pow_pChild_le p K hK
  have hB : (t1 : ℝ) * ((r : ℝ) + 1) * (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤
      2 * ((1 / 16384 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) := by
    have h1 : (t1 : ℝ) * ((r : ℝ) + 1) ≤ 2 * ((2 ^ K : ℕ) : ℝ) := by nlinarith
    calc (t1 : ℝ) * ((r : ℝ) + 1) * (2 : ℝ) ^ (-(pChild p K : ℤ))
        ≤ 2 * ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
          mul_le_mul_of_nonneg_right h1 hpc0.le
      _ = 2 * (((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) := by ring
      _ ≤ 2 * ((1 / 16384 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) := by linarith
  have hexp : (2.36 : ℝ) * (t1 : ℝ) * ((2.6 : ℝ) * eUnit p K * M +
      (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)) =
      ((2.36 * 2.6 : ℝ) * ((t1 : ℝ) * eUnit p K) +
        (2.36 : ℝ) * ((t1 : ℝ) * ((r : ℝ) + 1) * (2 : ℝ) ^ (-(pChild p K : ℤ)))) * M := by ring
  rw [hexp]
  have hinner : (2.36 * 2.6 : ℝ) * ((t1 : ℝ) * eUnit p K) +
      (2.36 : ℝ) * ((t1 : ℝ) * ((r : ℝ) + 1) * (2 : ℝ) ^ (-(pChild p K : ℤ))) <
      (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by nlinarith
  exact mul_lt_mul_of_pos_right hinner hM

/-- Solver-internal rounding (replaces the snapshot's `hD_lt`, FTP:2196). -/
theorem termD_at (p K t1 pSub : ℕ) (M : ℝ) (hM1 : 1 ≤ M)
    (hc : complexQuantizeMaxErr pSub ≤ 0.1 * eUnit p K)
    (hsolve : (t1 : ℝ) * complexQuantizeMaxErr pSub ≤ 0.0001 * (2 : ℝ) ^ (-(p : ℤ))) :
    (2.001 : ℝ) * complexQuantizeMaxErr pSub + 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M <
      (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
  have hM_pos : 0 < M := by linarith
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have he := eUnit_le_pow p K
  have hc0 := cqme_nonneg pSub
  have hc' : complexQuantizeMaxErr pSub ≤ 0.0001 * (2 : ℝ) ^ (-(p : ℤ)) := by nlinarith
  have h1 : (2.001 : ℝ) * complexQuantizeMaxErr pSub ≤
      (2.001 * 0.0001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have : complexQuantizeMaxErr pSub ≤ complexQuantizeMaxErr pSub * M := by nlinarith
    nlinarith
  have h2 : 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M ≤
      8 * (0.0001 * (2 : ℝ) ^ (-(p : ℤ))) * M := by
    apply mul_le_mul_of_nonneg_right _ hM_pos.le; linarith
  have h3 : 0 < (2 : ℝ) ^ (-(p : ℤ)) * M := mul_pos hp0 hM_pos
  nlinarith

#assert_std_axioms eUnit_pos natPow_two_eq_zpow natPow_mul_eUnit eUnit_le_pow two_zpow_neg_le_one
  eUnit_le_small pow_pChild_eq natPow_mul_pow_pChild_le StepSlots.hcr_le StepSlots.hclog_le
  StepSlots.hsolve_le StepSlots.ht1c_le StepSlots.hratio_le StepSlots.hq StepSlots.hcoef
  amplification_at termD_at

end WP.W14
