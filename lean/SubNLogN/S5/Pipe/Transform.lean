/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.ExecutablePipeline
import WP.Top.Current6
import WP.W4.Main
import WP.W4f.Top
import WP.W4o.OddRoute
import WP.W5.Bound
import WP.W9b.AltSum
import WP.W9c.Main
import WP.W9d.Final
import WP.W9s.Main
import WP.W9fBind.Plug
import WP.W9gx.Final
import WP.W10b.Main
import WP.W11b.Final
import Contracts.W9.Ret

/-!
# Component S5 (`Pipe/Transform.lean`): existing radix-2 `W9_pipeline`, `pipeBound` summands

**Scope (honest summary).**

What is proved:
* `w4_all_proved`, `w6a_all_proved`, `w9_preNode_proved`, `w9_postNode_proved`,
  `w9_leafFFT_proved`, `w9_pipeline_proved`: assembly of existing proved kernel contracts (`WP.W3*`,
  `WP.W4*`, `WP.W6a`, `WP.W9*`) into `TMFw.Contracts.W9_pipeline Mul` for every `Mul` with
  `W5_mulAt Mul`. This is the machine-level contract of the EXISTING radix-2 IntMul transform
  pipeline: a closed `BLoc` program computing `levelEvalV cSpec p_in xs` (i.e.
  `IntMul.computablePaperFastDFT p_in cSpec` mapped over the root nodes: Sinc-Gaussian spreading,
  the radix-2 synthetic FFT `W9_synFFT`, radix-2 Cooley-Tukey leaves) within
  `C * (pipeBound Mul wd cSpec p_in 0 xs.length + (tapeSyms cSpec).length + 1)` steps. This module
  only wires existing proofs together; it adds no kernel.
* `T3_pow15_le_explicit`, `T3_pow15_le`, `T3_mul_log2_pow15_le_explicit`: growth bounds for the
  Toom-3 cost recurrence `T3` (`(TMFw.Contracts.T3 c0 c1 w0 w) ^ 15 ≤ C * w ^ 22`, i.e. exponent `22/15`).
* `spread_slot_pow15_le_of_pos`, `spread_slot_pow15_le_explicit`, `spread_slot_pow15_le`: arithmetic
  bounds `((W8.hL n + 1) * (cnt * T3 c0 c1 w0 wid)) ^ 15 ≤ (A * n) ^ 15 * (Nat.log2 n) ^ 14` under
  numeric slot-shape hypotheses on `cnt`, `wid`.
* `specLeafK`, `hKLeaf`, `hKLeaf_succ_le`: leaf log-size of the existing headline schedule
  `W8.hSpec n` (`hKLeaf n + 1 ≤ 4 * Nat.log2 (Nat.log2 n) + 37` for `n ≥ 2`).
* `specLeafLin`, `specStepLinSum`, `specSpreadSlots`, `specTwistColLeafSlots`,
  `slotsCost_specSlots_eq`: exact split of `WP.W10b.specSlots` (hence, via
  `WP.W10b.pipeBound_eq_slots`, of `pipeBound`) into step-linear work, leaf-linear work, spread
  multiplication slots, and twist/column/leaf multiplication slots.
* `specLeafLin_headline_le`, `specTwistColLeafSlots_headline_le`, `leaf_and_twistColLeaf_pow15_le`,
  `specSpreadSlots_headline_pow15_le`: along `W8.hSpec n`, with `Mul = T3 c0 c1 w0`, three of the
  four summands (leaf-linear work, twist/column/leaf slots, spread slots) are bounded by
  `sqrtLogLogEnvelope C n = C * n * (Nat.sqrt (128 * Nat.log2 n) + 1) * (Nat.log2 (Nat.log2 n) + 2)`
  or satisfy `(f n) ^ 15 ≤ (A * n) ^ 15 * (Nat.log2 n) ^ 14`. These are bounds on summands of the
  proved step bound of the existing machine.

What is NOT proved: the fourth summand `specStepLinSum` (the step levels' linear work, which
contains the transposes and the radix-2 synthetic-FFT passes `W9.synBound`) is not bounded here;
the existing analysis `WP.W10b.stepLin_le` bounds each step level by `2^16 · E · (S + 1) · (K + 1)`,
which only gives an `O(n log n)`-type total. So no `o(n log n)` bound for the existing pipeline
follows from this module. Nothing in `S5/Pipe/` implements the Walsh-bridge transform (bridge §4,
Walsh layers §5, triple networks App. A, direct tensor FFT §6; see `SubNLogN/Machine/`). `sqrtLogLogEnvelope` is an explicit arithmetic
envelope with proved growth bounds; it is related to the machine only through the domination
theorems above.
-/

namespace WP.W10b

/-- Alias `P` for `hP` (`leafPrecision (W8.hL n) (W8.hP0 n) (W8.hK0 n)`), matching the `WP.W10b.Headline`
module documentation. -/
abbrev P (n : ℕ) : ℕ := hP n

end WP.W10b

namespace SubNLogN.S5.Pipe

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul IntMulTM.Contracts WP.Top

/-! ## Part 1: Unconditional `W9_pipeline` Witness -/

/-- All of `W4_all` is unconditionally proved from `WP.W4`, `WP.W4f`, `WP.W4o`, and `w4_moveRecord`. -/
theorem w4_all_proved : W4_all :=
  ⟨TMFw.W4.W4_transpose_holds .down .down,
   WP.W4f.W4_oddStrideFactor_holds,
   TMFw.W4o.W4_oddRoute_holds,
   w4_moveRecord⟩

/-- All of `W6a_all` is unconditionally proved from `WP.W6a` and `WP.W3`. -/
theorem w6a_all_proved : W6a_all :=
  WP.W6a.W6a_holds WP.W3.W3_subNat_holds

/-- Unconditional `W9_preNode` witness for any `Mul` with `W5_mulAt Mul`: the PRE node of the
existing radix-2 pipeline (transpose, alternating sum, spread, pre-twist, radix-2 synthetic FFT,
post-twist, emit), assembled from existing phase contracts. -/
theorem w9_preNode_proved (Mul : ℕ → ℕ) (hM : TMFw.Contracts.W5_mulAt Mul) :
    TMFw.Contracts.W9_preNode Mul := by
  have h3 : W3_all := WP.Top.W3_all_holds
  have h4 : W4_all := w4_all_proved
  have h6 : W6a_all := w6a_all_proved
  have hAddInt : W3_addInt := TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds
  have hSubInt : W3_subInt := TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds
  exact WP.W9comp.W9_preNode_of_phases_holds Mul
    (WP.W9b.W9_preTranspose_holds (TMFw.W4.W4_transpose_holds .down .up))
    (WP.W9b.W9_altSum_holds hAddInt hSubInt
      WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds
      TMFw.W3s.W3_shlVar_holds TMFw.W3s.W3_shrVar_holds)
    (WP.W9c.W9_spread_stage Mul hM h3 h4 h6)
    (WP.W9d.W9_preTwist_holds Mul hM h3 h4 h6)
    (WP.W9s.W9_synFFT_holds hAddInt hSubInt)
    (WP.W9d.W9_postTwist_holds Mul hM h3 h4 h6)
    WP.W9b.W9_emitRows_holds

/-- Unconditional `W9_postNode` witness for any `Mul` with `W5_mulAt Mul`: the POST node of the
existing radix-2 pipeline, assembled from existing phase contracts. -/
theorem w9_postNode_proved (Mul : ℕ → ℕ) (hM : TMFw.Contracts.W5_mulAt Mul) :
    TMFw.Contracts.W9_postNode Mul := by
  have h3 : W3_all := WP.Top.W3_all_holds
  have h4 : W4_all := w4_all_proved
  have h6 : W6a_all := w6a_all_proved
  have h9e := WP.W9e.W9e_holds h3 h4
  exact WP.W9comp.W9_postNode_of_phases_holds Mul
    h9e.1
    h9e.2.1
    (WP.W9fBind.W9_columns_holds_final Mul hM h3 h4 h6)
    h9e.2.2

/-- Unconditional `W9_leafFFT` witness for any `Mul` with `W5_mulAt Mul`: the existing radix-2
Cooley-Tukey leaf FFT (`WP.W9gx.W9_leafFFT_holds`). -/
theorem w9_leafFFT_proved (Mul : ℕ → ℕ) (hM : TMFw.Contracts.W5_mulAt Mul) :
    TMFw.Contracts.W9_leafFFT Mul :=
  WP.W9gx.W9_leafFFT_holds Mul hM
    (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    TMFw.W3s.W3_shlVar_holds
    TMFw.W3s.W3_shrVar_holds

/-- **Unconditional `W9_pipeline` witness (`w9_pipeline_proved`):**
Combines `WP.W9a.W9_pipeline_of_levels_holds`, `WP.W9a.W9_levels_of_kernels_holds`,
`WP.W9comp.W9_preNode_of_phases_holds`, `WP.W9comp.W9_postNode_of_phases_holds`,
and all proved phase kernels. This is the machine contract of the EXISTING radix-2 IntMul transform
pipeline (output `levelEvalV cSpec p_in xs`, i.e. `computablePaperFastDFT` mapped over the root
nodes, cost `C * (pipeBound Mul wd cSpec p_in 0 xs.length + (tapeSyms cSpec).length + 1)`), not of
the paper's new transform. -/
theorem w9_pipeline_proved (Mul : ℕ → ℕ) (hM : TMFw.Contracts.W5_mulAt Mul) :
    TMFw.Contracts.W9_pipeline Mul := by
  obtain ⟨hpl, hll, hpol⟩ :=
    WP.W9a.W9_levels_of_kernels_holds Mul
      WP.W9a.W9_sweep_holds
      TMFw.Contracts.w9_retMark
      WP.W9a.W9_retFlip_holds
      (w9_preNode_proved Mul hM)
      (w9_leafFFT_proved Mul hM)
      (w9_postNode_proved Mul hM)
  exact WP.W9a.W9_pipeline_of_levels_holds Mul WP.W9a.W9_level_holds hpl hll hpol

/-! ## Part 2: Toom-3 Exponent-`22/15` Lemma (`T3_pow15_le` and `spread_slot_pow15_le`) -/

/-- Base constant for the `T3` grid bound: `T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5) + 1`. -/
def T3GridBase (c0 c1 w0 : ℕ) : ℕ :=
  T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5) + 1

lemma T3GridBase_pos (c0 c1 w0 : ℕ) : 0 < T3GridBase c0 c1 w0 := by
  unfold T3GridBase; omega

/-- Explicit constant `C_T3 = (5 * T3GridBase c0 c1 w0) ^ 15 > 0` for `T3_pow15_le`. -/
def T3Pow15Const (c0 c1 w0 : ℕ) : ℕ :=
  (5 * T3GridBase c0 c1 w0) ^ 15

lemma T3Pow15Const_pos (c0 c1 w0 : ℕ) : 0 < T3Pow15Const c0 c1 w0 := by
  unfold T3Pow15Const
  have : 0 < 5 * T3GridBase c0 c1 w0 := Nat.mul_pos (by decide) (T3GridBase_pos c0 c1 w0)
  exact Nat.pow_pos this

lemma pow_right_comm' (a m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, mul_comm, pow_mul]

/-- Explicit Toom-3 exponent-`22/15` bound: for all `w ≥ 1`,
`(TMFw.Contracts.T3 c0 c1 w0 w) ^ 15 ≤ T3Pow15Const c0 c1 w0 * w ^ 22`. -/
theorem T3_pow15_le_explicit (c0 c1 w0 : ℕ) {w : ℕ} (hw : 1 ≤ w) :
    (T3 c0 c1 w0 w) ^ 15 ≤ T3Pow15Const c0 c1 w0 * w ^ 22 := by
  obtain ⟨j, hj1, hj2⟩ := WP.W5.exists_pow3 w hw
  have hgrid := WP.W5.T3_grid c0 c1 w0 (j + 1) w (by omega)
  have hT : T3 c0 c1 w0 w ≤ (5 * T3GridBase c0 c1 w0) * 5 ^ j := by
    have hle : T3 c0 c1 w0 w ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1) :=
      le_trans (Nat.le_add_right _ _) hgrid
    have hbase : T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5) ≤ T3GridBase c0 c1 w0 := by
      unfold T3GridBase; omega
    calc T3 c0 c1 w0 w
        ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1) := hle
      _ ≤ T3GridBase c0 c1 w0 * 5 ^ (j + 1) := Nat.mul_le_mul_right _ hbase
      _ = (5 * T3GridBase c0 c1 w0) * 5 ^ j := by rw [pow_succ]; ring
  have h5_3 : (5 ^ j) ^ 15 ≤ w ^ 22 := by
    have hdec : 5 ^ 15 ≤ 3 ^ 22 := by decide
    calc (5 ^ j) ^ 15 = (5 ^ 15) ^ j := pow_right_comm' 5 j 15
      _ ≤ (3 ^ 22) ^ j := Nat.pow_le_pow_left hdec j
      _ = (3 ^ j) ^ 22 := pow_right_comm' 3 22 j
      _ ≤ w ^ 22 := Nat.pow_le_pow_left hj1 22
  calc (T3 c0 c1 w0 w) ^ 15
      ≤ ((5 * T3GridBase c0 c1 w0) * 5 ^ j) ^ 15 := Nat.pow_le_pow_left hT 15
    _ = T3Pow15Const c0 c1 w0 * (5 ^ j) ^ 15 := by unfold T3Pow15Const; rw [mul_pow]
    _ ≤ T3Pow15Const c0 c1 w0 * w ^ 22 := Nat.mul_le_mul_left _ h5_3

/-- **Toom-3 Exponent-`22/15` Lemma (`T3_pow15_le`):**
There exists a constant `C_T3 > 0` such that for all `w ≥ 1`,
`(TMFw.Contracts.T3 c0 c1 w0 w) ^ 15 ≤ C_T3 * w ^ 22`. -/
theorem T3_pow15_le (c0 c1 w0 : ℕ) :
    ∃ C_T3 > 0, ∀ w ≥ 1, (TMFw.Contracts.T3 c0 c1 w0 w) ^ 15 ≤ C_T3 * w ^ 22 :=
  ⟨T3Pow15Const c0 c1 w0, T3Pow15Const_pos c0 c1 w0, fun _ hw => T3_pow15_le_explicit c0 c1 w0 hw⟩

/-- Linear exponential absorption: `600 ^ j * (j + 1) ≤ 601 * 601 ^ j` for all `j : ℕ`. -/
lemma pow600_mul_succ_le (j : ℕ) : 600 ^ j * (j + 1) ≤ 601 * 601 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hj : j + 1 ≤ 600
    · have h1 : j + 1 + 1 ≤ 601 := by omega
      have h2 : 600 ^ (j + 1) ≤ 601 ^ (j + 1) := Nat.pow_le_pow_left (by decide) _
      calc 600 ^ (j + 1) * (j + 1 + 1) ≤ 601 ^ (j + 1) * 601 := Nat.mul_le_mul h2 h1
        _ = 601 * 601 ^ (j + 1) := Nat.mul_comm _ _
    · have h3 : 600 * (j + 1 + 1) ≤ 601 * (j + 1) := by omega
      calc 600 ^ (j + 1) * (j + 1 + 1) = 600 ^ j * (600 * (j + 1 + 1)) := by ring
        _ ≤ 600 ^ j * (601 * (j + 1)) := Nat.mul_le_mul_left _ h3
        _ = 601 * (600 ^ j * (j + 1)) := by ring
        _ ≤ 601 * (601 * 601 ^ j) := Nat.mul_le_mul_left 601 ih
        _ = 601 * 601 ^ (j + 1) := by ring

/-- Strict exponent gap `5 ^ 15 < 3 ^ 22` absorbs `(j + 1) ^ 15`:
`(5 ^ j * (j + 1)) ^ 15 ≤ 601 ^ 15 * (3 ^ j) ^ 22`. -/
lemma pow5_mul_succ_pow15_le (j : ℕ) :
    (5 ^ j * (j + 1)) ^ 15 ≤ 601 ^ 15 * (3 ^ j) ^ 22 := by
  have h1 : (5 ^ j * (j + 1)) * 600 ^ j ≤ 601 * (5 * 601) ^ j := by
    calc (5 ^ j * (j + 1)) * 600 ^ j = 5 ^ j * (600 ^ j * (j + 1)) := by ring
      _ ≤ 5 ^ j * (601 * 601 ^ j) := Nat.mul_le_mul_left _ (pow600_mul_succ_le j)
      _ = 601 * (5 ^ j * 601 ^ j) := by ring
      _ = 601 * (5 * 601) ^ j := by rw [← mul_pow]
  have h2 : ((5 ^ j * (j + 1)) * 600 ^ j) ^ 15 ≤ (601 * (5 * 601) ^ j) ^ 15 :=
    Nat.pow_le_pow_left h1 15
  have hdec : (5 * 601) ^ 15 ≤ 3 ^ 22 * 600 ^ 15 := by decide
  have h3 : (((5 * 601) ^ j) ^ 15) ≤ (3 ^ j) ^ 22 * (600 ^ j) ^ 15 := by
    calc ((5 * 601) ^ j) ^ 15 = ((5 * 601) ^ 15) ^ j := pow_right_comm' (5 * 601) j 15
      _ ≤ (3 ^ 22 * 600 ^ 15) ^ j := Nat.pow_le_pow_left hdec j
      _ = (3 ^ 22) ^ j * (600 ^ 15) ^ j := by rw [mul_pow]
      _ = (3 ^ j) ^ 22 * (600 ^ j) ^ 15 := by
          rw [pow_right_comm' 3 22 j, pow_right_comm' 600 15 j]
  have hpos : 0 < (600 ^ j) ^ 15 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (5 ^ j * (j + 1)) ^ 15 * (600 ^ j) ^ 15
      = ((5 ^ j * (j + 1)) * 600 ^ j) ^ 15 := by ring
    _ ≤ (601 * (5 * 601) ^ j) ^ 15 := h2
    _ = 601 ^ 15 * ((5 * 601) ^ j) ^ 15 := by rw [mul_pow]
    _ ≤ 601 ^ 15 * ((3 ^ j) ^ 22 * (600 ^ j) ^ 15) := Nat.mul_le_mul_left _ h3
    _ = 601 ^ 15 * (3 ^ j) ^ 22 * (600 ^ j) ^ 15 := by ring

/-- Refined Toom-3 exponent-`22/15` bound absorbing `Nat.log2 w + 3`: for all `w ≥ 1`,
`((Nat.log2 w + 3) * T3 c0 c1 w0 w) ^ 15 ≤ (12020 * T3GridBase c0 c1 w0) ^ 15 * w ^ 22`. -/
theorem T3_mul_log2_pow15_le_explicit (c0 c1 w0 : ℕ) {w : ℕ} (hw : 1 ≤ w) :
    ((Nat.log2 w + 3) * T3 c0 c1 w0 w) ^ 15 ≤
      (12020 * T3GridBase c0 c1 w0) ^ 15 * w ^ 22 := by
  obtain ⟨j, hj1, hj2⟩ := WP.W5.exists_pow3 w hw
  have hgrid := WP.W5.T3_grid c0 c1 w0 (j + 1) w (by omega)
  have hT : T3 c0 c1 w0 w ≤ (5 * T3GridBase c0 c1 w0) * 5 ^ j := by
    have hle : T3 c0 c1 w0 w ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1) :=
      le_trans (Nat.le_add_right _ _) hgrid
    have hbase : T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5) ≤ T3GridBase c0 c1 w0 := by
      unfold T3GridBase; omega
    calc T3 c0 c1 w0 w
        ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1) := hle
      _ ≤ T3GridBase c0 c1 w0 * 5 ^ (j + 1) := Nat.mul_le_mul_right _ hbase
      _ = (5 * T3GridBase c0 c1 w0) * 5 ^ j := by rw [pow_succ]; ring
  have hlog : Nat.log2 w + 3 ≤ 4 * (j + 1) := by
    have hlt : Nat.log2 w < 2 * (j + 1) := by
      rw [Nat.log2_lt (by omega)]
      calc w < 3 ^ (j + 1) := hj2
        _ ≤ 4 ^ (j + 1) := Nat.pow_le_pow_left (by norm_num) _
        _ = 2 ^ (2 * (j + 1)) := by rw [pow_mul]; norm_num
    omega
  have hprod : (Nat.log2 w + 3) * T3 c0 c1 w0 w ≤
      (20 * T3GridBase c0 c1 w0) * (5 ^ j * (j + 1)) := by
    calc (Nat.log2 w + 3) * T3 c0 c1 w0 w
        ≤ (4 * (j + 1)) * ((5 * T3GridBase c0 c1 w0) * 5 ^ j) := Nat.mul_le_mul hlog hT
      _ = (20 * T3GridBase c0 c1 w0) * (5 ^ j * (j + 1)) := by ring
  have hjw : (5 ^ j * (j + 1)) ^ 15 ≤ 601 ^ 15 * w ^ 22 :=
    le_trans (pow5_mul_succ_pow15_le j) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hj1 22))
  calc ((Nat.log2 w + 3) * T3 c0 c1 w0 w) ^ 15
      ≤ ((20 * T3GridBase c0 c1 w0) * (5 ^ j * (j + 1))) ^ 15 := Nat.pow_le_pow_left hprod 15
    _ = (20 * T3GridBase c0 c1 w0) ^ 15 * (5 ^ j * (j + 1)) ^ 15 := by rw [mul_pow]
    _ ≤ (20 * T3GridBase c0 c1 w0) ^ 15 * (601 ^ 15 * w ^ 22) := Nat.mul_le_mul_left _ hjw
    _ = ((20 * T3GridBase c0 c1 w0) * 601) ^ 15 * w ^ 22 := by rw [mul_pow]; ring
    _ = (12020 * T3GridBase c0 c1 w0) ^ 15 * w ^ 22 := by ring

/-- Cube bound `(k + 3) ^ 3 ≤ 64 * 2 ^ k` for all `k : ℕ`. -/
lemma succ_add_two_cube_le (k : ℕ) : (k + 3) ^ 3 ≤ 64 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hsq : (k + 3) ^ 2 ≤ 16 * 2 ^ k := by
      have h := WP.W10.succ_sq_le_four_mul_two_pow (k + 2)
      have e : 4 * 2 ^ (k + 2) = 16 * 2 ^ k := by ring
      have ek : k + 2 + 1 = k + 3 := rfl
      rw [ek, e] at h
      exact h
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    have e1 : (k + 1 + 3) ^ 3 = (k + 3) ^ 3 + 3 * (k + 3) ^ 2 + 3 * k + 10 := by ring
    have e2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- For `b ≥ 1`, `(Nat.log2 b + 3) ^ 15 ≤ 4 ^ 15 * b ^ 5`. -/
lemma log2_add_three_pow15_le {b : ℕ} (hb : 1 ≤ b) :
    (Nat.log2 b + 3) ^ 15 ≤ 4 ^ 15 * b ^ 5 := by
  have h1 : (Nat.log2 b + 3) ^ 3 ≤ 64 * b := by
    calc (Nat.log2 b + 3) ^ 3 ≤ 64 * 2 ^ Nat.log2 b := succ_add_two_cube_le (Nat.log2 b)
      _ ≤ 64 * b := Nat.mul_le_mul_left 64 (Nat.log2_self_le (by omega))
  calc (Nat.log2 b + 3) ^ 15 = ((Nat.log2 b + 3) ^ 3) ^ 5 := by rw [← pow_mul]
    _ ≤ (64 * b) ^ 5 := Nat.pow_le_pow_left h1 5
    _ = 64 ^ 5 * b ^ 5 := by rw [mul_pow]
    _ = 4 ^ 15 * b ^ 5 := by norm_num

/-- Explicit constant `A_sp` for `spread_slot_pow15_le`. -/
def spreadSlotConst (c0 c1 w0 cw : ℕ) : ℕ :=
  12020 * T3GridBase c0 c1 w0 * 4 * (6144 * (cw + 181)) * (96 * (cw + 181) ^ 2)

lemma spreadSlotConst_pos (c0 c1 w0 cw : ℕ) : 0 < spreadSlotConst c0 c1 w0 cw := by
  unfold spreadSlotConst
  have h0 := T3GridBase_pos c0 c1 w0
  positivity

/-- Explicit spread-slot sub-`n log n` bound for `wid ≥ 1` under `cnt * wid ≤ 192 * E * (S + 1)`
and `wid ≤ 24 * (S + 1) ^ 2` along `W8.hSpec n`. -/
theorem spread_slot_pow15_le_of_pos (c0 c1 w0 cw : ℕ) {n cnt wid : ℕ} (hn : 2 ≤ n)
    (hwid1 : 1 ≤ wid)
    (hcw : cnt * wid ≤ 192 * 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1))
    (hwid : wid ≤ 24 * (WP.W10b.Sb cw n + 1) ^ 2) :
    ((W8.hL n + 1) * (cnt * T3 c0 c1 w0 wid)) ^ 15 ≤
      (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  set b := Nat.log2 n
  have hb1 : 1 ≤ b := WP.W10b.one_le_log2 hn
  have hb_succ : b + 1 ≤ 2 * b := by omega
  have hS := WP.W10b.Sb_succ_le cw n
  have hEl := WP.W10b.E_mul_le hn
  have hL : W8.hL n + 1 ≤ Nat.log2 b + 3 :=
    Nat.succ_le_succ (WP.W10b.hL_le_loglog hn)
  set C₁ := 6144 * (cw + 181)
  set C₂ := 96 * (cw + 181) ^ 2
  have hC₂_pos : 1 ≤ C₂ := by dsimp [C₂]; nlinarith
  have hcw_n : cnt * wid ≤ C₁ * n := by
    have hES : 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1) ≤ 32 * (cw + 181) * n := by
      calc 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1)
          ≤ 2 ^ W8.hK0 n * ((cw + 181) * (b + 1)) := Nat.mul_le_mul_left _ hS
        _ = (cw + 181) * (2 ^ W8.hK0 n * (b + 1)) := by ring
        _ ≤ (cw + 181) * (32 * n) := Nat.mul_le_mul_left _ hEl
        _ = 32 * (cw + 181) * n := by ring
    calc cnt * wid ≤ 192 * (2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1)) := by linarith
      _ ≤ 192 * (32 * (cw + 181) * n) := Nat.mul_le_mul_left 192 hES
      _ = C₁ * n := by dsimp [C₁]; ring
  have hwid_b : wid ≤ C₂ * b ^ 2 := by
    have hS_b : WP.W10b.Sb cw n + 1 ≤ 2 * (cw + 181) * b := by
      calc WP.W10b.Sb cw n + 1 ≤ (cw + 181) * (b + 1) := hS
        _ ≤ (cw + 181) * (2 * b) := Nat.mul_le_mul_left _ hb_succ
        _ = 2 * (cw + 181) * b := by ring
    calc wid ≤ 24 * (WP.W10b.Sb cw n + 1) ^ 2 := hwid
      _ ≤ 24 * (2 * (cw + 181) * b) ^ 2 := Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hS_b 2)
      _ = C₂ * b ^ 2 := by dsimp [C₂]; ring
  rcases le_total wid b with hwb | hbw
  · -- Small width: `wid ≤ b`.
    have hT := T3_pow15_le_explicit c0 c1 w0 hwid1
    have hlog15 : (W8.hL n + 1) ^ 15 ≤ 4 ^ 15 * b ^ 7 := by
      calc (W8.hL n + 1) ^ 15 ≤ (Nat.log2 b + 3) ^ 15 := Nat.pow_le_pow_left hL 15
        _ ≤ 4 ^ 15 * b ^ 5 := log2_add_three_pow15_le hb1
        _ ≤ 4 ^ 15 * b ^ 7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb1 (by decide))
    have hw7 : wid ^ 7 ≤ b ^ 7 := Nat.pow_le_pow_left hwb 7
    have hbase_le : 4 * (5 * T3GridBase c0 c1 w0) * C₁ ≤ spreadSlotConst c0 c1 w0 cw := by
      change 4 * (5 * T3GridBase c0 c1 w0) * C₁ ≤
        12020 * T3GridBase c0 c1 w0 * 4 * C₁ * C₂
      calc 4 * (5 * T3GridBase c0 c1 w0) * C₁
          = (20 * (T3GridBase c0 c1 w0 * C₁)) * 1 := by ring
        _ ≤ (48080 * (T3GridBase c0 c1 w0 * C₁)) * C₂ :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) hC₂_pos
        _ = 12020 * T3GridBase c0 c1 w0 * 4 * C₁ * C₂ := by ring
    calc ((W8.hL n + 1) * (cnt * T3 c0 c1 w0 wid)) ^ 15
        = (W8.hL n + 1) ^ 15 * (cnt ^ 15 * (T3 c0 c1 w0 wid) ^ 15) := by ring
      _ ≤ (4 ^ 15 * b ^ 7) * (cnt ^ 15 * (T3Pow15Const c0 c1 w0 * wid ^ 22)) :=
          Nat.mul_le_mul hlog15 (Nat.mul_le_mul_left _ hT)
      _ = 4 ^ 15 * T3Pow15Const c0 c1 w0 * (cnt * wid) ^ 15 * (b ^ 7 * wid ^ 7) := by ring
      _ ≤ 4 ^ 15 * T3Pow15Const c0 c1 w0 * (C₁ * n) ^ 15 * (b ^ 7 * b ^ 7) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcw_n 15))
            (Nat.mul_le_mul_left _ hw7)
      _ = (4 * (5 * T3GridBase c0 c1 w0) * C₁ * n) ^ 15 * b ^ 14 := by
          unfold T3Pow15Const; ring
      _ ≤ (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * b ^ 14 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right n hbase_le) 15)
  · -- Large width: `b ≤ wid`.
    have hL_wid : W8.hL n + 1 ≤ Nat.log2 wid + 3 := by
      have := IntMul.nat_log2_mono hbw
      omega
    have hT := T3_mul_log2_pow15_le_explicit c0 c1 w0 hwid1
    have hT' : ((W8.hL n + 1) * T3 c0 c1 w0 wid) ^ 15 ≤
        (12020 * T3GridBase c0 c1 w0) ^ 15 * wid ^ 22 :=
      le_trans (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hL_wid) 15) hT
    have hw7 : wid ^ 7 ≤ C₂ ^ 15 * b ^ 14 := by
      calc wid ^ 7 ≤ (C₂ * b ^ 2) ^ 7 := Nat.pow_le_pow_left hwid_b 7
        _ = C₂ ^ 7 * b ^ 14 := by ring
        _ ≤ C₂ ^ 15 * b ^ 14 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hC₂_pos (by decide))
    have hbase_le : 12020 * T3GridBase c0 c1 w0 * C₁ * C₂ ≤ spreadSlotConst c0 c1 w0 cw := by
      change 12020 * T3GridBase c0 c1 w0 * C₁ * C₂ ≤
        12020 * T3GridBase c0 c1 w0 * 4 * C₁ * C₂
      calc 12020 * T3GridBase c0 c1 w0 * C₁ * C₂
          = 1 * (12020 * T3GridBase c0 c1 w0 * C₁ * C₂) := by ring
        _ ≤ 4 * (12020 * T3GridBase c0 c1 w0 * C₁ * C₂) := Nat.mul_le_mul_right _ (by decide)
        _ = 12020 * T3GridBase c0 c1 w0 * 4 * C₁ * C₂ := by ring
    calc ((W8.hL n + 1) * (cnt * T3 c0 c1 w0 wid)) ^ 15
        = cnt ^ 15 * ((W8.hL n + 1) * T3 c0 c1 w0 wid) ^ 15 := by ring
      _ ≤ cnt ^ 15 * ((12020 * T3GridBase c0 c1 w0) ^ 15 * wid ^ 22) :=
          Nat.mul_le_mul_left _ hT'
      _ = (12020 * T3GridBase c0 c1 w0) ^ 15 * (cnt * wid) ^ 15 * wid ^ 7 := by ring
      _ ≤ (12020 * T3GridBase c0 c1 w0) ^ 15 * (C₁ * n) ^ 15 * (C₂ ^ 15 * b ^ 14) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcw_n 15)) hw7
      _ = (12020 * T3GridBase c0 c1 w0 * C₁ * C₂ * n) ^ 15 * b ^ 14 := by ring
      _ ≤ (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * b ^ 14 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right n hbase_le) 15)

/-- Explicit spread-slot sub-`n log n` bound under all three `spread_slot_ok` / `chain_slots`
conditions (`cnt ≤ 8 * E`, `cnt * wid ≤ 192 * E * (S + 1)`, `wid ≤ 24 * (S + 1) ^ 2`), without
requiring `1 ≤ wid`. -/
theorem spread_slot_pow15_le_explicit (c0 c1 w0 cw : ℕ) {n cnt wid : ℕ} (hn : 2 ≤ n)
    (hcnt : cnt ≤ 8 * 2 ^ W8.hK0 n)
    (hcw : cnt * wid ≤ 192 * 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1))
    (hwid : wid ≤ 24 * (WP.W10b.Sb cw n + 1) ^ 2) :
    ((W8.hL n + 1) * (cnt * T3 c0 c1 w0 wid)) ^ 15 ≤
      (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  rcases Nat.eq_zero_or_pos wid with rfl | hwid1
  · have hT01 : T3 c0 c1 w0 0 ≤ T3 c0 c1 w0 1 := T3_mono c0 c1 w0 (by decide)
    have hcw1 : cnt * 1 ≤ 192 * 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1) := by
      have : 8 * 2 ^ W8.hK0 n ≤ 192 * 2 ^ W8.hK0 n * 1 := by omega
      have hS1 : 1 ≤ WP.W10b.Sb cw n + 1 := Nat.succ_pos _
      calc cnt * 1 = cnt := Nat.mul_one cnt
        _ ≤ 8 * 2 ^ W8.hK0 n := hcnt
        _ ≤ 192 * 2 ^ W8.hK0 n * 1 := this
        _ ≤ 192 * 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1) := Nat.mul_le_mul_left _ hS1
    have hwid1_le : 1 ≤ 24 * (WP.W10b.Sb cw n + 1) ^ 2 := by
      have : 1 ≤ (WP.W10b.Sb cw n + 1) ^ 2 := Nat.one_le_pow 2 _ (Nat.succ_pos _)
      omega
    have h1 := spread_slot_pow15_le_of_pos c0 c1 w0 cw hn (le_rfl : 1 ≤ 1) hcw1 hwid1_le
    exact le_trans
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT01)) 15) h1
  · exact spread_slot_pow15_le_of_pos c0 c1 w0 cw hn hwid1 hcw hwid

/-- **Spread-slot arithmetic bound (`spread_slot_pow15_le`):**
There exists `A_sp > 0` such that for all `n ≥ 2` and all `cnt`, `wid` satisfying the numeric
slot-shape conditions of `WP.W10b.spread_slot_ok` (stated with `W8.hK0 n` and `WP.W10b.Sb cw n`):
`((W8.hL n + 1) * (cnt * TMFw.Contracts.T3 c0 c1 w0 wid)) ^ 15 ≤ (A_sp * n) ^ 15 * (Nat.log2 n) ^ 14`. -/
theorem spread_slot_pow15_le (c0 c1 w0 cw : ℕ) :
    ∃ A_sp > 0, ∀ n ≥ 2, ∀ cnt wid : ℕ,
      (cnt ≤ 8 * 2 ^ W8.hK0 n ∨ 1 ≤ wid) →
      cnt * wid ≤ 192 * 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1) →
      wid ≤ 24 * (WP.W10b.Sb cw n + 1) ^ 2 →
      ((W8.hL n + 1) * (cnt * TMFw.Contracts.T3 c0 c1 w0 wid)) ^ 15 ≤
        (A_sp * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  refine ⟨spreadSlotConst c0 c1 w0 cw, spreadSlotConst_pos c0 c1 w0 cw, ?_⟩
  intro n hn cnt wid hcond hcw hwid
  rcases hcond with hcnt | hwid1
  · exact spread_slot_pow15_le_explicit c0 c1 w0 cw hn hcnt hcw hwid
  · exact spread_slot_pow15_le_of_pos c0 c1 w0 cw hn hwid1 hcw hwid

/-! ## Part 3: Bounds on three of the four summands of `pipeBound` along `W8.hSpec n` -/

/-- The leaf log-size `K_leaf` of a `QuantizedFastDFTSpec` schedule tree. -/
def specLeafK : QuantizedFastDFTSpec → ℕ
  | .base _ R => Nat.log2 R
  | .step _ _ _ _ _ _ child => specLeafK child

/-- The leaf log-size `K_leaf` of the headline schedule `W8.hSpec n`. -/
def hKLeaf (n : ℕ) : ℕ := specLeafK (W8.hSpec n)

/-- Along `buildQuantizedSpecPaperStop L p K` (with `8 ≤ p` and `K ≤ 2 ^ (L + 1)`), the leaf
log-size satisfies `K_leaf + 1 ≤ 4 * (Nat.log2 (leafPrecision L p K) + 1)`. -/
theorem specLeafK_paperStop_succ_le :
    ∀ (L p K : ℕ), 8 ≤ p → K ≤ 2 ^ (L + 1) →
      specLeafK (buildQuantizedSpecPaperStop L p K) + 1 ≤
        4 * (Nat.log2 (leafPrecision L p K) + 1) := by
  intro L
  induction L with
  | zero =>
    intro p K _ hK
    simp only [buildQuantizedSpecPaperStop, specLeafK, Nat.log2_two_pow]
    have : K ≤ 2 := by simpa using hK
    omega
  | succ L ih =>
    intro p K hp hK
    have hP' : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · simp only [specLeafK, Nat.log2_two_pow]
      have h1 := log_len_add_one_le_of_two_pow_le_four_mul_sq K p hstop
      have h2 : Nat.log2 p ≤ Nat.log2 (leafPrecision (L + 1) p K) :=
        nat_log2_mono (le_leafPrecision (L + 1) p K)
      omega
    · simp only [quantizedBoxGaussianStepSpec, specLeafK]
      rw [hP']
      exact ih (pChild p K) (K - K / 2) (by rw [pChild_eq_additive]; omega)
        (by
          have e : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
          omega)

/-- **Refined Leaf Log-Size Bound on `W8.hSpec n` (`hKLeaf_succ_le`):**
For all `n ≥ 2`,
`hKLeaf n + 1 ≤ 4 * (Nat.log2 (WP.W10b.P n) + 1) ≤ 4 * Nat.log2 (Nat.log2 n) + 37`. -/
theorem hKLeaf_succ_le {n : ℕ} (hn : 2 ≤ n) :
    hKLeaf n + 1 ≤ 4 * (Nat.log2 (WP.W10b.P n) + 1) ∧
      4 * (Nat.log2 (WP.W10b.P n) + 1) ≤ 4 * Nat.log2 (Nat.log2 n) + 37 := by
  have hpre := W7.headline_pre n
  have h1 := specLeafK_paperStop_succ_le (W8.hL n) (W8.hP0 n) (W8.hK0 n) hpre.1 hpre.2
  have h2 := WP.W10b.log2_P_le hn
  refine ⟨h1, ?_⟩
  unfold WP.W10b.P
  omega

/-- Explicit arithmetic envelope
`C * n * (Nat.sqrt (128 * Nat.log2 n) + 1) * (Nat.log2 (Nat.log2 n) + 2)` (not itself a machine
cost; it bounds machine-cost summands only through the domination theorems of this section). -/
def sqrtLogLogEnvelope (C n : ℕ) : ℕ :=
  C * n * (Nat.sqrt (128 * Nat.log2 n) + 1) * (Nat.log2 (Nat.log2 n) + 2)

/-- For `n ≥ 2`, `(sqrtLogLogEnvelope C n) ^ 15 ≤ ((2048 * C + 1) * n) ^ 15 * (Nat.log2 n) ^ 14`. -/
theorem sqrtLogLogEnvelope_pow15_le (C : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (sqrtLogLogEnvelope C n) ^ 15 ≤
      ((2048 * C + 1) * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  set b := Nat.log2 n
  have hb1 : 1 ≤ b := WP.W10b.one_le_log2 hn
  have hs1 : 1 ≤ Nat.sqrt (128 * b) := Nat.le_sqrt.2 (by omega)
  have hs2 : Nat.sqrt (128 * b) + 1 ≤ 2 * Nat.sqrt (128 * b) := by omega
  have hs_sq : (Nat.sqrt (128 * b) + 1) ^ 2 ≤ 512 * b := by
    calc (Nat.sqrt (128 * b) + 1) ^ 2
        ≤ (2 * Nat.sqrt (128 * b)) ^ 2 := Nat.pow_le_pow_left hs2 2
      _ = 4 * (Nat.sqrt (128 * b)) ^ 2 := by ring
      _ ≤ 4 * (128 * b) := Nat.mul_le_mul_left 4 (Nat.sqrt_le' (128 * b))
      _ = 512 * b := by ring
  have hs15 : (Nat.sqrt (128 * b) + 1) ^ 15 ≤ 512 ^ 15 * b ^ 8 := by
    calc (Nat.sqrt (128 * b) + 1) ^ 15
        ≤ (Nat.sqrt (128 * b) + 1) ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
      _ = ((Nat.sqrt (128 * b) + 1) ^ 2) ^ 8 := by rw [← pow_mul]
      _ ≤ (512 * b) ^ 8 := Nat.pow_le_pow_left hs_sq 8
      _ = 512 ^ 8 * b ^ 8 := by rw [mul_pow]
      _ ≤ 512 ^ 15 * b ^ 8 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by decide))
  have hlog15 : (Nat.log2 b + 2) ^ 15 ≤ 4 ^ 15 * b ^ 6 := by
    calc (Nat.log2 b + 2) ^ 15
        ≤ (Nat.log2 b + 3) ^ 15 := Nat.pow_le_pow_left (by omega) 15
      _ ≤ 4 ^ 15 * b ^ 5 := log2_add_three_pow15_le hb1
      _ ≤ 4 ^ 15 * b ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb1 (by decide))
  have hbase : 2048 * C ≤ 2048 * C + 1 := Nat.le_succ _
  calc (sqrtLogLogEnvelope C n) ^ 15
      = (C * n) ^ 15 * ((Nat.sqrt (128 * b) + 1) ^ 15 * (Nat.log2 b + 2) ^ 15) := by
          unfold sqrtLogLogEnvelope; ring
    _ ≤ (C * n) ^ 15 * ((512 ^ 15 * b ^ 8) * (4 ^ 15 * b ^ 6)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hs15 hlog15)
    _ = (2048 * C * n) ^ 15 * b ^ 14 := by ring
    _ ≤ ((2048 * C + 1) * n) ^ 15 * b ^ 14 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right n hbase) 15)

/-- Any function `f : ℕ → ℕ` bounded by `sqrtLogLogEnvelope C n` for `n ≥ 2` satisfies
`(f n) ^ 15 ≤ (A * n) ^ 15 * (Nat.log2 n) ^ 14` with `A = 2048 * C + 1 > 0`. -/
theorem subNLogN_pow15_of_sqrtLogLogEnvelope (f : ℕ → ℕ) (C : ℕ)
    (hf : ∀ n ≥ 2, f n ≤ sqrtLogLogEnvelope C n) :
    ∃ A > 0, ∀ n ≥ 2, (f n) ^ 15 ≤ (A * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  refine ⟨2048 * C + 1, by omega, fun n hn => ?_⟩
  exact le_trans (Nat.pow_le_pow_left (hf n hn) 15) (sqrtLogLogEnvelope_pow15_le C hn)

/-- The `leafLin` value at the leaf of a `QuantizedFastDFTSpec` schedule tree. -/
def specLeafLin (wd : ℕ → ℕ) : QuantizedFastDFTSpec → ℕ → ℕ → ℕ → ℕ
  | .base p R, p_in, ℓ, M => WP.W10b.leafLin wd p (Nat.log2 R) p_in ℓ M
  | .step p K t1 _ _ _ child, _p_in, ℓ, M =>
      specLeafLin wd child (2 * pChild p K) (ℓ + 1) (M * t1)

/-- The sum of `stepLin` across all step levels of a `QuantizedFastDFTSpec` schedule tree. -/
def specStepLinSum (wd : ℕ → ℕ) : QuantizedFastDFTSpec → ℕ → ℕ → ℕ → ℕ
  | .base _ _, _, _, _ => 0
  | .step p K t1 r _ _ child, p_in, ℓ, M =>
      WP.W10b.stepLin wd p K t1 r child.p p_in ℓ M +
        specStepLinSum wd child (2 * pChild p K) (ℓ + 1) (M * t1)

/-- The spread multiplication slots (one per step level) of a `QuantizedFastDFTSpec` schedule tree. -/
def specSpreadSlots (wd : ℕ → ℕ) : QuantizedFastDFTSpec → ℕ → ℕ → ℕ → List WP.W10b.Slot
  | .base _ _, _, _, _ => []
  | .step p K t1 r _ _ child, p_in, ℓ, M =>
      ⟨0, M * (2 * (WP.W10b.preHdrQ p K t1 r p_in).t1 * (WP.W10b.preHdrQ p K t1 r p_in).nb),
        ((WP.W10b.preHdrQ p K t1 r p_in).W + 1) * ((WP.W10b.preHdrQ p K t1 r p_in).s + wd ℓ)⟩ ::
      specSpreadSlots wd child (2 * pChild p K) (ℓ + 1) (M * t1)

/-- The non-spread multiplication slots (twist and column at each step level, plus the `K_leaf + 1`
radix-2 butterfly stages at the leaf) of a `QuantizedFastDFTSpec` schedule tree. -/
def specTwistColLeafSlots (wd : ℕ → ℕ) : QuantizedFastDFTSpec → ℕ → ℕ → ℕ → List WP.W10b.Slot
  | .base _ R, _, ℓ, M =>
      List.replicate (Nat.log2 R + 1) ⟨0, M * (4 * 2 ^ Nat.log2 R), wd ℓ⟩
  | .step p K t1 r _ _ child, p_in, ℓ, M =>
      ⟨0, M * (8 * (WP.W10b.preHdrQ p K t1 r p_in).N), wd ℓ⟩ ::
      ⟨0, M * (8 * ((WP.W10b.postHdrQ p K t1 r child.p).t1 * (WP.W10b.postHdrQ p K t1 r child.p).r)),
        8 * ((WP.W10b.postHdrQ p K t1 r child.p).H + 1)⟩ ::
      specTwistColLeafSlots wd child (2 * pChild p K) (ℓ + 1) (M * t1)

/-- Exact partition of `slotsCost Mul (specSlots wd spec p_in ℓ M)` into step-linear work,
leaf-linear work, spread multiplication slots, and twist/column/leaf multiplication slots. -/
theorem slotsCost_specSlots_eq (Mul : ℕ → ℕ) (wd : ℕ → ℕ) :
    ∀ (spec : QuantizedFastDFTSpec) (p_in ℓ M : ℕ),
      WP.W10b.slotsCost Mul (WP.W10b.specSlots wd spec p_in ℓ M) =
        specStepLinSum wd spec p_in ℓ M +
        specLeafLin wd spec p_in ℓ M +
        WP.W10b.slotsCost Mul (specSpreadSlots wd spec p_in ℓ M) +
        WP.W10b.slotsCost Mul (specTwistColLeafSlots wd spec p_in ℓ M)
  | .base p R, p_in, ℓ, M => by
    simp only [WP.W10b.specSlots, WP.W10b.slotsCost_cons, WP.W10b.Slot.cost,
      specStepLinSum, specLeafLin, specSpreadSlots, specTwistColLeafSlots,
      WP.W10b.slotsCost_nil]
    ring
  | .step p K t1 r h1 h2 child, p_in, ℓ, M => by
    have ih := slotsCost_specSlots_eq Mul wd child (2 * pChild p K) (ℓ + 1) (M * t1)
    simp only [WP.W10b.specSlots, WP.W10b.slotsCost_cons, WP.W10b.Slot.cost,
      specStepLinSum, specLeafLin, specSpreadSlots, specTwistColLeafSlots]
    rw [ih]
    ring

/-- Refined `specLeafLin` bound along `buildQuantizedSpecPaperStop L p K`: uses `specLeafK`
instead of the root `K`. -/
theorem specLeafLin_paperStop_le (wd : ℕ → ℕ) (S : ℕ) (hwd : ∀ j, wd j ≤ S) :
    ∀ (L p K p_in ℓ M : ℕ), 8 ≤ p → p_in ≤ S → K ≤ S → 2 * leafPrecision L p K ≤ S → 1 ≤ M →
      specLeafLin wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M ≤
        65536 * (M * 2 ^ K) * (S + 1) * (specLeafK (buildQuantizedSpecPaperStop L p K) + 1) := by
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M _ hpin hKS hPS hM
    have hpP := le_leafPrecision 0 p K
    simp only [buildQuantizedSpecPaperStop, specLeafLin, specLeafK, Nat.log2_two_pow]
    exact WP.W10b.leafLin_le wd p K p_in ℓ M S hwd hpin (by omega) hKS hM
  | succ L ih =>
    intro p K p_in ℓ M hp hpin hKS hPS hM
    have hP' : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    have hqP : pChild p K ≤ leafPrecision L (pChild p K) (K - K / 2) := le_leafPrecision _ _ _
    have hq : 2 * pChild p K ≤ S := by omega
    have hpq : p ≤ pChild p K := by rw [pChild_eq_additive]; omega
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · simp only [specLeafLin, specLeafK, Nat.log2_two_pow]
      exact WP.W10b.leafLin_le wd p K p_in ℓ M S hwd hpin (by omega) hKS hM
    · simp only [quantizedBoxGaussianStepSpec, specLeafLin, specLeafK]
      have ht1pos : 1 ≤ 2 ^ (K / 2) := Nat.one_le_two_pow
      have h2 := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
        (by omega) hq (by omega) (by rw [← hP']; exact hPS) (Nat.mul_le_mul hM ht1pos)
      obtain ⟨hmul, -, -, -⟩ := WP.W10b.step_dims K
      have e : M * 2 ^ (K / 2) * 2 ^ (K - K / 2) = M * 2 ^ K := by rw [Nat.mul_assoc, hmul]
      rw [e] at h2
      exact h2

/-- Constant for the headline `leafLin` bound. -/
def leafLinHeadlineConst (cw : ℕ) : ℕ :=
  65536 * 32 * 19 * (cw + 181)

/-- **Refined `leafLin` bound on `W8.hSpec n` (`specLeafLin_headline_le`):**
Along `W8.hSpec n`, for any input precision `p_in ≤ WP.W10b.Sb cw n` (e.g. `W8.hB n` and
`W8.hP0 n`, see `p_in_le_Sb_of_root`) and `n ≥ 2`, `specLeafLin` is bounded by
`sqrtLogLogEnvelope (leafLinHeadlineConst cw) n`; the 15th-power form
`(A * n) ^ 15 * (Nat.log2 n) ^ 14` follows with `sqrtLogLogEnvelope_pow15_le`. -/
theorem specLeafLin_headline_le (cw : ℕ) (wd : ℕ → ℕ → ℕ)
    (hwd : ∀ n ℓ, wd n ℓ ≤ cw * (Nat.log2 n + 1)) {n p_in : ℕ} (hn : 2 ≤ n)
    (hpin : p_in ≤ WP.W10b.Sb cw n) :
    specLeafLin (wd n) (W8.hSpec n) p_in 0 1 ≤
      sqrtLogLogEnvelope (leafLinHeadlineConst cw) n := by
  have hpre := W7.headline_pre n
  have hEl := WP.W10b.E_mul_le hn
  have hS := WP.W10b.Sb_succ_le cw n
  have hSP : 2 * leafPrecision (W8.hL n) (W8.hP0 n) (W8.hK0 n) ≤ WP.W10b.Sb cw n := by
    unfold WP.W10b.Sb WP.W10b.hP; omega
  have hKS : W8.hK0 n ≤ WP.W10b.Sb cw n := by unfold WP.W10b.Sb; omega
  have hwS : ∀ j, wd n j ≤ WP.W10b.Sb cw n := fun j =>
    le_trans (hwd n j) (by unfold WP.W10b.Sb; omega)
  have hlin := specLeafLin_paperStop_le (wd n) (WP.W10b.Sb cw n) hwS
    (W8.hL n) (W8.hP0 n) (W8.hK0 n) p_in 0 1 hpre.1 hpin hKS hSP le_rfl
  have hES : (1 * 2 ^ W8.hK0 n) * (WP.W10b.Sb cw n + 1) ≤ 32 * (cw + 181) * n := by
    calc (1 * 2 ^ W8.hK0 n) * (WP.W10b.Sb cw n + 1)
        = 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1) := by ring
      _ ≤ 2 ^ W8.hK0 n * ((cw + 181) * (Nat.log2 n + 1)) := Nat.mul_le_mul_left _ hS
      _ = (cw + 181) * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
      _ ≤ (cw + 181) * (32 * n) := Nat.mul_le_mul_left _ hEl
      _ = 32 * (cw + 181) * n := by ring
  have hKL_bound : hKLeaf n + 1 ≤ 19 * (Nat.log2 (Nat.log2 n) + 2) := by
    obtain ⟨hk1, hk2⟩ := hKLeaf_succ_le hn
    omega
  have hsqrt1 : 1 ≤ Nat.sqrt (128 * Nat.log2 n) + 1 := Nat.succ_pos _
  calc specLeafLin (wd n) (W8.hSpec n) p_in 0 1
      ≤ 65536 * ((1 * 2 ^ W8.hK0 n) * (WP.W10b.Sb cw n + 1)) * (hKLeaf n + 1) := by
          simpa [W8.hSpec, hKLeaf, Nat.mul_assoc] using hlin
    _ ≤ 65536 * (32 * (cw + 181) * n) * (19 * (Nat.log2 (Nat.log2 n) + 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 65536 hES) hKL_bound
    _ = leafLinHeadlineConst cw * n * 1 * (Nat.log2 (Nat.log2 n) + 2) := by
          unfold leafLinHeadlineConst; ring
    _ ≤ leafLinHeadlineConst cw * n * (Nat.sqrt (128 * Nat.log2 n) + 1) *
          (Nat.log2 (Nat.log2 n) + 2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsqrt1)
    _ = sqrtLogLogEnvelope (leafLinHeadlineConst cw) n := rfl

/-- Every slot in `specTwistColLeafSlots` along `buildQuantizedSpecPaperStop L p K` has zero
linear part, `cnt ≤ 8 * E`, `cnt * wid ≤ 192 * E * (S + 1)`, and linear width `wid ≤ 24 * (S + 1)`. -/
theorem specTwistColLeafSlots_ok (wd : ℕ → ℕ) (S : ℕ) (hwd : ∀ j, wd j ≤ S) :
    ∀ (L p K p_in ℓ M : ℕ), 8 ≤ p → 2 * leafPrecision L p K ≤ S →
      ∀ s ∈ specTwistColLeafSlots wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M,
        s.lin = 0 ∧ s.cnt ≤ 8 * (M * 2 ^ K) ∧
          s.cnt * s.wid ≤ 192 * (M * 2 ^ K) * (S + 1) ∧
          s.wid ≤ 24 * (S + 1) := by
  have hleaf : ∀ (p K p_in ℓ M : ℕ),
      ∀ s ∈ specTwistColLeafSlots wd (.base p (2 ^ K)) p_in ℓ M,
        s.lin = 0 ∧ s.cnt ≤ 8 * (M * 2 ^ K) ∧
          s.cnt * s.wid ≤ 192 * (M * 2 ^ K) * (S + 1) ∧
          s.wid ≤ 24 * (S + 1) := by
    intro p K p_in ℓ M s hs
    simp only [specTwistColLeafSlots, Nat.log2_two_pow, List.mem_replicate] at hs
    rcases hs with ⟨-, rfl⟩
    have hw := hwd ℓ
    obtain ⟨hc1, hc2, -⟩ := WP.W10b.leaf_slot_ok M K S (wd ℓ) hw
    exact ⟨rfl, hc1, hc2, by dsimp only; omega⟩
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M _ _
    exact hleaf p K p_in ℓ M
  | succ L ih =>
    intro p K p_in ℓ M hp hPS
    have hP' : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    have hqP : pChild p K ≤ leafPrecision L (pChild p K) (K - K / 2) := le_leafPrecision _ _ _
    have hq : 2 * pChild p K ≤ S := by omega
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · exact hleaf p K p_in ℓ M
    · intro s hs
      simp only [quantizedBoxGaussianStepSpec, specTwistColLeafSlots, List.mem_cons] at hs
      obtain ⟨hmul, -, -, -⟩ := WP.W10b.step_dims K
      rcases hs with rfl | rfl | hs
      · -- Twist slot
        have hw := hwd ℓ
        obtain ⟨ht1, ht2, -⟩ := WP.W10b.twist_slot_ok M K S (wd ℓ) hw
        exact ⟨rfl, ht1, ht2, by dsimp only; omega⟩
      · -- Column slot
        obtain ⟨hc1, hc2, -⟩ := WP.W10b.column_slot_ok M K S (pChild p K) hq
        have hb : 8 * (barrettH (2 * pChild p K) + 1) ≤ 24 * (S + 1) := by
          unfold barrettH; omega
        exact ⟨rfl, hc1, hc2, hb⟩
      · -- Child slots
        have hc := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
          (by rw [pChild_eq_additive]; omega) (by rw [← hP']; exact hPS) s hs
        have e : M * 2 ^ (K / 2) * 2 ^ (K - K / 2) = M * 2 ^ K := by rw [Nat.mul_assoc, hmul]
        rw [e] at hc
        exact hc

/-- Number of slots in `specTwistColLeafSlots` along `buildQuantizedSpecPaperStop L p K`:
at most `2 * L + (specLeafK (buildQuantizedSpecPaperStop L p K) + 1)`. -/
theorem specTwistColLeafSlots_length_le (wd : ℕ → ℕ) :
    ∀ (L p K p_in ℓ M : ℕ),
      (specTwistColLeafSlots wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M).length ≤
        2 * L + (specLeafK (buildQuantizedSpecPaperStop L p K) + 1) := by
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M
    simp [buildQuantizedSpecPaperStop, specTwistColLeafSlots, specLeafK]
  | succ L ih =>
    intro p K p_in ℓ M
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · simp [specTwistColLeafSlots, specLeafK]
    · simp only [quantizedBoxGaussianStepSpec, specTwistColLeafSlots, specLeafK, List.length_cons]
      have h := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
      omega

/-- Global Toom-3 `w * Nat.sqrt w` bound valid for all `w : ℕ`. -/
def T3SqrtConst (c0 c1 w0 : ℕ) : ℕ :=
  2808 * (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) + T3 c0 c1 w0 4

theorem T3_le_mul_sqrt_add (c0 c1 w0 w : ℕ) :
    T3 c0 c1 w0 w ≤ T3SqrtConst c0 c1 w0 * (w * Nat.sqrt w) + T3SqrtConst c0 c1 w0 := by
  rcases lt_or_ge w 4 with hw4 | hw4
  · have h1 : T3 c0 c1 w0 w ≤ T3 c0 c1 w0 4 := T3_mono c0 c1 w0 (by omega)
    have h2 : T3 c0 c1 w0 4 ≤ T3SqrtConst c0 c1 w0 := by unfold T3SqrtConst; omega
    omega
  · obtain ⟨j, hj1, hj2⟩ := WP.W5.exists_pow3 w (by omega)
    have hT : T3 c0 c1 w0 w ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1) :=
      le_trans (Nat.le_add_right _ _) (WP.W5.T3_grid c0 c1 w0 (j + 1) w (by omega))
    have hs1 : w < (Nat.sqrt w + 1) * (Nat.sqrt w + 1) := Nat.lt_succ_sqrt w
    have hs2 : 2 ≤ Nat.sqrt w := Nat.le_sqrt.2 (by omega)
    have h4s : 3 ^ j ≤ 4 * (Nat.sqrt w * Nat.sqrt w) := by nlinarith
    have h9 : 9 ^ j ≤ w * w := by
      calc 9 ^ j = 3 ^ j * 3 ^ j := by rw [show (9 : ℕ) = 3 * 3 by norm_num, mul_pow]
        _ ≤ w * w := Nat.mul_le_mul hj1 hj1
    have hws : 27 ^ j ≤ 4 * ((w * Nat.sqrt w) * (w * Nat.sqrt w)) := by
      calc 27 ^ j = 3 ^ j * 9 ^ j := by rw [show (27 : ℕ) = 3 * 9 by norm_num, mul_pow]
        _ ≤ (4 * (Nat.sqrt w * Nat.sqrt w)) * (w * w) := Nat.mul_le_mul h4s h9
        _ = 4 * ((w * Nat.sqrt w) * (w * Nat.sqrt w)) := by ring
    have hkey := WP.W5.pow25_le (j + 1)
    have hsq : 5 ^ (j + 1) * 5 ^ (j + 1) ≤
        (2808 * (w * Nat.sqrt w)) * (2808 * (w * Nat.sqrt w)) := by
      have hj1_pos : 1 ≤ (j + 1) * (j + 1) := by nlinarith
      have h25 : 25 ^ (j + 1) ≤ 25 ^ (j + 1) * ((j + 1) * (j + 1)) :=
        Nat.le_mul_of_pos_right _ hj1_pos
      have e1 : 5 ^ (j + 1) * 5 ^ (j + 1) = 25 ^ (j + 1) := by
        rw [show (25 : ℕ) = 5 * 5 by norm_num, mul_pow]
      have e2 : 27 ^ (j + 1) = 27 * 27 ^ j := by ring
      have e3 : (2808 * (w * Nat.sqrt w)) * (2808 * (w * Nat.sqrt w)) =
          7884864 * ((w * Nat.sqrt w) * (w * Nat.sqrt w)) := by ring
      rw [e1, e3]
      rw [e2] at hkey
      omega
    have hle : 5 ^ (j + 1) ≤ 2808 * (w * Nat.sqrt w) :=
      Nat.mul_self_le_mul_self_iff.1 hsq
    have hmain : T3 c0 c1 w0 w ≤ T3SqrtConst c0 c1 w0 * (w * Nat.sqrt w) := by
      calc T3 c0 c1 w0 w
          ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * 5 ^ (j + 1) := hT
        _ ≤ (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * (2808 * (w * Nat.sqrt w)) :=
            Nat.mul_le_mul_left _ hle
        _ = 2808 * (T3 c0 c1 w0 (2 * c0 + 3) + c1 * (2 * c0 + 5)) * (w * Nat.sqrt w) := by ring
        _ ≤ T3SqrtConst c0 c1 w0 * (w * Nat.sqrt w) :=
            Nat.mul_le_mul_right _ (by unfold T3SqrtConst; omega)
    omega

/-- Per-slot constant for linear-width (`wid ≤ 24 * (S + 1)`) multiplication slots. -/
def linearWidthSlotConst (c0 c1 w0 cw : ℕ) : ℕ :=
  T3SqrtConst c0 c1 w0 * (6144 * (cw + 181) ^ 2 + 256)

/-- Any multiplication slot with `cnt ≤ 8 * E`, `cnt * wid ≤ 192 * E * (S + 1)`, and
`wid ≤ 24 * (S + 1)` along `W8.hSpec n` costs at most
`linearWidthSlotConst c0 c1 w0 cw * n * (Nat.sqrt (128 * Nat.log2 n) + 1)`. -/
theorem linear_width_slot_cost_le (c0 c1 w0 cw : ℕ) {n cnt wid : ℕ} (hn : 2 ≤ n)
    (hcnt : cnt ≤ 8 * 2 ^ W8.hK0 n)
    (hcw : cnt * wid ≤ 192 * 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1))
    (hwid : wid ≤ 24 * (WP.W10b.Sb cw n + 1)) :
    cnt * T3 c0 c1 w0 wid ≤
      linearWidthSlotConst c0 c1 w0 cw * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
  set b := Nat.log2 n
  have hb1 : 1 ≤ b := WP.W10b.one_le_log2 hn
  have hS := WP.W10b.Sb_succ_le cw n
  have hEl := WP.W10b.E_mul_le hn
  have hES : 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1) ≤ 32 * (cw + 181) * n := by
    calc 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1)
        ≤ 2 ^ W8.hK0 n * ((cw + 181) * (b + 1)) := Nat.mul_le_mul_left _ hS
      _ = (cw + 181) * (2 ^ W8.hK0 n * (b + 1)) := by ring
      _ ≤ (cw + 181) * (32 * n) := Nat.mul_le_mul_left _ hEl
      _ = 32 * (cw + 181) * n := by ring
  have hcnt_n : cnt ≤ 256 * n := by
    have hE : 2 ^ W8.hK0 n ≤ 32 * n :=
      le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) hEl
    omega
  have hcw_n : cnt * wid ≤ 6144 * (cw + 181) * n := by
    calc cnt * wid ≤ 192 * (2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1)) := by linarith
      _ ≤ 192 * (32 * (cw + 181) * n) := Nat.mul_le_mul_left 192 hES
      _ = 6144 * (cw + 181) * n := by ring
  have hwid_sq : wid ≤ ((cw + 181) * (Nat.sqrt (128 * b) + 1)) ^ 2 := by
    have h1 : wid ≤ (cw + 181) * (128 * b) := by
      calc wid ≤ 24 * (WP.W10b.Sb cw n + 1) := hwid
        _ ≤ 24 * ((cw + 181) * (b + 1)) := Nat.mul_le_mul_left 24 hS
        _ ≤ 24 * ((cw + 181) * (2 * b)) :=
            Nat.mul_le_mul_left 24 (Nat.mul_le_mul_left _ (by omega))
        _ = 48 * (cw + 181) * b := by ring
        _ ≤ (cw + 181) * (128 * b) := by nlinarith
    have h2 : 128 * b ≤ (Nat.sqrt (128 * b) + 1) ^ 2 :=
      le_trans (Nat.le_succ _) (Nat.lt_succ_sqrt' (128 * b))
    have h3 : cw + 181 ≤ (cw + 181) ^ 2 := Nat.le_self_pow (by decide) _
    calc wid ≤ (cw + 181) * (128 * b) := h1
      _ ≤ (cw + 181) ^ 2 * (Nat.sqrt (128 * b) + 1) ^ 2 := Nat.mul_le_mul h3 h2
      _ = ((cw + 181) * (Nat.sqrt (128 * b) + 1)) ^ 2 := by ring
  have hsqrt_wid : Nat.sqrt wid ≤ (cw + 181) * (Nat.sqrt (128 * b) + 1) := by
    calc Nat.sqrt wid
        ≤ Nat.sqrt (((cw + 181) * (Nat.sqrt (128 * b) + 1)) ^ 2) := Nat.sqrt_le_sqrt hwid_sq
      _ = (cw + 181) * (Nat.sqrt (128 * b) + 1) := Nat.sqrt_eq' _
  have hT := T3_le_mul_sqrt_add c0 c1 w0 wid
  have h1 : cnt * (T3SqrtConst c0 c1 w0 * (wid * Nat.sqrt wid)) ≤
      T3SqrtConst c0 c1 w0 * (6144 * (cw + 181) ^ 2) * n * (Nat.sqrt (128 * b) + 1) := by
    calc cnt * (T3SqrtConst c0 c1 w0 * (wid * Nat.sqrt wid))
        = T3SqrtConst c0 c1 w0 * (cnt * wid) * Nat.sqrt wid := by ring
      _ ≤ T3SqrtConst c0 c1 w0 * (6144 * (cw + 181) * n) *
            ((cw + 181) * (Nat.sqrt (128 * b) + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hcw_n) hsqrt_wid
      _ = T3SqrtConst c0 c1 w0 * (6144 * (cw + 181) ^ 2) * n * (Nat.sqrt (128 * b) + 1) := by ring
  have h2 : cnt * T3SqrtConst c0 c1 w0 ≤
      T3SqrtConst c0 c1 w0 * 256 * n * (Nat.sqrt (128 * b) + 1) := by
    have hs1 : 1 ≤ Nat.sqrt (128 * b) + 1 := Nat.succ_pos _
    calc cnt * T3SqrtConst c0 c1 w0
        ≤ (256 * n) * T3SqrtConst c0 c1 w0 := Nat.mul_le_mul_right _ hcnt_n
      _ = (T3SqrtConst c0 c1 w0 * 256 * n) * 1 := by ring
      _ ≤ (T3SqrtConst c0 c1 w0 * 256 * n) * (Nat.sqrt (128 * b) + 1) :=
          Nat.mul_le_mul_left _ hs1
  calc cnt * T3 c0 c1 w0 wid
      ≤ cnt * (T3SqrtConst c0 c1 w0 * (wid * Nat.sqrt wid) + T3SqrtConst c0 c1 w0) :=
        Nat.mul_le_mul_left cnt hT
    _ = cnt * (T3SqrtConst c0 c1 w0 * (wid * Nat.sqrt wid)) + cnt * T3SqrtConst c0 c1 w0 := by
        ring
    _ ≤ T3SqrtConst c0 c1 w0 * (6144 * (cw + 181) ^ 2) * n * (Nat.sqrt (128 * b) + 1) +
          T3SqrtConst c0 c1 w0 * 256 * n * (Nat.sqrt (128 * b) + 1) :=
        Nat.add_le_add h1 h2
    _ = linearWidthSlotConst c0 c1 w0 cw * n * (Nat.sqrt (128 * b) + 1) := by
        unfold linearWidthSlotConst; ring

lemma sum_map_le_length_mul {α : Type*} (l : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ l, f x ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have ha := h a (by simp)
    have hl := ih (fun x hx => h x (by simp [hx]))
    omega

/-- Constant for the total `specTwistColLeafSlots` bound on `W8.hSpec n`. -/
def twistColLeafHeadlineConst (c0 c1 w0 cw : ℕ) : ℕ :=
  21 * linearWidthSlotConst c0 c1 w0 cw

/-- **Refined Leaf/Twist/Column Multiplication Slot Bound on `W8.hSpec n`
(`specTwistColLeafSlots_headline_le`):**
Along `W8.hSpec n`, the total cost of all leaf, twist, and column multiplication slots across
all levels is bounded by `sqrtLogLogEnvelope (twistColLeafHeadlineConst c0 c1 w0 cw) n`. -/
theorem specTwistColLeafSlots_headline_le (c0 c1 w0 cw : ℕ) (wd : ℕ → ℕ → ℕ)
    (hwd : ∀ n ℓ, wd n ℓ ≤ cw * (Nat.log2 n + 1)) {n : ℕ} (hn : 2 ≤ n) (p_in : ℕ) :
    WP.W10b.slotsCost (T3 c0 c1 w0) (specTwistColLeafSlots (wd n) (W8.hSpec n) p_in 0 1) ≤
      sqrtLogLogEnvelope (twistColLeafHeadlineConst c0 c1 w0 cw) n := by
  have hpre := W7.headline_pre n
  have hSP : 2 * leafPrecision (W8.hL n) (W8.hP0 n) (W8.hK0 n) ≤ WP.W10b.Sb cw n := by
    unfold WP.W10b.Sb WP.W10b.hP; omega
  have hwS : ∀ j, wd n j ≤ WP.W10b.Sb cw n := fun j =>
    le_trans (hwd n j) (by unfold WP.W10b.Sb; omega)
  have hok := specTwistColLeafSlots_ok (wd n) (WP.W10b.Sb cw n) hwS
    (W8.hL n) (W8.hP0 n) (W8.hK0 n) p_in 0 1 hpre.1 hSP
  have hslot : ∀ s ∈ specTwistColLeafSlots (wd n) (W8.hSpec n) p_in 0 1,
      WP.W10b.Slot.cost (T3 c0 c1 w0) s ≤
        linearWidthSlotConst c0 c1 w0 cw * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
    intro s hs
    obtain ⟨hlin, hcnt, hcw_s, hwid_s⟩ := hok s hs
    rw [WP.W10b.Slot.cost, hlin, Nat.zero_add]
    rw [Nat.one_mul] at hcnt hcw_s
    exact linear_width_slot_cost_le c0 c1 w0 cw hn hcnt hcw_s hwid_s
  have hsum := sum_map_le_length_mul
    (specTwistColLeafSlots (wd n) (W8.hSpec n) p_in 0 1)
    (WP.W10b.Slot.cost (T3 c0 c1 w0))
    (linearWidthSlotConst c0 c1 w0 cw * n * (Nat.sqrt (128 * Nat.log2 n) + 1))
    hslot
  have hlen : (specTwistColLeafSlots (wd n) (W8.hSpec n) p_in 0 1).length ≤
      21 * (Nat.log2 (Nat.log2 n) + 2) := by
    have hl1 := specTwistColLeafSlots_length_le (wd n) (W8.hL n) (W8.hP0 n) (W8.hK0 n) p_in 0 1
    change (specTwistColLeafSlots (wd n) (W8.hSpec n) p_in 0 1).length ≤
      2 * W8.hL n + (hKLeaf n + 1) at hl1
    have hl2 := WP.W10b.hL_le_loglog hn
    obtain ⟨hk1, hk2⟩ := hKLeaf_succ_le hn
    omega
  calc WP.W10b.slotsCost (T3 c0 c1 w0) (specTwistColLeafSlots (wd n) (W8.hSpec n) p_in 0 1)
      ≤ (specTwistColLeafSlots (wd n) (W8.hSpec n) p_in 0 1).length *
          (linearWidthSlotConst c0 c1 w0 cw * n * (Nat.sqrt (128 * Nat.log2 n) + 1)) := hsum
    _ ≤ (21 * (Nat.log2 (Nat.log2 n) + 2)) *
          (linearWidthSlotConst c0 c1 w0 cw * n * (Nat.sqrt (128 * Nat.log2 n) + 1)) :=
        Nat.mul_le_mul_right _ hlen
    _ = sqrtLogLogEnvelope (twistColLeafHeadlineConst c0 c1 w0 cw) n := by
        unfold sqrtLogLogEnvelope twistColLeafHeadlineConst; ring

/-- **Combined Sub-`n log n` Exponent-`14/15` Theorem for `leafLin` and Leaf/Twist/Column Slots
(`leaf_and_twistColLeaf_pow15_le`):**
Along `W8.hSpec n`, both `specLeafLin` and `slotsCost (TMFw.Contracts.T3 c0 c1 w0) (specTwistColLeafSlots ...)`
(as well as their sum) are bounded by
`C * n * (Nat.sqrt (128 * Nat.log2 n) + 1) * (Nat.log2 (Nat.log2 n) + 2)` and satisfy
`(f n) ^ 15 ≤ (A * n) ^ 15 * (Nat.log2 n) ^ 14` for all `n ≥ 2`. -/
theorem leaf_and_twistColLeaf_pow15_le (c0 c1 w0 cw : ℕ) (wd : ℕ → ℕ → ℕ)
    (hwd : ∀ n ℓ, wd n ℓ ≤ cw * (Nat.log2 n + 1)) (p_in : ℕ → ℕ)
    (hpin : ∀ n ≥ 2, p_in n ≤ WP.W10b.Sb cw n) :
    ∃ C A : ℕ, 0 < C ∧ 0 < A ∧
      (∀ n ≥ 2,
        specLeafLin (wd n) (W8.hSpec n) (p_in n) 0 1 +
          WP.W10b.slotsCost (T3 c0 c1 w0)
            (specTwistColLeafSlots (wd n) (W8.hSpec n) (p_in n) 0 1) ≤
          C * n * (Nat.sqrt (128 * Nat.log2 n) + 1) * (Nat.log2 (Nat.log2 n) + 2)) ∧
      (∀ n ≥ 2,
        (specLeafLin (wd n) (W8.hSpec n) (p_in n) 0 1 +
          WP.W10b.slotsCost (T3 c0 c1 w0)
            (specTwistColLeafSlots (wd n) (W8.hSpec n) (p_in n) 0 1)) ^ 15 ≤
          (A * n) ^ 15 * (Nat.log2 n) ^ 14) := by
  set C := leafLinHeadlineConst cw + twistColLeafHeadlineConst c0 c1 w0 cw + 1
  have hC : 0 < C := by omega
  have hbound : ∀ n ≥ 2,
      specLeafLin (wd n) (W8.hSpec n) (p_in n) 0 1 +
        WP.W10b.slotsCost (T3 c0 c1 w0)
          (specTwistColLeafSlots (wd n) (W8.hSpec n) (p_in n) 0 1) ≤
        sqrtLogLogEnvelope C n := by
    intro n hn
    have h1 := specLeafLin_headline_le cw wd hwd hn (hpin n hn)
    have h2 := specTwistColLeafSlots_headline_le c0 c1 w0 cw wd hwd hn (p_in n)
    calc specLeafLin (wd n) (W8.hSpec n) (p_in n) 0 1 +
          WP.W10b.slotsCost (T3 c0 c1 w0)
            (specTwistColLeafSlots (wd n) (W8.hSpec n) (p_in n) 0 1)
        ≤ sqrtLogLogEnvelope (leafLinHeadlineConst cw) n +
            sqrtLogLogEnvelope (twistColLeafHeadlineConst c0 c1 w0 cw) n :=
          Nat.add_le_add h1 h2
      _ = (leafLinHeadlineConst cw + twistColLeafHeadlineConst c0 c1 w0 cw) *
            (n * (Nat.sqrt (128 * Nat.log2 n) + 1) * (Nat.log2 (Nat.log2 n) + 2)) := by
          unfold sqrtLogLogEnvelope; ring
      _ ≤ C * (n * (Nat.sqrt (128 * Nat.log2 n) + 1) * (Nat.log2 (Nat.log2 n) + 2)) :=
          Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = sqrtLogLogEnvelope C n := by unfold sqrtLogLogEnvelope; ring
  obtain ⟨A, hA, hpow⟩ := subNLogN_pow15_of_sqrtLogLogEnvelope _ C hbound
  exact ⟨C, A, hC, hA, hbound, hpow⟩

/-- Every slot in `specSpreadSlots` along `buildQuantizedSpecPaperStop L p K` satisfies
`WP.W10b.spread_slot_ok`'s bounds. -/
theorem specSpreadSlots_ok (wd : ℕ → ℕ) (S : ℕ) (hwd : ∀ j, wd j ≤ S) :
    ∀ (L p K p_in ℓ M : ℕ), 8 ≤ p → 2 * leafPrecision L p K ≤ S →
      ∀ s ∈ specSpreadSlots wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M,
        s.lin = 0 ∧ s.cnt ≤ 8 * (M * 2 ^ K) ∧
          s.cnt * s.wid ≤ 192 * (M * 2 ^ K) * (S + 1) ∧
          s.wid ≤ 24 * (S + 1) ^ 2 := by
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M _ _ s hs
    simp [buildQuantizedSpecPaperStop, specSpreadSlots] at hs
  | succ L ih =>
    intro p K p_in ℓ M hp hPS
    have hP' : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    have hqP : pChild p K ≤ leafPrecision L (pChild p K) (K - K / 2) := le_leafPrecision _ _ _
    have hq : 2 * pChild p K ≤ S := by omega
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · intro s hs
      simp [specSpreadSlots] at hs
    · intro s hs
      simp only [quantizedBoxGaussianStepSpec, specSpreadSlots, List.mem_cons] at hs
      rcases hs with rfl | hs
      · obtain ⟨hs1, hs2, hs3⟩ := WP.W10b.spread_slot_ok M K S (wd ℓ) (pChild p K) (hwd ℓ) hq
        exact ⟨rfl, hs1, hs2, hs3⟩
      · have hc := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
          (by rw [pChild_eq_additive]; omega) (by rw [← hP']; exact hPS) s hs
        obtain ⟨hmul, -, -, -⟩ := WP.W10b.step_dims K
        have e : M * 2 ^ (K / 2) * 2 ^ (K - K / 2) = M * 2 ^ K := by rw [Nat.mul_assoc, hmul]
        rw [e] at hc
        exact hc

/-- Number of spread slots along `buildQuantizedSpecPaperStop L p K`: at most `L`. -/
theorem specSpreadSlots_length_le (wd : ℕ → ℕ) :
    ∀ (L p K p_in ℓ M : ℕ),
      (specSpreadSlots wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M).length ≤ L := by
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M
    simp [buildQuantizedSpecPaperStop, specSpreadSlots]
  | succ L ih =>
    intro p K p_in ℓ M
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · simp [specSpreadSlots]
    · simp only [quantizedBoxGaussianStepSpec, specSpreadSlots, List.length_cons]
      have h := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
      omega

lemma exists_max_mem_or_default {α : Type*} (f : α → ℕ) (d : α) :
    ∀ l : List α, ∃ m : α, (m = d ∨ m ∈ l) ∧ (l.map f).sum ≤ l.length * f m
  | [] => ⟨d, Or.inl rfl, by simp⟩
  | a :: l => by
    obtain ⟨m, hm, hsum⟩ := exists_max_mem_or_default f d l
    rcases le_total (f a) (f m) with ham | hma
    · refine ⟨m, ?_, ?_⟩
      · rcases hm with rfl | hml
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem a hml)
      · simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
    · refine ⟨a, Or.inr List.mem_cons_self, ?_⟩
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hlm : l.length * f m ≤ l.length * f a := Nat.mul_le_mul_left _ hma
      omega

/-- **Total Spread-Slot Sub-`n log n` Bound on `W8.hSpec n`
(`specSpreadSlots_headline_pow15_le`):**
Along `W8.hSpec n`, the 15th power of the total cost of all spread multiplication slots across
all levels is bounded by `(spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14` for all `n ≥ 2`. -/
theorem specSpreadSlots_headline_pow15_le (c0 c1 w0 cw : ℕ) (wd : ℕ → ℕ → ℕ)
    (hwd : ∀ n ℓ, wd n ℓ ≤ cw * (Nat.log2 n + 1)) {n : ℕ} (hn : 2 ≤ n) (p_in : ℕ) :
    (WP.W10b.slotsCost (T3 c0 c1 w0) (specSpreadSlots (wd n) (W8.hSpec n) p_in 0 1)) ^ 15 ≤
      (spreadSlotConst c0 c1 w0 cw * n) ^ 15 * (Nat.log2 n) ^ 14 := by
  set l := specSpreadSlots (wd n) (W8.hSpec n) p_in 0 1
  obtain ⟨m, hm, hsum⟩ :=
    exists_max_mem_or_default (WP.W10b.Slot.cost (T3 c0 c1 w0)) WP.W10b.zeroSlot l
  have hlen : l.length ≤ W8.hL n + 1 := by
    have hl := specSpreadSlots_length_le (wd n) (W8.hL n) (W8.hP0 n) (W8.hK0 n) p_in 0 1
    change l.length ≤ W8.hL n at hl
    omega
  have hm_ok : m.lin = 0 ∧ m.cnt ≤ 8 * 2 ^ W8.hK0 n ∧
      m.cnt * m.wid ≤ 192 * 2 ^ W8.hK0 n * (WP.W10b.Sb cw n + 1) ∧
      m.wid ≤ 24 * (WP.W10b.Sb cw n + 1) ^ 2 := by
    rcases hm with rfl | hml
    · simp [WP.W10b.zeroSlot]
    · have hpre := W7.headline_pre n
      have hSP : 2 * leafPrecision (W8.hL n) (W8.hP0 n) (W8.hK0 n) ≤ WP.W10b.Sb cw n := by
        unfold WP.W10b.Sb WP.W10b.hP; omega
      have hwS : ∀ j, wd n j ≤ WP.W10b.Sb cw n := fun j =>
        le_trans (hwd n j) (by unfold WP.W10b.Sb; omega)
      obtain ⟨hlin, hcnt, hcw_m, hwid_m⟩ := specSpreadSlots_ok (wd n) (WP.W10b.Sb cw n) hwS
        (W8.hL n) (W8.hP0 n) (W8.hK0 n) p_in 0 1 hpre.1 hSP m hml
      rw [Nat.one_mul] at hcnt hcw_m
      exact ⟨hlin, hcnt, hcw_m, hwid_m⟩
  obtain ⟨hlin, hcnt, hcw_m, hwid_m⟩ := hm_ok
  have hcost_le : WP.W10b.slotsCost (T3 c0 c1 w0) l ≤
      (W8.hL n + 1) * (m.cnt * T3 c0 c1 w0 m.wid) := by
    calc WP.W10b.slotsCost (T3 c0 c1 w0) l
        ≤ l.length * WP.W10b.Slot.cost (T3 c0 c1 w0) m := hsum
      _ ≤ (W8.hL n + 1) * WP.W10b.Slot.cost (T3 c0 c1 w0) m := Nat.mul_le_mul_right _ hlen
      _ = (W8.hL n + 1) * (m.cnt * T3 c0 c1 w0 m.wid) := by
          rw [WP.W10b.Slot.cost, hlin, Nat.zero_add]
  exact le_trans (Nat.pow_le_pow_left hcost_le 15)
    (spread_slot_pow15_le_explicit c0 c1 w0 cw hn hcnt hcw_m hwid_m)

end SubNLogN.S5.Pipe
