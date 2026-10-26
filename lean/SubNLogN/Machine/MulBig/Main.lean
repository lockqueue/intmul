/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.MulBig.Prog
import SubNLogN.Machine.MulBig.Instances
import WP.Top.Main
import WP.Top.CostShape
import WP.W7pure.TableCost
import WP.W7pure.TapeBound
import WP.W5.Bound
import WP.W11b.Final
import WP.W10.Cost

/-!
# `mulBig` (K0.4): the contract holds — `mulBig_holds : MulBigContract` (Section 8 (`sec:lean`), Table 7 (`tab:lean-map`))

**The program.** `mulBigProg` (`SubNLogN/Machine/MulBig/Prog.lean`) with the proved stage programs:
the W3 adder and W6a divider (inside W0m's parameter phases), the W7 table builder
(`w7_buildTables_proved`), the tape converter (`WP.Top.TapeConv_proved`) and the `[MS]` multiplier
`W9_multiply` at `T3 c0 c1 w0` (`w9_multiply_proved`; Toom-3 is the multiplication used *inside* the
transform for its small products, matching `IntMulTM.intMul_TM2_nlogn`).

**The cost.** One run costs `mbCost … x y cSpec` (the sum of the stage costs). With
`n = operandBits x y ≤ N = mulBigSize x y`:
* `copyIn_param_le`: copy-in plus the parameter phases cost `≤ Klin·n` (always);
* `mbCost_le_of_large`: above the threshold of W7's `√n` bounds and of W9's cost shape, the
  remaining stages are bounded by W10's stage-cost total `(topCosts 0 …).total`: tables,
  conversion, glue and W9's tape term by `tabsN` (`aux_le`), copy-out and cleanup by `outN`
  (`out_le`), W9's transform work by the pipeline fields (`W9CostShape_of_W10b`);
* W10 (`W10_cost_holds`) bounds that total by `C10·n·log₂ n` eventually;
* `lin_nlog_le` turns `A·n + B·n·log₂ n` into `(A + B)·mulBigBound x y`;
* below the threshold there are finitely many operand pairs; their cost is absorbed into the
  constant through `WP.Top.supCost`.

**The overhead.** `mbOverhead_le`: wherever W7's `√n` bounds hold at `n ≥ 2` (in particular for
all `n` above W7's thresholds), everything except W9's transform work
`C9·(rootBound + pipeBound + pipeBound)` costs `≤ ohConst·mulBigSize x y` (linear call overhead).

**Non-vacuity.** `mulBig_nonvacuous`: the packaged program has, for every `x y`, an actual
evaluation from `X = natSyms x`, `Y = natSyms y`, `Z = []`, empty scratch, to `Z = natSyms (x * y)`
within the bound.
-/

namespace SubNLogN.Machine.MulBig

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-! ## Arithmetic -/

/-- `operandBits x y ≤ mulBigSize x y`. -/
theorem operandBits_le_mulBigSize (x y : ℕ) : operandBits x y ≤ mulBigSize x y := by
  rw [WP.W0m.operandBits_eq]
  unfold mulBigSize
  exact max_le (by omega) (max_le (by omega) (by omega))

/-- **Copy-in and the parameter phases are linear** in `n = operandBits x y`. -/
theorem copyIn_param_le (Ca Cd x y : ℕ) :
    (7 * bitLen x + 7) + (7 * bitLen y + 7) + WP.W0m.workCost Ca Cd x y ≤
      (200000 + 576 * Cd + 2306 * Ca) * operandBits x y := by
  have hn1 : 1 ≤ operandBits x y := WP.W0m.operandBits_pos x y
  have hx : bitLen x ≤ operandBits x y := by
    rw [WP.W0m.operandBits_eq]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hy : bitLen y ≤ operandBits x y := by
    rw [WP.W0m.operandBits_eq]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hin : WP.W0m.inLen x y ≤ 2 * operandBits x y + 1 := by
    unfold WP.W0m.inLen
    omega
  have hsq := WP.Top.sq_bitLen_le (18 * (WP.W0m.inLen x y + 1)) (by omega)
  have hlam : WP.W0m.lam x y = bitLen (18 * (WP.W0m.inLen x y + 1)) := rfl
  rw [← hlam] at hsq
  have hsq' : (WP.W0m.lam x y + 1) * (WP.W0m.lam x y + 1) ≤ 576 * operandBits x y := by omega
  have hL1 : WP.W0m.lam x y + 1 ≤ (WP.W0m.lam x y + 1) * (WP.W0m.lam x y + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h1 : Cd * ((WP.W0m.lam x y + 1) * (WP.W0m.lam x y + 1)) ≤ 576 * (Cd * operandBits x y) :=
    calc Cd * ((WP.W0m.lam x y + 1) * (WP.W0m.lam x y + 1)) ≤ Cd * (576 * operandBits x y) :=
          Nat.mul_le_mul_left _ hsq'
      _ = 576 * (Cd * operandBits x y) := by ring
  have h2 : Ca * (4 * WP.W0m.lam x y + 2) ≤ 2306 * (Ca * operandBits x y) :=
    calc Ca * (4 * WP.W0m.lam x y + 2) ≤ Ca * (2306 * operandBits x y) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2306 * (Ca * operandBits x y) := by ring
  have e : (200000 + 576 * Cd + 2306 * Ca) * operandBits x y =
      200000 * operandBits x y + 576 * (Cd * operandBits x y) + 2306 * (Ca * operandBits x y) := by
    ring
  rw [e]
  unfold WP.W0m.workCost
  omega

/-- Copy-out and cleanup are within the output stage's bound `WP.Top.outCost`. -/
theorem cleanup_le (ℓ J : ℕ) : (7 * ℓ + 7) + (2 * J + 2 * 76 + 1) ≤ WP.Top.outCost ℓ J := by
  unfold WP.Top.outCost
  rw [WP.Top.length_allGW]
  omega

/-- W9's cost: transform work plus the tape term. -/
theorem w9Cost_eq (C9 : ℕ) (Mul : ℕ → ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (n : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    WP.Top.w9Cost C9 Mul wdF wdI wR n cSpec =
      C9 * (rootBound Mul (wR n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
        pipeBound Mul (wdF n) cSpec (W8.hB n) 0 1 +
        pipeBound Mul (wdI n) cSpec (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) 0 1) +
      C9 * ((tapeSyms cSpec).length + 1) := by
  unfold WP.Top.w9Cost
  ring

/-- `A·n + B·n·log₂ n ≤ (A + B)·mulBigBound x y` for `n = operandBits x y`. -/
theorem lin_nlog_le (x y A B : ℕ) :
    A * operandBits x y + B * operandBits x y * Nat.log2 (operandBits x y) ≤
      (A + B) * mulBigBound x y := by
  have h1 := operandBits_le_mulBigSize x y
  have h2 := WP.Top.nlogn_mono h1
  have h3 : mulBigSize x y * Nat.log2 (mulBigSize x y) ≤
      mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ _)
  have h4 : mulBigSize x y ≤ mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h5 : A * operandBits x y ≤ A * (mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1)) :=
    Nat.mul_le_mul_left _ (le_trans h1 h4)
  have h6 : B * operandBits x y * Nat.log2 (operandBits x y) ≤
      B * (mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_trans h2 h3)
  calc A * operandBits x y + B * operandBits x y * Nat.log2 (operandBits x y)
      ≤ A * (mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1)) +
          B * (mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1)) := Nat.add_le_add h5 h6
    _ = (A + B) * (mulBigSize x y * (Nat.log2 (mulBigSize x y) + 1)) := by ring
    _ ≤ (A + B) * mulBigBound x y := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- `sqP n = (√n + 1)(log₂ n + 1)^8 ≤ 2^41·n` for `n ≥ 2` (the proof of
`SubNLogN.S5.sqP_le_linear`, restated here). -/
theorem sqP_le_lin (n : ℕ) (hn : 2 ≤ n) : WP.Top.sqP n ≤ 2 ^ 41 * n := by
  have hn0 : n ≠ 0 := by omega
  have h1 : Nat.log2 n + 1 < 2 ^ (Nat.log2 n / 16 + 5) := by
    have hq : Nat.log2 n / 16 < 2 ^ (Nat.log2 n / 16) := Nat.lt_two_pow_self
    have e : 2 ^ (Nat.log2 n / 16 + 5) = 32 * 2 ^ (Nat.log2 n / 16) := by rw [pow_add]; ring
    rw [e]; omega
  have h2 : (Nat.log2 n + 1) ^ 8 ≤ 2 ^ (Nat.log2 n / 2 + 40) := by
    have h := Nat.pow_lt_pow_left h1 (by omega : (8 : ℕ) ≠ 0)
    rw [← pow_mul] at h
    exact le_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
  have h3 : 2 ^ (Nat.log2 n / 2) ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]
    calc 2 ^ (Nat.log2 n / 2) * 2 ^ (Nat.log2 n / 2) = 2 ^ (Nat.log2 n / 2 + Nat.log2 n / 2) :=
          (pow_add _ _ _).symm
      _ ≤ 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := Nat.log2_self_le hn0
  have hs1 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hs2 : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have e40 : 2 ^ (Nat.log2 n / 2 + 40) = 2 ^ 40 * 2 ^ (Nat.log2 n / 2) := by rw [pow_add]; ring
  have h4 : (Nat.log2 n + 1) ^ 8 ≤ 2 ^ 40 * Nat.sqrt n :=
    h2.trans (by rw [e40]; exact Nat.mul_le_mul_left _ h3)
  unfold WP.Top.sqP
  calc (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8
      ≤ (Nat.sqrt n + 1) * (2 ^ 40 * Nat.sqrt n) := Nat.mul_le_mul_left _ h4
    _ = 2 ^ 40 * (Nat.sqrt n * Nat.sqrt n + Nat.sqrt n) := by ring
    _ ≤ 2 ^ 40 * (n + n) := Nat.mul_le_mul_left _ (Nat.add_le_add hs1 hs2)
    _ = 2 ^ 41 * n := by ring

/-- `α·sqP n + β·n + γ ≤ (α·2^41 + β + γ)·n` for `n ≥ 2`. -/
theorem poly_le_lin (α β γ n : ℕ) (hn : 2 ≤ n) :
    α * WP.Top.sqP n + β * n + γ ≤ (α * 2 ^ 41 + β + γ) * n := by
  have h1 : α * WP.Top.sqP n ≤ α * (2 ^ 41 * n) := Nat.mul_le_mul_left α (sqP_le_lin n hn)
  have h3 : γ ≤ γ * n := Nat.le_mul_of_pos_right γ (by omega)
  calc α * WP.Top.sqP n + β * n + γ
      ≤ α * (2 ^ 41 * n) + β * n + γ * n := Nat.add_le_add (Nat.add_le_add h1 le_rfl) h3
    _ = (α * 2 ^ 41 + β + γ) * n := by ring

/-! ## The cost of one run above the threshold -/

/-- **One run, above the threshold.** Given W7's `√n` bounds at `n = operandBits x y` (`hP`,
`hT7`), TapeConv's size clause (`hTS`) and W9's cost shape (`h9`), and `n` above the guard `N0` of
`WP.Top.topCosts`, the run costs at most `Klin·n` plus W10's stage-cost total at `n` (with no input
stage: `C0 = 0`). -/
theorem mbCost_le_of_large {Ca Cd C7 Cc C9 Cp Ct N0 : ℕ} {Mul M' : ℕ → ℕ}
    {wdF wdI : ℕ → ℕ → ℕ} {wR : ℕ → ℕ} {pc : WP.Top.PipeCosts} (x y : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (hN : N0 ≤ operandBits x y)
    (hP : (W8.hSpec (operandBits x y)).precomputeSeriesTableCost ≤
      Cp * WP.Top.sqP (operandBits x y))
    (hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length ≤
      Ct * WP.Top.sqP (operandBits x y))
    (hTS : (tapeSyms cSpec).length ≤
      Cc * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1))
    (h9 : C9 * (rootBound Mul (wR (operandBits x y)) (W8.hB (operandBits x y))
        (W8.hK0 (operandBits x y)) (W8.hK (operandBits x y)) (W8.hK (operandBits x y)) +
      pipeBound Mul (wdF (operandBits x y)) cSpec (W8.hB (operandBits x y)) 0 1 +
      pipeBound Mul (wdI (operandBits x y)) cSpec
        (IntMul.rootPrecision (W8.hB (operandBits x y)) (W8.hK0 (operandBits x y))) 0 1) ≤
      pc.cost M' (operandBits x y)) :
    mbCost Ca Cd C7 Cc C9 Mul wdF wdI wR x y cSpec ≤
      (200000 + 576 * Cd + 2306 * Ca) * operandBits x y +
        (WP.Top.topCosts 0 C7 Cp Ct Cc C9 N0 pc).total M' (operandBits x y) := by
  have hn1 : 1 ≤ operandBits x y := WP.W0m.operandBits_pos x y
  have hA := copyIn_param_le Ca Cd x y
  have hB := WP.Top.aux_le C7 Cp Ct Cc C9 (operandBits x y) hn1 cSpec hP hT7 hTS
  have hC := WP.Top.out_le Cc Ct x y cSpec hT7 hTS
  have hD := cleanup_le (bitLen (x * y))
    (WP.Top.totalSize (WP.Top.w9Out (operandBits x y) x y cSpec (x * y)))
  have hW := w9Cost_eq C9 Mul wdF wdI wR (operandBits x y) cSpec
  have h0 : WP.Top.inCostN 0 (operandBits x y) = 0 := by simp [WP.Top.inCostN]
  rw [WP.Top.topCosts_total, h0]
  unfold WP.Top.tabsN WP.Top.outN mbCost
  rw [if_pos hN, if_pos hN, hW]
  omega

/-! ## The linear call overhead -/

/-- The part of one run's cost outside W9's transform work: copy-in, parameters, tables, tape
conversion, glue, W9's tape term `C9·(|tapeSyms| + 1)`, copy-out and cleanup. -/
def mbOverhead (Ca Cd C7 Cc C9 x y : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  (7 * bitLen x + 7) + (7 * bitLen y + 7) + WP.W0m.workCost Ca Cd x y +
    (WP.Top.tabCost C7 (operandBits x y) cSpec + (WP.Top.convCost Cc cSpec +
      (WP.Top.glueCost (operandBits x y) + C9 * ((tapeSyms cSpec).length + 1)))) +
    ((7 * bitLen (x * y) + 7) +
      (2 * WP.Top.totalSize (WP.Top.w9Out (operandBits x y) x y cSpec (x * y)) + 2 * 76 + 1))

/-- One run = overhead + W9's transform work. -/
theorem mbCost_eq_overhead (Ca Cd C7 Cc C9 : ℕ) (Mul : ℕ → ℕ) (wdF wdI : ℕ → ℕ → ℕ)
    (wR : ℕ → ℕ) (x y : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    mbCost Ca Cd C7 Cc C9 Mul wdF wdI wR x y cSpec =
      mbOverhead Ca Cd C7 Cc C9 x y cSpec +
        C9 * (rootBound Mul (wR (operandBits x y)) (W8.hB (operandBits x y))
            (W8.hK0 (operandBits x y)) (W8.hK (operandBits x y)) (W8.hK (operandBits x y)) +
          pipeBound Mul (wdF (operandBits x y)) cSpec (W8.hB (operandBits x y)) 0 1 +
          pipeBound Mul (wdI (operandBits x y)) cSpec
            (IntMul.rootPrecision (W8.hB (operandBits x y)) (W8.hK0 (operandBits x y))) 0 1) := by
  unfold mbCost mbOverhead
  rw [w9Cost_eq]
  ring

/-- The constant of the linear overhead bound. -/
def ohConst (Ca Cd C7 Cp Ct Cc C9 : ℕ) : ℕ :=
  (200000 + 576 * Cd + 2306 * Ca) +
    (WP.Top.auxα C7 Cp Ct Cc C9 * 2 ^ 41 + WP.Top.auxβ C7 + WP.Top.auxγ C7 Cc C9) +
    (152 * (Cc * Ct) * 2 ^ 41 + 3064 + (152 * Cc + 6708))

/-- **The call overhead is linear in `N = mulBigSize x y`**: wherever W7's `√n` bounds hold at
`n = operandBits x y ≥ 2` (`hP`, `hT7`; they hold for all `n` above W7's threshold) and with
TapeConv's size clause `hTS`, everything except W9's transform work costs `≤ K·N` with
`K = ohConst …`. -/
theorem mbOverhead_le {Ca Cd C7 Cc C9 Cp Ct : ℕ} (x y : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (hn2 : 2 ≤ operandBits x y)
    (hP : (W8.hSpec (operandBits x y)).precomputeSeriesTableCost ≤
      Cp * WP.Top.sqP (operandBits x y))
    (hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length ≤
      Ct * WP.Top.sqP (operandBits x y))
    (hTS : (tapeSyms cSpec).length ≤
      Cc * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1)) :
    mbOverhead Ca Cd C7 Cc C9 x y cSpec ≤ ohConst Ca Cd C7 Cp Ct Cc C9 * mulBigSize x y := by
  have hn1 : 1 ≤ operandBits x y := by omega
  have hA := copyIn_param_le Ca Cd x y
  have hB := WP.Top.aux_le C7 Cp Ct Cc C9 (operandBits x y) hn1 cSpec hP hT7 hTS
  have hC := WP.Top.out_le Cc Ct x y cSpec hT7 hTS
  have hD := cleanup_le (bitLen (x * y))
    (WP.Top.totalSize (WP.Top.w9Out (operandBits x y) x y cSpec (x * y)))
  have hB' := poly_le_lin (WP.Top.auxα C7 Cp Ct Cc C9) (WP.Top.auxβ C7) (WP.Top.auxγ C7 Cc C9)
    (operandBits x y) hn2
  have hC' := poly_le_lin (152 * (Cc * Ct)) 3064 (152 * Cc + 6708) (operandBits x y) hn2
  have hK : ohConst Ca Cd C7 Cp Ct Cc C9 * operandBits x y ≤
      ohConst Ca Cd C7 Cp Ct Cc C9 * mulBigSize x y :=
    Nat.mul_le_mul_left _ (operandBits_le_mulBigSize x y)
  have e : ohConst Ca Cd C7 Cp Ct Cc C9 * operandBits x y =
      (200000 + 576 * Cd + 2306 * Ca) * operandBits x y +
        (WP.Top.auxα C7 Cp Ct Cc C9 * 2 ^ 41 + WP.Top.auxβ C7 + WP.Top.auxγ C7 Cc C9) *
          operandBits x y +
        (152 * (Cc * Ct) * 2 ^ 41 + 3064 + (152 * Cc + 6708)) * operandBits x y := by
    unfold ohConst
    ring
  unfold mbOverhead
  omega

/-! ## The contract -/

/-- **`mulBig` holds**: the IntMul pipeline, packaged on `MBLoc = Fin 3 ⊕ GW`, is a closed program
with finite nonempty registers that multiplies `X·Y` onto `Z` (operands restored, scratch empty
again) within `C·(N·(log₂ N + 1) + 1)` steps, `N = bitLen x + bitLen y + 1`, for one constant `C`. -/
theorem mulBig_holds : MulBigContract := by
  -- 1. the stage contracts
  obtain ⟨Ca, ma, Ra, Padd, hma, hfa, hna, hcla, hA⟩ := WP.W0m.addSpec_of_W3 WP.W3.W3_addNat_holds
  obtain ⟨Cd, md, Rd, Pdiv, hmd, hfd, hnd, hcld, hD⟩ :=
    WP.W0m.divSpec_of_W6a (WP.W6a.W6a_divModNat_holds WP.W3.W3_subNat_holds)
  have hma6 : ma ≤ 6 := by omega
  obtain ⟨C7, hC7⟩ := w7_buildTables_proved
  obtain ⟨m7, R7, -, P7, hm7, hf7, hn7, hcl7, hspec7⟩ := hC7 ()
  obtain ⟨Cc, hCc⟩ := WP.Top.TapeConv_proved
  obtain ⟨mc, Rc, -, Pc, hmc, hfc, hnc, hclc, hspecc⟩ := hCc ()
  obtain ⟨c0, c1, w0, hmul⟩ := W5_toom3Mul_iff_mulAt.mp w5_toom3Mul_proved
  obtain ⟨C9, hC9⟩ := w9_multiply_proved (T3 c0 c1 w0) hmul
  obtain ⟨m9, R9, P9, hm9, hf9, hn9, hcl9, hspec9⟩ := hC9 ()
  -- 2. the pure cost facts (W9's cost shape, W5's rate, W7's `√n` bounds, W10)
  obtain ⟨pc, A9, K9, N9, hpb, hcs⟩ :=
    WP.Top.W9CostShape_of_W10b WP.Top.TapeConv_proved WP.W11b.widths_headline c0 c1 w0 C9
  obtain ⟨CM, hMB⟩ := WP.Top.mulBound_of_T3 WP.W5.W5_T3_bound_holds c0 c1 w0 K9
  obtain ⟨Cp, Np, hCp⟩ := WP.W7pure.W7_tableCost_sqrt_holds
  obtain ⟨Ct, Nt, hCt⟩ := WP.W7pure.W7_tapeBound_sqrt_holds
  obtain ⟨C10, N10, hC10⟩ := WP.W10.W10_cost_holds
    (WP.Top.topCosts 0 C7 Cp Ct Cc C9 (max (max Np Nt) N9) pc) _ (WP.Top.topCosts_bounds hpb)
    (WP.Top.mulCost K9 (T3 c0 c1 w0)) CM hMB
  -- 3. the runs, with W7's hierarchy choice skolemized
  have hrun := fun x y => mulBigProg_runs (Mul := T3 c0 c1 w0)
    (wdF := fun n _ => WP.W11b.wdHead n) (wdI := fun n _ => WP.W11b.wdHead n)
    (wR := WP.W11b.wRHead) hA hD hma6 hmd hspec7 hm7 hspecc hmc hspec9 hm9
    WP.W11b.w9RootOK_headline x y
  obtain ⟨cS, hcS⟩ := Classical.skolem.mp (fun x => Classical.skolem.mp (hrun x))
  let F : ℕ → ℕ → ℕ := fun x y => mbCost Ca Cd C7 Cc C9 (T3 c0 c1 w0)
    (fun n _ => WP.W11b.wdHead n) (fun n _ => WP.W11b.wdHead n) WP.W11b.wRHead x y (cS x y)
  let Klin : ℕ := 200000 + 576 * Cd + 2306 * Ca
  let Ncut : ℕ := max (max (max (max Np Nt) N9) N10) 2
  -- 4. the cost above the threshold
  have hbig : ∀ x y, Ncut ≤ operandBits x y → F x y ≤ (Klin + C10) * mulBigBound x y := by
    intro x y hN
    have hN0 : max (max Np Nt) N9 ≤ operandBits x y :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN10 : N10 ≤ operandBits x y :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hn2 : 2 ≤ operandBits x y := le_trans (le_max_right _ _) hN
    have hNp : Np ≤ operandBits x y :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN0
    have hNt : Nt ≤ operandBits x y :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN0
    have hN9 : N9 ≤ operandBits x y := le_trans (le_max_right _ _) hN0
    have hj := (hcS x y).1
    have hP : (W8.hSpec (operandBits x y)).precomputeSeriesTableCost ≤
        Cp * WP.Top.sqP (operandBits x y) := by
      have h := hCp (operandBits x y) hNp
      unfold WP.Top.sqP
      rw [← Nat.mul_assoc]
      exact h
    have hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat (cS x y)).length ≤
        Ct * WP.Top.sqP (operandBits x y) := by
      have h1 := hj.size
      have h2 := hCt (operandBits x y) hNt (cS x y) hj.canonical hj.faithful
      have h3 : (Nat.log2 (operandBits x y) + 1) ^ 3 ≤ (Nat.log2 (operandBits x y) + 1) ^ 8 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : Ct * (Nat.sqrt (operandBits x y) + 1) * (Nat.log2 (operandBits x y) + 1) ^ 3 ≤
          Ct * WP.Top.sqP (operandBits x y) := by
        unfold WP.Top.sqP
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      exact le_trans h1 (le_trans h2 h4)
    have hTS := (hspecc (operandBits x y) (cS x y)
      (fun _ => W7.tape W7.snapshotSchedule.toTapeFormat (cS x y)) hj rfl).1
    have h9 := hcs (operandBits x y) hN9 (cS x y) hj
    have h1 := mbCost_le_of_large (Ca := Ca) (Cd := Cd) (C7 := C7) (Mul := T3 c0 c1 w0)
      (wdF := fun n _ => WP.W11b.wdHead n) (wdI := fun n _ => WP.W11b.wdHead n)
      (wR := WP.W11b.wRHead) x y (cS x y) hN0 hP hT7 hTS h9
    have h2 := hC10 (operandBits x y) hN10
    calc F x y ≤ Klin * operandBits x y +
          (WP.Top.topCosts 0 C7 Cp Ct Cc C9 (max (max Np Nt) N9) pc).total
            (WP.Top.mulCost K9 (T3 c0 c1 w0)) (operandBits x y) := h1
      _ ≤ Klin * operandBits x y + C10 * operandBits x y * Nat.log2 (operandBits x y) :=
          Nat.add_le_add_left h2 _
      _ ≤ (Klin + C10) * mulBigBound x y := lin_nlog_le x y Klin C10
  -- 5. all inputs: below the threshold, a finite maximum
  have hall : ∀ x y, F x y ≤ (Klin + C10 + WP.Top.supCost F Ncut) * mulBigBound x y := by
    intro x y
    have hb1 : 1 ≤ mulBigBound x y := by
      unfold mulBigBound
      omega
    by_cases hN : Ncut ≤ operandBits x y
    · calc F x y ≤ (Klin + C10) * mulBigBound x y := hbig x y hN
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · rw [not_le] at hN
      obtain ⟨hx, hy, -, -⟩ := input_bridge x y
      have hpow : 2 ^ operandBits x y ≤ 2 ^ Ncut := Nat.pow_le_pow_right (by omega) hN.le
      calc F x y ≤ WP.Top.supCost F Ncut :=
            WP.Top.le_supCost F (hx.trans_le hpow) (hy.trans_le hpow)
        _ ≤ WP.Top.supCost F Ncut * mulBigBound x y := Nat.le_mul_of_pos_right _ hb1
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  -- 6. the packaging
  refine ⟨Klin + C10 + WP.Top.supCost F Ncut, MRegs Ra Rd R7 Rc R9,
    mulBigProg Padd hma6 Pdiv hmd P7 hm7 Pc hmc P9 hm9, inferInstance, inferInstance,
    mulBigProg_closed hma6 hmd hm7 hmc hm9 hcla hcld hcl7 hclc hcl9, ?_⟩
  exact spec_of_runs fun x y rx ry rz hrx hry =>
    WP.W0m.runs_mono ((hcS x y).2 rx ry rz hrx hry) (fun _ h => h) (hall x y)

/-- **Non-vacuity.** The packaged `mulBig` program evaluates, for every `x y` and from some register
value, from `X = natSyms x`, `Y = natSyms y`, `Z = []` and empty scratch exactly to the same stacks
with `Z = natSyms (x * y)`, within `C * mulBigBound x y` steps. -/
theorem mulBig_nonvacuous : ∃ (C : ℕ) (R : Type) (P : Prog MBLoc (fun _ => Sym) R), P.Closed ∧
    ∀ x y : ℕ, ∃ (r r' : R) (t : ℕ),
      Eval [] P ⟨r, mbSt (natSyms x) (natSyms y) [] (fun _ => [])⟩
        ⟨r', mbSt (natSyms x) (natSyms y) (natSyms (x * y)) (fun _ => [])⟩ t ∧
      t ≤ C * mulBigBound x y := by
  obtain ⟨C, R, P, -, hn, hcl, hspec⟩ := mulBig_holds
  refine ⟨C, R, P, hcl, fun x y => ?_⟩
  obtain ⟨r⟩ := hn
  have h := hspec x y [] [] [] (mbSt (natSyms x) (natSyms y) [] (fun _ => [])) TermOK.nil
    TermOK.nil (List.append_nil _).symm (List.append_nil _).symm rfl (fun _ => rfl)
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨r, mbSt (natSyms x) (natSyms y) [] (fun _ => [])⟩ rfl
  rw [mbSt_update_inl2, List.append_nil] at hs'
  refine ⟨r, s'.var, t, ?_, ht⟩
  rw [← hs']
  exact e

#assert_std_axioms operandBits_le_mulBigSize copyIn_param_le cleanup_le w9Cost_eq lin_nlog_le
  sqP_le_lin poly_le_lin mbCost_le_of_large mbCost_eq_overhead mbOverhead_le mulBig_holds
  mulBig_nonvacuous

end SubNLogN.Machine.MulBig
