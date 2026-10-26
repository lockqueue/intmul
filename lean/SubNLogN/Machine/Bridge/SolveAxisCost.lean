/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisCostDefs
import SubNLogN.Machine.Bridge.SolveMath

/-!
# K5-SOLVE driver: the cost bound (`Bridge/SolveAxisCost.lean`)

`drvCost_le`: the summed per-step cost of the deconvolution-stage driver (`drvCost`,
`SolveAxisCostDefs.lean`) is at most `drvConst · solveCost b`, under the width hypotheses of
`SolveAxisStmt` (`P + 2 ≤ wI`, `log₂ R ≤ wI`, `1 ≤ wI, wT`). Uses `R = A_i · 2M`
(`SolveMathAux.solve_arith`), `mulW (n+1) ≤ 4 mulW n`, `bitLen M ≤ log₂ R + 1`,
`wT · bitLen (wI + wT) ≤ mulW (wI + wT + 1)` and `|hdr| + 1 ≤ setup`. All proved.
-/

namespace SubNLogN.Machine.Bridge.SolveCostAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common
  SubNLogN.Math.Bridge

theorem bl_eq_size (n : ℕ) : bitLen n = Nat.size n := by
  unfold bitLen; rw [IntMulTM.length_encodeNat]

theorem bl_le_self (n : ℕ) : bitLen n ≤ n := by
  rw [bl_eq_size]; exact Nat.size_le.2 Nat.lt_two_pow_self

theorem bl_le_log2 (n : ℕ) : bitLen n ≤ Nat.log2 n + 1 := by
  rw [bl_eq_size]; exact Nat.size_le.2 Nat.lt_log2_self

theorem bl_mono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  rw [bl_eq_size, bl_eq_size]; exact Nat.size_le_size h

theorem log2_succ_le' (n : ℕ) : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
  have h : Nat.log2 (n + 1) < Nat.log2 n + 2 := by
    rw [Nat.log2_lt (by omega)]
    have h1 := Nat.lt_log2_self (n := n)
    have h2 : 2 ^ (Nat.log2 n + 2) = 2 ^ (Nat.log2 n + 1) * 2 := by
      rw [show Nat.log2 n + 2 = Nat.log2 n + 1 + 1 by omega, Nat.pow_succ]
    rw [h2]; omega
  omega

theorem mulW_succ_le4 (n : ℕ) (hn : 1 ≤ n) : mulW (n + 1) ≤ 4 * mulW n := by
  unfold mulW
  have h := log2_succ_le' n
  have h1 : (n + 1) * (Nat.log2 (n + 1) + 1) ≤ (n + 1) * (Nat.log2 n + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (n + 1) * (Nat.log2 n + 2) ≤ (2 * n) * (Nat.log2 n + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 * n) * (Nat.log2 n + 2) = 2 * (n * Nat.log2 n) + 4 * n := by ring
  have h4 : n * (Nat.log2 n + 1) = n * Nat.log2 n + n := by ring
  omega

theorem mul_bl_le_mulW {a n : ℕ} (ha : a ≤ n) : a * bitLen n ≤ mulW (n + 1) := by
  unfold mulW
  have h1 : bitLen n ≤ Nat.log2 (n + 1) + 1 := by
    rw [bl_eq_size]
    exact Nat.size_le.2 (by have := Nat.lt_log2_self (n := n + 1); omega)
  have h2 : a * bitLen n ≤ (n + 1) * (Nat.log2 (n + 1) + 1) := Nat.mul_le_mul (by omega) h1
  omega

end SubNLogN.Machine.Bridge.SolveCostAux

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common
  SubNLogN.Math.Bridge SubNLogN.Machine.Bridge.SolveCostAux

/-- The cost constant of the deconvolution-stage driver. -/
def drvConst (Cp Cs Cm Cr Cj Cw : ℕ) : ℕ :=
  600 + 2 * Cp + 3 * Cs + 12 * Cw + 3 * Cr + 3 * Cj + 3 * Cm

/-- **The driver cost bound.** -/
theorem drvCost_le (b : BrPar) (i : Fin b.d) (Cp Cs Cm Cr Cj Cw : ℕ) (hshape : ShapeOK b.t)
    (hi : (i : ℕ) ≠ 0) (hwI : 1 ≤ b.wI) (hwT : 1 ≤ b.wT) (hP : b.P + 2 ≤ b.wI)
    (hlog : Nat.log2 (totalLen b.t) ≤ b.wI) :
    drvCost b i Cp Cs Cm Cr Cj Cw ≤ drvConst Cp Cs Cm Cr Cj Cw * solveCost b := by
  obtain ⟨hL0, hM0, -, -, -, hRLM, -⟩ := SolveMathAux.solve_arith hshape i
  have hd : 1 ≤ b.d := by have := i.isLt; omega
  have hSC : solveCost b = totalLen b.t * (2 * (b.wI + b.wT) + 1) +
      totalLen b.t * mulW (b.wI + b.wT + 1) + b.d * solTabLen b + b.setup := by
    simp only [solveCost, vol1, BrPar.R]
  have hLM : prefixProd b.t i * solveM b.t i ≤ totalLen b.t := by
    rw [hRLM]; exact Nat.mul_le_mul_left _ (by omega)
  have hML : solveM b.t i ≤ prefixProd b.t i * solveM b.t i := Nat.le_mul_of_pos_left _ hL0
  have hR2 : totalLen b.t = 2 * (prefixProd b.t i * solveM b.t i) := by rw [hRLM]; ring
  have hR1 : 1 ≤ totalLen b.t := by omega
  have hbM : bitLen (solveM b.t i) ≤ b.wI + 1 := by
    have h1 := bl_mono (show solveM b.t i ≤ totalLen b.t by omega)
    have h2 := bl_le_log2 (totalLen b.t)
    omega
  have hbP : bitLen (b.P + 2) ≤ b.wI := (bl_le_self _).trans hP
  have hV1 : b.wI + b.wT + 1 ≤ totalLen b.t * (2 * (b.wI + b.wT) + 1) := by
    have := Nat.mul_le_mul hR1 (le_refl (2 * (b.wI + b.wT) + 1)); omega
  have hW1 : mulW (b.wI + b.wT + 1) ≤ totalLen b.t * mulW (b.wI + b.wT + 1) :=
    Nat.le_mul_of_pos_left _ hR1
  have hS1 : (hdrSyms b.hdr).length + 1 ≤ b.setup := by
    have h := Nat.pow_le_pow_right (show 0 < (hdrSyms b.hdr).length + 1 by omega)
      (show 1 ≤ 3 by norm_num)
    simpa [BrPar.setup] using h
  have hSC1 : totalLen b.t * (2 * (b.wI + b.wT) + 1) + totalLen b.t * mulW (b.wI + b.wT + 1) +
      b.setup ≤ solveCost b := by rw [hSC]; omega
  -- the bracket of each kernel call
  have kPar : solveM b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup ≤
      solveCost b := by
    have m1 : solveM b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) ≤
        totalLen b.t * (2 * (b.wI + b.wT) + 1) := Nat.mul_le_mul (by omega) (by omega)
    have m2 : solTabLen b ≤ b.d * solTabLen b := Nat.le_mul_of_pos_left _ hd
    rw [hSC]; omega
  have kSp : totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (bitLen (solveM b.t i) + 1) + 1 ≤
      3 * solveCost b := by
    have m1 : totalLen b.t * (2 * b.wI + 1) ≤ totalLen b.t * (2 * (b.wI + b.wT) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have m2 : totalLen b.t * (bitLen (solveM b.t i) + 1) ≤
        totalLen b.t * (2 * (b.wI + b.wT) + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [hSC]; omega
  have kSw : prefixProd b.t i * solveM b.t i * (mulW (b.wI + (b.wT + 1) + 1) +
      bitLen (b.P + 2) + 1) + 1 ≤ 6 * solveCost b := by
    have hmw : mulW (b.wI + (b.wT + 1) + 1) ≤ 4 * mulW (b.wI + b.wT + 1) := by
      have := mulW_succ_le4 (b.wI + b.wT + 1) (by omega)
      rwa [show b.wI + b.wT + 1 + 1 = b.wI + (b.wT + 1) + 1 by omega] at this
    have m1 : prefixProd b.t i * solveM b.t i * (mulW (b.wI + (b.wT + 1) + 1) +
        bitLen (b.P + 2) + 1) ≤ totalLen b.t * (4 * mulW (b.wI + b.wT + 1) + (b.wI + 1)) :=
      Nat.mul_le_mul hLM (by omega)
    have m2 : totalLen b.t * (4 * mulW (b.wI + b.wT + 1) + (b.wI + 1)) =
        4 * (totalLen b.t * mulW (b.wI + b.wT + 1)) + totalLen b.t * (b.wI + 1) := by ring
    have m3 : totalLen b.t * (b.wI + 1) ≤ totalLen b.t * (2 * (b.wI + b.wT) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hSC]; omega
  have kRe : prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
      prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) + 1 ≤ 3 * solveCost b := by
    have m1 : prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) ≤
        totalLen b.t * (2 * (b.wI + b.wT) + 1) := Nat.mul_le_mul hLM (by omega)
    have m2 : prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) ≤
        totalLen b.t * (2 * (b.wI + b.wT) + 1) := Nat.mul_le_mul hLM (by omega)
    rw [hSC]; omega
  have kMg : prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
      prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
      (prefixProd b.t i * solveM b.t i + prefixProd b.t i * solveM b.t i) *
        (bitLen (solveM b.t i) + 1) + 1 ≤ 3 * solveCost b := by
    have m1 : prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
        prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) ≤
        totalLen b.t * (2 * (b.wI + b.wT) + 1) := by
      rw [show prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
          prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) =
          2 * (prefixProd b.t i * solveM b.t i) * (2 * b.wI + 1) by ring, ← hR2]
      exact Nat.mul_le_mul_left _ (by omega)
    have m2 : (prefixProd b.t i * solveM b.t i + prefixProd b.t i * solveM b.t i) *
        (bitLen (solveM b.t i) + 1) ≤ totalLen b.t * (2 * (b.wI + b.wT) + 1) := by
      rw [show prefixProd b.t i * solveM b.t i + prefixProd b.t i * solveM b.t i =
          2 * (prefixProd b.t i * solveM b.t i) by ring, ← hR2]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [hSC]; omega
  -- the terms without a kernel constant
  have kSet : setupCost b ≤ 77 * b.setup + 200 * (totalLen b.t * (2 * (b.wI + b.wT) + 1)) +
      12 * (totalLen b.t * mulW (b.wI + b.wT + 1)) := by
    unfold setupCost
    have h1 := bl_le_self (b.wI + b.wT + 2)
    have h2 : b.wT * bitLen (b.wI + b.wT) ≤ mulW (b.wI + b.wT + 1) := mul_bl_le_mulW (by omega)
    have h3 : b.wT * bitLen b.wT ≤ mulW (b.wI + b.wT + 1) :=
      (Nat.mul_le_mul_left _ (bl_mono (show b.wT ≤ b.wI + b.wT by omega))).trans h2
    have e : b.wT * (6 * bitLen (b.wI + b.wT) + 6 * bitLen b.wT + 19) =
        6 * (b.wT * bitLen (b.wI + b.wT)) + 6 * (b.wT * bitLen b.wT) + 19 * b.wT := by ring
    omega
  have kM24 : solveM b.t i * (24 * b.wT + 6 * bitLen (solveM b.t i) + 57) ≤
      63 * (totalLen b.t * (2 * (b.wI + b.wT) + 1)) := by
    calc solveM b.t i * (24 * b.wT + 6 * bitLen (solveM b.t i) + 57) ≤
          totalLen b.t * (63 * (2 * (b.wI + b.wT) + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 63 * (totalLen b.t * (2 * (b.wI + b.wT) + 1)) := by ring
  have kM3 : solveM b.t i * (2 * (b.wT + 1) + 1) ≤
      3 * (totalLen b.t * (2 * (b.wI + b.wT) + 1)) := by
    calc solveM b.t i * (2 * (b.wT + 1) + 1) ≤
          totalLen b.t * (3 * (2 * (b.wI + b.wT) + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * (totalLen b.t * (2 * (b.wI + b.wT) + 1)) := by ring
  have hb1 := bl_le_self b.wI
  have hb2 := bl_le_self (b.wI + 1)
  have hb3 := bl_le_self (b.wT + 1)
  have hb4 := bl_le_self (b.wI + b.wT + 2)
  -- the terms with a kernel constant
  have cPar := Nat.mul_le_mul_left Cp kPar
  have cSp : Cs * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (bitLen (solveM b.t i) + 1) +
      1) ≤ 3 * (Cs * solveCost b) :=
    (Nat.mul_le_mul_left Cs kSp).trans (le_of_eq (by ring))
  have cSw : Cw * (prefixProd b.t i * solveM b.t i * (mulW (b.wI + (b.wT + 1) + 1) +
      bitLen (b.P + 2) + 1) + 1) ≤ 6 * (Cw * solveCost b) :=
    (Nat.mul_le_mul_left Cw kSw).trans (le_of_eq (by ring))
  have cRe : Cr * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
      prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) + 1) ≤
      3 * (Cr * solveCost b) :=
    (Nat.mul_le_mul_left Cr kRe).trans (le_of_eq (by ring))
  have cRj : Cj * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
      prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) + 1) ≤
      3 * (Cj * solveCost b) :=
    (Nat.mul_le_mul_left Cj kRe).trans (le_of_eq (by ring))
  have cMg : Cm * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
      prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
      (prefixProd b.t i * solveM b.t i + prefixProd b.t i * solveM b.t i) *
        (bitLen (solveM b.t i) + 1) + 1) ≤ 3 * (Cm * solveCost b) :=
    (Nat.mul_le_mul_left Cm kMg).trans (le_of_eq (by ring))
  have hfin : drvConst Cp Cs Cm Cr Cj Cw * solveCost b = 600 * solveCost b +
      2 * (Cp * solveCost b) + 3 * (Cs * solveCost b) + 12 * (Cw * solveCost b) +
      3 * (Cr * solveCost b) + 3 * (Cj * solveCost b) + 3 * (Cm * solveCost b) := by
    unfold drvConst; ring
  rw [hfin]
  unfold drvCost
  omega

end SubNLogN.Machine.Bridge.SolveDrvAux
