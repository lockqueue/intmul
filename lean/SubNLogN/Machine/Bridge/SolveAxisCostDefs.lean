/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisSetup

/-!
# K5-SOLVE driver: the cost of the driver run (definition only)

`drvCost b i Cp Cs Cm Cr Cj Cw` is the sum of the per-step cost bounds of the deconvolution-stage
driver (`Bridge/SolveAxisRuns.lean`), in program order, with the constants of the parameter-row
(`Cp`), split (`Cs`), merge (`Cm`), reindex (`Cr`, `Cj`) and sweep (`Cw`) kernels:
setup, rows (h = 0), counting `M`, split, forward sweep, three row erasures, `KH := 1`, rows
(h = 1), `KH := 0`, reindex `I`, backward sweep, reindex `J`, three row erasures, merge, seven
counter erasures. Here `M = solveM t i = (R/A_i)/2`, `L = A_i = prefixProd t i`, `R = L·2M`.
-/

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common
  SubNLogN.Math.Bridge

/-- Per-step cost bounds of the driver run, summed in program order. -/
def drvCost (b : BrPar) (i : Fin b.d) (Cp Cs Cm Cr Cj Cw : ℕ) : ℕ :=
  setupCost b +
  Cp * (solveM b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup) +
  (solveM b.t i * (24 * b.wT + 6 * bitLen (solveM b.t i) + 57) + 4) +
  Cs * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (bitLen (solveM b.t i) + 1) + 1) +
  Cw * (prefixProd b.t i * solveM b.t i * (mulW (b.wI + (b.wT + 1) + 1) + bitLen (b.P + 2) + 1)
    + 1) +
  (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) +
  (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) +
  (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) + 1 +
  Cp * (solveM b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup) + 1 +
  Cr * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
    prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) + 1) +
  Cw * (prefixProd b.t i * solveM b.t i * (mulW (b.wI + (b.wT + 1) + 1) + bitLen (b.P + 2) + 1)
    + 1) +
  Cj * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
    prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) + 1) +
  (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) +
  (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) +
  (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) +
  Cm * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
    prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) +
    (prefixProd b.t i * solveM b.t i + prefixProd b.t i * solveM b.t i) *
      (bitLen (solveM b.t i) + 1) + 1) +
  (3 * bitLen b.wI + 2) + (3 * bitLen b.wI + 2) + (3 * bitLen (b.wI + 1) + 2) +
  (3 * bitLen (b.wT + 1) + 2) + (3 * bitLen (b.wI + b.wT + 2) + 2) +
  (3 * bitLen (b.P + 2) + 2) + (3 * bitLen (solveM b.t i) + 2)

end SubNLogN.Machine.Bridge.SolveDrvAux
