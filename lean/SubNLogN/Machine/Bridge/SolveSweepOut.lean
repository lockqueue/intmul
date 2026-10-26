/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepDefs

/-!
# K5-SOLVE (1i): the row-level form of the sweep output (definitions)

The sweep kernel processes an `L × M` row-major half row by row (`SolveSweepRow.lean`). This file
gives the row-level description of what it computes:
* `rowOf M ys j`: data row `j`;
* `bRowI`: the scaled row `b_s = Quant_q(μ_s y_s)`;
* `stepRowI`: one prefix row `p'_s = b_s + Quant_q(na_s p_s)`; `stepRowB`: the same from stored `b`;
* `closRow`: the closure row `Quant_q(γ_s p_s)`;
* `prefRows`: the prefix-pass rows (row `0` is `b` itself: state `0` before it);
* `bAll k`: the `b` rows `0..k-1` concatenated (the stored `b` stream);
* `secRows c`, `secAll c k`: the second-pass rows from the closure row `c`, and rows `0..k-1`
  concatenated;
* `sweepOut`: the kernel output, second-pass rows `0..L-2` followed by the closure row.
Definitions only; `sweepOut = sweepHalfI` is proved separately.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts SubNLogN.Machine

/-- Data row `j` of an `L × M` row-major list. -/
def rowOf (M : ℕ) (ys : List CInt) (j : ℕ) : List CInt := (ys.drop (j * M)).take M

/-- The `b` values of a row: `b_s = Quant_q(μ_s y_s)`. -/
def bRowI (q M : ℕ) (mus : List ℤ) (yr : List CInt) : List CInt :=
  (List.range M).map fun s => bI q (mus.getD s 0) (yr.getD s 0)

/-- The new states of a prefix row: `p'_s = b_s + Quant_q(na_s p_s)`. -/
def stepRowI (q M : ℕ) (mus nas : List ℤ) (yr prev : List CInt) : List CInt :=
  (List.range M).map fun s => stepI q (nas.getD s 0) (bI q (mus.getD s 0) (yr.getD s 0))
    (prev.getD s 0)

/-- The new states of a second-pass row from the stored `b` row `br`. -/
def stepRowB (q M : ℕ) (nas : List ℤ) (br prev : List CInt) : List CInt :=
  (List.range M).map fun s => stepI q (nas.getD s 0) (br.getD s 0) (prev.getD s 0)

/-- The closure row `Quant_q(γ_s p_s)`. -/
def closRow (q M : ℕ) (gms : List ℤ) (p : List CInt) : List CInt :=
  (List.range M).map fun s => rI q (gms.getD s 0) (p.getD s 0)

/-- The prefix-pass rows (from the zero state): row `0` is `b`, row `j+1` one step. -/
def prefRows (q M : ℕ) (mus nas : List ℤ) (ys : List CInt) : ℕ → List CInt
  | 0 => bRowI q M mus (rowOf M ys 0)
  | j + 1 => stepRowI q M mus nas (rowOf M ys (j + 1)) (prefRows q M mus nas ys j)

/-- The `b` rows `0..k-1`, concatenated. -/
def bAll (q M : ℕ) (mus : List ℤ) (ys : List CInt) : ℕ → List CInt
  | 0 => []
  | k + 1 => bAll q M mus ys k ++ bRowI q M mus (rowOf M ys k)

/-- The second-pass rows from the closure row `c` (row `j` uses the stored `b` row `j`). -/
def secRows (q M : ℕ) (mus nas : List ℤ) (ys : List CInt) (c : List CInt) : ℕ → List CInt
  | 0 => stepRowB q M nas (bRowI q M mus (rowOf M ys 0)) c
  | j + 1 => stepRowB q M nas (bRowI q M mus (rowOf M ys (j + 1))) (secRows q M mus nas ys c j)

/-- The second-pass rows `0..k-1`, concatenated. -/
def secAll (q M : ℕ) (mus nas : List ℤ) (ys : List CInt) (c : List CInt) : ℕ → List CInt
  | 0 => []
  | k + 1 => secAll q M mus nas ys c k ++ secRows q M mus nas ys c k

/-- The closure row of the half (from the last prefix row). -/
def crowOf (q L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt) : List CInt :=
  closRow q M gms (prefRows q M mus nas ys (L - 1))

/-- The kernel output: second-pass rows `0..L-2`, then the closure row. -/
def sweepOut (q L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt) : List CInt :=
  secAll q M mus nas ys (crowOf q L M mus nas gms ys) (L - 1) ++ crowOf q L M mus nas gms ys

end SubNLogN.Machine.Bridge.SolveAux
