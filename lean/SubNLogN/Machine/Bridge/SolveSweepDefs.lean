/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Arith

/-!
# K5-SOLVE (1b): the integer recurrence computed by the sweep kernel

The solver kernel (`SolveSweep*.lean`) works on numerators: a half of a deconvolution stage is an
`L × M` row-major array `ys` of one-coefficient records (column `s` is one cycle), with per-column
parameters `μ_s` (`mus`), the *negated* recurrence parameter `-â_s` (`nas`) and `γ̂_s` (`gms`), all
real numerators at `q = P + 2`. The kernel computes, per column, exactly the following integer
recurrence (the leaf kernels' operations: exact products `cmulTruncC 0`, half-up rounding
`roundHalfUpShiftC q`, exact sums `caddC`):
* `bI`: `b = Quant_q(μ y)`;
* `rI`: `Quant_q(a·p)` for a real parameter numerator `a`;
* `stepI`: one recurrence step `b + Quant_q(na·p)` (`na = -â`);
* `passI`: one pass from an initial state (`z_{-1}`);
* `closI`: the closure value `Quant_q(γ p_{L-1})` (prefix pass from `0`);
* `colI`: the column output: second pass from the closure value, and the closure value itself at
  the last row (`cycSweepFwdR roundHalfUpR`'s convention, Lemma 4.6 (`lem:bridge-C`)(iv));
* `sweepHalfI`: the whole half.
All definitions; the elementary identities are proved here.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts SubNLogN.Machine

/-- `b = Quant_q(μ·y)`, in the form produced by the leaf kernels. -/
def bI (q : ℕ) (mu : ℤ) (y : CInt) : CInt := roundHalfUpShiftC q (cmulTruncC 0 y (mu, 0))

/-- `Quant_q(a·p)` for a real parameter numerator `a`. -/
def rI (q : ℕ) (a : ℤ) (p : CInt) : CInt := roundHalfUpShiftC q (cmulTruncC 0 p (a, 0))

/-- One recurrence step `b + Quant_q(na·p)`. -/
def stepI (q : ℕ) (na : ℤ) (b p : CInt) : CInt := caddC b (rI q na p)

/-- The states of one pass started from `z0` (= `z_{-1}`). -/
def passI (q : ℕ) (mu na : ℤ) (ys : ℕ → CInt) (z0 : CInt) : ℕ → CInt
  | 0 => stepI q na (bI q mu (ys 0)) z0
  | j + 1 => stepI q na (bI q mu (ys (j + 1))) (passI q mu na ys z0 j)

/-- The closure value `Quant_q(γ p_{L-1})`, `p` the prefix pass from `0`. -/
def closI (q : ℕ) (mu na gm : ℤ) (L : ℕ) (ys : ℕ → CInt) : CInt :=
  rI q gm (passI q mu na ys (0, 0) (L - 1))

/-- The column output at row `j`: the second pass from the closure value, except that row `L - 1`
outputs the closure value itself. -/
def colI (q : ℕ) (mu na gm : ℤ) (L : ℕ) (ys : ℕ → CInt) (j : ℕ) : CInt :=
  if j = L - 1 then closI q mu na gm L ys else passI q mu na ys (closI q mu na gm L ys) j

/-- The output of the sweep on an `L × M` row-major half. -/
def sweepHalfI (q L M : ℕ) (mus nas gms : List ℤ) (ys : List CInt) : List CInt :=
  (List.range (L * M)).map fun x =>
    colI q (mus.getD (x % M) 0) (nas.getD (x % M) 0) (gms.getD (x % M) 0) L
      (fun j => ys.getD (j * M + x % M) 0) (x / M)

/-- Both components fit `w` bits. -/
def Fits2 (w : ℕ) (c : CInt) : Prop := FitsTwos w c.1 ∧ FitsTwos w c.2

/-- Width side condition of one column of the sweep (from `SolveFits`): the scaled inputs, the
prefix states, the closure value and the second-pass states fit `w` bits. -/
def ColFitsI (w q : ℕ) (mu na gm : ℤ) (L : ℕ) (ys : ℕ → CInt) : Prop :=
  Fits2 w (closI q mu na gm L ys) ∧ ∀ n, n < L →
    Fits2 w (bI q mu (ys n)) ∧ Fits2 w (passI q mu na ys (0, 0) n) ∧
      Fits2 w (passI q mu na ys (closI q mu na gm L ys) n)

/-- Stack content of the one-coefficient records `l` at width `w` (first record on top). -/
def rec1s (w : ℕ) (l : List CInt) : List Sym := carrSyms w (l.map fun c => [c])

/-! ## Elementary identities -/

theorem tdivPow_zero (z : ℤ) : tdivPow z 0 = z := by
  simp [tdivPow]

theorem cmulTruncC_zero_real (y : CInt) (a : ℤ) : cmulTruncC 0 y (a, 0) = (y.1 * a, y.2 * a) := by
  simp [cmulTruncC, truncShiftC, cmulC, tdivPow_zero]

theorem rhuPow_zero_left (s : ℕ) : rhuPow 0 s = 0 := by
  unfold rhuPow
  have hn : (0 : ℤ) < 2 ^ s := by positivity
  apply Int.ediv_eq_zero_of_lt <;> omega

theorem rI_zero (q : ℕ) (a : ℤ) : rI q a (0, 0) = (0, 0) := by
  simp [rI, cmulTruncC_zero_real, roundHalfUpShiftC, rhuPow_zero_left]

theorem stepI_zero (q : ℕ) (na : ℤ) (b : CInt) : stepI q na b (0, 0) = b := by
  simp [stepI, rI_zero, caddC]

end SubNLogN.Machine.Bridge.SolveAux
