import WP.W7k3t.Vals
import WP.W7k2.Canon.Kernels

/-!
# WP.W7k3t.Smoke — evaluated value-level checks of the tap kernel's values

`tapV` (Vals.lean) composes the values computed by the tap kernel's sub-kernels. It is proved
equal to W7k2's canonical `tapC` (`tapC_eq_tapV`, Decomp.lean). `tapC` in turn is proved equal to
the snapshot's `computableSincGaussianTapWithProgramCost` (`tapC_eq`).

The `#guard` lines below evaluate `tapV` directly against the snapshot at small inputs, as an
independent bit-exactness check. They also check the operand widths against `tapW`, as Bool
mirrors of the width statements: `setupWB` for the setup operands, `elseWB` for the else branch,
with `serWB` mirroring `SerW`.

A machine-level run is not possible here. The kernel composes abstract contract instances (`TI`:
the W3/W5/W6a arithmetic contracts), and this package has no concrete programs for them.

Points `p_work pSub t1 j1 s` (`pSub = 2`, so `B_c = W7.tapPrec 2 = 102`, `tapW 3 2 2 = 1308`):
* `3 2 2 1 0`: `numT = 5`, `(pSub+4)·denY ≤ numY`, so the tap clamps to `0`;
* `3 2 2 1 1`: `numT = 3`, `s < pSub` (signed offset), else branch;
* `3 2 2 1 2`: `numT = 1`, else branch.

Evaluation is cheap: two series of `17·pSub + 22 = 56` steps on numbers of a few hundred bits.
-/

namespace WP.W7k3t.Smoke

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3t

/-- `π` at the tap precision, as the level computes it. -/
def piN (pSub : ℕ) : ℕ := (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1.toNat

/-- `ln 2` at the tap precision. -/
def lnN (pSub : ℕ) : ℕ := (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1.toNat

/-- The sinc series step denominators. -/
def gS : ℕ → ℕ := fun k => (2 * k + 2) * (2 * k + 3)

/-- The Gaussian series step denominators. -/
def gE : ℕ → ℕ := fun k => k + 1

/-- `tapV` at the level's `π`, `ln 2` equals the snapshot's tap. -/
def tapOK (p_work pSub t1 j1 s : ℕ) : Bool :=
  tapV p_work pSub t1 j1 s (piN pSub) (lnN pSub) ==
    (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1

/-- Is the point in the clamp-to-`0` branch of `tapV`? -/
def clamps (p_work pSub t1 j1 s : ℕ) : Bool :=
  let πN := piN pSub
  let numT := numTV pSub t1 j1 s
  decide ((pSub + 4) * denYV p_work pSub t1 (lnN pSub) ≤ πN * numT * (πN * numT))

/-- Bool mirror of the setup width statement (`tap_widths_setup`). -/
def setupWB (p_work pSub t1 j1 s : ℕ) : Bool :=
  let W := tapW p_work pSub t1
  let πN := piN pSub
  let ln := lnN pSub
  let numT := numTV pSub t1 j1 s
  let NY := πN * numT * (πN * numT)
  let DY := denYV p_work pSub t1 ln
  decide (43 * pSub + 61 ≤ W) && decide (bitLen p_work ≤ W) && decide (bitLen t1 ≤ W) &&
  decide (bitLen j1 ≤ W) && decide (bitLen s ≤ W) &&
  decide (bitLen (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)).natAbs ≤ W) && decide (bitLen numT ≤ W) &&
  decide (bitLen πN ≤ W) && decide (bitLen (πN * numT) ≤ W) && decide (bitLen NY ≤ W) &&
  decide (bitLen (4 * p_work) ≤ W) && decide (bitLen ln ≤ W) &&
  decide (bitLen (4 * p_work * ln) ≤ W) && decide (bitLen (t1 * t1) ≤ W) &&
  decide (bitLen (4 * p_work * ln * (t1 * t1)) ≤ W) && decide (bitLen DY ≤ W) &&
  decide (bitLen ((pSub + 4) * DY) ≤ W)

/-- Bool mirror of `SerW W g pSub NY d`. -/
def serWB (W : ℕ) (g : ℕ → ℕ) (pSub NY d : ℕ) : Bool :=
  let N := 17 * pSub + 22
  let st := fun k => serState ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ)) d (fun _ => 1) g k
  let y := (serV g pSub NY d).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ)
  decide (bitLen NY ≤ W) && decide (bitLen d ≤ W) &&
  (List.range (N + 1)).all (fun k =>
    decide (bitLen (st k).1.natAbs ≤ W) && decide (bitLen (st k).2.natAbs ≤ W)) &&
  (List.range N).all (fun k =>
    decide (bitLen ((st k).1 * -(NY : ℤ)).natAbs ≤ W) && decide (bitLen (g k * d) ≤ W) &&
    decide (0 < g k * d)) &&
  decide (bitLen y.natAbs ≤ W) &&
  decide (bitLen (divRoundRatInt y ((2 ^ (43 * pSub + 60) : ℕ) : ℤ)).natAbs ≤ W)

/-- Bool mirror of the else-branch width statement (`tap_widths_else`, under the non-clamp
condition). -/
def elseWB (p_work pSub t1 j1 s : ℕ) : Bool :=
  let W := tapW p_work pSub t1
  let πN := piN pSub
  let numT := numTV pSub t1 j1 s
  let NY := πN * numT * (πN * numT)
  let DY := denYV p_work pSub t1 (lnN pSub)
  let D := denThV pSub t1
  let SV := clampSerV gS pSub NY (D * D)
  let EV := clampSerV gE pSub NY DY
  decide (bitLen D ≤ W) && decide (bitLen (D * D) ≤ W) && serWB W gS pSub NY (D * D) &&
  serWB W gE pSub NY DY && decide (bitLen SV.natAbs ≤ W) && decide (bitLen EV.natAbs ≤ W) &&
  decide (bitLen (SV * EV).natAbs ≤ W) &&
  decide (bitLen (SV * EV * ((2 ^ pSub : ℕ) : ℤ)).natAbs ≤ W) &&
  decide (bitLen (divRoundRatInt (SV * EV * ((2 ^ pSub : ℕ) : ℤ))
    ((2 ^ (2 * pSub + 4) : ℕ) : ℤ)).natAbs ≤ W)

/-- Informational: `(W, bitLen numY, bitLen denY, bitLen ((pSub+4)·denY), sinc clamp, exp clamp,
bitLen |S_sinc|, bitLen |S_exp|, tap)`. -/
def widths (p_work pSub t1 j1 s : ℕ) : ℕ × ℕ × ℕ × ℕ × ℤ × ℤ × ℕ × ℕ × ℤ :=
  let πN := piN pSub
  let numT := numTV pSub t1 j1 s
  let NY := πN * numT * (πN * numT)
  let DY := denYV p_work pSub t1 (lnN pSub)
  let D := denThV pSub t1
  (tapW p_work pSub t1, bitLen NY, bitLen DY, bitLen ((pSub + 4) * DY),
    clampSerV gS pSub NY (D * D), clampSerV gE pSub NY DY,
    bitLen (serV gS pSub NY (D * D)).2.natAbs, bitLen (serV gE pSub NY DY).2.natAbs,
    tapV p_work pSub t1 j1 s πN (lnN pSub))

#eval [widths 3 2 2 1 0, widths 3 2 2 1 1, widths 3 2 2 1 2]

-- (1) bit-exactness against the snapshot: the clamp point and two else points.
#guard tapOK 3 2 2 1 0
#guard tapOK 3 2 2 1 1
#guard tapOK 3 2 2 1 2
#guard clamps 3 2 2 1 0
#guard !clamps 3 2 2 1 1
#guard !clamps 3 2 2 1 2

-- (2) widths: the setup operands at every point; the else-branch operands where it is taken.
#guard setupWB 3 2 2 1 0
#guard setupWB 3 2 2 1 1
#guard setupWB 3 2 2 1 2
#guard elseWB 3 2 2 1 1
#guard elseWB 3 2 2 1 2

end WP.W7k3t.Smoke
