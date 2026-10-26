import IntMulTM.Exec.TopC
import WP.W7k2.Concrete
import WP.F9.Top
import WP.F9.Run

/-!
# The concrete final machine, end to end

`topP := topProgC P7C hm7 P9C hm9` with
* `P7C` from `WP.W7k2.Concrete`: the concrete table builder `buildProg BIC`, all twenty slots concrete
  (W3, W5 Toom-3, W6a, colRecip, W7k1 π/ln, W7k3 stdChar, W7k3t tap, W7k3 c0c1);
* `P9C` from `WP.F9.Top`: all stages concrete with no placeholders (columns = `WP.W9f.Concrete.progColsC`).

Every input of the execution test has a leaf-only schedule (under the stop rule `2^K0 ≤ 4p²`).
The machine is run with the indexed table runner with register normalizer `WP.F9.runTabledIxR`
(sound: `runTabledIxR_sound`), normalizing the pipeline's registers with `nr9` (the identity, `nr9_eq`).
`accepted a b S`: `encodeNat (a * b)` on the output stack and every other stack empty.
-/

namespace IntMulTM.Exec.TopRun

open TMFw TMFw.Contracts WP.Top IntMulTM

/-- `P9C` fits the Top's pipeline cap. -/
theorem hm9 : WP.F9.Top.m9 ≤ 64 := WP.F9.Top.hm9

/-- The concrete final program (test variant). -/
def topP := TopC.topProgC WP.W7k2.Concrete.P7C WP.W7k2.Concrete.hm7 WP.F9.Top.P9C hm9

/-- Its initial registers. -/
def σ0 := TopC.σ0C WP.W7k2.Concrete.r7 WP.F9.Top.r9

/-- Stack index for the runner: `input ↦ 0`, `output ↦ 1`, `work g ↦ 2 + position of g in allGW`. -/
def ix : StackId GW → ℕ
  | .input => 0
  | .output => 1
  | .work g => 2 + allGW.idxOf g

/-- Register normalizer of the final machine: `nr9` on the pipeline's register component (W9f's column
registers rebuilt from data), the identity elsewhere. -/
def nrTop (v : TopRegs InputStageRun.σIn WP.W7k2.Concrete.R7 WP.TapeConv.CR WP.F9.Top.R9) :
    TopRegs InputStageRun.σIn WP.W7k2.Concrete.R7 WP.TapeConv.CR WP.F9.Top.R9 :=
  (v.1, v.2.1, v.2.2.1, WP.F9.Top.nr9 v.2.2.2.1, v.2.2.2.2)

theorem nrTop_eq (v : TopRegs InputStageRun.σIn WP.W7k2.Concrete.R7 WP.TapeConv.CR WP.F9.Top.R9) :
    nrTop v = v := by
  simp [nrTop, WP.F9.Top.nr9_eq]

/-- Run on `(a, b)`. -/
def runTopIx (a b fuel : ℕ) : Option (ℕ × ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)) :=
  WP.F9.runTabledIxR topP σ0 InputStageRun.keys ix nrTop
    ⟨σ0, inputStk (W := GW) (encNatPair.encode (a, b))⟩ fuel

/-- The acceptance oracle on a finished run. -/
def accepted (a b : ℕ) (S : ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)) : Bool :=
  S .output == Computability.encodeNat (a * b) && (S .input).isEmpty &&
    allGW.all fun w => (S (.work w)).isEmpty

#guard WP.F9.ixOK InputStageRun.keys ix

end IntMulTM.Exec.TopRun
