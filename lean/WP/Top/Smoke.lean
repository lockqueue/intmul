import WP.Top.Output
import WP.Top.Glue
import IntMulTM.Framework.Test.EndToEnd

/-!
# WP.Top.Smoke — run the compiled output stage and the glue, and compare step counts

Only these parts of `topProg` can run today:
* the input stage needs W3/W6a programs;
* tables, conversion and W9 are contracts.

**Output stage.** The product `natSyms v` is loaded on `oa`, the input stack of the compiled machine;
every other stack is empty. The machine must halt with `encodeNat v` on the output stack. The proved
bound is `outCost (bitLen v) J + 1` (one halting step), with `J = bitLen v` symbols to clear.

**Glue.** The machine (stacks `GW`, input stack `pb`) runs `pb`/`pk`/`pK0` loads, then `glueProg`.
Its output stack is `c 0`.
-/

namespace WP.Top.Smoke

open Computability TMFw TMFw.Lib TMFw.Test TMFw.Contracts WP.Top IntMulTM

/-- The compiled output stage: input stack `oa`, output stack `output`. -/
def outTM : Turing.FinTM2 :=
  toFinTM2 (K := StackId GW) (Γ := StackId.Γ encNatPair.Γ) (.work .oa) .output outStage none

/-- `(machine run, proved bound + 1)` for the product `v`. -/
def runOut (v : ℕ) : Option (ℕ × List Bool) × ℕ :=
  (runTM outTM (natSyms v) 5000, outCost (bitLen v) (bitLen v) + 1)

/-- Expected outputs: `encodeNat v`. -/
def expectOut (v : ℕ) : List Bool := encodeNat v

-- v = 0, 1, 6, 255, 1000: `(some (steps, output), bound)`, then the expected output.
#eval [runOut 0, runOut 1, runOut 6, runOut 255, runOut 1000]
#eval [expectOut 0, expectOut 1, expectOut 6, expectOut 255, expectOut 1000]

/-- Glue test harness: copy the input (`natSyms b`) to `pb`, and fixed `k`, `K0` to `pk`, `pK0`,
then run the glue. -/
def glueTest : SProg GW :=
  .seq (copyBlock .pb .pk (.xs 1)) (.seq (copyBlock .pb .pK0 (.xs 1)) glueProg)

/-- Compiled glue harness: input stack `pb`, output stack `c 0`. -/
def glueTM : Turing.FinTM2 :=
  toFinTM2 (K := GW) (Γ := fun _ : GW => Sym) .pb (.c 0) glueTest none

-- With `b = k = K0 = 5`, `c 0` must be `hdrSyms [5, 5, 5, 5]`:
-- `natSyms 5 ++ [mark]`, four times.
#eval runTM glueTM (natSyms 5) 2000

end WP.Top.Smoke
