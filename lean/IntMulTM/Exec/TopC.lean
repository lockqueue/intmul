import IntMulTM.Exec.InputStageRun
import IntMulTM.Exec.ConvStageRun

/-!
# `topProgC`: the concrete final machine, waiting for the table builder and the W9 pipeline

`WP.Top.topProg` is the program of the headline theorem, a plain `def` parametrized by its stage programs.
`topProgC P7 hm7 P9 hm9` instantiates every stage that is concrete today:
* input: `InputStageRun.PinC` (copy-in + W0m work program with the verified W3 adder and W6a divider);
* tape conversion: `ConvStageRun.PcC` (`WP.TapeConv.convP`, as `TapeConv_of_contract` places it);
* glue and output: `WP.Top.glueStage`, `WP.Top.outStage` (built into `topProg`).
The table builder `P7` (`WP.W7k2`) and the level-synchronous pipeline `P9` (`WP.F9`) are the
two remaining parameters.

`okTop` is the end-to-end oracle of the acceptance statement: started from
`inputStk (encNatPair.encode (a, b))`, the machine halts with `encodeNat (a * b)` on the output stack and every
other stack empty (`outputStk`), within `fuel` steps.
-/

namespace IntMulTM.Exec.TopC

open TMFw TMFw.Contracts WP.Top IntMulTM

variable {R7 R9 : Type} {m7 m9 : ℕ}

/-- The concrete final program, given the table builder and the pipeline. -/
def topProgC (P7 : Prog (Loc 4 m7) (fun _ => Sym) R7) (hm7 : m7 ≤ 32)
    (P9 : Prog (W9.BLoc m9) (fun _ => Sym) R9) (hm9 : m9 ≤ 64) :
    Prog (StackId GW) (StackId.Γ encNatPair.Γ) (TopRegs InputStageRun.σIn R7 WP.TapeConv.CR R9) :=
  topProg InputStageRun.PinC P7 hm7 ConvStageRun.PcC (by decide) P9 hm9

/-- Its initial registers. -/
def σ0C (r7 : R7) (r9 : R9) : TopRegs InputStageRun.σIn R7 WP.TapeConv.CR R9 :=
  (InputStageRun.σIn0, r7, (none, 0), r9, none)

/-- Run the final machine on `(a, b)`. -/
def runTop (P7 : Prog (Loc 4 m7) (fun _ => Sym) R7) (hm7 : m7 ≤ 32) (r7 : R7)
    (P9 : Prog (W9.BLoc m9) (fun _ => Sym) R9) (hm9 : m9 ≤ 64) (r9 : R9) (a b fuel : ℕ) :
    Option (ℕ × ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)) :=
  runMachine (topProgC P7 hm7 P9 hm9) (σ0C r7 r9) InputStageRun.keys
    ⟨σ0C r7 r9, inputStk (W := GW) (encNatPair.encode (a, b))⟩ fuel

/-- The acceptance oracle: output `encodeNat (a * b)`, every other stack empty. -/
def okTop (P7 : Prog (Loc 4 m7) (fun _ => Sym) R7) (hm7 : m7 ≤ 32) (r7 : R7)
    (P9 : Prog (W9.BLoc m9) (fun _ => Sym) R9) (hm9 : m9 ≤ 64) (r9 : R9) (a b fuel : ℕ) : Bool :=
  match runTop P7 hm7 r7 P9 hm9 r9 a b fuel with
  | some (_, S) =>
    S .output == Computability.encodeNat (a * b) && (S .input).isEmpty &&
      allGW.all fun w => (S (.work w)).isEmpty
  | none => false

end IntMulTM.Exec.TopC
