import IntMulTM.Exec.W0mFullRun
import WP.Top.Embed

/-!
# Execution prototype 4: the production input stage (first stage of `topProgC`)

`PinC := WP.W0m.inputStage WP.Top.ι0 workP` is the input stage exactly as the final machine uses it: on the
78-stack production layout `StackId GW`, copy-in from the `PairSym` input stack, then the full W0m work
program (verified W3 adder, W6a divider over the W3 subtractor), with W0m's stacks placed by `ι0`. It is run
with `runMachine` from `inputStk (encNatPair.encode (a, b))`, the production initial state.

Check: the final state is the exact input-stage state of `WP.Top.afterIn_eq`: input and output stacks empty,
and every work stack `w` equal to `prmState (operandBits a b) a b w`.
-/

namespace IntMulTM.Exec.InputStageRun

open TMFw TMFw.Lib TMFw.Contracts WP.Top IntMulTM

/-- Registers of the input stage. -/
abbrev σIn : Type := Option Sym × WP.W0m.Regs W0mFullRun.Ra W0mFullRun.Rd

/-- The production input stage. -/
def PinC : Prog (StackId GW) (StackId.Γ encNatPair.Γ) σIn :=
  WP.W0m.inputStage ι0 W0mFullRun.workP

/-- Initial registers. -/
def σIn0 : σIn := (none, W0mFullRun.regs0)

/-- All 78 stacks of the production layout. -/
def keys : List (StackId GW) := [.input, .output] ++ allGW.map StackId.work

/-- Run `machine PinC σIn0` from the production initial state. -/
def run (a b fuel : ℕ) : Option (ℕ × ∀ k : StackId GW, List (StackId.Γ encNatPair.Γ k)) :=
  runMachine PinC σIn0 keys ⟨σIn0, inputStk (W := GW) (encNatPair.encode (a, b))⟩ fuel

/-- Generous step budget: copy-in `3L + 2` plus four times the work bound. -/
def fuel (a b : ℕ) : ℕ := 3 * (bitLen a + bitLen b + 1) + 4 * WP.W0m.workCost 20 110 a b + 200

/-- The final state is `afterIn_eq`'s input-stage state. -/
def ok (a b : ℕ) : Bool :=
  match run a b (fuel a b) with
  | some (_, S) =>
    (S .input).isEmpty && (S .output).isEmpty &&
      allGW.all fun w => S (.work w) == prmState (operandBits a b) a b w
  | none => false

#guard complete keys

#guard [(0, 0), (1, 1), (3, 5), (255, 255)].all fun (a, b) => ok a b

#guard [(2 ^ 64 - 1, 2 ^ 63 + 5), (2 ^ 191 + 2 ^ 100, 2 ^ 150 - 1)].all fun (a, b) => ok a b

-- `(a, b, steps, 3L + 2 + workCost 20 110 a b)`
#eval [(0, 0), (3, 5), (255, 255), (2 ^ 64 - 1, 2 ^ 63 + 5), (2 ^ 191 + 2 ^ 100, 2 ^ 150 - 1)].map
  fun (a, b) => (a, b, (run a b (fuel a b)).map Prod.fst,
    3 * (bitLen a + bitLen b + 1) + 2 + WP.W0m.workCost 20 110 a b)

end IntMulTM.Exec.InputStageRun
