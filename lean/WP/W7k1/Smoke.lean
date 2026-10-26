import WP.W7k1.Isqrt
import IntMulTM.Framework.Test.EndToEnd

/-!
# WP.W7k1.Smoke — the compiled `W7_isqrt` machine on small inputs

`isqTM` is the kernel compiled to a Mathlib `FinTM2` (`toFinTM2`): input `a` on `kA`, every other
stack empty, output read from `kZ`. `smokeOK a` runs it with the proved step budget plus one
(`machine_run`: the compiled machine takes `t + 1` steps for an evaluation of cost `t`) and checks
the output stack is exactly `natSyms (Nat.sqrt a)` and the step count is within
`200·(|a|² + 1) + 1`.

The harness keeps stacks as nested `Function.update` closures, so a run of `n` steps costs `O(n²)`
in the interpreter; the checks stay at inputs of at most 12 bits.
-/

namespace WP.W7k1

open TMFw TMFw.Test TMFw.Contracts Turing

/-- The compiled kernel. -/
def isqTM : FinTM2 :=
  toFinTM2 (Γ := fun _ : IK => Sym) kA kZ isqrtProg ((none, none, false) : IReg)

/-- Run the compiled kernel on `a`: `some (steps, destination stack)` if it halts within `fuel`. -/
def runIsqrt (a fuel : ℕ) : Option (ℕ × List Sym) := runTM isqTM (natSyms a) fuel

/-- The proved step budget of the compiled machine (`isqrtProg_eval` plus the halting step). -/
def isqBudget (a : ℕ) : ℕ := 200 * (bitLen a * bitLen a + 1) + 1

/-- Output `natSyms ⌊√a⌋`, within the proved budget. -/
def smokeOK (a : ℕ) : Bool :=
  match runIsqrt a (isqBudget a + 1) with
  | some (n, out) => decide (out = natSyms (Nat.sqrt a)) && decide (n ≤ isqBudget a)
  | none => false

#guard (List.range 64).all smokeOK
#guard [100, 255, 256, 1000, 1023, 1024, 4095].all smokeOK

-- `(a, actual steps, proved budget)`
#eval [0, 1, 2, 3, 4, 15, 16, 17, 255, 1000, 4095].map fun a =>
  (a, (runIsqrt a (isqBudget a + 1)).map Prod.fst, isqBudget a)

end WP.W7k1
