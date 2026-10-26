import IntMulTM.Exec.Runner
import WP.W7k1.Isqrt
import IntMulTM.Framework.Test.EndToEnd

/-!
# Execution prototype 1: `W7_isqrt` (W7k1) through `machine p σ0`

The kernel `isqrtProg` is run with `IntMulTM.Exec.runMachine` (no `toFinTM2`). Checks:
1. the runner agrees exactly (steps and output) with the framework's `toFinTM2` harness (`runIsqrt`,
   the same compiled machine) on small inputs;
2. on inputs beyond the reach of that `O(n²)` harness, the output is `natSyms ⌊√a⌋` and the step count is
   within the proved budget `isqBudget a`.
-/

namespace IntMulTM.Exec.IsqrtRun

open TMFw TMFw.Test TMFw.Contracts WP.W7k1 Turing

/-! Copies of `WP.W7k1.Smoke`'s definitions (not imported: that module runs its own smoke evals). -/

/-- The compiled kernel (baseline). -/
def isqTM : FinTM2 :=
  toFinTM2 (Γ := fun _ : IK => Sym) kA kZ isqrtProg ((none, none, false) : IReg)

/-- The `toFinTM2` harness run (baseline). -/
def runIsqrt (a fuel : ℕ) : Option (ℕ × List Sym) := runTM isqTM (natSyms a) fuel

/-- The proved step budget of the compiled machine (`isqrtProg_eval` plus the halting step). -/
def isqBudget (a : ℕ) : ℕ := 200 * (bitLen a * bitLen a + 1) + 1

/-- All stacks of the kernel. -/
def keys : List IK := (List.finRange 2).map Sum.inl ++ (List.finRange 6).map Sum.inr

/-- Run `machine isqrtProg σ0` on `natSyms a`: `(steps, destination stack)`. -/
def run (a fuel : ℕ) : Option (ℕ × List Sym) :=
  (runMachine isqrtProg ((none, none, false) : IReg) keys
      ⟨((none, none, false) : IReg), stkOnly kA (natSyms a)⟩ fuel).map fun r => (r.1, r.2 kZ)

/-- Output and step budget, from the direct runner. -/
def ok (a : ℕ) : Bool :=
  match run a (isqBudget a + 1) with
  | some (n, out) => decide (out = natSyms (Nat.sqrt a)) && decide (n ≤ isqBudget a)
  | none => false

#guard complete keys

-- 1. Same machine, same steps and output as the `toFinTM2` harness.
#guard [0, 1, 2, 3, 15, 16, 17, 255].all fun a =>
  run a (isqBudget a + 1) == runIsqrt a (isqBudget a + 1)

-- 2. Larger inputs: correct output within the proved budget.
#guard [4095, 65535, 2 ^ 20 + 3, 2 ^ 64 - 1, 2 ^ 100 + 12345].all ok

-- `(a, steps, budget)`
#eval [0, 255, 4095, 65535, 2 ^ 20 + 3, 2 ^ 64 - 1, 2 ^ 100 + 12345].map fun a =>
  (a, (run a (isqBudget a + 1)).map Prod.fst, isqBudget a)

end IntMulTM.Exec.IsqrtRun
