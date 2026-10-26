import WP.W3e.Shift
import IntMulTM.Framework.Test.EndToEnd

/-!
# WP.W3e.Smoke — the compiled shift machines on small inputs

`runShift p input fuel` runs `toFinTM2 X0 X0 p none`, whose machine is `machine p σ0` (the
framework compiler, Mathlib's `TM2.step`), from `input` on the operand stack. By `machine_run`, an
evaluation of cost `t` takes `t + 1` machine steps.

* `shlProg k`: exact cost `k + 3` for `a ≠ 0` and `3` for `a = 0`; budget `3·(k+1)`.
* `shrProg k`: exact cost `3k + 1`; budget `3·(k+1)`.

Each input is `natSyms a` followed by a `sep` terminator, which must be left in place. The checks
compare the output with `natSyms (a·2^k)` / `natSyms (a / 2^k)` and the step count with the budget.
-/

namespace WP.W3e

open TMFw TMFw.Lib TMFw.Test TMFw.Contracts Turing

/-- Run the compiled program on the operand stack: `some (steps, final stack)` if it halts. -/
def runShift (p : SProg (Loc 1 0)) (input : List Sym) (fuel : ℕ) : Option (ℕ × List Sym) :=
  runTM (toFinTM2 (Γ := fun _ : Loc 1 0 => Sym) X0 X0 p (none : Option Sym)) input fuel

/-- `shlProg k` on `a`: correct output within the proved budget (plus the halting step). -/
def shlOK (k a : ℕ) : Bool :=
  match runShift (shlProg k) (natSyms a ++ [.sep]) (3 * (k + 1) + 2) with
  | some (n, out) => decide (out = natSyms (a * 2 ^ k) ++ [.sep]) && decide (n ≤ 3 * (k + 1) + 1)
  | none => false

/-- `shrProg k` on `a`: correct output within the proved budget (plus the halting step). -/
def shrOK (k a : ℕ) : Bool :=
  match runShift (shrProg k) (natSyms a ++ [.sep]) (3 * (k + 1) + 2) with
  | some (n, out) => decide (out = natSyms (a / 2 ^ k) ++ [.sep]) && decide (n ≤ 3 * (k + 1) + 1)
  | none => false

#guard (List.range 5).all fun k => (List.range 33).all fun a => shlOK k a
#guard (List.range 7).all fun k => (List.range 70).all fun a => shrOK k a

-- exact step counts (`cost + 1`)
-- `5·2^3 = 40`: cost `3 + 3`
#guard runShift (shlProg 3) (natSyms 5 ++ [.sep]) 100 = some (7, natSyms 40 ++ [.sep])
-- `0·2^3 = 0` stays canonical (no zero bits pushed): cost 3
#guard runShift (shlProg 3) (natSyms 0 ++ [.sep]) 100 = some (4, [.sep])
#guard runShift (shlProg 0) (natSyms 6 ++ [.sep]) 100 = some (4, natSyms 6 ++ [.sep])
-- `13 / 2^3 = 1`: cost `3·3 + 1`
#guard runShift (shrProg 3) (natSyms 13 ++ [.sep]) 100 = some (11, natSyms 1 ++ [.sep])
-- `5 / 2^6 = 0`: the pops stop at the terminator, which stays in place
#guard runShift (shrProg 6) (natSyms 5 ++ [.sep]) 100 = some (20, [.sep])
#guard runShift (shrProg 2) [] 100 = some (8, [])

-- `(k, a, steps, budget + 1)`
#eval [(3, 5), (3, 0), (6, 1)].map fun (k, a) =>
  (k, a, (runShift (shlProg k) (natSyms a ++ [Sym.sep]) 100).map Prod.fst, 3 * (k + 1) + 1)
#eval [(3, 13), (6, 5), (0, 9)].map fun (k, a) =>
  (k, a, (runShift (shrProg k) (natSyms a ++ [Sym.sep]) 100).map Prod.fst, 3 * (k + 1) + 1)

end WP.W3e
