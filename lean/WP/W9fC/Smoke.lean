import WP.W9fC.Prims
import IntMulTM.Framework.Test.EndToEnd

/-!
# WP.W9fC.Smoke — the driver's generic stack programs on the compiled Mathlib machine

Each run returns `some (steps, output stack)`. The compiled machine takes the proved `Eval` cost
plus one final halting step (`machine_run`): `xferAll_eval` `3·|L| + 2`, `dropThrough_eval`
`2·|L| + 2`, `rewindTo_eval` (WP.W9comp.Kit) `3·|L| + 2`. The full driver `colsProg` is
parametric in the column solver, so it has no closed instance to run here.
-/

namespace WP.W9fC.Smoke

open Turing TMFw TMFw.Lib TMFw.Test WP.W9comp WP.W9fC

/-- `xferAll 0 1`: input on stack `0`, output stack `1`. -/
def xferTM : FinTM2 :=
  toFinTM2 (Γ := fun _ : Fin 2 => Sym) 0 1 (xferAll (0 : Fin 2) 1) (none : Option Sym)

def runXfer (l : List Sym) : Option (ℕ × List Sym) := runTM xferTM l 200

/-- `dropThrough 0 sep`: input and output on stack `0`. -/
def dropTM : FinTM2 :=
  toFinTM2 (Γ := fun _ : Fin 2 => Sym) 0 0 (dropThrough (0 : Fin 2) Sym.sep) (none : Option Sym)

def runDrop (l : List Sym) : Option (ℕ × List Sym) := runTM dropTM l 200

/-- `rewindTo 0 1 guard`: input on stack `0`, output stack `1`. -/
def rewTM : FinTM2 :=
  toFinTM2 (Γ := fun _ : Fin 2 => Sym) 0 1 (rewindTo (0 : Fin 2) 1 (Sym.tag 7)) (none : Option Sym)

def runRew (l : List Sym) : Option (ℕ × List Sym) := runTM rewTM l 200

-- xferAll: |L| = 3 ↦ 3·3 + 2 + 1 = 12 steps, output = reversed input; |L| = 0 ↦ 3 steps.
#eval (runXfer [Sym.bit true, Sym.sep2, Sym.mark], runXfer [])
-- dropThrough: L = [1, 0] then `sep` ↦ 2·2 + 2 + 1 = 7 steps, stack 0 = [mark].
#eval runDrop [Sym.bit true, Sym.bit false, Sym.sep, Sym.mark]
-- rewindTo: L = [pos, 1, sep] then the guard ↦ 3·3 + 2 + 1 = 12 steps, stack 1 = L reversed.
#eval runRew [Sym.pos, Sym.bit true, Sym.sep, Sym.tag 7, Sym.mark]

end WP.W9fC.Smoke
