import WP.W0m.WorkMain
import IntMulTM.Framework.Test.EndToEnd

/-!
# WP.W0m.Smoke — run the compiled input-stage prefix (phases A–D) and compare step counts

Phases A–D (parse, bit lengths, `n`, `b`) use only proved macros, so their compiled `FinTM2` can be
run with the framework's harness. Phases E and H call the hypothesized W3/W6a programs. They become
runnable once those WPs land.

The machine's input stack is `inp`, loaded with `inputSyms a b` (the layout right after copy-in).
Its output stack is `nn` or `bb`. The steps should equal the source cost plus one halting step;
`prefixBound` is the proved bound from `phA_runs … phD_runs`.
-/

namespace WP.W0m.Smoke

open TMFw TMFw.Test TMFw.Lib TMFw.Contracts WP.W0m

/-- Phases A–D. -/
def prefixProg : WProg Unit Unit := .seq phA (.seq phB (.seq phC phD))

/-- The initial registers. -/
def regs0 : Regs Unit Unit := (none, (none, none, .eq), (), ())

/-- Compiled prefix with output stack `nn`. -/
def prefixTMn : Turing.FinTM2 := toFinTM2 (Γ := fun _ : Stk => Sym) .inp .nn prefixProg regs0

/-- Compiled prefix with output stack `bb`. -/
def prefixTMb : Turing.FinTM2 := toFinTM2 (Γ := fun _ : Stk => Sym) .inp .bb prefixProg regs0

/-- Proved bound for phases A–D, plus one halting step. -/
def prefixBound (a b : ℕ) : ℕ :=
  (3 * bitLen a + 3 * bitLen b + 4) + (24 * bitLen a + 24 * bitLen b + 20) + (40 * lam a b + 50) +
    (40 * lam a b + 30) + 1

/-- `(steps, nn, bb, bound)`. -/
def runPrefix (a b : ℕ) : Option (ℕ × List Sym) × Option (ℕ × List Sym) × ℕ :=
  (runTM prefixTMn (inputSyms a b) 20000, runTM prefixTMb (inputSyms a b) 20000, prefixBound a b)

-- (5, 3): n = 3 = [1,1], b = max 1 (log₂ 3) = 1 = [1].
-- (1000, 7): n = 10 = [0,1,0,1], b = log₂ 10 = 3 = [1,1].
-- (0, 0): n = 1 = [1], b = 1.
#eval [runPrefix 5 3, runPrefix 1000 7, runPrefix 0 0, runPrefix 65535 1]

end WP.W0m.Smoke
