import IntMulTM.Exec.Runner
import WP.W0m.WorkMain
import IntMulTM.Framework.Test.EndToEnd

/-!
# Execution prototype 2: the W0m input stage, phases A–D, through `machine p σ0`

Phases E and H of the input stage call the W3 adder and the W6a divider, whose W3 programs are not
yet available as definitions, so only the prefix A–D (parse, bit lengths, `n`, `b`) is concrete.
Checks:
1. the direct runner agrees exactly (steps and outputs `nn`, `bb`) with the `toFinTM2` harness
   (`runPrefix`, the same compiled machine) on the W0m smoke inputs;
2. on 2–3 word operands: `nn = max 1 (max |a| |b|)` (`phC_runs`), `bb = sB nn` (`phD_runs`), and the
   step count is within the proved `prefixBound`.
-/

namespace IntMulTM.Exec.W0mRun

open TMFw TMFw.Test TMFw.Lib TMFw.Contracts WP.W0m

/-! Copies of `WP.W0m.Smoke`'s definitions (not imported: that module runs its own smoke evals). -/

/-- Phases A–D. -/
def prefixProg : WProg Unit Unit := .seq phA (.seq phB (.seq phC phD))

/-- The initial registers. -/
def regs0 : Regs Unit Unit := (none, (none, none, .eq), (), ())

/-- The `toFinTM2` machine with output stack `nn` (baseline). -/
def prefixTMn : Turing.FinTM2 := toFinTM2 (Γ := fun _ : Stk => Sym) .inp .nn prefixProg regs0

/-- The `toFinTM2` machine with output stack `bb` (baseline). -/
def prefixTMb : Turing.FinTM2 := toFinTM2 (Γ := fun _ : Stk => Sym) .inp .bb prefixProg regs0

/-- Proved bound for phases A–D, plus one halting step. -/
def prefixBound (a b : ℕ) : ℕ :=
  (3 * bitLen a + 3 * bitLen b + 4) + (24 * bitLen a + 24 * bitLen b + 20) + (40 * lam a b + 50) +
    (40 * lam a b + 30) + 1

/-- The baseline: `toFinTM2` harness runs. -/
def runPrefix (a b : ℕ) : Option (ℕ × List Sym) × Option (ℕ × List Sym) :=
  (runTM prefixTMn (inputSyms a b) 20000, runTM prefixTMb (inputSyms a b) 20000)

/-- All stacks of the input stage. -/
def keys : List Stk :=
  [.inp, .oa, .ob, .la, .lb, .nn, .bb, .kk, .k0, .lf, .p0, .rr, .t1, .t2, .t3, .c4, .tm, .ct, .cs,
    .x0, .x1] ++ (List.finRange 6).map Stk.s

/-- Run `machine prefixProg regs0` on `inputSyms a b`: `(steps, nn, bb)`. -/
def run (a b fuel : ℕ) : Option (ℕ × List Sym × List Sym) :=
  (runMachine prefixProg regs0 keys ⟨regs0, stkOnly .inp (inputSyms a b)⟩ fuel).map fun r =>
    (r.1, r.2 .nn, r.2 .bb)

/-- The expected `n`. -/
def nExp (a b : ℕ) : ℕ := max 1 (max (bitLen a) (bitLen b))

/-- Outputs as specified, within the proved bound. -/
def ok (a b : ℕ) : Bool :=
  match run a b (prefixBound a b + 1) with
  | some (t, nn, bb) =>
    decide (nn = natSyms (nExp a b)) && decide (bb = natSyms (sB (nExp a b))) &&
      decide (t ≤ prefixBound a b)
  | none => false

#guard complete keys

-- 1. Same machine as the `toFinTM2` harness: identical steps and outputs.
#guard [(5, 3), (1000, 7), (0, 0)].all fun (a, b) =>
  ((run a b 20000).map fun r => (r.1, r.2.1)) == (runPrefix a b).1 &&
    ((run a b 20000).map fun r => (r.1, r.2.2)) == (runPrefix a b).2

-- 2. Two- and three-word operands.
#guard [(2 ^ 64 - 1, 2 ^ 63 + 5), (2 ^ 128 + 7, 3), (2 ^ 191 + 2 ^ 100, 2 ^ 150 - 1)].all
  fun (a, b) => ok a b

-- `(steps, bound)`
#eval [(5, 3), (2 ^ 64 - 1, 2 ^ 63 + 5), (2 ^ 191 + 2 ^ 100, 2 ^ 150 - 1)].map fun (a, b) =>
  ((run a b (prefixBound a b + 1)).map Prod.fst, prefixBound a b)

end IntMulTM.Exec.W0mRun
