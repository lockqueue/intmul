import IntMulTM.Exec.Runner
import WP.Inst.W3
import WP.W6a.DivModProg
import WP.W0m.WorkMain

/-!
# Execution prototype 3: the full W0m work program (phases A–H) with the verified adder and divider

`workP` is `WP.W0m.workProg` instantiated with `WP.Inst.addNat.prog` (W3 adder) and
`WP.W6a.divModProg WP.Inst.subNat.prog` (W6a long division over the W3 subtractor). It is run with
`IntMulTM.Exec.runMachine` from `S0 a b` (the copied-in input on `inp`). Check: every work stack ends exactly
as `outW a b` says (operands, `n`, `b`, `K`, `k0`, `lf`, `p0`; all other stacks empty), which is the
post-state of `workProg_runs`.
-/

namespace IntMulTM.Exec.W0mFullRun

open TMFw TMFw.Lib TMFw.Contracts WP.W0m

/-- Adder registers. -/
abbrev Ra : Type := WP.Inst.addNat.R

/-- Divider registers. -/
abbrev Rd : Type := WP.W6a.DReg WP.Inst.subNat.R

/-- The W6a divider over the W3 subtractor. -/
def divP : Prog (Loc 4 3) (fun _ => Sym) Rd := WP.W6a.divModProg WP.Inst.subNat.prog

/-- The full work program. -/
def workP : WProg Ra Rd := workProg WP.Inst.addNat.prog (by decide) divP (by decide)

/-- Initial registers. -/
def regs0 : Regs Ra Rd :=
  (none, (none, none, .eq), WP.Inst.addNat.r0, (none, false, (none, none, .eq), WP.Inst.subNat.r0))

/-- All stacks of the input stage. -/
def keys : List Stk :=
  [.inp, .oa, .ob, .la, .lb, .nn, .bb, .kk, .k0, .lf, .p0, .rr, .t1, .t2, .t3, .c4, .tm, .ct, .cs,
    .x0, .x1] ++ (List.finRange 6).map Stk.s

/-- Run `machine workP regs0` from `S0 a b`. -/
def run (a b fuel : ℕ) : Option (ℕ × (Stk → List Sym)) :=
  runMachine workP regs0 keys ⟨regs0, S0 a b⟩ fuel

/-- Step budget for the runs (generous: the proved bound with `C_add = 20`, `C_div = 110`). -/
def fuel (a b : ℕ) : ℕ := 4 * workCost 20 110 a b + 100

/-- All work stacks as specified by `outW`. -/
def ok (a b : ℕ) : Bool :=
  match run a b (fuel a b) with
  | some (_, S) => keys.all fun k => S k == outW a b k
  | none => false

#guard complete keys

#guard [(0, 0), (1, 1), (3, 5), (255, 255), (1000, 7)].all fun (a, b) => ok a b

#guard [(2 ^ 64 - 1, 2 ^ 63 + 5), (2 ^ 128 + 7, 3), (2 ^ 191 + 2 ^ 100, 2 ^ 150 - 1)].all
  fun (a, b) => ok a b

-- `(a, b, steps, workCost 20 110 a b)`
#eval [(0, 0), (3, 5), (255, 255), (2 ^ 64 - 1, 2 ^ 63 + 5), (2 ^ 191 + 2 ^ 100, 2 ^ 150 - 1)].map
  fun (a, b) => (a, b, (run a b (fuel a b)).map Prod.fst, workCost 20 110 a b)

end IntMulTM.Exec.W0mFullRun
