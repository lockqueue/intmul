import WP.W9mp.Prog
import IntMulTM.Framework.Sim

/-!
# WP.W9mp.Smoke — run the compiled header glue and the composite (`#eval`)

* `rowP0 b K0`: run `pushP0` alone on `C0 = hdrSyms [b, K0, 1, 1] ++ [sep]`, with arbitrary old
  content on `C1` and on the three scratch stacks (it contains `symGuard` and `mark`). Checks that
  `C1 = hdrSyms [2b + 2K0 + 6] ++ old` and every other stack is restored, and reports the step
  count next to the proved bound `100·(b+K0+1)·(K0+1)` (+1 for `machine_run`).
* `rowMult b K0 k1 k2`: run the composite `multProg` with the five stage programs replaced by an
  **unverified test stub** `noop` (one register load, used by no theorem; every stage sits at scratch
  count `0` inside a composite with `3` scratch stacks, so `emb` is exercised). The glue must restore
  every stack exactly (`C1` included). The step count is compared with
  `6 + (7·bitLen b + 8) + (2·bitLen b + 2) + 100·(b+K0+1)·(K0+1) + (2·bitLen p0 + 2) + 1`.
-/

namespace WP.W9mp.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing
open WP.W9comp WP.W9mp

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. On halting,
return the number of steps and the final user stacks (copied from `WP.W9comp.Smoke`). -/
def runProg {K : Type} [DecidableEq K] {σ : Type} (p : Prog K (fun _ => Sym) σ) (σ0 : σ)
    (S : K → List Sym) (fuel : ℕ) : Option (ℕ × (K → List Sym)) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk S []⟩
where
  /-- the step loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)) → Option (ℕ × (K → List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, fun k => c.stk (some k))
      | some c' => go fuel (n + 1) c'

/-- Test stub (unverified): one register load. -/
def noop : SProg (BLoc 0) := .load id

theorem z3 : 0 ≤ 3 := Nat.zero_le 3

theorem h33 : 3 ≤ 3 := le_refl 3

#assert_std_axioms z3 h33

/-- The composite with stub stages. -/
def multStub : Prog (BLoc 3) (fun _ => Sym)
    (MRegs (Option Sym) (Option Sym) (Option Sym) (Option Sym) (Option Sym)) :=
  multProg z3 z3 z3 z3 z3 h33 noop noop noop noop noop

/-- Old content of `C1` and of the scratch stacks (contains `symGuard` and `mark`). -/
def c1old : List Sym := [Sym.mark, Sym.bit true, symGuard, Sym.sep]

def scr : List Sym := [symGuard, Sym.mark, Sym.bit false]

def init (b K0 k1 k2 : ℕ) : BLoc 3 → List Sym := fun k =>
  if k = .inl .C0 then hdrSyms [b, K0, k1, k2] ++ [Sym.sep]
  else if k = .inl .C1 then c1old
  else if k = .inl .S then [symLevel]
  else if k = .inl .OA then [Sym.bit true, Sym.mark]
  else if k = .inr 0 ∨ k = .inr 1 ∨ k = .inr 2 then scr
  else []

def allLB : List LB := [.S, .W0, .TL, .TR, .RET, .RQ, .C0, .C1, .C2, .C3, .OA, .OB]

/-- All 15 stacks agree. -/
def same (S S' : BLoc 3 → List Sym) : Bool :=
  allLB.all (fun k => S (.inl k) == S' (.inl k)) &&
    [(0 : Fin 3), 1, 2].all (fun j => S (.inr j) == S' (.inr j))

/-- `(b, K0, stacks as specified, steps, proved bound + 1)` for `pushP0`. -/
def rowP0 (b K0 : ℕ) : ℕ × ℕ × Bool × ℕ × ℕ :=
  let S0 := init b K0 1 1
  let bound := 100 * (b + K0 + 1) * (K0 + 1) + 1
  match runProg (pushP0 (K := BLoc 3) (.inl .C0) (.inl .C1) (.inr 0) (.inr 1) (.inr 2)) none S0
      200000 with
  | none => (b, K0, false, 0, bound)
  | some (steps, S) =>
    (b, K0, same S (Function.update S0 (.inl .C1) (hdrSyms [2 * b + 2 * K0 + 6] ++ c1old)),
      steps, bound)

/-- `(b, K0, all stacks restored, steps, proved bound + 1)` for the stub composite. -/
def rowMult (b K0 k1 k2 : ℕ) : ℕ × ℕ × Bool × ℕ × ℕ :=
  let S0 := init b K0 k1 k2
  let bound := 6 + (7 * bitLen b + 8) + (2 * bitLen b + 2) + 100 * (b + K0 + 1) * (K0 + 1) +
    (2 * bitLen (2 * b + 2 * K0 + 6) + 2) + 1
  match runProg multStub (none, none, none, none, none, none) S0 200000 with
  | none => (b, K0, false, 0, bound)
  | some (steps, S) => (b, K0, same S S0, steps, bound)

-- `pushP0`: C1 gets exactly `hdrSyms [2b+2K0+6]`, all else restored; steps within the bound.
#eval [rowP0 0 0, rowP0 1 0, rowP0 0 1, rowP0 5 3, rowP0 13 7, rowP0 64 10]

-- Stub composite: every stack restored (C1 included); steps within the bound.
#eval [rowMult 0 0 1 1, rowMult 5 3 2 2, rowMult 13 7 3 4, rowMult 64 10 5 6]

end WP.W9mp.Smoke
