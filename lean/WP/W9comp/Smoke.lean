import WP.W9comp.PreProg
import WP.W9comp.PostProg
import IntMulTM.Framework.Sim

/-!
# WP.W9comp.Smoke — run the compiled composites (`#eval`)

The composites take their phase programs as parameters. To run them, we instantiate the phases with
two **unverified test stubs**, used by no theorem:
* `noop`: one register load, cost 1;
* `adv n`: move `n` symbols from `TR` to `TL`, cost `2n + 1`. It stands in for a table phase that
  advances the head across `n` body symbols.

For PRE, `P3 := adv n` and every other phase is `noop`. For POST, `Q5 := adv n` and the others are
`noop`. Every phase sits at scratch count `0` inside a composite with `2` scratch stacks, so `emb`
is exercised.

Each row checks:
* that `TL`, `TR` and `W0` are restored exactly, and the scratch stacks are empty. `TL`'s old
  content contains `symGuard`; the rewind must stop at the guard that the composite pushed.
* the step count. It is compared with the exact `Eval` cost from the proofs, plus one
  (`machine_run`):
  * PRE: `6 + 1 + (2n + 1) + (3n + 2)` (six `noop`s, the guard push, `adv n`, and the rewind
    `3·L + 2` with `L = n` from `runs_rewind`);
  * POST: `3 + 1 + (2n + 1) + (3n + 2)`.
-/

namespace WP.W9comp.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing
open WP.W9comp

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. On halting,
return the number of steps and the final user stacks (copied from `WP.W6a.Smoke`). -/
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

/-- Test stub (unverified): move `n` symbols from `TR` to `TL`. -/
def adv : ℕ → SProg (BLoc 0)
  | 0 => noop
  | n + 1 => .seq (popR (.inl .TR)) (.seq (pushR (.inl .TL)) (adv n))

/-- Every stub phase has scratch count `0`; the composites have `2`. -/
theorem z2 : 0 ≤ 2 := Nat.zero_le 2

#assert_std_axioms z2

/-- The PRE composite with stubs. -/
def preStub (n : ℕ) : Prog (BLoc 2) (fun _ => Sym)
    (PreRegs (Option Sym) (Option Sym) (Option Sym) (Option Sym) (Option Sym) (Option Sym)
      (Option Sym)) :=
  preNodeProg z2 z2 z2 z2 z2 z2 z2 noop noop (adv n) noop noop noop noop

/-- The POST composite with stubs. -/
def postStub (n : ℕ) : Prog (BLoc 2) (fun _ => Sym)
    (PostRegs (Option Sym) (Option Sym) (Option Sym) (Option Sym)) :=
  postNodeProg z2 z2 z2 z2 noop noop (adv n) noop

/-- Initial stacks: `TL = tl0`, `TR = body ++ rest`, `W0 = w0`, everything else empty. -/
def init (tl0 tr0 w0 : List Sym) : BLoc 2 → List Sym := fun k =>
  if k = .inl .TL then tl0 else if k = .inl .TR then tr0 else if k = .inl .W0 then w0 else []

/-- A table body of `n` symbols (bits and separators, never `symGuard`). -/
def body (n : ℕ) : List Sym := (List.range n).map fun i => if i % 3 = 0 then Sym.sep else .bit (i % 2 = 0)

/-- Old `TL` content, deliberately containing `symGuard`. -/
def tl0 : List Sym := [symGuard, Sym.mark, symGuard]

def tr0 (n : ℕ) : List Sym := body n ++ [Sym.mark, Sym.bit true]

def w0 : List Sym := [Sym.bit true, Sym.sep]

/-- `(n, frame restored, steps, exact cost + 1)` for a composite run. -/
def row {σ : Type} (p : Prog (BLoc 2) (fun _ => Sym) σ) (σ0 : σ) (n expected : ℕ) :
    ℕ × Bool × ℕ × ℕ :=
  match runProg p σ0 (init tl0 (tr0 n) w0) 100000 with
  | none => (n, false, 0, expected)
  | some (steps, S) =>
    (n, S (.inl .TL) == tl0 && S (.inl .TR) == tr0 n && S (.inl .W0) == w0 &&
        S (.inl .RET) == [] && S (.inr 0) == [] && S (.inr 1) == [],
      steps, expected)

def rowPre (n : ℕ) : ℕ × Bool × ℕ × ℕ :=
  row (preStub n) (none, none, none, none, none, none, none, none) n
    (6 + 1 + (2 * n + 1) + (3 * n + 2) + 1)

def rowPost (n : ℕ) : ℕ × Bool × ℕ × ℕ :=
  row (postStub n) (none, none, none, none, none) n (3 + 1 + (2 * n + 1) + (3 * n + 2) + 1)

-- PRE composite: frame restored; steps equal the proved exact cost + 1.
#eval [rowPre 0, rowPre 1, rowPre 2, rowPre 7, rowPre 20]

-- POST composite: frame restored; steps equal the proved exact cost + 1.
#eval [rowPost 0, rowPost 1, rowPost 2, rowPost 7, rowPost 20]

end WP.W9comp.Smoke
