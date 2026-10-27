import WP.F9.PostLevelRun
import WP.W9f.Concrete

/-!
# WP.F9.PostLevelRunC — the POST level with every concrete POST kernel

`rowPostRaw` (WP.F9.PostLevelRun) with the real column stage `WP.W9f.Concrete.progColsC`. The node runs
Q2, Q3+Q4, Q5 (the W9f columns: forward and Nyquist solves with Barrett) and Q6 inside the real
POST level program (sweep, retFlip). The run is checked against `PostLevelSpec`'s post-state, which
uses the snapshot's `postNodeV` with the exact solvers.

**Parameters.** The snapshot's table builder sets `pSub = 2·pChild p K = 2·(p + 2K + 12)`. So every
paper-valid step level (`p ≥ 8`, `K ≥ 2`) has `pSub ≥ 48` and `H = barrettH pSub ≥ 146`.

On `stepChain 12 2` we have `pSub = 56` and `H = 170`. `colData` below shows the column data there is
55–58 bits wide and that Barrett = exact. Even so, the POST level does not finish within 7M steps
(over 835 s in `#eval`): W9f's cost bound has Barrett products up to `8(H+1) = 1368` bits wide. That
is far beyond the 900 s build cap in the Lean interpreter.

The run below therefore uses a small POST header, `(p, pSub, t1, r, pChild) = (3, 2, 2, 2, 4)`
(`H = 8`), with the column tables of the `W9_columns` node test: column `u2 = 0` is forward
and `u2 = 1` is Nyquist. `pureS` checks that the Barrett columns equal the exact columns on this
input. `ColumnOK` itself is not formally verified here.
-/

namespace WP.F9.PostLevelRunC

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9
  WP.F9.PostLevelRun WP.F9.StepRun

attribute [local instance 10000] instZeroIntElementary

/-- `c0` table: the column divisors. -/
def c0S : Array (ℤ × ℤ) := #[(3, 0), (2, 0)]

/-- `c1` table: the multipliers. -/
def c1S : Array (ℤ × ℤ) := #[(-1, 0), (1, 0)]

/-- The retained value of the node. -/
def altS : ℤ × ℤ := (1, -1)

/-- Two child outputs (`t1 = 2`) of `r = 2` entries at precision `pChild = 4`. -/
def ysS : List (Array (ℤ × ℤ)) := [#[(4, -8), (0, 4)], #[(8, 0), (-8, 8)]]

/-- Pure checks: `(Y, Barrett columns = exact columns)`. -/
def pureS : Array (Array (ℤ × ℤ)) × Bool :=
  let Y := w9Y 2 2 2 4 (w9ColRoutes 2 2 (w9QHatT 2 2 ysS.toArray))
  (Y, w9ZBarrett 2 2 2 c0S c1S altS Y == w9ZExact 2 2 2 c0S c1S altS Y)

-- `(Y, Barrett = exact)`.
#eval pureS

/-- The run, with a step budget of 3M. -/
def rowS (_ : Unit) : Bool × ℕ × List ℕ :=
  rowPostRaw WP.W9f.Concrete.progColsC WP.W9f.Concrete.r0ColsC WP.W9f.Concrete.normColsC
    3 2 2 2 4 c0S c1S [altS] ysS 3000000

/-- Run `f` and add the wall time in ms. -/
def timed (f : Unit → Bool × ℕ × List ℕ) : IO (Bool × ℕ × List ℕ × ℕ) := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"POST level: {r.1} {r.2.1} {r.2.2}"
  let t1 ← IO.monoMsNow
  return (r.1, r.2.1, r.2.2, t1 - t0)

-- POST level with the concrete columns: `(stacks ok, steps, differing stacks, wall ms)`.
#eval timed rowS

/-- Bit width of a complex entry. -/
def bitsZ (z : ℤ × ℤ) : ℕ := max (Nat.log2 z.1.natAbs) (Nat.log2 z.2.natAbs) + 1

/-- Maximal bit width of an array. -/
def bitsA (a : Array (ℤ × ℤ)) : ℕ := a.foldl (fun m z => max m (bitsZ z)) 0

/-- Pure: the column data of the POST level of chain `cs` at root input `x` (with `p_in`):
`([p, pSub, pChild, t1, r, H, bits Y, bits alt, bits c0, bits c1], Barrett = exact)`. -/
def colData (cs : ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ)) : List ℕ × Bool :=
  match cs with
  | .step p pSub m1 t1 r ft preTw postTw c0T c1T child =>
    let ys := levelEvalV child pSub (preNodeV p_in pSub m1 t1 r ft preTw postTw x).toList
    let alt := altNodeV p_in pSub t1 r x
    let Y := w9Y pSub t1 r child.p (w9ColRoutes t1 r (w9QHatT t1 r ys.toArray))
    ([p, pSub, child.p, t1, r, barrettH pSub, Y.foldl (fun m a => max m (bitsA a)) 0, bitsZ alt,
      bitsA c0T, bitsA c1T], w9ZBarrett pSub t1 r c0T c1T alt Y == w9ZExact pSub t1 r c0T c1T alt Y)
  | _ => ([], false)

-- The POST column data on `stepChain 12 2` for three root inputs.
#eval [colData (stepChain 12 2) 1 #[(3, 0), (-2, 1), (0, 0), (1, -1)],
  colData (stepChain 12 2) 1 #[(1, 0), (0, 1), (-1, 0), (1, -1)],
  colData (stepChain 12 2) 1 #[(1, 0), (0, 0), (1, 0), (1, 0)]]

end WP.F9.PostLevelRunC
