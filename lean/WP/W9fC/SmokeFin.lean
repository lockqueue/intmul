import WP.W9fC.Finish
import WP.W9fC.Setup
import IntMulTM.Framework.Sim

/-!
# WP.W9fC.SmokeFin — run compiled column-driver pieces (`#eval`)

Runs the compiled machine (`machine p σ0`, framework `Sim`) on tiny stacks. Each row reports
`(final stacks as expected, steps, expected steps)`. The expected count is the exact `Eval` cost of
the proofs plus one (`machine_run`):
* `xferAll`: `3·|L| + 2` (`runs_xfer'`);
* `dropThrough`: `2·|L| + 2` (`runs_drop'`);
* `finishProg`: `(3·|A| + 2) + 2 + (2·bitLen r + 2) + (2·|recD alt| + 2) + (2·bitLen t1 + 2)`
  (`fin_runs`; `runs_finish` states this plus 2).
For `setupProg` the row checks the final stacks and `steps ≤ bound + 1`, where the bound is the
cost of `runs_setup`: `6·bitLen p + 6·bitLen pSub + 7·bitLen t1 + 6·|W0| + 30`.
-/

namespace WP.W9fC.SmokeFin

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing WP.W9comp WP.W9fC

/-- Run the compiled machine of `p` from user stacks `S` for at most `fuel` steps. On halting,
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

theorem h7 : 7 ≤ 7 := le_rfl

#assert_std_axioms h7

/-- Stacks given on a list of locations, empty elsewhere. -/
def stk (l : List (BLoc 7 × List Sym)) (k : BLoc 7) : List Sym :=
  match l.find? (fun e => decide (e.1 = k)) with
  | some e => e.2
  | none => []

def ent : List (ℤ × ℤ) := [(3, -2), (0, 5), (-7, 1)]
def alt0 : ℤ × ℤ := (-1, 4)
def tail0 : List Sym := [Sym.mark, Sym.bit true]

/-- `xferAll W0 → M`. -/
def rowXfer (L : List Sym) : Bool × ℕ × ℕ :=
  match runProg (lft Unit (xferAll (.inl .W0) (sM h7))) ((), none)
      (stk [(.inl .W0, L), (sM h7, tail0)]) 10000 with
  | none => (false, 0, 3 * L.length + 3)
  | some (n, S) => (S (.inl .W0) == [] && S (sM h7) == L.reverse ++ tail0, n, 3 * L.length + 3)

/-- `dropThrough C3 mark` on a counter `natSyms k`. -/
def rowDrop (k : ℕ) : Bool × ℕ × ℕ :=
  match runProg (lft Unit (dropThrough (.inl .C3) Sym.mark)) ((), none)
      (stk [(.inl .C3, natSyms k ++ Sym.mark :: tail0)]) 10000 with
  | none => (false, 0, 2 * bitLen k + 3)
  | some (n, S) => (S (.inl .C3) == tail0, n, 2 * bitLen k + 3)

/-- The stacks of `colV r` (relevant part) for `runs_finish`. -/
def finInit (r t1 : ℕ) : BLoc 7 → List Sym :=
  stk [(sA h7, (blkE ent).reverse ++ symGuard :: tail0), (.inl .TR, symSub :: tail0),
    (.inl .TL, tail0), (.inl .C3, natSyms r ++ Sym.mark :: tail0),
    (.inl .RQ, entrySyms alt0 ++ tail0), (sCT h7, natSyms t1 ++ symGuard :: tail0)]

def rowFin (r t1 : ℕ) : Bool × ℕ × ℕ :=
  let ex := 3 * (blkE ent).length + 2 + 2 + (2 * bitLen r + 2) + (2 * (recD alt0).length + 2) +
    (2 * bitLen t1 + 2) + 1
  match runProg (finishProg h7 Unit) ((), none) (finInit r t1) 100000 with
  | none => (false, 0, ex)
  | some (n, S) =>
    (S (.inl .W0) == blkE ent && S (sA h7) == tail0 && S (.inl .TR) == tail0 &&
      S (.inl .TL) == symSub :: tail0 && S (.inl .C3) == tail0 && S (.inl .RQ) == tail0 &&
      S (sCT h7) == tail0, n, ex)

def setInit (p pSub t1 : ℕ) (w : List Sym) : BLoc 7 → List Sym :=
  stk [(.inl .C0, natSyms p ++ Sym.mark ::
      (natSyms pSub ++ Sym.mark :: (natSyms t1 ++ Sym.mark :: tail0))), (.inl .W0, w)]

def rowSet (p pSub t1 : ℕ) (w : List Sym) : Bool × ℕ × ℕ :=
  let bd := 6 * bitLen p + 6 * bitLen pSub + 7 * bitLen t1 + 6 * w.length + 30 + 1
  match runProg (setupProg h7 Unit) ((), none) (setInit p pSub t1 w) 100000 with
  | none => (false, 0, bd)
  | some (n, S) =>
    (S (.inl .W0) == [] && S (.inl .C0) == setInit p pSub t1 w (.inl .C0) &&
      S (.inl .C3) == [Sym.mark] && S (sM2 h7) == w && S (sA h7) == [symGuard] &&
      S (sCT h7) == natSyms t1 ++ [symGuard] && S (sT h7) == [] && S (sM h7) == [] &&
      decide (n ≤ bd), n, bd)

-- `xferAll`: stacks as expected; steps = proved exact cost + 1.
#eval [rowXfer [], rowXfer [Sym.bit true], rowXfer (blkE ent)]

-- `dropThrough`: stacks as expected; steps = proved exact cost + 1.
#eval [rowDrop 0, rowDrop 1, rowDrop 6, rowDrop 100]

-- `finishProg` (`runs_finish`): stacks as expected; steps = proved exact cost + 1.
#eval [rowFin 0 1, rowFin 1 2, rowFin 5 4, rowFin 16 8]

-- `setupProg` (`runs_setup`): stacks as expected; steps ≤ proved bound + 1.
#eval [rowSet 1 1 2 [], rowSet 5 3 4 (blkE ent), rowSet 12 6 8 [Sym.sep]]

end WP.W9fC.SmokeFin
