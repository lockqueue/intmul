import WP.W9s.RecMain
import IntMulTM.Framework.Sim

/-!
# WP.W9s.Smoke — run the compiled machine (`#eval`)

The arithmetic subroutines (`W3_addInt`, `W3_subInt`, halving) are contract parameters. These tests
run the parts of the machine that do not call them, with a dummy kit (`dKit`, never invoked):
* `rotRow` (the negacyclic rotation) for several shifts;
* `dealLoop` (even/odd dealing) on a 4-row block;
* `fft` on a 1-row block (the base case of the recursion, with the `fix`/`recur` machinery).

Each row checks the exact final stacks predicted by the `HT` theorems and compares the step count
(minus 1 for the final halt, `machine_run`) with the proved bound.
-/

namespace WP.W9s.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 WP.W9s Computability Turing

/-- Run the compiled machine of `p` from user stacks `S` (copied from `WP.W6a.Smoke`). -/
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

/-- A dummy instance (test scaffolding, never invoked by the tested programs). -/
def dInst (n : ℕ) : Inst n 4 Unit := ⟨0, Unit, fun _ => (), .load id, Nat.zero_le _, inferInstance,
  ⟨()⟩, trivial⟩

def dKit : Kit := ⟨dInst 3, dInst 3, Unit, fun _ => .load id⟩

def σ0 : dKit.R := (none, (), (), ())

/-- All host stacks. -/
def hosts : List Host := (List.finRange 2).map Sum.inl ++ (List.finRange 20).map Sum.inr

/-- Do two host states agree everywhere? -/
def agree (S T : Host → List Sym) : Bool := hosts.all fun k => S k == T k

def upd (S : Host → List Sym) (k : Host) (v : List Sym) : Host → List Sym :=
  fun j => if j = k then v else S j

def empty : Host → List Sym := fun _ => []

def f4 : List (ℤ × ℤ) := [(1, 2), (-3, 0), (5, -1), (0, 7)]

/-- `rotRow`: `(s, exact final state, steps − 1, bound 6|es f| + 9|f| + 20)`. -/
def rowRot (s : ℕ) : ℕ × Bool × ℕ × ℕ :=
  let S := upd (upd empty sD (rowE f4 ++ [symBlk])) sV (units (4 - s) ++ [symG])
  let T := upd (upd S sD [symBlk]) sG (growE s (rotL s f4))
  match runProg (rotRow dKit) σ0 S 100000 with
  | none => (s, false, 0, 0)
  | some (n, S') => (s, agree S' T, n - 1, 6 * (es f4).length + 9 * f4.length + 20)

def X4 : List (List (ℤ × ℤ)) := [[(1, 0), (2, -1)], [(0, 3), (4, 4)], [(-5, 1), (6, 0)], [(7, 7), (0, -2)]]

/-- `dealLoop`: `(exact final state, steps − 1, bound 3|blkR X| + |X| + 2)`. -/
def rowDeal : Bool × ℕ × ℕ :=
  let S := upd empty sA (blkR X4 ++ [symBlk])
  let T := upd (upd (upd S sA [symBlk]) sE (blkR (evensL X4)).reverse) sO (blkR (oddsL X4)).reverse
  match runProg (dealLoop dKit) σ0 S 100000 with
  | none => (false, 0, 0)
  | some (n, S') => (agree S' T, n - 1, 3 * (blkR X4).length + X4.length + 2)

/-- `fft` on one row (`n = 0`): `(state unchanged, steps − 1, bound costF 0 + 2)` with zero kit
constants (the kit is not invoked). -/
def rowFft1 : Bool × ℕ × ℕ :=
  let r := 2
  let row := [(3, -4), (-1, 2)]
  let S := upd (upd (upd empty sA (blkR [row] ++ [symBlk])) sDS (units (2 * r) ++ [symG])) sUR
    (units r ++ [symG])
  match runProg (fft dKit) σ0 S 100000 with
  | none => (false, 0, 0)
  | some (n, S') => (agree S' S, n - 1, costF 0 0 0 3 r 0 + 2)

#eval [rowRot 0, rowRot 1, rowRot 2, rowRot 3]

#eval rowDeal

#eval rowFft1

end WP.W9s.Smoke
