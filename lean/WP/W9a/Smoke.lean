import WP.W9a.Final
import IntMulTM.Framework.Sim

/-!
# WP.W9a.Smoke — run the compiled combinators (`#eval`)

`runProg` (as in WP.W6a.Smoke) runs the compiled machine `machine p σ0` (framework `Sim`) under
Mathlib's `TM2.step`. By `machine_run`, a run that halts after `n` steps has `Eval` cost `n − 1`.

Rows (tiny inputs). Each reports the output checks, the measured cost, the proved bound (contract
constants `32` for the sweep, `2` for the level driver, `3` for retFlip) and `cost ≤ bound`:
* `rowSweep`: `sweepProg` with the identity kernel `skip`, `g = 2`, four one-entry nodes;
* `rowLevel`: `lvlProg` with stand-in levels `moveSym TR TL` (test scaffolding), depth 2;
* `rowRet`: `retFlipProg` on a two-entry RET segment;
* `rowPipe`: `pipeProg (lvlProg …)` with the same stand-in levels; the tape and `TL` are restored.
The level programs proper need the node kernels (hypotheses), so they are not run here.
-/

namespace WP.W9a.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing WP.W9a

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. On halting,
return the number of steps and the final user stacks. -/
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

/-- The identity kernel (cost 1). -/
def idK : Prog (BLoc 4) (fun _ => Sym) Unit := skip

/-- Four one-entry nodes. -/
def xs0 : List (Array (ℤ × ℤ)) := [#[(1, 2)], #[(3, -1)], #[(0, 5)], #[(-2, 2)]]

/-- Sweep, `g = 2`: `(output ok, scratch empty, cost, proved bound, cost ≤ bound)`. -/
def rowSweep : Bool × Bool × ℕ × ℕ × Bool :=
  let g := 2
  let M := 2
  let out : ℕ → List Sym := fun i => groupSyms (groupAt g xs0 i)
  let bound := sumTo M (fun _ => 1) + 32 * ((streamSyms xs0).length +
    sumTo M (fun i => (out i).length) + M * (bitLen g + 1) + 1)
  let S : BLoc 4 → List Sym := fun k =>
    if k = .inl .S then streamSyms xs0 ++ [Sym.mark]
    else if k = .inl .C2 then natSyms g ++ [Sym.mark] else []
  match runProg (sweepProg (le_refl 4) idK) ((), none) S 1000000 with
  | none => (false, false, 0, bound, false)
  | some (n, S') =>
    (S' (.inl .S) == (List.range M).flatMap out ++ symLevel :: [Sym.mark],
      (List.finRange 4).all (fun j => S' (.inr j) == []), n - 1, bound, decide (n - 1 ≤ bound))

/-- Stand-in level (test scaffolding): move one tape symbol `TR → TL`. -/
def stepL : SProg (BLoc 0) := moveSym (.inl .TR) (.inl .TL)

/-- A depth-2 tag sequence. -/
def tape0 : List Sym := [symPre, symPre, symLeaf, symPost, symPost]

/-- Level driver bound with level costs 2: `Σ cPre + cLeaf + Σ cPost + 2·(2D + 3)`. -/
def lvlBound : ℕ := sumTo 2 (fun _ => 2) + 2 + sumTo 2 (fun _ => 2) + 2 * (2 * 2 + 3)

/-- Level driver: `(TR, TL ok, cost, proved bound, cost ≤ bound)`. -/
def rowLevel : Bool × ℕ × ℕ × Bool :=
  let S : BLoc 0 → List Sym := fun k => if k = .inl .TR then tape0 ++ [Sym.mark] else []
  match runProg (lvlProg stepL stepL stepL) ((none, none) : Option Sym × Option Sym) S 100000 with
  | none => (false, 0, lvlBound, false)
  | some (n, S') =>
    (S' (.inl .TR) == [Sym.mark] && S' (.inl .TL) == tape0.reverse, n - 1, lvlBound,
      decide (n - 1 ≤ lvlBound))

/-- Two retained values. -/
def alts0 : List (ℤ × ℤ) := [(1, -2), (3, 0)]

/-- retFlip: `(RET, RQ ok, cost, proved bound, cost ≤ bound)`. -/
def rowRet : Bool × ℕ × ℕ × Bool :=
  let bound := 3 * ((retSeg alts0).length + 1)
  let S : BLoc 0 → List Sym := fun k => if k = .inl .RET then retSeg alts0 ++ [Sym.mark] else []
  match runProg retFlipProg (none : Option Sym) S 100000 with
  | none => (false, 0, bound, false)
  | some (n, S') =>
    (S' (.inl .RET) == [Sym.mark] && S' (.inl .RQ) == blkE alts0, n - 1, bound,
      decide (n - 1 ≤ bound))

/-- Pipeline wrapper: `(TR and TL restored, cost, level bound + guard + rewind, cost ≤ bound)`. -/
def rowPipe : Bool × ℕ × ℕ × Bool :=
  let bound := 1 + lvlBound + (3 * tape0.length + 2)
  let S : BLoc 0 → List Sym := fun k =>
    if k = .inl .TR then tape0 ++ [Sym.mark] else if k = .inl .TL then [Sym.sep] else []
  match runProg (pipeProg (lvlProg stepL stepL stepL))
      (((none, none), none) : (Option Sym × Option Sym) × Option Sym) S 100000 with
  | none => (false, 0, bound, false)
  | some (n, S') =>
    (S' (.inl .TR) == tape0 ++ [Sym.mark] && S' (.inl .TL) == [Sym.sep], n - 1, bound,
      decide (n - 1 ≤ bound))

#eval rowSweep
#eval rowLevel
#eval rowRet
#eval rowPipe

end WP.W9a.Smoke
