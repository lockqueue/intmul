import WP.W7k3t.Concrete
import WP.F9.Run

/-!
# WP.W7k3t.ConcreteRun — the concrete tap kernel under `runTabled` (written by W9sq)

`WP.F9.runTabled` is the framework machine itself (`tabled_eq`, `runTabled_sound`). Start: the
contract's inputs on the named stacks `0..6` (`p_work pSub t1 j1 s`, `π`, `ln 2` at
`W7.tapPrec pSub`, each with a terminator), junk on `dst` and on the 16 scratch stacks. Check: all
24 stacks equal the contract's final state, i.e. `dst += intSyms (computableSincGaussianTapWithProgramCost
p_work pSub t1 j1 s).1` (snapshot value), everything else restored. Row: `(stacks ok, steps)`.
-/

namespace WP.W7k3t.ConcreteRun

open TMFw TMFw.Lib TMFw.Contracts WP.F9 WP.W7k3t.Concrete

/-- All stacks of `Loc 8 16`. -/
def keys : List (Loc 8 mC) := (List.finRange 8).map Sum.inl ++ (List.finRange mC).map Sum.inr

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- Start stacks. -/
def st0 (p_work pSub t1 j1 s : ℕ) : Loc 8 mC → List Sym
  | .inl 0 => natSyms p_work ++ [.mark]
  | .inl 1 => natSyms pSub ++ [.mark]
  | .inl 2 => natSyms t1 ++ [.tag 3]
  | .inl 3 => natSyms j1 ++ [.mark]
  | .inl 4 => natSyms s ++ [.mark]
  | .inl 5 => intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1 ++ [.mark]
  | .inl 6 => intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1 ++ [.mark]
  | _ => junk

/-- `(all 24 stacks as specified, steps)`. -/
def row (p_work pSub t1 j1 s : ℕ) : Bool × ℕ :=
  let S := st0 p_work pSub t1 j1 s
  let E := Function.update S (.inl 7)
    (intSyms (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1 ++ S (.inl 7))
  match runTabled progC r0C keys ⟨r0C, S⟩ 400000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

-- One run at `(p_work, pSub, t1, j1, s) = (1, 1, 2, 1, 0)` (`B_c = W7.tapPrec 1 = 72`; the Gaussian
-- is clamped, so the else-branch series is not exercised: at these widths it would take `≳ 10⁸`
-- steps). Prints `(stacks ok, steps, snapshot tap)` and fails the build on a mismatch.
#eval show IO (Bool × ℕ × ℤ) from do
  let r := row 1 1 2 1 0
  unless r.1 do throw (IO.userError "W7k3t concrete tap run: stacks differ from the contract")
  return (r.1, r.2, (IntMul.computableSincGaussianTapWithProgramCost 1 1 2 1 0).1)

end WP.W7k3t.ConcreteRun
