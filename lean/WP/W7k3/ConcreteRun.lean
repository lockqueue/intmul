import WP.W7k3.Concrete
import WP.F9.Run

/-!
# WP.W7k3.ConcreteRun — the concrete series sub-kernel, run

`WP.W7k3.Concrete.progC κ` runs under `WP.F9.runTabled` (the framework machine, `tabled_eq`). Each row:
* all stacks as specified: destination `= intSyms (serState a0 c d f g n).2 ++ old`, the named inputs
  restored, the twelve scratch stacks (junk at the start) restored;
* the number of machine steps.
-/

namespace WP.W7k3.ConcreteRun

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3 WP.W7k3.Concrete WP.F9

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `Loc 5 12`. -/
def keys : List (Loc 5 12) := (List.finRange 5).map Sum.inl ++ (List.finRange 12).map Sum.inr

/-- Start stacks. -/
def st0 (a0 c : ℤ) (d n : ℕ) : Loc 5 12 → List Sym
  | .inl 0 => intSyms a0 ++ [.mark]
  | .inl 1 => intSyms c ++ [.tag 3]
  | .inl 2 => natSyms d ++ [.mark]
  | .inl 3 => natSyms n ++ [.sep]
  | _ => junk

/-- `(all stacks as specified, steps)`. -/
def row (κ : SK) (a0 c : ℤ) (d n : ℕ) : Bool × ℕ :=
  let S := st0 a0 c d n
  let E := Function.update S (.inl 4) (intSyms (serState a0 c d κ.f κ.g n).2 ++ S (.inl 4))
  match runTabled (progC κ) r0C keys ⟨r0C, S⟩ 50000000 with
  | none => (false, 0)
  | some (t, S') => (keys.all fun k => S' k == E k, t)

/-- cos(3/4), sin(3/4) on the `2^12` grid, and a half-erf numerator (snapshot lambdas). -/
def rows : List (Bool × ℕ) :=
  [row SK.cos (2 ^ 12) (-9) 16 3, row SK.sin (3 * 2 ^ 10) (-9) 16 3, row SK.erf 1000 (-25) 49 3]

-- `(ok, steps)`.
#eval rows
#guard rows.all (·.1)

end WP.W7k3.ConcreteRun
