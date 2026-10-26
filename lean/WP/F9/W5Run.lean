import WP.F9.InstW5
import WP.F9.Run

/-!
# WP.F9.W5Run — the concrete Toom-3 multiplier, run

`WP.Inst.toomMul` is W5's `mulP` with the verified W3/W3b instances; it runs under `runTabled` (the
framework machine). Each row has three entries:
* `(x, y, z, scratch)` correct: `z = intSyms (a·b) ++ old z`; `x` and `y` are restored; the eight
  scratch stacks, which start with junk, are restored;
* the steps;
* the declared width `w = max |a| |b|`.
Operands of 10 or more bits take the Toom-3 branch.
-/

namespace WP.F9.W5Run

open TMFw TMFw.Lib TMFw.Contracts WP.F9

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `Loc 3 8`. -/
def keys : List (Loc 3 8) := (List.finRange 3).map Sum.inl ++ (List.finRange 8).map Sum.inr

/-- Start stacks. -/
def st0 (a b : ℤ) : Loc 3 8 → List Sym
  | .inl 0 => intSyms a ++ [.mark]
  | .inl 1 => intSyms b ++ [.tag 3]
  | _ => junk

/-- `(all stacks as specified, steps, w)`. -/
def row (a b : ℤ) : Bool × ℕ × ℕ :=
  let S := st0 a b
  let E := Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))
  match runTabled WP.Inst.toomMul WP.Inst.toomR0 keys ⟨WP.Inst.toomR0, S⟩ 20000000 with
  | none => (false, 0, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n, max (bitLen a.natAbs) (bitLen b.natAbs))

def rows : List (Bool × ℕ × ℕ) :=
  [row 0 0, row 1 1, row 3 (-5), row (-2) (-3), row 255 255, row 1000 (-999), row (-12345) 678,
    row (2 ^ 20 + 7) (3 ^ 12)]

-- `(ok, steps, w)`.
#eval rows
#guard rows.all (·.1)

end WP.F9.W5Run
