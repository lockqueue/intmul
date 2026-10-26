import WP.W9sq.Concrete
import WP.F9.Run

/-!
# WP.W9sq.ConcreteRun — `progC` (the concrete `W9_square` program) under `runTabled`

`WP.F9.runTabled` is the framework machine itself (`tabled_eq`, `runTabled_sound`). Start: the
root header `hdrSyms [b, K0, k1, k2]` on `C0` (with a tail), the one-node stream `streamSyms [z]` on
`S` (with a tail), junk on every other named and scratch stack. Check: every one of the 36 stacks
equals the contract's final state `update S0 S (streamSyms [rootSquareV (rootPrecision b K0) K0 z]
++ restS)` (snapshot value). Rows: `(stacks ok, steps)`.
-/

namespace WP.W9sq.ConcreteRun

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9sq.Concrete IntMul

/-- Every stack of `BLoc 24`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange mC).map Sum.inr

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- Tail of the stream. -/
def restS : List Sym := [symGuard, .sep, .bit false]

/-- Start stacks. -/
def st0 (b K0 k1 k2 : ℕ) (z : Array (ℤ × ℤ)) : BLoc mC → List Sym
  | .inl .S => streamSyms [z] ++ restS
  | .inl .C0 => hdrSyms [b, K0, k1, k2] ++ [.tag 3, .bit true]
  | .inl .W0 => []
  | _ => junk

/-- `(all 36 stacks as specified, steps)`. -/
def row (b K0 k1 k2 : ℕ) (z : Array (ℤ × ℤ)) : Bool × ℕ :=
  let S := st0 b K0 k1 k2 z
  let E := Function.update S (.inl .S)
    (streamSyms [rootSquareV (rootPrecision b K0) K0 z] ++ restS)
  match runTabled progC r0C keys ⟨r0C, S⟩ 50000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- `K0 = 0`, `b = 0` (`q = 8`): `(40, −7) ↦ (6, 2)`. -/
def row1 : Bool × ℕ := row 0 0 1 0 #[(40, -7)]

/-- `K0 = 1`, `b = 1` (`q = 12`): two entries, one with a negative real part. -/
def row2 : Bool × ℕ := row 1 1 1 1 #[(100, 37), (-90, 120)]

-- the snapshot values of the two rows
#eval (rootSquareV (rootPrecision 0 0) 0 #[(40, -7)],
  rootSquareV (rootPrecision 1 1) 1 #[(100, 37), (-90, 120)])

-- `(stacks ok, steps)`
#eval [row1, row2]
#guard [row1, row2].all (·.1)

end WP.W9sq.ConcreteRun
