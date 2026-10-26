import WP.W9h.Concrete
import WP.F9.Run

/-!
# WP.W9h.ConcreteRun — `progC` run under the tabled runner (`WP.F9.runTabled`)

Inputs satisfy `W9_reconstruct`'s hypotheses: `C0 = hdrSyms [b, K0, k1, k2] ++ r0`,
`OA = hdrSyms cs ++ rA` with `|cs| = k1 + k2 ≤ 2^K0` and `rA` terminated. Every other stack, scratch
included, starts with junk. A row is `true` iff the final stacks are exactly the contract's:
`OA = natSyms (reconstructChunksTree b cs) ++ rA` (the snapshot's carry pass), every other stack
restored.
-/

namespace WP.W9h.ConcreteRun

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9h.Concrete IntMul

/-- Every stack of `BLoc mC`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2, .inl .C3,
    .inl .OA, .inl .OB] ++ (List.finRange mC).map .inr

/-- Junk (restoration check). -/
def junk : List Sym := [Sym.bit true, Sym.tag 9]

def rA0 : List Sym := [Sym.mark, Sym.bit false]

/-- Start stacks. -/
def st0 (b K0 k1 k2 : ℕ) (cs : List ℕ) : BLoc mC → List Sym
  | .inl .C0 => hdrSyms [b, K0, k1, k2] ++ [Sym.sep]
  | .inl .OA => hdrSyms cs ++ rA0
  | _ => junk

/-- `(all stacks as the contract says, steps)`. -/
def row (b K0 k1 k2 : ℕ) (cs : List ℕ) : Bool × ℕ :=
  let S := st0 b K0 k1 k2 cs
  let E := Function.update S (.inl .OA) (natSyms (reconstructChunksTree b cs) ++ rA0)
  match runTabled progC r0C keys ⟨r0C, S⟩ 2000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

def rows : List (Bool × ℕ) :=
  [row 2 2 2 1 [3, 1, 2], row 4 3 3 3 [15, 31, 0, 7, 100, 1], row 2 2 2 2 [255, 255, 255, 255]]

-- `(ok, steps)`
#eval rows
#guard rows.all (·.1)

end WP.W9h.ConcreteRun
