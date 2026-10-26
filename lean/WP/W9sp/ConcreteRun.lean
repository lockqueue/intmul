import WP.W9sp.Concrete
import WP.F9.Run

/-!
# WP.W9sp.ConcreteRun — `progC` run under the tabled runner (`WP.F9.runTabled`)

Inputs satisfy `W9_splitPack`'s hypotheses: `A < 2^(b·k1)`, `B < 2^(b·k2)`, `k1 + k2 ≤ 2^K0`,
`OA = natSyms A ++ rA`, `OB = natSyms B ++ rB` (terminated), `C0 = hdrSyms [b, K0, k1, k2] ++ r0`.
Every other stack, scratch included, starts with junk. A row is `true` iff the final stacks are
exactly the contract's: `streamSyms [rootPackV b K0 k1 k2 A B]` pushed on `S`, `OA = rA`, `OB = rB`,
every other stack restored.
-/

namespace WP.W9sp.ConcreteRun

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9sp.Concrete

/-- Every stack of `BLoc mC`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2, .inl .C3,
    .inl .OA, .inl .OB] ++ (List.finRange mC).map .inr

/-- Junk (restoration check). -/
def junk : List Sym := [Sym.bit true, Sym.tag 9]

/-- Start stacks. -/
def st0 (b K0 k1 k2 A B : ℕ) (sOld rA rB : List Sym) : BLoc mC → List Sym
  | .inl .S => sOld
  | .inl .OA => natSyms A ++ rA
  | .inl .OB => natSyms B ++ rB
  | .inl .C0 => hdrSyms [b, K0, k1, k2] ++ [Sym.mark]
  | _ => junk

/-- `(all stacks as the contract says, steps)`. -/
def row (b K0 k1 k2 A B : ℕ) (sOld rA rB : List Sym) : Bool × ℕ :=
  let S := st0 b K0 k1 k2 A B sOld rA rB
  let E := Function.update (Function.update (Function.update S (.inl .S)
    (streamSyms [rootPackV b K0 k1 k2 A B] ++ sOld)) (.inl .OA) rA) (.inl .OB) rB
  match runTabled progC r0C keys ⟨r0C, S⟩ 2000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

def rows : List (Bool × ℕ) :=
  [row 2 2 2 2 13 6 [] [] [],
    row 2 2 2 2 13 6 [Sym.sep, Sym.bit true] [Sym.mark, Sym.bit true] [Sym.sep2],
    row 3 1 1 1 7 5 [symLevel] [Sym.pos] [Sym.neg]]

-- `(ok, steps)`
#eval rows
#guard rows.all (·.1)

end WP.W9sp.ConcreteRun
