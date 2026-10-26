import WP.W9c.Concrete
import WP.F9.Run

/-!
# WP.W9c.ConcreteRun — `progC` (one spread row) run under the tabled runner (`WP.F9.runTabled`)

Inputs satisfy `W9_spreadRow`'s hypotheses: `PreDims h`, `C0 = hdrSyms (preTapeFields …) ++ r0`,
`C1 = hdrSyms [p_in] ++ r1`, `W0 = blkE row` with `|row| = r`, `TR = filterRowSyms taps ++ restT`
with `|taps| ≤ W`. Every other stack, scratch included, starts with junk. A row is `true` iff the
final stacks are exactly the contract's: `W0 = blkE (spreadRowWithStride (fun _ _ => s) p_in pSub
m1 r taps row)` (the snapshot's static-stride spread row), `TR = restT`, `TL` gets the reversed
filter row, every other stack restored.
-/

namespace WP.W9c.ConcreteRun

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9c.Concrete IntMul

/-- Every stack of `BLoc mC`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2, .inl .C3,
    .inl .OA, .inl .OB] ++ (List.finRange mC).map .inr

/-- Junk (restoration check). -/
def junk : List Sym := [Sym.bit true, Sym.tag 9]

/-- Start stacks. -/
def st0 (h : PreHdr) (taps : List ℤ) (row : List (ℤ × ℤ)) : BLoc mC → List Sym
  | .inl .W0 => blkE row
  | .inl .TR => filterRowSyms taps ++ [symGuard]
  | .inl .C0 => hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ [Sym.sep]
  | .inl .C1 => hdrSyms [h.p_in] ++ [Sym.tag 5]
  | _ => junk

/-- `(all stacks as the contract says, steps)`. -/
def row (h : PreHdr) (taps : List ℤ) (rw : List (ℤ × ℤ)) : Bool × ℕ :=
  let S := st0 h taps rw
  let out := IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1 h.r
    taps rw.toArray
  let E := Function.update (Function.update (Function.update S (.inl .W0) (blkE out.toList))
    (.inl .TR) [symGuard]) (.inl .TL) ((filterRowSyms taps).reverse ++ S (.inl .TL))
  match runTabled progC r0C keys ⟨r0C, S⟩ 50000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- The snapshot's spread row (the expected `W0`), for display. -/
def spreadOut (h : PreHdr) (taps : List ℤ) (rw : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1 h.r taps
    rw.toArray).toList

/-- Row 1: `(p_in, pSub, m1, t1, r) = (2, 2, 1, 2, 4)` (stride 6, `W = 3`, 2 blocks per coordinate). -/
def row1 : Bool × ℕ := row ⟨2, 2, 1, 2, 4⟩ [1, -2, 1] [(5, -3), (0, 7), (-2, 2), (1, 0)]

/-- Row 2: `(0, 1, 0, 2, 2)` (stride 3, `W = 1`). -/
def row2 : Bool × ℕ := row ⟨0, 1, 0, 2, 2⟩ [3] [(1, 2), (-3, 4)]

/-- Row 3: `(3, 3, 2, 2, 8)` (stride 9, `W = 5`). -/
def row3 : Bool × ℕ :=
  row ⟨3, 3, 2, 2, 8⟩ [1, 2, 3, 2, 1]
    [(9, -1), (4, 4), (-7, 0), (0, 3), (2, -2), (-5, 6), (1, 1), (8, -8)]

-- the expected spread rows (nonzero)
#eval [spreadOut ⟨2, 2, 1, 2, 4⟩ [1, -2, 1] [(5, -3), (0, 7), (-2, 2), (1, 0)],
  spreadOut ⟨0, 1, 0, 2, 2⟩ [3] [(1, 2), (-3, 4)],
  spreadOut ⟨3, 3, 2, 2, 8⟩ [1, 2, 3, 2, 1] [(9, -1), (4, 4), (-7, 0), (0, 3), (2, -2), (-5, 6),
    (1, 1), (8, -8)]]

-- `(ok, steps)`, one `#eval` per row
#eval row1
#guard row1.1
#eval row2
#guard row2.1
#eval row3
#guard row3.1

end WP.W9c.ConcreteRun
