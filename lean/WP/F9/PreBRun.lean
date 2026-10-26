import WP.F9.PreB
import WP.F9.Run

/-!
# WP.F9.PreBRun — stage runs of the concrete PRE phases P1, P2, P8

`P1C`, `P2C` and `P8C` (WP.F9.PreB) run under `runTabled`, the framework machine.
* Start: the stacks of each contract. `C0` holds the PRE header followed by a tail, `C1` holds `p_in`
  followed by a tail, and every other stack, scratch included, holds junk.
* Check: every stack after the run against the contract's post-state with the snapshot value:
  `w9XRows` for P1, the reversed `alt_q` pushed on RET for P2, the node stream for P8.

Each row is `(stacks ok, steps)`.
-/

namespace WP.F9.PreBRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9

attribute [local instance 10000] instZeroIntElementary

/-- Sample entries. -/
def ents : List (ℤ × ℤ) :=
  [(0, 0), (1, -1), (-5, 3), (12, -7), (-2, 0), (6, 9), (-13, -1), (3, 4), (7, -8), (-1, 1)]

/-- Entry `i` of the sample cycle. -/
def ent (i : ℕ) : ℤ × ℤ := ents.getD (i % ents.length) (0, 0)

/-- A `rows × cols` sample matrix. -/
def mkMat (rows cols seed : ℕ) : Array (Array (ℤ × ℤ)) :=
  Array.ofFn fun i : Fin rows => Array.ofFn fun j : Fin cols => ent (seed + i.val * cols + j.val)

/-- A sample array. -/
def mkArr (n seed : ℕ) : Array (ℤ × ℤ) := Array.ofFn fun i : Fin n => ent (seed + i.val)

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `BLoc m`. -/
def keysB (m : ℕ) : List (BLoc m) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange m).map Sum.inr

/-- Start stacks: `W0`, the PRE header on `C0`, `p_in` on `C1` (with tails), junk elsewhere. -/
def st0 (m : ℕ) (h : PreHdr) (w0 : List Sym) : BLoc m → List Sym
  | .inl .W0 => w0
  | .inl .C0 => hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ [.tag 2, .bit true]
  | .inl .C1 => hdrSyms [h.p_in] ++ [.tag 3]
  | _ => junk

/-- Run: `(all stacks as specified, steps)`. -/
def runRow {m : ℕ} {σ : Type} (p : Prog (BLoc m) (fun _ => Sym) σ) (σ0 : σ)
    (S E : BLoc m → List Sym) : Bool × ℕ :=
  match runTabled p σ0 (keysB m) ⟨σ0, S⟩ 3000000 with
  | none => (false, 0)
  | some (n, S') => ((keysB m).all fun k => S' k == E k, n)

/-- P1 on `x` (`N` entries). -/
def rowP1 (h : PreHdr) (x : Array (ℤ × ℤ)) : Bool × ℕ :=
  let S := st0 8 h (blkE x.toList)
  runRow P1C p1r0 S (Function.update S (.inl .W0) (matSyms (w9XRows h.t1 h.r x)))

/-- P2 on `xRows` (`t1 × r`). -/
def rowP2 (h : PreHdr) (xRows : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 24 h (matSyms xRows)
  runRow P2C p2r0 S (Function.update S (.inl .RET)
    ((entrySyms (computableNyquistAltSumContiguous h.p_in h.pSub h.r
      (xRows.getD (h.t1 / 2) #[]))).reverse ++ S (.inl .RET)))

/-- P8 on `M` (`t1 × r`). -/
def rowP8 (h : PreHdr) (M : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 6 h (matSyms M)
  runRow P8C p8r0 S (Function.update S (.inl .W0) (M.toList.flatMap nodeSyms))

/-- `(p_in, pSub, m1, t1, r)`: square. -/
def hA : PreHdr := ⟨5, 4, 1, 2, 2⟩
/-- Non-square (`t1 = 2`, `r = 4`), `p_in < pSub`. -/
def hB : PreHdr := ⟨3, 6, 1, 2, 4⟩

def rows : List (Bool × ℕ) :=
  [rowP1 hA (mkArr 4 0), rowP1 hB (mkArr 8 3), rowP2 hA (mkMat 2 2 1), rowP2 hB (mkMat 2 4 2),
    rowP8 hA (mkMat 2 2 4), rowP8 hB (mkMat 2 4 5)]

-- P1, P1, P2, P2, P8, P8: `(stacks ok, steps)`.
#eval rows
#guard rows.all (·.1)

end WP.F9.PreBRun
