import WP.W9f.Concrete
import WP.W9f.RunR

/-!
# WP.W9f.ConcreteRun — tabled runs of the concrete column solver

`progC` (WP.W9f.Concrete) runs under `WP.W9f.RunR.runTabledR`. That is `WP.F9.runTabled`, which
steps the framework machine itself, plus the identity register map `normRC` (`normRC_eq`), applied
at each rebuild. `runTabledR_sound` gives the soundness statement of `runTabled_sound`, and
`keys_complete` lists every stack. Without `normRC` the IntLang op registers build a closure chain
that overflows the interpreter. `progC` contains the real cores: S1 `IFC`, S2 `INC` with the
Nyquist finish, the entry mover, and the comparator.

There is one column per regime: `u2 < r/2` (fwd), `u2 = r/2` (Nyquist), `u2 > r/2` (bwd). The
POST header has `t1 = 4`, `r = 8` and `pSub = 2`, so `H = 8`. The column and `alt` are nonzero,
and the column divisor is positive. `ColumnOK` is not formally verified here. Each run checks the
contract's final stacks exactly:
* `W0 = blkE (W8.columnSolveBarrett pSub H t1 mt1 r u2 c0 c1 Y alt)`, the contract value;
* `TR := restT` and `TL := rec.reverse ++ TL`;
* every other stack is restored (junk starts on every scratch and private stack).

Each row is `(stacks ok, steps, indices in keys of the stacks that differ, wall ms)`. Steps are
counted as in `machine_run` (cost + 1).
-/

namespace WP.W9f.ConcreteRun

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9f WP.W9f.Concrete IntMul

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 5]

/-- All stacks of `BLoc mC`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange mC).map .inr

theorem keys_complete : ∀ k : BLoc mC, k ∈ keys := by
  intro k
  rcases k with k | k
  · cases k <;> simp [keys]
  · simp [keys]

/-- Start stacks: the column on `W0`, the record `rc` on `TR`, the header on `C0`, `u2` on `C3`,
`alt` on `RQ`, junk elsewhere. -/
def colSt0 (h : PostHdr) (u2 : ℕ) (alt : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (rc : List Sym) :
    BLoc mC → List Sym
  | .inl .W0 => blkE Y.toList
  | .inl .TR => rc ++ [.tag 4]
  | .inl .C0 => hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ junk
  | .inl .C3 => natSyms u2 ++ [.tag 3]
  | .inl .RQ => entrySyms alt ++ junk
  | _ => junk

/-- One column of `W9_columnSolve`: `(all stacks as the contract says, steps, differing keys)`. -/
def runCol (h : PostHdr) (u2 : ℕ) (c0 c1 alt : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    Bool × ℕ × List ℕ :=
  let rc := postRecSyms c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1)
  let w0 := blkE (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1 Y
    alt).toList
  let S := colSt0 h u2 alt Y rc
  let E := Function.update (Function.update (Function.update S (.inl .W0) w0) (.inl .TR) [.tag 4])
    (.inl .TL) (rc.reverse ++ S (.inl .TL))
  match WP.W9f.RunR.runTabledR progC r0C keys normRC ⟨r0C, S⟩ 200000000 with
  | none => (false, 0, [])
  | some (n, S') =>
    let bad := ((keys.zip (List.range keys.length)).filter fun p => S' p.1 != E p.1).map (·.2)
    (bad.isEmpty, n, bad)

/-- `(p, pSub, t1, r, pChild)`: `t1 = 4`, `r = 8` (`r/2 = 4`), `H = 8`. -/
def hA : PostHdr := ⟨3, 2, 4, 8, 4⟩

/-- A nonzero column. -/
def Yp : Array (ℤ × ℤ) := #[(1, -2), (0, 2), (-2, 1), (2, 0)]

/-- Run `f`, fail unless the stacks are as the contract says, and add the wall time in ms. -/
def check (name : String) (f : Unit → Bool × ℕ × List ℕ) : IO (Bool × ℕ × List ℕ × ℕ) := do
  let t0 ← IO.monoMsNow
  let r := f ()
  unless r.1 do throw (IO.userError s!"{name}: stacks differ from the contract: {r}")
  let t1 ← IO.monoMsNow
  return (r.1, r.2.1, r.2.2, t1 - t0)

-- `(stacks ok, steps, differing keys, ms)`. Fwd: `u2 = 1`, divisor `c0 = 3`.
#eval check "fwd" fun _ => runCol hA 1 (3, 0) (-2, 0) (1, -1) Yp
-- Nyquist: `u2 = 4`, divisor `c0 = 3`.
#eval check "nyq" fun _ => runCol hA 4 (3, 0) (-2, 0) (1, -1) Yp
-- Bwd: `u2 = 6`, divisor `c1 = 2`.
#eval check "bwd" fun _ => runCol hA 6 (-1, 0) (2, 0) (1, -1) Yp

#assert_std_axioms keys_complete

end WP.W9f.ConcreteRun
