import WP.W9f.Concrete
import WP.W9f.RunR

/-!
# WP.W9f.ConcreteColsRun — a tabled run of the concrete columns stage

`progColsC` (WP.W9f.Concrete) is S3's driver `WP.W9fC.colsProg` on the real column solver `progC`.
It runs under `WP.W9f.RunR.runTabledR` with the identity register map `normColsC`
(`runTabledR_sound`; `keys_complete` lists every stack).

The run is one POST node: `t1 = 2`, `r = 2`, `pSub = 2` (`H = 8`). Column `u2 = 0` is fwd and
`u2 = 1` is Nyquist; `WP.W9f.ConcreteRun` runs a bwd column (the driver does not depend on the
regime). The column divisors are positive, the tables are real
(`.2 = 0`), and the entries and `alt` are nonzero. The `W9_columns` premises are not formally verified
here. The run checks the contract's final stacks exactly:
* `W0 = matSyms (w9ZBarrett pSub t1 r c0T c1T alt Y)`, the contract value;
* `TR := restT`, `TL := (postBody …).reverse ++ TL`, `RQ := rq`;
* every other stack is restored (junk starts on every scratch and private stack).

The row is `(stacks ok, steps, indices in keys of the stacks that differ, wall ms)`.
-/

namespace WP.W9f.ConcreteColsRun

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9f WP.W9f.Concrete IntMul

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 5]

/-- All stacks of `BLoc mColsC`. -/
def keys : List (BLoc mColsC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange mColsC).map .inr

theorem keys_complete : ∀ k : BLoc mColsC, k ∈ keys := by
  intro k
  rcases k with k | k
  · cases k <;> simp [keys]
  · simp [keys]

/-- Start stacks: `W0 = matSyms Y`, the POST body on `TR`, the header on `C0`, `alt` on `RQ`, junk
elsewhere. -/
def colsSt0 (h : PostHdr) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ) (Y : Array (Array (ℤ × ℤ))) :
    BLoc mColsC → List Sym
  | .inl .W0 => matSyms Y
  | .inl .TR => postBody h.pSub h.r c0T c1T ++ [.tag 4]
  | .inl .C0 => hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ junk
  | .inl .RQ => entrySyms alt ++ junk
  | _ => junk

/-- One node of `W9_columns`: `(all stacks as the contract says, steps, differing keys)`. -/
def runCols (h : PostHdr) (c0T c1T : Array (ℤ × ℤ)) (alt : ℤ × ℤ) (Y : Array (Array (ℤ × ℤ))) :
    Bool × ℕ × List ℕ :=
  let S := colsSt0 h c0T c1T alt Y
  let body := postBody h.pSub h.r c0T c1T
  let E := Function.update (Function.update (Function.update (Function.update S (.inl .W0)
      (matSyms (w9ZBarrett h.pSub h.t1 h.r c0T c1T alt Y))) (.inl .TR) [.tag 4])
      (.inl .TL) (body.reverse ++ S (.inl .TL))) (.inl .RQ) junk
  match WP.W9f.RunR.runTabledR progColsC r0ColsC keys normColsC ⟨r0ColsC, S⟩ 400000000 with
  | none => (false, 0, [])
  | some (n, S') =>
    let bad := ((keys.zip (List.range keys.length)).filter fun p => S' p.1 != E p.1).map (·.2)
    (bad.isEmpty, n, bad)

/-- `(p, pSub, t1, r, pChild)`: `t1 = 2`, `r = 2` (`r/2 = 1`), `H = 8`. -/
def hB : PostHdr := ⟨3, 2, 2, 2, 4⟩

/-- `c0` table: the divisors of the fwd and Nyquist columns. -/
def c0B : Array (ℤ × ℤ) := #[(3, 0), (2, 0)]

/-- `c1` table: the multipliers. -/
def c1B : Array (ℤ × ℤ) := #[(-1, 0), (1, 0)]

/-- Two columns of two entries. -/
def YB : Array (Array (ℤ × ℤ)) := #[#[(1, -2), (2, 0)], #[(0, 1), (-2, 2)]]

/-- Run `f`, fail unless the stacks are as the contract says, and add the wall time in ms. -/
def check (name : String) (f : Unit → Bool × ℕ × List ℕ) : IO (Bool × ℕ × List ℕ × ℕ) := do
  let t0 ← IO.monoMsNow
  let r := f ()
  unless r.1 do throw (IO.userError s!"{name}: stacks differ from the contract: {r}")
  let t1 ← IO.monoMsNow
  return (r.1, r.2.1, r.2.2, t1 - t0)

-- `(stacks ok, steps, differing keys, ms)`.
#eval check "columns" fun _ => runCols hB c0B c1B (1, -1) YB

#assert_std_axioms keys_complete

end WP.W9f.ConcreteColsRun
