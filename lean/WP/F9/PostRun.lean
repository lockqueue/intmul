import WP.F9.Post
import WP.F9.Run

/-!
# WP.F9.PostRun — stage runs of the concrete POST routing phases

`q2L`, `q34L` and `q6L` (WP.F9.Post) are the W9e phase programs with the verified W3 and W4
subroutines. Here they run under `runTabled`, i.e. the framework machine itself, by `tabled_eq` and
`runTabled_sound`.

* Start: `W0` holds the phase input, `C0` holds the POST header followed by a tail, and every other
  stack holds junk.
* Check: every one of the 28 local stacks after the run. `W0` must hold the snapshot value
  (`w9QHatT`, `w9Y ∘ w9ColRoutes`, `w9Out`); every other stack must be restored.

Each row is `(stacks ok, steps)`, with steps counted as in `machine_run` (cost + 1). The cases are
`t1 = 2`, `r ∈ {2, 4}`, and both rescale directions.
-/

namespace WP.F9.PostRun

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

/-- Arbitrary content of private stacks (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All local stacks. -/
def allStk : List WP.W9e.Stk :=
  [.w0, .c0, .tmp, .ka, .kb, .dd, .ee, .x, .x2, .y, .acc, .ks, .t1s, .cnt, .u, .ws, .bs, .pin,
    .pout, .dist, .dist1, .ms, .sg, .lo, .s 0, .s 1, .s 2, .s 3]

/-- Initial stacks: `W0`, the header on `C0` with a tail, junk elsewhere. -/
def st0 (h : PostHdr) (w0 : List Sym) : WP.W9e.Stk → List Sym
  | .w0 => w0
  | .c0 => hdrSyms (postFields h.p h.pSub h.t1 h.r h.pChild) ++ [.tag 2, .bit true]
  | _ => junk

/-- Run a phase program: `(all stacks as specified, steps)`. -/
def runRow {σ : Type} (p : Prog WP.W9e.Stk (fun _ => Sym) σ) (σ0 : σ)
    (S E : WP.W9e.Stk → List Sym) : Bool × ℕ :=
  match runTabled p σ0 allStk ⟨σ0, S⟩ 3000000 with
  | none => (false, 0)
  | some (n, S') => (allStk.all fun k => S' k == E k, n)

/-- Q2 on `qHat` (`t1 × r`). -/
def rowQ2 (h : PostHdr) (qHat : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 h (matSyms qHat)
  runRow q2L q2r0 S (Function.update S .w0 (blkE (w9QHatT h.t1 h.r qHat).toList))

/-- Q3+Q4 on `qHatT` (`N` entries). -/
def rowQ34 (h : PostHdr) (qHatT : Array (ℤ × ℤ)) : Bool × ℕ :=
  let S := st0 h (blkE qHatT.toList)
  runRow q34L q34r0 S
    (Function.update S .w0 (matSyms (w9Y h.pSub h.t1 h.r h.pChild (w9ColRoutes h.t1 h.r qHatT))))

/-- Q6 on `Zc` (`r × t1`). -/
def rowQ6 (h : PostHdr) (Zc : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 h (matSyms Zc)
  runRow q6L q6r0 S (Function.update S .w0 (nodeSyms (w9Out h.p h.pSub h.t1 h.r Zc)))

/-- `(p, pSub, t1, r, pChild)`: Q4 shifts left by 1, Q6 right by 2. -/
def hA : PostHdr := ⟨3, 5, 2, 2, 4⟩
/-- Q4 right by 2, Q6 right by 1. -/
def hD : PostHdr := ⟨2, 3, 2, 2, 5⟩
/-- Non-square (`t1 = 2`, `r = 4`); Q4 right by 2, Q6 left by 2. -/
def hB : PostHdr := ⟨6, 4, 2, 4, 6⟩

def rowsQ2 : List (Bool × ℕ) :=
  [rowQ2 hA (mkMat 2 2 0), rowQ2 hD (mkMat 2 2 5), rowQ2 hB (mkMat 2 4 1)]
def rowsQ34 : List (Bool × ℕ) :=
  [rowQ34 hA (mkArr 4 0), rowQ34 hD (mkArr 4 7), rowQ34 hB (mkArr 8 3)]
def rowsQ6 : List (Bool × ℕ) :=
  [rowQ6 hA (mkMat 2 2 0), rowQ6 hD (mkMat 2 2 3), rowQ6 hB (mkMat 4 2 1)]

/-- `allStk` lists every local stack. -/
theorem allStk_complete : ∀ k : WP.W9e.Stk, k ∈ allStk := by
  intro k
  cases k with
  | s i => fin_cases i <;> decide
  | _ => decide

-- Q2, Q3+Q4, Q6 with the verified subroutines: `(stacks ok, steps)`.
#eval rowsQ2
#eval rowsQ34
#eval rowsQ6
#guard (rowsQ2 ++ rowsQ34 ++ rowsQ6).all (·.1)

#assert_std_axioms allStk_complete

end WP.F9.PostRun
