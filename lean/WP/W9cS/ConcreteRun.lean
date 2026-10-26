import WP.W9cS.Concrete
import WP.F9.Run

/-!
# WP.W9cS.ConcreteRun — tabled runs of the concrete spread driver

`progC Pr` (WP.W9cS.Concrete) runs under `WP.F9.runTabled` (the framework machine itself:
`tabled_eq`, `runTabled_sound`; `keys_complete` lists every stack). The row kernel is still open,
so the runs plug in `stubRow`, **unverified test scaffolding used by no theorem** (the same as
`WP.W9cS.Smoke.fakeKer`): it leaves `W0` unchanged and moves one filter row `TR → TL`.

* `rowSnap`: all-zero rows. The snapshot's spread of a zero row is zero, so here the stub computes
  the true spread, and the run is checked against the **snapshot value**
  `matSyms (w9UStatic s p_in pSub m1 t1 r ft xRows)` on `W0`, `TR := restT`,
  `TL := (filterRowsSyms t1 ft).reverse ++ TL`, every other stack restored.
* `rowPlumb`: nonzero rows, checked against the driver's contract with the stub as the row kernel
  (`W0` unchanged).
Each row is `(stacks ok, steps)` (steps as in `machine_run`: cost + 1).
-/

namespace WP.W9cS.ConcreteRun

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9c WP.W9cS.Concrete IntMul

/-- **Test scaffolding (unverified)**: `W0` unchanged, one filter row moved `TR → TL`. -/
def stubRow : Prog (BLoc 0) (fun _ => Sym) (Option Sym) :=
  .seq (peekR (.inl .TR)) (.seq (.loop (fun r => decide (r ≠ some symSub))
    (.seq (popR (.inl .TR)) (.seq (pushR (.inl .TL)) (peekR (.inl .TR)))))
    (.seq (popR (.inl .TR)) (pushR (.inl .TL))))

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 5]

/-- All stacks of `BLoc (mC 0)`. -/
def keys : List (BLoc (mC 0)) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange (mC 0)).map .inr

theorem keys_complete : ∀ k : BLoc (mC 0), k ∈ keys := by
  intro k
  rcases k with k | k
  · cases k <;> simp [keys]
  · simp [keys]

/-- Start stacks: `W0 = matSyms xRows`, the filter rows on `TR`, the header on `C0`, `p_in` on
`C1`, junk elsewhere. -/
def st0 (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) :
    BLoc (mC 0) → List Sym
  | .inl .W0 => matSyms xRows
  | .inl .TR => filterRowsSyms h.t1 ft ++ [.tag 9]
  | .inl .C0 => hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ junk
  | .inl .C1 => hdrSyms [h.p_in] ++ junk
  | _ => junk

/-- Run with expected `W0` content `w0`: `(all stacks as the contract says, steps)`. -/
def runRow (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) (w0 : List Sym) :
    Bool × ℕ :=
  let S := st0 h ft xRows
  let E := Function.update (Function.update (Function.update S (.inl .W0) w0) (.inl .TR) [.tag 9])
    (.inl .TL) ((filterRowsSyms h.t1 ft).reverse ++ S (.inl .TL))
  match runTabled (progC stubRow) (r0C none) keys ⟨r0C none, S⟩ 2000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- Against the snapshot (all-zero rows). -/
def rowSnap (h : PreHdr) (ft : Array (List ℤ)) : Bool × ℕ :=
  let xRows : Array (Array (ℤ × ℤ)) := Array.ofFn fun _ : Fin h.t1 => Array.ofFn fun _ : Fin h.r => (0, 0)
  runRow h ft xRows (matSyms (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows))

/-- Driver plumbing with the stub kernel (nonzero rows; `W0` unchanged). -/
def rowPlumb (h : PreHdr) (ft : Array (List ℤ)) : Bool × ℕ :=
  let xRows : Array (Array (ℤ × ℤ)) := Array.ofFn fun i : Fin h.t1 => Array.ofFn fun j : Fin h.r =>
    ((i.val : ℤ) - 2 * j.val, 3 * (j.val : ℤ) - 1)
  runRow h ft xRows (matSyms xRows)

/-- `(p_in, pSub, m1, t1, r)`: `W = 3`, two rows of four. -/
def hA : PreHdr := ⟨5, 1, 1, 2, 4⟩
/-- Four rows of four, `W = 3`. -/
def hB : PreHdr := ⟨2, 2, 1, 4, 4⟩

def rows : List (Bool × ℕ) :=
  [rowSnap hA #[[1, -2], [3]], rowSnap hB #[[1], [2, 3], [], [-4]],
    rowPlumb hA #[[1, -2], [3]], rowPlumb hB #[[1], [2, 3], [], [-4]]]

-- `(stacks ok, steps)`: two runs against the snapshot, two plumbing runs.
#eval rows
#guard rows.all (·.1)

#assert_std_axioms keys_complete

end WP.W9cS.ConcreteRun
