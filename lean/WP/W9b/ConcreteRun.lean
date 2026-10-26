import WP.W9b.Concrete
import WP.F9.Run

/-!
# WP.W9b.ConcreteRun — execution checks of the concrete P1, P2, P8 kernels

`Concrete.P1.progC`, `P2.progC` and `P8.progC` run from `r0C` under `WP.F9.runTabled`, which steps
the framework machine itself (`tabled_eq`). Since `keysB` is complete (`keysB_complete`),
`runTabled_sound` turns each result into a halting run of `machine progC r0C`. The file is adapted
from `WP.F9.PreBRun`.
* Start: the stacks of each contract. `W0` holds the input, `C0` holds the PRE header followed by
  a tail, `C1` holds `p_in` followed by a tail, and every other stack, scratch included, holds junk.
* Check: all `12 + mC` stacks after the run, against the contract's post-state with the snapshot
  value: `w9XRows` for P1, the reversed `alt_q` (`computableNyquistAltSumContiguous`) pushed on
  `RET` for P2, and the node stream for P8.

Each row is `(stacks ok, steps)`, with steps counted as in `machine_run` (cost + 1). The headers
are square (`t1 = r = 2`) and non-square (`t1 = 2`, `r = 4`, `p_in < pSub`); both satisfy
`PreDims`.
-/

namespace WP.W9b.ConcreteRun

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

/-- `keysB m` lists every stack (the premise of `runTabled_sound`). -/
theorem keysB_complete (m : ℕ) : ∀ k : BLoc m, k ∈ keysB m := by
  intro k
  rcases k with l | i
  · cases l <;> simp [keysB]
  · simp [keysB]

/-- Start stacks: `W0`, the PRE header on `C0`, `p_in` on `C1` (with tails), junk elsewhere. -/
def st0 (m : ℕ) (h : PreHdr) (w0 : List Sym) : BLoc m → List Sym
  | .inl .W0 => w0
  | .inl .C0 => hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ [.tag 2, .bit true]
  | .inl .C1 => hdrSyms [h.p_in] ++ [.tag 3]
  | _ => junk

/-- Run `p` from `σ0`: `(all stacks as specified, steps)`. -/
def runRow {m : ℕ} {σ : Type} (p : Prog (BLoc m) (fun _ => Sym) σ) (σ0 : σ)
    (S E : BLoc m → List Sym) : Bool × ℕ :=
  match runTabled p σ0 (keysB m) ⟨σ0, S⟩ 3000000 with
  | none => (false, 0)
  | some (n, S') => ((keysB m).all fun k => S' k == E k, n)

/-- P1 on `x` (`N` entries): `W0` becomes `w9XRows`. -/
def rowP1 (h : PreHdr) (x : Array (ℤ × ℤ)) : Bool × ℕ :=
  let S := st0 Concrete.P1.mC h (blkE x.toList)
  runRow Concrete.P1.progC Concrete.P1.r0C S
    (Function.update S (.inl .W0) (matSyms (w9XRows h.t1 h.r x)))

/-- P2 on `xRows` (`t1 × r`): the reversed `alt_q` of row `t1/2` is pushed on `RET`. -/
def rowP2 (h : PreHdr) (xRows : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 Concrete.P2.mC h (matSyms xRows)
  runRow Concrete.P2.progC Concrete.P2.r0C S (Function.update S (.inl .RET)
    ((entrySyms (computableNyquistAltSumContiguous h.p_in h.pSub h.r
      (xRows.getD (h.t1 / 2) #[]))).reverse ++ S (.inl .RET)))

/-- P8 on `M` (`t1 × r`): `W0` becomes the `t1` nodes. -/
def rowP8 (h : PreHdr) (M : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 Concrete.P8.mC h (matSyms M)
  runRow Concrete.P8.progC Concrete.P8.r0C S
    (Function.update S (.inl .W0) (M.toList.flatMap nodeSyms))

/-- `(p_in, pSub, m1, t1, r)`: square. -/
def hA : PreHdr := ⟨5, 4, 1, 2, 2⟩
/-- Non-square (`t1 = 2`, `r = 4`), `p_in < pSub`. -/
def hB : PreHdr := ⟨3, 6, 1, 2, 4⟩

/-- Print the rows; fail (and so fail the build) unless every stack matches. -/
def check (name : String) (rows : List (Bool × ℕ)) : IO Unit := do
  IO.println s!"{name}: {rows}"
  unless rows.all (·.1) do throw (IO.userError s!"{name}: stack mismatch")

-- P1, with `WP.Inst.transpose`: `(stacks ok, steps)`.
#eval check "P1" [rowP1 hA (mkArr 4 0), rowP1 hB (mkArr 8 3)]
-- P2, with the `WP.Inst` W3 kit.
#eval check "P2" [rowP2 hA (mkMat 2 2 1), rowP2 hB (mkMat 2 4 2)]
-- P8.
#eval check "P8" [rowP8 hA (mkMat 2 2 4), rowP8 hB (mkMat 2 4 5)]

#assert_std_axioms keysB_complete

end WP.W9b.ConcreteRun
