import WP.W9c.RowSplit
import WP.W9c.RowZip
import WP.W9c.RowHdr
import WP.W9c.RowTaps
import IntMulTM.Framework.Sim

/-!
# WP.W9c.RowSmoke — run the four row kernels (`#eval`)

`runProg` runs the compiled machine `machine p σ0` under Mathlib's `TM2.step` (the
`WP.W6a.Smoke` harness); a run halting after `n` steps has `Eval` cost `n − 1` (`machine_run`).
Each row: `(outputs ok, frame ok, steps, proved bound)`.
-/

namespace WP.W9c.RowSmoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing IntMul

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. -/
def runProg {K : Type} [DecidableEq K] {σ : Type} (p : Prog K (fun _ => Sym) σ) (σ0 : σ)
    (S : K → List Sym) (fuel : ℕ) : Option (ℕ × (K → List Sym)) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk S []⟩
where
  /-- the step loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)) → Option (ℕ × (K → List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, fun k => c.stk (some k))
      | some c' => go fuel (n + 1) c'

/-- Split. -/
def rowSplitT (v : List (ℤ × ℤ)) : Bool × Bool × ℕ × ℕ :=
  let S : Loc 3 1 → List Sym := fun k => if k = .inl 0 then blkE v else []
  match runProg RowSplit.splitProg (none : Option Sym) S 100000 with
  | none => (false, false, 0, 0)
  | some (n, S') =>
    (S' (.inl 1) == listSyms (v.map Prod.fst) && S' (.inl 2) == listSyms (v.map Prod.snd),
      S' (.inl 0) == [] && S' (.inr 0) == [], n - 1, 10 * ((blkE v).length + 1))

/-- Zip (the pass outputs keep their guard `mark`). -/
def rowZipT (a b : List ℤ) : Bool × Bool × ℕ × ℕ :=
  let S : Loc 3 1 → List Sym := fun k =>
    if k = .inl 0 then listSyms a.reverse ++ [Sym.mark]
    else if k = .inl 1 then listSyms b.reverse ++ [Sym.mark] else []
  match runProg RowZip.zipProg (none : Option Sym) S 100000 with
  | none => (false, false, 0, 0)
  | some (n, S') =>
    (S' (.inl 2) == blkE (List.zip a b),
      S' (.inl 0) == [Sym.mark] && S' (.inl 1) == [Sym.mark] && S' (.inr 0) == [], n - 1,
      6 * ((listSyms a).length + (listSyms b).length + 1))

/-- Header. -/
def rowHdrT (pSub m1 t1 r p_in : ℕ) : Bool × Bool × ℕ × ℕ :=
  let S : Loc 9 1 → List Sym := fun k =>
    if k = .inl 0 then hdrSyms (preTapeFields pSub m1 t1 r)
    else if k = .inl 1 then hdrSyms [p_in] else []
  match runProg RowHdr.hdrProg (none : Option Sym) S 1000000 with
  | none => (false, false, 0, 0)
  | some (n, S') =>
    (S' (.inl 2) == natSyms pSub && S' (.inl 3) == natSyms m1 && S' (.inl 4) == natSyms r &&
        S' (.inl 5) == natSyms (natLog2Fuel r r) &&
        S' (.inl 6) == natSyms (effectiveFilterWidth m1 r) &&
        S' (.inl 7) == natSyms (strideOf pSub) && S' (.inl 8) == natSyms p_in,
      S' (.inl 0) == hdrSyms (preTapeFields pSub m1 t1 r) && S' (.inl 1) == hdrSyms [p_in] &&
        S' (.inr 0) == [],
      n - 1, 85 * ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 1))

/-- Filter row (the tape continues with `symGuard`). -/
def rowTapsT (taps : List ℤ) : Bool × Bool × ℕ × ℕ :=
  let S : Loc 4 3 → List Sym := fun k => if k = .inl 0 then filterRowSyms taps ++ [symGuard] else []
  match runProg RowTaps.tapsProg (none : Option Sym) S 1000000 with
  | none => (false, false, 0, 0)
  | some (n, S') =>
    (S' (.inl 1) == (filterRowSyms taps).reverse && S' (.inl 2) == listSyms taps &&
        S' (.inl 3) == natSyms taps.length,
      S' (.inl 0) == [symGuard] && S' (.inr 0) == [] && S' (.inr 1) == [] && S' (.inr 2) == [],
      n - 1, 30 * ((filterRowSyms taps).length + 1))

#eval [rowSplitT [(1, -2), (3, 0), (-5, 7)], rowSplitT [], rowSplitT [(0, 0)],
  rowSplitT [(12, -9), (-1, 1), (0, 6), (7, -7)]]

#eval [rowZipT [1, -2, 3] [0, 5, -7], rowZipT [] [], rowZipT [4] [-4],
  rowZipT [12, -1, 0, 7] [-9, 1, 6, -7]]

#eval [rowHdrT 6 2 4 8 3, rowHdrT 10 3 8 16 5, rowHdrT 0 0 2 2 0]

#eval [rowTapsT [1, -2, 3], rowTapsT [], rowTapsT [0, 7, -8, 9, 1], rowTapsT [-1]]

end WP.W9c.RowSmoke
