import WP.W9cS.Main
import IntMulTM.Framework.Sim

/-!
# WP.W9cS.Smoke — run the compiled spread driver (`#eval`)

The driver is parametrized by the row kernel, a hypothesis here. To run it we plug in
`fakeKer`, **unverified test scaffolding** used by no theorem: it leaves `W0` unchanged (so the
"spread" of each row is the row itself) and moves one filter row `TR → TL`.

Each row checks `W0` (rows reassembled in order), `TR`/`TL` (filter rows moved, reversed),
that every other stack (header `C0`, `C1`, six scratch stacks with junk) is restored, and the
step count of the compiled machine.
-/

namespace WP.W9cS.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 WP.W9c Computability Turing

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

/-- Test kernel (unverified): `W0` unchanged, one filter row moved `TR → TL`. -/
def fakeKer : Prog (BLoc 0) (fun _ => Sym) (Option Sym) :=
  .seq (peekR (.inl .TR)) (.seq (.loop (fun r => decide (r ≠ some symSub))
    (.seq (popR (.inl .TR)) (.seq (pushR (.inl .TL)) (peekR (.inl .TR)))))
    (.seq (popR (.inl .TR)) (pushR (.inl .TL))))

/-- Test entries. -/
def ents (n : ℕ) : List (ℤ × ℤ) := (List.range n).map fun i => ((i : ℤ) - 3, 2 * (i : ℤ) + 1)

/-- `(W0 ok, TR ok, TL ok, frame ok, steps)` for `t1` rows of `r` entries. -/
def row (t1 r : ℕ) (ft : Array (List ℤ)) : Bool × Bool × Bool × Bool × ℕ :=
  let junk : List Sym := [Sym.tag 5, Sym.bit true]
  let c0 : List Sym := hdrSyms (preTapeFields 1 1 t1 r) ++ [Sym.tag 7]
  let c1 : List Sym := hdrSyms [5]
  let S : BLoc (max 0 6) → List Sym := fun k =>
    match k with
    | .inl .W0 => blkE (ents (t1 * r))
    | .inl .TR => filterRowsSyms t1 ft ++ [Sym.tag 9]
    | .inl .TL => [Sym.tag 8]
    | .inl .C0 => c0
    | .inl .C1 => c1
    | .inl _ => [Sym.tag 10]
    | .inr _ => junk
  match runProg (spreadProg fakeKer) ((none, none) : Option Sym × Option Sym) S 100000 with
  | none => (false, false, false, false, 0)
  | some (n, S') =>
    (S' (.inl .W0) == blkE (ents (t1 * r)), S' (.inl .TR) == [Sym.tag 9],
      S' (.inl .TL) == (filterRowsSyms t1 ft).reverse ++ [Sym.tag 8],
      S' (.inl .C0) == c0 && S' (.inl .C1) == c1 && S' (.inl .S) == [Sym.tag 10] &&
        (List.range 6).all (fun i => if h : i < max 0 6 then S' (.inr ⟨i, h⟩) == junk else true),
      n - 1)

#eval [row 2 4 #[[1, -2], [3]], row 2 2 #[[], [7]], row 4 4 #[[1], [2, 3], [], [-4]],
  row 1 3 #[[5, 6, 7]]]

end WP.W9cS.Smoke
