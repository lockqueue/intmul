import WP.W9fM.Move
import IntMulTM.Framework.Sim

/-!
# WP.W9fM.Smoke — run the compiled entry mover (`#eval`)

`runProg` is a copy of `WP.W6a.Smoke.runProg` (this keeps the package standalone). It runs the
compiled machine `machine moveEntriesProg none` (framework `Sim`) under Mathlib's `TM2.step`; no
`toFinTM2`. By `machine_run`, a run that halts after `n` steps has `Eval` cost `n − 1`.

Each row starts from source `blkE xs ++ [tag 0]` (`tag 0` is not an entry start, so `NotEntry`
holds), destination `[tag 6]` and scratch `[bit true]`. It checks:

* the destination is `blkE xs.reverse ++ [tag 6]` (entry order reversed, symbols in order);
* the source is left as `[tag 0]`;
* the scratch stack is restored;
* the cost `n − 1` against the proved bound `16·(|blkE xs| + 1)`.
-/

namespace WP.W9fM.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. On halting,
return the number of steps and the final user stacks. -/
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

/-- `(|blkE xs|, dst ok, src ok, scratch ok, cost, proved bound)`. -/
def row (xs : List (ℤ × ℤ)) : ℕ × Bool × Bool × Bool × ℕ × ℕ :=
  let S : MStk → List Sym := fun k =>
    if k = .inl 0 then blkE xs ++ [Sym.tag 0] else if k = .inl 1 then [Sym.tag 6]
    else [Sym.bit true]
  match runProg moveEntriesProg none S 100000 with
  | none => ((blkE xs).length, false, false, false, 0, 0)
  | some (n, S') =>
    ((blkE xs).length, S' (.inl 1) == blkE xs.reverse ++ [Sym.tag 6], S' (.inl 0) == [Sym.tag 0],
      S' (.inr 0) == [Sym.bit true], n - 1, 16 * ((blkE xs).length + 1))

#eval [row [], row [(1, -2)], row [(1, -2), (0, 5), (-3, 0)], row [(12, -7), (0, 0)],
  row [(-1, 1), (2, -3), (0, 0), (100, -100)]]

end WP.W9fM.Smoke
