import WP.W9b.AltSum

/-!
# WP.W9b.Smoke — run the compiled machines (`#eval`)

`runProg` runs the compiled machine `machine p σ0` (framework `Sim`) under Mathlib's `TM2.step`
(the `WP.W6a.Smoke` harness). By `machine_run`, a run that halts after `n` steps has `Eval` cost
`n − 1`.

| kernel | run here | checked |
|---|---|---|
| P8 `emitProg` (`W9_emitRows`) | yes | output, frame, steps ≤ local bound (`emit_runs`) ≤ `35·emitBound` |
| P2 skip loop `skipRows` (part of `W9_altSum`) | yes (it calls no W3 program) | output, frame, steps ≤ `rs_skipRows` bound |
| P2 value bridge (`nyq_eq_acc`) | yes (pure) | snapshot value = rescaled pair accumulators |
| P2 full kernel, P1 kernel | **no** | they call the W3 / W4 programs, which are hypotheses here (rule 6) |

`kit0` is **unverified test scaffolding** (every W3 slot is `Lib.skip`); it is only used to run
`skipRows`, which never calls a W3 slot, and by no theorem.
-/

namespace WP.W9b.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability Turing
open IntMul (gRescale computableNyquistAltSumContiguous)

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

/-! ## P8: the emit kernel -/

/-- Initial stacks of the emit kernel: `W0 = matSyms M`, `C0` = the PRE header, the rest empty. -/
def eInit (pSub m1 t1 r : ℕ) (M : Array (Array (ℤ × ℤ))) : EStk → List Sym
  | .W0 => matSyms M
  | .C0 => hdrSyms (preTapeFields pSub m1 t1 r)
  | _ => []

/-- The local bound of `emit_runs`. -/
def emitLocal (pSub m1 t1 r : ℕ) (M : Array (Array (ℤ × ℤ))) : ℕ :=
  6 * (matSyms M).length + 23 * (t1 * r) + 31 * t1 +
    29 * (hdrSyms (preTapeFields pSub m1 t1 r)).length + 35

/-- `(t1, r, output ok, frame ok, steps, local bound, 35·emitBound)`. -/
def rowEmit (pSub m1 w : ℕ) (M : Array (Array (ℤ × ℤ))) : ℕ × ℕ × Bool × Bool × ℕ × ℕ × ℕ :=
  let t1 := M.size
  let r := (M.getD 0 #[]).size
  match runProg emitProg (none : Option Sym) (eInit pSub m1 t1 r M) 200000 with
  | none => (t1, r, false, false, 0, 0, 0)
  | some (n, S) =>
    (t1, r, S .W0 == M.toList.flatMap nodeSyms,
      S .C0 == hdrSyms (preTapeFields pSub m1 t1 r) && S .T == [] && S .R == [] &&
        S .K == [] && S .J == [] && S .H == [] && S .t == [],
      n - 1, emitLocal pSub m1 t1 r M, 35 * emitBound w ⟨0, pSub, m1, t1, r⟩)

/-! ## P2: the skip loop (no W3 calls) and the value bridge -/

/-- Test-only kit: every W3 slot is `Lib.skip` (unverified; `skipRows` never calls a slot). -/
def kit0 : W3Kit :=
  ⟨0, Unit, Lib.skip, by decide, 0, Unit, Lib.skip, by decide, 0, Unit, Lib.skip, by decide,
    0, Unit, Lib.skip, by decide, 0, Unit, Lib.skip, by decide, 0, Unit, Lib.skip, by decide⟩

/-- Initial registers for `kit0`. -/
def σk : KReg kit0 := (none, (none, none, .eq), (), (), (), (), (), ())

/-- Stacks before `skipRows`: the matrix on `W0`, `J = t1/2`, `R = r`, guards on `K`, `T`. -/
def sInit (M : Array (Array (ℤ × ℤ))) (j r : ℕ) : AStk → List Sym
  | .W0 => matSyms M
  | .J => natSyms j ++ [Sym.mark]
  | .R => natSyms r ++ [Sym.mark]
  | .K => [Sym.mark]
  | .T => [Sym.mark]
  | _ => []

/-- The bound of `rs_skipRows`. -/
def skipBound (r : ℕ) (rows : List (Array (ℤ × ℤ))) : ℕ :=
  3 * (blkE (rows.flatMap Array.toList)).length +
    rows.length * (7 * bitLen r + 9 + decSum r + 2 * r) + decSum rows.length + 2 * rows.length + 2

/-- `(rows skipped, W0 ok, T ok, frame ok, steps, proved bound)`. -/
def rowSkip (M : Array (Array (ℤ × ℤ))) : ℕ × Bool × Bool × Bool × ℕ × ℕ :=
  let t1 := M.size
  let r := (M.getD 0 #[]).size
  let rows := M.toList.take (t1 / 2)
  let restE := (M.toList.drop (t1 / 2)).flatMap Array.toList
  match runProg (skipRows kit0) σk (sInit M (t1 / 2) r) 200000 with
  | none => (t1 / 2, false, false, false, 0, 0)
  | some (n, S) =>
    (t1 / 2, S .W0 == blkE restE,
      S .T == (blkE (rows.flatMap Array.toList)).reverse ++ [Sym.mark],
      S .J == [Sym.mark] && S .R == natSyms r ++ [Sym.mark] && S .K == [Sym.mark] &&
        S .AR == [] && S .C0 == [],
      n - 1, skipBound r rows)

/-- Value bridge on row `t1/2` (`r = 2^mr`): `(snapshot value, rescaled accumulators, equal)`. -/
def rowVal (p_in pSub mr : ℕ) (row : Array (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) × Bool :=
  let a := computableNyquistAltSumContiguous p_in pSub (2 ^ mr) row
  let b := gRescale (mr + p_in) pSub (accIm (pairUp row.toList), accRe (pairUp row.toList))
  (a, b, a == b)

/-- Test matrices (entries of width `≤ 2`). -/
def M22 : Array (Array (ℤ × ℤ)) := #[#[(1, -2), (3, 0)], #[(-1, 1), (2, 2)]]
/-- `2 × 4`. -/
def M24 : Array (Array (ℤ × ℤ)) :=
  #[#[(1, 0), (0, 1), (2, -3), (-1, -1)], #[(3, 3), (0, 0), (-2, 1), (1, 2)]]
/-- `4 × 4`. -/
def M44 : Array (Array (ℤ × ℤ)) :=
  #[#[(1, 0), (0, 1), (2, -3), (-1, -1)], #[(3, 3), (0, 0), (-2, 1), (1, 2)],
    #[(0, -1), (1, 1), (3, -2), (2, 0)], #[(-3, 2), (1, -1), (0, 3), (2, 2)]]

-- P8: output and frame checked; steps ≤ local bound ≤ 35·emitBound.
#eval [rowEmit 4 2 2 M22, rowEmit 4 2 2 M24, rowEmit 4 2 2 M44]

-- P2 skip loop: rows `0 … t1/2 − 1` moved `W0 → T`; steps ≤ the `rs_skipRows` bound.
#eval [rowSkip M22, rowSkip M24, rowSkip M44]

-- P2 value bridge (`nyq_eq_acc`): left shift (`mr + p_in ≤ pSub`) and rounding shift.
#eval [rowVal 1 6 2 #[(1, 0), (0, 1), (2, -3), (-1, -1)], rowVal 3 1 2 #[(3, 3), (0, 0), (-2, 1), (1, 2)],
  rowVal 2 2 1 #[(5, -7), (3, 1)], rowVal 0 0 2 #[(1, 1), (1, 1), (1, 1), (1, 1)]]

end WP.W9b.Smoke
