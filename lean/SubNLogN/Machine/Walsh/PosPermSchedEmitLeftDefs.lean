/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitSt

/-!
# Schedule compiler emitter, the leftover pass: program and contract (`PosPermSchedEmitLeftDefs.lean`)

The last part of one stage of the emitter (`StageEmitSpec`, `PosPermSchedState.lean`). The pairs of
the stage whose target is `≥ JK` (`leftPairs`) are emitted one by one, in increasing position order,
as single flips `PosCmd.one c t` (Theorem 5.8, `thm:positional-perm`). The program `lLoop IT stA` is fixed here, and
`LeftPassStmt` is its contract, stated on the emitter states `st S₀ v acc bt`
(`PosPermSchedEmitSt.lean`).

**Scope (honest summary).** Definitions and one contract, no proofs here (except closedness). The
contract is proved as `leftPass_holds` (`PosPermSchedEmitLeft.lean`).
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh

/-- Emit a single flip `(c, t)`: `tag 1`, the fields `t`, `c`, `1`, then `sep2`. The accumulator
then gains `(cmdSyms (.one c t)).reverse` (`one_acc`). -/
def emitOne : SProg Stk :=
  .seq (pushA (Sym.tag 1)) (.seq (copyR .t .b) (.seq (emitA .b) (.seq (copyR .c .b)
    (.seq (emitA .b) (.seq (inc .b) (.seq (emitA .b) (pushA Sym.sep2)))))))

/-- A leftover candidate at position `xu` (with `xu < y = I xu`): emit it iff `t ≥ JK`. -/
def lPair (stA : Bool) : SProg Stk :=
  .seq (ctSet stA .xu) (.seq (ltR .t .JK .e0) (.seq (ifR .e0 skip emitOne)
    (.seq (clr .c) (.seq (clr .t) (clr .e0)))))

/-- One position of the leftover pass (increasing positions; `xu` counts up). -/
def lBody (IT : RawN) (stA : Bool) : SProg Stk :=
  .seq (lookR IT .xu .y) (.seq (ltR .xu .y .f) (.seq (ifR .f (lPair stA) skip)
    (.seq (clr .f) (.seq (clr .y) (inc .xu)))))

/-- **The leftover pass**: `len := m`, then `m` positions, then `xu := 0`. -/
def lLoop (IT : RawN) (stA : Bool) : SProg Stk :=
  .seq (copyR .m .len) (.seq (loopR .len (lBody IT stA)) (clr .xu))

/-- The registers of the leftover pass, cleared. -/
def lz (v : RegN → ℕ) : RegN → ℕ := fun r =>
  match r with
  | .xu | .len | .y | .f | .c | .t | .e0 | .b => 0
  | r => v r

/-- **[CONTRACT, proved: `leftPass_holds`, `PosPermSchedEmitLeft.lean`] The leftover pass of one
stage** (Theorem 5.8 (`thm:positional-perm`); `stageCmds`,
`PosPermLeaf.lean`).
* Setting: the table stack `IT` (`I0T` or `I1T`) holds `utab (finVals I)`. The scratch raw stacks
  `U`, `B1` are empty. The registers hold `lz v`, i.e. `v` with the pass's own registers cleared,
  where `v .m = m`, `v .K > 0` and `v .JK = numChunks m K · K`. The batch buffer is empty.
* Effect: the accumulator gains `(schedSyms L).reverse` and nothing else changes. Here `L` is the
  list of single flips of the stage's pairs with target `≥ JK`, in position order:
  `(leftPairs K stagePairs).map one`, via `leftPairs_stage` and `stage_eq`.
* Cost `(m + 1)·100·opW V` for any `V ≥ 1` bounding `m`, the table length and `JK`. -/
def LeftPassStmt : Prop :=
  ∀ (S₀ : Stk → List Sym) (IT : RawN), (IT = .I0T ∨ IT = .I1T) →
    ∀ (m : ℕ) (I : Fin m → Fin m) (stA : Bool) (v : RegN → ℕ) (acc : List Sym) (V : ℕ),
      S₀ (rs IT) = utab (finVals I) → S₀ (rs .U) = [] → S₀ (rs .B1) = [] →
      v .m = m → 0 < v .K → v .JK = numChunks m (v .K) * v .K →
      1 ≤ V → m ≤ V → (utab (finVals I)).length ≤ V → v .JK ≤ V →
      Runs (lLoop IT stA) (st S₀ (lz v) acc [])
        (st S₀ (lz v)
          ((schedSyms (((List.finRange m).filterMap
              (fun x => (pairOf stA I x).filter (leftQ (v .K)))).map
            (fun p => (PosCmd.one p.1 p.2 : PosCmd m (v .K))))).reverse ++ acc) [])
        (fun _ => True) ((m + 1) * (100 * opW V))

theorem closed_lLoop (IT : RawN) (stA : Bool) : (lLoop IT stA).Closed := by
  cases stA <;>
  simp [lLoop, lBody, lPair, emitOne, ctSet, copyR, ltR, lookR, emitA, pushA, clr, inc, ifR,
    loopR, copyU, ltF, lookup, PSIO.emitField, PSIO.halveStep, PSIO.halveBody, PSIO.moveAll, clearU,
    incR, ifNE, forDown, whileNE, whileTop, moveU, mv, skipEntry, moveToks, copyToks, drainTo,
    popR, pushR, peekR, pushC, skip, Prog.Closed, Prog.FreeBelow]

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
