/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseProg
import SubNLogN.Machine.CCore.LeafScalarDefs

/-!
# Scalar row leaf: shared definitions of the machine assembly (`CCore/LeafScalarRowDefs.lean`)

**Scope (honest summary).** Definitions only, plus `floorsOK_psS`:
* `psS`: the floor stacks `X, X2, Y, Tm` of the scalar-row program;
* `AccW acc C`: the work-layout (`Lw Er`, `CCore/LeafPhaseBase.lean`) specification of four closed
  accumulation calls `acc c` (one per coefficient `c`), as obtained from `AccStmt`
  (`CCore/LeafScalarDefs.lean:93`) through a `Fin 4` embedding at `X, X2, Y, cW`: the accumulator
  `u` on `X` and the source `v` on `X2` (each above a floor `mark`) are consumed (the floors stay),
  the result `zipC (accC c) u v` is pushed on `Y`, the counter `natSyms w` on `cW` and every other
  stack are restored; the sub-kernel scratch is empty before and after;
* `AccWStmt`: such calls exist (finite scratch, finite nonempty registers);
* `termCost`, `tgtCost`: the exact costs of one term and of one role (used by the loop lemmas).
Paper: the scalar rows of the complex triple network (Definition A.1(b) (`def:fixed-network-premises`),
[OAI26, §3.1]) inside an internal node of Lemma A.10(3) (`lem:transfer-phase`), Section A.5.
-/

namespace SubNLogN.Machine.CCore.LeafScalarRowAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore.LeafScalarAux

/-- The floors of the scalar-row program. -/
abbrev psS : List PS := [.X, .X2, .Y, .Tm]

theorem floorsOK_psS : FloorsOK psS := by
  refine ⟨by decide, ?_⟩
  intro q hq
  simp only [psS, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- **Work-layout specification of the accumulation calls** (see the module doc). -/
def AccW {Er Rr : Type} [DecidableEq Er] (acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr))
    (C : ℕ) : Prop :=
  (∀ c, (acc c).Closed) ∧
  ∀ (c : Coef) (d : List Sym) (sc : PS → List Sym) (w : ℕ) (u v : List (List CInt)),
    1 ≤ w → CAligned u v → CArrFits w v →
    sc .X = carrSyms w u ++ [Sym.mark] → sc .X2 = carrSyms w v ++ [Sym.mark] →
    sc .cW = natSyms w →
    Runs (acc c) (wst d sc (fun _ => []))
      (wst d (Function.update (Function.update (Function.update sc .X [Sym.mark]) .X2
        [Sym.mark]) .Y (carrSyms w (zipC (accC c) u v) ++ sc .Y)) (fun _ => []))
      (fun _ => True) (C * (cvol w u + cvol w v + w + 1))

/-- **The accumulation calls exist**: a finite private scratch `Er`, finite nonempty registers
`Rr`, four closed calls with the specification `AccW` at one constant `C`. -/
def AccWStmt : Prop :=
  ∃ (Er : Type) (_ : Fintype Er) (_ : DecidableEq Er) (Rr : Type) (_ : Finite Rr)
    (_ : Nonempty Rr) (acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)) (C : ℕ), AccW acc C

/-- Cost of one term at record-array volume `V`: certified copy `9V + 4`, accumulation
`C·(V + V + w_g + 1)`, move back `8V + 4`. -/
def termCost (wg V Cacc : ℕ) : ℕ := 9 * V + 4 + (Cacc * (V + V + wg + 1) + (8 * V + 4))

/-- Cost of one role with `n` terms: move in `8V + 4`, the terms, move out `8V + 4`. -/
def tgtCost (wg V Cacc n : ℕ) : ℕ := 8 * V + 4 + (n * termCost wg V Cacc + (8 * V + 4))

end SubNLogN.Machine.CCore.LeafScalarRowAux
