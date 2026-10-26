/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvCostKit
import SubNLogN.Machine.Layer.DrvParamsShared

/-!
# Layer driver, pre-phase parameters: the final stacks (`Machine/Layer/DrvPreParamsOut.lean`)

The final stacks of the pre-phase parameter kernel are written as eleven pushes (`preOutG`). Here
the value of the padding count is a parameter `np`; `preOut` (`DrvPreParams.lean`) is `preOutG` at
`np = npadVal t.d t.D t.K t.S`. `preOutG_eq` identifies these stacks with `drvPreParamsPost`
(`DrvParamsDefs.lean`), given `drvNpad t = np`.

`preOut_eq` is the instance `np = npadVal t.d t.D t.K t.S`, using
`drvNpad_eq` (`DrvParamsShared.lean`).

**Scope (honest summary).** Both `preOutG_eq` and `preOut_eq` are proved, with no extra hypotheses
in `preOut_eq`.
-/

namespace SubNLogN.Machine.Layer.DrvPreParamsAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine
open SubNLogN.Machine.Layer.DrvParamsAux SubNLogN.Machine.Layer.DrvParamsShared
open SubNLogN.Math.Networks (q0Of)

/-- The final stacks of the pre-phase parameter kernel as eleven pushes, with the padding count
`np` as a parameter. -/
noncomputable def preOutG {E : Type} [DecidableEq E] (np : ℕ) (t : LayerRT)
    (S : KLoc (Fin 12) E → List Sym) : KLoc (Fin 12) E → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update S
    (.inl 1) (natSyms t.w ++ S (.inl 1)))
    (.inl 2) (natSyms (t.P * 3 + 3) ++ S (.inl 2)))
    (.inl 3) (natSyms t.P ++ S (.inl 3)))
    (.inl 4) (hdrSyms [t.S, t.K, t.ρ, t.D, 0, 0, t.P * 3 + 3, t.P * 3 + 3] ++ S (.inl 4)))
    (.inl 5) (natSyms (min (q0Of t.d) t.D) ++ S (.inl 5)))
    (.inl 6) (natSyms (t.S * 2 ^ (t.K * (t.D - 1) + t.ρ)) ++ S (.inl 6)))
    (.inl 7) (natSyms t.K ++ S (.inl 7)))
    (.inl 8) ([Sym.bit (decide (q0Of t.d < t.D))] ++ S (.inl 8)))
    (.inl 9) (natSyms (2 ^ (t.K * t.D) * t.S) ++ S (.inl 9)))
    (.inl 10) (natSyms np ++ S (.inl 10)))
    (.inl 11) (natSyms t.r ++ S (.inl 11))

theorem drvRowsSym_eq (t : LayerRT) : drvRowsSym t = Sym.bit (decide (q0Of t.d < t.D)) := by
  by_cases h : q0Of t.d < t.D
  · rw [drvRowsSym_of_rows h, decide_eq_true h]
  · rw [drvRowsSym_of_not_rows h, decide_eq_false h]

/-- **The final stacks**, given the padding count. -/
theorem preOutG_eq {E : Type} [DecidableEq E] (t : LayerRT) (S : KLoc (Fin 12) E → List Sym)
    (np : ℕ) (hnp : drvNpad t = np) : preOutG np t S = drvPreParamsPost t S := by
  have hrow := drvRowsSym_eq t
  have hwg := drvWg_eq t
  have hdelta : drvDelta t = t.P := rfl
  funext l
  rcases l with i | e
  · fin_cases i <;>
      simp +decide [preOutG, drvPreParamsPost, hrow, hwg, hdelta, hnp, drvQ1, drvW0, drvKeep]
  · simp [preOutG, drvPreParamsPost]

/-- The final stacks of the pre-phase parameter kernel, as eleven pushes. -/
noncomputable def preOut {E : Type} [DecidableEq E] (t : LayerRT) (S : KLoc (Fin 12) E → List Sym) :
    KLoc (Fin 12) E → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update S
    (.inl 1) (natSyms t.w ++ S (.inl 1)))
    (.inl 2) (natSyms (t.P * 3 + 3) ++ S (.inl 2)))
    (.inl 3) (natSyms t.P ++ S (.inl 3)))
    (.inl 4) (hdrSyms [t.S, t.K, t.ρ, t.D, 0, 0, t.P * 3 + 3, t.P * 3 + 3] ++ S (.inl 4)))
    (.inl 5) (natSyms (min (q0Of t.d) t.D) ++ S (.inl 5)))
    (.inl 6) (natSyms (t.S * 2 ^ (t.K * (t.D - 1) + t.ρ)) ++ S (.inl 6)))
    (.inl 7) (natSyms t.K ++ S (.inl 7)))
    (.inl 8) ([Sym.bit (decide (q0Of t.d < t.D))] ++ S (.inl 8)))
    (.inl 9) (natSyms (2 ^ (t.K * t.D) * t.S) ++ S (.inl 9)))
    (.inl 10) (natSyms (npadVal t.d t.D t.K t.S) ++ S (.inl 10)))
    (.inl 11) (natSyms t.r ++ S (.inl 11))

/-- **The final stacks** of the pre-phase parameter kernel are `drvPreParamsPost`. -/
theorem preOut_eq {E : Type} [DecidableEq E] (t : LayerRT) (S : KLoc (Fin 12) E → List Sym) :
    preOut t S = drvPreParamsPost t S :=
  preOutG_eq t S _ (drvNpad_eq t)

end SubNLogN.Machine.Layer.DrvPreParamsAux
