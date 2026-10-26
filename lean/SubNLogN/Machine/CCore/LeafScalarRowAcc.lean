/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarRowDefs
import SubNLogN.Machine.CCore.LeafScalarAcc

/-!
# Scalar row leaf: the accumulation calls on the work layout (`CCore/LeafScalarRowAcc.lean`)

**Main result.** `SubNLogN.Machine.CCore.LeafScalarRowAcc.accW_holds :
LeafScalarRowAux.AccWStmt` (`CCore/LeafScalarRowDefs.lean`), with no hypotheses: the four
accumulation calls `accCall c` on the work layout `Lw AccE` (`CCore/LeafPhaseBase.lean`) satisfy
`AccW accCall 300`.

**Construction.** `accCall c := callInj ιW (lR AReg) (aMain (preOf c) (fOf c))`: the accumulate
kernel of `acc_holds` (`CCore/LeafScalarAcc.lean`), which runs on `CAddAux.CK`,
embedded along `ιW`: `u ↦ X`, `v ↦ X2`, the destination `↦ Y`, the width counter `↦ cW`, `CK`'s two
unused width slots and its nine scratch stacks to the private scratch `AccE = Fin 2 ⊕ Fin 9`; the
registers `AReg` through `lR`. The proof is `aMain_eval` plus `runs_callInj` (as `runs_rotCall`,
`LeafPhaseCall.lean`). The sub-kernel scratch is empty before and after (guards are removed).
-/

namespace SubNLogN.Machine.CCore.LeafScalarRowAcc

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith.CAddAux
  SubNLogN.Machine.CCore.LeafScalarAux SubNLogN.Machine.CCore.LeafScalarAccAux
  SubNLogN.Machine.CCore.LeafScalarRowAux

/-- Embedding of `CAddAux.CK` inside the work layout `Lw AccE`. -/
def ιW : CK → Lw AccE :=
  Sum.elim ![wS .X, wS .X2, wS .Y, wS .cW, .inr (.inl 0), .inr (.inl 1)] fun j => .inr (.inr j)

theorem ιW_injective : Function.Injective ιW := by
  refine Function.Injective.sumElim ?_ (fun e e' h => by simpa using h) ?_
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wS]
  · intro x e
    fin_cases x <;> simp [wS]

/-- The accumulation call of coefficient `c` on the work layout. -/
def accCall (c : Coef) : Prog (Lw AccE) (fun _ => Sym) (σ AReg) :=
  callInj ιW (lR AReg) (aMain (preOf c) (fOf c))

/-- **The accumulation calls on the work layout** (`AccWStmt`): `AccW accCall 300`. -/
theorem accW_holds : AccWStmt := by
  refine ⟨AccE, inferInstance, inferInstance, AReg, inferInstance, inferInstance, accCall, 300,
    fun c => closed_callInj ιW (lR AReg) (closed_aMain _ _), ?_⟩
  intro c d sc w u v hw hal hfv hX hX2 hcW
  refine runs_callInj (Q := fun _ => True) ιW_injective (lR AReg) ?_ ?_
  · apply Runs.of_eval
    rintro ⟨o, p, la, lb, cc⟩
    obtain ⟨v', t, ht, e⟩ := aMain_eval (preOf c) (fOf c) (gOf c) (hfgOf c) (accC c)
      (accC_eq c) w hw u v [Sym.mark] [Sym.mark] [] (wst d sc (fun _ => []) ∘ ιW) hal
      (fun _ => hfv) blkTerm_mark TermOK.nil hX hX2 (by rw [List.append_nil]; exact hcW)
      o p la lb cc
    refine ⟨v', t, e.of_eq (st_eqC rfl ?_) rfl, trivial, ht⟩
    funext k
    rcases k with k | k
    · fin_cases k <;> simp [ιW, wst]
    · simp [ιW, wst]
  · intro k hk
    rcases k with (_ | q) | x
    · rfl
    · have hqX : q ≠ .X := fun h => hk (.inl 0) (by simp [ιW, wS, h])
      have hqX2 : q ≠ .X2 := fun h => hk (.inl 1) (by simp [ιW, wS, h])
      have hqY : q ≠ .Y := fun h => hk (.inl 2) (by simp [ιW, wS, h])
      simp [wst, hqX, hqX2, hqY]
    · rfl

end SubNLogN.Machine.CCore.LeafScalarRowAcc
