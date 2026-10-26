/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimK
import SubNLogN.Machine.AppC.C5NetSimSteps

/-!
# Proposition A.7 network simulation, part K2 (`AppC/C5NetSimK2.lean`): the outer shears

`pre_sim` (`subHSteps` ↔ `preOpsK`) and `post_sim` (`hMinusDSteps` ↔ `postOpsK`) on the top class of
the node layout, from `foldl_sim` (`AppC/C5NetSimK.lean`) and the step index maps `pm_hdMinus`,
`pm_negD`, `pm_hdPlus` (`AppC/C5NetSimSteps.lean`). Paper: Proposition A.7 (`prop:transfer11`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAuxK

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step Elem RowClass)
open SubNLogN.Machine.C5.NetAux

section Sim2

variable (q k' N0 R N1 G B : ℕ) {β : Type} [Inhabited β]

/-- **`D ← D − H`**: `subHSteps` on the top class encode to the op list `preOps`. -/
theorem pre_sim (hq : 0 < q) (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → β) :
    (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
        ((subHSteps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := β) (q ^ mH ^ k') 3
          (4 + mH ^ (k' + 1)) (mH ^ k')).foldl
          (fun A s => s.runIn (RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) A) =
      permByInv (macroMap q mH preOpsK (k' + 1) N1 G B)
        ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A) := by
  refine foldl_sim q k' N0 R N1 G B hq _ _ ?_ A
  unfold subHSteps preOpsK
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro i _ A'
  exact elem_sim q k' N0 R N1 G B _ _ (pm_hdMinus q k' N0 R N1 G B hq i) A'

/-- **`D ← H − D`**: `hMinusDSteps` on the top class encode to the op list `postOps`. -/
theorem post_sim (hq : 0 < q) (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → β) :
    (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
        ((hMinusDSteps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := β) (q ^ mH ^ k') 3
          (4 + mH ^ (k' + 1)) (mH ^ k')).foldl
          (fun A s => s.runIn (RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) A) =
      permByInv (macroMap q mH postOpsK (k' + 1) N1 G B)
        ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A) := by
  refine foldl_sim q k' N0 R N1 G B hq _ _ ?_ A
  unfold hMinusDSteps postOpsK
  refine forall₂_flatMapK _ _ _ (fun i _ => ?_)
  exact List.Forall₂.cons (fun A' => elem_sim q k' N0 R N1 G B _ _ (pm_negD q k' N0 R N1 G B hq i) A')
    (List.Forall₂.cons (fun A' => elem_sim q k' N0 R N1 G B _ _
      (pm_hdPlus q k' N0 R N1 G B hq i i) A') List.Forall₂.nil)

end Sim2

end SubNLogN.Machine.C5.NetAuxK
