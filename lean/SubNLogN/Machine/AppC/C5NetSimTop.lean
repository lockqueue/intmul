/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimNode

/-!
# Proposition A.7 network simulation, part 8: the top level (`AppC/C5NetSimTop.lean`)

Helpers for the assembly of `C5NetStmt`, on `nodeLayout q (mH^(k'+1)) N0 R N1 G B` with the whole
array as class (`RowClass.top (rowF …)`):
* `top_hyps`: the hypotheses of the pure-network Proposition A.7 correctness for the interchange of the two chunks
  (depth `k' + 1`, `H` at field `3`, `D` at field `4 + mH^(k'+1)`);
* `proc_run`: one level of `interchangeProc` = the shears `subHSteps`, the node, `hMinusDSteps`;
* `node_full`: the node = the event list with `evOps`, then the relabelling `rhoPerm`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step RoleOp ProcK Elem RowClass)

section Top

variable {q k' N0 R N1 G B wd : ℕ}

theorem top_hyps (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (hq : q.Prime) (hq2 : q ≠ 2)
    (hint : ∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j))
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    (hR : Wb ^ (k' + 1) ∣ R) :
    InterchangeHyps (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) q fac (k' + 1) 3
      (4 + mH ^ (k' + 1)) (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) := by
  refine ⟨hq, hq2, hint, hfac, fun i' hi' => ?_, by omega, ?_, ?_, ?_⟩
  · show nodeR q (mH ^ (k' + 1)) N0 R N1 G B i'.val = q
    exact nodeR_q (by omega)
  · show 4 + mH ^ (k' + 1) + mH ^ (k' + 1) ≤ 5 + 2 * mH ^ (k' + 1)
    omega
  · show 1 < 3
    omega
  · show 1 * Wb ^ (k' + 1) ∣ (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).r
      (rowF q (mH ^ (k' + 1)) N0 R N1 G B)
    rw [nl_r_row, Nat.one_mul]
    exact hR

/-- One level of `interchangeProc` on the whole array: `subHSteps`, the node, `hMinusDSteps`. -/
theorem proc_run (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec wd) :
    ProcK.run (k' + 1) (interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
        (β := Rec wd) q fac (k' + 1) 3 (4 + mH ^ (k' + 1)))
        (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A =
      (hMinusDSteps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd) (q ^ mH ^ k') 3
          (4 + mH ^ (k' + 1)) (mH ^ k')).foldl
        (fun A s => s.runIn (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A)
        (Model.Op.run (ProcK.run k') (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B))
          (Model.Op.node Wb Wb_pos (bitNodeOps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
            (β := Rec wd) (q ^ mH ^ k') 3 (4 + mH ^ (k' + 1)) (mH ^ k') fac
            (fun i j => interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
              (β := Rec wd) q fac k' (3 + i.val * mH ^ k') (4 + mH ^ (k' + 1) + j.val * mH ^ k'))))
          ((subHSteps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd) (q ^ mH ^ k')
              3 (4 + mH ^ (k' + 1)) (mH ^ k')).foldl
            (fun A s => s.runIn (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) A)) := by
  show List.foldl (fun A o => Model.Op.run (ProcK.run k')
      (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) o A) A
    ((subHSteps (q ^ mH ^ k') 3 (4 + mH ^ (k' + 1)) (mH ^ k')).map Model.Op.prim ++
      [Model.Op.node Wb Wb_pos (bitNodeOps (q ^ mH ^ k') 3 (4 + mH ^ (k' + 1)) (mH ^ k') fac
        (fun i j => interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd)
          q fac k' (3 + i.val * mH ^ k') (4 + mH ^ (k' + 1) + j.val * mH ^ k')))] ++
      (hMinusDSteps (q ^ mH ^ k') 3 (4 + mH ^ (k' + 1)) (mH ^ k')).map Model.Op.prim :
      List (Model.Op (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (Rec wd)
        (ProcK (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (Rec wd) k'))) = _
  rw [List.foldl_append, List.foldl_append, List.foldl_map, List.foldl_map]
  rfl

/-- The node: the pure-network event list with `evOps`, then the relabelling `rhoPerm`. -/
theorem node_full (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec wd) :
    Model.Op.run (ProcK.run k') (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B))
        (Model.Op.node Wb Wb_pos (bitNodeOps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
          (β := Rec wd) (q ^ mH ^ k') 3 (4 + mH ^ (k' + 1)) (mH ^ k') fac
          (fun i j => interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
            (β := Rec wd) q fac k' (3 + i.val * mH ^ k') (4 + mH ^ (k' + 1) + j.val * mH ^ k')))) A =
      Model.relabelRun (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) Wb Wb_pos rhoPerm
        (((nodeEvents .bit 100).flatMap (InterchangeCorrect.evOps
          (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec wd) (q ^ mH ^ k') 3
          (4 + mH ^ (k' + 1)) (mH ^ k') fac
          (fun i j => interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
            (β := Rec wd) q fac k' (3 + i.val * mH ^ k') (4 + mH ^ (k' + 1) + j.val * mH ^ k')))).foldl
          (fun A o => o.run (ProcK.run k') (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B))
            Wb_pos A) A) := by
  show List.foldl _ A (bitNodeOps _ _ _ _ fac _) = _
  rw [InterchangeCorrect.bitNodeOps_eq, List.foldl_append, InterchangeCorrect.nodeMainOps_eq_flatMap]
  rfl

/-- **Merge = encoded relabelling.** If the role lists `us` simulate `A` (rows of `rowSize` records,
`W_b ∣ R`), the list-level merge in class order `ρ⁻¹ = rhoPerm.symm` is the encoding of the pure-network final
relabelling of `A` by `rhoPerm` (`Model.Layout.enc_relabelRun`). -/
theorem merge_relabel' (hR : Wb ∣ R) (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec wd)
    (us : Fin Wb → List (List Bool)) (hsim : Sim Wb (rowSize q mH (k' + 1) N1 G B) A us) :
    mergeBlocks Wb rhoPerm.symm (N0 * R / Wb) (rowSize q mH (k' + 1) N1 G B) us =
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
        (Model.relabelRun (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) Wb Wb_pos
          rhoPerm A)).map ofRec := by
  have hWr : Wb ∣ (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).r
      (rowF q (mH ^ (k' + 1)) N0 R N1 G B) := by
    rw [nl_r_row]
    exact hR
  have h0 : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockRange 0
      (rowF q (mH ^ (k' + 1)) N0 R N1 G B).val = N0 :=
    br_single' q (mH ^ (k' + 1)) N0 R N1 G B 0 (by omega)
  have hpl : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).place
      (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).n (rowF q (mH ^ (k' + 1)) N0 R N1 G B) =
        rowSize q mH (k' + 1) N1 G B :=
    nl_place q (mH ^ (k' + 1)) N0 R N1 G B
  have hus : us = fun r => (roleBlocks Wb r.val (rowSize q mH (k' + 1) N1 G B)
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A)).map ofRec := funext hsim
  subst hus
  rw [(nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc_relabelRun A
      (rowF q (mH ^ (k' + 1)) N0 R N1 G B) Wb_pos hWr rhoPerm, h0, nl_r_row, hpl, mergeBlocks_map,
    mergeBlocks_eq_model]
  simp only [roleBlocks_eq_model]

end Top

end SubNLogN.Machine.C5.NetAux
