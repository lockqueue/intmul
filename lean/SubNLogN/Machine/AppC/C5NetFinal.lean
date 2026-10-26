/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimTop
import SubNLogN.Machine.AppC.R2C5NetShape2
import SubNLogN.Machine.AppC.C5NetSimRun

/-!
# Proposition A.7 network leaf (`AppC/C5NetFinal.lean`): `C5NetStmt q` from network correctness

Proves the concrete network leaf of Proposition A.7 (`prop:transfer11`). (`AppC` and `C5`/`c5` retain
earlier draft numbering for stability; see Appendix A.) The instance is `mkData (rawMain fac) preOps
postOps rhoPerm.symm` (serialized raw schedule of `bitNodeOps`, `AppC/C5NetSim*.lean`).
`nodeCorrect_mkData` proves node correctness at every level `k = k'+1` by simulating
`interchangeProc (k'+1)` on the node layout (array `A` decoded from list `v`): outer shear `pre_sim`,
node `node_sim` (children by induction at depth `k'`), `merge_relabel`, outer shear `post_sim`,
`proc_run`/`node_full`, `InterchangeProcCorrectStmt` at depth `k'+1`, and `top_swap`. `c5Net_of`
derives `C5NetStmt q` from `BitNetCert`, `InterchangeProcCorrectStmt`, `ShearFacts`,
`InterchangeCallCountStmt`, and `C5Params q fac`.
-/

namespace SubNLogN.Machine.C5.NetAuxF

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step RoleOp ProcK)
open SubNLogN.Machine.C5.NetAux SubNLogN.Machine.C5.NetAuxK SubNLogN.Machine.C5.NetSimRunAux

/-- **Node correctness of the concrete network** at every level. -/
theorem nodeCorrect_mkData (hIC : InterchangeProcCorrectStmt) (hcert : BitNetCert)
    (hshear : ShearFacts) (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hC : C5Params q fac) :
    NodeCorrect q ((mkData (rawMain fac) preOps postOps rhoPerm.symm).toNet q) := by
  obtain ⟨hq, hq2, hint, hfac⟩ := hC
  have hq0 : 0 < q := hq.pos
  have hq1 : 1 ≤ q := hq0
  intro k N0 R N1 G B w v hk hN0 hR hN1 hG hB hdiv hv hvw
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hWR : Wb ∣ R := dvd_trans (dvd_pow_self Wb (by omega)) hdiv
  -- the decoded array
  obtain ⟨A, hA⟩ : ∃ X : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec w,
      X = fun x => toRec w (v.getD ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).lexEquiv x).val []) :=
    ⟨_, rfl⟩
  have hcard : v.length = (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).card := by
    rw [hv, nl_card]; rfl
  have hvA : ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A).map ofRec = v := by
    rw [hA]; exact enc_decode _ w v hcard hvw
  have hdvdL : ∀ X : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec w,
      rowSize q mH (k' + 1) N1 G B ∣ ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc X).length := by
    intro X
    rw [Model.Layout.enc_length, nl_card]
    exact Dvd.intro_left _ rfl
  have hmac : ∀ (os : List (StreamOp mH)) (X : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr →
      Rec w), ∀ y < ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc X).length,
      macroMap q mH os (k' + 1) N1 G B y < ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc X).length :=
    fun os X => macroMap_lt q mH os (k' + 1) N1 G B _ hq1 (by omega) (hdvdL X)
  -- the intermediate arrays and role lists
  obtain ⟨A₁, hA₁⟩ : ∃ X : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec w,
      X = (subHSteps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec w) (q ^ mH ^ k') 3
        (4 + mH ^ (k' + 1)) (mH ^ k')).foldl
        (fun A s => s.runIn (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) A :=
    ⟨_, rfl⟩
  obtain ⟨us₀, hus₀⟩ : ∃ us : Fin Wb → List (List Bool), us = fun r =>
      (roleBlocks Wb r.val (rowSize q mH (k' + 1) N1 G B)
        ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A₁)).map ofRec := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ X : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec w,
      X = ((nodeEvents .bit 100).flatMap (InterchangeCorrect.evOps
        (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec w) (q ^ mH ^ k') 3
        (4 + mH ^ (k' + 1)) (mH ^ k') fac
        (fun i j => interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec w)
          q fac k' (3 + i.val * mH ^ k') (4 + mH ^ (k' + 1) + j.val * mH ^ k')))).foldl
        (fun A o => o.run (ProcK.run k') (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B))
          Wb_pos A) A₁ := ⟨_, rfl⟩
  obtain ⟨us₂, hus₂⟩ : ∃ us : Fin Wb → List (List Bool), us =
      (rawMain fac).foldl (fun us x => x.run (fun op => streamMap q mH op (k' + 1) N1 G B)
        (childMap q k' G B) us) us₀ := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃⟩ : ∃ X : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec w,
      X = Model.relabelRun (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) Wb Wb_pos
        rhoPerm A₂ := ⟨_, rfl⟩
  obtain ⟨A₄, hA₄⟩ : ∃ X : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → Rec w,
      X = (hMinusDSteps (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (β := Rec w) (q ^ mH ^ k') 3
        (4 + mH ^ (k' + 1)) (mH ^ k')).foldl
        (fun A s => s.runIn (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) A₃ :=
    ⟨_, rfl⟩
  -- (1) the outer shear `pre` and the cyclic split
  have e1 : permByInv (macroMap q mH preOps (k' + 1) N1 G B) v =
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A₁).map ofRec := by
    rw [← hvA, permByInv_map _ _ _ (hmac preOps A), hA₁, pre_sim q k' N0 R N1 G B hq0 A]
    rfl
  have f1 : (fun r : Fin Wb => roleBlocks Wb r.val (rowSize q mH (k' + 1) N1 G B)
      (permByInv (macroMap q mH preOps (k' + 1) N1 G B) v)) = us₀ := by
    rw [hus₀, e1]
    funext r
    exact roleBlocks_map _ _ _ _ _
  -- (2) the schedule
  have f2 : runSched q ((mkData (rawMain fac) preOps postOps rhoPerm.symm).toNet q) (k' + 1) N1 G B
      (mkData (rawMain fac) preOps postOps rhoPerm.symm).sched us₀ = us₂ := by
    have hcm : (fun i j : Fin mH => swapMap q mH (k' + 1 - 1) (cG q mH (k' + 1) G i j)
        (cB q mH (k' + 1) B j)) = childMap q k' G B := by
      funext i j
      exact childMap_eq q k' G B i j
    rw [hus₂, runSched_mkData, hcm]
  -- (3) node simulation and merge in order `ρ⁻¹`
  have f3 : mergeBlocks Wb rhoPerm.symm (N0 * R / Wb) (rowSize q mH (k' + 1) N1 G B) us₂ =
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A₃).map ofRec := by
    have hsim0 : Sim Wb (rowSize q mH (k' + 1) N1 G B) A₁ us₀ := by
      rw [hus₀]; exact fun r => rfl
    have hsim2 : Sim Wb (rowSize q mH (k' + 1) N1 G B) A₂ us₂ := by
      have h := node_sim hIC hcert hshear fac hq hq2 hint hfac hG hB hdiv A₁ us₀ hsim0
      rw [← hA₂, ← hus₂] at h
      exact h
    rw [hA₃]
    exact merge_relabel q k' N0 R N1 G B w hWR A₂ us₂ hsim2
  -- (4) the outer shear `post`
  have f4 : permByInv (macroMap q mH postOps (k' + 1) N1 G B)
      (((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A₃).map ofRec) =
      ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A₄).map ofRec := by
    rw [permByInv_map _ _ _ (hmac postOps A₃), hA₄, post_sim q k' N0 R N1 G B hq0 A₃]
    rfl
  -- (5) one level of the pure-network procedure, its correctness, and the level interchange
  have f5 : ProcK.run (k' + 1) (interchangeProc (L := nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
      (β := Rec w) q fac (k' + 1) 3 (4 + mH ^ (k' + 1)))
      (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A = A₄ := by
    rw [proc_run fac A, node_full fac, ← hA₁, ← hA₂, ← hA₃, ← hA₄]
  have f6 := hIC hcert hshear (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (Rec w) q fac (k' + 1) 3
    (4 + mH ^ (k' + 1)) (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B))
    (top_hyps fac hq hq2 hint hfac hdiv) A
  have hswap : ∀ y < ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A).length,
      swapMap q mH (k' + 1) G B y < ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A).length := by
    intro y hy
    refine swapFieldsInv_lt _ _ _ _ _ y ?_ hy
    rw [Model.Layout.enc_length, nl_card]
    generalize q ^ mH ^ (k' + 1) = X
    exact Dvd.intro_left (N0 * R * N1) (by ring)
  have f7 : ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
      ((Step.swapBlocks 3 (4 + mH ^ (k' + 1)) (mH ^ (k' + 1)) :
        Step (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) (Rec w)).runIn
        (Model.RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A)).map ofRec =
      permByInv (swapMap q mH (k' + 1) G B) v := by
    rw [top_swap q k' N0 R N1 G B hq0 hG hB A, ← permByInv_map _ _ _ hswap, hvA]
  -- the chain
  show permByInv (macroMap q mH ((mkData (rawMain fac) preOps postOps rhoPerm.symm).ops
      (mkData (rawMain fac) preOps postOps rhoPerm.symm).post) (k' + 1) N1 G B)
      (mergeBlocks Wb rhoPerm.symm (N0 * R / Wb) (rowSize q mH (k' + 1) N1 G B)
        (runSched q ((mkData (rawMain fac) preOps postOps rhoPerm.symm).toNet q) (k' + 1) N1 G B
          (mkData (rawMain fac) preOps postOps rhoPerm.symm).sched
          (fun r => roleBlocks Wb r.val (rowSize q mH (k' + 1) N1 G B)
            (permByInv (macroMap q mH ((mkData (rawMain fac) preOps postOps rhoPerm.symm).ops
              (mkData (rawMain fac) preOps postOps rhoPerm.symm).pre) (k' + 1) N1 G B) v)))) =
    permByInv (swapMap q mH (k' + 1) G B) v
  rw [mkData_pre, mkData_post, f1, f2, f3, f4, ← f5, f6, f7]

/-- **The network leaf `C5NetStmt q`** under the pure-network certificates and `C5Params q fac`. -/
theorem c5Net_of (hcert : BitNetCert) (hIC : InterchangeProcCorrectStmt) (hshear : ShearFacts)
    (hCC : InterchangeCallCountStmt) (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hC : C5Params q fac) : C5NetStmt q := by
  -- the equalities are oriented `Wb = W`, `mH = m` so that `subst` never `whnf`s the closed `Wb`
  have key : ∀ (W m : ℕ), Wb = W → mH = m → ∃ D : NetData W m,
      NodeCorrect q (D.toNet q) ∧ (D.sched.filter SchedOp.isCall).length ≤ tripleSb 100 ∧
        (∀ o, ∀ op ∈ D.ops o, op.Valid q) ∧ (∀ g, ∀ p ∈ D.gates g, p.1 ≠ p.2) := by
    intro W m hW hm
    subst hW
    subst hm
    refine ⟨mkData (rawMain fac) preOps postOps rhoPerm.symm,
      nodeCorrect_mkData hIC hcert hshear q fac hC, ?_, ?_, ?_⟩
    · exact le_of_eq ((mkData_calls _ _ _ _).trans (R2ShapeAux.rawMain_calls_r2 hCC q fac hC))
    · exact mkData_ops_valid _ _ _ _ (fun op => op.Valid q) (R2ShapeAux.rawMain_valid_r2 hC.1 fac hC.2.2.2)
        (preOpsK_valid q) (postOpsK_valid q)
    · exact mkData_gates_ne _ _ _ _ (R2ShapeAux.rawMain_gates_ne_r2 fac)
  exact key (tripleWb 100) (tripleM 100) hcert.card_roles (by norm_num [tripleM, mH])

end SubNLogN.Machine.C5.NetAuxF
