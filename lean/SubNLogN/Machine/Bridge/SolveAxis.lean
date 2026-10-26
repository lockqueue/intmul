/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisRuns
import SubNLogN.Machine.Bridge.SolveAxisCost
import SubNLogN.Machine.Arith.CAdd
import SubNLogN.Machine.Arith.Shift

/-!
# K5-SOLVE: one deconvolution stage, `solveAxis_holds` (`Bridge/SolveAxis.lean`)

`solveAxis_holds : SolveAxisStmt` (`Contracts/Bridge.lean`), from three hypotheses: the sweep
kernel contract `SolveSweepStmt` (`Bridge/SolveSweepStmt.lean`), the parameter-row contract
`SolParamRowsStmt` (`Bridge/SolveParamsDefs.lean`) and the arithmetic leaf `CMulTruncStmt`
(`Contracts/Arith.lean`). The other ingredients are proved and used directly: the split, merge and
reindex kernels (`solveHalfSplit_holds`, `solveHalfMerge_holds`, `solveReindexI_holds`,
`solveReindexJ_holds`), the arithmetic leaves `Arith.cAdd_holds`, `Arith.roundHalfUpShift_holds`, the
value and width glue (`deconvAxis_glue`, `sweepFits_of_solveFits`), the driver run
(`SolveDrvAux.runs_drv_core`) and its cost bound (`SolveDrvAux.drvCost_le`). The multiplier
`MulBigContract` is the premise of `SolveAxisStmt` itself.

Cost constant: `SolveDrvAux.drvConst Cp Cs Cm Cr Cj Cw` of the six kernel constants.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.Bridge

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **[K5-SOLVE] One deconvolution stage** (`SolveAxisStmt`), from the sweep kernel, the parameter
rows and the truncating complex multiplication leaf. -/
theorem solveAxis_holds (hSw : SolveSweepStmt) (hPar : SolParamRowsStmt)
    (hCM : CMulTruncStmt) : SolveAxisStmt := by
  intro hMul
  obtain ⟨Cp, hKp⟩ := hPar
  obtain ⟨Ep, _, _, Rp, Pp, _, _, hclp, hsP⟩ := hKp ()
  obtain ⟨Cs, hKs⟩ := solveHalfSplit_holds
  obtain ⟨Es, _, _, Rs, Ps, _, _, hcls, hsS⟩ := hKs ()
  obtain ⟨Cm, hKm⟩ := solveHalfMerge_holds
  obtain ⟨Em, _, _, Rm, Pm, _, _, hclm, hsM⟩ := hKm ()
  obtain ⟨Cr, hKr⟩ := solveReindexI_holds
  obtain ⟨Er, _, _, Rr, Pr, _, _, hclr, hsR⟩ := hKr ()
  obtain ⟨Cj, hKj⟩ := solveReindexJ_holds
  obtain ⟨Ej, _, _, Rj, Pj, _, _, hclj, hsJ⟩ := hKj ()
  obtain ⟨Cw, hKw⟩ := hSw hMul hCM Arith.roundHalfUpShift_holds Arith.cAdd_holds
  obtain ⟨Ew, _, _, Rw, Pw, _, _, hclw, hsW⟩ := hKw ()
  refine ⟨SolveDrvAux.drvConst Cp Cs Cm Cr Cj Cw, fun _ =>
    ⟨SolveDrvAux.DW ⊕ SolveDrvAux.EPd Ep Es Em Er Ej Ew, inferInstance, inferInstance,
      SolveDrvAux.σd Rp Rs Rm Rr Rj Rw, SolveDrvAux.drvProg Pp Ps Pm Pr Pj Pw, inferInstance,
      inferInstance, SolveDrvAux.closed_drvProg hclp hcls hclm hclr hclj hclw, ?_⟩⟩
  intro b m i T Y rarr rax rpar rsol S hclean hshape hi him hwI hwT hP hlog htg htf hY hYf _ hSF
    hrarr hrax harr hax hpar hsol
  have h := SolveDrvAux.runs_drv_core hsP hsS hsM hsR hsJ hsW b m i T Y rarr rax rpar rsol
    (S (kW .ax)) (S (kW .ex)) S (fun e => hclean (.inr e)) hshape hi him hwI hwT hP htg htf hY
    hYf hSF hrarr hrax hax hpar hsol
  rw [← harr, SolveDrvAux.mk_eV S hclean, SolveDrvAux.mk_eV S hclean,
    Function.update_eq_self] at h
  exact WP.W9comp.runs_mono h (fun _ _ => trivial)
    (SolveDrvAux.drvCost_le b i Cp Cs Cm Cr Cj Cw hshape hi hwI hwT hP hlog)

end SubNLogN.Machine
