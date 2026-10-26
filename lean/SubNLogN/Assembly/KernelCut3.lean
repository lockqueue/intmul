import SubNLogN.Assembly.KernelCut2
import SubNLogN.Machine.Bridge.Reduction
import SubNLogN.Machine.Bridge.MidFnew
import SubNLogN.Machine.Bridge.MidUngroup
import SubNLogN.Machine.Bridge.Expose
import SubNLogN.Machine.Bridge.PrePostFinal
import SubNLogN.Machine.Bridge.InitCtr
import SubNLogN.Machine.FFT.Bands
import SubNLogN.Math.Networks.Proofs.AppCConstants

/-!
# Assembly: the kernel-level cut, version 3 (bridge machine split into component kernels)

`KernelCut3 P₀` decomposes the `bridge` field of `KernelCut2 P₀ P₁ J` (`Assembly/KernelCut2.lean`) into
the component obligations of `BridgeRed.bridgeMachine_of_parts` (`Machine/Bridge/Reduction.lean`)
and of the middle reduction `BridgeRed.midMachine_fnew_of_walsh` (`Machine/Bridge/MidFnew.lean`).
Supplied inside the proof (all proved, 0 `sorry`): `MulBig.mulBig_holds`, `post_holds`,
`initCtr_holds`, `BridgeRed.midGroup_holds`, `BridgeRed.midUngroup_holds`, `expose_of_c6` and
`restore_of_c6` (from the field `c6`), the band lemma `midCallsBand_of_bands row46Layer_OK 1` (which
fixes `P₁`), and the Lemma A.8 (`lem:transfer12`) premise `s_b/W_b < m^τ` at `τ = Row46.tau = 1 - 2^{-40}`
(`c6Premise_row46`, from `rate_bit`, Proposition A.2 (`prop:deficits`)). The middle exponent `J` is produced
by the Walsh-middle contract (`∃ J`), and `readParams` is quantified uniformly over `P₁ J`
(discharged in `Assembly/KernelCut4.lean`; historical identifier `c6` reflects an earlier draft's numbering).

Fields (all discharged in `KernelCut4`–`KernelCutFinal`): `readParams`, `tables`, `preScale`, `reorder`,
`c6`, `spreadLines`, `solveAxis`, `walshMiddle`.

* `kernelCut2Stmt_of_3 : KernelCut3Stmt → KernelCut2Stmt` (0 `sorry`);
* `kernelCutStmt_of_3 : KernelCut3Stmt → KernelCutStmt` (0 `sorry`; direct composition to
  `KernelCutStmt`);
* `w9X_of_kernelCut3 : KernelCut3Stmt → W9SubNLogNSpecX` (0 `sorry`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Machine SubNLogN.Machine.Pipe SubNLogN.Math.Cost SubNLogN.Math.Bridge

/-- `τ = Row46.tau = 1 - 4ξ` with `ξ = 2^{-42}` equals `1 - 2^{-40}`. -/
theorem tau_row46_eq : ((Row46.tau : ℚ) : ℝ) = 1 - (2 : ℝ)⁻¹ ^ 40 := by
  simp only [Row46.tau, Row46.xi]
  push_cast
  norm_num

/-- **The Lemma A.8 (`lem:transfer12`) premise at `τ = Row46.tau` (0 `sorry`):** `s_b / W_b < m^τ` at `h = 100`,
from `rate_bit` (`s_b / W_b < m^{1 - 2^{-40}}`, Proposition A.2 (`prop:deficits`)) and `τ = 1 - 2^{-40}`. -/
theorem c6Premise_row46 :
    (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ ((Row46.tau : ℚ) : ℝ) := by
  rw [tau_row46_eq]
  exact SubNLogN.Math.Networks.rate_bit

/-- **The kernel-level cut, version 3 (`KernelCut3 P₀`).** Component obligations of the bridge-branch
machine, at `τ = Row46.tau` and Walsh-middle cutoff `P₀`:
* `readParams` — read the root header, push the bridge/middle parameters (for all `P₁ J`);
* `tables` — the table generator (Lemma 4.6 (bridge Lemma C)(iii), `lem:bridge-C`);
* `preScale`, `reorder`, `spreadLines`, `solveAxis` — the stage kernels of the bridge machine (Section 4.4);
* `c6` — the arbitrary-width interchange `C6InterchangeStmt τ` (Lemma A.8 (`lem:transfer12`), giving
  `ExposeStmt`/`RestoreStmt` via `expose_of_c6`/`restore_of_c6`, Lemma 4.8 (bridge Lemma D));
* `walshMiddle` — the Walsh middle machine at Proposition A.11's bands of `midLayerParams row46Layer 1`
  with cutoff `P₀` and exponent `λ' = row46Layer.lam'` (Corollary 6.6 (`cor:walsh-middle`) on the machine). -/
structure KernelCut3 (P₀ : ℕ) : Prop where
  /-- read the root header and push the bridge/middle parameters, for every `P₁ J` -/
  readParams : ∀ P₁ J : ℕ,
    ReadParamsStmt fnewSched (walshMidData fnewSched row46Layer P₀ P₁ J) readParamsCost
  /-- the table generator (K6) -/
  tables : BridgeTablesMachineStmt
  /-- K5: pre-scaling -/
  preScale : PreScaleStmt
  /-- K5: the axis reordering at interchange factor `bridgeX τ` -/
  reorder : ReorderStmt (bridgeX ((Row46.tau : ℚ) : ℝ))
  /-- Appendix A (Lemma A.8): the interchange network machine at `τ` -/
  c6 : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ)
  /-- K5: spreading the lines -/
  spreadLines : SpreadLinesStmt
  /-- K5: the per-axis solver -/
  solveAxis : SolveAxisStmt
  /-- K4: the Walsh middle machine at the bands of `midLayerParams row46Layer 1`, cutoff `P₀` -/
  walshMiddle : WalshMiddleMachineGenStmt (LayerBands (midLayerParams row46Layer 1) P₀) row46Layer.lam'

/-- **The kernel-level cut, version 3 (`KernelCut3Stmt`):** `∃ P₀, KernelCut3 P₀`. -/
def KernelCut3Stmt : Prop := ∃ P₀ : ℕ, KernelCut3 P₀

/-- **Version 3 implies version 2 (`kernelCut2Stmt_of_3`, 0 `sorry`).** `P₁` from
`midCallsBand_of_bands row46Layer_OK 1`, `J` from `midMachine_fnew_of_walsh`, and the bridge machine from
`bridgeMachine_of_parts` with the proved parts. -/
theorem kernelCut2Stmt_of_3 (h : KernelCut3Stmt) : KernelCut2Stmt := by
  obtain ⟨P₀, hK⟩ := h
  obtain ⟨P₁, hP₁⟩ := midCallsBand_of_bands row46Layer_OK 1
  obtain ⟨J, hMid⟩ := BridgeRed.midMachine_fnew_of_walsh fnewSched row46Layer P₀ P₁ hP₁
    hK.walshMiddle BridgeRed.midGroup_holds BridgeRed.midUngroup_holds
  exact ⟨P₀, P₁, J, hK.readParams P₁ J, hK.tables,
    BridgeRed.bridgeMachine_of_parts _ _ MulBig.mulBig_holds hK.preScale hK.reorder
      (expose_of_c6 _ c6Premise_row46 hK.c6) (restore_of_c6 _ c6Premise_row46 hK.c6)
      hK.spreadLines hK.solveAxis post_holds initCtr_holds hMid⟩

/-- **Version 3 implies version 1 (`kernelCutStmt_of_3`, 0 `sorry`).** -/
theorem kernelCutStmt_of_3 (h : KernelCut3Stmt) : KernelCutStmt :=
  kernelCutStmt_of_2 (kernelCut2Stmt_of_3 h)

/-- **`W9SubNLogNSpecX` from the version-3 cut (0 `sorry`).** -/
theorem w9X_of_kernelCut3 (h : KernelCut3Stmt) : W9SubNLogNSpecX :=
  w9X_of_kernelCut2 (kernelCut2Stmt_of_3 h)

end SubNLogN.Assembly
