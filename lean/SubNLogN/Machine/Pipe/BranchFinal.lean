/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.Branch
import SubNLogN.Machine.Pipe.BranchMath
import SubNLogN.Machine.Pipe.ZeroOut
import SubNLogN.Machine.Pipe.ReadParamsCost
import SubNLogN.Machine.FFT.MidData
import SubNLogN.Assembly.Row46Layer

/-!
# K7 (`Machine/Pipe/BranchFinal.lean`): the Walsh-branch cut with the proved pieces wired in

`walshBranchCut_of_parts md X …`: the assembly's `WalshBranchCut` body for the closed map
`FnewOfR roundHalfUpR row46 (TabConcreteR roundHalfUpR row46) (walshMid row46)`, from
`walshBranchCut_of_kernels` (`Branch.lean`) at the fixed width schedule `fnewSched` and the fixed
ReadParams bound `readParamsCost`, with the proved `zeroOut_holds` (`ZeroOut.lean`) and the
value-level premise from `branchMath_of` (`BranchMath.lean`). Remaining hypotheses: the multiplier,
the kernels `ReadParamsStmt`/`GuardStmt`, `ConvInStmt`/`ConvOutStmt`, the K6
table machine and the K5 bridge machine, the middle's eligibility `MidOKW8Stmt md`, the
three width statements, and the cost clause at the concrete cost functions.

`walshBranchCut_of_pipe P₀ P₁ J τ …` pins the concrete objects: widths `fnewSched`, ReadParams bound
`readParamsCost`, middle data `walshMidData fnewSched row46Layer P₀ P₁ J`
(`Machine/FFT/MidData.lean`; `P₀`, `P₁`, `J` are the existential constants of the middle machine,
`midCallsBand_of_bands` and `WalshMiddleMachineGenStmt`, obtained by the assembly), interchange factor
`bridgeX τ` (`Contracts/Bridge.lean`). Its middle-eligibility premise is discharged by
`midOKW8_walshMidData` (from `Assembly.midBands_w8_of_width`).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

/-- **The Walsh-branch cut from the remaining parts (`walshBranchCut_of_parts`, 0 `sorry`).** -/
theorem walshBranchCut_of_parts (md : MidData) (X : ℕ → ℕ)
    (hMul : MulBigContract) (hRP : ReadParamsStmt fnewSched md readParamsCost) (hG : GuardStmt)
    (hTab : BridgeTablesMachineStmt) (hCI : ConvInStmt)
    (hBr : BridgeMachineStmt X (fnewFam fnewSched (walshMid Math.Cost.row46) md))
    (hCO : ConvOutStmt) (hMOK : MidOKW8Stmt md) (hSP : Bridge_spreadPart_widthsStmt)
    (hSV : Bridge_solve_widthsStmt) (hTF : TabConcrete_fitStmt)
    (hC : WalshCostClause (branchCost readParamsCost X fnewSched md)) :
    ∃ (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
      WalshBranchFromStmt (FnewOfR roundHalfUpR Math.Cost.row46
        (TabConcreteR roundHalfUpR Math.Cost.row46) (walshMid Math.Cost.row46)) N Tw ∧
        WalshCostClause Tw := by
  obtain ⟨N, hM⟩ := branchMath_of md hMOK hSP hSV hTF
  exact walshBranchCut_of_kernels fnewSched (walshMid Math.Cost.row46) md readParamsCost X N hMul
    hRP hG hTab hCI hBr hCO zeroOut_holds hM hC

/-- **K7 from the remaining parts (`exists_pipeFnewX_of_parts`, 0 `sorry`):**
`∃ Kc, PipeFnewXStmt Kc (TabConcreteR roundHalfUpR row46) (walshMid row46)`, i.e. a pipe machine for
the closed map `F_newConcreteK Kc row46`. -/
theorem exists_pipeFnewX_of_parts (md : MidData) (X : ℕ → ℕ)
    (hMul : MulBigContract) (hRP : ReadParamsStmt fnewSched md readParamsCost) (hG : GuardStmt)
    (hTab : BridgeTablesMachineStmt) (hCI : ConvInStmt)
    (hBr : BridgeMachineStmt X (fnewFam fnewSched (walshMid Math.Cost.row46) md))
    (hCO : ConvOutStmt) (hMOK : MidOKW8Stmt md) (hSP : Bridge_spreadPart_widthsStmt)
    (hSV : Bridge_solve_widthsStmt) (hTF : TabConcrete_fitStmt)
    (hC : WalshCostClause (branchCost readParamsCost X fnewSched md)) :
    ∃ Kc : ℕ, PipeFnewXStmt Kc (TabConcreteR roundHalfUpR Math.Cost.row46)
      (walshMid Math.Cost.row46) := by
  obtain ⟨N, Tw, hW, hTw⟩ := walshBranchCut_of_parts md X hMul hRP hG hTab hCI hBr hCO hMOK hSP hSV
    hTF hC
  exact exists_pipeFnewX _ _ N Tw hW hTw

/-- **The middle is eligible at the W8 pipe calls (`midOKW8_walshMidData`, 0 `sorry`)**, for WF's
middle data at the pipe's widths: from `Assembly.midBands_w8_of_width P₀ P₁` at
`w = fnewSched.wI p0 K0 p_in = schedP p0 K0 + 2 K0 + 16` (`q + 2 ≤ w ≤ 2q` since
`schedP p0 K0 ≥ 12 K0 + 256`). -/
theorem midOKW8_walshMidData (P₀ P₁ J : ℕ) :
    MidOKW8Stmt (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J) := by
  obtain ⟨N, hN⟩ := Assembly.midBands_w8_of_width P₀ P₁
  refine ⟨N, fun n hn pin => ?_⟩
  have hs : 12 * W8.hK0 n + 256 ≤ schedP (W8.hP0 n) (W8.hK0 n) := by
    unfold schedP
    omega
  exact hN n hn (schedP (W8.hP0 n) (W8.hK0 n) + 2 * W8.hK0 n + 16) (by omega) (by omega)

/-- **The Walsh-branch cut at the concrete pipe objects (`walshBranchCut_of_pipe`, 0 `sorry`).**
With `md = walshMidData fnewSched row46Layer P₀ P₁ J`, `X = bridgeX τ`, `rpCost = readParamsCost`,
`sch = fnewSched`: from the multiplier, the kernels (ReadParams, Guard, ConvIn, ConvOut, K6 tables, K5
bridge), the three width statements and the cost clause. -/
theorem walshBranchCut_of_pipe (P₀ P₁ J : ℕ) (τ : ℝ)
    (hMul : MulBigContract)
    (hRP : ReadParamsStmt fnewSched (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J)
      readParamsCost)
    (hG : GuardStmt) (hTab : BridgeTablesMachineStmt) (hCI : ConvInStmt)
    (hBr : BridgeMachineStmt (bridgeX τ) (fnewFam fnewSched (walshMid Math.Cost.row46)
      (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J)))
    (hCO : ConvOutStmt) (hSP : Bridge_spreadPart_widthsStmt) (hSV : Bridge_solve_widthsStmt)
    (hTF : TabConcrete_fitStmt)
    (hC : WalshCostClause (branchCost readParamsCost (bridgeX τ) fnewSched
      (walshMidData fnewSched Assembly.row46Layer P₀ P₁ J))) :
    ∃ (N : ℕ) (Tw : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ),
      WalshBranchFromStmt (FnewOfR roundHalfUpR Math.Cost.row46
        (TabConcreteR roundHalfUpR Math.Cost.row46) (walshMid Math.Cost.row46)) N Tw ∧
        WalshCostClause Tw :=
  walshBranchCut_of_parts _ _ hMul hRP hG hTab hCI hBr hCO (midOKW8_walshMidData P₀ P₁ J) hSP hSV
    hTF hC

end SubNLogN.Machine.Pipe
