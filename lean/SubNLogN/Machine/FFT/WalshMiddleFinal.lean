/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.Middle
import SubNLogN.Machine.FFT.PhaseHolds
import SubNLogN.Machine.FFT.DIF
import SubNLogN.Machine.Arith.HalfSum
import SubNLogN.Machine.Arith.CMul
import SubNLogN.Machine.Arith.CMulBRuns
import SubNLogN.Machine.FFT.LayoutFinal
import SubNLogN.Machine.Walsh.PosPermFull
import SubNLogN.Machine.Walsh.CubeHdr
import SubNLogN.Machine.Walsh.CnotScan
import SubNLogN.Machine.Walsh.CnotScanSelPhase
import SubNLogN.Machine.Walsh.PosPermSchedEmitAll
import SubNLogN.Machine.FFT.RoundsMain
import SubNLogN.Machine.FFT.ChunkMain
import SubNLogN.Machine.FFT.TwiddlePass
import SubNLogN.Machine.FFT.TwiddleAddr
import SubNLogN.Machine.MulBig.Main
import SubNLogN.Machine.FFT.Prefix
import SubNLogN.Machine.FFT.PrefixParam
import SubNLogN.Machine.FFT.PrefixPass
import SubNLogN.Machine.Arith.Shift
import SubNLogN.Assembly.Row46Layer

/-!
# K4: the Walsh-middle field wired from its parts (`Machine/FFT/WalshMiddleFinal.lean`)

`walshMiddle_of_open`: proves `WalshMiddleMachineStmt (midLayerParams row46Layer 1)`
(`Contracts/FFT.lean`; the field `walshMiddle` of `Assembly.KernelCut4`) conditional only on
`LayerMachineStmt (midLayerParams row46Layer 1)` — Proposition A.11's layer machine at the
middle's constants, which supplies the cutoff `P₀`.

Everything else is plugged in from proved theorems: `walshMiddleMachine_of_parts` (WF) with
`phaseTableMachine_holds`; `FFT.DIF.recordDIF_holds` with `Arith.halfSumDiff_holds` and
`Arith.cmulTrunc_holds`; `layoutExec_holds_of_posPerm` (both maps) with
`positionalPermMachine_of_leaves`, `cubeLayer_of_layerMachine`, the four scans
(`WalshScanAux.cnotScan_of_selPhase cnotScanSelPhase_holds`) and `posPermSched_holds`;
`roundsStmt_of_parts` with `FFT.PrefixAux.prefixRound_of` (`FFT.prefixParam_holds`,
`prefixPass_holds`, `Arith.truncShift_holds`), `chunkRound_of_cubeLayer` and `FFT.twiddlePass_holds`
(`MulBig.mulBig_holds`, `Arith.cmulTruncBcast_holds`, `FFT.twiddleAddr_holds`). No `sorry`.
-/

namespace SubNLogN.Machine

open SubNLogN.Assembly

/-- **The Walsh middle at Proposition A.11's bands of `midLayerParams row46Layer 1`, from the
layer machine** (Corollary 6.6, `cor:walsh-middle`): the only hypothesis is the layer machine
at the middle's constants, which supplies the cutoff `P₀`. -/
theorem walshMiddle_of_open (hLayer : LayerMachineStmt (midLayerParams row46Layer 1)) :
    WalshMiddleMachineStmt (midLayerParams row46Layer 1) := by
  obtain ⟨P₀, hL⟩ := hLayer
  refine ⟨P₀, ?_⟩
  have hLay := cubeLayer_of_layerMachine hL
  have hPP := positionalPermMachine_of_leaves hLay
    (WalshScanAux.cnotScan_of_selPhase cnotScanSelPhase_holds) posPermSched_holds
  exact walshMiddleMachine_of_parts phaseTableMachine_holds
    (FFT.DIF.recordDIF_holds Arith.halfSumDiff_holds Arith.cmulTrunc_holds)
    (layoutExec_holds_of_posPerm hPP .L)
    (roundsStmt_of_parts
      (FFT.PrefixAux.prefixRound_of FFT.prefixParam_holds FFT.PrefixPassAux.prefixPass_holds
        Arith.truncShift_holds)
      (chunkRound_of_cubeLayer hLay)
      (FFT.twiddlePass_holds MulBig.mulBig_holds Arith.cmulTruncBcast_holds
        FFT.twiddleAddr_holds))
    (layoutExec_holds_of_posPerm hPP .U)

end SubNLogN.Machine
