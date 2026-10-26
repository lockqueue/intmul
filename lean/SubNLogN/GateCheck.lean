import SubNLogN.Gate
import SubNLogN.Headline
import SubNLogN.S5.HeadlineCost
import SubNLogN.S5.TopExtended
import SubNLogN.S5.TopObligation
import SubNLogN.Assembly.KernelCutFinal
import SubNLogN.Math.Networks.Proofs.H2Final
import SubNLogN.S5.PipeExtended
import SubNLogN.S5.Pipe.BridgePipe
import SubNLogN.Assembly.KernelCut
import SubNLogN.Assembly.KernelCut3
import SubNLogN.Assembly.KernelCut4
import SubNLogN.Assembly.KernelCutFinal
import SubNLogN.Math.Networks.Proofs.AppCGuardFinal
import SubNLogN.Assembly.ChallengeHeadline
import SubNLogN.Math.Cost.WalshOKW8
import SubNLogN.Machine.Pipe.Contract

/-!
# G1 Integration Gate for `SubNLogN`

Runs `#subnlogn_gate_modules SubNLogN` and `#subnlogn_gate_check` on all exported headline theorems
of `SubNLogN.Headline`, plus `#print axioms` on every headline.
-/

#subnlogn_gate_check [
  SubNLogN.intMul_TM2_sub_nlogn,
  SubNLogN.intMul_TM2_sub_nlogn_46,
  SubNLogN.intMul_TM2_sub_nlogn_47,
  SubNLogN.intMul_TM2_sub_nlogn_56,
  SubNLogN.intMul_TM2_littleO_nlogn,
  SubNLogN.headline_S5_scheduleAndMain,
  SubNLogN.Assembly.intMul_challenge,
  SubNLogN.S5.kernelCut7_holds,
  SubNLogN.S5.w9SubNLogNSpecX_holds,
  SubNLogN.headline_S1_tripleNetworks_h100,
  SubNLogN.headline_S2_tapeTransfer,
  SubNLogN.headline_S3_walshAndDirectFFT,
  SubNLogN.headline_S4_bridgePrecision,
  SubNLogN.S5.walsh_row_46_admissible_and_slack,
  SubNLogN.S5.bluestein_rows_slack,
  SubNLogN.S5.headline_46_of_cutoff_and_accelerator,
  SubNLogN.S5.headline_46_of_core_workProg,
  SubNLogN.S5.headline_46_of_w9_subNLogN,
  SubNLogN.S5.headline_46_of_w9_pipe,
  SubNLogN.S5.headlineCost_of_stageBounds,
  SubNLogN.S5.headline_46_of_cutoff_and_accelerator',
  SubNLogN.S5.headline_46_of_core_workProg',
  SubNLogN.S5.headline_46_of_w9_subNLogN',
  SubNLogN.S5.w9SubNLogNSpec'_of_pipe',
  SubNLogN.S5.headline_46_of_w9_pipe',
  SubNLogN.S5.headline_46_of_w9X,
  SubNLogN.S5.w9X_of_w9',
  SubNLogN.S5.w9X_of_w9'_big,
  SubNLogN.S5.w9X_of_pipeX,
  SubNLogN.S5.headline_46_of_w9_pipeX,
  SubNLogN.S5.pipeX_of_pipe',
  SubNLogN.Assembly.w9X_of_contracts,
  SubNLogN.Assembly.w9X_of_cut,
  SubNLogN.Assembly.walshBranchCut_of_kernelCut,
  SubNLogN.Assembly.w9X_of_kernelCut,
  SubNLogN.Assembly.kernelCutStmt_of_2,
  SubNLogN.Assembly.kernelCut2Stmt_of_3,
  SubNLogN.Assembly.kernelCutStmt_of_3,
  SubNLogN.Assembly.w9X_of_kernelCut3,
  SubNLogN.Assembly.kernelCut3Stmt_of_4,
  SubNLogN.Assembly.kernelCutStmt_of_4,
  SubNLogN.Assembly.w9X_of_kernelCut4,
  SubNLogN.Assembly.kernelCut4_of_5,
  SubNLogN.Assembly.kernelCut5_of_6,
  SubNLogN.Assembly.kernelCut6_of_7,
  SubNLogN.Assembly.kernelCutStmt_of_7,
  SubNLogN.Assembly.w9X_of_kernelCut7,
  SubNLogN.Assembly.kernelCut7_of_mid,
  SubNLogN.Assembly.w9X_of_mid,
  SubNLogN.Machine.c6_holds,
  SubNLogN.Math.Networks.prop71Guard_holds,
  SubNLogN.Math.Networks.prop71_final,
  SubNLogN.Assembly.challenge_of_spec,
  SubNLogN.Machine.Pipe.exists_pipeFnewX,
  SubNLogN.Math.Cost.walshOK_eventually_holds,
  SubNLogN.Math.Networks.bitNetCert_holds,
  SubNLogN.Math.Networks.complexNetCert_holds,
  SubNLogN.Math.Networks.h2_bit_general,
  SubNLogN.Math.Networks.h2_complex_general,
  SubNLogN.S5.rootOKSubNLogN_computablePaperFastDFT,
  SubNLogN.S5.Pipe.w9_pipeline_proved,
  SubNLogN.S5.Pipe.specSpreadSlots_headline_pow15_le,
  SubNLogN.S5.Pipe.leaf_and_twistColLeaf_pow15_le,
  SubNLogN.S5.Pipe.T_stream_pow15_le,
  SubNLogN.S5.Pipe.bruhat_shear_bridge_certificate,
  SubNLogN.S5.Pipe.walshTripleButterflyBridge_holds,
  SubNLogN.S5.Pipe.w9_pipeline_headline_runs
]

#subnlogn_gate_expect_modules [SubNLogN] errors [] warnings []

#subnlogn_gate_crosscheck_modules [SubNLogN]

#subnlogn_gate_modules SubNLogN

#subnlogn_gate_expect [
  SubNLogN.intMul_TM2_sub_nlogn,
  SubNLogN.intMul_TM2_sub_nlogn_46,
  SubNLogN.intMul_TM2_sub_nlogn_47,
  SubNLogN.intMul_TM2_sub_nlogn_56,
  SubNLogN.intMul_TM2_littleO_nlogn,
  SubNLogN.headline_S1_tripleNetworks_h100,
  SubNLogN.headline_S2_tapeTransfer,
  SubNLogN.headline_S3_walshAndDirectFFT,
  SubNLogN.headline_S4_bridgePrecision,
  SubNLogN.headline_S5_scheduleAndMain
] errors [] warnings []

#subnlogn_gate_crosscheck [
  SubNLogN.intMul_TM2_sub_nlogn,
  SubNLogN.intMul_TM2_sub_nlogn_46,
  SubNLogN.intMul_TM2_sub_nlogn_47,
  SubNLogN.intMul_TM2_sub_nlogn_56,
  SubNLogN.intMul_TM2_littleO_nlogn,
  SubNLogN.headline_S1_tripleNetworks_h100,
  SubNLogN.headline_S2_tapeTransfer,
  SubNLogN.headline_S3_walshAndDirectFFT,
  SubNLogN.headline_S4_bridgePrecision,
  SubNLogN.headline_S5_scheduleAndMain
]

#print axioms SubNLogN.headline_S1_tripleNetworks_h100
#print axioms SubNLogN.headline_S2_tapeTransfer
#print axioms SubNLogN.headline_S3_walshAndDirectFFT
#print axioms SubNLogN.headline_S4_bridgePrecision
#print axioms SubNLogN.S5.walsh_row_46_admissible_and_slack
#print axioms SubNLogN.S5.bluestein_rows_slack
#print axioms SubNLogN.S5.headline_46_of_cutoff_and_accelerator
#print axioms SubNLogN.S5.headline_46_of_core_workProg
#print axioms SubNLogN.S5.headline_46_of_w9_subNLogN
#print axioms SubNLogN.S5.headline_46_of_w9_pipe
#print axioms SubNLogN.S5.rootOKSubNLogN_computablePaperFastDFT
#print axioms SubNLogN.S5.headline_46_of_cutoff_and_accelerator'
#print axioms SubNLogN.S5.headline_46_of_core_workProg'
#print axioms SubNLogN.S5.headline_46_of_w9_subNLogN'
#print axioms SubNLogN.S5.w9SubNLogNSpec'_of_pipe'
#print axioms SubNLogN.S5.headline_46_of_w9_pipe'
#print axioms SubNLogN.S5.headline_46_of_w9X
#print axioms SubNLogN.S5.w9X_of_w9'_big
#print axioms SubNLogN.S5.w9X_of_pipeX
#print axioms SubNLogN.Assembly.w9X_of_cut
#print axioms SubNLogN.Assembly.walshBranchCut_of_kernelCut
#print axioms SubNLogN.Assembly.w9X_of_kernelCut
#print axioms SubNLogN.Assembly.kernelCutStmt_of_2
#print axioms SubNLogN.Assembly.kernelCut2Stmt_of_3
#print axioms SubNLogN.Assembly.kernelCutStmt_of_3
#print axioms SubNLogN.Assembly.w9X_of_kernelCut3
#print axioms SubNLogN.Assembly.kernelCut3Stmt_of_4
#print axioms SubNLogN.Assembly.kernelCutStmt_of_4
#print axioms SubNLogN.Assembly.w9X_of_kernelCut4
#print axioms SubNLogN.Assembly.kernelCut4_of_5
#print axioms SubNLogN.Assembly.kernelCut5_of_6
#print axioms SubNLogN.Assembly.kernelCut6_of_7
#print axioms SubNLogN.Assembly.kernelCutStmt_of_7
#print axioms SubNLogN.Assembly.w9X_of_kernelCut7
#print axioms SubNLogN.Assembly.kernelCut7_of_mid
#print axioms SubNLogN.Assembly.w9X_of_mid
#print axioms SubNLogN.Machine.c6_holds
#print axioms SubNLogN.Math.Networks.prop71Guard_holds
#print axioms SubNLogN.Math.Networks.prop71_final
#print axioms SubNLogN.Assembly.challenge_of_spec
#print axioms SubNLogN.Assembly.intMul_challenge
#print axioms SubNLogN.Machine.Pipe.exists_pipeFnewX
#print axioms SubNLogN.Math.Cost.walshOK_eventually_holds
#print axioms SubNLogN.Math.Networks.bitNetCert_holds
#print axioms SubNLogN.Math.Networks.complexNetCert_holds
#print axioms SubNLogN.Math.Networks.h2_bit_general
#print axioms SubNLogN.Math.Networks.h2_complex_general
#print axioms SubNLogN.intMul_TM2_sub_nlogn
#print axioms SubNLogN.intMul_TM2_sub_nlogn_46
#print axioms SubNLogN.intMul_TM2_sub_nlogn_47
#print axioms SubNLogN.intMul_TM2_sub_nlogn_56
#print axioms SubNLogN.intMul_TM2_littleO_nlogn
#print axioms SubNLogN.headline_S5_scheduleAndMain
#print axioms SubNLogN.S5.kernelCut7_holds
