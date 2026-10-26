import IntMul.Preliminaries
import IntMul.Theorem1TwistedDuality
import IntMul.Theorem2PoissonIdentity
import IntMul.Theorem3BidiagonalAndSchedule
import IntMul.Theorem4KroneckerSpread
import IntMul.Theorem5ComplexityAndCorrectness
import IntMul.Theorem6And7Barriers
import IntMul.ExecutableAlgorithm
import IntMul.MaterializedAndComputable

/-!
# Automated Verification Check for `IntMul` Declarations

Every exported Lean declaration of `IntMul` (our independent formalization of the two-dimensional `O(n log n)` multiplier of `[MS]`)
(across `Preliminaries`, `Theorem1`–`Theorem7`, `ExecutableAlgorithm`, and `MaterializedAndComputable`) is checked via
`#check` so that any future rename or removal fails CI immediately.
-/
namespace IntMul

section G3DocChecks
#guard_msgs (drop info) in #check @BitCostM
#guard_msgs (drop info) in #check @ChunkSplitTree
#guard_msgs (drop info) in #check @ChunkSplitTree.Valid
#guard_msgs (drop info) in #check @ChunkSplitTree.spawnedLeaves
#guard_msgs (drop info) in #check @ChunkSplitTree.transformWork
#guard_msgs (drop info) in #check @ChunkSplitTree.zeroPaddedWork
#guard_msgs (drop info) in #check @ComputableExactFastDFTSpec
#guard_msgs (drop info) in #check @ComputablePaperFastDFTSpec
#guard_msgs (drop info) in #check @FFTVec
#guard_msgs (drop info) in #check @FastDFTSpec
#guard_msgs (drop info) in #check @FastDFTSpec.Valid
#guard_msgs (drop info) in #check @FitsSignedWord
#guard_msgs (drop info) in #check @MultiTapeFlatten2DState
#guard_msgs (drop info) in #check @MultiTapeParityInterleaveState
#guard_msgs (drop info) in #check @MultiTapeRunInterleaveState
#guard_msgs (drop info) in #check @MultiTapeScanState
#guard_msgs (drop info) in #check @MultiTapeUnshuffleState
#guard_msgs (drop info) in #check @PacketMatrix
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.Valid
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.intrinsicCost
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.intrinsicCostLeafMul
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.intrinsicCostRadix2Leaf
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.p
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.paperStopTotalCost_eq_three_terms
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.precomputeCost
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.precomputeRawTapCost
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.radix2LeafCost
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.stepOverheadCost
#guard_msgs (drop info) in #check @QuantizedFastDFTSpec.synAndRouteCost
#guard_msgs (drop info) in #check @RecordHeadStepValid
#guard_msgs (drop info) in #check @RecordTraceValid
#guard_msgs (drop info) in #check @ValidTransposeTrace
#guard_msgs (drop info) in #check @ValidTwoRegStep
#guard_msgs (drop info) in #check @abs_divRoundPow2_mul_sub_le
#guard_msgs (drop info) in #check @abs_realQuantizeInt_le
#guard_msgs (drop info) in #check @abs_sincGaussian_le_geometric_of_le_abs
#guard_msgs (drop info) in #check @abs_sincGaussian_le_of_le_abs
#guard_msgs (drop info) in #check @addBitCost
#guard_msgs (drop info) in #check @addMod2Pow
#guard_msgs (drop info) in #check @baseRadix2FFTExact
#guard_msgs (drop info) in #check @baseRadix2FFTExact_eq_dft1D
#guard_msgs (drop info) in #check @baseRadix2FFTQuantized
#guard_msgs (drop info) in #check @baseRadix2FFTQuantizedCore
#guard_msgs (drop info) in #check @bitCellDistance_le_of_recordHeadStepValid
#guard_msgs (drop info) in #check @bitCellHeadMovesOfRecordTrace
#guard_msgs (drop info) in #check @bitCellHeadMovesOfRecordTrace_le_two_mul_width_mul_steps
#guard_msgs (drop info) in #check @bitHeadOfRecord
#guard_msgs (drop info) in #check @bitRev
#guard_msgs (drop info) in #check @boxGaussianStepSpec
#guard_msgs (drop info) in #check @boxGaussianStepSpec_valid
#guard_msgs (drop info) in #check @buildComputableZHomFwdWithProgramCost
#guard_msgs (drop info) in #check @buildComputableZPartFwdWithProgramCost
#guard_msgs (drop info) in #check @buildComputableZPartNyqWithProgramCost
#guard_msgs (drop info) in #check @buildQuantizedSpec
#guard_msgs (drop info) in #check @buildQuantizedSpecPaperStop
#guard_msgs (drop info) in #check @buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le
#guard_msgs (drop info) in #check @buildQuantizedSpecPaperStop_paperStopTotalCost_le_quad
#guard_msgs (drop info) in #check @buildQuantizedSpecPaperStop_radix2LeafCost_le
#guard_msgs (drop info) in #check @buildQuantizedSpecPaperStop_valid
#guard_msgs (drop info) in #check @buildQuantizedSpec_intrinsicCostLeafMul_eq
#guard_msgs (drop info) in #check @buildQuantizedSpec_intrinsicCost_le
#guard_msgs (drop info) in #check @buildQuantizedSpec_intrinsicCost_le_quad_leafPrecision
#guard_msgs (drop info) in #check @buildQuantizedSpec_precomputeCost_le
#guard_msgs (drop info) in #check @buildQuantizedSpec_precomputeCost_le_quad_leafPrecision
#guard_msgs (drop info) in #check @buildQuantizedSpec_precomputeRawTapCost_le
#guard_msgs (drop info) in #check @buildQuantizedSpec_precomputeRawTapCost_le_quad_of_sq_le_sqrt
#guard_msgs (drop info) in #check @buildQuantizedSpec_valid
#guard_msgs (drop info) in #check @buildZHomFwdArray
#guard_msgs (drop info) in #check @buildZPartFwdArray
#guard_msgs (drop info) in #check @buildZPartNyqArray
#guard_msgs (drop info) in #check @butterfly_error_non_amplification
#guard_msgs (drop info) in #check @bwdRevRHS
#guard_msgs (drop info) in #check @c0Coeff_alphaSchedule_gt_049999999
#guard_msgs (drop info) in #check @c0_div_c1_pow_le_015_of_balanced
#guard_msgs (drop info) in #check @c0_sub_c1_alphaSchedule_ge
#guard_msgs (drop info) in #check @c1Coeff_alphaSchedule_gt_049999999
#guard_msgs (drop info) in #check @c1_div_c0_pow_le_015_of_balanced
#guard_msgs (drop info) in #check @complexNearestQuantizeMaxErr
#guard_msgs (drop info) in #check @complexQuantize
#guard_msgs (drop info) in #check @complexQuantizeMaxErr
#guard_msgs (drop info) in #check @complexQuantizeMaxErr_lt
#guard_msgs (drop info) in #check @complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow
#guard_msgs (drop info) in #check @complex_square_error_bound
#guard_msgs (drop info) in #check @computableBaseDFTExact
#guard_msgs (drop info) in #check @computableBaseRadix2FFTWithProgramCost
#guard_msgs (drop info) in #check @computableBaseRadix2FFTWithProgramCost_snd_le
#guard_msgs (drop info) in #check @computableExactFastDFT
#guard_msgs (drop info) in #check @computableExactFastDFTMultiply
#guard_msgs (drop info) in #check @computableExactFastDFTMultiplyWithCost
#guard_msgs (drop info) in #check @computableExactFastDFTMultiplyWithCost_snd_eq
#guard_msgs (drop info) in #check @computableExactFastDFTMultiply_eq_mul
#guard_msgs (drop info) in #check @computableExactFastDFTMultiply_eq_quantizedFastDFTMultiply
#guard_msgs (drop info) in #check @computableExactFastDFTMultiply_two_level_test
#guard_msgs (drop info) in #check @computableExactFastDFTWithCost
#guard_msgs (drop info) in #check @computableExactFastDFTWithCost_snd_eq
#guard_msgs (drop info) in #check @computableExactMultiplyOfBitLength
#guard_msgs (drop info) in #check @computableExactMultiplyOfBitLengthWithCost
#guard_msgs (drop info) in #check @computableExactMultiplyOfBitLengthWithCost_correct_and_isBigO
#guard_msgs (drop info) in #check @computableExactMultiplyOfBitLength_eq_mul
#guard_msgs (drop info) in #check @computableExactSolvers_three_regimes_test
#guard_msgs (drop info) in #check @computableKroneckerBitStride
#guard_msgs (drop info) in #check @computableMulBitCost
#guard_msgs (drop info) in #check @computableMulBitCost_eq
#guard_msgs (drop info) in #check @computableNegacyclicDirect
#guard_msgs (drop info) in #check @computableNyquistAltSumContiguous
#guard_msgs (drop info) in #check @computableNyquistAltSumContiguousWithProgramCost
#guard_msgs (drop info) in #check @computableOddStrideFactor
#guard_msgs (drop info) in #check @computableOddStrideInvPow2
#guard_msgs (drop info) in #check @computableOddStrideInvPow2_eq_oddStrideInvPow2
#guard_msgs (drop info) in #check @computablePackChunksExact
#guard_msgs (drop info) in #check @computablePaperFastDFTMultiplyWithProgramCost
#guard_msgs (drop info) in #check @computablePaperFastDFTMultiply_eq_mul
#guard_msgs (drop info) in #check @computablePaperFastDFTMultiply_eq_quantizedFastDFTMultiplyRadix2Leaf
#guard_msgs (drop info) in #check @computablePaperFastDFTWithProgramCost
#guard_msgs (drop info) in #check @computablePaperFastDFTWithProgramCost_snd_le
#guard_msgs (drop info) in #check @computablePaperMultiplyOfBitLengthGivenSpecWithProgramCost
#guard_msgs (drop info) in #check @computableSolveBidiagonalBwdExact
#guard_msgs (drop info) in #check @computableSolveBidiagonalBwdExactWithSteps
#guard_msgs (drop info) in #check @computableSolveBidiagonalBwdWithProgramCost
#guard_msgs (drop info) in #check @computableSolveBidiagonalBwd_full_internal_steps_le
#guard_msgs (drop info) in #check @computableSolveBidiagonalFwdExact
#guard_msgs (drop info) in #check @computableSolveBidiagonalFwdExactWithSteps
#guard_msgs (drop info) in #check @computableSolveBidiagonalFwdWithProgramCost
#guard_msgs (drop info) in #check @computableSolveNyquistExact
#guard_msgs (drop info) in #check @computableSolveNyquistExactWithSteps
#guard_msgs (drop info) in #check @computableSolveNyquistWithProgramCost
#guard_msgs (drop info) in #check @computableSpreadRowBlockImContiguous
#guard_msgs (drop info) in #check @computableSpreadRowBlockImContiguousWithCost
#guard_msgs (drop info) in #check @computableSpreadRowBlockReContiguous
#guard_msgs (drop info) in #check @computableSpreadRowBlockReContiguousWithCost
#guard_msgs (drop info) in #check @computableSpreadRowContiguous
#guard_msgs (drop info) in #check @computableSpreadRowContiguousWithCost
#guard_msgs (drop info) in #check @computableSpreadRowContiguousWithProgramCost
#guard_msgs (drop info) in #check @computableSyntheticFFTRadix2
#guard_msgs (drop info) in #check @computableSyntheticFFTRadix2WithCost
#guard_msgs (drop info) in #check @computableSyntheticFFTRadix2WithProgramCost
#guard_msgs (drop info) in #check @computableSyntheticFFTRadix2_size
#guard_msgs (drop info) in #check @computableSyntheticFFTRadix2_test
#guard_msgs (drop info) in #check @concreteLocalOvhBitOps_eq_of_window_width_cancellation
#guard_msgs (drop info) in #check @concreteLocalSynBitOps_eq_of_syntheticFFTRadix2WithCost
#guard_msgs (drop info) in #check @continuous_modulated_poisson_summation
#guard_msgs (drop info) in #check @cooleyTukeyTwiddle
#guard_msgs (drop info) in #check @cosetExtract
#guard_msgs (drop info) in #check @costedButterflyAvg
#guard_msgs (drop info) in #check @costedDivRoundRatInt
#guard_msgs (drop info) in #check @costedGAdd
#guard_msgs (drop info) in #check @costedGCombineQuantize
#guard_msgs (drop info) in #check @costedGMulScaled
#guard_msgs (drop info) in #check @costedGNyqStepQuantize
#guard_msgs (drop info) in #check @costedGPreTwistU
#guard_msgs (drop info) in #check @costedGRatioQuantize
#guard_msgs (drop info) in #check @costedGRescale
#guard_msgs (drop info) in #check @costedGSub
#guard_msgs (drop info) in #check @cyclicConv
#guard_msgs (drop info) in #check @cyclicConv_getD_eq_polyMulList_getD
#guard_msgs (drop info) in #check @delta0Poly
#guard_msgs (drop info) in #check @demoTwoLevelComputableExactSpec
#guard_msgs (drop info) in #check @dft1D
#guard_msgs (drop info) in #check @dft1DGrid_alternating_sum_eq_midpoint
#guard_msgs (drop info) in #check @dft1DGrid_eq_dft1D
#guard_msgs (drop info) in #check @dft1D_complex_pack
#guard_msgs (drop info) in #check @dft1D_conj_inv_packNormalizedChunks_im_eq
#guard_msgs (drop info) in #check @dft1D_cyclicConv
#guard_msgs (drop info) in #check @dft1D_norm_le
#guard_msgs (drop info) in #check @dft2D
#guard_msgs (drop info) in #check @dft2D_sincGaussian_spread_eq_poisson_lhs
#guard_msgs (drop info) in #check @dft2D_spreadArray2Tap_eq
#guard_msgs (drop info) in #check @dftApproxConvApprox_round_eq
#guard_msgs (drop info) in #check @divRoundPow2
#guard_msgs (drop info) in #check @divRoundPow2_eq_realQuantizeInt
#guard_msgs (drop info) in #check @divRoundRatInt
#guard_msgs (drop info) in #check @erfcScaled_realErfScaled_le_gaussian_tail
#guard_msgs (drop info) in #check @executedKroneckerSpreadStepBitCost
#guard_msgs (drop info) in #check @executed_kronecker_spread_cost_le_kroneckerSpreadStepBitCost
#guard_msgs (drop info) in #check @extractSignedSlot_add_mul
#guard_msgs (drop info) in #check @extremalSlice
#guard_msgs (drop info) in #check @fastDFT
#guard_msgs (drop info) in #check @fastDFTBranchingCost
#guard_msgs (drop info) in #check @fastDFTBranchingCost_le_multiplyBitComplexityBound
#guard_msgs (drop info) in #check @fastDFTBranchingCost_root_bound
#guard_msgs (drop info) in #check @fastDFTBranchingCost_unit_expansion_eq
#guard_msgs (drop info) in #check @fastDFTMultiply
#guard_msgs (drop info) in #check @fastDFTMultiplyWithCost
#guard_msgs (drop info) in #check @fastDFTMultiplyWithCost_concrete_ops_bound
#guard_msgs (drop info) in #check @fastDFTMultiplyWithCost_snd_isBigO_n_log_n_of_bound
#guard_msgs (drop info) in #check @fastDFTMultiply_boxGaussianStepSpec_eq_mul
#guard_msgs (drop info) in #check @fastDFTMultiply_eq_mul
#guard_msgs (drop info) in #check @fastDFTQuantized
#guard_msgs (drop info) in #check @fastDFTWithCost
#guard_msgs (drop info) in #check @fastDFTWithCost_snd_eq_branchingCost
#guard_msgs (drop info) in #check @fastDFT_boxGaussianStepSpec_eq_dft1D
#guard_msgs (drop info) in #check @fastDFT_eq_dft1D
#guard_msgs (drop info) in #check @fastIDFT
#guard_msgs (drop info) in #check @fastIDFT_inverts_fastDFT
#guard_msgs (drop info) in #check @fastIDFT_pointwiseMul_fastDFT_eq_cyclicConv
#guard_msgs (drop info) in #check @finProdIntEquiv
#guard_msgs (drop info) in #check @fixedPointWordBits_le_four_mul_pChild
#guard_msgs (drop info) in #check @flatten2DHeadStep
#guard_msgs (drop info) in #check @floydMatrixPotential
#guard_msgs (drop info) in #check @floydMatrixPotential_init
#guard_msgs (drop info) in #check @floydMatrixPotential_target_pow2
#guard_msgs (drop info) in #check @fourier_eq_integral_stdChar
#guard_msgs (drop info) in #check @fourier_modulated_shift
#guard_msgs (drop info) in #check @fourier_sincGaussian_eq_box_gaussian_integral
#guard_msgs (drop info) in #check @fourier_sincGaussian_eq_gHatBox
#guard_msgs (drop info) in #check @gDivScaled
#guard_msgs (drop info) in #check @gMulScaled
#guard_msgs (drop info) in #check @gQuantizeRat
#guard_msgs (drop info) in #check @getFFTVec_syntheticFFTRadix2_cast_eq_syntheticDFT
#guard_msgs (drop info) in #check @getFFTVec_syntheticFFTRadix2_cast_eq_syntheticFFTRadix2C
#guard_msgs (drop info) in #check @infinite_poisson_spread_sub_passband_norm_le
#guard_msgs (drop info) in #check @initPacketMatrix
#guard_msgs (drop info) in #check @interleaveParityHeadStep
#guard_msgs (drop info) in #check @interleaveParityHeadStep_valid
#guard_msgs (drop info) in #check @interleaveParityPass
#guard_msgs (drop info) in #check @interleaveRunsHeadStep
#guard_msgs (drop info) in #check @interleaveRunsHeadStep_valid
#guard_msgs (drop info) in #check @interleaveRunsPass
#guard_msgs (drop info) in #check @intrinsic_leaf_only_cost_quadratic
#guard_msgs (drop info) in #check @isBigO_sincGaussian_modulated_cocompact
#guard_msgs (drop info) in #check @kroneckerBitStride
#guard_msgs (drop info) in #check @kroneckerCyclicIntMul
#guard_msgs (drop info) in #check @kroneckerHeadroom
#guard_msgs (drop info) in #check @kroneckerSincGaussianSpreadArray
#guard_msgs (drop info) in #check @kroneckerSincGaussianSpreadArray_eq_sum_Icc
#guard_msgs (drop info) in #check @kroneckerSincGaussianSpreadRowContiguousWithCost
#guard_msgs (drop info) in #check @kroneckerSincGaussianSpreadRowContiguousWithCost_snd_eq
#guard_msgs (drop info) in #check @kroneckerSincGaussianSpreadRowMaterialized
#guard_msgs (drop info) in #check @kroneckerSpreadBlock_length_and_bitStride_bounds
#guard_msgs (drop info) in #check @kroneckerSpreadFilterTapsFolded
#guard_msgs (drop info) in #check @kroneckerSpreadNumBlocks
#guard_msgs (drop info) in #check @kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le
#guard_msgs (drop info) in #check @kroneckerSpreadRowBlockIm
#guard_msgs (drop info) in #check @kroneckerSpreadRowBlockRe
#guard_msgs (drop info) in #check @kroneckerSpreadStepBitCost
#guard_msgs (drop info) in #check @kroneckerSpreadStepBitCost_le
#guard_msgs (drop info) in #check @lemma1_synthetic_fft_rounding_bound
#guard_msgs (drop info) in #check @lemma2_child_amplification_error_bound
#guard_msgs (drop info) in #check @lemma2_inductive_error_closure
#guard_msgs (drop info) in #check @lemma2_inductive_error_closure_from_components
#guard_msgs (drop info) in #check @lemma2_inductive_error_closure_with_stopband
#guard_msgs (drop info) in #check @lemma2_inductive_error_closure_with_stopband_and_components
#guard_msgs (drop info) in #check @lemma2_sincGaussian_spatial_tail_bound
#guard_msgs (drop info) in #check @lemma2_termA_conditioning_mul_zpow_lt
#guard_msgs (drop info) in #check @lemma2_termA_sincGaussian_all_regimes_deconv_error_lt_of_balanced
#guard_msgs (drop info) in #check @lemma2_termA_sincGaussian_deconv_error_lt
#guard_msgs (drop info) in #check @lemma2_termA_sincGaussian_deconv_error_lt_of_balanced
#guard_msgs (drop info) in #check @lemma2_termA_sincGaussian_nyquist_deconv_error_lt
#guard_msgs (drop info) in #check @lemma2_termA_stopband_error_bound
#guard_msgs (drop info) in #check @lemma2_termBCD_error_bound
#guard_msgs (drop info) in #check @lemma2_windowed_child_amplification_error_bound
#guard_msgs (drop info) in #check @lemma2_windowed_child_and_solver_amplification_error_bound
#guard_msgs (drop info) in #check @log2_mul_add_one_le
#guard_msgs (drop info) in #check @log2_succ_mul_subMulRate_le_27_sq
#guard_msgs (drop info) in #check @materialize1D
#guard_msgs (drop info) in #check @materialize2D
#guard_msgs (drop info) in #check @materializeSpecRawTablesWithCost
#guard_msgs (drop info) in #check @maxChunkSeq
#guard_msgs (drop info) in #check @max_c0_c1_alphaSchedule_gt_049999999
#guard_msgs (drop info) in #check @mulBitCost
#guard_msgs (drop info) in #check @mulBitCostScaleFactor
#guard_msgs (drop info) in #check @mulBitCost_mul_le
#guard_msgs (drop info) in #check @mulBitCost_raw_temporaries_le_four_mul_pChild
#guard_msgs (drop info) in #check @multiplyBitComplexityBound
#guard_msgs (drop info) in #check @multitapeBitCellSteps
#guard_msgs (drop info) in #check @multitapeBitCellSteps_eq_recordSteps_mul_width
#guard_msgs (drop info) in #check @natDist
#guard_msgs (drop info) in #check @natLog2Fuel
#guard_msgs (drop info) in #check @natLog2Fuel_self
#guard_msgs (drop info) in #check @negacyclicShiftInt_cast_eq_negacyclicShiftIter
#guard_msgs (drop info) in #check @negacyclicShiftIter
#guard_msgs (drop info) in #check @negacyclicShiftIter_add
#guard_msgs (drop info) in #check @negacyclicShiftIter_add_steps
#guard_msgs (drop info) in #check @negacyclicShiftIter_cosetExtract_eq
#guard_msgs (drop info) in #check @negacyclicShiftIter_delta0_eval
#guard_msgs (drop info) in #check @negacyclicShiftIter_eval
#guard_msgs (drop info) in #check @negacyclicShiftIter_smul
#guard_msgs (drop info) in #check @negacyclicShiftStep_eval
#guard_msgs (drop info) in #check @normSinc
#guard_msgs (drop info) in #check @norm_baseRadix2FFTQuantized_sub_dft1D_le
#guard_msgs (drop info) in #check @norm_dft2D_kroneckerSincGaussianSpreadArray_sub_le
#guard_msgs (drop info) in #check @norm_dft2D_windowedSincGaussianSpreadArray_sub_le
#guard_msgs (drop info) in #check @norm_kroneckerSincGaussianSpreadArray_le
#guard_msgs (drop info) in #check @norm_kroneckerSincGaussianSpreadArray_sub_lt
#guard_msgs (drop info) in #check @norm_kroneckerSincGaussianSpreadArray_sub_windowed_lt
#guard_msgs (drop info) in #check @norm_qPost_le_two_pow_pChild
#guard_msgs (drop info) in #check @norm_sincGaussianSpreadArray_le
#guard_msgs (drop info) in #check @norm_solveBidiagonalFwdQuantized_sub_effRHS_le
#guard_msgs (drop info) in #check @norm_solveNyquistQuantized_sub_effRHS_le
#guard_msgs (drop info) in #check @norm_spread_row_table_perturbation_le
#guard_msgs (drop info) in #check @norm_stdChar
#guard_msgs (drop info) in #check @norm_stepPostTwist_le_r_add_one_mul
#guard_msgs (drop info) in #check @norm_stepRoutedChildOut_le
#guard_msgs (drop info) in #check @norm_syntheticFFTRadix2Quantized_sub_le
#guard_msgs (drop info) in #check @norm_syntheticFFTRadix2Quantized_sub_syntheticDFT_le
#guard_msgs (drop info) in #check @norm_twiddle_table_perturbation_le
#guard_msgs (drop info) in #check @norm_windowedSincGaussianSpreadArray_le
#guard_msgs (drop info) in #check @norm_windowedSincGaussianSpreadArray_le_window
#guard_msgs (drop info) in #check @norm_windowedSincGaussianSpreadArray_sub_lt
#guard_msgs (drop info) in #check @norm_windowedSincGaussianSpreadArray_sub_lt_tight
#guard_msgs (drop info) in #check @norm_zHomFwdQuantized_sub_le
#guard_msgs (drop info) in #check @norm_zPartFwdQuantized_le
#guard_msgs (drop info) in #check @norm_zPartNyqQuantized_le
#guard_msgs (drop info) in #check @nyquistAltSum
#guard_msgs (drop info) in #check @nyquistAltSumContiguous
#guard_msgs (drop info) in #check @oddModInvPow2Iter
#guard_msgs (drop info) in #check @oddModInvPow2Iter_dvd
#guard_msgs (drop info) in #check @oddStrideEquiv
#guard_msgs (drop info) in #check @oddStrideEquiv_bijective
#guard_msgs (drop info) in #check @oddStrideFactor
#guard_msgs (drop info) in #check @oddStrideFactor_mod_two
#guard_msgs (drop info) in #check @oddStrideFactor_mul_mod_eq
#guard_msgs (drop info) in #check @oddStrideInvPow2
#guard_msgs (drop info) in #check @oddStrideInvPow2_congr
#guard_msgs (drop info) in #check @odd_coprime_two_pow
#guard_msgs (drop info) in #check @one_le_log_of_three_le
#guard_msgs (drop info) in #check @overlapAddBucketsSinglePass
#guard_msgs (drop info) in #check @overlapAddBucketsSinglePassWithCost
#guard_msgs (drop info) in #check @packNormalizedChunks
#guard_msgs (drop info) in #check @packSignedKronecker
#guard_msgs (drop info) in #check @packSignedKronecker_polyAddInt
#guard_msgs (drop info) in #check @packSignedKronecker_polyMulInt
#guard_msgs (drop info) in #check @packSignedKronecker_polyScaleInt
#guard_msgs (drop info) in #check @phiQuotientRingHom
#guard_msgs (drop info) in #check @polyMulInt
#guard_msgs (drop info) in #check @polyMulKroneckerSigned
#guard_msgs (drop info) in #check @polyMulKroneckerSignedComputable
#guard_msgs (drop info) in #check @polyMulKroneckerSigned_eq_polyMulInt
#guard_msgs (drop info) in #check @polyMulKroneckerSigned_kroneckerHeadroom_eq
#guard_msgs (drop info) in #check @polyMulList
#guard_msgs (drop info) in #check @precomputeStepBitCost
#guard_msgs (drop info) in #check @precomputeStepBitCost_le
#guard_msgs (drop info) in #check @precomputeStepBitCost_le_precomputeStepRawTapBitCost
#guard_msgs (drop info) in #check @precomputeStepRawTapBitCost
#guard_msgs (drop info) in #check @programCost_callsite_operand_widths_covered
#guard_msgs (drop info) in #check @programCost_leaf_baseRadix2FFT_widths_sound
#guard_msgs (drop info) in #check @programCost_nyquist_altSum_widths_sound
#guard_msgs (drop info) in #check @programCost_root_pipeline_widths_sound
#guard_msgs (drop info) in #check @programCost_solvers_widths_sound
#guard_msgs (drop info) in #check @programCost_spread_widths_sound
#guard_msgs (drop info) in #check @programCost_twist_and_syntheticFFT_widths_sound
#guard_msgs (drop info) in #check @programCost_widths_sound
#guard_msgs (drop info) in #check @quantizeInt
#guard_msgs (drop info) in #check @quantizedBoxGaussianStepSpec
#guard_msgs (drop info) in #check @quantizedBoxGaussianStepSpec_valid
#guard_msgs (drop info) in #check @quantizedFastDFTConvApprox
#guard_msgs (drop info) in #check @quantizedFastDFTConvApprox_round_eq
#guard_msgs (drop info) in #check @quantizedFastDFTMultiply
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyIntrinsicCost
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyIntrinsicCost_snd_le
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyMaterialized
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyMaterializedWithCost
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyMaterializedWithCost_snd_eq
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyMaterialized_eq_mul
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyMaterialized_eq_quantizedFastDFTMultiply
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyRadix2Leaf
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyRadix2Leaf_eq_mul
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyWithCost
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyWithCost_eq_mul_and_le_multiplyBitComplexityBound
#guard_msgs (drop info) in #check @quantizedFastDFTMultiplyWithCost_snd_isBigO_n_log_n_of_bound
#guard_msgs (drop info) in #check @quantizedFastDFTMultiply_eq_mul
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLength
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLengthMaterialized
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLengthMaterialized_correct_and_isBigO
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLengthMaterialized_eq_quantizedMultiplyOfBitLength
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLengthPaperStop_correct_and_isBigO
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLengthPaperStop_snd_le_n_log_n_of_log2_ge_96
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLength_fst_eq_mul
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLength_leafPrecision_sq_le_two_pow_half_K0
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLength_snd_isBigO_n_log_n
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLength_snd_le_n_log_n
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLength_snd_le_n_log_n_of_log2_ge_96
#guard_msgs (drop info) in #check @quantized_coeff_ratio_pow_le
#guard_msgs (drop info) in #check @radixBMBOperator
#guard_msgs (drop info) in #check @radixBMBOperatorInt
#guard_msgs (drop info) in #check @radixBSyntheticStage
#guard_msgs (drop info) in #check @read1D
#guard_msgs (drop info) in #check @read1D_kroneckerSincGaussianSpreadRowContiguousWithCost_eq
#guard_msgs (drop info) in #check @read1D_runFlatten2DSteps_eq
#guard_msgs (drop info) in #check @read1D_runMultiTapeAffineOddRoute_eq
#guard_msgs (drop info) in #check @read1D_runMultiTapeAffineOddRoute_index_eq
#guard_msgs (drop info) in #check @read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq
#guard_msgs (drop info) in #check @read1D_runMultiTapeTranspose_eq
#guard_msgs (drop info) in #check @read1D_runMultiTapeTranspose_index_eq
#guard_msgs (drop info) in #check @read1D_runMultiTapeTranspose_mat_eq
#guard_msgs (drop info) in #check @read1D_sincGaussianFastDFTMaterialized_eq
#guard_msgs (drop info) in #check @read2D
#guard_msgs (drop info) in #check @read2D_runScan2DWithSteps_of_lt
#guard_msgs (drop info) in #check @read2D_syntheticFFTRadix2Materialized_eq
#guard_msgs (drop info) in #check @realErf
#guard_msgs (drop info) in #check @realQuantize
#guard_msgs (drop info) in #check @realQuantizeInt
#guard_msgs (drop info) in #check @realQuantizeInt_mem_four_mul_pChild_word
#guard_msgs (drop info) in #check @realQuantizeMaxErr
#guard_msgs (drop info) in #check @realSinc_eq_intervalIntegral
#guard_msgs (drop info) in #check @reconstructChunksTree
#guard_msgs (drop info) in #check @reconstructChunksTreeWithProgramCost
#guard_msgs (drop info) in #check @recursiveMergeSortTapeCost
#guard_msgs (drop info) in #check @recursiveMergeSortTapeCost_eq
#guard_msgs (drop info) in #check @recursiveTransposeTapeCost
#guard_msgs (drop info) in #check @recursiveTransposeTapeCost_eq
#guard_msgs (drop info) in #check @reverseHeadStep
#guard_msgs (drop info) in #check @reverseHeadStep_valid
#guard_msgs (drop info) in #check @rootPipelineBitCost
#guard_msgs (drop info) in #check @rootPipelineBitCost_le_quad
#guard_msgs (drop info) in #check @routedColumnEntry
#guard_msgs (drop info) in #check @routedColumnEntry_eq
#guard_msgs (drop info) in #check @routedInputGather
#guard_msgs (drop info) in #check @routedInputGather_eq
#guard_msgs (drop info) in #check @routedOddStrideIndex
#guard_msgs (drop info) in #check @routedOddStrideIndex_eq_oddStrideInvPow2
#guard_msgs (drop info) in #check @routedTranspose2D
#guard_msgs (drop info) in #check @routedTranspose2D_eq
#guard_msgs (drop info) in #check @routingAndStreamingStepBitCost
#guard_msgs (drop info) in #check @routingAndStreamingStepBitCost_le
#guard_msgs (drop info) in #check @runBwdRevSteps
#guard_msgs (drop info) in #check @runBwdRevSteps_steps
#guard_msgs (drop info) in #check @runFlatten2DSteps
#guard_msgs (drop info) in #check @runFlatten2DSteps_steps
#guard_msgs (drop info) in #check @runInterleaveParitySteps
#guard_msgs (drop info) in #check @runInterleaveParitySteps_heads_and_eq
#guard_msgs (drop info) in #check @runInterleaveParitySteps_steps
#guard_msgs (drop info) in #check @runInterleaveRunsSteps
#guard_msgs (drop info) in #check @runInterleaveRunsSteps_eq_interleaveRunsPass
#guard_msgs (drop info) in #check @runInterleaveRunsSteps_steps
#guard_msgs (drop info) in #check @runMultiTapeAffineOddRoute
#guard_msgs (drop info) in #check @runMultiTapeAffineOddRouteFullSteps
#guard_msgs (drop info) in #check @runMultiTapeAffineOddRouteFullSteps_snd_le
#guard_msgs (drop info) in #check @runMultiTapeAffineOddRouteHeadSteps_eq
#guard_msgs (drop info) in #check @runMultiTapeAffineOddRouteWithSteps
#guard_msgs (drop info) in #check @runMultiTapeAffineOddRouteWithSteps_snd
#guard_msgs (drop info) in #check @runMultiTapeTranspose
#guard_msgs (drop info) in #check @runMultiTapeTransposeFullSteps
#guard_msgs (drop info) in #check @runMultiTapeTransposeFullSteps_snd_le
#guard_msgs (drop info) in #check @runMultiTapeTransposeHeadSteps_eq
#guard_msgs (drop info) in #check @runMultiTapeTransposeWithSteps
#guard_msgs (drop info) in #check @runMultiTapeTransposeWithSteps_snd
#guard_msgs (drop info) in #check @runReverseFromState
#guard_msgs (drop info) in #check @runReverseSteps
#guard_msgs (drop info) in #check @runReverseSteps_steps
#guard_msgs (drop info) in #check @runScan2DCostedWithSteps
#guard_msgs (drop info) in #check @runScan2DWithSteps
#guard_msgs (drop info) in #check @runScan2DWithSteps_snd
#guard_msgs (drop info) in #check @runSeekForwardSteps
#guard_msgs (drop info) in #check @runSeekForwardSteps_steps
#guard_msgs (drop info) in #check @runSequentialScanCostedSteps
#guard_msgs (drop info) in #check @runSequentialScanSteps
#guard_msgs (drop info) in #check @runUnshuffleSteps
#guard_msgs (drop info) in #check @runUnshuffleSteps_eq_unshufflePass
#guard_msgs (drop info) in #check @runUnshuffleSteps_steps
#guard_msgs (drop info) in #check @scanHeadStep
#guard_msgs (drop info) in #check @scanHeadStep_valid
#guard_msgs (drop info) in #check @seekForwardHeadStep
#guard_msgs (drop info) in #check @seekForwardHeadStep_valid
#guard_msgs (drop info) in #check @sequentialAffineOddRoute
#guard_msgs (drop info) in #check @sequentialAffineOddRouteWithPasses
#guard_msgs (drop info) in #check @sequentialAffineOddRoute_index_eq
#guard_msgs (drop info) in #check @sequentialColumnMergeSortBitCost
#guard_msgs (drop info) in #check @sequentialLinearScanBitCost
#guard_msgs (drop info) in #check @sequentialPassBitCost
#guard_msgs (drop info) in #check @sequentialTapeTranspose
#guard_msgs (drop info) in #check @sequentialTapeTransposeWithPasses
#guard_msgs (drop info) in #check @sequentialTapeTranspose_index_eq
#guard_msgs (drop info) in #check @sequentialTransposeBitCost
#guard_msgs (drop info) in #check @shiftSignedSlot_add_mul
#guard_msgs (drop info) in #check @signedExtremalSlice
#guard_msgs (drop info) in #check @sincGaussian
#guard_msgs (drop info) in #check @sincGaussianFastDFTMaterialized
#guard_msgs (drop info) in #check @sincGaussianFastDFTMaterializedWithCost
#guard_msgs (drop info) in #check @sincGaussianFastDFTMaterializedWithCost_snd_eq
#guard_msgs (drop info) in #check @sincGaussianFastDFTQuantized
#guard_msgs (drop info) in #check @sincGaussianFastDFTQuantizedIntrinsicCost
#guard_msgs (drop info) in #check @sincGaussianFastDFTQuantizedIntrinsicCost_snd_le_intrinsicCost
#guard_msgs (drop info) in #check @sincGaussianFastDFTQuantizedWithCost
#guard_msgs (drop info) in #check @sincGaussianFastDFTQuantized_error_le
#guard_msgs (drop info) in #check @sincGaussianFastDFTRadix2Leaf
#guard_msgs (drop info) in #check @sincGaussianFastDFTRadix2Leaf_error_le
#guard_msgs (drop info) in #check @sincGaussianModulatedMap
#guard_msgs (drop info) in #check @sincGaussianSpreadArray
#guard_msgs (drop info) in #check @sincGaussianSpreadArray_eq_tsum_int
#guard_msgs (drop info) in #check @sincGaussianSpreadTerm
#guard_msgs (drop info) in #check @sincGaussian_modulated_poisson_summation
#guard_msgs (drop info) in #check @solveBidiagonalBwd
#guard_msgs (drop info) in #check @solveBidiagonalBwdMaterialized
#guard_msgs (drop info) in #check @solveBidiagonalBwdMaterializedWithSteps
#guard_msgs (drop info) in #check @solveBidiagonalBwdQuantized
#guard_msgs (drop info) in #check @solveBidiagonalBwdQuantized_word_width_bounds
#guard_msgs (drop info) in #check @solveBidiagonalBwd_cyclic_error_bound_of_balanced
#guard_msgs (drop info) in #check @solveBidiagonalBwd_eq_solveBidiagonalFwd_rev
#guard_msgs (drop info) in #check @solveBidiagonalBwd_sincGaussian_dft2D_error_le_of_balanced
#guard_msgs (drop info) in #check @solveBidiagonalFwd
#guard_msgs (drop info) in #check @solveBidiagonalFwdMaterialized
#guard_msgs (drop info) in #check @solveBidiagonalFwdMaterializedWithSteps
#guard_msgs (drop info) in #check @solveBidiagonalFwdQuantized
#guard_msgs (drop info) in #check @solveBidiagonalFwd_cyclic_error_bound_of_balanced
#guard_msgs (drop info) in #check @solveBidiagonalFwd_cyclic_error_bound_relaxed
#guard_msgs (drop info) in #check @solveBidiagonalFwd_sincGaussian_dft2D_error_le_of_balanced
#guard_msgs (drop info) in #check @solveNyquist
#guard_msgs (drop info) in #check @solveNyquistMaterialized
#guard_msgs (drop info) in #check @solveNyquistMaterializedWithSteps
#guard_msgs (drop info) in #check @solveNyquistQuantized
#guard_msgs (drop info) in #check @solveNyquist_cyclic_error_bound
#guard_msgs (drop info) in #check @solveNyquist_error_bound
#guard_msgs (drop info) in #check @solveNyquist_error_bound_alphaSchedule
#guard_msgs (drop info) in #check @solveNyquist_error_bound_relaxed
#guard_msgs (drop info) in #check @solveNyquist_sincGaussian_dft2D_error_le
#guard_msgs (drop info) in #check @solver_bwd_recurrence_word_width_bounds
#guard_msgs (drop info) in #check @solver_outputs_word_width_bounds
#guard_msgs (drop info) in #check @solver_recurrence_word_width_bounds
#guard_msgs (drop info) in #check @splitChunksTree
#guard_msgs (drop info) in #check @splitChunksTreeWithProgramCost
#guard_msgs (drop info) in #check @spreadArray2Tap
#guard_msgs (drop info) in #check @sq_log_le_four_mul
#guard_msgs (drop info) in #check @sqrt_two_lt_1416
#guard_msgs (drop info) in #check @stdChar
#guard_msgs (drop info) in #check @stdChar_add
#guard_msgs (drop info) in #check @stdChar_add_int
#guard_msgs (drop info) in #check @stdChar_int
#guard_msgs (drop info) in #check @stdChar_orthogonality_range
#guard_msgs (drop info) in #check @stepPostTwist
#guard_msgs (drop info) in #check @stepPreTwist
#guard_msgs (drop info) in #check @stepRoutedChildOut
#guard_msgs (drop info) in #check @stepSpread
#guard_msgs (drop info) in #check @stepSyntheticOut
#guard_msgs (drop info) in #check @stepSyntheticStage
#guard_msgs (drop info) in #check @step_intermediate_word_width_bounds
#guard_msgs (drop info) in #check @subMulRate
#guard_msgs (drop info) in #check @subMulRate_mul_le_27_sq
#guard_msgs (drop info) in #check @sumArrayCosts
#guard_msgs (drop info) in #check @sumRangeInt
#guard_msgs (drop info) in #check @sumRangePair
#guard_msgs (drop info) in #check @sum_range_tsum_lattice_fold
#guard_msgs (drop info) in #check @summable_fourier_sincGaussian_modulated
#guard_msgs (drop info) in #check @summable_gHatBox_realErfScaled
#guard_msgs (drop info) in #check @summable_norm_restrict_sincGaussian_modulated
#guard_msgs (drop info) in #check @summable_norm_sincGaussian_modulated
#guard_msgs (drop info) in #check @syntheticDFT
#guard_msgs (drop info) in #check @syntheticDFTWithStride
#guard_msgs (drop info) in #check @syntheticFFTRadix2
#guard_msgs (drop info) in #check @syntheticFFTRadix2AddOps
#guard_msgs (drop info) in #check @syntheticFFTRadix2C
#guard_msgs (drop info) in #check @syntheticFFTRadix2C_eq_syntheticDFT
#guard_msgs (drop info) in #check @syntheticFFTRadix2C_eq_syntheticDFTWithStride
#guard_msgs (drop info) in #check @syntheticFFTRadix2Materialized
#guard_msgs (drop info) in #check @syntheticFFTRadix2MaterializedWithCost
#guard_msgs (drop info) in #check @syntheticFFTRadix2Materialized_size
#guard_msgs (drop info) in #check @syntheticFFTRadix2MulOps
#guard_msgs (drop info) in #check @syntheticFFTRadix2Ops_closed_form
#guard_msgs (drop info) in #check @syntheticFFTRadix2Quantized
#guard_msgs (drop info) in #check @syntheticFFTRadix2WithCost
#guard_msgs (drop info) in #check @syntheticFFTRadix2WithCost_closed_form
#guard_msgs (drop info) in #check @syntheticFFTRadix2_eq_direct
#guard_msgs (drop info) in #check @syntheticFFTStepBitCost
#guard_msgs (drop info) in #check @syntheticIFFTRadix2
#guard_msgs (drop info) in #check @syntheticIFFTRadix2_inverts_syntheticFFTRadix2
#guard_msgs (drop info) in #check @table_perturbation_absorbed_by_step_error_closure
#guard_msgs (drop info) in #check @table_perturbation_single_step_bound
#guard_msgs (drop info) in #check @targetPacketMatrix
#guard_msgs (drop info) in #check @test_chunk_split_reconstruct
#guard_msgs (drop info) in #check @test_end_to_end_intmul
#guard_msgs (drop info) in #check @test_multistage_synthetic_fft_radix2
#guard_msgs (drop info) in #check @test_signed_kronecker_negative_poly_mul
#guard_msgs (drop info) in #check @test_synthetic_fft_butterfly_inversion
#guard_msgs (drop info) in #check @test_table1_precision_schedule
#guard_msgs (drop info) in #check @theorem1_pipeline_computes_dft2D
#guard_msgs (drop info) in #check @theorem1_pipeline_eq_step4
#guard_msgs (drop info) in #check @theorem1_twisted_fourier_duality
#guard_msgs (drop info) in #check @theorem2_continuous_poisson_to_dft1DGrid
#guard_msgs (drop info) in #check @theorem2_sincGaussian_dft2D_sub_passband_norm_le
#guard_msgs (drop info) in #check @theorem2_sincGaussian_poisson_to_dft1DGrid
#guard_msgs (drop info) in #check @theorem3_stopband_alias_bound_alphaSchedule
#guard_msgs (drop info) in #check @theorem4_signed_kronecker_polyMul_correct
#guard_msgs (drop info) in #check @theorem4_unpack_pack_signed_kronecker
#guard_msgs (drop info) in #check @theorem5_multiply_bit_complexity_isBigO_n_log_n
#guard_msgs (drop info) in #check @theorem5_multiply_bit_complexity_le_n_log_n
#guard_msgs (drop info) in #check @theorem5_root_pipeline_exact_int_recovery
#guard_msgs (drop info) in #check @theorem5_root_squaring_and_pipeline_error_lt_eight_ulp
#guard_msgs (drop info) in #check @theorem6_radixB_stage_eq_decoupled_MB
#guard_msgs (drop info) in #check @theorem7_1_MB_bitSlice_linearity
#guard_msgs (drop info) in #check @theorem7_1_MB_extremal_witness
#guard_msgs (drop info) in #check @theorem7_1_MB_signed_extremal_witness
#guard_msgs (drop info) in #check @theorem7_1_bitslice_magnitude_expansion
#guard_msgs (drop info) in #check @theorem7_2_floyd_trace_lower_bound
#guard_msgs (drop info) in #check @theorem7_2_validTwoRegStep_potential_diff_le
#guard_msgs (drop info) in #check @theorem7_3_bluestein_chirp_identity
#guard_msgs (drop info) in #check @theorem7_3_exponent_not_shift_invariant
#guard_msgs (drop info) in #check @theorem7_4_tree_spawnedLeaves_ge
#guard_msgs (drop info) in #check @theorem7_4_tree_transform_work_eq
#guard_msgs (drop info) in #check @theorem7_4_tree_zeroPaddedWork_ge
#guard_msgs (drop info) in #check @theorem7_5_admissible_schedule_depth_lower_bound
#guard_msgs (drop info) in #check @theorem7_5_negacyclicShiftIter_exact_order_two_mul_r
#guard_msgs (drop info) in #check @theorem7_6_max_chunk_convolution_peak
#guard_msgs (drop info) in #check @theorem7_6_packed_addition_sensitivity
#guard_msgs (drop info) in #check @theorem7_6_precision_lower_bound_from_dynamic_range
#guard_msgs (drop info) in #check @toComputableExactFastDFTSpec
#guard_msgs (drop info) in #check @toComputableExactFastDFTSpecWithCost
#guard_msgs (drop info) in #check @toScaledComplex_computableBaseRadix2FFTWithProgramCost_eq
#guard_msgs (drop info) in #check @toScaledComplex_computableExactFastDFT_eq
#guard_msgs (drop info) in #check @toScaledComplex_computablePaperFastDFT_eq
#guard_msgs (drop info) in #check @toScaledComplex_computableSyntheticFFTRadix2_eq
#guard_msgs (drop info) in #check @toScaledComplex_gMulScaled_eq_complexQuantize_mul
#guard_msgs (drop info) in #check @tsum_abs_sincGaussian_tails_le
#guard_msgs (drop info) in #check @tsum_int_eq_sum_Icc_add_tails
#guard_msgs (drop info) in #check @tsum_stopbandGHatBox_le
#guard_msgs (drop info) in #check @twistAndSolverStepBitCost
#guard_msgs (drop info) in #check @twistAndSolverStepBitCost_le
#guard_msgs (drop info) in #check @twoTapRowKernel
#guard_msgs (drop info) in #check @two_call_real_conv_recovery
#guard_msgs (drop info) in #check @two_call_square_identity
#guard_msgs (drop info) in #check @unpackSignedKronecker
#guard_msgs (drop info) in #check @unshuffleHeadStep
#guard_msgs (drop info) in #check @unshuffleHeadStep_valid
#guard_msgs (drop info) in #check @unshufflePass
#guard_msgs (drop info) in #check @windowedSincGaussianSpreadArray
#guard_msgs (drop info) in #check @xiPow_r_eq_neg_one
#guard_msgs (drop info) in #check @zHomBwdQuantized
#guard_msgs (drop info) in #check @zHomFwdQuantized
#guard_msgs (drop info) in #check @zPartBwdQuantized
#guard_msgs (drop info) in #check @zPartFwdEffRHS
#guard_msgs (drop info) in #check @zPartFwdQuantized
#guard_msgs (drop info) in #check @zPartNyqEffRHS
#guard_msgs (drop info) in #check @zPartNyqQuantized
#guard_msgs (drop info) in #check @zetaRoot
#guard_msgs (drop info) in #check @zetaRoot_r_eq_neg_one
#guard_msgs (drop info) in #check @AllCallSitesWidthSound
#guard_msgs (drop info) in #check @RecurrenceCallSitesWidthSound
#guard_msgs (drop info) in #check @TableBuilderCallSitesWidthSound
#guard_msgs (drop info) in #check @TablesFaithful
#guard_msgs (drop info) in #check @allCallSitesWidthSound_of_faithful
#guard_msgs (drop info) in #check @buildComputablePaperTablesWithProgramCost
#guard_msgs (drop info) in #check @buildComputablePaperTablesWithProgramCost_faithful
#guard_msgs (drop info) in #check @buildComputablePaperTablesWithProgramCost_snd_le
#guard_msgs (drop info) in #check @computableC0C1WithProgramCost
#guard_msgs (drop info) in #check @computableC0C1WithProgramCost_spec
#guard_msgs (drop info) in #check @computableLog2ScaledWithCost
#guard_msgs (drop info) in #check @computableLog2ScaledWithCost_error_le
#guard_msgs (drop info) in #check @computablePaperFastDFTMultiplyWithTables_snd_le
#guard_msgs (drop info) in #check @computablePaperFastDFTMultiply_faithful_eq_mul
#guard_msgs (drop info) in #check @computablePaperFastDFTWithProgramCost_faithful_snd_le_7000
#guard_msgs (drop info) in #check @computablePaperFastDFT_faithful_error_le
#guard_msgs (drop info) in #check @computablePaperMultiplyOfBitLength
#guard_msgs (drop info) in #check @computablePaperMultiplyOfBitLength_correct_and_isBigO
#guard_msgs (drop info) in #check @computablePaperMultiplyOfBitLength_smoke_test
#guard_msgs (drop info) in #check @computablePiScaledWithCost
#guard_msgs (drop info) in #check @computablePiScaledWithCost_error_le
#guard_msgs (drop info) in #check @computableSincGaussianTapWithProgramCost
#guard_msgs (drop info) in #check @computableSincGaussianTapWithProgramCost_spec
#guard_msgs (drop info) in #check @computableStdCharWithProgramCost
#guard_msgs (drop info) in #check @computableStdCharWithProgramCost_error_le
#guard_msgs (drop info) in #check @computableStepSmokeMultiply
#guard_msgs (drop info) in #check @computableStepSmokeMultiply_correct
#guard_msgs (drop info) in #check @computableStepSmokeMultiply_smoke_test
#guard_msgs (drop info) in #check @computableStepSmokeSpec
#guard_msgs (drop info) in #check @costedNatSqrt
#guard_msgs (drop info) in #check @costedShiftLeftInt
#guard_msgs (drop info) in #check @costedShiftLeftNat
#guard_msgs (drop info) in #check @idealRoundedPaperTables
#guard_msgs (drop info) in #check @norm_baseRadix2FFTOfTwiddles_sub_dft1D_le
#guard_msgs (drop info) in #check @programCost_root_pipeline_widths_sound_of_faithful
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLengthPaperStopSeries
#guard_msgs (drop info) in #check @quantizedMultiplyOfBitLengthPaperStopSeries_snd_le_n_log_n_of_log2_ge_256
#guard_msgs (drop info) in #check @runRecurrenceSeriesCosted
#guard_msgs (drop info) in #check @sincGaussianFastDFTOfTables
#guard_msgs (drop info) in #check @sincGaussianFastDFTOfTables_error_le
#guard_msgs (drop info) in #check @tableBuilderWithProgramCost_snd_le
#guard_msgs (drop info) in #check @tableBuilder_widths_sound
#guard_msgs (drop info) in #check @toScaledComplex
#guard_msgs (drop info) in #check @toScaledComplex_computablePaperFastDFT_eq_ofTables
#guard_msgs (drop info) in #check @dft2D_norm_le
#guard_msgs (drop info) in #check @effectiveFilterWidth_le_r
#guard_msgs (drop info) in #check @kroneckerBitStride_le_six_mul_of_bounds
#guard_msgs (drop info) in #check @lemma2_precision_schedule_closure
#guard_msgs (drop info) in #check @lemma2_windowed_sincGaussian_concrete_closure
#guard_msgs (drop info) in #check @norm_complexQuantize_sub_le
#guard_msgs (drop info) in #check @norm_syntheticDFT_le
#guard_msgs (drop info) in #check @norm_syntheticFFTRadix2Quantized_le
#guard_msgs (drop info) in #check @overlapAdd_folded_polyMulInt_eq
#guard_msgs (drop info) in #check @sincGaussianFastDFTStep_error_le
#guard_msgs (drop info) in #check @xiPow_r_eq_neg_one
#guard_msgs (drop info) in #check @zetaRoot_r_eq_neg_one
#guard_msgs (drop info) in #check @BitCostM.tick
#guard_msgs (drop info) in #check @BitCostM.ofFnM
#guard_msgs (drop info) in #check @BitCostM.mapListM
#guard_msgs (drop info) in #check @computableNegacyclicDirectWithCost
#guard_msgs (drop info) in #check @sumRangePairWithCost
#guard_msgs (drop info) in #check @costedGNyqAltSumScale
#guard_msgs (drop info) in #check @accumBucketIntWithCost
#guard_msgs (drop info) in #check @accumBucketsRangeWithCost
#guard_msgs (drop info) in #check @overlapAddBucketsSinglePassAuxWithCost
#guard_msgs (drop info) in #check @costedPackSignedLeaf
#guard_msgs (drop info) in #check @costedCombineSignedPack
#guard_msgs (drop info) in #check @costedUnpackSignedSlot
#guard_msgs (drop info) in #check @costedSplitSignedPower
#guard_msgs (drop info) in #check @costedMulInt
#guard_msgs (drop info) in #check @packSignedKroneckerTreeAuxWithCost
#guard_msgs (drop info) in #check @packSignedKroneckerTreeWithCost
#guard_msgs (drop info) in #check @unpackSignedKroneckerTreeAuxWithCost
#guard_msgs (drop info) in #check @unpackSignedKroneckerTreeWithCost
#guard_msgs (drop info) in #check @polyMulKroneckerSignedTreeWithCost
#guard_msgs (drop info) in #check @polyMulKroneckerSignedTreeWithCost_fst
#guard_msgs (drop info) in #check @polyMulKroneckerSignedTreeWithCost_snd_le
#guard_msgs (drop info) in #check @computableSpreadRowContiguousWithProgramCost_snd_le
#guard_msgs (drop info) in #check @splitChunksTreeWithProgramCost_snd_le
#guard_msgs (drop info) in #check @reconstructChunksTreeWithProgramCost_snd_le
#guard_msgs (drop info) in #check @size_mul_log2_add_one_mul_addBitCost_le_intrinsicCostRadix2Leaf
#guard_msgs (drop info) in #check @computablePaperStopStepRowSpread
#guard_msgs (drop info) in #check @computablePaperStopStepRowSmoke
#guard_msgs (drop info) in #check @computablePaperStopStepRowSmoke_expected_eq
#guard_msgs (drop info) in #check @computablePaperStopStepRow1CenterTap
#guard_msgs (drop info) in #check @computablePaperStopStepRow1CenterTap_spec
#guard_msgs (drop info) in #check @buildQuantizedSpecPaperStop_one_eight_nine_eq_step
#guard_msgs (drop info) in #check @costedGAltTerm
#guard_msgs (drop info) in #check @costedZHomInit
#guard_msgs (drop info) in #check @costedAddCarrySignedPower
#guard_msgs (drop info) in #check @costedSplitChunkLeaf
#guard_msgs (drop info) in #check @costedSplitChunkStep
#guard_msgs (drop info) in #check @costedReconstructChunkLeaf
#guard_msgs (drop info) in #check @costedReconstructChunkStep
#guard_msgs (drop info) in #check @overlapAddBucketIdx
#guard_msgs (drop info) in #check @instZeroIntElementary
#guard_msgs (drop info) in #check @natTreeFuel
#guard_msgs (drop info) in #check @natTreeLeftHalf
#guard_msgs (drop info) in #check @natTreeRightHalf
#guard_msgs (drop info) in #check @computableStepSmokeAllPairsExact
#guard_msgs (drop info) in #check @computablePaperMultiplyOfBitLength_paperStop_step_exact
#guard_msgs (drop info) in #check @costedNegInt0
#guard_msgs (drop info) in #check @costedCondNegInt0
#guard_msgs (drop info) in #check @costedSymmClampPow2Int
#guard_msgs (drop info) in #check @costedAddShiftLeftInt
#guard_msgs (drop info) in #check @costedSubShiftLeftInt
#guard_msgs (drop info) in #check @costedSubNatToInt0
#guard_msgs (drop info) in #check @costedSubNatAbsInt0
#guard_msgs (drop info) in #check @costedFoldRawTapRow
#guard_msgs (drop info) in #check @costedPackRootChunkPair
#guard_msgs (drop info) in #check @costedExtractRootSlot
end G3DocChecks

/-!
# Mechanical Cost-Monad Kernel `Expr` Soundness Linter

This compile-time metaprogram inspects the Lean kernel `Environment` (`Expr` DAG) to enforce five
syntactic cost-soundness invariants across the executable pipeline (together with compile-time
negative `#guard_msgs` self-tests confirming that violations are rejected):
1. **No Raw `(v, c)` Pair Forgery in Audited `BitCostM` Bodies (`hasForgedBitCostPairBody`)**:
   Walks the kernel `Expr` body (including all `.match_*` and `._unary` compiler auxiliaries) of all
   26 non-primitive `BitCostM` algorithm subroutines (`costMonadAlgorithmDefs`) and verifies that
   none of them directly constructs a `(v, c)` cost pair via `@Prod.mk _ Nat`; every `BitCostM`
   value must be constructed via `Pure.pure`, `Bind.bind`, `BitCostM.tick`, `BitCostM.ofFnM`,
   `BitCostM.mapListM`, or a sealed primitive in `sealedCostPrimitives`.
2. **Type-Directed `ℤ`-Carrier Operator Check + Strict `Int.*` and `IntMul.*` Whitelist**:
   Walks every application node in the `Expr` body of all 26 `costMonadAlgorithmDefs` via
   `findUncostedCarrierOpBody ``Int` and rejects any arithmetic or shift operator (`HAdd.hAdd`,
   `Add.add`, `HSub.hSub`, `Sub.sub`, `HMul.hMul`, `Mul.mul`, `HDiv.hDiv`, `Div.div`, `HMod.hMod`,
   `Mod.mod`, `HPow.hPow`, `Pow.pow`, `Monoid.toNatPow`, `Neg.neg`, `HShiftLeft.hShiftLeft`,
   `ShiftLeft.shiftLeft`, `HShiftRight.hShiftRight`, `ShiftRight.shiftRight`) whose carrier type
   is `Int` (`ℤ`), **regardless of which typeclass instance is used** (e.g. `Int.instAdd` or
   Mathlib's `Int.instNormedCommRing`). Also enforces a verified constant blacklist and a strict
   whitelist on `Int.*` constants (`[ ``Int, ``Int.ofNat, ``Int.instOfNat ]` only) and `IntMul.*`
   constants.
3. **Type-Directed `ℕ`-Carrier Operator Check in All 8 Divide-and-Conquer Tree Definitions (`costMonadTreeDefs`)**:
   Verifies via `findUncostedCarrierOpBody ``Nat` that all 8 divide-and-conquer binary-tree
   definitions (`packSignedKroneckerTreeAuxWithCost`, `packSignedKroneckerTreeWithCost`,
   `unpackSignedKroneckerTreeAuxWithCost`, `unpackSignedKroneckerTreeWithCost`,
   `splitChunksTreeAuxWithCost`, `splitChunksTreeWithProgramCost`,
   `reconstructChunksTreeAuxWithCost`, `reconstructChunksTreeWithProgramCost`) contain zero
   `Nat`-carrier arithmetic or shift operators (`+`, `-`, `*`, `/`, `%`, `^`, `<<<`, `>>>`),
   routing all $O(\log n)$-bit tree-recursion index halving through `natTreeFuel`,
   `natTreeLeftHalf`, and `natTreeRightHalf` and all multi-word shifts/masks through bit-shift
   (`<<<`, `>>>`) sealed primitives.
4. **Error on Fuel Exhaustion & Proof-Term Skipping (`collectBodyConstants`, `collectConeConstants`)**:
   Throws a compile-time error if recursion fuel is ever exhausted, and skips `.thmInfo`/`.axiomInfo`
   proof terms when walking the executable dependency cone.
5. **Transitive Headline Dependency-Cone Audit & Full Program-Costed Headline Module Classification (`computablePaperMultiplyOfBitLength`, corresponding to an earlier `[MS]` draft's executable specification, omitted in the current `[MS]`)**:
   Walks the transitive executable `IntMul.*` dependency cone of `computablePaperMultiplyOfBitLength`
   (stopping at `sealedCostPrimitives`), verifies that no uncosted algorithm function is reachable,
   and checks that every reachable declaration across all five program-costed headline modules
   (`ProgramCostPrimitives`, `PaperHeadlinePipeline`, `ComputableTranscendentals`,
   `ComputableTableBuilder`, and `CallSiteWidthSoundness`) is explicitly classified.
-/
section CostMonadKernelLinter

open Lean Elab Command

private def typeDirectedCarrierOps : List Lean.Name :=
  [ ``HAdd.hAdd, ``Add.add,
    ``HSub.hSub, ``Sub.sub,
    ``HMul.hMul, ``Mul.mul,
    ``HDiv.hDiv, ``Div.div,
    ``HMod.hMod, ``Mod.mod,
    ``HPow.hPow, ``Pow.pow, ``NPow.toPow,
    ``Neg.neg,
    ``HShiftLeft.hShiftLeft, ``ShiftLeft.shiftLeft,
    ``HShiftRight.hShiftRight, ``ShiftRight.shiftRight ]

private def findUncostedCarrierOpExpr (carrier : Lean.Name) : Lean.Expr → Option Lean.Name
  | e@(.app f a) =>
    let hit : Option Lean.Name :=
      match e.getAppFn with
      | .const opName _ =>
        if typeDirectedCarrierOps.contains opName &&
           (e.getAppArgs.toList.take 3).any (fun arg => arg.isConstOf carrier) then
          some opName
        else
          none
      | _ => none
    hit.orElse (fun _ =>
      (findUncostedCarrierOpExpr carrier f).orElse (fun _ =>
        findUncostedCarrierOpExpr carrier a))
  | .lam _ t b _ =>
    (findUncostedCarrierOpExpr carrier t).orElse (fun _ =>
      findUncostedCarrierOpExpr carrier b)
  | .forallE _ t b _ =>
    (findUncostedCarrierOpExpr carrier t).orElse (fun _ =>
      findUncostedCarrierOpExpr carrier b)
  | .letE _ t v b _ =>
    (findUncostedCarrierOpExpr carrier t).orElse (fun _ =>
      (findUncostedCarrierOpExpr carrier v).orElse (fun _ =>
        findUncostedCarrierOpExpr carrier b))
  | .mdata _ e => findUncostedCarrierOpExpr carrier e
  | .proj _ _ e => findUncostedCarrierOpExpr carrier e
  | _ => none

private def collectPayloadConstantsExpr : Lean.Expr → List Lean.Name
  | .const n _ => [n]
  | .app f a => collectPayloadConstantsExpr f ++ collectPayloadConstantsExpr a
  | .lam _ t b _ => collectPayloadConstantsExpr t ++ collectPayloadConstantsExpr b
  | .forallE _ t b _ => collectPayloadConstantsExpr t ++ collectPayloadConstantsExpr b
  | .letE _ t v b _ =>
      collectPayloadConstantsExpr t ++ collectPayloadConstantsExpr v ++ collectPayloadConstantsExpr b
  | .mdata _ e => collectPayloadConstantsExpr e
  | .proj _ _ e => collectPayloadConstantsExpr e
  | _ => []

private def hasForgedBitCostPairExpr : Lean.Expr → Bool
  | e@(.app f a) =>
    let isProdMkNat :=
      e.getAppFn.isConstOf ``Prod.mk &&
      e.getAppArgs.size ≥ 2 &&
      (e.getAppArgs[1]!.isConstOf ``Nat || e.getAppArgs[1]!.isConstOf ``IntMul.BitCostM)
    isProdMkNat || hasForgedBitCostPairExpr f || hasForgedBitCostPairExpr a
  | .lam _ t b _ => hasForgedBitCostPairExpr t || hasForgedBitCostPairExpr b
  | .forallE _ t b _ => hasForgedBitCostPairExpr t || hasForgedBitCostPairExpr b
  | .letE _ t v b _ =>
      hasForgedBitCostPairExpr t || hasForgedBitCostPairExpr v || hasForgedBitCostPairExpr b
  | .mdata _ e => hasForgedBitCostPairExpr e
  | .proj _ _ e => hasForgedBitCostPairExpr e
  | _ => false

private def isCompilerAuxOf (root c : Lean.Name) : Bool :=
  c != root &&
  (root.isPrefixOf c ||
   ((`IntMul).isPrefixOf c &&
    (match c with
     | .str _ s => s.startsWith "match_" || s == "_unary" || s == "_mutual"
     | _ => false)))

private def findUncostedCarrierOpBody (carrier : Lean.Name) (env : Lean.Environment) :
    ℕ → Lean.Name → Lean.Name → Except String (Option Lean.Name)
  | 0, root, curr => .error s!"CostMonadLinter: findUncostedCarrierOpBody fuel exhausted at {curr} (root {root})"
  | fuel + 1, root, curr =>
    match env.find? curr >>= (·.value?) with
    | none => .ok none
    | some val => do
      match findUncostedCarrierOpExpr carrier val with
      | some op => return some op
      | none =>
        let direct := collectPayloadConstantsExpr val
        direct.foldlM (fun acc c => do
          match acc with
          | some op => return some op
          | none =>
            if isCompilerAuxOf root c && c != curr then
              findUncostedCarrierOpBody carrier env fuel root c
            else
              return none) none

private def collectBodyConstants (env : Lean.Environment) :
    ℕ → Lean.Name → Lean.Name → Except String (List Lean.Name)
  | 0, root, curr => .error s!"CostMonadLinter: collectBodyConstants fuel exhausted at {curr} (root {root})"
  | fuel + 1, root, curr =>
    match env.find? curr >>= (·.value?) with
    | none => .ok []
    | some val => do
      let direct := collectPayloadConstantsExpr val
      direct.foldlM (fun acc c => do
        if isCompilerAuxOf root c && c != curr then
          let sub ← collectBodyConstants env fuel root c
          pure (acc ++ sub)
        else
          pure acc) direct

private def hasForgedBitCostPairBody (env : Lean.Environment) :
    ℕ → Lean.Name → Lean.Name → Except String Bool
  | 0, root, curr => .error s!"CostMonadLinter: hasForgedBitCostPairBody fuel exhausted at {curr} (root {root})"
  | fuel + 1, root, curr =>
    match env.find? curr >>= (·.value?) with
    | none => .ok false
    | some val => do
      if hasForgedBitCostPairExpr val then
        return true
      let direct := collectPayloadConstantsExpr val
      direct.foldlM (fun acc c => do
        if acc then
          return true
        else if isCompilerAuxOf root c && c != curr then
          hasForgedBitCostPairBody env fuel root c
        else
          return false) false

private def collectConeConstants (env : Lean.Environment)
    (sealed : List Lean.Name) :
    ℕ → List Lean.Name → List Lean.Name → Except String (List Lean.Name)
  | _, [], visited => .ok visited
  | 0, curr :: _, _ => .error s!"CostMonadLinter: collectConeConstants fuel exhausted at {curr}"
  | fuel + 1, curr :: worklist, visited =>
    if visited.contains curr || sealed.contains curr then
      collectConeConstants env sealed fuel worklist visited
    else
      let visited' := curr :: visited
      match env.find? curr with
      | none => collectConeConstants env sealed fuel worklist visited'
      | some (.thmInfo _) => collectConeConstants env sealed fuel worklist visited'
      | some (.axiomInfo _) => collectConeConstants env sealed fuel worklist visited'
      | some cinfo =>
        match cinfo.value? with
        | none => collectConeConstants env sealed fuel worklist visited'
        | some val =>
          let children := val.getUsedConstants.toList.filter (fun c =>
            (`IntMul).isPrefixOf c && !visited'.contains c && !sealed.contains c)
          collectConeConstants env sealed fuel (children ++ worklist) visited'

private def sealedCostPrimitives : List Lean.Name :=
  [ `IntMul.costedAddInt, `IntMul.costedSubInt, `IntMul.costedMulInt,
    `IntMul.costedDivRoundRatInt, `IntMul.costedGAdd, `IntMul.costedGSub,
    `IntMul.costedGAltTerm, `IntMul.costedZHomInit,
    `IntMul.costedGMulScaled, `IntMul.costedGRescale, `IntMul.costedGPreTwistU,
    `IntMul.costedGRatioQuantize, `IntMul.costedGCombineQuantize,
    `IntMul.costedGNyqStepQuantize, `IntMul.costedGNyqAltSumScale,
    `IntMul.costedGQuantizeCoordToScale, `IntMul.costedGQuantizeRat,
    `IntMul.costedButterflyAvg, `IntMul.costedPackSignedLeaf,
    `IntMul.costedCombineSignedPack, `IntMul.costedUnpackSignedSlot,
    `IntMul.costedSplitSignedPower, `IntMul.costedAddCarrySignedPower,
    `IntMul.costedSplitChunkLeaf, `IntMul.costedSplitChunkStep,
    `IntMul.costedReconstructChunkLeaf, `IntMul.costedReconstructChunkStep,
    `IntMul.accumBucketIntWithCost, `IntMul.computableNegacyclicDirectWithCost,
    `IntMul.costedNatSqrt, `IntMul.costedClampInt,
    `IntMul.costedShiftLeftNat, `IntMul.costedShiftLeftInt,
    `IntMul.costedNegInt0, `IntMul.costedCondNegInt0,
    `IntMul.costedSymmClampPow2Int, `IntMul.costedAddShiftLeftInt,
    `IntMul.costedSubShiftLeftInt, `IntMul.costedSubNatToInt0,
    `IntMul.costedSubNatAbsInt0, `IntMul.costedFoldRawTapRow,
    `IntMul.costedPackRootChunkPair, `IntMul.costedExtractRootSlot,
    `IntMul.recurrenceStepCosted ]

private def costMonadCombinators : List Lean.Name :=
  [ `IntMul.BitCostM.tick, `IntMul.BitCostM.ofFnM, `IntMul.BitCostM.mapListM,
    `IntMul.runSequentialScanCostedSteps, `IntMul.runScan2DCostedWithSteps ]

private def allowedPureHelpersInCostMonadDefs : List Lean.Name :=
  [ `IntMul.BitCostM, `IntMul.instPureBitCostM, `IntMul.instBindBitCostM, `IntMul.instMonadBitCostM,
    `IntMul.instZeroIntElementary,
    `IntMul.addBitCost, `IntMul.read1D, `IntMul.effectiveFilterWidth,
    `IntMul.kroneckerSpreadNumBlocks, `IntMul.computableKroneckerBitStride,
    `IntMul.overlapAddBucketIdx, `IntMul.natLog2Fuel,
    `IntMul.natTreeFuel, `IntMul.natTreeLeftHalf, `IntMul.natTreeRightHalf,
    `IntMul.runBwdRevSteps, `IntMul.runReverseSteps,
    `IntMul.MultiTapeScanState,
    `IntMul.MultiTapeScanState.outTape, `IntMul.MultiTapeScanState.steps ]

private def allowedIntConstsInCostMonadDefs : List Lean.Name :=
  [ `Int, `Int.ofNat, `Int.instOfNat ]

private def allowedIntConstsInHeadlineDefs : List Lean.Name :=
  [ `Int, `Int.ofNat, `Int.instOfNat, `Int.toNat,
    `Int.instLEInt, `Int.decLe, `Int.instMin ]

private def costMonadAlgorithmDefs : List Lean.Name :=
  [ `IntMul.sumRangePairWithCost,
    `IntMul.accumBucketsRangeWithCost,
    `IntMul.overlapAddBucketsSinglePassAuxWithCost,
    `IntMul.overlapAddBucketsSinglePassWithCost,
    `IntMul.packSignedKroneckerTreeAuxWithCost,
    `IntMul.packSignedKroneckerTreeWithCost,
    `IntMul.unpackSignedKroneckerTreeAuxWithCost,
    `IntMul.unpackSignedKroneckerTreeWithCost,
    `IntMul.polyMulKroneckerSignedTreeWithCost,
    `IntMul.computableSyntheticFFTRadix2WithProgramCost,
    `IntMul.buildComputableZPartFwdWithProgramCost,
    `IntMul.buildComputableZHomFwdWithProgramCost,
    `IntMul.buildComputableZPartNyqWithProgramCost,
    `IntMul.computableSolveBidiagonalFwdWithProgramCost,
    `IntMul.computableSolveNyquistWithProgramCost,
    `IntMul.computableSolveBidiagonalBwdWithProgramCost,
    `IntMul.computableNyquistAltSumContiguousWithProgramCost,
    `IntMul.computableSpreadRowBlockReContiguousWithCost,
    `IntMul.computableSpreadRowBlockImContiguousWithCost,
    `IntMul.computableSpreadRowContiguousWithProgramCost,
    `IntMul.splitChunksTreeAuxWithCost,
    `IntMul.splitChunksTreeWithProgramCost,
    `IntMul.reconstructChunksTreeAuxWithCost,
    `IntMul.reconstructChunksTreeWithProgramCost,
    `IntMul.computableBaseRadix2FFTCoreWithProgramCost,
    `IntMul.computableBaseRadix2FFTWithProgramCost ]

private def costMonadTreeDefs : List Lean.Name :=
  [ `IntMul.packSignedKroneckerTreeAuxWithCost,
    `IntMul.packSignedKroneckerTreeWithCost,
    `IntMul.unpackSignedKroneckerTreeAuxWithCost,
    `IntMul.unpackSignedKroneckerTreeWithCost,
    `IntMul.splitChunksTreeAuxWithCost,
    `IntMul.splitChunksTreeWithProgramCost,
    `IntMul.reconstructChunksTreeAuxWithCost,
    `IntMul.reconstructChunksTreeWithProgramCost ]

private def classifiedHeadlinePipelineDefs : List Lean.Name :=
  [ `IntMul.computablePaperMultiplyOfBitLength,
    `IntMul.computablePaperMultiplyOfBitLengthGivenSpecWithProgramCost,
    `IntMul.computablePaperFastDFTWithProgramCost,
    `IntMul.computablePaperFastDFTMultiplyWithProgramCost,
    `IntMul.buildComputablePaperTablesWithProgramCost,
    `IntMul.computableSincGaussianTapGivenPiLog2,
    `IntMul.runRecurrenceSeriesCosted,
    `IntMul.sqrtTwoAddIntIter,
    `IntMul.computablePiScaledCore,
    `IntMul.computablePiScaledWithCost,
    `IntMul.computableLog2ScaledWithCost,
    `IntMul.computableStdCharCore,
    `IntMul.computableStdCharWithProgramCost,
    `IntMul.computableSincRationalClamp,
    `IntMul.computableExpNegRationalClamp,
    `IntMul.computableSincGaussianTapInner,
    `IntMul.computableSincGaussianTapCore,
    `IntMul.computableSincGaussianTapWithProgramCost,
    `IntMul.computableHalfErfScaledInner,
    `IntMul.computableC0C1Inner,
    `IntMul.computableC0C1Core,
    `IntMul.computableC0C1WithProgramCost ]

private def classifiedHeadlinePipelineAndTableDefs : List Lean.Name :=
  `IntMul.ComputablePaperFastDFTSpec :: classifiedHeadlinePipelineDefs

private def forbiddenInCostMonadDefs : List Lean.Name :=
  [ `Int.add, `Int.sub, `Int.mul, `Int.ediv, `Int.emod, `Int.tdiv, `Int.tmod,
    `Int.fdiv, `Int.fmod, `Int.neg, `Int.pow, `Int.shiftLeft, `Int.shiftRight,
    `Int.instAdd, `Int.instSub, `Int.instMul, `Int.instDiv, `Int.instMod,
    `Int.instNegInt, `Int.instNatPow, `Int.instMonoid, `Int.instNormedCommRing,
    `Neg.neg, `HShiftLeft.hShiftLeft, `HShiftRight.hShiftRight,
    `Nat.shiftLeft, `Nat.shiftRight,
    `Finset.sum, `List.map, `List.foldl, `List.foldr, `List.sum,
    `Array.map, `Array.foldl, `Array.foldr,
    `IntMul.gAdd, `IntMul.gSub, `IntMul.gNeg, `IntMul.gAltTerm,
    `IntMul.gMulScaled, `IntMul.gRescale, `IntMul.gPreTwistU, `IntMul.gQuantizeRat,
    `IntMul.gQuantizeCoordToScale, `IntMul.gRatioQuantize, `IntMul.gCombineQuantize,
    `IntMul.gNyqStepQuantize, `IntMul.divRoundPow2, `IntMul.divRoundRatInt,
    `IntMul.accumBucketInt, `IntMul.extractSignedSlot, `IntMul.shiftSignedSlot,
    `IntMul.shiftSignedSlotIter,
    `IntMul.polyMulKroneckerSignedComputable, `IntMul.polyMulKroneckerSignedH,
    `IntMul.polyMulKroneckerSigned, `IntMul.packSignedKronecker, `IntMul.unpackSignedKronecker,
    `IntMul.computableNegacyclicDirect, `IntMul.overlapAddBucketsSinglePass,
    `IntMul.sumRangePair, `IntMul.sumRangeInt,
    `IntMul.splitChunks, `IntMul.evalRadix,
    `IntMul.splitChunksTree, `IntMul.splitChunksTreeAux,
    `IntMul.reconstructChunksTree, `IntMul.reconstructChunksTreeAux ]

private def forbiddenInTreeDefs : List Lean.Name :=
  [ `Nat.add, `Nat.sub, `Nat.mul, `Nat.div, `Nat.mod, `Nat.pow,
    `Nat.shiftLeft, `Nat.shiftRight ]

private def forbiddenUncostedInHeadlineCone : List Lean.Name :=
  [ `IntMul.polyMulKroneckerSignedComputable, `IntMul.polyMulKroneckerSignedH,
    `IntMul.polyMulKroneckerSigned, `IntMul.packSignedKronecker, `IntMul.unpackSignedKronecker,
    `IntMul.computableNegacyclicDirect, `IntMul.overlapAddBucketsSinglePass,
    `IntMul.sumRangePair, `IntMul.splitChunksTree, `IntMul.reconstructChunksTree,
    `IntMul.computableSpreadRowContiguous, `IntMul.computableSpreadRowContiguousWithCost,
    `IntMul.computableSyntheticFFTRadix2, `IntMul.computableSyntheticFFTRadix2WithCost,
    `IntMul.computableSolveBidiagonalFwdExact, `IntMul.computableSolveNyquistExact,
    `IntMul.computableSolveBidiagonalBwdExact, `IntMul.computableBaseDFTExact,
    `IntMul.computableExactFastDFT, `IntMul.idealRoundedPaperTables ]

private def auditCostMonadDef (env : Lean.Environment) (decl : Lean.Name)
    (forbidNatCarrierOps : Bool := false) : Except String Unit := do
  if (env.find? decl).isNone then
    throw s!"CostMonadLinter: missing declaration {decl}"
  let forged ← hasForgedBitCostPairBody env 32 decl decl
  if forged then
    throw s!"CostMonadLinter: {decl} constructs a raw (val, cost) pair via Prod.mk _ Nat"
  let intCarrierOp ← findUncostedCarrierOpBody ``Int env 32 decl decl
  if let some op := intCarrierOp then
    throw s!"CostMonadLinter: {decl} contains uncosted Int-carrier operator {op}"
  if forbidNatCarrierOps then
    let natCarrierOp ← findUncostedCarrierOpBody ``Nat env 32 decl decl
    if let some op := natCarrierOp then
      throw s!"CostMonadLinter: tree helper {decl} contains uncosted Nat-carrier operator {op}"
  let used ← collectBodyConstants env 32 decl decl
  for bad in forbiddenInCostMonadDefs do
    if used.contains bad then
      throw s!"CostMonadLinter: {decl} contains forbidden uncosted constant {bad}"
  if forbidNatCarrierOps then
    for bad in forbiddenInTreeDefs do
      if used.contains bad then
        throw s!"CostMonadLinter: tree helper {decl} contains forbidden arithmetic constant {bad}"
  for c in used do
    if (`Int).isPrefixOf c && !allowedIntConstsInCostMonadDefs.contains c then
      throw s!"CostMonadLinter: {decl} contains non-whitelisted Int constant {c}"
    if (`IntMul).isPrefixOf c &&
       c != decl && !isCompilerAuxOf decl c &&
       !costMonadAlgorithmDefs.contains c &&
       !sealedCostPrimitives.contains c &&
       !costMonadCombinators.contains c &&
       !allowedPureHelpersInCostMonadDefs.contains c then
      throw s!"CostMonadLinter: {decl} contains non-whitelisted IntMul constant {c}"

private def auditHeadlinePipelineDef (env : Lean.Environment) (decl : Lean.Name) :
    Except String Unit := do
  if (env.find? decl).isNone then
    throw s!"CostMonadLinter: missing headline declaration {decl}"
  let intCarrierOp ← findUncostedCarrierOpBody ``Int env 32 decl decl
  if let some op := intCarrierOp then
    throw s!"CostMonadLinter: headline definition {decl} contains uncosted Int-carrier operator {op}"
  let used ← collectBodyConstants env 32 decl decl
  for c in used do
    if (`Int).isPrefixOf c && !allowedIntConstsInHeadlineDefs.contains c then
      throw s!"CostMonadLinter: headline definition {decl} contains non-whitelisted Int constant {c}"
    if forbiddenUncostedInHeadlineCone.contains c then
      throw s!"CostMonadLinter: headline definition {decl} contains forbidden uncosted constant {c}"

run_cmd do
  let env ← getEnv
  for bad in typeDirectedCarrierOps ++ forbiddenInCostMonadDefs ++ forbiddenInTreeDefs ++
      forbiddenUncostedInHeadlineCone ++ classifiedHeadlinePipelineAndTableDefs do
    if (env.find? bad).isNone then
      throwError s!"CostMonadLinter: configured constant {bad} does not exist in Environment"
  for decl in costMonadAlgorithmDefs do
    let isTree := costMonadTreeDefs.contains decl
    match auditCostMonadDef env decl isTree with
    | .ok () => pure ()
    | .error msg => throwError msg
  for decl in classifiedHeadlinePipelineDefs do
    match auditHeadlinePipelineDef env decl with
    | .ok () => pure ()
    | .error msg => throwError msg
  let cone ← match collectConeConstants env sealedCostPrimitives 4096
      [`IntMul.computablePaperMultiplyOfBitLength] [] with
    | .ok c => pure c
    | .error msg => throwError msg
  for bad in forbiddenUncostedInHeadlineCone do
    if cone.contains bad then
      throwError s!"CostMonadLinter: headline dependency cone reaches uncosted function {bad}"
  let primModIdx := env.getModuleIdxFor? `IntMul.BitCostM
  let pipeModIdx := env.getModuleIdxFor? `IntMul.ComputablePaperFastDFTSpec
  let transModIdx := env.getModuleIdxFor? `IntMul.runRecurrenceSeriesCosted
  let tableModIdx := env.getModuleIdxFor? `IntMul.buildComputablePaperTablesWithProgramCost
  let headlineModIdx := env.getModuleIdxFor? `IntMul.computablePaperMultiplyOfBitLength
  let allClassifiedIn10_16_4 :=
    costMonadAlgorithmDefs ++ sealedCostPrimitives ++ costMonadCombinators ++
    allowedPureHelpersInCostMonadDefs ++ classifiedHeadlinePipelineAndTableDefs
  for c in cone do
    let modIdx := env.getModuleIdxFor? c
    if modIdx == primModIdx || modIdx == pipeModIdx || modIdx == transModIdx ||
       modIdx == tableModIdx || modIdx == headlineModIdx then
      if !isCompilerAuxOf c c &&
         !allClassifiedIn10_16_4.any (fun d => d == c || d.isPrefixOf c) then
        throwError s!"CostMonadLinter: unclassified Section 10.16.4 declaration {c} in headline cone"

-- Negative compile-time self-tests for `CostMonadKernelLinter`:
private def badCostMonadNeg (x : ℤ) : BitCostM ℤ := pure (-x)
private def badCostMonadPow (x : ℤ) (k : ℕ) : BitCostM ℤ := pure (x ^ k)
private def badCostMonadTreeNatMul (a b : ℕ) : BitCostM ℕ := pure (a * b)
private def badCostMonadToNatMul (a b : ℤ) : BitCostM ℕ := pure (a * b).toNat
private def badCostMonadForgedPair (x : ℤ) : BitCostM ℤ := (x, 0)
private def badCostMonadRingAdd (x y : ℤ) : BitCostM ℤ :=
  pure (@HAdd.hAdd ℤ ℤ ℤ (@instHAdd ℤ Int.instNormedCommRing.toDistrib.toAdd) x y)

/--
info: CostMonadLinter: _private.IntMul.0.IntMul.badCostMonadNeg contains uncosted Int-carrier operator Neg.neg
---
info: CostMonadLinter: _private.IntMul.0.IntMul.badCostMonadPow contains uncosted Int-carrier operator HPow.hPow
---
info: CostMonadLinter: tree helper _private.IntMul.0.IntMul.badCostMonadTreeNatMul contains uncosted Nat-carrier operator HMul.hMul
---
info: CostMonadLinter: _private.IntMul.0.IntMul.badCostMonadToNatMul contains uncosted Int-carrier operator HMul.hMul
---
info: CostMonadLinter: _private.IntMul.0.IntMul.badCostMonadForgedPair constructs a raw (val, cost) pair via Prod.mk _ Nat
---
info: CostMonadLinter: _private.IntMul.0.IntMul.badCostMonadRingAdd contains uncosted Int-carrier operator HAdd.hAdd
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  for (decl, isTree) in [
    (``badCostMonadNeg, false),
    (``badCostMonadPow, false),
    (``badCostMonadTreeNatMul, true),
    (``badCostMonadToNatMul, false),
    (``badCostMonadForgedPair, false),
    (``badCostMonadRingAdd, false)
  ] do
    match auditCostMonadDef env decl isTree with
    | .ok () => throwError s!"CostMonadLinter self-test failed: {decl} was unexpectedly accepted!"
    | .error msg => logInfo msg

end CostMonadKernelLinter

end IntMul
