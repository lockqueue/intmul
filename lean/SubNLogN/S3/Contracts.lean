import SubNLogN.S3.Walsh
import SubNLogN.S3.PositionalPerm
import SubNLogN.S3.DirectFFT

/-!
# Component S3 (`Contracts.lean`): Assembly of `Headline_S3_WalshAndDirectFFT`
-/

namespace SubNLogN.S3

open SubNLogN

/-- Proof of `Headline_S3_WalshAndDirectFFT` from `S3/Walsh`, `S3/PositionalPerm`, and `S3/DirectFFT`. -/
theorem headline_S3_holds : Headline_S3_WalshAndDirectFFT :=
  ⟨twoH0_cube_eq,
   twoH0_phaseS_cube_eq,
   twoH0_phaseCZ_false,
   twoH0_phaseCZ_true,
   xor_swap_three_stage_correct,
   cycle_two_involutions⟩

end SubNLogN.S3
