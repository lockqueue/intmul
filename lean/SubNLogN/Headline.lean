import SubNLogN.Spec
import SubNLogN.S1.Contracts
import SubNLogN.S2.Contracts
import SubNLogN.S3.Contracts
import SubNLogN.S4.Contracts
import SubNLogN.S5.Contracts

/-!
# Headline Theorems: Unconditional Sub-`n log n` Integer Multiplication on a `TM2` Turing Machine

This module proves every headline theorem of `SubNLogN/Spec.lean` from the component contract
modules `SubNLogN.S1.Contracts`–`SubNLogN.S5.Contracts` (Section 8, `sec:lean`), with zero `sorry`
in this file and with literal `Spec` types (names `S1`–`S5` are kept for identifier stability).
-/

namespace SubNLogN

/-- **Main Headline (`κ = 2^{-46}`):** Unconditional sub-`n log n` integer multiplication on `TM2`
in time `O(L · (log₂ L)^{1 - 2^{-46}})` (`C₁ = 14` Walsh route; Theorem 1 (`thm:main`), Theorem 2 (`thm:lean`)). -/
theorem intMul_TM2_sub_nlogn : IntMulSubNLogN :=
  S5.headline_TM2_subNLogN_46

/-- **Headline 1 (`κ = 2^{-46}`):** Alias with explicit `Headline_TM2_SubNLogN_46` type (Theorem 2, `thm:lean`). -/
theorem intMul_TM2_sub_nlogn_46 : Headline_TM2_SubNLogN_46 :=
  S5.headline_TM2_subNLogN_46

/-- **Headline 2 (`κ = 2^{-47}`):** Unconditional sub-`n log n` integer multiplication on `TM2`
in time `O(L · (log₂ L)^{1 - 2^{-47}})` (deduced from `κ = 2^{-46}` by exponent monotonicity; `C₁ = 20` row slack in `S5/Schedule.lean`, Remark 7.3 (`rem:printed-optimal`), Table 10 (`tab:all-rows`)). -/
theorem intMul_TM2_sub_nlogn_47 : Headline_TM2_SubNLogN_47 :=
  S5.headline_TM2_subNLogN_47

/-- **Headline 3 (`κ = 2^{-56}`):** Unconditional sub-`n log n` integer multiplication on `TM2`
in time `O(L · (log₂ L)^{1 - 2^{-56}})` (deduced from `κ = 2^{-46}` by exponent monotonicity; printed-interface row slack in `S5/Schedule.lean`, Remark 7.3 (`rem:printed-optimal`), Table 10). -/
theorem intMul_TM2_sub_nlogn_56 : Headline_TM2_SubNLogN_56 :=
  S5.headline_TM2_subNLogN_56

/-- **Headline 4 (`o(n log n)`):** Unconditional little-`o(n log n)` integer multiplication on `TM2`. -/
theorem intMul_TM2_littleO_nlogn : Headline_TM2_LittleO_NLogN :=
  S5.headline_TM2_littleO_nlogn

/-- **Component Headline S1:** Closed-form `h = 100` triple-network arithmetic & scalar-restoration checks (Appendix A; full proofs in `SubNLogN/Math/Networks/`). -/
theorem headline_S1_tripleNetworks_h100 : Headline_S1_TripleNetworks_h100 :=
  S1.headline_S1_holds

/-- **Component Headline S2:** Elementary `ℤ`/`ℕ` shear, division, and floor-remainder checks (Appendix A; full `TM2` kernels in `SubNLogN/Machine/{K1,AppC}/`). -/
theorem headline_S2_tapeTransfer : Headline_S2_TapeTransfer :=
  S2.headline_S2_holds

/-- **Component Headline S3:** Finite `2 × 2` Gaussian-integer, `Bool` XOR-swap, and modular-reflection checks (Sections 5–6; full proofs in `SubNLogN/{Math,Machine}/`). -/
theorem headline_S3_walshAndDirectFFT : Headline_S3_WalshAndDirectFFT :=
  S3.headline_S3_holds

/-- **Component Headline S4:** Closed-form integer exponent and rational-enclosure checks for Section 4 (`sec:bridge`; full proofs in `SubNLogN/{Math,Machine,Assembly}/`). -/
theorem headline_S4_bridgePrecision : Headline_S4_BridgePrecision :=
  S4.headline_S4_holds

/-- **Component Headline S5:** Four-way conjunction of the unconditional `TM2` headlines (`_46`, `_47`, `_56`, `LittleO`; Section 7, `sec:main`). -/
theorem headline_S5_scheduleAndMain : Headline_S5_ScheduleAndMain :=
  S5.headline_S5_holds

end SubNLogN
