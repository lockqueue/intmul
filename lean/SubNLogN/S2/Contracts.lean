import SubNLogN.S2.Streams
import SubNLogN.S2.Interchange
import SubNLogN.S2.Butterfly

/-!
# Component S2 (`Contracts.lean`): Assembly of `Headline_S2_TapeTransfer`
-/

namespace SubNLogN.S2

open SubNLogN

/-- Proof of `Headline_S2_TapeTransfer` from `S2/Streams`, `S2/Interchange`, and `S2/Butterfly`. -/
theorem headline_S2_holds : Headline_S2_TapeTransfer :=
  ⟨shear_step_pair_correct,
   role_split_volume_exact,
   truncation_toward_zero_error_sq⟩

end SubNLogN.S2
