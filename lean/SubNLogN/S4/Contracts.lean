import SubNLogN.S4.Solver
import SubNLogN.S4.Precision

/-!
# Component S4 (`Contracts.lean`): Assembly of `Headline_S4_BridgePrecision`
-/

namespace SubNLogN.S4

open SubNLogN

/-- Proof of `Headline_S4_BridgePrecision` from `S4/Solver` and `S4/Precision`. -/
theorem headline_S4_holds : Headline_S4_BridgePrecision :=
  ⟨bridge_master_margin,
   sqrt2_upper_enclosure,
   bridge_total_error_lt_0177021,
   two_call_root_recovery_lt_half⟩

end SubNLogN.S4
