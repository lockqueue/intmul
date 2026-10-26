import SubNLogN.S5.Schedule
import SubNLogN.S5.Dispatcher
import SubNLogN.S5.CostAssembly
import SubNLogN.S5.ExecutablePipeline
import SubNLogN.S5.TopObligation

/-!
# Component S5 (`Contracts.lean`): Assembly of `Headline_S5_ScheduleAndMain`
-/

namespace SubNLogN.S5

open SubNLogN

/-- Proof of `Headline_S5_ScheduleAndMain` from `S5/TopObligation` (with `S5/Schedule` and `S5/Dispatcher`). -/
theorem headline_S5_holds : Headline_S5_ScheduleAndMain :=
  ⟨headline_TM2_subNLogN_46,
   headline_TM2_subNLogN_47,
   headline_TM2_subNLogN_56,
   headline_TM2_littleO_nlogn⟩

end SubNLogN.S5
