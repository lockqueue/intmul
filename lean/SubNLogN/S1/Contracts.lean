import SubNLogN.S1.Params
import SubNLogN.S1.Lemma5
import SubNLogN.S1.Orbits
import SubNLogN.S1.Bruhat

/-!
# Component S1 (`Contracts.lean`): Assembly of `Headline_S1_TripleNetworks_h100`
-/

namespace SubNLogN.S1

open SubNLogN

/-- Proof of `Headline_S1_TripleNetworks_h100` from the `S1` component modules. -/
theorem headline_S1_holds : Headline_S1_TripleNetworks_h100 :=
  ⟨tripleM_100,
   tripleWb_100,
   tripleSb_100,
   tripleSavingBit_100,
   tripleWc_100,
   tripleSc_100,
   tripleSavingComplex_100,
   bit_deficit_tau_40,
   complex_deficit_sigma_42,
   printed_deficit_50.1,
   printed_deficit_50.2,
   guard_nu_11.1,
   guard_nu_11.2,
   lemma5_forward_restoration,
   open2_qradix5_coprime⟩

end SubNLogN.S1
