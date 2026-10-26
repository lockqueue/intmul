import SubNLogN.Headline
import SubNLogN.Assembly.ChallengeTransport

/-!
# The frozen challenge statement, from the `Spec` headline

`intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN` is the unconditional transport
`SubNLogN.Assembly.challenge_of_spec` (`SubNLogN/Assembly/ChallengeTransport.lean`) applied to the
`Spec`-level headline `SubNLogN.intMul_TM2_sub_nlogn_46 : SubNLogN.Headline_TM2_SubNLogN_46`
(`SubNLogN/Headline.lean`; `Headline_TM2_SubNLogN_46` unfolds to `SubNLogN.IntMulSubNLogN 46`).

**Status.** Unconditional: `SubNLogN.intMul_TM2_sub_nlogn_46` is `SubNLogN.S5.headline_TM2_subNLogN_46`,
derived from `SubNLogN.S5.w9SubNLogNSpecX_holds`, which is proved with 0 `sorry` (`SubNLogN/S5/TopObligation.lean`).
`#print axioms intMul_challenge` lists only Lean's standard axioms.
-/

namespace SubNLogN.Assembly

/-- **Challenge headline (`κ = 2^{-46}`)**: the frozen statement
`SubNLogN.Challenge.IntMulSubNLogN` of `SubNLogN/Challenge.lean`, obtained by transporting the
`Spec` headline `SubNLogN.intMul_TM2_sub_nlogn_46` along `challenge_of_spec`. Proved with 0 `sorry` (standard axioms only). -/
theorem intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN :=
  challenge_of_spec SubNLogN.intMul_TM2_sub_nlogn_46

end SubNLogN.Assembly
