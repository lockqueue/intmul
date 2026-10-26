import SubNLogN.Headline
import SubNLogN.Assembly.ChallengeTransport

/-!
NEGATIVE CONTROL (altered proof): the genuine proof term of `SubNLogN/Assembly/ChallengeHeadline.lean`,
preceded by a numerical side fact discharged with `native_decide`. `native_decide` introduces the axiom
`Lean.ofReduceBool` (trusting the compiler); `comparator` must reject the proof because that axiom is not
permitted, even though the Lean kernel accepts the declaration.
-/

theorem SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN := by
  have h : (2 : ℕ) ^ 46 = 70368744177664 := by native_decide
  exact SubNLogN.Assembly.challenge_of_spec SubNLogN.intMul_TM2_sub_nlogn_46

#print axioms SubNLogN.Assembly.intMul_challenge
