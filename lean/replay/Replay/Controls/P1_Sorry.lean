import SubNLogN.Challenge

/-!
NEGATIVE CONTROL (altered proof): the real statement `SubNLogN.Challenge.IntMulSubNLogN`, "proved" by
`sorry`. The Lean kernel accepts this module (`sorryAx` is an axiom), so kernel replay alone cannot reject
it; `comparator` must reject it because `sorryAx` is not a permitted axiom.
-/

theorem SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN := sorry
