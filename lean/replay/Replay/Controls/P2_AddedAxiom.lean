import SubNLogN.Challenge

/-!
NEGATIVE CONTROL (altered proof): the real statement, "proved" by an ad-hoc axiom asserting it.
`comparator` must reject it because `Replay.Controls.P2.intMul_challenge_axiom` is not a permitted axiom.
-/

namespace Replay.Controls.P2

axiom intMul_challenge_axiom : SubNLogN.Challenge.IntMulSubNLogN

end Replay.Controls.P2

theorem SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN :=
  Replay.Controls.P2.intMul_challenge_axiom
