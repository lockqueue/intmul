import SubNLogN.Challenge

/-!
NEGATIVE CONTROL (altered proof): an extra axiom (`Replay.Controls.P4.oracle : False`) used only
*indirectly*, through an intermediate lemma. `comparator` must detect the non-permitted axiom through the
transitive dependency chain `intMul_challenge → P4.lemma_from_oracle → P4.oracle`.
-/

namespace Replay.Controls.P4

axiom oracle : False

theorem lemma_from_oracle : SubNLogN.Challenge.IntMulSubNLogN := oracle.elim

end Replay.Controls.P4

theorem SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN :=
  Replay.Controls.P4.lemma_from_oracle
