import SubNLogN.Challenge

/-!
Statement-only challenge module for `comparator`.

It imports the frozen statement file `SubNLogN/Challenge.lean` unchanged and states the headline
theorem with its proof left open. `comparator` compares this statement (and, recursively, every
constant it depends on) against the exported theorem of the solution module
`SubNLogN.Assembly.ChallengeHeadline`, checks that the solution's proof uses only the permitted
axioms, and replays the solution's proof in the Lean kernel (and, if enabled, in `nanoda`).
-/

theorem SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN := sorry
