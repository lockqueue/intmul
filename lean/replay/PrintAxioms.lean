import SubNLogN.Assembly.ChallengeHeadline
import IntMulTM.Headline

/-!
Axioms used by the two headline theorems (run with `lake env lean replay/PrintAxioms.lean` from the
project root). `#print axioms` lists every axiom reachable from the proof term.
-/

#print axioms SubNLogN.Assembly.intMul_challenge
#print axioms IntMulTM.intMul_TM2_nlogn

-- The exact statement of the challenge headline, as elaborated (for the record).
#check @SubNLogN.Assembly.intMul_challenge
#print SubNLogN.Challenge.IntMulSubNLogN
