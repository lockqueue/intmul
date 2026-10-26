import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding

/-!
NEGATIVE CONTROL (statement constant swapped on the solution side): this module does NOT import
`SubNLogN/Challenge.lean`; it re-declares a constant with the same name `SubNLogN.Challenge.IntMulSubNLogN`
but defined as `True`, and "proves" it trivially. The theorem's type is syntactically the same constant name
as the challenge's, so a name-only comparison would be fooled; `comparator` must reject it because the
definition of `SubNLogN.Challenge.IntMulSubNLogN` differs between challenge and solution.
-/

namespace SubNLogN.Challenge

def IntMulSubNLogN : Prop := True

end SubNLogN.Challenge

theorem SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN := trivial
