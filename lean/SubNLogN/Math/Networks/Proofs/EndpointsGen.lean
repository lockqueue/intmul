import SubNLogN.Math.Networks.GeneralH
import SubNLogN.Math.Networks.Proofs.Endpoints2

/-!
# Endpoint certificates B2, C3 for general `h`

Proofs of `Prop7EndpointGenStmt h` (every `h ≠ 9`), `Prop8ZeroFullGenStmt h` and
`Prop8EndpointGenStmt h` (every `h`), statements in `GeneralH.lean`. The proofs are the uniform
ones of `Endpoints.lean` / `Endpoints2.lean` (`EndpointsAux.prop7Endpoint_gen`,
`EndpointsAux.prop8ZeroFull_gen`, `EndpointsAux.prop8Endpoint_gen`).

The hypothesis `h ≠ 9` is necessary for the bit statement: at `h = 9` the factor form `I - J/9`
kills the all-ones vector, so the ambient form `(I - J/9)^{⊗3}` is degenerate, `𝓕` is not
complemented by its orthogonal, `projAlong β₃ 𝓕 = 0`, and the identity `P_𝓕 - 0 = I` fails on the
scratch roles. The only `h`-dependent step of the proof is `(I + J/(9-h))(I - J/9) = I` (`J² = hJ`).
-/

namespace SubNLogN.Math.Networks

/-- **B2**, general `h ≠ 9`: `M_{sink(ρ(w))} - M_{source(w)} = I_m` for every role `w`. -/
theorem prop7EndpointGen_holds (h : ℕ) (h9 : h ≠ 9) : Prop7EndpointGenStmt h :=
  EndpointsAux.prop7Endpoint_gen h h9

/-- **C3, trivial routes**, every `h`: `C_0 = I` and `C_𝓕 = C^{⊗m}`. -/
theorem prop8ZeroFullGen_holds (h : ℕ) : Prop8ZeroFullGenStmt h :=
  EndpointsAux.prop8ZeroFull_gen h

/-- **C3**, every `h` and every number `k ≥ 1` of columns:
`i^{27k} Z_{a,k} C_{U_a^⊥}^{⊗k} (C_{U_a}^{⊗k})^{-1} Z_{a,k} = C^{⊗mk}`. -/
theorem prop8EndpointGen_holds (h : ℕ) : Prop8EndpointGenStmt h :=
  EndpointsAux.prop8Endpoint_gen h

end SubNLogN.Math.Networks
