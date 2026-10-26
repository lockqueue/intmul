import SubNLogN.Math.Networks.Labels

/-!
# Networks, part 4: rational frames of the bit network ([OAI26] Prop. 7)

Frame matrices `M_v` ([OAI26, §3.4, Prop. 7]): the projection `P_U` onto the label `U` along `U^⊥` (for the
ambient form `(I − J/9)^{⊗3}`) at every gate and sink, `−P_{U_a}` at the source of `X_a`, and `0`
at the other sources. Edge matrices `A_e = M_head − M_tail`; `s_b = Σ_e rank_ℚ A_e`.
-/

namespace SubNLogN.Math.Networks

/-- The projection onto `U` along its `β`-orthogonal complement ([OAI26, §3.4, Prop. 7]); defined as `0` when
`U ⊕ U^⊥ ≠ V` (this never happens for network labels, `Lemma6NondegBitStmt`). -/
noncomputable def projAlong {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (β : LinearMap.BilinForm K V) (U : Submodule K V) : V →ₗ[K] V :=
  open Classical in
  if hU : IsCompl U (β.orthogonal U) then Submodule.projection U (β.orthogonal U) hU else 0

/-- Rational frame matrix at a vertex of the bit network ([OAI26, §3.4, Prop. 7]). -/
noncomputable def frameB {h : ℕ} : Vertex .bit h → Module.End ℚ (Cube h → ℚ)
  | .source (.X a) => -projAlong (betaB3 h) (labelSub (betaB h) (labU a))
  | .source _ => 0
  | v => projAlong (betaB3 h) (labB v)

/-- Edge matrix `A_e = M_head − M_tail` ([OAI26, §3.4, Prop. 7]; Definition A.1(a) (`def:fixed-network-premises`)). -/
noncomputable def edgeMatB {h : ℕ} (e : Vertex .bit h × Vertex .bit h) :
    Module.End ℚ (Cube h → ℚ) :=
  frameB e.2 - frameB e.1

/-- Rational rank of an endomorphism of `ℚ^{[h]³}`. -/
noncomputable def rankQ {h : ℕ} (A : Module.End ℚ (Cube h → ℚ)) : ℕ :=
  Module.finrank ℚ (LinearMap.range A)

/-! ### Contracts: [OAI26] Prop. 7 at `h = 100` (pending results as `Prop`s) -/

/-- CONTRACT (B2). [OAI26, §3.4, Prop. 7]: at `h = 100`, for every role
`w`, `M_{sink(ρ(w))} − M_{source(w)} = I_m` (on `X_a`: `P_{U_a^⊥} − (−P_{U_a}) = I`; on the other
roles `P_𝓕 − 0 = I`). Frames are common to all incidences of a gate by construction (`frameB`
depends only on the vertex). -/
def Prop7EndpointStmt : Prop :=
  ∀ w : Role .bit 100, frameB (.sink w.rho) - frameB (.source w) = 1

/- The rank sum `prop7_rank_sum` (B4) is in `CellCalc.lean` (proved there from the per-role
soundness contracts, class counting and the kernel evaluation). -/

end SubNLogN.Math.Networks
