import SubNLogN.Math.Networks.Basic

/-!
# Networks, part 3: subspace labels and [OAI26] Lemma 6

Symbolic labels ([OAI26, §3.3]): every label is an orthogonal sum of pure
tensors `U₁ ⊗ U₂ ⊗ U₃` of factor tokens `0, F, ⟨t_T⟩, t_T^⊥, ⟨t_S,t_T⟩^⊥`. Their meaning
(`labelSub`) is a subspace of `𝓕 = F^{⊗3}`, realized as functions on the cube `[h]³`, for a factor
bilinear form on `F = K^h`:
* bit network: `K = ℚ`, `⟨x, y⟩ = xᵀ(I − J/9)y` ([OAI26, §3.3]);
* complex network: `K = 𝔽₂`, the dot product ([OAI26, §3.3]).
The ambient form on `𝓕` is the tensor cube of the factor form ([OAI26, §3.3]).

Stage `j` of an invocation with fixed coordinates `ι` uses `A = F^{⊗(j−1)}`,
`P = ⟨t_{a₁} ⊗ … ⊗ t_{a_{j−1}}⟩`, `B = P^⊥ ⊂ A`, `Q = ⟨t_{a_{j+1}} ⊗ … ⟩` ([OAI26, §3.3]) and the gate
labels of table (6) ([OAI26, §3.3, (6)]), all tensored with `Q`.
-/

namespace SubNLogN.Math.Networks

variable {h : ℕ}

/-- Coordinates of `𝓕 = F^{⊗3}`: the cube `[h]³` (`dim 𝓕 = m = h³`). -/
abbrev Cube (h : ℕ) := Fin h × Fin h × Fin h

/-- Factor tokens: `0`, `F`, `⟨t_T⟩`, `t_T^⊥`, `⟨t_S, t_T⟩^⊥`. -/
inductive Tok (h : ℕ) where
  | zero
  | full
  | line (t : Tri h)
  | perp (t : Tri h)
  | perp2 (s t : Tri h)
  deriving DecidableEq

/-- A pure tensor `U₁ ⊗ U₂ ⊗ U₃` of tokens. -/
abbrev Summand (h : ℕ) := Tok h × Tok h × Tok h

/-- A symbolic label: an (orthogonal) sum of pure tensors of tokens. -/
abbrev SymLabel (h : ℕ) := List (Summand h)

/-- `A ⊗ τ ⊗ Q` at stage `j` (`A = F^{⊗(j−1)}`, `τ` at coordinate `j`). -/
def stA : Stage → Fix h → Tok h → SymLabel h
  | .one, ι, τ => [(τ, .line ι.1, .line ι.2)]
  | .two, ι, τ => [(.full, τ, .line ι.2)]
  | .three, _, τ => [(.full, .full, τ)]

/-- `B ⊗ τ ⊗ Q` at stage `j`, `B = P^⊥ ⊂ A` (`B = 0` at stage 1, [OAI26, §3.3]). -/
def stB : Stage → Fix h → Tok h → SymLabel h
  | .one, _, _ => []
  | .two, ι, τ => [(.perp ι.1, τ, .line ι.2)]
  | .three, ι, τ => [(.perp ι.1, .full, τ), (.line ι.1, .perp ι.2, τ)]

/-- `P ⊗ τ ⊗ Q` at stage `j`. -/
def stP : Stage → Fix h → Tok h → SymLabel h
  | .one, ι, τ => [(τ, .line ι.1, .line ι.2)]
  | .two, ι, τ => [(.line ι.1, τ, .line ι.2)]
  | .three, ι, τ => [(.line ι.1, .line ι.2, τ)]

/-- Gate labels, table (6) ([OAI26, §3.3, (6)]): time 0 `B⊗⟨t⟩`, times 1, 4 `B⊗F`,
time 2 `(B⊗F) ⊥ (P⊗⟨t⟩)`, times 3, 6, 7 `A⊗F`, time 5 `(B⊗F) ⊥ (P⊗t^⊥)`, all `⊗ Q`. -/
def gateLabel : Gate h → SymLabel h
  | .side j ι r t =>
      if r = 0 then stB j ι (.line t)
      else if r = 2 then stB j ι .full ++ stP j ι (.line t)
      else if r = 5 then stB j ι .full ++ stP j ι (.perp t)
      else stA j ι .full
  | .center j ι r => if r = 3 ∨ r = 6 then stA j ι .full else stB j ι .full

/-- `U_a = ⟨t_{a₁} ⊗ t_{a₂} ⊗ t_{a₃}⟩` ([OAI26, §3.3]). -/
def labU (a : Addr h) : SymLabel h := [(.line a.1, .line a.2.1, .line a.2.2)]

/-- `U_a^⊥` as an orthogonal sum of pure tensors. -/
def labUperp (a : Addr h) : SymLabel h :=
  [(.perp a.1, .full, .full), (.line a.1, .perp a.2.1, .full), (.line a.1, .line a.2.1, .perp a.2.2)]

/-- The full space `𝓕`. -/
def labFull : SymLabel h := [(.full, .full, .full)]

/-- Source labels ([OAI26, §3.3]): `U_a` on `X_a`, `0` elsewhere. -/
def sourceLabel {κ : Kind} : Role κ h → SymLabel h
  | .X a => labU a
  | _ => []

/-- Sink labels ([OAI26, §3.3]): `U_a^⊥` on `Y_a`, `𝓕` elsewhere. -/
def sinkLabel {κ : Kind} : Role κ h → SymLabel h
  | .Y a => labUperp a
  | _ => labFull

/-- The label of a vertex. -/
def vlabel {κ : Kind} : Vertex κ h → SymLabel h
  | .source w => sourceLabel w
  | .gate g => gateLabel g
  | .sink w => sinkLabel w

/-! ### Meaning of a label -/

section Semantics

variable {K : Type*} [Field K]

/-- The indicator vector `t_T ∈ K^h` of a triple. -/
def ind (t : Tri h) : Fin h → K := fun i => if i ∈ t.1 then 1 else 0

/-- Meaning of a token for a factor form `β`. -/
def tokSub (β : LinearMap.BilinForm K (Fin h → K)) : Tok h → Submodule K (Fin h → K)
  | .zero => ⊥
  | .full => ⊤
  | .line t => K ∙ ind t
  | .perp t => β.orthogonal (K ∙ ind t)
  | .perp2 s t => β.orthogonal (Submodule.span K {ind s, ind t})

/-- The pure tensor `u ⊗ v ⊗ w` as a function on the cube. -/
def pure3 (u v w : Fin h → K) : Cube h → K := fun p => u p.1 * v p.2.1 * w p.2.2

/-- Meaning of a pure tensor of tokens: the span of `u ⊗ v ⊗ w` over its factors. -/
def summandSub (β : LinearMap.BilinForm K (Fin h → K)) (σ : Summand h) :
    Submodule K (Cube h → K) :=
  Submodule.span K {x | ∃ u ∈ tokSub β σ.1, ∃ v ∈ tokSub β σ.2.1, ∃ w ∈ tokSub β σ.2.2,
    x = pure3 u v w}

/-- Meaning of a symbolic label: the sum of the meanings of its summands. -/
def labelSub (β : LinearMap.BilinForm K (Fin h → K)) (L : SymLabel h) : Submodule K (Cube h → K) :=
  (L.map (summandSub β)).foldr (· ⊔ ·) ⊥

/-- Triple Kronecker product of factor matrices. -/
def kron3 (A B C : Matrix (Fin h) (Fin h) K) : Matrix (Cube h) (Cube h) K :=
  fun p q => A p.1 q.1 * B p.2.1 q.2.1 * C p.2.2 q.2.2

end Semantics

/-- The bit factor Gram matrix `I − J/9` ([OAI26, §3.3]). -/
def G0 (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := 1 - (9 : ℚ)⁻¹ • Matrix.of (fun _ _ => (1 : ℚ))

/-- The bit factor form `xᵀ(I − J/9)y` on `ℚ^h`. -/
noncomputable def betaB (h : ℕ) : LinearMap.BilinForm ℚ (Fin h → ℚ) := Matrix.toBilin' (G0 h)

/-- The bit ambient form on `𝓕 = ℚ^{[h]³}`: the tensor cube of `I − J/9`. -/
noncomputable def betaB3 (h : ℕ) : LinearMap.BilinForm ℚ (Cube h → ℚ) :=
  Matrix.toBilin' (kron3 (G0 h) (G0 h) (G0 h))

/-- The complex-network factor form: the dot product on `𝔽₂^h` ([OAI26, §3.3]). -/
noncomputable def betaC (h : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin h → ZMod 2) := Matrix.toBilin' 1

/-- The complex-network ambient form: the dot product on `𝔽₂^{[h]³}`. -/
noncomputable def betaC3 (h : ℕ) : LinearMap.BilinForm (ZMod 2) (Cube h → ZMod 2) :=
  Matrix.toBilin' 1

/-- Bit label of a vertex, as a subspace of `ℚ^{[h]³}`. -/
noncomputable def labB {κ : Kind} (v : Vertex κ h) : Submodule ℚ (Cube h → ℚ) :=
  labelSub (betaB h) (vlabel v)

/-- Binary label of a vertex, as a subspace of `𝔽₂^{[h]³}`. -/
noncomputable def labC {κ : Kind} (v : Vertex κ h) : Submodule (ZMod 2) (Cube h → ZMod 2) :=
  labelSub (betaC h) (vlabel v)

/-- Orthogonal residual of an edge with labels `U` (tail), `V` (head): `V ∩ U^⊥` if `U ≤ V`,
else `U ∩ V^⊥` ([OAI26, §3.3]). -/
noncomputable def residual {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (β : LinearMap.BilinForm K V)
    (U W : Submodule K V) : Submodule K V :=
  open Classical in if U ≤ W then W ⊓ β.orthogonal U else U ⊓ β.orthogonal W

/-! ### Contracts: [OAI26] Lemma 6 at `h = 100` (pending results as `Prop`s) -/

/-- CONTRACT. [OAI26, §3.3, Lemma 6], bit network, `h = 100`: every vertex
label is nondegenerate for the ambient form (`U ⊕ U^⊥ = 𝓕`). -/
def Lemma6NondegBitStmt : Prop :=
  ∀ v : Vertex .bit 100, IsCompl (labB v) ((betaB3 100).orthogonal (labB v))

/-- CONTRACT. [OAI26] Lemma 6, complex network (binary labels), `h = 100`: every vertex label is
nondegenerate for the dot product. -/
def Lemma6NondegComplexStmt : Prop :=
  ∀ v : Vertex .complex 100, IsCompl (labC v) ((betaC3 100).orthogonal (labC v))

/-- CONTRACT. [OAI26] Lemma 6, `h = 100`, both networks: every edge joins comparable labels. -/
def Lemma6NestedStmt : Prop :=
  (∀ w : Role .bit 100, ∀ e ∈ edges w, labB e.1 ≤ labB e.2 ∨ labB e.2 ≤ labB e.1) ∧
  (∀ w : Role .complex 100, ∀ e ∈ edges w, labC e.1 ≤ labC e.2 ∨ labC e.2 ≤ labC e.1)

/-- CONTRACT. [OAI26] Lemma 6, `h = 100`: the only decreasing edges are the central-wire edges
from time 3 to time 4 of an invocation, and each loses dimension exactly `h = 100`
(bit network; the complex statement is `Lemma6DecreasingComplexStmt`). -/
def Lemma6DecreasingBitStmt : Prop :=
  ∀ (w : Role .bit 100) (e : Vertex .bit 100 × Vertex .bit 100), e ∈ edges w →
    ¬ labB e.1 ≤ labB e.2 →
    (∃ j ι c, w = .center j ι c ∧ e = (.gate (.center j ι 3), .gate (.center j ι 4))) ∧
    Module.finrank ℚ (labB e.1) = Module.finrank ℚ (labB e.2) + 100

/-- CONTRACT. [OAI26] Lemma 6, complex network, `h = 100` (same statement over `𝔽₂`). -/
def Lemma6DecreasingComplexStmt : Prop :=
  ∀ (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100), e ∈ edges w →
    ¬ labC e.1 ≤ labC e.2 →
    (∃ j ι c, w = .center j ι c ∧ e = (.gate (.center j ι 3), .gate (.center j ι 4))) ∧
    Module.finrank (ZMod 2) (labC e.1) = Module.finrank (ZMod 2) (labC e.2) + 100

/-- CONTRACT. [OAI26, §3.3, (7)], `h = 100`: the absolute label-dimension changes
sum to `W m − 2N + 2L`, with `L_b = I·h·h`, `L_c = I·(h+1)·h`. -/
def Lemma6AbsSumStmt : Prop :=
    (∑ w : Role .bit 100, ((edges w).map fun e =>
        Int.natAbs ((Module.finrank ℚ (labB e.2) : ℤ) - Module.finrank ℚ (labB e.1))).sum) =
      tripleWb 100 * tripleM 100 - 2 * tripleN 100 + 2 * tripleLb 100 ∧
    (∑ w : Role .complex 100, ((edges w).map fun e =>
        Int.natAbs ((Module.finrank (ZMod 2) (labC e.2) : ℤ) - Module.finrank (ZMod 2) (labC e.1))).sum) =
      tripleWc 100 * tripleM 100 - 2 * tripleN 100 + 2 * tripleLc 100

end SubNLogN.Math.Networks
