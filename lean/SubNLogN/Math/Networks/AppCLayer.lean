import SubNLogN.Math.Networks.Framed
import SubNLogN.Math.Walsh.LayerSpec

/-!
# Appendix A at the math level (II): the complex contract (Lemma A.10 (`lem:transfer-phase`)) and the layer (Proposition A.11 (`prop:prop14-param`))

Lemma A.10 (`lem:transfer-phase`), Proposition A.11 (`prop:prop14-param`), Appendix A.5–A.6, and
Table 6 (`tab:walsh-rows`, Section 7.5). The value-level contract of the layer is `LayerSpec`
(`SubNLogN/Math/Walsh/LayerSpec.lean`): exact `Q_P(Hz)` on disk-grid inputs.
-/

namespace SubNLogN.Math.Networks

open SubNLogN.Math.Walsh

/-! ## Lemma A.10 (`lem:transfer-phase`): the exact recursive complex contract -/

/-- Apply a matrix on the column index of an array with spectator part `σ`. -/
noncomputable def applyCol {ι σ : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (f : ι × σ → ℂ) : ι × σ → ℂ :=
  fun p => ∑ y, A p.1 y * f (y, p.2)

/-- Physical edge operators of the complex network on `k` columns: `(C_V C_U⁻¹)^{⊗k}`. -/
noncomputable def cxEdgeOps {σ : Type*} (k : ℕ) :
    EdgeOps .complex 100 ((Fin k → Pt 100) × σ → ℂ) :=
  fun _ e f => applyCol (tpow k (frameC e.2) * (tpow k (frameC e.1))⁻¹) f

/-- Source correction `Z_{a,k}` before the network at `X_a` ([OAI26, §3.5, Prop. 8]). -/
noncomputable def cxPre {σ : Type*} (k : ℕ) (s : Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ)) :
    Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ)
  | .X a => applyCol (Zk k (ua a)) (s (.X a))
  | w => s w

/-- Sink corrections ([OAI26, §3.5, Prop. 8]): `i^{27k} Z_{a,k}` at `Y_a`, negation of the physical `X`
outputs. -/
noncomputable def cxPost {σ : Type*} (k : ℕ) (t : Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ)) :
    Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ)
  | .Y a => applyCol ((Complex.I ^ (27 * k)) • Zk k (ua a)) (t (.Y a))
  | .X a => -t (.X a)
  | w => t w

/-- CONTRACT (Lemma A.10 (`lem:transfer-phase`) network part; [OAI26, §3.5, Prop. 8];
Appendix A.5 (`sec:transfer-frames`)). At `h = 100`, on `k ≥ 1` columns, running the complex network with
edge operators `(C_V C_U⁻¹)^{⊗k}`, the source/sink corrections, and returning output role `ρ(w)` to
role `w`, every role (scratch included, arbitrary inputs) carries `C^{⊗mk}` of its input. -/
def ComplexArrayCorollaryStmt : Prop :=
  ∀ (σ : Type) (k : ℕ), 1 ≤ k → ∀ (s : Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ))
    (w : Role .complex 100),
    cxPost k (framedNet .complex (2⁻¹ : ℂ) (cxEdgeOps k) (cxPre k s)) w.rho =
      applyCol (tpow k Cfull) (s w)

/-- The move operator of a binary matrix: `(P_M f)(x) = f(M⁻¹x)` (entry `1` iff `x = M y`). -/
def permOp {h : ℕ} (M : Matrix (Cube h) (Cube h) (ZMod 2)) : Matrix (Pt h) (Pt h) ℂ :=
  fun x y => if x = M.mulVec y then 1 else 0

/-- CONTRACT (Lemma A.10 (`lem:transfer-phase`) coordinate kernels). For invertible binary `M`,
`P_M X_v P_M⁻¹ = X_{Mv}`; hence an edge operator `Π_{v∈B} K_v^{±1}` is `P_M (Π_j K_{e_j}^{±1}) P_M⁻¹`
when the first columns of `M` are `B`, and each `K_{e_j}` on `f` columns is one child `C^{⊗f}`. -/
def TranslationConjStmt : Prop :=
  ∀ (h : ℕ) (M M' : Matrix (Cube h) (Cube h) (ZMod 2)), M * M' = 1 →
    ∀ v : Pt h, permOp M * Xv v * permOp M' = Xv (M.mulVec v)

/-- An elementary row addition `row_i ← row_i + row_j` over `𝔽₂`. -/
def rowAdd {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) := 1 + Matrix.single i j 1

/-- CONTRACT (Lemma A.10 (`lem:transfer-phase`) row additions). Every invertible binary `n × n`
matrix is a product of at most `n(n−1) + 3n` elementary row additions (`i ≠ j`); in a group of `mf`
chunks each one is a packed selected-bit addition between two slots (Lemma A.9 (`lem:transfer13`)). -/
def BinaryRowAdditionsStmt : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)), IsUnit M.det →
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, p.1 ≠ p.2) ∧ l.length ≤ n * (n - 1) + 3 * n ∧
      M = (l.map fun p => rowAdd p.1 p.2).prod

/-! ## Proposition A.11 (`prop:prop14-param`): exactness, guard, cost -/

/-- `H₀^{⊗D}` on functions of `D` selected bits. -/
noncomputable def H0D (D : ℕ) (z : (Fin D → Bool) → ℂ) : (Fin D → Bool) → ℂ := fun e =>
  ((2 : ℂ) ^ D)⁻¹ * ∑ e' : Fin D → Bool,
    (-1 : ℂ) ^ (Finset.univ.filter fun j => e j = true ∧ e' j = true).card * z e'

/-- `𝒮_D`: multiplication by `i^{x₁+⋯+x_D}`. -/
noncomputable def SD (D : ℕ) (z : (Fin D → Bool) → ℂ) : (Fin D → Bool) → ℂ := fun e =>
  Complex.I ^ (Finset.univ.filter fun j => e j = true).card * z e

/-- `C^{⊗D}`, `C = aI + bX`. -/
noncomputable def CD (D : ℕ) (z : (Fin D → Bool) → ℂ) : (Fin D → Bool) → ℂ := fun e =>
  ∑ e' : Fin D → Bool, (∏ j, (if e j = e' j then ka else kb)) * z e'

/-- `b^D = (−i/2)^{⌊D/2⌋} b^{D mod 2}`. -/
noncomputable def bD (D : ℕ) : ℂ := (-Complex.I / 2) ^ (D / 2) * kb ^ (D % 2)

/-- CONTRACT (eq. (`eq:oai-h0`), `eq:oai-h0-transfer`; [OAI26, §5.1, (18)]):
`H₀^{⊗D} = b^D 𝒮_D C^{⊗D} 𝒮_D`. -/
def H0TensorIdentityStmt : Prop :=
  ∀ (D : ℕ) (z : (Fin D → Bool) → ℂ), H0D D z = bD D • SD D (CD D (SD D z))

/-- CONTRACT (Proposition A.11 (`prop:prop14-param`), value level, Appendix A.6 (`sec:transfer-layer`)). If `Csch` evaluates
`C^{⊗D}` exactly on the selected bits (as the recursion of Lemma A.10 (`lem:transfer-phase`) does, with no internal rounding thanks
to the guard), then `Q_P ∘ (b^D 𝒮_D Csch 𝒮_D)` satisfies `LayerSpec` (returns exactly `Q_P(Hz)`
on disk-grid inputs). -/
def Prop71FunctionalStmt : Prop :=
  ∀ (P r A K D S : ℕ) (ρ : Fin K) (Csch : RArr (LayerAddr A K D S) r → RArr (LayerAddr A K D S) r),
    (∀ z x₀ e₀ k, Csch z (setSelBits ρ x₀ e₀) k = CD D (fun e => z (setSelBits ρ x₀ e) k) e₀) →
    LayerSpec P r A K D S ρ (fun z => truncArr P (fun x k => bD D *
      (Complex.I ^ (Finset.univ.filter fun j => x.2.1 j ρ = true).card *
        Csch (fun y k' => Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card * z y k')
          x k)))

/-- CONTRACT (guard arithmetic, Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)): `s_c < m^5` (so
`s_c^{j_max} ≤ s_c d^5`). -/
theorem sc_lt_m_pow5 : tripleSc 100 < tripleM 100 ^ 5 := by
  decide

/-- CONTRACT (guard growth, Proposition A.11 (`prop:prop14-param`), eq. (`eq:walsh-guard-growth`)). For every constant `C_dep` and
`C₁ ≥ 14`, eventually `(m C_dep + 18) d⁷ ≤ C₀ d^{C₁}` (`C₀ = guardC0 100`). -/
def GuardGrowthStmt : Prop :=
  ∀ (Cdep : ℝ) (C1 : ℕ), 14 ≤ C1 → ∃ dstar : ℕ, ∀ d : ℕ, dstar ≤ d →
    ((tripleM 100 : ℝ) * Cdep + 18) * (d : ℝ) ^ 7 ≤ (guardC0 100 : ℝ) * (d : ℝ) ^ C1

/-- CONTRACT (guard is `o(P)`, Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)). With `d ≤ b_d P^ε` and `ε C₁ < 1`,
eventually `C₀ d^{C₁} ≤ P`. -/
def GuardSmallStmt : Prop :=
  ∀ (bd ε : ℝ) (C1 : ℕ), 0 < bd → 0 < ε → ε * C1 < 1 →
    ∃ P₀ : ℝ, ∀ P d : ℝ, P₀ ≤ P → 1 ≤ d → d ≤ bd * P ^ ε → (guardC0 100 : ℝ) * d ^ C1 ≤ P

/-- CONTRACT (layer recurrence, Proposition A.11 (`prop:prop14-param`), eqs. (`eq:walsh-layer-recurrence`)–(`eq:walsh-layer-unrolled`)). Let `m > 1`, `0 ≤ a ≤ m^σ`,
`0 ≤ σ < λ ≤ 1`, `β > 0`, `c, τ ≥ 0`, `τ(1 + c/β) ≤ λ`. There is `C'` such that for all `d ≥ 1`,
`1 ≤ K ≤ d^c` and normalized costs `F` (level `k` = `m^k` chunks) with `F 0 ≤ C`, leaves
`F k ≤ C m^k` when `m^k < d^β`, and internal nodes `F (k+1) ≤ a F k + C((m^{k+1} K)^τ + 1)` when
`d^β ≤ m^{k+1}`: every level with `m^k ≤ d` has `F k ≤ C' (d^λ + d^{σ+β(1−σ)} + 1)`. -/
def LayerRecurrenceStmt : Prop :=
  ∀ (m a C β c τ σ lam : ℝ), 1 < m → 0 ≤ a → a ≤ m ^ σ → 0 ≤ σ → σ < lam → lam ≤ 1 → 0 < β →
    0 ≤ c → 0 ≤ τ → τ * (1 + c / β) ≤ lam → 0 ≤ C →
    ∃ C' : ℝ, ∀ (d K : ℝ) (F : ℕ → ℝ), 1 ≤ d → 1 ≤ K → K ≤ d ^ c → F 0 ≤ C →
      (∀ k : ℕ, m ^ k < d ^ β → F k ≤ C * m ^ k) →
      (∀ k : ℕ, d ^ β ≤ m ^ (k + 1) → F (k + 1) ≤ a * F k + C * ((m ^ (k + 1) * K) ^ τ + 1)) →
      ∀ k : ℕ, m ^ k ≤ d → F k ≤ C' * (d ^ lam + d ^ (σ + β * (1 - σ)) + 1)

/-- The `κ = 2^{-46}` row (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)): `ξ = 2^{-42}`, `τ = 1−4ξ`, `σ = 1−ξ`, `β = 1/64`,
`c = ξ/256`, `λ = 1−63ξ/64`, `λ' = 1−31ξ/32`, `ε = 1/15`, `C₁ = 14`. -/
noncomputable def xi46 : ℝ := (2 : ℝ)⁻¹ ^ 42

/-- CONTRACT (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)): the `κ = 2^{-46}` row satisfies the hypotheses of Proposition A.11 (`prop:prop14-param`):
`max{τ,σ} < λ < 1`, `τ(1+c/β) < λ`, `max{λ, σ+β(1−σ)} < λ' < 1`, `ε C₁ < 1`. -/
def Row46AdmissibleStmt : Prop :=
  let ξ := xi46
  max (1 - 4 * ξ) (1 - ξ) < 1 - 63 * ξ / 64 ∧ 1 - 63 * ξ / 64 < 1 ∧
    (1 - 4 * ξ) * (1 + (ξ / 256) / (1 / 64)) < 1 - 63 * ξ / 64 ∧
    max (1 - 63 * ξ / 64) ((1 - ξ) + (1 / 64) * (1 - (1 - ξ))) < 1 - 31 * ξ / 32 ∧
    1 - 31 * ξ / 32 < 1 ∧ (1 / 15 : ℝ) * 14 < 1

end SubNLogN.Math.Networks
