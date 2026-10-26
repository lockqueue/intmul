import SubNLogN.Math.Networks.BitFrames

/-!
# Networks, part 5: phase frames of the complex network ([OAI26] Prop. 8)

Binary labels `U ⊂ 𝔽₂^m` (`m = h³`, coordinates the cube `[h]³`), `q_U(x) = wt(P_U x) mod 4`, and the
phase frame `C_U = H^{⊗m} diag(i^{q_U(x)}) H^{⊗m}` acting on functions `𝔽₂^m → ℂ` ([OAI26, §3.5, Prop. 8]).
With the normalised `H`, `(C_U)_{y,x} = 2^{−m} Σ_z (−1)^{(x+y)·z} i^{q_U(z)}`. Translation
`(X_v f)(x) = f(x + v)`; kernels `aI + bX_v` and its inverse `bI + aX_v`, `a = (1+i)/2`,
`b = (1−i)/2`. On `k` columns operators act by tensor powers (`tpow`).
-/

namespace SubNLogN.Math.Networks

/-- Points `x ∈ 𝔽₂^m`, `m = h³`. -/
abbrev Pt (h : ℕ) := Cube h → ZMod 2

/-- Integer Hamming weight. -/
def wt {h : ℕ} (x : Pt h) : ℕ := (Finset.univ.filter (fun p => x p ≠ 0)).card

/-- The `𝔽₂` dot product. -/
def dotC {h : ℕ} (x y : Pt h) : ZMod 2 := ∑ p, x p * y p

/-- `q_U(x) = wt(P_U x) mod 4`, projection over `𝔽₂` ([OAI26, §3.5, Prop. 8]). -/
noncomputable def qU {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) (x : Pt h) : ℕ :=
  wt (projAlong (betaC3 h) U x) % 4

/-- The phase frame `C_U` ([OAI26, §3.5, Prop. 8]). -/
noncomputable def CU {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) : Matrix (Pt h) (Pt h) ℂ :=
  fun y x => ((2 : ℂ) ^ (h ^ 3))⁻¹ * ∑ z : Pt h, (-1 : ℂ) ^ (dotC (x + y) z).val * Complex.I ^ (qU U z)

/-- Translation by `v`: `(X_v f)(x) = f(x + v)`. -/
def Xv {h : ℕ} (v : Pt h) : Matrix (Pt h) (Pt h) ℂ := fun x y => if y = x + v then 1 else 0

/-- `a = (1+i)/2`. -/
noncomputable def ka : ℂ := (1 + Complex.I) / 2

/-- `b = (1−i)/2`. -/
noncomputable def kb : ℂ := (1 - Complex.I) / 2

/-- Translation kernel `aI + bX_v` (`ε = 1`) or its inverse `bI + aX_v` (`ε ≠ 1`). -/
noncomputable def Kv {h : ℕ} (v : Pt h) (ε : ℤ) : Matrix (Pt h) (Pt h) ℂ :=
  if ε = 1 then ka • (1 : Matrix (Pt h) (Pt h) ℂ) + kb • Xv v else kb • 1 + ka • Xv v

/-- Phase frame at a vertex of the complex network. -/
noncomputable def frameC {h : ℕ} (v : Vertex .complex h) : Matrix (Pt h) (Pt h) ℂ := CU (labC v)

/-- Orthogonal residual of an edge of the complex network. -/
noncomputable def residC {h : ℕ} (e : Vertex .complex h × Vertex .complex h) :
    Submodule (ZMod 2) (Pt h) :=
  residual (betaC3 h) (labC e.1) (labC e.2)

/-- `B` is an orthonormal basis of `E` (norm-one, pairwise orthogonal, spanning). -/
def IsONB {h : ℕ} (E : Submodule (ZMod 2) (Pt h)) (B : List (Pt h)) : Prop :=
  (∀ v ∈ B, dotC v v = 1) ∧ B.Pairwise (fun u v => dotC u v = 0) ∧
    Submodule.span (ZMod 2) {v | v ∈ B} = E

/-- Kernel sign of a residual vector ([OAI26, §3.5, Prop. 8]): `wt(v) mod 4 ∈ {1, 3}` read as `±1`, negated on a
decreasing edge. -/
noncomputable def epsC {h : ℕ} (e : Vertex .complex h × Vertex .complex h) (v : Pt h) : ℤ :=
  (open Classical in if labC e.1 ≤ labC e.2 then 1 else -1) * (if wt v % 4 = 1 then 1 else -1)

/-- `k`-fold tensor power of an operator (one factor per column). -/
def tpow {ι : Type*} [Fintype ι] (k : ℕ) (A : Matrix ι ι ℂ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  fun x y => ∏ c, A (x c) (y c)

/-- The `2 × 2` kernel `C = HSH = aI + bX`, indexed by `𝔽₂`. -/
noncomputable def C2 : Matrix (ZMod 2) (ZMod 2) ℂ := fun i j => if i = j then ka else kb

/-- `C^{⊗m}` on `𝔽₂^m`. -/
noncomputable def Cfull {h : ℕ} : Matrix (Pt h) (Pt h) ℂ := fun x y => ∏ p, C2 (x p) (y p)

/-- `u_a = t_{a₁} ⊗ t_{a₂} ⊗ t_{a₃} ∈ 𝔽₂^m` (weight 27). -/
def ua {h : ℕ} (a : Addr h) : Pt h := fun p => ind a.1 p.1 * ind a.2.1 p.2.1 * ind a.2.2 p.2.2

/-- `Z_{a,k}`: `Z = diag(1, −1)` on the coordinates of `supp u_a` in each of `k` columns. -/
noncomputable def Zk {h : ℕ} (k : ℕ) (u : Pt h) : Matrix (Fin k → Pt h) (Fin k → Pt h) ℂ :=
  Matrix.diagonal fun x => ∏ c, (-1 : ℂ) ^ (dotC u (x c)).val

/-! ### Contracts: [OAI26] Lemma 6 (complex part) and [OAI26] Prop. 8 at `h = 100` (stated as `Prop`s) -/

/-- CONTRACT. [OAI26, §3.3, Lemma 6] (last part), `h = 100`: the residual of every edge of
the complex network has an orthonormal basis. -/
def Lemma6OnbStmt : Prop :=
  ∀ (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100), e ∈ edges w →
    ∃ B, IsONB (residC e) B

/-- CONTRACT (C2). [OAI26, §3.5, Prop. 8], `h = 100`: for every edge and
every orthonormal basis `B` of its residual, `C_V C_U⁻¹ = Π_{v ∈ B} K_v^{±1}`, i.e.
`C_V = (Π_{v∈B} K(v, ε_v)) · C_U`. -/
def Prop8EdgeStmt : Prop :=
  ∀ (w : Role .complex 100) (e : Vertex .complex 100 × Vertex .complex 100), e ∈ edges w →
    ∀ B : List (Pt 100), IsONB (residC e) B →
    frameC e.2 = (B.map fun v => Kv v (epsC e v)).prod * frameC e.1

/- The residual count `prop8_count` (C4) is in `CellCalc.lean`. -/

/-- CONTRACT (C3, trivial routes). [OAI26, §3.5, Prop. 8], `h = 100`: the zero label has frame `I` and the
full label has frame `C^{⊗m}` (`q_𝓕(x) = wt x`); hence every route other than `X_a → Y_a` is
`±C^{⊗m}`. -/
def Prop8ZeroFullStmt : Prop :=
  ∀ w : Role .complex 100,
    ((∀ a, w ≠ .X a) → frameC (.source w) = 1) ∧ ((∀ a, w ≠ .Y a) → frameC (.sink w) = Cfull)

/-- CONTRACT (C3). [OAI26, §3.5, Prop. 8] (endpoint corrections), `h = 100`, any
number `k ≥ 1` of columns: on the route `X_a → Y_a`, `i^{27k} Z_{a,k} C_{U_a^⊥} C_{U_a}^{-1} Z_{a,k}`
equals `C^{⊗mk}`. -/
def Prop8EndpointStmt : Prop :=
  ∀ (a : Addr 100) (k : ℕ), 1 ≤ k →
    (Complex.I ^ (27 * k)) • (Zk k (ua a) * tpow k (frameC (.sink (.Y a))) *
      (tpow k (frameC (.source (.X a))))⁻¹ * Zk k (ua a)) = tpow k Cfull

/-- CONTRACT (columns). Tensor powers are multiplicative: the `k`-column version of every frame
identity follows ([OAI26, §3.5, Prop. 8]). -/
def TpowMulStmt : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) (A B : Matrix ι ι ℂ),
    tpow k (A * B) = tpow k A * tpow k B

end SubNLogN.Math.Networks
