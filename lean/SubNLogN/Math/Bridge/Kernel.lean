import SubNLogN.Math.Common.DFT
import IntMul.Theorem3BidiagonalAndSchedule

/-!
# Bridge: kernel `G`, negative half-bin carrier, folded filter

Paper: Definition 4.1 (`def:carrier`). Reuse: `IntMul.sincGaussian` (`= sinc(s) e^{-πs²/α²}`,
normalized sinc), `IntMul.gHatBox`, `IntMul.realErfScaled` (`erf(√π α z)`),
`IntMul.fourier_sincGaussian_eq_gHatBox`, `IntMul.sincGaussian_modulated_poisson_summation`.

Standing assumptions of Section 4 (`sec:bridge`, Definition 4.1 (`def:carrier`)): alias width `ω ≥ 8`, `α` admissible.
Contracts are `def …Stmt : Prop` (CONTRACT docstrings); proofs `theorem … : …Stmt` live in
`SubNLogN/Math/Bridge/Proofs/`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators FourierTransform

/-- The default Gaussian parameter `α = 2√(ω ln 2 / π)` (lower end of eq. (`eq:alpha`),
Definition 4.1 (`def:carrier`)); definitionally `IntMul.alphaSchedule ω`. -/
noncomputable abbrev alphaDefault (ω : ℕ) : ℝ := IntMul.alphaSchedule ω

/-- Eq. (`eq:alpha`) (Definition 4.1 (`def:carrier`)): `2√(ω ln2/π) ≤ α ≤ 4√(ω ln2/π)`. -/
def AlphaAdmissible (ω : ℕ) (α : ℝ) : Prop :=
  2 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ≤ α ∧
    α ≤ 4 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi)

/-- `G(ξ) = ∫_{ξ-1/2}^{ξ+1/2} α e^{-πα²v²} dv` (Definition 4.1 (`def:carrier`), eq. (`eq:G`)). -/
noncomputable def kernelG (α ξ : ℝ) : ℝ :=
  ∫ v in (ξ - 1 / 2)..(ξ + 1 / 2), α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2))

/-- The negative half-bin carrier `g_h(s) = e^{-πis/t_h} sinc(s) e^{-πs²/α²}` (Definition 4.1 (`def:carrier`),
eq. (`eq:carrier`)), with `t = t_h`; `e^{-πis/t} = e(-s/(2t))`. -/
noncomputable def carrier (α : ℝ) (t : ℕ) (s : ℝ) : ℂ :=
  IntMul.stdChar (-(s / (2 * (t : ℝ)))) * (IntMul.sincGaussian α s : ℂ)

/-- The folded filter `H^{(h)}_δ(e) = ∑_{s ∈ e + t_hℤ} g_h(s + δ)` (Definition 4.1 (`def:carrier`),
eq. (`eq:folded`)), as a function of `e ∈ ℤ` (it is `t`-periodic). -/
noncomputable def foldedFilter (α : ℝ) (t : ℕ) (δ : ℝ) (e : ℤ) : ℂ :=
  ∑' m : ℤ, carrier α t ((e : ℝ) + (m : ℝ) * (t : ℝ) + δ)

/-- The truncated folded filter: only unfolded samples `s` with `|s| ≤ P` are kept
(Lemma 4.6 (bridge Lemma C)(i),(iii), Lemma B.3 (`lem:phase-tables`)):
`∑_{s ∈ [-P,P], s ≡ e (mod t)} g_h(s + δ)`. -/
noncomputable def truncFoldedFilter (α : ℝ) (t P : ℕ) (δ : ℝ) (e : ℤ) : ℂ :=
  ∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    if s % (t : ℤ) = e % (t : ℤ) then carrier α t ((s : ℝ) + δ) else 0

/-! ## Contracts -/

/-- CONTRACT (Definition 4.1 (`def:carrier`), eq. (`eq:G`)): `G(ξ) = ½[erf(a(ξ+½)) - erf(a(ξ-½))]`, `a = √π α`,
i.e. `kernelG α = IntMul.gHatBox (IntMul.realErfScaled α)`. Reuse:
`IntMul.theorem3_concrete_box_gaussian_integral_and_telescoping` plus substitution. -/
def KernelG_eq_gHatBoxStmt : Prop :=
  ∀ (α ξ : ℝ) (_hα : 0 < α),
    kernelG α ξ = IntMul.gHatBox (IntMul.realErfScaled α) ξ

/-- CONTRACT (Definition 4.1 (`def:carrier`), eq. (`eq:G`)): the Fourier transform `f̂(ξ) = ∫ f(s) e^{-2πiξs} ds` of
`sinc(s) e^{-πs²/α²}` is `G(ξ)`. Reuse: `IntMul.fourier_sincGaussian_eq_gHatBox`. -/
def Fourier_sincGaussian_eq_kernelGStmt : Prop :=
  ∀ (α ξ : ℝ) (_hα : 0 < α),
    (𝓕 fun s : ℝ => (IntMul.sincGaussian α s : ℂ)) ξ = (kernelG α ξ : ℂ)

/-- CONTRACT (Definition 4.1 (`def:carrier`), eq. (`eq:carrier`)): `ĝ_h(ξ) = G(ξ + 1/(2t_h))`. -/
def Fourier_carrierStmt : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α) (t : ℕ) (_ht : 0 < t) (ξ : ℝ),
    (𝓕 fun s : ℝ => carrier α t s) ξ = (kernelG α (ξ + 1 / (2 * (t : ℝ))) : ℂ)

/-- CONTRACT (Section 4.1, eq. (`eq:negacyclic`)): with `g_0(s) = sinc(s)e^{-πs²/α²}`,
`H_δ(e) = e^{-πi(e+δ)/t} ∑_{s ∈ e+tℤ} (-1)^{(e-s)/t} g_0(s+δ)`; writing `s = e + m t`,
`(-1)^{(e-s)/t} = (-1)^m`. -/
def FoldedFilter_negacyclicStmt : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α) (t : ℕ) (_ht : 0 < t) (δ : ℝ) (e : ℤ),
    foldedFilter α t δ e =
      IntMul.stdChar (-(((e : ℝ) + δ) / (2 * (t : ℝ)))) *
        ∑' m : ℤ, ((-1 : ℂ) ^ m) * (IntMul.sincGaussian α ((e : ℝ) + (m : ℝ) * (t : ℝ) + δ) : ℂ)

/-- CONTRACT (proof of Lemma 4.4 (`lem:bridge-B`)(i)): the intervals `[ξ-m-½, ξ-m+½]` tile `ℝ`,
so `∑_m G(ξ - m) = 1`. -/
def HasSum_kernelG_shiftStmt : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α) (ξ : ℝ),
    HasSum (fun m : ℤ => kernelG α (ξ - m)) 1

/-- CONTRACT (Lemma 4.4 (`lem:bridge-B`)(i)): all alias weights are positive, `G(ξ) > 0`. -/
def KernelG_posStmt : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α) (ξ : ℝ),
    0 < kernelG α ξ

/-- CONTRACT (Lemma 4.4 (`lem:bridge-B`)(iii)): `G` is even. -/
def KernelG_negStmt : Prop :=
  ∀ (α ξ : ℝ),
    kernelG α (-ξ) = kernelG α ξ

/-- CONTRACT (Lemma 4.4 (`lem:bridge-B`)(iii)): `G` is strictly decreasing on `[0, ∞)`. -/
def KernelG_strictAntiOnStmt : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α),
    StrictAntiOn (kernelG α) (Set.Ici 0)

/-- CONTRACT (eq. (`eq:poisson`) in Lemma 4.2 (`lem:bridge-A`), specialized to the carrier): for real `z, ξ`,
`∑_{e∈ℤ} g_h(z - e) e^{2πieξ} = ∑_{m∈ℤ} ĝ_h(ξ - m) e^{2πiz(ξ-m)}`, with `ĝ_h(η) = G(η + 1/(2t))`.
Reuse: `IntMul.sincGaussian_modulated_poisson_summation` at `ξ + 1/(2t)`. -/
def Carrier_poissonStmt : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α) (t : ℕ) (_ht : 0 < t) (z ξ : ℝ),
    (∑' e : ℤ, carrier α t (z - (e : ℝ)) * IntMul.stdChar ((e : ℝ) * ξ)) =
      ∑' m : ℤ, (kernelG α (ξ - (m : ℝ) + 1 / (2 * (t : ℝ))) : ℂ) *
        IntMul.stdChar (z * (ξ - (m : ℝ)))

end SubNLogN.Math.Bridge
