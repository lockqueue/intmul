import SubNLogN.Math.Bridge.Fnew
import IntMul.MaterializedAndComputable.ComputableTranscendentals

/-!
# Bridge: the concrete certified table family `TabConcrete` (definitions for machine evaluation)

Lemma 4.6 (bridge Lemma C)(iii) (`lem:bridge-C`, Lemma B.3 (`lem:phase-tables`)), realised with IntMul's certified evaluators
(`IntMul/MaterializedAndComputable/ComputableTranscendentals.lean`):
* the carrier phase `e^{-πi(s+a/A)/t} = e(-(sA+a)/(2tA))` uses `computableStdCharWithProgramCost`.
  The angle is reduced exactly modulo 1 first. Error `2·complexQuantizeMaxErr B` on the scale
  `2^{-(B+2)}`.
* `sinc(s+a/A)·e^{-π(s+a/A)²/α²}` with `α = alphaSchedule ω = alphaDefault ω` uses
  `computableSincGaussianTapWithProgramCost` at the mirrored point `-(s+a/A)`. The kernel is even.
  Error `2^{-pSub}`.
* `c_0, c_1` at `y = (2u+1)/(2t)` use `computableC0C1WithProgramCost ω pC (2t) (2u+1)`, where
  `c0Coeff = G(y)` and `c1Coeff = G(1-y) = G(y-1)`. Error `2^{-(pC+2)}`.

Precisions: sample precision `B = pSub = q + g + 6` with `g = ⌈lg(2P+2)⌉ + 12` (paper: `b = q + g`,
error `2^{-b-4}`), and `pC = q + 4` (paper: `b = q + 1`, error `2^{-b-4} = 2^{-q-5}`).

The stored entries (current interface: the rounding-parametric `tapConcreteR`, `muConcreteR`,
`ahatConcreteR`, `gamConcreteR`, `TabConcreteR`, nearest rounding `rr`; the `Quant_q` versions
`tapConcrete`, …, `TabConcrete` are legacy specializations retained for compatibility) are:
* tap: one nearest rounding `rnd_q` of the exact residue-class sum of evaluated samples, so taps
  with no sample are exactly `0` (`rnd_q 0 = 0` for every nearest rounding);
* `μ̂ = rnd_q(1/ĉ_max)` and `â = max(0, rnd_q(ĉ_min/ĉ_max))`, each an exact division followed by
  one nearest rounding;
* `γ̂ = closureFixedR rr q Q â A_h`.

The orientation is exact: `c_0 > c_1 ⟺ 2u < t`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost
open scoped BigOperators

/-- Tap guard `g = ⌈lg(2P+2)⌉ + 12` (Lemma B.3 (`lem:phase-tables`)). -/
def tapGuard (P : ℕ) : ℕ := lg (2 * P + 2) + 12

/-- Sample precision `B = pSub = q + g + 6` (`q = P + 2`). -/
def tapPrec (P : ℕ) : ℕ := P + 2 + tapGuard P + 6

/-- Precision of the `c_0, c_1` evaluator, `pC = q + 4`. -/
def coeffPrec (P : ℕ) : ℕ := P + 2 + 4

/-- Evaluated carrier phase `e(-(sA+a)/(2tA))`. The angle is reduced exactly to
`n/(2tA)` with `n = (-(sA+a)) mod 2tA`, then evaluated by IntMul's certified `stdChar` evaluator on the
scale `2^{-(B+2)}`. -/
noncomputable def phaseHat (B t A a : ℕ) (s : ℤ) : ℂ :=
  IntMul.toScaledComplex B
    (IntMul.computableStdCharWithProgramCost B
      ((-(s * (A : ℤ) + (a : ℤ))) % ((2 * t * A : ℕ) : ℤ)).toNat (2 * t * A) false).1

/-- Evaluated `sinc(s+a/A)·e^{-π(s+a/A)²/α²}`, `α = alphaSchedule ω`, via IntMul's certified tap
evaluator at the mirrored point `((pSub - s) - pSub) - a/A = -(s + a/A)`, on the scale `2^{-pSub}`. -/
noncomputable def sincGaussHat (ω pSub A a : ℕ) (s : ℤ) : ℂ :=
  ((((IntMul.computableSincGaussianTapWithProgramCost ω pSub A a ((pSub : ℤ) - s).toNat).1 : ℤ) : ℝ) /
    (2 : ℝ) ^ pSub : ℝ)

/-- Concrete stored tap of shift `a/A` at offset `e`: one `Quant_q` of the exact residue-class sum
of the evaluated samples `phaseHat · sincGaussHat` over `s ∈ [-P, P]`, `s ≡ e (mod t)`. -/
noncomputable def tapConcrete (ω P t A a : ℕ) (e : ℤ) : ℂ :=
  quantC (P + 2) (∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    if s % (t : ℤ) = e % (t : ℤ) then
      phaseHat (tapPrec P) t A a s * sincGaussHat ω (tapPrec P) A a s else 0)

/-- Evaluated `ĉ_0 ≈ G((u+½)/t)`. -/
noncomputable def c0Hat (ω P t u : ℕ) : ℝ :=
  (IntMul.toScaledComplex (coeffPrec P)
    (IntMul.computableC0C1WithProgramCost ω (coeffPrec P) (2 * t) (2 * u + 1)).1.1).re

/-- Evaluated `ĉ_1 ≈ G((u+½)/t - 1)`. -/
noncomputable def c1Hat (ω P t u : ℕ) : ℝ :=
  (IntMul.toScaledComplex (coeffPrec P)
    (IntMul.computableC0C1WithProgramCost ω (coeffPrec P) (2 * t) (2 * u + 1)).1.2).re

/-- `μ̂ = Quant_q(1/ĉ_max)`, with exact orientation `ĉ_max = ĉ_0 ⟺ 2u < t`. -/
noncomputable def muConcrete (ω P t u : ℕ) : ℝ :=
  quantR (P + 2) (if 2 * u < t then (c0Hat ω P t u)⁻¹ else (c1Hat ω P t u)⁻¹)

/-- `â = max(0, Quant_q(ĉ_min/ĉ_max))`. -/
noncomputable def ahatConcrete (ω P t u : ℕ) : ℝ :=
  max 0 (quantR (P + 2)
    (if 2 * u < t then c1Hat ω P t u / c0Hat ω P t u else c0Hat ω P t u / c1Hat ω P t u))

/-- `γ̂ = closureFixed q Q â A_h` with `Q = closurePrec q A_h t_h`. -/
noncomputable def gamConcrete (ω P t A u : ℕ) : ℝ :=
  closureFixed (P + 2) (closurePrec (P + 2) A t) (ahatConcrete ω P t u) A

/-- The concrete table family at `(p0, K0)`, with `ω = schedOmega p0 K0 d`, `P = schedP p0 K0`,
shape `fnewShape ρ K0`, and `A_h = prefixProd t i`. -/
noncomputable def TabConcrete (ρ : RowExps) (p0 K0 : ℕ) : BridgeTables (fnewShape ρ K0) where
  tap := fun i a e =>
    tapConcrete (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i)
      (prefixProd (fnewShape ρ K0) i) a e
  mu := fun i u => muConcrete (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i) u
  ahat := fun i u =>
    ahatConcrete (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i) u
  gam := fun i u =>
    gamConcrete (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i)
      (prefixProd (fnewShape ρ K0) i) u

/-! ## Parametric-rounding versions (nearest-rounding parameter `rr`)

Each `…R` definition is the definition of the same name without `R`, with the nearest rounding a
parameter `rr` (leading argument; see `Components.lean`). The `quantC`/`quantR` definitions above
(`tapConcrete`, `muConcrete`, `ahatConcrete`, `gamConcrete`, `TabConcrete`) are legacy specializations, kept
for compatibility with existing dependents. -/

/-- `tapConcrete` with rounding `crnd rr (P + 2)` of the exact residue-class sum. -/
noncomputable def tapConcreteR (rr : ℕ → ℝ → ℝ) (ω P t A a : ℕ) (e : ℤ) : ℂ :=
  crnd rr (P + 2) (∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    if s % (t : ℤ) = e % (t : ℤ) then
      phaseHat (tapPrec P) t A a s * sincGaussHat ω (tapPrec P) A a s else 0)

/-- `μ̂ = rr_q(1/ĉ_max)`, with exact orientation `ĉ_max = ĉ_0 ⟺ 2u < t`. -/
noncomputable def muConcreteR (rr : ℕ → ℝ → ℝ) (ω P t u : ℕ) : ℝ :=
  rr (P + 2) (if 2 * u < t then (c0Hat ω P t u)⁻¹ else (c1Hat ω P t u)⁻¹)

/-- `â = max(0, rr_q(ĉ_min/ĉ_max))`. -/
noncomputable def ahatConcreteR (rr : ℕ → ℝ → ℝ) (ω P t u : ℕ) : ℝ :=
  max 0 (rr (P + 2)
    (if 2 * u < t then c1Hat ω P t u / c0Hat ω P t u else c0Hat ω P t u / c1Hat ω P t u))

/-- `γ̂ = closureFixedR rr q Q â A_h` with `Q = closurePrec q A_h t_h`. -/
noncomputable def gamConcreteR (rr : ℕ → ℝ → ℝ) (ω P t A u : ℕ) : ℝ :=
  closureFixedR rr (P + 2) (closurePrec (P + 2) A t) (ahatConcreteR rr ω P t u) A

/-- The concrete table family at `(p0, K0)` for the nearest rounding `rr`, with
`ω = schedOmega p0 K0 d`, `P = schedP p0 K0`, shape `fnewShape ρ K0`, and `A_h = prefixProd t i`. -/
noncomputable def TabConcreteR (rr : ℕ → ℝ → ℝ) (ρ : RowExps) (p0 K0 : ℕ) :
    BridgeTables (fnewShape ρ K0) where
  tap := fun i a e =>
    tapConcreteR rr (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i)
      (prefixProd (fnewShape ρ K0) i) a e
  mu := fun i u =>
    muConcreteR rr (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i) u
  ahat := fun i u =>
    ahatConcreteR rr (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i) u
  gam := fun i u =>
    gamConcreteR rr (schedOmega p0 K0 (fnewD ρ K0 + 1)) (schedP p0 K0) (fnewShape ρ K0 i)
      (prefixProd (fnewShape ρ K0) i) u

/-- CONTRACT (Lemma 4.6 (bridge Lemma C)(iii) for the concrete family, `lem:bridge-C`, Lemma B.3 (`lem:phase-tables`)): for
every nearest rounding `rr` (`IsNearestRounding rr`) and under `WalshOK ρ p0 K0`,
`TabConcreteR rr ρ p0 K0` satisfies the table certification `TablesCertifiedR rr` of Theorem 4.7 at
`α = alphaDefault (schedOmega p0 K0 d)` and `P = schedP p0 K0`.
Route: IntMul evaluator specs (`computableStdCharWithProgramCost_error_le`,
`computableSincGaussianTapWithProgramCost_spec`, `computableC0C1WithProgramCost_spec`), then
`LemmaC_iii_tapStmt` and `LemmaC_iii_solverStmt` (with `u_S = 0`), `kernelG_eq_gHatBox`, and the
evenness and periodicity of `stdChar` and `sincGaussian`. -/
def TabConcrete_certifiedStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ (ρ : RowExps) (p0 K0 : ℕ), WalshOK ρ p0 K0 = true →
    TablesCertifiedR rr (alphaDefault (schedOmega p0 K0 (fnewD ρ K0 + 1))) (schedP p0 K0)
      (fnewShape ρ K0) (TabConcreteR rr ρ p0 K0)

end SubNLogN.Math.Bridge
