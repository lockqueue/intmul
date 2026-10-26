import Mathlib
import SubNLogN.Math.Cost.Params

/-!
# Cost: the `κ = 2^{-46}` Walsh row as exact rationals

Paper: Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`), row `C₁ = 14` and its margins,
together with Section 7.4 (`sec:main-gaps`), eq. (`eq:gaps`).

With `ξ = 2^{-42}`: `C₁ = 14`, `ε = 1/15`, `β = 1/64`, `c = ξ/256`, `τ = 1 - 4ξ`, `σ = 1 - ξ`,
`λ = 1 - 63ξ/64`, `λ' = 1 - 31ξ/32`, `κ = ξ/16 = 2^{-46}`, and the gaps
`g_pre = 1 - ε(1+c)`, `g_lay = ε(1-λ')`, `g_last = ε`, `g_axis = (1-ε)(1-τ)`, `g_short = 1 - ε`.
The network constant `ν = 11` is the certified value of Proposition A.2 (`prop:deficits`) and eq. (`eq:walsh-guard-constants`), taken here as a number.

Everything is a statement about explicit rationals (checked by `norm_num`); the link to the
exponents of `row46 : RowExps` is `row46_eps_eq` / `row46_c_eq`.

Theorems tagged CONTRACT are the contract statements; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost.Row46

/-- `ξ = 2^{-42}` (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`)). -/
def xi : ℚ := 1 / 2 ^ 42

/-- Guard exponent `C₁ = 14` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def C1 : ℕ := 14

/-- Network constant `ν = 11` (Proposition A.2 (`prop:deficits`), eq. (`eq:walsh-guard-constants`), certified there; used only in `C₁ ≥ ν + 3`). -/
def nu : ℕ := 11

/-- Dimension exponent `ε = 1/15` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def eps : ℚ := 1 / 15

/-- Leaf exponent `β = 1/64` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def beta : ℚ := 1 / 64

/-- Chunk exponent `c = ξ/256` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def c : ℚ := xi / 256

/-- Interchange exponent `τ = 1 - 4ξ` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def tau : ℚ := 1 - 4 * xi

/-- Complex-network exponent `σ = 1 - ξ` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def sigma : ℚ := 1 - xi

/-- `λ = 1 - 63ξ/64` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def lam : ℚ := 1 - 63 * xi / 64

/-- `λ' = 1 - 31ξ/32` (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`)). -/
def lam' : ℚ := 1 - 31 * xi / 32

/-- The target exponent `κ = ξ/16` (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`)). -/
def kappa : ℚ := xi / 16

/-- Prefix-round gap `g_pre = 1 - ε(1+c)` (Section 7.4, eq. (`eq:gaps`)). -/
def gPre : ℚ := 1 - eps * (1 + c)

/-- Butterfly-layer gap `g_lay = ε(1-λ')` (Section 7.4, eq. (`eq:gaps`)). -/
def gLay : ℚ := eps * (1 - lam')

/-- Last-axis gap `g_last = ε` (Section 7.4, eq. (`eq:gaps`)). -/
def gLast : ℚ := eps

/-- Axis-exposure gap `g_axis = (1-ε)(1-τ)` (Section 7.4, eq. (`eq:gaps`)). -/
def gAxis : ℚ := (1 - eps) * (1 - tau)

/-- Spreading/solver gap `g_short = 1 - ε` (Section 7.4, eq. (`eq:gaps`)). -/
def gShort : ℚ := 1 - eps

/-- `g_min`, the least of the five Walsh-route gaps (Section 7.4 (`sec:main-gaps`), eq. (`eq:gaps`)). -/
def gMin : ℚ := min (min (min (min gPre gLay) gLast) gAxis) gShort

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`)): `κ = ξ/16 = 2^{-46}`. -/
theorem kappa_eq : kappa = 1 / 2 ^ 46 := by
  norm_num [kappa, xi]

/-- CONTRACT (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`), Schedule.lean): `c = ξ/256 = 2^{-50}`. -/
theorem c_eq : c = 1 / 2 ^ 50 := by
  norm_num [c, xi]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`)): `g_lay = ε(1-λ') = 31ξ/480`. -/
theorem gLay_eq : gLay = 31 * xi / 480 := by
  norm_num [gLay, eps, lam', xi]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`)): `g_axis = (1-ε)(1-τ) = 56ξ/15`. -/
theorem gAxis_eq : gAxis = 56 * xi / 15 := by
  norm_num [gAxis, eps, tau, xi]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`)): `g_last = 1/15`. -/
theorem gLast_eq : gLast = 1 / 15 := by
  norm_num [gLast, eps]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`), "`g_pre, g_short > 0.9`"). -/
theorem gPre_gShort_gt : 9 / 10 < gPre ∧ 9 / 10 < gShort := by
  norm_num [gPre, gShort, eps, c, xi]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`), "the binding gap is the butterfly-layer gap"): `g_min = g_lay`. -/
theorem gMin_eq : gMin = gLay := by
  have h1 : gLay ≤ gPre := by norm_num [gLay, gPre, eps, lam', c, xi]
  have h2 : gLay ≤ gLast := by norm_num [gLay, gLast, eps, lam', xi]
  have h3 : gLay ≤ gAxis := by norm_num [gLay, gAxis, eps, lam', tau, xi]
  have h4 : gLay ≤ gShort := by norm_num [gLay, gShort, eps, lam', xi]
  rw [gMin, min_eq_right h1, min_eq_left h2, min_eq_left h3, min_eq_left h4]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`)): the slack is `g_min - κ = ξ/480`. -/
theorem slack_eq : gMin - kappa = xi / 480 := by
  rw [gMin_eq]; norm_num [gLay, kappa, eps, lam', xi]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), Table 6 (`tab:walsh-rows`), "the ratios `g_min/κ` are ... `31/30`"): `g_min / κ = 31/30`. -/
theorem gMin_div_kappa : gMin / kappa = 31 / 30 := by
  rw [gMin_eq]; norm_num [gLay, kappa, eps, lam', xi]

/-- CONTRACT (Section 7.4 (`sec:main-gaps`), eq. (`eq:gaps`), "a row gives `κ` whenever `0 < κ < g_min`"): `0 < κ` and `κ` is below each
of the five gaps and below `1` (the gap of the root-packing and linear terms). -/
theorem kappa_lt_gaps :
    0 < kappa ∧ kappa < gPre ∧ kappa < gLay ∧ kappa < gLast ∧ kappa < gAxis ∧
      kappa < gShort ∧ kappa < 1 := by
  norm_num [kappa, gPre, gLay, gLast, gAxis, gShort, eps, lam', tau, c, xi]

/-- CONTRACT (ranges required by Proposition A.11 (`prop:prop14-param`)): `0 < τ < 1`, `0 ≤ σ < 1`, `0 < β < 1`,
`c > 0`, `0 < ε < 1`. -/
theorem ranges :
    0 < tau ∧ tau < 1 ∧ 0 ≤ sigma ∧ sigma < 1 ∧ 0 < beta ∧ beta < 1 ∧ 0 < c ∧
      0 < eps ∧ eps < 1 := by
  norm_num [tau, sigma, beta, c, eps, xi]

/-- CONTRACT (Proposition A.11 (`prop:prop14-param`), eq. (`eq:walsh-layer-a`)): `max{τ, σ} < λ < 1` and `τ(1 + c/β) < λ`. -/
theorem layer_a : max tau sigma < lam ∧ lam < 1 ∧ tau * (1 + c / beta) < lam := by
  refine ⟨max_lt ?_ ?_, ?_, ?_⟩ <;> norm_num [tau, sigma, lam, c, beta, xi]

/-- CONTRACT (Proposition A.11 (`prop:prop14-param`), eq. (`eq:walsh-layer-b`)): `max{λ, σ + β(1-σ)} < λ' < 1`. -/
theorem layer_b : max lam (sigma + beta * (1 - sigma)) < lam' ∧ lam' < 1 := by
  refine ⟨max_lt ?_ ?_, ?_⟩ <;> norm_num [lam, sigma, beta, lam', xi]

/-- CONTRACT (Proposition A.11 (`prop:prop14-param`), guard admissibility): `ε C₁ < 1` and `C₁ ≥ ν + 3`. -/
theorem guard_ok : eps * C1 < 1 ∧ nu + 3 ≤ C1 := by
  refine ⟨?_, ?_⟩
  · norm_num [eps, C1]
  · decide

/-- CONTRACT (Section 7.5 (`sec:main-rows`)): `τ(1 + c/β) = (1-4ξ)(1+ξ/4) = 1 - (15/4)ξ - ξ²`. -/
theorem tau_mul_eq : tau * (1 + c / beta) = 1 - 15 / 4 * xi - xi ^ 2 := by
  norm_num [tau, c, beta, xi]

/-- CONTRACT (Section 7.5 (`sec:main-rows`), the strict margins of the `κ = 2^{-46}` row):
`λ - σ = ξ/64`, `λ - τ(1+c/β) = (177/64)ξ + ξ²`, `λ' - λ = ξ/64`, `1 - εC₁ = 1/15`, and
`σ + β(1-σ) = λ`. -/
theorem margins :
    lam - sigma = xi / 64 ∧ lam - tau * (1 + c / beta) = 177 / 64 * xi + xi ^ 2 ∧
      lam' - lam = xi / 64 ∧ 1 - eps * C1 = 1 / 15 ∧ sigma + beta * (1 - sigma) = lam := by
  norm_num [lam, sigma, tau, c, beta, lam', eps, C1, xi]

/-- CONTRACT (Section 7.4 (`sec:main-gaps`), "and `ε(1+c) < 1`"). -/
theorem eps_mul_one_add_c_lt_one : eps * (1 + c) < 1 := by
  norm_num [eps, c, xi]

/-- CONTRACT (Section 7.4 (`sec:main-gaps`) and Proposition A.11 (`prop:prop14-param`), the source of `κ`): `λ' > σ + β(1-σ)` and `εC₁ < 1` give
`g_lay < (1-β)(1-σ)/C₁`. -/
theorem gLay_lt_bound : gLay < (1 - beta) * (1 - sigma) / C1 := by
  norm_num [gLay, beta, sigma, C1, eps, lam', xi]

/-- CONTRACT (link to `Params.lean`): the real exponent `ε` of `row46` is `Row46.eps`. -/
theorem row46_eps_eq : row46.eps = ((eps : ℚ) : ℝ) := by
  rw [row46_eps]; norm_num [eps]

/-- CONTRACT (link to `Params.lean`): the real exponent `c` of `row46` is `Row46.c`. -/
theorem row46_c_eq : row46.c = ((c : ℚ) : ℝ) := by
  rw [row46_c]; norm_num [c, xi]

end SubNLogN.Math.Cost.Row46
