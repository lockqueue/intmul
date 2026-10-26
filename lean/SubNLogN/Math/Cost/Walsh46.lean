import Mathlib
import SubNLogN.Math.Cost.Asymptotics
import SubNLogN.Math.Cost.Row46
import SubNLogN.Math.Cost.Abstract
import SubNLogN.Math.Cost.WalshCore

/-!
# Cost: the Walsh-route cost bound and the `κ = 2^{-46}` headline cost

Paper: Section 7 (`sec:main`): eq. (`eq:root-cost`), eq. (`eq:setup`), Table 5 (`tab:cost-walsh`),
eq. (`eq:cost-W`) in Section 7.3, eq. (`eq:gaps`) in Section 7.4, Table 6 (`tab:walsh-rows`) in Section 7.5,
and the cost part of the proof of Theorem 1 (`thm:main`) in Section 7.6 (`sec:main-thm`).

* Five adapters turn the normalized costs of Table 5 into powers of `P`, using the bands of
  Lemma 7.1 (`Asymptotics.lean`):
  `dK ≤ P^{ε(1+c)}`, `ℓd^λ ≤ P^{1-ε(1-λ)}`, `ℓ m(P) ≤ |A_m| P^{1-ε} (lg 2P)^{j_m}`,
  `d(1 + ℓ^τ) ≤ 2P^{1-(1-ε)(1-τ)}`, `d(m(P) + m(P²)) ≤ |A_m|(1 + 2^{j_m}) P^ε (lg 2P)^{j_m}`,
  where `m(N) ≤ A_m (lg 2N)^{j_m}` is the multiplication-cost envelope of the independent multiplier (per bit) (Section 7.3 (`sec:main-tables`):
  `m(N) = (lg N)^{O(1)}` suffices on the Walsh route).
* `walshCost ρ λ' τ m D_set n` is the paper's cost expression
  `RP[dK + ℓd^{λ'} + ℓ m(P) + d(1+ℓ^τ) + d(m(P)+m(P²))] + RP·m(P) + n + (R/r)P^D + rP^D + P^D`
  (two bridge calls, root packing with `R·M(P) = RP·m(P)`, setup; the `O(·)` constants are one
  factor `A`).
* `headlineCost_walsh`: if `T n ≤ A · walshCost ρ λ' τ m D_set n` above a cutoff, for an
  admissible row whose gaps `ε(1-λ')`, `(1-ε)(1-τ)`, `ε` exceed `2^{-46}`, then
  `HeadlineCost (monoEnv T) C N` for some `C, N`.
* `headlineCost_walsh46`: the instance for the `κ = 2^{-46}` row (`row46`, `λ' = 1 - 31ξ/32`,
  `τ = 1 - 4ξ`).

The adapters and the two headline theorems are the `(bOf n, kOf n)` instances of the
family-generic statements of `WalshCore.lean` (pointwise adapters `*_of_bandsK`,
`headlineCost_walshBK`, `headlineCost_walsh46BK`), using `paper_famFacts : FamFacts bOf kOf`
(`AsymSizes.lean`) and `walshCost_eq_walshCostBK` (definitional).

This file proves no machine bound: `T` is an arbitrary function, and the hypothesis
`T n ≤ A · walshCost …` is what a machine-level cost analysis must supply.
-/

namespace SubNLogN.Math.Cost

open Filter
open SubNLogN.S5 (HeadlineCost)

variable {ρ : RowExps}

/-- Helper (not a paper statement): `2 ≤ P` for every `n` (indeed `P ≥ 256`). -/
private lemma two_le_POf (n : ℕ) : 2 ≤ POf n := by
  unfold POf
  omega

/-! ## The normalized costs of Table 5 as powers of `P` -/

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 1, prefix butterfly rounds `dK`, gap `g_pre = 1 - ε(1+c)`):
eventually `dK ≤ P^{ε(1+c)}`. -/
theorem eventually_prefix_le (hρ : ρ.Admissible) :
    ∀ᶠ n in atTop, (dOf ρ n : ℝ) * KOf ρ n ≤ (POf n : ℝ) ^ (ρ.eps * (1 + ρ.c)) := by
  filter_upwards [eventually_bands_P hρ] with n hB
  exact prefix_le_of_bandsK hρ hB

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 2, butterfly layers and both positional maps `ℓd^{λ'}`, gap
`g_lay = ε(1-λ')`): for `0 ≤ λ ≤ 1`, eventually `ℓ d^λ ≤ P^{1-ε(1-λ)}`. -/
theorem eventually_layer_le (hρ : ρ.Admissible) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∀ᶠ n in atTop, (lOf ρ n : ℝ) * (dOf ρ n : ℝ) ^ lam ≤ (POf n : ℝ) ^ (1 - ρ.eps * (1 - lam)) := by
  filter_upwards [eventually_bands_P hρ, (tendsto_dOf hρ).eventually_ge_atTop 2] with n hB hd2
  exact layer_le_of_bandsK lam h0 h1 hB hd2 (two_le_POf n)

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 3, complex twiddles and last-axis FFT `ℓ m(P)`, gap
`g_last = ε` up to logarithms): if `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`, then eventually
`ℓ m(P) ≤ |A_m| P^{1-ε} (lg 2P)^{j_m}`. -/
theorem eventually_last_le (hρ : ρ.Admissible) (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm) :
    ∀ᶠ n in atTop, (lOf ρ n : ℝ) * m (POf n) ≤
      |Am| * (POf n : ℝ) ^ (1 - ρ.eps) * Real.logb 2 (2 * POf n) ^ jm := by
  filter_upwards [eventually_bands_P hρ, (tendsto_dOf hρ).eventually_ge_atTop 2] with n hB hd2
  exact last_le_of_bandsK m Am jm hm hB hd2 (two_le_POf n)

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 4, axis exposures and restorations `d(1 + ℓ^τ)`, gap
`g_axis = (1-ε)(1-τ)`): for `0 ≤ τ ≤ 1`, eventually `d(1 + ℓ^τ) ≤ 2 P^{1-(1-ε)(1-τ)}`. -/
theorem eventually_axis_le (hρ : ρ.Admissible) (tau : ℝ) (h0 : 0 ≤ tau) (h1 : tau ≤ 1) :
    ∀ᶠ n in atTop, (dOf ρ n : ℝ) * (1 + (lOf ρ n : ℝ) ^ tau) ≤
      2 * (POf n : ℝ) ^ (1 - (1 - ρ.eps) * (1 - tau)) := by
  filter_upwards [eventually_bands_P hρ, (tendsto_dOf hρ).eventually_ge_atTop 2] with n hB hd2
  exact axis_le_of_bandsK hρ tau h0 h1 hB hd2 (two_le_POf n)

/-- CONTRACT (Table 5 (`tab:cost-walsh`) row 5, spreading and cyclic solves `d(m(P) + m(P²))`, gap
`g_short = 1 - ε` up to logarithms): if `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`, then eventually
`d(m(P) + m(P²)) ≤ |A_m| (1 + 2^{j_m}) P^ε (lg 2P)^{j_m}`. -/
theorem eventually_short_le (hρ : ρ.Admissible) (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm) :
    ∀ᶠ n in atTop, (dOf ρ n : ℝ) * (m (POf n) + m (POf n ^ 2)) ≤
      |Am| * (1 + 2 ^ jm) * (POf n : ℝ) ^ ρ.eps * Real.logb 2 (2 * POf n) ^ jm := by
  filter_upwards [eventually_bands_P hρ] with n hB
  exact short_le_of_bandsK m Am jm hm hB (two_le_POf n)

/-! ## The Walsh-route cost expression and the headline cost -/

/-- The Walsh-route cost expression at input length `n` (Section 7.2, eq. (`eq:root-cost`) with
`R·M(P) = RP·m(P)`, Section 7.3, eq. (`eq:cost-W`), Section 7.3, eq. (`eq:setup`)), for a row `ρ`, layer exponent
`λ'`, interchange exponent `τ`, multiplication-cost envelope `m` (per bit) and setup degree `D_set`:
`RP·[dK + ℓd^{λ'} + ℓ·m(P) + d(1 + ℓ^τ) + d(m(P) + m(P²))] + RP·m(P) + n
  + (R/r)P^{D_set} + r·P^{D_set} + P^{D_set}` (real powers `d^{λ'}`, `ℓ^τ`). -/
noncomputable def walshCost (ρ : RowExps) (lam' tau : ℝ) (m : ℕ → ℝ) (Dset n : ℕ) : ℝ :=
  (VOf n : ℝ) * ((dOf ρ n : ℝ) * KOf ρ n + (lOf ρ n : ℝ) * (dOf ρ n : ℝ) ^ lam'
      + (lOf ρ n : ℝ) * m (POf n) + (dOf ρ n : ℝ) * (1 + (lOf ρ n : ℝ) ^ tau)
      + (dOf ρ n : ℝ) * (m (POf n) + m (POf n ^ 2)))
    + (VOf n : ℝ) * m (POf n) + n
    + (((ROf n / rOf ρ n : ℕ) : ℝ) * (POf n : ℝ) ^ Dset + (rOf ρ n : ℝ) * (POf n : ℝ) ^ Dset
      + (POf n : ℝ) ^ Dset)

/-- `walshCost` is `walshCostBK` (`WalshCore.lean`) at the paper's root parameters
`(bOf n, kOf n)` (definitional). -/
theorem walshCost_eq_walshCostBK (ρ : RowExps) (lam' tau : ℝ) (m : ℕ → ℝ) (Dset n : ℕ) :
    walshCost ρ lam' tau m Dset n = walshCostBK ρ lam' tau m Dset (bOf n) (kOf n) n := rfl

/-- CONTRACT (cost part of the proof of Theorem 1 (`thm:main`), Section 7.6 (`sec:main-thm`), for any admissible row with the needed gaps).
Let `ρ` be admissible, `0 ≤ λ' ≤ 1`, `0 ≤ τ ≤ 1`, with `2^{-46} < ε(1-λ')`,
`2^{-46} < (1-ε)(1-τ)` and `2^{-46} < ε` (the gaps `g_pre`, `g_short` and the root-packing gap `1`
exceed `2^{-46}` automatically). Let `m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`, `0 ≤ A`, and
`T n ≤ A · walshCost ρ λ' τ m D_set n` for all `n ≥ N₀`. Then `HeadlineCost (monoEnv T) C N` for
some natural `C, N`. -/
theorem headlineCost_walsh (ρ : RowExps) (hρ : ρ.Admissible) (lam' tau : ℝ)
    (hlam'0 : 0 ≤ lam') (hlam'1 : lam' ≤ 1) (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    (hgLay : ((2 : ℝ) ^ 46)⁻¹ < ρ.eps * (1 - lam'))
    (hgAxis : ((2 : ℝ) ^ 46)⁻¹ < (1 - ρ.eps) * (1 - tau))
    (hgLast : ((2 : ℝ) ^ 46)⁻¹ < ρ.eps)
    (T : ℕ → ℕ) (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm)
    (A : ℝ) (hA : 0 ≤ A) (Dset N₀ : ℕ)
    (hT : ∀ n ≥ N₀, (T n : ℝ) ≤ A * walshCost ρ lam' tau m Dset n) :
    ∃ C N : ℕ, HeadlineCost (monoEnv T) C N := by
  exact headlineCost_walshBK bOf kOf paper_famFacts ρ hρ lam' tau hlam'0 hlam'1 htau0 htau1
    hgLay hgAxis hgLast T m Am jm hm A hA Dset N₀ hT

/-- CONTRACT (Theorem 1 (`thm:main`), cost conclusion at `κ = 2^{-46}`, Section 7.6 (`sec:main-thm`), proof of Theorem 1 (`thm:main`)): for the
`C₁ = 14` row (`ε = 1/15`, `c = 2^{-50}`, `λ' = 1 - 31ξ/32`, `τ = 1 - 4ξ`, `ξ = 2^{-42}`), if
`m N ≤ A_m (lg 2N)^{j_m}` for all `N ≥ 2`, `0 ≤ A`, and
`T n ≤ A · walshCost row46 λ' τ m D_set n` for all `n ≥ N₀`, then
`HeadlineCost (monoEnv T) C N` for some natural `C, N`. -/
theorem headlineCost_walsh46 (T : ℕ → ℕ) (m : ℕ → ℝ) (Am : ℝ) (jm : ℕ)
    (hm : ∀ N : ℕ, 2 ≤ N → m N ≤ Am * Real.logb 2 (2 * N) ^ jm)
    (A : ℝ) (hA : 0 ≤ A) (Dset N₀ : ℕ)
    (hT : ∀ n ≥ N₀, (T n : ℝ) ≤
      A * walshCost row46 ((Row46.lam' : ℚ) : ℝ) ((Row46.tau : ℚ) : ℝ) m Dset n) :
    ∃ C N : ℕ, HeadlineCost (monoEnv T) C N := by
  exact headlineCost_walsh46BK bOf kOf paper_famFacts T m Am jm hm A hA Dset N₀ hT

end SubNLogN.Math.Cost
