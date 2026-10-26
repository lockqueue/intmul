import SubNLogN.Math.Bridge.Algorithm
import SubNLogN.Math.Bridge.LemmaB_Ops
import SubNLogN.Math.Bridge.LemmaC_Spread
import SubNLogN.Math.Bridge.LemmaC_Tables
import SubNLogN.Math.Bridge.LemmaC_Solver

/-!
# Bridge: Theorem 4.7, the precision contract (`thm:bridge-precision`, Table 4 (`tab:widths`))
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}


/-- CONTRACT (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:bridge-total`)): `√2/8 + 2^{-12} + 2^{-23} = 0.17702096… < 0.177021`
(checkable with `√2 < 1.4142136`). -/
def Bridge_constant_ltStmt : Prop :=
    Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ) < 0.177021

/-- CONTRACT, master margin (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:master-margin`)): for
`p ≥ max(8,k)` and `1 ≤ d ≤ k`, `2^{14} d (P+1) R³ v ≤ 2^{-p-12}` with `P = schedP p k`, `R = 2^k`,
`v = 2^{-(P+2)}`. -/
def Master_marginStmt : Prop :=
  ∀ (p k d : ℕ) (_hp : max 8 k ≤ p) (_hd1 : 1 ≤ d) (_hdk : d ≤ k),
    (2 : ℝ) ^ 14 * (d : ℝ) * ((schedP p k : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 3 *
        gridUnit (schedP p k + 2) ≤ (2 : ℝ) ^ (-((p : ℤ) + 12))

/-- CONTRACT, Theorem 4.7 (`thm:bridge-precision`). Assume:
* the balanced shape;
* `p ≥ max(8,k)`, and `x` on the `(p+2)`-grid with `‖x‖_∞ ≤ 2^p`;
* the schedule `ω, P, q` of eq. (`eq:schedule`) and `α = 2√(ω ln2/π)`;
* tables certified to `v = 2^{-q}` (complex taps to `2v`), with closures computed at the stated `Q`.

Then for every middle transform at precision `q` (Definition 4.5) the bridge returns `F̂_R x` on the
`(p+2)`-grid with `‖F̂_R x - F_R x‖_∞ < (√2/8 + 2^{-12} + 2^{-23}) 2^{-p} X`, `X = max(1,‖x‖_∞)`.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def Bridge_precisionStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (_hshape : BalancedShape t k ℓ) (_hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (_hx : ∀ j, OnGrid (p + 2) (x j)) (_hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t) (_hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T) (Emid : ℝ) (δmid : ℕ) (run : (Idx t → ℂ) → (Idx t → ℂ)) (_hmid : IsMiddleTransform t (schedP p k) Emid δmid run),
    (∀ f, OnGrid (p + 2) (bridgeFixedR rr p (schedP p k) t T run x f)) ∧
      ‖bridgeFixedR rr p (schedP p k) t T run x - dft (totalLen t) x‖ <
        (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) *
          max 1 ‖x‖

/-- CONTRACT, Theorem 4.7 "more precisely", arithmetic part (`thm:bridge-precision`):
the arithmetic error before the final rounding is at most `2^{-p-12} X`.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def Bridge_arith_errorStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (_hshape : BalancedShape t k ℓ) (_hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (_hx : ∀ j, OnGrid (p + 2) (x j)) (_hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t) (_hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T) (Emid : ℝ) (δmid : ℕ) (run : (Idx t → ℂ) → (Idx t → ℂ)) (_hmid : IsMiddleTransform t (schedP p k) Emid δmid run),
    ‖bridgePreR rr (schedP p k) t T run x - bridgeExactScaled (alphaDefault (schedOmega p k d)) t x‖ ≤
      (2 : ℝ) ^ (-((p : ℤ) + 12)) * max 1 ‖x‖

/-- CONTRACT, Theorem 4.7 "more precisely", alias part (`thm:bridge-precision`):
the alias error is below `2^{-p-23} X`. -/
def Bridge_alias_errorStmt : Prop :=
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (_hshape : BalancedShape t k ℓ) (_hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (_hx : ∀ j, OnGrid (p + 2) (x j)) (_hxn : ‖x‖ ≤ (2 : ℝ) ^ p),
    ‖bridgeExactScaled (alphaDefault (schedOmega p k d)) t x - dft (totalLen t) x‖ <
      (2 : ℝ) ^ (-((p : ℤ) + 23)) * max 1 ‖x‖

/-- CONTRACT, Theorem 4.7 "more precisely", output part (`thm:bridge-precision`): the
final rounding contributes at most `(√2/8) 2^{-p}`.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def Bridge_round_errorStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ {d : ℕ} (p P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (run : (Idx t → ℂ) → (Idx t → ℂ)) (x : Fin (totalLen t) → ℂ),
    ‖bridgeFixedR rr p P t T run x - bridgePreR rr P t T run x‖ ≤ Real.sqrt 2 / 8 * (2 : ℝ) ^ (-(p : ℤ))

/-- CONTRACT (proof of Theorem 4.7 (`thm:bridge-precision`)): the pre-scaled input is exact on the `q`-grid, and the
completed spread array lies on the `q`-grid with `‖U‖_∞ ≤ 1/8`, so it is an admissible input of
Definition 4.5.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def Bridge_spread_admissibleStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (_hshape : BalancedShape t k ℓ) (_hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (_hx : ∀ j, OnGrid (p + 2) (x j)) (_hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t) (_hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T),
    (∀ j, OnGrid (schedP p k + 2) (preScaled t x j)) ∧
      (∀ j, OnGrid (schedP p k + 2) (spreadStageR rr (schedP p k) t T x j)) ∧
      ‖spreadStageR rr (schedP p k) t T x‖ ≤ 1 / 8

/-- CONTRACT (Table 4 (`tab:widths`), value-level rows). With
`q = P + 2`:
* the normalized input and the completed spread array have component width `q + 2`;
* every partial deconvolution output has component width `q + k + 6`.

The remaining rows (packing slots, layer internals, closure precision) are covered by
`spread_slot_bound`, the direct-FFT bounds, and `lemmaC_v`.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def Bridge_widthsStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (_hshape : BalancedShape t k ℓ) (_hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (_hx : ∀ j, OnGrid (p + 2) (x j)) (_hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t) (_hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T) (Emid : ℝ) (δmid : ℕ) (run : (Idx t → ℂ) → (Idx t → ℂ)) (_hmid : IsMiddleTransform t (schedP p k) Emid δmid run),
    (∀ j, FitsWidth (schedP p k + 2) (schedP p k + 4) (preScaled t x j)) ∧
      (∀ j, FitsWidth (schedP p k + 2) (schedP p k + 4) (spreadStageR rr (schedP p k) t T x j)) ∧
      ∀ m : ℕ, ∀ f, FitsWidth (schedP p k + 2) (schedP p k + 2 + k + 6)
        (((deconvOrder d).take m).foldl (fun Z i => deconvAxisFixedR rr (schedP p k + 2) t T i Z)
          (fun f' => run (spreadStageR rr (schedP p k) t T x) ((encFreq t).symm f')) f)

end SubNLogN.Math.Bridge
