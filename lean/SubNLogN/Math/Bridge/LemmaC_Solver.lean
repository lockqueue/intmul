import SubNLogN.Math.Bridge.Components

/-!
# Bridge: Lemma 4.6 (`lem:bridge-C`)(iv)–(vi), two-pass cyclic sweep and closure (`LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(iv) (`lem:bridge-C`). Assume `v ≤ 1/(64t)` and the tables
satisfy `|μ̂ - c_max^{-1}| ≤ v`, `|â - a'| ≤ v`, `â ≥ 0` and `|γ̂ - (1-â^L)^{-1}| ≤ v`, where
`c_max = max(c_0,c_1)` and `a' = min(c_0,c_1)/c_max` for the frequency digit `u < t`. Then for
every even cycle length `L`, the two-pass sweep (orientation `c_0 > c_1 ⟺ u < t/2`) returns `Ẑ`
with `‖Ẑ - B^{-1}Y‖_∞ ≤ 32 t² v max(1, ‖Y‖_∞)`. All its states (prefix states, closure value,
second-pass states) have modulus less than `7t max(1, ‖Y‖_∞)`.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def LemmaC_ivStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ (P ω : ℕ) (α : ℝ) (_hC : LemmaCParams P ω α) (t : ℕ) (_ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (u : ℕ) (_hu : u < t) (_hv : gridUnit (P + 2) ≤ 1 / (64 * (t : ℝ))) (mu ahat gam : ℝ) (L : ℕ) (_hL : Even L) (_hL0 : 0 < L) (_hmu : |mu - (max (kernelG α ((u + 1 / 2) / t)) (kernelG α ((u + 1 / 2) / t - 1)))⁻¹| ≤ gridUnit (P + 2)) (_ha : |ahat - min (kernelG α ((u + 1 / 2) / t)) (kernelG α ((u + 1 / 2) / t - 1)) / max (kernelG α ((u + 1 / 2) / t)) (kernelG α ((u + 1 / 2) / t - 1))| ≤ gridUnit (P + 2)) (_ha0 : 0 ≤ ahat) (_hgam : |gam - (1 - ahat ^ L)⁻¹| ≤ gridUnit (P + 2)) (Y : Fin L → ℂ),
    let c0 : ℂ := (kernelG α ((u + 1 / 2) / t) : ℂ)
    let c1 : ℂ := (kernelG α ((u + 1 / 2) / t - 1) : ℂ)
    let fwd : Bool := decide (2 * u < t)
    let Yn : ℕ → ℂ := if fwd then extNat Y else reorientIn L (extNat Y)
    let b : ℕ → ℂ := fun j => crnd rr (P + 2) ((mu : ℂ) * Yn j)
    (∀ j : Fin L, ‖cycSweepR rr fwd (P + 2) mu ahat gam L (extNat Y) j -
        Matrix.mulVec (cycBidiag c0 c1 L)⁻¹ Y j‖ ≤
          32 * (t : ℝ) ^ 2 * gridUnit (P + 2) * max 1 ‖Y‖) ∧
      (∀ n < L, ‖sweepPrefixR rr (P + 2) ahat b 0 n‖ < 7 * (t : ℝ) * max 1 ‖Y‖) ∧
      (∀ n < L, ‖cycSweepFwdR rr (P + 2) mu ahat gam L Yn n‖ < 7 * (t : ℝ) * max 1 ‖Y‖)

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(v) (`lem:bridge-C`): assume `v ≤ 1/(64t)`, `â` satisfies the
conditions of (iv), and `L` is even. Then `γ̂` computed with `Q = closurePrec q L t` satisfies the
hypothesis of (iv), `|γ̂ - (1-â^L)^{-1}| ≤ v`. (The bit-size claim is tape-level.)
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def LemmaC_vStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ (P ω : ℕ) (α : ℝ) (_hC : LemmaCParams P ω α) (t : ℕ) (_ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (u : ℕ) (_hu : u < t) (_hv : gridUnit (P + 2) ≤ 1 / (64 * (t : ℝ))) (ahat : ℝ) (L : ℕ) (_hL : Even L) (_hL0 : 0 < L) (_ha : |ahat - min (kernelG α ((u + 1 / 2) / t)) (kernelG α ((u + 1 / 2) / t - 1)) / max (kernelG α ((u + 1 / 2) / t)) (kernelG α ((u + 1 / 2) / t - 1))| ≤ gridUnit (P + 2)) (_ha0 : 0 ≤ ahat),
    |closureFixedR rr (P + 2) (closurePrec (P + 2) L t) ahat L - (1 - ahat ^ L)⁻¹| ≤
      gridUnit (P + 2)

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(vi) (`lem:bridge-C`, = Lemma 4.4 (bridge Lemma B)(vi)):
`‖(B_2⋯B_d)^{-1}‖_∞ ≤ D = R/t_1`. -/
def LemmaC_viStmt : Prop :=
  ∀ {d : ℕ} (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (hd : 1 ≤ d),
    opNormInf (Matrix.toLin' (truncProd α t)⁻¹) ≤ (totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)

end SubNLogN.Math.Bridge
