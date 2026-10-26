import SubNLogN.Math.Bridge.Components

/-!
# Bridge: Lemma 4.6 (`lem:bridge-C`)(iii) and Lemma B.3 (`lem:phase-tables`), value-level table entries (`LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(iii) taps (Lemma B.3 (`lem:phase-tables`)): with `g = ⌈lg(2P+2)⌉ + 12` and
sample approximations within `2^{-(q+g)-4}`, one nearest rounding of their exact residue-class sum
is within `(2P+1)2^{-q-g-4} + (√2/2)v < 0.71 v` of the truncated folded tap.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def LemmaC_iii_tapStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ (P ω : ℕ) (α : ℝ) (_hC : LemmaCParams P ω α) (t : ℕ) (_ht : 0 < t) (δ : ℝ) (e : ℤ) (ghat : ℤ → ℂ) (_hg : ∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), ‖ghat s - carrier α t ((s : ℝ) + δ)‖ ≤ (2 : ℝ) ^ (-((P + 2 + (lg (2 * P + 2) + 12) + 4 : ℕ) : ℤ))),
    ‖crnd rr (P + 2) (∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
        if s % (t : ℤ) = e % (t : ℤ) then ghat s else 0) - truncFoldedFilter α t P δ e‖ <
      0.71 * gridUnit (P + 2)

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(iii) solver entries (Lemma B.3 (`lem:phase-tables`)): with `b = q + 1`, if
`ĉ_0, ĉ_1` are within `2^{-b-4}` of `c_0, c_1 ≥ 0`, `c_max > 0.49999999`, the orientation is exact,
and `μ'`, `a''` are within `u_S ≤ 2^{-2b-64}` of `1/ĉ_max`, `ĉ_min/ĉ_max`, then
`μ̂ = rr_q(μ')` and `â = max(0, rr_q(a''))` satisfy `|μ̂ - c_max^{-1}| < v` and
`|â - a'| < v`, where `a' = c_min/c_max`.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def LemmaC_iii_solverStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ (q : ℕ) (c0 c1 c0h c1h μ' a'' uS : ℝ) (_hc0 : 0 ≤ c0) (_hc1 : 0 ≤ c1) (_hmax : (0.49999999 : ℝ) < max c0 c1) (_hne : c0 ≠ c1) (_h0 : |c0h - c0| ≤ (2 : ℝ) ^ (-(((q + 1) + 4 : ℕ) : ℤ))) (_h1 : |c1h - c1| ≤ (2 : ℝ) ^ (-(((q + 1) + 4 : ℕ) : ℤ))) (_huS : 0 ≤ uS ∧ uS ≤ (2 : ℝ) ^ (-((2 * (q + 1) + 64 : ℕ) : ℤ))) (_hμ : |μ' - (if c1 < c0 then c0h else c1h)⁻¹| ≤ uS) (_ha : |a'' - (if c1 < c0 then c1h / c0h else c0h / c1h)| ≤ uS),
    |rr q μ' - (max c0 c1)⁻¹| < gridUnit q ∧
      |max 0 (rr q a'') - min c0 c1 / max c0 c1| < gridUnit q

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(iii) phases (Lemma B.3 (`lem:phase-tables`)): if `|e_0 - e| < v/16` for a
unit phase `e`, then `ê = Q_q((1 - v/8) e_0)` is disk valued, `|ê| ≤ 1`, and `|ê - e| < 2v`. -/
def LemmaC_iii_phaseStmt : Prop :=
  ∀ (q : ℕ) (_hq : 8 ≤ q) (eph e0 : ℂ) (_he : ‖eph‖ = 1) (_h0 : ‖e0 - eph‖ < gridUnit q / 16),
    ‖truncC q ((1 - (gridUnit q : ℂ) / 8) * e0)‖ ≤ 1 ∧
      ‖truncC q ((1 - (gridUnit q : ℂ) / 8) * e0) - eph‖ < 2 * gridUnit q

/-- CONTRACT (Lemma B.3 (`lem:phase-tables`)): multiplying a disk operand by a stored phase and
truncating does not increase its modulus and adds less than `(2+√2)v < 4v`. -/
def LemmaC_iii_phase_mulStmt : Prop :=
  ∀ (q : ℕ) (z eh eph : ℂ) (_hz : ‖z‖ ≤ 1) (_heh : ‖eh‖ ≤ 1) (_heph : ‖eph‖ = 1) (_h : ‖eh - eph‖ < 2 * gridUnit q),
    ‖truncC q (eh * z)‖ ≤ ‖z‖ ∧ ‖truncC q (eh * z) - eph * z‖ < 4 * gridUnit q

end SubNLogN.Math.Bridge
