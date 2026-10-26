import Mathlib
import SubNLogN.Spec

/-!
# Networks, part 6: the real deficit link (Proposition A.2 (`prop:deficits`))

Proposition A.2 (`prop:deficits`) and [OAI26, §3.6, (10)]: from the exact
deficits `η = (Wm − s)/(Wm)` and a certified bound `L ≥ ln m`, `m^{1−u} > m(1 − Lu) ≥ m(1 − η) = s/W`
whenever `η ≥ L u`. The integer comparisons `η_b 2^{40} ≥ 14`, `η_c 2^{42} ≥ 14` are already in
`SubNLogN/S1/Params.lean` (`bit_deficit_tau_40`, `complex_deficit_sigma_42`); what is missing there
is the real-analytic step and `ln 10⁶ < 14`.
-/

namespace SubNLogN.Math.Networks

/-- CONTRACT. Proposition A.2 (`prop:deficits`): `ln 10⁶ < 14` (from `e⁷ > 10³`). -/
def LogMLt14Stmt : Prop := Real.log (tripleM 100 : ℝ) < 14

/-- CONTRACT. The deficit test (Proposition A.2 (`prop:deficits`), eq. (`eq:deficit-test`)): if `m > 1`, `W > 0`,
`ln m ≤ L`, `u > 0` and `L u ≤ η = (Wm − s)/(Wm)`, then `s/W < m^{1−u}`. -/
def DeficitTestStmt : Prop :=
  ∀ s W m L u : ℝ, 1 < m → 0 < W → Real.log m ≤ L → 0 < u →
    L * u ≤ (W * m - s) / (W * m) → s / W < m ^ (1 - u)

/-- CONTRACT (Proposition A.2 (`prop:deficits`)). At `h = 100`:
`s_b/W_b < m^{1−2^{−40}}` and `s_c/W_c < m^{1−2^{−42}}`, so `τ = 1 − 2^{−40}` and `σ = 1 − 2^{−42}` are
admissible in Proposition A.11 (`prop:prop14-param`). -/
def DeficitsH100Stmt : Prop :=
    (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 40) ∧
    (tripleSc 100 : ℝ) / tripleWc 100 < (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 42)

/-- CONTRACT ([OAI26, §3.6, (10)], Proposition A.2 (`prop:deficits`)). The printed exponent `1 − 2^{−50}` is admissible
for both networks at `h = 100`. -/
def DeficitsPrintedH100Stmt : Prop :=
    (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 50) ∧
    (tripleSc 100 : ℝ) / tripleWc 100 < (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 50)

end SubNLogN.Math.Networks
