import SubNLogN.Math.Bridge.Operators

/-!
# Bridge: Lemma 4.4 (`lem:bridge-B`), scalar parts

The omitted-alias weight, the passband `c_max` and the separation `|c_0 - c_1|`. These are real
analysis of `G` (erf/erfc bounds). Reuse: `IntMul.gHatBox`/`IntMul.realErfScaled` lemmas in
`IntMul/Theorem3BidiagonalAndSchedule.lean`. The constants are tight at `ω = 8`. (Names `LemmaB*`/`lemmaB*` reflect an earlier draft (bridge Lemma B), kept for stability.)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(ii) scalar core (`lem:bridge-B`): for every sample `y ∈ (0,1)`, the
omitted weight `Ψ(y) = 1 - G(y) - G(y-1) = ½erfc(a(y+½)) + ½erfc(a(3/2-y))` satisfies
`Ψ(y) < 0.120·2^{-ω}`; this bounds the row sums of `A_h - B_h`. -/
def Omitted_weight_ltStmt : Prop :=
  ∀ (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (y : ℝ) (_hy : 0 < y ∧ y < 1),
    1 - kernelG α y - kernelG α (y - 1) < 0.120 * (2 : ℝ) ^ (-(ω : ℤ))

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(iii) (`lem:bridge-B`): passband, for every frequency digit `u < t`,
`c_max = max(c_0,c_1) ≥ 1/2 - 0.060·2^{-4ω} > 0.49999999`, `c_0 = G(y)`, `c_1 = G(y-1)`,
`y = (u+1/2)/t`. -/
def LemmaB_iiiStmt : Prop :=
  ∀ (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : ℕ) (_ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (u : ℕ) (_hu : u < t),
    (1 / 2 : ℝ) - 0.060 * (2 : ℝ) ^ (-(4 * (ω : ℤ))) ≤
        max (kernelG α ((u + 1 / 2) / t)) (kernelG α ((u + 1 / 2) / t - 1)) ∧
      (0.49999999 : ℝ) < (1 / 2 : ℝ) - 0.060 * (2 : ℝ) ^ (-(4 * (ω : ℤ)))

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(iv) (`lem:bridge-B`): separation `|c_0 - c_1| ≥ 7/(4t)`. -/
def LemmaB_ivStmt : Prop :=
  ∀ (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : ℕ) (_ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (u : ℕ) (_hu : u < t),
    7 / (4 * (t : ℝ)) ≤ |kernelG α ((u + 1 / 2) / t) - kernelG α ((u + 1 / 2) / t - 1)|

end SubNLogN.Math.Bridge
