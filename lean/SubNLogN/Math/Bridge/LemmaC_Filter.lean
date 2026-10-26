import SubNLogN.Math.Bridge.Components

/-!
# Bridge: Lemma 4.6 (`lem:bridge-C`)(i), filter norms and the spatial tail (`LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(i) (`lem:bridge-C`): for every `δ ∈ [0,1)`, over one period
`‖H^{(h)}_δ‖_2 ≤ 1` and `‖H^{(h)}_δ‖_1 ≤ √t`. -/
def LemmaC_i_normsStmt : Prop :=
  ∀ (P ω : ℕ) (α : ℝ) (_hC : LemmaCParams P ω α) (t : ℕ) (_ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (δ : ℝ) (_hδ : 0 ≤ δ ∧ δ < 1),
    l2Norm (fun e : Fin t => foldedFilter α t δ ((e : ℕ) : ℤ)) ≤ 1 ∧
      l1Norm (fun e : Fin t => foldedFilter α t δ ((e : ℕ) : ℤ)) ≤ Real.sqrt t

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(i) (`lem:bridge-C`): truncating the unfolded kernel to
`|e| ≤ P` leaves a spatial tail `∑_{|e|>P} |g_h(e+δ)| < 0.10·2^{-P}` (`= 0.40 v`). -/
def LemmaC_i_tailStmt : Prop :=
  ∀ (P ω : ℕ) (α : ℝ) (_hC : LemmaCParams P ω α) (t : ℕ) (_ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (δ : ℝ) (_hδ : 0 ≤ δ ∧ δ < 1),
    (∑' e : ℤ, if (P : ℤ) < |e| then ‖carrier α t ((e : ℝ) + δ)‖ else 0) <
      0.10 * (2 : ℝ) ^ (-(P : ℤ))

end SubNLogN.Math.Bridge
