import SubNLogN.Math.Bridge.LemmaC_Filter

/-!
# Bridge: Lemma 4.6 (`lem:bridge-C`)(ii), one fixed-point spreading stage (`LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- CONTRACT, Lemma 4.6 (bridge Lemma C)(ii) (`lem:bridge-C`): for a `q`-grid array `z` with
`‖z‖_∞ ≤ 1`, one fixed-point spreading stage maps `z` to a `q`-grid array within `4(P+1)v` of
`S_h z`. (Packing/blocking claims are tape-level, see `spread_slot_bound`.)
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def LemmaC_iiStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ {d : ℕ} (P ω : ℕ) (α : ℝ) (_hC : LemmaCParams P ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (i : Fin d) (_hi : (i : ℕ) ≠ 0) (tap : ℕ → ℤ → ℂ) (_htap : TapsCertified α P t i tap) (z : Idx t → ℂ) (_hz : ∀ j, OnGrid (P + 2) (z j)) (_hzn : ‖z‖ ≤ 1),
    (∀ k, OnGrid (P + 2) (spreadAxisFixedR rr (P + 2) t i tap z k)) ∧
      ‖spreadAxisFixedR rr (P + 2) t i tap z - spreadAxis α t i z‖ ≤
        4 * ((P : ℝ) + 1) * gridUnit (P + 2)

/-- CONTRACT (proof of Lemma 4.6 (`lem:bridge-C`)(ii)): slot non-overflow of the signed Kronecker packing,
`16(2P+1) 2^{2q} < 2^{4P+15}` with `q = P + 2`. -/
def Spread_slot_boundStmt : Prop :=
  ∀ (P : ℕ),
    16 * (2 * P + 1) * 2 ^ (2 * (P + 2)) < 2 ^ (4 * P + 15)

end SubNLogN.Math.Bridge
