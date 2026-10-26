import SubNLogN.Math.Bridge.Algorithm

/-!
# Bridge: the deconvolution-chain contract (proof of Theorem 4.7 (`thm:bridge-precision`))

Shared interface: proved in `Proofs/Precision_Deconv.lean` (`deconv_chain_of`), consumed by
`bridge_arith_error_of` (Theorem 4.7, arithmetic part).
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

/-- CONTRACT, deconvolution chain (proof of Theorem 4.7 (`thm:bridge-precision`)). Let
`v = 2^{-(P+2)}` with `64 v ∑_{h≥2} t_h ≤ 1`. The fixed-point solvers `B_2^{-1}, …, B_d^{-1}`
(applied in this order by `deconvFixedR rr`, for any nearest rounding `rr`, each a two-pass cyclic
sweep per cycle, Lemma 4.6 (bridge Lemma C)(iv))
approximate `(B_2⋯B_d)^{-1} Y` with
`‖deconvFixedR rr Y - (B_2⋯B_d)^{-1} Y‖_∞ ≤ 64 D v (∑_{h≥2} t_h) max(1, ‖Y‖_∞)`, `D = ∏_{h≥2} t_h`.
(The paper states the case `‖Y‖_∞ ≤ 1`; the condition `v ≤ 1/(64 t_h)` of Lemma 4.6 (bridge Lemma C)(iv) follows
from the sum condition.) -/
def Deconv_chainStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ) (_hrr : IsNearestRounding rr) {d : ℕ} (P ω : ℕ) (α : ℝ) (_hC : LemmaCParams P ω α) (t : Fin d → ℕ) (_ht : ShapeOK t)
    (T : BridgeTables t) (_hT : TablesCertifiedR rr α P t T)
    (_hsum : 64 * gridUnit (P + 2) *
      (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) ≤ 1)
    (Y : Fin (totalLen t) → ℂ),
    ‖deconvFixedR rr (P + 2) t T Y - Matrix.mulVec (truncProd α t)⁻¹ Y‖ ≤
      64 * (dimD t : ℝ) * gridUnit (P + 2) *
        (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) * max 1 ‖Y‖

end SubNLogN.Math.Bridge
