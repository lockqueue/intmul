/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchMath
import SubNLogN.Math.Bridge.Proofs.SpreadPartial

/-!
# BM-SP (`Machine/Pipe/BranchMathSpread.lean`): widths of the partial spreads

Proves the contract `Bridge_spreadPart_widthsStmt` of `Machine/Pipe/BranchMath.lean`:
`bridge_spreadPart_widths : Bridge_spreadPart_widthsStmt`, unconditional.

`spreadPart q t T V n` (`Machine/Contracts/Bridge.lean`) is by definition the fold of
`spreadAxisFixedR roundHalfUpR q t i (T.tap i)` over `(spreadOrder d).take n`, so the contract is
`Math.Bridge.SpreadPartial.spreadPrefix_fitsWidth` (`Math/Bridge/Proofs/SpreadPartial.lean`) at the
machine rounding `roundHalfUpR` (`isNearestRounding_roundHalfUpR`). That lemma is the spreading
part of the proof of Theorem 4.7 (`thm:bridge-precision`) run on the prefix list: every
computed partial spread of `x' ∘ encIn` is on the `q`-grid with `‖·‖_∞ ≤ 1/16 + 1/16 = 1/8`, hence
fits component width `q + 2`, `q = schedP p k + 2` (Table 4 (`tab:widths`)).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

/-- **Widths of the partial spreads** (`Bridge_spreadPart_widthsStmt`; Theorem 4.7 (`thm:bridge-precision`),
Table 4 (`tab:widths`)), unconditional: every entry of `spreadPart (q) t T (x' ∘ encIn) n` has component width
`q + 2` on the `q`-grid, `q = schedP p k + 2`, for every `n`. -/
theorem bridge_spreadPart_widths : Bridge_spreadPart_widthsStmt := by
  intro d t k ℓ p hshape hp x hx hxn T hT n j
  exact SubNLogN.Math.Bridge.SpreadPartial.spreadPrefix_fitsWidth roundHalfUpR
    isNearestRounding_roundHalfUpR t k ℓ p hshape hp x hx hxn T hT n j

end SubNLogN.Machine.Pipe
