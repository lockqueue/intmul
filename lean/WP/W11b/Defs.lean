import WP.W11b.Basic

/-!
# WP.W11b.Defs — the node invariant and the width profiles

* `NodeInv spec p_in x`: the input of a node of the quantized schedule `spec` has the node size and
  dequantizes (at input precision `p_in`) to magnitudes `≤ 2^spec.p`. This is the hypothesis of the
  snapshot's `allCallSitesWidthSound_of_faithful` (CSWS:1787), and it propagates down the chain
  (`norm_qPost_of_faithful_le_two_pow_pChild`, FTP:1096).
* `reqW cSpec p_in`: the working width a chain needs at every level (a `max` over the levels).
* `specW spec`: the schedule-side bound that dominates `reqW` on faithful hierarchies.
* `wdHead n`, `wRHead n`: the headline width profiles (functions of the bit length `n` only).
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- Node invariant: size and magnitude of a node input. -/
def NodeInv (spec : QuantizedFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ)) : Prop :=
  x.size = spec.size ∧ ∀ k < spec.size, ‖toScaledComplex p_in (read1D x k)‖ ≤ (2 : ℝ) ^ spec.p

/-- Width needed by a chain with input precision `p_in` (max over its levels). -/
def reqW : ComputablePaperFastDFTSpec → ℕ → ℕ
  | .basePow2 p K _, p_in => max (p + p_in + 3) (4 * (2 * p + K + 8))
  | .step p pSub _ _ _ _ _ _ _ _ child, p_in =>
      max (max (p + p_in + 3) (3 * pSub + 3)) (reqW child pSub)

/-- Schedule-side width: the max over the levels of `pSub = 2·pChild p K` and `q_leaf`. -/
def specW : QuantizedFastDFTSpec → ℕ
  | .base p R => 2 * p + Nat.log2 R + 8
  | .step p K _ _ _ _ child => max (2 * pChild p K) (specW child)

/-- Headline working width of every level (forward and inverse transform). -/
def wdHead (n : ℕ) : ℕ :=
  2 * IntMulTM.Contracts.W8.hP0 n + 3 + 4 * specW (IntMulTM.Contracts.W8.hSpec n)

/-- Headline root width. -/
def wRHead (n : ℕ) : ℕ := 4 * IntMulTM.Contracts.W8.hP0 n

end WP.W11b
