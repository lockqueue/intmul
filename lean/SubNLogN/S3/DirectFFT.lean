import SubNLogN.Spec

/-!
# Component S3 (`DirectFFT.lean`): Finite `Fin 7` Unshuffle Witness & Per-Level Error Margin Check

**Scope.** Proves the `Fin 7` non-commutativity/unshuffle witness of Remark 6.4 (`rem:walsh-unshuffle`, named `remark74_*` from an earlier draft) and the closed numeral inequality `2 * (2 * 14142136 + 20000000) < 12 * 10000000`
accompanying Theorem 6.5 (`thm:direct-fft`); full proofs of Lemmas 6.1–6.3 and Theorem 6.5 live in `SubNLogN/{Math/Walsh,Machine/FFT}/`.
-/

namespace SubNLogN.S3

open SubNLogN

/-- Explicit witness from Remark 6.4 (`rem:walsh-unshuffle`): for record-axis widths `(4, 3)`
and `K = 2` (`m₀ = 7`), the layout map `L = [0, 3, 4, 1, 5, 6, 2]` and per-axis bit reversal
`B = [3, 2, 1, 0, 6, 5, 4]` do NOT commute (`L (B 0) = 1 ≠ 3 = B (L 0)`), and the natural-order
restoring map `U = B⁻¹ ∘ L⁻¹` satisfies `U (L (B j)) = j` for all `j ∈ Fin 7`. -/
def layoutExampleL : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩
  | ⟨2, _⟩ => ⟨4, by decide⟩
  | ⟨3, _⟩ => ⟨1, by decide⟩
  | ⟨4, _⟩ => ⟨5, by decide⟩
  | ⟨5, _⟩ => ⟨6, by decide⟩
  | ⟨6, _⟩ => ⟨2, by decide⟩

def bitRevExampleB : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨3, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩
  | ⟨3, _⟩ => ⟨0, by decide⟩
  | ⟨4, _⟩ => ⟨6, by decide⟩
  | ⟨5, _⟩ => ⟨5, by decide⟩
  | ⟨6, _⟩ => ⟨4, by decide⟩

def layoutExampleLinv : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩
  | ⟨2, _⟩ => ⟨6, by decide⟩
  | ⟨3, _⟩ => ⟨1, by decide⟩
  | ⟨4, _⟩ => ⟨2, by decide⟩
  | ⟨5, _⟩ => ⟨4, by decide⟩
  | ⟨6, _⟩ => ⟨5, by decide⟩

theorem remark74_noncommutativity_and_unshuffle :
    layoutExampleL (bitRevExampleB ⟨0, by decide⟩) ≠
      bitRevExampleB (layoutExampleL ⟨0, by decide⟩) ∧
    ∀ j : Fin 7, bitRevExampleB (layoutExampleLinv (layoutExampleL (bitRevExampleB j))) = j := by
  decide

/-- **Closed Numeral Check for the Direct-FFT Per-Level Error Margin (accompanying Theorem 6.5 (`thm:direct-fft`)):**
Using the rational upper bound `1.4142136 > √2`, checks `2 * (2 * 14142136 + 20000000) < 12 * 10000000`,
corresponding to `2 * (2 √2 + 2) < 12` (twice the single-stage budget `√2 + 2 + √2 < 5` across last-axis
and record-axis DIF passes; the full Theorem 6.5 proof is `direct_fft` in `SubNLogN/Math/Walsh/Proofs/Wiring.lean`
and `SubNLogN/Machine/FFT/`). -/
theorem direct_fft_per_level_error_margin :
    2 * (2 * 14142136 + 20000000) < 12 * 10000000 := by decide

end SubNLogN.S3
