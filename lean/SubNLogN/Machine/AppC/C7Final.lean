/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Main
import SubNLogN.Machine.AppC.C7LinesSetup
import SubNLogN.Machine.AppC.C7LinesOffKernel
import SubNLogN.Machine.FFT.Bands
import SubNLogN.Assembly.Row46Layer

/-!
# Lemma A.9: wiring to the open leaves (`Machine/AppC/C7Final.lean`)

0 `sorry`. The Lemma A.9 contract from its two remaining open inputs:
* `c7PackedXor_of_open τ (hC6 : C6InterchangeStmt τ) (hX : ∀ σ, C7ExtractStmt σ) :
  ∀ σ, C7PackedXorStmt τ σ`, from `c7PackedXor_of_lines_extract` (`C7Main.lean`: the address
  identity, the repair glue and the top-bit phase are proved there), the eight packed lines
  `c7Lines_holds` (`C7LinesSetup.lean`, needing the Lemma A.8 interchange **at the same `τ`**) and the
  proved offset kernels `c7LinesOff_holds` (`C7LinesOffKernel.lean`).
* At the middle layer's constants: `midLayerParams_row46_tau :
  (midLayerParams row46Layer 1).τ = ((Row46.tau : ℚ) : ℝ)` (by `rfl`: `midLayerParams` keeps `τ`)
  and `c7PackedXor_mid_of_open (hC6 : C6InterchangeStmt ((Row46.tau : ℚ) : ℝ))
  (hX : ∀ σ, C7ExtractStmt σ) : ∀ σ, C7PackedXorStmt (midLayerParams row46Layer 1).τ σ`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

/-- **Lemma A.9 from the Lemma A.8 interchange (at the same `τ`) and the extraction kernel** (0 `sorry`). -/
theorem c7PackedXor_of_open (τ : ℝ) (hC6 : C6InterchangeStmt τ) (hX : ∀ σ, C7ExtractStmt σ) :
    ∀ σ, C7PackedXorStmt τ σ := by
  intro σ
  obtain ⟨J, hOff⟩ := c7LinesOff_holds
  exact c7PackedXor_of_lines_extract τ σ (c7Lines_holds τ σ J hC6 hOff) (hX σ)

/-- The middle layer's `τ` is the `C₁ = 14` row's `τ = Row46.tau = 1 − 2^{-40}`. -/
theorem midLayerParams_row46_tau :
    (midLayerParams SubNLogN.Assembly.row46Layer 1).τ = ((SubNLogN.Math.Cost.Row46.tau : ℚ) : ℝ) :=
  rfl

/-- **Lemma A.9 at the middle layer's constants** (`p = midLayerParams row46Layer 1`, the instance needed
by `rowAdd_of_c7`), from the Lemma A.8 interchange at `τ = Row46.tau` and the extraction kernel. -/
theorem c7PackedXor_mid_of_open
    (hC6 : C6InterchangeStmt ((SubNLogN.Math.Cost.Row46.tau : ℚ) : ℝ))
    (hX : ∀ σ, C7ExtractStmt σ) :
    ∀ σ, C7PackedXorStmt (midLayerParams SubNLogN.Assembly.row46Layer 1).τ σ := by
  rw [midLayerParams_row46_tau]
  exact c7PackedXor_of_open _ hC6 hX

end SubNLogN.Machine
