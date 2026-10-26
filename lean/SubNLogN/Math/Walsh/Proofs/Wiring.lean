import SubNLogN.Math.Walsh.Proofs.PhaseTable
import SubNLogN.Math.Walsh.Proofs.Middle
import SubNLogN.Math.Walsh.Proofs.DirectFFT
import SubNLogN.Math.Walsh.Proofs.DirectFFTLocal
import SubNLogN.Math.Walsh.Proofs.LayoutPerm
import SubNLogN.Math.Walsh.Proofs.LayoutExact
import SubNLogN.Math.Walsh.Proofs.DirectFFTExact

/-!
# Walsh wiring: assembling the proved pieces into Theorem 6.5 and Corollary 6.6

Instantiates the conditional `_of` theorems of `SubNLogN/Math/Walsh/Proofs/` with the unconditional
component proofs (`thm:direct-fft`, `cor:walsh-middle`, `Middle.lean`).

Assembled ingredients (all unconditionally proved):
* `phase_table` (Lemma 6.1, `lem:phase-table`), `disk_product` (Lemma 6.2, `lem:disk-product`);
* `walsh_layout_perm`, `walsh_layout_round_slice`, `walsh_layout_unshuffle` (Lemma 6.3, `lem:walsh-layout`),
  `walsh_layout_exact` (Lemma 6.3 exact counterpart);
* `dif_exact`, `tensor_factor`, `tensor_encoding` (`Proofs/DirectFFTExact.lean`); `round_local_error`,
  `last_axis_level_error` (`Proofs/DirectFFTLocal.lean`); `direct_fft_of`, `direct_fft_count_of`;
* `walsh_middle_of` (`Proofs/Middle.lean`); the Section 5 theorems (`positional_perm`, `sliceCall_eq`, `walsh_exact`).
Final results: `direct_fft : DirectFFTStmt` (Theorem 6.5), `direct_fft_count`,
`walsh_middle : WalshMiddleStmt` (Corollary 6.6 for every oracle satisfying `WalshLayerOK`),
`walsh_middle_ideal : WalshMiddleIdealStmt` (Corollary 6.6 for `idealLayer`).
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-- Theorem 6.5 from the three exact-counterpart sub-contracts (DIF, tensor factorization, and
the exact counterpart of the layout). -/
theorem direct_fft_of_pending (hdif : DifExactStmt) (hfac : TensorFactorStmt)
    (hexact : WalshLayoutExactStmt) : DirectFFTStmt :=
  direct_fft_of round_local_error last_axis_level_error hdif hfac walsh_layout_perm
    walsh_layout_round_slice hexact walsh_layout_unshuffle

/-- Theorem 6.5, abstract counts of the record-axis program (proof of Theorem 6.5 (`thm:direct-fft`)). -/
theorem direct_fft_count : DirectFFTCountStmt :=
  direct_fft_count_of walsh_layout_perm

/-- Corollary 6.6 for the ideal oracle from Theorem 6.5 (Lemma 6.1 is discharged by
`phase_table`). -/
theorem walsh_middle_ideal_of_direct_fft (h85 : DirectFFTStmt) : WalshMiddleIdealStmt :=
  fun P D ℓ K a hq hD hℓ hℓq hK1 hKℓ ha =>
    walsh_middle_ideal_of h85 phase_table P D ℓ K a hq hD hℓ hℓq hK1 hKℓ ha

/-- Corollary 6.6 for a general oracle satisfying `WalshLayerOK`, from Theorem 6.5. -/
theorem walsh_middle_of_direct_fft (h85 : DirectFFTStmt) : WalshMiddleStmt :=
  walsh_middle_of h85 phase_table

/-- Corollary 6.6 for the ideal oracle from the three exact-counterpart sub-contracts. -/
theorem walsh_middle_ideal_of_pending (hdif : DifExactStmt) (hfac : TensorFactorStmt)
    (hexact : WalshLayoutExactStmt) : WalshMiddleIdealStmt :=
  walsh_middle_ideal_of_direct_fft (direct_fft_of_pending hdif hfac hexact)

/-- **Theorem 6.5** (direct complex tensor FFT, value level; `thm:direct-fft`). -/
theorem direct_fft : DirectFFTStmt :=
  direct_fft_of_pending dif_exact tensor_factor walsh_layout_exact

/-- **Corollary 6.6** (Walsh middle transform; `cor:walsh-middle`) for every layer oracle
satisfying `WalshLayerOK`. -/
theorem walsh_middle : WalshMiddleStmt :=
  walsh_middle_of_direct_fft direct_fft

/-- **Corollary 6.6 for the ideal oracle** (`cor:walsh-middle`): under the paper's shape and
size hypotheses of Theorem 6.5 at `q = P + 2`, `walshMiddle idealLayer (P + 2) D ℓ K a` is a middle
transform (Definition 4.5) with `E_mid = 12ℓ` and `δ_mid = 0`. -/
theorem walsh_middle_ideal : WalshMiddleIdealStmt :=
  walsh_middle_ideal_of_direct_fft direct_fft

end SubNLogN.Math.Walsh
