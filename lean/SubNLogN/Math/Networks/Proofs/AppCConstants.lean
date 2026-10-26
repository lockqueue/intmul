import SubNLogN.Math.Networks.Proofs.Counting
import SubNLogN.Math.Networks.Proofs.Deficit
import SubNLogN.Math.Networks.AppCCore

/-!
# Appendix A model constants and the quantitative deficit rates (value-level exports)

Re-exports for the machine-level formalization (`SubNLogN/Machine/`):

* the identification of the model constants `mH`, `Wb`, `Wc` (`Cert.lean`, `AppCProc.lean`,
  `AppCCore.lean`) with the `Spec.lean` numerals `tripleM 100`, `tripleWb 100`, `tripleWc 100`;
* the QUANTITATIVE rates `s/W < m^σ` (bit: `σ = 1 − 2^{-40}`; complex: `σ = 1 − 2^{-42}`). These are
  proved from the integer formulas (`deficitsH100_holds`, Proposition A.2 (`prop:deficits`)), not inferred
  from the strict integer deficit `s < W m` alone, which would not yield an explicit exponent.

Everything here is a re-export of proved theorems (`AppC` is a historical filename prefix retained for stability). No new hypotheses.
-/

namespace SubNLogN.Math.Networks

/-- `mH = tripleM 100 = 10^6`. -/
theorem mH_eq_tripleM : mH = tripleM 100 := by norm_num [mH, tripleM]

/-- `W_b = |Role .bit 100| = tripleWb 100`. -/
theorem Wb_eq_tripleWb : Wb = tripleWb 100 := by
  show Fintype.card (Role .bit 100) = tripleWb 100
  exact (cardRole_holds 100).1

/-- `W_c = |Role .complex 100| = tripleWc 100`. -/
theorem Wc_eq_tripleWc : Wc = tripleWc 100 := by
  show Fintype.card (Role .complex 100) = tripleWc 100
  exact (cardRole_holds 100).2

/-- Bit-network rate (Proposition A.7 (`prop:transfer11`)): `s_b / W_b < m^{1 − 2^{-40}}` at `h = 100`. -/
theorem rate_bit :
    (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 40) :=
  deficitsH100_holds.1

/-- Complex-network rate (Lemma A.10 (`lem:transfer-phase`)): `s_c / W_c < m^{σ}` with `σ = 1 − 2^{-42}` at `h = 100`. -/
theorem rate_complex :
    (tripleSc 100 : ℝ) / tripleWc 100 < (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 42) :=
  deficitsH100_holds.2

/-- Non-strict form of the complex rate (the form used by the cost recurrence, CR-01 (2.1)). -/
theorem rate_complex_le :
    (tripleSc 100 : ℝ) / tripleWc 100 ≤ (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 42) :=
  le_of_lt rate_complex

/-- Non-strict form of the bit rate. -/
theorem rate_bit_le :
    (tripleSb 100 : ℝ) / tripleWb 100 ≤ (tripleM 100 : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 40) :=
  le_of_lt rate_bit

/-- The complex exponent `σ = 1 − 2^{-42}` lies in `[0, 1]`. -/
theorem sigma42_mem : (0 : ℝ) ≤ 1 - (2 : ℝ)⁻¹ ^ 42 ∧ 1 - (2 : ℝ)⁻¹ ^ 42 ≤ 1 := by
  constructor <;> norm_num

/-- The bit exponent `τ = 1 − 2^{-40}` lies in `[0, 1]`. -/
theorem tau40_mem : (0 : ℝ) ≤ 1 - (2 : ℝ)⁻¹ ^ 40 ∧ 1 - (2 : ℝ)⁻¹ ^ 40 ≤ 1 := by
  constructor <;> norm_num

end SubNLogN.Math.Networks
