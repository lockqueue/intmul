import SubNLogN.Spec

/-!
# Component S3 (`Walsh.lean`): Three-Layer Walsh Selection, Lifted Exactness & Controlled Flips

**Scope.** Proves `2 × 2` Gaussian-integer identities and an `ℕ` exponent inequality accompanying Section 5 (`sec:walsh`) (full cube-level and `TM2` proofs live in `SubNLogN/{Math,Machine}/Walsh/`):
1. Lemma 5.1 (`lem:walsh-select`): `(2 H_0)^3 = 2 (2 H_0)` (wanted position) and
   `(2 H_0 ∘ S)^3 = 2 (1 + i) I` (unwanted position), together with `[2(1 - i)]^2 = -8 i`;
2. Lemma 5.2 (`lem:walsh-exact`): lifted denominator budget `q + 4 D < q_* = q + 8 d` for
   `1 ≤ D ≤ d`, guaranteeing that every `Q_{q_*}` truncation in a two-gadget CNOT batch discards
   only zero bits;
3. Lemma 5.4 (`lem:cnot`): `(2 H_0) ∘ CZ(false) ∘ (2 H_0) = 2 I` and
   `(2 H_0) ∘ CZ(true) ∘ (2 H_0) = 2 X`.
-/

namespace SubNLogN.S3

open SubNLogN

/-- **Wanted-Position Cube Identity (Lemma 5.1 (`lem:walsh-select`)):**
`(2 H_0)^3 = 2 (2 H_0)`, i.e. `H_0^3 = (1/2) H_0`. -/
theorem twoH0_cube_eq (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    twoH0 (twoH0 (twoH0 p)) =
      ((2 * (twoH0 p).1.1, 2 * (twoH0 p).1.2), (2 * (twoH0 p).2.1, 2 * (twoH0 p).2.2)) := by
  unfold twoH0; ext <;> ring

/-- **Unwanted-Position Cube Identity (Lemma 5.1 (`lem:walsh-select`)):**
`(2 H_0 ∘ S)^3 = 2 (1 + i) I`, i.e. `(H_0 S)^3 = ((1 + i) / 4) I`. -/
theorem twoH0_phaseS_cube_eq (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    twoH0 (phaseS (twoH0 (phaseS (twoH0 (phaseS p))))) =
      ((2 * (p.1.1 - p.1.2), 2 * (p.1.1 + p.1.2)),
       (2 * (p.2.1 - p.2.2), 2 * (p.2.1 + p.2.2))) := by
  unfold twoH0 phaseS; ext <;> ring

/-- Scalar square identity `[2(1 - i)]^2 = -8 i` (Lemma 5.1 (`lem:walsh-select`)). -/
theorem two_one_minus_i_sq :
    gaussMul (2, -2) (2, -2) = (0, -8) := by decide

/-- **Controlled Flip with Control `false` (Lemma 5.4 (`lem:cnot`)):**
`(2 H_0) ∘ CZ(false) ∘ (2 H_0) = 2 I`. -/
theorem twoH0_phaseCZ_false (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    twoH0 (phaseCZ false (twoH0 p)) =
      ((2 * p.1.1, 2 * p.1.2), (2 * p.2.1, 2 * p.2.2)) := by
  dsimp [twoH0, phaseCZ]; ext <;> ring

/-- **Controlled Flip with Control `true` (Lemma 5.4 (`lem:cnot`)):**
`(2 H_0) ∘ CZ(true) ∘ (2 H_0) = 2 X`. -/
theorem twoH0_phaseCZ_true (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    twoH0 (phaseCZ true (twoH0 p)) =
      ((2 * p.2.1, 2 * p.2.2), (2 * p.1.1, 2 * p.1.2)) := by
  dsimp [twoH0, phaseCZ]; ext <;> ring

/-- **Lifted Denominator Budget (Lemma 5.2 (`lem:walsh-exact`)):**
For `1 ≤ D ≤ d` and `s ≤ D`, all six layer calls across the two selective `H_T` gadgets of a
controlled-flip batch have denominator exponent at most `P + s + 3 D ≤ P + 4 D < P + 8 d = P_*`. -/
theorem lifted_denominator_budget (P D d s : ℕ) (hD : 1 ≤ D) (hd : D ≤ d) (hs : s ≤ D) :
    P + D < P + 8 * d ∧
    P + 2 * D < P + 8 * d ∧
    P + 3 * D < P + 8 * d ∧
    P + s + 3 * D < P + 8 * d := by
  omega

end SubNLogN.S3
