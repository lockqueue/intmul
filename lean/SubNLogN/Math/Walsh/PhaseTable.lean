import SubNLogN.Math.Common.DFT
import SubNLogN.Math.Common.Grid
import IntMul.MaterializedAndComputable.ComputableTranscendentals

/-!
# Direct FFT: disk-valued phases and disk-preserving products (Lemmas 6.1, 6.2)

Paper: Lemma 6.1 (`lem:phase-table`) and Lemma 6.2
(`lem:disk-product`) in Section 6.1 (`sec:direct-fft-phases`).

* `theta r j = e^{π i j / r} = stdChar (j / (2r))`.
* `PhaseTableSpec P ℓ θ̃`: for all `j < 2r` (`r = 2^ℓ`), `θ̃_j ∈ C̃_P`, `|θ̃_j| ≤ 1` and
  `|θ̃_j - θ_j| < 2 · 2^{-P}`. The direct FFT (Theorem 6.5) is stated for any table with this
  property.
* `phaseTableNum P ℓ j : ℤ × ℤ` is a concrete deterministic (computable) table of `P`-grid
  numerators: the fourth roots of unity are returned exactly; otherwise
  `θ̃_j = Q_P((1 - 2^{-P}/8) a_j)`, where `a_j` is the certified fixed-point evaluation of
  `stdChar (j/(2r))` by `IntMul.computableStdCharWithProgramCost` at precision `P + 6`
  (scale `2^{P+8}`). This replaces the Machin + Taylor evaluator of the paper's proof by the
  already certified IntMul evaluator; the final shrink-and-truncate step is the paper's
  (proof of Lemma 6.1 (`lem:phase-table`)).
* Cost note (machine level): the paper's "`O(P^3)` per entry" in Lemma 6.1
  (`lem:phase-table`) is replaced here by the certified IntMul evaluator. The machine contract of the IntMul
  evaluator (`W7_stdChar`) is quartic, `C · (q + bitLen den + 1)^4` steps per call; here
  `q = P + 6` and `den = 2^{ℓ+1}`, so each entry costs `C · (P + ℓ + 9)^4`, and the `2r`-entry
  table costs `2r · C · (P + ℓ + 9)^4`. This setup is absorbed in `O(V)`, `V = 2Rw`, iff
  `2^ℓ ≥ C_* P^3` for a suitable constant `C_*`. That holds for the bridge's root family, where
  `r = 2^ℓ` exceeds every fixed polynomial in `P`. This is absorbed into setup; the value-level statements
  do not depend on it.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-- The phase `θ_j = e^{π i j/r} = stdChar (j/(2r))`. -/
noncomputable def theta (r j : ℕ) : ℂ := IntMul.stdChar ((j : ℝ) / (2 * (r : ℝ)))

/-- A disk-valued phase table at precision `P` for `r = 2^ℓ` (the conclusion of Lemma 6.1):
for every `j < 2r`, `θ̃_j` lies on the `P`-grid, `|θ̃_j| ≤ 1` and `|θ̃_j - θ_j| < 2 · 2^{-P}`. -/
def PhaseTableSpec (P ℓ : ℕ) (θt : ℕ → ℂ) : Prop :=
  ∀ j, j < 2 * 2 ^ ℓ →
    OnGrid P (θt j) ∧ ‖θt j‖ ≤ 1 ∧ ‖θt j - theta (2 ^ ℓ) j‖ < 2 * gridUnit P

/-- Concrete table of `P`-grid numerators `(re, im)` (computable). If `r | 2j` the phase is the
fourth root `i^{2j/r}`, returned exactly; otherwise `Q_P((1 - 2^{-P-3}) a)` with `a` the
IntMul evaluation of `stdChar (j/(2r))` on the grid `2^{-(P+8)}`: with `a = (a₁ + i a₂) 2^{-(P+8)}`
the numerators are `trunc(a_k (2^{P+3} - 1) / 2^{P+11})` (truncation toward zero).
Machine cost per entry: quartic, `C · (P + ℓ + 9)^4` (see the module docstring). -/
def phaseTableNum (P ℓ j : ℕ) : ℤ × ℤ :=
  if (2 * j) % 2 ^ ℓ = 0 then
    match (2 * j / 2 ^ ℓ) % 4 with
    | 0 => (2 ^ P, 0)
    | 1 => (0, 2 ^ P)
    | 2 => (-(2 ^ P), 0)
    | _ => (0, -(2 ^ P))
  else
    let a := (IntMul.computableStdCharWithProgramCost (P + 6) j (2 * 2 ^ ℓ) false).1
    (Int.tdiv (a.1 * (2 ^ (P + 3) - 1)) (2 ^ (P + 11)),
      Int.tdiv (a.2 * (2 ^ (P + 3) - 1)) (2 ^ (P + 11)))

/-- The concrete table as complex numbers: numerators times `2^{-P}`. -/
noncomputable def phaseTable (P ℓ j : ℕ) : ℂ :=
  ⟨((phaseTableNum P ℓ j).1 : ℝ) * gridUnit P, ((phaseTableNum P ℓ j).2 : ℝ) * gridUnit P⟩

/-- **Lemma 6.1** (disk-valued phases, `lem:phase-table`): for `P ≥ 8` and `r = 2^ℓ` with
`ℓ ≤ P`, the concrete table satisfies `PhaseTableSpec` (`θ̃_j ∈ C̃_P`, `|θ̃_j| ≤ 1`,
`|θ̃_j - θ_j| < 2 · 2^{-P}` for `0 ≤ j < 2r`), and the fourth roots of unity (`r | 2j`) are returned
exactly. CONTRACT (proved in `Walsh/Proofs/PhaseTable.lean`). -/
def PhaseTableStmt : Prop :=
  ∀ (P ℓ : ℕ) (_ : 8 ≤ P) (_ : ℓ ≤ P),
    PhaseTableSpec P ℓ (phaseTable P ℓ) ∧
      ∀ j, j < 2 * 2 ^ ℓ → (2 * j) % 2 ^ ℓ = 0 → phaseTable P ℓ j = theta (2 ^ ℓ) j

/-- **Lemma 6.2** (disk-preserving products, `lem:disk-product`): for `a, b ∈ 𝔻_P`, the product
`ab` is exact on the `2P`-grid (it is `2^{-2P}((a₀b₀ - a₁b₁) + i(a₀b₁ + a₁b₀))`, four integer
products of the numerators), and `Q_P(ab)` lies in `𝔻_P` with `|Q_P(ab) - ab| < √2 · 2^{-P}`.
CONTRACT (proved in `Walsh/Proofs/PhaseTable.lean`). -/
def DiskProductStmt : Prop :=
  ∀ (P : ℕ) (a b : ℂ) (_ : OnDiskGrid P a) (_ : OnDiskGrid P b),
    OnGrid (P + P) (a * b) ∧ OnDiskGrid P (truncC P (a * b)) ∧
      ‖truncC P (a * b) - a * b‖ < Real.sqrt 2 * gridUnit P

end SubNLogN.Math.Walsh
