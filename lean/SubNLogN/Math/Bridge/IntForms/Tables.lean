import SubNLogN.Math.Bridge.TablesConcrete
import SubNLogN.Math.Common.GridInt
import SubNLogN.Math.Bridge.IntForms.Solver

/-!
# Bridge: integer forms of the concrete tables `TabConcreteR roundHalfUpR`

The entries of `TabConcreteR rr` (`SubNLogN/Math/Bridge/TablesConcrete.lean`) are reals/complexes
defined through IntMul's certified fixed-point evaluators and a nearest rounding `rr`. This file
gives their integer numerators for the half-up rounding `rr = roundHalfUpR` (the closed `F_new`),
for the machine table evaluator. Notation: `q = P + 2`, `B = tapPrec P` (`= pSub`), `pC = coeffPrec P`.

* Native evaluator outputs (no rounding), with value lemmas:
  - `phaseInt`, scale `2^(B+2)` (`phaseHat_eq`);
  - `sincInt`, scale `2^pSub` (`sincGaussHat_eq`);
  - `c0Int`, `c1Int`, scale `2^(pC+2)` (`c0Hat_eq`, `c1Hat_eq`).
* Before rounding, for every `rr`:
  - `tapNum ω P t A a e` is the exact numerator, scale `2^(2B+2)`, of
    `∑_{s ∈ [-P,P], s ≡ e (mod t)} phaseHat · sincGaussHat`, so
    `tapConcreteR rr … = crnd rr q (gridValC (2B+2) tapNum)` (`tapConcreteR_eq_crnd`);
  - `muConcreteR_eq_rr` gives `μ̂ = rr q (2^(pC+2)/cmaxInt)` and `ahatConcreteR_eq_rr` gives
    `â = max 0 (rr q (cminInt/cmaxInt))`. The orientation is `ĉ_max = ĉ_0 ⟺ 2u < t`
    (`cmaxInt`, `cminInt`).
* Stored integers at `rr = roundHalfUpR` (rounding to nearest, ties toward `+∞`):
  - `tapInt := rhuShiftC (2B - P) tapNum`;
  - `muInt := rhuDiv (2^(pC+2)·2^q) cmaxInt`;
  - `ahatInt := max 0 (rhuDiv (cminInt·2^q) cmaxInt)`;
  - `gamInt := closureFixedInt q (closurePrec q A t) q ahatInt A` (half-up integer closure of
    `IntForms/Solver.lean`).
  Value lemmas: `tapConcreteR_eq_gridValC` and `…ConcreteR_eq_gridValR`. Read-back lemmas:
  `gridIntC_tapConcreteR : gridIntC q (tapConcreteR roundHalfUpR …) = tapInt …` and
  `round (…ConcreteR roundHalfUpR … * 2^q) = …Int …`.

The read-back lemmas are stated with `GridInt.gridIntC` (same body as `Machine.gridInt`) and with
`round (x * 2^q)` (`Machine.realInt q x` by definition), so the file does not import `Machine`.

Access pattern (`tapOffsets`, `tapBlock`, `solBlock`), with `t = t_i` and
`A = A_i = prefixProd t i`:
* tap block of a spread axis `i ≠ 0`: entries `tapInt ω P t A a e` for `a < A` and `e` in the stored
  window (`[-P, P]` if `2P+1 ≤ t`, else `[0, t)`). Every `e : ℤ` is covered: the tap is
  `t`-periodic in `e` (`tapInt_add_period`) and vanishes on residues containing no `s ∈ [-P, P]`
  (`tapInt_eq_zero`).
* solver block of axis `i ≠ 0`: `[muInt ω P t u, ahatInt ω P t u, gamInt ω P t A u]` for `u < t`;
  the closure `γ̂` uses the cycle length `L = A`.

Helpers are in the namespace `SubNLogN.Math.Bridge.IntForms.TablesProof`.
-/

namespace SubNLogN.Math.Bridge.IntForms

open SubNLogN.Math.Common SubNLogN.Math.Common.GridInt
open scoped BigOperators

namespace TablesProof

theorem gridUnit_add_eq (a b : ℕ) : gridUnit (a + b) = gridUnit a * gridUnit b := by
  simp only [gridUnit, pow_add, mul_inv]

theorem round_gridValR_mul_two_pow (F : ℕ) (a : ℤ) : round (gridValR F a * 2 ^ F) = a := by
  rw [gridValR_mul_two_pow, round_intCast]

end TablesProof

open TablesProof

/-! ## Native integer outputs of the IntMul evaluators -/

/-- Gaussian-integer output (scale `2^(B+2)`) of the carrier-phase evaluator inside `phaseHat`. -/
def phaseInt (B t A a : ℕ) (s : ℤ) : ℤ × ℤ :=
  (IntMul.computableStdCharWithProgramCost B
    ((-(s * (A : ℤ) + (a : ℤ))) % ((2 * t * A : ℕ) : ℤ)).toNat (2 * t * A) false).1

/-- Integer output (scale `2^pSub`) of the sinc-Gaussian tap evaluator inside `sincGaussHat`. -/
def sincInt (ω pSub A a : ℕ) (s : ℤ) : ℤ :=
  (IntMul.computableSincGaussianTapWithProgramCost ω pSub A a ((pSub : ℤ) - s).toNat).1

/-- Numerator (scale `2^(coeffPrec P + 2)`) of `ĉ_0` (`c0Hat`). -/
def c0Int (ω P t u : ℕ) : ℤ :=
  (IntMul.computableC0C1WithProgramCost ω (coeffPrec P) (2 * t) (2 * u + 1)).1.1.1

/-- Numerator (scale `2^(coeffPrec P + 2)`) of `ĉ_1` (`c1Hat`). -/
def c1Int (ω P t u : ℕ) : ℤ :=
  (IntMul.computableC0C1WithProgramCost ω (coeffPrec P) (2 * t) (2 * u + 1)).1.2.1

theorem phaseHat_eq (B t A a : ℕ) (s : ℤ) :
    phaseHat B t A a s =
      ⟨((phaseInt B t A a s).1 : ℝ) * gridUnit (B + 2),
        ((phaseInt B t A a s).2 : ℝ) * gridUnit (B + 2)⟩ := by
  simp only [phaseHat, phaseInt, IntMul.toScaledComplex, gridUnit, div_eq_mul_inv]

theorem sincGaussHat_eq (ω pSub A a : ℕ) (s : ℤ) :
    sincGaussHat ω pSub A a s = (((sincInt ω pSub A a s : ℝ) * gridUnit pSub : ℝ) : ℂ) := by
  simp only [sincGaussHat, sincInt, gridUnit, div_eq_mul_inv]

theorem c0Hat_eq (ω P t u : ℕ) :
    c0Hat ω P t u = (c0Int ω P t u : ℝ) * gridUnit (coeffPrec P + 2) := by
  simp only [c0Hat, c0Int, IntMul.toScaledComplex, gridUnit, div_eq_mul_inv]

theorem c1Hat_eq (ω P t u : ℕ) :
    c1Hat ω P t u = (c1Int ω P t u : ℝ) * gridUnit (coeffPrec P + 2) := by
  simp only [c1Hat, c1Int, IntMul.toScaledComplex, gridUnit, div_eq_mul_inv]

/-! ## The tap sum as an exact integer -/

/-- Exact numerator, at scale `2^(2B+2)` with `B = tapPrec P`, of the residue-class sum
`∑_{s ∈ [-P,P], s ≡ e (mod t)} phaseHat · sincGaussHat` inside `tapConcrete`. -/
noncomputable def tapNum (ω P t A a : ℕ) (e : ℤ) : ℤ × ℤ :=
  ∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    if s % (t : ℤ) = e % (t : ℤ) then
      ((phaseInt (tapPrec P) t A a s).1 * sincInt ω (tapPrec P) A a s,
        (phaseInt (tapPrec P) t A a s).2 * sincInt ω (tapPrec P) A a s)
    else 0

theorem tapSum_eq (ω P t A a : ℕ) (e : ℤ) :
    (∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
      if s % (t : ℤ) = e % (t : ℤ) then
        phaseHat (tapPrec P) t A a s * sincGaussHat ω (tapPrec P) A a s else 0) =
      ⟨((tapNum ω P t A a e).1 : ℝ) * gridUnit (2 * tapPrec P + 2),
        ((tapNum ω P t A a e).2 : ℝ) * gridUnit (2 * tapPrec P + 2)⟩ := by
  have hg : gridUnit (2 * tapPrec P + 2) = gridUnit (tapPrec P + 2) * gridUnit (tapPrec P) := by
    rw [← gridUnit_add_eq]
    congr 1
    ring
  apply Complex.ext
  · simp only [Complex.re_sum, tapNum, Prod.fst_sum, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · simp only [phaseHat_eq, sincGaussHat_eq, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, Int.cast_mul, hg]
      ring
    · simp
  · simp only [Complex.im_sum, tapNum, Prod.snd_sum, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · simp only [phaseHat_eq, sincGaussHat_eq, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add, Int.cast_mul, hg]
      ring
    · simp

theorem tapSum_eq_gridValC (ω P t A a : ℕ) (e : ℤ) :
    (∑ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
      if s % (t : ℤ) = e % (t : ℤ) then
        phaseHat (tapPrec P) t A a s * sincGaussHat ω (tapPrec P) A a s else 0) =
      gridValC (2 * tapPrec P + 2) (tapNum ω P t A a e) :=
  tapSum_eq ω P t A a e

/-- `tapNum` depends on the offset only modulo `t`. -/
theorem tapNum_add_period (ω P t A a : ℕ) (e : ℤ) :
    tapNum ω P t A a (e + t) = tapNum ω P t A a e := by
  unfold tapNum
  simp only [Int.add_emod_right]

/-! ## Forms before rounding, for every rounding `rr` -/

/-- Numerator of `ĉ_max` (orientation `ĉ_max = ĉ_0 ⟺ 2u < t`). -/
def cmaxInt (ω P t u : ℕ) : ℤ := if 2 * u < t then c0Int ω P t u else c1Int ω P t u

/-- Numerator of `ĉ_min` (orientation `ĉ_min = ĉ_1 ⟺ 2u < t`). -/
def cminInt (ω P t u : ℕ) : ℤ := if 2 * u < t then c1Int ω P t u else c0Int ω P t u

theorem tapConcreteR_eq_crnd (rr : ℕ → ℝ → ℝ) (ω P t A a : ℕ) (e : ℤ) :
    tapConcreteR rr ω P t A a e =
      crnd rr (P + 2) (gridValC (2 * tapPrec P + 2) (tapNum ω P t A a e)) := by
  unfold tapConcreteR
  rw [tapSum_eq_gridValC]

theorem tapConcreteR_add_period (rr : ℕ → ℝ → ℝ) (ω P t A a : ℕ) (e : ℤ) :
    tapConcreteR rr ω P t A a (e + t) = tapConcreteR rr ω P t A a e := by
  rw [tapConcreteR_eq_crnd, tapConcreteR_eq_crnd, tapNum_add_period]

/-- For a nearest rounding `rr`, offsets whose residue class mod `t` contains no `s ∈ [-P, P]`
carry the zero tap. -/
theorem tapConcreteR_eq_zero {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (ω P t A a : ℕ)
    (e : ℤ) (h : ∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (t : ℤ) ≠ e % (t : ℤ)) :
    tapConcreteR rr ω P t A a e = 0 := by
  unfold tapConcreteR
  rw [Finset.sum_eq_zero, crnd_eq_self hrr (onGrid_zero _)]
  intro s hs
  exact if_neg (h s hs)

theorem muConcreteR_eq_rr (rr : ℕ → ℝ → ℝ) (ω P t u : ℕ) :
    muConcreteR rr ω P t u =
      rr (P + 2) ((2 : ℝ) ^ (coeffPrec P + 2) / (cmaxInt ω P t u : ℝ)) := by
  have key : ∀ n : ℤ, ((n : ℝ) * gridUnit (coeffPrec P + 2))⁻¹ =
      (2 : ℝ) ^ (coeffPrec P + 2) / (n : ℝ) := by
    intro n
    rw [gridUnit, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  unfold muConcreteR cmaxInt
  split_ifs
  · rw [c0Hat_eq, key]
  · rw [c1Hat_eq, key]

theorem ahatConcreteR_eq_rr (rr : ℕ → ℝ → ℝ) (ω P t u : ℕ) :
    ahatConcreteR rr ω P t u =
      max 0 (rr (P + 2) ((cminInt ω P t u : ℝ) / (cmaxInt ω P t u : ℝ))) := by
  have key : ∀ m n : ℤ, ((m : ℝ) * gridUnit (coeffPrec P + 2)) /
      ((n : ℝ) * gridUnit (coeffPrec P + 2)) = (m : ℝ) / (n : ℝ) :=
    fun m n => mul_div_mul_right _ _ (gridUnit_pos _).ne'
  unfold ahatConcreteR cminInt cmaxInt
  split_ifs
  · rw [c0Hat_eq, c1Hat_eq, key]
  · rw [c0Hat_eq, c1Hat_eq, key]

/-! ## Stored integers at the half-up rounding `rr = roundHalfUpR` -/

/-- Numerators (scale `2^(P+2)`) of the stored tap `tapConcreteR roundHalfUpR ω P t A a e`: the
exact sum `tapNum` (scale `2^(2B+2)`, `B = tapPrec P`) rounded half-up by `2^(2B-P)`. -/
noncomputable def tapInt (ω P t A a : ℕ) (e : ℤ) : ℤ × ℤ :=
  rhuShiftC (2 * tapPrec P - P) (tapNum ω P t A a e)

theorem tapConcreteR_eq_gridValC (ω P t A a : ℕ) (e : ℤ) :
    tapConcreteR roundHalfUpR ω P t A a e = gridValC (P + 2) (tapInt ω P t A a e) := by
  have hprec : 2 * tapPrec P + 2 = (P + 2) + (2 * tapPrec P - P) := by
    unfold tapPrec
    omega
  rw [tapConcreteR_eq_crnd, hprec, crnd_roundHalfUpR_gridValC]
  rfl

/-- The stored tap numerators: `gridIntC (P+2) (tapConcreteR roundHalfUpR …) = tapInt …`
(`gridIntC` has the same body as `Machine.gridInt`). -/
theorem gridIntC_tapConcreteR (ω P t A a : ℕ) (e : ℤ) :
    gridIntC (P + 2) (tapConcreteR roundHalfUpR ω P t A a e) = tapInt ω P t A a e := by
  rw [tapConcreteR_eq_gridValC, gridIntC_gridValC]

theorem tapInt_add_period (ω P t A a : ℕ) (e : ℤ) :
    tapInt ω P t A a (e + t) = tapInt ω P t A a e := by
  unfold tapInt
  rw [tapNum_add_period]

theorem tapInt_eq_zero (ω P t A a : ℕ) (e : ℤ)
    (h : ∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (t : ℤ) ≠ e % (t : ℤ)) :
    tapInt ω P t A a e = 0 := by
  rw [← gridIntC_tapConcreteR,
    tapConcreteR_eq_zero isNearestRounding_roundHalfUpR ω P t A a e h, gridIntC_zero]

/-- Numerator (scale `2^(P+2)`) of `μ̂ = muConcreteR roundHalfUpR ω P t u`. -/
def muInt (ω P t u : ℕ) : ℤ :=
  rhuDiv (2 ^ (coeffPrec P + 2) * 2 ^ (P + 2)) (cmaxInt ω P t u)

theorem muConcreteR_eq_gridValR (ω P t u : ℕ) :
    muConcreteR roundHalfUpR ω P t u = gridValR (P + 2) (muInt ω P t u) := by
  have h : (2 : ℝ) ^ (coeffPrec P + 2) = ((2 ^ (coeffPrec P + 2) : ℤ) : ℝ) := by
    norm_cast
  rw [muConcreteR_eq_rr, h, roundHalfUpR_intCast_div]
  rfl

/-- Numerator (scale `2^(P+2)`) of `â = ahatConcreteR roundHalfUpR ω P t u`. -/
def ahatInt (ω P t u : ℕ) : ℤ :=
  max 0 (rhuDiv (cminInt ω P t u * 2 ^ (P + 2)) (cmaxInt ω P t u))

theorem ahatConcreteR_eq_gridValR (ω P t u : ℕ) :
    ahatConcreteR roundHalfUpR ω P t u = gridValR (P + 2) (ahatInt ω P t u) := by
  rw [ahatConcreteR_eq_rr, roundHalfUpR_intCast_div]
  simp only [gridValR, ahatInt, Int.cast_max, Int.cast_zero]
  rw [max_mul_of_nonneg _ _ (gridUnit_pos (P + 2)).le, zero_mul]

/-- Numerator (scale `2^(P+2)`) of `γ̂ = gamConcreteR roundHalfUpR ω P t A u
= closureFixedR roundHalfUpR q Q â A` (`Q = closurePrec q A t`), through the half-up integer
closure `closureFixedInt` of `IntForms/Solver.lean`. -/
def gamInt (ω P t A u : ℕ) : ℤ :=
  closureFixedInt (P + 2) (closurePrec (P + 2) A t) (P + 2) (ahatInt ω P t u) A

theorem gamConcreteR_eq_gridValR (ω P t A u : ℕ) :
    gamConcreteR roundHalfUpR ω P t A u = gridValR (P + 2) (gamInt ω P t A u) := by
  rw [gamConcreteR, ahatConcreteR_eq_gridValR, gamInt]
  exact (closureFixedInt_spec _ _ _ _ _).symm

/-! ## Read-back (`Machine.realInt F x = round (x·2^F)`) -/

theorem round_muConcreteR (ω P t u : ℕ) :
    round (muConcreteR roundHalfUpR ω P t u * 2 ^ (P + 2)) = muInt ω P t u := by
  rw [muConcreteR_eq_gridValR, round_gridValR_mul_two_pow]

theorem round_ahatConcreteR (ω P t u : ℕ) :
    round (ahatConcreteR roundHalfUpR ω P t u * 2 ^ (P + 2)) = ahatInt ω P t u := by
  rw [ahatConcreteR_eq_gridValR, round_gridValR_mul_two_pow]

theorem round_gamConcreteR (ω P t A u : ℕ) :
    round (gamConcreteR roundHalfUpR ω P t A u * 2 ^ (P + 2)) = gamInt ω P t A u := by
  rw [gamConcreteR_eq_gridValR, round_gridValR_mul_two_pow]

end SubNLogN.Math.Bridge.IntForms
