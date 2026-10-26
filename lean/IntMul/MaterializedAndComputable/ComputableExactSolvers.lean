import IntMul.MaterializedAndComputable.SequentialTransducers
import IntMul.MaterializedAndComputable.ComputablePrimitives

/-!
# Part 2 — Computable Fixed-Point (`ℤ × ℤ`) 3-Regime Bidiagonal/Nyquist Solvers, Base DFT, and Chunk Packing

*Note on Leaf DFT*: This module provides both the shared fixed-point bidiagonal/Nyquist solver
primitives (`gPreTwistU`, `gDivQuantizeUnscaled`, `computableSolveBidiagonalFwd`,
`computableSolveNyquist`, `computableSolveBidiagonalBwd`) and the **legacy intermediate step**
`computableBaseDFTExact` for $R \mid 4$ ($R \in \{1, 2, 4\}$) leaves (`step := 4 / R`).
The paper-faithful headline pipeline (`PaperHeadlinePipeline.lean` / `computablePaperMultiplyOfBitLength`)
supersedes `computableBaseDFTExact` with the general power-of-two `BaseRadix2FFT` leaf
(`computableBaseRadix2FFTWithProgramCost` in `ProgramCostPrimitives.lean`) under the paper's stopping
rule $R \le 4 p^2$ (`buildQuantizedSpecPaperStop`).
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-- Pure-integer pre-twist product `complexQuantize q (toScaledComplex q tw * U)` where `uRaw : ℤ × ℤ`
represents `U = ⟨uRaw.1 / (2^q * 2^q), uRaw.2 / (2^q * 2^q)⟩`. -/
def gPreTwistU (q : ℕ) (tw uRaw : ℤ × ℤ) : ℤ × ℤ :=
  let den : ℤ := ((2 ^ q * 2 ^ q : ℕ) : ℤ)
  gQuantizeRat (tw.1 * uRaw.1 - tw.2 * uRaw.2) (tw.1 * uRaw.2 + tw.2 * uRaw.1) den

theorem toScaledComplex_gPreTwistU_eq (q : ℕ) (tw uRaw : ℤ × ℤ) (U : ℂ)
    (hU : U = ⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q),
               (uRaw.2 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q)⟩) :
    toScaledComplex q (gPreTwistU q tw uRaw) =
      complexQuantize q (toScaledComplex q tw * U) := by
  unfold gPreTwistU
  dsimp only
  have hden : (0 : ℤ) ≤ ((2 ^ q * 2 ^ q : ℕ) : ℤ) := by positivity
  refine toScaledComplex_gQuantizeRat_eq_complexQuantize q
    (tw.1 * uRaw.1 - tw.2 * uRaw.2) (tw.1 * uRaw.2 + tw.2 * uRaw.1)
    ((2 ^ q * 2 ^ q : ℕ) : ℤ) hden (toScaledComplex q tw * U) ?_ ?_
  · rw [hU]
    simp only [Complex.mul_re, toScaledComplex]
    push_cast
    ring
  · rw [hU]
    simp only [Complex.mul_im, toScaledComplex]
    push_cast
    ring

/-- Exact pure-integer quantized complex division `complexQuantize q (z / w)` when `z` and `w`
are represented by Gaussian integers `N, D : ℤ × ℤ` sharing any common positive scale `T > 0`
(`z = ⟨N.1 / T, N.2 / T⟩`, `w = ⟨D.1 / T, D.2 / T⟩`). -/
def gDivQuantizeUnscaled (q : ℕ) (N D : ℤ × ℤ) : ℤ × ℤ :=
  let S : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let numRe : ℤ := (N.1 * D.1 + N.2 * D.2) * S
  let numIm : ℤ := (N.2 * D.1 - N.1 * D.2) * S
  let den : ℤ := D.1 * D.1 + D.2 * D.2
  gQuantizeRat numRe numIm den

theorem toScaledComplex_gDivQuantizeUnscaled_eq
    (q : ℕ) (N D : ℤ × ℤ) (T : ℝ) (hT : 0 < T) (z w : ℂ)
    (hz : z = ⟨(N.1 : ℝ) / T, (N.2 : ℝ) / T⟩)
    (hw : w = ⟨(D.1 : ℝ) / T, (D.2 : ℝ) / T⟩) :
    toScaledComplex q (gDivQuantizeUnscaled q N D) = complexQuantize q (z / w) := by
  unfold gDivQuantizeUnscaled
  dsimp only
  set S : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  set den : ℤ := D.1 * D.1 + D.2 * D.2
  have hden_nonneg : 0 ≤ den := by
    dsimp [den]
    exact add_nonneg (mul_self_nonneg D.1) (mul_self_nonneg D.2)
  have hS_real : (S : ℝ) = (2 : ℝ) ^ (q + 2) := by
    dsimp [S]
    push_cast
    rfl
  have hS_pos : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
  refine toScaledComplex_gQuantizeRat_eq_complexQuantize q
    ((N.1 * D.1 + N.2 * D.2) * S) ((N.2 * D.1 - N.1 * D.2) * S) den hden_nonneg (z / w) ?_ ?_
  · rcases eq_or_lt_of_le hden_nonneg with hden0 | hden_pos
    · have hD1 : D.1 = 0 := by dsimp [den] at hden0; nlinarith
      have hD2 : D.2 = 0 := by dsimp [den] at hden0; nlinarith
      have hw0 : w = 0 := by rw [hw, hD1, hD2]; apply Complex.ext <;> simp
      rw [hw0, div_zero, Complex.zero_re, ← hden0]
      simp
    · have hden_r : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden_pos
      have hnormSq : Complex.normSq w = (den : ℝ) / (T * T) := by
        rw [hw, Complex.normSq_apply]
        dsimp [den]
        push_cast
        field_simp [hT.ne']
      rw [Complex.div_re, hnormSq, hz, hw]
      dsimp only
      push_cast
      rw [hS_real]
      field_simp [hT.ne', hden_r.ne', hS_pos.ne']
  · rcases eq_or_lt_of_le hden_nonneg with hden0 | hden_pos
    · have hD1 : D.1 = 0 := by dsimp [den] at hden0; nlinarith
      have hD2 : D.2 = 0 := by dsimp [den] at hden0; nlinarith
      have hw0 : w = 0 := by rw [hw, hD1, hD2]; apply Complex.ext <;> simp
      rw [hw0, div_zero, Complex.zero_im, ← hden0]
      simp
    · have hden_r : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden_pos
      have hnormSq : Complex.normSq w = (den : ℝ) / (T * T) := by
        rw [hw, Complex.normSq_apply]
        dsimp [den]
        push_cast
        field_simp [hT.ne']
      rw [Complex.div_im, hnormSq, hz, hw]
      dsimp only
      push_cast
      rw [hS_real]
      field_simp [hT.ne', hden_r.ne', hS_pos.ne']

/-- Exact pure-integer quantized rational step
`complexQuantize q ((y - c1 * zPart) / (c0 + d1 * zHom))`
where `y, c1, zPart, c0, d1, zHom : ℤ × ℤ` are all at precision `q` (`toScaledComplex q`). -/
def gRatioQuantize (q : ℕ) (y c1 zPart c0 d1 zHom : ℤ × ℤ) : ℤ × ℤ :=
  let S : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let N : ℤ × ℤ := gSub (y.1 * S, y.2 * S) (gMulUnit c1 zPart)
  let D : ℤ × ℤ := gAdd (c0.1 * S, c0.2 * S) (gMulUnit d1 zHom)
  gDivQuantizeUnscaled q N D

theorem toScaledComplex_gRatioQuantize_eq
    (q : ℕ) (y c1 zPart c0 d1 zHom : ℤ × ℤ) :
    toScaledComplex q (gRatioQuantize q y c1 zPart c0 d1 zHom) =
      complexQuantize q
        ((toScaledComplex q y - toScaledComplex q c1 * toScaledComplex q zPart) /
          (toScaledComplex q c0 + toScaledComplex q d1 * toScaledComplex q zHom)) := by
  unfold gRatioQuantize
  dsimp only
  set S_real : ℝ := (2 : ℝ) ^ (q + 2)
  have hS_pos : 0 < S_real := by positivity
  set T : ℝ := S_real * S_real
  have hT_pos : 0 < T := mul_pos hS_pos hS_pos
  refine toScaledComplex_gDivQuantizeUnscaled_eq q _ _ T hT_pos _ _ ?_ ?_
  · apply Complex.ext <;>
      (simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        toScaledComplex, gSub, gMulUnit, T, S_real];
       push_cast; field_simp [hS_pos.ne'])
  · apply Complex.ext <;>
      (simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        toScaledComplex, gAdd, gMulUnit, T, S_real];
       push_cast; field_simp [hS_pos.ne'])

/-- Exact pure-integer quantized linear combination `complexQuantize q (a + b * c)`. -/
def gCombineQuantize (q : ℕ) (a b c : ℤ × ℤ) : ℤ × ℤ :=
  let S : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let N : ℤ × ℤ := gAdd (a.1 * S, a.2 * S) (gMulUnit b c)
  gQuantizeRat N.1 N.2 S

theorem toScaledComplex_gCombineQuantize_eq (q : ℕ) (a b c : ℤ × ℤ) :
    toScaledComplex q (gCombineQuantize q a b c) =
      complexQuantize q (toScaledComplex q a + toScaledComplex q b * toScaledComplex q c) := by
  unfold gCombineQuantize
  dsimp only
  have hden : (0 : ℤ) ≤ ((2 ^ (q + 2) : ℕ) : ℤ) := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
  refine toScaledComplex_gQuantizeRat_eq_complexQuantize q _ _
    ((2 ^ (q + 2) : ℕ) : ℤ) hden
    (toScaledComplex q a + toScaledComplex q b * toScaledComplex q c) ?_ ?_
  · simp only [Complex.add_re, Complex.mul_re, toScaledComplex, gAdd, gMulUnit]
    push_cast
    field_simp [hpow.ne']
  · simp only [Complex.add_im, Complex.mul_im, toScaledComplex, gAdd, gMulUnit]
    push_cast
    field_simp [hpow.ne']

/-- Single-pass pure-integer array builder for `zPartFwdQuantized`. -/
def buildComputableZPartFwdExact (q : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : ℕ → Array (ℤ × ℤ)
  | 0 => #[(0, 0)]
  | n + 1 =>
    let arr := buildComputableZPartFwdExact q c0 c1 Y n
    let prev := read1D arr n
    let y_next := read1D Y (n + 1)
    arr.push (gRatioQuantize q y_next c1 prev c0 (0, 0) (0, 0))

@[simp]
theorem size_buildComputableZPartFwdExact (q : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) :
    (buildComputableZPartFwdExact q c0 c1 Y n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildComputableZPartFwdExact, ih]

theorem toScaledComplex_read1D_buildComputableZPartFwdExact_eq
    (q : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n u1 : ℕ) (hu1 : u1 ≤ n) :
    toScaledComplex q (read1D (buildComputableZPartFwdExact q c0 c1 Y n) u1) =
      zPartFwdQuantized q (toScaledComplex q c0) (toScaledComplex q c1)
        (fun k => toScaledComplex q (read1D Y k)) u1 := by
  induction n generalizing u1 with
  | zero =>
    have hu0 : u1 = 0 := by omega
    subst hu0
    exact toScaledComplex_zero q
  | succ n ih =>
    dsimp only [buildComputableZPartFwdExact]
    have hsize := size_buildComputableZPartFwdExact q c0 c1 Y n
    rw [read1D_push _ _ u1 (by omega), hsize]
    split_ifs with hlt
    · exact ih u1 (by omega)
    · have hu1_eq : u1 = n + 1 := by omega
      subst hu1_eq
      dsimp only [zPartFwdQuantized]
      rw [toScaledComplex_gRatioQuantize_eq, ih n le_rfl]
      congr 1
      simp only [toScaledComplex_zero, zero_mul, add_zero]
      rw [sub_div, neg_div, neg_mul, div_mul_eq_mul_div, sub_eq_add_neg]

/-- Single-pass pure-integer array builder for `zHomFwdQuantized`. -/
def buildComputableZHomFwdExact (q : ℕ) (c0 c1 : ℤ × ℤ) : ℕ → Array (ℤ × ℤ)
  | 0 => #[(((2 ^ (q + 2) : ℕ) : ℤ), 0)]
  | n + 1 =>
    let arr := buildComputableZHomFwdExact q c0 c1 n
    let prev := read1D arr n
    arr.push (gRatioQuantize q (0, 0) c1 prev c0 (0, 0) (0, 0))

@[simp]
theorem size_buildComputableZHomFwdExact (q : ℕ) (c0 c1 : ℤ × ℤ) (n : ℕ) :
    (buildComputableZHomFwdExact q c0 c1 n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildComputableZHomFwdExact, ih]

theorem toScaledComplex_read1D_buildComputableZHomFwdExact_eq
    (q : ℕ) (c0 c1 : ℤ × ℤ) (n u1 : ℕ) (hu1 : u1 ≤ n) :
    toScaledComplex q (read1D (buildComputableZHomFwdExact q c0 c1 n) u1) =
      zHomFwdQuantized q (toScaledComplex q c0) (toScaledComplex q c1) u1 := by
  induction n generalizing u1 with
  | zero =>
    have hu0 : u1 = 0 := by omega
    subst hu0
    dsimp only [buildComputableZHomFwdExact, zHomFwdQuantized, read1D]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
    apply Complex.ext
    · change (((2 ^ (q + 2) : ℕ) : ℤ) : ℝ) / (2 : ℝ) ^ (q + 2) = 1
      push_cast
      exact div_self hpow.ne'
    · simp [toScaledComplex]
  | succ n ih =>
    dsimp only [buildComputableZHomFwdExact]
    have hsize := size_buildComputableZHomFwdExact q c0 c1 n
    rw [read1D_push _ _ u1 (by omega), hsize]
    split_ifs with hlt
    · exact ih u1 (by omega)
    · have hu1_eq : u1 = n + 1 := by omega
      subst hu1_eq
      dsimp only [zHomFwdQuantized]
      rw [toScaledComplex_gRatioQuantize_eq, ih n le_rfl]
      congr 1
      simp only [toScaledComplex_zero, zero_sub, zero_mul, add_zero,
        neg_div, neg_mul, div_mul_eq_mul_div]

/-- Step-instrumented pure-integer forward cyclic bidiagonal column solver
(`computableSolveBidiagonalFwdExactWithSteps`, `[MS]` §§5.1–5.2):
uses `runSequentialScanSteps` and returns `(outArr, stOut.steps)`. -/
def computableSolveBidiagonalFwdExactWithSteps
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : Array (ℤ × ℤ) × ℕ :=
  let zPartArr := buildComputableZPartFwdExact q c0 c1 Y (t1 - 1)
  let zHomArr := buildComputableZHomFwdExact q c0 c1 (t1 - 1)
  let Z0 := gRatioQuantize q (read1D Y 0) c1 (read1D zPartArr (t1 - 1)) c0 c1 (read1D zHomArr (t1 - 1))
  let stOut := runSequentialScanSteps (fun u1 =>
    gCombineQuantize q (read1D zPartArr u1) Z0 (read1D zHomArr u1)) t1
  (stOut.outTape, stOut.steps)

/-- Pure-integer forward cyclic bidiagonal column solver (`computableSolveBidiagonalFwdExact`, `[MS]` §§5.1–5.2),
exact integer counterpart of `solveBidiagonalFwdQuantized`. -/
def computableSolveBidiagonalFwdExact
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (computableSolveBidiagonalFwdExactWithSteps q t1 c0 c1 Y).1

@[simp]
theorem computableSolveBidiagonalFwdExactWithSteps_fst
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalFwdExactWithSteps q t1 c0 c1 Y).1 =
      computableSolveBidiagonalFwdExact q t1 c0 c1 Y := rfl

@[simp]
theorem computableSolveBidiagonalFwdExactWithSteps_snd
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalFwdExactWithSteps q t1 c0 c1 Y).2 = t1 := by
  simp [computableSolveBidiagonalFwdExactWithSteps]

/-- **Exact Semantic Equivalence of `computableSolveBidiagonalFwdExact` and `solveBidiagonalFwdQuantized`**: -/
theorem toScaledComplex_computableSolveBidiagonalFwdExact_eq
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (u1 : ℕ) (hu1 : u1 < t1) :
    toScaledComplex q (read1D (computableSolveBidiagonalFwdExact q t1 c0 c1 Y) u1) =
      solveBidiagonalFwdQuantized q t1 (toScaledComplex q c0) (toScaledComplex q c1)
        (fun k => toScaledComplex q (read1D Y k)) u1 := by
  dsimp only [computableSolveBidiagonalFwdExact, computableSolveBidiagonalFwdExactWithSteps,
    solveBidiagonalFwdQuantized]
  rw [read1D_runSequentialScanSteps_eq _ t1 u1 hu1]
  rw [toScaledComplex_gCombineQuantize_eq,
      toScaledComplex_gRatioQuantize_eq,
      toScaledComplex_read1D_buildComputableZPartFwdExact_eq q c0 c1 Y (t1 - 1) (t1 - 1) le_rfl,
      toScaledComplex_read1D_buildComputableZHomFwdExact_eq q c0 c1 (t1 - 1) (t1 - 1) le_rfl,
      toScaledComplex_read1D_buildComputableZPartFwdExact_eq q c0 c1 Y (t1 - 1) u1 (by omega),
      toScaledComplex_read1D_buildComputableZHomFwdExact_eq q c0 c1 (t1 - 1) u1 (by omega)]

/-- Step-instrumented pure-integer backward cyclic bidiagonal column solver
(`computableSolveBidiagonalBwdExactWithSteps`, `[MS]` §§5.1–5.2):
uses the sequential reversal state machines `runBwdRevSteps` and `runReverseSteps` (stepping the read
head by `-1` and write head by `+1` via `Array.push` with zero random-access `t1 - 1 - u1`) and returns
`(stOut.outTape, stOut.outTape.size)` (the `t1` output entries to be weighted by
`16 * mulBitCost + 16 * addBitCost` per entry in the annotated cost model, while
`stIn.steps + stOut.steps` counts all seek and reverse head steps). -/
def computableSolveBidiagonalBwdExactWithSteps
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : Array (ℤ × ℤ) × ℕ :=
  let stIn := runBwdRevSteps t1 (read1D Y) t1
  let revArr := computableSolveBidiagonalFwdExact q t1 c1 c0 stIn.outTape
  let stOut := runReverseSteps t1 (read1D revArr) t1
  (stOut.outTape, stOut.outTape.size)

/-- Pure-integer backward cyclic bidiagonal column solver (`computableSolveBidiagonalBwdExact`, `[MS]` §§5.1–5.2),
exact integer counterpart of `solveBidiagonalBwdQuantized`. -/
def computableSolveBidiagonalBwdExact
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (computableSolveBidiagonalBwdExactWithSteps q t1 c0 c1 Y).1

@[simp]
theorem computableSolveBidiagonalBwdExactWithSteps_fst
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalBwdExactWithSteps q t1 c0 c1 Y).1 =
      computableSolveBidiagonalBwdExact q t1 c0 c1 Y := rfl

@[simp]
theorem computableSolveBidiagonalBwdExactWithSteps_snd
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalBwdExactWithSteps q t1 c0 c1 Y).2 = t1 := by
  simp [computableSolveBidiagonalBwdExactWithSteps]

/-- All internal array-build, forward-seek, and backward-reversal steps executed inside a single
backward column solve (`zPartArr.size + zHomArr.size + stIn.steps + stOut.steps`) are bounded by
`6 * t1 = 6 * (computableSolveBidiagonalBwdExactWithSteps q t1 c0 c1 Y).2` for all `1 ≤ t1`. -/
theorem computableSolveBidiagonalBwd_full_internal_steps_le
    (q t1 : ℕ) (ht1 : 1 ≤ t1) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    let stIn := runBwdRevSteps t1 (read1D Y) t1
    let zPartArr := buildComputableZPartFwdExact q c1 c0 stIn.outTape (t1 - 1)
    let zHomArr := buildComputableZHomFwdExact q c1 c0 (t1 - 1)
    let revArr := computableSolveBidiagonalFwdExact q t1 c1 c0 stIn.outTape
    let stOut := runReverseSteps t1 (read1D revArr) t1
    zPartArr.size + zHomArr.size + stIn.steps + stOut.steps ≤
      6 * (computableSolveBidiagonalBwdExactWithSteps q t1 c0 c1 Y).2 := by
  dsimp only
  rw [size_buildComputableZPartFwdExact, size_buildComputableZHomFwdExact,
      runBwdRevSteps_steps, runReverseSteps_steps,
      computableSolveBidiagonalBwdExactWithSteps_snd]
  split_ifs <;> omega

/-- **Exact Semantic Equivalence of `computableSolveBidiagonalBwdExact` and `solveBidiagonalBwdQuantized`**: -/
theorem toScaledComplex_computableSolveBidiagonalBwdExact_eq
    (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (u1 : ℕ) (hu1 : u1 < t1) :
    toScaledComplex q (read1D (computableSolveBidiagonalBwdExact q t1 c0 c1 Y) u1) =
      solveBidiagonalBwdQuantized q t1 (toScaledComplex q c0) (toScaledComplex q c1)
        (fun k => toScaledComplex q (read1D Y k)) u1 := by
  dsimp only [computableSolveBidiagonalBwdExact, computableSolveBidiagonalBwdExactWithSteps]
  rw [read1D_runReverseSteps_eq t1 _ t1 u1 hu1]
  rw [toScaledComplex_computableSolveBidiagonalFwdExact_eq q t1 c1 c0 _ (t1 - 1 - u1) (by omega),
      solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev]
  refine solveBidiagonalFwdQuantized_congr_lt q t1 (toScaledComplex q c1) (toScaledComplex q c0)
    _ _ (fun k hk => ?_) (t1 - 1 - u1) (by omega)
  rw [read1D_runBwdRevSteps_eq t1 (read1D Y) t1 k hk]
  dsimp only [bwdRevRHS]
  split_ifs <;> rfl

/-- Pure-integer step of `zPartNyqQuantized`: `complexQuantize q (Y(u1 + 1) / c0 - zPart(u1))`. -/
def gNyqStepQuantize (q : ℕ) (c0 y prev : ℤ × ℤ) : ℤ × ℤ :=
  if c0.1 * c0.1 + c0.2 * c0.2 = 0 then
    gRescale q q (gNeg prev)
  else
    gRatioQuantize q y c0 prev c0 (0, 0) (0, 0)

theorem toScaledComplex_gNyqStepQuantize_eq (q : ℕ) (c0 y prev : ℤ × ℤ) :
    toScaledComplex q (gNyqStepQuantize q c0 y prev) =
      complexQuantize q (toScaledComplex q y / toScaledComplex q c0 - toScaledComplex q prev) := by
  unfold gNyqStepQuantize
  split_ifs with h0
  · have hc0_1 : c0.1 = 0 := by nlinarith
    have hc0_2 : c0.2 = 0 := by nlinarith
    have hc0_zero : toScaledComplex q c0 = 0 := by
      apply Complex.ext <;> simp [toScaledComplex, hc0_1, hc0_2]
    rw [hc0_zero, div_zero, zero_sub, toScaledComplex_gRescale_eq, toScaledComplex_gNeg]
  · rw [toScaledComplex_gRatioQuantize_eq]
    have hc0_ne : toScaledComplex q c0 ≠ 0 := by
      intro hc
      have hre : (c0.1 : ℝ) / (2 : ℝ) ^ (q + 2) = 0 := by
        simpa [toScaledComplex] using congrArg Complex.re hc
      have him : (c0.2 : ℝ) / (2 : ℝ) ^ (q + 2) = 0 := by
        simpa [toScaledComplex] using congrArg Complex.im hc
      have hpow : (2 : ℝ) ^ (q + 2) ≠ 0 := by positivity
      have h1 : c0.1 = 0 := by exact_mod_cast (div_eq_zero_iff.mp hre).resolve_right hpow
      have h2 : c0.2 = 0 := by exact_mod_cast (div_eq_zero_iff.mp him).resolve_right hpow
      exact h0 (by simp [h1, h2])
    congr 1
    simp only [toScaledComplex_zero, zero_mul, add_zero]
    field_simp [hc0_ne]

/-- Single-pass pure-integer array builder for `zPartNyqQuantized`. -/
def buildComputableZPartNyqExact (q : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : ℕ → Array (ℤ × ℤ)
  | 0 => #[(0, 0)]
  | n + 1 =>
    let arr := buildComputableZPartNyqExact q c0 Y n
    let prev := read1D arr n
    let y_next := read1D Y (n + 1)
    arr.push (gNyqStepQuantize q c0 y_next prev)

@[simp]
theorem size_buildComputableZPartNyqExact (q : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) :
    (buildComputableZPartNyqExact q c0 Y n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildComputableZPartNyqExact, ih]

theorem toScaledComplex_read1D_buildComputableZPartNyqExact_eq
    (q : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n u1 : ℕ) (hu1 : u1 ≤ n) :
    toScaledComplex q (read1D (buildComputableZPartNyqExact q c0 Y n) u1) =
      zPartNyqQuantized q (toScaledComplex q c0)
        (fun k => toScaledComplex q (read1D Y k)) u1 := by
  induction n generalizing u1 with
  | zero =>
    have hu0 : u1 = 0 := by omega
    subst hu0
    exact toScaledComplex_zero q
  | succ n ih =>
    dsimp only [buildComputableZPartNyqExact]
    have hsize := size_buildComputableZPartNyqExact q c0 Y n
    rw [read1D_push _ _ u1 (by omega), hsize]
    split_ifs with hlt
    · exact ih u1 (by omega)
    · have hu1_eq : u1 = n + 1 := by omega
      subst hu1_eq
      dsimp only [zPartNyqQuantized]
      rw [toScaledComplex_gNyqStepQuantize_eq, ih n le_rfl]

/-- Signed alternating term `(-1)^v * z` in `ℤ × ℤ`. -/
def gAltTerm (v : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  if v % 2 = 0 then z else gNeg z

theorem toScaledComplex_gAltTerm (p v : ℕ) (z : ℤ × ℤ) :
    toScaledComplex p (gAltTerm v z) = (-1 : ℂ) ^ v * toScaledComplex p z := by
  unfold gAltTerm
  rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
  · obtain ⟨k, hk⟩ : 2 ∣ v := Nat.dvd_of_mod_eq_zero h0
    rw [if_pos h0, hk, pow_mul, neg_one_sq, one_pow, one_mul]
  · have hne : v % 2 ≠ 0 := by omega
    have hdiv : v = 2 * (v / 2) + 1 := by omega
    rw [if_neg hne, toScaledComplex_gNeg]
    conv_rhs => rw [hdiv, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one, neg_one_mul]

theorem toScaledComplex_sum_range (p m : ℕ) (f : ℕ → ℤ × ℤ) :
    toScaledComplex p (∑ v ∈ Finset.range m, f v) =
      ∑ v ∈ Finset.range m, toScaledComplex p (f v) := by
  induction m with
  | zero => exact toScaledComplex_zero p
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    exact toScaledComplex_gAdd p _ _

/-- Step-instrumented pure-integer Nyquist column solver (`computableSolveNyquistExactWithSteps`, `[MS]` §§5.1–5.2):
uses `runSequentialScanSteps` and returns `(stOut.outTape, stOut.steps)`. -/
def computableSolveNyquistExactWithSteps
    (q t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) : Array (ℤ × ℤ) × ℕ :=
  let zPartArr := buildComputableZPartNyqExact q c0 Y (t1 - 1)
  let alt_part : ℤ × ℤ := sumRangePair (fun v => gAltTerm v (read1D zPartArr v)) t1
  let diff : ℤ × ℤ := gQuantizeRat (alt_q.1 - alt_part.1) (alt_q.2 - alt_part.2) (t1 : ℤ)
  let stOut := runSequentialScanSteps (fun u1 =>
    gRescale q q (gAdd (read1D zPartArr u1) (gAltTerm u1 diff))) t1
  (stOut.outTape, stOut.steps)

/-- Pure-integer Nyquist column solver (`computableSolveNyquistExact`, `[MS]` §§5.1–5.2),
exact integer counterpart of `solveNyquistQuantized`. -/
def computableSolveNyquistExact
    (q t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) : Array (ℤ × ℤ) :=
  (computableSolveNyquistExactWithSteps q t1 c0 Y alt_q).1

@[simp]
theorem computableSolveNyquistExactWithSteps_fst
    (q t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) :
    (computableSolveNyquistExactWithSteps q t1 c0 Y alt_q).1 =
      computableSolveNyquistExact q t1 c0 Y alt_q := rfl

@[simp]
theorem computableSolveNyquistExactWithSteps_snd
    (q t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) :
    (computableSolveNyquistExactWithSteps q t1 c0 Y alt_q).2 = t1 := by
  simp [computableSolveNyquistExactWithSteps]

/-- **Exact Semantic Equivalence of `computableSolveNyquistExact` and `solveNyquistQuantized`**: -/
theorem toScaledComplex_computableSolveNyquistExact_eq
    (q t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) (u1 : ℕ) (hu1 : u1 < t1) :
    toScaledComplex q (read1D (computableSolveNyquistExact q t1 c0 Y alt_q) u1) =
      solveNyquistQuantized q t1 (toScaledComplex q c0)
        (fun k => toScaledComplex q (read1D Y k)) (toScaledComplex q alt_q) u1 := by
  have ht1_pos : 0 < t1 := by omega
  have ht1_real : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1_pos
  dsimp only [computableSolveNyquistExact, computableSolveNyquistExactWithSteps,
    solveNyquistQuantized]
  rw [read1D_runSequentialScanSteps_eq _ t1 u1 hu1]
  rw [sumRangePair_eq_sum]
  set zPartArr := buildComputableZPartNyqExact q c0 Y (t1 - 1)
  set alt_part : ℤ × ℤ := ∑ v ∈ Finset.range t1, gAltTerm v (read1D zPartArr v)
  set diff : ℤ × ℤ := gQuantizeRat (alt_q.1 - alt_part.1) (alt_q.2 - alt_part.2) (t1 : ℤ)
  have halt_part :
      toScaledComplex q alt_part =
        ∑ v ∈ Finset.range t1,
          (-1 : ℂ) ^ v * zPartNyqQuantized q (toScaledComplex q c0)
            (fun k => toScaledComplex q (read1D Y k)) v := by
    dsimp only [alt_part]
    rw [toScaledComplex_sum_range]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv_lt : v < t1 := Finset.mem_range.mp hv
    rw [toScaledComplex_gAltTerm,
        toScaledComplex_read1D_buildComputableZPartNyqExact_eq q c0 Y (t1 - 1) v (by omega)]
  have hdiff :
      toScaledComplex q diff =
        complexQuantize q ((toScaledComplex q alt_q - toScaledComplex q alt_part) / (t1 : ℂ)) := by
    refine toScaledComplex_gQuantizeRat_eq_complexQuantize q
      (alt_q.1 - alt_part.1) (alt_q.2 - alt_part.2) (t1 : ℤ) (by positivity)
      ((toScaledComplex q alt_q - toScaledComplex q alt_part) / (t1 : ℂ)) ?_ ?_
    · have hdiv : (toScaledComplex q alt_q - toScaledComplex q alt_part) / (t1 : ℂ) =
          (toScaledComplex q alt_q - toScaledComplex q alt_part) * ((1 / (t1 : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hdiv]
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, toScaledComplex]
      push_cast
      field_simp [ht1_real.ne']
    · have hdiv : (toScaledComplex q alt_q - toScaledComplex q alt_part) / (t1 : ℂ) =
          (toScaledComplex q alt_q - toScaledComplex q alt_part) * ((1 / (t1 : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hdiv]
      simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, toScaledComplex]
      push_cast
      field_simp [ht1_real.ne']
      ring
  rw [toScaledComplex_gRescale_eq, toScaledComplex_gAdd, toScaledComplex_gAltTerm,
      toScaledComplex_read1D_buildComputableZPartNyqExact_eq q c0 Y (t1 - 1) u1 (by omega),
      hdiff, halt_part]

/-- Pure-integer contiguous midpoint-row alternating sum (`computableNyquistAltSumContiguous`, `[MS]` §§5.1–5.2):
reads contiguous elements `read1D xMidRow j2` from the transposed midpoint row `xRows[t1 / 2]`
with zero stride-`t1` random access (`t1 / 2 + t1 * j2`). -/
def computableNyquistAltSumContiguous
    (p_in q r : ℕ) (xMidRow : Array (ℤ × ℤ)) : ℤ × ℤ :=
  let altSum : ℤ × ℤ := sumRangePair (fun j2 => gAltTerm j2 (read1D xMidRow j2)) r
  let S_out : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let den : ℤ := (r : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ)
  gQuantizeRat (-altSum.2 * S_out) (altSum.1 * S_out) den

theorem toScaledComplex_computableNyquistAltSumContiguous_eq
    (p_in q t1 r : ℕ) (hr : 0 < r)
    (xMidRow : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ j2 < r, x (t1 / 2 + t1 * j2) = toScaledComplex p_in (read1D xMidRow j2)) :
    toScaledComplex q (computableNyquistAltSumContiguous p_in q r xMidRow) =
      complexQuantize q (nyquistAltSum t1 r x) := by
  unfold computableNyquistAltSumContiguous nyquistAltSum
  dsimp only
  rw [sumRangePair_eq_sum]
  set altSum : ℤ × ℤ := ∑ j2 ∈ Finset.range r, gAltTerm j2 (read1D xMidRow j2)
  have haltSum_eq :
      (∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)) =
        toScaledComplex p_in altSum := by
    dsimp only [altSum]
    rw [toScaledComplex_sum_range]
    refine Finset.sum_congr rfl fun j2 hj2 => ?_
    have hj2_lt : j2 < r := Finset.mem_range.mp hj2
    rw [toScaledComplex_gAltTerm, ← hx j2 hj2_lt]
  rw [haltSum_eq]
  have hden : (0 : ℤ) ≤ (r : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
  have hr_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hpow_out : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
  refine toScaledComplex_gQuantizeRat_eq_complexQuantize q
    (-altSum.2 * ((2 ^ (q + 2) : ℕ) : ℤ)) (altSum.1 * ((2 ^ (q + 2) : ℕ) : ℤ))
    ((r : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ)) hden
    ((Complex.I / (r : ℂ)) * toScaledComplex p_in altSum) ?_ ?_
  · have hdiv : (Complex.I / (r : ℂ)) * toScaledComplex p_in altSum =
        Complex.I * toScaledComplex p_in altSum * ((1 / (r : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hdiv]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, toScaledComplex]
    push_cast
    field_simp [hr_real.ne', hpow_out.ne']
  · have hdiv : (Complex.I / (r : ℂ)) * toScaledComplex p_in altSum =
        Complex.I * toScaledComplex p_in altSum * ((1 / (r : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hdiv]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, toScaledComplex]
    push_cast
    field_simp [hr_real.ne', hpow_out.ne']

/-- Pure-integer midpoint-row alternating sum `complexQuantize q (nyquistAltSum t1 r x)`
for `x` at input precision `p_in`. -/
def computableNyquistAltSumExact
    (p_in q t1 r : ℕ) (xArr : Array (ℤ × ℤ)) : ℤ × ℤ :=
  let altSum : ℤ × ℤ := sumRangePair (fun j2 => gAltTerm j2 (read1D xArr (t1 / 2 + t1 * j2))) r
  let S_out : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let den : ℤ := (r : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ)
  gQuantizeRat (-altSum.2 * S_out) (altSum.1 * S_out) den

theorem toScaledComplex_computableNyquistAltSumExact_eq
    (p_in q t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < t1 * r, x k = toScaledComplex p_in (read1D xArr k)) :
    toScaledComplex q (computableNyquistAltSumExact p_in q t1 r xArr) =
      complexQuantize q (nyquistAltSum t1 r x) := by
  unfold computableNyquistAltSumExact nyquistAltSum
  dsimp only
  rw [sumRangePair_eq_sum]
  set altSum : ℤ × ℤ := ∑ j2 ∈ Finset.range r, gAltTerm j2 (read1D xArr (t1 / 2 + t1 * j2))
  have haltSum_eq :
      (∑ j2 ∈ Finset.range r, (-1 : ℂ) ^ j2 * x (t1 / 2 + t1 * j2)) =
        toScaledComplex p_in altSum := by
    dsimp only [altSum]
    rw [toScaledComplex_sum_range]
    refine Finset.sum_congr rfl fun j2 hj2 => ?_
    have hj2_lt : j2 < r := Finset.mem_range.mp hj2
    have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
    have hidx_lt : t1 / 2 + t1 * j2 < t1 * r := by
      have hj2_le : j2 + 1 ≤ r := hj2_lt
      calc t1 / 2 + t1 * j2 < t1 + t1 * j2 := Nat.add_lt_add_right hhalf_lt _
        _ = t1 * (j2 + 1) := by ring
        _ ≤ t1 * r := Nat.mul_le_mul_left t1 hj2_le
    rw [toScaledComplex_gAltTerm, ← hx _ hidx_lt]
  rw [haltSum_eq]
  have hden : (0 : ℤ) ≤ (r : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
  have hr_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hpow_out : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
  refine toScaledComplex_gQuantizeRat_eq_complexQuantize q
    (-altSum.2 * ((2 ^ (q + 2) : ℕ) : ℤ)) (altSum.1 * ((2 ^ (q + 2) : ℕ) : ℤ))
    ((r : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ)) hden
    ((Complex.I / (r : ℂ)) * toScaledComplex p_in altSum) ?_ ?_
  · have hdiv : (Complex.I / (r : ℂ)) * toScaledComplex p_in altSum =
        Complex.I * toScaledComplex p_in altSum * ((1 / (r : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hdiv]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, toScaledComplex]
    push_cast
    field_simp [hr_real.ne', hpow_out.ne']
  · have hdiv : (Complex.I / (r : ℂ)) * toScaledComplex p_in altSum =
        Complex.I * toScaledComplex p_in altSum * ((1 / (r : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hdiv]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, toScaledComplex]
    push_cast
    field_simp [hr_real.ne', hpow_out.ne']

/-- Exact unit 4th root of unity `i^m ∈ {(1, 0), (0, 1), (-1, 0), (0, -1)}` in `ℤ × ℤ`. -/
def unitFourthRoot (m : ℕ) : ℤ × ℤ :=
  match m % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

theorem stdChar_div_four_eq (m : ℕ) :
    stdChar ((m : ℝ) / 4) =
      ⟨((unitFourthRoot m).1 : ℝ), ((unitFourthRoot m).2 : ℝ)⟩ := by
  have h1 : stdChar ((m : ℝ) / 4) = Complex.I ^ m := by
    unfold stdChar
    have harg : (((2 * Real.pi * ((m : ℝ) / 4) : ℝ) : ℂ) * Complex.I) =
        (m : ℕ) * ((Real.pi / 2 : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  rw [h1]
  have hdiv : m = 4 * (m / 4) + m % 4 := (Nat.div_add_mod m 4).symm
  conv_lhs => rw [hdiv, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  unfold unitFourthRoot
  have hmod : m % 4 < 4 := Nat.mod_lt m (by decide)
  interval_cases m % 4 <;>
    (apply Complex.ext <;> simp [pow_two, pow_three])

theorem stdChar_div_of_dvd_four (R m : ℕ) (hR : 0 < R) (hdvd : R ∣ 4) :
    stdChar ((m : ℝ) / (R : ℝ)) =
      ⟨((unitFourthRoot (m * (4 / R))).1 : ℝ), ((unitFourthRoot (m * (4 / R))).2 : ℝ)⟩ := by
  have hmul : (4 / R) * R = 4 := Nat.div_mul_cancel hdvd
  have hR_ne : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have harg : (m : ℝ) / (R : ℝ) = ((m * (4 / R) : ℕ) : ℝ) / 4 := by
    have h4 : ((4 / R : ℕ) : ℝ) * (R : ℝ) = 4 := by exact_mod_cast hmul
    push_cast
    rw [div_eq_div_iff hR_ne (by norm_num)]
    calc (m : ℝ) * 4 = (m : ℝ) * (((4 / R : ℕ) : ℝ) * (R : ℝ)) := by rw [h4]
      _ = (m : ℝ) * ((4 / R : ℕ) : ℝ) * (R : ℝ) := by ring
  rw [harg]
  exact stdChar_div_four_eq (m * (4 / R))

/-- **Legacy Intermediate Step ($R \mid 4$ Leaf)**: Pure-integer leaf DFT
`complexQuantize p (dft1D R x u)` for leaf sizes `R ∣ 4` (`R ∈ {1, 2, 4}`) using exact fourth
roots of unity (`step := 4 / R`). Superseded in the headline pipeline (`PaperHeadlinePipeline.lean`)
by `computableBaseRadix2FFTWithProgramCost` for arbitrary power-of-two leaves $R = 2^K \le 4 p^2$. -/
def computableBaseDFTExact (p_in p R : ℕ) (xArr : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  let step := 4 / R
  let S_out : ℤ := ((2 ^ (p + 2) : ℕ) : ℤ)
  let den : ℤ := (R : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ)
  Array.ofFn (fun u : Fin R =>
    let sumPair : ℤ × ℤ := sumRangePair
      (fun j => gMulUnit (read1D xArr j) (unitFourthRoot (j * u.val * step))) R
    gQuantizeRat (sumPair.1 * S_out) (sumPair.2 * S_out) den)

theorem toScaledComplex_computableBaseDFTExact_eq
    (p_in p R : ℕ) (hR : 0 < R) (hdvd : R ∣ 4)
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < R, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < R) :
    toScaledComplex p (read1D (computableBaseDFTExact p_in p R xArr) u) =
      complexQuantize p (dft1D R x u) := by
  unfold computableBaseDFTExact dft1D
  rw [read1D_ofFn_of_lt R _ hu]
  dsimp only
  rw [sumRangePair_eq_sum]
  set step := 4 / R
  set sumPair : ℤ × ℤ := ∑ j ∈ Finset.range R,
    gMulUnit (read1D xArr j) (unitFourthRoot (j * u * step))
  have hsum_eq :
      (∑ j ∈ Finset.range R, x j * stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))) =
        toScaledComplex p_in sumPair := by
    dsimp only [sumPair]
    rw [toScaledComplex_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < R := Finset.mem_range.mp hj
    rw [hx j hj_lt, stdChar_div_of_dvd_four R (j * u) hR hdvd]
    apply Complex.ext <;>
      (simp only [Complex.mul_re, Complex.mul_im, toScaledComplex, gMulUnit];
       push_cast; ring)
  rw [hsum_eq]
  have hden : (0 : ℤ) ≤ (R : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
  have hR_real : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hR
  have hpow_out : (0 : ℝ) < (2 : ℝ) ^ (p + 2) := by positivity
  refine toScaledComplex_gQuantizeRat_eq_complexQuantize p
    (sumPair.1 * ((2 ^ (p + 2) : ℕ) : ℤ)) (sumPair.2 * ((2 ^ (p + 2) : ℕ) : ℤ))
    ((R : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ)) hden
    ((1 / (R : ℂ)) * toScaledComplex p_in sumPair) ?_ ?_
  · have hdiv : (1 / (R : ℂ)) * toScaledComplex p_in sumPair =
        toScaledComplex p_in sumPair * ((1 / (R : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hdiv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      toScaledComplex]
    push_cast
    field_simp [hR_real.ne', hpow_out.ne']
  · have hdiv : (1 / (R : ℂ)) * toScaledComplex p_in sumPair =
        toScaledComplex p_in sumPair * ((1 / (R : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hdiv]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      toScaledComplex]
    push_cast
    field_simp [hR_real.ne', hpow_out.ne']
    ring

/-- Direct computable odd-stride multiplier `w` for column `u2` at radix-2 depth `m` (`t1 = 2^m`),
using Hensel-lifting `computableOddStrideInvPow2` (zero `ZMod` or `WellFounded.fix`). -/
def computableOddStrideFactor (m u2 : ℕ) : ℕ :=
  if m = 0 then 1 else computableOddStrideInvPow2 m u2 1

@[simp]
theorem computableOddStrideFactor_eq_oddStrideFactor (m u2 : ℕ) :
    computableOddStrideFactor m u2 = oddStrideFactor m u2 := by
  unfold computableOddStrideFactor oddStrideFactor
  rw [computableOddStrideInvPow2_eq_oddStrideInvPow2]

theorem toScaledComplex_realQuantizeInt_pair (p : ℕ) (z : ℂ) :
    toScaledComplex p (realQuantizeInt p z.re, realQuantizeInt p z.im) =
      complexQuantize p z := by
  apply Complex.ext <;>
    (change ((realQuantizeInt p _ : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) = realQuantize p _;
     rw [realQuantize_eq_realQuantizeInt_div])

theorem toScaledComplex_realQuantizeInt_real (p : ℕ) (x : ℝ) :
    toScaledComplex p (realQuantizeInt p x, 0) = (realQuantize p x : ℂ) := by
  apply Complex.ext
  · change ((realQuantizeInt p x : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) = (realQuantize p x : ℂ).re
    rw [Complex.ofReal_re, realQuantize_eq_realQuantizeInt_div]
  · simp [toScaledComplex]

theorem oddStrideInvPow2_lt (k1 u2 u1 : ℕ) :
    oddStrideInvPow2 k1 u2 u1 < 2 ^ k1 := by
  haveI : NeZero (2 ^ k1) := ⟨pow_ne_zero _ (by decide)⟩
  unfold oddStrideInvPow2
  cases u2 <;> exact ZMod.val_lt _

/-- Pure-integer input chunk packer at input precision `p_in = b` (`scale = 2^(b + 2) = 4 * 2^b`):
splits `A` and `B` via the balanced divide-and-conquer binary-tree `splitChunksTree`, converts the
resulting chunk lists to `Array ℕ` once in $O(k_1 + k_2)$, and scans `0 .. R0 - 1` with $O(1)$
array lookups `read1D asArr j` and `read1D bsArr j` (avoiding $\Theta(R_0^2)$ linked-list `List.getD`
traversals). -/
def computablePackChunksExact (b k1 k2 R0 : ℕ) (A B : ℕ) : Array (ℤ × ℤ) :=
  let asArr := (splitChunksTree b k1 A).toArray
  let bsArr := (splitChunksTree b k2 B).toArray
  (runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0).outTape

theorem toScaledComplex_computablePackChunksExact_eq
    (b k1 k2 R0 A B j : ℕ) (hj : j < R0) :
    toScaledComplex b (read1D (computablePackChunksExact b k1 k2 R0 A B) j) =
      packNormalizedChunks b k1 k2 A B j := by
  unfold computablePackChunksExact packNormalizedChunks
  rw [read1D_runSequentialScanSteps_eq _ R0 j hj]
  simp only [read1D_toArray_eq_getD, splitChunksTree_eq_splitChunks]
  have hpow : (2 : ℝ) ^ (b + 2) = 4 * ((2 ^ b : ℕ) : ℝ) := by
    push_cast
    ring
  have h2b : ((2 ^ b : ℕ) : ℝ) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [← Complex.ofReal_div, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      toScaledComplex]
    rw [hpow]
    push_cast
    field_simp [h2b]
    ring
  · simp only [← Complex.ofReal_div, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      toScaledComplex]
    rw [hpow]
    push_cast
    field_simp [h2b]
    ring

end IntMul
