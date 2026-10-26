import IntMul.ExecutableAlgorithm.QuantizedFastDFT

namespace IntMul

/-! ## Multi-Level Schedule Builder, Intrinsic Bit-Cost Model & Parameter-Free `O(n log n)` Multiplier -/

/-- Recursive multi-level balanced Sinc-Gaussian schedule builder (`buildQuantizedSpec L p K`, `[MS]` §7):
- At `L = 0` (leaf): `.base p (2 ^ K)`,
- At `L + 1` (internal step): `quantizedBoxGaussianStepSpec p K (buildQuantizedSpec L (pChild p K) (K - K / 2))`. -/
def buildQuantizedSpec : ℕ → ℕ → ℕ → QuantizedFastDFTSpec
  | 0, p, K => .base p (2 ^ K)
  | L + 1, p, K =>
    quantizedBoxGaussianStepSpec p K (buildQuantizedSpec L (pChild p K) (K - K / 2))

/-- For any depth `L`, target precision `p`, and log-size `K`, `(buildQuantizedSpec L p K).size = 2 ^ K`. -/
@[simp]
theorem buildQuantizedSpec_size (L p K : ℕ) :
    (buildQuantizedSpec L p K).size = 2 ^ K := by
  cases L with
  | zero => rfl
  | succ L =>
    dsimp [buildQuantizedSpec, quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.size]
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]

/-- For any depth `L`, target precision `p`, and log-size `K`, `(buildQuantizedSpec L p K).p = p`. -/
@[simp]
theorem buildQuantizedSpec_p (L p K : ℕ) :
    (buildQuantizedSpec L p K).p = p := by
  cases L <;> rfl

/-- **Multi-Level Validity of `buildQuantizedSpec` (`[MS]` §7)**:
For any recursion depth `L`, root precision `8 ≤ p`, and log-length `2 ^ L ≤ K`,
the multi-level recursion specification `buildQuantizedSpec L p K` satisfies
`QuantizedFastDFTSpec.Valid`. -/
theorem buildQuantizedSpec_valid (L p K : ℕ) (hp : 8 ≤ p) (hK : 2 ^ L ≤ K) :
    (buildQuantizedSpec L p K).Valid := by
  induction L generalizing p K with
  | zero =>
    exact QuantizedFastDFTSpec.Valid.base p (2 ^ K)
  | succ L ih =>
    dsimp only [buildQuantizedSpec]
    have hpow1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hpow_succ : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
    have hK2 : 2 ≤ K := by omega
    have hK_child : 2 ^ L ≤ K - K / 2 := by omega
    have hp_child : 8 ≤ pChild p K := by
      unfold pChild pWork
      omega
    exact quantizedBoxGaussianStepSpec_valid p K hp hK2
      (buildQuantizedSpec L (pChild p K) (K - K / 2))
      (buildQuantizedSpec_size L (pChild p K) (K - K / 2))
      (buildQuantizedSpec_p L (pChild p K) (K - K / 2))
      (ih (pChild p K) (K - K / 2) hp_child hK_child)

/-- Cost of a fixed-point addition, subtraction, or bit-shift at bit-width `w`. -/
def addBitCost (w : ℕ) : ℕ := w

/-- Cost of a fixed-point multiplication at bit-width `w` under the classical non-circular
Schönhage–Strassen `M(w) = w * (⌊log₂ w⌋ + 1) * (⌊log₂(⌊log₂ w⌋ + 1)⌋ + 1)` bit-operation model
(pricing the `Θ(log² n)`-bit Kronecker block multiplications and `2p'`-bit fixed-point products
without assuming an `O(n log n)` sub-multiplier). -/
def mulBitCost (w : ℕ) : ℕ :=
  w * (Nat.log2 w + 1) * (Nat.log2 (Nat.log2 w + 1) + 1)

/-- Schönhage–Strassen sub-multiplier rate `P * (⌊log₂ P⌋ + 1) * (⌊log₂(⌊log₂ P⌋ + 1)⌋ + 1)` at
precision bound `P`. -/
def subMulRate (P : ℕ) : ℕ :=
  P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)

/-- For any parent precision `p` and log-length `K`, `p ≤ pChild p K` and the full fixed-point
word bit-width per real coordinate (carrying up to `p + 2 * K + 12` integer/headroom bits plus
`2 * pChild p K + 2` fractional/sign bits) is bounded above by `4 * pChild p K`. -/
theorem fixedPointWordBits_le_four_mul_pChild (p K : ℕ) :
    p ≤ pChild p K ∧ p + 2 * pChild p K + 2 ≤ 4 * pChild p K := by
  rw [pChild_eq_additive]
  omega

/-- Bit-operation cost of the addition-only Radix-2 Synthetic FFT butterflies over `R_r = ℂ[y]/(y^r + 1)`
at full fixed-point word bit-width `4 * p'` per real coordinate (`8 * p'` bits per complex entry). -/
def syntheticFFTStepBitCost (t1 r p' : ℕ) : ℕ :=
  2 * syntheticFFTRadix2AddOps r (Nat.log2 t1) * addBitCost (4 * p')

/-- Bit-operation cost of Overlap-Add Kronecker spreading at working precision `p'`:
for each of the `t1` rows and `numBlocks = kroneckerSpreadNumBlocks (2 * p') r` Overlap-Add blocks
of effective width `W_eff = effectiveFilterWidth (2 * p') r` and slot width `slotBits = 6 * p'`,
executes `2` packed integer multiplications (`Re` and `Im`) of bit-length `W_eff * slotBits`
plus `4 * W_eff` slot additions/extractions at bit-width `slotBits`. -/
def kroneckerSpreadStepBitCost (t1 r p' : ℕ) : ℕ :=
  let W_eff := effectiveFilterWidth (2 * p') r
  let numBlocks := kroneckerSpreadNumBlocks (2 * p') r
  let slotBits := 6 * p'
  t1 * numBlocks * (2 * mulBitCost (W_eff * slotBits) + 4 * W_eff * addBitCost slotBits)

/-- Actual operand-level bit-operation cost of `kroneckerSincGaussianSpreadArray` at a `.step` node
with parameters `(α, p, K, t1, r)` on input `x : ℕ → ℂ`: sums the actual `mulBitCost` and `addBitCost`
of every executed `polyMulKroneckerSigned` block call (`Re` and `Im`) using the actual polynomial
lengths `.length` and dynamic bit-strides `kroneckerBitStride` of `kroneckerSpreadRowBlockRe`,
`kroneckerSpreadRowBlockIm`, and `kroneckerSpreadFilterTapsFolded` (`[MS]` §6.2, Theorem 6.3). -/
noncomputable def executedKroneckerSpreadStepBitCost (α : ℝ) (p K t1 r : ℕ) (x : ℕ → ℂ) : ℕ :=
  let p' := pChild p K
  let q := 2 * p'
  let m1 := 2 * p'
  let W_eff := effectiveFilterWidth m1 r
  ∑ j1 ∈ Finset.range t1,
    ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
      (mulBitCost
          ((kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length *
            kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
        mulBitCost
          ((kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length *
            kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
        2 * W_eff *
          addBitCost
            (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
        2 * W_eff *
          addBitCost
            (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)))

/-- Bit-operation cost of pre-twists (`4` real muls + `2` real adds per entry),
post-twists (`4` real muls + `2` real adds per entry), step-rounded 3-regime bidiagonal/Nyquist
deconvolution (`solveBidiagonalFwdQuantized`, `solveNyquistQuantized`, `solveBidiagonalBwdQuantized`,
including `zPart*Quantized` steps, `zHom*Quantized` power steps, boundary `Z0`/`Z_last`/`diff`, and
`Z0 * zHom` combine: `≤ 8` real muls/divs + `12` real adds/quantizations per entry), and node
sub-step/output quantization at full fixed-point word bit-width `4 * p'` per real coordinate. -/
def twistAndSolverStepBitCost (t1 r p' : ℕ) : ℕ :=
  t1 * r * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))

/-- Sequential tape-scan bit cost for streaming `numItems` records of `itemBitWidth` bits each. -/
def sequentialPassBitCost (numItems itemBitWidth : ℕ) : ℕ :=
  numItems * addBitCost itemBitWidth

/-- Multitape sequential bit-movement cost of transposing a `t1 × r` array of complex entries at
full fixed-point word bit-width `4 * p'` per real coordinate (`8 * p'` bits per complex entry)
via `(sequentialTapeTransposeWithPasses (Nat.log2 t1) r ...).2 = 2 * ⌊log₂ t₁⌋` sequential
tape passes (`1` `unshufflePass` + `1` `interleaveRunsPass` per halving stage, `[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def sequentialTransposeBitCost (t1 r p' : ℕ) : ℕ :=
  (sequentialTapeTransposeWithPasses (Nat.log2 t1) r (fun _ => (0 : ℂ))).2 *
    sequentialPassBitCost (t1 * r) (8 * p')

/-- Multitape sequential bit-movement cost of routing the odd-stride column permutation
`v1Of u2 u1` across all `r` columns of length `t1` via the `⌊log₂ t₁⌋`-stage sequential
2-tape routing network `sequentialAffineOddRouteWithPasses` (`2 * ⌊log₂ t₁⌋` passes: `1`
`unshufflePass` + `1` `interleaveParityPass` per stage) at `8 * p'` bits per complex entry
(`[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def sequentialColumnMergeSortBitCost (t1 r p' : ℕ) : ℕ :=
  (sequentialAffineOddRouteWithPasses (Nat.log2 t1) 1 0 (fun _ => (0 : ℂ))).2 *
    sequentialPassBitCost (t1 * r) (8 * p')

/-- Multitape linear-scan bit-movement cost for Kronecker slot packing/unpacking, sub-step rounding
scans, and sequential twiddle/filter-tap streaming across the `t1 × r` array at `8 * p'` bits per
complex entry (`[MS]` §3.2 & §6.2). -/
def sequentialLinearScanBitCost (t1 r p' : ℕ) : ℕ :=
  8 * sequentialPassBitCost (t1 * r) (8 * p')

/-- Total multitape-TM data-routing and sequential-streaming bit cost at recursion level `(t1, r, p')`
(`[MS]` §§3.2, 3.4, 7.2, Theorem 1):
- `2 * sequentialTransposeBitCost t1 r p'`:
  (1) input stride-`t1` gather `routedInputGather t1 r x` into row-contiguous `(j1, i)` layout for
      `kroneckerSincGaussianSpreadArray`, and
  (2) output transpose `routedTranspose2D t1 r Z` between `u2`-major column solver sweeps and
      `u = u1_tilde * r + u2` layout,
- `sequentialTransposeBitCost r t1 p'`:
  child-output transpose of the `t1 × r` child-transform matrix `qHat` into `r` column-major segments
  of length `t1` (`qHat_T_res = runMultiTapeTransposeWithSteps m_r t1`, priced at `2 * ⌊log₂ r⌋` passes),
- `sequentialColumnMergeSortBitCost t1 r p'`:
  odd-stride column routing `routedColumnEntry t1 v1Of qHat u2 u1` from child outputs `qHat` into
  `u1`-contiguous solver columns,
- `sequentialLinearScanBitCost t1 r p'`:
  `8` linear streaming passes for Kronecker packing/unpacking, twiddle streaming, and sub-step rounding. -/
def routingAndStreamingStepBitCost (t1 r p' : ℕ) : ℕ :=
  2 * sequentialTransposeBitCost t1 r p' +
    sequentialTransposeBitCost r t1 p' +
    sequentialColumnMergeSortBitCost t1 r p' +
    sequentialLinearScanBitCost t1 r p'

/-- Recursive sequential-tape transpose cost over `m = log₂ t₁` halving stages (`sequentialTapeTransposeWithPasses`):
at stage `0` (`1 × r` row vector), `0` tape passes are needed; at stage `m + 1` (`2^(m+1) × r` matrix),
executes `2` half-size transposes of `2^m × r` plus `2` sequential full-tape passes (`1` `unshufflePass` +
`1` `interleaveRunsPass`) over all `2^(m+1) * r` complex entries of bit-width `8 * p'`. -/
def recursiveTransposeTapeCost (r p' : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * recursiveTransposeTapeCost r p' m + 2 * sequentialPassBitCost (2 ^ (m + 1) * r) (8 * p')

/-- Recursive sequential-tape odd-stride column-routing cost over `m = log₂ t₁` stages
(`sequentialAffineOddRouteWithPasses`) for all `r` columns simultaneously: at stage `0`, `0` passes;
at stage `m + 1`, executes `1` `unshufflePass`, recursively routes the even and odd `2^m × r` halves,
and merges them in `1` `interleaveParityPass` (`2` sequential passes per stage) over all
`2^(m+1) * r` entries of width `8 * p'`. -/
def recursiveMergeSortTapeCost (r p' : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * recursiveMergeSortTapeCost r p' m + 2 * sequentialPassBitCost (2 ^ (m + 1) * r) (8 * p')

/-- Bit-operation cost of precomputing the `t1 * W_eff` Sinc-Gaussian window taps
(`W_eff = effectiveFilterWidth (2 * p') r`), passband `c0`/`c1` coefficients, and `zetaRoot`
twiddle factors at full fixed-point word bit-width `4 * p'`. -/
def precomputeStepBitCost (t1 r p' : ℕ) : ℕ :=
  let W_eff := effectiveFilterWidth (2 * p') r
  (t1 * W_eff + 4 * r) * mulBitCost (4 * p') + t1 * W_eff * addBitCost (4 * p')

/-- Root-level bit-operation cost for `R0 = 2 ^ K0` at root precision `p0`:
packing (`R0 * addBitCost p0`), pointwise squaring (`R0 * mulBitCost p0`),
and scaling/rounding/carry propagation (`2 * R0 * addBitCost p0`). -/
def rootPipelineBitCost (R0 p0 : ℕ) : ℕ :=
  R0 * (mulBitCost p0 + 3 * addBitCost p0)

/-- Schedule-level precomputation bit-operation cost across all levels of a `QuantizedFastDFTSpec`
(charging `precomputeStepBitCost t1 r (pChild p K)` once per recursion level for the shared
Sinc-Gaussian window taps, passband `c0`/`c1` coefficients, and `zetaRoot` twiddle tables). -/
def QuantizedFastDFTSpec.precomputeCost : QuantizedFastDFTSpec → ℝ
  | .base _ _ => 0
  | .step p K t1 r _c1 _v1Of child =>
    ((precomputeStepBitCost t1 r (pChild p K) : ℕ) : ℝ) + child.precomputeCost

/-- Non-negativity of `spec.precomputeCost` for every `spec : QuantizedFastDFTSpec`. -/
theorem QuantizedFastDFTSpec.precomputeCost_nonneg (spec : QuantizedFastDFTSpec) :
    0 ≤ spec.precomputeCost := by
  induction spec with
  | base p R =>
    dsimp [QuantizedFastDFTSpec.precomputeCost]
    positivity
  | step p K t1 r c1 v1Of child ih =>
    dsimp [QuantizedFastDFTSpec.precomputeCost]
    positivity

/-- Full raw-tap and series-evaluation precomputation bit-operation cost at step `(t1, r, p')` (`[MS]` §3.3 (Lemma 3.2, eq. (8)), §6.1 & §7.2):
- Evaluates all `t1 * (4 * p' + 1)` raw Sinc-Gaussian window taps (`m ∈ [-2 p', 2 p']` for each row `j1 < t1`)
  before folding modulo `W_eff = effectiveFilterWidth (2 * p') r`, plus `4 * r` passband (`c0`, `c1`) and
  `zetaRoot` twiddle entries,
- Charges `(4 * p' + 1)` multiplications and `(4 * p' + 1)` additions of width `4 * p'` per entry (pricing
  full `(4 p' + 1)`-term series/Horner/AGM evaluation of `sincGaussian`, `realErfScaled`, `cos`, `sin`),
- Plus `t1 * (4 * p' + 1)` additions of width `4 * p'` for folding the raw taps modulo `W_eff`. -/
def precomputeStepRawTapBitCost (t1 r p' : ℕ) : ℕ :=
  let rawTaps := t1 * (4 * p' + 1)
  (rawTaps + 4 * r) * (4 * p' + 1) * (mulBitCost (4 * p') + addBitCost (4 * p')) +
    rawTaps * addBitCost (4 * p')

/-- `precomputeStepRawTapBitCost` dominates `precomputeStepBitCost` for all `t1, r, p' : ℕ`. -/
theorem precomputeStepBitCost_le_precomputeStepRawTapBitCost (t1 r p' : ℕ) :
    precomputeStepBitCost t1 r p' ≤ precomputeStepRawTapBitCost t1 r p' := by
  unfold precomputeStepBitCost precomputeStepRawTapBitCost
  dsimp only
  have hW : effectiveFilterWidth (2 * p') r ≤ 4 * p' + 1 := by
    have := effectiveFilterWidth_le_full (2 * p') r
    omega
  have ht1W : t1 * effectiveFilterWidth (2 * p') r ≤ t1 * (4 * p' + 1) :=
    Nat.mul_le_mul_left t1 hW
  have h1 :
      (t1 * effectiveFilterWidth (2 * p') r + 4 * r) * mulBitCost (4 * p') ≤
        (t1 * (4 * p' + 1) + 4 * r) * (4 * p' + 1) *
          (mulBitCost (4 * p') + addBitCost (4 * p')) := by
    calc (t1 * effectiveFilterWidth (2 * p') r + 4 * r) * mulBitCost (4 * p')
        = (t1 * effectiveFilterWidth (2 * p') r + 4 * r) * 1 * mulBitCost (4 * p') := by ring
      _ ≤ (t1 * (4 * p' + 1) + 4 * r) * (4 * p' + 1) *
            (mulBitCost (4 * p') + addBitCost (4 * p')) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have h2 :
      t1 * effectiveFilterWidth (2 * p') r * addBitCost (4 * p') ≤
        t1 * (4 * p' + 1) * addBitCost (4 * p') :=
    Nat.mul_le_mul_right _ ht1W
  exact Nat.add_le_add h1 h2

/-- Schedule-level raw-tap and series-evaluation precomputation cost across all levels of a `QuantizedFastDFTSpec`. -/
def QuantizedFastDFTSpec.precomputeRawTapCost : QuantizedFastDFTSpec → ℝ
  | .base _ _ => 0
  | .step p K t1 r _c1 _v1Of child =>
    ((precomputeStepRawTapBitCost t1 r (pChild p K) : ℕ) : ℝ) + child.precomputeRawTapCost

/-- Non-negativity of `spec.precomputeRawTapCost` for every `spec : QuantizedFastDFTSpec`. -/
theorem QuantizedFastDFTSpec.precomputeRawTapCost_nonneg (spec : QuantizedFastDFTSpec) :
    0 ≤ spec.precomputeRawTapCost := by
  induction spec with
  | base p R =>
    dsimp [QuantizedFastDFTSpec.precomputeRawTapCost]
    positivity
  | step p K t1 r c1 v1Of child ih =>
    dsimp [QuantizedFastDFTSpec.precomputeRawTapCost]
    positivity

/-- `spec.precomputeCost ≤ spec.precomputeRawTapCost` for every `spec : QuantizedFastDFTSpec`. -/
theorem QuantizedFastDFTSpec.precomputeCost_le_precomputeRawTapCost (spec : QuantizedFastDFTSpec) :
    spec.precomputeCost ≤ spec.precomputeRawTapCost := by
  induction spec with
  | base p R =>
    dsimp [QuantizedFastDFTSpec.precomputeCost, QuantizedFastDFTSpec.precomputeRawTapCost]
    exact le_rfl
  | step p K t1 r c1 v1Of child ih =>
    dsimp [QuantizedFastDFTSpec.precomputeCost, QuantizedFastDFTSpec.precomputeRawTapCost]
    have hstep :
        ((precomputeStepBitCost t1 r (pChild p K) : ℕ) : ℝ) ≤
          ((precomputeStepRawTapBitCost t1 r (pChild p K) : ℕ) : ℝ) := by
      exact_mod_cast precomputeStepBitCost_le_precomputeStepRawTapBitCost t1 r (pChild p K)
    linarith

/-- Intrinsic bit-operation and tape-routing cost of a `QuantizedFastDFTSpec` recursion tree derived
from primitive bit-operation pricing (`addBitCost`, Schönhage–Strassen `mulBitCost`) under `[MS]` Theorem 6.3
Kronecker spreading and multitape sequential routing:
- At `.base p R`: `R * R * addBitCost p` (quadratic `Θ(R^2 p)` direct `dft1D R` evaluation at `p`-bit precision),
- At `.step p K t1 r c1 v1Of child`:
  1. `syntheticFFTStepBitCost t1 r (pChild p K)` (addition-only Radix-2 Synthetic FFT butterflies over `R_r`),
  2. `kroneckerSpreadStepBitCost t1 r (pChild p K)` (`[MS]` Theorem 6.3 Overlap-Add Kronecker spreading),
  3. `twistAndSolverStepBitCost t1 r (pChild p K)` (pre/post twists, step-rounded 3-regime bidiagonal/Nyquist solve, `nyquistAltSum`, and quantization),
  4. `routingAndStreamingStepBitCost t1 r (pChild p K)` (`2 * log₂ t₁`-pass 2D transpose, `2 * log₂ t₁`-pass odd-stride column routing, and linear-scan tape streaming),
  5. Plus `t1` recursive child transforms of cost `child.intrinsicCost`. -/
def QuantizedFastDFTSpec.intrinsicCost : QuantizedFastDFTSpec → ℝ
  | .base p R => ((R * R * addBitCost p : ℕ) : ℝ)
  | .step p K t1 r _c1 _v1Of child =>
    ((syntheticFFTStepBitCost t1 r (pChild p K) : ℕ) : ℝ) +
      ((kroneckerSpreadStepBitCost t1 r (pChild p K) : ℕ) : ℝ) +
      ((twistAndSolverStepBitCost t1 r (pChild p K) : ℕ) : ℝ) +
      ((routingAndStreamingStepBitCost t1 r (pChild p K) : ℕ) : ℝ) +
      (t1 : ℝ) * child.intrinsicCost

/-- The intrinsic bit-operation cost `spec.intrinsicCost` is non-negative for every `spec`. -/
theorem QuantizedFastDFTSpec.intrinsicCost_nonneg (spec : QuantizedFastDFTSpec) :
    0 ≤ spec.intrinsicCost := by
  induction spec with
  | base p R =>
    dsimp [QuantizedFastDFTSpec.intrinsicCost]
    positivity
  | step p K t1 r c1 v1Of child ih =>
    dsimp [QuantizedFastDFTSpec.intrinsicCost]
    positivity

/-- **Intrinsic-Cost Instrumented Quantized Signed-Kronecker `FastDFT` (`sincGaussianFastDFTQuantizedIntrinsicCost`, `[MS]` §7)**:
Executes `sincGaussianFastDFTQuantized spec x` (using sequential 2-tape input gather `routedInputGather`,
the quantized signed-Kronecker spread `kroneckerSincGaussianSpreadArray`, sequential 2-tape odd-stride
column routing `routedColumnEntry`, step-rounded solvers, sequential 2-tape output transpose `routedTranspose2D`,
and sub-step rounding at every recursive level) while accumulating the actual operand-level Kronecker
spread cost `executedKroneckerSpreadStepBitCost`, `twistAndSolverStepBitCost`,
`routingAndStreamingStepBitCost`, and `syntheticFFTStepBitCost` directly from each node's executed inputs,
dimensions, and working precision (with zero caller-supplied cost functions). -/
noncomputable def sincGaussianFastDFTQuantizedIntrinsicCost :
    QuantizedFastDFTSpec → (ℕ → ℂ) → (ℕ → ℂ) × ℝ
  | .base p R, x =>
    (fun u => complexQuantize p (dft1D R x u), ((R * R * addBitCost p : ℕ) : ℝ))
  | .step p K t1 r _c1 v1Of child, x =>
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * pChild p K
    let xRouted := routedInputGather t1 r x
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r xRouted
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    let childRes := fun v1 => sincGaussianFastDFTQuantizedIntrinsicCost child (qPost v1)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => (childRes v1).1 u2
    let childCostSum : ℝ := ∑ v1 ∈ Finset.range t1, (childRes v1).2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (routedColumnEntry t1 v1Of qHat u2 u1)
    let Z : ℕ → ℕ → ℂ := fun u2 u1_tilde =>
      let y := (u2 : ℝ) / (r : ℝ)
      let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
      let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
      let z_sub :=
        if 2 * u2 < r then
          solveBidiagonalFwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
        else if 2 * u2 = r then
          solveNyquistQuantized pSub t1 c0 (Y u2) (complexQuantize pSub (nyquistAltSum t1 r xRouted)) u1_tilde
        else
          solveBidiagonalBwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
      complexQuantize p z_sub
    let out : ℕ → ℂ := routedTranspose2D t1 r Z
    let p' := pChild p K
    let localSyn : ℝ := ((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ)
    let localSpread : ℝ := ((executedKroneckerSpreadStepBitCost α p K t1 r xRouted : ℕ) : ℝ)
    let localTwistSolve : ℝ := ((twistAndSolverStepBitCost t1 r p' : ℕ) : ℝ)
    let localRouting : ℝ := ((routingAndStreamingStepBitCost t1 r p' : ℕ) : ℝ)
    (out, localSyn + localSpread + localTwistSolve + localRouting + childCostSum)

/-- **First-Projection Equivalence (`sincGaussianFastDFTQuantizedIntrinsicCost` computes `sincGaussianFastDFTQuantized`)**:
For any `spec : QuantizedFastDFTSpec` and `x : ℕ → ℂ`,
`(sincGaussianFastDFTQuantizedIntrinsicCost spec x).1 = sincGaussianFastDFTQuantized spec x`. -/
theorem sincGaussianFastDFTQuantizedIntrinsicCost_fst_eq
    (spec : QuantizedFastDFTSpec) (x : ℕ → ℂ) :
    (sincGaussianFastDFTQuantizedIntrinsicCost spec x).1 =
      sincGaussianFastDFTQuantized spec x := by
  induction spec generalizing x with
  | base p R => rfl
  | step p K t1 r c1 v1Of child ih =>
    funext u
    dsimp only [sincGaussianFastDFTQuantizedIntrinsicCost, sincGaussianFastDFTQuantized]
    rw [routedTranspose2D_eq]
    simp only [routedInputGather_eq, routedColumnEntry_eq, ih]

/-- Non-negativity of `(sincGaussianFastDFTQuantizedIntrinsicCost spec x).2` for every `spec` and `x`. -/
theorem sincGaussianFastDFTQuantizedIntrinsicCost_snd_nonneg
    (spec : QuantizedFastDFTSpec) (x : ℕ → ℂ) :
    0 ≤ (sincGaussianFastDFTQuantizedIntrinsicCost spec x).2 := by
  induction spec generalizing x with
  | base p R =>
    dsimp [sincGaussianFastDFTQuantizedIntrinsicCost]
    positivity
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [sincGaussianFastDFTQuantizedIntrinsicCost]
    refine add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) ?_
    exact Finset.sum_nonneg fun v1 _ => ih _

/-- **Intrinsic-Cost Instrumented Quantized Integer Multiplication (`quantizedFastDFTMultiplyIntrinsicCost`, `[MS]` §7)**:
Executes the 2-call complex-packed quantized pipeline using `sincGaussianFastDFTQuantizedIntrinsicCost`
for both the forward transform `fwd` and the conjugate-inverse transform `inv`, charging
`spec.precomputeRawTapCost` for schedule-level raw-tap/coefficient/twiddle precomputation and
`rootPipelineBitCost (2 ^ K0) p0` for packing, pointwise squaring, scaling, rounding, and carry propagation,
and returning `(product, fwd.2 + inv.2 + spec.precomputeRawTapCost + rootPipelineBitCost (2 ^ K0) p0)` with zero external cost functions. -/
noncomputable def quantizedFastDFTMultiplyIntrinsicCost
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ × ℝ :=
  let x_AB := packNormalizedChunks b k1 k2 A B
  let fwd := sincGaussianFastDFTQuantizedIntrinsicCost spec x_AB
  let p0 := rootPrecision b K0
  let S_tilde : ℕ → ℂ := fun u => complexQuantize p0 ((fwd.1 u) ^ 2)
  let inv := sincGaussianFastDFTQuantizedIntrinsicCost spec (fun u => star (S_tilde u))
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j =>
      ⌊((star (inv.1 j)).im * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)) + (1 / 2 : ℝ)⌋.toNat)
  (reconstructChunks b convNat,
    fwd.2 + inv.2 + spec.precomputeRawTapCost + ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ))

/-- **First-Projection Equivalence (`quantizedFastDFTMultiplyIntrinsicCost` computes `quantizedFastDFTMultiply`)**: -/
theorem quantizedFastDFTMultiplyIntrinsicCost_fst_eq
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) :
    (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).1 =
      quantizedFastDFTMultiply spec b K0 k1 k2 A B := by
  dsimp only [quantizedFastDFTMultiplyIntrinsicCost, quantizedFastDFTMultiply, quantizedFastDFTConvApprox]
  rw [sincGaussianFastDFTQuantizedIntrinsicCost_fst_eq, sincGaussianFastDFTQuantizedIntrinsicCost_fst_eq]

/-- **Exact Product Correctness of `quantizedFastDFTMultiplyIntrinsicCost`**:
For any valid `spec : QuantizedFastDFTSpec` with `spec.size = 2 ^ K0`, `spec.p = rootPrecision b K0`,
`k1 + k2 ≤ 2 ^ K0`, `A < (2 ^ b) ^ k1`, and `B < (2 ^ b) ^ k2`,
`(quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).1 = A * B`. -/
theorem quantizedFastDFTMultiplyIntrinsicCost_fst_eq_mul
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).1 = A * B := by
  rw [quantizedFastDFTMultiplyIntrinsicCost_fst_eq]
  exact quantizedFastDFTMultiply_eq_mul spec hvalid b K0 k1 k2 hsize hp0 hk A B hA hB

/-- The intrinsic multiplication cost `(quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2`
is non-negative for every `spec`, and dominates the `spec.precomputeCost` lower bound. -/
theorem quantizedFastDFTMultiplyIntrinsicCost_snd_nonneg
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) :
    0 ≤ (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2 := by
  dsimp only [quantizedFastDFTMultiplyIntrinsicCost]
  have hpre : 0 ≤ spec.precomputeRawTapCost :=
    spec.precomputeCost_nonneg.trans spec.precomputeCost_le_precomputeRawTapCost
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (sincGaussianFastDFTQuantizedIntrinsicCost_snd_nonneg _ _)
        (sincGaussianFastDFTQuantizedIntrinsicCost_snd_nonneg _ _))
      hpre)
    (Nat.cast_nonneg _)

/-- **Anti-Witness Quadratic Lower Bound for Leaf-Only Naive DFT (`intrinsic_leaf_only_cost_quadratic`)**:
For the leaf-only specification `.base (rootPrecision b K0) (2 ^ K0)` (depth `L = 0`), the intrinsic
multiplication cost is `2 * (2 ^ K0 * 2 ^ K0 * rootPrecision b K0) + rootPipelineBitCost (2 ^ K0) (rootPrecision b K0) ≥ 12 * 4 ^ K0 > 0`,
which is strictly quadratic `Θ(4^{K_0} (b + K_0))` and can never be `0` or `O(n log n)`. -/
theorem intrinsic_leaf_only_cost_quadratic (b K0 k1 k2 A B : ℕ) :
    (quantizedFastDFTMultiplyIntrinsicCost
      (.base (rootPrecision b K0) (2 ^ K0)) b K0 k1 k2 A B).2 =
      2 * (((2 ^ K0 * 2 ^ K0 * addBitCost (rootPrecision b K0) : ℕ) : ℝ)) +
        ((rootPipelineBitCost (2 ^ K0) (rootPrecision b K0) : ℕ) : ℝ) ∧
    (12 : ℝ) * (4 : ℝ) ^ K0 ≤
      (quantizedFastDFTMultiplyIntrinsicCost
        (.base (rootPrecision b K0) (2 ^ K0)) b K0 k1 k2 A B).2 ∧
    0 < (quantizedFastDFTMultiplyIntrinsicCost
      (.base (rootPrecision b K0) (2 ^ K0)) b K0 k1 k2 A B).2 := by
  have heq :
      (quantizedFastDFTMultiplyIntrinsicCost
        (.base (rootPrecision b K0) (2 ^ K0)) b K0 k1 k2 A B).2 =
        2 * (((2 ^ K0 * 2 ^ K0 * addBitCost (rootPrecision b K0) : ℕ) : ℝ)) +
          ((rootPipelineBitCost (2 ^ K0) (rootPrecision b K0) : ℕ) : ℝ) := by
    dsimp [quantizedFastDFTMultiplyIntrinsicCost, sincGaussianFastDFTQuantizedIntrinsicCost,
      QuantizedFastDFTSpec.precomputeRawTapCost]
    ring
  have hp0 : 6 ≤ rootPrecision b K0 := by
    unfold rootPrecision
    omega
  have hpow4 : (((2 ^ K0 * 2 ^ K0 : ℕ) : ℝ)) = (4 : ℝ) ^ K0 := by
    push_cast
    rw [← mul_pow]
    norm_num
  have hge : (12 : ℝ) * (4 : ℝ) ^ K0 ≤
      2 * (((2 ^ K0 * 2 ^ K0 * addBitCost (rootPrecision b K0) : ℕ) : ℝ)) := by
    unfold addBitCost
    have hnat : 6 * (2 ^ K0 * 2 ^ K0) ≤ 2 ^ K0 * 2 ^ K0 * rootPrecision b K0 := by
      nlinarith
    have hreal : (6 : ℝ) * (((2 ^ K0 * 2 ^ K0 : ℕ) : ℝ)) ≤
        (((2 ^ K0 * 2 ^ K0 * rootPrecision b K0 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    rw [hpow4] at hreal
    linarith
  have hroot_nonneg : (0 : ℝ) ≤ ((rootPipelineBitCost (2 ^ K0) (rootPrecision b K0) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hpos : (0 : ℝ) < (12 : ℝ) * (4 : ℝ) ^ K0 := by positivity
  refine ⟨heq, ?_, ?_⟩
  · linarith
  · linarith

/-- Exact base-2 logarithm of a power of two: `Nat.log2 (2 ^ m) = m`. -/
theorem nat_log2_two_pow (m : ℕ) : Nat.log2 (2 ^ m) = m := by
  have hne : 2 ^ m ≠ 0 := by positivity
  have hle : m ≤ Nat.log2 (2 ^ m) := (Nat.le_log2 hne).mpr le_rfl
  have hlt : Nat.log2 (2 ^ m) < m + 1 :=
    (Nat.log2_lt hne).mpr (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self m))
  omega

/-- Lower bound `2 ^ (Nat.log2 n) ≤ n` for `1 ≤ n`. -/
theorem two_pow_log2_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ (Nat.log2 n) ≤ n :=
  (Nat.le_log2 (by omega)).mp le_rfl

/-- Upper bound `n < 2 ^ (Nat.log2 n + 1)` for all `n : ℕ`. -/
theorem lt_two_pow_log2_succ (n : ℕ) : n < 2 ^ (Nat.log2 n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · exact (Nat.log2_lt hn.ne').mp (Nat.lt_succ_self _)

/-- Monotonicity of `Nat.log2`: `a ≤ b → Nat.log2 a ≤ Nat.log2 b`. -/
theorem nat_log2_mono {a b : ℕ} (hab : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have hb : b ≠ 0 := by omega
    exact (Nat.le_log2 hb).mpr ((two_pow_log2_le a ha).trans hab)

/-- Real logarithm bound `(Nat.log2 n : ℝ) ≤ 2 * Real.log (n : ℝ)` for `1 ≤ n`. -/
theorem nat_log2_real_le_two_mul_log (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hpow_nat : 2 ^ (Nat.log2 n) ≤ n := two_pow_log2_le n hn
  have hpow_real : (2 : ℝ) ^ (Nat.log2 n) ≤ (n : ℝ) := by exact_mod_cast hpow_nat
  have hlog : Real.log ((2 : ℝ) ^ (Nat.log2 n)) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hpow_real
  rw [Real.log_pow] at hlog
  have hlog2 : (0.5 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hnonneg : (0 : ℝ) ≤ (Nat.log2 n : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Elementary inequality `d + 1 ≤ 2 ^ d` for all `d : ℕ`. -/
theorem add_one_le_two_pow (d : ℕ) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [pow_succ]
    omega

/-- For all `1 ≤ m`, `Nat.log2 m + 1 ≤ m`. -/
theorem log2_succ_le_self (m : ℕ) (hm : 1 ≤ m) :
    Nat.log2 m + 1 ≤ m :=
  (add_one_le_two_pow (Nat.log2 m)).trans (two_pow_log2_le m hm)

/-- For all `k : ℕ`, `Nat.log2 (k + 1) ≤ k`. -/
theorem log2_add_one_le_self (k : ℕ) : Nat.log2 (k + 1) ≤ k := by
  have h1 : k + 1 ≤ 2 ^ k := add_one_le_two_pow k
  have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hlt : Nat.log2 (k + 1) < k + 1 := (Nat.log2_lt (by omega)).mpr (h1.trans_lt h2)
  omega

/-- Elementary polynomial-vs-exponential bound `(k + 1) * (k + 1) ≤ 4 * 2 ^ k` for all `k : ℕ`. -/
theorem sq_add_one_le_four_mul_two_pow (k : ℕ) : (k + 1) * (k + 1) ≤ 4 * 2 ^ k := by
  have ha := add_one_le_two_pow (k / 2)
  have hc := add_one_le_two_pow (k - k / 2)
  have hmul : (k / 2 + 1) * (k - k / 2 + 1) ≤ 2 ^ k := by
    calc (k / 2 + 1) * (k - k / 2 + 1)
        ≤ 2 ^ (k / 2) * 2 ^ (k - k / 2) := Nat.mul_le_mul ha hc
      _ = 2 ^ (k / 2 + (k - k / 2)) := (pow_add 2 _ _).symm
      _ = 2 ^ k := by rw [Nat.add_sub_of_le (Nat.div_le_self k 2)]
  have hk1 : k + 1 ≤ 2 * (k / 2 + 1) := by omega
  have hk2 : k + 1 ≤ 2 * (k - k / 2 + 1) := by omega
  calc (k + 1) * (k + 1)
      ≤ (2 * (k / 2 + 1)) * (2 * (k - k / 2 + 1)) := Nat.mul_le_mul hk1 hk2
    _ = 4 * ((k / 2 + 1) * (k - k / 2 + 1)) := by ring
    _ ≤ 4 * 2 ^ k := Nat.mul_le_mul_left 4 hmul

/-- For all `1 ≤ m`, `(Nat.log2 m + 1) * (Nat.log2 m + 1) ≤ 4 * m`. -/
theorem log2_succ_sq_le_four_mul (m : ℕ) (hm : 1 ≤ m) :
    (Nat.log2 m + 1) * (Nat.log2 m + 1) ≤ 4 * m :=
  (sq_add_one_le_four_mul_two_pow (Nat.log2 m)).trans
    (Nat.mul_le_mul_left 4 (two_pow_log2_le m hm))

/-- Elementary cubic polynomial-vs-exponential bound `(k + 1) ^ 3 ≤ 27 * 2 ^ k` for all `k : ℕ`. -/
theorem cube_add_one_le_27_mul_two_pow (k : ℕ) :
    (k + 1) * (k + 1) * (k + 1) ≤ 27 * 2 ^ k := by
  set a := k / 3
  set b := (k - a) / 2
  set c := k - a - b
  have ha := add_one_le_two_pow a
  have hb := add_one_le_two_pow b
  have hc := add_one_le_two_pow c
  have habc : a + b + c = k := by omega
  have hmul : (a + 1) * (b + 1) * (c + 1) ≤ 2 ^ k := by
    calc (a + 1) * (b + 1) * (c + 1)
        ≤ (2 ^ a * 2 ^ b) * 2 ^ c := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
      _ = 2 ^ (a + b + c) := by rw [← pow_add, ← pow_add]
      _ = 2 ^ k := by rw [habc]
  have hk1 : k + 1 ≤ 3 * (a + 1) := by omega
  have hk2 : k + 1 ≤ 3 * (b + 1) := by omega
  have hk3 : k + 1 ≤ 3 * (c + 1) := by omega
  calc (k + 1) * (k + 1) * (k + 1)
      ≤ (3 * (a + 1)) * (3 * (b + 1)) * (3 * (c + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hk1 hk2) hk3
    _ = 27 * ((a + 1) * (b + 1) * (c + 1)) := by ring
    _ ≤ 27 * 2 ^ k := Nat.mul_le_mul_left 27 hmul

/-- For all `1 ≤ m`, `(Nat.log2 m + 1) ^ 3 ≤ 27 * m`. -/
theorem log2_succ_cube_le_27_mul (m : ℕ) (hm : 1 ≤ m) :
    (Nat.log2 m + 1) * (Nat.log2 m + 1) * (Nat.log2 m + 1) ≤ 27 * m :=
  (cube_add_one_le_27_mul_two_pow (Nat.log2 m)).trans
    (Nat.mul_le_mul_left 27 (two_pow_log2_le m hm))

/-- When `1 ≤ P` and `L ≤ Nat.log2 P`, `L * subMulRate P ≤ 27 * P * P`. -/
theorem subMulRate_mul_le_27_sq (L P : ℕ) (hP : 1 ≤ P) (hL : L ≤ Nat.log2 P) :
    L * subMulRate P ≤ 27 * P * P := by
  unfold subMulRate
  have h1 : L ≤ Nat.log2 P + 1 := by omega
  have h2 : Nat.log2 (Nat.log2 P + 1) + 1 ≤ Nat.log2 P + 1 :=
    Nat.add_le_add_right (log2_add_one_le_self (Nat.log2 P)) 1
  have hcube :
      L * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1) ≤ 27 * P := by
    calc L * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)
        ≤ (Nat.log2 P + 1) * (Nat.log2 P + 1) * (Nat.log2 P + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right (Nat.log2 P + 1) h1) h2
      _ ≤ 27 * P := log2_succ_cube_le_27_mul P hP
  calc L * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))
      = P * (L * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)) := by ring
    _ ≤ P * (27 * P) := Nat.mul_le_mul_left P hcube
    _ = 27 * P * P := by ring

/-- Root pipeline cost bound `rootPipelineBitCost R0 p0 ≤ 7 * R0 * P * P` whenever `1 ≤ p0 ≤ P`. -/
theorem rootPipelineBitCost_le_quad (R0 p0 P : ℕ) (hp0 : 1 ≤ p0) (hP : p0 ≤ P) :
    rootPipelineBitCost R0 p0 ≤ 7 * R0 * P * P := by
  unfold rootPipelineBitCost mulBitCost addBitCost
  have h1P : 1 ≤ P := hp0.trans hP
  have hlog1 : Nat.log2 p0 + 1 ≤ Nat.log2 P + 1 := Nat.add_le_add_right (nat_log2_mono hP) 1
  have hlog2 : Nat.log2 (Nat.log2 p0 + 1) + 1 ≤ Nat.log2 P + 1 :=
    (Nat.add_le_add_right (log2_add_one_le_self (Nat.log2 p0)) 1).trans hlog1
  have hsq : (Nat.log2 p0 + 1) * (Nat.log2 (Nat.log2 p0 + 1) + 1) ≤ 4 * P := by
    calc (Nat.log2 p0 + 1) * (Nat.log2 (Nat.log2 p0 + 1) + 1)
        ≤ (Nat.log2 P + 1) * (Nat.log2 P + 1) := Nat.mul_le_mul hlog1 hlog2
      _ ≤ 4 * P := log2_succ_sq_le_four_mul P h1P
  have hmul :
      p0 * (Nat.log2 p0 + 1) * (Nat.log2 (Nat.log2 p0 + 1) + 1) ≤ 4 * (P * P) := by
    calc p0 * (Nat.log2 p0 + 1) * (Nat.log2 (Nat.log2 p0 + 1) + 1)
        = p0 * ((Nat.log2 p0 + 1) * (Nat.log2 (Nat.log2 p0 + 1) + 1)) := by ring
      _ ≤ P * (4 * P) := Nat.mul_le_mul hP hsq
      _ = 4 * (P * P) := by ring
  have hadd : 3 * p0 ≤ 3 * (P * P) := by
    calc 3 * p0 = 3 * (p0 * 1) := by ring
      _ ≤ 3 * (P * P) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hP h1P)
  calc R0 * (p0 * (Nat.log2 p0 + 1) * (Nat.log2 (Nat.log2 p0 + 1) + 1) + 3 * p0)
      ≤ R0 * (4 * (P * P) + 3 * (P * P)) := Nat.mul_le_mul_left R0 (Nat.add_le_add hmul hadd)
    _ = 7 * R0 * P * P := by ring

/-- Leaf log-length `K_L` reached after `L` balanced halving steps `K ↦ K - K / 2`. -/
def leafLogLen : ℕ → ℕ → ℕ
  | 0, K => K
  | L + 1, K => leafLogLen L (K - K / 2)

/-- Sum of log-lengths `∑_{d=0}^{L-1} K_d` across `L` balanced halving steps `K ↦ K - K / 2`. -/
def sumLogLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, K => K + sumLogLen L (K - K / 2)

/-- Leaf precision `p_L` reached after `L` balanced halving steps under `p ↦ pChild p K`. -/
def leafPrecision : ℕ → ℕ → ℕ → ℕ
  | 0, p, _ => p
  | L + 1, p, K => leafPrecision L (pChild p K) (K - K / 2)

/-- Whenever `K ≤ 2 ^ (L + 1)`, `L` balanced halving steps reduce `leafLogLen L K` to at most `2`
(so the leaf base-case transform length `2 ^ (leafLogLen L K)` is at most `4`). -/
theorem leafLogLen_le_two (L K : ℕ) (hK : K ≤ 2 ^ (L + 1)) : leafLogLen L K ≤ 2 := by
  induction L generalizing K with
  | zero =>
    dsimp [leafLogLen]
    omega
  | succ L ih =>
    dsimp [leafLogLen]
    have hpow : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
    exact ih (K - K / 2) (by omega)

/-- Telescoping bound `sumLogLen L K + 2 * leafLogLen L K ≤ 2 * K + L` for all `L, K : ℕ`. -/
theorem sumLogLen_add_two_mul_leafLogLen_le (L K : ℕ) :
    sumLogLen L K + 2 * leafLogLen L K ≤ 2 * K + L := by
  induction L generalizing K with
  | zero =>
    dsimp [sumLogLen, leafLogLen]
    omega
  | succ L ih =>
    dsimp [sumLogLen, leafLogLen]
    have h := ih (K - K / 2)
    omega

/-- Geometric series bound on log-lengths: `sumLogLen L K ≤ 2 * K + L` for all `L, K : ℕ`. -/
theorem sumLogLen_le (L K : ℕ) : sumLogLen L K ≤ 2 * K + L := by
  have h := sumLogLen_add_two_mul_leafLogLen_le L K
  omega

/-- Exact closed form for `leafPrecision L p K`:
`leafPrecision L p K = p + 2 * sumLogLen L K + 12 * L`. -/
theorem leafPrecision_eq (L p K : ℕ) :
    leafPrecision L p K = p + 2 * sumLogLen L K + 12 * L := by
  induction L generalizing p K with
  | zero =>
    rfl
  | succ L ih =>
    dsimp [leafPrecision, sumLogLen]
    rw [ih (pChild p K) (K - K / 2), pChild_eq_additive]
    ring

/-- Uniform upper bound `leafPrecision L p K ≤ p + 4 * K + 14 * L`. -/
theorem leafPrecision_le (L p K : ℕ) :
    leafPrecision L p K ≤ p + 4 * K + 14 * L := by
  rw [leafPrecision_eq]
  have h := sumLogLen_le L K
  omega

/-- Monotonicity `p ≤ leafPrecision L p K`. -/
theorem le_leafPrecision (L p K : ℕ) : p ≤ leafPrecision L p K := by
  rw [leafPrecision_eq]
  omega

/-- Monotonicity of `mulBitCost`: `w1 ≤ w2 → mulBitCost w1 ≤ mulBitCost w2`. -/
theorem mulBitCost_mono {w1 w2 : ℕ} (h : w1 ≤ w2) : mulBitCost w1 ≤ mulBitCost w2 := by
  unfold mulBitCost
  have h1 : Nat.log2 w1 + 1 ≤ Nat.log2 w2 + 1 := Nat.add_le_add_right (nat_log2_mono h) 1
  have h2 : Nat.log2 (Nat.log2 w1 + 1) + 1 ≤ Nat.log2 (Nat.log2 w2 + 1) + 1 :=
    Nat.add_le_add_right (nat_log2_mono h1) 1
  exact Nat.mul_le_mul (Nat.mul_le_mul h h1) h2

/-- Monotonicity of `addBitCost`: `w1 ≤ w2 → addBitCost w1 ≤ addBitCost w2`. -/
theorem addBitCost_mono {w1 w2 : ℕ} (h : w1 ≤ w2) : addBitCost w1 ≤ addBitCost w2 := h

/-- **Executed Operand Bit-Cost of `kroneckerSincGaussianSpreadArray` is Bounded by `kroneckerSpreadStepBitCost` (`[MS]` §6.2, Theorem 6.3)**:
For `8 ≤ p`, `2 ≤ K`, `0 < r`, `p' = pChild p K`, `q = 2 * p'`, `m1 = 2 * p'`, and input `x`
bounded by `2^{p'}` on `0 .. t1 * r - 1`, summing the actual operand bit-costs over all `j1 < t1`
and `b < kroneckerSpreadNumBlocks m1 r` (using the actual polynomial lengths `.length` and dynamic
bit-strides `kroneckerBitStride` of `kroneckerSpreadRowBlockRe`, `kroneckerSpreadRowBlockIm`, and
`kroneckerSpreadFilterTapsFolded`) is bounded above by `kroneckerSpreadStepBitCost t1 r p'`. -/
theorem executed_kronecker_spread_cost_le_kroneckerSpreadStepBitCost
    (α : ℝ) (p K t1 r : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (hr : 0 < r)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K)) :
    let p' := pChild p K
    let q := 2 * p'
    let m1 := 2 * p'
    let W_eff := effectiveFilterWidth m1 r
    (∑ j1 ∈ Finset.range t1,
      ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
        (mulBitCost
            ((kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          mulBitCost
            ((kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * W_eff *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * W_eff *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)))) ≤
      kroneckerSpreadStepBitCost t1 r (pChild p K) := by
  dsimp only
  set p' := pChild p K
  set q := 2 * p'
  set m1 := 2 * p'
  set W_eff := effectiveFilterWidth m1 r
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  set slotBits := 6 * p'
  set blockBound := 2 * mulBitCost (W_eff * slotBits) + 4 * W_eff * addBitCost slotBits
  have hinner :
      ∀ j1 ∈ Finset.range t1, ∀ b ∈ Finset.range numBlocks,
        mulBitCost
            ((kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          mulBitCost
            ((kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * W_eff *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * W_eff *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) ≤
          blockBound := by
    intro j1 hj1 b hb
    have hj1_lt : j1 < t1 := Finset.mem_range.mp hj1
    have hb_lt : b < numBlocks := Finset.mem_range.mp hb
    obtain ⟨hlenRe, hlenIm, _hlenTap, hSRe, hSIm⟩ :=
      kroneckerSpreadBlock_length_and_bitStride_bounds α p K t1 r hp hK hr x hx j1 b hj1_lt hb_lt
    have hmulRe :
        mulBitCost
          ((kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length *
            kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) ≤
          mulBitCost (W_eff * slotBits) := by
      rw [hlenRe]
      exact mulBitCost_mono (Nat.mul_le_mul_left W_eff hSRe)
    have hmulIm :
        mulBitCost
          ((kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length *
            kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) ≤
          mulBitCost (W_eff * slotBits) := by
      rw [hlenIm]
      exact mulBitCost_mono (Nat.mul_le_mul_left W_eff hSIm)
    have haddRe :
        2 * W_eff *
          addBitCost
            (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) ≤
          2 * W_eff * addBitCost slotBits :=
      Nat.mul_le_mul_left (2 * W_eff) (addBitCost_mono hSRe)
    have haddIm :
        2 * W_eff *
          addBitCost
            (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) ≤
          2 * W_eff * addBitCost slotBits :=
      Nat.mul_le_mul_left (2 * W_eff) (addBitCost_mono hSIm)
    dsimp [blockBound]
    linarith
  have hsum1 :
      (∑ j1 ∈ Finset.range t1,
        ∑ b ∈ Finset.range numBlocks,
          (mulBitCost
              ((kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length *
                kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                  (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
            mulBitCost
              ((kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length *
                kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                  (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
            2 * W_eff *
              addBitCost
                (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                  (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
            2 * W_eff *
              addBitCost
                (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                  (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)))) ≤
        ∑ _j1 ∈ Finset.range t1, ∑ _b ∈ Finset.range numBlocks, blockBound :=
    Finset.sum_le_sum fun j1 hj1 => Finset.sum_le_sum fun b hb => hinner j1 hj1 b hb
  have hconst :
      (∑ _j1 ∈ Finset.range t1, ∑ _b ∈ Finset.range numBlocks, blockBound) =
        kroneckerSpreadStepBitCost t1 r p' := by
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    unfold kroneckerSpreadStepBitCost
    dsimp only
    ring
  exact hsum1.trans_eq hconst

/-- Triangle-inequality norm bound for `complexQuantize`:
`‖complexQuantize q z‖ ≤ ‖z‖ + complexQuantizeMaxErr q`. -/
theorem norm_complexQuantize_le (q : ℕ) (z : ℂ) :
    ‖complexQuantize q z‖ ≤ ‖z‖ + complexQuantizeMaxErr q := by
  have h := norm_add_le (complexQuantize q z - z) z
  rw [sub_add_cancel] at h
  have herr := norm_complexQuantize_sub_le q z
  linarith

/-- Norm bound for a quantized twist multiplication at `pSub = 2 * pChild p K`:
when `r ≤ 2 ^ K`, `1 ≤ M`, `c ≤ 1`, and `‖w‖ ≤ ((r : ℝ) + c) * M`,
`‖complexQuantize pSub (complexQuantize pSub (zetaRoot r θ) * w)‖ ≤ ((r : ℝ) + c + 0.02) * M`. -/
theorem norm_complexQuantize_zetaRoot_mul_le
    (p K r : ℕ) (hr_le : r ≤ 2 ^ K) (θ : ℝ) (w : ℂ) (c M : ℝ)
    (hc1 : c ≤ 1) (hM1 : 1 ≤ M) (hw : ‖w‖ ≤ ((r : ℝ) + c) * M) :
    let pSub := 2 * pChild p K
    ‖complexQuantize pSub (complexQuantize pSub (zetaRoot r θ) * w)‖ ≤
      ((r : ℝ) + c + (0.02 : ℝ)) * M := by
  dsimp only
  set pSub := 2 * pChild p K
  set ε := complexQuantizeMaxErr pSub
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    unfold complexQuantizeMaxErr
    positivity
  have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hε_le : ε ≤ (0.01 : ℝ) := by
    have h1 := (complexQuantizeMaxErr_two_mul_pChild_lt p K).1.le
    linarith
  have hε_r : ε * ((r : ℝ) + 1) ≤ (0.01 : ℝ) := by
    have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K r hr_le
    linarith
  have htw : ‖complexQuantize pSub (zetaRoot r θ)‖ ≤ 1 + ε := by
    have h := norm_complexQuantize_le pSub (zetaRoot r θ)
    rw [norm_zetaRoot] at h
    exact h
  have hmul : ‖complexQuantize pSub (zetaRoot r θ) * w‖ ≤ (1 + ε) * (((r : ℝ) + c) * M) := by
    rw [norm_mul]
    exact mul_le_mul htw hw (norm_nonneg _) (by linarith)
  have hquant := norm_complexQuantize_le pSub (complexQuantize pSub (zetaRoot r θ) * w)
  have hε_rc : ε * ((r : ℝ) + c) ≤ (0.01 : ℝ) := by
    calc ε * ((r : ℝ) + c)
        ≤ ε * ((r : ℝ) + 1) := mul_le_mul_of_nonneg_left (by linarith) hε_nonneg
      _ ≤ (0.01 : ℝ) := hε_r
  nlinarith

/-- **Recursive Child-Input Norm Invariant (`norm_qPost_le_two_pow_pChild`, `[MS]` §§3.2, 6.3 (Lemma 6.5))**:
At any valid internal node `.step p K t1 r c1 v1Of child` (`0 < t1`, `0 < r`, `t1 * r = 2 ^ K`),
if the parent input satisfies `∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p`, then every post-twisted
Synthetic-FFT child input `qPost v1` passed to the `t1` recursive child calls satisfies
`∀ k2 < r, ‖qPost v1 k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (pChild p K)`. -/
theorem norm_qPost_le_two_pow_pChild
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * pChild p K
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
    let P : ℕ → ℕ → ℂ := fun j1 m =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (m : ℝ)) * U j1 m)
    let Q : ℕ → ℕ → ℂ := fun v m =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
    let qPost : ℕ → ℕ → ℂ := fun v m =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(m : ℝ))) * Q v m)
    ‖qPost v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) := by
  dsimp only
  set α := alphaSchedule (pWork p K)
  set pSub := 2 * pChild p K
  set M : ℝ := (2 : ℝ) ^ p
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr_le : r ≤ 2 ^ K := by
    rw [← hsize]
    exact Nat.le_mul_of_pos_left r ht1
  let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
  let P : ℕ → ℕ → ℂ := fun j1 m =>
    complexQuantize pSub (complexQuantize pSub (zetaRoot r (m : ℝ)) * U j1 m)
  let Q : ℕ → ℕ → ℂ := fun v m =>
    complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
  have hP : ∀ j1 < t1, ∀ m < r, ‖P j1 m‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M := by
    intro j1 hj1 m hm
    have hU := norm_kroneckerSincGaussianSpreadArray_le p K t1 r ht1 hr x M hM1 hx j1 m hj1 hm
    have h := norm_complexQuantize_zetaRoot_mul_le p K r hr_le (m : ℝ) (U j1 m) (0.5 : ℝ) M
      (by norm_num) hM1 hU
    dsimp only at h
    linarith
  have hQ : ‖Q v1 k2‖ ≤ ((r : ℝ) + (0.53 : ℝ)) * M := by
    obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    set w := syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2
    have hsyn : ‖w‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M + (Nat.log2 t1 : ℝ) * complexQuantizeMaxErr pSub :=
      norm_syntheticFFTRadix2Quantized_le pSub r (Nat.log2 t1) (r / t1) hr P
        (((r : ℝ) + (0.52 : ℝ)) * M) (fun j1 hj1 m hm => hP j1 (ht1_pow ▸ hj1) m hm) v1 k2 hk2
    have hquant := norm_complexQuantize_le pSub w
    have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hlog_err : complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤ (0.01 : ℝ) := by
      have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
      nlinarith
    dsimp only [Q]
    nlinarith
  have hqPost :
      ‖complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)‖ ≤
        ((r : ℝ) + 1) * M := by
    have h := norm_complexQuantize_zetaRoot_mul_le p K r hr_le (-(k2 : ℝ)) (Q v1 k2) (0.53 : ℝ) M
      (by norm_num) hM1 hQ
    dsimp only at h
    linarith
  have hr1_nat : r + 1 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : r + 1 ≤ 2 ^ (K + 1) := by
      rw [pow_succ]
      omega
    exact h2.trans (Nat.pow_le_pow_right zero_lt_two (by omega))
  have hr1_real : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast hr1_nat
  calc ‖complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)‖
      ≤ ((r : ℝ) + 1) * M := hqPost
    _ ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right hr1_real (by positivity)
    _ = (2 : ℝ) ^ (p + 2 * K + 12) := by
        rw [← pow_add]
        congr 1
        ring
    _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]

/-- **Executed-Tree Operand Bit-Cost Bound (`sincGaussianFastDFTQuantizedIntrinsicCost_snd_le_intrinsicCost`, `[MS]` §6.2 & §7.2)**:
For any valid multi-level specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`)
and any input `x : ℕ → ℂ` with `∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p`, the total operand-level
bit-cost `(sincGaussianFastDFTQuantizedIntrinsicCost spec x).2` accumulated across the executed
recursion tree (summing `executedKroneckerSpreadStepBitCost` on the actual node inputs `x` and
`qPost v1` at every internal node) is bounded above by `spec.intrinsicCost`. -/
theorem sincGaussianFastDFTQuantizedIntrinsicCost_snd_le_intrinsicCost
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (x : ℕ → ℂ) (hx : ∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p) :
    (sincGaussianFastDFTQuantizedIntrinsicCost spec x).2 ≤ spec.intrinsicCost := by
  induction hvalid generalizing x with
  | base p R =>
    dsimp [sincGaussianFastDFTQuantizedIntrinsicCost, QuantizedFastDFTSpec.intrinsicCost]
    exact le_rfl
  | @step p K t1 r c1 v1Of child hp hK ht1 _ht1_le hr _hr_le hsize _hc1 _heven hchild_size hchild_p _hchild _hv1 _hv1_lt ih =>
    dsimp only [sincGaussianFastDFTQuantizedIntrinsicCost, QuantizedFastDFTSpec.intrinsicCost,
      QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx ⊢
    rw [routedInputGather_eq]
    set α := alphaSchedule (pWork p K)
    set pSub := 2 * pChild p K
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    have hp_le_p' : p ≤ pChild p K := (fixedPointWordBits_le_four_mul_pChild p K).1
    have hx_p' : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K) := fun k hk =>
      (hx k hk).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp_le_p')
    have hspread_nat :
        executedKroneckerSpreadStepBitCost α p K t1 r x ≤
          kroneckerSpreadStepBitCost t1 r (pChild p K) :=
      executed_kronecker_spread_cost_le_kroneckerSpreadStepBitCost α p K t1 r hp hK hr x hx_p'
    have hspread_real :
        ((executedKroneckerSpreadStepBitCost α p K t1 r x : ℕ) : ℝ) ≤
          ((kroneckerSpreadStepBitCost t1 r (pChild p K) : ℕ) : ℝ) := by
      exact_mod_cast hspread_nat
    have hchild_sum :
        (∑ v1 ∈ Finset.range t1, (sincGaussianFastDFTQuantizedIntrinsicCost child (qPost v1)).2) ≤
          (t1 : ℝ) * child.intrinsicCost := by
      calc (∑ v1 ∈ Finset.range t1, (sincGaussianFastDFTQuantizedIntrinsicCost child (qPost v1)).2)
          ≤ ∑ _v1 ∈ Finset.range t1, child.intrinsicCost := by
            refine Finset.sum_le_sum fun v1 _ => ih (qPost v1) fun k2 hk2 => ?_
            rw [hchild_size] at hk2
            rw [hchild_p]
            exact norm_qPost_le_two_pow_pChild p K t1 r ht1 hr hsize x hx v1 k2 hk2
        _ = (t1 : ℝ) * child.intrinsicCost := by
            simp [Finset.sum_const, nsmul_eq_mul]
    linarith

/-- **End-to-End Executed Multiplication Bit-Cost Bound (`quantizedFastDFTMultiplyIntrinsicCost_snd_le`, `[MS]` §7.2)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) with
`spec.size = 2 ^ K0` and `spec.p = rootPrecision b K0`, and any `k1 k2 A B : ℕ`, the total
executed operand-level bit-cost `(quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2`
(across both forward and inverse executed trees, plus `spec.precomputeRawTapCost` and
`rootPipelineBitCost (2 ^ K0) (rootPrecision b K0)`) is bounded above by
`2 * spec.intrinsicCost + spec.precomputeRawTapCost + rootPipelineBitCost (2 ^ K0) (rootPrecision b K0)`. -/
theorem quantizedFastDFTMultiplyIntrinsicCost_snd_le
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0) :
    (quantizedFastDFTMultiplyIntrinsicCost spec b K0 k1 k2 A B).2 ≤
      2 * spec.intrinsicCost + spec.precomputeRawTapCost +
        ((rootPipelineBitCost (2 ^ K0) (rootPrecision b K0) : ℕ) : ℝ) := by
  dsimp only [quantizedFastDFTMultiplyIntrinsicCost]
  set x_AB := packNormalizedChunks b k1 k2 A B
  set fwd := sincGaussianFastDFTQuantizedIntrinsicCost spec x_AB
  set p0 := rootPrecision b K0
  set S_tilde : ℕ → ℂ := fun u => complexQuantize p0 ((fwd.1 u) ^ 2)
  have hp0_ge6 : 6 ≤ p0 := by
    dsimp [p0, rootPrecision]
    omega
  have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_le2 : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hx_AB_norm : ∀ k < spec.size, ‖x_AB k‖ ≤ (2 : ℝ) ^ spec.p := by
    intro k _
    have h1 := norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ spec.p := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ spec.p := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    linarith
  have hfwd_cost : fwd.2 ≤ spec.intrinsicCost :=
    sincGaussianFastDFTQuantizedIntrinsicCost_snd_le_intrinsicCost spec hvalid x_AB hx_AB_norm
  have hS_norm : ∀ u < spec.size, ‖star (S_tilde u)‖ ≤ (2 : ℝ) ^ spec.p := by
    intro u hu
    rw [norm_star]
    have hfst : fwd.1 u = sincGaussianFastDFTQuantized spec x_AB u :=
      congrFun (sincGaussianFastDFTQuantizedIntrinsicCost_fst_eq spec x_AB) u
    have herr := sincGaussianFastDFTQuantized_error_le spec hvalid x_AB (Real.sqrt 2) hsqrt2_ge1
      (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u hu
    have hpow_neg_le1 : (2 : ℝ) ^ (-(spec.p : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have herr_le2 : ‖fwd.1 u - dft1D spec.size x_AB u‖ ≤ 2 := by
      rw [hfst]
      nlinarith
    have hR0_pos : 0 < spec.size := by
      rw [hsize]
      exact pow_pos zero_lt_two K0
    have hdft_le2 : ‖dft1D spec.size x_AB u‖ ≤ 2 :=
      (dft1D_packNormalizedChunks_norm_le_sqrt_two spec.size hR0_pos b k1 k2 A B u).trans hsqrt2_le2
    have hfwd_le4 : ‖fwd.1 u‖ ≤ 4 := by
      have htri := norm_add_le (fwd.1 u - dft1D spec.size x_AB u) (dft1D spec.size x_AB u)
      rw [sub_add_cancel] at htri
      linarith
    have hsq_le16 : ‖(fwd.1 u) ^ 2‖ ≤ 16 := by
      rw [norm_pow]
      calc ‖fwd.1 u‖ ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfwd_le4 2
        _ = 16 := by norm_num
    have hq_le1 : complexQuantizeMaxErr p0 ≤ 1 := by
      have hlt := complexQuantizeMaxErr_lt p0
      have hz : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      linarith
    have hS_le17 : ‖S_tilde u‖ ≤ 17 := by
      have hq := norm_complexQuantize_le p0 ((fwd.1 u) ^ 2)
      dsimp only [S_tilde]
      linarith
    have h64_le : (64 : ℝ) ≤ (2 : ℝ) ^ spec.p := by
      calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
        _ ≤ (2 : ℝ) ^ spec.p := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    linarith
  have hinv_cost :
      (sincGaussianFastDFTQuantizedIntrinsicCost spec (fun u => star (S_tilde u))).2 ≤
        spec.intrinsicCost :=
    sincGaussianFastDFTQuantizedIntrinsicCost_snd_le_intrinsicCost spec hvalid
      (fun u => star (S_tilde u)) hS_norm
  linarith


end IntMul
