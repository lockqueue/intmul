import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives

/-!
# Multi-Level Recursive `FastDFT`, Schedule-Driven Slot Sizing & 2-Call Pointwise-Squaring DFT Convolution (`IntMul.FastDFT`)

This module implements the data-independent schedule encoders/decoders, Stage 1–5 mathematical and
fixed-point operators, the multi-level recursive `fastDFTRecursive` and `fastDFTRecursiveSched`
operators with $K$-stage Cooley–Tukey radix-2 butterfly leaf FFTs, unconditional multi-level
accuracy closure, and 2-call complex-packed pointwise-squaring root convolution (see
Section 3.5 (`sec:prelim-dft`), Section 5 (`sec:deconv`), Section 6 (`sec:spread-and-error`),
Section 7.1 (`sec:alg-spec`), and Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`)):

1. **Data-Independent Schedule Encodings (`encodeScheduleBits`, `decodeScheduleBits`,
   `encodeFullScheduleTable`, `decodeFullScheduleTable`; schedule (34) (`eq:cert-sched`))**:
   - Linear fixed-width binary encoding `encodeScheduleBits n` (`scheduleFieldBits n = 2 * n + 8`,
     `scheduleBitsLen n = 7 * (2 * n + 8) = 14 * n + 56`) of `cSpec n` (`n`, `b`, `N`,
     `K0`, `R0`, `p0`, and `recursionDepth (rootK0 n) (rootP0 n)`) and decoder `decodeScheduleBits`
     with unconditional round-trip theorem `decodeScheduleBits_encodeScheduleBits`.
   - Full multi-level schedule table encoding `encodeFullScheduleTable n` and decoder
     `decodeFullScheduleTable n` with unconditional round-trip theorem
     `decodeFullScheduleTable_encodeFullScheduleTable`.

2. **Stage-Level Operators & Component-Level Specification Equalities**:
   - **Stage 1 (Chunk Unpacking & Complex Packing, Section 7.1 (`sec:alg-spec`) Listing 1 (`lst:multiply`))**:
     `unpackInputChunks`, `unpackInputChunks_encodeInputBits`, `packChunksFixed`, and
     `wordWidthBounds_packChunksFixed`.
   - **Stage 2 (Kronecker + Overlap-Add Spreading, Section 6.2 (`sec:kronecker`) Theorem 6.3 (`thm:spread`))**:
     `levelFilterTapFixed` and `fitsSignedWord_levelFilterTapFixed`.
   - **Stage 3 (Multi-Level Recursive `FastDFT` with $K$-Stage Radix-2 Butterfly Leaf FFT &
     Unconditional Accuracy Closure, Section 5.1 (`sec:deconv-thm`), Section 5.2 (`sec:solvers`),
     Section 6.3 (`sec:forward-error`) Lemma 6.5 (`lem:forward`), and Section 7.1 (`sec:alg-spec`))**:
     `passbandC0`, `passbandC1`, `nyquistModeSum`, `radix2FFT1DExact`, `radix2FFT1DQuant`,
     `baseRadix2FFTQuant`, `fastDFTRecursive`, `multiLevel_concreteError_le`, `root_concreteError_le`,
     `vecInfNorm_fastDFTRecursive_sub_normDFT1D_le`,
     `vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_two_zpow`,
     `root_conv_error_budget_eq_one_eighth`, and `root_conv_recovery_of_fastDFT_approx`.
   - **Stage 4 (2-Call Complex-Packed Pointwise-Squaring Convolution & Base-$2^b$ Carry-Propagation
     Reconstruction, Section 3.5 (`sec:prelim-dft`) Lemma 3.4 (`lem:two-call`), Section 7.1 (`sec:alg-spec`),
     and Section 7.2 (`sec:cost-proof`) Theorem 1 (`thm:main`) Part 1)**:
     `twoCallDFTConv`, `twoCallDFTConv_re_eq_linearConvCoeff`, `fastTwoCallDFTConv`,
     `fastTwoCallDFTConv_sub_linearConvCoeff_le`, `reconstructProductViaFastDFT`, and
     `reconstructProductViaFastDFT_eq_mul`.
   - **Stage 5 (Data-Independent Schedule-Driven Slot Sizing, Section 3.2 (`sec:prelim-model`)
     equation (5) (`eq:height-bound`) and Section 6.2 (`sec:kronecker`) equation (31) (`eq:slot-width`))**:
     `childScheduleBIn`, `levelScheduleBIn`, `scheduleSlotBits`, `fastDFTRecursiveSched`,
     `vecInfNorm_fastDFTRecursive_Q_post_le`, `fastDFTRecursiveSched_eq_fastDFTRecursive`,
     `vecInfNorm_fastDFTRecursiveSched_sub_normDFT1D_le`, `fastTwoCallDFTConvSched`,
     `reconstructProductViaScheduleFastDFT`, and `reconstructProductViaScheduleFastDFT_eq_mul`.
-/

namespace IntMul

open scoped BigOperators ComplexConjugate

/-! ## 1. Data-Independent Schedule Encodings (`encodeScheduleBits`, `decodeScheduleBits`, `encodeFullScheduleTable`, `decodeFullScheduleTable`) -/

/-- Linear bit-width `2 * n + 8` per encoded field of the data-independent schedule `cSpec n`,
chosen so every schedule parameter (`n`, `b`, `N`, `K0`, `R0`, `p0`, and
`recursionDepth (rootK0 n) (rootP0 n)`) is strictly less than `2 ^ scheduleFieldBits n`
while keeping `scheduleBitsLen n = 7 * (2 * n + 8) = 14 * n + 56 = O(n)`. -/
def scheduleFieldBits (n : ℕ) : ℕ :=
  2 * n + 8

/-- Total bit-length `7 * scheduleFieldBits n = 7 * (2 * n + 8) = 14 * n + 56` of the encoded
schedule tape `encodeScheduleBits n`. -/
def scheduleBitsLen (n : ℕ) : ℕ :=
  7 * scheduleFieldBits n

theorem scheduleBitsLen_eq (n : ℕ) : scheduleBitsLen n = 14 * n + 56 := by
  unfold scheduleBitsLen scheduleFieldBits
  ring

theorem scheduleBitsLen_pos (n : ℕ) : 0 < scheduleBitsLen n := by
  rw [scheduleBitsLen_eq]
  omega

/-- The 7 data-independent schedule fields of `cSpec n` plus `recursionDepth (rootK0 n) (rootP0 n)`. -/
def scheduleFieldVec (n : ℕ) : Fin 7 → ℕ
  | ⟨0, _⟩ => (cSpec n).n
  | ⟨1, _⟩ => (cSpec n).b
  | ⟨2, _⟩ => (cSpec n).N
  | ⟨3, _⟩ => (cSpec n).K0
  | ⟨4, _⟩ => (cSpec n).R0
  | ⟨5, _⟩ => (cSpec n).p0
  | ⟨6, _⟩ => recursionDepth (rootK0 n) (rootP0 n)

/-- Every schedule field `scheduleFieldVec n i` fits strictly in `scheduleFieldBits n = 2 * n + 8`
unsigned bits. -/
theorem scheduleFieldVec_lt_two_pow (n : ℕ) (i : Fin 7) :
    scheduleFieldVec n i < 2 ^ scheduleFieldBits n := by
  have hb := chunkBits_le_add_four n
  have hN := numChunks_le_self n
  have hK0 := rootK0_le_add_two n
  have hrec := recursionDepth_le_K0 (rootK0 n) (rootP0 n)
  have hpow_self : 2 * n + 8 < 2 ^ (2 * n + 8) := Nat.lt_two_pow_self
  fin_cases i
  · simp only [scheduleFieldVec, cSpec_n, scheduleFieldBits]
    omega
  · simp only [scheduleFieldVec, cSpec_b, scheduleFieldBits]
    omega
  · simp only [scheduleFieldVec, cSpec_N, scheduleFieldBits]
    omega
  · simp only [scheduleFieldVec, cSpec_K0, scheduleFieldBits]
    omega
  · simp only [scheduleFieldVec, cSpec_R0, scheduleFieldBits, rootR0]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · simp only [scheduleFieldVec, cSpec_p0, scheduleFieldBits, rootP0]
    have hp0 : 2 * chunkBits n + 2 * rootK0 n + 6 ≤ 4 * n + 18 := by omega
    have h1 : 2 * n + 5 < 2 ^ (2 * n + 5) := Nat.lt_two_pow_self
    have h2 : 8 * 2 ^ (2 * n + 5) = 2 ^ (2 * n + 8) := by
      have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8, ← pow_add]
      congr 1
      omega
    omega
  · simp only [scheduleFieldVec, scheduleFieldBits]
    omega

/-- Canonical binary encoding of `cSpec n` (`n`, `b`, `N`, `K0`, `R0`, `p0`, and
`recursionDepth (rootK0 n) (rootP0 n)`) as a flat `List Bool` of length `7 * scheduleFieldBits n`. -/
def encodeScheduleBits (n : ℕ) : List Bool :=
  (List.ofFn (fun i : Fin 7 =>
    encodeNatBits (scheduleFieldBits n) (scheduleFieldVec n i))).flatten

@[simp]
theorem length_encodeScheduleBits (n : ℕ) :
    (encodeScheduleBits n).length = scheduleBitsLen n := by
  unfold encodeScheduleBits scheduleBitsLen
  exact length_flatten_ofFn (scheduleFieldBits n) _
    (fun i => length_encodeNatBits (scheduleFieldBits n) (scheduleFieldVec n i))

/-- Extract the `i`-th schedule field (`i : Fin 7`) from an encoded schedule bit-list `bs`. -/
def decodeScheduleField (bs : List Bool) (i : Fin 7) : ℕ :=
  decodeNatBits ((bs.drop (i.val * (bs.length / 7))).take (bs.length / 7))

/-- Round-trip recovery of each of the 7 schedule fields from `encodeScheduleBits n`. -/
@[simp]
theorem decodeScheduleField_encodeScheduleBits (n : ℕ) (i : Fin 7) :
    decodeScheduleField (encodeScheduleBits n) i = scheduleFieldVec n i := by
  unfold decodeScheduleField
  have hlen : (encodeScheduleBits n).length / 7 = scheduleFieldBits n := by
    rw [length_encodeScheduleBits, scheduleBitsLen]
    omega
  rw [hlen]
  unfold encodeScheduleBits
  rw [drop_take_flatten_ofFn (scheduleFieldBits n)
    (fun j : Fin 7 => encodeNatBits (scheduleFieldBits n) (scheduleFieldVec n j))
    (fun j => length_encodeNatBits (scheduleFieldBits n) (scheduleFieldVec n j)) i]
  exact decodeNatBits_encodeNatBits (scheduleFieldBits n) (scheduleFieldVec n i)
    (scheduleFieldVec_lt_two_pow n i)

/-- Decode an encoded schedule bit-list `bs : List Bool` back into a `RootSpec` structure
(`n`, `b`, `N`, `K0`, `R0`, `p0`). -/
def decodeScheduleBits (bs : List Bool) : RootSpec where
  n := decodeScheduleField bs ⟨0, by decide⟩
  b := decodeScheduleField bs ⟨1, by decide⟩
  N := decodeScheduleField bs ⟨2, by decide⟩
  K0 := decodeScheduleField bs ⟨3, by decide⟩
  R0 := decodeScheduleField bs ⟨4, by decide⟩
  p0 := decodeScheduleField bs ⟨5, by decide⟩

/-- Decode the recursion depth `recursionDepth (rootK0 n) (rootP0 n)` from `encodeScheduleBits n`. -/
def decodeScheduleRecursionDepth (bs : List Bool) : ℕ :=
  decodeScheduleField bs ⟨6, by decide⟩

/-- **Schedule Encoding Round-Trip Theorem (`decodeScheduleBits_encodeScheduleBits`)**:
Decoding `encodeScheduleBits n` recovers `cSpec n` bit-exactly for every `n : ℕ`. -/
@[simp]
theorem decodeScheduleBits_encodeScheduleBits (n : ℕ) :
    decodeScheduleBits (encodeScheduleBits n) = cSpec n := by
  unfold decodeScheduleBits
  simp only [decodeScheduleField_encodeScheduleBits]
  rfl

/-- Decoding the 7th field of `encodeScheduleBits n` recovers `recursionDepth (rootK0 n) (rootP0 n)`. -/
@[simp]
theorem decodeScheduleRecursionDepth_encodeScheduleBits (n : ℕ) :
    decodeScheduleRecursionDepth (encodeScheduleBits n) =
      recursionDepth (rootK0 n) (rootP0 n) := by
  unfold decodeScheduleRecursionDepth
  simp only [decodeScheduleField_encodeScheduleBits]
  rfl

/-- Full multi-level schedule table across all recursion levels
`ell ∈ {0, ..., recursionDepth (rootK0 n) (rootP0 n)}` (schedule (34) (`eq:cert-sched`),
Section 7.1 (`sec:alg-spec`)). -/
def fullScheduleTable (n : ℕ) : List LevelScheduleEntry :=
  List.ofFn (fun i : Fin (recursionDepth (rootK0 n) (rootP0 n) + 1) =>
    buildLevelScheduleEntry n i.val)

/-- Canonical binary encoding of the full multi-level schedule table across all recursion levels
`0 ≤ ell ≤ recursionDepth (rootK0 n) (rootP0 n)`, with `11 * scheduleFieldBits n` bits per level. -/
def encodeFullScheduleTable (n : ℕ) : List Bool :=
  (List.ofFn (fun i : Fin (recursionDepth (rootK0 n) (rootP0 n) + 1) =>
    encodeLevelScheduleEntry (scheduleFieldBits n) (buildLevelScheduleEntry n i.val))).flatten

/-- Total bit-length of the encoded full multi-level schedule table `encodeFullScheduleTable n`. -/
def fullScheduleTableBitsLen (n : ℕ) : ℕ :=
  (recursionDepth (rootK0 n) (rootP0 n) + 1) * (11 * scheduleFieldBits n)

@[simp]
theorem length_encodeFullScheduleTable (n : ℕ) :
    (encodeFullScheduleTable n).length = fullScheduleTableBitsLen n := by
  unfold encodeFullScheduleTable fullScheduleTableBitsLen
  exact length_flatten_ofFn (11 * scheduleFieldBits n) _
    (fun i => length_encodeLevelScheduleEntry (scheduleFieldBits n)
      (buildLevelScheduleEntry n i.val))

/-- Decode the `i`-th per-level schedule entry (`i : Fin (recursionDepth (rootK0 n) (rootP0 n) + 1)`)
from `encodeFullScheduleTable n`. -/
def decodeFullScheduleTableEntry (n : ℕ) (bs : List Bool)
    (i : Fin (recursionDepth (rootK0 n) (rootP0 n) + 1)) : LevelScheduleEntry :=
  let entryBits := 11 * scheduleFieldBits n
  decodeLevelScheduleEntry (scheduleFieldBits n) ((bs.drop (i.val * entryBits)).take entryBits)

/-- Decode the full multi-level schedule table from its encoded bit-list `bs`. -/
def decodeFullScheduleTable (n : ℕ) (bs : List Bool) : List LevelScheduleEntry :=
  List.ofFn (fun i : Fin (recursionDepth (rootK0 n) (rootP0 n) + 1) =>
    decodeFullScheduleTableEntry n bs i)

@[simp]
theorem decodeFullScheduleTableEntry_encodeFullScheduleTable (n : ℕ)
    (i : Fin (recursionDepth (rootK0 n) (rootP0 n) + 1)) :
    decodeFullScheduleTableEntry n (encodeFullScheduleTable n) i =
      buildLevelScheduleEntry n i.val := by
  unfold decodeFullScheduleTableEntry encodeFullScheduleTable
  dsimp only
  rw [drop_take_flatten_ofFn (11 * scheduleFieldBits n)
    (fun j : Fin (recursionDepth (rootK0 n) (rootP0 n) + 1) =>
      encodeLevelScheduleEntry (scheduleFieldBits n) (buildLevelScheduleEntry n j.val))
    (fun j => length_encodeLevelScheduleEntry (scheduleFieldBits n)
      (buildLevelScheduleEntry n j.val)) i]
  have hell : i.val ≤ rootK0 n := by
    have := i.isLt
    have := recursionDepth_le_K0 (rootK0 n) (rootP0 n)
    omega
  exact decodeLevelScheduleEntry_encodeLevelScheduleEntry_build n i.val (scheduleFieldBits n)
    hell (le_refl _)

/-- **Full Multi-Level Schedule Table Round-Trip Theorem (`decodeFullScheduleTable_encodeFullScheduleTable`)**:
Decoding `encodeFullScheduleTable n` recovers `fullScheduleTable n` across all recursion levels
`0 ≤ ell ≤ recursionDepth (rootK0 n) (rootP0 n)`. -/
@[simp]
theorem decodeFullScheduleTable_encodeFullScheduleTable (n : ℕ) :
    decodeFullScheduleTable n (encodeFullScheduleTable n) = fullScheduleTable n := by
  unfold decodeFullScheduleTable fullScheduleTable
  simp [decodeFullScheduleTableEntry_encodeFullScheduleTable]

/-! ## 2. Pure Tape-Level Stage Transformations & Component-Level Specification Equalities -/

/-! ### 2.1 Stage 1: Chunk Unpacking & Normalized Complex Packing (Section 7.1 (`sec:alg-spec`), Listing 1 (`lst:multiply`)) -/

/-- Unpack an input bit-list `inBits : List Bool` of length `2 * n` into the two length-`R_0`
chunk arrays `(fun i => natChunk (chunkBits n) A i.val, fun i => natChunk (chunkBits n) B i.val)`
(Section 7.1 (`sec:alg-spec`), Listing 1 (`lst:multiply`)). -/
def unpackInputChunks (n : ℕ) (inBits : List Bool) :
    (Fin (rootR0 n) → ℕ) × (Fin (rootR0 n) → ℕ) :=
  let A := decodeNatBits (inBits.take n)
  let B := decodeNatBits (inBits.drop n)
  (fun i => natChunk (chunkBits n) A i.val,
   fun i => natChunk (chunkBits n) B i.val)

/-- **Component-Level Equality for Stage 1 Chunk Unpacking (`unpackInputChunks_encodeInputBits`,
Section 7.1 (`sec:alg-spec`))**:
For any `A, B < 2 ^ n`, `unpackInputChunks n (encodeInputBits n A B)` extracts the exact
base-$2^b$ chunk sequences `natChunk (chunkBits n) A` and `natChunk (chunkBits n) B`. -/
@[simp]
theorem unpackInputChunks_encodeInputBits (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    unpackInputChunks n (encodeInputBits n A B) =
      (fun i => natChunk (chunkBits n) A i.val,
       fun i => natChunk (chunkBits n) B i.val) := by
  unfold unpackInputChunks
  rw [take_encodeInputBits, drop_encodeInputBits,
    decodeNatBits_encodeNatBits n A hA, decodeNatBits_encodeNatBits n B hB]

/-- Pack the normalized base-$2^b$ chunk pair `(a_i, b_i)` into `FixedComplex (rootP0 n + 2)` by
multiplying each $b$-bit chunk by $2^{-b}$ at fixed-point scale $2^{p_0 + 2}$
(Section 7.1 (`sec:alg-spec`), Listing 1 (`lst:multiply`) `PackNormalizedComplex`). -/
def packChunksFixed (n : ℕ)
    (chunks : (Fin (rootR0 n) → ℕ) × (Fin (rootR0 n) → ℕ)) :
    Fin (rootR0 n) → FixedComplex (rootP0 n + 2) :=
  fun i =>
    let scale : ℤ := (2 : ℤ) ^ (rootP0 n + 2 - chunkBits n)
    ⟨((chunks.1 i % 2 ^ chunkBits n : ℕ) : ℤ) * scale,
     ((chunks.2 i % 2 ^ chunkBits n : ℕ) : ℤ) * scale⟩

/-- Internalized word-width bound for `packChunksFixed`: every packed root chunk satisfies
`WordWidthBounds (rootP0 n + 2)` unconditionally. -/
theorem wordWidthBounds_packChunksFixed (n : ℕ)
    (chunks : (Fin (rootR0 n) → ℕ) × (Fin (rootR0 n) → ℕ)) (i : Fin (rootR0 n)) :
    WordWidthBounds (rootP0 n + 2) (packChunksFixed n chunks i) := by
  have hb_le : chunkBits n ≤ rootP0 n + 2 := by
    unfold rootP0
    omega
  have hpow_eq : (2 : ℤ) ^ chunkBits n * (2 : ℤ) ^ (rootP0 n + 2 - chunkBits n) =
      (2 : ℤ) ^ (rootP0 n + 2) := by
    rw [← pow_add, Nat.add_sub_of_le hb_le]
  have hscale_pos : (0 : ℤ) < (2 : ℤ) ^ (rootP0 n + 2 - chunkBits n) := by positivity
  have h_coord : ∀ c : ℕ,
      FitsSignedWord (rootP0 n + 2)
        (((c % 2 ^ chunkBits n : ℕ) : ℤ) * (2 : ℤ) ^ (rootP0 n + 2 - chunkBits n)) := by
    intro c
    unfold FitsSignedWord
    have hlt_nat : c % 2 ^ chunkBits n < 2 ^ chunkBits n := Nat.mod_lt c (by positivity)
    have hlt_int : ((c % 2 ^ chunkBits n : ℕ) : ℤ) < (2 : ℤ) ^ chunkBits n := by
      exact_mod_cast hlt_nat
    have hnn : (0 : ℤ) ≤ ((c % 2 ^ chunkBits n : ℕ) : ℤ) * (2 : ℤ) ^ (rootP0 n + 2 - chunkBits n) :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt hscale_pos)
    rw [abs_of_nonneg hnn, ← hpow_eq]
    exact mul_lt_mul_of_pos_right hlt_int hscale_pos
  exact ⟨h_coord (chunks.1 i), h_coord (chunks.2 i)⟩

/-! ### 2.2 Stage 2: Concrete Level Filter Table & Internalized Width Bounds (Section 6.2 (`sec:kronecker`), Theorem 6.3 (`thm:spread`)) -/

/-- `alphaEll K p` is strictly positive for all `K, p : ℕ`. -/
theorem alphaEll_pos (K p : ℕ) : 0 < alphaEll K p :=
  alphaFromPWork_pos (by unfold pWorkEll; omega)

/-- `alphaEll K p` is non-negative for all `K, p : ℕ`. -/
theorem alphaEll_nonneg (K p : ℕ) : 0 ≤ alphaEll K p :=
  le_of_lt (alphaEll_pos K p)

/-- `m1Ell K p` is strictly positive for all `K, p : ℕ`. -/
theorem m1Ell_pos (K p : ℕ) : 0 < m1Ell K p := by
  unfold m1Ell m1FromPWorkPChild
  rw [Nat.ceil_pos]
  have h1 : 0 < alphaFromPWork (pWorkEll K p) := alphaEll_pos K p
  have hpChild : (0 : ℝ) < (pChildEll K p : ℝ) := by
    rw [pChildEll_eq]
    positivity
  have hlog : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt (((pChildEll K p : ℝ) * Real.log 2) / Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  positivity

/-- The pre-folded half-width `foldedHalfWidth (m1Ell K p) (rEll K)` is strictly positive
for all `K, p : ℕ`. -/
theorem foldedHalfWidth_m1Ell_pos (K p : ℕ) :
    0 < foldedHalfWidth (m1Ell K p) (rEll K) :=
  lt_min (m1Ell_pos K p) (rEll_pos K)

/-- Concrete data-independent quantized Sinc-Gaussian filter table at recursion level `(K, p)`
with **zero artificial clamping** (Section 6.1 (`sec:filter-norms`)):
`quantizeRealMantissa (qChildEll K p) (filterTap (alphaEll K p) (m1Ell K p) (t1Ell K) j1 d)`. -/
noncomputable def levelFilterTapFixed (K p : ℕ) (j1 : Fin (t1Ell K)) (d : ℤ) : ℤ :=
  quantizeRealMantissa (qChildEll K p)
    (filterTap (alphaEll K p) (m1Ell K p) (t1Ell K) j1 d)

/-- Every tap of `levelFilterTapFixed K p` satisfies `FitsSignedWord (qChildEll K p + 1)`
unconditionally because `|filterTap| ≤ 1` (`fitsSignedWord_quantizeRealMantissa_filterTap`). -/
theorem fitsSignedWord_levelFilterTapFixed (K p : ℕ) (j1 : Fin (t1Ell K)) (d : ℤ) :
    FitsSignedWord (qChildEll K p + 1) (levelFilterTapFixed K p j1 d) :=
  fitsSignedWord_quantizeRealMantissa_filterTap
    (qChildEll K p) (alphaEll K p) (alphaEll_nonneg K p) (m1Ell K p) (t1Ell K) j1 d

/-! ### 2.3 Stage 3: Multi-Level Recursive `fastDFTRecursive` with Step 1 Sinc-Gaussian Spreading, Step 2 Quantized Twist Roots, Step 3 Backward-Shift & Nyquist Deconvolution, and `freqScatter` (Section 5.1 (`sec:deconv-thm`), Section 6 (`sec:spread-and-error`), and Section 7.1 (`sec:alg-spec`)) -/

/-- Standard row-major frequency scatter $u \mapsto M(\lfloor u / r \rfloor, u \bmod r)$, inverse to
the mixed-radix frequency decomposition $u = u_2 + r u_1$ (`freqFin`; Section 3.4 (`sec:routing`),
Lemma 3.3(i) (`lem:routing`), and Section 5.2 (`sec:solvers`)). -/
def freqScatter (t1 r : ℕ) {R : ℕ} (hR : R = t1 * r) {α : Type*}
    (M : Fin t1 → Fin r → α) (u : Fin R) : α :=
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : R = 0 := by omega
      exact absurd u.isLt (by omega)
    · exact hr
  have hu1 : u.val / r < t1 := by
    rw [Nat.div_lt_iff_lt_mul hr]
    simpa [hR] using u.isLt
  have hu2 : u.val % r < r := Nat.mod_lt u.val hr
  M ⟨u.val / r, hu1⟩ ⟨u.val % r, hu2⟩

/-- Round-trip identity: `freqScatter` evaluated at `freqFin u1 u2` recovers `M u1 u2`
(Section 3.4 (`sec:routing`), Lemma 3.3(i) (`lem:routing`)). -/
@[simp]
theorem freqScatter_freqFin {t1 r : ℕ} {α : Type*}
    (M : Fin t1 → Fin r → α) (u1 : Fin t1) (u2 : Fin r) :
    freqScatter t1 r rfl M (freqFin u1 u2) = M u1 u2 := by
  have hr : 0 < r := u2.pos
  unfold freqScatter freqFin
  dsimp only
  have hdiv : (u2.val + r * u1.val) / r = u1.val := by
    rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt u2.isLt, zero_add]
  have hmod : (u2.val + r * u1.val) % r = u2.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt u2.isLt]
  congr 1 <;> exact Fin.ext (by assumption)

/-- Input integer headroom bits `levelBIn K x` for Step 1 of `fastDFTRecursive K p x`, chosen so that
every quantized sample `quantizeComplexFixed q (x j)` satisfies `WordWidthBounds (q + levelBIn K x)`
unconditionally for all `x : Fin R → ℂ`. -/
noncomputable def levelBIn (K : ℕ) {R : ℕ} (x : Fin R → ℂ) : ℕ :=
  max (K + 4) (Nat.clog 2 (Nat.ceil (vecInfNorm x)) + 1)

/-- Every quantized sample `quantizeComplexFixed q (x j)` unconditionally satisfies
`WordWidthBounds (q + levelBIn K x)`. -/
theorem wordWidthBounds_quantizeComplexFixed_levelBIn (K q : ℕ) {R : ℕ}
    (x : Fin R → ℂ) (j : Fin R) :
    WordWidthBounds (q + levelBIn K x) (quantizeComplexFixed q (x j)) := by
  let b := Nat.clog 2 (Nat.ceil (vecInfNorm x))
  have hnorm : ‖x j‖ ≤ (2 : ℝ) ^ b := by
    have h1 : ‖x j‖ ≤ vecInfNorm x := norm_le_vecInfNorm x j
    have h2 : vecInfNorm x ≤ (Nat.ceil (vecInfNorm x) : ℝ) := Nat.le_ceil (vecInfNorm x)
    have h3 : Nat.ceil (vecInfNorm x) ≤ 2 ^ b := Nat.le_pow_clog (by norm_num) _
    have h3r : (Nat.ceil (vecInfNorm x) : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast h3
    linarith
  have hw := wordWidthBounds_quantizeComplexFixed_of_norm_le (q := q) hnorm
  apply hw.mono
  unfold levelBIn
  change b + q + 1 ≤ q + max (K + 4) (b + 1)
  omega

/-- Concrete Sinc-Gaussian primary passband weight $c_0(u_2) = \hat{g}_{\alpha_\ell}(u_2 / r_\ell)$
at level $(K, p)$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`), equation (19) (`eq:c0-c1`)). -/
noncomputable def passbandC0 (K p : ℕ) (u2 : Fin (rEll K)) : ℝ :=
  gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ))

/-- Concrete Sinc-Gaussian secondary passband weight $c_1(u_2) = \hat{g}_{\alpha_\ell}(u_2 / r_\ell - 1)$
at level $(K, p)$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`), equation (19) (`eq:c0-c1`)). -/
noncomputable def passbandC1 (K p : ℕ) (u2 : Fin (rEll K)) : ℝ :=
  gHat (alphaEll K p) ((u2.val : ℝ) / (rEll K : ℝ) - 1)

/-- Unconditional passband dominant weight bound for `passbandC0` and `passbandC1`
(Theorem 5.1(1) (`thm:deconv`), equation (20) (`eq:passband`)): for all $K \in \mathbb{N}$, $p \ge 8$,
and $u_2 \in \text{Fin}(r_\ell)$, $\max(c_0(u_2), c_1(u_2)) \ge \frac{49999999}{100000000}$. -/
theorem passbandC0_passbandC1_max_ge {K p : ℕ} (hp : 8 ≤ p) (u2 : Fin (rEll K)) :
    (49999999 / 100000000 : ℝ) ≤ max (passbandC0 K p u2) (passbandC1 K p u2) :=
  gHat_passband_max_ge_level hp u2

/-- Unconditional passband non-negativity for `passbandC0` and `passbandC1` (Theorem 5.1(1) (`thm:deconv`)). -/
theorem passbandC0_passbandC1_min_nonneg (K p : ℕ) (u2 : Fin (rEll K)) :
    0 ≤ min (passbandC0 K p u2) (passbandC1 K p u2) :=
  gHat_passband_min_nonneg_level K p u2

/-- Unconditional stopband alias tail bound for `passbandC0` and `passbandC1`
(Theorem 5.1(1) (`thm:deconv`), equation (21) (`eq:stopband`)):
$1 - c_0(u_2) - c_1(u_2) < 0.15 \cdot 2^{-p_{\text{work},\ell}}$. -/
theorem passbandC0_passbandC1_stopband_lt {K p : ℕ} (hp : 8 ≤ p) (u2 : Fin (rEll K)) :
    1 - passbandC0 K p u2 - passbandC1 K p u2 <
      (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ)) :=
  gHat_stopband_alias_lt_level hp u2

/-- Unconditional exact backward-shift algebraic inversion for `passbandC0` and `passbandC1`
at any non-Nyquist column $u_2 \ne r_\ell / 2$ (Theorem 5.1(2) (`thm:deconv`)). -/
theorem passbandC0_passbandC1_prevSolve_spec {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2)
    (B : Fin (t1Ell K) → ℂ) (m : Fin (t1Ell K)) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    (passbandC0 K p u2 : ℂ) * cyclicBidiagPrevSolve (passbandC0 K p u2) (passbandC1 K p u2) B m +
      (passbandC1 K p u2 : ℂ) *
        cyclicBidiagPrevSolve (passbandC0 K p u2) (passbandC1 K p u2) B (cyclicPrev m) = B m :=
  gHat_cyclicBidiagPrevSolve_spec hK hp u2 hu2 B m

/-- Unconditional $2.36 \, t_{1,\ell}$ backward-shift deconvolution conditioning bound for
`passbandC0` and `passbandC1` at any non-Nyquist column $u_2 \ne r_\ell / 2$
(Theorem 5.1(2) (`thm:deconv`), equation (24) (`eq:B-inv-norm`)). -/
theorem passbandC0_passbandC1_prev_conditioning_le_236_t1 {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2) (B : Fin (t1Ell K) → ℂ) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    vecInfNorm (cyclicBidiagPrevSolve (passbandC0 K p u2) (passbandC1 K p u2) B) ≤
      (236 / 100 : ℝ) * (t1Ell K : ℝ) * vecInfNorm B :=
  gHat_deconvolution_prev_conditioning_le_236_t1 hK hp u2 hu2 B

/-- Unconditional quantized Step 3 backward-shift solver approximation bound at precision
`qChildEll K p` for `passbandC0` and `passbandC1` at any non-Nyquist column $u_2 \ne r_\ell / 2$
(Theorem 5.1(2) (`thm:deconv`) and Lemma 5.2 (`lem:solver-err`)). -/
theorem passbandC0_passbandC1_prevSolveQuant_sub_le {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2) (B : Fin (t1Ell K) → ℂ) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let q := qChildEll K p
    let c0 := passbandC0 K p u2
    let c1 := passbandC1 K p u2
    vecInfNorm (fun u1 =>
      cyclicBidiagPrevSolveQuant q c0 c1 B u1 - cyclicBidiagPrevSolve c0 c1 B u1) ≤
      (2 : ℝ) ^ (-(q : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1Ell K : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          (1 + vecInfNorm (cyclicBidiagPrevSolve c0 c1 B)) := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  exact vecInfNorm_cyclicBidiagPrevSolveQuant_sub_le_of_bounds
    (gHat_passband_max_ge_level hp u2)
    (max_le (gHat_le_one _ _) (gHat_le_one _ _))
    (gHat_passband_min_nonneg_level K p u2)
    (gHat_ratio_pow_t1_le_015 K p hK hp u2 hu2)
    (qChildEll_step3_precision_le_quarter K p)
    B

/-- At the Nyquist column $u_2 = r_\ell / 2$ ($K \ge 2$), the two passband weights coincide:
`passbandC1 K p u2 = passbandC0 K p u2` (Theorem 5.1(3) (`thm:deconv`)). -/
theorem passbandC1_eq_passbandC0_of_nyquist {K : ℕ} (hK : 2 ≤ K) (p : ℕ)
    (u2 : Fin (rEll K)) (hu2 : u2.val = rEll K / 2) :
    passbandC1 K p u2 = passbandC0 K p u2 := by
  unfold passbandC1 passbandC0
  have hk2 : 1 ≤ k2Ell K := by unfold k2Ell; omega
  have hdvd : 2 ∣ rEll K := by
    unfold rEll
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : k2Ell K ≠ 0) with ⟨m, hm⟩
    rw [hm, pow_succ']
    exact dvd_mul_right 2 (2 ^ m)
  have hmul : 2 * u2.val = rEll K := by
    rw [hu2, Nat.mul_div_cancel' hdvd]
  have hmulR : 2 * (u2.val : ℝ) = (rEll K : ℝ) := by exact_mod_cast hmul
  have hr_ne : (rEll K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (rEll_pos K))
  rw [gHat_symm_one]
  congr 1
  field_simp [hr_ne]
  linarith

/-- Unconditional $2.36 \, t_{1,\ell}$ Nyquist column conditioning bound for `passbandC0` at
$u_2 = r_\ell / 2$ (Theorem 5.1(3) (`thm:deconv`)). -/
theorem passbandC0_nyquist_conditioning_le_236_t1 {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val = rEll K / 2)
    (B : Fin (t1Ell K) → ℂ) (altTrue : ℂ) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    vecInfNorm (nyquistColumnSolve (passbandC0 K p u2) B altTrue) ≤
      (236 / 100 : ℝ) * (t1Ell K : ℝ) * vecInfNorm B + ‖altTrue‖ / (t1Ell K : ℝ) := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  have hmax := passbandC0_passbandC1_max_ge hp u2
  rw [passbandC1_eq_passbandC0_of_nyquist hK p u2 hu2, max_self] at hmax
  exact nyquist_conditioning_le_236_t1_of_bounds hmax B altTrue

/-- Exact Nyquist mode alternating sum at $u_2 = r_\ell / 2$ (Theorem 5.1(3) (`thm:deconv`),
equation (25) (`eq:nyquist-id`)):
$$\frac{i}{r_\ell} \sum_{j_2 = 0}^{r_\ell - 1} (-1)^{j_2} x(t_{1,\ell}/2 + t_{1,\ell} j_2).$$ -/
noncomputable def nyquistModeSum (K : ℕ) (x : Fin (2 ^ K) → ℂ) : ℂ :=
  (Complex.I / (rEll K : ℂ)) *
    ∑ j2 : Fin (rEll K),
      ((-1 : ℂ) ^ j2.val) *
        x ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩

/-- Idempotence of `quantizeReal`: quantizing an already $q$-bit quantized real number is the identity. -/
theorem quantizeReal_idem (q : ℕ) (x : ℝ) :
    quantizeReal q (quantizeReal q x) = quantizeReal q x := by
  unfold quantizeReal quantizeRealMantissa
  set m : ℤ := ⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋
  have hmul : (m : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q = (m : ℝ) := by
    rw [mul_assoc, mul_comm ((2 : ℝ) ^ (-(q : ℤ))), two_pow_mul_two_zpow_neg, mul_one]
  rw [hmul]
  have hfl : ⌊(m : ℝ) + (1 / 2 : ℝ)⌋ = m :=
    floor_add_half_eq_of_abs_sub_lt_half (M := m) (by simp)
  rw [hfl]

/-- Idempotence of `quantizeComplex`: quantizing an already $q$-bit quantized complex number is the identity. -/
@[simp]
theorem quantizeComplex_idem (q : ℕ) (z : ℂ) :
    quantizeComplex q (quantizeComplex q z) = quantizeComplex q z := by
  apply Complex.ext
  · simp [quantizeReal_idem]
  · simp [quantizeReal_idem]

/-- Half-period root identity $e^{2\pi i (1/2)} = e^{\pi i} = -1$. -/
theorem expTwoPiI_half : expTwoPiI (1 / 2 : ℝ) = -1 := by
  have h1 : expTwoPiI (1 / 2 : ℝ) = zetaPow 1 1 := by
    unfold expTwoPiI zetaPow
    congr 1
    push_cast
    ring
  rw [h1]
  exact zetaPow_self zero_lt_one

/-- Half-period sign flip $e^{2\pi i (\theta + 1/2)} = -e^{2\pi i \theta}$. -/
theorem expTwoPiI_add_half (θ : ℝ) : expTwoPiI (θ + (1 / 2 : ℝ)) = -expTwoPiI θ := by
  rw [expTwoPiI_add, expTwoPiI_half, mul_neg_one]

/-- Exact $m$-stage Cooley–Tukey radix-2 decimation-in-time butterfly 1D FFT (`BaseRadix2FFT` in
Listing 1 (`lst:multiply`), Section 7.1 (`sec:alg-spec`) and Lemma 6.5(2) (`lem:forward`)). -/
noncomputable def radix2FFT1DExact :
    (m : ℕ) → (Fin (2 ^ m) → ℂ) → (Fin (2 ^ m) → ℂ)
  | 0, x => x
  | m + 1, x =>
    let E := radix2FFT1DExact m (fun j => x (evenSubIndex m j))
    let O := radix2FFT1DExact m (fun j => x (oddSubIndex m j))
    fun u =>
      let v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
      let w : ℂ := expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ))
      if u.val < 2 ^ m then
        (E v + w * O v) / 2
      else
        (E v - w * O v) / 2

/-- **Exactness of the $m$-Stage Cooley–Tukey Radix-2 Butterfly 1D FFT (`radix2FFT1DExact_eq_normDFT1D`,
Section 6.3 (`sec:forward-error`) and Section 7.1 (`sec:alg-spec`))**:
For every $m \in \mathbb{N}$ and input vector $x : \text{Fin}(2^m) \to \mathbb{C}$, the $m$-stage
Cooley–Tukey radix-2 butterfly recursion `radix2FFT1DExact m x` computes `normDFT1D x` identically. -/
theorem radix2FFT1DExact_eq_normDFT1D (m : ℕ) :
    ∀ (x : Fin (2 ^ m) → ℂ) (u : Fin (2 ^ m)),
      radix2FFT1DExact m x u = normDFT1D x u := by
  induction m with
  | zero =>
    intro x u
    have hu : u = 0 := Fin.ext (by omega)
    subst hu
    change x 0 = (((1 : ℕ) : ℝ)⁻¹ : ℂ) *
      ∑ j : Fin 1, x j * expTwoPiI (((j.val * 0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))
    rw [Fin.sum_univ_one]
    simp [expTwoPiI_zero]
  | succ m ih =>
    intro x u
    unfold radix2FFT1DExact
    dsimp only
    set v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
    set w : ℂ := expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ))
    rw [ih (fun j => x (evenSubIndex m j)) v, ih (fun j => x (oddSubIndex m j)) v]
    unfold normDFT1D
    rw [sum_fin_pow_succ_even_odd m]
    have h2m_ne : ((2 ^ m : ℕ) : ℝ) ≠ 0 := by positivity
    have h2m1_eq : ((2 ^ (m + 1) : ℕ) : ℝ) = 2 * ((2 ^ m : ℕ) : ℝ) := by
      rw [Nat.pow_succ']
      push_cast
      ring
    have h_inv : (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ : ℂ) = (((2 ^ m : ℕ) : ℝ)⁻¹ : ℂ) / 2 := by
      rw [h2m1_eq]
      push_cast
      ring
    split_ifs with hu
    · have hu_val : u.val = v.val := (Nat.mod_eq_of_lt hu).symm
      have heven : ∀ j : Fin (2 ^ m),
          x (evenSubIndex m j) *
              expTwoPiI ((((evenSubIndex m j).val * u.val : ℕ) : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)) =
            x (evenSubIndex m j) *
              expTwoPiI (((j.val * v.val : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by
        intro j
        congr 2
        rw [hu_val, h2m1_eq]
        simp only [evenSubIndex]
        push_cast
        field_simp [h2m_ne]
      have hodd : ∀ j : Fin (2 ^ m),
          x (oddSubIndex m j) *
              expTwoPiI ((((oddSubIndex m j).val * u.val : ℕ) : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)) =
            w * (x (oddSubIndex m j) *
              expTwoPiI (((j.val * v.val : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ))) := by
        intro j
        have harg : (((oddSubIndex m j).val * u.val : ℕ) : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) =
            (v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) +
              ((j.val * v.val : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
          rw [hu_val, h2m1_eq]
          simp only [oddSubIndex]
          push_cast
          field_simp [h2m_ne]
          ring
        rw [harg, expTwoPiI_add]
        dsimp [w]
        ring
      simp_rw [heven, hodd, ← Finset.mul_sum, h_inv]
      ring
    · have hu_ge : 2 ^ m ≤ u.val := le_of_not_gt hu
      have hu_lt : u.val < 2 * 2 ^ m := by
        have h1 : u.val < 2 ^ (m + 1) := u.isLt
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
        omega
      have hu_val : u.val = v.val + 2 ^ m := by
        have hmod : u.val % (2 ^ m) = u.val - 2 ^ m := by
          rw [Nat.mod_eq_sub_mod hu_ge, Nat.mod_eq_of_lt (by omega)]
        change u.val = u.val % (2 ^ m) + 2 ^ m
        omega
      have heven : ∀ j : Fin (2 ^ m),
          x (evenSubIndex m j) *
              expTwoPiI ((((evenSubIndex m j).val * u.val : ℕ) : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)) =
            x (evenSubIndex m j) *
              expTwoPiI (((j.val * v.val : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by
        intro j
        congr 1
        have harg : (((evenSubIndex m j).val * u.val : ℕ) : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) =
            ((j.val * v.val : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ) + ((j.val : ℤ) : ℝ) := by
          rw [hu_val, h2m1_eq]
          simp only [evenSubIndex]
          push_cast
          field_simp [h2m_ne]
        rw [harg, expTwoPiI_add_int]
      have hodd : ∀ j : Fin (2 ^ m),
          x (oddSubIndex m j) *
              expTwoPiI ((((oddSubIndex m j).val * u.val : ℕ) : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)) =
            -(w * (x (oddSubIndex m j) *
              expTwoPiI (((j.val * v.val : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ)))) := by
        intro j
        have harg : (((oddSubIndex m j).val * u.val : ℕ) : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) =
            (((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) +
              ((j.val * v.val : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ)) + (1 / 2 : ℝ)) +
              ((j.val : ℤ) : ℝ) := by
          rw [hu_val, h2m1_eq]
          simp only [oddSubIndex]
          push_cast
          field_simp [h2m_ne]
          ring
        rw [harg, expTwoPiI_add_int, expTwoPiI_add_half, expTwoPiI_add]
        dsimp [w]
        ring
      simp_rw [heven, hodd, Finset.sum_neg_distrib, ← Finset.mul_sum, h_inv]
      ring

/-- Quantized $m$-stage Cooley–Tukey radix-2 decimation-in-time butterfly 1D FFT at precision $q$
(`BaseRadix2FFT` in Listing 1 (`lst:multiply`), Section 7.1 (`sec:alg-spec`), and Lemma 6.5(2) (`lem:forward`)). -/
noncomputable def radix2FFT1DQuant (q : ℕ) :
    (m : ℕ) → (Fin (2 ^ m) → ℂ) → (Fin (2 ^ m) → ℂ)
  | 0, x => fun u => quantizeComplex q (x u)
  | m + 1, x =>
    let E := radix2FFT1DQuant q m (fun j => x (evenSubIndex m j))
    let O := radix2FFT1DQuant q m (fun j => x (oddSubIndex m j))
    fun u =>
      let v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
      let w : ℂ := quantizeComplex q (expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)))
      let t : ℂ := quantizeComplex q (w * O v)
      if u.val < 2 ^ m then
        quantizeComplex q ((E v + t) / 2)
      else
        quantizeComplex q ((E v - t) / 2)

/-- Inductive $\ell_\infty$ rounding error bound for the $m$-stage quantized radix-2 butterfly FFT
`radix2FFT1DQuant q m x` against `normDFT1D x` (Lemma 6.5(2) (`lem:forward`)):
$$\|\text{radix2FFT1DQuant } q \, m \, x - F_{2^m} x\|_\infty \le (4 \cdot 2^m - 3) \frac{\sqrt{2}}{2} 2^{-q} \max(1, \|x\|_\infty).$$ -/
theorem vecInfNorm_radix2FFT1DQuant_sub_normDFT1D_le (q m : ℕ) :
    ∀ (x : Fin (2 ^ m) → ℂ),
      vecInfNorm (fun u => radix2FFT1DQuant q m x u - normDFT1D x u) ≤
        (4 * ((2 ^ m : ℕ) : ℝ) - 3) *
          ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))) * max 1 (vecInfNorm x) := by
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have h2q_le_one : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 := by
    rw [← zpow_zero (2 : ℝ)]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_le : Real.sqrt 2 ≤ (72 / 50 : ℝ) := sqrt_two_le
  set ε : ℝ := (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ))
  have hε_pos : 0 < ε := by positivity
  have hε_le_one : ε ≤ 1 := by
    change (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 1
    nlinarith
  induction m with
  | zero =>
    intro x
    have hM_ge_one : 1 ≤ max 1 (vecInfNorm x) := le_max_left 1 (vecInfNorm x)
    apply vecInfNorm_le _ (by positivity)
    intro u
    rw [← radix2FFT1DExact_eq_normDFT1D 0 x u]
    unfold radix2FFT1DQuant radix2FFT1DExact
    have hq := norm_quantizeComplex_sub_self_le q (x u)
    calc
      ‖quantizeComplex q (x u) - x u‖ ≤ ε := hq
      _ = (4 * ((2 ^ 0 : ℕ) : ℝ) - 3) * ε * 1 := by norm_num
      _ ≤ (4 * ((2 ^ 0 : ℕ) : ℝ) - 3) * ε * max 1 (vecInfNorm x) := by gcongr
  | succ m ih =>
    intro x
    set M : ℝ := max 1 (vecInfNorm x)
    have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
    have hM_ge_norm : vecInfNorm x ≤ M := le_max_right 1 (vecInfNorm x)
    have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
    let xE : Fin (2 ^ m) → ℂ := fun j => x (evenSubIndex m j)
    let xO : Fin (2 ^ m) → ℂ := fun j => x (oddSubIndex m j)
    have hxE_norm : vecInfNorm xE ≤ M := by
      apply vecInfNorm_le xE (le_of_lt hM_pos)
      intro j
      exact (norm_le_vecInfNorm x (evenSubIndex m j)).trans hM_ge_norm
    have hxO_norm : vecInfNorm xO ≤ M := by
      apply vecInfNorm_le xO (le_of_lt hM_pos)
      intro j
      exact (norm_le_vecInfNorm x (oddSubIndex m j)).trans hM_ge_norm
    have hxE_max : max 1 (vecInfNorm xE) ≤ M := max_le hM_ge_one hxE_norm
    have hxO_max : max 1 (vecInfNorm xO) ≤ M := max_le hM_ge_one hxO_norm
    set Cm : ℝ := 4 * ((2 ^ m : ℕ) : ℝ) - 3
    have h2m_ge_one : (1 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    have hCm_pos : 0 < Cm := by
      change 0 < 4 * ((2 ^ m : ℕ) : ℝ) - 3
      linarith
    have h2m1_pos : 0 < 4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3 := by
      have h2m1_ge : (1 : ℝ) ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_two_pow
      linarith
    apply vecInfNorm_le _ (by positivity)
    intro u
    rw [← radix2FFT1DExact_eq_normDFT1D (m + 1) x u]
    unfold radix2FFT1DQuant radix2FFT1DExact
    dsimp only
    set v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
    set w_true : ℂ := expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ))
    set w : ℂ := quantizeComplex q w_true
    set Ev : ℂ := radix2FFT1DQuant q m xE v
    set Ov : ℂ := radix2FFT1DQuant q m xO v
    set Ev_true : ℂ := radix2FFT1DExact m xE v
    set Ov_true : ℂ := radix2FFT1DExact m xO v
    set t : ℂ := quantizeComplex q (w * Ov)
    have hEv_eq : Ev_true = normDFT1D xE v := radix2FFT1DExact_eq_normDFT1D m xE v
    have hOv_eq : Ov_true = normDFT1D xO v := radix2FFT1DExact_eq_normDFT1D m xO v
    have hEv_err : ‖Ev - Ev_true‖ ≤ Cm * ε * M := by
      rw [hEv_eq]
      calc
        ‖Ev - normDFT1D xE v‖
          ≤ vecInfNorm (fun k => radix2FFT1DQuant q m xE k - normDFT1D xE k) :=
            norm_le_vecInfNorm (fun k => radix2FFT1DQuant q m xE k - normDFT1D xE k) v
        _ ≤ Cm * ε * max 1 (vecInfNorm xE) := ih xE
        _ ≤ Cm * ε * M := mul_le_mul_of_nonneg_left hxE_max (by positivity)
    have hOv_err : ‖Ov - Ov_true‖ ≤ Cm * ε * M := by
      rw [hOv_eq]
      calc
        ‖Ov - normDFT1D xO v‖
          ≤ vecInfNorm (fun k => radix2FFT1DQuant q m xO k - normDFT1D xO k) :=
            norm_le_vecInfNorm (fun k => radix2FFT1DQuant q m xO k - normDFT1D xO k) v
        _ ≤ Cm * ε * max 1 (vecInfNorm xO) := ih xO
        _ ≤ Cm * ε * M := mul_le_mul_of_nonneg_left hxO_max (by positivity)
    have hOv_true_norm : ‖Ov_true‖ ≤ M := by
      rw [hOv_eq]
      exact (norm_normDFT1D_le xO v).trans hxO_norm
    have hw_sub : ‖w - w_true‖ ≤ ε := norm_quantizeComplex_sub_self_le q w_true
    have hw_norm : ‖w‖ ≤ 2 := by
      have htri : ‖w‖ ≤ ‖w - w_true‖ + ‖w_true‖ := by
        simpa using norm_add_le (w - w_true) w_true
      have hw1 : ‖w_true‖ = 1 := norm_expTwoPiI _
      linarith
    have ht_err : ‖t - w_true * Ov_true‖ ≤ (2 * Cm + 2) * ε * M := by
      have hdecomp : t - w_true * Ov_true =
          (t - w * Ov) + (w * (Ov - Ov_true) + (w - w_true) * Ov_true) := by ring
      rw [hdecomp]
      have h0 : ‖t - w * Ov‖ ≤ ε * M := by
        have hq : ‖t - w * Ov‖ ≤ ε := norm_quantizeComplex_sub_self_le q (w * Ov)
        calc
          ‖t - w * Ov‖ ≤ ε * 1 := by linarith
          _ ≤ ε * M := by gcongr
      have h1 : ‖w * (Ov - Ov_true)‖ ≤ 2 * Cm * ε * M := by
        rw [norm_mul]
        calc
          ‖w‖ * ‖Ov - Ov_true‖ ≤ 2 * (Cm * ε * M) :=
            mul_le_mul hw_norm hOv_err (norm_nonneg _) (by positivity)
          _ = 2 * Cm * ε * M := by ring
      have h2 : ‖(w - w_true) * Ov_true‖ ≤ ε * M := by
        rw [norm_mul]
        exact mul_le_mul hw_sub hOv_true_norm (norm_nonneg _) (le_of_lt hε_pos)
      have htri1 := norm_add_le (t - w * Ov) (w * (Ov - Ov_true) + (w - w_true) * Ov_true)
      have htri2 := norm_add_le (w * (Ov - Ov_true)) ((w - w_true) * Ov_true)
      linarith
    have hcoeff_step : ((3 / 2 : ℝ) * Cm + 2) * ε * M ≤
        (4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3) * ε * M := by
      have hlin : (3 / 2 : ℝ) * Cm + 2 ≤ 4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3 := by
        change (3 / 2 : ℝ) * (4 * ((2 ^ m : ℕ) : ℝ) - 3) + 2 ≤
          4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3
        have hpow : ((2 ^ (m + 1) : ℕ) : ℝ) = 2 * ((2 ^ m : ℕ) : ℝ) := by
          rw [Nat.pow_succ', Nat.cast_mul, Nat.cast_ofNat]
        rw [hpow]
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlin (le_of_lt hε_pos))
        (le_of_lt hM_pos)
    split_ifs with hu
    · have hhalf : ‖(Ev + t) / 2 - (Ev_true + w_true * Ov_true) / 2‖ ≤
          ((3 / 2 : ℝ) * Cm + 1) * ε * M := by
        have hsub : (Ev + t) / 2 - (Ev_true + w_true * Ov_true) / 2 =
            ((Ev - Ev_true) + (t - w_true * Ov_true)) / 2 := by ring
        rw [hsub, norm_div, Complex.norm_ofNat]
        have htri := norm_add_le (Ev - Ev_true) (t - w_true * Ov_true)
        linarith
      have hq_out : ‖quantizeComplex q ((Ev + t) / 2) - (Ev + t) / 2‖ ≤ ε * M := by
        have hq : ‖quantizeComplex q ((Ev + t) / 2) - (Ev + t) / 2‖ ≤ ε :=
          norm_quantizeComplex_sub_self_le q ((Ev + t) / 2)
        calc
          ‖quantizeComplex q ((Ev + t) / 2) - (Ev + t) / 2‖ ≤ ε * 1 := by linarith
          _ ≤ ε * M := by gcongr
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (quantizeComplex q ((Ev + t) / 2)) ((Ev + t) / 2) ((Ev_true + w_true * Ov_true) / 2)
      linarith
    · have hhalf : ‖(Ev - t) / 2 - (Ev_true - w_true * Ov_true) / 2‖ ≤
          ((3 / 2 : ℝ) * Cm + 1) * ε * M := by
        have hsub : (Ev - t) / 2 - (Ev_true - w_true * Ov_true) / 2 =
            ((Ev - Ev_true) - (t - w_true * Ov_true)) / 2 := by ring
        rw [hsub, norm_div, Complex.norm_ofNat]
        have htri := norm_sub_le (Ev - Ev_true) (t - w_true * Ov_true)
        linarith
      have hq_out : ‖quantizeComplex q ((Ev - t) / 2) - (Ev - t) / 2‖ ≤ ε * M := by
        have hq : ‖quantizeComplex q ((Ev - t) / 2) - (Ev - t) / 2‖ ≤ ε :=
          norm_quantizeComplex_sub_self_le q ((Ev - t) / 2)
        calc
          ‖quantizeComplex q ((Ev - t) / 2) - (Ev - t) / 2‖ ≤ ε * 1 := by linarith
          _ ≤ ε * M := by gcongr
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (quantizeComplex q ((Ev - t) / 2)) ((Ev - t) / 2) ((Ev_true - w_true * Ov_true) / 2)
      linarith

/-- Quantized $K$-stage Cooley–Tukey radix-2 butterfly base-case FFT at leaf levels
$R_\ell = 2^{K_\ell} \le 4 p_\ell^2$ (`BaseRadix2FFT` in Listing 1 (`lst:multiply`), Section 7.1 (`sec:alg-spec`),
and Lemma 6.5(2) (`lem:forward`)), executing `radix2FFT1DQuant` across $K$ butterfly stages at
precision $q_{\text{base}} = p_\ell + K_\ell + 4$ and quantizing the output to $p_\ell + 2$
fractional bits. -/
noncomputable def baseRadix2FFTQuant (K p : ℕ) (x : Fin (2 ^ K) → ℂ) (u : Fin (2 ^ K)) : ℂ :=
  quantizeComplex (p + 2) (radix2FFT1DQuant (qBaseEll K p) K x u)

@[simp]
theorem toComplex_quantizeComplexFixed_baseRadix2FFTQuant (K p : ℕ)
    (x : Fin (2 ^ K) → ℂ) (u : Fin (2 ^ K)) :
    (quantizeComplexFixed (p + 2) (baseRadix2FFTQuant K p x u)).toComplex =
      baseRadix2FFTQuant K p x u := by
  change quantizeComplex (p + 2) (baseRadix2FFTQuant K p x u) = baseRadix2FFTQuant K p x u
  unfold baseRadix2FFTQuant
  exact quantizeComplex_idem (p + 2) _

/-- **Unconditional $K$-Stage Radix-2 Butterfly Base-Leaf FFT Error Bound
(`vecInfNorm_baseRadix2FFTQuant_sub_normDFT1D_le`, Lemma 6.5(2) (`lem:forward`),
Section 6.3 (`sec:forward-error`) and Section 7.1 (`sec:alg-spec`))**:
For all $K, p \in \mathbb{N}$ and any input vector $x : \text{Fin } (2^K) \to \mathbb{C}$, the
quantized $K$-stage Cooley–Tukey radix-2 butterfly leaf FFT `baseRadix2FFTQuant K p x` at precision
$q_{\text{base}} = p + K + 4$ satisfies:
$$\|\text{baseRadix2FFTQuant } K \, p \, x - F_{2^K} x\|_\infty \le \frac{\sqrt{2}}{4} 2^{-p} \max(1, \|x\|_\infty).$$ -/
theorem vecInfNorm_baseRadix2FFTQuant_sub_normDFT1D_le (K p : ℕ) (x : Fin (2 ^ K) → ℂ) :
    vecInfNorm (fun u => baseRadix2FFTQuant K p x u - normDFT1D x u) ≤
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) * max 1 (vecInfNorm x) := by
  let qBase : ℕ := qBaseEll K p
  let M : ℝ := max 1 (vecInfNorm x)
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hloop := vecInfNorm_radix2FFT1DQuant_sub_normDFT1D_le qBase K x
  have hpow_qBase :
      ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(qBase : ℤ)) =
        (1 / 16 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    have hexp : -(qBase : ℤ) = -(K : ℤ) + (-(p : ℤ) + (-4 : ℤ)) := by
      change -((p + K + 4 : ℕ) : ℤ) = -(K : ℤ) + (-(p : ℤ) + (-4 : ℤ))
      omega
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    have hcancel : ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(K : ℤ)) = 1 := by
      push_cast
      exact two_pow_mul_two_zpow_neg K
    calc
      ((2 ^ K : ℕ) : ℝ) * ((2 : ℝ) ^ (-(K : ℤ)) * ((2 : ℝ) ^ (-(p : ℤ)) * (2 : ℝ) ^ (-4 : ℤ)))
        = (((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(K : ℤ))) *
            ((2 : ℝ) ^ (-4 : ℤ) * (2 : ℝ) ^ (-(p : ℤ))) := by ring
      _ = (1 / 16 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
        rw [hcancel, one_mul]
        norm_num
  have hloop_bound :
      (4 * ((2 ^ K : ℕ) : ℝ) - 3) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qBase : ℤ))) * M ≤
        (Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hle1 : 4 * ((2 ^ K : ℕ) : ℝ) - 3 ≤ 4 * ((2 ^ K : ℕ) : ℝ) := by linarith
    have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(qBase : ℤ)) := zpow_pos (by norm_num) _
    calc
      (4 * ((2 ^ K : ℕ) : ℝ) - 3) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qBase : ℤ))) * M
        ≤ (4 * ((2 ^ K : ℕ) : ℝ)) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qBase : ℤ))) * M :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hle1 (by positivity))
            (le_of_lt hM_pos)
      _ = 2 * Real.sqrt 2 * (((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(qBase : ℤ))) * M := by ring
      _ = (Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
          rw [hpow_qBase]
          ring
  apply vecInfNorm_le _ (by positivity)
  intro u
  unfold baseRadix2FFTQuant
  set y : ℂ := radix2FFT1DQuant qBase K x u
  have hy_err : ‖y - normDFT1D x u‖ ≤ (Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    (norm_le_vecInfNorm (fun v => radix2FFT1DQuant qBase K x v - normDFT1D x v) u).trans
      (hloop.trans hloop_bound)
  have hout_sub : ‖quantizeComplex (p + 2) y - y‖ ≤
      (Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have h := norm_quantizeComplex_sub_self_le (p + 2) y
    have hexp : -((p + 2 : ℕ) : ℤ) = -(p : ℤ) + (-2 : ℤ) := by push_cast; ring
    have hpow : (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
      rw [hexp, zpow_add₀ (by norm_num)]
      norm_num
      ring
    rw [hpow] at h
    calc
      ‖quantizeComplex (p + 2) y - y‖
        ≤ (Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)) * 1 := by linarith
      _ ≤ (Real.sqrt 2 / 8) * (2 : ℝ) ^ (-(p : ℤ)) * M := by gcongr
  have htri := norm_sub_le_norm_sub_add_norm_sub (quantizeComplex (p + 2) y) y (normDFT1D x u)
  linarith

/-- Unconditional Step 1 Kronecker spreading identity at any level `(K, p)`
(Theorem 6.3 (`thm:spread`), Section 6.2 (`sec:kronecker`)): with
`B_slot = kroneckerSlotBitsRaw (qChildEll K p) (levelBIn K x) (m1Ell K p) (foldedHalfWidth (m1Ell K p) (rEll K))`,
the 2-product Kronecker spreading `kroneckerMatrixSpreadFixed` on the gathered input matrix
equals `refMatrixSpreadFixed` unconditionally for all `x : Fin (2 ^ K) → ℂ` with zero clamping. -/
theorem fastDFTRecursive_step1_eq_refMatrixSpreadFixed (K p : ℕ) (x : Fin (2 ^ K) → ℂ) :
    let t1 := t1Ell K
    let r := rEll K
    let qChild := qChildEll K p
    let m1 := m1Ell K p
    let B_in := levelBIn K x
    let B_slot := kroneckerSlotBitsRaw qChild B_in m1 (foldedHalfWidth m1 r)
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r (Nat.two_pow_pos K) (fun j => quantizeComplexFixed qChild (x j))
    kroneckerMatrixSpreadFixed t1 r m1 B_slot qChild qChild (rEll_pos K)
      U_gathered (levelFilterTapFixed K p) =
    refMatrixSpreadFixed t1 r m1 qChild qChild (rEll_pos K)
      U_gathered (levelFilterTapFixed K p) := by
  intro t1 r qChild m1 B_in B_slot U_gathered
  funext j1 k2
  exact kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_raw_bounds
    t1 r m1 qChild B_in qChild qChild (rEll_pos K) (foldedHalfWidth_m1Ell_pos K p)
    U_gathered (levelFilterTapFixed K p)
    (fun _ _ => wordWidthBounds_quantizeComplexFixed_levelBIn K qChild x _)
    (fitsSignedWord_levelFilterTapFixed K p)
    j1 k2

/-- Multi-level recursive `FastDFT` operator (`fastDFTRecursive`, Section 7.1 (`sec:alg-spec`)
Listing 1 (`lst:multiply`) and Algorithm 1 (`alg:main`)):
- At base leaf nodes (`isBaseLeaf K p = true` or `K < 2`), executes `baseRadix2FFTQuant K p x` and
  quantizes into `FixedComplex (p + 2)` via `quantizeComplexFixed (p + 2)`.
- At internal nodes (`!isBaseLeaf K p` and `2 ≤ K`), executes the three stages of Listing 1 (`lst:multiply`):
  1. **Step 1 (Sinc-Gaussian Fractional-Shift Row Spreading, Section 6.2 (`sec:kronecker`) Theorem 6.3 (`thm:spread`))**:
     Decimates `x` via `oddStrideGather` into `U_gathered : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p)`
     and applies `kroneckerMatrixSpreadFixed` with `kroneckerSlotBitsRaw (qChildEll K p) (levelBIn K x) (m1Ell K p) (foldedHalfWidth (m1Ell K p) (rEll K))`
     and the unclamped `levelFilterTapFixed K p`.
  2. **Step 2 (Quantized Pre-Twist, Radix-2 Polynomial Transform (`radix2SyntheticFFTQuant`), Quantized Post-Twist, Recursive Child Calls & `oddColScatter`, Section 4.1 (`sec:twisted`) Proposition 4.1 (`thm:twisted`))**:
     Applies `preTwistQuantRoots`, `radix2SyntheticFFTQuant`, `postTwistQuantRoots`, the $t_{1,\ell}$
     recursive child calls `fastDFTRecursive (k2Ell K) (pChildEll K p)`, and `oddColScatter`.
  3. **Step 3 (2-Term Backward-Shift Cyclic Bidiagonal Deconvolution + Open-Chain Nyquist Solver + `freqScatter`, Section 5.1 (`sec:deconv-thm`) Theorem 5.1 (`thm:deconv`) and Section 5.2 (`sec:solvers`))**:
     Solves the Nyquist column `u2.val = rEll K / 2` via `nyquistColumnSolveQuant` (open-chain
     particular recurrence + alternating-sum correction `nyquistModeSum K x`), solves non-Nyquist
     columns `u2.val ≠ rEll K / 2` via `cyclicBidiagPrevSolveQuant (qChildEll K p) (passbandC0 K p u2) (passbandC1 K p u2)`,
     scatters via `freqScatter`, and quantizes to `FixedComplex (p + 2)` via `quantizeComplexFixed (p + 2)`. -/
noncomputable def fastDFTRecursive (K p : ℕ)
    (x : Fin (2 ^ K) → ℂ) : Fin (2 ^ K) → FixedComplex (p + 2) :=
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let m1 := m1Ell K p
    let B_in := levelBIn K x
    let B_slot := kroneckerSlotBitsRaw qChild B_in m1 (foldedHalfWidth m1 r)
    have hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    have ht1_pos : 0 < t1 := t1Ell_pos K
    have hr_pos : 0 < r := rEll_pos K
    haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
    have hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    -- Step 1: Odd-stride gather + 2-product Kronecker Sinc-Gaussian fractional-shift row spreading
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => quantizeComplexFixed qChild (x j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixed t1 r m1 B_slot qChild qChild hr_pos U_gathered (levelFilterTapFixed K p)
    let U_spread : Fin t1 → Fin r → ℂ :=
      fun j1 k2 => (U_spreadFixed j1 k2).toComplex
    -- Step 2: Quantized pre-twist, radix-2 polynomial transform (`radix2SyntheticFFTQuant`) over C[y]/(y^r + 1), quantized post-twist, recursive child calls, oddColScatter
    let U_pre : Fin t1 → Fin r → ℂ :=
      preTwistQuantRoots qChild U_spread
    let Q_syn : Fin t1 → Fin r → ℂ :=
      radix2SyntheticFFTQuant qChild (k1Ell K) c1 U_pre
    let Q_post : Fin t1 → Fin r → ℂ :=
      postTwistQuantRoots qChild Q_syn
    let Q_hat : Fin t1 → Fin r → ℂ :=
      fun v1 u2 => (fastDFTRecursive (k2Ell K) (pChildEll K p) (Q_post v1) u2).toComplex
    let Y_mat : Fin t1 → Fin r → ℂ :=
      oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hat
    -- Step 3: 2-term backward-shift cyclic bidiagonal deconvolution + Nyquist open-chain solver at u2 = r / 2
    let Z_mat : Fin t1 → Fin r → ℂ :=
      fun u1 u2 =>
        if u2.val = r / 2 then
          nyquistColumnSolveQuant qChild (passbandC0 K p u2) (fun m => Y_mat m u2) (nyquistModeSum K x) u1
        else
          cyclicBidiagPrevSolveQuant qChild (passbandC0 K p u2) (passbandC1 K p u2) (fun m => Y_mat m u2) u1
    fun u => quantizeComplexFixed (p + 2) (freqScatter t1 r hR_eq Z_mat u)
  else
    fun u => quantizeComplexFixed (p + 2) (baseRadix2FFTQuant K p x u)
termination_by K
decreasing_by
  unfold k2Ell
  omega

/-- Unfolding equation for `fastDFTRecursive` at base leaf levels (`isBaseLeaf K p = true`). -/
theorem fastDFTRecursive_of_isBaseLeaf {K p : ℕ} (h : isBaseLeaf K p = true)
    (x : Fin (2 ^ K) → ℂ) :
    fastDFTRecursive K p x =
      fun u => quantizeComplexFixed (p + 2) (baseRadix2FFTQuant K p x u) := by
  rw [fastDFTRecursive]
  simp [h]

/-- **Unconditional Level-$(K, p)$ Two-Mode Poisson Residual Bound
(`level_concretePoissonResidual_twoMode_le`, Theorem 4.2 (`thm:poisson`) and Theorem 5.1(1) (`thm:deconv`))**:
For any level $(K, p)$ with $p \ge 8$ and any input vector $x : \text{Fin}(t_{1,\ell} \cdot r_\ell) \to \mathbb{C}$,
the 2D-to-1D spatial residual of the concrete two-mode Sinc-Gaussian Poisson residual
(`concretePoissonResidual` from `PoissonKernel.lean`) satisfies:
$$\|\text{poissonSpatialResidual } x \, (\text{concretePoissonResidual } \alpha_\ell \, m_{1,\ell} \, \{0, 1\}) \, u_1 \, u_2\| \le \left(0.4 \cdot 2^{-p_{\text{child},\ell}} + 0.15 \cdot 2^{-p_{\text{work},\ell}}\right) \|x\|_\infty.$$ -/
theorem level_concretePoissonResidual_twoMode_le {K p : ℕ} (hp : 8 ≤ p)
    (x : Fin (t1Ell K * rEll K) → ℂ) (u1 : Fin (t1Ell K)) (u2 : Fin (rEll K)) :
    let pWork := pWorkEll K p
    let pChild := pChildEll K p
    let alpha := alphaEll K p
    let m1 := m1Ell K p
    ‖poissonSpatialResidual x
      (concretePoissonResidual alpha m1 ({0, 1} : Finset ℤ)) u1 u2‖ ≤
      ((4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
        (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) *
        vecInfNorm x := by
  have hpWork : 8 ≤ pWorkEll K p := by unfold pWorkEll; omega
  have hpChild : pWorkEll K p ≤ pChildEll K p := by unfold pChildEll; omega
  exact norm_poissonSpatialResidual_concretePoissonResidual_twoMode_le
    (pWorkEll K p) (pChildEll K p) hpWork hpChild (t1Ell_pos K) (rEll_pos K) x u1 u2

/-- Exact index agreement between `strideModIndex` and `strideFin` when `R = t1 * r`. -/
theorem strideModIndex_eq_cast_strideFin {t1 r R : ℕ} (hR_pos : 0 < R) (hR_eq : R = t1 * r)
    (j1 : Fin t1) (m : Fin r) :
    strideModIndex t1 r R hR_pos j1 m = Fin.cast hR_eq.symm (strideFin j1 m) := by
  apply Fin.ext
  unfold strideModIndex strideFin
  dsimp only [Fin.val_cast]
  have hlt : j1.val + m.val * t1 < R := by
    rw [hR_eq]
    exact (strideFin j1 m).isLt
  exact Nat.mod_eq_of_lt hlt

/-- **Unconditional Step 1 Sinc-Gaussian Row-Spreading Error and Norm Bound
(`matInfNorm_fastDFTRecursive_step1_sub_le`, Section 6.2 (`sec:kronecker`) Theorem 6.3 (`thm:spread`)
and Section 6.3 (`sec:forward-error`) Lemma 6.5 (`lem:forward`))**:
At any level $(K, p)$ with $8 \le p$, the 2-product Kronecker spreading output
`U_spread j1 k2 = (kroneckerMatrixSpreadFixed ... j1 k2).toComplex` in `fastDFTRecursive`
approximates the exact Sinc-Gaussian `spreadArray` matrix `U_true` within:
$$\|U_{\text{spread}} - U_{\text{true}}\|_\infty \le (2 m_{1,\ell} + 2) \cdot \frac{122}{400} \cdot 2^{-p_{\text{child},\ell}} \max(1, \|x\|_\infty),$$
and satisfies $\|U_{\text{true}}\|_\infty \le (2 m_{1,\ell} + 1) \max(1, \|x\|_\infty)$ and
$\|U_{\text{spread}}\|_\infty \le (2 m_{1,\ell} + 2) \max(1, \|x\|_\infty)$. -/
theorem matInfNorm_fastDFTRecursive_step1_sub_le {K p : ℕ} (hp : 8 ≤ p) (x : Fin (2 ^ K) → ℂ) :
    let t1 := t1Ell K
    let r := rEll K
    let qChild := qChildEll K p
    let pChild := pChildEll K p
    let m1 := m1Ell K p
    let alpha := alphaEll K p
    let B_in := levelBIn K x
    let B_slot := kroneckerSlotBitsRaw qChild B_in m1 (foldedHalfWidth m1 r)
    let hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    let hr_pos : 0 < r := rEll_pos K
    let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => quantizeComplexFixed qChild (x j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixed t1 r m1 B_slot qChild qChild hr_pos U_gathered (levelFilterTapFixed K p)
    let U_spread : Fin t1 → Fin r → ℂ := fun j1 k2 => (U_spreadFixed j1 k2).toComplex
    let U_true : Fin t1 → Fin r → ℂ :=
      spreadArray hr_pos m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))
    let W := (windowLengthEll K p : ℝ)
    let M := max 1 (vecInfNorm x)
    matInfNorm U_true ≤ W * M ∧
      matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) ≤
        (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M ∧
      matInfNorm U_spread ≤ (W + 1) * M := by
  intro t1 r qChild pChild m1 alpha B_in B_slot hR_pos hr_pos hR_eq xCast
    U_gathered U_spreadFixed U_spread U_true W M
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_ge_norm : vecInfNorm x ≤ M := le_max_right 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have hcard_Icc : (Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)).card = windowLengthEll K p := by
    rw [Int.card_Icc]
    unfold windowLengthEll windowLength
    omega
  have hW_pos : 0 < W := by
    change 0 < ((2 * m1 + 1 : ℕ) : ℝ)
    positivity
  have hU_true_le : matInfNorm U_true ≤ W * M := by
    apply matInfNorm_le _ (by positivity)
    intro j1 k2
    unfold U_true spreadArray
    have hterm : ∀ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
        ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
          (filterTap alpha m1 t1 j1 d : ℂ)‖ ≤ M := by
      intro d _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hx_le : ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))‖ ≤ M :=
        (norm_le_vecInfNorm x _).trans hM_ge_norm
      have hf_le : |filterTap alpha m1 t1 j1 d| ≤ 1 := abs_filterTap_le_one alpha m1 t1 j1 d
      calc
        ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))‖ *
            |filterTap alpha m1 t1 j1 d|
          ≤ M * 1 := mul_le_mul hx_le hf_le (abs_nonneg _) (le_of_lt hM_pos)
        _ = M := mul_one M
    calc
      ‖∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
          xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
            (filterTap alpha m1 t1 j1 d : ℂ)‖
        ≤ ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
            ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
              (filterTap alpha m1 t1 j1 d : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), M := Finset.sum_le_sum hterm
      _ = W * M := by simp [Finset.sum_const, hcard_Icc, W, nsmul_eq_mul]
  have hstep1_eq := fastDFTRecursive_step1_eq_refMatrixSpreadFixed K p x
  have h2q_eq : (2 : ℝ) ^ (-(qChild : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
    have hexp : -(qChild : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by
      change -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ)
      omega
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
    ring
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(qChild : ℤ)) := zpow_pos (by norm_num) _
  have hsqrt_le : Real.sqrt 2 ≤ (72 / 50 : ℝ) := sqrt_two_le
  have hsub_le : matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) ≤
      (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    apply matInfNorm_le _ (by positivity)
    intro j1 k2
    have hU_ref : U_spread j1 k2 =
        (refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered
          (levelFilterTapFixed K p) j1 k2).toComplex :=
      congrArg FixedComplex.toComplex
        (congrFun (congrFun (fastDFTRecursive_step1_eq_refMatrixSpreadFixed K p x) j1) k2)
    rw [hU_ref]
    let S_unrounded : ℂ :=
      ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
        quantizeComplex qChild (xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))) *
          (quantizeReal qChild (filterTap alpha m1 t1 j1 d) : ℂ)
    have hU_gath : ∀ m : Fin r,
        (U_gathered j1 m).toComplex = quantizeComplex qChild (xCast (strideFin j1 m)) := by
      intro m
      change (quantizeComplexFixed qChild
        (x (strideModIndex t1 r (2 ^ K) hR_pos j1 m))).toComplex = _
      rw [strideModIndex_eq_cast_strideFin hR_pos hR_eq j1 m]
      rfl
    have hround_diff :
        ‖(refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered
            (levelFilterTapFixed K p) j1 k2).toComplex - S_unrounded‖ ≤
          (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) := by
      let S_re : ℤ := rawCyclicConv r m1 hr_pos (fun j2 => (U_gathered j1 j2).re)
        (levelFilterTapFixed K p j1) k2
      let S_im : ℤ := rawCyclicConv r m1 hr_pos (fun j2 => (U_gathered j1 j2).im)
        (levelFilterTapFixed K p j1) k2
      have hre_eq : S_unrounded.re = (S_re : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [S_unrounded, S_re, rawCyclicConv, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        have hmod : cyclicModIndex r hr_pos ((k2.val : ℤ) - d) =
            intModFin r hr_pos ((k2.val : ℤ) - d) := rfl
        rw [hmod, ← hU_gath]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          FixedComplex.toComplex_re, quantizeReal, levelFilterTapFixed, Int.cast_mul,
          zpow_neg, zpow_natCast]
        ring
      have him_eq : S_unrounded.im = (S_im : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [S_unrounded, S_im, rawCyclicConv, Complex.im_sum, Int.cast_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        have hmod : cyclicModIndex r hr_pos ((k2.val : ℤ) - d) =
            intModFin r hr_pos ((k2.val : ℤ) - d) := rfl
        rw [hmod, ← hU_gath]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          FixedComplex.toComplex_im, quantizeReal, levelFilterTapFixed, Int.cast_mul,
          zpow_neg, zpow_natCast]
        ring
      have hre_le :
          |((refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered
              (levelFilterTapFixed K p) j1 k2).toComplex - S_unrounded).re| ≤
            (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [refMatrixSpreadFixed, refRowSpreadFixed, Complex.sub_re,
          FixedComplex.toComplex_re, hre_eq]
        change |(roundShiftInt S_re qChild : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) -
          (S_re : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ))| ≤ _
        rw [← sub_mul, abs_mul, abs_of_pos h2q_pos]
        exact mul_le_mul_of_nonneg_right (abs_roundShiftInt_sub_div_le S_re qChild) (le_of_lt h2q_pos)
      have him_le :
          |((refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered
              (levelFilterTapFixed K p) j1 k2).toComplex - S_unrounded).im| ≤
            (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [refMatrixSpreadFixed, refRowSpreadFixed, Complex.sub_im,
          FixedComplex.toComplex_im, him_eq]
        change |(roundShiftInt S_im qChild : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) -
          (S_im : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ))| ≤ _
        rw [← sub_mul, abs_mul, abs_of_pos h2q_pos]
        exact mul_le_mul_of_nonneg_right (abs_roundShiftInt_sub_div_le S_im qChild) (le_of_lt h2q_pos)
      calc
        ‖(refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered
            (levelFilterTapFixed K p) j1 k2).toComplex - S_unrounded‖
          ≤ Real.sqrt 2 * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) :=
            norm_complex_le_of_re_im_le (by positivity) hre_le him_le
        _ = (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) := by ring
    have hsum_diff :
        ‖S_unrounded - U_true j1 k2‖ ≤
          W * ((Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M) := by
      unfold S_unrounded U_true spreadArray
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
          ‖quantizeComplex qChild (xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))) *
              (quantizeReal qChild (filterTap alpha m1 t1 j1 d) : ℂ) -
            xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
              (filterTap alpha m1 t1 j1 d : ℂ)‖ ≤
            (Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
        intro d _
        let z : ℂ := xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))
        let f : ℝ := filterTap alpha m1 t1 j1 d
        have hz_norm : ‖z‖ ≤ M := (norm_le_vecInfNorm x _).trans hM_ge_norm
        have hqf_le : |quantizeReal qChild f| ≤ 1 :=
          abs_quantizeReal_le_one_of_abs_le_one qChild (abs_filterTap_le_one alpha m1 t1 j1 d)
        have hqf_sub : |quantizeReal qChild f - f| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) :=
          abs_quantizeReal_sub_self_le qChild f
        have hqz_sub : ‖quantizeComplex qChild z - z‖ ≤
            (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) :=
          norm_quantizeComplex_sub_self_le qChild z
        have hdecomp :
            quantizeComplex qChild z * (quantizeReal qChild f : ℂ) - z * (f : ℂ) =
              (quantizeComplex qChild z - z) * (quantizeReal qChild f : ℂ) +
                z * ((quantizeReal qChild f - f : ℝ) : ℂ) := by
          push_cast; ring
        rw [hdecomp]
        have h1 : ‖(quantizeComplex qChild z - z) * (quantizeReal qChild f : ℂ)‖ ≤
            (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc
            ‖quantizeComplex qChild z - z‖ * |quantizeReal qChild f|
              ≤ ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ))) * 1 :=
                mul_le_mul hqz_sub hqf_le (abs_nonneg _) (by positivity)
            _ = (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * 1 := by ring
            _ ≤ (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by gcongr
        have h2 : ‖z * ((quantizeReal qChild f - f : ℝ) : ℂ)‖ ≤
            (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc
            ‖z‖ * |quantizeReal qChild f - f|
              ≤ M * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) :=
                mul_le_mul hz_norm hqf_sub (abs_nonneg _) (le_of_lt hM_pos)
            _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by ring
        have htri := norm_add_le
          ((quantizeComplex qChild z - z) * (quantizeReal qChild f : ℂ))
          (z * ((quantizeReal qChild f - f : ℝ) : ℂ))
        linarith
      calc
        ‖∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
            (quantizeComplex qChild (xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))) *
                (quantizeReal qChild (filterTap alpha m1 t1 j1 d) : ℂ) -
              xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
                (filterTap alpha m1 t1 j1 d : ℂ))‖
          ≤ ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
              ‖quantizeComplex qChild (xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))) *
                  (quantizeReal qChild (filterTap alpha m1 t1 j1 d) : ℂ) -
                xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
                  (filterTap alpha m1 t1 j1 d : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
              ((Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M) :=
            Finset.sum_le_sum hterm
        _ = W * ((Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M) := by
            simp [Finset.sum_const, hcard_Icc, W, nsmul_eq_mul]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered
        (levelFilterTapFixed K p) j1 k2).toComplex
      S_unrounded (U_true j1 k2)
    have hround_M : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
        (Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
      have : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
          (Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * 1 := by nlinarith
      exact this.trans (by gcongr)
    have hcoeff : (Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
        (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
      rw [h2q_eq]
      nlinarith
    have hsum_le2 :
        (W + 1) * ((Real.sqrt 2 / 2 + 1 / 2) * (2 : ℝ) ^ (-(qChild : ℤ))) * M ≤
          (W + 1) * ((122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) * M := by
      have : 0 ≤ (W + 1) * M := by positivity
      nlinarith
    nlinarith
  have hU_spread_le : matInfNorm U_spread ≤ (W + 1) * M := by
    have hW_le : W ≤ 2 * (pChild : ℝ) + 1 := by
      unfold W pChild
      exact_mod_cast windowLengthEll_le_two_mul_pChildEll_add_one K p
    have hpChild_ge : 16 ≤ pChild := by
      unfold pChild pChildEll pWorkEll
      omega
    have hpow_le : ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 := by
      have h1 : pChild + 1 ≤ 2 ^ pChild := Nat.lt_two_pow_self
      have h1r : (pChild : ℝ) + 1 ≤ (2 : ℝ) ^ pChild := by exact_mod_cast h1
      calc
        ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (2 : ℝ) ^ pChild * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right h1r (le_of_lt h2p_pos)
        _ = 1 := two_pow_mul_two_zpow_neg pChild
    have herr_le_M : (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M ≤ M := by
      have h1 : (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 := by
        have hW1 : W + 1 ≤ 2 * ((pChild : ℝ) + 1) := by linarith
        calc
          (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))
            ≤ (2 * ((pChild : ℝ) + 1)) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
              nlinarith
          _ = (244 / 400 : ℝ) * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
          _ ≤ (244 / 400 : ℝ) * 1 := by nlinarith
          _ ≤ 1 := by norm_num
      nlinarith
    apply matInfNorm_le _ (by positivity)
    intro j1 k2
    have h1 := (norm_le_matInfNorm (fun i1 i2 => U_spread i1 i2 - U_true i1 i2) j1 k2).trans hsub_le
    have h2 := (norm_le_matInfNorm U_true j1 k2).trans hU_true_le
    have htri : ‖U_spread j1 k2‖ ≤ ‖U_spread j1 k2 - U_true j1 k2‖ + ‖U_true j1 k2‖ := by
      simpa using norm_add_le (U_spread j1 k2 - U_true j1 k2) (U_true j1 k2)
    linarith
  exact ⟨hU_true_le, hsub_le, hU_spread_le⟩

/-- `syntheticFFT c1` is a contraction in `matInfNorm` on `Fin t1 → Fin r → ℂ`. -/
theorem matInfNorm_syntheticFFT_sub_le {t1 r : ℕ} (ht1 : 0 < t1) (c1 : ℕ)
    (P1 P2 : Fin t1 → Fin r → ℂ) :
    matInfNorm (fun v1 k2 => syntheticFFT c1 P1 v1 k2 - syntheticFFT c1 P2 v1 k2) ≤
      matInfNorm (fun j1 k2 => P1 j1 k2 - P2 j1 k2) := by
  have ht1_r : (0 : ℝ) < (t1 : ℝ) := Nat.cast_pos.mpr ht1
  apply matInfNorm_le _ (matInfNorm_nonneg _)
  intro v1 k2
  unfold syntheticFFT
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hnorm_inv : ‖((t1 : ℝ)⁻¹ : ℂ)‖ = (t1 : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (le_of_lt ht1_r)]
  rw [norm_mul, hnorm_inv]
  have hterm : ∀ j1 : Fin t1,
      ‖negacyclicShift (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) (P1 j1) k2 -
        negacyclicShift (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) (P2 j1) k2‖ ≤
        matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2) := by
    intro j1
    rw [congrFun (negacyclicShift_sub_poly (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ))
      (P1 j1) (P2 j1)).symm k2]
    have h1 := norm_le_vecInfNorm
      (negacyclicShift (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) (fun m => P1 j1 m - P2 j1 m)) k2
    rw [vecInfNorm_negacyclicShift] at h1
    have h2 : vecInfNorm (fun m => P1 j1 m - P2 j1 m) ≤
        matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2) := by
      apply vecInfNorm_le _ (matInfNorm_nonneg _)
      intro m
      exact norm_le_matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2) j1 m
    exact h1.trans h2
  have hsum :
      ‖∑ j1 : Fin t1,
          (negacyclicShift (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) (P1 j1) k2 -
            negacyclicShift (2 * (c1 : ℤ) * (j1.val : ℤ) * (v1.val : ℤ)) (P2 j1) k2)‖ ≤
        (t1 : ℝ) * matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2) := by
    calc
      ‖∑ j1 : Fin t1, _‖
        ≤ ∑ j1 : Fin t1, ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ _j1 : Fin t1, matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2) :=
          Finset.sum_le_sum (fun j1 _ => hterm j1)
      _ = (t1 : ℝ) * matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (t1 : ℝ)⁻¹ * ‖∑ j1 : Fin t1, _‖
      ≤ (t1 : ℝ)⁻¹ * ((t1 : ℝ) * matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (le_of_lt ht1_r))
    _ = matInfNorm (fun i1 i2 => P1 i1 i2 - P2 i1 i2) :=
        inv_mul_cancel_left₀ (ne_of_gt ht1_r) _

/-- `syntheticFFT c1` does not increase `matInfNorm`. -/
theorem matInfNorm_syntheticFFT_le {t1 r : ℕ} (ht1 : 0 < t1) (c1 : ℕ)
    (P : Fin t1 → Fin r → ℂ) :
    matInfNorm (syntheticFFT c1 P) ≤ matInfNorm P := by
  have h := matInfNorm_syntheticFFT_sub_le ht1 c1 P (fun (_ : Fin t1) (_ : Fin r) => (0 : ℂ))
  have h0 : ∀ v1 k2, syntheticFFT c1 (fun (_ : Fin t1) (_ : Fin r) => (0 : ℂ)) v1 k2 = 0 := by
    intro v1 k2
    unfold syntheticFFT negacyclicShift
    simp
  simpa [h0] using h

/-- `preTwistExact` is an isometry in `matInfNorm`. -/
theorem matInfNorm_preTwistExact_le {t1 r : ℕ} (P : Fin t1 → Fin r → ℂ) :
    matInfNorm (preTwistExact P) ≤ matInfNorm P := by
  apply matInfNorm_le _ (matInfNorm_nonneg P)
  intro j1 k2
  unfold preTwistExact preTwist
  rw [norm_mul, norm_zetaPow, one_mul]
  exact norm_le_matInfNorm P j1 k2

/-- `postTwistExact` is an isometry in `matInfNorm`. -/
theorem matInfNorm_postTwistExact_le {t1 r : ℕ} (Q : Fin t1 → Fin r → ℂ) :
    matInfNorm (postTwistExact Q) ≤ matInfNorm Q := by
  apply matInfNorm_le _ (matInfNorm_nonneg Q)
  intro v1 k2
  unfold postTwistExact postTwist
  rw [norm_mul, norm_zetaPow, one_mul]
  exact norm_le_matInfNorm Q v1 k2

/-- Exact agreement between `oddColKeyMinus` (`TMPrimitives.lean`) and `oddStrideIndex` (`SyntheticFFT.lean`). -/
theorem oddColKeyMinus_eq_oddStrideIndex {t1 : ℕ} (ht1 : 0 < t1) (u2 : ℕ) (v1 : Fin t1) :
    oddColKeyMinus t1 ht1 u2 v1 = oddStrideIndex u2 v1 := by
  apply Fin.ext
  apply Nat.cast_injective (R := ℤ)
  rw [coe_oddStrideIndex]
  unfold oddColKeyMinus
  dsimp only
  rw [Int.natCast_emod, Int.natCast_mul]
  have hcast : ((2 * u2 + t1 - 1 : ℕ) : ℤ) = (2 * (u2 : ℤ) - 1) + (t1 : ℤ) := by omega
  rw [hcast, add_mul, Int.add_mul_emod_self_left]

/-- `vecInfNorm` is invariant under `Fin.cast`. -/
theorem vecInfNorm_comp_cast {R1 R2 : ℕ} (h : R1 = R2) (x : Fin R1 → ℂ) :
    vecInfNorm (fun idx : Fin R2 => x (Fin.cast h.symm idx)) = vecInfNorm x := by
  subst h; rfl

/-- `normDFT1D` commutes with `Fin.cast`. -/
theorem normDFT1D_comp_cast {R1 R2 : ℕ} (h : R1 = R2) (x : Fin R1 → ℂ) (u : Fin R2) :
    normDFT1D (fun idx : Fin R2 => x (Fin.cast h.symm idx)) u =
      normDFT1D x (Fin.cast h.symm u) := by
  subst h; rfl

/-- Even-dimension specialization of `nyquist_alternating_sum_eq` at $u_2 = r / 2$. -/
theorem nyquist_alternating_sum_eq_of_even {t1 r : ℕ}
    (ht1 : 2 ∣ t1) (hr : 2 ∣ r) (ht1_pos : 0 < t1) (_hr_pos : 0 < r)
    (x : Fin (t1 * r) → ℂ) (u2 : Fin r) (hu2 : u2.val = r / 2) :
    (∑ u1 : Fin t1, (-1 : ℂ) ^ u1.val * normDFT1D x (freqFin u1 u2)) =
      (Complex.I / (r : ℂ)) *
        ∑ j2 : Fin r,
          (-1 : ℂ) ^ j2.val *
            x ⟨t1 / 2 + t1 * j2.val, by
              have := j2.isLt
              have : t1 / 2 < t1 := Nat.div_lt_self ht1_pos (by norm_num)
              nlinarith⟩ := by
  rcases ht1 with ⟨h1, rfl⟩
  rcases hr with ⟨h2, rfl⟩
  have hh1 : 0 < h1 := by omega
  have hh2 : 0 < h2 := by omega
  have hdiv1 : (2 * h1) / 2 = h1 := Nat.mul_div_right h1 (by norm_num)
  have hdiv2 : (2 * h2) / 2 = h2 := Nat.mul_div_right h2 (by norm_num)
  have hu2_val : u2.val = h2 := hu2.trans hdiv2
  have hfreq : ∀ u1 : Fin (2 * h1),
      freqFin u1 u2 = ⟨h2 + (2 * h2) * u1.val, by have := u1.isLt; nlinarith⟩ := by
    intro u1
    ext
    simp [freqFin, hu2_val]
  simp_rw [hfreq, hdiv1]
  exact nyquist_alternating_sum_eq hh1 hh2 x

/-- At the Nyquist column $u_2 = r_\ell / 2$ ($K \ge 2$), the alternating sum of the true 1D DFT
column `u1 ↦ normDFT1D xCast (freqFin u1 u2)` equals `nyquistModeSum K x`
(Section 5.1 (`sec:deconv-thm`), Theorem 5.1(3) (`thm:deconv`)). -/
theorem sum_alternating_normDFT1D_freqFin_eq_nyquistModeSum {K : ℕ} (hK : 2 ≤ K)
    (x : Fin (2 ^ K) → ℂ) (u2 : Fin (rEll K)) (hu2 : u2.val = rEll K / 2) :
    let hR_eq : 2 ^ K = t1Ell K * rEll K := (t1Ell_mul_rEll K).symm
    let xCast : Fin (t1Ell K * rEll K) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    (∑ u1 : Fin (t1Ell K), (-1 : ℂ) ^ u1.val * normDFT1D xCast (freqFin u1 u2)) =
      nyquistModeSum K x := by
  intro hR_eq xCast
  have hk1 : 1 ≤ k1Ell K := by unfold k1Ell; omega
  have hk2 : 1 ≤ k2Ell K := by unfold k2Ell; omega
  have ht1_even : 2 ∣ t1Ell K := by
    unfold t1Ell
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : k1Ell K ≠ 0) with ⟨m, hm⟩
    rw [hm, pow_succ']
    exact dvd_mul_right 2 (2 ^ m)
  have hr_even : 2 ∣ rEll K := by
    unfold rEll
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : k2Ell K ≠ 0) with ⟨m, hm⟩
    rw [hm, pow_succ']
    exact dvd_mul_right 2 (2 ^ m)
  rw [nyquist_alternating_sum_eq_of_even ht1_even hr_even (t1Ell_pos K) (rEll_pos K) xCast u2 hu2]
  unfold nyquistModeSum
  congr 1
  refine Finset.sum_congr rfl (fun j2 _ => ?_)
  congr 1
  dsimp [xCast]
  congr 1
  ext
  have hlt : t1Ell K / 2 + t1Ell K * j2.val < 2 ^ K := by
    rw [hR_eq]
    have := j2.isLt
    have : t1Ell K / 2 < t1Ell K := Nat.div_lt_self (t1Ell_pos K) (by norm_num)
    nlinarith
  exact (Nat.mod_eq_of_lt hlt).symm

/-- Difference of two `nyquistColumnSolve` evaluations sharing the same `c0` and `alt`. -/
theorem nyquistColumnSolve_sub_same_alt {t1 : ℕ} (c0 : ℝ) (B1 B2 : Fin t1 → ℂ)
    (alt : ℂ) (u1 : Fin t1) :
    nyquistColumnSolve c0 B1 alt u1 - nyquistColumnSolve c0 B2 alt u1 =
      nyquistColumnSolve c0 (fun m => B1 m - B2 m) 0 u1 := by
  simp only [nyquistColumnSolve, nyquistOpenChainParticular]
  have hpart : ∀ m : Fin t1,
      nyquistOpenChainParticularAux c0 B1 m.val m.isLt -
        nyquistOpenChainParticularAux c0 B2 m.val m.isLt =
      nyquistOpenChainParticularAux c0 (fun j => B1 j - B2 j) m.val m.isLt :=
    fun m => nyquistOpenChainParticularAux_sub c0 B1 B2 m.val m.isLt
  have hsum :
      (∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticularAux c0 B1 m.val m.isLt) -
        (∑ m : Fin t1, (-1 : ℂ) ^ m.val * nyquistOpenChainParticularAux c0 B2 m.val m.isLt) =
      ∑ m : Fin t1, (-1 : ℂ) ^ m.val *
        nyquistOpenChainParticularAux c0 (fun j => B1 j - B2 j) m.val m.isLt := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← mul_sub, hpart m]
  rw [← hpart u1, ← hsum]
  ring

/-- Difference between `cyclicBidiagPrevSolve` and any solution `Z` of the backward-shift system
at a non-Nyquist column $u_2 \ne r_\ell / 2$. -/
theorem passbandC0_passbandC1_prevSolve_sub_eq {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (u2 : Fin (rEll K)) (hu2 : u2.val ≠ rEll K / 2)
    (B Z B_true : Fin (t1Ell K) → ℂ)
    (hZ : ∀ m : Fin (t1Ell K),
      letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
      (passbandC0 K p u2 : ℂ) * Z m + (passbandC1 K p u2 : ℂ) * Z (cyclicPrev m) = B_true m) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    (fun m => cyclicBidiagPrevSolve (passbandC0 K p u2) (passbandC1 K p u2) B m - Z m) =
      cyclicBidiagPrevSolve (passbandC0 K p u2) (passbandC1 K p u2) (fun m => B m - B_true m) := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  symm
  apply cyclicBidiagPrevSolve_of_spec
    (passbandC0 K p u2) (passbandC1 K p u2) (fun m => B m - B_true m)
    (fun m => cyclicBidiagPrevSolve (passbandC0 K p u2) (passbandC1 K p u2) B m - Z m)
    (lt_of_lt_of_le (by norm_num) (passbandC0_passbandC1_max_ge hp u2))
    (passbandC0_passbandC1_min_nonneg K p u2)
    (lt_of_le_of_lt (gHat_ratio_pow_t1_le_015 K p hK hp u2 hu2) (by norm_num))
  intro m
  have h1 := passbandC0_passbandC1_prevSolve_spec hK hp u2 hu2 B m
  have h2 := hZ m
  linear_combination h1 - h2

/-- Two-mode Poisson decomposition of `normDFT2D U_true` at level `(K, p)` (`8 ≤ p`) for any
spatial window half-width `m1 ≥ m1Ell K p`. -/
theorem normDFT2D_spreadArray_twoMode_sub_le_of_ge {K p m1 : ℕ} (hp : 8 ≤ p)
    (hm1 : m1Ell K p ≤ m1)
    (x : Fin (2 ^ K) → ℂ) (u2 : Fin (rEll K)) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let t1 := t1Ell K
    let r := rEll K
    let alpha := alphaEll K p
    let pWork := pWorkEll K p
    let pChild := pChildEll K p
    let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let U_true : Fin t1 → Fin r → ℂ :=
      spreadArray (rEll_pos K) m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))
    let Z_col : Fin t1 → ℂ := fun m => normDFT1D xCast (freqFin m u2)
    let B_true : Fin t1 → ℂ :=
      fun m => (passbandC0 K p u2 : ℂ) * Z_col m + (passbandC1 K p u2 : ℂ) * Z_col (cyclicPrev m)
    let M := max 1 (vecInfNorm x)
    vecInfNorm Z_col ≤ M ∧
      vecInfNorm B_true ≤ M ∧
      ∀ u1 : Fin t1,
        ‖normDFT2D U_true u1 u2 - B_true u1‖ ≤
          ((4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
            (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) * M := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  intro t1 r alpha pWork pChild hR_eq xCast U_true Z_col B_true M
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_ge_norm : vecInfNorm x ≤ M := le_max_right 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have hxCast_norm : vecInfNorm xCast = vecInfNorm x := vecInfNorm_comp_cast hR_eq x
  have hZ_le : vecInfNorm Z_col ≤ M := by
    apply vecInfNorm_le _ (le_of_lt hM_pos)
    intro m
    calc
      ‖normDFT1D xCast (freqFin m u2)‖
        ≤ vecInfNorm xCast := norm_normDFT1D_le xCast (freqFin m u2)
      _ = vecInfNorm x := hxCast_norm
      _ ≤ M := hM_ge_norm
  have hB_le : vecInfNorm B_true ≤ M := by
    have hc_min := passbandC0_passbandC1_min_nonneg K p u2
    have hc0_nn : 0 ≤ passbandC0 K p u2 := le_trans hc_min (min_le_left _ _)
    have hc1_nn : 0 ≤ passbandC1 K p u2 := le_trans hc_min (min_le_right _ _)
    have hc_sum : passbandC0 K p u2 + passbandC1 K p u2 ≤ 1 := by
      have h := gHat_stopband_alias_nonneg_level K p u2
      unfold passbandC0 passbandC1
      linarith
    apply vecInfNorm_le _ (le_of_lt hM_pos)
    intro m
    have hZm : ‖Z_col m‖ ≤ M := (norm_le_vecInfNorm Z_col m).trans hZ_le
    have hZp : ‖Z_col (cyclicPrev m)‖ ≤ M := (norm_le_vecInfNorm Z_col (cyclicPrev m)).trans hZ_le
    have h1 : ‖(passbandC0 K p u2 : ℂ) * Z_col m‖ ≤ passbandC0 K p u2 * M := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0_nn]
      exact mul_le_mul_of_nonneg_left hZm hc0_nn
    have h2 : ‖(passbandC1 K p u2 : ℂ) * Z_col (cyclicPrev m)‖ ≤ passbandC1 K p u2 * M := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc1_nn]
      exact mul_le_mul_of_nonneg_left hZp hc1_nn
    have htri := norm_add_le ((passbandC0 K p u2 : ℂ) * Z_col m)
      ((passbandC1 K p u2 : ℂ) * Z_col (cyclicPrev m))
    calc
      ‖B_true m‖
        ≤ passbandC0 K p u2 * M + passbandC1 K p u2 * M := htri.trans (add_le_add h1 h2)
      _ = (passbandC0 K p u2 + passbandC1 K p u2) * M := by ring
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hc_sum (le_of_lt hM_pos)
      _ = M := one_mul M
  refine ⟨hZ_le, hB_le, fun u1 => ?_⟩
  have hpoiss := poisson_fractional_shift_identity (t1Ell_pos K) (rEll_pos K) m1 alpha xCast
    ({0, 1} : Finset ℤ) u1 u2
  have hpair :
      (∑ m ∈ ({0, 1} : Finset ℤ),
        (gHat alpha ((u2.val : ℝ) / (r : ℝ) - (m : ℝ)) : ℂ) *
          normDFT1D xCast (freqFin (intModFin t1 (t1Ell_pos K) ((u1.val : ℤ) - m)) u2)) =
      B_true u1 := by
    rw [Finset.sum_pair (by decide : (0 : ℤ) ≠ 1)]
    have h0 : intModFin t1 (t1Ell_pos K) ((u1.val : ℤ) - 0) = u1 := by
      rw [sub_zero]
      exact intModFin_nat_coe t1 (t1Ell_pos K) u1
    have h1 : intModFin t1 (t1Ell_pos K) ((u1.val : ℤ) - 1) = cyclicPrev u1 :=
      intModFin_sub_one_eq_cyclicPrev u1
    rw [h0, h1]
    simp [B_true, Z_col, passbandC0, passbandC1, alpha, r]
  have hsub_eq :
      normDFT2D U_true u1 u2 - B_true u1 =
        poissonSpatialResidual xCast (concretePoissonResidual alpha m1 ({0, 1} : Finset ℤ)) u1 u2 := by
    change normDFT2D (spreadArray (rEll_pos K) m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))) u1 u2 -
      B_true u1 = _
    rw [hpoiss, hpair, add_sub_cancel_left]
  rw [hsub_eq]
  have hpWork : 8 ≤ pWorkEll K p := by unfold pWorkEll; omega
  have hpChild : pWorkEll K p ≤ pChildEll K p := by unfold pChildEll; omega
  have hres := norm_poissonSpatialResidual_concretePoissonResidual_twoMode_le_of_ge
    (pWorkEll K p) (pChildEll K p) m1 hpWork hpChild hm1 (t1Ell_pos K) (rEll_pos K) xCast u1 u2
  rw [hxCast_norm] at hres
  exact hres.trans (mul_le_mul_of_nonneg_left hM_ge_norm (by positivity))

/-- Two-mode Poisson decomposition of `normDFT2D U_true` at level `(K, p)` (`8 ≤ p`):
for every `(u1, u2)`, `normDFT2D U_true u1 u2` approximates the two-term backward-shift combination
`c0 * Z_col u1 + c1 * Z_col (cyclicPrev u1)` within `(0.4 * 2^(-pChild) + 0.15 * 2^(-pWork)) * M`. -/
theorem normDFT2D_spreadArray_twoMode_sub_le {K p : ℕ} (hp : 8 ≤ p)
    (x : Fin (2 ^ K) → ℂ) (u2 : Fin (rEll K)) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let t1 := t1Ell K
    let r := rEll K
    let m1 := m1Ell K p
    let alpha := alphaEll K p
    let pWork := pWorkEll K p
    let pChild := pChildEll K p
    let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let U_true : Fin t1 → Fin r → ℂ :=
      spreadArray (rEll_pos K) m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))
    let Z_col : Fin t1 → ℂ := fun m => normDFT1D xCast (freqFin m u2)
    let B_true : Fin t1 → ℂ :=
      fun m => (passbandC0 K p u2 : ℂ) * Z_col m + (passbandC1 K p u2 : ℂ) * Z_col (cyclicPrev m)
    let M := max 1 (vecInfNorm x)
    vecInfNorm Z_col ≤ M ∧
      vecInfNorm B_true ≤ M ∧
      ∀ u1 : Fin t1,
        ‖normDFT2D U_true u1 u2 - B_true u1‖ ≤
          ((4 / 10 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
            (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) * M :=
  normDFT2D_spreadArray_twoMode_sub_le_of_ge hp (le_refl _) x u2

/-- **Step 2 Error Propagation Bound for `fastDFTRecursive` (`norm_fastDFTRecursive_step2_sub_le`,
Section 4.1 (`sec:twisted`) Proposition 4.1 (`thm:twisted`) and Section 6.3 (`sec:forward-error`)
Lemma 6.5 (`lem:forward`))**:
At any level $(K, p)$ with $8 \le p$, given an error bound `E_child` on the child recursive call
`fastDFTRecursive (k2Ell K) (pChildEll K p)`, the Step 2 output matrix `Y_mat` approximates the
exact 2D DFT `normDFT2D U_true` of the Sinc-Gaussian `spreadArray` within:
$$\|Y_{\text{mat}}(u_1, u_2) - (F_{t_1, r} U_{\text{true}})_{u_1, u_2}\| \le \left((W_\ell + 3) E_{\text{child}} + (W_\ell + 0.18 K + 2) 2^{-p_{\text{child},\ell}}\right) \max(1, \|x\|_\infty).$$ -/
theorem norm_fastDFTRecursive_step2_sub_le {K p : ℕ} (hp : 8 ≤ p)
    {E_child : ℝ} (hE_pos : 0 ≤ E_child) (x : Fin (2 ^ K) → ℂ)
    (hchild : ∀ y : Fin (rEll K) → ℂ,
      vecInfNorm (fun u2 =>
        (fastDFTRecursive (k2Ell K) (pChildEll K p) y u2).toComplex - normDFT1D y u2) ≤
        E_child * max 1 (vecInfNorm y)) :
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let pChild := pChildEll K p
    let m1 := m1Ell K p
    let alpha := alphaEll K p
    let B_in := levelBIn K x
    let B_slot := kroneckerSlotBitsRaw qChild B_in m1 (foldedHalfWidth m1 r)
    let hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    let ht1_pos : 0 < t1 := t1Ell_pos K
    let hr_pos : 0 < r := rEll_pos K
    let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => quantizeComplexFixed qChild (x j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixed t1 r m1 B_slot qChild qChild hr_pos U_gathered (levelFilterTapFixed K p)
    let U_spread : Fin t1 → Fin r → ℂ := fun j1 k2 => (U_spreadFixed j1 k2).toComplex
    let U_true : Fin t1 → Fin r → ℂ :=
      spreadArray hr_pos m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))
    let U_pre : Fin t1 → Fin r → ℂ := preTwistQuantRoots qChild U_spread
    let Q_syn : Fin t1 → Fin r → ℂ := radix2SyntheticFFTQuant qChild (k1Ell K) c1 U_pre
    let Q_post : Fin t1 → Fin r → ℂ := postTwistQuantRoots qChild Q_syn
    let Q_hat : Fin t1 → Fin r → ℂ :=
      fun v1 u2 => (fastDFTRecursive (k2Ell K) pChild (Q_post v1) u2).toComplex
    let Y_mat : Fin t1 → Fin r → ℂ := oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hat
    let W := (windowLengthEll K p : ℝ)
    let M := max 1 (vecInfNorm x)
    ∀ (u1 : Fin t1) (u2 : Fin r),
      ‖Y_mat u1 u2 - normDFT2D U_true u1 u2‖ ≤
        (((W + 3) * E_child) +
          (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ))) * M := by
  intro t1 r c1 qChild pChild m1 alpha B_in B_slot hR_pos ht1_pos hr_pos hR_eq xCast
    U_gathered U_spreadFixed U_spread U_true U_pre Q_syn Q_post Q_hat Y_mat W M u1 u2
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have hW_pos : 0 < W := by
    change 0 < ((2 * m1 + 1 : ℕ) : ℝ)
    positivity
  have hstep1 := matInfNorm_fastDFTRecursive_step1_sub_le hp x
  have hU_true_le : matInfNorm U_true ≤ W * M := hstep1.1
  have hU_sub_le : matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) ≤
      (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := hstep1.2.1
  have hU_spread_le : matInfNorm U_spread ≤ (W + 1) * M := hstep1.2.2
  clear hstep1
  let U_pre_true : Fin t1 → Fin r → ℂ := preTwistExact U_true
  let Q_syn_true : Fin t1 → Fin r → ℂ := syntheticFFT c1 U_pre_true
  let Q_post_true : Fin t1 → Fin r → ℂ := postTwistExact Q_syn_true
  have hU_pre_true_le : matInfNorm U_pre_true ≤ W * M :=
    (matInfNorm_preTwistExact_le U_true).trans hU_true_le
  have hQ_syn_true_le : matInfNorm Q_syn_true ≤ W * M :=
    (matInfNorm_syntheticFFT_le ht1_pos c1 U_pre_true).trans hU_pre_true_le
  have hQ_post_true_le : matInfNorm Q_post_true ≤ W * M :=
    (matInfNorm_postTwistExact_le Q_syn_true).trans hQ_syn_true_le
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h2q_le : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
      (18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
    have hexp : -(qChild : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by
      change -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ)
      omega
    have hpow : (2 : ℝ) ^ (-(qChild : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
      rw [hexp, zpow_add₀ (by norm_num)]
      norm_num
      ring
    rw [hpow]
    have hsqrt := sqrt_two_le
    nlinarith
  have hW_le : W ≤ 2 * (pChild : ℝ) + 1 := by
    unfold W pChild
    exact_mod_cast windowLengthEll_le_two_mul_pChildEll_add_one K p
  have hK_le : (K : ℝ) ≤ (pChild : ℝ) := by
    have : K ≤ pChild := by unfold pChild pChildEll pWorkEll; omega
    exact_mod_cast this
  have hpow_le : ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 := by
    have h1 : pChild + 1 ≤ 2 ^ pChild := Nat.lt_two_pow_self
    have h1r : (pChild : ℝ) + 1 ≤ (2 : ℝ) ^ pChild := by exact_mod_cast h1
    calc
      ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))
        ≤ (2 : ℝ) ^ pChild * (2 : ℝ) ^ (-(pChild : ℤ)) :=
          mul_le_mul_of_nonneg_right h1r (le_of_lt h2p_pos)
      _ = 1 := two_pow_mul_two_zpow_neg pChild
  have hU_pre_sub : matInfNorm (fun j1 k2 => U_pre j1 k2 - U_pre_true j1 k2) ≤
      ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ)) *
        (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    have h1 := matInfNorm_preTwistQuantRoots_sub_le qChild U_spread U_true
    have h2 : 1 + matInfNorm U_spread ≤ (W + 2) * M := by
      linarith only [hU_spread_le, hM_ge_one]
    have h3 : (1 + matInfNorm U_spread) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ))) ≤
        ((W + 2) * M) * ((18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) :=
      mul_le_mul h2 h2q_le (by positivity) (by positivity)
    linarith only [h1, h3, hU_sub_le]
  have hQ_syn_sub : matInfNorm (fun v1 k2 => Q_syn v1 k2 - Q_syn_true v1 k2) ≤
      ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) + (18 / 100 : ℝ) * (K : ℝ)) *
        (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    apply matInfNorm_le _ (by positivity)
    intro v1 k2
    have hsyn_err := syntheticFFT_rounding_error_le K pChild c1 (t1Ell_mul_c1Ell K) U_pre v1
    have h1 : ‖Q_syn v1 k2 - syntheticFFT c1 U_pre v1 k2‖ ≤
        (18 / 100 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
      have h1a : ‖Q_syn v1 k2 - syntheticFFT c1 U_pre v1 k2‖ ≤
          (0.18 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * 1 := by
        have h1b := (norm_le_vecInfNorm (fun m => Q_syn v1 m - syntheticFFT c1 U_pre v1 m) k2).trans
          (hsyn_err.1.trans hsyn_err.2)
        linarith only [h1b]
      exact h1a.trans (by gcongr; norm_num)
    have h2 : ‖syntheticFFT c1 U_pre v1 k2 - Q_syn_true v1 k2‖ ≤
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ)) *
          (2 : ℝ) ^ (-(pChild : ℤ)) * M :=
      (norm_le_matInfNorm (fun i1 i2 => syntheticFFT c1 U_pre i1 i2 - Q_syn_true i1 i2) v1 k2).trans
        ((matInfNorm_syntheticFFT_sub_le ht1_pos c1 U_pre U_pre_true).trans hU_pre_sub)
    have htri := norm_sub_le_norm_sub_add_norm_sub (Q_syn v1 k2)
      (syntheticFFT c1 U_pre v1 k2) (Q_syn_true v1 k2)
    linarith only [htri, h1, h2]
  have hQ_syn_le : matInfNorm Q_syn ≤ (W + 2) * M := by
    have hcoeff : ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
        (18 / 100 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 2 := by
      have hlin : (W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) ≤ 2 * ((pChild : ℝ) + 1) := by
        linarith only [hW_le, hK_le]
      calc
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
            (18 / 100 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (2 * ((pChild : ℝ) + 1)) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right hlin (le_of_lt h2p_pos)
        _ = 2 * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        _ ≤ 2 * 1 := by linarith only [hpow_le]
        _ = 2 := by ring
    have herr_le : matInfNorm (fun v1 k2 => Q_syn v1 k2 - Q_syn_true v1 k2) ≤ 2 * M :=
      hQ_syn_sub.trans (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hM_pos))
    apply matInfNorm_le _ (by positivity)
    intro v1 k2
    have h1 := (norm_le_matInfNorm (fun i1 i2 => Q_syn i1 i2 - Q_syn_true i1 i2) v1 k2).trans herr_le
    have h2 := (norm_le_matInfNorm Q_syn_true v1 k2).trans hQ_syn_true_le
    have htri : ‖Q_syn v1 k2‖ ≤ ‖Q_syn v1 k2 - Q_syn_true v1 k2‖ + ‖Q_syn_true v1 k2‖ := by
      simpa using norm_add_le (Q_syn v1 k2 - Q_syn_true v1 k2) (Q_syn_true v1 k2)
    linarith only [htri, h1, h2]
  have hQ_post_sub : matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤
      (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    have h1 := matInfNorm_postTwistQuantRoots_sub_le qChild Q_syn Q_syn_true
    have h2 : 1 + matInfNorm Q_syn ≤ (W + 3) * M := by
      linarith only [hQ_syn_le, hM_ge_one]
    have h3 : (1 + matInfNorm Q_syn) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ))) ≤
        ((W + 3) * M) * ((18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) :=
      mul_le_mul h2 h2q_le (by positivity) (by positivity)
    have hsum :
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) + (W + 3) * (18 / 100 : ℝ)) ≤
        W + (18 / 100 : ℝ) * (K : ℝ) + 2 := by
      linarith only [hW_pos]
    have hprod_pos : 0 ≤ (2 : ℝ) ^ (-(pChild : ℤ)) * M := by positivity
    have h4 : matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) + (W + 3) * (18 / 100 : ℝ)) *
        ((2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
      linarith only [h1, h3, hQ_syn_sub]
    calc
      matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2)
        ≤ (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * ((2 : ℝ) ^ (-(pChild : ℤ)) * M) :=
          h4.trans (mul_le_mul_of_nonneg_right hsum hprod_pos)
      _ = (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by ring
  have hQ_post_le : ∀ v1 : Fin t1, max 1 (vecInfNorm (Q_post v1)) ≤ (W + 3) * M := by
    have hcoeff : (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 3 := by
      have hlin : W + (18 / 100 : ℝ) * (K : ℝ) + 2 ≤ 3 * ((pChild : ℝ) + 1) := by
        linarith only [hW_le, hK_le]
      calc
        (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (3 * ((pChild : ℝ) + 1)) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right hlin (le_of_lt h2p_pos)
        _ = 3 * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        _ ≤ 3 * 1 := by linarith only [hpow_le]
        _ = 3 := by ring
    have herr_le : matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤ 3 * M :=
      hQ_post_sub.trans (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hM_pos))
    have h1_le_WM : 1 ≤ (W + 3) * M := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (W + 3) * M := mul_le_mul (by linarith only [hW_pos]) hM_ge_one zero_le_one
            (by linarith only [hW_pos])
    intro v1
    apply max_le h1_le_WM
    apply vecInfNorm_le _ (by positivity)
    intro k2
    have h1 := (norm_le_matInfNorm (fun i1 i2 => Q_post i1 i2 - Q_post_true i1 i2) v1 k2).trans herr_le
    have h2 := (norm_le_matInfNorm Q_post_true v1 k2).trans hQ_post_true_le
    have htri : ‖Q_post v1 k2‖ ≤ ‖Q_post v1 k2 - Q_post_true v1 k2‖ + ‖Q_post_true v1 k2‖ := by
      simpa using norm_add_le (Q_post v1 k2 - Q_post_true v1 k2) (Q_post_true v1 k2)
    linarith only [htri, h1, h2]
  let v1 : Fin t1 := oddColKeyMinusInv t1 ht1_pos u2.val u1
  have hY_eq : Y_mat u1 u2 = Q_hat v1 u2 := rfl
  have hkey_eq : oddStrideIndex u2.val v1 = u1 := by
    rw [← oddColKeyMinus_eq_oddStrideIndex ht1_pos u2.val v1]
    exact oddColKeyMinus_oddColKeyMinusInv t1 ht1_pos ⟨k1Ell K, rfl⟩ u2.val u1
  have hduality : normDFT2D U_true u1 u2 = normDFT1D (Q_post_true v1) u2 := by
    rw [← hkey_eq]
    exact ((twisted_fourier_duality_reduction (t1Ell_mul_c1Ell K) U_true v1 u2).2).symm
  rw [hY_eq, hduality]
  have hchild_v1 : ‖Q_hat v1 u2 - normDFT1D (Q_post v1) u2‖ ≤ (W + 3) * E_child * M := by
    calc
      ‖Q_hat v1 u2 - normDFT1D (Q_post v1) u2‖
        ≤ vecInfNorm (fun m => Q_hat v1 m - normDFT1D (Q_post v1) m) :=
          norm_le_vecInfNorm (fun m => Q_hat v1 m - normDFT1D (Q_post v1) m) u2
      _ ≤ E_child * max 1 (vecInfNorm (Q_post v1)) := hchild (Q_post v1)
      _ ≤ E_child * ((W + 3) * M) :=
          mul_le_mul_of_nonneg_left (hQ_post_le v1) hE_pos
      _ = (W + 3) * E_child * M := by ring
  have hdft_diff : ‖normDFT1D (Q_post v1) u2 - normDFT1D (Q_post_true v1) u2‖ ≤
      (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    rw [← normDFT1D_sub]
    calc
      ‖normDFT1D (fun m => Q_post v1 m - Q_post_true v1 m) u2‖
        ≤ vecInfNorm (fun m => Q_post v1 m - Q_post_true v1 m) :=
          norm_normDFT1D_le _ u2
      _ ≤ matInfNorm (fun i1 i2 => Q_post i1 i2 - Q_post_true i1 i2) := by
          apply vecInfNorm_le _ (matInfNorm_nonneg _)
          intro m
          exact norm_le_matInfNorm (fun i1 i2 => Q_post i1 i2 - Q_post_true i1 i2) v1 m
      _ ≤ (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := hQ_post_sub
  have htri := norm_sub_le_norm_sub_add_norm_sub (Q_hat v1 u2)
    (normDFT1D (Q_post v1) u2) (normDFT1D (Q_post_true v1) u2)
  linarith only [htri, hchild_v1, hdft_diff]

/-- **Step 3 Deconvolution Error Bound for `fastDFTRecursive` (`norm_fastDFTRecursive_step3_col_sub_le`,
Section 5.1 (`sec:deconv-thm`) Theorem 5.1 (`thm:deconv`) and Section 6.3 (`sec:forward-error`)
Lemma 6.5(1) (`lem:forward`))**:
At any non-leaf level $(K, p)$ with $2 \le K$, $8 \le p$, and $4 p^2 < 2^K$, if `Y_mat` satisfies
the Step 2 bound against `normDFT2D U_true` with `0 ≤ E_child ≤ 2^(-pChild)`, then for every
`(u1, u2)` (both the Nyquist column $u_2 = r_\ell / 2$ via `nyquistColumnSolveQuant` and all
non-Nyquist columns $u_2 \ne r_\ell / 2$ via `cyclicBidiagPrevSolveQuant`), the Step 3 output
`Z_mat u1 u2` approximates `normDFT1D xCast (freqFin u1 u2)` within:
$$2.36 \, t_{1,\ell} \left((W_\ell + 4) E_{\text{child}} + (W_\ell + 0.54 K + 7) 2^{-p_{\text{child},\ell}} + 0.91 \cdot 2^{-p_{\text{work},\ell}}\right) \max(1, \|x\|_\infty).$$ -/
theorem norm_fastDFTRecursive_step3_col_sub_le {K p : ℕ} (hK : 2 ≤ K) (hp : 8 ≤ p)
    (hleaf : 4 * p * p < 2 ^ K) {E_child : ℝ} (hE_pos : 0 ≤ E_child)
    (hE_le : E_child ≤ (2 : ℝ) ^ (-(pChildEll K p : ℤ)))
    (x : Fin (2 ^ K) → ℂ) (Y_mat : Fin (t1Ell K) → Fin (rEll K) → ℂ)
    (hY : ∀ (u1 : Fin (t1Ell K)) (u2 : Fin (rEll K)),
      let t1 := t1Ell K
      let r := rEll K
      let m1 := m1Ell K p
      let alpha := alphaEll K p
      let pChild := pChildEll K p
      let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
      let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
      let U_true : Fin t1 → Fin r → ℂ :=
        spreadArray (rEll_pos K) m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))
      let W := (windowLengthEll K p : ℝ)
      let M := max 1 (vecInfNorm x)
      ‖Y_mat u1 u2 - normDFT2D U_true u1 u2‖ ≤
        (((W + 3) * E_child) +
          (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ))) * M) :
    letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
    let t1 := t1Ell K
    let r := rEll K
    let qChild := qChildEll K p
    let pChild := pChildEll K p
    let pWork := pWorkEll K p
    let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let Z_mat : Fin t1 → Fin r → ℂ :=
      fun u1 u2 =>
        if u2.val = r / 2 then
          nyquistColumnSolveQuant qChild (passbandC0 K p u2) (fun m => Y_mat m u2) (nyquistModeSum K x) u1
        else
          cyclicBidiagPrevSolveQuant qChild (passbandC0 K p u2) (passbandC1 K p u2) (fun m => Y_mat m u2) u1
    let W := (windowLengthEll K p : ℝ)
    let M := max 1 (vecInfNorm x)
    ∀ (u1 : Fin t1) (u2 : Fin r),
      ‖Z_mat u1 u2 - normDFT1D xCast (freqFin u1 u2)‖ ≤
        (236 / 100 : ℝ) * (t1 : ℝ) *
          ((((W + 4) * E_child) +
            (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
            (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)))) * M := by
  letI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
  intro t1 r qChild pChild pWork hR_eq xCast Z_mat W M u1 u2
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have ht1_ge_one : (1 : ℝ) ≤ (t1 : ℝ) := by
    have : 1 ≤ t1 := t1Ell_pos K
    exact_mod_cast this
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h2w_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pWork : ℤ)) := zpow_pos (by norm_num) _
  have h2q_eq : (2 : ℝ) ^ (-(qChild : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
    have hexp : -(qChild : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by
      change -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ)
      omega
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
    ring
  let m1 := m1Ell K p
  let alpha := alphaEll K p
  let U_true : Fin t1 → Fin r → ℂ :=
    spreadArray (rEll_pos K) m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))
  let Z_col : Fin t1 → ℂ := fun m => normDFT1D xCast (freqFin m u2)
  let c0 := passbandC0 K p u2
  let c1 := passbandC1 K p u2
  let B_true : Fin t1 → ℂ := fun m => (c0 : ℂ) * Z_col m + (c1 : ℂ) * Z_col (cyclicPrev m)
  let B_step2 : Fin t1 → ℂ := fun m => Y_mat m u2
  have hpoiss := normDFT2D_spreadArray_twoMode_sub_le hp x u2
  have hZ_col_le : vecInfNorm Z_col ≤ M := hpoiss.1
  have hB_true_le : vecInfNorm B_true ≤ M := hpoiss.2.1
  have hB_diff_le : vecInfNorm (fun m => B_step2 m - B_true m) ≤
      (((W + 3) * E_child) +
        (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
        (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) * M := by
    apply vecInfNorm_le _ (by positivity)
    intro m
    have h1 := hY m u2
    have h2 := hpoiss.2.2 m
    have htri := norm_sub_le_norm_sub_add_norm_sub (B_step2 m) (normDFT2D U_true m u2) (B_true m)
    linarith only [htri, h1, h2]
  clear hY hpoiss
  have hamp_le_M :
      (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) ≤ M := by
    have hbudget := level_error_budget_le (by omega : 1 ≤ K) (by omega : 1 ≤ p) hleaf
    have hp_le_one : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hsqrt_pos : (0 : ℝ) ≤ (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) := by positivity
    have hW_pos : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have hE_child_term : (W + 3) * E_child ≤ (W + 4) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
      calc
        (W + 3) * E_child ≤ (W + 4) * E_child := by linarith only [hE_pos]
        _ ≤ (W + 4) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
          mul_le_mul_of_nonneg_left hE_le (by positivity)
    have hinner_le :
        (((W + 3) * E_child) +
          (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
          (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤
        (((W + 4) * (2 : ℝ) ^ (-(pChild : ℤ))) +
          (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
          (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) := by
      have hmid : (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
          (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hK_nn]) (le_of_lt h2p_pos)
      linarith only [hE_child_term, hmid, h2w_pos]
    have hprod_le_one :
        (236 / 100 : ℝ) * (t1 : ℝ) *
          (((W + 3) * E_child) +
            (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
            (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤ 1 := by
      have h1 :
          (236 / 100 : ℝ) * (t1 : ℝ) *
            (((W + 3) * E_child) +
              (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤
          (236 / 100 : ℝ) * (t1 : ℝ) *
            (((W + 4) * (2 : ℝ) ^ (-(pChild : ℤ))) +
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) :=
        mul_le_mul_of_nonneg_left hinner_le (by positivity)
      linarith only [h1, hbudget, hp_le_one, hsqrt_pos]
    have hamp1 := mul_le_mul_of_nonneg_left hB_diff_le (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
    have hamp2 := mul_le_mul_of_nonneg_right hprod_le_one (le_of_lt hM_pos)
    linarith only [hamp1, hamp2]
  have hB_diff_le_M : vecInfNorm (fun m => B_step2 m - B_true m) ≤ M := by
    have hnn : 0 ≤ vecInfNorm (fun m => B_step2 m - B_true m) := vecInfNorm_nonneg _
    have h1 : 1 * vecInfNorm (fun m => B_step2 m - B_true m) ≤
        ((236 / 100 : ℝ) * (t1 : ℝ)) * vecInfNorm (fun m => B_step2 m - B_true m) :=
      mul_le_mul_of_nonneg_right (by linarith only [ht1_ge_one]) hnn
    linarith only [h1, hamp_le_M]
  have hB_step2_le : vecInfNorm B_step2 ≤ 2 * M := by
    apply vecInfNorm_le _ (by positivity)
    intro m
    have h1 := (norm_le_vecInfNorm (fun k => B_step2 k - B_true k) m).trans hB_diff_le_M
    have h2 := (norm_le_vecInfNorm B_true m).trans hB_true_le
    have htri : ‖B_step2 m‖ ≤ ‖B_step2 m - B_true m‖ + ‖B_true m‖ := by
      simpa using norm_add_le (B_step2 m - B_true m) (B_true m)
    linarith only [htri, h1, h2]
  have hquant_bound :
      (2 : ℝ) ^ (-(qChild : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (3 * M) ≤
      (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
    rw [h2q_eq]
    have h1 : 1 ≤ (236 / 100 : ℝ) * (t1 : ℝ) * M := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((236 / 100 : ℝ) * (t1 : ℝ)) * M :=
          mul_le_mul (by linarith only [ht1_ge_one]) hM_ge_one zero_le_one
            (by linarith only [ht1_ge_one])
        _ = (236 / 100 : ℝ) * (t1 : ℝ) * M := by ring
    have h2 : (1 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
        ((236 / 100 : ℝ) * (t1 : ℝ) * M) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt h2p_pos)
    have hlhs : (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
        2 * ((236 / 100 : ℝ) * (t1 : ℝ) * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)))) * (3 * M) =
        (1 / 4 : ℝ) * (1 * (2 : ℝ) ^ (-(pChild : ℤ))) +
          (3 / 2 : ℝ) * (((236 / 100 : ℝ) * (t1 : ℝ) * M) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
    have hrhs : (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) =
        2 * (((236 / 100 : ℝ) * (t1 : ℝ) * M) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
    rw [hlhs, hrhs]
    linarith only [h2, h2p_pos]
  dsimp only [Z_mat]
  split_ifs with hu2
  · -- Nyquist column u2.val = r / 2
    have hc1_eq : c1 = c0 := passbandC1_eq_passbandC0_of_nyquist hK p u2 hu2
    have hmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1 := passbandC0_passbandC1_max_ge hp u2
    rw [hc1_eq, max_self] at hmax
    have hc0_ne : c0 ≠ 0 := by linarith only [hmax]
    have halt : (∑ m : Fin t1, (-1 : ℂ) ^ m.val * Z_col m) = nyquistModeSum K x :=
      sum_alternating_normDFT1D_freqFin_eq_nyquistModeSum hK x u2 hu2
    have hrec : ∀ m : Fin t1, (c0 : ℂ) * Z_col m + (c0 : ℂ) * Z_col (cyclicPrev m) = B_true m := by
      intro m
      dsimp [B_true]
      rw [hc1_eq]
    have hZ_spec : Z_col u1 = nyquistColumnSolve c0 B_true (nyquistModeSum K x) u1 :=
      nyquistColumnSolve_spec hc0_ne B_true Z_col (nyquistModeSum K x) hrec halt u1
    have hexact_diff :
        ‖nyquistColumnSolve c0 B_step2 (nyquistModeSum K x) u1 - Z_col u1‖ ≤
          (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) := by
      rw [hZ_spec, nyquistColumnSolve_sub_same_alt]
      have hcond := passbandC0_nyquist_conditioning_le_236_t1 hK hp u2 hu2
        (fun m => B_step2 m - B_true m) 0
      simp only [norm_zero, zero_div, add_zero] at hcond
      exact (norm_le_vecInfNorm _ u1).trans hcond
    have hquant_diff :
        ‖nyquistColumnSolveQuant qChild c0 B_step2 (nyquistModeSum K x) u1 -
          nyquistColumnSolve c0 B_step2 (nyquistModeSum K x) u1‖ ≤
          (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
      have hq := (norm_le_vecInfNorm _ u1).trans
        (vecInfNorm_nyquistColumnSolveQuant_sub_le_of_bounds hmax
          (qChildEll_step3_precision_le_quarter K p) B_step2 (nyquistModeSum K x))
      have h1B : 1 + vecInfNorm B_step2 ≤ 3 * M := by linarith only [hB_step2_le, hM_ge_one]
      have hmul :
          2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (1 + vecInfNorm B_step2) ≤
          2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (3 * M) :=
        mul_le_mul_of_nonneg_left h1B (by positivity)
      linarith only [hq, hmul, hquant_bound]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (nyquistColumnSolveQuant qChild c0 B_step2 (nyquistModeSum K x) u1)
      (nyquistColumnSolve c0 B_step2 (nyquistModeSum K x) u1)
      (Z_col u1)
    have hamp_diff := mul_le_mul_of_nonneg_left hB_diff_le
      (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
    have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have hcoeff_le :
        (((W + 3) * E_child) +
          (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
          (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤
        (((W + 4) * E_child) +
          (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
          (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) := by
      have hmid : (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
          (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hK_nn]) (le_of_lt h2p_pos)
      linarith only [hE_pos, hmid, h2w_pos]
    have hcoeff_mul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcoeff_le (le_of_lt hM_pos))
      (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
    linarith only [htri, hquant_diff, hexact_diff, hamp_diff, hcoeff_mul]
  · -- Non-Nyquist column u2.val ≠ r / 2
    have hexact_vec :
        vecInfNorm (fun m => cyclicBidiagPrevSolve c0 c1 B_step2 m - Z_col m) ≤
          (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) := by
      rw [passbandC0_passbandC1_prevSolve_sub_eq hK hp u2 hu2 B_step2 Z_col B_true (fun _ => rfl)]
      exact passbandC0_passbandC1_prev_conditioning_le_236_t1 hK hp u2 hu2
        (fun m => B_step2 m - B_true m)
    have hexact_diff :
        ‖cyclicBidiagPrevSolve c0 c1 B_step2 u1 - Z_col u1‖ ≤
          (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) :=
      (norm_le_vecInfNorm _ u1).trans hexact_vec
    have hsolve_le : vecInfNorm (cyclicBidiagPrevSolve c0 c1 B_step2) ≤ 2 * M := by
      apply vecInfNorm_le _ (by positivity)
      intro m
      have h1 := (norm_le_vecInfNorm (fun k => cyclicBidiagPrevSolve c0 c1 B_step2 k - Z_col k) m).trans
        (hexact_vec.trans hamp_le_M)
      have h2 := (norm_le_vecInfNorm Z_col m).trans hZ_col_le
      have htri : ‖cyclicBidiagPrevSolve c0 c1 B_step2 m‖ ≤
          ‖cyclicBidiagPrevSolve c0 c1 B_step2 m - Z_col m‖ + ‖Z_col m‖ := by
        simpa using norm_add_le (cyclicBidiagPrevSolve c0 c1 B_step2 m - Z_col m) (Z_col m)
      linarith only [htri, h1, h2]
    have hquant_diff :
        ‖cyclicBidiagPrevSolveQuant qChild c0 c1 B_step2 u1 -
          cyclicBidiagPrevSolve c0 c1 B_step2 u1‖ ≤
          (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
      have hq := (norm_le_vecInfNorm _ u1).trans
        (passbandC0_passbandC1_prevSolveQuant_sub_le hK hp u2 hu2 B_step2)
      have h1S : 1 + vecInfNorm (cyclicBidiagPrevSolve c0 c1 B_step2) ≤ 3 * M := by
        linarith only [hsolve_le, hM_ge_one]
      have hmul :
          2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) *
            (1 + vecInfNorm (cyclicBidiagPrevSolve c0 c1 B_step2)) ≤
          2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (3 * M) :=
        mul_le_mul_of_nonneg_left h1S (by positivity)
      linarith only [hq, hmul, hquant_bound]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (cyclicBidiagPrevSolveQuant qChild c0 c1 B_step2 u1)
      (cyclicBidiagPrevSolve c0 c1 B_step2 u1)
      (Z_col u1)
    have hamp_diff := mul_le_mul_of_nonneg_left hB_diff_le
      (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
    have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have hcoeff_le :
        (((W + 3) * E_child) +
          (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
          (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤
        (((W + 4) * E_child) +
          (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
          (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) := by
      have hmid : (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
          (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hK_nn]) (le_of_lt h2p_pos)
      linarith only [hE_pos, hmid, h2w_pos]
    have hcoeff_mul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcoeff_le (le_of_lt hM_pos))
      (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
    linarith only [htri, hquant_diff, hexact_diff, hamp_diff, hcoeff_mul]

/-- **Single-Level Recursive Error Propagation for `fastDFTRecursive`
(`vecInfNorm_fastDFTRecursive_step_le`, Lemma 6.5(1)–(2) (`lem:forward`),
Section 6.3 (`sec:forward-error`) and Section 7.1 (`sec:alg-spec`))**:
At any non-leaf level $(K, p)$ (`isBaseLeaf K p = false`, $2 \le K$, $8 \le p$), if the child
recursive call `fastDFTRecursive (k2Ell K) (pChildEll K p)` satisfies error bound `E_child`
with `0 ≤ E_child ≤ 2^(-pChildEll K p)`, then `fastDFTRecursive K p x` satisfies the 4-source
recurrence error bound against `normDFT1D x`. -/
theorem vecInfNorm_fastDFTRecursive_step_le {K p : ℕ}
    (hleaf_bool : isBaseLeaf K p = false) (hK : 2 ≤ K) (hp : 8 ≤ p)
    {E_child : ℝ} (hE_pos : 0 ≤ E_child)
    (hE_le : E_child ≤ (2 : ℝ) ^ (-(pChildEll K p : ℤ)))
    (hchild : ∀ y : Fin (rEll K) → ℂ,
      vecInfNorm (fun u2 =>
        (fastDFTRecursive (k2Ell K) (pChildEll K p) y u2).toComplex - normDFT1D y u2) ≤
        E_child * max 1 (vecInfNorm y))
    (x : Fin (2 ^ K) → ℂ) :
    vecInfNorm (fun u => (fastDFTRecursive K p x u).toComplex - normDFT1D x u) ≤
      ((236 / 100 : ℝ) * (t1Ell K : ℝ) *
        ((((windowLengthEll K p : ℝ) + 4) * E_child) +
          ((windowLengthEll K p : ℝ) + (54 / 100 : ℝ) * (K : ℝ) + 7) *
            (2 : ℝ) ^ (-(pChildEll K p : ℤ)) +
          (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ))) +
        (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ))) * max 1 (vecInfNorm x) := by
  have hleaf : 4 * p * p < 2 ^ K := by
    have h := hleaf_bool
    unfold isBaseLeaf at h
    rw [decide_eq_false_iff_not, not_le] at h
    exact h
  have hcond : (!isBaseLeaf K p) = true ∧ 2 ≤ K := by
    simp [hleaf_bool, hK]
  let t1 := t1Ell K
  let r := rEll K
  let c1 := c1Ell K
  let qChild := qChildEll K p
  let pChild := pChildEll K p
  let pWork := pWorkEll K p
  let m1 := m1Ell K p
  let alpha := alphaEll K p
  let B_in := levelBIn K x
  let B_slot := kroneckerSlotBitsRaw qChild B_in m1 (foldedHalfWidth m1 r)
  have hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
  have ht1_pos : 0 < t1 := t1Ell_pos K
  have hr_pos : 0 < r := rEll_pos K
  haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
  have hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
  let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
  let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
    oddStrideGather t1 r hR_pos (fun j => quantizeComplexFixed qChild (x j))
  let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
    kroneckerMatrixSpreadFixed t1 r m1 B_slot qChild qChild hr_pos U_gathered (levelFilterTapFixed K p)
  let U_spread : Fin t1 → Fin r → ℂ := fun j1 k2 => (U_spreadFixed j1 k2).toComplex
  let U_pre : Fin t1 → Fin r → ℂ := preTwistQuantRoots qChild U_spread
  let Q_syn : Fin t1 → Fin r → ℂ := radix2SyntheticFFTQuant qChild (k1Ell K) c1 U_pre
  let Q_post : Fin t1 → Fin r → ℂ := postTwistQuantRoots qChild Q_syn
  let Q_hat : Fin t1 → Fin r → ℂ :=
    fun v1 u2 => (fastDFTRecursive (k2Ell K) pChild (Q_post v1) u2).toComplex
  let Y_mat : Fin t1 → Fin r → ℂ := oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hat
  let Z_mat : Fin t1 → Fin r → ℂ :=
    fun u1 u2 =>
      if u2.val = r / 2 then
        nyquistColumnSolveQuant qChild (passbandC0 K p u2) (fun m => Y_mat m u2) (nyquistModeSum K x) u1
      else
        cyclicBidiagPrevSolveQuant qChild (passbandC0 K p u2) (passbandC1 K p u2) (fun m => Y_mat m u2) u1
  let W := (windowLengthEll K p : ℝ)
  let M := max 1 (vecInfNorm x)
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have h2c_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h2w_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pWork : ℤ)) := zpow_pos (by norm_num) _
  have hstep2 := norm_fastDFTRecursive_step2_sub_le hp hE_pos x hchild
  have hstep3 := norm_fastDFTRecursive_step3_col_sub_le hK hp hleaf hE_pos hE_le x Y_mat hstep2
  clear hstep2
  apply vecInfNorm_le _ (by positivity)
  intro u
  have hunfold : (fastDFTRecursive K p x u).toComplex =
      quantizeComplex (p + 2) (freqScatter t1 r hR_eq Z_mat u) := by
    rw [fastDFTRecursive, if_pos hcond]
    rfl
  rw [hunfold]
  let u1 : Fin t1 := ⟨u.val / r, by rw [Nat.div_lt_iff_lt_mul hr_pos]; simpa [hR_eq] using u.isLt⟩
  let u2 : Fin r := ⟨u.val % r, Nat.mod_lt u.val hr_pos⟩
  have hfreq_eq : freqScatter t1 r hR_eq Z_mat u = Z_mat u1 u2 := by
    unfold freqScatter
    rfl
  have hu_cast : Fin.cast hR_eq.symm (freqFin u1 u2) = u := by
    ext
    simp only [Fin.val_cast, freqFin, u1, u2]
    exact Nat.mod_add_div u.val r
  have hdft_eq : normDFT1D x u = normDFT1D xCast (freqFin u1 u2) := by
    rw [normDFT1D_comp_cast hR_eq x (freqFin u1 u2), hu_cast]
  rw [hfreq_eq, hdft_eq]
  have hq_out : ‖quantizeComplex (p + 2) (Z_mat u1 u2) - Z_mat u1 u2‖ ≤
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have h := norm_quantizeComplex_sub_self_le (p + 2) (Z_mat u1 u2)
    have hexp : -((p + 2 : ℕ) : ℤ) = -(p : ℤ) + (-2 : ℤ) := by push_cast; ring
    have hpow : (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
      rw [hexp, zpow_add₀ (by norm_num)]
      norm_num
      ring
    rw [hpow] at h
    have hprod_pos : 0 ≤ Real.sqrt 2 * (2 : ℝ) ^ (-(p : ℤ)) := by positivity
    have h1 : ‖quantizeComplex (p + 2) (Z_mat u1 u2) - Z_mat u1 u2‖ ≤
        (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) * 1 := by
      calc ‖quantizeComplex (p + 2) (Z_mat u1 u2) - Z_mat u1 u2‖
        ≤ (Real.sqrt 2 / 2) * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) := h
        _ = (1 / 8 : ℝ) * (Real.sqrt 2 * (2 : ℝ) ^ (-(p : ℤ))) := by ring
        _ ≤ (1 / 4 : ℝ) * (Real.sqrt 2 * (2 : ℝ) ^ (-(p : ℤ))) :=
          mul_le_mul_of_nonneg_right (by norm_num) hprod_pos
        _ = (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) * 1 := by ring
    exact h1.trans (by gcongr)
  have hZ_diff := hstep3 u1 u2
  clear hstep3
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (quantizeComplex (p + 2) (Z_mat u1 u2)) (Z_mat u1 u2) (normDFT1D xCast (freqFin u1 u2))
  linarith only [htri, hq_out, hZ_diff]

/-- **Multi-Level Inductive Error Schedule Bound for `cSpec n` (`multiLevel_concreteError_le`,
Lemma 6.5(2) (`lem:forward`), Section 6.3 (`sec:forward-error`) and Section 7.2 (`sec:cost-proof`))**:
For every input size $n$ and every recursion level $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$,
the concrete multi-level error schedule `concreteLevelError (rootK0 n) (rootP0 n)` satisfies
`concreteLevelError (rootK0 n) (rootP0 n) ell ≤ 2 ^ (-levelP (rootK0 n) (rootP0 n) ell)`. -/
theorem multiLevel_concreteError_le (n ell : ℕ)
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n)) :
    concreteLevelError (rootK0 n) (rootP0 n) ell ≤
      (2 : ℝ) ^ (-(levelP (rootK0 n) (rootP0 n) ell : ℤ)) := by
  have hK0 : 1 ≤ rootK0 n := by
    have := rootK0_ge_two n
    omega
  have hp0 : 1 ≤ rootP0 n := by
    have := rootP0_ge_eighteen n
    omega
  exact inductive_accuracy_closure (rootK0 n) (rootP0 n) hK0 hp0 ell hell

/-- **Root-Level Inductive Error Schedule Bound (`root_concreteError_le`,
Lemma 6.5(2) (`lem:forward`) and Theorem 1 (`thm:main`))**:
At the root transform ($\ell = 0$), the concrete error schedule `concreteLevelError (rootK0 n) (rootP0 n) 0`
satisfies `concreteLevelError (rootK0 n) (rootP0 n) 0 ≤ 2 ^ (-rootP0 n)` for every $n \in \mathbb{N}$. -/
theorem root_concreteError_le (n : ℕ) :
    concreteLevelError (rootK0 n) (rootP0 n) 0 ≤ (2 : ℝ) ^ (-(rootP0 n : ℤ)) :=
  multiLevel_concreteError_le n 0 (Nat.zero_le _)

/-- **Unconditional Multi-Level `fastDFTRecursive` Accuracy Theorem
(`vecInfNorm_fastDFTRecursive_sub_normDFT1D_le`, Lemma 6.5(2) (`lem:forward`),
Section 6.3 (`sec:forward-error`) and Section 7.1 (`sec:alg-spec`))**:
For every input size $n \in \mathbb{N}$, every recursion level
$\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$, and every input vector
$x : \text{Fin}(2^{K_\ell}) \to \mathbb{C}$, the concrete multi-level recursive operator
`fastDFTRecursive (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) x` satisfies:
$$\|\text{fastDFTRecursive } K_\ell \, p_\ell \, x - F_{2^{K_\ell}} x\|_\infty \le \text{concreteLevelError } K_0 \, p_0 \, \ell \cdot \max(1, \|x\|_\infty).$$ -/
theorem vecInfNorm_fastDFTRecursive_sub_normDFT1D_le (n ell : ℕ)
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n))
    (x : Fin (2 ^ levelK (rootK0 n) ell) → ℂ) :
    vecInfNorm (fun u =>
      (fastDFTRecursive (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) x u).toComplex -
        normDFT1D x u) ≤
      concreteLevelError (rootK0 n) (rootP0 n) ell * max 1 (vecInfNorm x) := by
  let K0 := rootK0 n
  let p0 := rootP0 n
  let L := recursionDepth K0 p0
  have hp0_ge18 : 18 ≤ p0 := rootP0_ge_eighteen n
  have hp0_ge1 : 1 ≤ p0 := by omega
  have hmain : ∀ (d : ℕ) (hd : d ≤ L) (y : Fin (2 ^ levelK K0 (L - d)) → ℂ),
      vecInfNorm (fun u =>
        (fastDFTRecursive (levelK K0 (L - d)) (levelP K0 p0 (L - d)) y u).toComplex -
          normDFT1D y u) ≤
        concreteLevelError K0 p0 (L - d) * max 1 (vecInfNorm y) := by
    intro d
    induction d with
    | zero =>
      intro _ y
      simp only [Nat.sub_zero]
      have hleaf : isBaseLeaf (levelK K0 L) (levelP K0 p0 L) = true :=
        isBaseLeaf_recursionDepth K0 p0 hp0_ge1
      have hfun : (fun u => (fastDFTRecursive (levelK K0 L) (levelP K0 p0 L) y u).toComplex - normDFT1D y u) =
          (fun u => baseRadix2FFTQuant (levelK K0 L) (levelP K0 p0 L) y u - normDFT1D y u) := by
        funext u
        rw [fastDFTRecursive_of_isBaseLeaf hleaf y, toComplex_quantizeComplexFixed_baseRadix2FFTQuant]
      rw [hfun]
      have hbase := vecInfNorm_baseRadix2FFTQuant_sub_normDFT1D_le (levelK K0 L) (levelP K0 p0 L) y
      have herr_eq := concreteLevelError_of_ge (K0 := K0) (p0 := p0) (ell := L) (le_refl L)
      have hextra_nn : 0 ≤ ((2 ^ levelK K0 L : ℕ) : ℝ) * Real.sqrt 2 *
          (2 : ℝ) ^ (-(qBaseEll (levelK K0 L) (levelP K0 p0 L) : ℤ)) := by positivity
      have hM_nn : 0 ≤ max 1 (vecInfNorm y) := le_trans zero_le_one (le_max_left 1 _)
      have hle : (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(levelP K0 p0 L : ℤ)) ≤
          concreteLevelError K0 p0 L := by linarith
      exact hbase.trans (mul_le_mul_of_nonneg_right hle hM_nn)
    | succ d ih =>
      intro hd y
      let cur := L - (d + 1)
      have hcur_lt : cur < L := by omega
      have hcur_succ : cur + 1 = L - d := by omega
      have hleaf_false : isBaseLeaf (levelK K0 cur) (levelP K0 p0 cur) = false :=
        not_isBaseLeaf_of_lt_recursionDepth K0 p0 cur hcur_lt
      have hK_cur : 2 ≤ levelK K0 cur :=
        two_le_levelK_of_lt_recursionDepth hp0_ge1 hcur_lt
      have hp_cur : 8 ≤ levelP K0 p0 cur := by
        have := levelP_ge_p0 K0 p0 cur
        omega
      have hE_pos : 0 ≤ concreteLevelError K0 p0 (cur + 1) :=
        le_of_lt (concreteLevelError_pos K0 p0 (cur + 1))
      have hE_le : concreteLevelError K0 p0 (cur + 1) ≤
          (2 : ℝ) ^ (-(pChildEll (levelK K0 cur) (levelP K0 p0 cur) : ℤ)) :=
        multiLevel_concreteError_le n (cur + 1) (by change cur + 1 ≤ L; omega)
      have hchild : ∀ w : Fin (rEll (levelK K0 cur)) → ℂ,
          vecInfNorm (fun u2 =>
            (fastDFTRecursive (k2Ell (levelK K0 cur))
              (pChildEll (levelK K0 cur) (levelP K0 p0 cur)) w u2).toComplex - normDFT1D w u2) ≤
            concreteLevelError K0 p0 (cur + 1) * max 1 (vecInfNorm w) := by
        intro w
        have ih' := ih (by omega)
        rw [← hcur_succ] at ih'
        exact ih' w
      have hstep := vecInfNorm_fastDFTRecursive_step_le hleaf_false hK_cur hp_cur
        hE_pos hE_le hchild y
      rw [← concreteLevelError_of_lt hcur_lt] at hstep
      exact hstep
  have hsub := hmain (L - ell) (Nat.sub_le L ell)
  have heq : L - (L - ell) = ell := by
    change recursionDepth (rootK0 n) (rootP0 n) -
      (recursionDepth (rootK0 n) (rootP0 n) - ell) = ell
    omega
  rw [heq] at hsub
  exact hsub x

/-- **Unconditional Multi-Level `fastDFTRecursive` $2^{-p_\ell}$ Accuracy Bound
(`vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_two_zpow`, Lemma 6.5(2) (`lem:forward`),
equation (36) (`eq:inductive-bound`), Section 6.3 (`sec:forward-error`))**:
For every input size $n \in \mathbb{N}$, every recursion level
$\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$, and every input vector
$x : \text{Fin}(2^{K_\ell}) \to \mathbb{C}$, `fastDFTRecursive` approximates `normDFT1D x` within
$2^{-p_\ell} \max(1, \|x\|_\infty)$ unconditionally. -/
theorem vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_two_zpow (n ell : ℕ)
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n))
    (x : Fin (2 ^ levelK (rootK0 n) ell) → ℂ) :
    vecInfNorm (fun u =>
      (fastDFTRecursive (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) x u).toComplex -
        normDFT1D x u) ≤
      (2 : ℝ) ^ (-(levelP (rootK0 n) (rootP0 n) ell : ℤ)) * max 1 (vecInfNorm x) := by
  have hM_nn : 0 ≤ max 1 (vecInfNorm x) := le_trans zero_le_one (le_max_left 1 _)
  exact (vecInfNorm_fastDFTRecursive_sub_normDFT1D_le n ell hell x).trans
    (mul_le_mul_of_nonneg_right (multiLevel_concreteError_le n ell hell) hM_nn)

/-- **Conditional Multi-Level `fastDFTRecursive` Accuracy Closure
(`vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_of_levelError`, Lemma 6.5(2) (`lem:forward`))**:
At any recursion level $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$, if the concrete
operator `fastDFTRecursive` at level $\ell$ satisfies the concrete error schedule bound
`concreteLevelError (rootK0 n) (rootP0 n) ell * vecInfNorm x`, then its $\ell_\infty$ error
against `normDFT1D x` is bounded by `2 ^ (-levelP (rootK0 n) (rootP0 n) ell) * vecInfNorm x`. -/
theorem vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_of_levelError (n ell : ℕ)
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n))
    (x : Fin (2 ^ levelK (rootK0 n) ell) → ℂ)
    (happrox :
      vecInfNorm (fun u =>
        (fastDFTRecursive (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) x u).toComplex -
          normDFT1D x u) ≤
        concreteLevelError (rootK0 n) (rootP0 n) ell * vecInfNorm x) :
    vecInfNorm (fun u =>
      (fastDFTRecursive (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) x u).toComplex -
        normDFT1D x u) ≤
      (2 : ℝ) ^ (-(levelP (rootK0 n) (rootP0 n) ell : ℤ)) * vecInfNorm x := by
  exact le_trans happrox
    (mul_le_mul_of_nonneg_right (multiLevel_concreteError_le n ell hell) (vecInfNorm_nonneg x))

/-- **Root Convolution Error Budget Identity (`root_conv_error_budget_eq_one_eighth`,
Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`), Part 1)**:
Under the root precision $p_0 = 2b + 2K_0 + 6$, the worst-case 2-call root convolution
error budget $8 R_0 \cdot 2^{-p_0} \cdot 2^{2b + K_0}$ equals $1/8 < 1/2$ unconditionally. -/
theorem root_conv_error_budget_eq_one_eighth (n : ℕ) :
    8 * (rootR0 n : ℝ) * (2 : ℝ) ^ (-(rootP0 n : ℤ)) *
        (2 : ℝ) ^ (2 * chunkBits n + rootK0 n) = (1 / 8 : ℝ) ∧
      (1 / 8 : ℝ) < 1 / 2 :=
  root_conv_error_budget_lt_half n

/-- **Conditional Root Convolution Exact Integer Recovery (`root_conv_recovery_of_fastDFT_approx`,
Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`), Part 1)**:
Given any normalized 2-call root convolution approximation `cHat` to
`linearConvCoeff (chunkBits n) (numChunks n) A B k / rootR0 n` within the root error bound
`8 * 2 ^ (-rootP0 n) * 2 ^ (2 * chunkBits n + rootK0 n)`, nearest-integer rounding
`⌊rootR0 n * cHat + 1 / 2⌋` recovers `linearConvCoeff (chunkBits n) (numChunks n) A B k`
with zero bit error. -/
theorem root_conv_recovery_of_fastDFT_approx (n A B k : ℕ) (cHat : ℝ)
    (herr : |cHat - (linearConvCoeff (chunkBits n) (numChunks n) A B k : ℝ) / (rootR0 n : ℝ)| ≤
      8 * (2 : ℝ) ^ (-(rootP0 n : ℤ)) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n)) :
    |(rootR0 n : ℝ) * cHat - (linearConvCoeff (chunkBits n) (numChunks n) A B k : ℝ)| ≤
        (1 / 8 : ℝ) ∧
      ⌊(rootR0 n : ℝ) * cHat + (1 / 2 : ℝ)⌋ =
        (linearConvCoeff (chunkBits n) (numChunks n) A B k : ℤ) := by
  have h := root_conv_rounding_exact_of_approx n
    (linearConvCoeff (chunkBits n) (numChunks n) A B k) cHat herr
  exact ⟨h.1, h.2.2⟩

/-! ### 2.4 Stage 4: 2-Call Complex-Packed DFT Convolution & Exact Equivalence to `reconstructProductFromChunks` (Section 3.5 (`sec:prelim-dft`) Lemma 3.4 (`lem:two-call`), Section 7.1 (`sec:alg-spec`), and Section 7.2 (`sec:cost-proof`) Theorem 1 (`thm:main`)) -/

/-- Concrete 2-call complex-packed `fastDFTRecursive` cyclic convolution of the unpacked base-$2^b$
chunk vectors $a_j = \text{natChunk } (\text{chunkBits } n) \, A \, j \cdot 2^{-b}$ and
$b_j = \text{natChunk } (\text{chunkBits } n) \, B \, j \cdot 2^{-b}$ on `Fin (rootR0 n)` via
**pointwise complex squaring** `(Z u * Z u) / (2 * Complex.I)` (Lemma 3.4 (`lem:two-call`),
equation (10) (`eq:two-call`), and Section 7.1 (`sec:alg-spec`) Listing 1 (`lst:multiply`)):
- Call 1: Computes the forward quantized DFT `Z = fastDFTRecursive (rootK0 n) (rootP0 n) (packRealComplex aVec bVec)`
  of the unit-normalized chunk vectors.
- Pointwise Squaring: Forms `W_conj u = starRingEnd ℂ (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))`
  using a single local complex squaring at each frequency `u` (requiring zero cross-tape reversal pass
  to pair `u` with `(-u) mod R0`).
- Call 2: Computes the inverse DFT via conjugation and a second call to
  `fastDFTRecursive (rootK0 n) (rootP0 n)` on `W_conj`, and rescales by $2^{2b} R_0^2$. -/
noncomputable def fastTwoCallDFTConv (n A B : ℕ) (k : Fin (rootR0 n)) : ℂ :=
  let K0 := rootK0 n
  let p0 := rootP0 n
  let R0 := rootR0 n
  let b := chunkBits n
  let aVec : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let bVec : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let zVec : Fin R0 → ℂ := packRealComplex aVec bVec
  let Z : Fin R0 → ℂ := fun u => (fastDFTRecursive K0 p0 zVec u).toComplex
  let W_conj : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
  let C_inv : Fin R0 → ℂ := fun m => starRingEnd ℂ ((fastDFTRecursive K0 p0 W_conj m).toComplex)
  ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) * C_inv k))

/-- Reconstruct the integer product from `fastTwoCallDFTConv n A B k` via nearest-integer rounding
`⌊... + 1/2⌋.toNat` and base-$2^b$ carry-propagation evaluation (Section 7.1 (`sec:alg-spec`) and
Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`), Part 1). -/
noncomputable def reconstructProductViaFastDFT (n A B : ℕ) : ℕ :=
  ∑ k : Fin (rootR0 n),
    ⌊(fastTwoCallDFTConv n A B k).re + (1 / 2 : ℝ)⌋.toNat * 2 ^ (k.val * chunkBits n)

/-- Concrete 2-call complex-packed exact DFT cyclic convolution of the unpacked base-$2^b$ chunk vectors
$a_j = \text{natChunk } (\text{chunkBits } n) \, A \, j$ and
$b_j = \text{natChunk } (\text{chunkBits } n) \, B \, j$ on `Fin (rootR0 n)` via pointwise complex
squaring `(Z u * Z u) / (2 * Complex.I)` (Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`),
equation (10) (`eq:two-call`), and Section 7.1 (`sec:alg-spec`)):
- Call 1: Computes the single complex forward DFT `Z = normDFT1D (packRealComplex aVec bVec)`.
- Call 2: Computes the inverse DFT sum of `(Z u * Z u) / (2 * Complex.I)`. -/
noncomputable def twoCallDFTConv (n A B : ℕ) (k : Fin (rootR0 n)) : ℂ :=
  let R0 := rootR0 n
  let b := chunkBits n
  let aVec : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ)
  let bVec : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ)
  let zVec : Fin R0 → ℂ := packRealComplex aVec bVec
  let Z : Fin R0 → ℂ := normDFT1D zVec
  (R0 : ℂ) * ∑ u : Fin R0,
    ((Z u * Z u) / (2 * Complex.I)) * expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R0 : ℝ))

/-- Pointwise complex squaring identity divided by $2i$ (Section 3.5 (`sec:prelim-dft`),
Lemma 3.4 (`lem:two-call`), equation (10) (`eq:two-call`)):
$$\frac{(F_R(a + ib))_u^2}{2i} = (F_R a)_u (F_R b)_u - \frac{i}{2}\left((F_R a)_u^2 - (F_R b)_u^2\right).$$ -/
private theorem normDFT1D_packRealComplex_sq_div_two_I {R : ℕ} (a b : Fin R → ℝ) (u : Fin R) :
    (normDFT1D (packRealComplex a b) u * normDFT1D (packRealComplex a b) u) / (2 * Complex.I) =
      normDFT1D (fun j => (a j : ℂ)) u * normDFT1D (fun j => (b j : ℂ)) u -
        (Complex.I / 2) *
          (normDFT1D (fun j => (a j : ℂ)) u * normDFT1D (fun j => (a j : ℂ)) u -
           normDFT1D (fun j => (b j : ℂ)) u * normDFT1D (fun j => (b j : ℂ)) u) := by
  have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  apply mul_right_cancel₀ hI
  rw [div_mul_cancel₀ _ hI]
  calc
    normDFT1D (packRealComplex a b) u * normDFT1D (packRealComplex a b) u
      = (normDFT1D (packRealComplex a b) u) ^ 2 := (sq _).symm
    _ = (normDFT1D (fun j => (a j : ℂ)) u) ^ 2 -
          (normDFT1D (fun j => (b j : ℂ)) u) ^ 2 +
          2 * Complex.I * normDFT1D (fun j => (a j : ℂ)) u *
            normDFT1D (fun j => (b j : ℂ)) u := normDFT1D_packRealComplex_sq a b u
    _ = -(Complex.I ^ 2) *
          (normDFT1D (fun j => (a j : ℂ)) u * normDFT1D (fun j => (a j : ℂ)) u -
           normDFT1D (fun j => (b j : ℂ)) u * normDFT1D (fun j => (b j : ℂ)) u) +
          2 * Complex.I * normDFT1D (fun j => (a j : ℂ)) u *
            normDFT1D (fun j => (b j : ℂ)) u := by
        rw [Complex.I_sq]; ring
    _ = (normDFT1D (fun j => (a j : ℂ)) u * normDFT1D (fun j => (b j : ℂ)) u -
          (Complex.I / 2) *
            (normDFT1D (fun j => (a j : ℂ)) u * normDFT1D (fun j => (a j : ℂ)) u -
             normDFT1D (fun j => (b j : ℂ)) u * normDFT1D (fun j => (b j : ℂ)) u)) *
          (2 * Complex.I) := by ring

/-- For any $n$-bit integer $A < 2^n$, summing `natChunk (chunkBits n) A i * f i` over
`i : Fin (rootR0 n)` equals summing over `i ∈ Finset.range (numChunks n)` because all chunks
at indices $i \ge \text{numChunks } n$ vanish. -/
private theorem sum_fin_natChunk_eq_sum_range (n A : ℕ) (hA : A < 2 ^ n) (f : ℕ → ℂ) :
    (∑ i : Fin (rootR0 n), (natChunk (chunkBits n) A i.val : ℂ) * f i.val) =
      ∑ i ∈ Finset.range (numChunks n), (natChunk (chunkBits n) A i : ℂ) * f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (natChunk (chunkBits n) A i : ℂ) * f i) (rootR0 n)]
  have hsub : Finset.range (numChunks n) ⊆ Finset.range (rootR0 n) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    have := two_mul_numChunks_le_rootR0 n
    omega
  symm
  apply Finset.sum_subset hsub
  intro i _ hi_not
  rw [Finset.mem_range, not_lt] at hi_not
  rw [natChunk_eq_zero_of_lt (lt_chunk_pow_of_lt_two_pow hA) hi_not]
  simp

/-- Fourier transform of `linearConvCoeff (chunkBits n) (numChunks n) A B` over `Fin (rootR0 n)`
factors into the product of the chunk trigonometric polynomials over `Finset.range (numChunks n)`. -/
private theorem sum_fin_linearConvCoeff_mul_expTwoPiI (n A B : ℕ) (u : Fin (rootR0 n)) :
    (∑ m : Fin (rootR0 n),
      (linearConvCoeff (chunkBits n) (numChunks n) A B m.val : ℂ) *
        expTwoPiI (((m.val * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))) =
      (∑ i ∈ Finset.range (numChunks n),
        (natChunk (chunkBits n) A i : ℂ) *
          expTwoPiI (((i * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))) *
      (∑ j ∈ Finset.range (numChunks n),
        (natChunk (chunkBits n) B j : ℂ) *
          expTwoPiI (((j * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun m => (linearConvCoeff (chunkBits n) (numChunks n) A B m : ℂ) *
      expTwoPiI (((m * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))) (rootR0 n)]
  unfold linearConvCoeff
  simp_rw [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hi hj
  have h2N : 2 * numChunks n ≤ rootR0 n := two_mul_numChunks_le_rootR0 n
  have hij_lt : i + j < rootR0 n := by omega
  have hite : ∀ m ∈ Finset.range (rootR0 n),
      ((if i + j = m then natChunk (chunkBits n) A i * natChunk (chunkBits n) B j else 0 : ℕ) : ℂ) *
        expTwoPiI (((m * u.val : ℕ) : ℝ) / (rootR0 n : ℝ)) =
      if m = i + j then
        ((natChunk (chunkBits n) A i : ℂ) * expTwoPiI (((i * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))) *
          ((natChunk (chunkBits n) B j : ℂ) * expTwoPiI (((j * u.val : ℕ) : ℝ) / (rootR0 n : ℝ)))
      else 0 := by
    intro m _
    split_ifs with h1 h2
    · subst h1
      have hexp : (((i + j) * u.val : ℕ) : ℝ) / (rootR0 n : ℝ) =
          ((i * u.val : ℕ) : ℝ) / (rootR0 n : ℝ) + ((j * u.val : ℕ) : ℝ) / (rootR0 n : ℝ) := by
        push_cast
        ring
      rw [hexp, expTwoPiI_add]
      push_cast
      ring
    · omega
    · omega
    · simp
  rw [Finset.sum_congr rfl hite]
  simp [Finset.sum_ite_eq', hij_lt]

/-- Pointwise DFT convolution identity on `Fin (rootR0 n)`: for `A, B < 2 ^ n`,
`normDFT1D (fun m => linearConvCoeff b N A B m.val) u = rootR0 n * (normDFT1D aVec u * normDFT1D bVec u)`. -/
private theorem normDFT1D_linearConvCoeff_eq (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (u : Fin (rootR0 n)) :
    normDFT1D (fun m : Fin (rootR0 n) =>
      (linearConvCoeff (chunkBits n) (numChunks n) A B m.val : ℂ)) u =
      (rootR0 n : ℂ) *
        (normDFT1D (fun i : Fin (rootR0 n) => (natChunk (chunkBits n) A i.val : ℂ)) u *
         normDFT1D (fun j : Fin (rootR0 n) => (natChunk (chunkBits n) B j.val : ℂ)) u) := by
  have hR0_pos : 0 < rootR0 n := by
    have := rootR0_ge_four n
    omega
  have hR0_ne : (rootR0 n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hR0_pos)
  unfold normDFT1D
  rw [sum_fin_linearConvCoeff_mul_expTwoPiI n A B u,
    sum_fin_natChunk_eq_sum_range n A hA
      (fun i => expTwoPiI (((i * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))),
    sum_fin_natChunk_eq_sum_range n B hB
      (fun j => expTwoPiI (((j * u.val : ℕ) : ℝ) / (rootR0 n : ℝ)))]
  have hinv : ((rootR0 n : ℝ) : ℂ) = (rootR0 n : ℂ) := by norm_cast
  rw [hinv]
  set SA := ∑ i ∈ Finset.range (numChunks n),
    (natChunk (chunkBits n) A i : ℂ) * expTwoPiI (((i * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))
  set SB := ∑ j ∈ Finset.range (numChunks n),
    (natChunk (chunkBits n) B j : ℂ) * expTwoPiI (((j * u.val : ℕ) : ℝ) / (rootR0 n : ℝ))
  calc
    (rootR0 n : ℂ)⁻¹ * (SA * SB)
      = ((rootR0 n : ℂ) * (rootR0 n : ℂ)⁻¹) * ((rootR0 n : ℂ)⁻¹ * (SA * SB)) := by
        rw [mul_inv_cancel₀ hR0_ne, one_mul]
    _ = (rootR0 n : ℂ) * (((rootR0 n : ℂ)⁻¹ * SA) * ((rootR0 n : ℂ)⁻¹ * SB)) := by ring

/-- **Unconditional 2-Call Complex-Packed DFT Convolution Exactness Theorem
(`twoCallDFTConv_eq_linearConvCoeff`, Lemma 3.4 (`lem:two-call`), Section 7.1 (`sec:alg-spec`),
and Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`))**:
For all $n \in \mathbb{N}$, all $n$-bit integers $A, B < 2^n$, and every slot $k \in \text{Fin (rootR0 } n)$,
the 2-call complex-packed DFT cyclic convolution `twoCallDFTConv n A B k` (computed via pointwise
complex squaring `(Z u * Z u) / (2 * Complex.I)`) has real part equal to the true linear chunk
convolution coefficient `linearConvCoeff (chunkBits n) (numChunks n) A B k.val` and imaginary part
equal to `-(1/2) * (linearConvCoeff ... A A k.val - linearConvCoeff ... B B k.val)`. -/
theorem twoCallDFTConv_eq_linearConvCoeff (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (k : Fin (rootR0 n)) :
    twoCallDFTConv n A B k =
      (linearConvCoeff (chunkBits n) (numChunks n) A B k.val : ℂ) -
        (Complex.I / 2) *
          ((linearConvCoeff (chunkBits n) (numChunks n) A A k.val : ℂ) -
           (linearConvCoeff (chunkBits n) (numChunks n) B B k.val : ℂ)) := by
  unfold twoCallDFTConv
  dsimp only
  let aVec : Fin (rootR0 n) → ℝ := fun j => (natChunk (chunkBits n) A j.val : ℝ)
  let bVec : Fin (rootR0 n) → ℝ := fun j => (natChunk (chunkBits n) B j.val : ℝ)
  let cVec : Fin (rootR0 n) → ℂ := fun m =>
    (linearConvCoeff (chunkBits n) (numChunks n) A B m.val : ℂ) -
      (Complex.I / 2) *
        ((linearConvCoeff (chunkBits n) (numChunks n) A A m.val : ℂ) -
         (linearConvCoeff (chunkBits n) (numChunks n) B B m.val : ℂ))
  rw [Finset.mul_sum]
  have hterm : ∀ u : Fin (rootR0 n),
      (rootR0 n : ℂ) *
        (((normDFT1D (packRealComplex aVec bVec) u *
           normDFT1D (packRealComplex aVec bVec) u) / (2 * Complex.I)) *
          expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (rootR0 n : ℝ))) =
      normDFT1D cVec u * expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (rootR0 n : ℝ)) := by
    intro u
    rw [normDFT1D_packRealComplex_sq_div_two_I aVec bVec u]
    have ha : (fun j : Fin (rootR0 n) => (aVec j : ℂ)) =
        (fun j : Fin (rootR0 n) => (natChunk (chunkBits n) A j.val : ℂ)) := by
      funext j; simp [aVec]
    have hb : (fun j : Fin (rootR0 n) => (bVec j : ℂ)) =
        (fun j : Fin (rootR0 n) => (natChunk (chunkBits n) B j.val : ℂ)) := by
      funext j; simp [bVec]
    rw [ha, hb]
    have hc : normDFT1D cVec u =
        normDFT1D (fun m : Fin (rootR0 n) =>
          (linearConvCoeff (chunkBits n) (numChunks n) A B m.val : ℂ)) u -
        (Complex.I / 2) *
          (normDFT1D (fun m : Fin (rootR0 n) =>
            (linearConvCoeff (chunkBits n) (numChunks n) A A m.val : ℂ)) u -
           normDFT1D (fun m : Fin (rootR0 n) =>
            (linearConvCoeff (chunkBits n) (numChunks n) B B m.val : ℂ)) u) := by
      unfold cVec
      rw [normDFT1D_sub, normDFT1D_smul, normDFT1D_sub]
    rw [hc, normDFT1D_linearConvCoeff_eq n A B hA hB u,
      normDFT1D_linearConvCoeff_eq n A A hA hA u,
      normDFT1D_linearConvCoeff_eq n B B hB hB u]
    ring
  rw [Finset.sum_congr rfl (fun u _ => hterm u)]
  exact sum_normDFT1D_mul_expNegTwoPiI cVec k

/-- Real-part extraction of `twoCallDFTConv` recovers `linearConvCoeff` identically
(Section 3.5 (`sec:prelim-dft`), Lemma 3.4 (`lem:two-call`), and Table 3 (`tab:lean-map`)). -/
theorem twoCallDFTConv_re_eq_linearConvCoeff (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (k : Fin (rootR0 n)) :
    (twoCallDFTConv n A B k).re =
      (linearConvCoeff (chunkBits n) (numChunks n) A B k.val : ℝ) := by
  rw [twoCallDFTConv_eq_linearConvCoeff n A B hA hB k]
  simp

/-- **Nearest-Integer Rounding Recovery of `twoCallDFTConv` (`round_twoCallDFTConv_eq_linearConvCoeff`,
Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`), Part 1)**:
For all $A, B < 2^n$ and $k \in \text{Fin (rootR0 } n)$, nearest-integer rounding of the real part
of `twoCallDFTConv n A B k` recovers `linearConvCoeff (chunkBits n) (numChunks n) A B k.val`. -/
theorem round_twoCallDFTConv_eq_linearConvCoeff (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (k : Fin (rootR0 n)) :
    ⌊(twoCallDFTConv n A B k).re + (1 / 2 : ℝ)⌋.toNat =
      linearConvCoeff (chunkBits n) (numChunks n) A B k.val := by
  rw [twoCallDFTConv_re_eq_linearConvCoeff n A B hA hB k]
  set Ck := linearConvCoeff (chunkBits n) (numChunks n) A B k.val
  have hfl : ⌊(Ck : ℝ) + (1 / 2 : ℝ)⌋ = (Ck : ℤ) :=
    floor_add_half_eq_of_abs_sub_lt_half (M := (Ck : ℤ)) (by simp)
  rw [hfl, Int.toNat_natCast]

/-- Reconstruct the integer product from the base-$2^b$ linear convolution coefficients
$C_k = \text{linearConvCoeff } (chunkBits \, n) \, (numChunks \, n) \, A \, B \, k$ across
$k \in \{0, \dots, R_0 - 1\}$ (Section 7.1 (`sec:alg-spec`) `PropagateCarries` and
Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`), Part 1). -/
def reconstructProductFromChunks (n A B : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (rootR0 n),
    linearConvCoeff (chunkBits n) (numChunks n) A B k * 2 ^ (k * chunkBits n)

/-- **Unconditional Bit-Exact Carry-Propagation Reconstruction Theorem (`reconstructProductFromChunks_eq_mul`,
Section 7.1 (`sec:alg-spec`) and Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`), Part 1)**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$,
`reconstructProductFromChunks n A B = A * B`. -/
@[simp]
theorem reconstructProductFromChunks_eq_mul (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    reconstructProductFromChunks n A B = A * B := by
  unfold reconstructProductFromChunks
  have hpow : ∀ k : ℕ, 2 ^ (k * chunkBits n) = (2 ^ chunkBits n) ^ k := by
    intro k
    rw [Nat.mul_comm, pow_mul]
  simp_rw [hpow]
  exact carry_propagation_rootR0_eq_mul hA hB

/-- **Conditional Bit-Exactness of `reconstructProductViaFastDFT` under Root Convolution Error Budget
(`reconstructProductViaFastDFT_eq_mul_of_root_approx`, Section 7.1 (`sec:alg-spec`) and
Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`), Part 1)**:
Whenever the normalized 2-call `fastDFTRecursive` convolution `(fastTwoCallDFTConv n A B k).re / rootR0 n`
approximates `linearConvCoeff (chunkBits n) (numChunks n) A B k.val / rootR0 n` within the root
error budget `8 * 2 ^ (-rootP0 n) * 2 ^ (2 * chunkBits n + rootK0 n)`, nearest-integer rounding
and base-$2^b$ carry-propagation reconstruction `reconstructProductViaFastDFT n A B` equals `A * B`
bit-exactly. -/
theorem reconstructProductViaFastDFT_eq_mul_of_root_approx (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (herr : ∀ k : Fin (rootR0 n),
      |(fastTwoCallDFTConv n A B k).re / (rootR0 n : ℝ) -
        (linearConvCoeff (chunkBits n) (numChunks n) A B k.val : ℝ) / (rootR0 n : ℝ)| ≤
        8 * (2 : ℝ) ^ (-(rootP0 n : ℤ)) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n)) :
    reconstructProductViaFastDFT n A B = A * B := by
  unfold reconstructProductViaFastDFT
  have hR0_pos : (0 : ℝ) < (rootR0 n : ℝ) := by
    have := rootR0_ge_four n
    positivity
  have hR0_ne : (rootR0 n : ℝ) ≠ 0 := ne_of_gt hR0_pos
  have hterm : ∀ k : Fin (rootR0 n),
      ⌊(fastTwoCallDFTConv n A B k).re + (1 / 2 : ℝ)⌋.toNat * 2 ^ (k.val * chunkBits n) =
        linearConvCoeff (chunkBits n) (numChunks n) A B k.val * 2 ^ (k.val * chunkBits n) := by
    intro k
    have hrec := (root_conv_recovery_of_fastDFT_approx n A B k.val
      ((fastTwoCallDFTConv n A B k).re / (rootR0 n : ℝ)) (herr k)).2
    have hmul : (rootR0 n : ℝ) * ((fastTwoCallDFTConv n A B k).re / (rootR0 n : ℝ)) =
        (fastTwoCallDFTConv n A B k).re := mul_div_cancel₀ _ hR0_ne
    rw [hmul] at hrec
    rw [hrec, Int.toNat_natCast]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range
      (fun k => linearConvCoeff (chunkBits n) (numChunks n) A B k * 2 ^ (k * chunkBits n))
      (rootR0 n)]
  exact reconstructProductFromChunks_eq_mul n A B hA hB

/-- **Unconditional 2-Call `fastDFTRecursive` Root Convolution Error Bound
(`fastTwoCallDFTConv_sub_linearConvCoeff_le`, Theorem 1 (`thm:main`),
Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`), Part 1)**:
For all $n \in \mathbb{N}$, all $n$-bit integers $A, B < 2^n$, and every slot $k \in \text{Fin (rootR0 } n)$,
the concrete 2-call `fastDFTRecursive` convolution `fastTwoCallDFTConv n A B k` satisfies
`|(fastTwoCallDFTConv n A B k).re / rootR0 n - linearConvCoeff (chunkBits n) (numChunks n) A B k.val / rootR0 n| ≤ 8 * 2 ^ (-rootP0 n) * 2 ^ (2 * chunkBits n + rootK0 n)`
unconditionally. -/
theorem fastTwoCallDFTConv_sub_linearConvCoeff_le (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) (k : Fin (rootR0 n)) :
    |(fastTwoCallDFTConv n A B k).re / (rootR0 n : ℝ) -
      (linearConvCoeff (chunkBits n) (numChunks n) A B k.val : ℝ) / (rootR0 n : ℝ)| ≤
      8 * (2 : ℝ) ^ (-(rootP0 n : ℤ)) * (2 : ℝ) ^ (2 * chunkBits n + rootK0 n) := by
  let K0 := rootK0 n
  let p0 := rootP0 n
  let R0 := rootR0 n
  let b := chunkBits n
  let aVec : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let bVec : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let zVec : Fin R0 → ℂ := packRealComplex aVec bVec
  let Z : Fin R0 → ℂ := fun u => (fastDFTRecursive K0 p0 zVec u).toComplex
  let Z_true : Fin R0 → ℂ := normDFT1D zVec
  let W_conj : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
  let W_true : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ ((Z_true u * Z_true u) / (2 * Complex.I))
  let C_inv : Fin R0 → ℂ := fun m => starRingEnd ℂ ((fastDFTRecursive K0 p0 W_conj m).toComplex)
  let cVec : Fin R0 → ℂ := fun m =>
    (linearConvCoeff b (numChunks n) A B m.val : ℂ) -
      (Complex.I / 2) *
        ((linearConvCoeff b (numChunks n) A A m.val : ℂ) -
         (linearConvCoeff b (numChunks n) B B m.val : ℂ))
  have hp0_ge18 : 18 ≤ p0 := rootP0_ge_eighteen n
  have h2p0_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p0 : ℤ)) := zpow_pos (by norm_num) _
  have h2p0_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (1 / 16 : ℝ) := by
    calc
      (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (2 : ℝ) ^ (-4 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have ha_le : ∀ j : Fin R0, ‖(aVec j : ℂ)‖ ≤ 1 := by
    intro j
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlt : (natChunk b A j.val : ℝ) ≤ (2 : ℝ) ^ b := by
      exact_mod_cast le_of_lt (natChunk_lt b A j.val)
    calc
      (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ)) :=
          mul_le_mul_of_nonneg_right hlt (le_of_lt (zpow_pos (by norm_num) _))
      _ = 1 := two_pow_mul_two_zpow_neg b
  have hb_le : ∀ j : Fin R0, ‖(bVec j : ℂ)‖ ≤ 1 := by
    intro j
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlt : (natChunk b B j.val : ℝ) ≤ (2 : ℝ) ^ b := by
      exact_mod_cast le_of_lt (natChunk_lt b B j.val)
    calc
      (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ)) :=
          mul_le_mul_of_nonneg_right hlt (le_of_lt (zpow_pos (by norm_num) _))
      _ = 1 := two_pow_mul_two_zpow_neg b
  have hz_sqrt2 : vecInfNorm zVec ≤ Real.sqrt 2 := by
    apply vecInfNorm_le zVec (by positivity)
    intro j
    have hre : |(zVec j).re| ≤ 1 := by simpa [zVec, packRealComplex, Complex.norm_real] using ha_le j
    have him : |(zVec j).im| ≤ 1 := by simpa [zVec, packRealComplex, Complex.norm_real] using hb_le j
    simpa using norm_complex_le_of_re_im_le zero_le_one hre him
  have hz_max : max 1 (vecInfNorm zVec) ≤ 2 := by
    apply max_le (by norm_num)
    exact hz_sqrt2.trans (sqrt_two_le.trans (by norm_num))
  have hZ_err : ∀ u : Fin R0, ‖Z u - Z_true u‖ ≤ 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    intro u
    have h1 := norm_le_vecInfNorm (fun v => Z v - Z_true v) u
    have h2 := vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_two_zpow n 0 (Nat.zero_le _) zVec
    calc
      ‖Z u - Z_true u‖ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm zVec) := h1.trans h2
      _ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * 2 := mul_le_mul_of_nonneg_left hz_max (le_of_lt h2p0_pos)
      _ = 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by ring
  have hZ_true_le : ∀ u : Fin R0, ‖Z_true u‖ ≤ Real.sqrt 2 :=
    fun u => (norm_normDFT1D_le zVec u).trans hz_sqrt2
  have hWt_le : ∀ u : Fin R0, ‖W_true u‖ ≤ 1 := by
    intro u
    unfold W_true
    rw [RCLike.norm_conj, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    have hsq : ‖Z_true u‖ * ‖Z_true u‖ ≤ 2 := by
      calc
        ‖Z_true u‖ * ‖Z_true u‖ ≤ Real.sqrt 2 * Real.sqrt 2 :=
          mul_self_le_mul_self (norm_nonneg _) (hZ_true_le u)
        _ = 2 := Real.mul_self_sqrt (by norm_num)
    linarith
  have hW_err : ∀ u : Fin R0, ‖W_conj u - W_true u‖ ≤ (11 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    intro u
    unfold W_conj W_true
    rw [← map_sub, RCLike.norm_conj]
    have hZt_144 : ‖Z_true u‖ ≤ 72 / 50 := (hZ_true_le u).trans sqrt_two_le
    have hZ_sum : ‖Z u + Z_true u‖ ≤ 5 := by
      have h1 := norm_add_le (Z u - Z_true u) (Z_true u + Z_true u)
      have h2 := norm_add_le (Z_true u) (Z_true u)
      have heq : (Z u - Z_true u) + (Z_true u + Z_true u) = Z u + Z_true u := by ring
      rw [heq] at h1
      linarith [hZ_err u, hZt_144, h2p0_le]
    have hprod_sub : (Z u * Z u) / (2 * Complex.I) - (Z_true u * Z_true u) / (2 * Complex.I) =
        ((Z u + Z_true u) * (Z u - Z_true u)) / (2 * Complex.I) := by ring
    have hprod_err :
        ‖(Z u * Z u) / (2 * Complex.I) - (Z_true u * Z_true u) / (2 * Complex.I)‖ ≤
          5 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      rw [hprod_sub, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      have hm : ‖Z u + Z_true u‖ * ‖Z u - Z_true u‖ ≤ 5 * (2 * (2 : ℝ) ^ (-(p0 : ℤ))) :=
        mul_le_mul hZ_sum (hZ_err u) (norm_nonneg _) (by norm_num)
      linarith
    have hq_err :
        ‖quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)) -
          (Z u * Z u) / (2 * Complex.I)‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      have hq := norm_quantizeComplex_sub_self_le (p0 + 2) ((Z u * Z u) / (2 * Complex.I))
      have hexp : -((p0 + 2 : ℕ) : ℤ) = -(p0 : ℤ) + (-2 : ℤ) := by omega
      have hpow : (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
        rw [hexp, zpow_add₀ (by norm_num)]
        norm_num
        ring
      rw [hpow] at hq
      have hsqrt := sqrt_two_le
      nlinarith only [hq, hsqrt, h2p0_pos]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
      ((Z u * Z u) / (2 * Complex.I))
      ((Z_true u * Z_true u) / (2 * Complex.I))
    linarith
  have hW_max : max 1 (vecInfNorm W_conj) ≤ 2 := by
    apply max_le (by norm_num)
    apply vecInfNorm_le W_conj (by norm_num)
    intro u
    have htri := norm_add_le (W_conj u - W_true u) (W_true u)
    rw [sub_add_cancel] at htri
    linarith [hW_err u, hWt_le u, h2p0_le]
  have hC_inv_err : ‖C_inv k - starRingEnd ℂ (normDFT1D W_true k)‖ ≤
      8 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    unfold C_inv
    rw [← map_sub, RCLike.norm_conj]
    have h1 : ‖(fastDFTRecursive K0 p0 W_conj k).toComplex - normDFT1D W_conj k‖ ≤
        2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      have ha := norm_le_vecInfNorm
        (fun m => (fastDFTRecursive K0 p0 W_conj m).toComplex - normDFT1D W_conj m) k
      have hb := vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_two_zpow n 0 (Nat.zero_le _) W_conj
      calc
        ‖(fastDFTRecursive K0 p0 W_conj k).toComplex - normDFT1D W_conj k‖
          ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm W_conj) := ha.trans hb
        _ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * 2 := mul_le_mul_of_nonneg_left hW_max (le_of_lt h2p0_pos)
        _ = 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by ring
    have h2 : ‖normDFT1D W_conj k - normDFT1D W_true k‖ ≤
        (11 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      rw [← normDFT1D_sub]
      exact (norm_normDFT1D_le (fun u => W_conj u - W_true u) k).trans
        (vecInfNorm_le _ (by positivity) hW_err)
    have htri := norm_sub_le_norm_sub_add_norm_sub
      ((fastDFTRecursive K0 p0 W_conj k).toComplex) (normDFT1D W_conj k) (normDFT1D W_true k)
    linarith
  have hW_true_id : ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) *
      starRingEnd ℂ (normDFT1D W_true k))) = cVec k := by
    have hscale_real : ((2 ^ (2 * b) : ℕ) : ℝ) *
        ((2 : ℝ) ^ (-(b : ℤ)) * (2 : ℝ) ^ (-(b : ℤ))) = 1 := by
      have h2b : ((2 ^ (2 * b) : ℕ) : ℝ) = (2 : ℝ) ^ b * (2 : ℝ) ^ b := by
        rw [Nat.two_mul, pow_add]
        push_cast
        rfl
      calc
        ((2 ^ (2 * b) : ℕ) : ℝ) * ((2 : ℝ) ^ (-(b : ℤ)) * (2 : ℝ) ^ (-(b : ℤ)))
          = ((2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ))) * ((2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ))) := by
            rw [h2b]; ring
        _ = 1 := by rw [two_pow_mul_two_zpow_neg b, mul_one]
    have hscale_c : ((2 ^ (2 * b) : ℕ) : ℂ) *
        ((((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hscale_real
    have hWu : ∀ u : Fin R0,
        ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * W_true u) = starRingEnd ℂ (normDFT1D cVec u) := by
      intro u
      unfold W_true Z_true zVec
      rw [normDFT1D_packRealComplex_sq_div_two_I aVec bVec u]
      have ha : (fun j : Fin R0 => (aVec j : ℂ)) =
          (fun j : Fin R0 => (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * (natChunk b A j.val : ℂ)) := by
        funext j; simp [aVec, mul_comm]
      have hb : (fun j : Fin R0 => (bVec j : ℂ)) =
          (fun j : Fin R0 => (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * (natChunk b B j.val : ℂ)) := by
        funext j; simp [bVec, mul_comm]
      rw [ha, hb, normDFT1D_smul, normDFT1D_smul]
      have hconvAB := normDFT1D_linearConvCoeff_eq n A B hA hB u
      have hconvAA := normDFT1D_linearConvCoeff_eq n A A hA hA u
      have hconvBB := normDFT1D_linearConvCoeff_eq n B B hB hB u
      have hc : normDFT1D cVec u =
          normDFT1D (fun m : Fin R0 => (linearConvCoeff b (numChunks n) A B m.val : ℂ)) u -
          (Complex.I / 2) *
            (normDFT1D (fun m : Fin R0 => (linearConvCoeff b (numChunks n) A A m.val : ℂ)) u -
             normDFT1D (fun m : Fin R0 => (linearConvCoeff b (numChunks n) B B m.val : ℂ)) u) := by
        unfold cVec
        rw [normDFT1D_sub, normDFT1D_smul, normDFT1D_sub]
      set FA := normDFT1D (fun i : Fin R0 => (natChunk b A i.val : ℂ)) u
      set FB := normDFT1D (fun j : Fin R0 => (natChunk b B j.val : ℂ)) u
      set sb : ℂ := (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ)
      have hxy : ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) *
          ((sb * FA) * (sb * FB) - (Complex.I / 2) * ((sb * FA) * (sb * FA) - (sb * FB) * (sb * FB)))) =
          normDFT1D cVec u := by
        calc
          ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) *
              ((sb * FA) * (sb * FB) - (Complex.I / 2) * ((sb * FA) * (sb * FA) - (sb * FB) * (sb * FB))))
            = (((2 ^ (2 * b) : ℕ) : ℂ) * (sb * sb)) *
                ((R0 : ℂ) * (FA * FB) - (Complex.I / 2) * ((R0 : ℂ) * (FA * FA) - (R0 : ℂ) * (FB * FB))) := by
              ring
          _ = normDFT1D cVec u := by
              rw [hscale_c, one_mul, hc, hconvAB, hconvAA, hconvBB]
      have hconj := congrArg (starRingEnd ℂ) hxy
      simpa only [map_mul, map_natCast] using hconj
    have hfun : (fun u : Fin R0 => starRingEnd ℂ (normDFT1D cVec u)) =
        (fun u : Fin R0 => (((2 ^ (2 * b) : ℕ) : ℂ) * (R0 : ℂ)) * W_true u) := by
      funext u
      rw [mul_assoc, hWu u]
    have hdft := congrArg (fun f => (R0 : ℂ) * starRingEnd ℂ (normDFT1D f k)) hfun
    rw [conj_normDFT1D_conj_eq cVec k, normDFT1D_smul, map_mul, map_mul,
      map_natCast, map_natCast] at hdft
    calc
      ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) * starRingEnd ℂ (normDFT1D W_true k)))
        = (R0 : ℂ) * ((((2 ^ (2 * b) : ℕ) : ℂ) * (R0 : ℂ)) *
            starRingEnd ℂ (normDFT1D W_true k)) := by ring
      _ = cVec k := hdft.symm
  have hR0_pos : (0 : ℝ) < (R0 : ℝ) := by
    have := rootR0_ge_four n
    positivity
  have hR0_ne : (R0 : ℝ) ≠ 0 := ne_of_gt hR0_pos
  have hsub_c : fastTwoCallDFTConv n A B k - cVec k =
      ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) *
        (C_inv k - starRingEnd ℂ (normDFT1D W_true k)))) := by
    rw [← hW_true_id]
    change ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) * C_inv k)) -
      ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) * starRingEnd ℂ (normDFT1D W_true k))) = _
    ring
  have hre_div : |(fastTwoCallDFTConv n A B k).re / (R0 : ℝ) -
      (linearConvCoeff b (numChunks n) A B k.val : ℝ) / (R0 : ℝ)| ≤
      ‖fastTwoCallDFTConv n A B k - cVec k‖ / (R0 : ℝ) := by
    have hre : (fastTwoCallDFTConv n A B k).re / (R0 : ℝ) -
        (linearConvCoeff b (numChunks n) A B k.val : ℝ) / (R0 : ℝ) =
        (fastTwoCallDFTConv n A B k - cVec k).re / (R0 : ℝ) := by
      simp [cVec, sub_div]
    rw [hre, abs_div, abs_of_pos hR0_pos]
    exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (le_of_lt hR0_pos)
  have hnorm_sub : ‖fastTwoCallDFTConv n A B k - cVec k‖ / (R0 : ℝ) =
      (2 : ℝ) ^ (2 * b + K0) * ‖C_inv k - starRingEnd ℂ (normDFT1D W_true k)‖ := by
    rw [hsub_c, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have hpow_R0 : ((2 ^ (2 * b) : ℕ) : ℝ) * (R0 : ℝ) = (2 : ℝ) ^ (2 * b + K0) := by
      change ((2 ^ (2 * b) : ℕ) : ℝ) * ((2 ^ K0 : ℕ) : ℝ) = (2 : ℝ) ^ (2 * b + K0)
      rw [pow_add]
      push_cast
      rfl
    calc
      ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * ((R0 : ℝ) *
          ‖C_inv k - starRingEnd ℂ (normDFT1D W_true k)‖)) / (R0 : ℝ)
        = (((2 ^ (2 * b) : ℕ) : ℝ) * (R0 : ℝ)) *
            ‖C_inv k - starRingEnd ℂ (normDFT1D W_true k)‖ * ((R0 : ℝ) / (R0 : ℝ)) := by ring
      _ = (2 : ℝ) ^ (2 * b + K0) * ‖C_inv k - starRingEnd ℂ (normDFT1D W_true k)‖ := by
        rw [div_self hR0_ne, mul_one, hpow_R0]
  calc
    |(fastTwoCallDFTConv n A B k).re / (R0 : ℝ) -
        (linearConvCoeff b (numChunks n) A B k.val : ℝ) / (R0 : ℝ)|
      ≤ ‖fastTwoCallDFTConv n A B k - cVec k‖ / (R0 : ℝ) := hre_div
    _ = (2 : ℝ) ^ (2 * b + K0) * ‖C_inv k - starRingEnd ℂ (normDFT1D W_true k)‖ := hnorm_sub
    _ ≤ (2 : ℝ) ^ (2 * b + K0) * (8 * (2 : ℝ) ^ (-(p0 : ℤ))) :=
        mul_le_mul_of_nonneg_left hC_inv_err (by positivity)
    _ = 8 * (2 : ℝ) ^ (-(p0 : ℤ)) * (2 : ℝ) ^ (2 * b + K0) := by ring

/-- **Unconditional Nearest-Integer Rounding Recovery of `fastTwoCallDFTConv`
(`round_fastTwoCallDFTConv_eq_linearConvCoeff`, Theorem 1 (`thm:main`),
Section 7.2 (`sec:cost-proof`), Part 1)**:
For all $n \in \mathbb{N}$, all $n$-bit integers $A, B < 2^n$, and every slot $k \in \text{Fin (rootR0 } n)$,
nearest-integer rounding of `(fastTwoCallDFTConv n A B k).re` recovers
`linearConvCoeff (chunkBits n) (numChunks n) A B k.val` unconditionally. -/
@[simp]
theorem round_fastTwoCallDFTConv_eq_linearConvCoeff (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) (k : Fin (rootR0 n)) :
    ⌊(fastTwoCallDFTConv n A B k).re + (1 / 2 : ℝ)⌋.toNat =
      linearConvCoeff (chunkBits n) (numChunks n) A B k.val := by
  have hR0_pos : (0 : ℝ) < (rootR0 n : ℝ) := by
    have := rootR0_ge_four n
    positivity
  have hR0_ne : (rootR0 n : ℝ) ≠ 0 := ne_of_gt hR0_pos
  have hrec := (root_conv_recovery_of_fastDFT_approx n A B k.val
    ((fastTwoCallDFTConv n A B k).re / (rootR0 n : ℝ))
    (fastTwoCallDFTConv_sub_linearConvCoeff_le n A B hA hB k)).2
  have hmul : (rootR0 n : ℝ) * ((fastTwoCallDFTConv n A B k).re / (rootR0 n : ℝ)) =
      (fastTwoCallDFTConv n A B k).re := mul_div_cancel₀ _ hR0_ne
  rw [hmul] at hrec
  rw [hrec, Int.toNat_natCast]

/-- **Unconditional Bit-Exactness of `reconstructProductViaFastDFT`
(`reconstructProductViaFastDFT_eq_mul`, Section 7.1 (`sec:alg-spec`),
Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`), and Theorem 2 (`thm:lean`))**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, the concrete 2-call
`fastDFTRecursive` convolution and carry-propagation reconstruction `reconstructProductViaFastDFT n A B`
equals `A * B` bit-exactly. -/
@[simp]
theorem reconstructProductViaFastDFT_eq_mul (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    reconstructProductViaFastDFT n A B = A * B :=
  reconstructProductViaFastDFT_eq_mul_of_root_approx n A B hA hB
    (fastTwoCallDFTConv_sub_linearConvCoeff_le n A B hA hB)

/-- Reconstruct the integer product via the 2-call complex-packed DFT cyclic convolution
`twoCallDFTConv n A B k`, nearest-integer rounding `⌊... + 1/2⌋.toNat`, and base-$2^b$
carry-propagation evaluation (Section 7.1 (`sec:alg-spec`) and Theorem 1 (`thm:main`) in
Section 7.2 (`sec:cost-proof`), Part 1). -/
noncomputable def reconstructProductViaTwoCallDFT (n A B : ℕ) : ℕ :=
  ∑ k : Fin (rootR0 n),
    ⌊(twoCallDFTConv n A B k).re + (1 / 2 : ℝ)⌋.toNat * 2 ^ (k.val * chunkBits n)

/-- **Unconditional Exactness of 2-Call DFT Product Reconstruction
(`reconstructProductViaTwoCallDFT_eq_mul`, Section 7.1 (`sec:alg-spec`) and
Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`), Part 1)**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$,
`reconstructProductViaTwoCallDFT n A B = A * B`. -/
@[simp]
theorem reconstructProductViaTwoCallDFT_eq_mul (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    reconstructProductViaTwoCallDFT n A B = A * B := by
  unfold reconstructProductViaTwoCallDFT
  have hterm : ∀ k : Fin (rootR0 n),
      ⌊(twoCallDFTConv n A B k).re + (1 / 2 : ℝ)⌋.toNat * 2 ^ (k.val * chunkBits n) =
        linearConvCoeff (chunkBits n) (numChunks n) A B k.val * 2 ^ (k.val * chunkBits n) := by
    intro k
    rw [round_twoCallDFTConv_eq_linearConvCoeff n A B hA hB k]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range
      (fun k => linearConvCoeff (chunkBits n) (numChunks n) A B k * 2 ^ (k * chunkBits n))
      (rootR0 n)]
  exact reconstructProductFromChunks_eq_mul n A B hA hB

/-- Any product of two $n$-bit non-negative integers $A, B < 2^n$ fits strictly in $2n$ bits:
$A \cdot B < 2^{2n}$. -/
theorem mul_lt_two_pow_two_mul (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    A * B < 2 ^ (2 * n) := by
  calc
    A * B < 2 ^ n * 2 ^ n := mul_lt_mul'' hA hB (Nat.zero_le A) (Nat.zero_le B)
    _ = 2 ^ (2 * n) := by rw [← pow_add, Nat.two_mul]

/-! ### 2.5 Stage 5: Data-Independent Schedule-Driven Slot Sizing (`scheduleSlotBits`, `fastDFTRecursiveSched`) & Inductive Magnitude Invariant (Section 3.2 (`sec:prelim-model`) equation (5) (`eq:height-bound`) and Section 6.2 (`sec:kronecker`) equation (31) (`eq:slot-width`)) -/

/-- Computable data-independent child integer headroom bits at level `(K, p)`
(Section 3.2 (`sec:prelim-model`), equation (5) (`eq:height-bound`)). Since
`windowLengthEll K p ≤ 2 * pChildEll K p + 1`, the per-level $\ell_\infty$ norm growth factor
`windowLengthEll K p + 3` is at most
`2 * pChildEll K p + 4 ≤ 2 ^ (Nat.clog 2 (2 * pChildEll K p + 4))`, adding only
$O(\log p_{\text{child}}) = O(\log \log n)$ bits per recursion level. -/
def childScheduleBIn (K p B_in : ℕ) : ℕ :=
  B_in + Nat.clog 2 (2 * pChildEll K p + 4)

/-- Computable data-independent schedule headroom `B_in` at recursion level `ell` starting from
root headroom `B_root = 2` (Section 3.2 (`sec:prelim-model`), equation (5) (`eq:height-bound`)). -/
def levelScheduleBIn (K0 p0 : ℕ) : ℕ → ℕ
  | 0 => 2
  | ell + 1 =>
    childScheduleBIn (levelK K0 ell) (levelP K0 p0 ell) (levelScheduleBIn K0 p0 ell)

/-- Computable data-independent Kronecker slot bit-width at level `(K, p)` with schedule headroom
`B_in` and half-width `m1` (Section 6.2 (`sec:kronecker`), equation (31) (`eq:slot-width`)). -/
def scheduleSlotBits (K p B_in m1 : ℕ) : ℕ :=
  kroneckerSlotBitsRaw (qChildEll K p) (max (K + 4) (B_in + 1)) m1 (foldedHalfWidth m1 (rEll K))

/-- Whenever `vecInfNorm x ≤ (2 : ℝ) ^ B_in`, every quantized sample `quantizeComplexFixed q (x j)`
satisfies the data-independent word-width bound `WordWidthBounds (q + max (K + 4) (B_in + 1))`. -/
theorem wordWidthBounds_quantizeComplexFixed_of_vecInfNorm_le (K q B_in : ℕ) {R : ℕ}
    (x : Fin R → ℂ) (hx : vecInfNorm x ≤ (2 : ℝ) ^ B_in) (j : Fin R) :
    WordWidthBounds (q + max (K + 4) (B_in + 1)) (quantizeComplexFixed q (x j)) := by
  have hnorm : ‖x j‖ ≤ (2 : ℝ) ^ B_in := (norm_le_vecInfNorm x j).trans hx
  have hw := wordWidthBounds_quantizeComplexFixed_of_norm_le (b := B_in) (q := q) hnorm
  apply hw.mono
  omega

/-- Under the schedule magnitude invariant `vecInfNorm x ≤ (2 : ℝ) ^ B_in`, Step 1 of the
schedule-driven operator (`kroneckerMatrixSpreadFixed` with data-independent slot width
`scheduleSlotBits K p B_in (m1Ell K p)`) equals `refMatrixSpreadFixed`. -/
theorem fastDFTRecursiveSched_step1_eq_refMatrixSpreadFixed (K p B_in : ℕ)
    (x : Fin (2 ^ K) → ℂ) (hx : vecInfNorm x ≤ (2 : ℝ) ^ B_in) :
    let t1 := t1Ell K
    let r := rEll K
    let qChild := qChildEll K p
    let m1 := m1Ell K p
    let B_slot := scheduleSlotBits K p B_in m1
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r (Nat.two_pow_pos K) (fun j => quantizeComplexFixed qChild (x j))
    kroneckerMatrixSpreadFixed t1 r m1 B_slot qChild qChild (rEll_pos K)
      U_gathered (levelFilterTapFixed K p) =
    refMatrixSpreadFixed t1 r m1 qChild qChild (rEll_pos K)
      U_gathered (levelFilterTapFixed K p) := by
  intro t1 r qChild m1 B_slot U_gathered
  funext j1 k2
  exact kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_raw_bounds
    t1 r m1 qChild (max (K + 4) (B_in + 1)) qChild qChild (rEll_pos K)
    (foldedHalfWidth_m1Ell_pos K p) U_gathered (levelFilterTapFixed K p)
    (fun _ _ => wordWidthBounds_quantizeComplexFixed_of_vecInfNorm_le K qChild B_in x hx _)
    (fitsSignedWord_levelFilterTapFixed K p)
    j1 k2

/-- **Inductive Child Input Magnitude Invariant (`vecInfNorm_fastDFTRecursive_Q_post_le`,
Section 3.2 (`sec:prelim-model`) equation (5) (`eq:height-bound`) and Lemma 6.5 (`lem:forward`))**:
At any level `(K, p)` with `8 ≤ p`, if the parent input satisfies `vecInfNorm x ≤ (2 : ℝ) ^ B_in`,
then every post-twisted polynomial-transform (`syntheticFFT`) child input vector `Q_post v1` satisfies
`vecInfNorm (Q_post v1) ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in)`. -/
theorem vecInfNorm_fastDFTRecursive_Q_post_le {K p B_in : ℕ} (hp : 8 ≤ p)
    (x : Fin (2 ^ K) → ℂ) (hx : vecInfNorm x ≤ (2 : ℝ) ^ B_in) :
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let m1 := m1Ell K p
    let hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    let hr_pos : 0 < r := rEll_pos K
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => quantizeComplexFixed qChild (x j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered (levelFilterTapFixed K p)
    let U_spread : Fin t1 → Fin r → ℂ := fun j1 k2 => (U_spreadFixed j1 k2).toComplex
    let U_pre : Fin t1 → Fin r → ℂ := preTwistQuantRoots qChild U_spread
    let Q_syn : Fin t1 → Fin r → ℂ := radix2SyntheticFFTQuant qChild (k1Ell K) c1 U_pre
    let Q_post : Fin t1 → Fin r → ℂ := postTwistQuantRoots qChild Q_syn
    ∀ v1 : Fin t1, vecInfNorm (Q_post v1) ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in) := by
  intro t1 r c1 qChild m1 hR_pos hr_pos U_gathered U_spreadFixed U_spread U_pre Q_syn Q_post v1
  let pChild := pChildEll K p
  let alpha := alphaEll K p
  let ht1_pos : 0 < t1 := t1Ell_pos K
  let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
  let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
  let U_true : Fin t1 → Fin r → ℂ :=
    spreadArray hr_pos m1 xCast (fun j1 d => (filterTap alpha m1 t1 j1 d : ℂ))
  let W := (windowLengthEll K p : ℝ)
  let M := max 1 (vecInfNorm x)
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have hW_pos : 0 < W := by
    change 0 < ((2 * m1 + 1 : ℕ) : ℝ)
    positivity
  have hstep1 := matInfNorm_fastDFTRecursive_step1_sub_le hp x
  have hstep1_eq :
      kroneckerMatrixSpreadFixed t1 r m1
        (kroneckerSlotBitsRaw qChild (levelBIn K x) m1 (foldedHalfWidth m1 r))
        qChild qChild hr_pos U_gathered (levelFilterTapFixed K p) = U_spreadFixed :=
    fastDFTRecursive_step1_eq_refMatrixSpreadFixed K p x
  have hU_true_le : matInfNorm U_true ≤ W * M := hstep1.1
  have hU_sub_le : matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) ≤
      (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    have h := hstep1.2.1
    dsimp only at h
    rwa [hstep1_eq] at h
  have hU_spread_le : matInfNorm U_spread ≤ (W + 1) * M := by
    have h := hstep1.2.2
    rwa [hstep1_eq] at h
  clear hstep1
  let U_pre_true : Fin t1 → Fin r → ℂ := preTwistExact U_true
  let Q_syn_true : Fin t1 → Fin r → ℂ := syntheticFFT c1 U_pre_true
  let Q_post_true : Fin t1 → Fin r → ℂ := postTwistExact Q_syn_true
  have hU_pre_true_le : matInfNorm U_pre_true ≤ W * M :=
    (matInfNorm_preTwistExact_le U_true).trans hU_true_le
  have hQ_syn_true_le : matInfNorm Q_syn_true ≤ W * M :=
    (matInfNorm_syntheticFFT_le ht1_pos c1 U_pre_true).trans hU_pre_true_le
  have hQ_post_true_le : matInfNorm Q_post_true ≤ W * M :=
    (matInfNorm_postTwistExact_le Q_syn_true).trans hQ_syn_true_le
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h2q_le : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
      (18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
    have hexp : -(qChild : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by
      change -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ)
      omega
    have hpow : (2 : ℝ) ^ (-(qChild : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
      rw [hexp, zpow_add₀ (by norm_num)]
      norm_num
      ring
    rw [hpow]
    have hsqrt := sqrt_two_le
    nlinarith
  have hW_le : W ≤ 2 * (pChild : ℝ) + 1 := by
    unfold W pChild
    exact_mod_cast windowLengthEll_le_two_mul_pChildEll_add_one K p
  have hK_le : (K : ℝ) ≤ (pChild : ℝ) := by
    have : K ≤ pChild := by unfold pChild pChildEll pWorkEll; omega
    exact_mod_cast this
  have hpow_le : ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 := by
    have h1 : pChild + 1 ≤ 2 ^ pChild := Nat.lt_two_pow_self
    have h1r : (pChild : ℝ) + 1 ≤ (2 : ℝ) ^ pChild := by exact_mod_cast h1
    calc
      ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))
        ≤ (2 : ℝ) ^ pChild * (2 : ℝ) ^ (-(pChild : ℤ)) :=
          mul_le_mul_of_nonneg_right h1r (le_of_lt h2p_pos)
      _ = 1 := two_pow_mul_two_zpow_neg pChild
  have hU_pre_sub : matInfNorm (fun j1 k2 => U_pre j1 k2 - U_pre_true j1 k2) ≤
      ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ)) *
        (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    have h1 := matInfNorm_preTwistQuantRoots_sub_le qChild U_spread U_true
    have h2 : 1 + matInfNorm U_spread ≤ (W + 2) * M := by
      linarith only [hU_spread_le, hM_ge_one]
    have h3 : (1 + matInfNorm U_spread) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ))) ≤
        ((W + 2) * M) * ((18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) :=
      mul_le_mul h2 h2q_le (by positivity) (by positivity)
    linarith only [h1, h3, hU_sub_le]
  have hQ_syn_sub : matInfNorm (fun i1 k2 => Q_syn i1 k2 - Q_syn_true i1 k2) ≤
      ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) + (18 / 100 : ℝ) * (K : ℝ)) *
        (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    apply matInfNorm_le _ (by positivity)
    intro i1 k2
    have hsyn_err := syntheticFFT_rounding_error_le K pChild c1 (t1Ell_mul_c1Ell K) U_pre i1
    have h1 : ‖Q_syn i1 k2 - syntheticFFT c1 U_pre i1 k2‖ ≤
        (18 / 100 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
      have h1a : ‖Q_syn i1 k2 - syntheticFFT c1 U_pre i1 k2‖ ≤
          (0.18 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * 1 := by
        have h1b := (norm_le_vecInfNorm (fun m => Q_syn i1 m - syntheticFFT c1 U_pre i1 m) k2).trans
          (hsyn_err.1.trans hsyn_err.2)
        linarith only [h1b]
      exact h1a.trans (by gcongr; norm_num)
    have h2 : ‖syntheticFFT c1 U_pre i1 k2 - Q_syn_true i1 k2‖ ≤
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ)) *
          (2 : ℝ) ^ (-(pChild : ℤ)) * M :=
      (norm_le_matInfNorm (fun j1 j2 => syntheticFFT c1 U_pre j1 j2 - Q_syn_true j1 j2) i1 k2).trans
        ((matInfNorm_syntheticFFT_sub_le ht1_pos c1 U_pre U_pre_true).trans hU_pre_sub)
    have htri := norm_sub_le_norm_sub_add_norm_sub (Q_syn i1 k2)
      (syntheticFFT c1 U_pre i1 k2) (Q_syn_true i1 k2)
    linarith only [htri, h1, h2]
  have hQ_syn_le : matInfNorm Q_syn ≤ (W + 2) * M := by
    have hcoeff : ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
        (18 / 100 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 2 := by
      have hlin : (W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) ≤ 2 * ((pChild : ℝ) + 1) := by
        linarith only [hW_le, hK_le]
      calc
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
            (18 / 100 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (2 * ((pChild : ℝ) + 1)) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right hlin (le_of_lt h2p_pos)
        _ = 2 * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        _ ≤ 2 * 1 := by linarith only [hpow_le]
        _ = 2 := by ring
    have herr_le : matInfNorm (fun i1 k2 => Q_syn i1 k2 - Q_syn_true i1 k2) ≤ 2 * M :=
      hQ_syn_sub.trans (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hM_pos))
    apply matInfNorm_le _ (by positivity)
    intro i1 k2
    have h1 := (norm_le_matInfNorm (fun j1 j2 => Q_syn j1 j2 - Q_syn_true j1 j2) i1 k2).trans herr_le
    have h2 := (norm_le_matInfNorm Q_syn_true i1 k2).trans hQ_syn_true_le
    have htri : ‖Q_syn i1 k2‖ ≤ ‖Q_syn i1 k2 - Q_syn_true i1 k2‖ + ‖Q_syn_true i1 k2‖ := by
      simpa using norm_add_le (Q_syn i1 k2 - Q_syn_true i1 k2) (Q_syn_true i1 k2)
    linarith only [htri, h1, h2]
  have hQ_post_sub : matInfNorm (fun i1 k2 => Q_post i1 k2 - Q_post_true i1 k2) ≤
      (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    have h1 := matInfNorm_postTwistQuantRoots_sub_le qChild Q_syn Q_syn_true
    have h2 : 1 + matInfNorm Q_syn ≤ (W + 3) * M := by
      linarith only [hQ_syn_le, hM_ge_one]
    have h3 : (1 + matInfNorm Q_syn) * ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ))) ≤
        ((W + 3) * M) * ((18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) :=
      mul_le_mul h2 h2q_le (by positivity) (by positivity)
    have hsum :
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) + (W + 3) * (18 / 100 : ℝ)) ≤
        W + (18 / 100 : ℝ) * (K : ℝ) + 2 := by
      linarith only [hW_pos]
    have hprod_pos : 0 ≤ (2 : ℝ) ^ (-(pChild : ℤ)) * M := by positivity
    have h4 : matInfNorm (fun i1 k2 => Q_post i1 k2 - Q_post_true i1 k2) ≤
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) + (W + 3) * (18 / 100 : ℝ)) *
        ((2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
      linarith only [h1, h3, hQ_syn_sub]
    calc
      matInfNorm (fun i1 k2 => Q_post i1 k2 - Q_post_true i1 k2)
        ≤ (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * ((2 : ℝ) ^ (-(pChild : ℤ)) * M) :=
          h4.trans (mul_le_mul_of_nonneg_right hsum hprod_pos)
      _ = (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by ring
  have hQ_post_WM : vecInfNorm (Q_post v1) ≤ (W + 3) * M := by
    have hcoeff : (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 3 := by
      have hlin : W + (18 / 100 : ℝ) * (K : ℝ) + 2 ≤ 3 * ((pChild : ℝ) + 1) := by
        linarith only [hW_le, hK_le]
      calc
        (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (3 * ((pChild : ℝ) + 1)) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right hlin (le_of_lt h2p_pos)
        _ = 3 * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        _ ≤ 3 * 1 := by linarith only [hpow_le]
        _ = 3 := by ring
    have herr_le : matInfNorm (fun i1 k2 => Q_post i1 k2 - Q_post_true i1 k2) ≤ 3 * M :=
      hQ_post_sub.trans (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hM_pos))
    apply vecInfNorm_le _ (by positivity)
    intro k2
    have h1 := (norm_le_matInfNorm (fun j1 j2 => Q_post j1 j2 - Q_post_true j1 j2) v1 k2).trans herr_le
    have h2 := (norm_le_matInfNorm Q_post_true v1 k2).trans hQ_post_true_le
    have htri : ‖Q_post v1 k2‖ ≤ ‖Q_post v1 k2 - Q_post_true v1 k2‖ + ‖Q_post_true v1 k2‖ := by
      simpa using norm_add_le (Q_post v1 k2 - Q_post_true v1 k2) (Q_post_true v1 k2)
    linarith only [htri, h1, h2]
  have hM_le_pow : M ≤ (2 : ℝ) ^ B_in := by
    apply max_le (one_le_pow₀ (by norm_num)) hx
  have hW3_le_pow : W + 3 ≤ (2 : ℝ) ^ (Nat.clog 2 (2 * pChild + 4)) := by
    have h1 : W + 3 ≤ ((2 * pChild + 4 : ℕ) : ℝ) := by
      push_cast
      linarith only [hW_le]
    have h2 : 2 * pChild + 4 ≤ 2 ^ (Nat.clog 2 (2 * pChild + 4)) :=
      (Nat.clog_le_iff_le_pow (by norm_num)).mp le_rfl
    have h2r : ((2 * pChild + 4 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (2 * pChild + 4)) := by
      exact_mod_cast h2
    exact h1.trans h2r
  calc
    vecInfNorm (Q_post v1) ≤ (W + 3) * M := hQ_post_WM
    _ ≤ (2 : ℝ) ^ (Nat.clog 2 (2 * pChild + 4)) * (2 : ℝ) ^ B_in :=
      mul_le_mul hW3_le_pow hM_le_pow (le_of_lt hM_pos) (by positivity)
    _ = (2 : ℝ) ^ (childScheduleBIn K p B_in) := by
      unfold childScheduleBIn pChild
      rw [pow_add (2 : ℝ) B_in (Nat.clog 2 (2 * pChildEll K p + 4)), mul_comm]

/-- Schedule-driven multi-level `FastDFT` operator (`fastDFTRecursiveSched`): sizes `B_slot` in
Step 1 purely from the data-independent schedule parameter `B_in`
(`scheduleSlotBits K p B_in (m1Ell K p)`) without inspecting `vecInfNorm x` at runtime, and passes
`childScheduleBIn K p B_in` to the recursive child calls. -/
noncomputable def fastDFTRecursiveSched (K p B_in : ℕ)
    (x : Fin (2 ^ K) → ℂ) : Fin (2 ^ K) → FixedComplex (p + 2) :=
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let m1 := m1Ell K p
    let B_slot := scheduleSlotBits K p B_in m1
    have hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    have ht1_pos : 0 < t1 := t1Ell_pos K
    have hr_pos : 0 < r := rEll_pos K
    haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
    have hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => quantizeComplexFixed qChild (x j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixed t1 r m1 B_slot qChild qChild hr_pos U_gathered (levelFilterTapFixed K p)
    let U_spread : Fin t1 → Fin r → ℂ :=
      fun j1 k2 => (U_spreadFixed j1 k2).toComplex
    let U_pre : Fin t1 → Fin r → ℂ :=
      preTwistQuantRoots qChild U_spread
    let Q_syn : Fin t1 → Fin r → ℂ :=
      radix2SyntheticFFTQuant qChild (k1Ell K) c1 U_pre
    let Q_post : Fin t1 → Fin r → ℂ :=
      postTwistQuantRoots qChild Q_syn
    let Q_hat : Fin t1 → Fin r → ℂ :=
      fun v1 u2 =>
        (fastDFTRecursiveSched (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) (Q_post v1) u2).toComplex
    let Y_mat : Fin t1 → Fin r → ℂ :=
      oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hat
    let Z_mat : Fin t1 → Fin r → ℂ :=
      fun u1 u2 =>
        if u2.val = r / 2 then
          nyquistColumnSolveQuant qChild (passbandC0 K p u2) (fun m => Y_mat m u2) (nyquistModeSum K x) u1
        else
          cyclicBidiagPrevSolveQuant qChild (passbandC0 K p u2) (passbandC1 K p u2) (fun m => Y_mat m u2) u1
    fun u => quantizeComplexFixed (p + 2) (freqScatter t1 r hR_eq Z_mat u)
  else
    fun u => quantizeComplexFixed (p + 2) (baseRadix2FFTQuant K p x u)
termination_by K
decreasing_by
  unfold k2Ell
  omega

/-- **Exact Agreement Between `fastDFTRecursiveSched` and `fastDFTRecursive` Under Schedule Headroom
(`fastDFTRecursiveSched_eq_fastDFTRecursive`)**:
For every level `(K, p)` with `8 ≤ p` and every input `x : Fin (2 ^ K) → ℂ` satisfying
`vecInfNorm x ≤ (2 : ℝ) ^ B_in`, the data-independent schedule-sized operator
`fastDFTRecursiveSched K p B_in x` equals `fastDFTRecursive K p x` identically across all
recursive levels. -/
theorem fastDFTRecursiveSched_eq_fastDFTRecursive (K : ℕ) :
    ∀ (p B_in : ℕ) (_hp : 8 ≤ p) (x : Fin (2 ^ K) → ℂ) (_hx : vecInfNorm x ≤ (2 : ℝ) ^ B_in),
      fastDFTRecursiveSched K p B_in x = fastDFTRecursive K p x := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in hp x hx
    rw [fastDFTRecursiveSched, fastDFTRecursive]
    split_ifs with hcond
    · have hK2 : 2 ≤ K := hcond.2
      have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      have hpChild : 8 ≤ pChildEll K p := by unfold pChildEll pWorkEll; omega
      have hstep1_sched := fastDFTRecursiveSched_step1_eq_refMatrixSpreadFixed K p B_in x hx
      have hstep1_orig := fastDFTRecursive_step1_eq_refMatrixSpreadFixed K p x
      dsimp only at hstep1_sched hstep1_orig ⊢
      rw [hstep1_sched, hstep1_orig]
      have hQ_norm := vecInfNorm_fastDFTRecursive_Q_post_le hp x hx
      dsimp only at hQ_norm
      have hQ_hat :
          (fun (v1 : Fin (t1Ell K)) (u2 : Fin (rEll K)) =>
            (fastDFTRecursiveSched (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
              (postTwistQuantRoots (qChildEll K p)
                (radix2SyntheticFFTQuant (qChildEll K p) (k1Ell K) (c1Ell K)
                  (preTwistQuantRoots (qChildEll K p) fun j1 k2 =>
                    (refMatrixSpreadFixed (t1Ell K) (rEll K) (m1Ell K p) (qChildEll K p)
                      (qChildEll K p) (rEll_pos K)
                      (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K) fun j =>
                        quantizeComplexFixed (qChildEll K p) (x j))
                      (levelFilterTapFixed K p) j1 k2).toComplex)) v1) u2).toComplex) =
          (fun (v1 : Fin (t1Ell K)) (u2 : Fin (rEll K)) =>
            (fastDFTRecursive (k2Ell K) (pChildEll K p)
              (postTwistQuantRoots (qChildEll K p)
                (radix2SyntheticFFTQuant (qChildEll K p) (k1Ell K) (c1Ell K)
                  (preTwistQuantRoots (qChildEll K p) fun j1 k2 =>
                    (refMatrixSpreadFixed (t1Ell K) (rEll K) (m1Ell K p) (qChildEll K p)
                      (qChildEll K p) (rEll_pos K)
                      (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K) fun j =>
                        quantizeComplexFixed (qChildEll K p) (x j))
                      (levelFilterTapFixed K p) j1 k2).toComplex)) v1) u2).toComplex) := by
        funext v1 u2
        exact congrArg FixedComplex.toComplex
          (congrFun (ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in) hpChild _ (hQ_norm v1)) u2)
      funext u
      congr 1
      unfold freqScatter
      dsimp only
      split_ifs
      · congr 1
        funext m
        exact congrFun (congrFun (congrArg (oddColScatter (t1Ell_pos K) ⟨k1Ell K, rfl⟩) hQ_hat) m) _
      · congr 1
        funext m
        exact congrFun (congrFun (congrArg (oddColScatter (t1Ell_pos K) ⟨k1Ell K, rfl⟩) hQ_hat) m) _
    · rfl

/-- **Unconditional Multi-Level `fastDFTRecursiveSched` Accuracy Theorem
(`vecInfNorm_fastDFTRecursiveSched_sub_normDFT1D_le`, Lemma 6.5(2) (`lem:forward`),
equation (36) (`eq:inductive-bound`))**:
For every input size $n \in \mathbb{N}$, recursion level $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$,
schedule headroom $B_{\text{in}} \in \mathbb{N}$, and input $x : \text{Fin}(2^{K_\ell}) \to \mathbb{C}$
with $\|x\|_\infty \le 2^{B_{\text{in}}}$, `fastDFTRecursiveSched` satisfies the multi-level
error schedule bound `concreteLevelError (rootK0 n) (rootP0 n) ell * max 1 (vecInfNorm x)`. -/
theorem vecInfNorm_fastDFTRecursiveSched_sub_normDFT1D_le (n ell B_in : ℕ)
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n))
    (x : Fin (2 ^ levelK (rootK0 n) ell) → ℂ) (hx : vecInfNorm x ≤ (2 : ℝ) ^ B_in) :
    vecInfNorm (fun u =>
      (fastDFTRecursiveSched (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) B_in x u).toComplex -
        normDFT1D x u) ≤
      concreteLevelError (rootK0 n) (rootP0 n) ell * max 1 (vecInfNorm x) := by
  have hp : 8 ≤ levelP (rootK0 n) (rootP0 n) ell := by
    have h1 := rootP0_ge_eighteen n
    have h2 := levelP_ge_p0 (rootK0 n) (rootP0 n) ell
    omega
  rw [fastDFTRecursiveSched_eq_fastDFTRecursive (levelK (rootK0 n) ell)
    (levelP (rootK0 n) (rootP0 n) ell) B_in hp x hx]
  exact vecInfNorm_fastDFTRecursive_sub_normDFT1D_le n ell hell x

/-- Schedule-driven 2-call complex-packed `fastDFTRecursiveSched` cyclic convolution at root
schedule headroom `B_root = levelScheduleBIn (rootK0 n) (rootP0 n) 0 = 2` via pointwise complex
squaring `(Z u * Z u) / (2 * Complex.I)` (Lemma 3.4 (`lem:two-call`) and Section 7.1 (`sec:alg-spec`)). -/
noncomputable def fastTwoCallDFTConvSched (n A B : ℕ) (k : Fin (rootR0 n)) : ℂ :=
  let K0 := rootK0 n
  let p0 := rootP0 n
  let R0 := rootR0 n
  let b := chunkBits n
  let B0 := levelScheduleBIn K0 p0 0
  let aVec : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let bVec : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let zVec : Fin R0 → ℂ := packRealComplex aVec bVec
  let Z : Fin R0 → ℂ := fun u => (fastDFTRecursiveSched K0 p0 B0 zVec u).toComplex
  let W_conj : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
  let C_inv : Fin R0 → ℂ := fun m => starRingEnd ℂ ((fastDFTRecursiveSched K0 p0 B0 W_conj m).toComplex)
  ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) * C_inv k))

/-- Product reconstruction via the schedule-driven 2-call `fastDFTRecursiveSched` convolution
(Section 7.1 (`sec:alg-spec`) and Theorem 1 (`thm:main`) in Section 7.2 (`sec:cost-proof`)). -/
noncomputable def reconstructProductViaScheduleFastDFT (n A B : ℕ) : ℕ :=
  ∑ k : Fin (rootR0 n),
    ⌊(fastTwoCallDFTConvSched n A B k).re + (1 / 2 : ℝ)⌋.toNat * 2 ^ (k.val * chunkBits n)

/-- Exact equality between `fastTwoCallDFTConvSched` and `fastTwoCallDFTConv` for all `n, A, B`. -/
theorem fastTwoCallDFTConvSched_eq_fastTwoCallDFTConv (n A B : ℕ) (k : Fin (rootR0 n)) :
    fastTwoCallDFTConvSched n A B k = fastTwoCallDFTConv n A B k := by
  let K0 := rootK0 n
  let p0 := rootP0 n
  let R0 := rootR0 n
  let b := chunkBits n
  let aVec : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let bVec : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let zVec : Fin R0 → ℂ := packRealComplex aVec bVec
  have hp0_ge18 : 18 ≤ p0 := rootP0_ge_eighteen n
  have hp0 : 8 ≤ p0 := by omega
  have h2p0_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p0 : ℤ)) := zpow_pos (by norm_num) _
  have h2p0_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (1 / 16 : ℝ) := by
    calc
      (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (2 : ℝ) ^ (-4 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have ha_le : ∀ j : Fin R0, ‖(aVec j : ℂ)‖ ≤ 1 := by
    intro j
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlt : (natChunk b A j.val : ℝ) ≤ (2 : ℝ) ^ b := by
      exact_mod_cast le_of_lt (natChunk_lt b A j.val)
    calc
      (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ)) :=
          mul_le_mul_of_nonneg_right hlt (le_of_lt (zpow_pos (by norm_num) _))
      _ = 1 := two_pow_mul_two_zpow_neg b
  have hb_le : ∀ j : Fin R0, ‖(bVec j : ℂ)‖ ≤ 1 := by
    intro j
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlt : (natChunk b B j.val : ℝ) ≤ (2 : ℝ) ^ b := by
      exact_mod_cast le_of_lt (natChunk_lt b B j.val)
    calc
      (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ)) :=
          mul_le_mul_of_nonneg_right hlt (le_of_lt (zpow_pos (by norm_num) _))
      _ = 1 := two_pow_mul_two_zpow_neg b
  have hz_sqrt2 : vecInfNorm zVec ≤ Real.sqrt 2 := by
    apply vecInfNorm_le zVec (by positivity)
    intro j
    have hre : |(zVec j).re| ≤ 1 := by simpa [zVec, packRealComplex, Complex.norm_real] using ha_le j
    have him : |(zVec j).im| ≤ 1 := by simpa [zVec, packRealComplex, Complex.norm_real] using hb_le j
    simpa using norm_complex_le_of_re_im_le zero_le_one hre him
  have hz_le2 : vecInfNorm zVec ≤ 2 :=
    hz_sqrt2.trans (sqrt_two_le.trans (by norm_num))
  have hz_le : vecInfNorm zVec ≤ (2 : ℝ) ^ (levelScheduleBIn K0 p0 0) :=
    hz_le2.trans (by norm_num [levelScheduleBIn])
  have hcall1 : fastDFTRecursiveSched K0 p0 (levelScheduleBIn K0 p0 0) zVec =
      fastDFTRecursive K0 p0 zVec :=
    fastDFTRecursiveSched_eq_fastDFTRecursive K0 p0 (levelScheduleBIn K0 p0 0) hp0 zVec hz_le
  let Z : Fin R0 → ℂ := fun u => (fastDFTRecursive K0 p0 zVec u).toComplex
  let Z_true : Fin R0 → ℂ := normDFT1D zVec
  let W_conj : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
  let W_true : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ ((Z_true u * Z_true u) / (2 * Complex.I))
  have hz_max : max 1 (vecInfNorm zVec) ≤ 2 :=
    max_le (by norm_num) hz_le2
  have hZ_err : ∀ u : Fin R0, ‖Z u - Z_true u‖ ≤ 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    intro u
    have h1 := norm_le_vecInfNorm (fun v => Z v - Z_true v) u
    have h2 := vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_two_zpow n 0 (Nat.zero_le _) zVec
    calc
      ‖Z u - Z_true u‖ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm zVec) := h1.trans h2
      _ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * 2 := mul_le_mul_of_nonneg_left hz_max (le_of_lt h2p0_pos)
      _ = 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by ring
  have hZ_true_le : ∀ u : Fin R0, ‖Z_true u‖ ≤ Real.sqrt 2 :=
    fun u => (norm_normDFT1D_le zVec u).trans hz_sqrt2
  have hWt_le : ∀ u : Fin R0, ‖W_true u‖ ≤ 1 := by
    intro u
    unfold W_true
    rw [RCLike.norm_conj, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    have hsq : ‖Z_true u‖ * ‖Z_true u‖ ≤ 2 := by
      calc
        ‖Z_true u‖ * ‖Z_true u‖ ≤ Real.sqrt 2 * Real.sqrt 2 :=
          mul_self_le_mul_self (norm_nonneg _) (hZ_true_le u)
        _ = 2 := Real.mul_self_sqrt (by norm_num)
    linarith
  have hW_err : ∀ u : Fin R0, ‖W_conj u - W_true u‖ ≤ (11 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    intro u
    unfold W_conj W_true
    rw [← map_sub, RCLike.norm_conj]
    have hZt_144 : ‖Z_true u‖ ≤ 72 / 50 := (hZ_true_le u).trans sqrt_two_le
    have hZ_sum : ‖Z u + Z_true u‖ ≤ 5 := by
      have h1 := norm_add_le (Z u - Z_true u) (Z_true u + Z_true u)
      have h2 := norm_add_le (Z_true u) (Z_true u)
      have heq : (Z u - Z_true u) + (Z_true u + Z_true u) = Z u + Z_true u := by ring
      rw [heq] at h1
      linarith [hZ_err u, hZt_144, h2p0_le]
    have hprod_sub : (Z u * Z u) / (2 * Complex.I) - (Z_true u * Z_true u) / (2 * Complex.I) =
        ((Z u + Z_true u) * (Z u - Z_true u)) / (2 * Complex.I) := by ring
    have hprod_err :
        ‖(Z u * Z u) / (2 * Complex.I) - (Z_true u * Z_true u) / (2 * Complex.I)‖ ≤
          5 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      rw [hprod_sub, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      have hm : ‖Z u + Z_true u‖ * ‖Z u - Z_true u‖ ≤ 5 * (2 * (2 : ℝ) ^ (-(p0 : ℤ))) :=
        mul_le_mul hZ_sum (hZ_err u) (norm_nonneg _) (by norm_num)
      linarith
    have hq_err :
        ‖quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)) -
          (Z u * Z u) / (2 * Complex.I)‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      have hq := norm_quantizeComplex_sub_self_le (p0 + 2) ((Z u * Z u) / (2 * Complex.I))
      have hexp : -((p0 + 2 : ℕ) : ℤ) = -(p0 : ℤ) + (-2 : ℤ) := by omega
      have hpow : (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
        rw [hexp, zpow_add₀ (by norm_num)]
        norm_num
        ring
      rw [hpow] at hq
      have hsqrt := sqrt_two_le
      nlinarith only [hq, hsqrt, h2p0_pos]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
      ((Z u * Z u) / (2 * Complex.I))
      ((Z_true u * Z_true u) / (2 * Complex.I))
    linarith
  have hW_le : vecInfNorm W_conj ≤ (2 : ℝ) ^ (levelScheduleBIn K0 p0 0) := by
    change vecInfNorm W_conj ≤ (2 : ℝ) ^ 2
    apply vecInfNorm_le W_conj (by norm_num)
    intro u
    have htri := norm_add_le (W_conj u - W_true u) (W_true u)
    rw [sub_add_cancel] at htri
    linarith [hW_err u, hWt_le u, h2p0_le]
  have hcall2 : fastDFTRecursiveSched K0 p0 (levelScheduleBIn K0 p0 0) W_conj =
      fastDFTRecursive K0 p0 W_conj :=
    fastDFTRecursiveSched_eq_fastDFTRecursive K0 p0 (levelScheduleBIn K0 p0 0) hp0 W_conj hW_le
  unfold fastTwoCallDFTConvSched fastTwoCallDFTConv
  dsimp only
  rw [hcall1, hcall2]

/-- **Unconditional Bit-Exactness of `reconstructProductViaScheduleFastDFT`
(`reconstructProductViaScheduleFastDFT_eq_mul`, Theorem 1 (`thm:main`) and Theorem 2 (`thm:lean`))**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, the schedule-driven 2-call
`fastDFTRecursiveSched` convolution and carry-propagation reconstruction
`reconstructProductViaScheduleFastDFT n A B` (where every Kronecker slot width `B_slot` is sized
purely from the data-independent schedule `levelScheduleBIn`) equals `A * B` bit-exactly. -/
@[simp]
theorem reconstructProductViaScheduleFastDFT_eq_mul (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    reconstructProductViaScheduleFastDFT n A B = A * B := by
  unfold reconstructProductViaScheduleFastDFT
  simp_rw [fastTwoCallDFTConvSched_eq_fastTwoCallDFTConv]
  exact reconstructProductViaFastDFT_eq_mul n A B hA hB

/-! ### 2.6 Stage 6: Fixed-Point Rescaling & Rounding Bridges (`FixedComplex.rescale`, `FixedComplex.halfRounded`) -/

@[simp]
theorem quantizeRealMantissa_mul_two_zpow_neg (q : ℕ) (m : ℤ) :
    quantizeRealMantissa q ((m : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) = m := by
  unfold quantizeRealMantissa
  have hmul : (m : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q = (m : ℝ) := by
    rw [mul_assoc, mul_comm ((2 : ℝ) ^ (-(q : ℤ))), two_pow_mul_two_zpow_neg, mul_one]
  rw [hmul]
  exact floor_add_half_eq_of_abs_sub_lt_half (M := m) (by simp)

@[simp]
theorem quantizeComplexFixed_toComplex (q : ℕ) (z : FixedComplex q) :
    quantizeComplexFixed q z.toComplex = z := by
  ext
  · change quantizeRealMantissa q z.toComplex.re = z.re
    rw [FixedComplex.toComplex_re]
    exact quantizeRealMantissa_mul_two_zpow_neg q z.re
  · change quantizeRealMantissa q z.toComplex.im = z.im
    rw [FixedComplex.toComplex_im]
    exact quantizeRealMantissa_mul_two_zpow_neg q z.im

@[simp]
theorem quantizeComplex_toComplex (q : ℕ) (z : FixedComplex q) :
    quantizeComplex q z.toComplex = z.toComplex := by
  unfold quantizeComplex
  rw [quantizeComplexFixed_toComplex]

@[simp]
theorem quantizeComplexFixed_quantizeComplex (q : ℕ) (z : ℂ) :
    quantizeComplexFixed q (quantizeComplex q z) = quantizeComplexFixed q z :=
  quantizeComplexFixed_toComplex q (quantizeComplexFixed q z)

theorem roundShiftInt_mul_two_pow_sub_eq_quantizeRealMantissa (q1 q2 : ℕ) (m : ℤ) :
    roundShiftInt (m * (2 : ℤ) ^ (q2 - q1)) (q1 - q2) =
      quantizeRealMantissa q2 ((m : ℝ) * (2 : ℝ) ^ (-(q1 : ℤ))) := by
  rw [roundShiftInt_eq_quantizeRealMantissa]
  unfold quantizeRealMantissa
  congr 2
  rcases le_or_gt q1 q2 with hle | hlt
  · have hsub0 : q1 - q2 = 0 := Nat.sub_eq_zero_of_le hle
    have hadd : (q2 - q1) + q1 = q2 := Nat.sub_add_cancel hle
    rw [hsub0, pow_zero, div_one]
    push_cast
    have hpow : (2 : ℝ) ^ q2 = (2 : ℝ) ^ (q2 - q1) * (2 : ℝ) ^ q1 := by
      rw [← pow_add, hadd]
    rw [hpow]
    calc
      (m : ℝ) * (2 : ℝ) ^ (q2 - q1)
        = (m : ℝ) * (2 : ℝ) ^ (q2 - q1) * ((2 : ℝ) ^ q1 * (2 : ℝ) ^ (-(q1 : ℤ))) := by
          rw [two_pow_mul_two_zpow_neg, mul_one]
      _ = (m : ℝ) * (2 : ℝ) ^ (-(q1 : ℤ)) * ((2 : ℝ) ^ (q2 - q1) * (2 : ℝ) ^ q1) := by ring
  · have hsub0 : q2 - q1 = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
    have hadd : (q1 - q2) + q2 = q1 := Nat.sub_add_cancel (le_of_lt hlt)
    rw [hsub0, pow_zero, mul_one]
    have hpow : (2 : ℝ) ^ (-(q1 : ℤ)) * (2 : ℝ) ^ q2 = ((2 : ℝ) ^ (q1 - q2))⁻¹ := by
      have h1 : (2 : ℝ) ^ q1 * (2 : ℝ) ^ (-(q1 : ℤ)) = 1 := two_pow_mul_two_zpow_neg q1
      have h2 : (2 : ℝ) ^ q1 = (2 : ℝ) ^ (q1 - q2) * (2 : ℝ) ^ q2 := by
        rw [← pow_add, hadd]
      have h3 : (2 : ℝ) ^ (q1 - q2) ≠ 0 := by positivity
      rw [h2] at h1
      apply mul_left_cancel₀ h3
      rw [mul_inv_cancel₀ h3]
      linarith
    rw [div_eq_mul_inv, mul_assoc, hpow]

@[simp]
theorem FixedComplex.rescale_eq_quantizeComplexFixed {q1 : ℕ} (q2 : ℕ) (z : FixedComplex q1) :
    FixedComplex.rescale q2 z = quantizeComplexFixed q2 z.toComplex := by
  ext <;> simp [FixedComplex.rescale, quantizeComplexFixed,
    roundShiftInt_mul_two_pow_sub_eq_quantizeRealMantissa]

@[simp]
theorem FixedComplex.toComplex_rescale {q1 : ℕ} (q2 : ℕ) (z : FixedComplex q1) :
    (FixedComplex.rescale q2 z).toComplex = quantizeComplex q2 z.toComplex := by
  rw [FixedComplex.rescale_eq_quantizeComplexFixed, quantizeComplex]

@[simp]
theorem FixedComplex.toComplex_halfRounded {q : ℕ} (z : FixedComplex q) :
    (FixedComplex.halfRounded z).toComplex = quantizeComplex q (z.toComplex / 2) := by
  have hre : roundShiftInt z.re 1 = quantizeRealMantissa q (z.toComplex / 2).re := by
    rw [roundShiftInt_eq_quantizeRealMantissa]
    unfold quantizeRealMantissa
    congr 2
    simp only [Complex.div_ofNat_re, FixedComplex.toComplex_re]
    have hcancel : (2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q = 1 := by
      rw [mul_comm, two_pow_mul_two_zpow_neg]
    calc
      (z.re : ℝ) / (2 : ℝ) ^ 1 = ((z.re : ℝ) / 2) * ((2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q) := by
        rw [hcancel, pow_one, mul_one]
      _ = (z.re : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) / 2 * (2 : ℝ) ^ q := by ring
  have him : roundShiftInt z.im 1 = quantizeRealMantissa q (z.toComplex / 2).im := by
    rw [roundShiftInt_eq_quantizeRealMantissa]
    unfold quantizeRealMantissa
    congr 2
    simp only [Complex.div_ofNat_im, FixedComplex.toComplex_im]
    have hcancel : (2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q = 1 := by
      rw [mul_comm, two_pow_mul_two_zpow_neg]
    calc
      (z.im : ℝ) / (2 : ℝ) ^ 1 = ((z.im : ℝ) / 2) * ((2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q) := by
        rw [hcancel, pow_one, mul_one]
      _ = (z.im : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) / 2 * (2 : ℝ) ^ q := by ring
  unfold quantizeComplex
  congr 1
  ext <;> simp [FixedComplex.halfRounded, quantizeComplexFixed, hre, him]

end IntMul

#print axioms IntMul.decodeScheduleBits_encodeScheduleBits
#print axioms IntMul.decodeScheduleRecursionDepth_encodeScheduleBits
#print axioms IntMul.decodeFullScheduleTable_encodeFullScheduleTable
#print axioms IntMul.unpackInputChunks_encodeInputBits
#print axioms IntMul.wordWidthBounds_packChunksFixed
#print axioms IntMul.fitsSignedWord_levelFilterTapFixed
#print axioms IntMul.freqScatter_freqFin
#print axioms IntMul.wordWidthBounds_quantizeComplexFixed_levelBIn
#print axioms IntMul.passbandC0_passbandC1_max_ge
#print axioms IntMul.passbandC0_passbandC1_stopband_lt
#print axioms IntMul.passbandC0_passbandC1_prevSolve_spec
#print axioms IntMul.passbandC0_passbandC1_prev_conditioning_le_236_t1
#print axioms IntMul.passbandC0_passbandC1_prevSolveQuant_sub_le
#print axioms IntMul.passbandC0_nyquist_conditioning_le_236_t1
#print axioms IntMul.fastDFTRecursive_step1_eq_refMatrixSpreadFixed
#print axioms IntMul.level_concretePoissonResidual_twoMode_le
#print axioms IntMul.multiLevel_concreteError_le
#print axioms IntMul.root_concreteError_le
#print axioms IntMul.vecInfNorm_fastDFTRecursive_sub_normDFT1D_le
#print axioms IntMul.vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_two_zpow
#print axioms IntMul.vecInfNorm_fastDFTRecursive_sub_normDFT1D_le_of_levelError
#print axioms IntMul.root_conv_error_budget_eq_one_eighth
#print axioms IntMul.root_conv_recovery_of_fastDFT_approx
#print axioms IntMul.twoCallDFTConv_eq_linearConvCoeff
#print axioms IntMul.round_twoCallDFTConv_eq_linearConvCoeff
#print axioms IntMul.reconstructProductFromChunks_eq_mul
#print axioms IntMul.reconstructProductViaFastDFT_eq_mul_of_root_approx
#print axioms IntMul.fastTwoCallDFTConv_sub_linearConvCoeff_le
#print axioms IntMul.round_fastTwoCallDFTConv_eq_linearConvCoeff
#print axioms IntMul.reconstructProductViaFastDFT_eq_mul
#print axioms IntMul.reconstructProductViaTwoCallDFT_eq_mul
#print axioms IntMul.mul_lt_two_pow_two_mul
#print axioms IntMul.vecInfNorm_fastDFTRecursive_Q_post_le
#print axioms IntMul.fastDFTRecursiveSched_eq_fastDFTRecursive
#print axioms IntMul.vecInfNorm_fastDFTRecursiveSched_sub_normDFT1D_le
#print axioms IntMul.reconstructProductViaScheduleFastDFT_eq_mul
