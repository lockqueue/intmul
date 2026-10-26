import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Core Definitions, Parameter Schedule (`cSpec`), and Fixed-Point Representation (`IntMul.Defs`)

This module provides the foundational definitions shared across all components of the
windowed sinc-Gaussian fractional-shift integer multiplication formalization (using the
polynomial transform, `syntheticFFT` in this development):
1. Data-independent schedule parameters `cSpec(n)` and per-level recursion parameters
   (Section 6.3 (`sec:forward-error`), schedule (34) (`eq:cert-sched`), Section 7.1 (`sec:alg-spec`)).
2. Deterministic fixed-point real and complex representations at fractional bit-precision `q`
   (Section 3.2 (`sec:prelim-model`), Definition 3.1 (`def:grid`)).
3. Signed word-width predicates `FitsSignedWord` and `WordWidthBounds`
   (Section 3.2 (`sec:prelim-model`)).
4. Canonical bit-list encodings `encodeNatBits`, `decodeNatBits`, and `encodeInputBits`
   (`bits A ‖ bits B`, Section 8 (`sec:lean`)).
-/

namespace IntMul

/-! ## 1. Data-Independent Schedule Parameters (`cSpec`) -/

/-- Root chunk bit-width $b = \max(4, \lfloor \log_2 n \rfloor)$ (Section 3.1 (`sec:notation`), Table 2 (`tab:notation`), Section 7.1 (`sec:alg-spec`)). -/
def chunkBits (n : ℕ) : ℕ :=
  max 4 (Nat.log 2 n)

/-- Number of chunks $N = \lceil n / b \rceil$ (Table 2 (`tab:notation`), Section 7.1 (`sec:alg-spec`)). -/
def numChunks (n : ℕ) : ℕ :=
  (n + chunkBits n - 1) / chunkBits n

/-- Log-length $K_0 = \lceil \log_2(2N) \rceil$ of the root transform (Table 2 (`tab:notation`), Section 7.1 (`sec:alg-spec`)). -/
def rootK0 (n : ℕ) : ℕ :=
  max 2 (Nat.clog 2 (2 * max 1 (numChunks n)))

/-- Root transform length $R_0 = 2^{K_0} \ge 2N$ (Table 2 (`tab:notation`), Section 7.1 (`sec:alg-spec`)). -/
def rootR0 (n : ℕ) : ℕ :=
  2 ^ rootK0 n

/-- Root target precision $p_0 = 2b + 2K_0 + 6$ (Table 2 (`tab:notation`), Section 7.1 (`sec:alg-spec`)). -/
def rootP0 (n : ℕ) : ℕ :=
  2 * chunkBits n + 2 * rootK0 n + 6

/-- Complete data-independent root specification derived solely from $n$ (Section 7.1 (`sec:alg-spec`), Table 3 (`tab:lean-map`)). -/
structure RootSpec where
  /-- Input bit-length $n$. -/
  n : ℕ
  /-- Chunk bit-width $b$. -/
  b : ℕ
  /-- Number of base-$2^b$ chunks $N$. -/
  N : ℕ
  /-- Root log-length $K_0$. -/
  K0 : ℕ
  /-- Root transform length $R_0 = 2^{K_0}$. -/
  R0 : ℕ
  /-- Root precision $p_0 = 2b + 2K_0 + 6$. -/
  p0 : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Canonical schedule constructor `cSpec n` as a function of $n$ only (Section 7.1 (`sec:alg-spec`), Table 3 (`tab:lean-map`)). -/
def cSpec (n : ℕ) : RootSpec where
  n := n
  b := chunkBits n
  N := numChunks n
  K0 := rootK0 n
  R0 := rootR0 n
  p0 := rootP0 n

/-- First-axis log-dimension $k_{1,\ell} = \lfloor K_\ell / 2 \rfloor$ (Section 3.5 (`sec:prelim-dft`), Section 7.1 (`sec:alg-spec`)). -/
def k1Ell (K : ℕ) : ℕ := K / 2

/-- Second-axis log-dimension $k_{2,\ell} = \lceil K_\ell / 2 \rceil$ (Section 3.5 (`sec:prelim-dft`), Section 7.1 (`sec:alg-spec`)). -/
def k2Ell (K : ℕ) : ℕ := (K + 1) / 2

/-- First-axis transform dimension $t_{1,\ell} = 2^{\lfloor K_\ell / 2 \rfloor}$ (Section 3.5 (`sec:prelim-dft`), Section 7.1 (`sec:alg-spec`)). -/
def t1Ell (K : ℕ) : ℕ := 2 ^ k1Ell K

/-- Second-axis (recursive) transform dimension $r_\ell = 2^{\lceil K_\ell / 2 \rceil}$ (Section 3.5 (`sec:prelim-dft`), Section 7.1 (`sec:alg-spec`)). -/
def rEll (K : ℕ) : ℕ := 2 ^ k2Ell K

/-- Polynomial-transform step ratio $c_{1,\ell} = r_\ell / t_{1,\ell} \in \{1, 2\}$ (written $\nu_\ell$ in Section 3.5 (`sec:prelim-dft`)). -/
def c1Ell (K : ℕ) : ℕ := rEll K / t1Ell K

/-- Working cutoff precision $p_{\text{work},\ell} = p_\ell + K_\ell + 6$ (Lemma 6.5 (`lem:forward`), schedule (34) (`eq:cert-sched`)). -/
def pWorkEll (K p : ℕ) : ℕ := p + K + 6

/-- Purely additive child precision $p_{\ell+1} = p_{\text{work},\ell} + K_\ell + 6 = p_\ell + 2K_\ell + 12$ (Lemma 6.5 (`lem:forward`), schedule (34) (`eq:cert-sched`)). -/
def pChildEll (K p : ℕ) : ℕ := pWorkEll K p + K + 6

/-- Child fixed-point quantization fractional bits $q_{\text{child},\ell} = p_{\ell+1} + 2$ (Lemma 6.5 (`lem:forward`), schedule (34) (`eq:cert-sched`)). -/
def qChildEll (K p : ℕ) : ℕ := pChildEll K p + 2

/-- Base-case stopping predicate $R_\ell \le 4 p_\ell^2$ (Lemma 6.5(2) (`lem:forward`), Section 7.1 (`sec:alg-spec`)). -/
def isBaseLeaf (K p : ℕ) : Bool :=
  decide (2 ^ K ≤ 4 * p * p)

/-- Log-length $K_\ell$ at recursion depth $\ell$ starting from $K_0$. -/
def levelK (K0 : ℕ) : ℕ → ℕ
  | 0 => K0
  | ell + 1 => k2Ell (levelK K0 ell)

/-- Transform length $R_\ell = 2^{K_\ell}$ at recursion depth $\ell$. -/
def levelR (K0 ell : ℕ) : ℕ :=
  2 ^ levelK K0 ell

/-- Target precision $p_\ell$ at recursion depth $\ell$ under the additive schedule $p_{\ell+1} = p_\ell + 2K_\ell + 12$. -/
def levelP (K0 p0 : ℕ) : ℕ → ℕ
  | 0 => p0
  | ell + 1 => pChildEll (levelK K0 ell) (levelP K0 p0 ell)

/-! ## 2. Fixed-Point Complex Arithmetic and Quantization (Section 3.2 (`sec:prelim-model`)) -/

/-- A fixed-point complex number in $\tilde{\mathbb{C}}_q = 2^{-q} \mathbb{Z}[i]$ stored as integer
real and imaginary mantissas `(re, im)` (Definition 3.1 (`def:grid`), Section 3.2 (`sec:prelim-model`)). -/
@[ext]
structure FixedComplex (q : ℕ) where
  /-- Signed integer mantissa of the real part (scaled by $2^q$). -/
  re : ℤ
  /-- Signed integer mantissa of the imaginary part (scaled by $2^q$). -/
  im : ℤ
  deriving DecidableEq, Repr, Inhabited

namespace FixedComplex

/-- Exact complex value $2^{-q}(\text{re} + i \cdot \text{im}) \in \mathbb{C}$ of a `FixedComplex q`. -/
noncomputable def toComplex {q : ℕ} (z : FixedComplex q) : ℂ :=
  (((z.re : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) : ℝ) : ℂ) +
    (((z.im : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) : ℝ) : ℂ) * Complex.I

/-- Complex conjugate in $\tilde{\mathbb{C}}_q$. -/
def conj {q : ℕ} (z : FixedComplex q) : FixedComplex q :=
  ⟨z.re, -z.im⟩

/-- Addition in $\tilde{\mathbb{C}}_q$. -/
def add {q : ℕ} (z w : FixedComplex q) : FixedComplex q :=
  ⟨z.re + w.re, z.im + w.im⟩

/-- Subtraction in $\tilde{\mathbb{C}}_q$. -/
def sub {q : ℕ} (z w : FixedComplex q) : FixedComplex q :=
  ⟨z.re - w.re, z.im - w.im⟩

/-- Negation in $\tilde{\mathbb{C}}_q$. -/
def neg {q : ℕ} (z : FixedComplex q) : FixedComplex q :=
  ⟨-z.re, -z.im⟩

instance {q : ℕ} : Add (FixedComplex q) := ⟨add⟩
instance {q : ℕ} : Sub (FixedComplex q) := ⟨sub⟩
instance {q : ℕ} : Neg (FixedComplex q) := ⟨neg⟩
instance {q : ℕ} : Zero (FixedComplex q) := ⟨⟨0, 0⟩⟩

end FixedComplex

/-- Deterministic floor-shifted integer right-shift $\lfloor m / 2^k + 1/2 \rfloor = (m + 2^{k-1}) / 2^k$
(Definition 3.1 (`def:grid`), Section 8 (`sec:lean`)). -/
def roundShiftInt (m : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then m else (m + (2 : ℤ) ^ (k - 1)) / (2 : ℤ) ^ k

namespace FixedComplex

/-- Pure-integer division by 2 with round-half-up in `FixedComplex q`. -/
def halfRounded {q : ℕ} (z : FixedComplex q) : FixedComplex q :=
  ⟨roundShiftInt z.re 1, roundShiftInt z.im 1⟩

/-- Pure-integer fixed-point precision rescaling from `FixedComplex q1` to `FixedComplex q2`
via shift and round-half-up (`roundShiftInt`). -/
def rescale {q1 : ℕ} (q2 : ℕ) (z : FixedComplex q1) : FixedComplex q2 :=
  ⟨roundShiftInt (z.re * (2 : ℤ) ^ (q2 - q1)) (q1 - q2),
   roundShiftInt (z.im * (2 : ℤ) ^ (q2 - q1)) (q1 - q2)⟩

end FixedComplex

/-- Base-$2^b$ chunk $a_i = \lfloor A / 2^{i b} \rfloor \bmod 2^b \in [0, 2^b - 1]$ (Section 7.1 (`sec:alg-spec`)). -/
def natChunk (b A i : ℕ) : ℕ :=
  (A / (2 ^ b) ^ i) % 2 ^ b

/-- Deterministic floor-shifted quantization mantissa $\lfloor 2^q x + 1/2 \rfloor \in \mathbb{Z}$
(Definition 3.1 (`def:grid`), Section 3.2 (`sec:prelim-model`)). -/
noncomputable def quantizeRealMantissa (q : ℕ) (x : ℝ) : ℤ :=
  ⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋

/-- Deterministic quantization of a real number $x \in \mathbb{R}$ to $q$ fractional bits:
$2^{-q} \lfloor 2^q x + 1/2 \rfloor$ (Definition 3.1 (`def:grid`), Section 3.2 (`sec:prelim-model`)). -/
noncomputable def quantizeReal (q : ℕ) (x : ℝ) : ℝ :=
  (quantizeRealMantissa q x : ℝ) * (2 : ℝ) ^ (-(q : ℤ))

/-- Deterministic quantization of $z \in \mathbb{C}$ into `FixedComplex q` (Definition 3.1 (`def:grid`), Section 3.2 (`sec:prelim-model`)). -/
noncomputable def quantizeComplexFixed (q : ℕ) (z : ℂ) : FixedComplex q :=
  ⟨quantizeRealMantissa q z.re, quantizeRealMantissa q z.im⟩

/-- Deterministic quantization of $z \in \mathbb{C}$ to its nearest grid point in $\tilde{\mathbb{C}}_q \subset \mathbb{C}$ (Definition 3.1 (`def:grid`), Section 3.2 (`sec:prelim-model`)). -/
noncomputable def quantizeComplex (q : ℕ) (z : ℂ) : ℂ :=
  (quantizeComplexFixed q z).toComplex

/-! ## 3. Signed Word Width Bounds (Section 3.2 (`sec:prelim-model`)) -/

/-- Predicate asserting that a signed integer mantissa `m` fits within `w` magnitude bits (`|m| < 2^w`). -/
def FitsSignedWord (w : ℕ) (m : ℤ) : Prop :=
  |m| < (2 : ℤ) ^ w

/-- Predicate asserting that both mantissas of `z : FixedComplex q` fit within `w` magnitude bits. -/
def WordWidthBounds (w : ℕ) {q : ℕ} (z : FixedComplex q) : Prop :=
  FitsSignedWord w z.re ∧ FitsSignedWord w z.im

/-! ## 4. Shared Harmonic Analysis & Norm Definitions (Section 3.1 (`sec:notation`), Section 3.5 (`sec:prelim-dft`), Section 5.1 (`sec:deconv-thm`), Section 6.1 (`sec:filter-norms`)) -/

/-- Complex exponential $e^{2\pi i x} = \exp(2\pi i x)$ for $x \in \mathbb{R}$ (Section 3.5 (`sec:prelim-dft`)). -/
noncomputable def expTwoPiI (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * x * Complex.I)

/-- Complex exponential $e^{-2\pi i x} = \exp(-2\pi i x)$ for $x \in \mathbb{R}$ (Section 3.5 (`sec:prelim-dft`)). -/
noncomputable def expNegTwoPiI (x : ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * x * Complex.I)

/-- Primitive $2r$-th root of unity power $\zeta^m = \exp(i \pi m / r)$ for $m \in \mathbb{Z}$ (Section 4.1 (`sec:twisted`), Proposition 4.1 (`thm:twisted`)). -/
noncomputable def zetaPow (r : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (Real.pi * (m : ℝ) / (r : ℝ) * Complex.I)

/-- Normalized 1D Discrete Fourier Transform $(F_R x)_u = \frac{1}{R} \sum_{j=0}^{R-1} x_j e^{2\pi i j u / R}$ (Section 3.5 (`sec:prelim-dft`), equation (9) (`eq:dft-1d`)). -/
noncomputable def normDFT1D {R : ℕ} (x : Fin R → ℂ) (u : Fin R) : ℂ :=
  ((R : ℝ)⁻¹ : ℂ) * ∑ j : Fin R, x j * expTwoPiI (((j.val * u.val : ℕ) : ℝ) / (R : ℝ))

/-- Normalized 2D Discrete Fourier Transform $(F_{t_1, r} U)_{u_1, u_2} = \frac{1}{t_1 r} \sum_{j_1=0}^{t_1-1} \sum_{j_2=0}^{r-1} U_{j_1, j_2} e^{2\pi i j_1 u_1 / t_1} e^{2\pi i j_2 u_2 / r}$ (Section 3.5 (`sec:prelim-dft`), equation (11) (`eq:dft-2d`)). -/
noncomputable def normDFT2D {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) (u1 : Fin t1) (u2 : Fin r) : ℂ :=
  (((t1 * r : ℕ) : ℝ)⁻¹ : ℂ) *
    ∑ j1 : Fin t1, ∑ j2 : Fin r,
      U j1 j2 *
        expTwoPiI (((j1.val * u1.val : ℕ) : ℝ) / (t1 : ℝ)) *
        expTwoPiI (((j2.val * u2.val : ℕ) : ℝ) / (r : ℝ))

/-- Vector $\ell_\infty$-norm $\|x\|_\infty = \sup_{u} \|x_u\|$ using the Euclidean modulus on $\mathbb{C}$ (Section 3.1 (`sec:notation`)). -/
noncomputable def vecInfNorm {R : ℕ} (x : Fin R → ℂ) : ℝ :=
  (((Finset.univ : Finset (Fin R)).sup (fun u => ‖x u‖₊) : NNReal) : ℝ)

/-- Matrix $\ell_\infty$-norm $\|U\|_\infty = \sup_{j_1, j_2} \|U_{j_1, j_2}\|$ (Section 3.1 (`sec:notation`)). -/
noncomputable def matInfNorm {t1 r : ℕ} (U : Fin t1 → Fin r → ℂ) : ℝ :=
  (((Finset.univ : Finset (Fin t1 × Fin r)).sup (fun p => ‖U p.1 p.2‖₊) : NNReal) : ℝ)

/-- Sinc-Gaussian shape parameter $\alpha = 2\sqrt{p_{\text{work}} \ln 2 / \pi}$ (Section 5.1 (`sec:deconv-thm`), Theorem 5.1 (`thm:deconv`)). -/
noncomputable def alphaFromPWork (pWork : ℕ) : ℝ :=
  2 * Real.sqrt (((pWork : ℝ) * Real.log 2) / Real.pi)

/-- Level-$\ell$ Sinc-Gaussian shape parameter $\alpha_\ell = 2\sqrt{p_{\text{work},\ell} \ln 2 / \pi}$ (Section 5.1 (`sec:deconv-thm`), Lemma 6.1 (`lem:filter-norms`)). -/
noncomputable def alphaEll (K p : ℕ) : ℝ :=
  alphaFromPWork (pWorkEll K p)

/-- Spatial truncation half-width $m_{1,\ell} = \lceil \alpha_\ell \sqrt{p_{\ell+1} \ln 2 / \pi} \rceil$ (Lemma 6.1 (`lem:filter-norms`), Lemma 6.5 (`lem:forward`)). -/
noncomputable def m1FromPWorkPChild (pWork pChild : ℕ) : ℕ :=
  Nat.ceil (alphaFromPWork pWork * Real.sqrt (((pChild : ℝ) * Real.log 2) / Real.pi))

/-- Level-$\ell$ spatial truncation half-width $m_{1,\ell}$ (Lemma 6.1 (`lem:filter-norms`), Lemma 6.5 (`lem:forward`)). -/
noncomputable def m1Ell (K p : ℕ) : ℕ :=
  m1FromPWorkPChild (pWorkEll K p) (pChildEll K p)

/-- Full spatial filter window width $W_\ell = 2 m_{1,\ell} + 1$ (Section 6.1 (`sec:filter-norms`), Lemma 6.5 (`lem:forward`)). -/
def windowLength (m1 : ℕ) : ℕ :=
  2 * m1 + 1

/-- Level-$\ell$ full spatial filter window width $W_\ell = 2 m_{1,\ell} + 1$ (Section 6.1 (`sec:filter-norms`), Lemma 6.5 (`lem:forward`)). -/
noncomputable def windowLengthEll (K p : ℕ) : ℕ :=
  windowLength (m1Ell K p)

/-- Pre-folded spatial filter width $\tilde{W}_\ell = \min(W_\ell, r_\ell)$ (Section 6.1 (`sec:filter-norms`), Theorem 6.3 (`thm:spread`)). -/
def foldedWidth (W r : ℕ) : ℕ :=
  min W r

/-- Alias for pre-folded width $\min(W, r)$ (Section 6.1 (`sec:filter-norms`), Theorem 6.3 (`thm:spread`)). -/
abbrev foldedHalfWidth (W r : ℕ) : ℕ :=
  foldedWidth W r

/-! ## 5. Bit Encodings for the 8-Stack Machine (`Turing.FinTM2`, Section 8 (`sec:lean`)) -/

/-- Little-endian $w$-bit encoding of a natural number $x$ (`[bit_0, bit_1, ..., bit_{w-1}]`). -/
def encodeNatBits (w : ℕ) (x : ℕ) : List Bool :=
  List.ofFn (fun i : Fin w => x.testBit i.val)

/-- Decode a little-endian bit list `bs : List Bool` to a natural number $\sum_{i} b_i 2^i$. -/
def decodeNatBits : List Bool → ℕ
  | [] => 0
  | b :: bs => (bif b then 1 else 0) + 2 * decodeNatBits bs

/-- Canonical initial input bit-list encoding `bits A ‖ bits B` of two $n$-bit integers $A, B$ (Section 8 (`sec:lean`)). -/
def encodeInputBits (n A B : ℕ) : List Bool :=
  encodeNatBits n A ++ encodeNatBits n B

end IntMul
