import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives
import IntMul.FastDFT

/-!
# Computable Pure-Integer Schedule & Table Constructor (`IntMul.ComputableSchedule`)

This module provides the computable integer and rational (`ℕ`/`ℤ`/`ℚ`, zero `noncomputable`,
zero `ℝ`, zero `ℂ`) schedule-generation, radix-2 leaf-FFT, and column-sweep solver primitives for
the recursive sinc-Gaussian fractional-shift polynomial-transform DFT (`syntheticFFT` in this
development) and their exact equivalence bridges to `IntMul.FastDFT` (Section 3.3 (`sec:tables`),
Section 5.2 (`sec:solvers`), Section 6.3 (`sec:forward-error`), and Section 8 (`sec:lean`)):

1. **`ScheduleIntTree` & `computeScheduleIntTree`**:
   - `ScheduleIntTree K p B_in`: inductive integer schedule tree carrying the quantized filter taps,
     pre/post twist roots, passband weight mantissas `(c0Mantissa, c1Mantissa)`, and a **1D leaf
     twiddle table** `Fin (2 ^ K) → FixedComplex (qBaseEll K p)` of length $R_L = 2^K$ (never a 2D
     $4^K$ matrix).
   - `computeScheduleIntTree` and `computeScheduleIntTreeWithMul`: computable (`def`) fixed-point
     Taylor-series schedule table generators (zero `noncomputable`, zero `ℝ`/`ℂ`;
     Lemma 3.2 (`lem:elementary`) and Section 8 (`sec:lean`)).
   - `canonicalScheduleIntTree` and `validScheduleIntTree_computeScheduleIntTree`: the analytic
     bridge and accuracy certificate linking schedule tables to the exact filter taps and roots.
2. **$O(K \cdot 2^K)$ Recursive Cooley–Tukey Radix-2 Leaf FFT (`radix2FFT1DFixed`, `baseRadix2FFTFixed`)**:
   - Executes $K$ recursive radix-2 butterfly stages over `FixedComplex (qBaseEll K p)` indexing into
     the 1D leaf twiddle table via stride $2^{K - (m+1)}$ (Lemma 6.5(2) (`lem:forward`)), proved
     bit-exactly equal to `quantizeComplexFixed (p + 2) (baseRadix2FFTQuant K p ...)`.
3. **$O(t_1)$ Column-Sweep Deconvolution Solvers (`nyquistColumnSolveFixed`,
   `cyclicBidiagPrevSolveFixed`)**:
   - Computes the open-chain forward recurrence, alternating sum, and cyclic rank-1 correction
     **once per column** outside the row loop $u_1 \in \{0, \dots, t_1 - 1\}$, in $O(t_1)$
     operations per column (Section 5.2 (`sec:solvers`)), proved bit-exactly equal to
     `nyquistColumnSolveQuant` and `cyclicBidiagPrevSolveQuant`.
4. **Computable Negacyclic Shifts & Radix-2 Polynomial Transform (`negacyclicShiftFixed`,
   `radix2SyntheticFFTFixed`)**:
   - Executes the pure-integer butterfly stages over `FixedComplex`, proved bit-exactly equal to
     `radix2SyntheticFFTQuant` (`toComplex_radix2SyntheticFFTFixed`; Lemma 3.5 (`lem:syn-fft`)).
5. **Window Half-Width & Certified Rational/Fixed-Point Taylor & Square-Root Tables (`computeM1Ell`,
   `approxLogTwoFixed`, `approxPiFixed`, `approxSqrtFixed`, `computeFilterTapFixedWithMul`)**:
   - Evaluates the window half-width `computeM1Ell`, quantized filter taps, and passband mantissas
     (`computePassbandC0MantissaWithMul`, `computePassbandC1MantissaWithMul`; Section 3.3 (`sec:tables`)).
6. **Pure-Integer Width Bounds & Downstream Pipeline Split (`fitsSignedWord_approxPiFixed`,
   `fitsSignedWord_max_approxLogTwoFixed`; downstream `IntMul.ComputableCore`)**:
   - Proves `FitsSignedWord` bounds for tracked schedule evaluation; `computableFastDFTRecursiveWithMul`,
     `computableFastTwoCallDFTConv`, `computableIntMulBits`, and
     `computableReconstructProduct_canonical_eq_mul` are defined in the downstream module
     `IntMul/ComputableCore.lean`.
-/

namespace IntMul

/-! ### 1. Computable Negacyclic Shifts & Radix-2 Polynomial Transform (`syntheticFFT` in this development) over `FixedComplex` -/

/-- Computable pure-integer negacyclic monomial shift in $\tilde{\mathbb{C}}_q[y]/(y^r + 1)$. -/
def negacyclicShiftFixed {r q : ℕ} (s : ℤ) (P : Fin r → FixedComplex q) (k2 : Fin r) :
    FixedComplex q :=
  if ((k2.val : ℤ) - s) % (2 * (r : ℤ)) < (r : ℤ) then
    P (shiftModFin s k2)
  else
    -(P (shiftModFin s k2))

@[simp]
theorem toComplex_negacyclicShiftFixed {r q : ℕ} (s : ℤ) (P : Fin r → FixedComplex q) (k2 : Fin r) :
    (negacyclicShiftFixed s P k2).toComplex =
      negacyclicShift s (fun j => (P j).toComplex) k2 := by
  rw [negacyclicShift_eq_ite_mod_two_mul]
  unfold negacyclicShiftFixed
  split_ifs <;> simp

/-- Computable pure-integer radix-2 synthetic butterfly upper output. -/
def butterflyPlusFixed {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) : Fin r → FixedComplex q :=
  fun k2 => (U k2 + negacyclicShiftFixed s V k2).halfRounded

/-- Computable pure-integer radix-2 synthetic butterfly lower output. -/
def butterflyMinusFixed {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) : Fin r → FixedComplex q :=
  fun k2 => (U k2 - negacyclicShiftFixed s V k2).halfRounded

@[simp]
theorem toComplex_butterflyPlusFixed {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    (butterflyPlusFixed s U V k2).toComplex =
      butterflyPlusQuant q s (fun j => (U j).toComplex) (fun j => (V j).toComplex) k2 := by
  simp [butterflyPlusFixed, butterflyPlusQuant]

@[simp]
theorem toComplex_butterflyMinusFixed {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    (butterflyMinusFixed s U V k2).toComplex =
      butterflyMinusQuant q s (fun j => (U j).toComplex) (fun j => (V j).toComplex) k2 := by
  simp [butterflyMinusFixed, butterflyMinusQuant]

/-- Computable pure-integer $k_1$-stage radix-2 polynomial transform (`syntheticFFT` in this
development) butterfly network over $\tilde{\mathbb{C}}_q[y]/(y^r + 1)$, tabulating each stage via
`memoizeFin2` (Lemma 3.5 (`lem:syn-fft`)). -/
def radix2SyntheticFFTFixed {r q : ℕ} :
    (k1 : ℕ) → (c1 : ℕ) → (Fin (2 ^ k1) → Fin r → FixedComplex q) →
      (Fin (2 ^ k1) → Fin r → FixedComplex q)
  | 0, _c1, P => P
  | m + 1, c1, P =>
    let U := radix2SyntheticFFTFixed m (2 * c1) (fun j => P (evenSubIndex m j))
    let V := radix2SyntheticFFTFixed m (2 * c1) (fun j => P (oddSubIndex m j))
    memoizeFin2 (fun v1 =>
      let u : Fin (2 ^ m) := ⟨v1.val % (2 ^ m), Nat.mod_lt _ (by positivity)⟩
      let s : ℤ := 2 * (c1 : ℤ) * (u.val : ℤ)
      if v1.val < 2 ^ m then
        butterflyPlusFixed s (U u) (V u)
      else
        butterflyMinusFixed s (U u) (V u))

@[simp]
theorem toComplex_radix2SyntheticFFTFixed {r q : ℕ} (k1 : ℕ) :
    ∀ (c1 : ℕ) (P : Fin (2 ^ k1) → Fin r → FixedComplex q) (v1 : Fin (2 ^ k1)) (k2 : Fin r),
      (radix2SyntheticFFTFixed k1 c1 P v1 k2).toComplex =
        radix2SyntheticFFTQuant q k1 c1 (fun j1 j2 => (P j1 j2).toComplex) v1 k2 := by
  induction k1 with
  | zero =>
    intro c1 P v1 k2
    rfl
  | succ m ih =>
    intro c1 P v1 k2
    unfold radix2SyntheticFFTFixed radix2SyntheticFFTQuant
    simp only [memoizeFin2_eq]
    split_ifs <;> simp [ih]

/-! ### 2. $O(K \cdot 2^K)$ Recursive Cooley–Tukey Radix-2 Leaf FFT over `FixedComplex` -/

/-- Index bound for looking up the stage-$(m+1)$ butterfly twiddle factor
$\exp(2\pi i v / 2^{m+1}) = \exp(2\pi i (v \cdot 2^{K - (m+1)}) / 2^K)$ in the 1D leaf twiddle
table of length $2^K$. -/
theorem mul_two_pow_sub_lt {K m : ℕ} (hm : m + 1 ≤ K) (v : Fin (2 ^ m)) :
    v.val * 2 ^ (K - (m + 1)) < 2 ^ K := by
  calc
    v.val * 2 ^ (K - (m + 1)) < 2 ^ m * 2 ^ (K - (m + 1)) :=
      Nat.mul_lt_mul_of_pos_right v.isLt (Nat.two_pow_pos _)
    _ = 2 ^ (m + (K - (m + 1))) := (Nat.pow_add 2 m (K - (m + 1))).symm
    _ < 2 ^ K := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Fixed-point complex multiplication in $\tilde{\mathbb{C}}_q$ parameterized by an integer
multiplication operator `smul : ℤ → ℤ → ℤ`. -/
def FixedComplex.mulRoundedWith (smul : ℤ → ℤ → ℤ) {q : ℕ} (z w : FixedComplex q) :
    FixedComplex q :=
  ⟨roundShiftInt (smul z.re w.re - smul z.im w.im) q,
   roundShiftInt (smul z.re w.im + smul z.im w.re) q⟩

theorem FixedComplex.mulRoundedWith_eq_mulRounded (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, smul a b = a * b) {q : ℕ} (z w : FixedComplex q) :
    FixedComplex.mulRoundedWith smul z w = FixedComplex.mulRounded z w := by
  ext <;> simp [FixedComplex.mulRoundedWith, FixedComplex.mulRounded, hsmul]

theorem FixedComplex.mulRoundedWith_eq_mulRounded_of_bounds {w q : ℕ} (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, FitsSignedWord w a → FitsSignedWord w b → smul a b = a * b)
    {z1 z2 : FixedComplex q} (h1 : WordWidthBounds w z1) (h2 : WordWidthBounds w z2) :
    FixedComplex.mulRoundedWith smul z1 z2 = FixedComplex.mulRounded z1 z2 := by
  ext <;> simp [FixedComplex.mulRoundedWith, FixedComplex.mulRounded,
    hsmul _ _ h1.1 h2.1, hsmul _ _ h1.2 h2.2, hsmul _ _ h1.1 h2.2, hsmul _ _ h1.2 h2.1]

/-- Computable $m$-stage Cooley–Tukey radix-2 decimation-in-time butterfly FFT over `FixedComplex q`
parameterized by `smul : ℤ → ℤ → ℤ` and tabulated at each stage via `memoizeFin`. -/
def radix2FFT1DFixedWithMul (smul : ℤ → ℤ → ℤ) (K q : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    (m : ℕ) → m ≤ K → (Fin (2 ^ m) → FixedComplex q) → (Fin (2 ^ m) → FixedComplex q)
  | 0, _, x => x
  | m + 1, hm, x =>
    let E := radix2FFT1DFixedWithMul smul K q leafTwiddles m (Nat.le_of_succ_le hm)
      (fun j => x (evenSubIndex m j))
    let O := radix2FFT1DFixedWithMul smul K q leafTwiddles m (Nat.le_of_succ_le hm)
      (fun j => x (oddSubIndex m j))
    memoizeFin (fun u =>
      let v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
      let wIdx : Fin (2 ^ K) := ⟨v.val * 2 ^ (K - (m + 1)), mul_two_pow_sub_lt hm v⟩
      let w : FixedComplex q := leafTwiddles wIdx
      let t : FixedComplex q := FixedComplex.mulRoundedWith smul w (O v)
      if u.val < 2 ^ m then
        (E v + t).halfRounded
      else
        (E v - t).halfRounded)

/-- Computable $m$-stage Cooley–Tukey radix-2 decimation-in-time butterfly FFT over `FixedComplex q`,
indexing into a 1D leaf twiddle table `leafTwiddles : Fin (2 ^ K) → FixedComplex q` of length $2^K$
(`BaseRadix2FFT` in Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`), and
Lemma 6.5(2) (`lem:forward`)). -/
def radix2FFT1DFixed (K q : ℕ) (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    (m : ℕ) → m ≤ K → (Fin (2 ^ m) → FixedComplex q) → (Fin (2 ^ m) → FixedComplex q) :=
  radix2FFT1DFixedWithMul (· * ·) K q leafTwiddles

theorem radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, smul a b = a * b) (K q : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) (m : ℕ) (hm : m ≤ K)
    (x : Fin (2 ^ m) → FixedComplex q) :
    radix2FFT1DFixedWithMul smul K q leafTwiddles m hm x =
      radix2FFT1DFixed K q leafTwiddles m hm x := by
  unfold radix2FFT1DFixed
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold radix2FFT1DFixedWithMul
    simp only [memoizeFin_eq]
    funext u
    rw [ih, ih, FixedComplex.mulRoundedWith_eq_mulRounded smul hsmul,
      FixedComplex.mulRoundedWith_eq_mulRounded (· * ·) (fun _ _ => rfl)]

/-- Exact equivalence between the computable $m$-stage radix-2 butterfly FFT `radix2FFT1DFixed`
and the analytic quantized recursion `radix2FFT1DQuant`. -/
theorem radix2FFT1DFixed_toComplex_eq_radix2FFT1DQuant (K q : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (hleaf : ∀ u : Fin (2 ^ K),
      leafTwiddles u = quantizeComplexFixed q (expTwoPiI ((u.val : ℝ) / ((2 ^ K : ℕ) : ℝ))))
    (m : ℕ) (hm : m ≤ K) :
    ∀ (xFixed : Fin (2 ^ m) → FixedComplex q) (x : Fin (2 ^ m) → ℂ)
      (_hx : ∀ j : Fin (2 ^ m), (xFixed j).toComplex = quantizeComplex q (x j))
      (u : Fin (2 ^ m)),
      (radix2FFT1DFixed K q leafTwiddles m hm xFixed u).toComplex =
        radix2FFT1DQuant q m x u := by
  induction m with
  | zero =>
    intro xFixed x hx u
    unfold radix2FFT1DFixed radix2FFT1DFixedWithMul radix2FFT1DQuant
    exact hx u
  | succ m ih =>
    intro xFixed x hx u
    unfold radix2FFT1DFixed radix2FFT1DFixedWithMul radix2FFT1DQuant
    simp only [memoizeFin_eq]
    set hm' : m ≤ K := Nat.le_of_succ_le hm
    set v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
    set wIdx : Fin (2 ^ K) := ⟨v.val * 2 ^ (K - (m + 1)), mul_two_pow_sub_lt hm v⟩
    have hE : (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => xFixed (evenSubIndex m j)) v).toComplex =
        radix2FFT1DQuant q m (fun j => x (evenSubIndex m j)) v :=
      ih hm' (fun j => xFixed (evenSubIndex m j)) (fun j => x (evenSubIndex m j))
        (fun j => hx (evenSubIndex m j)) v
    have hO : (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => xFixed (oddSubIndex m j)) v).toComplex =
        radix2FFT1DQuant q m (fun j => x (oddSubIndex m j)) v :=
      ih hm' (fun j => xFixed (oddSubIndex m j)) (fun j => x (oddSubIndex m j))
        (fun j => hx (oddSubIndex m j)) v
    have hpowK : (2 ^ K : ℕ) = 2 ^ (m + 1) * 2 ^ (K - (m + 1)) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hm]
    have harg : ((wIdx.val : ℝ) / ((2 ^ K : ℕ) : ℝ)) =
        (v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) := by
      have hpos : ((2 ^ (K - (m + 1)) : ℕ) : ℝ) ≠ 0 := by positivity
      change (((v.val * 2 ^ (K - (m + 1)) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) =
        (v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)
      rw [hpowK]
      push_cast
      field_simp [hpos]
    have hw : (leafTwiddles wIdx).toComplex =
        quantizeComplex q (expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ))) := by
      rw [hleaf wIdx, ← quantizeComplex, harg]
    rw [FixedComplex.mulRoundedWith_eq_mulRounded (· * ·) (fun _ _ => rfl)]
    change (if u.val < 2 ^ m then
        (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => xFixed (evenSubIndex m j)) v +
          (leafTwiddles wIdx).mulRounded
            (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => xFixed (oddSubIndex m j)) v)).halfRounded
      else
        (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => xFixed (evenSubIndex m j)) v -
          (leafTwiddles wIdx).mulRounded
            (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => xFixed (oddSubIndex m j)) v)).halfRounded).toComplex =
      if u.val < 2 ^ m then
        quantizeComplex q ((radix2FFT1DQuant q m (fun j => x (evenSubIndex m j)) v +
          quantizeComplex q (quantizeComplex q (expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ))) *
            radix2FFT1DQuant q m (fun j => x (oddSubIndex m j)) v)) / 2)
      else
        quantizeComplex q ((radix2FFT1DQuant q m (fun j => x (evenSubIndex m j)) v -
          quantizeComplex q (quantizeComplex q (expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ))) *
            radix2FFT1DQuant q m (fun j => x (oddSubIndex m j)) v)) / 2)
    split_ifs with hu
    · rw [FixedComplex.toComplex_halfRounded, FixedComplex.toComplex_add_op,
        FixedComplex.toComplex_mulRounded, hE, hO, hw]
    · rw [FixedComplex.toComplex_halfRounded, FixedComplex.toComplex_sub_op,
        FixedComplex.toComplex_mulRounded, hE, hO, hw]

/-- Computable $O(K \cdot 2^K)$ $K$-stage Cooley–Tukey radix-2 leaf FFT over `FixedComplex`
parameterized by `smul : ℤ → ℤ → ℤ` and tabulated via `memoizeFin`. -/
def baseRadix2FFTFixedWithMul (smul : ℤ → ℤ → ℤ) (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    Fin (2 ^ K) → FixedComplex (p + 2) :=
  let qBase := qBaseEll K p
  let xBase : Fin (2 ^ K) → FixedComplex qBase :=
    memoizeFin (fun j => FixedComplex.rescale qBase (xFixed j))
  let yBase := radix2FFT1DFixedWithMul smul K qBase leafTwiddles K (le_refl K) xBase
  memoizeFin (fun u => FixedComplex.rescale (p + 2) (yBase u))

/-- Computable $O(K \cdot 2^K)$ $K$-stage Cooley–Tukey radix-2 leaf FFT over `FixedComplex`
(`BaseRadix2FFT` in Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`), and
Lemma 6.5(2) (`lem:forward`)). -/
def baseRadix2FFTFixed (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    Fin (2 ^ K) → FixedComplex (p + 2) :=
  baseRadix2FFTFixedWithMul (· * ·) K p leafTwiddles xFixed

theorem baseRadix2FFTFixedWithMul_eq_baseRadix2FFTFixed (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, smul a b = a * b) (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    baseRadix2FFTFixedWithMul smul K p leafTwiddles xFixed =
      baseRadix2FFTFixed K p leafTwiddles xFixed := by
  funext u
  unfold baseRadix2FFTFixed baseRadix2FFTFixedWithMul
  simp only [memoizeFin_eq]
  rw [radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed smul hsmul,
    radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl)]

/-- Canonical 1D quantized leaf twiddle table of length $2^K = R_L$ for `baseRadix2FFTFixed`. -/
noncomputable def canonicalLeafRoots (K p : ℕ) (u : Fin (2 ^ K)) :
    FixedComplex (qBaseEll K p) :=
  quantizeComplexFixed (qBaseEll K p)
    (expTwoPiI ((u.val : ℝ) / ((2 ^ K : ℕ) : ℝ)))

theorem baseRadix2FFTFixed_canonical_eq (K p : ℕ)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) (u : Fin (2 ^ K)) :
    baseRadix2FFTFixed K p (canonicalLeafRoots K p) xFixed u =
      quantizeComplexFixed (p + 2)
        (baseRadix2FFTQuant K p (fun j => (xFixed j).toComplex) u) := by
  unfold baseRadix2FFTFixed baseRadix2FFTFixedWithMul baseRadix2FFTQuant
  simp only [memoizeFin_eq]
  rw [radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl),
    FixedComplex.rescale_eq_quantizeComplexFixed, quantizeComplexFixed_quantizeComplex]
  congr 1
  exact radix2FFT1DFixed_toComplex_eq_radix2FFT1DQuant K (qBaseEll K p)
    (canonicalLeafRoots K p) (fun _ => rfl) K (le_refl K)
    (fun j => FixedComplex.rescale (qBaseEll K p) (xFixed j))
    (fun j => (xFixed j).toComplex)
    (fun j => FixedComplex.toComplex_rescale (qBaseEll K p) (xFixed j)) u

/-! ### 3. $O(t_1)$ Column-Sweep Deconvolution Solvers -/

/-- Computable alternating sign $(-1)^k \in \{1, -1\} \subset \mathbb{Z}$. -/
def altSign (k : ℕ) : ℤ :=
  if k % 2 = 0 then 1 else -1

theorem altSign_eq_one_or_neg_one (k : ℕ) : altSign k = 1 ∨ altSign k = -1 := by
  unfold altSign; split_ifs <;> simp

@[simp]
theorem cast_altSign_real (k : ℕ) : ((altSign k : ℤ) : ℝ) = (-1 : ℝ) ^ k := by
  unfold altSign
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · simp [Nat.mul_mod_right, pow_mul]
  · have hmod : (2 * m + 1) % 2 = 1 := by omega
    simp [hmod, pow_add, pow_mul]

@[simp]
theorem cast_altSign_complex (k : ℕ) : ((altSign k : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  exact_mod_cast cast_altSign_real k

/-- Computable pure-integer Nyquist mode alternating sum in `FixedComplex (qChildEll K p)`. -/
def nyquistModeSumFixed (K p : ℕ) (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    FixedComplex (qChildEll K p) :=
  let S_re : ℤ :=
    ∑ j2 : Fin (rEll K),
      altSign j2.val *
        (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩).re
  let S_im : ℤ :=
    ∑ j2 : Fin (rEll K),
      altSign j2.val *
        (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩).im
  FixedComplex.rescale (qChildEll K p) (⟨-S_im, S_re⟩ : FixedComplex (p + 2 + k2Ell K))

theorem nyquistModeSumFixed_eq_quantizeComplexFixed (K p : ℕ)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    nyquistModeSumFixed K p xFixed =
      quantizeComplexFixed (qChildEll K p)
        (nyquistModeSum K (fun j => (xFixed j).toComplex)) := by
  unfold nyquistModeSumFixed nyquistModeSum
  rw [FixedComplex.rescale_eq_quantizeComplexFixed]
  congr 1
  have hr : (rEll K : ℂ) = (((2 : ℝ) ^ (k2Ell K) : ℝ) : ℂ) := by
    unfold rEll
    push_cast
    rfl
  have hr_inv : ((rEll K : ℂ))⁻¹ = (((2 : ℝ) ^ (-(k2Ell K : ℤ)) : ℝ) : ℂ) := by
    rw [hr]
    push_cast
    rw [zpow_neg, zpow_natCast]
  rw [div_eq_mul_inv, hr_inv]
  have hscale : (2 : ℝ) ^ (-((p + 2 + k2Ell K : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-(k2Ell K : ℤ)) * (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) := by
    have hexp : -((p + 2 + k2Ell K : ℕ) : ℤ) = -(k2Ell K : ℤ) + -((p + 2 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_add₀ (by norm_num)]
  have hsum_re :
      (∑ j2 : Fin (rEll K),
        (-1 : ℂ) ^ j2.val *
          (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K,
            Nat.mod_lt _ (Nat.two_pow_pos K)⟩).toComplex).re =
      ((∑ j2 : Fin (rEll K),
        altSign j2.val *
          (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K,
            Nat.mod_lt _ (Nat.two_pow_pos K)⟩).re : ℤ) : ℝ) *
        (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) := by
    rw [Complex.re_sum, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j2 _ => ?_)
    rw [← cast_altSign_complex]
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
      FixedComplex.toComplex_re, Int.cast_mul]
    ring
  have hsum_im :
      (∑ j2 : Fin (rEll K),
        (-1 : ℂ) ^ j2.val *
          (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K,
            Nat.mod_lt _ (Nat.two_pow_pos K)⟩).toComplex).im =
      ((∑ j2 : Fin (rEll K),
        altSign j2.val *
          (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K,
            Nat.mod_lt _ (Nat.two_pow_pos K)⟩).im : ℤ) : ℝ) *
        (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) := by
    rw [Complex.im_sum, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j2 _ => ?_)
    rw [← cast_altSign_complex]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      FixedComplex.toComplex_im, Int.cast_mul]
    ring
  apply Complex.ext
  · rw [FixedComplex.toComplex_re, Int.cast_neg, hscale]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hsum_im]
    ring
  · rw [FixedComplex.toComplex_im, hscale]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hsum_re]
    ring

/-- Computable rational-to-mantissa rounding $\lfloor x \cdot 2^q + 1/2 \rfloor$. -/
def quantizeRatMantissa (q : ℕ) (x : ℚ) : ℤ :=
  ⌊x * (2 : ℚ) ^ q + (1 / 2 : ℚ)⌋

theorem quantizeRatMantissa_eq_quantizeRealMantissa (q : ℕ) (x : ℚ) :
    quantizeRatMantissa q x = quantizeRealMantissa q (x : ℝ) := by
  unfold quantizeRatMantissa quantizeRealMantissa
  rw [← Rat.floor_cast (α := ℝ)]
  push_cast
  rfl

/-- Fixed-point real-mantissa times complex multiplication in $\tilde{\mathbb{C}}_q$ parameterized
by `smul : ℤ → ℤ → ℤ`. -/
def FixedComplex.scaleRoundedWith (smul : ℤ → ℤ → ℤ) {q : ℕ} (m : ℤ) (z : FixedComplex q) :
    FixedComplex q :=
  ⟨roundShiftInt (smul m z.re) q, roundShiftInt (smul m z.im) q⟩

/-- Fixed-point real-mantissa times complex multiplication in $\tilde{\mathbb{C}}_q$
(`FixedComplex.scaleRounded`). -/
def FixedComplex.scaleRounded {q : ℕ} (m : ℤ) (z : FixedComplex q) : FixedComplex q :=
  FixedComplex.scaleRoundedWith (· * ·) m z

theorem FixedComplex.scaleRoundedWith_eq_scaleRounded (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, smul a b = a * b) {q : ℕ} (m : ℤ) (z : FixedComplex q) :
    FixedComplex.scaleRoundedWith smul m z = FixedComplex.scaleRounded m z := by
  ext <;> simp [FixedComplex.scaleRoundedWith, FixedComplex.scaleRounded, hsmul]

theorem FixedComplex.scaleRoundedWith_eq_scaleRounded_of_bounds {w q : ℕ} (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, FitsSignedWord w a → FitsSignedWord w b → smul a b = a * b)
    {m : ℤ} {z : FixedComplex q} (hm : FitsSignedWord w m) (hz : WordWidthBounds w z) :
    FixedComplex.scaleRoundedWith smul m z = FixedComplex.scaleRounded m z := by
  ext <;> simp [FixedComplex.scaleRoundedWith, FixedComplex.scaleRounded,
    hsmul _ _ hm hz.1, hsmul _ _ hm hz.2]

theorem FixedComplex.scaleRounded_eq_mulRounded {q : ℕ} (m : ℤ) (z : FixedComplex q) :
    FixedComplex.scaleRounded m z = FixedComplex.mulRounded ⟨m, 0⟩ z := by
  ext <;> simp [FixedComplex.scaleRounded, FixedComplex.scaleRoundedWith, FixedComplex.mulRounded]

theorem FixedComplex.toComplex_scaleRounded {q : ℕ} (m : ℤ) (z : FixedComplex q) :
    (FixedComplex.scaleRounded m z).toComplex =
      quantizeComplex q ((((m : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) : ℝ) : ℂ) * z.toComplex) := by
  rw [FixedComplex.scaleRounded_eq_mulRounded, FixedComplex.toComplex_mulRounded]
  congr 2
  unfold FixedComplex.toComplex
  simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, add_zero]

theorem FixedComplex.toComplex_rescale_of_le {q1 q2 : ℕ} (h : q1 ≤ q2) (z : FixedComplex q1) :
    (FixedComplex.rescale q2 z).toComplex = z.toComplex := by
  have hsub : q1 - q2 = 0 := Nat.sub_eq_zero_of_le h
  have hscale : (2 : ℝ) ^ (q2 - q1) * (2 : ℝ) ^ (-(q2 : ℤ)) = (2 : ℝ) ^ (-(q1 : ℤ)) := by
    have hexp : -(q1 : ℤ) = ((q2 - q1 : ℕ) : ℤ) + -(q2 : ℤ) := by omega
    rw [hexp, zpow_add₀ (by norm_num), zpow_natCast]
  apply Complex.ext
  · simp only [FixedComplex.rescale, FixedComplex.toComplex_re, hsub, roundShiftInt, ↓reduceIte,
      Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_assoc, hscale]
  · simp only [FixedComplex.rescale, FixedComplex.toComplex_im, hsub, roundShiftInt, ↓reduceIte,
      Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_assoc, hscale]

/-- Fixed-point complex division by a scalar mantissa `b : ℤ` at scale `q1`, rounded to scale `q2`
(`divScalarFixed`). -/
def divScalarFixed (q1 q2 : ℕ) (z : FixedComplex q1) (b : ℤ) : FixedComplex q2 :=
  ⟨roundDivInt (z.re * (2 : ℤ) ^ q2) b, roundDivInt (z.im * (2 : ℤ) ^ q2) b⟩

theorem toComplex_divScalarFixed (q1 q2 : ℕ) (z : FixedComplex q1) (b : ℤ) :
    (divScalarFixed q1 q2 z b).toComplex =
      quantizeComplex q2 (z.toComplex / ((((b : ℝ) * (2 : ℝ) ^ (-(q1 : ℤ))) : ℝ) : ℂ)) := by
  unfold divScalarFixed quantizeComplex quantizeComplexFixed
  congr 1
  ext <;> dsimp only
  · rw [roundDivInt_mul_two_pow_eq_quantizeRealMantissa q1 q2 z.re b,
      Complex.div_ofReal_re, FixedComplex.toComplex_re]
  · rw [roundDivInt_mul_two_pow_eq_quantizeRealMantissa q1 q2 z.im b,
      Complex.div_ofReal_im, FixedComplex.toComplex_im]

/-- Fixed-point complex division by a natural number `n : ℕ` in $\tilde{\mathbb{C}}_q$
(`divNatFixed`). -/
def divNatFixed {q : ℕ} (z : FixedComplex q) (n : ℕ) : FixedComplex q :=
  ⟨roundDivInt z.re n, roundDivInt z.im n⟩

theorem toComplex_divNatFixed {q : ℕ} (z : FixedComplex q) (n : ℕ) :
    (divNatFixed z n).toComplex = quantizeComplex q (z.toComplex / (n : ℂ)) := by
  unfold divNatFixed quantizeComplex quantizeComplexFixed
  congr 1
  ext <;> dsimp only
  · rw [roundDivInt_eq_quantizeRealMantissa_div_nat q z.re n,
      Complex.div_natCast_re, FixedComplex.toComplex_re]
  · rw [roundDivInt_eq_quantizeRealMantissa_div_nat q z.im n,
      Complex.div_natCast_im, FixedComplex.toComplex_im]

/-- Single step of the pure-integer non-Nyquist cyclic bidiagonal recurrence sweep in `FixedComplex qWork × ℤ`
parameterized by `smul : ℤ → ℤ → ℤ`. -/
def bidiagSweepStepFixedWithMul (smul : ℤ → ℤ → ℤ) (qWork : ℕ) (ratio_m : ℤ)
    (B_scaledFixed : ℕ → FixedComplex qWork) (s : ℕ)
    (st : FixedComplex qWork × ℤ) : FixedComplex qWork × ℤ :=
  (B_scaledFixed s + FixedComplex.scaleRoundedWith smul ratio_m st.1,
   roundShiftInt (smul ratio_m st.2) qWork)

/-- Single step of the pure-integer non-Nyquist cyclic bidiagonal recurrence sweep in `FixedComplex qWork × ℤ`
(`bidiagSweepStepFixed`). -/
def bidiagSweepStepFixed (qWork : ℕ) (ratio_m : ℤ)
    (B_scaledFixed : ℕ → FixedComplex qWork) (s : ℕ)
    (st : FixedComplex qWork × ℤ) : FixedComplex qWork × ℤ :=
  (B_scaledFixed s + FixedComplex.scaleRounded ratio_m st.1,
   roundShiftInt (ratio_m * st.2) qWork)

/-- Pure-integer single-pass $O(t_1)$ bidiagonal recurrence sweep parameterized by `smul : ℤ → ℤ → ℤ`
and tabulated via `memoizeRange` and `memoizeFin`
(`bidiagSweepFixedWithMul`):
computes `invA_m` and `ratio_m` once per column (plus 2 scalar divisions in `divScalarFixed` for `Z0`,
for 4 divisions per column total) and scales each RHS entry via fixed-point multiplication. -/
def bidiagSweepFixedWithMul (smul : ℤ → ℤ → ℤ) (t1 q : ℕ) (a_max a_min : ℤ)
    (Y_seq : ℕ → FixedComplex q) (idx : Fin t1 → ℕ) : Fin t1 → FixedComplex q :=
  let qWork : ℕ := q + 9
  let invA_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
  let ratio_m : ℤ := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
  let B_scaledFixed : ℕ → FixedComplex qWork :=
    memoizeRange t1 (fun s =>
      FixedComplex.scaleRoundedWith smul invA_m (FixedComplex.rescale qWork (Y_seq s)))
  let (trajArr, lastSt) :=
    buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
      (bidiagSweepStepFixedWithMul smul qWork ratio_m B_scaledFixed) t1
  let Z0 : FixedComplex qWork :=
    divScalarFixed qWork qWork lastSt.1 ((2 : ℤ) ^ qWork - lastSt.2)
  memoizeFin (fun u1 =>
    let st := trajArr.getD (idx u1) ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    FixedComplex.rescale q (st.1 + FixedComplex.scaleRoundedWith smul st.2 Z0))

/-- **Pure-Integer Single-Pass $O(t_1)$ Bidiagonal Recurrence Sweep (`bidiagSweepFixed`,
Theorem 5.1(2) (`thm:deconv`) and Section 5.2 (`sec:solvers`))**:
Computes the column reciprocal `invA_m` once per column, scales the RHS entries via fixed-point
multiplication, and computes the particular and homogeneous recurrence trajectories in a **single pass
of $t_1$ steps** via `buildRecurrenceArray` outside `fun u1 => ...` using only `ℤ`, `roundDivInt`,
`roundShiftInt`, `FixedComplex`, `memoizeRange`, and `memoizeFin` (zero `ℚ`, zero $\Theta(t_1^2)$
per-column sum, and only 4 scalar divisions per column). -/
def bidiagSweepFixed (t1 q : ℕ) (a_max a_min : ℤ)
    (Y_seq : ℕ → FixedComplex q) (idx : Fin t1 → ℕ) : Fin t1 → FixedComplex q :=
  let qWork : ℕ := q + 9
  let invA_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
  let ratio_m : ℤ := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
  let B_scaledFixed : ℕ → FixedComplex qWork :=
    memoizeRange t1 (fun s =>
      FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq s)))
  let (trajArr, lastSt) :=
    buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
      (bidiagSweepStepFixed qWork ratio_m B_scaledFixed) t1
  let Z0 : FixedComplex qWork :=
    divScalarFixed qWork qWork lastSt.1 ((2 : ℤ) ^ qWork - lastSt.2)
  memoizeFin (fun u1 =>
    let st := trajArr.getD (idx u1) ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    FixedComplex.rescale q (st.1 + FixedComplex.scaleRounded st.2 Z0))

/-- Computable fixed-point Step 3 forward-shift cyclic bidiagonal column solver parameterized by
`smul : ℤ → ℤ → ℤ` (`cyclicBidiagSolveFixedWithMul`). -/
def cyclicBidiagSolveFixedWithMul (smul : ℤ → ℤ → ℤ) {t1 q : ℕ} [NeZero t1] (a b : ℤ)
    (Y : Fin t1 → FixedComplex q) : Fin t1 → FixedComplex q :=
  have ht1 : 0 < t1 := NeZero.pos t1
  if b ≤ a then
    bidiagSweepFixedWithMul smul t1 q a b
      (fun s => Y ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => (t1 - u1.val) % t1)
  else
    bidiagSweepFixedWithMul smul t1 q b a
      (fun s => Y ⟨s % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => u1.val)

/-- Computable fixed-point Step 3 forward-shift cyclic bidiagonal column solver on integer mantissas
`a, b : ℤ`, executing the single-pass $O(t_1)$ linear recurrence sweep `bidiagSweepFixed`
(`cyclicBidiagSolveFixed`). -/
def cyclicBidiagSolveFixed {t1 q : ℕ} [NeZero t1] (a b : ℤ)
    (Y : Fin t1 → FixedComplex q) : Fin t1 → FixedComplex q :=
  have ht1 : 0 < t1 := NeZero.pos t1
  if b ≤ a then
    bidiagSweepFixed t1 q a b
      (fun s => Y ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => (t1 - u1.val) % t1)
  else
    bidiagSweepFixed t1 q b a
      (fun s => Y ⟨s % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => u1.val)

/-- Computable fixed-point Step 3 backward-shift cyclic bidiagonal column solver parameterized by
`smul : ℤ → ℤ → ℤ` (`cyclicBidiagPrevSolveFixedWithMul`). -/
def cyclicBidiagPrevSolveFixedWithMul (smul : ℤ → ℤ → ℤ) {t1 q : ℕ} [NeZero t1] (a b : ℤ)
    (Y : Fin t1 → FixedComplex q) : Fin t1 → FixedComplex q :=
  cyclicBidiagSolveFixedWithMul smul b a (fun m => Y (cyclicNext m))

/-- Computable fixed-point Step 3 backward-shift cyclic bidiagonal column solver on integer mantissas
`a, b : ℤ` (`cyclicBidiagPrevSolveFixed`). -/
def cyclicBidiagPrevSolveFixed {t1 q : ℕ} [NeZero t1] (a b : ℤ)
    (Y : Fin t1 → FixedComplex q) : Fin t1 → FixedComplex q :=
  cyclicBidiagSolveFixed b a (fun m => Y (cyclicNext m))

theorem cyclicBidiagPrevSolveFixedWithMul_eq_cyclicBidiagPrevSolveFixed (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, smul a b = a * b) {t1 q : ℕ} [NeZero t1] (a b : ℤ)
    (Y : Fin t1 → FixedComplex q) :
    cyclicBidiagPrevSolveFixedWithMul smul a b Y = cyclicBidiagPrevSolveFixed a b Y := by
  have hfn : smul = (· * ·) := funext fun x => funext fun y => hsmul x y
  subst hfn
  rfl

private theorem roundShiftInt_mul_eq_quantizeReal (q : ℕ) (m1 m2 : ℤ) :
    (roundShiftInt (m1 * m2) q : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) =
      quantizeReal q (((m1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * ((m2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))) := by
  unfold quantizeReal quantizeRealMantissa
  rw [roundShiftInt_eq_quantizeRealMantissa]
  have hcancel : (2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
  have hinner :
      ((m1 * m2 : ℤ) : ℝ) / (2 : ℝ) ^ q =
        ((m1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * ((m2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * (2 : ℝ) ^ q := by
    calc
      ((m1 * m2 : ℤ) : ℝ) / (2 : ℝ) ^ q
        = ((m1 : ℝ) * (m2 : ℝ) / (2 : ℝ) ^ q) * ((2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q) := by
          rw [hcancel, mul_one, Int.cast_mul]
      _ = (((m1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * ((m2 : ℝ) * ((2 : ℝ) ^ q)⁻¹)) * (2 : ℝ) ^ q := by
          rw [div_eq_mul_inv]
          ring
      _ = ((m1 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * ((m2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * (2 : ℝ) ^ q := by
          rw [zpow_neg, zpow_natCast]
  rw [hinner]

private theorem buildRecurrenceArray_bidiagSweepStepFixed_eq (q : ℕ) (a_max a_min : ℤ)
    (Y_seq : ℕ → FixedComplex q) :
    let qWork : ℕ := q + 9
    let c_max_q : ℝ := (a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
    let c_min_q : ℝ := (a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
    let invA_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
    let invA_q : ℝ := quantizeReal qWork (c_max_q⁻¹)
    let ratio_m : ℤ := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
    let ratio_q : ℝ := quantizeReal qWork (-c_min_q / c_max_q)
    let B_scaledFixed : ℕ → FixedComplex qWork :=
      fun s => FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq s))
    let B_scaled : ℕ → ℂ :=
      fun s => quantizeComplex qWork ((invA_q : ℂ) * (Y_seq s).toComplex)
    ∀ s : ℕ,
      ((buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
          (bidiagSweepStepFixed qWork ratio_m B_scaledFixed) s).2.1.toComplex =
        (buildRecurrenceArray ((0 : ℂ), (1 : ℝ))
          (bidiagSweepStep qWork ratio_q B_scaled) s).2.1) ∧
      (((buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
          (bidiagSweepStepFixed qWork ratio_m B_scaledFixed) s).2.2 : ℝ) *
        (2 : ℝ) ^ (-(qWork : ℤ)) =
        (buildRecurrenceArray ((0 : ℂ), (1 : ℝ))
          (bidiagSweepStep qWork ratio_q B_scaled) s).2.2) := by
  intro qWork c_max_q c_min_q invA_m invA_q ratio_m ratio_q B_scaledFixed B_scaled s
  have hinv_eq : (invA_m : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) = invA_q := by
    dsimp [invA_m, invA_q, quantizeReal, c_max_q]
    rw [roundDivInt_two_pow_add_eq_quantizeRealMantissa_inv q qWork a_max]
  have hratio_eq : (ratio_m : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) = ratio_q := by
    dsimp [ratio_m, ratio_q, quantizeReal, c_max_q, c_min_q]
    rw [roundDivInt_mul_two_pow_eq_quantizeRealMantissa q qWork (-a_min) a_max]
    congr 2
    push_cast
    ring
  induction s with
  | zero =>
    simp only [buildRecurrenceArray, FixedComplex.toComplex_zero, true_and]
    exact_mod_cast two_pow_mul_two_zpow_neg qWork
  | succ s ih =>
    simp only [buildRecurrenceArray, bidiagSweepStepFixed, bidiagSweepStep]
    refine ⟨?_, ?_⟩
    · rw [FixedComplex.toComplex_add_op, FixedComplex.toComplex_scaleRounded, hinv_eq,
        FixedComplex.toComplex_rescale_of_le (by omega : q ≤ qWork) (Y_seq s),
        FixedComplex.toComplex_scaleRounded, hratio_eq, ih.1]
    · rw [roundShiftInt_mul_eq_quantizeReal, hratio_eq, ih.2]

theorem toComplex_bidiagSweepFixed (t1 q : ℕ) (a_max a_min : ℤ)
    (Y_seq : ℕ → FixedComplex q) (idx : Fin t1 → ℕ) (hidx : ∀ u1 : Fin t1, idx u1 ≤ t1)
    (u1 : Fin t1) :
    (bidiagSweepFixed t1 q a_max a_min Y_seq idx u1).toComplex =
      bidiagSweepQuant t1 q a_max a_min (fun s => quantizeComplex q (Y_seq s).toComplex) idx u1 := by
  have hY_q : (fun s => quantizeComplex q (Y_seq s).toComplex) = (fun s => (Y_seq s).toComplex) := by
    funext s
    exact quantizeComplex_toComplex q (Y_seq s)
  rw [hY_q]
  unfold bidiagSweepFixed bidiagSweepQuant
  simp only [memoizeFin_eq, memoizeRange_eq]
  set qWork : ℕ := q + 9
  set c_max_q : ℝ := (a_max : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  set c_min_q : ℝ := (a_min : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  set invA_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
  set invA_q : ℝ := quantizeReal qWork (c_max_q⁻¹)
  set ratio_m : ℤ := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
  set ratio_q : ℝ := quantizeReal qWork (-c_min_q / c_max_q)
  set B_scaledFixed : ℕ → FixedComplex qWork :=
    fun s => FixedComplex.scaleRounded invA_m (FixedComplex.rescale qWork (Y_seq s))
  set B_scaled : ℕ → ℂ :=
    fun s => quantizeComplex qWork ((invA_q : ℂ) * (Y_seq s).toComplex)
  have hgetF := getD_buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    (bidiagSweepStepFixed qWork ratio_m B_scaledFixed) (hidx u1)
  have hgetC := getD_buildRecurrenceArray ((0 : ℂ), (1 : ℝ))
    (bidiagSweepStep qWork ratio_q B_scaled) (hidx u1)
  rw [hgetF, hgetC, FixedComplex.toComplex_rescale, FixedComplex.toComplex_add_op,
    FixedComplex.toComplex_scaleRounded]
  have hs := buildRecurrenceArray_bidiagSweepStepFixed_eq q a_max a_min Y_seq (idx u1)
  have ht1 := buildRecurrenceArray_bidiagSweepStepFixed_eq q a_max a_min Y_seq t1
  rw [hs.1, hs.2, toComplex_divScalarFixed, ht1.1]
  have hdenom :
      ((((2 : ℤ) ^ qWork -
          (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
            (bidiagSweepStepFixed qWork ratio_m B_scaledFixed) t1).2.2 : ℤ) : ℝ) *
        (2 : ℝ) ^ (-(qWork : ℤ))) =
      1 - (buildRecurrenceArray ((0 : ℂ), (1 : ℝ))
            (bidiagSweepStep qWork ratio_q B_scaled) t1).2.2 := by
    rw [Int.cast_sub, sub_mul, ← ht1.2]
    have hpow : (((2 : ℤ) ^ qWork : ℤ) : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) = 1 := by
      exact_mod_cast two_pow_mul_two_zpow_neg qWork
    rw [hpow]
  rw [hdenom]

/-- Exact bridge between pure-integer `cyclicBidiagSolveFixed` and `cyclicBidiagSolveQuantWithMantissa`
for any integer mantissas `a, b : ℤ`. -/
theorem toComplex_cyclicBidiagSolveFixed_withMantissa {t1 q : ℕ} [NeZero t1] (a b : ℤ)
    (Y : Fin t1 → FixedComplex q) (u1 : Fin t1) :
    (cyclicBidiagSolveFixed a b Y u1).toComplex =
      cyclicBidiagSolveQuantWithMantissa q a b (fun m => (Y m).toComplex) u1 := by
  have ht1 : 0 < t1 := NeZero.pos t1
  unfold cyclicBidiagSolveFixed cyclicBidiagSolveQuantWithMantissa
  dsimp only
  by_cases hba : b ≤ a
  · rw [if_pos hba, if_pos hba]
    exact toComplex_bidiagSweepFixed t1 q a b
      (fun s => Y ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1⟩)
      (fun v => (t1 - v.val) % t1)
      (fun v => le_of_lt (Nat.mod_lt _ ht1)) u1
  · rw [if_neg hba, if_neg hba]
    exact toComplex_bidiagSweepFixed t1 q b a
      (fun s => Y ⟨s % t1, Nat.mod_lt _ ht1⟩)
      (fun v => v.val)
      (fun v => le_of_lt v.isLt) u1

theorem toComplex_cyclicBidiagSolveFixed {t1 q : ℕ} [NeZero t1] (c0 c1 : ℝ)
    (Y : Fin t1 → FixedComplex q) (u1 : Fin t1) :
    (cyclicBidiagSolveFixed (quantizeRealMantissa q c0) (quantizeRealMantissa q c1) Y u1).toComplex =
      cyclicBidiagSolveQuant q c0 c1 (fun m => (Y m).toComplex) u1 :=
  toComplex_cyclicBidiagSolveFixed_withMantissa
    (quantizeRealMantissa q c0) (quantizeRealMantissa q c1) Y u1

theorem toComplex_cyclicBidiagPrevSolveFixed_withMantissa {t1 q : ℕ} [NeZero t1] (a b : ℤ)
    (Y : Fin t1 → FixedComplex q) (u1 : Fin t1) :
    (cyclicBidiagPrevSolveFixed a b Y u1).toComplex =
      cyclicBidiagPrevSolveQuantWithMantissa q a b (fun m => (Y m).toComplex) u1 :=
  toComplex_cyclicBidiagSolveFixed_withMantissa b a (fun m => Y (cyclicNext m)) u1

theorem toComplex_cyclicBidiagPrevSolveFixed {t1 q : ℕ} [NeZero t1] (c0 c1 : ℝ)
    (Y : Fin t1 → FixedComplex q) (u1 : Fin t1) :
    (cyclicBidiagPrevSolveFixed (quantizeRealMantissa q c0) (quantizeRealMantissa q c1) Y u1).toComplex =
      cyclicBidiagPrevSolveQuant q c0 c1 (fun m => (Y m).toComplex) u1 :=
  toComplex_cyclicBidiagPrevSolveFixed_withMantissa
    (quantizeRealMantissa q c0) (quantizeRealMantissa q c1) Y u1

/-- Pure-integer column-level $O(t_1)$ 2-pass open-chain + cyclic rank-1 correction Nyquist solver
parameterized by `smul : ℤ → ℤ → ℤ` and tabulated via `memoizeFin`
(`nyquistColumnSolveFixedWithMul`). -/
def nyquistColumnSolveFixedWithMul (smul : ℤ → ℤ → ℤ) {t1 q : ℕ} (a : ℤ)
    (Y : Fin t1 → FixedComplex q) (altFixed : FixedComplex q) : Fin t1 → FixedComplex q :=
  let qWork : ℕ := q + 4
  let invC0_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a
  let B_scaledFixed : Fin t1 → FixedComplex qWork :=
    memoizeFin (fun m => FixedComplex.scaleRoundedWith smul invC0_m (FixedComplex.rescale qWork (Y m)))
  let zpartArr : Array (FixedComplex qWork) :=
    (buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_scaledFixed) t1).1
  let altPart : FixedComplex qWork :=
    ⟨∑ m : Fin t1, altSign m.val * (zpartArr.getD m.val 0).re,
     ∑ m : Fin t1, altSign m.val * (zpartArr.getD m.val 0).im⟩
  let altWork : FixedComplex qWork := FixedComplex.rescale qWork altFixed
  let corr : FixedComplex qWork := divNatFixed (altWork - altPart) t1
  memoizeFin (fun u1 =>
    FixedComplex.rescale q
      (zpartArr.getD u1.val 0 + ⟨altSign u1.val * corr.re, altSign u1.val * corr.im⟩))

/-- **Pure-Integer Column-Level $O(t_1)$ 2-Pass Open-Chain + Cyclic Rank-1 Correction Nyquist Solver
(`nyquistColumnSolveFixed`, Theorem 5.1(3) (`thm:deconv`) and Section 5.2 (`sec:solvers`))**:
Computes the reciprocal $c_{0,q}^{-1}$, scaled right-hand side `B_scaledFixed`, open-chain trajectory
`zpartArr` (via `buildRecurrenceArray`), alternating sum `altPart`, and rank-1 cyclic correction `corr`
**once for the entire column** outside `fun u1 : Fin t1 => ...` in pure `ℤ` (zero `ℚ`), and tabulates
the output column via `memoizeFin`. -/
def nyquistColumnSolveFixed {t1 q : ℕ} (a : ℤ)
    (Y : Fin t1 → FixedComplex q) (altFixed : FixedComplex q) : Fin t1 → FixedComplex q :=
  let qWork : ℕ := q + 4
  let invC0_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a
  let B_scaledFixed : Fin t1 → FixedComplex qWork :=
    memoizeFin (fun m => FixedComplex.scaleRounded invC0_m (FixedComplex.rescale qWork (Y m)))
  let zpartArr : Array (FixedComplex qWork) :=
    (buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_scaledFixed) t1).1
  let altPart : FixedComplex qWork :=
    ⟨∑ m : Fin t1, altSign m.val * (zpartArr.getD m.val 0).re,
     ∑ m : Fin t1, altSign m.val * (zpartArr.getD m.val 0).im⟩
  let altWork : FixedComplex qWork := FixedComplex.rescale qWork altFixed
  let corr : FixedComplex qWork := divNatFixed (altWork - altPart) t1
  memoizeFin (fun u1 =>
    FixedComplex.rescale q
      (zpartArr.getD u1.val 0 + ⟨altSign u1.val * corr.re, altSign u1.val * corr.im⟩))

theorem nyquistColumnSolveFixedWithMul_eq_nyquistColumnSolveFixed (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, smul a b = a * b) {t1 q : ℕ} (a : ℤ)
    (Y : Fin t1 → FixedComplex q) (altFixed : FixedComplex q) :
    nyquistColumnSolveFixedWithMul smul a Y altFixed = nyquistColumnSolveFixed a Y altFixed := by
  have hfn : smul = (· * ·) := funext fun x => funext fun y => hsmul x y
  subst hfn
  rfl

private theorem toComplex_altSign_smul {q : ℕ} (k : ℕ) (z : FixedComplex q) :
    (⟨altSign k * z.re, altSign k * z.im⟩ : FixedComplex q).toComplex =
      (-1 : ℂ) ^ k * z.toComplex := by
  have h1 : ((-1 : ℂ) ^ k).re = ((altSign k : ℤ) : ℝ) := by
    rw [← cast_altSign_complex, Complex.intCast_re]
  have h2 : ((-1 : ℂ) ^ k).im = 0 := by
    rw [← cast_altSign_complex, Complex.intCast_im]
  apply Complex.ext
  · simp [FixedComplex.toComplex_re, h1, h2, mul_assoc]
  · simp [FixedComplex.toComplex_im, h1, h2, mul_assoc]

private theorem buildRecurrenceArray_nyquistOpenChainStep_fixed_toComplex
    {t1 qWork : ℕ} (B_scaledFixed : Fin t1 → FixedComplex qWork) :
    ∀ k : ℕ,
      ((buildRecurrenceArray (0 : FixedComplex qWork)
          (nyquistOpenChainStep B_scaledFixed) k).2).toComplex =
        (buildRecurrenceArray (0 : ℂ)
          (nyquistOpenChainStep (fun m => (B_scaledFixed m).toComplex)) k).2
  | 0 => FixedComplex.toComplex_zero
  | k + 1 => by
    simp only [buildRecurrenceArray, nyquistOpenChainStep]
    split_ifs with hk
    · rw [FixedComplex.toComplex_sub_op,
        buildRecurrenceArray_nyquistOpenChainStep_fixed_toComplex B_scaledFixed k]
    · exact FixedComplex.toComplex_zero

theorem toComplex_nyquistColumnSolveFixed_withMantissa {t1 q : ℕ} (a : ℤ)
    (Y : Fin t1 → FixedComplex q) (altTrue : ℂ) (u1 : Fin t1) :
    (nyquistColumnSolveFixed a Y (quantizeComplexFixed q altTrue) u1).toComplex =
      nyquistColumnSolveQuantWithMantissa q a (fun m => (Y m).toComplex) altTrue u1 := by
  unfold nyquistColumnSolveFixed nyquistColumnSolveQuantWithMantissa
  simp only [memoizeFin_eq, quantizeComplex_toComplex]
  set qWork : ℕ := q + 4
  set c0_q : ℝ := (a : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  set invC0_m : ℤ := roundDivInt ((2 : ℤ) ^ (q + qWork)) a
  set invC0_q : ℝ := quantizeReal qWork (c0_q⁻¹)
  have hinv_eq : (invC0_m : ℝ) * (2 : ℝ) ^ (-(qWork : ℤ)) = invC0_q := by
    dsimp [invC0_m, invC0_q, quantizeReal, c0_q]
    rw [roundDivInt_two_pow_add_eq_quantizeRealMantissa_inv q qWork a]
  set B_scaledFixed : Fin t1 → FixedComplex qWork :=
    fun m => FixedComplex.scaleRounded invC0_m (FixedComplex.rescale qWork (Y m))
  set B_scaled : Fin t1 → ℂ :=
    fun m => quantizeComplex qWork ((invC0_q : ℂ) * (Y m).toComplex)
  have hB_sc : (fun m => (B_scaledFixed m).toComplex) = B_scaled := by
    funext m
    dsimp [B_scaledFixed, B_scaled]
    rw [FixedComplex.toComplex_scaleRounded, hinv_eq,
      FixedComplex.toComplex_rescale_of_le (by omega : q ≤ qWork) (Y m)]
  have hzpart : ∀ m : Fin t1,
      ((buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_scaledFixed) t1).1.getD
        m.val 0).toComplex =
      (buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) t1).1.getD m.val 0 := by
    intro m
    rw [getD_buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_scaledFixed) (le_of_lt m.isLt),
      getD_buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) (le_of_lt m.isLt),
      buildRecurrenceArray_nyquistOpenChainStep_fixed_toComplex, hB_sc]
  rw [FixedComplex.toComplex_rescale, FixedComplex.toComplex_add_op, hzpart u1,
    toComplex_altSign_smul, toComplex_divNatFixed, FixedComplex.toComplex_sub_op,
    FixedComplex.toComplex_rescale_of_le (by omega : q ≤ qWork) (quantizeComplexFixed q altTrue)]
  have halt_sum :
      (⟨∑ m : Fin t1,
          altSign m.val *
            ((buildRecurrenceArray (0 : FixedComplex qWork)
              (nyquistOpenChainStep B_scaledFixed) t1).1.getD m.val 0).re,
        ∑ m : Fin t1,
          altSign m.val *
            ((buildRecurrenceArray (0 : FixedComplex qWork)
              (nyquistOpenChainStep B_scaledFixed) t1).1.getD m.val 0).im⟩ :
          FixedComplex qWork).toComplex =
      ∑ m : Fin t1,
        (-1 : ℂ) ^ m.val *
          (buildRecurrenceArray (0 : ℂ) (nyquistOpenChainStep B_scaled) t1).1.getD m.val 0 := by
    apply Complex.ext
    · rw [FixedComplex.toComplex_re, Int.cast_sum, Finset.sum_mul, Complex.re_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← hzpart m, ← toComplex_altSign_smul, FixedComplex.toComplex_re]
    · rw [FixedComplex.toComplex_im, Int.cast_sum, Finset.sum_mul, Complex.im_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← hzpart m, ← toComplex_altSign_smul, FixedComplex.toComplex_im]
  rw [halt_sum]
  rfl

theorem toComplex_nyquistColumnSolveFixed {t1 q : ℕ} (c0 : ℝ)
    (Y : Fin t1 → FixedComplex q) (altTrue : ℂ) (u1 : Fin t1) :
    (nyquistColumnSolveFixed (quantizeRealMantissa q c0) Y
      (quantizeComplexFixed q altTrue) u1).toComplex =
      nyquistColumnSolveQuant q c0 (fun m => (Y m).toComplex) altTrue u1 :=
  toComplex_nyquistColumnSolveFixed_withMantissa (quantizeRealMantissa q c0) Y altTrue u1

/-! ### 4. Integer Schedule Tree (`ScheduleIntTree`) & Computable Schedule Generator -/

/-- Precomputed pure-integer multi-level schedule & constants tree (`ScheduleIntTree`): carries all level parameters
`(K, p, B_in)`, the spatial half-width `m1`, the integer filter taps `filterTap`, the quantized
twist roots `preTwistRoot, postTwistRoot`, the passband weight mantissas `c0Mantissa, c1Mantissa`,
and at leaf levels the **1D** quantized leaf twiddle table `leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p)`
of length $2^K = R_L$. Zero `ℝ` or `ℂ` appear in this type. -/
inductive ScheduleIntTree : (K p B_in : ℕ) → Type
  | leaf (K p B_in : ℕ)
      (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p)) :
      ScheduleIntTree K p B_in
  | node (K p B_in m1 : ℕ)
      (filterTap : Fin (t1Ell K) → ℤ → ℤ)
      (preTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
      (postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
      (c0Mantissa : Fin (rEll K) → ℤ)
      (c1Mantissa : Fin (rEll K) → ℤ)
      (child : ScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) :
      ScheduleIntTree K p B_in

/-- Fixed-point integer-mantissa accumulator for an `N`-term series:
quantizes each term `term m` to an integer mantissa at scale `2 ^ q_acc` via `quantizeRatMantissa q_acc`,
sums the integer mantissas in `ℤ` (avoiding any `ℚ` denominator growth or `gcd` across terms),
and divides by `2 ^ q_acc` once at the end. -/
def fixedPointSumRat (q_acc N : ℕ) (term : ℕ → ℚ) : ℚ :=
  ((∑ m ∈ Finset.range N, quantizeRatMantissa q_acc (term m) : ℤ) : ℚ) / (2 : ℚ) ^ q_acc

theorem abs_fixedPointSumRat_sub_sum_le (q_acc N : ℕ) (term : ℕ → ℚ) :
    |(fixedPointSumRat q_acc N term : ℝ) - ∑ m ∈ Finset.range N, (term m : ℝ)| ≤
      (N : ℝ) * (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) := by
  have hcast : (fixedPointSumRat q_acc N term : ℝ) =
      ∑ m ∈ Finset.range N, (quantizeRatMantissa q_acc (term m) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) := by
    unfold fixedPointSumRat
    push_cast
    rw [div_eq_mul_inv, Finset.sum_mul, ← zpow_natCast, zpow_neg]
  rw [hcast, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Finset.range N,
        |(quantizeRatMantissa q_acc (term m) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) - (term m : ℝ)|
      ≤ ∑ _m ∈ Finset.range N, (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [ quantizeRatMantissa_eq_quantizeRealMantissa, ← quantizeReal]
        exact abs_quantizeReal_sub_self_le q_acc (term m : ℝ)
    _ = (N : ℝ) * (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) := by
        simp [mul_assoc]

theorem abs_fixedPointSumRat_add_sub_sum_le (q N : ℕ) (term : ℕ → ℚ) :
    |(fixedPointSumRat (q + N) N term : ℝ) - ∑ m ∈ Finset.range N, (term m : ℝ)| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  refine (abs_fixedPointSumRat_sub_sum_le (q + N) N term).trans ?_
  have hN : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
  have hzpow : (2 : ℝ) ^ (-((q + N : ℕ) : ℤ)) = (2 : ℝ) ^ (-(N : ℤ)) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hexp : -((q + N : ℕ) : ℤ) = -(N : ℤ) + -(q : ℤ) := by omega
    rw [hexp, zpow_add₀ (by norm_num)]
  have hcancel : (2 : ℝ) ^ N * (2 : ℝ) ^ (-(N : ℤ)) = 1 := two_pow_mul_two_zpow_neg N
  calc (N : ℝ) * (1 / 2 : ℝ) * (2 : ℝ) ^ (-((q + N : ℕ) : ℤ))
      ≤ (2 : ℝ) ^ N * (1 / 2 : ℝ) * ((2 : ℝ) ^ (-(N : ℤ)) * (2 : ℝ) ^ (-(q : ℤ))) := by
        rw [hzpow]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN (by norm_num)) (by positivity)
    _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ N * (2 : ℝ) ^ (-(N : ℤ))) * (2 : ℝ) ^ (-(q : ℤ)) := by ring
    _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by rw [hcancel, mul_one]

/-- Unrounded dyadic-rational Taylor series sum for $\ln 2$. -/
def rawApproxLogTwoRat (S : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (S + 1), (1 / 2 : ℚ) ^ (i + 1) / ((i : ℚ) + 1)

theorem abs_rawApproxLogTwoRat_sub_log_two_le (S : ℕ) :
    |(rawApproxLogTwoRat S : ℝ) - Real.log 2| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
  have hbound := Real.abs_log_sub_add_sum_range_le (x := (1 / 2 : ℝ))
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) (S + 1)
  have hlog : Real.log (1 - (1 / 2 : ℝ)) = -Real.log 2 := by
    have h1 : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
    rw [h1, Real.log_inv]
  have hcast : (∑ i ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) =
      (rawApproxLogTwoRat S : ℝ) := by
    unfold rawApproxLogTwoRat
    push_cast
    rfl
  rw [hcast, hlog, ← sub_eq_add_neg] at hbound
  have hrhs : ‖(1 / 2 : ℝ)‖ ^ (S + 1 + 1) / (1 - ‖(1 / 2 : ℝ)‖) ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
    have hnorm : ‖(1 / 2 : ℝ)‖ = (2 : ℝ)⁻¹ := by norm_num
    have h1 : (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
    rw [hnorm, h1, pow_succ, mul_div_cancel_right₀ _ (by norm_num)]
    calc ((2 : ℝ)⁻¹) ^ (S + 1)
        ≤ ((2 : ℝ)⁻¹) ^ S := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ S)
      _ = (2 : ℝ) ^ (-(S : ℤ)) := by rw [inv_pow, ← zpow_natCast, zpow_neg]
  exact hbound.trans hrhs

/-- Pure-integer rounding error bound for `roundDivInt`: for all `q_acc : ℕ` and `num den : ℤ`,
`|(roundDivInt num den : ℝ) * 2^(-q_acc) - (num / den) * 2^(-q_acc)| ≤ (1/2) * 2^(-q_acc)`. -/
theorem abs_roundDivInt_mul_zpow_sub_le (q_acc : ℕ) (num den : ℤ) :
    |(roundDivInt num den : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
      ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ (-(q_acc : ℤ))| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) := by
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ (-(q_acc : ℤ)) := zpow_pos (by norm_num) _
  rw [← sub_mul, abs_mul, abs_of_pos hzpos, roundDivInt_eq_floor_div_add_half]
  exact mul_le_mul_of_nonneg_right (abs_floor_add_half_sub_le _) hzpos.le

theorem getD_default_buildRecurrenceArray {α : Type*} (init d : α) (step : ℕ → α → α)
    {N m : ℕ} (hm : m ≤ N) :
    ((buildRecurrenceArray init step N).1).getD m d =
      (buildRecurrenceArray init step m).2 := by
  have hsz : m < (buildRecurrenceArray init step N).1.size := by
    rw [size_buildRecurrenceArray]
    omega
  have h1 : ((buildRecurrenceArray init step N).1).getD m d =
      ((buildRecurrenceArray init step N).1).getD m init := by
    simp [Array.getD, hsz]
  rw [h1, getD_buildRecurrenceArray init step hm]

/-- Pure-integer $i$-th mantissa term $\mathrm{roundDivInt}(2^{q_{\text{acc}} - (i + 1)}, i + 1)$
for the dyadic series of $\ln 2$. -/
def approxLogTwoTermFixed (q_acc i : ℕ) : ℤ :=
  roundDivInt ((2 : ℤ) ^ (q_acc - (i + 1))) ((i + 1 : ℕ) : ℤ)

theorem approxLogTwoTermFixed_eq_quantizeRatMantissa {q_acc i : ℕ} (hi : i + 1 ≤ q_acc) :
    approxLogTwoTermFixed q_acc i =
      quantizeRatMantissa q_acc ((1 / 2 : ℚ) ^ (i + 1) / ((i : ℚ) + 1)) := by
  unfold approxLogTwoTermFixed
  rw [roundDivInt_eq_floor_div_add_half, quantizeRatMantissa_eq_quantizeRealMantissa]
  unfold quantizeRealMantissa
  congr 2
  have hpow : (2 : ℝ) ^ q_acc = (2 : ℝ) ^ (q_acc - (i + 1)) * (2 : ℝ) ^ (i + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have h2i : (2 : ℝ) ^ (i + 1) ≠ 0 := by positivity
  push_cast
  rw [one_div, inv_pow, hpow]
  field_simp [h2i]

/-- Pure-integer fixed-point Taylor series approximation to $\ln 2$
(Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def approxLogTwoRat (S : ℕ) : ℚ :=
  let q_acc : ℕ := S + (S + 2)
  ((∑ i ∈ Finset.range (S + 2), approxLogTwoTermFixed q_acc i : ℤ) : ℚ) / (2 : ℚ) ^ q_acc

theorem approxLogTwoRat_eq_fixedPointSumRat (S : ℕ) :
    approxLogTwoRat S =
      fixedPointSumRat (S + (S + 2)) (S + 2) (fun i => (1 / 2 : ℚ) ^ (i + 1) / ((i : ℚ) + 1)) := by
  have hsum : (∑ i ∈ Finset.range (S + 2), approxLogTwoTermFixed (S + (S + 2)) i) =
      ∑ i ∈ Finset.range (S + 2),
        quantizeRatMantissa (S + (S + 2)) ((1 / 2 : ℚ) ^ (i + 1) / ((i : ℚ) + 1)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact approxLogTwoTermFixed_eq_quantizeRatMantissa (by omega)
  unfold approxLogTwoRat fixedPointSumRat
  dsimp only
  rw [hsum]

theorem approxLogTwoRat_nonneg (S : ℕ) : 0 ≤ approxLogTwoRat S := by
  rw [approxLogTwoRat_eq_fixedPointSumRat]
  unfold fixedPointSumRat
  have hsum : (0 : ℤ) ≤ ∑ i ∈ Finset.range (S + 2),
      quantizeRatMantissa (S + (S + 2)) ((1 / 2 : ℚ) ^ (i + 1) / ((i : ℚ) + 1)) := by
    refine Finset.sum_nonneg fun i _ => ?_
    unfold quantizeRatMantissa
    exact Int.floor_nonneg.mpr (by positivity)
  have hsum_q : (0 : ℚ) ≤ ((∑ i ∈ Finset.range (S + 2),
      quantizeRatMantissa (S + (S + 2)) ((1 / 2 : ℚ) ^ (i + 1) / ((i : ℚ) + 1)) : ℤ) : ℚ) := by
    exact_mod_cast hsum
  exact div_nonneg hsum_q (by positivity)

/-- Error bound for `approxLogTwoRat`:
$|\text{approxLogTwoRat}(S) - \ln 2| \le 2^{-S}$ for all $S \in \mathbb{N}$. -/
theorem abs_approxLogTwoRat_sub_log_two_le (S : ℕ) :
    |(approxLogTwoRat S : ℝ) - Real.log 2| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
  have hfp : |(approxLogTwoRat S : ℝ) - (rawApproxLogTwoRat (S + 1) : ℝ)| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) := by
    rw [approxLogTwoRat_eq_fixedPointSumRat]
    unfold rawApproxLogTwoRat
    rw [Rat.cast_sum]
    exact abs_fixedPointSumRat_add_sub_sum_le S (S + 2) _
  have hraw : |(rawApproxLogTwoRat (S + 1) : ℝ) - Real.log 2| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have h := abs_rawApproxLogTwoRat_sub_log_two_le (S + 1)
    have hexp : -((S + 1 : ℕ) : ℤ) = (-1 : ℤ) + -(S : ℤ) := by omega
    have h2_inv : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
    rw [hexp, zpow_add₀ (by norm_num), h2_inv] at h
    exact h
  have htri := abs_sub_le (approxLogTwoRat S : ℝ) (rawApproxLogTwoRat (S + 1) : ℝ) (Real.log 2)
  linarith

theorem approxLogTwoRat_le_one (S : ℕ) : (approxLogTwoRat S : ℝ) ≤ 2 := by
  have h := abs_approxLogTwoRat_sub_log_two_le S
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hpow : (2 : ℝ) ^ (-(S : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  linarith [(abs_le.mp h).2]

/-- Unrounded rational Taylor polynomial of $\arctan(x)$. -/
def rawArctanTaylorRat (N : ℕ) (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range N, (-1 : ℚ) ^ m * x ^ (2 * m + 1) / (2 * (m : ℚ) + 1)

theorem abs_rawArctanTaylorRat_sub_arctan_le (N : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    |(rawArctanTaylorRat N x : ℝ) - Real.arctan (x : ℝ)| ≤ (1 / 2 : ℝ) ^ (2 * N) := by
  have hr0 : (0 : ℝ) ≤ (x : ℝ) := Rat.cast_nonneg.mpr hx0
  have hr1 : (x : ℝ) ≤ 1 / 2 := by
    have : (x : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hx1
    norm_num at this
    exact this
  set r : ℝ := (x : ℝ)
  have harctan : Real.arctan r = ∫ t : ℝ in (0 : ℝ)..r, (1 + t ^ 2)⁻¹ := by
    rw [integral_inv_one_add_sq, Real.arctan_zero, sub_zero]
  have hsum_int : (rawArctanTaylorRat N x : ℝ) =
      ∫ t : ℝ in (0 : ℝ)..r, ∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * t ^ (2 * m) := by
    rw [intervalIntegral.integral_finset_sum]
    · unfold rawArctanTaylorRat
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega : 2 * m + 1 ≠ 0),
        sub_zero]
      push_cast
      ring
    · intro m _
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hint1 : IntervalIntegrable (fun t : ℝ => ∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * t ^ (2 * m))
      MeasureTheory.volume (0 : ℝ) r :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 + t ^ 2)⁻¹) MeasureTheory.volume (0 : ℝ) r :=
    (Continuous.inv₀ (by fun_prop) (fun t => by positivity)).intervalIntegrable _ _
  have hdiff : (rawArctanTaylorRat N x : ℝ) - Real.arctan r =
      ∫ t : ℝ in (0 : ℝ)..r,
        ((∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * t ^ (2 * m)) - (1 + t ^ 2)⁻¹) := by
    rw [hsum_int, harctan, ← intervalIntegral.integral_sub hint1 hint2]
  rw [hdiff, ← Real.norm_eq_abs]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) r,
      ‖(∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * t ^ (2 * m)) - (1 + t ^ 2)⁻¹‖ ≤
        (1 / 2 : ℝ) ^ (2 * N) := by
    intro t ht
    rw [Set.uIoc_of_le hr0] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 / 2 := ht.2.trans hr1
    have hu_ne : -(t ^ 2) ≠ (1 : ℝ) := by nlinarith [sq_nonneg t]
    have hgeom : (∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * t ^ (2 * m)) =
        (1 - (-(t ^ 2)) ^ N) / (1 + t ^ 2) := by
      have hterm : (fun m : ℕ => (-1 : ℝ) ^ m * t ^ (2 * m)) = (fun m : ℕ => (-(t ^ 2)) ^ m) := by
        ext m; ring
      rw [hterm, geom_sum_eq hu_ne]
      have hden : -(t ^ 2) - 1 = -(1 + t ^ 2) := by ring
      rw [hden, div_neg, ← neg_div, neg_sub]
    have hrem : (∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * t ^ (2 * m)) - (1 + t ^ 2)⁻¹ =
        -((- (t ^ 2)) ^ N) / (1 + t ^ 2) := by
      rw [hgeom, inv_eq_one_div]; ring
    rw [hrem, Real.norm_eq_abs, abs_div, abs_neg, abs_pow, abs_neg, abs_of_nonneg (sq_nonneg t),
      abs_of_pos (by positivity : 0 < 1 + t ^ 2), ← pow_mul]
    calc t ^ (2 * N) / (1 + t ^ 2)
        ≤ t ^ (2 * N) / 1 := div_le_div_of_nonneg_left (pow_nonneg ht0 _) zero_lt_one
          (by linarith [sq_nonneg t])
      _ = t ^ (2 * N) := div_one _
      _ ≤ (1 / 2 : ℝ) ^ (2 * N) := pow_le_pow_left₀ ht0 ht1 (2 * N)
  calc ‖∫ t : ℝ in (0 : ℝ)..r,
          ((∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * t ^ (2 * m)) - (1 + t ^ 2)⁻¹)‖
      ≤ (1 / 2 : ℝ) ^ (2 * N) * |r - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ (1 / 2 : ℝ) ^ (2 * N) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sub_zero, abs_of_nonneg hr0]
        linarith
    _ = (1 / 2 : ℝ) ^ (2 * N) := mul_one _

/-- Single step of the pure-integer power recurrence $P_{m+1} = \mathrm{roundDivInt}(P_m, k^2)$
for $(1/k)^{2m+1}$. -/
def arctanInvPowStepFixed (k : ℕ) (_m : ℕ) (P_m : ℤ) : ℤ :=
  roundDivInt P_m ((k * k : ℕ) : ℤ)

/-- Single-pass $O(N)$ pure-integer recurrence array for $P_m \approx (1/k)^{2m+1} \cdot 2^{q_{\text{acc}}}$
computed via `buildRecurrenceArray` with zero rational exponentiation. -/
def arctanInvPowArrayFixed (k q_acc N : ℕ) : Array ℤ :=
  (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
    (arctanInvPowStepFixed k) N).1

private theorem abs_buildRecurrenceArray_arctanInvPowStepFixed_sub_le
    {k : ℕ} (hk : 1 ≤ k) (q_acc : ℕ) :
    ∀ m : ℕ,
      |(((buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
          (arctanInvPowStepFixed k) m).2 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
        (1 / (k : ℝ)) ^ (2 * m + 1)| ≤
      ((m + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
  have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk2_r : (1 : ℝ) ≤ ((k * k : ℕ) : ℝ) := by
    have : 1 ≤ k * k := Nat.mul_le_mul hk hk
    exact_mod_cast this
  intro m
  induction m with
  | zero =>
    simp only [buildRecurrenceArray, Nat.mul_zero, zero_add, pow_one, Nat.cast_one, one_mul]
    have hstep := abs_roundDivInt_mul_zpow_sub_le q_acc ((2 : ℤ) ^ q_acc) (k : ℤ)
    have htarget : ((((2 : ℤ) ^ q_acc : ℤ) : ℝ) / ((k : ℤ) : ℝ)) * (2 : ℝ) ^ (-(q_acc : ℤ)) =
        1 / (k : ℝ) := by
      have hcancel := two_pow_mul_two_zpow_neg q_acc
      push_cast
      calc ((2 : ℝ) ^ q_acc / (k : ℝ)) * (2 : ℝ) ^ (-(q_acc : ℤ))
          = ((2 : ℝ) ^ q_acc * (2 : ℝ) ^ (-(q_acc : ℤ))) / (k : ℝ) := by ring
        _ = 1 / (k : ℝ) := by rw [hcancel]
    rwa [htarget] at hstep
  | succ m ih =>
    simp only [buildRecurrenceArray, arctanInvPowStepFixed]
    set P_m : ℤ := (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
      (arctanInvPowStepFixed k) m).2
    set p_m : ℝ := (P_m : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))
    set u_m : ℝ := (1 / (k : ℝ)) ^ (2 * m + 1)
    have hstep := abs_roundDivInt_mul_zpow_sub_le q_acc P_m ((k * k : ℕ) : ℤ)
    have htarget : ((P_m : ℝ) / (((k * k : ℕ) : ℤ) : ℝ)) * (2 : ℝ) ^ (-(q_acc : ℤ)) =
        p_m / ((k * k : ℕ) : ℝ) := by
      dsimp [p_m]
      push_cast
      ring
    rw [htarget] at hstep
    have hu_succ : (1 / (k : ℝ)) ^ (2 * (m + 1) + 1) = u_m / ((k * k : ℕ) : ℝ) := by
      have hexp : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
      rw [hexp, pow_add]
      dsimp [u_m]
      push_cast
      field_simp [hk_pos.ne']
    rw [hu_succ]
    have hdiv : |p_m / ((k * k : ℕ) : ℝ) - u_m / ((k * k : ℕ) : ℝ)| ≤ |p_m - u_m| := by
      rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((k * k : ℕ) : ℝ))]
      exact div_le_self (abs_nonneg _) hk2_r
    have htri := abs_sub_le
      ((roundDivInt P_m ((k * k : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))
      (p_m / ((k * k : ℕ) : ℝ))
      (u_m / ((k * k : ℕ) : ℝ))
    have hm_cast : ((m + 1 + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) =
        ((m + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) +
          ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
      push_cast; ring
    rw [hm_cast]
    linarith

/-- Pure-integer single-pass fixed-point Taylor polynomial of $\arctan(1/k)$
(Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def arctanInvTaylorRat (N k : ℕ) : ℚ :=
  let q_acc : ℕ := 4 * N + 6
  let arr : Array ℤ := arctanInvPowArrayFixed k q_acc N
  ((∑ m ∈ Finset.range (N + 1),
      altSign m * roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℚ) /
    (2 : ℚ) ^ q_acc

/-- Remainder bound for `arctanInvTaylorRat`: for $k \ge 2$,
$|\text{arctanInvTaylorRat}(N, k) - \arctan(1/k)| \le 2^{-2N}$. -/
theorem abs_arctanInvTaylorRat_sub_arctan_le (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    |(arctanInvTaylorRat N k : ℝ) - Real.arctan (1 / (k : ℝ))| ≤ (1 / 2 : ℝ) ^ (2 * N) := by
  set q_acc : ℕ := 4 * N + 6
  set arr : Array ℤ := arctanInvPowArrayFixed k q_acc N
  set x : ℚ := 1 / (k : ℚ)
  have hk1 : 1 ≤ k := by omega
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 / 2 := by
    dsimp [x]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)
  have hcast_sum : (arctanInvTaylorRat N k : ℝ) =
      ∑ m ∈ Finset.range (N + 1),
        (altSign m : ℝ) * ((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) *
          (2 : ℝ) ^ (-(q_acc : ℤ))) := by
    change ((((∑ m ∈ Finset.range (N + 1),
        altSign m * roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℚ) /
      (2 : ℚ) ^ q_acc : ℚ) : ℝ) = _
    push_cast
    rw [div_eq_mul_inv, Finset.sum_mul, ← zpow_natCast (2 : ℝ) q_acc, ← zpow_neg]
    refine Finset.sum_congr rfl fun m _ => by ring
  have hraw_sum : (rawArctanTaylorRat (N + 1) x : ℝ) =
      ∑ m ∈ Finset.range (N + 1),
        (altSign m : ℝ) * ((1 / (k : ℝ)) ^ (2 * m + 1) / (2 * (m : ℝ) + 1)) := by
    unfold rawArctanTaylorRat
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [cast_altSign_real]
    dsimp [x]
    push_cast
    ring
  have hterm_err : ∀ m ∈ Finset.range (N + 1),
      |(altSign m : ℝ) * ((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) *
          (2 : ℝ) ^ (-(q_acc : ℤ))) -
        (altSign m : ℝ) * ((1 / (k : ℝ)) ^ (2 * m + 1) / (2 * (m : ℝ) + 1))| ≤
      ((N + 2 : ℕ) : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm_le : m ≤ N := by omega
    rw [← mul_sub, abs_mul, cast_altSign_real, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hget : arr.getD m 0 =
        (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
          (arctanInvPowStepFixed k) m).2 :=
      getD_default_buildRecurrenceArray
        (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ)) 0 (arctanInvPowStepFixed k) hm_le
    rw [hget]
    set P_m : ℤ := (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
      (arctanInvPowStepFixed k) m).2
    set p_m : ℝ := (P_m : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))
    set u_m : ℝ := (1 / (k : ℝ)) ^ (2 * m + 1)
    have hrec := abs_buildRecurrenceArray_arctanInvPowStepFixed_sub_le hk1 q_acc m
    have hdiv_step := abs_roundDivInt_mul_zpow_sub_le q_acc P_m ((2 * m + 1 : ℕ) : ℤ)
    have htarget : ((P_m : ℝ) / (((2 * m + 1 : ℕ) : ℤ) : ℝ)) * (2 : ℝ) ^ (-(q_acc : ℤ)) =
        p_m / (2 * (m : ℝ) + 1) := by
      dsimp [p_m]
      push_cast
      ring
    rw [htarget] at hdiv_step
    have h2m1_ge1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hdiv_le : |p_m / (2 * (m : ℝ) + 1) - u_m / (2 * (m : ℝ) + 1)| ≤ |p_m - u_m| := by
      rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * (m : ℝ) + 1)]
      exact div_le_self (abs_nonneg _) h2m1_ge1
    have htri := abs_sub_le
      ((roundDivInt P_m ((2 * m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))
      (p_m / (2 * (m : ℝ) + 1))
      (u_m / (2 * (m : ℝ) + 1))
    have hm_N : ((m + 1 : ℕ) : ℝ) + 1 ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 2 ≤ N + 2)
    have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) := by positivity
    nlinarith
  have hfp : |(arctanInvTaylorRat N k : ℝ) - (rawArctanTaylorRat (N + 1) x : ℝ)| ≤
      (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (2 * N) := by
    rw [hcast_sum, hraw_sum, ← Finset.sum_sub_distrib]
    have hsum_le :
        |∑ m ∈ Finset.range (N + 1),
          ((altSign m : ℝ) * ((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) *
              (2 : ℝ) ^ (-(q_acc : ℤ))) -
            (altSign m : ℝ) * ((1 / (k : ℝ)) ^ (2 * m + 1) / (2 * (m : ℝ) + 1)))| ≤
        ((N + 1 : ℕ) : ℝ) * (((N + 2 : ℕ) : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simpa using Finset.sum_le_sum hterm_err
    refine hsum_le.trans ?_
    have hN1 : ((N + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := N + 1)).le
    have hN2 : ((N + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N + 2) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := N + 2)).le
    have hprod_le : ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * N + 3) := by
      calc ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (N + 2) :=
            mul_le_mul hN1 hN2 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (2 * N + 3) := by rw [← pow_add]; congr 1; omega
    have hzpow : (2 : ℝ) ^ (2 * N + 3) * (2 : ℝ) ^ (-(q_acc : ℤ)) ≤ (1 / 2 : ℝ) ^ (2 * N) := by
      rw [← zpow_natCast (2 : ℝ) (2 * N + 3), ← zpow_add₀ (by norm_num),
        one_div, inv_pow, ← zpow_natCast (2 : ℝ) (2 * N), ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by dsimp [q_acc]; omega)
    have hzpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(q_acc : ℤ)) := by positivity
    calc ((N + 1 : ℕ) : ℝ) * (((N + 2 : ℕ) : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))))
        = (1 / 2 : ℝ) * ((((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by ring
      _ ≤ (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * N + 3) * (2 : ℝ) ^ (-(q_acc : ℤ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod_le hzpos) (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (2 * N) :=
          mul_le_mul_of_nonneg_left hzpow (by norm_num)
  have hraw : |(rawArctanTaylorRat (N + 1) x : ℝ) - Real.arctan (1 / (k : ℝ))| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (2 * N) := by
    have h := abs_rawArctanTaylorRat_sub_arctan_le (N + 1) hx0 hx1
    have hx_cast : (x : ℝ) = 1 / (k : ℝ) := by dsimp [x]; push_cast; rfl
    rw [hx_cast] at h
    have h2 : 2 * (N + 1) = 2 * N + 2 := by omega
    have hpow2 : (1 / 2 : ℝ) ^ (2 * N + 2) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (2 * N) := by
      rw [pow_add]; ring
    rw [h2, hpow2] at h
    exact h
  have htri := abs_sub_le (arctanInvTaylorRat N k : ℝ) (rawArctanTaylorRat (N + 1) x : ℝ)
    (Real.arctan (1 / (k : ℝ)))
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * N) := by positivity
  linarith

/-- Computable rational Machin-like approximation to $\pi = 4(\arctan(1/2) + \arctan(1/3))$
(Lemma 3.2 (`lem:elementary`); Table 3 (`tab:lean-map`) in Section 8 (`sec:lean`)). -/
def approxPiRat (S : ℕ) : ℚ :=
  4 * (arctanInvTaylorRat (S + 3) 2 + arctanInvTaylorRat (S + 3) 3)

/-- Error bound for `approxPiRat`:
$|\text{approxPiRat}(S) - \pi| \le 2^{-S}$ for all $S \in \mathbb{N}$. -/
theorem abs_approxPiRat_sub_pi_le (S : ℕ) :
    |(approxPiRat S : ℝ) - Real.pi| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
  have hpi : Real.pi = 4 * (Real.arctan (1 / 2) + Real.arctan (1 / 3)) := by
    linarith [Real.arctan_inv_2_add_arctan_inv_3]
  have h1 := abs_arctanInvTaylorRat_sub_arctan_le (S + 3) (k := 2) (by norm_num)
  have h2 := abs_arctanInvTaylorRat_sub_arctan_le (S + 3) (k := 3) (by norm_num)
  unfold approxPiRat
  push_cast at h1 h2 ⊢
  have hsub : 4 * ((arctanInvTaylorRat (S + 3) 2 : ℝ) + (arctanInvTaylorRat (S + 3) 3 : ℝ)) - Real.pi =
      4 * (((arctanInvTaylorRat (S + 3) 2 : ℝ) - Real.arctan (1 / 2)) +
           ((arctanInvTaylorRat (S + 3) 3 : ℝ) - Real.arctan (1 / 3))) := by
    linarith [hpi]
  rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have htri := (abs_add_le
    ((arctanInvTaylorRat (S + 3) 2 : ℝ) - Real.arctan (1 / 2))
    ((arctanInvTaylorRat (S + 3) 3 : ℝ) - Real.arctan (1 / 3))).trans (add_le_add h1 h2)
  have hpow : 4 * ((1 / 2 : ℝ) ^ (2 * (S + 3)) + (1 / 2 : ℝ) ^ (2 * (S + 3))) ≤
      (2 : ℝ) ^ (-(S : ℤ)) := by
    have h4 : 4 * ((1 / 2 : ℝ) ^ (2 * (S + 3)) + (1 / 2 : ℝ) ^ (2 * (S + 3))) =
        (1 / 2 : ℝ) ^ (2 * S + 3) := by
      have : 2 * (S + 3) = (2 * S + 3) + 3 := by omega
      rw [this, pow_add]
      ring
    rw [h4]
    calc (1 / 2 : ℝ) ^ (2 * S + 3)
        ≤ (1 / 2 : ℝ) ^ S := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (2 : ℝ) ^ (-(S : ℤ)) := by rw [one_div, inv_pow, ← zpow_natCast, zpow_neg]
  linarith

theorem approxPiRat_nonneg (S : ℕ) : 0 ≤ (approxPiRat S : ℝ) := by
  have h := abs_approxPiRat_sub_pi_le S
  have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hpow : (2 : ℝ) ^ (-(S : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  linarith [(abs_le.mp h).1]

theorem approxPiRat_le_five (S : ℕ) : (approxPiRat S : ℝ) ≤ 5 := by
  have h := abs_approxPiRat_sub_pi_le S
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpow : (2 : ℝ) ^ (-(S : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  linarith [(abs_le.mp h).2]

/-- Computable dyadic integer square root approximation $\lfloor \sqrt{\max(0, Y) \cdot 4^S} \rfloor / 2^S$
(Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def approxSqrtRat (S : ℕ) (Y : ℚ) : ℚ :=
  (Nat.sqrt ⌊max 0 Y * (4 : ℚ) ^ S⌋₊ : ℚ) / (2 : ℚ) ^ S

theorem approxSqrtRat_nonneg (S : ℕ) (Y : ℚ) : 0 ≤ approxSqrtRat S Y := by
  unfold approxSqrtRat
  positivity

/-- Error bound for `approxSqrtRat`: for $Y \ge 0$,
$|\text{approxSqrtRat}(S, Y) - \sqrt{Y}| \le 2^{-S}$. -/
theorem abs_approxSqrtRat_sub_sqrt_le (S : ℕ) {Y : ℚ} (hY : 0 ≤ Y) :
    |(approxSqrtRat S Y : ℝ) - Real.sqrt (Y : ℝ)| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
  unfold approxSqrtRat
  rw [max_eq_right hY]
  set N : ℕ := ⌊Y * (4 : ℚ) ^ S⌋₊
  set k : ℕ := Nat.sqrt N
  have hY4 : 0 ≤ Y * (4 : ℚ) ^ S := by positivity
  have hN_le : (N : ℚ) ≤ Y * (4 : ℚ) ^ S := Nat.floor_le hY4
  have hN_lt : Y * (4 : ℚ) ^ S < (N : ℚ) + 1 := Nat.lt_floor_add_one _
  have hk_sq : k ^ 2 ≤ N := by rw [sq]; exact Nat.sqrt_le N
  have hN_succ_sq : N + 1 ≤ (k + 1) ^ 2 := by
    rw [sq]
    exact Nat.lt_succ_sqrt N
  have h4 : (4 : ℝ) ^ S = (2 : ℝ) ^ (2 * S) := by
    rw [pow_mul]; norm_num
  have hk_sq_R : (k : ℝ) ^ 2 ≤ (Y : ℝ) * (2 : ℝ) ^ (2 * S) := by
    have h1 : (k : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hk_sq
    have h2 : (N : ℝ) ≤ (Y : ℝ) * (4 : ℝ) ^ S := by exact_mod_cast hN_le
    rw [h4] at h2
    linarith
  have hk1_sq_R : (Y : ℝ) * (2 : ℝ) ^ (2 * S) ≤ ((k : ℝ) + 1) ^ 2 := by
    have h1 : (Y : ℝ) * (4 : ℝ) ^ S < (N : ℝ) + 1 := by exact_mod_cast hN_lt
    have h2 : (N : ℝ) + 1 ≤ ((k : ℝ) + 1) ^ 2 := by exact_mod_cast hN_succ_sq
    rw [h4] at h1
    linarith
  have hsqrt_scale : Real.sqrt ((Y : ℝ) * (2 : ℝ) ^ (2 * S)) = Real.sqrt (Y : ℝ) * (2 : ℝ) ^ S := by
    have hY_R : 0 ≤ (Y : ℝ) := Rat.cast_nonneg.mpr hY
    have h2S : (2 : ℝ) ^ (2 * S) = ((2 : ℝ) ^ S) ^ 2 := by ring
    rw [Real.sqrt_mul hY_R, h2S, Real.sqrt_sq (by positivity)]
  have hk_le : (k : ℝ) ≤ Real.sqrt (Y : ℝ) * (2 : ℝ) ^ S := by
    rw [← hsqrt_scale, ← Real.sqrt_sq (Nat.cast_nonneg k)]
    exact Real.sqrt_le_sqrt hk_sq_R
  have hk1_ge : Real.sqrt (Y : ℝ) * (2 : ℝ) ^ S ≤ (k : ℝ) + 1 := by
    rw [← hsqrt_scale, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    exact Real.sqrt_le_sqrt hk1_sq_R
  have h2S_pos : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
  push_cast
  rw [abs_le]
  have hdiv1 : (k : ℝ) / (2 : ℝ) ^ S ≤ Real.sqrt (Y : ℝ) :=
    (div_le_iff₀ h2S_pos).mpr hk_le
  have hdiv2 : Real.sqrt (Y : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ S + 1 / (2 : ℝ) ^ S := by
    rw [← add_div, le_div_iff₀ h2S_pos]
    exact hk1_ge
  have hzpow : 1 / (2 : ℝ) ^ S = (2 : ℝ) ^ (-(S : ℤ)) := by
    rw [one_div, ← zpow_natCast, zpow_neg]
  constructor <;> linarith

/-- General complex exponential Taylor series bound: for $\|z\| \le B$ and $N = 4B + q + 1$,
$\left\|e^z - \sum_{m=0}^{N-1} \frac{z^m}{m!}\right\| \le 2^{-q}$. -/
theorem norm_exp_sub_sum_range_le_two_zpow {z : ℂ} (B q : ℕ) (hz : ‖z‖ ≤ (B : ℝ)) :
    ‖Complex.exp z - ∑ m ∈ Finset.range (4 * B + q + 1), z ^ m / (m.factorial : ℂ)‖ ≤
      (2 : ℝ) ^ (-(q : ℤ)) := by
  set N : ℕ := 4 * B + q + 1
  have hcond : ‖z‖ / (N.succ : ℝ) ≤ 1 / 2 := by
    rw [Nat.cast_succ, div_le_iff₀ (by positivity)]
    have hBN : 2 * (B : ℝ) ≤ (N : ℝ) + 1 := by
      have : 2 * B ≤ N + 1 := by omega
      exact_mod_cast this
    linarith
  have hexp := Complex.exp_bound' hcond
  have hfac_pos : (0 : ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hpow_le : ‖z‖ ^ N / (N.factorial : ℝ) * 2 ≤ (B : ℝ) ^ N / (N.factorial : ℝ) * 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hz N) hfac_pos.le
  have hB_fac : (B : ℝ) ^ N / (N.factorial : ℝ) * 2 ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
    have hpow_exp := Real.pow_div_factorial_le_exp (2 * (B : ℝ)) (by positivity) N
    have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have hmul_pow : (2 * (B : ℝ)) ^ N = (2 : ℝ) ^ N * (B : ℝ) ^ N := mul_pow 2 (B : ℝ) N
    have hexp_le : Real.exp (2 * (B : ℝ)) ≤ (2 : ℝ) ^ (4 * B) := by
      have he1 : Real.exp 1 ≤ (2 : ℝ) ^ 2 := by linarith [Real.exp_one_lt_d9]
      have hnat : (2 * (B : ℝ)) = ((2 * B : ℕ) : ℝ) * 1 := by push_cast; ring
      rw [hnat, Real.exp_nat_mul]
      calc (Real.exp 1) ^ (2 * B)
          ≤ ((2 : ℝ) ^ 2) ^ (2 * B) := pow_le_pow_left₀ (Real.exp_pos 1).le he1 (2 * B)
        _ = (2 : ℝ) ^ (4 * B) := by rw [← pow_mul]; ring_nf
    have hdiv_le : (B : ℝ) ^ N / (N.factorial : ℝ) ≤ (2 : ℝ) ^ (4 * B) / (2 : ℝ) ^ N := by
      rw [le_div_iff₀ h2N_pos, mul_comm, ← mul_div_assoc, ← hmul_pow]
      exact hpow_exp.trans hexp_le
    calc (B : ℝ) ^ N / (N.factorial : ℝ) * 2
        ≤ ((2 : ℝ) ^ (4 * B) / (2 : ℝ) ^ N) * 2 :=
          mul_le_mul_of_nonneg_right hdiv_le (by norm_num)
      _ = (2 : ℝ) ^ (-(q : ℤ)) := by
          have hN_eq : N = 4 * B + (q + 1) := by omega
          rw [hN_eq, pow_add, pow_succ', ← div_div, div_self (by positivity : (2 : ℝ) ^ (4 * B) ≠ 0),
            ← zpow_natCast, zpow_neg]
          have h2q : (2 : ℝ) ^ q ≠ 0 := by positivity
          field_simp [h2q]
  exact hexp.trans (hpow_le.trans hB_fac)

/-- Unrounded rational Taylor polynomial of $\exp(x)$. -/
def rawExpTaylorRat (N : ℕ) (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range N, x ^ m / (m.factorial : ℚ)

theorem abs_rawExpTaylorRat_sub_exp_le (B q : ℕ) {x : ℚ} (hx : |(x : ℝ)| ≤ (B : ℝ)) :
    |(rawExpTaylorRat (4 * B + q + 1) x : ℝ) - Real.exp (x : ℝ)| ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  have hz : ‖((x : ℝ) : ℂ)‖ ≤ (B : ℝ) := by simpa [Complex.norm_real] using hx
  have h := norm_exp_sub_sum_range_le_two_zpow B q hz
  have hcast : Complex.exp ((x : ℝ) : ℂ) -
      ∑ m ∈ Finset.range (4 * B + q + 1), ((x : ℝ) : ℂ) ^ m / (m.factorial : ℂ) =
      ((Real.exp (x : ℝ) - (rawExpTaylorRat (4 * B + q + 1) x : ℝ) : ℝ) : ℂ) := by
    unfold rawExpTaylorRat
    rw [← Complex.ofReal_exp]
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at h
  exact h

/-- Dyadic rational quantization $2^{-q} \lfloor 2^q x + 1/2 \rfloor \in \mathbb{Q}$. -/
def quantizeRat (q : ℕ) (x : ℚ) : ℚ :=
  (quantizeRatMantissa q x : ℚ) / (2 : ℚ) ^ q

theorem cast_quantizeRat (q : ℕ) (x : ℚ) :
    (quantizeRat q x : ℝ) = quantizeReal q (x : ℝ) := by
  unfold quantizeRat quantizeReal
  rw [quantizeRatMantissa_eq_quantizeRealMantissa]
  push_cast
  rw [div_eq_mul_inv, ← zpow_natCast, zpow_neg]

theorem abs_quantizeRat_sub_self_le (q : ℕ) (x : ℚ) :
    |(quantizeRat q x : ℝ) - (x : ℝ)| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  rw [cast_quantizeRat]
  exact abs_quantizeReal_sub_self_le q (x : ℝ)

theorem abs_quantizeRat_le_succ_of_le (B q : ℕ) {x : ℚ} (hx : |(x : ℝ)| ≤ (B : ℝ)) :
    |(quantizeRat q x : ℝ)| ≤ ((B + 1 : ℕ) : ℝ) := by
  have h1 := abs_quantizeRat_sub_self_le q x
  have h2 : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have htri := abs_sub_le (quantizeRat q x : ℝ) (x : ℝ) 0
  rw [sub_zero, sub_zero] at htri
  push_cast
  linarith

theorem real_exp_nat_le_two_pow (K : ℕ) : Real.exp (K : ℝ) ≤ (2 : ℝ) ^ (2 * K) := by
  have he1 : Real.exp 1 ≤ (2 : ℝ) ^ 2 := by linarith [Real.exp_one_lt_d9]
  have hnat : (K : ℝ) = (K : ℝ) * 1 := by ring
  rw [hnat, Real.exp_nat_mul]
  calc (Real.exp 1) ^ K
      ≤ ((2 : ℝ) ^ 2) ^ K := pow_le_pow_left₀ (Real.exp_pos 1).le he1 K
    _ = (2 : ℝ) ^ (2 * K) := by rw [← pow_mul]

/-- Local Lipschitz continuity of `Real.exp` on $(-\infty, M]$:
for $a, b \le M$, $|e^a - e^b| \le e^M |a - b|$. -/
theorem abs_exp_sub_exp_le_of_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  have haux : ∀ u v : ℝ, u ≤ v → v ≤ M → |Real.exp u - Real.exp v| ≤ Real.exp M * (v - u) := by
    intro u v huv hvM
    have hle : Real.exp u ≤ Real.exp v := Real.exp_le_exp.mpr huv
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
    have h1 : Real.exp v - Real.exp u = Real.exp v * (1 - Real.exp (-(v - u))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2; ring
    have h2 : 1 - Real.exp (-(v - u)) ≤ v - u := by
      linarith [Real.add_one_le_exp (-(v - u))]
    have h3 : Real.exp v ≤ Real.exp M := Real.exp_le_exp.mpr hvM
    rw [h1]
    exact mul_le_mul h3 h2 (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) (Real.exp_pos M).le
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    exact haux a b hab hb
  · rw [abs_sub_comm (Real.exp a) (Real.exp b), abs_of_nonneg (sub_nonneg.mpr hba)]
    exact haux b a hba ha

/-- Single step of the pure-integer Taylor power-factorial recurrence
$T_{m+1} = \mathrm{roundDivInt}(\mathrm{smul}(T_m, r_{\text{mant}}), (m + 1) \cdot 2^{q_r})$. -/
def expTermStepFixedWithMul (smul : ℤ → ℤ → ℤ) (q_r : ℕ) (r_mant : ℤ) (m : ℕ) (T_m : ℤ) : ℤ :=
  roundDivInt (smul T_m r_mant) (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r)

def expTermStepFixed (q_r : ℕ) (r_mant : ℤ) (m : ℕ) (T_m : ℤ) : ℤ :=
  expTermStepFixedWithMul (· * ·) q_r r_mant m T_m

/-- Single-pass $O(N)$ pure-integer recurrence array for $T_m \approx \frac{r_q^m}{m!} \cdot 2^{q_{\text{acc}}}$
computed via `buildRecurrenceArray` with zero `x ^ m` and zero `m.factorial`. -/
def expTermArrayFixedWithMul (smul : ℤ → ℤ → ℤ) (q_r q_acc N : ℕ) (r_mant : ℤ) : Array ℤ :=
  (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixedWithMul smul q_r r_mant) N).1

def expTermArrayFixed (q_r q_acc N : ℕ) (r_mant : ℤ) : Array ℤ :=
  expTermArrayFixedWithMul (· * ·) q_r q_acc N r_mant

theorem expTermArrayFixedWithMul_eq_expTermArrayFixed (smul : ℤ → ℤ → ℤ)
    (hsmul : ∀ a b : ℤ, smul a b = a * b) (q_r q_acc N : ℕ) (r_mant : ℤ) :
    expTermArrayFixedWithMul smul q_r q_acc N r_mant =
      expTermArrayFixed q_r q_acc N r_mant := by
  have hfn : smul = (· * ·) := funext fun a => funext fun b => hsmul a b
  subst hfn
  rfl

/-- Monotonic recurrence growth majorant $\prod_{k=0}^{m-1} \max(1, B / (k + 1))$. -/
noncomputable def expRecGrowth (B : ℕ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => max 1 ((B : ℝ) / ((m + 1 : ℕ) : ℝ)) * expRecGrowth B m

private theorem one_le_expRecGrowth (B : ℕ) : ∀ m : ℕ, 1 ≤ expRecGrowth B m
  | 0 => le_refl 1
  | m + 1 => one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_expRecGrowth B m)

private theorem expRecGrowth_nonneg (B m : ℕ) : 0 ≤ expRecGrowth B m :=
  zero_le_one.trans (one_le_expRecGrowth B m)

private theorem mul_expRecGrowth_le (B m : ℕ) :
    ((B : ℝ) / ((m + 1 : ℕ) : ℝ)) * expRecGrowth B m ≤ expRecGrowth B (m + 1) :=
  mul_le_mul_of_nonneg_right (le_max_right _ _) (expRecGrowth_nonneg B m)

private theorem expRecGrowth_eq_pow_div_factorial_of_le (B : ℕ) :
    ∀ m : ℕ, m ≤ B → expRecGrowth B m = (B : ℝ) ^ m / (m.factorial : ℝ)
  | 0, _ => by simp [expRecGrowth]
  | m + 1, hm => by
    unfold expRecGrowth
    have h1 : (1 : ℝ) ≤ (B : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact_mod_cast hm
    rw [max_eq_right h1, expRecGrowth_eq_pow_div_factorial_of_le B m (Nat.le_of_succ_le hm),
      pow_succ', Nat.factorial_succ, Nat.cast_mul]
    ring

private theorem expRecGrowth_eq_of_ge (B : ℕ) :
    ∀ m : ℕ, B ≤ m → expRecGrowth B m = expRecGrowth B B
  | m, hm => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.add_succ, expRecGrowth]
      have h1 : (B : ℝ) / ((B + d + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_iff₀ (by positivity), one_mul]
        exact_mod_cast (by omega : B ≤ B + d + 1)
      rw [max_eq_left h1, one_mul, ih (by omega)]

private theorem expRecGrowth_le_two_pow (B m : ℕ) :
    expRecGrowth B m ≤ (2 : ℝ) ^ (2 * B) := by
  have hle_exp : ∀ k ≤ B, expRecGrowth B k ≤ (2 : ℝ) ^ (2 * B) := by
    intro k hk
    rw [expRecGrowth_eq_pow_div_factorial_of_le B k hk]
    exact (Real.pow_div_factorial_le_exp (B : ℝ) (by positivity) k).trans
      (real_exp_nat_le_two_pow B)
  rcases le_total m B with hm | hm
  · exact hle_exp m hm
  · rw [expRecGrowth_eq_of_ge B m hm]
    exact hle_exp B (le_refl B)

private theorem abs_buildRecurrenceArray_expTermStepFixed_sub_le
    (B q_r q_acc : ℕ) (r_mant : ℤ)
    (hr : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ (B : ℝ)) :
    let r_q : ℝ := (r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))
    ∀ m : ℕ,
      |(((buildRecurrenceArray ((2 : ℤ) ^ q_acc)
          (expTermStepFixed q_r r_mant) m).2 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
        r_q ^ m / (m.factorial : ℝ)| ≤
      (m : ℝ) * expRecGrowth B m * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
  intro r_q m
  induction m with
  | zero =>
    simp only [buildRecurrenceArray, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      Nat.cast_zero, zero_mul, Int.cast_pow, Int.cast_ofNat, two_pow_mul_two_zpow_neg,
      sub_self, abs_zero, le_refl]
  | succ m ih =>
    simp only [buildRecurrenceArray, expTermStepFixed, expTermStepFixedWithMul]
    set T_m : ℤ := (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
    set t_m : ℝ := (T_m : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))
    set u_m : ℝ := r_q ^ m / (m.factorial : ℝ)
    set ε : ℝ := (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))
    have hε_nn : 0 ≤ ε := by dsimp [ε]; positivity
    have hstep := abs_roundDivInt_mul_zpow_sub_le q_acc (T_m * r_mant)
      (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r)
    have htarget :
        (((T_m * r_mant : ℤ) : ℝ) / ((((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r : ℤ) : ℝ)) *
            (2 : ℝ) ^ (-(q_acc : ℤ)) =
          (t_m * r_q) / ((m + 1 : ℕ) : ℝ) := by
      have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have h2qr_ne : (2 : ℝ) ^ q_r ≠ 0 := by positivity
      dsimp [t_m, r_q]
      rw [zpow_neg (2 : ℝ) (q_r : ℤ), zpow_natCast]
      push_cast
      field_simp [hm1_ne, h2qr_ne]
    rw [htarget] at hstep
    have hu_succ : r_q ^ (m + 1) / ((m + 1).factorial : ℝ) = (u_m * r_q) / ((m + 1 : ℕ) : ℝ) := by
      dsimp [u_m]
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
      ring
    rw [hu_succ]
    have hprop : |(t_m * r_q) / ((m + 1 : ℕ) : ℝ) - (u_m * r_q) / ((m + 1 : ℕ) : ℝ)| ≤
        (m : ℝ) * expRecGrowth B (m + 1) * ε := by
      have h1 : (t_m * r_q) / ((m + 1 : ℕ) : ℝ) - (u_m * r_q) / ((m + 1 : ℕ) : ℝ) =
          (r_q / ((m + 1 : ℕ) : ℝ)) * (t_m - u_m) := by ring
      rw [h1, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ))]
      have hdiv_B : |r_q| / ((m + 1 : ℕ) : ℝ) ≤ (B : ℝ) / ((m + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hr (by positivity)
      calc (|r_q| / ((m + 1 : ℕ) : ℝ)) * |t_m - u_m|
          ≤ ((B : ℝ) / ((m + 1 : ℕ) : ℝ)) * ((m : ℝ) * expRecGrowth B m * ε) :=
            mul_le_mul hdiv_B ih (abs_nonneg _) (by positivity)
        _ = (m : ℝ) * (((B : ℝ) / ((m + 1 : ℕ) : ℝ)) * expRecGrowth B m) * ε := by ring
        _ ≤ (m : ℝ) * expRecGrowth B (m + 1) * ε :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_expRecGrowth_le B m) (Nat.cast_nonneg m)) hε_nn
    have h1_le : ε ≤ 1 * expRecGrowth B (m + 1) * ε := by
      rw [one_mul]
      exact le_mul_of_one_le_left hε_nn (one_le_expRecGrowth B (m + 1))
    change _ ≤ ε at hstep
    have htri := abs_sub_le
      ((roundDivInt (T_m * r_mant) (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r) : ℝ) *
        (2 : ℝ) ^ (-(q_acc : ℤ)))
      ((t_m * r_q) / ((m + 1 : ℕ) : ℝ))
      ((u_m * r_q) / ((m + 1 : ℕ) : ℝ))
    have hm_cast : ((m + 1 : ℕ) : ℝ) * expRecGrowth B (m + 1) * ε =
        (m : ℝ) * expRecGrowth B (m + 1) * ε + 1 * expRecGrowth B (m + 1) * ε := by
      push_cast; ring
    rw [hm_cast]
    linarith

private theorem abs_expTermArrayFixed_getD_sub_le
    (B q_r q_acc N : ℕ) (r_mant : ℤ)
    (hr : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ (B : ℝ))
    {m : ℕ} (hm : m ≤ N) :
    |(((expTermArrayFixed q_r q_acc N r_mant).getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
      ((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)| ≤
      (m : ℝ) * (2 : ℝ) ^ (2 * B) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
  have hget : (expTermArrayFixed q_r q_acc N r_mant).getD m 0 =
      (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 :=
    getD_default_buildRecurrenceArray ((2 : ℤ) ^ q_acc) 0 (expTermStepFixed q_r r_mant) hm
  rw [hget]
  refine (abs_buildRecurrenceArray_expTermStepFixed_sub_le B q_r q_acc r_mant hr m).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (expRecGrowth_le_two_pow B m) (Nat.cast_nonneg m))
    (by positivity)

private theorem abs_roundDivInt_expTermArrayFixed_getD_sub_le
    (B q_r q_acc N : ℕ) (r_mant : ℤ)
    (hr : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ (B : ℝ))
    {m d : ℕ} (hm : m ≤ N) (hd : 1 ≤ d) :
    |((roundDivInt ((expTermArrayFixed q_r q_acc N r_mant).getD m 0) (d : ℤ) : ℤ) : ℝ) *
        (2 : ℝ) ^ (-(q_acc : ℤ)) -
      (((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)) / (d : ℝ)| ≤
      ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
  set T_m : ℤ := (expTermArrayFixed q_r q_acc N r_mant).getD m 0
  set t_m : ℝ := (T_m : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))
  set u_m : ℝ := ((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)
  set ε : ℝ := (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))
  have hd_r : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hstep := abs_roundDivInt_mul_zpow_sub_le q_acc T_m (d : ℤ)
  have htarget : ((T_m : ℝ) / ((d : ℤ) : ℝ)) * (2 : ℝ) ^ (-(q_acc : ℤ)) = t_m / (d : ℝ) := by
    dsimp [t_m]; push_cast; ring
  rw [htarget] at hstep
  change _ ≤ ε at hstep
  have hdiv : |t_m / (d : ℝ) - u_m / (d : ℝ)| ≤ |t_m - u_m| := by
    rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < (d : ℝ))]
    exact div_le_self (abs_nonneg _) hd_r
  have hrec := abs_expTermArrayFixed_getD_sub_le B q_r q_acc N r_mant hr hm
  change |t_m - u_m| ≤ (m : ℝ) * (2 : ℝ) ^ (2 * B) * ε at hrec
  have h2B_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * B) := by
    exact_mod_cast (Nat.one_le_two_pow (n := 2 * B))
  have h1_le : ε ≤ 1 * (2 : ℝ) ^ (2 * B) * ε := by
    rw [one_mul]
    exact le_mul_of_one_le_left (by positivity) h2B_ge1
  have htri := abs_sub_le
    ((roundDivInt T_m (d : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))
    (t_m / (d : ℝ)) (u_m / (d : ℝ))
  have hm_cast : ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) * ε =
      (m : ℝ) * (2 : ℝ) ^ (2 * B) * ε + 1 * (2 : ℝ) ^ (2 * B) * ε := by
    push_cast; ring
  rw [hm_cast]
  linarith

private theorem sum_range_expTerm_err_le
    {B M q_acc q : ℕ} (hq_acc : 2 * M + 2 + 2 * B + (q + 2) ≤ q_acc) :
    ((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
      ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := M + 1)).le
  have hprod : ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) ≤
      (2 : ℝ) ^ (2 * M + 2 + 2 * B) := by
    calc ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B)
        ≤ (2 : ℝ) ^ (M + 1) * (2 : ℝ) ^ (M + 1) * (2 : ℝ) ^ (2 * B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hM1 hM1 (by positivity) (by positivity))
            (by positivity)
      _ = (2 : ℝ) ^ (2 * M + 2 + 2 * B) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
  have hzpow : (2 : ℝ) ^ (2 * M + 2 + 2 * B) * (2 : ℝ) ^ (-(q_acc : ℤ)) ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have h1 : (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) = (2 : ℝ) ^ ((-1 : ℤ) + -(q : ℤ)) := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    rw [← zpow_natCast (2 : ℝ) (2 * M + 2 + 2 * B), ← zpow_add₀ (by norm_num), h1]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hzpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(q_acc : ℤ)) := by positivity
  calc ((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
        ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))))
      = (1 / 2 : ℝ) * ((((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B)) *
          (2 : ℝ) ^ (-(q_acc : ℤ))) := by ring
    _ ≤ (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * M + 2 + 2 * B) * (2 : ℝ) ^ (-(q_acc : ℤ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hzpos) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) :=
        mul_le_mul_of_nonneg_left hzpow (by norm_num)
    _ = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by ring

/-- Pure-integer single-pass fixed-point Taylor polynomial of $\exp(x)$ parameterized by
`smul : ℤ → ℤ → ℤ` (Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def expTaylorRatWithMul (smul : ℤ → ℤ → ℤ) (N : ℕ) (x : ℚ) : ℚ :=
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let r_mant : ℤ := quantizeRatMantissa q_r x
  let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
  ((∑ m ∈ Finset.range (M + 1), arr.getD m 0 : ℤ) : ℚ) / (2 : ℚ) ^ q_acc

/-- Pure-integer single-pass fixed-point Taylor polynomial of $\exp(x)$
(Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def expTaylorRat (N : ℕ) (x : ℚ) : ℚ :=
  expTaylorRatWithMul (· * ·) N x

/-- Error bound for `expTaylorRat`: for $|x| \le B$,
$|\text{expTaylorRat}(4B + q + 1, x) - e^x| \le 2^{-q}$. -/
theorem abs_expTaylorRat_sub_exp_le (B q : ℕ) {x : ℚ} (hx : |(x : ℝ)| ≤ (B : ℝ)) :
    |(expTaylorRat (4 * B + q + 1) x : ℝ) - Real.exp (x : ℝ)| ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  set N : ℕ := 4 * B + q + 1
  set M : ℕ := N + 6
  set q_r : ℕ := 2 * M
  set q_acc : ℕ := 3 * M + 6
  set r_mant : ℤ := quantizeRatMantissa q_r x
  set x_q : ℚ := quantizeRat q_r x
  set arr : Array ℤ := expTermArrayFixed q_r q_acc M r_mant
  have hxq_eq : (r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ)) = (x_q : ℝ) := by
    dsimp [x_q, quantizeRat, r_mant]
    push_cast
    rw [div_eq_mul_inv, ← zpow_natCast, zpow_neg]
  have hxq_abs : |(x_q : ℝ)| ≤ ((B + 1 : ℕ) : ℝ) := abs_quantizeRat_le_succ_of_le B q_r hx
  have hr_abs : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ ((B + 1 : ℕ) : ℝ) := by
    rwa [hxq_eq]
  have hcast_sum : (expTaylorRat N x : ℝ) =
      ∑ m ∈ Finset.range (M + 1), ((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) := by
    change ((((∑ m ∈ Finset.range (M + 1), arr.getD m 0 : ℤ) : ℚ) /
      (2 : ℚ) ^ q_acc : ℚ) : ℝ) = _
    push_cast
    rw [div_eq_mul_inv, Finset.sum_mul, ← zpow_natCast (2 : ℝ) q_acc, ← zpow_neg]
  have hraw_sum : (rawExpTaylorRat (M + 1) x_q : ℝ) =
      ∑ m ∈ Finset.range (M + 1), (x_q : ℝ) ^ m / (m.factorial : ℝ) := by
    unfold rawExpTaylorRat; push_cast; rfl
  have hfp : |(expTaylorRat N x : ℝ) - (rawExpTaylorRat (M + 1) x_q : ℝ)| ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [hcast_sum, hraw_sum, ← Finset.sum_sub_distrib]
    have hsum_le :
        |∑ m ∈ Finset.range (M + 1),
          (((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
            (x_q : ℝ) ^ m / (m.factorial : ℝ))| ≤
        ((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (B + 1)) *
          ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ m ∈ Finset.range (M + 1),
          |(((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
            (x_q : ℝ) ^ m / (m.factorial : ℝ))| ≤
          ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (B + 1)) *
            ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
        intro m hm
        rw [Finset.mem_range] at hm
        rw [← hxq_eq]
        refine (abs_expTermArrayFixed_getD_sub_le (B + 1) q_r q_acc M r_mant hr_abs
          (by omega : m ≤ M)).trans ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : m ≤ M + 1)) (by positivity))
          (by positivity)
      simpa using Finset.sum_le_sum hterm
    exact hsum_le.trans (sum_range_expTerm_err_le (by dsimp [q_acc, M, N]; omega))
  have hraw : |(rawExpTaylorRat (M + 1) x_q : ℝ) - Real.exp (x_q : ℝ)| ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hM1 : M + 1 = 4 * (B + 1) + (q + 3) + 1 := by dsimp [M, N]; omega
    rw [hM1]
    have h := abs_rawExpTaylorRat_sub_exp_le (B + 1) (q + 3) hxq_abs
    have hle : (2 : ℝ) ^ (-((q + 3 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-((q + 2 : ℕ) : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hexp : -((q + 2 : ℕ) : ℤ) = (-2 : ℤ) + -(q : ℤ) := by omega
    have h4_inv : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [hexp, zpow_add₀ (by norm_num), h4_inv] at hle
    exact h.trans hle
  have hpert : |Real.exp (x_q : ℝ) - Real.exp (x : ℝ)| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hxq_le : (x_q : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := (le_abs_self _).trans hxq_abs
    have hx_le : (x : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
      have h1 := (le_abs_self (x : ℝ)).trans hx
      push_cast; linarith
    have hlip := abs_exp_sub_exp_le_of_le hxq_le hx_le
    have hexp_le := real_exp_nat_le_two_pow (B + 1)
    have hdiff := abs_quantizeRat_sub_self_le q_r x
    have h1 : Real.exp ((B + 1 : ℕ) : ℝ) * |(x_q : ℝ) - (x : ℝ)| ≤
        (2 : ℝ) ^ (2 * (B + 1)) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) :=
      mul_le_mul hexp_le hdiff (abs_nonneg _) (by positivity)
    have hzpow : (2 : ℝ) ^ (2 * (B + 1)) * (2 : ℝ) ^ (-(q_r : ℤ)) ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
      rw [← zpow_natCast (2 : ℝ) (2 * (B + 1)), ← zpow_add₀ (by norm_num)]
      exact zpow_le_zpow_right₀ (by norm_num) (by dsimp [q_r, M, N]; omega)
    calc |Real.exp (x_q : ℝ) - Real.exp (x : ℝ)|
        ≤ (2 : ℝ) ^ (2 * (B + 1)) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) := hlip.trans h1
      _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * (B + 1)) * (2 : ℝ) ^ (-(q_r : ℤ))) := by ring
      _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := mul_le_mul_of_nonneg_left hzpow (by norm_num)
  have htri1 := abs_sub_le (expTaylorRat N x : ℝ) (rawExpTaylorRat (M + 1) x_q : ℝ) (Real.exp (x : ℝ))
  have htri2 := abs_sub_le (rawExpTaylorRat (M + 1) x_q : ℝ) (Real.exp (x_q : ℝ)) (Real.exp (x : ℝ))
  linarith

private theorem abs_quantizeRat_le_of_le (B q : ℕ) {x : ℚ} (hx : |(x : ℝ)| ≤ (B : ℝ)) :
    |(quantizeRat q x : ℝ)| ≤ (B : ℝ) := by
  have hx_bounds := abs_le.mp hx
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hm_eq : (quantizeRatMantissa q x : ℤ) =
      Int.floor ((x : ℝ) * (2 : ℝ) ^ q + 1 / 2) := by
    rw [quantizeRatMantissa_eq_quantizeRealMantissa]
    rfl
  have hm_upper : (quantizeRatMantissa q x : ℤ) ≤ ((B * 2 ^ q : ℕ) : ℤ) := by
    rw [hm_eq, Int.floor_le_iff]
    have hmul : (x : ℝ) * (2 : ℝ) ^ q ≤ (B : ℝ) * (2 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right hx_bounds.2 h2q_pos.le
    push_cast
    linarith
  have hm_lower : -((B * 2 ^ q : ℕ) : ℤ) ≤ (quantizeRatMantissa q x : ℤ) := by
    rw [hm_eq, Int.le_floor]
    have hmul : -(B : ℝ) * (2 : ℝ) ^ q ≤ (x : ℝ) * (2 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right hx_bounds.1 h2q_pos.le
    push_cast
    linarith
  have hm_abs : |(quantizeRatMantissa q x : ℝ)| ≤ (B : ℝ) * (2 : ℝ) ^ q := by
    rw [abs_le]
    constructor
    · have h1 : (-((B * 2 ^ q : ℕ) : ℤ) : ℝ) ≤ (quantizeRatMantissa q x : ℝ) := by
        exact_mod_cast hm_lower
      push_cast at h1
      linarith
    · have h2 : (quantizeRatMantissa q x : ℝ) ≤ (((B * 2 ^ q : ℕ) : ℤ) : ℝ) := by
        exact_mod_cast hm_upper
      push_cast at h2
      linarith
  unfold quantizeRat
  push_cast
  rw [abs_div, abs_of_pos h2q_pos, div_le_iff₀ h2q_pos]
  exact hm_abs

/-- Lipschitz bound for $e^{ia}$: $\|e^{ia} - e^{ib}\| \le 2 |a - b|$. -/
theorem norm_exp_ofReal_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ 2 * |a - b| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)).re =
      Real.cos a - Real.cos b := by
    rw [Complex.sub_re, Complex.exp_mul_I, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have him : (Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)).im =
      Real.sin a - Real.sin b := by
    rw [Complex.sub_im, Complex.exp_mul_I, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  rw [hre, him]
  linarith [Real.abs_cos_sub_cos_le a b, Real.abs_sin_sub_sin_le a b]

/-- Integral representation $\operatorname{sinc}(x) = \int_{-1/2}^{1/2} \cos(2 x \nu) \, d\nu$. -/
theorem real_sinc_eq_intervalIntegral_cos (x : ℝ) :
    Real.sinc x = ∫ nu : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Real.cos (nu * (2 * x)) := by
  by_cases hx : x = 0
  · subst hx
    simp
    norm_num
  · have hc : 2 * x ≠ 0 := mul_ne_zero two_ne_zero hx
    rw [intervalIntegral.integral_comp_mul_right Real.cos hc, integral_cos, smul_eq_mul]
    have h1 : (1 / 2 : ℝ) * (2 * x) = x := by ring
    have h2 : (-1 / 2 : ℝ) * (2 * x) = -x := by ring
    rw [h1, h2, Real.sin_neg, Real.sinc_of_ne_zero hx]
    field_simp [hx]
    ring

/-- 1-Lipschitz continuity of `Real.sinc` on $\mathbb{R}$: $|\operatorname{sinc}(a) - \operatorname{sinc}(b)| \le |a - b|$. -/
theorem abs_sinc_sub_sinc_le (a b : ℝ) :
    |Real.sinc a - Real.sinc b| ≤ |a - b| := by
  rw [real_sinc_eq_intervalIntegral_cos a, real_sinc_eq_intervalIntegral_cos b,
    ← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    ← Real.norm_eq_abs]
  have hbound : ∀ nu ∈ Set.uIoc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      ‖Real.cos (nu * (2 * a)) - Real.cos (nu * (2 * b))‖ ≤ |a - b| := by
    intro nu hnu
    rw [Set.uIoc_of_le (by norm_num)] at hnu
    have hnu_abs : |nu| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hnu.1], hnu.2⟩
    rw [Real.norm_eq_abs]
    calc |Real.cos (nu * (2 * a)) - Real.cos (nu * (2 * b))|
        ≤ |nu * (2 * a) - nu * (2 * b)| := Real.abs_cos_sub_cos_le _ _
      _ = 2 * |nu| * |a - b| := by
          have : nu * (2 * a) - nu * (2 * b) = 2 * nu * (a - b) := by ring
          rw [this, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (1 / 2) * |a - b| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnu_abs (by norm_num)) (abs_nonneg _)
      _ = |a - b| := by ring
  calc ‖∫ nu : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), (Real.cos (nu * (2 * a)) - Real.cos (nu * (2 * b)))‖
      ≤ |a - b| * |(1 / 2 : ℝ) - (-1 / 2 : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = |a - b| := by norm_num

/-- 1-Lipschitz continuity of $z \mapsto \int_0^z e^{-t^2} dt$ on $\mathbb{R}$. -/
theorem abs_erf_integral_sub_le (a b : ℝ) :
    |(∫ t : ℝ in (0 : ℝ)..a, Real.exp (-(t ^ 2))) -
      (∫ t : ℝ in (0 : ℝ)..b, Real.exp (-(t ^ 2)))| ≤ |a - b| := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by fun_prop
  rw [intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), ← Real.norm_eq_abs]
  have hbound : ∀ t ∈ Set.uIoc b a, ‖Real.exp (-(t ^ 2))‖ ≤ (1 : ℝ) := by
    intro t _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    nlinarith [sq_nonneg t]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Computable Gaussian rational number $\text{re} + i \cdot \text{im} \in \mathbb{Q}(i)$ for
exact rational evaluation of $(i \theta)^m / m!$. -/
@[ext]
structure RatComplex where
  re : ℚ
  im : ℚ
deriving DecidableEq, Repr

namespace RatComplex

def add (z w : RatComplex) : RatComplex := ⟨z.re + w.re, z.im + w.im⟩
def mul (z w : RatComplex) : RatComplex := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def scaleDiv (z : RatComplex) (d : ℚ) : RatComplex := ⟨z.re / d, z.im / d⟩

def pow (z : RatComplex) : ℕ → RatComplex
  | 0 => ⟨1, 0⟩
  | m + 1 => mul (pow z m) z

noncomputable def toComplex (z : RatComplex) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * Complex.I

@[simp]
theorem toComplex_re (z : RatComplex) : z.toComplex.re = (z.re : ℝ) := by
  unfold toComplex
  rw [← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast]
  simp

@[simp]
theorem toComplex_im (z : RatComplex) : z.toComplex.im = (z.im : ℝ) := by
  unfold toComplex
  rw [← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast]
  simp

@[simp]
theorem toComplex_add (z w : RatComplex) :
    (add z w).toComplex = z.toComplex + w.toComplex := by
  unfold add toComplex; push_cast; ring

@[simp]
theorem toComplex_mul (z w : RatComplex) :
    (mul z w).toComplex = z.toComplex * w.toComplex := by
  unfold mul toComplex
  push_cast
  linear_combination (-(z.im : ℂ) * (w.im : ℂ)) * Complex.I_sq

@[simp]
theorem toComplex_scaleDiv (z : RatComplex) (d : ℚ) :
    (scaleDiv z d).toComplex = z.toComplex / (d : ℂ) := by
  unfold scaleDiv toComplex; push_cast; ring

@[simp]
theorem toComplex_pow (z : RatComplex) (m : ℕ) :
    (pow z m).toComplex = (z.toComplex) ^ m := by
  induction m with
  | zero => simp [pow, toComplex]
  | succ m ih => rw [pow, toComplex_mul, ih, pow_succ]

end RatComplex

/-- Real part of $i^m \in \{-1, 0, 1\}$ computed in $O(1)$ via `m % 4`. -/
def iPowRe (m : ℕ) : ℤ :=
  if m % 4 = 0 then 1 else if m % 4 = 2 then -1 else 0

/-- Imaginary part of $i^m \in \{-1, 0, 1\}$ computed in $O(1)$ via `m % 4`. -/
def iPowIm (m : ℕ) : ℤ :=
  if m % 4 = 1 then 1 else if m % 4 = 3 then -1 else 0

private theorem iPowRe_succ (m : ℕ) : iPowRe (m + 1) = -iPowIm m := by
  unfold iPowRe iPowIm; omega

private theorem iPowIm_succ (m : ℕ) : iPowIm (m + 1) = iPowRe m := by
  unfold iPowIm iPowRe; omega

private theorem abs_iPowRe_le_one (m : ℕ) : |(iPowRe m : ℝ)| ≤ 1 := by
  unfold iPowRe; split_ifs <;> norm_num

private theorem abs_iPowIm_le_one (m : ℕ) : |(iPowIm m : ℝ)| ≤ 1 := by
  unfold iPowIm; split_ifs <;> norm_num

theorem abs_iPowRe_int_le_one (m : ℕ) : |iPowRe m| ≤ 1 := by
  unfold iPowRe; split_ifs <;> decide

theorem abs_iPowIm_int_le_one (m : ℕ) : |iPowIm m| ≤ 1 := by
  unfold iPowIm; split_ifs <;> decide

private theorem ratComplex_pow_imag_eq (θ : ℚ) (m : ℕ) :
    RatComplex.pow ⟨0, θ⟩ m = ⟨(iPowRe m : ℚ) * θ ^ m, (iPowIm m : ℚ) * θ ^ m⟩ := by
  induction m with
  | zero =>
    ext <;> simp [RatComplex.pow, iPowRe, iPowIm]
  | succ m ih =>
    rw [RatComplex.pow, ih, iPowRe_succ, iPowIm_succ, pow_succ]
    ext <;> simp [RatComplex.mul] <;> ring

/-- Unrounded rational Taylor polynomial of $e^{i\theta}$. -/
def rawExpITaylorRat (N : ℕ) (θ : ℚ) : RatComplex :=
  ⟨∑ m ∈ Finset.range N, ((RatComplex.pow ⟨0, θ⟩ m).scaleDiv (m.factorial : ℚ)).re,
   ∑ m ∈ Finset.range N, ((RatComplex.pow ⟨0, θ⟩ m).scaleDiv (m.factorial : ℚ)).im⟩

theorem toComplex_rawExpITaylorRat (N : ℕ) (θ : ℚ) :
    (rawExpITaylorRat N θ).toComplex =
      ∑ m ∈ Finset.range N, (((θ : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) := by
  unfold rawExpITaylorRat RatComplex.toComplex
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := RatComplex.toComplex_scaleDiv (RatComplex.pow ⟨0, θ⟩ m) (m.factorial : ℚ)
  have hp := RatComplex.toComplex_pow ⟨0, θ⟩ m
  unfold RatComplex.toComplex at h hp
  rw [h, hp]
  simp

theorem norm_rawExpITaylorRat_sub_exp_le (B q : ℕ) {θ : ℚ} (hθ : |(θ : ℝ)| ≤ (B : ℝ)) :
    ‖(rawExpITaylorRat (4 * B + q + 1) θ).toComplex - Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖ ≤
      (2 : ℝ) ^ (-(q : ℤ)) := by
  rw [toComplex_rawExpITaylorRat, norm_sub_rev]
  refine norm_exp_sub_sum_range_le_two_zpow B q ?_
  simpa [norm_mul, Complex.norm_real] using hθ

/-- Pure-integer single-pass fixed-point Taylor polynomial of $e^{i\theta}$ parameterized by
`smul : ℤ → ℤ → ℤ` (Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def expITaylorRatWithMul (smul : ℤ → ℤ → ℤ) (N : ℕ) (θ : ℚ) : RatComplex :=
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let r_mant : ℤ := quantizeRatMantissa q_r θ
  let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
  ⟨((∑ m ∈ Finset.range (M + 1), iPowRe m * arr.getD m 0 : ℤ) : ℚ) / (2 : ℚ) ^ q_acc,
   ((∑ m ∈ Finset.range (M + 1), iPowIm m * arr.getD m 0 : ℤ) : ℚ) / (2 : ℚ) ^ q_acc⟩

/-- Pure-integer single-pass fixed-point Taylor polynomial of $e^{i\theta}$
(Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def expITaylorRat (N : ℕ) (θ : ℚ) : RatComplex :=
  expITaylorRatWithMul (· * ·) N θ

/-- Error bound for `expITaylorRat`: for $|\theta| \le B$,
$\|\text{expITaylorRat}(4B + q + 1, \theta) - e^{i\theta}\| \le 2^{-q}$
(Lemma 3.2 (`lem:elementary`); Table 3 (`tab:lean-map`) in Section 8 (`sec:lean`)). -/
theorem norm_expITaylorRat_sub_exp_le (B q : ℕ) {θ : ℚ} (hθ : |(θ : ℝ)| ≤ (B : ℝ)) :
    ‖(expITaylorRat (4 * B + q + 1) θ).toComplex - Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖ ≤
      (2 : ℝ) ^ (-(q : ℤ)) := by
  set N : ℕ := 4 * B + q + 1
  set M : ℕ := N + 6
  set q_r : ℕ := 2 * M
  set q_acc : ℕ := 3 * M + 6
  set r_mant : ℤ := quantizeRatMantissa q_r θ
  set θ_q : ℚ := quantizeRat q_r θ
  set arr : Array ℤ := expTermArrayFixed q_r q_acc M r_mant
  have hθq_eq : (r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ)) = (θ_q : ℝ) := by
    dsimp [θ_q, quantizeRat, r_mant]
    push_cast
    rw [div_eq_mul_inv, ← zpow_natCast, zpow_neg]
  have hθq_abs : |(θ_q : ℝ)| ≤ (B : ℝ) := abs_quantizeRat_le_of_le B q_r hθ
  have hr_abs : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ (B : ℝ) := by
    rwa [hθq_eq]
  have h2q1 : (2 : ℝ) ^ (-((q + 1 : ℕ) : ℤ)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hexp : -((q + 1 : ℕ) : ℤ) = (-1 : ℤ) + -(q : ℤ) := by omega
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
  have hre : |((expITaylorRat N θ).toComplex - (rawExpITaylorRat (M + 1) θ_q).toComplex).re| ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [Complex.sub_re, RatComplex.toComplex_re, RatComplex.toComplex_re]
    have hcast1 : ((expITaylorRat N θ).re : ℝ) =
        ∑ m ∈ Finset.range (M + 1),
          (iPowRe m : ℝ) * (((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
      change ((((∑ m ∈ Finset.range (M + 1), iPowRe m * arr.getD m 0 : ℤ) : ℚ) /
        (2 : ℚ) ^ q_acc : ℚ) : ℝ) = _
      push_cast
      rw [div_eq_mul_inv, Finset.sum_mul, ← zpow_natCast (2 : ℝ) q_acc, ← zpow_neg]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hcast2 : ((rawExpITaylorRat (M + 1) θ_q).re : ℝ) =
        ∑ m ∈ Finset.range (M + 1),
          (iPowRe m : ℝ) * ((θ_q : ℝ) ^ m / (m.factorial : ℝ)) := by
      unfold rawExpITaylorRat
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ratComplex_pow_imag_eq θ_q m]
      simp [RatComplex.scaleDiv, mul_div_assoc]
    rw [hcast1, hcast2, ← Finset.sum_sub_distrib]
    have hsum_le :
        |∑ m ∈ Finset.range (M + 1),
          ((iPowRe m : ℝ) * (((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
            (iPowRe m : ℝ) * ((θ_q : ℝ) ^ m / (m.factorial : ℝ)))| ≤
        ((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
          ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ m ∈ Finset.range (M + 1),
          |(iPowRe m : ℝ) * (((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
            (iPowRe m : ℝ) * ((θ_q : ℝ) ^ m / (m.factorial : ℝ))| ≤
          ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
            ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
        intro m hm
        rw [Finset.mem_range] at hm
        rw [← mul_sub, abs_mul, ← hθq_eq]
        have hi := abs_iPowRe_le_one m
        have herr := abs_expTermArrayFixed_getD_sub_le B q_r q_acc M r_mant hr_abs
          (by omega : m ≤ M)
        calc |(iPowRe m : ℝ)| *
              |(((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
                ((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ))|
            ≤ 1 * ((m : ℝ) * (2 : ℝ) ^ (2 * B) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) :=
              mul_le_mul hi herr (abs_nonneg _) zero_le_one
          _ ≤ ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
                ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : m ≤ M + 1)) (by positivity))
                (by positivity)
      simpa using Finset.sum_le_sum hterm
    have hbound := sum_range_expTerm_err_le (B := B) (M := M) (q_acc := q_acc) (q := q + 1)
      (by dsimp [q_acc, M, N]; omega)
    rw [h2q1] at hbound
    linarith
  have him : |((expITaylorRat N θ).toComplex - (rawExpITaylorRat (M + 1) θ_q).toComplex).im| ≤
      (1 / 8 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [Complex.sub_im, RatComplex.toComplex_im, RatComplex.toComplex_im]
    have hcast1 : ((expITaylorRat N θ).im : ℝ) =
        ∑ m ∈ Finset.range (M + 1),
          (iPowIm m : ℝ) * (((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
      change ((((∑ m ∈ Finset.range (M + 1), iPowIm m * arr.getD m 0 : ℤ) : ℚ) /
        (2 : ℚ) ^ q_acc : ℚ) : ℝ) = _
      push_cast
      rw [div_eq_mul_inv, Finset.sum_mul, ← zpow_natCast (2 : ℝ) q_acc, ← zpow_neg]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hcast2 : ((rawExpITaylorRat (M + 1) θ_q).im : ℝ) =
        ∑ m ∈ Finset.range (M + 1),
          (iPowIm m : ℝ) * ((θ_q : ℝ) ^ m / (m.factorial : ℝ)) := by
      unfold rawExpITaylorRat
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ratComplex_pow_imag_eq θ_q m]
      simp [RatComplex.scaleDiv, mul_div_assoc]
    rw [hcast1, hcast2, ← Finset.sum_sub_distrib]
    have hsum_le :
        |∑ m ∈ Finset.range (M + 1),
          ((iPowIm m : ℝ) * (((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
            (iPowIm m : ℝ) * ((θ_q : ℝ) ^ m / (m.factorial : ℝ)))| ≤
        ((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
          ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ m ∈ Finset.range (M + 1),
          |(iPowIm m : ℝ) * (((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
            (iPowIm m : ℝ) * ((θ_q : ℝ) ^ m / (m.factorial : ℝ))| ≤
          ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
            ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
        intro m hm
        rw [Finset.mem_range] at hm
        rw [← mul_sub, abs_mul, ← hθq_eq]
        have hi := abs_iPowIm_le_one m
        have herr := abs_expTermArrayFixed_getD_sub_le B q_r q_acc M r_mant hr_abs
          (by omega : m ≤ M)
        calc |(iPowIm m : ℝ)| *
              |(((arr.getD m 0 : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
                ((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ))|
            ≤ 1 * ((m : ℝ) * (2 : ℝ) ^ (2 * B) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) :=
              mul_le_mul hi herr (abs_nonneg _) zero_le_one
          _ ≤ ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
                ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : m ≤ M + 1)) (by positivity))
                (by positivity)
      simpa using Finset.sum_le_sum hterm
    have hbound := sum_range_expTerm_err_le (B := B) (M := M) (q_acc := q_acc) (q := q + 1)
      (by dsimp [q_acc, M, N]; omega)
    rw [h2q1] at hbound
    linarith
  have hfp_norm : ‖(expITaylorRat N θ).toComplex - (rawExpITaylorRat (M + 1) θ_q).toComplex‖ ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hle := Complex.norm_le_abs_re_add_abs_im
      ((expITaylorRat N θ).toComplex - (rawExpITaylorRat (M + 1) θ_q).toComplex)
    linarith
  have hraw : ‖(rawExpITaylorRat (M + 1) θ_q).toComplex - Complex.exp (((θ_q : ℝ) : ℂ) * Complex.I)‖ ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hM1 : M + 1 = 4 * B + (q + 7) + 1 := by dsimp [M, N]; omega
    rw [hM1]
    have h := norm_rawExpITaylorRat_sub_exp_le B (q + 7) hθq_abs
    have hle : (2 : ℝ) ^ (-((q + 7 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-((q + 2 : ℕ) : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hexp : -((q + 2 : ℕ) : ℤ) = (-2 : ℤ) + -(q : ℤ) := by omega
    have h4_inv : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [hexp, zpow_add₀ (by norm_num), h4_inv] at hle
    exact h.trans hle
  have hpert : ‖Complex.exp (((θ_q : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖ ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hlip := norm_exp_ofReal_mul_I_sub_le (θ_q : ℝ) (θ : ℝ)
    have hdiff := abs_quantizeRat_sub_self_le q_r θ
    have hzpow : (2 : ℝ) ^ (-(q_r : ℤ)) ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
      rw [← h2q1]
      exact zpow_le_zpow_right₀ (by norm_num) (by dsimp [q_r, M, N]; omega)
    linarith
  have htri1 := norm_sub_le_norm_sub_add_norm_sub
    (expITaylorRat N θ).toComplex (rawExpITaylorRat (M + 1) θ_q).toComplex
    (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
  have htri2 := norm_sub_le_norm_sub_add_norm_sub
    (rawExpITaylorRat (M + 1) θ_q).toComplex (Complex.exp (((θ_q : ℝ) : ℂ) * Complex.I))
    (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
  linarith

/-- Unrounded rational Taylor polynomial for $\operatorname{sinc}(\theta)$. -/
def rawSincTaylorRat (N : ℕ) (θ : ℚ) : ℚ :=
  ∑ m ∈ Finset.range N, (RatComplex.pow ⟨0, 1⟩ (m + 1)).im * θ ^ m / ((m + 1).factorial : ℚ)

theorem abs_rawSincTaylorRat_sub_sinc_le (B q : ℕ) {θ : ℚ} (hθ : |(θ : ℝ)| ≤ (B : ℝ)) :
    |(rawSincTaylorRat (4 * B + q + 1) θ : ℝ) - Real.sinc (θ : ℝ)| ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  set N : ℕ := 4 * B + q + 1
  by_cases hθ0 : θ = 0
  · subst hθ0
    have hN : N = (4 * B + q) + 1 := rfl
    unfold rawSincTaylorRat
    rw [hN, Finset.sum_range_succ']
    have hsum0 : ∑ k ∈ Finset.range (4 * B + q),
        (RatComplex.pow ⟨0, 1⟩ (k + 1 + 1)).im * (0 : ℚ) ^ (k + 1) / ((k + 1 + 1).factorial : ℚ) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [zero_pow (by omega : k + 1 ≠ 0)]
    rw [hsum0]
    simp [RatComplex.pow, RatComplex.mul]
  · have hθ_R_ne : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ0
    have hθ_abs_pos : 0 < |(θ : ℝ)| := abs_pos.mpr hθ_R_ne
    refine le_of_mul_le_mul_right ?_ hθ_abs_pos
    rw [← abs_mul, sub_mul, Real.sinc_of_ne_zero hθ_R_ne, div_mul_cancel₀ _ hθ_R_ne]
    have hpow_im : ∀ m : ℕ,
        ((RatComplex.pow ⟨0, 1⟩ (m + 1)).im : ℝ) * (θ : ℝ) ^ m * (θ : ℝ) =
          ((((θ : ℝ) : ℂ) * Complex.I) ^ (m + 1)).im := by
      intro m
      have h1 : (((θ : ℝ) : ℂ) * Complex.I) ^ (m + 1) =
          ((((θ : ℝ) ^ (m + 1) : ℝ) : ℂ)) * (RatComplex.pow ⟨0, 1⟩ (m + 1)).toComplex := by
        rw [mul_pow, RatComplex.toComplex_pow, Complex.ofReal_pow]
        simp [RatComplex.toComplex]
      rw [h1, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        RatComplex.toComplex_im, zero_mul, add_zero, pow_succ]
      ring
    have hsum_im : (rawSincTaylorRat N θ : ℝ) * (θ : ℝ) =
        (∑ m ∈ Finset.range (N + 1), (((θ : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).im := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Complex.add_im,
        Complex.one_im, add_zero, Complex.im_sum]
      unfold rawSincTaylorRat
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [div_mul_eq_mul_div, hpow_im m]
      have hdiv_im : ((((θ : ℝ) : ℂ) * Complex.I) ^ (m + 1) / ((m + 1).factorial : ℂ)).im =
          ((((θ : ℝ) : ℂ) * Complex.I) ^ (m + 1)).im / ((m + 1).factorial : ℝ) := by
        rw [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      exact hdiv_im.symm
    have hsin_im : Real.sin (θ : ℝ) = (Complex.exp (((θ : ℝ) : ℂ) * Complex.I)).im := by
      set r : ℝ := (θ : ℝ)
      rw [Complex.exp_mul_I]
      simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
    rw [abs_sub_comm, hsum_im, hsin_im, ← Complex.sub_im]
    set z : ℂ := ((θ : ℝ) : ℂ) * Complex.I
    have hz_norm : ‖z‖ = |(θ : ℝ)| := by simp [z]
    have hcond : ‖z‖ / ((N + 1).succ : ℝ) ≤ 1 / 2 := by
      rw [hz_norm, Nat.cast_succ, div_le_iff₀ (by positivity)]
      have hBN : 2 * (B : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by
        have : 2 * B ≤ (N + 1) + 1 := by omega
        exact_mod_cast this
      linarith
    have hexp_raw := Complex.exp_bound' hcond
    have hexp := (Complex.abs_im_le_norm _).trans (by simpa [norm_sub_rev] using hexp_raw)
    have hrhs_eq : ‖z‖ ^ (N + 1) / ((N + 1).factorial : ℝ) * 2 =
        (|(θ : ℝ)| ^ N / ((N + 1).factorial : ℝ) * 2) * |(θ : ℝ)| := by
      rw [hz_norm, pow_succ]
      ring
    rw [hrhs_eq] at hexp
    refine hexp.trans (mul_le_mul_of_nonneg_right ?_ hθ_abs_pos.le)
    have hfac_pos : (0 : ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
    have hfac_le : (N.factorial : ℝ) ≤ ((N + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ N)
    have hpow_le : |(θ : ℝ)| ^ N / ((N + 1).factorial : ℝ) * 2 ≤
        (B : ℝ) ^ N / (N.factorial : ℝ) * 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
      exact (div_le_div_of_nonneg_left (pow_nonneg hθ_abs_pos.le N) hfac_pos hfac_le).trans
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ_abs_pos.le hθ N) hfac_pos.le)
    refine hpow_le.trans ?_
    have hpow_exp := Real.pow_div_factorial_le_exp (2 * (B : ℝ)) (by positivity) N
    have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have hmul_pow : (2 * (B : ℝ)) ^ N = (2 : ℝ) ^ N * (B : ℝ) ^ N := mul_pow 2 (B : ℝ) N
    have hexp_le : Real.exp (2 * (B : ℝ)) ≤ (2 : ℝ) ^ (4 * B) := by
      have he1 : Real.exp 1 ≤ (2 : ℝ) ^ 2 := by linarith [Real.exp_one_lt_d9]
      have hnat : (2 * (B : ℝ)) = ((2 * B : ℕ) : ℝ) * 1 := by push_cast; ring
      rw [hnat, Real.exp_nat_mul]
      calc (Real.exp 1) ^ (2 * B)
          ≤ ((2 : ℝ) ^ 2) ^ (2 * B) := pow_le_pow_left₀ (Real.exp_pos 1).le he1 (2 * B)
        _ = (2 : ℝ) ^ (4 * B) := by rw [← pow_mul]; ring_nf
    have hdiv_le : (B : ℝ) ^ N / (N.factorial : ℝ) ≤ (2 : ℝ) ^ (4 * B) / (2 : ℝ) ^ N := by
      rw [le_div_iff₀ h2N_pos, mul_comm, ← mul_div_assoc, ← hmul_pow]
      exact hpow_exp.trans hexp_le
    calc (B : ℝ) ^ N / (N.factorial : ℝ) * 2
        ≤ ((2 : ℝ) ^ (4 * B) / (2 : ℝ) ^ N) * 2 :=
          mul_le_mul_of_nonneg_right hdiv_le (by norm_num)
      _ = (2 : ℝ) ^ (-(q : ℤ)) := by
          have hN_eq : N = 4 * B + (q + 1) := by omega
          rw [hN_eq, pow_add, pow_succ', ← div_div, div_self (by positivity : (2 : ℝ) ^ (4 * B) ≠ 0),
            ← zpow_natCast, zpow_neg]
          have h2q : (2 : ℝ) ^ q ≠ 0 := by positivity
          field_simp [h2q]

/-- Pure-integer single-pass fixed-point Taylor polynomial for $\operatorname{sinc}(\theta)$
parameterized by `smul : ℤ → ℤ → ℤ` (Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def sincTaylorRatWithMul (smul : ℤ → ℤ → ℤ) (N : ℕ) (θ : ℚ) : ℚ :=
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let r_mant : ℤ := quantizeRatMantissa q_r θ
  let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
  ((∑ m ∈ Finset.range (M + 1),
    iPowIm (m + 1) * roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ) : ℤ) : ℚ) / (2 : ℚ) ^ q_acc

/-- Pure-integer single-pass fixed-point Taylor polynomial for $\operatorname{sinc}(\theta)$
(Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def sincTaylorRat (N : ℕ) (θ : ℚ) : ℚ :=
  sincTaylorRatWithMul (· * ·) N θ

/-- Error bound for `sincTaylorRat`: for $|\theta| \le B$,
$|\text{sincTaylorRat}(4B + q + 1, \theta) - \operatorname{sinc}(\theta)| \le 2^{-q}$
(Lemma 3.2 (`lem:elementary`); Table 3 (`tab:lean-map`) in Section 8 (`sec:lean`)). -/
theorem abs_sincTaylorRat_sub_sinc_le (B q : ℕ) {θ : ℚ} (hθ : |(θ : ℝ)| ≤ (B : ℝ)) :
    |(sincTaylorRat (4 * B + q + 1) θ : ℝ) - Real.sinc (θ : ℝ)| ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  set N : ℕ := 4 * B + q + 1
  set M : ℕ := N + 6
  set q_r : ℕ := 2 * M
  set q_acc : ℕ := 3 * M + 6
  set r_mant : ℤ := quantizeRatMantissa q_r θ
  set θ_q : ℚ := quantizeRat q_r θ
  set arr : Array ℤ := expTermArrayFixed q_r q_acc M r_mant
  have hθq_eq : (r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ)) = (θ_q : ℝ) := by
    dsimp [θ_q, quantizeRat, r_mant]
    push_cast
    rw [div_eq_mul_inv, ← zpow_natCast, zpow_neg]
  have hθq_abs : |(θ_q : ℝ)| ≤ (B : ℝ) := abs_quantizeRat_le_of_le B q_r hθ
  have hr_abs : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ (B : ℝ) := by
    rwa [hθq_eq]
  have hfp : |(sincTaylorRat N θ : ℝ) - (rawSincTaylorRat (M + 1) θ_q : ℝ)| ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hcast1 : (sincTaylorRat N θ : ℝ) =
        ∑ m ∈ Finset.range (M + 1),
          (iPowIm (m + 1) : ℝ) *
            ((roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
      change ((((∑ m ∈ Finset.range (M + 1),
        iPowIm (m + 1) * roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ) : ℤ) : ℚ) /
          (2 : ℚ) ^ q_acc : ℚ) : ℝ) = _
      push_cast
      rw [div_eq_mul_inv, Finset.sum_mul, ← zpow_natCast (2 : ℝ) q_acc, ← zpow_neg]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hcast2 : (rawSincTaylorRat (M + 1) θ_q : ℝ) =
        ∑ m ∈ Finset.range (M + 1),
          (iPowIm (m + 1) : ℝ) * (((θ_q : ℝ) ^ m / (m.factorial : ℝ)) / ((m + 1 : ℕ) : ℝ)) := by
      unfold rawSincTaylorRat
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      have hfac : ((m + 1).factorial : ℝ) = (m.factorial : ℝ) * ((m + 1 : ℕ) : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, mul_comm]
      rw [ratComplex_pow_imag_eq 1 (m + 1), hfac, ← div_div]
      push_cast
      ring
    rw [hcast1, hcast2, ← Finset.sum_sub_distrib]
    have hsum_le :
        |∑ m ∈ Finset.range (M + 1),
          ((iPowIm (m + 1) : ℝ) *
              ((roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
            (iPowIm (m + 1) : ℝ) * (((θ_q : ℝ) ^ m / (m.factorial : ℝ)) / ((m + 1 : ℕ) : ℝ)))| ≤
        ((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
          ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ m ∈ Finset.range (M + 1),
          |(iPowIm (m + 1) : ℝ) *
              ((roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
            (iPowIm (m + 1) : ℝ) * (((θ_q : ℝ) ^ m / (m.factorial : ℝ)) / ((m + 1 : ℕ) : ℝ))| ≤
          ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
            ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
        intro m hm
        rw [Finset.mem_range] at hm
        rw [← mul_sub, abs_mul, ← hθq_eq]
        have hi := abs_iPowIm_le_one (m + 1)
        have herr := abs_roundDivInt_expTermArrayFixed_getD_sub_le B q_r q_acc M r_mant hr_abs
          (by omega : m ≤ M) (by omega : 1 ≤ m + 1)
        calc |(iPowIm (m + 1) : ℝ)| *
              |((roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)) -
                (((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)) /
                  ((m + 1 : ℕ) : ℝ))|
            ≤ 1 * (((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
                ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) :=
              mul_le_mul hi herr (abs_nonneg _) zero_le_one
          _ ≤ ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * B) *
                ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : m + 1 ≤ M + 1)) (by positivity))
                (by positivity)
      simpa using Finset.sum_le_sum hterm
    exact hsum_le.trans (sum_range_expTerm_err_le (by dsimp [q_acc, M, N]; omega))
  have hraw : |(rawSincTaylorRat (M + 1) θ_q : ℝ) - Real.sinc (θ_q : ℝ)| ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hM1 : M + 1 = 4 * B + (q + 7) + 1 := by dsimp [M, N]; omega
    rw [hM1]
    have h := abs_rawSincTaylorRat_sub_sinc_le B (q + 7) hθq_abs
    have hle : (2 : ℝ) ^ (-((q + 7 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-((q + 2 : ℕ) : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hexp : -((q + 2 : ℕ) : ℤ) = (-2 : ℤ) + -(q : ℤ) := by omega
    have h4_inv : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [hexp, zpow_add₀ (by norm_num), h4_inv] at hle
    exact h.trans hle
  have hpert : |Real.sinc (θ_q : ℝ) - Real.sinc (θ : ℝ)| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hlip := abs_sinc_sub_sinc_le (θ_q : ℝ) (θ : ℝ)
    have hdiff := abs_quantizeRat_sub_self_le q_r θ
    have hzpow : (2 : ℝ) ^ (-(q_r : ℤ)) ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by dsimp [q_r, M, N]; omega)
    linarith
  have htri1 := abs_sub_le (sincTaylorRat N θ : ℝ) (rawSincTaylorRat (M + 1) θ_q : ℝ) (Real.sinc (θ : ℝ))
  have htri2 := abs_sub_le (rawSincTaylorRat (M + 1) θ_q : ℝ) (Real.sinc (θ_q : ℝ)) (Real.sinc (θ : ℝ))
  linarith

/-- Unrounded rational Taylor polynomial of $\int_0^z e^{-t^2} dt$. -/
def rawErfIntegralTaylorRat (N : ℕ) (z : ℚ) : ℚ :=
  ∑ m ∈ Finset.range N, (-1 : ℚ) ^ m * z ^ (2 * m + 1) / ((m.factorial : ℚ) * (2 * (m : ℚ) + 1))

theorem abs_rawErfIntegralTaylorRat_sub_integral_le (B q : ℕ) {z : ℚ} (hz : |(z : ℝ)| ≤ (B : ℝ)) :
    |(rawErfIntegralTaylorRat (4 * B ^ 2 + (q + B) + 1) z : ℝ) -
      ∫ t : ℝ in (0 : ℝ)..(z : ℝ), Real.exp (-(t ^ 2))| ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  set N : ℕ := 4 * B ^ 2 + (q + B) + 1
  have hsum_int : (rawErfIntegralTaylorRat N z : ℝ) =
      ∫ t : ℝ in (0 : ℝ)..(z : ℝ), ∑ m ∈ Finset.range N, (-(t ^ 2)) ^ m / (m.factorial : ℝ) := by
    rw [intervalIntegral.integral_finset_sum]
    · unfold rawErfIntegralTaylorRat
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      have hfun : (fun t : ℝ => (-(t ^ 2)) ^ m / (m.factorial : ℝ)) =
          (fun t : ℝ => ((-1 : ℝ) ^ m / (m.factorial : ℝ)) * t ^ (2 * m)) := by
        ext t; ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow,
        zero_pow (by omega : 2 * m + 1 ≠ 0), sub_zero]
      rw [Nat.cast_mul, Nat.cast_ofNat, div_mul_div_comm]
    · intro m _
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hint1 : IntervalIntegrable (fun t : ℝ => ∑ m ∈ Finset.range N, (-(t ^ 2)) ^ m / (m.factorial : ℝ))
      MeasureTheory.volume (0 : ℝ) (z : ℝ) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint2 : IntervalIntegrable (fun t : ℝ => Real.exp (-(t ^ 2)))
      MeasureTheory.volume (0 : ℝ) (z : ℝ) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hsum_int, ← intervalIntegral.integral_sub hint1 hint2, ← Real.norm_eq_abs]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) (z : ℝ),
      ‖(∑ m ∈ Finset.range N, (-(t ^ 2)) ^ m / (m.factorial : ℝ)) - Real.exp (-(t ^ 2))‖ ≤
        (2 : ℝ) ^ (-((q + B : ℕ) : ℤ)) := by
    intro t ht
    have ht_abs : |t| ≤ |(z : ℝ)| := by
      rcases le_total (0 : ℝ) (z : ℝ) with hz0 | hz0
      · rw [Set.uIoc_of_le hz0] at ht
        rw [abs_of_nonneg ht.1.le, abs_of_nonneg hz0]
        exact ht.2
      · rw [Set.uIoc_of_ge hz0] at ht
        rw [abs_of_nonpos ht.2, abs_of_nonpos hz0]
        linarith [ht.1]
    have ht_B : |t| ≤ (B : ℝ) := ht_abs.trans hz
    have ht2_B : ‖((-(t ^ 2) : ℝ) : ℂ)‖ ≤ ((B ^ 2 : ℕ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg t), ← sq_abs]
      push_cast
      exact pow_le_pow_left₀ (abs_nonneg t) ht_B 2
    have hexp := norm_exp_sub_sum_range_le_two_zpow (B ^ 2) (q + B) ht2_B
    have hcast : Complex.exp ((-(t ^ 2) : ℝ) : ℂ) -
        ∑ m ∈ Finset.range N, ((-(t ^ 2) : ℝ) : ℂ) ^ m / (m.factorial : ℂ) =
        ((Real.exp (-(t ^ 2)) - ∑ m ∈ Finset.range N, (-(t ^ 2)) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp]
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hexp
    simpa [Real.norm_eq_abs] using hexp
  calc ‖∫ t : ℝ in (0 : ℝ)..(z : ℝ),
          ((∑ m ∈ Finset.range N, (-(t ^ 2)) ^ m / (m.factorial : ℝ)) - Real.exp (-(t ^ 2)))‖
      ≤ (2 : ℝ) ^ (-((q + B : ℕ) : ℤ)) * |(z : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ (2 : ℝ) ^ (-((q + B : ℕ) : ℤ)) * (2 : ℝ) ^ B := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sub_zero]
        have hB_pow : (B : ℝ) ≤ (2 : ℝ) ^ B := by
          exact_mod_cast (Nat.lt_two_pow_self (n := B)).le
        exact hz.trans hB_pow
    _ = (2 : ℝ) ^ (-(q : ℤ)) := by
        rw [← zpow_natCast (2 : ℝ) B, ← zpow_add₀ (by norm_num)]
        congr 1
        omega

/-- Pure-integer single-pass fixed-point Taylor polynomial of $\int_0^z e^{-t^2} dt$
parameterized by `smul : ℤ → ℤ → ℤ` (Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def erfIntegralTaylorRatWithMul (smul : ℤ → ℤ → ℤ) (N : ℕ) (z : ℚ) : ℚ :=
  let M : ℕ := N + 6
  let q_z : ℕ := M
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let z_mant : ℤ := quantizeRatMantissa q_z z
  let r_mant : ℤ := - smul z_mant z_mant
  let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
  let S_inner : ℤ := ∑ m ∈ Finset.range (M + 1),
    roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ)
  ((smul z_mant S_inner : ℤ) : ℚ) / (2 : ℚ) ^ (q_z + q_acc)

/-- Pure-integer single-pass fixed-point Taylor polynomial of $\int_0^z e^{-t^2} dt$
(Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def erfIntegralTaylorRat (N : ℕ) (z : ℚ) : ℚ :=
  erfIntegralTaylorRatWithMul (· * ·) N z

/-- Error bound for `erfIntegralTaylorRat`: for $|z| \le B$,
$\left|\text{erfIntegralTaylorRat}(4B^2 + q + B + 1, z) - \int_0^z e^{-t^2} dt\right| \le 2^{-q}$
(Lemma 3.2 (`lem:elementary`); Table 3 (`tab:lean-map`) in Section 8 (`sec:lean`)). -/
theorem abs_erfIntegralTaylorRat_sub_integral_le (B q : ℕ) {z : ℚ} (hz : |(z : ℝ)| ≤ (B : ℝ)) :
    |(erfIntegralTaylorRat (4 * B ^ 2 + (q + B) + 1) z : ℝ) -
      ∫ t : ℝ in (0 : ℝ)..(z : ℝ), Real.exp (-(t ^ 2))| ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  set N : ℕ := 4 * B ^ 2 + (q + B) + 1
  set M : ℕ := N + 6
  set q_z : ℕ := M
  set q_r : ℕ := 2 * M
  set q_acc : ℕ := 3 * M + 6
  set z_mant : ℤ := quantizeRatMantissa q_z z
  set z_q : ℚ := quantizeRat q_z z
  set r_mant : ℤ := - (z_mant * z_mant)
  set arr : Array ℤ := expTermArrayFixed q_r q_acc M r_mant
  have hzq_eq : (z_mant : ℝ) * (2 : ℝ) ^ (-(q_z : ℤ)) = (z_q : ℝ) := by
    dsimp [z_q, quantizeRat, z_mant]
    push_cast
    rw [div_eq_mul_inv, ← zpow_natCast, zpow_neg]
  have hzq_abs : |(z_q : ℝ)| ≤ (B : ℝ) := abs_quantizeRat_le_of_le B q_z hz
  have hr_eq : (r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ)) = -((z_q : ℝ) ^ 2) := by
    have hqr : -(q_r : ℤ) = -(q_z : ℤ) + -(q_z : ℤ) := by dsimp [q_r, q_z]; omega
    rw [hqr, zpow_add₀ (by norm_num)]
    dsimp [r_mant]
    push_cast
    rw [← hzq_eq]
    ring
  have hr_abs : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ ((B ^ 2 : ℕ) : ℝ) := by
    rw [hr_eq, abs_neg, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    push_cast
    exact pow_le_pow_left₀ (abs_nonneg _) hzq_abs 2
  have hfp : |(erfIntegralTaylorRat N z : ℝ) - (rawErfIntegralTaylorRat (M + 1) z_q : ℝ)| ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hcast1 : (erfIntegralTaylorRat N z : ℝ) =
        (z_q : ℝ) * ∑ m ∈ Finset.range (M + 1),
          ((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
      change ((((z_mant * ∑ m ∈ Finset.range (M + 1),
        roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℚ) /
          (2 : ℚ) ^ (q_z + q_acc) : ℚ) : ℝ) = _
      push_cast
      rw [pow_add, ← div_div, div_eq_mul_inv _ ((2 : ℝ) ^ q_acc),
        mul_div_right_comm, div_eq_mul_inv (z_mant : ℝ), ← zpow_natCast (2 : ℝ) q_z, ← zpow_neg,
        hzq_eq, mul_assoc, Finset.sum_mul, ← zpow_natCast (2 : ℝ) q_acc, ← zpow_neg]
    have hcast2 : (rawErfIntegralTaylorRat (M + 1) z_q : ℝ) =
        (z_q : ℝ) * ∑ m ∈ Finset.range (M + 1),
          ((((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)) /
            ((2 * m + 1 : ℕ) : ℝ)) := by
      unfold rawErfIntegralTaylorRat
      simp only [← div_div]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hr_eq]
      have hpow : (z_q : ℝ) ^ (2 * m + 1) = (z_q : ℝ) * ((z_q : ℝ) ^ 2) ^ m := by
        rw [pow_succ', pow_mul]
      have hneg_pow : (-((z_q : ℝ) ^ 2)) ^ m = (-1 : ℝ) ^ m * ((z_q : ℝ) ^ 2) ^ m := by
        rw [← neg_one_mul ((z_q : ℝ) ^ 2), mul_pow]
      rw [hpow, hneg_pow]
      ring
    rw [hcast1, hcast2, ← mul_sub, abs_mul]
    have hinner :
        |∑ m ∈ Finset.range (M + 1),
          (((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
            ((((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)) /
              ((2 * m + 1 : ℕ) : ℝ)))| ≤
        (1 / 4 : ℝ) * (2 : ℝ) ^ (-((q + B : ℕ) : ℤ)) := by
      have hsum_le :
          |∑ m ∈ Finset.range (M + 1),
            (((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
              ((((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)) /
                ((2 * m + 1 : ℕ) : ℝ)))| ≤
          ((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (B ^ 2)) *
            ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hterm : ∀ m ∈ Finset.range (M + 1),
            |((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
              ((((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)) /
                ((2 * m + 1 : ℕ) : ℝ))| ≤
            ((M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (B ^ 2)) *
              ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) := by
          intro m hm
          rw [Finset.mem_range] at hm
          refine (abs_roundDivInt_expTermArrayFixed_getD_sub_le (B ^ 2) q_r q_acc M r_mant hr_abs
            (by omega : m ≤ M) (by omega : 1 ≤ 2 * m + 1)).trans ?_
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : m + 1 ≤ M + 1)) (by positivity))
            (by positivity)
        simpa using Finset.sum_le_sum hterm
      exact hsum_le.trans (sum_range_expTerm_err_le (B := B ^ 2) (M := M) (q_acc := q_acc)
        (q := q + B) (by dsimp [q_acc, M, N]; omega))
    rw [← Finset.sum_sub_distrib]
    have hB_pow : |(z_q : ℝ)| ≤ (2 : ℝ) ^ B := by
      have : (B : ℝ) ≤ (2 : ℝ) ^ B := by exact_mod_cast (Nat.lt_two_pow_self (n := B)).le
      exact hzq_abs.trans this
    calc |(z_q : ℝ)| *
          |∑ m ∈ Finset.range (M + 1),
            (((roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) -
              ((((r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))) ^ m / (m.factorial : ℝ)) /
                ((2 * m + 1 : ℕ) : ℝ)))|
        ≤ (2 : ℝ) ^ B * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-((q + B : ℕ) : ℤ))) :=
          mul_le_mul hB_pow hinner (abs_nonneg _) (by positivity)
      _ = (1 / 4 : ℝ) * ((2 : ℝ) ^ B * (2 : ℝ) ^ (-((q + B : ℕ) : ℤ))) := by ring
      _ = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
          rw [← zpow_natCast (2 : ℝ) B, ← zpow_add₀ (by norm_num)]
          congr 2; omega
  have hraw : |(rawErfIntegralTaylorRat (M + 1) z_q : ℝ) -
      ∫ t : ℝ in (0 : ℝ)..(z_q : ℝ), Real.exp (-(t ^ 2))| ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hM1 : M + 1 = 4 * B ^ 2 + ((q + 7) + B) + 1 := by dsimp [M, N]; ring
    rw [hM1]
    have h := abs_rawErfIntegralTaylorRat_sub_integral_le B (q + 7) hzq_abs
    have hle : (2 : ℝ) ^ (-((q + 7 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-((q + 2 : ℕ) : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hexp : -((q + 2 : ℕ) : ℤ) = (-2 : ℤ) + -(q : ℤ) := by omega
    have h4_inv : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [hexp, zpow_add₀ (by norm_num), h4_inv] at hle
    exact h.trans hle
  have hpert : |(∫ t : ℝ in (0 : ℝ)..(z_q : ℝ), Real.exp (-(t ^ 2))) -
      (∫ t : ℝ in (0 : ℝ)..(z : ℝ), Real.exp (-(t ^ 2)))| ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hlip := abs_erf_integral_sub_le (z_q : ℝ) (z : ℝ)
    have hdiff := abs_quantizeRat_sub_self_le q_z z
    have hq_le_qz : q ≤ q_z := by dsimp [q_z, M, N]; omega
    have hzpow : (2 : ℝ) ^ (-(q_z : ℤ)) ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have htri1 := abs_sub_le (erfIntegralTaylorRat N z : ℝ) (rawErfIntegralTaylorRat (M + 1) z_q : ℝ)
    (∫ t : ℝ in (0 : ℝ)..(z : ℝ), Real.exp (-(t ^ 2)))
  have htri2 := abs_sub_le (rawErfIntegralTaylorRat (M + 1) z_q : ℝ)
    (∫ t : ℝ in (0 : ℝ)..(z_q : ℝ), Real.exp (-(t ^ 2)))
    (∫ t : ℝ in (0 : ℝ)..(z : ℝ), Real.exp (-(t ^ 2)))
  linarith

/-- 1-Lipschitz continuity of $x \mapsto e^{-x}$ on $[0, \infty)$:
for $a, b \ge 0$, $|e^{-a} - e^{-b}| \le |a - b|$. -/
theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have haux : ∀ u v : ℝ, 0 ≤ u → u ≤ v → |Real.exp (-u) - Real.exp (-v)| ≤ v - u := by
    intro u v hu huv
    have hge : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hge)]
    have h1 : Real.exp (-u) - Real.exp (-v) = Real.exp (-u) * (1 - Real.exp (-(v - u))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2; ring
    have h2 : 1 - Real.exp (-(v - u)) ≤ v - u := by
      linarith [Real.add_one_le_exp (-(v - u))]
    have h3 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [h1]
    calc Real.exp (-u) * (1 - Real.exp (-(v - u)))
        ≤ 1 * (v - u) := mul_le_mul h3 h2 (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) zero_le_one
      _ = v - u := one_mul _
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    exact haux a b ha hab
  · rw [abs_sub_comm (Real.exp (-a)), abs_of_nonneg (sub_nonneg.mpr hba)]
    exact haux b a hb hba

/-- Hölder continuity of `Real.sqrt`: for $a, b \ge 0$ and $|a - b| \le \varepsilon^2$ ($\varepsilon \ge 0$),
$|\sqrt{a} - \sqrt{b}| \le \varepsilon$. -/
theorem abs_sqrt_sub_sqrt_le {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (hab : |a - b| ≤ ε ^ 2) :
    |Real.sqrt a - Real.sqrt b| ≤ ε := by
  have hsq : |Real.sqrt a - Real.sqrt b| ^ 2 ≤ ε ^ 2 := by
    have hsum_ge : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
      have h1 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
      have h2 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
      rw [abs_le]
      constructor <;> linarith
    have hprod : (Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b) = a - b := by
      calc (Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b)
          = (Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2 := by ring
        _ = a - b := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
    calc |Real.sqrt a - Real.sqrt b| ^ 2
        = |Real.sqrt a - Real.sqrt b| * |Real.sqrt a - Real.sqrt b| := sq _
      _ ≤ (Real.sqrt a + Real.sqrt b) * |Real.sqrt a - Real.sqrt b| :=
          mul_le_mul_of_nonneg_right hsum_ge (abs_nonneg _)
      _ = |a - b| := by
          rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a + Real.sqrt b), ← abs_mul, hprod]
      _ ≤ ε ^ 2 := hab
  rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq hε]
  exact Real.sqrt_le_sqrt hsq

/-- Quotient perturbation bound when denominators are $\ge 1$:
for $d_1, d_2 \ge 1$, $|a_1 / d_1 - a_2 / d_2| \le |a_1 - a_2| + |a_2| \cdot |d_1 - d_2|$. -/
theorem abs_div_sub_div_le_of_one_le {a1 a2 d1 d2 : ℝ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) :
    |a1 / d1 - a2 / d2| ≤ |a1 - a2| + |a2| * |d1 - d2| := by
  have hd1_pos : 0 < d1 := by linarith
  have hd2_pos : 0 < d2 := by linarith
  have h12 : 1 ≤ d1 * d2 := one_le_mul_of_one_le_of_one_le hd1 hd2
  have hsplit : a1 / d1 - a2 / d2 = (a1 - a2) / d1 + (a2 * (d2 - d1)) / (d1 * d2) := by
    field_simp [hd1_pos.ne', hd2_pos.ne']
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hd1_pos]
    exact div_le_self (abs_nonneg _) hd1
  · rw [abs_div, abs_mul, abs_sub_comm d2 d1, abs_of_pos (mul_pos hd1_pos hd2_pos)]
    exact div_le_self (by positivity) h12

/-- Clamping below by `c` does not increase distance to any `y ≥ c`. -/
theorem abs_max_sub_le_of_le {c x y : ℝ} (hy : c ≤ y) :
    |max c x - y| ≤ |x - y| := by
  rcases le_total c x with hcx | hxc
  · rw [max_eq_right hcx]
  · rw [max_eq_left hxc, abs_le]
    have hxy := abs_le.mp (le_refl |x - y|)
    constructor <;> linarith

/-- Clamping above by `c` does not increase distance to any `y ≤ c`. -/
theorem abs_min_sub_le_of_le {c x y : ℝ} (hy : y ≤ c) :
    |min c x - y| ≤ |x - y| := by
  rcases le_total c x with hcx | hxc
  · rw [min_eq_left hcx, abs_le]
    have hxy := abs_le.mp (le_refl |x - y|)
    constructor <;> linarith
  · rw [min_eq_right hxc]

/-- Computable fixed-point unit root approximation $\mathrm{Round}_q(e^{2\pi i \cdot \text{num}/\text{den}})$
via dynamic-precision rational Taylor series, hoisting `approxPiRat (q + 10)` outside `(num, den)`
(Lemma 3.2 (`lem:elementary`) and equation (7) (`eq:faithful-table`) in Section 3.3 (`sec:tables`)). -/
def expTwoPiIRatFixed (q : ℕ) : ℤ → ℕ → FixedComplex q :=
  let S : ℕ := q + 10
  let piRat : ℚ := approxPiRat S
  fun num den =>
    if den = 0 then ⟨0, 0⟩
    else
      let numMod : ℤ := num % (den : ℤ)
      let θ : ℚ := 2 * piRat * (numMod : ℚ) / (den : ℚ)
      let w : RatComplex := expITaylorRat (4 * 10 + S + 1) θ
      ⟨quantizeRatMantissa q w.re, quantizeRatMantissa q w.im⟩

/-- Accuracy bound for `expTwoPiIRatFixed`: for any `den > 0`, `expTwoPiIRatFixed q num den`
approximates `expTwoPiI ((num : ℝ) / (den : ℝ))` within $\frac{18}{25} 2^{-q}$
(Lemma 3.2 (`lem:elementary`) and equation (7) (`eq:faithful-table`)). -/
theorem norm_expTwoPiIRatFixed_sub_expTwoPiI_le (q : ℕ) (num : ℤ) {den : ℕ} (hden : 0 < den) :
    ‖(expTwoPiIRatFixed q num den).toComplex - expTwoPiI ((num : ℝ) / (den : ℝ))‖ ≤
      (18 / 25 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  have hden_ne : den ≠ 0 := ne_of_gt hden
  have hden_z_pos : (0 : ℤ) < (den : ℤ) := Nat.cast_pos.mpr hden
  have hden_r_pos : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  unfold expTwoPiIRatFixed
  rw [if_neg hden_ne]
  dsimp only
  set numMod : ℤ := num % (den : ℤ)
  set S : ℕ := q + 10
  set piRat : ℚ := approxPiRat S
  set θ : ℚ := 2 * piRat * (numMod : ℚ) / (den : ℚ)
  set w : RatComplex := expITaylorRat (4 * 10 + S + 1) θ
  have hquant_eq :
      (⟨quantizeRatMantissa q w.re, quantizeRatMantissa q w.im⟩ : FixedComplex q).toComplex =
        quantizeComplex q w.toComplex := by
    change (⟨quantizeRatMantissa q w.re, quantizeRatMantissa q w.im⟩ : FixedComplex q).toComplex =
      (quantizeComplexFixed q w.toComplex).toComplex
    congr 1
    ext <;> simp [quantizeComplexFixed, RatComplex.toComplex, quantizeRatMantissa_eq_quantizeRealMantissa]
  rw [hquant_eq]
  have hmod_div : num = (den : ℤ) * (num / (den : ℤ)) + numMod :=
    (Int.mul_ediv_add_emod num (den : ℤ)).symm
  have hexp_per : expTwoPiI ((num : ℝ) / (den : ℝ)) = expTwoPiI ((numMod : ℝ) / (den : ℝ)) := by
    have hsplit : (num : ℝ) / (den : ℝ) =
        (numMod : ℝ) / (den : ℝ) + ((num / (den : ℤ) : ℤ) : ℝ) := by
      have hcast : (num : ℝ) = (den : ℝ) * ((num / (den : ℤ) : ℤ) : ℝ) + (numMod : ℝ) := by
        exact_mod_cast hmod_div
      rw [hcast]
      field_simp [hden_r_pos.ne']
      ring
    rw [hsplit, expTwoPiI_add_int]
  rw [hexp_per]
  have hmod_nn : 0 ≤ (numMod : ℝ) := by
    exact_mod_cast Int.emod_nonneg num hden_z_pos.ne'
  have hmod_lt : (numMod : ℝ) < (den : ℝ) := by
    exact_mod_cast Int.emod_lt_of_pos num hden_z_pos
  have hfrac_nn : 0 ≤ (numMod : ℝ) / (den : ℝ) := div_nonneg hmod_nn hden_r_pos.le
  have hfrac_le : (numMod : ℝ) / (den : ℝ) ≤ 1 := (div_lt_one hden_r_pos).mpr hmod_lt |>.le
  have hpi_nn : 0 ≤ (piRat : ℝ) := by exact_mod_cast approxPiRat_nonneg S
  have hpi_le : (piRat : ℝ) ≤ 5 := by exact_mod_cast approxPiRat_le_five S
  have hθ_cast : (θ : ℝ) = 2 * (piRat : ℝ) * ((numMod : ℝ) / (den : ℝ)) := by
    dsimp [θ]
    push_cast
    ring
  have hθ_abs : |(θ : ℝ)| ≤ (10 : ℕ) := by
    rw [hθ_cast, abs_of_nonneg (by positivity)]
    push_cast
    nlinarith
  have h2S : (2 : ℝ) ^ (-(S : ℤ)) = (1 / 1024 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hexp : -(S : ℤ) = (-10 : ℤ) + -(q : ℤ) := by dsimp [S]; omega
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
  have hw_err : ‖w.toComplex - Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖ ≤
      (2 : ℝ) ^ (-(S : ℤ)) :=
    norm_expITaylorRat_sub_exp_le 10 S hθ_abs
  have hexp_true_eq : expTwoPiI ((numMod : ℝ) / (den : ℝ)) =
      Complex.exp (((2 * Real.pi * ((numMod : ℝ) / (den : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    unfold expTwoPiI
    push_cast
    rfl
  rw [hexp_true_eq]
  have hθ_diff : |(θ : ℝ) - 2 * Real.pi * ((numMod : ℝ) / (den : ℝ))| ≤
      2 * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hsub : (θ : ℝ) - 2 * Real.pi * ((numMod : ℝ) / (den : ℝ)) =
        2 * ((piRat : ℝ) - Real.pi) * ((numMod : ℝ) / (den : ℝ)) := by
      rw [hθ_cast]; ring
    rw [hsub, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hfrac_nn]
    have hpi_err : |(piRat : ℝ) - Real.pi| ≤ (2 : ℝ) ^ (-(S : ℤ)) := abs_approxPiRat_sub_pi_le S
    calc 2 * |(piRat : ℝ) - Real.pi| * ((numMod : ℝ) / (den : ℝ))
        ≤ 2 * (2 : ℝ) ^ (-(S : ℤ)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpi_err (by norm_num)) hfrac_le hfrac_nn (by positivity)
      _ = 2 * (2 : ℝ) ^ (-(S : ℤ)) := mul_one _
  have hexp_diff :
      ‖Complex.exp (((θ : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((2 * Real.pi * ((numMod : ℝ) / (den : ℝ)) : ℝ) : ℂ) * Complex.I)‖ ≤
        4 * (2 : ℝ) ^ (-(S : ℤ)) := by
    refine (norm_exp_ofReal_mul_I_sub_le _ _).trans ?_
    linarith
  have hq_err : ‖quantizeComplex q w.toComplex - w.toComplex‖ ≤
      (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) :=
    norm_quantizeComplex_sub_self_le q w.toComplex
  have htri1 := norm_sub_le_norm_sub_add_norm_sub
    (quantizeComplex q w.toComplex) w.toComplex
    (Complex.exp (((2 * Real.pi * ((numMod : ℝ) / (den : ℝ)) : ℝ) : ℂ) * Complex.I))
  have htri2 := norm_sub_le_norm_sub_add_norm_sub
    w.toComplex (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
    (Complex.exp (((2 * Real.pi * ((numMod : ℝ) / (den : ℝ)) : ℝ) : ℂ) * Complex.I))
  have hsqrt : Real.sqrt 2 ≤ (71 / 50 : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 71 / 50)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  nlinarith

/-- Exact relationship between `zetaPow r m` and `expTwoPiI ((m : ℝ) / ((2 * r : ℕ) : ℝ))`. -/
theorem zetaPow_eq_expTwoPiI_div_two_mul (r : ℕ) (m : ℤ) :
    zetaPow r m = expTwoPiI ((m : ℝ) / ((2 * r : ℕ) : ℝ)) := by
  unfold zetaPow expTwoPiI
  congr 1
  push_cast
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr
    field_simp [hr_ne]

/-- Accuracy bound for `expTwoPiIRatFixed q m (2 * r)` against `zetaPow r m`. -/
theorem norm_expTwoPiIRatFixed_sub_zetaPow_le (q : ℕ) {r : ℕ} (hr : 0 < r) (m : ℤ) :
    ‖(expTwoPiIRatFixed q m (2 * r)).toComplex - zetaPow r m‖ ≤
      (18 / 25 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  rw [zetaPow_eq_expTwoPiI_div_two_mul]
  exact norm_expTwoPiIRatFixed_sub_expTwoPiI_le q m (by omega : 0 < 2 * r)

/-- Computable integer spatial window half-width $m_{1,\ell}^{\text{comp}} = \lfloor \sqrt{p_{\text{work},\ell} p_{\ell+1}} \rfloor + 1$:
a pure-integer upper bound on the analytic formula
$m_{1,\ell} = \lceil \frac{2\ln 2}{\pi} \sqrt{p_{\text{work},\ell} p_{\ell+1}} \rceil$
(`m1Ell K p` in `IntMul.Schedule`) that avoids transcendental constants in the integer index bound
while remaining within the constant factor $\frac{\pi}{2\ln 2} \approx 2.266$ and satisfying
`m1Ell K p ≤ computeM1Ell K p ≤ pChildEll K p` (Lemma 6.5 (`lem:forward`) in
Section 6.3 (`sec:forward-error`), and Section 8 (`sec:lean`)). -/
def computeM1Ell (K p : ℕ) : ℕ :=
  Nat.sqrt (pWorkEll K p * pChildEll K p) + 1

theorem computeM1Ell_pos (K p : ℕ) : 0 < computeM1Ell K p := by
  unfold computeM1Ell
  omega

/-- The computable window half-width `computeM1Ell K p` is at least the analytic `m1Ell K p`
(Lemma 6.5 (`lem:forward`) and Section 8 (`sec:lean`)). -/
theorem m1Ell_le_computeM1Ell (K p : ℕ) : m1Ell K p ≤ computeM1Ell K p := by
  unfold m1Ell m1FromPWorkPChild alphaFromPWork
  rw [Nat.ceil_le]
  set pW : ℕ := pWorkEll K p
  set pC : ℕ := pChildEll K p
  set a : ℝ := ((pW : ℝ) * Real.log 2) / Real.pi
  set b : ℝ := ((pC : ℝ) * Real.log 2) / Real.pi
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_gt : 3 < Real.pi := Real.pi_gt_three
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_lt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have ha_nn : 0 ≤ a := by positivity
  have hb_nn : 0 ≤ b := by positivity
  have ha_le : a ≤ (pW : ℝ) / 2 := by
    dsimp [a]
    rw [div_le_div_iff₀ hpi_pos (by norm_num)]
    have : (0 : ℝ) ≤ (pW : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hb_le : b ≤ (pC : ℝ) / 2 := by
    dsimp [b]
    rw [div_le_div_iff₀ hpi_pos (by norm_num)]
    have : (0 : ℝ) ≤ (pC : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hsq_u : (2 * Real.sqrt a * Real.sqrt b) ^ 2 = 4 * a * b := by
    calc (2 * Real.sqrt a * Real.sqrt b) ^ 2
        = 4 * (Real.sqrt a) ^ 2 * (Real.sqrt b) ^ 2 := by ring
      _ = 4 * a * b := by rw [Real.sq_sqrt ha_nn, Real.sq_sqrt hb_nn]
  have hab_le : 4 * a * b ≤ (pW : ℝ) * (pC : ℝ) := by nlinarith
  have hsqrt_nat : pW * pC ≤ (computeM1Ell K p) ^ 2 :=
    le_of_lt (Nat.lt_succ_sqrt' (pW * pC))
  have hsqrt_real : (pW : ℝ) * (pC : ℝ) ≤ ((computeM1Ell K p : ℝ)) ^ 2 := by
    exact_mod_cast hsqrt_nat
  have hsq_le : (2 * Real.sqrt a * Real.sqrt b) ^ 2 ≤ ((computeM1Ell K p : ℝ)) ^ 2 := by
    linarith
  rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.sqrt a * Real.sqrt b),
    ← Real.sqrt_sq (Nat.cast_nonneg (computeM1Ell K p))]
  exact Real.sqrt_le_sqrt hsq_le

/-- The computable window half-width `computeM1Ell K p` is at most `pChildEll K p`. -/
theorem computeM1Ell_le_pChildEll (K p : ℕ) : computeM1Ell K p ≤ pChildEll K p := by
  unfold computeM1Ell
  set a : ℕ := pWorkEll K p
  set b : ℕ := pChildEll K p
  have hab : a < b := by dsimp [a, b]; unfold pChildEll; omega
  have hb : 0 < b := by omega
  have hlt : a * b < b * b := Nat.mul_lt_mul_of_pos_right hab hb
  exact Nat.succ_le_of_lt (Nat.sqrt_lt.mpr hlt)

/-- Algebraic simplification of the Sinc-Gaussian exponent at `alphaEll K p`:
$-\pi t^2 / \alpha_\ell^2 = -(\pi t)^2 / (4 p_{\text{work},\ell} \ln 2)$. -/
theorem gaussian_arg_alphaEll_eq (K p : ℕ) (t : ℝ) :
    -Real.pi * t ^ 2 / (alphaEll K p) ^ 2 =
      -((Real.pi * t) ^ 2 / (4 * (pWorkEll K p : ℝ) * Real.log 2)) := by
  unfold alphaEll alphaFromPWork
  set pW : ℕ := pWorkEll K p
  have hpW_pos : (0 : ℝ) < (pW : ℝ) := by
    have : 0 < pW := by dsimp [pW]; unfold pWorkEll; omega
    exact_mod_cast this
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hrad_nn : 0 ≤ ((pW : ℝ) * Real.log 2) / Real.pi :=
    div_nonneg (mul_nonneg hpW_pos.le hlog_pos.le) hpi_pos.le
  have hsq : (2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi)) ^ 2 =
      4 * (((pW : ℝ) * Real.log 2) / Real.pi) := by
    rw [mul_pow, Real.sq_sqrt hrad_nn]
    ring
  rw [hsq]
  field_simp [hpW_pos.ne', hlog_pos.ne', hpi_pos.ne']

theorem fitsSignedWord_quantizeRatMantissa_of_abs_le_one (q : ℕ) {x : ℚ}
    (hx : |(x : ℝ)| ≤ 1) :
    FitsSignedWord (q + 1) (quantizeRatMantissa q x) := by
  rw [quantizeRatMantissa_eq_quantizeRealMantissa]
  have hbd := (wordWidthBounds_quantizeComplexFixed_of_norm_le (b := 0) (q := q)
    (z := ((x : ℝ) : ℂ)) (by simpa [Complex.norm_real] using hx)).1
  simpa [quantizeComplexFixed] using hbd

theorem cast_quantizeRatMantissa_mul_zpow (q : ℕ) (x : ℚ) :
    (quantizeRatMantissa q x : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) = quantizeReal q (x : ℝ) := by
  rw [quantizeRatMantissa_eq_quantizeRealMantissa, quantizeReal]

theorem cast_max_zero_quantizeRatMantissa_mul_zpow (q : ℕ) (x : ℚ) :
    ((max 0 (quantizeRatMantissa q x) : ℤ) : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) =
      max 0 (quantizeReal q (x : ℝ)) := by
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(q : ℤ)) := (zpow_pos (by norm_num) _).le
  rw [Int.cast_max, Int.cast_zero, max_mul_of_nonneg _ _ hpos, zero_mul,
    cast_quantizeRatMantissa_mul_zpow]

/-- Computable rational sinc-Gaussian filter tap value before fixed-point quantization,
hoisting `(piVal, log2Val)` per level `(K, p)` and using $O(p_{\text{child},\ell})$ Taylor terms
`B_exp = 25 * (pC + 1)` (Theorem 4.2 (`thm:poisson`) in Section 4.2 (`sec:poisson`),
Lemma 3.2 (`lem:elementary`), and Section 8 (`sec:lean`)). -/
def computeFilterTapRat (K p : ℕ) : Fin (t1Ell K) → ℤ → ℚ :=
  let m1 : ℕ := computeM1Ell K p
  let t1 : ℕ := t1Ell K
  let pW : ℕ := pWorkEll K p
  let pC : ℕ := pChildEll K p
  let q : ℕ := qChildEll K p
  let S : ℕ := q + 3 * pC + 20
  let piVal : ℚ := approxPiRat S
  let log2Val : ℚ := max (1 / 2) (approxLogTwoRat S)
  let B_sinc : ℕ := 5 * (m1 + 1)
  let B_exp : ℕ := 25 * (pC + 1)
  fun j1 d =>
    let tRat : ℚ := (d : ℚ) - (j1.val : ℚ) / (t1 : ℚ)
    let θ : ℚ := piVal * tRat
    let sincVal : ℚ := max (-1) (min 1 (sincTaylorRat (4 * B_sinc + S + 1) θ))
    let gRat : ℚ := θ ^ 2 / (4 * (pW : ℚ) * log2Val)
    let expVal : ℚ := max 0 (min 1 (expTaylorRat (4 * B_exp + S + 1) (-gRat)))
    sincVal * expVal

/-- Computable dynamic-precision rational sinc-Gaussian filter tap generator, hoisting the
per-level constants of `computeFilterTapRat K p` (Theorem 4.2 (`thm:poisson`),
Lemma 3.2 (`lem:elementary`), and Section 8 (`sec:lean`)). -/
def computeFilterTapFixed (K p : ℕ) : Fin (t1Ell K) → ℤ → ℤ :=
  let m1 : ℕ := computeM1Ell K p
  let q : ℕ := qChildEll K p
  let tapRat : Fin (t1Ell K) → ℤ → ℚ := computeFilterTapRat K p
  fun j1 d =>
    if |d| ≤ (m1 : ℤ) then
      quantizeRatMantissa q (tapRat j1 d)
    else 0

theorem abs_computeFilterTapRat_le_one (K p : ℕ) (j1 : Fin (t1Ell K)) (d : ℤ) :
    |(computeFilterTapRat K p j1 d : ℝ)| ≤ 1 := by
  unfold computeFilterTapRat
  dsimp only
  generalize sincTaylorRat _ _ = sRaw
  generalize expTaylorRat _ _ = eRaw
  set sincVal : ℚ := max (-1) (min 1 sRaw)
  set expVal : ℚ := max 0 (min 1 eRaw)
  have hsinc_lo : (-1 : ℝ) ≤ (sincVal : ℝ) := by
    dsimp [sincVal]; push_cast; exact le_max_left _ _
  have hsinc_hi : (sincVal : ℝ) ≤ 1 := by
    dsimp [sincVal]; push_cast; exact max_le (by norm_num) (min_le_left _ _)
  have hexp_lo : (0 : ℝ) ≤ (expVal : ℝ) := by
    dsimp [expVal]; push_cast; exact le_max_left _ _
  have hexp_hi : (expVal : ℝ) ≤ 1 := by
    dsimp [expVal]; push_cast; exact max_le (by norm_num) (min_le_left _ _)
  push_cast
  rw [abs_mul, abs_of_nonneg hexp_lo]
  have hsinc_abs : |(sincVal : ℝ)| ≤ 1 := abs_le.mpr ⟨hsinc_lo, hsinc_hi⟩
  nlinarith

/-- Every tap produced by `computeFilterTapFixed K p j1 d` fits in `qChildEll K p + 1` signed bits. -/
theorem fitsSignedWord_computeFilterTapFixed (K p : ℕ) (j1 : Fin (t1Ell K)) (d : ℤ) :
    FitsSignedWord (qChildEll K p + 1) (computeFilterTapFixed K p j1 d) := by
  unfold computeFilterTapFixed
  split_ifs with hd
  · exact fitsSignedWord_quantizeRatMantissa_of_abs_le_one (qChildEll K p)
      (abs_computeFilterTapRat_le_one K p j1 d)
  · unfold FitsSignedWord
    simp

theorem abs_computeFilterTapRat_sub_sincGaussian_le (K p : ℕ) (j1 : Fin (t1Ell K)) {d : ℤ}
    (hd : |d| ≤ (computeM1Ell K p : ℤ)) :
    |(computeFilterTapRat K p j1 d : ℝ) -
      sincGaussian (alphaEll K p) ((d : ℝ) - fractionalShift j1)| ≤
      (1 / 100 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) := by
  unfold computeFilterTapRat
  dsimp only
  set m1 : ℕ := computeM1Ell K p
  set pW : ℕ := pWorkEll K p
  set pC : ℕ := pChildEll K p
  set q : ℕ := qChildEll K p
  set S : ℕ := q + 3 * pC + 20
  set tRat : ℚ := (d : ℚ) - (j1.val : ℚ) / (t1Ell K : ℚ)
  generalize hpiVal : approxPiRat S = piVal
  generalize hl2Raw : approxLogTwoRat S = l2Raw
  set log2Val : ℚ := max (1 / 2) l2Raw
  set θ : ℚ := piVal * tRat
  set B_sinc : ℕ := 5 * (m1 + 1)
  generalize hsRaw : sincTaylorRat (4 * B_sinc + S + 1) θ = sRaw
  set sincVal : ℚ := max (-1) (min 1 sRaw)
  set gRat : ℚ := θ ^ 2 / (4 * (pW : ℚ) * log2Val)
  set B_exp : ℕ := 25 * (pC + 1)
  generalize heRaw : expTaylorRat (4 * B_exp + S + 1) (-gRat) = eRaw
  set expVal : ℚ := max 0 (min 1 eRaw)
  have ht_eq : ((d : ℝ) - fractionalShift j1) = (tRat : ℝ) := by
    dsimp [tRat, fractionalShift]
    push_cast
    rfl
  rw [ht_eq]
  unfold sincGaussian
  rw [sinc_eq_real_sinc, gaussian_arg_alphaEll_eq]
  set t : ℝ := (tRat : ℝ)
  set sincTrue : ℝ := Real.sinc (Real.pi * t)
  set gTrue : ℝ := (Real.pi * t) ^ 2 / (4 * (pW : ℝ) * Real.log 2)
  set expTrue : ℝ := Real.exp (-gTrue)
  have hd_abs_r : |(d : ℝ)| ≤ (m1 : ℝ) := by exact_mod_cast hd
  have hfrac_nn : 0 ≤ fractionalShift j1 := fractionalShift_nonneg j1
  have hfrac_le : fractionalShift j1 ≤ 1 := fractionalShift_le_one j1
  have ht_abs : |t| ≤ (m1 : ℝ) + 1 := by
    have : t = (d : ℝ) - fractionalShift j1 := ht_eq.symm
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hfrac_nn]
    linarith
  have hm1_le_pC : (m1 : ℝ) ≤ (pC : ℝ) := by exact_mod_cast computeM1Ell_le_pChildEll K p
  have ht_abs_pC : |t| ≤ (pC : ℝ) + 1 := by linarith
  have hpi_nn : 0 ≤ (piVal : ℝ) := by
    rw [← hpiVal]; exact_mod_cast approxPiRat_nonneg S
  have hpi_le : (piVal : ℝ) ≤ 5 := by
    rw [← hpiVal]; exact_mod_cast approxPiRat_le_five S
  have hθ_cast : (θ : ℝ) = (piVal : ℝ) * t := by dsimp [θ, t]; push_cast; rfl
  have hθ_abs : |(θ : ℝ)| ≤ (B_sinc : ℝ) := by
    rw [hθ_cast, abs_mul, abs_of_nonneg hpi_nn]
    calc (piVal : ℝ) * |t|
        ≤ 5 * ((m1 : ℝ) + 1) := mul_le_mul hpi_le ht_abs (abs_nonneg t) (by norm_num)
      _ = (B_sinc : ℝ) := by dsimp [B_sinc]; push_cast; ring
  have hpi_err : |(piVal : ℝ) - Real.pi| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
    rw [← hpiVal]; exact abs_approxPiRat_sub_pi_le S
  have hθ_diff : |(θ : ℝ) - Real.pi * t| ≤ ((pC : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hsub : (θ : ℝ) - Real.pi * t = ((piVal : ℝ) - Real.pi) * t := by
      rw [hθ_cast]; ring
    rw [hsub, abs_mul]
    calc |(piVal : ℝ) - Real.pi| * |t|
        ≤ (2 : ℝ) ^ (-(S : ℤ)) * ((pC : ℝ) + 1) :=
          mul_le_mul hpi_err ht_abs_pC (abs_nonneg _) (by positivity)
      _ = ((pC : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ)) := by ring
  have hsinc_clamp : |(sincVal : ℝ) - Real.sinc (θ : ℝ)| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
    have h1 : (sincVal : ℝ) = max (-1 : ℝ) (min 1 (sRaw : ℝ)) := by
      dsimp [sincVal]; push_cast; rfl
    rw [h1]
    have hbds := abs_le.mp (Real.abs_sinc_le_one (θ : ℝ))
    have htaylor : |(sRaw : ℝ) - Real.sinc (θ : ℝ)| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← hsRaw]; exact abs_sincTaylorRat_sub_sinc_le B_sinc S hθ_abs
    exact (abs_max_sub_le_of_le hbds.1).trans
      ((abs_min_sub_le_of_le hbds.2).trans htaylor)
  have hsinc_err : |(sincVal : ℝ) - sincTrue| ≤ ((pC : ℝ) + 2) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have htri := abs_sub_le (sincVal : ℝ) (Real.sinc (θ : ℝ)) sincTrue
    have hlip := (abs_sinc_sub_sinc_le (θ : ℝ) (Real.pi * t)).trans hθ_diff
    linarith
  have hlog2_ge : (1 / 2 : ℝ) ≤ (log2Val : ℝ) := by
    dsimp [log2Val]; push_cast; exact le_max_left _ _
  have hlog2_true_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_err : |(log2Val : ℝ) - Real.log 2| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
    have h1 : (log2Val : ℝ) = max (1 / 2 : ℝ) (l2Raw : ℝ) := by
      dsimp [log2Val]; push_cast; rfl
    rw [h1]
    have htaylor : |(l2Raw : ℝ) - Real.log 2| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← hl2Raw]; exact abs_approxLogTwoRat_sub_log_two_le S
    exact (abs_max_sub_le_of_le hlog2_true_ge).trans htaylor
  have hpW_ge1 : (1 : ℝ) ≤ (pW : ℝ) := by
    have : 1 ≤ pW := by dsimp [pW]; unfold pWorkEll; omega
    exact_mod_cast this
  have hpW_le_pC : (pW : ℝ) ≤ (pC : ℝ) := by
    have : pW ≤ pC := by dsimp [pW, pC]; unfold pChildEll; omega
    exact_mod_cast this
  have hden1_ge : 1 ≤ 4 * (pW : ℝ) * (log2Val : ℝ) := by
    calc (1 : ℝ) ≤ 4 * 1 * (1 / 2) := by norm_num
      _ ≤ 4 * (pW : ℝ) * (log2Val : ℝ) :=
        mul_le_mul (by linarith) hlog2_ge (by norm_num) (by positivity)
  have hden2_ge : 1 ≤ 4 * (pW : ℝ) * Real.log 2 := by
    calc (1 : ℝ) ≤ 4 * 1 * (1 / 2) := by norm_num
      _ ≤ 4 * (pW : ℝ) * Real.log 2 :=
        mul_le_mul (by linarith) hlog2_true_ge (by norm_num) (by positivity)
  have hgRat_cast : (gRat : ℝ) = (θ : ℝ) ^ 2 / (4 * (pW : ℝ) * (log2Val : ℝ)) := by
    dsimp [gRat]; push_cast; rfl
  have hgRat_nn : 0 ≤ (gRat : ℝ) := by rw [hgRat_cast]; positivity
  have hgTrue_nn : 0 ≤ gTrue := by
    dsimp [gTrue]
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hneg_gRat_abs : |((-gRat : ℚ) : ℝ)| ≤ (B_exp : ℝ) := by
    push_cast
    rw [abs_neg, abs_of_nonneg hgRat_nn, hgRat_cast]
    have hden_pos : 0 < 4 * (pW : ℝ) * (log2Val : ℝ) := by linarith
    rw [div_le_iff₀ hden_pos]
    have hθ2 : (θ : ℝ) ^ 2 ≤ 25 * ((m1 : ℝ) + 1) ^ 2 := by
      have h1 : |(θ : ℝ)| ^ 2 ≤ (B_sinc : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hθ_abs 2
      rw [sq_abs] at h1
      have h2 : (B_sinc : ℝ) ^ 2 = 25 * ((m1 : ℝ) + 1) ^ 2 := by
        dsimp [B_sinc]; push_cast; ring
      linarith
    have hm1_sq_nat : (m1 + 1) ^ 2 ≤ 2 * pW * (pC + 1) := by
      set s : ℕ := Nat.sqrt (pW * pC)
      have hm1_eq : m1 = s + 1 := rfl
      have hs_sq : s * s ≤ pW * pC := Nat.sqrt_le (pW * pC)
      have hs_le : s ≤ pC := by have := computeM1Ell_le_pChildEll K p; omega
      have hpW6 : 6 ≤ pW := by dsimp [pW]; unfold pWorkEll; omega
      have h4s : 4 * s ≤ pW * pC :=
        (Nat.mul_le_mul_left 4 hs_le).trans (Nat.mul_le_mul_right pC (by omega))
      calc (m1 + 1) ^ 2 = s * s + 4 * s + 4 := by rw [hm1_eq]; ring
        _ ≤ pW * pC + pW * pC + 2 * pW := by omega
        _ = 2 * pW * (pC + 1) := by ring
    have hm1_sq_r : ((m1 : ℝ) + 1) ^ 2 ≤ 2 * (pW : ℝ) * ((pC : ℝ) + 1) := by
      exact_mod_cast hm1_sq_nat
    have hden_2pW : 2 * (pW : ℝ) ≤ 4 * (pW : ℝ) * (log2Val : ℝ) := by
      calc 2 * (pW : ℝ) = 4 * (pW : ℝ) * (1 / 2) := by ring
        _ ≤ 4 * (pW : ℝ) * (log2Val : ℝ) :=
          mul_le_mul_of_nonneg_left hlog2_ge (by positivity)
    have hB_exp_eq : (B_exp : ℝ) = 25 * ((pC : ℝ) + 1) := by
      dsimp [B_exp]; push_cast; ring
    rw [hB_exp_eq]
    calc (θ : ℝ) ^ 2
        ≤ 25 * (2 * (pW : ℝ) * ((pC : ℝ) + 1)) := by linarith
      _ = (2 * (pW : ℝ)) * (25 * ((pC : ℝ) + 1)) := by ring
      _ ≤ (4 * (pW : ℝ) * (log2Val : ℝ)) * (25 * ((pC : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hden_2pW (by positivity)
      _ = 25 * ((pC : ℝ) + 1) * (4 * (pW : ℝ) * (log2Val : ℝ)) := by ring
  have hexp_clamp : |(expVal : ℝ) - Real.exp (-(gRat : ℝ))| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
    have h1 : (expVal : ℝ) = max (0 : ℝ) (min 1 (eRaw : ℝ)) := by
      dsimp [expVal]; push_cast; rfl
    rw [h1]
    have hexp_lo : (0 : ℝ) ≤ Real.exp (-(gRat : ℝ)) := (Real.exp_pos _).le
    have hexp_hi : Real.exp (-(gRat : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have htaylor : |(eRaw : ℝ) - Real.exp (-(gRat : ℝ))| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← heRaw]
      have hraw := abs_expTaylorRat_sub_exp_le B_exp S hneg_gRat_abs
      rwa [Rat.cast_neg] at hraw
    exact (abs_max_sub_le_of_le hexp_lo).trans ((abs_min_sub_le_of_le hexp_hi).trans htaylor)
  have hpi_le4 : Real.pi ≤ 4 := by linarith [Real.pi_lt_d4]
  have hpit_abs : |Real.pi * t| ≤ 4 * ((pC : ℝ) + 1) := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul hpi_le4 ht_abs_pC (abs_nonneg t) (by norm_num)
  have hθ_abs_pC : |(θ : ℝ)| ≤ 5 * ((pC : ℝ) + 1) := by
    rw [hθ_cast, abs_mul, abs_of_nonneg hpi_nn]
    exact mul_le_mul hpi_le ht_abs_pC (abs_nonneg t) (by norm_num)
  have hθ2_diff : |(θ : ℝ) ^ 2 - (Real.pi * t) ^ 2| ≤
      9 * ((pC : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hsub : (θ : ℝ) ^ 2 - (Real.pi * t) ^ 2 =
        ((θ : ℝ) + Real.pi * t) * ((θ : ℝ) - Real.pi * t) := by ring
    rw [hsub, abs_mul]
    have hsum_abs : |(θ : ℝ) + Real.pi * t| ≤ 9 * ((pC : ℝ) + 1) := by
      refine (abs_add_le _ _).trans ?_
      linarith
    calc |(θ : ℝ) + Real.pi * t| * |(θ : ℝ) - Real.pi * t|
        ≤ (9 * ((pC : ℝ) + 1)) * (((pC : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ))) :=
          mul_le_mul hsum_abs hθ_diff (abs_nonneg _) (by positivity)
      _ = 9 * ((pC : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (-(S : ℤ)) := by ring
  have hden_diff : |4 * (pW : ℝ) * (log2Val : ℝ) - 4 * (pW : ℝ) * Real.log 2| ≤
      4 * (pC : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hsub : 4 * (pW : ℝ) * (log2Val : ℝ) - 4 * (pW : ℝ) * Real.log 2 =
        4 * (pW : ℝ) * ((log2Val : ℝ) - Real.log 2) := by ring
    rw [hsub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (pW : ℝ))]
    calc 4 * (pW : ℝ) * |(log2Val : ℝ) - Real.log 2|
        ≤ (4 * (pC : ℝ)) * (2 : ℝ) ^ (-(S : ℤ)) :=
          mul_le_mul (by linarith) hlog2_err (abs_nonneg _) (by positivity)
      _ = 4 * (pC : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) := by ring
  have hpit2_le : |(Real.pi * t) ^ 2| ≤ 16 * ((pC : ℝ) + 1) ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |Real.pi * t| ^ 2
        ≤ (4 * ((pC : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hpit_abs 2
      _ = 16 * ((pC : ℝ) + 1) ^ 2 := by ring
  have hg_diff : |(gRat : ℝ) - gTrue| ≤
      (9 * ((pC : ℝ) + 1) ^ 2 + 64 * (pC : ℝ) * ((pC : ℝ) + 1) ^ 2) *
        (2 : ℝ) ^ (-(S : ℤ)) := by
    rw [hgRat_cast]
    refine (abs_div_sub_div_le_of_one_le hden1_ge hden2_ge).trans ?_
    have hmul : |(Real.pi * t) ^ 2| * |4 * (pW : ℝ) * (log2Val : ℝ) - 4 * (pW : ℝ) * Real.log 2| ≤
        16 * ((pC : ℝ) + 1) ^ 2 * (4 * (pC : ℝ) * (2 : ℝ) ^ (-(S : ℤ))) :=
      mul_le_mul hpit2_le hden_diff (abs_nonneg _) (by positivity)
    linarith
  have hexp_err : |(expVal : ℝ) - expTrue| ≤
      (1 + 9 * ((pC : ℝ) + 1) ^ 2 + 64 * (pC : ℝ) * ((pC : ℝ) + 1) ^ 2) *
        (2 : ℝ) ^ (-(S : ℤ)) := by
    have htri := abs_sub_le (expVal : ℝ) (Real.exp (-(gRat : ℝ))) expTrue
    have hlip := (abs_exp_neg_sub_exp_neg_le hgRat_nn hgTrue_nn).trans hg_diff
    linarith
  have hexpVal_abs : |(expVal : ℝ)| ≤ 1 := by
    have hexp_lo : (0 : ℝ) ≤ (expVal : ℝ) := by
      dsimp [expVal]; push_cast; exact le_max_left _ _
    have hexp_hi : (expVal : ℝ) ≤ 1 := by
      dsimp [expVal]; push_cast; exact max_le (by norm_num) (min_le_left _ _)
    exact abs_le.mpr ⟨by linarith, hexp_hi⟩
  have hsincTrue_abs : |sincTrue| ≤ 1 := Real.abs_sinc_le_one _
  have hprod_err : |((sincVal * expVal : ℚ) : ℝ) - sincTrue * expTrue| ≤
      (((pC : ℝ) + 2) + (1 + 9 * ((pC : ℝ) + 1) ^ 2 + 64 * (pC : ℝ) * ((pC : ℝ) + 1) ^ 2)) *
        (2 : ℝ) ^ (-(S : ℤ)) := by
    push_cast
    have hsplit : (sincVal : ℝ) * (expVal : ℝ) - sincTrue * expTrue =
        ((sincVal : ℝ) - sincTrue) * (expVal : ℝ) + sincTrue * ((expVal : ℝ) - expTrue) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |(sincVal : ℝ) - sincTrue| * |(expVal : ℝ)| ≤
        (((pC : ℝ) + 2) * (2 : ℝ) ^ (-(S : ℤ))) * 1 :=
      mul_le_mul hsinc_err hexpVal_abs (abs_nonneg _) (by positivity)
    have h2 : |sincTrue| * |(expVal : ℝ) - expTrue| ≤
        1 * ((1 + 9 * ((pC : ℝ) + 1) ^ 2 + 64 * (pC : ℝ) * ((pC : ℝ) + 1) ^ 2) *
          (2 : ℝ) ^ (-(S : ℤ))) :=
      mul_le_mul hsincTrue_abs hexp_err (abs_nonneg _) zero_le_one
    linarith
  have hp1 : ((pC : ℝ) + 1) ≤ (2 : ℝ) ^ pC := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := pC))
  have hpC_nn : (0 : ℝ) ≤ (pC : ℝ) := Nat.cast_nonneg _
  have hpC_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ pC := by
    exact_mod_cast (Nat.one_le_two_pow (n := pC))
  have hcube :
      ((pC : ℝ) + 2) + (1 + 9 * ((pC : ℝ) + 1) ^ 2 + 64 * (pC : ℝ) * ((pC : ℝ) + 1) ^ 2) ≤
        100 * ((2 : ℝ) ^ (3 * pC)) := by
    have hpow3 : ((2 : ℝ) ^ pC) ^ 3 = (2 : ℝ) ^ (3 * pC) := by
      rw [← pow_mul, mul_comm]
    rw [← hpow3]
    have hsq : ((pC : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ pC) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hp1 2
    have h3 : (pC : ℝ) * ((pC : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ pC) ^ 3 := by
      calc (pC : ℝ) * ((pC : ℝ) + 1) ^ 2
          ≤ (2 : ℝ) ^ pC * ((2 : ℝ) ^ pC) ^ 2 :=
            mul_le_mul (by linarith) hsq (sq_nonneg _) (by positivity)
        _ = ((2 : ℝ) ^ pC) ^ 3 := by ring
    have h1_le_2 : (2 : ℝ) ^ pC ≤ ((2 : ℝ) ^ pC) ^ 2 := le_self_pow₀ hpC_ge1 (by omega : 2 ≠ 0)
    have h1_le_3 : (2 : ℝ) ^ pC ≤ ((2 : ℝ) ^ pC) ^ 3 := le_self_pow₀ hpC_ge1 (by omega : 3 ≠ 0)
    have h2_le_3 : ((2 : ℝ) ^ pC) ^ 2 ≤ ((2 : ℝ) ^ pC) ^ 3 := by
      calc ((2 : ℝ) ^ pC) ^ 2
          = ((2 : ℝ) ^ pC) ^ 2 * 1 := (mul_one _).symm
        _ ≤ ((2 : ℝ) ^ pC) ^ 2 * (2 : ℝ) ^ pC :=
          mul_le_mul_of_nonneg_left hpC_ge1 (by positivity)
        _ = ((2 : ℝ) ^ pC) ^ 3 := by ring
    linarith
  have h2S : (2 : ℝ) ^ (-(S : ℤ)) =
      (2 : ℝ) ^ (-((3 * pC : ℕ) : ℤ)) * (1 / 1048576 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hexp : -(S : ℤ) = -((3 * pC : ℕ) : ℤ) + (-20 : ℤ) + -(q : ℤ) := by
      dsimp [S]; omega
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    norm_num
  have h1 := hprod_err.trans (mul_le_mul_of_nonneg_right hcube (by positivity))
  rw [h2S] at h1
  have hcancel : (2 : ℝ) ^ (3 * pC) * (2 : ℝ) ^ (-((3 * pC : ℕ) : ℤ)) = 1 :=
    two_pow_mul_two_zpow_neg (3 * pC)
  have hrhs :
      100 * (2 : ℝ) ^ (3 * pC) *
        ((2 : ℝ) ^ (-((3 * pC : ℕ) : ℤ)) * (1 / 1048576 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) =
      (100 / 1048576 : ℝ) * ((2 : ℝ) ^ (3 * pC) * (2 : ℝ) ^ (-((3 * pC : ℕ) : ℤ))) *
        (2 : ℝ) ^ (-(q : ℤ)) := by ring
  rw [hrhs, hcancel, mul_one] at h1
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  linarith

/-- Accuracy bound for `computeFilterTapFixed`: for all `(K, p)`, `j1`, and `d`,
`computeFilterTapFixed K p j1 d` approximates `filterTap (alphaEll K p) (computeM1Ell K p) (t1Ell K) j1 d`
within $\frac{51}{100} 2^{-q_{\text{child},\ell}}$ (Lemma 3.2 (`lem:elementary`) and
equation (7) (`eq:faithful-table`)). -/
theorem abs_computeFilterTapFixed_sub_filterTap_le (K p : ℕ) (j1 : Fin (t1Ell K)) (d : ℤ) :
    |((computeFilterTapFixed K p j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
      filterTap (alphaEll K p) (computeM1Ell K p) (t1Ell K) j1 d| ≤
      (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) := by
  unfold computeFilterTapFixed filterTap
  split_ifs with hd
  · rw [cast_quantizeRatMantissa_mul_zpow]
    have hq_err := abs_quantizeReal_sub_self_le (qChildEll K p) (computeFilterTapRat K p j1 d : ℝ)
    have hrat_err := abs_computeFilterTapRat_sub_sincGaussian_le K p j1 hd
    have htri := abs_sub_le (quantizeReal (qChildEll K p) (computeFilterTapRat K p j1 d : ℝ))
      (computeFilterTapRat K p j1 d : ℝ)
      (sincGaussian (alphaEll K p) ((d : ℝ) - fractionalShift j1))
    linarith
  · simp only [Int.cast_zero, zero_mul, sub_zero, abs_zero]
    exact mul_nonneg (by norm_num) (by positivity)

/-- Algebraic simplification of $\sqrt{\pi} \alpha_\ell = \sqrt{4 p_{\text{work},\ell} \ln 2}$
(Section 4.2 (`sec:poisson`) and Theorem 5.1 (`thm:deconv`)). -/
theorem sqrt_pi_mul_alphaEll_eq (K p : ℕ) :
    Real.sqrt Real.pi * alphaEll K p =
      Real.sqrt (4 * (pWorkEll K p : ℝ) * Real.log 2) := by
  set pW : ℕ := pWorkEll K p
  have hpW_nn : (0 : ℝ) ≤ (pW : ℝ) := Nat.cast_nonneg _
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hrad_nn : 0 ≤ ((pW : ℝ) * Real.log 2) / Real.pi :=
    div_nonneg (mul_nonneg hpW_nn hlog_pos.le) hpi_pos.le
  unfold alphaEll alphaFromPWork
  change Real.sqrt Real.pi * (2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi)) =
    Real.sqrt (4 * (pW : ℝ) * Real.log 2)
  have hlhs_nn : 0 ≤ Real.sqrt Real.pi * (2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi)) := by
    positivity
  rw [← Real.sqrt_sq hlhs_nn]
  congr 1
  calc (Real.sqrt Real.pi * (2 * Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi))) ^ 2
      = 4 * (Real.sqrt Real.pi) ^ 2 * (Real.sqrt (((pW : ℝ) * Real.log 2) / Real.pi)) ^ 2 := by ring
    _ = 4 * Real.pi * (((pW : ℝ) * Real.log 2) / Real.pi) := by
        rw [Real.sq_sqrt hpi_pos.le, Real.sq_sqrt hrad_nn]
    _ = 4 * (pW : ℝ) * Real.log 2 := by
        field_simp [hpi_pos.ne']

/-- Computable rational approximation to $\hat{g}_{\alpha_\ell}(y)$ before fixed-point quantization,
hoisting `(log2Val, cRat, sqrtPiVal)` per level `(K, p)` and using $O(p_{\text{child},\ell})$ Taylor
terms via `cBound = Nat.sqrt (3 * pW) + 1` and `B_erf = 2 * cBound` (Theorem 4.2 (`thm:poisson`),
Theorem 5.1 (`thm:deconv`), Lemma 3.2 (`lem:elementary`), and Section 8 (`sec:lean`)). -/
def computeGHatRat (K p : ℕ) : ℚ → ℚ :=
  let q : ℕ := qChildEll K p
  let pW : ℕ := pWorkEll K p
  let S : ℕ := q + 2 * pW + 20
  let log2Val : ℚ := max (1 / 2) (approxLogTwoRat (2 * S))
  let cBound : ℕ := Nat.sqrt (3 * pW) + 1
  let cRat : ℚ := min (cBound : ℚ) (approxSqrtRat S (4 * (pW : ℚ) * log2Val))
  let B_erf : ℕ := 2 * cBound
  let N_erf : ℕ := 4 * B_erf ^ 2 + (S + B_erf) + 1
  let sqrtPiVal : ℚ := max 1 (approxSqrtRat S (approxPiRat (2 * S)))
  fun yRat =>
    let z1 : ℚ := cRat * (1 / 2 - yRat)
    let z2 : ℚ := cRat * (1 / 2 + yRat)
    let I1Rat : ℚ := erfIntegralTaylorRat N_erf z1
    let I2Rat : ℚ := erfIntegralTaylorRat N_erf z2
    (I1Rat + I2Rat) / sqrtPiVal

/-- Computable dynamic-precision rational generator for the quantized mantissa of
$\hat{g}_{\alpha_\ell}(y)$ for $y \in [0, 1]$, hoisting the level constants of `computeGHatRat K p`
(Theorem 4.2 (`thm:poisson`), Theorem 5.1 (`thm:deconv`), Lemma 3.2 (`lem:elementary`), and
Section 8 (`sec:lean`)). -/
def computeGHatMantissa (K p : ℕ) : ℚ → ℤ :=
  let q : ℕ := qChildEll K p
  let gHatRat : ℚ → ℚ := computeGHatRat K p
  fun yRat =>
    max 0 (quantizeRatMantissa q (gHatRat yRat))

/-- Non-negativity of `computeGHatMantissa K p yRat`. -/
theorem computeGHatMantissa_nonneg (K p : ℕ) (yRat : ℚ) :
    0 ≤ computeGHatMantissa K p yRat := by
  unfold computeGHatMantissa
  exact le_max_left 0 _

theorem abs_computeGHatRat_sub_gHat_le (K p : ℕ) {yRat : ℚ}
    (hy0 : 0 ≤ yRat) (hy1 : yRat ≤ 1) :
    |(computeGHatRat K p yRat : ℝ) - gHat (alphaEll K p) (yRat : ℝ)| ≤
      (1 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) := by
  unfold computeGHatRat
  dsimp only
  set q : ℕ := qChildEll K p
  set pW : ℕ := pWorkEll K p
  set S : ℕ := q + 2 * pW + 20
  generalize hl2Raw : approxLogTwoRat (2 * S) = l2Raw
  set log2Val : ℚ := max (1 / 2) l2Raw
  set cBound : ℕ := Nat.sqrt (3 * pW) + 1
  generalize hcRaw : approxSqrtRat S (4 * (pW : ℚ) * log2Val) = cRaw
  set cRat : ℚ := min (cBound : ℚ) cRaw
  set z1 : ℚ := cRat * (1 / 2 - yRat)
  set z2 : ℚ := cRat * (1 / 2 + yRat)
  set B_erf : ℕ := 2 * cBound
  set N_erf : ℕ := 4 * B_erf ^ 2 + (S + B_erf) + 1
  generalize hI1Rat : erfIntegralTaylorRat N_erf z1 = I1Rat
  generalize hI2Rat : erfIntegralTaylorRat N_erf z2 = I2Rat
  generalize hpi2S : approxPiRat (2 * S) = pi2S
  generalize hsqrtPiRaw : approxSqrtRat S pi2S = sqrtPiRaw
  set sqrtPiVal : ℚ := max 1 sqrtPiRaw
  set gHatRat : ℚ := (I1Rat + I2Rat) / sqrtPiVal
  set y : ℝ := (yRat : ℝ)
  set cTrue : ℝ := Real.sqrt (4 * (pW : ℝ) * Real.log 2)
  set I1True : ℝ := ∫ t : ℝ in (0 : ℝ)..(cTrue * (1 / 2 - y)), Real.exp (-(t ^ 2))
  set I2True : ℝ := ∫ t : ℝ in (0 : ℝ)..(cTrue * (1 / 2 + y)), Real.exp (-(t ^ 2))
  have hy0_r : 0 ≤ y := Rat.cast_nonneg.mpr hy0
  have hy1_r : y ≤ 1 := by dsimp [y]; exact_mod_cast hy1
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have halpha_nn : 0 ≤ alphaEll K p := by unfold alphaEll alphaFromPWork; positivity
  have hgHat_nn : 0 ≤ gHat (alphaEll K p) y := gHat_nonneg (alphaEll K p) halpha_nn y
  have hgHat_le1 : gHat (alphaEll K p) y ≤ 1 := gHat_le_one (alphaEll K p) y
  have hgHat_eq : gHat (alphaEll K p) y = (I1True + I2True) / Real.sqrt Real.pi := by
    unfold gHat erf
    rw [sqrt_pi_mul_alphaEll_eq]
    have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    dsimp [I1True, I2True, cTrue, pW, y]
    field_simp [hsqrt_ne]
  have hlog2_true_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_ge : (1 / 2 : ℝ) ≤ (log2Val : ℝ) := by
    dsimp [log2Val]; push_cast; exact le_max_left _ _
  have hlog2_ge_q : (1 / 2 : ℚ) ≤ log2Val := le_max_left _ _
  have hlog2_err : |(log2Val : ℝ) - Real.log 2| ≤ (2 : ℝ) ^ (-((2 * S : ℕ) : ℤ)) := by
    have h1 : (log2Val : ℝ) = max (1 / 2 : ℝ) (l2Raw : ℝ) := by
      dsimp [log2Val]; push_cast; rfl
    rw [h1]
    have htaylor : |(l2Raw : ℝ) - Real.log 2| ≤ (2 : ℝ) ^ (-((2 * S : ℕ) : ℤ)) := by
      rw [← hl2Raw]; exact abs_approxLogTwoRat_sub_log_two_le (2 * S)
    exact (abs_max_sub_le_of_le hlog2_true_ge).trans htaylor
  have hpW_ge1 : (1 : ℝ) ≤ (pW : ℝ) := by
    have : 1 ≤ pW := by dsimp [pW]; unfold pWorkEll; omega
    exact_mod_cast this
  have hpW_sq : (pW : ℝ) ≤ (pW : ℝ) ^ 2 := le_self_pow₀ hpW_ge1 (by omega : 2 ≠ 0)
  have hrad_diff : |4 * (pW : ℝ) * (log2Val : ℝ) - 4 * (pW : ℝ) * Real.log 2| ≤
      (2 * (pW : ℝ) * (2 : ℝ) ^ (-(S : ℤ))) ^ 2 := by
    have hsub : 4 * (pW : ℝ) * (log2Val : ℝ) - 4 * (pW : ℝ) * Real.log 2 =
        4 * (pW : ℝ) * ((log2Val : ℝ) - Real.log 2) := by ring
    have h2S_sq : (2 : ℝ) ^ (-((2 * S : ℕ) : ℤ)) = ((2 : ℝ) ^ (-(S : ℤ))) ^ 2 := by
      have hexp : -((2 * S : ℕ) : ℤ) = -(S : ℤ) + -(S : ℤ) := by omega
      rw [hexp, zpow_add₀ (by norm_num), sq]
    rw [hsub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (pW : ℝ))]
    calc 4 * (pW : ℝ) * |(log2Val : ℝ) - Real.log 2|
        ≤ (4 * (pW : ℝ) ^ 2) * ((2 : ℝ) ^ (-(S : ℤ))) ^ 2 := by
          rw [← h2S_sq]
          exact mul_le_mul (by linarith) hlog2_err (abs_nonneg _) (by positivity)
      _ = (2 * (pW : ℝ) * (2 : ℝ) ^ (-(S : ℤ))) ^ 2 := by ring
  have hrad_true_nn : 0 ≤ 4 * (pW : ℝ) * Real.log 2 :=
    mul_nonneg (by positivity) (by linarith)
  have hsqrt_rad_diff :
      |Real.sqrt (4 * (pW : ℝ) * (log2Val : ℝ)) - cTrue| ≤
        2 * (pW : ℝ) * (2 : ℝ) ^ (-(S : ℤ)) :=
    abs_sqrt_sub_sqrt_le (by positivity) hrad_true_nn (by positivity) hrad_diff
  have hcTrue_le : cTrue ≤ (cBound : ℝ) := by
    dsimp [cTrue]
    have hlog_lt : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
    have hcb_nat : 3 * pW ≤ cBound ^ 2 := le_of_lt (Nat.lt_succ_sqrt' (3 * pW))
    have hcb_r : 3 * (pW : ℝ) ≤ (cBound : ℝ) ^ 2 := by exact_mod_cast hcb_nat
    have hle : 4 * (pW : ℝ) * Real.log 2 ≤ (cBound : ℝ) ^ 2 := by
      calc 4 * (pW : ℝ) * Real.log 2
          ≤ 4 * (pW : ℝ) * (3 / 4) := mul_le_mul_of_nonneg_left hlog_lt (by positivity)
        _ = 3 * (pW : ℝ) := by ring
        _ ≤ (cBound : ℝ) ^ 2 := hcb_r
    rw [← Real.sqrt_sq (Nat.cast_nonneg cBound)]
    exact Real.sqrt_le_sqrt hle
  have hcRat_nn : 0 ≤ (cRat : ℝ) := by
    dsimp [cRat]; push_cast
    exact le_min (by positivity) (by rw [← hcRaw]; exact_mod_cast approxSqrtRat_nonneg S _)
  have hcRat_le : (cRat : ℝ) ≤ (cBound : ℝ) := by
    dsimp [cRat]; push_cast; exact min_le_left _ _
  have hcRat_err : |(cRat : ℝ) - cTrue| ≤ (2 * (pW : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have h1 : (cRat : ℝ) = min (cBound : ℝ) (cRaw : ℝ) := by
      dsimp [cRat]; push_cast; rfl
    rw [h1]
    refine (abs_min_sub_le_of_le hcTrue_le).trans ?_
    have happrox : |(cRaw : ℝ) - Real.sqrt (4 * (pW : ℝ) * (log2Val : ℝ))| ≤
        (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← hcRaw]
      have hraw := abs_approxSqrtRat_sub_sqrt_le S (Y := 4 * (pW : ℚ) * log2Val) (by positivity)
      have hcast : ((4 * (pW : ℚ) * log2Val : ℚ) : ℝ) = 4 * (pW : ℝ) * (log2Val : ℝ) := by
        push_cast; rfl
      rwa [hcast] at hraw
    have htri := abs_sub_le (cRaw : ℝ) (Real.sqrt (4 * (pW : ℝ) * (log2Val : ℝ))) cTrue
    linarith
  have hy_sub_abs : |1 / 2 - y| ≤ (3 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hy_add_abs : |1 / 2 + y| ≤ (3 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz1_abs : |(z1 : ℝ)| ≤ (B_erf : ℝ) := by
    have hz1_cast : (z1 : ℝ) = (cRat : ℝ) * (1 / 2 - y) := by dsimp [z1, y]; push_cast; rfl
    rw [hz1_cast, abs_mul, abs_of_nonneg hcRat_nn]
    calc (cRat : ℝ) * |1 / 2 - y|
        ≤ (cBound : ℝ) * 2 :=
          mul_le_mul hcRat_le (by linarith) (abs_nonneg _) (by positivity)
      _ = (B_erf : ℝ) := by dsimp [B_erf]; push_cast; ring
  have hz2_abs : |(z2 : ℝ)| ≤ (B_erf : ℝ) := by
    have hz2_cast : (z2 : ℝ) = (cRat : ℝ) * (1 / 2 + y) := by dsimp [z2, y]; push_cast; rfl
    rw [hz2_cast, abs_mul, abs_of_nonneg hcRat_nn]
    calc (cRat : ℝ) * |1 / 2 + y|
        ≤ (cBound : ℝ) * 2 :=
          mul_le_mul hcRat_le (by linarith) (abs_nonneg _) (by positivity)
      _ = (B_erf : ℝ) := by dsimp [B_erf]; push_cast; ring
  have hz1_diff : |(z1 : ℝ) - cTrue * (1 / 2 - y)| ≤
      (3 * (pW : ℝ) + 2) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hsub : (z1 : ℝ) - cTrue * (1 / 2 - y) = ((cRat : ℝ) - cTrue) * (1 / 2 - y) := by
      dsimp [z1, y]; push_cast; ring
    rw [hsub, abs_mul]
    calc |(cRat : ℝ) - cTrue| * |1 / 2 - y|
        ≤ ((2 * (pW : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ))) * (3 / 2 : ℝ) :=
          mul_le_mul hcRat_err hy_sub_abs (abs_nonneg _) (by positivity)
      _ = (3 * (pW : ℝ) + 3 / 2) * (2 : ℝ) ^ (-(S : ℤ)) := by ring
      _ ≤ (3 * (pW : ℝ) + 2) * (2 : ℝ) ^ (-(S : ℤ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hz2_diff : |(z2 : ℝ) - cTrue * (1 / 2 + y)| ≤
      (3 * (pW : ℝ) + 2) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hsub : (z2 : ℝ) - cTrue * (1 / 2 + y) = ((cRat : ℝ) - cTrue) * (1 / 2 + y) := by
      dsimp [z2, y]; push_cast; ring
    rw [hsub, abs_mul]
    calc |(cRat : ℝ) - cTrue| * |1 / 2 + y|
        ≤ ((2 * (pW : ℝ) + 1) * (2 : ℝ) ^ (-(S : ℤ))) * (3 / 2 : ℝ) :=
          mul_le_mul hcRat_err hy_add_abs (abs_nonneg _) (by positivity)
      _ = (3 * (pW : ℝ) + 3 / 2) * (2 : ℝ) ^ (-(S : ℤ)) := by ring
      _ ≤ (3 * (pW : ℝ) + 2) * (2 : ℝ) ^ (-(S : ℤ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hI1_err : |(I1Rat : ℝ) - I1True| ≤ (3 * (pW : ℝ) + 3) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have htaylor : |(I1Rat : ℝ) - ∫ t : ℝ in (0 : ℝ)..(z1 : ℝ), Real.exp (-(t ^ 2))| ≤
        (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← hI1Rat]; exact abs_erfIntegralTaylorRat_sub_integral_le B_erf S hz1_abs
    have hlip := (abs_erf_integral_sub_le (z1 : ℝ) (cTrue * (1 / 2 - y))).trans hz1_diff
    have htri := abs_sub_le (I1Rat : ℝ)
      (∫ t : ℝ in (0 : ℝ)..(z1 : ℝ), Real.exp (-(t ^ 2))) I1True
    linarith
  have hI2_err : |(I2Rat : ℝ) - I2True| ≤ (3 * (pW : ℝ) + 3) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have htaylor : |(I2Rat : ℝ) - ∫ t : ℝ in (0 : ℝ)..(z2 : ℝ), Real.exp (-(t ^ 2))| ≤
        (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← hI2Rat]; exact abs_erfIntegralTaylorRat_sub_integral_le B_erf S hz2_abs
    have hlip := (abs_erf_integral_sub_le (z2 : ℝ) (cTrue * (1 / 2 + y))).trans hz2_diff
    have htri := abs_sub_le (I2Rat : ℝ)
      (∫ t : ℝ in (0 : ℝ)..(z2 : ℝ), Real.exp (-(t ^ 2))) I2True
    linarith
  have hsqrtPi_true_ge1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hsqrtPi_ge1 : (1 : ℝ) ≤ (sqrtPiVal : ℝ) := by
    dsimp [sqrtPiVal]; push_cast; exact le_max_left _ _
  have hsqrtPi_err : |(sqrtPiVal : ℝ) - Real.sqrt Real.pi| ≤ 2 * (2 : ℝ) ^ (-(S : ℤ)) := by
    have h1 : (sqrtPiVal : ℝ) = max (1 : ℝ) (sqrtPiRaw : ℝ) := by
      dsimp [sqrtPiVal]; push_cast; rfl
    rw [h1]
    refine (abs_max_sub_le_of_le hsqrtPi_true_ge1).trans ?_
    have hpi2S_nn : 0 ≤ pi2S := by rw [← hpi2S]; exact_mod_cast approxPiRat_nonneg (2 * S)
    have hpi_approx : |(sqrtPiRaw : ℝ) - Real.sqrt (pi2S : ℝ)| ≤ (2 : ℝ) ^ (-(S : ℤ)) := by
      rw [← hsqrtPiRaw]; exact abs_approxSqrtRat_sub_sqrt_le S hpi2S_nn
    have hpi_diff : |(pi2S : ℝ) - Real.pi| ≤ ((2 : ℝ) ^ (-(S : ℤ))) ^ 2 := by
      have h2S_sq : (2 : ℝ) ^ (-((2 * S : ℕ) : ℤ)) = ((2 : ℝ) ^ (-(S : ℤ))) ^ 2 := by
        have hexp : -((2 * S : ℕ) : ℤ) = -(S : ℤ) + -(S : ℤ) := by omega
        rw [hexp, zpow_add₀ (by norm_num), sq]
      rw [← h2S_sq, ← hpi2S]
      exact abs_approxPiRat_sub_pi_le (2 * S)
    have hsqrt_diff := abs_sqrt_sub_sqrt_le
      (Rat.cast_nonneg.mpr hpi2S_nn) Real.pi_pos.le (by positivity) hpi_diff
    have htri := abs_sub_le (sqrtPiRaw : ℝ) (Real.sqrt (pi2S : ℝ)) (Real.sqrt Real.pi)
    linarith
  have hI_sum_abs : |I1True + I2True| ≤ 2 := by
    have heq : I1True + I2True = Real.sqrt Real.pi * gHat (alphaEll K p) y := by
      rw [hgHat_eq, mul_div_cancel₀ _ (Real.sqrt_pos.mpr Real.pi_pos).ne']
    have hsqrt_le2 : Real.sqrt Real.pi ≤ 2 := by
      have : Real.pi ≤ 2 ^ 2 := by linarith [Real.pi_lt_d4]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt this
    rw [heq, abs_mul, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos), abs_of_nonneg hgHat_nn]
    calc Real.sqrt Real.pi * gHat (alphaEll K p) y
        ≤ 2 * 1 := mul_le_mul hsqrt_le2 hgHat_le1 hgHat_nn (by norm_num)
      _ = 2 := mul_one 2
  have hgHatRat_err : |(gHatRat : ℝ) - gHat (alphaEll K p) y| ≤
      (6 * (pW : ℝ) + 10) * (2 : ℝ) ^ (-(S : ℤ)) := by
    have hgRat_cast : (gHatRat : ℝ) = ((I1Rat : ℝ) + (I2Rat : ℝ)) / (sqrtPiVal : ℝ) := by
      dsimp [gHatRat]; push_cast; rfl
    rw [hgRat_cast, hgHat_eq]
    refine (abs_div_sub_div_le_of_one_le hsqrtPi_ge1 hsqrtPi_true_ge1).trans ?_
    have hnum : |((I1Rat : ℝ) + (I2Rat : ℝ)) - (I1True + I2True)| ≤
        (6 * (pW : ℝ) + 6) * (2 : ℝ) ^ (-(S : ℤ)) := by
      have hsub : ((I1Rat : ℝ) + (I2Rat : ℝ)) - (I1True + I2True) =
          ((I1Rat : ℝ) - I1True) + ((I2Rat : ℝ) - I2True) := by ring
      rw [hsub]
      refine (abs_add_le _ _).trans ?_
      linarith
    have hden_mul : |I1True + I2True| * |(sqrtPiVal : ℝ) - Real.sqrt Real.pi| ≤
        2 * (2 * (2 : ℝ) ^ (-(S : ℤ))) :=
      mul_le_mul hI_sum_abs hsqrtPi_err (abs_nonneg _) (by norm_num)
    linarith
  have hpW_pow : 6 * (pW : ℝ) + 10 ≤ 10 * (2 : ℝ) ^ (2 * pW) := by
    have h1 : (pW : ℝ) + 1 ≤ (2 : ℝ) ^ pW := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := pW))
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ pW := by
      exact_mod_cast (Nat.one_le_two_pow (n := pW))
    have hsq : ((2 : ℝ) ^ pW) ^ 2 = (2 : ℝ) ^ (2 * pW) := by
      rw [← pow_mul, mul_comm]
    have hpow_le : (2 : ℝ) ^ pW ≤ (2 : ℝ) ^ (2 * pW) := by
      rw [← hsq]
      exact le_self_pow₀ h2 (by omega : 2 ≠ 0)
    linarith
  have h2S : (2 : ℝ) ^ (-(S : ℤ)) =
      (2 : ℝ) ^ (-((2 * pW : ℕ) : ℤ)) * (1 / 1048576 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    have hexp : -(S : ℤ) = -((2 * pW : ℕ) : ℤ) + (-20 : ℤ) + -(q : ℤ) := by
      dsimp [S]; omega
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    norm_num
  have h1 := hgHatRat_err.trans (mul_le_mul_of_nonneg_right hpW_pow (by positivity))
  rw [h2S] at h1
  have hcancel : (2 : ℝ) ^ (2 * pW) * (2 : ℝ) ^ (-((2 * pW : ℕ) : ℤ)) = 1 :=
    two_pow_mul_two_zpow_neg (2 * pW)
  have hrhs :
      10 * (2 : ℝ) ^ (2 * pW) *
        ((2 : ℝ) ^ (-((2 * pW : ℕ) : ℤ)) * (1 / 1048576 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) =
      (10 / 1048576 : ℝ) * ((2 : ℝ) ^ (2 * pW) * (2 : ℝ) ^ (-((2 * pW : ℕ) : ℤ))) *
        (2 : ℝ) ^ (-(q : ℤ)) := by ring
  rw [hrhs, hcancel, mul_one] at h1
  linarith

/-- Accuracy bound for `computeGHatMantissa`: for any `yRat ∈ [0, 1]`,
`computeGHatMantissa K p yRat` approximates `gHat (alphaEll K p) (yRat : ℝ)` within
$\frac{11}{20} 2^{-q_{\text{child},\ell}}$ (Lemma 3.2 (`lem:elementary`) and
equation (7) (`eq:faithful-table`)). -/
theorem abs_computeGHatMantissa_sub_gHat_le (K p : ℕ) {yRat : ℚ}
    (hy0 : 0 ≤ yRat) (hy1 : yRat ≤ 1) :
    |((computeGHatMantissa K p yRat : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
      gHat (alphaEll K p) (yRat : ℝ)| ≤
      (11 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) := by
  unfold computeGHatMantissa
  rw [cast_max_zero_quantizeRatMantissa_mul_zpow]
  have halpha_nn : 0 ≤ alphaEll K p := by unfold alphaEll alphaFromPWork; positivity
  have hgHat_nn : 0 ≤ gHat (alphaEll K p) (yRat : ℝ) := gHat_nonneg (alphaEll K p) halpha_nn _
  refine (abs_max_sub_le_of_le hgHat_nn).trans ?_
  have hq_err := abs_quantizeReal_sub_self_le (qChildEll K p) (computeGHatRat K p yRat : ℝ)
  have hrat_err := abs_computeGHatRat_sub_gHat_le K p hy0 hy1
  have htri := abs_sub_le (quantizeReal (qChildEll K p) (computeGHatRat K p yRat : ℝ))
    (computeGHatRat K p yRat : ℝ) (gHat (alphaEll K p) (yRat : ℝ))
  linarith

/-- Computable dynamic-precision rational passband constant $c_0$ mantissa generator,
hoisting `computeGHatMantissa K p` (Theorem 5.1 (`thm:deconv`), equation (19) (`eq:c0-c1`),
and Lemma 3.2 (`lem:elementary`)). -/
def computePassbandC0Mantissa (K p : ℕ) : Fin (rEll K) → ℤ :=
  let gHatM : ℚ → ℤ := computeGHatMantissa K p
  let rQ : ℚ := (rEll K : ℚ)
  fun u2 => gHatM ((u2.val : ℚ) / rQ)

/-- Computable dynamic-precision rational passband constant $c_1$ mantissa generator,
hoisting `computeGHatMantissa K p` (Theorem 5.1 (`thm:deconv`), equation (19) (`eq:c0-c1`),
and Lemma 3.2 (`lem:elementary`)). -/
def computePassbandC1Mantissa (K p : ℕ) : Fin (rEll K) → ℤ :=
  let gHatM : ℚ → ℤ := computeGHatMantissa K p
  let rQ : ℚ := (rEll K : ℚ)
  fun u2 => gHatM (1 - (u2.val : ℚ) / rQ)

theorem computePassbandC0Mantissa_nonneg (K p : ℕ) (u2 : Fin (rEll K)) :
    0 ≤ computePassbandC0Mantissa K p u2 :=
  computeGHatMantissa_nonneg K p _

theorem computePassbandC1Mantissa_nonneg (K p : ℕ) (u2 : Fin (rEll K)) :
    0 ≤ computePassbandC1Mantissa K p u2 :=
  computeGHatMantissa_nonneg K p _

theorem abs_computePassbandC0Mantissa_sub_passbandC0_le (K p : ℕ) (u2 : Fin (rEll K)) :
    |((computePassbandC0Mantissa K p u2 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
      passbandC0 K p u2| ≤
      (11 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) := by
  unfold computePassbandC0Mantissa passbandC0
  have hr : (0 : ℚ) < (rEll K : ℚ) := Nat.cast_pos.mpr (rEll_pos K)
  have hy0 : 0 ≤ (u2.val : ℚ) / (rEll K : ℚ) := div_nonneg (Nat.cast_nonneg _) hr.le
  have hy1 : (u2.val : ℚ) / (rEll K : ℚ) ≤ 1 :=
    (div_lt_one hr).mpr (Nat.cast_lt.mpr u2.isLt) |>.le
  simpa using abs_computeGHatMantissa_sub_gHat_le K p hy0 hy1

theorem abs_computePassbandC1Mantissa_sub_passbandC1_le (K p : ℕ) (u2 : Fin (rEll K)) :
    |((computePassbandC1Mantissa K p u2 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
      passbandC1 K p u2| ≤
      (11 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)) := by
  unfold computePassbandC1Mantissa passbandC1
  have hr : (0 : ℚ) < (rEll K : ℚ) := Nat.cast_pos.mpr (rEll_pos K)
  have hfrac0 : 0 ≤ (u2.val : ℚ) / (rEll K : ℚ) := div_nonneg (Nat.cast_nonneg _) hr.le
  have hfrac1 : (u2.val : ℚ) / (rEll K : ℚ) ≤ 1 :=
    (div_lt_one hr).mpr (Nat.cast_lt.mpr u2.isLt) |>.le
  have hy0 : 0 ≤ 1 - (u2.val : ℚ) / (rEll K : ℚ) := by linarith
  have hy1 : 1 - (u2.val : ℚ) / (rEll K : ℚ) ≤ 1 := by linarith
  simpa using abs_computeGHatMantissa_sub_gHat_le K p hy0 hy1

theorem abs_computeFilterTapFixed_mul_zpow_le_one (K p : ℕ) (j1 : Fin (t1Ell K)) (d : ℤ) :
    |((computeFilterTapFixed K p j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))| ≤ 1 := by
  unfold computeFilterTapFixed
  split_ifs with hd
  · rw [cast_quantizeRatMantissa_mul_zpow]
    exact abs_quantizeReal_le_one_of_abs_le_one (qChildEll K p)
      (abs_computeFilterTapRat_le_one K p j1 d)
  · simp

/-- Tabulates a 2D filter tap table `f : Fin t1 → ℤ → ℤ` supported on `|d| ≤ m1` into a
2D contiguous `Array (Array ℤ)` of dimension `t1 × (2 * m1 + 1)`. -/
def memoizeFilterTap {t1 : ℕ} (m1 : ℕ) (f : Fin t1 → ℤ → ℤ) : Fin t1 → ℤ → ℤ :=
  let rows : Array (Array ℤ) :=
    Array.ofFn (fun j1 : Fin t1 =>
      Array.ofFn (fun k : Fin (2 * m1 + 1) => f j1 ((k.val : ℤ) - (m1 : ℤ))))
  fun j1 d =>
    if |d| ≤ (m1 : ℤ) then
      let idx : ℕ := (d + (m1 : ℤ)).toNat
      (rows.getD j1.val #[]).getD idx 0
    else 0

theorem memoizeFilterTap_eq_of_support {t1 : ℕ} (m1 : ℕ) (f : Fin t1 → ℤ → ℤ)
    (hsupp : ∀ j1 d, ¬ (|d| ≤ (m1 : ℤ)) → f j1 d = 0) :
    memoizeFilterTap m1 f = f := by
  funext j1 d
  unfold memoizeFilterTap
  dsimp only
  split_ifs with hd
  · have hd_bounds := abs_le.mp hd
    have hidx_nonneg : 0 ≤ d + (m1 : ℤ) := by omega
    have hidx_lt : (d + (m1 : ℤ)).toNat < 2 * m1 + 1 := by omega
    simp [Array.getD, Array.size_ofFn, j1.isLt, hidx_lt]
    rw [max_eq_left hidx_nonneg, add_sub_cancel_right]
  · exact (hsupp j1 d hd).symm

@[simp]
theorem memoizeFilterTap_computeFilterTapFixed (K p : ℕ) :
    memoizeFilterTap (computeM1Ell K p) (computeFilterTapFixed K p) =
      computeFilterTapFixed K p := by
  apply memoizeFilterTap_eq_of_support
  intro j1 d hd
  unfold computeFilterTapFixed
  exact if_neg hd

/-- Canonical precomputed integer schedule tree populated from the paper's quantized
filter taps, twist roots, passband weights, and 1D leaf twiddle table. -/
noncomputable def canonicalScheduleIntTree (K p B_in : ℕ) : ScheduleIntTree K p B_in :=
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    ScheduleIntTree.node K p B_in (m1Ell K p)
      (levelFilterTapFixed K p)
      (fun k2 => quantizeComplexFixed (qChildEll K p) (zetaPow (rEll K) (k2.val : ℤ)))
      (fun k2 => quantizeComplexFixed (qChildEll K p) (zetaPow (rEll K) (-(k2.val : ℤ))))
      (fun u2 => quantizeRealMantissa (qChildEll K p) (passbandC0 K p u2))
      (fun u2 => quantizeRealMantissa (qChildEll K p) (passbandC1 K p u2))
      (canonicalScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
  else
    ScheduleIntTree.leaf K p B_in (canonicalLeafRoots K p)
termination_by K
decreasing_by
  unfold k2Ell
  omega

/-- **Inductive Accuracy Specification for `ScheduleIntTree` (`ValidScheduleIntTree`)**:
Certifies that every node and leaf of a `ScheduleIntTree K p B_in` satisfies the paper's
window half-width bounds (`m1Ell K p ≤ m1 ≤ pChildEll K p`, Lemma 6.5 (`lem:forward`)),
filter-tap width and approximation bounds ($\le \frac{51}{100} 2^{-q_{\text{child}}}$),
pre/post twist root approximation bounds ($\le \frac{18}{25} 2^{-q_{\text{child}}}$),
passband constant approximation bounds ($\le \frac{11}{20} 2^{-q_{\text{child}}}$), and
1D leaf twiddle approximation bounds ($\le \frac{18}{25} 2^{-q_{\text{base}}}$).
Inhabited unconditionally by **both** `computeScheduleIntTree` (`validScheduleIntTree_computeScheduleIntTree`)
and `canonicalScheduleIntTree` (`validScheduleIntTree_canonicalScheduleIntTree`). -/
inductive ValidScheduleIntTree : {K p B_in : ℕ} → ScheduleIntTree K p B_in → Prop
  | leaf (K p B_in : ℕ) (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
      (hcond : ¬ ((!isBaseLeaf K p) = true ∧ 2 ≤ K))
      (hroots : ∀ u : Fin (2 ^ K),
        ‖(leafTwiddles u).toComplex - expTwoPiI ((u.val : ℝ) / ((2 ^ K : ℕ) : ℝ))‖ ≤
          (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qBaseEll K p : ℤ))) :
      ValidScheduleIntTree (.leaf K p B_in leafTwiddles)
  | node (K p B_in m1 : ℕ)
      (filterTap : Fin (t1Ell K) → ℤ → ℤ)
      (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
      (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
      (child : ScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
      (hcond : (!isBaseLeaf K p) = true ∧ 2 ≤ K)
      (hm1_ge : m1Ell K p ≤ m1)
      (hm1_le : m1 ≤ pChildEll K p)
      (htap_fits : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
        FitsSignedWord (qChildEll K p + 1) (filterTap j1 d))
      (htap_abs : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
        |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))| ≤ 1)
      (htap_err : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
        |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
          IntMul.filterTap (alphaEll K p) m1 (t1Ell K) j1 d| ≤
          (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
      (hpre_err : ∀ k2 : Fin (rEll K),
        ‖(preTwistRoot k2).toComplex - zetaPow (rEll K) (k2.val : ℤ)‖ ≤
          (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
      (hpost_err : ∀ k2 : Fin (rEll K),
        ‖(postTwistRoot k2).toComplex - zetaPow (rEll K) (-(k2.val : ℤ))‖ ≤
          (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
      (hc0_nn : ∀ u2 : Fin (rEll K), 0 ≤ c0Mantissa u2)
      (hc1_nn : ∀ u2 : Fin (rEll K), 0 ≤ c1Mantissa u2)
      (hc0_err : ∀ u2 : Fin (rEll K),
        |((c0Mantissa u2 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) - passbandC0 K p u2| ≤
          (11 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
      (hc1_err : ∀ u2 : Fin (rEll K),
        |((c1Mantissa u2 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) - passbandC1 K p u2| ≤
          (11 / 20 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
      (hchild : ValidScheduleIntTree child) :
      ValidScheduleIntTree (.node K p B_in m1 filterTap preTwistRoot postTwistRoot
        c0Mantissa c1Mantissa child)

/-- **Unconditional Validity of `canonicalScheduleIntTree`
(`validScheduleIntTree_canonicalScheduleIntTree`)**. -/
theorem validScheduleIntTree_canonicalScheduleIntTree (K : ℕ) :
    ∀ p B_in : ℕ, ValidScheduleIntTree (canonicalScheduleIntTree K p B_in) := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [canonicalScheduleIntTree]
    have hsqrt_le : Real.sqrt 2 / 2 ≤ 18 / 25 := by linarith [sqrt_two_le]
    split_ifs with hcond
    · have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(qChildEll K p : ℤ)) := zpow_pos (by norm_num) _
      exact ValidScheduleIntTree.node K p B_in (m1Ell K p)
        (levelFilterTapFixed K p)
        (fun k2 => quantizeComplexFixed (qChildEll K p) (zetaPow (rEll K) (k2.val : ℤ)))
        (fun k2 => quantizeComplexFixed (qChildEll K p) (zetaPow (rEll K) (-(k2.val : ℤ))))
        (fun u2 => quantizeRealMantissa (qChildEll K p) (passbandC0 K p u2))
        (fun u2 => quantizeRealMantissa (qChildEll K p) (passbandC1 K p u2))
        (canonicalScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
        hcond
        (le_refl _)
        (m1Ell_le_pChildEll K p)
        (fitsSignedWord_levelFilterTapFixed K p)
        (fun j1 d => by
          change |quantizeReal (qChildEll K p) (filterTap (alphaEll K p) (m1Ell K p) (t1Ell K) j1 d)| ≤ 1
          exact abs_quantizeReal_le_one_of_abs_le_one (qChildEll K p)
            (abs_filterTap_le_one (alphaEll K p) (m1Ell K p) (t1Ell K) j1 d))
        (fun j1 d => by
          have h := abs_quantizeReal_sub_self_le (qChildEll K p)
            (filterTap (alphaEll K p) (m1Ell K p) (t1Ell K) j1 d)
          change |quantizeReal (qChildEll K p) (filterTap (alphaEll K p) (m1Ell K p) (t1Ell K) j1 d) -
            filterTap (alphaEll K p) (m1Ell K p) (t1Ell K) j1 d| ≤ _
          linarith)
        (fun k2 => by
          have h := norm_quantizeComplex_sub_self_le (qChildEll K p) (zetaPow (rEll K) (k2.val : ℤ))
          exact h.trans (mul_le_mul_of_nonneg_right hsqrt_le h2q_pos.le))
        (fun k2 => by
          have h := norm_quantizeComplex_sub_self_le (qChildEll K p) (zetaPow (rEll K) (-(k2.val : ℤ)))
          exact h.trans (mul_le_mul_of_nonneg_right hsqrt_le h2q_pos.le))
        (fun u2 => by
          have hmin := passbandC0_passbandC1_min_nonneg K p u2
          have hc0 : 0 ≤ passbandC0 K p u2 := hmin.trans (min_le_left _ _)
          unfold quantizeRealMantissa
          exact Int.floor_nonneg.mpr (by positivity))
        (fun u2 => by
          have hmin := passbandC0_passbandC1_min_nonneg K p u2
          have hc1 : 0 ≤ passbandC1 K p u2 := hmin.trans (min_le_right _ _)
          unfold quantizeRealMantissa
          exact Int.floor_nonneg.mpr (by positivity))
        (fun u2 => by
          have h := abs_quantizeReal_sub_self_le (qChildEll K p) (passbandC0 K p u2)
          change |quantizeReal (qChildEll K p) (passbandC0 K p u2) - passbandC0 K p u2| ≤ _
          linarith)
        (fun u2 => by
          have h := abs_quantizeReal_sub_self_le (qChildEll K p) (passbandC1 K p u2)
          change |quantizeReal (qChildEll K p) (passbandC1 K p u2) - passbandC1 K p u2| ≤ _
          linarith)
        (ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in))
    · have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(qBaseEll K p : ℤ)) := zpow_pos (by norm_num) _
      exact ValidScheduleIntTree.leaf K p B_in (canonicalLeafRoots K p) hcond
        (fun u => by
          have h := norm_quantizeComplex_sub_self_le (qBaseEll K p)
            (expTwoPiI ((u.val : ℝ) / ((2 ^ K : ℕ) : ℝ)))
          exact h.trans (mul_le_mul_of_nonneg_right hsqrt_le h2q_pos.le))

/-- Bridge lemma: quantizing a rational quotient `(num : ℚ) / (den : ℚ)` to `q` fractional bits
equals the pure-integer rounded division `roundDivInt (num * 2^q) den` with zero `ℚ` arithmetic. -/
theorem quantizeRatMantissa_div_int_eq_roundDivInt (q : ℕ) (num den : ℤ) :
    quantizeRatMantissa q ((num : ℚ) / (den : ℚ)) =
      roundDivInt (num * (2 : ℤ) ^ q) den := by
  rw [quantizeRatMantissa_eq_quantizeRealMantissa, roundDivInt_eq_floor_div_add_half]
  unfold quantizeRealMantissa
  congr 2
  push_cast
  ring

theorem cast_max_div_two_pow (q : ℕ) (a b : ℤ) :
    ((max a b : ℤ) : ℚ) / (2 : ℚ) ^ q =
      max ((a : ℚ) / (2 : ℚ) ^ q) ((b : ℚ) / (2 : ℚ) ^ q) := by
  rcases le_total a b with h | h
  · have hq : (a : ℚ) / (2 : ℚ) ^ q ≤ (b : ℚ) / (2 : ℚ) ^ q :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
    rw [max_eq_right h, max_eq_right hq]
  · have hq : (b : ℚ) / (2 : ℚ) ^ q ≤ (a : ℚ) / (2 : ℚ) ^ q :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
    rw [max_eq_left h, max_eq_left hq]

theorem cast_min_div_two_pow (q : ℕ) (a b : ℤ) :
    ((min a b : ℤ) : ℚ) / (2 : ℚ) ^ q =
      min ((a : ℚ) / (2 : ℚ) ^ q) ((b : ℚ) / (2 : ℚ) ^ q) := by
  rcases le_total a b with h | h
  · have hq : (a : ℚ) / (2 : ℚ) ^ q ≤ (b : ℚ) / (2 : ℚ) ^ q :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
    rw [min_eq_left h, min_eq_left hq]
  · have hq : (b : ℚ) / (2 : ℚ) ^ q ≤ (a : ℚ) / (2 : ℚ) ^ q :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
    rw [min_eq_right h, min_eq_right hq]

/-- Pure-integer fixed-point square root on a dyadic mantissa `num` shifted by `2 ^ k`
with zero `ℚ` arithmetic. -/
def approxSqrtFixed (k : ℕ) (num : ℤ) : ℤ :=
  (Nat.sqrt ((max 0 num).toNat / 2 ^ k) : ℤ)

/-- Bridge lemma: pure-integer square root `approxSqrtFixed k num` divided by `2^S`
equals `approxSqrtRat S (num / 2^(2 * S + k))`. -/
theorem approxSqrtFixed_eq_approxSqrtRat (S k : ℕ) (num : ℤ) :
    (approxSqrtFixed k num : ℚ) / (2 : ℚ) ^ S =
      approxSqrtRat S ((num : ℚ) / (2 : ℚ) ^ (2 * S + k)) := by
  unfold approxSqrtFixed approxSqrtRat
  push_cast
  congr 2
  have hmax : max 0 ((num : ℚ) / (2 : ℚ) ^ (2 * S + k)) * (4 : ℚ) ^ S =
      (((max 0 num).toNat : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
    have h4 : (4 : ℚ) ^ S = (2 : ℚ) ^ (2 * S) := by rw [pow_mul]; norm_num
    have h2S : (2 : ℚ) ^ (2 * S) ≠ 0 := by positivity
    rcases le_total 0 num with hnum | hnum
    · have hnum_q : (0 : ℚ) ≤ (num : ℚ) / (2 : ℚ) ^ (2 * S + k) :=
        div_nonneg (by exact_mod_cast hnum) (by positivity)
      have htoNat : (((max 0 num).toNat : ℕ) : ℚ) = (num : ℚ) := by
        rw [max_eq_right hnum]
        exact_mod_cast Int.toNat_of_nonneg hnum
      rw [max_eq_right hnum_q, htoNat, h4, pow_add]
      push_cast
      field_simp [h2S]
    · have hnum_q : (num : ℚ) / (2 : ℚ) ^ (2 * S + k) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hnum) (by positivity)
      rw [max_eq_left hnum_q, max_eq_left hnum]
      simp
  have hfloor : ⌊(((max 0 num).toNat : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ)⌋₊ =
      (max 0 num).toNat / 2 ^ k := by
    rw [Nat.floor_eq_iff (by positivity)]
    set a : ℕ := (max 0 num).toNat
    set b : ℕ := 2 ^ k
    have hb_pos : 0 < b := by positivity
    have hb_qpos : (0 : ℚ) < (b : ℚ) := by positivity
    have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hmod : a % b < b := Nat.mod_lt a hb_pos
    have ha_q : (a : ℚ) = (b : ℚ) * ((a / b : ℕ) : ℚ) + ((a % b : ℕ) : ℚ) := by
      exact_mod_cast hdiv.symm
    have hr0 : (0 : ℚ) ≤ ((a % b : ℕ) : ℚ) := by positivity
    have hr1 : ((a % b : ℕ) : ℚ) < (b : ℚ) := by exact_mod_cast hmod
    constructor
    · rw [le_div_iff₀ hb_qpos, ha_q]; linarith
    · rw [div_lt_iff₀ hb_qpos, ha_q]; linarith
  rw [hmax, hfloor]

/-- Pure-integer fixed-point mantissa of $\ln 2$ at scale $q_{\text{acc}} = S + (S + 2)$
with zero `ℚ` arithmetic. -/
def approxLogTwoFixed (S : ℕ) : ℤ :=
  let q_acc : ℕ := S + (S + 2)
  ∑ i ∈ Finset.range (S + 2), approxLogTwoTermFixed q_acc i

theorem cast_approxLogTwoFixed_div (S : ℕ) :
    (approxLogTwoFixed S : ℚ) / (2 : ℚ) ^ (S + (S + 2)) = approxLogTwoRat S := rfl

/-- Pure-integer fixed-point mantissa of $\arctan(1/k)$ at scale $4N + 6$
with zero `ℚ` arithmetic. -/
def arctanInvTaylorFixed (N k : ℕ) : ℤ :=
  let q_acc : ℕ := 4 * N + 6
  let arr : Array ℤ := arctanInvPowArrayFixed k q_acc N
  ∑ m ∈ Finset.range (N + 1),
    altSign m * roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ)

theorem cast_arctanInvTaylorFixed_div (N k : ℕ) :
    (arctanInvTaylorFixed N k : ℚ) / (2 : ℚ) ^ (4 * N + 6) = arctanInvTaylorRat N k := rfl

/-- Pure-integer Machin-like fixed-point mantissa of $\pi = 4(\arctan(1/2) + \arctan(1/3))$
at scale $4(S + 3) + 6$ with zero `ℚ` arithmetic. -/
def approxPiFixed (S : ℕ) : ℤ :=
  4 * (arctanInvTaylorFixed (S + 3) 2 + arctanInvTaylorFixed (S + 3) 3)

theorem cast_approxPiFixed_div (S : ℕ) :
    (approxPiFixed S : ℚ) / (2 : ℚ) ^ (4 * (S + 3) + 6) = approxPiRat S := by
  unfold approxPiFixed approxPiRat
  rw [← cast_arctanInvTaylorFixed_div (S + 3) 2, ← cast_arctanInvTaylorFixed_div (S + 3) 3]
  push_cast
  ring

/-- Pure-integer fixed-point unit root approximation parameterized by `smul : ℤ → ℤ → ℤ`
with zero `ℚ` operations (Lemma 3.2 (`lem:elementary`); Section 8 (`sec:lean`)). -/
def expTwoPiIFixedWithMul (smul : ℤ → ℤ → ℤ) (q : ℕ) : ℤ → ℕ → FixedComplex q :=
  let S : ℕ := q + 10
  let q_pi : ℕ := 4 * (S + 3) + 6
  let piFixed : ℤ := approxPiFixed S
  let N : ℕ := 4 * 10 + S + 1
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  fun num den =>
    if den = 0 then ⟨0, 0⟩
    else
      let numMod : ℤ := num % (den : ℤ)
      let θNum : ℤ := 2 * smul piFixed numMod
      let θDen : ℤ := (den : ℤ) * (2 : ℤ) ^ q_pi
      let r_mant : ℤ := roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen
      let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
      let reSum : ℤ := ∑ m ∈ Finset.range (M + 1), iPowRe m * arr.getD m 0
      let imSum : ℤ := ∑ m ∈ Finset.range (M + 1), iPowIm m * arr.getD m 0
      ⟨roundDivInt (reSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc),
       roundDivInt (imSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)⟩

abbrev expTwoPiIFixed := expTwoPiIFixedWithMul (· * ·)

@[simp]
theorem expTwoPiIFixedWithMul_eq_expTwoPiIRatFixed (q : ℕ) :
    expTwoPiIFixedWithMul (· * ·) q = expTwoPiIRatFixed q := by
  funext num den
  unfold expTwoPiIFixedWithMul expTwoPiIRatFixed expITaylorRat expITaylorRatWithMul
  dsimp only
  split_ifs with hden
  · rfl
  · set S : ℕ := q + 10
    set q_pi : ℕ := 4 * (S + 3) + 6
    set piFixed : ℤ := approxPiFixed S
    set N : ℕ := 4 * 10 + S + 1
    set M : ℕ := N + 6
    set q_r : ℕ := 2 * M
    set q_acc : ℕ := 3 * M + 6
    set θNum : ℤ := 2 * (piFixed * (num % (den : ℤ)))
    set θDen : ℤ := (den : ℤ) * (2 : ℤ) ^ q_pi
    have hθ : (θNum : ℚ) / (θDen : ℚ) =
        2 * approxPiRat S * ((num % (den : ℤ) : ℤ) : ℚ) / (den : ℚ) := by
      dsimp [θNum, θDen, piFixed, q_pi]
      rw [← cast_approxPiFixed_div S]
      push_cast
      ring
    rw [← quantizeRatMantissa_div_int_eq_roundDivInt q_r θNum θDen, hθ]
    set arr : Array ℤ := expTermArrayFixedWithMul (· * ·) q_r q_acc M
      (quantizeRatMantissa q_r (2 * approxPiRat S * ((num % (den : ℤ) : ℤ) : ℚ) / (den : ℚ)))
    set reSum : ℤ := ∑ m ∈ Finset.range (M + 1), iPowRe m * arr.getD m 0
    set imSum : ℤ := ∑ m ∈ Finset.range (M + 1), iPowIm m * arr.getD m 0
    rw [← quantizeRatMantissa_div_int_eq_roundDivInt q reSum ((2 : ℤ) ^ q_acc),
      ← quantizeRatMantissa_div_int_eq_roundDivInt q imSum ((2 : ℤ) ^ q_acc)]
    push_cast
    rfl

private theorem half_eq_two_pow_sub_one_div (q : ℕ) (hq : 1 ≤ q) :
    (((2 : ℤ) ^ (q - 1) : ℤ) : ℚ) / (2 : ℚ) ^ q = 1 / 2 := by
  have hq_eq : q = (q - 1) + 1 := (Nat.sub_add_cancel hq).symm
  conv_lhs => rw [hq_eq, pow_succ]
  have h2 : (2 : ℚ) ^ (q - 1) ≠ 0 := by positivity
  push_cast
  field_simp [h2]

/-- Pure-integer clamped $\operatorname{sinc}$ Taylor mantissa at scale $3(N + 6) + 6$
with zero `ℚ` arithmetic. -/
def sincTaylorFixedWithMul (smul : ℤ → ℤ → ℤ) (N : ℕ) (θNum θDen : ℤ) : ℤ :=
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let r_mant : ℤ := roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen
  let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
  let sRaw : ℤ := ∑ m ∈ Finset.range (M + 1),
    iPowIm (m + 1) * roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ)
  max (-(2 : ℤ) ^ q_acc) (min ((2 : ℤ) ^ q_acc) sRaw)

abbrev sincTaylorFixed := sincTaylorFixedWithMul (· * ·)

theorem cast_sincTaylorFixedWithMul_div (N : ℕ) (θNum θDen : ℤ) :
    (sincTaylorFixedWithMul (· * ·) N θNum θDen : ℚ) /
        (2 : ℚ) ^ (3 * (N + 6) + 6) =
      max (-1) (min 1 (sincTaylorRat N ((θNum : ℚ) / (θDen : ℚ)))) := by
  unfold sincTaylorFixedWithMul sincTaylorRat sincTaylorRatWithMul
  dsimp only
  set q_r : ℕ := 2 * (N + 6)
  set q_acc : ℕ := 3 * (N + 6) + 6
  rw [← quantizeRatMantissa_div_int_eq_roundDivInt q_r θNum θDen,
    cast_max_div_two_pow, cast_min_div_two_pow]
  have h2 : (2 : ℚ) ^ q_acc ≠ 0 := by positivity
  push_cast
  rw [neg_div, div_self h2]

/-- Pure-integer clamped $\exp$ Taylor mantissa at scale $3(N + 6) + 6$
with zero `ℚ` arithmetic. -/
def expTaylorFixedWithMul (smul : ℤ → ℤ → ℤ) (N : ℕ) (gNum gDen : ℤ) : ℤ :=
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let r_mant : ℤ := roundDivInt (gNum * (2 : ℤ) ^ q_r) gDen
  let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
  let eRaw : ℤ := ∑ m ∈ Finset.range (M + 1), arr.getD m 0
  max 0 (min ((2 : ℤ) ^ q_acc) eRaw)

abbrev expTaylorFixed := expTaylorFixedWithMul (· * ·)

theorem cast_expTaylorFixedWithMul_div (N : ℕ) (gNum gDen : ℤ) :
    (expTaylorFixedWithMul (· * ·) N gNum gDen : ℚ) /
        (2 : ℚ) ^ (3 * (N + 6) + 6) =
      max 0 (min 1 (expTaylorRat N ((gNum : ℚ) / (gDen : ℚ)))) := by
  unfold expTaylorFixedWithMul expTaylorRat expTaylorRatWithMul
  dsimp only
  set q_r : ℕ := 2 * (N + 6)
  set q_acc : ℕ := 3 * (N + 6) + 6
  rw [← quantizeRatMantissa_div_int_eq_roundDivInt q_r gNum gDen,
    cast_max_div_two_pow, cast_min_div_two_pow]
  have h2 : (2 : ℚ) ^ q_acc ≠ 0 := by positivity
  push_cast
  rw [zero_div, div_self h2]

/-- Auxiliary pure-integer filter tap generator parameterized by atomic `(m1, t1, pW, pC, q, S)`
with zero `ℚ` operations. -/
def computeFilterTapAuxFixedWithMul (smul : ℤ → ℤ → ℤ) (m1 t1 pW pC q S : ℕ) :
    Fin t1 → ℤ → ℤ :=
  let q_pi : ℕ := 4 * (S + 3) + 6
  let piFixed : ℤ := approxPiFixed S
  let q_l2 : ℕ := S + (S + 2)
  let l2Fixed : ℤ := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S)
  let B_sinc : ℕ := 5 * (m1 + 1)
  let N_s : ℕ := 4 * B_sinc + S + 1
  let q_accs : ℕ := 3 * (N_s + 6) + 6
  let B_exp : ℕ := 25 * (pC + 1)
  let N_e : ℕ := 4 * B_exp + S + 1
  let q_acce : ℕ := 3 * (N_e + 6) + 6
  fun j1 d =>
    if |d| ≤ (m1 : ℤ) then
      let tNum : ℤ := d * (t1 : ℤ) - (j1.val : ℤ)
      let θNum : ℤ := smul piFixed tNum
      let θDen : ℤ := (t1 : ℤ) * (2 : ℤ) ^ q_pi
      let sincFixed : ℤ := sincTaylorFixedWithMul smul N_s θNum θDen
      let gNum : ℤ := -(smul θNum θNum * (2 : ℤ) ^ q_l2)
      let gDen : ℤ := (4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)
      let expFixed : ℤ := expTaylorFixedWithMul smul N_e gNum gDen
      roundDivInt (smul sincFixed expFixed * (2 : ℤ) ^ q) ((2 : ℤ) ^ (q_accs + q_acce))
    else 0

theorem computeFilterTapAuxFixedWithMul_eq (m1 t1 pW pC q S : ℕ) (ht1 : 0 < t1)
    (j1 : Fin t1) (d : ℤ) :
    computeFilterTapAuxFixedWithMul (· * ·) m1 t1 pW pC q S j1 d =
      if |d| ≤ (m1 : ℤ) then
        let tRat : ℚ := (d : ℚ) - (j1.val : ℚ) / (t1 : ℚ)
        let piVal : ℚ := approxPiRat S
        let log2Val : ℚ := max (1 / 2) (approxLogTwoRat S)
        let θ : ℚ := piVal * tRat
        let B_sinc : ℕ := 5 * (m1 + 1)
        let sincVal : ℚ := max (-1) (min 1 (sincTaylorRat (4 * B_sinc + S + 1) θ))
        let gRat : ℚ := θ ^ 2 / (4 * (pW : ℚ) * log2Val)
        let B_exp : ℕ := 25 * (pC + 1)
        let expVal : ℚ := max 0 (min 1 (expTaylorRat (4 * B_exp + S + 1) (-gRat)))
        quantizeRatMantissa q (sincVal * expVal)
      else 0 := by
  unfold computeFilterTapAuxFixedWithMul
  dsimp only
  split_ifs with hd
  · set q_pi : ℕ := 4 * (S + 3) + 6
    set piFixed : ℤ := approxPiFixed S
    set q_l2 : ℕ := S + (S + 2)
    set l2Fixed : ℤ := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S)
    set B_sinc : ℕ := 5 * (m1 + 1)
    set N_s : ℕ := 4 * B_sinc + S + 1
    set q_accs : ℕ := 3 * (N_s + 6) + 6
    set B_exp : ℕ := 25 * (pC + 1)
    set N_e : ℕ := 4 * B_exp + S + 1
    set q_acce : ℕ := 3 * (N_e + 6) + 6
    set tNum : ℤ := d * (t1 : ℤ) - (j1.val : ℤ)
    set θNum : ℤ := piFixed * tNum
    set θDen : ℤ := (t1 : ℤ) * (2 : ℤ) ^ q_pi
    set gNum : ℤ := -(θNum * θNum * (2 : ℤ) ^ q_l2)
    set gDen : ℤ := (4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)
    have ht1_ne : (t1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht1)
    have h2pi_ne : (2 : ℚ) ^ q_pi ≠ 0 := by positivity
    have h2l2_ne : (2 : ℚ) ^ q_l2 ≠ 0 := by positivity
    have hθ : (θNum : ℚ) / (θDen : ℚ) =
        approxPiRat S * ((d : ℚ) - (j1.val : ℚ) / (t1 : ℚ)) := by
      dsimp [θNum, θDen, tNum, piFixed, q_pi]
      rw [← cast_approxPiFixed_div S]
      push_cast
      field_simp [ht1_ne, h2pi_ne]
    have hl2 : (l2Fixed : ℚ) / (2 : ℚ) ^ q_l2 = max (1 / 2) (approxLogTwoRat S) := by
      dsimp [l2Fixed]
      rw [cast_max_div_two_pow, half_eq_two_pow_sub_one_div q_l2 (by dsimp [q_l2]; omega),
        cast_approxLogTwoFixed_div]
    have hg : (gNum : ℚ) / (gDen : ℚ) =
        -((approxPiRat S * ((d : ℚ) - (j1.val : ℚ) / (t1 : ℚ))) ^ 2 /
          (4 * (pW : ℚ) * max (1 / 2) (approxLogTwoRat S))) := by
      rw [← hθ, ← hl2]
      dsimp [gNum, gDen, θDen]
      have hpow2 : (2 : ℚ) ^ (2 * q_pi) = ((2 : ℚ) ^ q_pi) * ((2 : ℚ) ^ q_pi) := by
        rw [Nat.two_mul, pow_add]
      push_cast
      rw [hpow2]
      field_simp [ht1_ne, h2pi_ne, h2l2_ne]
    set sincFixed : ℤ := sincTaylorFixedWithMul (· * ·) N_s θNum θDen
    set expFixed : ℤ := expTaylorFixedWithMul (· * ·) N_e gNum gDen
    have hprod :
        ((sincFixed * expFixed : ℤ) : ℚ) / (((2 : ℤ) ^ (q_accs + q_acce) : ℤ) : ℚ) =
          ((sincFixed : ℚ) / (2 : ℚ) ^ q_accs) * ((expFixed : ℚ) / (2 : ℚ) ^ q_acce) := by
      rw [pow_add]
      push_cast
      exact (div_mul_div_comm (sincFixed : ℚ) ((2 : ℚ) ^ q_accs) (expFixed : ℚ) ((2 : ℚ) ^ q_acce)).symm
    rw [← quantizeRatMantissa_div_int_eq_roundDivInt q (sincFixed * expFixed) ((2 : ℤ) ^ (q_accs + q_acce)),
      hprod, cast_sincTaylorFixedWithMul_div N_s θNum θDen,
      cast_expTaylorFixedWithMul_div N_e gNum gDen, hθ, hg]
  · rfl

/-- Pure-integer fixed-point sinc-Gaussian filter tap generator parameterized by `smul : ℤ → ℤ → ℤ`
with zero `ℚ` operations (Theorem 4.2 (`thm:poisson`), Lemma 3.2 (`lem:elementary`), and
Section 8 (`sec:lean`)). -/
def computeFilterTapFixedWithMul (smul : ℤ → ℤ → ℤ) (K p : ℕ) : Fin (t1Ell K) → ℤ → ℤ :=
  let q : ℕ := qChildEll K p
  let pC : ℕ := pChildEll K p
  computeFilterTapAuxFixedWithMul smul (computeM1Ell K p) (t1Ell K) (pWorkEll K p) pC q
    (q + 3 * pC + 20)

@[simp]
theorem computeFilterTapFixedWithMul_eq_computeFilterTapFixed (K p : ℕ) :
    computeFilterTapFixedWithMul (· * ·) K p = computeFilterTapFixed K p := by
  funext j1 d
  unfold computeFilterTapFixedWithMul computeFilterTapFixed computeFilterTapRat
  exact computeFilterTapAuxFixedWithMul_eq (computeM1Ell K p) (t1Ell K) (pWorkEll K p)
    (pChildEll K p) (qChildEll K p) (qChildEll K p + 3 * pChildEll K p + 20)
    (t1Ell_pos K) j1 d

/-- Pure-integer $\int_0^z e^{-t^2}\,dt$ Taylor mantissa at scale $4(N + 6) + 6$
with zero `ℚ` arithmetic. -/
def erfIntegralTaylorFixedWithMul (smul : ℤ → ℤ → ℤ) (N : ℕ) (zNum zDen : ℤ) : ℤ :=
  let M : ℕ := N + 6
  let q_z : ℕ := M
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let z_mant : ℤ := roundDivInt (zNum * (2 : ℤ) ^ q_z) zDen
  let r_mant : ℤ := - smul z_mant z_mant
  let arr : Array ℤ := expTermArrayFixedWithMul smul q_r q_acc M r_mant
  let S_inner : ℤ := ∑ m ∈ Finset.range (M + 1),
    roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ)
  smul z_mant S_inner

abbrev erfIntegralTaylorFixed := erfIntegralTaylorFixedWithMul (· * ·)

theorem cast_erfIntegralTaylorFixedWithMul_div (N : ℕ) (zNum zDen : ℤ) :
    (erfIntegralTaylorFixedWithMul (· * ·) N zNum zDen : ℚ) /
        (2 : ℚ) ^ ((N + 6) + (3 * (N + 6) + 6)) =
      erfIntegralTaylorRat N ((zNum : ℚ) / (zDen : ℚ)) := by
  unfold erfIntegralTaylorFixedWithMul erfIntegralTaylorRat erfIntegralTaylorRatWithMul
  dsimp only
  set q_z : ℕ := N + 6
  rw [← quantizeRatMantissa_div_int_eq_roundDivInt q_z zNum zDen]

/-- Auxiliary pure-integer generator for the quantized mantissa of $\hat{g}_{\alpha_\ell}(\text{yNum} / r)$
parameterized by atomic `(q, pW, S)` with zero `ℚ` operations. -/
def computeGHatMantissaAuxFixedWithMul (smul : ℤ → ℤ → ℤ) (q pW S : ℕ) : ℤ → ℕ → ℤ :=
  let q_l2 : ℕ := 2 * S + (2 * S + 2)
  let l2Fixed : ℤ := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed (2 * S))
  let cBound : ℕ := Nat.sqrt (3 * pW) + 1
  let cRawFixed : ℤ := approxSqrtFixed (2 * S + 2) (4 * (pW : ℤ) * l2Fixed)
  let cFixed : ℤ := min ((cBound : ℤ) * (2 : ℤ) ^ S) cRawFixed
  let B_erf : ℕ := 2 * cBound
  let N_erf : ℕ := 4 * B_erf ^ 2 + (S + B_erf) + 1
  let M : ℕ := N_erf + 6
  let q_z : ℕ := M
  let q_acc : ℕ := 3 * M + 6
  let pi2SFixed : ℤ := approxPiFixed (2 * S)
  let sqrtPiRawFixed : ℤ := approxSqrtFixed (6 * S + 18) pi2SFixed
  let sqrtPiFixed : ℤ := max ((2 : ℤ) ^ S) sqrtPiRawFixed
  fun yNum r =>
    let zDen : ℤ := 2 * (r : ℤ) * (2 : ℤ) ^ S
    let z1Num : ℤ := smul cFixed ((r : ℤ) - 2 * yNum)
    let I1Fixed : ℤ := erfIntegralTaylorFixedWithMul smul N_erf z1Num zDen
    let z2Num : ℤ := smul cFixed ((r : ℤ) + 2 * yNum)
    let I2Fixed : ℤ := erfIntegralTaylorFixedWithMul smul N_erf z2Num zDen
    max 0 (roundDivInt (((I1Fixed + I2Fixed) * (2 : ℤ) ^ S) * (2 : ℤ) ^ q)
      (sqrtPiFixed * (2 : ℤ) ^ (q_z + q_acc)))

theorem computeGHatMantissaAuxFixedWithMul_eq (q pW S : ℕ) (yNum : ℤ) {r : ℕ} (hr : 0 < r) :
    computeGHatMantissaAuxFixedWithMul (· * ·) q pW S yNum r =
      let log2Val : ℚ := max (1 / 2) (approxLogTwoRat (2 * S))
      let cBound : ℕ := Nat.sqrt (3 * pW) + 1
      let cRat : ℚ := min (cBound : ℚ) (approxSqrtRat S (4 * (pW : ℚ) * log2Val))
      let B_erf : ℕ := 2 * cBound
      let N_erf : ℕ := 4 * B_erf ^ 2 + (S + B_erf) + 1
      let sqrtPiVal : ℚ := max 1 (approxSqrtRat S (approxPiRat (2 * S)))
      let z1 : ℚ := cRat * (1 / 2 - (yNum : ℚ) / (r : ℚ))
      let z2 : ℚ := cRat * (1 / 2 + (yNum : ℚ) / (r : ℚ))
      let I1Rat : ℚ := erfIntegralTaylorRat N_erf z1
      let I2Rat : ℚ := erfIntegralTaylorRat N_erf z2
      max 0 (quantizeRatMantissa q ((I1Rat + I2Rat) / sqrtPiVal)) := by
  unfold computeGHatMantissaAuxFixedWithMul
  dsimp only
  set q_l2 : ℕ := 2 * S + (2 * S + 2)
  set l2Fixed : ℤ := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed (2 * S))
  set cBound : ℕ := Nat.sqrt (3 * pW) + 1
  set cRawFixed : ℤ := approxSqrtFixed (2 * S + 2) (4 * (pW : ℤ) * l2Fixed)
  set cFixed : ℤ := min ((cBound : ℤ) * (2 : ℤ) ^ S) cRawFixed
  set B_erf : ℕ := 2 * cBound
  set N_erf : ℕ := 4 * B_erf ^ 2 + (S + B_erf) + 1
  set q_tot : ℕ := (N_erf + 6) + (3 * (N_erf + 6) + 6)
  set pi2SFixed : ℤ := approxPiFixed (2 * S)
  set sqrtPiRawFixed : ℤ := approxSqrtFixed (6 * S + 18) pi2SFixed
  set sqrtPiFixed : ℤ := max ((2 : ℤ) ^ S) sqrtPiRawFixed
  set zDen : ℤ := 2 * (r : ℤ) * (2 : ℤ) ^ S
  set z1Num : ℤ := cFixed * ((r : ℤ) - 2 * yNum)
  set z2Num : ℤ := cFixed * ((r : ℤ) + 2 * yNum)
  set I1Fixed : ℤ := erfIntegralTaylorFixedWithMul (· * ·) N_erf z1Num zDen
  set I2Fixed : ℤ := erfIntegralTaylorFixedWithMul (· * ·) N_erf z2Num zDen
  have hr_ne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hr)
  have h2S_ne : (2 : ℚ) ^ S ≠ 0 := by positivity
  have hl2 : (l2Fixed : ℚ) / (2 : ℚ) ^ q_l2 = max (1 / 2) (approxLogTwoRat (2 * S)) := by
    dsimp [l2Fixed]
    rw [cast_max_div_two_pow, half_eq_two_pow_sub_one_div q_l2 (by dsimp [q_l2]; omega),
      cast_approxLogTwoFixed_div]
  have hcRaw : (cRawFixed : ℚ) / (2 : ℚ) ^ S =
      approxSqrtRat S (4 * (pW : ℚ) * max (1 / 2) (approxLogTwoRat (2 * S))) := by
    have harg : ((4 * (pW : ℤ) * l2Fixed : ℤ) : ℚ) / (2 : ℚ) ^ (2 * S + (2 * S + 2)) =
        4 * (pW : ℚ) * ((l2Fixed : ℚ) / (2 : ℚ) ^ q_l2) := by
      dsimp [q_l2]
      push_cast
      ring
    dsimp [cRawFixed]
    rw [approxSqrtFixed_eq_approxSqrtRat S (2 * S + 2) (4 * (pW : ℤ) * l2Fixed), harg, hl2]
  have hcFixed : (cFixed : ℚ) / (2 : ℚ) ^ S =
      min (cBound : ℚ) (approxSqrtRat S (4 * (pW : ℚ) * max (1 / 2) (approxLogTwoRat (2 * S)))) := by
    have hcb : (((cBound : ℤ) * (2 : ℤ) ^ S : ℤ) : ℚ) / (2 : ℚ) ^ S = (cBound : ℚ) := by
      push_cast
      exact mul_div_cancel_right₀ (cBound : ℚ) h2S_ne
    dsimp [cFixed]
    rw [cast_min_div_two_pow, hcb, hcRaw]
  have hsqrtPiRaw : (sqrtPiRawFixed : ℚ) / (2 : ℚ) ^ S =
      approxSqrtRat S (approxPiRat (2 * S)) := by
    have hexp : 2 * S + (6 * S + 18) = 4 * (2 * S + 3) + 6 := by omega
    dsimp [sqrtPiRawFixed, pi2SFixed]
    rw [approxSqrtFixed_eq_approxSqrtRat S (6 * S + 18) (approxPiFixed (2 * S)),
      hexp, cast_approxPiFixed_div (2 * S)]
  have hsqrtPi : (sqrtPiFixed : ℚ) / (2 : ℚ) ^ S =
      max 1 (approxSqrtRat S (approxPiRat (2 * S))) := by
    have h1 : (((2 : ℤ) ^ S : ℤ) : ℚ) / (2 : ℚ) ^ S = 1 := by
      push_cast
      exact div_self h2S_ne
    dsimp [sqrtPiFixed]
    rw [cast_max_div_two_pow, h1, hsqrtPiRaw]
  set cRat : ℚ := min (cBound : ℚ) (approxSqrtRat S (4 * (pW : ℚ) * max (1 / 2) (approxLogTwoRat (2 * S))))
  set sqrtPiVal : ℚ := max 1 (approxSqrtRat S (approxPiRat (2 * S)))
  have hz1 : (z1Num : ℚ) / (zDen : ℚ) = cRat * (1 / 2 - (yNum : ℚ) / (r : ℚ)) := by
    rw [← hcFixed]
    dsimp [z1Num, zDen]
    push_cast
    field_simp [hr_ne, h2S_ne]
  have hz2 : (z2Num : ℚ) / (zDen : ℚ) = cRat * (1 / 2 + (yNum : ℚ) / (r : ℚ)) := by
    rw [← hcFixed]
    dsimp [z2Num, zDen]
    push_cast
    field_simp [hr_ne, h2S_ne]
  have hdiv :
      ((((I1Fixed + I2Fixed) * (2 : ℤ) ^ S : ℤ) : ℚ) /
          ((sqrtPiFixed * (2 : ℤ) ^ q_tot : ℤ) : ℚ)) =
        ((I1Fixed : ℚ) / (2 : ℚ) ^ q_tot + (I2Fixed : ℚ) / (2 : ℚ) ^ q_tot) /
          ((sqrtPiFixed : ℚ) / (2 : ℚ) ^ S) := by
    have h2z : (2 : ℚ) ^ q_tot ≠ 0 := by positivity
    push_cast
    field_simp [h2S_ne, h2z]
  rw [← quantizeRatMantissa_div_int_eq_roundDivInt q ((I1Fixed + I2Fixed) * (2 : ℤ) ^ S)
      (sqrtPiFixed * (2 : ℤ) ^ q_tot),
    hdiv, hsqrtPi,
    cast_erfIntegralTaylorFixedWithMul_div N_erf z1Num zDen,
    cast_erfIntegralTaylorFixedWithMul_div N_erf z2Num zDen,
    hz1, hz2]

/-- Pure-integer generator for the quantized mantissa of $\hat{g}_{\alpha_\ell}(\text{yNum} / r)$
parameterized by `smul : ℤ → ℤ → ℤ` with zero `ℚ` operations
(Theorem 4.2 (`thm:poisson`), Theorem 5.1 (`thm:deconv`), Lemma 3.2 (`lem:elementary`), and
Section 8 (`sec:lean`)). -/
def computeGHatMantissaFixedWithMul (smul : ℤ → ℤ → ℤ) (K p : ℕ) : ℤ → ℕ → ℤ :=
  let q : ℕ := qChildEll K p
  let pW : ℕ := pWorkEll K p
  computeGHatMantissaAuxFixedWithMul smul q pW (q + 2 * pW + 20)

abbrev computeGHatMantissaFixed := computeGHatMantissaFixedWithMul (· * ·)

theorem computeGHatMantissaFixedWithMul_eq_computeGHatMantissa (K p : ℕ) (yNum : ℤ)
    {r : ℕ} (hr : 0 < r) :
    computeGHatMantissaFixedWithMul (· * ·) K p yNum r =
      computeGHatMantissa K p ((yNum : ℚ) / (r : ℚ)) := by
  unfold computeGHatMantissaFixedWithMul computeGHatMantissa computeGHatRat
  exact computeGHatMantissaAuxFixedWithMul_eq (qChildEll K p) (pWorkEll K p)
    (qChildEll K p + 2 * pWorkEll K p + 20) yNum hr

/-- Pure-integer passband constant $c_0$ mantissa generator parameterized by `smul : ℤ → ℤ → ℤ`
with zero `ℚ` operations. -/
def computePassbandC0MantissaWithMul (smul : ℤ → ℤ → ℤ) (K p : ℕ) : Fin (rEll K) → ℤ :=
  let gHatM := computeGHatMantissaFixedWithMul smul K p
  let r := rEll K
  fun u2 => gHatM (u2.val : ℤ) r

/-- Pure-integer passband constant $c_1$ mantissa generator parameterized by `smul : ℤ → ℤ → ℤ`
with zero `ℚ` operations. -/
def computePassbandC1MantissaWithMul (smul : ℤ → ℤ → ℤ) (K p : ℕ) : Fin (rEll K) → ℤ :=
  let gHatM := computeGHatMantissaFixedWithMul smul K p
  let r := rEll K
  fun u2 => gHatM ((r : ℤ) - (u2.val : ℤ)) r

@[simp]
theorem computePassbandC0MantissaWithMul_eq_computePassbandC0Mantissa (K p : ℕ) :
    computePassbandC0MantissaWithMul (· * ·) K p = computePassbandC0Mantissa K p := by
  funext u2
  unfold computePassbandC0MantissaWithMul computePassbandC0Mantissa
  simpa using computeGHatMantissaFixedWithMul_eq_computeGHatMantissa K p (u2.val : ℤ) (rEll_pos K)

@[simp]
theorem computePassbandC1MantissaWithMul_eq_computePassbandC1Mantissa (K p : ℕ) :
    computePassbandC1MantissaWithMul (· * ·) K p = computePassbandC1Mantissa K p := by
  funext u2
  unfold computePassbandC1MantissaWithMul computePassbandC1Mantissa
  rw [computeGHatMantissaFixedWithMul_eq_computeGHatMantissa K p
    ((rEll K : ℤ) - (u2.val : ℤ)) (rEll_pos K)]
  congr 1
  have hr : (rEll K : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (rEll_pos K))
  push_cast
  field_simp [hr]

/-- **Computable Pure-Integer Schedule Tree Generator (`computeScheduleIntTree`)**:
Constructs the entire multi-level schedule tree `ScheduleIntTree K p B_in` using **pure
integer arithmetic (`ℕ`/`ℤ`, zero `ℚ`, zero `noncomputable`, zero `ℝ`, zero `ℂ`)** via
`expTwoPiIFixedWithMul`, `computeFilterTapFixedWithMul`, `computePassbandC0MantissaWithMul`, and
`computePassbandC1MantissaWithMul`, hoisting all per-level constants and pre-tabulating every
node's tables into contiguous arrays once per level via `memoizeFilterTap` and `memoizeFin`. -/
def computeScheduleIntTree (K p B_in : ℕ) : ScheduleIntTree K p B_in :=
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    let expRoot := expTwoPiIFixedWithMul (· * ·) (qChildEll K p)
    ScheduleIntTree.node K p B_in (computeM1Ell K p)
      (memoizeFilterTap (computeM1Ell K p) (computeFilterTapFixedWithMul (· * ·) K p))
      (memoizeFin (fun k2 => expRoot (k2.val : ℤ) (2 * rEll K)))
      (memoizeFin (fun k2 => expRoot (-(k2.val : ℤ)) (2 * rEll K)))
      (memoizeFin (computePassbandC0MantissaWithMul (· * ·) K p))
      (memoizeFin (computePassbandC1MantissaWithMul (· * ·) K p))
      (computeScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
  else
    let expLeaf := expTwoPiIFixedWithMul (· * ·) (qBaseEll K p)
    ScheduleIntTree.leaf K p B_in
      (memoizeFin (fun u => expLeaf (u.val : ℤ) (2 ^ K)))
termination_by K
decreasing_by
  unfold k2Ell
  omega

/-- **Unconditional Validity of the Computable Pure-Integer Schedule Tree
`computeScheduleIntTree` (`validScheduleIntTree_computeScheduleIntTree`)**:
For every `(K, p, B_in)`, the pure-integer schedule tree `computeScheduleIntTree K p B_in`
satisfies `ValidScheduleIntTree`. -/
theorem validScheduleIntTree_computeScheduleIntTree (K : ℕ) :
    ∀ p B_in : ℕ, ValidScheduleIntTree (computeScheduleIntTree K p B_in) := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [computeScheduleIntTree]
    split_ifs with hcond
    · dsimp only
      rw [computeFilterTapFixedWithMul_eq_computeFilterTapFixed,
        expTwoPiIFixedWithMul_eq_expTwoPiIRatFixed,
        computePassbandC0MantissaWithMul_eq_computePassbandC0Mantissa,
        computePassbandC1MantissaWithMul_eq_computePassbandC1Mantissa,
        memoizeFilterTap_computeFilterTapFixed, memoizeFin_eq, memoizeFin_eq,
        memoizeFin_eq, memoizeFin_eq]
      have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      exact ValidScheduleIntTree.node K p B_in (computeM1Ell K p)
        (computeFilterTapFixed K p)
        (fun k2 => expTwoPiIRatFixed (qChildEll K p) (k2.val : ℤ) (2 * rEll K))
        (fun k2 => expTwoPiIRatFixed (qChildEll K p) (-(k2.val : ℤ)) (2 * rEll K))
        (computePassbandC0Mantissa K p)
        (computePassbandC1Mantissa K p)
        (computeScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
        hcond
        (m1Ell_le_computeM1Ell K p)
        (computeM1Ell_le_pChildEll K p)
        (fitsSignedWord_computeFilterTapFixed K p)
        (abs_computeFilterTapFixed_mul_zpow_le_one K p)
        (abs_computeFilterTapFixed_sub_filterTap_le K p)
        (fun k2 => norm_expTwoPiIRatFixed_sub_zetaPow_le (qChildEll K p) (rEll_pos K) (k2.val : ℤ))
        (fun k2 => norm_expTwoPiIRatFixed_sub_zetaPow_le (qChildEll K p) (rEll_pos K) (-(k2.val : ℤ)))
        (computePassbandC0Mantissa_nonneg K p)
        (computePassbandC1Mantissa_nonneg K p)
        (abs_computePassbandC0Mantissa_sub_passbandC0_le K p)
        (abs_computePassbandC1Mantissa_sub_passbandC1_le K p)
        (ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in))
    · dsimp only
      rw [expTwoPiIFixedWithMul_eq_expTwoPiIRatFixed, memoizeFin_eq]
      exact ValidScheduleIntTree.leaf K p B_in
        (fun u => expTwoPiIRatFixed (qBaseEll K p) (u.val : ℤ) (2 ^ K))
        hcond
        (fun u => norm_expTwoPiIRatFixed_sub_expTwoPiI_le (qBaseEll K p) (u.val : ℤ) (Nat.two_pow_pos K))

/-- **Computable Pure-Integer Schedule Tree Generator Parameterized by Sub-Multiplier
`natMul : ℕ → ℕ → ℕ` (`computeScheduleIntTreeWithMul`)**:
Executes pure `ℕ`/`ℤ` fixed-point arithmetic (`roundDivInt`, `Nat.sqrt`, `signedMulFromNatMul natMul`)
with **zero `ℚ` operations** and **zero `Nat.gcd` normalizations**. -/
def computeScheduleIntTreeWithMul (natMul : ℕ → ℕ → ℕ) (K p B_in : ℕ) :
    ScheduleIntTree K p B_in :=
  let smul : ℤ → ℤ → ℤ := signedMulFromNatMul natMul
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    let expRoot := expTwoPiIFixedWithMul smul (qChildEll K p)
    ScheduleIntTree.node K p B_in (computeM1Ell K p)
      (memoizeFilterTap (computeM1Ell K p) (computeFilterTapFixedWithMul smul K p))
      (memoizeFin (fun k2 => expRoot (k2.val : ℤ) (2 * rEll K)))
      (memoizeFin (fun k2 => expRoot (-(k2.val : ℤ)) (2 * rEll K)))
      (memoizeFin (computePassbandC0MantissaWithMul smul K p))
      (memoizeFin (computePassbandC1MantissaWithMul smul K p))
      (computeScheduleIntTreeWithMul natMul (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
  else
    let expLeaf := expTwoPiIFixedWithMul smul (qBaseEll K p)
    ScheduleIntTree.leaf K p B_in
      (memoizeFin (fun u => expLeaf (u.val : ℤ) (2 ^ K)))
termination_by K
decreasing_by
  unfold k2Ell
  omega

/-- Equivalence between `computeScheduleIntTreeWithMul natMul` and `computeScheduleIntTree`
whenever `natMul` agrees with `Nat.mul`. -/
theorem computeScheduleIntTreeWithMul_eq_computeScheduleIntTree
    {natMul : ℕ → ℕ → ℕ} (hmul : ∀ a b : ℕ, natMul a b = a * b) (K : ℕ) :
    ∀ p B_in : ℕ,
      computeScheduleIntTreeWithMul natMul K p B_in = computeScheduleIntTree K p B_in := by
  have hsmul : signedMulFromNatMul natMul = (· * ·) := by
    funext x y
    exact signedMulFromNatMul_eq_mul natMul hmul x y
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [computeScheduleIntTreeWithMul, computeScheduleIntTree]
    dsimp only
    rw [hsmul]
    split_ifs with hcond
    · have hk2_lt : k2Ell K < K := by
        have hK2 : 2 ≤ K := hcond.2
        unfold k2Ell; omega
      rw [ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in)]
    · rfl

/-! ### 5. Pure-Integer Width Bounds for Tracked Schedule Evaluation -/

theorem approxLogTwoFixed_nonneg (S : ℕ) : 0 ≤ approxLogTwoFixed S := by
  have h1 : (0 : ℚ) ≤ approxLogTwoRat S := approxLogTwoRat_nonneg S
  have hpos : (0 : ℚ) < (2 : ℚ) ^ (S + (S + 2)) := by positivity
  rw [← cast_approxLogTwoFixed_div S, le_div_iff₀ hpos, zero_mul] at h1
  exact_mod_cast h1

theorem approxLogTwoFixed_le (S : ℕ) :
    approxLogTwoFixed S ≤ 2 * (2 : ℤ) ^ (S + (S + 2)) := by
  have h1 : (approxLogTwoRat S : ℝ) ≤ 2 := approxLogTwoRat_le_one S
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) (cast_approxLogTwoFixed_div S)
  push_cast at h2
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (S + (S + 2)) := by positivity
  rw [← h2, div_le_iff₀ hpos] at h1
  exact_mod_cast h1

theorem approxPiFixed_nonneg (S : ℕ) : 0 ≤ approxPiFixed S := by
  have h1 : (0 : ℝ) ≤ (approxPiRat S : ℝ) := approxPiRat_nonneg S
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) (cast_approxPiFixed_div S)
  push_cast at h2
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (4 * (S + 3) + 6) := by positivity
  rw [← h2, le_div_iff₀ hpos, zero_mul] at h1
  exact_mod_cast h1

theorem approxPiFixed_le (S : ℕ) :
    approxPiFixed S ≤ 5 * (2 : ℤ) ^ (4 * (S + 3) + 6) := by
  have h1 : (approxPiRat S : ℝ) ≤ 5 := approxPiRat_le_five S
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) (cast_approxPiFixed_div S)
  push_cast at h2
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (4 * (S + 3) + 6) := by positivity
  rw [← h2, div_le_iff₀ hpos] at h1
  exact_mod_cast h1

theorem fitsSignedWord_approxPiFixed (S : ℕ) {w : ℕ}
    (hw : 4 * (S + 3) + 10 ≤ w) :
    FitsSignedWord w (approxPiFixed S) := by
  unfold FitsSignedWord
  rw [abs_of_nonneg (approxPiFixed_nonneg S)]
  have hle := approxPiFixed_le S
  have hlt : 5 * (2 : ℤ) ^ (4 * (S + 3) + 6) < (2 : ℤ) ^ (4 * (S + 3) + 9) := by
    have : (2 : ℤ) ^ (4 * (S + 3) + 9) = 8 * (2 : ℤ) ^ (4 * (S + 3) + 6) := by
      rw [show 4 * (S + 3) + 9 = (4 * (S + 3) + 6) + 3 by omega, pow_add]; ring
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (4 * (S + 3) + 6) := by positivity
    linarith
  exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt
    (pow_le_pow_right₀ (by decide) (by omega)))

theorem fitsSignedWord_buildRecurrenceArray_arctanInvPowStepFixed (k q_acc : ℕ) :
    ∀ m : ℕ,
      FitsSignedWord (q_acc + 2)
        (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
          (arctanInvPowStepFixed k) m).2
  | 0 => by
    simp only [buildRecurrenceArray]
    refine FitsSignedWord.roundDivInt (k : ℤ) ?_
    unfold FitsSignedWord
    rw [abs_of_pos (by positivity)]
    exact pow_lt_pow_right₀ (by decide) (by omega)
  | m + 1 => by
    simp only [buildRecurrenceArray, arctanInvPowStepFixed]
    exact FitsSignedWord.roundDivInt ((k * k : ℕ) : ℤ)
      (fitsSignedWord_buildRecurrenceArray_arctanInvPowStepFixed k q_acc m)

theorem fitsSignedWord_arctanInvPowArrayFixed_getD (k q_acc N m : ℕ) :
    FitsSignedWord (q_acc + 2) ((arctanInvPowArrayFixed k q_acc N).getD m 0) := by
  by_cases hm : m ≤ N
  · rw [arctanInvPowArrayFixed,
      getD_default_buildRecurrenceArray _ 0 (arctanInvPowStepFixed k) hm]
    exact fitsSignedWord_buildRecurrenceArray_arctanInvPowStepFixed k q_acc m
  · unfold arctanInvPowArrayFixed
    have hsz : (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
        (arctanInvPowStepFixed k) N).1.size = N + 1 :=
      size_buildRecurrenceArray _ _ N
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    unfold FitsSignedWord; simp

theorem abs_roundDivInt_mul_two_pow_le (B q : ℕ) (a b : ℤ)
    (hab : |a| ≤ (B : ℤ) * |b|) :
    |roundDivInt (a * (2 : ℤ) ^ q) b| ≤ (B : ℤ) * (2 : ℤ) ^ q := by
  have h2q : (0 : ℤ) ≤ (2 : ℤ) ^ q := by positivity
  refine abs_roundDivInt_le_of_abs_le_mul (by positivity) ?_
  rw [abs_mul, abs_of_nonneg h2q]
  calc |a| * (2 : ℤ) ^ q
      ≤ ((B : ℤ) * |b|) * (2 : ℤ) ^ q := mul_le_mul_of_nonneg_right hab h2q
    _ = ((B : ℤ) * (2 : ℤ) ^ q) * |b| := by ring

theorem abs_roundDivInt_mul_two_pow_le_of_pos (B q : ℕ) {a b : ℤ}
    (hb : 0 < b) (hab : |a| ≤ (B : ℤ) * b) :
    |roundDivInt (a * (2 : ℤ) ^ q) b| ≤ (B : ℤ) * (2 : ℤ) ^ q := by
  apply abs_roundDivInt_mul_two_pow_le B q a b
  rwa [abs_of_pos hb]

theorem rEll_le_two_pow (K : ℕ) : rEll K ≤ 2 ^ K :=
  Nat.pow_le_pow_right (by decide) (by unfold k2Ell; omega)

theorem four_mul_lt_two_pow {q : ℕ} (hq : 18 ≤ q) : 4 * q < 2 ^ q := by
  have hlt := Nat.lt_two_pow_self (n := q - 3)
  have hpow : 2 ^ q = 8 * 2 ^ (q - 3) := by
    conv_lhs => rw [show q = (q - 3) + 3 by omega, pow_add]
    ring
  omega

theorem fitsSignedWord_max_approxLogTwoFixed (S : ℕ) {w : ℕ}
    (hw : 2 * S + 4 ≤ w) :
    FitsSignedWord w (max ((2 : ℤ) ^ (S + (S + 2) - 1)) (approxLogTwoFixed S)) := by
  unfold FitsSignedWord
  have hnn : 0 ≤ max ((2 : ℤ) ^ (S + (S + 2) - 1)) (approxLogTwoFixed S) :=
    le_trans (by positivity) (le_max_left _ _)
  rw [abs_of_nonneg hnn]
  have h1 : (2 : ℤ) ^ (S + (S + 2) - 1) ≤ 2 * (2 : ℤ) ^ (S + (S + 2)) := by
    have hle : (2 : ℤ) ^ (S + (S + 2) - 1) ≤ (2 : ℤ) ^ (S + (S + 2)) :=
      pow_le_pow_right₀ (by decide) (by omega)
    linarith [show (0 : ℤ) ≤ (2 : ℤ) ^ (S + (S + 2)) by positivity]
  have hle : max ((2 : ℤ) ^ (S + (S + 2) - 1)) (approxLogTwoFixed S) ≤
      2 * (2 : ℤ) ^ (S + (S + 2)) :=
    max_le h1 (approxLogTwoFixed_le S)
  have hlt : 2 * (2 : ℤ) ^ (S + (S + 2)) < (2 : ℤ) ^ (2 * S + 4) := by
    have hpow : (2 : ℤ) ^ (2 * S + 4) = 4 * (2 : ℤ) ^ (S + (S + 2)) := by
      rw [show 2 * S + 4 = (S + (S + 2)) + 2 by omega, pow_add]; ring
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (S + (S + 2)) := by positivity
    linarith
  exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt (pow_le_pow_right₀ (by decide) hw))

theorem toNat_max_zero_div_two_pow_lt_four_pow {w k : ℕ} {num : ℤ}
    (hnum : FitsSignedWord w num) :
    (max 0 num).toNat / 2 ^ k < 4 ^ w := by
  refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_
  have hlt : num < (2 : ℤ) ^ w := (abs_lt.mp hnum).2
  have htoNat : (max 0 num).toNat < 2 ^ w := by
    zify; rw [Int.toNat_of_nonneg (le_max_left _ _)]
    exact max_lt (by positivity) hlt
  exact lt_of_lt_of_le htoNat (Nat.pow_le_pow_left (by decide) w)

theorem toNat_max_zero_four_mul_l2GHat_div_lt_four_pow (pW S w : ℕ)
    (hpW : 4 * pW < 2 ^ S) (hw : 6 * S + 6 ≤ w) :
    (max 0 (4 * (pW : ℤ) *
      max ((2 : ℤ) ^ (2 * S + (2 * S + 2) - 1)) (approxLogTwoFixed (2 * S)))).toNat /
        2 ^ (2 * S + 2) < 4 ^ w := by
  apply toNat_max_zero_div_two_pow_lt_four_pow
  have hpW_fits : FitsSignedWord S (4 * (pW : ℤ)) := by
    unfold FitsSignedWord
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hpW
  have hl2_fits : FitsSignedWord (4 * S + 4)
      (max ((2 : ℤ) ^ (2 * S + (2 * S + 2) - 1)) (approxLogTwoFixed (2 * S))) :=
    fitsSignedWord_max_approxLogTwoFixed (2 * S) (by omega)
  exact (hpW_fits.mul hl2_fits).mono (by omega)

theorem toNat_max_zero_approxPiFixed_div_lt_four_pow (S k w : ℕ)
    (hw : 4 * (S + 3) + 10 ≤ w) :
    (max 0 (approxPiFixed S)).toNat / 2 ^ k < 4 ^ w :=
  toNat_max_zero_div_two_pow_lt_four_pow (fitsSignedWord_approxPiFixed S hw)

@[simp]
theorem expTermArrayFixedWithMul_mul_eq :
    expTermArrayFixedWithMul (· * ·) = expTermArrayFixed := rfl

theorem abs_buildRecurrenceArray_expTermStepFixed_le
    (B q_r q_acc : ℕ) (r_mant : ℤ)
    (hr : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r)
    {m : ℕ} (hm : m ≤ q_acc) :
    |(buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2| ≤
      (2 : ℤ) ^ (q_acc + 2 * B + 1) := by
  have hr_R : |(r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))| ≤ (B : ℝ) := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(q_r : ℤ)) := zpow_pos (by norm_num) _
    rw [abs_mul, abs_of_pos h2pos, zpow_neg, zpow_natCast,
      ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    exact_mod_cast hr
  have hrec := abs_buildRecurrenceArray_expTermStepFixed_sub_le B q_r q_acc r_mant hr_R m
  set T_m : ℤ := (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
  set r_q : ℝ := (r_mant : ℝ) * (2 : ℝ) ^ (-(q_r : ℤ))
  have hu_le : |r_q ^ m / (m.factorial : ℝ)| ≤ (2 : ℝ) ^ (2 * B) := by
    have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    rw [abs_div, abs_pow, abs_of_pos hfac_pos]
    have h1 : |r_q| ^ m / (m.factorial : ℝ) ≤ (B : ℝ) ^ m / (m.factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hr_R m) hfac_pos.le
    exact h1.trans ((Real.pow_div_factorial_le_exp (B : ℝ) (by positivity) m).trans
      (real_exp_nat_le_two_pow B))
  have hm_pow : (m : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) ≤ 1 := by
    have hm_lt : m < 2 ^ q_acc := lt_of_le_of_lt hm (Nat.lt_two_pow_self)
    have hm_r : (m : ℝ) ≤ (2 : ℝ) ^ q_acc := by exact_mod_cast (le_of_lt hm_lt)
    rw [zpow_neg, zpow_natCast]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ q_acc := by positivity
    calc (m : ℝ) * ((1 / 2 : ℝ) * ((2 : ℝ) ^ q_acc)⁻¹)
        ≤ (2 : ℝ) ^ q_acc * ((1 / 2 : ℝ) * ((2 : ℝ) ^ q_acc)⁻¹) :=
          mul_le_mul_of_nonneg_right hm_r (by positivity)
      _ = 1 / 2 := by field_simp [h2pos.ne']
      _ ≤ 1 := by norm_num
  have herr_le :
      (m : ℝ) * expRecGrowth B m * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))) ≤
        (2 : ℝ) ^ (2 * B) := by
    have hg := expRecGrowth_le_two_pow B m
    calc (m : ℝ) * expRecGrowth B m * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))
        = expRecGrowth B m * ((m : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))) := by ring
      _ ≤ (2 : ℝ) ^ (2 * B) * 1 :=
          mul_le_mul hg hm_pow (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * B) := mul_one _
  have htri := abs_sub_le ((T_m : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ)))
    (r_q ^ m / (m.factorial : ℝ)) 0
  rw [sub_zero, sub_zero] at htri
  have hTm_scaled : |(T_m : ℝ) * (2 : ℝ) ^ (-(q_acc : ℤ))| ≤ (2 : ℝ) ^ (2 * B + 1) := by
    have h2 : (2 : ℝ) ^ (2 * B) + (2 : ℝ) ^ (2 * B) = (2 : ℝ) ^ (2 * B + 1) := by
      rw [pow_succ]; ring
    linarith
  have hTm_R : |(T_m : ℝ)| ≤ (2 : ℝ) ^ (q_acc + 2 * B + 1) := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(q_acc : ℤ)) := zpow_pos (by norm_num) _
    rw [abs_mul, abs_of_pos h2pos, zpow_neg, zpow_natCast,
      ← div_eq_mul_inv, div_le_iff₀ (by positivity), ← pow_add,
      show 2 * B + 1 + q_acc = q_acc + 2 * B + 1 by omega] at hTm_scaled
    exact hTm_scaled
  exact_mod_cast hTm_R

theorem fitsSignedWord_buildRecurrenceArray_expTermStepFixed
    (B q_r q_acc : ℕ) (r_mant : ℤ)
    (hr : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r)
    {m w : ℕ} (hm : m ≤ q_acc) (hw : q_acc + 2 * B + 2 ≤ w) :
    FitsSignedWord w
      (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 := by
  unfold FitsSignedWord
  refine lt_of_le_of_lt (abs_buildRecurrenceArray_expTermStepFixed_le B q_r q_acc r_mant hr hm) ?_
  exact pow_lt_pow_right₀ (by decide) (by omega)

theorem abs_expTermArrayFixed_getD_le
    (B q_r q_acc N : ℕ) (r_mant : ℤ)
    (hr : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r)
    (hN : N ≤ q_acc) (m : ℕ) :
    |(expTermArrayFixed q_r q_acc N r_mant).getD m 0| ≤
      (2 : ℤ) ^ (q_acc + 2 * B + 1) := by
  by_cases hm : m ≤ N
  · change |(buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) N).1.getD m 0| ≤ _
    rw [getD_default_buildRecurrenceArray _ 0 (expTermStepFixed q_r r_mant) hm]
    exact abs_buildRecurrenceArray_expTermStepFixed_le B q_r q_acc r_mant hr (hm.trans hN)
  · change |(buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) N).1.getD m 0| ≤ _
    have hsz : (buildRecurrenceArray ((2 : ℤ) ^ q_acc)
        (expTermStepFixed q_r r_mant) N).1.size = N + 1 :=
      size_buildRecurrenceArray _ _ N
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none, abs_zero]
    positivity

theorem fitsSignedWord_of_abs_le_mul_two_pow {B q w : ℕ} {x : ℤ}
    (hx : |x| ≤ (B : ℤ) * (2 : ℤ) ^ q) (hw : q + B + 1 ≤ w) :
    FitsSignedWord w x := by
  unfold FitsSignedWord
  have hB : (B : ℤ) < (2 : ℤ) ^ B := by exact_mod_cast Nat.lt_two_pow_self
  have hlt : (B : ℤ) * (2 : ℤ) ^ q < (2 : ℤ) ^ (B + q) := by
    rw [pow_add]
    exact mul_lt_mul_of_pos_right hB (by positivity)
  exact lt_of_le_of_lt hx (lt_of_lt_of_le hlt
    (pow_le_pow_right₀ (by decide) (by omega)))

theorem expTermArrayFixedWithMul_eq_of_fitsSignedWord
    (smul : ℤ → ℤ → ℤ) (B q_r q_acc N w : ℕ) (r_mant : ℤ)
    (hr : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r)
    (hN : N ≤ q_acc)
    (hw_T : q_acc + 2 * B + 2 ≤ w)
    (hw_r : q_r + B + 1 ≤ w)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → smul x y = x * y) :
    expTermArrayFixedWithMul smul q_r q_acc N r_mant =
      expTermArrayFixed q_r q_acc N r_mant := by
  unfold expTermArrayFixed expTermArrayFixedWithMul
  congr 1
  refine buildRecurrenceArray_congr ((2 : ℤ) ^ q_acc)
    (expTermStepFixedWithMul smul q_r r_mant)
    (expTermStepFixed q_r r_mant) N (fun m hm => ?_)
  change roundDivInt
      (smul (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 r_mant)
      (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r) =
    roundDivInt
      ((buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 * r_mant)
      (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r)
  congr 1
  exact hsmul _ _
    (fitsSignedWord_buildRecurrenceArray_expTermStepFixed B q_r q_acc r_mant hr
      ((le_of_lt hm).trans hN) hw_T)
    (fitsSignedWord_of_abs_le_mul_two_pow hr hw_r)

theorem childScheduleBIn_le_pChildEll_of_not_isBaseLeaf {K p B_in : ℕ}
    (hleaf : ¬ isBaseLeaf K p = true) (hB : B_in ≤ p) :
    childScheduleBIn K p B_in ≤ pChildEll K p := by
  have hclog := clog_two_mul_pChildEll_add_four_le hleaf
  have hp := pChildEll_eq K p
  unfold childScheduleBIn
  omega

end IntMul
