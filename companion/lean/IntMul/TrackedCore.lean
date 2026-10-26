import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives
import IntMul.FastDFT
import IntMul.ComputableSchedule
import IntMul.ComputableCore

set_option backward.isDefEq.respectTransparency false

/-!
# Intrinsically Operation-Tracking Computable Integer & Bit-List Pipeline (`IntMul.TrackedCore`)

This module implements the bottom-up operation-tracking `CostM` execution of the computable
pure-integer sinc-Gaussian fractional-shift polynomial-transform (`syntheticFFT` in this
development) multiplication pipeline (Section 8 (`sec:lean`)):
1. Every fixed-point complex multiplication (`FixedComplex.mulRoundedWithTracked`,
   `FixedComplex.scaleRoundedWithTracked`) and every Step 1 blocked Kronecker Overlap-Add product
   (`kroneckerMatrixSpreadFixedWithMulTracked`) is driven by a bit-list sub-multiplier
   `subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)` (`signedMulFromTrackedBitMul`).
2. Step 3 cyclic bidiagonal deconvolution (`bidiagSweepFixedWithMulTracked`,
   `cyclicBidiagSolveFixedWithMulTracked`, `cyclicBidiagPrevSolveFixedWithMulTracked`) and Nyquist
   deconvolution (`nyquistColumnSolveFixedWithMulTracked`) hoist the column reciprocal division
   once per column (`invA_m`, `invC0_m`, `ratio_m`, `Z0`, `corr`), performing $O(1)$ bit-by-bit
   restoring divisions (`roundDivIntTracked`) and $O(t_1)$ fixed-point multiplications per column
   (Section 5.2 (`sec:solvers`)).
3. `computableNatMulBitsAuxTracked`, `computableNatMulBitsTracked`, and `computableNatMulTracked`
   execute bit-list chunk slicing (`sliceBitChunkFnTracked`), bit-list Kronecker slot
   packing/unpacking (`packSignedSlotsBitsTracked`, `unpackSignedSlotsBitsTracked`), and single-pass
   base-$2^b$ carry-save bit emission (`carrySaveEmitBitsTracked`) at **every** recursion depth
   $d \in \{2, 1, 0\}$, terminating at `binaryShiftAddMulBitsTracked` at depth $d = 0$ with **zero**
   wide-integer `natChunkFnTracked` or `evalBaseChunksTracked` conversions.
-/

namespace IntMul

open scoped BigOperators ComplexConjugate

/-- Whenever `bitMulTracked` agrees with bit-encoded natural multiplication on `< 2^w` operands,
`signedMulFromTrackedBitMul w bitMulTracked` agrees with exact signed multiplication on `w`-bit
signed words. -/
theorem signedMulFromTrackedBitMul_fst_of_bitMul_eq
    (w : ℕ) (bitMulTracked : List Bool → List Bool → CostM (List Bool))
    (hmul : ∀ a b : ℕ, a < 2 ^ w → b < 2 ^ w →
      (bitMulTracked (encodeNatBits w a) (encodeNatBits w b)).1 = encodeNatBits (2 * w) (a * b))
    {x y : ℤ} (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    (signedMulFromTrackedBitMul w bitMulTracked x y).1 = x * y := by
  rw [signedMulFromTrackedBitMul_fst]
  refine signedMulFromNatMul_eq_mul_of_fitsSignedWord
    (natMulFromBitMul w (fun xs ys => (bitMulTracked xs ys).1))
    (fun a ha b hb => ?_) hx hy
  unfold natMulFromBitMul
  dsimp only
  rw [hmul a b ha hb, List.take_of_length_le (by simp)]
  have hprod : a * b < 2 ^ (2 * w) := by
    rw [Nat.two_mul, pow_add]
    exact Nat.mul_lt_mul'' ha hb
  exact decodeNatBits_encodeNatBits (2 * w) (a * b) hprod

/-- Operation-tracking fixed-point complex multiplication in $\tilde{\mathbb{C}}_q$ parameterized by
`smulTracked : ℤ → ℤ → CostM ℤ`. -/
def FixedComplex.mulRoundedWithTracked (smulTracked : ℤ → ℤ → CostM ℤ) {q : ℕ}
    (z w : FixedComplex q) : CostM (FixedComplex q) :=
  let p1 := smulTracked z.re w.re
  let p2 := smulTracked z.im w.im
  let p3 := smulTracked z.re w.im
  let p4 := smulTracked z.im w.re
  let r1 := roundShiftIntTracked (p1.1 - p2.1) q
  let r2 := roundShiftIntTracked (p3.1 + p4.1) q
  (⟨r1.1, r2.1⟩, p1.2 + p2.2 + p3.2 + p4.2 + r1.2 + r2.2 + 4 * q + 4)

@[simp]
theorem FixedComplex.mulRoundedWithTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) {q : ℕ}
    (z w : FixedComplex q) :
    (FixedComplex.mulRoundedWithTracked smulTracked z w).1 =
      FixedComplex.mulRoundedWith (fun x y => (smulTracked x y).1) z w := rfl

theorem FixedComplex.mulRoundedWithTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ) {q : ℕ}
    (z w : FixedComplex q) (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M) :
    (FixedComplex.mulRoundedWithTracked smulTracked z w).2 ≤ 4 * M + 6 * q + 8 := by
  unfold FixedComplex.mulRoundedWithTracked
  have h1 := hM z.re w.re
  have h2 := hM z.im w.im
  have h3 := hM z.re w.im
  have h4 := hM z.im w.re
  simp only [roundShiftIntTracked_snd]
  omega

/-- Operation-tracking fixed-point real-mantissa times complex multiplication in $\tilde{\mathbb{C}}_q$
parameterized by `smulTracked : ℤ → ℤ → CostM ℤ`. -/
def FixedComplex.scaleRoundedWithTracked (smulTracked : ℤ → ℤ → CostM ℤ) {q : ℕ}
    (m : ℤ) (z : FixedComplex q) : CostM (FixedComplex q) :=
  let p1 := smulTracked m z.re
  let p2 := smulTracked m z.im
  let r1 := roundShiftIntTracked p1.1 q
  let r2 := roundShiftIntTracked p2.1 q
  (⟨r1.1, r2.1⟩, p1.2 + p2.2 + r1.2 + r2.2 + 2)

@[simp]
theorem FixedComplex.scaleRoundedWithTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) {q : ℕ}
    (m : ℤ) (z : FixedComplex q) :
    (FixedComplex.scaleRoundedWithTracked smulTracked m z).1 =
      FixedComplex.scaleRoundedWith (fun x y => (smulTracked x y).1) m z := rfl

theorem FixedComplex.scaleRoundedWithTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ) {q : ℕ}
    (m : ℤ) (z : FixedComplex q) (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M) :
    (FixedComplex.scaleRoundedWithTracked smulTracked m z).2 ≤ 2 * M + 2 * q + 6 := by
  unfold FixedComplex.scaleRoundedWithTracked
  have h1 := hM m z.re
  have h2 := hM m z.im
  simp only [roundShiftIntTracked_snd]
  omega

/-- Operation-tracking fixed-point complex division by a scalar mantissa `b : ℤ` via bit-by-bit
restoring division `roundDivIntTracked`. -/
def divScalarFixedTracked (q1 q2 : ℕ) (z : FixedComplex q1) (b : ℤ) :
    CostM (FixedComplex q2) :=
  let r1 := roundDivIntTracked (6 * (q1 + q2)) (z.re * (2 : ℤ) ^ q2) b
  let r2 := roundDivIntTracked (6 * (q1 + q2)) (z.im * (2 : ℤ) ^ q2) b
  (⟨r1.1, r2.1⟩, r1.2 + r2.2 + 2 * q2 + 2)

theorem divScalarFixedTracked_fst {q1 q2 : ℕ} {z : FixedComplex q1} (b : ℤ)
    (hz : WordWidthBounds (6 * q1 + 5 * q2) z) :
    (divScalarFixedTracked q1 q2 z b).1 = divScalarFixed q1 q2 z b := by
  unfold divScalarFixedTracked divScalarFixed
  have hre : FitsSignedWord (6 * (q1 + q2)) (z.re * (2 : ℤ) ^ q2) :=
    (hz.1.mul_two_pow q2).mono (by omega)
  have him : FitsSignedWord (6 * (q1 + q2)) (z.im * (2 : ℤ) ^ q2) :=
    (hz.2.mul_two_pow q2).mono (by omega)
  simp [roundDivIntTracked_fst b hre, roundDivIntTracked_fst b him]

theorem divScalarFixedTracked_snd_le (q1 q2 : ℕ) (z : FixedComplex q1) (b : ℤ) :
    (divScalarFixedTracked q1 q2 z b).2 ≤
      2 * (5 * (6 * (q1 + q2)) * (6 * (q1 + q2)) + 20 * (6 * (q1 + q2)) + 13) + 2 * q2 + 2 := by
  unfold divScalarFixedTracked
  dsimp only
  have h1 := roundDivIntTracked_snd_le (6 * (q1 + q2)) (z.re * (2 : ℤ) ^ q2) b
  have h2 := roundDivIntTracked_snd_le (6 * (q1 + q2)) (z.im * (2 : ℤ) ^ q2) b
  linarith

/-- Operation-tracking fixed-point complex division by a natural number `n : ℕ` via bit-by-bit
restoring division `roundDivIntTracked`. -/
def divNatFixedTracked {q : ℕ} (z : FixedComplex q) (n : ℕ) : CostM (FixedComplex q) :=
  let r1 := roundDivIntTracked (10 * q) z.re n
  let r2 := roundDivIntTracked (10 * q) z.im n
  (⟨r1.1, r2.1⟩, r1.2 + r2.2 + 2)

theorem divNatFixedTracked_fst {q : ℕ} {z : FixedComplex q} (n : ℕ)
    (hz : WordWidthBounds (10 * q) z) :
    (divNatFixedTracked z n).1 = divNatFixed z n := by
  unfold divNatFixedTracked divNatFixed
  simp [roundDivIntTracked_fst (n : ℤ) hz.1, roundDivIntTracked_fst (n : ℤ) hz.2]

theorem divNatFixedTracked_snd_le {q : ℕ} (z : FixedComplex q) (n : ℕ) :
    (divNatFixedTracked z n).2 ≤
      2 * (5 * (10 * q) * (10 * q) + 20 * (10 * q) + 13) + 2 := by
  unfold divNatFixedTracked
  dsimp only
  have h1 := roundDivIntTracked_snd_le (10 * q) z.re n
  have h2 := roundDivIntTracked_snd_le (10 * q) z.im n
  linarith

/-- Operation-tracking negacyclic monomial shift in $\tilde{\mathbb{C}}_q[y]/(y^r + 1)$. Charges `2 * q + 4` bit operations for reading/negating the real and imaginary
words of width $q + 2$. -/
def negacyclicShiftFixedTracked {r q : ℕ} (s : ℤ) (P : Fin r → FixedComplex q) (k2 : Fin r) :
    CostM (FixedComplex q) :=
  (negacyclicShiftFixed s P k2, 2 * q + 4)

@[simp]
theorem negacyclicShiftFixedTracked_fst {r q : ℕ} (s : ℤ) (P : Fin r → FixedComplex q) (k2 : Fin r) :
    (negacyclicShiftFixedTracked s P k2).1 = negacyclicShiftFixed s P k2 := rfl

@[simp]
theorem negacyclicShiftFixedTracked_snd {r q : ℕ} (s : ℤ) (P : Fin r → FixedComplex q) (k2 : Fin r) :
    (negacyclicShiftFixedTracked s P k2).2 = 2 * q + 4 := rfl

/-- Operation-tracking radix-2 synthetic butterfly upper output. -/
def butterflyPlusFixedTracked {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    CostM (FixedComplex q) :=
  let sh := negacyclicShiftFixedTracked s V k2
  let ad := FixedComplex.addTracked (U k2) sh.1
  let hf := FixedComplex.halfRoundedTracked ad.1
  (hf.1, sh.2 + ad.2 + hf.2)

@[simp]
theorem butterflyPlusFixedTracked_fst {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    (butterflyPlusFixedTracked s U V k2).1 = butterflyPlusFixed s U V k2 := rfl

@[simp]
theorem butterflyPlusFixedTracked_snd {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    (butterflyPlusFixedTracked s U V k2).2 = 6 * q + 12 := by
  simp only [butterflyPlusFixedTracked, negacyclicShiftFixedTracked_snd,
    FixedComplex.addTracked_snd, FixedComplex.halfRoundedTracked_snd]
  ring

/-- Operation-tracking radix-2 synthetic butterfly lower output. -/
def butterflyMinusFixedTracked {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    CostM (FixedComplex q) :=
  let sh := negacyclicShiftFixedTracked s V k2
  let sb := FixedComplex.subTracked (U k2) sh.1
  let hf := FixedComplex.halfRoundedTracked sb.1
  (hf.1, sh.2 + sb.2 + hf.2)

@[simp]
theorem butterflyMinusFixedTracked_fst {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    (butterflyMinusFixedTracked s U V k2).1 = butterflyMinusFixed s U V k2 := rfl

@[simp]
theorem butterflyMinusFixedTracked_snd {r q : ℕ} (s : ℤ) (U V : Fin r → FixedComplex q) (k2 : Fin r) :
    (butterflyMinusFixedTracked s U V k2).2 = 6 * q + 12 := by
  simp only [butterflyMinusFixedTracked, negacyclicShiftFixedTracked_snd,
    FixedComplex.subTracked_snd, FixedComplex.halfRoundedTracked_snd]
  ring

/-- Operation-tracking $k_1$-stage radix-2 polynomial-transform (`radix2SyntheticFFTFixedTracked`)
butterfly network over $\tilde{\mathbb{C}}_q[y]/(y^r + 1)$ (Lemma 3.5 (`lem:syn-fft`)).
Explicitly materializes and charges for the even/odd deinterleaving pass (`U_in`, `V_in`) at each of
the $k_1$ butterfly stages. -/
def radix2SyntheticFFTFixedTracked {r q : ℕ} :
    (k1 : ℕ) → (c1 : ℕ) → (Fin (2 ^ k1) → Fin r → FixedComplex q) →
      CostM (Fin (2 ^ k1) → Fin r → FixedComplex q)
  | 0, _c1, P => (P, 2)
  | m + 1, c1, P =>
    let U_in := memoizeFin2Tracked (fun (j : Fin (2 ^ m)) (k2 : Fin r) =>
      (P (evenSubIndex m j) k2, 2 * q + 4))
    let V_in := memoizeFin2Tracked (fun (j : Fin (2 ^ m)) (k2 : Fin r) =>
      (P (oddSubIndex m j) k2, 2 * q + 4))
    let U := radix2SyntheticFFTFixedTracked m (2 * c1) U_in.1
    let V := radix2SyntheticFFTFixedTracked m (2 * c1) V_in.1
    let stage := memoizeFin2Tracked (fun (v1 : Fin (2 ^ (m + 1))) (k2 : Fin r) =>
      let u : Fin (2 ^ m) := ⟨v1.val % (2 ^ m), Nat.mod_lt _ (by positivity)⟩
      let s : ℤ := 2 * (c1 : ℤ) * (u.val : ℤ)
      if v1.val < 2 ^ m then
        butterflyPlusFixedTracked s (U.1 u) (V.1 u) k2
      else
        butterflyMinusFixedTracked s (U.1 u) (V.1 u) k2)
    (stage.1, U_in.2 + V_in.2 + U.2 + V.2 + stage.2)

@[simp]
theorem radix2SyntheticFFTFixedTracked_fst {r q : ℕ} :
    ∀ (k1 c1 : ℕ) (P : Fin (2 ^ k1) → Fin r → FixedComplex q),
      (radix2SyntheticFFTFixedTracked k1 c1 P).1 = radix2SyntheticFFTFixed k1 c1 P
  | 0, _c1, _P => rfl
  | m + 1, c1, P => by
    unfold radix2SyntheticFFTFixedTracked radix2SyntheticFFTFixed
    simp only [memoizeFin2Tracked_fst, memoizeFin2_eq,
      radix2SyntheticFFTFixedTracked_fst m (2 * c1)]
    funext v1 k2
    split_ifs <;> simp

theorem wordWidthBounds_negacyclicShiftFixed {r q W : ℕ} (s : ℤ)
    (P : Fin r → FixedComplex q) (hP : ∀ j : Fin r, WordWidthBounds W (P j)) (k2 : Fin r) :
    WordWidthBounds W (negacyclicShiftFixed s P k2) := by
  unfold negacyclicShiftFixed
  split_ifs
  · exact hP _
  · exact ⟨(hP _).1.neg, (hP _).2.neg⟩

theorem wordWidthBounds_radix2SyntheticFFTFixed {r q W : ℕ} (_hW : 1 ≤ W) :
    ∀ (k1 c1 : ℕ) (P : Fin (2 ^ k1) → Fin r → FixedComplex q),
      (∀ j1 k2, WordWidthBounds W (P j1 k2)) →
      ∀ (v1 : Fin (2 ^ k1)) (k2 : Fin r),
        WordWidthBounds W (radix2SyntheticFFTFixed k1 c1 P v1 k2)
  | 0, _, P, hP, v1, k2 => hP v1 k2
  | m + 1, c1, P, hP, v1, k2 => by
    unfold radix2SyntheticFFTFixed
    simp only [memoizeFin2_eq]
    have hU := wordWidthBounds_radix2SyntheticFFTFixed _hW m (2 * c1)
      (fun j => P (evenSubIndex m j)) (fun j1 j2 => hP _ _)
      ⟨v1.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩ k2
    have hV := wordWidthBounds_negacyclicShiftFixed
      (2 * (c1 : ℤ) * ((v1.val % 2 ^ m : ℕ) : ℤ))
      (radix2SyntheticFFTFixed m (2 * c1) (fun j => P (oddSubIndex m j))
        ⟨v1.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩)
      (wordWidthBounds_radix2SyntheticFFTFixed _hW m (2 * c1)
        (fun j => P (oddSubIndex m j)) (fun j1 j2 => hP _ _)
        ⟨v1.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩) k2
    split_ifs
    · exact ⟨FitsSignedWord.halfRounded_add hU.1 hV.1,
             FitsSignedWord.halfRounded_add hU.2 hV.2⟩
    · exact ⟨FitsSignedWord.halfRounded_sub hU.1 hV.1,
             FitsSignedWord.halfRounded_sub hU.2 hV.2⟩

theorem radix2SyntheticFFTFixedTracked_snd_le {r q : ℕ} :
    ∀ (k1 c1 : ℕ) (P : Fin (2 ^ k1) → Fin r → FixedComplex q),
      (radix2SyntheticFFTFixedTracked k1 c1 P).2 ≤
        k1 * (2 ^ k1) * (r * (8 * q + 18)) + 5 * (2 ^ k1) - 3
  | 0, _c1, _P => by simp [radix2SyntheticFFTFixedTracked]
  | m + 1, c1, P => by
    rw [radix2SyntheticFFTFixedTracked]
    have hU_in : (memoizeFin2Tracked (fun (j : Fin (2 ^ m)) (k2 : Fin r) =>
        (P (evenSubIndex m j) k2, 2 * q + 4))).2 ≤
        (2 ^ m) * (r * (2 * q + 4)) + (2 ^ m) * r + 1 :=
      memoizeFin2Tracked_snd_le _ (2 * q + 4) (fun _ _ => le_rfl)
    have hV_in : (memoizeFin2Tracked (fun (j : Fin (2 ^ m)) (k2 : Fin r) =>
        (P (oddSubIndex m j) k2, 2 * q + 4))).2 ≤
        (2 ^ m) * (r * (2 * q + 4)) + (2 ^ m) * r + 1 :=
      memoizeFin2Tracked_snd_le _ (2 * q + 4) (fun _ _ => le_rfl)
    have hU := radix2SyntheticFFTFixedTracked_snd_le m (2 * c1)
      (memoizeFin2Tracked (fun (j : Fin (2 ^ m)) (k2 : Fin r) =>
        (P (evenSubIndex m j) k2, 2 * q + 4))).1
    have hV := radix2SyntheticFFTFixedTracked_snd_le m (2 * c1)
      (memoizeFin2Tracked (fun (j : Fin (2 ^ m)) (k2 : Fin r) =>
        (P (oddSubIndex m j) k2, 2 * q + 4))).1
    refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add hU_in hV_in) hU) hV)
      (memoizeFin2Tracked_snd_le _ (6 * q + 12)
        (fun v1 k2 => by dsimp only; split_ifs <;> simp))) ?_
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    set B : ℕ := r * (8 * q + 18)
    have hstage_eq :
        2 * ((2 ^ m) * (r * (2 * q + 4)) + (2 ^ m) * r) +
          (2 ^ (m + 1)) * (r * (6 * q + 12)) + (2 ^ (m + 1)) * r =
          (2 ^ (m + 1)) * B := by
      dsimp [B]; rw [hpow]; ring
    have hident : 2 * (m * 2 ^ m * B) + 2 ^ (m + 1) * B = (m + 1) * 2 ^ (m + 1) * B := by
      rw [hpow]; ring
    omega

/-- Operation-tracking $m$-stage Cooley–Tukey radix-2 butterfly FFT over `FixedComplex q`
parameterized by `smulTracked : ℤ → ℤ → CostM ℤ`.
Explicitly materializes and charges for the even/odd deinterleaving pass (`E_in`, `O_in`) at each of
the $m$ butterfly stages. -/
def radix2FFT1DFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) (K q : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    (m : ℕ) → m ≤ K → (Fin (2 ^ m) → FixedComplex q) → CostM (Fin (2 ^ m) → FixedComplex q)
  | 0, _, x => (x, 2)
  | m + 1, hm, x =>
    let E_in := memoizeFinTracked (fun j : Fin (2 ^ m) => (x (evenSubIndex m j), 2 * q + 4))
    let O_in := memoizeFinTracked (fun j : Fin (2 ^ m) => (x (oddSubIndex m j), 2 * q + 4))
    let E := radix2FFT1DFixedWithMulTracked smulTracked K q leafTwiddles m
      (Nat.le_of_succ_le hm) E_in.1
    let O := radix2FFT1DFixedWithMulTracked smulTracked K q leafTwiddles m
      (Nat.le_of_succ_le hm) O_in.1
    let stage := memoizeFinTracked (fun u : Fin (2 ^ (m + 1)) =>
      let v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
      let wIdx : Fin (2 ^ K) := ⟨v.val * 2 ^ (K - (m + 1)), mul_two_pow_sub_lt hm v⟩
      let w : FixedComplex q := leafTwiddles wIdx
      let t := FixedComplex.mulRoundedWithTracked smulTracked w (O.1 v)
      let bfly := if u.val < 2 ^ m then
          FixedComplex.addTracked (E.1 v) t.1
        else
          FixedComplex.subTracked (E.1 v) t.1
      let hf := FixedComplex.halfRoundedTracked bfly.1
      (hf.1, t.2 + bfly.2 + hf.2))
    (stage.1, E_in.2 + O_in.2 + E.2 + O.2 + stage.2)

@[simp]
theorem radix2FFT1DFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) (K q : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q) :
    ∀ (m : ℕ) (hm : m ≤ K) (x : Fin (2 ^ m) → FixedComplex q),
      (radix2FFT1DFixedWithMulTracked smulTracked K q leafTwiddles m hm x).1 =
        radix2FFT1DFixedWithMul (fun x y => (smulTracked x y).1) K q leafTwiddles m hm x
  | 0, _, _ => rfl
  | m + 1, hm, x => by
    unfold radix2FFT1DFixedWithMulTracked radix2FFT1DFixedWithMul
    simp only [memoizeFinTracked_fst, memoizeFin_eq,
      radix2FFT1DFixedWithMulTracked_fst smulTracked K q leafTwiddles m]
    funext u
    split_ifs <;> simp <;> rfl

theorem radix2FFT1DFixedWithMul_eq_and_bounds (smul : ℤ → ℤ → ℤ) (K q W0 W : ℕ)
    (hsmul : ∀ x y : ℤ, FitsSignedWord W x → FitsSignedWord W y → smul x y = x * y)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (htw : ∀ u : Fin (2 ^ K), WordWidthBounds (q + 2) (leafTwiddles u))
    (hw_tw : q + 2 ≤ W) :
    ∀ (m : ℕ) (hm : m ≤ K) (x : Fin (2 ^ m) → FixedComplex q),
      (∀ j : Fin (2 ^ m), WordWidthBounds W0 (x j)) →
      1 ≤ W0 →
      W0 + 4 * m ≤ W →
      radix2FFT1DFixedWithMul smul K q leafTwiddles m hm x =
        radix2FFT1DFixed K q leafTwiddles m hm x ∧
      ∀ u : Fin (2 ^ m),
        WordWidthBounds (W0 + 4 * m) (radix2FFT1DFixed K q leafTwiddles m hm x u)
  | 0, _, x, hx, _, _ => ⟨rfl, fun u => by simpa [radix2FFT1DFixed, radix2FFT1DFixedWithMul] using hx u⟩
  | m + 1, hm, x, hx, hW0, hmW => by
    have hm' : m ≤ K := Nat.le_of_succ_le hm
    have hmW' : W0 + 4 * m ≤ W := by omega
    have ihE := radix2FFT1DFixedWithMul_eq_and_bounds smul K q W0 W hsmul leafTwiddles htw hw_tw
      m hm' (fun j => x (evenSubIndex m j)) (fun j => hx _) hW0 hmW'
    have ihO := radix2FFT1DFixedWithMul_eq_and_bounds smul K q W0 W hsmul leafTwiddles htw hw_tw
      m hm' (fun j => x (oddSubIndex m j)) (fun j => hx _) hW0 hmW'
    have hstep_eq :
        radix2FFT1DFixedWithMul smul K q leafTwiddles (m + 1) hm x =
          radix2FFT1DFixed K q leafTwiddles (m + 1) hm x := by
      unfold radix2FFT1DFixed radix2FFT1DFixedWithMul
      simp only [memoizeFin_eq]
      rw [ihE.1, ihO.1,
        radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl),
        radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl)]
      funext u
      set v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
      set wIdx : Fin (2 ^ K) := ⟨v.val * 2 ^ (K - (m + 1)), mul_two_pow_sub_lt hm v⟩
      have hmul_eq :
          FixedComplex.mulRoundedWith smul (leafTwiddles wIdx)
            (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => x (oddSubIndex m j)) v) =
          FixedComplex.mulRounded (leafTwiddles wIdx)
            (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => x (oddSubIndex m j)) v) :=
        FixedComplex.mulRoundedWith_eq_mulRounded_of_bounds smul hsmul
          ((htw wIdx).mono hw_tw) ((ihO.2 v).mono hmW')
      rw [hmul_eq, FixedComplex.mulRoundedWith_eq_mulRounded (· * ·) (fun _ _ => rfl)]
    refine ⟨hstep_eq, fun u => ?_⟩
    unfold radix2FFT1DFixed radix2FFT1DFixedWithMul
    simp only [memoizeFin_eq]
    rw [radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl),
      radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl),
      FixedComplex.mulRoundedWith_eq_mulRounded (· * ·) (fun _ _ => rfl)]
    set v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
    set wIdx : Fin (2 ^ K) := ⟨v.val * 2 ^ (K - (m + 1)), mul_two_pow_sub_lt hm v⟩
    have ht_bds :
        WordWidthBounds (W0 + 4 * (m + 1))
          (FixedComplex.mulRounded (leafTwiddles wIdx)
            (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => x (oddSubIndex m j)) v)) := by
      have h1 := WordWidthBounds.mulRounded_sub_left (htw wIdx) (ihO.2 v)
      exact h1.mono (by omega)
    have hE_bds :
        WordWidthBounds (W0 + 4 * (m + 1))
          (radix2FFT1DFixed K q leafTwiddles m hm' (fun j => x (evenSubIndex m j)) v) :=
      (ihE.2 v).mono (by omega)
    split_ifs
    · exact ⟨FitsSignedWord.halfRounded_add hE_bds.1 ht_bds.1,
             FitsSignedWord.halfRounded_add hE_bds.2 ht_bds.2⟩
    · exact ⟨FitsSignedWord.halfRounded_sub hE_bds.1 ht_bds.1,
             FitsSignedWord.halfRounded_sub hE_bds.2 ht_bds.2⟩

theorem radix2FFT1DFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ) (K q : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M) :
    ∀ (m : ℕ) (hm : m ≤ K) (x : Fin (2 ^ m) → FixedComplex q),
      (radix2FFT1DFixedWithMulTracked smulTracked K q leafTwiddles m hm x).2 ≤
        m * (2 ^ m) * (4 * M + 12 * q + 22) + 5 * (2 ^ m) - 3
  | 0, _, _ => by simp [radix2FFT1DFixedWithMulTracked]
  | m + 1, hm, x => by
    rw [radix2FFT1DFixedWithMulTracked]
    have hE_in : (memoizeFinTracked (fun j : Fin (2 ^ m) => (x (evenSubIndex m j), 2 * q + 4))).2 ≤
        (2 ^ m) * (2 * q + 4) + 2 ^ m + 1 :=
      memoizeFinTracked_snd_le _ (2 * q + 4) (fun _ => le_rfl)
    have hO_in : (memoizeFinTracked (fun j : Fin (2 ^ m) => (x (oddSubIndex m j), 2 * q + 4))).2 ≤
        (2 ^ m) * (2 * q + 4) + 2 ^ m + 1 :=
      memoizeFinTracked_snd_le _ (2 * q + 4) (fun _ => le_rfl)
    have hE := radix2FFT1DFixedWithMulTracked_snd_le smulTracked K q leafTwiddles M hM m
      (Nat.le_of_succ_le hm)
      (memoizeFinTracked (fun j : Fin (2 ^ m) => (x (evenSubIndex m j), 2 * q + 4))).1
    have hO := radix2FFT1DFixedWithMulTracked_snd_le smulTracked K q leafTwiddles M hM m
      (Nat.le_of_succ_le hm)
      (memoizeFinTracked (fun j : Fin (2 ^ m) => (x (oddSubIndex m j), 2 * q + 4))).1
    refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add hE_in hO_in) hE) hO)
      (memoizeFinTracked_snd_le _ (4 * M + 10 * q + 16) (fun u => by
        dsimp only
        have ht := FixedComplex.mulRoundedWithTracked_snd_le smulTracked
          (leafTwiddles ⟨(u.val % 2 ^ m) * 2 ^ (K - (m + 1)),
            mul_two_pow_sub_lt hm ⟨u.val % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩⟩)
          ((radix2FFT1DFixedWithMulTracked smulTracked K q leafTwiddles m
            (Nat.le_of_succ_le hm)
            (memoizeFinTracked (fun j : Fin (2 ^ m) => (x (oddSubIndex m j), 2 * q + 4))).1).1
            ⟨u.val % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩) M hM
        split_ifs <;> simp only [FixedComplex.addTracked_snd, FixedComplex.subTracked_snd,
          FixedComplex.halfRoundedTracked_snd] <;> omega))) ?_
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := Nat.pow_succ'
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    set B : ℕ := 4 * M + 12 * q + 22
    have hstage_eq :
        2 * ((2 ^ m) * (2 * q + 4) + 2 ^ m) +
          (2 ^ (m + 1)) * (4 * M + 10 * q + 16) + 2 ^ (m + 1) = (2 ^ (m + 1)) * B := by
      dsimp [B]; rw [hpow]; ring
    have hident : 2 * (m * 2 ^ m * B) + 2 ^ (m + 1) * B = (m + 1) * 2 ^ (m + 1) * B := by
      rw [hpow]; ring
    omega

/-- Operation-tracking $O(K \cdot 2^K)$ Cooley–Tukey radix-2 leaf FFT over `FixedComplex`
parameterized by `smulTracked : ℤ → ℤ → CostM ℤ`. -/
def baseRadix2FFTFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    CostM (Fin (2 ^ K) → FixedComplex (p + 2)) :=
  let qBase := qBaseEll K p
  let xBase := memoizeFinTracked (fun j : Fin (2 ^ K) =>
    FixedComplex.rescaleTracked qBase (xFixed j))
  let yBase := radix2FFT1DFixedWithMulTracked smulTracked K qBase leafTwiddles K (le_refl K) xBase.1
  let out := memoizeFinTracked (fun u : Fin (2 ^ K) =>
    FixedComplex.rescaleTracked (p + 2) (yBase.1 u))
  (out.1, xBase.2 + yBase.2 + out.2)

@[simp]
theorem baseRadix2FFTFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    (baseRadix2FFTFixedWithMulTracked smulTracked K p leafTwiddles xFixed).1 =
      baseRadix2FFTFixedWithMul (fun x y => (smulTracked x y).1) K p leafTwiddles xFixed := by
  unfold baseRadix2FFTFixedWithMulTracked baseRadix2FFTFixedWithMul
  simp

/-- Operation-tracking Nyquist mode alternating sum in `FixedComplex (qChildEll K p)`. -/
def nyquistModeSumFixedTracked (K p : ℕ) (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    CostM (FixedComplex (qChildEll K p)) :=
  let S_re := sumFinIntTracked (p + 2 + k2Ell K) (fun j2 : Fin (rEll K) =>
    (altSign j2.val *
      (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩).re,
      p + 4))
  let S_im := sumFinIntTracked (p + 2 + k2Ell K) (fun j2 : Fin (rEll K) =>
    (altSign j2.val *
      (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩).im,
      p + 4))
  let res := FixedComplex.rescaleTracked (qChildEll K p)
    (⟨-S_im.1, S_re.1⟩ : FixedComplex (p + 2 + k2Ell K))
  (res.1, S_re.2 + S_im.2 + res.2 + p + 4)

@[simp]
theorem nyquistModeSumFixedTracked_fst (K p : ℕ)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    (nyquistModeSumFixedTracked K p xFixed).1 = nyquistModeSumFixed K p xFixed := by
  unfold nyquistModeSumFixedTracked nyquistModeSumFixed
  simp

/-- Operation-tracking single step of the non-Nyquist cyclic bidiagonal recurrence sweep. -/
def bidiagSweepStepFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) (qWork : ℕ) (ratio_m : ℤ)
    (B_scaledFixed : ℕ → FixedComplex qWork) (s : ℕ)
    (st : FixedComplex qWork × ℤ) : CostM (FixedComplex qWork × ℤ) :=
  let sc := FixedComplex.scaleRoundedWithTracked smulTracked ratio_m st.1
  let ad := FixedComplex.addTracked (B_scaledFixed s) sc.1
  let pr := smulTracked ratio_m st.2
  let sh := roundShiftIntTracked pr.1 qWork
  ((ad.1, sh.1), sc.2 + ad.2 + pr.2 + sh.2 + 2)

@[simp]
theorem bidiagSweepStepFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) (qWork : ℕ)
    (ratio_m : ℤ) (B_scaledFixed : ℕ → FixedComplex qWork) (s : ℕ)
    (st : FixedComplex qWork × ℤ) :
    (bidiagSweepStepFixedWithMulTracked smulTracked qWork ratio_m B_scaledFixed s st).1 =
      bidiagSweepStepFixedWithMul (fun x y => (smulTracked x y).1) qWork ratio_m B_scaledFixed s st := rfl

theorem abs_buildRecurrenceArray_bidiagSweepStepFixed_le (qWork W_B : ℕ) (ratio_m : ℤ)
    (hratio : |ratio_m| ≤ (2 : ℤ) ^ qWork)
    (B_scaledFixed : ℕ → FixedComplex qWork)
    (hB : ∀ s : ℕ, WordWidthBounds W_B (B_scaledFixed s)) :
    ∀ s : ℕ,
      let st := (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
        (bidiagSweepStepFixed qWork ratio_m B_scaledFixed) s).2
      |st.1.re| ≤ (s : ℤ) * (2 : ℤ) ^ W_B ∧
      |st.1.im| ≤ (s : ℤ) * (2 : ℤ) ^ W_B ∧
      |st.2| ≤ (2 : ℤ) ^ qWork
  | 0 => ⟨by simp [buildRecurrenceArray]; rfl, by simp [buildRecurrenceArray]; rfl, by simp [buildRecurrenceArray]⟩
  | s + 1 => by
    have ih := abs_buildRecurrenceArray_bidiagSweepStepFixed_le qWork W_B ratio_m hratio
      B_scaledFixed hB s
    set st := (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
      (bidiagSweepStepFixed qWork ratio_m B_scaledFixed) s).2
    change |(B_scaledFixed s + FixedComplex.scaleRounded ratio_m st.1).re| ≤ _ ∧
      |(B_scaledFixed s + FixedComplex.scaleRounded ratio_m st.1).im| ≤ _ ∧
      |roundShiftInt (ratio_m * st.2) qWork| ≤ _
    have hBs_re : |(B_scaledFixed s).re| ≤ (2 : ℤ) ^ W_B :=
      le_of_lt ((fitsSignedWord_iff_abs_lt W_B _).mp (hB s).1)
    have hBs_im : |(B_scaledFixed s).im| ≤ (2 : ℤ) ^ W_B :=
      le_of_lt ((fitsSignedWord_iff_abs_lt W_B _).mp (hB s).2)
    have hsc_re : |roundShiftInt (ratio_m * st.1.re) qWork| ≤ (s : ℤ) * (2 : ℤ) ^ W_B :=
      (abs_roundShiftInt_mul_le_of_abs_le_two_pow hratio).trans ih.1
    have hsc_im : |roundShiftInt (ratio_m * st.1.im) qWork| ≤ (s : ℤ) * (2 : ℤ) ^ W_B :=
      (abs_roundShiftInt_mul_le_of_abs_le_two_pow hratio).trans ih.2.1
    have hsc_2 : |roundShiftInt (ratio_m * st.2) qWork| ≤ (2 : ℤ) ^ qWork :=
      (abs_roundShiftInt_mul_le_of_abs_le_two_pow hratio).trans ih.2.2
    have htri_re := abs_add_le (B_scaledFixed s).re (roundShiftInt (ratio_m * st.1.re) qWork)
    have htri_im := abs_add_le (B_scaledFixed s).im (roundShiftInt (ratio_m * st.1.im) qWork)
    have hstep : (2 : ℤ) ^ W_B + (s : ℤ) * (2 : ℤ) ^ W_B = ((s + 1 : ℕ) : ℤ) * (2 : ℤ) ^ W_B := by
      push_cast; ring
    refine ⟨?_, ?_, hsc_2⟩
    · exact htri_re.trans (by linarith)
    · exact htri_im.trans (by linarith)

/-- Operation-tracking single-pass $O(t_1)$ bidiagonal recurrence sweep:
Computes the column reciprocal `invA_m` and ratio `ratio_m` **once per column** (at working precision
`qWork = q + 9`) and scales each entry `Y_seq s` via `FixedComplex.scaleRoundedWithTracked smulTracked`,
using only 4 restoring divisions per column instead of $2 t_1 + 3$. -/
def bidiagSweepFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) (t1 q : ℕ) (a_max a_min : ℤ)
    (Y_seq : ℕ → FixedComplex q) (idx : Fin t1 → ℕ) : CostM (Fin t1 → FixedComplex q) :=
  let qWork : ℕ := q + 9
  let invA_m := roundDivIntTracked (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) a_max
  let ratio_m := roundDivIntTracked (6 * (q + qWork)) (-a_min * (2 : ℤ) ^ qWork) a_max
  let B_scaledFixed := memoizeRangeTracked t1 (fun s =>
    let rs := FixedComplex.rescaleTracked qWork (Y_seq s)
    let sc := FixedComplex.scaleRoundedWithTracked smulTracked invA_m.1 rs.1
    (sc.1, rs.2 + sc.2))
  let recSweep := buildRecurrenceArrayTracked ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    (bidiagSweepStepFixedWithMulTracked smulTracked qWork ratio_m.1 B_scaledFixed.1) t1
  let trajArr := recSweep.1.1
  let lastSt := recSweep.1.2
  let Z0 := divScalarFixedTracked qWork qWork lastSt.1 ((2 : ℤ) ^ qWork - lastSt.2)
  let out := memoizeFinTracked (fun u1 : Fin t1 =>
    let st := trajArr.getD (idx u1) ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    let sc := FixedComplex.scaleRoundedWithTracked smulTracked st.2 Z0.1
    let ad := FixedComplex.addTracked st.1 sc.1
    let rs := FixedComplex.rescaleTracked q ad.1
    (rs.1, sc.2 + ad.2 + rs.2 + 2))
  (out.1, invA_m.2 + ratio_m.2 + B_scaledFixed.2 + recSweep.2 + Z0.2 + out.2 + 4)

theorem bidiagSweepFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) (t1 q : ℕ)
    (a_max a_min : ℤ) (Y_seq : ℕ → FixedComplex q) (idx : Fin t1 → ℕ)
    (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q) (hidx : ∀ u1 : Fin t1, idx u1 ≤ t1)
    (ha_nn : 0 ≤ a_min) (ha_le : a_max ≥ a_min)
    (ha_fits : FitsSignedWord (2 * q) a_min)
    (hY : ∀ s : ℕ, WordWidthBounds (3 * q) (Y_seq s))
    (hsmul : ∀ x y : ℤ, FitsSignedWord (10 * q) x → FitsSignedWord (10 * q) y →
      (smulTracked x y).1 = x * y) :
    (bidiagSweepFixedWithMulTracked smulTracked t1 q a_max a_min Y_seq idx).1 =
      bidiagSweepFixed t1 q a_max a_min Y_seq idx := by
  unfold bidiagSweepFixedWithMulTracked bidiagSweepFixed
  set qWork : ℕ := q + 9
  have hpow_fits : FitsSignedWord (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) :=
    (FitsSignedWord.two_pow (q + qWork)).mono (by omega)
  have hinv_eq :
      (roundDivIntTracked (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) a_max).1 =
        roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max :=
    roundDivIntTracked_fst a_max hpow_fits
  set invA := roundDivInt ((2 : ℤ) ^ (q + qWork)) a_max
  have hinv_bds : FitsSignedWord (3 * q) invA :=
    (FitsSignedWord.roundDivInt a_max hpow_fits).mono (by omega)
  have hrs_bds : ∀ s : ℕ, WordWidthBounds (4 * q) (FixedComplex.rescale qWork (Y_seq s)) := by
    intro s
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 9 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY s).1.mul_two_pow 9).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY s).2.mul_two_pow 9).mono (by omega)
  have hnum_fits : FitsSignedWord (6 * (q + qWork)) (-a_min * (2 : ℤ) ^ qWork) :=
    (ha_fits.neg.mul_two_pow qWork).mono (by omega)
  have hratio_eq :
      (roundDivIntTracked (6 * (q + qWork)) (-a_min * (2 : ℤ) ^ qWork) a_max).1 =
        roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max :=
    roundDivIntTracked_fst a_max hnum_fits
  have hratio_le : |roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max| ≤ (2 : ℤ) ^ qWork := by
    by_cases hmax0 : a_max = 0
    · simp [hmax0, roundDivInt]
    · apply abs_roundDivInt_le_of_abs_le_mul (by positivity)
      rw [abs_mul, abs_neg, abs_of_nonneg ha_nn, abs_of_nonneg (by omega : 0 ≤ a_max),
        abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ qWork), mul_comm ((2 : ℤ) ^ qWork) a_max]
      exact mul_le_mul_of_nonneg_right ha_le (by positivity)
  have hratio_fits : FitsSignedWord (10 * q) (roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max) := by
    rw [fitsSignedWord_iff_abs_lt]
    exact lt_of_le_of_lt hratio_le (pow_lt_pow_right₀ (by decide) (by omega))
  have hB_eq :
      (memoizeRangeTracked t1 (fun s =>
        let rs := FixedComplex.rescaleTracked qWork (Y_seq s)
        let sc := FixedComplex.scaleRoundedWithTracked smulTracked invA rs.1
        (sc.1, rs.2 + sc.2))).1 =
        memoizeRange t1 (fun s => FixedComplex.scaleRounded invA (FixedComplex.rescale qWork (Y_seq s))) := by
    funext s
    simp only [memoizeRangeTracked_fst, memoizeRange_eq, FixedComplex.rescaleTracked_fst,
      FixedComplex.scaleRoundedWithTracked_fst]
    exact FixedComplex.scaleRoundedWith_eq_scaleRounded_of_bounds _ hsmul
      (hinv_bds.mono (by omega)) ((hrs_bds s).mono (by omega))
  set B_sc := memoizeRange t1 (fun s =>
    FixedComplex.scaleRounded invA (FixedComplex.rescale qWork (Y_seq s)))
  have hB_bds : ∀ s : ℕ, WordWidthBounds (6 * q) (B_sc s) := by
    intro s
    dsimp [B_sc]
    rw [memoizeRange_eq]
    have hqW : qWork = q + 9 := rfl
    exact ⟨(FitsSignedWord.roundShiftInt_sub (w := 6 * q - 1) (k := qWork)
              ((hinv_bds.mul (hrs_bds s).1).mono (by omega))).mono (by omega),
           (FitsSignedWord.roundShiftInt_sub (w := 6 * q - 1) (k := qWork)
              ((hinv_bds.mul (hrs_bds s).2).mono (by omega))).mono (by omega)⟩
  set ratio_val := roundDivInt (-a_min * (2 : ℤ) ^ qWork) a_max
  have hst_bds : ∀ s ≤ t1,
      let st := (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
        (bidiagSweepStepFixed qWork ratio_val B_sc) s).2
      WordWidthBounds (7 * q + 1) st.1 ∧ FitsSignedWord (qWork + 1) st.2 := by
    intro s hs
    have habs := abs_buildRecurrenceArray_bidiagSweepStepFixed_le qWork (6 * q)
      ratio_val hratio_le B_sc hB_bds s
    have hs_pow : (s : ℤ) * (2 : ℤ) ^ (6 * q) < (2 : ℤ) ^ (7 * q + 1) := by
      have hs_le : (s : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast (hs.trans ht1)
      calc (s : ℤ) * (2 : ℤ) ^ (6 * q)
          ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ (6 * q) := mul_le_mul_of_nonneg_right hs_le (by positivity)
        _ = (2 : ℤ) ^ (7 * q) := by rw [← pow_add, show q + 6 * q = 7 * q by ring]
        _ < (2 : ℤ) ^ (7 * q + 1) := pow_lt_pow_right₀ (by decide) (by omega)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [fitsSignedWord_iff_abs_lt]; exact lt_of_le_of_lt habs.1 hs_pow
    · rw [fitsSignedWord_iff_abs_lt]; exact lt_of_le_of_lt habs.2.1 hs_pow
    · rw [fitsSignedWord_iff_abs_lt]
      exact lt_of_le_of_lt habs.2.2 (pow_lt_pow_right₀ (by decide) (by omega))
  have hrec_eq :
      buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
        (fun s st => (bidiagSweepStepFixedWithMulTracked smulTracked qWork ratio_val B_sc s st).1) t1 =
      buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
        (bidiagSweepStepFixed qWork ratio_val B_sc) t1 := by
    refine buildRecurrenceArray_congr _ _ _ t1 (fun s hs => ?_)
    have hbds := hst_bds s (le_of_lt hs)
    set st := (buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
      (bidiagSweepStepFixed qWork ratio_val B_sc) s).2
    simp only [bidiagSweepStepFixedWithMulTracked_fst]
    change bidiagSweepStepFixedWithMul (fun x y => (smulTracked x y).1) qWork ratio_val B_sc s st =
      bidiagSweepStepFixed qWork ratio_val B_sc s st
    unfold bidiagSweepStepFixed bidiagSweepStepFixedWithMul
    dsimp only
    have hsc : FixedComplex.scaleRoundedWith (fun x y => (smulTracked x y).1) ratio_val st.1 =
        FixedComplex.scaleRounded ratio_val st.1 :=
      FixedComplex.scaleRoundedWith_eq_scaleRounded_of_bounds _ hsmul hratio_fits
        (hbds.1.mono (by omega))
    have hpr : (smulTracked ratio_val st.2).1 = ratio_val * st.2 :=
      hsmul _ _ hratio_fits (hbds.2.mono (by omega))
    rw [hsc, hpr]
  simp only [memoizeFinTracked_fst, memoizeFin_eq, buildRecurrenceArrayTracked_fst,
    hinv_eq, hratio_eq, hB_eq]
  change (fun u1 : Fin t1 => _) = _
  rw [hrec_eq]
  set recVal := buildRecurrenceArray ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)
    (bidiagSweepStepFixed qWork ratio_val B_sc) t1
  have hlast_bds : WordWidthBounds (7 * q + 1) recVal.2.1 := (hst_bds t1 (le_refl t1)).1
  have hZ0_eq :
      (divScalarFixedTracked qWork qWork recVal.2.1 ((2 : ℤ) ^ qWork - recVal.2.2)).1 =
        divScalarFixed qWork qWork recVal.2.1 ((2 : ℤ) ^ qWork - recVal.2.2) :=
    divScalarFixedTracked_fst _ (hlast_bds.mono (by omega))
  rw [hZ0_eq]
  set Z0_val := divScalarFixed qWork qWork recVal.2.1 ((2 : ℤ) ^ qWork - recVal.2.2)
  have hZ0_bds : WordWidthBounds (10 * q) Z0_val := by
    exact ⟨(FitsSignedWord.roundDivInt _ (hlast_bds.1.mul_two_pow qWork)).mono (by omega),
           (FitsSignedWord.roundDivInt _ (hlast_bds.2.mul_two_pow qWork)).mono (by omega)⟩
  funext u1
  simp only [FixedComplex.rescaleTracked_fst, FixedComplex.addTracked_fst,
    FixedComplex.scaleRoundedWithTracked_fst]
  have hst_u1 : FitsSignedWord (10 * q)
      (recVal.1.getD (idx u1) ((0 : FixedComplex qWork), (2 : ℤ) ^ qWork)).2 := by
    rw [getD_default_buildRecurrenceArray _ _ _ (hidx u1)]
    exact ((hst_bds (idx u1) (hidx u1)).2).mono (by omega)
  rw [FixedComplex.scaleRoundedWith_eq_scaleRounded_of_bounds _ hsmul hst_u1 hZ0_bds]
  rfl

/-- Operation-tracking Step 3 forward-shift cyclic bidiagonal column solver. -/
def cyclicBidiagSolveFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) {t1 q : ℕ} [NeZero t1]
    (a b : ℤ) (Y : Fin t1 → FixedComplex q) : CostM (Fin t1 → FixedComplex q) :=
  have ht1 : 0 < t1 := NeZero.pos t1
  if b ≤ a then
    bidiagSweepFixedWithMulTracked smulTracked t1 q a b
      (fun s => Y ⟨(t1 - 1 - s % t1) % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => (t1 - u1.val) % t1)
  else
    bidiagSweepFixedWithMulTracked smulTracked t1 q b a
      (fun s => Y ⟨s % t1, Nat.mod_lt _ ht1⟩)
      (fun u1 => u1.val)

theorem cyclicBidiagSolveFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) {t1 q : ℕ}
    [NeZero t1] (a b : ℤ) (Y : Fin t1 → FixedComplex q)
    (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (ha_fits : FitsSignedWord (2 * q) a) (hb_fits : FitsSignedWord (2 * q) b)
    (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (hsmul : ∀ x y : ℤ, FitsSignedWord (10 * q) x → FitsSignedWord (10 * q) y →
      (smulTracked x y).1 = x * y) :
    (cyclicBidiagSolveFixedWithMulTracked smulTracked a b Y).1 =
      cyclicBidiagSolveFixed a b Y := by
  have ht1_pos : 0 < t1 := NeZero.pos t1
  unfold cyclicBidiagSolveFixedWithMulTracked cyclicBidiagSolveFixed
  split_ifs with hba
  · exact bidiagSweepFixedWithMulTracked_fst smulTracked t1 q a b _ _ hq ht1
      (fun u1 => le_of_lt (Nat.mod_lt _ ht1_pos)) hb_nn hba hb_fits (fun s => hY _) hsmul
  · exact bidiagSweepFixedWithMulTracked_fst smulTracked t1 q b a _ _ hq ht1
      (fun u1 => le_of_lt u1.isLt) ha_nn (by omega) ha_fits (fun s => hY _) hsmul

/-- Operation-tracking Step 3 backward-shift cyclic bidiagonal column solver. -/
def cyclicBidiagPrevSolveFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) {t1 q : ℕ}
    [NeZero t1] (a b : ℤ) (Y : Fin t1 → FixedComplex q) : CostM (Fin t1 → FixedComplex q) :=
  cyclicBidiagSolveFixedWithMulTracked smulTracked b a (fun m => Y (cyclicNext m))

theorem cyclicBidiagPrevSolveFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) {t1 q : ℕ}
    [NeZero t1] (a b : ℤ) (Y : Fin t1 → FixedComplex q)
    (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b)
    (ha_fits : FitsSignedWord (2 * q) a) (hb_fits : FitsSignedWord (2 * q) b)
    (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (hsmul : ∀ x y : ℤ, FitsSignedWord (10 * q) x → FitsSignedWord (10 * q) y →
      (smulTracked x y).1 = x * y) :
    (cyclicBidiagPrevSolveFixedWithMulTracked smulTracked a b Y).1 =
      cyclicBidiagPrevSolveFixed a b Y := by
  unfold cyclicBidiagPrevSolveFixedWithMulTracked cyclicBidiagPrevSolveFixed
  exact cyclicBidiagSolveFixedWithMulTracked_fst smulTracked b a (fun m => Y (cyclicNext m))
    hq ht1 hb_nn ha_nn hb_fits ha_fits (fun m => hY _) hsmul

theorem abs_buildRecurrenceArray_nyquistOpenChainStep_le {t1 qWork W_B : ℕ}
    (B_scaledFixed : Fin t1 → FixedComplex qWork)
    (hB : ∀ m : Fin t1, WordWidthBounds W_B (B_scaledFixed m)) :
    ∀ k : ℕ,
      let st := (buildRecurrenceArray (0 : FixedComplex qWork)
        (nyquistOpenChainStep B_scaledFixed) k).2
      |st.re| ≤ (k : ℤ) * (2 : ℤ) ^ W_B ∧ |st.im| ≤ (k : ℤ) * (2 : ℤ) ^ W_B
  | 0 => ⟨by simp [buildRecurrenceArray]; rfl, by simp [buildRecurrenceArray]; rfl⟩
  | k + 1 => by
    have ih := abs_buildRecurrenceArray_nyquistOpenChainStep_le B_scaledFixed hB k
    set st := (buildRecurrenceArray (0 : FixedComplex qWork)
      (nyquistOpenChainStep B_scaledFixed) k).2
    have ih1 : |st.re| ≤ (k : ℤ) * (2 : ℤ) ^ W_B := ih.1
    have ih2 : |st.im| ≤ (k : ℤ) * (2 : ℤ) ^ W_B := ih.2
    change |(nyquistOpenChainStep B_scaledFixed k st).re| ≤ ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ W_B ∧
      |(nyquistOpenChainStep B_scaledFixed k st).im| ≤ ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ W_B
    unfold nyquistOpenChainStep
    split_ifs with hk
    · change |(B_scaledFixed ⟨k + 1, hk⟩).re - st.re| ≤ ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ W_B ∧
        |(B_scaledFixed ⟨k + 1, hk⟩).im - st.im| ≤ ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ W_B
      have hBk_re : |(B_scaledFixed ⟨k + 1, hk⟩).re| ≤ (2 : ℤ) ^ W_B :=
        le_of_lt ((fitsSignedWord_iff_abs_lt W_B _).mp (hB ⟨k + 1, hk⟩).1)
      have hBk_im : |(B_scaledFixed ⟨k + 1, hk⟩).im| ≤ (2 : ℤ) ^ W_B :=
        le_of_lt ((fitsSignedWord_iff_abs_lt W_B _).mp (hB ⟨k + 1, hk⟩).2)
      have htri_re := abs_sub (B_scaledFixed ⟨k + 1, hk⟩).re st.re
      have htri_im := abs_sub (B_scaledFixed ⟨k + 1, hk⟩).im st.im
      have hstep : (2 : ℤ) ^ W_B + (k : ℤ) * (2 : ℤ) ^ W_B = ((k + 1 : ℕ) : ℤ) * (2 : ℤ) ^ W_B := by
        push_cast; ring
      exact ⟨by linarith, by linarith⟩
    · simp; constructor <;> positivity

/-- Operation-tracking column-level $O(t_1)$ 2-pass open-chain + cyclic rank-1 correction Nyquist
solver.
Charges `16 * qWork + 4` per step in `recChain` and `sumFinIntTracked (8 * qWork)` for `altRe`/`altIm`
to match the proven `WordWidthBounds (8 * q + 1)` on `zpartArr`. -/
def nyquistColumnSolveFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) {t1 q : ℕ} (a : ℤ)
    (Y : Fin t1 → FixedComplex q) (altFixed : FixedComplex q) : CostM (Fin t1 → FixedComplex q) :=
  let qWork : ℕ := q + 4
  let invC0_m := roundDivIntTracked (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) a
  let B_scaledFixed := memoizeFinTracked (fun m : Fin t1 =>
    let rs := FixedComplex.rescaleTracked qWork (Y m)
    let sc := FixedComplex.scaleRoundedWithTracked smulTracked invC0_m.1 rs.1
    (sc.1, rs.2 + sc.2))
  let recChain := buildRecurrenceArrayTracked (0 : FixedComplex qWork)
    (fun k prev => (nyquistOpenChainStep B_scaledFixed.1 k prev, 16 * qWork + 4)) t1
  let zpartArr := recChain.1.1
  let altRe := sumFinIntTracked (8 * qWork) (fun m : Fin t1 =>
    (altSign m.val * (zpartArr.getD m.val 0).re, 8 * qWork + 2))
  let altIm := sumFinIntTracked (8 * qWork) (fun m : Fin t1 =>
    (altSign m.val * (zpartArr.getD m.val 0).im, 8 * qWork + 2))
  let altPart : FixedComplex qWork := ⟨altRe.1, altIm.1⟩
  let altWork := FixedComplex.rescaleTracked qWork altFixed
  let diff := FixedComplex.subTracked altWork.1 altPart
  let corr := divNatFixedTracked diff.1 t1
  let out := memoizeFinTracked (fun u1 : Fin t1 =>
    let ad := FixedComplex.addTracked (zpartArr.getD u1.val 0)
      ⟨altSign u1.val * corr.1.re, altSign u1.val * corr.1.im⟩
    let rs := FixedComplex.rescaleTracked q ad.1
    (rs.1, ad.2 + rs.2 + 16 * qWork + 4))
  (out.1,
    invC0_m.2 + B_scaledFixed.2 + recChain.2 + altRe.2 + altIm.2 +
    altWork.2 + diff.2 + corr.2 + out.2 + 4)

theorem nyquistColumnSolveFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) {t1 q : ℕ}
    (a : ℤ) (Y : Fin t1 → FixedComplex q) (altFixed : FixedComplex q)
    (hq : 14 ≤ q) (ht1 : t1 ≤ 2 ^ q)
    (hY : ∀ m : Fin t1, WordWidthBounds (3 * q) (Y m))
    (halt : WordWidthBounds (3 * q) altFixed)
    (hsmul : ∀ x y : ℤ, FitsSignedWord (10 * q) x → FitsSignedWord (10 * q) y →
      (smulTracked x y).1 = x * y) :
    (nyquistColumnSolveFixedWithMulTracked smulTracked a Y altFixed).1 =
      nyquistColumnSolveFixed a Y altFixed := by
  unfold nyquistColumnSolveFixedWithMulTracked nyquistColumnSolveFixed
  set qWork : ℕ := q + 4
  have hpow_fits : FitsSignedWord (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) :=
    (FitsSignedWord.two_pow (q + qWork)).mono (by omega)
  have hinv_eq :
      (roundDivIntTracked (q + qWork + 2) ((2 : ℤ) ^ (q + qWork)) a).1 =
        roundDivInt ((2 : ℤ) ^ (q + qWork)) a :=
    roundDivIntTracked_fst a hpow_fits
  set invC0 := roundDivInt ((2 : ℤ) ^ (q + qWork)) a
  have hinv_bds : FitsSignedWord (3 * q) invC0 :=
    (FitsSignedWord.roundDivInt a hpow_fits).mono (by omega)
  have hrs_bds : ∀ m : Fin t1, WordWidthBounds (4 * q) (FixedComplex.rescale qWork (Y m)) := by
    intro m
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 4 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY m).1.mul_two_pow 4).mono (by omega)
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((hY m).2.mul_two_pow 4).mono (by omega)
  set B_sc : Fin t1 → FixedComplex qWork := fun m =>
    FixedComplex.scaleRounded invC0 (FixedComplex.rescale qWork (Y m))
  have hB_fn :
      (fun m : Fin t1 =>
        (FixedComplex.scaleRoundedWithTracked smulTracked invC0
          (FixedComplex.rescale qWork (Y m))).1) = B_sc := by
    funext m
    rw [FixedComplex.scaleRoundedWithTracked_fst]
    exact FixedComplex.scaleRoundedWith_eq_scaleRounded_of_bounds _ hsmul
      (hinv_bds.mono (by omega)) ((hrs_bds m).mono (by omega))
  have hB_bds : ∀ m : Fin t1, WordWidthBounds (7 * q) (B_sc m) := by
    intro m
    exact ⟨((hinv_bds.mul (hrs_bds m).1).roundShiftInt qWork).mono (by omega),
           ((hinv_bds.mul (hrs_bds m).2).roundShiftInt qWork).mono (by omega)⟩
  have hzpart_bds : ∀ m : Fin t1,
      WordWidthBounds (8 * q + 1)
        ((buildRecurrenceArray (0 : FixedComplex qWork)
          (nyquistOpenChainStep B_sc) t1).1.getD m.val 0) := by
    intro m
    rw [getD_default_buildRecurrenceArray _ _ _ (le_of_lt m.isLt)]
    have habs := abs_buildRecurrenceArray_nyquistOpenChainStep_le B_sc hB_bds m.val
    have hm_pow : (m.val : ℤ) * (2 : ℤ) ^ (7 * q) < (2 : ℤ) ^ (8 * q + 1) := by
      have hm_le : (m.val : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast (le_of_lt m.isLt).trans ht1
      calc (m.val : ℤ) * (2 : ℤ) ^ (7 * q)
          ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ (7 * q) := mul_le_mul_of_nonneg_right hm_le (by positivity)
        _ = (2 : ℤ) ^ (8 * q) := by rw [← pow_add, show q + 7 * q = 8 * q by ring]
        _ < (2 : ℤ) ^ (8 * q + 1) := pow_lt_pow_right₀ (by decide) (by omega)
    exact ⟨(fitsSignedWord_iff_abs_lt _ _).mpr (lt_of_le_of_lt habs.1 hm_pow),
           (fitsSignedWord_iff_abs_lt _ _).mpr (lt_of_le_of_lt habs.2 hm_pow)⟩
  set zArr := (buildRecurrenceArray (0 : FixedComplex qWork) (nyquistOpenChainStep B_sc) t1).1
  have halt_re_bds :
      FitsSignedWord (9 * q + 1) (∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).re) := by
    have h := fitsSignedWord_sum_fin ht1 (fun m : Fin t1 => altSign m.val * (zArr.getD m.val 0).re)
      (fun m => by
        rcases altSign_eq_one_or_neg_one m.val with h1 | h1
        · rw [h1, one_mul]; exact (hzpart_bds m).1
        · rw [h1, neg_one_mul]; exact (hzpart_bds m).1.neg)
    exact h.mono (by omega)
  have halt_im_bds :
      FitsSignedWord (9 * q + 1) (∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).im) := by
    have h := fitsSignedWord_sum_fin ht1 (fun m : Fin t1 => altSign m.val * (zArr.getD m.val 0).im)
      (fun m => by
        rcases altSign_eq_one_or_neg_one m.val with h1 | h1
        · rw [h1, one_mul]; exact (hzpart_bds m).2
        · rw [h1, neg_one_mul]; exact (hzpart_bds m).2.neg)
    exact h.mono (by omega)
  have haltWork_bds : WordWidthBounds (4 * q) (FixedComplex.rescale qWork altFixed) := by
    have hsub : q - qWork = 0 := by omega
    have hsub2 : qWork - q = 4 := by omega
    refine ⟨?_, ?_⟩
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((halt.1.mul_two_pow 4).mono (by omega))
    · simp only [FixedComplex.rescale, hsub, hsub2, roundShiftInt_zero]
      exact ((halt.2.mul_two_pow 4).mono (by omega))
  have hdiff_bds :
      WordWidthBounds (10 * qWork)
        ((FixedComplex.rescale qWork altFixed).sub
          (⟨∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).re,
            ∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).im⟩ : FixedComplex qWork)) :=
    ⟨(FitsSignedWord.sub (haltWork_bds.1.mono (by omega)) halt_re_bds).mono (by omega),
     (FitsSignedWord.sub (haltWork_bds.2.mono (by omega)) halt_im_bds).mono (by omega)⟩
  simp only [memoizeFinTracked_fst, memoizeFin_eq, buildRecurrenceArrayTracked_fst,
    sumFinIntTracked_fst, FixedComplex.rescaleTracked_fst, FixedComplex.subTracked_fst,
    FixedComplex.addTracked_fst, hinv_eq]
  rw [hB_fn]
  change (fun u1 : Fin t1 =>
      FixedComplex.rescale q
        ((zArr.getD u1.val 0).add
          ⟨altSign u1.val *
              (divNatFixedTracked
                ((FixedComplex.rescale qWork altFixed).sub
                  ⟨∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).re,
                    ∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).im⟩) t1).1.re,
            altSign u1.val *
              (divNatFixedTracked
                ((FixedComplex.rescale qWork altFixed).sub
                  ⟨∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).re,
                    ∑ m : Fin t1, altSign m.val * (zArr.getD m.val 0).im⟩) t1).1.im⟩)) = _
  rw [divNatFixedTracked_fst t1 hdiff_bds]
  rfl

/-- Operation-tracking 2D filter tap table memoizer `memoizeFilterTapTracked`: evaluates `f j1 d`
once for each `(j1, d)` with `|d| ≤ m1` and accumulates all computation and array-write steps
(`memoizeFilterTapTracked`). -/
def memoizeFilterTapTracked {t1 : ℕ} (m1 : ℕ) (f : Fin t1 → ℤ → CostM ℤ) :
    CostM (Fin t1 → ℤ → ℤ) :=
  let tbl := memoizeFin2 (fun (j1 : Fin t1) (k : Fin (2 * m1 + 1)) =>
    f j1 ((k.val : ℤ) - (m1 : ℤ)))
  (memoizeFilterTap m1 (fun j1 d => (f j1 d).1),
    (∑ j1 : Fin t1, ∑ k : Fin (2 * m1 + 1), (tbl j1 k).2) + t1 * (2 * m1 + 1) + 1)

@[simp]
theorem memoizeFilterTapTracked_fst {t1 : ℕ} (m1 : ℕ) (f : Fin t1 → ℤ → CostM ℤ) :
    (memoizeFilterTapTracked m1 f).1 = memoizeFilterTap m1 (fun j1 d => (f j1 d).1) := rfl

@[simp]
theorem memoizeFilterTapTracked_snd {t1 : ℕ} (m1 : ℕ) (f : Fin t1 → ℤ → CostM ℤ) :
    (memoizeFilterTapTracked m1 f).2 =
      (∑ j1 : Fin t1, ∑ k : Fin (2 * m1 + 1), (f j1 ((k.val : ℤ) - (m1 : ℤ))).2) +
        t1 * (2 * m1 + 1) + 1 := by
  simp [memoizeFilterTapTracked]

theorem memoizeFilterTapTracked_snd_le {t1 : ℕ} (m1 : ℕ) (f : Fin t1 → ℤ → CostM ℤ)
    (c : ℕ) (hc : ∀ j1 d, (f j1 d).2 ≤ c) :
    (memoizeFilterTapTracked m1 f).2 ≤ t1 * ((2 * m1 + 1) * c) + t1 * (2 * m1 + 1) + 1 := by
  rw [memoizeFilterTapTracked_snd]
  have hsum :
      ∑ j1 : Fin t1, ∑ k : Fin (2 * m1 + 1), (f j1 ((k.val : ℤ) - (m1 : ℤ))).2 ≤
        ∑ _j1 : Fin t1, ∑ _k : Fin (2 * m1 + 1), c :=
    Finset.sum_le_sum (fun j1 _ => Finset.sum_le_sum (fun k _ => hc j1 _))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- Operation-tracking pure-integer fixed-point mantissa of $\ln 2$. -/
def approxLogTwoFixedTracked (w S : ℕ) : CostM ℤ :=
  let q_acc : ℕ := S + (S + 2)
  sumRangeTracked w (S + 2) (fun i =>
    roundDivIntTracked (w + q_acc + 2) ((2 : ℤ) ^ (q_acc - (i + 1))) ((i + 1 : ℕ) : ℤ))

@[simp]
theorem approxLogTwoFixedTracked_fst (w S : ℕ) :
    (approxLogTwoFixedTracked w S).1 = approxLogTwoFixed S := by
  unfold approxLogTwoFixedTracked approxLogTwoFixed approxLogTwoTermFixed
  simp only [sumRangeTracked_fst]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact roundDivIntTracked_fst _
    ((FitsSignedWord.two_pow (S + (S + 2) - (i + 1))).mono (by omega))

/-- Operation-tracking pure-integer recurrence array for $(1/k)^{2m+1}$. -/
def arctanInvPowArrayFixedTracked (w k q_acc N : ℕ) : CostM (Array ℤ) :=
  let init := roundDivIntTracked (w + q_acc + 2) ((2 : ℤ) ^ q_acc) (k : ℤ)
  let recArr := buildRecurrenceArrayTracked init.1
    (fun _m P_m => roundDivIntTracked (w + q_acc + 2) P_m ((k * k : ℕ) : ℤ)) N
  (recArr.1.1, init.2 + recArr.2 + 2)

@[simp]
theorem arctanInvPowArrayFixedTracked_fst (w k q_acc N : ℕ) :
    (arctanInvPowArrayFixedTracked w k q_acc N).1 = arctanInvPowArrayFixed k q_acc N := by
  unfold arctanInvPowArrayFixedTracked arctanInvPowArrayFixed
  have hinit_fits : FitsSignedWord (w + q_acc + 2) ((2 : ℤ) ^ q_acc) :=
    (FitsSignedWord.two_pow q_acc).mono (by omega)
  have hinit :
      (roundDivIntTracked (w + q_acc + 2) ((2 : ℤ) ^ q_acc) (k : ℤ)).1 =
        roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ) :=
    roundDivIntTracked_fst (k : ℤ) hinit_fits
  simp only [buildRecurrenceArrayTracked_fst, hinit]
  congr 1
  refine buildRecurrenceArray_congr _ _ _ N (fun m _ => ?_)
  exact roundDivIntTracked_fst ((k * k : ℕ) : ℤ)
    ((fitsSignedWord_buildRecurrenceArray_arctanInvPowStepFixed k q_acc m).mono (by omega))

/-- Operation-tracking pure-integer fixed-point mantissa of $\arctan(1/k)$. -/
def arctanInvTaylorFixedTracked (w N k : ℕ) : CostM ℤ :=
  let q_acc : ℕ := 4 * N + 6
  let arr := arctanInvPowArrayFixedTracked w k q_acc N
  let s := sumRangeTracked w (N + 1) (fun m =>
    let d := roundDivIntTracked (w + q_acc + 2) (arr.1.getD m 0) ((2 * m + 1 : ℕ) : ℤ)
    (altSign m * d.1, d.2 + 2))
  (s.1, arr.2 + s.2 + 2)

@[simp]
theorem arctanInvTaylorFixedTracked_fst (w N k : ℕ) :
    (arctanInvTaylorFixedTracked w N k).1 = arctanInvTaylorFixed N k := by
  unfold arctanInvTaylorFixedTracked arctanInvTaylorFixed
  simp only [sumRangeTracked_fst, arctanInvPowArrayFixedTracked_fst]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [roundDivIntTracked_fst ((2 * m + 1 : ℕ) : ℤ)
    ((fitsSignedWord_arctanInvPowArrayFixed_getD k (4 * N + 6) N m).mono (by omega))]

/-- Operation-tracking pure-integer Machin-like fixed-point mantissa of $\pi$. -/
def approxPiFixedTracked (w S : ℕ) : CostM ℤ :=
  let a2 := arctanInvTaylorFixedTracked w (S + 3) 2
  let a3 := arctanInvTaylorFixedTracked w (S + 3) 3
  (4 * (a2.1 + a3.1), a2.2 + a3.2 + w + 4)

@[simp]
theorem approxPiFixedTracked_fst (w S : ℕ) :
    (approxPiFixedTracked w S).1 = approxPiFixed S := by
  unfold approxPiFixedTracked approxPiFixed
  simp

/-- Operation-tracking pure-integer fixed-point square root via bit-by-bit restoring binary square
root `binaryRestoringSqrtRegTracked`. Charges `sq.2 + 2 * w + k + 4` to cover both the `2 * w` bits of `num` and the
`k`-bit shift. -/
def approxSqrtFixedTracked (w k : ℕ) (num : ℤ) : CostM ℤ :=
  let sq := binaryRestoringSqrtRegTracked w ((max 0 num).toNat / 2 ^ k)
  ((sq.1.1 : ℤ), sq.2 + 2 * w + k + 4)

theorem approxSqrtFixedTracked_fst {w k : ℕ} {num : ℤ}
    (h : (max 0 num).toNat / 2 ^ k < 4 ^ w) :
    (approxSqrtFixedTracked w k num).1 = approxSqrtFixed k num := by
  unfold approxSqrtFixedTracked approxSqrtFixed
  simp [binaryRestoringSqrtRegTracked_fst_fst h]

/-- Operation-tracking single-pass $O(N)$ pure-integer Taylor power-factorial recurrence array. -/
def expTermArrayFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ)
    (w q_r q_acc N : ℕ) (r_mant : ℤ) : CostM (Array ℤ) :=
  let recArr := buildRecurrenceArrayTracked ((2 : ℤ) ^ q_acc)
    (fun m T_m =>
      let prod := smulTracked T_m r_mant
      let div := roundDivIntTracked (2 * w) prod.1 (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r)
      (div.1, prod.2 + div.2 + 2)) N
  (recArr.1.1, recArr.2 + 2)

theorem expTermArrayFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ)
    (B w q_r q_acc N : ℕ) (r_mant : ℤ)
    (hr : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r)
    (hN : N ≤ q_acc)
    (hw_T : q_acc + 2 * B + 2 ≤ w)
    (hw_r : q_r + B + 1 ≤ w)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → (smulTracked x y).1 = x * y) :
    (expTermArrayFixedWithMulTracked smulTracked w q_r q_acc N r_mant).1 =
      expTermArrayFixed q_r q_acc N r_mant := by
  unfold expTermArrayFixedWithMulTracked expTermArrayFixed expTermArrayFixedWithMul
  simp only [buildRecurrenceArrayTracked_fst]
  congr 1
  have hr_fits : FitsSignedWord w r_mant := fitsSignedWord_of_abs_le_mul_two_pow hr hw_r
  refine buildRecurrenceArray_congr ((2 : ℤ) ^ q_acc) _
    (expTermStepFixed q_r r_mant) N (fun m hm => ?_)
  have hT_fits : FitsSignedWord w
      (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 :=
    fitsSignedWord_buildRecurrenceArray_expTermStepFixed B q_r q_acc r_mant hr
      ((le_of_lt hm).trans hN) hw_T
  rw [hsmul _ _ hT_fits hr_fits,
    roundDivIntTracked_fst _ ((hT_fits.mul hr_fits).mono (by omega))]
  rfl

/-- Operation-tracking pure-integer fixed-point unit root approximation.
Explicitly charges `5 * w * w + 20 * w + 13` for the `w`-bit modular reduction `num % (den : ℤ)`. -/
def expTwoPiIFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ) (w q : ℕ)
    (piFixed : ℤ) (num : ℤ) (den : ℕ) : CostM (FixedComplex q) :=
  let S : ℕ := q + 10
  let q_pi : ℕ := 4 * (S + 3) + 6
  let N : ℕ := 4 * 10 + S + 1
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  if den = 0 then (⟨0, 0⟩, 2)
  else
    let numMod : ℤ := num % (den : ℤ)
    let prodPi := smulTracked piFixed numMod
    let θNum : ℤ := 2 * prodPi.1
    let θDen : ℤ := (den : ℤ) * (2 : ℤ) ^ q_pi
    let r_mant := roundDivIntTracked (2 * w + q_r + 2) (θNum * (2 : ℤ) ^ q_r) θDen
    let arr := expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant.1
    let reSum := sumRangeTracked w (M + 1) (fun m => (iPowRe m * arr.1.getD m 0, 2))
    let imSum := sumRangeTracked w (M + 1) (fun m => (iPowIm m * arr.1.getD m 0, 2))
    let reOut := roundDivIntTracked (w + M + q + 2) (reSum.1 * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)
    let imOut := roundDivIntTracked (w + M + q + 2) (imSum.1 * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)
    (⟨reOut.1, imOut.1⟩,
      prodPi.2 + r_mant.2 + arr.2 + reSum.2 + imSum.2 + reOut.2 + imOut.2 +
      (5 * w * w + 20 * w + 13) + 4)

theorem expTwoPiIFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ) (w q : ℕ)
    (num : ℤ) (den : ℕ) (hq : 4 ≤ q) (hw : 100 * q ≤ w) (hden : den ≤ 2 ^ q)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → (smulTracked x y).1 = x * y) :
    (expTwoPiIFixedWithMulTracked smulTracked w q (approxPiFixed (q + 10)) num den).1 =
      expTwoPiIFixed q num den := by
  unfold expTwoPiIFixedWithMulTracked expTwoPiIFixed expTwoPiIFixedWithMul
  split_ifs with hden0
  · rfl
  · dsimp only
    set S : ℕ := q + 10
    set q_pi : ℕ := 4 * (S + 3) + 6
    set N : ℕ := 4 * 10 + S + 1
    set M : ℕ := N + 6
    set q_r : ℕ := 2 * M
    set q_acc : ℕ := 3 * M + 6
    set piFixed : ℤ := approxPiFixed S
    set numMod : ℤ := num % (den : ℤ)
    have hden_pos : (0 : ℤ) < (den : ℤ) := by positivity
    have hpi_fits : FitsSignedWord w piFixed :=
      fitsSignedWord_approxPiFixed S (by omega)
    have hmod_abs : |numMod| < (den : ℤ) := by
      have h0 : 0 ≤ numMod := Int.emod_nonneg num (ne_of_gt hden_pos)
      have h1 : numMod < (den : ℤ) := Int.emod_lt_of_pos num hden_pos
      rw [abs_of_nonneg h0]; exact h1
    have hmod_fits : FitsSignedWord w numMod := by
      rw [fitsSignedWord_iff_abs_lt]
      have hden_z : (den : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast hden
      exact lt_of_lt_of_le hmod_abs (hden_z.trans (pow_le_pow_right₀ (by decide) (by omega)))
    have hprod_eq : (smulTracked piFixed numMod).1 = piFixed * numMod :=
      hsmul _ _ hpi_fits hmod_fits
    rw [hprod_eq]
    set θNum : ℤ := 2 * (piFixed * numMod)
    set θDen : ℤ := (den : ℤ) * (2 : ℤ) ^ q_pi
    have hθ_fits : FitsSignedWord (2 * w + q_r + 2) (θNum * (2 : ℤ) ^ q_r) := by
      have hp : FitsSignedWord (w + w) (piFixed * numMod) := hpi_fits.mul hmod_fits
      have h2p : FitsSignedWord (w + w + 1) θNum := by
        have hsum : θNum = piFixed * numMod + piFixed * numMod := by ring
        rw [hsum]; exact hp.add hp
      exact (h2p.mul_two_pow q_r).mono (by omega)
    have hr_eq :
        (roundDivIntTracked (2 * w + q_r + 2) (θNum * (2 : ℤ) ^ q_r) θDen).1 =
          roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen :=
      roundDivIntTracked_fst θDen hθ_fits
    rw [hr_eq]
    set r_mant := roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen
    have hθ_bound : |θNum| ≤ (10 : ℤ) * θDen := by
      have hpi_nn : 0 ≤ piFixed := approxPiFixed_nonneg S
      have hpi_le : piFixed ≤ 5 * (2 : ℤ) ^ q_pi := approxPiFixed_le S
      have hmod_le : |numMod| ≤ (den : ℤ) := le_of_lt hmod_abs
      calc |θNum| = 2 * piFixed * |numMod| := by
            dsimp [θNum]; rw [abs_mul, abs_mul, abs_of_pos (by decide), abs_of_nonneg hpi_nn]; ring
        _ ≤ 2 * (5 * (2 : ℤ) ^ q_pi) * (den : ℤ) := by
            nlinarith [abs_nonneg numMod]
        _ = (10 : ℤ) * θDen := by dsimp [θDen]; ring
    have hr_bound : |r_mant| ≤ (10 : ℤ) * (2 : ℤ) ^ q_r :=
      abs_roundDivInt_mul_two_pow_le_of_pos 10 q_r (by positivity) hθ_bound
    have harr_eq :
        (expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant).1 =
          expTermArrayFixed q_r q_acc M r_mant :=
      expTermArrayFixedWithMulTracked_fst smulTracked 10 w q_r q_acc M r_mant hr_bound
        (by omega) (by omega) (by omega) hsmul
    rw [harr_eq, expTermArrayFixedWithMul_mul_eq]
    set arr := expTermArrayFixed q_r q_acc M r_mant
    have harr_bds : ∀ m : ℕ, FitsSignedWord (q_acc + 22) (arr.getD m 0) := by
      intro m
      rw [fitsSignedWord_iff_abs_lt]
      exact lt_of_le_of_lt (abs_expTermArrayFixed_getD_le 10 q_r q_acc M r_mant hr_bound (by omega) m)
        (pow_lt_pow_right₀ (by decide) (by omega))
    have hM_pow : M + 1 ≤ 2 ^ (M + 1) := le_of_lt Nat.lt_two_pow_self
    have hreSum_fits :
        FitsSignedWord (w + M + q + 2)
          ((∑ m ∈ Finset.range (M + 1), iPowRe m * arr.getD m 0) * (2 : ℤ) ^ q) := by
      have hsum := fitsSignedWord_sum_range (M + 1) hM_pow
        (fun m => iPowRe m * arr.getD m 0)
        (fun m _ => by
          rw [fitsSignedWord_iff_abs_lt, abs_mul]
          have hi := abs_iPowRe_int_le_one m
          have ha := (fitsSignedWord_iff_abs_lt _ _).mp (harr_bds m)
          nlinarith [abs_nonneg (arr.getD m 0)])
      exact (hsum.mul_two_pow q).mono (by omega)
    have himSum_fits :
        FitsSignedWord (w + M + q + 2)
          ((∑ m ∈ Finset.range (M + 1), iPowIm m * arr.getD m 0) * (2 : ℤ) ^ q) := by
      have hsum := fitsSignedWord_sum_range (M + 1) hM_pow
        (fun m => iPowIm m * arr.getD m 0)
        (fun m _ => by
          rw [fitsSignedWord_iff_abs_lt, abs_mul]
          have hi := abs_iPowIm_int_le_one m
          have ha := (fitsSignedWord_iff_abs_lt _ _).mp (harr_bds m)
          nlinarith [abs_nonneg (arr.getD m 0)])
      exact (hsum.mul_two_pow q).mono (by omega)
    simp only [sumRangeTracked_fst]
    rw [roundDivIntTracked_fst _ hreSum_fits, roundDivIntTracked_fst _ himSum_fits]

/-- Operation-tracking pure-integer clamped $\operatorname{sinc}$ Taylor mantissa. -/
def sincTaylorFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ)
    (w N : ℕ) (θNum θDen : ℤ) : CostM ℤ :=
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let r_mant := roundDivIntTracked (2 * w + q_r + 2) (θNum * (2 : ℤ) ^ q_r) θDen
  let arr := expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant.1
  let sRaw := sumRangeTracked w (M + 1) (fun m =>
    let d := roundDivIntTracked w (arr.1.getD m 0) ((m + 1 : ℕ) : ℤ)
    (iPowIm (m + 1) * d.1, d.2 + 2))
  (max (-(2 : ℤ) ^ q_acc) (min ((2 : ℤ) ^ q_acc) sRaw.1),
    r_mant.2 + arr.2 + sRaw.2 + 4)

theorem sincTaylorFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ)
    (B w N : ℕ) (θNum θDen : ℤ)
    (hθ_fits : FitsSignedWord (2 * w) θNum)
    (hden : 0 < θDen) (hθ_le : |θNum| ≤ (B : ℤ) * θDen)
    (hw_T : (3 * (N + 6) + 6) + 2 * B + 2 ≤ w)
    (hw_r : 2 * (N + 6) + B + 1 ≤ w)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → (smulTracked x y).1 = x * y) :
    (sincTaylorFixedWithMulTracked smulTracked w N θNum θDen).1 =
      sincTaylorFixed N θNum θDen := by
  unfold sincTaylorFixedWithMulTracked sincTaylorFixed sincTaylorFixedWithMul
  dsimp only
  set M : ℕ := N + 6
  set q_r : ℕ := 2 * M
  set q_acc : ℕ := 3 * M + 6
  have hr_eq :
      (roundDivIntTracked (2 * w + q_r + 2) (θNum * (2 : ℤ) ^ q_r) θDen).1 =
        roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen :=
    roundDivIntTracked_fst θDen ((hθ_fits.mul_two_pow q_r).mono (by omega))
  rw [hr_eq]
  set r_mant := roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen
  have hr_bound : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r :=
    abs_roundDivInt_mul_two_pow_le_of_pos B q_r hden hθ_le
  have harr_eq :
      (expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant).1 =
        expTermArrayFixed q_r q_acc M r_mant :=
    expTermArrayFixedWithMulTracked_fst smulTracked B w q_r q_acc M r_mant hr_bound
      (by omega) hw_T hw_r hsmul
  rw [harr_eq, expTermArrayFixedWithMul_mul_eq]
  have harr_bds : ∀ m : ℕ, FitsSignedWord w ((expTermArrayFixed q_r q_acc M r_mant).getD m 0) := by
    intro m
    rw [fitsSignedWord_iff_abs_lt]
    exact lt_of_le_of_lt (abs_expTermArrayFixed_getD_le B q_r q_acc M r_mant hr_bound (by omega) m)
      (pow_lt_pow_right₀ (by decide) (by omega))
  simp only [sumRangeTracked_fst]
  congr 2
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [roundDivIntTracked_fst _ (harr_bds m)]

/-- Operation-tracking pure-integer clamped $\exp$ Taylor mantissa. -/
def expTaylorFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ)
    (w N : ℕ) (gNum gDen : ℤ) : CostM ℤ :=
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let r_mant := roundDivIntTracked (3 * w + q_r + 2) (gNum * (2 : ℤ) ^ q_r) gDen
  let arr := expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant.1
  let eRaw := sumRangeTracked w (M + 1) (fun m => (arr.1.getD m 0, 2))
  (max 0 (min ((2 : ℤ) ^ q_acc) eRaw.1),
    r_mant.2 + arr.2 + eRaw.2 + 4)

theorem expTaylorFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ)
    (B w N : ℕ) (gNum gDen : ℤ)
    (hg_fits : FitsSignedWord (3 * w) gNum)
    (hden : 0 < gDen) (hg_le : |gNum| ≤ (B : ℤ) * gDen)
    (hw_T : (3 * (N + 6) + 6) + 2 * B + 2 ≤ w)
    (hw_r : 2 * (N + 6) + B + 1 ≤ w)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → (smulTracked x y).1 = x * y) :
    (expTaylorFixedWithMulTracked smulTracked w N gNum gDen).1 =
      expTaylorFixed N gNum gDen := by
  unfold expTaylorFixedWithMulTracked expTaylorFixed expTaylorFixedWithMul
  dsimp only
  set M : ℕ := N + 6
  set q_r : ℕ := 2 * M
  set q_acc : ℕ := 3 * M + 6
  have hr_eq :
      (roundDivIntTracked (3 * w + q_r + 2) (gNum * (2 : ℤ) ^ q_r) gDen).1 =
        roundDivInt (gNum * (2 : ℤ) ^ q_r) gDen :=
    roundDivIntTracked_fst gDen ((hg_fits.mul_two_pow q_r).mono (by omega))
  rw [hr_eq]
  set r_mant := roundDivInt (gNum * (2 : ℤ) ^ q_r) gDen
  have hr_bound : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r :=
    abs_roundDivInt_mul_two_pow_le_of_pos B q_r hden hg_le
  have harr_eq :
      (expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant).1 =
        expTermArrayFixed q_r q_acc M r_mant :=
    expTermArrayFixedWithMulTracked_fst smulTracked B w q_r q_acc M r_mant hr_bound
      (by omega) hw_T hw_r hsmul
  rw [harr_eq, expTermArrayFixedWithMul_mul_eq]
  simp only [sumRangeTracked_fst]

/-- Operation-tracking filter tap entry generator. Explicitly charges `4 * w * w + 20 * w + 16` for the `w`-bit scalar multiplications
`d * (t1 : ℤ)` and `(4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed`. -/
def computeFilterTapEntryTracked (smulTracked : ℤ → ℤ → CostM ℤ)
    (w m1 t1 pW pC q S : ℕ) (piFixed l2Fixed : ℤ) (j1 : Fin t1) (d : ℤ) : CostM ℤ :=
  let q_pi : ℕ := 4 * (S + 3) + 6
  let q_l2 : ℕ := S + (S + 2)
  let B_sinc : ℕ := 5 * (m1 + 1)
  let N_s : ℕ := 4 * B_sinc + S + 1
  let q_accs : ℕ := 3 * (N_s + 6) + 6
  let B_exp : ℕ := 25 * (pC + 1)
  let N_e : ℕ := 4 * B_exp + S + 1
  let q_acce : ℕ := 3 * (N_e + 6) + 6
  if |d| ≤ (m1 : ℤ) then
    let tNum : ℤ := d * (t1 : ℤ) - (j1.val : ℤ)
    let θNumP := smulTracked piFixed tNum
    let θDen : ℤ := (t1 : ℤ) * (2 : ℤ) ^ q_pi
    let sincFixed := sincTaylorFixedWithMulTracked smulTracked w N_s θNumP.1 θDen
    let θSq := smulTracked θNumP.1 θNumP.1
    let gNum : ℤ := -(θSq.1 * (2 : ℤ) ^ q_l2)
    let gDen : ℤ := (4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)
    let expFixed := expTaylorFixedWithMulTracked smulTracked w N_e gNum gDen
    let prodSE := smulTracked sincFixed.1 expFixed.1
    let res := roundDivIntTracked (2 * w + q + 2) (prodSE.1 * (2 : ℤ) ^ q) ((2 : ℤ) ^ (q_accs + q_acce))
    (res.1, θNumP.2 + sincFixed.2 + θSq.2 + expFixed.2 + prodSE.2 + res.2 + (4 * w * w + 20 * w + 16))
  else
    (0, 2)

private theorem abs_max_neg_min_le {A x : ℤ} (hA : 0 ≤ A) :
    |max (-A) (min A x)| ≤ A :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem abs_max_zero_min_le {A x : ℤ} (hA : 0 ≤ A) :
    |max 0 (min A x)| ≤ A := by
  rw [abs_of_nonneg (le_max_left 0 _)]
  exact max_le hA (min_le_left _ _)

theorem computeFilterTapEntryTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ)
    (w K p : ℕ) (hK : 2 ≤ K) (hw : 1000 * qChildEll K p ≤ w)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → (smulTracked x y).1 = x * y)
    (j1 : Fin (t1Ell K)) (d : ℤ) :
    let q := qChildEll K p
    let pC := pChildEll K p
    let S := q + 3 * pC + 20
    let q_l2 := S + (S + 2)
    let piFixed := approxPiFixed S
    let l2Fixed := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S)
    (computeFilterTapEntryTracked smulTracked w (computeM1Ell K p) (t1Ell K) (pWorkEll K p)
      pC q S piFixed l2Fixed j1 d).1 =
      computeFilterTapFixedWithMul (· * ·) K p j1 d := by
  dsimp only
  set q := qChildEll K p
  set pC := pChildEll K p
  set pW := pWorkEll K p
  set m1 := computeM1Ell K p
  let t1 := t1Ell K
  set S := q + 3 * pC + 20
  set q_pi := 4 * (S + 3) + 6
  set q_l2 := S + (S + 2)
  set B_sinc := 5 * (m1 + 1)
  set N_s := 4 * B_sinc + S + 1
  set q_accs := 3 * (N_s + 6) + 6
  set B_exp := 25 * (pC + 1)
  set N_e := 4 * B_exp + S + 1
  set q_acce := 3 * (N_e + 6) + 6
  have hq_eq : q = p + 2 * K + 14 := by unfold q qChildEll pChildEll pWorkEll; omega
  have hpC_eq : pC = p + 2 * K + 12 := by unfold pC pChildEll pWorkEll; omega
  have hpW_eq : pW = p + K + 6 := by unfold pW pWorkEll; rfl
  have hm1_le : m1 ≤ pC := computeM1Ell_le_pChildEll K p
  have ht1_pos : 0 < t1 := t1Ell_pos K
  have ht1_le : t1 ≤ 2 ^ K := t1Ell_le_two_pow K
  have hpi_fits : FitsSignedWord (4 * S + 22) (approxPiFixed S) :=
    fitsSignedWord_approxPiFixed S (by omega)
  have hpi_nn : 0 ≤ approxPiFixed S := approxPiFixed_nonneg S
  have hpi_le : approxPiFixed S ≤ 5 * (2 : ℤ) ^ q_pi := approxPiFixed_le S
  have hl2_ge : (2 : ℤ) ^ (q_l2 - 1) ≤ max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S) :=
    le_max_left _ _
  have hl2_pos : (0 : ℤ) < max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S) :=
    lt_of_lt_of_le (by positivity) hl2_ge
  unfold computeFilterTapEntryTracked computeFilterTapFixedWithMul computeFilterTapAuxFixedWithMul
  dsimp only
  generalize approxPiFixed S = piFixed at hpi_fits hpi_nn hpi_le ⊢
  generalize max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S) = l2Fixed at hl2_ge hl2_pos ⊢
  split_ifs with hd
  · dsimp only
    set tNum : ℤ := d * (t1Ell K : ℤ) - (j1.val : ℤ)
    have ht1_z : (0 : ℤ) < (t1Ell K : ℤ) := by exact_mod_cast ht1_pos
    have htNum_abs : |tNum| ≤ ((m1 + 1 : ℕ) : ℤ) * (t1 : ℤ) := by
      have hj1 : (j1.val : ℤ) < (t1 : ℤ) := by exact_mod_cast j1.isLt
      have hj1_nn : (0 : ℤ) ≤ (j1.val : ℤ) := Nat.cast_nonneg j1.val
      have hdt1 : |d * (t1 : ℤ)| ≤ (m1 : ℤ) * (t1 : ℤ) := by
        rw [abs_mul, abs_of_pos ht1_z]
        exact mul_le_mul_of_nonneg_right hd (le_of_lt ht1_z)
      have htri := abs_sub (d * (t1 : ℤ)) (j1.val : ℤ)
      rw [abs_of_nonneg hj1_nn] at htri
      push_cast; linarith
    have htNum_fits : FitsSignedWord (2 * q) tNum := by
      rw [fitsSignedWord_iff_abs_lt]
      have hm1_pow : ((m1 + 1 : ℕ) : ℤ) < (2 : ℤ) ^ q := by
        have : m1 + 1 < 2 ^ q := lt_of_le_of_lt (by omega : m1 + 1 ≤ q) Nat.lt_two_pow_self
        exact_mod_cast this
      have ht1_pow : (t1 : ℤ) ≤ (2 : ℤ) ^ q := by
        have : t1 ≤ 2 ^ q := ht1_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
        exact_mod_cast this
      calc |tNum| ≤ ((m1 + 1 : ℕ) : ℤ) * (t1 : ℤ) := htNum_abs
        _ < (2 : ℤ) ^ q * (2 : ℤ) ^ q := by nlinarith [ht1_pos]
        _ = (2 : ℤ) ^ (2 * q) := by rw [← pow_add, Nat.two_mul]
    have hθ_eq : (smulTracked piFixed tNum).1 = piFixed * tNum :=
      hsmul _ _ (hpi_fits.mono (by omega)) (htNum_fits.mono (by omega))
    rw [hθ_eq]
    set θNum := piFixed * tNum
    set θDen : ℤ := (t1Ell K : ℤ) * (2 : ℤ) ^ q_pi
    have hθDen_pos : 0 < θDen := mul_pos ht1_z (by positivity)
    have hθ_fits : FitsSignedWord (4 * S + 22 + 2 * q) θNum := hpi_fits.mul htNum_fits
    have hθ_bound : |θNum| ≤ ((5 * (m1 + 1) : ℕ) : ℤ) * θDen := by
      calc |θNum| = piFixed * |tNum| := by
            dsimp [θNum]; rw [abs_mul, abs_of_nonneg hpi_nn]
        _ ≤ (5 * (2 : ℤ) ^ q_pi) * (((m1 + 1 : ℕ) : ℤ) * (t1 : ℤ)) :=
            mul_le_mul hpi_le htNum_abs (abs_nonneg _) (by positivity)
        _ = ((5 * (m1 + 1) : ℕ) : ℤ) * θDen := by dsimp [θDen, t1]; ring
    have hsinc_eq :
        (sincTaylorFixedWithMulTracked smulTracked w N_s θNum θDen).1 =
          sincTaylorFixed N_s θNum θDen :=
      sincTaylorFixedWithMulTracked_fst smulTracked (5 * (m1 + 1)) w N_s θNum θDen
        (hθ_fits.mono (by omega)) hθDen_pos hθ_bound (by omega) (by omega) hsmul
    have hθSq_eq : (smulTracked θNum θNum).1 = θNum * θNum :=
      hsmul _ _ (hθ_fits.mono (by omega)) (hθ_fits.mono (by omega))
    rw [hsinc_eq, hθSq_eq]
    set gNum : ℤ := -((θNum * θNum) * (2 : ℤ) ^ q_l2)
    set gDen : ℤ := (4 * (pW : ℤ) * (t1Ell K : ℤ) * (t1Ell K : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)
    have hpW_z : (0 : ℤ) < (pW : ℤ) := by exact_mod_cast (by omega : 0 < pW)
    have hgDen_pos : 0 < gDen :=
      mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by decide) hpW_z) ht1_z) ht1_z) hl2_pos) (by positivity)
    have hg_fits : FitsSignedWord (3 * w) gNum :=
      (((hθ_fits.mul hθ_fits).mul_two_pow q_l2).neg).mono (by omega)
    have hg_bound : |gNum| ≤ ((50 * (m1 + 1) : ℕ) : ℤ) * gDen := by
      have h2l2 : (2 : ℤ) ^ q_l2 ≤ 2 * l2Fixed := by
        calc (2 : ℤ) ^ q_l2 = 2 * (2 : ℤ) ^ (q_l2 - 1) := by
              conv_lhs => rw [show q_l2 = (q_l2 - 1) + 1 by omega, pow_succ']
          _ ≤ 2 * l2Fixed := mul_le_mul_of_nonneg_left hl2_ge (by decide)
      have hm1_pW : ((m1 + 1 : ℕ) : ℤ) ≤ 4 * (pW : ℤ) := by
        have : m1 + 1 ≤ 4 * pW := by omega
        exact_mod_cast this
      have hθ_sq_le : |θNum| * |θNum| ≤
          (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) * (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) :=
        mul_le_mul hθ_bound hθ_bound (abs_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hθDen_pos))
      have hDen_sq : θDen * θDen = (t1 : ℤ) * (t1 : ℤ) * (2 : ℤ) ^ (2 * q_pi) := by
        dsimp [θDen, t1]; rw [Nat.two_mul, pow_add]; ring
      have hsq_id : (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) * (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) =
          25 * ((m1 + 1 : ℕ) : ℤ) * ((m1 + 1 : ℕ) : ℤ) * (θDen * θDen) := by
        push_cast; ring
      have htail_nn : 0 ≤ (t1 : ℤ) * (t1 : ℤ) * l2Fixed * (2 : ℤ) ^ (2 * q_pi) :=
        mul_nonneg (mul_nonneg (mul_self_nonneg (t1 : ℤ)) (le_of_lt hl2_pos)) (by positivity)
      dsimp [gNum]
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ q_l2)]
      calc (|θNum| * |θNum|) * (2 : ℤ) ^ q_l2
          ≤ ((((5 * (m1 + 1) : ℕ) : ℤ) * θDen) * (((5 * (m1 + 1) : ℕ) : ℤ) * θDen)) *
              (2 * l2Fixed) :=
            mul_le_mul hθ_sq_le h2l2 (by positivity) (mul_self_nonneg _)
        _ = 50 * ((m1 + 1 : ℕ) : ℤ) * ((m1 + 1 : ℕ) : ℤ) *
              ((t1 : ℤ) * (t1 : ℤ) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)) := by
            rw [hsq_id, hDen_sq]; ring
        _ ≤ 50 * ((m1 + 1 : ℕ) : ℤ) * (4 * (pW : ℤ)) *
              ((t1 : ℤ) * (t1 : ℤ) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hm1_pW
                (mul_nonneg (by decide) (Nat.cast_nonneg _)))
              htail_nn
        _ = ((50 * (m1 + 1) : ℕ) : ℤ) * gDen := by dsimp [gDen, t1]; ring
    have hexp_eq :
        (expTaylorFixedWithMulTracked smulTracked w N_e gNum gDen).1 =
          expTaylorFixed N_e gNum gDen :=
      expTaylorFixedWithMulTracked_fst smulTracked (50 * (m1 + 1)) w N_e gNum gDen
        hg_fits hgDen_pos hg_bound (by omega) (by omega) hsmul
    rw [hexp_eq]
    have hsinc_fits : FitsSignedWord w (sincTaylorFixed N_s θNum θDen) := by
      rw [fitsSignedWord_iff_abs_lt]
      unfold sincTaylorFixed sincTaylorFixedWithMul
      exact lt_of_le_of_lt (abs_max_neg_min_le (by positivity))
        (pow_lt_pow_right₀ (by decide) (by omega))
    have hexp_fits : FitsSignedWord w (expTaylorFixed N_e gNum gDen) := by
      rw [fitsSignedWord_iff_abs_lt]
      unfold expTaylorFixed expTaylorFixedWithMul
      exact lt_of_le_of_lt (abs_max_zero_min_le (by positivity))
        (pow_lt_pow_right₀ (by decide) (by omega))
    have hprod_eq :
        (smulTracked (sincTaylorFixed N_s θNum θDen) (expTaylorFixed N_e gNum gDen)).1 =
          sincTaylorFixed N_s θNum θDen * expTaylorFixed N_e gNum gDen :=
      hsmul _ _ hsinc_fits hexp_fits
    have hres_fits :
        FitsSignedWord (2 * w + q + 2)
          ((sincTaylorFixed N_s θNum θDen * expTaylorFixed N_e gNum gDen) * (2 : ℤ) ^ q) :=
      ((hsinc_fits.mul hexp_fits).mul_two_pow q).mono (by omega)
    rw [hprod_eq, roundDivIntTracked_fst _ hres_fits]
  · rfl

/-- Operation-tracking pure-integer $\int_0^z e^{-t^2}\,dt$ Taylor mantissa. -/
def erfIntegralTaylorFixedWithMulTracked (smulTracked : ℤ → ℤ → CostM ℤ)
    (w N : ℕ) (zNum zDen : ℤ) : CostM ℤ :=
  let M : ℕ := N + 6
  let q_z : ℕ := M
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := 3 * M + 6
  let z_mant := roundDivIntTracked (2 * w + q_z + 2) (zNum * (2 : ℤ) ^ q_z) zDen
  let zSq := smulTracked z_mant.1 z_mant.1
  let r_mant : ℤ := - zSq.1
  let arr := expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant
  let S_inner := sumRangeTracked w (M + 1) (fun m =>
    roundDivIntTracked w (arr.1.getD m 0) ((2 * m + 1 : ℕ) : ℤ))
  let out := smulTracked z_mant.1 S_inner.1
  (out.1, z_mant.2 + zSq.2 + arr.2 + S_inner.2 + out.2 + 4)

theorem erfIntegralTaylorFixedWithMulTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ)
    (B w N : ℕ) (zNum zDen : ℤ)
    (hz_fits : FitsSignedWord (2 * w) zNum)
    (hden : 0 < zDen) (hz_le : |zNum| ≤ (B : ℤ) * zDen)
    (hw_T : (3 * (N + 6) + 6) + 2 * (B * B) + (N + 6) + 4 ≤ w)
    (hw_r : 2 * (N + 6) + B * B + 1 ≤ w)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → (smulTracked x y).1 = x * y) :
    (erfIntegralTaylorFixedWithMulTracked smulTracked w N zNum zDen).1 =
      erfIntegralTaylorFixed N zNum zDen ∧
    FitsSignedWord (2 * w) (erfIntegralTaylorFixed N zNum zDen) := by
  unfold erfIntegralTaylorFixedWithMulTracked erfIntegralTaylorFixed erfIntegralTaylorFixedWithMul
  dsimp only
  set M : ℕ := N + 6
  set q_z : ℕ := M
  set q_r : ℕ := 2 * M
  set q_acc : ℕ := 3 * M + 6
  have hz_eq :
      (roundDivIntTracked (2 * w + q_z + 2) (zNum * (2 : ℤ) ^ q_z) zDen).1 =
        roundDivInt (zNum * (2 : ℤ) ^ q_z) zDen :=
    roundDivIntTracked_fst zDen ((hz_fits.mul_two_pow q_z).mono (by omega))
  rw [hz_eq]
  set z_mant := roundDivInt (zNum * (2 : ℤ) ^ q_z) zDen
  have hz_bound : |z_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_z :=
    abs_roundDivInt_mul_two_pow_le_of_pos B q_z hden hz_le
  have hB_le_B2 : B ≤ B * B + 1 := by nlinarith
  have hz_mant_fits : FitsSignedWord w z_mant :=
    fitsSignedWord_of_abs_le_mul_two_pow hz_bound (by omega)
  have hzSq_eq : (smulTracked z_mant z_mant).1 = z_mant * z_mant :=
    hsmul _ _ hz_mant_fits hz_mant_fits
  rw [hzSq_eq]
  set r_mant : ℤ := -(z_mant * z_mant)
  have hr_bound : |r_mant| ≤ ((B * B : ℕ) : ℤ) * (2 : ℤ) ^ q_r := by
    dsimp [r_mant]
    rw [abs_neg, abs_mul]
    calc |z_mant| * |z_mant|
        ≤ ((B : ℤ) * (2 : ℤ) ^ q_z) * ((B : ℤ) * (2 : ℤ) ^ q_z) :=
          mul_le_mul hz_bound hz_bound (abs_nonneg _) (by positivity)
      _ = ((B * B : ℕ) : ℤ) * (2 : ℤ) ^ q_r := by
          dsimp [q_r, q_z]; rw [Nat.two_mul, pow_add]; push_cast; ring
  have harr_eq :
      (expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M r_mant).1 =
        expTermArrayFixed q_r q_acc M r_mant :=
    expTermArrayFixedWithMulTracked_fst smulTracked (B * B) w q_r q_acc M r_mant hr_bound
      (by omega) (by omega) hw_r hsmul
  rw [harr_eq, expTermArrayFixedWithMul_mul_eq]
  set arr := expTermArrayFixed q_r q_acc M r_mant
  have harr_bds : ∀ m : ℕ, FitsSignedWord (q_acc + 2 * (B * B) + 2) (arr.getD m 0) := by
    intro m
    rw [fitsSignedWord_iff_abs_lt]
    exact lt_of_le_of_lt (abs_expTermArrayFixed_getD_le (B * B) q_r q_acc M r_mant hr_bound (by omega) m)
      (pow_lt_pow_right₀ (by decide) (by omega))
  have hS_sum :
      (sumRangeTracked w (M + 1) (fun m =>
        roundDivIntTracked w (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ))).1 =
      ∑ m ∈ Finset.range (M + 1), roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ) := by
    rw [sumRangeTracked_fst]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    exact roundDivIntTracked_fst _ ((harr_bds m).mono (by omega))
  rw [hS_sum]
  have hM_pow : M + 1 ≤ 2 ^ (M + 1) := le_of_lt Nat.lt_two_pow_self
  have hS_fits :
      FitsSignedWord w
        (∑ m ∈ Finset.range (M + 1), roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ)) := by
    have hsum := fitsSignedWord_sum_range (M + 1) hM_pow
      (fun m => roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ))
      (fun m _ => FitsSignedWord.roundDivInt _ (harr_bds m))
    exact hsum.mono (by omega)
  have hprod_fits : FitsSignedWord (2 * w)
      (z_mant * ∑ m ∈ Finset.range (M + 1), roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ)) :=
    (hz_mant_fits.mul hS_fits).mono (by omega)
  rw [hsmul _ _ hz_mant_fits hS_fits]
  exact ⟨rfl, hprod_fits⟩

/-- Operation-tracking passband $\hat{g}_{\alpha_\ell}(\text{yNum} / r)$ mantissa entry generator. -/
def computeGHatMantissaEntryTracked (smulTracked : ℤ → ℤ → CostM ℤ)
    (w q S N_erf : ℕ) (cFixed sqrtPiFixed : ℤ) (yNum : ℤ) (r : ℕ) : CostM ℤ :=
  let M : ℕ := N_erf + 6
  let q_z : ℕ := M
  let q_acc : ℕ := 3 * M + 6
  let zDen : ℤ := 2 * (r : ℤ) * (2 : ℤ) ^ S
  let z1Num := smulTracked cFixed ((r : ℤ) - 2 * yNum)
  let I1Fixed := erfIntegralTaylorFixedWithMulTracked smulTracked w N_erf z1Num.1 zDen
  let z2Num := smulTracked cFixed ((r : ℤ) + 2 * yNum)
  let I2Fixed := erfIntegralTaylorFixedWithMulTracked smulTracked w N_erf z2Num.1 zDen
  let div := roundDivIntTracked (2 * w + S + q + 2)
    (((I1Fixed.1 + I2Fixed.1) * (2 : ℤ) ^ S) * (2 : ℤ) ^ q)
    (sqrtPiFixed * (2 : ℤ) ^ (q_z + q_acc))
  (max 0 div.1, z1Num.2 + I1Fixed.2 + z2Num.2 + I2Fixed.2 + div.2 + 6)

theorem computeGHatMantissaEntryTracked_fst (smulTracked : ℤ → ℤ → CostM ℤ)
    (w K p : ℕ) (hK : 2 ≤ K) (hw : 1000 * qChildEll K p ≤ w)
    (hsmul : ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y → (smulTracked x y).1 = x * y)
    (yNum : ℤ) (hy0 : 0 ≤ yNum) (hyr : yNum ≤ (rEll K : ℤ)) :
    let q := qChildEll K p
    let pW := pWorkEll K p
    let S := q + 2 * pW + 20
    let q_l2 := 2 * S + (2 * S + 2)
    let l2Fixed := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed (2 * S))
    let cBound := Nat.sqrt (3 * pW) + 1
    let cRawFixed := approxSqrtFixed (2 * S + 2) (4 * (pW : ℤ) * l2Fixed)
    let cFixed := min ((cBound : ℤ) * (2 : ℤ) ^ S) cRawFixed
    let B_erf := 2 * cBound
    let N_erf := 4 * B_erf ^ 2 + (S + B_erf) + 1
    let pi2SFixed := approxPiFixed (2 * S)
    let sqrtPiRawFixed := approxSqrtFixed (6 * S + 18) pi2SFixed
    let sqrtPiFixed := max ((2 : ℤ) ^ S) sqrtPiRawFixed
    (computeGHatMantissaEntryTracked smulTracked w q S N_erf cFixed sqrtPiFixed yNum (rEll K)).1 =
      computeGHatMantissaFixed K p yNum (rEll K) := by
  unfold computeGHatMantissaEntryTracked computeGHatMantissaFixed
    computeGHatMantissaFixedWithMul computeGHatMantissaAuxFixedWithMul
  dsimp only
  have hcRaw_nn : (0 : ℤ) ≤
      approxSqrtFixed (2 * (qChildEll K p + 2 * pWorkEll K p + 20) + 2)
        (4 * (pWorkEll K p : ℤ) *
          max ((2 : ℤ) ^ (2 * (qChildEll K p + 2 * pWorkEll K p + 20) +
            (2 * (qChildEll K p + 2 * pWorkEll K p + 20) + 2) - 1))
            (approxLogTwoFixed (2 * (qChildEll K p + 2 * pWorkEll K p + 20)))) := by
    unfold approxSqrtFixed; positivity
  generalize
    approxSqrtFixed (2 * (qChildEll K p + 2 * pWorkEll K p + 20) + 2)
      (4 * (pWorkEll K p : ℤ) *
        max ((2 : ℤ) ^ (2 * (qChildEll K p + 2 * pWorkEll K p + 20) +
          (2 * (qChildEll K p + 2 * pWorkEll K p + 20) + 2) - 1))
          (approxLogTwoFixed (2 * (qChildEll K p + 2 * pWorkEll K p + 20)))) = cRawFixed at hcRaw_nn ⊢
  generalize
    max ((2 : ℤ) ^ (qChildEll K p + 2 * pWorkEll K p + 20))
      (approxSqrtFixed (6 * (qChildEll K p + 2 * pWorkEll K p + 20) + 18)
        (approxPiFixed (2 * (qChildEll K p + 2 * pWorkEll K p + 20)))) = sqrtPiFixed
  set q := qChildEll K p
  set pW := pWorkEll K p
  set r := rEll K
  set S := q + 2 * pW + 20
  set cBound := Nat.sqrt (3 * pW) + 1
  set cFixed := min ((cBound : ℤ) * (2 : ℤ) ^ S) cRawFixed
  set B_erf := 2 * cBound
  set N_erf := 4 * B_erf ^ 2 + (S + B_erf) + 1
  have hq_eq : q = p + 2 * K + 14 := by unfold q qChildEll pChildEll pWorkEll; omega
  have hpW_eq : pW = p + K + 6 := by unfold pW pWorkEll; rfl
  have hr_pos : 0 < r := rEll_pos K
  have hr_le : r ≤ 2 ^ K := rEll_le_two_pow K
  have hsqrt_sq : Nat.sqrt (3 * pW) * Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le (3 * pW)
  have hsqrt_le : Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le_self (3 * pW)
  have hcBound_sq : cBound * cBound ≤ 9 * pW + 1 := by
    change (Nat.sqrt (3 * pW) + 1) * (Nat.sqrt (3 * pW) + 1) ≤ 9 * pW + 1
    nlinarith
  have hBerf_sq : B_erf ^ 2 ≤ 36 * pW + 4 := by
    change (2 * cBound) ^ 2 ≤ 36 * pW + 4
    nlinarith
  have hBerf_mul : B_erf * B_erf ≤ 36 * pW + 4 := by
    change (2 * cBound) * (2 * cBound) ≤ 36 * pW + 4
    nlinarith
  have hcFixed_nn : 0 ≤ cFixed := le_min (by positivity) hcRaw_nn
  have hcFixed_le : cFixed ≤ (cBound : ℤ) * (2 : ℤ) ^ S := min_le_left _ _
  have hcFixed_fits : FitsSignedWord (S + q) cFixed := by
    rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg hcFixed_nn]
    have hc_pow : (cBound : ℤ) < (2 : ℤ) ^ q := by
      have : cBound < 2 ^ q :=
        lt_of_le_of_lt (by omega : cBound ≤ 4 * q) (four_mul_lt_two_pow (by omega))
      exact_mod_cast this
    calc cFixed ≤ (cBound : ℤ) * (2 : ℤ) ^ S := hcFixed_le
      _ < (2 : ℤ) ^ q * (2 : ℤ) ^ S := mul_lt_mul_of_pos_right hc_pow (by positivity)
      _ = (2 : ℤ) ^ (S + q) := by rw [← pow_add, add_comm]
  have hy1_abs : |(r : ℤ) - 2 * yNum| ≤ 2 * (r : ℤ) := by
    rw [abs_le]; constructor <;> linarith
  have hy2_abs : |(r : ℤ) + 2 * yNum| ≤ 3 * (r : ℤ) := by
    rw [abs_le]; constructor <;> linarith
  have hr_pow : 3 * (r : ℤ) < (2 : ℤ) ^ q := by
    have hr_z : (r : ℤ) ≤ (2 : ℤ) ^ K := by exact_mod_cast hr_le
    have hK_pow : (4 : ℤ) * (2 : ℤ) ^ K ≤ (2 : ℤ) ^ q := by
      have : 2 ^ (K + 2) ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by omega)
      simpa [pow_add, mul_comm] using (by exact_mod_cast this : (2 : ℤ) ^ (K + 2) ≤ (2 : ℤ) ^ q)
    linarith [show (0 : ℤ) < (2 : ℤ) ^ K by positivity]
  have hy1_fits : FitsSignedWord q ((r : ℤ) - 2 * yNum) :=
    (fitsSignedWord_iff_abs_lt q _).mpr (lt_of_le_of_lt (hy1_abs.trans (by linarith)) hr_pow)
  have hy2_fits : FitsSignedWord q ((r : ℤ) + 2 * yNum) :=
    (fitsSignedWord_iff_abs_lt q _).mpr (lt_of_le_of_lt hy2_abs hr_pow)
  have hz1_eq : (smulTracked cFixed ((r : ℤ) - 2 * yNum)).1 = cFixed * ((r : ℤ) - 2 * yNum) :=
    hsmul _ _ (hcFixed_fits.mono (by omega)) (hy1_fits.mono (by omega))
  have hz2_eq : (smulTracked cFixed ((r : ℤ) + 2 * yNum)).1 = cFixed * ((r : ℤ) + 2 * yNum) :=
    hsmul _ _ (hcFixed_fits.mono (by omega)) (hy2_fits.mono (by omega))
  rw [hz1_eq, hz2_eq]
  set zDen : ℤ := 2 * (r : ℤ) * (2 : ℤ) ^ S
  set z1Num : ℤ := cFixed * ((r : ℤ) - 2 * yNum)
  set z2Num : ℤ := cFixed * ((r : ℤ) + 2 * yNum)
  have hz1_bound : |z1Num| ≤ (B_erf : ℤ) * zDen := by
    rw [abs_mul, abs_of_nonneg hcFixed_nn]
    calc cFixed * |(r : ℤ) - 2 * yNum|
        ≤ ((cBound : ℤ) * (2 : ℤ) ^ S) * (3 * (r : ℤ)) :=
          mul_le_mul hcFixed_le (hy1_abs.trans (by linarith)) (abs_nonneg _) (by positivity)
      _ ≤ (B_erf : ℤ) * zDen := by
          dsimp [B_erf, zDen]
          nlinarith [show (0 : ℤ) ≤ (cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S by positivity]
  have hz2_bound : |z2Num| ≤ (B_erf : ℤ) * zDen := by
    rw [abs_mul, abs_of_nonneg hcFixed_nn]
    calc cFixed * |(r : ℤ) + 2 * yNum|
        ≤ ((cBound : ℤ) * (2 : ℤ) ^ S) * (3 * (r : ℤ)) :=
          mul_le_mul hcFixed_le hy2_abs (abs_nonneg _) (by positivity)
      _ ≤ (B_erf : ℤ) * zDen := by
          dsimp [B_erf, zDen]
          nlinarith [show (0 : ℤ) ≤ (cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S by positivity]
  have hI1 := erfIntegralTaylorFixedWithMulTracked_fst smulTracked B_erf w N_erf z1Num zDen
    ((hcFixed_fits.mul hy1_fits).mono (by omega)) (by positivity) hz1_bound
    (by omega) (by omega) hsmul
  have hI2 := erfIntegralTaylorFixedWithMulTracked_fst smulTracked B_erf w N_erf z2Num zDen
    ((hcFixed_fits.mul hy2_fits).mono (by omega)) (by positivity) hz2_bound
    (by omega) (by omega) hsmul
  have hdiv_fits :
      FitsSignedWord (2 * w + S + q + 2)
        (((erfIntegralTaylorFixed N_erf z1Num zDen +
            erfIntegralTaylorFixed N_erf z2Num zDen) * (2 : ℤ) ^ S) * (2 : ℤ) ^ q) :=
    ((((hI1.2.add hI2.2).mul_two_pow S).mul_two_pow q)).mono (by omega)
  rw [hI1.1, hI2.1, roundDivIntTracked_fst _ hdiv_fits]

/-- **Intrinsically Operation-Tracking Pure-Integer Schedule Tree Generator
(`computeScheduleIntTreeWithMulTracked`)**:
Constructs `ScheduleIntTree K p B_in` and accumulates the exact step count `.2` bottom-up from the
primitive Taylor series, bit-by-bit restoring divisions (`roundDivIntTracked`), bit-by-bit restoring
square roots (`binaryRestoringSqrtRegTracked`), bit-list sub-multiplications
(`subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)`), and array tabulations
(`memoizeFilterTapTracked`, `memoizeFinTracked`), with **zero** calls to any formula cost
(`scheduleTreeGenOps`). -/
def computeScheduleIntTreeWithMulTracked
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)) (K p B_in : ℕ) :
    CostM (ScheduleIntTree K p B_in) :=
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    let q := qChildEll K p
    let w := 1000 * q
    let pW := pWorkEll K p
    let pC := pChildEll K p
    let m1 := computeM1Ell K p
    let r := rEll K
    let smul := signedMulFromTrackedBitMul w (subMulBits w)
    -- Hoisted constants for expTwoPiIFixedWithMulTracked
    let piRoot := approxPiFixedTracked w (q + 10)
    -- Hoisted constants for computeFilterTapEntryTracked
    let S_tap := q + 3 * pC + 20
    let q_l2_tap := S_tap + (S_tap + 2)
    let piTap := approxPiFixedTracked w S_tap
    let l2Tap := approxLogTwoFixedTracked w S_tap
    let l2TapFixed := max ((2 : ℤ) ^ (q_l2_tap - 1)) l2Tap.1
    -- Hoisted constants for computeGHatMantissaEntryTracked
    let S_ghat := q + 2 * pW + 20
    let q_l2_ghat := 2 * S_ghat + (2 * S_ghat + 2)
    let l2GHat := approxLogTwoFixedTracked w (2 * S_ghat)
    let l2GHatFixed := max ((2 : ℤ) ^ (q_l2_ghat - 1)) l2GHat.1
    let cBoundSq := binaryRestoringSqrtRegTracked w (3 * pW)
    let cBound := cBoundSq.1.1 + 1
    let cRaw := approxSqrtFixedTracked w (2 * S_ghat + 2) (4 * (pW : ℤ) * l2GHatFixed)
    let cFixed := min ((cBound : ℤ) * (2 : ℤ) ^ S_ghat) cRaw.1
    let B_erf := 2 * cBound
    let N_erf := 4 * B_erf ^ 2 + (S_ghat + B_erf) + 1
    let pi2S := approxPiFixedTracked w (2 * S_ghat)
    let sqrtPiRaw := approxSqrtFixedTracked w (6 * S_ghat + 18) pi2S.1
    let sqrtPiFixed := max ((2 : ℤ) ^ S_ghat) sqrtPiRaw.1
    -- Tabulate node tables
    let tapTbl := memoizeFilterTapTracked m1
      (computeFilterTapEntryTracked smul w m1 (t1Ell K) pW pC q S_tap piTap.1 l2TapFixed)
    let preTbl := memoizeFinTracked (fun k2 : Fin r =>
      expTwoPiIFixedWithMulTracked smul w q piRoot.1 (k2.val : ℤ) (2 * r))
    let postTbl := memoizeFinTracked (fun k2 : Fin r =>
      expTwoPiIFixedWithMulTracked smul w q piRoot.1 (-(k2.val : ℤ)) (2 * r))
    let c0Tbl := memoizeFinTracked (fun u2 : Fin r =>
      computeGHatMantissaEntryTracked smul w q S_ghat N_erf cFixed sqrtPiFixed (u2.val : ℤ) r)
    let c1Tbl := memoizeFinTracked (fun u2 : Fin r =>
      computeGHatMantissaEntryTracked smul w q S_ghat N_erf cFixed sqrtPiFixed
        ((r : ℤ) - (u2.val : ℤ)) r)
    let child := computeScheduleIntTreeWithMulTracked subMulBits
      (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
    let hoistCost := piRoot.2 + piTap.2 + l2Tap.2 + l2GHat.2 + cBoundSq.2 +
      cRaw.2 + pi2S.2 + sqrtPiRaw.2 + (4 * w * w + 20 * w + 16)
    (ScheduleIntTree.node K p B_in m1 tapTbl.1 preTbl.1 postTbl.1 c0Tbl.1 c1Tbl.1 child.1,
      hoistCost + tapTbl.2 + preTbl.2 + postTbl.2 + c0Tbl.2 + c1Tbl.2 + child.2)
  else
    let qBase := qBaseEll K p
    let wLeaf := 100 * qBase
    let smulLeaf := signedMulFromTrackedBitMul wLeaf (subMulBits wLeaf)
    let piLeaf := approxPiFixedTracked wLeaf (qBase + 10)
    let leafTbl := memoizeFinTracked (fun u : Fin (2 ^ K) =>
      expTwoPiIFixedWithMulTracked smulLeaf wLeaf qBase piLeaf.1 (u.val : ℤ) (2 ^ K))
    (ScheduleIntTree.leaf K p B_in leafTbl.1, piLeaf.2 + leafTbl.2 + 2)
termination_by K
decreasing_by
  unfold k2Ell
  omega

private theorem scheduleIntTree_node_congr {K p B_in m1 : ℕ}
    {t1 t2 : Fin (t1Ell K) → ℤ → ℤ}
    {pre1 pre2 post1 post2 : Fin (rEll K) → FixedComplex (qChildEll K p)}
    {c0_1 c0_2 c1_1 c1_2 : Fin (rEll K) → ℤ}
    {ch1 ch2 : ScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)}
    (ht : t1 = t2) (hpre : pre1 = pre2) (hpost : post1 = post2)
    (hc0 : c0_1 = c0_2) (hc1 : c1_1 = c1_2) (hch : ch1 = ch2) :
    ScheduleIntTree.node K p B_in m1 t1 pre1 post1 c0_1 c1_1 ch1 =
      ScheduleIntTree.node K p B_in m1 t2 pre2 post2 c0_2 c1_2 ch2 := by
  subst ht hpre hpost hc0 hc1 hch; rfl

/-- Whenever `subMulBits w` agrees with bit-encoded natural multiplication on `.1` for `w`-bit
operands (`a < 2 ^ w`, `b < 2 ^ w`), the first projection of
`computeScheduleIntTreeWithMulTracked subMulBits` equals `computeScheduleIntTree`. -/
@[simp]
theorem computeScheduleIntTreeWithMulTracked_fst_of_mul_eq
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool))
    (hmul : ∀ w a b : ℕ, a < 2 ^ w → b < 2 ^ w →
      (subMulBits w (encodeNatBits w a) (encodeNatBits w b)).1 = encodeNatBits (2 * w) (a * b))
    (K : ℕ) :
    ∀ p B_in : ℕ,
      (computeScheduleIntTreeWithMulTracked subMulBits K p B_in).1 =
        computeScheduleIntTree K p B_in := by
  have hsmul : ∀ w : ℕ, ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y →
      (signedMulFromTrackedBitMul w (subMulBits w) x y).1 = x * y :=
    fun w _ _ hx hy => signedMulFromTrackedBitMul_fst_of_bitMul_eq w (subMulBits w) (hmul w) hx hy
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [computeScheduleIntTreeWithMulTracked, computeScheduleIntTree]
    split_ifs with hcond
    · have hK2 : 2 ≤ K := hcond.2
      have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      let q := qChildEll K p; let w := 1000 * q; let pW := pWorkEll K p
      let S_ghat := q + 2 * pW + 20
      have hq_eq : q = p + 2 * K + 14 := by unfold q qChildEll pChildEll pWorkEll; omega
      have hpW_eq : pW = p + K + 6 := by unfold pW pWorkEll; rfl
      have hw_eq : w = 1000 * q := rfl
      have hS_eq : S_ghat = q + 2 * pW + 20 := rfl
      have hcBound_lt : 3 * pW < 4 ^ w := (lt_of_le_of_lt (by omega : 3 * pW ≤ w)
        Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by decide) w)
      have hpW_pow : 4 * pW < 2 ^ S_ghat :=
        lt_of_le_of_lt (by omega : 4 * pW ≤ 4 * S_ghat) (four_mul_lt_two_pow (by omega))
      have hcRaw_lt := toNat_max_zero_four_mul_l2GHat_div_lt_four_pow pW S_ghat w hpW_pow (by omega)
      have hsqrtPi_lt :=
        toNat_max_zero_approxPiFixed_div_lt_four_pow (2 * S_ghat) (6 * S_ghat + 18) w (by omega)
      have h2r_le : 2 * rEll K ≤ 2 ^ q := by
        have hr_le : rEll K ≤ 2 ^ K := rEll_le_two_pow K
        calc 2 * rEll K ≤ 2 ^ (K + 1) := by rw [Nat.pow_succ']; omega
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by omega)
      dsimp only
      refine scheduleIntTree_node_congr ?_ ?_ ?_ ?_ ?_
        (ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in))
      · rw [memoizeFilterTapTracked_fst]
        refine congrArg (memoizeFilterTap (computeM1Ell K p)) (funext fun j1 => funext fun d => ?_)
        rw [approxPiFixedTracked_fst, approxLogTwoFixedTracked_fst]
        exact computeFilterTapEntryTracked_fst _ w K p hK2 (le_refl w) (hsmul w) j1 d
      · rw [memoizeFinTracked_fst, memoizeFin_eq]; funext k2
        rw [approxPiFixedTracked_fst]
        exact expTwoPiIFixedWithMulTracked_fst _ w q (k2.val : ℤ) (2 * rEll K)
          (by omega) (by omega) h2r_le (hsmul w)
      · rw [memoizeFinTracked_fst, memoizeFin_eq]; funext k2
        rw [approxPiFixedTracked_fst]
        exact expTwoPiIFixedWithMulTracked_fst _ w q (-(k2.val : ℤ)) (2 * rEll K)
          (by omega) (by omega) h2r_le (hsmul w)
      · rw [memoizeFinTracked_fst, memoizeFin_eq]; funext u2
        rw [approxLogTwoFixedTracked_fst,
          binaryRestoringSqrtRegTracked_fst_fst hcBound_lt,
          approxSqrtFixedTracked_fst hcRaw_lt,
          approxPiFixedTracked_fst,
          approxSqrtFixedTracked_fst hsqrtPi_lt]
        exact computeGHatMantissaEntryTracked_fst _ w K p hK2 (le_refl w) (hsmul w)
          (u2.val : ℤ) (Nat.cast_nonneg u2.val) (by exact_mod_cast le_of_lt u2.isLt)
      · rw [memoizeFinTracked_fst, memoizeFin_eq]; funext u2
        have hu2 : (u2.val : ℤ) < (rEll K : ℤ) := by exact_mod_cast u2.isLt
        rw [approxLogTwoFixedTracked_fst,
          binaryRestoringSqrtRegTracked_fst_fst hcBound_lt,
          approxSqrtFixedTracked_fst hcRaw_lt,
          approxPiFixedTracked_fst,
          approxSqrtFixedTracked_fst hsqrtPi_lt]
        exact computeGHatMantissaEntryTracked_fst _ w K p hK2 (le_refl w) (hsmul w)
          ((rEll K : ℤ) - (u2.val : ℤ)) (by omega) (by omega)
    · let qBase := qBaseEll K p; let wLeaf := 100 * qBase
      have hqBase_eq : qBase = p + K + 4 := rfl
      have h2K_le : 2 ^ K ≤ 2 ^ qBase := Nat.pow_le_pow_right (by decide) (by omega)
      dsimp only
      refine congrArg (ScheduleIntTree.leaf K p B_in) ?_
      rw [memoizeFinTracked_fst, memoizeFin_eq]; funext u
      rw [approxPiFixedTracked_fst]
      exact expTwoPiIFixedWithMulTracked_fst _ wLeaf qBase (u.val : ℤ) (2 ^ K)
        (by omega) (le_refl wLeaf) h2K_le (hsmul wLeaf)

theorem computeScheduleIntTreeWithMulTracked_root_fst_of_mul_eq
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool))
    (hmul : ∀ w a b : ℕ, a < 2 ^ w → b < 2 ^ w →
      (subMulBits w (encodeNatBits w a) (encodeNatBits w b)).1 = encodeNatBits (2 * w) (a * b))
    (n : ℕ) :
    (computeScheduleIntTreeWithMulTracked subMulBits
      (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)).1 =
      computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0) :=
  computeScheduleIntTreeWithMulTracked_fst_of_mul_eq subMulBits hmul
    (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)

theorem norm_nyquistModeSum_le (K : ℕ) (x : Fin (2 ^ K) → ℂ) :
    ‖nyquistModeSum K x‖ ≤ vecInfNorm x := by
  unfold nyquistModeSum
  rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_natCast]
  have hr_pos : (0 : ℝ) < (rEll K : ℝ) := Nat.cast_pos.mpr (rEll_pos K)
  have hsum : ‖∑ j2 : Fin (rEll K),
      ((-1 : ℂ) ^ j2.val) *
        x ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩‖ ≤
      (rEll K : ℝ) * vecInfNorm x := by
    calc ‖∑ j2 : Fin (rEll K), _‖
        ≤ ∑ j2 : Fin (rEll K), ‖((-1 : ℂ) ^ j2.val) *
            x ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j2 : Fin (rEll K), vecInfNorm x := by
          refine Finset.sum_le_sum (fun j2 _ => ?_)
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact norm_le_vecInfNorm x _
      _ = (rEll K : ℝ) * vecInfNorm x := by simp [nsmul_eq_mul]
  calc (1 / (rEll K : ℝ)) * _
      ≤ (1 / (rEll K : ℝ)) * ((rEll K : ℝ) * vecInfNorm x) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = vecInfNorm x := by field_simp

theorem wordWidthBounds_of_approx_norm_le_one {q : ℕ} {z : FixedComplex q} {w : ℂ}
    (hw : ‖w‖ ≤ 1) (herr : ‖z.toComplex - w‖ ≤ 1) :
    WordWidthBounds (q + 2) z := by
  have hz : ‖z.toComplex‖ ≤ (2 : ℝ) ^ 1 := by
    have htri := norm_add_le (z.toComplex - w) w
    rw [sub_add_cancel] at htri
    norm_num
    linarith
  exact (wordWidthBounds_of_norm_toComplex_le hz).mono (by omega)

theorem fitsSignedWord_of_approx_le_one {q : ℕ} (hq : 2 ≤ q) {m : ℤ} {c : ℝ}
    (hm_nn : 0 ≤ m) (hc_le : c ≤ 1)
    (herr : |(m : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - c| ≤ 1) :
    FitsSignedWord (2 * q) m := by
  have h1 : (m : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) ≤ 2 := by
    have := (abs_sub_le_iff.mp herr).1
    linarith
  have h2 : (m : ℝ) ≤ 2 * (2 : ℝ) ^ q := by
    calc (m : ℝ) = ((m : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * (2 : ℝ) ^ q := by
          rw [mul_assoc, mul_comm ((2 : ℝ) ^ (-(q : ℤ))), two_pow_mul_two_zpow_neg, mul_one]
      _ ≤ 2 * (2 : ℝ) ^ q := mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : m ≤ 2 * (2 : ℤ) ^ q := by exact_mod_cast h2
  have h4 : |m| ≤ (2 : ℤ) ^ (q + 1) := by
    rw [abs_of_nonneg hm_nn, pow_succ']
    exact h3
  exact fitsSignedWord_of_abs_le_two_pow (by omega) h4

theorem baseRadix2FFTFixedWithMul_eq_baseRadix2FFTFixed_of_bounds (smul : ℤ → ℤ → ℤ)
    (K p : ℕ)
    (hsmul : ∀ x y : ℤ, FitsSignedWord (6 * qBaseEll K p) x →
      FitsSignedWord (6 * qBaseEll K p) y → smul x y = x * y)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (htw : ∀ u : Fin (2 ^ K), WordWidthBounds (qBaseEll K p + 2) (leafTwiddles u))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : ∀ j : Fin (2 ^ K), WordWidthBounds (2 * qBaseEll K p)
      (FixedComplex.rescale (qBaseEll K p) (xFixed j))) :
    baseRadix2FFTFixedWithMul smul K p leafTwiddles xFixed =
      baseRadix2FFTFixed K p leafTwiddles xFixed := by
  funext u
  unfold baseRadix2FFTFixed baseRadix2FFTFixedWithMul
  simp only [memoizeFin_eq]
  have h1 := (radix2FFT1DFixedWithMul_eq_and_bounds smul K (qBaseEll K p)
    (2 * qBaseEll K p) (6 * qBaseEll K p) hsmul leafTwiddles htw
    (by unfold qBaseEll; omega) K (le_refl K)
    (fun j => FixedComplex.rescale (qBaseEll K p) (xFixed j)) hx
    (by unfold qBaseEll; omega) (by unfold qBaseEll; omega)).1
  rw [h1, radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl)]

/-- **Intrinsically Operation-Tracking Multi-Level Recursive `FastDFT`
(`computableFastDFTRecursiveWithMulTracked`)**:
Routes Step 1 blocked Kronecker Overlap-Add products directly to the bit-list sub-multiplier
`subMulBits wKron : List Bool → List Bool → CostM (List Bool)` via
`kroneckerMatrixSpreadFixedWithMulTracked` (using $O(m \cdot B_{\text{slot}})$ bit-list two's-complement
slot packing and unpacking, Lemma 6.2 (`lem:kronecker`)), and routes all Step 2/Step 3/leaf
fixed-point multiplications to `signedMulFromTrackedBitMul`. -/
def computableFastDFTRecursiveWithMulTracked
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool))
    {K p B_in : ℕ} (tree : ScheduleIntTree K p B_in)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    CostM (Fin (2 ^ K) → FixedComplex (p + 2)) :=
  match tree with
  | .leaf K p _B_in leafTwiddles =>
    let smulLeaf := signedMulFromTrackedBitMul (6 * qBaseEll K p) (subMulBits (6 * qBaseEll K p))
    baseRadix2FFTFixedWithMulTracked smulLeaf K p leafTwiddles xFixed
  | .node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child =>
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let B_slot := scheduleSlotBits K p B_in m1
    let W_tilde := foldedHalfWidth m1 r
    let wKron := kroneckerPackedBitLength W_tilde B_slot
    let smulChild := signedMulFromTrackedBitMul (10 * qChild) (subMulBits (10 * qChild))
    have hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    have ht1_pos : 0 < t1 := t1Ell_pos K
    have hr_pos : 0 < r := rEll_pos K
    haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
    have hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let U_gathered := memoizeFin2Tracked (fun (j1 : Fin t1) (j2 : Fin r) =>
      let rs := FixedComplex.rescaleTracked qChild (oddStrideGather t1 r hR_pos xFixed j1 j2)
      (rs.1, rs.2 + (2 * qChild + 4) * (k1Ell K + 1)))
    let U_spreadFixed := kroneckerMatrixSpreadFixedWithMulTracked (subMulBits wKron)
      t1 r m1 B_slot qChild qChild hr_pos U_gathered.1 filterTap
    let U_preFixed := memoizeFin2Tracked (fun (j1 : Fin t1) (k2 : Fin r) =>
      FixedComplex.mulRoundedWithTracked smulChild (preTwistRoot k2) (U_spreadFixed.1 j1 k2))
    let Q_synFixed := radix2SyntheticFFTFixedTracked (k1Ell K) c1 U_preFixed.1
    let Q_postFixed := memoizeFin2Tracked (fun (v1 : Fin t1) (k2 : Fin r) =>
      FixedComplex.mulRoundedWithTracked smulChild (postTwistRoot k2) (Q_synFixed.1 v1 k2))
    let Q_hatRows := memoizeFinTracked (fun v1 : Fin t1 =>
      computableFastDFTRecursiveWithMulTracked subMulBits child (Q_postFixed.1 v1))
    let Y_matFixed := memoizeFin2Tracked (fun (m : Fin t1) (u2 : Fin r) =>
      (oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hatRows.1 m u2,
        (4 * qChild + 8) * (k1Ell K + 1)))
    let altFixed := nyquistModeSumFixedTracked K p xFixed
    let Z_colsRows := memoizeFinTracked (fun u2 : Fin r =>
      if u2.val = r / 2 then
        nyquistColumnSolveFixedWithMulTracked smulChild (c0Mantissa u2)
          (fun m => Y_matFixed.1 m u2) altFixed.1
      else
        cyclicBidiagPrevSolveFixedWithMulTracked smulChild (c0Mantissa u2) (c1Mantissa u2)
          (fun m => Y_matFixed.1 m u2))
    let Z_matFixed := memoizeFin2Tracked (fun (u1 : Fin t1) (u2 : Fin r) =>
      (Z_colsRows.1 u2 u1, (2 * qChild + 4) * (k1Ell K + 1)))
    let outVec := memoizeFinTracked (fun u : Fin (2 ^ K) =>
      let rs := FixedComplex.rescaleTracked (p + 2) (freqScatter t1 r hR_eq Z_matFixed.1 u)
      (rs.1, rs.2 + (2 * qChild + 4) * (k1Ell K + 1)))
    (outVec.1,
      U_gathered.2 + U_spreadFixed.2 + U_preFixed.2 + Q_synFixed.2 + Q_postFixed.2 +
      Q_hatRows.2 + Y_matFixed.2 + altFixed.2 + Z_colsRows.2 + Z_matFixed.2 + outVec.2)

/-- Whenever `subMulBits w` agrees with bit-encoded natural multiplication on `< 2^w` operands, the
first projection of `computableFastDFTRecursiveWithMulTracked subMulBits` equals
`computableFastDFTRecursive` on any valid schedule tree. -/
theorem computableFastDFTRecursiveWithMulTracked_fst_of_mul_eq
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool))
    (hmul : ∀ w a b : ℕ, a < 2 ^ w → b < 2 ^ w →
      (subMulBits w (encodeNatBits w a) (encodeNatBits w b)).1 = encodeNatBits (2 * w) (a * b))
    {K p B_in : ℕ} {tree : ScheduleIntTree K p B_in}
    (htree : ValidScheduleIntTree tree) :
    ∀ (_hp : 8 ≤ p) (_hB_in : B_in ≤ p)
      (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
      (_hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in),
      (computableFastDFTRecursiveWithMulTracked subMulBits tree xFixed).1 =
        computableFastDFTRecursive tree xFixed := by
  have hsmul : ∀ w : ℕ, ∀ x y : ℤ, FitsSignedWord w x → FitsSignedWord w y →
      (signedMulFromTrackedBitMul w (subMulBits w) x y).1 = x * y :=
    fun w _ _ hxw hyw => signedMulFromTrackedBitMul_fst_of_bitMul_eq w (subMulBits w) (hmul w) hxw hyw
  have hsmul_std : ∀ x y : ℤ, signedMulFromNatMul (· * ·) x y = x * y :=
    signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
  induction htree with
  | leaf K p B_in leafTwiddles _hcond hroots =>
    intro hp hB_in xFixed hx
    unfold computableFastDFTRecursiveWithMulTracked computableFastDFTRecursive
    dsimp only
    rw [baseRadix2FFTFixedWithMulTracked_fst]
    apply baseRadix2FFTFixedWithMul_eq_baseRadix2FFTFixed_of_bounds _ K p
      (hsmul (6 * qBaseEll K p)) leafTwiddles
    · intro u
      apply wordWidthBounds_of_approx_norm_le_one (norm_expTwoPiI _).le
      have h1 : (2 : ℝ) ^ (-(qBaseEll K p : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      linarith [hroots u]
    · intro j
      rw [FixedComplex.rescale_eq_quantizeComplexFixed]
      exact (wordWidthBounds_quantizeComplexFixed_of_vecInfNorm_le K (qBaseEll K p) B_in
        (fun j => (xFixed j).toComplex) hx j).mono (by unfold qBaseEll; omega)
  | node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child
      hcond hm1_ge hm1_le htap_fits htap_abs htap_err hpre_err hpost_err hc0_nn hc1_nn
      hc0_err hc1_err hchild ih =>
    intro hp hB_in xFixed hx
    have hK2 : 2 ≤ K := hcond.2
    have hnot_leaf : ¬ isBaseLeaf K p = true := by
      have h := hcond.1; simpa using h
    have hpChild : 8 ≤ pChildEll K p := by unfold pChildEll pWorkEll; omega
    have hB_child : childScheduleBIn K p B_in ≤ pChildEll K p :=
      childScheduleBIn_le_pChildEll_of_not_isBaseLeaf hnot_leaf hB_in
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let pChild := pChildEll K p
    let B_slot := scheduleSlotBits K p B_in m1
    let W_tilde := foldedHalfWidth m1 r
    let wKron := kroneckerPackedBitLength W_tilde B_slot
    let wChild := 10 * qChild
    have hr_pos : 0 < r := rEll_pos K
    have ht1_pos : 0 < t1 := t1Ell_pos K
    have hq_one : (2 : ℝ) ^ (-(qChildEll K p : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hpre_bds : ∀ k2 : Fin r, WordWidthBounds (qChild + 2) (preTwistRoot k2) := fun k2 =>
      wordWidthBounds_of_approx_norm_le_one (norm_zetaPow _ _).le
        (by linarith [hpre_err k2])
    have hpost_bds : ∀ k2 : Fin r, WordWidthBounds (qChild + 2) (postTwistRoot k2) := fun k2 =>
      wordWidthBounds_of_approx_norm_le_one (norm_zetaPow _ _).le
        (by linarith [hpost_err k2])
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r (Nat.two_pow_pos K) (fun j => FixedComplex.rescale qChild (xFixed j))
    have hbit_kron : ∀ as bs : List Bool,
        as.length = 3 * foldedHalfWidth m1 r * B_slot →
        bs.length = 3 * foldedHalfWidth m1 r * B_slot →
        decodeNatBits (subMulBits wKron as bs).1 = decodeNatBits as * decodeNatBits bs := by
      intro as bs has hbs
      have has_lt : decodeNatBits as < 2 ^ wKron := by
        simpa [wKron, kroneckerPackedBitLength, has] using decodeNatBits_lt as
      have hbs_lt : decodeNatBits bs < 2 ^ wKron := by
        simpa [wKron, kroneckerPackedBitLength, hbs] using decodeNatBits_lt bs
      have has_enc : encodeNatBits wKron (decodeNatBits as) = as := by
        simpa [wKron, kroneckerPackedBitLength, has] using encodeNatBits_decodeNatBits as
      have hbs_enc : encodeNatBits wKron (decodeNatBits bs) = bs := by
        simpa [wKron, kroneckerPackedBitLength, hbs] using encodeNatBits_decodeNatBits bs
      have hprod_lt : decodeNatBits as * decodeNatBits bs < 2 ^ (2 * wKron) := by
        rw [Nat.two_mul, pow_add]
        exact Nat.mul_lt_mul'' has_lt hbs_lt
      rw [← has_enc, ← hbs_enc, hmul wKron (decodeNatBits as) (decodeNatBits bs) has_lt hbs_lt,
        has_enc, hbs_enc, decodeNatBits_encodeNatBits (2 * wKron) _ hprod_lt]
    have hspread :
        (kroneckerMatrixSpreadFixedWithMulTracked (subMulBits wKron)
          t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap).1 =
        kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
          t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap :=
      (kroneckerMatrixSpreadFixedWithMulTracked_fst_of_bitMul_eq (subMulBits wKron)
        t1 r m1 B_slot qChild qChild hr_pos hbit_kron U_gathered filterTap).trans
        (kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq _ hsmul_std
          t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap).symm
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
        t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap
    have hstep2 := computableFastDFTRecursive_step2_bounds hp hm1_ge hm1_le filterTap
      htap_fits htap_abs htap_err preTwistRoot postTwistRoot hpre_err hpost_err xFixed hx
    have hU_spread_bds : ∀ j1 k2, WordWidthBounds (3 * qChild) (U_spreadFixed j1 k2) := by
      intro j1 k2
      have hnorm : ‖(U_spreadFixed j1 k2).toComplex‖ ≤
          (((2 * m1 + 1 : ℕ) : ℝ) + 1) * max 1 (vecInfNorm (fun j => (xFixed j).toComplex)) :=
        (norm_le_matInfNorm (fun i1 i2 => (U_spreadFixed i1 i2).toComplex) j1 k2).trans hstep2.1
      have hW_pow : ((2 * m1 + 1 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ pChild := by
        have h1 : 2 * m1 + 2 ≤ 2 * (pChild + 1) := by omega
        have h2 : pChild + 1 ≤ 2 ^ (pChild - 1) := by
          have := @Nat.lt_two_pow_self (pChild - 2)
          have hpow : 2 ^ (pChild - 1) = 2 * 2 ^ (pChild - 2) := by
            conv_lhs => rw [show pChild - 1 = (pChild - 2) + 1 by omega, pow_succ']
          omega
        have h3 : 2 * m1 + 2 ≤ 2 ^ pChild := by
          calc 2 * m1 + 2 ≤ 2 * (pChild + 1) := h1
            _ ≤ 2 * 2 ^ (pChild - 1) := Nat.mul_le_mul_left 2 h2
            _ = 2 ^ pChild := by
                conv_rhs => rw [show pChild = (pChild - 1) + 1 by omega, pow_succ']
        exact_mod_cast h3
      have hM_pow : max 1 (vecInfNorm (fun j => (xFixed j).toComplex)) ≤ (2 : ℝ) ^ pChild := by
        refine max_le (one_le_pow₀ (by norm_num)) (hx.trans ?_)
        exact pow_le_pow_right₀ (by norm_num) (hB_in.trans (by unfold pChild pChildEll pWorkEll; omega))
      have hprod : ‖(U_spreadFixed j1 k2).toComplex‖ ≤ (2 : ℝ) ^ (2 * pChild) := by
        calc ‖(U_spreadFixed j1 k2).toComplex‖
            ≤ (2 : ℝ) ^ pChild * (2 : ℝ) ^ pChild :=
              hnorm.trans (mul_le_mul hW_pow hM_pow (by positivity) (by positivity))
          _ = (2 : ℝ) ^ (2 * pChild) := by rw [← pow_add, Nat.two_mul]
      exact (wordWidthBounds_of_norm_toComplex_le hprod).mono (by unfold qChild qChildEll pChild; omega)
    have hpre_mul :
        (fun j1 k2 => FixedComplex.mulRoundedWith
          (fun x y => (signedMulFromTrackedBitMul wChild (subMulBits wChild) x y).1)
          (preTwistRoot k2) (U_spreadFixed j1 k2)) =
        (fun j1 k2 => FixedComplex.mulRounded (preTwistRoot k2) (U_spreadFixed j1 k2)) := by
      funext j1 k2
      exact FixedComplex.mulRoundedWith_eq_mulRounded_of_bounds _ (hsmul wChild)
        ((hpre_bds k2).mono (by unfold wChild qChild qChildEll; omega))
        ((hU_spread_bds j1 k2).mono (by unfold wChild; omega))
    let U_preFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun j1 k2 => FixedComplex.mulRounded (preTwistRoot k2) (U_spreadFixed j1 k2)
    have hU_pre_bds : ∀ j1 k2, WordWidthBounds (3 * qChild + 4) (U_preFixed j1 k2) := by
      intro j1 k2
      exact (WordWidthBounds.mulRounded_sub_left (hpre_bds k2)
        (hU_spread_bds j1 k2)).mono (by unfold qChild qChildEll; omega)
    let Q_synFixed : Fin t1 → Fin r → FixedComplex qChild :=
      radix2SyntheticFFTFixed (k1Ell K) c1 U_preFixed
    have hQ_syn_bds : ∀ v1 k2, WordWidthBounds (3 * qChild + 4) (Q_synFixed v1 k2) :=
      wordWidthBounds_radix2SyntheticFFTFixed (by omega) (k1Ell K) c1 U_preFixed hU_pre_bds
    let Q_postFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun v1 k2 => FixedComplex.mulRounded (postTwistRoot k2) (Q_synFixed v1 k2)
    have hchild_eq :
        (fun v1 : Fin t1 =>
          (computableFastDFTRecursiveWithMulTracked subMulBits child
            (fun k2 : Fin r => FixedComplex.mulRoundedWith
              (fun x y => (signedMulFromTrackedBitMul wChild (subMulBits wChild) x y).1)
              (postTwistRoot k2) (Q_synFixed v1 k2))).1) =
        (fun v1 : Fin t1 => computableFastDFTRecursive child (Q_postFixed v1)) := by
      funext v1
      have hrow :
          (fun k2 : Fin r => FixedComplex.mulRoundedWith
            (fun x y => (signedMulFromTrackedBitMul wChild (subMulBits wChild) x y).1)
            (postTwistRoot k2) (Q_synFixed v1 k2)) = Q_postFixed v1 := by
        funext k2
        exact FixedComplex.mulRoundedWith_eq_mulRounded_of_bounds _ (hsmul wChild)
          ((hpost_bds k2).mono (by unfold wChild qChild qChildEll; omega))
          ((hQ_syn_bds v1 k2).mono (by unfold wChild qChild qChildEll; omega))
      rw [hrow]
      exact ih hpChild hB_child (Q_postFixed v1) (hstep2.2.2.2 v1)
    let Q_hatFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun v1 => computableFastDFTRecursive child (Q_postFixed v1)
    let Y_matFixed : Fin t1 → Fin r → FixedComplex qChild :=
      oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hatFixed
    have hY_bds : ∀ (m : Fin t1) (u2 : Fin r), WordWidthBounds (3 * qChild) (Y_matFixed m u2) := by
      intro m u2
      let v1 : Fin t1 := oddColKeyMinusInv t1 ht1_pos u2.val m
      change WordWidthBounds (3 * qChild) (Q_hatFixed v1 u2)
      have hacc := (norm_le_vecInfNorm _ u2).trans
        (vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow hchild hpChild
          (Q_postFixed v1) (hstep2.2.2.2 v1))
      have hdft := (norm_normDFT1D_le (fun k2 => (Q_postFixed v1 k2).toComplex) u2).trans
        (hstep2.2.2.2 v1)
      have hp_one : (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      have hmax_B : max 1 (vecInfNorm (fun k2 => (Q_postFixed v1 k2).toComplex)) ≤
          (2 : ℝ) ^ (childScheduleBIn K p B_in) :=
        max_le (one_le_pow₀ (by norm_num)) (hstep2.2.2.2 v1)
      have hnorm : ‖(Q_hatFixed v1 u2).toComplex‖ ≤ (2 : ℝ) ^ (pChild + 1) := by
        have htri := norm_add_le
          ((Q_hatFixed v1 u2).toComplex - normDFT1D (fun k2 => (Q_postFixed v1 k2).toComplex) u2)
          (normDFT1D (fun k2 => (Q_postFixed v1 k2).toComplex) u2)
        rw [sub_add_cancel] at htri
        have hsum : ‖(Q_hatFixed v1 u2).toComplex‖ ≤ 2 * (2 : ℝ) ^ (childScheduleBIn K p B_in) := by
          have hm := mul_le_mul hp_one hmax_B (by positivity) zero_le_one
          change ‖(Q_hatFixed v1 u2).toComplex - normDFT1D (fun k2 => (Q_postFixed v1 k2).toComplex) u2‖ ≤
            (2 : ℝ) ^ (-(pChild : ℤ)) * max 1 (vecInfNorm (fun k2 => (Q_postFixed v1 k2).toComplex)) at hacc
          linarith
        calc ‖(Q_hatFixed v1 u2).toComplex‖
            ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in + 1) := by
              rw [pow_succ']; exact hsum
          _ ≤ (2 : ℝ) ^ (pChild + 1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
      exact (wordWidthBounds_of_norm_toComplex_le hnorm).mono (by unfold qChild qChildEll pChild; omega)
    have halt_bds : WordWidthBounds (3 * qChild) (nyquistModeSumFixed K p xFixed) := by
      rw [nyquistModeSumFixed_eq_quantizeComplexFixed]
      have hnyq : ‖nyquistModeSum K (fun j => (xFixed j).toComplex)‖ ≤ (2 : ℝ) ^ B_in :=
        (norm_nyquistModeSum_le K (fun j => (xFixed j).toComplex)).trans hx
      exact (wordWidthBounds_quantizeComplexFixed_of_norm_le hnyq).mono
        (by unfold qChild qChildEll pChildEll pWorkEll; omega)
    have hc0_bds : ∀ u2 : Fin r, FitsSignedWord (2 * qChild) (c0Mantissa u2) := fun u2 => by
      have hc0_le1 : passbandC0 K p u2 ≤ 1 := by unfold passbandC0; exact gHat_le_one _ _
      exact fitsSignedWord_of_approx_le_one (by unfold qChild qChildEll pChildEll pWorkEll; omega)
        (hc0_nn u2) hc0_le1 (by linarith [hc0_err u2, hq_one])
    have hc1_bds : ∀ u2 : Fin r, FitsSignedWord (2 * qChild) (c1Mantissa u2) := fun u2 => by
      have hc1_le1 : passbandC1 K p u2 ≤ 1 := by unfold passbandC1; exact gHat_le_one _ _
      exact fitsSignedWord_of_approx_le_one (by unfold qChild qChildEll pChildEll pWorkEll; omega)
        (hc1_nn u2) hc1_le1 (by linarith [hc1_err u2, hq_one])
    have ht1_le : t1 ≤ 2 ^ qChild := t1Ell_le_two_pow_qChildEll K p
    unfold computableFastDFTRecursiveWithMulTracked computableFastDFTRecursive
    dsimp only
    simp only [memoizeFinTracked_fst, memoizeFin2Tracked_fst, memoizeFin_eq, memoizeFin2_eq,
      FixedComplex.rescaleTracked_fst, FixedComplex.mulRoundedWithTracked_fst,
      radix2SyntheticFFTFixedTracked_fst, nyquistModeSumFixedTracked_fst]
    have hgather :
        (fun (j1 : Fin t1) (j2 : Fin r) =>
          FixedComplex.rescale qChild
            (oddStrideGather t1 r (Nat.two_pow_pos K) xFixed j1 j2)) = U_gathered := rfl
    rw [hgather, hspread, hpre_mul, hchild_eq]
    haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
    funext u
    congr 1
    congr 1
    funext u1 u2
    split_ifs with hu2
    · exact congrFun (nyquistColumnSolveFixedWithMulTracked_fst _ (c0Mantissa u2)
        (fun m => Y_matFixed m u2) (nyquistModeSumFixed K p xFixed)
        (by unfold qChild qChildEll pChildEll pWorkEll; omega) ht1_le (fun m => hY_bds m u2) halt_bds
        (hsmul wChild)) u1
    · exact congrFun (cyclicBidiagPrevSolveFixedWithMulTracked_fst _ (c0Mantissa u2) (c1Mantissa u2)
        (fun m => Y_matFixed m u2) (by unfold qChild qChildEll pChildEll pWorkEll; omega) ht1_le
        (hc0_nn u2) (hc1_nn u2) (hc0_bds u2) (hc1_bds u2) (fun m => hY_bds m u2)
        (hsmul wChild)) u1

/-- **Intrinsically Operation-Tracking 2-Call Complex-Packed Convolution From Chunks
(`computableConvFromChunksWithMulTracked`)**. -/
def computableConvFromChunksWithMulTracked
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (aChunks bChunks : Fin (rootR0 n) → ℕ) : CostM (Fin (rootR0 n) → ℤ) :=
  let p0 := rootP0 n
  let R0 := rootR0 n
  let smulRoot := signedMulFromTrackedBitMul (2 * (p0 + 2)) (subMulBits (2 * (p0 + 2)))
  let zFixed := memoizeFinTracked (fun j : Fin R0 =>
    (packChunksFixed n (aChunks, bChunks) j, 2 * (p0 + 2) + 4))
  let dft1 := computableFastDFTRecursiveWithMulTracked subMulBits tree zFixed.1
  let W_conj := memoizeFinTracked (fun u : Fin R0 =>
    let z := dft1.1 u
    let p1 := smulRoot (2 * z.re) z.im
    let p2 := smulRoot z.im z.im
    let p3 := smulRoot z.re z.re
    let r1 := roundShiftIntTracked p1.1 (p0 + 3)
    let r2 := roundShiftIntTracked (p2.1 - p3.1) (p0 + 3)
    let c := FixedComplex.conjTracked (⟨r1.1, r2.1⟩ : FixedComplex (p0 + 2))
    (c.1, p1.2 + p2.2 + p3.2 + r1.2 + r2.2 + c.2 + 2 * p0 + 6))
  let dft2 := computableFastDFTRecursiveWithMulTracked subMulBits tree W_conj.1
  let C_inv := memoizeFinTracked (fun m : Fin R0 =>
    FixedComplex.conjTracked (dft2.1 m))
  let out := memoizeFinTracked (fun k : Fin R0 =>
    let rs := roundShiftIntTracked (C_inv.1 k).re 8
    (rs.1, rs.2 + p0 + 4))
  (out.1, zFixed.2 + dft1.2 + W_conj.2 + dft2.2 + C_inv.2 + out.2 + R0 + 4)

theorem vecInfNorm_packChunksFixed_le_sqrt_two (n : ℕ) (aChunks bChunks : Fin (rootR0 n) → ℕ) :
    vecInfNorm (fun j => (packChunksFixed n (aChunks, bChunks) j).toComplex) ≤ Real.sqrt 2 := by
  let p0 := rootP0 n
  let b := chunkBits n
  have hb_le : b ≤ p0 + 2 := by unfold b p0 rootP0; omega
  have hpow : (2 : ℝ) ^ (p0 + 2 - b) * (2 : ℝ) ^ b = (2 : ℝ) ^ (p0 + 2) := by
    rw [← pow_add, Nat.sub_add_cancel hb_le]
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) := zpow_pos (by norm_num) _
  apply vecInfNorm_le _ (by positivity)
  intro j
  have hre : |((packChunksFixed n (aChunks, bChunks) j).toComplex).re| ≤ 1 := by
    unfold packChunksFixed
    dsimp only
    rw [FixedComplex.toComplex_re, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
      abs_of_nonneg (by positivity)]
    have hlt : ((aChunks j % 2 ^ b : ℕ) : ℝ) ≤ (2 : ℝ) ^ b :=
      by exact_mod_cast le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos b))
    calc ((aChunks j % 2 ^ b : ℕ) : ℝ) * (2 : ℝ) ^ (p0 + 2 - b) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (p0 + 2 - b) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlt (by positivity)) h2_pos.le
      _ = (2 : ℝ) ^ (p0 + 2) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) := by rw [mul_comm ((2 : ℝ) ^ b), hpow]
      _ = 1 := two_pow_mul_two_zpow_neg (p0 + 2)
  have him : |((packChunksFixed n (aChunks, bChunks) j).toComplex).im| ≤ 1 := by
    unfold packChunksFixed
    dsimp only
    rw [FixedComplex.toComplex_im, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
      abs_of_nonneg (by positivity)]
    have hlt : ((bChunks j % 2 ^ b : ℕ) : ℝ) ≤ (2 : ℝ) ^ b :=
      by exact_mod_cast le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos b))
    calc ((bChunks j % 2 ^ b : ℕ) : ℝ) * (2 : ℝ) ^ (p0 + 2 - b) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (p0 + 2 - b) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlt (by positivity)) h2_pos.le
      _ = (2 : ℝ) ^ (p0 + 2) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) := by rw [mul_comm ((2 : ℝ) ^ b), hpow]
      _ = 1 := two_pow_mul_two_zpow_neg (p0 + 2)
  simpa using norm_complex_le_of_re_im_le zero_le_one hre him

theorem computableConvFromChunksWithMulTracked_fst_of_mul_eq
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool))
    (hmul : ∀ w a b : ℕ, a < 2 ^ w → b < 2 ^ w →
      (subMulBits w (encodeNatBits w a) (encodeNatBits w b)).1 = encodeNatBits (2 * w) (a * b))
    (n : ℕ)
    {tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)}
    (htree : ValidScheduleIntTree tree)
    (aChunks bChunks : Fin (rootR0 n) → ℕ) :
    (computableConvFromChunksWithMulTracked subMulBits n tree aChunks bChunks).1 =
      computableConvFromChunksWithMul (· * ·) n tree aChunks bChunks := by
  let p0 := rootP0 n
  let R0 := rootR0 n
  let B0 := levelScheduleBIn (rootK0 n) (rootP0 n) 0
  let wRoot := 2 * (p0 + 2)
  have hp0_ge18 : 18 ≤ p0 := rootP0_ge_eighteen n
  have hp0_ge8 : 8 ≤ p0 := by omega
  have hB0_le : B0 ≤ p0 := by change 2 ≤ p0; omega
  have hpow_B0 : (2 : ℝ) ^ B0 = 4 := by change (2 : ℝ) ^ 2 = 4; norm_num
  have hsmul : ∀ x y : ℤ, FitsSignedWord wRoot x → FitsSignedWord wRoot y →
      (signedMulFromTrackedBitMul wRoot (subMulBits wRoot) x y).1 =
        signedMulFromNatMul (· * ·) x y := by
    intro x y hxw hyw
    rw [signedMulFromTrackedBitMul_fst_of_bitMul_eq wRoot (subMulBits wRoot) (hmul wRoot) hxw hyw,
      signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)]
  set zFixed : Fin R0 → FixedComplex (p0 + 2) := packChunksFixed n (aChunks, bChunks)
  have hz_sqrt2 : vecInfNorm (fun j => (zFixed j).toComplex) ≤ Real.sqrt 2 :=
    vecInfNorm_packChunksFixed_le_sqrt_two n aChunks bChunks
  have hz_B0 : vecInfNorm (fun j => (zFixed j).toComplex) ≤ (2 : ℝ) ^ B0 := by
    rw [hpow_B0]; exact hz_sqrt2.trans (sqrt_two_le.trans (by norm_num))
  have hdft1 : (computableFastDFTRecursiveWithMulTracked subMulBits tree zFixed).1 =
      computableFastDFTRecursive tree zFixed :=
    computableFastDFTRecursiveWithMulTracked_fst_of_mul_eq subMulBits hmul htree hp0_ge8 hB0_le zFixed hz_B0
  set ZFixed : Fin R0 → FixedComplex (p0 + 2) := computableFastDFTRecursive tree zFixed
  have hZ_norm : ∀ u : Fin R0, ‖(ZFixed u).toComplex‖ ≤ 2 := by
    intro u
    have hacc := (norm_le_vecInfNorm _ u).trans
      (vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow htree hp0_ge8 zFixed hz_B0)
    have hdft := ((norm_normDFT1D_le (fun j => (zFixed j).toComplex) u).trans hz_sqrt2).trans sqrt_two_le
    have h2p0_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (1 / 16 : ℝ) := by
      calc (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (2 : ℝ) ^ (-4 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 1 / 16 := by norm_num
    have hmax : max 1 (vecInfNorm (fun j => (zFixed j).toComplex)) ≤ 4 := by
      rw [hpow_B0] at hz_B0; exact max_le (by norm_num) hz_B0
    have hm := mul_le_mul h2p0_le hmax (by positivity) (by positivity)
    have htri := norm_add_le
      ((ZFixed u).toComplex - normDFT1D (fun j => (zFixed j).toComplex) u)
      (normDFT1D (fun j => (zFixed j).toComplex) u)
    rw [sub_add_cancel] at htri
    change ‖(ZFixed u).toComplex - normDFT1D (fun j => (zFixed j).toComplex) u‖ ≤
      (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm (fun j => (zFixed j).toComplex)) at hacc
    linarith
  have hZ_bds : ∀ u : Fin R0, WordWidthBounds (p0 + 4) (ZFixed u) := fun u =>
    (wordWidthBounds_of_norm_toComplex_le (b := 1) (by simpa using hZ_norm u)).mono (by omega)
  have hW_eq :
      (fun u : Fin R0 =>
        (⟨roundShiftInt ((signedMulFromTrackedBitMul wRoot (subMulBits wRoot) (2 * (ZFixed u).re) (ZFixed u).im).1) (p0 + 3),
          roundShiftInt ((signedMulFromTrackedBitMul wRoot (subMulBits wRoot) (ZFixed u).im (ZFixed u).im).1 -
            (signedMulFromTrackedBitMul wRoot (subMulBits wRoot) (ZFixed u).re (ZFixed u).re).1) (p0 + 3)⟩ :
          FixedComplex (p0 + 2)).conj) =
      (fun u : Fin R0 =>
        (⟨roundShiftInt (signedMulFromNatMul (· * ·) (2 * (ZFixed u).re) (ZFixed u).im) (p0 + 3),
          roundShiftInt (signedMulFromNatMul (· * ·) (ZFixed u).im (ZFixed u).im -
            signedMulFromNatMul (· * ·) (ZFixed u).re (ZFixed u).re) (p0 + 3)⟩ :
          FixedComplex (p0 + 2)).conj) := by
    funext u
    have hre : FitsSignedWord wRoot (ZFixed u).re := (hZ_bds u).1.mono (by unfold wRoot; omega)
    have him : FitsSignedWord wRoot (ZFixed u).im := (hZ_bds u).2.mono (by unfold wRoot; omega)
    have h2re : FitsSignedWord wRoot (2 * (ZFixed u).re) := by
      have h : 2 * (ZFixed u).re = (ZFixed u).re * (2 : ℤ) ^ 1 := by ring
      rw [h]
      exact ((hZ_bds u).1.mul_two_pow 1).mono (by unfold wRoot p0 rootP0; omega)
    simp only [hsmul (2 * (ZFixed u).re) (ZFixed u).im h2re him,
      hsmul (ZFixed u).im (ZFixed u).im him him,
      hsmul (ZFixed u).re (ZFixed u).re hre hre]
  set W_conjFixed : Fin R0 → FixedComplex (p0 + 2) := fun u =>
    (⟨roundShiftInt (signedMulFromNatMul (· * ·) (2 * (ZFixed u).re) (ZFixed u).im) (p0 + 3),
      roundShiftInt (signedMulFromNatMul (· * ·) (ZFixed u).im (ZFixed u).im -
        signedMulFromNatMul (· * ·) (ZFixed u).re (ZFixed u).re) (p0 + 3)⟩ :
      FixedComplex (p0 + 2)).conj
  have hW_B0 : vecInfNorm (fun u => (W_conjFixed u).toComplex) ≤ (2 : ℝ) ^ B0 := by
    rw [hpow_B0]
    apply vecInfNorm_le _ (by norm_num)
    intro u
    have hsmul_std : ∀ x y : ℤ, signedMulFromNatMul (· * ·) x y = x * y :=
      signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
    have htoC : (W_conjFixed u).toComplex =
        starRingEnd ℂ (quantizeComplex (p0 + 2) (((ZFixed u).toComplex * (ZFixed u).toComplex) / (2 * Complex.I))) := by
      dsimp only [W_conjFixed]
      simp only [hsmul_std]
      exact toComplex_freqSquareConjFixed (ZFixed u)
    rw [htoC, RCLike.norm_conj]
    set w : ℂ := ((ZFixed u).toComplex * (ZFixed u).toComplex) / (2 * Complex.I)
    have hw_le : ‖w‖ ≤ 2 := by
      dsimp [w]
      rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      have hsq : ‖(ZFixed u).toComplex‖ * ‖(ZFixed u).toComplex‖ ≤ 4 := by
        nlinarith [hZ_norm u, norm_nonneg (ZFixed u).toComplex]
      linarith
    have hq := norm_quantizeComplex_sub_self_le (p0 + 2) w
    have h2p : (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hsqrt := sqrt_two_le
    have hq1 : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) ≤ 1 := by
      nlinarith [hsqrt, h2p, zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((p0 + 2 : ℕ) : ℤ))]
    have htri := norm_add_le (quantizeComplex (p0 + 2) w - w) w
    rw [sub_add_cancel] at htri
    linarith
  have hdft2 : (computableFastDFTRecursiveWithMulTracked subMulBits tree W_conjFixed).1 =
      computableFastDFTRecursive tree W_conjFixed :=
    computableFastDFTRecursiveWithMulTracked_fst_of_mul_eq subMulBits hmul htree hp0_ge8 hB0_le W_conjFixed hW_B0
  unfold computableConvFromChunksWithMulTracked computableConvFromChunksWithMul
  dsimp only
  simp only [memoizeFinTracked_fst, memoizeFin_eq,
    computableFastDFTRecursiveWithMul_eq_of_mul_eq (· * ·) (fun _ _ => rfl),
    roundShiftIntTracked_fst, FixedComplex.conjTracked_fst]
  rw [hdft1, hW_eq, hdft2]

/-- **Depth-Bounded Self-Recursive Operation-Tracking Bit-List Multiplication
(`computableNatMulBitsAuxTracked`)**:
- At bootstrap depth `d = 0`, executes `binaryShiftAddMulBitsTracked w aBits bBits` (pure bit-list
  shift-and-add multiplication over `w` bit steps, with **zero** calls to Lean's built-in `(· * ·)`
  and **zero** `ℕ` conversions).
- At depth `d + 1`, when `1 ≤ w`, slices `aBits.take w` and `bBits.take w` into base-$2^b$ chunks via
  `sliceBitChunkFnTracked` ($O(w)$ bit operations), generates the integer schedule tree via
  `computeScheduleIntTreeWithMulTracked`, executes `computableConvFromChunksWithMulTracked` routing
  every sub-multiplication `(w', xs, ys)` to `computableNatMulBitsAuxTracked d w' xs ys`, and emits
  the $2w$-bit product bit-list via single-pass base-$2^b$ carry-save `carrySaveEmitBitsTracked`
  ($O(w)$ bit operations, with **zero** wide-integer Horner `evalBaseChunksTracked` conversions). -/
def computableNatMulBitsAuxTracked : ℕ → ℕ → List Bool → List Bool → CostM (List Bool)
  | 0, w, aBits, bBits => binaryShiftAddMulBitsTracked w aBits bBits
  | d + 1, w, aBits, bBits =>
    if 1 ≤ w then
      let b := chunkBits w
      let R0 := rootR0 w
      let aChunks := sliceBitChunkFnTracked b R0 (aBits.take w)
      let bChunks := sliceBitChunkFnTracked b R0 (bBits.take w)
      let subMulBits : ℕ → List Bool → List Bool → CostM (List Bool) :=
        fun w' xs ys => computableNatMulBitsAuxTracked d w' xs ys
      let sched := computeScheduleIntTreeWithMulTracked subMulBits
        (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0)
      let conv := computableConvFromChunksWithMulTracked subMulBits w sched.1 aChunks.1 bChunks.1
      let emit := carrySaveEmitBitsTracked b (2 * w)
        (List.ofFn (fun k : Fin R0 => (conv.1 k).toNat)) 0
      (emit.1, aChunks.2 + bChunks.2 + sched.2 + conv.2 + emit.2 + 2 * w + R0 + 4)
    else
      binaryShiftAddMulBitsTracked w aBits bBits

/-- **Exactness of `computableNatMulBitsAuxTracked` on All `w`-Bit Operands
(`computableNatMulBitsAuxTracked_fst`)**:
For all depths $d \in \mathbb{N}$, all widths $w \in \mathbb{N}$, and all $w$-bit integers
$A, B < 2^w$,
`(computableNatMulBitsAuxTracked d w (encodeNatBits w A) (encodeNatBits w B)).1 = encodeNatBits (2 * w) (A * B)`. -/
theorem computableNatMulBitsAuxTracked_fst (d : ℕ) :
    ∀ w A B : ℕ, A < 2 ^ w → B < 2 ^ w →
      (computableNatMulBitsAuxTracked d w (encodeNatBits w A) (encodeNatBits w B)).1 =
        encodeNatBits (2 * w) (A * B) := by
  induction d with
  | zero =>
    intro w A B hA hB
    unfold computableNatMulBitsAuxTracked
    rw [binaryShiftAddMulBitsTracked_fst,
      List.take_of_length_le (by simp), List.take_of_length_le (by simp),
      decodeNatBits_encodeNatBits w A hA, decodeNatBits_encodeNatBits w B hB]
  | succ d ih =>
    intro w A B hA hB
    unfold computableNatMulBitsAuxTracked
    split_ifs with hw
    · dsimp only
      have hsched := computeScheduleIntTreeWithMulTracked_root_fst_of_mul_eq _ ih w
      rw [carrySaveEmitBitsTracked_fst, sliceBitChunkFnTracked_fst, sliceBitChunkFnTracked_fst,
        hsched, computableConvFromChunksWithMulTracked_fst_of_mul_eq _ ih w
          (validScheduleIntTree_computeScheduleIntTree _ _ _)]
      rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp),
        ← take_encodeInputBits w A B, ← drop_encodeInputBits w A B,
        carrySaveEmitBits_conv_eq_encodeNatBits_reconstruct,
        take_encodeInputBits, drop_encodeInputBits,
        decodeNatBits_encodeNatBits w A hA, decodeNatBits_encodeNatBits w B hB,
        computableReconstructProductWithMul_eq_of_mul_eq (· * ·) (fun _ _ => rfl),
        computableReconstructProduct_computeScheduleIntTree_eq_mul w A B hA hB]
    · rw [binaryShiftAddMulBitsTracked_fst,
        List.take_of_length_le (by simp), List.take_of_length_le (by simp),
        decodeNatBits_encodeNatBits w A hA, decodeNatBits_encodeNatBits w B hB]

/-- **Self-Recursive Parameter-Free Operation-Tracking Bit-List Multiplication
(`computableNatMulBitsTracked`)**:
Takes ONLY `(n, inBits)` (with **no** free `M_mul` parameter and **no** external schedule parameter),
slices `inBits` into $b$-bit chunks via `sliceBitChunkFnTracked`, generates the integer schedule
tree via `computeScheduleIntTreeWithMulTracked`, executes `computableConvFromChunksWithMulTracked`
routing every sub-word multiplication to `computableNatMulBitsAuxTracked 1`, emits the $2n$-bit
product bitstream via `carrySaveEmitBitsTracked`, and accumulates the exact `.2` step count
bottom-up. -/
def computableNatMulBitsTracked (n : ℕ) (inBits : List Bool) : CostM (List Bool) :=
  let b := chunkBits n
  let R0 := rootR0 n
  let aChunks := sliceBitChunkFnTracked b R0 (inBits.take n)
  let bChunks := sliceBitChunkFnTracked b R0 (inBits.drop n)
  let subMulBits : ℕ → List Bool → List Bool → CostM (List Bool) :=
    fun w xs ys => computableNatMulBitsAuxTracked 1 w xs ys
  let sched := computeScheduleIntTreeWithMulTracked subMulBits
    (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
  let conv := computableConvFromChunksWithMulTracked subMulBits n sched.1 aChunks.1 bChunks.1
  let emit := carrySaveEmitBitsTracked b (2 * n)
    (List.ofFn (fun k : Fin R0 => (conv.1 k).toNat)) 0
  (emit.1, aChunks.2 + bChunks.2 + sched.2 + conv.2 + emit.2 + 2 * n + R0 + 4)

@[simp]
theorem computableNatMulBitsTracked_fst (n : ℕ) (inBits : List Bool) :
    (computableNatMulBitsTracked n inBits).1 = computableIntMulBits n inBits := by
  unfold computableNatMulBitsTracked computableIntMulBits
  dsimp only
  have hsub := computableNatMulBitsAuxTracked_fst 1
  have hsched := computeScheduleIntTreeWithMulTracked_root_fst_of_mul_eq _ hsub n
  rw [carrySaveEmitBitsTracked_fst, sliceBitChunkFnTracked_fst, sliceBitChunkFnTracked_fst,
    hsched, computableConvFromChunksWithMulTracked_fst_of_mul_eq _ hsub n
      (validScheduleIntTree_computeScheduleIntTree _ _ _)]

@[simp]
theorem computableNatMulBitsTracked_fst_encodeInputBits (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    (computableNatMulBitsTracked n (encodeInputBits n A B)).1 =
      encodeNatBits (2 * n) (A * B) := by
  rw [computableNatMulBitsTracked_fst, computableIntMulBits_encodeInputBits n A B hA hB]

/-- **Self-Recursive Operation-Tracking Computable Integer Multiplication (`computableNatMulTracked`)**:
Encodes `(A, B)` into $n$-bit lists via `encodeNatBitsTracked`, executes the pure bit-list recursive
multiplier `computableNatMulBitsTracked` across all depths $d = 2 \to 1 \to 0$ (using
`sliceBitChunkFnTracked`, `packSignedSlotsBitsTracked`, `unpackSignedSlotsBitsTracked`, and
`carrySaveEmitBitsTracked` with **zero** wide-integer `natChunkFnTracked` or `evalBaseChunksTracked`
calls), and decodes the $2n$-bit product bit-list via `decodeNatBitsTracked (2 * n)`. -/
def computableNatMulTracked (n A B : ℕ) : CostM ℕ :=
  let aBits := encodeNatBitsTracked n A
  let bBits := encodeNatBitsTracked n B
  let prodBits := computableNatMulBitsTracked n (aBits.1 ++ bBits.1)
  let out := decodeNatBitsTracked (2 * n) prodBits.1
  (out.1, aBits.2 + bBits.2 + prodBits.2 + out.2 + 2 * n + 2)

theorem computableNatMulTracked_fst (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    (computableNatMulTracked n A B).1 = A * B := by
  unfold computableNatMulTracked
  dsimp only
  have hprod : A * B < 2 ^ (2 * n) := by
    rw [Nat.two_mul, pow_add]
    exact Nat.mul_lt_mul'' hA hB
  rw [decodeNatBitsTracked_fst, encodeNatBitsTracked_fst, encodeNatBitsTracked_fst]
  change decodeNatBits ((computableNatMulBitsTracked n (encodeInputBits n A B)).1.take (2 * n)) = A * B
  rw [computableNatMulBitsTracked_fst_encodeInputBits n A B hA hB,
    List.take_of_length_le (by simp),
    decodeNatBits_encodeNatBits (2 * n) (A * B) hprod]

/-! ### Helper Step-Count Upper Bounds (`_snd_le`) for Tracked Schedule & Deconvolution Primitives -/

theorem approxLogTwoFixedTracked_snd_le (w S : ℕ) :
    (approxLogTwoFixedTracked w S).2 ≤
      (S + 2) * (15 * (w + 2 * S + 4) * (w + 2 * S + 4)) + 4 := by
  unfold approxLogTwoFixedTracked
  dsimp only
  set W := w + (S + (S + 2)) + 2
  have hW : W = w + 2 * S + 4 := by dsimp [W]; omega
  have h := sumRangeTracked_snd_le w (S + 2)
    (fun i => roundDivIntTracked W
      ((2 : ℤ) ^ (S + (S + 2) - (i + 1))) ((i + 1 : ℕ) : ℤ))
    (5 * W * W + 20 * W + 13)
    (fun i _ => roundDivIntTracked_snd_le W _ _)
  have hstep : 5 * W * W + 20 * W + 13 + w + 2 ≤ 15 * (w + 2 * S + 4) * (w + 2 * S + 4) := by
    have hW4 : 4 ≤ W := by omega
    have hwW : w ≤ W := by omega
    rw [← hW]
    nlinarith
  have hmul := Nat.mul_le_mul_left (S + 2) hstep
  linarith

theorem arctanInvPowArrayFixedTracked_snd_le (w k q_acc N : ℕ) :
    (arctanInvPowArrayFixedTracked w k q_acc N).2 ≤
      (N + 1) * (20 * (w + q_acc + 2) * (w + q_acc + 2)) + 4 := by
  unfold arctanInvPowArrayFixedTracked
  dsimp only
  set W := w + q_acc + 2
  have hinit := roundDivIntTracked_snd_le W ((2 : ℤ) ^ q_acc) (k : ℤ)
  have hrec := buildRecurrenceArrayTracked_snd_le
    (roundDivIntTracked W ((2 : ℤ) ^ q_acc) (k : ℤ)).1
    (fun _m P_m => roundDivIntTracked W P_m ((k * k : ℕ) : ℤ))
    (5 * W * W + 20 * W + 13) N
    (fun _m _ P_m => roundDivIntTracked_snd_le W P_m _)
  have hstep : 5 * W * W + 20 * W + 13 + 2 ≤ 20 * W * W := by
    have : 2 ≤ W := by dsimp [W]; omega
    nlinarith
  have hmul := Nat.mul_le_mul_left N hstep
  linarith

theorem arctanInvTaylorFixedTracked_snd_le (w N k : ℕ) :
    (arctanInvTaylorFixedTracked w N k).2 ≤
      (N + 1) * (35 * (w + 4 * N + 8) * (w + 4 * N + 8)) + 8 := by
  unfold arctanInvTaylorFixedTracked
  dsimp only
  set q_acc := 4 * N + 6
  set W := w + q_acc + 2
  have hW : W = w + 4 * N + 8 := by dsimp [W, q_acc]; omega
  set arr := arctanInvPowArrayFixedTracked w k q_acc N
  set s := sumRangeTracked w (N + 1) (fun m =>
    let d := roundDivIntTracked W (arr.1.getD m 0) ((2 * m + 1 : ℕ) : ℤ)
    (altSign m * d.1, d.2 + 2))
  have harr : arr.2 ≤ (N + 1) * (20 * W * W) + 4 :=
    arctanInvPowArrayFixedTracked_snd_le w k q_acc N
  have hs : s.2 ≤ (N + 1) * (5 * W * W + 20 * W + 15 + w + 2) + 2 :=
    sumRangeTracked_snd_le w (N + 1) _ (5 * W * W + 20 * W + 15) (fun m _ => by
      dsimp only
      have hd := roundDivIntTracked_snd_le W (arr.1.getD m 0) ((2 * m + 1 : ℕ) : ℤ)
      omega)
  have hstep :
      20 * W * W + (5 * W * W + 20 * W + 15 + w + 2) ≤
        35 * (w + 4 * N + 8) * (w + 4 * N + 8) := by
    have hW8 : 8 ≤ W := by omega
    have hwW : w ≤ W := by omega
    rw [← hW]
    nlinarith
  have hmul := Nat.mul_le_mul_left (N + 1) hstep
  linarith

theorem approxPiFixedTracked_snd_le (w S : ℕ) :
    (approxPiFixedTracked w S).2 ≤
      (S + 4) * (70 * (w + 4 * S + 20) * (w + 4 * S + 20)) + w + 24 := by
  unfold approxPiFixedTracked
  dsimp only
  have h2 := arctanInvTaylorFixedTracked_snd_le w (S + 3) 2
  have h3 := arctanInvTaylorFixedTracked_snd_le w (S + 3) 3
  have heq : w + 4 * (S + 3) + 8 = w + 4 * S + 20 := by omega
  rw [heq] at h2 h3
  linarith

theorem approxSqrtFixedTracked_snd_le (w k : ℕ) (num : ℤ) :
    (approxSqrtFixedTracked w k num).2 ≤ 5 * w * w + 8 * w + k + 6 := by
  unfold approxSqrtFixedTracked
  dsimp only
  have h := binaryRestoringSqrtRegTracked_snd_le w ((max 0 num).toNat / 2 ^ k)
  omega

theorem expTermArrayFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    (w q_r q_acc N : ℕ) (r_mant : ℤ) (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M) :
    (expTermArrayFixedWithMulTracked smulTracked w q_r q_acc N r_mant).2 ≤
      N * (M + 20 * w * w + 40 * w + 17) + 4 := by
  unfold expTermArrayFixedWithMulTracked
  dsimp only
  have hrec := buildRecurrenceArrayTracked_snd_le ((2 : ℤ) ^ q_acc)
    (fun m T_m =>
      let p := smulTracked T_m r_mant
      let d := roundDivIntTracked (2 * w) p.1 (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r)
      (d.1, p.2 + d.2 + 2))
    (M + 20 * w * w + 40 * w + 15) N
    (fun m _ T_m => by
      dsimp only
      have hp := hM T_m r_mant
      have hd := roundDivIntTracked_snd_le (2 * w) (smulTracked T_m r_mant).1
        (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r)
      nlinarith)
  linarith

theorem sincTaylorFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    (w N : ℕ) (θNum θDen : ℤ) (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 8 * w + 10) :
    (sincTaylorFixedWithMulTracked smulTracked w N θNum θDen).2 ≤
      (N + 7) * (M + 25 * w * w + 70 * w + 50) +
        28 * (w + N + 7) * (w + N + 7) + 30 := by
  unfold sincTaylorFixedWithMulTracked
  dsimp only
  set r_mant := roundDivIntTracked (2 * w + 2 * (N + 6) + 2) (θNum * (2 : ℤ) ^ (2 * (N + 6))) θDen
  set arr := expTermArrayFixedWithMulTracked smulTracked w (2 * (N + 6))
    (3 * (N + 6) + 6) (N + 6) r_mant.1
  set sRaw := sumRangeTracked w (N + 6 + 1) (fun m =>
    let d := roundDivIntTracked w (arr.1.getD m 0) ((m + 1 : ℕ) : ℤ)
    (iPowIm (m + 1) * d.1, d.2 + 2))
  have hrm : r_mant.2 ≤ 28 * (w + N + 7) * (w + N + 7) := by
    have h0 := roundDivIntTracked_snd_le (2 * w + 2 * (N + 6) + 2)
      (θNum * (2 : ℤ) ^ (2 * (N + 6))) θDen
    nlinarith
  have harr : arr.2 ≤ (N + 6) * (M + 8 * w + 10 + 20 * w * w + 40 * w + 17) + 4 :=
    expTermArrayFixedWithMulTracked_snd_le smulTracked w (2 * (N + 6))
      (3 * (N + 6) + 6) (N + 6) r_mant.1 (M + 8 * w + 10) hM
  have hs : sRaw.2 ≤ (N + 6 + 1) * (5 * w * w + 20 * w + 15 + w + 2) + 2 :=
    sumRangeTracked_snd_le w (N + 6 + 1) _ (5 * w * w + 20 * w + 15) (fun m _ => by
      dsimp only
      have hd := roundDivIntTracked_snd_le w (arr.1.getD m 0) ((m + 1 : ℕ) : ℤ)
      omega)
  have harr' : (N + 6) * (M + 8 * w + 10 + 20 * w * w + 40 * w + 17) ≤
      (N + 7) * (M + 20 * w * w + 48 * w + 27) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsum :
      (N + 7) * (M + 20 * w * w + 48 * w + 27) +
        (N + 6 + 1) * (5 * w * w + 20 * w + 15 + w + 2) ≤
        (N + 7) * (M + 25 * w * w + 70 * w + 50) := by
    have h1 : (M + 20 * w * w + 48 * w + 27) + (5 * w * w + 20 * w + 15 + w + 2) ≤
        M + 25 * w * w + 70 * w + 50 := by nlinarith
    calc (N + 7) * (M + 20 * w * w + 48 * w + 27) +
          (N + 6 + 1) * (5 * w * w + 20 * w + 15 + w + 2)
        = (N + 7) * ((M + 20 * w * w + 48 * w + 27) + (5 * w * w + 20 * w + 15 + w + 2)) := by ring
      _ ≤ (N + 7) * (M + 25 * w * w + 70 * w + 50) := Nat.mul_le_mul_left _ h1
  linarith

theorem expTaylorFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    (w N : ℕ) (gNum gDen : ℤ) (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 8 * w + 10) :
    (expTaylorFixedWithMulTracked smulTracked w N gNum gDen).2 ≤
      (N + 7) * (M + 20 * w * w + 50 * w + 35) +
        55 * (w + N + 7) * (w + N + 7) + 30 := by
  unfold expTaylorFixedWithMulTracked
  dsimp only
  set r_mant := roundDivIntTracked (3 * w + 2 * (N + 6) + 2) (gNum * (2 : ℤ) ^ (2 * (N + 6))) gDen
  set arr := expTermArrayFixedWithMulTracked smulTracked w (2 * (N + 6))
    (3 * (N + 6) + 6) (N + 6) r_mant.1
  set eRaw := sumRangeTracked w (N + 6 + 1) (fun m => (arr.1.getD m 0, 2))
  have hrm : r_mant.2 ≤ 55 * (w + N + 7) * (w + N + 7) := by
    have h0 := roundDivIntTracked_snd_le (3 * w + 2 * (N + 6) + 2)
      (gNum * (2 : ℤ) ^ (2 * (N + 6))) gDen
    nlinarith
  have harr : arr.2 ≤ (N + 6) * (M + 8 * w + 10 + 20 * w * w + 40 * w + 17) + 4 :=
    expTermArrayFixedWithMulTracked_snd_le smulTracked w (2 * (N + 6))
      (3 * (N + 6) + 6) (N + 6) r_mant.1 (M + 8 * w + 10) hM
  have he : eRaw.2 ≤ (N + 6 + 1) * (2 + w + 2) + 2 :=
    sumRangeTracked_snd_le w (N + 6 + 1) _ 2 (fun _ _ => le_rfl)
  have harr' : (N + 6) * (M + 8 * w + 10 + 20 * w * w + 40 * w + 17) ≤
      (N + 7) * (M + 20 * w * w + 48 * w + 27) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsum :
      (N + 7) * (M + 20 * w * w + 48 * w + 27) + (N + 6 + 1) * (2 + w + 2) ≤
        (N + 7) * (M + 20 * w * w + 50 * w + 35) := by
    have h1 : (M + 20 * w * w + 48 * w + 27) + (2 + w + 2) ≤
        M + 20 * w * w + 50 * w + 35 := by omega
    calc (N + 7) * (M + 20 * w * w + 48 * w + 27) + (N + 6 + 1) * (2 + w + 2)
        = (N + 7) * ((M + 20 * w * w + 48 * w + 27) + (2 + w + 2)) := by ring
      _ ≤ (N + 7) * (M + 20 * w * w + 50 * w + 35) := Nat.mul_le_mul_left _ h1
  linarith

theorem erfIntegralTaylorFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    (w N : ℕ) (zNum zDen : ℤ) (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 8 * w + 10) :
    (erfIntegralTaylorFixedWithMulTracked smulTracked w N zNum zDen).2 ≤
      (N + 7) * (M + 25 * w * w + 70 * w + 50) +
        2 * M + 28 * (w + N + 7) * (w + N + 7) + 16 * w + 50 := by
  unfold erfIntegralTaylorFixedWithMulTracked
  dsimp only
  set z_mant := roundDivIntTracked (2 * w + (N + 6) + 2) (zNum * (2 : ℤ) ^ (N + 6)) zDen
  set zSq := smulTracked z_mant.1 z_mant.1
  set arr := expTermArrayFixedWithMulTracked smulTracked w (2 * (N + 6))
    (3 * (N + 6) + 6) (N + 6) (-zSq.1)
  set S_inner := sumRangeTracked w (N + 6 + 1) (fun m =>
    roundDivIntTracked w (arr.1.getD m 0) ((2 * m + 1 : ℕ) : ℤ))
  set out := smulTracked z_mant.1 S_inner.1
  have hz : z_mant.2 ≤ 28 * (w + N + 7) * (w + N + 7) := by
    have h0 := roundDivIntTracked_snd_le (2 * w + (N + 6) + 2)
      (zNum * (2 : ℤ) ^ (N + 6)) zDen
    nlinarith
  have hzSq : zSq.2 ≤ M + 8 * w + 10 := hM _ _
  have harr : arr.2 ≤ (N + 6) * (M + 8 * w + 10 + 20 * w * w + 40 * w + 17) + 4 :=
    expTermArrayFixedWithMulTracked_snd_le smulTracked w (2 * (N + 6))
      (3 * (N + 6) + 6) (N + 6) (-zSq.1) (M + 8 * w + 10) hM
  have hS : S_inner.2 ≤ (N + 6 + 1) * (5 * w * w + 20 * w + 13 + w + 2) + 2 :=
    sumRangeTracked_snd_le w (N + 6 + 1) _ (5 * w * w + 20 * w + 13) (fun m _ =>
      roundDivIntTracked_snd_le w _ _)
  have hout : out.2 ≤ M + 8 * w + 10 := hM _ _
  have harr' : (N + 6) * (M + 8 * w + 10 + 20 * w * w + 40 * w + 17) ≤
      (N + 7) * (M + 20 * w * w + 48 * w + 27) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsum :
      (N + 7) * (M + 20 * w * w + 48 * w + 27) +
        (N + 6 + 1) * (5 * w * w + 20 * w + 13 + w + 2) ≤
        (N + 7) * (M + 25 * w * w + 70 * w + 50) := by
    have h1 : (M + 20 * w * w + 48 * w + 27) + (5 * w * w + 20 * w + 13 + w + 2) ≤
        M + 25 * w * w + 70 * w + 50 := by nlinarith
    calc (N + 7) * (M + 20 * w * w + 48 * w + 27) +
          (N + 6 + 1) * (5 * w * w + 20 * w + 13 + w + 2)
        = (N + 7) * ((M + 20 * w * w + 48 * w + 27) + (5 * w * w + 20 * w + 13 + w + 2)) := by ring
      _ ≤ (N + 7) * (M + 25 * w * w + 70 * w + 50) := Nat.mul_le_mul_left _ h1
  linarith

theorem nyquistModeSumFixedTracked_snd_le (K p : ℕ)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    (nyquistModeSumFixedTracked K p xFixed).2 ≤ 10 * (2 ^ K) * qChildEll K p := by
  unfold nyquistModeSumFixedTracked
  dsimp only
  simp only [FixedComplex.rescaleTracked_snd]
  set S_re := sumFinIntTracked (p + 2 + k2Ell K) (fun j2 : Fin (rEll K) =>
    (altSign j2.val *
      (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩).re,
      p + 4))
  set S_im := sumFinIntTracked (p + 2 + k2Ell K) (fun j2 : Fin (rEll K) =>
    (altSign j2.val *
      (xFixed ⟨(t1Ell K / 2 + t1Ell K * j2.val) % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩).im,
      p + 4))
  have hre : S_re.2 ≤ rEll K * ((p + 4) + (p + 2 + k2Ell K) + 2) + 2 :=
    sumFinIntTracked_snd_le (p + 2 + k2Ell K) _ (p + 4) (fun _ => le_rfl)
  have him : S_im.2 ≤ rEll K * ((p + 4) + (p + 2 + k2Ell K) + 2) + 2 :=
    sumFinIntTracked_snd_le (p + 2 + k2Ell K) _ (p + 4) (fun _ => le_rfl)
  clear_value S_re S_im
  have hq : p + 2 * K + 14 = qChildEll K p := (qChildEll_eq K p).symm
  have hk2 : k2Ell K ≤ K := by unfold k2Ell; omega
  have hr_le : rEll K ≤ 2 ^ K := by
    rw [← t1Ell_mul_rEll K]
    exact Nat.le_mul_of_pos_left _ (t1Ell_pos K)
  have h_bound : (p + 4) + (p + 2 + k2Ell K) + 2 ≤ 2 * qChildEll K p := by omega
  have h_mul : rEll K * ((p + 4) + (p + 2 + k2Ell K) + 2) ≤ (2 ^ K) * (2 * qChildEll K p) :=
    Nat.mul_le_mul hr_le h_bound
  have h_tail : 2 + 2 + (2 * (p + 2 + k2Ell K + qChildEll K p) + 4) + p + 4 ≤
      5 * qChildEll K p := by omega
  have h_tail_mul : 5 * qChildEll K p ≤ (2 ^ K) * (5 * qChildEll K p) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos K)
  have h_sum : S_re.2 + S_im.2 + (2 * (p + 2 + k2Ell K + qChildEll K p) + 4) + (p + 4) ≤
      (2 ^ K) * (2 * qChildEll K p) + (2 ^ K) * (2 * qChildEll K p) +
        (2 ^ K) * (5 * qChildEll K p) := by omega
  calc S_re.2 + S_im.2 + (2 * (p + 2 + k2Ell K + qChildEll K p) + 4) + (p + 4)
      ≤ (2 ^ K) * (2 * qChildEll K p) + (2 ^ K) * (2 * qChildEll K p) +
          (2 ^ K) * (5 * qChildEll K p) := h_sum
    _ = 9 * ((2 ^ K) * qChildEll K p) := by ring
    _ ≤ 10 * ((2 ^ K) * qChildEll K p) := Nat.mul_le_mul_right _ (by decide)
    _ = 10 * (2 ^ K) * qChildEll K p := by ring

theorem bidiagSweepFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    (t1 q : ℕ) (ht1 : 1 ≤ t1) (hq : 14 ≤ q) (a_max a_min : ℤ)
    (Y_seq : ℕ → FixedComplex q) (idx : Fin t1 → ℕ)
    (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 80 * q + 10) :
    (bidiagSweepFixedWithMulTracked smulTracked t1 q a_max a_min Y_seq idx).2 ≤
      t1 * (7 * M + 650 * q) + 6000 * q * q := by
  unfold bidiagSweepFixedWithMulTracked
  dsimp only
  set invA_m := roundDivIntTracked (q + (q + 9) + 2) ((2 : ℤ) ^ (q + (q + 9))) a_max
  set ratio_m := roundDivIntTracked (6 * (q + (q + 9))) (-a_min * (2 : ℤ) ^ (q + 9)) a_max
  set B_scaledFixed := memoizeRangeTracked t1 (fun s =>
    let rs := FixedComplex.rescaleTracked (q + 9) (Y_seq s)
    let sc := FixedComplex.scaleRoundedWithTracked smulTracked invA_m.1 rs.1
    (sc.1, rs.2 + sc.2))
  set recSweep := buildRecurrenceArrayTracked ((0 : FixedComplex (q + 9)), (2 : ℤ) ^ (q + 9))
    (bidiagSweepStepFixedWithMulTracked smulTracked (q + 9) ratio_m.1 B_scaledFixed.1) t1
  set Z0 := divScalarFixedTracked (q + 9) (q + 9) recSweep.1.2.1 ((2 : ℤ) ^ (q + 9) - recSweep.1.2.2)
  set out := memoizeFinTracked (fun u1 : Fin t1 =>
    let st := recSweep.1.1.getD (idx u1) ((0 : FixedComplex (q + 9)), (2 : ℤ) ^ (q + 9))
    let sc := FixedComplex.scaleRoundedWithTracked smulTracked st.2 Z0.1
    let ad := FixedComplex.addTracked st.1 sc.1
    let rs := FixedComplex.rescaleTracked q ad.1
    (rs.1, sc.2 + ad.2 + rs.2 + 2))
  have hinv : invA_m.2 ≤ 5 * (q + (q + 9) + 2) * (q + (q + 9) + 2) + 20 * (q + (q + 9) + 2) + 13 :=
    roundDivIntTracked_snd_le (q + (q + 9) + 2) ((2 : ℤ) ^ (q + (q + 9))) a_max
  have hrat : ratio_m.2 ≤ 5 * (6 * (q + (q + 9))) * (6 * (q + (q + 9))) + 20 * (6 * (q + (q + 9))) + 13 :=
    roundDivIntTracked_snd_le (6 * (q + (q + 9))) (-a_min * (2 : ℤ) ^ (q + 9)) a_max
  have hB : B_scaledFixed.2 ≤
      t1 * (2 * (q + (q + 9)) + 4 + 2 * (M + 80 * q + 10) + 2 * (q + 9) + 6) + t1 + 1 :=
    memoizeRangeTracked_snd_le t1 _
      (2 * (q + (q + 9)) + 4 + 2 * (M + 80 * q + 10) + 2 * (q + 9) + 6)
      (fun s _ => by
        dsimp only
        simp only [FixedComplex.rescaleTracked_snd]
        have hsc := FixedComplex.scaleRoundedWithTracked_snd_le smulTracked invA_m.1
          (FixedComplex.rescaleTracked (q + 9) (Y_seq s)).1 (M + 80 * q + 10) hM
        omega)
  have hrec : recSweep.2 ≤ t1 * (3 * (M + 80 * q + 10) + 5 * (q + 9) + 14 + 2) + 2 :=
    buildRecurrenceArrayTracked_snd_le ((0 : FixedComplex (q + 9)), (2 : ℤ) ^ (q + 9))
      (bidiagSweepStepFixedWithMulTracked smulTracked (q + 9) ratio_m.1 B_scaledFixed.1)
      (3 * (M + 80 * q + 10) + 5 * (q + 9) + 14) t1
      (fun s _ st => by
        unfold bidiagSweepStepFixedWithMulTracked
        dsimp only
        simp only [FixedComplex.addTracked_snd, roundShiftIntTracked_snd]
        have hsc := FixedComplex.scaleRoundedWithTracked_snd_le smulTracked ratio_m.1 st.1
          (M + 80 * q + 10) hM
        have hpr := hM ratio_m.1 st.2
        omega)
  have hZ0 : Z0.2 ≤
      2 * (5 * (6 * (q + 9 + (q + 9))) * (6 * (q + 9 + (q + 9))) + 20 * (6 * (q + 9 + (q + 9))) + 13) +
        2 * (q + 9) + 2 :=
    divScalarFixedTracked_snd_le (q + 9) (q + 9) recSweep.1.2.1 ((2 : ℤ) ^ (q + 9) - recSweep.1.2.2)
  have hout : out.2 ≤ t1 * (2 * (M + 80 * q + 10) + 6 * (q + 9) + 2 * q + 16) + t1 + 1 :=
    memoizeFinTracked_snd_le _
      (2 * (M + 80 * q + 10) + 6 * (q + 9) + 2 * q + 16)
      (fun u1 => by
        dsimp only
        simp only [FixedComplex.addTracked_snd, FixedComplex.rescaleTracked_snd]
        have hsc := FixedComplex.scaleRoundedWithTracked_snd_le smulTracked
          (recSweep.1.1.getD (idx u1) ((0 : FixedComplex (q + 9)), (2 : ℤ) ^ (q + 9))).2
          Z0.1 (M + 80 * q + 10) hM
        omega)
  clear_value invA_m ratio_m B_scaledFixed recSweep Z0 out
  have hq2 : 14 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have hq1 : 196 ≤ q * q := Nat.mul_le_mul hq hq
  have ht1q : 14 * t1 ≤ t1 * q := by
    calc 14 * t1 = t1 * 14 := Nat.mul_comm 14 t1
      _ ≤ t1 * q := Nat.mul_le_mul_left t1 hq
  have hM_nn : 0 ≤ t1 * M := Nat.zero_le _
  linarith only [ht1, hq, hq2, hq1, ht1q, hM_nn, hinv, hrat, hB, hrec, hZ0, hout]

theorem cyclicBidiagPrevSolveFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    {t1 q : ℕ} [NeZero t1] (hq : 14 ≤ q) (a b : ℤ) (Y : Fin t1 → FixedComplex q)
    (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 80 * q + 10) :
    (cyclicBidiagPrevSolveFixedWithMulTracked smulTracked a b Y).2 ≤
      t1 * (7 * M + 650 * q) + 6000 * q * q := by
  unfold cyclicBidiagPrevSolveFixedWithMulTracked cyclicBidiagSolveFixedWithMulTracked
  have ht1 : 1 ≤ t1 := NeZero.pos t1
  split_ifs <;> exact bidiagSweepFixedWithMulTracked_snd_le smulTracked t1 q ht1 hq _ _ _ _ M hM

theorem nyquistColumnSolveFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    {t1 q : ℕ} (ht1 : 1 ≤ t1) (hq : 14 ≤ q) (a : ℤ)
    (Y : Fin t1 → FixedComplex q) (altFixed : FixedComplex q)
    (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 80 * q + 10) :
    (nyquistColumnSolveFixedWithMulTracked smulTracked a Y altFixed).2 ≤
      t1 * (7 * M + 650 * q) + 6000 * q * q := by
  unfold nyquistColumnSolveFixedWithMulTracked
  dsimp only
  set invC0_m := roundDivIntTracked (q + (q + 4) + 2) ((2 : ℤ) ^ (q + (q + 4))) a
  set B_scaledFixed := memoizeFinTracked (fun m : Fin t1 =>
    let rs := FixedComplex.rescaleTracked (q + 4) (Y m)
    let sc := FixedComplex.scaleRoundedWithTracked smulTracked invC0_m.1 rs.1
    (sc.1, rs.2 + sc.2))
  set recChain := buildRecurrenceArrayTracked (0 : FixedComplex (q + 4))
    (fun k prev => (nyquistOpenChainStep B_scaledFixed.1 k prev, 16 * (q + 4) + 4)) t1
  set altRe := sumFinIntTracked (8 * (q + 4)) (fun m : Fin t1 =>
    (altSign m.val * (recChain.1.1.getD m.val 0).re, 8 * (q + 4) + 2))
  set altIm := sumFinIntTracked (8 * (q + 4)) (fun m : Fin t1 =>
    (altSign m.val * (recChain.1.1.getD m.val 0).im, 8 * (q + 4) + 2))
  set altWork := FixedComplex.rescaleTracked (q + 4) altFixed
  set diff := FixedComplex.subTracked altWork.1 ⟨altRe.1, altIm.1⟩
  set corr := divNatFixedTracked diff.1 t1
  set out := memoizeFinTracked (fun u1 : Fin t1 =>
    let ad := FixedComplex.addTracked (recChain.1.1.getD u1.val 0)
      ⟨altSign u1.val * corr.1.re, altSign u1.val * corr.1.im⟩
    let rs := FixedComplex.rescaleTracked q ad.1
    (rs.1, ad.2 + rs.2 + 16 * (q + 4) + 4))
  have hinv : invC0_m.2 ≤ 5 * (q + (q + 4) + 2) * (q + (q + 4) + 2) + 20 * (q + (q + 4) + 2) + 13 :=
    roundDivIntTracked_snd_le (q + (q + 4) + 2) ((2 : ℤ) ^ (q + (q + 4))) a
  have hB : B_scaledFixed.2 ≤
      t1 * (2 * (q + (q + 4)) + 4 + 2 * (M + 80 * q + 10) + 2 * (q + 4) + 6) + t1 + 1 :=
    memoizeFinTracked_snd_le _
      (2 * (q + (q + 4)) + 4 + 2 * (M + 80 * q + 10) + 2 * (q + 4) + 6)
      (fun m => by
        dsimp only
        simp only [FixedComplex.rescaleTracked_snd]
        have hsc := FixedComplex.scaleRoundedWithTracked_snd_le smulTracked invC0_m.1
          (FixedComplex.rescaleTracked (q + 4) (Y m)).1 (M + 80 * q + 10) hM
        omega)
  have hrec : recChain.2 ≤ t1 * (16 * (q + 4) + 4 + 2) + 2 :=
    buildRecurrenceArrayTracked_snd_le (0 : FixedComplex (q + 4))
      (fun k prev => (nyquistOpenChainStep B_scaledFixed.1 k prev, 16 * (q + 4) + 4))
      (16 * (q + 4) + 4) t1 (fun _ _ _ => le_rfl)
  have haltRe : altRe.2 ≤ t1 * ((8 * (q + 4) + 2) + (8 * (q + 4)) + 2) + 2 :=
    sumFinIntTracked_snd_le (8 * (q + 4)) _ (8 * (q + 4) + 2) (fun _ => le_rfl)
  have haltIm : altIm.2 ≤ t1 * ((8 * (q + 4) + 2) + (8 * (q + 4)) + 2) + 2 :=
    sumFinIntTracked_snd_le (8 * (q + 4)) _ (8 * (q + 4) + 2) (fun _ => le_rfl)
  have haltW : altWork.2 = 2 * (q + (q + 4)) + 4 := rfl
  have hdiff : diff.2 = 2 * (q + 4) + 4 := rfl
  have hcorr : corr.2 ≤
      2 * (5 * (10 * (q + 4)) * (10 * (q + 4)) + 20 * (10 * (q + 4)) + 13) + 2 :=
    divNatFixedTracked_snd_le diff.1 t1
  have hout : out.2 ≤ t1 * (2 * (q + 4) + 4 + 2 * ((q + 4) + q) + 4 + 16 * (q + 4) + 4) + t1 + 1 :=
    memoizeFinTracked_snd_le _
      (2 * (q + 4) + 4 + 2 * ((q + 4) + q) + 4 + 16 * (q + 4) + 4)
      (fun u1 => by
        dsimp only
        simp only [FixedComplex.addTracked_snd, FixedComplex.rescaleTracked_snd]
        omega)
  clear_value invC0_m B_scaledFixed recChain altRe altIm altWork diff corr out
  have hq2 : 14 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have hq1 : 196 ≤ q * q := Nat.mul_le_mul hq hq
  have ht1q : 14 * t1 ≤ t1 * q := by
    calc 14 * t1 = t1 * 14 := Nat.mul_comm 14 t1
      _ ≤ t1 * q := Nat.mul_le_mul_left t1 hq
  have hM_nn : 0 ≤ t1 * M := Nat.zero_le _
  linarith only [ht1, hq, hq2, hq1, ht1q, hM_nn, hinv, hB, hrec, haltRe, haltIm, haltW, hdiff, hcorr, hout]

theorem qChildEll_le_fourteen_mul_t1Ell_of_internal {K p : ℕ}
    (hleaf : (!isBaseLeaf K p) = true) (hK2 : 2 ≤ K) :
    qChildEll K p ≤ 14 * t1Ell K := by
  have hlt : 4 * p * p < 2 ^ K := by
    unfold isBaseLeaf at hleaf
    rw [Bool.not_eq_true', decide_eq_false_iff_not, not_le] at hleaf
    exact hleaf
  have ht1r : t1Ell K * rEll K = 2 ^ K := t1Ell_mul_rEll K
  have hr_le : rEll K ≤ 2 * t1Ell K := by
    unfold rEll t1Ell k2Ell k1Ell
    calc 2 ^ ((K + 1) / 2)
        ≤ 2 ^ (K / 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ (K / 2) := by rw [pow_succ']
  have hsq : 4 * p * p < 2 * (t1Ell K * t1Ell K) := by
    calc 4 * p * p < 2 ^ K := hlt
      _ = t1Ell K * rEll K := ht1r.symm
      _ ≤ t1Ell K * (2 * t1Ell K) := Nat.mul_le_mul_left _ hr_le
      _ = 2 * (t1Ell K * t1Ell K) := by ring
  have hp_lt : p < t1Ell K := by nlinarith
  have hk1_pos : 1 ≤ k1Ell K := by unfold k1Ell; omega
  have ht1_ge2 : 2 ≤ t1Ell K := by
    unfold t1Ell
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k1Ell K := Nat.pow_le_pow_right (by norm_num) hk1_pos
  have hk1_le : k1Ell K ≤ t1Ell K := le_of_lt Nat.lt_two_pow_self
  have hK_le : K ≤ 3 * t1Ell K := by
    have : K ≤ 2 * k1Ell K + 1 := by unfold k1Ell; omega
    omega
  have hq : qChildEll K p = p + 2 * K + 14 := qChildEll_eq K p
  omega

end IntMul

#print axioms IntMul.bidiagSweepFixedWithMulTracked_fst
#print axioms IntMul.cyclicBidiagPrevSolveFixedWithMulTracked_fst
#print axioms IntMul.nyquistColumnSolveFixedWithMulTracked_fst
#print axioms IntMul.computeScheduleIntTreeWithMulTracked_fst_of_mul_eq
#print axioms IntMul.computableFastDFTRecursiveWithMulTracked_fst_of_mul_eq
#print axioms IntMul.computableConvFromChunksWithMulTracked_fst_of_mul_eq
#print axioms IntMul.computableNatMulBitsAuxTracked_fst
#print axioms IntMul.computableNatMulBitsTracked_fst_encodeInputBits
#print axioms IntMul.computableNatMulTracked_fst
