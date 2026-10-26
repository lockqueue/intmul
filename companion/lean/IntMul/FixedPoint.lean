import IntMul.Defs

/-!
# Fixed-Point Arithmetic, Quantization Error Bounds, Word-Width Invariants & Bit Encodings (`IntMul.FixedPoint`)

This module proves the foundational lemmas for `IntMul.Defs` covering:
1. Canonical little-endian bit encodings (`encodeNatBits`, `decodeNatBits`, `encodeInputBits`)
   and their exact round-trip and length identities (Section 8 (`sec:lean`)).
2. Deterministic floor-shifted real and complex quantization error bounds
   (Section 3.2 (`sec:prelim-model`), Definition 3.1 (`def:grid`), equation (4) (`eq:quant-err`)).
3. Exact equivalence between integer shift-rounding `roundShiftInt` and mathematical floor
   quantization, plus fixed-point complex multiplication `FixedComplex.mulRounded`
   (Section 3.2 (`sec:prelim-model`), Definition 3.1 (`def:grid`)).
4. Signed word-width bounds (`FitsSignedWord`, `WordWidthBounds`) and their closure
   under fixed-point arithmetic operations (Section 3.2 (`sec:prelim-model`)).
5. Pure-integer rounded division (`roundDivInt`), single-pass recurrence and table builders,
   and the operation-tracking cost monad `CostM` for the executable value-level pipeline
   (Section 8 (`sec:lean`)).
-/

namespace IntMul

/-! ## 1. Bit Encoding Round-Trip & Length Lemmas (Section 8 (`sec:lean`)) -/

/-- `encodeNatBits w x` always has length `w`. -/
@[simp]
theorem encodeNatBits_length (w x : ℕ) : (encodeNatBits w x).length = w := by
  simp [encodeNatBits]

/-- `encodeInputBits n A B` always has length `2 * n`. -/
@[simp]
theorem encodeInputBits_length (n A B : ℕ) : (encodeInputBits n A B).length = 2 * n := by
  simp [encodeInputBits]
  omega

@[simp]
private theorem encodeNatBits_zero (x : ℕ) : encodeNatBits 0 x = [] := rfl

/-- Unfolding `encodeNatBits (w + 1) x` into its least-significant bit and shifted tail. -/
private theorem encodeNatBits_succ (w x : ℕ) :
    encodeNatBits (w + 1) x = x.testBit 0 :: encodeNatBits w (x / 2) := by
  unfold encodeNatBits
  rw [List.ofFn_succ]
  congr 2
  funext i
  exact Nat.testBit_succ x i.val

private theorem bif_testBit_zero (x : ℕ) :
    (bif x.testBit 0 then 1 else 0) = x % 2 := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- Decoding `encodeNatBits w x` recovers `x % 2 ^ w` for every `x : ℕ`. -/
private theorem decodeNatBits_encodeNatBits_mod (w x : ℕ) :
    decodeNatBits (encodeNatBits w x) = x % 2 ^ w := by
  induction w generalizing x with
  | zero =>
    simp [encodeNatBits, decodeNatBits]
    omega
  | succ w ih =>
    rw [encodeNatBits_succ, decodeNatBits, ih (x / 2), bif_testBit_zero, pow_succ']
    have h1 := Nat.div_add_mod x 2
    have h2 := Nat.div_add_mod (x / 2) (2 ^ w)
    have h3 : (x / 2) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have h4 : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hlt : x % 2 + 2 * ((x / 2) % 2 ^ w) < 2 * 2 ^ w := by omega
    have heq : x = (x % 2 + 2 * ((x / 2) % 2 ^ w)) + (2 * 2 ^ w) * ((x / 2) / 2 ^ w) := by
      calc
        x = 2 * (x / 2) + x % 2 := h1.symm
        _ = 2 * (2 ^ w * ((x / 2) / 2 ^ w) + (x / 2) % 2 ^ w) + x % 2 := by rw [h2]
        _ = (x % 2 + 2 * ((x / 2) % 2 ^ w)) + (2 * 2 ^ w) * ((x / 2) / 2 ^ w) := by ring
    conv_rhs => rw [heq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Round-trip decoding of `encodeNatBits w x` when `x < 2 ^ w`. -/
@[simp]
theorem decodeNatBits_encodeNatBits (w x : ℕ) (hx : x < 2 ^ w) :
    decodeNatBits (encodeNatBits w x) = x := by
  rw [decodeNatBits_encodeNatBits_mod, Nat.mod_eq_of_lt hx]

/-- Any decoded bit list of length `L` represents a natural number `< 2 ^ L`. -/
theorem decodeNatBits_lt (bs : List Bool) : decodeNatBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [decodeNatBits]
  | cons b bs ih =>
    simp only [decodeNatBits, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

/-- Round-trip encoding of `decodeNatBits bs` back to `bs`. -/
@[simp]
theorem encodeNatBits_decodeNatBits (bs : List Bool) :
    encodeNatBits bs.length (decodeNatBits bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, encodeNatBits_succ, decodeNatBits]
    have hbit : ((bif b then 1 else 0) + 2 * decodeNatBits bs).testBit 0 = b := by
      rw [Nat.testBit_zero]
      cases b <;> simp
    have hdiv : ((bif b then 1 else 0) + 2 * decodeNatBits bs) / 2 = decodeNatBits bs := by
      cases b
      · simp
      · simp
        omega
    rw [hbit, hdiv, ih]

/-! ## 2. Real & Complex Quantization Error Bounds (Section 3.2 (`sec:prelim-model`), Definition 3.1 (`def:grid`)) -/

/-- Round-half-up floor quantization $\lfloor y + 1/2 \rfloor$ is within $1/2$ of $y$ for all $y \in \mathbb{R}$. -/
theorem abs_floor_add_half_sub_le (y : ℝ) :
    |(⌊y + (1 / 2 : ℝ)⌋ : ℝ) - y| ≤ (1 / 2 : ℝ) := by
  rw [abs_le]
  have h1 : (⌊y + (1 / 2 : ℝ)⌋ : ℝ) ≤ y + (1 / 2 : ℝ) := Int.floor_le (y + 1 / 2)
  have h2 : y + (1 / 2 : ℝ) < (⌊y + (1 / 2 : ℝ)⌋ : ℝ) + 1 := Int.lt_floor_add_one (y + 1 / 2)
  constructor <;> linarith

/-- Mantissa error bound $|\lfloor 2^q x + 1/2 \rfloor - 2^q x| \le 1/2$. -/
theorem abs_quantizeRealMantissa_sub_le (q : ℕ) (x : ℝ) :
    |(quantizeRealMantissa q x : ℝ) - x * (2 : ℝ) ^ q| ≤ (1 / 2 : ℝ) :=
  abs_floor_add_half_sub_le (x * (2 : ℝ) ^ q)

/-- Cancellation identity $2^q \cdot 2^{-q} = 1$ in $\mathbb{R}$. -/
theorem two_pow_mul_two_zpow_neg (q : ℕ) :
    (2 : ℝ) ^ q * (2 : ℝ) ^ (-(q : ℤ)) = 1 := by
  rw [← zpow_natCast (2 : ℝ) q, ← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]

/-- Real quantization error bound $|Q_q(x) - x| \le \frac{1}{2} 2^{-q}$
(Section 3.2 (`sec:prelim-model`), equation (4) (`eq:quant-err`)). -/
theorem abs_quantizeReal_sub_self_le (q : ℕ) (x : ℝ) :
    |quantizeReal q x - x| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  unfold quantizeReal
  have hx : (x * (2 : ℝ) ^ q) * (2 : ℝ) ^ (-(q : ℤ)) = x := by
    rw [mul_assoc, two_pow_mul_two_zpow_neg, mul_one]
  have hdiff : (quantizeRealMantissa q x : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - x =
      ((quantizeRealMantissa q x : ℝ) - x * (2 : ℝ) ^ q) * (2 : ℝ) ^ (-(q : ℤ)) := by
    calc
      (quantizeRealMantissa q x : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) - x
        = (quantizeRealMantissa q x : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) -
            (x * (2 : ℝ) ^ q) * (2 : ℝ) ^ (-(q : ℤ)) := by rw [hx]
      _ = ((quantizeRealMantissa q x : ℝ) - x * (2 : ℝ) ^ q) * (2 : ℝ) ^ (-(q : ℤ)) := by ring
  rw [hdiff, abs_mul]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  rw [abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_right (abs_quantizeRealMantissa_sub_le q x) (le_of_lt hpos)

namespace FixedComplex

@[simp]
theorem toComplex_re {q : ℕ} (z : FixedComplex q) :
    z.toComplex.re = (z.re : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  unfold toComplex
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]

@[simp]
theorem toComplex_im {q : ℕ} (z : FixedComplex q) :
    z.toComplex.im = (z.im : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  unfold toComplex
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    mul_one, Complex.ofReal_re, Complex.I_re, mul_zero, add_zero, zero_add]

@[simp]
theorem toComplex_zero {q : ℕ} : (0 : FixedComplex q).toComplex = 0 := by
  apply Complex.ext <;> simp [show (0 : FixedComplex q).re = 0 from rfl,
    show (0 : FixedComplex q).im = 0 from rfl]

@[simp]
theorem toComplex_add {q : ℕ} (z w : FixedComplex q) :
    (z.add w).toComplex = z.toComplex + w.toComplex := by
  apply Complex.ext <;> simp [add, add_mul]

@[simp]
theorem toComplex_add_op {q : ℕ} (z w : FixedComplex q) :
    (z + w).toComplex = z.toComplex + w.toComplex :=
  toComplex_add z w

@[simp]
theorem toComplex_sub {q : ℕ} (z w : FixedComplex q) :
    (z.sub w).toComplex = z.toComplex - w.toComplex := by
  apply Complex.ext <;> simp [sub, sub_mul]

@[simp]
theorem toComplex_sub_op {q : ℕ} (z w : FixedComplex q) :
    (z - w).toComplex = z.toComplex - w.toComplex :=
  toComplex_sub z w

@[simp]
theorem toComplex_neg {q : ℕ} (z : FixedComplex q) :
    z.neg.toComplex = -z.toComplex := by
  apply Complex.ext <;> simp [neg, neg_mul]

@[simp]
theorem toComplex_neg_op {q : ℕ} (z : FixedComplex q) :
    (-z).toComplex = -z.toComplex :=
  toComplex_neg z

@[simp]
theorem toComplex_conj {q : ℕ} (z : FixedComplex q) :
    z.conj.toComplex = starRingEnd ℂ z.toComplex := by
  apply Complex.ext <;> simp [conj, neg_mul]

end FixedComplex

@[simp]
theorem quantizeComplex_re (q : ℕ) (z : ℂ) :
    (quantizeComplex q z).re = quantizeReal q z.re := by
  simp [quantizeComplex, quantizeComplexFixed, quantizeReal]

@[simp]
theorem quantizeComplex_im (q : ℕ) (z : ℂ) :
    (quantizeComplex q z).im = quantizeReal q z.im := by
  simp [quantizeComplex, quantizeComplexFixed, quantizeReal]

/-- Bounding the Euclidean norm `‖w‖` on $\mathbb{C}$ by $\sqrt{2}$ times a uniform coordinate bound $B$
(Section 3.2 (`sec:prelim-model`)). -/
theorem norm_complex_le_of_re_im_le {w : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hre : |w.re| ≤ B) (him : |w.im| ≤ B) :
    ‖w‖ ≤ Real.sqrt 2 * B := by
  have hre2 : w.re ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs w.re, ← sq_abs B]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rwa [abs_of_nonneg hB]) 2
  have him2 : w.im ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs w.im, ← sq_abs B]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rwa [abs_of_nonneg hB]) 2
  have hsq : ‖w‖ ^ 2 ≤ (Real.sqrt 2 * B) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, Real.sq_sqrt (by norm_num)]
    linarith
  have hnonneg : 0 ≤ Real.sqrt 2 * B := mul_nonneg (Real.sqrt_nonneg 2) hB
  nlinarith [norm_nonneg w]

/-- Complex quantization error bound $\|Q_q(z) - z\| \le \frac{\sqrt{2}}{2} 2^{-q}$
(Section 3.2 (`sec:prelim-model`), equation (4) (`eq:quant-err`)). -/
theorem norm_quantizeComplex_sub_self_le (q : ℕ) (z : ℂ) :
    ‖quantizeComplex q z - z‖ ≤ (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) := by
  have hB : 0 ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by positivity
  have hre : |(quantizeComplex q z - z).re| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    simpa using abs_quantizeReal_sub_self_le q z.re
  have him : |(quantizeComplex q z - z).im| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    simpa using abs_quantizeReal_sub_self_le q z.im
  calc
    ‖quantizeComplex q z - z‖ ≤ Real.sqrt 2 * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) :=
      norm_complex_le_of_re_im_le hB hre him
    _ = (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) := by ring

/-- Quantizing $z \in \mathbb{C}$ to $p + 2$ fractional bits incurs error at most
$\frac{\sqrt{2}}{8} 2^{-p} \le \frac{\sqrt{2}}{4} 2^{-p}$ (Section 3.2 (`sec:prelim-model`)). -/
theorem norm_quantizeComplex_p_add_two_sub_self_le (p : ℕ) (z : ℂ) :
    ‖quantizeComplex (p + 2) z - z‖ ≤ (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have h := norm_quantizeComplex_sub_self_le (p + 2) z
  have hexp : -((p + 2 : ℕ) : ℤ) = -(p : ℤ) + (-2 : ℤ) := by push_cast; ring
  have hpow : (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(p : ℤ)) * (1 / 4 : ℝ) := by
    rw [hexp, zpow_add₀ (by norm_num)]
    norm_num
  rw [hpow] at h
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hsqrt : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- Rational upper bound $\sqrt{2} \le 72/50 = 1.44$. -/
theorem sqrt_two_le : Real.sqrt 2 ≤ (72 / 50 : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- Numerical bound $\frac{\sqrt{2}}{4} \le \frac{18}{50} = 0.36$ (used in Lemma 3.5 (`lem:syn-fft`), Table 3 (`tab:lean-map`)). -/
theorem sqrt_two_div_four_le : Real.sqrt 2 / 4 ≤ (18 / 50 : ℝ) := by
  have := sqrt_two_le
  linarith

/-- Numerical bound $\frac{\sqrt{2}/4}{2} \le \frac{18}{100} = 0.18$ (Lemma 3.5 (`lem:syn-fft`), Table 3 (`tab:lean-map`)). -/
theorem sqrt_two_div_eight_le : (Real.sqrt 2 / 4) / 2 ≤ (18 / 100 : ℝ) := by
  have := sqrt_two_div_four_le
  linarith

/-! ## 3. `roundShiftInt` and Fixed-Point Multiplication (Section 3.2 (`sec:prelim-model`), Definition 3.1 (`def:grid`)) -/

/-- Exact identity between integer shift-rounding `roundShiftInt m k` and floor rounding
$\lfloor m / 2^k + 1/2 \rfloor$ for all $m \in \mathbb{Z}$ and $k \in \mathbb{N}$
(Definition 3.1 (`def:grid`), Section 8 (`sec:lean`)). -/
theorem roundShiftInt_eq_quantizeRealMantissa (m : ℤ) (k : ℕ) :
    roundShiftInt m k = ⌊(m : ℝ) / (2 : ℝ) ^ k + (1 / 2 : ℝ)⌋ := by
  unfold roundShiftInt
  split_ifs with hk
  · subst hk
    simp only [pow_zero, div_one]
    rw [Int.floor_intCast_add]
    have hfl : ⌊(1 / 2 : ℝ)⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num
    omega
  · symm
    rw [Int.floor_eq_iff]
    set a : ℤ := m + (2 : ℤ) ^ (k - 1)
    set b : ℤ := (2 : ℤ) ^ k
    have hb_pos : (0 : ℤ) < b := by positivity
    have hb_rpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    have hk1 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk), pow_succ]
    have half_eq : (m : ℝ) / (2 : ℝ) ^ k + (1 / 2 : ℝ) = (a : ℝ) / (2 : ℝ) ^ k := by
      simp only [a, Int.cast_add, Int.cast_pow, Int.cast_ofNat]
      rw [add_div, hk1]
      have h2pos : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
      field_simp
    rw [half_eq]
    have ha_real : (a : ℝ) = (2 : ℝ) ^ k * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by
      have hcast : ((b * (a / b) + a % b : ℤ) : ℝ) = (a : ℝ) := by exact_mod_cast hdiv
      simpa [b] using hcast.symm
    have hr0 : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast hmod0
    have hr1 : ((a % b : ℤ) : ℝ) < (2 : ℝ) ^ k := by
      have : ((a % b : ℤ) : ℝ) < (b : ℝ) := by exact_mod_cast hmod1
      simpa [b] using this
    constructor
    · rw [le_div_iff₀ hb_rpos, ha_real]
      linarith
    · rw [div_lt_iff₀ hb_rpos, ha_real]
      linarith

/-- Mantissa rounding error bound $|\text{roundShiftInt}(m, k) - m / 2^k| \le 1/2$. -/
theorem abs_roundShiftInt_sub_div_le (m : ℤ) (k : ℕ) :
    |(roundShiftInt m k : ℝ) - (m : ℝ) / (2 : ℝ) ^ k| ≤ (1 / 2 : ℝ) := by
  rw [roundShiftInt_eq_quantizeRealMantissa]
  exact abs_floor_add_half_sub_le ((m : ℝ) / (2 : ℝ) ^ k)

namespace FixedComplex

/-- Fixed-point complex multiplication in $\tilde{\mathbb{C}}_q$ with a single floor-shifted rounding
per output component (Section 3.2 (`sec:prelim-model`), Definition 3.1 (`def:grid`)). -/
def mulRounded {q : ℕ} (z w : FixedComplex q) : FixedComplex q :=
  ⟨roundShiftInt (z.re * w.re - z.im * w.im) q,
   roundShiftInt (z.re * w.im + z.im * w.re) q⟩

/-- `FixedComplex.mulRounded z w` is equal to `quantizeComplexFixed q (z.toComplex * w.toComplex)`. -/
theorem mulRounded_eq_quantizeComplexFixed {q : ℕ} (z w : FixedComplex q) :
    mulRounded z w = quantizeComplexFixed q (z.toComplex * w.toComplex) := by
  have hzpow : (2 : ℝ) ^ (-(q : ℤ)) = ((2 : ℝ) ^ q)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  ext
  · simp only [mulRounded, quantizeComplexFixed, quantizeRealMantissa,
      roundShiftInt_eq_quantizeRealMantissa, Complex.mul_re, toComplex_re, toComplex_im, hzpow]
    congr 2
    have h2 : (2 : ℝ) ^ q ≠ 0 := by positivity
    push_cast
    field_simp
  · simp only [mulRounded, quantizeComplexFixed, quantizeRealMantissa,
      roundShiftInt_eq_quantizeRealMantissa, Complex.mul_im, toComplex_re, toComplex_im, hzpow]
    congr 2
    have h2 : (2 : ℝ) ^ q ≠ 0 := by positivity
    push_cast
    field_simp

/-- Converting `FixedComplex.mulRounded z w` to $\mathbb{C}$ equals `quantizeComplex q (z.toComplex * w.toComplex)`. -/
theorem toComplex_mulRounded {q : ℕ} (z w : FixedComplex q) :
    (mulRounded z w).toComplex = quantizeComplex q (z.toComplex * w.toComplex) := by
  rw [mulRounded_eq_quantizeComplexFixed, quantizeComplex]

/-- Complex rounding error bound for fixed-point complex multiplication:
$\|(\text{mulRounded } z \, w).\text{toComplex} - z.\text{toComplex} \cdot w.\text{toComplex}\| \le \frac{\sqrt{2}}{2} 2^{-q}$
(Section 3.2 (`sec:prelim-model`)). -/
theorem norm_mulRounded_sub_mul_le {q : ℕ} (z w : FixedComplex q) :
    ‖(mulRounded z w).toComplex - z.toComplex * w.toComplex‖ ≤
      (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) := by
  rw [toComplex_mulRounded]
  exact norm_quantizeComplex_sub_self_le q (z.toComplex * w.toComplex)

end FixedComplex

/-! ## 4. Signed Word-Width Bounds (`FitsSignedWord`, `WordWidthBounds`, Section 3.2 (`sec:prelim-model`)) -/

/-- Monotonicity of `FitsSignedWord` in the bit-width `w`. -/
theorem FitsSignedWord.mono {w1 w2 : ℕ} {m : ℤ} (h : FitsSignedWord w1 m) (hw : w1 ≤ w2) :
    FitsSignedWord w2 m := by
  unfold FitsSignedWord at *
  have hpow : (2 : ℤ) ^ w1 ≤ (2 : ℤ) ^ w2 :=
     pow_le_pow_right₀ (by norm_num) hw
  omega

/-- Zero fits in any signed word width `w`. -/
theorem FitsSignedWord.zero (w : ℕ) : FitsSignedWord w 0 := by
  unfold FitsSignedWord
  simp only [abs_zero]
  positivity

/-- Closure of `FitsSignedWord` under negation. -/
theorem FitsSignedWord.neg {w : ℕ} {m : ℤ} (h : FitsSignedWord w m) :
    FitsSignedWord w (-m) := by
  unfold FitsSignedWord at *
  rwa [abs_neg]

/-- Adding two `w`-bit signed integers fits in `w + 1` bits. -/
theorem FitsSignedWord.add {w : ℕ} {m1 m2 : ℤ}
    (h1 : FitsSignedWord w m1) (h2 : FitsSignedWord w m2) :
    FitsSignedWord (w + 1) (m1 + m2) := by
  unfold FitsSignedWord at *
  have htri := abs_add_le m1 m2
  rw [pow_succ]
  omega

/-- Subtracting two `w`-bit signed integers fits in `w + 1` bits. -/
theorem FitsSignedWord.sub {w : ℕ} {m1 m2 : ℤ}
    (h1 : FitsSignedWord w m1) (h2 : FitsSignedWord w m2) :
    FitsSignedWord (w + 1) (m1 - m2) := by
  rw [sub_eq_add_neg]
  exact h1.add h2.neg

/-- Multiplying a `w1`-bit and a `w2`-bit signed integer fits in `w1 + w2` bits. -/
theorem FitsSignedWord.mul {w1 w2 : ℕ} {m1 m2 : ℤ}
    (h1 : FitsSignedWord w1 m1) (h2 : FitsSignedWord w2 m2) :
    FitsSignedWord (w1 + w2) (m1 * m2) := by
  unfold FitsSignedWord at *
  rw [abs_mul, pow_add]
  exact mul_lt_mul'' h1 h2 (abs_nonneg m1) (abs_nonneg m2)

/-- Right-shifting a `w`-bit signed integer by `k` bits via `roundShiftInt` fits in `w + 1` bits. -/
theorem FitsSignedWord.roundShiftInt_le {w : ℕ} (k : ℕ) {m : ℤ}
    (h : FitsSignedWord w m) :
    FitsSignedWord (w + 1) (roundShiftInt m k) := by
  unfold FitsSignedWord at *
  have hcast : |(m : ℝ)| < (2 : ℝ) ^ w := by exact_mod_cast h
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hdiv : |(m : ℝ) / (2 : ℝ) ^ k| < (2 : ℝ) ^ w := by
    rw [abs_div, abs_of_pos h2k]
    exact lt_of_le_of_lt (div_le_self (abs_nonneg (m : ℝ)) hpow) hcast
  have herr := abs_roundShiftInt_sub_div_le m k
  have htri : |(roundShiftInt m k : ℝ)| ≤
      |(roundShiftInt m k : ℝ) - (m : ℝ) / (2 : ℝ) ^ k| + |(m : ℝ) / (2 : ℝ) ^ k| := by
    have := abs_add_le ((roundShiftInt m k : ℝ) - (m : ℝ) / (2 : ℝ) ^ k) ((m : ℝ) / (2 : ℝ) ^ k)
    simpa using this
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ w := one_le_pow₀ (by norm_num)
  have hbound : |(roundShiftInt m k : ℝ)| < (2 : ℝ) ^ (w + 1) := by
    rw [pow_succ]
    linarith
  exact_mod_cast hbound

/-- Equivalence between `FitsSignedWord w m` and `m.natAbs < 2 ^ w`. -/
theorem fitsSignedWord_iff_natAbs_lt (w : ℕ) (m : ℤ) :
    FitsSignedWord w m ↔ m.natAbs < 2 ^ w := by
  unfold FitsSignedWord
  rw [← Int.natCast_natAbs]
  exact_mod_cast Iff.rfl

/-- Right-shifting a `(w + k)`-bit signed integer by `k` bits via `roundShiftInt` fits in `w + 1` bits. -/
theorem FitsSignedWord.roundShiftInt_sub {w k : ℕ} {m : ℤ}
    (h : FitsSignedWord (w + k) m) :
    FitsSignedWord (w + 1) (roundShiftInt m k) := by
  unfold FitsSignedWord roundShiftInt at *
  split_ifs with hk0
  · subst hk0
    rw [Nat.add_zero] at h
    exact lt_of_lt_of_le h (pow_le_pow_right₀ (by norm_num) (Nat.le_succ w))
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have hb_pos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
    set a : ℤ := m + (2 : ℤ) ^ (k - 1)
    set b : ℤ := (2 : ℤ) ^ k
    have ha : a = m + (2 : ℤ) ^ (k - 1) := rfl
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    have hpow_wk : (2 : ℤ) ^ (w + k) = (2 : ℤ) ^ w * b := by
      simp [b, pow_add]
    have h2k_pos : (0 : ℤ) ≤ (2 : ℤ) ^ (k - 1) := by positivity
    have h2k : (2 : ℤ) ^ (k - 1) ≤ b :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
    have h1w : 1 ≤ (2 : ℤ) ^ w := one_le_pow₀ (by norm_num)
    have hm_lo : -(2 : ℤ) ^ (w + k) < m := (abs_lt.mp h).1
    have hm_hi : m < (2 : ℤ) ^ (w + k) := (abs_lt.mp h).2
    have hq_lo : -(2 : ℤ) ^ (w + 1) < a / b := by
      rw [pow_succ]
      nlinarith
    have hq_hi : a / b < (2 : ℤ) ^ (w + 1) := by
      rw [pow_succ]
      nlinarith
    exact abs_lt.mpr ⟨hq_lo, hq_hi⟩

/-- `roundShiftInt m k` never exceeds `|m|` in absolute value. -/
theorem abs_roundShiftInt_le_self (m : ℤ) (k : ℕ) :
    |roundShiftInt m k| ≤ |m| := by
  unfold roundShiftInt
  split_ifs with hk0
  · exact le_rfl
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    set b : ℤ := (2 : ℤ) ^ k
    set c : ℤ := (2 : ℤ) ^ (k - 1)
    have hb_eq : b = 2 * c := by
      dsimp [b, c]
      conv_lhs => rw [← Nat.sub_add_cancel hk_pos, pow_succ']
    have hc_pos : (0 : ℤ) < c := by positivity
    have hb_pos : (0 : ℤ) < b := by omega
    set a : ℤ := m + c
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    rcases le_or_gt 0 m with hm | hm
    · have hq0 : 0 ≤ a / b := by nlinarith
      have hqm : a / b ≤ m := by nlinarith
      rw [abs_of_nonneg hq0, abs_of_nonneg hm]
      exact hqm
    · have hq0 : a / b ≤ 0 := by nlinarith
      have hqm : m ≤ a / b := by nlinarith
      rw [abs_of_nonpos hq0, abs_of_neg hm]
      omega

/-- Right-shifting a `w`-bit signed integer by `k` bits via `roundShiftInt` fits in `w` bits. -/
theorem FitsSignedWord.roundShiftInt_self {w : ℕ} (k : ℕ) {m : ℤ}
    (h : FitsSignedWord w m) :
    FitsSignedWord w (roundShiftInt m k) :=
  lt_of_le_of_lt (abs_roundShiftInt_le_self m k) h

/-- Averaging two `w`-bit signed integers via `roundShiftInt (m1 + m2) 1` fits in `w` bits. -/
theorem FitsSignedWord.halfRounded_add {w : ℕ} {m1 m2 : ℤ}
    (h1 : FitsSignedWord w m1) (h2 : FitsSignedWord w m2) :
    FitsSignedWord w (roundShiftInt (m1 + m2) 1) := by
  unfold FitsSignedWord at *
  change |(m1 + m2 + 1) / 2| < (2 : ℤ) ^ w
  set a : ℤ := m1 + m2 + 1
  have hdiv : 2 * (a / 2) + a % 2 = a := Int.mul_ediv_add_emod a 2
  have hmod0 : 0 ≤ a % 2 := Int.emod_nonneg a (by decide)
  have hmod1 : a % 2 < 2 := Int.emod_lt_of_pos a (by decide)
  have h1' := abs_lt.mp h1
  have h2' := abs_lt.mp h2
  exact abs_lt.mpr ⟨by omega, by omega⟩

/-- Half-difference of two `w`-bit signed integers via `roundShiftInt (m1 - m2) 1` fits in `w` bits. -/
theorem FitsSignedWord.halfRounded_sub {w : ℕ} {m1 m2 : ℤ}
    (h1 : FitsSignedWord w m1) (h2 : FitsSignedWord w m2) :
    FitsSignedWord w (roundShiftInt (m1 - m2) 1) := by
  rw [sub_eq_add_neg]
  exact h1.halfRounded_add h2.neg

theorem fitsSignedWord_iff_abs_lt (w : ℕ) (m : ℤ) :
    FitsSignedWord w m ↔ |m| < (2 : ℤ) ^ w := Iff.rfl

theorem fitsSignedWord_of_abs_le_two_pow {w1 w2 : ℕ} (hw : w1 < w2) {m : ℤ}
    (hm : |m| ≤ (2 : ℤ) ^ w1) :
    FitsSignedWord w2 m :=
  lt_of_le_of_lt hm (pow_lt_pow_right₀ (by decide) hw)

theorem FitsSignedWord.two_pow (k : ℕ) : FitsSignedWord (k + 1) ((2 : ℤ) ^ k) := by
  unfold FitsSignedWord
  rw [abs_of_pos (by positivity)]
  exact pow_lt_pow_right₀ (by decide) (Nat.lt_succ_self k)

theorem FitsSignedWord.mul_two_pow {w : ℕ} {m : ℤ} (h : FitsSignedWord w m) (k : ℕ) :
    FitsSignedWord (w + k) (m * (2 : ℤ) ^ k) := by
  unfold FitsSignedWord at *
  have hk : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  rw [abs_mul, abs_of_pos hk, pow_add]
  exact mul_lt_mul_of_pos_right h hk

theorem FitsSignedWord.roundShiftInt {w : ℕ} (k : ℕ) {m : ℤ}
    (h : FitsSignedWord w m) :
    FitsSignedWord w (roundShiftInt m k) :=
  h.roundShiftInt_self k

@[simp]
theorem roundShiftInt_zero (m : ℤ) : roundShiftInt m 0 = m := by
  simp [roundShiftInt]

/-- Monotonicity of `WordWidthBounds` in the bit-width `w`. -/
theorem WordWidthBounds.mono {w1 w2 q : ℕ} {z : FixedComplex q}
    (h : WordWidthBounds w1 z) (hw : w1 ≤ w2) :
    WordWidthBounds w2 z :=
  ⟨h.1.mono hw, h.2.mono hw⟩

/-- Zero satisfies `WordWidthBounds w` for all `w`. -/
theorem WordWidthBounds.zero (w q : ℕ) : WordWidthBounds w (0 : FixedComplex q) :=
  ⟨FitsSignedWord.zero w, FitsSignedWord.zero w⟩

/-- Closure of `WordWidthBounds` under `FixedComplex.neg`. -/
theorem WordWidthBounds.neg {w q : ℕ} {z : FixedComplex q} (h : WordWidthBounds w z) :
    WordWidthBounds w z.neg :=
  ⟨h.1.neg, h.2.neg⟩

/-- Closure of `WordWidthBounds` under `FixedComplex.conj`. -/
theorem WordWidthBounds.conj {w q : ℕ} {z : FixedComplex q} (h : WordWidthBounds w z) :
    WordWidthBounds w z.conj :=
  ⟨h.1, h.2.neg⟩

/-- Closure of `WordWidthBounds` under `FixedComplex.add`. -/
theorem WordWidthBounds.add {w q : ℕ} {z1 z2 : FixedComplex q}
    (h1 : WordWidthBounds w z1) (h2 : WordWidthBounds w z2) :
    WordWidthBounds (w + 1) (z1.add z2) :=
  ⟨h1.1.add h2.1, h1.2.add h2.2⟩

/-- Closure of `WordWidthBounds` under `FixedComplex.sub`. -/
theorem WordWidthBounds.sub {w q : ℕ} {z1 z2 : FixedComplex q}
    (h1 : WordWidthBounds w z1) (h2 : WordWidthBounds w z2) :
    WordWidthBounds (w + 1) (z1.sub z2) :=
  ⟨h1.1.sub h2.1, h1.2.sub h2.2⟩

/-- Closure of `WordWidthBounds` under `FixedComplex.mulRounded`. -/
theorem WordWidthBounds.mulRounded {w1 w2 q : ℕ} {z1 z2 : FixedComplex q}
    (h1 : WordWidthBounds w1 z1) (h2 : WordWidthBounds w2 z2) :
    WordWidthBounds (w1 + w2 + 2) (FixedComplex.mulRounded z1 z2) := by
  refine ⟨?_, ?_⟩
  · exact ((h1.1.mul h2.1).sub (h1.2.mul h2.2)).roundShiftInt_le q
  · exact ((h1.1.mul h2.2).add (h1.2.mul h2.1)).roundShiftInt_le q

/-- Tighter closure of `WordWidthBounds` under `FixedComplex.mulRounded` accounting for the
right-shift by `q` bits: if `z1` fits in `w1` bits and `z2` fits in `q + d` bits, their
`mulRounded` product fits in `w1 + d + 2` bits. -/
theorem WordWidthBounds.mulRounded_sub {w1 d q : ℕ} {z1 z2 : FixedComplex q}
    (h1 : WordWidthBounds w1 z1) (h2 : WordWidthBounds (q + d) z2) :
    WordWidthBounds (w1 + d + 2) (FixedComplex.mulRounded z1 z2) := by
  have h1' : FitsSignedWord (w1 + d + 1 + q) (z1.re * z2.re - z1.im * z2.im) := by
    have hm : FitsSignedWord (w1 + (q + d) + 1) (z1.re * z2.re - z1.im * z2.im) :=
      (h1.1.mul h2.1).sub (h1.2.mul h2.2)
    exact hm.mono (by omega)
  have h2' : FitsSignedWord (w1 + d + 1 + q) (z1.re * z2.im + z1.im * z2.re) := by
    have hm : FitsSignedWord (w1 + (q + d) + 1) (z1.re * z2.im + z1.im * z2.re) :=
      (h1.1.mul h2.2).add (h1.2.mul h2.1)
    exact hm.mono (by omega)
  exact ⟨h1'.roundShiftInt_sub, h2'.roundShiftInt_sub⟩

theorem WordWidthBounds.mulRounded_sub_left {d w2 q : ℕ} {z1 z2 : FixedComplex q}
    (h1 : WordWidthBounds (q + d) z1) (h2 : WordWidthBounds w2 z2) :
    WordWidthBounds (d + w2 + 2) (FixedComplex.mulRounded z1 z2) := by
  have h1' : FitsSignedWord (d + w2 + 1 + q) (z1.re * z2.re - z1.im * z2.im) := by
    have hm : FitsSignedWord ((q + d) + w2 + 1) (z1.re * z2.re - z1.im * z2.im) :=
      (h1.1.mul h2.1).sub (h1.2.mul h2.2)
    exact hm.mono (by omega)
  have h2' : FitsSignedWord (d + w2 + 1 + q) (z1.re * z2.im + z1.im * z2.re) := by
    have hm : FitsSignedWord ((q + d) + w2 + 1) (z1.re * z2.im + z1.im * z2.re) :=
      (h1.1.mul h2.2).add (h1.2.mul h2.1)
    exact hm.mono (by omega)
  exact ⟨h1'.roundShiftInt_sub, h2'.roundShiftInt_sub⟩

/-- Any `z : FixedComplex q` with `‖z.toComplex‖ < 2 ^ b` satisfies `WordWidthBounds (b + q) z`. -/
theorem wordWidthBounds_of_norm_toComplex_lt {b q : ℕ} {z : FixedComplex q}
    (hz : ‖z.toComplex‖ < (2 : ℝ) ^ b) :
    WordWidthBounds (b + q) z := by
  have h_coord : ∀ (m : ℤ), |(m : ℝ) * (2 : ℝ) ^ (-(q : ℤ))| < (2 : ℝ) ^ b →
      FitsSignedWord (b + q) m := by
    intro m hm
    unfold FitsSignedWord
    have h2q : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
    rw [abs_mul, abs_of_pos h2q] at hm
    have hpow : (2 : ℝ) ^ (b + q) = (2 : ℝ) ^ b / (2 : ℝ) ^ (-(q : ℤ)) := by
      rw [pow_add, zpow_neg, zpow_natCast, div_inv_eq_mul]
    have hlt : |(m : ℝ)| < (2 : ℝ) ^ (b + q) := by
      rw [hpow, lt_div_iff₀ h2q]
      exact hm
    exact_mod_cast hlt
  refine ⟨h_coord z.re ?_, h_coord z.im ?_⟩
  · rw [← FixedComplex.toComplex_re]
    exact lt_of_le_of_lt (Complex.abs_re_le_norm z.toComplex) hz
  · rw [← FixedComplex.toComplex_im]
    exact lt_of_le_of_lt (Complex.abs_im_le_norm z.toComplex) hz

/-- Any `z : FixedComplex q` with `‖z.toComplex‖ ≤ 2 ^ b` satisfies `WordWidthBounds (b + q + 1) z`. -/
theorem wordWidthBounds_of_norm_toComplex_le {b q : ℕ} {z : FixedComplex q}
    (hz : ‖z.toComplex‖ ≤ (2 : ℝ) ^ b) :
    WordWidthBounds (b + q + 1) z := by
  have hlt : ‖z.toComplex‖ < (2 : ℝ) ^ (b + 1) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
    rw [pow_succ]
    linarith
  have hw := wordWidthBounds_of_norm_toComplex_lt hlt
  exact hw.mono (by omega)

/-- `WordWidthBounds w z` bounds the real part $|z.\text{toComplex}.\text{re}| < 2^w \cdot 2^{-q}$. -/
theorem WordWidthBounds.abs_toComplex_re_lt {w q : ℕ} {z : FixedComplex q}
    (h : WordWidthBounds w z) :
    |z.toComplex.re| < (2 : ℝ) ^ w * (2 : ℝ) ^ (-(q : ℤ)) := by
  rw [FixedComplex.toComplex_re, abs_mul]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  rw [abs_of_pos hpos]
  have hre : |(z.re : ℝ)| < (2 : ℝ) ^ w := by exact_mod_cast h.1
  exact mul_lt_mul_of_pos_right hre hpos

/-- `WordWidthBounds w z` bounds the imaginary part $|z.\text{toComplex}.\text{im}| < 2^w \cdot 2^{-q}$. -/
theorem WordWidthBounds.abs_toComplex_im_lt {w q : ℕ} {z : FixedComplex q}
    (h : WordWidthBounds w z) :
    |z.toComplex.im| < (2 : ℝ) ^ w * (2 : ℝ) ^ (-(q : ℤ)) := by
  rw [FixedComplex.toComplex_im, abs_mul]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  rw [abs_of_pos hpos]
  have him : |(z.im : ℝ)| < (2 : ℝ) ^ w := by exact_mod_cast h.2
  exact mul_lt_mul_of_pos_right him hpos

/-- `WordWidthBounds w z` bounds the Euclidean modulus $\|z.\text{toComplex}\| \le \sqrt{2} \cdot 2^w \cdot 2^{-q}$. -/
theorem WordWidthBounds.norm_toComplex_le {w q : ℕ} {z : FixedComplex q}
    (h : WordWidthBounds w z) :
    ‖z.toComplex‖ ≤ Real.sqrt 2 * ((2 : ℝ) ^ w * (2 : ℝ) ^ (-(q : ℤ))) := by
  apply norm_complex_le_of_re_im_le (by positivity)
  · exact le_of_lt h.abs_toComplex_re_lt
  · exact le_of_lt h.abs_toComplex_im_lt

/-- Conversely, any complex number $z \in \mathbb{C}$ with $\|z\| \le 2^b$ quantizes into
`WordWidthBounds (b + q + 1) (quantizeComplexFixed q z)` (Section 3.2 (`sec:prelim-model`)). -/
theorem wordWidthBounds_quantizeComplexFixed_of_norm_le {b q : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (2 : ℝ) ^ b) :
    WordWidthBounds (b + q + 1) (quantizeComplexFixed q z) := by
  have h_coord : ∀ x : ℝ, |x| ≤ (2 : ℝ) ^ b → FitsSignedWord (b + q + 1) (quantizeRealMantissa q x) := by
    intro x hx
    unfold FitsSignedWord
    have h2q : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
    have hmul : |x * (2 : ℝ) ^ q| ≤ (2 : ℝ) ^ (b + q) := by
      rw [abs_mul, abs_of_pos h2q, pow_add]
      exact mul_le_mul_of_nonneg_right hx (le_of_lt h2q)
    have herr := abs_quantizeRealMantissa_sub_le q x
    have htri : |(quantizeRealMantissa q x : ℝ)| ≤
        |(quantizeRealMantissa q x : ℝ) - x * (2 : ℝ) ^ q| + |x * (2 : ℝ) ^ q| := by
      have := abs_add_le ((quantizeRealMantissa q x : ℝ) - x * (2 : ℝ) ^ q) (x * (2 : ℝ) ^ q)
      simpa using this
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (b + q) := one_le_pow₀ (by norm_num)
    have hlt : |(quantizeRealMantissa q x : ℝ)| < (2 : ℝ) ^ (b + q + 1) := by
      rw [pow_succ]
      linarith
    exact_mod_cast hlt
  refine ⟨h_coord z.re (le_trans (Complex.abs_re_le_norm z) hz),
          h_coord z.im (le_trans (Complex.abs_im_le_norm z) hz)⟩

/-! ## 5. Computable Integer Division Rounding (`roundDivInt`) and Single-Pass Recurrence Array (`buildRecurrenceArray`) -/

/-- Computable round-half-up integer division $\lfloor \text{num} / \text{den} + 1/2 \rfloor$ in pure `ℤ`
(`roundDivInt`, Section 3.2 (`sec:prelim-model`)). Handles `den > 0`, `den < 0`, and `den = 0` unconditionally
so that `roundDivInt num den = ⌊(num : ℝ) / (den : ℝ) + 1/2⌋` for all `num, den : ℤ`. -/
def roundDivInt (num den : ℤ) : ℤ :=
  if 0 < den then
    (2 * num + den) / (2 * den)
  else if den < 0 then
    (-2 * num - den) / (-2 * den)
  else
    0

/-- Unconditional identity between pure-integer `roundDivInt num den` and real floor rounding
$\lfloor (\text{num} : \mathbb{R}) / (\text{den} : \mathbb{R}) + 1/2 \rfloor$ for all `num, den : ℤ`. -/
theorem roundDivInt_eq_floor_div_add_half (num den : ℤ) :
    roundDivInt num den = ⌊(num : ℝ) / (den : ℝ) + (1 / 2 : ℝ)⌋ := by
  unfold roundDivInt
  split_ifs with hpos hneg
  · symm
    rw [Int.floor_eq_iff]
    set a : ℤ := 2 * num + den
    set b : ℤ := 2 * den
    have hb_pos : (0 : ℤ) < b := by omega
    have hden_rpos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hpos
    have hb_rpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    have half_eq : (num : ℝ) / (den : ℝ) + (1 / 2 : ℝ) = (a : ℝ) / (b : ℝ) := by
      simp only [a, b, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      have hden_ne : (den : ℝ) ≠ 0 := ne_of_gt hden_rpos
      field_simp
    rw [half_eq]
    have ha_real : (a : ℝ) = (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by
      have hcast : ((b * (a / b) + a % b : ℤ) : ℝ) = (a : ℝ) := by exact_mod_cast hdiv
      simpa using hcast.symm
    have hr0 : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast hmod0
    have hr1 : ((a % b : ℤ) : ℝ) < (b : ℝ) := by exact_mod_cast hmod1
    constructor
    · rw [le_div_iff₀ hb_rpos]
      linarith
    · rw [div_lt_iff₀ hb_rpos]
      linarith
  · symm
    rw [Int.floor_eq_iff]
    set a : ℤ := -2 * num - den
    set b : ℤ := -2 * den
    have hb_pos : (0 : ℤ) < b := by omega
    have hden_rneg : (den : ℝ) < 0 := by exact_mod_cast hneg
    have hb_rpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    have half_eq : (num : ℝ) / (den : ℝ) + (1 / 2 : ℝ) = (a : ℝ) / (b : ℝ) := by
      simp only [a, b, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat]
      have hden_ne : (den : ℝ) ≠ 0 := ne_of_lt hden_rneg
      field_simp
      ring
    rw [half_eq]
    have ha_real : (a : ℝ) = (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by
      have hcast : ((b * (a / b) + a % b : ℤ) : ℝ) = (a : ℝ) := by exact_mod_cast hdiv
      simpa using hcast.symm
    have hr0 : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast hmod0
    have hr1 : ((a % b : ℤ) : ℝ) < (b : ℝ) := by exact_mod_cast hmod1
    constructor
    · rw [le_div_iff₀ hb_rpos]
      linarith
    · rw [div_lt_iff₀ hb_rpos]
      linarith
  · have hden0 : den = 0 := by omega
    subst hden0
    simp only [Int.cast_zero, div_zero, zero_add]
    symm
    rw [Int.floor_eq_iff]
    constructor <;> norm_num

/-- Unconditional identity bridging fixed-point integer division `roundDivInt (a * 2^q2) b` to
`quantizeRealMantissa q2 ((a * 2^(-q1)) / (b * 2^(-q1)))`. -/
theorem roundDivInt_mul_two_pow_eq_quantizeRealMantissa (q1 q2 : ℕ) (a b : ℤ) :
    roundDivInt (a * (2 : ℤ) ^ q2) b =
      quantizeRealMantissa q2 (((a : ℝ) * (2 : ℝ) ^ (-(q1 : ℤ))) / ((b : ℝ) * (2 : ℝ) ^ (-(q1 : ℤ)))) := by
  rw [roundDivInt_eq_floor_div_add_half]
  unfold quantizeRealMantissa
  congr 2
  have h2nz : (2 : ℝ) ^ (-(q1 : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [mul_div_mul_right _ _ h2nz, div_mul_eq_mul_div]
  push_cast
  rfl

/-- Unconditional identity bridging fixed-point reciprocal `roundDivInt (2^(q1 + q2)) a` to
`quantizeRealMantissa q2 (((a : ℝ) * 2^(-q1))⁻¹)`. -/
theorem roundDivInt_two_pow_add_eq_quantizeRealMantissa_inv (q1 q2 : ℕ) (a : ℤ) :
    roundDivInt ((2 : ℤ) ^ (q1 + q2)) a =
      quantizeRealMantissa q2 (((a : ℝ) * (2 : ℝ) ^ (-(q1 : ℤ)))⁻¹) := by
  rw [roundDivInt_eq_floor_div_add_half]
  unfold quantizeRealMantissa
  congr 2
  rw [mul_inv, zpow_neg, zpow_natCast, inv_inv, pow_add]
  push_cast
  ring

/-- Unconditional identity bridging integer division `roundDivInt a n` to
`quantizeRealMantissa q ((a * 2^(-q)) / n)`. -/
theorem roundDivInt_eq_quantizeRealMantissa_div_nat (q : ℕ) (a : ℤ) (n : ℕ) :
    roundDivInt a (n : ℤ) =
      quantizeRealMantissa q (((a : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) / (n : ℝ)) := by
  rw [roundDivInt_eq_floor_div_add_half]
  unfold quantizeRealMantissa
  congr 2
  have hcancel : (2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
  calc
    (a : ℝ) / ((n : ℤ) : ℝ) = ((a : ℝ) / (n : ℝ)) * ((2 : ℝ) ^ (-(q : ℤ)) * (2 : ℝ) ^ q) := by
      rw [hcancel, mul_one, Int.cast_natCast]
    _ = ((a : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) / (n : ℝ) * (2 : ℝ) ^ q := by ring

/-- `roundDivInt num den` never exceeds `|num|` in absolute value. -/
theorem abs_roundDivInt_le_self (num den : ℤ) :
    |roundDivInt num den| ≤ |num| := by
  unfold roundDivInt
  split_ifs with h1 h2
  · set a : ℤ := 2 * num + den
    set b : ℤ := 2 * den
    have hb_pos : (0 : ℤ) < b := by omega
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    rcases le_or_gt 0 num with hnum | hnum
    · have hq0 : 0 ≤ a / b := by nlinarith
      have hqm : a / b ≤ num := by nlinarith
      rw [abs_of_nonneg hq0, abs_of_nonneg hnum]
      exact hqm
    · have hq0 : a / b ≤ 0 := by nlinarith
      have hqm : num ≤ a / b := by nlinarith
      rw [abs_of_nonpos hq0, abs_of_neg hnum]
      omega
  · set a : ℤ := -2 * num - den
    set b : ℤ := -2 * den
    have hb_pos : (0 : ℤ) < b := by omega
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    rcases le_or_gt 0 num with hnum | hnum
    · have hq0 : a / b ≤ 0 := by nlinarith
      have hqm : -num ≤ a / b := by nlinarith
      rw [abs_of_nonpos hq0, abs_of_nonneg hnum]
      omega
    · have hq0 : 0 ≤ a / b := by nlinarith
      have hqm : a / b ≤ -num := by nlinarith
      rw [abs_of_nonneg hq0, abs_of_neg hnum]
      exact hqm
  · exact abs_nonneg num

/-- Rounded integer division `roundDivInt num den` preserves `FitsSignedWord w`. -/
theorem FitsSignedWord.roundDivInt {w : ℕ} {num : ℤ} (den : ℤ)
    (h : FitsSignedWord w num) :
    FitsSignedWord w (roundDivInt num den) :=
  lt_of_le_of_lt (abs_roundDivInt_le_self num den) h

/-- If `|num| ≤ M * |den|`, then `|roundDivInt num den| ≤ M`. -/
theorem abs_roundDivInt_le_of_abs_le_mul {num den M : ℤ} (hM : 0 ≤ M)
    (h : |num| ≤ M * |den|) :
    |roundDivInt num den| ≤ M := by
  unfold roundDivInt
  split_ifs with h1 h2
  · have hden_abs : |den| = den := abs_of_pos h1
    rw [hden_abs] at h
    rcases abs_le.mp h with ⟨hlo, hhi⟩
    set a : ℤ := 2 * num + den
    set b : ℤ := 2 * den
    have hb_pos : (0 : ℤ) < b := by omega
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · have hden_abs : |den| = -den := abs_of_neg h2
    rw [hden_abs] at h
    rcases abs_le.mp h with ⟨hlo, hhi⟩
    set a : ℤ := -2 * num - den
    set b : ℤ := -2 * den
    have hb_pos : (0 : ℤ) < b := by omega
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · simpa using hM

/-- If `|a| ≤ |b|`, then `|roundDivInt (a * 2^q) b| ≤ 2^q`. -/
theorem abs_roundDivInt_le_two_pow_of_abs_le {q : ℕ} {a b : ℤ} (h : |a| ≤ |b|) :
    |roundDivInt (a * (2 : ℤ) ^ q) b| ≤ (2 : ℤ) ^ q := by
  have h2q : (0 : ℤ) ≤ (2 : ℤ) ^ q := by positivity
  refine abs_roundDivInt_le_of_abs_le_mul h2q ?_
  rw [abs_mul, abs_of_nonneg h2q, mul_comm]
  exact mul_le_mul_of_nonneg_left h h2q

/-- If `|r| ≤ 2^q`, then `|roundShiftInt (r * x) q| ≤ |x|` for all `x : ℤ`. -/
theorem abs_roundShiftInt_mul_le_of_abs_le_two_pow {q : ℕ} {r x : ℤ}
    (hr : |r| ≤ (2 : ℤ) ^ q) :
    |roundShiftInt (r * x) q| ≤ |x| := by
  have hprod : |r * x| ≤ (2 : ℤ) ^ q * |x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hr (abs_nonneg x)
  rcases abs_le.mp hprod with ⟨hlo, hhi⟩
  unfold roundShiftInt
  split_ifs with hq0
  · subst hq0
    simpa using hprod
  · set q' : ℕ := q - 1
    have hq_eq : (2 : ℤ) ^ q = 2 * (2 : ℤ) ^ q' := by
      have : q = q' + 1 := by omega
      rw [this, pow_succ']
    have h2q'_pos : (0 : ℤ) < (2 : ℤ) ^ q' := by positivity
    set a : ℤ := r * x + (2 : ℤ) ^ q'
    set b : ℤ := (2 : ℤ) ^ q
    have hb_pos : (0 : ℤ) < b := by positivity
    have hdiv : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
    have hmod0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb_pos)
    have hmod1 : a % b < b := Int.emod_lt_of_pos a hb_pos
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Single-pass $O(k)$ linear recurrence trajectory builder (`buildRecurrenceArray`):
computes the array `#[x_0, x_1, ..., x_k]` and final state `x_k`
in a single pass of $k$ step calls (`Array.push`). -/
def buildRecurrenceArray {α : Type*} (init : α) (step : ℕ → α → α) : (k : ℕ) → Array α × α
  | 0 => (#[init], init)
  | k + 1 =>
    let (arr, prev) := buildRecurrenceArray init step k
    let next := step k prev
    (arr.push next, next)

/-- The array returned by `buildRecurrenceArray init step k` has size `k + 1`. -/
theorem size_buildRecurrenceArray {α : Type*} (init : α) (step : ℕ → α → α) :
    ∀ k : ℕ, (buildRecurrenceArray init step k).1.size = k + 1
  | 0 => rfl
  | k + 1 => by
    simp only [buildRecurrenceArray, Array.size_push, size_buildRecurrenceArray init step k]

/-- Looking up index `s ≤ k` in `(buildRecurrenceArray init step k).1` returns the exact
state `(buildRecurrenceArray init step s).2` at step `s`. -/
theorem getD_buildRecurrenceArray {α : Type*} (init : α) (step : ℕ → α → α) :
    ∀ {k s : ℕ}, s ≤ k →
      (buildRecurrenceArray init step k).1.getD s init =
        (buildRecurrenceArray init step s).2
  | 0, s, hs => by
    have hs0 : s = 0 := Nat.eq_zero_of_le_zero hs
    subst hs0
    rfl
  | k + 1, s, hs => by
    rcases Nat.of_le_succ hs with hle | rfl
    · rw [buildRecurrenceArray, Array.getD_eq_getD_getElem?, Array.getElem?_push]
      have hsz : (buildRecurrenceArray init step k).1.size = k + 1 :=
        size_buildRecurrenceArray init step k
      have hne : s ≠ (buildRecurrenceArray init step k).1.size := by omega
      rw [if_neg hne, ← Array.getD_eq_getD_getElem?]
      exact getD_buildRecurrenceArray init step hle
    · rw [buildRecurrenceArray, Array.getD_eq_getD_getElem?, Array.getElem?_push]
      have hsz : k + 1 = (buildRecurrenceArray init step k).1.size :=
        (size_buildRecurrenceArray init step k).symm
      rw [if_pos hsz]
      rfl

/-- Congruence for `buildRecurrenceArray` along the actual recurrence trajectory: if `step1 s`
and `step2 s` agree at the actual state `(buildRecurrenceArray init step2 s).2` for all `s < k`,
then `buildRecurrenceArray init step1 k = buildRecurrenceArray init step2 k`. -/
theorem buildRecurrenceArray_congr {α : Type*} (init : α)
    (step1 step2 : ℕ → α → α) :
    ∀ (k : ℕ),
      (∀ s < k, step1 s (buildRecurrenceArray init step2 s).2 =
        step2 s (buildRecurrenceArray init step2 s).2) →
      buildRecurrenceArray init step1 k = buildRecurrenceArray init step2 k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := buildRecurrenceArray_congr init step1 step2 k
      (fun s hs => h s (Nat.lt_succ_of_lt hs))
    have hk := h k (Nat.lt_succ_self k)
    simp only [buildRecurrenceArray, ih, hk]

/-- Tabulates a finite-domain table `f : Fin N → α` into a contiguous `Array α` of size `N`
and looks up entries in $O(1)$ via `Array.getD`. -/
def memoizeFin {N : ℕ} {α : Type} [Inhabited α] (f : Fin N → α) : Fin N → α :=
  let arr : Array α := Array.ofFn f
  fun i => arr.getD i.val default

@[simp]
theorem memoizeFin_eq {N : ℕ} {α : Type} [Inhabited α] (f : Fin N → α) :
    memoizeFin f = f := by
  funext i
  unfold memoizeFin
  simp [Array.getD, Array.size_ofFn, i.isLt]

/-- Tabulates a 2D finite-domain table `f : Fin N → Fin M → α` into a 2D contiguous
`Array (Array α)` of dimension `N × M` and looks up entries in $O(1)$ via `Array.getD`. -/
def memoizeFin2 {N M : ℕ} {α : Type} [Inhabited α] (f : Fin N → Fin M → α) :
    Fin N → Fin M → α :=
  let rows : Array (Array α) := Array.ofFn (fun i : Fin N => Array.ofFn (f i))
  fun i j => (rows.getD i.val #[]).getD j.val default

@[simp]
theorem memoizeFin2_eq {N M : ℕ} {α : Type} [Inhabited α] (f : Fin N → Fin M → α) :
    memoizeFin2 f = f := by
  funext i j
  unfold memoizeFin2
  simp [Array.getD, Array.size_ofFn, i.isLt, j.isLt]

/-- Tabulates a finite prefix `0, ..., N - 1` of `f : ℕ → α` into a contiguous `Array α` of
size `N` and looks up entries for `k < N` in $O(1)$ via `Array` indexing. -/
def memoizeRange {α : Type} (N : ℕ) (f : ℕ → α) : ℕ → α :=
  let arr : Array α := Array.ofFn (fun i : Fin N => f i.val)
  fun k => if h : k < arr.size then arr[k] else f k

@[simp]
theorem memoizeRange_eq {α : Type} (N : ℕ) (f : ℕ → α) :
    memoizeRange N f = f := by
  funext k
  unfold memoizeRange
  split_ifs with h
  · simp
  · rfl

/-! ## 6. Operation-Tracking Cost Monad `CostM` & Tracked Primitives (Section 8 (`sec:lean`))

To tie the counted bit-operation recurrence directly to the executable functional pipeline,
`CostM α := α × ℕ` pairs every computed value `.1 : α` with the cumulative elementary bit-operation
count `.2 : ℕ` accrued while computing it. -/

/-- Lightweight writer/cost pair `(value, stepCount)` tracking elementary operations alongside the
computed result (Section 8 (`sec:lean`)). -/
abbrev CostM (α : Type*) := α × ℕ

/-- Explicit linear bit-width cost wrapper (`costLinearWordOp`):
every primitive operation on $w$-bit integers/words or bit slices (`add`, `sub`, `cmp`,
`condSubMux`, `shift`, `slice`, `encode`, `decode`) charges a cost linear in its declared bit-width
parameter $w$. -/
def costLinearWordOp (coeff w const : ℕ) : ℕ :=
  coeff * w + const

/-- Per-bit-step cost of a $w$-bit conditional add/subtract-and-shift register step in
`binaryShiftAddMulRegAux`, `binaryRestoringDivModRegAux`, and `binaryRestoringSqrtRegAux`
(`5 * w + 6` elementary bit operations per step, matching the uniform `FinTM2` step count
`5 * w + 3 ≤ 5 * w + 6`). -/
def bitStepRegCost (w : ℕ) : ℕ :=
  5 * w + 6

/-- Operation-tracking finite-domain table constructor: evaluates `f i : CostM α` once for each
`i : Fin N` when building the backing `Array`, returning the lookup function `Fin N → α` paired
with the total tabulation cost `(∑ i : Fin N, (f i).2) + N + 1`. -/
def memoizeFinTracked {N : ℕ} {α : Type} [Inhabited α] (f : Fin N → CostM α) :
    CostM (Fin N → α) :=
  let tbl := memoizeFin f
  (memoizeFin (fun i => (tbl i).1), (∑ i : Fin N, (tbl i).2) + N + 1)

@[simp]
theorem memoizeFinTracked_fst {N : ℕ} {α : Type} [Inhabited α] (f : Fin N → CostM α) :
    (memoizeFinTracked f).1 = fun i => (f i).1 := by
  simp [memoizeFinTracked]

@[simp]
theorem memoizeFinTracked_snd {N : ℕ} {α : Type} [Inhabited α] (f : Fin N → CostM α) :
    (memoizeFinTracked f).2 = (∑ i : Fin N, (f i).2) + N + 1 := by
  simp [memoizeFinTracked]

theorem memoizeFinTracked_snd_le {N : ℕ} {α : Type} [Inhabited α] (f : Fin N → CostM α)
    (B : ℕ) (hB : ∀ i : Fin N, (f i).2 ≤ B) :
    (memoizeFinTracked f).2 ≤ N * B + N + 1 := by
  rw [memoizeFinTracked_snd]
  have hsum : ∑ i : Fin N, (f i).2 ≤ ∑ _i : Fin N, B :=
    Finset.sum_le_sum (fun i _ => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- Operation-tracking 2D finite-domain table constructor: evaluates `f i j : CostM α` once for
each `(i, j) : Fin N × Fin M` when building the 2D `Array`, returning the lookup function
`Fin N → Fin M → α` paired with the total tabulation cost
`(∑ i : Fin N, ∑ j : Fin M, (f i j).2) + N * M + 1`. -/
def memoizeFin2Tracked {N M : ℕ} {α : Type} [Inhabited α] (f : Fin N → Fin M → CostM α) :
    CostM (Fin N → Fin M → α) :=
  let tbl := memoizeFin2 f
  (memoizeFin2 (fun i j => (tbl i j).1),
    (∑ i : Fin N, ∑ j : Fin M, (tbl i j).2) + N * M + 1)

@[simp]
theorem memoizeFin2Tracked_fst {N M : ℕ} {α : Type} [Inhabited α]
    (f : Fin N → Fin M → CostM α) :
    (memoizeFin2Tracked f).1 = fun i j => (f i j).1 := by
  simp [memoizeFin2Tracked]

@[simp]
theorem memoizeFin2Tracked_snd {N M : ℕ} {α : Type} [Inhabited α]
    (f : Fin N → Fin M → CostM α) :
    (memoizeFin2Tracked f).2 = (∑ i : Fin N, ∑ j : Fin M, (f i j).2) + N * M + 1 := by
  simp [memoizeFin2Tracked]

theorem memoizeFin2Tracked_snd_le {N M : ℕ} {α : Type} [Inhabited α]
    (f : Fin N → Fin M → CostM α) (B : ℕ) (hB : ∀ i : Fin N, ∀ j : Fin M, (f i j).2 ≤ B) :
    (memoizeFin2Tracked f).2 ≤ N * (M * B) + N * M + 1 := by
  rw [memoizeFin2Tracked_snd]
  have hsum : ∑ i : Fin N, ∑ j : Fin M, (f i j).2 ≤ ∑ _i : Fin N, ∑ _j : Fin M, B :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hB i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- Operation-tracking finite-prefix table constructor for `0, ..., N - 1`: evaluates `f k` once
for each `k < N` when building the backing `Array`, returning the lookup function `ℕ → α` paired
with the prefix tabulation cost `(∑ k ∈ Finset.range N, (f k).2) + N + 1`. -/
def memoizeRangeTracked {α : Type} (N : ℕ) (f : ℕ → CostM α) : CostM (ℕ → α) :=
  let tbl := memoizeRange N f
  (memoizeRange N (fun k => (tbl k).1),
    (∑ k ∈ Finset.range N, (tbl k).2) + N + 1)

@[simp]
theorem memoizeRangeTracked_fst {α : Type} (N : ℕ) (f : ℕ → CostM α) :
    (memoizeRangeTracked N f).1 = fun k => (f k).1 := by
  simp [memoizeRangeTracked]

@[simp]
theorem memoizeRangeTracked_snd {α : Type} (N : ℕ) (f : ℕ → CostM α) :
    (memoizeRangeTracked N f).2 = (∑ k ∈ Finset.range N, (f k).2) + N + 1 := by
  simp [memoizeRangeTracked]

theorem memoizeRangeTracked_snd_le {α : Type} (N : ℕ) (f : ℕ → CostM α)
    (B : ℕ) (hB : ∀ k < N, (f k).2 ≤ B) :
    (memoizeRangeTracked N f).2 ≤ N * B + N + 1 := by
  rw [memoizeRangeTracked_snd]
  have hsum : ∑ k ∈ Finset.range N, (f k).2 ≤ ∑ _k ∈ Finset.range N, B :=
    Finset.sum_le_sum (fun k hk => hB k (Finset.mem_range.mp hk))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  omega

/-- Operation-tracking prefix recurrence builder: executes `k` steps of `step s acc` starting from
`init`, accumulating both the `Array α` of prefix values and the step count of all `k` iterations. -/
def buildRecurrenceArrayTracked {α : Type*} (init : α) (step : ℕ → α → CostM α) :
    (k : ℕ) → CostM (Array α × α)
  | 0 => ((#[init], init), 2)
  | k + 1 =>
    let prev := buildRecurrenceArrayTracked init step k
    let next := step k prev.1.2
    ((prev.1.1.push next.1, next.1), prev.2 + next.2 + 2)

@[simp]
theorem buildRecurrenceArrayTracked_fst {α : Type*} (init : α) (step : ℕ → α → CostM α) :
    ∀ k : ℕ,
      (buildRecurrenceArrayTracked init step k).1 =
        buildRecurrenceArray init (fun s a => (step s a).1) k
  | 0 => rfl
  | k + 1 => by
    simp [buildRecurrenceArrayTracked, buildRecurrenceArray,
      buildRecurrenceArrayTracked_fst init step k]

theorem buildRecurrenceArrayTracked_snd_le {α : Type*} (init : α) (step : ℕ → α → CostM α)
    (B : ℕ) :
    ∀ (k : ℕ), (∀ s < k, ∀ a : α, (step s a).2 ≤ B) →
      (buildRecurrenceArrayTracked init step k).2 ≤ k * (B + 2) + 2
  | 0, _ => by simp [buildRecurrenceArrayTracked]
  | k + 1, hB => by
    simp only [buildRecurrenceArrayTracked]
    have ih := buildRecurrenceArrayTracked_snd_le init step B k
      (fun s hs a => hB s (Nat.lt_succ_of_lt hs) a)
    have hstep := hB k (Nat.lt_succ_self k) (buildRecurrenceArrayTracked init step k).1.2
    calc (buildRecurrenceArrayTracked init step k).2 +
          (step k (buildRecurrenceArrayTracked init step k).1.2).2 + 2
      _ ≤ (k * (B + 2) + 2) + B + 2 := by omega
      _ = (k + 1) * (B + 2) + 2 := by ring

/-- Operation-tracking dyadic rounded right-shift `roundShiftInt m s`: returns `roundShiftInt m s`
and charges `s + 2` elementary bit-shift steps. -/
def roundShiftIntTracked (m : ℤ) (s : ℕ) : CostM ℤ :=
  (roundShiftInt m s, s + 2)

@[simp]
theorem roundShiftIntTracked_fst (m : ℤ) (s : ℕ) :
    (roundShiftIntTracked m s).1 = roundShiftInt m s := rfl

@[simp]
theorem roundShiftIntTracked_snd (m : ℤ) (s : ℕ) :
    (roundShiftIntTracked m s).2 = s + 2 := rfl

/-- Auxiliary bit-by-bit restoring binary division loop over `k` bit steps of a `w`-bit register
(`binaryRestoringDivModRegAux`):
at each bit step, shifts the running remainder left by 1 bit (`2 * r' + a % 2`), performs a
`w`-bit trial comparison/subtraction `b ≤ r_dbl`, and selects `r_dbl - b` vs `r_dbl`, charging
`bitStepRegCost w = 5 * w + 6` elementary bit operations per step (`k * (5 * w + 6)` total), without
calling Lean's built-in multi-bit `/` or `%`. -/
def binaryRestoringDivModRegAux (w : ℕ) : ℕ → ℕ → ℕ → CostM (ℕ × ℕ)
  | 0, _, _ => ((0, 0), 0)
  | k + 1, a, b =>
    let prev := binaryRestoringDivModRegAux w k (a / 2) b
    if b = 0 then
      ((0, a), prev.2 + bitStepRegCost w)
    else
      let q' := prev.1.1
      let r' := prev.1.2
      let r_dbl := 2 * r' + a % 2
      let q := if b ≤ r_dbl then 2 * q' + 1 else 2 * q'
      let r := if b ≤ r_dbl then r_dbl - b else r_dbl
      ((q, r), prev.2 + bitStepRegCost w)

/-- Bit-by-bit restoring binary division over a `w`-bit register (`binaryRestoringDivModRegTracked`):
runs `w` bit steps of `binaryRestoringDivModRegAux w`, charging `5 * w + 6` elementary bit
operations per step (`w * (5 * w + 6)` total, i.e., $\Theta(w^2)$ bit operations). -/
def binaryRestoringDivModRegTracked (w a b : ℕ) : CostM (ℕ × ℕ) :=
  binaryRestoringDivModRegAux w w a b

theorem binaryRestoringDivModRegAux_fst (w : ℕ) :
    ∀ {k a : ℕ} (b : ℕ), a < 2 ^ k →
      (binaryRestoringDivModRegAux w k a b).1 = (a / b, a % b)
  | 0, a, b, ha => by
    have ha0 : a = 0 := by omega
    subst ha0
    simp [binaryRestoringDivModRegAux]
  | k + 1, a, b, ha => by
    have ha2 : a / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at ha
      omega
    simp only [binaryRestoringDivModRegAux, binaryRestoringDivModRegAux_fst w b ha2]
    by_cases hb : b = 0
    · subst hb; simp
    · rw [if_neg hb]
      have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
      have hr' : (a / 2) % b < b := Nat.mod_lt (a / 2) hb_pos
      have hmod2 : a % 2 < 2 := Nat.mod_lt a (by decide)
      have ha_decomp : (2 * ((a / 2) % b) + a % 2) + b * (2 * ((a / 2) / b)) = a := by
        have hdiv2 : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
        have hdivb : a / 2 = b * ((a / 2) / b) + (a / 2) % b := (Nat.div_add_mod (a / 2) b).symm
        linarith
      by_cases hcmp : b ≤ 2 * ((a / 2) % b) + a % 2
      · simp only [if_pos hcmp]
        have hr_lt : 2 * ((a / 2) % b) + a % 2 - b < b := by omega
        have heq : (2 * ((a / 2) % b) + a % 2 - b) + b * (2 * ((a / 2) / b) + 1) = a := by
          have : b * (2 * ((a / 2) / b) + 1) = b * (2 * ((a / 2) / b)) + b := by ring
          omega
        rcases (Nat.div_mod_unique hb_pos).mpr ⟨heq, hr_lt⟩ with ⟨hq, hr⟩
        exact Prod.ext hq.symm hr.symm
      · simp only [if_neg hcmp]
        have hr_lt : 2 * ((a / 2) % b) + a % 2 < b := by omega
        rcases (Nat.div_mod_unique hb_pos).mpr ⟨ha_decomp, hr_lt⟩ with ⟨hq, hr⟩
        exact Prod.ext hq.symm hr.symm

theorem binaryRestoringDivModRegTracked_fst {w a : ℕ} (b : ℕ) (ha : a < 2 ^ w) :
    (binaryRestoringDivModRegTracked w a b).1 = (a / b, a % b) :=
  binaryRestoringDivModRegAux_fst w b ha

theorem binaryRestoringDivModRegAux_snd_le (w : ℕ) :
    ∀ (k a b : ℕ), (binaryRestoringDivModRegAux w k a b).2 ≤ k * (5 * w + 6)
  | 0, _, _ => by simp [binaryRestoringDivModRegAux]
  | k + 1, a, b => by
    simp only [binaryRestoringDivModRegAux, bitStepRegCost]
    have ih := binaryRestoringDivModRegAux_snd_le w k (a / 2) b
    split_ifs <;> nlinarith

theorem binaryRestoringDivModRegTracked_snd_le (w a b : ℕ) :
    (binaryRestoringDivModRegTracked w a b).2 ≤ 5 * w * w + 6 * w := by
  have h := binaryRestoringDivModRegAux_snd_le w w a b
  unfold binaryRestoringDivModRegTracked
  nlinarith

/-- Signed Euclidean division by a positive natural number `b > 0` computed directly from the
quotient and remainder `(qr.1.1, qr.1.2)` of `binaryRestoringDivModRegTracked`, without
calling Lean's built-in integer `/`. -/
def edivPosByRestoringTracked (w : ℕ) (a : ℤ) (b : ℕ) : CostM ℤ :=
  if 0 ≤ a then
    let qr := binaryRestoringDivModRegTracked w a.natAbs b
    ((qr.1.1 : ℤ), qr.2 + 1)
  else
    let qr := binaryRestoringDivModRegTracked w (-a).natAbs b
    (if qr.1.2 = 0 then -(qr.1.1 : ℤ) else -(qr.1.1 : ℤ) - 1, qr.2 + 1)

theorem edivPosByRestoringTracked_fst {w : ℕ} {a : ℤ} {b : ℕ}
    (ha : a.natAbs < 2 ^ w) (hb : 0 < b) :
    (edivPosByRestoringTracked w a b).1 = a / (b : ℤ) := by
  unfold edivPosByRestoringTracked
  have hb_z : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hdiv_z : (b : ℤ) * (a / (b : ℤ)) + a % (b : ℤ) = a := Int.mul_ediv_add_emod a (b : ℤ)
  have hmod0 : 0 ≤ a % (b : ℤ) := Int.emod_nonneg a (ne_of_gt hb_z)
  have hmod1 : a % (b : ℤ) < (b : ℤ) := Int.emod_lt_of_pos a hb_z
  split_ifs with hsign
  · dsimp only
    rw [binaryRestoringDivModRegTracked_fst b ha]
    set m : ℕ := a.natAbs
    have hm_eq : (m : ℤ) = a := Int.natAbs_of_nonneg hsign
    have hdiv_n : b * (m / b) + m % b = m := Nat.div_add_mod m b
    have hmod_n : m % b < b := Nat.mod_lt m hb
    have hdiv_nz : (b : ℤ) * ((m / b : ℕ) : ℤ) + ((m % b : ℕ) : ℤ) = a := by
      rw [← hm_eq]; exact_mod_cast hdiv_n
    have hmod_nz : ((m % b : ℕ) : ℤ) < (b : ℤ) := by exact_mod_cast hmod_n
    have hmod_nn : (0 : ℤ) ≤ ((m % b : ℕ) : ℤ) := by positivity
    nlinarith
  · dsimp only
    have ha_neg : (-a).natAbs < 2 ^ w := by simpa using ha
    rw [binaryRestoringDivModRegTracked_fst b ha_neg]
    set m : ℕ := (-a).natAbs
    have hm_eq : (m : ℤ) = -a := Int.natAbs_of_nonneg (by omega)
    have hdiv_n : b * (m / b) + m % b = m := Nat.div_add_mod m b
    have hmod_n : m % b < b := Nat.mod_lt m hb
    have hdiv_nz : (b : ℤ) * ((m / b : ℕ) : ℤ) + ((m % b : ℕ) : ℤ) = -a := by
      rw [← hm_eq]; exact_mod_cast hdiv_n
    have hmod_nz : ((m % b : ℕ) : ℤ) < (b : ℤ) := by exact_mod_cast hmod_n
    split_ifs with hrem0
    · have hrem_z : ((m % b : ℕ) : ℤ) = 0 := by exact_mod_cast hrem0
      nlinarith
    · have hrem_pos : (0 : ℤ) < ((m % b : ℕ) : ℤ) := by
        exact_mod_cast Nat.pos_of_ne_zero hrem0
      nlinarith

theorem edivPosByRestoringTracked_snd_le (w : ℕ) (a : ℤ) (b : ℕ) :
    (edivPosByRestoringTracked w a b).2 ≤ 5 * w * w + 6 * w + 1 := by
  unfold edivPosByRestoringTracked
  split_ifs
  · dsimp only
    have h := binaryRestoringDivModRegTracked_snd_le w a.natAbs b
    omega
  · dsimp only
    have h := binaryRestoringDivModRegTracked_snd_le w (-a).natAbs b
    omega

/-- Operation-tracking rounded integer division `roundDivIntTracked w num den`: computes
`roundDivInt num den` directly from `(w + 1)`-bit restoring binary division of `2 * num` by `|den|`
followed by a 1-bit rounded shift `roundShiftInt dStep.1 1`, charging the bit-by-bit
restoring division cost. -/
def roundDivIntTracked (w : ℕ) (num den : ℤ) : CostM ℤ :=
  if 0 < den then
    let dStep := edivPosByRestoringTracked (w + 1) (2 * num) den.natAbs
    (roundShiftInt dStep.1 1, dStep.2 + 4 * w + 1)
  else if den < 0 then
    let dStep := edivPosByRestoringTracked (w + 1) (-2 * num) (-den).natAbs
    (roundShiftInt dStep.1 1, dStep.2 + 4 * w + 1)
  else
    (0, 2)

private theorem roundShiftInt_ediv_two_mul_eq (num d : ℤ) (hd : 0 < d) :
    roundShiftInt ((2 * num) / d) 1 = (2 * num + d) / (2 * d) := by
  change ((2 * num) / d + 1) / 2 = (2 * num + d) / (2 * d)
  set q : ℤ := (2 * num + d) / (2 * d)
  set r : ℤ := (2 * num + d) % (2 * d)
  have h2d_pos : (0 : ℤ) < 2 * d := by omega
  have hdiv1 : (2 * d) * q + r = 2 * num + d := Int.mul_ediv_add_emod (2 * num + d) (2 * d)
  have hr0 : 0 ≤ r := Int.emod_nonneg (2 * num + d) (ne_of_gt h2d_pos)
  have hr1 : r < 2 * d := Int.emod_lt_of_pos (2 * num + d) h2d_pos
  set q1 : ℤ := (2 * num) / d
  set r1 : ℤ := (2 * num) % d
  have hdiv2 : d * q1 + r1 = 2 * num := Int.mul_ediv_add_emod (2 * num) d
  have hr1_0 : 0 ≤ r1 := Int.emod_nonneg (2 * num) (ne_of_gt hd)
  have hr1_1 : r1 < d := Int.emod_lt_of_pos (2 * num) hd
  have hq1_bounds : 2 * q - 1 ≤ q1 ∧ q1 ≤ 2 * q := by
    constructor <;> nlinarith
  set q2 : ℤ := (q1 + 1) / 2
  set r2 : ℤ := (q1 + 1) % 2
  have hdiv3 : 2 * q2 + r2 = q1 + 1 := Int.mul_ediv_add_emod (q1 + 1) 2
  have hr2_0 : 0 ≤ r2 := Int.emod_nonneg (q1 + 1) (by decide)
  have hr2_1 : r2 < 2 := Int.emod_lt_of_pos (q1 + 1) (by decide)
  omega

theorem roundDivIntTracked_fst {w : ℕ} {num : ℤ} (den : ℤ)
    (hnum : FitsSignedWord w num) :
    (roundDivIntTracked w num den).1 = roundDivInt num den := by
  unfold roundDivIntTracked roundDivInt
  have hnum_nat : num.natAbs < 2 ^ w := (fitsSignedWord_iff_natAbs_lt w num).mp hnum
  have h2num_pos : (2 * num).natAbs < 2 ^ (w + 1) := by
    rw [Int.natAbs_mul, Nat.pow_succ']
    simpa using Nat.mul_lt_mul_of_pos_left hnum_nat (by decide : 0 < 2)
  have h2num_neg : (-2 * num).natAbs < 2 ^ (w + 1) := by
    have : (-2 * num).natAbs = (2 * num).natAbs := by
      rw [show -2 * num = -(2 * num) by ring, Int.natAbs_neg]
    rw [this]
    exact h2num_pos
  split_ifs with h1 h2
  · dsimp only
    have hb_pos : 0 < den.natAbs := Int.natAbs_pos.mpr (ne_of_gt h1)
    have hb_eq : (den.natAbs : ℤ) = den := Int.natAbs_of_nonneg (le_of_lt h1)
    rw [edivPosByRestoringTracked_fst h2num_pos hb_pos, hb_eq]
    exact roundShiftInt_ediv_two_mul_eq num den h1
  · dsimp only
    have hb_pos : 0 < (-den).natAbs := Int.natAbs_pos.mpr (by omega)
    have hb_eq : ((-den).natAbs : ℤ) = -den := Int.natAbs_of_nonneg (by omega)
    rw [edivPosByRestoringTracked_fst h2num_neg hb_pos, hb_eq]
    have h := roundShiftInt_ediv_two_mul_eq (-num) (-den) (by omega)
    simpa [ show 2 * -num = -2 * num by ring,
            show -2 * num + -den = -2 * num - den by ring,
            show 2 * -den = -2 * den by ring, sub_eq_add_neg ] using h
  · rfl

theorem roundDivIntTracked_snd_le (w : ℕ) (num den : ℤ) :
    (roundDivIntTracked w num den).2 ≤ 5 * w * w + 20 * w + 13 := by
  unfold roundDivIntTracked
  split_ifs
  · dsimp only
    have hdiv := edivPosByRestoringTracked_snd_le (w + 1) (2 * num) den.natAbs
    nlinarith
  · dsimp only
    have hdiv := edivPosByRestoringTracked_snd_le (w + 1) (-2 * num) (-den).natAbs
    nlinarith
  · omega

/-- Auxiliary bit-by-bit restoring binary integer square root loop over `k` 2-bit steps of a `w`-bit
register (`binaryRestoringSqrtRegAux`):
at each step, shifts the running remainder by 2 bits, performs a `w`-bit trial comparison/subtraction
`cand ≤ r_quad`, and charges `bitStepRegCost w = 5 * w + 6` elementary bit operations per step,
without calling Lean's built-in `Nat.sqrt` or `*`. -/
def binaryRestoringSqrtRegAux (w : ℕ) : ℕ → ℕ → CostM (ℕ × ℕ)
  | 0, _ => ((0, 0), 2)
  | k + 1, m =>
    let prev := binaryRestoringSqrtRegAux w k (m / 4)
    let s' := prev.1.1
    let r' := prev.1.2
    let r_quad := (r' + r') + (r' + r') + m % 4
    let cand := (s' + s') + (s' + s') + 1
    let s := if cand ≤ r_quad then (s' + s') + 1 else s' + s'
    let r := if cand ≤ r_quad then r_quad - cand else r_quad
    ((s, r), prev.2 + bitStepRegCost w)

/-- Bit-by-bit restoring binary integer square root over `w` 2-bit steps
(`binaryRestoringSqrtRegTracked`): charges `w * (5 * w + 6) + 2` elementary bit operations ($\Theta(w^2)$). -/
def binaryRestoringSqrtRegTracked (w m : ℕ) : CostM (ℕ × ℕ) :=
  binaryRestoringSqrtRegAux w w m

theorem binaryRestoringSqrtRegAux_spec (w : ℕ) :
    ∀ {k m : ℕ}, m < 4 ^ k →
      (binaryRestoringSqrtRegAux w k m).1.1 * (binaryRestoringSqrtRegAux w k m).1.1 +
        (binaryRestoringSqrtRegAux w k m).1.2 = m ∧
      (binaryRestoringSqrtRegAux w k m).1.2 ≤ 2 * (binaryRestoringSqrtRegAux w k m).1.1
  | 0, m, hm => by
    have hm0 : m = 0 := by omega
    subst hm0
    simp [binaryRestoringSqrtRegAux]
  | k + 1, m, hm => by
    have hm4 : m / 4 < 4 ^ k := by
      rw [Nat.pow_succ] at hm
      omega
    simp only [binaryRestoringSqrtRegAux]
    rcases binaryRestoringSqrtRegAux_spec w hm4 with ⟨hsq', hrem'⟩
    set s' := (binaryRestoringSqrtRegAux w k (m / 4)).1.1
    set r' := (binaryRestoringSqrtRegAux w k (m / 4)).1.2
    have hmod4 : m % 4 < 4 := Nat.mod_lt m (by decide)
    have hdiv4 : 4 * (m / 4) + m % 4 = m := Nat.div_add_mod m 4
    by_cases hcmp : (s' + s') + (s' + s') + 1 ≤ (r' + r') + (r' + r') + m % 4
    · simp only [if_pos hcmp]
      have hexp : (s' + s' + 1) * (s' + s' + 1) =
          4 * (s' * s') + ((s' + s') + (s' + s') + 1) := by ring
      constructor <;> omega
    · simp only [if_neg hcmp]
      have hexp : (s' + s') * (s' + s') = 4 * (s' * s') := by ring
      constructor <;> omega

theorem binaryRestoringSqrtRegTracked_spec {w m : ℕ} (hm : m < 4 ^ w) :
    (binaryRestoringSqrtRegTracked w m).1.1 * (binaryRestoringSqrtRegTracked w m).1.1 +
      (binaryRestoringSqrtRegTracked w m).1.2 = m ∧
    (binaryRestoringSqrtRegTracked w m).1.2 ≤ 2 * (binaryRestoringSqrtRegTracked w m).1.1 :=
  binaryRestoringSqrtRegAux_spec w hm

theorem binaryRestoringSqrtRegTracked_fst_fst {w m : ℕ} (hm : m < 4 ^ w) :
    (binaryRestoringSqrtRegTracked w m).1.1 = m.sqrt := by
  rcases binaryRestoringSqrtRegTracked_spec hm with ⟨hsq, hrem⟩
  have h1 : m.sqrt * m.sqrt ≤ m := Nat.sqrt_le m
  have h2 : m < (m.sqrt + 1) * (m.sqrt + 1) := Nat.lt_succ_sqrt m
  nlinarith

theorem binaryRestoringSqrtRegAux_snd_le (w : ℕ) :
    ∀ (k m : ℕ), (binaryRestoringSqrtRegAux w k m).2 ≤ k * (5 * w + 6) + 2
  | 0, _ => by simp [binaryRestoringSqrtRegAux]
  | k + 1, m => by
    simp only [binaryRestoringSqrtRegAux, bitStepRegCost]
    have ih := binaryRestoringSqrtRegAux_snd_le w k (m / 4)
    nlinarith

theorem binaryRestoringSqrtRegTracked_snd_le (w m : ℕ) :
    (binaryRestoringSqrtRegTracked w m).2 ≤ 5 * w * w + 6 * w + 2 := by
  have h := binaryRestoringSqrtRegAux_snd_le w w m
  unfold binaryRestoringSqrtRegTracked
  nlinarith

namespace FixedComplex

/-- Operation-tracking fixed-point complex addition at precision `q`. -/
def addTracked {q : ℕ} (z w : FixedComplex q) : CostM (FixedComplex q) :=
  (z.add w, 2 * q + 4)

@[simp]
theorem addTracked_fst {q : ℕ} (z w : FixedComplex q) :
    (addTracked z w).1 = z.add w := rfl

@[simp]
theorem addTracked_snd {q : ℕ} (z w : FixedComplex q) :
    (addTracked z w).2 = 2 * q + 4 := rfl

/-- Operation-tracking fixed-point complex subtraction at precision `q`. -/
def subTracked {q : ℕ} (z w : FixedComplex q) : CostM (FixedComplex q) :=
  (z.sub w, 2 * q + 4)

@[simp]
theorem subTracked_fst {q : ℕ} (z w : FixedComplex q) :
    (subTracked z w).1 = z.sub w := rfl

@[simp]
theorem subTracked_snd {q : ℕ} (z w : FixedComplex q) :
    (subTracked z w).2 = 2 * q + 4 := rfl

/-- Operation-tracking fixed-point complex conjugation at precision `q`. -/
def conjTracked {q : ℕ} (z : FixedComplex q) : CostM (FixedComplex q) :=
  (z.conj, q + 2)

@[simp]
theorem conjTracked_fst {q : ℕ} (z : FixedComplex q) :
    (conjTracked z).1 = z.conj := rfl

@[simp]
theorem conjTracked_snd {q : ℕ} (z : FixedComplex q) :
    (conjTracked z).2 = q + 2 := rfl

/-- Operation-tracking division by 2 with round-half-up in `FixedComplex q`. -/
def halfRoundedTracked {q : ℕ} (z : FixedComplex q) : CostM (FixedComplex q) :=
  (halfRounded z, 2 * q + 4)

@[simp]
theorem halfRoundedTracked_fst {q : ℕ} (z : FixedComplex q) :
    (halfRoundedTracked z).1 = halfRounded z := rfl

@[simp]
theorem halfRoundedTracked_snd {q : ℕ} (z : FixedComplex q) :
    (halfRoundedTracked z).2 = 2 * q + 4 := rfl

/-- Operation-tracking precision rescaling from `FixedComplex q1` to `FixedComplex q2`. -/
def rescaleTracked {q1 : ℕ} (q2 : ℕ) (z : FixedComplex q1) : CostM (FixedComplex q2) :=
  (rescale q2 z, 2 * (q1 + q2) + 4)

@[simp]
theorem rescaleTracked_fst {q1 : ℕ} (q2 : ℕ) (z : FixedComplex q1) :
    (rescaleTracked q2 z).1 = rescale q2 z := rfl

@[simp]
theorem rescaleTracked_snd {q1 : ℕ} (q2 : ℕ) (z : FixedComplex q1) :
    (rescaleTracked q2 z).2 = 2 * (q1 + q2) + 4 := rfl

end FixedComplex

/-- Explicit bit-by-bit binary shift-and-add natural-number multiplication (`binaryShiftAddMul`,
Section 8 (`sec:lean`)).
Computes $A \cdot B$ using only single-bit parity tests (`A % 2 = 1`), single-bit right shifts
(`A / 2`), and additions (`P + P`, `+ B`), without calling Lean's built-in `(· * ·)`. -/
def binaryShiftAddMul (A B : ℕ) : ℕ :=
  if h : A = 0 then
    0
  else
    have : A / 2 < A := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    let P := binaryShiftAddMul (A / 2) B
    (P + P) + (if A % 2 = 1 then B else 0)
termination_by A

/-- Exactness of `binaryShiftAddMul` (`binaryShiftAddMul_eq_mul`). -/
@[simp]
theorem binaryShiftAddMul_eq_mul (A : ℕ) : ∀ B : ℕ, binaryShiftAddMul A B = A * B := by
  induction A using Nat.strongRecOn with
  | ind A ih =>
    intro B
    rw [binaryShiftAddMul]
    by_cases h : A = 0
    · simp [h]
    · rw [dif_neg h]
      dsimp only
      have hdiv : A / 2 < A := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      rw [ih (A / 2) hdiv B]
      have hmod : A % 2 = 0 ∨ A % 2 = 1 := Nat.mod_two_eq_zero_or_one A
      have hdecomp : 2 * (A / 2) + A % 2 = A := Nat.div_add_mod A 2
      rcases hmod with h0 | h1
      · rw [if_neg (by omega), add_zero]
        nlinarith
      · rw [if_pos h1]
        nlinarith

/-- Exact bit-width $\lfloor \log_2 \max(a, b) \rfloor + 1$ of a sub-multiplication operand pair
$(a, b)$. -/
def operandBitWidth (a b : ℕ) : ℕ :=
  Nat.log 2 (max a b) + 1

lemma lt_two_pow_operandBitWidth_left (a b : ℕ) : a < 2 ^ operandBitWidth a b := by
  unfold operandBitWidth
  exact lt_of_le_of_lt (le_max_left a b) (Nat.lt_pow_succ_log_self (by decide) (max a b))

lemma lt_two_pow_operandBitWidth_right (a b : ℕ) : b < 2 ^ operandBitWidth a b := by
  unfold operandBitWidth
  exact lt_of_le_of_lt (le_max_right a b) (Nat.lt_pow_succ_log_self (by decide) (max a b))

/-- Operation-tracking range summation `∑ m ∈ Finset.range N, f m`, accumulating each term's
computation cost `.2` plus `(w + 2)` addition steps per term recursively. -/
def sumRangeTracked (w : ℕ) : ℕ → (ℕ → CostM ℤ) → CostM ℤ
  | 0, _ => (0, 2)
  | m + 1, f =>
    let prev := sumRangeTracked w m f
    let term := f m
    (prev.1 + term.1, prev.2 + term.2 + w + 2)

@[simp]
theorem sumRangeTracked_fst (w : ℕ) :
    ∀ (N : ℕ) (f : ℕ → CostM ℤ),
      (sumRangeTracked w N f).1 = ∑ m ∈ Finset.range N, (f m).1
  | 0, _ => by simp [sumRangeTracked]
  | m + 1, f => by
    simp [sumRangeTracked, sumRangeTracked_fst w m f, Finset.sum_range_succ]

theorem sumRangeTracked_snd_le (w : ℕ) :
    ∀ (N : ℕ) (f : ℕ → CostM ℤ) (c : ℕ),
      (∀ m < N, (f m).2 ≤ c) →
      (sumRangeTracked w N f).2 ≤ N * (c + w + 2) + 2
  | 0, _, _, _ => by simp [sumRangeTracked]
  | m + 1, f, c, hc => by
    simp only [sumRangeTracked]
    have h1 := sumRangeTracked_snd_le w m f c (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have h2 := hc m (Nat.lt_succ_self m)
    linarith

/-- Operation-tracking finite-domain summation `∑ i : Fin N, f i`, accumulating each term's
computation cost `.2` plus `(w + 2)` addition steps per term recursively. -/
def sumFinIntTracked (w : ℕ) : {N : ℕ} → (Fin N → CostM ℤ) → CostM ℤ
  | 0, _ => (0, 2)
  | m + 1, f =>
    let prev := sumFinIntTracked w (fun i : Fin m => f i.castSucc)
    let last := f (Fin.last m)
    (prev.1 + last.1, prev.2 + last.2 + w + 2)

@[simp]
theorem sumFinIntTracked_fst (w : ℕ) :
    ∀ {N : ℕ} (f : Fin N → CostM ℤ),
      (sumFinIntTracked w f).1 = ∑ i : Fin N, (f i).1
  | 0, _ => by simp [sumFinIntTracked]
  | m + 1, f => by
    simp [sumFinIntTracked, sumFinIntTracked_fst w (fun i : Fin m => f i.castSucc),
      Fin.sum_univ_castSucc]

theorem sumFinIntTracked_snd_le (w : ℕ) :
    ∀ {N : ℕ} (f : Fin N → CostM ℤ) (c : ℕ),
      (∀ i : Fin N, (f i).2 ≤ c) →
      (sumFinIntTracked w f).2 ≤ N * (c + w + 2) + 2
  | 0, _, _, _ => by simp [sumFinIntTracked]
  | m + 1, f, c, hc => by
    simp only [sumFinIntTracked]
    have h1 := sumFinIntTracked_snd_le w (fun i : Fin m => f i.castSucc) c (fun i => hc i.castSucc)
    have h2 := hc (Fin.last m)
    linarith

theorem fitsSignedWord_sum_range {w b : ℕ} (N : ℕ) (hN : N ≤ 2 ^ b) (f : ℕ → ℤ)
    (hf : ∀ m < N, FitsSignedWord w (f m)) :
    FitsSignedWord (w + b) (∑ m ∈ Finset.range N, f m) := by
  unfold FitsSignedWord
  by_cases hN0 : N = 0
  · subst hN0; simp
  · have hterm : ∀ m ∈ Finset.range N, |f m| ≤ (2 : ℤ) ^ w - 1 := by
      intro m hm
      have h : |f m| < (2 : ℤ) ^ w := hf m (Finset.mem_range.mp hm)
      omega
    have hsum : |∑ m ∈ Finset.range N, f m| ≤ ∑ m ∈ Finset.range N, |f m| :=
      Finset.abs_sum_le_sum_abs _ _
    have hle : ∑ m ∈ Finset.range N, |f m| ≤ (N : ℤ) * ((2 : ℤ) ^ w - 1) := by
      calc ∑ m ∈ Finset.range N, |f m|
          ≤ ∑ _m ∈ Finset.range N, ((2 : ℤ) ^ w - 1) := Finset.sum_le_sum hterm
        _ = (N : ℤ) * ((2 : ℤ) ^ w - 1) := by simp; ring
    have hNb : (N : ℤ) ≤ (2 : ℤ) ^ b := by exact_mod_cast hN
    have hpos : (0 : ℤ) < (2 : ℤ) ^ w := by positivity
    have hposN : (0 : ℤ) < (N : ℤ) := by positivity
    have hlt : (N : ℤ) * ((2 : ℤ) ^ w - 1) < (2 : ℤ) ^ (w + b) := by
      rw [pow_add, mul_comm ((2 : ℤ) ^ w)]
      nlinarith
    omega

theorem fitsSignedWord_sum_fin {w b N : ℕ} (hN : N ≤ 2 ^ b) (f : Fin N → ℤ)
    (hf : ∀ i : Fin N, FitsSignedWord w (f i)) :
    FitsSignedWord (w + b) (∑ i : Fin N, f i) := by
  have heq : (∑ i : Fin N, f i) = ∑ m ∈ Finset.range N, (if h : m < N then f ⟨m, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => if h : m < N then f ⟨m, h⟩ else 0) N]
    exact Finset.sum_congr rfl (fun i _ => by simp [i.isLt])
  rw [heq]
  exact fitsSignedWord_sum_range N hN _ (fun m hm => by simp [hm, hf ⟨m, hm⟩])

/-- Auxiliary bit-by-bit binary shift-and-add loop over `k` bit steps of a `w`-bit register:
charges `5 * w + 6` elementary register steps per bit iteration without calling Lean's
built-in `(· * ·)`. -/
def binaryShiftAddMulRegAux (w : ℕ) : ℕ → ℕ → ℕ → CostM ℕ
  | 0, _, _ => (0, 0)
  | k + 1, A, B =>
    let prev := binaryShiftAddMulRegAux w k (A / 2) B
    let term : ℕ := if A % 2 = 1 then B else 0
    ((prev.1 + prev.1) + term, prev.2 + (5 * w + 6))

theorem binaryShiftAddMulRegAux_fst (w : ℕ) :
    ∀ {k A : ℕ} (B : ℕ), A < 2 ^ k → (binaryShiftAddMulRegAux w k A B).1 = A * B
  | 0, A, B, hA => by
    have hA0 : A = 0 := by omega
    simp [binaryShiftAddMulRegAux, hA0]
  | k + 1, A, B, hA => by
    have hdiv : A / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_succ]
      exact hA
    simp only [binaryShiftAddMulRegAux, binaryShiftAddMulRegAux_fst w B hdiv]
    have hmod : A % 2 = 0 ∨ A % 2 = 1 := Nat.mod_two_eq_zero_or_one A
    have hdecomp : 2 * (A / 2) + A % 2 = A := Nat.div_add_mod A 2
    rcases hmod with h0 | h1
    · rw [if_neg (by omega), add_zero]
      nlinarith
    · rw [if_pos h1]
      nlinarith

@[simp]
theorem binaryShiftAddMulRegAux_snd (w : ℕ) :
    ∀ (k A B : ℕ), (binaryShiftAddMulRegAux w k A B).2 = k * (5 * w + 6)
  | 0, _, _ => by simp [binaryShiftAddMulRegAux]
  | k + 1, A, B => by
    simp only [binaryShiftAddMulRegAux, binaryShiftAddMulRegAux_snd w k (A / 2) B]
    ring

/-- Operation-tracking `w`-bit binary shift-and-add multiplication (`binaryShiftAddMulRegTracked`). -/
def binaryShiftAddMulRegTracked (w A B : ℕ) : CostM ℕ :=
  binaryShiftAddMulRegAux w w A B

theorem binaryShiftAddMulRegTracked_fst {w A : ℕ} (B : ℕ) (hA : A < 2 ^ w) :
    (binaryShiftAddMulRegTracked w A B).1 = A * B :=
  binaryShiftAddMulRegAux_fst w B hA

@[simp]
theorem binaryShiftAddMulRegTracked_snd (w A B : ℕ) :
    (binaryShiftAddMulRegTracked w A B).2 = w * (5 * w + 6) :=
  binaryShiftAddMulRegAux_snd w w A B

/-- Single-pass $O(R \cdot b)$ chunk extraction from a natural number `x : ℕ`:
slices `x` into `R` base-$2^b$ chunks by taking `x % 2 ^ b` and shifting right by $b$ bits (`x / 2 ^ b`)
at each step, avoiding repeated $\Theta(R \cdot n)$-bit shifts `x / 2 ^ (i * b)`. -/
def extractNatChunks (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | R + 1, x => (x % 2 ^ b) :: extractNatChunks b R (x / 2 ^ b)

@[simp]
lemma length_extractNatChunks (b R x : ℕ) : (extractNatChunks b R x).length = R := by
  induction R generalizing x with
  | zero => rfl
  | succ R ih => simp [extractNatChunks, ih]

lemma getElem_extractNatChunks (b : ℕ) :
    ∀ (R x i : ℕ) (hi : i < (extractNatChunks b R x).length),
      (extractNatChunks b R x)[i] = natChunk b x i
  | 0, _, i, hi => by simp [extractNatChunks] at hi
  | R + 1, x, 0, _ => by simp [extractNatChunks, natChunk]
  | R + 1, x, i + 1, hi => by
      simp only [extractNatChunks, List.getElem_cons_succ]
      rw [getElem_extractNatChunks b R (x / 2 ^ b) i]
      unfold natChunk
      rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- Array-memoized single-pass base-$2^b$ chunk lookup for `x : ℕ`. -/
def natChunkFn (b R x : ℕ) : Fin R → ℕ :=
  let arr := (extractNatChunks b R x).toArray
  fun i => arr.getD i.val 0

@[simp]
theorem natChunkFn_eq_natChunk (b R x : ℕ) (i : Fin R) :
    natChunkFn b R x i = natChunk b x i.val := by
  unfold natChunkFn
  have hlen : i.val < (extractNatChunks b R x).length := by simp [i.isLt]
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    getElem?_pos (extractNatChunks b R x) i.val hlen, Option.getD_some]
  exact getElem_extractNatChunks b R x i.val hlen

theorem natChunkFn_eq_natChunk_fun (b R x : ℕ) :
    natChunkFn b R x = fun i : Fin R => natChunk b x i.val := by
  funext i
  exact natChunkFn_eq_natChunk b R x i

/-- Single-pass $O(R \cdot b)$ bit-slice chunk extraction directly from `bs : List Bool`:
slices `bs` into `R` chunks of $b$ bits and decodes each $b$-bit slice locally via
`decodeNatBits (bs.take b)`, without decoding the full $n$-bit list into a single $n$-bit `ℕ`
(Section 7.1 (`sec:alg-spec`)). -/
def sliceBitChunks (b : ℕ) : ℕ → List Bool → List ℕ
  | 0, _ => []
  | R + 1, bs => decodeNatBits (bs.take b) :: sliceBitChunks b R (bs.drop b)

/-- Array-memoized single-pass bit-slice chunk lookup for `bs : List Bool`. -/
def sliceBitChunkFn (b R : ℕ) (bs : List Bool) : Fin R → ℕ :=
  let arr := (sliceBitChunks b R bs).toArray
  fun i => arr.getD i.val 0

lemma decodeNatBits_take_lt (b : ℕ) (bs : List Bool) :
    decodeNatBits (bs.take b) < 2 ^ b := by
  calc decodeNatBits (bs.take b)
      < 2 ^ (bs.take b).length := decodeNatBits_lt (bs.take b)
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (List.length_take_le b bs)

lemma decodeNatBits_eq_take_add_drop (b : ℕ) (bs : List Bool) :
    decodeNatBits bs = decodeNatBits (bs.take b) + 2 ^ b * decodeNatBits (bs.drop b) := by
  induction b generalizing bs with
  | zero => simp [decodeNatBits]
  | succ b ih =>
    cases bs with
    | nil => simp [decodeNatBits]
    | cons bit rest =>
      simp only [List.take_succ_cons, List.drop_succ_cons, decodeNatBits]
      rw [ih rest, pow_succ']
      ring

@[simp]
lemma decodeNatBits_mod_two_pow (b : ℕ) (bs : List Bool) :
    decodeNatBits bs % 2 ^ b = decodeNatBits (bs.take b) := by
  rw [decodeNatBits_eq_take_add_drop b bs, mul_comm (2 ^ b), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (decodeNatBits_take_lt b bs)]

@[simp]
lemma decodeNatBits_div_two_pow (b : ℕ) (bs : List Bool) :
    decodeNatBits bs / 2 ^ b = decodeNatBits (bs.drop b) := by
  have hpos : 0 < 2 ^ b := by positivity
  rw [decodeNatBits_eq_take_add_drop b bs, mul_comm (2 ^ b), Nat.add_mul_div_right _ _ hpos,
    Nat.div_eq_of_lt (decodeNatBits_take_lt b bs), zero_add]

@[simp]
theorem sliceBitChunks_eq_extractNatChunks (b R : ℕ) (bs : List Bool) :
    sliceBitChunks b R bs = extractNatChunks b R (decodeNatBits bs) := by
  induction R generalizing bs with
  | zero => rfl
  | succ R ih =>
    simp only [sliceBitChunks, extractNatChunks, decodeNatBits_mod_two_pow,
      decodeNatBits_div_two_pow, ih (bs.drop b)]

@[simp]
theorem sliceBitChunkFn_eq_natChunkFn (b R : ℕ) (bs : List Bool) :
    sliceBitChunkFn b R bs = natChunkFn b R (decodeNatBits bs) := by
  unfold sliceBitChunkFn natChunkFn
  rw [sliceBitChunks_eq_extractNatChunks]

/-- Single-pass $O(R \cdot b)$ Horner base-$2^b$ evaluation of a list of chunk values:
`evalBaseChunks b (c :: cs) = c + 2 ^ b * evalBaseChunks b cs`, avoiding repeated $\Theta(R \cdot n)$
shifts `2 ^ (k * b)`. -/
def evalBaseChunks (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + 2 ^ b * evalBaseChunks b cs

lemma evalBaseChunks_ofFn_eq_sum (b : ℕ) {R : ℕ} (f : Fin R → ℕ) :
    evalBaseChunks b (List.ofFn f) =
      ∑ k : Fin R, f k * 2 ^ (k.val * b) := by
  induction R with
  | zero =>
    simp [evalBaseChunks]
  | succ R ih =>
    rw [List.ofFn_succ, evalBaseChunks, ih (fun i => f i.succ), Fin.sum_univ_succ,
      Fin.val_zero, Nat.zero_mul, pow_zero, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.val_succ, Nat.succ_mul, pow_add]
    ring

lemma encodeNatBits_succ_eq (w x : ℕ) :
    encodeNatBits (w + 1) x = x.testBit 0 :: encodeNatBits w (x / 2) := by
  unfold encodeNatBits
  rw [List.ofFn_succ]
  congr 2
  funext i
  exact Nat.testBit_succ x i.val

lemma encodeNatBits_add (w1 w2 x : ℕ) :
    encodeNatBits (w1 + w2) x = encodeNatBits w1 x ++ encodeNatBits w2 (x / 2 ^ w1) := by
  induction w1 generalizing x with
  | zero =>
    simp [encodeNatBits]
  | succ w1 ih =>
    rw [Nat.succ_add, encodeNatBits_succ_eq (w1 + w2) x, encodeNatBits_succ_eq w1 x,
      List.cons_append, ih (x / 2), Nat.div_div_eq_div_mul, ← pow_succ']

lemma encodeNatBits_add_mul_two_pow (w x y : ℕ) :
    encodeNatBits w (x + 2 ^ w * y) = encodeNatBits w x := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih =>
    rw [encodeNatBits_succ_eq, encodeNatBits_succ_eq]
    have hpow : 2 ^ (w + 1) * y = 2 * (2 ^ w * y) := by rw [pow_succ']; ring
    have hbit : (x + 2 ^ (w + 1) * y).testBit 0 = x.testBit 0 := by
      rw [Nat.testBit_zero, Nat.testBit_zero, hpow, mul_comm 2, Nat.add_mul_mod_self_right]
    have hdiv : (x + 2 ^ (w + 1) * y) / 2 = x / 2 + 2 ^ w * y := by
      rw [hpow, mul_comm 2, Nat.add_mul_div_right _ _ (by decide)]
    rw [hbit, hdiv, ih (x / 2)]

lemma encodeNatBits_mod_two_pow_of_le {w b : ℕ} (hw : w ≤ b) (x : ℕ) :
    encodeNatBits w (x % 2 ^ b) = encodeNatBits w x := by
  have hdecomp : x = x % 2 ^ b + 2 ^ b * (x / 2 ^ b) := (Nat.mod_add_div x (2 ^ b)).symm
  have hpow : 2 ^ b * (x / 2 ^ b) = 2 ^ w * (2 ^ (b - w) * (x / 2 ^ b)) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hw]
  conv_rhs => rw [hdecomp, hpow, encodeNatBits_add_mul_two_pow]

lemma encodeNatBits_step_carry (b outLen total rest : ℕ) :
    encodeNatBits (min outLen b) (total % 2 ^ b) ++
        encodeNatBits (outLen - min outLen b) (total / 2 ^ b + rest) =
      encodeNatBits outLen (total + 2 ^ b * rest) := by
  by_cases hle : outLen ≤ b
  · have hmin : min outLen b = outLen := Nat.min_eq_left hle
    have hsub : outLen - outLen = 0 := Nat.sub_self outLen
    rw [hmin, hsub]
    have hnil : encodeNatBits 0 (total / 2 ^ b + rest) = [] := rfl
    rw [hnil, List.append_nil, encodeNatBits_mod_two_pow_of_le hle total]
    have hpow : 2 ^ b * rest = 2 ^ outLen * (2 ^ (b - outLen) * rest) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hle]
    rw [hpow, encodeNatBits_add_mul_two_pow]
  · have hlt : b < outLen := not_le.mp hle
    have hmin : min outLen b = b := Nat.min_eq_right (le_of_lt hlt)
    rw [hmin]
    have hout : outLen = b + (outLen - b) := (Nat.add_sub_of_le (le_of_lt hlt)).symm
    conv_rhs => rw [hout, encodeNatBits_add b (outLen - b) (total + 2 ^ b * rest)]
    congr 1
    · rw [encodeNatBits_mod_two_pow_of_le (le_refl b) total, encodeNatBits_add_mul_two_pow]
    · congr 1
      rw [mul_comm (2 ^ b) rest, Nat.add_mul_div_right _ _ (by positivity)]

/-- Single-pass $O(R \cdot b)$ carry-save bit-stream emitter (`carrySaveEmitBits`,
Section 7.1 (`sec:alg-spec`), Section 7.2 (`sec:cost-proof`)):
Given chunk values `cs : List ℕ` and running carry `carry : ℕ`, at each step adds `total := c + carry`,
emits the low $\min(\text{outLen}, b)$ bits `encodeNatBits (min outLen b) (total % 2 ^ b)`, and
propagates `total / 2 ^ b` to the next chunk, without materializing a single $2n$-bit `ℕ`. -/
def carrySaveEmitBits (b : ℕ) : ℕ → List ℕ → ℕ → List Bool
  | outLen, [], carry => encodeNatBits outLen carry
  | outLen, c :: cs, carry =>
      let stepBits := min outLen b
      let total := c + carry
      encodeNatBits stepBits (total % 2 ^ b) ++
        carrySaveEmitBits b (outLen - stepBits) cs (total / 2 ^ b)

theorem carrySaveEmitBits_eq_encodeNatBits (b : ℕ) (cs : List ℕ) :
    ∀ (outLen carry : ℕ),
      carrySaveEmitBits b outLen cs carry =
        encodeNatBits outLen (carry + evalBaseChunks b cs) := by
  induction cs with
  | nil =>
    intro outLen carry
    simp [carrySaveEmitBits, evalBaseChunks]
  | cons c cs ih =>
    intro outLen carry
    simp only [carrySaveEmitBits, evalBaseChunks]
    rw [ih (outLen - min outLen b) ((c + carry) / 2 ^ b),
      encodeNatBits_step_carry b outLen (c + carry) (evalBaseChunks b cs)]
    congr 1
    ring

/-- Operation-tracking `w`-bit unsigned bit-encoding (`encodeNatBitsTracked`):
encodes `x` into `w` LSB-first bits in `2 * w + 2` elementary bit steps. -/
def encodeNatBitsTracked (w x : ℕ) : CostM (List Bool) :=
  (encodeNatBits w x, costLinearWordOp 2 w 2)

@[simp]
theorem encodeNatBitsTracked_fst (w x : ℕ) :
    (encodeNatBitsTracked w x).1 = encodeNatBits w x := rfl

@[simp]
theorem encodeNatBitsTracked_snd (w x : ℕ) :
    (encodeNatBitsTracked w x).2 = 2 * w + 2 := rfl

/-- Operation-tracking `w`-bit unsigned bit-decoding (`decodeNatBitsTracked`):
decodes the first `w` bits `bs.take w` in `2 * w + 2` elementary bit steps. -/
def decodeNatBitsTracked (w : ℕ) (bs : List Bool) : CostM ℕ :=
  (decodeNatBits (bs.take w), costLinearWordOp 2 w 2)

@[simp]
theorem decodeNatBitsTracked_fst (w : ℕ) (bs : List Bool) :
    (decodeNatBitsTracked w bs).1 = decodeNatBits (bs.take w) := rfl

@[simp]
theorem decodeNatBitsTracked_snd (w : ℕ) (bs : List Bool) :
    (decodeNatBitsTracked w bs).2 = 2 * w + 2 := rfl

/-- Operation-tracking `w`-bit base-case shift-and-add multiplication on `List Bool` operands
(`binaryShiftAddMulBitsTracked`):
decodes `aBits.take w` and `bBits.take w`, runs `binaryShiftAddMulRegTracked w`, and encodes the
`2 * w`-bit product bit-list in `5 * w * w + 14 * w + 8` bit operations. -/
def binaryShiftAddMulBitsTracked (w : ℕ) (aBits bBits : List Bool) : CostM (List Bool) :=
  let a := decodeNatBitsTracked w aBits
  let b := decodeNatBitsTracked w bBits
  let prod := binaryShiftAddMulRegTracked w a.1 b.1
  let out := encodeNatBitsTracked (2 * w) prod.1
  (out.1, a.2 + b.2 + prod.2 + out.2 + 2)

@[simp]
theorem binaryShiftAddMulBitsTracked_fst (w : ℕ) (aBits bBits : List Bool) :
    (binaryShiftAddMulBitsTracked w aBits bBits).1 =
      encodeNatBits (2 * w) (decodeNatBits (aBits.take w) * decodeNatBits (bBits.take w)) := by
  unfold binaryShiftAddMulBitsTracked
  dsimp only [encodeNatBitsTracked_fst, decodeNatBitsTracked_fst]
  rw [binaryShiftAddMulRegTracked_fst _ (decodeNatBits_take_lt w aBits)]

@[simp]
theorem binaryShiftAddMulBitsTracked_snd (w : ℕ) (aBits bBits : List Bool) :
    (binaryShiftAddMulBitsTracked w aBits bBits).2 = 5 * w * w + 14 * w + 8 := by
  simp only [binaryShiftAddMulBitsTracked, decodeNatBitsTracked_snd,
    binaryShiftAddMulRegTracked_snd, encodeNatBitsTracked_snd]
  ring

theorem binaryShiftAddMulBitsTracked_snd_le {w : ℕ} (hw : 1 ≤ w) (aBits bBits : List Bool) :
    (binaryShiftAddMulBitsTracked w aBits bBits).2 ≤ 27 * (w * w) := by
  rw [binaryShiftAddMulBitsTracked_snd]
  nlinarith

/-- Operation-tracking single-pass bit-slice chunk extraction from `bs : List Bool`. -/
def sliceBitChunksTracked (b : ℕ) : ℕ → List Bool → CostM (List ℕ)
  | 0, _ => ([], 2)
  | R + 1, bs =>
    let tail := sliceBitChunksTracked b R (bs.drop b)
    (decodeNatBits (bs.take b) :: tail.1, tail.2 + 2 * b + 2)

@[simp]
theorem sliceBitChunksTracked_fst (b : ℕ) :
    ∀ (R : ℕ) (bs : List Bool), (sliceBitChunksTracked b R bs).1 = sliceBitChunks b R bs
  | 0, _ => rfl
  | R + 1, bs => by simp [sliceBitChunksTracked, sliceBitChunks, sliceBitChunksTracked_fst b R]

@[simp]
theorem sliceBitChunksTracked_snd (b : ℕ) :
    ∀ (R : ℕ) (bs : List Bool), (sliceBitChunksTracked b R bs).2 = R * (2 * b + 2) + 2
  | 0, _ => by simp [sliceBitChunksTracked]
  | R + 1, bs => by
    simp only [sliceBitChunksTracked, sliceBitChunksTracked_snd b R (bs.drop b)]
    ring

/-- Operation-tracking array-memoized bit-slice chunk lookup for `bs : List Bool`. -/
def sliceBitChunkFnTracked (b R : ℕ) (bs : List Bool) : CostM (Fin R → ℕ) :=
  let ch := sliceBitChunksTracked b R bs
  let arr := ch.1.toArray
  ((fun i => arr.getD i.val 0), ch.2 + R + 2)

@[simp]
theorem sliceBitChunkFnTracked_fst (b R : ℕ) (bs : List Bool) :
    (sliceBitChunkFnTracked b R bs).1 = sliceBitChunkFn b R bs := by
  unfold sliceBitChunkFnTracked sliceBitChunkFn
  simp

@[simp]
theorem sliceBitChunkFnTracked_snd (b R : ℕ) (bs : List Bool) :
    (sliceBitChunkFnTracked b R bs).2 = R * (2 * b + 3) + 4 := by
  simp only [sliceBitChunkFnTracked, sliceBitChunksTracked_snd]
  ring

/-- Operation-tracking single-pass carry-save bit-stream emitter. -/
def carrySaveEmitBitsTracked (b : ℕ) : ℕ → List ℕ → ℕ → CostM (List Bool)
  | outLen, [], carry => (encodeNatBits outLen carry, outLen + 2)
  | outLen, c :: cs, carry =>
    let stepBits := min outLen b
    let total := c + carry
    let tail := carrySaveEmitBitsTracked b (outLen - stepBits) cs (total / 2 ^ b)
    (encodeNatBits stepBits (total % 2 ^ b) ++ tail.1, tail.2 + 2 * b + 2)

@[simp]
theorem carrySaveEmitBitsTracked_fst (b : ℕ) (cs : List ℕ) :
    ∀ (outLen carry : ℕ),
      (carrySaveEmitBitsTracked b outLen cs carry).1 = carrySaveEmitBits b outLen cs carry := by
  induction cs with
  | nil => intro outLen carry; rfl
  | cons c cs ih =>
    intro outLen carry
    simp [carrySaveEmitBitsTracked, carrySaveEmitBits, ih]

theorem carrySaveEmitBitsTracked_snd_le (b : ℕ) (cs : List ℕ) :
    ∀ (outLen carry : ℕ),
      (carrySaveEmitBitsTracked b outLen cs carry).2 ≤ cs.length * (2 * b + 2) + outLen + 2 := by
  induction cs with
  | nil => intro outLen carry; simp [carrySaveEmitBitsTracked]
  | cons c cs ih =>
    intro outLen carry
    simp only [carrySaveEmitBitsTracked, List.length_cons]
    have h := ih (outLen - min outLen b) ((c + carry) / 2 ^ b)
    linarith [Nat.sub_le outLen (min outLen b)]

end IntMul

#print axioms IntMul.decodeNatBits_encodeNatBits
#print axioms IntMul.encodeNatBits_decodeNatBits
#print axioms IntMul.abs_quantizeReal_sub_self_le
#print axioms IntMul.norm_quantizeComplex_p_add_two_sub_self_le
#print axioms IntMul.roundShiftInt_eq_quantizeRealMantissa
#print axioms IntMul.FixedComplex.norm_mulRounded_sub_mul_le
#print axioms IntMul.wordWidthBounds_quantizeComplexFixed_of_norm_le
