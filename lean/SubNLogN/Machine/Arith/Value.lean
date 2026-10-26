/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Arith

/-!
# AR, value level (`Arith/Value.lean`): the integer operations of `Contracts/Arith.lean` are `Q`/`Quant`

**Scope (honest summary).** Pure lemmas, all proved (no `sorry`):
* `truncInt_intCast_div` and `roundHalfEven_intCast_div`: the real rounding functions of
  `SubNLogN/Math/Common/Grid.lean` at `z / 2^s` are `tdivPow z s` and `rnePow z s`.
* `gridVal_truncShiftC` : `gridVal F (truncShiftC s c) = truncC F (gridVal (F + s) c)`.
* `gridVal_quantShiftC` : `gridVal F (quantShiftC s c) = quantC F (gridVal (F + s) c)`.
* `gridVal_halfSumC`, `gridVal_halfDiffC` : `Q_F((x ± y)/2)` at precision `F`
  (Theorem 6.5 (`thm:direct-fft`)).
* `gridVal_cmulC` (the exact product) and `gridVal_cmulTruncC` : `Q_F(x·y)` for `x` at precision
  `F₁`, `y` at precision `F₂` and `F₁ + F₂ = F + s` (Lemma 6.2 (`lem:disk-product`)).
* `cvol_eq` : `cvol w v = v.length + 2·w·ncoef v` (with `twosBits_length`, `crecBits_length`).
-/

namespace SubNLogN.Machine

open SubNLogN.Math.Common

/-! ## Rounding of integer quotients -/

/-- `truncInt (z / d) = tdiv z d` for `d > 0`. -/
theorem truncInt_intCast_div (z : ℤ) (d : ℕ) (hd : 0 < d) :
    truncInt ((z : ℝ) / (d : ℝ)) = z.tdiv (d : ℤ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  unfold truncInt
  split_ifs with h
  · have hz : (0 : ℝ) ≤ z := by
      by_contra hneg
      push Not at hneg
      have : (z : ℝ) / d < 0 := div_neg_of_neg_of_pos hneg hdpos
      linarith
    have hz' : 0 ≤ z := by exact_mod_cast hz
    rw [Int.floor_div_natCast, Int.floor_intCast, Int.tdiv_eq_ediv_of_nonneg hz']
  · have hz : (z : ℝ) < 0 := by
      by_contra hneg
      push Not at hneg
      exact h (div_nonneg hneg hdpos.le)
    have hz' : z < 0 := by exact_mod_cast hz
    have e1 : (z : ℝ) / d = -((((-z : ℤ)) : ℝ) / d) := by push_cast; ring
    have e2 : z.tdiv (d : ℤ) = -((-z).tdiv (d : ℤ)) := by rw [Int.neg_tdiv, neg_neg]
    rw [e1, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast, e2,
      Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ -z)]

/-- `roundHalfEven (z / 2^s) = rnePow z s`. -/
theorem roundHalfEven_intCast_div (z : ℤ) (s : ℕ) :
    roundHalfEven ((z : ℝ) / ((2 ^ s : ℕ) : ℝ)) = rnePow z s := by
  have hfl : ⌊(z : ℝ) / ((2 ^ s : ℕ) : ℝ)⌋ = z / 2 ^ s := by
    rw [Int.floor_div_natCast, Int.floor_intCast]; push_cast; rfl
  have hfr : Int.fract ((z : ℝ) / ((2 ^ s : ℕ) : ℝ)) =
      ((z % 2 ^ s : ℤ) : ℝ) / ((2 ^ s : ℕ) : ℝ) := by
    rw [Int.fract_div_intCast_eq_div_intCast_mod]; push_cast; rfl
  have hpos : (0 : ℝ) < ((2 ^ s : ℕ) : ℝ) := by positivity
  have hlt : Int.fract ((z : ℝ) / ((2 ^ s : ℕ) : ℝ)) < 1 / 2 ↔ 2 * (z % 2 ^ s) < 2 ^ s := by
    rw [hfr, div_lt_iff₀ hpos]
    constructor
    · intro h
      have h' : ((2 * (z % 2 ^ s) : ℤ) : ℝ) < ((2 ^ s : ℤ) : ℝ) := by push_cast at h ⊢; linarith
      exact_mod_cast h'
    · intro h
      have h' : ((2 * (z % 2 ^ s) : ℤ) : ℝ) < ((2 ^ s : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; linarith
  have hgt : 1 / 2 < Int.fract ((z : ℝ) / ((2 ^ s : ℕ) : ℝ)) ↔ 2 ^ s < 2 * (z % 2 ^ s) := by
    rw [hfr, lt_div_iff₀ hpos]
    constructor
    · intro h
      have h' : ((2 ^ s : ℤ) : ℝ) < ((2 * (z % 2 ^ s) : ℤ) : ℝ) := by push_cast at h ⊢; linarith
      exact_mod_cast h'
    · intro h
      have h' : ((2 ^ s : ℤ) : ℝ) < ((2 * (z % 2 ^ s) : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; linarith
  unfold roundHalfEven rnePow
  rw [hfl]
  by_cases h1 : 2 * (z % 2 ^ s) < 2 ^ s
  · rw [if_pos (hlt.2 h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hlt.1 h)), if_neg h1]
    by_cases h2 : 2 ^ s < 2 * (z % 2 ^ s)
    · rw [if_pos (hgt.2 h2), if_pos h2]
    · rw [if_neg (fun h => h2 (hgt.1 h)), if_neg h2]

/-! ## Grid values -/

private theorem scale_aux (a : ℤ) (F s : ℕ) :
    (a : ℝ) * gridUnit (F + s) * 2 ^ F = (a : ℝ) / ((2 ^ s : ℕ) : ℝ) := by
  have h1 : (2 : ℝ) ^ F ≠ 0 := by positivity
  have h3 : (2 : ℝ) ^ F * ((2 : ℝ) ^ F)⁻¹ = 1 := mul_inv_cancel₀ h1
  unfold gridUnit
  push_cast
  rw [pow_add, mul_inv, div_eq_mul_inv]
  linear_combination ((a : ℝ) * ((2 : ℝ) ^ s)⁻¹) * h3

private theorem gridUnit_add' (p q : ℕ) : gridUnit (p + q) = gridUnit p * gridUnit q := by
  unfold gridUnit; rw [pow_add, mul_inv]

/-- **`truncShiftC` is `Q_F`**: `Q_F` of a value at precision `F + s` (Definition 3.1 (`def:grid`)). -/
theorem gridVal_truncShiftC (F s : ℕ) (c : CInt) :
    gridVal F (truncShiftC s c) = truncC F (gridVal (F + s) c) := by
  apply Complex.ext
  · show ((tdivPow c.1 s : ℤ) : ℝ) * gridUnit F = truncR F ((c.1 : ℝ) * gridUnit (F + s))
    unfold truncR
    rw [scale_aux, truncInt_intCast_div _ _ (by positivity)]
    simp [tdivPow]
  · show ((tdivPow c.2 s : ℤ) : ℝ) * gridUnit F = truncR F ((c.2 : ℝ) * gridUnit (F + s))
    unfold truncR
    rw [scale_aux, truncInt_intCast_div _ _ (by positivity)]
    simp [tdivPow]

/-- **`quantShiftC` is `Quant_F`**: `Quant_F` of a value at precision `F + s`
(Definition 3.1 (`def:grid`)). -/
theorem gridVal_quantShiftC (F s : ℕ) (c : CInt) :
    gridVal F (quantShiftC s c) = quantC F (gridVal (F + s) c) := by
  apply Complex.ext
  · show ((rnePow c.1 s : ℤ) : ℝ) * gridUnit F = quantR F ((c.1 : ℝ) * gridUnit (F + s))
    unfold quantR
    rw [scale_aux, roundHalfEven_intCast_div]
  · show ((rnePow c.2 s : ℤ) : ℝ) * gridUnit F = quantR F ((c.2 : ℝ) * gridUnit (F + s))
    unfold quantR
    rw [scale_aux, roundHalfEven_intCast_div]

private theorem gridVal_half_add (F : ℕ) (a b : CInt) :
    (gridVal F a + gridVal F b) / 2 = gridVal (F + 1) (a.1 + b.1, a.2 + b.2) := by
  have h : gridUnit (F + 1) = gridUnit F / 2 := by
    unfold gridUnit; rw [pow_succ, mul_inv, div_eq_mul_inv]
  apply Complex.ext
  · rw [Complex.div_ofNat_re, Complex.add_re]
    show (((a.1 : ℝ) * gridUnit F + (b.1 : ℝ) * gridUnit F) / 2) =
      ((a.1 + b.1 : ℤ) : ℝ) * gridUnit (F + 1)
    rw [h]; push_cast; ring
  · rw [Complex.div_ofNat_im, Complex.add_im]
    show (((a.2 : ℝ) * gridUnit F + (b.2 : ℝ) * gridUnit F) / 2) =
      ((a.2 + b.2 : ℤ) : ℝ) * gridUnit (F + 1)
    rw [h]; push_cast; ring

private theorem gridVal_half_sub (F : ℕ) (a b : CInt) :
    (gridVal F a - gridVal F b) / 2 = gridVal (F + 1) (a.1 - b.1, a.2 - b.2) := by
  have h : gridUnit (F + 1) = gridUnit F / 2 := by
    unfold gridUnit; rw [pow_succ, mul_inv, div_eq_mul_inv]
  apply Complex.ext
  · rw [Complex.div_ofNat_re, Complex.sub_re]
    show (((a.1 : ℝ) * gridUnit F - (b.1 : ℝ) * gridUnit F) / 2) =
      ((a.1 - b.1 : ℤ) : ℝ) * gridUnit (F + 1)
    rw [h]; push_cast; ring
  · rw [Complex.div_ofNat_im, Complex.sub_im]
    show (((a.2 : ℝ) * gridUnit F - (b.2 : ℝ) * gridUnit F) / 2) =
      ((a.2 - b.2 : ℤ) : ℝ) * gridUnit (F + 1)
    rw [h]; push_cast; ring

/-- **Normalized butterfly, upper output**: `halfSumC` is `Q_F((x + y)/2)` at precision `F`
(Theorem 6.5 (`thm:direct-fft`)). -/
theorem gridVal_halfSumC (F : ℕ) (a b : CInt) :
    gridVal F (halfSumC a b) = truncC F ((gridVal F a + gridVal F b) / 2) := by
  rw [gridVal_half_add]; exact gridVal_truncShiftC F 1 _

/-- **Normalized butterfly, lower output**: `halfDiffC` is `Q_F((x - y)/2)` at precision `F`. -/
theorem gridVal_halfDiffC (F : ℕ) (a b : CInt) :
    gridVal F (halfDiffC a b) = truncC F ((gridVal F a - gridVal F b) / 2) := by
  rw [gridVal_half_sub]; exact gridVal_truncShiftC F 1 _

/-- **Exact product**: precisions add. -/
theorem gridVal_cmulC (F₁ F₂ : ℕ) (a b : CInt) :
    gridVal F₁ a * gridVal F₂ b = gridVal (F₁ + F₂) (cmulC a b) := by
  apply Complex.ext
  · show (a.1 : ℝ) * gridUnit F₁ * ((b.1 : ℝ) * gridUnit F₂) -
        (a.2 : ℝ) * gridUnit F₁ * ((b.2 : ℝ) * gridUnit F₂) =
      ((a.1 * b.1 - a.2 * b.2 : ℤ) : ℝ) * gridUnit (F₁ + F₂)
    rw [gridUnit_add']; push_cast; ring
  · show (a.1 : ℝ) * gridUnit F₁ * ((b.2 : ℝ) * gridUnit F₂) +
        (a.2 : ℝ) * gridUnit F₁ * ((b.1 : ℝ) * gridUnit F₂) =
      ((a.1 * b.2 + a.2 * b.1 : ℤ) : ℝ) * gridUnit (F₁ + F₂)
    rw [gridUnit_add']; push_cast; ring

/-- **`cmulTruncC` is `Q_F` of the exact product** (Lemma 6.2 (`lem:disk-product`)): for `x` at precision
`F₁`, `y` at precision `F₂` and `F₁ + F₂ = F + s`. With `F₁ = F₂ = F = s = P` this is `Q_P(xy)`. -/
theorem gridVal_cmulTruncC (F F₁ F₂ s : ℕ) (h : F₁ + F₂ = F + s) (a b : CInt) :
    gridVal F (cmulTruncC s a b) = truncC F (gridVal F₁ a * gridVal F₂ b) := by
  rw [gridVal_cmulC, h]; exact gridVal_truncShiftC F s _

/-! ## Volumes -/

theorem twosBits_length (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem crecBits_length (w : ℕ) (cs : List CInt) :
    (crecBits w cs).length = 2 * w * cs.length := by
  induction cs with
  | nil => simp [crecBits]
  | cons c cs ih =>
    simp only [crecBits, List.flatMap_cons, List.length_append, coefBits, twosBits_length,
      List.length_cons] at ih ⊢
    rw [ih]; ring

/-- **Volume of a complex record array**: `#records + 2·w·#coefficients`. -/
theorem cvol_eq (w : ℕ) (v : List (List CInt)) : cvol w v = v.length + 2 * w * ncoef v := by
  induction v with
  | nil => simp [cvol, carrSyms, arrSyms, TMFw.Contracts.blk, ncoef]
  | cons cs v ih =>
    simp only [cvol, carrSyms, arrSyms, TMFw.Contracts.blk, List.map_cons, List.flatten_cons,
      List.length_append, recSyms, List.length_map, crecBits_length,
      ncoef, List.sum_cons, List.length_cons, List.length_nil] at ih ⊢
    rw [ih]; ring

end SubNLogN.Machine
