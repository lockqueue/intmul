import SubNLogN.Math.Common.Grid
import SubNLogN.Math.Common.RoundNearest

/-!
# Common: integer numerators of grid values (`GridInt`)

Integer-level infrastructure shared by the machine kernels and the integer-arithmetic modules. A value
on the `F`-grid `C̃_F = 2^{-F}(ℤ + iℤ)` (Definition 3.1 (`def:grid`)) is represented by its pair
of integer numerators. This file imports only `Common/Grid.lean` and `Common/RoundNearest.lean`
(no `Machine`).

Definitions (bodies chosen to agree by `rfl` with the `Machine` ones):
* `gridValC F c = (c.1 + i·c.2)·2^{-F}` (= `Machine.gridVal`), `gridValR F a = a·2^{-F}`,
  `gridIntC F z = (round (Re z·2^F), round (Im z·2^F))` (= `Machine.gridInt`);
* `rneDivPos n d` (nearest rounding of `n/d`, ties to even, for `d > 0`), `rneDiv n d` (any `d`,
  `0` for `d = 0`), `rneShift z s = rneDivPos z (2^s)` (unfolds to `Machine.rnePow`),
  `tdivShift z s = z.tdiv (2^s)` (= `Machine.tdivPow`), and the componentwise `rneShiftC`,
  `tdivShiftC` (= `Machine.quantShiftC`, `Machine.truncShiftC`);
* `smulC a c = (a·c.1, a·c.2)`, `cmulC a b` (= `Machine.cmulC`).
* half-up roundings (ties toward `+∞`): `rhuShift z s` (= `Machine.rhuPow`), `rhuShiftC`
  (= `Machine.roundHalfUpShiftC`), `rhuDiv n d` (any `d`).

Main facts:
* rounding of integer quotients: `roundHalfEven_div_of_pos`, `roundHalfEven_div`,
  `truncInt_div_of_pos`, `roundHalfEven_div_two_pow`, `truncInt_div_two_pow`;
* `Quant_F`/`Q_F` of a value at precision `F + s`: `quantR_gridValR`, `truncR_gridValR`,
  `quantC_gridValC`, `truncC_gridValC`;
* half-up: `floor_div_add_half`, `floor_div_two_pow_add_half`, `roundHalfUpR_gridValR`,
  `crnd_roundHalfUpR_gridValC` (`roundHalfUpR`, `crnd` from `Common/RoundNearest.lean`);
* round trip `gridIntC_gridValC`, `gridValC_gridIntC`, `onGrid_iff_exists_gridValC`;
* numerator algebra (`gridValC_add`, `gridValC_sum`, `gridValC_smulC`, `gridValC_cmulC`,
  `I_mul_gridValC`, `star_gridValC`, …) and precision changes (`gridValC_add_prec`,
  `gridValC_add_smulC_two_pow`, `gridValC_regrid`, `gridIntC_regrid`);
* norm and width bounds (`abs_fst_le_norm_mul`, `fitsWidth_gridValC_iff`,
  `fitsWidth_of_onDiskGrid`, …) and nearest rounding of `gridIntC`.
-/

namespace SubNLogN.Math.Common.GridInt

open SubNLogN.Math.Common

/-! ## Definitions -/

/-- The value `(c.1 + i·c.2)·2^{-F}` of a numerator pair at precision `F` (same body as
`SubNLogN.Machine.gridVal`). -/
noncomputable def gridValC (F : ℕ) (c : ℤ × ℤ) : ℂ :=
  ⟨(c.1 : ℝ) * gridUnit F, (c.2 : ℝ) * gridUnit F⟩

/-- The value `a·2^{-F}` of a real numerator at precision `F`. -/
noncomputable def gridValR (F : ℕ) (a : ℤ) : ℝ := (a : ℝ) * gridUnit F

/-- The nearest numerators `(round (Re z·2^F), round (Im z·2^F))` of `z` at precision `F`, exact
on the `F`-grid (same body as `SubNLogN.Machine.gridInt`). -/
noncomputable def gridIntC (F : ℕ) (z : ℂ) : ℤ × ℤ :=
  (round (z.re * 2 ^ F), round (z.im * 2 ^ F))

/-- Nearest rounding of `n / d`, ties to even, for `d > 0` (floor quotient `n / d` and remainder
`n % d ∈ [0, d)`). -/
def rneDivPos (n d : ℤ) : ℤ :=
  if 2 * (n % d) < d then n / d
  else if d < 2 * (n % d) then n / d + 1
  else if n / d % 2 = 0 then n / d else n / d + 1

/-- Nearest rounding of `n / d`, ties to even, for any `d` (`0` for `d = 0`, matching `x / 0 = 0`
in `ℝ`). -/
def rneDiv (n d : ℤ) : ℤ :=
  if d = 0 then 0 else if 0 < d then rneDivPos n d else rneDivPos (-n) (-d)

/-- Nearest rounding of `z / 2^s`, ties to even (unfolds to the body of
`SubNLogN.Machine.rnePow`). -/
def rneShift (z : ℤ) (s : ℕ) : ℤ := rneDivPos z (2 ^ s)

/-- Truncation toward zero of `z / 2^s` (same body as `SubNLogN.Machine.tdivPow`). -/
def tdivShift (z : ℤ) (s : ℕ) : ℤ := z.tdiv (2 ^ s)

/-- Componentwise `rneShift` (= `SubNLogN.Machine.quantShiftC`). -/
def rneShiftC (s : ℕ) (c : ℤ × ℤ) : ℤ × ℤ := (rneShift c.1 s, rneShift c.2 s)

/-- Componentwise `tdivShift` (= `SubNLogN.Machine.truncShiftC`). -/
def tdivShiftC (s : ℕ) (c : ℤ × ℤ) : ℤ × ℤ := (tdivShift c.1 s, tdivShift c.2 s)

/-- An integer times a numerator pair. -/
def smulC (a : ℤ) (c : ℤ × ℤ) : ℤ × ℤ := (a * c.1, a * c.2)

/-- Exact complex product of numerators `(a₀b₀ - a₁b₁, a₀b₁ + a₁b₀)` (same body as
`SubNLogN.Machine.cmulC`). -/
def cmulC (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

@[simp] theorem gridValC_re (F : ℕ) (c : ℤ × ℤ) : (gridValC F c).re = (c.1 : ℝ) * gridUnit F :=
  rfl

@[simp] theorem gridValC_im (F : ℕ) (c : ℤ × ℤ) : (gridValC F c).im = (c.2 : ℝ) * gridUnit F :=
  rfl

@[simp] theorem gridIntC_fst (F : ℕ) (z : ℂ) : (gridIntC F z).1 = round (z.re * 2 ^ F) := rfl

@[simp] theorem gridIntC_snd (F : ℕ) (z : ℂ) : (gridIntC F z).2 = round (z.im * 2 ^ F) := rfl

theorem gridValC_eq_mk (F : ℕ) (c : ℤ × ℤ) : gridValC F c = ⟨gridValR F c.1, gridValR F c.2⟩ :=
  rfl

theorem smulC_eq_smul (a : ℤ) (c : ℤ × ℤ) : smulC a c = a • c := rfl

/-! ## The grid unit -/

theorem gridUnit_mul_two_pow (F : ℕ) : gridUnit F * 2 ^ F = 1 := by
  unfold gridUnit; exact inv_mul_cancel₀ (by positivity)

theorem two_pow_mul_gridUnit (F : ℕ) : (2 : ℝ) ^ F * gridUnit F = 1 := by
  unfold gridUnit; exact mul_inv_cancel₀ (by positivity)

theorem gridUnit_add (p q : ℕ) : gridUnit (p + q) = gridUnit p * gridUnit q := by
  unfold gridUnit; rw [pow_add, mul_inv]

theorem gridUnit_ne_zero (F : ℕ) : gridUnit F ≠ 0 := (gridUnit_pos F).ne'

/-- `a·2^{-(F+s)}·2^F = a/2^s`. -/
theorem intCast_mul_gridUnit_add_mul (a : ℤ) (F s : ℕ) :
    (a : ℝ) * gridUnit (F + s) * 2 ^ F = (a : ℝ) / 2 ^ s := by
  rw [gridUnit_add]
  unfold gridUnit
  field_simp

/-- Round trip of a real numerator: `a·2^{-F}·2^F = a`. -/
theorem gridValR_mul_two_pow (F : ℕ) (a : ℤ) : gridValR F a * 2 ^ F = a := by
  unfold gridValR; rw [mul_assoc, gridUnit_mul_two_pow, mul_one]

theorem gridValC_re_mul_two_pow (F : ℕ) (c : ℤ × ℤ) : (gridValC F c).re * 2 ^ F = c.1 :=
  gridValR_mul_two_pow F c.1

theorem gridValC_im_mul_two_pow (F : ℕ) (c : ℤ × ℤ) : (gridValC F c).im * 2 ^ F = c.2 :=
  gridValR_mul_two_pow F c.2

/-- `round (a·2^{-F}·2^F) = a`. -/
theorem round_intCast_mul_gridUnit_mul (a : ℤ) (F : ℕ) :
    round ((a : ℝ) * gridUnit F * 2 ^ F) = a := by
  rw [mul_assoc, gridUnit_mul_two_pow, mul_one, round_intCast]

/-! ## Rounding of integer quotients -/

/-- `roundHalfEven (n/d) = rneDivPos n d` for `d > 0`. -/
theorem roundHalfEven_div_of_pos (n d : ℤ) (hd : 0 < d) :
    roundHalfEven ((n : ℝ) / (d : ℝ)) = rneDivPos n d := by
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = (e : ℤ) := ⟨d.toNat, by omega⟩
  have he : (0 : ℝ) < (e : ℝ) := by exact_mod_cast hd
  have hcast : ((e : ℤ) : ℝ) = (e : ℝ) := Int.cast_natCast e
  rw [hcast]
  have hfl : ⌊(n : ℝ) / (e : ℝ)⌋ = n / (e : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_intCast]
  have hfr : Int.fract ((n : ℝ) / (e : ℝ)) = ((n % (e : ℤ) : ℤ) : ℝ) / (e : ℝ) :=
    Int.fract_div_intCast_eq_div_intCast_mod
  have hlt : Int.fract ((n : ℝ) / (e : ℝ)) < 1 / 2 ↔ 2 * (n % (e : ℤ)) < (e : ℤ) := by
    rw [hfr, div_lt_iff₀ he]
    constructor
    · intro h
      have h' : ((2 * (n % (e : ℤ)) : ℤ) : ℝ) < ((e : ℤ) : ℝ) := by push_cast at h ⊢; linarith
      exact_mod_cast h'
    · intro h
      have h' : ((2 * (n % (e : ℤ)) : ℤ) : ℝ) < ((e : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; linarith
  have hgt : 1 / 2 < Int.fract ((n : ℝ) / (e : ℝ)) ↔ (e : ℤ) < 2 * (n % (e : ℤ)) := by
    rw [hfr, lt_div_iff₀ he]
    constructor
    · intro h
      have h' : ((e : ℤ) : ℝ) < ((2 * (n % (e : ℤ)) : ℤ) : ℝ) := by push_cast at h ⊢; linarith
      exact_mod_cast h'
    · intro h
      have h' : ((e : ℤ) : ℝ) < ((2 * (n % (e : ℤ)) : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; linarith
  unfold roundHalfEven rneDivPos
  rw [hfl]
  by_cases h1 : 2 * (n % (e : ℤ)) < (e : ℤ)
  · rw [if_pos (hlt.2 h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hlt.1 h)), if_neg h1]
    by_cases h2 : (e : ℤ) < 2 * (n % (e : ℤ))
    · rw [if_pos (hgt.2 h2), if_pos h2]
    · rw [if_neg (fun h => h2 (hgt.1 h)), if_neg h2]

/-- `roundHalfEven (n/d) = rneDiv n d` for every `d` (both are `0` for `d = 0`). -/
theorem roundHalfEven_div (n d : ℤ) : roundHalfEven ((n : ℝ) / (d : ℝ)) = rneDiv n d := by
  unfold rneDiv
  split_ifs with h0 hpos
  · subst h0; simp [roundHalfEven]
  · exact roundHalfEven_div_of_pos n d hpos
  · have hneg : 0 < -d := by omega
    rw [← roundHalfEven_div_of_pos (-n) (-d) hneg]
    congr 1
    push_cast
    rw [neg_div_neg_eq]

/-- `truncInt (z/d) = z.tdiv d` for `d > 0`. -/
theorem truncInt_div_of_pos (z d : ℤ) (hd : 0 < d) :
    truncInt ((z : ℝ) / (d : ℝ)) = z.tdiv d := by
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = (e : ℤ) := ⟨d.toNat, by omega⟩
  have hdpos : (0 : ℝ) < e := by exact_mod_cast hd
  have hcast : ((e : ℤ) : ℝ) = (e : ℝ) := Int.cast_natCast e
  rw [hcast]
  unfold truncInt
  split_ifs with h
  · have hz : (0 : ℝ) ≤ z := by
      by_contra hneg
      push Not at hneg
      have : (z : ℝ) / e < 0 := div_neg_of_neg_of_pos hneg hdpos
      linarith
    have hz' : 0 ≤ z := by exact_mod_cast hz
    rw [Int.floor_div_natCast, Int.floor_intCast, Int.tdiv_eq_ediv_of_nonneg hz']
  · have hz : (z : ℝ) < 0 := by
      by_contra hneg
      push Not at hneg
      exact h (div_nonneg hneg hdpos.le)
    have hz' : z < 0 := by exact_mod_cast hz
    have e1 : (z : ℝ) / e = -((((-z : ℤ)) : ℝ) / e) := by push_cast; ring
    have e2 : z.tdiv (e : ℤ) = -((-z).tdiv (e : ℤ)) := by rw [Int.neg_tdiv, neg_neg]
    rw [e1, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast, e2,
      Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ -z)]

/-- `roundHalfEven (z/2^s) = rneShift z s`. -/
theorem roundHalfEven_div_two_pow (z : ℤ) (s : ℕ) :
    roundHalfEven ((z : ℝ) / 2 ^ s) = rneShift z s := by
  have h := roundHalfEven_div_of_pos z (2 ^ s) (by positivity)
  push_cast at h
  exact h

/-- `truncInt (z/2^s) = tdivShift z s`. -/
theorem truncInt_div_two_pow (z : ℤ) (s : ℕ) :
    truncInt ((z : ℝ) / 2 ^ s) = tdivShift z s := by
  have h := truncInt_div_of_pos z (2 ^ s) (by positivity)
  push_cast at h
  exact h

/-- **`Quant_F` of a value at precision `F + s`** (Definition 3.1 (`def:grid`)):
`quantR F (z·2^{-(F+s)}) = rneShift z s · 2^{-F}`. -/
theorem quantR_gridValR (F s : ℕ) (z : ℤ) :
    quantR F (gridValR (F + s) z) = gridValR F (rneShift z s) := by
  unfold quantR gridValR
  rw [intCast_mul_gridUnit_add_mul, roundHalfEven_div_two_pow]

/-- **`Q_F` of a value at precision `F + s`** (Definition 3.1 (`def:grid`)):
`truncR F (z·2^{-(F+s)}) = tdivShift z s · 2^{-F}`. -/
theorem truncR_gridValR (F s : ℕ) (z : ℤ) :
    truncR F (gridValR (F + s) z) = gridValR F (tdivShift z s) := by
  unfold truncR gridValR
  rw [intCast_mul_gridUnit_add_mul, truncInt_div_two_pow]

/-- Complex form: `quantC F (gridValC (F + s) c) = gridValC F (rneShiftC s c)`. -/
theorem quantC_gridValC (F s : ℕ) (c : ℤ × ℤ) :
    quantC F (gridValC (F + s) c) = gridValC F (rneShiftC s c) := by
  apply Complex.ext
  · exact quantR_gridValR F s c.1
  · exact quantR_gridValR F s c.2

/-- Complex form: `truncC F (gridValC (F + s) c) = gridValC F (tdivShiftC s c)`. -/
theorem truncC_gridValC (F s : ℕ) (c : ℤ × ℤ) :
    truncC F (gridValC (F + s) c) = gridValC F (tdivShiftC s c) := by
  apply Complex.ext
  · exact truncR_gridValR F s c.1
  · exact truncR_gridValR F s c.2

/-- `Q_F` fixes values at precision `F`. -/
theorem truncC_gridValC_self (F : ℕ) (c : ℤ × ℤ) : truncC F (gridValC F c) = gridValC F c :=
  truncC_eq_self F _ ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩

/-- `Quant_F` fixes values at precision `F`. -/
theorem quantC_gridValC_self (F : ℕ) (c : ℤ × ℤ) : quantC F (gridValC F c) = gridValC F c :=
  quantC_eq_self F _ ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩

/-! ## Half-up rounding (ties toward `+∞`) -/

/-- Nearest rounding of `z / 2^s`, ties toward `+∞`: `(z + 2^s / 2) / 2^s` (floor division; same
body as `SubNLogN.Machine.rhuPow`). -/
def rhuShift (z : ℤ) (s : ℕ) : ℤ := (z + 2 ^ s / 2) / 2 ^ s

/-- Componentwise `rhuShift` (= `SubNLogN.Machine.roundHalfUpShiftC`). -/
def rhuShiftC (s : ℕ) (c : ℤ × ℤ) : ℤ × ℤ := (rhuShift c.1 s, rhuShift c.2 s)

/-- Nearest rounding of `n / d`, ties toward `+∞`, for any `d` (`0` for `d = 0`, matching
`x / 0 = 0` in `ℝ`). -/
def rhuDiv (n d : ℤ) : ℤ :=
  if 0 ≤ d then (2 * n + d) / (2 * d) else (-(2 * n) - d) / (-(2 * d))

/-- `⌊n/d + 1/2⌋ = rhuDiv n d` for every `d`. -/
theorem floor_div_add_half (n d : ℤ) : ⌊(n : ℝ) / (d : ℝ) + 1 / 2⌋ = rhuDiv n d := by
  unfold rhuDiv
  rcases lt_trichotomy d 0 with hd | rfl | hd
  · rw [if_neg (by omega)]
    obtain ⟨e, he⟩ : ∃ e : ℕ, -(2 * d) = (e : ℤ) := ⟨(-(2 * d)).toNat, by omega⟩
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne
    have heR : ((e : ℕ) : ℝ) = -(2 * (d : ℝ)) := by exact_mod_cast he.symm
    have h : (n : ℝ) / (d : ℝ) + 1 / 2 = (((-(2 * n) - d : ℤ)) : ℝ) / ((e : ℕ) : ℝ) := by
      rw [heR]; push_cast; field_simp; ring
    rw [h, Int.floor_div_natCast, Int.floor_intCast, he]
  · rw [if_pos le_rfl]
    simp only [Int.cast_zero, div_zero, zero_add, mul_zero, add_zero, Int.ediv_zero]
    exact Int.floor_eq_zero_iff.mpr ⟨by norm_num, by norm_num⟩
  · rw [if_pos hd.le]
    obtain ⟨e, he⟩ : ∃ e : ℕ, 2 * d = (e : ℤ) := ⟨(2 * d).toNat, by omega⟩
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have heR : ((e : ℕ) : ℝ) = 2 * (d : ℝ) := by exact_mod_cast he.symm
    have h : (n : ℝ) / (d : ℝ) + 1 / 2 = (((2 * n + d : ℤ)) : ℝ) / ((e : ℕ) : ℝ) := by
      rw [heR]; push_cast; field_simp
    rw [h, Int.floor_div_natCast, Int.floor_intCast, he]

/-- `⌊z/2^s + 1/2⌋ = rhuShift z s`. -/
theorem floor_div_two_pow_add_half (z : ℤ) (s : ℕ) :
    ⌊(z : ℝ) / 2 ^ s + 1 / 2⌋ = rhuShift z s := by
  unfold rhuShift
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have h0 : ⌊(1 / 2 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by norm_num, by norm_num⟩
    rw [pow_zero, div_one, Int.floor_intCast_add, h0]
    norm_num
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have h2 : (2 : ℤ) ^ (t + 1) / 2 = 2 ^ t := by
      rw [pow_succ]; exact Int.mul_ediv_cancel _ (by norm_num)
    rw [h2]
    have e : (z : ℝ) / 2 ^ (t + 1) + 1 / 2 =
        (((z + 2 ^ t : ℤ)) : ℝ) / (((2 ^ (t + 1) : ℕ)) : ℝ) := by
      push_cast; field_simp; ring
    rw [e, Int.floor_div_natCast, Int.floor_intCast]
    push_cast
    rfl

/-- **Half-up rounding of a value at precision `F + s`**:
`roundHalfUpR F (z·2^{-(F+s)}) = rhuShift z s · 2^{-F}`. -/
theorem roundHalfUpR_gridValR (F s : ℕ) (z : ℤ) :
    roundHalfUpR F (gridValR (F + s) z) = gridValR F (rhuShift z s) := by
  unfold roundHalfUpR gridValR
  rw [intCast_mul_gridUnit_add_mul, floor_div_two_pow_add_half]

/-- The defining equation of `roundHalfUpR` (`Common/RoundNearest.lean`). -/
theorem roundHalfUpR_eq (q : ℕ) (x : ℝ) :
    roundHalfUpR q x = ((⌊x * 2 ^ q + 1 / 2⌋ : ℤ) : ℝ) * gridUnit q := rfl

/-- Half-up rounding of an integer quotient: `roundHalfUpR q (n/d) = gridValR q (rhuDiv (n·2^q) d)`
for every `d`. -/
theorem roundHalfUpR_intCast_div (q : ℕ) (n d : ℤ) :
    roundHalfUpR q ((n : ℝ) / (d : ℝ)) = gridValR q (rhuDiv (n * 2 ^ q) d) := by
  unfold roundHalfUpR gridValR
  have e : (n : ℝ) / (d : ℝ) * 2 ^ q = (((n * 2 ^ q : ℤ)) : ℝ) / (d : ℝ) := by push_cast; ring
  rw [e, floor_div_add_half]

/-- Ties-to-even rounding of an integer quotient: `quantR q (n/d) = gridValR q (rneDiv (n·2^q) d)`
for every `d`. -/
theorem quantR_intCast_div (q : ℕ) (n d : ℤ) :
    quantR q ((n : ℝ) / (d : ℝ)) = gridValR q (rneDiv (n * 2 ^ q) d) := by
  unfold quantR gridValR
  have e : (n : ℝ) / (d : ℝ) * 2 ^ q = (((n * 2 ^ q : ℤ)) : ℝ) / (d : ℝ) := by push_cast; ring
  rw [e, roundHalfEven_div]

/-- Complex form: `crnd roundHalfUpR F (gridValC (F + s) c) = gridValC F (rhuShiftC s c)`. -/
theorem crnd_roundHalfUpR_gridValC (F s : ℕ) (c : ℤ × ℤ) :
    crnd roundHalfUpR F (gridValC (F + s) c) = gridValC F (rhuShiftC s c) := by
  apply Complex.ext
  · exact roundHalfUpR_gridValR F s c.1
  · exact roundHalfUpR_gridValR F s c.2

/-! ## Round trip -/

/-- Every numerator pair gives a grid value. -/
theorem onGrid_gridValC (F : ℕ) (c : ℤ × ℤ) : OnGrid F (gridValC F c) :=
  ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩

/-- `gridIntC ∘ gridValC = id`. -/
theorem gridIntC_gridValC (F : ℕ) (c : ℤ × ℤ) : gridIntC F (gridValC F c) = c := by
  ext <;> simp [round_intCast_mul_gridUnit_mul]

/-- `gridValC ∘ gridIntC = id` on the `F`-grid. -/
theorem gridValC_gridIntC {F : ℕ} {z : ℂ} (hz : OnGrid F z) : gridValC F (gridIntC F z) = z := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  apply Complex.ext
  · rw [gridValC_re, gridIntC_fst, ha, round_intCast_mul_gridUnit_mul]
  · rw [gridValC_im, gridIntC_snd, hb, round_intCast_mul_gridUnit_mul]

/-- Grid values are exactly the values of numerator pairs. -/
theorem onGrid_iff_exists_gridValC {F : ℕ} {z : ℂ} :
    OnGrid F z ↔ ∃ c : ℤ × ℤ, gridValC F c = z :=
  ⟨fun hz => ⟨gridIntC F z, gridValC_gridIntC hz⟩, fun ⟨c, hc⟩ => hc ▸ onGrid_gridValC F c⟩

theorem gridValC_injective (F : ℕ) : Function.Injective (gridValC F) := fun c d h => by
  rw [← gridIntC_gridValC F c, h, gridIntC_gridValC]

theorem gridValC_inj {F : ℕ} {c d : ℤ × ℤ} : gridValC F c = gridValC F d ↔ c = d :=
  (gridValC_injective F).eq_iff

/-- On the grid the numerators are unique: `gridIntC F z = c ↔ gridValC F c = z`. -/
theorem gridIntC_eq_iff {F : ℕ} {z : ℂ} (hz : OnGrid F z) (c : ℤ × ℤ) :
    gridIntC F z = c ↔ gridValC F c = z := by
  constructor
  · rintro rfl; exact gridValC_gridIntC hz
  · rintro rfl; exact gridIntC_gridValC F c

/-! ## Numerator algebra -/

/-- `gridValC F c = 2^{-F}·(c.1 + i·c.2)`. -/
theorem gridValC_eq (F : ℕ) (c : ℤ × ℤ) :
    gridValC F c = (gridUnit F : ℂ) * ((c.1 : ℂ) + (c.2 : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [mul_comm]

@[simp] theorem gridValC_zero (F : ℕ) : gridValC F 0 = 0 := by
  apply Complex.ext <;> simp

theorem gridValC_add (F : ℕ) (c d : ℤ × ℤ) : gridValC F (c + d) = gridValC F c + gridValC F d := by
  apply Complex.ext <;> simp [add_mul]

theorem gridValC_neg (F : ℕ) (c : ℤ × ℤ) : gridValC F (-c) = -gridValC F c := by
  apply Complex.ext <;> simp

theorem gridValC_sub (F : ℕ) (c d : ℤ × ℤ) : gridValC F (c - d) = gridValC F c - gridValC F d := by
  apply Complex.ext <;> simp [sub_mul]

/-- `gridValC F` as an additive homomorphism. -/
noncomputable def gridValCHom (F : ℕ) : ℤ × ℤ →+ ℂ := AddMonoidHom.mk' (gridValC F) (gridValC_add F)

@[simp] theorem gridValCHom_apply (F : ℕ) (c : ℤ × ℤ) : gridValCHom F c = gridValC F c := rfl

/-- Finite sums. -/
theorem gridValC_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ × ℤ) (F : ℕ) :
    gridValC F (∑ i ∈ s, f i) = ∑ i ∈ s, gridValC F (f i) :=
  map_sum (gridValCHom F) f s

/-- Integer multiples: `gridValC F (smulC a c) = a·gridValC F c`. -/
theorem gridValC_smulC (F : ℕ) (a : ℤ) (c : ℤ × ℤ) :
    gridValC F (smulC a c) = (a : ℂ) * gridValC F c := by
  apply Complex.ext <;> simp [smulC, mul_assoc]

theorem gridValC_zsmul (F : ℕ) (a : ℤ) (c : ℤ × ℤ) : gridValC F (a • c) = (a : ℂ) * gridValC F c :=
  gridValC_smulC F a c

/-- Multiplication by `i`: `i·gridValC F (a, b) = gridValC F (-b, a)`. -/
theorem I_mul_gridValC (F : ℕ) (c : ℤ × ℤ) : Complex.I * gridValC F c = gridValC F (-c.2, c.1) := by
  apply Complex.ext <;> simp

/-- Conjugation: `conj (gridValC F (a, b)) = gridValC F (a, -b)`. -/
theorem star_gridValC (F : ℕ) (c : ℤ × ℤ) : star (gridValC F c) = gridValC F (c.1, -c.2) := by
  apply Complex.ext <;> simp

/-- **Exact product**: precisions add (`gridValC F a * gridValC G b = gridValC (F + G) (cmulC a b)`). -/
theorem gridValC_cmulC (F G : ℕ) (a b : ℤ × ℤ) :
    gridValC F a * gridValC G b = gridValC (F + G) (cmulC a b) := by
  apply Complex.ext
  · simp only [Complex.mul_re, gridValC_re, gridValC_im, cmulC, gridUnit_add]; push_cast; ring
  · simp only [Complex.mul_im, gridValC_re, gridValC_im, cmulC, gridUnit_add]; push_cast; ring

/-- Real products: `gridValR p a * gridValR p' b = gridValR (p + p') (a * b)`. -/
theorem gridValR_mul (p p' : ℕ) (a b : ℤ) :
    gridValR p a * gridValR p' b = gridValR (p + p') (a * b) := by
  unfold gridValR; rw [gridUnit_add]; push_cast; ring

/-- A real grid value times a complex one: `gridValR p a · gridValC p' c = gridValC (p + p') (smulC a c)`. -/
theorem ofReal_gridValR_mul_gridValC (p p' : ℕ) (a : ℤ) (c : ℤ × ℤ) :
    ((gridValR p a : ℝ) : ℂ) * gridValC p' c = gridValC (p + p') (smulC a c) := by
  apply Complex.ext
  · simp only [Complex.re_ofReal_mul, gridValC_re, gridValR, smulC, gridUnit_add]; push_cast; ring
  · simp only [Complex.im_ofReal_mul, gridValC_im, gridValR, smulC, gridUnit_add]; push_cast; ring

/-! ## Changing the precision -/

/-- Raising the precision divides the value: `gridValC (F + t) c = gridValC F c / 2^t`. -/
theorem gridValC_add_prec (F t : ℕ) (c : ℤ × ℤ) : gridValC (F + t) c = gridValC F c / 2 ^ t := by
  rw [gridValC_eq, gridValC_eq, gridUnit_add]
  unfold gridUnit
  push_cast
  ring

/-- `gridValC (F + 1) c = gridValC F c / 2`. -/
theorem gridValC_succ (F : ℕ) (c : ℤ × ℤ) : gridValC (F + 1) c = gridValC F c / 2 := by
  simpa using gridValC_add_prec F 1 c

/-- Scaling by `2^e`: `2^e·gridValC F c = gridValC F (smulC (2^e) c)`. -/
theorem two_pow_mul_gridValC (F e : ℕ) (c : ℤ × ℤ) :
    (2 : ℂ) ^ e * gridValC F c = gridValC F (smulC (2 ^ e) c) := by
  rw [gridValC_smulC]; push_cast; rfl

/-- `gridValC (F + s) (smulC (2^s) c) = gridValC F c`. -/
theorem gridValC_add_smulC_two_pow (F s : ℕ) (c : ℤ × ℤ) :
    gridValC (F + s) (smulC (2 ^ s) c) = gridValC F c := by
  rw [← two_pow_mul_gridValC, gridValC_add_prec]
  field_simp

/-- **Re-gridding**: for `F ≤ F'` the same value at the finer precision `F'` has its numerators
multiplied by `2^{F'-F}`. -/
theorem gridValC_regrid {F F' : ℕ} (h : F ≤ F') (c : ℤ × ℤ) :
    gridValC F' (smulC (2 ^ (F' - F)) c) = gridValC F c := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact gridValC_add_smulC_two_pow F t c

/-! ## Numerators of grid values -/

theorem gridIntC_zero (F : ℕ) : gridIntC F 0 = 0 := by
  rw [gridIntC_eq_iff (onGrid_zero F), gridValC_zero]

theorem gridIntC_add {F : ℕ} {z w : ℂ} (hz : OnGrid F z) (hw : OnGrid F w) :
    gridIntC F (z + w) = gridIntC F z + gridIntC F w := by
  rw [gridIntC_eq_iff (hz.add hw), gridValC_add, gridValC_gridIntC hz, gridValC_gridIntC hw]

theorem gridIntC_neg {F : ℕ} {z : ℂ} (hz : OnGrid F z) : gridIntC F (-z) = -gridIntC F z := by
  rw [gridIntC_eq_iff hz.neg, gridValC_neg, gridValC_gridIntC hz]

theorem gridIntC_sub {F : ℕ} {z w : ℂ} (hz : OnGrid F z) (hw : OnGrid F w) :
    gridIntC F (z - w) = gridIntC F z - gridIntC F w := by
  rw [gridIntC_eq_iff (hz.sub hw), gridValC_sub, gridValC_gridIntC hz, gridValC_gridIntC hw]

theorem gridIntC_intCast_mul {F : ℕ} {z : ℂ} (hz : OnGrid F z) (a : ℤ) :
    gridIntC F ((a : ℂ) * z) = smulC a (gridIntC F z) := by
  rw [gridIntC_eq_iff (hz.intCast_mul a), gridValC_smulC, gridValC_gridIntC hz]

/-- `gridIntC` of a numerator value at a coarser precision: `gridIntC (F + s) (gridValC F c) =
smulC (2^s) c`. -/
theorem gridIntC_gridValC_add (F s : ℕ) (c : ℤ × ℤ) :
    gridIntC (F + s) (gridValC F c) = smulC (2 ^ s) c := by
  rw [← gridValC_add_smulC_two_pow F s c, gridIntC_gridValC]

/-- **Re-gridding of numerators**: on the `F`-grid and for `F ≤ F'`,
`gridIntC F' z = smulC (2^{F'-F}) (gridIntC F z)`. -/
theorem gridIntC_regrid {F F' : ℕ} (h : F ≤ F') {z : ℂ} (hz : OnGrid F z) :
    gridIntC F' z = smulC (2 ^ (F' - F)) (gridIntC F z) := by
  rw [gridIntC_eq_iff (hz.mono h), gridValC_regrid h, gridValC_gridIntC hz]

/-! ## Norm bounds on numerators -/

/-- `|c.1| ≤ ‖gridValC F c‖·2^F`. -/
theorem abs_fst_le_norm_mul (F : ℕ) (c : ℤ × ℤ) : |(c.1 : ℝ)| ≤ ‖gridValC F c‖ * 2 ^ F := by
  have h := Complex.abs_re_le_norm (gridValC F c)
  rw [gridValC_re, abs_mul, abs_of_pos (gridUnit_pos F)] at h
  calc |(c.1 : ℝ)| = |(c.1 : ℝ)| * gridUnit F * 2 ^ F := by
        rw [mul_assoc, gridUnit_mul_two_pow, mul_one]
    _ ≤ ‖gridValC F c‖ * 2 ^ F := by gcongr

/-- `|c.2| ≤ ‖gridValC F c‖·2^F`. -/
theorem abs_snd_le_norm_mul (F : ℕ) (c : ℤ × ℤ) : |(c.2 : ℝ)| ≤ ‖gridValC F c‖ * 2 ^ F := by
  have h := Complex.abs_im_le_norm (gridValC F c)
  rw [gridValC_im, abs_mul, abs_of_pos (gridUnit_pos F)] at h
  calc |(c.2 : ℝ)| = |(c.2 : ℝ)| * gridUnit F * 2 ^ F := by
        rw [mul_assoc, gridUnit_mul_two_pow, mul_one]
    _ ≤ ‖gridValC F c‖ * 2 ^ F := by gcongr

/-- If `‖gridValC F c‖ ≤ 2^M` then both numerators are at most `2^{M+F}` in absolute value. -/
theorem abs_le_of_norm_le {F M : ℕ} {c : ℤ × ℤ} (h : ‖gridValC F c‖ ≤ 2 ^ M) :
    |c.1| ≤ 2 ^ (M + F) ∧ |c.2| ≤ 2 ^ (M + F) := by
  have hF : (0 : ℝ) < 2 ^ F := by positivity
  have hb : ‖gridValC F c‖ * 2 ^ F ≤ (2 : ℝ) ^ (M + F) := by
    rw [pow_add]; exact mul_le_mul_of_nonneg_right h hF.le
  have h1 := (abs_fst_le_norm_mul F c).trans hb
  have h2 := (abs_snd_le_norm_mul F c).trans hb
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- Numerators of a disk-grid value: `|a|, |b| ≤ 2^F`. -/
theorem abs_gridIntC_le_of_onDiskGrid {F : ℕ} {z : ℂ} (hz : OnDiskGrid F z) :
    |(gridIntC F z).1| ≤ 2 ^ F ∧ |(gridIntC F z).2| ≤ 2 ^ F := by
  have h : ‖gridValC F (gridIntC F z)‖ ≤ 2 ^ 0 := by
    rw [gridValC_gridIntC hz.1, pow_zero]; exact hz.2
  simpa using abs_le_of_norm_le h

/-! ## Widths -/

/-- `FitsWidthR` of a numerator value is a bound on the numerator. -/
theorem fitsWidthR_gridValR_iff {F w : ℕ} {a : ℤ} :
    FitsWidthR F w (gridValR F a) ↔ -(2 : ℤ) ^ (w - 1) ≤ a ∧ a < (2 : ℤ) ^ (w - 1) := by
  constructor
  · rintro ⟨a', ha', h1, h2⟩
    have haa : a = a' := by
      have h := mul_right_cancel₀ (gridUnit_ne_zero F) ha'
      exact_mod_cast h
    subst haa
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨a, rfl, h1, h2⟩

/-- `FitsWidth` of a numerator value is a bound on both numerators. -/
theorem fitsWidth_gridValC_iff {F w : ℕ} {c : ℤ × ℤ} :
    FitsWidth F w (gridValC F c) ↔
      (-(2 : ℤ) ^ (w - 1) ≤ c.1 ∧ c.1 < (2 : ℤ) ^ (w - 1)) ∧
        (-(2 : ℤ) ^ (w - 1) ≤ c.2 ∧ c.2 < (2 : ℤ) ^ (w - 1)) :=
  and_congr fitsWidthR_gridValR_iff fitsWidthR_gridValR_iff

/-- A value fitting a width lies on the grid. -/
theorem onGrid_of_fitsWidth {F w : ℕ} {z : ℂ} (h : FitsWidth F w z) : OnGrid F z := by
  obtain ⟨⟨a, ha, -⟩, ⟨b, hb, -⟩⟩ := h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

/-- For a grid value, `FitsWidth` is a bound on the numerators `gridIntC F z`. -/
theorem fitsWidth_iff_gridIntC {F w : ℕ} {z : ℂ} (hz : OnGrid F z) :
    FitsWidth F w z ↔
      (-(2 : ℤ) ^ (w - 1) ≤ (gridIntC F z).1 ∧ (gridIntC F z).1 < (2 : ℤ) ^ (w - 1)) ∧
        (-(2 : ℤ) ^ (w - 1) ≤ (gridIntC F z).2 ∧ (gridIntC F z).2 < (2 : ℤ) ^ (w - 1)) := by
  conv_lhs => rw [← gridValC_gridIntC hz]
  exact fitsWidth_gridValC_iff

/-- `FitsWidth` is monotone in the width. -/
theorem fitsWidth_mono {F w w' : ℕ} {z : ℂ} (h : FitsWidth F w z) (hw : w ≤ w') :
    FitsWidth F w' z := by
  have hp : (2 : ℤ) ^ (w - 1) ≤ 2 ^ (w' - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hg := onGrid_of_fitsWidth h
  rw [fitsWidth_iff_gridIntC hg] at h ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A grid value of modulus at most `2^M` fits width `M + F + 2`. -/
theorem fitsWidth_of_norm_le {F M : ℕ} {z : ℂ} (hz : OnGrid F z) (h : ‖z‖ ≤ 2 ^ M) :
    FitsWidth F (M + F + 2) z := by
  rw [← gridValC_gridIntC hz] at h
  obtain ⟨h1, h2⟩ := abs_le_of_norm_le h
  rw [fitsWidth_iff_gridIntC hz, show M + F + 2 - 1 = M + F + 1 by omega]
  have hp : (2 : ℤ) ^ (M + F) < 2 ^ (M + F + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [abs_le] at h1 h2
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

/-- Disk-grid values fit width `F + 2`. -/
theorem fitsWidth_of_onDiskGrid {F : ℕ} {z : ℂ} (hz : OnDiskGrid F z) : FitsWidth F (F + 2) z := by
  have h := fitsWidth_of_norm_le (M := 0) hz.1 (by rw [pow_zero]; exact hz.2)
  simpa using h

/-! ## `gridIntC` is a nearest rounding -/

/-- `‖gridValC F (gridIntC F z) - z‖ ≤ (√2/2)·2^{-F}`. -/
theorem norm_gridValC_gridIntC_sub_le (F : ℕ) (z : ℂ) :
    ‖gridValC F (gridIntC F z) - z‖ ≤ Real.sqrt 2 / 2 * gridUnit F := by
  have key : ∀ x : ℝ, |(round (x * 2 ^ F) : ℝ) * gridUnit F - x| ≤ gridUnit F / 2 := by
    intro x
    have h := abs_sub_round (x * 2 ^ F)
    have e : (round (x * 2 ^ F) : ℝ) * gridUnit F - x =
        -((x * 2 ^ F - round (x * 2 ^ F)) * gridUnit F) := by
      rw [sub_mul, mul_assoc x, two_pow_mul_gridUnit, mul_one]; ring
    rw [e, abs_neg, abs_mul, abs_of_pos (gridUnit_pos F)]
    nlinarith [gridUnit_pos F]
  have hre : |(gridValC F (gridIntC F z) - z).re| ≤ gridUnit F / 2 := by
    rw [Complex.sub_re, gridValC_re, gridIntC_fst]; exact key z.re
  have him : |(gridValC F (gridIntC F z) - z).im| ≤ gridUnit F / 2 := by
    rw [Complex.sub_im, gridValC_im, gridIntC_snd]; exact key z.im
  calc ‖gridValC F (gridIntC F z) - z‖
      ≤ Real.sqrt 2 * max |(gridValC F (gridIntC F z) - z).re|
          |(gridValC F (gridIntC F z) - z).im| := Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (gridUnit F / 2) := by gcongr; exact max_le hre him
    _ = Real.sqrt 2 / 2 * gridUnit F := by ring

end SubNLogN.Math.Common.GridInt
