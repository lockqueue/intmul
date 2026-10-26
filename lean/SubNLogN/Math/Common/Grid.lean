import Mathlib

/-!
# Common: fixed-point grids, widths and rounding (Definition 3.1 (`def:grid`) and eq. (`eq:rounding`))

Shared by the fractional-shift bridge and the Walsh / direct-FFT middle transform.

* `gridUnit q = 2^{-q}`; `OnGrid q z` : `z ∈ C̃_q = 2^{-q}(ℤ + iℤ)`; `OnDiskGrid q z` : `z ∈ 𝔻_q`.
* `FitsWidth q w z` : each component is `2^{-q}` times a signed `w`-bit two's-complement integer
  (Definition 3.1 (`def:grid`)).
* `truncC q` is `Q_q` (componentwise truncation toward zero, [OAI26, eq. (26)], Definition 3.1 (`def:grid`)).
* `quantC q` is `Quant_q` (componentwise nearest rounding, ties to even, [MS] Definition 3.1;
  Section 3.2, Definition 3.1 (`def:grid`)).

Theorems tagged CONTRACT are statements of the paper; all of them are proved in this file
(via the private helper lemmas below).
-/

namespace SubNLogN.Math.Common

/-- The grid unit `2^{-q}`. -/
noncomputable def gridUnit (q : ℕ) : ℝ := ((2 : ℝ) ^ q)⁻¹

theorem gridUnit_pos (q : ℕ) : 0 < gridUnit q := by
  unfold gridUnit; positivity

/-- A real number lies on the grid `2^{-q} ℤ`. -/
def OnGridR (q : ℕ) (x : ℝ) : Prop := ∃ a : ℤ, x = (a : ℝ) * gridUnit q

/-- A complex number lies on the fixed-point grid `C̃_q = 2^{-q}(ℤ + iℤ)` (Definition 3.1
(`def:grid`)). -/
def OnGrid (q : ℕ) (z : ℂ) : Prop := OnGridR q z.re ∧ OnGridR q z.im

/-- The disk grid `𝔻_q = {z ∈ C̃_q : |z| ≤ 1}` (Definition 3.1 (`def:grid`)). -/
def OnDiskGrid (q : ℕ) (z : ℂ) : Prop := OnGrid q z ∧ ‖z‖ ≤ 1

/-- A real component is `2^{-q}` times a signed `w`-bit two's-complement integer, i.e. an integer
in `[-2^{w-1}, 2^{w-1})` (Definition 3.1 (`def:grid`); intended for `w ≥ 1`). -/
def FitsWidthR (q w : ℕ) (x : ℝ) : Prop :=
  ∃ a : ℤ, x = (a : ℝ) * gridUnit q ∧ -(2 : ℤ) ^ (w - 1) ≤ a ∧ a < (2 : ℤ) ^ (w - 1)

/-- Both components of `z` fit the format of `FitsWidthR q w` ("component width `w`"). -/
def FitsWidth (q w : ℕ) (z : ℂ) : Prop := FitsWidthR q w z.re ∧ FitsWidthR q w z.im

/-- Truncation of a real number toward zero to an integer. -/
noncomputable def truncInt (x : ℝ) : ℤ := if 0 ≤ x then ⌊x⌋ else ⌈x⌉

/-- Real truncation toward zero to the grid `2^{-q}ℤ`. -/
noncomputable def truncR (q : ℕ) (x : ℝ) : ℝ := (truncInt (x * 2 ^ q) : ℝ) * gridUnit q

/-- `Q_q`: componentwise truncation toward zero to `C̃_q` ([OAI26, eq. (26)], Definition 3.1 (`def:grid`)). -/
noncomputable def truncC (q : ℕ) (z : ℂ) : ℂ := ⟨truncR q z.re, truncR q z.im⟩

/-- Rounding of a real number to the nearest integer, ties to even. -/
noncomputable def roundHalfEven (x : ℝ) : ℤ :=
  if Int.fract x < 1 / 2 then ⌊x⌋
  else if 1 / 2 < Int.fract x then ⌊x⌋ + 1
  else if ⌊x⌋ % 2 = 0 then ⌊x⌋ else ⌊x⌋ + 1

/-- Real nearest rounding (ties to even) to the grid `2^{-q}ℤ`. -/
noncomputable def quantR (q : ℕ) (x : ℝ) : ℝ := (roundHalfEven (x * 2 ^ q) : ℝ) * gridUnit q

/-- `Quant_q`: componentwise nearest rounding to `C̃_q`, ties to even ([MS] Definition 3.1;
Section 3.2, Definition 3.1 (`def:grid`)). -/
noncomputable def quantC (q : ℕ) (z : ℂ) : ℂ := ⟨quantR q z.re, quantR q z.im⟩

/-! ## Private helpers (integer rounding and grid arithmetic) -/

private theorem gridUnit_mul_two_pow (q : ℕ) : gridUnit q * 2 ^ q = 1 := by
  unfold gridUnit; exact inv_mul_cancel₀ (by positivity)

private theorem gridUnit_add (q q' : ℕ) : gridUnit (q + q') = gridUnit q * gridUnit q' := by
  unfold gridUnit; rw [pow_add, mul_inv]

/-- For `q ≤ q'`, `2^{-q} = 2^{q'-q} · 2^{-q'}`. -/
private theorem gridUnit_eq_mul_of_le {q q' : ℕ} (h : q ≤ q') :
    gridUnit q = (2 : ℝ) ^ (q' - q) * gridUnit q' := by
  unfold gridUnit
  have h2 : (2 : ℝ) ^ q' = 2 ^ (q' - q) * 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

private theorem gridUnit_succ (q : ℕ) : gridUnit (q + 1) = gridUnit q / 2 := by
  unfold gridUnit; rw [pow_succ, mul_inv, div_eq_mul_inv]

/-- `|truncInt y - y| < 1`. -/
private theorem abs_truncInt_sub_lt (y : ℝ) : |(truncInt y : ℝ) - y| < 1 := by
  unfold truncInt
  split_ifs with h
  · have h1 := Int.floor_le y
    have h2 := Int.lt_floor_add_one y
    rw [abs_lt]; constructor <;> linarith
  · have h1 := Int.le_ceil y
    have h2 := Int.ceil_lt_add_one y
    rw [abs_lt]; constructor <;> linarith

/-- `|truncInt y| ≤ |y|` (truncation toward zero). -/
private theorem abs_truncInt_le (y : ℝ) : |(truncInt y : ℝ)| ≤ |y| := by
  unfold truncInt
  split_ifs with h
  · have h1 := Int.floor_le y
    have h2 : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr h
    rw [abs_of_nonneg h2, abs_of_nonneg h]; exact h1
  · rw [not_le] at h
    have h1 := Int.le_ceil y
    have h3 : ⌈y⌉ ≤ 0 := Int.ceil_le.mpr (by simpa using h.le)
    have h2 : (⌈y⌉ : ℝ) ≤ 0 := by exact_mod_cast h3
    rw [abs_of_nonpos h2, abs_of_neg h]; linarith

/-- `|roundHalfEven y - y| ≤ 1/2`. -/
private theorem abs_roundHalfEven_sub_le (y : ℝ) : |(roundHalfEven y : ℝ) - y| ≤ 1 / 2 := by
  have hf := Int.fract_nonneg y
  have hf1 := Int.fract_lt_one y
  have hy : Int.fract y = y - ⌊y⌋ := (Int.self_sub_floor y).symm
  unfold roundHalfEven
  split_ifs with h1 h2 h3 <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- `truncInt` is the identity on integers. -/
private theorem truncInt_intCast (a : ℤ) : truncInt (a : ℝ) = a := by
  unfold truncInt
  split_ifs
  · exact Int.floor_intCast a
  · exact Int.ceil_intCast a

/-- `roundHalfEven` is the identity on integers. -/
private theorem roundHalfEven_intCast (a : ℤ) : roundHalfEven (a : ℝ) = a := by
  unfold roundHalfEven
  rw [Int.fract_intCast, Int.floor_intCast, if_pos (by norm_num : (0 : ℝ) < 1 / 2)]

/-- Scaling identity: `n·2^{-q} - x = (n - x·2^q)·2^{-q}`. -/
private theorem scaled_sub (q : ℕ) (n x : ℝ) :
    n * gridUnit q - x = (n - x * 2 ^ q) * gridUnit q := by
  have h := gridUnit_mul_two_pow q
  calc n * gridUnit q - x = n * gridUnit q - x * (gridUnit q * 2 ^ q) := by rw [h, mul_one]
    _ = (n - x * 2 ^ q) * gridUnit q := by ring

/-- If both components of `w` are `< δ` in modulus then `‖w‖ < √2 δ`. -/
private theorem norm_lt_of_abs_re_im_lt {w : ℂ} {δ : ℝ} (hre : |w.re| < δ) (him : |w.im| < δ) :
    ‖w‖ < Real.sqrt 2 * δ := by
  have hδ : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hre
  have a1 : w.re * w.re < δ ^ 2 := by
    nlinarith [abs_mul_abs_self w.re, abs_nonneg w.re]
  have a2 : w.im * w.im < δ ^ 2 := by
    nlinarith [abs_mul_abs_self w.im, abs_nonneg w.im]
  rw [Complex.norm_def, show Real.sqrt 2 * δ = Real.sqrt (2 * δ ^ 2) by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hδ.le]]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [Complex.normSq_apply]; linarith

/-- If both components of `w` are `≤ δ` in modulus then `‖w‖ ≤ √2 δ`. -/
private theorem norm_le_of_abs_re_im_le {w : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (hre : |w.re| ≤ δ)
    (him : |w.im| ≤ δ) : ‖w‖ ≤ Real.sqrt 2 * δ := by
  have a1 : w.re * w.re ≤ δ ^ 2 := by
    nlinarith [abs_mul_abs_self w.re, abs_nonneg w.re]
  have a2 : w.im * w.im ≤ δ ^ 2 := by
    nlinarith [abs_mul_abs_self w.im, abs_nonneg w.im]
  rw [Complex.norm_def, show Real.sqrt 2 * δ = Real.sqrt (2 * δ ^ 2) by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hδ]]
  apply Real.sqrt_le_sqrt
  rw [Complex.normSq_apply]; linarith

/-- Real truncation is the identity on `2^{-q}ℤ`. -/
private theorem truncR_of_onGridR {q : ℕ} {x : ℝ} (hx : OnGridR q x) : truncR q x = x := by
  obtain ⟨a, rfl⟩ := hx
  unfold truncR
  have h : (a : ℝ) * gridUnit q * 2 ^ q = a := by rw [mul_assoc, gridUnit_mul_two_pow, mul_one]
  rw [h, truncInt_intCast]

/-- Real nearest rounding is the identity on `2^{-q}ℤ`. -/
private theorem quantR_of_onGridR {q : ℕ} {x : ℝ} (hx : OnGridR q x) : quantR q x = x := by
  obtain ⟨a, rfl⟩ := hx
  unfold quantR
  have h : (a : ℝ) * gridUnit q * 2 ^ q = a := by rw [mul_assoc, gridUnit_mul_two_pow, mul_one]
  rw [h, roundHalfEven_intCast]

private theorem onGridR_mono {q q' : ℕ} (h : q ≤ q') {x : ℝ} (hx : OnGridR q x) :
    OnGridR q' x := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a * 2 ^ (q' - q), ?_⟩
  rw [gridUnit_eq_mul_of_le h]
  push_cast
  ring

private theorem onGridR_add {q : ℕ} {x y : ℝ} (hx : OnGridR q x) (hy : OnGridR q y) :
    OnGridR q (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; ring⟩

private theorem onGridR_neg {q : ℕ} {x : ℝ} (hx : OnGridR q x) : OnGridR q (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by push_cast; ring⟩

private theorem onGridR_sub {q : ℕ} {x y : ℝ} (hx : OnGridR q x) (hy : OnGridR q y) :
    OnGridR q (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; ring⟩

private theorem onGridR_mul {q q' : ℕ} {x y : ℝ} (hx : OnGridR q x) (hy : OnGridR q' y) :
    OnGridR (q + q') (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by rw [gridUnit_add]; push_cast; ring⟩

private theorem onGridR_half {q : ℕ} {x : ℝ} (hx : OnGridR q x) : OnGridR (q + 1) (x / 2) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, by rw [gridUnit_succ]; ring⟩

private theorem onGridR_intCast_mul {q : ℕ} {x : ℝ} (hx : OnGridR q x) (n : ℤ) :
    OnGridR q ((n : ℝ) * x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨n * a, by push_cast; ring⟩

private theorem onGridR_intCast (q : ℕ) (a : ℤ) : OnGridR q (a : ℝ) :=
  ⟨a * 2 ^ q, by push_cast; linear_combination (-(a : ℝ)) * gridUnit_mul_two_pow q⟩

/-! ## Rounding error bounds (Section 3.2, eq. (`eq:rounding`)) -/

/-- CONTRACT (Section 3.2, eq. (`eq:rounding`)): real truncation error `|Q_q(x) - x| < 2^{-q}`. -/
theorem abs_truncR_sub_lt (q : ℕ) (x : ℝ) : |truncR q x - x| < gridUnit q := by
  unfold truncR
  have hg := gridUnit_pos q
  rw [scaled_sub, abs_mul, abs_of_pos hg]
  exact lt_of_lt_of_eq (mul_lt_mul_of_pos_right (abs_truncInt_sub_lt (x * 2 ^ q)) hg) (one_mul _)

/-- CONTRACT (Section 3.2, eq. (`eq:rounding`)): truncation toward zero does not increase `|x|`. -/
theorem abs_truncR_le (q : ℕ) (x : ℝ) : |truncR q x| ≤ |x| := by
  unfold truncR
  have hg := gridUnit_pos q
  rw [abs_mul, abs_of_pos hg]
  calc |(truncInt (x * 2 ^ q) : ℝ)| * gridUnit q ≤ |x * 2 ^ q| * gridUnit q :=
        mul_le_mul_of_nonneg_right (abs_truncInt_le (x * 2 ^ q)) hg.le
    _ = |x| * (gridUnit q * 2 ^ q) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ q)]; ring
    _ = |x| := by rw [gridUnit_mul_two_pow, mul_one]

/-- CONTRACT (Section 3.2, eq. (`eq:rounding`)): `|Q_q(z) - z| < √2 · 2^{-q}`. -/
theorem norm_truncC_sub_lt (q : ℕ) (z : ℂ) : ‖truncC q z - z‖ < Real.sqrt 2 * gridUnit q := by
  apply norm_lt_of_abs_re_im_lt
  · rw [Complex.sub_re]; exact abs_truncR_sub_lt q z.re
  · rw [Complex.sub_im]; exact abs_truncR_sub_lt q z.im

/-- CONTRACT (Section 3.2, eq. (`eq:rounding`)): `|Q_q(z)| ≤ |z|`. -/
theorem norm_truncC_le (q : ℕ) (z : ℂ) : ‖truncC q z‖ ≤ ‖z‖ := by
  have h1 : |truncR q z.re| ≤ |z.re| := abs_truncR_le q z.re
  have h2 : |truncR q z.im| ≤ |z.im| := abs_truncR_le q z.im
  have e1 : truncR q z.re * truncR q z.re ≤ z.re * z.re := by
    rw [← abs_mul_abs_self (truncR q z.re), ← abs_mul_abs_self z.re]
    exact mul_self_le_mul_self (abs_nonneg _) h1
  have e2 : truncR q z.im * truncR q z.im ≤ z.im * z.im := by
    rw [← abs_mul_abs_self (truncR q z.im), ← abs_mul_abs_self z.im]
    exact mul_self_le_mul_self (abs_nonneg _) h2
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  rw [Complex.normSq_apply, Complex.normSq_apply]
  show truncR q z.re * truncR q z.re + truncR q z.im * truncR q z.im ≤ z.re * z.re + z.im * z.im
  linarith

/-- CONTRACT (Section 3.2, eq. (`eq:rounding`)): real nearest-rounding error `|Quant_q(x) - x| ≤ 2^{-q}/2`. -/
theorem abs_quantR_sub_le (q : ℕ) (x : ℝ) : |quantR q x - x| ≤ gridUnit q / 2 := by
  unfold quantR
  have hg := gridUnit_pos q
  rw [scaled_sub, abs_mul, abs_of_pos hg]
  calc |(roundHalfEven (x * 2 ^ q) : ℝ) - x * 2 ^ q| * gridUnit q ≤ 1 / 2 * gridUnit q :=
        mul_le_mul_of_nonneg_right (abs_roundHalfEven_sub_le (x * 2 ^ q)) hg.le
    _ = gridUnit q / 2 := by ring

/-- CONTRACT (Section 3.2, eq. (`eq:rounding`)): `|Quant_q(z) - z| ≤ (√2/2) · 2^{-q}`. -/
theorem norm_quantC_sub_le (q : ℕ) (z : ℂ) :
    ‖quantC q z - z‖ ≤ Real.sqrt 2 / 2 * gridUnit q := by
  have hg := gridUnit_pos q
  have h := norm_le_of_abs_re_im_le (w := quantC q z - z) (δ := gridUnit q / 2) (by positivity)
    (by rw [Complex.sub_re]; exact abs_quantR_sub_le q z.re)
    (by rw [Complex.sub_im]; exact abs_quantR_sub_le q z.im)
  calc ‖quantC q z - z‖ ≤ Real.sqrt 2 * (gridUnit q / 2) := h
    _ = Real.sqrt 2 / 2 * gridUnit q := by ring

/-- CONTRACT (Section 3.2 (`sec:prelim-grids`)): `Q_q` maps the closed unit disk into the disk grid `𝔻_q`. -/
theorem truncC_mem_diskGrid (q : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) : OnDiskGrid q (truncC q z) := by
  exact ⟨⟨⟨truncInt (z.re * 2 ^ q), rfl⟩, ⟨truncInt (z.im * 2 ^ q), rfl⟩⟩,
    (norm_truncC_le q z).trans hz⟩

/-! ## Grid membership -/

/-- CONTRACT: `Q_q(z)` lies on `C̃_q`. -/
theorem truncC_onGrid (q : ℕ) (z : ℂ) : OnGrid q (truncC q z) := by
  exact ⟨⟨truncInt (z.re * 2 ^ q), rfl⟩, ⟨truncInt (z.im * 2 ^ q), rfl⟩⟩

/-- CONTRACT: `Quant_q(z)` lies on `C̃_q`. -/
theorem quantC_onGrid (q : ℕ) (z : ℂ) : OnGrid q (quantC q z) := by
  exact ⟨⟨roundHalfEven (z.re * 2 ^ q), rfl⟩, ⟨roundHalfEven (z.im * 2 ^ q), rfl⟩⟩

/-- CONTRACT: `Q_q` is the identity on `C̃_q`. -/
theorem truncC_eq_self (q : ℕ) (z : ℂ) (hz : OnGrid q z) : truncC q z = z := by
  apply Complex.ext
  · exact truncR_of_onGridR hz.1
  · exact truncR_of_onGridR hz.2

/-- CONTRACT: `Quant_q` is the identity on `C̃_q`. -/
theorem quantC_eq_self (q : ℕ) (z : ℂ) (hz : OnGrid q z) : quantC q z = z := by
  apply Complex.ext
  · exact quantR_of_onGridR hz.1
  · exact quantR_of_onGridR hz.2

/-- CONTRACT: `C̃_q ⊆ C̃_{q'}` for `q ≤ q'`. -/
theorem OnGrid.mono {q q' : ℕ} (h : q ≤ q') {z : ℂ} (hz : OnGrid q z) : OnGrid q' z := by
  exact ⟨onGridR_mono h hz.1, onGridR_mono h hz.2⟩

/-- CONTRACT: `C̃_q` is closed under addition. -/
theorem OnGrid.add {q : ℕ} {z w : ℂ} (hz : OnGrid q z) (hw : OnGrid q w) : OnGrid q (z + w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re]; exact onGridR_add hz.1 hw.1
  · rw [Complex.add_im]; exact onGridR_add hz.2 hw.2

/-- CONTRACT: `C̃_q` is closed under negation. -/
theorem OnGrid.neg {q : ℕ} {z : ℂ} (hz : OnGrid q z) : OnGrid q (-z) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.neg_re]; exact onGridR_neg hz.1
  · rw [Complex.neg_im]; exact onGridR_neg hz.2

/-- CONTRACT: `C̃_q` is closed under subtraction. -/
theorem OnGrid.sub {q : ℕ} {z w : ℂ} (hz : OnGrid q z) (hw : OnGrid q w) : OnGrid q (z - w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.sub_re]; exact onGridR_sub hz.1 hw.1
  · rw [Complex.sub_im]; exact onGridR_sub hz.2 hw.2

/-- CONTRACT: the product of a `C̃_q` and a `C̃_{q'}` element lies on `C̃_{q+q'}`. -/
theorem OnGrid.mul {q q' : ℕ} {z w : ℂ} (hz : OnGrid q z) (hw : OnGrid q' w) :
    OnGrid (q + q') (z * w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re]; exact onGridR_sub (onGridR_mul hz.1 hw.1) (onGridR_mul hz.2 hw.2)
  · rw [Complex.mul_im]; exact onGridR_add (onGridR_mul hz.1 hw.2) (onGridR_mul hz.2 hw.1)

/-- CONTRACT: `C̃_q` is closed under multiplication by `i`. -/
theorem OnGrid.mul_I {q : ℕ} {z : ℂ} (hz : OnGrid q z) : OnGrid q (z * Complex.I) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_I_re]; exact onGridR_neg hz.2
  · rw [Complex.mul_I_im]; exact hz.1

/-- CONTRACT: halving maps `C̃_q` into `C̃_{q+1}`. -/
theorem OnGrid.half {q : ℕ} {z : ℂ} (hz : OnGrid q z) : OnGrid (q + 1) (z / 2) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.div_ofNat_re]; exact onGridR_half hz.1
  · rw [Complex.div_ofNat_im]; exact onGridR_half hz.2

/-- CONTRACT: `C̃_q` is closed under multiplication by integers. -/
theorem OnGrid.intCast_mul {q : ℕ} {z : ℂ} (hz : OnGrid q z) (n : ℤ) : OnGrid q ((n : ℂ) * z) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    exact onGridR_intCast_mul hz.1 n
  · rw [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero]
    exact onGridR_intCast_mul hz.2 n

/-- The real part of `Q_q(z)` is the real truncation of `Re z`. -/
@[simp] theorem truncC_re (q : ℕ) (z : ℂ) : (truncC q z).re = truncR q z.re := rfl

/-- The imaginary part of `Q_q(z)` is the real truncation of `Im z`. -/
@[simp] theorem truncC_im (q : ℕ) (z : ℂ) : (truncC q z).im = truncR q z.im := rfl

/-- The real part of `Quant_q(z)` is the real nearest rounding of `Re z`. -/
@[simp] theorem quantC_re (q : ℕ) (z : ℂ) : (quantC q z).re = quantR q z.re := rfl

/-- The imaginary part of `Quant_q(z)` is the real nearest rounding of `Im z`. -/
@[simp] theorem quantC_im (q : ℕ) (z : ℂ) : (quantC q z).im = quantR q z.im := rfl

/-- CONTRACT: `Q_q` does not increase the modulus of the real part. -/
theorem abs_re_truncC_le (q : ℕ) (z : ℂ) : |(truncC q z).re| ≤ |z.re| := by
  exact abs_truncR_le q z.re

/-- CONTRACT: `Q_q` does not increase the modulus of the imaginary part. -/
theorem abs_im_truncC_le (q : ℕ) (z : ℂ) : |(truncC q z).im| ≤ |z.im| := by
  exact abs_truncR_le q z.im

/-- CONTRACT: `0 ∈ C̃_q`. -/
theorem onGrid_zero (q : ℕ) : OnGrid q 0 := by
  exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

/-- CONTRACT: Gaussian integers lie on every grid. -/
theorem onGrid_intCast (q : ℕ) (a b : ℤ) : OnGrid q ⟨a, b⟩ := by
  exact ⟨onGridR_intCast q a, onGridR_intCast q b⟩

end SubNLogN.Math.Common
