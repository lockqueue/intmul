import SubNLogN.Math.Common.Grid

/-!
# Common: nearest roundings onto the `q`-grid (`RoundNearest`)

An abstract interface for "a nearest rounding onto the grid `2^{-q}ℤ`", so that statements can be
made for any tie-breaking rule (Definition 3.1 (`def:grid`) and eq. (`eq:rounding`)).

* `IsNearestRounding rr`: for all `q, x`, `rr q x` lies on the `q`-grid and
  `|rr q x - x| ≤ 2^{-q}/2`.
* `crnd rr q z`: the componentwise complex rounding; `crnd_quantR : crnd quantR = quantC`.
* Instances: `quantR` (ties to even; `isNearestRounding_quantR`) and `roundHalfUpR` (ties toward
  `+∞`, i.e. the machine's half-up rounding and WP's `W9d_roundShift`;
  `isNearestRounding_roundHalfUpR`).
* Transfer lemmas for any `rr` with `hrr : IsNearestRounding rr`: `rr_onGridR`, `abs_rr_sub_le`,
  `rr_eq_self` (grid points are fixed, since distinct grid points are `2^{-q}` apart),
  `crnd_onGrid`, `abs_re_crnd_sub_le`, `abs_im_crnd_sub_le`,
  `norm_crnd_sub_le` (`≤ (√2/2)·2^{-q}`) and `crnd_eq_self`.
-/

namespace SubNLogN.Math.Common

/-- A nearest rounding onto the `q`-grid (any tie-breaking rule): `rr q x ∈ 2^{-q}ℤ` and
`|rr q x - x| ≤ 2^{-q}/2`. -/
def IsNearestRounding (rr : ℕ → ℝ → ℝ) : Prop :=
  ∀ q x, OnGridR q (rr q x) ∧ |rr q x - x| ≤ gridUnit q / 2

/-- The componentwise complex rounding `⟨rr q (Re z), rr q (Im z)⟩`. -/
def crnd (rr : ℕ → ℝ → ℝ) (q : ℕ) (z : ℂ) : ℂ := ⟨rr q z.re, rr q z.im⟩

@[simp] theorem crnd_re (rr : ℕ → ℝ → ℝ) (q : ℕ) (z : ℂ) : (crnd rr q z).re = rr q z.re := rfl

@[simp] theorem crnd_im (rr : ℕ → ℝ → ℝ) (q : ℕ) (z : ℂ) : (crnd rr q z).im = rr q z.im := rfl

/-- `crnd quantR = quantC`. -/
theorem crnd_quantR : crnd quantR = quantC := by
  funext q z; rfl

/-- Nearest rounding with ties toward `+∞` ("half up"): `⌊x·2^q + 1/2⌋·2^{-q}`. -/
noncomputable def roundHalfUpR (q : ℕ) (x : ℝ) : ℝ :=
  ((⌊x * 2 ^ q + 1 / 2⌋ : ℤ) : ℝ) * gridUnit q

/-- `Quant_q` (ties to even) is a nearest rounding. -/
theorem isNearestRounding_quantR : IsNearestRounding quantR :=
  fun q x => ⟨⟨roundHalfEven (x * 2 ^ q), rfl⟩, abs_quantR_sub_le q x⟩

/-- The half-up rounding is a nearest rounding. -/
theorem isNearestRounding_roundHalfUpR : IsNearestRounding roundHalfUpR := by
  intro q x
  refine ⟨⟨⌊x * 2 ^ q + 1 / 2⌋, rfl⟩, ?_⟩
  have hg := gridUnit_pos q
  have h2 : (2 : ℝ) ^ q * gridUnit q = 1 := by
    unfold gridUnit; exact mul_inv_cancel₀ (by positivity)
  have h1 := Int.floor_le (x * 2 ^ q + 1 / 2)
  have h3 := Int.lt_floor_add_one (x * 2 ^ q + 1 / 2)
  have hb : |(⌊x * 2 ^ q + 1 / 2⌋ : ℝ) - x * 2 ^ q| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have e : (⌊x * 2 ^ q + 1 / 2⌋ : ℝ) * gridUnit q - x =
      ((⌊x * 2 ^ q + 1 / 2⌋ : ℝ) - x * 2 ^ q) * gridUnit q := by
    rw [sub_mul, mul_assoc x, h2, mul_one]
  unfold roundHalfUpR
  rw [e, abs_mul, abs_of_pos hg]
  calc |(⌊x * 2 ^ q + 1 / 2⌋ : ℝ) - x * 2 ^ q| * gridUnit q ≤ 1 / 2 * gridUnit q :=
        mul_le_mul_of_nonneg_right hb hg.le
    _ = gridUnit q / 2 := by ring

section Transfer

variable {rr : ℕ → ℝ → ℝ}

/-- A nearest rounding lands on the grid. -/
theorem rr_onGridR (hrr : IsNearestRounding rr) (q : ℕ) (x : ℝ) : OnGridR q (rr q x) :=
  (hrr q x).1

/-- A nearest rounding errs by at most half a unit. -/
theorem abs_rr_sub_le (hrr : IsNearestRounding rr) (q : ℕ) (x : ℝ) :
    |rr q x - x| ≤ gridUnit q / 2 :=
  (hrr q x).2

/-- A nearest rounding fixes grid points (distinct grid points are `2^{-q}` apart). -/
theorem rr_eq_self (hrr : IsNearestRounding rr) {q : ℕ} {x : ℝ} (hx : OnGridR q x) :
    rr q x = x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := rr_onGridR hrr q x
  have hg := gridUnit_pos q
  have h := abs_rr_sub_le hrr q x
  rw [hb, ha, ← sub_mul, abs_mul, abs_of_pos hg] at h
  have h2 : |(b : ℝ) - a| ≤ 1 / 2 := by nlinarith
  have h3 : ((|b - a| : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h4 : |b - a| < 1 := by exact_mod_cast h3
  have h5 : b = a := by rw [abs_lt] at h4; omega
  rw [hb, ha, h5]

/-- The complex rounding lands on the grid. -/
theorem crnd_onGrid (hrr : IsNearestRounding rr) (q : ℕ) (z : ℂ) : OnGrid q (crnd rr q z) :=
  ⟨rr_onGridR hrr q z.re, rr_onGridR hrr q z.im⟩

/-- Real part of the complex rounding error. -/
theorem abs_re_crnd_sub_le (hrr : IsNearestRounding rr) (q : ℕ) (z : ℂ) :
    |(crnd rr q z - z).re| ≤ gridUnit q / 2 := by
  rw [Complex.sub_re]; exact abs_rr_sub_le hrr q z.re

/-- Imaginary part of the complex rounding error. -/
theorem abs_im_crnd_sub_le (hrr : IsNearestRounding rr) (q : ℕ) (z : ℂ) :
    |(crnd rr q z - z).im| ≤ gridUnit q / 2 := by
  rw [Complex.sub_im]; exact abs_rr_sub_le hrr q z.im

/-- The complex rounding error: `‖crnd rr q z - z‖ ≤ (√2/2)·2^{-q}`. -/
theorem norm_crnd_sub_le (hrr : IsNearestRounding rr) (q : ℕ) (z : ℂ) :
    ‖crnd rr q z - z‖ ≤ Real.sqrt 2 / 2 * gridUnit q := by
  calc ‖crnd rr q z - z‖
      ≤ Real.sqrt 2 * max |(crnd rr q z - z).re| |(crnd rr q z - z).im| :=
        Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (gridUnit q / 2) := by
        gcongr; exact max_le (abs_re_crnd_sub_le hrr q z) (abs_im_crnd_sub_le hrr q z)
    _ = Real.sqrt 2 / 2 * gridUnit q := by ring

/-- The complex rounding fixes grid points. -/
theorem crnd_eq_self (hrr : IsNearestRounding rr) {q : ℕ} {z : ℂ} (hz : OnGrid q z) :
    crnd rr q z = z :=
  Complex.ext (rr_eq_self hrr hz.1) (rr_eq_self hrr hz.2)

end Transfer

end SubNLogN.Math.Common
