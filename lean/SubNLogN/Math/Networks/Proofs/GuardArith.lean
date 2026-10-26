import Mathlib
import SubNLogN.Math.Networks.AppCFun

/-!
# Appendix A guard arithmetic

Proofs of the three guard-arithmetic contracts of `AppCFun.lean` (Proposition A.11 (`prop:prop14-param`),
Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-guard-growth`)):

* `guardDyadic_holds : GuardDyadicStmt`: the Gaussian dyadics `GaussDyadic a b` (denominator `2^a`,
  real and imaginary parts at most `2^b` in absolute value) are closed under `+` and `−` (bound
  `b + 1`), halving (denominator `a + 1`), negation and multiplication by `i`, and are monotone in
  `a` and in `b`;
* `guardRepr_holds : GuardReprStmt`: the integer numerators at denominator `2^a` are at most
  `2^{a+b}` in absolute value;
* `guardRecurrence_holds : GuardRecurrenceStmt`: the depth recurrence `A(j+1) ≤ s·A(j) + E`
  (`j < j_max`) with `A 0 ≤ 8d`, `1 < s < m⁵` and `m^{j_max − 1} ≤ d` gives
  `A j_max ≤ s(8 + E/(s−1))·d⁶`. Route: `(s−1)A(j) ≤ (s−1)s^j·8d + E(s^j − 1)` by induction, hence
  `A(j_max) ≤ s^{j_max}(8d + E/(s−1))`, and `s^{j_max} ≤ s·(m⁵)^{j_max−1} ≤ s·d⁵`.

All helpers are in `SubNLogN.Math.Networks.GuardArithAux`.
-/

namespace SubNLogN.Math.Networks

namespace GuardArithAux

/-! ## Gaussian dyadics -/

/-- Real and imaginary parts of `(m + n i) / 2^a`. -/
theorem re_im_of_eq {a : ℕ} {m n : ℤ} {z : ℂ}
    (h : z = ((m : ℂ) + (n : ℂ) * Complex.I) / 2 ^ a) :
    z.re = (m : ℝ) / 2 ^ a ∧ z.im = (n : ℝ) / 2 ^ a := by
  have h2 : (2 : ℂ) ^ a = (((2 : ℝ) ^ a : ℝ) : ℂ) := by norm_cast
  rw [h, h2, Complex.div_ofReal_re, Complex.div_ofReal_im]
  simp

/-- Lifting the denominator: `(m + n i)/2^a = (m 2^t + n 2^t i)/2^{a+t}`. -/
theorem lift_eq {a t : ℕ} {m n : ℤ} :
    ((m : ℂ) + (n : ℂ) * Complex.I) / 2 ^ a
      = (((m * 2 ^ t : ℤ) : ℂ) + ((n * 2 ^ t : ℤ) : ℂ) * Complex.I) / 2 ^ (a + t) := by
  rw [div_eq_div_iff (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero)]
  push_cast
  ring

/-- If `x = k / 2^a` and `|x| ≤ 2^b` then `|k| ≤ 2^{a+b}`. -/
theorem num_bound {a b : ℕ} {k : ℤ} {x : ℝ} (hx : x = (k : ℝ) / 2 ^ a) (hb : |x| ≤ 2 ^ b) :
    |k| ≤ 2 ^ (a + b) := by
  have ha : (0 : ℝ) < 2 ^ a := by positivity
  rw [hx, abs_div, abs_of_pos ha, div_le_iff₀ ha] at hb
  have h : ((|k| : ℤ) : ℝ) ≤ ((2 ^ (a + b) : ℤ) : ℝ) := by
    push_cast
    rw [add_comm a b, pow_add]
    exact hb
  exact_mod_cast h

/-! ## The depth recurrence -/

/-- Closed form of the recurrence, multiplied by `s − 1 > 0`:
`(s − 1)·A j ≤ (s − 1)·s^j·A₀ + E(s^j − 1)` for `j ≤ j_max`. -/
theorem rec_bound {s E A₀ : ℝ} {A : ℕ → ℝ} {jmax : ℕ} (hs : 1 < s) (h0 : A 0 ≤ A₀)
    (hrec : ∀ j < jmax, A (j + 1) ≤ s * A j + E) :
    ∀ j ≤ jmax, (s - 1) * A j ≤ (s - 1) * (s ^ j * A₀) + E * (s ^ j - 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h : (s - 1) * A 0 ≤ (s - 1) * A₀ := mul_le_mul_of_nonneg_left h0 (by linarith)
    simpa using h
  | succ j ih =>
    intro hj
    have h1 := hrec j (by omega)
    have h2 := ih (by omega)
    have hs1 : (0 : ℝ) ≤ s - 1 := by linarith
    have hs0 : (0 : ℝ) ≤ s := by linarith
    have h3 : (s - 1) * A (j + 1) ≤ (s - 1) * (s * A j + E) := mul_le_mul_of_nonneg_left h1 hs1
    have h4 : s * ((s - 1) * A j) ≤ s * ((s - 1) * (s ^ j * A₀) + E * (s ^ j - 1)) :=
      mul_le_mul_of_nonneg_left h2 hs0
    rw [pow_succ]
    nlinarith [h3, h4]

/-- `s^J ≤ s·d⁵` when `1 < s < m⁵`, `1 < m`, `1 ≤ d` and `m^{J−1} ≤ d`. -/
theorem pow_le {m s d : ℝ} {J : ℕ} (hm : 1 < m) (hs : 1 < s) (hsm : s < m ^ 5) (hd : 1 ≤ d)
    (hmd : m ^ (J - 1) ≤ d) : s ^ J ≤ s * d ^ 5 := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    have h1 : (1 : ℝ) ≤ d ^ 5 := one_le_pow₀ hd
    rw [pow_zero]
    nlinarith
  · obtain ⟨i, rfl⟩ : ∃ i, J = i + 1 := ⟨J - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hmd
    have hs0 : 0 ≤ s := by linarith
    have hm0 : 0 ≤ m := by linarith
    have h1 : s ^ i ≤ (m ^ 5) ^ i := pow_le_pow_left₀ hs0 hsm.le i
    have h2 : (m ^ 5) ^ i = (m ^ i) ^ 5 := by rw [← pow_mul, ← pow_mul, mul_comm]
    have h3 : (m ^ i) ^ 5 ≤ d ^ 5 := pow_le_pow_left₀ (pow_nonneg hm0 i) hmd 5
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans h3)) hs0

end GuardArithAux

/-- CONTRACT `GuardDyadicStmt` (guard closure, Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)). -/
theorem guardDyadic_holds : GuardDyadicStmt := by
  intro a b z w hz hw
  obtain ⟨⟨m, n, hzmn⟩, hzre, hzim⟩ := hz
  obtain ⟨⟨m', n', hwmn⟩, hwre, hwim⟩ := hw
  have hb : (0 : ℝ) < 2 ^ b := by positivity
  have hb1 : (2 : ℝ) ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
  obtain ⟨hzre1, hzre2⟩ := abs_le.mp hzre
  obtain ⟨hzim1, hzim2⟩ := abs_le.mp hzim
  obtain ⟨hwre1, hwre2⟩ := abs_le.mp hwre
  obtain ⟨hwim1, hwim2⟩ := abs_le.mp hwim
  refine ⟨⟨⟨m + m', n + n', ?_⟩, ?_, ?_⟩, ⟨⟨m - m', n - n', ?_⟩, ?_, ?_⟩,
    ⟨⟨m, n, ?_⟩, ?_, ?_⟩, ⟨⟨-m, -n, ?_⟩, ?_, ?_⟩, ⟨⟨-n, m, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  -- `z + w`
  · rw [hzmn, hwmn]; push_cast; ring
  · rw [Complex.add_re, hb1]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Complex.add_im, hb1]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- `z - w`
  · rw [hzmn, hwmn]; push_cast; ring
  · rw [Complex.sub_re, hb1]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Complex.sub_im, hb1]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- `z / 2`
  · rw [hzmn, div_div, ← pow_succ]
  · rw [Complex.div_ofNat_re]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Complex.div_ofNat_im]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- `-z`
  · rw [hzmn]; push_cast; ring
  · rw [Complex.neg_re, abs_neg]; exact hzre
  · rw [Complex.neg_im, abs_neg]; exact hzim
  -- `i z`
  · rw [hzmn]; push_cast; linear_combination ((n : ℂ) / 2 ^ a) * Complex.I_sq
  · rw [Complex.I_mul_re, abs_neg]; exact hzim
  · rw [Complex.I_mul_im]; exact hzre
  -- monotone in the denominator exponent
  · intro a' ha'
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ha'
    exact ⟨⟨m * 2 ^ t, n * 2 ^ t, hzmn.trans GuardArithAux.lift_eq⟩, hzre, hzim⟩
  -- monotone in the magnitude exponent
  · intro b' hb'
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb'
    exact ⟨⟨m, n, hzmn⟩, hzre.trans h, hzim.trans h⟩

/-- CONTRACT `GuardReprStmt` (representation, Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)). -/
theorem guardRepr_holds : GuardReprStmt := by
  intro a b z hz
  obtain ⟨⟨m, n, hzmn⟩, hzre, hzim⟩ := hz
  obtain ⟨hre, him⟩ := GuardArithAux.re_im_of_eq hzmn
  exact ⟨m, n, hzmn, GuardArithAux.num_bound hre hzre, GuardArithAux.num_bound him hzim⟩

/-- CONTRACT `GuardRecurrenceStmt` (depth recurrence over sequential children,
Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)). -/
theorem guardRecurrence_holds : GuardRecurrenceStmt := by
  intro m s E d jmax A hm hs hsm hE hd hmd hA0 hrec
  have hs1 : 0 < s - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hcl := GuardArithAux.rec_bound hs hA0 hrec jmax le_rfl
  have hpow : s ^ jmax ≤ s * d ^ 5 := GuardArithAux.pow_le hm hs hsm hd hmd
  -- write `E = q (s − 1)` with `q = E/(s − 1) ≥ 0`
  obtain ⟨q, hq0, hEq, hqdef⟩ : ∃ q : ℝ, 0 ≤ q ∧ E = q * (s - 1) ∧ E / (s - 1) = q :=
    ⟨E / (s - 1), div_nonneg hE hs1.le, (div_mul_cancel₀ E (ne_of_gt hs1)).symm, rfl⟩
  rw [hqdef]
  subst hEq
  have hA : A jmax ≤ s ^ jmax * (8 * d) + q * (s ^ jmax - 1) := by
    have h1 : (s - 1) * A jmax ≤ (s - 1) * (s ^ jmax * (8 * d) + q * (s ^ jmax - 1)) := by
      nlinarith [hcl]
    exact le_of_mul_le_mul_left h1 hs1
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have h2 : s ^ jmax * (8 * d + q) ≤ s * d ^ 5 * (8 * d + q) :=
    mul_le_mul_of_nonneg_right hpow (by linarith)
  have h3 : 8 * d + q ≤ (8 + q) * d := by nlinarith [mul_le_mul_of_nonneg_left hd hq0]
  have h4 : s * d ^ 5 * (8 * d + q) ≤ s * d ^ 5 * ((8 + q) * d) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hs0.le (pow_nonneg hd0 5))
  have h5 : s * d ^ 5 * ((8 + q) * d) = s * (8 + q) * d ^ 6 := by ring
  nlinarith [hA, h2, h4, h5, hq0]

end SubNLogN.Math.Networks
