import SubNLogN.Math.Bridge.LemmaB_Scalar

/-!
# Bridge: Lemma 4.4 (bridge Lemma B)(iv), separation `|c₀ - c₁| ≥ 7/(4t)` (`lem:bridge-B`)

We prove `LemmaB_ivStmt` unconditionally (no pending contract is used), directly from the integral
definition `kernelG α ξ = ∫_{ξ-1/2}^{ξ+1/2} φ`, `φ(v) = α e^{-πα²v²}`, plus the IntMul Gaussian tail
bound `IntMul.erfcScaled_realErfScaled_le_gaussian_tail`. (Names `LemmaB*`/`lemmaB*` reflect an earlier draft (bridge Lemma B), now Lemma 4.4 (`lem:bridge-B`), kept for stability.)

Proof (a derivative-free version of the paper's argument). Write `A = πα² = a²`.
1. `G(½-e) - G(½-e-1) = ∫_{-e}^{e} (φ(v) - φ(v+1)) dv` (evenness of `G` and of `φ`, a shift).
2. The integrand is `≥ 0` for `v ≥ -½`, so for `0 ≤ e₀ ≤ e ≤ ½` the integral over `[-e,e]` is at least
   the one over `[-e₀,e₀]` (this is the paper's "D is increasing").
3. For `v ≥ -¼`, `φ(v+1) ≤ κ φ(v)` with `κ = e^{-A/2}`, so for `e₀ ≤ ¼` the integral over
   `[-e₀,e₀]` is `≥ (1-κ)·2∫_0^{e₀} φ`.
4. Concavity of `s ↦ ∫_0^s φ` (as `φ` decreases on `[0,∞)`): `∫_0^{e₀} φ ≥ 4e₀ ∫_0^{1/4} φ`.
5. `∫_0^{1/4} φ = ½ erf(a/4) ≥ ½(1 - e^{-A/16}/(πα/4))` (IntMul tail bound).
6. Numerics, from `A ≥ 32 ln 2` (admissibility, `ω ≥ 8`): `e^{-A/16} ≤ 1/4`, `κ ≤ 1/256`,
   `πα/4 ≥ 2.085`; hence `∫_0^{1/4} φ ≥ 0.44` and the gap is
   `≥ 2(1-κ)·4e₀·0.44 ≥ 3.506 e₀ ≥ (7/2)e₀ = 7/(4t)` for `e₀ = 1/(2t)`.
7. Since `t` is even, every sample `y = (u+½)/t` has `e = |y-½| ≥ 1/(2t)`; the case `y > ½` reduces
   to `y < ½` by evenness of `G`.

Only the lower end of admissibility `α ≥ 2√(ω ln2/π)` is used (as in the paper).
-/

namespace SubNLogN.Math.Bridge

open MeasureTheory

namespace LemmaBSep

/-- The Gaussian density `φ_α(v) = α e^{-πα²v²}` whose box integral is `kernelG`. -/
noncomputable def dens (α v : ℝ) : ℝ := α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2))

theorem kernelG_eq_dens (α ξ : ℝ) :
    kernelG α ξ = ∫ v in (ξ - 1 / 2)..(ξ + 1 / 2), dens α v := rfl

theorem continuous_dens (α : ℝ) : Continuous (dens α) := by
  unfold dens
  fun_prop

theorem dens_neg (α v : ℝ) : dens α (-v) = dens α v := by
  simp [dens]

/-- `φ_α` is radially non-increasing (for `α ≥ 0`). -/
theorem dens_le_of_sq_le {α v w : ℝ} (hα : 0 ≤ α) (h : v ^ 2 ≤ w ^ 2) :
    dens α w ≤ dens α v := by
  unfold dens
  apply mul_le_mul_of_nonneg_left _ hα
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ Real.pi * α ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h h0
  linarith

/-- `G` is even (a local copy, so that this file does not depend on `KernelG_negStmt`). -/
theorem kernelG_neg' (α ξ : ℝ) : kernelG α (-ξ) = kernelG α ξ := by
  rw [kernelG_eq_dens, kernelG_eq_dens]
  have h := intervalIntegral.integral_comp_neg (a := ξ - 1 / 2) (b := ξ + 1 / 2) (dens α)
  simp only [dens_neg] at h
  rw [h, show (-ξ - 1 / 2 : ℝ) = -(ξ + 1 / 2) by ring, show (-ξ + 1 / 2 : ℝ) = -(ξ - 1 / 2) by ring]

/-- Step 1: `G(½-e) - G(½-e-1) = ∫_{-e}^{e} (φ(v) - φ(v+1)) dv`. -/
theorem kernelG_sub_eq (α e : ℝ) :
    kernelG α (1 / 2 - e) - kernelG α (1 / 2 - e - 1) =
      ∫ v in (-e)..e, (dens α v - dens α (v + 1)) := by
  have hc := continuous_dens α
  have hc1 : Continuous (fun v => dens α (v + 1)) := hc.comp (continuous_add_const 1)
  have h0 : kernelG α (1 / 2 - e) = ∫ v in (-e)..(1 - e), dens α v := by
    rw [kernelG_eq_dens]
    rw [show (1 / 2 - e - 1 / 2 : ℝ) = -e by ring, show (1 / 2 - e + 1 / 2 : ℝ) = 1 - e by ring]
  have h1 : kernelG α (1 / 2 - e - 1) = ∫ v in e..(1 + e), dens α v := by
    rw [show (1 / 2 - e - 1 : ℝ) = -(1 / 2 + e) by ring, kernelG_neg', kernelG_eq_dens]
    rw [show (1 / 2 + e - 1 / 2 : ℝ) = e by ring, show (1 / 2 + e + 1 / 2 : ℝ) = 1 + e by ring]
  have hshift : (∫ v in (-e)..e, dens α (v + 1)) = ∫ v in (1 - e)..(1 + e), dens α v := by
    rw [intervalIntegral.integral_comp_add_right (dens α) 1]
    rw [show (-e + 1 : ℝ) = 1 - e by ring, show (e + 1 : ℝ) = 1 + e by ring]
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-e) e) (hc.intervalIntegrable (μ := volume) e (1 - e))
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) e (1 - e))
    (hc.intervalIntegrable (μ := volume) (1 - e) (1 + e))
  have hsub : (∫ v in (-e)..e, (dens α v - dens α (v + 1))) =
      (∫ v in (-e)..e, dens α v) - ∫ v in (-e)..e, dens α (v + 1) :=
    intervalIntegral.integral_sub (hc.intervalIntegrable (-e) e) (hc1.intervalIntegrable (-e) e)
  rw [h0, h1, hsub, hshift]
  linarith

theorem dens_sub_shift_nonneg {α v : ℝ} (hα : 0 ≤ α) (hv : -1 / 2 ≤ v) :
    0 ≤ dens α v - dens α (v + 1) := by
  have h := dens_le_of_sq_le hα (v := v) (w := v + 1) (by nlinarith)
  linarith

/-- Step 3 (pointwise): for `v ≥ -¼`, `φ(v+1) ≤ e^{-πα²/2} φ(v)`. -/
theorem dens_shift_le {α v : ℝ} (hα : 0 ≤ α) (hv : -1 / 4 ≤ v) :
    dens α (v + 1) ≤ Real.exp (-(Real.pi * α ^ 2 / 2)) * dens α v := by
  unfold dens
  rw [mul_left_comm, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hα
  apply Real.exp_le_exp.mpr
  have hA : 0 ≤ Real.pi * α ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 2 * v + 1 by linarith) hA
  have h2 : Real.pi * α ^ 2 * (v + 1) ^ 2 =
      Real.pi * α ^ 2 * v ^ 2 + Real.pi * α ^ 2 * (2 * v + 1) := by ring
  linarith

/-- Step 2: for `0 ≤ e₀ ≤ e ≤ ½`, `∫_{-e₀}^{e₀} (φ(v) - φ(v+1)) ≤ ∫_{-e}^{e} (φ(v) - φ(v+1))`. -/
theorem integral_gap_mono {α e₀ e : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ e₀) (h01 : e₀ ≤ e)
    (he : e ≤ 1 / 2) :
    (∫ v in (-e₀)..e₀, (dens α v - dens α (v + 1))) ≤
      ∫ v in (-e)..e, (dens α v - dens α (v + 1)) := by
  have hc := continuous_dens α
  have hgc : Continuous (fun v => dens α v - dens α (v + 1)) :=
    hc.sub (hc.comp (continuous_add_const 1))
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hgc.intervalIntegrable (μ := volume) (-e) (-e₀))
    (hgc.intervalIntegrable (μ := volume) (-e₀) e₀)
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hgc.intervalIntegrable (μ := volume) (-e) e₀)
    (hgc.intervalIntegrable (μ := volume) e₀ e)
  have hL : 0 ≤ ∫ v in (-e)..(-e₀), (dens α v - dens α (v + 1)) :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun v hv => dens_sub_shift_nonneg hα (by linarith [hv.1]))
  have hR : 0 ≤ ∫ v in e₀..e, (dens α v - dens α (v + 1)) :=
    intervalIntegral.integral_nonneg h01
      (fun v hv => dens_sub_shift_nonneg hα (by linarith [hv.1]))
  linarith

theorem integral_dens_sym (α e : ℝ) :
    (∫ v in (-e)..e, dens α v) = 2 * ∫ v in (0 : ℝ)..e, dens α v := by
  have hc := continuous_dens α
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-e) 0) (hc.intervalIntegrable (μ := volume) 0 e)
  have hneg : (∫ v in (-e)..0, dens α v) = ∫ v in (0 : ℝ)..e, dens α v := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := e) (dens α)
    simp only [dens_neg, neg_zero] at h
    exact h.symm
  linarith

/-- Step 4 (concavity of `s ↦ ∫_0^s φ`): for `0 ≤ s ≤ S`, `s ∫_0^S φ ≤ S ∫_0^s φ`. -/
theorem integral_dens_concave {α s S : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hsS : s ≤ S) :
    s * ∫ v in (0 : ℝ)..S, dens α v ≤ S * ∫ v in (0 : ℝ)..s, dens α v := by
  have hc := continuous_dens α
  have hk1 : IntervalIntegrable (fun _ : ℝ => dens α s) volume 0 s :=
    continuous_const.intervalIntegrable _ _
  have hk2 : IntervalIntegrable (fun _ : ℝ => dens α s) volume s S :=
    continuous_const.intervalIntegrable _ _
  have ha : s * dens α s ≤ ∫ v in (0 : ℝ)..s, dens α v := by
    have h := intervalIntegral.integral_mono_on hs hk1 (hc.intervalIntegrable 0 s)
      (fun v hv => dens_le_of_sq_le hα (by nlinarith [hv.1, hv.2]) :
        ∀ v ∈ Set.Icc (0 : ℝ) s, dens α s ≤ dens α v)
    simpa using h
  have hb : (∫ v in s..S, dens α v) ≤ (S - s) * dens α s := by
    have h := intervalIntegral.integral_mono_on hsS (hc.intervalIntegrable s S) hk2
      (fun v hv => dens_le_of_sq_le hα (by nlinarith [hv.1, hv.2]) :
        ∀ v ∈ Set.Icc s S, dens α v ≤ dens α s)
    simpa using h
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 s) (hc.intervalIntegrable (μ := volume) s S)
  have h1 := mul_le_mul_of_nonneg_left hb hs
  have h2 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hsS)
  rw [← hadj]
  nlinarith

/-- `∫_0^{1/4} φ = ½ erf(√π α/4)` (substitution `t = √π α v`). -/
theorem integral_dens_quarter_eq {α : ℝ} (hα : 0 < α) :
    (∫ v in (0 : ℝ)..(1 / 4), dens α v) = (1 / 2) * IntMul.realErfScaled α (1 / 4) := by
  have hpi := Real.pi_pos
  have hsq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hc : 0 < Real.sqrt Real.pi * α := mul_pos hsq hα
  have h1 : ∀ v : ℝ, dens α v = α * Real.exp (-((Real.sqrt Real.pi * α * v) ^ 2)) := by
    intro v
    unfold dens
    rw [mul_pow, mul_pow, Real.sq_sqrt hpi.le]
  have h2 := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / 4)
    (fun t : ℝ => Real.exp (-(t ^ 2))) hc.ne'
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, h2]
  unfold IntMul.realErfScaled IntMul.realErf
  rw [mul_zero, smul_eq_mul]
  generalize (∫ t in (0 : ℝ)..Real.sqrt Real.pi * α * (1 / 4), Real.exp (-(t ^ 2))) = I
  field_simp

/-- Step 5: `∫_0^{1/4} φ ≥ ½(1 - e^{-πα²/16}/(πα/4))`. -/
theorem integral_dens_quarter_ge {α : ℝ} (hα : 0 < α) :
    (1 / 2) * (1 - Real.exp (-(Real.pi * α ^ 2 * (1 / 4) ^ 2)) / (Real.pi * α * (1 / 4))) ≤
      ∫ v in (0 : ℝ)..(1 / 4), dens α v := by
  rw [integral_dens_quarter_eq hα]
  have h := IntMul.erfcScaled_realErfScaled_le_gaussian_tail α (1 / 4) hα (by norm_num)
  unfold IntMul.erfcScaled at h
  linarith

theorem exp_neg_le_one_div {X c : ℝ} (hc : 0 < c) (hX : Real.log c ≤ X) :
    Real.exp (-X) ≤ 1 / c := by
  rw [Real.exp_neg, one_div]
  apply inv_anti₀ hc
  calc c = Real.exp (Real.log c) := (Real.exp_log hc).symm
    _ ≤ Real.exp X := Real.exp_le_exp.mpr hX

/-- Admissibility (lower end) with `ω ≥ 8` gives `α > 0` and `πα² ≥ 32 ln 2`. -/
theorem alpha_facts {ω : ℕ} (hω : 8 ≤ ω) {α : ℝ} (hα : AlphaAdmissible ω α) :
    0 < α ∧ 32 * Real.log 2 ≤ Real.pi * α ^ 2 := by
  obtain ⟨hlo, -⟩ := hα
  have hω' : (8 : ℝ) ≤ (ω : ℝ) := by exact_mod_cast hω
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  have harg : 0 < (ω : ℝ) * Real.log 2 / Real.pi := by positivity
  have hs := Real.sqrt_pos.mpr harg
  have hsq := Real.sq_sqrt harg.le
  refine ⟨by linarith, ?_⟩
  have h2 : 4 * ((ω : ℝ) * Real.log 2 / Real.pi) ≤ α ^ 2 := by
    have := mul_le_mul hlo hlo (by positivity) (by linarith)
    nlinarith
  have h3 : Real.pi * (4 * ((ω : ℝ) * Real.log 2 / Real.pi)) = 4 * (ω : ℝ) * Real.log 2 := by
    field_simp
  calc 32 * Real.log 2 ≤ 4 * (ω : ℝ) * Real.log 2 := by nlinarith
    _ = Real.pi * (4 * ((ω : ℝ) * Real.log 2 / Real.pi)) := h3.symm
    _ ≤ Real.pi * α ^ 2 := mul_le_mul_of_nonneg_left h2 hpi.le

/-- Core separation bound: if `πα² ≥ 32 ln 2`, `t ≥ 2` and `1/(2t) ≤ e ≤ ½`, then
`G(½-e) - G(½-e-1) ≥ 7/(4t)`. -/
theorem sep_core {α t e : ℝ} (hα : 0 < α) (hA : 32 * Real.log 2 ≤ Real.pi * α ^ 2)
    (ht : 2 ≤ t) (he0 : 1 / (2 * t) ≤ e) (he1 : e ≤ 1 / 2) :
    7 / (4 * t) ≤ kernelG α (1 / 2 - e) - kernelG α (1 / 2 - e - 1) := by
  rw [kernelG_sub_eq]
  have ht0 : 0 < t := by linarith
  have he₀pos : 0 < 1 / (2 * t) := by positivity
  have he₀q : 1 / (2 * t) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h74 : 7 / (4 * t) = 7 / 2 * (1 / (2 * t)) := by field_simp; ring
  rw [h74]
  generalize 1 / (2 * t) = e₀ at he₀pos he₀q he0 ⊢
  have hmono := integral_gap_mono hα.le he₀pos.le he0 he1
  have hc := continuous_dens α
  have hκint : (∫ v in (-e₀)..e₀, (1 - Real.exp (-(Real.pi * α ^ 2 / 2))) * dens α v) ≤
      ∫ v in (-e₀)..e₀, (dens α v - dens α (v + 1)) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuous_const.mul hc).intervalIntegrable _ _
    · exact (hc.sub (hc.comp (continuous_add_const 1))).intervalIntegrable _ _
    · intro v hv
      have := dens_shift_le hα.le (v := v) (by linarith [hv.1])
      linarith
  rw [intervalIntegral.integral_const_mul, integral_dens_sym] at hκint
  have hconc := integral_dens_concave hα.le he₀pos.le he₀q
  have hI := integral_dens_quarter_ge hα
  have hlog2 := Real.log_two_gt_d9
  have hpi4 := Real.pi_gt_d4
  have hpi := Real.pi_pos
  have hE : Real.exp (-(Real.pi * α ^ 2 * (1 / 4) ^ 2)) ≤ 1 / 4 := by
    apply exp_neg_le_one_div (by norm_num)
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; nlinarith
  have hκle : Real.exp (-(Real.pi * α ^ 2 / 2)) ≤ 1 / 256 := by
    apply exp_neg_le_one_div (by norm_num)
    have : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    rw [this]; nlinarith
  have hP : 2.085 ≤ Real.pi * α * (1 / 4) := by
    have hPpos : 0 < Real.pi * α * (1 / 4) := by positivity
    have hP2 : (Real.pi * α * (1 / 4)) ^ 2 = Real.pi * (Real.pi * α ^ 2) / 16 := by ring
    have h1 : Real.pi * (32 * Real.log 2) ≤ Real.pi * (Real.pi * α ^ 2) :=
      mul_le_mul_of_nonneg_left hA hpi.le
    have h2 : (3.1415 : ℝ) * (32 * 0.6931471803) ≤ Real.pi * (32 * Real.log 2) :=
      mul_le_mul hpi4.le (by linarith) (by norm_num) hpi.le
    nlinarith
  have hEP : Real.exp (-(Real.pi * α ^ 2 * (1 / 4) ^ 2)) / (Real.pi * α * (1 / 4)) ≤ 0.12 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hI1 : 0.44 ≤ ∫ v in (0 : ℝ)..(1 / 4), dens α v := by linarith
  have hI0 : 1.76 * e₀ ≤ ∫ v in (0 : ℝ)..e₀, dens α v := by
    have := mul_le_mul_of_nonneg_left hI1 he₀pos.le
    linarith
  have hκ0 : 0 ≤ Real.exp (-(Real.pi * α ^ 2 / 2)) := (Real.exp_pos _).le
  have h1κ : 0 ≤ 1 - Real.exp (-(Real.pi * α ^ 2 / 2)) := by linarith
  have hfin := mul_le_mul_of_nonneg_left hI0 h1κ
  have hκe := mul_le_mul_of_nonneg_right hκle he₀pos.le
  nlinarith

end LemmaBSep

open LemmaBSep in
/-- **Lemma 4.4 (bridge Lemma B)(iv)** (`lem:bridge-B`): for `ω ≥ 8`, admissible `α`, `t ≥ 2` a
power of two and every digit `u < t`, with `y = (u+½)/t`, `|G(y) - G(y-1)| ≥ 7/(4t)`.
Unconditional: proved from the integral definition of `kernelG` and the IntMul Gaussian tail
bound; only the lower end of `AlphaAdmissible` is used. -/
theorem lemmaB_iv : LemmaB_ivStmt := by
  intro ω hω α hα t ht u hu
  obtain ⟨hα0, hA⟩ := alpha_facts hω hα
  obtain ⟨ht2, k, hk⟩ := ht
  have heven : 2 ∣ t := by
    rcases k with _ | k
    · simp at hk; omega
    · exact ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
  obtain ⟨m, hm⟩ := heven
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
  have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
  have huR : (u : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hu
  set y : ℝ := ((u : ℝ) + 1 / 2) / (t : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one ht0]; linarith
  rcases Nat.lt_or_ge (2 * u + 1) t with h | h
  · -- `y < ½`; parity of `t` gives `2u + 2 ≤ t`, i.e. `½ - y ≥ 1/(2t)`.
    have h2 : 2 * u + 2 ≤ t := by omega
    have h2R : 2 * (u : ℝ) + 2 ≤ (t : ℝ) := by exact_mod_cast h2
    have he0 : 1 / (2 * (t : ℝ)) ≤ 1 / 2 - y := by
      rw [hy, show (1 : ℝ) / 2 - ((u : ℝ) + 1 / 2) / t = ((t : ℝ) - 2 * u - 1) / (2 * t) by
        field_simp; ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have he1 : 1 / 2 - y ≤ 1 / 2 := by linarith
    have key := sep_core hα0 hA htR he0 he1
    rw [show (1 : ℝ) / 2 - (1 / 2 - y) = y by ring] at key
    exact key.trans (le_abs_self _)
  · -- `y > ½`; parity gives `t ≤ 2u`, i.e. `y - ½ ≥ 1/(2t)`; reduce to the first case by evenness.
    have h2 : t ≤ 2 * u := by omega
    have h2R : (t : ℝ) ≤ 2 * (u : ℝ) := by exact_mod_cast h2
    have he0 : 1 / (2 * (t : ℝ)) ≤ y - 1 / 2 := by
      rw [hy, show ((u : ℝ) + 1 / 2) / t - 1 / 2 = (2 * (u : ℝ) + 1 - t) / (2 * t) by
        field_simp]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have he1 : y - 1 / 2 ≤ 1 / 2 := by linarith
    have key := sep_core hα0 hA htR he0 he1
    have e1 : kernelG α (1 / 2 - (y - 1 / 2)) = kernelG α (y - 1) := by
      rw [show (1 : ℝ) / 2 - (y - 1 / 2) = -(y - 1) by ring, kernelG_neg']
    have e2 : kernelG α (1 / 2 - (y - 1 / 2) - 1) = kernelG α y := by
      rw [show (1 : ℝ) / 2 - (y - 1 / 2) - 1 = -y by ring, kernelG_neg']
    rw [e1, e2] at key
    rw [abs_sub_comm]
    exact key.trans (le_abs_self _)

end SubNLogN.Math.Bridge
