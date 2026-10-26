import SubNLogN.Math.Bridge.Kernel

/-!
# Bridge: proofs of the kernel `G` / carrier / folded-filter contracts

Proofs of the `…Stmt` contracts of `SubNLogN/Math/Bridge/Kernel.lean` (Definition 4.1 (`def:carrier`),
eq. (`eq:poisson`), and Lemma 4.4 (`lem:bridge-B`)). Everything is reduced to the IntMul development:

* `kernelG_eq_gHatBox`: substitution `t = √π α v` in `G(ξ) = ∫_{ξ-1/2}^{ξ+1/2} α e^{-πα²v²} dv`
  and `IntMul.theorem3_concrete_box_gaussian_integral_and_telescoping`.
* `fourier_sincGaussian_eq_kernelG`: `IntMul.fourier_sincGaussian_eq_gHatBox` + the above.
* `kernelG_pos`, `kernelG_neg` (reflection `v ↦ -v`), `kernelG_strictAntiOn` (shift `v ↦ v + 1`
  and `e^{-πα²v²} > e^{-πα²(v+1)²}` for `v > -1/2`).
* `hasSum_kernelG_shift`: summability (`IntMul.summable_gHatBox_realErfScaled`), the telescoping
  partial sums over `[-N, N]` (`IntMul.theorem3_gHatBox_telescoping_sum`) and `erf(±∞) = ±1`
  (proved here from `integral_gaussian_Ioi`).
* `fourier_carrier`: the modulation `e(-s/(2t))` shifts the frequency (pointwise in the integrand).
* `carrier_poisson`: `IntMul.sincGaussian_modulated_poisson_summation` at `ξ + 1/(2t)`.
* `foldedFilter_negacyclic`: `e(-m/2) = (-1)^m` and `tsum_mul_left`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators FourierTransform
open Filter Topology MeasureTheory

/-! ## Part 1: closed form, Fourier transform, positivity, evenness -/

/-- `G(ξ) = ½[erf(a(ξ+½)) - erf(a(ξ-½))]`, `a = √π α` (eq. (`eq:G`)). -/
theorem kernelG_eq_gHatBox : KernelG_eq_gHatBoxStmt := by
  intro α ξ hα
  rw [(IntMul.theorem3_concrete_box_gaussian_integral_and_telescoping α ξ 0).1]
  unfold kernelG
  have hsqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hc0 : Real.sqrt Real.pi * α ≠ 0 := (mul_pos hsqrt_pos hα).ne'
  have hfun : (fun v : ℝ => α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2))) =
      fun v : ℝ => α * (fun t : ℝ => Real.exp (-(t ^ 2))) (Real.sqrt Real.pi * α * v) := by
    funext v
    simp only
    congr 3
    rw [mul_pow, mul_pow, hsq]
  have hsub := intervalIntegral.integral_comp_mul_left (a := ξ - 1 / 2) (b := ξ + 1 / 2)
    (fun t : ℝ => Real.exp (-(t ^ 2))) hc0
  rw [hfun, intervalIntegral.integral_const_mul, hsub, smul_eq_mul]
  field_simp

/-- `𝓕[sinc(s) e^{-πs²/α²}](ξ) = G(ξ)` (Definition 4.1 (`def:carrier`), eq. (`eq:G`)). -/
theorem fourier_sincGaussian_eq_kernelG : Fourier_sincGaussian_eq_kernelGStmt := by
  intro α ξ hα
  rw [IntMul.fourier_sincGaussian_eq_gHatBox α ξ hα, kernelG_eq_gHatBox α ξ hα]

/-- `G(ξ) > 0` for `α > 0`. -/
theorem kernelG_pos : KernelG_posStmt := by
  intro α hα ξ
  rw [kernelG_eq_gHatBox α ξ hα]
  exact IntMul.gHatBox_realErfScaled_pos α ξ hα

/-- `G` is even (for every real `α`; reflection `v ↦ -v` of the integration interval). -/
theorem kernelG_neg : KernelG_negStmt := by
  intro α ξ
  unfold kernelG
  have h := intervalIntegral.integral_comp_neg (a := ξ - 1 / 2) (b := ξ + 1 / 2)
    (fun v : ℝ => α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2)))
  simp only [neg_sq] at h
  rw [h]
  congr 1 <;> ring

/-! ## Part 2: `erf(±∞) = ±1` and the tiling identity `∑_m G(ξ - m) = 1` -/

namespace KernelProof

/-- `realErf z → 1` as `z → +∞` (from `∫_0^∞ e^{-t²} dt = √π/2`). -/
theorem tendsto_realErf_atTop : Tendsto IntMul.realErf atTop (𝓝 1) := by
  have hint : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq one_pos
  have hgauss : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
    simpa only [neg_one_mul, div_one] using integral_gaussian_Ioi 1
  have ht0 := (intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint.integrableOn
    tendsto_id).const_mul (2 / Real.sqrt Real.pi)
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h1 : 2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / 2) = 1 := by field_simp
  rw [hgauss, h1] at ht0
  exact ht0

/-- `realErf z → -1` as `z → -∞` (oddness). -/
theorem tendsto_realErf_atBot : Tendsto IntMul.realErf atBot (𝓝 (-1)) := by
  have h := (tendsto_realErf_atTop.comp tendsto_neg_atBot_atTop).neg
  have hfun : (fun x : ℝ => -(IntMul.realErf ∘ fun y : ℝ => -y) x) = IntMul.realErf := by
    funext x
    simp [IntMul.realErf_neg]
  rw [hfun] at h
  exact h

/-- `erf(√π α z) → 1` as `z → +∞` for `α > 0`. -/
theorem tendsto_realErfScaled_atTop (α : ℝ) (hα : 0 < α) :
    Tendsto (IntMul.realErfScaled α) atTop (𝓝 1) := by
  have hc : 0 < Real.sqrt Real.pi * α := mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hα
  exact tendsto_realErf_atTop.comp (tendsto_id.const_mul_atTop hc)

/-- `erf(√π α z) → -1` as `z → -∞` for `α > 0`. -/
theorem tendsto_realErfScaled_atBot (α : ℝ) (hα : 0 < α) :
    Tendsto (IntMul.realErfScaled α) atBot (𝓝 (-1)) := by
  have hc : 0 < Real.sqrt Real.pi * α := mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hα
  exact tendsto_realErf_atBot.comp (tendsto_id.const_mul_atBot hc)

end KernelProof

open KernelProof

/-- The intervals `[ξ-m-½, ξ-m+½]` tile `ℝ`: `∑_{m∈ℤ} G(ξ - m) = 1` (Lemma 4.4 (`lem:bridge-B`)(i)). -/
theorem hasSum_kernelG_shift : HasSum_kernelG_shiftStmt := by
  intro α hα ξ
  have hfun : (fun m : ℤ => kernelG α (ξ - m)) =
      fun m : ℤ => IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ)) := by
    funext m
    exact kernelG_eq_gHatBox α _ hα
  rw [hfun]
  have hS : Summable (fun m : ℤ => IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ))) :=
    IntMul.summable_gHatBox_realErfScaled α ξ hα
  have hpart : ∀ N : ℕ,
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ)) =
        (1 / 2 : ℝ) * (IntMul.realErfScaled α (ξ + (N : ℝ) + 1 / 2) -
          IntMul.realErfScaled α (ξ - (N : ℝ) - 1 / 2)) := by
    intro N
    rw [IntMul.theorem3_gHatBox_telescoping_sum (IntMul.realErfScaled α) ξ (-(N : ℤ)) (N : ℤ)
      (by omega)]
    push_cast
    ring_nf
  have hup : Tendsto (fun N : ℕ => IntMul.realErfScaled α (ξ + (N : ℝ) + 1 / 2)) atTop (𝓝 1) := by
    refine (tendsto_realErfScaled_atTop α hα).comp ?_
    exact tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have hdown : Tendsto (fun N : ℕ => IntMul.realErfScaled α (ξ - (N : ℝ) - 1 / 2)) atTop
      (𝓝 (-1)) := by
    refine (tendsto_realErfScaled_atBot α hα).comp ?_
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) + (1 / 2 - ξ)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => -((N : ℝ) + (1 / 2 - ξ))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h1
    refine h2.congr fun N => ?_
    show -((N : ℝ) + (1 / 2 - ξ)) = ξ - (N : ℝ) - 1 / 2
    ring
  have hlim : Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ))) atTop (𝓝 1) := by
    simp_rw [hpart]
    have h3 := (hup.sub hdown).const_mul (1 / 2 : ℝ)
    have h4 : (1 / 2 : ℝ) * (1 - -1) = 1 := by norm_num
    rw [h4] at h3
    exact h3
  have hT : Tendsto (fun s : Finset ℤ => ∑ m ∈ s,
      IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ))) atTop
      (𝓝 (∑' m : ℤ, IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ)))) := hS.hasSum
  have hlim' := hT.comp Finset.tendsto_Icc_neg
  rw [← tendsto_nhds_unique hlim' hlim]
  exact hS.hasSum

/-- `G` is strictly decreasing on `[0, ∞)` (Lemma 4.4 (`lem:bridge-B`)(iii)): for `0 ≤ x < y`,
`G(x) - G(y) = ∫_{x-1/2}^{y-1/2} (f(v) - f(v+1)) dv > 0`, `f(v) = α e^{-πα²v²}`. -/
theorem kernelG_strictAntiOn : KernelG_strictAntiOnStmt := by
  intro α hα x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  let f : ℝ → ℝ := fun v => α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2))
  have hcont : Continuous f := by fun_prop
  have hG : ∀ ξ, kernelG α ξ = ∫ v in (ξ - 1 / 2)..(ξ + 1 / 2), f v := fun ξ => rfl
  rw [hG, hG]
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hcont.intervalIntegrable a b
  have hcont1 : Continuous fun v => f (v + 1) := hcont.comp (continuous_id.add continuous_const)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hii (x - 1 / 2) (y - 1 / 2))
    (hii (y - 1 / 2) (x + 1 / 2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hii (y - 1 / 2) (x + 1 / 2))
    (hii (x + 1 / 2) (y + 1 / 2))
  have h3 : (∫ v in (x + 1 / 2)..(y + 1 / 2), f v) =
      ∫ v in (x - 1 / 2)..(y - 1 / 2), f (v + 1) := by
    rw [intervalIntegral.integral_comp_add_right f 1]
    congr 1 <;> ring
  have h4 : (∫ v in (x - 1 / 2)..(y - 1 / 2), (f v - f (v + 1))) =
      (∫ v in (x - 1 / 2)..(y - 1 / 2), f v) - ∫ v in (x - 1 / 2)..(y - 1 / 2), f (v + 1) :=
    intervalIntegral.integral_sub (hii _ _) (hcont1.intervalIntegrable _ _)
  have h5 : 0 < ∫ v in (x - 1 / 2)..(y - 1 / 2), (f v - f (v + 1)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hcont.sub hcont1).intervalIntegrable _ _) (fun v hv => ?_) (by linarith)
    have hv1 : x - 1 / 2 < v := hv.1
    have hpa : 0 < Real.pi * α ^ 2 := by positivity
    have hsq : v ^ 2 < (v + 1) ^ 2 := by nlinarith
    have hlt : -(Real.pi * α ^ 2 * (v + 1) ^ 2) < -(Real.pi * α ^ 2 * v ^ 2) := by nlinarith
    have hexp := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hlt) hα
    show 0 < α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2)) -
      α * Real.exp (-(Real.pi * α ^ 2 * (v + 1) ^ 2))
    linarith
  linarith

/-! ## Part 3: the negative half-bin carrier and its folded filter -/

/-- `ĝ_h(ξ) = G(ξ + 1/(2t_h))` (eq. (`eq:carrier`)): the modulation `e(-s/(2t))` shifts the
frequency; proved pointwise on the Fourier integrands (no integrability needed). -/
theorem fourier_carrier : Fourier_carrierStmt := by
  intro α hα t _ht ξ
  rw [← fourier_sincGaussian_eq_kernelG α _ hα, IntMul.fourier_eq_integral_stdChar,
    IntMul.fourier_eq_integral_stdChar]
  congr 1
  funext s
  unfold carrier
  rw [← mul_assoc, ← IntMul.stdChar_add]
  congr 2
  ring

/-- Poisson summation for the carrier (eq. (`eq:poisson`) in Lemma 4.2 (`lem:bridge-A`), specialized to `g_h`):
`IntMul.sincGaussian_modulated_poisson_summation` at frequency `ξ + 1/(2t)`. -/
theorem carrier_poisson : Carrier_poissonStmt := by
  intro α hα t _ht z ξ
  have hL : ∀ e : ℤ, carrier α t (z - (e : ℝ)) * IntMul.stdChar ((e : ℝ) * ξ) =
      IntMul.stdChar (-(z * (1 / (2 * (t : ℝ))))) *
        ((IntMul.sincGaussian α (z - (e : ℝ)) : ℂ) *
          IntMul.stdChar ((ξ + 1 / (2 * (t : ℝ))) * (e : ℝ))) := by
    intro e
    have hph : IntMul.stdChar (-((z - (e : ℝ)) / (2 * (t : ℝ)))) * IntMul.stdChar ((e : ℝ) * ξ) =
        IntMul.stdChar (-(z * (1 / (2 * (t : ℝ))))) *
          IntMul.stdChar ((ξ + 1 / (2 * (t : ℝ))) * (e : ℝ)) := by
      rw [← IntMul.stdChar_add, ← IntMul.stdChar_add]
      congr 1
      ring
    unfold carrier
    calc IntMul.stdChar (-((z - (e : ℝ)) / (2 * (t : ℝ)))) *
          (IntMul.sincGaussian α (z - (e : ℝ)) : ℂ) * IntMul.stdChar ((e : ℝ) * ξ)
        = (IntMul.stdChar (-((z - (e : ℝ)) / (2 * (t : ℝ)))) * IntMul.stdChar ((e : ℝ) * ξ)) *
            (IntMul.sincGaussian α (z - (e : ℝ)) : ℂ) := by ring
      _ = _ := by rw [hph]; ring
  rw [tsum_congr hL, tsum_mul_left,
    IntMul.sincGaussian_modulated_poisson_summation α z (ξ + 1 / (2 * (t : ℝ))) hα,
    ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [kernelG_eq_gHatBox α _ hα]
  have h1 : ξ + 1 / (2 * (t : ℝ)) - (m : ℝ) = ξ - (m : ℝ) + 1 / (2 * (t : ℝ)) := by ring
  have h2 : IntMul.stdChar (-(z * (1 / (2 * (t : ℝ))))) *
      IntMul.stdChar ((ξ - (m : ℝ) + 1 / (2 * (t : ℝ))) * z) =
        IntMul.stdChar (z * (ξ - (m : ℝ))) := by
    rw [← IntMul.stdChar_add]
    congr 1
    ring
  rw [h1]
  calc IntMul.stdChar (-(z * (1 / (2 * (t : ℝ))))) *
        ((IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ) + 1 / (2 * (t : ℝ))) : ℂ) *
          IntMul.stdChar ((ξ - (m : ℝ) + 1 / (2 * (t : ℝ))) * z))
      = (IntMul.gHatBox (IntMul.realErfScaled α) (ξ - (m : ℝ) + 1 / (2 * (t : ℝ))) : ℂ) *
          (IntMul.stdChar (-(z * (1 / (2 * (t : ℝ))))) *
            IntMul.stdChar ((ξ - (m : ℝ) + 1 / (2 * (t : ℝ))) * z)) := by ring
    _ = _ := by rw [h2]

namespace KernelProof

/-- `e(-m/2) = e^{-πim} = (-1)^m` for `m ∈ ℤ`. -/
theorem stdChar_neg_int_div_two (m : ℤ) : IntMul.stdChar (-((m : ℝ) / 2)) = (-1 : ℂ) ^ m := by
  unfold IntMul.stdChar
  have h : (((2 * Real.pi * (-((m : ℝ) / 2)) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (-((Real.pi : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

end KernelProof

/-- Negacyclic form of the folded filter (Section 4.1, eq. (`eq:negacyclic`)): for
`s = e + m t`, `e^{-πi(s+δ)/t} = (-1)^m e^{-πi(e+δ)/t}`. -/
theorem foldedFilter_negacyclic : FoldedFilter_negacyclicStmt := by
  intro α _hα t ht δ e
  unfold foldedFilter
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  unfold carrier
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have h2 : (m : ℝ) * (t : ℝ) / (2 * (t : ℝ)) = (m : ℝ) / 2 := mul_div_mul_right _ _ ht'
  have h1 : -(((e : ℝ) + (m : ℝ) * (t : ℝ) + δ) / (2 * (t : ℝ))) =
      -(((e : ℝ) + δ) / (2 * (t : ℝ))) + -((m : ℝ) / 2) := by
    rw [← h2]
    ring
  rw [h1, IntMul.stdChar_add, stdChar_neg_int_div_two]
  ring

end SubNLogN.Math.Bridge
