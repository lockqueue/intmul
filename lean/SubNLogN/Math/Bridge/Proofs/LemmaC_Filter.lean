import SubNLogN.Math.Bridge.LemmaC_Filter

/-!
# Proofs: Lemma 4.6 (`lem:bridge-C`)(i), filter norms and the spatial tail (`LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability)

* `lemmaC_i_tail : LemmaC_i_tailStmt` (unconditional). Proof: `‖g_h(s)‖ = |sinc(s)| e^{-πs²/α²}`
  and `|sinc s| ≤ 1/(π|s|)` (IntMul `abs_sincGaussian_le`). From `α² = 4λ_G ω ln2/π`,
  `λ_G ≤ 4`, `ω ≤ P` and `16 (ln 2)² < π²` we get `ln 2 · α² ≤ π P`, hence for `|s| ≥ P + k`
  (`k : ℕ`) `π s²/α² ≥ (P + k) ln 2` and `‖g_h(s)‖ ≤ 2^{-P} 2^{-k}/(πP)`. The samples with
  `e ≥ P+1` have `|e + δ| ≥ P + (e - P - 1)`, those with `e ≤ -(P+1)` have
  `|e + δ| > P + (-e - P - 1)`, so each side is dominated by a geometric series of sum
  `2·2^{-P}/(πP)`; the total is `≤ 4·2^{-P}/(πP) < 0.10·2^{-P}` for `P ≥ 20`. (A geometric
  majorant replaces the paper's sum-vs-integral comparison; the constant is weaker than the
  paper's `0.06` but meets the stated `0.10`.)
* `lemmaC_i_norms_of` (conditional on the Kernel contracts `Carrier_poissonStmt`,
  `HasSum_kernelG_shiftStmt`, `KernelG_posStmt`): the unnormalized DFT of one period of `H_δ`
  at frequency `u` is `∑_{n∈ℤ} g_h(n+δ) e(-nu/t)`, which by Poisson is
  `∑_m G((u+½)/t - m) e(δ(u/t - m))`, of modulus `≤ ∑_m G(·-m) = 1`; Parseval on `Fin t`
  (via `IntMul.stdChar_orthogonality_range`) gives `‖H_δ‖₂ ≤ 1`, and Cauchy–Schwarz
  `‖H_δ‖₁ ≤ √t`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

/-! ## The spatial tail -/

namespace LemmaCFilterProof

/-- The carrier phase has modulus one: `‖g_h(s)‖ = |sinc(s) e^{-πs²/α²}|`. -/
theorem norm_carrier_eq (α : ℝ) (t : ℕ) (s : ℝ) :
    ‖carrier α t s‖ = |IntMul.sincGaussian α s| := by
  unfold carrier
  rw [norm_mul, IntMul.norm_stdChar, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The exponent inequality behind the tail (proof of Lemma 4.6 (`lem:bridge-C`)(i)): under Lemma 4.6 (bridge Lemma C)'s
hypotheses, `ln 2 · α² ≤ π P` (i.e. `α √(P ln 2/π) ≤ P`). -/
theorem log_two_mul_alpha_sq_le {P ω : ℕ} {α : ℝ} (hC : LemmaCParams P ω α) :
    Real.log 2 * α ^ 2 ≤ Real.pi * P := by
  obtain ⟨_hP20, _hω8, hωP, _hα, lamG, _hl1, hl4, hα2⟩ := hC
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hl4' : (lamG : ℝ) ≤ 4 := by exact_mod_cast hl4
  have hωP' : (ω : ℝ) ≤ P := by exact_mod_cast hωP
  have hω0 : (0 : ℝ) ≤ ω := Nat.cast_nonneg ω
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  rw [hα2, mul_div_assoc', div_le_iff₀ Real.pi_pos]
  have hlw : (lamG : ℝ) * ω ≤ 4 * P := by
    nlinarith [mul_le_mul_of_nonneg_right hl4' hω0]
  have h1 : Real.log 2 * (4 * (lamG : ℝ) * ω * Real.log 2) ≤ 16 * Real.log 2 ^ 2 * P := by
    have := mul_le_mul_of_nonneg_left hlw (sq_nonneg (Real.log 2))
    nlinarith
  have hl2 : Real.log 2 ^ 2 < 0.49 := by nlinarith
  have hp2 : 9 < Real.pi * Real.pi := by nlinarith
  have h2 : 16 * Real.log 2 ^ 2 ≤ Real.pi * Real.pi := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hP0
  nlinarith

/-- Pointwise geometric tail bound: if `ln 2 · α² ≤ π P`, `P > 0` and `|s| ≥ P + k`, then
`‖g_h(s)‖ ≤ (1/(πP)) · 2^{-P} · 2^{-k}`. -/
theorem norm_carrier_le_geom {α : ℝ} (hα : 0 < α) (t P k : ℕ) (hP : 0 < P)
    (hkey : Real.log 2 * α ^ 2 ≤ Real.pi * P) {s : ℝ} (hs : (P : ℝ) + k ≤ |s|) :
    ‖carrier α t s‖ ≤ 1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * ((1 : ℝ) / 2) ^ k) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsP : (P : ℝ) ≤ |s| := by linarith
  have habs0 : 0 < |s| := lt_of_lt_of_le hP0 hsP
  have hs0 : s ≠ 0 := abs_pos.mp habs0
  have hpi := Real.pi_pos
  rw [norm_carrier_eq]
  refine (IntMul.abs_sincGaussian_le α s hs0).trans ?_
  apply mul_le_mul
  · exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hsP hpi.le)
  · have hexp : (2 ^ P : ℝ)⁻¹ * ((1 : ℝ) / 2) ^ k =
        Real.exp (-(((P : ℝ) + k) * Real.log 2)) := by
      rw [show -(((P : ℝ) + k) * Real.log 2) =
          -((P : ℝ) * Real.log 2) + -((k : ℝ) * Real.log 2) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div_pow, one_div]
    rw [hexp, Real.exp_le_exp]
    have hα2 : 0 < α ^ 2 := by positivity
    have hss : ((P : ℝ) + k) ^ 2 ≤ s ^ 2 := by
      rw [← sq_abs s]
      exact pow_le_pow_left₀ (by positivity) hs 2
    have h4 : ((P : ℝ) + k) * Real.log 2 * α ^ 2 ≤ Real.pi * s ^ 2 := by
      calc ((P : ℝ) + k) * Real.log 2 * α ^ 2 = ((P : ℝ) + k) * (Real.log 2 * α ^ 2) := by ring
        _ ≤ ((P : ℝ) + k) * (Real.pi * P) := mul_le_mul_of_nonneg_left hkey (by positivity)
        _ ≤ Real.pi * ((P : ℝ) + k) ^ 2 := by
          nlinarith [mul_nonneg (mul_nonneg hpi.le (add_nonneg hP0.le hk0)) hk0]
        _ ≤ Real.pi * s ^ 2 := mul_le_mul_of_nonneg_left hss hpi.le
    have h3 : ((P : ℝ) + k) * Real.log 2 ≤ Real.pi / α ^ 2 * s ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hα2]
      exact h4
    have h5 : -(Real.pi / α ^ 2) * s ^ 2 = -(Real.pi / α ^ 2 * s ^ 2) := by ring
    rw [h5]
    exact neg_le_neg h3
  · exact (Real.exp_pos _).le
  · positivity

end LemmaCFilterProof

open LemmaCFilterProof

/-- **Lemma 4.6 (bridge Lemma C)(i), spatial tail** (`lem:bridge-C`):
`∑_{|e|>P} |g_h(e+δ)| < 0.10·2^{-P}`. We prove the bound `4·2^{-P}/(πP)` (geometric majorant
on each side) and then use `P ≥ 20`, `π > 3`. -/
theorem lemmaC_i_tail : LemmaC_i_tailStmt := by
  intro P ω α hC t _ht δ hδ
  have hkey := log_two_mul_alpha_sq_le hC
  obtain ⟨hP20, -, -, hα, -⟩ := hC
  have hP : 0 < P := by omega
  set f : ℤ → ℝ := fun e => if (P : ℤ) < |e| then ‖carrier α t ((e : ℝ) + δ)‖ else 0
    with hf_def
  have hf0 : ∀ e, 0 ≤ f e := fun e => by
    simp only [hf_def]
    split_ifs <;> positivity
  -- the geometric majorant `n ↦ (1/(πP)) 2^{-P} 2^{-n}`
  have hgeo : Summable (fun n : ℕ => 1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * ((1 : ℝ) / 2) ^ n)) :=
    (summable_geometric_two.mul_left _).mul_left _
  have hgeo_sum : ∑' n : ℕ, 1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * ((1 : ℝ) / 2) ^ n) =
      1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * 2) := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_two]
  -- positive side: `e = n + (P+1)`
  have hpos_le : ∀ n : ℕ, f ((n + (P + 1) : ℕ) : ℤ) ≤
      1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * ((1 : ℝ) / 2) ^ n) := by
    intro n
    have hcond : (P : ℤ) < |((n + (P + 1) : ℕ) : ℤ)| := by
      rw [abs_of_nonneg (by positivity)]
      omega
    simp only [hf_def]
    rw [if_pos hcond]
    apply norm_carrier_le_geom hα t P n hP hkey
    have h1 : (((n + (P + 1) : ℕ) : ℤ) : ℝ) = (n : ℝ) + P + 1 := by push_cast; ring
    rw [h1]
    calc (P : ℝ) + n ≤ (n : ℝ) + P + 1 + δ := by linarith [hδ.1]
      _ ≤ |(n : ℝ) + P + 1 + δ| := le_abs_self _
  have hpos_zero : ∀ i ∈ Finset.range (P + 1), f (i : ℤ) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcond : ¬ (P : ℤ) < |(i : ℤ)| := by
      rw [abs_of_nonneg (by positivity)]
      omega
    simp only [hf_def]
    rw [if_neg hcond]
  have hs1 : Summable (fun n : ℕ => f ((n + (P + 1) : ℕ) : ℤ)) :=
    Summable.of_nonneg_of_le (fun n => hf0 _) hpos_le hgeo
  have hs1' : Summable (fun n : ℕ => f (n : ℤ)) :=
    (summable_nat_add_iff (f := fun n : ℕ => f (n : ℤ)) (P + 1)).mp hs1
  have hS1 : ∑' n : ℕ, f (n : ℤ) ≤ 1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * 2) := by
    rw [← hs1'.sum_add_tsum_nat_add (P + 1), Finset.sum_eq_zero hpos_zero, zero_add,
      ← hgeo_sum]
    exact Summable.tsum_le_tsum hpos_le hs1 hgeo
  -- negative side: `e = -((n + P) + 1)`
  have hneg_le : ∀ n : ℕ, f (-(((n + P : ℕ) : ℤ) + 1)) ≤
      1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * ((1 : ℝ) / 2) ^ n) := by
    intro n
    have hcond : (P : ℤ) < |(-(((n + P : ℕ) : ℤ) + 1))| := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      omega
    simp only [hf_def]
    rw [if_pos hcond]
    apply norm_carrier_le_geom hα t P n hP hkey
    have h1 : ((-(((n + P : ℕ) : ℤ) + 1) : ℤ) : ℝ) = -((n : ℝ) + P + 1) := by push_cast; ring
    rw [h1]
    calc (P : ℝ) + n ≤ -(-((n : ℝ) + P + 1) + δ) := by linarith [hδ.2]
      _ ≤ |-((n : ℝ) + P + 1) + δ| := neg_le_abs _
  have hneg_zero : ∀ i ∈ Finset.range P, f (-((i : ℤ) + 1)) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcond : ¬ (P : ℤ) < |(-((i : ℤ) + 1))| := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      omega
    simp only [hf_def]
    rw [if_neg hcond]
  have hs2 : Summable (fun n : ℕ => f (-(((n + P : ℕ) : ℤ) + 1))) :=
    Summable.of_nonneg_of_le (fun n => hf0 _) hneg_le hgeo
  have hs2' : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    (summable_nat_add_iff (f := fun n : ℕ => f (-((n : ℤ) + 1))) P).mp hs2
  have hS2 : ∑' n : ℕ, f (-((n : ℤ) + 1)) ≤ 1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * 2) := by
    rw [← hs2'.sum_add_tsum_nat_add P, Finset.sum_eq_zero hneg_zero, zero_add, ← hgeo_sum]
    exact Summable.tsum_le_tsum hneg_le hs2 hgeo
  -- assemble
  have htot : ∑' e : ℤ, f e ≤
      1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * 2) + 1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * 2) := by
    rw [tsum_of_nat_of_neg_add_one hs1' hs2']
    exact add_le_add hS1 hS2
  have hX : (2 : ℝ) ^ (-(P : ℤ)) = (2 ^ P : ℝ)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hXpos : 0 < (2 ^ P : ℝ)⁻¹ := by positivity
  have hc : 1 / (Real.pi * P) < 0.025 := by
    rw [div_lt_iff₀ (by positivity)]
    have h20 : (20 : ℝ) ≤ P := by exact_mod_cast hP20
    nlinarith [mul_le_mul (le_of_lt Real.pi_gt_three) h20 (by norm_num) Real.pi_pos.le]
  rw [hX]
  have hcX := mul_lt_mul_of_pos_right hc hXpos
  calc ∑' e : ℤ, f e ≤
      1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * 2) + 1 / (Real.pi * P) * ((2 ^ P : ℝ)⁻¹ * 2) := htot
    _ < 0.10 * (2 ^ P : ℝ)⁻¹ := by nlinarith

/-! ## Filter norms: Parseval on `Fin t` -/

namespace LemmaCFilterProof

/-- Complex conjugation of the standard character: `conj e(x) = e(-x)`. -/
theorem conj_stdChar (x : ℝ) : (starRingEnd ℂ) (IntMul.stdChar x) = IntMul.stdChar (-x) := by
  unfold IntMul.stdChar
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Discrete orthogonality on `Fin t` (from `IntMul.stdChar_orthogonality_range`):
`∑_{u<t} e(-eu/t) e(e'u/t) = t·[e = e']`. -/
theorem stdChar_orth_fin (t : ℕ) (ht : 0 < t) (e e' : Fin t) :
    ∑ u ∈ Finset.range t, IntMul.stdChar (-(((e : ℕ) : ℝ) * (u : ℝ) / (t : ℝ))) *
      IntMul.stdChar (((e' : ℕ) : ℝ) * (u : ℝ) / (t : ℝ)) = if e = e' then (t : ℂ) else 0 := by
  have h := IntMul.stdChar_orthogonality_range t ht e e' e.isLt e'.isLt
  have hif : (if e = e' then (t : ℂ) else 0) = if (e : ℕ) = (e' : ℕ) then (t : ℂ) else 0 := by
    by_cases hee : e = e'
    · rw [if_pos hee, if_pos (congrArg Fin.val hee)]
    · rw [if_neg hee, if_neg (fun h' => hee (Fin.ext h'))]
  rw [hif, ← h]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  congr 1
  · congr 1
    ring
  · congr 1
    push_cast
    ring

/-- Abstract Parseval: if the kernel `χ` is orthogonal on `range t` with norm `t`, then
`∑_{u<t} |∑_e y_e χ_e(u)|² = t ∑_e |y_e|²`. -/
theorem parseval_of_orth {t : ℕ} (y : Fin t → ℂ) (χ : Fin t → ℕ → ℂ)
    (horth : ∀ e e' : Fin t, ∑ u ∈ Finset.range t, χ e u * (starRingEnd ℂ) (χ e' u) =
      if e = e' then (t : ℂ) else 0) :
    ∑ u ∈ Finset.range t, ‖∑ e : Fin t, y e * χ e u‖ ^ 2 =
      (t : ℝ) * ∑ e : Fin t, ‖y e‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hsq : ∀ u : ℕ, ((‖∑ e : Fin t, y e * χ e u‖ ^ 2 : ℝ) : ℂ) =
      ∑ e : Fin t, ∑ e' : Fin t,
        y e * (starRingEnd ℂ) (y e') * (χ e u * (starRingEnd ℂ) (χ e' u)) := by
    intro u
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun e' _ => ?_))
    rw [map_mul]
    ring
  rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun u _ => hsq u), Finset.sum_comm]
  have key : ∀ e : Fin t, ∑ u ∈ Finset.range t, ∑ e' : Fin t,
      y e * (starRingEnd ℂ) (y e') * (χ e u * (starRingEnd ℂ) (χ e' u)) =
      (t : ℂ) * ((‖y e‖ ^ 2 : ℝ) : ℂ) := by
    intro e
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, horth]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.mul_conj', Complex.ofReal_pow]
    ring
  rw [Finset.sum_congr rfl (fun e _ => key e), ← Finset.mul_sum]
  push_cast
  try ring

/-- Parseval for the unnormalized DFT `X(u) = ∑_e y_e e(-eu/t)` on `Fin t`:
`∑_{u<t} |X(u)|² = t ∑_e |y_e|²`. -/
theorem sum_norm_sq_dft (t : ℕ) (ht : 0 < t) (y : Fin t → ℂ) :
    ∑ u ∈ Finset.range t,
        ‖∑ e : Fin t, y e * IntMul.stdChar (-(((e : ℕ) : ℝ) * (u : ℝ) / (t : ℝ)))‖ ^ 2 =
      (t : ℝ) * ∑ e : Fin t, ‖y e‖ ^ 2 := by
  refine parseval_of_orth y (fun e u => IntMul.stdChar (-(((e : ℕ) : ℝ) * (u : ℝ) / (t : ℝ))))
    (fun e e' => ?_)
  simp only [conj_stdChar, neg_neg]
  exact stdChar_orth_fin t ht e e'

/-! ## Filter norms: the DFT of one period -/

/-- Splitting a summable `ℤ`-series into the residue classes `e + tℤ`, `e ∈ Fin t`. -/
theorem tsum_int_eq_sum_fin_tsum {t : ℕ} [NeZero t] (F : ℤ → ℂ) (hF : Summable F) :
    ∑' n : ℤ, F n = ∑ e : Fin t, ∑' m : ℤ, F (m * (t : ℤ) + ((e : ℕ) : ℤ)) := by
  let E : ℤ ≃ Fin t × ℤ := (Int.divModEquiv t).trans (Equiv.prodComm _ _)
  have h1 : HasSum (fun p : Fin t × ℤ => F (p.2 * (t : ℤ) + ((p.1 : ℕ) : ℤ))) (∑' n, F n) :=
    (E.symm.hasSum_iff (f := F)).mpr hF.hasSum
  have h2 : ∀ e : Fin t, HasSum (fun m : ℤ => F (m * (t : ℤ) + ((e : ℕ) : ℤ)))
      (∑' m : ℤ, F (m * (t : ℤ) + ((e : ℕ) : ℤ))) :=
    fun e => (h1.summable.prod_factor e).hasSum
  exact (h1.prod_fiberwise h2).unique (hasSum_fintype _)

/-- The phase `e(-nu/t)` only depends on `n mod t`. -/
theorem stdChar_fold (t : ℕ) (ht : 0 < t) (m : ℤ) (e u : ℕ) :
    IntMul.stdChar (-((((m * (t : ℤ) + (e : ℤ) : ℤ)) : ℝ) * (u : ℝ) / (t : ℝ))) =
      IntMul.stdChar (-((e : ℝ) * (u : ℝ) / (t : ℝ))) := by
  have ht' : (t : ℝ) ≠ 0 := by positivity
  rw [show -((((m * (t : ℤ) + (e : ℤ) : ℤ)) : ℝ) * (u : ℝ) / (t : ℝ)) =
      -((e : ℝ) * (u : ℝ) / (t : ℝ)) + ((-(m * (u : ℤ)) : ℤ) : ℝ) by
    push_cast
    field_simp
    ring]
  exact IntMul.stdChar_add_int _ _

/-- Lemma 4.6 (bridge Lemma C)(i) proof, first step (`lem:bridge-C`): given the Kernel contracts,
every unnormalized DFT coefficient `∑_{e<t} H_δ(e) e(-eu/t)` of one period of the folded filter
has modulus at most one. It equals `∑_m G((u+½)/t - m) e(δ(u/t - m))` with `G > 0`,
`∑_m G(· - m) = 1`. -/
theorem norm_dft_foldedFilter_le (hP : Carrier_poissonStmt) (hS : HasSum_kernelG_shiftStmt)
    (hpos : KernelG_posStmt) {α : ℝ} (hα : 0 < α) {t : ℕ} (ht : 0 < t) (δ : ℝ) (u : ℕ) :
    ‖∑ e : Fin t, foldedFilter α t δ ((e : ℕ) : ℤ) *
        IntMul.stdChar (-(((e : ℕ) : ℝ) * (u : ℝ) / (t : ℝ)))‖ ≤ 1 := by
  have : NeZero t := ⟨ht.ne'⟩
  set F : ℤ → ℂ := fun n =>
    carrier α t ((n : ℝ) + δ) * IntMul.stdChar (-((n : ℝ) * (u : ℝ) / (t : ℝ))) with hF
  -- summability of the samples (Gaussian decay, IntMul)
  have hsumm : Summable (fun n : ℤ => ‖F n‖) := by
    have h0 := IntMul.summable_norm_sincGaussian_modulated α (-δ) 0 hα
    refine h0.congr (fun n => ?_)
    have e1 : (-δ) - (n : ℝ) = -((n : ℝ) + δ) := by ring
    simp only [hF, zero_mul, IntMul.stdChar_zero, mul_one, norm_mul, IntMul.norm_stdChar, e1,
      IntMul.sincGaussian_even, norm_carrier_eq, Complex.norm_real, Real.norm_eq_abs]
  have hFs : Summable F := hsumm.of_norm
  -- unfold the period and recombine the residue classes
  have h1 : ∑ e : Fin t, foldedFilter α t δ ((e : ℕ) : ℤ) *
        IntMul.stdChar (-(((e : ℕ) : ℝ) * (u : ℝ) / (t : ℝ))) = ∑' n : ℤ, F n := by
    rw [tsum_int_eq_sum_fin_tsum (t := t) F hFs]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    unfold foldedFilter
    rw [← tsum_mul_right]
    refine tsum_congr (fun m => ?_)
    simp only [hF]
    congr 1
    · congr 1
      push_cast
      ring
    · exact (stdChar_fold t ht m e u).symm
  -- reindex `n = -k` to match the Poisson contract
  have h2 : ∑' n : ℤ, F n =
      ∑' k : ℤ, carrier α t (δ - (k : ℝ)) * IntMul.stdChar ((k : ℝ) * ((u : ℝ) / (t : ℝ))) := by
    rw [← (Equiv.neg ℤ).tsum_eq F]
    refine tsum_congr (fun k => ?_)
    simp only [hF, Equiv.neg_apply]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [h1, h2, hP α hα t ht δ ((u : ℝ) / (t : ℝ))]
  -- the alias weights are positive and sum to one
  have hG : HasSum (fun m : ℤ => kernelG α ((u : ℝ) / (t : ℝ) - (m : ℝ) + 1 / (2 * (t : ℝ)))) 1 := by
    have h := hS α hα ((u : ℝ) / (t : ℝ) + 1 / (2 * (t : ℝ)))
    have hfun : (fun m : ℤ => kernelG α ((u : ℝ) / (t : ℝ) + 1 / (2 * (t : ℝ)) - (m : ℝ))) =
        (fun m : ℤ => kernelG α ((u : ℝ) / (t : ℝ) - (m : ℝ) + 1 / (2 * (t : ℝ)))) := by
      funext m
      congr 1
      ring
    rwa [hfun] at h
  have hnorm : ∀ m : ℤ, ‖(kernelG α ((u : ℝ) / (t : ℝ) - (m : ℝ) + 1 / (2 * (t : ℝ))) : ℂ) *
      IntMul.stdChar (δ * ((u : ℝ) / (t : ℝ) - (m : ℝ)))‖ =
        kernelG α ((u : ℝ) / (t : ℝ) - (m : ℝ) + 1 / (2 * (t : ℝ))) := by
    intro m
    rw [norm_mul, IntMul.norm_stdChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hpos α hα _)]
  have hsum_n : Summable (fun m : ℤ =>
      ‖(kernelG α ((u : ℝ) / (t : ℝ) - (m : ℝ) + 1 / (2 * (t : ℝ))) : ℂ) *
        IntMul.stdChar (δ * ((u : ℝ) / (t : ℝ) - (m : ℝ)))‖) := by
    simp_rw [hnorm]
    exact hG.summable
  refine (norm_tsum_le_tsum_norm hsum_n).trans (le_of_eq ?_)
  simp_rw [hnorm]
  exact hG.tsum_eq

end LemmaCFilterProof

/-- **Lemma 4.6 (bridge Lemma C)(i), filter norms** (`lem:bridge-C`), conditional on the
Kernel contracts (Poisson summation for the carrier, the partition of unity `∑_m G(ξ-m) = 1`,
and `G > 0`): over one period, `‖H_δ‖₂ ≤ 1` and `‖H_δ‖₁ ≤ √t`. (Only `α > 0` and `t > 0` are
used from the hypotheses.) -/
theorem lemmaC_i_norms_of (hP : Carrier_poissonStmt) (hS : HasSum_kernelG_shiftStmt)
    (hpos : KernelG_posStmt) : LemmaC_i_normsStmt := by
  intro P ω α hC t ht δ _hδ
  have hα : 0 < α := hC.2.2.2.1
  have ht0 : 0 < t := by omega
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht0
  have hpars := sum_norm_sq_dft t ht0 (fun e : Fin t => foldedFilter α t δ ((e : ℕ) : ℤ))
  have hdft : ∀ u ∈ Finset.range t,
      ‖∑ e : Fin t, foldedFilter α t δ ((e : ℕ) : ℤ) *
        IntMul.stdChar (-(((e : ℕ) : ℝ) * (u : ℝ) / (t : ℝ)))‖ ^ 2 ≤ 1 :=
    fun u _ => pow_le_one₀ (norm_nonneg _) (norm_dft_foldedFilter_le hP hS hpos hα ht0 δ u)
  have hsum_le : (t : ℝ) * ∑ e : Fin t, ‖foldedFilter α t δ ((e : ℕ) : ℤ)‖ ^ 2 ≤ t := by
    rw [← hpars]
    calc _ ≤ ∑ u ∈ Finset.range t, (1 : ℝ) := Finset.sum_le_sum hdft
      _ = t := by simp
  have hl2sq : ∑ e : Fin t, ‖foldedFilter α t δ ((e : ℕ) : ℤ)‖ ^ 2 ≤ 1 := by
    nlinarith
  refine ⟨?_, ?_⟩
  · unfold l2Norm
    calc Real.sqrt (∑ e : Fin t, ‖foldedFilter α t δ ((e : ℕ) : ℤ)‖ ^ 2)
        ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hl2sq
      _ = 1 := Real.sqrt_one
  · unfold l1Norm
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin t)))
      (f := fun e : Fin t => ‖foldedFilter α t δ ((e : ℕ) : ℤ)‖)
    rw [Finset.card_univ, Fintype.card_fin] at hcs
    apply Real.le_sqrt_of_sq_le
    nlinarith

end SubNLogN.Math.Bridge
