import Mathlib
import SubNLogN.Math.Cost.AsymBands

/-!
# Cost: Lemma 7.1, row-dependent growth statements of the paper family (part 3 of `Asymptotics`)

Paper: Lemma 7.1 (`lem:root-family`, Section 7.1 (`sec:main-alg`)), with the uses in Section 7.3 (`sec:main-tables`, setup eq. (`eq:setup`) is
`o(RP)`, `R/r ≥ r/2`), Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`) (cutoff: `Δ ≤ k/2`, setup `≤ RP`) and Remark A.12 (`rem:walsh-delta`) (`Δ = o(P)`):
`d = Θ(P^ε)`, `ℓ = Θ(P^{1-ε})`, `K = Θ(P^{εc})`, `dK = o(P)`, `K = o(ℓ)`, `K/log P → ∞`,
`r/P^j → ∞`, `(R/r)/P^j → ∞`, `R/r ≥ r/2`, the guard `2Δ ≤ k` and `Δ = o(P)` when `εC₁ < 1`, and the
setup bound `C_set((R/r)P^D + rP^D + P^D) ≤ RP`.

Theorems tagged CONTRACT are the contract statements; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

open Filter Asymptotics Topology

variable {ρ : RowExps}

/-! ### Auxiliary facts (private) -/

namespace AsymGrowthAux

/-- `x^a = o(x^b)` at `+∞` for real exponents `a < b`. -/
private theorem isLittleO_rpow_rpow {a b : ℝ} (hab : a < b) :
    (fun x : ℝ => x ^ a) =o[atTop] (fun x : ℝ => x ^ b) := by
  rw [isLittleO_iff_tendsto']
  · refine (tendsto_rpow_neg_atTop (sub_pos.2 hab)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_sub hx, neg_sub]
  · filter_upwards [eventually_gt_atTop 0] with x hx h
    exact absurd h (Real.rpow_pos_of_pos hx b).ne'

/-- `P^a = o(P^b)` along `n → ∞` for real exponents `a < b`. -/
private theorem isLittleO_POf_rpow {a b : ℝ} (hab : a < b) :
    (fun n => (POf n : ℝ) ^ a) =o[atTop] (fun n => (POf n : ℝ) ^ b) :=
  (isLittleO_rpow_rpow hab).comp_tendsto AsymBandsAux.tendsto_POf_real

/-- `k^s = o(k)` along `n → ∞` for a real exponent `s < 1`. -/
private theorem isLittleO_kOf_rpow {s : ℝ} (hs : s < 1) :
    (fun n => (kOf n : ℝ) ^ s) =o[atTop] (fun n => (kOf n : ℝ)) := by
  have h := (isLittleO_rpow_rpow hs).comp_tendsto AsymBandsAux.tendsto_kOf_real
  simpa only [Function.comp_def, Real.rpow_one] using h

/-- `x^s / log x → ∞` at `+∞` for `s > 0` (from `log = o(x^s)`). -/
private theorem tendsto_rpow_div_log {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => x ^ s / Real.log x) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  have hM : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [(isLittleO_log_rpow_atTop hs).def (inv_pos.2 hM), eventually_gt_atTop 1]
    with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos (by linarith) s
  rw [Real.norm_of_nonneg hlog.le, Real.norm_of_nonneg hxs.le] at hx
  rw [le_div_iff₀ hlog]
  have h1 : M * Real.log x ≤ max M 1 * Real.log x :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hlog.le
  have h2 : max M 1 * Real.log x ≤ max M 1 * ((max M 1)⁻¹ * x ^ s) :=
    mul_le_mul_of_nonneg_left hx hM.le
  have h3 : max M 1 * ((max M 1)⁻¹ * x ^ s) = x ^ s := by
    rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]
  linarith

/-- `x / k^j / 32^j ≤ x / P^j` when `x ≥ 0` and `0 < P ≤ 32k`. -/
private theorem div_pow_le_div_pow {x k P : ℝ} (j : ℕ) (hx : 0 ≤ x) (hP : 0 < P)
    (hPk : P ≤ 32 * k) : x / k ^ j / 32 ^ j ≤ x / P ^ j := by
  rw [div_div, ← mul_pow]
  exact div_le_div_of_nonneg_left hx (pow_pos hP j) (pow_le_pow_left₀ hP.le (by linarith) j)

/-- Transfer of `f(k)/k^j → ∞` (as `k → ∞`) to `f(kOf n)/P^j → ∞` (as `n → ∞`), using
eventually `P ≤ 32k`. -/
private theorem tendsto_div_POf_pow {f : ℕ → ℕ} (j : ℕ)
    (hf : Tendsto (fun k => (f k : ℝ) / (k : ℝ) ^ j) atTop atTop) :
    Tendsto (fun n => (f (kOf n) : ℝ) / (POf n : ℝ) ^ j) atTop atTop := by
  have h := (hf.comp tendsto_kOf).atTop_div_const (by positivity : (0 : ℝ) < 32 ^ j)
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [AsymBandsAux.eventually_POf_band] with n ⟨_, hPk⟩
  have hPk' : (POf n : ℝ) ≤ 32 * (kOf n : ℝ) := by exact_mod_cast hPk
  exact div_pow_le_div_pow j (Nat.cast_nonneg _) (AsymBandsAux.POf_pos_real n) hPk'

/-- `εC₁ < 1` from `e₁C₁ < e₂`. -/
private theorem eps_mul_lt_one {ρ : RowExps} {C₁ : ℕ} (hC₁ : ρ.e₁ * C₁ < ρ.e₂) :
    ρ.eps * C₁ < 1 := by
  have he₂ : (0 : ℝ) < ρ.e₂ := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hC₁
  have h : ((ρ.e₁ * C₁ : ℕ) : ℝ) < ρ.e₂ := by exact_mod_cast hC₁
  push_cast at h
  unfold RowExps.eps
  rw [div_mul_eq_mul_div, div_lt_one he₂]
  exact h

/-- The guard is at most `C₀ k^{εC₁}`: `Δ = C₀ d^{C₁}` and `d ≤ k^ε`. -/
private theorem guard_le_rpow (hρ : ρ.Admissible) (C₀ C₁ n : ℕ) :
    (guardOf C₀ C₁ ρ n : ℝ) ≤ C₀ * (kOf n : ℝ) ^ (ρ.eps * C₁) := by
  have hk0 : (0 : ℝ) ≤ kOf n := Nat.cast_nonneg _
  have hd := AsymBandsAux.dOf_le_rpow hρ n
  have h : (guardOf C₀ C₁ ρ n : ℝ) = C₀ * (dOf ρ n : ℝ) ^ C₁ := by
    simp only [guardOf, Nat.cast_mul, Nat.cast_pow]
  rw [h, Real.rpow_mul hk0, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hd C₁) (Nat.cast_nonneg _)

end AsymGrowthAux

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`d = Θ(P^ε)`"). -/
theorem isTheta_dOf (hρ : ρ.Admissible) :
    (fun n => (dOf ρ n : ℝ)) =Θ[atTop] (fun n => (POf n : ℝ) ^ ρ.eps) := by
  -- The bands at `P` (`eventually_bands_P`): `¼P^ε ≤ d ≤ P^ε`.
  have hB := eventually_bands_P hρ
  refine ⟨IsBigO.of_bound 1 ?_, IsBigO.of_bound 4 ?_⟩
  · filter_upwards [hB] with n ⟨_, h2, _⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    linarith
  · filter_upwards [hB] with n ⟨h1, _⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    linarith

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`ℓ = Θ(P^{1-ε})`"). -/
theorem isTheta_lOf (hρ : ρ.Admissible) :
    (fun n => (lOf ρ n : ℝ)) =Θ[atTop] (fun n => (POf n : ℝ) ^ (1 - ρ.eps)) := by
  -- From the bands at `P` (`P/(128d) ≤ ℓ ≤ P/(8d)`, `¼P^ε ≤ d ≤ P^ε`) and `P^{1-ε} P^ε = P`:
  -- eventually `P^{1-ε} ≤ 128ℓ` and `ℓ ≤ P^{1-ε}`.
  have key : ∀ᶠ n in atTop, (POf n : ℝ) ^ (1 - ρ.eps) ≤ 128 * lOf ρ n ∧
      (lOf ρ n : ℝ) ≤ (POf n : ℝ) ^ (1 - ρ.eps) := by
    filter_upwards [eventually_bands_P hρ] with n ⟨h1, h2, h3, h4, _, _⟩
    have hP := AsymBandsAux.POf_pos_real n
    have hPe : 0 < (POf n : ℝ) ^ ρ.eps := Real.rpow_pos_of_pos hP _
    have hd : (0 : ℝ) < dOf ρ n := by linarith
    have hl0 : (0 : ℝ) ≤ lOf ρ n := Nat.cast_nonneg _
    have hsplit : (POf n : ℝ) ^ (1 - ρ.eps) * (POf n : ℝ) ^ ρ.eps = POf n := by
      rw [← Real.rpow_add hP, sub_add_cancel, Real.rpow_one]
    have h3' : (POf n : ℝ) ≤ lOf ρ n * (128 * dOf ρ n) :=
      (div_le_iff₀ (mul_pos (by norm_num) hd)).1 h3
    have h4' : (lOf ρ n : ℝ) * (8 * dOf ρ n) ≤ POf n :=
      (le_div_iff₀ (mul_pos (by norm_num) hd)).1 h4
    constructor
    · have hlow : (POf n : ℝ) ^ (1 - ρ.eps) * (POf n : ℝ) ^ ρ.eps
          ≤ 128 * lOf ρ n * (POf n : ℝ) ^ ρ.eps := by
        calc (POf n : ℝ) ^ (1 - ρ.eps) * (POf n : ℝ) ^ ρ.eps = POf n := hsplit
          _ ≤ lOf ρ n * (128 * dOf ρ n) := h3'
          _ ≤ lOf ρ n * (128 * (POf n : ℝ) ^ ρ.eps) :=
            mul_le_mul_of_nonneg_left (by linarith) hl0
          _ = 128 * lOf ρ n * (POf n : ℝ) ^ ρ.eps := by ring
      exact le_of_mul_le_mul_right hlow hPe
    · have hup : (lOf ρ n : ℝ) * (POf n : ℝ) ^ ρ.eps
          ≤ (POf n : ℝ) ^ (1 - ρ.eps) * (POf n : ℝ) ^ ρ.eps := by
        calc (lOf ρ n : ℝ) * (POf n : ℝ) ^ ρ.eps ≤ lOf ρ n * (8 * dOf ρ n) :=
              mul_le_mul_of_nonneg_left (by linarith) hl0
          _ ≤ POf n := h4'
          _ = (POf n : ℝ) ^ (1 - ρ.eps) * (POf n : ℝ) ^ ρ.eps := hsplit.symm
      exact le_of_mul_le_mul_right hup hPe
  refine ⟨IsBigO.of_bound 1 ?_, IsBigO.of_bound 128 ?_⟩
  · filter_upwards [key] with n ⟨_, h⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    linarith
  · filter_upwards [key] with n ⟨h, _⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    linarith

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`K = Θ(P^{εc})`"). -/
theorem isTheta_KOf (hρ : ρ.Admissible) :
    (fun n => (KOf ρ n : ℝ)) =Θ[atTop] (fun n => (POf n : ℝ) ^ (ρ.eps * ρ.c)) := by
  -- `⅛P^{εc} ≤ K ≤ P^{εc}` eventually (`eventually_KOf_bounds`).
  have hK := eventually_KOf_bounds hρ
  refine ⟨IsBigO.of_bound 1 ?_, IsBigO.of_bound 8 ?_⟩
  · filter_upwards [hK] with n ⟨_, h2⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    linarith
  · filter_upwards [hK] with n ⟨h1, _⟩
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    linarith

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`dK = o(P)`"). -/
theorem isLittleO_dK_P (hρ : ρ.Admissible) :
    (fun n => (dOf ρ n : ℝ) * KOf ρ n) =o[atTop] (fun n => (POf n : ℝ)) := by
  -- Eventually `dK ≤ P^ε · P^{εc} = P^{ε(1+c)}` (bands at `P`, `eventually_KOf_bounds`), and
  -- `ε(1+c) ≤ 2ε < 1`.
  obtain ⟨he0, he1, -, hc1⟩ := AsymBandsAux.admissible_real hρ
  have hlt : ρ.eps * (1 + ρ.c) < 1 := by nlinarith [mul_le_mul_of_nonneg_left hc1 he0.le]
  have hO : (fun n => (dOf ρ n : ℝ) * KOf ρ n) =O[atTop]
      (fun n => (POf n : ℝ) ^ (ρ.eps * (1 + ρ.c))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_bands_P hρ, eventually_KOf_bounds hρ] with n ⟨_, h2, _⟩ ⟨_, hK2⟩
    have hP := AsymBandsAux.POf_pos_real n
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Real.norm_of_nonneg (Real.rpow_nonneg hP.le _), one_mul, mul_add, mul_one,
      Real.rpow_add hP]
    exact mul_le_mul h2 hK2 (Nat.cast_nonneg _) (Real.rpow_nonneg hP.le _)
  have ho : (fun n => (POf n : ℝ) ^ (ρ.eps * (1 + ρ.c))) =o[atTop] (fun n => (POf n : ℝ)) := by
    have h := AsymGrowthAux.isLittleO_POf_rpow hlt
    simpa only [Real.rpow_one] using h
  exact hO.trans_isLittleO ho

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`K = o(ℓ)`"). -/
theorem isLittleO_K_l (hρ : ρ.Admissible) :
    (fun n => (KOf ρ n : ℝ)) =o[atTop] (fun n => (lOf ρ n : ℝ)) := by
  -- `K = Θ(P^{εc})`, `ℓ = Θ(P^{1-ε})` and `εc ≤ ε < 1 - ε`.
  obtain ⟨he0, he1, -, hc1⟩ := AsymBandsAux.admissible_real hρ
  have hlt : ρ.eps * ρ.c < 1 - ρ.eps := by nlinarith [mul_le_mul_of_nonneg_left hc1 he0.le]
  exact (isTheta_KOf hρ).isBigO.trans_isLittleO
    ((AsymGrowthAux.isLittleO_POf_rpow hlt).trans_isBigO (isTheta_lOf hρ).symm.isBigO)

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`K/log P → ∞`"). -/
theorem tendsto_K_div_log (hρ : ρ.Admissible) :
    Tendsto (fun n => (KOf ρ n : ℝ) / Real.log (POf n)) atTop atTop := by
  -- Eventually `K ≥ ⅛P^{εc}`, and `P^{εc}/log P → ∞` (`εc > 0`, `P → ∞`).
  obtain ⟨he0, -, hc0, -⟩ := AsymBandsAux.admissible_real hρ
  have hlim : Tendsto (fun n => (1 / 8 : ℝ) * ((POf n : ℝ) ^ (ρ.eps * ρ.c) / Real.log (POf n)))
      atTop atTop :=
    ((AsymGrowthAux.tendsto_rpow_div_log (mul_pos he0 hc0)).comp
      AsymBandsAux.tendsto_POf_real).const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_KOf_bounds hρ] with n ⟨hK, _⟩
  have hlog : 0 < Real.log (POf n) := Real.log_pos (AsymBandsAux.one_lt_POf_real n)
  show (1 / 8 : ℝ) * ((POf n : ℝ) ^ (ρ.eps * ρ.c) / Real.log (POf n))
    ≤ (KOf ρ n : ℝ) / Real.log (POf n)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hK hlog.le

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`r/P^j → ∞` for every fixed `j`"). -/
theorem tendsto_r_div_pow (hρ : ρ.Admissible) (j : ℕ) :
    Tendsto (fun n => (rOf ρ n : ℝ) / (POf n : ℝ) ^ j) atTop atTop := by
  -- `rOf ρ n = rK ρ (kOf n)` definitionally; `tendsto_rK_div_pow` and eventually `P ≤ 32k`.
  exact AsymGrowthAux.tendsto_div_POf_pow (f := rK ρ) j (tendsto_rK_div_pow hρ j)

/-- CONTRACT (Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`), "`R/r ≥ 4CP^{D_set+1}`" for large `k`): `(R/r)/P^j → ∞` for every
fixed `j` (`R/r = 2^{k-ℓ}` exactly). -/
theorem tendsto_R_div_r_div_pow (hρ : ρ.Admissible) (j : ℕ) :
    Tendsto (fun n => ((ROf n / rOf ρ n : ℕ) : ℝ) / (POf n : ℝ) ^ j) atTop atTop := by
  -- `ROf n / rOf ρ n = 2^k / rK ρ k` at `k = kOf n` definitionally; `tendsto_R_div_rK_div_pow`
  -- and eventually `P ≤ 32k`.
  exact AsymGrowthAux.tendsto_div_POf_pow (f := fun k => 2 ^ k / rK ρ k) j
    (tendsto_R_div_rK_div_pow hρ j)

/-- CONTRACT (Section 7.3 (`sec:main-tables`), eq. (`eq:setup`), "`R/r ≥ r/2`"): eventually `r/2 ≤ R/r`. -/
theorem eventually_r_div_two_le (hρ : ρ.Admissible) :
    ∀ᶠ n in atTop, rOf ρ n / 2 ≤ ROf n / rOf ρ n := by
  -- With `d ≥ 2`, `ℓ = m + 1 ≥ 1` and `dℓ < k + d` (`d_mul_l_spec`): `2m ≤ dm < k`, so
  -- `r/2 = 2^m ≤ 2^{k-(m+1)} = R/r`.
  filter_upwards [(tendsto_dOf hρ).eventually_ge_atTop 2, eventually_two_le_lOf hρ] with n hd hl
  obtain ⟨-, h2⟩ := d_mul_l_spec ρ n (by omega)
  obtain ⟨m, hm⟩ : ∃ m, lOf ρ n = m + 1 := ⟨lOf ρ n - 1, by omega⟩
  rw [hm, Nat.mul_add_one] at h2
  have h4 : 2 * m ≤ dOf ρ n * m := Nat.mul_le_mul_right m hd
  have hR : 2 ^ kOf n / 2 ^ (m + 1) = 2 ^ (kOf n - (m + 1)) := Nat.pow_div (by omega) (by norm_num)
  have hr : 2 ^ (m + 1) / 2 = 2 ^ m := by
    rw [pow_succ]
    exact Nat.mul_div_cancel _ (by norm_num)
  show 2 ^ lOf ρ n / 2 ≤ 2 ^ kOf n / 2 ^ lOf ρ n
  rw [hm, hR, hr]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- CONTRACT (Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`), "the guard term gives `Δ ≤ C₀k^{εC₁} + 1 ≤ k/2`"): for an integer constant
`C₀` and `εC₁ < 1` (i.e. `e₁C₁ < e₂`), eventually `2Δ ≤ k`. -/
theorem eventually_guard_le (hρ : ρ.Admissible) (C₀ C₁ : ℕ) (hC₁ : ρ.e₁ * C₁ < ρ.e₂) :
    ∀ᶠ n in atTop, 2 * guardOf C₀ C₁ ρ n ≤ kOf n := by
  -- `Δ ≤ C₀k^{εC₁}` (`d ≤ k^ε`) and `k^{εC₁} = o(k)` (`εC₁ < 1`): eventually `k^{εC₁} ≤ ck` with
  -- `2C₀c ≤ 1`, so `2Δ ≤ 2C₀ck ≤ k`.
  have hs := AsymGrowthAux.eps_mul_lt_one hC₁
  have hC : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
  obtain ⟨c, hc0, hc1⟩ : ∃ c : ℝ, 0 < c ∧ 2 * C₀ * c ≤ 1 := by
    refine ⟨1 / (2 * C₀ + 1), by positivity, ?_⟩
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  filter_upwards [(AsymGrowthAux.isLittleO_kOf_rpow hs).def hc0] with n hn
  have hk0 : (0 : ℝ) ≤ kOf n := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hk0 _), Real.norm_of_nonneg hk0] at hn
  have hg := AsymGrowthAux.guard_le_rpow hρ C₀ C₁ n
  have h1 : (C₀ : ℝ) * (kOf n : ℝ) ^ (ρ.eps * C₁) ≤ C₀ * (c * kOf n) :=
    mul_le_mul_of_nonneg_left hn hC
  have h2 : 2 * (C₀ : ℝ) * c * kOf n ≤ 1 * kOf n := mul_le_mul_of_nonneg_right hc1 hk0
  have h4 : ((2 * guardOf C₀ C₁ ρ n : ℕ) : ℝ) ≤ kOf n := by
    push_cast
    linarith
  exact_mod_cast h4

/-- CONTRACT (Remark A.12 (`rem:walsh-delta`), "through `Δ = o(P)`"; Section 7.3 (`sec:main-tables`)): for `εC₁ < 1`, `Δ = o(P)`. -/
theorem isLittleO_guard (hρ : ρ.Admissible) (C₀ C₁ : ℕ) (hC₁ : ρ.e₁ * C₁ < ρ.e₂) :
    (fun n => (guardOf C₀ C₁ ρ n : ℝ)) =o[atTop] (fun n => (POf n : ℝ)) := by
  -- `Δ = O(k^{εC₁})` (`d ≤ k^ε`), `k^{εC₁} = o(k)` (`εC₁ < 1`) and `k = O(P)` (`k ≤ P`).
  have hs := AsymGrowthAux.eps_mul_lt_one hC₁
  have h1 : (fun n => (guardOf C₀ C₁ ρ n : ℝ)) =O[atTop]
      (fun n => (kOf n : ℝ) ^ (ρ.eps * C₁)) := by
    refine IsBigO.of_bound C₀ (Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact AsymGrowthAux.guard_le_rpow hρ C₀ C₁ n
  have h3 : (fun n => (kOf n : ℝ)) =O[atTop] (fun n => (POf n : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul]
    exact_mod_cast AsymBandsAux.kOf_le_POf n
  exact h1.trans_isLittleO ((AsymGrowthAux.isLittleO_kOf_rpow hs).trans_isBigO h3)

/-- CONTRACT (Section 7.3 (`sec:main-tables`), eq. (`eq:setup`) is `o(RP)`; Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`), "so the setup is at most `RP`"): for
all constants `C_set, D`, eventually `C_set((R/r)P^D + rP^D + P^D) ≤ RP`. -/
theorem eventually_setup_le (hρ : ρ.Admissible) (Cset D : ℕ) :
    ∀ᶠ n in atTop,
      Cset * (ROf n / rOf ρ n * POf n ^ D + rOf ρ n * POf n ^ D + POf n ^ D) ≤ VOf n := by
  -- Transfer the uniform `k`-level bound `eventually_setupK` along `k → ∞` at `P' = P`
  -- (eventually `16k ≤ P ≤ 32k`); `R = 2^k`, `r = rK ρ k` and `V = 2^k P` definitionally.
  filter_upwards [tendsto_kOf.eventually (eventually_setupK hρ Cset D),
    AsymBandsAux.eventually_POf_band] with n h ⟨h1, h2⟩
  exact h (POf n) h1 (by omega)

end SubNLogN.Math.Cost
