import Mathlib
import SubNLogN.Math.Cost.AsymSizes
import SubNLogN.Math.Cost.AsymK

/-!
# Cost: Lemma 7.1, row-dependent sizes of the paper family, bands (part 2 of `Asymptotics`)

Paper: Lemma 7.1 (`lem:root-family`, Section 7.1 (`sec:main-alg`)). For an admissible row (`0 < ε < 1/14`,
`0 < c ≤ 1`): `½k^ε ≤ d ≤ k^ε`, `d → ∞`, eventually `ℓ ≥ 2`, the bands eq. (`eq:bands`) at any precision
`16k ≤ P' ≤ 64k` (in particular `P' ∈ {P, q, q + 8d}`) and `K = Θ(P^{εc})` with explicit constants.
The `k`-level versions are in `AsymK.lean`; `Bands ρ P' n` is definitionally `BandsK ρ P' (kOf n)`
(`bands_iff_bandsK`).

Theorems tagged CONTRACT are the contract statements; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

open Filter Asymptotics Topology

/-! ## Row-dependent sizes -/

variable {ρ : RowExps}

/-! ### Auxiliary facts (used here and in `AsymGrowth`)

Kept in the namespace `AsymBandsAux` to avoid clashes with helper names of other files. -/

namespace AsymBandsAux

/-- Real-valued form of admissibility: `0 < ε < 1/14` and `0 < c ≤ 1`. -/
theorem admissible_real (hρ : ρ.Admissible) :
    0 < ρ.eps ∧ ρ.eps < 1 / 14 ∧ 0 < ρ.c ∧ ρ.c ≤ 1 := by
  obtain ⟨he₁, he₁₂, hc₁, hc₁₂⟩ := hρ
  have he₂ : (0 : ℝ) < ρ.e₂ := by exact_mod_cast (show 0 < ρ.e₂ by omega)
  have hc₂ : (0 : ℝ) < ρ.c₂ := by exact_mod_cast (show 0 < ρ.c₂ by omega)
  have he₁' : (0 : ℝ) < ρ.e₁ := by exact_mod_cast he₁
  have hc₁' : (0 : ℝ) < ρ.c₁ := by exact_mod_cast hc₁
  have he₁₂' : (14 : ℝ) * ρ.e₁ < ρ.e₂ := by exact_mod_cast he₁₂
  have hc₁₂' : (ρ.c₁ : ℝ) ≤ ρ.c₂ := by exact_mod_cast hc₁₂
  unfold RowExps.eps RowExps.c
  refine ⟨div_pos he₁' he₂, ?_, div_pos hc₁' hc₂, (div_le_one hc₂).2 hc₁₂'⟩
  rw [div_lt_iff₀ he₂]
  linarith

/-- `256 ≤ P` for every `n`. -/
theorem le_POf (n : ℕ) : 256 ≤ POf n := by
  unfold POf; omega

/-- `k ≤ P` for every `n`. -/
theorem kOf_le_POf (n : ℕ) : kOf n ≤ POf n := by
  unfold POf; omega

/-- `1 < P`, as a real number. -/
theorem one_lt_POf_real (n : ℕ) : (1 : ℝ) < POf n := by
  have := le_POf n
  exact_mod_cast (show 1 < POf n by omega)

/-- `0 < P`, as a real number. -/
theorem POf_pos_real (n : ℕ) : (0 : ℝ) < POf n :=
  lt_trans one_pos (one_lt_POf_real n)

/-- `q = P + 2` (definitional). -/
theorem qOf_eq (n : ℕ) : qOf n = POf n + 2 := rfl

/-- For an admissible row, `d ≤ k` for every `k` (`d^{e₂} ≤ k^{e₁} ≤ k^{e₂}` as `e₁ ≤ e₂`). -/
theorem dK_le_self (hρ : ρ.Admissible) (k : ℕ) : dK ρ k ≤ k := by
  obtain ⟨he₁, he₁₂, -, -⟩ := hρ
  have he₂ : 0 < ρ.e₂ := by omega
  have h : dK ρ k ^ ρ.e₂ ≤ k ^ ρ.e₁ :=
    (le_floorRatPow_iff (x := k) (e₁ := ρ.e₁) he₂ (dK ρ k)).1 le_rfl
  have h2 : k ^ ρ.e₁ ≤ k ^ ρ.e₂ := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, Nat.zero_pow he₁]
      exact Nat.zero_le _
    · exact Nat.pow_le_pow_right hk (by omega)
  exact (Nat.pow_le_pow_iff_left he₂.ne').1 (h.trans h2)

/-- For an admissible row, `d ≤ k^ε` for every `n` (`d = ⌊k^ε⌋₊`). -/
theorem dOf_le_rpow (hρ : ρ.Admissible) (n : ℕ) : (dOf ρ n : ℝ) ≤ (kOf n : ℝ) ^ ρ.eps := by
  have he₂ : 0 < ρ.e₂ := by have := hρ.2.1; omega
  rw [dOf_eq_floor ρ he₂ n]
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `k → ∞`, as a real number. -/
theorem tendsto_kOf_real : Tendsto (fun n => (kOf n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_kOf

/-- `P → ∞`, as a real number. -/
theorem tendsto_POf_real : Tendsto (fun n => (POf n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono kOf_le_POf tendsto_kOf)

/-- Eventually `16k ≤ P ≤ 32k` (from `eventually_POf_bounds`, as `P < q`). -/
theorem eventually_POf_band : ∀ᶠ n in atTop, 16 * kOf n ≤ POf n ∧ POf n ≤ 32 * kOf n := by
  filter_upwards [eventually_POf_bounds] with n ⟨_, h2, h3⟩
  have hq := qOf_eq n
  exact ⟨h2, by omega⟩

end AsymBandsAux

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), "once `k^ε ≥ 2` we have `½k^ε ≤ d ≤ k^ε`"): for an admissible row and any
`n` with `k^ε ≥ 2`. -/
theorem dOf_bounds (hρ : ρ.Admissible) (n : ℕ) (hk : 2 ≤ (kOf n : ℝ) ^ ρ.eps) :
    (1 / 2 : ℝ) * (kOf n : ℝ) ^ ρ.eps ≤ dOf ρ n ∧ (dOf ρ n : ℝ) ≤ (kOf n : ℝ) ^ ρ.eps := by
  -- `dOf ρ n = dK ρ (kOf n)` definitionally (`dOf_eq_dK`): the `k`-level bound `dK_bounds`.
  exact dK_bounds hρ (kOf n) hk

/-- CONTRACT (Lemma 7.1 (`lem:root-family`) and eq. (`eq:cutoff`), activation "`d ≥ 2`"): `d → ∞`. -/
theorem tendsto_dOf (hρ : ρ.Admissible) : Tendsto (dOf ρ) atTop atTop := by
  -- `dOf ρ = dK ρ ∘ kOf` definitionally; `tendsto_dK` and `tendsto_kOf`.
  exact (tendsto_dK hρ).comp tendsto_kOf

/-- CONTRACT (Section 4.4 (`sec:bridge-alg`), "`ℓ ≥ 2`", required by the bridge; from `ℓ ≥ k^{1-ε}`, proof of Lemma 7.1 (`lem:root-family`)):
eventually `2 ≤ ℓ`. -/
theorem eventually_two_le_lOf (hρ : ρ.Admissible) : ∀ᶠ n in atTop, 2 ≤ lOf ρ n := by
  -- `lOf ρ n = lK ρ (kOf n)` definitionally; transfer `eventually_two_le_lK` along `k → ∞`.
  exact tendsto_kOf.eventually (eventually_two_le_lK hρ)

/-- The bands of Lemma 7.1 at a precision `P'` (Lemma 7.1 (`lem:root-family`), eq. (`eq:bands`) with `a_d = 1/4`,
`b_d = 1`, `a_r = 1/128`, `b_r = 1/8`, `C_ℓ = 1`; proof of Lemma 7.1 (`lem:root-family`)): `¼P'^ε ≤ d ≤ P'^ε`,
`P'/(128d) ≤ ℓ ≤ P'/(8d)` (equivalently `2^{P'/(128d)} ≤ r ≤ 2^{P'/(8d)}`, as `r = 2^ℓ`),
`dℓ ≤ P'` and `lg(R/r) = k - ℓ ≤ P'`. -/
def Bands (ρ : RowExps) (P' n : ℕ) : Prop :=
  (1 / 4 : ℝ) * (P' : ℝ) ^ ρ.eps ≤ dOf ρ n ∧ (dOf ρ n : ℝ) ≤ (P' : ℝ) ^ ρ.eps ∧
    (P' : ℝ) / (128 * dOf ρ n) ≤ lOf ρ n ∧ (lOf ρ n : ℝ) ≤ (P' : ℝ) / (8 * dOf ρ n) ∧
    dOf ρ n * lOf ρ n ≤ P' ∧ kOf n - lOf ρ n ≤ P'

/-- CONTRACT (Lemma 7.1 bands, eq. (`eq:bands`)): for an admissible row and any
precision `P'` with eventually `16k ≤ P' ≤ 64k`, the bands `Bands ρ P' n` hold eventually. -/
theorem eventually_bands (hρ : ρ.Admissible) (P' : ℕ → ℕ)
    (hlo : ∀ᶠ n in atTop, 16 * kOf n ≤ P' n) (hhi : ∀ᶠ n in atTop, P' n ≤ 64 * kOf n) :
    ∀ᶠ n in atTop, Bands ρ (P' n) n := by
  -- Transfer the uniform `k`-level bands `eventually_bandsK` along `k → ∞`; `Bands ρ P' n` is
  -- definitionally `BandsK ρ P' (kOf n)`.
  filter_upwards [tendsto_kOf.eventually (eventually_bandsK hρ), hlo, hhi] with n h h1 h2
  exact h (P' n) h1 h2

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), eq. (`eq:bands`), "at both precisions `P' ∈ {q, q+8d}`"): the bands at `P' = q`. -/
theorem eventually_bands_q (hρ : ρ.Admissible) : ∀ᶠ n in atTop, Bands ρ (qOf n) n := by
  -- `16k ≤ P < q ≤ 32k` eventually (`eventually_POf_bounds`).
  refine eventually_bands hρ qOf ?_ ?_
  · filter_upwards [eventually_POf_bounds] with n ⟨_, h2, _⟩
    have hq := AsymBandsAux.qOf_eq n
    omega
  · filter_upwards [eventually_POf_bounds] with n ⟨_, _, h3⟩
    omega

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), eq. (`eq:bands`), "at both precisions `P' ∈ {q, q+8d}`"): the bands at `P' = q + 8d`. -/
theorem eventually_bands_q_add (hρ : ρ.Admissible) :
    ∀ᶠ n in atTop, Bands ρ (qOf n + 8 * dOf ρ n) n := by
  -- `16k ≤ q ≤ q + 8d` and `q + 8d ≤ 32k + 8k ≤ 64k` (`d ≤ k`, `AsymBandsAux.dK_le_self`).
  refine eventually_bands hρ (fun n => qOf n + 8 * dOf ρ n) ?_ ?_
  · filter_upwards [eventually_POf_bounds] with n ⟨_, h2, _⟩
    have hq := AsymBandsAux.qOf_eq n
    show 16 * kOf n ≤ qOf n + 8 * dOf ρ n
    omega
  · filter_upwards [eventually_POf_bounds] with n ⟨_, _, h3⟩
    have hd : dOf ρ n ≤ kOf n := AsymBandsAux.dK_le_self hρ (kOf n)
    show qOf n + 8 * dOf ρ n ≤ 64 * kOf n
    omega

/-- CONTRACT (the bands at the schedule precision `P' = P`, used with the cost tables Table 5 (`tab:cost-walsh`)). -/
theorem eventually_bands_P (hρ : ρ.Admissible) : ∀ᶠ n in atTop, Bands ρ (POf n) n := by
  -- `16k ≤ P ≤ 32k` eventually (`AsymBandsAux.eventually_POf_band`).
  refine eventually_bands hρ POf ?_ ?_
  · filter_upwards [AsymBandsAux.eventually_POf_band] with n h
    exact h.1
  · filter_upwards [AsymBandsAux.eventually_POf_band] with n ⟨_, h⟩
    omega

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`K = Θ(P^{εc})`", explicit constants): eventually
`⅛ P^{εc} ≤ K ≤ P^{εc}`. -/
theorem eventually_KOf_bounds (hρ : ρ.Admissible) :
    ∀ᶠ n in atTop, (1 / 8 : ℝ) * (POf n : ℝ) ^ (ρ.eps * ρ.c) ≤ KOf ρ n ∧
      (KOf ρ n : ℝ) ≤ (POf n : ℝ) ^ (ρ.eps * ρ.c) := by
  -- `K = ⌊d^c⌋₊` (`KOf_eq_floor`). With `¼P^ε ≤ d ≤ P^ε` (bands at `P`): `K ≤ d^c ≤ (P^ε)^c =
  -- P^{εc}`; and once `d^c ≥ 2` (eventual, as `d → ∞`, `c > 0`): `K > d^c - 1 ≥ d^c/2 ≥
  -- ½(¼)^c P^{εc} ≥ ⅛P^{εc}`, using `(¼)^c ≥ ¼` for `c ≤ 1`.
  obtain ⟨-, -, hc0, hc1⟩ := AsymBandsAux.admissible_real hρ
  have hc₂ : 0 < ρ.c₂ := by have := hρ.2.2.1; have := hρ.2.2.2; omega
  have hdc : Tendsto (fun n => (dOf ρ n : ℝ) ^ ρ.c) atTop atTop :=
    (tendsto_rpow_atTop hc0).comp (tendsto_natCast_atTop_atTop.comp (tendsto_dOf hρ))
  filter_upwards [eventually_bands_P hρ, hdc.eventually_ge_atTop 2] with n hB hd2
  obtain ⟨hB1, hB2, -, -, -, -⟩ := hB
  have hd2' : (2 : ℝ) ≤ (dOf ρ n : ℝ) ^ ρ.c := hd2
  have hP0 : (0 : ℝ) ≤ POf n := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ dOf ρ n := Nat.cast_nonneg _
  have hPe : (0 : ℝ) ≤ (POf n : ℝ) ^ ρ.eps := Real.rpow_nonneg hP0 _
  have hKeq : KOf ρ n = ⌊(dOf ρ n : ℝ) ^ ρ.c⌋₊ := KOf_eq_floor ρ hc₂ n
  have hpow : (POf n : ℝ) ^ (ρ.eps * ρ.c) = ((POf n : ℝ) ^ ρ.eps) ^ ρ.c := Real.rpow_mul hP0 _ _
  rw [hpow, hKeq]
  constructor
  · have h1 : (dOf ρ n : ℝ) ^ ρ.c - 1 < (⌊(dOf ρ n : ℝ) ^ ρ.c⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have h2 : ((1 / 4 : ℝ) * (POf n : ℝ) ^ ρ.eps) ^ ρ.c ≤ (dOf ρ n : ℝ) ^ ρ.c :=
      Real.rpow_le_rpow (by positivity) hB1 hc0.le
    have h3 : ((1 / 4 : ℝ) * (POf n : ℝ) ^ ρ.eps) ^ ρ.c
        = (1 / 4 : ℝ) ^ ρ.c * ((POf n : ℝ) ^ ρ.eps) ^ ρ.c :=
      Real.mul_rpow (by norm_num) hPe
    have h4 : (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) ^ ρ.c := by
      calc (1 / 4 : ℝ) = (1 / 4 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 4 : ℝ) ^ ρ.c := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hc1
    have h5 : 0 ≤ ((POf n : ℝ) ^ ρ.eps) ^ ρ.c := Real.rpow_nonneg hPe _
    have h6 : (1 / 4 : ℝ) * ((POf n : ℝ) ^ ρ.eps) ^ ρ.c
        ≤ (1 / 4 : ℝ) ^ ρ.c * ((POf n : ℝ) ^ ρ.eps) ^ ρ.c :=
      mul_le_mul_of_nonneg_right h4 h5
    linarith
  · have h1 : (⌊(dOf ρ n : ℝ) ^ ρ.c⌋₊ : ℝ) ≤ (dOf ρ n : ℝ) ^ ρ.c :=
      Nat.floor_le (Real.rpow_nonneg hd0 _)
    have h2 : (dOf ρ n : ℝ) ^ ρ.c ≤ ((POf n : ℝ) ^ ρ.eps) ^ ρ.c :=
      Real.rpow_le_rpow hd0 hB2 hc0.le
    linarith

/-- `Bands` is `BandsK` at `k = kOf n` (definitional). -/
theorem bands_iff_bandsK (ρ : RowExps) (P' n : ℕ) : Bands ρ P' n ↔ BandsK ρ P' (kOf n) := Iff.rfl

end SubNLogN.Math.Cost
