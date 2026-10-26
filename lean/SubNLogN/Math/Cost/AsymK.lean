import Mathlib
import SubNLogN.Math.Cost.Family

/-!
# Cost: Lemma 7.1, row-dependent part, at the level of the transform exponent `k`

Paper: Lemma 7.1 (`lem:root-family`, Section 7.1 (`sec:main-alg`)), with the
uses in Section 7.3 (`sec:main-tables`, eq. (`eq:setup`) is `o(RP)`) and Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`) (what the cutoff guarantees).

The row-dependent sizes `d, ℓ, r` depend on the input only through `k` (`R = 2^k`), so these facts
are stated as `k → ∞` (`Filter.atTop` on `ℕ`), uniformly over all precisions `P'` with
`16k ≤ P' ≤ 64k`. They transfer to any root family `n ↦ (b n, k n)` with `k n → ∞` and
eventually `16 k ≤ P ≤ 64 k` (`FamFacts`), in particular to the paper family (`AsymBands`,
`AsymGrowth`) and to the machine's W8 family (`FamilyW8`). Row: admissible
(`0 < ε < 1/14`, `0 < c ≤ 1`, `RowExps.Admissible`).

Theorems tagged CONTRACT are statements to be proved; all of them are proved in this file (helper
lemmas in the namespace `AsymK`).
-/

namespace SubNLogN.Math.Cost

open Filter

variable {ρ : RowExps}

/-! ## Helper facts (namespace `AsymK`)

Proof plan (proof of Lemma 7.1 (`lem:root-family`)). Write `d = dK ρ k`, `ℓ = lK ρ k`, `r = rK ρ k = 2^ℓ`, `ε = e₁/e₂`.
Everything except the real-power bands is proved in `ℕ`:
* `y ≤ d ↔ y^{e₂} ≤ k^{e₁}` (`le_floorRatPow_iff`); hence `d² ≤ k` (as `2e₁ ≤ e₂`) and `y ≤ d`
  once `y^{e₂} ≤ k`, so `d → ∞`;
* for `1 ≤ k` (so `1 ≤ d`): `k ≤ dℓ < k + d` (ceiling division), `ℓ ≤ k`, `d ≤ ℓ` (from
  `d² ≤ k ≤ dℓ`) and `k ≤ ℓ²`;
* for `4 ≤ k` and `4 ≤ d`: `4(ℓ - 1) ≤ d(ℓ - 1) < k`, hence `k ≤ (k - ℓ)²`;
* eventually `m^N ≤ 2^m` (`isLittleO_pow_const_const_pow_of_one_lt`); so if eventually
  `k ≤ f(k)²` then eventually `k^j ≤ 2^{f(k)}`. With `f = ℓ` this bounds `r` from below, with
  `f = k - ℓ` it bounds `R/r = 2^{k-ℓ}` (`Nat.pow_div`) from below.
The real bands use `d = ⌊k^ε⌋₊` (`floorRatPow_eq_floor_rpow`) and `64^ε = 2^{6ε} ≤ 2`
(`6ε ≤ 1`, from `14e₁ < e₂`).
-/

namespace AsymK

/-- `0 < e₁` for an admissible row. -/
theorem e₁_pos (hρ : ρ.Admissible) : 0 < ρ.e₁ := by
  obtain ⟨h1, -, -, -⟩ := hρ
  exact h1

/-- `0 < e₂` for an admissible row. -/
theorem e₂_pos (hρ : ρ.Admissible) : 0 < ρ.e₂ := by
  obtain ⟨h1, h2, -, -⟩ := hρ
  omega

/-- `6 e₁ ≤ e₂` for an admissible row (from `14 e₁ < e₂`). -/
theorem six_e₁_le (hρ : ρ.Admissible) : 6 * ρ.e₁ ≤ ρ.e₂ := by
  obtain ⟨h1, h2, -, -⟩ := hρ
  omega

/-- `0 < ε` for an admissible row. -/
theorem eps_pos (hρ : ρ.Admissible) : 0 < ρ.eps := by
  have h1 : (0 : ℝ) < ρ.e₁ := by exact_mod_cast e₁_pos hρ
  have h2 : (0 : ℝ) < ρ.e₂ := by exact_mod_cast e₂_pos hρ
  exact div_pos h1 h2

/-- `6ε ≤ 1` for an admissible row. -/
theorem six_eps_le_one (hρ : ρ.Admissible) : 6 * ρ.eps ≤ 1 := by
  have h2 : (0 : ℝ) < ρ.e₂ := by exact_mod_cast e₂_pos hρ
  have h3 : (6 : ℝ) * ρ.e₁ ≤ ρ.e₂ := by exact_mod_cast six_e₁_le hρ
  show 6 * ((ρ.e₁ : ℝ) / ρ.e₂) ≤ 1
  rw [mul_div_assoc', div_le_iff₀ h2, one_mul]
  exact h3

/-- `64^ε ≤ 2` for an admissible row (`64^ε = 2^{6ε}` and `6ε ≤ 1`). -/
theorem sixtyfour_rpow_eps_le (hρ : ρ.Admissible) : (64 : ℝ) ^ ρ.eps ≤ 2 := by
  have e : (2 : ℝ) ^ (6 : ℝ) = 64 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [← e, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc (2 : ℝ) ^ (6 * ρ.eps) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (six_eps_le_one hρ)
    _ = 2 := Real.rpow_one 2

/-- `d = ⌊k^ε⌋₊` with the real power. -/
theorem dK_eq_floor (hρ : ρ.Admissible) (k : ℕ) : dK ρ k = ⌊(k : ℝ) ^ ρ.eps⌋₊ := by
  show floorRatPow k ρ.e₁ ρ.e₂ = ⌊(k : ℝ) ^ ((ρ.e₁ : ℝ) / ρ.e₂)⌋₊
  exact floorRatPow_eq_floor_rpow (e₂_pos hρ)

/-- `d ≤ k^ε` (real power). -/
theorem dK_le_rpow (hρ : ρ.Admissible) (k : ℕ) : (dK ρ k : ℝ) ≤ (k : ℝ) ^ ρ.eps := by
  rw [dK_eq_floor hρ]
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- `y ≤ d ↔ y^{e₂} ≤ k^{e₁}` (integer comparison). -/
theorem le_dK_iff (hρ : ρ.Admissible) (k y : ℕ) : y ≤ dK ρ k ↔ y ^ ρ.e₂ ≤ k ^ ρ.e₁ :=
  le_floorRatPow_iff (e₂_pos hρ) y

/-- `d^{e₂} ≤ k^{e₁}`. -/
theorem dK_pow_le (hρ : ρ.Admissible) (k : ℕ) : dK ρ k ^ ρ.e₂ ≤ k ^ ρ.e₁ :=
  (le_dK_iff hρ k _).1 le_rfl

/-- If `y^{e₂} ≤ k` then `y ≤ d`. -/
theorem le_dK_of_pow_le (hρ : ρ.Admissible) {k y : ℕ} (h : y ^ ρ.e₂ ≤ k) : y ≤ dK ρ k :=
  (le_dK_iff hρ k y).2 (le_trans h (Nat.le_self_pow (e₁_pos hρ).ne' k))

/-- `1 ≤ d` for `1 ≤ k`. -/
theorem one_le_dK (hρ : ρ.Admissible) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ dK ρ k :=
  le_dK_of_pow_le hρ (by rw [one_pow]; exact hk)

/-- `d² ≤ k` (for every `k`), as `d^{2e₁} ≤ d^{e₂} ≤ k^{e₁}`. -/
theorem dK_sq_le (hρ : ρ.Admissible) (k : ℕ) : dK ρ k ^ 2 ≤ k := by
  rcases Nat.eq_zero_or_pos (dK ρ k) with h0 | hpos
  · rw [h0]
    simp
  · have h6 := six_e₁_le hρ
    have h1 : dK ρ k ^ (2 * ρ.e₁) ≤ dK ρ k ^ ρ.e₂ := Nat.pow_le_pow_right hpos (by omega)
    have h2 : (dK ρ k ^ 2) ^ ρ.e₁ ≤ k ^ ρ.e₁ := by
      rw [← pow_mul]
      exact le_trans h1 (dK_pow_le hρ k)
    exact (Nat.pow_le_pow_iff_left (e₁_pos hρ).ne').1 h2

/-- `d ≤ k` (for every `k`). -/
theorem dK_le_self (hρ : ρ.Admissible) (k : ℕ) : dK ρ k ≤ k :=
  le_trans (Nat.le_self_pow two_ne_zero _) (dK_sq_le hρ k)

/-- Ceiling division: for `1 ≤ b`, `a ≤ b · ((a + b - 1) / b) < a + b`. -/
theorem ceilDiv_bounds {a b : ℕ} (hb : 1 ≤ b) :
    a ≤ b * ((a + b - 1) / b) ∧ b * ((a + b - 1) / b) < a + b := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) (show b > 0 by omega)
  constructor <;> omega

/-- For `1 ≤ k`: `k ≤ dℓ < k + d` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
theorem dK_mul_lK_bounds (hρ : ρ.Admissible) {k : ℕ} (hk : 1 ≤ k) :
    k ≤ dK ρ k * lK ρ k ∧ dK ρ k * lK ρ k < k + dK ρ k :=
  ceilDiv_bounds (one_le_dK hρ hk)

/-- For `1 ≤ k`: `ℓ ≤ k`. -/
theorem lK_le_self (hρ : ρ.Admissible) {k : ℕ} (hk : 1 ≤ k) : lK ρ k ≤ k := by
  have h := (dK_mul_lK_bounds hρ hk).2
  have h1 : 1 * (lK ρ k - 1) ≤ dK ρ k * (lK ρ k - 1) :=
    Nat.mul_le_mul_right _ (one_le_dK hρ hk)
  have h2 : dK ρ k * (lK ρ k - 1) = dK ρ k * lK ρ k - dK ρ k := Nat.mul_sub_one _ _
  omega

/-- For `1 ≤ k`: `d ≤ ℓ` (from `d² ≤ k ≤ dℓ`). -/
theorem dK_le_lK (hρ : ρ.Admissible) {k : ℕ} (hk : 1 ≤ k) : dK ρ k ≤ lK ρ k := by
  have h3 : dK ρ k * dK ρ k ≤ dK ρ k * lK ρ k := by
    rw [← sq]
    exact le_trans (dK_sq_le hρ k) (dK_mul_lK_bounds hρ hk).1
  exact Nat.le_of_mul_le_mul_left h3 (one_le_dK hρ hk)

/-- For `1 ≤ k`: `k ≤ ℓ²` (as `k ≤ dℓ ≤ ℓ²`). -/
theorem le_lK_sq (hρ : ρ.Admissible) {k : ℕ} (hk : 1 ≤ k) : k ≤ lK ρ k ^ 2 := by
  rw [sq]
  exact le_trans (dK_mul_lK_bounds hρ hk).1 (Nat.mul_le_mul_right _ (dK_le_lK hρ hk))

/-- For `4 ≤ k` and `4 ≤ d`: `k ≤ (k - ℓ)²` (as `4(ℓ - 1) ≤ d(ℓ - 1) < k`). -/
theorem le_sub_lK_sq (hρ : ρ.Admissible) {k : ℕ} (hk : 4 ≤ k) (hd : 4 ≤ dK ρ k) :
    k ≤ (k - lK ρ k) ^ 2 := by
  have h := (dK_mul_lK_bounds hρ (by omega : 1 ≤ k)).2
  have h1 : 4 * (lK ρ k - 1) ≤ dK ρ k * (lK ρ k - 1) := Nat.mul_le_mul_right _ hd
  have h2 : dK ρ k * (lK ρ k - 1) = dK ρ k * lK ρ k - dK ρ k := Nat.mul_sub_one _ _
  have hm2 : 2 ≤ k - lK ρ k := by omega
  have hmk : k ≤ 2 * (k - lK ρ k) := by omega
  calc k ≤ 2 * (k - lK ρ k) := hmk
    _ ≤ (k - lK ρ k) * (k - lK ρ k) := Nat.mul_le_mul_right _ hm2
    _ = (k - lK ρ k) ^ 2 := (sq _).symm

/-- `R / r = 2^{k-ℓ}` for `1 ≤ k` (`Nat.pow_div`, as `ℓ ≤ k`). -/
theorem two_pow_div_rK (hρ : ρ.Admissible) {k : ℕ} (hk : 1 ≤ k) :
    2 ^ k / rK ρ k = 2 ^ (k - lK ρ k) :=
  Nat.pow_div (lK_le_self hρ hk) (by norm_num)

/-- Eventually `m^N ≤ 2^m` (from `n^N = o(2^n)`). -/
theorem eventually_pow_le_two_pow (N : ℕ) : ∀ᶠ m : ℕ in atTop, m ^ N ≤ 2 ^ m := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) N
    (by norm_num : (1 : ℝ) < 2)).eventuallyLE
  filter_upwards [h] with m hm
  have h1 : ((m ^ N : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    push_cast
    calc (m : ℝ) ^ N ≤ ‖(m : ℝ) ^ N‖ := Real.le_norm_self _
      _ ≤ ‖(2 : ℝ) ^ m‖ := hm
      _ = (2 : ℝ) ^ m := Real.norm_of_nonneg (by positivity)
  exact_mod_cast h1

/-- If eventually `k ≤ f(k)²`, then for every `j`, eventually `k^j ≤ 2^{f(k)}`. -/
theorem eventually_pow_le_two_pow_of_le_sq {f : ℕ → ℕ} (hf : ∀ᶠ k in atTop, k ≤ f k ^ 2)
    (j : ℕ) : ∀ᶠ k in atTop, k ^ j ≤ 2 ^ f k := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_pow_le_two_pow (2 * j))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hf
  refine eventually_atTop.2 ⟨max K (M ^ 2), fun k hk => ?_⟩
  have hk1 : k ≤ f k ^ 2 := hK k (le_of_max_le_left hk)
  have hk2 : M ^ 2 ≤ k := le_of_max_le_right hk
  have hfM : M ≤ f k := by
    by_contra h
    have h' : f k ^ 2 < M ^ 2 := Nat.pow_lt_pow_left (not_le.mp h) two_ne_zero
    exact lt_irrefl _ (lt_of_le_of_lt (le_trans hk2 hk1) h')
  calc k ^ j ≤ (f k ^ 2) ^ j := Nat.pow_le_pow_left hk1 j
    _ = f k ^ (2 * j) := by rw [← pow_mul]
    _ ≤ 2 ^ f k := hM (f k) hfM

/-- Eventually `4 ≤ d`. -/
theorem eventually_four_le_dK (hρ : ρ.Admissible) : ∀ᶠ k in atTop, 4 ≤ dK ρ k :=
  (eventually_ge_atTop (4 ^ ρ.e₂)).mono fun _ hk => le_dK_of_pow_le hρ hk

/-- For every `j`, eventually `k^j ≤ r`. -/
theorem eventually_pow_le_rK (hρ : ρ.Admissible) (j : ℕ) : ∀ᶠ k in atTop, k ^ j ≤ rK ρ k :=
  eventually_pow_le_two_pow_of_le_sq (f := lK ρ)
    ((eventually_ge_atTop 1).mono fun _ hk => le_lK_sq hρ hk) j

/-- For every `j`, eventually `k^j ≤ R / r` (`R = 2^k`). -/
theorem eventually_pow_le_two_pow_div_rK (hρ : ρ.Admissible) (j : ℕ) :
    ∀ᶠ k in atTop, k ^ j ≤ 2 ^ k / rK ρ k := by
  have hf : ∀ᶠ k in atTop, k ≤ (k - lK ρ k) ^ 2 := by
    filter_upwards [eventually_ge_atTop 4, eventually_four_le_dK hρ] with k hk hd
    exact le_sub_lK_sq hρ hk hd
  filter_upwards [eventually_pow_le_two_pow_of_le_sq (f := fun k => k - lK ρ k) hf j,
    eventually_ge_atTop 1] with k hk hk1
  rw [two_pow_div_rK hρ hk1]
  exact hk

/-- The arithmetic of the setup bound: if `qr ≤ R`, `q ≤ R`, `3A ≤ r`, `3A ≤ q`, `CX ≤ A` and
`1 ≤ P`, then `C(qX + rX + X) ≤ RP`. -/
theorem setup_arith {R r q A C X P : ℕ} (hqr : q * r ≤ R) (hqR : q ≤ R) (hr : 3 * A ≤ r)
    (hq : 3 * A ≤ q) (hX : C * X ≤ A) (hP : 1 ≤ P) : C * (q * X + r * X + X) ≤ R * P := by
  have h1 : q * (3 * A) ≤ q * r := Nat.mul_le_mul_left q hr
  have h2 : r * (3 * A) ≤ r * q := Nat.mul_le_mul_left r hq
  have h4 : q * (C * X) ≤ q * A := Nat.mul_le_mul_left q hX
  have h5 : r * (C * X) ≤ r * A := Nat.mul_le_mul_left r hX
  have h6 : R * 1 ≤ R * P := Nat.mul_le_mul_left R hP
  linarith

end AsymK

/-- CONTRACT (proof of Lemma 7.1 (`lem:root-family`), "once `k^ε ≥ 2` we have `½k^ε ≤ d ≤ k^ε`"), at `k`. -/
theorem dK_bounds (hρ : ρ.Admissible) (k : ℕ) (hk : 2 ≤ (k : ℝ) ^ ρ.eps) :
    (1 / 2 : ℝ) * (k : ℝ) ^ ρ.eps ≤ dK ρ k ∧ (dK ρ k : ℝ) ≤ (k : ℝ) ^ ρ.eps := by
  -- `d = ⌊k^ε⌋₊`, so `k^ε - 1 < d ≤ k^ε`, and `k^ε - 1 ≥ ½k^ε` once `k^ε ≥ 2`.
  have h0 : 0 ≤ (k : ℝ) ^ ρ.eps := Real.rpow_nonneg (Nat.cast_nonneg k) _
  rw [AsymK.dK_eq_floor hρ]
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one ((k : ℝ) ^ ρ.eps)
  constructor <;> linarith

/-- CONTRACT (Lemma 7.1 (`lem:root-family`) and eq. (`eq:cutoff`), activation "`d ≥ 2`"): `d → ∞` as `k → ∞`. -/
theorem tendsto_dK (hρ : ρ.Admissible) : Tendsto (dK ρ) atTop atTop := by
  -- `y ≤ d` as soon as `k ≥ y^{e₂}` (integer comparison).
  exact tendsto_atTop.2 fun y => (eventually_ge_atTop (y ^ ρ.e₂)).mono fun _ hk =>
    AsymK.le_dK_of_pow_le hρ hk

/-- CONTRACT (Section 4.4 (`sec:bridge-alg`), "`ℓ ≥ 2`"; from `ℓ ≥ k^{1-ε}`, proof of Lemma 7.1 (`lem:root-family`)): eventually `2 ≤ ℓ`. -/
theorem eventually_two_le_lK (hρ : ρ.Admissible) : ∀ᶠ k in atTop, 2 ≤ lK ρ k := by
  -- `k ≤ ℓ²` for `k ≥ 1`, so `ℓ ≥ 2` once `k ≥ 4`.
  filter_upwards [eventually_ge_atTop 4] with k hk
  have h := AsymK.le_lK_sq hρ (by omega : 1 ≤ k)
  by_contra hl
  have h1 : lK ρ k ≤ 1 := by omega
  have h2 : lK ρ k ^ 2 ≤ 1 := by
    calc lK ρ k ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 1 := by norm_num
  omega

/-- CONTRACT (Lemma 7.1 bands, eq. (`eq:bands`)), at `k`, uniformly in the precision:
eventually in `k`, every `P'` with `16k ≤ P' ≤ 64k` satisfies `BandsK ρ P' k`. -/
theorem eventually_bandsK (hρ : ρ.Admissible) :
    ∀ᶠ k in atTop, ∀ P' : ℕ, 16 * k ≤ P' → P' ≤ 64 * k → BandsK ρ P' k := by
  -- Threshold `k ≥ 2^{e₂}` (so `d ≥ 2`, hence `k^ε ≥ 2` and `½k^ε ≤ d ≤ k^ε`). Then for
  -- `16k ≤ P' ≤ 64k`: `¼P'^ε ≤ ¼·64^ε k^ε ≤ ½k^ε ≤ d`, `d ≤ k^ε ≤ P'^ε`,
  -- `P' ≤ 64k ≤ 64dℓ`, `8dℓ < 8(k + d) ≤ 16k ≤ P'` (as `d ≤ k`), `dℓ < 2k ≤ P'`, `k - ℓ ≤ P'`.
  filter_upwards [eventually_ge_atTop (2 ^ ρ.e₂), eventually_ge_atTop 1] with k hk2 hk1
  intro P' hP1 hP2
  have hd2 : 2 ≤ dK ρ k := AsymK.le_dK_of_pow_le hρ hk2
  have hdk := AsymK.dK_le_self hρ k
  obtain ⟨hkl, hlk⟩ := AsymK.dK_mul_lK_bounds hρ hk1
  have heps := AsymK.eps_pos hρ
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkε0 : 0 ≤ (k : ℝ) ^ ρ.eps := Real.rpow_nonneg hk0 _
  have hdle := AsymK.dK_le_rpow hρ k
  have hkε2 : (2 : ℝ) ≤ (k : ℝ) ^ ρ.eps := le_trans (by exact_mod_cast hd2) hdle
  have hhalf := (dK_bounds hρ k hkε2).1
  have hP1r : (k : ℝ) ≤ P' := by exact_mod_cast (by omega : k ≤ P')
  have hP2r : (P' : ℝ) ≤ 64 * k := by exact_mod_cast hP2
  have hPε : (P' : ℝ) ^ ρ.eps ≤ 64 ^ ρ.eps * (k : ℝ) ^ ρ.eps := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) hk0]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hP2r heps.le
  have h64 := mul_le_mul_of_nonneg_right (AsymK.sixtyfour_rpow_eps_le hρ) hkε0
  have hdpos : (0 : ℝ) < dK ρ k := Nat.cast_pos.mpr (by omega)
  refine ⟨by linarith, le_trans hdle (Real.rpow_le_rpow hk0 hP1r heps.le), ?_, ?_, by omega,
    by omega⟩
  · rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 128) hdpos)]
    have e : lK ρ k * (128 * dK ρ k) = 128 * (dK ρ k * lK ρ k) := by ring
    have h : P' ≤ lK ρ k * (128 * dK ρ k) := by rw [e]; omega
    exact_mod_cast h
  · rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hdpos)]
    have e : lK ρ k * (8 * dK ρ k) = 8 * (dK ρ k * lK ρ k) := by ring
    have h : lK ρ k * (8 * dK ρ k) ≤ P' := by rw [e]; omega
    exact_mod_cast h

/-- CONTRACT (Lemma 7.1 (`lem:root-family`), "`r/P^j → ∞` for every fixed `j`"), at `k`: `r / k^j → ∞`. -/
theorem tendsto_rK_div_pow (hρ : ρ.Admissible) (j : ℕ) :
    Tendsto (fun k => (rK ρ k : ℝ) / (k : ℝ) ^ j) atTop atTop := by
  -- Eventually `k^{j+1} ≤ r`, so `r / k^j ≥ k → ∞`.
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [AsymK.eventually_pow_le_rK hρ (j + 1), eventually_gt_atTop 0] with k hk hk0
  have hkpos : (0 : ℝ) < (k : ℝ) ^ j := pow_pos (Nat.cast_pos.mpr hk0) j
  rw [le_div_iff₀ hkpos]
  have h : ((k ^ (j + 1) : ℕ) : ℝ) ≤ (rK ρ k : ℝ) := Nat.cast_le.mpr hk
  calc (k : ℝ) * (k : ℝ) ^ j = ((k ^ (j + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ rK ρ k := h

/-- CONTRACT (Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`), "`R/r ≥ 4CP^{D_set+1}`" for large `k`), at `k`: `(R/r) / k^j → ∞` for
every fixed `j` (`R/r = 2^k / 2^ℓ = 2^{k-ℓ}`). -/
theorem tendsto_R_div_rK_div_pow (hρ : ρ.Admissible) (j : ℕ) :
    Tendsto (fun k => ((2 ^ k / rK ρ k : ℕ) : ℝ) / (k : ℝ) ^ j) atTop atTop := by
  -- Eventually `k^{j+1} ≤ R/r`, so `(R/r) / k^j ≥ k → ∞`.
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [AsymK.eventually_pow_le_two_pow_div_rK hρ (j + 1), eventually_gt_atTop 0]
    with k hk hk0
  have hkpos : (0 : ℝ) < (k : ℝ) ^ j := pow_pos (Nat.cast_pos.mpr hk0) j
  rw [le_div_iff₀ hkpos]
  have h : ((k ^ (j + 1) : ℕ) : ℝ) ≤ ((2 ^ k / rK ρ k : ℕ) : ℝ) := Nat.cast_le.mpr hk
  calc (k : ℝ) * (k : ℝ) ^ j = ((k ^ (j + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ k / rK ρ k : ℕ) : ℝ) := h

/-- CONTRACT (Section 7.3 (`sec:main-tables`), eq. (`eq:setup`) is `o(RP)`; Section 7.6 (`sec:main-thm`), eq. (`eq:cutoff`), "so the setup is at most `RP`"), at `k`,
uniformly in the precision: for all constants `C_set, D`, eventually in `k`, every `P'` with
`16k ≤ P' ≤ 64k` satisfies `C_set((R/r)P'^D + rP'^D + P'^D) ≤ RP'` with `R = 2^k`, `r = rK ρ k`. -/
theorem eventually_setupK (hρ : ρ.Admissible) (Cset D : ℕ) :
    ∀ᶠ k in atTop, ∀ P' : ℕ, 16 * k ≤ P' → P' ≤ 64 * k →
      Cset * (2 ^ k / rK ρ k * P' ^ D + rK ρ k * P' ^ D + P' ^ D) ≤ 2 ^ k * P' := by
  -- With `A = C_set·64^D·k^D ≥ C_set·P'^D`: eventually `3A ≤ k^{D+1} ≤ r` and `3A ≤ R/r`
  -- (`k ≥ 3C_set·64^D`); then `(R/r)·r ≤ R` and `R/r ≤ R` give `A(R/r + r + 1) ≤ R ≤ RP'`.
  filter_upwards [AsymK.eventually_pow_le_rK hρ (D + 1),
    AsymK.eventually_pow_le_two_pow_div_rK hρ (D + 1),
    eventually_ge_atTop (3 * Cset * 64 ^ D), eventually_ge_atTop 1] with k hr hq hkC hk1
  intro P' hP1 hP2
  have hPD : Cset * P' ^ D ≤ Cset * (64 ^ D * k ^ D) := by
    have h := Nat.pow_le_pow_left hP2 D
    rw [mul_pow] at h
    exact Nat.mul_le_mul_left Cset h
  have h3A : 3 * (Cset * (64 ^ D * k ^ D)) ≤ k ^ (D + 1) := by
    have h := Nat.mul_le_mul_right (k ^ D) hkC
    calc 3 * (Cset * (64 ^ D * k ^ D)) = 3 * Cset * 64 ^ D * k ^ D := by ring
      _ ≤ k * k ^ D := h
      _ = k ^ (D + 1) := by ring
  exact AsymK.setup_arith (Nat.div_mul_le_self _ _) (Nat.div_le_self _ _) (le_trans h3A hr)
    (le_trans h3A hq) hPD (by omega)

end SubNLogN.Math.Cost
