import Mathlib
import SubNLogN.Math.Cost.Family

/-!
# Cost: integer facts about the parameters at a transform exponent `K0`

For the `κ = 2^{-46}` row (`row46`: `ε = 1/15`, `c = 2^{-50}`), the dimension `d = dK row46 K0`
is the largest `y` with `y^15 ≤ K0` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)) and the chunk width
`K = KK row46 K0` is the largest `y` with `y^{2^50} ≤ d`. This file records the elementary
integer consequences used by the W8 instances of the cost theorem (`WalshW8.lean`) and by the
eventual Walsh eligibility (`WalshOKW8.lean`):
* `dK46_spec`: `d^15 ≤ K0 < (d+1)^15`; `two_le_dK46`: `2^15 ≤ K0 → 2 ≤ d`;
* `dK_mul_lK_bounds` (any row): `1 ≤ d → K0 ≤ dℓ < K0 + d` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)); `lK_le`: `ℓ ≤ K0`;
* `dK46_lt_lK46`: `2^15 ≤ K0 → d < ℓ`; `KK46_bounds`: `1 ≤ d → 1 ≤ K ≤ d` (via the
  exponent-generic `one_le_floorRatPow`, `floorRatPow_one_le`).

All statements are proved (no `sorry`).
-/

namespace SubNLogN.Math.Cost

/-- For the `κ = 2^{-46}` row, `d = dK row46 K0` satisfies `d^15 ≤ K0 < (d+1)^15`
(`d = ⌊K0^{1/15}⌋` by integer comparison, Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
theorem dK46_spec (K0 : ℕ) : dK row46 K0 ^ 15 ≤ K0 ∧ K0 < (dK row46 K0 + 1) ^ 15 := by
  have hd : dK row46 K0 = floorRatPow K0 1 15 := rfl
  rw [hd]
  have h := fun y => le_floorRatPow_iff (x := K0) (e₁ := 1) (e₂ := 15) (by norm_num) y
  refine ⟨by simpa using (h (floorRatPow K0 1 15)).1 le_rfl, ?_⟩
  by_contra hc
  have h2 := (h (floorRatPow K0 1 15 + 1)).2 (by simpa using not_lt.1 hc)
  omega

/-- For the `κ = 2^{-46}` row, `2^15 ≤ K0` implies `2 ≤ d`. -/
theorem two_le_dK46 {K0 : ℕ} (h : 2 ^ 15 ≤ K0) : 2 ≤ dK row46 K0 := by
  have hd : dK row46 K0 = floorRatPow K0 1 15 := rfl
  rw [hd, le_floorRatPow_iff (by norm_num)]
  simpa using h

/-- For any row, if `1 ≤ d` then `K0 ≤ dℓ < K0 + d` (`ℓ = ⌈K0/d⌉`; Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`),
"`0 ≤ dℓ - k < d`"). -/
theorem dK_mul_lK_bounds (ρ : RowExps) (K0 : ℕ) (hd : 1 ≤ dK ρ K0) :
    K0 ≤ dK ρ K0 * lK ρ K0 ∧ dK ρ K0 * lK ρ K0 < K0 + dK ρ K0 := by
  have hl : lK ρ K0 = (K0 + dK ρ K0 - 1) / dK ρ K0 := rfl
  rw [hl]
  have h1 := Nat.div_add_mod (K0 + dK ρ K0 - 1) (dK ρ K0)
  have h2 := Nat.mod_lt (K0 + dK ρ K0 - 1) (by omega : dK ρ K0 > 0)
  constructor <;> omega

/-- For any row, if `1 ≤ d` then `ℓ ≤ K0`. -/
theorem lK_le (ρ : RowExps) (K0 : ℕ) (hd : 1 ≤ dK ρ K0) : lK ρ K0 ≤ K0 := by
  have h := (dK_mul_lK_bounds ρ K0 hd).2
  by_contra hc
  have h3 : dK ρ K0 * (K0 + 1) ≤ dK ρ K0 * lK ρ K0 := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- For the `κ = 2^{-46}` row, `2^15 ≤ K0` implies `d < ℓ` (if `ℓ ≤ d` then
`K0 ≤ dℓ ≤ d² < d^15 ≤ K0`). -/
theorem dK46_lt_lK46 {K0 : ℕ} (h : 2 ^ 15 ≤ K0) : dK row46 K0 < lK row46 K0 := by
  have hd2 := two_le_dK46 h
  have hb := dK_mul_lK_bounds row46 K0 (by omega)
  have hs := (dK46_spec K0).1
  by_contra hc
  have h1 : dK row46 K0 * lK row46 K0 ≤ dK row46 K0 * dK row46 K0 :=
    Nat.mul_le_mul_left _ (not_lt.1 hc)
  have h2 : dK row46 K0 * dK row46 K0 < dK row46 K0 ^ 15 := by
    rw [← pow_two]
    exact Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

/-- For `0 < e` and `1 ≤ x`: `1 ≤ ⌊x^{1/e}⌋` (integer comparison). Stated for a variable exponent
`e` so that instances such as `e = 2^50` never make the kernel evaluate `1 ^ e`. -/
theorem one_le_floorRatPow {x e : ℕ} (he : 0 < e) (hx : 1 ≤ x) : 1 ≤ floorRatPow x 1 e := by
  rw [le_floorRatPow_iff he, one_pow, pow_one]
  exact hx

/-- For `0 < e`: `⌊x^{1/e}⌋ ≤ x` (integer comparison). -/
theorem floorRatPow_one_le {x e : ℕ} (he : 0 < e) : floorRatPow x 1 e ≤ x := by
  have h1 := (le_floorRatPow_iff (x := x) (e₁ := 1) he (floorRatPow x 1 e)).1 le_rfl
  rw [pow_one] at h1
  exact le_trans (Nat.le_self_pow (by omega) _) h1

/-- For the `κ = 2^{-46}` row, if `1 ≤ d` then the chunk width satisfies `1 ≤ K ≤ d`
(`K = ⌊d^{2^{-50}}⌋` by integer comparison). -/
theorem KK46_bounds {K0 : ℕ} (hd : 1 ≤ dK row46 K0) :
    1 ≤ KK row46 K0 ∧ KK row46 K0 ≤ dK row46 K0 := by
  have hK : KK row46 K0 = floorRatPow (dK row46 K0) 1 (2 ^ 50) := rfl
  rw [hK]
  exact ⟨one_le_floorRatPow (by positivity) hd, floorRatPow_one_le (by positivity)⟩

end SubNLogN.Math.Cost
