import WP.W7k3.SeriesSpec
import WP.W7k2.Arith

/-!
# WP.W7k3.SerMath — arithmetic facts for the series sub-kernel

* `fits_natAbs_lt`: the snapshot's width predicate `FitsSignedScalarWord w z` is `|z| < 2^(w-1)`.
* `natAbs_divRound_le`: rounding division by a positive integer does not increase the magnitude, so
  the next series term `a_{k+1}` is bounded by the step numerator `a_k·c·f k`.
* `SK.g_ge`, `SK.g1_le`, `SK.g2_le`, `SK.fac_le`: the step factors of an admissible kind.
* `serW_of`: the snapshot's per-call-site predicate, restated on `serState` as magnitude bounds.
* `bl_lt`, `bl_add`, `bl_fac`: the resulting operand sizes, all `≤ W + 1`.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

theorem fits_natAbs_lt {w : ℕ} {z : ℤ} (h : IntMul.FitsSignedScalarWord w z) :
    z.natAbs < 2 ^ (w - 1) := by
  unfold IntMul.FitsSignedScalarWord at h
  have h1 : ((z.natAbs : ℕ) : ℤ) < 2 ^ (w - 1) := by rwa [Int.natCast_natAbs]
  exact_mod_cast h1

/-- W6a's `divRoundRatInt` is the snapshot's. -/
theorem dr_eq (x y : ℤ) : divRoundRatInt x y = IntMul.divRoundRatInt x y := rfl

theorem natAbs_divRound_le (x : ℤ) {y : ℤ} (hy : 0 < y) :
    (divRoundRatInt x y).natAbs ≤ x.natAbs := by
  unfold divRoundRatInt
  rw [if_pos hy]
  have h2y : 0 < 2 * y := by omega
  have hdm := Int.mul_ediv_add_emod (2 * x + y) (2 * y)
  have hr0 := Int.emod_nonneg (2 * x + y) (ne_of_gt h2y)
  have hr1 := Int.emod_lt_of_pos (2 * x + y) h2y
  generalize (2 * x + y) / (2 * y) = q at hdm ⊢
  generalize (2 * x + y) % (2 * y) = r at hdm hr0 hr1
  rcases le_or_gt 0 x with hx | hx
  · have hq0 : 0 ≤ q := by
      by_contra hq
      have h1 : 2 * y * q ≤ 2 * y * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    have hqx : q ≤ x := by
      by_contra hq
      have h1 : 2 * y * (x + 1) ≤ 2 * y * q := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h2 : x ≤ x * y := by nlinarith
      nlinarith
    have : (q.natAbs : ℤ) ≤ (x.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonneg hq0, abs_of_nonneg hx]
      exact hqx
    exact_mod_cast this
  · have hq0 : q ≤ 0 := by
      by_contra hq
      have h1 : 2 * y * 1 ≤ 2 * y * q := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    have hqx : x ≤ q := by
      by_contra hq
      have h1 : 2 * y * q ≤ 2 * y * (x - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h2 : x * y ≤ x := by nlinarith
      nlinarith
    have : (q.natAbs : ℤ) ≤ (x.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonpos hq0, abs_of_neg hx]
      omega
    exact_mod_cast this

/-! ## Step factors of an admissible kind -/

theorem SK.g1_le (κ : SK) (hκ : κ.OK) (k : ℕ) : κ.gγ * k + κ.gδ ≤ κ.g k := by
  obtain ⟨-, -, h3, -⟩ := hκ
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem SK.g2_le (κ : SK) (hκ : κ.OK) (k : ℕ) : κ.gε * k + κ.gζ ≤ κ.g k := by
  obtain ⟨-, h2, -⟩ := hκ
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem SK.g_ge (κ : SK) (hκ : κ.OK) (k : ℕ) : k + 1 ≤ κ.g k := by
  have h := SK.g1_le κ hκ k
  obtain ⟨h1, h2, -⟩ := hκ
  have : k ≤ κ.gγ * k := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem SK.fac_le (κ : SK) (hκ : κ.OK) {k n : ℕ} (hk : k ≤ n) :
    κ.f k ≤ 3 * n + 3 ∧ κ.gγ * k + κ.gδ ≤ 3 * n + 3 ∧ κ.gε * k + κ.gζ ≤ 3 * n + 3 := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9⟩ := hκ
  have e1 : κ.fα * k ≤ 3 * n := Nat.mul_le_mul h4 hk
  have e2 : κ.gγ * k ≤ 3 * n := Nat.mul_le_mul h6 hk
  have e3 : κ.gε * k ≤ 3 * n := Nat.mul_le_mul h8 hk
  unfold SK.f
  omega

/-! ## The snapshot's width predicate on `serState` -/

/-- `RecurrenceCallSitesWidthSound`, restated on `serState` as magnitude bounds `< 2^(W-1)`. -/
theorem serW_of {W : ℕ} {a0 c : ℤ} {d n : ℕ} {f g : ℕ → ℕ}
    (h : IntMul.RecurrenceCallSitesWidthSound W a0 c d f g n) :
    c.natAbs < 2 ^ (W - 1) ∧ d < 2 ^ (W - 1) ∧ ∀ k < n,
      (serState a0 c d f g k).1.natAbs < 2 ^ (W - 1) ∧
      (serState a0 c d f g k).2.natAbs < 2 ^ (W - 1) ∧
      f k < 2 ^ (W - 1) ∧ g k < 2 ^ (W - 1) ∧
      ((serState a0 c d f g k).1 * c).natAbs < 2 ^ (W - 1) ∧
      ((serState a0 c d f g k).1 * c * (f k : ℤ)).natAbs < 2 ^ (W - 1) ∧
      g k * d < 2 ^ (W - 1) := by
  obtain ⟨hc, hd, hk⟩ := h
  refine ⟨fits_natAbs_lt hc, by simpa using fits_natAbs_lt hd, fun k hkn => ?_⟩
  have h' := hk k hkn
  simp only [runRecurrenceSeriesCosted_fst_eq] at h'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h'
  refine ⟨fits_natAbs_lt h1, fits_natAbs_lt h2, by simpa using fits_natAbs_lt h3,
    by simpa using fits_natAbs_lt h4, fits_natAbs_lt h5, fits_natAbs_lt h6, ?_⟩
  have := fits_natAbs_lt h7
  rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at this

/-! ## Operand sizes -/

theorem bl_lt {W x : ℕ} (h : x < 2 ^ (W - 1)) : bitLen x ≤ W + 1 :=
  bitLen_le_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem bl_add {W x y : ℕ} (hx : x < 2 ^ (W - 1)) (hy : y < 2 ^ (W - 1)) :
    bitLen (x + y) ≤ W + 1 := by
  apply bitLen_le_of_lt
  have h1 : 2 ^ (W - 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
  omega

theorem bl_fac {W n x : ℕ} (hW : 1 ≤ W) (hn : n < 2 ^ (W - 1)) (hx : x ≤ 3 * n + 3) :
    bitLen x ≤ W + 1 := by
  apply bitLen_le_of_lt
  obtain ⟨V, rfl⟩ : ∃ V, W = V + 1 := ⟨W - 1, by omega⟩
  have h2 : 2 ^ (V + 1 + 1) = 4 * 2 ^ V := by ring
  rw [show V + 1 - 1 = V by omega] at hn
  omega

#assert_std_axioms fits_natAbs_lt dr_eq natAbs_divRound_le SK.g1_le SK.g2_le SK.g_ge SK.fac_le
  serW_of bl_lt bl_add bl_fac

end WP.W7k3
