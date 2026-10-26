/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Machine.Contracts.Arith
import SubNLogN.Math.Walsh.IntForms.Address

/-!
# K4-TWIDDLE, value level (`Machine/FFT/TwiddleMath.lean`)

**Scope (honest summary).** Value-level facts for `TwiddlePassStmt` (`Machine/Contracts/FFT.lean`),
all proved (no `sorry`); no machine program here.
* `gridInt_truncC_mul`: for `t, c` on the `q`-grid, the numerators of `Q_q(t·c)` are
  `cmulTruncC q (num c) (num t)` (exact product, then truncation toward zero by `2^q`;
  Lemma 6.2, `lem:disk-product`).
* `encCube_twiddle`: the twiddle pass on the stored data is one `cmulTruncBcast` with the
  per-record phases `twPhases` (Section 6.3, `sec:direct-fft-twiddle`, and eq. `eq:round-protocol`).
* `twPhases_eq`: the phase of record `n` is `θ̃_{2·twJNat ℓ K a v n}` (via
  `IntForms.twJNat_eq`).
* (The fitting, shape and volume facts for the `CMulTruncBcastStmt` call are in
  `Machine/FFT/TwiddleFacts.lean`.)

All names live in `SubNLogN.Machine.FFT.TwiddleAux`.
-/

namespace SubNLogN.Machine.FFT.TwiddleAux

open SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## Truncation of an integer quotient -/

theorem floor_intCast_div_natCast_real (m : ℤ) (d : ℕ) :
    ⌊(m : ℝ) / (d : ℝ)⌋ = m / (d : ℤ) := by
  have h : ((m : ℝ) / (d : ℝ)) = (((m : ℚ) / (d : ℚ) : ℚ) : ℝ) := by push_cast; ring
  rw [h, Rat.floor_cast, Rat.floor_intCast_div_natCast]

/-- Truncation toward zero of `m / d` is `Int.tdiv m d` (`d > 0`). -/
theorem truncInt_intCast_div (m : ℤ) (d : ℕ) (hd : 0 < d) :
    truncInt ((m : ℝ) / (d : ℝ)) = m.tdiv d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold truncInt
  by_cases hm : 0 ≤ m
  · have hx : (0 : ℝ) ≤ (m : ℝ) / d := div_nonneg (by exact_mod_cast hm) hd'.le
    rw [if_pos hx, floor_intCast_div_natCast_real, Int.tdiv_eq_ediv_of_nonneg hm]
  · replace hm : m < 0 := not_le.mp hm
    have hx : ¬ (0 : ℝ) ≤ (m : ℝ) / d := by
      rw [not_le]; exact div_neg_of_neg_of_pos (by exact_mod_cast hm) hd'
    rw [if_neg hx]
    have h1 : ((m : ℝ) / d) = -(((-m : ℤ) : ℝ) / d) := by push_cast; ring
    rw [h1, Int.ceil_neg, floor_intCast_div_natCast_real,
      ← Int.tdiv_eq_ediv_of_nonneg (a := -m) (b := (d : ℤ)) (by omega), Int.neg_tdiv, neg_neg]

/-! ## One coefficient -/

theorem gridInt_of_onGrid {q : ℕ} {z : ℂ} {a b : ℤ} (ha : z.re = (a : ℝ) * gridUnit q)
    (hb : z.im = (b : ℝ) * gridUnit q) : gridInt q z = (a, b) := by
  have hu : gridUnit q * (2 : ℝ) ^ q = 1 := by unfold gridUnit; field_simp
  unfold gridInt
  rw [ha, hb, mul_assoc, mul_assoc, hu, mul_one, mul_one, round_intCast, round_intCast]

/-- **One coefficient of the twiddle pass.** For `t, c` on the `q`-grid, the numerators of
`Q_q(t·c)` are `truncShiftC q (cmulC (num c) (num t))` (Lemma 6.2, `lem:disk-product`). -/
theorem gridInt_truncC_mul {q : ℕ} {t c : ℂ} (ht : OnGrid q t) (hc : OnGrid q c) :
    gridInt q (truncC q (t * c)) = cmulTruncC q (gridInt q c) (gridInt q t) := by
  obtain ⟨⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := hc
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩⟩ := ht
  rw [gridInt_of_onGrid hc1 hc2, gridInt_of_onGrid ht1 ht2]
  have hpos : 0 < 2 ^ q := Nat.two_pow_pos q
  have hq : ((2 ^ q : ℕ) : ℝ) = (2 : ℝ) ^ q := by push_cast; ring
  have hu : gridUnit q = ((2 : ℝ) ^ q)⁻¹ := rfl
  have key : ∀ m : ℤ, (m : ℝ) * gridUnit q * gridUnit q * (2 : ℝ) ^ q =
      (m : ℝ) / ((2 ^ q : ℕ) : ℝ) := by
    intro m; rw [hq, hu]; field_simp
  have hre : (t * c).re * (2 : ℝ) ^ q = ((t1 * c1 - t2 * c2 : ℤ) : ℝ) / ((2 ^ q : ℕ) : ℝ) := by
    rw [Complex.mul_re, ht1, ht2, hc1, hc2, ← key]; push_cast; ring
  have him : (t * c).im * (2 : ℝ) ^ q = ((t1 * c2 + t2 * c1 : ℤ) : ℝ) / ((2 ^ q : ℕ) : ℝ) := by
    rw [Complex.mul_im, ht1, ht2, hc1, hc2, ← key]; push_cast; ring
  have hgu : gridUnit q * (2 : ℝ) ^ q = 1 := by rw [hu]; field_simp
  unfold gridInt cmulTruncC truncShiftC cmulC tdivPow
  simp only [truncC_re, truncC_im, truncR]
  rw [hre, him, truncInt_intCast_div _ _ hpos, truncInt_intCast_div _ _ hpos, mul_assoc, hgu,
    mul_one, mul_assoc, hgu, mul_one, round_intCast, round_intCast]
  push_cast
  congr 1 <;> congr 1 <;> ring

/-! ## The whole pass -/

/-- The per-record phases `θ̃_{2J(x)}` of round `v` as stored numerators, in cube order. -/
noncomputable def twPhases (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ) :
    List CInt :=
  (cubeAddrs (addrBits a)).map fun x => gridInt q (θt (2 * twJ ℓ K a v x))

/-- **The twiddle pass on the stored data** (Section 6.3 and eq. `eq:round-protocol`): for a record
array and per-record phases on the `q`-grid, `Q_q(D_f z)` is stored as `cmulTruncBcast`. -/
theorem encCube_truncArr_diagArr {m r q : ℕ} (f : Cube m → ℂ) (z : RArr (Cube m) r)
    (hz : ∀ x k, OnGrid q (z x k)) (hf : ∀ x, OnGrid q (f x)) :
    encCube q (truncArr q (diagArr f z)) =
      cmulTruncBcast q (encCube q z) ((cubeAddrs m).map fun x => gridInt q (f x)) := by
  unfold encCube encArr cmulTruncBcast
  rw [List.zipWith_map_left, List.zipWith_map_right, List.zipWith_self]
  refine List.map_congr_left fun x _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun k _ => ?_
  exact gridInt_truncC_mul (hf x) (hz x k)

/-- The twiddle pass of round `v` on the stored data. -/
theorem encCube_twiddle (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) (hz : ArrOnDiskGrid q z) (hθ : TabOK q ℓ θt) :
    encCube q (truncArr q (diagArr (fun x => θt (2 * twJ ℓ K a v x)) z)) =
      cmulTruncBcast q (encCube q z) (twPhases q ℓ K a v θt) :=
  encCube_truncArr_diagArr _ z (fun x k => (hz x k).1)
    (fun x => (hθ _ (IntForms.two_mul_twJ_lt ℓ K a v x)).1)

/-- The phase of record `n` through the integer form `twJNat` (`IntForms.twJNat_eq`). -/
theorem twPhases_eq (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (hK : 0 < K)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (v : ℕ) (θt : ℕ → ℂ) :
    twPhases q ℓ K a v θt =
      (List.range (2 ^ addrBits a)).map fun n => gridInt q (θt (2 * IntForms.twJNat ℓ K a v n)) := by
  unfold twPhases cubeAddrs
  rw [List.map_map]
  refine List.map_congr_left fun n _ => ?_
  rw [IntForms.twJNat_eq ℓ K a hK ha v n]
  rfl

theorem length_twPhases (q ℓ K : ℕ) {D : ℕ} (a : Fin D → ℕ) (v : ℕ) (θt : ℕ → ℂ) :
    (twPhases q ℓ K a v θt).length = 2 ^ addrBits a := by
  simp [twPhases, cubeAddrs]

end SubNLogN.Machine.FFT.TwiddleAux
