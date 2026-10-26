import Contracts.W6
import Contracts.W9.Common
import IntMulTM.SpecFacts

/-!
# WP.W9fW.Basic — magnitude bounds for one reciprocal (Barrett) step

* `abs_divRoundRatInt_le`: for `d > 0` and `|x| < P` (`P ≥ 0`), `|divRoundRatInt x d| ≤ P`.
* `recStepBarrett_magLe`: with the column reciprocal `μ = ⌊2^H / a⌋`, `a > 0`, and the Barrett
  dividend bound `W8.NumBound H (W8.recNum q y c z)`, both coordinates of
  `W8.recStepBarrett q H μ a c y z` have magnitude `≤ 2^H` (the step equals `divRoundRatInt N a`
  by `W8.divRoundBarrett_exact`).
* `MagLe H z` (both coordinates `≤ 2^H` in magnitude) implies `W9.EntryW (H + 1) z`.
* `read1D` helpers for `#[x]` and `arr.push x`, and `ArrW` from `read1D` bounds.
-/

namespace WP.W9fW

open IntMul IntMulTM.Contracts TMFw.Contracts

/-- Both coordinates have magnitude at most `2^H`. -/
def MagLe (H : ℕ) (z : ℤ × ℤ) : Prop :=
  |z.1| ≤ ((2 ^ H : ℕ) : ℤ) ∧ |z.2| ≤ ((2 ^ H : ℕ) : ℤ)

theorem magLe_zero (H : ℕ) : MagLe H (0, 0) := by
  have hP : (0 : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := by positivity
  exact ⟨(abs_zero : |(0 : ℤ)| = 0).le.trans hP, (abs_zero : |(0 : ℤ)| = 0).le.trans hP⟩

/-- `|x| ≤ 2^H` gives `bitLen |x| ≤ H + 1` (`bitLen = Nat.size`). -/
theorem bitLen_natAbs_le_succ {x : ℤ} {H : ℕ} (h : |x| ≤ ((2 ^ H : ℕ) : ℤ)) :
    bitLen x.natAbs ≤ H + 1 := by
  rw [Int.abs_eq_natAbs] at h
  have h1 : x.natAbs ≤ 2 ^ H := by exact_mod_cast h
  have e : bitLen x.natAbs = Nat.size x.natAbs := IntMulTM.length_encodeNat _
  rw [e]
  exact Nat.size_le.2 (lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self H)))

theorem entryW_of_magLe {H : ℕ} {z : ℤ × ℤ} (h : MagLe H z) : W9.EntryW (H + 1) z :=
  ⟨bitLen_natAbs_le_succ h.1, bitLen_natAbs_le_succ h.2⟩

/-- **Rounded division does not grow the magnitude bound.** -/
theorem abs_divRoundRatInt_le {x d P : ℤ} (hd : 0 < d) (hP : 0 ≤ P) (hx : |x| < P) :
    |divRoundRatInt x d| ≤ P := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hx
  have h2d : 0 < 2 * d := by omega
  have hk : 0 ≤ P * (d - 1) := mul_nonneg hP (by omega)
  unfold divRoundRatInt
  rw [if_pos hd, abs_le]
  constructor
  · rw [Int.le_ediv_iff_mul_le h2d]
    nlinarith
  · have h3 : (2 * x + d) / (2 * d) < P + 1 := by
      rw [Int.ediv_lt_iff_lt_mul h2d]
      nlinarith
    omega

/-- **One reciprocal step**: magnitudes stay `≤ 2^H`. -/
theorem recStepBarrett_magLe (q H : ℕ) (a c : ℤ) (y z : ℤ × ℤ) (ha : 0 < a)
    (hN : W8.NumBound H (W8.recNum q y c z)) :
    MagLe H (W8.recStepBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c y z) := by
  obtain ⟨h1, h2⟩ := hN
  have hP : (0 : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := by positivity
  refine ⟨?_, ?_⟩
  · show |W8.divRoundBarrett H (((2 ^ H : ℕ) : ℤ) / a) (W8.recNum q y c z).1 a| ≤ _
    rw [W8.divRoundBarrett_exact _ _ _ ha h1]
    exact abs_divRoundRatInt_le ha hP h1
  · show |W8.divRoundBarrett H (((2 ^ H : ℕ) : ℤ) / a) (W8.recNum q y c z).2 a| ≤ _
    rw [W8.divRoundBarrett_exact _ _ _ ha h2]
    exact abs_divRoundRatInt_le ha hP h2

theorem recStepBarrett_entryW (q H : ℕ) (a c : ℤ) (y z : ℤ × ℤ) (ha : 0 < a)
    (hN : W8.NumBound H (W8.recNum q y c z)) :
    W9.EntryW (H + 1) (W8.recStepBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c y z) :=
  entryW_of_magLe (recStepBarrett_magLe q H a c y z ha hN)

/-! ## `read1D` helpers -/

theorem read1D_push_cases (arr : Array (ℤ × ℤ)) (x : ℤ × ℤ) (k : ℕ) :
    read1D (arr.push x) k = read1D arr k ∨ read1D (arr.push x) k = x := by
  by_cases hk : k < arr.size + 1
  · rw [read1D_push arr x k hk]
    by_cases hlt : k < arr.size
    · left
      rw [if_pos hlt]
    · right
      rw [if_neg hlt]
  · left
    have h1 : ¬ k < (arr.push x).size := by
      rw [Array.size_push]
      exact hk
    have h2 : ¬ k < arr.size := by omega
    unfold read1D
    rw [dif_neg h1, dif_neg h2]

theorem read1D_singleton_cases (x : ℤ × ℤ) (k : ℕ) :
    read1D #[x] k = x ∨ read1D #[x] k = (0, 0) := by
  unfold read1D
  by_cases hk : k < #[x].size
  · left
    rw [dif_pos hk]
    have hs : #[x].size = 1 := rfl
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  · right
    rw [dif_neg hk]
    rfl

theorem magLe_read1D_singleton {H : ℕ} {x : ℤ × ℤ} (hx : MagLe H x) (k : ℕ) :
    MagLe H (read1D #[x] k) := by
  rcases read1D_singleton_cases x k with h | h <;> rw [h]
  · exact hx
  · exact magLe_zero H

theorem magLe_read1D_push {H : ℕ} {arr : Array (ℤ × ℤ)} {x : ℤ × ℤ}
    (harr : ∀ k, MagLe H (read1D arr k)) (hx : MagLe H x) (k : ℕ) :
    MagLe H (read1D (arr.push x) k) := by
  rcases read1D_push_cases arr x k with h | h <;> rw [h]
  · exact harr k
  · exact hx

/-- `read1D` bounds for every index give `W9.ArrW`. -/
theorem arrW_of_read1D {w : ℕ} {arr : Array (ℤ × ℤ)} (h : ∀ k, W9.EntryW w (read1D arr k)) :
    W9.ArrW w arr := by
  show ∀ z ∈ arr.toList, W9.EntryW w z
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hz
  have hi' : i < arr.size := hi
  have h1 := h i
  unfold read1D at h1
  rw [dif_pos hi'] at h1
  exact h1

#assert_std_axioms magLe_zero bitLen_natAbs_le_succ entryW_of_magLe abs_divRoundRatInt_le
  recStepBarrett_magLe recStepBarrett_entryW read1D_push_cases read1D_singleton_cases
  magLe_read1D_singleton magLe_read1D_push arrW_of_read1D

end WP.W9fW
