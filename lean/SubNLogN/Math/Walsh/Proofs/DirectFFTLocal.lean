import SubNLogN.Math.Walsh.DirectFFT

/-!
# Direct FFT: local error estimates (round protocol, one last-axis DIF level)

Paper: proof of Theorem 6.5, `thm:direct-fft`, eq. (`eq:round-protocol`).

* `round_local_error : RoundLocalErrorStmt` (proof of Theorem 6.5 (`thm:direct-fft`), eq. (`eq:round-protocol`)): for a disk array `z` on
  the `P`-grid, the round protocol `Q_P(D̃ Q_P(H_T z))` returns a disk array on the `P`-grid within
  `6 · 2^{-P}` of the exact round `D_ζ H_T z`. Pointwise, with `h = (H_T z)(x)_k` (`|h| ≤ 1`,
  since `H_T` is an `∞`-norm contraction, `norm_hT_apply_le`) and `u = 2^{-P}`:
  `Q_P(θ̃ Q_P h) - ζ h = [Q_P(θ̃ Q_P h) - θ̃ Q_P h] + (θ̃ - ζ) Q_P h + ζ (Q_P h - h)`,
  of modulus `< √2 u + 2u + √2 u < 6u` (`DirectFFTLocal.round_scalar`).
* `last_axis_level_error : LastAxisLevelErrorStmt` (proof of Theorem 6.5 (`thm:direct-fft`)): one rounded DIF
  level; an upper output carries one truncation (`< √2 u`), a lower output the same three-term
  estimate with the table phase `θ̃_{2^{s+1} j}` and the exact phase `θ_{2^{s+1} j}` of
  `PhaseTableSpec` (index `2^{s+1} j < 2 · 2^ℓ`).

Local scalar rounding and phase-product error estimates; helpers live in the namespace
`SubNLogN.Math.Walsh.DirectFFTLocal` to avoid name clashes.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

namespace DirectFFTLocal

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 :=
  (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).2 (by norm_num)

theorem norm_theta (r j : ℕ) : ‖theta r j‖ = 1 := IntMul.norm_stdChar _

/-- Scalar core of the round protocol: for `|h| ≤ 1`, `|θ̃| ≤ 1`, `|ζ| = 1` and
`|θ̃ - ζ| < 2 · 2^{-P}`, the value `Q_P(θ̃ Q_P(h))` lies in `𝔻_P` and is within `6 · 2^{-P}`
of `ζ h`. -/
theorem round_scalar {P : ℕ} {h θt ζ : ℂ} (hh : ‖h‖ ≤ 1) (hθ : ‖θt‖ ≤ 1) (hζ : ‖ζ‖ = 1)
    (hd : ‖θt - ζ‖ < 2 * gridUnit P) :
    OnDiskGrid P (truncC P (θt * truncC P h)) ∧
      ‖truncC P (θt * truncC P h) - ζ * h‖ < 6 * gridUnit P := by
  have hh'1 : ‖truncC P h‖ ≤ 1 := (norm_truncC_le P h).trans hh
  have hh'2 : ‖truncC P h - h‖ < Real.sqrt 2 * gridUnit P := norm_truncC_sub_lt P h
  have hp1 : ‖θt * truncC P h‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hθ (norm_nonneg _) hh'1
  refine ⟨truncC_mem_diskGrid P _ hp1, ?_⟩
  have e1 := norm_truncC_sub_lt P (θt * truncC P h)
  have e2 : ‖(θt - ζ) * truncC P h‖ ≤ ‖θt - ζ‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hh'1
  have e3 : ‖ζ * (truncC P h - h)‖ = ‖truncC P h - h‖ := by rw [norm_mul, hζ, one_mul]
  have hu := gridUnit_pos P
  have hs : Real.sqrt 2 * gridUnit P < 2 * gridUnit P :=
    mul_lt_mul_of_pos_right sqrt_two_lt_two hu
  have key : truncC P (θt * truncC P h) - ζ * h =
      (truncC P (θt * truncC P h) - θt * truncC P h) + (θt - ζ) * truncC P h +
        ζ * (truncC P h - h) := by ring
  rw [key]
  have h3 := norm_add₃_le (a := truncC P (θt * truncC P h) - θt * truncC P h)
    (b := (θt - ζ) * truncC P h) (c := ζ * (truncC P h - h))
  linarith

/-- A record array all of whose coefficients have modulus `< B` has sup norm `< B`. -/
theorem norm_lt_of_forall {α : Type} [Fintype α] {r : ℕ} {z : RArr α r} {B : ℝ} (hB : 0 < B)
    (h : ∀ x k, ‖z x k‖ < B) : ‖z‖ < B :=
  (pi_norm_lt_iff hB).2 fun x => (pi_norm_lt_iff hB).2 fun k => h x k

end DirectFFTLocal

/-- **Local round estimate** (proof of Theorem 6.5 (`thm:direct-fft`)). -/
theorem round_local_error : RoundLocalErrorStmt := by
  intro m r P T θt ζ z hz hθ hζ hd
  have key : ∀ x k, OnDiskGrid P (truncC P (θt x * truncC P (hT T z x k))) ∧
      ‖truncC P (θt x * truncC P (hT T z x k)) - ζ x * hT T z x k‖ < 6 * gridUnit P :=
    fun x k => DirectFFTLocal.round_scalar (norm_hT_apply_le T z (fun y k' => (hz y k').2) x k)
      (hθ x) (hζ x) (hd x)
  exact ⟨fun x k => (key x k).1,
    DirectFFTLocal.norm_lt_of_forall (mul_pos (by norm_num) (gridUnit_pos P))
      fun x k => (key x k).2⟩

/-- **Local last-axis estimate** (proof of Theorem 6.5 (`thm:direct-fft`)). -/
theorem last_axis_level_error : LastAxisLevelErrorStmt := by
  intro P ℓ s θt w hs htab hw
  have hw1 : ∀ i, ‖getCoeff w i‖ ≤ 1 := by
    intro i; unfold getCoeff; split_ifs
    · exact (hw _).2
    · simp
  have hu := gridUnit_pos P
  have hh : ∀ a b : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖(a + b) / 2‖ ≤ 1 ∧ ‖(a - b) / 2‖ ≤ 1 := by
    intro a b ha hb
    have h1 := norm_add_le a b
    have h2 := norm_sub_le a b
    rw [norm_div, norm_div, Complex.norm_ofNat]
    constructor <;> linarith
  have hpow2 : 2 ^ (s + 1) * 2 ^ (ℓ - s - 1) = 2 ^ ℓ := by
    rw [← pow_add]; congr 1; omega
  have key : ∀ k : Fin (2 ^ ℓ), OnDiskGrid P (difLevel P ℓ s θt w k) ∧
      ‖difLevel P ℓ s θt w k - difLevelExact ℓ s w k‖ < 6 * gridUnit P := by
    intro k
    simp only [difLevel, difLevelExact]
    split_ifs with hk
    · have hc := (hh _ _ (hw1 k) (hw1 ((k : ℕ) + 2 ^ (ℓ - s - 1)))).1
      refine ⟨truncC_mem_diskGrid P _ hc, ?_⟩
      have := norm_truncC_sub_lt P ((getCoeff w k + getCoeff w ((k : ℕ) + 2 ^ (ℓ - s - 1))) / 2)
      have hs2 : Real.sqrt 2 * gridUnit P < 6 * gridUnit P :=
        mul_lt_mul_of_pos_right (by linarith [DirectFFTLocal.sqrt_two_lt_two]) hu
      linarith
    · have hmod : (k : ℕ) % 2 ^ (ℓ - s) < 2 ^ (ℓ - s) := Nat.mod_lt _ (by positivity)
      have hpow : 2 ^ (ℓ - s) = 2 * 2 ^ (ℓ - s - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hj1 : (k : ℕ) % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1) < 2 ^ (ℓ - s - 1) := by omega
      have hj : 2 ^ (s + 1) * ((k : ℕ) % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1)) < 2 * 2 ^ ℓ := by
        have := mul_lt_mul_of_pos_left hj1 (show 0 < 2 ^ (s + 1) by positivity)
        rw [hpow2] at this
        omega
      obtain ⟨-, hθ1, hθ2⟩ := htab _ hj
      exact DirectFFTLocal.round_scalar (hh _ _ (hw1 _) (hw1 k)).2 hθ1
        (DirectFFTLocal.norm_theta _ _) hθ2
  exact ⟨fun k => (key k).1, (pi_norm_lt_iff (mul_pos (by norm_num) hu)).2 fun k => (key k).2⟩

end SubNLogN.Math.Walsh
