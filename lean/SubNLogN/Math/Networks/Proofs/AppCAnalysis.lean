import SubNLogN.Math.Networks.AppCLayer

/-!
# Proofs of the Appendix A analysis leaves (guard and layer recurrence)

Proves the contracts `GuardGrowthStmt`, `GuardSmallStmt`, `LayerRecurrenceStmt` stated in
`SubNLogN/Math/Networks/AppCLayer.lean` (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)).
No hypotheses are assumed: all three are proved outright.

## Plan

* `GuardGrowthStmt` (Proposition A.11 (`prop:prop14-param`), eq. (`eq:walsh-guard-growth`)). Put `A = m C_dep + 18` (any sign) and
  `d_* = ⌈A⌉₊ + 1`. For `d ≥ d_*` we have `d ≥ 1` and `A ≤ d`; writing `C₁ = 7 + e` with `e ≥ 7 ≥ 1`,
  `A ≤ d ≤ d^e ≤ C₀ d^e` (as `C₀ = guardC0 100 ≥ 1`, by `decide`), hence
  `A d⁷ ≤ C₀ d^e d⁷ = C₀ d^{C₁}`.
* `GuardSmallStmt` (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)). Put `q = 1 − ε C₁ > 0`, `B = C₀ b_d^{C₁} > 0`,
  `P₀ = max 1 (B^{1/q})`. For `P ≥ P₀`: `B = (B^{1/q})^q ≤ P^q`, and from `1 ≤ d ≤ b_d P^ε`,
  `d^{C₁} ≤ (b_d P^ε)^{C₁} = b_d^{C₁} P^{ε C₁}`; so `C₀ d^{C₁} ≤ B P^{ε C₁} ≤ P^q P^{ε C₁} = P`.
* `LayerRecurrenceStmt` (Proposition A.11 (`prop:prop14-param`), eqs. (`eq:walsh-layer-recurrence`)–(`eq:walsh-layer-unrolled`)). Put `r = m^{σ−λ} ∈ [0, 1)` and
  `Y = 2C/(1 − r) ≥ 0` (so `Y r + 2C = Y`); `C' = C + Y`. Given `d, K, F`, put
  `X = C (d^β)^{1−σ} ≥ C`. Invariant, by induction on `j` (for *every* `j`):
  `F j ≤ X (m^j)^σ + Y (m^j)^λ`.
  - `j = 0`: `F 0 ≤ C ≤ X ≤ X + Y`.
  - leaf (`m^{j+1} < d^β`): `C m^{j+1} = C (m^{j+1})^σ (m^{j+1})^{1−σ} ≤ C (m^{j+1})^σ (d^β)^{1−σ}`
    (uses `0 ≤ 1 − σ`, i.e. `σ < λ ≤ 1`).
  - internal (`d^β ≤ E := m^{j+1}`): overhead `(E K)^τ ≤ E^λ` (since
    `K ≤ d^c = (d^β)^{c/β} ≤ E^{c/β}`, so `E K ≤ E^{1+c/β}` and `(E K)^τ ≤ E^{τ(1+c/β)} ≤ E^λ` as
    `E ≥ 1`), and `1 ≤ E^λ`; with `0 ≤ a ≤ m^σ`, `m^σ = m^λ r` and the invariant at `j`:
    `F(j+1) ≤ m^σ (X (m^j)^σ + Y (m^j)^λ) + 2C E^λ = X E^σ + (Y r + 2C) E^λ = X E^σ + Y E^λ`.
  Finally, for `m^k ≤ d`: `(m^k)^σ ≤ d^σ`, `(m^k)^λ ≤ d^λ`, and `X d^σ = C d^{σ+β(1−σ)}`, so
  `F k ≤ C d^{σ+β(1−σ)} + Y d^λ ≤ (C + Y)(d^λ + d^{σ+β(1−σ)} + 1)`.
  (No geometric sums are needed: the `+1` overhead terms are absorbed into `E^λ ≥ 1`.)
-/

namespace SubNLogN.Math.Networks

/-- `C₀ = guardC0 100 ≥ 1` (exact evaluation by `decide`). -/
theorem appc_one_le_guardC0 : 1 ≤ guardC0 100 := by
  decide

/-- Guard growth (Proposition A.11 (`prop:prop14-param`), eq. (`eq:walsh-guard-growth`)): for every real `C_dep` and `C₁ ≥ 14`, there is
`d_*` with `(m C_dep + 18) d⁷ ≤ C₀ d^{C₁}` for all naturals `d ≥ d_*` (here `d_* = ⌈m C_dep + 18⌉₊ + 1`). -/
theorem guardGrowth_holds : GuardGrowthStmt := by
  intro Cdep C1 hC1
  obtain ⟨e, rfl⟩ : ∃ e, C1 = 7 + e := ⟨C1 - 7, by omega⟩
  have he : e ≠ 0 := by omega
  refine ⟨⌈(tripleM 100 : ℝ) * Cdep + 18⌉₊ + 1, fun d hd => ?_⟩
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast le_trans (Nat.le_add_left 1 _) hd
  have hAd : (tripleM 100 : ℝ) * Cdep + 18 ≤ (d : ℝ) := by
    have h : (⌈(tripleM 100 : ℝ) * Cdep + 18⌉₊ : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast le_trans (Nat.le_add_right _ 1) hd
    exact le_trans (Nat.le_ceil _) h
  have hC0 : (1 : ℝ) ≤ (guardC0 100 : ℝ) := by exact_mod_cast appc_one_le_guardC0
  have h1 : (d : ℝ) ≤ (d : ℝ) ^ e := le_self_pow₀ hd1 he
  have h2 : (d : ℝ) ^ e ≤ (guardC0 100 : ℝ) * (d : ℝ) ^ e :=
    le_mul_of_one_le_left (pow_nonneg (le_trans zero_le_one hd1) e) hC0
  have h7 : (0 : ℝ) ≤ (d : ℝ) ^ 7 := pow_nonneg (le_trans zero_le_one hd1) 7
  calc ((tripleM 100 : ℝ) * Cdep + 18) * (d : ℝ) ^ 7
      ≤ ((guardC0 100 : ℝ) * (d : ℝ) ^ e) * (d : ℝ) ^ 7 :=
        mul_le_mul_of_nonneg_right (le_trans hAd (le_trans h1 h2)) h7
    _ = (guardC0 100 : ℝ) * (d : ℝ) ^ (7 + e) := by rw [pow_add]; ring

/-- Guard smallness (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)): for `b_d > 0`, `ε > 0`, `ε C₁ < 1` there is
`P₀` (namely `max 1 ((C₀ b_d^{C₁})^{1/(1−εC₁)})`) such that `C₀ d^{C₁} ≤ P` whenever `P ≥ P₀` and
`1 ≤ d ≤ b_d P^ε`. -/
theorem guardSmall_holds : GuardSmallStmt := by
  intro bd ε C1 hbd hε hεC
  have hC0 : (0 : ℝ) < (guardC0 100 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one appc_one_le_guardC0
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - ε * C1 := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (guardC0 100 : ℝ) * bd ^ C1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; exact mul_pos hC0 (pow_pos hbd _)
  refine ⟨max 1 (B ^ (1 / q)), ?_⟩
  intro P d hP hd hdP
  have hP1 : 1 ≤ P := le_trans (le_max_left _ _) hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hPB : B ^ (1 / q) ≤ P := le_trans (le_max_right _ _) hP
  have hBq : B ≤ P ^ q := by
    have h1 : (B ^ (1 / q)) ^ q = B := by
      rw [← Real.rpow_mul hB0.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
    calc B = (B ^ (1 / q)) ^ q := h1.symm
      _ ≤ P ^ q := Real.rpow_le_rpow (Real.rpow_nonneg hB0.le _) hPB hq0.le
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hdC : d ^ C1 ≤ bd ^ C1 * P ^ (ε * C1) := by
    calc d ^ C1 ≤ (bd * P ^ ε) ^ C1 := pow_le_pow_left₀ hd0 hdP C1
      _ = bd ^ C1 * P ^ (ε * C1) := by
        rw [mul_pow, ← Real.rpow_natCast (P ^ ε), ← Real.rpow_mul hP0.le]
  calc (guardC0 100 : ℝ) * d ^ C1 ≤ (guardC0 100 : ℝ) * (bd ^ C1 * P ^ (ε * C1)) :=
        mul_le_mul_of_nonneg_left hdC hC0.le
    _ = B * P ^ (ε * C1) := by rw [hB]; ring
    _ ≤ P ^ q * P ^ (ε * C1) := mul_le_mul_of_nonneg_right hBq (Real.rpow_nonneg hP0.le _)
    _ = P := by rw [← Real.rpow_add hP0, hq]; norm_num

/-- Internal-node overhead (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)): if `0 ≤ d`, `0 ≤ K ≤ d^c`, `1 ≤ E`,
`d^β ≤ E`, `β > 0`, `c, τ ≥ 0` and `τ(1 + c/β) ≤ λ`, then `(E K)^τ ≤ E^λ`. -/
theorem appc_overhead_le {d K E β c τ lam : ℝ} (hd : 0 ≤ d) (hK : 0 ≤ K) (hKd : K ≤ d ^ c)
    (hE : 1 ≤ E) (hdE : d ^ β ≤ E) (hβ : 0 < β) (hc : 0 ≤ c) (hτ : 0 ≤ τ)
    (hlam : τ * (1 + c / β) ≤ lam) : (E * K) ^ τ ≤ E ^ lam := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hcβ : 0 ≤ c / β := div_nonneg hc hβ.le
  have hβc : β * (c / β) = c := by field_simp
  have hK' : K ≤ E ^ (c / β) := by
    calc K ≤ d ^ c := hKd
      _ = (d ^ β) ^ (c / β) := by rw [← Real.rpow_mul hd, hβc]
      _ ≤ E ^ (c / β) := Real.rpow_le_rpow (Real.rpow_nonneg hd _) hdE hcβ
  have h2 : E * K ≤ E ^ (1 + c / β) := by
    rw [Real.rpow_add hE0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hK' hE0.le
  calc (E * K) ^ τ ≤ (E ^ (1 + c / β)) ^ τ :=
        Real.rpow_le_rpow (mul_nonneg hE0.le hK) h2 hτ
    _ = E ^ (τ * (1 + c / β)) := by
        rw [← Real.rpow_mul hE0.le]
        congr 1
        ring
    _ ≤ E ^ lam := Real.rpow_le_rpow_of_exponent_le hE hlam

/-- Layer recurrence (Proposition A.11 (`prop:prop14-param`), eqs. (`eq:walsh-layer-recurrence`)–(`eq:walsh-layer-unrolled`)). Under the hypotheses of
`LayerRecurrenceStmt` the constant `C' = C + 2C/(1 − m^{σ−λ})` works: every level `k` with `m^k ≤ d`
has `F k ≤ C' (d^λ + d^{σ+β(1−σ)} + 1)`. The proof shows, by induction on `j`, the invariant
`F j ≤ X (m^j)^σ + Y (m^j)^λ` for all `j`, with `X = C (d^β)^{1−σ}` and `Y = 2C/(1 − m^{σ−λ})`. -/
theorem layerRecurrence_holds : LayerRecurrenceStmt := by
  intro m a C β c τ σ lam hm ha0 ham hσ0 hσlam hlam1 hβ hc hτ hτlam hC
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = m ^ (σ - lam) := ⟨_, rfl⟩
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg hm (by linarith)
  have h1r : 0 < 1 - r := by linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 2 * C / (1 - r) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by
    rw [hY]
    exact div_nonneg (by linarith) h1r.le
  have hY1 : Y * (1 - r) = 2 * C := by
    rw [hY]
    exact div_mul_cancel₀ _ h1r.ne'
  have hYeq : Y * r + 2 * C = Y := by
    calc Y * r + 2 * C = Y * r + Y * (1 - r) := by rw [hY1]
      _ = Y := by ring
  have hmσ : m ^ σ = m ^ lam * r := by
    rw [hr, ← Real.rpow_add hm0]
    congr 1
    ring
  refine ⟨C + Y, ?_⟩
  intro d K F hd hK hKd hF0 hleaf hint k hk
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hdβ : 1 ≤ d ^ β := Real.one_le_rpow hd hβ.le
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = C * (d ^ β) ^ (1 - σ) := ⟨_, rfl⟩
  have hX1 : C ≤ X := by
    rw [hX]
    exact le_mul_of_one_le_right hC (Real.one_le_rpow hdβ (by linarith))
  have hX0 : 0 ≤ X := le_trans hC hX1
  have key : ∀ j : ℕ, F j ≤ X * (m ^ j) ^ σ + Y * (m ^ j) ^ lam := by
    intro j
    induction j with
    | zero =>
      simp only [pow_zero, Real.one_rpow, mul_one]
      linarith
    | succ j ih =>
      have hE1 : 1 ≤ m ^ (j + 1) := one_le_pow₀ hm.le
      have hE0 : 0 < m ^ (j + 1) := pow_pos hm0 _
      have hYE : 0 ≤ Y * (m ^ (j + 1)) ^ lam := mul_nonneg hY0 (Real.rpow_nonneg hE0.le _)
      by_cases hl : m ^ (j + 1) < d ^ β
      · -- leaf level: `F (j+1) ≤ C m^{j+1} ≤ X (m^{j+1})^σ`
        have hs0 : 0 ≤ (m ^ (j + 1)) ^ σ := Real.rpow_nonneg hE0.le _
        have hle : (m ^ (j + 1)) ^ (1 - σ) ≤ (d ^ β) ^ (1 - σ) :=
          Real.rpow_le_rpow hE0.le hl.le (by linarith)
        have hsplit : (m ^ (j + 1)) ^ σ * (m ^ (j + 1)) ^ (1 - σ) = m ^ (j + 1) := by
          rw [← Real.rpow_add hE0]
          norm_num
        have h2 : C * m ^ (j + 1) ≤ X * (m ^ (j + 1)) ^ σ := by
          calc C * m ^ (j + 1) = C * ((m ^ (j + 1)) ^ σ * (m ^ (j + 1)) ^ (1 - σ)) := by
                rw [hsplit]
            _ ≤ C * ((m ^ (j + 1)) ^ σ * (d ^ β) ^ (1 - σ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hs0) hC
            _ = X * (m ^ (j + 1)) ^ σ := by rw [hX]; ring
        have h1 := hleaf (j + 1) hl
        linarith
      · -- internal level
        have hl' : d ^ β ≤ m ^ (j + 1) := not_lt.mp hl
        have h1 := hint j hl'
        have hov : (m ^ (j + 1) * K) ^ τ ≤ (m ^ (j + 1)) ^ lam :=
          appc_overhead_le hd0.le (by linarith) hKd hE1 hl' hβ hc hτ hτlam
        have hone : (1 : ℝ) ≤ (m ^ (j + 1)) ^ lam := Real.one_le_rpow hE1 (by linarith)
        have hmj0 : 0 ≤ m ^ j := pow_nonneg hm0.le j
        have hB0 : 0 ≤ X * (m ^ j) ^ σ + Y * (m ^ j) ^ lam :=
          add_nonneg (mul_nonneg hX0 (Real.rpow_nonneg hmj0 _))
            (mul_nonneg hY0 (Real.rpow_nonneg hmj0 _))
        have h3 : a * F j ≤ m ^ σ * (X * (m ^ j) ^ σ + Y * (m ^ j) ^ lam) :=
          le_trans (mul_le_mul_of_nonneg_left ih ha0) (mul_le_mul_of_nonneg_right ham hB0)
        have hmj : (m ^ (j + 1)) ^ σ = (m ^ j) ^ σ * m ^ σ := by
          rw [pow_succ, Real.mul_rpow hmj0 hm0.le]
        have hmjl : (m ^ (j + 1)) ^ lam = (m ^ j) ^ lam * m ^ lam := by
          rw [pow_succ, Real.mul_rpow hmj0 hm0.le]
        have h4 : m ^ σ * (X * (m ^ j) ^ σ + Y * (m ^ j) ^ lam) =
            X * (m ^ (j + 1)) ^ σ + Y * r * (m ^ (j + 1)) ^ lam := by
          rw [hmj, hmjl, hmσ]
          ring
        have h5 : C * ((m ^ (j + 1) * K) ^ τ + 1) ≤ 2 * C * (m ^ (j + 1)) ^ lam := by
          calc C * ((m ^ (j + 1) * K) ^ τ + 1)
              ≤ C * ((m ^ (j + 1)) ^ lam + (m ^ (j + 1)) ^ lam) :=
                mul_le_mul_of_nonneg_left (add_le_add hov hone) hC
            _ = 2 * C * (m ^ (j + 1)) ^ lam := by ring
        calc F (j + 1) ≤ a * F j + C * ((m ^ (j + 1) * K) ^ τ + 1) := h1
          _ ≤ X * (m ^ (j + 1)) ^ σ + Y * r * (m ^ (j + 1)) ^ lam +
              2 * C * (m ^ (j + 1)) ^ lam := by linarith
          _ = X * (m ^ (j + 1)) ^ σ + (Y * r + 2 * C) * (m ^ (j + 1)) ^ lam := by ring
          _ = X * (m ^ (j + 1)) ^ σ + Y * (m ^ (j + 1)) ^ lam := by rw [hYeq]
  have hk0 : 0 ≤ m ^ k := pow_nonneg hm0.le k
  have hkσ : (m ^ k) ^ σ ≤ d ^ σ := Real.rpow_le_rpow hk0 hk hσ0
  have hkl : (m ^ k) ^ lam ≤ d ^ lam := Real.rpow_le_rpow hk0 hk (by linarith)
  have hXd : X * d ^ σ = C * d ^ (σ + β * (1 - σ)) := by
    rw [hX, ← Real.rpow_mul hd0.le, Real.rpow_add hd0]
    ring
  have hA0 : 0 ≤ d ^ lam := Real.rpow_nonneg hd0.le _
  have hB0 : 0 ≤ d ^ (σ + β * (1 - σ)) := Real.rpow_nonneg hd0.le _
  have hCA : 0 ≤ C * d ^ lam := mul_nonneg hC hA0
  have hYB : 0 ≤ Y * d ^ (σ + β * (1 - σ)) := mul_nonneg hY0 hB0
  calc F k ≤ X * (m ^ k) ^ σ + Y * (m ^ k) ^ lam := key k
    _ ≤ X * d ^ σ + Y * d ^ lam :=
        add_le_add (mul_le_mul_of_nonneg_left hkσ hX0) (mul_le_mul_of_nonneg_left hkl hY0)
    _ = C * d ^ (σ + β * (1 - σ)) + Y * d ^ lam := by rw [hXd]
    _ ≤ (C + Y) * (d ^ lam + d ^ (σ + β * (1 - σ)) + 1) := by
        nlinarith [hCA, hYB, hC, hY0]

end SubNLogN.Math.Networks
