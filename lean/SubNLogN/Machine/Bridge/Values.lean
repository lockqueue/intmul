/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.Lists

/-!
# K5 reduction (2): value-level facts used by the sequencing

* every stage output of the fixed-point bridge lies on the `q`-grid (`spreadAxisFixedR_onGrid`,
  `deconvAxisFixedR_onGrid`, for any nearest rounding), so the next part's grid hypothesis holds;
* the array encodings agree across the parts (`encVec_eq_recsAt_in`, `encT_freq_eq_encVec`);
* width hypotheses in the form the parts need (`cArrFits_recsAt`, …);
* `preScaleExp_le_eBound`: the pre-scaling exponent is bounded by `eBound b = wIn + R + 6` (used
  for the data-independent cost).

All proved.
-/

namespace SubNLogN.Machine.BridgeRed

open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine

variable {d : ℕ}

/-! ## Grid membership of the stage outputs -/

theorem sweepPrefixR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ) (ahat : ℝ)
    (b : ℕ → ℂ) (hb : ∀ n, OnGrid q (b n)) (z : ℂ) : ∀ n, OnGrid q (sweepPrefixR rr q ahat b z n)
  | 0 => by rw [sweepPrefixR]; exact (hb 0).add (crnd_onGrid hrr _ _)
  | n + 1 => by rw [sweepPrefixR]; exact (hb (n + 1)).add (crnd_onGrid hrr _ _)

theorem cycSweepFwdR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) (j : ℕ) :
    OnGrid q (cycSweepFwdR rr q mu ahat gam L Y j) := by
  unfold cycSweepFwdR
  split_ifs
  · exact crnd_onGrid hrr _ _
  · exact sweepPrefixR_onGrid hrr _ _ _ (fun _ => crnd_onGrid hrr _ _) _ _

theorem cycSweepR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (fwd : Bool) (q : ℕ)
    (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) (j : ℕ) :
    OnGrid q (cycSweepR rr fwd q mu ahat gam L Y j) := by
  unfold cycSweepR
  split_ifs
  · exact cycSweepFwdR_onGrid hrr _ _ _ _ _ _ _
  · exact cycSweepFwdR_onGrid hrr _ _ _ _ _ _ _

/-- Every output of a deconvolution stage lies on the `q`-grid. -/
theorem deconvAxisFixedR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (t : Fin d → ℕ) (T : BridgeTables t) (i : Fin d) (Y : Fin (totalLen t) → ℂ)
    (f : Fin (totalLen t)) : OnGrid q (deconvAxisFixedR rr q t T i Y f) := by
  unfold deconvAxisFixedR
  exact cycSweepR_onGrid hrr _ _ _ _ _ _ _ _

/-- Every output of a spreading stage lies on the `q`-grid. -/
theorem spreadAxisFixedR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (t : Fin d → ℕ) (i : Fin d) (tap : ℕ → ℤ → ℂ) (V : Idx t → ℂ) (k : Idx t) :
    OnGrid q (spreadAxisFixedR rr q t i tap V k) := by
  unfold spreadAxisFixedR
  exact crnd_onGrid hrr _ _

/-- After any number of stages, the partial spread is on the grid (if the start is). -/
theorem spreadPart_onGrid (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (V : Idx t → ℂ)
    (hV : ∀ k, OnGrid q (V k)) : ∀ n k, OnGrid q (spreadPart q t T V n k) := by
  intro n
  induction n with
  | zero => simpa [spreadPart_zero] using hV
  | succ n ih =>
    intro k
    cases hi : (spreadOrder d)[n]? with
    | none =>
      have : spreadPart q t T V (n + 1) = spreadPart q t T V n := by
        unfold spreadPart
        rw [List.take_add_one, hi]
        simp
      rw [this]
      exact ih k
    | some i =>
      rw [spreadPart_succ q t T V n i hi]
      exact spreadAxisFixedR_onGrid isNearestRounding_roundHalfUpR _ _ _ _ _ _

/-- The partial deconvolutions are on the grid when the start is. -/
theorem deconvPart_onGrid (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (Y : Fin (totalLen t) → ℂ)
    (hY : ∀ f, OnGrid q (Y f)) : ∀ n f, OnGrid q (deconvPart q t T Y n f) := by
  intro n
  induction n with
  | zero => simpa [deconvPart_zero] using hY
  | succ n ih =>
    intro f
    cases hi : (deconvOrder d)[n]? with
    | none =>
      have : deconvPart q t T Y (n + 1) = deconvPart q t T Y n := by
        unfold deconvPart
        rw [List.take_add_one, hi]
        simp
      rw [this]
      exact ih f
    | some i =>
      rw [deconvPart_succ q t T Y n i hi]
      exact deconvAxisFixedR_onGrid isNearestRounding_roundHalfUpR _ _ _ _ _ _

/-! ## Encodings -/

/-- The pre-scaled array in index order is the tensor array `x' ∘ encIn` in input order. -/
theorem encVec_eq_recsAt_in (F : ℕ) (t : Fin d → ℕ) (y : Fin (totalLen t) → ℂ) :
    encVec F y = recsAt (idxAddrsIn t) (fun j => gridInt F (y (encIn t j))) := by
  simp [encVec, recsAt, idxAddrsIn, List.map_map, Function.comp_def]

/-- A tensor array in natural order is the one-dimensional array `Z ∘ encFreq⁻¹` in index order. -/
theorem encT_freq_eq_encVec (F : ℕ) (t : Fin d → ℕ) (Z : Idx t → ℂ) :
    encT F (idxAddrsFreq t) Z = encVec F (fun f => Z ((encFreq t).symm f)) := by
  simp [encT, encVec, recsAt, idxAddrsFreq, List.map_map, Function.comp_def]

/-! ## Widths -/

theorem cArrFits_recsAt {α : Type} (w : ℕ) (addrs : List α) (v : α → CInt)
    (h : ∀ j, FitsTwos w (v j).1 ∧ FitsTwos w (v j).2) : CArrFits w (recsAt addrs v) := by
  intro cs hcs c hc
  simp only [recsAt, List.mem_map] at hcs
  obtain ⟨j, _, rfl⟩ := hcs
  simp only [List.mem_singleton] at hc
  subst hc
  exact h j

theorem cArrFits_encT (w F : ℕ) {t : Fin d → ℕ} (addrs : List (Idx t)) (Z : Idx t → ℂ)
    (h : ArrFits w F Z) : CArrFits w (encT F addrs Z) :=
  cArrFits_recsAt w addrs _ fun j => h j

theorem cArrFits_encVec (w F : ℕ) {R : ℕ} (y : Fin R → ℂ) (h : ArrFits w F y) :
    CArrFits w (encVec F y) := by
  intro cs hcs c hc
  simp only [encVec, List.mem_map] at hcs
  obtain ⟨j, _, rfl⟩ := hcs
  simp only [List.mem_singleton] at hc
  subst hc
  exact h j

/-- Fits of a tensor array transfer to its natural-order one-dimensional view. -/
theorem arrFits_comp_symm (w F : ℕ) {t : Fin d → ℕ} (Z : Idx t → ℂ) (h : ArrFits w F Z) :
    ArrFits w F (fun f => Z ((encFreq t).symm f)) := fun f => h _

/-- …and back. -/
theorem arrFits_of_comp_symm (w F : ℕ) {t : Fin d → ℕ} (Z : Idx t → ℂ)
    (h : ArrFits w F (fun f => Z ((encFreq t).symm f))) : ArrFits w F Z := by
  intro j
  have := h (encFreq t j)
  simpa using this

/-! ## The pre-scaling exponent -/

/-- A grid value whose numerators fit `w` bits has components of modulus `≤ 2^w`. -/
theorem abs_re_im_le_of_fits {F w : ℕ} {z : ℂ} (hg : OnGrid F z) (hf : FitsC w F z) :
    |z.re| ≤ 2 ^ w ∧ |z.im| ≤ 2 ^ w := by
  obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := hg
  have hu : gridUnit F * 2 ^ F = 1 := by
    unfold gridUnit
    exact inv_mul_cancel₀ (by positivity)
  have hra : (gridInt F z).1 = a := by
    simp only [gridInt]
    rw [ha, mul_assoc, hu, mul_one, round_intCast]
  have hrc : (gridInt F z).2 = c := by
    simp only [gridInt]
    rw [hc, mul_assoc, hu, mul_one, round_intCast]
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hf
  rw [hra] at h1 h2
  rw [hrc] at h3 h4
  have hgu : 0 < gridUnit F := gridUnit_pos F
  have hgu1 : gridUnit F ≤ 1 := by
    unfold gridUnit
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hw : (2 : ℝ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (Nat.sub_le w 1)
  have key : ∀ n : ℤ, -(2 ^ (w - 1) : ℤ) ≤ n → n < 2 ^ (w - 1) → |(n : ℝ)| * gridUnit F ≤ 2 ^ w := by
    intro n hn1 hn2
    have hn : |n| ≤ 2 ^ (w - 1) := abs_le.mpr ⟨hn1, hn2.le⟩
    have hnR : |(n : ℝ)| ≤ (2 : ℝ) ^ (w - 1) := by
      rw [← Int.cast_abs]
      exact_mod_cast hn
    calc |(n : ℝ)| * gridUnit F ≤ |(n : ℝ)| * 1 :=
          mul_le_mul_of_nonneg_left hgu1 (abs_nonneg _)
      _ ≤ 2 ^ w := by rw [mul_one]; exact hnR.trans hw
  constructor
  · rw [ha, abs_mul, abs_of_pos hgu]
    exact key a h1 h2
  · rw [hc, abs_mul, abs_of_pos hgu]
    exact key c h3 h4

/-- **The pre-scaling exponent is bounded by `eBound b = wIn + R + 6`** when the input lies on the
`pIn`-grid with numerators fitting `wIn` bits and every `t_i ≥ 1`: `H ≤ wIn + 1` (`2^H` is the
first power of two above `max(1, max |Re x_j|, max |Im x_j|) ≤ 2^{wIn}`) and
`⌈(lg D)/2⌉ ≤ lg D ≤ D + 1 ≤ R + 1`. -/
theorem preScaleExp_le_eBound (b : BrPar) (x : Fin (totalLen b.t) → ℂ)
    (hgrid : ∀ j, OnGrid b.pIn (x j)) (hfit : ArrFits b.wIn b.pIn x) (ht : ∀ i, 1 ≤ b.t i) :
    preScaleExp b.t x ≤ eBound b := by
  have hw1 : (1 : ℝ) ≤ 2 ^ b.wIn := one_le_pow₀ (by norm_num)
  have hM : max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖) ≤ (2 : ℝ) ^ b.wIn := by
    refine max_le hw1 (max_le ?_ ?_)
    · rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro j
      rw [Real.norm_eq_abs]
      exact (abs_re_im_le_of_fits (hgrid j) (hfit j)).1
    · rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro j
      rw [Real.norm_eq_abs]
      exact (abs_re_im_le_of_fits (hgrid j) (hfit j)).2
  have hpos : (0 : ℝ) < max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hclog : Int.clog 2 (max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖)) ≤ (b.wIn : ℤ) := by
    by_contra hc
    rw [not_le] at hc
    have h1 := Int.zpow_pred_clog_lt_self (b := 2) (by norm_num) hpos
    have h2 : ((2 : ℕ) : ℝ) ^ (b.wIn : ℤ) ≤ ((2 : ℕ) : ℝ) ^
        (Int.clog 2 (max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖)) - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_natCast] at h2
    push_cast at h1 h2
    linarith
  have hH : (preScaleH x).toNat ≤ b.wIn + 1 := by
    unfold preScaleH
    rw [Int.toNat_le]
    push_cast
    omega
  have hD : dimD b.t ≤ totalLen b.t := by
    unfold dimD totalLen
    exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
      (fun i _ _ => ht i)
  have hc : Nat.clog 2 (dimD b.t) ≤ dimD b.t := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hlg1 : 1 ≤ lg (dimD b.t) := le_max_right _ _
  have hlg : lg (dimD b.t) ≤ totalLen b.t + 1 := by
    unfold lg
    omega
  unfold preScaleExp eBound
  have : (lg (dimD b.t) + 1) / 2 ≤ lg (dimD b.t) := by omega
  simp only [BrPar.R]
  omega

end SubNLogN.Machine.BridgeRed
