import SubNLogN.Math.Bridge.Algorithm
import SubNLogN.Math.Common.GridInt

/-!
# Integer forms: spreading, pre-scaling and output rounding of the bridge

Value-level ℤ formulas, with equality lemmas, for the arithmetic of `bridgeFixedR roundHalfUpR`
(`SubNLogN/Math/Bridge/Algorithm.lean`; the nearest rounding is `rr := roundHalfUpR`, ties toward
`+∞`, the machine's rounding), for use by the tape-level machine implementation
(`SubNLogN.Machine`):
* `spreadAxisInt`: one fixed-point spreading stage (`spreadAxisFixedR roundHalfUpR`, Lemma 4.6 (bridge Lemma C)(ii)), per output.
  It is the exact Gaussian-integer accumulation of products of `q`-grid numerators (scale `2q`),
  then one nearest rounding (ties toward `+∞`, `rhuShiftC`) by `2^q`. See `spreadAxisFixed_eq_gridValC`.
* `preScaleMax`, `preScaleHNat`, `preScaleExpNat`: the pre-scaling exponent `preScaleExp` of
  an input given by numerators at a general precision `pIn` (`preScaleExp_eq_nat`).
  `preScaledInt` gives the pre-scaled numerators at the grid precision `q`
  (`preScaled_eq_gridValC_of_le`, `preScaled_eq_gridValC_of_onGrid`).
  `preScaleExpNat_le` bounds the exponent.
* `postScaleInt`: the final rounding `crnd roundHalfUpR (p+2) (2^e · Z)` (`crnd_two_pow_mul_gridValC`,
  `bridgeFixed_eq_gridValC`).

A complex value at fractional precision `F` is a pair `c : ℤ × ℤ` with value `gridValC F c`.
-/

namespace SubNLogN.Math.Bridge.IntForms

open SubNLogN.Math.Common SubNLogN.Math.Common.GridInt SubNLogN.Math.Bridge
open scoped BigOperators

variable {d : ℕ}

namespace SpreadAux

/-! ## Local helpers (the numerator calculus itself is `SubNLogN.Math.Common.GridInt`) -/

/-- Multiplication by `2^e`: `2^e · gridValC (F + e) c = gridValC F c`. -/
theorem two_pow_mul_gridValC_add (F e : ℕ) (c : ℤ × ℤ) :
    (2 : ℂ) ^ e * gridValC (F + e) c = gridValC F c := by
  rw [two_pow_mul_gridValC, gridValC_add_smulC_two_pow]

/-- `‖(j ↦ a_j·c)‖_∞ = (max_j |a_j|)·c` for integers `a_j` and `c ≥ 0`. -/
theorem norm_fun_intCast_mul {R : ℕ} (a : Fin R → ℤ) (c : ℝ) (hc : 0 ≤ c) :
    ‖fun j => (a j : ℝ) * c‖ = ((Finset.univ.sup fun j => (a j).natAbs : ℕ) : ℝ) * c := by
  have habs : ∀ j, ‖(a j : ℝ) * c‖ = ((a j).natAbs : ℝ) * c := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, ← Int.cast_natCast, Int.natCast_natAbs,
      Int.cast_abs]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun j => ?_)
    rw [habs]
    apply mul_le_mul_of_nonneg_right _ hc
    exact_mod_cast Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ j)
  · rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR
      simp
    · obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin R))
        ⟨⟨0, hR⟩, Finset.mem_univ _⟩ (fun j => (a j).natAbs)
      rw [hj0, ← habs j0]
      exact norm_le_pi_norm (fun j => (a j : ℝ) * c) j0

/-- `⌈log₂ (M·2^{-p})⌉ = ⌈log₂ M⌉ - p` for `M ≥ 2^p`. -/
theorem clog_natCast_mul_gridUnit (M p : ℕ) (hM : 2 ^ p ≤ M) :
    Int.clog 2 ((M : ℝ) * gridUnit p) = (Nat.clog 2 M : ℤ) - p := by
  have hM1 : 1 ≤ M := le_trans Nat.one_le_two_pow hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hr : (0 : ℝ) < (M : ℝ) * gridUnit p := mul_pos hMpos (gridUnit_pos p)
  have hu : gridUnit p = (2 : ℝ) ^ (-(p : ℤ)) := by
    unfold gridUnit; rw [zpow_neg, zpow_natCast]
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  apply le_antisymm
  · rw [← Int.le_zpow_iff_clog_le (by norm_num) hr, h2, sub_eq_add_neg, zpow_add₀ two_ne_zero,
      zpow_natCast, hu]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.le_pow_clog (by norm_num) M
  · rw [← Int.sub_one_lt_iff, ← Int.zpow_lt_iff_lt_clog (by norm_num) hr, h2, hu]
    have e : (Nat.clog 2 M : ℤ) - p - 1 = ((Nat.clog 2 M : ℤ) - 1) + (-(p : ℤ)) := by ring
    rw [e, zpow_add₀ two_ne_zero]
    apply mul_lt_mul_of_pos_right _ (by positivity)
    rcases Nat.lt_or_ge 1 M with h | h
    · have h1 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
      have hc : 0 < Nat.clog 2 M := Nat.clog_pos (by norm_num) h
      have e2 : ((Nat.clog 2 M : ℤ) - 1) = ((Nat.clog 2 M).pred : ℕ) := by
        rw [Nat.pred_eq_sub_one, Nat.cast_sub hc]; push_cast; ring
      rw [e2, zpow_natCast]
      exact_mod_cast h1
    · have hM' : M = 1 := by omega
      subst hM'
      norm_num

theorem le_clog_of_two_pow_le (M p : ℕ) (hM : 2 ^ p ≤ M) : p ≤ Nat.clog 2 M := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) M
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hM.trans h)

end SpreadAux

/-! ## Spreading (Lemma 4.6 (bridge Lemma C)(ii), `spreadAxisFixedR`) -/

/-- Integer form of one fixed-point spreading stage along Lean axis `i`, output `k`: the exact
Gaussian-integer sum `∑_a Vn(update k i a) · Tn(lowerIndex t i k, a - k_i)` of products of
`q`-numerators (an integer at scale `2^{-2q}`), rounded once by `2^q` (nearest, ties toward `+∞`). -/
def spreadAxisInt (q : ℕ) (t : Fin d → ℕ) (i : Fin d) (Tn : ℕ → ℤ → ℤ × ℤ)
    (Vn : Idx t → ℤ × ℤ) (k : Idx t) : ℤ × ℤ :=
  rhuShiftC q (∑ a : Fin (t i), cmulC (Vn (Function.update k i a))
    (Tn (lowerIndex t i k) ((a : ℤ) - ((k i : ℕ) : ℤ))))

/-- `spreadAxisFixedR roundHalfUpR` on `q`-grid data is `spreadAxisInt` on the numerators. -/
theorem spreadAxisFixed_eq_gridValC (q : ℕ) (t : Fin d → ℕ) (i : Fin d)
    (tap : ℕ → ℤ → ℂ) (Tn : ℕ → ℤ → ℤ × ℤ) (htap : ∀ a e, tap a e = gridValC q (Tn a e))
    (V : Idx t → ℂ) (Vn : Idx t → ℤ × ℤ) (hV : ∀ k, V k = gridValC q (Vn k)) (k : Idx t) :
    spreadAxisFixedR roundHalfUpR q t i tap V k = gridValC q (spreadAxisInt q t i Tn Vn k) := by
  unfold spreadAxisFixedR spreadAxisInt
  simp only [htap, hV, gridValC_cmulC]
  rw [← gridValC_sum, crnd_roundHalfUpR_gridValC]

/-! ## Pre-scaling (step (1), `preScaleExp`, `preScaled`) -/

/-- For input numerators `X` at precision `pIn`:
`M = max(2^pIn, max_j |Re X_j|, max_j |Im X_j|)`. -/
def preScaleMax {R : ℕ} (pIn : ℕ) (X : Fin R → ℤ × ℤ) : ℕ :=
  max (2 ^ pIn) (max (Finset.univ.sup fun j => (X j).1.natAbs)
    (Finset.univ.sup fun j => (X j).2.natAbs))

/-- `H = 1 + (⌈log₂ M⌉ - pIn)` (exact subtraction, since `M ≥ 2^pIn`). -/
def preScaleHNat {R : ℕ} (pIn : ℕ) (X : Fin R → ℤ × ℤ) : ℕ :=
  1 + (Nat.clog 2 (preScaleMax pIn X) - pIn)

/-- The exponent `e = H + ⌊(lg D + 1)/2⌋ + 4` of the pre-scale `S = 2^e`. -/
def preScaleExpNat (t : Fin d → ℕ) (pIn : ℕ) (X : Fin (totalLen t) → ℤ × ℤ) : ℕ :=
  preScaleHNat pIn X + (lg (dimD t) + 1) / 2 + 4

/-- `preScaleH x` from the input numerators at precision `pIn`. -/
theorem preScaleH_eq_nat {R : ℕ} (pIn : ℕ) (x : Fin R → ℂ) (X : Fin R → ℤ × ℤ)
    (hx : ∀ j, x j = gridValC pIn (X j)) :
    preScaleH x = (preScaleHNat pIn X : ℤ) := by
  have hre : (fun j => (x j).re) = fun j => ((X j).1 : ℝ) * gridUnit pIn := by
    funext j; rw [hx j]; rfl
  have him : (fun j => (x j).im) = fun j => ((X j).2 : ℝ) * gridUnit pIn := by
    funext j; rw [hx j]; rfl
  have hu := gridUnit_pos pIn
  have hmax : max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖) =
      ((preScaleMax pIn X : ℕ) : ℝ) * gridUnit pIn := by
    rw [hre, him, SpreadAux.norm_fun_intCast_mul _ _ hu.le,
      SpreadAux.norm_fun_intCast_mul _ _ hu.le]
    have h1 : (1 : ℝ) = ((2 ^ pIn : ℕ) : ℝ) * gridUnit pIn := by
      push_cast; rw [mul_comm]; exact (GridInt.gridUnit_mul_two_pow pIn).symm
    rw [h1, ← max_mul_of_nonneg _ _ hu.le, ← max_mul_of_nonneg _ _ hu.le]
    unfold preScaleMax
    push_cast
    rfl
  have hM : 2 ^ pIn ≤ preScaleMax pIn X := le_max_left _ _
  unfold preScaleH
  rw [hmax, SpreadAux.clog_natCast_mul_gridUnit (preScaleMax pIn X) pIn hM]
  unfold preScaleHNat
  have hle := SpreadAux.le_clog_of_two_pow_le (preScaleMax pIn X) pIn hM
  push_cast [Nat.cast_sub hle]
  ring

/-- `preScaleExp t x = preScaleExpNat t pIn X` for an input `x` with numerators `X` at
precision `pIn`. -/
theorem preScaleExp_eq_nat (t : Fin d → ℕ) (pIn : ℕ) (x : Fin (totalLen t) → ℂ)
    (X : Fin (totalLen t) → ℤ × ℤ) (hx : ∀ j, x j = gridValC pIn (X j)) :
    preScaleExp t x = preScaleExpNat t pIn X := by
  unfold preScaleExp preScaleExpNat
  rw [preScaleH_eq_nat pIn x X hx, Int.toNat_natCast]

/-- Numerator at precision `q` of `x / 2^e` for `x` with numerator `c` at precision `pIn`: an
exact left shift if `pIn + e ≤ q`, otherwise the arithmetic right shift (floor division by
`2^{pIn+e-q}`), which is exact when `x / 2^e` lies on the `q`-grid. No rounding is involved. -/
def preScaledInt (q pIn e : ℕ) (c : ℤ × ℤ) : ℤ × ℤ :=
  if pIn + e ≤ q then smulC (2 ^ (q - (pIn + e))) c
  else (c.1 / 2 ^ (pIn + e - q), c.2 / 2 ^ (pIn + e - q))

theorem preScaled_eq_gridValC_add (t : Fin d → ℕ) (pIn : ℕ) (x : Fin (totalLen t) → ℂ)
    (X : Fin (totalLen t) → ℤ × ℤ) (hx : ∀ j, x j = gridValC pIn (X j)) (j : Fin (totalLen t)) :
    preScaled t x j = gridValC (pIn + preScaleExp t x) (X j) := by
  unfold preScaled
  rw [hx j, gridValC_add_prec]

/-- Pre-scaled input, case `pIn + e ≤ q` (exact left shift). -/
theorem preScaled_eq_gridValC_of_le (t : Fin d → ℕ) (pIn q : ℕ) (x : Fin (totalLen t) → ℂ)
    (X : Fin (totalLen t) → ℤ × ℤ) (hx : ∀ j, x j = gridValC pIn (X j))
    (hq : pIn + preScaleExp t x ≤ q) (j : Fin (totalLen t)) :
    preScaled t x j = gridValC q (preScaledInt q pIn (preScaleExp t x) (X j)) := by
  rw [preScaled_eq_gridValC_add t pIn x X hx j]
  unfold preScaledInt
  rw [if_pos hq]
  obtain ⟨s, hs⟩ : ∃ s, q = pIn + preScaleExp t x + s := ⟨q - (pIn + preScaleExp t x), by omega⟩
  subst hs
  rw [show pIn + preScaleExp t x + s - (pIn + preScaleExp t x) = s by omega,
    gridValC_add_smulC_two_pow]

/-- Pre-scaled input, general case: if `x/2^e` lies on the `q`-grid, its numerator is
`preScaledInt q pIn e (X j)`. -/
theorem preScaled_eq_gridValC_of_onGrid (t : Fin d → ℕ) (pIn q : ℕ) (x : Fin (totalLen t) → ℂ)
    (X : Fin (totalLen t) → ℤ × ℤ) (hx : ∀ j, x j = gridValC pIn (X j)) (j : Fin (totalLen t))
    (hgrid : OnGrid q (preScaled t x j)) :
    preScaled t x j = gridValC q (preScaledInt q pIn (preScaleExp t x) (X j)) := by
  by_cases hq : pIn + preScaleExp t x ≤ q
  · exact preScaled_eq_gridValC_of_le t pIn q x X hx hq j
  · rw [preScaled_eq_gridValC_add t pIn x X hx j] at hgrid ⊢
    unfold preScaledInt
    rw [if_neg hq]
    obtain ⟨s, hs⟩ : ∃ s, pIn + preScaleExp t x = q + s := ⟨pIn + preScaleExp t x - q, by omega⟩
    rw [hs] at hgrid ⊢
    rw [show q + s - q = s by omega]
    obtain ⟨c', hc'⟩ := onGrid_iff_exists_gridValC.mp hgrid
    rw [← gridValC_add_smulC_two_pow q s c', gridValC_inj] at hc'
    rw [← hc', gridValC_add_smulC_two_pow]
    have h2 : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
    simp only [smulC, Int.mul_ediv_cancel_left _ h2]

/-- Bound on the pre-scaling exponent (for the cost analysis): if every input component has
`|X_j| ≤ 2^{wIn-1}` (e.g. it fits `wIn`-bit two's complement) and all `t_i ≥ 1`, then
`preScaleExpNat t pIn X ≤ wIn + totalLen t + 6`. -/
theorem preScaleExpNat_le (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (pIn wIn : ℕ)
    (X : Fin (totalLen t) → ℤ × ℤ)
    (hX : ∀ j, (X j).1.natAbs ≤ 2 ^ (wIn - 1) ∧ (X j).2.natAbs ≤ 2 ^ (wIn - 1)) :
    preScaleExpNat t pIn X ≤ wIn + totalLen t + 6 := by
  have hsup1 : (Finset.univ.sup fun j => (X j).1.natAbs) ≤ 2 ^ (wIn - 1) :=
    Finset.sup_le (fun j _ => (hX j).1)
  have hsup2 : (Finset.univ.sup fun j => (X j).2.natAbs) ≤ 2 ^ (wIn - 1) :=
    Finset.sup_le (fun j _ => (hX j).2)
  have hM : preScaleMax pIn X ≤ 2 ^ (max pIn (wIn - 1)) := by
    unfold preScaleMax
    apply max_le
    · exact Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    · apply max_le
      · exact hsup1.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      · exact hsup2.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have hclog : Nat.clog 2 (preScaleMax pIn X) ≤ max pIn (wIn - 1) := Nat.clog_le_of_le_pow hM
  have hsub : max pIn (wIn - 1) - pIn ≤ wIn - 1 :=
    Nat.sub_le_iff_le_add.mpr (max_le (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  have hH : preScaleHNat pIn X ≤ wIn + 1 := by
    unfold preScaleHNat
    have := Nat.sub_le_sub_right hclog pIn
    omega
  have hD : dimD t ≤ totalLen t := by
    unfold dimD totalLen
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin d => (i : ℕ) ≠ 0)]
    exact Nat.le_mul_of_pos_right _ (Finset.prod_pos (fun i _ => ht i))
  have hlg : lg (dimD t) ≤ dimD t + 1 := by
    unfold lg
    apply max_le _ (by omega)
    have := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := dimD t)).le
    omega
  have hdiv : (lg (dimD t) + 1) / 2 ≤ lg (dimD t) + 1 := Nat.div_le_self _ _
  unfold preScaleExpNat
  omega

/-- `preScaleExp` bound for an input with numerators `X` at precision `pIn`. -/
theorem preScaleExp_le (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (pIn wIn : ℕ)
    (x : Fin (totalLen t) → ℂ) (X : Fin (totalLen t) → ℤ × ℤ)
    (hx : ∀ j, x j = gridValC pIn (X j))
    (hX : ∀ j, (X j).1.natAbs ≤ 2 ^ (wIn - 1) ∧ (X j).2.natAbs ≤ 2 ^ (wIn - 1)) :
    preScaleExp t x ≤ wIn + totalLen t + 6 := by
  rw [preScaleExp_eq_nat t pIn x X hx]
  exact preScaleExpNat_le t ht pIn wIn X hX

/-! ## Output rounding (step (5), `bridgeFixedR`) -/

/-- `crnd roundHalfUpR` fixes values on its grid. -/
theorem crnd_roundHalfUpR_gridValC_self (F : ℕ) (c : ℤ × ℤ) :
    crnd roundHalfUpR F (gridValC F c) = gridValC F c :=
  crnd_eq_self isNearestRounding_roundHalfUpR (onGrid_gridValC F c)

/-- Numerator at precision `p+2` of `crnd roundHalfUpR (p+2) (2^e · Z)` for `Z` with numerator `c`
at precision `q`: an exact left shift if `q ≤ p + 2 + e`, otherwise `rhuShiftC (q - (p+2+e))`. -/
def postScaleInt (q p e : ℕ) (c : ℤ × ℤ) : ℤ × ℤ :=
  if q ≤ p + 2 + e then smulC (2 ^ (p + 2 + e - q)) c else rhuShiftC (q - (p + 2 + e)) c

theorem crnd_two_pow_mul_gridValC (q p e : ℕ) (c : ℤ × ℤ) :
    crnd roundHalfUpR (p + 2) ((2 : ℂ) ^ e * gridValC q c) = gridValC (p + 2) (postScaleInt q p e c) := by
  unfold postScaleInt
  by_cases hq : q ≤ p + 2 + e
  · rw [if_pos hq]
    have h1 : gridValC q c = gridValC (q + (p + 2 + e - q)) (smulC (2 ^ (p + 2 + e - q)) c) :=
      (gridValC_add_smulC_two_pow q _ c).symm
    rw [h1, show q + (p + 2 + e - q) = (p + 2) + e by omega, SpreadAux.two_pow_mul_gridValC_add,
      crnd_roundHalfUpR_gridValC_self]
  · rw [if_neg hq]
    conv_lhs => rw [show q = (p + 2 + (q - (p + 2 + e))) + e by omega]
    rw [SpreadAux.two_pow_mul_gridValC_add, crnd_roundHalfUpR_gridValC]

/-- The bridge output from the numerators `Zn` (precision `q = P + 2`) of the deconvolved array. -/
theorem bridgeFixed_eq_gridValC (p P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (run : (Idx t → ℂ) → (Idx t → ℂ)) (x : Fin (totalLen t) → ℂ)
    (Zn : Fin (totalLen t) → ℤ × ℤ)
    (hZ : ∀ f, deconvFixedR roundHalfUpR (P + 2) t T
      (fun f' => run (spreadStageR roundHalfUpR P t T x) ((encFreq t).symm f')) f =
        gridValC (P + 2) (Zn f))
    (f : Fin (totalLen t)) :
    bridgeFixedR roundHalfUpR p P t T run x f =
      gridValC (p + 2) (postScaleInt (P + 2) p (preScaleExp t x) (Zn f)) := by
  unfold bridgeFixedR bridgePreR
  rw [hZ f]
  exact crnd_two_pow_mul_gridValC (P + 2) p (preScaleExp t x) (Zn f)

end SubNLogN.Math.Bridge.IntForms
