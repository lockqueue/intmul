import SubNLogN.Math.Bridge.LemmaC_Solver
import SubNLogN.Math.Bridge.LemmaB_Scalar
import SubNLogN.Math.Bridge.Proofs.LemmaB_Separation

/-!
# Bridge: proof of the Lemma 4.6 (bridge Lemma C)(v) closure contract

Proof of `LemmaC_vStmt` (`SubNLogN/Math/Bridge/LemmaC_Solver.lean`, Lemma 4.6
(`lem:bridge-C`)(v)). `lemmaC_v_of` derives it from the separation contract
`LemmaB_ivStmt` (`|c_0 - c_1| ≥ 7/(4t)`), taken as an explicit hypothesis; `lemmaC_v` is the
unconditional version, instantiating it with `lemmaB_iv` (`Proofs/LemmaB_Separation.lean`). (Names `LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), now Lemma 4.6 (`lem:bridge-C`), kept for stability.)

Helpers are in the namespace `SubNLogN.Math.Bridge.LemmaCClosureProof` (public:
`powTrunc_bounds`, `alphaAdmissible_of_lemmaCParams`; the rest are private).

* `powTrunc_bounds`: truncated binary powering of a base `a ∈ [0,1]` at precision `Q` satisfies
  `0 ≤ powTrunc Q a L ≤ a^L` and `a^L - powTrunc Q a L ≤ (2L-1)·2^{-Q}` for `L ≥ 1`
  (strong induction along the definition of `powTrunc`; this is slightly sharper than the paper's
  `2L·2^{-Q}`, and the sharper form is what makes the induction close).
* `kernelG_nonneg_of_pos`, `kernelG_le_one_of_pos` (private): `0 ≤ G(ξ) ≤ 1` for `α > 0` (the
  integrand is a probability density: `∫_ℝ α e^{-πα²v²} dv = 1`, Mathlib's `integral_gaussian`).
* `alphaAdmissible_of_lemmaCParams`: the Lemma 4.6 (bridge Lemma C) parameter hypothesis implies eq. (`eq:alpha`).
* `lemmaC_v_of`: `a' = c_min/c_max ≤ 1 - 7/(4t)` (from B(iv) and `0 ≤ c_min < c_max ≤ 1`), hence
  `â ≤ 1 - 1/(2t)`; both denominators `1 - â^L`, `1 - powTrunc` are `≥ 1/(2t)`, so
  `|(1-ŷ)⁻¹ - (1-â^L)⁻¹| ≤ 4t²·2L·2^{-Q} ≤ v/2048` with `Q = closurePrec q L t`
  (using `2^{lg n} ≥ n`), and the final nearest rounding adds `≤ v/2`.

The hypotheses `u < t` and `2 ≤ t = 2^a` are used to call `LemmaB_ivStmt` (and `t ≥ 2` below);
`v ≤ 1/(64t)` gives `â ≤ 1 - 1/(2t)`; `Even L` is not used (only `L > 0`).
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

/-! Helpers live in the per-file namespace `LemmaCClosureProof` (project hygiene: only the
contract theorems are declared directly in `SubNLogN.Math.Bridge`). -/

namespace LemmaCClosureProof

/-! ## Grid helpers (private copies; the same facts are private in `Proofs/LemmaC_Tables.lean`) -/

private theorem gridUnit_add_eq_mul (a b : ℕ) : gridUnit (a + b) = gridUnit a * gridUnit b := by
  unfold gridUnit; rw [pow_add, mul_inv]

/-- `n · 2^{-lg n} ≤ 1`, since `2^{lg n} ≥ 2^{⌈log₂ n⌉} ≥ n`. -/
private theorem natCast_mul_gridUnit_lg_le_one (n : ℕ) : (n : ℝ) * gridUnit (lg n) ≤ 1 := by
  have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  have h2 : 2 ^ Nat.clog 2 n ≤ 2 ^ lg n := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h3 : (n : ℝ) ≤ (2 : ℝ) ^ lg n := by exact_mod_cast h1.trans h2
  unfold gridUnit
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  exact h3

/-! ## Truncation of nonnegative reals -/

/-- Truncation toward zero keeps nonnegative numbers nonnegative. -/
private theorem truncR_nonneg_of_nonneg {Q : ℕ} {x : ℝ} (hx : 0 ≤ x) : 0 ≤ truncR Q x := by
  unfold truncR truncInt
  have h2 : 0 ≤ x * 2 ^ Q := by positivity
  rw [if_pos h2]
  have h3 : (0 : ℝ) ≤ (⌊x * 2 ^ Q⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr h2
  exact mul_nonneg h3 (gridUnit_pos Q).le

/-- Truncation toward zero does not increase a nonnegative number. -/
private theorem truncR_le_self_of_nonneg {Q : ℕ} {x : ℝ} (hx : 0 ≤ x) : truncR Q x ≤ x := by
  have h := abs_truncR_le Q x
  rw [abs_of_nonneg hx] at h
  exact (le_abs_self _).trans h

/-- One-sided truncation error: `x - Q(x) < 2^{-Q}`. -/
private theorem sub_truncR_lt (Q : ℕ) (x : ℝ) : x - truncR Q x < gridUnit Q := by
  have h := abs_truncR_sub_lt Q x
  rw [abs_sub_comm] at h
  exact (le_abs_self _).trans_lt h

/-- `Q(1) = 1`. -/
private theorem truncR_one (Q : ℕ) : truncR Q 1 = 1 := by
  have hg : OnGrid Q (⟨1, 0⟩ : ℂ) := by simpa using onGrid_intCast Q 1 0
  have h := congrArg Complex.re (truncC_eq_self Q ⟨1, 0⟩ hg)
  simpa using h

/-! ## Truncated binary powering -/

private theorem powTrunc_zero (Q : ℕ) (a : ℝ) : powTrunc Q a 0 = 1 := by
  rw [powTrunc]; simp

private theorem powTrunc_even (Q : ℕ) (a : ℝ) {m : ℕ} (hm : 0 < m) :
    powTrunc Q a (2 * m) = truncR Q (powTrunc Q a m * powTrunc Q a m) := by
  rw [powTrunc]
  have h1 : 2 * m ≠ 0 := by omega
  have h2 : 2 * m % 2 = 0 := by omega
  have h3 : 2 * m / 2 = m := by omega
  rw [dif_neg h1, if_pos h2, h3]

private theorem powTrunc_odd (Q : ℕ) (a : ℝ) (m : ℕ) :
    powTrunc Q a (2 * m + 1) = truncR Q (truncR Q (powTrunc Q a m * powTrunc Q a m) * a) := by
  rw [powTrunc]
  have h1 : 2 * m + 1 ≠ 0 := by omega
  have h2 : ¬ (2 * m + 1) % 2 = 0 := by omega
  have h3 : (2 * m + 1) / 2 = m := by omega
  rw [dif_neg h1, if_neg h2, h3]

/-- Truncated binary powering of a base `a ∈ [0,1]` (Lemma 4.6 (bridge Lemma C)(v), `lem:bridge-C`):
`0 ≤ powTrunc Q a L ≤ a^L`, and for `L ≥ 1` the error is at most `(2L-1)·2^{-Q}`. -/
theorem powTrunc_bounds (Q : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (L : ℕ) :
    0 ≤ powTrunc Q a L ∧ powTrunc Q a L ≤ a ^ L ∧
      (0 < L → a ^ L - powTrunc Q a L ≤ (2 * (L : ℝ) - 1) * gridUnit Q) := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    have hw := gridUnit_pos Q
    obtain ⟨m, hmL | hmL⟩ := Nat.even_or_odd' L
    · subst hmL
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · subst hm0
        refine ⟨by rw [powTrunc_zero]; norm_num, by rw [powTrunc_zero]; simp, ?_⟩
        intro h; omega
      · obtain ⟨p0, p1, p2⟩ := ih m (by omega)
        rw [powTrunc_even Q a hm]
        have ham0 : 0 ≤ a ^ m := pow_nonneg ha0 m
        have ham1 : a ^ m ≤ 1 := pow_le_one₀ ha0 ha1
        have hpp : 0 ≤ powTrunc Q a m * powTrunc Q a m := mul_nonneg p0 p0
        have hsq : a ^ (2 * m) = a ^ m * a ^ m := by rw [two_mul, pow_add]
        refine ⟨truncR_nonneg_of_nonneg hpp, ?_, ?_⟩
        · calc truncR Q (powTrunc Q a m * powTrunc Q a m)
              ≤ powTrunc Q a m * powTrunc Q a m := truncR_le_self_of_nonneg hpp
            _ ≤ a ^ m * a ^ m := mul_le_mul p1 p1 p0 ham0
            _ = a ^ (2 * m) := hsq.symm
        · intro _
          have e1 := sub_truncR_lt Q (powTrunc Q a m * powTrunc Q a m)
          have e2 := p2 hm
          have e3 : (a ^ m - powTrunc Q a m) * (a ^ m + powTrunc Q a m) ≤
              (a ^ m - powTrunc Q a m) * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          have hid : a ^ (2 * m) - truncR Q (powTrunc Q a m * powTrunc Q a m) =
              (a ^ m - powTrunc Q a m) * (a ^ m + powTrunc Q a m) +
                (powTrunc Q a m * powTrunc Q a m -
                  truncR Q (powTrunc Q a m * powTrunc Q a m)) := by
            rw [hsq]; ring
          rw [hid]
          push_cast
          nlinarith
    · subst hmL
      obtain ⟨p0, p1, p2⟩ := ih m (by omega)
      rw [powTrunc_odd]
      have ham0 : 0 ≤ a ^ m := pow_nonneg ha0 m
      have ham1 : a ^ m ≤ 1 := pow_le_one₀ ha0 ha1
      have hpp : 0 ≤ powTrunc Q a m * powTrunc Q a m := mul_nonneg p0 p0
      have hs0 : 0 ≤ truncR Q (powTrunc Q a m * powTrunc Q a m) := truncR_nonneg_of_nonneg hpp
      have hs1 : truncR Q (powTrunc Q a m * powTrunc Q a m) ≤ powTrunc Q a m * powTrunc Q a m :=
        truncR_le_self_of_nonneg hpp
      have hsa : 0 ≤ truncR Q (powTrunc Q a m * powTrunc Q a m) * a := mul_nonneg hs0 ha0
      have hsq : a ^ (2 * m + 1) = a ^ m * a ^ m * a := by rw [pow_succ, two_mul, pow_add]
      refine ⟨truncR_nonneg_of_nonneg hsa, ?_, ?_⟩
      · calc truncR Q (truncR Q (powTrunc Q a m * powTrunc Q a m) * a)
            ≤ truncR Q (powTrunc Q a m * powTrunc Q a m) * a := truncR_le_self_of_nonneg hsa
          _ ≤ a ^ m * a ^ m * a :=
            mul_le_mul_of_nonneg_right (hs1.trans (mul_le_mul p1 p1 p0 ham0)) ha0
          _ = a ^ (2 * m + 1) := hsq.symm
      · intro _
        have e1 := sub_truncR_lt Q (powTrunc Q a m * powTrunc Q a m)
        have e2 := sub_truncR_lt Q (truncR Q (powTrunc Q a m * powTrunc Q a m) * a)
        -- `a·X ≤ X` for the two nonnegative defects `X`
        have hX0 : 0 ≤ a ^ m * a ^ m - powTrunc Q a m * powTrunc Q a m := by
          nlinarith [mul_le_mul p1 p1 p0 ham0]
        have hX : a * (a ^ m * a ^ m - powTrunc Q a m * powTrunc Q a m) ≤
            a ^ m * a ^ m - powTrunc Q a m * powTrunc Q a m := mul_le_of_le_one_left hX0 ha1
        have hY0 : 0 ≤ powTrunc Q a m * powTrunc Q a m -
            truncR Q (powTrunc Q a m * powTrunc Q a m) := by linarith
        have hY : a * (powTrunc Q a m * powTrunc Q a m -
            truncR Q (powTrunc Q a m * powTrunc Q a m)) ≤
            powTrunc Q a m * powTrunc Q a m - truncR Q (powTrunc Q a m * powTrunc Q a m) :=
          mul_le_of_le_one_left hY0 ha1
        have hid : a ^ (2 * m + 1) - truncR Q (truncR Q (powTrunc Q a m * powTrunc Q a m) * a) =
            a * (a ^ m * a ^ m - powTrunc Q a m * powTrunc Q a m) +
              a * (powTrunc Q a m * powTrunc Q a m -
                truncR Q (powTrunc Q a m * powTrunc Q a m)) +
              (truncR Q (powTrunc Q a m * powTrunc Q a m) * a -
                truncR Q (truncR Q (powTrunc Q a m * powTrunc Q a m) * a)) := by
          rw [hsq]; ring
        rw [hid]
        rcases Nat.eq_zero_or_pos m with hm0 | hm
        · subst hm0
          simp only [powTrunc_zero, mul_one, one_mul, truncR_one, pow_zero, sub_self, mul_zero,
            zero_add] at e2 ⊢
          push_cast
          linarith
        · have e3 := p2 hm
          have e4 : (a ^ m - powTrunc Q a m) * (a ^ m + powTrunc Q a m) ≤
              (a ^ m - powTrunc Q a m) * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          have hfac : a ^ m * a ^ m - powTrunc Q a m * powTrunc Q a m =
              (a ^ m - powTrunc Q a m) * (a ^ m + powTrunc Q a m) := by ring
          push_cast
          nlinarith

/-! ## The alias weights lie in `[0,1]`; the parameter hypothesis gives eq. (`eq:alpha`) -/

/-- `G(ξ) ≥ 0` for `α ≥ 0` (nonnegative integrand over a positively oriented interval). -/
private theorem kernelG_nonneg_of_pos {α : ℝ} (hα : 0 ≤ α) (ξ : ℝ) : 0 ≤ kernelG α ξ := by
  unfold kernelG
  apply intervalIntegral.integral_nonneg (by linarith)
  intro v _
  exact mul_nonneg hα (Real.exp_pos _).le

/-- `G(ξ) ≤ 1` for `α > 0`: `∫_{ξ-1/2}^{ξ+1/2} α e^{-πα²v²} dv ≤ ∫_ℝ α e^{-πα²v²} dv = 1`. -/
private theorem kernelG_le_one_of_pos {α : ℝ} (hα : 0 < α) (ξ : ℝ) : kernelG α ξ ≤ 1 := by
  unfold kernelG
  have hb : 0 < Real.pi * α ^ 2 := by positivity
  have hint : MeasureTheory.Integrable
      (fun v : ℝ => α * Real.exp (-(Real.pi * α ^ 2) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul α
  have hfun : (fun v : ℝ => α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2))) =
      fun v : ℝ => α * Real.exp (-(Real.pi * α ^ 2) * v ^ 2) := by
    funext v; ring_nf
  rw [hfun, intervalIntegral.integral_of_le (by linarith)]
  calc ∫ v in Set.Ioc (ξ - 1 / 2) (ξ + 1 / 2), α * Real.exp (-(Real.pi * α ^ 2) * v ^ 2)
      ≤ ∫ v, α * Real.exp (-(Real.pi * α ^ 2) * v ^ 2) :=
        MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun v => mul_nonneg hα.le (Real.exp_pos _).le)
    _ = 1 := by
        rw [MeasureTheory.integral_const_mul, integral_gaussian]
        have h1 : Real.pi / (Real.pi * α ^ 2) = (α⁻¹) ^ 2 := by
          field_simp
        rw [h1, Real.sqrt_sq (inv_nonneg.mpr hα.le), mul_inv_cancel₀ hα.ne']

/-- The Lemma 4.6 (bridge Lemma C) parameter hypothesis (`α² = 4λ_G ω ln2/π`, `λ_G ∈ [1,4]`, `α > 0`) implies
eq. (`eq:alpha`): `2√(ω ln2/π) ≤ α ≤ 4√(ω ln2/π)`. -/
theorem alphaAdmissible_of_lemmaCParams {P ω : ℕ} {α : ℝ} (hC : LemmaCParams P ω α) :
    AlphaAdmissible ω α := by
  obtain ⟨_, _, _, hα, lamG, hl1, hl4, hsq⟩ := hC
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : 0 ≤ (ω : ℝ) * Real.log 2 / Real.pi :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog.le) Real.pi_pos.le
  have hs0 : 0 ≤ Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ^ 2 = (ω : ℝ) * Real.log 2 / Real.pi :=
    Real.sq_sqrt hX
  have hl1' : (1 : ℝ) ≤ (lamG : ℝ) := by exact_mod_cast hl1
  have hl4' : (lamG : ℝ) ≤ 4 := by exact_mod_cast hl4
  have hα2 : α ^ 2 = 4 * (lamG : ℝ) * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) ^ 2 := by
    rw [hs2, hsq]; ring
  constructor
  · have h : (2 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi)) ^ 2 ≤ α ^ 2 := by
      rw [hα2]; nlinarith [sq_nonneg (Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi))]
    nlinarith
  · have h : α ^ 2 ≤ (4 * Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi)) ^ 2 := by
      rw [hα2]; nlinarith [sq_nonneg (Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi))]
    nlinarith

/-! ## Lemma 4.6 (bridge Lemma C)(v) -/

/-- Numeric core of C(v): `4t² · 2L · 2^{-Q} ≤ v/2048` for `Q = closurePrec q L t`
(uses `2^{lg n} ≥ n` for `n = L` and `n = 4t`). -/
private theorem closurePrec_bound (q L t : ℕ) :
    8 * (t : ℝ) ^ 2 * (L : ℝ) * gridUnit (closurePrec q L t) ≤ gridUnit q / 2048 := by
  unfold closurePrec
  rw [gridUnit_add_eq_mul (q + lg L + 2 * lg (4 * t)) 10,
    gridUnit_add_eq_mul (q + lg L) (2 * lg (4 * t)), gridUnit_add_eq_mul q (lg L),
    two_mul, gridUnit_add_eq_mul (lg (4 * t)) (lg (4 * t))]
  have hL := natCast_mul_gridUnit_lg_le_one L
  have h4t := natCast_mul_gridUnit_lg_le_one (4 * t)
  push_cast at h4t
  have hq := gridUnit_pos q
  have hgL := gridUnit_pos (lg L)
  have hg4 := gridUnit_pos (lg (4 * t))
  have h10 : gridUnit 10 = 1 / 1024 := by unfold gridUnit; norm_num
  rw [h10]
  have h0 : 0 ≤ 4 * (t : ℝ) * gridUnit (lg (4 * t)) := by positivity
  have h16 : (4 * (t : ℝ) * gridUnit (lg (4 * t))) * (4 * (t : ℝ) * gridUnit (lg (4 * t))) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul h4t h4t h0 zero_le_one
      _ = 1 := one_mul 1
  have hB0 : 0 ≤ (L : ℝ) * gridUnit (lg L) := by positivity
  have hAB := mul_le_mul h16 hL hB0 zero_le_one
  calc 8 * (t : ℝ) ^ 2 * (L : ℝ) * (gridUnit q * gridUnit (lg L) *
        (gridUnit (lg (4 * t)) * gridUnit (lg (4 * t))) * (1 / 1024))
      = ((4 * (t : ℝ) * gridUnit (lg (4 * t))) * (4 * (t : ℝ) * gridUnit (lg (4 * t)))) *
          ((L : ℝ) * gridUnit (lg L)) * (gridUnit q / 2048) := by ring
    _ ≤ 1 * 1 * (gridUnit q / 2048) := mul_le_mul_of_nonneg_right hAB (by positivity)
    _ = gridUnit q / 2048 := by ring

end LemmaCClosureProof

open LemmaCClosureProof in
/-- Lemma 4.6 (bridge Lemma C)(v) (`lem:bridge-C`), from Lemma 4.4 (bridge Lemma B)(iv) (`|c_0 - c_1| ≥ 7/(4t)`). -/
theorem lemmaC_v_of (hBiv : LemmaB_ivStmt) : LemmaC_vStmt := by
  intro rr hrr P ω α hC t ht u hu hv ahat L _hL hL0 ha ha0
  unfold closureFixedR
  have hα : 0 < α := hC.2.2.2.1
  have hsep := hBiv ω hC.2.1 α (alphaAdmissible_of_lemmaCParams hC) t ht u hu
  set c0 := kernelG α (((u : ℝ) + 1 / 2) / (t : ℝ)) with hc0_def
  set c1 := kernelG α (((u : ℝ) + 1 / 2) / (t : ℝ) - 1) with hc1_def
  have hc0 : 0 ≤ c0 := kernelG_nonneg_of_pos hα.le _
  have hc1 : 0 ≤ c1 := kernelG_nonneg_of_pos hα.le _
  have hc0' : c0 ≤ 1 := kernelG_le_one_of_pos hα _
  have hc1' : c1 ≤ 1 := kernelG_le_one_of_pos hα _
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht.1
  have ht0 : (0 : ℝ) < t := by linarith
  -- `a' = c_min/c_max ≤ 1 - 7/(4t)`
  have hMm : max c0 c1 - min c0 c1 = |c0 - c1| := by rw [max_sub_min_eq_abs, abs_sub_comm]
  have hM1 : max c0 c1 ≤ 1 := max_le hc0' hc1'
  have hm0 : 0 ≤ min c0 c1 := le_min hc0 hc1
  have h7 : 0 < 7 / (4 * (t : ℝ)) := by positivity
  have hM0 : 0 < max c0 c1 := by linarith
  have ha' : min c0 c1 / max c0 c1 ≤ 1 - 7 / (4 * (t : ℝ)) := by
    rw [div_le_iff₀ hM0]
    have : 7 / (4 * (t : ℝ)) * max c0 c1 ≤ 7 / (4 * (t : ℝ)) := mul_le_of_le_one_right h7.le hM1
    nlinarith
  -- `â ≤ 1 - 1/(2t)`
  have hahat : ahat ≤ 1 - 1 / (2 * (t : ℝ)) := by
    have h1 := (abs_le.mp ha).2
    have e1 : 7 / (4 * (t : ℝ)) = 7 / 4 * (t : ℝ)⁻¹ := by ring
    have e2 : 1 / (64 * (t : ℝ)) = 1 / 64 * (t : ℝ)⁻¹ := by ring
    have e3 : 1 / (2 * (t : ℝ)) = 1 / 2 * (t : ℝ)⁻¹ := by ring
    have hti : 0 < (t : ℝ)⁻¹ := inv_pos.mpr ht0
    rw [e1] at ha'
    rw [e2] at hv
    rw [e3]
    linarith
  have h2t : 0 < 1 / (2 * (t : ℝ)) := by positivity
  have hahat1 : ahat ≤ 1 := by linarith
  -- truncated powering
  obtain ⟨y0, yx, yerr⟩ := powTrunc_bounds (closurePrec (P + 2) L t) ahat ha0 hahat1 L
  have hxa : ahat ^ L ≤ ahat := pow_le_of_le_one ha0 hahat1 hL0.ne'
  set x := ahat ^ L with hx_def
  set y := powTrunc (closurePrec (P + 2) L t) ahat L with hy_def
  -- both denominators are `≥ 1/(2t)`
  have hdx : 1 ≤ (1 - x) * (2 * (t : ℝ)) := by
    have : 1 / (2 * (t : ℝ)) ≤ 1 - x := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  have hdy : 1 ≤ (1 - y) * (2 * (t : ℝ)) := by
    have : 1 / (2 * (t : ℝ)) ≤ 1 - y := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have hden : 0 < (1 - y) * (1 - x) := mul_pos hy1 hx1
  have hden4 : 1 ≤ 4 * (t : ℝ) ^ 2 * ((1 - y) * (1 - x)) := by
    have := one_le_mul_of_one_le_of_one_le hdy hdx
    linarith
  -- derivative bound for `(1 - ·)⁻¹`
  have hxy : 0 ≤ x - y := by linarith
  have hdiff : |(1 - y)⁻¹ - (1 - x)⁻¹| ≤ 4 * (t : ℝ) ^ 2 * (x - y) := by
    rw [inv_sub_inv hy1.ne' hx1.ne', abs_div, abs_of_pos hden, div_le_iff₀ hden,
      show (1 - x) - (1 - y) = -(x - y) by ring, abs_neg, abs_of_nonneg hxy]
    have := mul_le_mul_of_nonneg_left hden4 hxy
    linarith
  -- powering error `≤ 2L·2^{-Q}`
  have hw := gridUnit_pos (closurePrec (P + 2) L t)
  have herr : x - y ≤ 2 * (L : ℝ) * gridUnit (closurePrec (P + 2) L t) := by
    have := yerr hL0
    nlinarith
  have hQ := closurePrec_bound (P + 2) L t
  have hround := abs_rr_sub_le hrr (P + 2) ((1 - y)⁻¹)
  have hv0 := gridUnit_pos (P + 2)
  have t1 := abs_sub_le (rr (P + 2) ((1 - y)⁻¹)) ((1 - y)⁻¹) ((1 - x)⁻¹)
  have ht2' : 0 ≤ 4 * (t : ℝ) ^ 2 := by positivity
  have h4 : 4 * (t : ℝ) ^ 2 * (x - y) ≤
      4 * (t : ℝ) ^ 2 * (2 * (L : ℝ) * gridUnit (closurePrec (P + 2) L t)) :=
    mul_le_mul_of_nonneg_left herr ht2'
  linarith

/-- Lemma 4.6 (bridge Lemma C)(v), unconditional: `lemmaC_v_of` with the proved separation bound `lemmaB_iv`. -/
theorem lemmaC_v : LemmaC_vStmt := lemmaC_v_of lemmaB_iv

end SubNLogN.Math.Bridge
