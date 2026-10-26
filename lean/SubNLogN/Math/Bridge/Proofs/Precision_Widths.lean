import SubNLogN.Math.Bridge.Proofs.Precision_Deconv
import SubNLogN.Math.Bridge.Proofs.Precision_Basic

/-!
# Bridge: Theorem 4.7, the widths table (Table 4 (`tab:widths`))

Proves `bridge_widths_of : … → Bridge_widthsStmt` (value-level rows of Table 4 (`tab:widths`), for every
nearest rounding `rr`), conditional on `Bridge_spread_admissibleStmt` and on the contracts used by the
deconvolution chain
(`LemmaC_ivStmt`, `LemmaC_vStmt`, `LemmaB_vStmt`, `LemmaB_v_axisStmt`, through
`PrecisionDeconvProof.deconv_chain_list`).

Every row is "on the `q`-grid plus a magnitude bound" (`fitsWidth_of_norm_lt`: a `q`-grid value of
modulus `< 2^e` fits width `w` when `q + e + 1 ≤ w`), with `q = P + 2`:
* normalized input `x' = x/S`: on the grid by `Bridge_spread_admissibleStmt`, and `‖x'_j‖ ≤ 1`
  because `S ≥ 2^H = 2·2^{⌈log₂ C⌉} ≥ 2C ≥ ‖x_j‖` (`norm_preScaled_le_one`); width `q + 2`;
* completed spread array: on the grid with `‖U‖ ≤ 1/8` (`Bridge_spread_admissibleStmt`);
  width `q + 2`;
* partial deconvolution outputs after `m` solver stages: on the grid, because every solver output is
  a rounded value `crnd rr q _` or a sum of two of them (`foldl_deconvR_onGrid`) and the middle
  output is on the
  grid (`IsMiddleTransform.out_onGrid`); modulus `≤ max(1,‖Ŷ‖)·D_m·(1 + 64 v S_m) ≤ 2·2^k`
  (`deconv_chain_list` on the prefix list), using `‖Ŷ‖ ≤ ‖U‖ + E_mid v ≤ 1/8 + 7/8`
  (`norm_dftTensor_le`, `E_mid ≤ 16R(k+1)`), `D_m ≤ R = 2^k` and `64 v ∑_h t_h ≤ 1`;
  width `q + k + 6`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace PrecisionWidthsProof

variable {d : ℕ}

/-! ## Widths from grid membership and magnitude -/

/-- A real on the `q`-grid with `|x| < 2^e` fits component width `w` when `q + e + 1 ≤ w`. -/
theorem fitsWidthR_of_abs_lt {q w e : ℕ} {x : ℝ} (hx : OnGridR q x) (hb : |x| < (2 : ℝ) ^ e)
    (hw : q + e + 1 ≤ w) : FitsWidthR q w x := by
  obtain ⟨a, rfl⟩ := hx
  have hg : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have ha : |(a : ℝ)| < (2 : ℝ) ^ (e + q) := by
    rw [abs_mul, abs_of_pos (gridUnit_pos q)] at hb
    unfold gridUnit at hb
    rw [mul_inv_lt_iff₀ hg] at hb
    rwa [pow_add]
  have h1 : (2 : ℝ) ^ (e + q) ≤ (2 : ℝ) ^ (w - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : |(a : ℝ)| < (((2 : ℤ) ^ (w - 1) : ℤ) : ℝ) := by push_cast; linarith
  have h3 : |a| < (2 : ℤ) ^ (w - 1) := by exact_mod_cast h2
  rw [abs_lt] at h3
  exact ⟨a, rfl, h3.1.le, h3.2⟩

/-- A complex number on the `q`-grid with `‖z‖ < 2^e` fits component width `w` when
`q + e + 1 ≤ w`. -/
theorem fitsWidth_of_norm_lt {q w e : ℕ} {z : ℂ} (hz : OnGrid q z) (hb : ‖z‖ < (2 : ℝ) ^ e)
    (hw : q + e + 1 ≤ w) : FitsWidth q w z :=
  ⟨fitsWidthR_of_abs_lt hz.1 ((Complex.abs_re_le_norm z).trans_lt hb) hw,
    fitsWidthR_of_abs_lt hz.2 ((Complex.abs_im_le_norm z).trans_lt hb) hw⟩

/-! ## Solver outputs lie on the grid -/

theorem sweepPrefixR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ) (ahat : ℝ)
    (b : ℕ → ℂ) (zinit : ℂ) (hb : ∀ n, OnGrid q (b n)) (n : ℕ) :
    OnGrid q (sweepPrefixR rr q ahat b zinit n) := by
  cases n with
  | zero => exact (hb 0).add (crnd_onGrid hrr q _)
  | succ n => exact (hb (n + 1)).add (crnd_onGrid hrr q _)

theorem cycSweepFwdR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) (j : ℕ) :
    OnGrid q (cycSweepFwdR rr q mu ahat gam L Y j) := by
  unfold cycSweepFwdR
  split_ifs
  · exact crnd_onGrid hrr q _
  · exact sweepPrefixR_onGrid hrr q ahat _ _ (fun n => crnd_onGrid hrr q _) j

theorem cycSweepR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (fwd : Bool) (q : ℕ)
    (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) (j : ℕ) :
    OnGrid q (cycSweepR rr fwd q mu ahat gam L Y j) := by
  unfold cycSweepR
  split_ifs
  · exact cycSweepFwdR_onGrid hrr q mu ahat gam L Y j
  · exact cycSweepFwdR_onGrid hrr q mu ahat gam L _ _

/-- Every output of a fixed-point deconvolution stage lies on the `q`-grid (whatever the input). -/
theorem deconvAxisFixedR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (t : Fin d → ℕ) (T : BridgeTables t) (i : Fin d) (Y : Fin (totalLen t) → ℂ)
    (f : Fin (totalLen t)) : OnGrid q (deconvAxisFixedR rr q t T i Y f) :=
  cycSweepR_onGrid hrr _ _ _ _ _ _ _ _

theorem foldl_deconvR_onGrid {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (t : Fin d → ℕ) (T : BridgeTables t) (l : List (Fin d)) (Y : Fin (totalLen t) → ℂ)
    (hY : ∀ f, OnGrid q (Y f)) :
    ∀ f, OnGrid q (l.foldl (fun Z i => deconvAxisFixedR rr q t T i Z) Y f) := by
  induction l generalizing Y with
  | nil => exact hY
  | cons i l ih => exact ih _ (fun f => deconvAxisFixedR_onGrid hrr q t T i Y f)

/-! ## Shape and schedule facts -/

/-- In the balanced shape `d ≤ k` (each `t_i ≥ 2`, so `2^d ≤ ∏ t_i = 2^k`). -/
theorem d_le_k {t : Fin d → ℕ} {k ℓ : ℕ} (h : BalancedShape t k ℓ) : d ≤ k := by
  have hsh := PrecisionBasic.shapeOK_of_balancedShape h
  obtain ⟨-, hR, -⟩ := h
  have h1 : 2 ^ d ≤ totalLen t := by
    have := Finset.pow_card_le_prod Finset.univ t 2 (fun i _ => (hsh i).1)
    simpa using this
  rw [hR] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

/-- Every `t_i` divides `R = 2^k`, so `t_i ≤ 2^k`. -/
theorem t_le_two_pow {t : Fin d → ℕ} {k : ℕ} (hR : totalLen t = 2 ^ k) (i : Fin d) :
    t i ≤ 2 ^ k := by
  rw [← hR]
  exact Nat.le_of_dvd (by rw [hR]; positivity) (Finset.dvd_prod_of_mem t (Finset.mem_univ i))

/-- `α = alphaDefault ω` satisfies the Lemma 4.6 (bridge Lemma C) parameter hypothesis (with `λ_G = 1`). -/
theorem lemmaCParams_default {P ω : ℕ} (hP : 20 ≤ P) (hω : 8 ≤ ω) (hωP : ω ≤ P) :
    LemmaCParams P ω (alphaDefault ω) := by
  refine ⟨hP, hω, hωP, IntMul.alphaSchedule_pos ω (by omega), 1, le_rfl, by norm_num, ?_⟩
  unfold alphaDefault IntMul.alphaSchedule
  rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg one_le_two)) Real.pi_pos.le)]
  push_cast
  ring

/-- `2^n · 2^{-(n+2)} = 1/4`. -/
theorem two_pow_mul_gridUnit (n : ℕ) : (2 : ℝ) ^ n * gridUnit (n + 2) = 1 / 4 := by
  unfold gridUnit
  rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  norm_num

/-! ## The normalized input -/

/-- `‖x'_j‖ ≤ 1` for the pre-scaled input `x' = x/S`: with `C = max(1, max|Re x|, max|Im x|)`,
`S ≥ 2^H = 2·2^{⌈log₂ C⌉} ≥ 2C ≥ |Re x_j| + |Im x_j| ≥ ‖x_j‖`. -/
theorem norm_preScaled_le_one (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) (j : Fin (totalLen t)) :
    ‖preScaled t x j‖ ≤ 1 := by
  set C : ℝ := max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖) with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  have hclog : Int.clog 2 C = ((Int.clog 2 C).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg]
    rw [Int.clog_of_one_le_right 2 hC1]
    exact Nat.cast_nonneg _
  set n := (Int.clog 2 C).toNat with hn
  have hCn : C ≤ (2 : ℝ) ^ n := by
    have h := Int.self_le_zpow_clog (R := ℝ) (b := 2) (by norm_num) C
    rw [hclog, zpow_natCast] at h
    exact_mod_cast h
  have hH : (preScaleH x).toNat = n + 1 := by
    unfold preScaleH
    rw [← hC, hclog]
    omega
  have hs : n + 1 ≤ preScaleExp t x := by
    unfold preScaleExp
    rw [hH]
    omega
  have hre : |(x j).re| ≤ C := by
    have h1 := norm_le_pi_norm (fun j => (x j).re) j
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_max_left _ _).trans (le_max_right _ _))
  have him : |(x j).im| ≤ C := by
    have h1 := norm_le_pi_norm (fun j => (x j).im) j
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_max_right _ _).trans (le_max_right _ _))
  have hxj : ‖x j‖ ≤ 2 * C := (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
  have h2s : 2 * C ≤ (2 : ℝ) ^ preScaleExp t x := by
    calc 2 * C ≤ 2 * 2 ^ n := by linarith
      _ = 2 ^ (n + 1) := by ring
      _ ≤ 2 ^ preScaleExp t x := pow_le_pow_right₀ (by norm_num) hs
  unfold preScaled
  rw [norm_div, norm_pow, Complex.norm_ofNat, div_le_one (by positivity)]
  linarith

end PrecisionWidthsProof

open PrecisionWidthsProof in
/-- The widths table of Theorem 4.7 (Table 4 (`tab:widths`), value-level rows), with
`q = P + 2`: the normalized input and the completed spread array have component width `q + 2`,
and every partial deconvolution output has component width `q + k + 6`. Conditional on
`Bridge_spread_admissibleStmt` and on Lemma 4.6 (bridge Lemma C)(iv), C(v), B(v), B(v)_axis (deconvolution chain). -/
theorem bridge_widths_of (hspread : Bridge_spread_admissibleStmt) (hCiv : LemmaC_ivStmt)
    (hCv : LemmaC_vStmt) (hBv : LemmaB_vStmt) (hBax : LemmaB_v_axisStmt) :
    Bridge_widthsStmt := by
  intro rr hrr d t k ℓ p hshape hp x hx hxn T hT Emid δmid run hmid
  obtain ⟨hpre, hUg, hUn⟩ := hspread rr hrr t k ℓ p hshape hp x hx hxn T hT
  have hsh := PrecisionBasic.shapeOK_of_balancedShape hshape
  have hdk := d_le_k hshape
  obtain ⟨hd2, hR, -, -, -⟩ := hshape
  have hPdef : schedP p k = 2 * p + 12 * k + 32 * Nat.clog 2 (p + k + 2) + 256 := by
    unfold schedP; rfl
  refine ⟨fun j => ?_, fun j => ?_, fun m f => ?_⟩
  · -- normalized input: `‖x'_j‖ ≤ 1 < 2`
    have h1 : ‖preScaled t x j‖ < (2 : ℝ) ^ 1 := by
      have := norm_preScaled_le_one t x j
      norm_num; linarith
    exact fitsWidth_of_norm_lt (hpre j) h1 (by omega)
  · -- completed spread array: `‖U_j‖ ≤ 1/8 < 2`
    have h1 : ‖spreadStageR rr (schedP p k) t T x j‖ < (2 : ℝ) ^ 1 := by
      have := norm_le_pi_norm (spreadStageR rr (schedP p k) t T x) j
      norm_num; linarith
    exact fitsWidth_of_norm_lt (hUg j) h1 (by omega)
  · -- partial deconvolution outputs
    set P := schedP p k with hP
    set U := spreadStageR rr P t T x with hU
    set Y0 : Fin (totalLen t) → ℂ := fun f' => run U ((encFreq t).symm f') with hY0
    set l := (deconvOrder d).take m with hl
    -- grid membership
    have hY0g : ∀ f, OnGrid (P + 2) (Y0 f) := fun f => hmid.out_onGrid U hUg hUn _
    have hg := foldl_deconvR_onGrid hrr (P + 2) t T l Y0 hY0g f
    -- `‖Ŷ‖ ≤ ‖U‖ + E_mid v ≤ 1/8 + 7/8`
    have hv0 : 0 < gridUnit (P + 2) := gridUnit_pos _
    have hRr : (totalLen t : ℝ) = 2 ^ k := by rw [hR]; push_cast; ring
    have hEv : Emid * gridUnit (P + 2) ≤ 7 / 8 := by
      have hE := hmid.Emid_le
      have hlg : (lg (totalLen t) : ℝ) + 1 ≤ 2 ^ (k + 1) := by
        rw [hR]
        unfold lg
        rw [Nat.clog_pow 2 k (by norm_num)]
        have h1 : max k 1 ≤ k + 1 := max_le (by omega) (by omega)
        have h2 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
        have h3 : max k 1 + 1 ≤ 2 ^ (k + 1) := by omega
        exact_mod_cast h3
      have hbig : (2 : ℝ) ^ (2 * k + 5) ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 := two_pow_mul_gridUnit P
      calc Emid * gridUnit (P + 2)
          ≤ 16 * (totalLen t : ℝ) * ((lg (totalLen t) : ℝ) + 1) * gridUnit (P + 2) :=
            mul_le_mul_of_nonneg_right hE hv0.le
        _ ≤ 16 * 2 ^ k * 2 ^ (k + 1) * gridUnit (P + 2) := by
            rw [hRr]; gcongr
        _ = 2 ^ (2 * k + 5) * gridUnit (P + 2) := by ring
        _ ≤ 2 ^ P * gridUnit (P + 2) := mul_le_mul_of_nonneg_right hbig hv0.le
        _ ≤ 7 / 8 := by rw [h4]; norm_num
    have hrun : ‖run U‖ ≤ 1 := by
      have herr := hmid.err U hUg hUn
      have hdft := norm_dftTensor_le t U
      calc ‖run U‖ = ‖(run U - dftTensor t U) + dftTensor t U‖ := by rw [sub_add_cancel]
        _ ≤ ‖run U - dftTensor t U‖ + ‖dftTensor t U‖ := norm_add_le _ _
        _ ≤ Emid * gridUnit (P + 2) + ‖U‖ := add_le_add herr hdft
        _ ≤ 7 / 8 + 1 / 8 := add_le_add hEv hUn
        _ = 1 := by norm_num
    have hY0n : ‖Y0‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun f' => (norm_le_pi_norm (run U) _).trans hrun
    -- the prefix list of solver axes
    have hsub : l.Sublist (List.finRange d) :=
      (List.take_sublist m (deconvOrder d)).trans (by unfold deconvOrder; apply List.filter_sublist)
    have hlnz : ∀ i ∈ l, (i : ℕ) ≠ 0 := fun i hi =>
      PrecisionDeconvProof.mem_deconvOrder'.mp (List.mem_of_mem_take hi)
    have hS0 : 0 ≤ (l.map (fun i => (t i : ℝ))).sum :=
      List.sum_nonneg (fun a ha => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; positivity)
    have hsum : 64 * gridUnit (P + 2) * (l.map (fun i => (t i : ℝ))).sum ≤ 1 := by
      have hS : (l.map (fun i => (t i : ℝ))).sum ≤
          ((List.finRange d).map (fun i => (t i : ℝ))).sum :=
        (hsub.map _).sum_le_sum
          (fun a ha => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; positivity)
      rw [← Fin.sum_univ_def] at hS
      have hle : ∑ i, (t i : ℝ) ≤ (d : ℝ) * 2 ^ k := by
        calc ∑ i, (t i : ℝ) ≤ ∑ _i : Fin d, (2 : ℝ) ^ k :=
              Finset.sum_le_sum (fun i _ => by exact_mod_cast t_le_two_pow hR i)
          _ = (d : ℝ) * 2 ^ k := by simp
      have hd : (d : ℝ) ≤ 2 ^ k := by exact_mod_cast (hdk.trans Nat.lt_two_pow_self.le)
      have hbig : (2 : ℝ) ^ (2 * k + 6) ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 := two_pow_mul_gridUnit P
      calc 64 * gridUnit (P + 2) * (l.map (fun i => (t i : ℝ))).sum
          ≤ 64 * gridUnit (P + 2) * ((d : ℝ) * 2 ^ k) := by
            gcongr; exact hS.trans hle
        _ ≤ 64 * gridUnit (P + 2) * (2 ^ k * 2 ^ k) := by gcongr
        _ = 2 ^ (2 * k + 6) * gridUnit (P + 2) := by ring
        _ ≤ 2 ^ P * gridUnit (P + 2) := mul_le_mul_of_nonneg_right hbig hv0.le
        _ ≤ 1 := by rw [h4]; norm_num
    have hprod : (l.map (fun i => (t i : ℝ))).prod ≤ (2 : ℝ) ^ k := by
      have hdvd := (hsub.map t).prod_dvd_prod
      rw [← Fin.prod_univ_def] at hdvd
      have hle : (l.map t).prod ≤ 2 ^ k := by
        rw [← hR]; exact Nat.le_of_dvd (by rw [hR]; positivity) hdvd
      have hcast : (l.map (fun i => (t i : ℝ))).prod = (((l.map t).prod : ℕ) : ℝ) := by
        rw [Nat.cast_list_prod, List.map_map]; rfl
      rw [hcast]; exact_mod_cast hle
    -- the chain bound on the prefix
    have hωP : schedOmega p k d ≤ P := by
      have hlg : lg d ≤ k := by
        unfold lg
        have h1 : Nat.clog 2 d ≤ d := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
        exact max_le (h1.trans hdk) (by omega)
      unfold schedOmega; omega
    have hC : LemmaCParams P (schedOmega p k d) (alphaDefault (schedOmega p k d)) :=
      lemmaCParams_default (by omega) (by unfold schedOmega; omega) hωP
    obtain ⟨hnorm, -⟩ := PrecisionDeconvProof.deconv_chain_list hCiv hCv hBv hBax rr hrr hC hsh hT l
      hlnz hsum Y0
    rw [max_eq_left hY0n, one_mul] at hnorm
    have h64 : 0 ≤ 64 * gridUnit (P + 2) * (l.map (fun i => (t i : ℝ))).sum :=
      mul_nonneg (mul_nonneg (by norm_num) hv0.le) hS0
    have hZ : ‖l.foldl (fun Z i => deconvAxisFixedR rr (P + 2) t T i Z) Y0‖ ≤ 2 ^ k * 2 :=
      hnorm.trans (mul_le_mul hprod (by linarith) (by linarith) (by positivity))
    have hZf : ‖l.foldl (fun Z i => deconvAxisFixedR rr (P + 2) t T i Z) Y0 f‖ < (2 : ℝ) ^ (k + 5) := by
      have h1 := norm_le_pi_norm (l.foldl (fun Z i => deconvAxisFixedR rr (P + 2) t T i Z) Y0) f
      have h2 : (0 : ℝ) < 2 ^ k := by positivity
      have h3 : (2 : ℝ) ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
      rw [h3]; linarith
    exact fitsWidth_of_norm_lt hg hZf (by omega)

end SubNLogN.Math.Bridge
