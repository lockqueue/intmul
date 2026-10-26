import SubNLogN.Math.Bridge.Precision
import SubNLogN.Math.Bridge.Proofs.DeconvContract

/-!
# Bridge: Theorem 4.7 — spreading admissibility and the arithmetic error

Proofs of two contracts of `SubNLogN/Math/Bridge/Precision.lean` (Section 4.5,
proof of Theorem 4.7 (`thm:bridge-precision`)):

* `bridge_spread_admissible_of (hM hCi hCii) : Bridge_spread_admissibleStmt`, from the master
  margin (`Master_marginStmt`), Lemma 4.6 (bridge Lemma C)(i) (`LemmaC_i_normsStmt`, filter norms) and Lemma 4.6 (bridge Lemma C)(ii)
  (`LemmaC_iiStmt`, one fixed-point spreading stage).
* `bridge_arith_error_of (hM hCi hCii hCvi hdc) : Bridge_arith_errorStmt`, additionally from
  Lemma 4.6 (bridge Lemma C)(vi) (`LemmaC_viStmt`, `‖(B_2⋯B_d)^{-1}‖_∞ ≤ R/t_1`) and the deconvolution-chain contract
  `Deconv_chainStmt` (`Proofs/DeconvContract.lean`; proved as `deconv_chain_of` in
  `Proofs/Precision_Deconv.lean`).

Reusable lemmas (namespace `SubNLogN.Math.Bridge.PrecisionArith`):
* pre-scaling (proof of Theorem 4.7 (`thm:bridge-precision`)): `preScaleC` (= `C`), `le_two_pow_preScaleH`
  (`X ≤ 2^H`), `two_pow_preScaleH_lt` (`2^H < 4X`), `preScaleH_toNat_le` (`H ≤ p+1`),
  `le_two_pow_preScaleExp` (`16 √D X ≤ S`), `two_pow_preScaleExp_le` (`S ≤ 128 D X`),
  `preScaleExp_le` (exponent `≤ p+k+6`), `norm_preScaled_le` (`‖x'‖_∞ ≤ 1/(16√D)`),
  `preScaled_onGrid` (`x'` exact on the `q`-grid);
* shape and schedule: `shapeOK_of_balanced`, `le_of_balanced` (`d ≤ k`), `lemmaCParams_sched`
  (the Lemma 4.6 (bridge Lemma C) hypotheses at `(P, ω, α)` of eq. (`eq:schedule`)), `alphaDefault_admissible'`,
  `schedP_ge`, `dimD_le_totalLen`, `le_totalLen`;
* generic error propagation: `chain_spread_bound` (a chain of perturbed maps with a uniform local
  error on a "good" set inside the unit ball);
* spreading: `foldedFilter_add_period`, `fracShift_mem` (`δ_h ∈ [0,1)`), `norm_spreadAxis_le`
  (`‖S_h z‖_∞ ≤ √t_h ‖z‖_∞`), `spread_chain` (grid membership, `E_spread ≤ 4(P+1) v d √D`,
  `‖S_2⋯S_d V‖ ≤ ‖V‖ √D`), `spreadStage_facts` (all spreading facts of Theorem 4.7, incl. `‖U‖ ≤ 1/8`).

All bridge roundings are an arbitrary componentwise nearest rounding `rr` (`IsNearestRounding rr`,
`SubNLogN/Math/Common/RoundNearest.lean`); rounding enters these proofs only through the contracts
`LemmaC_iiStmt` and `Deconv_chainStmt`, so no property of a particular tie rule is used.

Constants versus the paper (all in the safe direction): `E_spread ≤ 4(P+1) v d √D` (paper:
`16 d(P+1)√D v`); `S ≤ 128 D X` (paper: `S < 128 √D X`; only `D ≤ R` is used afterwards); the
normalized arithmetic error is `≤ 84 d(P+1) R² v` (paper: `96 d(P+1)R² v`), so the final bound is
`10752 d(P+1) R³ v X ≤ 2^{14} d(P+1) R³ v X ≤ 2^{-p-12} X`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace PrecisionArith

/-! ## Pre-scaling (proof of Theorem 4.7 (`thm:bridge-precision`)) -/

section PreScale

variable {R : ℕ}

/-- `C = max(1, max_j |Re x_j|, max_j |Im x_j|)` (proof of Theorem 4.7 (`thm:bridge-precision`)). -/
noncomputable def preScaleC (x : Fin R → ℂ) : ℝ :=
  max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖)

theorem preScaleH_eq (x : Fin R → ℂ) : preScaleH x = 1 + Int.clog 2 (preScaleC x) := rfl

theorem one_le_preScaleC (x : Fin R → ℂ) : 1 ≤ preScaleC x := le_max_left _ _

theorem preScaleC_pos (x : Fin R → ℂ) : 0 < preScaleC x :=
  lt_of_lt_of_le one_pos (one_le_preScaleC x)

/-- `C ≤ X`, where `X = max(1, ‖x‖_∞)`. -/
theorem preScaleC_le (x : Fin R → ℂ) : preScaleC x ≤ max 1 ‖x‖ := by
  unfold preScaleC
  refine max_le_max le_rfl (max_le ?_ ?_)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm x j)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm x j)

/-- `X ≤ 2C`. -/
theorem le_two_mul_preScaleC (x : Fin R → ℂ) : max 1 ‖x‖ ≤ 2 * preScaleC x := by
  have hC1 := one_le_preScaleC x
  have h4 : ‖fun j => (x j).re‖ ≤ preScaleC x := (le_max_left _ _).trans (le_max_right _ _)
  have h5 : ‖fun j => (x j).im‖ ≤ preScaleC x := (le_max_right _ _).trans (le_max_right _ _)
  refine max_le (by linarith) ((pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_)
  have h1 := Complex.norm_le_abs_re_add_abs_im (x j)
  have h2 : |(x j).re| ≤ ‖fun j => (x j).re‖ := by
    have := norm_le_pi_norm (fun j => (x j).re) j
    rwa [Real.norm_eq_abs] at this
  have h3 : |(x j).im| ≤ ‖fun j => (x j).im‖ := by
    have := norm_le_pi_norm (fun j => (x j).im) j
    rwa [Real.norm_eq_abs] at this
  linarith

theorem clog_preScaleC_nonneg (x : Fin R → ℂ) : 0 ≤ Int.clog 2 (preScaleC x) := by
  rw [Int.clog_of_one_le_right 2 (one_le_preScaleC x)]
  exact Nat.cast_nonneg _

/-- `H = 1 + ⌈log₂ C⌉ ≥ 1`, so `H.toNat = H`. -/
theorem preScaleH_toNat_cast (x : Fin R → ℂ) :
    ((preScaleH x).toNat : ℤ) = 1 + Int.clog 2 (preScaleC x) := by
  rw [Int.toNat_of_nonneg (by rw [preScaleH_eq]; linarith [clog_preScaleC_nonneg x])]
  rfl

theorem two_pow_preScaleH (x : Fin R → ℂ) :
    (2 : ℝ) ^ (preScaleH x).toNat = 2 * (2 : ℝ) ^ (Int.clog 2 (preScaleC x)) := by
  rw [← zpow_natCast, preScaleH_toNat_cast, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]

/-- `X ≤ 2^H` (proof of Theorem 4.7 (`thm:bridge-precision`)). -/
theorem le_two_pow_preScaleH (x : Fin R → ℂ) : max 1 ‖x‖ ≤ (2 : ℝ) ^ (preScaleH x).toNat := by
  rw [two_pow_preScaleH]
  have h := Int.self_le_zpow_clog (R := ℝ) (b := 2) (by norm_num) (preScaleC x)
  push_cast at h
  linarith [le_two_mul_preScaleC x]

/-- `2^H < 4X` (proof of Theorem 4.7 (`thm:bridge-precision`)). -/
theorem two_pow_preScaleH_lt (x : Fin R → ℂ) :
    (2 : ℝ) ^ (preScaleH x).toNat < 4 * max 1 ‖x‖ := by
  rw [two_pow_preScaleH]
  have h := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 2) (by norm_num) (preScaleC_pos x)
  push_cast at h
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] at h
  linarith [preScaleC_le x]

/-- `H ≤ p + 1` when `‖x‖_∞ ≤ 2^p` (proof of Theorem 4.7 (`thm:bridge-precision`)). -/
theorem preScaleH_toNat_le (x : Fin R → ℂ) (p : ℕ) (hx : ‖x‖ ≤ (2 : ℝ) ^ p) :
    (preScaleH x).toNat ≤ p + 1 := by
  have hC : preScaleC x ≤ ((2 : ℕ) : ℝ) ^ (p : ℤ) := by
    rw [zpow_natCast]
    push_cast
    exact (preScaleC_le x).trans (max_le (one_le_pow₀ (by norm_num)) hx)
  have h := (Int.le_zpow_iff_clog_le (R := ℝ) (b := 2) (by norm_num) (preScaleC_pos x)).1 hC
  have h2 := preScaleH_toNat_cast x
  omega

end PreScale

section Lg

theorem one_le_lg' (n : ℕ) : 1 ≤ lg n := le_max_right _ _

theorem le_two_pow_lg' (n : ℕ) : n ≤ 2 ^ lg n :=
  (Nat.le_pow_clog (by norm_num) n).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

theorem two_pow_lg_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ lg n ≤ 2 * n := by
  unfold lg
  rcases Nat.lt_or_ge 1 n with h | h
  · have hc := Nat.clog_pos (b := 2) (by norm_num) h
    rw [max_eq_left (by omega)]
    have h2 : 2 ^ (Nat.clog 2 n - 1) < n := by
      simpa [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h3 : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have hn1 : n = 1 := by omega
    subst hn1
    simp [Nat.clog_one_right]

theorem lg_le_of_le_two_pow {n k : ℕ} (h : n ≤ 2 ^ k) : lg n ≤ k + 1 := by
  unfold lg
  have := Nat.clog_le_of_le_pow h
  exact max_le (by omega) (by omega)

theorem lg_le_self {n : ℕ} (hn : 1 ≤ n) : lg n ≤ n := by
  unfold lg
  exact max_le (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le) hn

/-- `√n ≤ 2^{⌈(lg n)/2⌉}`, with `⌈(lg n)/2⌉ = (lg n + 1)/2`. -/
theorem sqrt_le_two_pow_half_lg (n : ℕ) : Real.sqrt n ≤ (2 : ℝ) ^ ((lg n + 1) / 2) := by
  have h1 : (n : ℝ) ≤ ((2 : ℝ) ^ ((lg n + 1) / 2)) ^ 2 := by
    rw [← pow_mul]
    calc (n : ℝ) ≤ (2 : ℝ) ^ lg n := by exact_mod_cast le_two_pow_lg' n
      _ ≤ (2 : ℝ) ^ ((lg n + 1) / 2 * 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc Real.sqrt n ≤ Real.sqrt (((2 : ℝ) ^ ((lg n + 1) / 2)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = (2 : ℝ) ^ ((lg n + 1) / 2) := Real.sqrt_sq (by positivity)

/-- `2^{⌈(lg n)/2⌉} ≤ 2n` for `n ≥ 1`. -/
theorem two_pow_half_lg_le (n : ℕ) (hn : 1 ≤ n) : (2 : ℝ) ^ ((lg n + 1) / 2) ≤ 2 * n := by
  have h1 : (lg n + 1) / 2 ≤ lg n := by have := one_le_lg' n; omega
  calc (2 : ℝ) ^ ((lg n + 1) / 2) ≤ (2 : ℝ) ^ lg n := pow_le_pow_right₀ (by norm_num) h1
    _ ≤ 2 * n := by exact_mod_cast two_pow_lg_le n hn

end Lg

section Shape

variable {d : ℕ}

theorem one_le_dimD (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) : 1 ≤ dimD t := by
  have h : 0 < dimD t := by
    unfold dimD
    exact Finset.prod_pos fun i _ => ht i
  omega

theorem dimD_le_totalLen (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) : dimD t ≤ totalLen t := by
  unfold dimD totalLen
  exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) (fun i _ _ => ht i)

theorem le_totalLen (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (i : Fin d) : t i ≤ totalLen t :=
  Finset.single_le_prod' (fun j _ => ht j) (Finset.mem_univ i)

theorem shapeOK_of_balanced {t : Fin d → ℕ} {k ℓ : ℕ} (h : BalancedShape t k ℓ) : ShapeOK t := by
  intro i
  obtain ⟨_, _, hℓ, _, hall⟩ := h
  have h4 : 4 ≤ 2 ^ ℓ := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  rcases hall i with h1 | h1
  · exact ⟨by omega, ℓ, h1⟩
  · refine ⟨by omega, ℓ - 1, ?_⟩
    have : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem one_le_of_shapeOK {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) : 1 ≤ t i :=
  le_trans (by norm_num) (ht i).1

theorem le_of_balanced {t : Fin d → ℕ} {k ℓ : ℕ} (h : BalancedShape t k ℓ) : d ≤ k := by
  have hs := shapeOK_of_balanced h
  have hR : totalLen t = 2 ^ k := h.2.1
  have h2 : 2 ^ d ≤ totalLen t := by
    calc 2 ^ d = ∏ _i : Fin d, 2 := by simp
      _ ≤ ∏ i, t i := Finset.prod_le_prod (fun i _ => by norm_num) (fun i _ => (hs i).1)
  rw [hR] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

theorem schedP_ge (p k : ℕ) : 2 * p + 12 * k + 256 ≤ schedP p k := by
  unfold schedP; omega

theorem lemmaCParams_sched {p k d : ℕ} (hp : max 8 k ≤ p) (hd1 : 1 ≤ d) (hdk : d ≤ k) :
    LemmaCParams (schedP p k) (schedOmega p k d) (alphaDefault (schedOmega p k d)) := by
  have hP := schedP_ge p k
  have hlg := lg_le_self hd1
  have h8 : 8 ≤ p := le_trans (le_max_left _ _) hp
  refine ⟨by omega, by unfold schedOmega; omega, by unfold schedOmega; omega, ?_, 1, le_rfl,
    by norm_num, ?_⟩
  · exact IntMul.alphaSchedule_pos _ (by unfold schedOmega; omega)
  · show (IntMul.alphaSchedule _) ^ 2 = _
    unfold IntMul.alphaSchedule
    rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by norm_num))) Real.pi_pos.le)]
    push_cast
    ring

theorem alphaDefault_admissible' (ω : ℕ) : AlphaAdmissible ω (alphaDefault ω) := by
  unfold AlphaAdmissible alphaDefault IntMul.alphaSchedule
  refine ⟨le_rfl, ?_⟩
  have := Real.sqrt_nonneg ((ω : ℝ) * Real.log 2 / Real.pi)
  linarith

end Shape

/-! ## Generic error propagation along a chain of perturbed maps -/

section Chain

variable {E ι : Type*} [SeminormedAddCommGroup E]

/-- A list product of reals that are all `≥ 1` is `≥ 1`. -/
theorem one_le_prod_map_of_one_le {l : List ι} {a : ι → ℝ} (ha : ∀ i ∈ l, 1 ≤ a i) :
    1 ≤ (l.map a).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons]
    have h1 : 1 ≤ a i := ha i (List.mem_cons.2 (Or.inl rfl))
    have h2 : 1 ≤ (l.map a).prod := ih (fun j hj => ha j (List.mem_cons.2 (Or.inr hj)))
    nlinarith

/-- **Perturbed chain, uniform local error on a good set.** Let `M_i` be `a_i`-Lipschitz maps with
`‖M_i z‖ ≤ a_i ‖z‖` and `a_i ≥ 1`, and let `F_i` be approximations such that, for every good `z` with
`‖z‖ ≤ 1`, `F_i z` is good and `‖F_i z - M_i z‖ ≤ η`. Run both chains along `l` from good `z₀`
and from `w₀` with `‖w₀‖ ≤ b`, `‖z₀ - w₀‖ ≤ e`. If `(b + e + η |l|) ∏ a_i ≤ 1` (so every computed
state stays in the unit ball), then the computed result is good, its distance to the exact result is
at most `(e + η |l|) ∏ a_i`, and the exact result has norm at most `b ∏ a_i`. -/
theorem chain_spread_bound (F M : ι → E → E) (a : ι → ℝ) (η : ℝ) (Good : E → Prop) :
    ∀ (l : List ι), (∀ i ∈ l, 1 ≤ a i) → 0 ≤ η →
    (∀ i ∈ l, ∀ z w, ‖M i z - M i w‖ ≤ a i * ‖z - w‖) →
    (∀ i ∈ l, ∀ z, ‖M i z‖ ≤ a i * ‖z‖) →
    (∀ i ∈ l, ∀ z, Good z → ‖z‖ ≤ 1 → Good (F i z) ∧ ‖F i z - M i z‖ ≤ η) →
    ∀ (z₀ w₀ : E) (b e : ℝ), Good z₀ → ‖w₀‖ ≤ b → ‖z₀ - w₀‖ ≤ e →
      (b + e + η * l.length) * (l.map a).prod ≤ 1 →
      Good (l.foldl (fun z i => F i z) z₀) ∧
      ‖l.foldl (fun z i => F i z) z₀ - l.foldl (fun z i => M i z) w₀‖ ≤
        (e + η * l.length) * (l.map a).prod ∧
      ‖l.foldl (fun z i => M i z) w₀‖ ≤ b * (l.map a).prod := by
  intro l
  induction l with
  | nil =>
    intro _ _ _ _ _ z₀ w₀ b e hz₀ hw₀ hzw _
    simp only [List.foldl_nil, List.map_nil, List.prod_nil, List.length_nil, mul_one,
      Nat.cast_zero, mul_zero, add_zero]
    exact ⟨hz₀, hzw, hw₀⟩
  | cons i l ih =>
    intro ha hη hMl hMn hF z₀ w₀ b e hz₀ hw₀ hzw hcond
    have hmem : i ∈ i :: l := List.mem_cons.2 (Or.inl rfl)
    have hsub : ∀ j ∈ l, j ∈ i :: l := fun j hj => List.mem_cons.2 (Or.inr hj)
    have hai : 1 ≤ a i := ha i hmem
    have hA : 1 ≤ (l.map a).prod := one_le_prod_map_of_one_le (fun j hj => ha j (hsub j hj))
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one] at hcond ⊢
    have hb : 0 ≤ b := (norm_nonneg _).trans hw₀
    have he : 0 ≤ e := (norm_nonneg _).trans hzw
    have hn : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    have hηn : 0 ≤ η * ((l.length : ℝ) + 1) := by positivity
    have hprod : 1 ≤ a i * (l.map a).prod := by nlinarith
    have hz₀n : ‖z₀‖ ≤ 1 := by
      have h1 : ‖z₀‖ ≤ b + e := by
        calc ‖z₀‖ = ‖w₀ + (z₀ - w₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖w₀‖ + ‖z₀ - w₀‖ := norm_add_le _ _
          _ ≤ b + e := add_le_add hw₀ hzw
      have h2 : b + e + η * ((l.length : ℝ) + 1) ≤
          (b + e + η * ((l.length : ℝ) + 1)) * (a i * (l.map a).prod) := by
        nlinarith
      linarith
    obtain ⟨hg₁, hF₁⟩ := hF i hmem z₀ hz₀ hz₀n
    have he₁ : ‖F i z₀ - M i w₀‖ ≤ η + a i * e := by
      calc ‖F i z₀ - M i w₀‖ = ‖(F i z₀ - M i z₀) + (M i z₀ - M i w₀)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖F i z₀ - M i z₀‖ + ‖M i z₀ - M i w₀‖ := norm_add_le _ _
        _ ≤ η + a i * e := add_le_add hF₁
            ((hMl i hmem z₀ w₀).trans (mul_le_mul_of_nonneg_left hzw (by linarith)))
    have hb₁ : ‖M i w₀‖ ≤ a i * b :=
      (hMn i hmem w₀).trans (mul_le_mul_of_nonneg_left hw₀ (by linarith))
    have hX : a i * b + (η + a i * e) + η * l.length ≤
        a i * (b + e + η * ((l.length : ℝ) + 1)) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hai) hηn]
    have hcond₁ : (a i * b + (η + a i * e) + η * l.length) * (l.map a).prod ≤ 1 := by
      calc (a i * b + (η + a i * e) + η * l.length) * (l.map a).prod
          ≤ a i * (b + e + η * ((l.length : ℝ) + 1)) * (l.map a).prod :=
            mul_le_mul_of_nonneg_right hX (by linarith)
        _ = (b + e + η * ((l.length : ℝ) + 1)) * (a i * (l.map a).prod) := by ring
        _ ≤ 1 := hcond
    obtain ⟨hg, herr, hnrm⟩ := ih (fun j hj => ha j (hsub j hj)) hη
      (fun j hj => hMl j (hsub j hj)) (fun j hj => hMn j (hsub j hj))
      (fun j hj => hF j (hsub j hj)) (F i z₀) (M i w₀) (a i * b) (η + a i * e) hg₁ hb₁ he₁ hcond₁
    refine ⟨hg, ?_, ?_⟩
    · have hY : η + a i * e + η * l.length ≤ a i * (e + η * ((l.length : ℝ) + 1)) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hai) hηn]
      calc _ ≤ (η + a i * e + η * l.length) * (l.map a).prod := herr
        _ ≤ a i * (e + η * ((l.length : ℝ) + 1)) * (l.map a).prod :=
            mul_le_mul_of_nonneg_right hY (by linarith)
        _ = (e + η * ((l.length : ℝ) + 1)) * (a i * (l.map a).prod) := by ring
    · calc _ ≤ a i * b * (l.map a).prod := hnrm
        _ = b * (a i * (l.map a).prod) := by ring

end Chain


/-! ## Spreading (proof of Theorem 4.7 (`thm:bridge-precision`)) -/

section Spread

variable {d : ℕ}

/-- The folded filter is `t`-periodic in the offset (reindex `m ↦ m + 1` in the defining sum). -/
theorem foldedFilter_add_period (α : ℝ) (t : ℕ) (δ : ℝ) (e : ℤ) :
    foldedFilter α t δ (e + t) = foldedFilter α t δ e := by
  unfold foldedFilter
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun m : ℤ => carrier α t ((e : ℝ) + (m : ℝ) * (t : ℝ) + δ))]
  congr 1
  funext m
  simp only [Equiv.coe_addRight]
  congr 1
  push_cast
  ring

/-- Sums of a `T`-periodic function over a shifted period agree. -/
theorem sum_fin_sub_eq_of_periodic {T : ℕ} (g : ℤ → ℝ) (hg : ∀ e, g (e + T) = g e) (c : Fin T) :
    ∑ a : Fin T, g (((a : ℕ) : ℤ) - ((c : ℕ) : ℤ)) = ∑ e : Fin T, g ((e : ℕ) : ℤ) := by
  have : NeZero T := ⟨by have := c.isLt; omega⟩
  refine Fintype.sum_equiv (Equiv.subRight c) _ _ fun a => ?_
  simp only [Equiv.subRight_apply]
  rcases le_or_gt c a with h | h
  · rw [Fin.coe_sub_iff_le.2 h, Nat.cast_sub (Fin.le_iff_val_le_val.1 h)]
  · rw [Fin.coe_sub_iff_lt.2 h]
    have hlt : (c : ℕ) < T := c.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_add, ← hg]
    congr 1
    ring

theorem prefixProd_pos' (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (n : ℕ) : 0 < prefixProd t n :=
  Finset.prod_pos fun i _ => ht i

/-- Mixed-radix bound `∑_{l<n} k_l A_l < A_n`. -/
theorem sum_lt_prefixProd (t : Fin d → ℕ) (k : Idx t) (n : ℕ) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin d => (l : ℕ) < n), (k l : ℕ) * prefixProd t l <
      prefixProd t n := by
  induction n with
  | zero => simp [prefixProd]
  | succ n ih =>
    by_cases hn : n < d
    · have hset : Finset.univ.filter (fun l : Fin d => (l : ℕ) < n + 1) =
          insert (⟨n, hn⟩ : Fin d) (Finset.univ.filter (fun l : Fin d => (l : ℕ) < n)) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        constructor
        · intro h; omega
        · intro h; omega
      have hnot : (⟨n, hn⟩ : Fin d) ∉ Finset.univ.filter (fun l : Fin d => (l : ℕ) < n) := by
        simp
      have hpp : prefixProd t (n + 1) = t ⟨n, hn⟩ * prefixProd t n := by
        unfold prefixProd
        rw [hset, Finset.prod_insert hnot]
      rw [hset, Finset.sum_insert hnot, hpp]
      have hk : (k ⟨n, hn⟩ : ℕ) + 1 ≤ t ⟨n, hn⟩ := (k ⟨n, hn⟩).isLt
      have hval : ((⟨n, hn⟩ : Fin d) : ℕ) = n := rfl
      rw [hval]
      nlinarith
    · have hset : Finset.univ.filter (fun l : Fin d => (l : ℕ) < n + 1) =
          Finset.univ.filter (fun l : Fin d => (l : ℕ) < n) := by
        ext l
        have := l.isLt
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; omega
        · intro h; omega
      have hpp : prefixProd t (n + 1) = prefixProd t n := by
        unfold prefixProd
        rw [hset]
      rw [hset, hpp]
      exact ih

theorem lowerIndex_lt_prefixProd (t : Fin d → ℕ) (i : Fin d) (k : Idx t) :
    lowerIndex t i k < prefixProd t i := by
  have h := sum_lt_prefixProd t k i
  unfold lowerIndex
  have hset : Finset.univ.filter (fun l : Fin d => l < i) =
      Finset.univ.filter (fun l : Fin d => (l : ℕ) < (i : ℕ)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  rw [hset]
  exact h

/-- `δ_h(k) ∈ [0,1)`. -/
theorem fracShift_mem (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (i : Fin d) (k : Idx t) :
    0 ≤ fracShift t i k ∧ fracShift t i k < 1 := by
  unfold fracShift
  have hA : (0 : ℝ) < prefixProd t i := by exact_mod_cast prefixProd_pos' t ht i
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hA]
  exact_mod_cast lowerIndex_lt_prefixProd t i k

/-- `S_h` is linear: `S_h z - S_h w = S_h (z - w)`. -/
theorem spreadAxis_sub (α : ℝ) (t : Fin d → ℕ) (i : Fin d) (z w : Idx t → ℂ) :
    spreadAxis α t i z - spreadAxis α t i w = spreadAxis α t i (z - w) := by
  funext k
  simp only [spreadAxis, Pi.sub_apply, ← Finset.sum_sub_distrib, sub_mul]

/-- `‖S_h z‖_∞ ≤ √t_h ‖z‖_∞` (Lemma 4.6 (bridge Lemma C)(i): `‖H_δ‖_1 ≤ √t_h` over one period;
proof of Theorem 4.7 (`thm:bridge-precision`)). -/
theorem norm_spreadAxis_le (hCi : LemmaC_i_normsStmt) {P ω : ℕ} {α : ℝ}
    (hC : LemmaCParams P ω α) (t : Fin d → ℕ) (ht : ShapeOK t) (i : Fin d) (z : Idx t → ℂ) :
    ‖spreadAxis α t i z‖ ≤ Real.sqrt (t i) * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have hδ := fracShift_mem t (fun j => one_le_of_shapeOK ht j) i k
  have hl1 := (hCi P ω α hC (t i) (ht i) (fracShift t i k) hδ).2
  have hper : ∀ e : ℤ, ‖foldedFilter α (t i) (fracShift t i k) (e + (t i : ℕ))‖ =
      ‖foldedFilter α (t i) (fracShift t i k) e‖ := fun e => by
    rw [foldedFilter_add_period]
  have hsum := sum_fin_sub_eq_of_periodic
    (fun e => ‖foldedFilter α (t i) (fracShift t i k) e‖) hper (k i)
  unfold spreadAxis
  calc ‖∑ a : Fin (t i), z (Function.update k i a) *
          foldedFilter α (t i) (fracShift t i k) ((a : ℤ) - ((k i : ℕ) : ℤ))‖
      ≤ ∑ a : Fin (t i), ‖z (Function.update k i a)‖ *
          ‖foldedFilter α (t i) (fracShift t i k) ((a : ℤ) - ((k i : ℕ) : ℤ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_mul _ _).le)
    _ ≤ ∑ a : Fin (t i), ‖z‖ *
          ‖foldedFilter α (t i) (fracShift t i k) ((a : ℤ) - ((k i : ℕ) : ℤ))‖ :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_right (norm_le_pi_norm z _) (norm_nonneg _)
    _ = ‖z‖ * l1Norm (fun e : Fin (t i) => foldedFilter α (t i) (fracShift t i k) ((e : ℕ) : ℤ)) := by
        rw [← Finset.mul_sum]
        congr 1
    _ ≤ ‖z‖ * Real.sqrt (t i) := mul_le_mul_of_nonneg_left hl1 (norm_nonneg _)
    _ = Real.sqrt (t i) * ‖z‖ := mul_comm _ _

theorem prod_map_sqrt (t : Fin d → ℕ) (l : List (Fin d)) :
    (l.map (fun i => Real.sqrt (t i))).prod = Real.sqrt (((l.map t).prod : ℕ) : ℝ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _)]

theorem spreadOrder_nodup (d : ℕ) : (spreadOrder d).Nodup :=
  (List.nodup_reverse.2 (List.nodup_finRange d)).filter _

theorem spreadOrder_toFinset (d : ℕ) :
    (spreadOrder d).toFinset = Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0) := by
  ext i
  simp [spreadOrder]

/-- `∏_{h ∈ spreadOrder} t_h = D`. -/
theorem prod_spreadOrder (t : Fin d → ℕ) : ((spreadOrder d).map t).prod = dimD t := by
  rw [← List.prod_toFinset t (spreadOrder_nodup d), spreadOrder_toFinset]
  rfl

theorem length_spreadOrder_le (d : ℕ) : (spreadOrder d).length ≤ d :=
  (List.length_filter_le _ _).trans (by simp)

theorem ne_zero_of_mem_spreadOrder {i : Fin d} (hi : i ∈ spreadOrder d) : (i : ℕ) ≠ 0 := by
  unfold spreadOrder at hi
  simpa using (List.mem_filter.1 hi).2

/-- **Spreading induction** (proof of Theorem 4.7 (`thm:bridge-precision`)): for a `q`-grid input `V` and certified
taps, if `(‖V‖ + 4(P+1) v d) √D ≤ 1` then every computed partial spread stays in the unit ball (so
Lemma 4.6 (bridge Lemma C)(ii) applies at each of the `d-1` stages), the completed array is on the `q`-grid, its distance
to the exact `S_2⋯S_d V` is at most `E_spread ≤ 4(P+1) v d √D`, and `‖S_2⋯S_d V‖ ≤ ‖V‖ √D`. -/
theorem spread_chain (hCi : LemmaC_i_normsStmt) (hCii : LemmaC_iiStmt)
    (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) {P ω : ℕ} {α : ℝ}
    (hC : LemmaCParams P ω α) (t : Fin d → ℕ) (ht : ShapeOK t) (T : BridgeTables t)
    (hT : ∀ i : Fin d, (i : ℕ) ≠ 0 → TapsCertified α P t i (T.tap i))
    (V : Idx t → ℂ) (hV : ∀ j, OnGrid (P + 2) (V j))
    (hcond : (‖V‖ + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * d) * Real.sqrt (dimD t) ≤ 1) :
    (∀ j, OnGrid (P + 2) (spreadFixedR rr (P + 2) t T V j)) ∧
    ‖spreadFixedR rr (P + 2) t T V - spreadAll α t V‖ ≤
      4 * ((P : ℝ) + 1) * gridUnit (P + 2) * d * Real.sqrt (dimD t) ∧
    ‖spreadAll α t V‖ ≤ ‖V‖ * Real.sqrt (dimD t) := by
  have hv := gridUnit_pos (P + 2)
  have hη : 0 ≤ 4 * ((P : ℝ) + 1) * gridUnit (P + 2) := by positivity
  have hA : ((spreadOrder d).map (fun i => Real.sqrt (t i))).prod = Real.sqrt (dimD t) := by
    rw [prod_map_sqrt, prod_spreadOrder]
  have hlen : ((spreadOrder d).length : ℝ) ≤ d := by exact_mod_cast length_spreadOrder_le d
  have hsD : 0 ≤ Real.sqrt (dimD t) := Real.sqrt_nonneg _
  have hsq1 : ∀ i ∈ spreadOrder d, 1 ≤ Real.sqrt (t i) := fun i _ =>
    Real.one_le_sqrt.2 (by exact_mod_cast one_le_of_shapeOK ht i)
  have hcond' : (‖V‖ + 0 + 4 * ((P : ℝ) + 1) * gridUnit (P + 2) * (spreadOrder d).length) *
      ((spreadOrder d).map (fun i => Real.sqrt (t i))).prod ≤ 1 := by
    rw [hA]
    refine le_trans ?_ hcond
    apply mul_le_mul_of_nonneg_right _ hsD
    nlinarith
  obtain ⟨hg, herr, hnrm⟩ := chain_spread_bound
    (fun i z => spreadAxisFixedR rr (P + 2) t i (T.tap i) z) (fun i z => spreadAxis α t i z)
    (fun i => Real.sqrt (t i)) (4 * ((P : ℝ) + 1) * gridUnit (P + 2))
    (fun z => ∀ j, OnGrid (P + 2) (z j)) (spreadOrder d) hsq1 hη
    (fun i _ z w => by
      rw [spreadAxis_sub]
      exact norm_spreadAxis_le hCi hC t ht i _)
    (fun i _ z => norm_spreadAxis_le hCi hC t ht i z)
    (fun i hi z hz hzn => hCii rr hrr P ω α hC t ht i (ne_zero_of_mem_spreadOrder hi) (T.tap i)
      (hT i (ne_zero_of_mem_spreadOrder hi)) z hz hzn)
    V V ‖V‖ 0 hV le_rfl (by simp) hcond'
  refine ⟨hg, ?_, ?_⟩
  · refine herr.trans ?_
    rw [hA, zero_add]
    apply mul_le_mul_of_nonneg_right _ hsD
    nlinarith
  · rw [← hA]
    exact hnrm

end Spread

/-! ## The pre-scaling exponent `S = 2^{H + ⌈(lg D)/2⌉ + 4}` (proof of Theorem 4.7 (`thm:bridge-precision`)) -/

section PreScaleExp

variable {d : ℕ}

theorem two_pow_preScaleExp (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) :
    (2 : ℝ) ^ preScaleExp t x =
      (2 : ℝ) ^ (preScaleH x).toNat * (2 : ℝ) ^ ((lg (dimD t) + 1) / 2) * 16 := by
  unfold preScaleExp
  rw [pow_add, pow_add]
  norm_num

/-- `S ≥ 16 √D X` (proof of Theorem 4.7 (`thm:bridge-precision`)). -/
theorem le_two_pow_preScaleExp (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) :
    16 * Real.sqrt (dimD t) * max 1 ‖x‖ ≤ (2 : ℝ) ^ preScaleExp t x := by
  rw [two_pow_preScaleExp]
  have h1 := le_two_pow_preScaleH x
  have h2 := sqrt_le_two_pow_half_lg (dimD t)
  have hX : 0 ≤ max 1 ‖x‖ := le_trans zero_le_one (le_max_left _ _)
  have hs : 0 ≤ Real.sqrt (dimD t) := Real.sqrt_nonneg _
  calc 16 * Real.sqrt (dimD t) * max 1 ‖x‖ = max 1 ‖x‖ * Real.sqrt (dimD t) * 16 := by ring
    _ ≤ (2 : ℝ) ^ (preScaleH x).toNat * (2 : ℝ) ^ ((lg (dimD t) + 1) / 2) * 16 := by gcongr

/-- `S ≤ 128 D X` (proof of Theorem 4.7 (`thm:bridge-precision`) has `S < 128 √D X`; `D` is used here, which is
cruder but suffices with `D ≤ R`). -/
theorem two_pow_preScaleExp_le (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (x : Fin (totalLen t) → ℂ) :
    (2 : ℝ) ^ preScaleExp t x ≤ 128 * (dimD t : ℝ) * max 1 ‖x‖ := by
  rw [two_pow_preScaleExp]
  have h1 := (two_pow_preScaleH_lt x).le
  have h2 := two_pow_half_lg_le (dimD t) (one_le_dimD t ht)
  calc (2 : ℝ) ^ (preScaleH x).toNat * (2 : ℝ) ^ ((lg (dimD t) + 1) / 2) * 16
      ≤ (4 * max 1 ‖x‖) * (2 * (dimD t : ℝ)) * 16 := by gcongr
    _ = 128 * (dimD t : ℝ) * max 1 ‖x‖ := by ring

/-- The exponent is at most `p + k + 6` when `‖x‖_∞ ≤ 2^p` and `D ≤ 2^k`. -/
theorem preScaleExp_le (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) (p k : ℕ)
    (hx : ‖x‖ ≤ (2 : ℝ) ^ p) (hD : dimD t ≤ 2 ^ k) : preScaleExp t x ≤ p + k + 6 := by
  unfold preScaleExp
  have h1 := preScaleH_toNat_le x p hx
  have h2 := lg_le_of_le_two_pow hD
  omega

/-- `‖x'‖_∞ ≤ 1/(16 √D)` (proof of Theorem 4.7 (`thm:bridge-precision`)). -/
theorem norm_preScaled_le (t : Fin d → ℕ) (ht : ∀ i, 1 ≤ t i) (x : Fin (totalLen t) → ℂ) :
    ‖preScaled t x‖ ≤ 1 / (16 * Real.sqrt (dimD t)) := by
  have hD : (1 : ℝ) ≤ dimD t := by exact_mod_cast one_le_dimD t ht
  have hs : 0 < Real.sqrt (dimD t) := Real.sqrt_pos.2 (by linarith)
  have hS := le_two_pow_preScaleExp t x
  have hSpos : (0 : ℝ) < (2 : ℝ) ^ preScaleExp t x := by positivity
  have hX : ‖x‖ ≤ max 1 ‖x‖ := le_max_right _ _
  have key : ‖x‖ / (2 : ℝ) ^ preScaleExp t x ≤ 1 / (16 * Real.sqrt (dimD t)) := by
    rw [div_le_div_iff₀ hSpos (by positivity)]
    nlinarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  unfold preScaled
  rw [norm_div, norm_pow, Complex.norm_ofNat]
  exact le_trans (div_le_div_of_nonneg_right (norm_le_pi_norm x j) hSpos.le) key

/-- Exact division by `2^n` maps the `q`-grid into the `(q+n)`-grid. -/
theorem onGrid_div_two_pow {q : ℕ} {z : ℂ} (hz : OnGrid q z) (n : ℕ) :
    OnGrid (q + n) (z / (2 : ℂ) ^ n) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    have h := ih.half
    rw [div_div, ← pow_succ] at h
    exact h

/-- `x'` is exact on the `q`-grid (proof of Theorem 4.7 (`thm:bridge-precision`)), given `p + E ≤ P`. -/
theorem preScaled_onGrid (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) {p P : ℕ}
    (hx : ∀ j, OnGrid (p + 2) (x j)) (hE : p + preScaleExp t x ≤ P) (j : Fin (totalLen t)) :
    OnGrid (P + 2) (preScaled t x j) :=
  (onGrid_div_two_pow (hx j) (preScaleExp t x)).mono (by omega)

end PreScaleExp

/-! ## Theorem 4.7: margins and the spreading stage -/

section Stage

/-- `2^{-(p+12)} ≤ 1`. -/
theorem two_zpow_neg_le_one (p : ℕ) : (2 : ℝ) ^ (-((p : ℤ) + 12)) ≤ 1 :=
  zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

/-- `√D ≤ D` for `D ≥ 1`. -/
theorem sqrt_le_self_of_one_le {D : ℝ} (hD : 1 ≤ D) : Real.sqrt D ≤ D := by
  calc Real.sqrt D ≤ Real.sqrt (D ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = D := Real.sqrt_sq (by linarith)

/-- Arithmetic of the spreading margins: with `K = d(P+1)v`, `√D ≤ R³` and `2^{14} K R³ ≤ 1`,
`4 K √D ≤ 1/16`; together with `‖x'‖ √D ≤ 1/16` this gives the condition of `spread_chain`. -/
theorem spread_margin_aux {K s R3 a : ℝ} (hK : 0 ≤ K) (hs : s ≤ R3)
    (hM : 2 ^ 14 * (K * R3) ≤ 1) (ha : a * s ≤ 1 / 16) :
    4 * K * s ≤ 1 / 16 ∧ (a + 4 * K) * s ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left hs hK
  constructor <;> nlinarith

/-- **Pre-scaling and spreading stage of Theorem 4.7** (proof of Theorem 4.7 (`thm:bridge-precision`)). Under the
hypotheses of Theorem 4.7, with `P = schedP p k`, `v = 2^{-(P+2)}`, `V = x' ∘ encIn` and the completed
fixed-point spread array `U = spreadStageR rr P t T x`:
1. `x'` is exact on the `q`-grid;
2. `U` lies on the `q`-grid;
3. `‖U - S_2⋯S_d V‖_∞ ≤ E_spread := 4(P+1) v d √D` (the paper's cruder bound is `16 d(P+1)√D v`);
4. `‖S_2⋯S_d V‖_∞ ≤ 1/16`;
5. `‖U‖_∞ ≤ 1/8`.
The Lemma 4.6 (bridge Lemma C) hypotheses (`8 ≤ ω ≤ P`, `P ≥ 20`, `α² = 4ω ln2/π`) and the margin
`4(P+1) v d √D ≤ 1/16` are derived from the schedule and eq. (`eq:master-margin`). -/
theorem spreadStage_facts (hM : Master_marginStmt) (hCi : LemmaC_i_normsStmt)
    (hCii : LemmaC_iiStmt) (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr)
    {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (hshape : BalancedShape t k ℓ)
    (hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (hx : ∀ j, OnGrid (p + 2) (x j))
    (hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t)
    (hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T) :
    (∀ j, OnGrid (schedP p k + 2) (preScaled t x j)) ∧
    (∀ j, OnGrid (schedP p k + 2) (spreadStageR rr (schedP p k) t T x j)) ∧
    ‖spreadStageR rr (schedP p k) t T x -
        spreadAll (alphaDefault (schedOmega p k d)) t (fun j => preScaled t x (encIn t j))‖ ≤
      4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d * Real.sqrt (dimD t) ∧
    ‖spreadAll (alphaDefault (schedOmega p k d)) t (fun j => preScaled t x (encIn t j))‖ ≤
      1 / 16 ∧
    ‖spreadStageR rr (schedP p k) t T x‖ ≤ 1 / 8 := by
  have hs := shapeOK_of_balanced hshape
  have ht1 : ∀ i, 1 ≤ t i := fun i => one_le_of_shapeOK hs i
  have hd2 : 2 ≤ d := hshape.1
  have hdk : d ≤ k := le_of_balanced hshape
  have hR : totalLen t = 2 ^ k := hshape.2.1
  have hC := lemmaCParams_sched (d := d) hp (by omega) hdk
  have hMM := (hM p k d hp (by omega) hdk).trans (two_zpow_neg_le_one p)
  have hPge := schedP_ge p k
  have hv : 0 < gridUnit (schedP p k + 2) := gridUnit_pos _
  have hD1 : (1 : ℝ) ≤ dimD t := by exact_mod_cast one_le_dimD t ht1
  have hDR : (dimD t : ℝ) ≤ (2 : ℝ) ^ k := by
    have h := dimD_le_totalLen t ht1
    rw [hR] at h
    exact_mod_cast h
  have hsD0 : 0 < Real.sqrt (dimD t) := Real.sqrt_pos.2 (by linarith)
  have hsDD := sqrt_le_self_of_one_le hD1
  have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hR3 : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ 3 := le_self_pow₀ hR1 (by norm_num)
  have hK : 0 ≤ (d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) := by positivity
  have h1 : Real.sqrt (dimD t) ≤ ((2 : ℝ) ^ k) ^ 3 := le_trans hsDD (le_trans hDR hR3)
  have hMM' : (2 : ℝ) ^ 14 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) *
      ((2 : ℝ) ^ k) ^ 3) ≤ 1 := by
    have h3 : (2 : ℝ) ^ 14 * (d : ℝ) * ((schedP p k : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 3 *
        gridUnit (schedP p k + 2) =
        2 ^ 14 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) *
          ((2 : ℝ) ^ k) ^ 3) := by ring
    rw [← h3]; exact hMM
  -- the pre-scaled input
  have hE : p + preScaleExp t x ≤ schedP p k := by
    have h := preScaleExp_le t x p k hxn (by rw [← hR]; exact dimD_le_totalLen t ht1)
    omega
  have hpre : ∀ j, OnGrid (schedP p k + 2) (preScaled t x j) := preScaled_onGrid t x hx hE
  have hVn : ‖(fun j => preScaled t x (encIn t j))‖ ≤ 1 / (16 * Real.sqrt (dimD t)) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    exact (norm_le_pi_norm (preScaled t x) _).trans (norm_preScaled_le t ht1 x)
  have hVs : ‖(fun j => preScaled t x (encIn t j))‖ * Real.sqrt (dimD t) ≤ 1 / 16 := by
    calc ‖(fun j => preScaled t x (encIn t j))‖ * Real.sqrt (dimD t)
        ≤ 1 / (16 * Real.sqrt (dimD t)) * Real.sqrt (dimD t) :=
          mul_le_mul_of_nonneg_right hVn hsD0.le
      _ = 1 / 16 := by field_simp
  obtain ⟨hm1', hcond'⟩ := spread_margin_aux hK h1 hMM' hVs
  -- margin: `4(P+1) v d √D ≤ 1/16`
  have hm1 : 4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d *
      Real.sqrt (dimD t) ≤ 1 / 16 := by
    have e : 4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d * Real.sqrt (dimD t) =
        4 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2)) *
          Real.sqrt (dimD t) := by ring
    rw [e]; exact hm1'
  have hcond : (‖(fun j => preScaled t x (encIn t j))‖ +
      4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d) * Real.sqrt (dimD t) ≤ 1 := by
    have e : 4 * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2) * d =
        4 * ((d : ℝ) * ((schedP p k : ℝ) + 1) * gridUnit (schedP p k + 2)) := by ring
    rw [e]; exact hcond'
  obtain ⟨hg, herr, hnrm⟩ := spread_chain hCi hCii rr hrr hC t hs T (fun i hi => (hT i hi).1)
    (fun j => preScaled t x (encIn t j)) (fun j => hpre _) hcond
  refine ⟨hpre, hg, herr, hnrm.trans hVs, ?_⟩
  calc ‖spreadStageR rr (schedP p k) t T x‖
      ≤ ‖spreadAll (alphaDefault (schedOmega p k d)) t (fun j => preScaled t x (encIn t j))‖ +
        ‖spreadStageR rr (schedP p k) t T x -
          spreadAll (alphaDefault (schedOmega p k d)) t (fun j => preScaled t x (encIn t j))‖ :=
        norm_le_insert' _ _
    _ ≤ 1 / 16 + 1 / 16 := add_le_add (hnrm.trans hVs) (herr.trans hm1)
    _ = 1 / 8 := by norm_num

/-- `64 d + 16(P+1) + 4(P+1)d ≤ 84 d(P+1)` for `d ≥ 1`, `P ≥ 0`. -/
theorem poly_aux {dd PP : ℝ} (hd : 1 ≤ dd) (hP : 0 ≤ PP) :
    64 * dd + 16 * (PP + 1) + 4 * (PP + 1) * dd ≤ 84 * (dd * (PP + 1)) := by
  nlinarith

end Stage

end PrecisionArith

open PrecisionArith in
/-- **Theorem 4.7, spreading admissibility** (proof of Theorem 4.7 (`thm:bridge-precision`)). -/
theorem bridge_spread_admissible_of (hM : Master_marginStmt) (hCi : LemmaC_i_normsStmt)
    (hCii : LemmaC_iiStmt) : Bridge_spread_admissibleStmt := by
  intro rr hrr d t k ℓ p hshape hp x hx hxn T hT
  obtain ⟨h1, h2, -, -, h5⟩ :=
    spreadStage_facts hM hCi hCii rr hrr t k ℓ p hshape hp x hx hxn T hT
  exact ⟨h1, h2, h5⟩

open PrecisionArith in
open scoped Matrix in
/-- **Theorem 4.7, arithmetic error** (`thm:bridge-precision`):
`‖bridgePreR rr - bridgeExactScaled‖_∞ ≤ 2^{-p-12} X` for every nearest rounding `rr`.

Proof (paper's structure, with the explicit constants used here): with `v = 2^{-(P+2)}`,
`U = spreadStageR rr`, `Ŷ = run U` and `Y = F_t(S_2⋯S_d x')` (both read in frequency order),
* `‖U - S_2⋯S_d x'‖ ≤ 4(P+1) v d √D` and `‖U‖ ≤ 1/8` (`spreadStage_facts`);
* middle: `‖Ŷ - Y‖ ≤ E_mid v + 4(P+1) v d √D` (Definition 4.5 and `‖F_t‖ ≤ 1`), `‖Ŷ‖ ≤ 1/8 + E_mid v ≤ 1`;
* deconvolution chain (`Deconv_chainStmt`, needs `64 v ∑ t_h ≤ 1`):
  `‖deconvFixedR rr Ŷ - (B_2⋯B_d)^{-1} Ŷ‖ ≤ 64 D v ∑ t_h`;
* `‖(B_2⋯B_d)^{-1}‖ ≤ R/t_1 ≤ R` (Lemma 4.6 (bridge Lemma C)(vi)) amplifies `‖Ŷ - Y‖`;
* so the normalized error is `≤ 84 d (P+1) R² v`, and `S ≤ 128 D X ≤ 128 R X` gives
  `≤ 10752 d (P+1) R³ v X ≤ 2^{14} d (P+1) R³ v X ≤ 2^{-p-12} X` (eq. (`eq:master-margin`)). -/
theorem bridge_arith_error_of (hM : Master_marginStmt) (hCi : LemmaC_i_normsStmt)
    (hCii : LemmaC_iiStmt) (hCvi : LemmaC_viStmt) (hdc : Deconv_chainStmt) :
    Bridge_arith_errorStmt := by
  intro rr hrr d t k ℓ p hshape hp x hx hxn T hT Emid δmid run hmid
  obtain ⟨-, hUg, hEs, -, hUn⟩ :=
    spreadStage_facts hM hCi hCii rr hrr t k ℓ p hshape hp x hx hxn T hT
  have hs := shapeOK_of_balanced hshape
  have ht1 : ∀ i, 1 ≤ t i := fun i => one_le_of_shapeOK hs i
  have hd2 : 2 ≤ d := hshape.1
  have hd1 : 1 ≤ d := by omega
  have hdk : d ≤ k := le_of_balanced hshape
  have hR : totalLen t = 2 ^ k := hshape.2.1
  have hC := lemmaCParams_sched (d := d) hp hd1 hdk
  have hMM := hM p k d hp hd1 hdk
  have hPge := schedP_ge p k
  have hkp : k ≤ p := le_trans (le_max_right _ _) hp
  -- Step 0: `bridgePreR - bridgeExactScaled = S · (deconvFixedR Ŷ - (B_2⋯B_d)^{-1} Y)`.
  have hgoal : ‖bridgePreR rr (schedP p k) t T run x -
      bridgeExactScaled (alphaDefault (schedOmega p k d)) t x‖ ≤
      (2 : ℝ) ^ preScaleExp t x *
        ‖deconvFixedR rr (schedP p k + 2) t T
            (fun f' => run (spreadStageR rr (schedP p k) t T x) ((encFreq t).symm f')) -
          (truncProd (alphaDefault (schedOmega p k d)) t)⁻¹ *ᵥ
            (fun f' => dftTensor t (spreadAll (alphaDefault (schedOmega p k d)) t
              (fun j => preScaled t x (encIn t j))) ((encFreq t).symm f'))‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun f => ?_
    simp only [Pi.sub_apply, bridgePreR, bridgeExactScaled]
    rw [← mul_sub, norm_mul, norm_pow, Complex.norm_ofNat, ← Pi.sub_apply]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ f) (by positivity)
  refine hgoal.trans ?_
  set P := schedP p k with hPdef
  set α := alphaDefault (schedOmega p k d) with hαdef
  set v := gridUnit (P + 2) with hvdef
  set U := spreadStageR rr P t T x with hUdef
  set V : Idx t → ℂ := fun j => preScaled t x (encIn t j) with hVdef
  set Yh : Fin (totalLen t) → ℂ := fun f' => run U ((encFreq t).symm f') with hYhdef
  set Y : Fin (totalLen t) → ℂ :=
    fun f' => dftTensor t (spreadAll α t V) ((encFreq t).symm f') with hYdef
  have hv : 0 < v := gridUnit_pos _
  -- sizes
  have hRr : ((totalLen t : ℕ) : ℝ) = (2 : ℝ) ^ k := by rw [hR]; push_cast; rfl
  have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hR3 : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ 3 := le_self_pow₀ hR1 (by norm_num)
  have hD1 : (1 : ℝ) ≤ dimD t := by exact_mod_cast one_le_dimD t ht1
  have hDR : (dimD t : ℝ) ≤ (2 : ℝ) ^ k := by
    rw [← hRr]; exact_mod_cast dimD_le_totalLen t ht1
  have hsD : Real.sqrt (dimD t) ≤ (2 : ℝ) ^ k := (sqrt_le_self_of_one_le hD1).trans hDR
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hRd : (2 : ℝ) ^ k ≤ d * ((2 : ℝ) ^ k) ^ 3 :=
    le_trans hR3 (le_mul_of_one_le_left (by positivity) hdR)
  -- the base margin quantity `M_b = d (P+1) R³ v`, `2^{14} M_b ≤ 2^{-p-12} ≤ 1`
  set Mb := (d : ℝ) * ((P : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 3 * v with hMbdef
  have hMb0 : 0 ≤ Mb := by rw [hMbdef]; positivity
  have hMb : (2 : ℝ) ^ 14 * Mb ≤ (2 : ℝ) ^ (-((p : ℤ) + 12)) := by
    have e : (2 : ℝ) ^ 14 * (d : ℝ) * ((P : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 3 * v = 2 ^ 14 * Mb := by
      rw [hMbdef]; ring
    rw [← e]; exact hMM
  have hMb1 : (2 : ℝ) ^ 14 * Mb ≤ 1 := hMb.trans (two_zpow_neg_le_one p)
  -- middle step
  have hErrMid : ‖run U - dftTensor t U‖ ≤ Emid * v := hmid.err U hUg hUn
  have hEmv0 : 0 ≤ Emid * v := (norm_nonneg _).trans hErrMid
  have hlgR : (lg (totalLen t) : ℝ) ≤ P := by
    have h1 : lg (totalLen t) ≤ k + 1 := lg_le_of_le_two_pow (le_of_eq hR)
    exact_mod_cast (show lg (totalLen t) ≤ P by omega)
  have hEm : Emid * v ≤ 16 * (2 : ℝ) ^ k * ((P : ℝ) + 1) * v := by
    have h1 := mul_le_mul_of_nonneg_right hmid.Emid_le hv.le
    rw [hRr] at h1
    have h2 : 16 * (2 : ℝ) ^ k * ((lg (totalLen t) : ℝ) + 1) * v ≤
        16 * (2 : ℝ) ^ k * ((P : ℝ) + 1) * v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hv.le
    linarith
  have hFt : ‖dftTensor t U - dftTensor t (spreadAll α t V)‖ ≤ ‖U - spreadAll α t V‖ := by
    rw [← map_sub]; exact norm_dftTensor_le t _
  have hEY : ‖Yh - Y‖ ≤ Emid * v + ‖U - spreadAll α t V‖ := by
    refine (pi_norm_le_iff_of_nonneg (add_nonneg hEmv0 (norm_nonneg _))).2 fun f => ?_
    calc ‖(Yh - Y) f‖ = ‖(run U - dftTensor t (spreadAll α t V)) ((encFreq t).symm f)‖ := rfl
      _ ≤ ‖run U - dftTensor t (spreadAll α t V)‖ := norm_le_pi_norm _ _
      _ ≤ ‖run U - dftTensor t U‖ + ‖dftTensor t U - dftTensor t (spreadAll α t V)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Emid * v + ‖U - spreadAll α t V‖ := add_le_add hErrMid hFt
  have hRPv : (2 : ℝ) ^ k * ((P : ℝ) + 1) * v ≤ Mb := by
    calc (2 : ℝ) ^ k * ((P : ℝ) + 1) * v = (2 : ℝ) ^ k * (((P : ℝ) + 1) * v) := by ring
      _ ≤ (d * ((2 : ℝ) ^ k) ^ 3) * (((P : ℝ) + 1) * v) :=
          mul_le_mul_of_nonneg_right hRd (by positivity)
      _ = Mb := by rw [hMbdef]; ring
  have hYhn : ‖Yh‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun f => ?_
    calc ‖Yh f‖ = ‖run U ((encFreq t).symm f)‖ := rfl
      _ ≤ ‖run U‖ := norm_le_pi_norm _ _
      _ ≤ ‖dftTensor t U‖ + ‖run U - dftTensor t U‖ := norm_le_insert' _ _
      _ ≤ ‖U‖ + Emid * v := add_le_add (norm_dftTensor_le t U) hErrMid
      _ ≤ 1 / 8 + 16 * (2 : ℝ) ^ k * ((P : ℝ) + 1) * v := add_le_add hUn hEm
      _ ≤ 1 := by linarith
  -- deconvolution chain
  have hsumle : (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) ≤
      d * (2 : ℝ) ^ k := by
    calc (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ))
        ≤ ∑ i : Fin d, (t i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ _i : Fin d, (2 : ℝ) ^ k := Finset.sum_le_sum fun i _ => by
          rw [← hRr]; exact_mod_cast le_totalLen t ht1 i
      _ = d * (2 : ℝ) ^ k := by simp
  have hvdR : v * (d * (2 : ℝ) ^ k) ≤ Mb := by
    calc v * (d * (2 : ℝ) ^ k) = (d * (2 : ℝ) ^ k) * v := by ring
      _ ≤ (d * (((P : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 3)) * v := by
          apply mul_le_mul_of_nonneg_right _ hv.le
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact le_trans hR3 (le_mul_of_one_le_left (by positivity) (by linarith))
      _ = Mb := by rw [hMbdef]; ring
  have hsum : 64 * v * (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hsumle (by positivity : (0 : ℝ) ≤ 64 * v)
    linarith
  have hdc' := hdc rr hrr P (schedOmega p k d) α hC t hs T hT hsum Yh
  rw [max_eq_left hYhn, mul_one] at hdc'
  -- `(B_2⋯B_d)^{-1}` amplifies by at most `R/t_1 ≤ R` (Lemma 4.6 (bridge Lemma C)(vi))
  have hvi := hCvi (schedOmega p k d) hC.2.1 α (alphaDefault_admissible' _) t hs hd1
  have hBinv : ‖(truncProd α t)⁻¹ *ᵥ (Yh - Y)‖ ≤ (2 : ℝ) ^ k * ‖Yh - Y‖ := by
    have h1 := norm_apply_le_opNormInf (Matrix.toLin' (truncProd α t)⁻¹) (Yh - Y)
    rw [Matrix.toLin'_apply] at h1
    have ht0 : (1 : ℝ) ≤ (t ⟨0, hd1⟩ : ℝ) := by exact_mod_cast ht1 _
    have h2 : (totalLen t : ℝ) / (t ⟨0, hd1⟩ : ℝ) ≤ (2 : ℝ) ^ k := by
      rw [hRr]; exact div_le_self (by positivity) ht0
    exact h1.trans (mul_le_mul_of_nonneg_right (hvi.trans h2) (norm_nonneg _))
  have hN : ‖deconvFixedR rr (P + 2) t T Yh - (truncProd α t)⁻¹ *ᵥ Y‖ ≤
      64 * (dimD t : ℝ) * v * (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) +
        (2 : ℝ) ^ k * (Emid * v + ‖U - spreadAll α t V‖) := by
    have hsplit : deconvFixedR rr (P + 2) t T Yh - (truncProd α t)⁻¹ *ᵥ Y =
        (deconvFixedR rr (P + 2) t T Yh - (truncProd α t)⁻¹ *ᵥ Yh) +
          (truncProd α t)⁻¹ *ᵥ (Yh - Y) := by
      rw [Matrix.mulVec_sub]; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add hdc' (hBinv.trans ?_))
    exact mul_le_mul_of_nonneg_left hEY (by positivity)
  -- normalized error `≤ 84 d (P+1) R² v`
  have hNb : 64 * (dimD t : ℝ) * v *
        (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) +
        (2 : ℝ) ^ k * (Emid * v + ‖U - spreadAll α t V‖) ≤
      84 * ((d : ℝ) * ((P : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 2 * v) := by
    have hsum0 : 0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) :=
      Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have e1 : 64 * (dimD t : ℝ) * v *
        (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) ≤
        64 * (2 : ℝ) ^ k * v * (d * (2 : ℝ) ^ k) := by
      have h1 : 64 * (dimD t : ℝ) * v ≤ 64 * (2 : ℝ) ^ k * v := by
        have := mul_le_mul_of_nonneg_right hDR hv.le
        linarith
      calc _ ≤ 64 * (2 : ℝ) ^ k * v *
            (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 hsum0
        _ ≤ 64 * (2 : ℝ) ^ k * v * (d * (2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left hsumle (by positivity)
    have e2 : Emid * v + ‖U - spreadAll α t V‖ ≤
        16 * (2 : ℝ) ^ k * ((P : ℝ) + 1) * v + 4 * ((P : ℝ) + 1) * v * d * (2 : ℝ) ^ k := by
      have h' : 4 * ((P : ℝ) + 1) * v * d * Real.sqrt (dimD t) ≤
          4 * ((P : ℝ) + 1) * v * d * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hsD (by positivity)
      linarith
    have e3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
    have hW : 0 ≤ ((2 : ℝ) ^ k) ^ 2 * v := by positivity
    have e4 := mul_le_mul_of_nonneg_right (poly_aux hdR hP0) hW
    linarith
  have hS := two_pow_preScaleExp_le t ht1 x
  have hX0 : (0 : ℝ) ≤ max 1 ‖x‖ := le_trans zero_le_one (le_max_left _ _)
  calc (2 : ℝ) ^ preScaleExp t x * ‖deconvFixedR rr (P + 2) t T Yh - (truncProd α t)⁻¹ *ᵥ Y‖
      ≤ (128 * (2 : ℝ) ^ k * max 1 ‖x‖) *
          (84 * ((d : ℝ) * ((P : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 2 * v)) := by
        refine mul_le_mul ?_ (hN.trans hNb) (norm_nonneg _) (by positivity)
        refine hS.trans ?_
        have := mul_le_mul_of_nonneg_right hDR hX0
        linarith
    _ = 10752 * Mb * max 1 ‖x‖ := by rw [hMbdef]; ring
    _ ≤ (2 : ℝ) ^ 14 * Mb * max 1 ‖x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hMb0) hX0
    _ ≤ (2 : ℝ) ^ (-((p : ℤ) + 12)) * max 1 ‖x‖ := mul_le_mul_of_nonneg_right hMb hX0

end SubNLogN.Math.Bridge
