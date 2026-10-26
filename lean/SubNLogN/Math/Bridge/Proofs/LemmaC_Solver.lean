import SubNLogN.Math.Bridge.LemmaC_Solver
import SubNLogN.Math.Bridge.LemmaB_Ops

/-!
# Proof of Lemma 4.6 (bridge Lemma C)(iv): the two-pass cyclic solver (`lem:bridge-C`)

Main result: `lemmaC_iv_of`, which proves `LemmaC_ivStmt` from the contracts `LemmaB_ivStmt`
(separation), `LemmaB_vStmt` (invertibility of `B` and `‖B⁻¹‖_∞ ≤ 4t/7`), `KernelG_negStmt` and
`KernelG_strictAntiOnStmt` (orientation `c_0 > c_1 ⟺ 2u < t`). The facts `0 ≤ G ≤ 1` are proved
here directly from the definition of `kernelG` (Gaussian integral). (Names `LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemma C), kept for stability.)

Proof plan (forward case `c_0 > c_1`; the backward case is the same recurrence after the
reorientation `z_i = Z_{-i mod L}`, `y'_i = Y_{1-i mod L}`):
* `Z = B⁻¹Y` (Mathlib inverse) satisfies the cyclic recurrence `Z_n + a' Z_{n-1} = c_max⁻¹ Y_n`,
  `a' = c_min/c_max`, and `‖Z‖_∞ ≤ (4t/7)‖Y‖_∞ ≤ t‖Y‖_∞` (Lemma 4.4 (bridge Lemma B)(v)).
* Against the stored recurrence `Z_n = b_n - â Z_{n-1} + r_n` (`b_n = Quant(μ̂ Y_n)`) the residual is
  `|r_n| ≤ σ := v‖Y‖ + v + v·t‖Y‖` (`|μ̂ - c_max⁻¹| ≤ v`, `|â - a'| ≤ v`, one rounding).
* Deviation lemma `sweepPrefix_dev`: a pass of the recurrence started from `zinit` satisfies
  `z_n - Z_n = (-â)^{n+1}(zinit - Z_{L-1}) + E_n` with `|E_n| ≤ (v + σ) Σ_{k ≤ n} â^k`.
* First pass (`zinit = 0`, `L` even): `z_{L-1} = (1 - â^L) Z_{L-1} + E`, so the closure
  `Quant(γ̂ z_{L-1})` is within `C := v·t‖Y‖ + (v+σ)(1+v)/(1-â) + v` of `Z_{L-1}`; this uses the
  cancellation `(1-â^L)⁻¹ Σ_{k<L} â^k = 1/(1-â)`, uniformly in `L`.
* Second pass: within `C + (v+σ)/(1-â)` of `Z`. Numerics: `1/(1-â) ≤ 2t`, `t v ≤ 1/64`, giving
  `≤ 32 t² v max(1,‖Y‖)` and state bounds `< 7t max(1,‖Y‖)`.
(The paper compares with `Z̃ = μ̂(I+âT)⁻¹Y`; we compare directly with `Z = B⁻¹Y`, which gives the
same kind of bound with room to spare.)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace LemmaCivProof

/-! ## Rounding and geometric-sum helpers -/

/-- Crude rounding bound `‖Quant_q(z) - z‖ ≤ 2^{-q}` (from `√2/2 ≤ 1`). -/
theorem norm_crnd_sub_le_gridUnit {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (z : ℂ) : ‖crnd rr q z - z‖ ≤ gridUnit q := by
  have h := norm_crnd_sub_le hrr q z
  have h2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hg := gridUnit_pos q
  calc ‖crnd rr q z - z‖ ≤ Real.sqrt 2 / 2 * gridUnit q := h
    _ ≤ 1 * gridUnit q := by gcongr; linarith
    _ = gridUnit q := one_mul _

/-- `Σ_{k<n} a^k ≤ 1/(1-a)` for `0 ≤ a < 1`. -/
theorem geom_sum_le_inv (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, a ^ k ≤ 1 / (1 - a) := by
  have hD : 0 < 1 - a := by linarith
  have h := mul_neg_geom_sum a n
  have hp : 0 ≤ a ^ n := pow_nonneg ha0 n
  rw [le_div_iff₀ hD]
  linarith [mul_comm (1 - a) (∑ k ∈ Finset.range n, a ^ k)]

/-- `Σ_{k<n+1} a^k = a·Σ_{k<n} a^k + 1` (the step of the geometric sum used in the induction). -/
theorem geom_sum_succ' (a : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), a ^ k = a * ∑ k ∈ Finset.range n, a ^ k + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## The deviation lemma for one pass of the recurrence -/

/-- One pass of the stored recurrence `z ← b_n + Quant(-â z)`, started from `zinit`, compared with
a sequence `Z` that satisfies the same recurrence up to residuals `≤ σ`, started from `Zinit`:
`z_n - Z_n = (-â)^{n+1} (zinit - Zinit) + E_n` with `‖E_n‖ ≤ (v + σ) Σ_{k ≤ n} â^k`. -/
theorem sweepPrefix_dev {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (b : ℕ → ℂ) (zinit Zinit : ℂ)
    (Z : ℕ → ℂ) (σ : ℝ) (N : ℕ)
    (h0 : ‖Z 0 - (b 0 - (a : ℂ) * Zinit)‖ ≤ σ)
    (hs : ∀ n, n + 1 < N → ‖Z (n + 1) - (b (n + 1) - (a : ℂ) * Z n)‖ ≤ σ) :
    ∀ n, n < N → ∃ E : ℂ,
      sweepPrefixR rr q a b zinit n - Z n = (-(a : ℂ)) ^ (n + 1) * (zinit - Zinit) + E ∧
      ‖E‖ ≤ (gridUnit q + σ) * ∑ k ∈ Finset.range (n + 1), a ^ k := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨(crnd rr q (-(a : ℂ) * zinit) - (-(a : ℂ) * zinit)) -
      (Z 0 - (b 0 - (a : ℂ) * Zinit)), ?_, ?_⟩
    · simp only [sweepPrefixR]; ring
    · simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
      calc _ ≤ ‖crnd rr q (-(a : ℂ) * zinit) - (-(a : ℂ) * zinit)‖ +
            ‖Z 0 - (b 0 - (a : ℂ) * Zinit)‖ := norm_sub_le _ _
        _ ≤ gridUnit q + σ := add_le_add (norm_crnd_sub_le_gridUnit hrr q _) h0
  | succ m ih =>
    intro hm
    obtain ⟨E, hE, hEn⟩ := ih (by omega)
    set S := sweepPrefixR rr q a b zinit m with hS
    refine ⟨-(a : ℂ) * E + (crnd rr q (-(a : ℂ) * S) - (-(a : ℂ) * S)) -
      (Z (m + 1) - (b (m + 1) - (a : ℂ) * Z m)), ?_, ?_⟩
    · show b (m + 1) + crnd rr q (-(a : ℂ) * S) - Z (m + 1) = _
      linear_combination (-(a : ℂ)) * hE
    · have hσ0 : 0 ≤ σ := (norm_nonneg _).trans h0
      have hr := hs m hm
      have hq := norm_crnd_sub_le_gridUnit hrr q (-(a : ℂ) * S)
      have haE : ‖-(a : ℂ) * E‖ = a * ‖E‖ := by
        rw [norm_mul, norm_neg, Complex.norm_of_nonneg ha0]
      rw [geom_sum_succ' a (m + 1)]
      calc _ ≤ ‖-(a : ℂ) * E + (crnd rr q (-(a : ℂ) * S) - (-(a : ℂ) * S))‖ +
            ‖Z (m + 1) - (b (m + 1) - (a : ℂ) * Z m)‖ := norm_sub_le _ _
        _ ≤ (‖-(a : ℂ) * E‖ + ‖crnd rr q (-(a : ℂ) * S) - (-(a : ℂ) * S)‖) + σ :=
            add_le_add (norm_add_le _ _) hr
        _ ≤ (a * ((gridUnit q + σ) * ∑ k ∈ Finset.range (m + 1), a ^ k) + gridUnit q) + σ := by
            rw [haE]; gcongr
        _ = (gridUnit q + σ) * (a * ∑ k ∈ Finset.range (m + 1), a ^ k + 1) := by ring

/-! ## Numerics -/

/-- The final arithmetic: with `σ = vK + v + v t K`, `X = 1/(1-â) ≤ 2t`, `v t ≤ 1/64`, `t ≥ 2`:
`v t K + (v+σ)(1+v)X + v + (v+σ)X ≤ 32 t² v max(1,K)` (in fact `≤ (6t² + 19t + 1) v max(1,K)`). -/
theorem numeric_total (t v K X : ℝ) (ht : 2 ≤ t) (hv0 : 0 ≤ v) (hvt : v * t ≤ 1 / 64)
    (hK : 0 ≤ K) (hX0 : 0 ≤ X) (hX : X ≤ 2 * t) :
    v * (t * K) + (v + (v * K + v + v * (t * K))) * ((1 + v) * X) + v +
      (v + (v * K + v + v * (t * K))) * X ≤ 32 * t ^ 2 * v * max 1 K := by
  have hM1 : 1 ≤ max 1 K := le_max_left _ _
  have hMK : K ≤ max 1 K := le_max_right _ _
  set M := max 1 K with hM
  have ht0 : 0 ≤ t := by linarith
  have hv1 : v ≤ 1 := by nlinarith [mul_nonneg hv0 (sub_nonneg.mpr ht)]
  have hM0 : 0 ≤ M := by linarith
  have hs : v + (v * K + v + v * (t * K)) ≤ v * M * (3 + t) := by
    have e1 : v * K ≤ v * M := mul_le_mul_of_nonneg_left hMK hv0
    have e2 : v * (t * K) ≤ v * (t * M) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hMK ht0) hv0
    have e3 : v ≤ v * M := le_mul_of_one_le_right hv0 hM1
    nlinarith
  have hs0 : 0 ≤ v + (v * K + v + v * (t * K)) := by positivity
  have hvM : 0 ≤ v * M * (3 + t) := by positivity
  have t1 : v * (t * K) ≤ v * (t * M) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMK ht0) hv0
  have t2 : (v + (v * K + v + v * (t * K))) * ((1 + v) * X) ≤ (v * M * (3 + t)) * (2 * (2 * t)) :=
    mul_le_mul hs (mul_le_mul (by linarith) hX hX0 (by norm_num)) (by positivity) hvM
  have t3 : v ≤ v * M := le_mul_of_one_le_right hv0 hM1
  have t4 : (v + (v * K + v + v * (t * K))) * X ≤ (v * M * (3 + t)) * (2 * t) :=
    mul_le_mul hs hX hX0 hvM
  have hpoly : 6 * t ^ 2 + 19 * t + 1 ≤ 32 * t ^ 2 := by nlinarith
  have hvM0 : 0 ≤ v * M := by positivity
  calc v * (t * K) + (v + (v * K + v + v * (t * K))) * ((1 + v) * X) + v +
        (v + (v * K + v + v * (t * K))) * X
      ≤ v * (t * M) + (v * M * (3 + t)) * (2 * (2 * t)) + v * M + (v * M * (3 + t)) * (2 * t) := by
        linarith
    _ = v * M * (6 * t ^ 2 + 19 * t + 1) := by ring
    _ ≤ v * M * (32 * t ^ 2) := mul_le_mul_of_nonneg_left hpoly hvM0
    _ = 32 * t ^ 2 * v * M := by ring

/-! ## The forward solver -/

/-- Unfolding of `cycSweepFwd`. -/
theorem cycSweepFwd_eq (rr : ℕ → ℝ → ℝ) (q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (y : ℕ → ℂ) (n : ℕ) :
    cycSweepFwdR rr q mu ahat gam L y n =
      if n = L - 1 then
        crnd rr q ((gam : ℂ) * sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * y j)) 0 (L - 1))
      else sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * y j))
        (crnd rr q ((gam : ℂ) * sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * y j)) 0 (L - 1)))
        n :=
  rfl

/-- Core estimate for the forward sweep: if `Z` solves the cyclic recurrence
`Z_n + a' Z_{n-1} = c⁻¹ y_n` (`Z_{-1} = Z_{L-1}`) with `‖Z_n‖ ≤ tK`, and the stored parameters
satisfy the hypotheses of Lemma 4.6 (bridge Lemma C)(iv), then the computed sweep is within `32 t² v max(1,K)` of `Z`
and all states are `< 7t max(1,K)`. -/
theorem fwd_core {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ) (t : ℝ) (ht : 2 ≤ t) (hv : gridUnit q ≤ 1 / (64 * t))
    (L : ℕ) (hLe : Even L) (hL0 : 0 < L) (mu ahat gam a' cinv : ℝ)
    (hmu : |mu - cinv| ≤ gridUnit q) (ha0 : 0 ≤ ahat) (ha1 : ahat ≤ 1 - 1 / (2 * t))
    (ha' : |ahat - a'| ≤ gridUnit q) (hgam : |gam - (1 - ahat ^ L)⁻¹| ≤ gridUnit q)
    (y : ℕ → ℂ) (K : ℝ) (hy : ∀ n, ‖y n‖ ≤ K) (Z : ℕ → ℂ)
    (hZ0 : Z 0 + (a' : ℂ) * Z (L - 1) = (cinv : ℂ) * y 0)
    (hZs : ∀ n, n + 1 < L → Z (n + 1) + (a' : ℂ) * Z n = (cinv : ℂ) * y (n + 1))
    (hZb : ∀ n, n < L → ‖Z n‖ ≤ t * K) :
    (∀ n, n < L → ‖cycSweepFwdR rr q mu ahat gam L y n - Z n‖ ≤
        32 * t ^ 2 * gridUnit q * max 1 K) ∧
    (∀ n, n < L → ‖sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * y j)) 0 n‖ <
        7 * t * max 1 K) ∧
    (∀ n, n < L → ‖cycSweepFwdR rr q mu ahat gam L y n‖ < 7 * t * max 1 K) := by
  have hvpos : 0 < gridUnit q := gridUnit_pos q
  have htpos : 0 < t := by linarith
  have hK : 0 ≤ K := (norm_nonneg _).trans (hy 0)
  have hvt : gridUnit q * t ≤ 1 / 64 := by
    have h1 := mul_le_mul_of_nonneg_right hv htpos.le
    have h2 : 1 / (64 * t) * t = 1 / 64 := by field_simp
    linarith
  have hht : 0 < 1 / (2 * t) := by positivity
  have ha1' : ahat < 1 := by linarith
  have hDpos : 0 < 1 - ahat := by linarith
  have hX : 1 / (1 - ahat) ≤ 2 * t := by
    rw [div_le_iff₀ hDpos]
    have h1 : 1 / (2 * t) * (2 * t) = 1 := by field_simp
    have h2 : 1 / (2 * t) * (2 * t) ≤ (1 - ahat) * (2 * t) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hX0 : 0 ≤ 1 / (1 - ahat) := by positivity
  set v := gridUnit q with hvdef
  set X := 1 / (1 - ahat) with hXdef
  set b : ℕ → ℂ := fun j => crnd rr q ((mu : ℂ) * y j) with hb
  set σ := v * K + v + v * (t * K) with hσ
  have hσ0 : 0 ≤ σ := by positivity
  -- residual of the exact solution against the stored recurrence
  have hres : ∀ n, ∀ Zp : ℂ, Z n + (a' : ℂ) * Zp = (cinv : ℂ) * y n → ‖Zp‖ ≤ t * K →
      ‖Z n - (b n - (ahat : ℂ) * Zp)‖ ≤ σ := by
    intro n Zp hZp hZpb
    have e : Z n - (b n - (ahat : ℂ) * Zp) =
        ((cinv - mu : ℝ) : ℂ) * y n + ((mu : ℂ) * y n - b n) + ((ahat - a' : ℝ) : ℂ) * Zp := by
      push_cast
      linear_combination hZp
    rw [e]
    have h1 : ‖((cinv - mu : ℝ) : ℂ) * y n‖ ≤ v * K := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul hmu (hy n) (norm_nonneg _) hvpos.le
    have h2 : ‖(mu : ℂ) * y n - b n‖ ≤ v := by
      rw [norm_sub_rev]; exact norm_crnd_sub_le_gridUnit hrr q _
    have h3 : ‖((ahat - a' : ℝ) : ℂ) * Zp‖ ≤ v * (t * K) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ha' hZpb (norm_nonneg _) hvpos.le
    calc _ ≤ ‖((cinv - mu : ℝ) : ℂ) * y n + ((mu : ℂ) * y n - b n)‖ +
          ‖((ahat - a' : ℝ) : ℂ) * Zp‖ := norm_add_le _ _
      _ ≤ (‖((cinv - mu : ℝ) : ℂ) * y n‖ + ‖(mu : ℂ) * y n - b n‖) +
          ‖((ahat - a' : ℝ) : ℂ) * Zp‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (v * K + v) + v * (t * K) := by gcongr
      _ = σ := by rw [hσ]
  have hL1 : L - 1 < L := by omega
  have h0 : ‖Z 0 - (b 0 - (ahat : ℂ) * Z (L - 1))‖ ≤ σ := hres 0 _ hZ0 (hZb _ hL1)
  have hs : ∀ n, n + 1 < L → ‖Z (n + 1) - (b (n + 1) - (ahat : ℂ) * Z n)‖ ≤ σ :=
    fun n hn => hres (n + 1) _ (hZs n hn) (hZb n (by omega))
  have hgeom : ∀ n, ∑ k ∈ Finset.range n, ahat ^ k ≤ X := geom_sum_le_inv ahat ha0 ha1'
  -- one pass from an arbitrary start
  have hpass : ∀ zinit : ℂ, ∀ n, n < L → ‖sweepPrefixR rr q ahat b zinit n - Z n‖ ≤
      ‖zinit - Z (L - 1)‖ + (v + σ) * X := by
    intro zinit n hn
    obtain ⟨E, hE, hEn⟩ := sweepPrefix_dev hrr q ahat ha0 b zinit (Z (L - 1)) Z σ L h0 hs n hn
    rw [hE]
    have hpow : ‖(-(ahat : ℂ)) ^ (n + 1)‖ ≤ 1 := by
      rw [norm_pow, norm_neg, Complex.norm_of_nonneg ha0]
      exact pow_le_one₀ ha0 ha1'.le
    have hE' : ‖E‖ ≤ (v + σ) * X :=
      hEn.trans (mul_le_mul_of_nonneg_left (hgeom _) (by positivity))
    have hm : ‖(-(ahat : ℂ)) ^ (n + 1) * (zinit - Z (L - 1))‖ ≤ ‖zinit - Z (L - 1)‖ := by
      rw [norm_mul]
      calc _ ≤ 1 * ‖zinit - Z (L - 1)‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ = _ := one_mul _
    calc _ ≤ ‖(-(ahat : ℂ)) ^ (n + 1) * (zinit - Z (L - 1))‖ + ‖E‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hm hE'
  -- the closure value
  set s := sweepPrefixR rr q ahat b 0 (L - 1) with hsdef
  set zLast := crnd rr q ((gam : ℂ) * s) with hzLast
  have hclose : ‖zLast - Z (L - 1)‖ ≤ v * (t * K) + (v + σ) * ((1 + v) * X) + v := by
    obtain ⟨E, hE, hEn⟩ := sweepPrefix_dev hrr q ahat ha0 b 0 (Z (L - 1)) Z σ L h0 hs (L - 1) hL1
    have hLL : L - 1 + 1 = L := by omega
    rw [hLL, Even.neg_pow hLe] at hE
    rw [hLL] at hEn
    have hs' : s = (1 - (ahat : ℂ) ^ L) * Z (L - 1) + E := by
      rw [hsdef]; linear_combination hE
    have hpL : ahat ^ L < 1 := pow_lt_one₀ ha0 ha1' (by omega)
    have hpL0 : 0 ≤ ahat ^ L := pow_nonneg ha0 L
    have hDL : 0 < 1 - ahat ^ L := by linarith
    have hSL : (1 - ahat) * ∑ k ∈ Finset.range L, ahat ^ k = 1 - ahat ^ L :=
      mul_neg_geom_sum ahat L
    have hg1 : |gam * (1 - ahat ^ L) - 1| ≤ v := by
      have e1 : gam * (1 - ahat ^ L) - 1 = (gam - (1 - ahat ^ L)⁻¹) * (1 - ahat ^ L) := by
        field_simp
      rw [e1, abs_mul, abs_of_pos hDL]
      calc _ ≤ v * (1 - ahat ^ L) := mul_le_mul_of_nonneg_right hgam hDL.le
        _ ≤ v * 1 := by gcongr; linarith
        _ = v := mul_one v
    have hS0 : 0 ≤ ∑ k ∈ Finset.range L, ahat ^ k :=
      Finset.sum_nonneg (fun k _ => pow_nonneg ha0 k)
    have hgS : |gam| * ∑ k ∈ Finset.range L, ahat ^ k ≤ (1 + v) * X := by
      have hgabs : |gam| ≤ (1 - ahat ^ L)⁻¹ + v := by
        have h1 := abs_sub_abs_le_abs_sub gam (1 - ahat ^ L)⁻¹
        rw [abs_of_pos (inv_pos.mpr hDL)] at h1
        linarith
      have hSeq : (1 - ahat ^ L)⁻¹ * ∑ k ∈ Finset.range L, ahat ^ k = X := by
        have hSeq' : ∑ k ∈ Finset.range L, ahat ^ k = (1 - ahat ^ L) / (1 - ahat) := by
          rw [eq_div_iff hDpos.ne', mul_comm]; exact hSL
        rw [hSeq', hXdef, ← mul_div_assoc, inv_mul_cancel₀ hDL.ne']
      calc |gam| * ∑ k ∈ Finset.range L, ahat ^ k
          ≤ ((1 - ahat ^ L)⁻¹ + v) * ∑ k ∈ Finset.range L, ahat ^ k :=
            mul_le_mul_of_nonneg_right hgabs hS0
        _ = X + v * ∑ k ∈ Finset.range L, ahat ^ k := by rw [add_mul, hSeq]
        _ ≤ X + v * X := by gcongr; exact hgeom L
        _ = (1 + v) * X := by ring
    have e : zLast - Z (L - 1) = ((gam * (1 - ahat ^ L) - 1 : ℝ) : ℂ) * Z (L - 1) +
        (gam : ℂ) * E + (zLast - (gam : ℂ) * s) := by
      push_cast
      linear_combination (gam : ℂ) * hs'
    rw [e]
    have k1 : ‖((gam * (1 - ahat ^ L) - 1 : ℝ) : ℂ) * Z (L - 1)‖ ≤ v * (t * K) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hg1 (hZb _ hL1) (norm_nonneg _) hvpos.le
    have k2 : ‖(gam : ℂ) * E‖ ≤ (v + σ) * ((1 + v) * X) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |gam| * ‖E‖ ≤ |gam| * ((v + σ) * ∑ k ∈ Finset.range L, ahat ^ k) :=
            mul_le_mul_of_nonneg_left hEn (abs_nonneg _)
        _ = (v + σ) * (|gam| * ∑ k ∈ Finset.range L, ahat ^ k) := by ring
        _ ≤ (v + σ) * ((1 + v) * X) := mul_le_mul_of_nonneg_left hgS (by positivity)
    have k3 : ‖zLast - (gam : ℂ) * s‖ ≤ v := norm_crnd_sub_le_gridUnit hrr q _
    calc _ ≤ ‖((gam * (1 - ahat ^ L) - 1 : ℝ) : ℂ) * Z (L - 1) + (gam : ℂ) * E‖ +
          ‖zLast - (gam : ℂ) * s‖ := norm_add_le _ _
      _ ≤ (‖((gam * (1 - ahat ^ L) - 1 : ℝ) : ℂ) * Z (L - 1)‖ + ‖(gam : ℂ) * E‖) +
          ‖zLast - (gam : ℂ) * s‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (v * (t * K) + (v + σ) * ((1 + v) * X)) + v := by gcongr
  -- totals
  have hTot := numeric_total t v K X ht hvpos.le hvt hK hX0 hX
  have hM1 : 1 ≤ max 1 K := le_max_left _ _
  have hMK : K ≤ max 1 K := le_max_right _ _
  have hvσX : 0 ≤ (v + σ) * X := by positivity
  have hsmall : 32 * t ^ 2 * v * max 1 K ≤ t * max 1 K / 2 := by
    have h1 : 32 * t ^ 2 * v * max 1 K = 32 * (v * t) * (t * max 1 K) := by ring
    have h2 : 0 ≤ t * max 1 K := by positivity
    rw [h1]
    nlinarith
  have htM : 0 < t * max 1 K := by positivity
  have hcyc : ∀ n, cycSweepFwdR rr q mu ahat gam L y n =
      if n = L - 1 then zLast else sweepPrefixR rr q ahat b zLast n := fun n => rfl
  have herr : ∀ n, n < L → ‖cycSweepFwdR rr q mu ahat gam L y n - Z n‖ ≤
      32 * t ^ 2 * v * max 1 K := by
    intro n hn
    rw [hcyc]
    split_ifs with hnL
    · rw [hnL]
      have := hclose
      linarith
    · have h1 := hpass zLast n hn
      linarith
  refine ⟨herr, ?_, ?_⟩
  · intro n hn
    have h1 := hpass 0 n hn
    have h2 : ‖(0 : ℂ) - Z (L - 1)‖ ≤ t * K := by rw [zero_sub, norm_neg]; exact hZb _ hL1
    have h3 := hZb n hn
    have h4 : ‖sweepPrefixR rr q ahat b 0 n‖ ≤ ‖Z n‖ + ‖sweepPrefixR rr q ahat b 0 n - Z n‖ := by
      have := norm_add_le (Z n) (sweepPrefixR rr q ahat b 0 n - Z n)
      rwa [add_sub_cancel] at this
    have h5 : t * K ≤ t * max 1 K := mul_le_mul_of_nonneg_left hMK htpos.le
    show ‖sweepPrefixR rr q ahat b 0 n‖ < 7 * t * max 1 K
    nlinarith
  · intro n hn
    have h1 := herr n hn
    have h3 := hZb n hn
    have h4 : ‖cycSweepFwdR rr q mu ahat gam L y n‖ ≤ ‖Z n‖ +
        ‖cycSweepFwdR rr q mu ahat gam L y n - Z n‖ := by
      have := norm_add_le (Z n) (cycSweepFwdR rr q mu ahat gam L y n - Z n)
      rwa [add_sub_cancel] at this
    have h5 : t * K ≤ t * max 1 K := mul_le_mul_of_nonneg_left hMK htpos.le
    nlinarith

/-! ## Facts about the kernel `G` -/

/-- `LemmaCParams` gives `ω ≥ 8`, `α > 0` and eq. (`eq:alpha`) (`AlphaAdmissible`), since
`α = 2√λ_G·√(ω ln2/π)` with `√λ_G ∈ [1,2]`. -/
theorem alphaAdmissible_of_params {P ω : ℕ} {α : ℝ} (hC : LemmaCParams P ω α) :
    8 ≤ ω ∧ AlphaAdmissible ω α ∧ 0 < α := by
  obtain ⟨_, hω, _, hα, lamG, hl1, hl4, hsq⟩ := hC
  refine ⟨hω, ?_, hα⟩
  have hx0 : 0 ≤ (ω : ℝ) * Real.log 2 / Real.pi := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have := Real.pi_pos
    positivity
  set x := (ω : ℝ) * Real.log 2 / Real.pi with hx
  have hsq' : α ^ 2 = 4 * (lamG : ℝ) * x := by rw [hsq, hx]; ring
  have hl1' : (1 : ℝ) ≤ lamG := by exact_mod_cast hl1
  have hl4' : (lamG : ℝ) ≤ 4 := by exact_mod_cast hl4
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  constructor
  · by_contra h
    have h2 : α ^ 2 < (2 * Real.sqrt x) ^ 2 := pow_lt_pow_left₀ (not_le.mp h) hα.le two_ne_zero
    nlinarith
  · by_contra h
    have h2 : (4 * Real.sqrt x) ^ 2 < α ^ 2 :=
      pow_lt_pow_left₀ (not_le.mp h) (by positivity) two_ne_zero
    nlinarith

/-- `G ≥ 0` (integral of a positive function over `[ξ-½, ξ+½]`). -/
theorem kernelG_nonneg {α : ℝ} (hα : 0 ≤ α) (ξ : ℝ) : 0 ≤ kernelG α ξ := by
  unfold kernelG
  apply intervalIntegral.integral_nonneg (by linarith)
  intro u _
  positivity

/-- `G ≤ 1`: the Gaussian density `α e^{-πα²v²}` has total integral `1`. -/
theorem kernelG_le_one {α : ℝ} (hα : 0 < α) (ξ : ℝ) : kernelG α ξ ≤ 1 := by
  unfold kernelG
  have hb : 0 < Real.pi * α ^ 2 := by have := Real.pi_pos; positivity
  have hfun : (fun v : ℝ => α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2))) =
      fun v => α * Real.exp (-(Real.pi * α ^ 2) * v ^ 2) := by
    funext v; rw [neg_mul]
  have hint : MeasureTheory.Integrable
      (fun v : ℝ => α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2))) := by
    rw [hfun]; exact (integrable_exp_neg_mul_sq hb).const_mul α
  have htot : ∫ v : ℝ, α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2)) = 1 := by
    rw [hfun, MeasureTheory.integral_const_mul, integral_gaussian]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    rw [show Real.pi / (Real.pi * α ^ 2) = (1 / α) ^ 2 by field_simp]
    rw [Real.sqrt_sq (by positivity)]
    field_simp
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc _ ≤ ∫ v : ℝ, α * Real.exp (-(Real.pi * α ^ 2 * v ^ 2)) :=
        MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall (fun v => by simp only [Pi.zero_apply]; positivity))
    _ = 1 := htot

/-- Orientation: for `t ≥ 2` a power of two and `y = (u+½)/t`, `c_1 < c_0` iff `2u < t`
(uses that `G` is even and strictly decreasing on `[0,∞)`, and that `t` is even). -/
theorem orient {α : ℝ} (hα : 0 < α) (hneg : KernelG_negStmt) (hanti : KernelG_strictAntiOnStmt)
    (t : ℕ) (ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (u : ℕ) (hu : u < t) :
    (2 * u < t → kernelG α ((u + 1 / 2) / t - 1) < kernelG α ((u + 1 / 2) / t)) ∧
    (¬ 2 * u < t → kernelG α ((u + 1 / 2) / t) < kernelG α ((u + 1 / 2) / t - 1)) := by
  obtain ⟨ht2, a, ha⟩ := ht
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha; omega
  have heven : 2 ∣ t := by rw [ha]; exact dvd_pow_self 2 ha0
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  set y : ℝ := ((u : ℝ) + 1 / 2) / (t : ℝ) with hy
  have hc1 : kernelG α (y - 1) = kernelG α (1 - y) := by
    rw [show y - 1 = -(1 - y) by ring]; exact hneg α (1 - y)
  have hy0 : 0 ≤ y := by positivity
  have hy2 : 2 * y = (2 * (u : ℝ) + 1) / (t : ℝ) := by rw [hy]; ring
  have hy1 : 0 < 1 - y := by
    have h1 : (u : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hu
    have h2 : (2 * (u : ℝ) + 1) / (t : ℝ) < 2 := by
      rw [div_lt_iff₀ htpos]; linarith
    linarith
  constructor
  · intro h2
    have h3 : 2 * u + 1 < t := by omega
    have h3' : 2 * (u : ℝ) + 1 < (t : ℝ) := by exact_mod_cast h3
    have h4 : (2 * (u : ℝ) + 1) / (t : ℝ) < 1 := (div_lt_one htpos).mpr h3'
    have hlt : y < 1 - y := by linarith
    rw [hc1]
    exact hanti α hα (Set.mem_Ici.mpr hy0) (Set.mem_Ici.mpr hy1.le) hlt
  · intro h2
    have h3 : t < 2 * u + 1 := by omega
    have h3' : (t : ℝ) < 2 * (u : ℝ) + 1 := by exact_mod_cast h3
    have h4 : 1 < (2 * (u : ℝ) + 1) / (t : ℝ) := (one_lt_div htpos).mpr h3'
    have hlt : 1 - y < y := by linarith
    rw [hc1]
    exact hanti α hα (Set.mem_Ici.mpr hy1.le) (Set.mem_Ici.mpr hy0) hlt

/-! ## The cyclic bidiagonal matrix and index bookkeeping -/

theorem cycBidiag_mulVec_apply (c0 c1 : ℂ) (L : ℕ) (Z : Fin L → ℂ) (j : Fin L) :
    Matrix.mulVec (cycBidiag c0 c1 L) Z j = c0 * Z j + c1 * Z (shiftFin j (-1)) := by
  simp only [Matrix.mulVec, dotProduct, cycBidiag, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `Z = B⁻¹Y` solves `c_0 Z_j + c_1 Z_{j-1} = Y_j`. -/
theorem inv_mulVec_eq (c0 c1 : ℂ) (L : ℕ) (hdet : IsUnit (cycBidiag c0 c1 L).det)
    (Y : Fin L → ℂ) (j : Fin L) :
    c0 * Matrix.mulVec (cycBidiag c0 c1 L)⁻¹ Y j +
      c1 * Matrix.mulVec (cycBidiag c0 c1 L)⁻¹ Y (shiftFin j (-1)) = Y j := by
  rw [← cycBidiag_mulVec_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]

theorem toNat_emod_of_eq {L : ℕ} (r : ℕ) (hr : r < L) (m k : ℤ) (h : m = r + k * L) :
    (m % (L : ℤ)).toNat = r := by
  subst h
  rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)]
  simp

theorem imod_congr {L : ℕ} (m m' k : ℤ) (h : m = m' + k * L) : imod m L = imod m' L := by
  subst h; unfold imod; rw [Int.add_mul_emod_self_right]

theorem imod_lt {L : ℕ} (hL : 0 < L) (m : ℤ) : imod m L < L := toNat_emod_lt hL m

theorem imod_natCast {L : ℕ} (n : ℕ) (hn : n < L) : imod (n : ℤ) L = n :=
  toNat_emod_of_eq n hn n 0 (by ring)

theorem extNat_of_lt {L : ℕ} (Z : Fin L → ℂ) (n : ℕ) (hn : n < L) : extNat Z n = Z ⟨n, hn⟩ := by
  simp [extNat, hn]

theorem norm_extNat_le {L : ℕ} (Z : Fin L → ℂ) (n : ℕ) : ‖extNat Z n‖ ≤ ‖Z‖ := by
  unfold extNat
  split_ifs with h
  · exact norm_le_pi_norm Z _
  · rw [norm_zero]; exact norm_nonneg _

theorem shiftFin_zero {L : ℕ} (hL : 0 < L) :
    shiftFin (⟨0, hL⟩ : Fin L) (-1) = ⟨L - 1, by omega⟩ := by
  apply Fin.ext
  show ((((0 : ℕ) : ℤ) + (-1)) % (L : ℤ)).toNat = L - 1
  exact toNat_emod_of_eq (L - 1) (by omega) _ (-1) (by push_cast [Nat.cast_sub (by omega : 1 ≤ L)]; ring)

theorem shiftFin_succ {L : ℕ} (n : ℕ) (hn : n + 1 < L) :
    shiftFin (⟨n + 1, hn⟩ : Fin L) (-1) = ⟨n, by omega⟩ := by
  apply Fin.ext
  show ((((n + 1 : ℕ) : ℤ) + (-1)) % (L : ℤ)).toNat = n
  exact toNat_emod_of_eq n (by omega) _ 0 (by push_cast; ring)

/-! ## From `B⁻¹Y` to the ℕ-indexed recurrences (both orientations) -/

/-- Dividing `c_max Z_n + c_min Z_{n-1} = Y_n` by `c_max`. -/
theorem div_eq_helper (c0 c1 : ℝ) (hc0 : c0 ≠ 0) (A B C : ℂ)
    (h : (c0 : ℂ) * A + (c1 : ℂ) * B = C) :
    A + ((c1 / c0 : ℝ) : ℂ) * B = ((c0⁻¹ : ℝ) : ℂ) * C := by
  have hc : (c0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0
  rw [← h]; push_cast; field_simp

/-- Forward reading: `extNat Z` satisfies the ℕ-indexed cyclic recurrence. -/
theorem fwd_eqs (c0 c1 : ℂ) (L : ℕ) (hL0 : 0 < L) (Z Y : Fin L → ℂ)
    (hZ : ∀ j : Fin L, c0 * Z j + c1 * Z (shiftFin j (-1)) = Y j) :
    c0 * extNat Z 0 + c1 * extNat Z (L - 1) = extNat Y 0 ∧
    ∀ n, n + 1 < L → c0 * extNat Z (n + 1) + c1 * extNat Z n = extNat Y (n + 1) := by
  constructor
  · have h := hZ ⟨0, hL0⟩
    rw [shiftFin_zero hL0] at h
    rw [extNat_of_lt Z 0 hL0, extNat_of_lt Z (L - 1) (by omega), extNat_of_lt Y 0 hL0]
    exact h
  · intro n hn
    have h := hZ ⟨n + 1, hn⟩
    rw [shiftFin_succ n hn] at h
    rw [extNat_of_lt Z (n + 1) hn, extNat_of_lt Z n (by omega), extNat_of_lt Y (n + 1) hn]
    exact h

/-- Backward reading, generic step: with `z_i = Z_{-i mod L}` and `y'_i = Y_{1-i mod L}`, the
equation of `B` at `j = 1 - i` reads `c_1 z_i + c_0 z_{i'} = y'_i` whenever `-i' ≡ 1 - i`. -/
theorem bwd_eq_gen (c0 c1 : ℂ) (L : ℕ) (hL0 : 0 < L) (Z Y : Fin L → ℂ)
    (hZ : ∀ j : Fin L, c0 * Z j + c1 * Z (shiftFin j (-1)) = Y j) (i i' : ℕ) (k : ℤ)
    (hii : -(i' : ℤ) = (1 - (i : ℤ)) + k * L) :
    c1 * extNat Z (imod (-(i : ℤ)) L) + c0 * extNat Z (imod (-(i' : ℤ)) L) =
      reorientIn L (extNat Y) i := by
  have h := hZ ⟨imod (1 - (i : ℤ)) L, imod_lt hL0 _⟩
  have hs : shiftFin (⟨imod (1 - (i : ℤ)) L, imod_lt hL0 _⟩ : Fin L) (-1) =
      ⟨imod (-(i : ℤ)) L, imod_lt hL0 _⟩ := by
    apply Fin.ext
    show ((((imod (1 - (i : ℤ)) L : ℕ) : ℤ) + (-1)) % (L : ℤ)).toNat = imod (-(i : ℤ)) L
    have h1 : ((imod (1 - (i : ℤ)) L : ℕ) : ℤ) = (1 - (i : ℤ)) % (L : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hL0.ne'))
    rw [h1, Int.emod_add_emod, show (1 - (i : ℤ)) + -1 = -(i : ℤ) by ring]
    rfl
  have hi' : imod (-(i' : ℤ)) L = imod (1 - (i : ℤ)) L := imod_congr _ _ k hii
  rw [hs] at h
  unfold reorientIn
  rw [hi', extNat_of_lt Z _ (imod_lt hL0 _), extNat_of_lt Z _ (imod_lt hL0 _),
    extNat_of_lt Y _ (imod_lt hL0 _)]
  linear_combination h

/-- `(-((-j) mod L)) mod L = j` for `j < L`. -/
theorem imod_neg_imod_neg {L : ℕ} (hL0 : 0 < L) (j : ℕ) (hj : j < L) :
    imod (-((imod (-(j : ℤ)) L : ℕ) : ℤ)) L = j := by
  have h1 : ((imod (-(j : ℤ)) L : ℕ) : ℤ) = (-(j : ℤ)) % (L : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hL0.ne'))
  rw [h1, imod_congr _ (j : ℤ) ((-(j : ℤ)) / (L : ℤ)) (by rw [Int.emod_def]; ring)]
  exact imod_natCast j hj

/-- `ahat ≤ 1 - 1/(2t)` from `|â - c_min/c_max| ≤ v ≤ 1/(64t)`, `c_max ≤ 1`, `c_min ≥ 0` and the
separation `c_max - c_min ≥ 7/(4t)` (Lemma 4.4 (bridge Lemma B)(iv)). -/
theorem ahat_le (t v ahat cM cm : ℝ) (ht : 2 ≤ t) (hv : v ≤ 1 / (64 * t)) (hcm : 0 ≤ cm)
    (hcM : cM ≤ 1) (hsep : 7 / (4 * t) ≤ cM - cm) (ha : |ahat - cm / cM| ≤ v) :
    ahat ≤ 1 - 1 / (2 * t) := by
  have htpos : 0 < t := by linarith
  have h7 : 0 < 7 / (4 * t) := by positivity
  have hcMpos : 0 < cM := by linarith
  have h1 : cm / cM ≤ 1 - 7 / (4 * t) := by
    rw [div_le_iff₀ hcMpos]
    have : 7 / (4 * t) * cM ≤ 7 / (4 * t) := by nlinarith
    nlinarith
  have h2 : ahat ≤ cm / cM + v := by linarith [le_abs_self (ahat - cm / cM)]
  have h4 : 1 / (64 * t) + 1 / (2 * t) ≤ 7 / (4 * t) := by
    have e : 7 / (4 * t) - (1 / (64 * t) + 1 / (2 * t)) = 79 / (64 * t) := by
      field_simp; ring
    have : 0 < 79 / (64 * t) := by positivity
    linarith
  linarith

end LemmaCivProof

open LemmaCivProof in
/-- **Lemma 4.6 (bridge Lemma C)(iv)** (`lem:bridge-C`): the two-pass cyclic sweep
returns `Ẑ` with `‖Ẑ - B⁻¹Y‖_∞ ≤ 32t²v·max(1,‖Y‖_∞)`, uniformly in the even cycle length `L`, and
all its states (prefix states, closure value, second-pass states) are `< 7t·max(1,‖Y‖_∞)`.
Proved from Lemma 4.4 (bridge Lemma B)(iv) (separation), Lemma 4.4 (bridge Lemma B)(v) (invertibility, `‖B⁻¹‖_∞ ≤ 4t/7`) and the
evenness / strict monotonicity of `G` (orientation `c_0 > c_1 ⟺ 2u < t`). -/
theorem lemmaC_iv_of (hiv : LemmaB_ivStmt) (hv : LemmaB_vStmt) (hneg : KernelG_negStmt)
    (hanti : KernelG_strictAntiOnStmt) : LemmaC_ivStmt := by
  intro rr hrr P ω α hC t ht u hu hvt mu ahat gam L hL hL0 hmu ha ha0 hgam Y
  obtain ⟨hω, hadm, hα⟩ := alphaAdmissible_of_params hC
  have hL2 : 2 ≤ L := by obtain ⟨k, hk⟩ := hL; omega
  obtain ⟨hdet, hnorm, hsep, -⟩ := hv ω hω α hadm t ht u hu L (by omega)
  have hsepiv := hiv ω hω α hadm t ht u hu
  have horient := orient hα hneg hanti t ht u hu
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.1
  set c0r := kernelG α (((u : ℝ) + 1 / 2) / (t : ℝ)) with hc0r
  set c1r := kernelG α (((u : ℝ) + 1 / 2) / (t : ℝ) - 1) with hc1r
  have hc0nn : 0 ≤ c0r := kernelG_nonneg hα.le _
  have hc1nn : 0 ≤ c1r := kernelG_nonneg hα.le _
  have hc0le : c0r ≤ 1 := kernelG_le_one hα _
  have hc1le : c1r ≤ 1 := kernelG_le_one hα _
  set Z := Matrix.mulVec (cycBidiag (c0r : ℂ) (c1r : ℂ) L)⁻¹ Y with hZdef
  have hZeq : ∀ j : Fin L, (c0r : ℂ) * Z j + (c1r : ℂ) * Z (shiftFin j (-1)) = Y j :=
    inv_mulVec_eq _ _ L hdet Y
  have hZnorm : ‖Z‖ ≤ (t : ℝ) * ‖Y‖ := by
    have h1 := norm_apply_le_opNormInf (Matrix.toLin' (cycBidiag (c0r : ℂ) (c1r : ℂ) L)⁻¹) Y
    rw [Matrix.toLin'_apply] at h1
    have h2 : opNormInf (Matrix.toLin' (cycBidiag (c0r : ℂ) (c1r : ℂ) L)⁻¹) ≤ t := by
      have : 4 * (t : ℝ) / 7 ≤ t := by linarith
      linarith
    calc ‖Z‖ ≤ _ := h1
      _ ≤ (t : ℝ) * ‖Y‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hYn : ∀ n, ‖extNat Y n‖ ≤ ‖Y‖ := fun n => norm_extNat_le Y n
  dsimp only
  by_cases h2 : 2 * u < t
  · -- forward orientation, `c_0 > c_1`
    have hd : decide (2 * u < t) = true := decide_eq_true h2
    have hlt : c1r < c0r := horient.1 h2
    have hc0pos : 0 < c0r := lt_of_le_of_lt hc1nn hlt
    rw [max_eq_left hlt.le] at hmu
    rw [max_eq_left hlt.le, min_eq_right hlt.le] at ha
    have hsep' : 7 / (4 * (t : ℝ)) ≤ c0r - c1r := by
      rw [abs_of_pos (by linarith : 0 < c0r - c1r)] at hsepiv; exact hsepiv
    have ha1 := ahat_le (t : ℝ) _ ahat c0r c1r htR hvt hc1nn hc0le hsep' ha
    obtain ⟨hE0, hEs⟩ := fwd_eqs _ _ L hL0 Z Y hZeq
    have core := fwd_core hrr (P + 2) (t : ℝ) htR hvt L hL hL0 mu ahat gam (c1r / c0r) c0r⁻¹ hmu
      ha0 ha1 ha hgam (extNat Y) ‖Y‖ hYn (extNat Z)
      (div_eq_helper c0r c1r hc0pos.ne' _ _ _ hE0)
      (fun n hn => div_eq_helper c0r c1r hc0pos.ne' _ _ _ (hEs n hn))
      (fun n _ => (norm_extNat_le Z n).trans hZnorm)
    simp only [hd, cycSweepR, ↓reduceIte]
    refine ⟨fun j => ?_, core.2.1, core.2.2⟩
    have h := core.1 j j.isLt
    rwa [extNat_of_lt Z j j.isLt] at h
  · -- backward orientation, `c_1 > c_0`
    have hd : decide (2 * u < t) = false := decide_eq_false h2
    have hlt : c0r < c1r := horient.2 h2
    have hc1pos : 0 < c1r := lt_of_le_of_lt hc0nn hlt
    rw [max_eq_right hlt.le] at hmu
    rw [max_eq_right hlt.le, min_eq_left hlt.le] at ha
    have hsep' : 7 / (4 * (t : ℝ)) ≤ c1r - c0r := by
      rw [abs_of_neg (by linarith : c0r - c1r < 0)] at hsepiv; linarith
    have ha1 := ahat_le (t : ℝ) _ ahat c1r c0r htR hvt hc0nn hc1le hsep' ha
    set zb : ℕ → ℂ := fun i => extNat Z (imod (-(i : ℤ)) L) with hzb
    have hB0 : (c1r : ℂ) * zb 0 + (c0r : ℂ) * zb (L - 1) = reorientIn L (extNat Y) 0 :=
      bwd_eq_gen _ _ L hL0 Z Y hZeq 0 (L - 1) (-1) (by omega)
    have hBs : ∀ n, n + 1 < L → (c1r : ℂ) * zb (n + 1) + (c0r : ℂ) * zb n =
        reorientIn L (extNat Y) (n + 1) :=
      fun n hn => bwd_eq_gen _ _ L hL0 Z Y hZeq (n + 1) n 0 (by omega)
    have hy' : ∀ n, ‖reorientIn L (extNat Y) n‖ ≤ ‖Y‖ := fun n => norm_extNat_le Y _
    have core := fwd_core hrr (P + 2) (t : ℝ) htR hvt L hL hL0 mu ahat gam (c0r / c1r) c1r⁻¹ hmu
      ha0 ha1 ha hgam (reorientIn L (extNat Y)) ‖Y‖ hy' zb
      (div_eq_helper c1r c0r hc1pos.ne' _ _ _ hB0)
      (fun n hn => div_eq_helper c1r c0r hc1pos.ne' _ _ _ (hBs n hn))
      (fun n _ => (norm_extNat_le Z _).trans hZnorm)
    simp only [hd, cycSweepR, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun j => ?_, core.2.1, core.2.2⟩
    have h := core.1 (imod (-((j : ℕ) : ℤ)) L) (imod_lt hL0 _)
    have hzj : zb (imod (-((j : ℕ) : ℤ)) L) = Z j := by
      show extNat Z (imod (-((imod (-((j : ℕ) : ℤ)) L : ℕ) : ℤ)) L) = Z j
      rw [imod_neg_imod_neg hL0 j j.isLt, extNat_of_lt Z j j.isLt]
    rwa [hzj] at h

end SubNLogN.Math.Bridge
