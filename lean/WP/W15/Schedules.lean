import IntMul.Theorem6And7Barriers
import IntMul.MaterializedAndComputable.PaperStopAndRadix2Leaf
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.OrderOfElement
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W15.Schedules: multiplicative order of `y` and `⟨y⟩`-driven schedule depth (analyzing the omitted earlier `[MS]` draft barrier discussion)

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every result in this file holds only in the
restricted model defined explicitly below.

**Model (c): `⟨y⟩`-driven schedules.** A recursion schedule is a sequence of log-sizes
`K 0 ≥ K 1 ≥ … ≥ K L`. Level `ℓ` runs a synthetic FFT of length `t₁ = 2^(K ℓ - K (ℓ+1))` over
`R_r = ℂ[y]/(y^r + 1)` with `r = 2^(K (ℓ+1))`, driven by a root of unity `ω` that is a power of `y`
and has multiplicative order exactly `t₁` (`YDrivenSchedule`). `R_r` is Mathlib's
`AdjoinRoot (X^r + C 1)`. Nothing here is a cost statement.

**What is proved.**
* `YDrivenSchedule.admissible`: the snapshot's `AdmissibleRingSchedule` (B67:1057), which the snapshot
  *assumes*, follows from the model (from `y^(2r) = 1` alone). Hence
  `K 0 + 1 ≤ 2^L (K L + 1)` (B67:1064) holds for every `⟨y⟩`-driven schedule.
* `tightK_*`: that bound is attained.
* `paper75_depth_claim_false`: the schedule-depth claim "`L ≥ log₂ log₂ n − O(1)`" in the structural-barrier discussion of an earlier `[MS]` draft (omitted in the current `[MS]`) is false.
* `orderOf_yRoot_pow2`: `y` has order exactly `2r` in `R_r` for `r = 2^ρ` (`ord(y) = 2r` in `R_r`, cf. `[MS]` §3.5).
* The snapshot's actual schedule (`buildQuantizedSpecPaperStop`, PaperStopAndRadix2Leaf.lean:43, which
  recurses on `K - K/2`) follows `halvingK` (`paperStop_logSizes`), is a `⟨y⟩`-driven schedule whose
  roots are the snapshot's twiddles `y^(2 c₁)` (`halvingYDriven`), and is within one level of the
  optimal depth among all admissible schedules with the same endpoints (`halving_depth_near_optimal`).
-/

namespace WP.W15

open IntMul Polynomial

/-! ## 1. Refutation of the omitted earlier `[MS]` draft schedule-depth claim -/

/-- The counterexample family `K ℓ = 2^(J + a - ℓ) - 1` (here `t₁ = 2r` at every level). -/
def counterK (a J l : ℕ) : ℕ := 2 ^ (J + a - l) - 1

theorem counterK_admissible (a J : ℕ) : AdmissibleRingSchedule J (counterK a J) := by
  intro l hl
  have e : J + a - l = (J + a - (l + 1)) + 1 := by omega
  unfold counterK
  rw [e]
  set m := J + a - (l + 1) with hm
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hsucc : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
  refine ⟨by omega, ?_⟩
  have h1 : 2 ^ (m + 1) - 1 - (2 ^ m - 1) = 2 ^ m := by omega
  have h2 : 2 * 2 ^ (2 ^ m - 1) = 2 ^ (2 ^ m) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h1, h2]

/-- The schedule-depth claim from the structural-barrier discussion of an earlier `[MS]` draft (omitted in the current `[MS]`), stated for log-sizes: there is a constant `C`
such that every admissible schedule that descends from `K 0` to a leaf with
`K L ≤ 2 log₂ (K 0)` (i.e. `R_L ≤ (log₂ R₀)²`, corresponding to `R_L = O((log n)²)`) has depth
`L ≥ log₂ (K 0) - C`. With `R₀ = 2^(K 0)` and `n ≈ K 0 · 2^(K 0)`, `log₂ (K 0)` is
`log₂ log₂ n` up to `o(1)`. -/
def PaperDepthClaim : Prop :=
  ∃ C : ℕ, ∀ (L : ℕ) (K : ℕ → ℕ), AdmissibleRingSchedule L K →
    K L ≤ 2 * Nat.log 2 (K 0) → Nat.log 2 (K 0) ≤ L + C

theorem log_two_pow_sub_one (N : ℕ) : Nat.log 2 (2 ^ (N + 1) - 1) = N := by
  have hpos : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  have hsucc : 2 ^ (N + 1) = 2 ^ N * 2 := pow_succ 2 N
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · omega

/-- **The omitted earlier `[MS]` draft schedule-depth claim is false.** For every `C`, the family `counterK (C+2) (2^(C+2))`
is admissible, reaches a polylogarithmic leaf, and has depth `log₂ (K 0) - C - 1`. -/
theorem paper75_depth_claim_false : ¬ PaperDepthClaim := by
  rintro ⟨C, hC⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = 2 ^ (C + 2) := ⟨_, rfl⟩
  have hadm := counterK_admissible (C + 2) J
  have hJpos : 1 ≤ J := hJ ▸ Nat.one_le_two_pow
  have hK0 : counterK (C + 2) J 0 = 2 ^ ((J + (C + 2) - 1) + 1) - 1 := by
    have e : J + (C + 2) - 0 = (J + (C + 2) - 1) + 1 := by omega
    unfold counterK
    rw [e]
  have hKL : counterK (C + 2) J J = 2 ^ (C + 2) - 1 := by
    have e : J + (C + 2) - J = C + 2 := by omega
    unfold counterK
    rw [e]
  have hlog : Nat.log 2 (counterK (C + 2) J 0) = J + (C + 2) - 1 := by
    rw [hK0, log_two_pow_sub_one]
  have hstop : counterK (C + 2) J J ≤ 2 * Nat.log 2 (counterK (C + 2) J 0) := by
    rw [hKL, hlog, ← hJ]
    omega
  have := hC J (counterK (C + 2) J) hadm hstop
  rw [hlog] at this
  omega

/-! ## 2. The snapshot's depth bound is tight -/

/-- The extremal schedule `K ℓ = 2^(L - ℓ) (c + 1) - 1`. -/
def tightK (L c l : ℕ) : ℕ := 2 ^ (L - l) * (c + 1) - 1

theorem tightK_admissible (L c : ℕ) : AdmissibleRingSchedule L (tightK L c) := by
  intro l hl
  have e : L - l = (L - (l + 1)) + 1 := by omega
  unfold tightK
  rw [e]
  set x := 2 ^ (L - (l + 1)) * (c + 1) with hx
  have hxpos : 1 ≤ x := by
    rw [hx]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
  have hsucc : 2 ^ (L - (l + 1) + 1) * (c + 1) = 2 * x := by rw [hx, pow_succ]; ring
  rw [hsucc]
  refine ⟨by omega, ?_⟩
  have h1 : 2 * x - 1 - (x - 1) = x := by omega
  have h2 : 2 * 2 ^ (x - 1) = 2 ^ x := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h1, h2]

theorem tightK_end (L c : ℕ) : tightK L c L = c := by
  simp [tightK]

/-- **Tightness.** The extremal schedule meets `K 0 + 1 ≤ 2^L (K L + 1)` with equality. -/
theorem tightK_extremal (L c : ℕ) : tightK L c 0 + 1 = 2 ^ L * (tightK L c L + 1) := by
  rw [tightK_end]
  unfold tightK
  have : 1 ≤ 2 ^ L * (c + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
  simp only [Nat.sub_zero]
  omega

/-! ## 3. `⟨y⟩`-driven schedules in `R_r = ℂ[y]/(y^r + 1)` -/

/-- `y^r + 1`. -/
noncomputable def rPoly (r : ℕ) : ℂ[X] := X ^ r + C 1

/-- `R_r = ℂ[y]/(y^r + 1)`. -/
abbrev Rr (r : ℕ) : Type := AdjoinRoot (rPoly r)

/-- The synthetic root `y ∈ R_r`. -/
noncomputable abbrev yRoot (r : ℕ) : Rr r := AdjoinRoot.root (rPoly r)

theorem yRoot_pow_r (r : ℕ) : yRoot r ^ r = -1 := by
  have h : yRoot r ^ r + 1 = 0 := by
    have h0 := AdjoinRoot.eval₂_root (rPoly r)
    rw [rPoly, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one] at h0
    exact h0
  linear_combination h

theorem yRoot_pow_two_mul (r : ℕ) : yRoot r ^ (2 * r) = 1 := by
  rw [mul_comm, pow_mul, yRoot_pow_r]
  norm_num

theorem neg_one_ne_one_Rr (r : ℕ) (hr : 0 < r) : (-1 : Rr r) ≠ 1 := by
  intro h
  have hdeg : (rPoly r).degree ≠ 0 := by
    rw [rPoly, Polynomial.degree_X_pow_add_C hr]
    exact_mod_cast hr.ne'
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  have e : (AdjoinRoot.of (rPoly r)) (-1) = (AdjoinRoot.of (rPoly r)) 1 := by
    rw [map_neg, map_one, h]
  have := hinj e
  norm_num at this

theorem yRoot_pow_r_ne_one (r : ℕ) (hr : 0 < r) : yRoot r ^ r ≠ 1 := by
  rw [yRoot_pow_r]
  exact neg_one_ne_one_Rr r hr

/-- **`ord(y) = 2r`** in `R_r` for `r = 2^ρ` (in Mathlib's quotient
ring; the snapshot proves it in its coefficient model, B67:1017). -/
theorem orderOf_yRoot_pow2 (ρ : ℕ) : orderOf (yRoot (2 ^ ρ)) = 2 * 2 ^ ρ := by
  have h1 : ¬ yRoot (2 ^ ρ) ^ 2 ^ ρ = 1 := yRoot_pow_r_ne_one (2 ^ ρ) (by positivity)
  have h2 : yRoot (2 ^ ρ) ^ 2 ^ (ρ + 1) = 1 := by
    rw [pow_succ, mul_comm]
    exact yRoot_pow_two_mul (2 ^ ρ)
  rw [orderOf_eq_prime_pow h1 h2, pow_succ, mul_comm]

/-- Any power of `y` has order dividing `2r`. -/
theorem orderOf_dvd_of_mem_powers (r : ℕ) {ω : Rr r} (h : ω ∈ Submonoid.powers (yRoot r)) :
    orderOf ω ∣ 2 * r := by
  obtain ⟨n, rfl⟩ := h
  apply orderOf_dvd_of_pow_eq_one
  rw [← pow_mul, mul_comm, pow_mul, yRoot_pow_two_mul, one_pow]

/-- **Model (c).** A `⟨y⟩`-driven schedule of depth `L`: non-increasing log-sizes `K`, and at each level
`ℓ < L` a root `ω ℓ` in `R_{2^(K (ℓ+1))}` that is a power of `y` and has order exactly
`t₁ = 2^(K ℓ - K (ℓ+1))`. -/
structure YDrivenSchedule (L : ℕ) where
  K : ℕ → ℕ
  mono : ∀ l < L, K (l + 1) ≤ K l
  ω : ∀ l, l < L → Rr (2 ^ K (l + 1))
  ω_mem : ∀ l (hl : l < L), ω l hl ∈ Submonoid.powers (yRoot (2 ^ K (l + 1)))
  ω_order : ∀ l (hl : l < L), orderOf (ω l hl) = 2 ^ (K l - K (l + 1))

/-- **Admissibility is derived, not assumed.** -/
theorem YDrivenSchedule.admissible {L : ℕ} (S : YDrivenSchedule L) :
    AdmissibleRingSchedule L S.K := by
  intro l hl
  refine ⟨S.mono l hl, ?_⟩
  have h := orderOf_dvd_of_mem_powers _ (S.ω_mem l hl)
  rw [S.ω_order l hl] at h
  exact h

/-- **Corrected `⟨y⟩`-driven schedule depth bound (cf. `theorem7_5_admissible_schedule_depth_lower_bound`).** Every `⟨y⟩`-driven schedule satisfies
`K 0 + 1 ≤ 2^L (K L + 1)`, i.e. `L ≥ log₂ ((K 0 + 1)/(K L + 1))`; this is tight (`tightK_extremal`). -/
theorem YDrivenSchedule.depth_lower_bound {L : ℕ} (S : YDrivenSchedule L) :
    S.K 0 + 1 ≤ 2 ^ L * (S.K L + 1) :=
  (theorem7_5_admissible_schedule_depth_lower_bound L S.K S.admissible).2

/-! ## 4. The snapshot's schedule: `K ↦ K - K/2` -/

/-- One level of the snapshot's split (`buildQuantizedSpecPaperStop` recurses on `K - K / 2`). -/
def halve (K : ℕ) : ℕ := K - K / 2

/-- The snapshot's log-size sequence from `K₀`. -/
def halvingK (K0 : ℕ) : ℕ → ℕ
  | 0 => K0
  | l + 1 => halve (halvingK K0 l)

theorem halvingK_zero (K0 : ℕ) : halvingK K0 0 = K0 := rfl

theorem halvingK_succ (K0 l : ℕ) : halvingK K0 (l + 1) = halve (halvingK K0 l) := rfl

theorem halvingK_succ' (K0 l : ℕ) : halvingK K0 (l + 1) = halvingK (halve K0) l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [halvingK_succ, ih, halvingK_succ]

theorem halvingK_admissible (K0 L : ℕ) : AdmissibleRingSchedule L (halvingK K0) := by
  intro l _
  rw [halvingK_succ]
  set K := halvingK K0 l
  unfold halve
  refine ⟨by omega, ?_⟩
  have h1 : K - (K - K / 2) = K / 2 := by omega
  rw [h1, ← pow_succ']
  exact Nat.pow_dvd_pow 2 (by omega)

theorem halvingK_depth_upper (K0 L : ℕ) : 2 ^ L * (halvingK K0 L - 1) ≤ K0 - 1 := by
  induction L with
  | zero => simp [halvingK_zero]
  | succ L ih =>
    rw [halvingK_succ, pow_succ]
    have h : 2 * (halve (halvingK K0 L) - 1) ≤ halvingK K0 L - 1 := by
      unfold halve
      omega
    calc 2 ^ L * 2 * (halve (halvingK K0 L) - 1) = 2 ^ L * (2 * (halve (halvingK K0 L) - 1)) := by
          ring
      _ ≤ 2 ^ L * (halvingK K0 L - 1) := Nat.mul_le_mul_left _ h
      _ ≤ K0 - 1 := ih

/-- **The snapshot's schedule is depth-optimal up to one level.** Any admissible schedule `K'` with
the same endpoints (`K' 0 = K₀`, `K' L' = halvingK K₀ L ≥ 2`) has depth `L' ≥ L - 1`. -/
theorem halving_depth_near_optimal (K0 L L' : ℕ) (K' : ℕ → ℕ)
    (hadm : AdmissibleRingSchedule L' K') (h0 : K' 0 = K0) (hend : K' L' = halvingK K0 L)
    (hge : 2 ≤ halvingK K0 L) : L ≤ L' + 1 := by
  have hlow := (theorem7_5_admissible_schedule_depth_lower_bound L' K' hadm).2
  rw [h0, hend] at hlow
  have hup := halvingK_depth_upper K0 L
  set x := halvingK K0 L with hx
  have hx3 : x + 1 ≤ 3 * (x - 1) := by omega
  have hlt : 2 ^ L * (x - 1) < 3 * 2 ^ L' * (x - 1) := by
    calc 2 ^ L * (x - 1) ≤ K0 - 1 := hup
      _ < K0 + 1 := by omega
      _ ≤ 2 ^ L' * (x + 1) := hlow
      _ ≤ 2 ^ L' * (3 * (x - 1)) := Nat.mul_le_mul_left _ hx3
      _ = 3 * 2 ^ L' * (x - 1) := by ring
  have hpow : 2 ^ L < 3 * 2 ^ L' := Nat.lt_of_mul_lt_mul_right hlt
  have hpow' : 2 ^ L < 2 ^ (L' + 2) := by
    calc 2 ^ L < 3 * 2 ^ L' := hpow
      _ < 4 * 2 ^ L' := by
          have : 0 < 2 ^ L' := by positivity
          omega
      _ = 2 ^ (L' + 2) := by rw [pow_add]; ring
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow'
  omega

/-- The snapshot's twiddle at a level with log-sizes `K → halve K`: `ω = y^(2 c₁)` with
`c₁ = r / t₁ = 2^(halve K - K/2)` (the polynomial-transform twiddle of `[MS]` §3.5, eq. (12) and Proposition 4.1, `syntheticDFT`, Preliminaries.lean:283). -/
noncomputable def snapshotTwiddle (K : ℕ) : Rr (2 ^ halve K) :=
  yRoot (2 ^ halve K) ^ (2 * 2 ^ (halve K - K / 2))

/-- The snapshot's twiddle has order exactly `t₁ = 2^(K/2)`. -/
theorem orderOf_snapshotTwiddle (K : ℕ) : orderOf (snapshotTwiddle K) = 2 ^ (K - halve K) := by
  have he : K - halve K = K / 2 := by unfold halve; omega
  rw [he]
  have hK' : K / 2 ≤ halve K := by unfold halve; omega
  rcases Nat.eq_zero_or_pos (K / 2) with h0 | hpos
  · rw [h0, pow_zero, orderOf_eq_one_iff]
    unfold snapshotTwiddle
    rw [h0, Nat.sub_zero, mul_comm, pow_mul]
    have : yRoot (2 ^ halve K) ^ (2 ^ halve K * 2) = 1 := by
      rw [mul_comm]
      exact yRoot_pow_two_mul _
    rw [← pow_mul, this]
  · obtain ⟨n, hn⟩ : ∃ n, K / 2 = n + 1 := ⟨K / 2 - 1, by omega⟩
    rw [hn]
    apply orderOf_eq_prime_pow
    · unfold snapshotTwiddle
      rw [← pow_mul]
      have hexp : 2 * 2 ^ (halve K - K / 2) * 2 ^ n = 2 ^ halve K := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
      rw [hexp]
      exact yRoot_pow_r_ne_one _ (by positivity)
    · unfold snapshotTwiddle
      rw [← pow_mul]
      have hexp : 2 * 2 ^ (halve K - K / 2) * 2 ^ (n + 1) = 2 * 2 ^ halve K := by
        rw [← pow_succ', ← pow_add, ← pow_succ']
        congr 1
        omega
      rw [hexp]
      exact yRoot_pow_two_mul _

/-- **The snapshot's schedule is an instance of model (c)**, with the snapshot's own twiddles. -/
noncomputable def halvingYDriven (K0 L : ℕ) : YDrivenSchedule L where
  K := halvingK K0
  mono := fun l _ => by
    show halve (halvingK K0 l) ≤ halvingK K0 l
    unfold halve
    omega
  ω := fun l _ => snapshotTwiddle (halvingK K0 l)
  ω_mem := fun _ _ => ⟨_, rfl⟩
  ω_order := fun l _ => orderOf_snapshotTwiddle (halvingK K0 l)

/-- Log-sizes along the spine of a `QuantizedFastDFTSpec` (a step node records its `K`). -/
def specLogSizes : QuantizedFastDFTSpec → List ℕ
  | .base _ R => [Nat.log 2 R]
  | .step _ K _ _ _ _ child => K :: specLogSizes child

/-- **The snapshot's spec follows `halvingK`.** -/
theorem paperStop_logSizes (L p K i : ℕ)
    (hi : i < (specLogSizes (buildQuantizedSpecPaperStop L p K)).length) :
    (specLogSizes (buildQuantizedSpecPaperStop L p K)).getD i 0 = halvingK K i := by
  induction L generalizing p K i with
  | zero =>
    simp only [buildQuantizedSpecPaperStop, specLogSizes, List.length_singleton] at hi ⊢
    have : i = 0 := by omega
    subst this
    simp [Nat.log_pow, halvingK_zero]
  | succ L ih =>
    simp only [buildQuantizedSpecPaperStop] at hi ⊢
    split_ifs with hstop
    · rw [if_pos hstop] at hi
      simp only [specLogSizes, List.length_singleton] at hi ⊢
      have : i = 0 := by omega
      subst this
      simp [Nat.log_pow, halvingK_zero]
    · rw [if_neg hstop] at hi
      simp only [quantizedBoxGaussianStepSpec, specLogSizes, List.length_cons] at hi ⊢
      cases i with
      | zero => simp [halvingK_zero]
      | succ i =>
        rw [List.getD_cons_succ, ih (pChild p K) (K - K / 2) i (by omega)]
        exact (halvingK_succ' K i).symm

/-- **The snapshot's schedule satisfies the (corrected) admissibility condition** along its whole
spine. -/
theorem paperStop_admissible (L p K : ℕ) :
    AdmissibleRingSchedule ((specLogSizes (buildQuantizedSpecPaperStop L p K)).length - 1)
      (fun l => (specLogSizes (buildQuantizedSpecPaperStop L p K)).getD l 0) := by
  intro l hl
  dsimp only
  rw [paperStop_logSizes L p K l (by omega), paperStop_logSizes L p K (l + 1) (by omega)]
  exact halvingK_admissible K (l + 1) l (by omega)

#assert_std_axioms counterK_admissible paper75_depth_claim_false tightK_admissible tightK_extremal
  orderOf_yRoot_pow2 orderOf_dvd_of_mem_powers YDrivenSchedule.admissible
  YDrivenSchedule.depth_lower_bound halvingK_admissible halvingK_depth_upper
  halving_depth_near_optimal orderOf_snapshotTwiddle paperStop_logSizes paperStop_admissible

#assert_std_axioms log_two_pow_sub_one tightK_end yRoot_pow_r yRoot_pow_two_mul neg_one_ne_one_Rr
  yRoot_pow_r_ne_one halvingK_zero halvingK_succ halvingK_succ'

end WP.W15
