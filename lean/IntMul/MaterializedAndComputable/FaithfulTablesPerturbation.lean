import IntMul.MaterializedAndComputable.PaperHeadlinePipeline

/-!
# Part 2a — Perturbation-Tolerant Table Faithfulness (`TablesFaithful`)

This module defines `TablesFaithful : ComputablePaperFastDFTSpec → QuantizedFastDFTSpec → Prop`
and proves that any `cSpec` whose tables (`twiddles`, `filterTaps`, `preTwiddles`, `postTwiddles`,
`c0Table`, `c1Table`) approximate the mathematical transcendentals within `1` ULP preserves:
1. The inductive DFT error bound `‖toScaledComplex spec.p (read1D (computablePaperFastDFT p_in cSpec xArr) u) - dft1D spec.size x u‖ ≤ (2 : ℝ) ^ (-(spec.p : ℤ)) * M`,
2. Exact integer multiplication `computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B = A * B`, and
3. The `7000 * spec.intrinsicCostRadix2Leaf` program cost bound.
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-- **Perturbation-Tolerant Table Faithfulness Predicate (`TablesFaithful`, `[MS]` §3.3 (Lemma 3.2, eq. (7)) & §7)**:
Certifies that all four precomputed integer table families in `cSpec : ComputablePaperFastDFTSpec`
faithfully approximate the mathematical transcendentals of `spec : QuantizedFastDFTSpec` within `1` ULP:
1. **Leaf Twiddles (`T1`)**: At `.basePow2 p K twiddles` matching `.base p (2 ^ K)`, `8 ≤ p`, `K ≤ 5 * p`,
   and every leaf twiddle entry `(s < K, u < 2^(s + 1))` is within `2 * complexQuantizeMaxErr (2 * p + K + 8)`
   of `stdChar (u / 2^(s + 1))`.
2. **Pre-Folded Sinc-Gaussian Spread Taps (`T3`)**: At `.step`, for each row `j1 < t1`, `filterTaps.getD j1 []`
   is the modulo-`W_eff` folded sum of raw integer taps `G : ℕ → ℤ` (`s < 2 * pSub + 1`) such that each
   `G s / 2^pSub` is within `2^(-pSub)` (`1` ULP at scale `2^pSub`) of
   `sincGaussian α ((s - pSub) - j1 / t1)` and satisfies `(G s).natAbs ≤ 2 ^ pSub + 1`.
3. **Chirp Pre/Post-Twiddles (`T2`)**: Every `k2 < r` entry of `preTwiddles` and `postTwiddles` is within
   `2 * complexQuantizeMaxErr pSub` of `zetaRoot r k2` and `zetaRoot r (-k2)`.
4. **Passband Deconvolution Tables (`T4`)**: Every `u2 < r` entry of `c0Table` and `c1Table` has zero
   imaginary part, lies in `[0, 2^(pSub + 2)]`, is within `2 * realQuantizeMaxErr pSub` (`1` ULP at scale
   `2^(pSub + 2)`) of `c0Coeff (realErfScaled α) (u2 / r)` and `c1Coeff (realErfScaled α) (u2 / r)`,
   and respects the passband regime ordering (`c1 ≤ c0` for `2 * u2 < r`, `c1 = c0` at `2 * u2 = r`,
   `c0 ≤ c1` for `r < 2 * u2`). -/
inductive TablesFaithful : ComputablePaperFastDFTSpec → QuantizedFastDFTSpec → Prop
  | base (p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
      (hp : 8 ≤ p) (hK : K ≤ 5 * p)
      (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
        ‖toScaledComplex (2 * p + K + 8) (read1D (twiddles.getD s #[]) u) -
            stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤
          2 * complexQuantizeMaxErr (2 * p + K + 8)) :
      TablesFaithful (.basePow2 p K twiddles) (.base p (2 ^ K))
  | step (p K t1 r c1 : ℕ) (v1Of : ℕ → ℕ → ℕ)
      (filterTaps : Array (List ℤ))
      (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
      (cChild : ComputablePaperFastDFTSpec) (child : QuantizedFastDFTSpec)
      (hv1_eq : ∀ u2 u1 : ℕ, v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1)
      (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
        filterTaps.getD j1 [] =
          (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
            ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
                (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
              G s) ∧
        (∀ s < 2 * (2 * pChild p K) + 1,
          |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
              sincGaussian (alphaSchedule (pWork p K))
                (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
            (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
        (∀ s < 2 * (2 * pChild p K) + 1,
          (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
      (hPre : ∀ k2 < r,
        ‖toScaledComplex (2 * pChild p K) (read1D preTwiddles k2) -
            zetaRoot r (k2 : ℝ)‖ ≤
          2 * complexQuantizeMaxErr (2 * pChild p K))
      (hPost : ∀ k2 < r,
        ‖toScaledComplex (2 * pChild p K) (read1D postTwiddles k2) -
            zetaRoot r (-(k2 : ℝ))‖ ≤
          2 * complexQuantizeMaxErr (2 * pChild p K))
      (hC01 : ∀ u2 < r,
        let pSub := 2 * pChild p K
        let y := (u2 : ℝ) / (r : ℝ)
        let α := alphaSchedule (pWork p K)
        let c0_pair := read1D c0Table u2
        let c1_pair := read1D c1Table u2
        c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
        0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
        0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
        |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
          2 * realQuantizeMaxErr pSub ∧
        |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
          2 * realQuantizeMaxErr pSub ∧
        (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
        (2 * u2 = r → c1_pair = c0_pair) ∧
        (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1))
      (hChild : TablesFaithful cChild child) :
      TablesFaithful
        (.step p (2 * pChild p K) (2 * pChild p K) t1 r
          filterTaps preTwiddles postTwiddles c0Table c1Table cChild)
        (.step p K t1 r c1 v1Of child)

theorem TablesFaithful.p_eq {cSpec : ComputablePaperFastDFTSpec} {spec : QuantizedFastDFTSpec}
    (h : TablesFaithful cSpec spec) : cSpec.p = spec.p := by
  cases h <;> rfl

theorem TablesFaithful.paperExecutableValid {cSpec : ComputablePaperFastDFTSpec} {spec : QuantizedFastDFTSpec}
    (h : TablesFaithful cSpec spec) : spec.PaperExecutableValid := by
  induction h with
  | base p K _ hp hK _ =>
    exact QuantizedFastDFTSpec.PaperExecutableValid.base hp hK
  | step _ _ _ _ _ _ _ _ _ _ _ _ _ hv1_eq _ _ _ _ _ ih =>
    exact QuantizedFastDFTSpec.PaperExecutableValid.step hv1_eq ih

/-- The mathematical reference table specification `idealRoundedPaperTables spec` satisfies `TablesFaithful`. -/
theorem idealRoundedPaperTables_faithful
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid) :
    TablesFaithful (idealRoundedPaperTables spec) spec := by
  induction hvalid with
  | base p R =>
    cases hexec with
    | @base p K hp hK =>
      dsimp only [idealRoundedPaperTables]
      rw [nat_log2_two_pow]
      refine TablesFaithful.base p K _ hp hK (fun s hs u hu => ?_)
      rw [array_getD_ofFn_of_lt K _ #[] s hs, read1D_ofFn_of_lt (2 ^ (s + 1)) _ hu,
          toScaledComplex_realQuantizeInt_pair]
      have h1 := norm_complexQuantize_sub_le (2 * p + K + 8)
        (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ)))
      have hq_nonneg : 0 ≤ complexQuantizeMaxErr (2 * p + K + 8) := by
        unfold complexQuantizeMaxErr; positivity
      linarith
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hexec with
    | step hv1_eq hchild_exec =>
      dsimp only [idealRoundedPaperTables]
      set α := alphaSchedule (pWork p K)
      set pSub := 2 * pChild p K
      have hα : 0 < α := alphaSchedule_pos (pWork p K) (by unfold pWork; omega)
      have hqSub_nonneg : 0 ≤ complexQuantizeMaxErr pSub := by
        unfold complexQuantizeMaxErr; positivity
      have hrqSub_nonneg : 0 ≤ realQuantizeMaxErr pSub := by
        unfold realQuantizeMaxErr; positivity
      refine TablesFaithful.step p K t1 r c1 v1Of _ _ _ _ _ _ child hv1_eq
        (fun j1 hj1 => ?_) (fun k2 hk2 => ?_) (fun k2 hk2 => ?_) (fun u2 hu2 => ?_)
        (ih hchild_exec)
      · refine ⟨fun s => quantizeInt pSub (sincGaussian α (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))),
          ?_, ?_, ?_⟩
        · rw [array_getD_ofFn_of_lt t1 _ [] j1 hj1]
          rfl
        · intro s _
          have h1 := abs_quantizeReal_sub_le pSub
            (sincGaussian α (((s : ℤ) - (pSub : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
          have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pSub : ℤ)) := zpow_pos (by norm_num) _
          dsimp [quantizeReal] at h1
          linarith
        · intro s _
          dsimp only [pSub]
          have h1 := natAbs_quantizeInt_le (2 * pChild p K) 1
            (sincGaussian α (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
            (by simpa using abs_sincGaussian_le_one α (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
          omega
      · rw [read1D_ofFn_of_lt r _ hk2, toScaledComplex_realQuantizeInt_pair]
        have h1 := norm_complexQuantize_sub_le pSub (zetaRoot r (k2 : ℝ))
        linarith
      · rw [read1D_ofFn_of_lt r _ hk2, toScaledComplex_realQuantizeInt_pair]
        have h1 := norm_complexQuantize_sub_le pSub (zetaRoot r (-(k2 : ℝ)))
        linarith
      · dsimp only
        rw [read1D_ofFn_of_lt r _ hu2, read1D_ofFn_of_lt r _ hu2]
        set y := (u2 : ℝ) / (r : ℝ)
        set c0R := c0Coeff (realErfScaled α) y
        set c1R := c1Coeff (realErfScaled α) y
        have hr_pos_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
        have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
        have hy1 : y ≤ 1 := (div_le_one hr_pos_real).mpr (by exact_mod_cast hu2.le)
        have hc0_pos : 0 ≤ c0R := (c0Coeff_realErfScaled_pos α y hα).le
        have hc1_pos : 0 ≤ c1R := (c1Coeff_realErfScaled_pos α y hα).le
        have hsum_le1 : c0R + c1R ≤ 1 := c0_add_c1_realErfScaled_le_one α y hα
        have hc0_le1 : c0R ≤ 1 := by linarith
        have hc1_le1 : c1R ≤ 1 := by linarith
        have hc0_Icc := realQuantize_mem_Icc_zero_one pSub hc0_pos hc0_le1
        have hc1_Icc := realQuantize_mem_Icc_zero_one pSub hc1_pos hc1_le1
        have hscale_pos : (0 : ℝ) < (2 : ℝ) ^ (pSub + 2) := by positivity
        have hc0_int_bounds : 0 ≤ realQuantizeInt pSub c0R ∧ realQuantizeInt pSub c0R ≤ (2 : ℤ) ^ (pSub + 2) := by
          rw [realQuantize_eq_realQuantizeInt_div] at hc0_Icc
          have hlo : (0 : ℝ) ≤ (realQuantizeInt pSub c0R : ℝ) := by
            have := mul_nonneg hc0_Icc.1 hscale_pos.le
            rwa [div_mul_cancel₀ _ hscale_pos.ne'] at this
          have hhi : (realQuantizeInt pSub c0R : ℝ) ≤ (2 : ℝ) ^ (pSub + 2) := by
            exact (div_le_one hscale_pos).mp hc0_Icc.2
          exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
        have hc1_int_bounds : 0 ≤ realQuantizeInt pSub c1R ∧ realQuantizeInt pSub c1R ≤ (2 : ℤ) ^ (pSub + 2) := by
          rw [realQuantize_eq_realQuantizeInt_div] at hc1_Icc
          have hlo : (0 : ℝ) ≤ (realQuantizeInt pSub c1R : ℝ) := by
            have := mul_nonneg hc1_Icc.1 hscale_pos.le
            rwa [div_mul_cancel₀ _ hscale_pos.ne'] at this
          have hhi : (realQuantizeInt pSub c1R : ℝ) ≤ (2 : ℝ) ^ (pSub + 2) := by
            exact (div_le_one hscale_pos).mp hc1_Icc.2
          exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
        have hc0_re : (toScaledComplex pSub (realQuantizeInt pSub c0R, 0)).re = realQuantize pSub c0R :=
          (realQuantize_eq_realQuantizeInt_div pSub c0R).symm
        have hc1_re : (toScaledComplex pSub (realQuantizeInt pSub c1R, 0)).re = realQuantize pSub c1R :=
          (realQuantize_eq_realQuantizeInt_div pSub c1R).symm
        have hc0_err : |realQuantize pSub c0R - c0R| ≤ 2 * realQuantizeMaxErr pSub := by
          have := abs_realQuantize_sub_le pSub c0R
          linarith
        have hc1_err : |realQuantize pSub c1R - c1R| ≤ 2 * realQuantizeMaxErr pSub := by
          have := abs_realQuantize_sub_le pSub c1R
          linarith
        refine ⟨rfl, rfl, hc0_int_bounds.1, hc0_int_bounds.2, hc1_int_bounds.1, hc1_int_bounds.2,
          by rwa [hc0_re], by rwa [hc1_re], ?_, ?_, ?_⟩
        · intro h_fwd
          have hy_half : y ≤ 1 / 2 := by
            dsimp [y]
            rw [div_le_iff₀ hr_pos_real]
            have : 2 * (u2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h_fwd.le
            linarith
          have hle := realQuantize_mono pSub (c1Coeff_le_c0Coeff_of_le_half α y hα hy0 hy_half)
          rw [realQuantize_eq_realQuantizeInt_div, realQuantize_eq_realQuantizeInt_div,
              div_le_div_iff_of_pos_right hscale_pos] at hle
          exact_mod_cast hle
        · intro h_nyq
          have hy_eq : y = 1 / 2 := by
            dsimp [y]
            rw [div_eq_iff hr_pos_real.ne']
            have : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast h_nyq
            linarith
          have hc01_eq : c0R = c1R := by
            dsimp [c0R, c1R]
            rw [hy_eq]
            linarith [theorem3_nyquist_passband_eq (realErfScaled α) (realErfScaled_zero α)]
          rw [hc01_eq]
        · intro h_bwd
          have hy_half : 1 / 2 ≤ y := by
            dsimp [y]
            rw [le_div_iff₀ hr_pos_real]
            have : (r : ℝ) ≤ 2 * (u2 : ℝ) := by exact_mod_cast h_bwd.le
            linarith
          have hle := realQuantize_mono pSub (c0Coeff_le_c1Coeff_of_ge_half α y hα hy_half hy1)
          rw [realQuantize_eq_realQuantizeInt_div, realQuantize_eq_realQuantizeInt_div,
              div_le_div_iff_of_pos_right hscale_pos] at hle
          exact_mod_cast hle

/-! ### Part 1: Leaf `BaseRadix2FFT` Perturbation Bounds -/

/-- Complex semantics of `computableBaseRadix2FFTCoreWithProgramCost` parameterized by an arbitrary
twiddle table `twiddles : Array (Array (ℤ × ℤ))` (`[MS]` §7). -/
noncomputable def baseRadix2FFTCoreOfTwiddles
    (q_leaf : ℕ) (twiddles : Array (Array (ℤ × ℤ))) : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x, _ => complexQuantize q_leaf (x 0)
  | s + 1, x, u =>
    let Y0 := baseRadix2FFTCoreOfTwiddles q_leaf twiddles s (fun j => x (2 * j)) u
    let Y1 := baseRadix2FFTCoreOfTwiddles q_leaf twiddles s (fun j => x (2 * j + 1)) u
    let ω_q := toScaledComplex q_leaf (read1D (twiddles.getD s #[]) (u % 2 ^ (s + 1)))
    let prod_q := complexQuantize q_leaf (ω_q * Y1)
    complexQuantize q_leaf ((Y0 + prod_q) / 2)

/-- Complex semantics of `computableBaseRadix2FFTWithProgramCost` parameterized by `twiddles`. -/
noncomputable def baseRadix2FFTOfTwiddles
    (p K : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (x : ℕ → ℂ) (u : ℕ) : ℂ :=
  let q_leaf := 2 * p + K + 8
  complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u)

theorem baseRadix2FFTCoreOfTwiddles_mod
    (q_leaf : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (K : ℕ) (x : ℕ → ℂ) (u : ℕ) :
    baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x (u % 2 ^ K) =
      baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u := by
  induction K generalizing x u with
  | zero => rfl
  | succ K ih =>
    dsimp only [baseRadix2FFTCoreOfTwiddles]
    have hdvd : 2 ^ K ∣ 2 ^ (K + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ K)
    have hmod_K : (u % 2 ^ (K + 1)) % 2 ^ K = u % 2 ^ K := Nat.mod_mod_of_dvd u hdvd
    have hY0 :
        baseRadix2FFTCoreOfTwiddles q_leaf twiddles K (fun j => x (2 * j)) (u % 2 ^ (K + 1)) =
          baseRadix2FFTCoreOfTwiddles q_leaf twiddles K (fun j => x (2 * j)) u := by
      rw [← ih (fun j => x (2 * j)) (u % 2 ^ (K + 1)), hmod_K, ih (fun j => x (2 * j)) u]
    have hY1 :
        baseRadix2FFTCoreOfTwiddles q_leaf twiddles K (fun j => x (2 * j + 1)) (u % 2 ^ (K + 1)) =
          baseRadix2FFTCoreOfTwiddles q_leaf twiddles K (fun j => x (2 * j + 1)) u := by
      rw [← ih (fun j => x (2 * j + 1)) (u % 2 ^ (K + 1)), hmod_K, ih (fun j => x (2 * j + 1)) u]
    rw [hY0, hY1, Nat.mod_mod]

theorem toScaledComplex_computableBaseRadix2FFTCoreWithProgramCost_eq_ofTwiddles
    (p_in q_leaf : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (s : ℕ)
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < 2 ^ s, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < 2 ^ s) :
    toScaledComplex q_leaf
      (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).1 u) =
      baseRadix2FFTCoreOfTwiddles q_leaf twiddles s x u := by
  induction s generalizing xArr x u with
  | zero =>
    have hu0 : u = 0 := by simpa using hu
    subst hu0
    dsimp only [computableBaseRadix2FFTCoreWithProgramCost, baseRadix2FFTCoreOfTwiddles,
      costedGRescale, Bind.bind, Pure.pure]
    have hread : read1D #[gRescale p_in q_leaf (read1D xArr 0)] 0 = gRescale p_in q_leaf (read1D xArr 0) := rfl
    rw [hread, toScaledComplex_gRescale_eq, ← hx 0 (by decide)]
  | succ s ih =>
    dsimp only [computableBaseRadix2FFTCoreWithProgramCost, baseRadix2FFTCoreOfTwiddles,
      Bind.bind, Pure.pure]
    rw [BitCostM.ofFnM_fst, read1D_ofFn_of_lt (2 ^ (s + 1)) _ hu]
    dsimp only [costedButterflyAvg, costedGMulScaled]
    rw [toScaledComplex_divRoundPow2_one_eq_complexQuantize_avg,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul]
    have hu_mod : u % 2 ^ s < 2 ^ s := Nat.mod_lt u (pow_pos zero_lt_two s)
    have hxEven : ∀ j < 2 ^ s,
        x (2 * j) = toScaledComplex p_in (read1D (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val))) j) := by
      intro j hj
      rw [read1D_ofFn_of_lt (2 ^ s) _ hj]
      exact hx (2 * j) (by rw [pow_succ']; omega)
    have hxOdd : ∀ j < 2 ^ s,
        x (2 * j + 1) = toScaledComplex p_in (read1D (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val + 1))) j) := by
      intro j hj
      rw [read1D_ofFn_of_lt (2 ^ s) _ hj]
      exact hx (2 * j + 1) (by rw [pow_succ']; omega)
    have hY0 := ih
      (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val)))
      (fun j => x (2 * j)) hxEven (u % 2 ^ s) hu_mod
    have hY1 := ih
      (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val + 1)))
      (fun j => x (2 * j + 1)) hxOdd (u % 2 ^ s) hu_mod
    rw [baseRadix2FFTCoreOfTwiddles_mod] at hY0 hY1
    rw [hY0, hY1, Nat.mod_eq_of_lt hu]

theorem toScaledComplex_computableBaseRadix2FFTWithProgramCost_eq_ofTwiddles
    (p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < 2 ^ K, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < 2 ^ K) :
    toScaledComplex p
      (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u) =
      baseRadix2FFTOfTwiddles p K twiddles x u := by
  unfold computableBaseRadix2FFTWithProgramCost baseRadix2FFTOfTwiddles
  dsimp only [costedGRescale, runSequentialScanCostedSteps, Bind.bind, Pure.pure, BitCostM.tick]
  rw [read1D_runSequentialScanSteps_eq _ (2 ^ K) u hu,
      toScaledComplex_gRescale_eq,
      toScaledComplex_computableBaseRadix2FFTCoreWithProgramCost_eq_ofTwiddles p_in (2 * p + K + 8)
        twiddles K xArr x hx u hu]

/-- **Per-Stage Error Closure for `baseRadix2FFTCoreOfTwiddles` under `2 * complexQuantizeMaxErr q_leaf` Twiddle Perturbation**:
When every stage `s < K` twiddle is within `2 * complexQuantizeMaxErr q_leaf` of `stdChar (u / 2^(s + 1))`,
the `K`-stage radix-2 butterfly error is at most `((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf * M`. -/
theorem norm_baseRadix2FFTCoreOfTwiddles_sub_exact_le
    (q_leaf K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex q_leaf (read1D (twiddles.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤
        2 * complexQuantizeMaxErr q_leaf)
    (hq : ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf ≤ 1)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < 2 ^ K, ‖x k‖ ≤ M) (u : ℕ) :
    ‖baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u - baseRadix2FFTExact K x u‖ ≤
      ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf * M := by
  induction K generalizing x u with
  | zero =>
    dsimp only [baseRadix2FFTCoreOfTwiddles, baseRadix2FFTExact]
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr q_leaf := by
      unfold complexQuantizeMaxErr; positivity
    have h1 : ‖complexQuantize q_leaf (x 0) - x 0‖ ≤ complexQuantizeMaxErr q_leaf :=
      norm_complexQuantize_sub_le q_leaf (x 0)
    push_cast
    nlinarith
  | succ K ih =>
    dsimp only [baseRadix2FFTCoreOfTwiddles, baseRadix2FFTExact]
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr q_leaf := by
      unfold complexQuantizeMaxErr; positivity
    have hq_K : ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf ≤ 1 := by
      have hle : ((K + 1 : ℕ) : ℝ) ≤ ((K + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (K + 1)
      nlinarith
    have htw_K : ∀ s < K, ∀ u' < 2 ^ (s + 1),
        ‖toScaledComplex q_leaf (read1D (twiddles.getD s #[]) u') -
            stdChar ((u' : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤
          2 * complexQuantizeMaxErr q_leaf :=
      fun s hs u' hu' => htw s (Nat.lt_succ_of_lt hs) u' hu'
    have hx0 : ∀ j < 2 ^ K, ‖x (2 * j)‖ ≤ M := by
      intro j hj
      exact hx (2 * j) (by rw [pow_succ']; omega)
    have hx1 : ∀ j < 2 ^ K, ‖x (2 * j + 1)‖ ≤ M := by
      intro j hj
      exact hx (2 * j + 1) (by rw [pow_succ']; omega)
    set Y0 := baseRadix2FFTCoreOfTwiddles q_leaf twiddles K (fun j => x (2 * j)) u
    set Y0_ex := baseRadix2FFTExact K (fun j => x (2 * j)) u
    set Y1 := baseRadix2FFTCoreOfTwiddles q_leaf twiddles K (fun j => x (2 * j + 1)) u
    set Y1_ex := baseRadix2FFTExact K (fun j => x (2 * j + 1)) u
    set ω := stdChar (((u % 2 ^ (K + 1) : ℕ) : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ))
    set ω_q := toScaledComplex q_leaf (read1D (twiddles.getD K #[]) (u % 2 ^ (K + 1)))
    set prod_q := complexQuantize q_leaf (ω_q * Y1)
    set E_K : ℝ := ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf * M
    have hY0_err : ‖Y0 - Y0_ex‖ ≤ E_K := ih htw_K hq_K (fun j => x (2 * j)) hx0 u
    have hY1_err : ‖Y1 - Y1_ex‖ ≤ E_K := ih htw_K hq_K (fun j => x (2 * j + 1)) hx1 u
    have hY1_ex_norm : ‖Y1_ex‖ ≤ M := by
      dsimp [Y1_ex]
      rw [baseRadix2FFTExact_eq_dft1D]
      exact dft1D_norm_le (2 ^ K) (pow_pos zero_lt_two K) (fun j => x (2 * j + 1)) M
        (fun j hj => hx1 j (Finset.mem_range.mp hj)) u
    have hEK_le_M : E_K ≤ M := by
      dsimp [E_K]
      nlinarith
    have hY1_norm : ‖Y1‖ ≤ 2 * M := by
      have htri := norm_add_le (Y1 - Y1_ex) Y1_ex
      rw [sub_add_cancel] at htri
      linarith
    have hprod_err : ‖prod_q - ω * Y1_ex‖ ≤ 5 * complexQuantizeMaxErr q_leaf * M + E_K := by
      have hsplit : prod_q - ω * Y1_ex =
          (prod_q - ω_q * Y1) + (ω_q - ω) * Y1 + ω * (Y1 - Y1_ex) := by ring
      rw [hsplit]
      have h1 : ‖prod_q - ω_q * Y1‖ ≤ complexQuantizeMaxErr q_leaf :=
        norm_complexQuantize_sub_le q_leaf (ω_q * Y1)
      have h2_tw : ‖ω_q - ω‖ ≤ 2 * complexQuantizeMaxErr q_leaf :=
        htw K (Nat.lt_succ_self K) (u % 2 ^ (K + 1)) (Nat.mod_lt u (pow_pos zero_lt_two (K + 1)))
      have h2 : ‖(ω_q - ω) * Y1‖ ≤ (2 * complexQuantizeMaxErr q_leaf) * (2 * M) := by
        rw [norm_mul]
        exact mul_le_mul h2_tw hY1_norm (norm_nonneg _) (by positivity)
      have h3 : ‖ω * (Y1 - Y1_ex)‖ ≤ E_K := by
        rw [norm_mul, norm_stdChar, one_mul]
        exact hY1_err
      have htri1 := norm_add_le ((prod_q - ω_q * Y1) + (ω_q - ω) * Y1) (ω * (Y1 - Y1_ex))
      have htri2 := norm_add_le (prod_q - ω_q * Y1) ((ω_q - ω) * Y1)
      nlinarith
    have havg_err :
        ‖(Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2‖ ≤
          E_K + (2.5 : ℝ) * complexQuantizeMaxErr q_leaf * M := by
      have hsub : (Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2 =
          ((Y0 - Y0_ex) + (prod_q - ω * Y1_ex)) / 2 := by ring
      rw [hsub, norm_div, Complex.norm_ofNat]
      have htri := norm_add_le (Y0 - Y0_ex) (prod_q - ω * Y1_ex)
      linarith
    have hout_round :
        ‖complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0 + prod_q) / 2‖ ≤
          complexQuantizeMaxErr q_leaf :=
      norm_complexQuantize_sub_le q_leaf ((Y0 + prod_q) / 2)
    have htri_out :
        ‖complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0_ex + ω * Y1_ex) / 2‖ ≤
          ‖complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0 + prod_q) / 2‖ +
            ‖(Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2‖ := by
      have hsplit :
          complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0_ex + ω * Y1_ex) / 2 =
            (complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0 + prod_q) / 2) +
              ((Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2) := by ring
      rw [hsplit]
      exact norm_add_le _ _
    have hcast : ((K + 1 + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf * M =
        E_K + 4 * complexQuantizeMaxErr q_leaf * M := by
      dsimp [E_K]
      push_cast
      ring
    rw [hcast]
    nlinarith

theorem baseRadix2FFTOfTwiddles_core_err_factor_le (p K : ℕ) :
    ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr (2 * p + K + 8) ≤
      (0.007 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have h3 := baseRadix2FFTQuantized_core_err_factor_le p K
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr (2 * p + K + 8) := by
    unfold complexQuantizeMaxErr; positivity
  have hK_nonneg : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by positivity
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  linarith

theorem norm_baseRadix2FFTOfTwiddles_sub_dft1D_le
    (p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex (2 * p + K + 8) (read1D (twiddles.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * p + K + 8))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < 2 ^ K, ‖x k‖ ≤ M) (u : ℕ) :
    ‖baseRadix2FFTOfTwiddles p K twiddles x u - dft1D (2 ^ K) x u‖ ≤
      (2 : ℝ) ^ (-(p : ℤ)) * M := by
  unfold baseRadix2FFTOfTwiddles
  dsimp only
  set q_leaf := 2 * p + K + 8
  have hfac := baseRadix2FFTOfTwiddles_core_err_factor_le p K
  have hpow_le_one : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hq_cond : ((K + 1 : ℕ) : ℝ) * 4 * complexQuantizeMaxErr q_leaf ≤ 1 := by
    linarith
  have hcore := norm_baseRadix2FFTCoreOfTwiddles_sub_exact_le q_leaf K twiddles htw hq_cond x M hM1 hx u
  rw [baseRadix2FFTExact_eq_dft1D] at hcore
  have hM_pos : 0 < M := by linarith
  have hcore_le :
      ‖baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u - dft1D (2 ^ K) x u‖ ≤
        (0.007 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    hcore.trans (mul_le_mul_of_nonneg_right hfac hM_pos.le)
  have hout_le :
      ‖complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u) -
        baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u‖ ≤
        (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr p := by unfold complexQuantizeMaxErr; positivity
    have h1 := norm_complexQuantize_sub_le p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u)
    have h2 := (complexQuantizeMaxErr_lt p).le
    nlinarith
  have htri :
      ‖complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u) - dft1D (2 ^ K) x u‖ ≤
        ‖complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u) -
          baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u‖ +
          ‖baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u - dft1D (2 ^ K) x u‖ := by
    have hsplit :
        complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u) - dft1D (2 ^ K) x u =
          (complexQuantize p (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u) -
            baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u) +
            (baseRadix2FFTCoreOfTwiddles q_leaf twiddles K x u - dft1D (2 ^ K) x u) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  have hpow_M_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M := by positivity
  linarith

/-! ### Part 2: Folded Spread Tap Perturbation & Bit-Stride Bounds -/

/-- Complex semantics of the overlap-add signed-Kronecker spread for an arbitrary pre-folded tap
list `gTapFold : List ℤ` (`[MS]` §3.3 & §§6.1–6.2). -/
noncomputable def kroneckerSpreadOfFoldedTaps
    (q m1 t1 r : ℕ) (gTapFold : List ℤ) (x : ℕ → ℂ) (j1 k2 : ℕ) : ℂ :=
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let W_eff := effectiveFilterWidth m1 r
  let reSum : ℤ :=
    ∑ b ∈ Finset.range numBlocks,
      let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b
      let prodRe := polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold
      ∑ i ∈ (Finset.range (2 * W_eff)).filter
          (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
        prodRe.getD i 0
  let imSum : ℤ :=
    ∑ b ∈ Finset.range numBlocks,
      let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b
      let prodIm := polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold
      ∑ i ∈ (Finset.range (2 * W_eff)).filter
          (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
        prodIm.getD i 0
  ⟨(reSum : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q),
   (imSum : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q)⟩

theorem computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps
    (p_in q m1 t1 r : ℕ) (gTapFold : List ℤ) (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 k2 : ℕ)
    (hx : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) (hk2 : k2 < r) :
    let uRaw := read1D (computableSpreadRowContiguousWithCost p_in q m1 r gTapFold xRow).1 k2
    (⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q),
      (uRaw.2 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q)⟩ : ℂ) =
      kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 := by
  dsimp only [computableSpreadRowContiguousWithCost, kroneckerSpreadOfFoldedTaps]
  rw [read1D_ofFn_of_lt r _ hk2]
  dsimp only
  rw [read1D_overlapAddBucketsSinglePass_of_lt r _ _ _ _ k2 hk2,
      read1D_overlapAddBucketsSinglePass_of_lt r _ _ _ _ k2 hk2]
  simp only [emod_toNat_eq_iff_of_lt _ r k2 hk2, sumRangeInt_eq_sum, ← Finset.sum_filter,
    polyMulKroneckerSignedComputable_eq, computableKroneckerBitStride_eq]
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  have hRe_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodReArr :=
          if hb : b < numBlocks then
            let fBlockRe := computableSpreadRowBlockReContiguous p_in q m1 r xRow b
            (polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold).toArray
          else #[]
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          read1D prodReArr i) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b
        let prodRe := polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    simp only [hb, ↓reduceDIte, read1D_toArray_eq_getD,
      computableSpreadRowBlockReContiguous_eq p_in q m1 t1 r xRow x j1 hx b]
  have hIm_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodImArr :=
          if hb : b < numBlocks then
            let fBlockIm := computableSpreadRowBlockImContiguous p_in q m1 r xRow b
            (polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold).toArray
          else #[]
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          read1D prodImArr i) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b
        let prodIm := polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    simp only [hb, ↓reduceDIte, read1D_toArray_eq_getD,
      computableSpreadRowBlockImContiguous_eq p_in q m1 t1 r xRow x j1 hx b]
  simp only [Array.size_ofFn, Array.getElem_ofFn]
  rw [hRe_sum, hIm_sum]

theorem kroneckerSpreadOfFoldedTaps_eq_sum_range
    (q m1 t1 r : ℕ) (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth m1 r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u),
          G s))
    (x : ℕ → ℂ) (j1 k2 : ℕ) (hk2 : k2 < r) :
    kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 =
      ∑ s ∈ Finset.range (2 * m1 + 1),
        quantizeComplex q (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)) *
          (((G s : ℝ) / (2 : ℝ) ^ q : ℝ) : ℂ) := by
  unfold kroneckerSpreadOfFoldedTaps
  dsimp only
  have hRe :
      (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          (polyMulKroneckerSigned
            (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b) gTapFold)
            (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b) gTapFold).getD i 0) =
      ∑ s ∈ Finset.range (2 * m1 + 1),
        quantizeInt q (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)).re * G s := by
    have h1 :
        (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulKroneckerSigned
              (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b) gTapFold)
              (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b) gTapFold).getD i 0) =
        ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulInt (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b) gTapFold).getD i 0 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [polyMulKroneckerSigned_kroneckerBitStride_eq]
    rw [h1, hFold]
    exact overlapAdd_folded_polyMulInt_eq m1 r k2 hk2
      (fun j2 => quantizeInt q (x (j1 + t1 * j2)).re) G
  have hIm :
      (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          (polyMulKroneckerSigned
            (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b) gTapFold)
            (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b) gTapFold).getD i 0) =
      ∑ s ∈ Finset.range (2 * m1 + 1),
        quantizeInt q (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)).im * G s := by
    have h1 :
        (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulKroneckerSigned
              (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b) gTapFold)
              (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b) gTapFold).getD i 0) =
        ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulInt (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b) gTapFold).getD i 0 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [polyMulKroneckerSigned_kroneckerBitStride_eq]
    rw [h1, hFold]
    exact overlapAdd_folded_polyMulInt_eq m1 r k2 hk2
      (fun j2 => quantizeInt q (x (j1 + t1 * j2)).im) G
  rw [hRe, hIm]
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp [quantizeComplex, quantizeReal]
    ring
  · simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp [quantizeComplex, quantizeReal]
    ring

/-- Single-tap quantized product perturbation bound under `1`-ULP tap approximation (`|w_q - w| ≤ 2^(-q)`):
for `‖z‖ ≤ M`, `|w| ≤ 1`, and `1 ≤ M`, `‖quantizeComplex q z * (w_q : ℂ) - z * (w : ℂ)‖ ≤ 5 * 2^(-q) * M`. -/
theorem norm_quantizeComplex_mul_approxReal_sub_le
    (q : ℕ) (z : ℂ) (w_q w M : ℝ) (hM1 : 1 ≤ M) (hz : ‖z‖ ≤ M) (hw : |w| ≤ 1)
    (hw_q : |w_q - w| ≤ (2 : ℝ) ^ (-(q : ℤ))) :
    ‖quantizeComplex q z * (w_q : ℂ) - z * (w : ℂ)‖ ≤
      5 * (2 : ℝ) ^ (-(q : ℤ)) * M := by
  have hpow_le_one : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-(q : ℤ)) := zpow_nonneg (by norm_num) _
  have hz_err : ‖quantizeComplex q z - z‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
    norm_quantizeComplex_sub_le q z
  have hw_err : ‖(w_q : ℂ) - (w : ℂ)‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hw_q
  have hqw_norm : ‖(w_q : ℂ)‖ ≤ 2 := by
    have htri := norm_add_le ((w_q : ℂ) - (w : ℂ)) (w : ℂ)
    have hw_norm : ‖(w : ℂ)‖ = |w| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [sub_add_cancel, hw_norm] at htri
    linarith
  have hsplit :
      quantizeComplex q z * (w_q : ℂ) - z * (w : ℂ) =
        (quantizeComplex q z - z) * (w_q : ℂ) +
          z * ((w_q : ℂ) - (w : ℂ)) := by ring
  rw [hsplit]
  have htri := norm_add_le
    ((quantizeComplex q z - z) * (w_q : ℂ))
    (z * ((w_q : ℂ) - (w : ℂ)))
  rw [norm_mul, norm_mul] at htri
  have h1 : ‖quantizeComplex q z - z‖ * ‖(w_q : ℂ)‖ ≤
      2 * (2 : ℝ) ^ (-(q : ℤ)) * M := by
    calc ‖quantizeComplex q z - z‖ * ‖(w_q : ℂ)‖
        ≤ (2 : ℝ) ^ (-(q : ℤ)) * 2 :=
          mul_le_mul hz_err hqw_norm (norm_nonneg _) hpow_nonneg
      _ = 2 * (2 : ℝ) ^ (-(q : ℤ)) * 1 := by ring
      _ ≤ 2 * (2 : ℝ) ^ (-(q : ℤ)) * M :=
          mul_le_mul_of_nonneg_left hM1 (by positivity)
  have h2 : ‖z‖ * ‖(w_q : ℂ) - (w : ℂ)‖ ≤
      1 * (2 : ℝ) ^ (-(q : ℤ)) * M := by
    calc ‖z‖ * ‖(w_q : ℂ) - (w : ℂ)‖
        ≤ M * (2 : ℝ) ^ (-(q : ℤ)) :=
          mul_le_mul hz hw_err (norm_nonneg _) (by linarith)
      _ = 1 * (2 : ℝ) ^ (-(q : ℤ)) * M := by ring
  have hpowM : 0 ≤ (2 : ℝ) ^ (-(q : ℤ)) * M := by positivity
  linarith

theorem norm_kroneckerSpreadOfFoldedTaps_sub_windowed_le
    (α : ℝ) (q m1 t1 r : ℕ) (_ht1 : 0 < t1) (hr : 0 < r)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth m1 r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u),
          G s))
    (hG_err : ∀ s < 2 * m1 + 1,
      |((G s : ℝ) / (2 : ℝ) ^ q) -
          sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
        (2 : ℝ) ^ (-(q : ℤ)))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M) :
    ‖kroneckerSpreadOfFoldedTaps q m1 t1 r gTapFold x j1 k2 -
        windowedSincGaussianSpreadArray α m1 t1 r x j1 k2‖ ≤
      ((2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ))) * M := by
  rw [kroneckerSpreadOfFoldedTaps_eq_sum_range q m1 t1 r gTapFold G hFold x j1 k2 hk2]
  unfold windowedSincGaussianSpreadArray
  rw [sum_Icc_neg_eq_sum_range_two_mul_add_one m1, ← Finset.sum_sub_distrib]
  dsimp only [sincGaussianSpreadTerm]
  simp only [Int.cast_sub]
  calc ‖∑ s ∈ Finset.range (2 * m1 + 1),
          (quantizeComplex q (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)) *
            (((G s : ℝ) / (2 : ℝ) ^ q : ℝ) : ℂ) -
           x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) *
            (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)) : ℂ))‖
      ≤ ∑ s ∈ Finset.range (2 * m1 + 1),
          ‖quantizeComplex q (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)) *
            (((G s : ℝ) / (2 : ℝ) ^ q : ℝ) : ℂ) -
           x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) *
            (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ Finset.range (2 * m1 + 1), (5 * (2 : ℝ) ^ (-(q : ℤ)) * M) := by
        refine Finset.sum_le_sum fun s hs_mem => ?_
        have hs_lt : s < 2 * m1 + 1 := Finset.mem_range.mp hs_mem
        have hidx_lt : j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat < t1 * r := by
          have hmod_lt : (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat < r := by
            have hr_int : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
            have h1 := Int.emod_lt_of_pos ((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) hr_int
            have h2 := Int.emod_nonneg ((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) hr_int.ne'
            omega
          have hle : (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat + 1 ≤ r := hmod_lt
          calc j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat
              < t1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat :=
                Nat.add_lt_add_right hj1 _
            _ = t1 * ((((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
        exact norm_quantizeComplex_mul_approxReal_sub_le q
          (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat))
          ((G s : ℝ) / (2 : ℝ) ^ q)
          (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
          M hM1 (hx _ hidx_lt)
          (abs_sincGaussian_le_one α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
          (hG_err s hs_lt)
    _ = ((2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ))) * M := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring

theorem norm_kroneckerSpreadOfFoldedTaps_sub_lt
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
          G s))
    (hG_err : ∀ s < 2 * (2 * pChild p K) + 1,
      |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
          sincGaussian (alphaSchedule (pWork p K))
            (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
        (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M) :
    ‖kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2 -
        sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2‖ <
      (0.5 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  have hM_pos : 0 < M := by linarith
  have hP12 : 12 ≤ pChild p K := by unfold pChild pWork; omega
  have hle := norm_kroneckerSpreadOfFoldedTaps_sub_windowed_le
    (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r ht1 hr
    j1 k2 hj1 hk2 gTapFold G hFold hG_err x M hM1 hx
  have hlt := five_mul_four_mul_add_one_zpow_lt (pChild p K) hP12
  have hcast : (2 * ((2 * pChild p K : ℕ) : ℝ) + 1) = 2 * (2 * (pChild p K : ℝ)) + 1 := by
    push_cast; ring
  rw [hcast] at hle
  have hB2 :
      ‖kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2 -
          windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2‖ <
        (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M :=
    hle.trans_lt (mul_lt_mul_of_pos_right hlt hM_pos)
  have hB1 := norm_windowedSincGaussianSpreadArray_sub_lt p K t1 r ht1 hr x M hM_pos hx j1 k2 hj1
  have hsplit :
      kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2 -
        sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2 =
      (kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2 -
        windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2) +
      (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2 -
        sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2) := by ring
  rw [hsplit]
  have htri := norm_add_le
    (kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2 -
      windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2)
    (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
  linarith

theorem norm_dft2D_kroneckerSpreadOfFoldedTaps_sub_le
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (filterTaps : Array (List ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u1 u2 : ℕ) :
    ‖dft2D t1 r (fun j1 k2 => kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r (filterTaps.getD j1 []) x j1 k2) u1 u2 -
        dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖ ≤
      (0.5 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  rw [← dft2D_sub]
  refine dft2D_norm_le t1 r ht1 hr _ _ (fun j1 hj1 k2 hk2 => ?_) u1 u2
  rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
  exact (norm_kroneckerSpreadOfFoldedTaps_sub_lt p K t1 r ht1 hr j1 k2 hj1 hk2 _ G hFold hG_err x M hM1 hx).le

theorem norm_kroneckerSpreadOfFoldedTaps_le
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
          G s))
    (hG_err : ∀ s < 2 * (2 * pChild p K) + 1,
      |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
          sincGaussian (alphaSchedule (pWork p K))
            (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
        (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)))
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M) :
    ‖kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2‖ ≤
      ((r : ℝ) + (0.5 : ℝ)) * M := by
  have hα : 0 < alphaSchedule (pWork p K) := alphaSchedule_pos (pWork p K) (by unfold pWork; omega)
  have hdiff := (norm_kroneckerSpreadOfFoldedTaps_sub_lt
    p K t1 r ht1 hr j1 k2 hj1 hk2 gTapFold G hFold hG_err x M hM1 hx).le
  have hinf := norm_sincGaussianSpreadArray_le
    (alphaSchedule (pWork p K)) hα t1 r hr x M hx j1 k2 hj1 hk2
  have hpow_le : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have htri := norm_add_le
    (kroneckerSpreadOfFoldedTaps (2 * pChild p K) (2 * pChild p K) t1 r gTapFold x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
    (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
  rw [sub_add_cancel] at htri
  nlinarith

theorem listMaxNatAbs_of_folded_taps_le
    (q m1 r : ℕ) (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth m1 r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u),
          G s))
    (hG_abs : ∀ s < 2 * m1 + 1, (G s).natAbs ≤ 2 ^ q + 1) :
    listMaxNatAbs gTapFold ≤ (2 * m1 + 1) * (2 ^ q + 1) := by
  subst hFold
  refine listMaxNatAbs_le _ _ fun c hc => ?_
  rcases List.mem_map.mp hc with ⟨u, _, rfl⟩
  have hsum := natAbs_sum_le
    ((Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u))
    G (2 ^ q + 1)
    (fun s hs => hG_abs s (Finset.mem_range.mp (Finset.mem_of_mem_filter s hs)))
  have hcard :
      ((Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u)).card ≤
        2 * m1 + 1 := by
    calc ((Finset.range (2 * m1 + 1)).filter _).card
        ≤ (Finset.range (2 * m1 + 1)).card := Finset.card_filter_le _ _
      _ = 2 * m1 + 1 := Finset.card_range _
  exact hsum.trans (Nat.mul_le_mul_right _ hcard)

theorem kroneckerBitStride_kroneckerSpreadRowBlock_of_folded_le
    (p K t1 r : ℕ) (hp : 8 ≤ p) (_hK : 2 ≤ K) (_hr : 0 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
          G s))
    (hG_abs : ∀ s < 2 * (2 * pChild p K) + 1, (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K))
    (j1 b : ℕ) (hj1 : j1 < t1) :
    kroneckerBitStride
      (kroneckerSpreadRowBlockRe (2 * pChild p K) (2 * pChild p K) t1 r x j1 b) gTapFold ≤
        6 * pChild p K ∧
    kroneckerBitStride
      (kroneckerSpreadRowBlockIm (2 * pChild p K) (2 * pChild p K) t1 r x j1 b) gTapFold ≤
        6 * pChild p K := by
  set p' := pChild p K
  have hp' : 17 ≤ p' := by unfold p' pChild pWork; omega
  have hW : effectiveFilterWidth (2 * p') r ≤ 4 * p' + 1 := by
    have h1 := effectiveFilterWidth_le_full (2 * p') r
    omega
  have hx' : ∀ k < t1 * r, ‖x k‖ ≤ ((2 ^ p' : ℕ) : ℝ) := by
    intro k hk; simpa using hx k hk
  have hpow : 2 ^ p' * 2 ^ (2 * p') = 2 ^ (3 * p') := by
    rw [← pow_add]; congr 1; omega
  have hfRe_max :
      listMaxNatAbs (kroneckerSpreadRowBlockRe (2 * p') (2 * p') t1 r x j1 b) ≤
        2 ^ (3 * p') + 1 := by
    have h1 := listMaxNatAbs_kroneckerSpreadRowBlockRe_le (2 * p') (2 * p') t1 r (2 ^ p') x hx' j1 b hj1
    omega
  have hfIm_max :
      listMaxNatAbs (kroneckerSpreadRowBlockIm (2 * p') (2 * p') t1 r x j1 b) ≤
        2 ^ (3 * p') + 1 := by
    have h1 := listMaxNatAbs_kroneckerSpreadRowBlockIm_le (2 * p') (2 * p') t1 r (2 ^ p') x hx' j1 b hj1
    omega
  have hg_max : listMaxNatAbs gTapFold ≤ (4 * p' + 1) * (2 ^ (2 * p') + 1) := by
    have h1 := listMaxNatAbs_of_folded_taps_le (2 * p') (2 * p') r gTapFold G hFold hG_abs
    have heq : 2 * (2 * p') + 1 = 4 * p' + 1 := by omega
    rwa [heq] at h1
  have hg_len : gTapFold.length ≤ 4 * p' + 1 := by
    rw [hFold, List.length_map, List.length_range]
    exact hW
  exact ⟨kroneckerBitStride_le_six_mul_of_bounds p' hp' _ _
           (by rw [length_kroneckerSpreadRowBlockRe]; exact hW) hg_len hfRe_max hg_max,
         kroneckerBitStride_le_six_mul_of_bounds p' hp' _ _
           (by rw [length_kroneckerSpreadRowBlockIm]; exact hW) hg_len hfIm_max hg_max⟩

/-! ### Part 3: Passband Coefficient Conditioning under `2 * realQuantizeMaxErr` Perturbation -/

/-- **Perturbation-Tolerant Passband Coefficient Conditioning Bound (`faithful_coeff_ratio_pow_le`, `[MS]` §3.3 & §5.1)**:
For any `p, K, t1 : ℕ` with `t1 ≤ 2 ^ K`, any passband coefficients `a, b ∈ [0, 1]` satisfying
`0.49999999 ≤ a`, `b ≤ a`, and `(b / a) ^ t1 ≤ 0.15`, and any faithful approximations `a_q, b_q : ℝ`
satisfying `0 ≤ b_q`, `b_q ≤ a_q`, `a_q ≤ 1`, `|a_q - a| ≤ 2 * realQuantizeMaxErr (2 * pChild p K)`,
and `|b_q - b| ≤ 2 * realQuantizeMaxErr (2 * pChild p K)`, we have:
`0.4999 ≤ a_q`, `a_q ≤ 1`, `0 ≤ b_q`, `b_q ≤ a_q`, and `(b_q / a_q) ^ t1 ≤ 0.1501`. -/
theorem faithful_coeff_ratio_pow_le
    (p K t1 : ℕ) (ht1_le : t1 ≤ 2 ^ K)
    (a b a_q b_q : ℝ)
    (ha_gt : (0.49999999 : ℝ) ≤ a) (_ha_le : a ≤ 1)
    (hb_nonneg : 0 ≤ b) (hba : b ≤ a)
    (hratio : (b / a) ^ t1 ≤ (0.15 : ℝ))
    (hb_q_nonneg : 0 ≤ b_q) (hba_q : b_q ≤ a_q) (ha_q_le1 : a_q ≤ 1)
    (h_err_a : |a_q - a| ≤ 2 * realQuantizeMaxErr (2 * pChild p K))
    (h_err_b : |b_q - b| ≤ 2 * realQuantizeMaxErr (2 * pChild p K)) :
    (0.4999 : ℝ) ≤ a_q ∧ a_q ≤ 1 ∧ 0 ≤ b_q ∧ b_q ≤ a_q ∧
      (b_q / a_q) ^ t1 ≤ (0.1501 : ℝ) := by
  set q := 2 * pChild p K
  have hP_ge : K + 12 ≤ pChild p K := by unfold pChild pWork; omega
  have hq_ge : K + 24 ≤ q := by dsimp [q]; omega
  have h_qerr_small : realQuantizeMaxErr q ≤ (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by
    rw [realQuantizeMaxErr_eq]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h_a_q_ge : (0.4999 : ℝ) ≤ a_q := by
    have h1 := (abs_le.mp h_err_a).1
    linarith
  refine ⟨h_a_q_ge, ha_q_le1, hb_q_nonneg, hba_q, ?_⟩
  have ha_pos : 0 < a := by linarith
  have ha_q_pos : 0 < a_q := by linarith
  have hdiv_q_abs : |b_q / a_q| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hb_q_nonneg ha_q_pos.le)]
    exact (div_le_one ha_q_pos).mpr hba_q
  have hdiv_abs : |b / a| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hb_nonneg ha_pos.le)]
    exact (div_le_one ha_pos).mpr hba
  have hdiv_diff : |b_q / a_q - b / a| ≤ 10 * realQuantizeMaxErr q := by
    have h1 := abs_div_sub_div_le a b a_q b_q (0.4999 : ℝ)
      (by norm_num) (by linarith) h_a_q_ge hb_nonneg hba
    have h2 : (|b_q - b| + |a_q - a|) / (0.4999 : ℝ) ≤ (4 * realQuantizeMaxErr q) / (0.4999 : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have hq_nonneg : 0 ≤ realQuantizeMaxErr q := by
      rw [realQuantizeMaxErr_eq]; positivity
    have h3 : (4 * realQuantizeMaxErr q) / (0.4999 : ℝ) ≤ 10 * realQuantizeMaxErr q := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.4999)]
      linarith
    linarith
  have hpow_diff := abs_pow_sub_pow_le (b_q / a_q) (b / a) hdiv_q_abs hdiv_abs t1
  have ht1_real : (t1 : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast ht1_le
  have ht1_err : (t1 : ℝ) * (10 * realQuantizeMaxErr q) ≤ (0.0001 : ℝ) := by
    rw [realQuantizeMaxErr_eq]
    have hzpow_q :
        (2 : ℝ) ^ (-(q : ℤ)) ≤ (2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hcancel : (2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) = 1 := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
    calc (t1 : ℝ) * (10 * ((0.125 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))))
        ≤ (2 : ℝ) ^ (K : ℤ) * (10 * ((0.125 : ℝ) * ((2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(K : ℤ))))) :=
          mul_le_mul ht1_real
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzpow_q (by norm_num)) (by norm_num))
            (by positivity) (by positivity)
      _ = (10 * (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ)) * ((2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ))) := by ring
      _ = 10 * (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by rw [hcancel, mul_one]
      _ ≤ (0.0001 : ℝ) := by norm_num
  have hpow_sub : (b_q / a_q) ^ t1 - (b / a) ^ t1 ≤ (t1 : ℝ) * |b_q / a_q - b / a| :=
    (le_abs_self _).trans hpow_diff
  have hmul_le : (t1 : ℝ) * |b_q / a_q - b / a| ≤ (t1 : ℝ) * (10 * realQuantizeMaxErr q) :=
    mul_le_mul_of_nonneg_left hdiv_diff (Nat.cast_nonneg t1)
  linarith

/-! ### Part 4: Master Inductive Error, Correctness, and Program-Cost Closure under `TablesFaithful` -/

/-- For any `p, K, r : ℕ` with `r ≤ 2 ^ K`, since `pChild p K = p + 2 * K + 12 ≥ K + 12`,
`2 * complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1) ≤ 0.01 * 2^{-pChild p K}`. -/
theorem two_mul_complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow
    (p K r : ℕ) (hr : r ≤ 2 ^ K) :
    2 * complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1) ≤
      (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
  have h1 : complexQuantizeMaxErr (2 * pChild p K) ≤
      (0.354 : ℝ) * (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) :=
    (complexQuantizeMaxErr_lt (2 * pChild p K)).le
  have hP_ge : K + 12 ≤ pChild p K := by unfold pChild pWork; omega
  have hr_real : (r : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]; exact_mod_cast hr
  have hpowK_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]; exact_mod_cast (Nat.one_le_two_pow (n := K))
  have hr1_le : (r : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ (K : ℤ) := by linarith
  have hzpow :
      (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) ≤
        (2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
    push_cast; omega
  have hcancel : (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (K : ℤ) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  calc 2 * complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1)
      ≤ (2 * ((0.354 : ℝ) * (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)))) * (2 * (2 : ℝ) ^ (K : ℤ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hr1_le (by positivity) (by positivity)
    _ ≤ (2 * ((0.354 : ℝ) * ((2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ))))) *
          (2 * (2 : ℝ) ^ (K : ℤ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzpow (by norm_num)) (by norm_num))
          (by positivity)
    _ = (2 * (0.354 : ℝ) * 2 * (2 : ℝ) ^ (-12 : ℤ)) *
          ((2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (K : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by ring
    _ = (2 * (0.354 : ℝ) * 2 * (2 : ℝ) ^ (-12 : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
        rw [hcancel, mul_one]
    _ ≤ (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- Norm bound for a quantized twist multiplication with any faithful twiddle approximation `tw`
at `pSub = 2 * pChild p K`:
when `r ≤ 2 ^ K`, `1 ≤ M`, `c ≤ 1`, `‖tw - zetaRoot r θ‖ ≤ 2 * complexQuantizeMaxErr pSub`,
and `‖w‖ ≤ ((r : ℝ) + c) * M`,
`‖complexQuantize pSub (tw * w)‖ ≤ ((r : ℝ) + c + 0.02) * M`. -/
theorem norm_complexQuantize_approx_zetaRoot_mul_le
    (p K r : ℕ) (hr_le : r ≤ 2 ^ K) (θ : ℝ) (tw w : ℂ) (c M : ℝ)
    (hc1 : c ≤ 1) (hM1 : 1 ≤ M)
    (htw_err : ‖tw - zetaRoot r θ‖ ≤ 2 * complexQuantizeMaxErr (2 * pChild p K))
    (hw : ‖w‖ ≤ ((r : ℝ) + c) * M) :
    let pSub := 2 * pChild p K
    ‖complexQuantize pSub (tw * w)‖ ≤ ((r : ℝ) + c + (0.02 : ℝ)) * M := by
  dsimp only
  set pSub := 2 * pChild p K
  set ε := complexQuantizeMaxErr pSub
  have hε_nonneg : 0 ≤ ε := by dsimp [ε]; unfold complexQuantizeMaxErr; positivity
  have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hε_le : ε ≤ (0.01 : ℝ) := by
    have h1 := (complexQuantizeMaxErr_two_mul_pChild_lt p K).1.le
    linarith
  have h2ε_r : 2 * ε * ((r : ℝ) + 1) ≤ (0.01 : ℝ) := by
    have h1 := two_mul_complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K r hr_le
    linarith
  have htw : ‖tw‖ ≤ 1 + 2 * ε := by
    have htri := norm_add_le (tw - zetaRoot r θ) (zetaRoot r θ)
    rw [sub_add_cancel, norm_zetaRoot] at htri
    linarith
  have hmul : ‖tw * w‖ ≤ (1 + 2 * ε) * (((r : ℝ) + c) * M) := by
    rw [norm_mul]
    exact mul_le_mul htw hw (norm_nonneg _) (by linarith)
  have hquant := norm_complexQuantize_le pSub (tw * w)
  have h2ε_rc : 2 * ε * ((r : ℝ) + c) ≤ (0.01 : ℝ) := by
    calc 2 * ε * ((r : ℝ) + c)
        ≤ 2 * ε * ((r : ℝ) + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (0.01 : ℝ) := h2ε_r
  nlinarith

/-- **Recursive Child-Input Norm Invariant under Faithful Tables (`norm_qPost_of_faithful_le_two_pow_pChild`, `[MS]` §§3.2, 6.3 (Lemma 6.5))**:
At any valid internal node `.step p K t1 r c1 v1Of child` (`0 < t1`, `0 < r`, `t1 * r = 2 ^ K`),
if `filterTaps`, `preTwiddles`, and `postTwiddles` satisfy the `TablesFaithful` conditions and
`∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p`, then every post-twisted Synthetic-FFT child input `qPost v1`
satisfies `∀ k2 < r, ‖qPost v1 k2‖ ≤ ((r : ℝ) + 1) * (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (pChild p K)`. -/
theorem norm_qPost_of_faithful_le_two_pow_pChild
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r) (hsize : t1 * r = 2 ^ K)
    (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hPost : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    let pSub := 2 * pChild p K
    let U : ℕ → ℕ → ℂ := fun j1 m =>
      kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 m
    let P : ℕ → ℕ → ℂ := fun j1 m =>
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles m) * U j1 m)
    let Q : ℕ → ℕ → ℂ := fun v m =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
    let qPost : ℕ → ℕ → ℂ := fun v m =>
      complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles m) * Q v m)
    ‖qPost v1 k2‖ ≤ (2 : ℝ) ^ (pChild p K) := by
  dsimp only
  set pSub := 2 * pChild p K
  set M : ℝ := (2 : ℝ) ^ p
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr_le : r ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_left r ht1
  let U : ℕ → ℕ → ℂ := fun j1 m =>
    kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 m
  let P : ℕ → ℕ → ℂ := fun j1 m =>
    complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles m) * U j1 m)
  let Q : ℕ → ℕ → ℂ := fun v m =>
    complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v m)
  have hP : ∀ j1 < t1, ∀ m < r, ‖P j1 m‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M := by
    intro j1 hj1 m hm
    rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
    have hU := norm_kroneckerSpreadOfFoldedTaps_le p K t1 r ht1 hr j1 m hj1 hm
      (filterTaps.getD j1 []) G hFold hG_err x M hM1 hx
    have h := norm_complexQuantize_approx_zetaRoot_mul_le p K r hr_le (m : ℝ)
      (toScaledComplex pSub (read1D preTwiddles m)) (U j1 m) (0.5 : ℝ) M
      (by norm_num) hM1 (hPre m hm) hU
    dsimp only at h
    linarith
  have hQ : ‖Q v1 k2‖ ≤ ((r : ℝ) + (0.53 : ℝ)) * M := by
    obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    set w := syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2
    have hsyn : ‖w‖ ≤ ((r : ℝ) + (0.52 : ℝ)) * M + (Nat.log2 t1 : ℝ) * complexQuantizeMaxErr pSub :=
      norm_syntheticFFTRadix2Quantized_le pSub r (Nat.log2 t1) (r / t1) hr P
        (((r : ℝ) + (0.52 : ℝ)) * M) (fun j1 hj1 m hm => hP j1 (ht1_pow ▸ hj1) m hm) v1 k2 hk2
    have hquant := norm_complexQuantize_le pSub w
    have hpow_le1 : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hlog_err : complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤ (0.01 : ℝ) := by
      have h1 := complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
      nlinarith
    dsimp only [Q]
    nlinarith
  have hqPost :
      ‖complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)‖ ≤
        ((r : ℝ) + 1) * M := by
    have h := norm_complexQuantize_approx_zetaRoot_mul_le p K r hr_le (-(k2 : ℝ))
      (toScaledComplex pSub (read1D postTwiddles k2)) (Q v1 k2) (0.53 : ℝ) M
      (by norm_num) hM1 (hPost k2 hk2) hQ
    dsimp only at h
    linarith
  have hr1_nat : r + 1 ≤ 2 ^ (2 * K + 12) := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : r + 1 ≤ 2 ^ (K + 1) := by rw [pow_succ]; omega
    exact h2.trans (Nat.pow_le_pow_right zero_lt_two (by omega))
  have hr1_real : (r : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * K + 12) := by exact_mod_cast hr1_nat
  calc ‖complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)‖
      ≤ ((r : ℝ) + 1) * M := hqPost
    _ ≤ (2 : ℝ) ^ (2 * K + 12) * (2 : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right hr1_real (by positivity)
    _ = (2 : ℝ) ^ (p + 2 * K + 12) := by rw [← pow_add]; congr 1; ring
    _ = (2 : ℝ) ^ (pChild p K) := by rw [pChild_eq_additive]

/-- Row-level operand bit-cost bound for `computableSpreadRowContiguousWithCost` under any folded
tap list `gTapFold` satisfying the `TablesFaithful` magnitude bound (`|G s| ≤ 2^(2 * pChild p K) + 1`). -/
theorem computableSpreadRowContiguousWithCost_of_folded_snd_le
    (p_in p K t1 r : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (hr : 0 < r)
    (gTapFold : List ℤ) (G : ℕ → ℤ)
    (hFold : gTapFold =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
          G s))
    (hG_abs : ∀ s < 2 * (2 * pChild p K) + 1, (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1)
    (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 : ℕ) (hj1 : j1 < t1)
    (hxRow : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i))
    (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K)) :
    let p' := pChild p K
    let pSub := 2 * p'
    let W_eff := effectiveFilterWidth pSub r
    (computableSpreadRowContiguousWithCost p_in pSub pSub r gTapFold xRow).2 ≤
      kroneckerSpreadNumBlocks pSub r *
        (2 * mulBitCost (W_eff * (6 * p')) + 4 * W_eff * addBitCost (6 * p')) := by
  dsimp only
  set p' := pChild p K
  set pSub := 2 * p'
  set W_eff := effectiveFilterWidth pSub r
  set numBlocks := kroneckerSpreadNumBlocks pSub r
  unfold computableSpreadRowContiguousWithCost
  dsimp only
  refine sumArrayCosts_ofFn_le_const numBlocks _
    (2 * mulBitCost (W_eff * (6 * p')) + 4 * W_eff * addBitCost (6 * p'))
    (fun b _ => ?_)
  dsimp only
  simp only [computableMulBitCost_eq, computableKroneckerBitStride_eq,
    computableSpreadRowBlockReContiguous_eq p_in pSub pSub t1 r xRow x j1 hxRow b,
    computableSpreadRowBlockImContiguous_eq p_in pSub pSub t1 r xRow x j1 hxRow b]
  obtain ⟨hSRe, hSIm⟩ := kroneckerBitStride_kroneckerSpreadRowBlock_of_folded_le
    p K t1 r hp hK hr gTapFold G hFold hG_abs x hx j1 b hj1
  have hmulRe :
      mulBitCost
        ((kroneckerSpreadRowBlockRe pSub pSub t1 r x j1 b).length *
          kroneckerBitStride (kroneckerSpreadRowBlockRe pSub pSub t1 r x j1 b) gTapFold) ≤
        mulBitCost (W_eff * (6 * p')) := by
    rw [length_kroneckerSpreadRowBlockRe]
    exact mulBitCost_mono (Nat.mul_le_mul_left W_eff hSRe)
  have hmulIm :
      mulBitCost
        ((kroneckerSpreadRowBlockIm pSub pSub t1 r x j1 b).length *
          kroneckerBitStride (kroneckerSpreadRowBlockIm pSub pSub t1 r x j1 b) gTapFold) ≤
        mulBitCost (W_eff * (6 * p')) := by
    rw [length_kroneckerSpreadRowBlockIm]
    exact mulBitCost_mono (Nat.mul_le_mul_left W_eff hSIm)
  have haddRe :
      2 * W_eff *
        addBitCost (kroneckerBitStride (kroneckerSpreadRowBlockRe pSub pSub t1 r x j1 b) gTapFold) ≤
        2 * W_eff * addBitCost (6 * p') :=
    Nat.mul_le_mul_left (2 * W_eff) (addBitCost_mono hSRe)
  have haddIm :
      2 * W_eff *
        addBitCost (kroneckerBitStride (kroneckerSpreadRowBlockIm pSub pSub t1 r x j1 b) gTapFold) ≤
        2 * W_eff * addBitCost (6 * p') :=
    Nat.mul_le_mul_left (2 * W_eff) (addBitCost_mono hSIm)
  dsimp only [W_eff] at hmulRe hmulIm haddRe haddIm ⊢
  linarith

/-- Functional mathematical specification of `computablePaperFastDFT` parameterized by an
arbitrary precomputed table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`sincGaussianFastDFTOfTables`). -/
noncomputable def sincGaussianFastDFTOfTables :
    ComputablePaperFastDFTSpec → (ℕ → ℂ) → ℕ → ℂ
  | .basePow2 p K twiddles, x, u =>
    baseRadix2FFTOfTwiddles p K twiddles x u
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, x, u =>
    let U : ℕ → ℕ → ℂ := fun j1 k2 =>
      kroneckerSpreadOfFoldedTaps pSub m1 t1 r (filterTaps.getD j1 []) x j1 k2
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTOfTables child (qPost v1) u2
    let v1Of : ℕ → ℕ → ℕ := fun u2 u1 =>
      oddStrideInvPow2 (Nat.log2 t1) u2 u1
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
    let u2 := u % r
    let u1_tilde := u / r
    let c0_q : ℂ := toScaledComplex pSub (read1D c0Table u2)
    let c1_q : ℂ := toScaledComplex pSub (read1D c1Table u2)
    let alt_q : ℂ := complexQuantize pSub (nyquistAltSum t1 r x)
    let z_sub : ℂ :=
      if 2 * u2 < r then
        solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde
      else
        solveBidiagonalBwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
    complexQuantize p z_sub

set_option backward.dsimp.instances true in
/-- **Semantic Equivalence of `computablePaperFastDFT` and `sincGaussianFastDFTOfTables` under `TablesFaithful`
(`toScaledComplex_computablePaperFastDFT_eq_ofTables`, `[MS]` §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) and any faithful
table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`hfaith : TablesFaithful cSpec spec`),
dequantizing the pure-integer output of `computablePaperFastDFT p_in cSpec xArr` equals
`sincGaussianFastDFTOfTables cSpec x u`. -/
theorem toScaledComplex_computablePaperFastDFT_eq_ofTables
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < spec.size) :
    toScaledComplex spec.p
      (read1D (computablePaperFastDFT p_in cSpec xArr) u) =
      sincGaussianFastDFTOfTables cSpec x u := by
  unfold computablePaperFastDFT
  induction hvalid generalizing cSpec p_in xArr x u with
  | base p R =>
    cases hfaith with
    | @base p K twiddles hp hK_le htw =>
      dsimp only [computablePaperFastDFTWithProgramCost, sincGaussianFastDFTOfTables,
        QuantizedFastDFTSpec.p]
      dsimp only [QuantizedFastDFTSpec.size] at hx hu
      exact toScaledComplex_computableBaseRadix2FFTWithProgramCost_eq_ofTwiddles
        p_in p K twiddles xArr x hx u hu
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hfaith with
    | @step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      dsimp only [sincGaussianFastDFTOfTables, QuantizedFastDFTSpec.p]
      dsimp only [QuantizedFastDFTSpec.size] at hx hu
      obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
      obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
      dsimp only [computablePaperFastDFTWithProgramCost, runScan2DCostedWithSteps,
        runSequentialScanCostedSteps, costedGPreTwistU, costedGRescale, costedGMulScaled]
      set pSub := 2 * pChild p K
      set p' := pSub / 2
      set m_t1 := natLog2Fuel t1 t1
      set m_r := natLog2Fuel r r
      have hm_t1 : m_t1 = Nat.log2 t1 := natLog2Fuel_self t1
      have hm_r : m_r = Nat.log2 r := natLog2Fuel_self r
      set xRoutedRes := runMultiTapeTransposeFullSteps m_t1 r (read1D xArr)
      set xRows_res :=
        runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
      set xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
      have hxRow_eq : ∀ j1 < t1, ∀ i < r,
          x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i) := by
        intro j1 hj1 i hi
        dsimp only [xRows, xRows_res, xRoutedRes]
        have hj1_m : j1 < 2 ^ m_t1 := by rw [hm_t1]; exact ht1_pow.symm ▸ hj1
        rw [read1D_array_getD_eq_read2D,
            read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi,
            runMultiTapeTransposeFullSteps_fst,
            read1D_runMultiTapeTranspose_index_eq m_t1 r hr (read1D xArr) j1 i hj1_m hi,
            hm_t1, ht1_pow]
        have hidx_lt : j1 + t1 * i < t1 * r := by
          have hi_le : i + 1 ≤ r := hi
          calc j1 + t1 * i < t1 + t1 * i := Nat.add_lt_add_right hj1 _
            _ = t1 * (i + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hi_le
        have hcomm : i * t1 + j1 = j1 + t1 * i := by ring
        rw [hcomm, hx (j1 + t1 * i) hidx_lt]
      set U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun j1 : Fin t1 =>
          computableSpreadRowContiguousWithProgramCost p_in pSub p' pSub r
            (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
      set U_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
      set P_res :=
        runScan2DWithSteps t1 r (fun j1 k2 =>
          gPreTwistU pSub (read1D preTwiddles k2) (read2D U_mat j1 k2))
      set P_mat : Array (Array (ℤ × ℤ)) := P_res.1
      set syn_res := computableSyntheticFFTRadix2WithProgramCost p' t1 r m_t1 (r / t1) P_mat
      set Q_res :=
        runScan2DWithSteps t1 r (fun v1 k2 =>
          gRescale pSub pSub (read2D syn_res.1 v1 k2))
      set Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
      set qPost_res :=
        runScan2DWithSteps t1 r (fun v1 k2 =>
          gMulScaled (pSub + 2) (read1D postTwiddles k2) (read2D Q_mat v1 k2))
      set qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
      set qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun v1 : Fin t1 =>
          computablePaperFastDFTWithProgramCost pSub cChild (qPost_mat.getD v1.val #[]))
      set qHat_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
      set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
      set qHat_T_res := runMultiTapeTransposeFullSteps m_r t1 (read1D stFlatQ.outTape)
      set colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          runMultiTapeAffineOddRouteFullSteps m_t1
            (computableOddStrideFactor m_t1 u2.val) 0
            (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
      set Y_res :=
        runScan2DWithSteps r t1 (fun u2 u1 =>
          let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
          gRescale cChild.p pSub (read1D colArr u1))
      set Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
      set alt_q : ℤ × ℤ :=
        (computableNyquistAltSumContiguousWithProgramCost p_in pSub p' r (xRows.getD (t1 / 2) #[])).1
      set Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          let c0 := read1D c0Table u2.val
          let c1_pass := read1D c1Table u2.val
          let Y_col := Y_mat.getD u2.val #[]
          if 2 * u2.val < r then
            computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1_pass Y_col
          else if 2 * u2.val = r then
            computableSolveNyquistWithProgramCost pSub p' t1 c0 Y_col alt_q
          else
            computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1_pass Y_col)
      set Z_cols_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
      set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
      set Z_flat_res := runMultiTapeTransposeFullSteps m_t1 r (read1D stFlatZ.outTape)
      rw [read1D_runSequentialScanSteps_eq _ (t1 * r) u hu, toScaledComplex_gRescale_eq]
      apply congrArg (complexQuantize p)
      set U : ℕ → ℕ → ℂ := fun j1 k2 =>
        kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 k2
      set P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
      set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
      set qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTOfTables cChild (qPost v1) u2
      set v1Of' : ℕ → ℕ → ℕ := fun u2 u1 =>
        oddStrideInvPow2 (Nat.log2 t1) u2 u1
      set Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of' u2 u1) u2)
      have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r,
          toScaledComplex pSub ((P_mat.getD j1 #[]).getD k2 (0, 0)) = P j1 k2 := by
        intro j1 hj1 k2 hk2
        have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
        rw [array_getD_getD_eq_read2D_pair]
        dsimp only [P_mat, P_res, P]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2]
        have hU_row : read2D U_mat j1 k2 =
            read1D (computableSpreadRowContiguousWithCost p_in pSub pSub r
              (filterTaps.getD j1 []) (xRows.getD j1 #[])).1 k2 := by
          dsimp only [U_mat, U_rows]
          rw [read2D_ofFn_of_lt t1 _ hj1_t1 k2]
          simp only [Array.size_ofFn, hj1_t1, ↓reduceDIte, Array.getElem_ofFn,
            computableSpreadRowContiguousWithProgramCost_fst]
        rw [hU_row]
        exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2) _ (U j1 k2)
          (computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps
            p_in pSub pSub t1 r (filterTaps.getD j1 []) (xRows.getD j1 #[]) x j1 k2
            (hxRow_eq j1 hj1_t1) hk2).symm
      have hQ_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D Q_mat v1 k2) = Q v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [Q_mat, Q_res, Q, syn_res]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize pSub)
        have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
          rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
        rw [computableSyntheticFFTRadix2WithProgramCost_fst, hm_t1,
            ← array_getD_getD_eq_read2D_pair _ v1 k2,
            toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1 k2 (ht1_pow.symm ▸ hv1) hk2]
        exact syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P hP_eq v1 k2 hk2
      have hqPost_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [qPost_mat, qPost_res, qPost]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
      have hqHat_eq : ∀ v1 < t1, ∀ u2 < r,
          toScaledComplex child.p (read2D qHat_mat v1 u2) = qHat v1 u2 := by
        intro v1 hv1 u2 hu2
        dsimp only [qHat_mat, qHat_res, qHat]
        rw [read2D_ofFn_of_lt t1 _ hv1 u2]
        simp only [Array.size_ofFn, hv1, ↓reduceDIte, Array.getElem_ofFn]
        exact ih cChild hchild_faith pSub (qPost_mat.getD v1 #[]) (qPost v1)
          (fun k hk => by
            have hk_r : k < r := hchild_size ▸ hk
            rw [read1D_array_getD_eq_read2D]
            exact (hqPost_eq v1 hv1 k hk_r).symm)
          u2 (hchild_size.symm ▸ hu2)
      have hY_eq : ∀ u2 < r, ∀ u1 < t1,
          toScaledComplex pSub (read2D Y_mat u2 u1) = Y u2 u1 := by
        intro u2 hu2 u1 hu1
        dsimp only [Y_mat, Y_res, colRoutes, qHat_T_res, stFlatQ, Y, v1Of']
        rw [read2D_runScan2DWithSteps_of_lt r t1 _ hu2 hu1]
        simp only [Array.size_ofFn, hu2, ↓reduceDIte, Array.getElem_ofFn, toScaledComplex_gRescale_eq]
        have hu1_m : u1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hu1
        have hv1_t1 : oddStrideInvPow2 (Nat.log2 t1) u2 u1 < t1 := by
          rw [← hv1_eq u2 u1]; exact hv1_lt u2 hu2 u1 hu1
        have hcChild_p : cChild.p = child.p := hchild_faith.p_eq
        rw [runMultiTapeAffineOddRouteFullSteps_fst, computableOddStrideFactor_eq_oddStrideFactor, hm_t1,
            read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq (Nat.log2 t1) u2 u1 _ hu1_m,
            runMultiTapeTransposeFullSteps_fst, hm_r,
            read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 r) r t1 hr_pow ht1 qHat_mat u2
              (oddStrideInvPow2 (Nat.log2 t1) u2 u1) hu2 hv1_t1,
            hcChild_p, hqHat_eq _ hv1_t1 u2 hu2]
      have hu2_lt : u % r < r := Nat.mod_lt u hr
      have hu1_lt : u / r < t1 := by rw [Nat.div_lt_iff_lt_mul hr]; linarith
      have hu_decomp : (u / r) * r + u % r = u := by rw [mul_comm, Nat.div_add_mod]
      have hZ_flat : read1D Z_flat_res.1 u = read2D Z_cols_mat (u % r) (u / r) := by
        dsimp only [Z_flat_res, stFlatZ]
        rw [runMultiTapeTransposeFullSteps_fst, hm_t1]
        conv_lhs => rw [← hu_decomp]
        exact read1D_runMultiTapeTranspose_flatten2D_eq (Nat.log2 t1) t1 r ht1_pow hr Z_cols_mat (u / r) (u % r) hu1_lt hu2_lt
      rw [hZ_flat]
      have halt_eq : toScaledComplex pSub alt_q = complexQuantize pSub (nyquistAltSum t1 r x) := by
        dsimp only [alt_q]
        rw [computableNyquistAltSumContiguousWithProgramCost_fst]
        have hhalf_lt : t1 / 2 < t1 := Nat.div_lt_self ht1 (by decide)
        exact toScaledComplex_computableNyquistAltSumContiguous_eq p_in pSub t1 r hr
          (xRows.getD (t1 / 2) #[]) x (hxRow_eq (t1 / 2) hhalf_lt)
      exact toScaledComplex_Z_cols_paper_step_eq pSub p' t1 r c0Table c1Table Y_mat alt_q
        (toScaledComplex pSub (read1D c0Table (u % r)))
        (toScaledComplex pSub (read1D c1Table (u % r)))
        (complexQuantize pSub (nyquistAltSum t1 r x))
        (Y (u % r)) (u % r) (u / r) hu2_lt hu1_lt rfl rfl halt_eq
        (fun k hk => hY_eq (u % r) hu2_lt k hk)

set_option maxHeartbeats 1600000 in
/-- **Single-Step Error Closure under Faithful Tables (`sincGaussianFastDFTOfTables_step_error_le`, `[MS]` Lemma 6.5, §6.3)**:
Given any recursive child transform `childDFT : (ℕ → ℂ) → ℕ → ℂ` satisfying the inductive error bound
`≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * M'`, one step of `sincGaussianFastDFTOfTables` under faithful tables
`filterTaps`, `preTwiddles`, `postTwiddles`, `c0Table`, `c1Table` satisfies the parent error bound
`≤ (2 : ℝ) ^ (-(p : ℤ)) * M`. -/
theorem sincGaussianFastDFTOfTables_step_error_le
    {p K t1 r c1 : ℕ} {v1Of : ℕ → ℕ → ℕ}
    (hp : 8 ≤ p) (hK : 2 ≤ K)
    (ht1 : 0 < t1) (ht1_le : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (hr_le : r ≤ 2 * t1)
    (hsize : t1 * r = 2 ^ K)
    (hc1 : c1 * t1 = r)
    (heven : t1 % 2 = 0)
    (hv1 : ∀ u2 < r, ∀ u1 : ℕ, ∃ q : ℤ,
      (2 * (u2 : ℤ) - 1) * (v1Of u2 u1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ))
    (hv1_eq : ∀ u2 u1 : ℕ, v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1)
    (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
    (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
      filterTaps.getD j1 [] =
        (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
          ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
              (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u),
            G s) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        |((G s : ℝ) / (2 : ℝ) ^ (2 * pChild p K)) -
            sincGaussian (alphaSchedule (pWork p K))
              (((s : ℤ) - ((2 * pChild p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
          (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) ∧
      (∀ s < 2 * (2 * pChild p K) + 1,
        (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1))
    (hPre : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D preTwiddles k2) - zetaRoot r (k2 : ℝ)‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hPost : ∀ k2 < r,
      ‖toScaledComplex (2 * pChild p K) (read1D postTwiddles k2) - zetaRoot r (-(k2 : ℝ))‖ ≤
        2 * complexQuantizeMaxErr (2 * pChild p K))
    (hC01 : ∀ u2 < r,
      let pSub := 2 * pChild p K
      let y := (u2 : ℝ) / (r : ℝ)
      let α := alphaSchedule (pWork p K)
      let c0_pair := read1D c0Table u2
      let c1_pair := read1D c1Table u2
      c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
      0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
      0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
      |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
        2 * realQuantizeMaxErr pSub ∧
      |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
        2 * realQuantizeMaxErr pSub ∧
      (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
      (2 * u2 = r → c1_pair = c0_pair) ∧
      (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1))
    (childDFT : (ℕ → ℂ) → ℕ → ℂ)
    (hchild_err : ∀ (x' : ℕ → ℂ) (M' : ℝ), 1 ≤ M' →
      (∀ k < r, ‖x' k‖ ≤ M') → ∀ u' < r,
      ‖childDFT x' u' - dft1D r x' u'‖ ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * M')
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < t1 * r) :
    let pSub := 2 * pChild p K
    let U : ℕ → ℕ → ℂ := fun j1 k2 =>
      kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 k2
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => childDFT (qPost v1) u2
    let v1Of' : ℕ → ℕ → ℕ := fun u2 u1 =>
      oddStrideInvPow2 (Nat.log2 t1) u2 u1
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of' u2 u1) u2)
    let u2 := u % r
    let u1_tilde := u / r
    let c0_q : ℂ := toScaledComplex pSub (read1D c0Table u2)
    let c1_q : ℂ := toScaledComplex pSub (read1D c1Table u2)
    let alt_q : ℂ := complexQuantize pSub (nyquistAltSum t1 r x)
    let z_sub : ℂ :=
      if 2 * u2 < r then
        solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde
      else
        solveBidiagonalBwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
    ‖complexQuantize p z_sub - dft1D (t1 * r) x u‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) * M := by
  dsimp only
  have hM_pos : 0 < M := by linarith
  have hp_work : 8 ≤ pWork p K := by unfold pWork; omega
  set α := alphaSchedule (pWork p K)
  have hα : 0 < α := alphaSchedule_pos (pWork p K) (by omega)
  set pSub := 2 * pChild p K
  let U : ℕ → ℕ → ℂ := fun j1 k2 =>
    kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 k2
  let U_inf := sincGaussianSpreadArray α t1 r x
  let P_unq : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
  let P : ℕ → ℕ → ℂ := fun j1 k2 =>
    complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
  let Q_unq : ℕ → ℕ → ℂ := syntheticDFT t1 r P_unq
  let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
    complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
  let qPost_unq : ℕ → ℕ → ℂ := fun v1 k2 => zetaRoot r (-(k2 : ℝ)) * Q_unq v1 k2
  let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
    complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
  let qHat : ℕ → ℕ → ℂ := fun v1 u2 => childDFT (qPost v1) u2
  let v1Of' : ℕ → ℕ → ℕ := fun u2 u1 =>
    oddStrideInvPow2 (Nat.log2 t1) u2 u1
  let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of' u2 u1) u2)
  set u2 := u % r
  set u1_tilde := u / r
  have hu2 : u2 < r := Nat.mod_lt u hr
  have hu1_tilde : u1_tilde < t1 := by
    rw [mul_comm] at hu; exact Nat.div_lt_of_lt_mul hu
  set y := (u2 : ℝ) / (r : ℝ)
  set c0R : ℝ := c0Coeff (realErfScaled α) y
  set c1R : ℝ := c1Coeff (realErfScaled α) y
  set c0 : ℂ := (c0R : ℂ)
  set c1_pass : ℂ := (c1R : ℂ)
  set c0_p := read1D c0Table u2
  set c1_p := read1D c1Table u2
  set c0_qR : ℝ := (c0_p.1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
  set c1_qR : ℝ := (c1_p.1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
  set c0_q : ℂ := toScaledComplex pSub c0_p
  set c1_q : ℂ := toScaledComplex pSub c1_p
  obtain ⟨hc0_im, hc1_im, hc0_p_nonneg, hc0_p_le, hc1_p_nonneg, hc1_p_le,
    hc0_err_re, hc1_err_re, hc10_p_fwd, hc10_p_nyq, hc01_p_bwd⟩ := hC01 u2 hu2
  have hpow_pSub2_pos : (0 : ℝ) < (2 : ℝ) ^ (pSub + 2) := by positivity
  have hc0_err : |c0_qR - c0R| ≤ 2 * realQuantizeMaxErr pSub := hc0_err_re
  have hc1_err : |c1_qR - c1R| ≤ 2 * realQuantizeMaxErr pSub := hc1_err_re
  have hc0_qR_nonneg : 0 ≤ c0_qR := div_nonneg (by exact_mod_cast hc0_p_nonneg) hpow_pSub2_pos.le
  have hc0_qR_le1 : c0_qR ≤ 1 := (div_le_one hpow_pSub2_pos).mpr (by exact_mod_cast hc0_p_le)
  have hc1_qR_nonneg : 0 ≤ c1_qR := div_nonneg (by exact_mod_cast hc1_p_nonneg) hpow_pSub2_pos.le
  have hc1_qR_le1 : c1_qR ≤ 1 := (div_le_one hpow_pSub2_pos).mpr (by exact_mod_cast hc1_p_le)
  have hc10_fwd : 2 * u2 < r → c1_qR ≤ c0_qR := fun h =>
    div_le_div_of_nonneg_right (by exact_mod_cast hc10_p_fwd h) hpow_pSub2_pos.le
  have hc01_bwd : r < 2 * u2 → c0_qR ≤ c1_qR := fun h =>
    div_le_div_of_nonneg_right (by exact_mod_cast hc01_p_bwd h) hpow_pSub2_pos.le
  have hc0_q_eq : c0_q = (c0_qR : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; simp [c0_q, c0_p, toScaledComplex, hc0_im]
  have hc1_q_eq : c1_q = (c1_qR : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; simp [c1_q, c1_p, toScaledComplex, hc1_im]
  set alt_q : ℂ := complexQuantize pSub (nyquistAltSum t1 r x)
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hMr_ge1 : 1 ≤ ((r : ℝ) + 1) * M := by nlinarith
  have hr_le_2K : r ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_left r ht1
  have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_right t1 hr
  have hSub_r_err : 2 * complexQuantizeMaxErr pSub * ((r : ℝ) + 1) ≤
      (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
    two_mul_complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K r hr_le_2K
  have hSub_err := complexQuantizeMaxErr_two_mul_pChild_lt p K
  have hpow_child_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild p K : ℤ)) := zpow_pos (by norm_num) _
  have hpow_child_le_one : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hSub_le_pChild_M :
      complexQuantizeMaxErr pSub ≤ (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    have h1 := hSub_err.1.le
    nlinarith
  have hSub_r_le_pChild_M :
      2 * complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) ≤
        (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    calc 2 * complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M)
        = (2 * complexQuantizeMaxErr pSub * ((r : ℝ) + 1)) * M := by ring
      _ ≤ ((0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) * M :=
          mul_le_mul_of_nonneg_right hSub_r_err hM_pos.le
      _ = (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by ring
  have hqSub_nonneg : 0 ≤ complexQuantizeMaxErr pSub := by
    unfold complexQuantizeMaxErr; positivity
  have hU_norm : ∀ j1 < t1, ∀ k2 < r, ‖U j1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
    intro j1 hj1 k2 hk2
    rcases hTaps j1 hj1 with ⟨G, hFold, hG_err, _⟩
    exact norm_kroneckerSpreadOfFoldedTaps_le p K t1 r ht1 hr j1 k2 hj1 hk2
      (filterTaps.getD j1 []) G hFold hG_err x M hM1 hx
  have hP_err : ∀ j1 < t1, ∀ k2 < r,
      ‖P j1 k2 - P_unq j1 k2‖ ≤ (0.02 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    intro j1 hj1 k2 hk2
    set tw := toScaledComplex pSub (read1D preTwiddles k2)
    have hsplit : P j1 k2 - P_unq j1 k2 =
        (P j1 k2 - tw * U j1 k2) + (tw - zetaRoot r (k2 : ℝ)) * U j1 k2 := by
      dsimp only [P_unq]; ring
    rw [hsplit]
    have h1 : ‖P j1 k2 - tw * U j1 k2‖ ≤ complexQuantizeMaxErr pSub :=
      norm_complexQuantize_sub_le pSub (tw * U j1 k2)
    have h2_tw : ‖tw - zetaRoot r (k2 : ℝ)‖ ≤ 2 * complexQuantizeMaxErr pSub := hPre k2 hk2
    have h2_U : ‖U j1 k2‖ ≤ ((r : ℝ) + 1) * M := by
      have := hU_norm j1 hj1 k2 hk2; linarith
    have h2 : ‖(tw - zetaRoot r (k2 : ℝ)) * U j1 k2‖ ≤
        2 * complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) := by
      rw [norm_mul]
      exact mul_le_mul h2_tw h2_U (norm_nonneg _) (by positivity)
    have htri_P := norm_add_le (P j1 k2 - tw * U j1 k2) ((tw - zetaRoot r (k2 : ℝ)) * U j1 k2)
    linarith
  have hQ_err : ∀ v1 : ℕ, ∀ k2 < r,
      ‖Q v1 k2 - Q_unq v1 k2‖ ≤ (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    intro v1 k2 hk2
    obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
    have h1 := norm_syntheticFFTRadix2Quantized_sub_syntheticDFT_le pSub t1 r ht1_pow hr
      P P_unq ((0.02 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) hP_err v1 k2 hk2
    have hlog_err : complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤
        (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
      complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
    have hlog_err_M : ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub ≤
        (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      calc ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub
          = (complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1)) * 1 := by ring
        _ ≤ ((0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) * M :=
            mul_le_mul hlog_err hM1 (by norm_num) (by positivity)
        _ = (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by ring
    linarith
  have hQ_unq_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖Q_unq v1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
    intro v1 k2 hk2
    dsimp only [Q_unq]
    refine norm_syntheticDFT_le t1 r ht1 hr P_unq (((r : ℝ) + (0.5 : ℝ)) * M) ?_ v1 k2 hk2
    intro j1 hj1 m hm
    dsimp only [P_unq]
    rw [norm_mul, norm_zetaRoot, one_mul]
    exact hU_norm j1 hj1 m hm
  have hQ_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖Q v1 k2‖ ≤ ((r : ℝ) + 1) * M := by
    intro v1 k2 hk2
    have htri_Q := norm_add_le (Q v1 k2 - Q_unq v1 k2) (Q_unq v1 k2)
    rw [sub_add_cancel] at htri_Q
    have h1 := hQ_err v1 k2 hk2
    have h2 := hQ_unq_norm v1 k2 hk2
    nlinarith
  have hqPost_err : ∀ v1 : ℕ, ∀ k2 < r,
      ‖qPost v1 k2 - qPost_unq v1 k2‖ ≤ (0.05 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    intro v1 k2 hk2
    set tw := toScaledComplex pSub (read1D postTwiddles k2)
    have hsplit : qPost v1 k2 - qPost_unq v1 k2 =
        (qPost v1 k2 - tw * Q v1 k2) +
          (tw - zetaRoot r (-(k2 : ℝ))) * Q v1 k2 +
          zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - Q_unq v1 k2) := by
      dsimp only [qPost_unq]; ring
    rw [hsplit]
    have h1 : ‖qPost v1 k2 - tw * Q v1 k2‖ ≤ complexQuantizeMaxErr pSub :=
      norm_complexQuantize_sub_le pSub (tw * Q v1 k2)
    have h2_tw : ‖tw - zetaRoot r (-(k2 : ℝ))‖ ≤ 2 * complexQuantizeMaxErr pSub := hPost k2 hk2
    have h2 : ‖(tw - zetaRoot r (-(k2 : ℝ))) * Q v1 k2‖ ≤
        2 * complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) := by
      rw [norm_mul]
      exact mul_le_mul h2_tw (hQ_norm v1 k2 hk2) (norm_nonneg _) (by positivity)
    have h3 : ‖zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - Q_unq v1 k2)‖ ≤
        (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      rw [norm_mul, norm_zetaRoot, one_mul]
      exact hQ_err v1 k2 hk2
    have htri_qP1 := norm_add_le
      ((qPost v1 k2 - tw * Q v1 k2) + (tw - zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
      (zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - Q_unq v1 k2))
    have htri_qP2 := norm_add_le
      (qPost v1 k2 - tw * Q v1 k2)
      ((tw - zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    linarith
  have hqPost_unq_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖qPost_unq v1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
    intro v1 k2 hk2
    dsimp only [qPost_unq]
    rw [norm_mul, norm_zetaRoot, one_mul]
    exact hQ_unq_norm v1 k2 hk2
  have hqPost_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖qPost v1 k2‖ ≤ ((r : ℝ) + 1) * M := by
    intro v1 k2 hk2
    have htri_q := norm_add_le (qPost v1 k2 - qPost_unq v1 k2) (qPost_unq v1 k2)
    rw [sub_add_cancel] at htri_q
    have h1 := hqPost_err v1 k2 hk2
    have h2 := hqPost_unq_norm v1 k2 hk2
    nlinarith
  set ε_child : ℝ := (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)
  set ε_B : ℝ := (0.6 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M
  set ε_total : ℝ := ε_B + ε_child
  have hε_total_nonneg : 0 ≤ ε_total := by dsimp only [ε_total, ε_B, ε_child]; positivity
  have hY_win_err : ∀ k : ℕ,
      ‖Y u2 k - dft2D t1 r U k u2‖ ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M + ε_child := by
    intro k
    have hv1_k_eq : v1Of' u2 k = v1Of u2 k := (hv1_eq u2 k).symm
    rcases hv1 u2 hu2 k with ⟨q, hq⟩
    rw [← hv1_k_eq] at hq
    have hpipe := theorem1_pipeline_computes_dft2D t1 r c1 ht1 hr hc1 U (v1Of' u2 k) k u2 q hq
    dsimp only at hpipe
    have hih := hchild_err (qPost (v1Of' u2 k)) (((r : ℝ) + 1) * M) hMr_ge1 (hqPost_norm (v1Of' u2 k))
      u2 hu2
    have h_dft1D_sub :
        ‖dft1D r (qPost (v1Of' u2 k)) u2 - dft1D r (qPost_unq (v1Of' u2 k)) u2‖ ≤
          (0.05 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M :=
      norm_dft1D_sub_le r hr (qPost (v1Of' u2 k)) (qPost_unq (v1Of' u2 k))
        ((0.05 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) (hqPost_err (v1Of' u2 k)) u2
    have h_Y_round : ‖Y u2 k - qHat (v1Of' u2 k) u2‖ ≤ complexQuantizeMaxErr pSub :=
      norm_complexQuantize_sub_le pSub (qHat (v1Of' u2 k) u2)
    have hpipe_eq : dft1D r (qPost_unq (v1Of' u2 k)) u2 = dft2D t1 r U k u2 := hpipe
    have hsplit : Y u2 k - dft2D t1 r U k u2 =
        (Y u2 k - qHat (v1Of' u2 k) u2) +
          (qHat (v1Of' u2 k) u2 - dft1D r (qPost (v1Of' u2 k)) u2) +
          (dft1D r (qPost (v1Of' u2 k)) u2 - dft1D r (qPost_unq (v1Of' u2 k)) u2) := by
      rw [← hpipe_eq]; ring
    have htri_Y1 := norm_add_le
      ((Y u2 k - qHat (v1Of' u2 k) u2) + (qHat (v1Of' u2 k) u2 - dft1D r (qPost (v1Of' u2 k)) u2))
      (dft1D r (qPost (v1Of' u2 k)) u2 - dft1D r (qPost_unq (v1Of' u2 k)) u2)
    have htri_Y2 := norm_add_le
      (Y u2 k - qHat (v1Of' u2 k) u2)
      (qHat (v1Of' u2 k) u2 - dft1D r (qPost (v1Of' u2 k)) u2)
    rw [← hsplit] at htri_Y1
    dsimp only [qHat] at htri_Y1 htri_Y2 h_Y_round
    linarith
  have hB12_err : ∀ k : ℕ,
      ‖dft2D t1 r U k u2 - dft2D t1 r U_inf k u2‖ ≤ (0.5 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M :=
    fun k => norm_dft2D_kroneckerSpreadOfFoldedTaps_sub_le p K t1 r ht1 hr filterTaps hTaps x M hM1 hx k u2
  have hY_err : ∀ k : ℕ, ‖Y u2 k - dft2D t1 r U_inf k u2‖ ≤ ε_total := by
    intro k
    have hsplit :
        Y u2 k - dft2D t1 r U_inf k u2 =
          (Y u2 k - dft2D t1 r U k u2) + (dft2D t1 r U k u2 - dft2D t1 r U_inf k u2) := by ring
    rw [hsplit]
    have h1 := hY_win_err k
    have h2 := hB12_err k
    have htri_k := norm_add_le (Y u2 k - dft2D t1 r U k u2) (dft2D t1 r U k u2 - dft2D t1 r U_inf k u2)
    dsimp only [ε_total, ε_B]
    linarith
  let X : ℕ → ℂ := fun v => dft1DGrid t1 r x u2 v
  let Y_ideal : ℕ → ℂ := fun k =>
    c0 * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) +
    c1_pass * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)
  let Y_ideal_q : ℕ → ℂ := fun k =>
    c0_q * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) +
    c1_q * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)
  let Y_spread : ℕ → ℂ := fun k => dft2D t1 r U_inf k u2
  have hX_norm : ∀ v : ℕ, ‖X v‖ ≤ M := norm_dft1DGrid_le t1 r ht1 hr x M hx u2 hu2
  have h_bnd_q : Y_ideal_q 0 = c0_q * X 0 + c1_q * X (t1 - 1) := by
    dsimp only [Y_ideal_q]
    rw [emod_sub_zero_toNat t1 0 ht1, emod_zero_sub_one_toNat t1 ht1]
  have h_int_q : ∀ v : ℕ, v + 1 < t1 → Y_ideal_q (v + 1) = c0_q * X (v + 1) + c1_q * X v := by
    intro v hv
    dsimp only [Y_ideal_q]
    rw [emod_sub_zero_toNat t1 (v + 1) hv, emod_succ_sub_one_toNat t1 v hv]
  have hrq_le_cq : realQuantizeMaxErr pSub ≤ complexQuantizeMaxErr pSub := by
    unfold realQuantizeMaxErr complexQuantizeMaxErr
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((pSub : ℤ) + 2)) := zpow_pos (by norm_num) _
    nlinarith
  have h_ideal_q_err : ∀ k : ℕ,
      ‖Y_ideal k - Y_ideal_q k‖ ≤ (0.02 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
    intro k
    set v0 := (((k : ℤ) - 0).emod (t1 : ℤ)).toNat
    set v1 := (((k : ℤ) - 1).emod (t1 : ℤ)).toNat
    have hsplit : Y_ideal k - Y_ideal_q k =
        (c0 - c0_q) * X v0 + (c1_pass - c1_q) * X v1 := by
      dsimp only [Y_ideal, Y_ideal_q]; ring
    rw [hsplit]
    have htri := norm_add_le ((c0 - c0_q) * X v0) ((c1_pass - c1_q) * X v1)
    have hc0_diff : ‖c0 - c0_q‖ ≤ 2 * complexQuantizeMaxErr pSub := by
      dsimp only [c0]
      rw [hc0_q_eq, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      linarith
    have hc1_diff : ‖c1_pass - c1_q‖ ≤ 2 * complexQuantizeMaxErr pSub := by
      dsimp only [c1_pass]
      rw [hc1_q_eq, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      linarith
    have h1 : ‖(c0 - c0_q) * X v0‖ ≤ 2 * complexQuantizeMaxErr pSub * M := by
      rw [norm_mul]
      exact mul_le_mul hc0_diff (hX_norm v0) (norm_nonneg _) (by positivity)
    have h2 : ‖(c1_pass - c1_q) * X v1‖ ≤ 2 * complexQuantizeMaxErr pSub * M := by
      rw [norm_mul]
      exact mul_le_mul hc1_diff (hX_norm v1) (norm_nonneg _) (by positivity)
    have hSub_M : complexQuantizeMaxErr pSub * M ≤ (0.001 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M :=
      mul_le_mul_of_nonneg_right hSub_err.1.le hM_pos.le
    have hpow_M_pos : 0 < (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := mul_pos hpow_child_pos hM_pos
    linarith
  have h_spread_ideal : ∀ k : ℕ,
      ‖Y_spread k - Y_ideal k‖ ≤ (0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M :=
    fun k => theorem2_sincGaussian_dft2D_sub_passband_norm_le
      (pWork p K) t1 r (by omega) ht1 hr k u2 hu2 x M hM_pos.le hx
  set ε_rhs : ℝ :=
    (0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M +
      (ε_total + (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
  have hε_rhs_nonneg : 0 ≤ ε_rhs := by dsimp only [ε_rhs]; positivity
  have h_eff_ideal_q :
      ∀ (m : ℕ) (z : ℂ),
        ‖z - Y u2 m‖ ≤ complexQuantizeMaxErr pSub →
        ‖z - Y_ideal_q m‖ ≤ ε_rhs := by
    intro m z hz
    have hsplit : z - Y_ideal_q m =
        (z - Y u2 m) + (Y u2 m - Y_spread m) +
          (Y_spread m - Y_ideal m) + (Y_ideal m - Y_ideal_q m) := by ring
    rw [hsplit]
    have htri1 := norm_add_le
      ((z - Y u2 m) + (Y u2 m - Y_spread m) + (Y_spread m - Y_ideal m))
      (Y_ideal m - Y_ideal_q m)
    have htri2 := norm_add_le
      ((z - Y u2 m) + (Y u2 m - Y_spread m))
      (Y_spread m - Y_ideal m)
    have htri3 := norm_add_le (z - Y u2 m) (Y u2 m - Y_spread m)
    have h2 := hY_err m
    have h3 := h_spread_ideal m
    have h4 := h_ideal_q_err m
    dsimp only [ε_rhs]
    linarith
  have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
  have hc1R_pos : 0 < c1R := c1Coeff_realErfScaled_pos α y hα
  have hc01_sum : c0R + c1R ≤ 1 := c0_add_c1_realErfScaled_le_one α y hα
  have hc0R_le1 : c0R ≤ 1 := by linarith
  have hc1R_le1 : c1R ≤ 1 := by linarith
  have hr_pos_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hy1 : y ≤ 1 := (div_le_one hr_pos_real).mpr (by exact_mod_cast hu2.le)
  have hA_lt :
      (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M) <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have h1 := mul_lt_mul_of_pos_right (lemma2_termA_conditioning_mul_zpow_lt p K t1 hK ht1_le) hM_pos
    linarith
  have hBC_lt :
      (2.36 : ℝ) * (t1 : ℝ) * (ε_total + (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) <
        (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    lemma2_windowed_child_and_solver_amplification_error_bound p K t1 r M hK hr hM_pos hsize
  have hpow_p_le1 : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h_cyc_le_M : (2.36 : ℝ) * (t1 : ℝ) * ε_rhs ≤ M := by
    have hsum_lt : (2.36 : ℝ) * (t1 : ℝ) * ε_rhs < (0.039 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      dsimp only [ε_rhs]; linarith
    nlinarith
  have ht1_qSub := t1_mul_complexQuantizeMaxErr_two_mul_pChild_le p K t1 ht1_le_2K
  let z_sub : ℂ :=
    if 2 * u2 < r then
      solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
    else if 2 * u2 = r then
      solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde
    else
      solveBidiagonalBwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
  have hz_sub_err :
      ‖z_sub - dft1D (t1 * r) x u‖ ≤
        (2.36 : ℝ) * (t1 : ℝ) * ε_rhs +
          (2.001 : ℝ) * complexQuantizeMaxErr pSub +
          8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
    rw [← dft1DGrid_eq_dft1D t1 r x u]
    change ‖z_sub - X u1_tilde‖ ≤
      (2.36 : ℝ) * (t1 : ℝ) * ε_rhs +
        (2.001 : ℝ) * complexQuantizeMaxErr pSub +
        8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M
    dsimp only [z_sub]
    split_ifs with h_fwd h_nyq
    · have hy_half : y ≤ 1 / 2 := by
        dsimp only [y]; rw [div_le_iff₀ hr_pos_real]
        have : 2 * (u2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h_fwd.le
        linarith
      have hc0R_gt : (0.49999999 : ℝ) ≤ c0R :=
        (c0Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy0 hy_half).le
      have hc10R : c1R ≤ c0R := c1Coeff_le_c0Coeff_of_le_half α y hα hy0 hy_half
      have hratioR : (c1R / c0R) ^ t1 ≤ (0.15 : ℝ) :=
        c1_div_c0_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1 hr hr_le h_fwd
      obtain ⟨hc0_q_ge, hc0_q_le1, hc1_q_nonneg, hc10_q, hratio_q⟩ :=
        faithful_coeff_ratio_pow_le p K t1 ht1_le_2K c0R c1R c0_qR c1_qR
          hc0R_gt hc0R_le1 hc1R_pos.le hc10R hratioR
          hc1_qR_nonneg (hc10_fwd h_fwd) hc0_qR_le1 hc0_err hc1_err
      have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
        rw [hc0_q_eq, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hnorm_c1_q : ‖c1_q‖ = c1_qR := by
        rw [hc1_q_eq, Complex.norm_real, Real.norm_of_nonneg hc1_q_nonneg]
      have hc0_q_pos : 0 < ‖c0_q‖ := by linarith
      have hc0_q_ne : c0_q ≠ 0 := norm_pos_iff.mp hc0_q_pos
      have hc0_q_le1_norm : ‖c0_q‖ ≤ 1 := by linarith
      have hc10_q_norm : ‖c1_q‖ ≤ ‖c0_q‖ := by linarith
      have hratio_q_norm : (‖c1_q‖ / ‖c0_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
        rw [hnorm_c1_q, hnorm_c0_q]; exact hratio_q
      have hdenom_q : c0_q + c1_q * zHomFwd c0_q c1_q (t1 - 1) ≠ 0 :=
        denom_ne_zero_of_relaxed t1 c0_q c1_q (0.4999 : ℝ) (0.1501 : ℝ)
          le_rfl (by linarith) hratio_q_norm le_rfl
      have hrec_q := solveBidiagonalFwd_recover_exact t1 c0_q c1_q ht1 hc0_q_ne hdenom_q
        X Y_ideal_q h_bnd_q h_int_q u1_tilde hu1_tilde
      have hrec_0 := solveBidiagonalFwd_recover_exact t1 c0_q c1_q ht1 hc0_q_ne hdenom_q
        X Y_ideal_q h_bnd_q h_int_q 0 ht1
      have h_eff := norm_solveBidiagonalFwdQuantized_sub_effRHS_le
        pSub t1 ht1 c0_q c1_q (by linarith) hc0_q_le1_norm hc10_q_norm hratio_q_norm
        (by linarith [ht1_qSub.2]) (Y u2) u1_tilde hu1_tilde
      have h_cyc := solveBidiagonalFwd_cyclic_error_bound_relaxed
        t1 ht1 c0_q c1_q Y_ideal_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2))
        (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc10_q_norm hratio_q_norm le_rfl
        hε_rhs_nonneg
        (fun k => h_eff_ideal_q k _ (norm_zPartFwdEffRHS_sub_le pSub c0_q c1_q hc0_q_ne hc0_q_le1_norm (Y u2) k))
        u1_tilde hu1_tilde
      have h_cyc_0 := solveBidiagonalFwd_cyclic_error_bound_relaxed
        t1 ht1 c0_q c1_q Y_ideal_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2))
        (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc10_q_norm hratio_q_norm le_rfl
        hε_rhs_nonneg
        (fun k => h_eff_ideal_q k _ (norm_zPartFwdEffRHS_sub_le pSub c0_q c1_q hc0_q_ne hc0_q_le1_norm (Y u2) k))
        0 ht1
      have hZ0_le :
          ‖solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0‖ ≤ 2 * M := by
        have htri0 := norm_add_le
          (solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0 -
            solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q 0)
          (solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q 0)
        rw [sub_add_cancel, hrec_0] at htri0
        rw [hrec_0] at h_cyc_0
        have hX0 := hX_norm 0
        linarith
      have hmul_Z0 :
          4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
            ‖solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0‖ ≤
            8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
        calc 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
              ‖solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0‖
            ≤ 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * (2 * M) :=
              mul_le_mul_of_nonneg_left hZ0_le
                (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg))
          _ = 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by ring
      rw [← hrec_q]
      have hsplit :
          solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde -
            solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q u1_tilde =
          (solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde -
            solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde) +
          (solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde -
            solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q u1_tilde) := by ring
      rw [hsplit]
      have htri := norm_add_le
        (solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde -
          solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde)
        (solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde -
          solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q u1_tilde)
      linarith
    · have hy_eq : y = 1 / 2 := by
        dsimp only [y]; rw [div_eq_iff hr_pos_real.ne']
        have : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast h_nyq
        linarith
      have hc1_q_eq_c0_q : c1_q = c0_q :=
        congrArg (toScaledComplex pSub) (hc10_p_nyq h_nyq)
      have hy_half : y ≤ 1 / 2 := by linarith
      have hc0R_gt : (0.49999999 : ℝ) ≤ c0R :=
        (c0Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy0 hy_half).le
      have hzero_ratio : ((0 : ℝ) / c0R) ^ t1 ≤ (0.15 : ℝ) := by
        rw [zero_div, zero_pow ht1.ne']; norm_num
      have hzero_err : |(0 : ℝ) - 0| ≤ 2 * realQuantizeMaxErr pSub := by
        rw [sub_self, abs_zero, realQuantizeMaxErr_eq]; positivity
      obtain ⟨hc0_q_ge, hc0_q_le1, _, _, _⟩ :=
        faithful_coeff_ratio_pow_le p K t1 ht1_le_2K c0R 0 c0_qR 0
          hc0R_gt hc0R_le1 le_rfl hc0R_pos.le hzero_ratio
          le_rfl hc0_qR_nonneg hc0_qR_le1 hc0_err hzero_err
      have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
        rw [hc0_q_eq, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hc0_q_pos : 0 < ‖c0_q‖ := by linarith
      have hc0_q_ne : c0_q ≠ 0 := norm_pos_iff.mp hc0_q_pos
      have hc0_q_le1_norm : ‖c0_q‖ ≤ 1 := by linarith
      have h_alt := (dft1DGrid_alternating_sum_nyquist_eq t1 r u2 ht1 hr heven h_nyq x).symm
      have h_int_nyq : ∀ v : ℕ, v + 1 < t1 → Y_ideal_q (v + 1) = c0_q * X (v + 1) + c0_q * X v := by
        intro v hv
        rw [h_int_q v hv, hc1_q_eq_c0_q]
      have hrec_q := solveNyquist_recover_exact t1 ht1 c0_q hc0_q_ne
        X Y_ideal_q h_int_nyq (nyquistAltSum t1 r x) h_alt u1_tilde hu1_tilde
      have h_eff := norm_solveNyquistQuantized_sub_effRHS_le
        pSub t1 c0_q hc0_q_ne (Y u2) alt_q u1_tilde
      have h_nyq_cyc := solveNyquist_error_bound_relaxed
        t1 ht1 c0_q Y_ideal_q (zPartNyqEffRHS pSub c0_q (Y u2))
        (nyquistAltSum t1 r x) alt_q (0.4999 : ℝ) ε_rhs (complexQuantizeMaxErr pSub)
        le_rfl (by linarith) hε_rhs_nonneg
        (fun k => h_eff_ideal_q k _ (norm_zPartNyqEffRHS_sub_le pSub c0_q hc0_q_ne hc0_q_le1_norm (Y u2) k))
        (norm_complexQuantize_sub_le pSub (nyquistAltSum t1 r x))
        u1_tilde hu1_tilde
      have ht1_ge1 : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1
      have hqSub_le_8 :
          complexQuantizeMaxErr pSub / (t1 : ℝ) ≤
            (0.001 : ℝ) * complexQuantizeMaxErr pSub +
              8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
        have hdiv : complexQuantizeMaxErr pSub / (t1 : ℝ) ≤ complexQuantizeMaxErr pSub :=
          div_le_self hqSub_nonneg ht1_ge1
        have h1 : complexQuantizeMaxErr pSub ≤ (t1 : ℝ) * complexQuantizeMaxErr pSub := by
          calc complexQuantizeMaxErr pSub = 1 * complexQuantizeMaxErr pSub := (one_mul _).symm
            _ ≤ (t1 : ℝ) * complexQuantizeMaxErr pSub :=
                mul_le_mul_of_nonneg_right ht1_ge1 hqSub_nonneg
        have h2 : (t1 : ℝ) * complexQuantizeMaxErr pSub ≤
            ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
          calc (t1 : ℝ) * complexQuantizeMaxErr pSub
              = ((t1 : ℝ) * complexQuantizeMaxErr pSub) * 1 := (mul_one _).symm
            _ ≤ ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M :=
                mul_le_mul_of_nonneg_left hM1 (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg)
        have h3 : 0 ≤ ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg) hM_pos.le
        linarith
      rw [← hrec_q]
      have hsplit :
          solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde -
            solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1_tilde =
          (solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde -
            solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde) +
          (solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde -
            solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1_tilde) := by ring
      rw [hsplit]
      have htri := norm_add_le
        (solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde -
          solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde)
        (solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde -
          solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1_tilde)
      linarith
    · have h_bwd : r < 2 * u2 := by omega
      have hy_half : 1 / 2 ≤ y := by
        dsimp only [y]; rw [le_div_iff₀ hr_pos_real]
        have : (r : ℝ) ≤ 2 * (u2 : ℝ) := by exact_mod_cast h_bwd.le
        linarith
      have hc1R_gt : (0.49999999 : ℝ) ≤ c1R :=
        (c1Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy_half hy1).le
      have hc01R : c0R ≤ c1R := c0Coeff_le_c1Coeff_of_ge_half α y hα hy_half hy1
      have hratioR : (c0R / c1R) ^ t1 ≤ (0.15 : ℝ) :=
        c0_div_c1_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1 hr hr_le h_bwd hu2
      obtain ⟨hc1_q_ge, hc1_q_le1, hc0_q_nonneg, hc01_q, hratio_q⟩ :=
        faithful_coeff_ratio_pow_le p K t1 ht1_le_2K c1R c0R c1_qR c0_qR
          hc1R_gt hc1R_le1 hc0R_pos.le hc01R hratioR
          hc0_qR_nonneg (hc01_bwd h_bwd) hc1_qR_le1 hc1_err hc0_err
      have hnorm_c1_q : ‖c1_q‖ = c1_qR := by
        rw [hc1_q_eq, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
        rw [hc0_q_eq, Complex.norm_real, Real.norm_of_nonneg hc0_q_nonneg]
      have hc1_q_pos : 0 < ‖c1_q‖ := by linarith
      have hc1_q_ne : c1_q ≠ 0 := norm_pos_iff.mp hc1_q_pos
      have hc1_q_le1_norm : ‖c1_q‖ ≤ 1 := by linarith
      have hc01_q_norm : ‖c0_q‖ ≤ ‖c1_q‖ := by linarith
      have hratio_q_norm : (‖c0_q‖ / ‖c1_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
        rw [hnorm_c0_q, hnorm_c1_q]; exact hratio_q
      have hdenom_bwd_q : c1_q + c0_q * zHomBwd c0_q c1_q (t1 - 1) ≠ 0 :=
        denom_ne_zero_of_relaxed t1 c1_q c0_q (0.4999 : ℝ) (0.1501 : ℝ)
          le_rfl (by linarith) hratio_q_norm le_rfl
      have hrec_q := solveBidiagonalBwd_recover_exact t1 c0_q c1_q ht1 hc1_q_ne hdenom_bwd_q
        X Y_ideal_q h_bnd_q h_int_q u1_tilde hu1_tilde
      have ht1_sub_lt : t1 - 1 < t1 := Nat.sub_lt ht1 Nat.zero_lt_one
      have hrec_last := solveBidiagonalBwd_recover_exact t1 c0_q c1_q ht1 hc1_q_ne hdenom_bwd_q
        X Y_ideal_q h_bnd_q h_int_q (t1 - 1) ht1_sub_lt
      rw [solveBidiagonalBwd_eq_solveBidiagonalFwd_rev, Nat.sub_self] at hrec_last
      rw [← hrec_q,
          solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev,
          solveBidiagonalBwd_eq_solveBidiagonalFwd_rev]
      set d := t1 - 1 - u1_tilde
      have hd_lt : d < t1 :=
        Nat.lt_of_le_of_lt (Nat.sub_le (t1 - 1) u1_tilde) (Nat.sub_lt ht1 Nat.zero_lt_one)
      have h_eff := norm_solveBidiagonalFwdQuantized_sub_effRHS_le
        pSub t1 ht1 c1_q c0_q (by linarith) hc1_q_le1_norm hc01_q_norm hratio_q_norm
        (by linarith [ht1_qSub.2]) (bwdRevRHS t1 (Y u2)) d hd_lt
      have h_rev_rhs :
          ∀ k : ℕ,
            ‖zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2)) k -
                bwdRevRHS t1 Y_ideal_q k‖ ≤ ε_rhs := by
        intro k
        have h_eff_step := norm_zPartFwdEffRHS_sub_le pSub c1_q c0_q hc1_q_ne hc1_q_le1_norm
          (bwdRevRHS t1 (Y u2)) k
        by_cases hk0 : k = 0
        · subst hk0
          have h1 : bwdRevRHS t1 (Y u2) 0 = Y u2 0 := rfl
          have h2 : bwdRevRHS t1 Y_ideal_q 0 = Y_ideal_q 0 := rfl
          rw [h1] at h_eff_step; rw [h2]
          exact h_eff_ideal_q 0 _ h_eff_step
        · have h1 : bwdRevRHS t1 (Y u2) k = Y u2 (t1 - k) := if_neg hk0
          have h2 : bwdRevRHS t1 Y_ideal_q k = Y_ideal_q (t1 - k) := if_neg hk0
          rw [h1] at h_eff_step; rw [h2]
          exact h_eff_ideal_q (t1 - k) _ h_eff_step
      have h_cyc := solveBidiagonalFwd_cyclic_error_bound_relaxed
        t1 ht1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q)
        (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2)))
        (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc01_q_norm hratio_q_norm le_rfl
        hε_rhs_nonneg h_rev_rhs d hd_lt
      have h_cyc_0 := solveBidiagonalFwd_cyclic_error_bound_relaxed
        t1 ht1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q)
        (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2)))
        (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc01_q_norm hratio_q_norm le_rfl
        hε_rhs_nonneg h_rev_rhs 0 ht1
      have hZ0_le :
          ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0‖ ≤ 2 * M := by
        have htri0 := norm_add_le
          (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0 -
            solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) 0)
          (solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) 0)
        rw [sub_add_cancel, hrec_last] at htri0
        rw [hrec_last] at h_cyc_0
        have hXlast := hX_norm (t1 - 1)
        linarith
      have hmul_Z0 :
          4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
            ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0‖ ≤
            8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
        calc 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
              ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0‖
            ≤ 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * (2 * M) :=
              mul_le_mul_of_nonneg_left hZ0_le
                (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg))
          _ = 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by ring
      have hsplit :
          solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 (Y u2)) d -
            solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d =
          (solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 (Y u2)) d -
            solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d) +
          (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d -
            solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d) := by ring
      rw [hsplit]
      have htri := norm_add_le
        (solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 (Y u2)) d -
          solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d)
        (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d -
          solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d)
      linarith
  have hD_lt :
      (2.001 : ℝ) * complexQuantizeMaxErr pSub +
        8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M <
        (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have h2 := hSub_err.2
    have h3 := ht1_qSub.1
    have hpart1 :
        (2.001 : ℝ) * complexQuantizeMaxErr pSub <
          (0.002001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      calc (2.001 : ℝ) * complexQuantizeMaxErr pSub
          = (2.001 : ℝ) * (complexQuantizeMaxErr pSub * 1) := by ring
        _ ≤ (2.001 : ℝ) * (complexQuantizeMaxErr pSub * M) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM1 hqSub_nonneg) (by norm_num)
        _ < (2.001 : ℝ) * (((0.001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) * M) :=
            mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h2 hM_pos) (by norm_num)
        _ = (0.002001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by ring
    have hpart2 :
        8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M ≤
          (0.0008 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      calc 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M
          ≤ 8 * ((0.0001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) * M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) hM_pos.le
        _ = (0.0008 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by ring
    have hpos_pow_M : 0 < (2 : ℝ) ^ (-(p : ℤ)) * M := by positivity
    linarith
  have hQ_lt :
      ‖complexQuantize p z_sub - z_sub‖ < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr p := by unfold complexQuantizeMaxErr; positivity
    calc ‖complexQuantize p z_sub - z_sub‖
        ≤ complexQuantizeMaxErr p := norm_complexQuantize_sub_le p z_sub
      _ = complexQuantizeMaxErr p * 1 := (mul_one _).symm
      _ ≤ complexQuantizeMaxErr p * M := mul_le_mul_of_nonneg_left hM1 hq_nonneg
      _ < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
          mul_lt_mul_of_pos_right (complexQuantizeMaxErr_lt p) hM_pos
  have htri_final :
      ‖complexQuantize p z_sub - dft1D (t1 * r) x u‖ ≤
        ‖z_sub - dft1D (t1 * r) x u‖ + ‖complexQuantize p z_sub - z_sub‖ := by
    have hsplit : complexQuantize p z_sub - dft1D (t1 * r) x u =
        (z_sub - dft1D (t1 * r) x u) + (complexQuantize p z_sub - z_sub) := by ring
    rw [hsplit]; exact norm_add_le _ _
  have hrhs_expand :
      (2.36 : ℝ) * (t1 : ℝ) * ε_rhs =
        (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M) +
          (2.36 : ℝ) * (t1 : ℝ) * (ε_total + (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) := by
    dsimp only [ε_rhs]; ring
  have hpow_p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M :=
    mul_pos (zpow_pos (by norm_num) _) hM_pos
  linarith

/-- **Multi-Level Inductive Error Bound for `sincGaussianFastDFTOfTables` under `TablesFaithful`
(`sincGaussianFastDFTOfTables_error_le`, `[MS]` Lemma 6.5, §6.3)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) and any faithful
table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`hfaith : TablesFaithful cSpec spec`),
`‖sincGaussianFastDFTOfTables cSpec x u - dft1D spec.size x u‖ ≤ (2 : ℝ) ^ (-(spec.p : ℤ)) * M`. -/
theorem sincGaussianFastDFTOfTables_error_le
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < spec.size, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < spec.size) :
    ‖sincGaussianFastDFTOfTables cSpec x u - dft1D spec.size x u‖ ≤
      (2 : ℝ) ^ (-(spec.p : ℤ)) * M := by
  induction hvalid generalizing cSpec x M u with
  | base p R =>
    cases hfaith with
    | @base p K twiddles hp hK_le htw =>
      dsimp only [sincGaussianFastDFTOfTables, QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx ⊢
      exact norm_baseRadix2FFTOfTwiddles_sub_dft1D_le p K twiddles htw x M hM1 hx u
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p _hchild hv1 _hv1_lt ih =>
    cases hfaith with
    | @step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      dsimp only [sincGaussianFastDFTOfTables, QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx hu ⊢
      exact sincGaussianFastDFTOfTables_step_error_le
        hp hK ht1 ht1_le hr hr_le hsize hc1 heven hv1 hv1_eq
        filterTaps preTwiddles postTwiddles c0Table c1Table
        hTaps hPre hPost hC01
        (sincGaussianFastDFTOfTables cChild)
        (fun x' M' hM1' hx' u' hu' => by
          rw [← hchild_p, ← hchild_size]
          exact ih cChild hchild_faith x' M' hM1' (by rwa [hchild_size]) u' (by rwa [hchild_size]))
        x M hM1 hx u hu

/-- **Direct Error Bound for `computablePaperFastDFT` under `TablesFaithful` (`computablePaperFastDFT_faithful_error_le`, `[MS]` §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`), any faithful
table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`hfaith : TablesFaithful cSpec spec`),
and any input array `xArr` dequantizing to `x` with `‖x k‖ ≤ M`,
`‖toScaledComplex spec.p (read1D (computablePaperFastDFT p_in cSpec xArr) u) - dft1D spec.size x u‖ ≤
  (2 : ℝ) ^ (-(spec.p : ℤ)) * M`. -/
theorem computablePaperFastDFT_faithful_error_le
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ k < spec.size, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < spec.size) :
    ‖toScaledComplex spec.p (read1D (computablePaperFastDFT p_in cSpec xArr) u) -
        dft1D spec.size x u‖ ≤
      (2 : ℝ) ^ (-(spec.p : ℤ)) * M := by
  rw [toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith p_in xArr x hx u hu]
  exact sincGaussianFastDFTOfTables_error_le spec hvalid cSpec hfaith x M hM1 hM u hu

/-- **Master End-to-End Correctness Theorem for `computablePaperFastDFTMultiply` under `TablesFaithful`
(`computablePaperFastDFTMultiply_faithful_eq_mul`, `[MS]` §7)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`) and any faithful
table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`hfaith : TablesFaithful cSpec spec`) with
`spec.size = 2 ^ K0`, `spec.p = rootPrecision b K0`, `k1 + k2 ≤ 2 ^ K0`, and
`A < (2 ^ b) ^ k1`, `B < (2 ^ b) ^ k2`, `computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B = A * B`. -/
theorem computablePaperFastDFTMultiply_faithful_eq_mul
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B = A * B := by
  unfold computablePaperFastDFTMultiply computablePaperFastDFTMultiplyWithProgramCost
  dsimp only [runSequentialScanCostedSteps, costedGMulScaled, costedDivRoundRatInt]
  rw [reconstructChunksTreeWithProgramCost_fst, reconstructChunksTree_eq_reconstructChunks,
      splitChunksTreeWithProgramCost_fst, splitChunksTreeWithProgramCost_fst]
  set xs := splitChunks b k1 A
  set ys := splitChunks b k2 B
  set R0 := 2 ^ K0
  set p0 := rootPrecision b K0
  set x_AB := packNormalizedChunks b k1 k2 A B
  set asArr := (splitChunksTree b k1 A).toArray
  set bsArr := (splitChunksTree b k2 B).toArray
  set stPack := runSequentialScanSteps (fun j =>
    (4 * ((read1D asArr j : ℕ) : ℤ), 4 * ((read1D bsArr j : ℕ) : ℤ))) R0
  set fwd := computablePaperFastDFTWithProgramCost b cSpec stPack.outTape
  set stSq := runSequentialScanSteps (fun u =>
    gConj (gMulScaled (p0 + 2) (read1D fwd.1 u) (read1D fwd.1 u))) R0
  set inv := computablePaperFastDFTWithProgramCost p0 cSpec stSq.outTape
  set numScale : ℤ := ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ)
  set denScale : ℤ := 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ)
  set stExt := runSequentialScanSteps (fun j =>
    let imInt : ℤ := -(read1D inv.1 j).2
    let d := divRoundRatInt (imInt * numScale) denScale
    d.toNat) R0
  have hmap :
      (List.range (k1 + k2)).map (fun j => read1D stExt.outTape j) =
      (List.range (k1 + k2)).map (fun j => (polyMulList xs ys).getD j 0) := by
    refine List.map_congr_left fun j hj_mem => ?_
    have hj_lt : j < k1 + k2 := List.mem_range.mp hj_mem
    have hj_R0 : j < R0 := by dsimp [R0]; omega
    rw [read1D_runSequentialScanSteps_eq _ R0 j hj_R0]
    have hy : ∀ u < R0, toScaledComplex p0 (read1D fwd.1 u) = sincGaussianFastDFTOfTables cSpec x_AB u := by
      intro u hu
      rw [← hp0]
      exact toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith b stPack.outTape x_AB
        (fun k hk => (toScaledComplex_computablePackChunksExact_eq b k1 k2 R0 A B k (hsize ▸ hk)).symm)
        u (hsize.symm ▸ hu)
    have hsConj : ∀ u < spec.size,
        star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2)) =
          toScaledComplex p0 (read1D stSq.outTape u) := by
      intro u hu
      have hu_R0 : u < R0 := hsize ▸ hu
      dsimp only [stSq]
      rw [read1D_runSequentialScanSteps_eq _ R0 u hu_R0, toScaledComplex_gConj,
          toScaledComplex_gMulScaled_eq_complexQuantize_mul, hy u hu_R0, sq]
    have hz : toScaledComplex p0 (read1D inv.1 j) =
        sincGaussianFastDFTOfTables cSpec
          (fun u => star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2))) j := by
      have h := toScaledComplex_computablePaperFastDFT_eq_ofTables spec hvalid cSpec hfaith p0 stSq.outTape
        (fun u => star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2)))
        hsConj j (hsize.symm ▸ hj_R0)
      rwa [hp0] at h
    have hzim :
        (star (sincGaussianFastDFTOfTables cSpec
          (fun u => star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2))) j)).im =
        ((-(read1D inv.1 j).2 : ℤ) : ℝ) / (2 : ℝ) ^ (p0 + 2) := by
      rw [← hz, ← toScaledComplex_gConj]
      simp [toScaledComplex, gConj]
    have hden_pos : (0 : ℤ) < 2 * ((2 ^ (p0 + 2) : ℕ) : ℤ) := by positivity
    dsimp only [numScale, denScale]
    rw [divRoundRatInt_eq_floor _ _ hden_pos]
    have hfloor_eq :
        ⌊(((-(read1D inv.1 j).2 : ℤ) * ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ) : ℤ) : ℝ) /
            ((2 * ((2 ^ (p0 + 2) : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2⌋ =
        ⌊(star (sincGaussianFastDFTOfTables cSpec
          (fun u => star (complexQuantize p0 ((sincGaussianFastDFTOfTables cSpec x_AB u) ^ 2))) j)).im *
          (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) + (1 / 2 : ℝ)⌋ := by
      rw [hzim]
      congr 2
      have hzpow :
          (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) =
            (((2 ^ (2 * b + 2 * K0) : ℕ) : ℝ) / 2) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        have hcast : (2 : ℤ) * (b : ℤ) + 2 * (K0 : ℤ) = ((2 * b + 2 * K0 : ℕ) : ℤ) := by
          push_cast; ring
        rw [hcast, zpow_natCast]; push_cast; rfl
      rw [hzpow]
      have hpow_ne : (2 : ℝ) ^ (p0 + 2) ≠ 0 := by positivity
      push_cast
      field_simp [hpow_ne]
    rw [hfloor_eq]
    have hround := dftApproxConvApprox_round_eq (sincGaussianFastDFTOfTables cSpec) b K0 k1 k2 A B
      (fun x' M' hM1' hx' u' hu' => by
        have herr := sincGaussianFastDFTOfTables_error_le spec hvalid cSpec hfaith x' M' hM1'
          (by rwa [hsize]) u' (by rwa [hsize])
        rwa [hsize, hp0] at herr)
      hk j hj_R0
    dsimp only at hround
    rw [hround, Int.toNat_natCast]
  have hpoly_len : (polyMulList xs ys).length ≤ k1 + k2 := by
    have := length_polyMulList_le xs ys
    rw [length_splitChunks, length_splitChunks] at this
    exact this
  rw [hmap, reconstructChunks_eq_evalRadix, evalRadix_range_getD (2 ^ b) _ (k1 + k2) hpoly_len,
      ← reconstructChunks_eq_evalRadix]
  exact reconstructChunks_polyMulList_splitChunks b k1 k2 A B hA hB

/-- **Program-Cost Upper Bound for `computablePaperFastDFTWithProgramCost` under `TablesFaithful`
(`computablePaperFastDFTWithProgramCost_faithful_snd_le_7000`, `[MS]` §7.2)**:
For any valid specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`), any faithful
table hierarchy `cSpec : ComputablePaperFastDFTSpec` (`hfaith : TablesFaithful cSpec spec`),
any input precision `p_in : ℕ`, and any input `xArr : Array (ℤ × ℤ)` and `x : ℕ → ℂ` satisfying
`∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k)` and `∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p`,
the integer bit-operation and tape-head-step cost `.2` accumulated bottom-up by
`computablePaperFastDFTWithProgramCost p_in cSpec xArr` satisfies:
`((computablePaperFastDFTWithProgramCost p_in cSpec xArr).2 : ℝ) ≤ 7000 * spec.intrinsicCostRadix2Leaf`. -/
theorem computablePaperFastDFTWithProgramCost_faithful_snd_le_7000
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (cSpec : ComputablePaperFastDFTSpec) (hfaith : TablesFaithful cSpec spec)
    (p_in : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < spec.size, x k = toScaledComplex p_in (read1D xArr k))
    (hM : ∀ k < spec.size, ‖x k‖ ≤ (2 : ℝ) ^ spec.p) :
    ((computablePaperFastDFTWithProgramCost p_in cSpec xArr).2 : ℝ) ≤
      7000 * spec.intrinsicCostRadix2Leaf := by
  induction hvalid generalizing cSpec p_in xArr x with
  | base p R =>
    cases hfaith with
    | @base p K twiddles hp hK_le htw =>
      dsimp only [computablePaperFastDFTWithProgramCost]
      refine (computableBaseRadix2FFTWithProgramCost_snd_le p_in p K hp hK_le twiddles xArr).trans ?_
      have hpos : 0 ≤ (QuantizedFastDFTSpec.base p (2 ^ K)).intrinsicCostRadix2Leaf := by
        dsimp [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]; positivity
      linarith
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p hchild hv1 hv1_lt ih =>
    cases hfaith with
    | @step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      dsimp only [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
      dsimp only [QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx hM
      obtain ⟨ht1_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
      obtain ⟨hr_pow, _⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow r t1 K (by rw [mul_comm, hsize])
      set pSub := 2 * pChild p K
      set p' := pChild p K
      have hp'_div : pSub / 2 = p' := Nat.mul_div_right p' zero_lt_two
      dsimp only [computablePaperFastDFTWithProgramCost]
      set m_t1 := natLog2Fuel t1 t1
      set m_r := natLog2Fuel r r
      have hm_t1 : m_t1 = Nat.log2 t1 := natLog2Fuel_self t1
      have hm_r : m_r = Nat.log2 r := natLog2Fuel_self r
      set xRoutedRes := runMultiTapeTransposeFullSteps m_t1 r (read1D xArr)
      set xRows_res :=
        runScan2DWithSteps t1 r (fun j1 i => read1D xRoutedRes.1 (j1 * r + i))
      set xRows : Array (Array (ℤ × ℤ)) := xRows_res.1
      have hxRow_eq : ∀ j1 < t1, ∀ i < r,
          x (j1 + t1 * i) = toScaledComplex p_in (read1D (xRows.getD j1 #[]) i) := by
        intro j1 hj1 i hi
        dsimp only [xRows, xRows_res, xRoutedRes]
        have hj1_m : j1 < 2 ^ m_t1 := by rw [hm_t1]; exact ht1_pow.symm ▸ hj1
        rw [read1D_array_getD_eq_read2D,
            read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi,
            runMultiTapeTransposeFullSteps_fst,
            read1D_runMultiTapeTranspose_index_eq m_t1 r hr (read1D xArr) j1 i hj1_m hi,
            hm_t1, ht1_pow]
        have hidx_lt : j1 + t1 * i < t1 * r := by
          have hi_le : i + 1 ≤ r := hi
          calc j1 + t1 * i < t1 + t1 * i := Nat.add_lt_add_right hj1 _
            _ = t1 * (i + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hi_le
        have hcomm : i * t1 + j1 = j1 + t1 * i := by ring
        rw [hcomm, hx (j1 + t1 * i) hidx_lt]
      set U_rows : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun j1 : Fin t1 =>
          computableSpreadRowContiguousWithProgramCost p_in pSub (pSub / 2) pSub r
            (filterTaps.getD j1.val []) (xRows.getD j1.val #[]))
      set U_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun j1 : Fin t1 => if h : j1.val < U_rows.size then U_rows[j1.val].1 else #[])
      set P_res :=
        runScan2DCostedWithSteps t1 r (fun j1 k2 =>
          costedGPreTwistU pSub (6 * (pSub / 2)) (read1D preTwiddles k2) (read2D U_mat j1 k2))
      set P_mat : Array (Array (ℤ × ℤ)) := P_res.1
      set syn_res := computableSyntheticFFTRadix2WithProgramCost (pSub / 2) t1 r m_t1 (r / t1) P_mat
      set Q_res :=
        runScan2DCostedWithSteps t1 r (fun v1 k2 =>
          costedGRescale pSub pSub (4 * (pSub / 2)) (read2D syn_res.1 v1 k2))
      set Q_mat : Array (Array (ℤ × ℤ)) := Q_res.1
      set qPost_res :=
        runScan2DCostedWithSteps t1 r (fun v1 k2 =>
          costedGMulScaled (pSub + 2) (6 * (pSub / 2)) (read1D postTwiddles k2) (read2D Q_mat v1 k2))
      set qPost_mat : Array (Array (ℤ × ℤ)) := qPost_res.1
      set qHat_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun v1 : Fin t1 =>
          computablePaperFastDFTWithProgramCost pSub cChild (qPost_mat.getD v1.val #[]))
      set qHat_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun v1 : Fin t1 => if h : v1.val < qHat_res.size then qHat_res[v1.val].1 else #[])
      set stFlatQ := runFlatten2DSteps r qHat_mat (t1 * r)
      set qHat_T_res := runMultiTapeTransposeFullSteps m_r t1 (read1D stFlatQ.outTape)
      set colRoutes : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          runMultiTapeAffineOddRouteFullSteps m_t1
            (computableOddStrideFactor m_t1 u2.val) 0
            (fun v1 => read1D qHat_T_res.1 (u2.val * t1 + v1)))
      set Y_res :=
        runScan2DCostedWithSteps r t1 (fun u2 u1 =>
          let colArr := if h : u2 < colRoutes.size then colRoutes[u2].1 else #[]
          costedGRescale cChild.p pSub (4 * (pSub / 2)) (read1D colArr u1))
      set Y_mat : Array (Array (ℤ × ℤ)) := Y_res.1
      set altRes :=
        computableNyquistAltSumContiguousWithProgramCost p_in pSub (pSub / 2) r (xRows.getD (t1 / 2) #[])
      set alt_q : ℤ × ℤ := altRes.1
      set Z_cols_res : Array (Array (ℤ × ℤ) × ℕ) :=
        Array.ofFn (fun u2 : Fin r =>
          let c0 := read1D c0Table u2.val
          let c1_pass := read1D c1Table u2.val
          let Y_col := Y_mat.getD u2.val #[]
          if 2 * u2.val < r then
            computableSolveBidiagonalFwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col
          else if 2 * u2.val = r then
            computableSolveNyquistWithProgramCost pSub (pSub / 2) t1 c0 Y_col alt_q
          else
            computableSolveBidiagonalBwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col)
      set Z_cols_mat : Array (Array (ℤ × ℤ)) :=
        Array.ofFn (fun u2 : Fin r => if h : u2.val < Z_cols_res.size then Z_cols_res[u2.val].1 else #[])
      set stFlatZ := runFlatten2DSteps t1 Z_cols_mat (r * t1)
      set Z_flat_res := runMultiTapeTransposeFullSteps m_t1 r (read1D stFlatZ.outTape)
      set outScan := runSequentialScanCostedSteps (fun u =>
        costedGRescale pSub p (4 * (pSub / 2)) (read1D Z_flat_res.1 u)) (t1 * r)
      set U : ℕ → ℕ → ℂ := fun j1 k2 =>
        kroneckerSpreadOfFoldedTaps pSub pSub t1 r (filterTaps.getD j1 []) x j1 k2
      set P : ℕ → ℕ → ℂ := fun j1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D preTwiddles k2) * U j1 k2)
      set Q : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
      set qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
        complexQuantize pSub (toScaledComplex pSub (read1D postTwiddles k2) * Q v1 k2)
      have hP_eq : ∀ j1 < 2 ^ (Nat.log2 t1), ∀ k2 < r,
          toScaledComplex pSub ((P_mat.getD j1 #[]).getD k2 (0, 0)) = P j1 k2 := by
        intro j1 hj1 k2 hk2
        have hj1_t1 : j1 < t1 := ht1_pow ▸ hj1
        rw [array_getD_getD_eq_read2D_pair]
        dsimp only [P_mat, P_res, runScan2DCostedWithSteps, costedGPreTwistU, P]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1_t1 hk2]
        have hU_row : read2D U_mat j1 k2 =
            read1D (computableSpreadRowContiguousWithCost p_in pSub pSub r
              (filterTaps.getD j1 []) (xRows.getD j1 #[])).1 k2 := by
          dsimp only [U_mat, U_rows]
          rw [read2D_ofFn_of_lt t1 _ hj1_t1 k2]
          simp only [Array.size_ofFn, hj1_t1, ↓reduceDIte, Array.getElem_ofFn,
            computableSpreadRowContiguousWithProgramCost_fst]
        rw [hU_row]
        exact toScaledComplex_gPreTwistU_eq pSub (read1D preTwiddles k2) _ (U j1 k2)
          (computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps
            p_in pSub pSub t1 r (filterTaps.getD j1 []) (xRows.getD j1 #[]) x j1 k2
            (hxRow_eq j1 hj1_t1) hk2).symm
      have hQ_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D Q_mat v1 k2) = Q v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [Q_mat, Q_res, runScan2DCostedWithSteps, costedGRescale, Q, syn_res]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gRescale_eq]
        apply congrArg (complexQuantize pSub)
        have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
          rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
        rw [computableSyntheticFFTRadix2WithProgramCost_fst, hm_t1,
            ← array_getD_getD_eq_read2D_pair _ v1 k2,
            toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow P_mat v1 k2 (ht1_pow.symm ▸ hv1) hk2]
        exact syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ P hP_eq v1 k2 hk2
      have hqPost_eq : ∀ v1 < t1, ∀ k2 < r,
          toScaledComplex pSub (read2D qPost_mat v1 k2) = qPost v1 k2 := by
        intro v1 hv1 k2 hk2
        dsimp only [qPost_mat, qPost_res, runScan2DCostedWithSteps, costedGMulScaled, qPost]
        rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2,
            toScaledComplex_gMulScaled_eq_complexQuantize_mul, hQ_eq v1 hv1 k2 hk2]
      -- 1. Bound `syn_res.2`:
      have hsyn_cost : syn_res.2 = 2 * syntheticFFTStepBitCost t1 r p' := by
        dsimp only [syn_res, syntheticFFTStepBitCost]
        rw [computableSyntheticFFTRadix2WithProgramCost_snd, hm_t1, hp'_div]
      -- 2. Bound `spreadCost = sumArrayCosts U_rows`:
      have hspread_le :
          sumArrayCosts U_rows ≤
            17 * kroneckerSpreadStepBitCost t1 r p' + 7 * twistAndSolverStepBitCost t1 r p' := by
        have hp_le_p' : p ≤ p' := (fixedPointWordBits_le_four_mul_pChild p K).1
        have hx_p' : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ p' := by
          intro k hk
          exact (hM k hk).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp_le_p')
        have hrow_bound :
            sumArrayCosts U_rows ≤
              t1 *
                (17 * (kroneckerSpreadNumBlocks pSub r *
                  (2 * mulBitCost (effectiveFilterWidth pSub r * (6 * p')) +
                    4 * effectiveFilterWidth pSub r * addBitCost (6 * p'))) +
                 (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                  r * (2 * addBitCost (6 * p')))) := by
          dsimp only [U_rows]
          refine sumArrayCosts_ofFn_le_const t1 _ _ (fun j1 hj1 => ?_)
          dsimp only
          rw [hp'_div]
          rcases hTaps j1 hj1 with ⟨G, hFold, _, hG_abs⟩
          have hg_len : (filterTaps.getD j1 []).length ≤ effectiveFilterWidth pSub r := by
            rw [hFold, List.length_map, List.length_range]
          have hprog := computableSpreadRowContiguousWithProgramCost_snd_le p_in pSub p' pSub r
            (filterTaps.getD j1 []) hg_len (xRows.getD j1 #[])
          have hbase := computableSpreadRowContiguousWithCost_of_folded_snd_le p_in p K t1 r hp hK hr
            (filterTaps.getD j1 []) G hFold hG_abs (xRows.getD j1 #[]) x j1 hj1
            (hxRow_eq j1 hj1) hx_p'
          exact hprog.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 17 hbase) _)
        have hextra_row := computableSpreadRowContiguousWithProgramCost_extra_le p' r
        have hmul_dist :
            t1 *
              (17 * (kroneckerSpreadNumBlocks pSub r *
                (2 * mulBitCost (effectiveFilterWidth pSub r * (6 * p')) +
                  4 * effectiveFilterWidth pSub r * addBitCost (6 * p'))) +
               (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                r * (2 * addBitCost (6 * p')))) ≤
              17 * kroneckerSpreadStepBitCost t1 r p' + 7 * twistAndSolverStepBitCost t1 r p' := by
          rw [Nat.mul_add]
          refine Nat.add_le_add ?_ ?_
          · exact le_of_eq (by dsimp [kroneckerSpreadStepBitCost, pSub, p']; ring)
          · calc t1 * (kroneckerSpreadNumBlocks pSub r * (8 * effectiveFilterWidth pSub r * addBitCost (6 * p')) +
                  r * (2 * addBitCost (6 * p')))
                ≤ t1 * (7 * (r * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')))) :=
                  Nat.mul_le_mul_left t1 hextra_row
              _ = 7 * twistAndSolverStepBitCost t1 r p' := by dsimp [twistAndSolverStepBitCost]; ring
        exact hrow_bound.trans hmul_dist
      -- 3. Bound `solverCost = sumArrayCosts Z_cols_res`:
      have hsolver_le :
          sumArrayCosts Z_cols_res ≤ 81 * twistAndSolverStepBitCost t1 r p' := by
        have hcol := sumArrayCosts_ofFn_le_const r
          (fun u2 : Fin r =>
            let c0 := read1D c0Table u2.val
            let c1_pass := read1D c1Table u2.val
            let Y_col := Y_mat.getD u2.val #[]
            if 2 * u2.val < r then
              computableSolveBidiagonalFwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col
            else if 2 * u2.val = r then
              computableSolveNyquistWithProgramCost pSub (pSub / 2) t1 c0 Y_col alt_q
            else
              computableSolveBidiagonalBwdWithProgramCost pSub (pSub / 2) t1 c0 c1_pass Y_col)
          (81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')))
          (fun u2 _ => by
            dsimp only
            rw [hp'_div]
            split_ifs with h1 h2
            · exact computableSolveBidiagonalFwdWithProgramCost_snd_le pSub p' t1 ht1 _ _ _
            · exact computableSolveNyquistWithProgramCost_snd_le pSub p' t1 ht1 _ _ _
            · exact computableSolveBidiagonalBwdWithProgramCost_snd_le pSub p' t1 ht1 _ _ _)
        calc sumArrayCosts Z_cols_res
            ≤ r * (81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) := hcol
          _ = 81 * twistAndSolverStepBitCost t1 r p' := by dsimp [twistAndSolverStepBitCost]; ring
      -- 4. Bound `twistAndSolverCost`:
      have hP_cost_eq :
          P_res.2.2 = (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) := by
        dsimp only [P_res]
        refine runScan2DCostedWithSteps_cost_const t1 r _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGPreTwistU]
        rw [hp'_div, computableMulBitCost_eq]
      have hQ_cost_eq :
          Q_res.2.2 = (t1 * r) * (2 * addBitCost (4 * p')) := by
        dsimp only [Q_res]
        refine runScan2DCostedWithSteps_cost_const t1 r _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGRescale]
        rw [hp'_div]
      have hqPost_cost_eq :
          qPost_res.2.2 = (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) := by
        dsimp only [qPost_res]
        refine runScan2DCostedWithSteps_cost_const t1 r _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGMulScaled]
        rw [hp'_div, computableMulBitCost_eq]
      have hY_cost_eq :
          Y_res.2.2 = (r * t1) * (2 * addBitCost (4 * p')) := by
        dsimp only [Y_res]
        refine runScan2DCostedWithSteps_cost_const r t1 _ _ (fun _ _ _ _ => ?_)
        dsimp only [costedGRescale]
        rw [hp'_div]
      have hout_eq :
          outScan.2.2 = (t1 * r) * (2 * addBitCost (4 * p')) := by
        dsimp only [outScan]
        refine runSequentialScanCostedSteps_cost_const _ (t1 * r) _ (fun _ _ => ?_)
        dsimp only [costedGRescale]
        rw [hp'_div]
      have htwist_le :
          P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
            altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2 ≤
            96 * twistAndSolverStepBitCost t1 r p' := by
        rw [hP_cost_eq, hQ_cost_eq, hqPost_cost_eq, hY_cost_eq, hout_eq]
        obtain ⟨h6, _, _⟩ := mulBitCost_raw_temporaries_le_four_mul_pChild p'
        have halt_le :
            altRes.2 ≤ 5 * twistAndSolverStepBitCost t1 r p' := by
          dsimp only [altRes, twistAndSolverStepBitCost]
          rw [hp'_div]
          exact computableNyquistAltSumContiguousWithProgramCost_snd_le p_in pSub p' t1 r ht1 hr _
        have hscans_le :
            (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (t1 * r) * (2 * addBitCost (4 * p')) +
              (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (r * t1) * (2 * addBitCost (4 * p')) ≤
              9 * twistAndSolverStepBitCost t1 r p' := by
          have hstep :
              2 * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) + 4 * addBitCost (4 * p') ≤
                9 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by
            dsimp [addBitCost]; omega
          calc (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
                (t1 * r) * (2 * addBitCost (4 * p')) +
                (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
                (r * t1) * (2 * addBitCost (4 * p'))
              = (t1 * r) * (2 * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) + 4 * addBitCost (4 * p')) := by ring
            _ ≤ (t1 * r) * (9 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) :=
                Nat.mul_le_mul_left (t1 * r) hstep
            _ = 9 * twistAndSolverStepBitCost t1 r p' := by dsimp [twistAndSolverStepBitCost]; ring
        have hout_le :
            (t1 * r) * (2 * addBitCost (4 * p')) ≤ 1 * twistAndSolverStepBitCost t1 r p' := by
          dsimp [twistAndSolverStepBitCost, addBitCost]
          rw [Nat.one_mul]
          refine Nat.mul_le_mul_left (t1 * r) ?_
          omega
        calc (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (t1 * r) * (2 * addBitCost (4 * p')) +
              (t1 * r) * (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p')) +
              (r * t1) * (2 * addBitCost (4 * p')) +
              altRes.2 + sumArrayCosts Z_cols_res + (t1 * r) * (2 * addBitCost (4 * p'))
            ≤ 9 * twistAndSolverStepBitCost t1 r p' +
              5 * twistAndSolverStepBitCost t1 r p' +
              81 * twistAndSolverStepBitCost t1 r p' +
              1 * twistAndSolverStepBitCost t1 r p' :=
              Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hscans_le halt_le) hsolver_le) hout_le
          _ = 96 * twistAndSolverStepBitCost t1 r p' := by ring
      -- 5. Bound `routingCost`:
      have hrouting_le :
          (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
            (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
              stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
            addBitCost (8 * (pSub / 2)) ≤
          2 * routingAndStreamingStepBitCost t1 r p' := by
        have hcol_sum : sumArrayCosts colRoutes = r * ((2 * m_t1 + 1) * 2 ^ m_t1) := by
          dsimp only [colRoutes]
          refine sumArrayCosts_ofFn_const r _ ((2 * m_t1 + 1) * 2 ^ m_t1) (fun u2 _ => ?_)
          exact runMultiTapeAffineOddRouteFullSteps_snd m_t1 _ 0 _
        have hlhs_eq :
            (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
              (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
              addBitCost (8 * (pSub / 2)) =
            (2 * ((2 * Nat.log2 t1) * (t1 * r)) + (2 * Nat.log2 r) * (r * t1) +
              (2 * Nat.log2 t1) * (t1 * r) + 12 * (t1 * r)) * addBitCost (8 * p') := by
          dsimp only [xRoutedRes, qHat_T_res, Z_flat_res, xRows_res, P_res, Q_res, qPost_res,
            stFlatQ, Y_res, stFlatZ, outScan]
          rw [runMultiTapeTransposeFullSteps_snd, runMultiTapeTransposeFullSteps_snd,
              runMultiTapeTransposeFullSteps_snd, hcol_sum,
              runScan2DWithSteps_snd,
              runScan2DCostedWithSteps_steps, runScan2DCostedWithSteps_steps,
              runScan2DCostedWithSteps_steps, runScan2DCostedWithSteps_steps,
              runFlatten2DSteps_steps, runFlatten2DSteps_steps,
              runSequentialScanCostedSteps_steps,
              hm_t1, hm_r, ht1_pow, hr_pow, hp'_div]
          ring
        have hrhs_eq :
            2 * routingAndStreamingStepBitCost t1 r p' =
              (2 * (2 * ((2 * Nat.log2 t1) * (t1 * r)) + (2 * Nat.log2 r) * (r * t1) +
                (2 * Nat.log2 t1) * (t1 * r)) + 16 * (t1 * r)) * addBitCost (8 * p') := by
          unfold routingAndStreamingStepBitCost sequentialTransposeBitCost
            sequentialColumnMergeSortBitCost sequentialLinearScanBitCost sequentialPassBitCost
          rw [sequentialTapeTransposeWithPasses_snd, sequentialTapeTransposeWithPasses_snd,
              sequentialAffineOddRouteWithPasses_snd]
          ring
        rw [hlhs_eq, hrhs_eq]
        refine Nat.mul_le_mul_right (addBitCost (8 * p')) ?_
        omega
      -- 6. Bound `childCostSum = sumArrayCosts qHat_res`:
      have hchild_sum :
          ((sumArrayCosts qHat_res : ℕ) : ℝ) ≤
            (t1 : ℝ) * (7000 * child.intrinsicCostRadix2Leaf) := by
        dsimp only [qHat_res]
        refine sumArrayCosts_ofFn_cast_le_const t1 _ (7000 * child.intrinsicCostRadix2Leaf)
          (fun v1 hv1 => ?_)
        refine ih cChild hchild_faith pSub (qPost_mat.getD v1 #[]) (qPost v1)
          (fun k hk => ?_) (fun k hk => ?_)
        · have hk_r : k < r := hchild_size ▸ hk
          rw [read1D_array_getD_eq_read2D]
          exact (hqPost_eq v1 hv1 k hk_r).symm
        · have hk_r : k < r := hchild_size ▸ hk
          rw [hchild_p]
          exact norm_qPost_of_faithful_le_two_pow_pChild p K t1 r ht1 hr hsize
            filterTaps preTwiddles postTwiddles hTaps hPre hPost x hM v1 k hk_r
      -- Combine all 6 bounds into `≤ 7000 * (...)`:
      have hlocal_nat :
          syn_res.2 + sumArrayCosts U_rows +
            (P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
              altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2) +
            (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
              (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
              addBitCost (8 * (pSub / 2)) ≤
          7000 * (syntheticFFTStepBitCost t1 r p' + kroneckerSpreadStepBitCost t1 r p' +
            twistAndSolverStepBitCost t1 r p' + routingAndStreamingStepBitCost t1 r p') := by
        have h1 : syn_res.2 ≤ 2 * syntheticFFTStepBitCost t1 r p' := le_of_eq hsyn_cost
        calc syn_res.2 + sumArrayCosts U_rows +
              (P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
                altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2) +
              (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
                (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                  stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
                addBitCost (8 * (pSub / 2))
            ≤ 2 * syntheticFFTStepBitCost t1 r p' +
              (17 * kroneckerSpreadStepBitCost t1 r p' + 7 * twistAndSolverStepBitCost t1 r p') +
              96 * twistAndSolverStepBitCost t1 r p' +
              2 * routingAndStreamingStepBitCost t1 r p' :=
              Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 hspread_le) htwist_le) hrouting_le
          _ ≤ 7000 * (syntheticFFTStepBitCost t1 r p' + kroneckerSpreadStepBitCost t1 r p' +
              twistAndSolverStepBitCost t1 r p' + routingAndStreamingStepBitCost t1 r p') := by
              omega
      have hlocal_real :
          ((syn_res.2 + sumArrayCosts U_rows +
            (P_res.2.2 + Q_res.2.2 + qPost_res.2.2 + Y_res.2.2 +
              altRes.2 + sumArrayCosts Z_cols_res + outScan.2.2) +
            (xRoutedRes.2 + qHat_T_res.2 + Z_flat_res.2 + sumArrayCosts colRoutes +
              (xRows_res.2 + P_res.2.1 + Q_res.2.1 + qPost_res.2.1 +
                stFlatQ.steps + Y_res.2.1 + stFlatZ.steps + outScan.2.1)) *
              addBitCost (8 * (pSub / 2)) : ℕ) : ℝ) ≤
          7000 * (((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ) +
            ((kroneckerSpreadStepBitCost t1 r p' : ℕ) : ℝ) +
            ((twistAndSolverStepBitCost t1 r p' : ℕ) : ℝ) +
            ((routingAndStreamingStepBitCost t1 r p' : ℕ) : ℝ)) := by
        exact_mod_cast hlocal_nat
      have hcomb := add_le_add hlocal_real hchild_sum
      push_cast at hcomb ⊢
      calc ((syn_res.2 : ℝ) + (sumArrayCosts U_rows : ℝ) +
            ((P_res.2.2 : ℝ) + (Q_res.2.2 : ℝ) + (qPost_res.2.2 : ℝ) + (Y_res.2.2 : ℝ) +
              (altRes.2 : ℝ) + (sumArrayCosts Z_cols_res : ℝ) + (outScan.2.2 : ℝ)) +
            ((xRoutedRes.2 : ℝ) + (qHat_T_res.2 : ℝ) + (Z_flat_res.2 : ℝ) + (sumArrayCosts colRoutes : ℝ) +
              ((xRows_res.2 : ℝ) + (P_res.2.1 : ℝ) + (Q_res.2.1 : ℝ) + (qPost_res.2.1 : ℝ) +
                (stFlatQ.steps : ℝ) + (Y_res.2.1 : ℝ) + (stFlatZ.steps : ℝ) + (outScan.2.1 : ℝ))) *
              (addBitCost (8 * (pSub / 2)) : ℝ) +
            (sumArrayCosts qHat_res : ℝ))
          ≤ 7000 * ((syntheticFFTStepBitCost t1 r p' : ℝ) +
              (kroneckerSpreadStepBitCost t1 r p' : ℝ) +
              (twistAndSolverStepBitCost t1 r p' : ℝ) +
              (routingAndStreamingStepBitCost t1 r p' : ℝ)) +
            (t1 : ℝ) * (7000 * child.intrinsicCostRadix2Leaf) := hcomb
        _ = 7000 * (((syntheticFFTStepBitCost t1 r p' : ℝ) +
              (kroneckerSpreadStepBitCost t1 r p' : ℝ) +
              (twistAndSolverStepBitCost t1 r p' : ℝ) +
              (routingAndStreamingStepBitCost t1 r p' : ℝ)) +
            (t1 : ℝ) * child.intrinsicCostRadix2Leaf) := by ring

/-- Lower bound `0.4 ≤ ‖c0 + c1 * zHomFwdQuantized q c0 c1 (t1 - 1)‖` on the quantized cyclic
solver denominator under the relaxed passband conditioning hypotheses (`[MS]` §5.1). -/
theorem norm_denom_zHomFwdQuantized_ge_04
    (q t1 : ℕ) (ht1 : 0 < t1) (c0 c1 : ℂ)
    (hc0_ge : (0.4999 : ℝ) ≤ ‖c0‖) (hc0_le1 : ‖c0‖ ≤ 1)
    (hc10 : ‖c1‖ ≤ ‖c0‖)
    (hratio : (‖c1‖ / ‖c0‖) ^ t1 ≤ (0.1501 : ℝ))
    (ht1_q : (t1 : ℝ) * complexQuantizeMaxErr q ≤ (0.001 : ℝ)) :
    (0.4 : ℝ) ≤ ‖c0 + c1 * zHomFwdQuantized q c0 c1 (t1 - 1)‖ := by
  have hc0_pos : 0 < ‖c0‖ := by linarith
  have hc1_le1 : ‖c1‖ ≤ 1 := hc10.trans hc0_le1
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr q := by
    unfold complexQuantizeMaxErr; positivity
  set D := c0 + c1 * zHomFwd c0 c1 (t1 - 1)
  set D_q := c0 + c1 * zHomFwdQuantized q c0 c1 (t1 - 1)
  have htail_eq : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ = ‖c0‖ * (‖c1‖ / ‖c0‖) ^ t1 := by
    unfold zHomFwd
    rw [norm_mul, norm_pow, norm_div, norm_neg]
    have ht1_eq : t1 = (t1 - 1) + 1 := by omega
    conv_rhs => rw [ht1_eq, pow_succ]
    have hc0_ne : ‖c0‖ ≠ 0 := hc0_pos.ne'
    field_simp [hc0_ne]
  have htail_le : ‖c1 * zHomFwd c0 c1 (t1 - 1)‖ ≤ ‖c0‖ * (0.1501 : ℝ) := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_left hratio hc0_pos.le
  have hD_ge : (0.424 : ℝ) ≤ ‖D‖ := by
    have htri := norm_sub_le D (c1 * zHomFwd c0 c1 (t1 - 1))
    have hsub : D - c1 * zHomFwd c0 c1 (t1 - 1) = c0 := by dsimp only [D]; ring
    rw [hsub] at htri
    nlinarith
  have ht1_sub_le : ((t1 - 1 : ℕ) : ℝ) ≤ (t1 : ℝ) := by
    exact_mod_cast Nat.sub_le t1 1
  have hhom_t1 :
      ‖zHomFwd c0 c1 (t1 - 1) - zHomFwdQuantized q c0 c1 (t1 - 1)‖ ≤
        (t1 : ℝ) * complexQuantizeMaxErr q := by
    rw [norm_sub_rev]
    exact (norm_zHomFwdQuantized_sub_le q c0 c1 hc0_pos hc10 (t1 - 1)).trans
      (mul_le_mul_of_nonneg_right ht1_sub_le hq_nonneg)
  have hD_diff : ‖D - D_q‖ ≤ (t1 : ℝ) * complexQuantizeMaxErr q := by
    have heq : D - D_q = c1 * (zHomFwd c0 c1 (t1 - 1) - zHomFwdQuantized q c0 c1 (t1 - 1)) := by
      dsimp only [D, D_q]; ring
    rw [heq, norm_mul]
    calc ‖c1‖ * ‖zHomFwd c0 c1 (t1 - 1) - zHomFwdQuantized q c0 c1 (t1 - 1)‖
        ≤ 1 * ((t1 : ℝ) * complexQuantizeMaxErr q) :=
          mul_le_mul hc1_le1 hhom_t1 (norm_nonneg _) zero_le_one
      _ = (t1 : ℝ) * complexQuantizeMaxErr q := one_mul _
  have htri := norm_add_le D_q (D - D_q)
  have hadd : D_q + (D - D_q) = D := by ring
  rw [hadd] at htri
  linarith

/-- Under `TablesFaithful`, for every column `u2 < r`, the passband table entries `c0_p = read1D c0Table u2`
and `c1_p = read1D c1Table u2` satisfy the solver conditioning and denominator lower bounds in their
respective active regime (`2 * u2 < r`, `2 * u2 = r`, or `r < 2 * u2`). -/
theorem faithful_c0_c1_solver_preconditions
    (p K t1 r : ℕ) (_hp : 8 ≤ p) (_hK : 2 ≤ K)
    (ht1 : 0 < t1) (hr : 0 < r) (hr_le : r ≤ 2 * t1) (hsize : t1 * r = 2 ^ K)
    (c0Table c1Table : Array (ℤ × ℤ))
    (hC01 : ∀ u2 < r,
      let pSub := 2 * pChild p K
      let y := (u2 : ℝ) / (r : ℝ)
      let α := alphaSchedule (pWork p K)
      let c0_pair := read1D c0Table u2
      let c1_pair := read1D c1Table u2
      c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
      0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
      0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
      |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
        2 * realQuantizeMaxErr pSub ∧
      |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
        2 * realQuantizeMaxErr pSub ∧
      (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
      (2 * u2 = r → c1_pair = c0_pair) ∧
      (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1))
    (u2 : ℕ) (hu2 : u2 < r) :
    let pSub := 2 * pChild p K
    let c0_q := toScaledComplex pSub (read1D c0Table u2)
    let c1_q := toScaledComplex pSub (read1D c1Table u2)
    (2 * u2 < r →
      (0.4999 : ℝ) ≤ ‖c0_q‖ ∧ ‖c0_q‖ ≤ 1 ∧ ‖c1_q‖ ≤ ‖c0_q‖ ∧
      (0.4 : ℝ) ≤ ‖c0_q + c1_q * zHomFwdQuantized pSub c0_q c1_q (t1 - 1)‖) ∧
    (2 * u2 = r →
      (0.4999 : ℝ) ≤ ‖c0_q‖ ∧ ‖c0_q‖ ≤ 1) ∧
    (r < 2 * u2 →
      (0.4999 : ℝ) ≤ ‖c1_q‖ ∧ ‖c1_q‖ ≤ 1 ∧ ‖c0_q‖ ≤ ‖c1_q‖ ∧
      (0.4 : ℝ) ≤ ‖c1_q + c0_q * zHomBwdQuantized pSub c0_q c1_q (t1 - 1)‖) := by
  dsimp only
  set pSub := 2 * pChild p K
  set α := alphaSchedule (pWork p K)
  set y := (u2 : ℝ) / (r : ℝ)
  set c0R := c0Coeff (realErfScaled α) y
  set c1R := c1Coeff (realErfScaled α) y
  set c0_p := read1D c0Table u2
  set c1_p := read1D c1Table u2
  set c0_qR : ℝ := (c0_p.1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
  set c1_qR : ℝ := (c1_p.1 : ℝ) / (2 : ℝ) ^ (pSub + 2)
  set c0_q : ℂ := toScaledComplex pSub c0_p
  set c1_q : ℂ := toScaledComplex pSub c1_p
  obtain ⟨hc0_im, hc1_im, hc0_p_nonneg, hc0_p_le, hc1_p_nonneg, hc1_p_le,
    hc0_err_re, hc1_err_re, hc10_p_fwd, _, hc01_p_bwd⟩ := hC01 u2 hu2
  have hpow_pSub2_pos : (0 : ℝ) < (2 : ℝ) ^ (pSub + 2) := by positivity
  have hc0_err : |c0_qR - c0R| ≤ 2 * realQuantizeMaxErr pSub := hc0_err_re
  have hc1_err : |c1_qR - c1R| ≤ 2 * realQuantizeMaxErr pSub := hc1_err_re
  have hc0_qR_nonneg : 0 ≤ c0_qR := div_nonneg (by exact_mod_cast hc0_p_nonneg) hpow_pSub2_pos.le
  have hc0_qR_le1 : c0_qR ≤ 1 := (div_le_one hpow_pSub2_pos).mpr (by exact_mod_cast hc0_p_le)
  have hc1_qR_nonneg : 0 ≤ c1_qR := div_nonneg (by exact_mod_cast hc1_p_nonneg) hpow_pSub2_pos.le
  have hc1_qR_le1 : c1_qR ≤ 1 := (div_le_one hpow_pSub2_pos).mpr (by exact_mod_cast hc1_p_le)
  have hc10_fwd : 2 * u2 < r → c1_qR ≤ c0_qR := fun h =>
    div_le_div_of_nonneg_right (by exact_mod_cast hc10_p_fwd h) hpow_pSub2_pos.le
  have hc01_bwd : r < 2 * u2 → c0_qR ≤ c1_qR := fun h =>
    div_le_div_of_nonneg_right (by exact_mod_cast hc01_p_bwd h) hpow_pSub2_pos.le
  have hc0_q_eq : c0_q = (c0_qR : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; simp [c0_q, c0_p, toScaledComplex, hc0_im]
  have hc1_q_eq : c1_q = (c1_qR : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; simp [c1_q, c1_p, toScaledComplex, hc1_im]
  have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
    rw [hc0_q_eq, Complex.norm_real, Real.norm_of_nonneg hc0_qR_nonneg]
  have hnorm_c1_q : ‖c1_q‖ = c1_qR := by
    rw [hc1_q_eq, Complex.norm_real, Real.norm_of_nonneg hc1_qR_nonneg]
  have hp_work : 8 ≤ pWork p K := by unfold pWork; omega
  have hα : 0 < α := alphaSchedule_pos (pWork p K) (by omega)
  have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
  have hc1R_pos : 0 < c1R := c1Coeff_realErfScaled_pos α y hα
  have hc01_sum : c0R + c1R ≤ 1 := c0_add_c1_realErfScaled_le_one α y hα
  have hc0R_le1 : c0R ≤ 1 := by linarith
  have hc1R_le1 : c1R ≤ 1 := by linarith
  have hr_pos_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
  have hy1 : y ≤ 1 := (div_le_one hr_pos_real).mpr (by exact_mod_cast hu2.le)
  have ht1_le_2K : t1 ≤ 2 ^ K := by rw [← hsize]; exact Nat.le_mul_of_pos_right t1 hr
  have ht1_qSub := (t1_mul_complexQuantizeMaxErr_two_mul_pChild_le p K t1 ht1_le_2K).2
  refine ⟨fun h_fwd => ?_, fun h_nyq => ?_, fun h_bwd => ?_⟩
  · have hy_half : y ≤ 1 / 2 := by
      dsimp only [y]; rw [div_le_iff₀ hr_pos_real]
      have : 2 * (u2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h_fwd.le
      linarith
    have hc0R_gt : (0.49999999 : ℝ) ≤ c0R :=
      (c0Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy0 hy_half).le
    have hc10R : c1R ≤ c0R := c1Coeff_le_c0Coeff_of_le_half α y hα hy0 hy_half
    have hratioR : (c1R / c0R) ^ t1 ≤ (0.15 : ℝ) :=
      c1_div_c0_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1 hr hr_le h_fwd
    obtain ⟨hc0_q_ge, hc0_q_le1, _, hc10_q, hratio_q⟩ :=
      faithful_coeff_ratio_pow_le p K t1 ht1_le_2K c0R c1R c0_qR c1_qR
        hc0R_gt hc0R_le1 hc1R_pos.le hc10R hratioR
        hc1_qR_nonneg (hc10_fwd h_fwd) hc0_qR_le1 hc0_err hc1_err
    have h1 : (0.4999 : ℝ) ≤ ‖c0_q‖ := by linarith
    have h2 : ‖c0_q‖ ≤ 1 := by linarith
    have h3 : ‖c1_q‖ ≤ ‖c0_q‖ := by linarith
    have h4 : (‖c1_q‖ / ‖c0_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
      rw [hnorm_c1_q, hnorm_c0_q]; exact hratio_q
    exact ⟨h1, h2, h3, norm_denom_zHomFwdQuantized_ge_04 pSub t1 ht1 c0_q c1_q h1 h2 h3 h4 (by linarith)⟩
  · have hy_half : y ≤ 1 / 2 := by
      dsimp only [y]; rw [div_le_iff₀ hr_pos_real]
      have : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast h_nyq
      linarith
    have hc0R_gt : (0.49999999 : ℝ) ≤ c0R :=
      (c0Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy0 hy_half).le
    have hzero_ratio : ((0 : ℝ) / c0R) ^ t1 ≤ (0.15 : ℝ) := by
      rw [zero_div, zero_pow ht1.ne']; norm_num
    have hzero_err : |(0 : ℝ) - 0| ≤ 2 * realQuantizeMaxErr pSub := by
      rw [sub_self, abs_zero, realQuantizeMaxErr_eq]; positivity
    obtain ⟨hc0_q_ge, hc0_q_le1, _, _, _⟩ :=
      faithful_coeff_ratio_pow_le p K t1 ht1_le_2K c0R 0 c0_qR 0
        hc0R_gt hc0R_le1 le_rfl hc0R_pos.le hzero_ratio
        le_rfl hc0_qR_nonneg hc0_qR_le1 hc0_err hzero_err
    exact ⟨by linarith, by linarith⟩
  · have hy_half : 1 / 2 ≤ y := by
      dsimp only [y]; rw [le_div_iff₀ hr_pos_real]
      have : (r : ℝ) ≤ 2 * (u2 : ℝ) := by exact_mod_cast h_bwd.le
      linarith
    have hc1R_gt : (0.49999999 : ℝ) ≤ c1R :=
      (c1Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy_half hy1).le
    have hc01R : c0R ≤ c1R := c0Coeff_le_c1Coeff_of_ge_half α y hα hy_half hy1
    have hratioR : (c0R / c1R) ^ t1 ≤ (0.15 : ℝ) :=
      c0_div_c1_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1 hr hr_le h_bwd hu2
    obtain ⟨hc1_q_ge, hc1_q_le1, _, hc01_q, hratio_q⟩ :=
      faithful_coeff_ratio_pow_le p K t1 ht1_le_2K c1R c0R c1_qR c0_qR
        hc1R_gt hc1R_le1 hc0R_pos.le hc01R hratioR
        hc0_qR_nonneg (hc01_bwd h_bwd) hc1_qR_le1 hc1_err hc0_err
    have h1 : (0.4999 : ℝ) ≤ ‖c1_q‖ := by linarith
    have h2 : ‖c1_q‖ ≤ 1 := by linarith
    have h3 : ‖c0_q‖ ≤ ‖c1_q‖ := by linarith
    have h4 : (‖c0_q‖ / ‖c1_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
      rw [hnorm_c0_q, hnorm_c1_q]; exact hratio_q
    exact ⟨h1, h2, h3, norm_denom_zHomFwdQuantized_ge_04 pSub t1 ht1 c1_q c0_q h1 h2 h3 h4 (by linarith)⟩

end IntMul
