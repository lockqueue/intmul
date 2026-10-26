import IntMul.MaterializedAndComputable.FaithfulTablesPerturbation
import WP.W14.Schedule

/-!
# W14 (3/11): schedule-parametric table faithfulness

`TablesFaithfulAt S` is the snapshot's `TablesFaithful` (FTP:36) with the hard-wired
`2 * pChild p K` (sub-step grid and window) and `2 * p + K + 8` (leaf grid) replaced by
`S.pSub p K`, `S.m1 p K` and `S.qLeaf p K`. At `snapshotSchedule` it is `TablesFaithful`
(`tablesFaithfulAt_snapshot_iff`).

Non-vacuity: `idealRoundedTablesAt S spec` (round-to-nearest tables, the analogue of PHP:83) satisfies
`TablesFaithfulAt S` for every valid paper-executable spec (`idealRoundedTablesAt_faithful`).
-/

namespace WP.W14

open IntMul Complex Real

/-- **Schedule-parametric table faithfulness** (FTP:36 with the schedule `S`). -/
inductive TablesFaithfulAt (S : StepSchedule) :
    ComputablePaperFastDFTSpec → QuantizedFastDFTSpec → Prop
  | base (p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
      (hp : 8 ≤ p) (hK : K ≤ 5 * p)
      (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
        ‖toScaledComplex (S.qLeaf p K) (read1D (twiddles.getD s #[]) u) -
            stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤
          2 * complexQuantizeMaxErr (S.qLeaf p K)) :
      TablesFaithfulAt S (.basePow2 p K twiddles) (.base p (2 ^ K))
  | step (p K t1 r c1 : ℕ) (v1Of : ℕ → ℕ → ℕ)
      (filterTaps : Array (List ℤ))
      (preTwiddles postTwiddles c0Table c1Table : Array (ℤ × ℤ))
      (cChild : ComputablePaperFastDFTSpec) (child : QuantizedFastDFTSpec)
      (hv1_eq : ∀ u2 u1 : ℕ, v1Of u2 u1 = oddStrideInvPow2 (Nat.log2 t1) u2 u1)
      (hTaps : ∀ j1 < t1, ∃ G : ℕ → ℤ,
        filterTaps.getD j1 [] =
          (List.range (effectiveFilterWidth (S.m1 p K) r)).map (fun u =>
            ∑ s ∈ (Finset.range (2 * (S.m1 p K) + 1)).filter
                (fun s => s % effectiveFilterWidth (S.m1 p K) r = u),
              G s) ∧
        (∀ s < 2 * (S.m1 p K) + 1,
          |((G s : ℝ) / (2 : ℝ) ^ (S.pSub p K)) -
              sincGaussian (alphaSchedule (pWork p K))
                (((s : ℤ) - ((S.m1 p K : ℕ) : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))| ≤
            (2 : ℝ) ^ (-((S.pSub p K : ℕ) : ℤ))) ∧
        (∀ s < 2 * (S.m1 p K) + 1,
          (G s).natAbs ≤ 2 ^ (S.pSub p K) + 1))
      (hPre : ∀ k2 < r,
        ‖toScaledComplex (S.pSub p K) (read1D preTwiddles k2) -
            zetaRoot r (k2 : ℝ)‖ ≤
          2 * complexQuantizeMaxErr (S.pSub p K))
      (hPost : ∀ k2 < r,
        ‖toScaledComplex (S.pSub p K) (read1D postTwiddles k2) -
            zetaRoot r (-(k2 : ℝ))‖ ≤
          2 * complexQuantizeMaxErr (S.pSub p K))
      (hC01 : ∀ u2 < r,
        let pSub := S.pSub p K
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
      (hChild : TablesFaithfulAt S cChild child) :
      TablesFaithfulAt S
        (.step p (S.pSub p K) (S.m1 p K) t1 r
          filterTaps preTwiddles postTwiddles c0Table c1Table cChild)
        (.step p K t1 r c1 v1Of child)

theorem TablesFaithfulAt.p_eq {S : StepSchedule} {cSpec : ComputablePaperFastDFTSpec}
    {spec : QuantizedFastDFTSpec} (h : TablesFaithfulAt S cSpec spec) : cSpec.p = spec.p := by
  cases h <;> rfl

/-- At the snapshot's schedule, `TablesFaithfulAt` is the snapshot's `TablesFaithful`. -/
theorem tablesFaithfulAt_snapshot_iff (cSpec : ComputablePaperFastDFTSpec) (spec : QuantizedFastDFTSpec) :
    TablesFaithfulAt snapshotSchedule cSpec spec ↔ TablesFaithful cSpec spec := by
  constructor
  · intro h
    induction h with
    | base p K twiddles hp hK htw => exact TablesFaithful.base p K twiddles hp hK htw
    | step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 _ ih =>
      exact TablesFaithful.step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table
        cChild child hv1_eq hTaps hPre hPost hC01 ih
  · intro h
    induction h with
    | base p K twiddles hp hK htw => exact TablesFaithfulAt.base p K twiddles hp hK htw
    | step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 _ ih =>
      exact TablesFaithfulAt.step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table
        cChild child hv1_eq hTaps hPre hPost hC01 ih

/-- Round-to-nearest tables at schedule `S` (PHP:83 with the schedule `S`). -/
noncomputable def idealRoundedTablesAt (S : StepSchedule) :
    QuantizedFastDFTSpec → ComputablePaperFastDFTSpec
  | .base p R =>
    let K := Nat.log2 R
    let q_leaf := S.qLeaf p K
    let twiddles : Array (Array (ℤ × ℤ)) :=
      Array.ofFn (fun s : Fin K =>
        Array.ofFn (fun u : Fin (2 ^ (s.val + 1)) =>
          (realQuantizeInt q_leaf (stdChar ((u.val : ℝ) / ((2 ^ (s.val + 1) : ℕ) : ℝ))).re,
           realQuantizeInt q_leaf (stdChar ((u.val : ℝ) / ((2 ^ (s.val + 1) : ℕ) : ℝ))).im)))
    .basePow2 p K twiddles
  | .step p K t1 r _c1 _v1Of child =>
    let α := alphaSchedule (pWork p K)
    let pSub := S.pSub p K
    let m1 := S.m1 p K
    let filterTaps : Array (List ℤ) :=
      Array.ofFn (fun j1 : Fin t1 =>
        kroneckerSpreadFilterTapsFolded α pSub m1 t1 r j1.val)
    let preTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2 : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).re,
         realQuantizeInt pSub (zetaRoot r (k2.val : ℝ)).im))
    let postTwiddles : Array (ℤ × ℤ) :=
      Array.ofFn (fun k2 : Fin r =>
        (realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).re,
         realQuantizeInt pSub (zetaRoot r (-(k2.val : ℝ))).im))
    let c0Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r =>
        (realQuantizeInt pSub (c0Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
    let c1Table : Array (ℤ × ℤ) :=
      Array.ofFn (fun u2 : Fin r =>
        (realQuantizeInt pSub (c1Coeff (realErfScaled α) ((u2.val : ℝ) / (r : ℝ))), 0))
    .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table
      (idealRoundedTablesAt S child)

/-- Faithfulness of the passband tables at any grid `pSub` (the `hC01` clause). -/
theorem idealRounded_c01_faithful (pSub p K r u2 : ℕ) (hr : 0 < r) (hu2 : u2 < r) :
    let y := (u2 : ℝ) / (r : ℝ)
    let α := alphaSchedule (pWork p K)
    let c0_pair : ℤ × ℤ := (realQuantizeInt pSub (c0Coeff (realErfScaled α) y), 0)
    let c1_pair : ℤ × ℤ := (realQuantizeInt pSub (c1Coeff (realErfScaled α) y), 0)
    c0_pair.2 = 0 ∧ c1_pair.2 = 0 ∧
    0 ≤ c0_pair.1 ∧ c0_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    0 ≤ c1_pair.1 ∧ c1_pair.1 ≤ (2 : ℤ) ^ (pSub + 2) ∧
    |(toScaledComplex pSub c0_pair).re - c0Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    |(toScaledComplex pSub c1_pair).re - c1Coeff (realErfScaled α) y| ≤
      2 * realQuantizeMaxErr pSub ∧
    (2 * u2 < r → c1_pair.1 ≤ c0_pair.1) ∧
    (2 * u2 = r → c1_pair = c0_pair) ∧
    (r < 2 * u2 → c0_pair.1 ≤ c1_pair.1) := by
  dsimp only
  set α := alphaSchedule (pWork p K)
  have hα : 0 < α := alphaSchedule_pos (pWork p K) (by unfold pWork; omega)
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
  have hc0_int_bounds :
      0 ≤ realQuantizeInt pSub c0R ∧ realQuantizeInt pSub c0R ≤ (2 : ℤ) ^ (pSub + 2) := by
    rw [realQuantize_eq_realQuantizeInt_div] at hc0_Icc
    have hlo : (0 : ℝ) ≤ (realQuantizeInt pSub c0R : ℝ) := by
      have := mul_nonneg hc0_Icc.1 hscale_pos.le
      rwa [div_mul_cancel₀ _ hscale_pos.ne'] at this
    have hhi : (realQuantizeInt pSub c0R : ℝ) ≤ (2 : ℝ) ^ (pSub + 2) :=
      (div_le_one hscale_pos).mp hc0_Icc.2
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hc1_int_bounds :
      0 ≤ realQuantizeInt pSub c1R ∧ realQuantizeInt pSub c1R ≤ (2 : ℤ) ^ (pSub + 2) := by
    rw [realQuantize_eq_realQuantizeInt_div] at hc1_Icc
    have hlo : (0 : ℝ) ≤ (realQuantizeInt pSub c1R : ℝ) := by
      have := mul_nonneg hc1_Icc.1 hscale_pos.le
      rwa [div_mul_cancel₀ _ hscale_pos.ne'] at this
    have hhi : (realQuantizeInt pSub c1R : ℝ) ≤ (2 : ℝ) ^ (pSub + 2) :=
      (div_le_one hscale_pos).mp hc1_Icc.2
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hc0_re : (toScaledComplex pSub (realQuantizeInt pSub c0R, 0)).re = realQuantize pSub c0R :=
    (realQuantize_eq_realQuantizeInt_div pSub c0R).symm
  have hc1_re : (toScaledComplex pSub (realQuantizeInt pSub c1R, 0)).re = realQuantize pSub c1R :=
    (realQuantize_eq_realQuantizeInt_div pSub c1R).symm
  have hc0_err : |realQuantize pSub c0R - c0R| ≤ 2 * realQuantizeMaxErr pSub := by
    have := abs_realQuantize_sub_le pSub c0R
    have h0 : 0 ≤ realQuantizeMaxErr pSub := by unfold realQuantizeMaxErr; positivity
    linarith
  have hc1_err : |realQuantize pSub c1R - c1R| ≤ 2 * realQuantizeMaxErr pSub := by
    have := abs_realQuantize_sub_le pSub c1R
    have h0 : 0 ≤ realQuantizeMaxErr pSub := by unfold realQuantizeMaxErr; positivity
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

/-- **Non-vacuity.** The round-to-nearest tables at schedule `S` are faithful. -/
theorem idealRoundedTablesAt_faithful (S : StepSchedule)
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hexec : spec.PaperExecutableValid) :
    TablesFaithfulAt S (idealRoundedTablesAt S spec) spec := by
  induction hvalid with
  | base p R =>
    cases hexec with
    | @base p K hp hK =>
      dsimp only [idealRoundedTablesAt]
      rw [nat_log2_two_pow]
      refine TablesFaithfulAt.base p K _ hp hK (fun s hs u hu => ?_)
      rw [array_getD_ofFn_of_lt K _ #[] s hs, read1D_ofFn_of_lt (2 ^ (s + 1)) _ hu,
          toScaledComplex_realQuantizeInt_pair]
      have h1 := norm_complexQuantize_sub_le (S.qLeaf p K)
        (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ)))
      have hq_nonneg : 0 ≤ complexQuantizeMaxErr (S.qLeaf p K) := by
        unfold complexQuantizeMaxErr; positivity
      linarith
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p
      hchild hv1 hv1_lt ih =>
    cases hexec with
    | step hv1_eq hchild_exec =>
      dsimp only [idealRoundedTablesAt]
      set α := alphaSchedule (pWork p K)
      set pSub := S.pSub p K
      set m1 := S.m1 p K
      have hqSub_nonneg : 0 ≤ complexQuantizeMaxErr pSub := by
        unfold complexQuantizeMaxErr; positivity
      refine TablesFaithfulAt.step p K t1 r c1 v1Of _ _ _ _ _ _ child hv1_eq
        (fun j1 hj1 => ?_) (fun k2 hk2 => ?_) (fun k2 hk2 => ?_) (fun u2 hu2 => ?_)
        (ih hchild_exec)
      · refine ⟨fun s => quantizeInt pSub (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))),
          ?_, ?_, ?_⟩
        · rw [array_getD_ofFn_of_lt t1 _ [] j1 hj1]
          rfl
        · intro s _
          have h1 := abs_quantizeReal_sub_le pSub
            (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
          have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pSub : ℤ)) := zpow_pos (by norm_num) _
          dsimp [quantizeReal] at h1
          linarith
        · intro s _
          show (quantizeInt pSub
            (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))).natAbs ≤ 2 ^ pSub + 1
          have h1 := natAbs_quantizeInt_le pSub 1
            (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
            (by simpa using abs_sincGaussian_le_one α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
          omega
      · rw [read1D_ofFn_of_lt r _ hk2, toScaledComplex_realQuantizeInt_pair]
        have h1 := norm_complexQuantize_sub_le pSub (zetaRoot r (k2 : ℝ))
        linarith
      · rw [read1D_ofFn_of_lt r _ hk2, toScaledComplex_realQuantizeInt_pair]
        have h1 := norm_complexQuantize_sub_le pSub (zetaRoot r (-(k2 : ℝ)))
        linarith
      · dsimp only
        rw [read1D_ofFn_of_lt r _ hu2, read1D_ofFn_of_lt r _ hu2]
        exact idealRounded_c01_faithful pSub p K r u2 hr hu2

#assert_std_axioms TablesFaithfulAt.p_eq tablesFaithfulAt_snapshot_iff idealRounded_c01_faithful
  idealRoundedTablesAt_faithful

end WP.W14
