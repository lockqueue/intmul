import WP.W7k3t.Vals

/-!
# WP.W7k3t.Widths — operand widths of the tap kernel, from the snapshot's width certificate
(contributed by W9h)

The snapshot certifies (`IntMul.computableSincGaussianTapWithProgramCost_widths_sound`, CTr:3915)
that every operand of the tap evaluator fits a signed `w`-bit word, `w = 181·pSub + 2·p_work +
2·log₂ t1 + 280`. With `bitLen_le_of_fits` this gives `bitLen ≤ w`; products of two certified
operands have `bitLen ≤ 2w`; the machine bound is `tapW = 2w + 8`.

* `tap_widths_setup`: the setup operands (numerators, denominators, threshold).
* `tap_widths_else`: under the non-clamp condition, the two clamped series (`SerW`), the clamps,
  their product and the final rounding.
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-! ## Parameters of the snapshot evaluator -/

theorem w9h_eN (pSub : ℕ) : 4 * (4 * (pSub + 1)) + (pSub + 2) + 4 = 17 * pSub + 22 := by ring
theorem w9h_eBint (pSub : ℕ) :
    pSub + 2 + 2 * (17 * pSub + 22) + 2 * (4 * (pSub + 1)) + 6 = 43 * pSub + 60 := by ring
theorem w9h_eBc (pSub : ℕ) : pSub + 2 + (17 * pSub + 22) + 3 * (4 * (pSub + 1)) + 6 = 30 * pSub + 42 := by
  ring

theorem tapPrec_eq' (pSub : ℕ) : W7.tapPrec pSub = 30 * pSub + 42 := by
  unfold W7.tapPrec
  ring

/-! ## Conversions -/

theorem bitLen_of_fits_nat {w n : ℕ} (h : IntMul.FitsSignedScalarWord w (n : ℤ)) : bitLen n ≤ w := by
  have := bitLen_le_of_fits h
  simpa using this

theorem bitLen_of_fits_neg_nat {w n : ℕ} (h : IntMul.FitsSignedScalarWord w (-(n : ℤ))) :
    bitLen n ≤ w := by
  have := bitLen_le_of_fits h
  simpa using this

/-- The snapshot's rounding is the contracts' rounding. -/
theorem divRound_eq_contracts : IntMul.divRoundRatInt = divRoundRatInt := rfl

/-- `|divRound n d| ≤ |n|` for `d ≥ 1`. -/
theorem natAbs_divRound_le (n d : ℤ) (hd : 1 ≤ d) :
    (IntMul.divRoundRatInt n d).natAbs ≤ n.natAbs := by
  unfold IntMul.divRoundRatInt
  rw [if_pos (by omega)]
  have h2d : (0 : ℤ) < 2 * d := by omega
  have h1 := Int.ediv_mul_le (2 * n + d) (ne_of_gt h2d)
  have h2 := Int.lt_ediv_add_one_mul_self (2 * n + d) h2d
  generalize (2 * n + d) / (2 * d) = q at h1 h2 ⊢
  rw [← Int.ofNat_le, Int.natCast_natAbs, Int.natCast_natAbs, abs_le]
  rcases le_or_gt 0 n with hn | hn
  · have hq0 : 0 ≤ q := by
      by_contra hc
      have hq1 : q + 1 ≤ 0 := by omega
      nlinarith
    have hqn : q ≤ n := by
      by_contra hc
      have hq1 : n + 1 ≤ q := by omega
      nlinarith
    rw [abs_of_nonneg hn]
    constructor <;> linarith
  · have hq0 : q ≤ 0 := by
      by_contra hc
      have hq1 : 1 ≤ q := by omega
      nlinarith
    have hqn : n ≤ q := by
      by_contra hc
      have hq1 : q + 1 ≤ n := by omega
      nlinarith
    rw [abs_of_neg hn]
    constructor <;> linarith

/-! ## Setup widths -/

theorem tap_widths_setup (p_work pSub t1 j1 s : ℕ) (hp : 0 < p_work) (hpS : 0 < pSub)
    (ht1 : 0 < t1) (hj1 : j1 < t1) (hs : s < 2 * pSub + 1) :
    let W := tapW p_work pSub t1
    let πN := (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1.toNat
    let lnN := (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1.toNat
    let numT := numTV pSub t1 j1 s
    let NY := πN * numT * (πN * numT)
    let DY := denYV p_work pSub t1 lnN
    43 * pSub + 61 ≤ W ∧ bitLen p_work ≤ W ∧ bitLen t1 ≤ W ∧ bitLen j1 ≤ W ∧ bitLen s ≤ W ∧
    bitLen (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)).natAbs ≤ W ∧ bitLen numT ≤ W ∧
    bitLen πN ≤ W ∧ bitLen (πN * numT) ≤ W ∧ bitLen NY ≤ W ∧
    bitLen (4 * p_work) ≤ W ∧ bitLen lnN ≤ W ∧ bitLen (4 * p_work * lnN) ≤ W ∧
    bitLen (t1 * t1) ≤ W ∧ bitLen (4 * p_work * lnN * (t1 * t1)) ≤ W ∧ bitLen DY ≤ W ∧
    bitLen ((pSub + 4) * DY) ≤ W := by
  have h := IntMul.computableSincGaussianTapWithProgramCost_widths_sound p_work pSub t1 j1 s hp hpS
    ht1 hj1 hs
  unfold IntMul.SincGaussianTapWidthSound at h
  dsimp only at h
  rw [w9h_eN] at h
  rw [w9h_eBint, w9h_eBc, show pSub + 2 + 2 = pSub + 4 by omega] at h
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := h
  have b1 := bitLen_le_of_fits h1
  have b2 := bitLen_of_fits_nat h2
  have b3 := bitLen_of_fits_nat h3
  have b4 := bitLen_of_fits_nat h4
  have b5 := bitLen_of_fits_nat h5
  have b7 := bitLen_of_fits_nat h7
  have b8 := bitLen_of_fits_nat h8
  have b9 := bitLen_of_fits_nat h9
  have b10 := bitLen_of_fits_nat h10
  have b11 := bitLen_of_fits_nat h11
  have b12 := bitLen_of_fits_nat h12
  rw [sq] at b10 b12
  dsimp only
  simp only [tapPrec_eq', numTV, denYV, tapW]
  have m6 : bitLen (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)).natAbs ≤
      bitLen ((s : ℤ) - (pSub : ℤ)).natAbs + bitLen t1 := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact bitLen_mul_le _ _
  have hj : bitLen j1 ≤ bitLen t1 := bitLen_mono hj1.le
  have hps := bitLen_le_self p_work
  have hss := bitLen_le_self s
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    le_trans (bitLen_mul_le _ _) (by omega), by omega, by omega, by omega, by omega,
    le_trans (bitLen_mul_le _ _) (by omega), by omega,
    le_trans (bitLen_mul_le _ _) (by omega)⟩

/-! ## Else-branch widths -/

/-- One clamped series from the snapshot's call-site certificate (the term `a_N`, not covered by the
certificate, by `|divRound n d| ≤ |n|`; the sum `s_N` from the certified `s_N·2^B`). -/
theorem serW_of_snap {w W pSub NY d : ℕ} {g : ℕ → ℕ} (hwW : w ≤ W)
    (hR : IntMul.RecurrenceCallSitesWidthSound w ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ)) d
      (fun _ => 1) g (17 * pSub + 22))
    (hy : IntMul.FitsSignedScalarWord w ((serV g pSub NY d).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ)))
    (hr : IntMul.FitsSignedScalarWord w (divRoundRatInt ((serV g pSub NY d).2 *
      ((2 ^ (pSub + 2) : ℕ) : ℤ)) ((2 ^ (43 * pSub + 60) : ℕ) : ℤ)))
    (hpos : ∀ k < 17 * pSub + 22, 0 < g k * d) :
    SerW W g pSub NY d := by
  unfold IntMul.RecurrenceCallSitesWidthSound at hR
  obtain ⟨hc, hd, hk⟩ := hR
  simp only [WP.W7k2.runRecurrenceSeriesCosted_fst_eq] at hk
  refine ⟨le_trans (bitLen_of_fits_neg_nat hc) hwW, le_trans (bitLen_of_fits_nat hd) hwW, ?_, ?_,
    ?_, ?_, hpos, le_trans (bitLen_le_of_fits hy) hwW, le_trans (bitLen_le_of_fits hr) hwW⟩
  · intro k hk'
    rcases Nat.lt_or_ge k (17 * pSub + 22) with hlt | hge
    · exact le_trans (bitLen_le_of_fits (hk k hlt).1) hwW
    · obtain rfl : k = 17 * pSub + 21 + 1 := by omega
      rw [serState_succ]
      unfold serStep
      have hd1 : (1 : ℤ) ≤ ((g (17 * pSub + 21) : ℕ) : ℤ) * (d : ℤ) := by
        have h0 : 1 ≤ g (17 * pSub + 21) * d := hpos (17 * pSub + 21) (by omega)
        exact_mod_cast h0
      have h6 := (hk (17 * pSub + 21) (by omega)).2.2.2.2.2.1
      exact le_trans (bitLen_mono (natAbs_divRound_le _ _ hd1))
        (le_trans (bitLen_le_of_fits h6) hwW)
  · intro k hk'
    rcases Nat.lt_or_ge k (17 * pSub + 22) with hlt | hge
    · exact le_trans (bitLen_le_of_fits (hk k hlt).2.1) hwW
    · obtain rfl : k = 17 * pSub + 22 := by omega
      have hle : ((serV g pSub NY d).2).natAbs ≤
          ((serV g pSub NY d).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ)).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      exact le_trans (bitLen_mono hle) (le_trans (bitLen_le_of_fits hy) hwW)
  · intro k hlt
    exact le_trans (bitLen_le_of_fits (hk k hlt).2.2.2.2.1) hwW
  · intro k hlt
    have h7 := bitLen_le_of_fits (hk k hlt).2.2.2.2.2.2
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h7
    exact le_trans h7 hwW

/-- The else-branch widths from the certificate pieces, over opaque values (no snapshot evaluator
in sight, so no expensive unfolding). -/
theorem else_of_cert {w W pSub NY DY D : ℕ} (hwW : 2 * w ≤ W) (hD : bitLen D ≤ w)
    (hR1 : IntMul.RecurrenceCallSitesWidthSound w ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ))
      (D * D) (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) (17 * pSub + 22))
    (hy1 : IntMul.FitsSignedScalarWord w
      ((serV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D)).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ)))
    (hr1 : IntMul.FitsSignedScalarWord w (divRoundRatInt
      ((serV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D)).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ))
      ((2 ^ (43 * pSub + 60) : ℕ) : ℤ)))
    (hR2 : IntMul.RecurrenceCallSitesWidthSound w ((2 ^ (43 * pSub + 60) : ℕ) : ℤ) (-(NY : ℤ))
      DY (fun _ => 1) (fun k => k + 1) (17 * pSub + 22))
    (hy2 : IntMul.FitsSignedScalarWord w
      ((serV (fun k => k + 1) pSub NY DY).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ)))
    (hr2 : IntMul.FitsSignedScalarWord w (divRoundRatInt
      ((serV (fun k => k + 1) pSub NY DY).2 * ((2 ^ (pSub + 2) : ℕ) : ℤ))
      ((2 ^ (43 * pSub + 60) : ℕ) : ℤ)))
    (hsi : IntMul.FitsSignedScalarWord w
      (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D)))
    (hei : IntMul.FitsSignedScalarWord w (clampSerV (fun k => k + 1) pSub NY DY))
    (hpr : IntMul.FitsSignedScalarWord w
      (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D) *
        clampSerV (fun k => k + 1) pSub NY DY * ((2 ^ pSub : ℕ) : ℤ)))
    (hrd : IntMul.FitsSignedScalarWord w (divRoundRatInt
      (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D) *
        clampSerV (fun k => k + 1) pSub NY DY * ((2 ^ pSub : ℕ) : ℤ))
      ((2 ^ (2 * pSub + 4) : ℕ) : ℤ)))
    (hDpos : 0 < D) (hDY : 0 < DY) :
    bitLen D ≤ W ∧ bitLen (D * D) ≤ W ∧
    SerW W (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D) ∧
    SerW W (fun k => k + 1) pSub NY DY ∧
    bitLen (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D)).natAbs ≤ W ∧
    bitLen (clampSerV (fun k => k + 1) pSub NY DY).natAbs ≤ W ∧
    bitLen (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D) *
      clampSerV (fun k => k + 1) pSub NY DY).natAbs ≤ W ∧
    bitLen (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D) *
      clampSerV (fun k => k + 1) pSub NY DY * ((2 ^ pSub : ℕ) : ℤ)).natAbs ≤ W ∧
    bitLen (divRoundRatInt (clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D) *
      clampSerV (fun k => k + 1) pSub NY DY * ((2 ^ pSub : ℕ) : ℤ))
      ((2 ^ (2 * pSub + 4) : ℕ) : ℤ)).natAbs ≤ W := by
  have bs := bitLen_le_of_fits hsi
  have be := bitLen_le_of_fits hei
  refine ⟨by omega, le_trans (bitLen_mul_le _ _) (by omega),
    serW_of_snap (by omega) hR1 hy1 hr1 (fun k _ => Nat.mul_pos (by positivity) (Nat.mul_pos hDpos hDpos)),
    serW_of_snap (by omega) hR2 hy2 hr2 (fun k _ => Nat.mul_pos (Nat.succ_pos k) hDY),
    by omega, by omega, ?_,
    le_trans (bitLen_le_of_fits hpr) (by omega), le_trans (bitLen_le_of_fits hrd) (by omega)⟩
  rw [Int.natAbs_mul]
  exact le_trans (bitLen_mul_le _ _) (by omega)

set_option maxHeartbeats 400000 in
theorem tap_widths_else (p_work pSub t1 j1 s : ℕ) (hp : 0 < p_work) (hpS : 0 < pSub)
    (ht1 : 0 < t1) (hj1 : j1 < t1) (hs : s < 2 * pSub + 1) :
    let W := tapW p_work pSub t1
    let πN := (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1.toNat
    let lnN := (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1.toNat
    let numT := numTV pSub t1 j1 s
    let NY := πN * numT * (πN * numT)
    let DY := denYV p_work pSub t1 lnN
    let D := denThV pSub t1
    let SV := clampSerV (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D)
    let EV := clampSerV (fun k => k + 1) pSub NY DY
    ¬ ((pSub + 4) * DY ≤ NY) →
    bitLen D ≤ W ∧ bitLen (D * D) ≤ W ∧
    SerW W (fun k => (2 * k + 2) * (2 * k + 3)) pSub NY (D * D) ∧ SerW W (fun k => k + 1) pSub NY DY ∧
    bitLen SV.natAbs ≤ W ∧ bitLen EV.natAbs ≤ W ∧ bitLen (SV * EV).natAbs ≤ W ∧
    bitLen (SV * EV * ((2 ^ pSub : ℕ) : ℤ)).natAbs ≤ W ∧
    bitLen (divRoundRatInt (SV * EV * ((2 ^ pSub : ℕ) : ℤ))
      ((2 ^ (2 * pSub + 4) : ℕ) : ℤ)).natAbs ≤ W := by
  have h := IntMul.computableSincGaussianTapWithProgramCost_widths_sound p_work pSub t1 j1 s hp hpS
    ht1 hj1 hs
  unfold IntMul.SincGaussianTapWidthSound at h
  dsimp only at h
  rw [w9h_eN] at h
  rw [w9h_eBint, w9h_eBc, show pSub + 2 + 2 = pSub + 4 by omega,
    show 2 * (pSub + 2) = 2 * pSub + 4 by omega] at h
  simp only [IntMul.costedClampInt, WP.W7k2.runRecurrenceSeriesCosted_fst_eq, sq,
    divRound_eq_contracts] at h
  obtain ⟨-, -, -, -, -, -, -, h6, -, -, -, -, -, -, helse⟩ := h
  dsimp only
  simp only [tapPrec_eq', numTV, denYV, denThV, tapW]
  generalize (IntMul.computablePiScaledWithCost (30 * pSub + 42)).1.toNat = πN at helse ⊢
  generalize (IntMul.computableLog2ScaledWithCost (30 * pSub + 42)).1.toNat = lnN at helse ⊢
  intro hne
  obtain ⟨hR1, hy1, -, hr1, hR2, hy2, hr2, hsi, hei, hpr, -, hrd⟩ :=
    helse (fun hc => hne (by exact_mod_cast hc))
  have hD : 0 < t1 * 2 ^ (30 * pSub + 42) := Nat.mul_pos ht1 (Nat.two_pow_pos _)
  have hDY : 0 < 4 * p_work * lnN * (t1 * t1) * 2 ^ (30 * pSub + 42) := by
    rcases Nat.eq_zero_or_pos (4 * p_work * lnN * (t1 * t1) * 2 ^ (30 * pSub + 42)) with h0 | h0
    · exact absurd (by rw [h0, Nat.mul_zero]; exact Nat.zero_le _) hne
    · exact h0
  exact else_of_cert (by omega) (bitLen_of_fits_nat h6) hR1 hy1 hr1 hR2 hy2 hr2 hsi hei hpr hrd hD hDY

#assert_std_axioms w9h_eN w9h_eBint w9h_eBc tapPrec_eq' bitLen_of_fits_nat bitLen_of_fits_neg_nat
  divRound_eq_contracts natAbs_divRound_le tap_widths_setup serW_of_snap else_of_cert tap_widths_else

end WP.W7k3t
