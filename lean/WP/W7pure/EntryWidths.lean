import WP.W7pure.Basic

/-!
# WP.W7pure.EntryWidths — `W7_entryWidths_of_faithful`: faithful snapshot tables meet the widths

`W7_entryWidths_of_faithful` (Contracts/W7/Shapes.lean:134): for `8 ≤ p`, `K ≤ 2^(L+1)` and every
`cSpec` with `TablesFaithful cSpec (buildQuantizedSpecPaperStop L p K)`,
`W7.EntryWidths W7.snapshotFormat cSpec`.

Proof: induction on `TablesFaithful` (FTP:36), carrying `W8.ColumnDivisorsPos`, which W6 proves for
every valid faithful hierarchy (`W8_columnDivisor_pos_of_faithful_holds`; validity is PSR:77).

| field | width | from |
|---|---|---|
| leaf twiddles | `q_leaf + 3`, `q_leaf = 2p + K + 8` | `htw` (precision `2p+K+8`, FTP:40) and `‖stdChar‖ = 1` |
| folded taps | `2·pSub = 4p′` | `hTaps`, `|G s| ≤ 2^pSub + 1`, CTB:324 `fitsSignedScalarWord_fold_sum` (`p′ ≥ 12`) |
| pre/post twiddles | `pSub + 3` | `hPre`/`hPost` and `‖zetaRoot‖ = 1` |
| `c0`, `c1` | real, `≥ 0`, `pSub + 3` bits | `hC01`: `.2 = 0`, `0 ≤ .1 ≤ 2^(pSub+2)` |
| column divisor | `> 0` | `W8.ColumnDivisorsPos` |

Twiddle width (`twiddle_bitLen_le`): `‖z/2^(q+2) − ζ‖ ≤ 2·cqme q < 1` with `‖ζ‖ = 1` gives
`|z.j| < 2·2^(q+2) = 2^(q+3)`.
-/

namespace WP.W7pure

open TMFw.Contracts IntMul

/-- `2·complexQuantizeMaxErr q < 1` (it is `< 0.708·2^(-q)`). -/
theorem two_mul_cqme_lt_one (q : ℕ) : 2 * complexQuantizeMaxErr q < 1 := by
  have h1 := complexQuantizeMaxErr_lt q
  have h2 : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  linarith

/-- **Twiddle width.** An entry within `2·cqme q` of a unit complex number (at scale `2^(q+2)`) has
both components below `2^(q+3)` in magnitude. -/
theorem twiddle_bitLen_le (q : ℕ) (z : ℤ × ℤ) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (h : ‖toScaledComplex q z - ζ‖ ≤ 2 * complexQuantizeMaxErr q) :
    bitLen z.1.natAbs ≤ q + 3 ∧ bitLen z.2.natAbs ≤ q + 3 := by
  have hc := two_mul_cqme_lt_one q
  have hn : ‖toScaledComplex q z‖ < 2 := by
    calc ‖toScaledComplex q z‖ = ‖(toScaledComplex q z - ζ) + ζ‖ := by rw [sub_add_cancel]
      _ ≤ ‖toScaledComplex q z - ζ‖ + ‖ζ‖ := norm_add_le _ _
      _ < 2 := by linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (q + 2) := by positivity
  have hpow : (2 : ℝ) * (2 : ℝ) ^ (q + 2) = (2 : ℝ) ^ (q + 3) := by ring
  -- `|x| / 2^(q+2) < 2` gives `x.natAbs < 2^(q+3)`.
  have key : ∀ x : ℤ, |(x : ℝ) / (2 : ℝ) ^ (q + 2)| ≤ ‖toScaledComplex q z‖ →
      bitLen x.natAbs ≤ q + 3 := by
    intro x hx
    rw [abs_div, abs_of_pos hpos] at hx
    have h3 : |(x : ℝ)| < (2 : ℝ) ^ (q + 3) := by
      rw [← hpow]
      exact (div_lt_iff₀ hpos).1 (lt_of_le_of_lt hx hn)
    have h4 : ((x.natAbs : ℕ) : ℝ) < ((2 ^ (q + 3) : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      exact h3
    exact bitLen_le_of_lt (by exact_mod_cast h4)
  exact ⟨key z.1 (Complex.abs_re_le_norm (toScaledComplex q z)),
    key z.2 (Complex.abs_im_le_norm (toScaledComplex q z))⟩

/-- **Widths of faithful tables**, given positive column divisors. -/
theorem entryWidths_of_faithful_aux {cSpec : ComputablePaperFastDFTSpec}
    {spec : QuantizedFastDFTSpec} (h : TablesFaithful cSpec spec) :
    IntMulTM.Contracts.W8.ColumnDivisorsPos cSpec → W7.EntryWidths W7.snapshotFormat cSpec := by
  induction h with
  | base p K twiddles hp hK htw =>
    intro _
    simp only [W7.EntryWidths]
    intro s hs u hu
    exact twiddle_bitLen_le (2 * p + K + 8) _ _ (norm_stdChar _) (htw s hs u hu)
  | step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
      hv1_eq hTaps hPre hPost hC01 hChild ih =>
    intro hpos
    simp only [IntMulTM.Contracts.W8.ColumnDivisorsPos] at hpos
    obtain ⟨hdiv, hposC⟩ := hpos
    simp only [W7.EntryWidths]
    refine ⟨?_, ?_, ?_, ih hposC⟩
    · intro j1 hj1 g hg
      obtain ⟨G, hrow, -, hG⟩ := hTaps j1 hj1
      rw [hrow] at hg
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hg
      have hp' : 12 ≤ pChild p K := by rw [pChild_eq_additive]; omega
      have hfit := fitsSignedScalarWord_fold_sum (pChild p K) (2 * pChild p K)
        (effectiveFilterWidth (2 * pChild p K) r) u G hp' rfl hG
      exact le_trans (bitLen_natAbs_le_of_fits hfit) (by omega)
    · intro k2 hk2
      obtain ⟨h1, h2⟩ := twiddle_bitLen_le _ _ _ (norm_zetaRoot r _) (hPre k2 hk2)
      obtain ⟨h3, h4⟩ := twiddle_bitLen_le _ _ _ (norm_zetaRoot r _) (hPost k2 hk2)
      exact ⟨h1, h2, h3, h4⟩
    · intro u2 hu2
      obtain ⟨h0im, h1im, h0nn, h0le, h1nn, h1le, -, -, -, -, -⟩ := hC01 u2 hu2
      have hb0 := bitLen_natAbs_le_of_nonneg_le h0nn h0le
      have hb1 := bitLen_natAbs_le_of_nonneg_le h1nn h1le
      exact ⟨h0im, h1im, h0nn, by omega, h1nn, by omega, hdiv u2 hu2⟩

/-- **W7_entryWidths_of_faithful** (Contracts/W7/Shapes.lean:134). -/
theorem W7_entryWidths_of_faithful_holds : W7_entryWidths_of_faithful := by
  intro L p K hp _ cSpec hfaith
  have hvalid := buildQuantizedSpecPaperStop_valid L p K hp
  exact entryWidths_of_faithful_aux hfaith
    (IntMulTM.Contracts.W8_columnDivisor_pos_of_faithful_holds cSpec _ hvalid hfaith)

#assert_std_axioms two_mul_cqme_lt_one twiddle_bitLen_le entryWidths_of_faithful_aux
  W7_entryWidths_of_faithful_holds

end WP.W7pure
