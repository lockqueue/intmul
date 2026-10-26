import IntMul.ExecutableAlgorithm.IdealizedFastDFT

namespace IntMul

/-! ## Multi-Level Quantized Recursive `sincGaussianFastDFTQuantized` & End-to-End Root Pipeline Exact Recovery -/

/-- Unit-circle norm of `zetaRoot`: `‖zetaRoot r x‖ = 1`. -/
theorem norm_zetaRoot (r : ℕ) (x : ℝ) : ‖zetaRoot r x‖ = 1 := by
  unfold zetaRoot
  exact norm_stdChar _

/-- Nearest-integer scaled fixed-point integer at bit precision `q : ℕ`:
`quantizeInt q x = ⌊x * 2^q + 1/2⌋`. -/
noncomputable def quantizeInt (q : ℕ) (x : ℝ) : ℤ :=
  ⌊x * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋

/-- Fixed-point real quantization at bit precision `q : ℕ`:
`quantizeReal q x = (quantizeInt q x : ℝ) / 2^q`. -/
noncomputable def quantizeReal (q : ℕ) (x : ℝ) : ℝ :=
  (quantizeInt q x : ℝ) / (2 : ℝ) ^ q

/-- Fixed-point complex quantization at bit precision `q : ℕ`:
`quantizeComplex q z = ⟨quantizeReal q z.re, quantizeReal q z.im⟩`. -/
noncomputable def quantizeComplex (q : ℕ) (z : ℂ) : ℂ :=
  ⟨quantizeReal q z.re, quantizeReal q z.im⟩

/-- `quantizeReal (p + 2) x` is identically `realQuantize p x`. -/
theorem quantizeReal_add_two_eq_realQuantize (p : ℕ) (x : ℝ) :
    quantizeReal (p + 2) x = realQuantize p x := by
  unfold quantizeReal quantizeInt realQuantize
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- `quantizeComplex (p + 2) z` is identically `complexQuantize p z`. -/
theorem quantizeComplex_add_two_eq_complexQuantize (p : ℕ) (z : ℂ) :
    quantizeComplex (p + 2) z = complexQuantize p z := by
  unfold quantizeComplex complexQuantize
  rw [quantizeReal_add_two_eq_realQuantize, quantizeReal_add_two_eq_realQuantize]

/-- Rounding error of `quantizeReal q x`: `|quantizeReal q x - x| ≤ (1 / 2) * 2^{-q}`. -/
theorem abs_quantizeReal_sub_le (q : ℕ) (x : ℝ) :
    |quantizeReal q x - x| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
  unfold quantizeReal quantizeInt
  set scale : ℝ := (2 : ℝ) ^ q
  set inv_scale : ℝ := (2 : ℝ) ^ (-(q : ℤ))
  have h_inv_eq : scale⁻¹ = inv_scale := by
    dsimp [scale, inv_scale]
    rw [zpow_neg, zpow_natCast]
  rw [div_eq_mul_inv, h_inv_eq]
  have h_inv_pos : 0 < inv_scale := zpow_pos (by norm_num) _
  have h_mul : scale * inv_scale = 1 := by
    dsimp [scale, inv_scale]
    rw [← zpow_natCast (2 : ℝ) q, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        add_neg_cancel, zpow_zero]
  have h_diff : (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) * inv_scale - x =
      ((⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) - x * scale) * inv_scale := by
    calc (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) * inv_scale - x
        = (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) * inv_scale - x * (scale * inv_scale) := by
          rw [h_mul, mul_one]
      _ = ((⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) - x * scale) * inv_scale := by ring
  rw [h_diff, abs_mul, abs_of_pos h_inv_pos]
  have h_floor_le : (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) ≤ x * scale + (1 / 2 : ℝ) :=
    Int.floor_le (x * scale + (1 / 2 : ℝ))
  have h_lt_floor : x * scale + (1 / 2 : ℝ) - 1 < (⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) :=
    Int.sub_one_lt_floor (x * scale + (1 / 2 : ℝ))
  have h_abs_u : |(⌊x * scale + (1 / 2 : ℝ)⌋ : ℝ) - x * scale| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_mul_of_nonneg_right h_abs_u h_inv_pos.le

/-- Norm error of `quantizeComplex q z`:
`‖quantizeComplex q z - z‖ ≤ (2 : ℝ) ^ (-(q : ℤ))`. -/
theorem norm_quantizeComplex_sub_le (q : ℕ) (z : ℂ) :
    ‖quantizeComplex q z - z‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) := by
  have hnorm : ‖quantizeComplex q z - z‖ =
      Real.sqrt ((quantizeComplex q z - z).re ^ 2 + (quantizeComplex q z - z).im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    ring_nf
  have hre : (quantizeComplex q z - z).re = quantizeReal q z.re - z.re := rfl
  have him : (quantizeComplex q z - z).im = quantizeReal q z.im - z.im := rfl
  rw [hnorm, hre, him]
  have hδ : (0 : ℝ) ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by positivity
  have hbound := complex_rounding_norm_le
    (quantizeReal q z.re - z.re)
    (quantizeReal q z.im - z.im)
    ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) hδ
    (abs_quantizeReal_sub_le q z.re)
    (abs_quantizeReal_sub_le q z.im)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(q : ℤ)) := zpow_nonneg (by norm_num) _
  calc Real.sqrt ((quantizeReal q z.re - z.re) ^ 2 + (quantizeReal q z.im - z.im) ^ 2)
      ≤ Real.sqrt 2 * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) := hbound
    _ ≤ 2 * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) :=
        mul_le_mul_of_nonneg_right hsqrt2 (by positivity)
    _ = (2 : ℝ) ^ (-(q : ℤ)) := by ring

/-- Pointwise bound `|sincGaussian α t| ≤ 1` for all `α, t : ℝ`. -/
theorem abs_sincGaussian_le_one (α t : ℝ) : |sincGaussian α t| ≤ 1 := by
  unfold sincGaussian
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hsinc : |normSinc t| ≤ 1 := abs_realSinc_le_one t
  have hexp : Real.exp (-(Real.pi / α ^ 2) * t ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ Real.pi / α ^ 2 := div_nonneg Real.pi_pos.le (sq_nonneg α)
    have h2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hmul : 0 ≤ (Real.pi / α ^ 2) * t ^ 2 := mul_nonneg h1 h2
    linarith
  calc |normSinc t| * Real.exp (-(Real.pi / α ^ 2) * t ^ 2)
      ≤ 1 * 1 := mul_le_mul hsinc hexp (Real.exp_pos _).le zero_le_one
    _ = 1 := mul_one 1

/-- Single-tap quantized product perturbation bound: for `‖z‖ ≤ M`, `|w| ≤ 1`, and `1 ≤ M`,
`‖quantizeComplex q z * (quantizeReal q w : ℂ) - z * (w : ℂ)‖ ≤ 5 * 2^{-q} * M`. -/
theorem norm_quantizeComplex_mul_quantizeReal_sub_le
    (q : ℕ) (z : ℂ) (w M : ℝ) (hM1 : 1 ≤ M) (hz : ‖z‖ ≤ M) (hw : |w| ≤ 1) :
    ‖quantizeComplex q z * (quantizeReal q w : ℂ) - z * (w : ℂ)‖ ≤
      5 * (2 : ℝ) ^ (-(q : ℤ)) * M := by
  have hpow_le_one : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-(q : ℤ)) := zpow_nonneg (by norm_num) _
  have hpowM : 0 ≤ (2 : ℝ) ^ (-(q : ℤ)) * M := by positivity
  have hz_err : ‖quantizeComplex q z - z‖ ≤ (2 : ℝ) ^ (-(q : ℤ)) :=
    norm_quantizeComplex_sub_le q z
  have hw_err : ‖(quantizeReal q w : ℂ) - (w : ℂ)‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_quantizeReal_sub_le q w
  have hqw_norm : ‖(quantizeReal q w : ℂ)‖ ≤ 2 := by
    have htri := norm_add_le ((quantizeReal q w : ℂ) - (w : ℂ)) (w : ℂ)
    have hw_norm : ‖(w : ℂ)‖ = |w| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [sub_add_cancel, hw_norm] at htri
    linarith
  have hsplit :
      quantizeComplex q z * (quantizeReal q w : ℂ) - z * (w : ℂ) =
        (quantizeComplex q z - z) * (quantizeReal q w : ℂ) +
          z * ((quantizeReal q w : ℂ) - (w : ℂ)) := by ring
  rw [hsplit]
  have htri := norm_add_le
    ((quantizeComplex q z - z) * (quantizeReal q w : ℂ))
    (z * ((quantizeReal q w : ℂ) - (w : ℂ)))
  rw [norm_mul, norm_mul] at htri
  have h1 : ‖quantizeComplex q z - z‖ * ‖(quantizeReal q w : ℂ)‖ ≤
      2 * (2 : ℝ) ^ (-(q : ℤ)) * M := by
    calc ‖quantizeComplex q z - z‖ * ‖(quantizeReal q w : ℂ)‖
        ≤ (2 : ℝ) ^ (-(q : ℤ)) * 2 :=
          mul_le_mul hz_err hqw_norm (norm_nonneg _) hpow_nonneg
      _ = 2 * (2 : ℝ) ^ (-(q : ℤ)) * 1 := by ring
      _ ≤ 2 * (2 : ℝ) ^ (-(q : ℤ)) * M :=
          mul_le_mul_of_nonneg_left hM1 (by positivity)
  have h2 : ‖z‖ * ‖(quantizeReal q w : ℂ) - (w : ℂ)‖ ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * M := by
    calc ‖z‖ * ‖(quantizeReal q w : ℂ) - (w : ℂ)‖
        ≤ M * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) :=
          mul_le_mul hz hw_err (norm_nonneg _) (by linarith)
      _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) * M := by ring
  linarith

/-- Quantized real-part cyclic-padded row vector of length `r + 2 * m1` for row `j1` of the
Sinc-Gaussian spreading step (`[MS]` §6.2, Theorem 6.3). -/
noncomputable def kroneckerSpreadRowRe (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 : ℕ) : List ℤ :=
  (List.range (r + 2 * m1)).map (fun (i : ℕ) =>
    quantizeInt q (x (j1 + t1 * (((i : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat)).re)

/-- Quantized imaginary-part cyclic-padded row vector of length `r + 2 * m1` for row `j1` of the
Sinc-Gaussian spreading step (`[MS]` §6.2, Theorem 6.3). -/
noncomputable def kroneckerSpreadRowIm (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 : ℕ) : List ℤ :=
  (List.range (r + 2 * m1)).map (fun (i : ℕ) =>
    quantizeInt q (x (j1 + t1 * (((i : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat)).im)

/-- Quantized Sinc-Gaussian filter tap polynomial of length `2 * m1 + 1` for row `j1` (`[MS]` §6.2, Theorem 6.3). -/
noncomputable def kroneckerSpreadFilterTaps (α : ℝ) (q m1 t1 : ℕ) (j1 : ℕ) : List ℤ :=
  (List.range (2 * m1 + 1)).map (fun (s : ℕ) =>
    quantizeInt q (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))))

/-- Pre-folded quantized Sinc-Gaussian filter tap polynomial of length
`W_eff = effectiveFilterWidth m1 r ≤ r` for row `j1` (`[MS]` §6.2, Theorem 6.3).
Folds the `2 * m1 + 1` quantized filter taps modulo `W_eff`. -/
noncomputable def kroneckerSpreadFilterTapsFolded (α : ℝ) (q m1 t1 r : ℕ) (j1 : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun (u : ℕ) =>
    ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % W_eff = u),
      quantizeInt q (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))))

/-- Quantized real-part input block `b` of length `W_eff = effectiveFilterWidth m1 r`
for row `j1` of the Overlap-Add Sinc-Gaussian spreading step (`[MS]` §6.2, Theorem 6.3). -/
noncomputable def kroneckerSpreadRowBlockRe (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun (a : ℕ) =>
    if b * W_eff + a < r then
      quantizeInt q (x (j1 + t1 * (b * W_eff + a))).re
    else 0)

/-- Quantized imaginary-part input block `b` of length `W_eff = effectiveFilterWidth m1 r`
for row `j1` of the Overlap-Add Sinc-Gaussian spreading step (`[MS]` §6.2, Theorem 6.3). -/
noncomputable def kroneckerSpreadRowBlockIm (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun (a : ℕ) =>
    if b * W_eff + a < r then
      quantizeInt q (x (j1 + t1 * (b * W_eff + a))).im
    else 0)

/-- **Quantized Signed-Kronecker Overlap-Add Sinc-Gaussian Spread Array (`kroneckerSincGaussianSpreadArray`, `[MS]` §6.2, Theorem 6.3)**:
Computes the 2D spread array `U(j_1, k_2)` for each row `j_1` by:
1. Pre-folding the `2 * m_1 + 1` quantized Sinc-Gaussian filter taps modulo `W_eff = effectiveFilterWidth m1 r`
   (`kroneckerSpreadFilterTapsFolded`),
2. Partitioning the row of length `r` into `kroneckerSpreadNumBlocks m1 r = ⌈r / W_eff⌉` blocks of
   length `W_eff` (`kroneckerSpreadRowBlockRe`, `kroneckerSpreadRowBlockIm`),
3. Multiplying each block with the pre-folded filter via `polyMulKroneckerSigned` at universal
   bit-stride `kroneckerBitStride`, and
4. Overlap-adding the acyclic block products modulo `r` and rescaling by `2^{-2q}`. -/
noncomputable def kroneckerSincGaussianSpreadArray
    (α : ℝ) (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) : ℂ :=
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let gTapFold := kroneckerSpreadFilterTapsFolded α q m1 t1 r j1
  let convRe : ℤ :=
    ∑ b ∈ Finset.range numBlocks,
      let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b
      let prodRe := polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold
      ∑ i ∈ (Finset.range (2 * W_eff)).filter
          (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
        prodRe.getD i 0
  let convIm : ℤ :=
    ∑ b ∈ Finset.range numBlocks,
      let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b
      let prodIm := polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold
      ∑ i ∈ (Finset.range (2 * W_eff)).filter
          (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
        prodIm.getD i 0
  let scale : ℝ := (2 : ℝ) ^ q * (2 : ℝ) ^ q
  ⟨(convRe : ℝ) / scale, (convIm : ℝ) / scale⟩

/-! Note: `polyMulInt_map_range_getD_eq_sum_range`, `sum_filter_polyMulInt_map_range_eq`,
`sum_range_mul_range`, `sum_blocks_eq_sum_range`, `sum_range_ite_emod_eq`, `sum_folded_filter_eq`,
and `overlapAdd_folded_polyMulInt_eq` are proved in `IntMul/Theorem4KroneckerSpread.lean`. -/

/-- **Exact Equivalence of `kroneckerSincGaussianSpreadArray` with the Quantized Windowed Sum (`[MS]` §6.2, Theorem 6.3)**:
For every `k2 < r`, `kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2` equals the exact sum over
`m ∈ [-m_1, m_1]` of the `q`-bit quantized input samples multiplied by the `q`-bit quantized
Sinc-Gaussian filter taps. -/
theorem kroneckerSincGaussianSpreadArray_eq_sum_Icc
    (α : ℝ) (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 k2 : ℕ) (hk2 : k2 < r) :
    kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2 =
      ∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
        quantizeComplex q (x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat)) *
          (quantizeReal q (sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))) : ℂ) := by
  unfold kroneckerSincGaussianSpreadArray
  dsimp only
  have hRe :
      (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          (polyMulKroneckerSigned
            (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1))
            (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
            (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)).getD i 0) =
      ∑ s ∈ Finset.range (2 * m1 + 1),
        quantizeInt q (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)).re *
          quantizeInt q (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))) := by
    have h1 :
        (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulKroneckerSigned
              (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1))
              (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)).getD i 0) =
        ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulInt (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)).getD i 0 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [polyMulKroneckerSigned_kroneckerBitStride_eq]
    rw [h1]
    exact overlapAdd_folded_polyMulInt_eq m1 r k2 hk2
      (fun j2 => quantizeInt q (x (j1 + t1 * j2)).re)
      (fun s => quantizeInt q (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))))
  have hIm :
      (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          (polyMulKroneckerSigned
            (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1))
            (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
            (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)).getD i 0) =
      ∑ s ∈ Finset.range (2 * m1 + 1),
        quantizeInt q (x (j1 + t1 * (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)).im *
          quantizeInt q (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))) := by
    have h1 :
        (∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulKroneckerSigned
              (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1))
              (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)).getD i 0) =
        ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
          ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
              (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
            (polyMulInt (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
              (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)).getD i 0 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [polyMulKroneckerSigned_kroneckerBitStride_eq]
    rw [h1]
    exact overlapAdd_folded_polyMulInt_eq m1 r k2 hk2
      (fun j2 => quantizeInt q (x (j1 + t1 * j2)).im)
      (fun s => quantizeInt q (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))))
  rw [hRe, hIm, sum_Icc_neg_eq_sum_range_two_mul_add_one m1]
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp [quantizeComplex, quantizeReal]
    push_cast
    ring
  · simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp [quantizeComplex, quantizeReal]
    push_cast
    ring

/-- Length of `kroneckerSpreadFilterTapsFolded` is `effectiveFilterWidth m1 r`. -/
@[simp]
theorem length_kroneckerSpreadFilterTapsFolded (α : ℝ) (q m1 t1 r j1 : ℕ) :
    (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1).length = effectiveFilterWidth m1 r := by
  simp [kroneckerSpreadFilterTapsFolded]

/-- Length of `kroneckerSpreadRowBlockRe` is `effectiveFilterWidth m1 r`. -/
@[simp]
theorem length_kroneckerSpreadRowBlockRe (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 b : ℕ) :
    (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length = effectiveFilterWidth m1 r := by
  simp [kroneckerSpreadRowBlockRe]

/-- Length of `kroneckerSpreadRowBlockIm` is `effectiveFilterWidth m1 r`. -/
@[simp]
theorem length_kroneckerSpreadRowBlockIm (q m1 t1 r : ℕ) (x : ℕ → ℂ) (j1 b : ℕ) :
    (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length = effectiveFilterWidth m1 r := by
  simp [kroneckerSpreadRowBlockIm]

/-- Magnitude bound for `quantizeInt q y`: if `|y| ≤ B` (`B : ℕ`), then
`(quantizeInt q y).natAbs ≤ B * 2 ^ q + 1`. -/
theorem natAbs_quantizeInt_le (q B : ℕ) (y : ℝ) (hy : |y| ≤ (B : ℝ)) :
    (quantizeInt q y).natAbs ≤ B * 2 ^ q + 1 := by
  unfold quantizeInt
  set z : ℤ := ⌊y * (2 : ℝ) ^ q + (1 / 2 : ℝ)⌋
  have h1 : -(B : ℝ) ≤ y ∧ y ≤ (B : ℝ) := abs_le.mp hy
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
  have hmul_hi : y * (2 : ℝ) ^ q ≤ (B : ℝ) * (2 : ℝ) ^ q :=
    mul_le_mul_of_nonneg_right h1.2 hpow
  have hmul_lo : -(B : ℝ) * (2 : ℝ) ^ q ≤ y * (2 : ℝ) ^ q := by
    nlinarith [h1.1, hpow]
  have hfloor_le : (z : ℝ) ≤ y * (2 : ℝ) ^ q + (1 / 2 : ℝ) :=
    Int.floor_le _
  have hfloor_gt : y * (2 : ℝ) ^ q + (1 / 2 : ℝ) - 1 < (z : ℝ) :=
    Int.sub_one_lt_floor _
  have hhi_real : (z : ℝ) ≤ (((B * 2 ^ q + 1 : ℕ) : ℤ) : ℝ) := by
    push_cast
    linarith
  have hlo_real : (-(((B * 2 ^ q + 1 : ℕ) : ℤ)) : ℝ) ≤ (z : ℝ) := by
    push_cast
    linarith
  have hhi_int : z ≤ ((B * 2 ^ q + 1 : ℕ) : ℤ) := by exact_mod_cast hhi_real
  have hlo_int : -((B * 2 ^ q + 1 : ℕ) : ℤ) ≤ z := by exact_mod_cast hlo_real
  omega

/-- Maximum coefficient magnitude of the pre-folded filter `kroneckerSpreadFilterTapsFolded`. -/
theorem listMaxNatAbs_kroneckerSpreadFilterTapsFolded_le (α : ℝ) (q m1 t1 r j1 : ℕ) :
    listMaxNatAbs (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) ≤
      (2 * m1 + 1) * (2 ^ q + 1) := by
  refine listMaxNatAbs_le _ _ fun c hc => ?_
  unfold kroneckerSpreadFilterTapsFolded at hc
  rcases List.mem_map.mp hc with ⟨u, _, rfl⟩
  have hsum := natAbs_sum_le
    ((Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u))
    (fun s => quantizeInt q (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ))))
    (2 ^ q + 1)
    (fun s _ => by
      have h1 := natAbs_quantizeInt_le q 1
        (sincGaussian α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
        (by simpa using abs_sincGaussian_le_one α (((s : ℤ) - (m1 : ℤ) : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
      omega)
  have hcard :
      ((Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u)).card ≤
        2 * m1 + 1 := by
    calc ((Finset.range (2 * m1 + 1)).filter _).card
        ≤ (Finset.range (2 * m1 + 1)).card := Finset.card_filter_le _ _
      _ = 2 * m1 + 1 := Finset.card_range _
  exact hsum.trans (Nat.mul_le_mul_right _ hcard)

/-- Maximum coefficient magnitude of a real-part input block `kroneckerSpreadRowBlockRe`. -/
theorem listMaxNatAbs_kroneckerSpreadRowBlockRe_le
    (q m1 t1 r B : ℕ) (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (B : ℝ))
    (j1 b : ℕ) (hj1 : j1 < t1) :
    listMaxNatAbs (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b) ≤ B * 2 ^ q + 1 := by
  refine listMaxNatAbs_le _ _ fun c hc => ?_
  unfold kroneckerSpreadRowBlockRe at hc
  rcases List.mem_map.mp hc with ⟨a, _, rfl⟩
  split_ifs with hlt
  · have hidx : j1 + t1 * (b * effectiveFilterWidth m1 r + a) < t1 * r := by
      have hle : b * effectiveFilterWidth m1 r + a + 1 ≤ r := hlt
      calc j1 + t1 * (b * effectiveFilterWidth m1 r + a)
          < t1 + t1 * (b * effectiveFilterWidth m1 r + a) := Nat.add_lt_add_right hj1 _
        _ = t1 * (b * effectiveFilterWidth m1 r + a + 1) := by ring
        _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
    have hre : |(x (j1 + t1 * (b * effectiveFilterWidth m1 r + a))).re| ≤ (B : ℝ) :=
      (Complex.abs_re_le_norm _).trans (hx _ hidx)
    exact natAbs_quantizeInt_le q B _ hre
  · simp

/-- Maximum coefficient magnitude of an imaginary-part input block `kroneckerSpreadRowBlockIm`. -/
theorem listMaxNatAbs_kroneckerSpreadRowBlockIm_le
    (q m1 t1 r B : ℕ) (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (B : ℝ))
    (j1 b : ℕ) (hj1 : j1 < t1) :
    listMaxNatAbs (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b) ≤ B * 2 ^ q + 1 := by
  refine listMaxNatAbs_le _ _ fun c hc => ?_
  unfold kroneckerSpreadRowBlockIm at hc
  rcases List.mem_map.mp hc with ⟨a, _, rfl⟩
  split_ifs with hlt
  · have hidx : j1 + t1 * (b * effectiveFilterWidth m1 r + a) < t1 * r := by
      have hle : b * effectiveFilterWidth m1 r + a + 1 ≤ r := hlt
      calc j1 + t1 * (b * effectiveFilterWidth m1 r + a)
          < t1 + t1 * (b * effectiveFilterWidth m1 r + a) := Nat.add_lt_add_right hj1 _
        _ = t1 * (b * effectiveFilterWidth m1 r + a + 1) := by ring
        _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
    have him : |(x (j1 + t1 * (b * effectiveFilterWidth m1 r + a))).im| ≤ (B : ℝ) :=
      (Complex.abs_im_le_norm _).trans (hx _ hidx)
    exact natAbs_quantizeInt_le q B _ him
  · simp

/-- **Actual Operand Bit-Stride Bound for Real-Part Overlap-Add Blocks (`kroneckerBitStride ≤ 6 * pChild p K`, `[MS]` §6.2, Theorem 6.3)**:
For `8 ≤ p`, `2 ≤ K`, `0 < r`, `p' = pChild p K`, `q = 2 * p'`, `m1 = 2 * p'`, and input `x`
bounded by `2^{p'}` on `0 .. t1 * r - 1`, every block `b` and row `j1 < t1` satisfies
`kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b) (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) ≤ 6 * p'`. -/
theorem kroneckerBitStride_kroneckerSpreadRowBlockRe_le
    (α : ℝ) (p K t1 r : ℕ) (hp : 8 ≤ p) (_hK : 2 ≤ K) (_hr : 0 < r)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K))
    (j1 b : ℕ) (hj1 : j1 < t1) (_hb : b < kroneckerSpreadNumBlocks (2 * pChild p K) r) :
    kroneckerBitStride
      (kroneckerSpreadRowBlockRe (2 * pChild p K) (2 * pChild p K) t1 r x j1 b)
      (kroneckerSpreadFilterTapsFolded α (2 * pChild p K) (2 * pChild p K) t1 r j1) ≤
        6 * pChild p K := by
  set p' := pChild p K
  have hp' : 17 ≤ p' := by
    unfold p' pChild pWork
    omega
  have hW : effectiveFilterWidth (2 * p') r ≤ 4 * p' + 1 := by
    have h1 := effectiveFilterWidth_le_full (2 * p') r
    omega
  have hx' : ∀ k < t1 * r, ‖x k‖ ≤ ((2 ^ p' : ℕ) : ℝ) := by
    intro k hk
    simpa using hx k hk
  have hf_max :
      listMaxNatAbs (kroneckerSpreadRowBlockRe (2 * p') (2 * p') t1 r x j1 b) ≤
        2 ^ (3 * p') + 1 := by
    have h1 := listMaxNatAbs_kroneckerSpreadRowBlockRe_le (2 * p') (2 * p') t1 r (2 ^ p') x hx' j1 b hj1
    have hpow : 2 ^ p' * 2 ^ (2 * p') = 2 ^ (3 * p') := by
      rw [← pow_add]
      congr 1
      omega
    omega
  have hg_max :
      listMaxNatAbs (kroneckerSpreadFilterTapsFolded α (2 * p') (2 * p') t1 r j1) ≤
        (4 * p' + 1) * (2 ^ (2 * p') + 1) := by
    have h1 := listMaxNatAbs_kroneckerSpreadFilterTapsFolded_le α (2 * p') (2 * p') t1 r j1
    have heq : 2 * (2 * p') + 1 = 4 * p' + 1 := by omega
    rwa [heq] at h1
  refine kroneckerBitStride_le_six_mul_of_bounds p' hp' _ _ ?_ ?_ hf_max hg_max
  · rw [length_kroneckerSpreadRowBlockRe]
    exact hW
  · rw [length_kroneckerSpreadFilterTapsFolded]
    exact hW

/-- **Actual Operand Bit-Stride Bound for Imaginary-Part Overlap-Add Blocks (`kroneckerBitStride ≤ 6 * pChild p K`, `[MS]` §6.2, Theorem 6.3)**:
For `8 ≤ p`, `2 ≤ K`, `0 < r`, `p' = pChild p K`, `q = 2 * p'`, `m1 = 2 * p'`, and input `x`
bounded by `2^{p'}` on `0 .. t1 * r - 1`, every block `b` and row `j1 < t1` satisfies
`kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b) (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) ≤ 6 * p'`. -/
theorem kroneckerBitStride_kroneckerSpreadRowBlockIm_le
    (α : ℝ) (p K t1 r : ℕ) (hp : 8 ≤ p) (_hK : 2 ≤ K) (_hr : 0 < r)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K))
    (j1 b : ℕ) (hj1 : j1 < t1) (_hb : b < kroneckerSpreadNumBlocks (2 * pChild p K) r) :
    kroneckerBitStride
      (kroneckerSpreadRowBlockIm (2 * pChild p K) (2 * pChild p K) t1 r x j1 b)
      (kroneckerSpreadFilterTapsFolded α (2 * pChild p K) (2 * pChild p K) t1 r j1) ≤
        6 * pChild p K := by
  set p' := pChild p K
  have hp' : 17 ≤ p' := by
    unfold p' pChild pWork
    omega
  have hW : effectiveFilterWidth (2 * p') r ≤ 4 * p' + 1 := by
    have h1 := effectiveFilterWidth_le_full (2 * p') r
    omega
  have hx' : ∀ k < t1 * r, ‖x k‖ ≤ ((2 ^ p' : ℕ) : ℝ) := by
    intro k hk
    simpa using hx k hk
  have hf_max :
      listMaxNatAbs (kroneckerSpreadRowBlockIm (2 * p') (2 * p') t1 r x j1 b) ≤
        2 ^ (3 * p') + 1 := by
    have h1 := listMaxNatAbs_kroneckerSpreadRowBlockIm_le (2 * p') (2 * p') t1 r (2 ^ p') x hx' j1 b hj1
    have hpow : 2 ^ p' * 2 ^ (2 * p') = 2 ^ (3 * p') := by
      rw [← pow_add]
      congr 1
      omega
    omega
  have hg_max :
      listMaxNatAbs (kroneckerSpreadFilterTapsFolded α (2 * p') (2 * p') t1 r j1) ≤
        (4 * p' + 1) * (2 ^ (2 * p') + 1) := by
    have h1 := listMaxNatAbs_kroneckerSpreadFilterTapsFolded_le α (2 * p') (2 * p') t1 r j1
    have heq : 2 * (2 * p') + 1 = 4 * p' + 1 := by omega
    rwa [heq] at h1
  refine kroneckerBitStride_le_six_mul_of_bounds p' hp' _ _ ?_ ?_ hf_max hg_max
  · rw [length_kroneckerSpreadRowBlockIm]
    exact hW
  · rw [length_kroneckerSpreadFilterTapsFolded]
    exact hW

/-- **Combined Overlap-Add Block Length and Bit-Stride Guarantee (`[MS]` §6.2, Theorem 6.3)**:
For `8 ≤ p`, `2 ≤ K`, `0 < r`, `p' = pChild p K`, `q = 2 * p'`, `m1 = 2 * p'`, and
`∀ k < t1 * r, ‖x k‖ ≤ 2^{p'}`, every row `j1 < t1` and block `b < kroneckerSpreadNumBlocks m1 r`
has block and folded-filter polynomial lengths equal to `effectiveFilterWidth m1 r` and actual
executed Kronecker bit-stride at most `6 * p'`. -/
theorem kroneckerSpreadBlock_length_and_bitStride_bounds
    (α : ℝ) (p K t1 r : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (hr : 0 < r)
    (x : ℕ → ℂ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K))
    (j1 b : ℕ) (hj1 : j1 < t1) (hb : b < kroneckerSpreadNumBlocks (2 * pChild p K) r) :
    let p' := pChild p K
    let q := 2 * p'
    let m1 := 2 * p'
    (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length = effectiveFilterWidth m1 r ∧
    (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length = effectiveFilterWidth m1 r ∧
    (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1).length = effectiveFilterWidth m1 r ∧
    kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
      (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) ≤ 6 * p' ∧
    kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
      (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) ≤ 6 * p' :=
  ⟨length_kroneckerSpreadRowBlockRe _ _ _ _ _ _ _,
   length_kroneckerSpreadRowBlockIm _ _ _ _ _ _ _,
   length_kroneckerSpreadFilterTapsFolded _ _ _ _ _ _,
   kroneckerBitStride_kroneckerSpreadRowBlockRe_le α p K t1 r hp hK hr x hx j1 b hj1 hb,
   kroneckerBitStride_kroneckerSpreadRowBlockIm_le α p K t1 r hp hK hr x hx j1 b hj1 hb⟩

/-- **Pointwise Error Bound Between `kroneckerSincGaussianSpreadArray` and `windowedSincGaussianSpreadArray` (Term B2, `[MS]` §6.2, Theorem 6.3 & §6.3, Lemma 6.5)**:
For any `k2 < r`, `1 ≤ M`, and input `x` bounded by `M` on `0 .. t1 * r - 1`,
`‖kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2 - windowedSincGaussianSpreadArray α m1 t1 r x j1 k2‖ ≤
  (2 * m1 + 1) * 5 * 2^{-q} * M`. -/
theorem norm_kroneckerSincGaussianSpreadArray_sub_windowed_le
    (α : ℝ) (q m1 t1 r : ℕ) (_ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) :
    ‖kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2 -
        windowedSincGaussianSpreadArray α m1 t1 r x j1 k2‖ ≤
      ((2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ))) * M := by
  rw [kroneckerSincGaussianSpreadArray_eq_sum_Icc α q m1 t1 r x j1 k2 hk2]
  unfold windowedSincGaussianSpreadArray
  rw [← Finset.sum_sub_distrib]
  have hcard : ((Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)).card : ℝ) = 2 * (m1 : ℝ) + 1 := by
    rw [Int.card_Icc]
    have h1 : ((m1 : ℤ) + 1 - -(m1 : ℤ)).toNat = 2 * m1 + 1 := by omega
    rw [h1]
    push_cast
    ring
  calc ‖∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
          (quantizeComplex q (x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat)) *
            (quantizeReal q (sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))) : ℂ) -
           x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat) *
            (sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)) : ℂ))‖
      ≤ ∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
          ‖quantizeComplex q (x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat)) *
            (quantizeReal q (sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ))) : ℂ) -
           x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat) *
            (sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), (5 * (2 : ℝ) ^ (-(q : ℤ)) * M) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have hidx_lt : j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat < t1 * r := by
          have hmod_lt : (((k2 : ℤ) - m) % (r : ℤ)).toNat < r := by
            have hr_int : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
            have h1 := Int.emod_lt_of_pos ((k2 : ℤ) - m) hr_int
            have h2 := Int.emod_nonneg ((k2 : ℤ) - m) hr_int.ne'
            omega
          have hle : (((k2 : ℤ) - m) % (r : ℤ)).toNat + 1 ≤ r := hmod_lt
          calc j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat
              < t1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat :=
                Nat.add_lt_add_right hj1 _
            _ = t1 * ((((k2 : ℤ) - m) % (r : ℤ)).toNat + 1) := by ring
            _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
        exact norm_quantizeComplex_mul_quantizeReal_sub_le q
          (x (j1 + t1 * (((k2 : ℤ) - m) % (r : ℤ)).toNat))
          (sincGaussian α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
          M hM1 (hx _ hidx_lt)
          (abs_sincGaussian_le_one α ((m : ℝ) - (j1 : ℝ) / (t1 : ℝ)))
    _ = ((Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)).card : ℝ) * (5 * (2 : ℝ) ^ (-(q : ℤ)) * M) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((2 * (m1 : ℝ) + 1) * 5 * (2 : ℝ) ^ (-(q : ℤ))) * M := by
        rw [hcard]
        ring

/-- Numerical bound `(2 * (2 * P) + 1) * 5 * 2^{-(2 * P)} < 0.1 * 2^{-P}` for all `12 ≤ P`. -/
theorem five_mul_four_mul_add_one_zpow_lt (P : ℕ) (hP : 12 ≤ P) :
    (2 * (2 * (P : ℝ)) + 1) * 5 * (2 : ℝ) ^ (-((2 * P : ℕ) : ℤ)) <
      (0.1 : ℝ) * (2 : ℝ) ^ (-(P : ℤ)) := by
  have hexp : ∀ d : ℕ, d + 1 ≤ 2 ^ d := by
    intro d
    induction d with
    | zero => decide
    | succ d ih =>
      have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      rw [pow_succ]
      omega
  have h1 : 4 * P + 1 ≤ 49 * 2 ^ (P - 12) := by
    have h2 := hexp (P - 12)
    have h3 : 1 ≤ 2 ^ (P - 12) := Nat.one_le_two_pow
    omega
  have h3 : (49 * 2 ^ (P - 12)) * 50 < 2 ^ P := by
    have hpow : 2 ^ P = 4096 * 2 ^ (P - 12) := by
      have heq : P = 12 + (P - 12) := by omega
      conv_lhs => rw [heq, pow_add]
      norm_num
    have hpos : 0 < 2 ^ (P - 12) := by positivity
    omega
  have hnat : ((4 * P + 1) * 5) * 10 < 2 ^ P := by omega
  have hreal : ((2 * (2 * (P : ℝ)) + 1) * 5) * 10 < (2 : ℝ) ^ (P : ℤ) := by
    rw [zpow_natCast]
    have hcast : ((2 * (2 * (P : ℝ)) + 1) * 5) * 10 = (((4 * P + 1) * 5 * 10 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast]
    exact_mod_cast hnat
  have hpow2 : (2 : ℝ) ^ (-((2 * P : ℕ) : ℤ)) = (2 : ℝ) ^ (-(P : ℤ)) * (2 : ℝ) ^ (-(P : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have hinv : (2 : ℝ) ^ (P : ℤ) * (2 : ℝ) ^ (-(P : ℤ)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  have hpos_negP : (0 : ℝ) < (2 : ℝ) ^ (-(P : ℤ)) := zpow_pos (by norm_num) _
  have hstep :
      (2 * (2 * (P : ℝ)) + 1) * 5 * (2 : ℝ) ^ (-(P : ℤ)) < (0.1 : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hreal hpos_negP
    rw [hinv] at hmul
    linarith
  rw [hpow2]
  calc (2 * (2 * (P : ℝ)) + 1) * 5 * ((2 : ℝ) ^ (-(P : ℤ)) * (2 : ℝ) ^ (-(P : ℤ)))
      = ((2 * (2 * (P : ℝ)) + 1) * 5 * (2 : ℝ) ^ (-(P : ℤ))) * (2 : ℝ) ^ (-(P : ℤ)) := by ring
    _ < (0.1 : ℝ) * (2 : ℝ) ^ (-(P : ℤ)) :=
        mul_lt_mul_of_pos_right hstep hpos_negP

/-- **Term B2 Bound (`< 0.1 * 2^{-p_child} * M`, `[MS]` §6.2, Theorem 6.3 & §6.3, Lemma 6.5)**:
At bit precision `q = 2 * pChild p K` and window half-width `m1 = 2 * pChild p K`, the quantization
and signed-Kronecker evaluation of the Sinc-Gaussian spread differs from the unquantized windowed
spread by strictly less than `0.1 * 2^{-pChild p K} * M`. -/
theorem norm_kroneckerSincGaussianSpreadArray_sub_windowed_lt
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) :
    ‖kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2 -
        windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2‖ <
      (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  have hM_pos : 0 < M := by linarith
  have hP12 : 12 ≤ pChild p K := by
    unfold pChild pWork
    omega
  have hle := norm_kroneckerSincGaussianSpreadArray_sub_windowed_le
    (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r ht1 hr
    x M hM1 hx j1 k2 hj1 hk2
  have hlt := five_mul_four_mul_add_one_zpow_lt (pChild p K) hP12
  have hcast : (2 * ((2 * pChild p K : ℕ) : ℝ) + 1) = 2 * (2 * (pChild p K : ℝ)) + 1 := by
    push_cast
    ring
  rw [hcast] at hle
  exact hle.trans_lt (mul_lt_mul_of_pos_right hlt hM_pos)

/-- **Combined Term B1 + B2 Pointwise Spread Error Bound (`< 0.5 * 2^{-p_child} * M`, `[MS]` §6.2, Theorem 6.3 & §6.3, Lemma 6.5)**:
The executed signed-Kronecker quantized spread `kroneckerSincGaussianSpreadArray` differs from the
ideal infinite-series spread `sincGaussianSpreadArray` by `< 0.5 * 2^{-pChild p K} * M`. -/
theorem norm_kroneckerSincGaussianSpreadArray_sub_lt
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) :
    ‖kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2 -
        sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2‖ <
      (0.5 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  have hM_pos : 0 < M := by linarith
  have hB2 := norm_kroneckerSincGaussianSpreadArray_sub_windowed_lt
    p K t1 r ht1 hr x M hM1 hx j1 k2 hj1 hk2
  have hB1 := norm_windowedSincGaussianSpreadArray_sub_lt
    p K t1 r ht1 hr x M hM_pos hx j1 k2 hj1
  have hsplit :
      kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2 -
        sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2 =
      (kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2 -
        windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2) +
      (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2 -
        sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2) := by ring
  rw [hsplit]
  have htri := norm_add_le
    (kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2 -
      windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2)
    (windowedSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) t1 r x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
  linarith

/-- **2D DFT Error Bound for `kroneckerSincGaussianSpreadArray` (Terms B1 + B2, `≤ 0.5 * 2^{-p_child} * M`, `[MS]` §§6.2–6.3)**:
Since `dft2D` is `ℓ_∞`-non-expansive on `t1 × r`, the 2D DFT of `kroneckerSincGaussianSpreadArray`
differs from the 2D DFT of the ideal infinite-series spread `sincGaussianSpreadArray` by at most
`0.5 * 2^{-pChild p K} * M`. -/
theorem norm_dft2D_kroneckerSincGaussianSpreadArray_sub_le
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u1 u2 : ℕ) :
    ‖dft2D t1 r (kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x) u1 u2 -
        dft2D t1 r (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x) u1 u2‖ ≤
      (0.5 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
  rw [← dft2D_sub]
  refine dft2D_norm_le t1 r ht1 hr _ _ (fun j1 hj1 k2 hk2 => ?_) u1 u2
  exact (norm_kroneckerSincGaussianSpreadArray_sub_lt p K t1 r ht1 hr x M hM1 hx j1 k2 hj1 hk2).le

/-- **Uniform Norm Bound for `kroneckerSincGaussianSpreadArray` (`≤ (r + 0.5) * M`, `[MS]` §§6.2–6.3)**:
For any `j1 < t1` and `k2 < r`, `‖kroneckerSincGaussianSpreadArray ... j1 k2‖ ≤ (r + 0.5) * M`. -/
theorem norm_kroneckerSincGaussianSpreadArray_le
    (p K t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) :
    ‖kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2‖ ≤
      ((r : ℝ) + (0.5 : ℝ)) * M := by
  have hα : 0 < alphaSchedule (pWork p K) := alphaSchedule_pos (pWork p K) (by unfold pWork; omega)
  have hdiff := (norm_kroneckerSincGaussianSpreadArray_sub_lt
    p K t1 r ht1 hr x M hM1 hx j1 k2 hj1 hk2).le
  have hinf := norm_sincGaussianSpreadArray_le
    (alphaSchedule (pWork p K)) hα t1 r hr x M hx j1 k2 hj1 hk2
  have hpow_le : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have htri := norm_add_le
    (kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x j1 k2 -
      sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
    (sincGaussianSpreadArray (alphaSchedule (pWork p K)) t1 r x j1 k2)
  rw [sub_add_cancel] at htri
  nlinarith

/-- `ℓ_∞` difference bound for `dft1D`: if `‖f j - g j‖ ≤ M` for all `j < R`, then
`‖dft1D R f u - dft1D R g u‖ ≤ M`. -/
theorem norm_dft1D_sub_le (R : ℕ) (hR : 0 < R) (f g : ℕ → ℂ) (M : ℝ)
    (hfg : ∀ j < R, ‖f j - g j‖ ≤ M) (u : ℕ) :
    ‖dft1D R f u - dft1D R g u‖ ≤ M := by
  have hsub : dft1D R f u - dft1D R g u = dft1D R (fun j => f j - g j) u := by
    unfold dft1D
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsub]
  exact dft1D_norm_le R hR (fun j => f j - g j) M (fun j hj => hfg j (Finset.mem_range.mp hj)) u

/-- Exact base-2 logarithm of a power of two: `Nat.log2 (2 ^ m) = m`. -/
theorem nat_log2_two_pow_early (m : ℕ) : Nat.log2 (2 ^ m) = m := by
  have hne : 2 ^ m ≠ 0 := by positivity
  have hle : m ≤ Nat.log2 (2 ^ m) := (Nat.le_log2 hne).mpr le_rfl
  have hlt : Nat.log2 (2 ^ m) < m + 1 :=
    (Nat.log2_lt hne).mpr (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self m))
  omega

/-- Whenever `t1 * r = 2 ^ K`, `t1` is an exact power of two `t1 = 2 ^ (Nat.log2 t1)` with
`Nat.log2 t1 ≤ K ≤ 2 ^ K`. -/
theorem two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow (t1 r K : ℕ) (hsize : t1 * r = 2 ^ K) :
    2 ^ (Nat.log2 t1) = t1 ∧ Nat.log2 t1 ≤ 2 ^ K := by
  have hdvd : t1 ∣ 2 ^ K := ⟨r, hsize.symm⟩
  obtain ⟨m, hmK, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [nat_log2_two_pow_early]
  refine ⟨rfl, hmK.trans ?_⟩
  have hlt : K < 2 ^ K := Nat.lt_two_pow_self
  omega

/-! Note: `syntheticFFTRadix2Quantized`, `norm_syntheticFFTRadix2Quantized_sub_le`,
`norm_syntheticFFTRadix2Quantized_le`, and `norm_syntheticFFTRadix2Quantized_sub_syntheticDFT_le`
are defined and proved in `IntMul/Theorem1TwistedDuality.lean`. -/

/-- Error bound of `complexQuantize (2 * pChild p K)` relative to `2^{-pChild p K}` and `2^{-p}`:
`complexQuantizeMaxErr (2 * pChild p K) < 0.001 * 2^{-pChild p K}` and
`complexQuantizeMaxErr (2 * pChild p K) < 0.001 * 2^{-p}`. -/
theorem complexQuantizeMaxErr_two_mul_pChild_lt (p K : ℕ) :
    complexQuantizeMaxErr (2 * pChild p K) < (0.001 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) ∧
    complexQuantizeMaxErr (2 * pChild p K) < (0.001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  have h1 := complexQuantizeMaxErr_lt (2 * pChild p K)
  have hP12 : 12 ≤ pChild p K := by
    unfold pChild pWork
    omega
  have hp_le : p ≤ pChild p K := by
    unfold pChild pWork
    omega
  have hzpow1 :
      (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) ≤
        (2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
    push_cast
    omega
  have hzpow2 :
      (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ (2 : ℝ) ^ (-(p : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h_first :
      complexQuantizeMaxErr (2 * pChild p K) < (0.001 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
    calc complexQuantizeMaxErr (2 * pChild p K)
        < (0.354 : ℝ) * (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) := h1
      _ ≤ (0.354 : ℝ) * ((2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) :=
          mul_le_mul_of_nonneg_left hzpow1 (by norm_num)
      _ = ((0.354 : ℝ) * (2 : ℝ) ^ (-12 : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by ring
      _ < (0.001 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
          mul_lt_mul_of_pos_right (by norm_num) (zpow_pos (by norm_num) _)
  refine ⟨h_first, ?_⟩
  exact h_first.trans_le (mul_le_mul_of_nonneg_left hzpow2 (by norm_num))

/-- For any `p, K, r : ℕ` with `r ≤ 2 ^ K`, since `pChild p K = p + 2 * K + 12 ≥ K + 12`,
`complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1) ≤ 0.01 * 2^{-pChild p K}`. -/
theorem complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow
    (p K r : ℕ) (hr : r ≤ 2 ^ K) :
    complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1) ≤
      (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
  have h1 : complexQuantizeMaxErr (2 * pChild p K) ≤
      (0.354 : ℝ) * (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) :=
    (complexQuantizeMaxErr_lt (2 * pChild p K)).le
  have hP_ge : K + 12 ≤ pChild p K := by
    unfold pChild pWork
    omega
  have hr_real : (r : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast hr
  have hpowK_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast (Nat.one_le_two_pow (n := K))
  have hr1_le : (r : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ (K : ℤ) := by linarith
  have hzpow :
      (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) ≤
        (2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
    push_cast
    omega
  have hcancel : (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (K : ℤ) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  calc complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1)
      ≤ ((0.354 : ℝ) * (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) * (2 * (2 : ℝ) ^ (K : ℤ)) :=
        mul_le_mul h1 hr1_le (by positivity) (by positivity)
    _ ≤ ((0.354 : ℝ) * ((2 : ℝ) ^ (-12 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)))) *
          (2 * (2 : ℝ) ^ (K : ℤ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzpow (by norm_num)) (by positivity)
    _ = ((0.354 : ℝ) * 2 * (2 : ℝ) ^ (-12 : ℤ)) *
          ((2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (K : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by ring
    _ = ((0.354 : ℝ) * 2 * (2 : ℝ) ^ (-12 : ℤ)) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
        rw [hcancel, mul_one]
    _ ≤ (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- For `8 ≤ p`, `2 ≤ K`, and `r ≤ 2 ^ ((K + 1) / 2)`,
`complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1) ≤ 0.01 * 2^{-pChild p K}`. -/
theorem complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le
    (p K r : ℕ) (_hp : 8 ≤ p) (_hK : 2 ≤ K) (hr : r ≤ 2 ^ ((K + 1) / 2)) :
    complexQuantizeMaxErr (2 * pChild p K) * ((r : ℝ) + 1) ≤
      (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) := by
  refine complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K r ?_
  exact hr.trans (Nat.pow_le_pow_right zero_lt_two (by omega))

/-- Monotonicity of `realQuantize p`: if `x ≤ y`, then `realQuantize p x ≤ realQuantize p y`. -/
theorem realQuantize_mono (p : ℕ) {x y : ℝ} (h : x ≤ y) :
    realQuantize p x ≤ realQuantize p y := by
  unfold realQuantize
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (p + 2) := by positivity
  have hinv : (0 : ℝ) ≤ (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) := by positivity
  have h1 : x * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ) ≤ y * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ) := by
    nlinarith
  have h2 : (⌊x * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ)⌋ : ℝ) ≤
      (⌊y * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ)⌋ : ℝ) := by
    exact_mod_cast Int.floor_mono h1
  exact mul_le_mul_of_nonneg_right h2 hinv

/-- Exact fixed point of `realQuantize p` at `0`: `realQuantize p 0 = 0`. -/
@[simp]
theorem realQuantize_zero (p : ℕ) : realQuantize p 0 = 0 := by
  unfold realQuantize
  have hfloor : ⌊(0 : ℝ) * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ)⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
  rw [hfloor]
  simp

/-- Exact fixed point of `realQuantize p` at `1`: `realQuantize p 1 = 1`. -/
@[simp]
theorem realQuantize_one (p : ℕ) : realQuantize p 1 = 1 := by
  unfold realQuantize
  set N : ℤ := (2 : ℤ) ^ (p + 2)
  have hrew : (1 : ℝ) * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ) = (1 / 2 : ℝ) + (N : ℝ) := by
    dsimp [N]
    push_cast
    ring
  have hfloor_half : ⌊(1 / 2 : ℝ)⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
  have hfloor : ⌊(1 : ℝ) * (2 : ℝ) ^ (p + 2) + (1 / 2 : ℝ)⌋ = N := by
    rw [hrew, Int.floor_add_intCast, hfloor_half, zero_add]
  rw [hfloor]
  dsimp [N]
  push_cast
  rw [← zpow_natCast (2 : ℝ) (p + 2), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hexp : ((p + 2 : ℕ) : ℤ) + -((p : ℤ) + 2) = 0 := by push_cast; ring
  rw [hexp, zpow_zero]

/-- If `x ∈ [0, 1]`, then `realQuantize p x ∈ [0, 1]`. -/
theorem realQuantize_mem_Icc_zero_one (p : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ realQuantize p x ∧ realQuantize p x ≤ 1 := by
  refine ⟨?_, ?_⟩
  · rw [← realQuantize_zero p]
    exact realQuantize_mono p hx0
  · rw [← realQuantize_one p]
    exact realQuantize_mono p hx1

/-- Norm of `(realQuantize p x : ℂ) - (x : ℂ)` is bounded by `realQuantizeMaxErr p ≤ complexQuantizeMaxErr p`. -/
theorem norm_realQuantize_coe_sub_le (p : ℕ) (x : ℝ) :
    ‖(realQuantize p x : ℂ) - (x : ℂ)‖ ≤ realQuantizeMaxErr p ∧
    ‖(realQuantize p x : ℂ) - (x : ℂ)‖ ≤ complexQuantizeMaxErr p := by
  have h1 : ‖(realQuantize p x : ℂ) - (x : ℂ)‖ = |realQuantize p x - x| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  have habs := abs_realQuantize_sub_le p x
  refine ⟨habs, habs.trans ?_⟩
  rw [realQuantizeMaxErr_eq, complexQuantizeMaxErr_eq]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hzpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p : ℤ)) := zpow_nonneg (by norm_num) _
  nlinarith

/-- Elementary power perturbation bound on `[-1, 1]`: for `|a| ≤ 1`, `|b| ≤ 1`, and `n : ℕ`,
`|a ^ n - b ^ n| ≤ n * |a - b|`. -/
theorem abs_pow_sub_pow_le (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (n : ℕ) :
    |a ^ n - b ^ n| ≤ (n : ℝ) * |a - b| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    have htri := abs_add_le (a * (a ^ n - b ^ n)) ((a - b) * b ^ n)
    rw [abs_mul, abs_mul, abs_pow] at htri
    have hbn : |b| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg b) hb
    have h1 : |a| * |a ^ n - b ^ n| ≤ 1 * ((n : ℝ) * |a - b|) :=
      mul_le_mul ha ih (abs_nonneg _) zero_le_one
    have h2 : |a - b| * |b| ^ n ≤ |a - b| * 1 :=
      mul_le_mul_of_nonneg_left hbn (abs_nonneg _)
    push_cast
    linarith

/-- Quotient perturbation bound when `0 ≤ b ≤ a` and `0 < M ≤ a, a_q`:
`|b_q / a_q - b / a| ≤ (|b_q - b| + |a_q - a|) / M`. -/
theorem abs_div_sub_div_le (a b a_q b_q M : ℝ)
    (hM : 0 < M) (ha : M ≤ a) (ha_q : M ≤ a_q)
    (hb_nonneg : 0 ≤ b) (hba : b ≤ a) :
    |b_q / a_q - b / a| ≤ (|b_q - b| + |a_q - a|) / M := by
  have ha_pos : 0 < a := lt_of_lt_of_le hM ha
  have ha_q_pos : 0 < a_q := lt_of_lt_of_le hM ha_q
  have hident : b_q / a_q - b / a = ((b_q - b) + (b / a) * (a - a_q)) / a_q := by
    field_simp [ha_pos.ne', ha_q_pos.ne']
    ring
  rw [hident, abs_div, abs_of_pos ha_q_pos]
  have hratio_abs : |b / a| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hb_nonneg ha_pos.le)]
    exact (div_le_one ha_pos).mpr hba
  have hnum : |(b_q - b) + (b / a) * (a - a_q)| ≤ |b_q - b| + |a_q - a| := by
    have htri := abs_add_le (b_q - b) ((b / a) * (a - a_q))
    rw [abs_mul, abs_sub_comm a a_q] at htri
    have hmul : |b / a| * |a_q - a| ≤ 1 * |a_q - a| :=
      mul_le_mul_of_nonneg_right hratio_abs (abs_nonneg _)
    linarith
  calc |(b_q - b) + (b / a) * (a - a_q)| / a_q
      ≤ (|b_q - b| + |a_q - a|) / a_q := div_le_div_of_nonneg_right hnum ha_q_pos.le
    _ ≤ (|b_q - b| + |a_q - a|) / M :=
        div_le_div_of_nonneg_left (by positivity) hM ha_q

/-- **Quantized Passband Coefficient Conditioning Bound (`quantized_coeff_ratio_pow_le`, `[MS]` §5.1)**:
For any `p, K, t1 : ℕ` with `t1 ≤ 2 ^ K` and any passband coefficients `a, b ∈ [0, 1]` satisfying
`0.49999999 ≤ a`, `b ≤ a`, and `(b / a) ^ t1 ≤ 0.15`, their quantized counterparts
`a_q = realQuantize (2 * pChild p K) a` and `b_q = realQuantize (2 * pChild p K) b` satisfy
`0.4999 ≤ a_q ≤ 1`, `0 ≤ b_q ≤ a_q`, and `(b_q / a_q) ^ t1 ≤ 0.1501`. -/
theorem quantized_coeff_ratio_pow_le
    (p K t1 : ℕ) (ht1_le : t1 ≤ 2 ^ K)
    (a b : ℝ) (ha_gt : (0.49999999 : ℝ) ≤ a) (ha_le : a ≤ 1)
    (hb_nonneg : 0 ≤ b) (hba : b ≤ a)
    (hratio : (b / a) ^ t1 ≤ (0.15 : ℝ)) :
    let q := 2 * pChild p K
    let a_q := realQuantize q a
    let b_q := realQuantize q b
    (0.4999 : ℝ) ≤ a_q ∧ a_q ≤ 1 ∧ 0 ≤ b_q ∧ b_q ≤ a_q ∧
      (b_q / a_q) ^ t1 ≤ (0.1501 : ℝ) := by
  dsimp only
  set q := 2 * pChild p K
  set a_q := realQuantize q a
  set b_q := realQuantize q b
  have hP_ge : K + 12 ≤ pChild p K := by
    unfold pChild pWork
    omega
  have hq_ge : K + 24 ≤ q := by
    dsimp [q]
    omega
  have h_err_a : |a_q - a| ≤ realQuantizeMaxErr q := abs_realQuantize_sub_le q a
  have h_err_b : |b_q - b| ≤ realQuantizeMaxErr q := abs_realQuantize_sub_le q b
  have h_qerr_small : realQuantizeMaxErr q ≤ (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by
    rw [realQuantizeMaxErr_eq]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h_a_q_ge : (0.4999 : ℝ) ≤ a_q := by
    have h1 := (abs_le.mp h_err_a).1
    linarith
  have ha0 : 0 ≤ a := by linarith
  have hb1 : b ≤ 1 := hba.trans ha_le
  have ha_q_Icc := realQuantize_mem_Icc_zero_one q ha0 ha_le
  have hb_q_Icc := realQuantize_mem_Icc_zero_one q hb_nonneg hb1
  have hba_q : b_q ≤ a_q := realQuantize_mono q hba
  refine ⟨h_a_q_ge, ha_q_Icc.2, hb_q_Icc.1, hba_q, ?_⟩
  have ha_pos : 0 < a := by linarith
  have ha_q_pos : 0 < a_q := by linarith
  have hdiv_q_abs : |b_q / a_q| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hb_q_Icc.1 ha_q_pos.le)]
    exact (div_le_one ha_q_pos).mpr hba_q
  have hdiv_abs : |b / a| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hb_nonneg ha_pos.le)]
    exact (div_le_one ha_pos).mpr hba
  have hdiv_diff : |b_q / a_q - b / a| ≤ 5 * realQuantizeMaxErr q := by
    have h1 := abs_div_sub_div_le a b a_q b_q (0.4999 : ℝ)
      (by norm_num) (by linarith) h_a_q_ge hb_nonneg hba
    have h2 : (|b_q - b| + |a_q - a|) / (0.4999 : ℝ) ≤ (2 * realQuantizeMaxErr q) / (0.4999 : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have hq_nonneg : 0 ≤ realQuantizeMaxErr q := by
      rw [realQuantizeMaxErr_eq]
      positivity
    have h3 : (2 * realQuantizeMaxErr q) / (0.4999 : ℝ) ≤ 5 * realQuantizeMaxErr q := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.4999)]
      linarith
    linarith
  have hpow_diff := abs_pow_sub_pow_le (b_q / a_q) (b / a) hdiv_q_abs hdiv_abs t1
  have ht1_real : (t1 : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast ht1_le
  have ht1_err : (t1 : ℝ) * (5 * realQuantizeMaxErr q) ≤ (0.0001 : ℝ) := by
    rw [realQuantizeMaxErr_eq]
    have hzpow_q :
        (2 : ℝ) ^ (-(q : ℤ)) ≤ (2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hcancel : (2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) = 1 := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
    calc (t1 : ℝ) * (5 * ((0.125 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))))
        ≤ (2 : ℝ) ^ (K : ℤ) * (5 * ((0.125 : ℝ) * ((2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(K : ℤ))))) :=
          mul_le_mul ht1_real
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzpow_q (by norm_num)) (by norm_num))
            (by positivity) (by positivity)
      _ = (5 * (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ)) * ((2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ))) := by ring
      _ = 5 * (0.125 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by rw [hcancel, mul_one]
      _ ≤ (0.0001 : ℝ) := by norm_num
  have hpow_sub : (b_q / a_q) ^ t1 - (b / a) ^ t1 ≤ (t1 : ℝ) * |b_q / a_q - b / a| :=
    (le_abs_self _).trans hpow_diff
  have hmul_le : (t1 : ℝ) * |b_q / a_q - b / a| ≤ (t1 : ℝ) * (5 * realQuantizeMaxErr q) :=
    mul_le_mul_of_nonneg_left hdiv_diff (Nat.cast_nonneg t1)
  linarith

/-- For any `p, K, t1 : ℕ` with `t1 ≤ 2 ^ K`, since `2 * pChild p K = 2 * p + 4 * K + 24`,
`(t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) ≤ 0.0001 * 2^{-p}` and `≤ 0.0001`. -/
theorem t1_mul_complexQuantizeMaxErr_two_mul_pChild_le
    (p K t1 : ℕ) (ht1 : t1 ≤ 2 ^ K) :
    (t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) ≤
      (0.0001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) ∧
    (t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) ≤ (0.0001 : ℝ) := by
  have h1 : complexQuantizeMaxErr (2 * pChild p K) ≤
      (0.354 : ℝ) * (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) :=
    (complexQuantizeMaxErr_lt (2 * pChild p K)).le
  have hP_eq : pChild p K = p + 2 * K + 12 := pChild_eq_additive p K
  have ht1_real : (t1 : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast ht1
  have hzpow :
      (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ)) ≤
        (2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
    push_cast
    omega
  have hcancel : (2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  have hmain :
      (t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K) ≤
        (0.0001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (t1 : ℝ) * complexQuantizeMaxErr (2 * pChild p K)
        ≤ (2 : ℝ) ^ (K : ℤ) * ((0.354 : ℝ) * (2 : ℝ) ^ (-((2 * pChild p K : ℕ) : ℤ))) :=
          mul_le_mul ht1_real h1 (by unfold complexQuantizeMaxErr; positivity) (by positivity)
      _ ≤ (2 : ℝ) ^ (K : ℤ) *
            ((0.354 : ℝ) * ((2 : ℝ) ^ (-24 : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzpow (by norm_num)) (by positivity)
      _ = ((0.354 : ℝ) * (2 : ℝ) ^ (-24 : ℤ)) *
            ((2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ))) * (2 : ℝ) ^ (-(p : ℤ)) := by ring
      _ = ((0.354 : ℝ) * (2 : ℝ) ^ (-24 : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) := by
          rw [hcancel, mul_one]
      _ ≤ (0.0001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hpow_le1 : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  refine ⟨hmain, by linarith⟩

/-- Uniform norm bound on `dft1DGrid`: if `∀ k < t1 * r, ‖x k‖ ≤ M` (`t1, r > 0`, `u2 < r`),
then `‖dft1DGrid t1 r x u2 v‖ ≤ M` for all `v : ℕ`. -/
theorem norm_dft1DGrid_le (t1 r : ℕ) (ht1 : 0 < t1) (hr : 0 < r)
    (x : ℕ → ℂ) (M : ℝ) (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u2 : ℕ) (hu2 : u2 < r) (v : ℕ) :
    ‖dft1DGrid t1 r x u2 v‖ ≤ M := by
  have hgrid : dft1DGrid t1 r x u2 v = dft1D (t1 * r) x (u2 + r * v) := by
    have hmod : (u2 + r * v) % r = u2 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu2]
    have hdiv : (u2 + r * v) / r = v := by
      rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hu2, zero_add]
    rw [← dft1DGrid_eq_dft1D t1 r x (u2 + r * v), hmod, hdiv]
  rw [hgrid]
  exact dft1D_norm_le (t1 * r) (Nat.mul_pos ht1 hr) x M
    (fun j hj => hx j (Finset.mem_range.mp hj)) (u2 + r * v)


end IntMul
