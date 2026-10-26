import IntMul.MaterializedAndComputable.ComputableTableBuilder

/-!
# W8 contracts: TM-friendly reformulations of the executable `IntMul` pipeline

All statements refer to `IntMul` (our independent executable specification of `[MS]`'s 2D multiplier)
(`IntMul.MaterializedAndComputable` and `IntMul.Theorem4KroneckerSpread`).

## Conventions
* A **contract** is a `def W8_<name> : Prop`. Its docstring gives the intended proof route and the
  snapshot lemmas to reuse.
* Where the statement is easy, a sanity-check proof `theorem W8_<name>_holds : W8_<name>` follows.
  An implication between contracts is recorded as `theorem W8_<a>_of_<b>`.
* There is no `sorry`, `native_decide`, `implemented_by`, `extern` or `unsafe` in this file.
* Helper reformulations and plain lemmas live under `IntMulTM.Contracts.W8.*`.
* File:line abbreviations:
  - CP = `ComputablePrimitives.lean`;
  - CES = `ComputableExactSolvers.lean`;
  - PCP = `ProgramCostPrimitives.lean`;
  - PHP = `PaperHeadlinePipeline.lean`;
  - TB = `ComputableTableBuilder.lean`;
  - FTP = `FaithfulTablesPerturbation.lean`;
  - CSWS = `CallSiteWidthSoundness.lean`;
  - PSR = `PaperStopAndRadix2Leaf.lean`;
  - T4 = `Theorem4KroneckerSpread.lean`.

## Parametric refinement route
1. The machine's own table hierarchy is decoded to `cSpec`. W7 proves `TablesFaithful cSpec spec`.
2. W8 proves every reformulation below equal to the snapshot function **for arbitrary inputs and
   tables**. The equality is `.1`-equality where the snapshot carries a cost counter.
3. W9 proves the machine bit-exact to the reformulations.
4. W11 closes with `computablePaperFastDFTMultiply_faithful_eq_mul` (FTP:2304); see section (e).

The division contracts (W6b, pure part) are in `Contracts/W6.lean`.
-/

namespace IntMulTM.Contracts

open IntMul
open scoped BigOperators

/-! ## Plain helper lemmas (reused by the contracts below and by `Contracts/W6.lean`) -/

/-- `divRoundRatInt` depends only on the rational `num / den`: scaling both by `c > 0` is a no-op. -/
theorem W8.divRoundRatInt_scale (u v c : ℤ) (hc : 0 < c) :
    divRoundRatInt (u * c) (v * c) = divRoundRatInt u v := by
  unfold divRoundRatInt
  by_cases hv : 0 < v
  · have hvc : 0 < v * c := mul_pos hv hc
    rw [if_pos hvc, if_pos hv]
    have h1 : 2 * (u * c) + v * c = (2 * u + v) * c := by ring
    have h2 : 2 * (v * c) = (2 * v) * c := by ring
    rw [h1, h2, Int.mul_ediv_mul_of_pos_left _ _ hc]
  · have hv' : v ≤ 0 := not_lt.mp hv
    have hvc : ¬ 0 < v * c := not_lt.mpr (by nlinarith)
    rw [if_neg hvc, if_neg hv]

/-- An exact quotient is returned unchanged: `divRoundRatInt (m * D) D = m` for `D > 0`. -/
theorem W8.divRoundRatInt_mul_cancel (m D : ℤ) (hD : 0 < D) : divRoundRatInt (m * D) D = m := by
  unfold divRoundRatInt
  rw [if_pos hD]
  have h1 : 2 * (m * D) + D = (2 * m + 1) * D := by ring
  rw [h1, Int.mul_ediv_mul_of_pos_left _ _ hD]
  omega

/-- `divRoundRatInt` by `2^k` is the snapshot's `divRoundPow2` (round half up). -/
theorem W8.divRoundRatInt_pow2 (num : ℤ) (k : ℕ) :
    divRoundRatInt num ((2 ^ k : ℕ) : ℤ) = divRoundPow2 num k := by
  unfold divRoundRatInt divRoundPow2
  have hpos : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  rw [if_pos hpos]
  split_ifs with hk
  · subst hk
    simp only [pow_zero, Nat.cast_one, mul_one]
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : ((2 ^ (j + 1) : ℕ) : ℤ) = 2 * ((2 ^ j : ℕ) : ℤ) := by push_cast; ring
    rw [h1]
    have h2 : 2 * num + 2 * ((2 ^ j : ℕ) : ℤ) = 2 * (num + ((2 ^ j : ℕ) : ℤ)) := by ring
    rw [h2, Int.mul_ediv_mul_of_pos _ _ (by norm_num : (0 : ℤ) < 2)]

/-- `gRescale` (CP:703-706) is a left shift when `p_in ≤ p_out` and a round-half-up right shift
otherwise. -/
theorem W8.gRescale_shift (p_in p_out : ℕ) (z : ℤ × ℤ) :
    gRescale p_in p_out z =
      if p_in ≤ p_out then
        (z.1 * ((2 ^ (p_out - p_in) : ℕ) : ℤ), z.2 * ((2 ^ (p_out - p_in) : ℕ) : ℤ))
      else (divRoundPow2 z.1 (p_in - p_out), divRoundPow2 z.2 (p_in - p_out)) := by
  unfold gRescale gQuantizeRat
  dsimp only
  split_ifs with h
  · obtain ⟨d, rfl⟩ : ∃ d, p_out = p_in + d := ⟨p_out - p_in, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have hS : ((2 ^ (p_in + d + 2) : ℕ) : ℤ) = ((2 ^ d : ℕ) : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ) := by
      push_cast; ring
    have hpos : (0 : ℤ) < ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
    rw [hS, ← mul_assoc, ← mul_assoc, W8.divRoundRatInt_mul_cancel _ _ hpos,
      W8.divRoundRatInt_mul_cancel _ _ hpos]
  · obtain ⟨d, rfl⟩ : ∃ d, p_in = p_out + d := ⟨p_in - p_out, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have hS : ((2 ^ (p_out + d + 2) : ℕ) : ℤ) = ((2 ^ d : ℕ) : ℤ) * ((2 ^ (p_out + 2) : ℕ) : ℤ) := by
      push_cast; ring
    have hpos : (0 : ℤ) < ((2 ^ (p_out + 2) : ℕ) : ℤ) := by positivity
    rw [hS, W8.divRoundRatInt_scale _ _ _ hpos, W8.divRoundRatInt_scale _ _ _ hpos,
      W8.divRoundRatInt_pow2, W8.divRoundRatInt_pow2]

/-- `gRescale q q` is the identity (used by the Nyquist zero branch and output rescales). -/
theorem W8.gRescale_self (q : ℕ) (z : ℤ × ℤ) : gRescale q q z = z := by
  rw [W8.gRescale_shift, if_pos le_rfl]
  simp

/-! ## (a) Static Kronecker stride -/

/-- **W8_strideMonotone.** Any stride `s ≥ computableKroneckerBitStride f g` yields the exact signed
polynomial product. Hence it yields the same block product as the snapshot's data-dependent stride,
since that stride is itself `≥` it (and `polyMulKroneckerSigned_kroneckerBitStride_eq`, T4:533).

*Proof route (done below):*
1. `polyMulKroneckerSignedComputable_eq` (CP:227).
2. `theorem4_signed_kronecker_polyMul_correct` (T4:177) at `H = 2^(s-1)`.
3. The headroom: `polyMulInt_mem_bounds_kroneckerHeadroom` (T4:424) and
   `kroneckerHeadroom_le_two_pow_kroneckerBitStride` (T4:459), plus monotonicity of `2^(·-1)`.

This mirrors `polyMulKroneckerSigned_kroneckerHeadroom_eq` (T4:520). -/
def W8_strideMonotone : Prop :=
  ∀ (s : ℕ) (f g : List ℤ), computableKroneckerBitStride f g ≤ s →
    polyMulKroneckerSignedComputable s f g = polyMulInt f g

theorem W8_strideMonotone_holds : W8_strideMonotone := by
  intro s f g hs
  rw [computableKroneckerBitStride_eq] at hs
  rw [polyMulKroneckerSignedComputable_eq]
  unfold polyMulKroneckerSigned
  dsimp only
  rw [← length_polyMulInt_eq f g]
  have hH : (0 : ℤ) < (2 : ℤ) ^ (s - 1) := by positivity
  have hle : kroneckerHeadroom f g ≤ (2 : ℤ) ^ (s - 1) :=
    (kroneckerHeadroom_le_two_pow_kroneckerBitStride f g).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  refine theorem4_signed_kronecker_polyMul_correct _ hH f g fun c hc => ?_
  rcases polyMulInt_mem_bounds_kroneckerHeadroom f g c hc with ⟨hlo, hhi⟩
  exact ⟨by linarith, hhi.trans_le hle⟩

/-- Block pairs of `computableSpreadRowContiguousWithCost` (CP:922-934), with the stride of the two
block products replaced by an arbitrary stride rule `σ`. The cost component is copied verbatim; it
plays no role in the value. -/
def W8.spreadBlockPairs (σ : List ℤ → List ℤ → ℕ) (p_in q m1 r : ℕ) (gTapFold : List ℤ)
    (xRow : Array (ℤ × ℤ)) : Array ((Array ℤ × Array ℤ) × ℕ) :=
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  Array.ofFn (fun b : Fin numBlocks =>
    let fBlockRe := computableSpreadRowBlockReContiguous p_in q m1 r xRow b.val
    let fBlockIm := computableSpreadRowBlockImContiguous p_in q m1 r xRow b.val
    let sRe := computableKroneckerBitStride fBlockRe gTapFold
    let sIm := computableKroneckerBitStride fBlockIm gTapFold
    let prodRe := polyMulKroneckerSignedComputable (σ fBlockRe gTapFold) fBlockRe gTapFold
    let prodIm := polyMulKroneckerSignedComputable (σ fBlockIm gTapFold) fBlockIm gTapFold
    let blockCost :=
      computableMulBitCost (fBlockRe.length * sRe) +
      computableMulBitCost (fBlockIm.length * sIm) +
      2 * W_eff * addBitCost sRe +
      2 * W_eff * addBitCost sIm
    ((prodRe.toArray, prodIm.toArray), blockCost))

/-- The bucket indices, single-pass overlap-add and readout of `computableSpreadRowContiguousWithCost`
(CP:935-945), copied verbatim, as a function of the block pairs. -/
def W8.spreadRowFromPairs (m1 r : ℕ) (blockPairs : Array ((Array ℤ × Array ℤ) × ℕ)) :
    Array (ℤ × ℤ) :=
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let idxFn := fun b i => ((((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat
  let bucketsRe := overlapAddBucketsSinglePass r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodReArr := if hb : b < blockPairs.size then blockPairs[b].1.1 else #[]
      read1D prodReArr i)
  let bucketsIm := overlapAddBucketsSinglePass r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodImArr := if hb : b < blockPairs.size then blockPairs[b].1.2 else #[]
      read1D prodImArr i)
  Array.ofFn (fun k2 : Fin r => (read1D bucketsRe k2.val, read1D bucketsIm k2.val))

/-- The spread row of `computableSpreadRowContiguousWithCost` (CP:918-946), with the data-dependent
stride `computableKroneckerBitStride` of the block products replaced by an arbitrary stride rule
`σ`. A TM uses the static stride `σ := fun _ _ => S`. Everything else (blocks, bucket indices,
single-pass overlap-add, readout) is copied verbatim. -/
def W8.spreadRowWithStride (σ : List ℤ → List ℤ → ℕ) (p_in q m1 r : ℕ) (gTapFold : List ℤ)
    (xRow : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  W8.spreadRowFromPairs m1 r (W8.spreadBlockPairs σ p_in q m1 r gTapFold xRow)

/-- **W8_staticStride_rowEq.** If the stride rule dominates the data-dependent stride on every block
of the row, the row equals the snapshot's spread row exactly as the pipeline calls it (PHP:151,
`.1` of the cost-carrying version).

*Proof (done below):*
1. `computableSpreadRowContiguousWithProgramCost_fst` (PCP:1719) gives
   `(computableSpreadRowContiguousWithCost …).1`.
2. The block-pair arrays agree entrywise by `W8_strideMonotone`, applied to `σ` and to the
   snapshot's own stride (`le_rfl`).
3. The rest is definitionally the snapshot's code (`rfl`). -/
def W8_staticStride_rowEq : Prop :=
  ∀ (σ : List ℤ → List ℤ → ℕ) (p_in q p' m1 r : ℕ) (gTapFold : List ℤ) (xRow : Array (ℤ × ℤ)),
    (∀ b < kroneckerSpreadNumBlocks m1 r,
      computableKroneckerBitStride (computableSpreadRowBlockReContiguous p_in q m1 r xRow b) gTapFold ≤
          σ (computableSpreadRowBlockReContiguous p_in q m1 r xRow b) gTapFold ∧
      computableKroneckerBitStride (computableSpreadRowBlockImContiguous p_in q m1 r xRow b) gTapFold ≤
          σ (computableSpreadRowBlockImContiguous p_in q m1 r xRow b) gTapFold) →
    W8.spreadRowWithStride σ p_in q m1 r gTapFold xRow =
      (computableSpreadRowContiguousWithProgramCost p_in q p' m1 r gTapFold xRow).1

theorem W8_staticStride_rowEq_holds : W8_staticStride_rowEq := by
  intro σ p_in q p' m1 r gTapFold xRow hσ
  rw [computableSpreadRowContiguousWithProgramCost_fst]
  have hpairs : W8.spreadBlockPairs σ p_in q m1 r gTapFold xRow =
      W8.spreadBlockPairs computableKroneckerBitStride p_in q m1 r gTapFold xRow := by
    unfold W8.spreadBlockPairs
    dsimp only
    congr 1
    funext b
    obtain ⟨hRe, hIm⟩ := hσ b.val b.isLt
    try dsimp only
    rw [W8_strideMonotone_holds _ _ _ hRe, W8_strideMonotone_holds _ _ _ hIm,
      W8_strideMonotone_holds _ _ _ le_rfl, W8_strideMonotone_holds _ _ _ le_rfl]
  unfold W8.spreadRowWithStride
  rw [hpairs]
  rfl

/-- **W8_staticStride_sixP.** The snapshot already proves the static schedule bound `6 * pChild p K`
for every block of a spread row. The hypotheses are:
* folded taps in the exact `TablesFaithful.hTaps` shape, with raw taps `|G s| ≤ 2^pSub + 1`;
* an input row bounded by `2^(pChild p K)`.

*Proof (done below):* `computableKroneckerBitStride_eq` (CP:216),
`computableSpreadRowBlock{Re,Im}Contiguous_eq` (CP:774, 787), and
`kroneckerBitStride_kroneckerSpreadRowBlock_of_folded_le` (FTP:890).

That last lemma rests on `kroneckerBitStride_le_six_mul_of_bounds` (T4:1024). The input-magnitude
premise must be supplied by W9/G-OPSIZE at each node. -/
def W8_staticStride_sixP : Prop :=
  ∀ (p K t1 r : ℕ), 8 ≤ p → 2 ≤ K → 0 < r →
  ∀ (gTapFold : List ℤ) (G : ℕ → ℤ),
    gTapFold =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u), G s) →
    (∀ s < 2 * (2 * pChild p K) + 1, (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1) →
  ∀ (p_in : ℕ) (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 : ℕ), j1 < t1 →
    (∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K)) →
    (∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) →
  ∀ b : ℕ,
    computableKroneckerBitStride
        (computableSpreadRowBlockReContiguous p_in (2 * pChild p K) (2 * pChild p K) r xRow b)
        gTapFold ≤ 6 * pChild p K ∧
    computableKroneckerBitStride
        (computableSpreadRowBlockImContiguous p_in (2 * pChild p K) (2 * pChild p K) r xRow b)
        gTapFold ≤ 6 * pChild p K

theorem W8_staticStride_sixP_holds : W8_staticStride_sixP := by
  intro p K t1 r hp hK hr gTapFold G hFold hG p_in xRow x j1 hj1 hx hxRow b
  simp only [computableKroneckerBitStride_eq]
  rw [computableSpreadRowBlockReContiguous_eq p_in _ _ t1 r xRow x j1 hxRow b,
    computableSpreadRowBlockImContiguous_eq p_in _ _ t1 r xRow x j1 hxRow b]
  exact kroneckerBitStride_kroneckerSpreadRowBlock_of_folded_le p K t1 r hp hK hr gTapFold G
    hFold hG x hx j1 b hj1

/-- **W8_staticStride_sixP_row.** The row a TM computes with the static stride `6 * pChild p K`
equals the snapshot's row at the pipeline's arguments. Those arguments are `q = m1 = pSub = 2p′` and
`p′ = pChild p K` (PHP:151 with `TablesFaithful`).

*Proof (done below):* `W8_staticStride_rowEq` plus `W8_staticStride_sixP`. -/
def W8_staticStride_sixP_row : Prop :=
  ∀ (p K t1 r : ℕ), 8 ≤ p → 2 ≤ K → 0 < r →
  ∀ (gTapFold : List ℤ) (G : ℕ → ℤ),
    gTapFold =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u), G s) →
    (∀ s < 2 * (2 * pChild p K) + 1, (G s).natAbs ≤ 2 ^ (2 * pChild p K) + 1) →
  ∀ (p_in : ℕ) (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 : ℕ), j1 < t1 →
    (∀ k < t1 * r, ‖x k‖ ≤ (2 : ℝ) ^ (pChild p K)) →
    (∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) →
    W8.spreadRowWithStride (fun _ _ => 6 * pChild p K) p_in (2 * pChild p K) (2 * pChild p K) r
        gTapFold xRow =
      (computableSpreadRowContiguousWithProgramCost p_in (2 * pChild p K) (pChild p K)
        (2 * pChild p K) r gTapFold xRow).1

theorem W8_staticStride_sixP_row_of_rowEq (hrow : W8_staticStride_rowEq) :
    W8_staticStride_sixP_row := by
  intro p K t1 r hp hK hr gTapFold G hFold hG p_in xRow x j1 hj1 hx hxRow
  exact hrow (fun _ _ => 6 * pChild p K) p_in (2 * pChild p K) (pChild p K) (2 * pChild p K) r
    gTapFold xRow (fun b _ =>
      W8_staticStride_sixP_holds p K t1 r hp hK hr gTapFold G hFold hG p_in xRow x j1 hj1 hx hxRow b)

theorem W8_staticStride_sixP_row_holds : W8_staticStride_sixP_row :=
  W8_staticStride_sixP_row_of_rowEq W8_staticStride_rowEq_holds

/-! ## (b) Shift-and-round for power-of-two denominators -/

/-- **W8_divRoundRatInt_pow2.** `divRoundRatInt num (2^k) = divRoundPow2 num k`. For `k ≥ 1` this
is `(num + 2^(k-1)) / 2^k`, i.e. round half toward `+∞`. Proved below via `Int.mul_ediv_mul_of_pos`. -/
def W8_divRoundRatInt_pow2 : Prop :=
  ∀ (num : ℤ) (k : ℕ), divRoundRatInt num ((2 ^ k : ℕ) : ℤ) = divRoundPow2 num k

theorem W8_divRoundRatInt_pow2_holds : W8_divRoundRatInt_pow2 := W8.divRoundRatInt_pow2

/-- **W8_divRoundPow2_shift.** `divRoundPow2 x k = (x + 2^(k-1)) >>> k` for `k ≥ 1`: an add plus a
bit shift on the machine. Proved below by `Int.shiftRight_eq_div_pow`. -/
def W8_divRoundPow2_shift : Prop :=
  ∀ (x : ℤ) (k : ℕ),
    divRoundPow2 x k = if k = 0 then x else (x + ((2 ^ (k - 1) : ℕ) : ℤ)) >>> k

theorem W8_divRoundPow2_shift_holds : W8_divRoundPow2_shift := by
  intro x k
  unfold divRoundPow2
  split_ifs
  · rfl
  · rw [Int.shiftRight_eq_div_pow]

/-- **W8_divRoundRatInt_scale.** Rational invariance (generic). Proved above as
`W8.divRoundRatInt_scale`. -/
def W8_divRoundRatInt_scale : Prop :=
  ∀ (u v c : ℤ), 0 < c → divRoundRatInt (u * c) (v * c) = divRoundRatInt u v

theorem W8_divRoundRatInt_scale_holds : W8_divRoundRatInt_scale := W8.divRoundRatInt_scale

/-- **W8_gRescale_shift.** `gRescale` (CP:703-706; the Q/Y/out rescales at PHP:164, 189, 211 and
the leaf rescales at PCP:2172, 2197) is a shift. Proved above as `W8.gRescale_shift`. -/
def W8_gRescale_shift : Prop :=
  ∀ (p_in p_out : ℕ) (z : ℤ × ℤ),
    gRescale p_in p_out z =
      if p_in ≤ p_out then
        (z.1 * ((2 ^ (p_out - p_in) : ℕ) : ℤ), z.2 * ((2 ^ (p_out - p_in) : ℕ) : ℤ))
      else (divRoundPow2 z.1 (p_in - p_out), divRoundPow2 z.2 (p_in - p_out))

theorem W8_gRescale_shift_holds : W8_gRescale_shift := W8.gRescale_shift

/-- **W8_gQuantizeCoordToScale_shift.** The spread input quantization (CP:727-728, used at CP:760,
771) is a shift. -/
def W8_gQuantizeCoordToScale_shift : Prop :=
  ∀ (p_in q : ℕ) (v : ℤ),
    gQuantizeCoordToScale p_in q v =
      if p_in + 2 ≤ q then v * ((2 ^ (q - (p_in + 2)) : ℕ) : ℤ)
      else divRoundPow2 v (p_in + 2 - q)

theorem W8_gQuantizeCoordToScale_shift_holds : W8_gQuantizeCoordToScale_shift := by
  intro p_in q v
  unfold gQuantizeCoordToScale
  split_ifs with h
  · obtain ⟨d, rfl⟩ : ∃ d, q = p_in + 2 + d := ⟨q - (p_in + 2), by omega⟩
    rw [Nat.add_sub_cancel_left]
    have hS : ((2 ^ (p_in + 2 + d) : ℕ) : ℤ) = ((2 ^ d : ℕ) : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ) := by
      push_cast; ring
    have hpos : (0 : ℤ) < ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
    rw [hS, ← mul_assoc, W8.divRoundRatInt_mul_cancel _ _ hpos]
  · obtain ⟨d, hd⟩ : ∃ d, p_in + 2 = q + d := ⟨p_in + 2 - q, by omega⟩
    have hd' : p_in + 2 - q = d := by omega
    rw [hd', hd]
    have hS : ((2 ^ (q + d) : ℕ) : ℤ) = ((2 ^ d : ℕ) : ℤ) * ((2 ^ q : ℕ) : ℤ) := by
      push_cast; ring
    have hpos : (0 : ℤ) < ((2 ^ q : ℕ) : ℤ) := by positivity
    rw [hS, W8.divRoundRatInt_scale _ _ _ hpos, W8.divRoundRatInt_pow2]

/-- **W8_gPreTwistU_shift.** The pre-twist denominator `2^q * 2^q` (CES:24-26; PHP:157) is
`2^(2q)`, so the rounding is a shift. -/
def W8_gPreTwistU_shift : Prop :=
  ∀ (q : ℕ) (tw uRaw : ℤ × ℤ),
    gPreTwistU q tw uRaw =
      (divRoundPow2 (tw.1 * uRaw.1 - tw.2 * uRaw.2) (2 * q),
       divRoundPow2 (tw.1 * uRaw.2 + tw.2 * uRaw.1) (2 * q))

theorem W8_gPreTwistU_shift_holds : W8_gPreTwistU_shift := by
  intro q tw uRaw
  unfold gPreTwistU gQuantizeRat
  dsimp only
  have h : ((2 ^ q * 2 ^ q : ℕ) : ℤ) = ((2 ^ (2 * q) : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, W8.divRoundRatInt_pow2, W8.divRoundRatInt_pow2]

/-- **W8_extractRootSlot_shift.** At the headline root precision `p0 = rootPrecision b K0 = 2b + 2K0 + 6`,
the root digit extraction (PHP:1066-1071) is `(-z.2 + 2^8) >>> 9`, i.e. `divRoundPow2 (-z.2) 9`. -/
def W8_extractRootSlot_shift : Prop :=
  ∀ (b K0 : ℕ) (z : ℤ × ℤ),
    (costedExtractRootSlot (rootPrecision b K0) b K0 z).1 = (divRoundPow2 (-z.2) 9).toNat

theorem W8_extractRootSlot_shift_holds : W8_extractRootSlot_shift := by
  intro b K0 z
  simp only [costedDivRoundRatInt, rootPrecision]
  have hden : (2 : ℤ) * ((2 ^ (2 * b + 2 * K0 + 6 + 2) : ℕ) : ℤ) =
      ((2 ^ 9 : ℕ) : ℤ) * ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ) := by
    push_cast; ring
  have hpos : (0 : ℤ) < ((2 ^ (2 * b + 2 * K0) : ℕ) : ℤ) := by positivity
  rw [hden, W8.divRoundRatInt_scale _ _ _ hpos, W8.divRoundRatInt_pow2]

/-- **W8_nyquistDivT1_shift.** The Nyquist solver's division by `t1` (CES:461 and PCP:863,
`gQuantizeRat … (t1 : ℤ)`) is a shift whenever `t1 = 2^m`. On the headline schedule this holds by
`W8_paperStop_dimsPow2`, or in general from `t1 * r = 2^K`
(`two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow`, QuantizedSubstepBridges:767). -/
def W8_nyquistDivT1_shift : Prop :=
  ∀ (t1 m : ℕ) (a b : ℤ), t1 = 2 ^ m →
    gQuantizeRat a b (t1 : ℤ) = (divRoundPow2 a m, divRoundPow2 b m)

theorem W8_nyquistDivT1_shift_holds : W8_nyquistDivT1_shift := by
  intro t1 m a b ht1
  subst ht1
  unfold gQuantizeRat
  rw [W8.divRoundRatInt_pow2, W8.divRoundRatInt_pow2]

/-- **W8_nyquistAltSumScale_shift.** The Nyquist alternating-sum scale (PCP:848-851, denominator
`r * 2^(p_in+2)`, called at PCP:943) is a `gRescale` from precision `m + p_in` when `r = 2^m`. By
`W8_gRescale_shift` it is therefore a shift. -/
def W8_nyquistAltSumScale_shift : Prop :=
  ∀ (p_in q w r m : ℕ) (altSum : ℤ × ℤ), r = 2 ^ m →
    (costedGNyqAltSumScale p_in q w r altSum).1 = gRescale (m + p_in) q (-altSum.2, altSum.1)

theorem W8_nyquistAltSumScale_shift_holds : W8_nyquistAltSumScale_shift := by
  intro p_in q w r m altSum hr
  subst hr
  simp only [costedGNyqAltSumScale, costedGQuantizeRat, gRescale]
  have h : ((2 ^ m : ℕ) : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ) = ((2 ^ (m + p_in + 2) : ℕ) : ℤ) := by
    push_cast; ring
  rw [h]

/-- Every step node of a schedule has power-of-two dimensions `t1 = 2^(K/2)` and `r = 2^(K - K/2)`. -/
def W8.StepDimsPow2 : QuantizedFastDFTSpec → Prop
  | .base _ _ => True
  | .step _ K t1 r _ _ child => t1 = 2 ^ (K / 2) ∧ r = 2 ^ (K - K / 2) ∧ W8.StepDimsPow2 child

/-- **W8_paperStop_dimsPow2.** On the headline schedule (`buildQuantizedSpecPaperStop`, PSR:43-50;
`quantizedBoxGaussianStepSpec`, QuantizedFastDFT:521-523), `t1` and `r` are exact powers of two at
every step node. So `/t1` and `/r` are shifts. Under `TablesFaithful` the computable spec carries the
same `t1, r` (FTP:44-90). Proved below by induction on the fuel. -/
def W8_paperStop_dimsPow2 : Prop :=
  ∀ (L p K : ℕ), W8.StepDimsPow2 (buildQuantizedSpecPaperStop L p K)

theorem W8_paperStop_dimsPow2_holds : W8_paperStop_dimsPow2 := by
  intro L
  induction L with
  | zero =>
    intro p K
    simp [buildQuantizedSpecPaperStop, W8.StepDimsPow2]
  | succ L ih =>
    intro p K
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs
    · simp [W8.StepDimsPow2]
    · simp only [quantizedBoxGaussianStepSpec, W8.StepDimsPow2]
      first
        | exact ⟨rfl, rfl, ih _ _⟩
        | exact ih _ _
        | exact ⟨trivial, trivial, ih _ _⟩

/-! ## (d) Single-pass fold of the raw tap row -/

/-- The single-pass tap fold a TM runs: one left-to-right pass over the `n` raw taps, adding
`G s` into bucket `s % W` of a `W`-bucket array. It reuses the snapshot's O(1)-per-step bucket
updater `accumBucketsRange` (CP:829-833). -/
def W8.foldTapsSinglePass (W n : ℕ) (G : ℕ → ℤ) : List ℤ :=
  (accumBucketsRange (fun s => s % W) G n (Array.replicate W 0)).toList

/-- **W8_foldSinglePass_hTapsShape.** The single-pass fold produces exactly the folded-tap shape
of `TablesFaithful.hTaps` (FTP:49-54) for any raw taps `G` and any `W`, including `W = 0`.

*Proof (done below):* `List.ext_getElem`, then `read1D_accumBucketsRange_of_lt` (CP:842) and
`sumRangeInt_ite_eq_sum_filter` (CP:189). So a machine whose tap rows are the single-pass fold of
raw taps meeting the `hTaps` accuracy and magnitude clauses satisfies `hTaps`. That is W7's
obligation. The snapshot's own `costedFoldRawTapRow` (TB:35-39) scans all inputs per output, which
is quadratic. -/
def W8_foldSinglePass_hTapsShape : Prop :=
  ∀ (W n : ℕ) (G : ℕ → ℤ),
    W8.foldTapsSinglePass W n G =
      (List.range W).map (fun u => ∑ s ∈ (Finset.range n).filter (fun s => s % W = u), G s)

theorem W8_foldSinglePass_hTapsShape_holds : W8_foldSinglePass_hTapsShape := by
  intro W n G
  apply List.ext_getElem
  · simp [W8.foldTapsSinglePass]
  · intro u _ h2
    have hu : u < W := by simpa using h2
    have hsz : u < (Array.replicate W (0 : ℤ)).size := by simpa using hu
    have hsz' : u < (accumBucketsRange (fun s => s % W) G n (Array.replicate W 0)).size := by
      simpa using hu
    have key := read1D_accumBucketsRange_of_lt (fun s => s % W) G n (Array.replicate W 0) u hsz
    beta_reduce at key
    have hzero : read1D (Array.replicate W (0 : ℤ)) u = 0 := by
      unfold read1D; simp [hu]
    rw [hzero, zero_add, sumRangeInt_ite_eq_sum_filter] at key
    simp only [W8.foldTapsSinglePass, Array.getElem_toList, List.getElem_map, List.getElem_range]
    rw [← key]
    unfold read1D
    rw [dif_pos hsz']

/-- **W8_foldSinglePass_hTaps.** The instance at the exact `hTaps` parameters
`W = effectiveFilterWidth (2 * pChild p K) r` and `n = 2 * (2 * pChild p K) + 1`. -/
def W8_foldSinglePass_hTaps : Prop :=
  ∀ (p K r : ℕ) (G : ℕ → ℤ),
    W8.foldTapsSinglePass (effectiveFilterWidth (2 * pChild p K) r) (2 * (2 * pChild p K) + 1) G =
      (List.range (effectiveFilterWidth (2 * pChild p K) r)).map (fun u =>
        ∑ s ∈ (Finset.range (2 * (2 * pChild p K) + 1)).filter
            (fun s => s % effectiveFilterWidth (2 * pChild p K) r = u), G s)

theorem W8_foldSinglePass_hTaps_holds : W8_foldSinglePass_hTaps :=
  fun _ _ _ G => W8_foldSinglePass_hTapsShape_holds _ _ G

/-- **W8_costedFoldRawTapRow_eq.** The snapshot's fold (TB:35-39, value part) equals the
single-pass fold of the raw-tap array read with `read1D`. -/
def W8_costedFoldRawTapRow_eq : Prop :=
  ∀ (p' pSub W : ℕ) (rawArr : Array ℤ),
    (costedFoldRawTapRow p' pSub W rawArr).1 =
      W8.foldTapsSinglePass W (2 * pSub + 1) (fun s => read1D rawArr s)

theorem W8_costedFoldRawTapRow_eq_holds : W8_costedFoldRawTapRow_eq := by
  intro p' pSub W rawArr
  rw [W8_foldSinglePass_hTapsShape_holds]

/-! ## (e) The parametric pipeline interface consumed by W11 -/

/-- Headline schedule parameter `b` as a function of the bit length `n` (CSWS:2264). -/
def W8.hB (n : ℕ) : ℕ := max 1 (Nat.log2 n)
/-- Headline schedule parameter `k` (CSWS:2265). -/
def W8.hK (n : ℕ) : ℕ := n / W8.hB n + 1
/-- Headline schedule parameter `K0` (CSWS:2266). -/
def W8.hK0 (n : ℕ) : ℕ := max 4 (Nat.log2 (2 * W8.hK n) + 2)
/-- Headline schedule fuel `L` (CSWS:2267). -/
def W8.hL (n : ℕ) : ℕ := Nat.log2 (W8.hK0 n - 1)
/-- Headline root precision `p0` (CSWS:2268). -/
def W8.hP0 (n : ℕ) : ℕ := rootPrecision (W8.hB n) (W8.hK0 n)
/-- Headline schedule `spec` (CSWS:2269). -/
def W8.hSpec (n : ℕ) : QuantizedFastDFTSpec :=
  buildQuantizedSpecPaperStop (W8.hL n) (W8.hP0 n) (W8.hK0 n)

/-- **W8_parametricPipeline (= FTP:2304).** For any valid schedule and **any** faithful table
hierarchy, the counter-erased pipeline value is the exact product. The premises are:
* `spec.Valid` and `TablesFaithful cSpec spec`;
* size `2^K0` and precision `rootPrecision b K0`;
* `k1 + k2 ≤ 2^K0` and input range `A < (2^b)^k1`, `B < (2^b)^k2`.

No shape, size or width condition on `cSpec` beyond `TablesFaithful` is needed for the **value**.
W7's canonical-shape and serialized-size outputs are cost/layout obligations, not correctness
premises. `PaperExecutableValid` follows from `TablesFaithful` (`TablesFaithful.paperExecutableValid`,
FTP:96). Proof: the snapshot theorem itself. -/
def W8_parametricPipeline : Prop :=
  ∀ (spec : QuantizedFastDFTSpec), spec.Valid →
  ∀ (cSpec : ComputablePaperFastDFTSpec), TablesFaithful cSpec spec →
  ∀ (b K0 k1 k2 : ℕ), spec.size = 2 ^ K0 → spec.p = rootPrecision b K0 → k1 + k2 ≤ 2 ^ K0 →
  ∀ (A B : ℕ), A < (2 ^ b) ^ k1 → B < (2 ^ b) ^ k2 →
    computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B = A * B

theorem W8_parametricPipeline_holds : W8_parametricPipeline :=
  fun spec hvalid cSpec hfaith b K0 k1 k2 hsize hp0 hk A B hA hB =>
    computablePaperFastDFTMultiply_faithful_eq_mul spec hvalid cSpec hfaith b K0 k1 k2 hsize hp0 hk
      A B hA hB

/-- **W8_parametricHeadline.** The headline instance of `W8_parametricPipeline` (CSWS:2369-2411
with the builder's tables replaced by an arbitrary faithful `cSpec`). With the headline schedule and
`A, B < 2^n`, any `cSpec` faithful to `W8.hSpec n` gives the exact product. All root premises are
discharged from the schedule. Proof below replays CSWS:2378-2411. -/
def W8_parametricHeadline : Prop :=
  ∀ (n A B : ℕ) (cSpec : ComputablePaperFastDFTSpec),
    A < 2 ^ n → B < 2 ^ n → TablesFaithful cSpec (W8.hSpec n) →
    computablePaperFastDFTMultiply cSpec (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) A B = A * B

theorem W8_parametricHeadline_holds : W8_parametricHeadline := by
  intro n A B cSpec hA hB hfaith
  have hb_pos : 1 ≤ W8.hB n := le_max_left 1 (Nat.log2 n)
  have hK0_ge4 : 4 ≤ W8.hK0 n := le_max_left 4 (Nat.log2 (2 * W8.hK n) + 2)
  have hp0 : 8 ≤ W8.hP0 n := by
    unfold W8.hP0 rootPrecision
    omega
  have hvalid : (W8.hSpec n).Valid :=
    buildQuantizedSpecPaperStop_valid (W8.hL n) (W8.hP0 n) (W8.hK0 n) hp0
  have hsize : (W8.hSpec n).size = 2 ^ W8.hK0 n :=
    buildQuantizedSpecPaperStop_size (W8.hL n) (W8.hP0 n) (W8.hK0 n)
  have hspec_p : (W8.hSpec n).p = rootPrecision (W8.hB n) (W8.hK0 n) :=
    buildQuantizedSpecPaperStop_p (W8.hL n) (W8.hP0 n) (W8.hK0 n)
  have hk : W8.hK n + W8.hK n ≤ 2 ^ W8.hK0 n := by
    have hlt := lt_two_pow_log2_succ (2 * W8.hK n)
    have hle_exp : Nat.log2 (2 * W8.hK n) + 1 ≤ W8.hK0 n := by
      have : Nat.log2 (2 * W8.hK n) + 2 ≤ W8.hK0 n :=
        le_max_right 4 (Nat.log2 (2 * W8.hK n) + 2)
      omega
    have hpow_le : 2 ^ (Nat.log2 (2 * W8.hK n) + 1) ≤ 2 ^ W8.hK0 n :=
      Nat.pow_le_pow_right zero_lt_two hle_exp
    omega
  have hbk : n ≤ W8.hB n * W8.hK n := by
    unfold W8.hK
    have hdiv := Nat.div_add_mod n (W8.hB n)
    have hmod : n % W8.hB n < W8.hB n := Nat.mod_lt n (by omega)
    have hmul : W8.hB n * (n / W8.hB n + 1) = W8.hB n * (n / W8.hB n) + W8.hB n := by ring
    omega
  have hpow_bk : 2 ^ n ≤ (2 ^ W8.hB n) ^ W8.hK n := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right zero_lt_two hbk
  exact computablePaperFastDFTMultiply_faithful_eq_mul (W8.hSpec n) hvalid cSpec hfaith
    (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) hsize hspec_p hk A B
    (hA.trans_le hpow_bk) (hB.trans_le hpow_bk)

/-- **W8_machineInterface: the minimal clean interface the machine side must meet.** For each input
`(n, A, B)` with `A, B < 2^n`, the machine must deliver both of the following:
* (W7) a table hierarchy that decodes to some `cSpec` with `TablesFaithful cSpec (W8.hSpec n)`;
* (W9) an output equal to `computablePaperFastDFTMultiply cSpec (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) A B`,
  proved through the W8 reformulations (stride, shifts, reciprocal division, fold) and the `_fst`
  bridges.

Then the output is `A * B`. The input-encoding bridge to `n` and `A, B < 2^n` is G-INPUT/W12. -/
def W8_machineInterface : Prop :=
  ∀ (n A B out : ℕ), A < 2 ^ n → B < 2 ^ n →
    (∃ cSpec : ComputablePaperFastDFTSpec, TablesFaithful cSpec (W8.hSpec n) ∧
      out = computablePaperFastDFTMultiply cSpec (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) A B) →
    out = A * B

theorem W8_machineInterface_holds : W8_machineInterface := by
  rintro n A B out hA hB ⟨cSpec, hfaith, rfl⟩
  exact W8_parametricHeadline_holds n A B cSpec hA hB hfaith

/-- **W8_costErasure.** The pipeline values used above are literally the `.1` of the cost-carrying
programs (PHP:1112-1114, 229-231), so W9 refines `…WithProgramCost` through its component `_fst`
lemmas:
* `computableSpreadRowContiguousWithProgramCost_fst` (PCP:1719);
* `computableSyntheticFFTRadix2WithProgramCost_fst` (PCP:422);
* `computableSolveBidiagonal{Fwd,Bwd}WithProgramCost_fst` (PCP:610, 708);
* `computableSolveNyquistWithProgramCost_fst` (PCP:872);
* `computableNyquistAltSumContiguousWithProgramCost_fst` (PCP:946);
* `runScan2DCostedWithSteps_fst` (PCP:379) and `runSequentialScanCostedSteps_fst` (PCP:350);
* `splitChunksTreeWithProgramCost_fst` and `reconstructChunksTreeWithProgramCost_fst`.

Both conjuncts are `rfl`. -/
def W8_costErasure : Prop :=
  (∀ (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ),
    computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B =
      (computablePaperFastDFTMultiplyWithProgramCost cSpec b K0 k1 k2 A B).1) ∧
  (∀ (p_in : ℕ) (cSpec : ComputablePaperFastDFTSpec) (xArr : Array (ℤ × ℤ)),
    computablePaperFastDFT p_in cSpec xArr = (computablePaperFastDFTWithProgramCost p_in cSpec xArr).1)

theorem W8_costErasure_holds : W8_costErasure :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end IntMulTM.Contracts
