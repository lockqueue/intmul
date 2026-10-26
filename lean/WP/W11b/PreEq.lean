import WP.W11b.Shapes

/-!
# WP.W11b.PreEq — dequantized values of the PRE phases (W9 forms)

The `hxRow_eq`, `hP_eq`, `hQ_eq`, `hqPost_eq` steps of the snapshot's
`allCallSitesWidthSound_of_faithful` (CSWS:1822-1940), restated on the W9 phase helpers
(`w9XRows`, `w9U`, `w9P`, `w9Q`/`w9Syn`, `preNodeV`). With `norm_qPost_of_faithful_le_two_pow_pChild`
(FTP:1096) they give the node invariant of the children.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- Dequantized node input. -/
noncomputable def xOf (p_in : ℕ) (x : Array (ℤ × ℤ)) : ℕ → ℂ :=
  fun k => toScaledComplex p_in (read1D x k)

/-- The snapshot's real-valued pre-twisted matrix `P` (CSWS:1897). -/
noncomputable def pOf (p_in pSub t1 r : ℕ) (ft : Array (List ℤ)) (preTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : ℕ → ℕ → ℂ :=
  fun j1 m => complexQuantize pSub (toScaledComplex pSub (read1D preTw m) *
    kroneckerSpreadOfFoldedTaps pSub pSub t1 r (ft.getD j1 []) (xOf p_in x) j1 m)

/-- The snapshot's real-valued `Q` (CSWS:1899). -/
noncomputable def qOf (p_in pSub t1 r : ℕ) (ft : Array (List ℤ)) (preTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : ℕ → ℕ → ℂ :=
  fun v m => complexQuantize pSub
    (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) (pOf p_in pSub t1 r ft preTw x) v m)

/-- The snapshot's real-valued children inputs `qPost` (CSWS:1901). -/
noncomputable def qPostOf (p_in pSub t1 r : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : ℕ → ℕ → ℂ :=
  fun v m => complexQuantize pSub (toScaledComplex pSub (read1D postTw m) *
    qOf p_in pSub t1 r ft preTw x v m)

theorem hxRow_w9 {t1 r : ℕ} (K : ℕ) (hsize : t1 * r = 2 ^ K) (hr : 0 < r) (p_in : ℕ)
    (x : Array (ℤ × ℤ)) : ∀ j1 < t1, ∀ i < r,
      xOf p_in x (j1 + t1 * i) = toScaledComplex p_in (read1D ((w9XRows t1 r x).getD j1 #[]) i) := by
  intro j1 hj1 i hi
  obtain ⟨ht1_pow, -⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  rw [read1D_array_getD_eq_read2D, read2D_w9XRows x (Nat.log2 t1) ht1_pow.symm hr hj1 hi]
  unfold xOf
  rw [show i * t1 + j1 = j1 + t1 * i by ring]

theorem read2D_w9U {p_in pSub m1 t1 r : ℕ} {ft : Array (List ℤ)} {xRows : Array (Array (ℤ × ℤ))}
    {j1 : ℕ} (hj1 : j1 < t1) (k2 : ℕ) :
    read2D (w9U p_in pSub m1 t1 r ft xRows) j1 k2 =
      read1D (computableSpreadRowContiguousWithCost p_in pSub m1 r (ft.getD j1 [])
        (xRows.getD j1 #[])).1 k2 := by
  unfold w9U
  rw [read2D_ofFn_of_lt t1 _ hj1 k2]
  rfl

theorem p_eq_w9 {t1 r : ℕ} (K : ℕ) (hsize : t1 * r = 2 ^ K) (hr : 0 < r)
    (p_in pSub : ℕ) (ft : Array (List ℤ)) (preTw : Array (ℤ × ℤ)) (x : Array (ℤ × ℤ)) :
    ∀ j1 < t1, ∀ k2 < r,
      toScaledComplex pSub (read2D (w9P pSub t1 r preTw
        (w9U p_in pSub pSub t1 r ft (w9XRows t1 r x))) j1 k2) =
        pOf p_in pSub t1 r ft preTw x j1 k2 := by
  intro j1 hj1 k2 hk2
  unfold w9P
  rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hk2, read2D_w9U hj1]
  exact toScaledComplex_gPreTwistU_eq pSub (read1D preTw k2) _ _
    (computableSpreadRowContiguousWithCost_eq_kroneckerSpreadOfFoldedTaps p_in pSub pSub t1 r
      (ft.getD j1 []) ((w9XRows t1 r x).getD j1 #[]) (xOf p_in x) j1 k2
      (hxRow_w9 K hsize hr p_in x j1 hj1) hk2).symm

theorem q_eq_w9 {t1 r c1 : ℕ} (K : ℕ) (hsize : t1 * r = 2 ^ K) (ht1 : 0 < t1) (hr : 0 < r)
    (hc1 : c1 * t1 = r) (p_in pSub : ℕ) (ft : Array (List ℤ)) (preTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : ∀ v1 < t1, ∀ k2 < r,
      toScaledComplex pSub (read2D (w9Q pSub t1 r (w9Syn t1 r (w9P pSub t1 r preTw
        (w9U p_in pSub pSub t1 r ft (w9XRows t1 r x))))) v1 k2) =
        qOf p_in pSub t1 r ft preTw x v1 k2 := by
  intro v1 hv1 k2 hk2
  obtain ⟨ht1_pow, -⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
  have hc1_pow : 2 ^ (Nat.log2 t1) * (r / t1) = r := by
    rw [ht1_pow, ← hc1, Nat.mul_div_left c1 ht1, mul_comm]
  unfold w9Q w9Syn
  rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2, toScaledComplex_gRescale_eq]
  unfold qOf
  apply congrArg (complexQuantize pSub)
  rw [natLog2Fuel_self, ← array_getD_getD_eq_read2D_pair _ v1 k2,
    toScaledComplex_computableSyntheticFFTRadix2_eq pSub t1 r (Nat.log2 t1) (r / t1) hc1_pow _ v1 k2
      (ht1_pow.symm ▸ hv1) hk2]
  refine syntheticFFTRadix2Quantized_congr_lt pSub r (Nat.log2 t1) (r / t1) _ _
    (fun j hj m hm => ?_) v1 k2 hk2
  rw [array_getD_getD_eq_read2D_pair]
  exact p_eq_w9 K hsize hr p_in pSub ft preTw x j (ht1_pow ▸ hj) m hm

theorem qPost_eq_w9 {t1 r c1 : ℕ} (K : ℕ) (hsize : t1 * r = 2 ^ K) (ht1 : 0 < t1) (hr : 0 < r)
    (hc1 : c1 * t1 = r) (p_in pSub : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
    (x : Array (ℤ × ℤ)) : ∀ v1 < t1, ∀ k2 < r,
      toScaledComplex pSub (read2D (preNodeV p_in pSub pSub t1 r ft preTw postTw x) v1 k2) =
        qPostOf p_in pSub t1 r ft preTw postTw x v1 k2 := by
  intro v1 hv1 k2 hk2
  rw [preNodeV_eq_phases]
  unfold w9QPost
  rw [read2D_runScan2DWithSteps_of_lt t1 r _ hv1 hk2, toScaledComplex_gMulScaled_eq_complexQuantize_mul,
    q_eq_w9 K hsize ht1 hr hc1 p_in pSub ft preTw x v1 hv1 k2 hk2]
  rfl

#assert_std_axioms hxRow_w9 read2D_w9U p_eq_w9 q_eq_w9 qPost_eq_w9

end WP.W11b
