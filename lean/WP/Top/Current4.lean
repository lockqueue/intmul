import WP.Top.Current3
import WP.W9comp.Kernels
import WP.W7k1.Isqrt
import WP.W7k1.Pi
import WP.W7k1.Ln
import WP.W7k2.ColRecip
import WP.W7k2.Arith
import WP.W7pure.EntryWidths
import WP.W7pure.TapeSize
import WP.W6a.DivRound
import WP.W3b.Sign
import WP.W3b.CmpInt
import WP.W3b.DecAmortised
import Contracts.W9.Ret

/-!
# WP.Top.Current4 — the headline from leaf machine contracts

`intMul_TM2_nlogn_current4` is `intMul_TM2_nlogn_current3` with `h7` and `h9` wired down to leaf
contracts. Every hypothesis is either a leaf machine contract that is not yet proved, or (for now)
a W9 assembly Prop.

The following are discharged by proved results:
* W3: `w3_copyNat`, `w3_cmpNat`, `w3_isZeroNat`, `w3_incNat`, `w3_decNat`, `w3_natToInt`,
  `w3_splitSign` (frozen contracts); W3b's signed ops and `W3_dec_amortised` (W3b);
* W4: `w4_moveRecord` (frozen contracts);
* W5: `W5_toom3Mul_holds` (W5); W6a: `W6a_holds` (W6a);
* W7: `W7_isqrt_holds`, `W7_piScaled_holds`, `W7_log2Scaled_holds` (W7k1); `W7_colRecip_holds`
  and `T3_le_quad` (W7k2); `W7_entryWidths_of_faithful_holds` and `W7_tapeSize_holds` (W7pure);
  `W7_buildTables_of_ref` and `W7.refFacts_snapshot` (`Contracts.W7`);
* W9: `w9_retMark` (`Contracts.W9`); `W9_preNode_of_phases_holds`, `W9_postNode_of_phases_holds`
  (W9comp).

**Shared `Mul`.** For W7, `W5_toom3Mul_iff_mulAt` gives one triple `c0 c1 w0`. Then
`Mul := T3 c0 c1 w0`, and `T3_le_quad` gives the growth premise `∃ K, ∀ w, Mul w ≤ K·(w+1)²`. W9 is
wired at every `Mul` with `W5_mulAt Mul`, which is what `intMul_TM2_nlogn_current3` consumes.

**Hypothesis shapes.** Each hypothesis carries every premise its owner may use. A theorem that
needs fewer premises fits by projection.
* W9 stage kernels: W9comp's binding shape (`W9StageThms4` = `W9StageThms` without
  `preTranspose`). The pre-transpose kernel `h9pT` also gets `W4_transpose .down .up`, which is not
  in `W4_all`; W9b's kernel needs it.
* W9 assembly: `W3_all → W4_all → W6a_all → ∀ Mul, …`.
* W7 kernels and builder: `∀ Mul, W5_mulAt Mul → growth → W7.Hyps → …`.
-/

namespace WP.Top

open TMFw TMFw.Contracts IntMulTM.Contracts.Top

/-- `W3_all` from the ten open unsigned W3 contracts. The rest is proved in the frozen contracts
or in W3b. -/
theorem W3_all_of_open (h3drop : W3_dropNat) (h3norm : W3_normNat) (h3add : W3_addNat)
    (h3sub : W3_subNat) (h3shlC : W3_shlConst) (h3shrC : W3_shrConst) (h3shlV : W3_shlVar)
    (h3shrV : W3_shrVar) (h3split : W3_splitAt) (h3concat : W3_concatAt) : W3_all :=
  ⟨w3_copyNat, h3drop, h3norm, w3_isZeroNat, w3_cmpNat, h3add, h3sub, h3shlC, h3shrC, h3shlV,
    h3shrV, h3split, h3concat, w3_incNat, w3_decNat, TMFw.W3b.W3_dec_amortised_holds, w3_natToInt,
    TMFw.W3b.W3_attachSign_holds, w3_splitSign, TMFw.W3b.W3_negInt_holds,
    TMFw.W3b.W3_signInt_holds, TMFw.W3b.W3_addInt_holds h3add h3sub,
    TMFw.W3b.W3_subInt_holds h3add h3sub, TMFw.W3b.W3_cmpInt_holds, TMFw.W3b.W3_smallOpInt_holds⟩

/-- `W7.Hyps` (the machine contracts W7 may assume) from `W3_all`, W5 and W6a. -/
theorem W7_hyps_of (h3 : W3_all) (h5 : W5_toom3Mul) (h6 : W6a_all) : W7.Hyps := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, _, a17, a18, a19,
    a20, a21, a22, a23, a24, a25⟩ := h3
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a17, a18, a19, a20,
    a21, a22, a23, a24, a25⟩, w4_moveRecord, h5, h6.1, h6.2⟩

/-- `W7_kernels` from the three open kernels: `isqrt`, `π`, `ln 2` (W7k1) and `colRecip` (W7k2)
are proved. -/
theorem W7_kernels_of (h3 : W3_all) (h6 : W6a_all) (hstd : W7_stdChar)
    (htap : W7_sincGaussianTap) (hc01 : W7_c0c1) : W7_kernels := by
  obtain ⟨hcopy, hdrop, _, hisz, hcmp, hadd, hsub, hshl, hshr, hshlV, hshrV, _, _, hinc, hdec, _⟩ :=
    h3
  exact ⟨WP.W7k1.W7_isqrt_holds,
    WP.W7k1.W7_piScaled_holds hcopy hinc hshl hshlV hadd hsub hshrV hshr hdrop hisz hdec,
    WP.W7k1.W7_log2Scaled_holds hcopy hinc hshl hshlV hadd hsub hshrV hshr hdrop hisz hdec h6.1,
    hstd, htap, hc01, WP.W7k2.W7_colRecip_holds hcopy hshl hcmp hshlV hdrop h6.1⟩

/-- **h7 from leaves.** `Mul := T3 c0 c1 w0` from W5; growth premise from `T3_le_quad`; the kernels
from `W7_kernels_of`; the builder's bit-exact tape is turned into the joint output contract by
`W7_buildTables_of_ref`, with W7pure's two pure facts. -/
theorem W7_buildTables_of_leaves (h3 : W3_all) (h6 : W6a_all) (h5 : W5_toom3Mul)
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule) :
    W7_buildTables W7.snapshotSchedule := by
  obtain ⟨c0, c1, w0, hM⟩ := W5_toom3Mul_iff_mulAt.mp h5
  have hg := WP.W7k2.T3_le_quad c0 c1 w0
  have hH := W7_hyps_of h3 h5 h6
  exact W7_buildTables_of_ref _
    (h7ref _ hM hg hH (W7_kernels_of h3 h6 (h7std _ hM hg hH) (h7tap _ hM hg hH) (h7c01 _ hM hg hH)))
    (W7.refFacts_snapshot WP.W7pure.W7_entryWidths_of_faithful_holds WP.W7pure.W7_tapeSize_holds)

/-- **h9 from leaves**, at every `Mul` with `W5_mulAt Mul`:
* the node kernels come from the phases (W9comp);
* the level programs come from `W9_levels_of_kernels`, with `w9_retMark` proved;
* then `W9_pipeline_of_levels` and `W9_multiply_of_parts`. -/
theorem W9_multiply_of_leaves (h3 : W3_all) (h4 : W4_all) (h6 : W6a_all)
    (H9 : WP.W9comp.W9StageThms)
    (hA1 : W3_all → W4_all → W6a_all → ∀ Mul, W9_levels_of_kernels Mul)
    (hA2 : W3_all → W4_all → W6a_all → ∀ Mul, W9_pipeline_of_levels Mul)
    (hA3 : W3_all → W4_all → W6a_all → ∀ Mul, W9_multiply_of_parts Mul) :
    ∀ Mul, W5_mulAt Mul → W9_multiply Mul := by
  intro Mul hM
  have hpre : W9_preNode Mul :=
    WP.W9comp.W9_preNode_of_phases_holds Mul (H9.preTranspose h3 h4 h6) (H9.altSum h3 h4 h6)
      (H9.spread Mul hM h3 h4 h6) (H9.preTwist Mul hM h3 h4 h6) (H9.synFFT h3 h4 h6)
      (H9.postTwist Mul hM h3 h4 h6) (H9.emitRows h3 h4 h6)
  have hpost : W9_postNode Mul :=
    WP.W9comp.W9_postNode_of_phases_holds Mul (H9.postTranspose h3 h4 h6)
      (H9.columnRoutes h3 h4 h6) (H9.columns Mul hM h3 h4 h6) (H9.postOutput h3 h4 h6)
  obtain ⟨hpl, hll, hpol⟩ := hA1 h3 h4 h6 Mul (H9.sweep h3 h4 h6) w9_retMark
    (H9.retFlip h3 h4 h6) hpre (H9.leafFFT Mul hM h3 h4 h6) hpost
  exact hA3 h3 h4 h6 Mul (hA2 h3 h4 h6 Mul (H9.level h3 h4 h6) hpl hll hpol)
    (H9.splitPack h3 h4 h6) (H9.square Mul hM h3 h4 h6) (H9.extract h3 h4 h6)
    (H9.reconstruct h3 h4 h6)

/-- W9comp's `W9StageThms` without `preTranspose`, in the same binding shape. W9b proves
`W9_preTranspose` from `W4_transpose .down .up`, which is not in `W4_all`. So the pre-transpose
kernel is a separate hypothesis that takes that W4 contract as an extra premise. -/
structure W9StageThms4 : Prop where
  altSum : W3_all → W4_all → W6a_all → W9_altSum
  spread : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_spread Mul
  preTwist : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_preTwist Mul
  synFFT : W3_all → W4_all → W6a_all → W9_synFFT
  postTwist : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_postTwist Mul
  emitRows : W3_all → W4_all → W6a_all → W9_emitRows
  postTranspose : W3_all → W4_all → W6a_all → W9_postTranspose
  columnRoutes : W3_all → W4_all → W6a_all → W9_columnRoutes
  columns : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_columns Mul
  postOutput : W3_all → W4_all → W6a_all → W9_postOutput
  leafFFT : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_leafFFT Mul
  splitPack : W3_all → W4_all → W6a_all → W9_splitPack
  square : ∀ Mul, W5_mulAt Mul → W3_all → W4_all → W6a_all → W9_square Mul
  extract : W3_all → W4_all → W6a_all → W9_extract
  reconstruct : W3_all → W4_all → W6a_all → W9_reconstruct
  retFlip : W3_all → W4_all → W6a_all → W9_retFlip
  sweep : W3_all → W4_all → W6a_all → W9_sweep
  level : W3_all → W4_all → W6a_all → W9_level

/-- The full `W9StageThms`: the separate pre-transpose kernel is fed `W4_transpose .down .up`. -/
theorem W9StageThms4.toStageThms (H : W9StageThms4) (h4trU : W4_transpose .down .up)
    (h9pT : W4_transpose .down .up → W3_all → W4_all → W6a_all → W9_preTranspose) :
    WP.W9comp.W9StageThms where
  preTranspose h3 h4 h6 := h9pT h4trU h3 h4 h6
  altSum := H.altSum
  spread := H.spread
  preTwist := H.preTwist
  synFFT := H.synFFT
  postTwist := H.postTwist
  emitRows := H.emitRows
  postTranspose := H.postTranspose
  columnRoutes := H.columnRoutes
  columns := H.columns
  postOutput := H.postOutput
  leafFFT := H.leafFFT
  splitPack := H.splitPack
  square := H.square
  extract := H.extract
  reconstruct := H.reconstruct
  retFlip := H.retFlip
  sweep := H.sweep
  level := H.level

/-- **The headline from leaf machine contracts** (plus, temporarily, the three W9 assembly Props).
| hypotheses | owner |
|---|---|
| `h3drop … h3concat` (10 unsigned W3 contracts) | W3 |
| `h4tr`, `h4trU` (`W4_transpose .down .down` / `.down .up`), `h4osf`, `h4or` | W4 / W4o |
| `h7std`, `h7tap`, `h7c01` (W7 kernels), `h7ref` (bit-exact builder) | W7k2 |
| `h9pT` (pre-transpose; extra premise `W4_transpose .down .up`) | W9b |
| `H9` (the other 18 W9 stage kernels, W9comp's binding shape) | W9a..h |
| `hA1`, `hA2` (levels, pipeline) | W9a |
| `hA3` (multiply from parts) | `WP.W9mp` |
| `hroot`, `hw` | W11b | -/
theorem intMul_TM2_nlogn_current4
    (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (h3drop : W3_dropNat) (h3norm : W3_normNat) (h3add : W3_addNat) (h3sub : W3_subNat)
    (h3shlC : W3_shlConst) (h3shrC : W3_shrConst) (h3shlV : W3_shlVar) (h3shrV : W3_shrVar)
    (h3split : W3_splitAt) (h3concat : W3_concatAt)
    (h4tr : W4_transpose .down .down) (h4osf : W4_oddStrideFactor)
    (h4or : W4_oddRoute .down .down) (h4trU : W4_transpose .down .up)
    (h7std : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_stdChar)
    (h7tap : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps →
      W7_sincGaussianTap)
    (h7c01 : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_c0c1)
    (h7ref : ∀ Mul, W5_mulAt Mul → (∃ K, ∀ w, Mul w ≤ K * (w + 1) ^ 2) → W7.Hyps → W7_kernels →
      W7_buildTablesRef W7.snapshotSchedule)
    (h9pT : W4_transpose .down .up → W3_all → W4_all → W6a_all → W9_preTranspose)
    (H9 : W9StageThms4)
    (hA1 : W3_all → W4_all → W6a_all → ∀ Mul, W9_levels_of_kernels Mul)
    (hA2 : W3_all → W4_all → W6a_all → ∀ Mul, W9_pipeline_of_levels Mul)
    (hA3 : W3_all → W4_all → W6a_all → ∀ Mul, W9_multiply_of_parts Mul)
    (hroot : W9RootOK wdF wdI wR)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    IntMulTM.IntMulNLogN := by
  have h3 := W3_all_of_open h3drop h3norm h3add h3sub h3shlC h3shrC h3shlV h3shrV h3split h3concat
  have h4 : W4_all := ⟨h4tr, h4osf, h4or, w4_moveRecord⟩
  have h6 : W6a_all := WP.W6a.W6a_holds h3sub
  have h5 : W5_toom3Mul := WP.W5.W5_toom3Mul_holds (TMFw.W3b.W3_addInt_holds h3add h3sub)
    (TMFw.W3b.W3_subInt_holds h3add h3sub) TMFw.W3b.W3_smallOpInt_holds h3split h3shlV
  exact intMul_TM2_nlogn_current3 wdF wdI wR h3add h3sub h3split h3shlV
    (W7_buildTables_of_leaves h3 h6 h5 h7std h7tap h7c01 h7ref)
    (W9_multiply_of_leaves h3 h4 h6 (H9.toStageThms h4trU h9pT) hA1 hA2 hA3) hroot hw

#assert_std_axioms W3_all_of_open W7_hyps_of W7_kernels_of W7_buildTables_of_leaves
  W9_multiply_of_leaves W9StageThms4.toStageThms intMul_TM2_nlogn_current4

end WP.Top
