import Contracts.W7.Format

/-!
# Contracts.W7.Shapes — canonical shapes, record widths, and serialized tape size

`TablesFaithful` is a correctness predicate only: a faithful hierarchy may carry unbounded unused
array entries beyond those read by the pipeline. W7 therefore delivers three more properties of the decoded
hierarchy, bundled with faithfulness in `W7.JointOutput`:

| Property | Predicate | Content |
|---|---|---|
| 2 shapes | `W7.Canonical` | leaf `K` stages of `2^(s+1)` entries; `t1` rows of exactly `W_eff` taps; pre/post twiddles and `c0`, `c1` of length `r` |
| 3 widths | `W7.EntryWidths` | taps `≤ 2·pSub` bits; twiddles and `c0`, `c1` `≤ pSub + 3` bits (leaf: `q_leaf + 3`); `c0`, `c1` real and `≥ 0`; column divisor `> 0` |
| 4 size | `W7.tapeBound` | per step level `(t1·W_eff + 3r + O(1))·O(pSub + H)` plus headers; leaf `O(2^K·q_leaf)` |

The record lengths behind `W7.tapeBound` are:
* tap `bitLen + 2 ≤ 2·pSub + 2`;
* complex record `≤ 2·pSub + 9`;
* post record `≤ 2·pSub + H + 11`, since `0 ≤ μ ≤ 2^H`.

Pure obligations (statements only; owner W7):
* `W7_tapeSize`: shapes and widths bound the tape;
* `W7_entryWidths_of_faithful`: faithful snapshot tables meet the widths.
-/

namespace TMFw.Contracts

open IntMul (ComputablePaperFastDFTSpec QuantizedFastDFTSpec read1D effectiveFilterWidth
  kroneckerSpreadNumBlocks)

/-- **Structural correspondence** between a table hierarchy and its schedule: same node chain, same
`p`, `t1`, `r` at every step, and leaf size `R = 2^K`. Every faithful hierarchy has it
(`W7.sameShape_of_faithful`, proved for the snapshot; a field of `W7.TableSchedule`). So a
schedule-generic consumer (W9) can read `t1`, `r` from the tape headers and still know they are the
schedule's powers of two (`W8_paperStop_dimsPow2`). -/
def W7.SameShape : ComputablePaperFastDFTSpec → QuantizedFastDFTSpec → Prop
  | .basePow2 p' K' _, .base p R => p' = p ∧ R = 2 ^ K'
  | .step p' _ _ t1' r' _ _ _ _ _ child', .step p _ t1 r _ _ child =>
      p' = p ∧ t1' = t1 ∧ r' = r ∧ W7.SameShape child' child
  | _, _ => False

/-- **Canonical shapes** (F6 item 2). Every array has exactly the length the pipeline reads, so the
tape (`W7.tape`, used entries only) carries the whole hierarchy. -/
def W7.Canonical : ComputablePaperFastDFTSpec → Prop
  | .basePow2 _ K tw => tw.size = K ∧ ∀ s < K, (tw.getD s #[]).size = 2 ^ (s + 1)
  | .step _ _ m1 t1 r taps pre post c0 c1 child =>
      taps.size = t1 ∧ (∀ j1 < t1, (taps.getD j1 []).length = effectiveFilterWidth m1 r) ∧
      pre.size = r ∧ post.size = r ∧ c0.size = r ∧ c1.size = r ∧ W7.Canonical child

/-- **Record width bounds** (F6 item 3), in bits of the magnitudes:
* folded taps: at most `2·pSub`;
* pre/post twiddles and `c0`, `c1`: at most `pSub + 3` (`2^(pSub+2)` scale);
* leaf twiddles: at most `q_leaf + 3`;
* `c0`, `c1`: real and non-negative;
* the class-R column divisor is positive (W6b's precondition).

`μ ≤ 2^H` holds by construction. -/
def W7.EntryWidths (F : W7.TapeFormat) : ComputablePaperFastDFTSpec → Prop
  | .basePow2 p K tw =>
      ∀ s < K, ∀ u < 2 ^ (s + 1),
        bitLen (read1D (tw.getD s #[]) u).1.natAbs ≤ F.qLeaf p K + 3 ∧
        bitLen (read1D (tw.getD s #[]) u).2.natAbs ≤ F.qLeaf p K + 3
  | .step _ pSub _ t1 r taps pre post c0 c1 child =>
      (∀ j1 < t1, ∀ g ∈ taps.getD j1 [], bitLen g.natAbs ≤ 2 * pSub) ∧
      (∀ k2 < r,
        bitLen (read1D pre k2).1.natAbs ≤ pSub + 3 ∧ bitLen (read1D pre k2).2.natAbs ≤ pSub + 3 ∧
        bitLen (read1D post k2).1.natAbs ≤ pSub + 3 ∧ bitLen (read1D post k2).2.natAbs ≤ pSub + 3) ∧
      (∀ u2 < r,
        (read1D c0 u2).2 = 0 ∧ (read1D c1 u2).2 = 0 ∧
        0 ≤ (read1D c0 u2).1 ∧ bitLen (read1D c0 u2).1.natAbs ≤ pSub + 3 ∧
        0 ≤ (read1D c1 u2).1 ∧ bitLen (read1D c1 u2).1.natAbs ≤ pSub + 3 ∧
        0 < IntMulTM.Contracts.W8.columnDivisor r u2 (read1D c0 u2).1 (read1D c1 u2).1) ∧
      W7.EntryWidths F child

/-- Explicit serialized-size bound (F6 item 4), mirroring `W7.tapeFrom` with the record bounds above.
Header lengths are kept exact; they are `O(log n)` symbols. -/
def W7.tapeBoundFrom (F : W7.TapeFormat) (pIn : ℕ) : ComputablePaperFastDFTSpec → ℕ
  | .basePow2 p K _ =>
      1 + (W7.header [p, K, F.qLeaf p K, pIn]).length + (2 ^ (K + 1) + K) * (2 * F.qLeaf p K + 9)
  | .step p pSub m1 t1 r _ _ _ _ _ child =>
      (1 + (W7.header [p, pSub, m1, t1, r, Nat.log2 t1, Nat.log2 r, effectiveFilterWidth m1 r,
          kroneckerSpreadNumBlocks m1 r, child.p, pIn]).length +
        t1 * (effectiveFilterWidth m1 r * (2 * pSub + 2) + 1) + 2 * r * (2 * pSub + 9) + 3) +
      W7.tapeBoundFrom F pSub child +
      (1 + (W7.header [p, pSub, t1, r, Nat.log2 t1, Nat.log2 r, child.p, F.hShift p pSub]).length +
        r * (2 * pSub + F.hShift p pSub + 11) + 1)

/-- The size bound of a whole tape. -/
def W7.tapeBound (F : W7.TapeFormat) (cSpec : ComputablePaperFastDFTSpec) : ℕ :=
  W7.tapeBoundFrom F 0 cSpec

/-- **Joint faithfulness, canonical shapes, entry widths, and tape-size bound** for `cSpec` and `spec`. -/
structure W7.JointOutput (F : W7.TapeFormat)
    (Faithful : ComputablePaperFastDFTSpec → QuantizedFastDFTSpec → Prop)
    (spec : QuantizedFastDFTSpec) (cSpec : ComputablePaperFastDFTSpec) : Prop where
  /-- 1: the parametric pipeline theorem applies (FTP:2304, or W14's `_at` variant). -/
  faithful : Faithful cSpec spec
  /-- 2: canonical shapes. -/
  canonical : W7.Canonical cSpec
  /-- 3: record width bounds. -/
  widths : W7.EntryWidths F cSpec
  /-- 4: serialized-size bound. -/
  size : (W7.tape F cSpec).length ≤ W7.tapeBound F cSpec

/-- The snapshot's tape constants: `q_leaf = 2p + K + 8` (CTB:96) and `H = 3·pSub + 2`
(`W8_numBound_of_widths` with `w = 4p′`, `pSub = 2p′`). -/
def W7.snapshotFormat : W7.TapeFormat :=
  ⟨fun p K => 2 * p + K + 8, fun _ pSub => 3 * pSub + 2⟩

/-- **W7_tapeSize** (pure; statement only; owner W7). Canonical shapes and record widths bound the
tape by `W7.tapeBound`.

*Route:* induction on `cSpec`; `List.length_append`, `List.length_flatten` and the record-length
lemmas `W7.length_realRec`, `W7.length_cplxRec`, `W7.length_postRec`. For `μ`,
`0 ≤ ⌊2^H/d⌋ ≤ 2^H` holds because `d > 0` (`EntryWidths`). The leaf stage sum is
`Σ_{s<K} 2^(s+1) = 2^(K+1) − 2`. -/
def W7_tapeSize : Prop :=
  ∀ (F : W7.TapeFormat) (cSpec : ComputablePaperFastDFTSpec),
    W7.Canonical cSpec → W7.EntryWidths F cSpec → (W7.tape F cSpec).length ≤ W7.tapeBound F cSpec

/-- **W7_entryWidths_of_faithful** (pure; statement only; owner W7). Faithful snapshot-schedule tables
meet the width bounds.

*Route:*
* taps: from `hTaps`, `|G s| ≤ 2^pSub + 1` and the folded sums, via CTB:324
  `fitsSignedScalarWord_fold_sum` (`4p′ − 1 ≤ 2·pSub` bits);
* twiddles: from the accuracy clauses (`‖tw/2^(q+2) − ζ‖ ≤ 2·cqme q` with `|ζ| = 1`, so
  `|tw.j| < 2^(q+3)`);
* `c0`, `c1`: from hC01 (FTP:76-78);
* divisor positivity: `W8_columnDivisor_pos_of_faithful_holds` (Contracts/W6.lean, proved).

`Canonical` is **not** implied by `TablesFaithful` (arrays may be longer); it is a separate machine
obligation. -/
def W7_entryWidths_of_faithful : Prop :=
  ∀ (L p K : ℕ), 8 ≤ p → K ≤ 2 ^ (L + 1) → ∀ cSpec : ComputablePaperFastDFTSpec,
    IntMul.TablesFaithful cSpec (IntMul.buildQuantizedSpecPaperStop L p K) →
    W7.EntryWidths W7.snapshotFormat cSpec

end TMFw.Contracts
