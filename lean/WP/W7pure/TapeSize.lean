import WP.W7pure.Basic

/-!
# WP.W7pure.TapeSize — `W7_tapeSize`: canonical shapes and record widths bound the tape

`W7_tapeSize` (Contracts/W7/Shapes.lean:117): for every tape format `F` and hierarchy `cSpec`,
`W7.Canonical cSpec → W7.EntryWidths F cSpec → (W7.tape F cSpec).length ≤ W7.tapeBound F cSpec`.

Proof: induction on `cSpec` (generalizing the header field `pIn`), with one length lemma per segment.
Record lengths come from `W7.length_realRec`, `W7.length_cplxRec`, `W7.length_postRec`:

| segment | bound used | source |
|---|---|---|
| leaf, stage `s` | `2^(s+1)` complex records of `≤ 2q+9` symbols, plus `tagSub` | `EntryWidths` (leaf), `length_stages_le` |
| pre, row `j1` | `W_eff` real records of `≤ 2·pSub+2` symbols, plus `tagRow` | `Canonical` (row length), `EntryWidths` (taps) |
| pre, twiddles | `2r` complex records of `≤ 2·pSub+9` symbols | `EntryWidths` (twiddles) |
| post | `r` records of `≤ 2·pSub+H+11` symbols | `EntryWidths` (`c0`, `c1`, divisor `> 0` ⇒ `0 ≤ μ ≤ 2^H`) |

Only the row lengths need `Canonical`; the other arrays are read through `read1D`.
-/

namespace WP.W7pure

open TMFw.Contracts IntMul

/-- A filter row: `l.length` real records of at most `w + 2` symbols each, then `tagRow`. -/
theorem length_row_le (l : List ℤ) (w : ℕ) (h : ∀ g ∈ l, bitLen g.natAbs ≤ w) :
    ((l.map W7.realRec).flatten ++ [W7.tagRow]).length ≤ l.length * (w + 2) + 1 := by
  rw [List.length_append, List.length_singleton]
  have h1 := length_flatten_map_le l W7.realRec (w + 2) (fun g hg => by
    rw [W7.length_realRec]
    have h2 := h g hg
    omega)
  omega

/-- **Leaf segment.** -/
theorem length_leafSeg_le (pIn p K q : ℕ) (tw : Array (Array (ℤ × ℤ)))
    (h : ∀ s < K, ∀ u < 2 ^ (s + 1),
      bitLen (read1D (tw.getD s #[]) u).1.natAbs ≤ q + 3 ∧
        bitLen (read1D (tw.getD s #[]) u).2.natAbs ≤ q + 3) :
    (W7.leafSeg pIn p K q tw).length ≤
      1 + (W7.header [p, K, q, pIn]).length + (2 ^ (K + 1) + K) * (2 * q + 9) := by
  have hst := length_stages_le K (2 * q + 9)
    (fun s => ((List.range (2 ^ (s + 1))).map fun u =>
      W7.cplxRec (read1D (tw.getD s #[]) u)).flatten ++ [W7.tagSub])
    (fun s hs => by
      rw [List.length_append, List.length_singleton]
      have h1 := length_flatten_map_range_le (2 ^ (s + 1))
        (fun u => W7.cplxRec (read1D (tw.getD s #[]) u)) (2 * q + 9) (fun u hu => by
          rw [W7.length_cplxRec]
          have h2 := h s hs u hu
          omega)
      omega)
  have e : (2 ^ (K + 1) + K) * (2 * q + 9) = 2 ^ (K + 1) * (2 * q + 9) + K * (2 * q + 9) := by
    ring
  have hK : K ≤ K * (2 * q + 9) := Nat.le_mul_of_pos_right K (by omega)
  unfold W7.leafSeg
  rw [List.length_cons, List.length_append]
  omega

/-- **Pre segment.** -/
theorem length_preSeg_le (pIn p pSub m1 t1 r childP : ℕ) (taps : Array (List ℤ))
    (pre post : Array (ℤ × ℤ))
    (hrows : ∀ j1 < t1, (taps.getD j1 []).length = effectiveFilterWidth m1 r)
    (htaps : ∀ j1 < t1, ∀ g ∈ taps.getD j1 [], bitLen g.natAbs ≤ 2 * pSub)
    (htw : ∀ k2 < r,
      bitLen (read1D pre k2).1.natAbs ≤ pSub + 3 ∧ bitLen (read1D pre k2).2.natAbs ≤ pSub + 3 ∧
        bitLen (read1D post k2).1.natAbs ≤ pSub + 3 ∧
        bitLen (read1D post k2).2.natAbs ≤ pSub + 3) :
    (W7.preSeg pIn p pSub m1 t1 r childP taps pre post).length ≤
      1 + (W7.header [p, pSub, m1, t1, r, Nat.log2 t1, Nat.log2 r, effectiveFilterWidth m1 r,
          kroneckerSpreadNumBlocks m1 r, childP, pIn]).length +
        t1 * (effectiveFilterWidth m1 r * (2 * pSub + 2) + 1) + 2 * r * (2 * pSub + 9) + 3 := by
  have hA := length_flatten_map_range_le t1
    (fun j1 => ((taps.getD j1 []).map W7.realRec).flatten ++ [W7.tagRow])
    (effectiveFilterWidth m1 r * (2 * pSub + 2) + 1) (fun j1 hj1 => by
      have h1 := length_row_le (taps.getD j1 []) (2 * pSub) (htaps j1 hj1)
      rw [hrows j1 hj1] at h1
      exact h1)
  have hB := length_flatten_map_range_le r (fun k2 => W7.cplxRec (read1D pre k2)) (2 * pSub + 9)
    (fun k2 hk2 => by
      rw [W7.length_cplxRec]
      obtain ⟨h1, h2, -, -⟩ := htw k2 hk2
      omega)
  have hC := length_flatten_map_range_le r (fun k2 => W7.cplxRec (read1D post k2)) (2 * pSub + 9)
    (fun k2 hk2 => by
      rw [W7.length_cplxRec]
      obtain ⟨-, -, h1, h2⟩ := htw k2 hk2
      omega)
  have e : 2 * r * (2 * pSub + 9) = r * (2 * pSub + 9) + r * (2 * pSub + 9) := by ring
  unfold W7.preSeg
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

/-- **Post segment.** `μ = ⌊2^H / d⌋` with `d > 0` has at most `H + 1` bits. -/
theorem length_postSeg_le (p pSub t1 r childP H : ℕ) (c0 c1 : Array (ℤ × ℤ))
    (hc : ∀ u2 < r,
      bitLen (read1D c0 u2).1.natAbs ≤ pSub + 3 ∧ bitLen (read1D c1 u2).1.natAbs ≤ pSub + 3 ∧
        0 < IntMulTM.Contracts.W8.columnDivisor r u2 (read1D c0 u2).1 (read1D c1 u2).1) :
    (W7.postSeg p pSub t1 r childP H c0 c1).length ≤
      1 + (W7.header [p, pSub, t1, r, Nat.log2 t1, Nat.log2 r, childP, H]).length +
        r * (2 * pSub + H + 11) + 1 := by
  have hA := length_flatten_map_range_le r (fun u2 =>
      W7.postRec (read1D c0 u2).1 (read1D c1 u2).1
        (W7.colRecip H r u2 (read1D c0 u2).1 (read1D c1 u2).1)) (2 * pSub + H + 11)
    (fun u2 hu2 => by
      rw [W7.length_postRec]
      obtain ⟨h1, h2, hd⟩ := hc u2 hu2
      have h3 := bitLen_colRecip_le H r u2 _ _ hd
      omega)
  unfold W7.postSeg
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

/-- `W7_tapeSize` for every header field `pIn`. -/
theorem tapeFrom_length_le (F : W7.TapeFormat) (cSpec : ComputablePaperFastDFTSpec) :
    ∀ pIn : ℕ, W7.Canonical cSpec → W7.EntryWidths F cSpec →
      (W7.tapeFrom F pIn cSpec).length ≤ W7.tapeBoundFrom F pIn cSpec := by
  induction cSpec with
  | basePow2 p K tw =>
    intro pIn _ hW
    simp only [W7.EntryWidths] at hW
    simp only [W7.tapeFrom, W7.tapeBoundFrom]
    exact length_leafSeg_le pIn p K (F.qLeaf p K) tw hW
  | step p pSub m1 t1 r taps pre post c0 c1 child ih =>
    intro pIn hC hW
    simp only [W7.Canonical] at hC
    simp only [W7.EntryWidths] at hW
    obtain ⟨-, hrows, -, -, -, -, hCc⟩ := hC
    obtain ⟨htaps, htw, hc01, hWc⟩ := hW
    have hpre := length_preSeg_le pIn p pSub m1 t1 r child.p taps pre post hrows htaps htw
    have hpost := length_postSeg_le p pSub t1 r child.p (F.hShift p pSub) c0 c1
      (fun u2 hu2 => by
        obtain ⟨-, -, -, h0, -, h1, hd⟩ := hc01 u2 hu2
        exact ⟨h0, h1, hd⟩)
    have hchild := ih pSub hCc hWc
    simp only [W7.tapeFrom, W7.tapeBoundFrom, List.length_append]
    omega

/-- **W7_tapeSize** (Contracts/W7/Shapes.lean:117). -/
theorem W7_tapeSize_holds : W7_tapeSize :=
  fun F cSpec hC hW => tapeFrom_length_le F cSpec 0 hC hW

#assert_std_axioms length_row_le length_leafSeg_le length_preSeg_le length_postSeg_le
  tapeFrom_length_le W7_tapeSize_holds

end WP.W7pure
