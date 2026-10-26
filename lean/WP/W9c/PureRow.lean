import Contracts.W9.Pre

/-!
# WP.W9c.PureRow — the static-stride spread row, one coordinate at a time

`W8.spreadRowWithStride (fun _ _ => s) p_in q m1 r taps row` (the value of `W9_spreadRow`) is the
pair of two independent one-coordinate spreads (`spread1`) of the real and the imaginary parts of
the row (`spreadRow_toList`). Each coordinate is a sum over blocks `b < nb` and slots `i < 2·W` of
the block product `prodB … b` (`polyMulKroneckerSignedComputable s` of the quantized block `blockF`
and the taps), put into bucket `((b·W + i) − m1) mod r`.

All statements are about the snapshot's definitions as W8 restates them; nothing here is new
mathematics.
-/

namespace WP.W9c

open IntMul
open scoped BigOperators

/-- The effective filter width `W = min(2·m1 + 1, r)`. -/
abbrev Wf (m1 r : ℕ) : ℕ := effectiveFilterWidth m1 r

/-- The number of blocks `nb = ⌈r / W⌉`. -/
abbrev NB (m1 r : ℕ) : ℕ := kroneckerSpreadNumBlocks m1 r

/-- The quantized block `b` of one coordinate `x` (length `W`; zero past the row end). -/
def blockF (p_in q m1 r : ℕ) (x : List ℤ) (b : ℕ) : List ℤ :=
  (List.range (Wf m1 r)).map fun a =>
    if b * Wf m1 r + a < r then gQuantizeCoordToScale p_in q (x.getD (b * Wf m1 r + a) 0) else 0

/-- The block product at static stride `s`. -/
def prodB (s p_in q m1 r : ℕ) (taps x : List ℤ) (b : ℕ) : List ℤ :=
  polyMulKroneckerSignedComputable s (blockF p_in q m1 r x b) taps

/-- The bucket of slot `i` of block `b`. -/
def bucket (m1 r b i : ℕ) : ℕ := ((((b * Wf m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat

/-- Bucket `k` of one coordinate of the spread row. -/
def spread1At (s p_in q m1 r : ℕ) (taps x : List ℤ) (k : ℕ) : ℤ :=
  ∑ b ∈ Finset.range (NB m1 r), ∑ i ∈ Finset.range (2 * Wf m1 r),
    if bucket m1 r b i = k then (prodB s p_in q m1 r taps x b).getD i 0 else 0

/-- One coordinate of the spread row (`r` buckets). -/
def spread1 (s p_in q m1 r : ℕ) (taps x : List ℤ) : List ℤ :=
  (List.range r).map (spread1At s p_in q m1 r taps x)

theorem length_spread1 (s p_in q m1 r : ℕ) (taps x : List ℤ) :
    (spread1 s p_in q m1 r taps x).length = r := by
  simp [spread1]

/-! ## The row is the pair of its two coordinates -/

theorem read1D_toArray (l : List ℤ) (i : ℕ) : read1D l.toArray i = l.getD i 0 := by
  unfold read1D
  by_cases h : i < l.length
  · rw [dif_pos (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rw [dif_neg (by simpa using h)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem blockRe_eq (p_in q m1 r : ℕ) (row : Array (ℤ × ℤ)) (b : ℕ) :
    computableSpreadRowBlockReContiguous p_in q m1 r row b =
      blockF p_in q m1 r (row.toList.map Prod.fst) b := by
  unfold computableSpreadRowBlockReContiguous blockF
  refine List.map_congr_left fun a _ => ?_
  split_ifs with h
  · congr 1
    unfold read1D
    by_cases hi : b * Wf m1 r + a < row.size
    · rw [dif_pos hi]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [dif_neg hi]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
  · rfl

theorem blockIm_eq (p_in q m1 r : ℕ) (row : Array (ℤ × ℤ)) (b : ℕ) :
    computableSpreadRowBlockImContiguous p_in q m1 r row b =
      blockF p_in q m1 r (row.toList.map Prod.snd) b := by
  unfold computableSpreadRowBlockImContiguous blockF
  refine List.map_congr_left fun a _ => ?_
  split_ifs with h
  · congr 1
    unfold read1D
    by_cases hi : b * Wf m1 r + a < row.size
    · rw [dif_pos hi]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [dif_neg hi]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
  · rfl

/-- Entry `k < r` of the static-stride spread row. -/
theorem spreadRow_getElem (s p_in q m1 r : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ)) (k : ℕ)
    (hk : k < r) :
    read1D (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => s) p_in q m1 r taps row) k =
      (spread1At s p_in q m1 r taps (row.toList.map Prod.fst) k,
        spread1At s p_in q m1 r taps (row.toList.map Prod.snd) k) := by
  unfold IntMulTM.Contracts.W8.spreadRowWithStride IntMulTM.Contracts.W8.spreadRowFromPairs
  dsimp only
  rw [read1D_ofFn_of_lt _ _ hk]
  dsimp only
  rw [read1D_overlapAddBucketsSinglePass_of_lt _ _ _ _ _ _ hk,
    read1D_overlapAddBucketsSinglePass_of_lt _ _ _ _ _ _ hk]
  simp only [sumRangeInt_eq_sum]
  unfold spread1At
  refine Prod.ext ?_ ?_ <;> dsimp only
  · refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun i _ => ?_
    have hb' : b < (IntMulTM.Contracts.W8.spreadBlockPairs (fun _ _ => s) p_in q m1 r taps
        row).size := by
      simpa [IntMulTM.Contracts.W8.spreadBlockPairs] using hb
    rw [dif_pos hb']
    simp only [IntMulTM.Contracts.W8.spreadBlockPairs, Array.getElem_ofFn]
    rw [read1D_toArray, blockRe_eq]
    rfl
  · refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun i _ => ?_
    have hb' : b < (IntMulTM.Contracts.W8.spreadBlockPairs (fun _ _ => s) p_in q m1 r taps
        row).size := by
      simpa [IntMulTM.Contracts.W8.spreadBlockPairs] using hb
    rw [dif_pos hb']
    simp only [IntMulTM.Contracts.W8.spreadBlockPairs, Array.getElem_ofFn]
    rw [read1D_toArray, blockIm_eq]
    rfl

theorem size_spreadRow (s p_in q m1 r : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ)) :
    (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => s) p_in q m1 r taps row).size = r := by
  simp [IntMulTM.Contracts.W8.spreadRowWithStride, IntMulTM.Contracts.W8.spreadRowFromPairs]

/-- **The spread row is the zip of its two coordinates.** -/
theorem spreadRow_toList (s p_in q m1 r : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ)) :
    (IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => s) p_in q m1 r taps row).toList =
      List.zip (spread1 s p_in q m1 r taps (row.toList.map Prod.fst))
        (spread1 s p_in q m1 r taps (row.toList.map Prod.snd)) := by
  apply List.ext_getElem
  · simp [size_spreadRow, length_spread1]
  · intro k h1 h2
    have hk : k < r := by simpa [size_spreadRow] using h1
    have e := spreadRow_getElem s p_in q m1 r taps row k hk
    unfold read1D at e
    rw [dif_pos (by rw [size_spreadRow]; exact hk)] at e
    simp only [Array.getElem_toList, List.getElem_zip]
    rw [e]
    simp [spread1]

#assert_std_axioms length_spread1 read1D_toArray blockRe_eq blockIm_eq spreadRow_getElem
  size_spreadRow spreadRow_toList

end WP.W9c
