import Contracts.W9.Pre

/-!
# WP.W9d.TwistPure — value lemmas for the pre-twist (P4) and post-twist (P7)

Both twists multiply each entry `(j, k)` of a `t1 × r` matrix by the twiddle `tw[k]` and round
by a shift (W8_gPreTwistU_shift: `gPreTwistU q = twistF (2q)`; `gMulScaled q = twistF q`).

* `twistF s tw u`: the common entry map.
* `runScan2D_toList`, `mat_toList_eq`: the rows of `runScan2DWithSteps` and of a well-shaped
  matrix, as lists of `range` maps.
* `w9P_rows`, `w9QPost_rows`: the twist outputs row by row, as `zipWith` of the twiddle row.
* Widths of the entries read from tables and matrices.
-/

namespace WP.W9d

open IntMul TMFw TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- The common entry map of both twists: one complex product, then a rounding shift by `s`. -/
def twistF (s : ℕ) (tw u : ℤ × ℤ) : ℤ × ℤ :=
  (divRoundPow2 (tw.1 * u.1 - tw.2 * u.2) s, divRoundPow2 (tw.1 * u.2 + tw.2 * u.1) s)

theorem gPreTwistU_eq (q : ℕ) (tw u : ℤ × ℤ) : gPreTwistU q tw u = twistF (2 * q) tw u :=
  IntMulTM.Contracts.W8_gPreTwistU_shift_holds q tw u

theorem gMulScaled_eq (q : ℕ) (tw u : ℤ × ℤ) : gMulScaled q tw u = twistF q tw u := rfl

/-! ## Matrices as lists of rows -/

/-- An array of size `n` whose `read1D` agrees with `g` below `n` is `g` on `range n`. -/
theorem toList_eq_of_read1D {α : Type} [Zero α] (A : Array α) (n : ℕ) (g : ℕ → α)
    (hs : A.size = n) (hg : ∀ j < n, read1D A j = g j) : A.toList = (List.range n).map g := by
  apply List.ext_getElem
  · simp [hs]
  · intro j h1 _
    simp only [Array.length_toList] at h1
    rw [List.getElem_map, List.getElem_range, ← hg j (by omega)]
    simp [read1D, h1]

theorem runScan2D_fst_eq {α : Type} (n1 n2 : ℕ) (g : ℕ → ℕ → α) :
    (runScan2DWithSteps n1 n2 g).1 =
      Array.ofFn (fun i : Fin n1 => (runSequentialScanSteps (g i.val) n2).outTape) := by
  unfold runScan2DWithSteps
  exact IntMul.LevelSync.ofFn_dite_fst n1 _ #[]

/-- The rows of `runScan2DWithSteps n1 n2 g`. -/
theorem runScan2D_toList {α : Type} [Zero α] (n1 n2 : ℕ) (g : ℕ → ℕ → α) :
    (runScan2DWithSteps n1 n2 g).1.toList.map Array.toList =
      (List.range n1).map (fun i => (List.range n2).map (g i)) := by
  rw [runScan2D_fst_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 _
    simp only [List.length_map, Array.length_toList, Array.size_ofFn] at h1
    simp only [List.getElem_map, Array.getElem_toList, Array.getElem_ofFn, List.getElem_range]
    exact toList_eq_of_read1D _ n2 (g i) (size_runSequentialScanSteps _ _)
      (fun j hj => read1D_runSequentialScanSteps_eq _ _ _ hj)

/-- The rows of a well-shaped `n1 × n2` matrix. -/
theorem mat_toList_eq {α : Type} [Zero α] (M : Array (Array α)) (n1 n2 : ℕ) (hs : M.size = n1)
    (hr : ∀ row ∈ M.toList, row.size = n2) :
    M.toList.map Array.toList = (List.range n1).map (fun i => (List.range n2).map (read2D M i)) := by
  apply List.ext_getElem
  · simp [hs]
  · intro i h1 _
    simp only [List.length_map, Array.length_toList] at h1
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    have hmem : M.toList[i]'(by simpa using h1) ∈ M.toList := List.getElem_mem _
    rw [Array.getElem_toList] at hmem
    have hrow : M[i].size = n2 := hr _ hmem
    refine toList_eq_of_read1D _ n2 _ hrow (fun j hj => ?_)
    have hj' : j < M[i].size := by omega
    simp only [read1D, read2D, dif_pos h1, dif_pos hj']

/-- `matSyms` of a well-shaped matrix. -/
theorem matSyms_eq_range (M : Array (Array (ℤ × ℤ))) (n1 n2 : ℕ) (hs : M.size = n1)
    (hr : ∀ row ∈ M.toList, row.size = n2) :
    matSyms M = blkE ((List.range n1).map (fun i => (List.range n2).map (read2D M i))).flatten := by
  unfold matSyms
  rw [List.flatMap_def, mat_toList_eq M n1 n2 hs hr]

/-- `matSyms` of a `runScan2DWithSteps` matrix. -/
theorem matSyms_runScan2D (n1 n2 : ℕ) (g : ℕ → ℕ → ℤ × ℤ) :
    matSyms (runScan2DWithSteps n1 n2 g).1 =
      blkE ((List.range n1).map (fun i => (List.range n2).map (g i))).flatten := by
  unfold matSyms
  rw [List.flatMap_def, runScan2D_toList]

theorem map_range_zipWith {α β γ : Type} (n : ℕ) (f : α → β → γ) (a : ℕ → α) (b : ℕ → β) :
    (List.range n).map (fun k => f (a k) (b k)) =
      List.zipWith f ((List.range n).map a) ((List.range n).map b) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-! ## The twist outputs -/

/-- The twiddle row read by the machine: the first `r` entries of the table (`read1D`). -/
def twRow (r : ℕ) (tw : Array (ℤ × ℤ)) : List (ℤ × ℤ) := (List.range r).map (read1D tw)

/-- The input rows of a `t1 × r` matrix. -/
def inRows (t1 r : ℕ) (U : Array (Array (ℤ × ℤ))) : List (List (ℤ × ℤ)) :=
  (List.range t1).map (fun j => (List.range r).map (read2D U j))

theorem twSyms_eq (r : ℕ) (tw : Array (ℤ × ℤ)) :
    twSyms r tw = blkE (twRow r tw) ++ [symSub] := by
  simp only [twSyms, blkE, blk, twRow, List.flatMap_def, List.map_map]
  rfl

theorem matSyms_inRows (t1 r : ℕ) (U : Array (Array (ℤ × ℤ))) (hs : U.size = t1)
    (hr : ∀ row ∈ U.toList, row.size = r) : matSyms U = blkE (inRows t1 r U).flatten :=
  matSyms_eq_range U t1 r hs hr

/-- **The pre-twist, row by row.** -/
theorem matSyms_w9P (pSub t1 r : ℕ) (tw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) :
    matSyms (w9P pSub t1 r tw U) =
      blkE ((inRows t1 r U).map (List.zipWith (twistF (2 * pSub)) (twRow r tw))).flatten := by
  unfold w9P
  rw [matSyms_runScan2D]
  congr 2
  simp only [inRows, List.map_map]
  congr 1
  funext j
  simp only [Function.comp, twRow, gPreTwistU_eq]
  exact map_range_zipWith r (twistF (2 * pSub)) (read1D tw) (read2D U j)

/-- **The post-twist, row by row.** -/
theorem matSyms_w9QPost (pSub t1 r : ℕ) (tw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ))) :
    matSyms (w9QPost pSub t1 r tw Q) =
      blkE ((inRows t1 r Q).map (List.zipWith (twistF (pSub + 2)) (twRow r tw))).flatten := by
  unfold w9QPost
  rw [matSyms_runScan2D]
  congr 2
  simp only [inRows, List.map_map]
  congr 1
  funext j
  simp only [Function.comp, twRow, gMulScaled_eq]
  exact map_range_zipWith r (twistF (pSub + 2)) (read1D tw) (read2D Q j)

/-! ## Shapes and widths -/

theorem length_twRow (r : ℕ) (tw : Array (ℤ × ℤ)) : (twRow r tw).length = r := by
  simp [twRow]

theorem length_inRows (t1 r : ℕ) (U : Array (Array (ℤ × ℤ))) : (inRows t1 r U).length = t1 := by
  simp [inRows]

theorem length_of_mem_inRows {t1 r : ℕ} {U : Array (Array (ℤ × ℤ))} {row : List (ℤ × ℤ)}
    (h : row ∈ inRows t1 r U) : row.length = r := by
  simp only [inRows, List.mem_map, List.mem_range] at h
  obtain ⟨j, -, rfl⟩ := h
  simp

theorem twRow_width {w r : ℕ} {tw : Array (ℤ × ℤ)} (h : TwW w r tw) :
    ∀ z ∈ twRow r tw, EntryW w z := by
  intro z hz
  simp only [twRow, List.mem_map, List.mem_range] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  exact h k hk

/-- Entries of a well-shaped matrix of width `≤ w`. -/
theorem inRows_width {w t1 r : ℕ} {U : Array (Array (ℤ × ℤ))} (hs : U.size = t1)
    (hr : ∀ row ∈ U.toList, row.size = r) (hw : MatW w U) :
    ∀ row ∈ inRows t1 r U, ∀ z ∈ row, EntryW w z := by
  intro row hrow z hz
  have h := mat_toList_eq U t1 r hs hr
  have hrow' : row ∈ U.toList.map Array.toList := by
    rw [h]
    exact hrow
  simp only [List.mem_map] at hrow'
  obtain ⟨a, ha, rfl⟩ := hrow'
  exact hw a ha z (by simpa using hz)

/-- Every entry of the twist output has width `≤ w` (from `MatW w` of the output matrix). -/
theorem outRows_width {w : ℕ} {M : Array (Array (ℤ × ℤ))} {rows : List (List (ℤ × ℤ))}
    (hM : matSyms M = blkE rows.flatten) (hrows : M.toList.map Array.toList = rows)
    (hw : MatW w M) : ∀ row ∈ rows, ∀ z ∈ row, EntryW w z := by
  intro row hrow z hz
  rw [← hrows] at hrow
  simp only [List.mem_map] at hrow
  obtain ⟨a, ha, rfl⟩ := hrow
  exact hw a ha z (by simpa using hz)

/-- The rows of the pre-twist output. -/
theorem w9P_toList (pSub t1 r : ℕ) (tw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ))) :
    (w9P pSub t1 r tw U).toList.map Array.toList =
      (inRows t1 r U).map (List.zipWith (twistF (2 * pSub)) (twRow r tw)) := by
  unfold w9P
  rw [runScan2D_toList]
  simp only [inRows, List.map_map]
  congr 1
  funext j
  simp only [Function.comp, twRow, gPreTwistU_eq]
  exact map_range_zipWith r (twistF (2 * pSub)) (read1D tw) (read2D U j)

/-- The rows of the post-twist output. -/
theorem w9QPost_toList (pSub t1 r : ℕ) (tw : Array (ℤ × ℤ)) (Q : Array (Array (ℤ × ℤ))) :
    (w9QPost pSub t1 r tw Q).toList.map Array.toList =
      (inRows t1 r Q).map (List.zipWith (twistF (pSub + 2)) (twRow r tw)) := by
  unfold w9QPost
  rw [runScan2D_toList]
  simp only [inRows, List.map_map]
  congr 1
  funext j
  simp only [Function.comp, twRow, gMulScaled_eq]
  exact map_range_zipWith r (twistF (pSub + 2)) (read1D tw) (read2D Q j)

#assert_std_axioms gPreTwistU_eq gMulScaled_eq toList_eq_of_read1D runScan2D_fst_eq
  runScan2D_toList mat_toList_eq matSyms_eq_range matSyms_runScan2D map_range_zipWith twSyms_eq
  matSyms_inRows matSyms_w9P matSyms_w9QPost length_twRow length_inRows length_of_mem_inRows
  twRow_width inRows_width outRows_width w9P_toList w9QPost_toList

end WP.W9d
