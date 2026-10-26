import WP.W11b.Defs

/-!
# WP.W11b.Shapes — sizes of the phase arrays, and widths of pure data movement

* sizes: spread rows (`r`), radix-2 core stages (`2^s`), the W9 phase matrices;
* transposes and flattenings only copy entries, so they preserve `EntryW` bounds.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

theorem size_spreadRow (p_in q m1 r : ℕ) (taps : List ℤ) (row : Array (ℤ × ℤ)) :
    (computableSpreadRowContiguous p_in q m1 r taps row).size = r := by
  simp [computableSpreadRowContiguous, computableSpreadRowContiguousWithCost]

theorem size_core (p_in q : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    ∀ (s : ℕ) (y : Array (ℤ × ℤ)),
      (computableBaseRadix2FFTCoreWithProgramCost p_in q tw s y).1.size = 2 ^ s
  | 0, y => by simp [computableBaseRadix2FFTCoreWithProgramCost]
  | s + 1, y => by simp [computableBaseRadix2FFTCoreWithProgramCost]

theorem entryW_of_read1D_zero {w : ℕ} {x : Array (ℤ × ℤ)} {k : ℕ} (hk : ¬ k < x.size) :
    EntryW w (read1D x k) := by
  unfold read1D
  rw [dif_neg hk]
  exact entryW_zero w

/-- A transpose only moves entries. -/
theorem arrW_transpose {w : ℕ} (m r : ℕ) {tape : ℕ → ℤ × ℤ} (h : ∀ k, EntryW w (tape k)) :
    ArrW w (runMultiTapeTranspose m r tape) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · intro z hz
    have hlen := List.length_pos_of_mem hz
    simp [size_runMultiTapeTranspose, hr] at hlen
  refine arrW_of_read1D fun k hk => ?_
  rw [size_runMultiTapeTranspose] at hk
  have hj : k / r < 2 ^ m := (Nat.div_lt_iff_lt_mul hr).2 hk
  have hi : k % r < r := Nat.mod_lt _ hr
  have he := read1D_runMultiTapeTranspose_index_eq m r hr tape (k / r) (k % r) hj hi
  rw [Nat.div_add_mod' k r] at he
  rw [he]
  exact h _

/-- A flattening only moves entries. -/
theorem entryW_flatten {w C : ℕ} (hC : 0 < C) {mat : Array (Array (ℤ × ℤ))} (h : MatW w mat)
    (n k : ℕ) : EntryW w (read1D (runFlatten2DSteps C mat n).outTape k) := by
  by_cases hk : k < n
  · rw [read1D_runFlatten2DSteps_eq C hC mat n k hk]
    exact entryW_read2D_of_matW h _ _
  · exact entryW_of_read1D_zero (by simpa using hk)

/-- The row matrix of a node is a transpose of the node. -/
theorem read2D_w9XRows {t1 r : ℕ} (x : Array (ℤ × ℤ)) (m : ℕ) (ht1 : t1 = 2 ^ m) (hr : 0 < r)
    {j1 i : ℕ} (hj1 : j1 < t1) (hi : i < r) :
    read2D (w9XRows t1 r x) j1 i = read1D x (i * t1 + j1) := by
  unfold w9XRows
  dsimp only
  rw [read2D_runScan2DWithSteps_of_lt t1 r _ hj1 hi]
  have hm : natLog2Fuel t1 t1 = m := by rw [natLog2Fuel_self, ht1, Nat.log2_two_pow]
  rw [hm]
  have hj1' : j1 < 2 ^ m := ht1 ▸ hj1
  rw [read1D_runMultiTapeTranspose_index_eq m r hr _ j1 i hj1' hi, ← ht1]

theorem matW_w9XRows {w t1 r : ℕ} {x : Array (ℤ × ℤ)} (hx : ArrW w x) :
    MatW w (w9XRows t1 r x) := by
  unfold w9XRows
  dsimp only
  refine matW_runScan2D fun i _ j _ => ?_
  exact entryW_read1D_of_arrW (arrW_transpose _ _ fun k => entryW_read1D_of_arrW hx k) _

theorem size_w9XRows (t1 r : ℕ) (x : Array (ℤ × ℤ)) : (w9XRows t1 r x).size = t1 := by
  unfold w9XRows
  exact runScan2DWithSteps_fst_size _ _ _

theorem rows_w9XRows (t1 r : ℕ) (x : Array (ℤ × ℤ)) :
    ∀ row ∈ (w9XRows t1 r x).toList, row.size = r := by
  intro row hrow
  unfold w9XRows at hrow
  exact runScan2D_mem_size hrow

#assert_std_axioms size_spreadRow size_core entryW_of_read1D_zero arrW_transpose entryW_flatten
  read2D_w9XRows matW_w9XRows size_w9XRows rows_w9XRows

end WP.W11b
