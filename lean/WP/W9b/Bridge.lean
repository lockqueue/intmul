import Contracts.W9.Pre

/-!
# WP.W9b.Bridge — pure index bridges: W4's routing specs against the snapshot's routers

W4's contracts state the routing kernels with the list specs `transposeL` and `oddRouteL`
(`Contracts.Machine.W4`). The snapshot's PRE/POST phases use the head-step machines
`runMultiTapeTranspose` (ST:704) and `runMultiTapeAffineOddRoute` (ST:873). This file proves them
equal, from the snapshot's own index identities:

* `runMultiTapeTranspose_toList`: `(runMultiTapeTranspose m r (read1D x)).toList =
  transposeL r (2^m) x.toList`, from `read1D_runMultiTapeTranspose_index_eq` (ST:810).
* `runMultiTapeAffineOddRoute_toList`: `(runMultiTapeAffineOddRoute m w b (read1D v)).toList =
  oddRouteL m w b v.toList` for odd `w`, from `read1D_runMultiTapeAffineOddRoute_index_eq` (ST:974).
* `w9XRows_flat`: P1's value `w9XRows t1 r x` (the `xRows` of `preNodeV`), flattened row-major, is
  `transposeL r t1 x.toList` when `t1 = 2^(log t1)` and `x.size = t1·r`.
* `matSyms_w9XRows`: the same at the symbol level, i.e. exactly what `W4_transpose` (dimensions
  `2^m_r × 2^m_t1`) pushes.
-/

namespace WP.W9b

open IntMul IntMul.LevelSync TMFw TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-! ## Index arithmetic and list helpers -/

/-- The source index of a row-major transpose is in range. -/
theorem transpose_idx_lt {rows cols k : ℕ} (hk : k < cols * rows) :
    k % rows * cols + k / rows < rows * cols := by
  have hr : 0 < rows := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hj : k / rows < cols := (Nat.div_lt_iff_lt_mul hr).2 hk
  have hi : k % rows < rows := Nat.mod_lt _ hr
  calc k % rows * cols + k / rows < k % rows * cols + cols := Nat.add_lt_add_left hj _
    _ = (k % rows + 1) * cols := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ rows * cols := Nat.mul_le_mul_right _ hi

/-- `transposeL` commutes with `map` (no default is ever read). -/
theorem transposeL_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (rows cols : ℕ)
    (l : List α) (hl : l.length = rows * cols) :
    (transposeL rows cols l).map f = transposeL rows cols (l.map f) := by
  unfold transposeL
  rw [List.map_map]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  have hlt := transpose_idx_lt hk
  have h1 : k % rows * cols + k / rows < l.length := by rw [hl]; exact hlt
  have h2 : k % rows * cols + k / rows < (l.map f).length := by rw [List.length_map]; exact h1
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getElem_map]

section Generic

variable {α : Type} [Zero α]

theorem toList_getElem_eq_read1D (a : Array α) (k : ℕ) (hk : k < a.toList.length) :
    a.toList[k] = read1D a k := by
  have hk' : k < a.size := by simpa using hk
  unfold read1D
  rw [dif_pos hk']
  simp

theorem size_runMultiTapeTranspose (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTranspose m r tape).size = 2 ^ m * r := by
  cases m with
  | zero => simp [runMultiTapeTranspose]
  | succ m =>
    simp only [runMultiTapeTranspose, size_runInterleaveRunsSteps]
    ring

theorem size_runMultiTapeAffineOddRoute (m w b : ℕ) (col : ℕ → α) :
    (runMultiTapeAffineOddRoute m w b col).size = 2 ^ m := by
  cases m with
  | zero => simp [runMultiTapeAffineOddRoute]
  | succ m =>
    simp only [runMultiTapeAffineOddRoute, size_runInterleaveParitySteps]
    ring

/-- A sequential scan materializes its tape. -/
theorem scan_outTape_eq_ofFn (g : ℕ → α) (n : ℕ) :
    (runSequentialScanSteps g n).outTape = Array.ofFn (fun j : Fin n => g j) := by
  apply Array.ext
  · simp
  · intro j h1 h2
    have e := read1D_runSequentialScanSteps_eq g n j (by simpa using h1)
    unfold read1D at e
    rw [dif_pos h1] at e
    rw [e, Array.getElem_ofFn]

/-- `runScan2DWithSteps` materializes its function. -/
theorem scan2D_eq_ofFn (n1 n2 : ℕ) (f : ℕ → ℕ → α) :
    (runScan2DWithSteps n1 n2 f).1 =
      Array.ofFn (fun i : Fin n1 => Array.ofFn (fun j : Fin n2 => f i j)) := by
  unfold runScan2DWithSteps
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [scan_outTape_eq_ofFn]

/-- Cutting an array of `n1·n2` entries into `n1` rows of `n2` and flattening them again. -/
theorem flat_ofFn_rows (a : Array α) (n1 n2 : ℕ) (ha : a.size = n1 * n2) :
    (Array.ofFn (fun i : Fin n1 => Array.ofFn (fun j : Fin n2 =>
      read1D a (i * n2 + j)))).toList.flatMap Array.toList = a.toList := by
  have h1 : a.toList = List.ofFn (fun k : Fin (n1 * n2) => read1D a k) := by
    apply List.ext_getElem
    · simp [ha]
    · intro k hk1 hk2
      rw [List.getElem_ofFn, toList_getElem_eq_read1D _ _ hk1]
  rw [h1, List.ofFn_mul, List.flatMap_def, Array.toList_ofFn, List.map_ofFn]
  congr 2
  funext i
  simp

/-- **Transpose bridge.** The snapshot's multi-pass transpose of an `r × 2^m` array is W4's
`transposeL r (2^m)`. -/
theorem runMultiTapeTranspose_toList [Inhabited α] (m r : ℕ) (hr : 0 < r) (x : Array α)
    (hx : x.size = r * 2 ^ m) :
    (runMultiTapeTranspose m r (read1D x)).toList = transposeL r (2 ^ m) x.toList := by
  apply List.ext_getElem
  · simp [transposeL, size_runMultiTapeTranspose]
  · intro k h1 h2
    have hk : k < 2 ^ m * r := by simpa [size_runMultiTapeTranspose] using h1
    have hj : k / r < 2 ^ m := (Nat.div_lt_iff_lt_mul hr).2 hk
    have hi : k % r < r := Nat.mod_lt _ hr
    have key := read1D_runMultiTapeTranspose_index_eq m r hr (read1D x) (k / r) (k % r) hj hi
    rw [Nat.div_add_mod' k r] at key
    rw [toList_getElem_eq_read1D _ _ h1, key]
    simp only [transposeL, List.getElem_map, List.getElem_range]
    have hlt : k % r * 2 ^ m + k / r < x.size := by rw [hx]; exact transpose_idx_lt hk
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    unfold read1D
    rw [dif_pos hlt]
    simp

/-- **Odd-route bridge.** The snapshot's affine odd-stride router is W4's `oddRouteL`. -/
theorem runMultiTapeAffineOddRoute_toList [Inhabited α] (m w b : ℕ) (hw : w % 2 = 1)
    (v : Array α) (hv : v.size = 2 ^ m) :
    (runMultiTapeAffineOddRoute m w b (read1D v)).toList = oddRouteL m w b v.toList := by
  apply List.ext_getElem
  · simp [oddRouteL, size_runMultiTapeAffineOddRoute]
  · intro k h1 h2
    have hk : k < 2 ^ m := by simpa [size_runMultiTapeAffineOddRoute] using h1
    rw [toList_getElem_eq_read1D _ _ h1,
      read1D_runMultiTapeAffineOddRoute_index_eq m w b hw _ k hk]
    simp only [oddRouteL, List.getElem_map, List.getElem_range]
    have hlt : (w * k + b) % 2 ^ m < v.size := by
      rw [hv]
      exact Nat.mod_lt _ (Nat.two_pow_pos m)
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    unfold read1D
    rw [dif_pos hlt]
    simp

end Generic

/-! ## P1: the value `w9XRows` of `preNodeV` -/

theorem w9XRows_eq (t1 r : ℕ) (x : Array (ℤ × ℤ)) :
    w9XRows t1 r x = Array.ofFn (fun i : Fin t1 => Array.ofFn (fun j : Fin r =>
      read1D (runMultiTapeTranspose (natLog2Fuel t1 t1) r (read1D x)) (i * r + j))) :=
  scan2D_eq_ofFn t1 r _

theorem w9XRows_size (t1 r : ℕ) (x : Array (ℤ × ℤ)) : (w9XRows t1 r x).size = t1 := by
  rw [w9XRows_eq, Array.size_ofFn]

theorem w9XRows_rows (t1 r : ℕ) (x : Array (ℤ × ℤ)) :
    ∀ row ∈ (w9XRows t1 r x).toList, row.size = r := by
  intro row hrow
  rw [w9XRows_eq, Array.toList_ofFn, List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  exact Array.size_ofFn

/-- **P1 bridge.** Flattened row-major, `xRows` is W4's `transposeL r t1` of the node. -/
theorem w9XRows_flat (t1 r : ℕ) (x : Array (ℤ × ℤ)) (ht1 : t1 = 2 ^ natLog2Fuel t1 t1)
    (hr : 0 < r) (hx : x.size = t1 * r) :
    (w9XRows t1 r x).toList.flatMap Array.toList = transposeL r t1 x.toList := by
  rw [w9XRows_eq, flat_ofFn_rows _ t1 r (by rw [size_runMultiTapeTranspose, ← ht1])]
  have h := runMultiTapeTranspose_toList (natLog2Fuel t1 t1) r hr x
    (by rw [hx, ← ht1, Nat.mul_comm])
  rw [h, ← ht1]

/-- **P1 bridge, symbol level**: the workspace matrix of `xRows` is the W4 transpose of the node's
entry records. -/
theorem matSyms_w9XRows (t1 r : ℕ) (x : Array (ℤ × ℤ)) (ht1 : t1 = 2 ^ natLog2Fuel t1 t1)
    (hr : 0 < r) (hx : x.size = t1 * r) :
    matSyms (w9XRows t1 r x) = blk .down (transposeL r t1 (x.toList.map entrySyms)) := by
  unfold matSyms blkE
  rw [w9XRows_flat t1 r x ht1 hr hx,
    transposeL_map _ _ _ _ (by rw [Array.length_toList, hx, Nat.mul_comm])]

#assert_std_axioms transpose_idx_lt transposeL_map toList_getElem_eq_read1D
  size_runMultiTapeTranspose size_runMultiTapeAffineOddRoute scan_outTape_eq_ofFn scan2D_eq_ofFn
  flat_ofFn_rows runMultiTapeTranspose_toList runMultiTapeAffineOddRoute_toList w9XRows_eq
  w9XRows_size w9XRows_rows w9XRows_flat matSyms_w9XRows

end WP.W9b
