import Contracts.W9.Post

/-!
# WP.W9e.Bridge — W4's routing specs against the snapshot's routing in `postNodeV`

The POST phases Q2, Q3 and Q6 (`Contracts.W9.Post`) are stated with the snapshot's routing
functions (`runMultiTapeTranspose`, `runMultiTapeAffineOddRoute`, `runScan2DWithSteps`,
`runSequentialScanSteps`), as used by `IntMul.LevelSync.postNodeV`. The machine uses W4's kernels,
whose specs are the pure list functions `transposeL` and `oddRouteL`. This module proves the index
bridges (contract doc O11), all from the snapshot's index identities:

| bridge | statement | snapshot lemma |
|---|---|---|
| `w9QHatT_toList` | Q2: `w9QHatT t1 r qHat = transposeL t1 r (flat qHat)` | `read1D_runMultiTapeTranspose_flatten2D_eq` (ST:844) |
| `w9ColRoutes_getD` | Q3: column `u2` of `w9ColRoutes` is `oddRouteL m_t1 w 0 (colOf …)` with W4's `w` | `read1D_runMultiTapeAffineOddRoute_index_eq` (ST:974), `computableOddStrideFactor_bridge` |
| `w9Y_getD` | Q4: row `u2` of `w9Y` is the rescaled routed column | `runScan2DWithSteps` unfolded |
| `w9Out_toList` | Q6: `w9Out = map (gRescale pSub p) (transposeL r t1 (flat Zc))` | `read1D_runMultiTapeTranspose_flatten2D_eq` |

Plus the list facts the machine proofs use: `transposeL_map`, `oddRouteL_map` (W4 kernels move
records, i.e. `entrySyms` images), membership (for width bounds) and flattening.
-/

namespace WP.W9e

open IntMul IntMul.LevelSync TMFw TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-! ## List helpers -/

theorem getD_eq_get {α : Type} (l : List α) (d : α) {n : ℕ} (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) (d : β) (d' : α) {n : ℕ}
    (h : n < l.length) : (l.map f).getD n d = f (l.getD n d') := by
  rw [getD_eq_get _ _ (by simpa using h), getD_eq_get _ _ h, List.getElem_map]

theorem getD_irrel {α : Type} (l : List α) (d d' : α) {n : ℕ} (h : n < l.length) :
    l.getD n d = l.getD n d' := by
  rw [getD_eq_get _ _ h, getD_eq_get _ _ h]

theorem mem_of_getD {α : Type} (l : List α) (d : α) {n : ℕ} (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [getD_eq_get _ _ h]
  exact List.getElem_mem h

theorem read1D_eq_get {α : Type} [Zero α] (a : Array α) {i : ℕ} (h : i < a.size) :
    read1D a i = a[i] := by
  unfold read1D
  rw [dif_pos h]

theorem read1D_eq_getD {α : Type} [Zero α] (a : Array α) (d : α) {i : ℕ} (h : i < a.size) :
    read1D a i = a.toList.getD i d := by
  rw [read1D_eq_get a h, getD_eq_get _ _ (by simpa using h), Array.getElem_toList]

theorem read2D_eq_get {α : Type} [Zero α] (M : Array (Array α)) {i j : ℕ} (hi : i < M.size)
    (hj : j < M[i].size) : read2D M i j = M[i][j] := by
  unfold read2D
  rw [dif_pos hi]
  dsimp only
  rw [dif_pos hj]

/-- An array as the list of its `getD`s. -/
theorem toList_eq_map_getD {α : Type} (M : Array α) (d : α) :
    M.toList = (List.range M.size).map (fun i => M.getD i d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    have hi : i < M.size := by simpa using h1
    simp [Array.getD, hi]

theorem map_range_read1D {α β : Type} [Zero α] (a : Array α) (g : α → β) {n : ℕ}
    (h : a.size = n) : (List.range n).map (fun i => g (read1D a i)) = a.toList.map g := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    have hi : i < a.size := by rw [h]; simpa using h1
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, read1D_eq_get a hi]

/-! ## Flattening a matrix with uniform rows -/

theorem length_flatMap_toList {α : Type} (c : ℕ) :
    ∀ (L : List (Array α)), (∀ row ∈ L, row.size = c) →
      (L.flatMap Array.toList).length = L.length * c
  | [], _ => by simp
  | row :: L, h => by
    have hrow : row.size = c := h row (by simp)
    have ih := length_flatMap_toList c L (fun r hr => h r (by simp [hr]))
    rw [List.flatMap_cons, List.length_append, Array.length_toList, hrow, ih, List.length_cons,
      Nat.succ_mul]
    omega

theorem getD_flatMap_toList {α : Type} (c : ℕ) (d : α) :
    ∀ (L : List (Array α)), (∀ row ∈ L, row.size = c) → ∀ (i j : ℕ), i < L.length → j < c →
      (L.flatMap Array.toList).getD (i * c + j) d = ((L.getD i #[]).toList).getD j d
  | [], _, i, j, hi, _ => by simp at hi
  | row :: L, h, i, j, hi, hj => by
    have hrow : row.size = c := h row (by simp)
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by rw [Array.length_toList]; omega)]
      rfl
    | succ i =>
      have hle : row.toList.length ≤ (i + 1) * c + j := by
        rw [Array.length_toList, hrow, Nat.succ_mul]
        omega
      rw [List.getD_append_right _ _ _ _ hle, List.getD_cons_succ]
      have he : (i + 1) * c + j - row.toList.length = i * c + j := by
        rw [Array.length_toList, hrow, Nat.succ_mul]
        omega
      rw [he]
      exact getD_flatMap_toList c d L (fun r hr => h r (by simp [hr])) i j
        (by simp at hi; omega) hj

/-- Entry `(i, j)` of a matrix with rows of size `c`, read from its row-major flattening. -/
theorem flat_getD {α : Type} [Zero α] (M : Array (Array α)) (c : ℕ) (d : α)
    (hc : ∀ row ∈ M.toList, row.size = c) {i j : ℕ} (hi : i < M.size) (hj : j < c) :
    (M.toList.flatMap Array.toList).getD (i * c + j) d = read2D M i j := by
  have hi' : i < M.toList.length := by simpa using hi
  rw [getD_flatMap_toList c d M.toList hc i j hi' hj]
  have hrow : M[i].size = c := hc _ (by simp)
  rw [getD_eq_get M.toList #[] hi', Array.getElem_toList]
  rw [getD_eq_get M[i].toList d (by simp [hrow, hj]), Array.getElem_toList,
    read2D_eq_get M hi (by rw [hrow]; exact hj)]

/-! ## `transposeL` and `oddRouteL` -/

theorem transpose_idx_lt {rows cols k : ℕ} (hk : k < cols * rows) :
    (k % rows) * cols + k / rows < rows * cols := by
  have hr : 0 < rows := by
    rcases Nat.eq_zero_or_pos rows with h | h
    · subst h
      simp at hk
    · exact h
  have h1 : k / rows < cols := (Nat.div_lt_iff_lt_mul hr).2 hk
  have h2 : k % rows + 1 ≤ rows := Nat.mod_lt _ hr
  have h3 := Nat.mul_le_mul_right cols h2
  rw [Nat.add_mul, Nat.one_mul] at h3
  omega

theorem length_transposeL {α : Type} [Inhabited α] (rows cols : ℕ) (v : List α) :
    (transposeL rows cols v).length = cols * rows := by
  simp [transposeL]

theorem transposeL_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (rows cols : ℕ)
    (v : List α) (hv : v.length = rows * cols) :
    transposeL rows cols (v.map f) = (transposeL rows cols v).map f := by
  unfold transposeL
  rw [List.map_map]
  refine List.map_congr_left (fun k hk => ?_)
  rw [List.mem_range] at hk
  exact getD_map_lt f v default default (hv ▸ transpose_idx_lt hk)

theorem mem_of_mem_transposeL {α : Type} [Inhabited α] {rows cols : ℕ} {v : List α}
    (hv : v.length = rows * cols) {x : α} (hx : x ∈ transposeL rows cols v) : x ∈ v := by
  unfold transposeL at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range] at hk
  exact mem_of_getD v default (hv ▸ transpose_idx_lt hk)

theorem length_oddRouteL {α : Type} [Inhabited α] (k w b : ℕ) (v : List α) :
    (oddRouteL k w b v).length = 2 ^ k := by
  simp [oddRouteL]

theorem oddRouteL_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (k w b : ℕ)
    (v : List α) (hv : v.length = 2 ^ k) :
    oddRouteL k w b (v.map f) = (oddRouteL k w b v).map f := by
  unfold oddRouteL
  rw [List.map_map]
  refine List.map_congr_left (fun u _ => ?_)
  exact getD_map_lt f v default default (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos k))

theorem mem_of_mem_oddRouteL {α : Type} [Inhabited α] {k w b : ℕ} {v : List α}
    (hv : v.length = 2 ^ k) {x : α} (hx : x ∈ oddRouteL k w b v) : x ∈ v := by
  unfold oddRouteL at hx
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
  exact mem_of_getD v default (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos k))

/-! ## Sizes of the snapshot's routing machines -/

theorem size_runMultiTapeTranspose {α : Type} [Zero α] (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTranspose m r tape).size = 2 ^ m * r := by
  cases m with
  | zero => simp [runMultiTapeTranspose]
  | succ m =>
    simp only [runMultiTapeTranspose, size_runInterleaveRunsSteps, pow_succ]
    ring

theorem size_runMultiTapeAffineOddRoute {α : Type} [Zero α] (m w b : ℕ) (col : ℕ → α) :
    (runMultiTapeAffineOddRoute m w b col).size = 2 ^ m := by
  cases m with
  | zero => simp [runMultiTapeAffineOddRoute]
  | succ m =>
    simp only [runMultiTapeAffineOddRoute, size_runInterleaveParitySteps, pow_succ]
    ring

theorem toList_runSequentialScanSteps {α : Type} (g : ℕ → α) (n : ℕ) :
    (runSequentialScanSteps g n).outTape.toList = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runSequentialScanSteps, scanHeadStep, Array.toList_push, ih,
      runSequentialScanSteps_inHead, List.range_succ, List.map_append, List.map_cons,
      List.map_nil]

/-! ## Q2: the transpose of `qHat` -/

/-- **Q2 bridge.** The snapshot's transposed buffer `w9QHatT` (`runMultiTapeTranspose m_r t1` of
the row-major flattening, ST:844) is W4's `transposeL t1 r` of the flattened `t1 × r` matrix. -/
theorem w9QHatT_toList (t1 r : ℕ) (qHat : Array (Array (ℤ × ℤ))) (ht1 : 0 < t1)
    (hr : r = 2 ^ natLog2Fuel r r) (hsize : qHat.size = t1)
    (hrows : ∀ row ∈ qHat.toList, row.size = r) :
    (w9QHatT t1 r qHat).toList = transposeL t1 r (qHat.toList.flatMap Array.toList) := by
  apply List.ext_getElem
  · rw [Array.length_toList, length_transposeL]
    unfold w9QHatT
    rw [size_runMultiTapeTranspose, ← hr]
  · intro k hk1 hk2
    rw [length_transposeL] at hk2
    have hu2 : k / t1 < r := (Nat.div_lt_iff_lt_mul ht1).2 hk2
    have hv1 : k % t1 < t1 := Nat.mod_lt _ ht1
    have hk1' : k < (w9QHatT t1 r qHat).size := by simpa using hk1
    rw [Array.getElem_toList, ← read1D_eq_get _ hk1']
    have h1 := read1D_runMultiTapeTranspose_flatten2D_eq (natLog2Fuel r r) r t1 hr.symm ht1 qHat
      (k / t1) (k % t1) hu2 hv1
    rw [Nat.div_add_mod'] at h1
    unfold w9QHatT
    rw [h1]
    unfold transposeL
    erw [List.getElem_map, List.getElem_range,
      flat_getD qHat r default hrows (by rw [hsize]; exact hv1) hu2]

/-! ## Q3: the odd-stride column routes -/

/-- Column `u2` (`t1` consecutive entries) of a row-major `r × t1` buffer. -/
def colOf (t1 : ℕ) (L : List (ℤ × ℤ)) (u2 : ℕ) : List (ℤ × ℤ) := (L.drop (u2 * t1)).take t1

theorem length_colOf (t1 : ℕ) (L : List (ℤ × ℤ)) (r u2 : ℕ) (hL : L.length = t1 * r)
    (hu2 : u2 < r) : (colOf t1 L u2).length = t1 := by
  have h1 : (u2 + 1) * t1 ≤ r * t1 := Nat.mul_le_mul_right t1 hu2
  rw [Nat.succ_mul] at h1
  unfold colOf
  rw [List.length_take, List.length_drop, hL, Nat.mul_comm t1 r]
  omega

theorem getD_colOf (t1 : ℕ) (L : List (ℤ × ℤ)) (u2 : ℕ) (d : ℤ × ℤ) {i : ℕ} (hi : i < t1)
    (hL : u2 * t1 + i < L.length) : (colOf t1 L u2).getD i d = L.getD (u2 * t1 + i) d := by
  unfold colOf
  rw [getD_eq_get _ _ (by rw [List.length_take, List.length_drop]; omega),
    getD_eq_get _ _ hL, List.getElem_take, List.getElem_drop]

theorem mem_of_mem_colOf {t1 : ℕ} {L : List (ℤ × ℤ)} {u2 : ℕ} {x : ℤ × ℤ}
    (hx : x ∈ colOf t1 L u2) : x ∈ L :=
  List.mem_of_mem_drop (List.mem_of_mem_take hx)

/-- The odd-stride multiplier used by the snapshot is odd (via W4's restatement). -/
theorem oddStrideFactor_odd (m u2 : ℕ) : IntMul.computableOddStrideFactor m u2 % 2 = 1 := by
  rw [← computableOddStrideFactor_bridge]
  exact (computableOddStrideFactor_param m u2).1

/-- **Q3 bridge.** Column `u2` of `w9ColRoutes` (the snapshot's multi-pass affine odd-stride
router, ST:974) is W4's `oddRouteL m_t1 w 0` of the column, where `w` is W4's restated
`computableOddStrideFactor m_t1 u2` (`computableOddStrideFactor_bridge`). -/
theorem w9ColRoutes_getD (t1 r : ℕ) (qHatT : Array (ℤ × ℤ))
    (ht1 : t1 = 2 ^ natLog2Fuel t1 t1) (hsize : qHatT.size = t1 * r) {u2 : ℕ} (hu2 : u2 < r) :
    ((w9ColRoutes t1 r qHatT).getD u2 #[]).toList =
      oddRouteL (natLog2Fuel t1 t1)
        (TMFw.Contracts.computableOddStrideFactor (natLog2Fuel t1 t1) u2) 0
        (colOf t1 qHatT.toList u2) := by
  unfold w9ColRoutes
  rw [array_getD_ofFn_of_lt r _ #[] u2 hu2]
  dsimp only
  rw [computableOddStrideFactor_bridge]
  apply List.ext_getElem
  · rw [Array.length_toList, size_runMultiTapeAffineOddRoute, length_oddRouteL]
  · intro u1 h1 h2
    rw [length_oddRouteL] at h2
    have h1' : u1 < (runMultiTapeAffineOddRoute (natLog2Fuel t1 t1)
        (IntMul.computableOddStrideFactor (natLog2Fuel t1 t1) u2) 0
        (fun v1 => read1D qHatT (u2 * t1 + v1))).size := by simpa using h1
    rw [Array.getElem_toList, ← read1D_eq_get _ h1',
      read1D_runMultiTapeAffineOddRoute_index_eq _ _ _ (oddStrideFactor_odd _ u2) _ u1 h2]
    unfold oddRouteL
    erw [List.getElem_map, List.getElem_range]
    have hjt : (IntMul.computableOddStrideFactor (natLog2Fuel t1 t1) u2 * u1 + 0) %
        2 ^ natLog2Fuel t1 t1 < t1 :=
      calc _ < 2 ^ natLog2Fuel t1 t1 := Nat.mod_lt _ (Nat.two_pow_pos _)
        _ = t1 := ht1.symm
    have hlen : u2 * t1 + (IntMul.computableOddStrideFactor (natLog2Fuel t1 t1) u2 * u1 + 0) %
        2 ^ natLog2Fuel t1 t1 < qHatT.toList.length := by
      have h3 : (u2 + 1) * t1 ≤ r * t1 := Nat.mul_le_mul_right t1 hu2
      rw [Nat.succ_mul] at h3
      rw [Array.length_toList, hsize, Nat.mul_comm t1 r]
      omega
    rw [getD_colOf t1 qHatT.toList u2 default hjt hlen,
      read1D_eq_getD qHatT default (by simpa using hlen)]

/-! ## Q4: the `Y` rescale -/

theorem size_w9Y (pSub t1 r pChild : ℕ) (CR : Array (Array (ℤ × ℤ))) :
    (w9Y pSub t1 r pChild CR).size = r := by
  simp [w9Y, runScan2DWithSteps]

/-- **Q4 bridge.** Row `u2` of `w9Y` is column `u2` of the routes, rescaled `pChild → pSub`. -/
theorem w9Y_getD (pSub t1 r pChild : ℕ) (CR : Array (Array (ℤ × ℤ))) {u2 : ℕ} (hu2 : u2 < r)
    (hrow : (CR.getD u2 #[]).size = t1) :
    ((w9Y pSub t1 r pChild CR).getD u2 #[]).toList =
      (CR.getD u2 #[]).toList.map (gRescale pChild pSub) := by
  unfold w9Y runScan2DWithSteps
  dsimp only
  rw [array_getD_ofFn_of_lt r _ #[] u2 hu2]
  dsimp only
  rw [dif_pos (by simpa using hu2)]
  simp only [Array.getElem_ofFn]
  rw [toList_runSequentialScanSteps, map_range_read1D _ _ hrow]

/-- The flattening of `w9Y`, row by row. -/
theorem w9Y_flat (pSub t1 r pChild : ℕ) (CR : Array (Array (ℤ × ℤ)))
    (hrow : ∀ u2 < r, (CR.getD u2 #[]).size = t1) :
    (w9Y pSub t1 r pChild CR).toList.flatMap Array.toList =
      (List.range r).flatMap (fun u2 => (CR.getD u2 #[]).toList.map (gRescale pChild pSub)) := by
  rw [toList_eq_map_getD _ #[], size_w9Y, List.flatMap_map]
  refine List.flatMap_congr (fun u2 hu2 => ?_)
  rw [List.mem_range] at hu2
  exact w9Y_getD pSub t1 r pChild CR hu2 (hrow u2 hu2)

/-! ## Q6: the output transpose and rescale -/

/-- **Q6 bridge.** `w9Out` (transpose `m_t1` back to output order `u1·r + u2`, then the rescale
`pSub → p`) is the rescaled W4 `transposeL r t1` of the flattened `r × t1` solver output. -/
theorem w9Out_toList (p pSub t1 r : ℕ) (Zc : Array (Array (ℤ × ℤ))) (hr0 : 0 < r)
    (ht1 : t1 = 2 ^ natLog2Fuel t1 t1) (hsize : Zc.size = r)
    (hcols : ∀ col ∈ Zc.toList, col.size = t1) :
    (w9Out p pSub t1 r Zc).toList =
      (transposeL r t1 (Zc.toList.flatMap Array.toList)).map (gRescale pSub p) := by
  unfold w9Out
  dsimp only
  rw [toList_runSequentialScanSteps]
  unfold transposeL
  rw [List.map_map]
  refine List.map_congr_left (fun k hk => ?_)
  rw [List.mem_range] at hk
  have hu1 : k / r < t1 := (Nat.div_lt_iff_lt_mul hr0).2 hk
  have hu2 : k % r < r := Nat.mod_lt _ hr0
  have h1 := read1D_runMultiTapeTranspose_flatten2D_eq (natLog2Fuel t1 t1) t1 r ht1.symm hr0 Zc
    (k / r) (k % r) hu1 hu2
  rw [Nat.div_add_mod'] at h1
  simp only [Function.comp]
  rw [h1, flat_getD Zc t1 default hcols (by rw [hsize]; exact hu2) hu1]

#assert_std_axioms getD_eq_get getD_map_lt getD_irrel mem_of_getD read1D_eq_get read1D_eq_getD
  read2D_eq_get toList_eq_map_getD map_range_read1D length_flatMap_toList getD_flatMap_toList
  flat_getD transpose_idx_lt length_transposeL transposeL_map mem_of_mem_transposeL
  length_oddRouteL oddRouteL_map mem_of_mem_oddRouteL size_runMultiTapeTranspose
  size_runMultiTapeAffineOddRoute toList_runSequentialScanSteps w9QHatT_toList length_colOf
  getD_colOf mem_of_mem_colOf oddStrideFactor_odd w9ColRoutes_getD size_w9Y w9Y_getD w9Y_flat
  w9Out_toList

end WP.W9e
