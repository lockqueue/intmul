/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Arith

/-!
# K5-SOLVE-b (`Bridge/SolveSplitDefs.lean`): masked split/merge and backward reindex of the
natural-order solver — list functions and contracts

Part 2 of the 3-way split of `SolveAxisStmt` (`Contracts/Bridge.lean`; Lemma 4.6 (`lem:bridge-C`)(iv)
and Section 4.6 (`sec:bridge-D`), splitting forward and backward columns into separate streams so the
backward row-block reindex leaves the forward columns untouched). The deconvolution stage on axis `i` sees the array in
natural frequency order as `L = A_i` rows of `2M = R/A_i` one-coefficient records (row-major, row
`0` on top). Row `j`'s first `M` records are the forward columns (`2u < t_i`) and its last `M`
records the backward columns.

**List functions** (namespace `SubNLogN.Machine.SolveSplit`):
* `fwdHalf M v`, `bwdHalf M v`: the `L × M` forward / backward halves (row-major), and
  `mergeHalves M F B`, their inverse (`mergeHalves_fwdHalf_bwdHalf`, `fwdHalf_mergeHalves`,
  `bwdHalf_mergeHalves`).
* `reindexI M u = reverseRows (rotateLeft 2 rows)` and `reindexJ M u = reverseRows (rotateLeft 1
  rows)` on an array of rows of length `M`: new row `i` is old row `(L + 1 - i) % L`, resp.
  `(L - i) % L` (`getElem?_reindexI`, `getElem?_reindexJ`).
All of them commute with `List.map` (so they act on records of any payload) and preserve or halve
lengths as stated (`length_*`).

**Contracts** (namespace `SubNLogN.Machine`), each a `KContract (Fin n) Unit` (one program for all
runtime data, payload agnostic, scratch clean at entry, all unmentioned stacks restored):
`SolveHalfSplitStmt`, `SolveHalfMergeStmt`, `SolveReindexIStmt`, `SolveReindexJStmt`.
The counter `M` is `natSyms M` on a parameter stack (restored); cost
`C·(cvol + #records·(bitLen M + 1) + 1)`.
-/

namespace SubNLogN.Machine

namespace SolveSplit

variable {α β : Type}

/-! ## Halves of rows of length `2M` -/

/-- Forward halves of the first `n` rows (row length `2M`): the first `M` entries of each row. -/
def fwdRows (M : ℕ) : ℕ → List α → List α
  | 0, _ => []
  | n + 1, v => v.take M ++ fwdRows M n (v.drop (2 * M))

/-- Backward halves of the first `n` rows (row length `2M`): the last `M` entries of each row. -/
def bwdRows (M : ℕ) : ℕ → List α → List α
  | 0, _ => []
  | n + 1, v => (v.drop M).take M ++ bwdRows M n (v.drop (2 * M))

/-- The forward half (row-major `L × M`) of `L = |v|/(2M)` rows of length `2M`. -/
def fwdHalf (M : ℕ) (v : List α) : List α := fwdRows M (v.length / (2 * M)) v

/-- The backward half (row-major `L × M`) of `L = |v|/(2M)` rows of length `2M`. -/
def bwdHalf (M : ℕ) (v : List α) : List α := bwdRows M (v.length / (2 * M)) v

/-- Interleave `n` half-rows: row `j` is `F`'s `j`-th block of `M` followed by `B`'s. -/
def mergeRowsH (M : ℕ) : ℕ → List α → List α → List α
  | 0, _, _ => []
  | n + 1, F, B => F.take M ++ (B.take M ++ mergeRowsH M n (F.drop M) (B.drop M))

/-- The inverse of the half split: `L = |F|/M` rows, each `F`'s block followed by `B`'s block. -/
def mergeHalves (M : ℕ) (F B : List α) : List α := mergeRowsH M (F.length / M) F B

/-! ## Rows of length `M` and the backward reindex maps -/

/-- The first `n` rows of length `M`. -/
def rowsOf (M : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | n + 1, u => u.take M :: rowsOf M n (u.drop M)

/-- `reverseRows ∘ rotateLeft a` on the `|u|/M` rows of length `M`. -/
def reindexRot (a M : ℕ) (u : List α) : List α :=
  (((rowsOf M (u.length / M) u).rotate a).reverse).flatten

/-- Input reindex of the backward system (Lemma 4.6 (`lem:bridge-C`)(iv), `I = reverseRows ∘ rotateLeft 2`):
new row `i` is old row `(L + 1 - i) % L`, i.e. `Y_{1-i mod L}`. -/
def reindexI (M : ℕ) (u : List α) : List α := reindexRot 2 M u

/-- Output readout of the backward system (`J = reverseRows ∘ rotateLeft 1`): new row `j` is old
row `(L - j) % L`, i.e. `Z_{-j mod L}`. -/
def reindexJ (M : ℕ) (u : List α) : List α := reindexRot 1 M u

/-! ## `map` -/

theorem fwdRows_map (f : α → β) (M : ℕ) : ∀ (n : ℕ) (v : List α),
    fwdRows M n (v.map f) = (fwdRows M n v).map f
  | 0, _ => rfl
  | n + 1, v => by
    simp only [fwdRows, List.map_append, ← List.map_drop, ← List.map_take, fwdRows_map f M n]

theorem bwdRows_map (f : α → β) (M : ℕ) : ∀ (n : ℕ) (v : List α),
    bwdRows M n (v.map f) = (bwdRows M n v).map f
  | 0, _ => rfl
  | n + 1, v => by
    simp only [bwdRows, List.map_append, ← List.map_drop, ← List.map_take, bwdRows_map f M n]

theorem mergeRowsH_map (f : α → β) (M : ℕ) : ∀ (n : ℕ) (F B : List α),
    mergeRowsH M n (F.map f) (B.map f) = (mergeRowsH M n F B).map f
  | 0, _, _ => rfl
  | n + 1, F, B => by
    simp only [mergeRowsH, List.map_append, ← List.map_drop, ← List.map_take,
      mergeRowsH_map f M n]

theorem rowsOf_map (f : α → β) (M : ℕ) : ∀ (n : ℕ) (u : List α),
    rowsOf M n (u.map f) = (rowsOf M n u).map (List.map f)
  | 0, _ => rfl
  | n + 1, u => by
    simp only [rowsOf, List.map_cons, ← List.map_drop, ← List.map_take, rowsOf_map f M n]

theorem fwdHalf_map (f : α → β) (M : ℕ) (v : List α) :
    fwdHalf M (v.map f) = (fwdHalf M v).map f := by
  simp only [fwdHalf, List.length_map, fwdRows_map]

theorem bwdHalf_map (f : α → β) (M : ℕ) (v : List α) :
    bwdHalf M (v.map f) = (bwdHalf M v).map f := by
  simp only [bwdHalf, List.length_map, bwdRows_map]

theorem mergeHalves_map (f : α → β) (M : ℕ) (F B : List α) :
    mergeHalves M (F.map f) (B.map f) = (mergeHalves M F B).map f := by
  simp only [mergeHalves, List.length_map, mergeRowsH_map]

theorem reindexRot_map (f : α → β) (a M : ℕ) (u : List α) :
    reindexRot a M (u.map f) = (reindexRot a M u).map f := by
  simp only [reindexRot, List.length_map, rowsOf_map, List.map_flatten, List.map_reverse,
    List.map_rotate]

theorem reindexI_map (f : α → β) (M : ℕ) (u : List α) :
    reindexI M (u.map f) = (reindexI M u).map f := reindexRot_map f 2 M u

theorem reindexJ_map (f : α → β) (M : ℕ) (u : List α) :
    reindexJ M (u.map f) = (reindexJ M u).map f := reindexRot_map f 1 M u


/-! ## Lengths -/

theorem length_fwdRows (M : ℕ) : ∀ (n : ℕ) (v : List α), n * (2 * M) ≤ v.length →
    (fwdRows M n v).length = n * M
  | 0, _, _ => by simp [fwdRows]
  | n + 1, v, hv => by
    have e : (n + 1) * (2 * M) = n * (2 * M) + 2 * M := by ring
    have h2 : n * (2 * M) ≤ (v.drop (2 * M)).length := by rw [List.length_drop]; omega
    simp only [fwdRows, List.length_append, List.length_take, length_fwdRows M n _ h2]
    rw [Nat.min_eq_left (by omega)]
    ring

theorem length_bwdRows (M : ℕ) : ∀ (n : ℕ) (v : List α), n * (2 * M) ≤ v.length →
    (bwdRows M n v).length = n * M
  | 0, _, _ => by simp [bwdRows]
  | n + 1, v, hv => by
    have e : (n + 1) * (2 * M) = n * (2 * M) + 2 * M := by ring
    have h2 : n * (2 * M) ≤ (v.drop (2 * M)).length := by rw [List.length_drop]; omega
    simp only [bwdRows, List.length_append, List.length_take, List.length_drop,
      length_bwdRows M n _ h2]
    rw [Nat.min_eq_left (by omega)]
    ring

theorem length_mergeRowsH (M : ℕ) : ∀ (n : ℕ) (F B : List α), n * M ≤ F.length →
    n * M ≤ B.length → (mergeRowsH M n F B).length = n * (2 * M)
  | 0, _, _, _, _ => by simp [mergeRowsH]
  | n + 1, F, B, hF, hB => by
    have e : (n + 1) * M = n * M + M := by ring
    have hF' : n * M ≤ (F.drop M).length := by rw [List.length_drop]; omega
    have hB' : n * M ≤ (B.drop M).length := by rw [List.length_drop]; omega
    simp only [mergeRowsH, List.length_append, List.length_take,
      length_mergeRowsH M n _ _ hF' hB']
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    ring

theorem fwdHalf_eq {M L : ℕ} (hM : 0 < M) {v : List α} (hv : v.length = L * (2 * M)) :
    fwdHalf M v = fwdRows M L v := by
  rw [fwdHalf, hv, Nat.mul_div_cancel L (by omega)]

theorem bwdHalf_eq {M L : ℕ} (hM : 0 < M) {v : List α} (hv : v.length = L * (2 * M)) :
    bwdHalf M v = bwdRows M L v := by
  rw [bwdHalf, hv, Nat.mul_div_cancel L (by omega)]

theorem mergeHalves_eq {M L : ℕ} (hM : 0 < M) {F B : List α} (hF : F.length = L * M) :
    mergeHalves M F B = mergeRowsH M L F B := by
  rw [mergeHalves, hF, Nat.mul_div_cancel L hM]

theorem length_fwdHalf {M L : ℕ} (hM : 0 < M) {v : List α} (hv : v.length = L * (2 * M)) :
    (fwdHalf M v).length = L * M := by
  rw [fwdHalf_eq hM hv, length_fwdRows M L v (le_of_eq hv.symm)]

theorem length_bwdHalf {M L : ℕ} (hM : 0 < M) {v : List α} (hv : v.length = L * (2 * M)) :
    (bwdHalf M v).length = L * M := by
  rw [bwdHalf_eq hM hv, length_bwdRows M L v (le_of_eq hv.symm)]

theorem length_mergeHalves {M L : ℕ} (hM : 0 < M) {F B : List α} (hF : F.length = L * M)
    (hB : B.length = L * M) : (mergeHalves M F B).length = L * (2 * M) := by
  rw [mergeHalves_eq hM hF, length_mergeRowsH M L F B (le_of_eq hF.symm) (le_of_eq hB.symm)]

/-! ## The split and the merge are inverse -/

theorem mergeRowsH_fwdRows_bwdRows (M : ℕ) : ∀ (n : ℕ) (v : List α), v.length = n * (2 * M) →
    mergeRowsH M n (fwdRows M n v) (bwdRows M n v) = v
  | 0, v, hv => by simp only [mergeRowsH]; exact (List.eq_nil_of_length_eq_zero (by simpa using hv)).symm
  | n + 1, v, hv => by
    have e : (n + 1) * (2 * M) = n * (2 * M) + 2 * M := by ring
    have h2 : (v.drop (2 * M)).length = n * (2 * M) := by rw [List.length_drop]; omega
    have hA : (v.take M).length = M := by rw [List.length_take]; omega
    have hB0 : ((v.drop M).take M).length = M := by
      rw [List.length_take, List.length_drop]; omega
    simp only [fwdRows, bwdRows, mergeRowsH, List.take_left' hA, List.drop_left' hA,
      List.take_left' hB0, List.drop_left' hB0, mergeRowsH_fwdRows_bwdRows M n _ h2]
    have hdd : v.drop (2 * M) = (v.drop M).drop M := by rw [List.drop_drop]; congr 1; omega
    rw [hdd, List.take_append_drop, List.take_append_drop]

theorem fwdRows_mergeRowsH (M : ℕ) : ∀ (n : ℕ) (F B : List α), F.length = n * M →
    B.length = n * M → fwdRows M n (mergeRowsH M n F B) = F
  | 0, F, _, hF, _ => by simp only [fwdRows]; exact (List.eq_nil_of_length_eq_zero (by simpa using hF)).symm
  | n + 1, F, B, hF, hB => by
    have e : (n + 1) * M = n * M + M := by ring
    have hA : (F.take M).length = M := by rw [List.length_take]; omega
    have hB0 : (B.take M).length = M := by rw [List.length_take]; omega
    have hAB : (F.take M ++ B.take M).length = 2 * M := by
      rw [List.length_append, hA, hB0]; ring
    have hF' : (F.drop M).length = n * M := by rw [List.length_drop]; omega
    have hB' : (B.drop M).length = n * M := by rw [List.length_drop]; omega
    simp only [fwdRows, mergeRowsH]
    rw [List.take_left' hA, ← List.append_assoc, List.drop_left' hAB,
      fwdRows_mergeRowsH M n _ _ hF' hB', List.take_append_drop]

theorem bwdRows_mergeRowsH (M : ℕ) : ∀ (n : ℕ) (F B : List α), F.length = n * M →
    B.length = n * M → bwdRows M n (mergeRowsH M n F B) = B
  | 0, _, B, _, hB => by simp only [bwdRows]; exact (List.eq_nil_of_length_eq_zero (by simpa using hB)).symm
  | n + 1, F, B, hF, hB => by
    have e : (n + 1) * M = n * M + M := by ring
    have hA : (F.take M).length = M := by rw [List.length_take]; omega
    have hB0 : (B.take M).length = M := by rw [List.length_take]; omega
    have hAB : (F.take M ++ B.take M).length = 2 * M := by
      rw [List.length_append, hA, hB0]; ring
    have hF' : (F.drop M).length = n * M := by rw [List.length_drop]; omega
    have hB' : (B.drop M).length = n * M := by rw [List.length_drop]; omega
    simp only [bwdRows, mergeRowsH]
    rw [List.drop_left' hA, List.take_left' hB0, ← List.append_assoc, List.drop_left' hAB,
      bwdRows_mergeRowsH M n _ _ hF' hB', List.take_append_drop]

theorem mergeHalves_fwdHalf_bwdHalf {M L : ℕ} (hM : 0 < M) {v : List α}
    (hv : v.length = L * (2 * M)) : mergeHalves M (fwdHalf M v) (bwdHalf M v) = v := by
  rw [mergeHalves_eq hM (length_fwdHalf hM hv), fwdHalf_eq hM hv, bwdHalf_eq hM hv,
    mergeRowsH_fwdRows_bwdRows M L v hv]

theorem fwdHalf_mergeHalves {M L : ℕ} (hM : 0 < M) {F B : List α} (hF : F.length = L * M)
    (hB : B.length = L * M) : fwdHalf M (mergeHalves M F B) = F := by
  rw [fwdHalf_eq hM (length_mergeHalves hM hF hB), mergeHalves_eq hM hF,
    fwdRows_mergeRowsH M L F B hF hB]

theorem bwdHalf_mergeHalves {M L : ℕ} (hM : 0 < M) {F B : List α} (hF : F.length = L * M)
    (hB : B.length = L * M) : bwdHalf M (mergeHalves M F B) = B := by
  rw [bwdHalf_eq hM (length_mergeHalves hM hF hB), mergeHalves_eq hM hF,
    bwdRows_mergeRowsH M L F B hF hB]

/-! ## Index formulas for the halves -/

theorem getElem?_fwdRows (M : ℕ) : ∀ (n : ℕ) (v : List α) (x : ℕ), n * (2 * M) ≤ v.length →
    x < n * M → (fwdRows M n v)[x]? = v[x / M * (2 * M) + x % M]?
  | 0, _, x, _, hx => by simp at hx
  | n + 1, v, x, hv, hx => by
    have e : (n + 1) * (2 * M) = n * (2 * M) + 2 * M := by ring
    have e' : (n + 1) * M = n * M + M := by ring
    have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h; simp at hx
      · exact h
    have hA : (v.take M).length = M := by rw [List.length_take]; omega
    simp only [fwdRows]
    by_cases hxM : x < M
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hxM,
        Nat.div_eq_of_lt hxM, Nat.mod_eq_of_lt hxM]
      simp
    · have h2 : n * (2 * M) ≤ (v.drop (2 * M)).length := by rw [List.length_drop]; omega
      have hxle : (v.take M).length ≤ x := by rw [hA]; omega
      have hxlt : x - M < n * M := by omega
      rw [List.getElem?_append_right hxle, hA, getElem?_fwdRows M n _ (x - M) h2 hxlt,
        List.getElem?_drop]
      have hq : x / M = (x - M) / M + 1 := Nat.div_eq_sub_div hM (by omega)
      have hr : x % M = (x - M) % M := Nat.mod_eq_sub_mod (by omega)
      rw [hq, hr]
      congr 1
      ring

theorem getElem?_bwdRows (M : ℕ) : ∀ (n : ℕ) (v : List α) (x : ℕ), n * (2 * M) ≤ v.length →
    x < n * M → (bwdRows M n v)[x]? = v[x / M * (2 * M) + M + x % M]?
  | 0, _, x, _, hx => by simp at hx
  | n + 1, v, x, hv, hx => by
    have e : (n + 1) * (2 * M) = n * (2 * M) + 2 * M := by ring
    have e' : (n + 1) * M = n * M + M := by ring
    have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h; simp at hx
      · exact h
    have hA : ((v.drop M).take M).length = M := by
      rw [List.length_take, List.length_drop]; omega
    simp only [bwdRows]
    by_cases hxM : x < M
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hxM,
        List.getElem?_drop, Nat.div_eq_of_lt hxM, Nat.mod_eq_of_lt hxM]
      simp
    · have h2 : n * (2 * M) ≤ (v.drop (2 * M)).length := by rw [List.length_drop]; omega
      have hxle : ((v.drop M).take M).length ≤ x := by rw [hA]; omega
      have hxlt : x - M < n * M := by omega
      rw [List.getElem?_append_right hxle, hA, getElem?_bwdRows M n _ (x - M) h2 hxlt,
        List.getElem?_drop]
      have hq : x / M = (x - M) / M + 1 := Nat.div_eq_sub_div hM (by omega)
      have hr : x % M = (x - M) % M := Nat.mod_eq_sub_mod (by omega)
      rw [hq, hr]
      congr 1
      ring

/-- Entry `x` of the forward half is entry `⌊x/M⌋·2M + x mod M` of `v`. -/
theorem getElem?_fwdHalf {M L : ℕ} (hM : 0 < M) {v : List α} (hv : v.length = L * (2 * M))
    {x : ℕ} (hx : x < L * M) : (fwdHalf M v)[x]? = v[x / M * (2 * M) + x % M]? := by
  rw [fwdHalf_eq hM hv]
  exact getElem?_fwdRows M L v x (le_of_eq hv.symm) hx

/-- Entry `x` of the backward half is entry `⌊x/M⌋·2M + M + x mod M` of `v`. -/
theorem getElem?_bwdHalf {M L : ℕ} (hM : 0 < M) {v : List α} (hv : v.length = L * (2 * M))
    {x : ℕ} (hx : x < L * M) : (bwdHalf M v)[x]? = v[x / M * (2 * M) + M + x % M]? := by
  rw [bwdHalf_eq hM hv]
  exact getElem?_bwdRows M L v x (le_of_eq hv.symm) hx

/-! ## Rows of length `M` -/

theorem length_rowsOf (M : ℕ) : ∀ (n : ℕ) (u : List α), (rowsOf M n u).length = n
  | 0, _ => rfl
  | n + 1, u => by simp [rowsOf, length_rowsOf M n]

theorem getElem?_rowsOf (M : ℕ) : ∀ (n : ℕ) (u : List α) (k : ℕ), k < n →
    (rowsOf M n u)[k]? = some ((u.drop (k * M)).take M)
  | 0, _, k, hk => by simp at hk
  | n + 1, u, 0, _ => by simp [rowsOf]
  | n + 1, u, k + 1, hk => by
    simp only [rowsOf, List.getElem?_cons_succ]
    rw [getElem?_rowsOf M n _ k (by omega), List.drop_drop]
    congr 3
    ring

theorem length_mem_rowsOf (M : ℕ) : ∀ (n : ℕ) (u : List α), n * M ≤ u.length →
    ∀ r ∈ rowsOf M n u, r.length = M
  | 0, _, _, r, hr => by simp [rowsOf] at hr
  | n + 1, u, hu, r, hr => by
    have e : (n + 1) * M = n * M + M := by ring
    simp only [rowsOf, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [List.length_take]; omega
    · exact length_mem_rowsOf M n _ (by rw [List.length_drop]; omega) r hr

/-- Indexing a flattened list of rows of a common length `M`. -/
theorem getElem?_flatten_rows {M : ℕ} : ∀ (rs : List (List α)) (i c : ℕ),
    (∀ r ∈ rs, r.length = M) → c < M → rs.flatten[i * M + c]? = rs[i]?.bind (·[c]?)
  | [], i, c, _, _ => by simp
  | r :: rs, 0, c, h, hc => by
    have hr : r.length = M := h r (by simp)
    simp only [List.flatten_cons, Nat.zero_mul, Nat.zero_add, List.getElem?_cons_zero,
      Option.bind_some]
    rw [List.getElem?_append_left (by omega)]
  | r :: rs, i + 1, c, h, hc => by
    have hr : r.length = M := h r (by simp)
    simp only [List.flatten_cons, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [hr]; nlinarith), hr]
    have e : (i + 1) * M + c - M = i * M + c := by
      rw [Nat.add_mul, one_mul]; omega
    rw [e]
    exact getElem?_flatten_rows rs i c (fun r' hr' => h r' (by simp [hr'])) hc

theorem length_flatten_rows {M : ℕ} : ∀ (rs : List (List α)), (∀ r ∈ rs, r.length = M) →
    rs.flatten.length = rs.length * M
  | [], _ => by simp
  | r :: rs, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      length_flatten_rows rs (fun r' hr' => h r' (by simp [hr'])), h r (by simp)]
    ring

/-! ## The backward reindex maps -/

theorem rowsOf_eq {M L : ℕ} (hM : 0 < M) {u : List α} (hu : u.length = L * M) :
    rowsOf M (u.length / M) u = rowsOf M L u := by
  rw [hu, Nat.mul_div_cancel L hM]

theorem length_reindexRot (a : ℕ) {M L : ℕ} (hM : 0 < M) {u : List α} (hu : u.length = L * M) :
    (reindexRot a M u).length = L * M := by
  have hrows := length_mem_rowsOf M L u (le_of_eq hu.symm)
  rw [reindexRot, rowsOf_eq hM hu, length_flatten_rows (M := M)]
  · simp [length_rowsOf]
  · intro r hr
    rw [List.mem_reverse, List.mem_rotate] at hr
    exact hrows r hr

/-- Row `i` of `reindexRot a M u` is row `(L - 1 - i + a) % L` of `u`. -/
theorem getElem?_reindexRot (a : ℕ) {M L : ℕ} (hM : 0 < M) {u : List α} (hu : u.length = L * M)
    {i c : ℕ} (hi : i < L) (hc : c < M) :
    (reindexRot a M u)[i * M + c]? = u[(L - 1 - i + a) % L * M + c]? := by
  have hrows := length_mem_rowsOf M L u (le_of_eq hu.symm)
  have hL : 0 < L := by omega
  have hlen : (rowsOf M L u).length = L := length_rowsOf M L u
  rw [reindexRot, rowsOf_eq hM hu, getElem?_flatten_rows (M := M) _ i c ?_ hc]
  · rw [List.getElem?_reverse (by simp [hlen]; omega), List.length_rotate, hlen,
      List.getElem?_rotate (by rw [hlen]; omega), hlen,
      getElem?_rowsOf M L u _ (Nat.mod_lt _ hL), Option.bind_some,
      List.getElem?_take_of_lt hc, List.getElem?_drop]
  · intro r hr
    rw [List.mem_reverse, List.mem_rotate] at hr
    exact hrows r hr

theorem length_reindexI {M L : ℕ} (hM : 0 < M) {u : List α} (hu : u.length = L * M) :
    (reindexI M u).length = L * M := length_reindexRot 2 hM hu

theorem length_reindexJ {M L : ℕ} (hM : 0 < M) {u : List α} (hu : u.length = L * M) :
    (reindexJ M u).length = L * M := length_reindexRot 1 hM hu

/-- **Input reindex** (`Y_{1-i mod L}`): row `i` of `reindexI M u` is row `(L + 1 - i) % L` of
`u`. -/
theorem getElem?_reindexI {M L : ℕ} (hM : 0 < M) {u : List α} (hu : u.length = L * M)
    {i c : ℕ} (hi : i < L) (hc : c < M) :
    (reindexI M u)[i * M + c]? = u[(L + 1 - i) % L * M + c]? := by
  rw [reindexI, getElem?_reindexRot 2 hM hu hi hc, show L - 1 - i + 2 = L + 1 - i by omega]

/-- **Output readout** (`Z_{-j mod L}`): row `j` of `reindexJ M u` is row `(L - j) % L` of `u`. -/
theorem getElem?_reindexJ {M L : ℕ} (hM : 0 < M) {u : List α} (hu : u.length = L * M)
    {j c : ℕ} (hj : j < L) (hc : c < M) :
    (reindexJ M u)[j * M + c]? = u[(L - j) % L * M + c]? := by
  rw [reindexJ, getElem?_reindexRot 1 hM hu hj hc, show L - 1 - j + 1 = L - j by omega]

end SolveSplit

open TMFw TMFw.Contracts

/-! ## Contracts -/

/-- **[CONTRACT] K5-SOLVE-b, half split** (Section 4.6 (`sec:bridge-D`)). Named stacks
(`Fin 4`): `0` the source (consumed), `1` / `2` the forward / backward destinations, `3` the counter
`natSyms M` (restored). The source holds `L` rows of `2M` records (row-major, row `0` on top). The
forward destination receives the first `M` records of every row (`fwdHalf`), the backward one the last
`M` (`bwdHalf`), each row-major on top of its old content. Payload agnostic (any width `wd`).
Cost `C·(cvol wd v + |v|·(bitLen M + 1) + 1)`. -/
def SolveHalfSplitStmt : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (wd L M : ℕ) (v : List (List CInt)) (rest rM : List Sym) (S : KLoc (Fin 4) E → List Sym),
      KClean S → 1 ≤ M → v.length = L * (2 * M) → BlkTerm rest → TermOK rM →
      S (.inl 0) = carrSyms wd v ++ rest → S (.inl 3) = natSyms M ++ rM →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) rest)
          (.inl 1) (carrSyms wd (SolveSplit.fwdHalf M v) ++ S (.inl 1)))
          (.inl 2) (carrSyms wd (SolveSplit.bwdHalf M v) ++ S (.inl 2)))
        (fun _ => True) (C * (cvol wd v + v.length * (bitLen M + 1) + 1))

/-- **[CONTRACT] K5-SOLVE-b, half merge** (Section 4.6 (`sec:bridge-D`)). Named stacks (`Fin 4`): `0` the
destination, `1` / `2` the forward / backward halves (consumed), `3` the counter `natSyms M`
(restored). Each half holds `L` rows of `M` records; the destination receives, on top of its old
content, the `L` rows of `2M` records `mergeHalves M F B` (row `j` = forward row `j` followed by
backward row `j`). Payload agnostic. Cost `C·(cvol F + cvol B + (|F| + |B|)·(bitLen M + 1) + 1)`. -/
def SolveHalfMergeStmt : Prop :=
  KContract (Fin 4) Unit fun _ E _ _ _ C P =>
    ∀ (wd L M : ℕ) (F B : List (List CInt)) (rF rB rM : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      KClean S → 1 ≤ M → F.length = L * M → B.length = L * M → BlkTerm rF → BlkTerm rB →
      TermOK rM →
      S (.inl 1) = carrSyms wd F ++ rF → S (.inl 2) = carrSyms wd B ++ rB →
      S (.inl 3) = natSyms M ++ rM →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 1) rF) (.inl 2) rB)
          (.inl 0) (carrSyms wd (SolveSplit.mergeHalves M F B) ++ S (.inl 0)))
        (fun _ => True)
        (C * (cvol wd F + cvol wd B + (F.length + B.length) * (bitLen M + 1) + 1))

/-- **[CONTRACT] K5-SOLVE-b, backward input reindex** (Lemma 4.6 (`lem:bridge-C`)(iv), `I = reverseRows ∘
rotateLeft 2`; Section 4.6 (`sec:bridge-D`)). Named stacks (`Fin 2`): `0` an array of `L` rows of `M` records, in
place; `1` the counter `natSyms M` (restored). New row `i` is old row `(L + 1 - i) % L`
(`SolveSplit.getElem?_reindexI`). Payload agnostic; `L ≥ 2` (as for every solver axis, `L = A_i ≥ t_0`).
Cost `C·(cvol u + |u|·(bitLen M + 1) + 1)`. -/
def SolveReindexIStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C P =>
    ∀ (wd L M : ℕ) (u : List (List CInt)) (rest rM : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ M → 2 ≤ L → u.length = L * M → BlkTerm rest → TermOK rM →
      S (.inl 0) = carrSyms wd u ++ rest → S (.inl 1) = natSyms M ++ rM →
      Runs P S (Function.update S (.inl 0) (carrSyms wd (SolveSplit.reindexI M u) ++ rest))
        (fun _ => True) (C * (cvol wd u + u.length * (bitLen M + 1) + 1))

/-- **[CONTRACT] K5-SOLVE-b, backward output readout** (Lemma 4.6 (`lem:bridge-C`)(iv), `J = reverseRows ∘
rotateLeft 1`). Named stacks (`Fin 2`): `0` an array of `L` rows of `M` records, in place; `1` the
counter `natSyms M` (restored). New row `j` is old row `(L - j) % L`
(`SolveSplit.getElem?_reindexJ`). Payload agnostic; `L ≥ 2`. Cost `C·(cvol u + |u|·(bitLen M + 1) + 1)`. -/
def SolveReindexJStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C P =>
    ∀ (wd L M : ℕ) (u : List (List CInt)) (rest rM : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ M → 2 ≤ L → u.length = L * M → BlkTerm rest → TermOK rM →
      S (.inl 0) = carrSyms wd u ++ rest → S (.inl 1) = natSyms M ++ rM →
      Runs P S (Function.update S (.inl 0) (carrSyms wd (SolveSplit.reindexJ M u) ++ rest))
        (fun _ => True) (C * (cvol wd u + u.length * (bitLen M + 1) + 1))

end SubNLogN.Machine
