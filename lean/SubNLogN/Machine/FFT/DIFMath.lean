/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Walsh
import SubNLogN.Machine.Arith.Value
import SubNLogN.Math.Walsh.DirectFFT
import SubNLogN.Machine.FFT.DIFBase

/-!
# K4-DIF, value level (`Machine/FFT/DIFMath.lean`): the blocked DIF pipeline is `lastAxisFFT`

**Scope (honest summary).** Pure definitions and proved lemmas (no `sorry`), no machine:
* list combinators `inter` (interleave), `evens`, `odds`, `tab2 n k f` (the table of rows
  `[f g 0, …, f g (k-1)]`, `g < n`), with their algebra;
* the integer pipeline the machine computes: `levelB` (one DIF level on the *blocked* array: every
  block is split into halves, half-sums `halfSumC` and half-differences `halfDiffC`, the
  differences times the stage table `stageB` by `cmulTruncC q`, then the two results interleaved
  record by record), `levelsB` (levels `0, …, s-1`), `brPass` (merge consecutive pairs by
  coefficientwise interleaving), `brIter`;
* `pipeline_correct`: for a disk-grid input `z` and a disk-grid table `θ̃` (entries `j < 2r`),
  `brIter ℓ (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)) = encCube q (lastAxisFFT q ℓ θt z)`
  (`lastAxisFFT`, `Math/Walsh/DirectFFT.lean:73`; Theorem 6.5, `thm:direct-fft`, Section 6.4);
* the shape and width facts the arithmetic contracts need (`levelsB_eq`, `fits_*`).
-/

namespace SubNLogN.Machine.FFT.DIF

open SubNLogN.Math.Common SubNLogN.Math.Walsh

/-! ## Tables of rows -/

/-- The table of rows `[f g 0, …, f g (k-1)]`, `g < n`. -/
def tab2 {α : Type} (n k : ℕ) (f : ℕ → ℕ → α) : List (List α) :=
  (List.range n).map fun g => (List.range k).map (f g)

theorem inter_range {α : Type} (F G : ℕ → α) : ∀ n,
    inter ((List.range n).map F) ((List.range n).map G) =
      (List.range (2 * n)).map fun i => if i % 2 = 0 then F (i / 2) else G (i / 2)
  | 0 => rfl
  | n + 1 => by
    have e := inter_append_pair ((List.range n).map F) ((List.range n).map G) (F n) (G n)
      (by simp)
    rw [List.range_succ, List.map_append, List.map_append, List.map_cons, List.map_cons,
      List.map_nil, List.map_nil, e, inter_range F G n,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ]
    have h1 : 2 * n % 2 = 0 := by omega
    have h2 : 2 * n / 2 = n := by omega
    have h3 : (2 * n + 1) % 2 = 1 := by omega
    have h4 : (2 * n + 1) / 2 = n := by omega
    simp [h1, h2, h3, h4]

theorem take_map_range {α : Type} (F : ℕ → α) (h k : ℕ) (hk : h ≤ k) :
    ((List.range k).map F).take h = (List.range h).map F := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

theorem drop_map_range {α : Type} (F : ℕ → α) (h k : ℕ) :
    ((List.range (h + k)).map F).drop h = (List.range k).map fun j => F (h + j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_drop]

theorem zipWith_map_range {α β γ : Type} (op : α → β → γ) (F : ℕ → α) (G : ℕ → β) (k : ℕ) :
    List.zipWith op ((List.range k).map F) ((List.range k).map G) =
      (List.range k).map fun j => op (F j) (G j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem tab2_congr {α : Type} {n k : ℕ} {f g : ℕ → ℕ → α}
    (h : ∀ i, i < n → ∀ j, j < k → f i j = g i j) : tab2 n k f = tab2 n k g := by
  unfold tab2
  apply List.map_congr_left
  intro i hi
  apply List.map_congr_left
  intro j hj
  exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

theorem length_tab2 {α : Type} (n k : ℕ) (f : ℕ → ℕ → α) : (tab2 n k f).length = n := by
  simp [tab2]

theorem mem_tab2 {α : Type} {n k : ℕ} {f : ℕ → ℕ → α} {row : List α} (h : row ∈ tab2 n k f) :
    row.length = k ∧ ∀ c ∈ row, ∃ i, i < n ∧ ∃ j, j < k ∧ c = f i j := by
  simp only [tab2, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨by simp, fun c hc => ?_⟩
  simp only [List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  exact ⟨i, hi, j, hj, rfl⟩

theorem tab2_map_take {α : Type} (n h k : ℕ) (f : ℕ → ℕ → α) (hk : h ≤ k) :
    (tab2 n k f).map (List.take h) = tab2 n h f := by
  simp only [tab2, List.map_map]
  apply List.map_congr_left
  intro i _
  exact take_map_range _ h k hk

theorem tab2_map_drop {α : Type} (n h : ℕ) (f : ℕ → ℕ → α) :
    (tab2 n (h + h) f).map (List.drop h) = tab2 n h (fun i j => f i (h + j)) := by
  simp only [tab2, List.map_map]
  apply List.map_congr_left
  intro i _
  exact drop_map_range _ h h

theorem zipC_tab2 (op : CInt → CInt → CInt) (n k : ℕ) (f g : ℕ → ℕ → CInt) :
    zipC op (tab2 n k f) (tab2 n k g) = tab2 n k (fun i j => op (f i j) (g i j)) := by
  unfold zipC tab2
  rw [zipWith_map_range]
  apply List.map_congr_left
  intro i _
  exact zipWith_map_range _ _ _ k

theorem replicate_eq_tab2 {α : Type} (n k : ℕ) (F : ℕ → α) :
    List.replicate n ((List.range k).map F) = tab2 n k (fun _ j => F j) := by
  simp [tab2, List.map_const']

theorem inter_tab2 {α : Type} (n k : ℕ) (f g : ℕ → ℕ → α) :
    inter (tab2 n k f) (tab2 n k g) =
      tab2 (2 * n) k (fun i j => if i % 2 = 0 then f (i / 2) j else g (i / 2) j) := by
  unfold tab2
  rw [inter_range]
  apply List.map_congr_left
  intro i _
  split_ifs with h <;> simp [h]

theorem zipWith_inter_tab2 {α : Type} (n k : ℕ) (f g : ℕ → ℕ → α) :
    List.zipWith inter (tab2 n k f) (tab2 n k g) =
      tab2 n (2 * k) (fun i j => if j % 2 = 0 then f i (j / 2) else g i (j / 2)) := by
  unfold tab2
  rw [zipWith_map_range]
  apply List.map_congr_left
  intro i _
  exact inter_range _ _ k

theorem tab2_double {α : Type} (n k : ℕ) (f : ℕ → ℕ → α) :
    tab2 (2 * n) k f = inter (tab2 n k (fun i j => f (2 * i) j))
      (tab2 n k (fun i j => f (2 * i + 1) j)) := by
  rw [inter_tab2]
  apply tab2_congr
  intro i _ j _
  split_ifs with h
  · congr 1; omega
  · congr 1; omega


/-! ## The integer pipeline -/

/-- The integer phase table: `gridInt q (θ̃_j)`, `j < 2·2^ℓ` (the payloads of `tabRecs`). -/
noncomputable def tabInt (q ℓ : ℕ) (θt : ℕ → ℂ) : List CInt :=
  (List.range (2 * 2 ^ ℓ)).map fun j => gridInt q (θt j)

/-- The stage table: `[tab[st·j]]_{j<h}`. -/
def stageB (tab : List CInt) (h st : ℕ) : List CInt :=
  (List.range h).map fun j => tab.getD (st * j) 0

/-- One DIF level on the blocked array (blocks of `2h` coefficients): half-sums of the halves, then
half-differences times the stage table (`cmulTruncC q`), interleaved block by block. -/
def levelB (q h : ℕ) (stage : List CInt) (B : List (List CInt)) : List (List CInt) :=
  inter (zipC halfSumC (B.map (List.take h)) (B.map (List.drop h)))
    (zipC (cmulTruncC q) (zipC halfDiffC (B.map (List.take h)) (B.map (List.drop h)))
      (List.replicate B.length stage))

/-- Levels `0, …, s-1` (level `s'` has half `2^{ℓ-s'-1}` and stage stride `2^{s'+1}`). -/
def levelsB (q ℓ : ℕ) (tab : List CInt) : ℕ → List (List CInt) → List (List CInt)
  | 0, B => B
  | s + 1, B => levelB q (2 ^ (ℓ - s - 1)) (stageB tab (2 ^ (ℓ - s - 1)) (2 ^ (s + 1)))
      (levelsB q ℓ tab s B)

/-- One bit-reversal pass: consecutive record pairs merged by coefficientwise interleaving. -/
def brPass (B : List (List CInt)) : List (List CInt) := List.zipWith inter (evens B) (odds B)

/-- `t` bit-reversal passes. -/
def brIter : ℕ → List (List CInt) → List (List CInt)
  | 0, B => B
  | t + 1, B => brPass (brIter t B)

theorem levelB_tab2 (q h n : ℕ) (stage : List CInt) (hst : stage.length = h)
    (f : ℕ → ℕ → CInt) :
    levelB q h stage (tab2 n (h + h) f) = tab2 (2 * n) h (fun i j =>
      if i % 2 = 0 then halfSumC (f (i / 2) j) (f (i / 2) (h + j))
      else cmulTruncC q (halfDiffC (f (i / 2) j) (f (i / 2) (h + j))) (stage.getD j 0)) := by
  have hs : stage = (List.range h).map fun j => stage.getD j 0 := by
    apply List.ext_getElem
    · simp [hst]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h1]
  have hrep : List.replicate n stage = tab2 n h (fun _ j => stage.getD j 0) := by
    rw [tab2, List.map_const', List.length_range, ← hs]
  unfold levelB
  rw [tab2_map_take _ _ _ _ (by omega), tab2_map_drop, zipC_tab2, zipC_tab2, length_tab2, hrep,
    zipC_tab2, inter_tab2]

theorem brPass_tab2 {n k : ℕ} (f : ℕ → ℕ → CInt) :
    brPass (tab2 (2 * n) k f) = tab2 n (2 * k) (fun i j => f (2 * i + j % 2) (j / 2)) := by
  unfold brPass
  rw [tab2_double, evens_inter _ _ (by simp [length_tab2]), odds_inter _ _ (by simp [length_tab2]),
    zipWith_inter_tab2]
  apply tab2_congr
  intro i _ j _
  split_ifs with h
  · rw [h, Nat.add_zero]
  · rw [show j % 2 = 1 by omega]

/-! ## Grid values -/

theorem gridUnit_mul_pow (F : ℕ) : gridUnit F * (2 : ℝ) ^ F = 1 := by
  unfold gridUnit
  field_simp

theorem gridInt_gridVal (F : ℕ) (c : CInt) : gridInt F (gridVal F c) = c := by
  obtain ⟨a, b⟩ := c
  simp [gridInt, gridVal, mul_assoc, gridUnit_mul_pow]

theorem gridVal_gridInt {F : ℕ} {z : ℂ} (hz : OnGrid F z) : gridVal F (gridInt F z) = z := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  apply Complex.ext
  · simp [gridVal, gridInt, ha, mul_assoc, gridUnit_mul_pow]
  · simp [gridVal, gridInt, hb, mul_assoc, gridUnit_mul_pow]

theorem halfSumC_gridInt {q : ℕ} {a b : ℂ} (ha : OnGrid q a) (hb : OnGrid q b) :
    halfSumC (gridInt q a) (gridInt q b) = gridInt q (truncC q ((a + b) / 2)) := by
  rw [← gridInt_gridVal q (halfSumC _ _), gridVal_halfSumC, gridVal_gridInt ha, gridVal_gridInt hb]

theorem halfDiffC_gridInt {q : ℕ} {a b : ℂ} (ha : OnGrid q a) (hb : OnGrid q b) :
    halfDiffC (gridInt q a) (gridInt q b) = gridInt q (truncC q ((a - b) / 2)) := by
  rw [← gridInt_gridVal q (halfDiffC _ _), gridVal_halfDiffC, gridVal_gridInt ha,
    gridVal_gridInt hb]

theorem cmulTruncC_gridInt {q : ℕ} {d t : ℂ} (hd : OnGrid q d) (ht : OnGrid q t) :
    cmulTruncC q (gridInt q d) (gridInt q t) = gridInt q (truncC q (t * d)) := by
  rw [← gridInt_gridVal q (cmulTruncC q _ _), gridVal_cmulTruncC q q q q rfl, gridVal_gridInt hd,
    gridVal_gridInt ht, mul_comm]

theorem abs_gridInt_le {q : ℕ} {z : ℂ} (hz : OnDiskGrid q z) :
    |(gridInt q z).1| ≤ 2 ^ q ∧ |(gridInt q z).2| ≤ 2 ^ q := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hn⟩ := hz
  have hz : z = gridVal q (a, b) := by
    apply Complex.ext
    · simp [gridVal, ha]
    · simp [gridVal, hb]
  have hg : gridInt q z = (a, b) := by rw [hz, gridInt_gridVal]
  rw [hg]
  have hu : 0 < gridUnit q := gridUnit_pos q
  have hu2 : gridUnit q * (2 : ℝ) ^ q = 1 := gridUnit_mul_pow q
  have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hn
  have him : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hn
  rw [ha, abs_mul, abs_of_pos hu] at hre
  rw [hb, abs_mul, abs_of_pos hu] at him
  have h2 : (0 : ℝ) < 2 ^ q := by positivity
  constructor
  · have : (|a| : ℝ) ≤ 2 ^ q := by
      have := mul_le_mul_of_nonneg_right hre h2.le
      rw [mul_assoc, hu2, mul_one, one_mul] at this
      exact_mod_cast this
    exact_mod_cast this
  · have : (|b| : ℝ) ≤ 2 ^ q := by
      have := mul_le_mul_of_nonneg_right him h2.le
      rw [mul_assoc, hu2, mul_one, one_mul] at this
      exact_mod_cast this
    exact_mod_cast this

theorem fitsTwos_of_abs_le {q w : ℕ} (hw : q + 2 ≤ w) {a : ℤ} (ha : |a| ≤ 2 ^ q) :
    FitsTwos w a := by
  unfold FitsTwos
  have h1 : (2 : ℤ) ^ q * 2 ≤ 2 ^ (w - 1) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℤ) < 2 ^ q := by positivity
  constructor <;> [linarith [neg_abs_le a]; linarith [le_abs_self a]]

theorem fits_gridInt {q w : ℕ} (hw : q + 2 ≤ w) {z : ℂ} (hz : OnDiskGrid q z) :
    FitsTwos w (gridInt q z).1 ∧ FitsTwos w (gridInt q z).2 :=
  ⟨fitsTwos_of_abs_le hw (abs_gridInt_le hz).1, fitsTwos_of_abs_le hw (abs_gridInt_le hz).2⟩

/-! ## Disk-grid invariants of the DIF levels -/

theorem getCoeff_diskGrid {q n : ℕ} {w : Fin n → ℂ} (hw : ∀ k, OnDiskGrid q (w k)) (k : ℕ) :
    OnDiskGrid q (getCoeff w k) := by
  unfold getCoeff
  split_ifs with h
  · exact hw _
  · exact ⟨onGrid_zero q, by simp⟩

theorem norm_half_le {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖(a + b) / 2‖ ≤ 1 ∧ ‖(a - b) / 2‖ ≤ 1 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  constructor
  · rw [norm_div, h2]
    have := norm_add_le a b
    linarith
  · rw [norm_div, h2]
    have := norm_sub_le a b
    linarith

theorem difIdx_lt {ℓ s : ℕ} (hs : s < ℓ) (k : ℕ) :
    2 ^ (s + 1) * (k % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1)) < 2 * 2 ^ ℓ := by
  have hpow1 : 2 ^ (ℓ - s) = 2 * 2 ^ (ℓ - s - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow3 : 2 ^ (s + 1) * 2 ^ (ℓ - s - 1) = 2 ^ ℓ := by
    rw [← pow_add]; congr 1; omega
  have hm : k % 2 ^ (ℓ - s) < 2 ^ (ℓ - s) := Nat.mod_lt _ (by positivity)
  have h1 : k % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1) < 2 ^ (ℓ - s - 1) := by omega
  have h2 : 2 ^ (s + 1) * (k % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1)) < 2 ^ (s + 1) * 2 ^ (ℓ - s - 1) :=
    Nat.mul_lt_mul_of_pos_left h1 (by positivity)
  have h3 : 0 < 2 ^ ℓ := by positivity
  omega

theorem difLevel_diskGrid {q ℓ s : ℕ} {θt : ℕ → ℂ}
    (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (hs : s < ℓ) {w : Fin (2 ^ ℓ) → ℂ}
    (hw : ∀ k, OnDiskGrid q (w k)) (k : Fin (2 ^ ℓ)) : OnDiskGrid q (difLevel q ℓ s θt w k) := by
  unfold difLevel
  split_ifs with h
  · apply truncC_mem_diskGrid
    exact (norm_half_le (getCoeff_diskGrid hw _).2 (getCoeff_diskGrid hw _).2).1
  · apply truncC_mem_diskGrid
    rw [norm_mul]
    have h1 := (hθ _ (difIdx_lt hs k)).2
    have h2 : ‖truncC q ((getCoeff w (↑k - 2 ^ (ℓ - s - 1)) - getCoeff w ↑k) / 2)‖ ≤ 1 :=
      (norm_truncC_le _ _).trans
        (norm_half_le (getCoeff_diskGrid hw _).2 (getCoeff_diskGrid hw _).2).2
    exact mul_le_one₀ h1 (norm_nonneg _) h2

/-- The values after levels `0, …, s-1` (the fold of `lastAxisFFT`). -/
noncomputable def Wst (q ℓ : ℕ) (θt : ℕ → ℂ) (v : Fin (2 ^ ℓ) → ℂ) (s : ℕ) : Fin (2 ^ ℓ) → ℂ :=
  (List.range s).foldl (fun w s' => difLevel q ℓ s' θt w) v

theorem Wst_succ (q ℓ : ℕ) (θt : ℕ → ℂ) (v : Fin (2 ^ ℓ) → ℂ) (s : ℕ) :
    Wst q ℓ θt v (s + 1) = difLevel q ℓ s θt (Wst q ℓ θt v s) := by
  simp [Wst, List.range_succ, List.foldl_append]

theorem Wst_diskGrid {q ℓ : ℕ} {θt : ℕ → ℂ} (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j))
    {v : Fin (2 ^ ℓ) → ℂ} (hv : ∀ k, OnDiskGrid q (v k)) :
    ∀ s, s ≤ ℓ → ∀ k, OnDiskGrid q (Wst q ℓ θt v s k)
  | 0, _, k => hv k
  | s + 1, hs, k => by
    rw [Wst_succ]
    exact difLevel_diskGrid hθ (by omega) (Wst_diskGrid hθ hv s (by omega)) k


/-! ## The level invariant -/

/-- Integer coefficient `j` of block `g` after `s` levels (`2^{m+s}` blocks of `2^{ℓ-s}`
coefficients): block `g` is the aligned chunk `g mod 2^s` of record `g / 2^s`. -/
noncomputable def blkF (q ℓ m : ℕ) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ)) (s : ℕ) :
    ℕ → ℕ → CInt :=
  fun g j => gridInt q (getCoeff (Wst q ℓ θt (z (cubeOfNat m (g / 2 ^ s))) s)
    (g % 2 ^ s * 2 ^ (ℓ - s) + j))

theorem encCube_eq_tab2 (q ℓ m : ℕ) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ)) :
    encCube q z = tab2 (2 ^ m) (2 ^ ℓ) (blkF q ℓ m θt z 0) := by
  unfold encCube encArr cubeAddrs tab2
  rw [List.map_map]
  apply List.map_congr_left
  intro g _
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have h1' : j < 2 ^ ℓ := by simpa using h1
    have e : blkF q ℓ m θt z 0 g j = gridInt q (z (cubeOfNat m g) ⟨j, h1'⟩) := by
      show gridInt q (getCoeff (Wst q ℓ θt (z (cubeOfNat m (g / 2 ^ 0))) 0)
        (g % 2 ^ 0 * 2 ^ (ℓ - 0) + j)) = _
      have e1 : g / 2 ^ 0 = g := by simp
      have e2 : g % 2 ^ 0 * 2 ^ (ℓ - 0) + j = j := by
        rw [pow_zero, Nat.mod_one, Nat.zero_mul, Nat.zero_add]
      rw [e1, e2]
      simp [Wst, getCoeff, h1']
    rw [List.getElem_map, List.getElem_range, e]
    simp

theorem level_point (q ℓ m : ℕ) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ))
    (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (hz : ArrOnDiskGrid q z) (s : ℕ)
    (hs : s < ℓ) (i j : ℕ) (hj : j < 2 ^ (ℓ - s - 1)) :
    (if i % 2 = 0 then
        halfSumC (blkF q ℓ m θt z s (i / 2) j) (blkF q ℓ m θt z s (i / 2) (2 ^ (ℓ - s - 1) + j))
      else cmulTruncC q (halfDiffC (blkF q ℓ m θt z s (i / 2) j)
        (blkF q ℓ m θt z s (i / 2) (2 ^ (ℓ - s - 1) + j)))
        ((stageB (tabInt q ℓ θt) (2 ^ (ℓ - s - 1)) (2 ^ (s + 1))).getD j 0)) =
      blkF q ℓ m θt z (s + 1) i j := by
  have hhpos : 0 < 2 ^ (ℓ - s - 1) := by positivity
  have hPpos : 0 < 2 ^ s := by positivity
  have hpow1 : 2 ^ (ℓ - s) = 2 * 2 ^ (ℓ - s - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow2 : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hpow3 : 2 * 2 ^ s * 2 ^ (ℓ - s - 1) = 2 ^ ℓ := by
    rw [← hpow2, ← pow_add]; congr 1; omega
  have hls : ℓ - (s + 1) = ℓ - s - 1 := by omega
  -- names
  generalize hh : 2 ^ (ℓ - s - 1) = h at hhpos hpow1 hpow3 hj ⊢
  generalize hP : 2 ^ s = P at hPpos hpow2 hpow3 ⊢
  have hrP : i / 2 % P < P := Nat.mod_lt _ hPpos
  generalize hr : i / 2 % P = r at hrP
  set x := z (cubeOfNat m (i / 2 / P)) with hx
  set w := Wst q ℓ θt x s with hw
  have hwd : ∀ k, OnDiskGrid q (getCoeff w k) :=
    getCoeff_diskGrid (Wst_diskGrid hθ (fun k => hz _ k) s hs.le)
  have hB : ∀ j', blkF q ℓ m θt z s (i / 2) j' = gridInt q (getCoeff w (r * (2 * h) + j')) := by
    intro j'
    simp only [blkF, hP, hpow1, hr, hw, hx]
  have hdiv : i / 2 ^ (s + 1) = i / 2 / P := by rw [hpow2, Nat.div_div_eq_div_mul]
  have hmod : i % 2 ^ (s + 1) = i % 2 + 2 * r := by rw [hpow2, Nat.mod_mul, hr]
  have hB1 : blkF q ℓ m θt z (s + 1) i j =
      gridInt q (getCoeff (difLevel q ℓ s θt w) ((i % 2 + 2 * r) * h + j)) := by
    simp only [blkF, Wst_succ, hdiv, hmod, hls, hh, hw, hx]
  rw [hB, hB, hB1]
  have hc2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hlt : i % 2 * h + j < 2 * h := by
    rcases Nat.mod_two_eq_zero_or_one i with hc | hc <;> rw [hc] <;> omega
  have hk2 : (i % 2 + 2 * r) * h + j = r * (2 * h) + (i % 2 * h + j) := by ring
  have hkl : (i % 2 + 2 * r) * h + j < 2 ^ ℓ := by
    rw [← hpow3, hk2]
    have : (r + 1) * (2 * h) ≤ P * (2 * h) := Nat.mul_le_mul_right _ hrP
    nlinarith
  rcases Nat.mod_two_eq_zero_or_one i with hc | hc
  · -- upper output
    have hk' : (i % 2 + 2 * r) * h + j = r * (2 * h) + j := by rw [hc]; ring
    have hkl' : r * (2 * h) + j < 2 ^ ℓ := by rw [← hk']; exact hkl
    have hgc : getCoeff (difLevel q ℓ s θt w) ((i % 2 + 2 * r) * h + j) =
        difLevel q ℓ s θt w ⟨r * (2 * h) + j, hkl'⟩ := by
      rw [hk']
      simp [getCoeff, hkl']
    have hm : (r * (2 * h) + j) % 2 ^ (ℓ - s) = j := by
      rw [hpow1, Nat.mul_comm r, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hgc, if_pos hc]
    simp only [difLevel, Fin.val_mk, hm, hh, if_pos hj]
    rw [halfSumC_gridInt (hwd _).1 (hwd _).1,
      show r * (2 * h) + (h + j) = r * (2 * h) + j + h by ring]
  · -- lower output
    have hk' : (i % 2 + 2 * r) * h + j = r * (2 * h) + (h + j) := by rw [hc]; ring
    have hkl' : r * (2 * h) + (h + j) < 2 ^ ℓ := by rw [← hk']; exact hkl
    have hgc : getCoeff (difLevel q ℓ s θt w) ((i % 2 + 2 * r) * h + j) =
        difLevel q ℓ s θt w ⟨r * (2 * h) + (h + j), hkl'⟩ := by
      rw [hk']
      simp [getCoeff, hkl']
    have hm : (r * (2 * h) + (h + j)) % 2 ^ (ℓ - s) = h + j := by
      rw [hpow1, Nat.mul_comm r, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hidx : 2 ^ (s + 1) * j < 2 * 2 ^ ℓ := by
      rw [hpow2, ← hpow3]
      have : 2 * P * j < 2 * P * h := Nat.mul_lt_mul_of_pos_left hj (by positivity)
      nlinarith
    have hst : (stageB (tabInt q ℓ θt) h (2 ^ (s + 1))).getD j 0 =
        gridInt q (θt (2 ^ (s + 1) * j)) := by
      rw [stageB, List.getD_eq_getElem _ _ (by simpa using hj)]
      simp only [List.getElem_map, List.getElem_range]
      rw [tabInt, List.getD_eq_getElem _ _ (by simpa using hidx)]
      simp
    rw [hgc, if_neg (by omega : ¬ i % 2 = 0)]
    simp only [difLevel, Fin.val_mk, hm, hh, if_neg (by omega : ¬ (h + j < h)),
      Nat.add_sub_cancel_left]
    rw [hst, halfDiffC_gridInt (hwd _).1 (hwd _).1,
      cmulTruncC_gridInt (truncC_onGrid _ _) (hθ _ hidx).1,
      show r * (2 * h) + (h + j) - h = r * (2 * h) + j by omega]

theorem levelsB_eq (q ℓ m : ℕ) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ))
    (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (hz : ArrOnDiskGrid q z) :
    ∀ s, s ≤ ℓ → levelsB q ℓ (tabInt q ℓ θt) s (encCube q z) =
      tab2 (2 ^ m * 2 ^ s) (2 ^ (ℓ - s)) (blkF q ℓ m θt z s)
  | 0, _ => by simp [levelsB, encCube_eq_tab2 q ℓ m θt z]
  | s + 1, hs => by
    rw [levelsB, levelsB_eq q ℓ m θt z hθ hz s (by omega)]
    have hpow1 : 2 ^ (ℓ - s) = 2 ^ (ℓ - s - 1) + 2 ^ (ℓ - s - 1) := by
      rw [← two_mul, ← pow_succ']; congr 1; omega
    rw [hpow1, levelB_tab2 q _ _ _ (by simp [stageB])]
    rw [show 2 ^ m * 2 ^ (s + 1) = 2 * (2 ^ m * 2 ^ s) by ring,
      show ℓ - (s + 1) = ℓ - s - 1 by omega]
    apply tab2_congr
    intro i _ j hj
    exact level_point q ℓ m θt z hθ hz s (by omega) i j hj

/-! ## The bit-reversal invariant -/

theorem bitRevNat_zero (k : ℕ) : bitRevNat 0 k = 0 := by simp [bitRevNat]

theorem bitRevNat_succ (t j : ℕ) : bitRevNat (t + 1) j = j % 2 * 2 ^ t + bitRevNat t (j / 2) := by
  unfold bitRevNat
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.testBit_succ, show t + 1 - 1 - (i + 1) = t - 1 - i by omega]

/-- Record `g` after `t` bit-reversal passes holds the aligned chunk `g mod 2^{ℓ-t}` of record
`g / 2^{ℓ-t}`, bit reversed. -/
def brF (Y : ℕ → ℕ → CInt) (ℓ t : ℕ) : ℕ → ℕ → CInt :=
  fun g k => Y (g / 2 ^ (ℓ - t)) (g % 2 ^ (ℓ - t) * 2 ^ t + bitRevNat t k)

theorem brIter_eq (Y : ℕ → ℕ → CInt) (M ℓ : ℕ) :
    ∀ t, t ≤ ℓ → brIter t (tab2 (M * 2 ^ ℓ) 1 (fun g _ => Y (g / 2 ^ ℓ) (g % 2 ^ ℓ))) =
      tab2 (M * 2 ^ (ℓ - t)) (2 ^ t) (brF Y ℓ t)
  | 0, _ => by
    simp only [brIter, Nat.sub_zero, pow_zero]
    apply tab2_congr
    intro g _ k _
    simp [brF, bitRevNat_zero]
  | t + 1, ht => by
    rw [brIter, brIter_eq Y M ℓ t (by omega)]
    have hpow : M * 2 ^ (ℓ - t) = 2 * (M * 2 ^ (ℓ - (t + 1))) := by
      rw [show ℓ - t = (ℓ - (t + 1)) + 1 by omega, pow_succ]; ring
    rw [hpow, brPass_tab2, show 2 * 2 ^ t = 2 ^ (t + 1) by rw [pow_succ]; ring]
    apply tab2_congr
    intro i _ j _
    simp only [brF]
    have hQ : 0 < 2 ^ (ℓ - (t + 1)) := by positivity
    have hp2 : 2 ^ (ℓ - t) = 2 * 2 ^ (ℓ - (t + 1)) := by
      rw [show ℓ - t = (ℓ - (t + 1)) + 1 by omega, pow_succ]; ring
    rw [hp2, bitRevNat_succ]
    have hc : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have e1 : (2 * i + j % 2) / (2 * 2 ^ (ℓ - (t + 1))) = i / 2 ^ (ℓ - (t + 1)) := by
      rw [← Nat.div_div_eq_div_mul]
      congr 1
      omega
    have e2 : (2 * i + j % 2) % (2 * 2 ^ (ℓ - (t + 1))) = j % 2 + 2 * (i % 2 ^ (ℓ - (t + 1))) := by
      have ha : (2 * i + j % 2) % 2 = j % 2 := by omega
      have hb : (2 * i + j % 2) / 2 = i := by omega
      rw [Nat.mod_mul, ha, hb]
    rw [e1, e2]
    congr 1
    rw [pow_succ]
    ring

/-! ## The pipeline computes `lastAxisFFT` -/

theorem pipeline_correct (q ℓ m : ℕ) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ))
    (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (hz : ArrOnDiskGrid q z) :
    brIter ℓ (levelsB q ℓ (tabInt q ℓ θt) ℓ (encCube q z)) =
      encCube q (lastAxisFFT q ℓ θt z) := by
  rw [levelsB_eq q ℓ m θt z hθ hz ℓ le_rfl, Nat.sub_self, pow_zero]
  set Y : ℕ → ℕ → CInt := fun x i =>
    gridInt q (getCoeff (Wst q ℓ θt (z (cubeOfNat m x)) ℓ) i) with hY
  have h1 : tab2 (2 ^ m * 2 ^ ℓ) 1 (blkF q ℓ m θt z ℓ) =
      tab2 (2 ^ m * 2 ^ ℓ) 1 (fun g _ => Y (g / 2 ^ ℓ) (g % 2 ^ ℓ)) := by
    apply tab2_congr
    intro g _ j hj
    have : j = 0 := by omega
    subst this
    simp [blkF, hY]
  rw [h1, brIter_eq Y (2 ^ m) ℓ ℓ le_rfl, Nat.sub_self, pow_zero, mul_one,
    encCube_eq_tab2 q ℓ m θt (lastAxisFFT q ℓ θt z)]
  apply tab2_congr
  intro g _ k hk
  have hR : getCoeff (Wst q ℓ θt (lastAxisFFT q ℓ θt z (cubeOfNat m g)) 0) k =
      getCoeff (Wst q ℓ θt (z (cubeOfNat m g)) ℓ) (bitRevNat ℓ k) := by
    rw [show Wst q ℓ θt (lastAxisFFT q ℓ θt z (cubeOfNat m g)) 0 =
      lastAxisFFT q ℓ θt z (cubeOfNat m g) from rfl, getCoeff, dif_pos hk]
    rfl
  simp only [brF, blkF, hY, Nat.sub_self, pow_zero, Nat.div_one, Nat.mod_one, Nat.zero_mul,
    Nat.zero_add, Nat.sub_zero, mul_one, hR]

end SubNLogN.Machine.FFT.DIF
