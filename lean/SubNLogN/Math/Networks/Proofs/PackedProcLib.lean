import SubNLogN.Math.Networks.AppCPacked

/-!
# Lemma A.9 (`lem:transfer13`): shared library for the packed selected-bit addition proofs

Generic facts about the abstract stream model (`AppCModel.lean`), used by `PackedProcCorrectStmt`
(`Proofs/PackedProc.lean`, `Proofs/PackedProcBits.lean`) and `PackedProcWFStmt`
(`Proofs/PackedProcWF.lean`). Namespace `SubNLogN.Math.Networks.PackedProcAux`.

* **Mixed-radix blocks** of an arbitrary layout and arbitrary block `[t₀, t₁)`: `blockVal_split`,
  `blockRange_split`, `blockVal_lt`, `blockVal_blockSet` (`= v % blockRange`), `blockSet_blockVal`,
  `blockVal_digit` (digit of a field), `apply_eq_of_blockVal_eq`, disjoint blocks
  (`blockVal_blockSet_of_disjoint`, `blockSet_comm_of_disjoint`), `blockRange_binary`
  (`= 2^(t₁−t₀)` for binary fields).
* **Binary chunks** (`ChunkOK Ly L p`: `L` binary fields at `p`, inside the layout): `chunkVal_lt`,
  `chunkVal_blockSet`, `chunkBit_eq` (bit `j` of a chunk is bit `j` of its value), `eq_of_bitAt_eq`,
  `addr_ext3` (an address is determined by three chunk values and the other fields).
* **Address-moving steps** (`elem`, `sparsePerm`, `swapBlocks`): `stepPull`, `pullComp`, and
  `foldl_runIn`: a list of such steps run in a row class `c` whose pulls fix the row field acts as
  `A ↦ (a ↦ if a ∈ c then A (pullComp p a) else A a)`. Effects of `swapBlocks` and `Elem.shift` on
  chunk values (`swap_chunk_*`, `shift_chunk_*`).
-/

namespace SubNLogN.Math.Networks

open Model

namespace PackedProcAux

/-! ## Mixed-radix blocks of a layout -/

section Blocks

variable {Ly : Layout}

theorem mem_filter_inBlock {n t₀ t₁ : ℕ} (j : Fin n) :
    j ∈ Finset.univ.filter (inBlock t₀ t₁ (n := n)) ↔ t₀ ≤ j.val ∧ j.val < t₁ := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock]

theorem filter_inBlock_union {n t₀ u t₁ : ℕ} (h₁ : t₀ ≤ u) (h₂ : u ≤ t₁) :
    Finset.univ.filter (inBlock t₀ t₁ (n := n)) =
      Finset.univ.filter (inBlock t₀ u (n := n)) ∪ Finset.univ.filter (inBlock u t₁ (n := n)) := by
  ext j
  simp only [Finset.mem_union, mem_filter_inBlock]
  omega

theorem disjoint_filter_inBlock {n t₀ u t₁ : ℕ} :
    Disjoint (Finset.univ.filter (inBlock t₀ u (n := n)))
      (Finset.univ.filter (inBlock u t₁ (n := n))) := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  rw [mem_filter_inBlock] at h1 h2
  omega

theorem filter_inBlock_eq_empty {n t₀ t₁ : ℕ} (h : n ≤ t₀ ∨ t₁ ≤ t₀) :
    Finset.univ.filter (inBlock t₀ t₁ (n := n)) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr (fun j _ hj => ?_)
  simp only [inBlock] at hj
  omega

theorem filter_inBlock_single {n t : ℕ} (h : t < n) :
    Finset.univ.filter (inBlock t (t + 1) (n := n)) = {⟨t, h⟩} := by
  ext j
  simp only [mem_filter_inBlock, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem blockSet_apply_of_not {t₀ t₁ : ℕ} (x : Ly.Addr) (v : ℕ) (j : Fin Ly.n)
    (hj : ¬ (t₀ ≤ j.val ∧ j.val < t₁)) : Ly.blockSet t₀ t₁ x v j = x j := by
  simp only [Layout.blockSet]
  rw [if_neg (show ¬ inBlock t₀ t₁ j from hj)]

theorem blockSet_apply_val {t₀ t₁ : ℕ} (x : Ly.Addr) (v : ℕ) (j : Fin Ly.n)
    (hj : t₀ ≤ j.val ∧ j.val < t₁) :
    (Ly.blockSet t₀ t₁ x v j).val = v / Ly.place t₁ j % Ly.r j := by
  simp only [Layout.blockSet]
  rw [if_pos (show inBlock t₀ t₁ j from hj)]

theorem blockVal_congr {t₀ t₁ : ℕ} {x y : Ly.Addr}
    (h : ∀ j : Fin Ly.n, t₀ ≤ j.val → j.val < t₁ → x j = y j) :
    Ly.blockVal t₀ t₁ x = Ly.blockVal t₀ t₁ y := by
  unfold Layout.blockVal
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_filter_inBlock] at hj
  rw [h j hj.1 hj.2]

theorem blockSet_congr {t₀ t₁ : ℕ} {x y : Ly.Addr} (v : ℕ)
    (h : ∀ j : Fin Ly.n, ¬ (t₀ ≤ j.val ∧ j.val < t₁) → x j = y j) :
    Ly.blockSet t₀ t₁ x v = Ly.blockSet t₀ t₁ y v := by
  funext j
  by_cases hj : t₀ ≤ j.val ∧ j.val < t₁
  · exact Fin.ext (by rw [blockSet_apply_val _ _ _ hj, blockSet_apply_val _ _ _ hj])
  · rw [blockSet_apply_of_not _ _ _ hj, blockSet_apply_of_not _ _ _ hj, h j hj]

theorem blockSet_blockSet (t₀ t₁ : ℕ) (x : Ly.Addr) (v v' : ℕ) :
    Ly.blockSet t₀ t₁ (Ly.blockSet t₀ t₁ x v) v' = Ly.blockSet t₀ t₁ x v' :=
  blockSet_congr v' fun j hj => blockSet_apply_of_not x v j hj

theorem place_eq_blockRange (t₁ : ℕ) (j : Fin Ly.n) :
    Ly.place t₁ j = Ly.blockRange (j.val + 1) t₁ := by
  unfold Layout.place Layout.blockRange
  rw [Finset.filter_congr (q := inBlock (j.val + 1) t₁ (n := Ly.n)) (fun j' _ => by
    unfold inBlock; rw [Fin.lt_def]; omega)]

theorem blockRange_split {t₀ u t₁ : ℕ} (h₁ : t₀ ≤ u) (h₂ : u ≤ t₁) :
    Ly.blockRange t₀ t₁ = Ly.blockRange t₀ u * Ly.blockRange u t₁ := by
  unfold Layout.blockRange
  rw [filter_inBlock_union h₁ h₂, Finset.prod_union disjoint_filter_inBlock]

theorem blockRange_eq_one {t₀ t₁ : ℕ} (h : Ly.n ≤ t₀ ∨ t₁ ≤ t₀) : Ly.blockRange t₀ t₁ = 1 := by
  unfold Layout.blockRange
  rw [filter_inBlock_eq_empty h, Finset.prod_empty]

theorem blockVal_eq_zero {t₀ t₁ : ℕ} (h : Ly.n ≤ t₀ ∨ t₁ ≤ t₀) (x : Ly.Addr) :
    Ly.blockVal t₀ t₁ x = 0 := by
  unfold Layout.blockVal
  rw [filter_inBlock_eq_empty h, Finset.sum_empty]

theorem place_split {u t₁ : ℕ} (j : Fin Ly.n) (hj : j.val < u) (h₂ : u ≤ t₁) :
    Ly.place t₁ j = Ly.place u j * Ly.blockRange u t₁ := by
  rw [place_eq_blockRange, place_eq_blockRange, blockRange_split (by omega) h₂]

theorem place_self (j : Fin Ly.n) : Ly.place (j.val + 1) j = 1 := by
  rw [place_eq_blockRange, blockRange_eq_one (Or.inr le_rfl)]

theorem blockRange_single {t : ℕ} (h : t < Ly.n) : Ly.blockRange t (t + 1) = Ly.r ⟨t, h⟩ := by
  unfold Layout.blockRange
  rw [filter_inBlock_single h, Finset.prod_singleton]

theorem blockVal_single {t : ℕ} (h : t < Ly.n) (x : Ly.Addr) :
    Ly.blockVal t (t + 1) x = (x ⟨t, h⟩).val := by
  unfold Layout.blockVal
  rw [filter_inBlock_single h, Finset.sum_singleton]
  have : Ly.place (t + 1) ⟨t, h⟩ = 1 := place_self ⟨t, h⟩
  rw [this, mul_one]

theorem blockVal_split {t₀ u t₁ : ℕ} (h₁ : t₀ ≤ u) (h₂ : u ≤ t₁) (x : Ly.Addr) :
    Ly.blockVal t₀ t₁ x = Ly.blockVal t₀ u x * Ly.blockRange u t₁ + Ly.blockVal u t₁ x := by
  unfold Layout.blockVal
  rw [filter_inBlock_union h₁ h₂, Finset.sum_union disjoint_filter_inBlock, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_filter_inBlock] at hj
  rw [place_split j hj.2 h₂, mul_assoc]


theorem blockVal_single_lt (t : ℕ) (x : Ly.Addr) :
    Ly.blockVal t (t + 1) x < Ly.blockRange t (t + 1) := by
  by_cases h : t < Ly.n
  · rw [blockVal_single h, blockRange_single h]
    exact (x ⟨t, h⟩).isLt
  · rw [blockVal_eq_zero (Or.inl (by omega)), blockRange_eq_one (Or.inl (by omega))]
    exact Nat.one_pos

/-- The value of a block is below its range. -/
theorem blockVal_lt (t₀ t₁ : ℕ) (x : Ly.Addr) : Ly.blockVal t₀ t₁ x < Ly.blockRange t₀ t₁ := by
  induction t₁ with
  | zero =>
    rw [blockVal_eq_zero (Or.inr (Nat.zero_le _)), blockRange_eq_one (Or.inr (Nat.zero_le _))]
    exact Nat.one_pos
  | succ t ih =>
    by_cases ht : t₀ ≤ t
    · rw [blockVal_split ht (Nat.le_succ t), blockRange_split ht (Nat.le_succ t)]
      have h1 := blockVal_single_lt t x
      have h2 : (Ly.blockVal t₀ t x + 1) * Ly.blockRange t (t + 1) ≤
          Ly.blockRange t₀ t * Ly.blockRange t (t + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ih)
      nlinarith
    · rw [blockVal_eq_zero (Or.inr (by omega)), blockRange_eq_one (Or.inr (by omega))]
      exact Nat.one_pos

theorem blockRange_pos (t₀ t₁ : ℕ) (x : Ly.Addr) : 0 < Ly.blockRange t₀ t₁ :=
  lt_of_le_of_lt (Nat.zero_le _) (blockVal_lt t₀ t₁ x)

/-- Reading back an overwritten block gives the value modulo the range. -/
theorem blockVal_blockSet (t₀ t₁ : ℕ) (x : Ly.Addr) (v : ℕ) :
    Ly.blockVal t₀ t₁ (Ly.blockSet t₀ t₁ x v) = v % Ly.blockRange t₀ t₁ := by
  induction t₁ generalizing v with
  | zero =>
    rw [blockVal_eq_zero (Or.inr (Nat.zero_le _)), blockRange_eq_one (Or.inr (Nat.zero_le _)),
      Nat.mod_one]
  | succ t ih =>
    by_cases ht : t₀ ≤ t
    · rw [blockVal_split ht (Nat.le_succ t), blockRange_split ht (Nat.le_succ t)]
      have e1 : Ly.blockVal t₀ t (Ly.blockSet t₀ (t + 1) x v) =
          Ly.blockVal t₀ t (Ly.blockSet t₀ t x (v / Ly.blockRange t (t + 1))) := by
        apply blockVal_congr
        intro j hj1 hj2
        apply Fin.ext
        rw [blockSet_apply_val _ _ _ ⟨hj1, by omega⟩, blockSet_apply_val _ _ _ ⟨hj1, hj2⟩,
          place_split j hj2 (Nat.le_succ t), Nat.div_div_eq_div_mul, Nat.mul_comm]
      have e2 : Ly.blockVal t (t + 1) (Ly.blockSet t₀ (t + 1) x v) =
          v % Ly.blockRange t (t + 1) := by
        by_cases htn : t < Ly.n
        · rw [blockVal_single htn, blockRange_single htn,
            blockSet_apply_val _ _ _ ⟨ht, Nat.lt_succ_self t⟩]
          have : Ly.place (t + 1) ⟨t, htn⟩ = 1 := place_self ⟨t, htn⟩
          rw [this, Nat.div_one]
        · rw [blockVal_eq_zero (Or.inl (by omega)), blockRange_eq_one (Or.inl (by omega)),
            Nat.mod_one]
      rw [e1, ih, e2, Nat.mul_comm (Ly.blockRange t₀ t), Nat.mod_mul]
      ring
    · rw [blockVal_eq_zero (Or.inr (by omega)), blockRange_eq_one (Or.inr (by omega)),
        Nat.mod_one]

/-- The digit of field `j` in the value of a block containing it. -/
theorem blockVal_digit {t₀ t₁ : ℕ} (x : Ly.Addr) (j : Fin Ly.n) (hj : t₀ ≤ j.val ∧ j.val < t₁) :
    Ly.blockVal t₀ t₁ x / Ly.place t₁ j % Ly.r j = (x j).val := by
  have hs1 := blockVal_split (show t₀ ≤ j.val + 1 by omega) (show j.val + 1 ≤ t₁ by omega) x
  have hs2 := blockVal_split (show t₀ ≤ j.val by omega) (Nat.le_succ j.val) x
  have hlt := blockVal_lt (j.val + 1) t₁ x
  have hsingle := blockVal_single j.isLt x
  have hrsingle := blockRange_single (Ly := Ly) j.isLt
  have hxj := (x j).isLt
  rw [place_eq_blockRange, hs1]
  rw [Nat.div_eq_of_lt_le (k := Ly.blockVal t₀ (j.val + 1) x) (by nlinarith) (by nlinarith)]
  rw [hs2, hsingle, hrsingle, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by simp)]

/-- Overwriting a block with its own value changes nothing. -/
theorem blockSet_blockVal (t₀ t₁ : ℕ) (x : Ly.Addr) :
    Ly.blockSet t₀ t₁ x (Ly.blockVal t₀ t₁ x) = x := by
  funext j
  by_cases hj : t₀ ≤ j.val ∧ j.val < t₁
  · exact Fin.ext (by rw [blockSet_apply_val _ _ _ hj, blockVal_digit x j hj])
  · exact blockSet_apply_of_not _ _ _ hj

/-- Two addresses with the same block value agree on every field of the block. -/
theorem apply_eq_of_blockVal_eq {t₀ t₁ : ℕ} {x y : Ly.Addr}
    (h : Ly.blockVal t₀ t₁ x = Ly.blockVal t₀ t₁ y) (j : Fin Ly.n)
    (hj : t₀ ≤ j.val ∧ j.val < t₁) : x j = y j :=
  Fin.ext (by rw [← blockVal_digit x j hj, ← blockVal_digit y j hj, h])

theorem blockVal_blockSet_of_disjoint {t₀ t₁ s₀ s₁ : ℕ} (h : t₁ ≤ s₀ ∨ s₁ ≤ t₀) (x : Ly.Addr)
    (v : ℕ) : Ly.blockVal s₀ s₁ (Ly.blockSet t₀ t₁ x v) = Ly.blockVal s₀ s₁ x :=
  blockVal_congr fun j hj₁ hj₂ => blockSet_apply_of_not x v j (by omega)

theorem blockSet_comm_of_disjoint {t₀ t₁ s₀ s₁ : ℕ} (h : t₁ ≤ s₀ ∨ s₁ ≤ t₀) (x : Ly.Addr)
    (v w : ℕ) :
    Ly.blockSet s₀ s₁ (Ly.blockSet t₀ t₁ x v) w = Ly.blockSet t₀ t₁ (Ly.blockSet s₀ s₁ x w) v := by
  funext j
  by_cases hj : t₀ ≤ j.val ∧ j.val < t₁
  · rw [blockSet_apply_of_not _ _ j (by omega)]
    exact Fin.ext (by rw [blockSet_apply_val _ _ _ hj, blockSet_apply_val _ _ _ hj])
  · by_cases hj' : s₀ ≤ j.val ∧ j.val < s₁
    · rw [blockSet_apply_of_not _ _ j hj]
      exact Fin.ext (by rw [blockSet_apply_val _ _ _ hj', blockSet_apply_val _ _ _ hj'])
    · rw [blockSet_apply_of_not _ _ j hj', blockSet_apply_of_not _ _ j hj,
        blockSet_apply_of_not _ _ j hj, blockSet_apply_of_not _ _ j hj']

/-- A block of binary fields inside the layout has range `2 ^ (t₁ − t₀)`. -/
theorem blockRange_binary {t₀ t₁ : ℕ} (h : t₀ ≤ t₁) (hn : t₁ ≤ Ly.n)
    (hr : ∀ i : Fin Ly.n, t₀ ≤ i.val → i.val < t₁ → Ly.r i = 2) :
    Ly.blockRange t₀ t₁ = 2 ^ (t₁ - t₀) := by
  obtain ⟨k, rfl⟩ : ∃ k, t₁ = t₀ + k := ⟨t₁ - t₀, by omega⟩
  induction k with
  | zero => rw [add_zero, blockRange_eq_one (Or.inr le_rfl), Nat.sub_self, pow_zero]
  | succ k ih =>
    rw [← add_assoc, blockRange_split (Nat.le_add_right t₀ k) (Nat.le_succ _),
      ih (by omega) (by omega) (fun i h1 h2 => hr i h1 (by omega)),
      blockRange_single (show t₀ + k < Ly.n by omega),
      hr ⟨t₀ + k, by omega⟩ (by simp) (by simp)]
    rw [show t₀ + k + 1 - t₀ = (t₀ + k - t₀) + 1 by omega, pow_succ]


/-! ### Chunks of binary fields -/

/-- A chunk of `L` binary fields at position `p`, inside the layout. -/
def ChunkOK (Ly : Layout) (L p : ℕ) : Prop :=
  p + L ≤ Ly.n ∧ ∀ i : Fin Ly.n, p ≤ i.val → i.val < p + L → Ly.r i = 2

theorem chunkRange {L p : ℕ} (h : ChunkOK Ly L p) : Ly.blockRange p (p + L) = 2 ^ L := by
  rw [blockRange_binary (Nat.le_add_right p L) h.1 h.2, Nat.add_sub_cancel_left]

theorem chunkVal_lt {L p : ℕ} (h : ChunkOK Ly L p) (a : Ly.Addr) : chunkVal L p a < 2 ^ L := by
  have := blockVal_lt p (p + L) a
  rwa [chunkRange h] at this

theorem chunkVal_blockSet {L p : ℕ} (h : ChunkOK Ly L p) (a : Ly.Addr) (v : ℕ) :
    chunkVal L p (Ly.blockSet p (p + L) a v) = v % 2 ^ L := by
  unfold chunkVal
  rw [blockVal_blockSet, chunkRange h]

theorem chunkVal_blockSet_of_lt {L p : ℕ} (h : ChunkOK Ly L p) (a : Ly.Addr) {v : ℕ}
    (hv : v < 2 ^ L) : chunkVal L p (Ly.blockSet p (p + L) a v) = v := by
  rw [chunkVal_blockSet h, Nat.mod_eq_of_lt hv]

/-- Bit `j` of a chunk is its field `p + L − 1 − j`. -/
theorem chunkBit_eq_field {L p j : ℕ} (h : ChunkOK Ly L p) (hj : j < L) (a : Ly.Addr) :
    chunkBit L p j a = (a ⟨p + L - 1 - j, by have := h.1; omega⟩).val := by
  unfold chunkBit
  rw [show p + L - j = (p + L - 1 - j) + 1 by omega, blockVal_single]

/-- Bit `j` of a chunk is bit `j` of its value. -/
theorem chunkBit_eq {L p j : ℕ} (h : ChunkOK Ly L p) (hj : j < L) (a : Ly.Addr) :
    chunkBit L p j a = bitAt (chunkVal L p a) j := by
  have hq : p + L - 1 - j < Ly.n := by have := h.1; omega
  rw [chunkBit_eq_field h hj]
  have hd := blockVal_digit a ⟨p + L - 1 - j, hq⟩
    (show p ≤ p + L - 1 - j ∧ p + L - 1 - j < p + L by omega)
  have hpl : Ly.place (p + L) ⟨p + L - 1 - j, hq⟩ = 2 ^ j := by
    rw [place_eq_blockRange]
    have e : (⟨p + L - 1 - j, hq⟩ : Fin Ly.n).val + 1 = p + L - j := by
      show p + L - 1 - j + 1 = p + L - j; omega
    rw [e, blockRange_binary (t₀ := p + L - j) (t₁ := p + L) (by omega) h.1
      (fun i h1 h2 => h.2 i (by omega) h2)]
    congr 1; omega
  have hr2 : Ly.r ⟨p + L - 1 - j, hq⟩ = 2 := h.2 _ (by show p ≤ p + L - 1 - j; omega)
    (by show p + L - 1 - j < p + L; omega)
  rw [hpl] at hd
  rw [← hd, hr2]
  rfl

/-- Two numbers below `2^L` with the same low `L` bits are equal. -/
theorem eq_of_bitAt_eq {L m m' : ℕ} (hm : m < 2 ^ L) (hm' : m' < 2 ^ L)
    (h : ∀ i < L, bitAt m i = bitAt m' i) : m = m' := by
  induction L generalizing m m' with
  | zero => simp at hm hm'; omega
  | succ L ih =>
    have h0 : m % 2 = m' % 2 := by
      have := h 0 (Nat.succ_pos L); simpa [bitAt] using this
    have hdiv : m / 2 = m' / 2 := by
      refine ih (by rw [pow_succ] at hm; omega) (by rw [pow_succ] at hm'; omega) fun i hi => ?_
      have := h (i + 1) (by omega)
      simp only [bitAt, pow_succ, ← Nat.div_div_eq_div_mul] at this ⊢
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm] at this
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      exact this
    omega

/-- Two addresses that agree outside the three chunks and on the three chunk values are equal. -/
theorem addr_ext3 {L px py pz : ℕ} {a b : Ly.Addr}
    (hout : ∀ j : Fin Ly.n, ¬ (px ≤ j.val ∧ j.val < px + L) → ¬ (py ≤ j.val ∧ j.val < py + L) →
      ¬ (pz ≤ j.val ∧ j.val < pz + L) → a j = b j)
    (hx : chunkVal L px a = chunkVal L px b) (hy : chunkVal L py a = chunkVal L py b)
    (hz : chunkVal L pz a = chunkVal L pz b) : a = b := by
  funext j
  by_cases h1 : px ≤ j.val ∧ j.val < px + L
  · exact apply_eq_of_blockVal_eq hx j h1
  by_cases h2 : py ≤ j.val ∧ j.val < py + L
  · exact apply_eq_of_blockVal_eq hy j h2
  by_cases h3 : pz ≤ j.val ∧ j.val < pz + L
  · exact apply_eq_of_blockVal_eq hz j h3
  exact hout j h1 h2 h3

end Blocks

/-! ## Address-moving steps and runs restricted to a row class -/

section Pulls

variable {Ly : Layout} {β : Type}

/-- The pull of `swapBlocks t₀ s₀ len` (interchange of the blocks `[t₀, t₀+len)`, `[s₀, s₀+len)`). -/
def swapPull (Ly : Layout) (t₀ s₀ len : ℕ) (x : Ly.Addr) : Ly.Addr :=
  Ly.blockSet s₀ (s₀ + len) (Ly.blockSet t₀ (t₀ + len) x (Ly.blockVal s₀ (s₀ + len) x))
    (Ly.blockVal t₀ (t₀ + len) x)

/-- The address map of an address-moving step: `s.run A = A ∘ stepPull s` (`run_eq_comp`). -/
def stepPull : Step Ly β → Ly.Addr → Ly.Addr
  | .elem e => e.pull
  | .sparsePerm pull _ => pull
  | .swapBlocks t₀ s₀ len => swapPull Ly t₀ s₀ len
  | .recMap _ => id
  | .addrMap _ => id
  | .digitGate _ _ => id

/-- Address-moving steps. -/
def IsMove : Step Ly β → Prop
  | .elem _ => True
  | .sparsePerm _ _ => True
  | .swapBlocks _ _ _ => True
  | .recMap _ => False
  | .addrMap _ => False
  | .digitGate _ _ => False

theorem run_eq_comp (s : Step Ly β) (hs : IsMove s) (A : Ly.Addr → β) :
    s.run A = A ∘ stepPull s := by
  cases s with
  | elem e => rfl
  | sparsePerm pull supp => rfl
  | swapBlocks t₀ s₀ len => rfl
  | recMap f => exact hs.elim
  | addrMap f => exact hs.elim
  | digitGate i G => exact hs.elim

/-- Composite pull of a step list (the first step's pull is applied last). -/
def pullComp : List (Step Ly β) → Ly.Addr → Ly.Addr
  | [] => id
  | s :: p => stepPull s ∘ pullComp p

theorem pullComp_nil : pullComp ([] : List (Step Ly β)) = id := rfl

theorem pullComp_cons (s : Step Ly β) (p : List (Step Ly β)) :
    pullComp (s :: p) = stepPull s ∘ pullComp p := rfl

theorem pullComp_append (p q : List (Step Ly β)) :
    pullComp (p ++ q) = pullComp p ∘ pullComp q := by
  induction p with
  | nil => rfl
  | cons s p ih => rw [List.cons_append, pullComp_cons, pullComp_cons, ih]; rfl

theorem pullComp_row (c : RowClass Ly) (p : List (Step Ly β))
    (hp : ∀ s ∈ p, ∀ x, stepPull s x c.row = x c.row) (a : Ly.Addr) :
    pullComp p a c.row = a c.row := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    rw [pullComp_cons, Function.comp_apply, hp s (by simp),
      ih (fun s' hs' => hp s' (by simp [hs']))]

/-- **Runs of address-moving steps in a class**: if every pull fixes the row field, the run of the
list in class `c` reads `A` at the composite pull on `c` and is the identity elsewhere. -/
theorem foldl_runIn (c : RowClass Ly) (p : List (Step Ly β))
    (hp : ∀ s ∈ p, IsMove s ∧ ∀ x, stepPull s x c.row = x c.row) (A : Ly.Addr → β) :
    List.foldl (fun A s => Step.runIn c s A) A p =
      fun a => if c.mem a then A (pullComp p a) else A a := by
  induction p generalizing A with
  | nil =>
    funext a
    by_cases ha : c.mem a
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]; rfl
  | cons s p ih =>
    rw [List.foldl_cons, ih (fun s' hs' => hp s' (by simp [hs']))]
    funext a
    have hs := hp s (by simp)
    by_cases ha : c.mem a
    · have hrow := pullComp_row c p (fun s' hs' => (hp s' (by simp [hs'])).2) a
      have hmem : c.mem (pullComp p a) := by
        unfold RowClass.mem at ha ⊢
        rw [hrow]
        exact ha
      rw [if_pos ha, if_pos ha]
      show (if c.mem (pullComp p a) then s.run A (pullComp p a) else A (pullComp p a)) = _
      rw [if_pos hmem, run_eq_comp s hs.1]
      rfl
    · rw [if_neg ha, if_neg ha]
      show (if c.mem a then s.run A a else A a) = A a
      rw [if_neg ha]

/-! ### Effects of interchanges and shifts on chunks -/

variable {L : ℕ}

theorem swapPull_apply_of_not {pt pr : ℕ} (x : Ly.Addr) (j : Fin Ly.n)
    (h1 : ¬ (pt ≤ j.val ∧ j.val < pt + L)) (h2 : ¬ (pr ≤ j.val ∧ j.val < pr + L)) :
    swapPull Ly pt pr L x j = x j := by
  unfold swapPull
  rw [blockSet_apply_of_not _ _ j h2, blockSet_apply_of_not _ _ j h1]

theorem swap_chunk_right {pt pr : ℕ} (ht : ChunkOK Ly L pt) (hr : ChunkOK Ly L pr)
    (x : Ly.Addr) : chunkVal L pr (swapPull Ly pt pr L x) = chunkVal L pt x :=
  chunkVal_blockSet_of_lt hr _ (chunkVal_lt ht x)

theorem swap_chunk_left {pt pr : ℕ} (ht : ChunkOK Ly L pt) (hr : ChunkOK Ly L pr)
    (hd : pt + L ≤ pr ∨ pr + L ≤ pt) (x : Ly.Addr) :
    chunkVal L pt (swapPull Ly pt pr L x) = chunkVal L pr x := by
  unfold swapPull chunkVal
  rw [blockVal_blockSet_of_disjoint (by omega : pr + L ≤ pt ∨ pt + L ≤ pr)]
  exact chunkVal_blockSet_of_lt ht _ (chunkVal_lt hr x)

theorem swap_chunk_other {pt pr p : ℕ} (h1 : p + L ≤ pt ∨ pt + L ≤ p)
    (h2 : p + L ≤ pr ∨ pr + L ≤ p) (x : Ly.Addr) :
    chunkVal L p (swapPull Ly pt pr L x) = chunkVal L p x := by
  unfold swapPull chunkVal
  rw [blockVal_blockSet_of_disjoint (by omega), blockVal_blockSet_of_disjoint (by omega)]

theorem shift_pull_eq (t₀ t₁ : ℕ) (off : Ly.Addr → ℕ) (x : Ly.Addr) :
    (Elem.shift t₀ t₁ off : Elem Ly).pull x =
      Ly.blockSet t₀ t₁ x ((Ly.blockVal t₀ t₁ x + Ly.blockRange t₀ t₁ -
        off x % Ly.blockRange t₀ t₁) % Ly.blockRange t₀ t₁) := rfl

theorem shift_chunk_self {p : ℕ} (h : ChunkOK Ly L p) (off : Ly.Addr → ℕ) (x : Ly.Addr) :
    chunkVal L p ((Elem.shift p (p + L) off : Elem Ly).pull x) =
      (chunkVal L p x + 2 ^ L - off x % 2 ^ L) % 2 ^ L := by
  rw [shift_pull_eq, chunkRange h, chunkVal_blockSet h, Nat.mod_mod]
  rfl

theorem shift_chunk_other {p q : ℕ} (hd : p + L ≤ q ∨ q + L ≤ p) (off : Ly.Addr → ℕ)
    (x : Ly.Addr) : chunkVal L q ((Elem.shift p (p + L) off : Elem Ly).pull x) = chunkVal L q x := by
  rw [shift_pull_eq]
  exact blockVal_blockSet_of_disjoint (by omega) x _

theorem shift_apply_of_not {t₀ t₁ : ℕ} (off : Ly.Addr → ℕ) (x : Ly.Addr) (j : Fin Ly.n)
    (hj : ¬ (t₀ ≤ j.val ∧ j.val < t₁)) : (Elem.shift t₀ t₁ off : Elem Ly).pull x j = x j := by
  rw [shift_pull_eq]
  exact blockSet_apply_of_not _ _ j hj

end Pulls

end PackedProcAux

end SubNLogN.Math.Networks
