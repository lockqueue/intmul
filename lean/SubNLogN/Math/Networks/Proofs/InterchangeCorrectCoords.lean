import SubNLogN.Math.Networks.Proofs.InterchangeCorrectRadix

/-!
# Proposition A.7 (`prop:transfer11`) correctness, part B1: chunk coordinates

A *chunk* at field `t₀` is `mH` consecutive blocks `blk t₀ b i` of `b` radix-`q` fields; its
coordinates are the block values in `ZMod (q^b)` (`coords`), written back by `setCoords`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-- A chunk of `mH` coordinate blocks of `b ≥ 1` radix-`q` fields starting at `t₀`, inside `L`. -/
structure ChunkOK (L : Layout) (q t₀ b : ℕ) : Prop where
  hb : 0 < b
  fits : t₀ + mH * b ≤ L.n
  radix : ∀ j : Fin L.n, t₀ ≤ j.val → j.val < t₀ + mH * b → L.r j = q

/-- The two chunks of the Proposition A.7 (`prop:transfer11`) recursion: `H` at `h₀` strictly before `D` at `d₀`. -/
structure TwoChunks (L : Layout) (q h₀ d₀ b : ℕ) : Prop where
  H : ChunkOK L q h₀ b
  D : ChunkOK L q d₀ b
  HD : h₀ + mH * b ≤ d₀

/-- Coordinate `i` (the block `blk t₀ b i`) of the chunk at `t₀`, in `ZMod Q`. -/
def coords (L : Layout) (Q t₀ b : ℕ) (x : L.Addr) (i : Fin mH) : ZMod Q :=
  ((L.blockVal (blk t₀ b i).1 (blk t₀ b i).2 x : ℕ) : ZMod Q)

theorem cidx_lt {t₀ b j : ℕ} (h : t₀ ≤ j ∧ j < t₀ + mH * b) : (j - t₀) / b < mH := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; omega
  · exact (Nat.div_lt_iff_lt_mul hb).2 (by omega)

/-- Overwrite every coordinate of the chunk at `t₀`: block `i` receives the digits of `(X i).val`. -/
def setCoords (L : Layout) (Q t₀ b : ℕ) (x : L.Addr) (X : Fin mH → ZMod Q) : L.Addr := fun j =>
  if h : t₀ ≤ j.val ∧ j.val < t₀ + mH * b then
    L.blockSet (blk t₀ b ⟨(j.val - t₀) / b, cidx_lt h⟩).1 (blk t₀ b ⟨(j.val - t₀) / b, cidx_lt h⟩).2
      x (X ⟨(j.val - t₀) / b, cidx_lt h⟩).val j
  else x j

theorem setCoords_of_not {Q t₀ b : ℕ} (x : L.Addr) (X : Fin mH → ZMod Q) (j : Fin L.n)
    (hj : ¬ (t₀ ≤ j.val ∧ j.val < t₀ + mH * b)) : setCoords L Q t₀ b x X j = x j := by
  simp only [setCoords, dif_neg hj]

/-! ### Helpers (sub-namespace `CoordsAux`) -/

namespace CoordsAux

lemma blk_eq (t₀ b : ℕ) (i : Fin mH) : blk t₀ b i = (t₀ + i.val * b, t₀ + i.val * b + b) := by
  simp only [blk, Prod.mk.injEq, true_and]
  ring

/-- The block of coordinate `i` lies inside the chunk. -/
lemma blk_le_chunk (t₀ b : ℕ) (i : Fin mH) : t₀ + i.val * b + b ≤ t₀ + mH * b := by
  have h : (i.val + 1) * b ≤ mH * b := Nat.mul_le_mul_right b i.isLt
  rw [add_one_mul] at h
  omega

/-- A field of the chunk lies in the block of its coordinate index. -/
lemma cidx_mem {t₀ b j : ℕ} (h : t₀ ≤ j ∧ j < t₀ + mH * b) :
    t₀ + (j - t₀) / b * b ≤ j ∧ j < t₀ + (j - t₀) / b * b + b := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; omega
    · exact hb
  have h1 := Nat.div_mul_le_self (j - t₀) b
  have h2 := Nat.lt_div_mul_add (a := j - t₀) hb
  omega

/-- The coordinate index of a field of block `i` is `i`. -/
lemma cidx_eq {t₀ b j : ℕ} (i : Fin mH) (h1 : t₀ + i.val * b ≤ j) (h2 : j < t₀ + i.val * b + b) :
    (j - t₀) / b = i.val := by
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [add_one_mul]; omega

lemma exists_blk {t₀ b : ℕ} {j : Fin L.n} (h : t₀ ≤ j.val ∧ j.val < t₀ + mH * b) :
    ∃ i : Fin mH, t₀ + i.val * b ≤ j.val ∧ j.val < t₀ + i.val * b + b :=
  ⟨⟨(j.val - t₀) / b, cidx_lt h⟩, cidx_mem h⟩

lemma setCoords_apply_of_mem {Q t₀ b : ℕ} (x : L.Addr) (X : Fin mH → ZMod Q) (j : Fin L.n)
    (i : Fin mH) (h1 : t₀ + i.val * b ≤ j.val) (h2 : j.val < t₀ + i.val * b + b) :
    setCoords L Q t₀ b x X j = L.blockSet (blk t₀ b i).1 (blk t₀ b i).2 x (X i).val j := by
  have hin : t₀ ≤ j.val ∧ j.val < t₀ + mH * b :=
    ⟨by omega, lt_of_lt_of_le h2 (blk_le_chunk t₀ b i)⟩
  have hci : ∀ p, (⟨(j.val - t₀) / b, p⟩ : Fin mH) = i := fun _ => Fin.ext (cidx_eq i h1 h2)
  simp only [setCoords, dif_pos hin, hci]

lemma blockSet_blk_apply_base {t₀ b : ℕ} (i : Fin mH) (x y : L.Addr) (v : ℕ) (j : Fin L.n)
    (h1 : t₀ + i.val * b ≤ j.val) (h2 : j.val < t₀ + i.val * b + b) :
    L.blockSet (blk t₀ b i).1 (blk t₀ b i).2 x v j = L.blockSet (blk t₀ b i).1 (blk t₀ b i).2 y v j := by
  have hin : inBlock (blk t₀ b i).1 (blk t₀ b i).2 j := by
    rw [blk_eq]; exact ⟨h1, h2⟩
  simp only [Layout.blockSet, if_pos hin]

/-- On the chunk, `setCoords` does not depend on the base address. -/
lemma setCoords_base {Q t₀ b : ℕ} (x y : L.Addr) (X : Fin mH → ZMod Q) (j : Fin L.n)
    (h : t₀ ≤ j.val ∧ j.val < t₀ + mH * b) :
    setCoords L Q t₀ b x X j = setCoords L Q t₀ b y X j := by
  obtain ⟨i, h1, h2⟩ := exists_blk h
  rw [setCoords_apply_of_mem x X j i h1 h2, setCoords_apply_of_mem y X j i h1 h2]
  exact blockSet_blk_apply_base i x y _ j h1 h2

lemma setCoords_congr_out {Q t₀ b : ℕ} {y z : L.Addr} (X : Fin mH → ZMod Q)
    (hout : ∀ j : Fin L.n, ¬ (t₀ ≤ j.val ∧ j.val < t₀ + mH * b) → y j = z j) :
    setCoords L Q t₀ b y X = setCoords L Q t₀ b z X := by
  funext j
  by_cases h : t₀ ≤ j.val ∧ j.val < t₀ + mH * b
  · exact setCoords_base y z X j h
  · rw [setCoords_of_not y X j h, setCoords_of_not z X j h, hout j h]

/-- The radix `q` is positive as soon as the chunk has an address. -/
lemma q_pos {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (x : L.Addr) : 0 < q := by
  have hmb : 0 < mH * b := Nat.mul_pos (by norm_num [mH]) hC.hb
  have hlt : t₀ < L.n := by have := hC.fits; omega
  have hr := hC.radix ⟨t₀, hlt⟩ (le_refl _) (by simp only; omega)
  have := Fin.pos (x ⟨t₀, hlt⟩)
  omega

/-- Helper form of `blockRange_blk` (usable before it). -/
lemma blockRange_blk_aux {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (i : Fin mH) :
    L.blockRange (blk t₀ b i).1 (blk t₀ b i).2 = q ^ b := by
  have hle := blk_le_chunk t₀ b i
  have hfits := hC.fits
  rw [blk_eq]
  simp only
  rw [blockRange_eq_pow (by omega) (by omega) (fun j hj₁ hj₂ => hC.radix j (by omega) (by omega)),
    Nat.add_sub_cancel_left]

end CoordsAux

open CoordsAux

theorem setCoords_setCoords {Q t₀ b : ℕ} (x : L.Addr) (X Y : Fin mH → ZMod Q) :
    setCoords L Q t₀ b (setCoords L Q t₀ b x X) Y = setCoords L Q t₀ b x Y := by
  funext j
  by_cases h : t₀ ≤ j.val ∧ j.val < t₀ + mH * b
  · exact setCoords_base _ x Y j h
  · rw [setCoords_of_not _ Y j h, setCoords_of_not x X j h, setCoords_of_not x Y j h]

theorem coords_congr {Q t₀ b : ℕ} {y z : L.Addr}
    (h : ∀ j : Fin L.n, t₀ ≤ j.val → j.val < t₀ + mH * b → y j = z j) :
    coords L Q t₀ b y = coords L Q t₀ b z := by
  funext i
  have hle := blk_le_chunk t₀ b i
  simp only [coords]
  rw [blockVal_congr (fun j hj₁ hj₂ => h j (by rw [blk_eq] at hj₁; simp only at hj₁; omega)
    (by rw [blk_eq] at hj₂; simp only at hj₂; omega))]

theorem coords_setCoords {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (x : L.Addr) (X : Fin mH → ZMod (q ^ b)) :
    coords L (q ^ b) t₀ b (setCoords L (q ^ b) t₀ b x X) = X := by
  have hq := q_pos hC x
  have : NeZero (q ^ b) := ⟨(pow_pos hq b).ne'⟩
  funext i
  simp only [coords]
  rw [blockVal_congr (y := L.blockSet (blk t₀ b i).1 (blk t₀ b i).2 x (X i).val)
    (fun j hj₁ hj₂ => by
      rw [blk_eq] at hj₁ hj₂
      exact setCoords_apply_of_mem x X j i hj₁ hj₂),
    blockVal_blockSet, blockRange_blk_aux hC, ZMod.natCast_mod, ZMod.natCast_zmod_val]

theorem setCoords_coords {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (x : L.Addr) :
    setCoords L (q ^ b) t₀ b x (coords L (q ^ b) t₀ b x) = x := by
  funext j
  by_cases h : t₀ ≤ j.val ∧ j.val < t₀ + mH * b
  · obtain ⟨i, h1, h2⟩ := exists_blk h
    rw [setCoords_apply_of_mem x _ j i h1 h2]
    simp only [coords]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (blockRange_blk_aux hC i ▸ blockVal_lt _ _ x),
      blockSet_blockVal]
  · exact setCoords_of_not x _ j h

/-- Addresses agreeing off the chunk and on its coordinates are equal. -/
theorem eq_of_coords {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) {y z : L.Addr}
    (hout : ∀ j : Fin L.n, ¬ (t₀ ≤ j.val ∧ j.val < t₀ + mH * b) → y j = z j)
    (hc : coords L (q ^ b) t₀ b y = coords L (q ^ b) t₀ b z) : y = z :=
  calc y = setCoords L (q ^ b) t₀ b y (coords L (q ^ b) t₀ b y) := (setCoords_coords hC y).symm
    _ = setCoords L (q ^ b) t₀ b y (coords L (q ^ b) t₀ b z) := by rw [hc]
    _ = setCoords L (q ^ b) t₀ b z (coords L (q ^ b) t₀ b z) := setCoords_congr_out _ hout
    _ = z := setCoords_coords hC z

/-- Overwriting one coordinate block is a coordinate update. -/
theorem blockSet_blk {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (x : L.Addr) (i : Fin mH) (v : ℕ) :
    L.blockSet (blk t₀ b i).1 (blk t₀ b i).2 x v =
      setCoords L (q ^ b) t₀ b x (Function.update (coords L (q ^ b) t₀ b x) i (v : ZMod (q ^ b))) := by
  funext j
  by_cases h : t₀ ≤ j.val ∧ j.val < t₀ + mH * b
  · obtain ⟨i', h1, h2⟩ := exists_blk h
    rw [setCoords_apply_of_mem x _ j i' h1 h2]
    by_cases hii : i' = i
    · subst hii
      rw [Function.update_self, ZMod.val_natCast, ← blockRange_blk_aux hC i', blockSet_mod]
    · rw [Function.update_of_ne hii]
      have hnot : ¬ ((blk t₀ b i).1 ≤ j.val ∧ j.val < (blk t₀ b i).2) := by
        rw [blk_eq]
        rintro ⟨h3, h4⟩
        exact hii (Fin.ext ((cidx_eq i' h1 h2).symm.trans (cidx_eq i h3 h4)))
      rw [blockSet_apply_of_not x v j hnot]
      simp only [coords]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (blockRange_blk_aux hC i' ▸ blockVal_lt _ _ x),
        blockSet_blockVal]
  · have hnot : ¬ ((blk t₀ b i).1 ≤ j.val ∧ j.val < (blk t₀ b i).2) := by
      rw [blk_eq]
      have := blk_le_chunk t₀ b i
      rintro ⟨h3, h4⟩
      exact h ⟨by omega, by omega⟩
    rw [setCoords_of_not x _ j h, blockSet_apply_of_not x v j hnot]

theorem blockRange_blk {q t₀ b : ℕ} (hC : ChunkOK L q t₀ b) (i : Fin mH) :
    L.blockRange (blk t₀ b i).1 (blk t₀ b i).2 = q ^ b :=
  blockRange_blk_aux hC i

/-! ### Two chunks -/

theorem coords_setCoords_H {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (X : Fin mH → ZMod (q ^ b)) :
    coords L (q ^ b) d₀ b (setCoords L (q ^ b) h₀ b x X) = coords L (q ^ b) d₀ b x := by
  have hHD := hT.HD
  exact coords_congr fun j hj₁ _ => setCoords_of_not x X j (by omega)

theorem coords_setCoords_D {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (X : Fin mH → ZMod (q ^ b)) :
    coords L (q ^ b) h₀ b (setCoords L (q ^ b) d₀ b x X) = coords L (q ^ b) h₀ b x := by
  have hHD := hT.HD
  exact coords_congr fun j _ hj₂ => setCoords_of_not x X j (by omega)

theorem setCoords_comm {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (X Y : Fin mH → ZMod (q ^ b)) :
    setCoords L (q ^ b) d₀ b (setCoords L (q ^ b) h₀ b x X) Y =
      setCoords L (q ^ b) h₀ b (setCoords L (q ^ b) d₀ b x Y) X := by
  have hHD := hT.HD
  funext j
  by_cases hD : d₀ ≤ j.val ∧ j.val < d₀ + mH * b
  · have hH : ¬ (h₀ ≤ j.val ∧ j.val < h₀ + mH * b) := by omega
    rw [setCoords_of_not _ X j hH]
    exact setCoords_base _ x Y j hD
  · rw [setCoords_of_not _ Y j hD]
    by_cases hH : h₀ ≤ j.val ∧ j.val < h₀ + mH * b
    · exact setCoords_base x _ X j hH
    · rw [setCoords_of_not x X j hH, setCoords_of_not _ X j hH, setCoords_of_not x Y j hD]

/-- A row class whose row field precedes the chunk is preserved by `setCoords`. -/
theorem mem_setCoords {Q t₀ b : ℕ} (c : RowClass L) (hc : c.row.val < t₀) (x : L.Addr)
    (X : Fin mH → ZMod Q) : c.mem (setCoords L Q t₀ b x X) ↔ c.mem x := by
  unfold RowClass.mem
  rw [setCoords_of_not x X c.row (by omega)]

end InterchangeCorrect

end SubNLogN.Math.Networks
