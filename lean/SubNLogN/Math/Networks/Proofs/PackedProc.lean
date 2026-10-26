import SubNLogN.Math.Networks.Proofs.PackedProcLib
import SubNLogN.Math.Networks.Proofs.PackedProcBits

/-!
# Lemma A.9 (`lem:transfer13`): correctness of the packed selected-bit addition (`PackedProcCorrectStmt`)

`packedAddProc L K ρ f C` (`AppCPacked.lean`, Lemma A.9 (`lem:transfer13`)) uses only
address-moving steps. With the shared library `Proofs/PackedProcLib.lean`:
* the run in a row class `c` whose row field lies outside the three chunks is
  `a ↦ if a ∈ c then A (pullComp p a) else A a` (`foldl_runIn`);
* the pull of each packed line inverts its forward map, which acts on the chunk values as
  `packedLine` (`line_pull_fwd`); so the pull of the eight lines is a left inverse of `addrS0`
  (`pull_lines_addrS0`), and the repair pull `addrS0 ∘ addrT0` leaves `addrT0`;
* the top-bit steps flip `y_j` iff `x_j = 1` (`j = ρ + (f−1)K`), and `addrT0` after this flip is
  `addrXorAll` (`Proofs/PackedProcBits.lean`).
The hypotheses `RunEightSpecStmt` and `PackedAgreeStmt` are not needed for correctness (they are used
for well-formedness of the repair step).
-/

namespace SubNLogN.Math.Networks

open Model

namespace PackedProcAux

section Lines

variable {Ly : Layout} {β : Type} {L K ρ f : ℕ} {C : Chunks3}

/-- Membership in the three chunk positions. -/
def Mem3 (C : Chunks3) (p : ℕ) : Prop := p = C.px ∨ p = C.py ∨ p = C.pz

/-- The chunk geometry of `PackedHyps`. -/
structure Geo (Ly : Layout) (L : ℕ) (C : Chunks3) : Prop where
  hx : ChunkOK Ly L C.px
  hy : ChunkOK Ly L C.py
  hz : ChunkOK Ly L C.pz
  dxy : C.px + L ≤ C.py ∨ C.py + L ≤ C.px
  dxz : C.px + L ≤ C.pz ∨ C.pz + L ≤ C.px
  dyz : C.py + L ≤ C.pz ∨ C.pz + L ≤ C.py
  pos : 0 < L

theorem geo_of_hyps (h : PackedHyps Ly L K ρ f C) : Geo Ly L C := by
  obtain ⟨hK, hL, _, hf, hxn, hyn, hzn, dxy, dxz, dyz, hbin⟩ := h
  refine ⟨⟨hxn, fun i h1 h2 => hbin i (Or.inl ⟨h1, h2⟩)⟩,
    ⟨hyn, fun i h1 h2 => hbin i (Or.inr (Or.inl ⟨h1, h2⟩))⟩,
    ⟨hzn, fun i h1 h2 => hbin i (Or.inr (Or.inr ⟨h1, h2⟩))⟩, dxy, dxz, dyz, ?_⟩
  rw [hL]
  exact Nat.mul_pos (by omega) (by omega)

theorem Geo.chunk (G : Geo Ly L C) {p : ℕ} (hp : Mem3 C p) : ChunkOK Ly L p := by
  rcases hp with rfl | rfl | rfl
  exacts [G.hx, G.hy, G.hz]

theorem Geo.disj (G : Geo Ly L C) {p q : ℕ} (hp : Mem3 C p) (hq : Mem3 C q) (hne : p ≠ q) :
    p + L ≤ q ∨ q + L ≤ p := by
  have := G.dxy; have := G.dxz; have := G.dyz
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | omega

theorem Geo.ne_xy (G : Geo Ly L C) : C.px ≠ C.py := by have := G.dxy; have := G.pos; omega
theorem Geo.ne_xz (G : Geo Ly L C) : C.px ≠ C.pz := by have := G.dxz; have := G.pos; omega
theorem Geo.ne_yz (G : Geo Ly L C) : C.py ≠ C.pz := by have := G.dyz; have := G.pos; omega

theorem mem3_x (C : Chunks3) : Mem3 C C.px := Or.inl rfl
theorem mem3_y (C : Chunks3) : Mem3 C C.py := Or.inr (Or.inl rfl)
theorem mem3_z (C : Chunks3) : Mem3 C C.pz := Or.inr (Or.inr rfl)

theorem mem3_right (C : Chunks3) : Mem3 C C.right := by
  unfold Chunks3.right Mem3
  rcases le_total C.py C.pz with h | h
  · rw [max_eq_right h]
    rcases le_total C.px C.pz with h' | h'
    · rw [max_eq_right h']; exact Or.inr (Or.inr rfl)
    · rw [max_eq_left h']; exact Or.inl rfl
  · rw [max_eq_left h]
    rcases le_total C.px C.py with h' | h'
    · rw [max_eq_right h']; exact Or.inr (Or.inl rfl)
    · rw [max_eq_left h']; exact Or.inl rfl

/-- A field outside the three chunks. -/
def Out3 (L : ℕ) (C : Chunks3) (j : ℕ) : Prop :=
  ¬ (C.px ≤ j ∧ j < C.px + L) ∧ ¬ (C.py ≤ j ∧ j < C.py + L) ∧ ¬ (C.pz ≤ j ∧ j < C.pz + L)

theorem out3_not_mem {j p : ℕ} (hj : Out3 L C j) (hp : Mem3 C p) : ¬ (p ≤ j ∧ j < p + L) := by
  rcases hp with rfl | rfl | rfl
  exacts [hj.1, hj.2.1, hj.2.2]

/-! ### `movedPos` -/

theorem movedPos_right (pt pr : ℕ) : movedPos pt pr pr = pt := by
  unfold movedPos; rw [if_pos rfl]

theorem movedPos_left {pt pr : ℕ} (h : pt ≠ pr) : movedPos pt pr pt = pr := by
  unfold movedPos; rw [if_neg h, if_pos rfl]

theorem movedPos_other {pt pr p : ℕ} (h1 : p ≠ pr) (h2 : p ≠ pt) : movedPos pt pr p = p := by
  unfold movedPos; rw [if_neg h1, if_neg h2]

theorem movedPos_self (pt p : ℕ) : movedPos pt pt p = p := by
  unfold movedPos; split_ifs <;> omega

theorem movedPos_invol (pt pr p : ℕ) : movedPos pt pr (movedPos pt pr p) = p := by
  unfold movedPos; split_ifs <;> omega

theorem movedPos_eq_right_iff (pt pr p : ℕ) : movedPos pt pr p = pr ↔ p = pt := by
  unfold movedPos; split_ifs <;> omega

theorem movedPos_mem {pt pr p : ℕ} (ht : Mem3 C pt) (hr : Mem3 C pr) (hp : Mem3 C p) :
    Mem3 C (movedPos pt pr p) := by
  unfold movedPos; split_ifs <;> assumption

/-! ### The optional interchange `σ` -/

/-- Pull of the optional interchange of the chunks at `pt` and `pr` (none if `pt = pr`). -/
def sigmaPull (Ly : Layout) (L pt pr : ℕ) (x : Ly.Addr) : Ly.Addr :=
  if pt = pr then x else swapPull Ly pt pr L x

theorem pullComp_swp (pt pr : ℕ) :
    pullComp (if pt = pr then ([] : List (Step Ly β)) else [.swapBlocks pt pr L]) =
      sigmaPull Ly L pt pr := by
  funext x
  unfold sigmaPull
  split_ifs <;> rfl

theorem sigma_chunk (G : Geo Ly L C) {pt pr p : ℕ} (ht : Mem3 C pt) (hr : Mem3 C pr)
    (hp : Mem3 C p) (x : Ly.Addr) :
    chunkVal L p (sigmaPull Ly L pt pr x) = chunkVal L (movedPos pt pr p) x := by
  unfold sigmaPull
  by_cases htr : pt = pr
  · rw [if_pos htr, htr, movedPos_self]
  · rw [if_neg htr]
    by_cases hpr : p = pr
    · rw [hpr, movedPos_right]
      exact swap_chunk_right (G.chunk ht) (G.chunk hr) x
    · by_cases hpt : p = pt
      · rw [hpt, movedPos_left htr]
        exact swap_chunk_left (G.chunk ht) (G.chunk hr) (G.disj ht hr htr) x
      · rw [movedPos_other hpr hpt]
        exact swap_chunk_other (G.disj hp ht hpt) (G.disj hp hr hpr) x

theorem sigma_apply_out {pt pr : ℕ} (ht : Mem3 C pt) (hr : Mem3 C pr) (x : Ly.Addr)
    (j : Fin Ly.n) (hj : Out3 L C j.val) : sigmaPull Ly L pt pr x j = x j := by
  unfold sigmaPull
  split_ifs
  · rfl
  · exact swapPull_apply_of_not x j (out3_not_mem hj ht) (out3_not_mem hj hr)

/-! ### Setting chunk values; the forward map of a packed line -/

/-- Overwrite the three chunk values. -/
def setChunks (L : ℕ) (C : Chunks3) (b : Ly.Addr) (v : ℕ × ℕ × ℕ) : Ly.Addr :=
  Ly.blockSet C.pz (C.pz + L)
    (Ly.blockSet C.py (C.py + L) (Ly.blockSet C.px (C.px + L) b v.1) v.2.1) v.2.2

theorem setChunks_x (G : Geo Ly L C) (b : Ly.Addr) (v : ℕ × ℕ × ℕ) :
    chunkVal L C.px (setChunks L C b v) = v.1 % 2 ^ L := by
  have h1 := G.dxz; have h2 := G.dxy
  unfold setChunks chunkVal
  rw [blockVal_blockSet_of_disjoint (by omega), blockVal_blockSet_of_disjoint (by omega)]
  exact chunkVal_blockSet G.hx b v.1

theorem setChunks_y (G : Geo Ly L C) (b : Ly.Addr) (v : ℕ × ℕ × ℕ) :
    chunkVal L C.py (setChunks L C b v) = v.2.1 % 2 ^ L := by
  have h1 := G.dyz
  unfold setChunks chunkVal
  rw [blockVal_blockSet_of_disjoint (by omega)]
  exact chunkVal_blockSet G.hy _ v.2.1

theorem setChunks_z (G : Geo Ly L C) (b : Ly.Addr) (v : ℕ × ℕ × ℕ) :
    chunkVal L C.pz (setChunks L C b v) = v.2.2 % 2 ^ L :=
  chunkVal_blockSet G.hz _ v.2.2

theorem setChunks_apply_out (b : Ly.Addr) (v : ℕ × ℕ × ℕ) (j : Fin Ly.n) (hj : Out3 L C j.val) :
    setChunks L C b v j = b j := by
  unfold setChunks
  rw [blockSet_apply_of_not _ _ j hj.2.2, blockSet_apply_of_not _ _ j hj.2.1,
    blockSet_apply_of_not _ _ j hj.1]

/-- The forward map of one packed line on addresses (`packedLine` on the chunk values). -/
def lineFwd (L K ρ f : ℕ) (C : Chunks3) (op : Bool × ℤ × ℕ) (b : Ly.Addr) : Ly.Addr :=
  setChunks L C b (packedLine L K ρ f op (chunkVals L C b))

/-- Target and other chunk of a line. -/
def tgtPos (C : Chunks3) (op : Bool × ℤ × ℕ) : ℕ := if op.1 then C.py else C.pz

/-- The offset of the shift of a packed line (as in `lineSteps`). -/
def lineOff (Ly : Layout) (L K ρ f : ℕ) (C : Chunks3) (op : Bool × ℤ × ℕ) (a : Ly.Addr) : ℕ :=
  let s := ∑ i ∈ Finset.range (f - 1), 2 ^ (ρ + i * K) *
    (if chunkBit L (movedPos (tgtPos C op) C.right C.px) (ρ + i * K) a = 1 ∧
        chunkBit L (movedPos (tgtPos C op) C.right (if op.1 then C.pz else C.py)) (ρ + i * K) a =
          op.2.2 then 1 else 0)
  if op.2.1 = 1 then s % 2 ^ L else (2 ^ L - s % 2 ^ L) % 2 ^ L

theorem lineSteps_eq (op : Bool × ℤ × ℕ) :
    lineSteps (Ly := Ly) (β := β) L K ρ f C op =
      (if tgtPos C op = C.right then [] else [.swapBlocks (tgtPos C op) C.right L]) ++
        [.elem (.shift C.right (C.right + L) (lineOff Ly L K ρ f C op))] ++
        (if tgtPos C op = C.right then [] else [.swapBlocks (tgtPos C op) C.right L]) := rfl

theorem pullComp_line (op : Bool × ℤ × ℕ) (a : Ly.Addr) :
    pullComp (lineSteps (Ly := Ly) (β := β) L K ρ f C op) a =
      sigmaPull Ly L (tgtPos C op) C.right
        ((Elem.shift C.right (C.right + L) (lineOff Ly L K ρ f C op) : Elem Ly).pull
          (sigmaPull Ly L (tgtPos C op) C.right a)) := by
  rw [lineSteps_eq, pullComp_append, pullComp_append, pullComp_swp]
  rfl

theorem toNat_emod_lt (z : ℤ) (L : ℕ) : (z % (2 : ℤ) ^ L).toNat < 2 ^ L := by
  have hpos : (0 : ℤ) < (2 : ℤ) ^ L := by positivity
  have h0 : 0 ≤ z % (2 : ℤ) ^ L := Int.emod_nonneg _ hpos.ne'
  have h1 : z % (2 : ℤ) ^ L < (2 : ℤ) ^ L := Int.emod_lt_of_pos _ hpos
  have hc : ((2 ^ L : ℕ) : ℤ) = (2 : ℤ) ^ L := by norm_num
  have h2 : (((z % (2 : ℤ) ^ L).toNat : ℕ) : ℤ) = z % (2 : ℤ) ^ L := Int.toNat_of_nonneg h0
  have h3 : (((z % (2 : ℤ) ^ L).toNat : ℕ) : ℤ) < ((2 ^ L : ℕ) : ℤ) := by rw [h2, hc]; exact h1
  exact_mod_cast h3

/-- The arithmetic of one line: subtracting the natural offset undoes the integer shift. -/
theorem line_arith {L tgt s : ℕ} (ht : tgt < 2 ^ L) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ((((tgt : ℤ) + ε * (s : ℤ)) % (2 : ℤ) ^ L).toNat + 2 ^ L -
      (if ε = 1 then s % 2 ^ L else (2 ^ L - s % 2 ^ L) % 2 ^ L) % 2 ^ L) % 2 ^ L = tgt := by
  have hRpos : 0 < 2 ^ L := by positivity
  have hRz : (2 : ℤ) ^ L = ((2 ^ L : ℕ) : ℤ) := by norm_num
  have h0 : 0 ≤ ((tgt : ℤ) + ε * (s : ℤ)) % (2 : ℤ) ^ L := Int.emod_nonneg _ (by positivity)
  have ho_lt : (if ε = 1 then s % 2 ^ L else (2 ^ L - s % 2 ^ L) % 2 ^ L) % 2 ^ L < 2 ^ L :=
    Nat.mod_lt _ hRpos
  have key : (((((tgt : ℤ) + ε * (s : ℤ)) % (2 : ℤ) ^ L).toNat + 2 ^ L -
      (if ε = 1 then s % 2 ^ L else (2 ^ L - s % 2 ^ L) % 2 ^ L) % 2 ^ L : ℕ) : ZMod (2 ^ L)) =
      (tgt : ZMod (2 ^ L)) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]
    have hn : ((((tgt : ℤ) + ε * (s : ℤ)) % (2 : ℤ) ^ L).toNat : ZMod (2 ^ L)) =
        (((tgt : ℤ) + ε * (s : ℤ) : ℤ) : ZMod (2 ^ L)) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0, hRz, ZMod.intCast_mod]
    rw [hn]
    rcases hε with rfl | rfl
    · rw [if_pos rfl, ZMod.natCast_mod, ZMod.natCast_mod]
      push_cast
      ring
    · rw [if_neg (by norm_num), ZMod.natCast_mod, ZMod.natCast_mod,
        Nat.cast_sub (Nat.mod_lt s hRpos).le, ZMod.natCast_self, ZMod.natCast_mod]
      push_cast
      ring
  have := congrArg ZMod.val key
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht] at this
/-- Core of the line inversion (positions abstract): after `σ`, the shift on the rightmost chunk
by the right offset, and `σ` again, the target chunk is back to its old value. -/
theorem line_core (G : Geo Ly L C) {pt po : ℕ}
    (hcase : (pt = C.py ∧ po = C.pz) ∨ (pt = C.pz ∧ po = C.py))
    (off : Ly.Addr → ℕ) (b a0 : Ly.Addr) (newv : ℕ)
    (hout : ∀ j : Fin Ly.n, Out3 L C j.val → a0 j = b j)
    (hx : chunkVal L C.px a0 = chunkVal L C.px b) (ho : chunkVal L po a0 = chunkVal L po b)
    (ht : chunkVal L pt a0 = newv)
    (har : (newv + 2 ^ L - off (sigmaPull Ly L pt C.right a0) % 2 ^ L) % 2 ^ L = chunkVal L pt b) :
    sigmaPull Ly L pt C.right ((Elem.shift C.right (C.right + L) off : Elem Ly).pull
      (sigmaPull Ly L pt C.right a0)) = b := by
  have hpt : Mem3 C pt := by
    rcases hcase with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact mem3_y C
    · rw [h]; exact mem3_z C
  have hpr := mem3_right C
  have hothers : ∀ q, Mem3 C q → q ≠ pt → q = C.px ∨ q = po := by
    intro q hq hne
    rcases hq with hq | hq | hq
    · exact Or.inl hq
    · rcases hcase with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd (hq.trans h1.symm) hne
      · exact Or.inr (hq.trans h2.symm)
    · rcases hcase with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Or.inr (hq.trans h2.symm)
      · exact absurd (hq.trans h1.symm) hne
  have hval : ∀ q, Mem3 C q →
      chunkVal L q (sigmaPull Ly L pt C.right ((Elem.shift C.right (C.right + L) off : Elem Ly).pull
        (sigmaPull Ly L pt C.right a0))) = chunkVal L q b := by
    intro q hq
    rw [sigma_chunk G hpt hpr hq]
    have hmq := movedPos_mem hpt hpr hq
    by_cases hqr : movedPos pt C.right q = C.right
    · have hq_pt : q = pt := (movedPos_eq_right_iff pt C.right q).mp hqr
      rw [hqr, shift_chunk_self (G.chunk hpr), sigma_chunk G hpt hpr hpr, movedPos_right, ht,
        har, hq_pt]
    · have hq_pt : q ≠ pt := fun h => hqr ((movedPos_eq_right_iff pt C.right q).mpr h)
      rw [shift_chunk_other (G.disj hpr hmq (Ne.symm hqr)), sigma_chunk G hpt hpr hmq,
        movedPos_invol]
      rcases hothers q hq hq_pt with h | h
      · rw [h]; exact hx
      · rw [h]; exact ho
  apply addr_ext3 (L := L) (px := C.px) (py := C.py) (pz := C.pz)
  · intro j h1 h2 h3
    have hj : Out3 L C j.val := ⟨h1, h2, h3⟩
    rw [sigma_apply_out hpt hpr _ j hj, shift_apply_of_not _ _ j (out3_not_mem hj hpr),
      sigma_apply_out hpt hpr _ j hj, hout j hj]
  · exact hval _ (mem3_x C)
  · exact hval _ (mem3_y C)
  · exact hval _ (mem3_z C)

/-- The natural-number offset sum of a line, computed on chunk values. -/
def offSum (K ρ f : ℕ) (par x o : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (f - 1), 2 ^ (ρ + i * K) *
    (if bitAt x (ρ + i * K) = 1 ∧ bitAt o (ρ + i * K) = par then 1 else 0)

theorem offSum_cast (K ρ f par x o : ℕ) :
    ((offSum K ρ f par x o : ℕ) : ℤ) = ∑ i ∈ Finset.range (f - 1), (2 : ℤ) ^ (ρ + i * K) *
      (if bitAt x (ρ + i * K) = 1 ∧ bitAt o (ρ + i * K) = par then 1 else 0) := by
  unfold offSum
  push_cast
  rfl

theorem sel_lt {L K ρ f i : ℕ} (hL : L = f * K) (hρ : ρ < K) (hi : i < f - 1) :
    ρ + i * K < L := by
  have h1 : i + 1 ≤ f := by omega
  have h2 : (i + 1) * K ≤ f * K := Nat.mul_le_mul_right K h1
  rw [hL]
  calc ρ + i * K < K + i * K := by omega
    _ = (i + 1) * K := by ring
    _ ≤ f * K := h2

/-- The offset read by the shift of a line equals `offSum` on the original chunk values. -/
theorem lineOff_eq (G : Geo Ly L C) (hL : L = f * K) (hρ : ρ < K) (op : Bool × ℤ × ℕ)
    {po : ℕ} (hpo : po = if op.1 then C.pz else C.py) (hpt : Mem3 C (tgtPos C op))
    (hpoM : Mem3 C po) (a0 : Ly.Addr) :
    lineOff Ly L K ρ f C op (sigmaPull Ly L (tgtPos C op) C.right a0) =
      if op.2.1 = 1 then offSum K ρ f op.2.2 (chunkVal L C.px a0) (chunkVal L po a0) % 2 ^ L
      else (2 ^ L - offSum K ρ f op.2.2 (chunkVal L C.px a0) (chunkVal L po a0) % 2 ^ L) % 2 ^ L := by
  have hpr := mem3_right C
  have hs : (∑ i ∈ Finset.range (f - 1), 2 ^ (ρ + i * K) *
      (if chunkBit L (movedPos (tgtPos C op) C.right C.px) (ρ + i * K)
            (sigmaPull Ly L (tgtPos C op) C.right a0) = 1 ∧
          chunkBit L (movedPos (tgtPos C op) C.right (if op.1 then C.pz else C.py)) (ρ + i * K)
            (sigmaPull Ly L (tgtPos C op) C.right a0) = op.2.2 then 1 else 0)) =
      offSum K ρ f op.2.2 (chunkVal L C.px a0) (chunkVal L po a0) := by
    unfold offSum
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hj := sel_lt hL hρ hi
    have hmx := movedPos_mem hpt hpr (mem3_x C)
    rw [← hpo]
    have hmo := movedPos_mem hpt hpr hpoM
    rw [chunkBit_eq (G.chunk hmx) hj, chunkBit_eq (G.chunk hmo) hj,
      sigma_chunk G hpt hpr hmx, sigma_chunk G hpt hpr hmo, movedPos_invol, movedPos_invol]
  unfold lineOff
  simp only []
  rw [hs]

theorem packedLine_fst (op : Bool × ℤ × ℕ) (xyz : ℕ × ℕ × ℕ) :
    (packedLine L K ρ f op xyz).1 = xyz.1 := by
  unfold packedLine
  split_ifs <;> rfl

theorem packedLine_lt (op : Bool × ℤ × ℕ) {xyz : ℕ × ℕ × ℕ} (h1 : xyz.1 < 2 ^ L)
    (h2 : xyz.2.1 < 2 ^ L) (h3 : xyz.2.2 < 2 ^ L) :
    (packedLine L K ρ f op xyz).1 < 2 ^ L ∧ (packedLine L K ρ f op xyz).2.1 < 2 ^ L ∧
      (packedLine L K ρ f op xyz).2.2 < 2 ^ L := by
  unfold packedLine
  split_ifs
  · exact ⟨h1, toNat_emod_lt _ L, h3⟩
  · exact ⟨h1, h2, toNat_emod_lt _ L⟩

theorem chunkVals_setChunks (G : Geo Ly L C) (b : Ly.Addr) {v : ℕ × ℕ × ℕ} (h1 : v.1 < 2 ^ L)
    (h2 : v.2.1 < 2 ^ L) (h3 : v.2.2 < 2 ^ L) : chunkVals L C (setChunks L C b v) = v := by
  unfold chunkVals
  rw [setChunks_x G, setChunks_y G, setChunks_z G, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3]

theorem setChunks_setChunks (G : Geo Ly L C) (b : Ly.Addr) (v w : ℕ × ℕ × ℕ) :
    setChunks L C (setChunks L C b v) w = setChunks L C b w := by
  apply addr_ext3 (L := L) (px := C.px) (py := C.py) (pz := C.pz)
  · intro j h1 h2 h3
    rw [setChunks_apply_out _ _ j ⟨h1, h2, h3⟩, setChunks_apply_out _ _ j ⟨h1, h2, h3⟩,
      setChunks_apply_out _ _ j ⟨h1, h2, h3⟩]
  · rw [setChunks_x G, setChunks_x G]
  · rw [setChunks_y G, setChunks_y G]
  · rw [setChunks_z G, setChunks_z G]

theorem setChunks_self (G : Geo Ly L C) (b : Ly.Addr) : setChunks L C b (chunkVals L C b) = b := by
  apply addr_ext3 (L := L) (px := C.px) (py := C.py) (pz := C.pz)
  · intro j h1 h2 h3
    exact setChunks_apply_out _ _ j ⟨h1, h2, h3⟩
  · rw [setChunks_x G]; exact Nat.mod_eq_of_lt (chunkVal_lt G.hx b)
  · rw [setChunks_y G]; exact Nat.mod_eq_of_lt (chunkVal_lt G.hy b)
  · rw [setChunks_z G]; exact Nat.mod_eq_of_lt (chunkVal_lt G.hz b)

/-- **One packed line**: its pull is a left inverse of its forward map. -/
theorem line_pull_fwd (G : Geo Ly L C) (hL : L = f * K) (hρ : ρ < K) (op : Bool × ℤ × ℕ)
    (hop : op.2.1 = 1 ∨ op.2.1 = -1) (b : Ly.Addr) :
    pullComp (lineSteps (Ly := Ly) (β := β) L K ρ f C op) (lineFwd L K ρ f C op b) = b := by
  rw [pullComp_line]
  obtain ⟨isY, ε, par⟩ := op
  have hx := chunkVal_lt G.hx b
  have hy := chunkVal_lt G.hy b
  have hz := chunkVal_lt G.hz b
  cases isY with
  | true =>
    obtain ⟨S, hS⟩ : ∃ S, S = offSum K ρ f par (chunkVal L C.px b) (chunkVal L C.pz b) := ⟨_, rfl⟩
    obtain ⟨newv, hnewv⟩ : ∃ v : ℕ,
        v = ((((chunkVal L C.py b : ℕ) : ℤ) + ε * (S : ℤ)) % (2 : ℤ) ^ L).toNat := ⟨_, rfl⟩
    have hfwd : lineFwd L K ρ f C (true, ε, par) b =
        setChunks L C b (chunkVal L C.px b, newv, chunkVal L C.pz b) := by
      unfold lineFwd
      congr 1
      rw [hnewv, hS, offSum_cast]
      rfl
    have hnew_lt : newv < 2 ^ L := by rw [hnewv]; exact toNat_emod_lt _ L
    have hx0 : chunkVal L C.px (setChunks L C b (chunkVal L C.px b, newv, chunkVal L C.pz b)) =
        chunkVal L C.px b := by rw [setChunks_x G]; exact Nat.mod_eq_of_lt hx
    have hz0 : chunkVal L C.pz (setChunks L C b (chunkVal L C.px b, newv, chunkVal L C.pz b)) =
        chunkVal L C.pz b := by rw [setChunks_z G]; exact Nat.mod_eq_of_lt hz
    have hy0 : chunkVal L C.py (setChunks L C b (chunkVal L C.px b, newv, chunkVal L C.pz b)) =
        newv := by rw [setChunks_y G]; exact Nat.mod_eq_of_lt hnew_lt
    rw [hfwd]
    refine line_core (pt := tgtPos C (true, ε, par)) (po := C.pz) G (Or.inl ⟨rfl, rfl⟩) _ b _ newv
      (fun j hj => setChunks_apply_out b _ j hj) hx0 hz0 hy0 ?_
    rw [lineOff_eq G hL hρ (true, ε, par) (po := C.pz) rfl (mem3_y C) (mem3_z C), hx0, hz0]
    have h := line_arith (s := S) hy ε hop
    rw [hS] at h
    rw [hnewv, hS]
    exact h
  | false =>
    obtain ⟨S, hS⟩ : ∃ S, S = offSum K ρ f par (chunkVal L C.px b) (chunkVal L C.py b) := ⟨_, rfl⟩
    obtain ⟨newv, hnewv⟩ : ∃ v : ℕ,
        v = ((((chunkVal L C.pz b : ℕ) : ℤ) + ε * (S : ℤ)) % (2 : ℤ) ^ L).toNat := ⟨_, rfl⟩
    have hfwd : lineFwd L K ρ f C (false, ε, par) b =
        setChunks L C b (chunkVal L C.px b, chunkVal L C.py b, newv) := by
      unfold lineFwd
      congr 1
      rw [hnewv, hS, offSum_cast]
      rfl
    have hnew_lt : newv < 2 ^ L := by rw [hnewv]; exact toNat_emod_lt _ L
    have hx0 : chunkVal L C.px (setChunks L C b (chunkVal L C.px b, chunkVal L C.py b, newv)) =
        chunkVal L C.px b := by rw [setChunks_x G]; exact Nat.mod_eq_of_lt hx
    have hy0 : chunkVal L C.py (setChunks L C b (chunkVal L C.px b, chunkVal L C.py b, newv)) =
        chunkVal L C.py b := by rw [setChunks_y G]; exact Nat.mod_eq_of_lt hy
    have hz0 : chunkVal L C.pz (setChunks L C b (chunkVal L C.px b, chunkVal L C.py b, newv)) =
        newv := by rw [setChunks_z G]; exact Nat.mod_eq_of_lt hnew_lt
    rw [hfwd]
    refine line_core (pt := tgtPos C (false, ε, par)) (po := C.py) G (Or.inr ⟨rfl, rfl⟩) _ b _ newv
      (fun j hj => setChunks_apply_out b _ j hj) hx0 hy0 hz0 ?_
    rw [lineOff_eq G hL hρ (false, ε, par) (po := C.py) rfl (mem3_z C) (mem3_y C), hx0, hy0]
    have h := line_arith (s := S) hz ε hop
    rw [hS] at h
    rw [hnewv, hS]
    exact h

/-! ### The eight lines are a left inverse of `addrS0` -/

/-- The forward maps of a list of lines, applied in order. -/
def fwdComp (L K ρ f : ℕ) (C : Chunks3) : List (Bool × ℤ × ℕ) → Ly.Addr → Ly.Addr
  | [] => id
  | op :: ops => fwdComp L K ρ f C ops ∘ lineFwd L K ρ f C op

theorem pull_lines_fwd (G : Geo Ly L C) (hL : L = f * K) (hρ : ρ < K)
    (ops : List (Bool × ℤ × ℕ)) (hops : ∀ op ∈ ops, op.2.1 = 1 ∨ op.2.1 = -1) (b : Ly.Addr) :
    pullComp (ops.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C)) (fwdComp L K ρ f C ops b) =
      b := by
  induction ops generalizing b with
  | nil => rfl
  | cons op ops ih =>
    rw [show (op :: ops).flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) =
        lineSteps L K ρ f C op ++ ops.flatMap (lineSteps L K ρ f C) from rfl, pullComp_append]
    simp only [fwdComp, Function.comp_apply]
    rw [ih (fun op' h => hops op' (List.mem_cons_of_mem _ h)),
      line_pull_fwd G hL hρ op (hops op (by simp)) b]

theorem fwdComp_eq (G : Geo Ly L C) (ops : List (Bool × ℤ × ℕ)) (b : Ly.Addr) :
    fwdComp L K ρ f C ops b =
      setChunks L C b (ops.foldl (fun p op => packedLine L K ρ f op p) (chunkVals L C b)) := by
  induction ops generalizing b with
  | nil => exact (setChunks_self G b).symm
  | cons op ops ih =>
    simp only [fwdComp, Function.comp_apply, List.foldl_cons]
    rw [ih (lineFwd L K ρ f C op b)]
    have hlt := packedLine_lt (L := L) (K := K) (ρ := ρ) (f := f) op (xyz := chunkVals L C b)
      (chunkVal_lt G.hx b) (chunkVal_lt G.hy b) (chunkVal_lt G.hz b)
    unfold lineFwd
    rw [setChunks_setChunks G, chunkVals_setChunks G _ hlt.1 hlt.2.1 hlt.2.2]

theorem packedS0_fst (xyz : ℕ × ℕ × ℕ) : (packedS0 L K ρ f xyz).1 = xyz.1 := by
  unfold packedS0
  generalize eightOps = ops
  induction ops generalizing xyz with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [ih, packedLine_fst]

theorem addrS0_eq (b : Ly.Addr) :
    addrS0 L K ρ f C b = setChunks L C b (packedS0 L K ρ f (chunkVals L C b)) := by
  have h1 : (packedS0 L K ρ f (chunkVals L C b)).1 = chunkVal L C.px b := packedS0_fst _
  have h2 : Ly.blockSet C.px (C.px + L) b (chunkVal L C.px b) = b := blockSet_blockVal _ _ b
  show Ly.blockSet C.pz (C.pz + L) (Ly.blockSet C.py (C.py + L) b
      (packedS0 L K ρ f (chunkVals L C b)).2.1) (packedS0 L K ρ f (chunkVals L C b)).2.2 =
    setChunks L C b (packedS0 L K ρ f (chunkVals L C b))
  unfold setChunks
  rw [h1, h2]

theorem eightOps_sign : ∀ op ∈ eightOps, op.2.1 = 1 ∨ op.2.1 = -1 := by decide

/-- **The eight packed lines**: the composite pull of their steps is a left inverse of `addrS0`. -/
theorem pull_lines_addrS0 (G : Geo Ly L C) (hL : L = f * K) (hρ : ρ < K) (b : Ly.Addr) :
    pullComp (eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C)) (addrS0 L K ρ f C b) =
      b := by
  rw [addrS0_eq, show setChunks L C b (packedS0 L K ρ f (chunkVals L C b)) =
    fwdComp L K ρ f C eightOps b from (fwdComp_eq G eightOps b).symm]
  exact pull_lines_fwd G hL hρ eightOps eightOps_sign b

/-! ### Every step of the procedure moves only chunk fields -/

theorem moves_swp (c : RowClass Ly) (hrow : Out3 L C c.row.val) {pt : ℕ} (hpt : Mem3 C pt) :
    ∀ s ∈ (if pt = C.right then ([] : List (Step Ly β)) else [.swapBlocks pt C.right L]),
      IsMove s ∧ ∀ x, stepPull s x c.row = x c.row := by
  intro s hs
  split_ifs at hs with h
  · simp at hs
  · rw [List.mem_singleton] at hs
    subst hs
    exact ⟨trivial, fun x => swapPull_apply_of_not x c.row (out3_not_mem hrow hpt)
      (out3_not_mem hrow (mem3_right C))⟩

theorem moves_lineSteps (c : RowClass Ly) (hrow : Out3 L C c.row.val) (op : Bool × ℤ × ℕ) :
    ∀ s ∈ lineSteps (Ly := Ly) (β := β) L K ρ f C op,
      IsMove s ∧ ∀ x, stepPull s x c.row = x c.row := by
  have hpt : Mem3 C (tgtPos C op) := by
    unfold tgtPos
    split_ifs
    · exact mem3_y C
    · exact mem3_z C
  rw [lineSteps_eq]
  intro s hs
  rw [List.mem_append, List.mem_append, List.mem_singleton] at hs
  rcases hs with (hs | rfl) | hs
  · exact moves_swp c hrow hpt s hs
  · exact ⟨trivial, fun x => shift_apply_of_not _ x c.row (out3_not_mem hrow (mem3_right C))⟩
  · exact moves_swp c hrow hpt s hs

theorem topBitSteps_eq : topBitSteps (Ly := Ly) (β := β) L K ρ f C =
    (if C.py = C.right then [] else [.swapBlocks C.py C.right L]) ++
      [.elem (.shift (C.right + L - 1 - (ρ + (f - 1) * K)) (C.right + L - (ρ + (f - 1) * K))
        (fun a => chunkBit L (movedPos C.py C.right C.px) (ρ + (f - 1) * K) a))] ++
      (if C.py = C.right then [] else [.swapBlocks C.py C.right L]) := rfl

theorem moves_topBitSteps (c : RowClass Ly) (hrow : Out3 L C c.row.val)
    (hj : ρ + (f - 1) * K < L) :
    ∀ s ∈ topBitSteps (Ly := Ly) (β := β) L K ρ f C,
      IsMove s ∧ ∀ x, stepPull s x c.row = x c.row := by
  rw [topBitSteps_eq]
  intro s hs
  rw [List.mem_append, List.mem_append, List.mem_singleton] at hs
  rcases hs with (hs | rfl) | hs
  · exact moves_swp c hrow (mem3_y C) s hs
  · refine ⟨trivial, fun x => shift_apply_of_not _ x c.row ?_⟩
    have := out3_not_mem hrow (mem3_right C)
    omega
  · exact moves_swp c hrow (mem3_y C) s hs

theorem repair_row (c : RowClass Ly) (hrow : Out3 L C c.row.val) (x : Ly.Addr) :
    stepPull (repairStep (Ly := Ly) (β := β) L K ρ f C) x c.row = x c.row := by
  show Ly.blockSet C.pz (C.pz + L) (Ly.blockSet C.py (C.py + L) (addrT0 L K ρ f C x) _) _ c.row =
    x c.row
  rw [blockSet_apply_of_not _ _ _ hrow.2.2, blockSet_apply_of_not _ _ _ hrow.2.1]
  exact blockSet_apply_of_not _ _ _ hrow.2.1

/-- **Assembly**, given the top-bit facts: the procedure computes `addrXorAll` on the class. -/
theorem packedProc_assemble (hP : PackedHyps Ly L K ρ f C) (c : RowClass Ly)
    (hcx : c.row.val < C.px ∨ C.px + L ≤ c.row.val) (hcy : c.row.val < C.py ∨ C.py + L ≤ c.row.val)
    (hcz : c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) (A : Ly.Addr → β)
    (topMap : Ly.Addr → Ly.Addr)
    (htop : ∀ a, pullComp (topBitSteps (Ly := Ly) (β := β) L K ρ f C) a = topMap a)
    (hT0 : ∀ a, addrT0 L K ρ f C (topMap a) = addrXorAll L K ρ f C a) :
    ProcK.run 0 (packedAddProc (Ly := Ly) (β := β) L K ρ f C) c A =
      fun a => if c.mem a then A (addrXorAll L K ρ f C a) else A a := by
  have G := geo_of_hyps hP
  have hL : L = f * K := hP.2.1
  have hρ : ρ < K := hP.2.2.1
  have hf : 1 ≤ f := hP.2.2.2.1
  have hj : ρ + (f - 1) * K < L := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [hL, Nat.add_sub_cancel, Nat.add_mul, one_mul]
    linarith
  have hrow : Out3 L C c.row.val := ⟨by omega, by omega, by omega⟩
  have hmoves : ∀ s ∈ eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) ++
      [repairStep (Ly := Ly) (β := β) L K ρ f C] ++ topBitSteps (Ly := Ly) (β := β) L K ρ f C,
      IsMove s ∧ ∀ x, stepPull s x c.row = x c.row := by
    intro s hs
    rw [List.mem_append, List.mem_append, List.mem_flatMap, List.mem_singleton] at hs
    rcases hs with (⟨op, -, hs⟩ | rfl) | hs
    · exact moves_lineSteps c hrow op s hs
    · exact ⟨trivial, repair_row c hrow⟩
    · exact moves_topBitSteps c hrow hj s hs
  show List.foldl (fun A s => Step.runIn c s A) A
    (eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) ++
      [repairStep (Ly := Ly) (β := β) L K ρ f C] ++ topBitSteps (Ly := Ly) (β := β) L K ρ f C) = _
  rw [foldl_runIn c _ hmoves A]
  funext a
  by_cases ha : c.mem a
  · rw [if_pos ha, if_pos ha]
    congr 1
    rw [pullComp_append, pullComp_append, Function.comp_apply, Function.comp_apply, htop a]
    show pullComp (eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C))
      (addrS0 L K ρ f C (addrT0 L K ρ f C (topMap a))) = addrXorAll L K ρ f C a
    rw [pull_lines_addrS0 G hL hρ, hT0]
  · rw [if_neg ha, if_neg ha]

end Lines

end PackedProcAux

/-- **Lemma A.9 (`lem:transfer13`) correctness**: in any row class whose
row field lies outside the three chunks, for any payload, `packedAddProc` computes exactly the
selected-bit XOR `y_{ρ+iK} ⊕= x_{ρ+iK}` (`i < f`), all other fields and records preserved. -/
theorem packedProcCorrect_holds : PackedProcCorrectStmt := by
  intro _ _ Ly β L K ρ f C hP c hcx hcy hcz A
  exact PackedProcAux.packedProc_assemble hP c hcx hcy hcz A (PackedProcBitsAux.topMap L K ρ f C)
    (PackedProcBitsAux.pullComp_topBitSteps hP) (PackedProcBitsAux.addrT0_topMap hP)

end SubNLogN.Math.Networks
