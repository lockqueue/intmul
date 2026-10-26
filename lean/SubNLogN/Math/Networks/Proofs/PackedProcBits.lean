import SubNLogN.Math.Networks.Proofs.PackedProcLib
import SubNLogN.Math.Networks.Proofs.PackedRepair

/-!
# Lemma A.9 (`lem:transfer13`) (`packedAddProc`): the omitted top selected bit and the final XOR

Part of the proof of `PackedProcCorrectStmt` (assembled in `Proofs/PackedProc.lean`). Here:
* `topMap L K ρ f C a`: overwrite chunk `y` by `y XOR 2^j x_j`, `j = ρ + (f−1)K`;
* `pullComp_topBitSteps`: under `PackedHyps`, the composite pull of `topBitSteps` is `topMap`.
  If `y` is the rightmost chunk this is one single-field shift (`shift1_chunk_self`). Otherwise it
  is swap–shift–swap (`sss_*`), where the control bit is read at `movedPos`;
* `run_topBitSteps`: the run form in a class whose row field is outside the chunks (via
  `PackedProcAux.foldl_runIn`);
* `addrT0_topMap`: `addrT0 ∘ topMap = addrXorAll`. The two XORs act on different bits; the
  composition is `packedFull_holds` (`Proofs/PackedRepair.lean`).
Uses the shared library `PackedProcAux` (`Proofs/PackedProcLib.lean`). All declarations are in
`SubNLogN.Math.Networks.PackedProcBitsAux`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace PackedProcBitsAux

open PackedProcAux

variable {Ly : Layout}

/-! ### Bits of natural numbers -/

theorem bitAt_lt_two (x j : ℕ) : bitAt x j < 2 := Nat.mod_lt _ two_pos

theorem bitAt_eq_ite (x j : ℕ) : bitAt x j = if x.testBit j then 1 else 0 := by
  unfold bitAt
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

theorem bitAt_xor (x y j : ℕ) : bitAt (Nat.xor x y) j = (bitAt x j + bitAt y j) % 2 := by
  rw [bitAt_eq_ite, bitAt_eq_ite, bitAt_eq_ite]
  have : (Nat.xor x y).testBit j = (x.testBit j ^^ y.testBit j) := Nat.testBit_xor x y j
  rw [this]
  cases x.testBit j <;> cases y.testBit j <;> rfl

theorem bitAt_two_pow_mul (j j' b : ℕ) (hb : b < 2) :
    bitAt (2 ^ j * b) j' = if j' = j then b else 0 := by
  interval_cases b
  · simp [bitAt]
  · rw [mul_one, bitAt_eq_ite, Nat.testBit_two_pow]
    by_cases h : j' = j
    · subst h; simp
    · simp [h, Ne.symm h]

theorem xorBit_lt {y L j b : ℕ} (hy : y < 2 ^ L) (hj : j < L) (hb : b < 2) :
    Nat.xor y (2 ^ j * b) < 2 ^ L := by
  refine Nat.xor_lt_two_pow hy ?_
  interval_cases b
  · simp
  · rw [mul_one]; exact Nat.pow_lt_pow_right (by norm_num) hj

/-- Bit `j'` of `y XOR 2^j b` (`b ∈ {0,1}`). -/
theorem bitAt_xorBit (y j j' b : ℕ) (hb : b < 2) :
    bitAt (Nat.xor y (2 ^ j * b)) j' = if j' = j then (bitAt y j + b) % 2 else bitAt y j' := by
  rw [bitAt_xor, bitAt_two_pow_mul j j' b hb]
  by_cases h : j' = j
  · subst h; simp
  · simp only [h, if_false, add_zero]
    exact Nat.mod_eq_of_lt (bitAt_lt_two _ _)

/-! ### The top-bit pull and the single-field shift -/

/-- The pull of the top-bit steps: `y ← y XOR 2^j x_j`, `j = ρ + (f−1)K`. -/
def topMap (L K ρ f : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr :=
  Ly.blockSet C.py (C.py + L) a
    (Nat.xor (chunkVal L C.py a) (2 ^ (ρ + (f - 1) * K) * chunkBit L C.px (ρ + (f - 1) * K) a))

theorem chunkOK_of {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C) :
    ChunkOK Ly L C.px ∧ ChunkOK Ly L C.py ∧ ChunkOK Ly L C.pz := by
  obtain ⟨_, _, _, _, hx, hy, hz, _, _, _, hb⟩ := hH
  exact ⟨⟨hx, fun i h1 h2 => hb i (Or.inl ⟨h1, h2⟩)⟩,
    ⟨hy, fun i h1 h2 => hb i (Or.inr (Or.inl ⟨h1, h2⟩))⟩,
    ⟨hz, fun i h1 h2 => hb i (Or.inr (Or.inr ⟨h1, h2⟩))⟩⟩

theorem chunkBit_lt_two {L p j : ℕ} (h : ChunkOK Ly L p) (hj : j < L) (a : Ly.Addr) :
    chunkBit L p j a < 2 := by
  rw [chunkBit_eq h hj]; exact bitAt_lt_two _ _

/-- A shift of the single binary field holding bit `j` of the chunk at `p` XORs that bit with the
offset parity. -/
theorem shift1_chunk_self {L p j : ℕ} (h : ChunkOK Ly L p) (hj : j < L) (off : Ly.Addr → ℕ)
    (x : Ly.Addr) :
    chunkVal L p ((Elem.shift (p + L - 1 - j) (p + L - j) off : Elem Ly).pull x) =
      Nat.xor (chunkVal L p x) (2 ^ j * (off x % 2)) := by
  have hr : Ly.blockRange (p + L - 1 - j) (p + L - j) = 2 := by
    rw [blockRange_binary (by omega) (by have := h.1; omega)
      (fun i h1 h2 => h.2 i (by omega) (by omega))]
    rw [show p + L - j - (p + L - 1 - j) = 1 by omega, pow_one]
  have ho : off x % 2 < 2 := Nat.mod_lt _ two_pos
  refine eq_of_bitAt_eq (chunkVal_lt h _) (xorBit_lt (chunkVal_lt h x) hj ho) fun i hi => ?_
  rw [← chunkBit_eq h hi, bitAt_xorBit _ _ _ _ ho]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← chunkBit_eq h hi]
    unfold chunkBit
    rw [shift_pull_eq, blockVal_blockSet, hr]
    have hbv : Ly.blockVal (p + L - 1 - i) (p + L - i) x < 2 := by
      have := blockVal_lt (p + L - 1 - i) (p + L - i) x
      rwa [hr] at this
    generalize Ly.blockVal (p + L - 1 - i) (p + L - i) x = bv at hbv ⊢
    generalize off x % 2 = o at ho ⊢
    interval_cases bv <;> interval_cases o <;> rfl
  · rw [if_neg hij, ← chunkBit_eq h hi, chunkBit_eq_field h hi, chunkBit_eq_field h hi]
    have hne : ¬ (p + L - 1 - j ≤ p + L - 1 - i ∧ p + L - 1 - i < p + L - j) := by omega
    exact congrArg Fin.val (shift_apply_of_not off x _ hne)

theorem shift1_chunk_other {L p q j : ℕ} (hd : p + L ≤ q ∨ q + L ≤ p) (hj : j < L)
    (off : Ly.Addr → ℕ) (x : Ly.Addr) :
    chunkVal L q ((Elem.shift (p + L - 1 - j) (p + L - j) off : Elem Ly).pull x) =
      chunkVal L q x := by
  unfold chunkVal
  rw [shift_pull_eq]
  exact blockVal_blockSet_of_disjoint (by omega) x _

/-- The swap–shift–swap composite of the top-bit steps when the target is not rightmost. -/
def sss (L pt pr j : ℕ) (off : Ly.Addr → ℕ) (a : Ly.Addr) : Ly.Addr :=
  swapPull Ly pt pr L
    ((Elem.shift (pr + L - 1 - j) (pr + L - j) off : Elem Ly).pull (swapPull Ly pt pr L a))

theorem sss_pt {L pt pr j : ℕ} (okt : ChunkOK Ly L pt) (okr : ChunkOK Ly L pr)
    (hd : pt + L ≤ pr ∨ pr + L ≤ pt) (hj : j < L) (off : Ly.Addr → ℕ) (a : Ly.Addr) :
    chunkVal L pt (sss L pt pr j off a) =
      Nat.xor (chunkVal L pt a) (2 ^ j * (off (swapPull Ly pt pr L a) % 2)) := by
  unfold sss
  rw [swap_chunk_left okt okr hd, shift1_chunk_self okr hj, swap_chunk_right okt okr]

theorem sss_pr {L pt pr j : ℕ} (okt : ChunkOK Ly L pt) (okr : ChunkOK Ly L pr)
    (hd : pt + L ≤ pr ∨ pr + L ≤ pt) (hj : j < L) (off : Ly.Addr → ℕ) (a : Ly.Addr) :
    chunkVal L pr (sss L pt pr j off a) = chunkVal L pr a := by
  unfold sss
  rw [swap_chunk_right okt okr, shift1_chunk_other (p := pr) (q := pt) (by omega) hj,
    swap_chunk_left okt okr hd]

theorem sss_other {L pt pr q j : ℕ} (hq1 : q + L ≤ pt ∨ pt + L ≤ q)
    (hq2 : q + L ≤ pr ∨ pr + L ≤ q) (hj : j < L) (off : Ly.Addr → ℕ) (a : Ly.Addr) :
    chunkVal L q (sss L pt pr j off a) = chunkVal L q a := by
  unfold sss
  rw [swap_chunk_other hq1 hq2, shift1_chunk_other (by omega) hj, swap_chunk_other hq1 hq2]

theorem sss_out {L pt pr j : ℕ} (hj : j < L) (off : Ly.Addr → ℕ) (a : Ly.Addr) (k : Fin Ly.n)
    (h1 : ¬ (pt ≤ k.val ∧ k.val < pt + L)) (h2 : ¬ (pr ≤ k.val ∧ k.val < pr + L)) :
    sss L pt pr j off a k = a k := by
  unfold sss
  rw [swapPull_apply_of_not _ k h1 h2, shift_apply_of_not off _ k (by omega),
    swapPull_apply_of_not _ k h1 h2]

theorem top_lt {L K ρ f : ℕ} (hL : L = f * K) (hρ : ρ < K) (hf : 1 ≤ f) :
    ρ + (f - 1) * K < L := by
  subst hL
  have h1 : (f - 1) * K + K = f * K := by
    have : f - 1 + 1 = f := by omega
    calc (f - 1) * K + K = (f - 1 + 1) * K := by ring
      _ = f * K := by rw [this]
  omega

theorem right_cases (C : Chunks3) : C.right = C.px ∨ C.right = C.py ∨ C.right = C.pz := by
  unfold Chunks3.right; omega

/-- **Pull form** of the top-bit steps: their composite pull is `topMap`. -/
theorem pullComp_topBitSteps {β : Type} {L K ρ f : ℕ} {C : Chunks3}
    (hH : PackedHyps Ly L K ρ f C) (a : Ly.Addr) :
    pullComp (topBitSteps (Ly := Ly) (β := β) L K ρ f C) a = topMap L K ρ f C a := by
  obtain ⟨okx, oky, okz⟩ := chunkOK_of hH
  obtain ⟨hK, hL, hρ, hf, -, -, -, hxy, hxz, hyz, -⟩ := hH
  have hL1 : 1 ≤ L := by subst hL; nlinarith
  have hjL := top_lt hL hρ hf
  have hright := right_cases C
  simp only [topBitSteps, topMap]
  generalize ρ + (f - 1) * K = j at hjL ⊢
  by_cases hpr : C.py = C.right
  · rw [if_pos hpr]
    simp only [List.nil_append, List.append_nil, pullComp_cons, pullComp_nil, Function.comp_id]
    show (Elem.shift (C.right + L - 1 - j) (C.right + L - j)
      (fun a => chunkBit L (movedPos C.py C.right C.px) j a) : Elem Ly).pull a = _
    rw [← hpr]
    have hmv : movedPos C.py C.py C.px = C.px := by
      unfold movedPos
      have : C.px ≠ C.py := by omega
      simp [this]
    rw [hmv]
    have hoffa : chunkBit L C.px j a % 2 = chunkBit L C.px j a :=
      Nat.mod_eq_of_lt (chunkBit_lt_two okx hjL a)
    refine addr_ext3 (px := C.px) (py := C.py) (pz := C.pz) (L := L) ?_ ?_ ?_ ?_
    · intro k h1 h2 h3
      rw [shift_apply_of_not _ a k (by omega), blockSet_apply_of_not _ _ k h2]
    · rw [shift1_chunk_other (by omega) hjL]
      unfold chunkVal
      rw [blockVal_blockSet_of_disjoint (by omega)]
    · rw [shift1_chunk_self oky hjL, chunkVal_blockSet_of_lt oky _
        (xorBit_lt (chunkVal_lt oky a) hjL (chunkBit_lt_two okx hjL a)), hoffa]
    · rw [shift1_chunk_other (by omega) hjL]
      unfold chunkVal
      rw [blockVal_blockSet_of_disjoint (by omega)]
  · rw [if_neg hpr]
    simp only [List.singleton_append]
    show sss L C.py C.right j (fun a => chunkBit L (movedPos C.py C.right C.px) j a) a = _
    have hW : Nat.xor (chunkVal L C.py a) (2 ^ j * chunkBit L C.px j a) < 2 ^ L :=
      xorBit_lt (chunkVal_lt oky a) hjL (chunkBit_lt_two okx hjL a)
    rcases hright with h | h | h
    · rw [h]
      have hmv : movedPos C.py C.px C.px = C.py := by unfold movedPos; simp
      rw [hmv]
      have hoff : chunkBit L C.py j (swapPull Ly C.py C.px L a) % 2 = chunkBit L C.px j a := by
        rw [chunkBit_eq oky hjL, swap_chunk_left oky okx (by omega), ← chunkBit_eq okx hjL,
          Nat.mod_eq_of_lt (chunkBit_lt_two okx hjL a)]
      refine addr_ext3 (px := C.px) (py := C.py) (pz := C.pz) (L := L) ?_ ?_ ?_ ?_
      · intro k h1 h2 h3
        rw [sss_out hjL _ a k h2 h1, blockSet_apply_of_not _ _ k h2]
      · rw [sss_pr oky okx (by omega) hjL]
        unfold chunkVal
        rw [blockVal_blockSet_of_disjoint (by omega)]
      · rw [sss_pt oky okx (by omega) hjL, hoff, chunkVal_blockSet_of_lt oky _ hW]
      · rw [sss_other (by omega) (by omega) hjL]
        unfold chunkVal
        rw [blockVal_blockSet_of_disjoint (by omega)]
    · exact absurd h.symm hpr
    · rw [h]
      have hmv : movedPos C.py C.pz C.px = C.px := by
        unfold movedPos
        have h1 : C.px ≠ C.pz := by omega
        have h2 : C.px ≠ C.py := by omega
        simp [h1, h2]
      rw [hmv]
      have hoff : chunkBit L C.px j (swapPull Ly C.py C.pz L a) % 2 = chunkBit L C.px j a := by
        rw [chunkBit_eq okx hjL, swap_chunk_other (by omega) (by omega), ← chunkBit_eq okx hjL,
          Nat.mod_eq_of_lt (chunkBit_lt_two okx hjL a)]
      refine addr_ext3 (px := C.px) (py := C.py) (pz := C.pz) (L := L) ?_ ?_ ?_ ?_
      · intro k h1 h2 h3
        rw [sss_out hjL _ a k h2 h3, blockSet_apply_of_not _ _ k h2]
      · rw [sss_other (by omega) (by omega) hjL]
        unfold chunkVal
        rw [blockVal_blockSet_of_disjoint (by omega)]
      · rw [sss_pt oky okz (by omega) hjL, hoff, chunkVal_blockSet_of_lt oky _ hW]
      · rw [sss_pr oky okz (by omega) hjL]
        unfold chunkVal
        rw [blockVal_blockSet_of_disjoint (by omega)]

theorem xor_swap (y A B : ℕ) : Nat.xor (Nat.xor y A) B = Nat.xor (Nat.xor y B) A := by
  show (y ^^^ A) ^^^ B = (y ^^^ B) ^^^ A
  rw [Nat.xor_assoc, Nat.xor_comm A B, ← Nat.xor_assoc]

/-- `T₀` after the top-bit pull is the full selected-bit XOR. -/
theorem addrT0_topMap {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C)
    (a : Ly.Addr) : addrT0 L K ρ f C (topMap L K ρ f C a) = addrXorAll L K ρ f C a := by
  obtain ⟨okx, oky, okz⟩ := chunkOK_of hH
  obtain ⟨hK, hL, hρ, hf, -, -, -, hxy, hxz, hyz, -⟩ := hH
  have hjL := top_lt hL hρ hf
  have hbit : ∀ i, i < f → ρ + i * K < L := by
    intro i hi
    have : i * K ≤ (f - 1) * K := Nat.mul_le_mul_right K (by omega)
    omega
  have hW : Nat.xor (chunkVal L C.py a)
      (2 ^ (ρ + (f - 1) * K) * chunkBit L C.px (ρ + (f - 1) * K) a) < 2 ^ L :=
    xorBit_lt (chunkVal_lt oky a) hjL (chunkBit_lt_two okx hjL a)
  unfold addrT0 addrXorAll topMap
  rw [blockSet_blockSet]
  congr 1
  have hcv : chunkVals L C (Ly.blockSet C.py (C.py + L) a (Nat.xor (chunkVal L C.py a)
      (2 ^ (ρ + (f - 1) * K) * chunkBit L C.px (ρ + (f - 1) * K) a))) =
      (chunkVal L C.px a, Nat.xor (chunkVal L C.py a)
        (2 ^ (ρ + (f - 1) * K) * chunkBit L C.px (ρ + (f - 1) * K) a), chunkVal L C.pz a) := by
    unfold chunkVals
    rw [chunkVal_blockSet_of_lt oky a hW]
    unfold chunkVal
    rw [blockVal_blockSet_of_disjoint (by omega), blockVal_blockSet_of_disjoint (by omega)]
  rw [hcv]
  have hfull := packedFull_holds K ρ f hf hρ
    (chunkVal L C.px a, chunkVal L C.py a, chunkVal L C.pz a)
  have h2 := congrArg (fun p => p.2.1) hfull
  simp only [packedTopXor, packedT0, packedFull] at h2
  simp only [packedT0]
  have hsum : (∑ i ∈ Finset.range f, 2 ^ (ρ + i * K) * chunkBit L C.px (ρ + i * K) a) =
      ∑ i ∈ Finset.range f, 2 ^ (ρ + i * K) * bitAt (chunkVal L C.px a) (ρ + i * K) :=
    Finset.sum_congr rfl fun i hi => by rw [chunkBit_eq okx (hbit i (Finset.mem_range.mp hi))]
  rw [hsum, chunkBit_eq okx hjL, ← h2, xor_swap]

/-- **Run form** of the top-bit steps (in a class whose row field is outside the chunks). -/
theorem run_topBitSteps {β : Type} {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C)
    (c : RowClass Ly) (hcx : c.row.val < C.px ∨ C.px + L ≤ c.row.val)
    (hcy : c.row.val < C.py ∨ C.py + L ≤ c.row.val)
    (hcz : c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) (A : Ly.Addr → β) :
    ProcK.run 0 (topBitSteps (Ly := Ly) (β := β) L K ρ f C) c A =
      fun a => if c.mem a then A (topMap L K ρ f C a) else A a := by
  have hjL := top_lt hH.2.1 hH.2.2.1 hH.2.2.2.1
  have hright := right_cases C
  have hro : ¬ (C.right ≤ c.row.val ∧ c.row.val < C.right + L) := by
    rcases hright with h | h | h <;> rw [h] <;> omega
  have hry : ¬ (C.py ≤ c.row.val ∧ c.row.val < C.py + L) := by omega
  have hsteps : ∀ s ∈ topBitSteps (Ly := Ly) (β := β) L K ρ f C,
      IsMove s ∧ ∀ x, stepPull s x c.row = x c.row := by
    intro s hs
    simp only [topBitSteps] at hs
    by_cases hpr : C.py = C.right
    · rw [if_pos hpr] at hs
      simp only [List.nil_append, List.append_nil, List.mem_singleton] at hs
      subst hs
      exact ⟨trivial, fun x => shift_apply_of_not _ x c.row (by omega)⟩
    · rw [if_neg hpr] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with (rfl | rfl) | rfl
      · exact ⟨trivial, fun x => swapPull_apply_of_not x c.row hry hro⟩
      · exact ⟨trivial, fun x => shift_apply_of_not _ x c.row (by omega)⟩
      · exact ⟨trivial, fun x => swapPull_apply_of_not x c.row hry hro⟩
  show List.foldl (fun A s => Step.runIn c s A) A (topBitSteps (Ly := Ly) (β := β) L K ρ f C) = _
  rw [foldl_runIn c _ hsteps A]
  funext a
  rw [pullComp_topBitSteps hH a]

end PackedProcBitsAux

end SubNLogN.Math.Networks
