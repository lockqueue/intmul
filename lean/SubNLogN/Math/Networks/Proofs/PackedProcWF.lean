import SubNLogN.Math.Networks.AppCPacked
import SubNLogN.Math.Networks.Proofs.PackedRepair
import SubNLogN.Math.Networks.Proofs.PackedProcLib

/-!
# Proof of `PackedProcWFStmt` (well-formedness of the Lemma A.9 (`lem:transfer13`) procedure `packedAddProc`)

We prove `packedProcWF_holds : PackedProcWFStmt` (statement in `AppCPacked.lean`): under
`PackedHyps` (and `PackedAgreeStmt`, the hypothesis of the statement), every step of
`packedAddProc L K ρ f C` satisfies `Step.WF 2`.

## Plan
* **Interchanges.** `swapBlocks pt pr L` (target `pt ∈ {py, pz}`, `pr = C.right`, emitted only when
  `pt ≠ pr`) exchanges two disjoint chunks inside the layout, both of range `2^L` (binary fields)
  (`swp_WF`).
* **Shifts read only earlier fields.** In a packed line the target chunk has been moved to the
  rightmost position `pr = C.right`; the two control chunks then sit at `movedPos pt pr p`, which is a
  chunk position different from `pr`, hence (disjoint chunks of `L ≥ 1` fields) ends before `pr`
  (`moved_le`). A `chunkBit` of a chunk at `q` reads only fields `< q + L - j ≤ pr`
  (`chunkBit_congr`). The top-bit shift targets field `pr + L - 1 - j` and reads one field
  `< q + L - j ≤ pr + L - 1 - j`.
* **Repair.** The pull is `addrS0 ∘ addrT0`. On chunk values these maps act as `packedS0` and
  `packedT0` (`chunkVals_addrS0`, `chunkVals_addrT0`). `addrT0` is an involution and `addrS0` is
  injective (`packedS0` is injective on the rectangle, `PackedRepairAux.foldl_bijOn`, and an address
  is determined by its chunk values and its other fields), so the pull is injective, hence bijective
  (finite type). Off the exceptional set `S₀ (T₀ p) = T₀ (T₀ p) = p` (`PackedAgreeStmt` applied to
  `T₀ p`, which is good), so the pull fixes the address.
* The mixed-radix facts about the chunk blocks (ranges `2^L`, values below `2^L`, reading back an
  overwritten chunk, overwriting a chunk with its own value) are collected in `ChunkFacts` and
  derived from `PackedHyps` with the shared block lemmas of `PackedProcLib` (`chunkFacts_of_hyps`).
-/

namespace SubNLogN.Math.Networks

open Model

namespace PackedProcWFAux

open PackedAgreeAux PackedRepairAux PackedProcAux

variable {Ly : Layout}

/-! ### Block facts (generic block lemmas are from `PackedProcLib`) -/

lemma bs_apply_of_mem {t₀ t₁ : ℕ} (x y : Ly.Addr) (v : ℕ) (j : Fin Ly.n)
    (hj : t₀ ≤ j.val ∧ j.val < t₁) : Ly.blockSet t₀ t₁ x v j = Ly.blockSet t₀ t₁ y v j :=
  Fin.ext (by rw [blockSet_apply_val _ _ _ hj, blockSet_apply_val _ _ _ hj])

/-- A chunk bit reads only fields before `q + L - j`. -/
lemma chunkBit_congr {L q j : ℕ} {x y : Ly.Addr}
    (h : ∀ i : Fin Ly.n, i.val < q + L - j → x i = y i) : chunkBit L q j x = chunkBit L q j y :=
  blockVal_congr fun i _ hi => h i hi

/-! ### Positions of the chunks -/

lemma one_le_L {L K f : ℕ} (hK : 6 ≤ K) (hL : L = f * K) (hf : 1 ≤ f) : 1 ≤ L := by
  subst hL; nlinarith

lemma right_add_le (C : Chunks3) {L n : ℕ} (hx : C.px + L ≤ n) (hy : C.py + L ≤ n)
    (hz : C.pz + L ≤ n) : C.right + L ≤ n := by
  unfold Chunks3.right; omega

/-- After moving the target (at `py` or `pz`) to the rightmost position, the other two chunks end
before it. -/
lemma moved_le (C : Chunks3) {L : ℕ} (hL : 1 ≤ L)
    (hxy : C.px + L ≤ C.py ∨ C.py + L ≤ C.px) (hxz : C.px + L ≤ C.pz ∨ C.pz + L ≤ C.px)
    (hyz : C.py + L ≤ C.pz ∨ C.pz + L ≤ C.py) :
    movedPos C.py C.right C.px + L ≤ C.right ∧ movedPos C.py C.right C.pz + L ≤ C.right ∧
      movedPos C.pz C.right C.px + L ≤ C.right ∧ movedPos C.pz C.right C.py + L ≤ C.right := by
  unfold movedPos Chunks3.right
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-! ### Block facts about the three chunks -/

/-- The block facts about the three chunks used by the procedure; `chunkFacts_of_hyps` derives them
from `PackedHyps` and the mixed-radix block lemmas. -/
structure ChunkFacts (Ly : Layout) (L : ℕ) (C : Chunks3) : Prop where
  range : ∀ p : ℕ, (p = C.px ∨ p = C.py ∨ p = C.pz) → Ly.blockRange p (p + L) = 2 ^ L
  rect : ∀ a : Ly.Addr, chunkVals L C a ∈ packedRect L
  valY : ∀ (a : Ly.Addr) (v : ℕ), chunkVals L C (Ly.blockSet C.py (C.py + L) a v) =
    ((chunkVals L C a).1, v % 2 ^ L, (chunkVals L C a).2.2)
  valZ : ∀ (a : Ly.Addr) (v : ℕ), chunkVals L C (Ly.blockSet C.pz (C.pz + L) a v) =
    ((chunkVals L C a).1, (chunkVals L C a).2.1, v % 2 ^ L)
  setY : ∀ a : Ly.Addr, Ly.blockSet C.py (C.py + L) a (chunkVals L C a).2.1 = a
  setZ : ∀ a : Ly.Addr, Ly.blockSet C.pz (C.pz + L) a (chunkVals L C a).2.2 = a

/-! ### The shifts and interchanges -/

lemma right_cases (C : Chunks3) : C.right = C.px ∨ C.right = C.py ∨ C.right = C.pz := by
  unfold Chunks3.right; omega

/-- The interchange of the target chunk (at `py` or `pz`) with the rightmost chunk is well formed:
two disjoint blocks inside the layout, both of range `2^L`. -/
lemma swp_WF {β : Type} {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C)
    (hF : ChunkFacts Ly L C) (pt : ℕ) (hpt : pt = C.py ∨ pt = C.pz) (s : Step Ly β)
    (hs : s ∈ (if pt = C.right then [] else [Step.swapBlocks pt C.right L] : List (Step Ly β))) :
    Step.WF 2 s := by
  obtain ⟨hK, hL, hρ, hf, hx, hy, hz, hxy, hxz, hyz, -⟩ := hH
  split_ifs at hs with h
  · simp at hs
  · rw [List.mem_singleton] at hs
    subst hs
    refine ⟨?_, ?_, right_add_le C hx hy hz, ?_⟩
    · unfold Chunks3.right at h ⊢; omega
    · rcases hpt with rfl | rfl <;> assumption
    · rw [hF.range pt (Or.inr hpt), hF.range C.right (right_cases C)]

lemma lineSteps_WF {β : Type} {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C)
    (hF : ChunkFacts Ly L C) (op : Bool × ℤ × ℕ) :
    ∀ s ∈ lineSteps (Ly := Ly) (β := β) L K ρ f C op, Step.WF 2 s := by
  obtain ⟨hK, hL, hρ, hf, hx, hy, hz, hxy, hxz, hyz, -⟩ := id hH
  have hL1 : 1 ≤ L := one_le_L hK hL hf
  have hR : C.right + L ≤ Ly.n := right_add_le C hx hy hz
  obtain ⟨m1, m2, m3, m4⟩ := moved_le C hL1 hxy hxz hyz
  obtain ⟨t, e, q⟩ := op
  intro s hs
  cases t
  · simp only [lineSteps, Bool.false_eq_true, ↓reduceIte, List.mem_append,
      List.mem_singleton] at hs
    rcases hs with (hs | rfl) | hs
    · exact swp_WF hH hF _ (Or.inr rfl) _ hs
    · refine ⟨by omega, hR, fun x y hxy => ?_⟩
      have e1 : ∀ j, chunkBit L (movedPos C.pz C.right C.px) j x =
          chunkBit L (movedPos C.pz C.right C.px) j y :=
        fun j => chunkBit_congr fun i hi => hxy i (by omega)
      have e2 : ∀ j, chunkBit L (movedPos C.pz C.right C.py) j x =
          chunkBit L (movedPos C.pz C.right C.py) j y :=
        fun j => chunkBit_congr fun i hi => hxy i (by omega)
      simp only [e1, e2]
    · exact swp_WF hH hF _ (Or.inr rfl) _ hs
  · simp only [lineSteps, ↓reduceIte, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | rfl) | hs
    · exact swp_WF hH hF _ (Or.inl rfl) _ hs
    · refine ⟨by omega, hR, fun x y hxy => ?_⟩
      have e1 : ∀ j, chunkBit L (movedPos C.py C.right C.px) j x =
          chunkBit L (movedPos C.py C.right C.px) j y :=
        fun j => chunkBit_congr fun i hi => hxy i (by omega)
      have e2 : ∀ j, chunkBit L (movedPos C.py C.right C.pz) j x =
          chunkBit L (movedPos C.py C.right C.pz) j y :=
        fun j => chunkBit_congr fun i hi => hxy i (by omega)
      simp only [e1, e2]
    · exact swp_WF hH hF _ (Or.inl rfl) _ hs

lemma topBitSteps_WF {β : Type} {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C)
    (hF : ChunkFacts Ly L C) : ∀ s ∈ topBitSteps (Ly := Ly) (β := β) L K ρ f C, Step.WF 2 s := by
  obtain ⟨hK, hL, hρ, hf, hx, hy, hz, hxy, hxz, hyz, -⟩ := id hH
  have hL1 : 1 ≤ L := one_le_L hK hL hf
  have hR : C.right + L ≤ Ly.n := right_add_le C hx hy hz
  obtain ⟨m1, -, -, -⟩ := moved_le C hL1 hxy hxz hyz
  intro s hs
  simp only [topBitSteps, List.mem_append, List.mem_singleton] at hs
  rcases hs with (hs | rfl) | hs
  · exact swp_WF hH hF _ (Or.inl rfl) _ hs
  · exact ⟨by omega, by omega, fun x y hxy => chunkBit_congr fun i hi => hxy i (by omega)⟩
  · exact swp_WF hH hF _ (Or.inl rfl) _ hs

/-! ### The repair step -/

lemma packedLine_fst (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) (p : ℕ × ℕ × ℕ) :
    (packedLine L K ρ f op p).1 = p.1 := by
  obtain ⟨t, e, q⟩ := op
  obtain ⟨x, y, z⟩ := p
  cases t <;> rfl

lemma foldl_fst (L K ρ f : ℕ) : ∀ (ops : List (Bool × ℤ × ℕ)) (p : ℕ × ℕ × ℕ),
    (ops.foldl (fun p op => packedLine L K ρ f op p) p).1 = p.1
  | [], _ => rfl
  | op :: rest, p => by
    simp only [List.foldl_cons]
    rw [foldl_fst L K ρ f rest, packedLine_fst]

section repair

variable {L : ℕ} {C : Chunks3}

lemma chunkVals_addrT0 (hF : ChunkFacts Ly L C) {K ρ f : ℕ} (hK : 1 ≤ K) (hL : L = f * K)
    (hρ : ρ < K) (a : Ly.Addr) :
    chunkVals L C (addrT0 L K ρ f C a) = packedT0 K ρ f (chunkVals L C a) := by
  have hmem := packedT0_mem hK hL hρ (hF.rect a)
  unfold addrT0
  rw [hF.valY, Nat.mod_eq_of_lt hmem.2.1]
  rfl

lemma chunkVals_addrS0 (hF : ChunkFacts Ly L C) {K ρ f : ℕ} (a : Ly.Addr) :
    chunkVals L C (addrS0 L K ρ f C a) = packedS0 L K ρ f (chunkVals L C a) := by
  have hmem : packedS0 L K ρ f (chunkVals L C a) ∈ packedRect L :=
    (foldl_bijOn L K ρ f eightOps).mapsTo (hF.rect a)
  have hfst : (packedS0 L K ρ f (chunkVals L C a)).1 = (chunkVals L C a).1 :=
    foldl_fst L K ρ f eightOps (chunkVals L C a)
  simp only [addrS0]
  rw [hF.valZ, hF.valY]
  simp only
  rw [Nat.mod_eq_of_lt hmem.2.1, Nat.mod_eq_of_lt hmem.2.2, ← hfst]

lemma addrT0_invol (hF : ChunkFacts Ly L C) {K ρ f : ℕ} (hK : 1 ≤ K) (hL : L = f * K)
    (hρ : ρ < K) (a : Ly.Addr) : addrT0 L K ρ f C (addrT0 L K ρ f C a) = a := by
  show Ly.blockSet C.py (C.py + L) (addrT0 L K ρ f C a)
    (packedT0 K ρ f (chunkVals L C (addrT0 L K ρ f C a))).2.1 = a
  rw [chunkVals_addrT0 hF hK hL hρ, packedT0_invol]
  unfold addrT0
  rw [blockSet_blockSet, hF.setY]

lemma addrS0_inj (hF : ChunkFacts Ly L C) {K ρ f : ℕ} :
    Function.Injective (addrS0 (Ly := Ly) L K ρ f C) := by
  intro a b hab
  have hcv : chunkVals L C a = chunkVals L C b := by
    have h := congrArg (chunkVals L C) hab
    rw [chunkVals_addrS0 hF, chunkVals_addrS0 hF] at h
    exact (foldl_bijOn L K ρ f eightOps).injOn (hF.rect a) (hF.rect b) h
  funext j
  by_cases hjy : C.py ≤ j.val ∧ j.val < C.py + L
  · rw [← hF.setY a, ← hF.setY b, hcv]
    exact bs_apply_of_mem _ _ _ j hjy
  · by_cases hjz : C.pz ≤ j.val ∧ j.val < C.pz + L
    · rw [← hF.setZ a, ← hF.setZ b, hcv]
      exact bs_apply_of_mem _ _ _ j hjz
    · have ea : addrS0 L K ρ f C a j = a j := by
        simp only [addrS0]
        rw [blockSet_apply_of_not _ _ j hjz, blockSet_apply_of_not _ _ j hjy]
      have eb : addrS0 L K ρ f C b j = b j := by
        simp only [addrS0]
        rw [blockSet_apply_of_not _ _ j hjz, blockSet_apply_of_not _ _ j hjy]
      rw [← ea, ← eb, hab]

/-- Off the exceptional set the repair pull is the identity. -/
lemma repair_fix (hF : ChunkFacts Ly L C) (hAgree : PackedAgreeStmt) {K ρ f : ℕ} (hK : 6 ≤ K)
    (hL : L = f * K) (hρ : ρ < K) (a : Ly.Addr) (hg : packedGood K ρ f (chunkVals L C a)) :
    addrS0 L K ρ f C (addrT0 L K ρ f C a) = a := by
  have hK1 : 1 ≤ K := by omega
  obtain ⟨hpx, hpy, hpz⟩ := hF.rect a
  have hT := hAgree L K ρ f hK hL hρ (chunkVals L C a) hpx hpy hpz hg
  obtain ⟨htx, hty, htz⟩ := packedT0_mem hK1 hL hρ (hF.rect a)
  have hS := (hAgree L K ρ f hK hL hρ (packedT0 K ρ f (chunkVals L C a)) htx hty htz hT.2).1
  rw [packedT0_invol] at hS
  simp only [addrS0]
  rw [chunkVals_addrT0 hF hK1 hL hρ, hS]
  unfold addrT0
  rw [blockSet_blockSet, hF.setY, hF.setZ]

lemma repairStep_WF {β : Type} (hAgree : PackedAgreeStmt) {K ρ f : ℕ}
    (hH : PackedHyps Ly L K ρ f C) (hF : ChunkFacts Ly L C) :
    Step.WF 2 (repairStep (Ly := Ly) (β := β) L K ρ f C) := by
  obtain ⟨hK, hL, hρ, hf, hx, hy, hz, hxy, hxz, hyz, -⟩ := hH
  have hK1 : 1 ≤ K := by omega
  refine ⟨?_, fun a ha => ?_⟩
  · have hinj : Function.Injective (fun a => addrS0 L K ρ f C (addrT0 L K ρ f C a)) :=
      (addrS0_inj hF).comp (Function.LeftInverse.injective (addrT0_invol hF hK1 hL hρ))
    exact Finite.injective_iff_bijective.mp hinj
  · have hg : packedGood K ρ f (chunkVals L C a) := by
      simpa using ha
    exact repair_fix hF hAgree hK hL hρ a hg

end repair

/-- `packedAddProc` is well formed, given the block facts `ChunkFacts`. -/
theorem packedProcWF_of_facts (hAgree : PackedAgreeStmt) {β : Type} {L K ρ f : ℕ}
    {C : Chunks3} (hH : PackedHyps Ly L K ρ f C) (hF : ChunkFacts Ly L C) :
    ProcK.WF 2 0 (packedAddProc (Ly := Ly) (β := β) L K ρ f C) := by
  show ∀ s ∈ @id (List (Step Ly β)) (packedAddProc (Ly := Ly) (β := β) L K ρ f C), Step.WF 2 s
  intro s hs
  have hs' : s ∈ eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) ++
      [repairStep L K ρ f C] ++ topBitSteps L K ρ f C := hs
  rcases List.mem_append.mp hs' with hs1 | hs3
  · rcases List.mem_append.mp hs1 with hs1 | hs2
    · obtain ⟨op, -, hop⟩ := List.mem_flatMap.mp hs1
      exact lineSteps_WF hH hF op s hop
    · rw [List.mem_singleton] at hs2
      subst hs2
      exact repairStep_WF hAgree hH hF
  · exact topBitSteps_WF hH hF s hs3

/-- The block facts `ChunkFacts` follow from `PackedHyps` (three disjoint chunks of binary fields
inside the layout) and the mixed-radix block lemmas of `PackedProcLib`. -/
theorem chunkFacts_of_hyps {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C) :
    ChunkFacts Ly L C := by
  obtain ⟨-, -, -, -, hx, hy, hz, hxy, hxz, hyz, hr⟩ := hH
  have okx : ChunkOK Ly L C.px := ⟨hx, fun i h1 h2 => hr i (Or.inl ⟨h1, h2⟩)⟩
  have oky : ChunkOK Ly L C.py := ⟨hy, fun i h1 h2 => hr i (Or.inr (Or.inl ⟨h1, h2⟩))⟩
  have okz : ChunkOK Ly L C.pz := ⟨hz, fun i h1 h2 => hr i (Or.inr (Or.inr ⟨h1, h2⟩))⟩
  refine ⟨?_, fun a => ⟨chunkVal_lt okx a, chunkVal_lt oky a, chunkVal_lt okz a⟩, ?_, ?_,
    fun a => blockSet_blockVal _ _ a, fun a => blockSet_blockVal _ _ a⟩
  · rintro p (rfl | rfl | rfl)
    · exact chunkRange okx
    · exact chunkRange oky
    · exact chunkRange okz
  · intro a v
    have d1 : chunkVal L C.px (Ly.blockSet C.py (C.py + L) a v) = chunkVal L C.px a :=
      blockVal_blockSet_of_disjoint (by omega) a v
    have d3 : chunkVal L C.pz (Ly.blockSet C.py (C.py + L) a v) = chunkVal L C.pz a :=
      blockVal_blockSet_of_disjoint (by omega) a v
    show (chunkVal L C.px (Ly.blockSet C.py (C.py + L) a v),
        chunkVal L C.py (Ly.blockSet C.py (C.py + L) a v),
        chunkVal L C.pz (Ly.blockSet C.py (C.py + L) a v)) =
      (chunkVal L C.px a, v % 2 ^ L, chunkVal L C.pz a)
    rw [d1, d3, chunkVal_blockSet oky]
  · intro a v
    have d1 : chunkVal L C.px (Ly.blockSet C.pz (C.pz + L) a v) = chunkVal L C.px a :=
      blockVal_blockSet_of_disjoint (by omega) a v
    have d2 : chunkVal L C.py (Ly.blockSet C.pz (C.pz + L) a v) = chunkVal L C.py a :=
      blockVal_blockSet_of_disjoint (by omega) a v
    show (chunkVal L C.px (Ly.blockSet C.pz (C.pz + L) a v),
        chunkVal L C.py (Ly.blockSet C.pz (C.pz + L) a v),
        chunkVal L C.pz (Ly.blockSet C.pz (C.pz + L) a v)) =
      (chunkVal L C.px a, chunkVal L C.py a, v % 2 ^ L)
    rw [d1, d2, chunkVal_blockSet okz]

end PackedProcWFAux

/-- **Well-formedness of the Lemma A.9 (`lem:transfer13`) procedure** (`PackedProcWFStmt`). Under `PackedHyps` (and the
statement's hypothesis `PackedAgreeStmt`), every step of `packedAddProc` is well formed for radix
bound `2`: the interchanges exchange two disjoint chunks of range `2^L` inside the layout, every
shift reads only fields before its target block, and the repair pull `addrS0 ∘ addrT0` is a
bijection fixing every address outside the exceptional set. -/
theorem packedProcWF_holds : PackedProcWFStmt := by
  intro hAgree Ly β L K ρ f C hH
  exact PackedProcWFAux.packedProcWF_of_facts hAgree hH (PackedProcWFAux.chunkFacts_of_hyps hH)

end SubNLogN.Math.Networks
