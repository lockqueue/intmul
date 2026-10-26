import SubNLogN.Math.Networks.AppCSafe
import SubNLogN.Math.Networks.Proofs.PackedProcWF

/-!
# Proof of `PackedProcClassSafeStmt` (class safety of the Lemma A.9 (`lem:transfer13`) procedure `packedAddProc`)

We prove `packedProcClassSafe_holds : PackedProcClassSafeStmt` (statement in `AppCSafe.lean`): under
`PackedHyps` and if the row field of the class `c` lies outside the three chunks, every step of
`packedAddProc L K ρ f C` is class safe in `c`.

Every pull of the procedure changes only fields of the three chunks:
* `swapBlocks pt pr L` (`pt ∈ {py, pz}`, `pr = C.right`, which is a chunk position) changes only
  the two chunk blocks;
* the line shifts change only the block `[pr, pr + L)`; the top-bit shift changes only the field
  `pr + L − 1 − j` with `j = ρ + (f−1)K < L`, inside `[pr, pr + L)`;
* the repair pull `addrS0 ∘ addrT0` changes only the `y` and `z` blocks.
So every pull fixes the row field, and membership in `c` (which depends only on the row field) is
preserved in both directions (`preserves_of_row`).
-/

namespace SubNLogN.Math.Networks

open Model

namespace PackedSafeAux

open PackedProcAux PackedProcWFAux

variable {Ly : Layout}

/-- A map fixing the row field preserves membership in the class, in both directions. -/
lemma preserves_of_row (c : RowClass Ly) (g : Ly.Addr → Ly.Addr)
    (h : ∀ x, g x c.row = x c.row) : PreservesClass c g := by
  intro x
  unfold RowClass.mem
  rw [h x]

/-- The rightmost chunk position is one of the three chunk positions, so a row outside the three
chunks is outside the rightmost one. -/
lemma row_out_right {C : Chunks3} {L r : ℕ} (hx : r < C.px ∨ C.px + L ≤ r)
    (hy : r < C.py ∨ C.py + L ≤ r) (hz : r < C.pz ∨ C.pz + L ≤ r) :
    r < C.right ∨ C.right + L ≤ r := by
  rcases right_cases C with h | h | h <;> rw [h] <;> assumption

lemma swapPullMap_row (c : RowClass Ly) {pt pr L : ℕ}
    (h1 : c.row.val < pt ∨ pt + L ≤ c.row.val) (h2 : c.row.val < pr ∨ pr + L ≤ c.row.val)
    (x : Ly.Addr) : swapPullMap Ly pt pr L x c.row = x c.row :=
  swapPull_apply_of_not (pt := pt) (pr := pr) (L := L) x c.row (by omega) (by omega)

lemma swp_safe {β : Type} (c : RowClass Ly) {pt pr L : ℕ}
    (h1 : c.row.val < pt ∨ pt + L ≤ c.row.val) (h2 : c.row.val < pr ∨ pr + L ≤ c.row.val)
    (s : Step Ly β)
    (hs : s ∈ (if pt = pr then [] else [Step.swapBlocks pt pr L] : List (Step Ly β))) :
    Step.ClassSafe c s := by
  split_ifs at hs
  · simp at hs
  · rw [List.mem_singleton] at hs
    subst hs
    exact preserves_of_row c _ (swapPullMap_row c h1 h2)

lemma shift_safe {β : Type} (c : RowClass Ly) {t₀ t₁ : ℕ} (off : Ly.Addr → ℕ)
    (hc : c.row.val < t₀ ∨ t₁ ≤ c.row.val) :
    Step.ClassSafe c (Step.elem (Elem.shift t₀ t₁ off) : Step Ly β) :=
  preserves_of_row c _ (fun x => shift_apply_of_not off x c.row (by omega))

lemma lineSteps_safe {β : Type} {L K ρ f : ℕ} {C : Chunks3} (c : RowClass Ly)
    (hx : c.row.val < C.px ∨ C.px + L ≤ c.row.val) (hy : c.row.val < C.py ∨ C.py + L ≤ c.row.val)
    (hz : c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) (op : Bool × ℤ × ℕ) :
    ∀ s ∈ lineSteps (Ly := Ly) (β := β) L K ρ f C op, Step.ClassSafe c s := by
  have hr := row_out_right hx hy hz
  obtain ⟨t, e, q⟩ := op
  intro s hs
  cases t
  · simp only [lineSteps, Bool.false_eq_true, ↓reduceIte, List.mem_append,
      List.mem_singleton] at hs
    rcases hs with (hs | rfl) | hs
    · exact swp_safe c hz hr s hs
    · exact shift_safe c _ hr
    · exact swp_safe c hz hr s hs
  · simp only [lineSteps, ↓reduceIte, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | rfl) | hs
    · exact swp_safe c hy hr s hs
    · exact shift_safe c _ hr
    · exact swp_safe c hy hr s hs

lemma topBitSteps_safe {β : Type} {L K ρ f : ℕ} {C : Chunks3} (hH : PackedHyps Ly L K ρ f C)
    (c : RowClass Ly) (hx : c.row.val < C.px ∨ C.px + L ≤ c.row.val)
    (hy : c.row.val < C.py ∨ C.py + L ≤ c.row.val) (hz : c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) :
    ∀ s ∈ topBitSteps (Ly := Ly) (β := β) L K ρ f C, Step.ClassSafe c s := by
  obtain ⟨-, hL, hρ, hf, -⟩ := hH
  have hr := row_out_right hx hy hz
  have hj : ρ + (f - 1) * K < L := by
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    rw [hL, Nat.add_sub_cancel, add_mul, one_mul]
    omega
  intro s hs
  simp only [topBitSteps, List.mem_append, List.mem_singleton] at hs
  rcases hs with (hs | rfl) | hs
  · exact swp_safe c hy hr s hs
  · exact shift_safe c _ (by omega)
  · exact swp_safe c hy hr s hs

lemma repair_safe {β : Type} {L K ρ f : ℕ} {C : Chunks3} (c : RowClass Ly)
    (hy : c.row.val < C.py ∨ C.py + L ≤ c.row.val) (hz : c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) :
    Step.ClassSafe c (repairStep (Ly := Ly) (β := β) L K ρ f C) := by
  show PreservesClass c (fun a => addrS0 L K ρ f C (addrT0 L K ρ f C a))
  refine preserves_of_row c _ (fun a => ?_)
  have e1 : ∀ (x : Ly.Addr) (v : ℕ), Ly.blockSet C.py (C.py + L) x v c.row = x c.row :=
    fun x v => blockSet_apply_of_not x v c.row (by omega)
  have e2 : ∀ (x : Ly.Addr) (v : ℕ), Ly.blockSet C.pz (C.pz + L) x v c.row = x c.row :=
    fun x v => blockSet_apply_of_not x v c.row (by omega)
  simp only [addrS0, addrT0]
  rw [e2, e1, e1]

end PackedSafeAux

open PackedSafeAux in
/-- **Class safety of the Lemma A.9 (`lem:transfer13`) procedure** (`PackedProcClassSafeStmt`). Under `PackedHyps`, if the row
field of `c` lies outside the three chunks, every step of `packedAddProc` is class safe in `c`: all
its pulls fix the row field. -/
theorem packedProcClassSafe_holds : PackedProcClassSafeStmt := by
  intro Ly β L K ρ f C hH c hcx hcy hcz
  have key : ∀ s ∈ eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) ++
      [repairStep L K ρ f C] ++ topBitSteps L K ρ f C, Step.ClassSafe c s := by
    intro s hs
    rcases List.mem_append.mp hs with hs1 | hs3
    · rcases List.mem_append.mp hs1 with hs1 | hs2
      · obtain ⟨op, -, hop⟩ := List.mem_flatMap.mp hs1
        exact lineSteps_safe c hcx hcy hcz op s hop
      · rw [List.mem_singleton] at hs2
        subst hs2
        exact repair_safe c hcy hcz
    · exact topBitSteps_safe hH c hcx hcy hcz s hs3
  exact List.forall_iff_forall_mem.mpr key

end SubNLogN.Math.Networks
