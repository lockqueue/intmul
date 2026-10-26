/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Header

/-!
# K6 (`Machine/Tables/DropSegs.lean`): dropping a run of `mark`-terminated blocks

**Scope (honest summary).** Infrastructure only: a skip instruction, a guarded decrement
(`decPos`: `v ↦ v - 1` in `ℕ`), and `HT.dropSegs_spec`: a countdown loop that pops `n` blocks
`s ++ [mark]` (no `mark` inside `s`) from a stack, with the exact cost
`C + 1 + n·(C(n+1) + C + 3) + 2·Σ(|s| + 1)`.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2

/-! ## `loopCost` as a sum -/

theorem loopCost_eq_sum (B : ℕ → ℕ) : ∀ n, loopCost B n = 1 + ∑ i ∈ Finset.range n, (B i + 1)
  | 0 => by simp [loopCost]
  | n + 1 => by
    rw [loopCost, loopCost_eq_sum B n, Finset.sum_range_succ]
    omega

theorem sum_range_getD_length (segs : List (List Sym)) :
    ∑ j ∈ Finset.range segs.length, (segs.getD j []).length = (segs.map List.length).sum := by
  induction segs with
  | nil => simp
  | cons s segs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

/-! ## Skip and guarded decrement -/

section Small

variable (I : TB)

/-- Do nothing (one step). -/
def tskip : TP I := .load id

/-- `x ↦ x - 1` (truncated): decrement unless zero. -/
def decPos (x : TL) : TP I :=
  (tiz I x).seq (.ite (fun s => I.iz.obs (I.liz.get s)) (tskip I) (tdc I x))

theorem decPos_closed (x : TL) : (decPos I x).Closed :=
  ⟨callI_closed _ _ _ _, ⟨trivial, callI_closed _ _ _ _⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.tskip_spec (B : TL → List Sym) (ρ : List (TP I)) : HT ρ B (tskip I) B 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨⟨v, S⟩, 1, Eval.load ρ id v S, rfl, le_rfl⟩

theorem HT.decPos_spec (hI : I.Spec Mul C) (x : TL) (B : TL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (TP I)) :
    HT ρ B (decPos I x) (Function.update B x (natSyms (v - 1) ++ r))
      (C + (C * (bitLen v + 1) + 1) + 1) := by
  refine (HT.tizIte_spec hI x B _ v r hr hB (tskip I) (tdc I x) ρ (T₁ := 1)
    (T₂ := C * (bitLen v + 1)) (fun h => ?_) (fun h => ?_)).mono ?_
  · subst h
    refine (HT.tskip_spec B ρ).of_eq ?_ le_rfl
    rw [Nat.zero_sub, ← hB, Function.update_eq_self]
  · obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact HT.tdc_spec hI x B u r hr hB ρ
  · have : max 1 (C * (bitLen v + 1)) ≤ C * (bitLen v + 1) + 1 := max_le (by omega) (by omega)
    omega

end Small

/-! ## Dropping blocks -/

section Drop

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

/-- Countdown states of the block dropper. -/
def dropSt (B : TL → List Sym) (X ctr : TL) (segs : List (List Sym)) (rest : List Sym) (j : ℕ) :
    TL → List Sym :=
  Function.update (Function.update B ctr (natSyms j ++ []))
    X (((segs.drop (segs.length - j)).map (· ++ [Sym.mark])).flatten ++ rest)

/-- Cost of dropping the blocks `segs`. -/
def dropSegsCost (C : ℕ) (segs : List (List Sym)) : ℕ :=
  C + 1 + segs.length * (C * (segs.length + 1) + C + 3) +
    2 * (segs.map fun s => s.length + 1).sum

theorem HT.dropSegs_spec (hI : I.Spec Mul C) (X ctr : TL) (hXc : X ≠ ctr)
    (segs : List (List Sym)) (hsegs : ∀ s ∈ segs, Sym.mark ∉ s) (rest : List Sym)
    (B : TL → List Sym) (hX : B X = (segs.map (· ++ [Sym.mark])).flatten ++ rest)
    (hc : B ctr = natSyms segs.length) (ρ : List (TP I)) :
    HT ρ B (tcd I ctr (dropBlock I X)) (Function.update (Function.update B ctr []) X rest)
      (dropSegsCost C segs) := by
  set n := segs.length with hn
  have hSt : ∀ j, dropSt B X ctr segs rest j ctr = natSyms j ++ [] := fun j => by
    simp [dropSt, Function.update_of_ne hXc.symm]
  have hloop := HT.tcd_spec hI ctr [] TermOK.nil (dropSt B X ctr segs rest) hSt
    (dropBlock I X) n (fun i => 2 * (segs.getD (n - (i + 1)) []).length + 2) ρ (fun i hi => by
      have hi1 : n - (i + 1) < segs.length := by omega
      have hdrop : segs.drop (n - (i + 1)) = segs.getD (n - (i + 1)) [] :: segs.drop (n - i) := by
        rw [List.drop_eq_getElem_cons hi1, List.getD_eq_getElem _ _ hi1]
        congr 2
        omega
      have hpre : (Function.update (dropSt B X ctr segs rest (i + 1)) ctr (natSyms i ++ [])) X =
          segs.getD (n - (i + 1)) [] ++ Sym.mark ::
            (((segs.drop (n - i)).map (· ++ [Sym.mark])).flatten ++ rest) := by
        rw [Function.update_of_ne hXc]
        simp only [dropSt, Function.update_self]
        rw [← hn, hdrop]
        simp
      have hseg : Sym.mark ∉ segs.getD (n - (i + 1)) [] := by
        rw [List.getD_eq_getElem _ _ hi1]
        exact hsegs _ (List.getElem_mem hi1)
      refine (HT.dropBlock_spec X ρ _ _ hseg _ hpre).of_eq ?_ le_rfl
      funext g
      by_cases hgX : g = X
      · rw [hgX, Function.update_self]
        simp only [dropSt, Function.update_self]
        rw [hn]
      · by_cases hgc : g = ctr
        · rw [hgc, Function.update_of_ne hXc.symm, Function.update_self]
          simp only [dropSt, Function.update_of_ne hXc.symm, Function.update_self]
        · rw [Function.update_of_ne hgX, Function.update_of_ne hgc]
          simp only [dropSt, Function.update_of_ne hgX, Function.update_of_ne hgc])
  have hSn : dropSt B X ctr segs rest n = B := by
    simp only [dropSt, ← hn, Nat.sub_self, List.drop_zero, List.append_nil]
    rw [← hX, ← hc, Function.update_eq_self, Function.update_eq_self]
  rw [hSn] at hloop
  refine hloop.of_eq ?_ ?_
  · simp only [dropSt, natSyms_zero, List.nil_append, Nat.sub_zero, List.drop_length,
      List.map_nil, List.flatten_nil]
  · -- cost
    rw [loopCost_eq_sum]
    have h1 : ∀ i ∈ Finset.range n, C * (bitLen (i + 1) + 1) + (2 * (segs.getD (n - (i + 1))
        []).length + 2) + C + 1 ≤ (C * (n + 1) + C + 3) + 2 * (segs.getD (n - 1 - i) []).length :=
      by
      intro i hi
      rw [Finset.mem_range] at hi
      have hb : bitLen (i + 1) ≤ n := le_trans (bitLen_le_self _) (by omega)
      have : C * (bitLen (i + 1) + 1) ≤ C * (n + 1) := Nat.mul_le_mul_left _ (by omega)
      rw [show n - 1 - i = n - (i + 1) by omega]
      omega
    have h2 := Finset.sum_le_sum h1
    have hsplit : ∑ i ∈ Finset.range n, ((C * (n + 1) + C + 3) + 2 * (segs.getD (n - 1 - i)
        []).length) = n * (C * (n + 1) + C + 3) + 2 * (segs.map List.length).sum := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        ← Finset.mul_sum, Finset.sum_range_reflect (fun j => (segs.getD j []).length) n, hn,
        sum_range_getD_length]
    have h3 : (segs.map List.length).sum ≤ (segs.map fun s => s.length + 1).sum :=
      List.sum_le_sum (fun s _ => Nat.le_succ _)
    unfold dropSegsCost
    rw [← hn]
    omega

end Drop

end SubNLogN.Machine.Tables
