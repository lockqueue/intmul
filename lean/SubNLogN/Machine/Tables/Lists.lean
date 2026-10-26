/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Tables

/-!
# K6 (`Machine/Tables/Lists.lean`): list facts about the stored bridge tables

**Scope (honest summary).** Pure lemmas about the table formats of
`SubNLogN/Machine/Contracts/Bridge.lean` (`carrSyms`, `tapBlock`, `solBlock`, `tapTabSyms`,
`solTabSyms`, `tapTabLen`, `solTabLen`) and about `spreadOrder`/`deconvOrder`: no `mark` inside a
block, exact symbol lengths, `|tapBlock t P T i| ≤ prefixProd t i` (the blocks list distinct
lower-digit tuples), hence `|tapTabSyms| ≤ tapTabLen b` and `|solTabSyms| = solTabLen b`.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine

/-! ## Axis orders -/

theorem length_finRange_filter_ne_zero (d : ℕ) :
    ((List.finRange d).filter (fun i : Fin d => decide ((i : ℕ) ≠ 0))).length = d - 1 := by
  cases d with
  | zero => simp
  | succ n =>
    rw [List.finRange_succ, List.filter_cons]
    simp [List.filter_map, Function.comp_def]

theorem length_spreadOrder (d : ℕ) : (spreadOrder d).length = d - 1 := by
  unfold spreadOrder
  rw [List.filter_reverse, List.length_reverse]
  exact length_finRange_filter_ne_zero d

theorem length_deconvOrder (d : ℕ) : (deconvOrder d).length = d - 1 :=
  length_finRange_filter_ne_zero d

/-! ## Record arrays -/

theorem length_twosBits (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem length_crecBits (w : ℕ) (cs : List CInt) : (crecBits w cs).length = 2 * w * cs.length := by
  induction cs with
  | nil => simp [crecBits]
  | cons c cs ih =>
    simp only [crecBits, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [coefBits, length_twosBits]
    ring

theorem length_carrSyms (w : ℕ) (v : List (List CInt)) :
    (carrSyms w v).length = (v.map fun r => 2 * w * r.length + 1).sum := by
  induction v with
  | nil => simp [carrSyms, arrSyms, blk]
  | cons r v ih =>
    simp only [carrSyms, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      List.sum_cons] at ih ⊢
    rw [ih]
    simp [recSyms, length_crecBits]

theorem mark_not_mem_carrSyms (w : ℕ) (v : List (List CInt)) : Sym.mark ∉ carrSyms w v := by
  simp [carrSyms, arrSyms, blk, recSyms]

theorem length_carrSyms_le (w k N : ℕ) (v : List (List CInt)) (hN : v.length ≤ N)
    (hk : ∀ r ∈ v, r.length = k) : (carrSyms w v).length ≤ N * (k * (2 * w) + 1) := by
  rw [length_carrSyms]
  have h : (v.map fun r => 2 * w * r.length + 1) = v.map fun _ => k * (2 * w) + 1 := by
    apply List.map_congr_left
    intro r hr
    rw [hk r hr]
    ring
  rw [h, List.map_const', List.sum_replicate, smul_eq_mul]
  exact Nat.mul_le_mul_right _ hN

theorem length_carrSyms_eq (w k : ℕ) (v : List (List CInt))
    (hk : ∀ r ∈ v, r.length = k) : (carrSyms w v).length = v.length * (k * (2 * w) + 1) := by
  rw [length_carrSyms]
  have h : (v.map fun r => 2 * w * r.length + 1) = v.map fun _ => k * (2 * w) + 1 := by
    apply List.map_congr_left
    intro r hr
    rw [hk r hr]
    ring
  rw [h, List.map_const', List.sum_replicate, smul_eq_mul]

/-! ## Blocks -/

theorem nodup_expAddrs {d : ℕ} (t : Fin d → ℕ) (i : Fin d) : (expAddrs t i).Nodup := by
  unfold expAddrs idxAddrsFreq
  exact ((List.nodup_finRange _).map (Equiv.injective _)).map (Equiv.injective _)

/-- The tap block of axis `i` lists distinct lower-digit tuples, hence at most `A_i` records. -/
theorem length_tapBlock_le {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (T : BridgeTables t) (i : Fin d) :
    (tapBlock t P T i).length ≤ prefixProd t i := by
  unfold tapBlock
  rw [List.length_map]
  set F := (expAddrs t i).filter (fun j => decide (∀ l : Fin d, i ≤ l → (j l : ℕ) = 0)) with hFdef
  have hF : F.Nodup := (nodup_expAddrs t i).filter _
  let g : Idx t → ((l : {l : Fin d // (l : ℕ) < (i : ℕ)}) → Fin (t l)) := fun j l => j l
  have hg : ∀ j ∈ F, ∀ j' ∈ F, g j = g j' → j = j' := by
    intro j hj j' hj' h
    rw [hFdef, List.mem_filter] at hj hj'
    simp only [decide_eq_true_eq] at hj hj'
    funext l
    by_cases hl : (l : ℕ) < (i : ℕ)
    · exact congrFun h ⟨l, hl⟩
    · have hil : i ≤ l := Fin.le_def.mpr (by omega)
      exact Fin.ext ((hj.2 l hil).trans (hj'.2 l hil).symm)
  have hmap : (F.map g).Nodup := hF.map_on hg
  calc F.length = (F.map g).length := (List.length_map _).symm
    _ ≤ Fintype.card ((l : {l : Fin d // (l : ℕ) < (i : ℕ)}) → Fin (t l)) := hmap.length_le_card
    _ = prefixProd t i := by
      rw [Fintype.card_pi]
      simp only [Fintype.card_fin]
      unfold prefixProd
      exact (Finset.prod_subtype (Finset.univ.filter (fun l : Fin d => (l : ℕ) < (i : ℕ)))
        (fun l => by simp) (fun l => t l)).symm

theorem length_tapRec {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (tap : ℕ → ℤ → ℂ) (i : Fin d) (a : ℕ) :
    (tapRec t P tap i a).length = (tapOffsets t P i).length := by
  simp [tapRec]

theorem length_solBlock {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (T : BridgeTables t) (i : Fin d) :
    (solBlock t P T i).length = t i := by
  simp [solBlock]

/-! ## Table stacks as lists of blocks -/

/-- The tap blocks (without their `mark`s), in stack order. -/
noncomputable def tapSegs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    List (List Sym) :=
  (spreadOrder d).map fun i => carrSyms wT (tapBlock t P T i)

/-- The solver blocks (without their `mark`s), in stack order. -/
noncomputable def solSegs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    List (List Sym) :=
  (deconvOrder d).map fun i => carrSyms wT (solBlock t P T i)

theorem tapTabSyms_eq_segs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    tapTabSyms wT P t T = ((tapSegs wT P t T).map (· ++ [Sym.mark])).flatten := by
  simp [tapTabSyms, tapSegs, List.flatMap, Function.comp_def]

theorem solTabSyms_eq_segs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    solTabSyms wT P t T = ((solSegs wT P t T).map (· ++ [Sym.mark])).flatten := by
  simp [solTabSyms, solSegs, List.flatMap, Function.comp_def]

theorem mark_not_mem_tapSegs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    ∀ s ∈ tapSegs wT P t T, Sym.mark ∉ s := by
  intro s hs
  simp only [tapSegs, List.mem_map] at hs
  obtain ⟨i, -, rfl⟩ := hs
  exact mark_not_mem_carrSyms _ _

theorem mark_not_mem_solSegs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    ∀ s ∈ solSegs wT P t T, Sym.mark ∉ s := by
  intro s hs
  simp only [solSegs, List.mem_map] at hs
  obtain ⟨i, -, rfl⟩ := hs
  exact mark_not_mem_carrSyms _ _

theorem length_tapSegs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    (tapSegs wT P t T).length = d - 1 := by
  simp [tapSegs, length_spreadOrder]

theorem length_solSegs {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    (solSegs wT P t T).length = d - 1 := by
  simp [solSegs, length_deconvOrder]

/-- Total payload length of the tap blocks plus their marks is at most `tapTabLen b`. -/
theorem sum_tapSegs_le (b : BrPar) (T : BridgeTables b.t) :
    ((tapSegs b.wT b.P b.t T).map fun s => s.length + 1).sum ≤ tapTabLen b := by
  unfold tapSegs tapTabLen
  rw [List.map_map]
  apply List.sum_le_sum
  intro i _
  simp only [Function.comp_apply]
  have := length_carrSyms_le b.wT (tapOffsets b.t b.P i).length (prefixProd b.t i)
    (tapBlock b.t b.P T i) (length_tapBlock_le _ _ _ _) (fun r hr => by
      simp only [tapBlock, List.mem_map] at hr
      obtain ⟨j, -, rfl⟩ := hr
      exact length_tapRec _ _ _ _ _)
  omega

theorem sum_solSegs_eq (b : BrPar) (T : BridgeTables b.t) :
    ((solSegs b.wT b.P b.t T).map fun s => s.length + 1).sum = solTabLen b := by
  unfold solSegs solTabLen
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [length_carrSyms_eq b.wT 3 (solBlock b.t b.P T i) (fun r hr => by
      simp only [solBlock, List.mem_map] at hr
      obtain ⟨u, -, rfl⟩ := hr
      simp [solRec]), length_solBlock]

end SubNLogN.Machine.Tables
