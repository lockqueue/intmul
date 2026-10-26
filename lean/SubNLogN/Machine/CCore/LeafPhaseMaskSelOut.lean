/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelScanDefs

/-!
# C-core phase leaf, record-wise sign selection: moving the selection out (`LeafPhaseMaskSelOut.lean`)

**Scope (honest summary).** `msOutLoop Out Dst` moves reversed records (`sep :: bits.reverse`, last
record on top) from `Out` onto `Dst`, restoring the records and their order (`runs_msOutLoop`,
proved); `selOut_eq` rewrites the select loop's output in this form; `selRecs_eq` identifies the
selection of `MaskSelStmt` with the `mapIdx` form.
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP
open SubNLogN.Machine.CCore.LeafScalarAux

variable {K : Type}

/-- Move all reversed records from `Out` onto `Dst`. -/
def msOutLoop (Out Dst : K) : PProg K :=
  .seq (peekT Out) (.loop (fun v => isSepO v.t) (.seq (msMvRecBack Out Dst) (peekT Out)))

theorem closed_msOutLoop (Out Dst : K) : (msOutLoop Out Dst).Closed :=
  WP.W9comp.closed_seq (closed_peekT Out) (WP.W9comp.closed_seq (closed_msMvRecBack Out Dst)
    (closed_peekT Out))

/-- A reversed record. -/
def recRev (p : List Bool) : List Sym := Sym.sep :: p.reverse.map Sym.bit

theorem whileCost_le_sum {α : Type} (Tp : ℕ) (Tb : List α → α → List α → ℕ) (g : α → ℕ)
    (hg : ∀ d x r, Tb d x r ≤ g x) :
    ∀ rest done, whileCost Tp Tb done rest ≤ (rest.map fun x => g x + Tp + 1).sum + 1
  | [], _ => by simp [whileCost]
  | x :: rest, done => by
    have h1 := whileCost_le_sum Tp Tb g hg rest (done ++ [x])
    have h2 := hg done x rest
    simp only [whileCost, List.map_cons, List.sum_cons]
    omega

theorem length_arrSyms (rs : List (List Bool)) :
    (arrSyms rs).length = (rs.map fun p => p.length + 1).sum := by
  induction rs with
  | nil => simp [arrSyms, blk]
  | cons p rs ih =>
    simp only [arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      List.sum_cons] at ih ⊢
    rw [ih]
    simp [recSyms]

theorem sum_out_le : ∀ rs : List (List Bool),
    (rs.map fun x => 3 * x.length + 6 + 1 + 1).sum ≤ 8 * (rs.map fun p => p.length + 1).sum
  | [] => by simp
  | p :: rs => by
    have ih := sum_out_le rs
    simp only [List.map_cons, List.sum_cons]
    omega

theorem map_mapIdx_m {α β γ : Type} (g : β → γ) : ∀ (l : List α) (f : ℕ → α → β),
    (l.mapIdx f).map g = l.mapIdx (fun i a => g (f i a))
  | [], _ => rfl
  | a :: l, f => by
    simp only [List.mapIdx_cons, List.map_cons, map_mapIdx_m g l]

section Runs

variable [DecidableEq K]

theorem runs_msOutLoop {Out Dst : K} (hne : Out ≠ Dst) (rs : List (List Bool))
    (S : K → List Sym) (hOut : S Out = (rs.map recRev).flatten) :
    Runs (msOutLoop Out Dst) S
      (Function.update (Function.update S Out []) Dst ((rs.reverse.map recSyms).flatten ++ S Dst))
      (fun _ => True) (8 * (arrSyms rs).length + 2) := by
  let st : List (List Bool) → List (List Bool) → K → List Sym := fun done rest =>
    Function.update (Function.update S Out (rest.map recRev).flatten) Dst
      ((done.reverse.map recSyms).flatten ++ S Dst)
  have hw := runs_while (pk := peekT Out) (body := msMvRecBack Out Dst)
    (c := fun v => isSepO v.t) st 1 (fun _ x _ => 3 * x.length + 6)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT Out (st done rest)) (fun v hv => ?_) le_rfl
      show isSepO v.t = !rest.isEmpty
      rw [hv]
      simp only [st]
      rw [Function.update_of_ne hne, Function.update_self]
      rcases rest with _ | ⟨x, rest⟩
      · rfl
      · simp [recRev])
    (fun done x rest => by
      have h := runs_msMvRecBack hne x (rest.map recRev).flatten (st done (x :: rest))
        (by
          rcases rest with _ | ⟨y, rest⟩
          · exact TermOK.nil
          · exact TermOK.cons rfl _)
        (by
          simp only [st]
          rw [Function.update_of_ne hne, Function.update_self]
          simp [recRev])
      refine WP.W9comp.runs_congr h ?_
      funext k
      simp only [st, Function.update_apply]
      split_ifs <;> simp_all)
    rs []
  have h0 : st [] rs = S := by
    simp only [st, List.reverse_nil, List.map_nil, List.flatten_nil, List.nil_append]
    rw [← hOut, Function.update_eq_self, Function.update_eq_self]
  rw [h0] at hw
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have hc := whileCost_le_sum 1 (fun (_ : List (List Bool)) (x : List Bool) _ => 3 * x.length + 6)
      (fun x => 3 * x.length + 6) (fun _ _ _ => le_rfl) rs []
    rw [length_arrSyms]
    have hs := sum_out_le rs
    omega

end Runs

/-- The select loop's output, in the form consumed by `runs_msOutLoop`. -/
theorem selOut_eq (G : List Bool) (S : ℕ) (ps : List (List Bool × List Bool)) :
    selOut G S ps = (((ps.mapIdx fun j pr =>
      if G.getD ((j / S) % G.length) false then pr.2 else pr.1).reverse).map recRev).flatten := by
  unfold selOut
  rw [List.map_reverse, map_mapIdx_m]
  rfl

/-- The selection of `MaskSelStmt` in `mapIdx` form. -/
theorem selRecs_eq (b : ℕ → Bool) (v vn : List (List Bool)) (h : v.length = vn.length) :
    selRecs b v vn = (v.zip vn).mapIdx fun j pr => if b j then pr.2 else pr.1 := by
  apply List.ext_getElem
  · simp [selRecs, h]
  · intro i h1 h2
    simp only [selRecs, List.getElem_map, List.getElem_range, List.getElem_mapIdx,
      List.getElem_zip]
    have hv : i < v.length := by simpa [selRecs] using h1
    have hvn : i < vn.length := by omega
    split_ifs <;> simp [List.getD_eq_getElem?_getD, hv, hvn]

end SubNLogN.Machine.CCore.PhaseMaskAux
