/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimLayout
import SubNLogN.Machine.AppC.C5NetSimGate
import SubNLogN.Math.Networks.LayoutEncoding2

/-!
# Proposition A.7 network simulation, part K (`AppC/C5NetSimK.lean`): outer shears, top swap, decoding

On the node layout `L = nodeLayout q e N0 R N1 G B` (`e = mH^(k'+1)`, `AppC/C5NetSimLayout.lean`) in
its top class (the whole array), with any payload `β`:
* `preOpsK = [hdShift i i true]_i` (= `preOps` in `AppC/C5NetSimShape.lean`, by `rfl`), the op list for
  `subHSteps` (`D ← D − H`, `Math/Networks/AppCProc.lean`; simulation `pre_sim` proved in `AppC/C5NetSimK2.lean`);
* `postOpsK = [unit D i (-1), hdShift i i false]_i` (= `postOps`), the op list for `hMinusDSteps`
  (`D ← H − D`; simulation `post_sim` proved in `AppC/C5NetSimK2.lean`);
* `top_swap`: `Model.Step.swapBlocks 3 (4 + e) e` encodes to `permByInv (swapMap q mH (k'+1) G B)`;
* `enc_decode`: decoding a list of width-`w` bit records into `Rec w`-valued arrays and encoding
  back is the identity.
Generic tools: `foldl_sim` (a list of steps matching a list of stream ops, entrywise, encodes to
the op list's `macroMap`), `elem_sim` (an elementary step with a `PullMatch` index map).
Paper: Proposition A.7 (`prop:transfer11`) (the three outer shears). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAuxK

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step Elem RowClass)
open SubNLogN.Machine.C5.NetAux

/-- The op list of `D ← D − H` (`= NetAux.preOps`). -/
def preOpsK : List (StreamOp mH) := (List.finRange mH).map fun i => .hdShift i i true

/-- The op list of `D ← H − D` (`= NetAux.postOps`). -/
def postOpsK : List (StreamOp mH) :=
  (List.finRange mH).flatMap fun i => [.unit .D i (-1), .hdShift i i false]

theorem forall₂_flatMapK {ι α γ : Type} {Rl : α → γ → Prop} (l : List ι) (f : ι → List α)
    (g : ι → List γ) (h : ∀ x ∈ l, List.Forall₂ Rl (f x) (g x)) :
    List.Forall₂ Rl (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h x (List.mem_cons_self ..))
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-! ## `permByInv` on arbitrary lists -/

theorem permByInv_id' {α : Type} [Inhabited α] (v : List α) : permByInv id v = v := by
  simp only [permByInv]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range, id]
  rw [List.getD_eq_getElem _ _ h2]

theorem permByInv_comp' {α : Type} [Inhabited α] (f g : ℕ → ℕ) (v : List α)
    (hf : ∀ y < v.length, f y < v.length) :
    permByInv f (permByInv g v) = permByInv (g ∘ f) v := by
  simp only [permByInv, List.length_map, List.length_range]
  refine List.map_congr_left (fun y hy => ?_)
  rw [List.mem_range] at hy
  rw [List.getD_eq_getElem _ _ (by simpa using hf y hy)]
  simp

theorem permByInv_congr {α : Type} [Inhabited α] {f g : ℕ → ℕ} (v : List α)
    (h : ∀ y < v.length, f y = g y) : permByInv f v = permByInv g v := by
  simp only [permByInv]
  refine List.map_congr_left (fun y hy => ?_)
  rw [List.mem_range] at hy
  rw [h y hy]

/-! ## Decoding -/

/-- Decoding a list of width-`w` records into an array and encoding back is the identity. -/
theorem enc_decode (L : Layout) (w : ℕ) (v : List (List Bool)) (hv : v.length = L.card)
    (hw : ∀ p ∈ v, p.length = w) :
    (L.enc (fun x => toRec w (v.getD (L.lexEquiv x).val []))).map ofRec = v := by
  apply List.ext_getElem
  · rw [List.length_map, Model.Layout.enc_length, hv]
  · intro n h1 h2
    rw [List.getElem_map, Model.Layout.enc_getElem]
    simp only [Equiv.apply_symm_apply]
    rw [List.getD_eq_getElem _ _ h2, ofRec_toRec _ (hw _ (List.getElem_mem h2))]

section Sim

variable (q k' N0 R N1 G B : ℕ) {β : Type} [Inhabited β]

/-- Running a step in the top class is running it. -/
theorem runIn_top (s : Step (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) β)
    (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → β) :
    s.runIn (RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A = s.run A := by
  funext x
  simp only [Model.Step.runIn,
    if_pos ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).top_mem (rowF q (mH ^ (k' + 1)) N0 R N1 G B) x)]

/-- An elementary step with a matching index map. -/
theorem elem_sim (e : Elem (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)) (f : ℕ → ℕ)
    (hpm : PullMatch (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) e.pull f)
    (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → β) :
    (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
        ((Step.elem e : Step (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) β).runIn
          (RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) =
      permByInv f ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A) := by
  rw [runIn_top]
  exact (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc_comp A e.pull f (fun y h => (hpm y h).symm)

/-- A list of steps matching a list of stream ops entrywise encodes to the op list's `macroMap`. -/
theorem foldl_sim (hq : 1 ≤ q) (ss : List (Step (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) β))
    (os : List (StreamOp mH))
    (h : List.Forall₂ (fun s o => ∀ A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → β,
      (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
          (s.runIn (RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) =
        permByInv (streamMap q mH o (k' + 1) N1 G B)
          ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A)) ss os) :
    ∀ A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → β,
      (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
          (ss.foldl (fun A s => s.runIn (RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) A) =
        permByInv (macroMap q mH os (k' + 1) N1 G B)
          ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A) := by
  induction h with
  | nil =>
    intro A
    rw [List.foldl_nil, show macroMap q mH [] (k' + 1) N1 G B = id from rfl, permByInv_id']
  | @cons s o ss os hso _ ih =>
    intro A
    rw [List.foldl_cons, ih, hso A, permByInv_comp' _ _ _ ?_, ← macroMap_cons]
    intro y hy
    rw [Model.Layout.enc_length] at hy ⊢
    exact macroMap_lt q mH os (k' + 1) N1 G B _ hq (by omega)
      (by rw [nl_card]; exact Dvd.intro_left _ rfl) y hy

/-- The interchange of the two chunks of `nodeLayout q e …` (any `e`) has index map
`swapFieldsInv (q^e) G (q^e) B`. -/
theorem swap_gen (e : ℕ) (hq : 0 < q) (hG : 0 < G) (hB : 0 < B)
    (A : (nodeLayout q e N0 R N1 G B).Addr → β) :
    (nodeLayout q e N0 R N1 G B).enc
        ((Step.swapBlocks 3 (4 + e) e : Step (nodeLayout q e N0 R N1 G B) β).run A) =
      permByInv (swapFieldsInv (q ^ e) G (q ^ e) B) ((nodeLayout q e N0 R N1 G B).enc A) := by
  have hn : (nodeLayout q e N0 R N1 G B).n = 5 + 2 * e := rfl
  have ht : 3 + e ≤ (nodeLayout q e N0 R N1 G B).n := by rw [hn]; omega
  have hs : 4 + e + e ≤ (nodeLayout q e N0 R N1 G B).n := by rw [hn]; omega
  have hH : (nodeLayout q e N0 R N1 G B).blockRange 3 (3 + e) = q ^ e := by
    rw [br_chunk q e N0 R N1 G B 3 (3 + e) (by omega) (Or.inl ⟨le_rfl, le_rfl⟩),
      Nat.add_sub_cancel_left]
  have hD : (nodeLayout q e N0 R N1 G B).blockRange (4 + e) (4 + e + e) = q ^ e := by
    rw [br_chunk q e N0 R N1 G B (4 + e) (4 + e + e) (by omega) (Or.inr ⟨le_rfl, by omega⟩),
      Nat.add_sub_cancel_left]
  have hGr : (nodeLayout q e N0 R N1 G B).blockRange (3 + e) (4 + e) = G := by
    rw [show 4 + e = 3 + e + 1 by omega, br_single' q e N0 R N1 G B (3 + e) (by omega), nodeR_G]
  have hBr : (nodeLayout q e N0 R N1 G B).blockRange (4 + e + e) (nodeLayout q e N0 R N1 G B).n =
      B := by
    rw [hn, show 5 + 2 * e = 4 + e + e + 1 by omega,
      br_single' q e N0 R N1 G B (4 + e + e) (by omega), show 4 + e + e = 4 + 2 * e by omega,
      nodeR_B]
  rw [Model.enc_run_swapBlocks ht hs A]
  refine permByInv_congr _ (fun y _ => ?_)
  rw [Model.swapIdx_eq_swapFieldsInv (by omega : 3 + e ≤ 4 + e) hs (hH.trans hD.symm)
    ⟨by rw [hH]; exact pow_pos hq e, by rw [hGr]; exact hG, by rw [hBr]; exact hB⟩ y, hD, hGr, hBr]
  rfl

/-- **The level interchange**: `Model.Step.swapBlocks 3 (4 + e) e` on the top class encodes to
`permByInv (swapMap q mH (k'+1) G B)`. -/
theorem top_swap (hq : 0 < q) (hG : 0 < G) (hB : 0 < B)
    (A : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).Addr → β) :
    (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc
        ((Step.swapBlocks 3 (4 + mH ^ (k' + 1)) (mH ^ (k' + 1)) :
          Step (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B) β).runIn
          (RowClass.top (rowF q (mH ^ (k' + 1)) N0 R N1 G B)) A) =
      permByInv (swapMap q mH (k' + 1) G B) ((nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).enc A) := by
  rw [runIn_top]
  exact swap_gen q N0 R N1 G B (mH ^ (k' + 1)) hq hG hB A

end Sim

end SubNLogN.Machine.C5.NetAuxK
