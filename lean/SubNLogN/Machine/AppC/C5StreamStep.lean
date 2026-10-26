/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Leaves
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# Proposition A.7 stream kernel, part 1: in-place steps and their composition

`StepStmt q m F` has the shape of `C5StreamStmt q m op` (`AppC/C5Leaves.lean`), but with an
arbitrary family of inverse address maps `F k N1 G B` in place of `streamMap q m op`. A kernel
for `F` rewrites the array on stack `0` in place into `permByInv (F k N1 G B) v` and restores
every other stack. The counters `k, N1, G, B` on stacks `1`-`4` are restored. The cost is
`C·(V + 1)`. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Results (namespace `SubNLogN.Machine.C5.StreamAux`):
* `c5StreamStmt_of_step`: `C5StreamStmt q m op` is `op.Valid q → StepStmt q m (streamMap q m op)`.
* `stepStmt_id`: the identity map.
* `stepStmt_congr`: maps that agree on the index range.
* `stepStmt_comp`: sequential composition. Running `F` and then `F'` realizes
  `y ↦ F (F' y)`, provided both maps send the index range into itself (`InRange`).
* `stepStmt_iter`: `n`-fold repetition.
-/

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine

/-- In-place step contract on the Proposition A.7 interface, with inverse address maps `F k N1 G B`. -/
def StepStmt (q m : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (k Rt N1 G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B → v.length = Rt * rowSize q m k N1 G B →
      (∀ p ∈ v, p.length = w) → BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms k ++ r1 →
      S (.inl 2) = natSyms N1 ++ r2 → S (.inl 3) = natSyms G ++ r3 → S (.inl 4) = natSyms B ++ r4 →
      Runs P S (Function.update S (.inl 0) (arrSyms (permByInv (F k N1 G B) v) ++ rest))
        (fun _ => True) (C * (vol v + 1))

/-- `F` maps the index range `[0, Rt·rowSize)` into itself, for every valid descriptor. -/
def InRange (q m : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ k Rt N1 G B y, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
    y < Rt * rowSize q m k N1 G B → F k N1 G B y < Rt * rowSize q m k N1 G B

theorem c5StreamStmt_of_step {q m : ℕ} {op : StreamOp m}
    (h : op.Valid q → StepStmt q m (streamMap q m op)) : C5StreamStmt q m op := h

/-! ## `permByInv` facts -/

section PermFacts

variable {α : Type} [Inhabited α]

theorem permByInv_congr' {f g : ℕ → ℕ} (v : List α) (h : ∀ y < v.length, f y = g y) :
    permByInv f v = permByInv g v := by
  unfold permByInv
  refine List.map_congr_left fun y hy => ?_
  rw [h y (List.mem_range.1 hy)]

theorem permByInv_comp' (f g : ℕ → ℕ) (v : List α) (hg : ∀ y < v.length, g y < v.length) :
    permByInv g (permByInv f v) = permByInv (fun y => f (g y)) v := by
  unfold permByInv
  rw [List.length_map, List.length_range]
  refine List.map_congr_left fun y hy => ?_
  have hy' := List.mem_range.1 hy
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hg y hy'),
    List.getElem_map, List.getElem_range]

theorem permByInv_id' (v : List α) : permByInv (fun y => y) v = v := by
  unfold permByInv
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ h2

end PermFacts

theorem inl_ne' {E : Type} {i j : Fin 5} (h : i ≠ j) : (Sum.inl i : KLoc (Fin 5) E) ≠ Sum.inl j :=
  fun e => h (Sum.inl_injective e)

/-! ## Identity, congruence -/

theorem stepStmt_id (q m : ℕ) : StepStmt q m (fun _ _ _ _ y => y) := by
  refine ⟨1, fun _ => ⟨Empty, inferInstance, inferInstance, NatArith.Reg, .load id,
    inferInstance, inferInstance, by simp [Prog.Closed, Prog.FreeBelow], ?_⟩⟩
  intro k Rt N1 G B w v rest r1 r2 r3 r4 S _ _ _ _ _ _ _ _ _ _ _ _ hS0 _ _ _ _
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (NatArith.runs_loadId S) ?_)
    (fun _ h => h) (by omega)
  have hp : permByInv ((fun (_ _ _ _ : ℕ) (y : ℕ) => y) k N1 G B) v = v := permByInv_id' v
  rw [hp, ← hS0, Function.update_eq_self]

theorem stepStmt_congr {q m : ℕ} {F F' : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hF : ∀ k Rt N1 G B y, 1 ≤ k → 1 ≤ Rt → 1 ≤ N1 → 1 ≤ G → 1 ≤ B →
      y < Rt * rowSize q m k N1 G B → F k N1 G B y = F' k N1 G B y)
    (h : StepStmt q m F) : StepStmt q m F' := by
  obtain ⟨C, h⟩ := h
  refine ⟨C, fun p => ?_⟩
  obtain ⟨E, i1, i2, R, P, hRf, hRn, hPc, hP⟩ := h p
  refine ⟨E, i1, i2, R, P, hRf, hRn, hPc, ?_⟩
  intro k Rt N1 G B w v rest r1 r2 r3 r4 S hk hRt hN1 hG hB hlen hw hrest h1 h2 h3 h4
    hS0 hS1 hS2 hS3 hS4
  have := hP k Rt N1 G B w v rest r1 r2 r3 r4 S hk hRt hN1 hG hB hlen hw hrest h1 h2 h3 h4
    hS0 hS1 hS2 hS3 hS4
  rwa [permByInv_congr' v (fun y hy => hF k Rt N1 G B y hk hRt hN1 hG hB (hlen ▸ hy))] at this

theorem inRange_id (q m : ℕ) : InRange q m (fun _ _ _ _ y => y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ hy => hy

theorem inRange_comp {q m : ℕ} {F F' : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} (h1 : InRange q m F)
    (h2 : InRange q m F') : InRange q m (fun k N1 G B y => F k N1 G B (F' k N1 G B y)) :=
  fun k Rt N1 G B y hk hRt hN1 hG hB hy =>
    h1 k Rt N1 G B _ hk hRt hN1 hG hB (h2 k Rt N1 G B y hk hRt hN1 hG hB hy)

/-! ## Sequential composition -/

theorem stepStmt_comp {q m : ℕ} {F F' : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (h1 : StepStmt q m F) (h2 : StepStmt q m F') (hr1 : InRange q m F) (hr2 : InRange q m F') :
    StepStmt q m (fun k N1 G B y => F k N1 G B (F' k N1 G B y)) := by
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  refine ⟨C1 + C2, fun p => ?_⟩
  obtain ⟨E1, _, _, R1, P1, hR1f, hR1n, hP1c, hP1⟩ := h1 p
  obtain ⟨E2, _, _, R2, P2, hR2f, hR2n, hP2c, hP2⟩ := h2 p
  have hι1 : Function.Injective (Sum.map id Sum.inl : KLoc (Fin 5) E1 → KLoc (Fin 5) (E1 ⊕ E2)) :=
    Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩
  have hι2 : Function.Injective (Sum.map id Sum.inr : KLoc (Fin 5) E2 → KLoc (Fin 5) (E1 ⊕ E2)) :=
    Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩
  refine ⟨E1 ⊕ E2, inferInstance, inferInstance, R1 × R2,
    .seq (callInj (Sum.map id Sum.inl) (Lens.fst R1 R2) P1)
      (callInj (Sum.map id Sum.inr) (Lens.snd R1 R2) P2),
    by have := hR1f; have := hR2f; infer_instance,
    by have := hR1n; have := hR2n; infer_instance,
    ⟨closed_callInj _ _ hP1c, closed_callInj _ _ hP2c⟩, ?_⟩
  intro k Rt N1 G B w v rest r1 r2 r3 r4 S hk hRt hN1 hG hB hlen hw hrest hr1' hr2' hr3' hr4'
    hS0 hS1 hS2 hS3 hS4
  have hlen1 : (permByInv (F k N1 G B) v).length = Rt * rowSize q m k N1 G B := by
    rw [permByInv_length]; exact hlen
  have hw1 : ∀ p ∈ permByInv (F k N1 G B) v, p.length = w :=
    permByInv_widths _ v w (fun y hy => by
      rw [hlen] at hy ⊢; exact hr1 k Rt N1 G B y hk hRt hN1 hG hB hy) hw
  have hvol : vol (permByInv (F k N1 G B) v) = vol v := by
    rw [vol_of_widths _ w hw1, vol_of_widths v w hw, hlen1, hlen]
  -- step 1
  have e1 := hP1 k Rt N1 G B w v rest r1 r2 r3 r4 (S ∘ Sum.map id Sum.inl) hk hRt hN1 hG hB hlen hw
    hrest hr1' hr2' hr3' hr4' hS0 hS1 hS2 hS3 hS4
  have run1 : Runs (callInj (Sum.map id Sum.inl) (Lens.fst R1 R2) P1) S
      (Function.update S (.inl 0) (arrSyms (permByInv (F k N1 G B) v) ++ rest)) (fun _ => True)
      (C1 * (vol v + 1)) := by
    refine runs_callInj hι1 (Lens.fst R1 R2) (Q := fun _ => True) ?_ ?_
    · have hz : Function.update S (.inl 0) (arrSyms (permByInv (F k N1 G B) v) ++ rest) ∘
          Sum.map id Sum.inl = Function.update (S ∘ Sum.map id Sum.inl) (.inl 0)
            (arrSyms (permByInv (F k N1 G B) v) ++ rest) :=
        Function.update_comp_eq_of_injective S hι1 (.inl 0) _
      rw [hz]
      exact e1
    · intro x hx
      rw [Function.update_of_ne]
      intro h
      exact hx (.inl 0) h.symm
  -- step 2
  have e2 := hP2 k Rt N1 G B w (permByInv (F k N1 G B) v) rest r1 r2 r3 r4
    (Function.update S (.inl 0) (arrSyms (permByInv (F k N1 G B) v) ++ rest) ∘ Sum.map id Sum.inr)
    hk hRt hN1 hG hB hlen1 hw1 hrest hr1' hr2' hr3' hr4'
    (Function.update_self _ _ _)
    ((Function.update_of_ne (inl_ne' (by decide)) _ _).trans hS1)
    ((Function.update_of_ne (inl_ne' (by decide)) _ _).trans hS2)
    ((Function.update_of_ne (inl_ne' (by decide)) _ _).trans hS3)
    ((Function.update_of_ne (inl_ne' (by decide)) _ _).trans hS4)
  have run2 : Runs (callInj (Sum.map id Sum.inr) (Lens.snd R1 R2) P2)
      (Function.update S (.inl 0) (arrSyms (permByInv (F k N1 G B) v) ++ rest))
      (Function.update (Function.update S (.inl 0) (arrSyms (permByInv (F k N1 G B) v) ++ rest))
        (.inl 0) (arrSyms (permByInv (F' k N1 G B) (permByInv (F k N1 G B) v)) ++ rest))
      (fun _ => True) (C2 * (vol (permByInv (F k N1 G B) v) + 1)) := by
    refine runs_callInj hι2 (Lens.snd R1 R2) (Q := fun _ => True) ?_ ?_
    · have hz : Function.update (Function.update S (.inl 0)
            (arrSyms (permByInv (F k N1 G B) v) ++ rest)) (.inl 0)
            (arrSyms (permByInv (F' k N1 G B) (permByInv (F k N1 G B) v)) ++ rest) ∘
          Sum.map id Sum.inr = Function.update (Function.update S (.inl 0)
            (arrSyms (permByInv (F k N1 G B) v) ++ rest) ∘ Sum.map id Sum.inr) (.inl 0)
            (arrSyms (permByInv (F' k N1 G B) (permByInv (F k N1 G B) v)) ++ rest) :=
        Function.update_comp_eq_of_injective _ hι2 (.inl 0) _
      rw [hz]
      exact e2
    · intro x hx
      rw [Function.update_of_ne]
      intro h
      exact hx (.inl 0) h.symm
  have hcomp : permByInv (F' k N1 G B) (permByInv (F k N1 G B) v) =
      permByInv (fun y => F k N1 G B (F' k N1 G B y)) v :=
    permByInv_comp' _ _ v (fun y hy => by
      rw [hlen] at hy ⊢; exact hr2 k Rt N1 G B y hk hRt hN1 hG hB hy)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq run1 run2) ?_)
    (fun _ h => h) (le_of_eq ?_)
  · rw [Function.update_idem, hcomp]
  · rw [hvol, Nat.add_mul]

theorem inRange_iter {q m : ℕ} {F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} (hr : InRange q m F) :
    ∀ n, InRange q m (fun k N1 G B => (F k N1 G B)^[n])
  | 0 => inRange_id q m
  | n + 1 => fun k Rt N1 G B y hk hRt hN1 hG hB hy => by
    show (F k N1 G B)^[n + 1] y < Rt * rowSize q m k N1 G B
    rw [Function.iterate_succ_apply']
    exact hr k Rt N1 G B _ hk hRt hN1 hG hB (inRange_iter hr n k Rt N1 G B y hk hRt hN1 hG hB hy)

/-- `n`-fold repetition of a step. -/
theorem stepStmt_iter {q m : ℕ} {F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} (h : StepStmt q m F)
    (hr : InRange q m F) : ∀ n, StepStmt q m (fun k N1 G B => (F k N1 G B)^[n])
  | 0 => stepStmt_id q m
  | n + 1 => by
    refine stepStmt_congr (fun k Rt N1 G B y _ _ _ _ _ _ => ?_)
      (stepStmt_comp h (stepStmt_iter h hr n) hr (inRange_iter hr n))
    exact (Function.iterate_succ_apply' _ _ _).symm

end SubNLogN.Machine.C5.StreamAux
