/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseCore
import SubNLogN.Machine.CCore.LeafPhaseMaskDefs

/-!
# C-core phase leaf: floors and the `RotIPowStmt` call on the work layout (`CCore/LeafPhaseCall.lean`)

**Scope (honest summary).** Exact `Runs` facts on the work layout `Lw` (`LeafPhaseBase.lean`),
everything proved:
* `pushMarks ps`, `popMarks ps`: push/pop floor marks on a list of scratch stacks;
* `ι3 a b c j`: the `Fin 3` sub-kernel layout of `RotIPowStmt` (`Layer/DrvPreKDefs.lean:42`) at the
  scratch stacks `a, b, c`, its private scratch through `j`; `runs_rotCall`.
(The `MaskSelStmt` call `ι9`/`runs_maskCall` is in `LeafPhaseMask.lean`.)
-/
namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Machine.Layer.DrvPreK

variable {Er : Type}

/-! ## Floors -/

/-- Push a floor `mark` on each listed scratch stack. -/
def pushMarks : List PS → SProg (Lw Er)
  | [] => skip
  | p :: ps => .seq (pushC (wS p) .mark) (pushMarks ps)

/-- Pop the top symbol of each listed scratch stack. -/
def popMarks : List PS → SProg (Lw Er)
  | [] => skip
  | p :: ps => .seq (unprotect (wS p)) (popMarks ps)

theorem closed_pushMarks : ∀ ps : List PS, (pushMarks (Er := Er) ps).Closed
  | [] => by simp [pushMarks, skip, Prog.Closed, Prog.FreeBelow]
  | p :: ps => ⟨by simp [pushC, Prog.Closed, Prog.FreeBelow], closed_pushMarks ps⟩

theorem closed_popMarks : ∀ ps : List PS, (popMarks (Er := Er) ps).Closed
  | [] => by simp [popMarks, skip, Prog.Closed, Prog.FreeBelow]
  | p :: ps => ⟨by simp [unprotect, popR, Prog.Closed, Prog.FreeBelow], closed_popMarks ps⟩

variable [DecidableEq Er]

theorem runs_pushMarks (d : List Sym) (er : Er → List Sym) :
    ∀ (ps : List PS) (sc : PS → List Sym), ps.Nodup →
      Runs (pushMarks ps) (wst d sc er)
        (wst d (fun q => if q ∈ ps then Sym.mark :: sc q else sc q) er) (fun _ => True)
        (ps.length + 1)
  | [], sc, _ => by
    simp only [List.not_mem_nil, if_false]
    exact Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v _, trivial, le_rfl⟩
  | p :: ps, sc, hnd => by
    have hp : p ∉ ps := (List.nodup_cons.mp hnd).1
    have h1 := Calculus.runs_pushC (wS (Er := Er) p) Sym.mark (wst d sc er)
    rw [update_wst_S] at h1
    have h2 := runs_pushMarks d er ps (Function.update sc p (Sym.mark :: sc p))
      (List.nodup_cons.mp hnd).2
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
      (fun _ h => h) (by simp only [List.length_cons]; omega)
    congr 1
    funext q
    by_cases hq : q = p
    · subst hq; simp [hp]
    · by_cases hq' : q ∈ ps <;> simp [hq, hq', Function.update_apply]

theorem runs_popMarks (d : List Sym) (er : Er → List Sym) :
    ∀ (ps : List PS) (sc : PS → List Sym), ps.Nodup → (∀ q ∈ ps, sc q = [Sym.mark]) →
      Runs (popMarks ps) (wst d sc er) (wst d (fun q => if q ∈ ps then [] else sc q) er)
        (fun _ => True) (ps.length + 1)
  | [], sc, _, _ => by
    simp only [List.not_mem_nil, if_false]
    exact Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v _, trivial, le_rfl⟩
  | p :: ps, sc, hnd, hm => by
    have hp : p ∉ ps := (List.nodup_cons.mp hnd).1
    have h1 := Calculus.runs_popR (wS (Er := Er) p) (wst d sc er) Sym.mark []
      (by simpa using hm p List.mem_cons_self)
    rw [update_wst_S] at h1
    have h2 := runs_popMarks d er ps (Function.update sc p []) (List.nodup_cons.mp hnd).2
      (fun q hq => by
        rw [Function.update_of_ne (by rintro rfl; exact hp hq)]
        exact hm q (List.mem_cons_of_mem _ hq))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
      (fun _ h => h) (by simp only [List.length_cons]; omega)
    congr 1
    funext q
    by_cases hq : q = p
    · subst hq; simp [hp]
    · by_cases hq' : q ∈ ps <;> simp [hq, hq', Function.update_apply]

/-! ## The `RotIPowStmt` call -/

theorem blkTerm_mark : BlkTerm [Sym.mark] := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact ⟨rfl, by decide⟩

/-- The `Fin 3` sub-kernel layout at the scratch stacks `a, b, c`, private scratch through `j`. -/
def ι3 {Er' : Type} (a b c : PS) (j : Er' → Er) : KLoc (Fin 3) Er' → Lw Er
  | .inl i => if i.val = 0 then wS a else if i.val = 1 then wS b else wS c
  | .inr e => .inr (j e)

theorem ι3_injective {Er' : Type} {a b c : PS} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {j : Er' → Er} (hj : Function.Injective j) : Function.Injective (ι3 (Er := Er) a b c j) := by
  rintro (i | e) (i' | e') h
  · have hi := i.isLt; have hi' := i'.isLt
    simp only [ι3] at h
    apply congrArg Sum.inl
    apply Fin.ext
    split_ifs at h <;> simp_all [wS] <;> omega
  · simp only [ι3] at h; split_ifs at h <;> simp at h
  · simp only [ι3] at h; split_ifs at h <;> simp at h
  · simp only [ι3, Sum.inr.injEq] at h; rw [hj h]

/-- **A `RotIPowStmt` call** on the work layout: the array on `a` (above a floor `mark`) becomes
`mapC (rotIPowC e)` of it on `b` (above its floor `mark`); `a` keeps its floor; the counter
`natSyms w` on `c` is restored. -/
theorem runs_rotCall {Er' Rr Rr' : Type} [DecidableEq Er'] (lr : Lens (σ Rr) Rr') {e C : ℕ}
    {P : Prog (KLoc (Fin 3) Er') (fun _ => Sym) Rr'}
    (hspec : ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym)
      (S : KLoc (Fin 3) Er' → List Sym),
      1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC e) v) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w (mapC (rotIPowC e) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w v + w + 1)))
    {a b c : PS} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {j : Er' → Er}
    (hj : Function.Injective j) (d : List Sym) (sc : PS → List Sym) (er : Er → List Sym)
    (w : ℕ) (v : List (List CInt)) (hw : 1 ≤ w) (hf1 : CArrFits w v)
    (hf2 : CArrFits w (mapC (rotIPowC e) v))
    (ha : sc a = carrSyms w v ++ [Sym.mark]) (hb : sc b = [Sym.mark]) (hc : sc c = natSyms w) :
    Runs (callInj (ι3 a b c j) lr P) (wst d sc er)
      (wst d (Function.update (Function.update sc a [Sym.mark]) b
        (carrSyms w (mapC (rotIPowC e) v) ++ [Sym.mark])) er) (fun _ => True)
      (C * (cvol w v + w + 1)) := by
  refine runs_callInj (Q := fun _ => True) (ι3_injective hab hac hbc hj) lr ?_ ?_
  · have h := hspec w v [Sym.mark] [] (wst d sc er ∘ ι3 a b c j) hw hf1 hf2 blkTerm_mark
      TermOK.nil (by simp [ι3, ha]) (by simp [ι3, hc])
    refine WP.W9comp.runs_congr h ?_
    funext x
    rcases x with i | x
    · have hi := i.isLt
      by_cases h0 : i.val = 0
      · have : i = 0 := Fin.ext h0
        subst this; simp [ι3, Function.update_apply, hab]
      · by_cases h1 : i.val = 1
        · have : i = 1 := Fin.ext h1
          subst this; simp [ι3, Function.update_apply, hab, hb, Ne.symm hab]
        · have : i = 2 := Fin.ext (by omega)
          subst this; simp [ι3, Function.update_apply, Ne.symm hac, Ne.symm hbc]
    · simp [ι3, Function.update_apply]
  · intro k hk
    rcases k with (_ | q) | x
    · rfl
    · simp only [wst, Function.update_apply]
      have hqa : q ≠ a := fun h => hk (.inl 0) (by simp [ι3, h])
      have hqb : q ≠ b := fun h => hk (.inl 1) (by simp [ι3, h])
      simp [hqa, hqb]
    · rfl

end SubNLogN.Machine.CCore.LeafScalarAux
