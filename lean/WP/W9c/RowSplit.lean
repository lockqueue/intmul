import WP.W9c.RowLib

/-!
# WP.W9c.RowSplit — `W9c_rowSplit`: the row block into its two coordinate lists

`splitProg` (local stacks `Loc 3 1`: named `W0 XR XI`, scratch `T`):

1. guard `mark` on `T`;
2. `whileP W0 isSgnR (moveRec W0 T)`: every entry `W0 → T`, each reversed (W4's `moveRec`);
3. `whileP T isSepR entryBack`: the entries back from `T`, last first; each reversed entry
   `sep · bits(b)ʳ · sgn b · sep2 · bits(a)ʳ · sgn a` puts `intSyms b ++ [sep]` on `XI` and
   `intSyms a ++ [sep]` on `XR` (`mvNumR` re-reverses the bits);
4. pop the guard.

Cost `≤ 10·(|blkE v| + 1)`. No hypotheses (pure data movement).
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W9c.RowLib

namespace RowSplit

/-- Local stacks: named `W0 XR XI`, one scratch `T`. -/
abbrev SL : Type := Loc 3 1

/-- the row block -/
abbrev sW : SL := .inl 0
/-- the real parts -/
abbrev sR : SL := .inl 1
/-- the imaginary parts -/
abbrev sI : SL := .inl 2
/-- the temporary -/
abbrev sT : SL := .inr 0

/-- Phase 1: every entry `W0 → T`, each reversed. -/
def phase1 : SProg SL := whileP sW isSgnR (moveRec sW sT)

/-- One reversed entry from `T`: imaginary part to `XI`, real part to `XR`. -/
def entryBack : SProg SL :=
  .seq (popR sT) (.seq (pushC sI .sep) (.seq (mvNumR sT sI)
  (.seq (popR sT) (.seq (pushC sR .sep) (mvNumR sT sR)))))

/-- Phase 2: the entries back from `T`, last first. -/
def phase2 : SProg SL := whileP sT isSepR entryBack

/-- **The split kernel.** -/
def splitProg : SProg SL := .seq (pushC sT .mark) (.seq phase1 (.seq phase2 (popR sT)))

theorem closed_splitProg : splitProg.Closed := by
  refine ⟨by simp [Prog.FreeBelow, pushC], closed_whileP _ _ ?_,
    closed_whileP _ _ ?_, by simp [Prog.FreeBelow, popR]⟩
  · simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, popR, pushR]
  · have h := closed_mvNumR (K := SL) sT sI
    have h' := closed_mvNumR (K := SL) sT sR
    exact ⟨by simp [Prog.FreeBelow, popR], by simp [Prog.FreeBelow, pushC], h,
      by simp [Prog.FreeBelow, popR], by simp [Prog.FreeBelow, pushC], h'⟩

theorem entrySyms_reverse_append (e : ℤ × ℤ) (rest : List Sym) :
    (entrySyms e).reverse ++ rest = Sym.sep :: ((encodeNat e.2.natAbs).reverse.map Sym.bit ++
      sgnSym e.2 :: Sym.sep2 :: ((encodeNat e.1.natAbs).reverse.map Sym.bit ++
        sgnSym e.1 :: rest)) := by
  simp [entrySyms, intSyms, natSyms]

/-- One reversed entry. -/
theorem rs_entryBack (X : SL → List Sym) (e : ℤ × ℤ) (rest : List Sym)
    (hT : X sT = (entrySyms e).reverse ++ rest) :
    Runs entryBack X (Function.update (Function.update (Function.update X sT rest)
      sR (intSyms e.1 ++ Sym.sep :: X sR)) sI (intSyms e.2 ++ Sym.sep :: X sI))
      (fun _ => True) (3 * (entrySyms e).length) := by
  rw [entrySyms_reverse_append] at hT
  have e1 := rs_pop sT Sym.sep _ X hT
  set X1 := Function.update X sT ((encodeNat e.2.natAbs).reverse.map Sym.bit ++
    sgnSym e.2 :: Sym.sep2 :: ((encodeNat e.1.natAbs).reverse.map Sym.bit ++
      sgnSym e.1 :: rest)) with hX1
  have e2 := rs_push sI Sym.sep X1
  set X2 := Function.update X1 sI (Sym.sep :: X1 sI) with hX2
  have e3 := rs_mvNumR (src := sT) (dst := sI) (by decide) (encodeNat e.2.natAbs).reverse
    (sgnSym e.2) (sgnSym_isBit _) (Sym.sep2 :: ((encodeNat e.1.natAbs).reverse.map Sym.bit ++
      sgnSym e.1 :: rest)) X2 (by simp [hX2, hX1])
  set X3 := Function.update (Function.update X2 sT (Sym.sep2 ::
    ((encodeNat e.1.natAbs).reverse.map Sym.bit ++ sgnSym e.1 :: rest))) sI
    (sgnSym e.2 :: ((encodeNat e.2.natAbs).reverse.reverse.map Sym.bit ++ X2 sI)) with hX3
  have e4 := rs_pop sT Sym.sep2 ((encodeNat e.1.natAbs).reverse.map Sym.bit ++
    sgnSym e.1 :: rest) X3 (by simp [hX3])
  set X4 := Function.update X3 sT ((encodeNat e.1.natAbs).reverse.map Sym.bit ++
    sgnSym e.1 :: rest) with hX4
  have e5 := rs_push sR Sym.sep X4
  set X5 := Function.update X4 sR (Sym.sep :: X4 sR) with hX5
  have e6 := rs_mvNumR (src := sT) (dst := sR) (by decide) (encodeNat e.1.natAbs).reverse
    (sgnSym e.1) (sgnSym_isBit _) rest X5 (by simp [hX5, hX4])
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5 e6))))) ?_ ?_
  · funext x
    rcases x with i | j
    · fin_cases i <;> simp [hX5, hX4, hX3, hX2, hX1, intSyms, natSyms]
    · fin_cases j
      simp [hX5, hX4, hX3, hX2, hX1]
  · rw [length_entrySyms]
    simp only [List.length_reverse, bitLen]
    omega

/-- Phase 1 states: entries `todo` on `W0`, entries `done` reversed on `T` (over its guard). -/
def F1 (S : SL → List Sym) (rw : List Sym) (done todo : List (ℤ × ℤ)) : SL → List Sym :=
  Function.update (Function.update S sW (blkE todo ++ rw)) sT
    ((blkE done).reverse ++ Sym.mark :: S sT)

/-- Phase 2 states: reversed entries `todo` on `T`, the parts of `done` (last first) on `XR`/`XI`. -/
def F2 (S : SL → List Sym) (rw : List Sym) (done todo : List (ℤ × ℤ)) : SL → List Sym :=
  Function.update (Function.update (Function.update (Function.update S sW rw) sT
    ((todo.flatMap fun e => (entrySyms e).reverse) ++ Sym.mark :: S sT))
    sR (listSyms (done.reverse.map Prod.fst) ++ S sR))
    sI (listSyms (done.reverse.map Prod.snd) ++ S sI)

theorem rs_phase1 (S : SL → List Sym) (rw : List Sym) (hrw : EndOK rw) (v : List (ℤ × ℤ)) :
    Runs phase1 (F1 S rw [] v) (F1 S rw v []) (fun _ => True)
      ((v.map fun e => 3 * (entrySyms e).length).sum + 2 * v.length + 2) := by
  refine whileP_runs sW isSgnR (moveRec sW sT) (F1 S rw) v _ ?_ ?_ ?_
  · intro done a todo _
    simp only [F1, Function.update_of_ne (show sW ≠ sT by decide), Function.update_self,
      blkE_cons, entrySyms, intSyms, List.append_assoc, List.cons_append, List.head?_cons]
    exact isSgnR_sgnSym _
  · simp only [F1, Function.update_of_ne (show sW ≠ sT by decide), Function.update_self]
    simpa [blkE, blk] using isSgnR_of_endOK hrw
  · intro done a todo _
    refine runs_post (rs_moveRec (src := sW) (dst := sT) (by decide) (entrySyms a)
      (blkE todo ++ rw) _ (entrySyms_recOK a) ?_) ?_ le_rfl
    · simp [F1, blkE_cons]
    · funext x
      rcases x with i | j
      · fin_cases i <;> simp [F1]
      · fin_cases j
        simp [F1, blkE, blk]

theorem rs_phase2 (S : SL → List Sym) (rw : List Sym) (v : List (ℤ × ℤ)) :
    Runs phase2 (F2 S rw [] v.reverse) (F2 S rw v.reverse []) (fun _ => True)
      ((v.reverse.map fun e => 3 * (entrySyms e).length).sum + 2 * v.reverse.length + 2) := by
  refine whileP_runs sT isSepR entryBack (F2 S rw) v.reverse _ ?_ ?_ ?_
  · intro done a todo _
    simp [F2, isSepR, entrySyms]
  · simp [F2, isSepR]
  · intro done a todo _
    refine runs_post (rs_entryBack _ a ((todo.flatMap fun e => (entrySyms e).reverse) ++
      Sym.mark :: S sT) (by simp [F2])) ?_ le_rfl
    funext x
    rcases x with i | j
    · fin_cases i <;> simp [F2, listSyms_cons]
    · fin_cases j
      simp [F2]

/-- **Local specification of the split kernel.** -/
theorem rs_split (v : List (ℤ × ℤ)) (rw : List Sym) (S : SL → List Sym) (hrw : EndOK rw)
    (hW : S sW = blkE v ++ rw) :
    Runs splitProg S (Function.update (Function.update (Function.update S sW rw)
      sR (listSyms (v.map Prod.fst) ++ S sR)) sI (listSyms (v.map Prod.snd) ++ S sI))
      (fun _ => True) (10 * ((blkE v).length + 1)) := by
  have e0 := rs_push sT Sym.mark S
  have e1 := rs_phase1 S rw hrw v
  have e2 := rs_phase2 S rw v
  have e3 := rs_pop sT Sym.mark (S sT) (F2 S rw v.reverse []) (by simp [F2])
  have h01 : Function.update S sT (Sym.mark :: S sT) = F1 S rw [] v := by
    funext x
    rcases x with i | j
    · fin_cases i <;> simp [F1, hW]
    · fin_cases j
      simp [F1, blkE, blk]
  have h12 : F1 S rw v [] = F2 S rw [] v.reverse := by
    funext x
    rcases x with i | j
    · fin_cases i <;> simp [F1, F2, blkE, blk, listSyms_nil]
    · fin_cases j
      simp [F1, F2, reverse_blkE]
  rw [← h01] at e1
  rw [h12] at e1
  refine runs_post (runs_seq e0 (runs_seq e1 (runs_seq e2 e3))) ?_ ?_
  · funext x
    rcases x with i | j
    · fin_cases i <;> simp [F2]
    · fin_cases j
      simp [F2]
  · have hs := sum_entry_costs v
    have hr : (v.reverse.map fun e => 3 * (entrySyms e).length).sum =
        (v.map fun e => 3 * (entrySyms e).length).sum := by
      rw [List.map_reverse, List.sum_reverse]
    have h4 := four_le_length_blkE v
    simp only [List.length_reverse]
    omega

end RowSplit

/-- **`W9c_rowSplit` holds** (no hypotheses). -/
theorem w9c_rowSplit_holds : W9c_rowSplit := by
  refine ⟨10, fun _ => ⟨1, Option Sym, fun _ => (), RowSplit.splitProg, by decide, inferInstance,
    ⟨none⟩, RowSplit.closed_splitProg, ?_⟩⟩
  intro v rw S hrw hW
  exact RowSplit.rs_split v rw S hrw hW

#assert_std_axioms RowSplit.closed_splitProg RowSplit.entrySyms_reverse_append
  RowSplit.rs_entryBack RowSplit.rs_phase1 RowSplit.rs_phase2 RowSplit.rs_split w9c_rowSplit_holds

end WP.W9c
