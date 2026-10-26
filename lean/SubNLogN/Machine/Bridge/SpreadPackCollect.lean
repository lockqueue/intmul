/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadPackData

/-!
# K5 spreading, data packing: the collection phase (`Bridge/SpreadPackCollect.lean`)

**Scope (honest summary).** Proved exact evaluation of the collection phase of the data packer
(`collect_eval`): walking the ruler `RW` (`W` marks, restored), while the source shows a bit, one
one-coefficient record (bits, then `sep`) moves onto the buffer `A` and a mark goes onto `M`; at a
non-bit (or after `W` records) the remaining steps do nothing.
-/

namespace SubNLogN.Machine.Bridge.SpreadPackAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SpreadAux Computability

variable {K : Type} [DecidableEq K]

theorem collect_eval (ι : PackRole → K) (hι : Function.Injective ι) {w : ℕ} (hw : 1 ≤ w)
    (W : ℕ) (B : List CInt) (hBW : B.length ≤ W) (rest DW : List Sym)
    (hrest : B.length < W → TermOK rest) (hDW : DW.head? ≠ some .mark) (S : K → List Sym)
    (hsrc : S (ι .src) = dRecs w B ++ rest) (hRW : S (ι .RW) = List.replicate W .mark ++ DW)
    (hX1 : (S (ι (.tmp 3))).head? ≠ some .mark) (v : AReg) :
    ∃ v', Eval [] (.seq (walk (ι .RW) (ι (.tmp 3)) (collectBody (ι .src) (ι (.tmp 0)) (ι .M)))
        (moveMarks (ι (.tmp 3)) (ι .RW))) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (ι .src) rest) (ι (.tmp 0))
        (B.reverse.flatMap (revRec w) ++ S (ι (.tmp 0)))) (ι .M)
        (List.replicate B.length .mark ++ S (ι .M))⟩
      ((Finset.range W).sum (fun j => (if j < B.length then 8 * w + 7 else 4) + 4) + 2 +
        (4 * W + 2)) := by
  let Sc : ℕ → K → List Sym := fun j => Function.update (Function.update (Function.update
    (Function.update (Function.update S (ι .src) (dRecs w (B.drop j) ++ rest)) (ι (.tmp 0))
      ((B.take j).reverse.flatMap (revRec w) ++ S (ι (.tmp 0)))) (ι .M)
      (List.replicate (min j B.length) .mark ++ S (ι .M))) (ι .RW)
      (List.replicate (W - j) .mark ++ DW)) (ι (.tmp 3)) (List.replicate j .mark ++ S (ι (.tmp 3)))
  have hRX : ι .RW ≠ ι (.tmp 3) := hι.ne (by decide)
  have hSR : ∀ j ≤ W, Sc j (ι .RW) = List.replicate (W - j) .mark ++ DW := by
    intro j _
    simp only [Sc, Function.update_of_ne hRX, Function.update_self]
  have hSX : ∀ j ≤ W, Sc j (ι (.tmp 3)) = List.replicate j .mark ++ S (ι (.tmp 3)) := by
    intro j _
    simp only [Sc, Function.update_self]
  have h0 : Sc 0 = S := by
    refine ext_P (ι := ι) (fun k hk => ?_) (fun r => ?_)
    · simp [Sc, Function.update_apply, hk]
    · rcases r with _ | k | _ | _ | _ | _ | j
      · simp [Sc, Function.update_apply, hι.eq_iff, hsrc]
      · simp [Sc, Function.update_apply, hι.eq_iff]
      · simp [Sc, Function.update_apply, hι.eq_iff]
      · simp [Sc, Function.update_apply, hι.eq_iff, hRW]
      · simp [Sc, Function.update_apply, hι.eq_iff]
      · simp [Sc, Function.update_apply, hι.eq_iff]
      · fin_cases j <;> simp [Sc, Function.update_apply, hι.eq_iff]
  have hstep : ∀ j < W, ∀ u, ∃ w', Eval [] (collectBody (ι .src) (ι (.tmp 0)) (ι .M))
      ⟨u, Function.update (Function.update (Sc j) (ι .RW)
        (List.replicate (W - j - 1) .mark ++ DW)) (ι (.tmp 3)) (.mark :: Sc j (ι (.tmp 3)))⟩
      ⟨w', Sc (j + 1)⟩ ((fun j => if j < B.length then 8 * w + 7 else 4) j) := by
    intro j hj u
    set T := Function.update (Function.update (Sc j) (ι .RW)
      (List.replicate (W - j - 1) .mark ++ DW)) (ι (.tmp 3)) (.mark :: Sc j (ι (.tmp 3))) with hT
    have e1 := eval_peekO (ι .src) u T
    have hrw : W - j - 1 = W - (j + 1) := by omega
    by_cases hjm : j < B.length
    · have hdrop : B.drop j = B[j] :: B.drop (j + 1) := List.drop_eq_getElem_cons hjm
      have hTs0 : T (ι .src) = dRecs w (B.drop j) ++ rest := by
        simp [hT, Sc, Function.update_apply, hι.eq_iff]
      have hTs : T (ι .src) = (coefBits w B[j]).map Sym.bit ++
          Sym.sep :: (dRecs w (B.drop (j + 1)) ++ rest) := by
        rw [hTs0, hdrop, dRecs_cons, List.append_assoc, List.cons_append]
      obtain ⟨b, bs, hbs⟩ : ∃ b bs, coefBits w B[j] = b :: bs := by
        cases h : coefBits w B[j] with
        | nil =>
          have := length_coefBits w B[j]
          rw [h] at this
          simp at this
          omega
        | cons b bs => exact ⟨b, bs, rfl⟩
      have hc : isBitO ({ u with o := (T (ι .src)).head? } : AReg).o = true := by
        show isBitO (T (ι .src)).head? = true
        rw [hTs, hbs]
        rfl
      have e2 := mvBits_eval (hι.ne (by decide) : ι .src ≠ ι (.tmp 0)) (coefBits w B[j])
        (Sym.sep :: (dRecs w (B.drop (j + 1)) ++ rest)) { u with o := (T (ι .src)).head? } T
        (TermOK.cons rfl _) hTs
      set S2 := Function.update (Function.update T (ι .src)
        (Sym.sep :: (dRecs w (B.drop (j + 1)) ++ rest))) (ι (.tmp 0))
        ((coefBits w B[j]).reverse.map Sym.bit ++ T (ι (.tmp 0))) with hS2
      have hS2s : S2 (ι .src) = Sym.sep :: (dRecs w (B.drop (j + 1)) ++ rest) := by
        rw [hS2, Function.update_of_ne (hι.ne (by decide)), Function.update_self]
      have e3 := eval_move1 (hι.ne (by decide) : ι .src ≠ ι (.tmp 0))
        { ({ u with o := (T (ι .src)).head? } : AReg) with
          q := (Sym.sep :: (dRecs w (B.drop (j + 1)) ++ rest)).head? } S2 Sym.sep
        (dRecs w (B.drop (j + 1)) ++ rest) hS2s
      refine ⟨_, eval_of_stk (Eval.seq e1 (Eval.ite_true hc (Eval.seq e2 (Eval.seq e3
        (eval_pushS (ι .M) Sym.mark _ _))))) ?_ ?_⟩
      · have hmin : min (j + 1) B.length = min j B.length + 1 := by omega
        have htake : (B.take (j + 1)).reverse.flatMap (revRec w) =
            revRec w B[j] ++ (B.take j).reverse.flatMap (revRec w) := by
          rw [List.take_add_one, List.getElem?_eq_getElem hjm, Option.toList_some,
            List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatMap_cons]
        have hrev : revRec w B[j] = Sym.sep :: (coefBits w B[j]).reverse.map Sym.bit := by
          simp [revRec, recSyms, List.map_reverse]
        refine ext_P (ι := ι) (fun k hk => ?_) (fun r => ?_)
        · simp [hS2, hT, Sc, Function.update_apply, hk]
        · rcases r with _ | k | _ | _ | _ | _ | j'
          · simp [hS2, hT, Sc, Function.update_apply, hι.eq_iff]
          · simp [hS2, hT, Sc, Function.update_apply, hι.eq_iff]
          · simp [hS2, hT, Sc, Function.update_apply, hι.eq_iff, hmin, List.replicate_succ]
          · simp [hS2, hT, Sc, Function.update_apply, hι.eq_iff, hrw]
          · simp [hS2, hT, Sc, Function.update_apply, hι.eq_iff]
          · simp [hS2, hT, Sc, Function.update_apply, hι.eq_iff]
          · fin_cases j' <;> simp [hS2, hT, Sc, Function.update_apply, hι.eq_iff, htake, hrev,
              List.replicate_succ]
      · simp only [hjm, if_true, length_coefBits]
        ring
    · have hjm' : B.length ≤ j := by omega
      have hdrop : B.drop j = [] := List.drop_of_length_le hjm'
      have hdrop' : B.drop (j + 1) = [] := List.drop_of_length_le (by omega)
      have htake : B.take j = B := List.take_of_length_le hjm'
      have htake' : B.take (j + 1) = B := List.take_of_length_le (by omega)
      have hmin : min j B.length = B.length := by omega
      have hmin' : min (j + 1) B.length = B.length := by omega
      have hTs : T (ι .src) = rest := by
        simp [hT, Sc, Function.update_apply, hι.eq_iff, hdrop, dRecs]
      have hc : isBitO ({ u with o := (T (ι .src)).head? } : AReg).o = false := by
        show isBitO (T (ι .src)).head? = false
        rw [hTs]
        exact isBitO_false_of_termOK (hrest (by omega))
      refine ⟨_, eval_of_stk (Eval.seq e1 (Eval.ite_false hc (Eval.seq (eval_skipA _ _)
        (eval_skipA _ _)))) ?_ ?_⟩
      · refine ext_P (ι := ι) (fun k hk => ?_) (fun r => ?_)
        · simp [hT, Sc, Function.update_apply, hk]
        · rcases r with _ | k | _ | _ | _ | _ | j'
          · simp [hT, Sc, Function.update_apply, hι.eq_iff, hdrop, hdrop']
          · simp [hT, Sc, Function.update_apply, hι.eq_iff]
          · simp [hT, Sc, Function.update_apply, hι.eq_iff, hmin, hmin']
          · simp [hT, Sc, Function.update_apply, hι.eq_iff, hrw]
          · simp [hT, Sc, Function.update_apply, hι.eq_iff]
          · simp [hT, Sc, Function.update_apply, hι.eq_iff]
          · fin_cases j' <;> simp [hT, Sc, Function.update_apply, hι.eq_iff, htake, htake',
              List.replicate_succ]
      · simp [hjm]
  obtain ⟨v1, e1⟩ := walk_eval_family' hRX (collectBody (ι .src) (ι (.tmp 0)) (ι .M)) W DW
    (S (ι (.tmp 3))) hDW Sc hSR hSX _ hstep v
  rw [h0] at e1
  have e2 := moveMarks_eval (hι.ne (by decide) : ι (.tmp 3) ≠ ι .RW) W (S (ι (.tmp 3))) v1 (Sc W)
    hX1 (hSX W le_rfl)
  have hdW : B.drop W = [] := List.drop_of_length_le hBW
  have htW : B.take W = B := List.take_of_length_le hBW
  have hmW : min W B.length = B.length := by omega
  refine ⟨_, eval_of_stk (Eval.seq e1 e2) ?_ rfl⟩
  refine ext_P (ι := ι) (fun k hk => ?_) (fun r => ?_)
  · simp [Sc, Function.update_apply, hk]
  · rcases r with _ | k | _ | _ | _ | _ | j'
    · simp [Sc, Function.update_apply, hι.eq_iff, hdW, dRecs]
    · simp [Sc, Function.update_apply, hι.eq_iff]
    · simp [Sc, Function.update_apply, hι.eq_iff, hmW]
    · simp [Sc, Function.update_apply, hι.eq_iff, hRW]
    · simp [Sc, Function.update_apply, hι.eq_iff]
    · simp [Sc, Function.update_apply, hι.eq_iff]
    · fin_cases j' <;> simp [Sc, Function.update_apply, hι.eq_iff, htW]

end SubNLogN.Machine.Bridge.SpreadPackAux
