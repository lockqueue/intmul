/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSplitMove

/-!
# K5-SOLVE-b (`Bridge/SolveSplit.lean`): the half split and the half merge

Proofs of `SolveHalfSplitStmt` and `SolveHalfMergeStmt` (`Bridge/SolveSplitDefs.lean`;
Section 4.6 (`sec:bridge-D`), masked forward and backward column passes).

* **Split** (`splitProg`, scratch `tF, tB, cnt, ctmp`): a `mark` on `tF`, `tB`; for every row: move
  `M` records onto `tF`, then `M` onto `tB` (`moveM`, records pushed reversed); finally rewind `tF`
  onto the forward destination and `tB` onto the backward one (`rewindTo`, restoring the order).
* **Merge** (`mergeProg`, scratch `T, cnt, ctmp`): a `mark` on `T`; for every row: move `M` records
  of the forward half, then `M` of the backward half onto `T`; rewind `T` onto the destination.

Main results: `SubNLogN.Machine.solveHalfSplit_holds : SolveHalfSplitStmt` and
`SubNLogN.Machine.solveHalfMerge_holds : SolveHalfMergeStmt` (constant `C = 64`). Helpers live in
`SubNLogN.Machine.Bridge.SolveBAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveBAux

open TMFw TMFw.Contracts TMFw.Lib WP.W9comp SubNLogN.Machine.K2 SubNLogN.Machine.Calculus
  Computability SubNLogN.Machine.SolveSplit

variable {α : Type}

/-! ## Snoc forms of the row functions -/

theorem drop_two_rows (M k : ℕ) (v : List α) :
    (v.drop (2 * M)).drop (k * (2 * M)) = v.drop ((k + 1) * (2 * M)) := by
  rw [List.drop_drop]
  congr 1
  ring

theorem fwdRows_succ_snoc (M : ℕ) : ∀ (k : ℕ) (v : List α),
    fwdRows M (k + 1) v = fwdRows M k v ++ (v.drop (k * (2 * M))).take M
  | 0, v => by simp [fwdRows]
  | k + 1, v => by
    rw [fwdRows, fwdRows_succ_snoc M k (v.drop (2 * M)), fwdRows, List.append_assoc,
      drop_two_rows]

theorem bwdRows_succ_snoc (M : ℕ) : ∀ (k : ℕ) (v : List α),
    bwdRows M (k + 1) v = bwdRows M k v ++ ((v.drop (k * (2 * M))).drop M).take M
  | 0, v => by simp [bwdRows]
  | k + 1, v => by
    rw [bwdRows, bwdRows_succ_snoc M k (v.drop (2 * M)), bwdRows, List.append_assoc,
      drop_two_rows]

theorem mergeRowsH_succ_snoc (M : ℕ) : ∀ (k : ℕ) (F B : List α),
    mergeRowsH M (k + 1) F B =
      mergeRowsH M k F B ++ ((F.drop (k * M)).take M ++ (B.drop (k * M)).take M)
  | 0, F, B => by simp [mergeRowsH]
  | k + 1, F, B => by
    have hF : (F.drop M).drop (k * M) = F.drop ((k + 1) * M) := by
      rw [List.drop_drop]; congr 1; ring
    have hB : (B.drop M).drop (k * M) = B.drop ((k + 1) * M) := by
      rw [List.drop_drop]; congr 1; ring
    rw [mergeRowsH, mergeRowsH_succ_snoc M k (F.drop M) (B.drop M), mergeRowsH, hF, hB]
    simp only [List.append_assoc]

/-- Row `k` of `v` (rows of length `2M`) splits into its forward block, its backward block and the
remaining rows. -/
theorem drop_row_split (M k : ℕ) (v : List α) (hv : (k + 1) * (2 * M) ≤ v.length) :
    v.drop (k * (2 * M)) = (v.drop (k * (2 * M))).take M ++
      (((v.drop (k * (2 * M))).drop M).take M ++ v.drop ((k + 1) * (2 * M))) := by
  have h1 : ((v.drop (k * (2 * M))).drop M).drop M = v.drop ((k + 1) * (2 * M)) := by
    rw [List.drop_drop, List.drop_drop]
    congr 1
    ring
  rw [← h1, List.take_append_drop, List.take_append_drop]


theorem vol_fwdRows_add_bwdRows (M : ℕ) : ∀ (n : ℕ) (v : List (List Bool)),
    vol (fwdRows M n v) + vol (bwdRows M n v) ≤ vol v
  | 0, v => by simp [fwdRows, bwdRows, vol_nil]
  | n + 1, v => by
    have ih := vol_fwdRows_add_bwdRows M n (v.drop (2 * M))
    have hv : vol v = vol (v.take M) + (vol ((v.drop M).take M) + vol (v.drop (2 * M))) := by
      have hdd : v.drop (2 * M) = (v.drop M).drop M := by rw [List.drop_drop]; congr 1; omega
      rw [hdd, ← vol_append, List.take_append_drop, ← vol_append, List.take_append_drop]
    simp only [fwdRows, bwdRows, vol_append]
    omega

theorem vol_mergeRowsH_le (M : ℕ) : ∀ (n : ℕ) (F B : List (List Bool)),
    vol (mergeRowsH M n F B) ≤ vol F + vol B
  | 0, F, B => by simp [mergeRowsH, vol_nil]
  | n + 1, F, B => by
    have ih := vol_mergeRowsH_le M n (F.drop M) (B.drop M)
    have hF : vol F = vol (F.take M) + vol (F.drop M) := by
      rw [← vol_append, List.take_append_drop]
    have hB : vol B = vol (B.take M) + vol (B.drop M) := by
      rw [← vol_append, List.take_append_drop]
    simp only [mergeRowsH, vol_append]
    omega

/-- The head of a suffix of an array: a record iff the suffix is nonempty. -/
theorem isRecR_drop_head (ps : List (List Bool)) (rest : List Sym) (hrest : BlkTerm rest)
    (j : ℕ) : isRecR ((arrSyms (ps.drop j) ++ rest).head?) = decide (j < ps.length) := by
  by_cases hj : j < ps.length
  · rw [List.drop_eq_getElem_cons hj, isRecR_head_cons]
    exact (decide_eq_true hj).symm
  · rw [List.drop_eq_nil_of_le (by omega), arrSyms_nil, List.nil_append, isRecR_of_blkTerm hrest]
    exact (decide_eq_false hj).symm

/-! ## The split kernel -/

/-- Private scratch of the split kernel. -/
inductive SplitE
  | tF | tB | cnt | ctmp
  deriving DecidableEq

instance : Fintype SplitE where
  elems := {.tF, .tB, .cnt, .ctmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the split kernel. -/
abbrev SpLoc : Type := KLoc (Fin 4) SplitE

/-- One row: `M` records onto `tF`, `M` records onto `tB`, then peek the source. -/
def splitRow : SProg SpLoc :=
  .seq (moveM (.inl 3) (.inl 0) (.inr .tF) (.inr .cnt) (.inr .ctmp))
    (.seq (moveM (.inl 3) (.inl 0) (.inr .tB) (.inr .cnt) (.inr .ctmp)) (peekR (.inl 0)))

/-- Marks on `tF`, `tB`; peek the source. -/
def splitInit : SProg SpLoc :=
  .seq (pushC (.inr .tF) .mark) (.seq (pushC (.inr .tB) .mark) (peekR (.inl 0)))

/-- The split program. -/
def splitProg : SProg SpLoc :=
  .seq (.seq splitInit (.loop isRecR splitRow))
    (.seq (rewindTo (.inr .tF) (.inl 1) .mark) (rewindTo (.inr .tB) (.inl 2) .mark))

theorem closed_splitProg : splitProg.Closed := by
  have h1 := closed_moveM (K := SpLoc) (.inl 3) (.inl 0) (.inr .tF) (.inr .cnt) (.inr .ctmp)
  have h2 := closed_moveM (K := SpLoc) (.inl 3) (.inl 0) (.inr .tB) (.inr .cnt) (.inr .ctmp)
  have hp : (peekR (K := SpLoc) (.inl 0)).Closed := by simp [Prog.Closed, Prog.FreeBelow, peekR]
  have hm1 : (pushC (K := SpLoc) (.inr .tF) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hm2 : (pushC (K := SpLoc) (.inr .tB) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hr1 : (rewindTo (K := SpLoc) (.inr .tF) (.inl 1) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR]
  have hr2 : (rewindTo (K := SpLoc) (.inr .tB) (.inl 2) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR]
  exact ⟨⟨⟨hm1, ⟨hm2, hp⟩⟩, ⟨h1, ⟨h2, hp⟩⟩⟩, ⟨hr1, hr2⟩⟩

section Split

variable (S : SpLoc → List Sym) (M L : ℕ) (ps : List (List Bool)) (rest : List Sym)

/-- Row-loop invariant of the split with `n` rows remaining. -/
def spState (n : ℕ) : SpLoc → List Sym :=
  Function.update (Function.update (Function.update S (.inl 0)
      (arrSyms (ps.drop ((L - n) * (2 * M))) ++ rest))
    (.inr .tF) ((arrSyms (fwdRows M (L - n) ps)).reverse ++ [Sym.mark]))
    (.inr .tB) ((arrSyms (bwdRows M (L - n) ps)).reverse ++ [Sym.mark])

/-- Constant part of one row's cost. -/
def rowConst (M : ℕ) : ℕ := 2 * (M * (6 * bitLen M + 10) + 7 * bitLen M + 9) + 1

theorem split_row (hclean : KClean S) (hM : 1 ≤ M) (hv : ps.length = L * (2 * M))
    (hrest : BlkTerm rest) (rM : List Sym) (hrM : TermOK rM)
    (hctr : S (.inl 3) = natSyms M ++ rM) (n : ℕ) (hn : n < L) :
    Runs splitRow (spState S M L ps rest (n + 1)) (spState S M L ps rest n)
      (fun v => isRecR v = decide (0 < n))
      (3 * vol (ps.drop ((L - (n + 1)) * (2 * M))) - 3 * vol (ps.drop ((L - n) * (2 * M))) +
        rowConst M) := by
  obtain ⟨k, hk⟩ : ∃ k, k = L - (n + 1) := ⟨_, rfl⟩
  have hk1 : L - n = k + 1 := by omega
  rw [← hk, hk1]
  have hlen : (k + 1) * (2 * M) ≤ ps.length := by
    rw [hv]; exact Nat.mul_le_mul_right _ (by omega)
  have hsplit := drop_row_split M k ps hlen
  set A := (ps.drop (k * (2 * M))).take M with hAdef
  set B := ((ps.drop (k * (2 * M))).drop M).take M with hBdef
  set Rr := ps.drop ((k + 1) * (2 * M)) with hRr
  have e2 : (k + 1) * (2 * M) = k * (2 * M) + 2 * M := by ring
  have hA : A.length = M := by
    simp only [hAdef, List.length_take, List.length_drop]; omega
  have hB : B.length = M := by
    simp only [hBdef, List.length_take, List.length_drop]; omega
  have hst : spState S M L ps rest (n + 1) = Function.update (Function.update (Function.update S
      (.inl 0) (arrSyms (A ++ (B ++ Rr)) ++ rest))
      (.inr .tF) ((arrSyms (fwdRows M k ps)).reverse ++ [Sym.mark]))
      (.inr .tB) ((arrSyms (bwdRows M k ps)).reverse ++ [Sym.mark]) := by
    rw [spState, show L - (n + 1) = k by omega, ← hsplit]
  rw [hst]
  set S0 := Function.update (Function.update (Function.update S
      (.inl 0) (arrSyms (A ++ (B ++ Rr)) ++ rest))
      (.inr .tF) ((arrSyms (fwdRows M k ps)).reverse ++ [Sym.mark]))
      (.inr .tB) ((arrSyms (bwdRows M k ps)).reverse ++ [Sym.mark]) with hS0
  have hS0ctr : S0 (.inl 3) = natSyms M ++ rM := by
    rw [hS0, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hctr]
  have hS0cnt : S0 (.inr .cnt) = [] := by
    rw [hS0, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hclean]
  have hS0src : S0 (.inl 0) = arrSyms (A ++ (B ++ Rr)) ++ rest := by
    rw [hS0, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have h1 := moveM_runs (ctr := (.inl 3 : SpLoc)) (src := .inl 0) (dst := .inr .tF)
    (cnt := .inr .cnt) (ctmp := .inr .ctmp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S0 M rM hrM A (B ++ Rr) hA rest hS0ctr hS0cnt hS0src
  set S1 := Function.update (Function.update S0 (.inl 0) (arrSyms (B ++ Rr) ++ rest)) (.inr .tF)
    ((arrSyms A).reverse ++ S0 (.inr .tF)) with hS1
  have hS1ctr : S1 (.inl 3) = natSyms M ++ rM := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0ctr]
  have hS1cnt : S1 (.inr .cnt) = [] := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0cnt]
  have hS1src : S1 (.inl 0) = arrSyms (B ++ Rr) ++ rest := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_self]
  have h2 := moveM_runs (ctr := (.inl 3 : SpLoc)) (src := .inl 0) (dst := .inr .tB)
    (cnt := .inr .cnt) (ctmp := .inr .ctmp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S1 M rM hrM B Rr hB rest hS1ctr hS1cnt hS1src
  set S2 := Function.update (Function.update S1 (.inl 0) (arrSyms Rr ++ rest)) (.inr .tB)
    ((arrSyms B).reverse ++ S1 (.inr .tB)) with hS2
  have h3 : Runs (peekR (.inl 0)) S2 S2 (fun v => isRecR v = decide (0 < n)) 1 := by
    apply Runs.of_eval
    intro x
    refine ⟨_, 1, peekR_eval (.inl 0) x S2, ?_, le_rfl⟩
    have hsrc : S2 (.inl 0) = arrSyms (ps.drop ((k + 1) * (2 * M))) ++ rest := by
      rw [hS2, Function.update_of_ne (by decide), Function.update_self]
    rw [hsrc, isRecR_drop_head ps rest hrest]
    have hiff : (k + 1) * (2 * M) < ps.length ↔ 0 < n := by
      rw [hv]
      constructor
      · intro h
        by_contra h0
        have : n = 0 := by omega
        subst this
        have : k + 1 = L := by omega
        rw [this] at h
        exact lt_irrefl _ h
      · intro h
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    exact decide_eq_decide.2 hiff
  have h := runs_seq h1 (runs_seq h2 h3)
  have hfin : S2 = spState S M L ps rest n := by
    rw [spState, hk1, fwdRows_succ_snoc, bwdRows_succ_snoc, ← hAdef, ← hBdef, ← hRr]
    funext key
    rcases key with i | e
    · fin_cases i <;> simp [hS2, hS1, hS0, Function.update_apply]
    · cases e <;> simp [hS2, hS1, hS0, Function.update_apply, arrSyms_append,
        List.reverse_append, List.append_assoc]
  refine runs_mono (runs_congr h hfin) (fun _ hq => hq) ?_
  have hvol : vol (ps.drop (k * (2 * M))) = vol A + (vol B + vol Rr) := by
    rw [hsplit, vol_append, vol_append]
  rw [hA, hB] at *
  simp only [rowConst]
  omega

end Split


section SplitMain

variable (S : SpLoc → List Sym) (M L : ℕ) (ps : List (List Bool)) (rest : List Sym)

/-- **The split program**, bit-record form. -/
theorem split_main (hclean : KClean S) (hM : 1 ≤ M) (hv : ps.length = L * (2 * M))
    (hrest : BlkTerm rest) (rM : List Sym) (hrM : TermOK rM)
    (hsrc : S (.inl 0) = arrSyms ps ++ rest) (hctr : S (.inl 3) = natSyms M ++ rM) :
    Runs splitProg S
      (Function.update (Function.update (Function.update S (.inl 0) rest)
        (.inl 1) (arrSyms (fwdHalf M ps) ++ S (.inl 1)))
        (.inl 2) (arrSyms (bwdHalf M ps) ++ S (.inl 2)))
      (fun _ => True) (6 * vol ps + ps.length * (13 * bitLen M + 20) + 8) := by
  have hM0 : 0 < M := hM
  -- initialization
  have h0 : Runs splitInit S (spState S M L ps rest L) (fun v => isRecR v = decide (0 < L)) 3 := by
    apply Runs.of_eval
    intro x
    have e1 := pushC_eval (.inr .tF : SpLoc) .mark x S
    have e2 := pushC_eval (.inr .tB : SpLoc) .mark x
      (Function.update S (.inr .tF) (.mark :: S (.inr .tF)))
    have e3 := peekR_eval (.inl 0 : SpLoc) x (Function.update (Function.update S (.inr .tF)
      (.mark :: S (.inr .tF))) (.inr .tB) (.mark :: Function.update S (.inr .tF)
        (.mark :: S (.inr .tF)) (.inr .tB)))
    have hst : Function.update (Function.update S (.inr .tF) (.mark :: S (.inr .tF))) (.inr .tB)
        (.mark :: Function.update S (.inr .tF) (.mark :: S (.inr .tF)) (.inr .tB)) =
        spState S M L ps rest L := by
      funext key
      rcases key with i | e
      · fin_cases i <;> simp [spState, Function.update_apply, hsrc]
      · cases e <;> simp [spState, Function.update_apply, fwdRows, bwdRows, hclean .tF,
          hclean .tB, hclean .cnt, hclean .ctmp, arrSyms_nil]
    refine ⟨_, 3, (Eval.seq e1 (Eval.seq e2 e3)).of_eq (by rw [hst]) rfl, ?_, le_rfl⟩
    have hsrc' : spState S M L ps rest L (.inl 0) =
        arrSyms (ps.drop ((L - L) * (2 * M))) ++ rest := by
      rw [spState, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self]
    rw [hsrc', isRecR_drop_head ps rest hrest, hv, Nat.sub_self, Nat.zero_mul]
    refine decide_eq_decide.2 ⟨fun h => ?_, fun h => Nat.mul_pos h (by omega)⟩
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp at h
    · exact h0
  have hloop := API.seq_loop_pot (ρ := []) (p := splitRow) (c := isRecR)
    (st := spState S M L ps rest) (S := S)
    (B := fun n => 3 * vol (ps.drop ((L - (n + 1)) * (2 * M))) -
      3 * vol (ps.drop ((L - n) * (2 * M))) + rowConst M)
    (Φ := fun n => 3 * vol (ps.drop ((L - n) * (2 * M)))) (a := rowConst M) (N := L)
    ((API.runsIn_nil_iff _ _ _ _ _).2 h0)
    (fun n hn => (API.runsIn_nil_iff _ _ _ _ _).2
      (split_row S M L ps rest hclean hM hv hrest rM hrM hctr n hn))
    (fun n hn => by
      have := vol_drop_anti ps (show (L - (n + 1)) * (2 * M) ≤ (L - n) * (2 * M) from
        Nat.mul_le_mul_right _ (by omega))
      omega)
  have hl := (API.runsIn_nil_iff _ _ _ _ _).1 hloop
  -- the rewinds
  set S3 := spState S M L ps rest 0 with hS3
  have hFsrc : S3 (.inr .tF) = (arrSyms (fwdRows M L ps)).reverse ++ Sym.mark :: [] := by
    simp [hS3, spState]
  have e4 : Runs (rewindTo (.inr .tF) (.inl 1) .mark) S3
      (Function.update (Function.update S3 (.inr .tF) []) (.inl 1)
        ((arrSyms (fwdRows M L ps)).reverse.reverse ++ S3 (.inl 1))) (fun _ => True)
      (3 * (arrSyms (fwdRows M L ps)).reverse.length + 2) := by
    apply Runs.of_eval
    intro x
    exact ⟨_, _, rewindTo_eval (by simp) .mark x _ [] S3 (mark_not_mem_reverse_arrSyms _) hFsrc,
      trivial, le_rfl⟩
  set S4 := Function.update (Function.update S3 (.inr .tF) []) (.inl 1)
    ((arrSyms (fwdRows M L ps)).reverse.reverse ++ S3 (.inl 1)) with hS4
  have hBsrc : S4 (.inr .tB) = (arrSyms (bwdRows M L ps)).reverse ++ Sym.mark :: [] := by
    simp [hS4, hS3, spState]
  have e5 : Runs (rewindTo (.inr .tB) (.inl 2) .mark) S4
      (Function.update (Function.update S4 (.inr .tB) []) (.inl 2)
        ((arrSyms (bwdRows M L ps)).reverse.reverse ++ S4 (.inl 2))) (fun _ => True)
      (3 * (arrSyms (bwdRows M L ps)).reverse.length + 2) := by
    apply Runs.of_eval
    intro x
    exact ⟨_, _, rewindTo_eval (by simp) .mark x _ [] S4 (mark_not_mem_reverse_arrSyms _) hBsrc,
      trivial, le_rfl⟩
  have h := runs_seq hl (runs_seq e4 e5)
  have hfin : Function.update (Function.update S4 (.inr .tB) []) (.inl 2)
      ((arrSyms (bwdRows M L ps)).reverse.reverse ++ S4 (.inl 2)) =
      Function.update (Function.update (Function.update S (.inl 0) rest)
        (.inl 1) (arrSyms (fwdHalf M ps) ++ S (.inl 1)))
        (.inl 2) (arrSyms (bwdHalf M ps) ++ S (.inl 2)) := by
    rw [fwdHalf_eq hM0 hv, bwdHalf_eq hM0 hv]
    have hdrop : ps.drop (L * (2 * M)) = [] := List.drop_eq_nil_of_le (by omega)
    funext key
    rcases key with i | e
    · fin_cases i <;> simp [hS4, hS3, spState, Function.update_apply, hdrop, arrSyms_nil]
    · cases e <;> simp [hS4, hS3, spState, Function.update_apply, hclean .tF, hclean .tB,
        hclean .cnt, hclean .ctmp]
  refine runs_mono (runs_congr h hfin) (fun _ _ => trivial) ?_
  have hvF := vol_fwdRows_add_bwdRows M L ps
  have hlF : (arrSyms (fwdRows M L ps)).reverse.length = vol (fwdRows M L ps) := by
    simp [vol]
  have hlB : (arrSyms (bwdRows M L ps)).reverse.length = vol (bwdRows M L ps) := by
    simp [vol]
  rw [hlF, hlB, Nat.sub_self, Nat.zero_mul, List.drop_zero]
  -- the row costs
  have hb : L * (rowConst M + 1) ≤ ps.length * (13 * bitLen M + 20) := by
    rw [hv]
    simp only [rowConst]
    have h2 : L * 2 ≤ L * (2 * M) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  omega

end SplitMain

end SubNLogN.Machine.Bridge.SolveBAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.Bridge.SolveBAux

/-- **K5-SOLVE-b: the half split meets `SolveHalfSplitStmt`** (constant `64`). -/
theorem solveHalfSplit_holds : SolveHalfSplitStmt := by
  refine ⟨64, fun _ => ⟨SplitE, inferInstance, inferInstance, Option Sym, splitProg,
    inferInstance, ⟨none⟩, closed_splitProg, ?_⟩⟩
  intro wd L M v rest rM S hclean hM hv hrest hrM hsrc hctr
  have hps : (v.map (crecBits wd)).length = L * (2 * M) := by rw [List.length_map, hv]
  have h := split_main S M L (v.map (crecBits wd)) rest hclean hM hps hrest rM hrM hsrc hctr
  rw [SolveSplit.fwdHalf_map, SolveSplit.bwdHalf_map] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  have hcv : cvol wd v = vol (v.map (crecBits wd)) := rfl
  rw [hcv, List.length_map]
  nlinarith

end SubNLogN.Machine

namespace SubNLogN.Machine.Bridge.SolveBAux

open TMFw TMFw.Contracts TMFw.Lib WP.W9comp SubNLogN.Machine.K2 SubNLogN.Machine.Calculus
  Computability SubNLogN.Machine.SolveSplit

/-! ## The merge kernel -/

/-- Private scratch of the merge kernel. -/
inductive MergeE
  | T | cnt | ctmp
  deriving DecidableEq

instance : Fintype MergeE where
  elems := {.T, .cnt, .ctmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the merge kernel. -/
abbrev MgLoc : Type := KLoc (Fin 4) MergeE

/-- One row: `M` forward records, then `M` backward records onto `T`; peek the forward half. -/
def mergeRow : SProg MgLoc :=
  .seq (moveM (.inl 3) (.inl 1) (.inr .T) (.inr .cnt) (.inr .ctmp))
    (.seq (moveM (.inl 3) (.inl 2) (.inr .T) (.inr .cnt) (.inr .ctmp)) (peekR (.inl 1)))

/-- A mark on `T`; peek the forward half. -/
def mergeInit : SProg MgLoc := .seq (pushC (.inr .T) .mark) (peekR (.inl 1))

/-- The merge program. -/
def mergeProg : SProg MgLoc :=
  .seq (.seq mergeInit (.loop isRecR mergeRow)) (rewindTo (.inr .T) (.inl 0) .mark)

theorem closed_mergeProg : mergeProg.Closed := by
  have h1 := closed_moveM (K := MgLoc) (.inl 3) (.inl 1) (.inr .T) (.inr .cnt) (.inr .ctmp)
  have h2 := closed_moveM (K := MgLoc) (.inl 3) (.inl 2) (.inr .T) (.inr .cnt) (.inr .ctmp)
  have hp : (peekR (K := MgLoc) (.inl 1)).Closed := by simp [Prog.Closed, Prog.FreeBelow, peekR]
  have hm : (pushC (K := MgLoc) (.inr .T) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hr : (rewindTo (K := MgLoc) (.inr .T) (.inl 0) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR]
  exact ⟨⟨⟨hm, hp⟩, ⟨h1, ⟨h2, hp⟩⟩⟩, hr⟩

section Merge

variable (S : MgLoc → List Sym) (M L : ℕ) (F B : List (List Bool)) (rF rB : List Sym)

/-- Row-loop invariant of the merge with `n` rows remaining. -/
def mgState (n : ℕ) : MgLoc → List Sym :=
  Function.update (Function.update (Function.update S (.inl 1)
      (arrSyms (F.drop ((L - n) * M)) ++ rF))
    (.inl 2) (arrSyms (B.drop ((L - n) * M)) ++ rB))
    (.inr .T) ((arrSyms (mergeRowsH M (L - n) F B)).reverse ++ [Sym.mark])

/-- The head of `F.drop (j·M)`: a record iff rows remain. -/
theorem isRecR_rowsM_head (hrF : BlkTerm rF) (hM : 1 ≤ M) (hF : F.length = L * M) (j : ℕ)
    (hj : j ≤ L) : isRecR ((arrSyms (F.drop (j * M)) ++ rF).head?) = decide (0 < L - j) := by
  rw [isRecR_drop_head F rF hrF, hF]
  refine decide_eq_decide.2 ⟨fun h => ?_, fun h => Nat.mul_lt_mul_of_pos_right (by omega) hM⟩
  by_contra h0
  have : j = L := by omega
  subst this
  exact lt_irrefl _ h

theorem merge_row (hclean : KClean S) (hM : 1 ≤ M) (hF : F.length = L * M)
    (hB : B.length = L * M) (hrF : BlkTerm rF) (rM : List Sym) (hrM : TermOK rM)
    (hctr : S (.inl 3) = natSyms M ++ rM) (n : ℕ) (hn : n < L) :
    Runs mergeRow (mgState S M L F B rF rB (n + 1)) (mgState S M L F B rF rB n)
      (fun v => isRecR v = decide (0 < n))
      (3 * vol (F.drop ((L - (n + 1)) * M)) + 3 * vol (B.drop ((L - (n + 1)) * M)) -
        (3 * vol (F.drop ((L - n) * M)) + 3 * vol (B.drop ((L - n) * M))) + rowConst M) := by
  obtain ⟨k, hk⟩ : ∃ k, k = L - (n + 1) := ⟨_, rfl⟩
  have hk1 : L - n = k + 1 := by omega
  rw [← hk, hk1]
  have e1 : (k + 1) * M = k * M + M := by ring
  have hlenF : (k + 1) * M ≤ F.length := by rw [hF]; exact Nat.mul_le_mul_right _ (by omega)
  have hlenB : (k + 1) * M ≤ B.length := by rw [hB]; exact Nat.mul_le_mul_right _ (by omega)
  have hsF : F.drop (k * M) = (F.drop (k * M)).take M ++ F.drop ((k + 1) * M) := by
    rw [show F.drop ((k + 1) * M) = (F.drop (k * M)).drop M by
      rw [List.drop_drop, add_one_mul], List.take_append_drop]
  have hsB : B.drop (k * M) = (B.drop (k * M)).take M ++ B.drop ((k + 1) * M) := by
    rw [show B.drop ((k + 1) * M) = (B.drop (k * M)).drop M by
      rw [List.drop_drop, add_one_mul], List.take_append_drop]
  set Fk := (F.drop (k * M)).take M with hFk
  set Bk := (B.drop (k * M)).take M with hBk
  set FR := F.drop ((k + 1) * M) with hFR
  set BR := B.drop ((k + 1) * M) with hBR
  have hFkl : Fk.length = M := by simp only [hFk, List.length_take, List.length_drop]; omega
  have hBkl : Bk.length = M := by simp only [hBk, List.length_take, List.length_drop]; omega
  have hst : mgState S M L F B rF rB (n + 1) = Function.update (Function.update (Function.update S
      (.inl 1) (arrSyms (Fk ++ FR) ++ rF)) (.inl 2) (arrSyms (Bk ++ BR) ++ rB))
      (.inr .T) ((arrSyms (mergeRowsH M k F B)).reverse ++ [Sym.mark]) := by
    rw [mgState, show L - (n + 1) = k by omega, ← hsF, ← hsB]
  rw [hst]
  set S0 := Function.update (Function.update (Function.update S
      (.inl 1) (arrSyms (Fk ++ FR) ++ rF)) (.inl 2) (arrSyms (Bk ++ BR) ++ rB))
      (.inr .T) ((arrSyms (mergeRowsH M k F B)).reverse ++ [Sym.mark]) with hS0
  have hS0ctr : S0 (.inl 3) = natSyms M ++ rM := by
    rw [hS0, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hctr]
  have hS0cnt : S0 (.inr .cnt) = [] := by
    rw [hS0, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hclean]
  have hS0src : S0 (.inl 1) = arrSyms (Fk ++ FR) ++ rF := by
    rw [hS0, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have h1 := moveM_runs (ctr := (.inl 3 : MgLoc)) (src := .inl 1) (dst := .inr .T)
    (cnt := .inr .cnt) (ctmp := .inr .ctmp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S0 M rM hrM Fk FR hFkl rF hS0ctr hS0cnt hS0src
  set S1 := Function.update (Function.update S0 (.inl 1) (arrSyms FR ++ rF)) (.inr .T)
    ((arrSyms Fk).reverse ++ S0 (.inr .T)) with hS1
  have hS1ctr : S1 (.inl 3) = natSyms M ++ rM := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0ctr]
  have hS1cnt : S1 (.inr .cnt) = [] := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0cnt]
  have hS1src : S1 (.inl 2) = arrSyms (Bk ++ BR) ++ rB := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS0,
      Function.update_of_ne (by decide), Function.update_self]
  have h2 := moveM_runs (ctr := (.inl 3 : MgLoc)) (src := .inl 2) (dst := .inr .T)
    (cnt := .inr .cnt) (ctmp := .inr .ctmp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S1 M rM hrM Bk BR hBkl rB hS1ctr hS1cnt hS1src
  set S2 := Function.update (Function.update S1 (.inl 2) (arrSyms BR ++ rB)) (.inr .T)
    ((arrSyms Bk).reverse ++ S1 (.inr .T)) with hS2
  have h3 : Runs (peekR (.inl 1)) S2 S2 (fun v => isRecR v = decide (0 < n)) 1 := by
    apply Runs.of_eval
    intro x
    refine ⟨_, 1, peekR_eval (.inl 1) x S2, ?_, le_rfl⟩
    have hsrc : S2 (.inl 1) = arrSyms (F.drop ((k + 1) * M)) ++ rF := by
      rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS1,
        Function.update_of_ne (by decide), Function.update_self]
    rw [hsrc, isRecR_rowsM_head M L F rF hrF hM hF (k + 1) (by omega)]
    exact decide_eq_decide.2 ⟨fun _ => by omega, fun _ => by omega⟩
  have h := runs_seq h1 (runs_seq h2 h3)
  have hfin : S2 = mgState S M L F B rF rB n := by
    rw [mgState, hk1, mergeRowsH_succ_snoc, ← hFk, ← hBk, ← hFR, ← hBR]
    funext key
    rcases key with i | e
    · fin_cases i <;> simp [hS2, hS1, hS0, Function.update_apply]
    · cases e <;> simp [hS2, hS1, hS0, Function.update_apply, arrSyms_append,
        List.reverse_append, List.append_assoc]
  refine runs_mono (runs_congr h hfin) (fun _ hq => hq) ?_
  have hvF : vol (F.drop (k * M)) = vol Fk + vol FR := by rw [hsF, vol_append]
  have hvB : vol (B.drop (k * M)) = vol Bk + vol BR := by rw [hsB, vol_append]
  rw [hFkl, hBkl] at *
  simp only [rowConst]
  omega

/-- **The merge program**, bit-record form. -/
theorem merge_main (hclean : KClean S) (hM : 1 ≤ M) (hF : F.length = L * M)
    (hB : B.length = L * M) (hrF : BlkTerm rF) (hrB : BlkTerm rB) (rM : List Sym)
    (hrM : TermOK rM) (hsF : S (.inl 1) = arrSyms F ++ rF) (hsB : S (.inl 2) = arrSyms B ++ rB)
    (hctr : S (.inl 3) = natSyms M ++ rM) :
    Runs mergeProg S
      (Function.update (Function.update (Function.update S (.inl 1) rF) (.inl 2) rB)
        (.inl 0) (arrSyms (mergeHalves M F B) ++ S (.inl 0)))
      (fun _ => True)
      (6 * (vol F + vol B) + (F.length + B.length) * (13 * bitLen M + 20) + 6) := by
  have hM0 : 0 < M := hM
  have h0 : Runs mergeInit S (mgState S M L F B rF rB L) (fun v => isRecR v = decide (0 < L))
      2 := by
    apply Runs.of_eval
    intro x
    have e1 := pushC_eval (.inr .T : MgLoc) .mark x S
    have e2 := peekR_eval (.inl 1 : MgLoc) x (Function.update S (.inr .T) (.mark :: S (.inr .T)))
    have hst : Function.update S (.inr .T) (.mark :: S (.inr .T)) = mgState S M L F B rF rB L := by
      funext key
      rcases key with i | e
      · fin_cases i <;> simp [mgState, Function.update_apply, hsF, hsB]
      · cases e <;> simp [mgState, Function.update_apply, mergeRowsH, hclean .T, hclean .cnt,
          hclean .ctmp, arrSyms_nil]
    refine ⟨_, 2, (Eval.seq e1 e2).of_eq (by rw [hst]) rfl, ?_, le_rfl⟩
    have hsrc : mgState S M L F B rF rB L (.inl 1) = arrSyms (F.drop (0 * M)) ++ rF := by
      rw [mgState, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self, Nat.sub_self]
    rw [hsrc, isRecR_rowsM_head M L F rF hrF hM hF 0 (Nat.zero_le _), Nat.sub_zero]
  have hloop := API.seq_loop_pot (ρ := []) (p := mergeRow) (c := isRecR)
    (st := mgState S M L F B rF rB) (S := S)
    (B := fun n => 3 * vol (F.drop ((L - (n + 1)) * M)) + 3 * vol (B.drop ((L - (n + 1)) * M)) -
        (3 * vol (F.drop ((L - n) * M)) + 3 * vol (B.drop ((L - n) * M))) + rowConst M)
    (Φ := fun n => 3 * vol (F.drop ((L - n) * M)) + 3 * vol (B.drop ((L - n) * M)))
    (a := rowConst M) (N := L)
    ((API.runsIn_nil_iff _ _ _ _ _).2 h0)
    (fun n hn => (API.runsIn_nil_iff _ _ _ _ _).2
      (merge_row S M L F B rF rB hclean hM hF hB hrF rM hrM hctr n hn))
    (fun n hn => by
      have h1 := vol_drop_anti F (show (L - (n + 1)) * M ≤ (L - n) * M from
        Nat.mul_le_mul_right _ (by omega))
      have h2 := vol_drop_anti B (show (L - (n + 1)) * M ≤ (L - n) * M from
        Nat.mul_le_mul_right _ (by omega))
      omega)
  have hl := (API.runsIn_nil_iff _ _ _ _ _).1 hloop
  set S3 := mgState S M L F B rF rB 0 with hS3
  have hTsrc : S3 (.inr .T) = (arrSyms (mergeRowsH M L F B)).reverse ++ Sym.mark :: [] := by
    rw [hS3, mgState, Function.update_self, Nat.sub_zero]
  have e4 : Runs (rewindTo (.inr .T) (.inl 0) .mark) S3
      (Function.update (Function.update S3 (.inr .T) []) (.inl 0)
        ((arrSyms (mergeRowsH M L F B)).reverse.reverse ++ S3 (.inl 0))) (fun _ => True)
      (3 * (arrSyms (mergeRowsH M L F B)).reverse.length + 2) := by
    apply Runs.of_eval
    intro x
    exact ⟨_, _, rewindTo_eval (by decide) .mark x _ [] S3 (mark_not_mem_reverse_arrSyms _)
      hTsrc, trivial, le_rfl⟩
  have h := runs_seq hl e4
  have hfin : Function.update (Function.update S3 (.inr .T) []) (.inl 0)
      ((arrSyms (mergeRowsH M L F B)).reverse.reverse ++ S3 (.inl 0)) =
      Function.update (Function.update (Function.update S (.inl 1) rF) (.inl 2) rB)
        (.inl 0) (arrSyms (mergeHalves M F B) ++ S (.inl 0)) := by
    rw [mergeHalves_eq hM0 hF]
    have hdF : F.drop (L * M) = [] := List.drop_eq_nil_of_le (by omega)
    have hdB : B.drop (L * M) = [] := List.drop_eq_nil_of_le (by omega)
    funext key
    rcases key with i | e
    · fin_cases i <;> simp [hS3, mgState, Function.update_apply, hdF, hdB, arrSyms_nil]
    · cases e <;> simp [hS3, mgState, Function.update_apply, hclean .T, hclean .cnt,
        hclean .ctmp]
  refine runs_mono (runs_congr h hfin) (fun _ _ => trivial) ?_
  have hvm := vol_mergeRowsH_le M L F B
  have hlm : (arrSyms (mergeRowsH M L F B)).reverse.length = vol (mergeRowsH M L F B) := by
    simp [vol]
  rw [hlm, Nat.sub_self, Nat.zero_mul, List.drop_zero, List.drop_zero]
  have hb : L * (rowConst M + 1) ≤ (F.length + B.length) * (13 * bitLen M + 20) := by
    rw [hF, hB]
    simp only [rowConst]
    have h2 : L * 2 ≤ L * (2 * M) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  omega

end Merge

end SubNLogN.Machine.Bridge.SolveBAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.Bridge.SolveBAux

/-- **K5-SOLVE-b: the half merge meets `SolveHalfMergeStmt`** (constant `64`). -/
theorem solveHalfMerge_holds : SolveHalfMergeStmt := by
  refine ⟨64, fun _ => ⟨MergeE, inferInstance, inferInstance, Option Sym, mergeProg,
    inferInstance, ⟨none⟩, closed_mergeProg, ?_⟩⟩
  intro wd L M F B rF rB rM S hclean hM hF hB hrF hrB hrM hsF hsB hctr
  have hF' : (F.map (crecBits wd)).length = L * M := by rw [List.length_map, hF]
  have hB' : (B.map (crecBits wd)).length = L * M := by rw [List.length_map, hB]
  have h := merge_main S M L (F.map (crecBits wd)) (B.map (crecBits wd)) rF rB hclean hM hF' hB'
    hrF hrB rM hrM hsF hsB hctr
  rw [SolveSplit.mergeHalves_map] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  have hcF : cvol wd F = vol (F.map (crecBits wd)) := rfl
  have hcB : cvol wd B = vol (B.map (crecBits wd)) := rfl
  rw [hcF, hcB, List.length_map, List.length_map]
  nlinarith

end SubNLogN.Machine
