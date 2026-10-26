/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSplit

/-!
# K5-SOLVE-b (`Bridge/SolveReindex.lean`): the backward row reindex maps `I` and `J`

Proofs of `SolveReindexIStmt` (`I = reverseRows ∘ rotateLeft 2`) and `SolveReindexJStmt`
(`J = reverseRows ∘ rotateLeft 1`) (`Bridge/SolveSplitDefs.lean`;
Lemma 4.6 (`lem:bridge-C`)(iv) and Section 4.6 (`sec:bridge-D`), backward row-block reversals).

**Program** `reindexProg a` (scratch `Pre, Suf, D1, Tmp, cnt, ctmp`; `a ∈ {1, 2}`):
1. marks on `Pre`, `Suf`, `D1`;
2. *rotate*: move the first `a` rows (`a` counted moves of `M` records) onto `Pre`, all remaining
   records onto `Suf` (records pushed reversed); rewind `Pre`, then `Suf`, onto `D1`. Now `D1`
   holds the rows rotated left by `a`, first row on top;
3. *reverse rows*: while `D1` has a record: a mark on `Tmp`, move `M` records `D1 → Tmp`, rewind
   `Tmp` onto the array. Each row keeps its internal order, the row order is reversed;
4. drop the mark of `D1`.

Main results: `SubNLogN.Machine.solveReindexI_holds`, `SubNLogN.Machine.solveReindexJ_holds`
(constant `C = 64`). Helpers live in `SubNLogN.Machine.Bridge.SolveBAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveBAux

open TMFw TMFw.Contracts TMFw.Lib WP.W9comp SubNLogN.Machine.K2 SubNLogN.Machine.Calculus
  Computability SubNLogN.Machine.SolveSplit

variable {α : Type}

/-! ## Rows -/

theorem flatten_rowsOf (M : ℕ) : ∀ (n : ℕ) (u : List α), (rowsOf M n u).flatten = u.take (n * M)
  | 0, u => by simp [rowsOf]
  | n + 1, u => by
    rw [rowsOf, List.flatten_cons, flatten_rowsOf M n, show (n + 1) * M = M + n * M by ring,
      List.take_add]

theorem take_rowsOf (M : ℕ) : ∀ (a n : ℕ) (u : List α), a ≤ n →
    (rowsOf M n u).take a = rowsOf M a u
  | 0, n, u, _ => by simp [rowsOf]
  | a + 1, n + 1, u, h => by
    rw [rowsOf, rowsOf, List.take_succ_cons, take_rowsOf M a n _ (by omega)]
  | a + 1, 0, u, h => by omega

theorem drop_rowsOf (M : ℕ) : ∀ (a n : ℕ) (u : List α), a ≤ n →
    (rowsOf M n u).drop a = rowsOf M (n - a) (u.drop (a * M))
  | 0, n, u, _ => by simp
  | a + 1, n + 1, u, h => by
    rw [rowsOf, List.drop_succ_cons, drop_rowsOf M a n _ (by omega), List.drop_drop,
      show n + 1 - (a + 1) = n - a by omega, show M + a * M = (a + 1) * M by ring]
  | a + 1, 0, u, h => by omega

/-- The rotated row list flattens to the rotated array. -/
theorem flatten_rotate_rowsOf (M L a : ℕ) (u : List α) (hu : u.length = L * M) (ha : a ≤ L) :
    ((rowsOf M L u).rotate a).flatten = u.drop (a * M) ++ u.take (a * M) := by
  rw [List.rotate_eq_drop_append_take (by rw [length_rowsOf]; exact ha), List.flatten_append,
    drop_rowsOf M a L u ha, take_rowsOf M a L u ha, flatten_rowsOf, flatten_rowsOf]
  congr 1
  rw [List.take_of_length_le]
  rw [List.length_drop, hu, ← Nat.sub_mul]

/-! ## The reindex kernel -/

/-- Private scratch of the reindex kernel. -/
inductive ReE
  | Pre | Suf | D1 | Tmp | cnt | ctmp
  deriving DecidableEq

instance : Fintype ReE where
  elems := {.Pre, .Suf, .D1, .Tmp, .cnt, .ctmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the reindex kernel. -/
abbrev RLoc : Type := KLoc (Fin 2) ReE

/-- `a` counted moves of `M` records from the array onto `Pre`. -/
def prefixMoves : ℕ → SProg RLoc
  | 0 => skip
  | a + 1 => .seq (moveM (.inl 1) (.inl 0) (.inr .Pre) (.inr .cnt) (.inr .ctmp)) (prefixMoves a)

/-- One row of the row reversal: `D1 → Tmp → array`. -/
def revRow : SProg RLoc :=
  .seq (pushC (.inr .Tmp) .mark)
    (.seq (moveM (.inl 1) (.inr .D1) (.inr .Tmp) (.inr .cnt) (.inr .ctmp))
      (.seq (rewindTo (.inr .Tmp) (.inl 0) .mark) (peekR (.inr .D1))))

/-- Marks on `Pre`, `Suf`, `D1`. -/
def reMarks : SProg RLoc :=
  .seq (pushC (.inr .Pre) .mark) (.seq (pushC (.inr .Suf) .mark) (pushC (.inr .D1) .mark))

/-- Rotation left by `a` rows onto `D1`. -/
def reRotate (a : ℕ) : SProg RLoc :=
  .seq (prefixMoves a) (.seq (moveAll (.inl 0) (.inr .Suf))
    (.seq (rewindTo (.inr .Pre) (.inr .D1) .mark) (rewindTo (.inr .Suf) (.inr .D1) .mark)))

/-- Row reversal from `D1` onto the array; drop the mark of `D1`. -/
def reReverse : SProg RLoc :=
  .seq (.seq (peekR (.inr .D1)) (.loop isRecR revRow)) (popR (.inr .D1))

/-- The reindex program `reverseRows ∘ rotateLeft a`. -/
def reindexProg (a : ℕ) : SProg RLoc := .seq reMarks (.seq (reRotate a) reReverse)

theorem closed_prefixMoves : ∀ a : ℕ, (prefixMoves a).Closed
  | 0 => by simp [prefixMoves, skip, Prog.Closed, Prog.FreeBelow]
  | a + 1 => ⟨closed_moveM _ _ _ _ _, closed_prefixMoves a⟩

theorem closed_reindexProg (a : ℕ) : (reindexProg a).Closed := by
  have hm : ∀ k : ReE, (pushC (K := RLoc) (.inr k) .mark).Closed := fun _ => by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hr : ∀ (s d : RLoc), (rewindTo s d .mark).Closed := fun _ _ => by
    simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR]
  have hp : (peekR (K := RLoc) (.inr .D1)).Closed := by simp [Prog.Closed, Prog.FreeBelow, peekR]
  have hpop : (popR (K := RLoc) (.inr .D1)).Closed := by simp [Prog.Closed, Prog.FreeBelow, popR]
  exact ⟨⟨hm _, ⟨hm _, hm _⟩⟩, ⟨⟨closed_prefixMoves a, ⟨closed_moveAll _ _, ⟨hr _ _, hr _ _⟩⟩⟩,
    ⟨⟨hp, ⟨hm _, ⟨closed_moveM _ _ _ _ _, ⟨hr _ _, hp⟩⟩⟩⟩, hpop⟩⟩⟩

section Reindex

variable (S : RLoc → List Sym) (M L a : ℕ) (ps : List (List Bool)) (rest : List Sym)

/-- State during the prefix moves (`j` rows moved onto `Pre`). -/
def preState (j : ℕ) : RLoc → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (.inl 0)
    (arrSyms (ps.drop (j * M)) ++ rest))
    (.inr .Pre) ((arrSyms (ps.take (j * M))).reverse ++ [Sym.mark]))
    (.inr .Suf) [Sym.mark]) (.inr .D1) [Sym.mark]

/-- Per-move constant of `moveM`. -/
def mvConst (M : ℕ) : ℕ := M * (6 * bitLen M + 10) + 7 * bitLen M + 9

theorem prefix_runs (hclean : KClean S) (rM : List Sym) (hrM : TermOK rM)
    (hctr : S (.inl 1) = natSyms M ++ rM) :
    ∀ (b j : ℕ), (j + b) * M ≤ ps.length →
      Runs (prefixMoves b) (preState S M ps rest j) (preState S M ps rest (j + b))
        (fun _ => True) (3 * vol (ps.drop (j * M)) - 3 * vol (ps.drop ((j + b) * M)) +
          b * mvConst M + 1)
  | 0, j, _ => by
    apply Runs.of_eval
    intro x
    exact ⟨x, 1, skip_eval [] _, trivial, by simp⟩
  | b + 1, j, hb => by
    have e1 : (j + 1) * M = j * M + M := by ring
    have hle : (j + 1) * M ≤ ps.length := le_trans (Nat.mul_le_mul_right _ (by omega)) hb
    have hsp : ps.drop (j * M) = (ps.drop (j * M)).take M ++ ps.drop ((j + 1) * M) := by
      rw [show ps.drop ((j + 1) * M) = (ps.drop (j * M)).drop M by
        rw [List.drop_drop, add_one_mul], List.take_append_drop]
    set blk := (ps.drop (j * M)).take M with hblk
    have hbl : blk.length = M := by
      simp only [hblk, List.length_take, List.length_drop]; omega
    have hsrc : preState S M ps rest j (.inl 0) = arrSyms (blk ++ ps.drop ((j + 1) * M)) ++ rest := by
      rw [preState, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self, ← hsp]
    have hctr' : preState S M ps rest j (.inl 1) = natSyms M ++ rM := by
      rw [preState, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hctr]
    have hcnt : preState S M ps rest j (.inr .cnt) = [] := by
      rw [preState, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hclean]
    have h1 := moveM_runs (ctr := (.inl 1 : RLoc)) (src := .inl 0) (dst := .inr .Pre)
      (cnt := .inr .cnt) (ctmp := .inr .ctmp) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (preState S M ps rest j) M rM hrM blk (ps.drop ((j + 1) * M)) hbl
      rest hctr' hcnt hsrc
    have hmid : Function.update (Function.update (preState S M ps rest j) (.inl 0)
        (arrSyms (ps.drop ((j + 1) * M)) ++ rest)) (.inr .Pre)
        ((arrSyms blk).reverse ++ preState S M ps rest j (.inr .Pre)) =
        preState S M ps rest (j + 1) := by
      have ht : ps.take ((j + 1) * M) = ps.take (j * M) ++ blk := by
        rw [e1, List.take_add]
      funext key
      rcases key with i | e
      · fin_cases i <;> simp [preState, Function.update_apply]
      · cases e <;> simp [preState, Function.update_apply, ht, arrSyms_append,
          List.reverse_append, List.append_assoc]
    have h2 := prefix_runs hclean rM hrM hctr b (j + 1) (by
      rw [show j + 1 + b = j + (b + 1) by omega]; exact hb)
    have h := runs_seq (runs_congr h1 hmid) h2
    rw [show j + 1 + b = j + (b + 1) by omega] at h
    refine runs_mono h (fun _ _ => trivial) ?_
    have hv1 : vol (ps.drop (j * M)) = vol blk + vol (ps.drop ((j + 1) * M)) := by
      rw [hsp, vol_append]
    have hv2 := vol_drop_anti ps (show (j + 1) * M ≤ (j + (b + 1)) * M from
      Nat.mul_le_mul_right _ (by omega))
    have hmv : M * (6 * bitLen M + 10) + 7 * bitLen M + 9 = mvConst M := rfl
    have hb1 : (b + 1) * mvConst M = b * mvConst M + mvConst M := by ring
    omega

end Reindex

section ReindexMain

variable (S : RLoc → List Sym) (M L a : ℕ) (ps : List (List Bool)) (rest : List Sym)

/-- The rows rotated left by `a`. -/
def rotRows : List (List (List Bool)) := (rowsOf M L ps).rotate a

theorem length_rotRows : (rotRows M L a ps).length = L := by
  simp [rotRows, length_rowsOf]

theorem length_mem_rotRows (hv : ps.length = L * M) : ∀ r ∈ rotRows M L a ps, r.length = M := by
  intro r hr
  rw [rotRows, List.mem_rotate] at hr
  exact length_mem_rowsOf M L ps (le_of_eq hv.symm) r hr

theorem isRecR_D1_head (hM : 1 ≤ M) (hv : ps.length = L * M) (j : ℕ) :
    isRecR ((arrSyms (((rotRows M L a ps).drop j).flatten) ++ [Sym.mark]).head?) =
      decide (j < L) := by
  by_cases hj : j < L
  · have hlt : j < (rotRows M L a ps).length := by rw [length_rotRows]; exact hj
    rw [List.drop_eq_getElem_cons hlt, List.flatten_cons]
    have hlen := length_mem_rotRows M L a ps hv _ (List.getElem_mem hlt)
    obtain ⟨p, q, hpq⟩ : ∃ p q, (rotRows M L a ps)[j] = p :: q := by
      cases h : (rotRows M L a ps)[j] with
      | nil => rw [h] at hlen; simp at hlen; omega
      | cons p q => exact ⟨p, q, rfl⟩
    rw [hpq, List.cons_append, isRecR_head_cons]
    exact (decide_eq_true hj).symm
  · rw [List.drop_eq_nil_of_le (by rw [length_rotRows]; omega), List.flatten_nil, arrSyms_nil,
      List.nil_append]
    simp [isRecR, hj]

/-- Row-reversal invariant with `n` rows remaining on `D1`. -/
def rvState (n : ℕ) : RLoc → List Sym :=
  Function.update (Function.update S (.inl 0)
    (arrSyms (((rotRows M L a ps).take (L - n)).reverse.flatten) ++ rest))
    (.inr .D1) (arrSyms (((rotRows M L a ps).drop (L - n)).flatten) ++ [Sym.mark])

theorem rev_row (hclean : KClean S) (hM : 1 ≤ M) (hv : ps.length = L * M) (rM : List Sym)
    (hrM : TermOK rM) (hctr : S (.inl 1) = natSyms M ++ rM) (n : ℕ) (hn : n < L) :
    Runs revRow (rvState S M L a ps rest (n + 1)) (rvState S M L a ps rest n)
      (fun v => isRecR v = decide (0 < n))
      (6 * vol (((rotRows M L a ps).drop (L - (n + 1))).flatten) -
        6 * vol (((rotRows M L a ps).drop (L - n)).flatten) + (mvConst M + 4)) := by
  obtain ⟨k, hk⟩ : ∃ k, k = L - (n + 1) := ⟨_, rfl⟩
  have hk1 : L - n = k + 1 := by omega
  rw [← hk, hk1]
  have hlt : k < (rotRows M L a ps).length := by rw [length_rotRows]; omega
  have hdrop := List.drop_eq_getElem_cons hlt
  set R := (rotRows M L a ps)[k] with hR
  set Q := ((rotRows M L a ps).drop (k + 1)).flatten with hQ
  have hRl : R.length = M := length_mem_rotRows M L a ps hv R (List.getElem_mem hlt)
  have htake : (rotRows M L a ps).take (k + 1) = (rotRows M L a ps).take k ++ [R] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    rfl
  -- state 0
  set S0 := rvState S M L a ps rest (n + 1) with hS0
  have hS0D : S0 (.inr .D1) = arrSyms (R ++ Q) ++ [Sym.mark] := by
    rw [hS0, rvState, Function.update_self, show L - (n + 1) = k by omega, hdrop,
      List.flatten_cons]
  have e1 : Runs (pushC (.inr .Tmp) .mark) S0
      (Function.update S0 (.inr .Tmp) (Sym.mark :: S0 (.inr .Tmp))) (fun _ => True) 1 := by
    apply Runs.of_eval
    intro x
    exact ⟨x, 1, pushC_eval _ _ x S0, trivial, le_rfl⟩
  set S1 := Function.update S0 (.inr .Tmp) (Sym.mark :: S0 (.inr .Tmp)) with hS1
  have hS1ctr : S1 (.inl 1) = natSyms M ++ rM := by
    rw [hS1, Function.update_of_ne (by decide), hS0, rvState, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hctr]
  have hS1cnt : S1 (.inr .cnt) = [] := by
    rw [hS1, Function.update_of_ne (by decide), hS0, rvState, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hclean]
  have hS1D : S1 (.inr .D1) = arrSyms (R ++ Q) ++ [Sym.mark] := by
    rw [hS1, Function.update_of_ne (by decide), hS0D]
  have e2 := moveM_runs (ctr := (.inl 1 : RLoc)) (src := .inr .D1) (dst := .inr .Tmp)
    (cnt := .inr .cnt) (ctmp := .inr .ctmp) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S1 M rM hrM R Q hRl [Sym.mark] hS1ctr hS1cnt hS1D
  set S2 := Function.update (Function.update S1 (.inr .D1) (arrSyms Q ++ [Sym.mark])) (.inr .Tmp)
    ((arrSyms R).reverse ++ S1 (.inr .Tmp)) with hS2
  have hS2T : S2 (.inr .Tmp) = (arrSyms R).reverse ++ Sym.mark :: [] := by
    rw [hS2, Function.update_self, hS1, Function.update_self, hS0, rvState,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), hclean]
  have e3 : Runs (rewindTo (.inr .Tmp) (.inl 0) .mark) S2
      (Function.update (Function.update S2 (.inr .Tmp) []) (.inl 0)
        ((arrSyms R).reverse.reverse ++ S2 (.inl 0))) (fun _ => True)
      (3 * (arrSyms R).reverse.length + 2) := by
    apply Runs.of_eval
    intro x
    exact ⟨_, _, rewindTo_eval (by decide) .mark x _ [] S2 (mark_not_mem_reverse_arrSyms _) hS2T,
      trivial, le_rfl⟩
  set S3 := Function.update (Function.update S2 (.inr .Tmp) []) (.inl 0)
    ((arrSyms R).reverse.reverse ++ S2 (.inl 0)) with hS3
  have e4 : Runs (peekR (.inr .D1)) S3 S3 (fun v => isRecR v = decide (0 < n)) 1 := by
    apply Runs.of_eval
    intro x
    refine ⟨_, 1, peekR_eval (.inr .D1) x S3, ?_, le_rfl⟩
    have hD : S3 (.inr .D1) = arrSyms (((rotRows M L a ps).drop (k + 1)).flatten) ++ [Sym.mark] := by
      rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS2,
        Function.update_of_ne (by decide), Function.update_self]
    rw [hD, isRecR_D1_head M L a ps hM hv (k + 1)]
    exact decide_eq_decide.2 ⟨fun _ => by omega, fun _ => by omega⟩
  have h := runs_seq e1 (runs_seq e2 (runs_seq e3 e4))
  have hfin : S3 = rvState S M L a ps rest n := by
    rw [rvState, hk1, htake]
    funext key
    rcases key with i | e
    · fin_cases i
      · simp [hS3, hS2, hS1, hS0, rvState, Function.update_apply, show L - (n + 1) = k by omega,
          arrSyms_append, List.reverse_append, List.append_assoc]
      · simp [hS3, hS2, hS1, hS0, rvState, Function.update_apply]
    · cases e <;> simp [hS3, hS2, hS1, hS0, rvState, Function.update_apply, hclean .Tmp, hQ]
  refine runs_mono (runs_congr h hfin) (fun _ hq => hq) ?_
  have hv1 : vol (((rotRows M L a ps).drop k).flatten) = vol R + vol Q := by
    rw [hdrop, List.flatten_cons, vol_append]
  have hl : (arrSyms R).reverse.length = vol R := by simp [vol]
  rw [hl]
  have hmv : M * (6 * bitLen M + 10) + 7 * bitLen M + 9 = mvConst M := rfl
  omega

/-- **The reindex program** `reverseRows ∘ rotateLeft a`, bit-record form. -/
theorem reindex_main (hclean : KClean S) (hM : 1 ≤ M) (ha : a ≤ L) (hv : ps.length = L * M)
    (hrest : BlkTerm rest) (rM : List Sym) (hrM : TermOK rM)
    (hsrc : S (.inl 0) = arrSyms ps ++ rest) (hctr : S (.inl 1) = natSyms M ++ rM) :
    Runs (reindexProg a) S (Function.update S (.inl 0) (arrSyms (reindexRot a M ps) ++ rest))
      (fun _ => True) (12 * vol ps + ps.length * (26 * bitLen M + 50) + 13) := by
  have hM0 : 0 < M := hM
  -- marks
  have h1 : Runs reMarks S (preState S M ps rest 0) (fun _ => True) 3 := by
    apply Runs.of_eval
    intro x
    have e1 := pushC_eval (.inr .Pre : RLoc) .mark x S
    have e2 := pushC_eval (.inr .Suf : RLoc) .mark x (Function.update S (.inr .Pre)
      (.mark :: S (.inr .Pre)))
    have e3 := pushC_eval (.inr .D1 : RLoc) .mark x (Function.update (Function.update S (.inr .Pre)
      (.mark :: S (.inr .Pre))) (.inr .Suf) (.mark :: Function.update S (.inr .Pre)
        (.mark :: S (.inr .Pre)) (.inr .Suf)))
    refine ⟨x, 3, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, trivial, le_rfl⟩
    congr 1
    funext key
    rcases key with i | e
    · fin_cases i <;> simp [preState, Function.update_apply, hsrc]
    · cases e <;> simp [preState, Function.update_apply, hclean .Pre, hclean .Suf, hclean .D1,
        arrSyms_nil]
  -- prefix moves
  have hle0 : (0 + a) * M ≤ ps.length := by
    rw [hv, Nat.zero_add]
    exact Nat.mul_le_mul_right _ ha
  have h2 := prefix_runs S M ps rest hclean rM hrM hctr a 0 hle0
  rw [Nat.zero_add] at h2
  -- moveAll
  have hPs : preState S M ps rest a (.inl 0) = arrSyms (ps.drop (a * M)) ++ rest := by
    rw [preState, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have h3 := moveAll_runs (src := (.inl 0 : RLoc)) (dst := .inr .Suf) (by decide)
    (preState S M ps rest a) (ps.drop (a * M)) rest hrest hPs
  set S3 := Function.update (Function.update (preState S M ps rest a) (.inl 0) rest) (.inr .Suf)
    ((arrSyms (ps.drop (a * M))).reverse ++ preState S M ps rest a (.inr .Suf)) with hS3
  -- rewind Pre onto D1
  have hS3P : S3 (.inr .Pre) = (arrSyms (ps.take (a * M))).reverse ++ Sym.mark :: [] := by
    rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), preState,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have h4 : Runs (rewindTo (.inr .Pre) (.inr .D1) .mark) S3
      (Function.update (Function.update S3 (.inr .Pre) []) (.inr .D1)
        ((arrSyms (ps.take (a * M))).reverse.reverse ++ S3 (.inr .D1))) (fun _ => True)
      (3 * (arrSyms (ps.take (a * M))).reverse.length + 2) := by
    apply Runs.of_eval
    intro x
    exact ⟨_, _, rewindTo_eval (by decide) .mark x _ [] S3 (mark_not_mem_reverse_arrSyms _) hS3P,
      trivial, le_rfl⟩
  set S4 := Function.update (Function.update S3 (.inr .Pre) []) (.inr .D1)
    ((arrSyms (ps.take (a * M))).reverse.reverse ++ S3 (.inr .D1)) with hS4
  -- rewind Suf onto D1
  have hS4S : S4 (.inr .Suf) = (arrSyms (ps.drop (a * M))).reverse ++ Sym.mark :: [] := by
    rw [hS4, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS3,
      Function.update_self, preState, Function.update_of_ne (by decide), Function.update_self]
  have h5 : Runs (rewindTo (.inr .Suf) (.inr .D1) .mark) S4
      (Function.update (Function.update S4 (.inr .Suf) []) (.inr .D1)
        ((arrSyms (ps.drop (a * M))).reverse.reverse ++ S4 (.inr .D1))) (fun _ => True)
      (3 * (arrSyms (ps.drop (a * M))).reverse.length + 2) := by
    apply Runs.of_eval
    intro x
    exact ⟨_, _, rewindTo_eval (by decide) .mark x _ [] S4 (mark_not_mem_reverse_arrSyms _) hS4S,
      trivial, le_rfl⟩
  have hrv : Function.update (Function.update S4 (.inr .Suf) []) (.inr .D1)
      ((arrSyms (ps.drop (a * M))).reverse.reverse ++ S4 (.inr .D1)) =
      rvState S M L a ps rest L := by
    have hflat : ((rotRows M L a ps).drop (L - L)).flatten = ps.drop (a * M) ++ ps.take (a * M) := by
      rw [Nat.sub_self, List.drop_zero, rotRows, flatten_rotate_rowsOf M L a ps hv ha]
    rw [rvState, hflat]
    funext key
    rcases key with i | e
    · fin_cases i <;> simp [hS4, hS3, preState, Function.update_apply, arrSyms_nil]
    · cases e <;> simp [hS4, hS3, preState, Function.update_apply, hclean .Pre, hclean .Suf,
        hclean .D1, hclean .Tmp, hclean .cnt, hclean .ctmp, arrSyms_append, List.append_assoc]
  have hrot := runs_seq h2 (runs_seq h3 (runs_seq h4 (runs_congr h5 hrv)))
  -- the row reversal
  have h0 : Runs (peekR (.inr .D1)) (rvState S M L a ps rest L) (rvState S M L a ps rest L)
      (fun v => isRecR v = decide (0 < L)) 1 := by
    apply Runs.of_eval
    intro x
    refine ⟨_, 1, peekR_eval (.inr .D1 : RLoc) x _, ?_, le_rfl⟩
    have hD : rvState S M L a ps rest L (.inr .D1) =
        arrSyms (((rotRows M L a ps).drop 0).flatten) ++ [Sym.mark] := by
      rw [rvState, Function.update_self, Nat.sub_self]
    rw [hD, isRecR_D1_head M L a ps hM hv 0]
  have hloop := API.seq_loop_pot (ρ := []) (p := revRow) (c := isRecR)
    (st := rvState S M L a ps rest) (S := rvState S M L a ps rest L)
    (B := fun n => 6 * vol (((rotRows M L a ps).drop (L - (n + 1))).flatten) -
        6 * vol (((rotRows M L a ps).drop (L - n)).flatten) + (mvConst M + 4))
    (Φ := fun n => 6 * vol (((rotRows M L a ps).drop (L - n)).flatten)) (a := mvConst M + 4)
    (N := L) ((API.runsIn_nil_iff _ _ _ _ _).2 h0)
    (fun n hn => (API.runsIn_nil_iff _ _ _ _ _).2
      (rev_row S M L a ps rest hclean hM hv rM hrM hctr n hn))
    (fun n hn => by
      have hle : vol (((rotRows M L a ps).drop (L - n)).flatten) ≤
          vol (((rotRows M L a ps).drop (L - (n + 1))).flatten) := by
        have hlt : L - (n + 1) < (rotRows M L a ps).length := by rw [length_rotRows]; omega
        rw [List.drop_eq_getElem_cons hlt, List.flatten_cons, vol_append,
          show L - (n + 1) + 1 = L - n by omega]
        omega
      omega)
  have hl := (API.runsIn_nil_iff _ _ _ _ _).1 hloop
  have hpop : Runs (popR (.inr .D1)) (rvState S M L a ps rest 0)
      (Function.update S (.inl 0) (arrSyms (reindexRot a M ps) ++ rest)) (fun _ => True) 1 := by
    have hre : reindexRot a M ps = ((rotRows M L a ps).take L).reverse.flatten := by
      rw [reindexRot, rowsOf_eq hM0 hv, List.take_of_length_le (by rw [length_rotRows])]
      rfl
    have hdL : (rotRows M L a ps).drop L = [] :=
      List.drop_eq_nil_of_le (by rw [length_rotRows])
    have hst : Function.update (rvState S M L a ps rest 0) (.inr .D1)
        ((rvState S M L a ps rest 0) (.inr .D1)).tail =
        Function.update S (.inl 0) (arrSyms (reindexRot a M ps) ++ rest) := by
      funext key
      rcases key with i | e
      · fin_cases i <;> simp [rvState, Function.update_apply, hre]
      · cases e <;> simp [rvState, Function.update_apply, hdL, arrSyms_nil, hclean .D1]
    apply Runs.of_eval
    intro x
    exact ⟨_, 1, (popR_eval (.inr .D1 : RLoc) x _).of_eq (by rw [hst]) rfl, trivial, le_rfl⟩
  have h := runs_seq h1 (runs_seq hrot (runs_seq hl hpop))
  refine runs_mono h (fun _ _ => trivial) ?_
  -- cost
  have hvta : vol ps = vol (ps.take (a * M)) + vol (ps.drop (a * M)) := by
    rw [← vol_append, List.take_append_drop]
  have hl1 : (arrSyms (ps.take (a * M))).reverse.length = vol (ps.take (a * M)) := by simp [vol]
  have hl2 : (arrSyms (ps.drop (a * M))).reverse.length = vol (ps.drop (a * M)) := by simp [vol]
  have hΦ : vol (((rotRows M L a ps).drop (L - L)).flatten) = vol ps := by
    rw [Nat.sub_self, List.drop_zero, rotRows, flatten_rotate_rowsOf M L a ps hv ha, vol_append]
    omega
  have hdl : (ps.drop (a * M)).length ≤ ps.length := by simp
  rw [hl1, hl2, hΦ, Nat.zero_mul, List.drop_zero]
  have hb : (a + L) * (mvConst M + 5) ≤ ps.length * (26 * bitLen M + 48) := by
    rw [hv]
    have h2 : (a + L) * (mvConst M + 5) ≤ (2 * L) * (mvConst M + 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : L ≤ L * M := Nat.le_mul_of_pos_right L hM0
    have h4 : (2 * L) * (7 * bitLen M + 14) ≤ (2 * (L * M)) * (7 * bitLen M + 14) :=
      Nat.mul_le_mul_right _ (by omega)
    have h5 : (2 * L) * (mvConst M + 5) =
        (2 * (L * M)) * (6 * bitLen M + 10) + (2 * L) * (7 * bitLen M + 14) := by
      simp only [mvConst]; ring
    have h6 : (L * M) * (26 * bitLen M + 48) =
        (2 * (L * M)) * (6 * bitLen M + 10) + (2 * (L * M)) * (7 * bitLen M + 14) := by ring
    omega
  have hb' : a * mvConst M + L * (mvConst M + 4 + 1) ≤ ps.length * (26 * bitLen M + 48) := by
    have h7 : (a + L) * (mvConst M + 5) = a * mvConst M + L * (mvConst M + 4 + 1) + 5 * a := by
      ring
    omega
  have he : ps.length * (26 * bitLen M + 50) = ps.length * (26 * bitLen M + 48) + 2 * ps.length := by
    ring
  have hvd : vol (ps.drop (a * M)) ≤ vol ps := by omega
  omega

end ReindexMain

end SubNLogN.Machine.Bridge.SolveBAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.Bridge.SolveBAux

/-- **K5-SOLVE-b: the backward input reindex `I` meets `SolveReindexIStmt`** (constant `64`). -/
theorem solveReindexI_holds : SolveReindexIStmt := by
  refine ⟨64, fun _ => ⟨ReE, inferInstance, inferInstance, Option Sym, reindexProg 2,
    inferInstance, ⟨none⟩, closed_reindexProg 2, ?_⟩⟩
  intro wd L M u rest rM S hclean hM hL hu hrest hrM hsrc hctr
  have hps : (u.map (crecBits wd)).length = L * M := by rw [List.length_map, hu]
  have h := reindex_main S M L 2 (u.map (crecBits wd)) rest hclean hM hL hps hrest rM hrM hsrc
    hctr
  rw [SolveSplit.reindexRot_map] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  have hcv : cvol wd u = vol (u.map (crecBits wd)) := rfl
  rw [hcv, List.length_map]
  nlinarith

/-- **K5-SOLVE-b: the backward output readout `J` meets `SolveReindexJStmt`** (constant `64`). -/
theorem solveReindexJ_holds : SolveReindexJStmt := by
  refine ⟨64, fun _ => ⟨ReE, inferInstance, inferInstance, Option Sym, reindexProg 1,
    inferInstance, ⟨none⟩, closed_reindexProg 1, ?_⟩⟩
  intro wd L M u rest rM S hclean hM hL hu hrest hrM hsrc hctr
  have hps : (u.map (crecBits wd)).length = L * M := by rw [List.length_map, hu]
  have h := reindex_main S M L 1 (u.map (crecBits wd)) rest hclean hM (by omega) hps hrest rM
    hrM hsrc hctr
  rw [SolveSplit.reindexRot_map] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  have hcv : cvol wd u = vol (u.map (crecBits wd)) := rfl
  rw [hcv, List.length_map]
  nlinarith

end SubNLogN.Machine
