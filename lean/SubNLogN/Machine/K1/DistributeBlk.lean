/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DistributeBlkCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# K1-dist, block rows (`K1/DistributeBlk.lean`): `K2DistributeBlkStmt W`, `K2MergeBlkStmt W ord`

**Scope (honest summary).** Fully proved (no placeholders), no hypotheses beyond the contracts' own:
* `SubNLogN.Machine.k2DistributeBlk_holds (W : ℕ) : K2DistributeBlkStmt W`,
* `SubNLogN.Machine.k2MergeBlk_holds (W : ℕ) (ord : Equiv.Perm (Fin W)) : K2MergeBlkStmt W ord`.

Paper: Fact 3.3(3) (`fact:oai-streams`) and Lemma A.4(4) (`lem:transfer-streams`:
distributing complete rows cyclically among a fixed number `W` of streams, and merging them in a
fixed order of the row classes). Here a *row* is a block of `s` consecutive records (`s` a runtime
counter, restored), as in Proposition A.7 (`prop:transfer11`) and Lemma A.10 (`lem:transfer-phase`). Contracts:
`Contracts/Streams.lean` (`K2DistributeBlkStmt`, `K2MergeBlkStmt`, specs `roleBlocks`,
`mergeBlocks`, posts `distBlkPost`, `mergeBlkPost`).

**Constants (what is proved).** Distribution `C = 16·W + 30` (an additive `Θ(W)` is forced by this
program shape; the per-round `O(W)` overhead is bounded coarsely); merge `C = 43` for `W ≥ 1`
(independent of `W`: every round moves `W` full rows), `C = 1` for `W = 0`.

## Program design (same skeleton as `K1/Distribute.lean`, rows in place of records)
A row moves with `rowMove src dst cnt T tmp` (`K1/DistributeBlkCore.lean`): copy the counter `s`
onto `T` above a `mark`, then `s` times `moveRec` + `dec`; the decrements are amortized by
`incSeqCost_le`, so a row costs `≤ 3·vol(row) + 23·s + 11 ≤ 26·vol(row) + 11` (`s ≤ vol(row)`).
* **Distribution** (named `Fin 2 ⊕ Fin W`: `inl 0` source, `inl 1` counter, `inr w` role stacks;
  scratch `Fin W ⊕ Fin 2`: `inl k` collector of class `k`, `inr 0` = `T`, `inr 1` = `tmp`):
  marks on the collectors; rounds `forEachFin W (k ↦ growMove src (collector k))` (guarded row
  moves; round `j` deals rows `jW, …, jW + W - 1`, row `jW + k` has class `k`) while the source has a
  record; then `rewindTo` each collector onto its role stack. Invariant `dBState pos`: the first
  `pos` records are dealt. `W = 0`: `dropArr`.
* **Merge** (same named stacks, `inl 0` = destination; scratch `Unit ⊕ Fin 2`: `Z`, `T`, `tmp`):
  mark on `Z`; while role stack `0` has a record: `forEachFin W (c ↦ rowMove (role (ord c)) Z)`;
  then `rewindTo Z dst`. Invariants `lBState` (loop) and `rBState` (inside a round). For `s = 0`
  the streams are empty and the loop exits at once. `W = 0`: `skip`.
-/

namespace SubNLogN.Machine.K2

open TMFw TMFw.Contracts TMFw.Lib WP.W9comp

/-! ## K2a-blk: distribution of block rows -/

/-- Stacks of the block distribution kernel. Named `Fin 2 ⊕ Fin W` (`inl 0` source, `inl 1`
counter `s`, `inr w` role stack `w`); scratch `Fin W ⊕ Fin 2` (`inl k` collector of class `k`,
`inr 0` = `T`, `inr 1` = `tmp`). -/
abbrev DBLoc (W : ℕ) : Type := KLoc (Fin 2 ⊕ Fin W) (Fin W ⊕ Fin 2)

/-- Phase 1: a `mark` on every collector. -/
def distBMarks (W : ℕ) : SProg (DBLoc W) := forEachFin W fun k => pushC (.inr (.inl k)) .mark

/-- One round: deal the next (up to) `W` rows, row `k` of the round onto collector `k`. -/
def distBRound (W : ℕ) : SProg (DBLoc W) :=
  forEachFin W fun k =>
    growMove (.inl (.inl 0)) (.inr (.inl k)) (.inl (.inl 1)) (.inr (.inr 0)) (.inr (.inr 1))

/-- Phase 2: rounds while the source has a record. -/
def distBLoop (W : ℕ) : SProg (DBLoc W) :=
  .loop isRecR (.seq (distBRound W) (peekR (.inl (.inl 0))))

/-- Phase 3: each collector back onto its role stack. -/
def distBBack (W : ℕ) : SProg (DBLoc W) :=
  forEachFin W fun k => rewindTo (.inr (.inl k)) (.inl (.inr k)) .mark

/-- The block distribution program (`W ≥ 1`). -/
def distBProg (W : ℕ) : SProg (DBLoc W) :=
  .seq (distBMarks W) (.seq (.seq (peekR (.inl (.inl 0))) (distBLoop W)) (distBBack W))

theorem closed_distBProg (W : ℕ) : (distBProg W).Closed := by
  have h1 := closed_forEachFin W (fun k => pushC (K := DBLoc W) (.inr (.inl k)) .mark)
    (fun _ => by simp [Prog.Closed, Prog.FreeBelow, pushC])
  have h2 := closed_forEachFin W (fun k => growMove (K := DBLoc W) (.inl (.inl 0)) (.inr (.inl k))
    (.inl (.inl 1)) (.inr (.inr 0)) (.inr (.inr 1))) (fun _ => closed_growMove _ _ _ _ _)
  have h3 := closed_forEachFin W (fun k => rewindTo (K := DBLoc W) (.inr (.inl k)) (.inl (.inr k))
    .mark) (fun _ => by simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR])
  have hp : (peekR (K := DBLoc W) (.inl (.inl 0))).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, peekR]
  exact ⟨h1, ⟨⟨hp, ⟨h2, hp⟩⟩, h3⟩⟩

section DistB

variable {W : ℕ} (s : ℕ) (v : List (List Bool)) (rest : List Sym) (S : DBLoc W → List Sym)

/-- **Invariant of the dealing phase** after the first `pos` records were dealt: the source holds
records `pos, pos + 1, …` on `rest`; collector `k` holds, above its `mark`, the class-`k` records
among the first `pos` (row of record `x` is `x / s`), reversed; all other stacks are untouched. -/
def dBState (pos : ℕ) : DBLoc W → List Sym
  | .inl (.inl i) => if i = 0 then arrSyms (v.drop pos) ++ rest else S (.inl (.inl i))
  | .inl (.inr w) => S (.inl (.inr w))
  | .inr (.inl k) =>
    (arrSyms (roleBlocks W k.val s (v.take pos))).reverse ++ Sym.mark :: S (.inr (.inl k))
  | .inr (.inr j) => S (.inr (.inr j))

theorem dBState_src (pos : ℕ) :
    dBState s v rest S pos (.inl (.inl 0)) = arrSyms (v.drop pos) ++ rest := by
  simp [dBState]

theorem dBState_cnt (pos : ℕ) : dBState s v rest S pos (.inl (.inl 1)) = S (.inl (.inl 1)) := by
  simp [dBState]

theorem dBState_of_le {pos : ℕ} (h : v.length ≤ pos) :
    dBState s v rest S pos = dBState s v rest S v.length := by
  funext key
  rcases key with ((i | w) | (k | j))
  · simp [dBState, List.drop_eq_nil_of_le h]
  · rfl
  · simp [dBState, List.take_of_length_le h]
  · rfl

/-- **One row step** (row `m`, class `i = m % W`): `dBState (m·s)` to `dBState ((m+1)·s)`; a no-op
once the source is exhausted. Cost `≤ 13 + 26·(vol of row m)`. -/
theorem distB_step (R : ℕ) (hR : v.length = R * s) (hrest : BlkTerm rest) (r1 : List Sym)
    (hr1 : TermOK r1) (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1) (i : Fin W) (m : ℕ)
    (hm : m % W = i.val) :
    Runs (growMove (K := DBLoc W) (.inl (.inl 0)) (.inr (.inl i)) (.inl (.inl 1)) (.inr (.inr 0))
        (.inr (.inr 1)))
      (dBState s v rest S (m * s)) (dBState s v rest S ((m + 1) * s)) (fun _ => True)
      (13 + (26 * vol (v.drop (m * s)) - 26 * vol (v.drop ((m + 1) * s)))) := by
  apply Runs.of_eval
  intro x
  have hms : (m + 1) * s = m * s + s := Nat.succ_mul m s
  by_cases hlt : m * s < v.length
  · have hsle : s ≤ (v.drop (m * s)).length := by
      rw [List.length_drop, hR]
      have hmR : m < R := by
        by_contra hc
        have := Nat.mul_le_mul_right s (Nat.le_of_not_lt hc)
        omega
      have := Nat.mul_le_mul_right s (show m + 1 ≤ R by omega)
      omega
    have hne : v.drop (m * s) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
      omega
    have hdd : (v.drop (m * s)).drop s = v.drop ((m + 1) * s) := by
      rw [List.drop_drop, hms]
    have e := growMove_eval_row (src := (.inl (.inl 0) : DBLoc W)) (dst := .inr (.inl i))
      (cnt := .inl (.inl 1)) (T := .inr (.inr 0)) (tmp := .inr (.inr 1)) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) x s r1 hr1 (v.drop (m * s)) hne rest
      (dBState s v rest S (m * s)) hsle (dBState_src s v rest S _)
      (by rw [dBState_cnt]; exact hcnt)
    refine ⟨some Sym.mark, _, e.of_eq ?_ rfl, trivial, ?_⟩
    · congr 1
      funext key
      rcases key with ((i' | w) | (k | j))
      · by_cases hi : i' = 0
        · subst hi
          rw [Function.update_of_ne (by simp), Function.update_self, dBState_src, hdd]
        · simp [dBState, hi]
      · simp [dBState]
      · by_cases hk : k = i
        · subst hk
          have hr : roleBlocks W k.val s (v.take ((m + 1) * s)) =
              roleBlocks W k.val s (v.take (m * s)) ++ (v.drop (m * s)).take s := by
            rw [hms, roleBlocks_take_row W k.val s m v s le_rfl, if_pos hm]
          simp only [Function.update_self, dBState, hr, arrSyms_append, List.reverse_append,
            List.append_assoc]
        · have hk' : ¬ m % W = k.val := by
            rw [hm]
            exact fun h => hk (Fin.ext h.symm)
          have hr : roleBlocks W k.val s (v.take ((m + 1) * s)) =
              roleBlocks W k.val s (v.take (m * s)) := by
            rw [hms, roleBlocks_take_row W k.val s m v s le_rfl, if_neg hk', List.append_nil]
          rw [Function.update_of_ne (by simpa using hk), Function.update_of_ne (by simp)]
          simp only [dBState, hr]
      · simp [dBState]
    · have hrow : vol (v.drop (m * s)) =
          vol ((v.drop (m * s)).take s) + vol (v.drop ((m + 1) * s)) := by
        rw [← hdd, vol_take_add_drop]
      have hsv : s ≤ vol ((v.drop (m * s)).take s) := by
        have := length_le_vol ((v.drop (m * s)).take s)
        rwa [List.length_take, Nat.min_eq_left hsle] at this
      have hc := rowMove_cost_le s (v.drop (m * s))
      omega
  · have hd : v.drop (m * s) = [] := List.drop_eq_nil_of_le (by omega)
    have htest : isRecR ((dBState s v rest S (m * s)) (.inl (.inl 0))).head? = false := by
      rw [dBState_src, hd, arrSyms_nil, List.nil_append]
      exact isRecR_of_blkTerm hrest
    have hle2 : v.length ≤ (m + 1) * s := by
      have := Nat.mul_le_mul_right s (Nat.le_succ m)
      omega
    refine ⟨(dBState s v rest S (m * s) (.inl (.inl 0))).head?, 3,
      (growMove_eval_skip x _ htest).of_eq ?_ rfl, trivial, by omega⟩
    rw [dBState_of_le s v rest S (by omega : v.length ≤ m * s), dBState_of_le s v rest S hle2]

/-- **One round** from row `m0` (a multiple of `W`): `dBState (m0·s)` to `dBState ((m0+W)·s)`. -/
theorem distB_round (R : ℕ) (hR : v.length = R * s) (hrest : BlkTerm rest) (r1 : List Sym)
    (hr1 : TermOK r1) (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1) (m0 : ℕ) (hm0 : m0 % W = 0) :
    Runs (distBRound W) (dBState s v rest S (m0 * s)) (dBState s v rest S ((m0 + W) * s))
      (fun _ => True)
      (W * 13 + (26 * vol (v.drop (m0 * s)) - 26 * vol (v.drop ((m0 + W) * s))) + 1) := by
  have h := runs_forEachFin_pot W (fun k => growMove (K := DBLoc W) (.inl (.inl 0)) (.inr (.inl k))
      (.inl (.inl 1)) (.inr (.inr 0)) (.inr (.inr 1)))
    (fun i => dBState s v rest S ((m0 + i) * s)) (fun i => 26 * vol (v.drop ((m0 + i) * s))) 13
    (fun i => by
      have := vol_drop_anti v (Nat.mul_le_mul_right s (show m0 + i ≤ m0 + (i + 1) by omega))
      omega)
    (fun i => by
      have hm : (m0 + i.val) % W = i.val := by
        rw [Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
      exact distB_step s v rest S R hR hrest r1 hr1 hcnt i (m0 + i.val) hm)
  exact h

/-- The dealing loop stops when the source is exhausted. -/
theorem distB_loop_exit (hrest : BlkTerm rest) (m : ℕ) (hm : v.length ≤ m * s) :
    Eval [] (distBLoop W)
      ⟨(dBState s v rest S (m * s) (.inl (.inl 0))).head?, dBState s v rest S (m * s)⟩
      ⟨(dBState s v rest S (m * s) (.inl (.inl 0))).head?, dBState s v rest S v.length⟩ 1 := by
  have hd : v.drop (m * s) = [] := List.drop_eq_nil_of_le hm
  have htest : isRecR (dBState s v rest S (m * s) (.inl (.inl 0))).head? = false := by
    rw [dBState_src, hd, arrSyms_nil, List.nil_append]
    exact isRecR_of_blkTerm hrest
  refine (Eval.loop_false htest).of_eq ?_ rfl
  rw [dBState_of_le s v rest S hm]

/-- **The dealing loop.** From row `m` (a multiple of `W`; register = peeked source top) the loop
reaches `dBState v.length` within `(13·W + 4)·(records left) + 26·(volume left) + 1`. -/
theorem distB_loop (hW : 0 < W) (R : ℕ) (hR : v.length = R * s) (hrest : BlkTerm rest)
    (r1 : List Sym) (hr1 : TermOK r1) (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1) :
    ∀ (d m : ℕ), v.length - m * s ≤ d → m % W = 0 →
      ∃ x' t, Eval [] (distBLoop W)
          ⟨(dBState s v rest S (m * s) (.inl (.inl 0))).head?, dBState s v rest S (m * s)⟩
          ⟨x', dBState s v rest S v.length⟩ t ∧
        t ≤ (13 * W + 4) * (v.length - m * s) + 26 * vol (v.drop (m * s)) + 1 := by
  intro d
  induction d with
  | zero =>
    intro m hd _
    exact ⟨_, 1, distB_loop_exit s v rest S hrest m (by omega), by omega⟩
  | succ d ih =>
    intro m hd hm
    by_cases hlt : m * s < v.length
    · have hs : 0 < s := by
        rcases Nat.eq_zero_or_pos s with h | h
        · rw [h, Nat.mul_zero] at hR
          omega
        · exact h
      obtain ⟨⟨x1, S1⟩, t1, e1, ⟨hS1, -⟩, ht1⟩ :=
        distB_round s v rest S R hR hrest r1 hr1 hcnt m hm
          ⟨(dBState s v rest S (m * s) (.inl (.inl 0))).head?, dBState s v rest S (m * s)⟩ rfl
      simp only at hS1
      subst hS1
      have hm' : (m + W) % W = 0 := by
        rw [Nat.add_mod_right]
        exact hm
      have hmW : m * s + s ≤ (m + W) * s := by
        have := Nat.mul_le_mul_right s (show m + 1 ≤ m + W by omega)
        rw [Nat.succ_mul] at this
        exact this
      obtain ⟨x', t2, e2, ht2⟩ := ih (m + W) (by omega) hm'
      have epk := peekR_eval (.inl (.inl 0) : DBLoc W) x1 (dBState s v rest S ((m + W) * s))
      have htest : isRecR (dBState s v rest S (m * s) (.inl (.inl 0))).head? = true := by
        rw [dBState_src, List.drop_eq_getElem_cons hlt]
        exact isRecR_head_cons _ _ _
      refine ⟨x', t1 + 1 + t2 + 1, Eval.loop_true htest (Eval.seq e1 epk) e2, ?_⟩
      have hvol := vol_drop_anti v (show m * s ≤ (m + W) * s by omega)
      have hK : (13 * W + 4) * (v.length - (m + W) * s) + (13 * W + 4) ≤
          (13 * W + 4) * (v.length - m * s) := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    · exact ⟨_, 1, distB_loop_exit s v rest S hrest m (by omega), by omega⟩

/-- Intermediate states of the marker phase (`mark` pushed on the collectors `k < i`). -/
def markBState (i : ℕ) : DBLoc W → List Sym
  | .inl x => S (.inl x)
  | .inr (.inl k) => if k.val < i then Sym.mark :: S (.inr (.inl k)) else S (.inr (.inl k))
  | .inr (.inr j) => S (.inr (.inr j))

/-- **Phase 1** (markers): `S` to `dBState 0`, cost `W + 1`. -/
theorem distB_marks (hS : S (.inl (.inl 0)) = arrSyms v ++ rest) :
    Runs (distBMarks W) S (dBState s v rest S 0) (fun _ => True) (W + 1) := by
  have h := runs_forEachFin W (fun k => pushC (K := DBLoc W) (.inr (.inl k)) .mark) (fun _ => 1)
    (markBState S) (fun i => by
      apply Runs.of_eval
      intro x
      refine ⟨x, 1, (pushC_eval _ _ x _).of_eq ?_ rfl, trivial, le_rfl⟩
      congr 1
      funext key
      rcases key with x' | (k | j)
      · simp [markBState]
      · by_cases hk : k = i
        · subst hk
          simp [markBState]
        · have hk' : k.val ≠ i.val := fun h => hk (Fin.ext h)
          rw [Function.update_of_ne (by simpa using hk)]
          by_cases hlt : k.val < i.val
          · simp [markBState, hlt, show k.val < i.val + 1 by omega]
          · simp [markBState, hlt, show ¬ k.val < i.val + 1 by omega]
      · simp [markBState])
  have h0 : markBState S 0 = S := by
    funext key
    rcases key with x | (k | j) <;> simp [markBState]
  have hW : markBState S W = dBState s v rest S 0 := by
    funext key
    rcases key with ((i | w) | (k | j))
    · by_cases hi : i = 0
      · subst hi
        simp [markBState, dBState, hS]
      · simp [markBState, dBState, hi]
    · simp [markBState, dBState]
    · simp [markBState, dBState, roleBlocks_nil, arrSyms_nil]
    · simp [markBState, dBState]
  rw [h0, hW] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  simp

/-- Intermediate states of the move-back phase (classes `k < i` already on their role stacks). -/
def backBState (i : ℕ) : DBLoc W → List Sym
  | .inl (.inl i') => if i' = 0 then rest else S (.inl (.inl i'))
  | .inl (.inr r) =>
    if r.val < i then arrSyms (roleBlocks W r.val s v) ++ S (.inl (.inr r))
    else S (.inl (.inr r))
  | .inr (.inl k) =>
    if k.val < i then S (.inr (.inl k))
    else (arrSyms (roleBlocks W k.val s v)).reverse ++ Sym.mark :: S (.inr (.inl k))
  | .inr (.inr j) => S (.inr (.inr j))

/-- **Phase 3** (move back): `dBState v.length` to `distBlkPost s v rest S`; coarsely,
`vol (roleBlocks W k s v) ≤ vol v`. -/
theorem distB_back :
    Runs (distBBack W) (dBState s v rest S v.length) (distBlkPost s v rest S) (fun _ => True)
      (W * (3 * vol v + 2) + 1) := by
  have h := runs_forEachFin W
    (fun k => rewindTo (K := DBLoc W) (.inr (.inl k)) (.inl (.inr k)) .mark)
    (fun k => 3 * vol (roleBlocks W k.val s v) + 2) (backBState s v rest S) (fun i => by
      apply Runs.of_eval
      intro x
      have hsrc : backBState s v rest S i (.inr (.inl i)) =
          (arrSyms (roleBlocks W i.val s v)).reverse ++ Sym.mark :: S (.inr (.inl i)) := by
        simp [backBState]
      have e := rewindTo_eval (src := (.inr (.inl i) : DBLoc W)) (dst := .inl (.inr i)) (by simp)
        .mark x _ _ _ (mark_not_mem_reverse_arrSyms _) hsrc
      refine ⟨some Sym.mark, _, e.of_eq ?_ rfl, trivial, by simp [vol]⟩
      congr 1
      funext key
      rcases key with ((i' | r) | (k | j))
      · simp [backBState]
      · by_cases hr : r = i
        · subst hr
          simp [backBState]
        · have hr' : r.val ≠ i.val := fun h => hr (Fin.ext h)
          rw [Function.update_of_ne (by simpa using hr), Function.update_of_ne (by simp)]
          by_cases hlt : r.val < i.val
          · simp [backBState, hlt, show r.val < i.val + 1 by omega]
          · simp [backBState, hlt, show ¬ r.val < i.val + 1 by omega]
      · by_cases hk : k = i
        · subst hk
          simp [backBState]
        · have hk' : k.val ≠ i.val := fun h => hk (Fin.ext h)
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simpa using hk)]
          by_cases hlt : k.val < i.val
          · simp [backBState, hlt, show k.val < i.val + 1 by omega]
          · simp [backBState, hlt, show ¬ k.val < i.val + 1 by omega]
      · simp [backBState])
  have h0 : backBState s v rest S 0 = dBState s v rest S v.length := by
    funext key
    rcases key with ((i | w) | (k | j)) <;> simp [backBState, dBState, arrSyms_nil]
  have hW : backBState s v rest S W = distBlkPost s v rest S := by
    funext key
    rcases key with ((i | w) | (k | j)) <;> simp [backBState, distBlkPost]
  rw [h0, hW] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  have hle : ((List.finRange W).map fun k : Fin W => 3 * vol (roleBlocks W k.val s v) + 2).sum ≤
      ((List.finRange W).map fun _ : Fin W => 3 * vol v + 2).sum :=
    List.sum_le_sum (fun k _ => by have := vol_roleBlocks_le W k.val s v; omega)
  simp only [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul] at hle
  omega

/-- **The block distribution program (`W ≥ 1`) meets the K2a-blk contract**, constant
`16·W + 30`. -/
theorem distB_main (hW : 0 < W) (R : ℕ) (hR : v.length = R * s) (hrest : BlkTerm rest)
    (r1 : List Sym) (hr1 : TermOK r1) (hS : S (.inl (.inl 0)) = arrSyms v ++ rest)
    (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1) :
    Runs (distBProg W) S (distBlkPost s v rest S) (fun _ => True)
      ((16 * W + 30) * (vol v + 1)) := by
  have h1 := distB_marks s v rest S hS
  have h2 : Runs (.seq (peekR (.inl (.inl 0))) (distBLoop W)) (dBState s v rest S 0)
      (dBState s v rest S v.length) (fun _ => True) ((13 * W + 4) * v.length + 26 * vol v + 2) := by
    apply Runs.of_eval
    intro x
    obtain ⟨x', t, e, ht⟩ := distB_loop s v rest S hW R hR hrest r1 hr1 hcnt v.length 0
      (by omega) (Nat.zero_mod W)
    simp only [Nat.zero_mul, Nat.sub_zero, List.drop_zero] at e ht
    exact ⟨x', 1 + t, Eval.seq (peekR_eval _ x _) e, trivial, by omega⟩
  have h := runs_seq h1 (runs_seq h2 (distB_back s v rest S))
  refine runs_mono h (fun _ _ => trivial) ?_
  have hn := length_le_vol v
  have h3 : (13 * W + 4) * v.length ≤ (13 * W + 4) * vol v := Nat.mul_le_mul_left _ hn
  nlinarith

end DistB

/-! ## K2b-blk: merge of block rows -/

/-- Stacks of the block merge kernel. Named `Fin 2 ⊕ Fin W` (`inl 0` destination, `inl 1` counter
`s`, `inr w` role stack `w`); scratch `Unit ⊕ Fin 2` (`inl ()` = `Z`, `inr 0` = `T`,
`inr 1` = `tmp`). -/
abbrev MBLoc (W : ℕ) : Type := KLoc (Fin 2 ⊕ Fin W) (Unit ⊕ Fin 2)

/-- One round: move the next row of each role stack `ord 0, …, ord (W - 1)` (in this order) onto
`Z`. -/
def mergeBRound (W : ℕ) (ord : Equiv.Perm (Fin W)) : SProg (MBLoc W) :=
  forEachFin W fun c =>
    rowMove (.inl (.inr (ord c))) (.inr (.inl ())) (.inl (.inl 1)) (.inr (.inr 0)) (.inr (.inr 1))

/-- Rounds while role stack `r0` has a record. -/
def mergeBLoop (W : ℕ) (ord : Equiv.Perm (Fin W)) (r0 : Fin W) : SProg (MBLoc W) :=
  .loop isRecR (.seq (mergeBRound W ord) (peekR (.inl (.inr r0))))

/-- The block merge program (`W ≥ 1`; `r0` is the role stack tested by the loop). -/
def mergeBProg (W : ℕ) (ord : Equiv.Perm (Fin W)) (r0 : Fin W) : SProg (MBLoc W) :=
  .seq (pushC (.inr (.inl ())) .mark)
    (.seq (.seq (peekR (.inl (.inr r0))) (mergeBLoop W ord r0))
      (rewindTo (.inr (.inl ())) (.inl (.inl 0)) .mark))

theorem closed_mergeBProg (W : ℕ) (ord : Equiv.Perm (Fin W)) (r0 : Fin W) :
    (mergeBProg W ord r0).Closed := by
  have h2 := closed_forEachFin W (fun c => rowMove (K := MBLoc W) (.inl (.inr (ord c)))
    (.inr (.inl ())) (.inl (.inl 1)) (.inr (.inr 0)) (.inr (.inr 1)))
    (fun _ => closed_rowMove _ _ _ _ _)
  have hp : (peekR (K := MBLoc W) (.inl (.inr r0))).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, peekR]
  have hm : (pushC (K := MBLoc W) (.inr (.inl ())) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hr : (rewindTo (K := MBLoc W) (.inr (.inl ())) (.inl (.inl 0)) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR]
  exact ⟨hm, ⟨⟨hp, ⟨h2, hp⟩⟩, hr⟩⟩

section MergeB

variable {W : ℕ} (ord : Equiv.Perm (Fin W)) (s : ℕ) (rests : Fin W → List Sym)
  (S : MBLoc W → List Sym)

/-- **Loop invariant of the block merge**: role stack `r` holds the remaining records `us r` on
`rests r`, `Z` holds `A`, every other stack is untouched. -/
def lBState (us : Fin W → List (List Bool)) (A : List Sym) : MBLoc W → List Sym
  | .inl (.inl i) => S (.inl (.inl i))
  | .inl (.inr r) => arrSyms (us r) ++ rests r
  | .inr (.inl _) => A
  | .inr (.inr j) => S (.inr (.inr j))

/-- **Round invariant** after the first `i` row moves: the classes `ord 0, …, ord (i - 1)` lost
their first row (`take s`), which sits on `Z` (reversed, in this order) above `A`. -/
def rBState (us : Fin W → List (List Bool)) (A : List Sym) (i : ℕ) : MBLoc W → List Sym
  | .inl (.inl i') => S (.inl (.inl i'))
  | .inl (.inr r) =>
    if (ord.symm r).val < i then arrSyms ((us r).drop s) ++ rests r else arrSyms (us r) ++ rests r
  | .inr (.inl _) =>
    (arrSyms (((List.finRange W).take i).flatMap fun c => (us (ord c)).take s)).reverse ++ A
  | .inr (.inr j) => S (.inr (.inr j))

/-- **One row move** of a merge round (class `ord c`). -/
theorem mergeB_step (r1 : List Sym) (hr1 : TermOK r1) (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1)
    (us : Fin W → List (List Bool)) (hus : ∀ r, s ≤ (us r).length) (A : List Sym) (c : Fin W) :
    Runs (rowMove (K := MBLoc W) (.inl (.inr (ord c))) (.inr (.inl ())) (.inl (.inl 1))
        (.inr (.inr 0)) (.inr (.inr 1)))
      (rBState ord s rests S us A c.val) (rBState ord s rests S us A (c.val + 1)) (fun _ => True)
      (3 * vol ((us (ord c)).take s) + incSeqCost 6 10 s + 7 * bitLen s + 11) := by
  apply Runs.of_eval
  intro x
  have hsrc : rBState ord s rests S us A c.val (.inl (.inr (ord c))) =
      arrSyms (us (ord c)) ++ rests (ord c) := by
    simp [rBState]
  have e := rowMove_eval (src := (.inl (.inr (ord c)) : MBLoc W)) (dst := .inr (.inl ()))
    (cnt := .inl (.inl 1)) (T := .inr (.inr 0)) (tmp := .inr (.inr 1)) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) x s r1 hr1 (us (ord c)) (rests (ord c)) _ (hus _) hsrc
    (by simp [rBState, hcnt])
  refine ⟨some Sym.mark, _, e.of_eq ?_ rfl, trivial, le_rfl⟩
  congr 1
  funext key
  rcases key with ((i' | r) | (⟨⟩ | j))
  · simp [rBState]
  · by_cases hr : r = ord c
    · subst hr
      simp [rBState]
    · have hr' : (ord.symm r).val ≠ c.val := fun h => hr (by rw [← Fin.ext h]; simp)
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simpa using hr)]
      by_cases hlt : (ord.symm r).val < c.val
      · simp [rBState, hlt, show (ord.symm r).val < c.val + 1 by omega]
      · simp [rBState, hlt, show ¬ (ord.symm r).val < c.val + 1 by omega]
  · have ht : (List.finRange W).take (c.val + 1) = (List.finRange W).take c.val ++ [c] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp), List.getElem_finRange]
      rfl
    simp only [Function.update_self, rBState, ht, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, arrSyms_append, List.reverse_append, List.append_assoc]
  · simp [rBState]

/-- **One block-merge round**: `lBState us A` to `lBState (drop s ∘ us) (first rows reversed ++ A)`,
cost `≤ 26·(volume of the first rows) + 11·W + 1`. -/
theorem mergeB_round (r1 : List Sym) (hr1 : TermOK r1) (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1)
    (us : Fin W → List (List Bool)) (hus : ∀ r, s ≤ (us r).length) (A : List Sym) :
    Runs (mergeBRound W ord) (lBState rests S us A)
      (lBState rests S (fun r => (us r).drop s)
        ((arrSyms ((List.finRange W).flatMap fun c => (us (ord c)).take s)).reverse ++ A))
      (fun _ => True) (26 * ∑ r, vol ((us r).take s) + 11 * W + 1) := by
  have h := runs_forEachFin W (fun c => rowMove (K := MBLoc W) (.inl (.inr (ord c)))
      (.inr (.inl ())) (.inl (.inl 1)) (.inr (.inr 0)) (.inr (.inr 1)))
    (fun c => 3 * vol ((us (ord c)).take s) + incSeqCost 6 10 s + 7 * bitLen s + 11)
    (rBState ord s rests S us A) (fun c => mergeB_step ord s rests S r1 hr1 hcnt us hus A c)
  have h0 : rBState ord s rests S us A 0 = lBState rests S us A := by
    funext key
    rcases key with ((i | r) | (⟨⟩ | j)) <;> simp [rBState, lBState, arrSyms_nil]
  have hW : rBState ord s rests S us A W = lBState rests S (fun r => (us r).drop s)
      ((arrSyms ((List.finRange W).flatMap fun c => (us (ord c)).take s)).reverse ++ A) := by
    funext key
    rcases key with ((i | r) | (⟨⟩ | j)) <;> simp [rBState, lBState, List.take_of_length_le]
  rw [h0, hW] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  rw [sum_finRange, show (∑ c : Fin W, (3 * vol ((us (ord c)).take s) + incSeqCost 6 10 s +
      7 * bitLen s + 11)) = ∑ r : Fin W, (3 * vol ((us r).take s) + incSeqCost 6 10 s +
      7 * bitLen s + 11) from Equiv.sum_comp ord (fun r => 3 * vol ((us r).take s) +
      incSeqCost 6 10 s + 7 * bitLen s + 11)]
  have hle : ∀ r, 3 * vol ((us r).take s) + incSeqCost 6 10 s + 7 * bitLen s + 11 ≤
      26 * vol ((us r).take s) + 11 := by
    intro r
    have hc := rowMove_cost_le s (us r)
    have hsv : s ≤ vol ((us r).take s) := by
      have := length_le_vol ((us r).take s)
      rwa [List.length_take, Nat.min_eq_left (hus r)] at this
    omega
  have h1 := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hle r)
  have h2 : ∑ r : Fin W, (26 * vol ((us r).take s) + 11) = 26 * ∑ r, vol ((us r).take s) + 11 * W := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, Nat.mul_comm W 11]
  omega

/-- The merge loop exits at once when the tested role stack is empty. -/
theorem mergeB_loop_exit (r0 : Fin W) (hrests : ∀ r, BlkTerm (rests r))
    (us : Fin W → List (List Bool)) (hus : ∀ r, us r = []) (A : List Sym) :
    Eval [] (mergeBLoop W ord r0) ⟨(lBState rests S us A (.inl (.inr r0))).head?, lBState rests S us A⟩
      ⟨(lBState rests S us A (.inl (.inr r0))).head?, lBState rests S us A⟩ 1 := by
  have htest : isRecR (lBState rests S us A (.inl (.inr r0))).head? = false := by
    simp only [lBState, hus, arrSyms_nil, List.nil_append]
    exact isRecR_of_blkTerm (hrests r0)
  exact Eval.loop_false htest

/-- **The block merge loop** (`s ≥ 1`). From `lBState us A` with all streams of `g` rows, the loop
empties all role stacks onto `Z` in merge order, within `26·(total volume) + (11·W + 3)·g + 1`. -/
theorem mergeB_loop (hs : 0 < s) (r0 : Fin W) (hrests : ∀ r, BlkTerm (rests r)) (r1 : List Sym)
    (hr1 : TermOK r1) (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1) (g : ℕ) :
    ∀ (us : Fin W → List (List Bool)) (A : List Sym), (∀ r, (us r).length = g * s) →
      ∃ x' t, Eval [] (mergeBLoop W ord r0)
          ⟨(lBState rests S us A (.inl (.inr r0))).head?, lBState rests S us A⟩
          ⟨x', lBState rests S (fun _ => []) ((arrSyms (mergeBlocks W ord g s us)).reverse ++ A)⟩ t ∧
        t ≤ 26 * ∑ r, vol (us r) + (11 * W + 3) * g + 1 := by
  induction g with
  | zero =>
    intro us A h
    have hus : ∀ r, us r = [] := fun r => List.eq_nil_of_length_eq_zero (by rw [h r]; simp)
    refine ⟨(lBState rests S us A (.inl (.inr r0))).head?, 1,
      (mergeB_loop_exit ord rests S r0 hrests us hus A).of_eq ?_ rfl, by omega⟩
    have hus' : us = fun _ => [] := funext hus
    subst hus'
    rw [mergeBlocks_zero, arrSyms_nil, List.reverse_nil, List.nil_append]
  | succ g ih =>
    intro us A h
    have hus : ∀ r, s ≤ (us r).length := fun r => by
      rw [h r, Nat.succ_mul]
      omega
    obtain ⟨⟨x1, S1⟩, t1, e1, ⟨hS1, -⟩, ht1⟩ := mergeB_round ord s rests S r1 hr1 hcnt us hus A
      ⟨(lBState rests S us A (.inl (.inr r0))).head?, lBState rests S us A⟩ rfl
    simp only at hS1
    subst hS1
    have hd : ∀ r, ((us r).drop s).length = g * s := fun r => by
      rw [List.length_drop, h r, Nat.succ_mul, Nat.add_sub_cancel]
    obtain ⟨x', t2, e2, ht2⟩ := ih (fun r => (us r).drop s)
      ((arrSyms ((List.finRange W).flatMap fun c => (us (ord c)).take s)).reverse ++ A) hd
    have epk := peekR_eval (.inl (.inr r0) : MBLoc W) x1 (lBState rests S (fun r => (us r).drop s)
      ((arrSyms ((List.finRange W).flatMap fun c => (us (ord c)).take s)).reverse ++ A))
    have htest : isRecR (lBState rests S us A (.inl (.inr r0))).head? = true := by
      have hne : us r0 ≠ [] := fun h0 => by
        have := hus r0
        rw [h0] at this
        simp at this
        omega
      obtain ⟨p, u', hpu⟩ := List.exists_cons_of_ne_nil hne
      simp only [lBState, hpu]
      exact isRecR_head_cons _ _ _
    refine ⟨x', t1 + 1 + t2 + 1, (Eval.loop_true htest (Eval.seq e1 epk) e2).of_eq ?_ rfl, ?_⟩
    · rw [mergeBlocks_succ, arrSyms_append, List.reverse_append, List.append_assoc]
    · have hsum : ∑ r, vol (us r) = ∑ r, vol ((us r).take s) + ∑ r, vol ((us r).drop s) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun r _ => (vol_take_add_drop s (us r)).symm)
      have hmul : (11 * W + 3) * (g + 1) = (11 * W + 3) * g + (11 * W + 3) := Nat.mul_succ _ _
      rw [hsum, hmul]
      omega

/-- **The block merge program (`W ≥ 1`) meets the K2b-blk contract**, constant `43`. -/
theorem mergeB_main (hW : 0 < W) (g : ℕ) (us : Fin W → List (List Bool))
    (hlen : ∀ r, (us r).length = g * s) (hrests : ∀ r, BlkTerm (rests r)) (r1 : List Sym)
    (hr1 : TermOK r1) (hS : ∀ r, S (.inl (.inr r)) = arrSyms (us r) ++ rests r)
    (hcnt : S (.inl (.inl 1)) = natSyms s ++ r1) :
    Runs (mergeBProg W ord ⟨0, hW⟩) S (mergeBlkPost ord g s us rests S) (fun _ => True)
      (43 * (∑ r, vol (us r) + 1)) := by
  set A0 : List Sym := Sym.mark :: S (.inr (.inl ())) with hA0
  -- phase 1: the marker on `Z`
  have h1 : Runs (pushC (K := MBLoc W) (.inr (.inl ())) .mark) S (lBState rests S us A0)
      (fun _ => True) 1 := by
    apply Runs.of_eval
    intro x
    refine ⟨x, 1, (pushC_eval _ _ x S).of_eq ?_ rfl, trivial, le_rfl⟩
    congr 1
    funext key
    rcases key with ((i | r) | (⟨⟩ | j))
    · simp [lBState]
    · simp [lBState, hS]
    · simp [lBState, hA0]
    · simp [lBState]
  -- phase 3: rewind `Z` onto the destination
  have h3 : Runs (rewindTo (K := MBLoc W) (.inr (.inl ())) (.inl (.inl 0)) .mark)
      (lBState rests S (fun _ => []) ((arrSyms (mergeBlocks W ord g s us)).reverse ++ A0))
      (mergeBlkPost ord g s us rests S) (fun _ => True)
      (3 * vol (mergeBlocks W ord g s us) + 2) := by
    apply Runs.of_eval
    intro x
    have e := rewindTo_eval (src := (.inr (.inl ()) : MBLoc W)) (dst := .inl (.inl 0)) (by simp)
      .mark x ((arrSyms (mergeBlocks W ord g s us)).reverse) (S (.inr (.inl ())))
      (lBState rests S (fun _ => []) ((arrSyms (mergeBlocks W ord g s us)).reverse ++ A0))
      (mark_not_mem_reverse_arrSyms _) rfl
    refine ⟨some Sym.mark, _, e.of_eq ?_ rfl, trivial, by simp [vol]⟩
    congr 1
    funext key
    rcases key with ((i | r) | (⟨⟩ | j))
    · by_cases hi : i = 0
      · subst hi
        simp [lBState, mergeBlkPost]
      · simp [lBState, mergeBlkPost, hi]
    · simp [lBState, mergeBlkPost, arrSyms_nil]
    · simp [lBState, mergeBlkPost]
    · simp [lBState, mergeBlkPost]
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · -- `s = 0`: all streams are empty
    subst hs0
    have hus : ∀ r, us r = [] := fun r => List.eq_nil_of_length_eq_zero (by rw [hlen r]; simp)
    have h2 : Runs (.seq (peekR (.inl (.inr ⟨0, hW⟩))) (mergeBLoop W ord ⟨0, hW⟩))
        (lBState rests S us A0)
        (lBState rests S (fun _ => []) ((arrSyms (mergeBlocks W ord g 0 us)).reverse ++ A0))
        (fun _ => True) 2 := by
      apply Runs.of_eval
      intro x
      refine ⟨(lBState rests S us A0 (.inl (.inr ⟨0, hW⟩))).head?, 1 + 1,
        Eval.seq (peekR_eval _ x _)
          ((mergeB_loop_exit ord rests S ⟨0, hW⟩ hrests us hus A0).of_eq ?_ rfl), trivial, le_rfl⟩
      have hus' : us = fun _ => [] := funext hus
      subst hus'
      rw [mergeBlocks_s_zero, arrSyms_nil, List.reverse_nil, List.nil_append]
    have h := runs_seq h1 (runs_seq h2 h3)
    refine runs_mono h (fun _ _ => trivial) ?_
    rw [mergeBlocks_s_zero, vol_nil]
    omega
  · -- `s ≥ 1`
    have h2 : Runs (.seq (peekR (.inl (.inr ⟨0, hW⟩))) (mergeBLoop W ord ⟨0, hW⟩))
        (lBState rests S us A0)
        (lBState rests S (fun _ => []) ((arrSyms (mergeBlocks W ord g s us)).reverse ++ A0))
        (fun _ => True) (26 * ∑ r, vol (us r) + (11 * W + 3) * g + 2) := by
      apply Runs.of_eval
      intro x
      obtain ⟨x', t, e, ht⟩ := mergeB_loop ord s rests S hs ⟨0, hW⟩ hrests r1 hr1 hcnt g us A0 hlen
      exact ⟨x', 1 + t, Eval.seq (peekR_eval _ x _) e, trivial, by omega⟩
    have h := runs_seq h1 (runs_seq h2 h3)
    refine runs_mono h (fun _ _ => trivial) ?_
    rw [vol_mergeBlocks ord s g us hlen]
    -- `W·g ≤ V`: every stream holds `g·s ≥ g` records
    have hWg : W * g ≤ ∑ r, vol (us r) := by
      have hle : ∀ r ∈ (Finset.univ : Finset (Fin W)), g ≤ vol (us r) := fun r _ => by
        have h1' := length_le_vol (us r)
        rw [hlen r] at h1'
        have : g ≤ g * s := Nat.le_mul_of_pos_right g hs
        omega
      have := Finset.sum_le_sum hle
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
      exact this
    have hg : (11 * W + 3) * g ≤ 14 * (W * g) := by
      have : 3 * g ≤ 3 * (W * g) := Nat.mul_le_mul_left 3 (Nat.le_mul_of_pos_left g hW)
      nlinarith
    omega

end MergeB

end SubNLogN.Machine.K2

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2

/-- **[PROVED] K2a-blk, cyclic distribution of block rows into `W` role streams**
(`K2DistributeBlkStmt W`, `Contracts/Streams.lean`; paper: Fact 3.3(3) (`fact:oai-streams`),
Lemma A.4(4) (`lem:transfer-streams`)). No hypotheses beyond the contract's own. Scratch `E = Fin W ⊕ Fin 2` (one collector
per role, plus the counter copy `T` and a temporary), registers `Option Sym`, cost constant
`C = 16·W + 30` (depends on the fixed `W`, as the contract permits). For `W ≥ 1` the program is
`distBProg W`; for `W = 0` there are no role stacks and `dropArr` only consumes the source. -/
theorem k2DistributeBlk_holds (W : ℕ) : K2DistributeBlkStmt W := by
  refine ⟨16 * W + 30, fun _ => ⟨Fin W ⊕ Fin 2, inferInstance, inferInstance, Option Sym,
    if W = 0 then dropArr (.inl (.inl 0)) else distBProg W, inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · split_ifs
    · exact closed_dropArr _
    · exact closed_distBProg W
  · intro R s v rest r1 S hR hrest hr1 hS hcnt
    split_ifs with hW
    · subst hW
      apply Runs.of_eval
      intro x
      refine ⟨rest.head?, 3 * vol v + 2, (dropArr_eval x v rest S hrest hS).of_eq ?_ rfl, trivial,
        by omega⟩
      congr 1
      funext key
      rcases key with ((i | w) | e)
      · by_cases hi : i = 0
        · subst hi
          simp [distBlkPost]
        · simp [distBlkPost, hi]
      · exact w.elim0
      · simp [distBlkPost]
    · exact distB_main s v rest S (Nat.pos_of_ne_zero hW) R hR hrest r1 hr1 hS hcnt

/-- **[PROVED] K2b-blk, merge of `W` streams of block rows in the fixed class order `ord`**
(`K2MergeBlkStmt W ord`, `Contracts/Streams.lean`; paper: Fact 3.3(3) (`fact:oai-streams`),
Lemma A.4(4) (`lem:transfer-streams`)). No hypotheses beyond the contract's own. For `W ≥ 1`: scratch
`E = Unit ⊕ Fin 2` (`Z`, the counter copy `T`, a temporary), registers `Option Sym`, program
`mergeBProg W ord ⟨0, _⟩`, cost constant `C = 43` (independent of `W`). For `W = 0` the merge is
empty: `skip`, `C = 1`. -/
theorem k2MergeBlk_holds (W : ℕ) (ord : Equiv.Perm (Fin W)) : K2MergeBlkStmt W ord := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    refine ⟨1, fun _ => ⟨Unit ⊕ Fin 2, inferInstance, inferInstance, Option Sym, skip,
      inferInstance, ⟨none⟩, ?_, ?_⟩⟩
    · simp [Prog.Closed, Prog.FreeBelow, skip]
    · intro g s us rests r1 S _ _ _ _ _
      apply Runs.of_eval
      intro x
      refine ⟨x, 1, (skip_eval [] _).of_eq ?_ rfl, trivial, by simp⟩
      congr 1
      funext key
      rcases key with ((i | w) | e)
      · have hnil : ∀ l : List ℕ, l.flatMap (fun _ => ([] : List (List Bool))) = [] :=
          fun l => List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
        by_cases hi : i = 0
        · subst hi
          simp [mergeBlkPost, mergeBlocks, hnil, arrSyms_nil]
        · simp [mergeBlkPost, hi]
      · exact w.elim0
      · simp [mergeBlkPost]
  · refine ⟨43, fun _ => ⟨Unit ⊕ Fin 2, inferInstance, inferInstance, Option Sym,
      mergeBProg W ord ⟨0, hW⟩, inferInstance, ⟨none⟩, closed_mergeBProg W ord _, ?_⟩⟩
    intro g s us rests r1 S hlen hrests hr1 hS hcnt
    rw [sum_finRange]
    exact mergeB_main ord s rests S hW g us hlen hrests r1 hr1 hS hcnt

end SubNLogN.Machine
