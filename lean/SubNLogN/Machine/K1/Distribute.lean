/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DistributeCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# K1-dist (`K1/Distribute.lean`): proofs of `K2DistributeStmt W` and `K2MergeStmt W ord`

**Scope (honest summary).** Fully proved (no placeholders), no extra hypotheses:
* `SubNLogN.Machine.k2Distribute_holds (W : ℕ) : K2DistributeStmt W`,
* `SubNLogN.Machine.k2Merge_holds (W : ℕ) (ord : Equiv.Perm (Fin W)) : K2MergeStmt W ord`.

Paper: Fact 3.3(3) (`fact:oai-streams`) and Lemma A.4(4) (`lem:transfer-streams`,
cyclic row distribution among `W` streams: "send row `r` to stream `r mod W`; each stream
keeps the row order, and a merge reads the streams in the prescribed order of row classes").
The contract statements are `K2DistributeStmt` and `K2MergeStmt` in
`SubNLogN/Machine/Contracts/Streams.lean`.

**Cost constants (what is proved).** As the contracts allow, the constants depend on the fixed
compile-time data:
* distribution: `C = 6·W + 9`. An additive `Θ(W)` is unavoidable for this program shape (it touches
  every role stack), so `C ≥ W` is forced by the `C·(V+1)` form; our internal round accounting is
  coarse (`O(W)` per round, rounds `≤` rows), which still fits `C = O(W)`;
* merge: `C = 9` for `W ≥ 1` (every round moves `W` records, so the per-round `O(W)` is absorbed),
  `C = 1` for `W = 0`.

## Program design
Records move with W4's `moveRec` (`Contracts/Machine/W4.lean`), which pushes a record reversed.
A whole stack of reversed records is moved back in one pass with `WP.W9comp.rewindTo` (symbol by
symbol down to a `mark`, which is dropped), restoring the record orientation and the row order.

**Distribution** (stacks `KLoc (Option (Fin W)) (Fin W)`: named `none` = source, `some k` = role
stack `k`; private scratch `.inr k` collects class `k`):
1. `distMarks`: push a `mark` on every scratch stack `k` (`forEachFin W`).
2. `distLoop`: while the source has a record: one *round* `forEachFin W (k ↦ gmove src (.inr k))`
   (guarded move of the next row onto scratch `k`). Round `j` deals rows `jW, …, jW + W - 1`, and row
   `jW + k` has class `k`; a partial last round moves fewer rows (guards fail on the `BlkTerm` rest).
   Invariant (`dState m`, `m` = rows dealt): source = rows `m, m+1, …`; scratch `k` =
   `(arrSyms (roleRows W k (v.take m))).reverse ++ mark :: old`.
3. `distBack`: for each `k`, `rewindTo (.inr k) (some k) mark`: role stack `k` receives
   `arrSyms (roleRows W k v)` on its old content and scratch `k` is restored.
For `W = 0` there are no role stacks and the contract just consumes the source: `dropArr`.

**Merge** (stacks `KLoc (Option (Fin W)) Unit`: `none` = destination, `some r` = role stacks,
scratch `.inr ()` = `Z`), for `W ≥ 1`:
1. push `mark` on `Z`;
2. loop while role stack `0` has a record (all streams have the same length `g`): one round
   `forEachFin W (c ↦ moveRec (some (ord c)) Z)`, i.e. the round-`t` rows of the classes
   `ord 0, …, ord (W-1)` in this order. Invariant (`lState us A`): role `r` holds the remaining
   rows `us r`, `Z` holds `A`; `rState` is the state inside a round.
3. `rewindTo Z none mark`: the destination receives `arrSyms (mergeRows W ord g us)`.
For `W = 0` the merge is empty and the program is `skip`.

Cost accounting: `gmove` costs `3·|p| + 5` on a record and `3` otherwise; `moveRec` `3·|p| + 3`;
`rewindTo` `3·|L| + 2`; loop tests and peeks `1`. See `dist_loop`, `merge_loop`.
-/

namespace SubNLogN.Machine.K2

open TMFw TMFw.Contracts TMFw.Lib WP.W9comp

/-! ## K2a: distribution -/

/-- Stacks of the distribution kernel: named `Option (Fin W)` (`none` = source, `some k` = role
stack `k`) and the private scratch family `Fin W` (scratch `k` collects the rows of class `k`). -/
abbrev DLoc (W : ℕ) : Type := KLoc (Option (Fin W)) (Fin W)

/-- Phase 1: a `mark` on every scratch stack. -/
def distMarks (W : ℕ) : SProg (DLoc W) := forEachFin W fun k => pushC (.inr k) .mark

/-- One round: deal the next (up to) `W` rows, row `k` of the round onto scratch `k`. -/
def distRound (W : ℕ) : SProg (DLoc W) := forEachFin W fun k => gmove (.inl none) (.inr k)

/-- Phase 2: rounds while the source has a record (the register holds the peeked source top). -/
def distLoop (W : ℕ) : SProg (DLoc W) := .loop isRecR (.seq (distRound W) (peekR (.inl none)))

/-- Phase 3: move each class back from its scratch stack onto its role stack. -/
def distBack (W : ℕ) : SProg (DLoc W) :=
  forEachFin W fun k => rewindTo (.inr k) (.inl (some k)) .mark

/-- The distribution program (`W ≥ 1`). -/
def distProg (W : ℕ) : SProg (DLoc W) :=
  .seq (distMarks W) (.seq (.seq (peekR (.inl none)) (distLoop W)) (distBack W))

theorem closed_distProg (W : ℕ) : (distProg W).Closed := by
  have h1 := closed_forEachFin W (fun k => pushC (K := DLoc W) (.inr k) .mark)
    (fun _ => by simp [Prog.Closed, Prog.FreeBelow, pushC])
  have h2 := closed_forEachFin W (fun k => gmove (K := DLoc W) (.inl none) (.inr k))
    (fun _ => closed_gmove _ _)
  have h3 := closed_forEachFin W (fun k => rewindTo (K := DLoc W) (.inr k) (.inl (some k)) .mark)
    (fun _ => by simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR])
  have hp : (peekR (K := DLoc W) (.inl none)).Closed := by simp [Prog.Closed, Prog.FreeBelow, peekR]
  exact ⟨h1, ⟨⟨hp, ⟨h2, hp⟩⟩, h3⟩⟩

section Dist

variable {W : ℕ} (v : List (List Bool)) (rest : List Sym) (S : DLoc W → List Sym)

/-- **Invariant of the dealing phase** after `m` rows were dealt: the source holds rows
`m, m + 1, …` on `rest`; scratch stack `k` holds, above its `mark`, the class-`k` rows among the
first `m`, reversed (last on top); the role stacks are untouched. -/
def dState (m : ℕ) : DLoc W → List Sym
  | .inl none => arrSyms (v.drop m) ++ rest
  | .inl (some r) => S (.inl (some r))
  | .inr k => (arrSyms (roleRows W k.val (v.take m))).reverse ++ Sym.mark :: S (.inr k)

theorem dState_of_le {m : ℕ} (h : v.length ≤ m) :
    dState v rest S m = dState v rest S v.length := by
  funext key
  rcases key with (_ | r) | k
  · simp [dState, List.drop_eq_nil_of_le h]
  · rfl
  · simp [dState, List.take_of_length_le h]

/-- **One dealing step** (`gmove` of row `m` onto scratch `i`, where `m % W = i`): `dState m` to
`dState (m + 1)`; if the source is exhausted it is a no-op. Cost `3 + 3·(vol of row m)`. -/
theorem dist_step (hrest : BlkTerm rest) (i : Fin W) (m : ℕ) (hm : m % W = i.val) :
    Runs (gmove (K := DLoc W) (.inl none) (.inr i)) (dState v rest S m)
      (dState v rest S (m + 1)) (fun _ => True)
      (3 + (3 * vol (v.drop m) - 3 * vol (v.drop (m + 1)))) := by
  apply Runs.of_eval
  intro x
  by_cases hlt : m < v.length
  · have hd := List.drop_eq_getElem_cons hlt
    have hS : dState v rest S m (.inl none) = recSyms v[m] ++ (arrSyms (v.drop (m + 1)) ++ rest) := by
      simp only [dState, hd, arrSyms_cons, List.append_assoc]
    have e := gmove_eval_rec (src := (.inl none : DLoc W)) (dst := .inr i) (by simp) x v[m] _ _ hS
    refine ⟨some Sym.sep, _, e.of_eq ?_ rfl, trivial, ?_⟩
    · congr 1
      funext key
      rcases key with (_ | r) | k
      · simp [dState]
      · simp [dState]
      · by_cases hk : k = i
        · subst hk
          have hr : roleRows W k.val (v.take (m + 1)) = roleRows W k.val (v.take m) ++ [v[m]] := by
            rw [roleRows_take_succ, if_pos hm, List.getElem?_eq_getElem hlt]
            rfl
          simp only [Function.update_self, dState, hr, arrSyms_append, arrSyms_singleton,
            List.reverse_append, List.append_assoc]
        · have hk' : ¬ m % W = k.val := by
            rw [hm]
            exact fun h => hk (Fin.ext h.symm)
          have hr : roleRows W k.val (v.take (m + 1)) = roleRows W k.val (v.take m) := by
            rw [roleRows_take_succ, if_neg hk', List.append_nil]
          rw [Function.update_of_ne (by simpa using hk), Function.update_of_ne (by simp)]
          simp only [dState, hr]
    · rw [vol_drop_eq_of_lt v hlt]
      omega
  · have hd : v.drop m = [] := List.drop_eq_nil_of_le (by omega)
    have htest : isRecR ((dState v rest S m) (.inl none)).head? = false := by
      simp only [dState, hd, arrSyms_nil, List.nil_append]
      exact isRecR_of_blkTerm hrest
    refine ⟨(dState v rest S m (.inl none)).head?, 3, (gmove_eval_skip x _ htest).of_eq ?_ rfl,
      trivial, by omega⟩
    rw [dState_of_le v rest S (by omega : v.length ≤ m),
      dState_of_le v rest S (by omega : v.length ≤ m + 1)]

/-- **One round** from a multiple `m0` of `W`: `dState m0` to `dState (m0 + W)`, cost
`3·W + 3·(vol of the dealt rows) + 1`. -/
theorem dist_round (hrest : BlkTerm rest) (m0 : ℕ) (hm0 : m0 % W = 0) :
    Runs (distRound W) (dState v rest S m0) (dState v rest S (m0 + W)) (fun _ => True)
      (W * 3 + (3 * vol (v.drop m0) - 3 * vol (v.drop (m0 + W))) + 1) := by
  have h := runs_forEachFin_pot W (fun k => gmove (K := DLoc W) (.inl none) (.inr k))
    (fun i => dState v rest S (m0 + i)) (fun i => 3 * vol (v.drop (m0 + i))) 3
    (fun i => by
      have := vol_drop_anti v (show m0 + i ≤ m0 + (i + 1) by omega)
      omega)
    (fun i => by
      have hm : (m0 + i.val) % W = i.val := by
        rw [Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
      exact dist_step v rest S hrest i (m0 + i.val) hm)
  exact h

/-- The dealing loop stops when the source is exhausted (one failing test). -/
theorem dist_loop_exit (hrest : BlkTerm rest) (m : ℕ) (hm : v.length ≤ m) :
    Eval [] (distLoop W) ⟨(dState v rest S m (.inl none)).head?, dState v rest S m⟩
      ⟨(dState v rest S m (.inl none)).head?, dState v rest S v.length⟩ 1 := by
  have hd : v.drop m = [] := List.drop_eq_nil_of_le hm
  have htest : isRecR (dState v rest S m (.inl none)).head? = false := by
    simp only [dState, hd, arrSyms_nil, List.nil_append]
    exact isRecR_of_blkTerm hrest
  refine (Eval.loop_false htest).of_eq ?_ rfl
  rw [dState_of_le v rest S hm]

/-- **The dealing loop.** From a multiple `m` of `W` (register = peeked source top), the loop
reaches `dState v.length` (all rows dealt) within `(3·W + 6)·(rows left) + 3·(volume left) + 1`.
Induction on an upper bound `d` of the number of rows left. -/
theorem dist_loop (hW : 0 < W) (hrest : BlkTerm rest) :
    ∀ (d m : ℕ), v.length - m ≤ d → m % W = 0 →
      ∃ x' t, Eval [] (distLoop W) ⟨(dState v rest S m (.inl none)).head?, dState v rest S m⟩
          ⟨x', dState v rest S v.length⟩ t ∧
        t ≤ (3 * W + 6) * (v.length - m) + 3 * vol (v.drop m) + 1 := by
  intro d
  induction d with
  | zero =>
    intro m hd _
    exact ⟨_, 1, dist_loop_exit v rest S hrest m (by omega), by omega⟩
  | succ d ih =>
    intro m hd hm
    by_cases hlt : m < v.length
    · obtain ⟨⟨x1, S1⟩, t1, e1, ⟨hS1, -⟩, ht1⟩ :=
        dist_round v rest S hrest m hm ⟨(dState v rest S m (.inl none)).head?, dState v rest S m⟩ rfl
      simp only at hS1
      subst hS1
      have hm' : (m + W) % W = 0 := by
        rw [Nat.add_mod_right]
        exact hm
      obtain ⟨x', t2, e2, ht2⟩ := ih (m + W) (by omega) hm'
      have epk := peekR_eval (.inl none : DLoc W) x1 (dState v rest S (m + W))
      have htest : isRecR (dState v rest S m (.inl none)).head? = true := by
        simp only [dState, List.drop_eq_getElem_cons hlt]
        exact isRecR_head_cons _ _ _
      refine ⟨x', t1 + 1 + t2 + 1, Eval.loop_true htest (Eval.seq e1 epk) e2, ?_⟩
      have hvol := vol_drop_anti v (show m ≤ m + W by omega)
      have hK : (3 * W + 6) * (v.length - (m + W)) + (3 * W + 6) ≤
          (3 * W + 6) * (v.length - m) := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    · exact ⟨_, 1, dist_loop_exit v rest S hrest m (by omega), by omega⟩

/-- Intermediate states of the marker phase (`mark` pushed on the scratch stacks `k < i`). -/
def markState (i : ℕ) : DLoc W → List Sym
  | .inl x => S (.inl x)
  | .inr k => if k.val < i then Sym.mark :: S (.inr k) else S (.inr k)

/-- **Phase 1** (markers): `S` to `dState 0`, cost `W + 1`. -/
theorem dist_marks (hS : S (.inl none) = arrSyms v ++ rest) :
    Runs (distMarks W) S (dState v rest S 0) (fun _ => True) (W + 1) := by
  have h := runs_forEachFin W (fun k => pushC (K := DLoc W) (.inr k) .mark) (fun _ => 1)
    (markState S) (fun i => by
      apply Runs.of_eval
      intro x
      refine ⟨x, 1, (pushC_eval _ _ x _).of_eq ?_ rfl, trivial, le_rfl⟩
      congr 1
      funext key
      rcases key with x' | k
      · simp [markState]
      · by_cases hk : k = i
        · subst hk
          simp [markState]
        · have hk' : k.val ≠ i.val := fun h => hk (Fin.ext h)
          rw [Function.update_of_ne (by simpa using hk)]
          by_cases hlt : k.val < i.val
          · simp [markState, hlt, show k.val < i.val + 1 by omega]
          · simp [markState, hlt, show ¬ k.val < i.val + 1 by omega])
  have h0 : markState S 0 = S := by
    funext key
    rcases key with x | k <;> simp [markState]
  have hW : markState S W = dState v rest S 0 := by
    funext key
    rcases key with (_ | r) | k
    · simp [markState, dState, hS]
    · simp [markState, dState]
    · simp [markState, dState, roleRows_nil, arrSyms_nil]
  rw [h0, hW] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  simp

/-- Intermediate states of the move-back phase (classes `k < i` already on their role stacks). -/
def backState (i : ℕ) : DLoc W → List Sym
  | .inl none => rest
  | .inl (some r) =>
    if r.val < i then arrSyms (roleRows W r.val v) ++ S (.inl (some r)) else S (.inl (some r))
  | .inr k =>
    if k.val < i then S (.inr k)
    else (arrSyms (roleRows W k.val v)).reverse ++ Sym.mark :: S (.inr k)

/-- **Phase 3** (move back): `dState v.length` to `distPost v rest S`. Each `rewindTo` costs
`3·(vol of class k) + 2`; coarsely, `vol (roleRows W k v) ≤ vol v`. -/
theorem dist_back :
    Runs (distBack W) (dState v rest S v.length) (distPost v rest S) (fun _ => True)
      (W * (3 * vol v + 2) + 1) := by
  have h := runs_forEachFin W (fun k => rewindTo (K := DLoc W) (.inr k) (.inl (some k)) .mark)
    (fun k => 3 * vol (roleRows W k.val v) + 2) (backState v rest S) (fun i => by
      apply Runs.of_eval
      intro x
      have hsrc : backState v rest S i (.inr i) =
          (arrSyms (roleRows W i.val v)).reverse ++ Sym.mark :: S (.inr i) := by
        simp [backState]
      have e := rewindTo_eval (src := (.inr i : DLoc W)) (dst := .inl (some i)) (by simp) .mark x
        _ _ _ (mark_not_mem_reverse_arrSyms _) hsrc
      refine ⟨some Sym.mark, _, e.of_eq ?_ rfl, trivial, by simp [vol]⟩
      congr 1
      funext key
      rcases key with (_ | r) | k
      · simp [backState]
      · by_cases hr : r = i
        · subst hr
          simp [backState]
        · have hr' : r.val ≠ i.val := fun h => hr (Fin.ext h)
          rw [Function.update_of_ne (by simpa using hr), Function.update_of_ne (by simp)]
          by_cases hlt : r.val < i.val
          · simp [backState, hlt, show r.val < i.val + 1 by omega]
          · simp [backState, hlt, show ¬ r.val < i.val + 1 by omega]
      · by_cases hk : k = i
        · subst hk
          simp [backState]
        · have hk' : k.val ≠ i.val := fun h => hk (Fin.ext h)
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simpa using hk)]
          by_cases hlt : k.val < i.val
          · simp [backState, hlt, show k.val < i.val + 1 by omega]
          · simp [backState, hlt, show ¬ k.val < i.val + 1 by omega])
  have h0 : backState v rest S 0 = dState v rest S v.length := by
    funext key
    rcases key with (_ | r) | k <;> simp [backState, dState, arrSyms_nil]
  have hW : backState v rest S W = distPost v rest S := by
    funext key
    rcases key with (_ | r) | k <;> simp [backState, distPost]
  rw [h0, hW] at h
  refine runs_mono h (fun _ _ => trivial) ?_
  have hle : ((List.finRange W).map fun k : Fin W => 3 * vol (roleRows W k.val v) + 2).sum ≤
      ((List.finRange W).map fun _ : Fin W => 3 * vol v + 2).sum :=
    List.sum_le_sum (fun k _ => by have := vol_roleRows_le W k.val v; omega)
  simp only [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul] at hle
  omega

/-- **The distribution program (`W ≥ 1`) meets the K2a contract**, constant `6·W + 9`. -/
theorem dist_main (hW : 0 < W) (hrest : BlkTerm rest) (hS : S (.inl none) = arrSyms v ++ rest) :
    Runs (distProg W) S (distPost v rest S) (fun _ => True) ((6 * W + 9) * (vol v + 1)) := by
  have h1 := dist_marks v rest S hS
  have h2 : Runs (.seq (peekR (.inl none)) (distLoop W)) (dState v rest S 0)
      (dState v rest S v.length) (fun _ => True) ((3 * W + 6) * v.length + 3 * vol v + 2) := by
    apply Runs.of_eval
    intro x
    obtain ⟨x', t, e, ht⟩ := dist_loop v rest S hW hrest v.length 0 (by omega) (Nat.zero_mod W)
    refine ⟨x', 1 + t, Eval.seq (peekR_eval _ x _) e, trivial, ?_⟩
    simp only [Nat.sub_zero, List.drop_zero] at ht
    omega
  have h := runs_seq h1 (runs_seq h2 (dist_back v rest S))
  refine runs_mono h (fun _ _ => trivial) ?_
  have hn := length_le_vol v
  have h3 : (3 * W + 6) * v.length ≤ (3 * W + 6) * vol v := Nat.mul_le_mul_left _ hn
  nlinarith

end Dist

/-! ## K2b: merge -/

/-- Stacks of the merge kernel: named `Option (Fin W)` (`none` = destination, `some r` = role
stack `r`) and one private scratch stack `Z = .inr ()`. -/
abbrev MLoc (W : ℕ) : Type := KLoc (Option (Fin W)) Unit

/-- One round: move the next record of each of the role stacks `ord 0, …, ord (W - 1)` (in this
order) onto `Z`. -/
def mergeRound (W : ℕ) (ord : Equiv.Perm (Fin W)) : SProg (MLoc W) :=
  forEachFin W fun c => moveRec (.inl (some (ord c))) (.inr ())

/-- Rounds while role stack `r0` has a record (the register holds its peeked top). -/
def mergeLoop (W : ℕ) (ord : Equiv.Perm (Fin W)) (r0 : Fin W) : SProg (MLoc W) :=
  .loop isRecR (.seq (mergeRound W ord) (peekR (.inl (some r0))))

/-- The merge program (`W ≥ 1`; `r0` is the role stack tested by the loop). -/
def mergeProg (W : ℕ) (ord : Equiv.Perm (Fin W)) (r0 : Fin W) : SProg (MLoc W) :=
  .seq (pushC (.inr ()) .mark)
    (.seq (.seq (peekR (.inl (some r0))) (mergeLoop W ord r0)) (rewindTo (.inr ()) (.inl none) .mark))

theorem closed_mergeProg (W : ℕ) (ord : Equiv.Perm (Fin W)) (r0 : Fin W) :
    (mergeProg W ord r0).Closed := by
  have h2 := closed_forEachFin W (fun c => moveRec (K := MLoc W) (.inl (some (ord c))) (.inr ()))
    (fun _ => by simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, pushR, popR])
  have hp : (peekR (K := MLoc W) (.inl (some r0))).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, peekR]
  have hm : (pushC (K := MLoc W) (.inr ()) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hr : (rewindTo (K := MLoc W) (.inr ()) (.inl none) .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR]
  exact ⟨hm, ⟨⟨hp, ⟨h2, hp⟩⟩, hr⟩⟩

section Merge

variable {W : ℕ} (ord : Equiv.Perm (Fin W)) (rests : Fin W → List Sym) (S : MLoc W → List Sym)

/-- **Loop invariant of the merge**: role stack `r` holds the remaining rows `us r` on `rests r`,
`Z` holds `A`, and the destination is untouched. -/
def lState (us : Fin W → List (List Bool)) (A : List Sym) : MLoc W → List Sym
  | .inl none => S (.inl none)
  | .inl (some r) => arrSyms (us r) ++ rests r
  | .inr _ => A

/-- **Round invariant** after the first `i` moves of a round with heads `a` and tails `b`: the
classes `ord 0, …, ord (i - 1)` have lost their heads, which sit (reversed, in this order) on `Z`
above `A`. -/
def rState (a : Fin W → List Bool) (b : Fin W → List (List Bool)) (A : List Sym) (i : ℕ) :
    MLoc W → List Sym
  | .inl none => S (.inl none)
  | .inl (some r) =>
    if (ord.symm r).val < i then arrSyms (b r) ++ rests r else arrSyms (a r :: b r) ++ rests r
  | .inr _ => (arrSyms (((List.finRange W).take i).map fun c => a (ord c))).reverse ++ A

/-- **One merge move**: the head of class `ord c` moves onto `Z`; cost `3·|head| + 3`. -/
theorem merge_step (a : Fin W → List Bool) (b : Fin W → List (List Bool)) (A : List Sym)
    (c : Fin W) :
    Runs (moveRec (K := MLoc W) (.inl (some (ord c))) (.inr ())) (rState ord rests S a b A c.val)
      (rState ord rests S a b A (c.val + 1)) (fun _ => True) (3 * (a (ord c)).length + 3) := by
  apply Runs.of_eval
  intro x
  have hS : rState ord rests S a b A c.val (.inl (some (ord c))) =
      (a (ord c)).map Sym.bit ++ Sym.sep :: (arrSyms (b (ord c)) ++ rests (ord c)) := by
    simp [rState, arrSyms_cons, recSyms]
  have e := moveRec_eval (src := (.inl (some (ord c)) : MLoc W)) (dst := .inr ()) (by simp) x _ _
    _ (bits_data _) hS
  refine ⟨some Sym.sep, _, e.of_eq ?_ rfl, trivial, by simp⟩
  congr 1
  funext key
  rcases key with (_ | r) | ⟨⟩
  · simp [rState]
  · by_cases hr : r = ord c
    · subst hr
      simp [rState]
    · have hr' : (ord.symm r).val ≠ c.val := fun h => hr (by rw [← Fin.ext h]; simp)
      rw [Function.update_of_ne (by simp), Function.update_of_ne (by simpa using hr)]
      by_cases hlt : (ord.symm r).val < c.val
      · simp [rState, hlt, show (ord.symm r).val < c.val + 1 by omega]
      · simp [rState, hlt, show ¬ (ord.symm r).val < c.val + 1 by omega]
  · have ht : (List.finRange W).take (c.val + 1) = (List.finRange W).take c.val ++ [c] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp), List.getElem_finRange]
      rfl
    simp only [Function.update_self, rState, ht, List.map_append, List.map_cons, List.map_nil,
      arrSyms_append, arrSyms_singleton, List.reverse_append, reverse_recSyms, List.append_assoc,
      List.cons_append]

/-- **One merge round**: `lState (a :: b) A` to `lState b (heads reversed ++ A)`. -/
theorem merge_round (a : Fin W → List Bool) (b : Fin W → List (List Bool)) (A : List Sym) :
    Runs (mergeRound W ord) (lState rests S (fun r => a r :: b r) A)
      (lState rests S b ((arrSyms ((List.finRange W).map fun c => a (ord c))).reverse ++ A))
      (fun _ => True) (3 * ∑ r, ((a r).length + 1) + 1) := by
  have h := runs_forEachFin W (fun c => moveRec (K := MLoc W) (.inl (some (ord c))) (.inr ()))
    (fun c => 3 * (a (ord c)).length + 3) (rState ord rests S a b A)
    (fun c => merge_step ord rests S a b A c)
  have h0 : rState ord rests S a b A 0 = lState rests S (fun r => a r :: b r) A := by
    funext key
    rcases key with (_ | r) | ⟨⟩ <;> simp [rState, lState, arrSyms_nil]
  have hW : rState ord rests S a b A W =
      lState rests S b ((arrSyms ((List.finRange W).map fun c => a (ord c))).reverse ++ A) := by
    funext key
    rcases key with (_ | r) | ⟨⟩ <;> simp [rState, lState, List.take_of_length_le]
  rw [h0, hW] at h
  refine runs_mono h (fun _ _ => trivial) (le_of_eq ?_)
  rw [sum_finRange, show (∑ c : Fin W, (3 * (a (ord c)).length + 3)) =
      ∑ r : Fin W, (3 * (a r).length + 3) from Equiv.sum_comp ord (fun r => 3 * (a r).length + 3),
    Finset.mul_sum]
  exact congrArg (· + 1) (Finset.sum_congr rfl (fun r _ => by ring))

/-- **The merge loop.** From `lState us A` with all streams of length `g` (register = peeked top
of role stack `r0`), the loop empties all role stacks onto `Z` in merge order, within
`3·(total volume) + 3·g + 1`. Induction on `g`. -/
theorem merge_loop (r0 : Fin W) (hrests : ∀ r, BlkTerm (rests r)) (g : ℕ) :
    ∀ (us : Fin W → List (List Bool)) (A : List Sym), (∀ r, (us r).length = g) →
      ∃ x' t, Eval [] (mergeLoop W ord r0)
          ⟨(lState rests S us A (.inl (some r0))).head?, lState rests S us A⟩
          ⟨x', lState rests S (fun _ => []) ((arrSyms (mergeRows W ord g us)).reverse ++ A)⟩ t ∧
        t ≤ 3 * ∑ r, vol (us r) + 3 * g + 1 := by
  induction g with
  | zero =>
    intro us A h
    have hus : us = fun _ => [] := funext fun r => List.eq_nil_of_length_eq_zero (h r)
    subst hus
    have htest : isRecR (lState rests S (fun _ => []) A (.inl (some r0))).head? = false := by
      simp only [lState, arrSyms_nil, List.nil_append]
      exact isRecR_of_blkTerm (hrests r0)
    refine ⟨(lState rests S (fun _ => []) A (.inl (some r0))).head?, 1,
      (Eval.loop_false htest).of_eq ?_ rfl, by omega⟩
    rw [mergeRows_zero, arrSyms_nil, List.reverse_nil, List.nil_append]
  | succ g ih =>
    intro us A h
    obtain ⟨a, b, rfl, hb⟩ := exists_cons_fun us h
    obtain ⟨⟨x1, S1⟩, t1, e1, ⟨hS1, -⟩, ht1⟩ :=
      merge_round ord rests S a b A
        ⟨(lState rests S (fun r => a r :: b r) A (.inl (some r0))).head?,
          lState rests S (fun r => a r :: b r) A⟩ rfl
    simp only at hS1
    subst hS1
    obtain ⟨x', t2, e2, ht2⟩ :=
      ih b ((arrSyms ((List.finRange W).map fun c => a (ord c))).reverse ++ A) hb
    have epk := peekR_eval (.inl (some r0) : MLoc W) x1
      (lState rests S b ((arrSyms ((List.finRange W).map fun c => a (ord c))).reverse ++ A))
    have htest :
        isRecR (lState rests S (fun r => a r :: b r) A (.inl (some r0))).head? = true := by
      simp only [lState]
      exact isRecR_head_cons _ _ _
    refine ⟨x', t1 + 1 + t2 + 1, (Eval.loop_true htest (Eval.seq e1 epk) e2).of_eq ?_ rfl, ?_⟩
    · rw [mergeRows_succ, arrSyms_append, List.reverse_append, List.append_assoc]
    · have hsum : ∑ r, vol (a r :: b r) = ∑ r, ((a r).length + 1) + ∑ r, vol (b r) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun r _ => by rw [vol_cons])
      rw [hsum]
      omega

/-- **The merge program (`W ≥ 1`) meets the K2b contract**, constant `9`. -/
theorem merge_main (hW : 0 < W) (g : ℕ) (us : Fin W → List (List Bool))
    (hlen : ∀ r, (us r).length = g) (hrests : ∀ r, BlkTerm (rests r))
    (hS : ∀ r, S (.inl (some r)) = arrSyms (us r) ++ rests r) :
    Runs (mergeProg W ord ⟨0, hW⟩) S (mergePost ord g us rests S) (fun _ => True)
      (9 * (∑ r, vol (us r) + 1)) := by
  have h1 : Runs (pushC (K := MLoc W) (.inr ()) .mark) S
      (lState rests S us (Sym.mark :: S (.inr ()))) (fun _ => True) 1 := by
    apply Runs.of_eval
    intro x
    refine ⟨x, 1, (pushC_eval _ _ x S).of_eq ?_ rfl, trivial, le_rfl⟩
    congr 1
    funext key
    rcases key with (_ | r) | ⟨⟩
    · simp [lState]
    · simp [lState, hS]
    · simp [lState]
  have h2 : Runs (.seq (peekR (.inl (some ⟨0, hW⟩))) (mergeLoop W ord ⟨0, hW⟩))
      (lState rests S us (Sym.mark :: S (.inr ())))
      (lState rests S (fun _ => [])
        ((arrSyms (mergeRows W ord g us)).reverse ++ Sym.mark :: S (.inr ())))
      (fun _ => True) (3 * ∑ r, vol (us r) + 3 * g + 2) := by
    apply Runs.of_eval
    intro x
    obtain ⟨x', t, e, ht⟩ := merge_loop ord rests S ⟨0, hW⟩ hrests g us _ hlen
    exact ⟨x', 1 + t, Eval.seq (peekR_eval _ x _) e, trivial, by omega⟩
  have h3 : Runs (rewindTo (K := MLoc W) (.inr ()) (.inl none) .mark)
      (lState rests S (fun _ => [])
        ((arrSyms (mergeRows W ord g us)).reverse ++ Sym.mark :: S (.inr ())))
      (mergePost ord g us rests S) (fun _ => True) (3 * vol (mergeRows W ord g us) + 2) := by
    apply Runs.of_eval
    intro x
    have e := rewindTo_eval (src := (.inr () : MLoc W)) (dst := .inl none) (by simp) .mark x
      ((arrSyms (mergeRows W ord g us)).reverse) (S (.inr ()))
      (lState rests S (fun _ => [])
        ((arrSyms (mergeRows W ord g us)).reverse ++ Sym.mark :: S (.inr ())))
      (mark_not_mem_reverse_arrSyms _) rfl
    refine ⟨some Sym.mark, _, e.of_eq ?_ rfl, trivial, by simp [vol]⟩
    congr 1
    funext key
    rcases key with (_ | r) | ⟨⟩
    · simp [lState, mergePost]
    · simp [lState, mergePost, arrSyms_nil]
    · simp [lState, mergePost]
  have h := runs_seq h1 (runs_seq h2 h3)
  refine runs_mono h (fun _ _ => trivial) ?_
  rw [vol_mergeRows ord g us hlen]
  have hg : g ≤ ∑ r, vol (us r) := by
    calc g = (us ⟨0, hW⟩).length := (hlen _).symm
      _ ≤ vol (us ⟨0, hW⟩) := length_le_vol _
      _ ≤ ∑ r, vol (us r) :=
        Finset.single_le_sum (f := fun r => vol (us r)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
  omega

end Merge

end SubNLogN.Machine.K2

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.K2

/-- **[PROVED] K2a, cyclic distribution of rows into `W` role streams** (`K2DistributeStmt W`,
`Contracts/Streams.lean`; paper: Fact 3.3(3) (`fact:oai-streams`), Lemma A.4(4) (`lem:transfer-streams`)).
No hypotheses beyond the contract's own. Scratch `E = Fin W` (one collecting stack per role),
registers `Option Sym`, cost constant `C = 6·W + 9` (depends on the fixed `W`, as the contract
permits). For `W ≥ 1` the program is `distProg W`; for `W = 0` there are no role stacks and the
program `dropArr` only consumes the source. -/
theorem k2Distribute_holds (W : ℕ) : K2DistributeStmt W := by
  refine ⟨6 * W + 9, fun _ => ⟨Fin W, inferInstance, inferInstance, Option Sym,
    if W = 0 then dropArr (.inl none) else distProg W, inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · split_ifs
    · exact closed_dropArr _
    · exact closed_distProg W
  · intro v rest S hrest hS
    split_ifs with hW
    · subst hW
      apply Runs.of_eval
      intro x
      refine ⟨rest.head?, 3 * vol v + 2, (dropArr_eval x v rest S hrest hS).of_eq ?_ rfl, trivial,
        by omega⟩
      congr 1
      funext key
      rcases key with (_ | r) | k
      · simp [distPost]
      · exact r.elim0
      · exact k.elim0
    · exact dist_main v rest S (Nat.pos_of_ne_zero hW) hrest hS

/-- **[PROVED] K2b, merge of `W` role streams in the fixed class order `ord`** (`K2MergeStmt W ord`,
`Contracts/Streams.lean`; paper: Fact 3.3(3) (`fact:oai-streams`), Lemma A.4(4) (`lem:transfer-streams`)).
No hypotheses beyond the contract's own (equal stream lengths `g`, `BlkTerm` rests). For `W ≥ 1`:
scratch `E = Unit` (one stack `Z`), registers `Option Sym`, program `mergeProg W ord ⟨0, _⟩`, cost
constant `C = 9` (independent of `W`). For `W = 0` the merge is empty: `skip`, `C = 1`. -/
theorem k2Merge_holds (W : ℕ) (ord : Equiv.Perm (Fin W)) : K2MergeStmt W ord := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    refine ⟨1, fun _ => ⟨Unit, inferInstance, inferInstance, Option Sym, skip, inferInstance,
      ⟨none⟩, ?_, ?_⟩⟩
    · simp [Prog.Closed, Prog.FreeBelow, skip]
    · intro g us rests S _ _ _
      apply Runs.of_eval
      intro x
      refine ⟨x, 1, (skip_eval [] _).of_eq ?_ rfl, trivial, by simp⟩
      congr 1
      funext key
      rcases key with (_ | r) | u
      · have hnil : ∀ l : List ℕ, l.flatMap (fun _ => ([] : List (List Bool))) = [] :=
          fun l => List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
        simp [mergePost, mergeRows, hnil, arrSyms_nil]
      · exact r.elim0
      · rfl
  · refine ⟨9, fun _ => ⟨Unit, inferInstance, inferInstance, Option Sym, mergeProg W ord ⟨0, hW⟩,
      inferInstance, ⟨none⟩, closed_mergeProg W ord _, ?_⟩⟩
    intro g us rests S hlen hrests hS
    rw [sum_finRange]
    exact merge_main ord rests S hW g us hlen hrests hS

end SubNLogN.Machine
