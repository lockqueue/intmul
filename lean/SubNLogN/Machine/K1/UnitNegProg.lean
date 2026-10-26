/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitBase

/-!
# K5-neg, programs and the block step (`K1/UnitNegProg.lean`)

**Scope (honest summary).** Programs of the negation kernel `t ↦ -t mod q^b` (`K5NegStmt`) and
proved exact-stack specifications of its pieces:
* `negAct`: one block of `s` records; the first block of a fiber goes to the accumulator, the
  others to the negation store (`runsM_negAct_first`, `runsM_negAct_rest`);
* `unloadBlk`: the top block of the negation store is restored to its internal order and
  appended to the accumulator (`runsM_unloadBlk`).
Construction: [OAI26, §2.1, proof of Lemma 4] (cited by `SubNLogN/Machine/Contracts/Streams.lean`, `K5NegStmt`):
"Negation leaves the block at zero fixed and reverses the order of the other `Q - 1` blocks. Push
these blocks consecutively to a temporary tape … Reverse each popped block on a second temporary
tape before writing it." Paper: Lemma A.4 (`lem:transfer-streams`, a negative
multiplier adds a reversal).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-- Negation kernel programs: no families; the register holds the "first block" flag. -/
abbrev PN : Type := KP (L5 0 0) Bool

/-! ## Programs -/

/-- One block: the first block of a fiber goes to the accumulator, later ones to the store. -/
def negAct : PN :=
  .seq (.ite (fun r => r.2) (cdMove SC5 CNT5 TMP5 (mvRec SRC5 ACC5))
    (cdMove SC5 CNT5 TMP5 (mvRec SRC5 NEG5))) (.load fun r => (r.1, false))

/-- Move the top block of the negation store, in order, onto the accumulator. -/
def unloadBlk : PN :=
  .seq (lift (Lib.pushC TMP25 .mark)) (.seq (cdMove SC5 CNT5 TMP5 (mvRev NEG5 TMP25))
    (rwd TMP25 ACC5))

/-- Unload the negation store block by block. -/
def unloadNeg : PN := whileTop NEG5 isSepS unloadBlk

/-- One fiber of `q^b` blocks (the depth stack holds `b` tokens). -/
def negFiber (q : ℕ) : PN :=
  .seq (.load fun r => (r.1, true)) (.seq (lift (Lib.pushC NEG5 .mark))
    (.seq (recProg q DEP5 negAct) (.seq unloadNeg (lift (Lib.popR NEG5)))))

/-- Nonempty input, `q ≥ 2`: unary `b`, all fibers, clear the depth stack. -/
def negMain (q : ℕ) : PN :=
  .seq (unaryB BC5 CNT5 TMP5 DEP5) (.seq (whileTop SRC5 isRecStart (negFiber q)) (clearDep DEP5))

/-- **The negation kernel** for `q ≥ 2` (counters are read only if the input is nonempty). -/
def negProg (q : ℕ) : PN :=
  .seq (lift (Lib.pushC ACC5 .mark)) (.seq (.seq (peekO SRC5)
    (.ite (fun r => testO isRecStart r.1) (negMain q) Lib.skip)) (rwd ACC5 DST5))

/-- The identity kernel (used for `q ≤ 1`, where `q^b ≤ 1`). -/
def idProg5 : PN := .seq (lift (Lib.pushC ACC5 .mark)) (.seq (mvArr SRC5 ACC5) (rwd ACC5 DST5))

theorem closed_negAct : negAct.Closed :=
  ⟨⟨closed_cdMove _ _ _ (closed_mvRec _ _), closed_cdMove _ _ _ (closed_mvRec _ _)⟩, trivial⟩

theorem closed_unloadBlk : unloadBlk.Closed :=
  ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]),
    closed_cdMove _ _ _ (closed_mvRev _ _), closed_rwd _ _⟩

theorem closed_negFiber (q : ℕ) : (negFiber q).Closed :=
  ⟨trivial, closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]),
    closed_recProg q _ closed_negAct, closed_whileTop _ _ closed_unloadBlk,
    closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.popR])⟩

theorem closed_unaryB {K M : Type} (bc cnt tmp dk : K) : (unaryB (M := M) bc cnt tmp dk).Closed :=
  ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]),
    closed_cdMove _ _ _ (closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]))⟩

theorem closed_clearDep {K M : Type} (dk : K) : (clearDep (M := M) dk).Closed :=
  ⟨closed_whileTop _ _ (closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.popR])),
    closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.popR])⟩

theorem closed_negProg (q : ℕ) : (negProg q).Closed :=
  ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]),
    ⟨trivial, ⟨closed_unaryB _ _ _ _, closed_whileTop _ _ (closed_negFiber q), closed_clearDep _⟩,
      trivial⟩, closed_rwd _ _⟩

theorem closed_idProg5 : idProg5.Closed :=
  ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]), closed_mvArr _ _,
    closed_rwd _ _⟩

/-! ## Blocks -/

/-- Block `t` (records `[t·s, (t+1)·s)`) of a record list. -/
def blkOf (s : ℕ) (f : List (List Bool)) (t : ℕ) : List (List Bool) := (f.drop (t * s)).take s

/-- Output of one negated fiber of `Q` blocks: block `0`, then blocks `Q-1, …, 1`. -/
def negFib (Q s : ℕ) (f : List (List Bool)) : List (List Bool) :=
  blkOf s f 0 ++ (List.range (Q - 1)).reverse.flatMap fun i => blkOf s f (i + 1)

theorem take_mul_flatMap {α : Type} (u : List α) (s : ℕ) :
    ∀ k : ℕ, u.take (k * s) = (List.range k).flatMap fun i => (u.drop (i * s)).take s
  | 0 => by simp
  | k + 1 => by
    rw [Nat.succ_mul, List.take_add, take_mul_flatMap u s k, List.range_succ, List.flatMap_append]
    simp

theorem take_drop_blocks (s Q : ℕ) (w : List (List Bool)) :
    (w.take (Q * s)).drop s = (List.range (Q - 1)).flatMap fun i => blkOf s w (i + 1) := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
    rw [List.drop_take, show (Q' + 1) * s - s = Q' * s by rw [Nat.succ_mul]; omega,
      take_mul_flatMap, show Q' + 1 - 1 = Q' by omega]
    refine flatMap_congr' fun i _ => ?_
    rw [blkOf, List.drop_drop, Nat.succ_mul, Nat.add_comm]

theorem rev_arrSyms_flatMap {α : Type} (f : α → List (List Bool)) :
    ∀ l : List α, (arrSyms (l.flatMap f)).reverse = l.reverse.flatMap (fun x => (arrSyms (f x)).reverse)
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, arrSyms_append, List.reverse_append, rev_arrSyms_flatMap f l,
      List.reverse_cons, List.flatMap_append]
    simp

theorem vol_reverse (u : List (List Bool)) : vol u.reverse = vol u := by
  induction u with
  | nil => rfl
  | cons p u ih => rw [List.reverse_cons, vol_append, ih, vol_cons]; simp [vol, arrSyms_cons, length_recSyms]; omega

theorem vol_flatten (bs : List (List (List Bool))) : vol bs.flatten = (bs.map vol).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.flatten_cons, vol_append, ih, List.map_cons, List.sum_cons]

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := TMFw.W3s.bitLen_le_of_lt Nat.lt_two_pow_self

/-! ## The block step -/

/-- Recursion states of one fiber after `n` blocks (depth stack: its base `sg 1`). -/
def negSt (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs xs : Fin 0 → List Sym)
    (s : ℕ) (w : List (List Bool)) (R accP neg0 : List Sym) (n : ℕ) : L5 0 0 → List Sym :=
  mk5 (Function.update nm 0 (arrSyms (w.drop (n * s)) ++ R))
    (Function.update (Function.update sg 0 ((arrSyms (w.take (min n 1 * s))).reverse ++ accP)) 4
      ((arrSyms ((w.take (n * s)).drop s)).reverse ++ Sym.mark :: neg0)) zs xs

/-- Cost bound of one block step. -/
def negActCost (s : ℕ) (blk : List (List Bool)) : ℕ := 3 * vol blk + 23 * s + 14

section Steps

variable (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs xs : Fin 0 → List Sym)
  (s : ℕ) (w : List (List Bool)) (R accP neg0 : List Sym) (r3 : List Sym)

theorem runsM_negAct_first (hr3 : TermOK r3) (hw : s ≤ w.length) (hnm3 : nm 3 = natSyms s ++ r3) :
    RunsM negAct true (negSt nm sg zs xs s w R accP neg0 0) false
      (negSt nm sg zs xs s w R accP neg0 1) (negActCost s (w.take s)) := by
  have h := runsM_cdMvRec (M := Bool) (ns := SC5) (cnt := CNT5) (tmp := TMP5) (src := SRC5)
    (dst := ACC5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s r3 hr3 w R hw true (negSt nm sg zs xs s w R accP neg0 0)
    (by simp only [negSt, mk5_nm, Function.update_self, Nat.zero_mul, List.drop_zero])
    (by simp only [negSt, mk5_nm]; rw [Function.update_of_ne (by decide)]; exact hnm3)
  have h2 := RunsM.ite_pos (c := fun r : Option Sym × Bool => r.2)
    (p' := cdMove SC5 CNT5 TMP5 (mvRec SRC5 NEG5)) (fun _ => rfl) h
  have h3 := RunsM.load (K := L5 0 0) (fun _ => false) true
    (Function.update (Function.update (negSt nm sg zs xs s w R accP neg0 0) SRC5
      (arrSyms (w.drop s) ++ R)) ACC5
      ((arrSyms (w.take s)).reverse ++ negSt nm sg zs xs s w R accP neg0 0 ACC5))
  refine RunsM.of_eq (h2.seq h3) rfl rfl rfl ?_ ?_
  · simp only [negSt, upd5_nm, upd5_sg, mk5_sg, Function.update_idem, Nat.zero_mul,
      Nat.one_mul, Nat.min_def, List.take_zero, List.drop_nil, arrSyms_nil, List.reverse_nil,
      List.nil_append]
    refine mk5_ext rfl ?_ rfl rfl
    funext j
    fin_cases j <;> simp [Function.update_apply, List.drop_take]
  · unfold negActCost
    have := incSeqCost_le 6 8 s
    have := bitLen_le_self s
    omega

theorem runsM_negAct_rest (n : ℕ) (hn : 1 ≤ n) (hr3 : TermOK r3) (hw : (n + 1) * s ≤ w.length)
    (hnm3 : nm 3 = natSyms s ++ r3) :
    RunsM negAct false (negSt nm sg zs xs s w R accP neg0 n) false
      (negSt nm sg zs xs s w R accP neg0 (n + 1)) (negActCost s ((w.drop (n * s)).take s)) := by
  have hw' : s ≤ (w.drop (n * s)).length := by
    rw [List.length_drop, Nat.succ_mul] at *
    omega
  have h := runsM_cdMvRec (M := Bool) (ns := SC5) (cnt := CNT5) (tmp := TMP5) (src := SRC5)
    (dst := NEG5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s r3 hr3 (w.drop (n * s)) R hw' false
    (negSt nm sg zs xs s w R accP neg0 n)
    (by simp only [negSt, mk5_nm, Function.update_self])
    (by simp only [negSt, mk5_nm]; rw [Function.update_of_ne (by decide)]; exact hnm3)
  have h2 := RunsM.ite_neg (c := fun r : Option Sym × Bool => r.2)
    (p := cdMove SC5 CNT5 TMP5 (mvRec SRC5 ACC5)) (fun _ => rfl) h
  have h3 := RunsM.load (K := L5 0 0) (fun _ => false) false
    (Function.update (Function.update (negSt nm sg zs xs s w R accP neg0 n) SRC5
      (arrSyms ((w.drop (n * s)).drop s) ++ R)) NEG5
      ((arrSyms ((w.drop (n * s)).take s)).reverse ++ negSt nm sg zs xs s w R accP neg0 n NEG5))
  refine RunsM.of_eq (h2.seq h3) rfl rfl rfl ?_ ?_
  · have hmin : min n 1 = 1 := by omega
    have hmin' : min (n + 1) 1 = 1 := by omega
    have hneg : (arrSyms ((w.take ((n + 1) * s)).drop s)).reverse =
        (arrSyms ((w.drop (n * s)).take s)).reverse ++ (arrSyms ((w.take (n * s)).drop s)).reverse := by
      have hw2 : n * s + s ≤ w.length := by rw [← Nat.succ_mul]; exact hw
      rw [Nat.succ_mul, List.take_add, List.drop_append_of_le_length (by
        rw [List.length_take]; have := Nat.le_mul_of_pos_left s hn; omega),
        arrSyms_append, List.reverse_append]
    simp only [negSt, upd5_nm, upd5_sg, mk5_sg, Function.update_idem, hmin, hmin',
      List.drop_drop]
    refine mk5_ext ?_ ?_ rfl rfl
    · rw [Nat.succ_mul, Nat.add_comm (n * s) s]
    · funext j
      fin_cases j <;> simp [Function.update_apply, hneg]
  · unfold negActCost
    have := incSeqCost_le 6 8 s
    have := bitLen_le_self s
    omega

/-- Cost bound of unloading one block. -/
def unloadCost (s : ℕ) (b : List (List Bool)) : ℕ := 6 * vol b + 26 * s + 15

theorem runsM_unloadBlk (m : Bool) (sg : Fin 9 → List Sym) (b : List (List Bool)) (hb : b.length = s)
    (Rn : List Sym) (hRn : TermOK Rn) (hr3 : TermOK r3) (hnm3 : nm 3 = natSyms s ++ r3)
    (hneg : sg 4 = (arrSyms b).reverse ++ Rn) :
    RunsM unloadBlk m (mk5 nm sg zs xs) m
      (mk5 nm (Function.update (Function.update sg 4 Rn) 0 ((arrSyms b).reverse ++ sg 0)) zs xs)
      (unloadCost s b) := by
  have h1 := RunsM.push (M := Bool) TMP25 Sym.mark m (mk5 nm sg zs xs)
  rw [upd5_sg, mk5_sg] at h1
  have h2 := runsM_cdMvRev (M := Bool) (ns := SC5) (cnt := CNT5) (tmp := TMP5) (src := NEG5)
    (dst := TMP25) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r3 hr3 b.reverse Rn hRn m (mk5 nm (Function.update sg 5 (Sym.mark :: sg 5)) zs xs)
    (by rw [mk5_sg, Function.update_of_ne (by decide), hneg, arrSyms_reverse_eq])
    (by rw [mk5_nm, List.length_reverse, hb, hnm3])
  rw [upd5_sg, upd5_sg, mk5_sg, List.reverse_reverse] at h2
  have h3 := runsM_rwd (M := Bool) (src := TMP25) (dst := ACC5) (by decide) (arrSyms b) (sg 5)
    (mark_not_mem_arrSyms b) m
    (mk5 nm (Function.update (Function.update (Function.update sg 5 (Sym.mark :: sg 5)) 4 Rn) 5
      (arrSyms b ++ Function.update (Function.update sg 5 (Sym.mark :: sg 5)) 4 Rn 5)) zs xs)
    (by simp [Function.update_apply])
  rw [upd5_sg, upd5_sg, mk5_sg] at h3
  refine RunsM.of_eq (h1.seq (h2.seq h3)) rfl rfl rfl ?_ ?_
  · refine mk5_ext rfl ?_ rfl rfl
    funext j
    fin_cases j <;> simp [Function.update_apply]
  · unfold unloadCost
    rw [vol_reverse, List.length_reverse, hb, ← vol]
    have := incSeqCost_le 6 8 s
    have := bitLen_le_self s
    omega

end Steps

end SubNLogN.Machine.K1.SMM
