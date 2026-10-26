/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.SplitMapPhase
import SubNLogN.Machine.K1.SplitMapCount

/-!
# K1c-mix, superblocks (`K1/SplitMapMain.lean`)

**Scope (honest summary).** The K1c-mix superblock program and its proved exact-stack
specification. A superblock is `q·N1` consecutive records (shape `[N0] × [q] × [N1]`, one value of
the prefix `x0`):
* `pushMarks`: a `mark` on every stream and output stack;
* `splitAll`: block `c` (`N1` records, counted down from the counter `N1`) is moved to stream `c`;
* `mapPhase` (`K1/SplitMapPhase.lean`), `popSeps` (drops the stream marks);
* `mergeAll`: the output stacks are rewound in order `0, …, q-1` onto the accumulator.
Paper: Lemma A.4(3) (`lem:transfer-streams`, `q` streams, nested merge, and amortized counters).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-! ## List lemmas -/

theorem arrSyms_eq_flatMap (ws : List (List Bool)) : arrSyms ws = ws.flatMap recSyms := by
  simp [arrSyms, blk, List.flatMap]

theorem arrSyms_reverse_eq (ws : List (List Bool)) :
    (arrSyms ws).reverse = ws.reverse.flatMap (fun w => (recSyms w).reverse) := by
  rw [arrSyms_eq_flatMap, reverse_flatMap']

theorem take_drop_eq_map {α : Type} (v : List α) (a n : ℕ) (d : α) (h : a + n ≤ v.length) :
    (v.drop a).take n = (List.range n).map (fun l => v.getD (a + l) d) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem]

theorem range_mul_flatMap (a b : ℕ) :
    List.range (a * b) = (List.range a).flatMap (fun h => (List.range b).map (fun r => h * b + r)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
    simp

theorem mk1_ext {q : ℕ} {nm nm' : Fin 3 → List Sym} {st st' ou ou' : Fin q → List Sym}
    {ex ex' : Fin 4 → List Sym} (h1 : nm = nm') (h2 : st = st') (h3 : ou = ou') (h4 : ex = ex') :
    mk1 nm st ou ex = mk1 nm' st' ou' ex' := by
  subst h1 h2 h3 h4
  rfl

@[simp] theorem mk1_strm {q : ℕ} (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym)
    (ex : Fin 4 → List Sym) (c : Fin q) : mk1 nm st ou ex (STRM c) = st c := rfl

@[simp] theorem mk1_out {q : ℕ} (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym)
    (ex : Fin 4 → List Sym) (c : Fin q) : mk1 nm st ou ex (OUT c) = ou c := rfl

@[simp] theorem mk1_nm {q : ℕ} (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym)
    (ex : Fin 4 → List Sym) (i : Fin 3) : mk1 nm st ou ex (.inl i) = nm i := rfl

@[simp] theorem mk1_ex {q : ℕ} (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym)
    (ex : Fin 4 → List Sym) (j : Fin 4) : mk1 nm st ou ex (.inr (.inr (.inr j))) = ex j := rfl

theorem csum_mul (k : ℕ) (f : ℕ → ℕ) :
    ∀ (n0 len : ℕ), csum (fun i => k * f i) n0 len = k * csum f n0 len
  | _, 0 => by simp [csum]
  | n0, len + 1 => by simp only [csum]; rw [csum_mul k f (n0 + 1) len, Nat.mul_add]

theorem csum_vol (w : List (List Bool)) :
    ∀ (n0 len : ℕ), n0 + len ≤ w.length →
      csum (fun i => (w.getD i []).length + 1) n0 len = vol ((w.drop n0).take len)
  | _, 0, _ => by simp [csum]
  | n0, len + 1, h => by
    simp only [csum]
    rw [csum_vol w (n0 + 1) len (by omega), List.drop_eq_getElem_cons (i := n0) (by omega),
      List.take_succ_cons, vol_cons, List.getD_eq_getElem _ _ (by omega)]

theorem vol_uniform (L : ℕ) : ∀ (w : List (List Bool)), (∀ p ∈ w, p.length = L) →
    vol w = w.length * (L + 1)
  | [], _ => by simp
  | p :: w, h => by
    rw [vol_cons, vol_uniform L w (fun p' hp => h p' (List.mem_cons_of_mem _ hp)),
      h p List.mem_cons_self, List.length_cons, Nat.succ_mul]
    omega

/-! ## Programs -/

section Progs

variable {q : ℕ} {A : ℕ}

/-- A `mark` on every stream and every output stack. -/
def pushMarks : P1 q A :=
  forEachFin q (fun c => .seq (lift (Lib.pushC (STRM c) .mark)) (lift (Lib.pushC (OUT c) .mark)))

/-- Block `c` of the superblock (`N1` records, the counter on `NC`) goes to stream `c`. -/
def splitAll : P1 q A := forEachFin q (fun c => cdMove NC CNT TMP (mvRec SRC (STRM c)))

/-- Rewind the output stacks `0, …, q-1` onto the accumulator. -/
def mergeAll : P1 q A := forEachFin q (fun c => rwd (OUT c) ACC)

/-- One superblock. -/
def superblock [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) : P1 q A :=
  .seq pushMarks (.seq splitAll (.seq (mapPhase g) (.seq popSeps mergeAll)))

/-- **The K1c-mix program**: superblocks while the source shows a record; then the accumulator
is rewound onto the destination. -/
def k1mixProg [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) : P1 q A :=
  .seq (lift (Lib.pushC ACC .mark)) (.seq (whileTop SRC isRecStart (superblock g)) (rwd ACC DST))

theorem closed_pushMarks : (pushMarks (q := q) (A := A)).Closed :=
  closed_forEachFin _ _ fun _ => ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]),
    closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC])⟩

theorem closed_splitAll : (splitAll (q := q) (A := A)).Closed :=
  closed_forEachFin _ _ fun _ => closed_cdMove _ _ _ (closed_mvRec _ _)

theorem closed_mergeAll : (mergeAll (q := q) (A := A)).Closed :=
  closed_forEachFin _ _ fun _ => closed_rwd _ _

theorem closed_superblock [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) :
    (superblock (A := A) g).Closed :=
  ⟨closed_pushMarks, closed_splitAll, closed_mapPhase g, closed_popSeps, closed_mergeAll⟩

theorem closed_k1mixProg [NeZero q] (g : (Fin q → ℕ) → Fin q → ℕ) :
    (k1mixProg (A := A) g).Closed :=
  ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]),
    closed_whileTop _ _ (closed_superblock g), closed_rwd _ _⟩

end Progs

/-! ## Marks and merge -/

section Simple

variable {q : ℕ} {A : ℕ}

theorem runs_pushMarks (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (st ou : Fin q → List Sym) :
    Runs (pushMarks (A := A)) (mk1 nm st ou ex)
      (mk1 nm (fun c => Sym.mark :: st c) (fun c => Sym.mark :: ou c) ex) (fun _ => True)
      (2 * q + 1) := by
  have key := runs_forEachFin q (fun c => Prog.seq (lift (M := M1 q A) (Lib.pushC (STRM c) .mark))
      (lift (Lib.pushC (OUT c) .mark))) (fun _ => 2)
    (fun i => mk1 nm (fun c => if c.val < i then Sym.mark :: st c else st c)
      (fun c => if c.val < i then Sym.mark :: ou c else ou c) ex) ?_
  · refine runs_of_eq key (by rw [fam_zero, fam_zero]) (by rw [fam_all, fam_all]) (by simp; omega)
  · intro i
    refine runs_of_forall_runsM fun m => ⟨m, ?_⟩
    have h1 := RunsM.push (M := M1 q A) (STRM i) Sym.mark m
      (mk1 nm (fun c => if c.val < (i : ℕ) then Sym.mark :: st c else st c)
        (fun c => if c.val < (i : ℕ) then Sym.mark :: ou c else ou c) ex)
    have h2 := RunsM.push (M := M1 q A) (OUT i) Sym.mark m
      (Function.update (mk1 nm (fun c => if c.val < (i : ℕ) then Sym.mark :: st c else st c)
        (fun c => if c.val < (i : ℕ) then Sym.mark :: ou c else ou c) ex) (STRM i)
        (Sym.mark :: (mk1 nm (fun c => if c.val < (i : ℕ) then Sym.mark :: st c else st c)
          (fun c => if c.val < (i : ℕ) then Sym.mark :: ou c else ou c) ex) (STRM i)))
    refine RunsM.of_eq (h1.seq h2) rfl rfl rfl ?_ le_rfl
    simp only [upd_strm, upd_out, mk1_strm, mk1_out, lt_irrefl, if_false]
    refine mk1_ext rfl ?_ ?_ rfl
    · exact fam_upd i.val i.isLt (fun c => Sym.mark :: st c) st
    · exact fam_upd i.val i.isLt (fun c => Sym.mark :: ou c) ou

theorem take_finRange_succ (i : ℕ) (hi : i < q) :
    (List.finRange q).take (i + 1) = (List.finRange q).take i ++ [⟨i, hi⟩] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem runs_mergeAll (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (st Z : Fin q → List Sym)
    (Ls : Fin q → List Sym) (hL : ∀ c, Sym.mark ∉ Ls c) :
    Runs (mergeAll (A := A)) (mk1 nm st (fun c => Ls c ++ Sym.mark :: Z c) ex)
      (mk1 nm st Z (Function.update ex 0
        (((List.finRange q).flatMap Ls).reverse ++ ex 0))) (fun _ => True)
      (3 * ((List.finRange q).map fun c => (Ls c).length).sum + 2 * q + 1) := by
  have key := runs_forEachFin q (fun c => rwd (M := M1 q A) (OUT c) ACC)
    (fun c => 3 * (Ls c).length + 2)
    (fun i => mk1 nm st (fun c => if c.val < i then Z c else Ls c ++ Sym.mark :: Z c)
      (Function.update ex 0 ((((List.finRange q).take i).flatMap Ls).reverse ++ ex 0))) ?_
  · refine runs_of_eq key ?_ ?_ ?_
    · rw [fam_zero]
      refine mk1_ext rfl rfl rfl ?_
      simp
    · rw [fam_all]
      refine mk1_ext rfl rfl rfl ?_
      rw [List.take_of_length_le (by simp)]
    · rw [List.sum_map_add, List.map_const', List.sum_replicate, List.length_finRange,
        ← List.sum_map_mul_left]
      simp [smul_eq_mul]
      omega
  · intro i
    refine runs_of_forall_runsM fun m => ⟨m, ?_⟩
    have h := runsM_rwd (M := M1 q A) (src := OUT i) (dst := ACC) (by simp) (Ls i) (Z i) (hL i) m
      (mk1 nm st (fun c => if c.val < (i : ℕ) then Z c else Ls c ++ Sym.mark :: Z c)
        (Function.update ex 0 ((((List.finRange q).take (i : ℕ)).flatMap Ls).reverse ++ ex 0)))
      (by simp only [mk1_out, lt_irrefl, if_false])
    refine RunsM.of_eq h rfl rfl rfl ?_ le_rfl
    simp only [upd_out, upd_ex, mk1_ex, Function.update_self, Function.update_idem]
    refine mk1_ext rfl rfl ?_ ?_
    · exact fam_upd i.val i.isLt Z (fun c => Ls c ++ Sym.mark :: Z c)
    · congr 1
      rw [take_finRange_succ i.val i.isLt, List.flatMap_append, List.reverse_append]
      simp

end Simple

end SubNLogN.Machine.K1.SMM

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-! ## The split -/

section Split

variable {q : ℕ} {A : ℕ}

/-- One block: `N1` records move from the source to stream `c` (they arrive reversed). -/
theorem runs_splitBlk (c : Fin q) (N1 : ℕ) (r2 : List Sym) (hr2 : TermOK r2)
    (w : List (List Bool)) (R : List Sym) (hw : N1 ≤ w.length) (nm : Fin 3 → List Sym)
    (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (hnm0 : nm 0 = arrSyms w ++ R) (hnm2 : nm 2 = natSyms N1 ++ r2) :
    Runs (cdMove NC CNT TMP (mvRec (M := M1 q A) SRC (STRM c))) (mk1 nm st ou ex)
      (mk1 (Function.update nm 0 (arrSyms (w.drop N1) ++ R))
        (Function.update st c ((arrSyms (w.take N1)).reverse ++ st c)) ou ex)
      (fun _ => True) (incSeqCost 6 8 N1 + 3 * vol (w.take N1) + 2 * N1 + 7 * bitLen N1 + 12) := by
  refine runs_of_runsM_all fun m => ?_
  set S : ℕ → L1 q → List Sym := fun i => mk1 (Function.update nm 0 (arrSyms (w.drop i) ++ R))
    (Function.update st c ((arrSyms (w.take i)).reverse ++ st c)) ou ex with hS
  have hS0 : S 0 = mk1 nm st ou ex := by
    rw [hS]
    refine mk1_ext ?_ ?_ rfl rfl
    · rw [List.drop_zero, ← hnm0, Function.update_eq_self]
    · simp
  have key := runsM_cdMove (M := M1 q A) (ns := NC) (cnt := CNT) (tmp := TMP) (by simp) (by simp)
    (by simp) (mvRec SRC (STRM c)) N1 r2 (ex 2) hr2 (fun _ => m) S
    (fun i => 3 * ((w.getD i []).length + 1))
    (by rw [hS0]; exact hnm2) (by rw [hS0]; rfl) (by rw [hS]; rfl) ?_
  · rw [hS0] at key
    refine RunsM.of_eq key rfl rfl rfl (by rw [hS]) ?_
    rw [csum_mul, csum_vol w 0 N1 (by omega), List.drop_zero]
  · intro i hi X
    have hdrop : w.drop i = w[i] :: w.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
    have hsrc : (Function.update (S i) CNT X) SRC = recSyms w[i] ++ (arrSyms (w.drop (i + 1)) ++ R) := by
      rw [Function.update_of_ne (by simp), hS]
      simp only [mk1_nm, Function.update_self]
      rw [hdrop, arrSyms_cons, List.append_assoc]
    have h := runsM_mvRec (M := M1 q A) (src := SRC) (dst := STRM c) (by simp) w[i]
      (arrSyms (w.drop (i + 1)) ++ R) m (Function.update (S i) CNT X) hsrc
    refine RunsM.of_eq h rfl rfl rfl ?_ ?_
    · rw [hS]
      simp only [upd_ex, upd_nm, upd_strm, mk1_strm, Function.update_idem, Function.update_self]
      have e : (arrSyms (List.take (i + 1) w)).reverse =
          (recSyms w[i]).reverse ++ (arrSyms (List.take i w)).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          arrSyms_append, arrSyms_cons, arrSyms_nil, List.append_nil, List.reverse_append]
      rw [e, List.append_assoc]
    · rw [List.getD_eq_getElem _ _ (by omega)]
      omega

theorem runs_splitAll (N1 : ℕ) (r2 : List Sym) (hr2 : TermOK r2)
    (w : List (List Bool)) (R : List Sym) (hw : q * N1 ≤ w.length) (nm : Fin 3 → List Sym)
    (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (hnm0 : nm 0 = arrSyms w ++ R) (hnm2 : nm 2 = natSyms N1 ++ r2) :
    Runs (splitAll (q := q) (A := A)) (mk1 nm st ou ex)
      (mk1 (Function.update nm 0 (arrSyms (w.drop (q * N1)) ++ R))
        (fun c => (arrSyms ((w.drop (c.val * N1)).take N1)).reverse ++ st c) ou ex)
      (fun _ => True)
      (((List.finRange q).map fun c => incSeqCost 6 8 N1 + 3 * vol ((w.drop (c.val * N1)).take N1)
        + 2 * N1 + 7 * bitLen N1 + 12).sum + 1) := by
  have key := runs_forEachFin q (fun c => cdMove NC CNT TMP (mvRec (M := M1 q A) SRC (STRM c)))
    (fun c => incSeqCost 6 8 N1 + 3 * vol ((w.drop (c.val * N1)).take N1) + 2 * N1 +
      7 * bitLen N1 + 12)
    (fun i => mk1 (Function.update nm 0 (arrSyms (w.drop (i * N1)) ++ R))
      (fun c => if c.val < i then (arrSyms ((w.drop (c.val * N1)).take N1)).reverse ++ st c
        else st c) ou ex) ?_
  · refine runs_of_eq key ?_ (by rw [fam_all]) le_rfl
    rw [fam_zero]
    refine mk1_ext ?_ rfl rfl rfl
    rw [Nat.zero_mul, List.drop_zero, ← hnm0, Function.update_eq_self]
  · intro i
    have hi : (i.val + 1) * N1 ≤ w.length :=
      le_trans (Nat.mul_le_mul_right N1 (Nat.succ_le_of_lt i.isLt)) hw
    have h := runs_splitBlk (A := A) i N1 r2 hr2 (w.drop (i.val * N1)) R
      (by rw [List.length_drop]; rw [Nat.succ_mul] at hi; omega)
      (Function.update nm 0 (arrSyms (w.drop (i.val * N1)) ++ R))
      (fun c => if c.val < i.val then (arrSyms ((w.drop (c.val * N1)).take N1)).reverse ++ st c
        else st c) ou ex (by simp) (by simp [hnm2])
    refine runs_of_eq h rfl ?_ le_rfl
    refine mk1_ext ?_ ?_ rfl rfl
    · rw [Function.update_idem, List.drop_drop, Nat.succ_mul]
    · simp only [lt_irrefl, if_false]
      exact fam_upd i.val i.isLt (fun c => (arrSyms ((w.drop (c.val * N1)).take N1)).reverse ++ st c) st

end Split

end SubNLogN.Machine.K1.SMM
