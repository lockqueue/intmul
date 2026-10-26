/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.SplitMapDigit

/-!
# K1c, the map phase (`K1/SplitMapPhase.lean`)

**Scope (honest summary).** Proved exact-stack specifications of the K1c map phase:
* `digitLoop`: all digit tuples of one aligned record tuple (`loopR_digitLoop`);
* `recStep`: one aligned record tuple, record ends included (`runs_recStep`);
* `mapPhase`: all aligned record tuples of a superblock (`loopR_mapPhase`).
The streams hold the `q` blocks reversed (last record on top); the output stacks receive the
output records `G B t c` (output digit `d` of stream `c` is `g (fun c' => digit d of t c') c`) in
`.down` orientation. Paper: Lemma A.4(3) (`lem:transfer-streams`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts

section Progs

variable {q : ℕ} [NeZero q] {A : ℕ}

/-- All digit tuples of the current record tuple (while stream `0` shows a bit). -/
def digitLoop (g : (Fin q → ℕ) → Fin q → ℕ) : P1 q A := whileTop (STRM 0) Sym.isBit (digitStep g)

/-- Pop the reversed record ends (`sep`) of all streams. -/
def popSeps : P1 q A := forEachFin q (fun c => lift (Lib.popR (STRM c)))

/-- Push a record end on every output stack. -/
def pushSeps : P1 q A := forEachFin q (fun c => lift (Lib.pushC (OUT c) .sep))

/-- One aligned record tuple. -/
def recStep (g : (Fin q → ℕ) → Fin q → ℕ) : P1 q A := .seq popSeps (.seq pushSeps (digitLoop g))

/-- All aligned record tuples (while stream `0` shows a reversed record end). -/
def mapPhase (g : (Fin q → ℕ) → Fin q → ℕ) : P1 q A := whileTop (STRM 0) isSepS (recStep g)

theorem closed_digitLoop (g : (Fin q → ℕ) → Fin q → ℕ) : (digitLoop (A := A) g).Closed :=
  closed_whileTop _ _ (closed_digitStep g)

omit [NeZero q] in
theorem closed_popSeps : (popSeps (q := q) (A := A)).Closed :=
  closed_forEachFin _ _ fun _ => closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.popR])

omit [NeZero q] in
theorem closed_pushSeps : (pushSeps (q := q) (A := A)).Closed :=
  closed_forEachFin _ _ fun _ => closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC])

theorem closed_recStep (g : (Fin q → ℕ) → Fin q → ℕ) : (recStep (A := A) g).Closed :=
  ⟨closed_popSeps, closed_pushSeps, closed_digitLoop g⟩

theorem closed_mapPhase (g : (Fin q → ℕ) → Fin q → ℕ) : (mapPhase (A := A) g).Closed :=
  closed_whileTop _ _ (closed_recStep g)

end Progs

/-! ## Data of a record tuple -/

/-- The digit tuples of a record tuple `t` (records of `B` digits). -/
def dtups {q : ℕ} (B : ℕ) (t : Fin q → List ℕ) : List (Fin q → ℕ) :=
  (List.range B).map fun d => fun c => (t c).getD d 0

/-- Output record of stream `c` for the record tuple `t`. -/
def outRec {q : ℕ} (g : (Fin q → ℕ) → Fin q → ℕ) (B : ℕ) (t : Fin q → List ℕ) (c : Fin q) :
    List ℕ :=
  (List.range B).map fun d => g (fun c' => (t c').getD d 0) c

theorem map_dtups {q : ℕ} (B : ℕ) (t : Fin q → List ℕ) (c : Fin q) (h : (t c).length = B) :
    (dtups B t).map (fun dt => dt c) = t c := by
  subst h
  apply List.ext_getElem (by simp [dtups])
  intro n h1 h2
  simp only [dtups, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ h2]

theorem digitRec_eq_flatMap {q : ℕ} (A B : ℕ) (t : Fin q → List ℕ) (c : Fin q)
    (h : (t c).length = B) :
    digitRec A (t c) = (dtups B t).flatMap (fun dt => bitsLE (digitWidth A) (dt c)) := by
  conv_lhs => rw [← map_dtups B t c h]
  simp [digitRec, digitBits, List.flatMap_map]

theorem digitRec_outRec {q : ℕ} (g : (Fin q → ℕ) → Fin q → ℕ) (A B : ℕ) (t : Fin q → List ℕ)
    (c : Fin q) :
    digitRec A (outRec g B t c) =
      (dtups B t).flatMap (fun dt => bitsLE (digitWidth A) (g dt c)) := by
  simp [digitRec, digitBits, outRec, dtups, List.flatMap_map]

theorem mem_dtups_lt {q : ℕ} (A B : ℕ) (t : Fin q → List ℕ) (ht : ∀ c, ∀ d ∈ t c, d < A)
    (hA : ∀ c, (t c).length = B) : ∀ dt ∈ dtups B t, ∀ c, dt c < 2 ^ digitWidth A := by
  intro dt hdt c
  simp only [dtups, List.mem_map, List.mem_range] at hdt
  obtain ⟨d, hd, rfl⟩ := hdt
  have hlt : (t c).getD d 0 < A := by
    rw [List.getD_eq_getElem _ _ (by rw [hA c]; exact hd)]
    exact ht c _ (List.getElem_mem _)
  have hA1 : A - 1 < 2 ^ digitWidth A := Nat.lt_size_self _
  simp only [digitWidth] at hA1 ⊢
  omega

theorem runs_of_eq {K R : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) R}
    {S S2 S' S2' : K → List Sym} {Q : R → Prop} {T T2 : ℕ} (h : Runs P S S' Q T) (hS : S = S2)
    (hS' : S' = S2') (hT : T ≤ T2) : Runs P S2 S2' Q T2 := by
  subst hS hS'
  exact WP.W9comp.runs_mono h (fun _ h => h) hT

theorem reverse_flatMap' {α β : Type} (f : α → List β) :
    ∀ l : List α, (l.flatMap f).reverse = l.reverse.flatMap (fun x => (f x).reverse)
  | [] => rfl
  | x :: l => by simp [reverse_flatMap' f l, List.flatMap_append]

theorem head_bit_of_ne {l : List Bool} (hl : l ≠ []) (R : List Sym) :
    testO Sym.isBit ((l.map Sym.bit).reverse ++ R).head? = true := by
  obtain ⟨x, xs, hx⟩ : ∃ x xs, l.reverse = x :: xs := by
    cases h : l.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp h) hl
    | cons x xs => exact ⟨x, xs, rfl⟩
  rw [← List.map_reverse, hx]
  rfl

/-! ## The loops -/

section Loops

variable {q : ℕ} [NeZero q] {A : ℕ} (g : (Fin q → ℕ) → Fin q → ℕ)

theorem loopR_digitLoop (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (W : Fin q → List Sym)
    (hW : testO Sym.isBit (W 0).head? = false) :
    ∀ (rd : List (Fin q → ℕ)) (st ou : Fin q → List Sym),
      (∀ dt ∈ rd, ∀ c, dt c < 2 ^ digitWidth A) →
      (∀ c, st c = rd.flatMap (fun dt => ((bitsLE (digitWidth A) (dt c)).map Sym.bit).reverse) ++
        W c) →
      LoopR (M := M1 q A) (STRM 0) Sym.isBit (digitStep (A := A) g) (mk1 nm st ou ex)
        (mk1 nm W (fun c => rd.reverse.flatMap (fun dt =>
          (bitsLE (digitWidth A) (g dt c)).map Sym.bit) ++ ou c) ex)
        (rd.length * (digitWidth A * (4 * q + 4)) + 1) := by
  by_cases hw : digitWidth A = 0
  · have hb : ∀ d, bitsLE (digitWidth A) d = [] := by simp [bitsLE, hw]
    intro rd st ou _ hst
    have hst' : st = W := by
      funext c
      simp [hst c, hb]
    subst hst'
    refine (LoopR.congr (LoopR.stop ?_) ?_).mono (Nat.le_add_left _ _)
    · exact hW
    · congr 1
      funext c
      simp [hb]
  · intro rd
    induction rd with
    | nil =>
      intro st ou _ hst
      have hst' : st = W := by
        funext c
        simp [hst c]
      subst hst'
      refine (LoopR.congr (LoopR.stop ?_) ?_).mono (Nat.le_add_left _ _)
      · exact hW
      · simp
    | cons dt rd ih =>
      intro st ou hdg hst
      have hdt : ∀ c, dt c < 2 ^ digitWidth A := hdg dt List.mem_cons_self
      have hrd : ∀ dt ∈ rd, ∀ c, dt c < 2 ^ digitWidth A :=
        fun dt' h => hdg dt' (List.mem_cons_of_mem _ h)
      have hst2 : ∀ c, st c = ((bitsLE (digitWidth A) (dt c)).map Sym.bit).reverse ++
          ((rd.flatMap fun dt => ((bitsLE (digitWidth A) (dt c)).map Sym.bit).reverse) ++ W c) := by
        intro c
        rw [hst c, List.flatMap_cons, List.append_assoc]
      have h1 := runs_digitStep (A := A) g dt hdt
        (fun c => (rd.flatMap fun dt => ((bitsLE (digitWidth A) (dt c)).map Sym.bit).reverse) ++ W c)
        nm ex st ou hst2
      have h2 := ih _ (fun c => (bitsLE (digitWidth A) (g dt c)).map Sym.bit ++ ou c) hrd
        (fun c => rfl)
      have hc : testO Sym.isBit ((mk1 nm st ou ex) (STRM 0)).head? = true := by
        show testO Sym.isBit (st 0).head? = true
        rw [hst2 0]
        apply head_bit_of_ne
        rw [← List.length_pos_iff, length_bitsLE]
        omega
      refine ((LoopR.step hc h1 h2).congr ?_).mono ?_
      · congr 1
        funext c
        simp [List.flatMap_append, List.append_assoc]
      · simp only [List.length_cons]
        have hw1 : 1 ≤ digitWidth A := Nat.one_le_iff_ne_zero.mpr hw
        have : 2 * (q * (digitWidth A + 1) + 1) + 2 ≤ digitWidth A * (4 * q + 4) := by nlinarith
        nlinarith

omit [NeZero q] in
theorem runs_popSeps (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (st ou X : Fin q → List Sym)
    (x : Sym) (hst : ∀ c, st c = x :: X c) :
    Runs (popSeps (A := A)) (mk1 nm st ou ex) (mk1 nm X ou ex) (fun _ => True) (q + 1) := by
  have key := runs_forEachFin q (fun c => lift (M := M1 q A) (Lib.popR (STRM c))) (fun _ => 1)
    (fun i => mk1 nm (fun c => if c.val < i then X c else st c) ou ex) ?_
  · refine runs_of_eq key (by rw [fam_zero]) (by rw [fam_all]) (by simp)
  · intro i
    refine runs_of_runsM_all fun m => ?_
    have h := RunsM.pop (M := M1 q A) (STRM i) x (X i) m
      (mk1 nm (fun c => if c.val < (i : ℕ) then X c else st c) ou ex) (by simp [hst i])
    refine RunsM.of_eq h rfl rfl rfl ?_ le_rfl
    rw [upd_strm]
    congr 1
    exact fam_upd i.val i.isLt X st

omit [NeZero q] in
theorem runs_pushSeps (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (st ou : Fin q → List Sym) :
    Runs (pushSeps (A := A)) (mk1 nm st ou ex) (mk1 nm st (fun c => Sym.sep :: ou c) ex)
      (fun _ => True) (q + 1) := by
  have key := runs_forEachFin q (fun c => lift (M := M1 q A) (Lib.pushC (OUT c) .sep))
    (fun _ => 1)
    (fun i => mk1 nm st (fun c => if c.val < i then Sym.sep :: ou c else ou c) ex) ?_
  · refine runs_of_eq key (by rw [fam_zero]) (by rw [fam_all]) (by simp)
  · intro i
    refine runs_of_runsM_all fun m => ?_
    have h := RunsM.push (M := M1 q A) (OUT i) Sym.sep m
      (mk1 nm st (fun c => if c.val < (i : ℕ) then Sym.sep :: ou c else ou c) ex)
    refine RunsM.of_eq h rfl rfl rfl ?_ le_rfl
    rw [upd_out]
    congr 1
    have e : (mk1 nm st (fun c : Fin q => if c.val < (i : ℕ) then Sym.sep :: ou c else ou c) ex)
        (OUT i) = ou i := by simp
    rw [e]
    exact fam_upd i.val i.isLt (fun c => Sym.sep :: ou c) ou

/-- **One aligned record tuple.** -/
theorem runs_recStep (B : ℕ) (t : Fin q → List ℕ) (ht : ∀ c, (t c).length = B)
    (hA : ∀ c, ∀ d ∈ t c, d < A) (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (W ou : Fin q → List Sym)
    (hW : testO Sym.isBit (W 0).head? = false) :
    Runs (recStep (A := A) g) (mk1 nm (fun c => (recSyms (digitRec A (t c))).reverse ++ W c) ou ex)
      (mk1 nm W (fun c => recSyms (digitRec A (outRec g B t c)) ++ ou c) ex) (fun _ => True)
      (2 * q + 4 + B * (digitWidth A * (4 * q + 4))) := by
  set X : Fin q → List Sym := fun c => ((digitRec A (t c)).map Sym.bit).reverse ++ W c with hX
  have h1 := runs_popSeps (A := A) nm ex (fun c => (recSyms (digitRec A (t c))).reverse ++ W c) ou X
    Sym.sep (fun c => by simp [hX, recSyms_reverse, List.map_reverse])
  have h2 := runs_pushSeps (A := A) nm ex X ou
  have hX2 : ∀ c, X c = (dtups B t).reverse.flatMap
      (fun dt => ((bitsLE (digitWidth A) (dt c)).map Sym.bit).reverse) ++ W c := by
    intro c
    rw [hX]
    simp only
    rw [digitRec_eq_flatMap A B t c (ht c), List.map_flatMap, reverse_flatMap']
  have h3 := runs_whileTop (loopR_digitLoop (A := A) g nm ex W hW (dtups B t).reverse X
    (fun c => Sym.sep :: ou c) (fun dt hdt => mem_dtups_lt A B t hA ht dt (List.mem_reverse.mp hdt))
    hX2)
  refine runs_of_eq (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 h3)) rfl ?_ ?_
  · congr 1
    funext c
    rw [List.reverse_reverse, digitRec_outRec]
    simp [recSyms, List.map_flatMap]
  · simp [dtups]
    omega

/-- **The map phase**, by induction on the record tuples in processing order (last first). -/
theorem loopR_mapPhase (B : ℕ) (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (W : Fin q → List Sym)
    (hW : (W 0).head? = some Sym.mark) :
    ∀ (ts : List (Fin q → List ℕ)) (st ou : Fin q → List Sym),
      (∀ t ∈ ts, ∀ c, (t c).length = B ∧ ∀ d ∈ t c, d < A) →
      (∀ c, st c = ts.flatMap (fun t => (recSyms (digitRec A (t c))).reverse) ++ W c) →
      LoopR (M := M1 q A) (STRM 0) isSepS (recStep (A := A) g) (mk1 nm st ou ex)
        (mk1 nm W (fun c => ts.reverse.flatMap
          (fun t => recSyms (digitRec A (outRec g B t c))) ++ ou c) ex)
        (ts.length * (2 * q + 6 + B * (digitWidth A * (4 * q + 4))) + 1)
  | [], st, ou, _, hst => by
    have hst' : st = W := by
      funext c
      simp [hst c]
    subst hst'
    refine (LoopR.congr (LoopR.stop ?_) ?_).mono (by simp)
    · show testO isSepS (st 0).head? = false
      simp [hW, testO, isSepS]
    · simp
  | t :: ts, st, ou, hts, hst => by
    have ht := hts t List.mem_cons_self
    have hts' : ∀ t ∈ ts, ∀ c, (t c).length = B ∧ ∀ d ∈ t c, d < A :=
      fun t' h => hts t' (List.mem_cons_of_mem _ h)
    set W' : Fin q → List Sym := fun c => ts.flatMap (fun t => (recSyms (digitRec A (t c))).reverse)
      ++ W c with hW'
    have hW'0 : testO Sym.isBit (W' 0).head? = false := by
      rw [hW']
      cases ts with
      | nil => simp [hW, testO]
      | cons t' ts' => simp [recSyms_reverse, testO]
    have hst2 : ∀ c, st c = (recSyms (digitRec A (t c))).reverse ++ W' c := by
      intro c
      rw [hst c, hW']
      simp [List.append_assoc]
    have hst3 : st = fun c => (recSyms (digitRec A (t c))).reverse ++ W' c := funext hst2
    have h1 := runs_recStep (A := A) g B t (fun c => (ht c).1) (fun c => (ht c).2) nm ex W' ou hW'0
    rw [← hst3] at h1
    have h2 := loopR_mapPhase B nm ex W hW ts W'
      (fun c => recSyms (digitRec A (outRec g B t c)) ++ ou c) hts' (fun c => rfl)
    have hc : testO isSepS ((mk1 nm st ou ex) (STRM 0)).head? = true := by
      show testO isSepS (st 0).head? = true
      rw [hst2 0, recSyms_reverse]
      rfl
    refine ((LoopR.step hc h1 h2).congr ?_).mono ?_
    · congr 1
      funext c
      simp [List.flatMap_append, List.append_assoc]
    · simp only [List.length_cons]
      nlinarith

end Loops

end SubNLogN.Machine.K1.SMM
