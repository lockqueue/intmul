/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.SplitMapBase
import SubNLogN.Machine.Contracts.Family
import Mathlib.Tactic.Linarith

/-!
# K1/K5 shared kit, part 2 (`K1/SplitMapMove.lean`): loop forms, record movers, encodings

**Scope (honest summary).** Proved helper lemmas (no contract is proved here):
* `LoopR` (register-agnostic loop form of `whileTop`, steps `LoopR.stop`/`LoopR.step`,
  `runs_whileTop`) and `LoopM` (exact-state form, `LoopM.stop`/`LoopM.step`, `runsM_whileTop'`);
* `runsM_forEachProg`, `runs_of_forall_runsM`, `runsM_of_runs`-style conversions;
* record movers: `mvRec` (one record, arrives reversed; W4 `moveRec`), `mvRev` (one reversed
  record, order restored), `mvArr` (all records of an array), `rwd` (rewind to a `mark`);
* encoding lemmas for `recSyms`, `arrSyms`, `vol`, and `bitsVal (bitsLE w d) = d % 2^w`.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts

/-! ## Symbol tests -/

/-- Record start in `.down` orientation: a payload bit or the record end `sep`. -/
def isRecStart : Sym → Bool
  | .bit _ => true
  | .sep => true
  | _ => false

/-- Is the symbol `sep`? -/
def isSepS : Sym → Bool
  | .sep => true
  | _ => false

/-- Is the symbol the depth token? -/
def isTokS (x : Sym) : Bool := decide (x = tok)

/-! ## Encodings -/

@[simp] theorem arrSyms_nil : arrSyms [] = [] := rfl

theorem arrSyms_cons (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := by
  simp [arrSyms, blk]

theorem arrSyms_append (v w : List (List Bool)) : arrSyms (v ++ w) = arrSyms v ++ arrSyms w := by
  simp [arrSyms, blk]

theorem length_recSyms (p : List Bool) : (recSyms p).length = p.length + 1 := by
  simp [recSyms]

@[simp] theorem vol_nil : vol [] = 0 := rfl

theorem vol_cons (p : List Bool) (v : List (List Bool)) : vol (p :: v) = p.length + 1 + vol v := by
  simp [vol, arrSyms_cons, length_recSyms]

theorem vol_append (v w : List (List Bool)) : vol (v ++ w) = vol v + vol w := by
  simp [vol, arrSyms_append]

theorem recSyms_reverse (p : List Bool) :
    (recSyms p).reverse = Sym.sep :: p.reverse.map Sym.bit := by
  simp [recSyms, List.map_reverse]

theorem mark_not_mem_recSyms (p : List Bool) : Sym.mark ∉ recSyms p := by
  simp [recSyms]

theorem mark_not_mem_arrSyms (v : List (List Bool)) : Sym.mark ∉ arrSyms v := by
  induction v with
  | nil => simp
  | cons p v ih =>
    rw [arrSyms_cons, List.mem_append, not_or]
    exact ⟨mark_not_mem_recSyms p, ih⟩

theorem testO_recStart (p : List Bool) (R : List Sym) :
    testO isRecStart (recSyms p ++ R).head? = true := by
  cases p with
  | nil => rfl
  | cons b p => rfl

theorem testO_recStart_of_blkTerm {R : List Sym} (hR : BlkTerm R) :
    testO isRecStart R.head? = false := by
  cases R with
  | nil => rfl
  | cons x R =>
    obtain ⟨h1, h2⟩ := hR x rfl
    cases x <;> simp_all [testO, isRecStart, isDataSym]

theorem termOK_of_blkTerm {R : List Sym} (hR : BlkTerm R) : TermOK R := by
  intro x hx
  obtain ⟨h1, -⟩ := hR x hx
  cases x <;> simp_all [isDataSym]

theorem bitsVal_bitsLE : ∀ (w d : ℕ), TMFw.bitsVal (bitsLE w d) = d % 2 ^ w
  | 0, d => by simp [bitsLE, Nat.mod_one]
  | w + 1, d => by
    have h1 : bitsLE (w + 1) d = d.testBit 0 :: bitsLE w (d / 2) := by
      simp only [bitsLE, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      simp [Function.comp, Nat.testBit_add_one]
    rw [h1, TMFw.bitsVal_cons, bitsVal_bitsLE w (d / 2), pow_succ', Nat.mod_mul]
    have h2 : (d.testBit 0).toNat = d % 2 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]
    rw [h2]
    omega

theorem bitsVal_bitsLE_of_lt {w d : ℕ} (h : d < 2 ^ w) : TMFw.bitsVal (bitsLE w d) = d := by
  rw [bitsVal_bitsLE, Nat.mod_eq_of_lt h]

theorem length_bitsLE (w d : ℕ) : (bitsLE w d).length = w := by simp [bitsLE]

/-! ## Loop forms -/

section Loops

variable {K M : Type} [DecidableEq K]

/-- Register-agnostic loop form of `whileTop k c body`. -/
def LoopR (k : K) (c : Sym → Bool) (body : KP K M) (S S' : K → List Sym) (T : ℕ) : Prop :=
  ∀ m : M, ∃ m' t, t ≤ T ∧ Eval [] (.loop (fun r => testO c r.1) (.seq body (peekO k)))
    ⟨((S k).head?, m), S⟩ ⟨((S' k).head?, m'), S'⟩ t

theorem LoopR.stop {k : K} {c : Sym → Bool} {body : KP K M} {S : K → List Sym}
    (h : testO c (S k).head? = false) : LoopR k c body S S 1 :=
  fun m => ⟨m, 1, le_rfl, Eval.loop_false h⟩

theorem LoopR.step {k : K} {c : Sym → Bool} {body : KP K M} {S S1 S' : K → List Sym} {T1 T2 : ℕ}
    (hc : testO c (S k).head? = true) (hb : Runs body S S1 (fun _ => True) T1)
    (hl : LoopR k c body S1 S' T2) : LoopR k c body S S' (T1 + T2 + 2) := by
  intro m
  obtain ⟨s1, t1, e1, ⟨hs1, -⟩, ht1⟩ := hb ⟨((S k).head?, m), S⟩ rfl
  obtain ⟨⟨o1, m1⟩, S1'⟩ := s1
  change S1' = S1 at hs1
  subst hs1
  obtain ⟨m', t2, ht2, e2⟩ := hl m1
  exact ⟨m', t1 + 1 + t2 + 1, by omega, Eval.loop_true hc (Eval.seq e1 (Eval.peek _ _ _ _ _)) e2⟩

theorem LoopR.mono {k : K} {c : Sym → Bool} {body : KP K M} {S S' : K → List Sym} {T T' : ℕ}
    (h : LoopR k c body S S' T) (hT : T ≤ T') : LoopR k c body S S' T' := by
  intro m
  obtain ⟨m', t, ht, e⟩ := h m
  exact ⟨m', t, ht.trans hT, e⟩

theorem LoopR.congr {k : K} {c : Sym → Bool} {body : KP K M} {S S' S'' : K → List Sym} {T : ℕ}
    (h : LoopR k c body S S' T) (he : S' = S'') : LoopR k c body S S'' T := he ▸ h

theorem runs_whileTop {k : K} {c : Sym → Bool} {body : KP K M} {S S' : K → List Sym} {T : ℕ}
    (h : LoopR k c body S S' T) : Runs (whileTop k c body) S S' (fun _ => True) (T + 1) := by
  intro s hs
  obtain ⟨⟨o, m⟩, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨m', t, ht, e⟩ := h m
  exact ⟨_, 1 + t, Eval.seq (Eval.peek _ _ _ _ _) e, ⟨rfl, trivial⟩, by omega⟩

/-- Exact-state loop form of `whileTop k c body`. -/
def LoopM (k : K) (c : Sym → Bool) (body : KP K M) (m : M) (S : K → List Sym) (m' : M)
    (S' : K → List Sym) (T : ℕ) : Prop :=
  ∃ t, t ≤ T ∧ Eval [] (.loop (fun r => testO c r.1) (.seq body (peekO k)))
    ⟨((S k).head?, m), S⟩ ⟨((S' k).head?, m'), S'⟩ t

theorem LoopM.stop {k : K} {c : Sym → Bool} {body : KP K M} {m : M} {S : K → List Sym}
    (h : testO c (S k).head? = false) : LoopM k c body m S m S 1 :=
  ⟨1, le_rfl, Eval.loop_false h⟩

theorem LoopM.step {k : K} {c : Sym → Bool} {body : KP K M} {m m1 m' : M}
    {S S1 S' : K → List Sym} {T1 T2 : ℕ}
    (hc : testO c (S k).head? = true) (hb : RunsM body m S m1 S1 T1)
    (hl : LoopM k c body m1 S1 m' S' T2) : LoopM k c body m S m' S' (T1 + T2 + 2) := by
  obtain ⟨o1, t1, ht1, e1⟩ := hb ((S k).head?)
  obtain ⟨t2, ht2, e2⟩ := hl
  exact ⟨t1 + 1 + t2 + 1, by omega, Eval.loop_true hc (Eval.seq e1 (Eval.peek _ _ _ _ _)) e2⟩

theorem RunsM.of_eq {P : KP K M} {m m2 m' m2' : M}
    {S S2 S' S2' : K → List Sym} {T T2 : ℕ} (h : RunsM P m S m' S' T) (hm : m = m2) (hS : S = S2)
    (hm' : m' = m2') (hS' : S' = S2') (hT : T ≤ T2) : RunsM P m2 S2 m2' S2' T2 := by
  subst hm hS hm' hS'
  exact h.mono hT

theorem LoopM.mono {k : K} {c : Sym → Bool} {body : KP K M} {m m' : M} {S S' : K → List Sym}
    {T T' : ℕ} (h : LoopM k c body m S m' S' T) (hT : T ≤ T') : LoopM k c body m S m' S' T' := by
  obtain ⟨t, ht, e⟩ := h
  exact ⟨t, ht.trans hT, e⟩

theorem LoopM.congr {k : K} {c : Sym → Bool} {body : KP K M} {m m' : M} {S S' S'' : K → List Sym}
    {T : ℕ} (h : LoopM k c body m S m' S' T) (he : S' = S'') : LoopM k c body m S m' S'' T :=
  he ▸ h

theorem runsM_whileTop' {k : K} {c : Sym → Bool} {body : KP K M} {m m' : M}
    {S S' : K → List Sym} {T : ℕ} (h : LoopM k c body m S m' S' T) :
    RunsM (whileTop k c body) m S m' S' (T + 1) := by
  intro o
  obtain ⟨t, ht, e⟩ := h
  exact ⟨_, 1 + t, by omega, Eval.seq (Eval.peek _ _ _ _ _) e⟩

/-! ## Conversions and sequences -/

theorem runs_of_forall_runsM {P : KP K M} {S S' : K → List Sym} {T : ℕ}
    (h : ∀ m, ∃ m', RunsM P m S m' S' T) : Runs P S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨⟨o, m⟩, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨m', h'⟩ := h m
  obtain ⟨o', t, ht, e⟩ := h' o
  exact ⟨_, t, e, ⟨rfl, trivial⟩, ht⟩

theorem runs_of_runsM_all {P : KP K M} {S S' : K → List Sym} {T : ℕ}
    (h : ∀ m, RunsM P m S m S' T) : Runs P S S' (fun _ => True) T :=
  runs_of_forall_runsM fun m => ⟨m, h m⟩

/-- `forEachProg` with exact states. -/
theorem runsM_forEachProg {α : Type} (f : α → KP K M) :
    ∀ (l : List α) (m : ℕ → M) (S : ℕ → K → List Sym) (T : α → ℕ),
      (∀ (i : ℕ) (hi : i < l.length), RunsM (f l[i]) (m i) (S i) (m (i + 1)) (S (i + 1)) (T l[i])) →
      RunsM (forEachProg l f) (m 0) (S 0) (m l.length) (S l.length) ((l.map T).sum + 1)
  | [], m, S, T, _ => by simpa using RunsM.skip (m 0) (S 0)
  | a :: l, m, S, T, h => by
    have h0 := h 0 (by simp)
    have ih := runsM_forEachProg f l (fun i => m (i + 1)) (fun i => S (i + 1)) T
      (fun i hi => h (i + 1) (by simpa using hi))
    have := RunsM.seq h0 ih
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    refine (this.mono ?_)
    simp only [List.getElem_cons_zero]
    omega

end Loops

/-! ## Record movers -/

section Movers

variable {K M : Type}

/-- Move one record (bits, then `sep`) from `src` to `dst`; it arrives reversed. -/
def mvRec (src dst : K) : KP K M := lift (moveRec src dst)

/-- Move one reversed record (`sep`, then the bits reversed) from `src` to `dst`, restoring its
order. -/
def mvRev (src dst : K) : KP K M :=
  .seq (lift (Lib.popR src)) (.seq (lift (Lib.pushC dst .sep)) (lift (Lib.moveBlock src dst)))

/-- Move all records of a `.down` array from `src` to `dst` (orientation flips). -/
def mvArr (src dst : K) : KP K M := whileTop src isRecStart (mvRec src dst)

/-- Move everything above the first `mark` of `src` to `dst`, dropping the `mark`. -/
def rwd (src dst : K) : KP K M := lift (WP.W9comp.rewindTo src dst .mark)

theorem closed_mvRec (src dst : K) : (mvRec (M := M) src dst).Closed :=
  closed_lift (by simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, Lib.pushR, Lib.popR])

theorem closed_mvRev (src dst : K) : (mvRev (M := M) src dst).Closed := by
  refine ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.popR]),
    closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]), closed_lift ?_⟩
  simp [Prog.Closed, Prog.FreeBelow, Lib.moveBlock, Lib.moveBits, Lib.moveBitsBody, Lib.restoreR,
    Lib.pushR, Lib.popR, Lib.skip]

theorem closed_mvArr (src dst : K) : (mvArr (M := M) src dst).Closed :=
  closed_whileTop _ _ (closed_mvRec src dst)

theorem closed_rwd (src dst : K) : (rwd (M := M) src dst).Closed :=
  closed_lift (by simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody,
    Lib.pushR, Lib.popR])

variable [DecidableEq K]

theorem runsM_mvRec {src dst : K} (hne : src ≠ dst) (p : List Bool) (R : List Sym) (m : M)
    (S : K → List Sym) (hS : S src = recSyms p ++ R) :
    RunsM (mvRec src dst) m S m
      (Function.update (Function.update S src R) dst ((recSyms p).reverse ++ S dst))
      (3 * p.length + 3) := by
  have hd : ∀ x ∈ p.map Sym.bit, isDataSym x = true := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    rfl
  have hS' : S src = p.map Sym.bit ++ Sym.sep :: R := by
    rw [hS]
    simp [recSyms]
  have h := RunsM.ofLib (M := M)
    (fun o => ⟨_, _, le_rfl, moveRec_eval hne o (p.map Sym.bit) R S hd hS'⟩) m
  refine (h.congr ?_).mono (by simp)
  rw [recSyms_reverse, List.map_reverse]
  rfl

theorem runsM_mvRev {src dst : K} (hne : src ≠ dst) (p : List Bool) (R : List Sym)
    (hR : TermOK R) (m : M) (S : K → List Sym) (hS : S src = (recSyms p).reverse ++ R) :
    RunsM (mvRev src dst) m S m
      (Function.update (Function.update S src R) dst (recSyms p ++ S dst)) (3 * p.length + 6) := by
  rw [recSyms_reverse, List.cons_append] at hS
  have h1 := RunsM.pop src Sym.sep (p.reverse.map Sym.bit ++ R) m S hS
  have h2 := RunsM.push dst Sym.sep m (Function.update S src (p.reverse.map Sym.bit ++ R))
  set S2 := Function.update (Function.update S src (p.reverse.map Sym.bit ++ R)) dst
    (Sym.sep :: Function.update S src (p.reverse.map Sym.bit ++ R) dst) with hS2
  have hS2src : S2 src = p.reverse.map Sym.bit ++ R := by
    rw [hS2, Function.update_of_ne hne, Function.update_self]
  have h3 : RunsM (lift (Lib.moveBlock src dst)) m S2 m
      (Function.update (Function.update S2 src R) dst (p.reverse.reverse.map Sym.bit ++ S2 dst))
      (3 * p.reverse.length + 4) :=
    RunsM.ofLib (fun o => ⟨_, _, le_rfl, Lib.moveBlock_eval hne [] o p.reverse R S2 hR hS2src⟩) m
  refine ((h1.seq (h2.seq h3)).congr ?_).mono (by simp; omega)
  funext k
  simp only [hS2, Function.update_apply, List.reverse_reverse, recSyms]
  split_ifs <;> simp_all

theorem loopR_mvArr {src dst : K} (hne : src ≠ dst) (R : List Sym) (hR : BlkTerm R) :
    ∀ (v : List (List Bool)) (S : K → List Sym), S src = arrSyms v ++ R →
      LoopR src isRecStart (mvRec (M := M) src dst) S
        (Function.update (Function.update S src R) dst ((arrSyms v).reverse ++ S dst))
        (5 * vol v + 1)
  | [], S, hS => by
    have h : Function.update (Function.update S src R) dst ((arrSyms []).reverse ++ S dst) = S := by
      simp only [arrSyms_nil, List.nil_append] at hS
      rw [arrSyms_nil, List.reverse_nil, List.nil_append,
        show S dst = Function.update S src R dst from (Function.update_of_ne hne.symm _ _).symm,
        Function.update_eq_self, ← hS, Function.update_eq_self]
    rw [h]
    refine (LoopR.stop ?_).mono (by simp)
    simp only [arrSyms_nil, List.nil_append] at hS
    rw [hS]
    exact testO_recStart_of_blkTerm hR
  | p :: v, S, hS => by
    rw [arrSyms_cons, List.append_assoc] at hS
    have h1 := runs_of_runsM_all (fun m => runsM_mvRec (M := M) hne p (arrSyms v ++ R) m S hS)
    have ih := loopR_mvArr hne R hR v
      (Function.update (Function.update S src (arrSyms v ++ R)) dst ((recSyms p).reverse ++ S dst))
      (by rw [Function.update_of_ne hne, Function.update_self])
    have hc : testO isRecStart (S src).head? = true := by rw [hS]; exact testO_recStart p _
    refine ((LoopR.step hc h1 ih).mono ?_).congr ?_
    · rw [vol_cons]; omega
    · funext k
      simp only [Function.update_apply, arrSyms_cons, List.reverse_append, List.append_assoc]
      split_ifs <;> simp_all

theorem runs_mvArr {src dst : K} (hne : src ≠ dst) (v : List (List Bool)) (R : List Sym)
    (hR : BlkTerm R) (S : K → List Sym) (hS : S src = arrSyms v ++ R) :
    Runs (mvArr (M := M) src dst) S
      (Function.update (Function.update S src R) dst ((arrSyms v).reverse ++ S dst))
      (fun _ => True) (5 * vol v + 2) :=
  runs_whileTop (loopR_mvArr hne R hR v S hS)

theorem runsM_rwd {src dst : K} (hne : src ≠ dst) (L rest : List Sym) (hg : Sym.mark ∉ L)
    (m : M) (S : K → List Sym) (hS : S src = L ++ Sym.mark :: rest) :
    RunsM (rwd src dst) m S m (Function.update (Function.update S src rest) dst (L.reverse ++ S dst))
      (3 * L.length + 2) :=
  RunsM.ofLib (fun o => ⟨_, _, le_rfl, WP.W9comp.rewindTo_eval hne .mark o L rest S hg hS⟩) m

end Movers

end SubNLogN.Machine.K1.SMM
