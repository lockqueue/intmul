/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelDefs
import SubNLogN.Machine.Bridge.PrePostCall
import WP.W3s.Math

/-!
# C-core phase leaf, record-wise sign selection: machine gadgets (`LeafPhaseMaskSelKit.lean`)

**Scope (honest summary).** Generic programs (any stack type `K`, register `PReg` of
`Bridge/PrePostLoop.lean`) with proved `Runs` lemmas (exact final stacks, explicit costs), used by
the kernel of `MaskSelStmt`:
* records: `msMvRec` (move a record `bits ++ [sep]`, reversed), `msMvRecBack` (move a reversed
  record back, restoring it), `msDropRec`, and `msDropBits` (drop a bit block);
* `msPushAll` (push a static list);
* loops: `msCd` (count-down loop on a `natSyms` counter), `msU` (unary loop over a block of `0`
  bits, restored), `msB` (loop consuming a bit block, branching on each bit).
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability

variable {K : Type}

/-- Lift a `TMFw.Lib` program to `PReg` registers. -/
abbrev msLift (P : SProg K) : PProg K := P.liftRegs lensPO

/-- Do nothing (one step). -/
def msSkip : PProg K := .load id

/-- Move one record (`bits ++ [sep]`) from `src` onto `dst`: it arrives as `sep :: bits.reverse`. -/
def msMvRec (src dst : K) : PProg K := .seq (msLift (moveBlock src dst)) (msLift (moveSym src dst))

/-- Move one reversed record (`sep :: bits.reverse`) from `src` onto `dst`, restoring it. -/
def msMvRecBack (src dst : K) : PProg K :=
  .seq (msLift (moveSym src dst)) (msLift (moveBlock src dst))

/-- Drop the top bit block of `k`. -/
def msDropBits (k : K) : PProg K :=
  .seq (peekT k) (.loop (fun v => isBitO v.t) (.seq (popO k) (peekT k)))

/-- Drop one record (`bits ++ [sep]`) from `k`. -/
def msDropRec (k : K) : PProg K := .seq (msDropBits k) (popO k)

/-- Push a static list onto `k` (the head of the list ends on top). -/
def msPushAll (k : K) : List Sym → PProg K
  | [] => msSkip
  | x :: xs => .seq (msPushAll k xs) (msLift (pushC k x))

/-- Count-down loop: while the counter on `C` (`natSyms`) is nonzero, decrement it and run `body`. -/
def msCd (C U : K) (body : PProg K) : PProg K :=
  .seq (peekT C) (.loop (fun v => isBitO v.t) (.seq (.seq (msLift (decIfPos C U)) body) (peekT C)))

/-- Unary loop: once per bit of `F` (moved onto `F2`), run `body`; then move the bits back. -/
def msU (F F2 : K) (body : PProg K) : PProg K :=
  .seq (.seq (peekT F) (.loop (fun v => isBitO v.t)
    (.seq (.seq (msLift (moveSym F F2)) body) (peekT F)))) (msLift (moveBlock F2 F))

/-- Bit loop: pop the bits of `T` one by one, running `bodyT` or `bodyF`. -/
def msB (T : K) (bodyT bodyF : PProg K) : PProg K :=
  .seq (peekT T) (.loop (fun v => isBitO v.t)
    (.seq (.seq (popO T) (.ite (fun v => bitOf v.o) bodyT bodyF)) (peekT T)))

/-! ## Closedness -/

theorem closed_msSkip : (msSkip (K := K)).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, msSkip]

theorem closed_msLift {P : SProg K} (h : P.Closed) : (msLift P).Closed :=
  WP.W9comp.closed_liftRegs _ h

theorem closed_msPushAll (k : K) : ∀ l : List Sym, (msPushAll k l).Closed
  | [] => closed_msSkip
  | x :: xs => WP.W9comp.closed_seq (closed_msPushAll k xs)
      (closed_msLift (by simp [Prog.Closed, Prog.FreeBelow, pushC]))

theorem closed_peekT (k : K) : (peekT k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, peekT]

theorem closed_popO (k : K) : (popO k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, popO]

theorem closed_msDropBits (k : K) : (msDropBits k).Closed :=
  WP.W9comp.closed_seq (closed_peekT k) (WP.W9comp.closed_seq (closed_popO k) (closed_peekT k))

theorem closed_msDropRec (k : K) : (msDropRec k).Closed :=
  WP.W9comp.closed_seq (closed_msDropBits k) (closed_popO k)

theorem closed_moveSym' (src dst : K) : (moveSym src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveSym, popR, pushR]

theorem closed_moveBlock' (src dst : K) : (moveBlock src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR,
    skip]

theorem closed_msMvRec (src dst : K) : (msMvRec src dst).Closed :=
  WP.W9comp.closed_seq (closed_msLift (closed_moveBlock' src dst))
    (closed_msLift (closed_moveSym' src dst))

theorem closed_msMvRecBack (src dst : K) : (msMvRecBack src dst).Closed :=
  WP.W9comp.closed_seq (closed_msLift (closed_moveSym' src dst))
    (closed_msLift (closed_moveBlock' src dst))

theorem closed_msCd (C U : K) {body : PProg K} (hb : body.Closed) : (msCd C U body).Closed :=
  WP.W9comp.closed_seq (closed_peekT C) (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_msLift (closed_decIfPos C U)) hb) (closed_peekT C))

theorem closed_msU (F F2 : K) {body : PProg K} (hb : body.Closed) : (msU F F2 body).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_peekT F) (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_msLift (closed_moveSym' F F2)) hb) (closed_peekT F)))
    (closed_msLift (closed_moveBlock' F2 F))

theorem closed_msB (T : K) {bT bF : PProg K} (hT : bT.Closed) (hF : bF.Closed) :
    (msB T bT bF).Closed :=
  WP.W9comp.closed_seq (closed_peekT T) (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_popO T) ⟨hT, hF⟩) (closed_peekT T))

/-! ## `Runs` lemmas -/

section Runs

variable [DecidableEq K]

theorem runs_msSkip (S : K → List Sym) : Runs (msSkip (K := K)) S S (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v S, trivial, le_rfl⟩

theorem runs_popO (k : K) (x : Sym) (L : List Sym) (S : K → List Sym) (hS : S k = x :: L) :
    Runs (popO k) S (Function.update S k L) (fun v => v.o = some x) 1 := by
  refine Runs.of_eval fun v => ⟨{ v with o := some x }, 1, ?_, rfl, le_rfl⟩
  have h := Eval.pop (Γ := fun _ => Sym) [] k (fun v o => { v with o := o }) v S
  rw [hS] at h
  exact h

theorem runs_msMvRec {src dst : K} (hne : src ≠ dst) (p : List Bool) (L : List Sym)
    (S : K → List Sym) (hS : S src = recSyms p ++ L) :
    Runs (msMvRec src dst) S
      (Function.update (Function.update S src L) dst
        (Sym.sep :: (p.reverse.map Sym.bit ++ S dst)))
      (fun _ => True) (3 * p.length + 6) := by
  have hS' : S src = p.map Sym.bit ++ (Sym.sep :: L) := by rw [hS]; simp [recSyms]
  have h1 := runs_liftRegs lensPO (runs_moveBlock hne p (Sym.sep :: L) S (TermOK.cons rfl L) hS')
  have h2 := runs_liftRegs lensPO (runs_moveSym hne Sym.sep L
    (Function.update (Function.update S src (Sym.sep :: L)) dst (p.reverse.map Sym.bit ++ S dst))
    (by rw [Function.update_of_ne hne, Function.update_self]))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
    (fun _ _ => trivial) (by omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_msMvRecBack {src dst : K} (hne : src ≠ dst) (p : List Bool) (L : List Sym)
    (S : K → List Sym) (hL : TermOK L) (hS : S src = Sym.sep :: (p.reverse.map Sym.bit ++ L)) :
    Runs (msMvRecBack src dst) S
      (Function.update (Function.update S src L) dst (recSyms p ++ S dst))
      (fun _ => True) (3 * p.length + 6) := by
  have h1 := runs_liftRegs lensPO (runs_moveSym hne Sym.sep (p.reverse.map Sym.bit ++ L) S hS)
  have h2 := runs_liftRegs lensPO (runs_moveBlock hne p.reverse L
    (Function.update (Function.update S src (p.reverse.map Sym.bit ++ L)) dst (Sym.sep :: S dst))
    hL (by rw [Function.update_of_ne hne, Function.update_self]))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
    (fun _ _ => trivial) (by simp only [List.length_reverse]; omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all [recSyms]

theorem runs_msDropBits {k : K} (bs : List Bool) (L : List Sym) (S : K → List Sym)
    (hL : TermOK L) (hS : S k = bs.map Sym.bit ++ L) :
    Runs (msDropBits k) S (Function.update S k L) (fun _ => True) (3 * bs.length + 2) := by
  let st : List Bool → List Bool → K → List Sym := fun _ rest =>
    Function.update S k (rest.map Sym.bit ++ L)
  have h0 : st [] bs = S := by
    simp only [st]
    rw [← hS, Function.update_eq_self]
  have hw := runs_while (pk := peekT k) (body := popO k) (c := fun v => isBitO v.t) st 1
    (fun _ _ _ => 1)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT k (st done rest)) (fun v hv => ?_) le_rfl
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      simp only [st, Function.update_self]
      rcases rest with _ | ⟨x, rest⟩
      · simp [isBitO_of_termOK hL]
      · simp)
    (fun done x rest => by
      refine WP.W9comp.runs_mono (WP.W9comp.runs_congr
        (runs_popO k (Sym.bit x) (rest.map Sym.bit ++ L) (st done (x :: rest)) (by simp [st])) ?_)
        (fun _ _ => trivial) le_rfl
      simp [st])
    bs []
  rw [h0] at hw
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw ?_) (fun _ _ => trivial) ?_
  · simp [st]
  · have := whileCost_const 1 1 (fun _ _ _ => 1) (fun _ _ _ => le_rfl) bs []
    omega

theorem runs_msDropRec {k : K} (p : List Bool) (L : List Sym) (S : K → List Sym)
    (hS : S k = recSyms p ++ L) :
    Runs (msDropRec k) S (Function.update S k L) (fun _ => True) (3 * p.length + 3) := by
  have hS' : S k = p.map Sym.bit ++ (Sym.sep :: L) := by rw [hS]; simp [recSyms]
  have h1 := runs_msDropBits p (Sym.sep :: L) S (TermOK.cons rfl L) hS'
  have h2 := runs_popO k Sym.sep L (Function.update S k (Sym.sep :: L)) (by simp)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
    (fun _ _ => trivial) (by omega)
  simp

theorem runs_msPushAll (k : K) : ∀ (l : List Sym) (S : K → List Sym),
    Runs (msPushAll k l) S (Function.update S k (l ++ S k)) (fun _ => True) (l.length + 1)
  | [], S => by
    have h := runs_msSkip (K := K) S
    simp only [List.nil_append, Function.update_eq_self, List.length_nil, zero_add]
    exact h
  | x :: xs, S => by
    have h1 := runs_msPushAll k xs S
    have h2 := runs_liftRegs lensPO (runs_pushC k x (Function.update S k (xs ++ S k)))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
      (fun _ _ => trivial) (by simp)
    simp

theorem runs_msCd {C U : K} (hCU : C ≠ U) (body : PProg K) (RC : List Sym) (hRC : TermOK RC)
    (st : ℕ → K → List Sym) (B : ℕ)
    (hbody : ∀ j m, Runs body (Function.update (st j) C (natSyms m ++ RC))
        (Function.update (st (j + 1)) C (natSyms m ++ RC)) (fun _ => True) B)
    (n : ℕ) :
    Runs (msCd C U body) (Function.update (st 0) C (natSyms n ++ RC))
      (Function.update (st n) C RC) (fun _ => True) (n * (B + 8 * bitLen n + 13) + 2) := by
  let st' : List Unit → List Unit → K → List Sym := fun done rest =>
    Function.update (st done.length) C (natSyms rest.length ++ RC)
  have hw := runs_while (pk := peekT C) (body := .seq (msLift (decIfPos C U)) body)
    (c := fun v => isBitO v.t) st' 1 (fun _ _ rest => 8 * bitLen (rest.length + 1) + 10 + B)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT C (st' done rest)) (fun v hv => ?_) le_rfl
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      simp only [st', Function.update_self]
      rw [isBitO_natSyms _ hRC]
      cases rest <;> simp)
    (fun done x rest => by
      have h1 := runs_liftRegs lensPO (runs_decIfPos hCU (rest.length + 1) RC
        (st' done (x :: rest)) hRC (by simp [st']))
      have h2 := hbody done.length rest.length
      have e1 : Function.update (st' done (x :: rest)) C (natSyms (rest.length + 1 - 1) ++ RC) =
          Function.update (st done.length) C (natSyms rest.length ++ RC) := by
        simp [st']
      have e2 : Function.update (st (done.length + 1)) C (natSyms rest.length ++ RC) =
          st' (done ++ [x]) rest := by
        simp [st']
      exact WP.W9comp.runs_congr (WP.W9comp.runs_seq (WP.W9comp.runs_congr h1 e1) h2) e2)
    (List.replicate n ()) []
  have h0 : st' [] (List.replicate n ()) = Function.update (st 0) C (natSyms n ++ RC) := by
    simp [st']
  have h1 : st' ([] ++ List.replicate n ()) [] = Function.update (st n) C RC := by
    simp [st', natSyms, encodeNat_zero]
  rw [h0, h1] at hw
  refine WP.W9comp.runs_mono hw (fun _ _ => trivial) ?_
  have hc := whileCost_le_traj 1 (8 * bitLen n + 10 + B)
    (fun (_ : List Unit) (_ : Unit) (rest : List Unit) => 8 * bitLen (rest.length + 1) + 10 + B)
    (List.replicate n ()) (fun done x rest h => by
      have hl : rest.length + 1 ≤ n := by
        have := congrArg List.length h
        simp at this
        omega
      have := TMFw.W3s.bitLen_mono hl
      omega)
    (List.replicate n ()) [] (by simp)
  simp only [List.length_replicate] at hc
  nlinarith

theorem runs_msU {F F2 : K} (hne : F ≠ F2) (body : PProg K) (RF : List Sym) (hRF : TermOK RF)
    (st : ℕ → K → List Sym) (B : ℕ)
    (hbody : ∀ j a b, Runs body
        (Function.update (Function.update (st j) F (List.replicate a (Sym.bit false) ++ RF)) F2
          (List.replicate b (Sym.bit false)))
        (Function.update (Function.update (st (j + 1)) F (List.replicate a (Sym.bit false) ++ RF))
          F2 (List.replicate b (Sym.bit false))) (fun _ => True) B)
    (f : ℕ) :
    Runs (msU F F2 body)
      (Function.update (Function.update (st 0) F (List.replicate f (Sym.bit false) ++ RF)) F2 [])
      (Function.update (Function.update (st f) F (List.replicate f (Sym.bit false) ++ RF)) F2 [])
      (fun _ => True) (f * (B + 4) + 3 * f + 6) := by
  let st' : List Unit → List Unit → K → List Sym := fun done rest =>
    Function.update (Function.update (st done.length) F
      (List.replicate rest.length (Sym.bit false) ++ RF)) F2
      (List.replicate done.length (Sym.bit false))
  have hw := runs_while (pk := peekT F) (body := .seq (msLift (moveSym F F2)) body)
    (c := fun v => isBitO v.t) st' 1 (fun _ _ _ => 2 + B)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT F (st' done rest)) (fun v hv => ?_) le_rfl
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      simp only [st']
      rw [Function.update_of_ne hne, Function.update_self]
      rcases rest with _ | ⟨x, rest⟩
      · simp [isBitO_of_termOK hRF]
      · simp [List.replicate_succ])
    (fun done x rest => by
      have h1 := runs_liftRegs lensPO (runs_moveSym hne (Sym.bit false)
        (List.replicate rest.length (Sym.bit false) ++ RF) (st' done (x :: rest))
        (by simp only [st']; rw [Function.update_of_ne hne, Function.update_self]
            simp [List.replicate_succ]))
      have h2 := hbody done.length rest.length (done.length + 1)
      have e1 : Function.update (Function.update (st' done (x :: rest)) F
            (List.replicate rest.length (Sym.bit false) ++ RF)) F2
            (Sym.bit false :: st' done (x :: rest) F2) =
          Function.update (Function.update (st done.length) F
            (List.replicate rest.length (Sym.bit false) ++ RF)) F2
            (List.replicate (done.length + 1) (Sym.bit false)) := by
        funext k
        simp only [st', Function.update_apply]
        split_ifs <;> simp_all [List.replicate_succ]
      have e2 : Function.update (Function.update (st (done.length + 1)) F
            (List.replicate rest.length (Sym.bit false) ++ RF)) F2
            (List.replicate (done.length + 1) (Sym.bit false)) = st' (done ++ [x]) rest := by
        simp [st']
      exact WP.W9comp.runs_congr (WP.W9comp.runs_seq (WP.W9comp.runs_congr h1 e1) h2) e2)
    (List.replicate f ()) []
  have h0 : st' [] (List.replicate f ()) =
      Function.update (Function.update (st 0) F (List.replicate f (Sym.bit false) ++ RF)) F2 [] := by
    simp [st']
  rw [h0] at hw
  have hS1 : st' ([] ++ List.replicate f ()) [] F2 = (List.replicate f false).map Sym.bit ++ [] := by
    simp [st', List.map_replicate]
  have h3 := runs_liftRegs lensPO (runs_moveBlock hne.symm (List.replicate f false) []
    (st' ([] ++ List.replicate f ()) []) TermOK.nil hS1)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hw h3) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    simp only [st', Function.update_apply]
    split_ifs <;> simp_all [List.map_replicate]
  · have hc := whileCost_const 1 (2 + B) (fun (_ : List Unit) (_ : Unit) (_ : List Unit) => 2 + B)
      (fun _ _ _ => le_rfl) (List.replicate f ()) []
    simp only [List.length_replicate] at hc ⊢
    nlinarith

theorem runs_msB {T : K} (bodyT bodyF : PProg K) (RT : List Sym) (hRT : TermOK RT)
    (st : List Bool → K → List Sym) (B : ℕ)
    (hbody : ∀ (done : List Bool) (b : Bool) (rest : List Bool), Runs (if b then bodyT else bodyF)
        (Function.update (st done) T (rest.map Sym.bit ++ RT))
        (Function.update (st (done ++ [b])) T (rest.map Sym.bit ++ RT)) (fun _ => True) B)
    (bs : List Bool) :
    Runs (msB T bodyT bodyF) (Function.update (st []) T (bs.map Sym.bit ++ RT))
      (Function.update (st bs) T RT) (fun _ => True) (bs.length * (B + 4) + 2) := by
  let st' : List Bool → List Bool → K → List Sym := fun done rest =>
    Function.update (st done) T (rest.map Sym.bit ++ RT)
  have hw := runs_while (pk := peekT T) (body := .seq (popO T) (.ite (fun v => bitOf v.o) bodyT bodyF))
    (c := fun v => isBitO v.t) st' 1 (fun _ _ _ => 1 + (B + 1))
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekT T (st' done rest)) (fun v hv => ?_) le_rfl
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      simp only [st', Function.update_self]
      rcases rest with _ | ⟨x, rest⟩
      · simp [isBitO_of_termOK hRT]
      · simp)
    (fun done b rest => by
      have h1 := runs_popO T (Sym.bit b) (rest.map Sym.bit ++ RT) (st' done (b :: rest))
        (by simp [st'])
      have h1' : Runs (popO T) (st' done (b :: rest))
          (Function.update (st done) T (rest.map Sym.bit ++ RT)) (fun v => bitOf v.o = b) 1 :=
        WP.W9comp.runs_mono (WP.W9comp.runs_congr h1 (by simp [st'])) (fun v hv => by
          rw [hv]; rfl) le_rfl
      have hb := hbody done b rest
      exact runs_seq_ite h1'
        (fun h => by subst h; simpa using hb) (fun h => by subst h; simpa using hb))
    bs []
  have h0 : st' [] bs = Function.update (st []) T (bs.map Sym.bit ++ RT) := rfl
  rw [h0] at hw
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hw (by simp [st'])) (fun _ _ => trivial) ?_
  have hc := whileCost_const 1 (1 + (B + 1)) (fun (_ : List Bool) (_ : Bool) (_ : List Bool) => 1 + (B + 1))
    (fun _ _ _ => le_rfl) bs []
  nlinarith

/-! ## Loops with step hypotheses along the trajectory only -/

theorem triple_whileT_aux {σ : Type} {pk body : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {α : Type} (all : List α) (st : List α → List α → K → List Sym) (Tp : ℕ)
    (Tb : List α → α → List α → ℕ)
    (hpk : ∀ done rest, done ++ rest = all →
      Runs pk (st done rest) (st done rest) (fun v => c v = !rest.isEmpty) Tp)
    (hstep : ∀ done x rest, done ++ x :: rest = all →
      Runs body (st done (x :: rest)) (st (done ++ [x]) rest) (fun _ => True) (Tb done x rest)) :
    ∀ rest done, done ++ rest = all →
      Triple [] (fun s => s.stk = st done rest ∧ c s.var = !rest.isEmpty)
        (.loop c (.seq body pk)) (fun s => s.stk = st (done ++ rest) [] ∧ True)
        (whileCost Tp Tb done rest)
  | [], done, _ => by
    rintro ⟨v, S⟩ ⟨hS, hc⟩
    refine ⟨⟨v, S⟩, 1, Eval.loop_false (by simpa using hc), ⟨?_, trivial⟩, le_refl _⟩
    simpa using hS
  | x :: rest, done, hall => by
    rintro ⟨v, S⟩ ⟨hS, hc⟩
    have hall' : (done ++ [x]) ++ rest = all := by simpa using hall
    have h12 := WP.W9comp.runs_seq (hstep done x rest hall) (hpk (done ++ [x]) rest hall')
    obtain ⟨s1, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := h12 ⟨v, S⟩ hS
    obtain ⟨s2, t2, e2, ⟨hs2, -⟩, ht2⟩ :=
      triple_whileT_aux all st Tp Tb hpk hstep rest (done ++ [x]) hall' s1 ⟨hs1, hq1⟩
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true (by simpa using hc) e1 e2, ⟨?_, trivial⟩, ?_⟩
    · rw [hs2]
      simp
    · simp only [whileCost]
      omega

/-- **`while` over a list**, with hypotheses only along the trajectory `all`. -/
theorem runs_whileT {σ : Type} {pk body : Prog K (fun _ => Sym) σ} {c : σ → Bool} {α : Type}
    (all : List α) (st : List α → List α → K → List Sym) (Tp : ℕ) (Tb : List α → α → List α → ℕ)
    (hpk : ∀ done rest, done ++ rest = all →
      Runs pk (st done rest) (st done rest) (fun v => c v = !rest.isEmpty) Tp)
    (hstep : ∀ done x rest, done ++ x :: rest = all →
      Runs body (st done (x :: rest)) (st (done ++ [x]) rest) (fun _ => True) (Tb done x rest)) :
    Runs (.seq pk (.loop c (.seq body pk))) (st [] all) (st all []) (fun _ => True)
      (Tp + whileCost Tp Tb [] all) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := hpk [] all (by simp) s hs
  obtain ⟨s2, t2, e2, hq2, ht2⟩ :=
    triple_whileT_aux all st Tp Tb hpk hstep all [] (by simp) s1 ⟨hs1, hq1⟩
  refine ⟨s2, t1 + t2, Eval.seq e1 e2, ?_, by omega⟩
  simpa using hq2

/-- Count-down loop with the body hypothesis only for the actual iterations (`j < n`, counter
value `n - (j + 1)` during iteration `j`). -/
theorem runs_msCdT {C U : K} (hCU : C ≠ U) (body : PProg K) (RC : List Sym) (hRC : TermOK RC)
    (st : ℕ → K → List Sym) (n B : ℕ)
    (hbody : ∀ j, j < n → Runs body (Function.update (st j) C (natSyms (n - (j + 1)) ++ RC))
        (Function.update (st (j + 1)) C (natSyms (n - (j + 1)) ++ RC)) (fun _ => True) B) :
    Runs (msCd C U body) (Function.update (st 0) C (natSyms n ++ RC))
      (Function.update (st n) C RC) (fun _ => True) (n * (B + 8 * bitLen n + 13) + 2) := by
  let st' : List Unit → List Unit → K → List Sym := fun done rest =>
    Function.update (st done.length) C (natSyms rest.length ++ RC)
  have hw := runs_whileT (pk := peekT C) (body := .seq (msLift (decIfPos C U)) body)
    (c := fun v => isBitO v.t) (List.replicate n ()) st' 1
    (fun _ _ rest => 8 * bitLen (rest.length + 1) + 10 + B)
    (fun done rest _ => by
      refine WP.W9comp.runs_mono (runs_peekT C (st' done rest)) (fun v hv => ?_) le_rfl
      show isBitO v.t = !rest.isEmpty
      rw [hv]
      simp only [st', Function.update_self]
      rw [isBitO_natSyms _ hRC]
      cases rest <;> simp)
    (fun done x rest hall => by
      have hlen : done.length + rest.length + 1 = n := by
        have := congrArg List.length hall
        simp at this
        omega
      have h1 := runs_liftRegs lensPO (runs_decIfPos hCU (rest.length + 1) RC
        (st' done (x :: rest)) hRC (by simp [st']))
      have h2 := hbody done.length (by omega)
      have e1 : Function.update (st' done (x :: rest)) C (natSyms (rest.length + 1 - 1) ++ RC) =
          Function.update (st done.length) C (natSyms (n - (done.length + 1)) ++ RC) := by
        rw [show rest.length + 1 - 1 = n - (done.length + 1) by omega]
        simp [st']
      have e2 : Function.update (st (done.length + 1)) C (natSyms (n - (done.length + 1)) ++ RC) =
          st' (done ++ [x]) rest := by
        rw [show n - (done.length + 1) = rest.length by omega]
        simp [st']
      exact WP.W9comp.runs_congr (WP.W9comp.runs_seq (WP.W9comp.runs_congr h1 e1) h2) e2)
  have h0 : st' [] (List.replicate n ()) = Function.update (st 0) C (natSyms n ++ RC) := by
    simp [st']
  have h1 : st' (List.replicate n ()) [] = Function.update (st n) C RC := by
    simp [st', natSyms, encodeNat_zero]
  rw [h0, h1] at hw
  refine WP.W9comp.runs_mono hw (fun _ _ => trivial) ?_
  have hc := whileCost_le_traj 1 (8 * bitLen n + 10 + B)
    (fun (_ : List Unit) (_ : Unit) (rest : List Unit) => 8 * bitLen (rest.length + 1) + 10 + B)
    (List.replicate n ()) (fun done x rest h => by
      have hl : rest.length + 1 ≤ n := by
        have := congrArg List.length h
        simp at this
        omega
      have := TMFw.W3s.bitLen_mono hl
      omega)
    (List.replicate n ()) [] (by simp)
  simp only [List.length_replicate] at hc
  nlinarith

end Runs

end SubNLogN.Machine.CCore.PhaseMaskAux
