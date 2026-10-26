/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractSetup

/-!
# Lemma A.9 extraction: the setup phase, proved (`Machine/AppC/C7ExtractSetupProof.lean`)

**Scope.** `c7XSetup_holds : C7XSetupStmt` (`Machine/AppC/C7ExtractSetup.lean`),
proved (no `sorry`) for every arithmetic kit `xk`. Helpers live in the namespace
`SubNLogN.Machine.AppC.C7SetupAux`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

Program (`setupProg`): phase A moves the array record by record onto `T` above a `sep`, counting
the records on `cM` (`K1.moveRec`, `Lib.inc`); phase B counts the bits of a copy of `M`, giving
`A = Nat.size M` on `cA` and `Ac`; phase C builds the constants (`1, 10, 11` bit by bit;
`f·K` and `f - 1` with the kit; `2^e` by a countdown of `e` zero bits above a one; `2^K`, `2^{ρ+1}`
by one more zero bit); phase D pushes the tags on `H` and `Bk`. Every work stack used as a
temporary is restored.
-/

namespace SubNLogN.Machine.AppC.C7SetupAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus
  SubNLogN.Machine.AppC.C7ExtractAux

/-! ## 1. Phases A and B -/

section Progs

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

/-- One record: move it onto `T`, count it on `cM`, peek at the next record. -/
def moveBody : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq ((moveRec sArr (wk .T)).liftRegs xk.lw)
    (.seq ((inc (wk .cM) (wk .u1)).liftRegs xk.lw) (peekW xk sArr))

/-- Phase A: the array onto `T` (above a `sep`), the record count on `cM`. -/
def phaseA : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk (wk .T) Sym.sep) (.seq (pushW xk (wk .cM) Sym.mark)
    (.seq (peekW xk sArr) (.loop (fun r => SubNLogN.Machine.K1.isRecTop (xk.lw.get r))
      (moveBody xk))))

/-- One bit of `M`: pop it, count it on `cA`, peek at the next one. -/
def sizeBody : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (popW xk (wk .g1)) (.seq ((inc (wk .cA) (wk .u1)).liftRegs xk.lw) (peekW xk (wk .g1)))

/-- Phase B: `A = Nat.size M` on `cA` and on `Ac`. -/
def phaseB : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk (wk .cA) Sym.mark) (.seq (pushW xk (wk .g1) Sym.mark)
    (.seq (cpT xk (wk .cM) (wk .g1)) (.seq (peekW xk (wk .g1))
      (.seq (.loop (fun r => optIsBit (xk.lw.get r)) (sizeBody xk))
        (.seq (popW xk (wk .g1)) (.seq (pushW xk sAc Sym.mark) (cpT xk (wk .cA) sAc)))))))

theorem closed_moveRecL : ((moveRec (sArr : XK E') (wk .T)).liftRegs xk.lw).Closed :=
  WP.W9comp.closed_liftRegs xk.lw (by simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody,
    popR, pushR])

theorem closed_incL (k t : XK E') : ((inc k t).liftRegs xk.lw).Closed :=
  WP.W9comp.closed_liftRegs xk.lw (by simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop,
    scanBody, pushC, popR, restoreR, pushR, skip, moveBits, moveBitsBody])

theorem closed_phaseA : (phaseA xk).Closed :=
  ⟨closed_pushW xk _ _, closed_pushW xk _ _, closed_peekW xk _,
    ⟨closed_moveRecL xk, closed_incL xk _ _, closed_peekW xk _⟩⟩

theorem closed_phaseB : (phaseB xk).Closed :=
  ⟨closed_pushW xk _ _, closed_pushW xk _ _, closed_copyW xk _ _ _, closed_peekW xk _,
    ⟨closed_popW xk _, closed_incL xk _ _, closed_peekW xk _⟩, closed_popW xk _,
    closed_pushW xk _ _, closed_copyW xk _ _ _⟩

end Progs

/-! ## 2. Update helpers -/

@[simp] theorem natSyms_zero_s : natSyms 0 = [] := rfl

theorem upd3_congr {K : Type} [DecidableEq K] {f g : K → List Sym} {a b c : K}
    {va vb vc : List Sym} (h : ∀ k, k ≠ a → k ≠ b → k ≠ c → f k = g k) :
    Function.update (Function.update (Function.update f a va) b vb) c vc =
      Function.update (Function.update (Function.update g a va) b vb) c vc := by
  funext k
  by_cases hc : k = c
  · subst hc
    simp
  · by_cases hb : k = b
    · subst hb
      simp [hc]
    · by_cases ha : k = a
      · subst ha
        simp [hc, hb]
      · simp [ha, hb, hc, h k ha hb hc]

theorem upd2_congr {K : Type} [DecidableEq K] {f g : K → List Sym} {a b : K}
    {va vb : List Sym} (h : ∀ k, k ≠ a → k ≠ b → f k = g k) :
    Function.update (Function.update f a va) b vb =
      Function.update (Function.update g a va) b vb := by
  funext k
  by_cases hb : k = b
  · subst hb
    simp
  · by_cases ha : k = a
    · subst ha
      simp [hb]
    · simp [ha, hb, h k ha hb]

/-! ## 3. Phase A: the move loop -/

section PhaseA

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

/-- The state of phase A after `x` records (`vs` still on the array stack). -/
def stA (S : XK E' → List Sym) (w : List (List Bool)) (rest : List Sym) (x : ℕ)
    (vs : List (List Bool)) (_ : Unit) : XK E' → List Sym :=
  Function.update (Function.update (Function.update S sArr (SubNLogN.Machine.arrSyms vs ++ rest))
    (wk .T) ((SubNLogN.Machine.arrSyms (w.take x)).reverse ++ Sym.sep :: S (wk .T))) (wk .cM)
    (natSyms x ++ Sym.mark :: S (wk .cM))

theorem stepA (S : XK E' → List Sym) (w : List (List Bool)) (rest : List Sym) (x : ℕ)
    (a : List Bool) (vs : List (List Bool)) (g : Unit) (hok : a :: vs = w.drop x) :
    Triple [] (fun s => s.stk = stA S w rest x (a :: vs) g ∧
        xk.lw.get s.var = (SubNLogN.Machine.arrSyms (a :: vs) ++ rest).head?) (moveBody xk)
      (fun s => s.stk = stA S w rest (x + 1) vs g ∧
        xk.lw.get s.var = (SubNLogN.Machine.arrSyms vs ++ rest).head?)
      (3 * (a.map Sym.bit).length + 3 + (6 * ones (encodeNat x) + 9 + 1)) := by
  have hx : x < w.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hok
    exact List.cons_ne_nil _ _ hok
  have hwx : w[x] = a := by
    rw [List.drop_eq_getElem_cons hx] at hok
    exact (List.cons.inj hok).1.symm
  have hT : (SubNLogN.Machine.arrSyms (w.take (x + 1))).reverse ++ Sym.sep :: S (wk .T) =
      Sym.sep :: ((a.map Sym.bit).reverse ++ stA S w rest x (a :: vs) g (wk .T)) := by
    rw [rev_arr_take_succ w x hx, hwx]
    simp [stA]
  have hS1 : stA S w rest x (a :: vs) g sArr =
      a.map Sym.bit ++ Sym.sep :: (SubNLogN.Machine.arrSyms vs ++ rest) := by
    simp [stA, SubNLogN.Machine.K1.arrSyms_cons, SubNLogN.Machine.recSyms]
  have hd : ∀ y ∈ a.map Sym.bit, isDataSym y = true := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨b, -, rfl⟩ := hy
    rfl
  have r1 := SubNLogN.Machine.K1.runs_wk_moveRec xk.lw (src := sArr) (dst := wk .T) (by simp)
    (a.map Sym.bit) (SubNLogN.Machine.arrSyms vs ++ rest) (stA S w rest x (a :: vs) g) hd hS1
  have r2 := SubNLogN.Machine.K1.runs_wk_inc xk.lw (k := wk .cM) (t := wk .u1) (by simp) x
    (Sym.mark :: S (wk .cM))
    (Function.update (Function.update (stA S w rest x (a :: vs) g) sArr
      (SubNLogN.Machine.arrSyms vs ++ rest)) (wk .T)
      (Sym.sep :: ((a.map Sym.bit).reverse ++ stA S w rest x (a :: vs) g (wk .T))))
    (termOK_mark _) (by simp [stA])
  have heq : Function.update (Function.update (Function.update (stA S w rest x (a :: vs) g) sArr
      (SubNLogN.Machine.arrSyms vs ++ rest)) (wk .T)
      (Sym.sep :: ((a.map Sym.bit).reverse ++ stA S w rest x (a :: vs) g (wk .T)))) (wk .cM)
      (natSyms (x + 1) ++ Sym.mark :: S (wk .cM)) = stA S w rest (x + 1) vs g := by
    rw [← hT]
    unfold stA
    exact upd3_congr (fun k h1 h2 h3 => by simp [h1, h2, h3])
  have r3 := RunsIn.iff_runs.mp (runsIn_peekW xk sArr (stA S w rest (x + 1) vs g))
  refine Triple.conseq (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (WP.W9comp.runs_congr r2 heq)
    r3)) (fun s hs => hs.1) (fun s hs => ⟨hs.1, by rw [hs.2]; simp [stA]⟩) le_rfl

/-- **Phase A.** -/
theorem runs_phaseA (S : XK E' → List Sym) (w : List (List Bool)) (rest : List Sym)
    (hrest : BlkTerm rest) (hS : S sArr = SubNLogN.Machine.arrSyms w ++ rest) :
    Runs (phaseA xk) S
      (Function.update (Function.update (Function.update S sArr rest) (wk .T)
        ((SubNLogN.Machine.arrSyms w).reverse ++ Sym.sep :: S (wk .T))) (wk .cM)
        (natSyms w.length ++ Sym.mark :: S (wk .cM))) (fun _ => True)
      (1 + (1 + (1 + SubNLogN.Machine.K1.loopB
        (fun x a => 3 * (a.map Sym.bit).length + 3 + (6 * ones (encodeNat x) + 9 + 1)) 0 w))) := by
  have hloop := SubNLogN.Machine.K1.triple_loop_list (body := moveBody xk)
    (c := fun r => SubNLogN.Machine.K1.isRecTop (xk.lw.get r))
    (stA S w rest) (fun vs r => xk.lw.get r = (SubNLogN.Machine.arrSyms vs ++ rest).head?)
    (fun _ _ g => g)
    (fun x a => 3 * (a.map Sym.bit).length + 3 + (6 * ones (encodeNat x) + 9 + 1))
    (fun x vs => vs = w.drop x)
    (fun x a vs h => by
      have h2 := congrArg List.tail h
      simpa [List.tail_drop] using h2)
    (fun r hr => by rw [hr]; exact SubNLogN.Machine.K1.isRecTop_nil hrest)
    (fun a vs r hr => by rw [hr]; exact SubNLogN.Machine.K1.isRecTop_cons a vs rest)
    (fun x a vs g hok => stepA xk S w rest x a vs g hok) w 0 () (by simp)
  have h0 : Function.update (Function.update S (wk .T) (Sym.sep :: S (wk .T))) (wk .cM)
      (Sym.mark :: Function.update S (wk .T) (Sym.sep :: S (wk .T)) (wk .cM)) =
      stA S w rest 0 w () := by
    funext k
    by_cases h1 : k = wk .cM
    · subst h1
      simp [stA]
    · by_cases h2 : k = wk .T
      · subst h2
        simp [stA, SubNLogN.Machine.arrSyms, blk]
      · by_cases h3 : k = sArr
        · subst h3
          simp [stA, hS]
        · simp [stA, h1, h2, h3]
  have r1 := runs_pushW xk (wk .T) Sym.sep S
  have r2 := runs_pushW xk (wk .cM) Sym.mark (Function.update S (wk .T) (Sym.sep :: S (wk .T)))
  have r3 := RunsIn.iff_runs.mp (runsIn_peekW xk sArr (stA S w rest 0 w ()))
  have hPL : Runs (.seq (peekW xk sArr) (.loop (fun r => SubNLogN.Machine.K1.isRecTop
      (xk.lw.get r)) (moveBody xk))) (stA S w rest 0 w ())
      (Function.update (Function.update (Function.update S sArr rest) (wk .T)
        ((SubNLogN.Machine.arrSyms w).reverse ++ Sym.sep :: S (wk .T))) (wk .cM)
        (natSyms w.length ++ Sym.mark :: S (wk .cM))) (fun _ => True)
      (1 + SubNLogN.Machine.K1.loopB
        (fun x a => 3 * (a.map Sym.bit).length + 3 + (6 * ones (encodeNat x) + 9 + 1)) 0 w) :=
    Triple.seq (Triple.post r3 (fun s hs => ⟨hs.1, by rw [hs.2]; simp [stA]⟩))
      (Triple.post hloop (fun s hs => ⟨by rw [hs]; simp [stA, SubNLogN.Machine.arrSyms, blk],
        trivial⟩))
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (WP.W9comp.runs_congr r2 h0) hPL)

end PhaseA

/-! ## 4. Phase B: the bit length of `M` -/

section PhaseB

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

/-- The state of phase B after `x` bits (`vs` still on `g1`). -/
def stB (S : XK E' → List Sym) (x : ℕ) (vs : List Bool) (_ : Unit) : XK E' → List Sym :=
  Function.update (Function.update S (wk .g1) (vs.map Sym.bit ++ Sym.mark :: S (wk .g1))) (wk .cA)
    (natSyms x ++ Sym.mark :: S (wk .cA))

theorem stepB (S : XK E' → List Sym) (x : ℕ) (a : Bool) (vs : List Bool) (g : Unit) :
    Triple [] (fun s => s.stk = stB S x (a :: vs) g ∧
        xk.lw.get s.var = ((a :: vs).map Sym.bit ++ Sym.mark :: S (wk .g1)).head?) (sizeBody xk)
      (fun s => s.stk = stB S (x + 1) vs g ∧
        xk.lw.get s.var = (vs.map Sym.bit ++ Sym.mark :: S (wk .g1)).head?)
      (1 + (6 * ones (encodeNat x) + 9 + 1)) := by
  have r1 := runs_popW_cons xk (wk .g1) (stB S x (a :: vs) g) (Sym.bit a)
    (vs.map Sym.bit ++ Sym.mark :: S (wk .g1)) (by simp [stB])
  have r2 := SubNLogN.Machine.K1.runs_wk_inc xk.lw (k := wk .cA) (t := wk .u1) (by simp) x
    (Sym.mark :: S (wk .cA))
    (Function.update (stB S x (a :: vs) g) (wk .g1) (vs.map Sym.bit ++ Sym.mark :: S (wk .g1)))
    (termOK_mark _) (by simp [stB])
  have heq : Function.update (Function.update (stB S x (a :: vs) g) (wk .g1)
      (vs.map Sym.bit ++ Sym.mark :: S (wk .g1))) (wk .cA)
      (natSyms (x + 1) ++ Sym.mark :: S (wk .cA)) = stB S (x + 1) vs g := by
    unfold stB
    exact upd2_congr (fun k h1 h2 => by simp [h1, h2])
  have r3 := RunsIn.iff_runs.mp (runsIn_peekW xk (wk .g1) (stB S (x + 1) vs g))
  refine Triple.conseq (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (WP.W9comp.runs_congr r2 heq)
    r3)) (fun s hs => hs.1) (fun s hs => ⟨hs.1, by rw [hs.2]; simp [stB]⟩) le_rfl

theorem length_encodeNat_size (M : ℕ) : (encodeNat M).length = Nat.size M := by
  rw [← bitLen_eq_size]
  rfl

/-- **Phase B.** -/
theorem runs_phaseB (S : XK E' → List Sym) (M : ℕ) (C0 : List Sym)
    (hM : S (wk .cM) = natSyms M ++ Sym.mark :: C0) :
    Runs (phaseB xk) S
      (Function.update (Function.update S (wk .cA) (natSyms (Nat.size M) ++ Sym.mark :: S (wk .cA)))
        sAc (natSyms (Nat.size M) ++ Sym.mark :: S sAc)) (fun _ => True)
      (1 + (1 + (7 * bitLen M + 7 + (1 + (SubNLogN.Machine.K1.loopB
        (fun x _ => 1 + (6 * ones (encodeNat x) + 9 + 1)) 0 (encodeNat M) +
        (1 + (1 + (7 * bitLen (Nat.size M) + 7)))))))) := by
  have hloop := SubNLogN.Machine.K1.triple_loop_list (body := sizeBody xk)
    (c := fun r => optIsBit (xk.lw.get r))
    (stB S) (fun vs r => xk.lw.get r = (vs.map Sym.bit ++ Sym.mark :: S (wk .g1)).head?)
    (fun _ _ g => g) (fun x _ => 1 + (6 * ones (encodeNat x) + 9 + 1)) (fun _ _ => True)
    (fun _ _ _ _ => trivial) (fun r hr => by rw [hr]; rfl) (fun a vs r hr => by rw [hr]; rfl)
    (fun x a vs g _ => stepB xk S x a vs g) (encodeNat M) 0 () trivial
  have hA := length_encodeNat_size M
  have r1 := runs_pushW xk (wk .cA) Sym.mark S
  have r2 := runs_pushW xk (wk .g1) Sym.mark (Function.update S (wk .cA) (Sym.mark :: S (wk .cA)))
  have r3 := runs_copyW xk (src := wk .cM) (dst := wk .g1) (tmp := wk .u1) (by simp) (by simp)
    (by simp) M (Sym.mark :: C0)
    (Function.update (Function.update S (wk .cA) (Sym.mark :: S (wk .cA))) (wk .g1)
      (Sym.mark :: Function.update S (wk .cA) (Sym.mark :: S (wk .cA)) (wk .g1)))
    (termOK_mark _) (by simp [hM])
  have h0 : Function.update (Function.update (Function.update S (wk .cA) (Sym.mark :: S (wk .cA)))
      (wk .g1) (Sym.mark :: Function.update S (wk .cA) (Sym.mark :: S (wk .cA)) (wk .g1))) (wk .g1)
      (natSyms M ++ Function.update (Function.update S (wk .cA) (Sym.mark :: S (wk .cA))) (wk .g1)
        (Sym.mark :: Function.update S (wk .cA) (Sym.mark :: S (wk .cA)) (wk .g1)) (wk .g1)) =
      stB S 0 (encodeNat M) () := by
    funext k
    by_cases h1 : k = wk .cA
    · subst h1
      simp [stB]
    · by_cases h2 : k = wk .g1
      · subst h2
        simp [stB, natSyms]
      · simp [stB, h1, h2]
  have r4 := RunsIn.iff_runs.mp (runsIn_peekW xk (wk .g1) (stB S 0 (encodeNat M) ()))
  have r5 := runs_popW_cons xk (wk .g1) (stB S (0 + (encodeNat M).length) []
    (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) Sym.mark (S (wk .g1))
    (by simp [stB])
  have r6 := runs_pushW xk sAc Sym.mark (Function.update (stB S (0 + (encodeNat M).length) []
    (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) (wk .g1) (S (wk .g1)))
  have r7 := runs_copyW xk (src := wk .cA) (dst := sAc) (tmp := wk .u1) (by simp) (by simp)
    (by simp) (Nat.size M) (Sym.mark :: S (wk .cA))
    (Function.update (Function.update (stB S (0 + (encodeNat M).length) []
      (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) (wk .g1) (S (wk .g1))) sAc
      (Sym.mark :: Function.update (stB S (0 + (encodeNat M).length) []
        (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) (wk .g1) (S (wk .g1)) sAc))
    (termOK_mark _) (by simp [stB, hA])
  have hrest := WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6 r7)
  have hfin : Function.update (Function.update (Function.update (stB S (0 + (encodeNat M).length) []
      (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) (wk .g1) (S (wk .g1))) sAc
      (Sym.mark :: Function.update (stB S (0 + (encodeNat M).length) []
        (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) (wk .g1) (S (wk .g1)) sAc))
      sAc (natSyms (Nat.size M) ++ Function.update (Function.update (stB S (0 + (encodeNat M).length)
        [] (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) (wk .g1)
        (S (wk .g1))) sAc (Sym.mark :: Function.update (stB S (0 + (encodeNat M).length) []
          (SubNLogN.Machine.K1.foldG (fun _ _ g => g) 0 (encodeNat M) ())) (wk .g1) (S (wk .g1))
          sAc) sAc) =
      Function.update (Function.update S (wk .cA) (natSyms (Nat.size M) ++ Sym.mark :: S (wk .cA)))
        sAc (natSyms (Nat.size M) ++ Sym.mark :: S sAc) := by
    funext k
    by_cases h1 : k = sAc
    · subst h1
      simp [stB]
    · by_cases h2 : k = wk .g1
      · subst h2
        simp [stB, h1]
      · by_cases h3 : k = wk .cA
        · subst h3
          simp [stB, hA]
        · simp [stB, h1, h2, h3]
  have hLR := Triple.seq (Triple.post r4 (fun s hs => ⟨hs.1, by rw [hs.2]; simp [stB]⟩))
    (Triple.seq hloop (WP.W9comp.runs_congr hrest hfin))
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq
    (WP.W9comp.runs_congr r3 h0) hLR))

end PhaseB

/-! ## 5. Phase C: the constants -/

section PhaseC

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

/-- Push the bits of a list, last bit first (the head ends on top). -/
def pushBitsW (k : XK E') : List Bool → Prog (XK E') (fun _ => Sym) xk.R
  | [] => skipW xk
  | b :: bs => .seq (pushBitsW k bs) (pushW xk k (Sym.bit b))

theorem closed_pushBitsW (k : XK E') : ∀ bs : List Bool, (pushBitsW xk k bs).Closed
  | [] => closed_skipW xk
  | _ :: bs => ⟨closed_pushBitsW k bs, closed_pushW xk _ _⟩

theorem runs_pushBitsW (k : XK E') : ∀ (bs : List Bool) (S : XK E' → List Sym),
    Runs (pushBitsW xk k bs) S (Function.update S k (bs.map Sym.bit ++ S k)) (fun _ => True)
      (bs.length + 1)
  | [], S => by
    refine WP.W9comp.runs_congr (runs_skipW xk S) ?_
    simp
  | b :: bs, S => by
    have h1 := runs_pushBitsW k bs S
    have h2 := runs_pushW xk k (Sym.bit b) (Function.update S k (bs.map Sym.bit ++ S k))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 h2) ?_)
      (fun _ h => h) ?_
    · rw [Function.update_idem, Function.update_self]
      rfl
    · simp only [List.length_cons]
      omega

/-- A constant on a fresh floor. -/
def constW (k : XK E') (c : ℕ) : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk k Sym.mark) (pushBitsW xk k (encodeNat c))

theorem runs_constW (k : XK E') (c : ℕ) (S : XK E' → List Sym) :
    Runs (constW xk k c) S (Function.update S k (natSyms c ++ Sym.mark :: S k)) (fun _ => True)
      (1 + ((encodeNat c).length + 1)) := by
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (runs_pushW xk k Sym.mark S)
    (runs_pushBitsW xk k (encodeNat c) _)) ?_
  simp [natSyms]

/-- Copy `src` onto a fresh floor of `dst`, then run `op`. -/
def cpOpW (dst src : XK E') (op : Prog (XK E') (fun _ => Sym) xk.R) :
    Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk dst Sym.mark) (.seq (cpT xk src dst) op)

theorem runs_cpOpW {dst src : XK E'} (hsd : src ≠ dst) (hs1 : src ≠ wk .u1) (hd1 : dst ≠ wk .u1)
    {op : Prog (XK E') (fun _ => Sym) xk.R} (a b : ℕ) (rs : List Sym) (hrs : TermOK rs)
    (S : XK E' → List Sym) (hS : S src = natSyms a ++ rs) {T : ℕ}
    (hop : Runs op (Function.update S dst (natSyms a ++ Sym.mark :: S dst))
      (Function.update S dst (natSyms b ++ Sym.mark :: S dst)) (fun _ => True) T) :
    Runs (cpOpW xk dst src op) S (Function.update S dst (natSyms b ++ Sym.mark :: S dst))
      (fun _ => True) (1 + (7 * bitLen a + 7 + T)) := by
  have r1 := runs_pushW xk dst Sym.mark S
  have r2 := runs_copyW xk (src := src) (dst := dst) (tmp := wk .u1) hsd hs1 hd1 a rs
    (Function.update S dst (Sym.mark :: S dst)) hrs (by simp [hsd, hS])
  have e : Function.update (Function.update S dst (Sym.mark :: S dst)) dst
      (natSyms a ++ Function.update S dst (Sym.mark :: S dst) dst) =
      Function.update S dst (natSyms a ++ Sym.mark :: S dst) := by simp
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq (WP.W9comp.runs_congr r2 e) hop)

theorem natSyms_two_pow_succ (k : ℕ) : natSyms (2 ^ (k + 1)) = Sym.bit false :: natSyms (2 ^ k) := by
  rw [natSyms_two_pow, natSyms_two_pow, List.replicate_succ, List.cons_append]

theorem natSyms_one' : natSyms 1 = [Sym.bit true] := rfl

/-- `2^N` on a fresh floor of `dst`, `N` read from `src` (through the counter `g2`). -/
def pow2W (dst src : XK E') : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk dst Sym.mark) (.seq (pushW xk dst (Sym.bit true)) (.seq (pushW xk (wk .g2) Sym.mark)
    (.seq (cpT xk src (wk .g2)) (.seq (countdown xk.lw (wk .g2) (wk .u5)
      (pushW xk dst (Sym.bit false))) (popW xk (wk .g2))))))

/-- The countdown family of `pow2W`. -/
def stP (S : XK E' → List Sym) (dst : XK E') (N n : ℕ) : XK E' → List Sym :=
  Function.update S dst (natSyms (2 ^ (N - n)) ++ Sym.mark :: S dst)

theorem runs_pow2W {dst src : XK E'} (hd2 : dst ≠ wk .g2) (hs2 : src ≠ wk .g2)
    (hs1 : src ≠ wk .u1) (hsd : src ≠ dst) (N : ℕ) (rs : List Sym) (hrs : TermOK rs)
    (S : XK E' → List Sym) (hS : S src = natSyms N ++ rs) :
    Runs (pow2W xk dst src) S (Function.update S dst (natSyms (2 ^ N) ++ Sym.mark :: S dst))
      (fun _ => True) (1 + (1 + (1 + (7 * bitLen N + 7 + (countdownCost (fun _ => 1) N + 1))))) := by
  have hbody : ∀ n, n < N → RunsIn [] (pushW xk dst (Sym.bit false))
      (Function.update (stP S dst N (n + 1)) (wk .g2) (natSyms (n + 1) ++ Sym.mark :: S (wk .g2)))
      (Function.update (stP S dst N n) (wk .g2) (natSyms (n + 1) ++ Sym.mark :: S (wk .g2)))
      (fun _ => True) 1 := by
    intro n hn
    refine RunsIn.iff_runs.mpr (WP.W9comp.runs_congr (runs_pushW xk dst (Sym.bit false) _) ?_)
    have hN : N - n = N - (n + 1) + 1 := by omega
    funext k
    by_cases h1 : k = wk .g2
    · subst h1
      simp [stP, Ne.symm hd2]
    · by_cases h2 : k = dst
      · subst h2
        simp [stP, h1, hN, natSyms_two_pow_succ]
      · simp [stP, h1, h2]
  have hcd := RunsIn.iff_runs.mp (runsIn_countdown (ρ := []) xk.lw (c := wk .g2) (t := wk .u5)
    (by simp) N (Sym.mark :: S (wk .g2)) (termOK_mark _) (stP S dst N) (fun _ => 1) hbody)
  have r1 := runs_pushW xk dst Sym.mark S
  have r2 := runs_pushW xk dst (Sym.bit true) (Function.update S dst (Sym.mark :: S dst))
  have r3 := runs_pushW xk (wk .g2) Sym.mark (Function.update (Function.update S dst
    (Sym.mark :: S dst)) dst (Sym.bit true :: Function.update S dst (Sym.mark :: S dst) dst))
  have r4 := runs_copyW xk (src := src) (dst := wk .g2) (tmp := wk .u1) hs2 hs1 (by simp) N rs
    (Function.update (Function.update (Function.update S dst (Sym.mark :: S dst)) dst
      (Sym.bit true :: Function.update S dst (Sym.mark :: S dst) dst)) (wk .g2)
      (Sym.mark :: Function.update (Function.update S dst (Sym.mark :: S dst)) dst
        (Sym.bit true :: Function.update S dst (Sym.mark :: S dst) dst) (wk .g2)))
    hrs (by simp [hsd, hs2, hS])
  have e4 : Function.update (Function.update (Function.update (Function.update S dst
      (Sym.mark :: S dst)) dst (Sym.bit true :: Function.update S dst (Sym.mark :: S dst) dst))
      (wk .g2) (Sym.mark :: Function.update (Function.update S dst (Sym.mark :: S dst)) dst
        (Sym.bit true :: Function.update S dst (Sym.mark :: S dst) dst) (wk .g2))) (wk .g2)
      (natSyms N ++ Function.update (Function.update (Function.update S dst (Sym.mark :: S dst))
        dst (Sym.bit true :: Function.update S dst (Sym.mark :: S dst) dst)) (wk .g2)
        (Sym.mark :: Function.update (Function.update S dst (Sym.mark :: S dst)) dst
          (Sym.bit true :: Function.update S dst (Sym.mark :: S dst) dst) (wk .g2)) (wk .g2)) =
      Function.update (stP S dst N N) (wk .g2) (natSyms N ++ Sym.mark :: S (wk .g2)) := by
    funext k
    by_cases h1 : k = wk .g2
    · subst h1
      simp [stP, Ne.symm hd2]
    · by_cases h2 : k = dst
      · subst h2
        simp [stP, h1, natSyms_one']
      · simp [stP, h1, h2]
  have r6 := runs_popW_cons xk (wk .g2) (Function.update (stP S dst N 0) (wk .g2)
    (Sym.mark :: S (wk .g2))) Sym.mark (S (wk .g2)) (by simp)
  have e6 : Function.update (Function.update (stP S dst N 0) (wk .g2) (Sym.mark :: S (wk .g2)))
      (wk .g2) (S (wk .g2)) = Function.update S dst (natSyms (2 ^ N) ++ Sym.mark :: S dst) := by
    funext k
    by_cases h1 : k = wk .g2
    · subst h1
      simp [stP, Ne.symm hd2]
    · simp [stP, h1]
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq (WP.W9comp.runs_congr r4 e4) (WP.W9comp.runs_seq hcd
      (WP.W9comp.runs_congr r6 e6)))))

end PhaseC

/-! ## 6. Phase C, assembled -/

section PhaseC2

variable {E' : Type} [DecidableEq E'] (xk : XKit (XK E'))

theorem bitLen_le_self'' (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen_eq_size]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem bitLen_le_of_lt'' {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  rw [bitLen_eq_size]
  exact Nat.size_le.2 h

theorem runs_cL (K f n : ℕ) (r1 r3 : List Sym) (hr1 : TermOK r1) (hr3 : TermOK r3)
    (S : XK E' → List Sym) (hK : S sK = natSyms K ++ r1) (hf : S sF = natSyms f ++ r3)
    (hfn : bitLen f ≤ n) (hKn : bitLen K ≤ n) (hfKn : bitLen (f * K) ≤ n) :
    Runs (cpOpW xk (wk .cL) sF (mulT xk (wk .cL) sK)) S
      (Function.update S (wk .cL) (natSyms (f * K) ++ Sym.mark :: S (wk .cL))) (fun _ => True)
      (1 + (7 * bitLen f + 7 + opCost xk n)) := by
  refine runs_cpOpW xk (by simp) (by simp) (by simp) f (f * K) r3 hr3 S hf ?_
  have h := runs_mulBy xk (k := wk .cL) (b := sK) (t := wk .iT) (A := wk .u1) (Bs := wk .u2)
    (Acc := wk .u3) (T := wk .u4) (by simp) f K n (Sym.mark :: S (wk .cL)) r1
    (Function.update S (wk .cL) (natSyms f ++ Sym.mark :: S (wk .cL))) (termOK_mark _) hr1
    (by simp) (by simp [hK]) hfn hKn hfKn
  refine WP.W9comp.runs_congr h ?_
  simp

theorem runs_cF1 (f n : ℕ) (r3 X : List Sym) (hr3 : TermOK r3) (S : XK E' → List Sym)
    (hf : S sF = natSyms f ++ r3) (hc1 : S (wk .c1) = natSyms 1 ++ Sym.mark :: X) (hf1 : 1 ≤ f)
    (hfn : bitLen f ≤ n) (h1n : bitLen 1 ≤ n) :
    Runs (cpOpW xk (wk .cF1) sF (subT xk (wk .cF1) (wk .c1))) S
      (Function.update S (wk .cF1) (natSyms (f - 1) ++ Sym.mark :: S (wk .cF1))) (fun _ => True)
      (1 + (7 * bitLen f + 7 + opCost xk n)) := by
  refine runs_cpOpW xk (by simp) (by simp) (by simp) f (f - 1) r3 hr3 S hf ?_
  have h := runs_subFrom xk (k := wk .cF1) (b := wk .c1) (t := wk .iT) (t1 := wk .u1)
    (t2 := wk .u2) (t3 := wk .u3) (by simp) f 1 n (Sym.mark :: S (wk .cF1)) (Sym.mark :: X)
    (Function.update S (wk .cF1) (natSyms f ++ Sym.mark :: S (wk .cF1))) (termOK_mark _)
    (termOK_mark _) hf1 (by simp) (by simp [hc1]) hfn h1n
  refine WP.W9comp.runs_congr h ?_
  simp

theorem runs_c2K1 (K : ℕ) (hK : 1 ≤ K) (X : List Sym) (S : XK E' → List Sym)
    (hc : S (wk .c2K) = natSyms (2 ^ K) ++ Sym.mark :: X) :
    Runs (cpOpW xk (wk .c2K1) (wk .c2K) (popW xk (wk .c2K1))) S
      (Function.update S (wk .c2K1) (natSyms (2 ^ (K - 1)) ++ Sym.mark :: S (wk .c2K1)))
      (fun _ => True) (1 + (7 * bitLen (2 ^ K) + 7 + 1)) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine runs_cpOpW xk (by simp) (by simp) (by simp) (2 ^ (K' + 1)) (2 ^ K') (Sym.mark :: X)
    (termOK_mark _) S hc ?_
  have h := runs_popW_cons xk (wk .c2K1)
    (Function.update S (wk .c2K1) (natSyms (2 ^ (K' + 1)) ++ Sym.mark :: S (wk .c2K1)))
    (Sym.bit false) (natSyms (2 ^ K') ++ Sym.mark :: S (wk .c2K1))
    (by simp [natSyms_two_pow_succ])
  refine WP.W9comp.runs_congr h ?_
  simp

theorem runs_c2r1 (ρ : ℕ) (X : List Sym) (S : XK E' → List Sym)
    (hc : S (wk .c2r) = natSyms (2 ^ ρ) ++ Sym.mark :: X) :
    Runs (cpOpW xk (wk .c2r1) (wk .c2r) (pushW xk (wk .c2r1) (Sym.bit false))) S
      (Function.update S (wk .c2r1) (natSyms (2 ^ (ρ + 1)) ++ Sym.mark :: S (wk .c2r1)))
      (fun _ => True) (1 + (7 * bitLen (2 ^ ρ) + 7 + 1)) := by
  refine runs_cpOpW xk (by simp) (by simp) (by simp) (2 ^ ρ) (2 ^ (ρ + 1)) (Sym.mark :: X)
    (termOK_mark _) S hc ?_
  refine WP.W9comp.runs_congr (runs_pushW xk (wk .c2r1) (Sym.bit false) _) ?_
  simp [natSyms_two_pow_succ]

/-- Phase C: the eleven constants. -/
def phaseC : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (constW xk (wk .c1) 1) (.seq (constW xk (wk .c10) 10) (.seq (constW xk (wk .c11) 11)
    (.seq (cpOpW xk (wk .cL) sF (mulT xk (wk .cL) sK)) (.seq (pow2W xk (wk .c2L) (wk .cL))
      (.seq (pow2W xk (wk .c2K) sK) (.seq (cpOpW xk (wk .c2K1) (wk .c2K) (popW xk (wk .c2K1)))
        (.seq (pow2W xk (wk .c2r) sRho)
          (.seq (cpOpW xk (wk .c2r1) (wk .c2r) (pushW xk (wk .c2r1) (Sym.bit false)))
            (.seq (cpOpW xk (wk .cF1) sF (subT xk (wk .cF1) (wk .c1)))
              (pow2W xk (wk .c2A) (wk .cA)))))))))))

/-- Phase D: the tags. -/
def phaseD : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (pushW xk sH (Sym.tag 15)) (pushW xk sB (Sym.tag 14))

/-- **The setup program.** -/
def setupProg : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (phaseA xk) (.seq (phaseB xk) (.seq (phaseC xk) (phaseD xk)))

theorem closed_constW (k : XK E') (c : ℕ) : (constW xk k c).Closed :=
  ⟨closed_pushW xk _ _, closed_pushBitsW xk _ _⟩

theorem closed_pow2W (dst src : XK E') : (pow2W xk dst src).Closed :=
  ⟨closed_pushW xk _ _, closed_pushW xk _ _, closed_pushW xk _ _, closed_copyW xk _ _ _,
    closed_countdown xk.lw _ _ (closed_pushW xk _ _), closed_popW xk _⟩

theorem closed_setupProg : (setupProg xk).Closed :=
  ⟨closed_phaseA xk, closed_phaseB xk,
    ⟨closed_constW xk _ _, closed_constW xk _ _, closed_constW xk _ _,
      ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_mulBy xk _ _ _ _ _ _ _⟩,
      closed_pow2W xk _ _, closed_pow2W xk _ _,
      ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_popW xk _⟩, closed_pow2W xk _ _,
      ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_pushW xk _ _⟩,
      ⟨closed_pushW xk _ _, closed_copyW xk _ _ _, closed_subFrom xk _ _ _ _ _ _⟩,
      closed_pow2W xk _ _⟩,
    ⟨closed_pushW xk _ _, closed_pushW xk _ _⟩⟩

theorem cd_le (N : ℕ) : countdownCost (fun _ => 1) N ≤ 17 * N + 2 := by
  have h := countdownCost_le (fun _ => 1) N
  have h2 : ((List.range N).map fun _ => 1).sum = N * 1 := sum_range_const N 1
  omega

theorem costC_le (K ρ f A O : ℕ) (hK1 : 1 ≤ K) (hf1 : 1 ≤ f) (hfK : f * K < A) (hρK : ρ < K) :
    (1 + ((encodeNat 1).length + 1)) + ((1 + ((encodeNat 10).length + 1)) +
      ((1 + ((encodeNat 11).length + 1)) + ((1 + (7 * bitLen f + 7 + O)) +
      ((1 + (1 + (1 + (7 * bitLen (f * K) + 7 + (countdownCost (fun _ => 1) (f * K) + 1))))) +
      ((1 + (1 + (1 + (7 * bitLen K + 7 + (countdownCost (fun _ => 1) K + 1))))) +
      ((1 + (7 * bitLen (2 ^ K) + 7 + 1)) +
      ((1 + (1 + (1 + (7 * bitLen ρ + 7 + (countdownCost (fun _ => 1) ρ + 1))))) +
      ((1 + (7 * bitLen (2 ^ ρ) + 7 + 1)) + ((1 + (7 * bitLen f + 7 + O)) +
      (1 + (1 + (1 + (7 * bitLen A + 7 + (countdownCost (fun _ => 1) A + 1)))))))))))))) ≤
    2 * O + 300 * (A + 2) := by
  have hKfK : K ≤ f * K := Nat.le_mul_of_pos_left K (by omega)
  have hffK : f ≤ f * K := Nat.le_mul_of_pos_right f (by omega)
  have c1 := cd_le (f * K)
  have c2 := cd_le K
  have c3 := cd_le ρ
  have c4 := cd_le A
  have e1 : (encodeNat 1).length = 1 := rfl
  have e10 : (encodeNat 10).length = 4 := rfl
  have e11 : (encodeNat 11).length = 4 := rfl
  have d1 : bitLen (2 ^ K) ≤ A + 1 := bitLen_le_of_lt'' (Nat.pow_lt_pow_right (by norm_num)
    (show K < A + 1 by omega))
  have d2 : bitLen (2 ^ ρ) ≤ A + 1 := bitLen_le_of_lt'' (Nat.pow_lt_pow_right (by norm_num)
    (show ρ < A + 1 by omega))
  have d3 := bitLen_le_self'' A
  have d4 := bitLen_le_self'' ρ
  have d5 := bitLen_le_self'' K
  have d6 := bitLen_le_self'' f
  have d7 := bitLen_le_self'' (f * K)
  generalize countdownCost (fun _ => 1) (f * K) = q1 at c1 ⊢
  generalize countdownCost (fun _ => 1) K = q2 at c2 ⊢
  generalize countdownCost (fun _ => 1) ρ = q3 at c3 ⊢
  generalize countdownCost (fun _ => 1) A = q4 at c4 ⊢
  generalize bitLen (2 ^ K) = q5 at d1 ⊢
  generalize bitLen (2 ^ ρ) = q6 at d2 ⊢
  generalize f * K = L at hfK hKfK hffK c1 d7 ⊢
  linarith

theorem runs_phaseC (K ρ f A : ℕ) (r1 r2 r3 X : List Sym) (hr1 : TermOK r1) (hr2 : TermOK r2)
    (hr3 : TermOK r3) (S : XK E' → List Sym) (hK : S sK = natSyms K ++ r1)
    (hρ : S sRho = natSyms ρ ++ r2) (hf : S sF = natSyms f ++ r3)
    (hA : S (wk .cA) = natSyms A ++ Sym.mark :: X) (hK1 : 1 ≤ K) (hf1 : 1 ≤ f) (hfK : f * K < A)
    (hρK : ρ < K) (X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 : List Sym)
    (h1 : S (wk .c1) = X1) (h2 : S (wk .c10) = X2) (h3 : S (wk .c11) = X3)
    (h4 : S (wk .cL) = X4) (h5 : S (wk .c2L) = X5) (h6 : S (wk .c2K) = X6)
    (h7 : S (wk .c2K1) = X7) (h8 : S (wk .c2r) = X8) (h9 : S (wk .c2r1) = X9)
    (h10 : S (wk .cF1) = X10) (h11 : S (wk .c2A) = X11) :
    Runs (phaseC xk) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S
        (wk .c1) (natSyms 1 ++ Sym.mark :: X1))
        (wk .c10) (natSyms 10 ++ Sym.mark :: X2))
        (wk .c11) (natSyms 11 ++ Sym.mark :: X3))
        (wk .cL) (natSyms (f * K) ++ Sym.mark :: X4))
        (wk .c2L) (natSyms (2 ^ (f * K)) ++ Sym.mark :: X5))
        (wk .c2K) (natSyms (2 ^ K) ++ Sym.mark :: X6))
        (wk .c2K1) (natSyms (2 ^ (K - 1)) ++ Sym.mark :: X7))
        (wk .c2r) (natSyms (2 ^ ρ) ++ Sym.mark :: X8))
        (wk .c2r1) (natSyms (2 ^ (ρ + 1)) ++ Sym.mark :: X9))
        (wk .cF1) (natSyms (f - 1) ++ Sym.mark :: X10))
        (wk .c2A) (natSyms (2 ^ A) ++ Sym.mark :: X11))
      (fun _ => True) (2 * opCost xk (A + 2) + 300 * (A + 2)) := by
  have hKfK : K ≤ f * K := Nat.le_mul_of_pos_left K (by omega)
  have hffK : f ≤ f * K := Nat.le_mul_of_pos_right f (by omega)
  have bf : bitLen f ≤ A + 2 := le_trans (bitLen_le_self'' f) (by omega)
  have bK : bitLen K ≤ A + 2 := le_trans (bitLen_le_self'' K) (by omega)
  have bfK : bitLen (f * K) ≤ A + 2 := le_trans (bitLen_le_self'' _) (by omega)
  have b1 : bitLen 1 ≤ A + 2 := le_trans (bitLen_le_self'' 1) (by omega)
  obtain ⟨S1, e1⟩ : ∃ T, T = Function.update S (wk .c1) (natSyms 1 ++ Sym.mark :: X1) := ⟨_, rfl⟩
  obtain ⟨S2, e2⟩ : ∃ T, T = Function.update S1 (wk .c10) (natSyms 10 ++ Sym.mark :: X2) :=
    ⟨_, rfl⟩
  obtain ⟨S3, e3⟩ : ∃ T, T = Function.update S2 (wk .c11) (natSyms 11 ++ Sym.mark :: X3) :=
    ⟨_, rfl⟩
  obtain ⟨S4, e4⟩ : ∃ T, T = Function.update S3 (wk .cL) (natSyms (f * K) ++ Sym.mark :: X4) :=
    ⟨_, rfl⟩
  obtain ⟨S5, e5⟩ : ∃ T, T = Function.update S4 (wk .c2L)
      (natSyms (2 ^ (f * K)) ++ Sym.mark :: X5) := ⟨_, rfl⟩
  obtain ⟨S6, e6⟩ : ∃ T, T = Function.update S5 (wk .c2K) (natSyms (2 ^ K) ++ Sym.mark :: X6) :=
    ⟨_, rfl⟩
  obtain ⟨S7, e7⟩ : ∃ T, T = Function.update S6 (wk .c2K1)
      (natSyms (2 ^ (K - 1)) ++ Sym.mark :: X7) := ⟨_, rfl⟩
  obtain ⟨S8, e8⟩ : ∃ T, T = Function.update S7 (wk .c2r) (natSyms (2 ^ ρ) ++ Sym.mark :: X8) :=
    ⟨_, rfl⟩
  obtain ⟨S9, e9⟩ : ∃ T, T = Function.update S8 (wk .c2r1)
      (natSyms (2 ^ (ρ + 1)) ++ Sym.mark :: X9) := ⟨_, rfl⟩
  obtain ⟨S10, e10⟩ : ∃ T, T = Function.update S9 (wk .cF1)
      (natSyms (f - 1) ++ Sym.mark :: X10) := ⟨_, rfl⟩
  obtain ⟨S11, e11⟩ : ∃ T, T = Function.update S10 (wk .c2A)
      (natSyms (2 ^ A) ++ Sym.mark :: X11) := ⟨_, rfl⟩
  have s1 := runs_constW xk (wk .c1) 1 S
  rw [h1, ← e1] at s1
  have s2 := runs_constW xk (wk .c10) 10 S1
  have q2 : S1 (wk .c10) = X2 := by rw [e1, ← h2]; simp
  rw [q2, ← e2] at s2
  have s3 := runs_constW xk (wk .c11) 11 S2
  have q3 : S2 (wk .c11) = X3 := by rw [e2, e1, ← h3]; simp
  rw [q3, ← e3] at s3
  have s4 := runs_cL xk K f (A + 2) r1 r3 hr1 hr3 S3 (by rw [e3, e2, e1]; simp [hK])
    (by rw [e3, e2, e1]; simp [hf]) bf bK bfK
  have q4 : S3 (wk .cL) = X4 := by rw [e3, e2, e1, ← h4]; simp
  rw [q4, ← e4] at s4
  have s5 := runs_pow2W xk (dst := wk .c2L) (src := wk .cL) (by simp) (by simp) (by simp)
    (by simp) (f * K) (Sym.mark :: X4) (termOK_mark _) S4 (by rw [e4]; simp)
  have q5 : S4 (wk .c2L) = X5 := by rw [e4, e3, e2, e1, ← h5]; simp
  rw [q5, ← e5] at s5
  have s6 := runs_pow2W xk (dst := wk .c2K) (src := sK) (by simp) (by simp) (by simp)
    (by simp) K r1 hr1 S5 (by rw [e5, e4, e3, e2, e1]; simp [hK])
  have q6 : S5 (wk .c2K) = X6 := by rw [e5, e4, e3, e2, e1, ← h6]; simp
  rw [q6, ← e6] at s6
  have s7 := runs_c2K1 xk K hK1 X6 S6 (by rw [e6]; simp)
  have q7 : S6 (wk .c2K1) = X7 := by rw [e6, e5, e4, e3, e2, e1, ← h7]; simp
  rw [q7, ← e7] at s7
  have s8 := runs_pow2W xk (dst := wk .c2r) (src := sRho) (by simp) (by simp) (by simp)
    (by simp) ρ r2 hr2 S7 (by rw [e7, e6, e5, e4, e3, e2, e1]; simp [hρ])
  have q8 : S7 (wk .c2r) = X8 := by rw [e7, e6, e5, e4, e3, e2, e1, ← h8]; simp
  rw [q8, ← e8] at s8
  have s9 := runs_c2r1 xk ρ X8 S8 (by rw [e8]; simp)
  have q9 : S8 (wk .c2r1) = X9 := by rw [e8, e7, e6, e5, e4, e3, e2, e1, ← h9]; simp
  rw [q9, ← e9] at s9
  have s10 := runs_cF1 xk f (A + 2) r3 X1 hr3 S9 (by rw [e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp [hf])
    (by rw [e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp) hf1 bf b1
  have q10 : S9 (wk .cF1) = X10 := by rw [e9, e8, e7, e6, e5, e4, e3, e2, e1, ← h10]; simp
  rw [q10, ← e10] at s10
  have s11 := runs_pow2W xk (dst := wk .c2A) (src := wk .cA) (by simp) (by simp) (by simp)
    (by simp) A (Sym.mark :: X) (termOK_mark _) S10 (by rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp [hA])
  have q11 : S10 (wk .c2A) = X11 := by rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, ← h11]; simp
  rw [q11, ← e11] at s11
  have hall := WP.W9comp.runs_seq s1 (WP.W9comp.runs_seq s2 (WP.W9comp.runs_seq s3
    (WP.W9comp.runs_seq s4 (WP.W9comp.runs_seq s5 (WP.W9comp.runs_seq s6
    (WP.W9comp.runs_seq s7 (WP.W9comp.runs_seq s8 (WP.W9comp.runs_seq s9
    (WP.W9comp.runs_seq s10 s11)))))))))
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e9, ← e10, ← e11]
  exact WP.W9comp.runs_mono hall (fun _ _ => trivial) (costC_le K ρ f A (opCost xk (A + 2)) hK1
    hf1 hfK hρK)

theorem runs_phaseD (S : XK E' → List Sym) (Xh Xb : List Sym) (hh : S sH = Xh) (hb : S sB = Xb) :
    Runs (phaseD xk) S (Function.update (Function.update S sH (Sym.tag 15 :: Xh)) sB
      (Sym.tag 14 :: Xb)) (fun _ => True) (1 + 1) := by
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (runs_pushW xk sH (Sym.tag 15) S)
    (runs_pushW xk sB (Sym.tag 14) _)) ?_
  subst hh hb
  simp

theorem runs_phaseB' (S : XK E' → List Sym) (M : ℕ) (C0 Xa Xs : List Sym)
    (hM : S (wk .cM) = natSyms M ++ Sym.mark :: C0) (ha : S (wk .cA) = Xa) (hs : S sAc = Xs) :
    Runs (phaseB xk) S
      (Function.update (Function.update S (wk .cA) (natSyms (Nat.size M) ++ Sym.mark :: Xa))
        sAc (natSyms (Nat.size M) ++ Sym.mark :: Xs)) (fun _ => True)
      (1 + (1 + (7 * bitLen M + 7 + (1 + (SubNLogN.Machine.K1.loopB
        (fun x _ => 1 + (6 * ones (encodeNat x) + 9 + 1)) 0 (encodeNat M) +
        (1 + (1 + (7 * bitLen (Nat.size M) + 7)))))))) := by
  subst ha hs
  exact runs_phaseB xk S M C0 hM

end PhaseC2

/-! ## 7. Costs and the main theorem -/

theorem loopB_A_le (A M : ℕ) (hb : ∀ y, y < M → bitLen y ≤ A) :
    ∀ (vs : List (List Bool)) (x : ℕ), x + vs.length ≤ M →
      SubNLogN.Machine.K1.loopB
        (fun x a => 3 * (a.map Sym.bit).length + 3 + (6 * ones (encodeNat x) + 9 + 1)) x vs ≤
        3 * SubNLogN.Machine.vol vs + vs.length * (6 * A + 11) + 1
  | [], x, _ => by simp [SubNLogN.Machine.K1.loopB]
  | a :: vs, x, h => by
    have h' : x + 1 + vs.length ≤ M := by simp only [List.length_cons] at h; omega
    have ih := loopB_A_le A M hb vs (x + 1) h'
    have h1 : ones (encodeNat x) ≤ A := le_trans (ones_le_length _) (hb x (by omega))
    have hl : (a.map Sym.bit).length = a.length := List.length_map _
    simp only [SubNLogN.Machine.K1.loopB, SubNLogN.Machine.K1.vol_cons, List.length_cons]
    have e : (vs.length + 1) * (6 * A + 11) = vs.length * (6 * A + 11) + (6 * A + 11) := by ring
    omega

theorem loopB_B_le (A : ℕ) : ∀ (vs : List Bool) (x : ℕ), (∀ y, y < x + vs.length → bitLen y ≤ A) →
    SubNLogN.Machine.K1.loopB (fun x (_ : Bool) => 1 + (6 * ones (encodeNat x) + 9 + 1)) x vs ≤
      vs.length * (6 * A + 12) + 1
  | [], x, _ => by simp [SubNLogN.Machine.K1.loopB]
  | a :: vs, x, h => by
    have ih := loopB_B_le A vs (x + 1) (fun y hy => h y (by simp only [List.length_cons]; omega))
    have h1 : ones (encodeNat x) ≤ A := le_trans (ones_le_length _)
      (h x (by simp only [List.length_cons]; omega))
    simp only [SubNLogN.Machine.K1.loopB, List.length_cons]
    have e : (vs.length + 1) * (6 * A + 12) = vs.length * (6 * A + 12) + (6 * A + 12) := by ring
    omega

open SubNLogN.Machine.AppC.C7Aux in
theorem fK_lt_size (K f N0 N1 N2 N3 : ℕ) (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) : 3 * (f * K) < Nat.size (c7M K f N0 N1 N2 N3) := by
  rw [Nat.lt_size]
  unfold c7M
  have h2 : 2 ^ (3 * (f * K)) = 2 ^ (f * K) * 2 ^ (f * K) * 2 ^ (f * K) := by
    rw [← pow_add, ← pow_add]
    ring_nf
  rw [h2]
  calc 2 ^ (f * K) * 2 ^ (f * K) * 2 ^ (f * K)
      = 1 * 2 ^ (f * K) * 1 * 2 ^ (f * K) * 1 * 2 ^ (f * K) * 1 := by ring
    _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 := by gcongr

end SubNLogN.Machine.AppC.C7SetupAux

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus
  SubNLogN.Machine.AppC.C7Aux SubNLogN.Machine.AppC.C7SetupAux

/-- **The setup phase of the extraction kernel, proved** (`C7XSetupStmt`): for every arithmetic
kit, `setupProg` (phases A-D of `Machine/AppC/C7ExtractSetupProof.lean`) reaches `setupSt` within
`setupCost`. No `sorry`, no extra hypothesis. -/
theorem c7XSetup_holds : C7XSetupStmt := by
  intro E' _ xk
  refine ⟨setupProg xk, closed_setupProg xk, ?_⟩
  intro K ρ f N0 N1 N2 N3 R w rest r1 r2 r3 r4 r5 r6 r7 S hK6 hρK hf1 hN0 hN1 hN2 hN3 hR1 hw hwR
    hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hSK hSρ hSf hSN1 hSN2 hSN3 hSR
  have hsz : 3 * (f * K) < Nat.size w.length := by
    rw [hw]
    exact fK_lt_size K f N0 N1 N2 N3 hN0 hN1 hN2 hN3
  have hK1 : 1 ≤ K := by omega
  have hfK : f * K < Nat.size w.length := by omega
  obtain ⟨SA, eA⟩ : ∃ T, T = Function.update (Function.update (Function.update S sArr rest)
      (wk .T) ((SubNLogN.Machine.arrSyms w).reverse ++ Sym.sep :: S (wk .T))) (wk .cM)
      (natSyms w.length ++ Sym.mark :: S (wk .cM)) := ⟨_, rfl⟩
  have rA := runs_phaseA xk S w rest hrest hS0
  rw [← eA] at rA
  obtain ⟨SB, eB⟩ : ∃ T, T = Function.update (Function.update SA (wk .cA)
      (natSyms (Nat.size w.length) ++ Sym.mark :: S (wk .cA))) sAc
      (natSyms (Nat.size w.length) ++ Sym.mark :: S sAc) := ⟨_, rfl⟩
  have rB := runs_phaseB' xk SA w.length (S (wk .cM)) (S (wk .cA)) (S sAc) (by rw [eA]; simp)
    (by rw [eA]; simp) (by rw [eA]; simp)
  rw [← eB] at rB
  obtain ⟨SC, eC⟩ : ∃ T, T = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update SB
      (wk .c1) (natSyms 1 ++ Sym.mark :: S (wk .c1)))
      (wk .c10) (natSyms 10 ++ Sym.mark :: S (wk .c10)))
      (wk .c11) (natSyms 11 ++ Sym.mark :: S (wk .c11)))
      (wk .cL) (natSyms (f * K) ++ Sym.mark :: S (wk .cL)))
      (wk .c2L) (natSyms (2 ^ (f * K)) ++ Sym.mark :: S (wk .c2L)))
      (wk .c2K) (natSyms (2 ^ K) ++ Sym.mark :: S (wk .c2K)))
      (wk .c2K1) (natSyms (2 ^ (K - 1)) ++ Sym.mark :: S (wk .c2K1)))
      (wk .c2r) (natSyms (2 ^ ρ) ++ Sym.mark :: S (wk .c2r)))
      (wk .c2r1) (natSyms (2 ^ (ρ + 1)) ++ Sym.mark :: S (wk .c2r1)))
      (wk .cF1) (natSyms (f - 1) ++ Sym.mark :: S (wk .cF1)))
      (wk .c2A) (natSyms (2 ^ Nat.size w.length) ++ Sym.mark :: S (wk .c2A)) := ⟨_, rfl⟩
  have rC := runs_phaseC xk K ρ f (Nat.size w.length) r1 r2 r3 (S (wk .cA)) hr1 hr2 hr3 SB
    (by rw [eB, eA]; simp [hSK]) (by rw [eB, eA]; simp [hSρ]) (by rw [eB, eA]; simp [hSf])
    (by rw [eB]; simp) hK1 hf1 hfK hρK (S (wk .c1)) (S (wk .c10)) (S (wk .c11)) (S (wk .cL))
    (S (wk .c2L)) (S (wk .c2K)) (S (wk .c2K1)) (S (wk .c2r)) (S (wk .c2r1)) (S (wk .cF1))
    (S (wk .c2A)) (by rw [eB, eA]; simp) (by rw [eB, eA]; simp) (by rw [eB, eA]; simp)
    (by rw [eB, eA]; simp) (by rw [eB, eA]; simp) (by rw [eB, eA]; simp)
    (by rw [eB, eA]; simp) (by rw [eB, eA]; simp) (by rw [eB, eA]; simp)
    (by rw [eB, eA]; simp) (by rw [eB, eA]; simp)
  rw [← eC] at rC
  have rD := runs_phaseD xk SC (S sH) (S sB) (by rw [eC, eB, eA]; simp) (by rw [eC, eB, eA]; simp)
  have hall := WP.W9comp.runs_seq rA (WP.W9comp.runs_seq rB (WP.W9comp.runs_seq rC rD))
  have hfin : Function.update (Function.update SC sH (Sym.tag 15 :: S sH)) sB
      (Sym.tag 14 :: S sB) = setupSt S K ρ f w rest := by
    rw [eC, eB, eA]
    rfl
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall hfin) (fun _ _ => trivial) ?_
  have hbM : bitLen w.length = Nat.size w.length := bitLen_eq_size _
  have hlen := length_encodeNat_size w.length
  have hLA := loopB_A_le (Nat.size w.length) w.length (fun y hy => by
    rw [bitLen_eq_size]
    exact Nat.size_le_size hy.le) w 0 (by simp)
  have hLB := loopB_B_le (Nat.size w.length) (encodeNat w.length) 0 (fun y hy => by
    have := bitLen_le_self'' y
    omega)
  rw [hlen] at hLB
  have hbA := bitLen_le_self'' (Nat.size w.length)
  have hO : 40 * (Nat.size w.length + 3) ^ 2 ≤ opCost xk (Nat.size w.length + 2) := by
    unfold opCost
    have e : Nat.size w.length + 2 + 1 = Nat.size w.length + 3 := by omega
    rw [e]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold setupCost
  generalize Nat.size w.length = A at hO hLA hLB hbM hbA ⊢
  generalize opCost xk (A + 2) = O at hO ⊢
  have eS : (A + 3) ^ 2 = A * A + 6 * A + 9 := by ring
  have eA2 : A * (6 * A + 12) = 6 * (A * A) + 12 * A := by ring
  have h6 : 6 * A + 11 ≤ O := by nlinarith
  have hMO : w.length * (6 * A + 11) ≤ w.length * O := Nat.mul_le_mul_left _ h6
  have h200 : 100 * 2 * O ≤ 100 * (A + 2) * O := Nat.mul_le_mul_right _ (by omega)
  have e : (w.length + 100 * (A + 2)) * O = w.length * O + 100 * (A + 2) * O := by ring
  rw [e]
  linarith

end SubNLogN.Machine.AppC.C7ExtractAux
