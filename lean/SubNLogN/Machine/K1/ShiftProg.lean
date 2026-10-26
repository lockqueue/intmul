/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.ShiftMath
import SubNLogN.Machine.K1.AddSub
import IntMulTM.Framework.Lib.Counter

/-!
# `SubNLogN.Machine.K1.ShiftProg`: programs of the shift kernel and its per-record loops

Paper: Lemma A.4(5) (`lem:transfer-streams`) and its proof in Appendix A.1 (`sec:transfer-premises`)
(partition each word into the retained interval and the known zero or sign bits; copy the
retained interval and fill the rest in one traversal; not `t` one-bit shifts).

## Plan (program design, invariants, cost)
Registers `XReg = o × p × lb × ng`: two symbol slots, the last input bit read, and the flag
`t < 0`. Unary counters are runs of tokens `bit true` above a `mark` guard.
* Room counter `U` (`w2` tokens) with its used-token stack `U'`; shift counter `D`
  (`d = min(|t|, cap)` tokens, `cap = w2` if `t ≥ 0`, `cap = w1` if `t < 0`) with `D'`.
* Per record (input bits `xs`, `|xs| = w1`), output pushed on `T` (reversed):
  * `t ≥ 0`, phase Z (`zLoop`): `d` zeros (`d ≤ w2`), moving `D → D'`, `U → U'`.
  * `t < 0`, phase S (`sLoop`): skip `d` input bits (`d ≤ w1`), moving `D → D'`.
  * phase C (`cLoop`): copy input bits while room is left.
  * phase E (`eLoop`): fill the remaining room with the last bit read (the sign).
  * phase X (`dropBits`): discard the remaining input bits; then the record ends.
  * restore `U` and `D` (`moveBlock U' U`, `moveBlock D' D`). Cost `O(w1 + w2)`.
* This file: the programs (all of them, including the preprocessing used in
  `K1/ShiftPre.lean`) and the loop lemmas of one record: `zLoop_eval`, `sLoop_eval`,
  `cLoop_eval`, `eLoop_eval`, `dropBits_eval` (exact final states and costs).

**Scope (honest summary).** Programs and proved evaluation lemmas only (no `sorry`).
-/

namespace SubNLogN.Machine.K1.ShiftAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1 SubNLogN.Machine.K1.AddSubAux

/-! ## Registers, tokens, atoms -/

/-- Registers of the shift kernel: slots `o`, `p`, the last bit read `lb`, the flag `ng`. -/
abbrev XReg : Type := Option Sym × Option Sym × Bool × Bool

/-- Programs of the shift kernel. -/
abbrev XProg (K : Type) : Type := Prog K (fun _ => Sym) XReg

/-- Lens onto the slot `o` (to run `TMFw.Lib` routines). -/
def lensX : Lens XReg (Option Sym) := Lens.fst _ _

/-- Run a `TMFw.Lib` routine on the slot `o`. -/
def liftX {K : Type} (p : SProg K) : XProg K := p.liftRegs lensX

/-- `n` unary tokens. -/
def toks (n : ℕ) : List Sym := List.replicate n (Sym.bit true)

/-- The last element of `l`, or `b` if `l` is empty. -/
def lastOr : Bool → List Bool → Bool
  | b, [] => b
  | _, x :: l => lastOr x l

theorem toks_succ (n : ℕ) : toks (n + 1) = Sym.bit true :: toks n := rfl

theorem toks_succ' (n : ℕ) (L : List Sym) : toks (n + 1) ++ L = toks n ++ Sym.bit true :: L := by
  simp [toks, List.replicate_succ']

theorem replicate_succ_append' {α : Type} (n : ℕ) (a : α) (L : List α) :
    List.replicate (n + 1) a ++ L = List.replicate n a ++ a :: L := by
  simp [List.replicate_succ']

theorem toks_eq_map (n : ℕ) : toks n = (List.replicate n true).map Sym.bit := by
  simp [toks, List.map_replicate]

theorem lastOr_nil (b : Bool) : lastOr b [] = b := rfl

theorem lastOr_cons (b x : Bool) (l : List Bool) : lastOr b (x :: l) = lastOr x l := rfl

theorem lastOr_eq_getLast? (b : Bool) : ∀ l : List Bool, lastOr b l = l.getLast?.getD b
  | [] => rfl
  | [x] => rfl
  | x :: y :: l => by
    rw [lastOr_cons, lastOr_eq_getLast? x (y :: l), List.getLast?_cons_cons]
    cases h : (y :: l).getLast? with
    | none => simp at h
    | some z => rfl

theorem lastOr_append (b : Bool) (l₁ l₂ : List Bool) :
    lastOr b (l₁ ++ l₂) = lastOr (lastOr b l₁) l₂ := by
  induction l₁ generalizing b with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, lastOr_cons, lastOr_cons, ih]

theorem head?_toks_mark (n : ℕ) (L : List Sym) :
    optIsBit (toks n ++ Sym.mark :: L).head? = decide (0 < n) := by
  cases n <;> rfl

section Atoms

variable {K : Type}

/-- Peek `k` into `o`. -/
def pkO (k : K) : XProg K := .peek k fun v o => (o, v.2)
/-- Peek `k` into `p`. -/
def pkP (k : K) : XProg K := .peek k fun v o => (v.1, o, v.2.2)
/-- Pop `k` into `o`. -/
def ppO (k : K) : XProg K := .pop k fun v o => (o, v.2)
/-- Pop `k`, discarding the symbol. -/
def pd (k : K) : XProg K := .pop k fun v _ => v
/-- Push a constant on `k`. -/
def pc (k : K) (x : Sym) : XProg K := .push k fun _ => x
/-- `lb := ` the bit in `o`. -/
def setLb : XProg K := .load fun v => (v.1, v.2.1, optBit v.1, v.2.2.2)
/-- Push the bit `lb` on `k`. -/
def pushLb (k : K) : XProg K := .push k fun v => .bit v.2.2.1
/-- Push the symbol in `o` on `k` (default `sep`). -/
def pushO (k : K) : XProg K := .push k fun v => v.1.getD .sep
/-- Both slots hold bits. -/
def bothBits (v : XReg) : Bool := optIsBit v.1 && optIsBit v.2.1
/-- The slot `o` holds a bit. -/
def oBit (v : XReg) : Bool := optIsBit v.1
/-- The flag `ng`. -/
def isNg (v : XReg) : Bool := v.2.2.2

variable [DecidableEq K]

theorem pkO_eval (k : K) (v : XReg) (S : K → List Sym) :
    Eval [] (pkO k) ⟨v, S⟩ ⟨((S k).head?, v.2), S⟩ 1 := Eval.peek _ _ _ _ _

theorem pkP_eval (k : K) (v : XReg) (S : K → List Sym) :
    Eval [] (pkP k) ⟨v, S⟩ ⟨(v.1, (S k).head?, v.2.2), S⟩ 1 := Eval.peek _ _ _ _ _

theorem ppO_eval (k : K) (v : XReg) (S : K → List Sym) (x : Sym) (L : List Sym)
    (h : S k = x :: L) : Eval [] (ppO k) ⟨v, S⟩ ⟨(some x, v.2), Function.update S k L⟩ 1 :=
  eval_pop_cons [] k _ v S x L h

theorem pd_eval (k : K) (v : XReg) (S : K → List Sym) (x : Sym) (L : List Sym)
    (h : S k = x :: L) : Eval [] (pd k) ⟨v, S⟩ ⟨v, Function.update S k L⟩ 1 :=
  eval_pop_cons [] k _ v S x L h

theorem pc_eval (k : K) (x : Sym) (v : XReg) (S : K → List Sym) :
    Eval [] (pc k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 := Eval.push _ _ _ _ _

end Atoms

/-! ## Programs -/

section Programs

variable {K : Type}

/-- Phase Z: one leading zero (consumes a shift token and a room token). -/
def zBody (kT kD kD' kU kU' : K) : XProg K :=
  .seq (pc kT (.bit false)) (.seq (pd kD) (.seq (pc kD' (.bit true)) (.seq (pd kU)
    (.seq (pc kU' (.bit true)) (.seq (pkO kD) (pkP kU))))))

/-- Phase Z loop. -/
def zLoop (kT kD kD' kU kU' : K) : XProg K := .loop bothBits (zBody kT kD kD' kU kU')

/-- Phase S: skip one input bit (consumes a shift token). -/
def sBody (kX kD kD' : K) : XProg K :=
  .seq (ppO kX) (.seq setLb (.seq (pd kD) (.seq (pc kD' (.bit true)) (.seq (pkO kD) (pkP kX)))))

/-- Phase S loop. -/
def sLoop (kX kD kD' : K) : XProg K := .loop bothBits (sBody kX kD kD')

/-- Phase C: copy one input bit (consumes a room token). -/
def cBody (kX kT kU kU' : K) : XProg K :=
  .seq (ppO kX) (.seq setLb (.seq (pushLb kT) (.seq (pd kU) (.seq (pc kU' (.bit true))
    (.seq (pkO kU) (pkP kX))))))

/-- Phase C loop. -/
def cLoop (kX kT kU kU' : K) : XProg K := .loop bothBits (cBody kX kT kU kU')

/-- Phase E: one copy of the last bit read (consumes a room token). -/
def eBody (kT kU kU' : K) : XProg K :=
  .seq (pushLb kT) (.seq (pd kU) (.seq (pc kU' (.bit true)) (pkO kU)))

/-- Phase E loop. -/
def eLoop (kT kU kU' : K) : XProg K := .loop oBit (eBody kT kU kU')

/-- Drop loop. -/
def dropLoop (k : K) : XProg K := .loop oBit (.seq (pd k) (pkO k))

/-- Drop the bit block on top of `k`. -/
def dropBits (k : K) : XProg K := .seq (pkO k) (dropLoop k)

/-- The common tail of one record: phases C, E, X, the record end, and the counter restores. -/
def recTailX (kX kT kU kU' kD kD' : K) : XProg K :=
  .seq (pkO kU) (.seq (pkP kX) (.seq (cLoop kX kT kU kU')
  (.seq (pkO kU) (.seq (eLoop kT kU kU')
  (.seq (dropBits kX)
  (.seq (pd kX) (.seq (pc kT .sep)
  (.seq (liftX (moveBlock kU' kU)) (.seq (liftX (moveBlock kD' kD))
    (pkO kX))))))))))

/-- One record of the shift kernel: phase S (`t < 0`) or phase Z (`t ≥ 0`), then the tail. -/
def recBodyX (kX kT kU kU' kD kD' : K) : XProg K :=
  .seq (.ite isNg (.seq (pkO kD) (.seq (pkP kX) (sLoop kX kD kD')))
    (.seq (pkO kD) (.seq (pkP kU) (zLoop kT kD kD' kU kU'))))
  (recTailX kX kT kU kU' kD kD')

/-- The record loop of the shift kernel. -/
def recLoopX (kX kT kU kU' kD kD' : K) : XProg K := .loop oBit (recBodyX kX kT kU kU' kD kD')

/-- Unary expansion step: decrement the counter `kC` (temp `kM`), push a token on `kU`. -/
def uBody (kC kM kU : K) : XProg K := .seq (liftX (dec kC kM)) (.seq (pc kU (.bit true)) (pkO kC))

/-- Unary expansion loop. -/
def uLoop (kC kM kU : K) : XProg K := .loop oBit (uBody kC kM kU)

/-- Capped countdown step: decrement `kC`, move one symbol `kc → ks`, push a token on `kD`. -/
def capBody (kC kM kc ks kD : K) : XProg K :=
  .seq (liftX (dec kC kM)) (.seq (ppO kc) (.seq (pushO ks) (.seq (pc kD (.bit true))
    (.seq (pkO kC) (pkP kc)))))

/-- Capped countdown loop. -/
def capLoop (kC kM kc ks kD : K) : XProg K := .loop bothBits (capBody kC kM kc ks kD)

/-- Build the room counter: `U := w2` tokens, from the binary `w2` on `kW` (restored). -/
def buildU (kW kC kM kU : K) : XProg K :=
  .seq (pc kC .mark) (.seq (liftX (copyBlock kW kC kM)) (.seq (pkO kC) (uLoop kC kM kU)))

/-- Read the sign of `t` into `ng`. -/
def readSign (kTc : K) : XProg K :=
  .seq (pkO kTc) (.load fun v => (v.1, v.2.1, v.2.2.1, decide (v.1 = some .neg)))

/-- Build the shift counter `D := min(|t|, cap)` tokens (`cap = w1` if `t < 0`, else `w2`). -/
def buildD (kX kTc kC kM kU kU' kD : K) : XProg K :=
  .seq (pd kTc)
  (.seq (liftX (copyBlock kTc kC kM))
  (.seq (.push kTc fun v => if v.2.2.2 then .neg else .pos)
  (.seq (.ite isNg
      (.seq (pc kM .mark) (.seq (pkO kC) (.seq (pkP kX) (.seq (capLoop kC kM kX kM kD)
        (liftX (moveBits kM kX))))))
      (.seq (pkO kC) (.seq (pkP kU) (.seq (capLoop kC kM kU kU' kD)
        (liftX (moveBlock kU' kU))))))
    (dropBits kC))))

/-- Push the guards. -/
def setupX (kT kU kU' kD kD' : K) : XProg K :=
  .seq (pc kT .mark) (.seq (pc kU .mark) (.seq (pc kU' .mark) (.seq (pc kD .mark) (pc kD' .mark))))

/-- Drop the counters and the guards. -/
def cleanupX (kU kU' kD kD' kC : K) : XProg K :=
  .seq (dropBits kU) (.seq (pd kU) (.seq (dropBits kD) (.seq (pd kD) (.seq (pd kU')
    (.seq (pd kD') (pd kC))))))

/-- The shift kernel body, run when the source holds at least one record. -/
def shiftMain (kX kZ kW kTc kT kU kU' kD kD' kC kM : K) : XProg K :=
  .seq (setupX kT kU kU' kD kD')
  (.seq (buildU kW kC kM kU)
  (.seq (readSign kTc)
  (.seq (buildD kX kTc kC kM kU kU' kD)
  (.seq (pkO kX)
  (.seq (recLoopX kX kT kU kU' kD kD')
  (.seq (liftX (WP.W9comp.rewindTo kT kZ .mark))
    (cleanupX kU kU' kD kD' kC)))))))

/-- The shift kernel. -/
def shiftProg (kX kZ kW kTc kT kU kU' kD kD' kC kM : K) : XProg K :=
  .seq (pkO kX) (.ite oBit (shiftMain kX kZ kW kTc kT kU kU' kD kD' kC kM) skip)

theorem closed_shiftProg (kX kZ kW kTc kT kU kU' kD kD' kC kM : K) :
    (shiftProg kX kZ kW kTc kT kU kU' kD kD' kC kM).Closed := by
  simp [shiftProg, shiftMain, setupX, buildU, readSign, buildD, recLoopX, recBodyX, recTailX,
    cleanupX,
    zLoop, zBody, sLoop, sBody, cLoop, cBody, eLoop, eBody, dropBits, dropLoop, uLoop, uBody,
    capLoop, capBody, liftX, pkO, pkP, ppO, pd, pc, setLb, pushLb, pushO, Prog.Closed,
    Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs, dec, copyBlock, moveBlock, moveBits,
    moveBitsDup, restoreR, WP.W9comp.rewindTo, pushC, popR, pushR, peekR, scanLoop, scanBody,
    decFix, skip, moveBitsBody, dupBody, WP.W9comp.rewindBody]

end Programs

/-! ## Per-record loops: evaluation -/

section Loops

theorem st_eqX {K : Type} {v v' : XReg} {S S' : K → List Sym} (hv : v = v') (hS : S = S') :
    (⟨v, S⟩ : St K (fun _ => Sym) XReg) = ⟨v', S'⟩ := by
  subst hv; subst hS; rfl

variable {K : Type} [DecidableEq K]

theorem zLoop_eval {kT kD kD' kU kU' : K} (h1 : kT ≠ kD) (h2 : kT ≠ kD') (h3 : kT ≠ kU)
    (h4 : kT ≠ kU') (h5 : kD ≠ kD') (h6 : kD ≠ kU) (h7 : kD ≠ kU') (h8 : kD' ≠ kU)
    (h9 : kD' ≠ kU') (h10 : kU ≠ kU') :
    ∀ (d u : ℕ) (lb ng : Bool) (D0 U0 : List Sym) (S : K → List Sym), d ≤ u →
      S kD = toks d ++ Sym.mark :: D0 → S kU = toks u ++ Sym.mark :: U0 →
      Eval [] (zLoop kT kD kD' kU kU') ⟨((S kD).head?, (S kU).head?, lb, ng), S⟩
        ⟨(some Sym.mark, (toks (u - d) ++ Sym.mark :: U0).head?, lb, ng),
          Function.update (Function.update (Function.update (Function.update (Function.update S
            kT (List.replicate d (Sym.bit false) ++ S kT)) kD (Sym.mark :: D0))
            kD' (toks d ++ S kD')) kU (toks (u - d) ++ Sym.mark :: U0)) kU' (toks d ++ S kU')⟩
          (8 * d + 1)
  | 0, u, lb, ng, D0, U0, S, _, hD, hU => by
    have hD' : S kD = Sym.mark :: D0 := hD
    refine (Eval.loop_false ?_).of_eq (st_eqX ?_ ?_) rfl
    · show bothBits ((S kD).head?, (S kU).head?, lb, ng) = false
      rw [hD']
      rfl
    · rw [hD', hU, Nat.sub_zero]
      rfl
    · funext k
      simp only [Function.update_apply, List.replicate_zero, List.nil_append, Nat.sub_zero]
      split_ifs <;> simp_all [toks]
  | d + 1, u, lb, ng, D0, U0, S, hdu, hD, hU => by
    obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
    have hD' : S kD = Sym.bit true :: (toks d ++ Sym.mark :: D0) := hD
    have hU' : S kU = Sym.bit true :: (toks u' ++ Sym.mark :: U0) := hU
    set S5 := Function.update (Function.update (Function.update (Function.update
      (Function.update S kT (Sym.bit false :: S kT)) kD (toks d ++ Sym.mark :: D0))
      kD' (Sym.bit true :: S kD')) kU (toks u' ++ Sym.mark :: U0)) kU' (Sym.bit true :: S kU')
      with hS5
    have h5D : S5 kD = toks d ++ Sym.mark :: D0 := by
      rw [hS5, Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
        Function.update_self]
    have h5U : S5 kU = toks u' ++ Sym.mark :: U0 := by
      rw [hS5, Function.update_of_ne h10, Function.update_self]
    have e : Eval [] (zBody kT kD kD' kU kU') ⟨((S kD).head?, (S kU).head?, lb, ng), S⟩
        ⟨((S5 kD).head?, (S5 kU).head?, lb, ng), S5⟩ 7 := by
      refine (Eval.seq (Eval.push _ _ _ _ _) (Eval.seq (Eval.pop _ _ _ _ _)
        (Eval.seq (Eval.push _ _ _ _ _) (Eval.seq (Eval.pop _ _ _ _ _)
        (Eval.seq (Eval.push _ _ _ _ _) (Eval.seq (Eval.peek _ _ _ _ _)
          (Eval.peek _ _ _ _ _))))))).of_eq ?_ rfl
      rw [h5D, h5U, hS5]
      simp only [Function.update_apply, if_neg h1.symm, if_neg h3.symm, if_neg h6.symm,
        if_neg h8.symm, if_neg h10.symm, if_neg h7, if_neg h5, if_neg h6, if_neg h10,
        if_neg h7.symm, if_neg h5.symm, if_neg h2.symm, if_neg h4.symm, if_neg h9.symm, if_pos,
        hD', hU', List.tail_cons]
    have ih := zLoop_eval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 d u' lb ng D0 U0 S5 (by omega) h5D h5U
    refine (Eval.loop_true ?_ e ih).of_eq (st_eqX ?_ ?_) ?_
    · show bothBits ((S kD).head?, (S kU).head?, lb, ng) = true
      rw [hD', hU']
      rfl
    · rw [show u' + 1 - (d + 1) = u' - d by omega]
    · funext k
      simp only [hS5, Function.update_apply, toks_succ', replicate_succ_append',
        show u' + 1 - (d + 1) = u' - d by omega]
      split_ifs <;> simp_all
    · omega

theorem sLoop_eval {kX kD kD' : K} (h1 : kX ≠ kD) (h2 : kX ≠ kD') (h3 : kD ≠ kD') :
    ∀ (d : ℕ) (xs : List Bool) (lb ng : Bool) (D0 R : List Sym) (S : K → List Sym),
      d ≤ xs.length → S kD = toks d ++ Sym.mark :: D0 → S kX = xs.map Sym.bit ++ Sym.sep :: R →
      Eval [] (sLoop kX kD kD') ⟨((S kD).head?, (S kX).head?, lb, ng), S⟩
        ⟨(some Sym.mark, ((xs.drop d).map Sym.bit ++ Sym.sep :: R).head?,
            lastOr lb (xs.take d), ng),
          Function.update (Function.update (Function.update S
            kX ((xs.drop d).map Sym.bit ++ Sym.sep :: R)) kD (Sym.mark :: D0))
            kD' (toks d ++ S kD')⟩ (7 * d + 1)
  | 0, xs, lb, ng, D0, R, S, _, hD, hX => by
    have hD' : S kD = Sym.mark :: D0 := hD
    refine (Eval.loop_false ?_).of_eq (st_eqX ?_ ?_) rfl
    · show bothBits ((S kD).head?, (S kX).head?, lb, ng) = false
      rw [hD']
      rfl
    · rw [hD', hX, List.drop_zero, List.take_zero]
      rfl
    · funext k
      simp only [Function.update_apply, List.drop_zero]
      split_ifs <;> simp_all [toks]
  | d + 1, [], lb, ng, D0, R, S, hd, _, _ => by simp at hd
  | d + 1, x :: xs, lb, ng, D0, R, S, hd, hD, hX => by
    have hD' : S kD = Sym.bit true :: (toks d ++ Sym.mark :: D0) := hD
    have hX' : S kX = Sym.bit x :: (xs.map Sym.bit ++ Sym.sep :: R) := hX
    set S3 := Function.update (Function.update (Function.update S
      kX (xs.map Sym.bit ++ Sym.sep :: R)) kD (toks d ++ Sym.mark :: D0))
      kD' (Sym.bit true :: S kD') with hS3
    have h3D : S3 kD = toks d ++ Sym.mark :: D0 := by
      rw [hS3, Function.update_of_ne h3, Function.update_self]
    have h3X : S3 kX = xs.map Sym.bit ++ Sym.sep :: R := by
      rw [hS3, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
    have e : Eval [] (sBody kX kD kD') ⟨((S kD).head?, (S kX).head?, lb, ng), S⟩
        ⟨((S3 kD).head?, (S3 kX).head?, x, ng), S3⟩ 6 := by
      refine (Eval.seq (Eval.pop _ _ _ _ _) (Eval.seq (Eval.load _ _ _ _)
        (Eval.seq (Eval.pop _ _ _ _ _) (Eval.seq (Eval.push _ _ _ _ _)
        (Eval.seq (Eval.peek _ _ _ _ _) (Eval.peek _ _ _ _ _)))))).of_eq ?_ rfl
      rw [h3D, h3X, hS3]
      simp only [Function.update_apply, if_neg h1, if_neg h2, if_neg h3, if_neg h1.symm,
        if_neg h2.symm, if_neg h3.symm, if_pos, hD', hX', List.tail_cons, List.head?_cons,
        optBit_some_bit]
    have ih := sLoop_eval h1 h2 h3 d xs x ng D0 R S3 (by simp at hd; omega) h3D h3X
    refine (Eval.loop_true ?_ e ih).of_eq (st_eqX ?_ ?_) ?_
    · show bothBits ((S kD).head?, (S kX).head?, lb, ng) = true
      rw [hD', hX']
      rfl
    · rw [List.drop_succ_cons, List.take_succ_cons, lastOr_cons]
    · funext k
      simp only [hS3, Function.update_apply, toks_succ', List.drop_succ_cons]
      split_ifs <;> simp_all
    · omega

theorem cLoop_eval {kX kT kU kU' : K} (h1 : kX ≠ kT) (h2 : kX ≠ kU) (h3 : kX ≠ kU')
    (h4 : kT ≠ kU) (h5 : kT ≠ kU') (h6 : kU ≠ kU') :
    ∀ (ys : List Bool) (u : ℕ) (lb ng : Bool) (U0 R : List Sym) (S : K → List Sym),
      S kU = toks u ++ Sym.mark :: U0 → S kX = ys.map Sym.bit ++ Sym.sep :: R →
      Eval [] (cLoop kX kT kU kU') ⟨((S kU).head?, (S kX).head?, lb, ng), S⟩
        ⟨((toks (u - min u ys.length) ++ Sym.mark :: U0).head?,
          ((ys.drop (min u ys.length)).map Sym.bit ++ Sym.sep :: R).head?,
          lastOr lb (ys.take (min u ys.length)), ng),
          Function.update (Function.update (Function.update (Function.update S
            kX ((ys.drop (min u ys.length)).map Sym.bit ++ Sym.sep :: R))
            kT ((ys.take (min u ys.length)).reverse.map Sym.bit ++ S kT))
            kU (toks (u - min u ys.length) ++ Sym.mark :: U0))
            kU' (toks (min u ys.length) ++ S kU')⟩ (8 * min u ys.length + 1)
  | [], u, lb, ng, U0, R, S, hU, hX => by
    have hX' : S kX = Sym.sep :: R := hX
    have hm : min u ([] : List Bool).length = 0 := by simp
    rw [hm]
    refine (Eval.loop_false ?_).of_eq (st_eqX ?_ ?_) rfl
    · show bothBits ((S kU).head?, (S kX).head?, lb, ng) = false
      rw [hX']
      simp [bothBits, optIsBit]
    · rw [hU, hX', Nat.sub_zero]
      rfl
    · funext k
      simp only [Function.update_apply, List.drop_zero, List.take_zero, Nat.sub_zero]
      split_ifs <;> simp_all [toks]
  | y :: ys, 0, lb, ng, U0, R, S, hU, hX => by
    have hU' : S kU = Sym.mark :: U0 := hU
    have hm : min 0 (y :: ys).length = 0 := by simp
    rw [hm]
    refine (Eval.loop_false ?_).of_eq (st_eqX ?_ ?_) rfl
    · show bothBits ((S kU).head?, (S kX).head?, lb, ng) = false
      rw [hU']
      rfl
    · rw [hU', hX]
      rfl
    · funext k
      simp only [Function.update_apply, List.drop_zero, List.take_zero, Nat.sub_zero]
      split_ifs <;> simp_all [toks]
  | y :: ys, u + 1, lb, ng, U0, R, S, hU, hX => by
    have hU' : S kU = Sym.bit true :: (toks u ++ Sym.mark :: U0) := hU
    have hX' : S kX = Sym.bit y :: (ys.map Sym.bit ++ Sym.sep :: R) := hX
    have hm : min (u + 1) (y :: ys).length = min u ys.length + 1 := by
      rw [List.length_cons]
      omega
    set S4 := Function.update (Function.update (Function.update (Function.update S
      kX (ys.map Sym.bit ++ Sym.sep :: R)) kT (Sym.bit y :: S kT))
      kU (toks u ++ Sym.mark :: U0)) kU' (Sym.bit true :: S kU') with hS4
    have h4U : S4 kU = toks u ++ Sym.mark :: U0 := by
      rw [hS4, Function.update_of_ne h6, Function.update_self]
    have h4X : S4 kX = ys.map Sym.bit ++ Sym.sep :: R := by
      rw [hS4, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
        Function.update_self]
    have e : Eval [] (cBody kX kT kU kU') ⟨((S kU).head?, (S kX).head?, lb, ng), S⟩
        ⟨((S4 kU).head?, (S4 kX).head?, y, ng), S4⟩ 7 := by
      refine (Eval.seq (Eval.pop _ _ _ _ _) (Eval.seq (Eval.load _ _ _ _)
        (Eval.seq (Eval.push _ _ _ _ _) (Eval.seq (Eval.pop _ _ _ _ _)
        (Eval.seq (Eval.push _ _ _ _ _) (Eval.seq (Eval.peek _ _ _ _ _)
          (Eval.peek _ _ _ _ _))))))).of_eq ?_ rfl
      rw [h4U, h4X, hS4]
      simp only [Function.update_apply, if_neg h1, if_neg h2, if_neg h3,
        if_neg h6, if_neg h1.symm, if_neg h2.symm, if_neg h3.symm, if_neg h4.symm,
        if_neg h5.symm, if_neg h6.symm, if_pos, hU', hX', List.tail_cons, List.head?_cons,
        optBit_some_bit]
    have ih := cLoop_eval h1 h2 h3 h4 h5 h6 ys u y ng U0 R S4 h4U h4X
    rw [hm]
    refine (Eval.loop_true ?_ e ih).of_eq (st_eqX ?_ ?_) ?_
    · show bothBits ((S kU).head?, (S kX).head?, lb, ng) = true
      rw [hU', hX']
      rfl
    · rw [List.drop_succ_cons, List.take_succ_cons, lastOr_cons,
        show u + 1 - (min u ys.length + 1) = u - min u ys.length by omega]
    · funext k
      simp only [hS4, Function.update_apply, toks_succ', List.drop_succ_cons, List.take_succ_cons,
        List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append, show u + 1 - (min u ys.length + 1) = u - min u ys.length by omega]
      split_ifs <;> simp_all
    · omega

theorem eLoop_eval {kT kU kU' : K} (h1 : kT ≠ kU) (h2 : kT ≠ kU') (h3 : kU ≠ kU') :
    ∀ (u : ℕ) (p : Option Sym) (lb ng : Bool) (U0 : List Sym) (S : K → List Sym),
      S kU = toks u ++ Sym.mark :: U0 →
      Eval [] (eLoop kT kU kU') ⟨((S kU).head?, p, lb, ng), S⟩
        ⟨(some Sym.mark, p, lb, ng), Function.update (Function.update (Function.update S
          kT (List.replicate u (Sym.bit lb) ++ S kT)) kU (Sym.mark :: U0)) kU' (toks u ++ S kU')⟩
        (5 * u + 1)
  | 0, p, lb, ng, U0, S, hU => by
    have hU' : S kU = Sym.mark :: U0 := hU
    refine (Eval.loop_false ?_).of_eq (st_eqX ?_ ?_) rfl
    · show oBit ((S kU).head?, p, lb, ng) = false
      rw [hU']
      rfl
    · rw [hU']
      rfl
    · funext k
      simp only [Function.update_apply, List.replicate_zero, List.nil_append]
      split_ifs <;> simp_all [toks]
  | u + 1, p, lb, ng, U0, S, hU => by
    have hU' : S kU = Sym.bit true :: (toks u ++ Sym.mark :: U0) := hU
    set S3 := Function.update (Function.update (Function.update S
      kT (Sym.bit lb :: S kT)) kU (toks u ++ Sym.mark :: U0)) kU' (Sym.bit true :: S kU')
      with hS3
    have h3U : S3 kU = toks u ++ Sym.mark :: U0 := by
      rw [hS3, Function.update_of_ne h3, Function.update_self]
    have e : Eval [] (eBody kT kU kU') ⟨((S kU).head?, p, lb, ng), S⟩
        ⟨((S3 kU).head?, p, lb, ng), S3⟩ 4 := by
      refine (Eval.seq (Eval.push _ _ _ _ _) (Eval.seq (Eval.pop _ _ _ _ _)
        (Eval.seq (Eval.push _ _ _ _ _) (Eval.peek _ _ _ _ _)))).of_eq ?_ rfl
      rw [h3U, hS3]
      simp only [Function.update_apply, if_neg h3, if_neg h1.symm,
        if_neg h2.symm, if_neg h3.symm, if_pos, hU', List.tail_cons]
    have ih := eLoop_eval h1 h2 h3 u p lb ng U0 S3 h3U
    refine (Eval.loop_true ?_ e ih).of_eq (st_eqX rfl ?_) ?_
    · show oBit ((S kU).head?, p, lb, ng) = true
      rw [hU']
      rfl
    · funext k
      simp only [hS3, Function.update_apply, toks_succ', replicate_succ_append']
      split_ifs <;> simp_all
    · omega

theorem dropLoop_eval (k : K) :
    ∀ (bs : List Bool) (rest : List Sym) (p : Option Sym) (lb ng : Bool) (S : K → List Sym),
      TermOK rest → S k = bs.map Sym.bit ++ rest →
      Eval [] (dropLoop k) ⟨((S k).head?, p, lb, ng), S⟩
        ⟨(rest.head?, p, lb, ng), Function.update S k rest⟩ (3 * bs.length + 1)
  | [], rest, p, lb, ng, S, hr, hS => by
    have hS' : S k = rest := hS
    refine (Eval.loop_false ?_).of_eq (st_eqX ?_ ?_) rfl
    · show oBit ((S k).head?, p, lb, ng) = false
      rw [hS']
      exact optIsBit_head?_of_termOK hr
    · rw [hS']
    · rw [update_eq_of_eq hS']
  | b :: bs, rest, p, lb, ng, S, hr, hS => by
    have hS' : S k = Sym.bit b :: (bs.map Sym.bit ++ rest) := hS
    have e : Eval [] (.seq (pd k) (pkO k)) ⟨((S k).head?, p, lb, ng), S⟩
        ⟨(((Function.update S k (bs.map Sym.bit ++ rest)) k).head?, p, lb, ng),
          Function.update S k (bs.map Sym.bit ++ rest)⟩ 2 :=
      Eval.seq (pd_eval k _ S _ _ hS') (pkO_eval k _ _)
    have ih := dropLoop_eval k bs rest p lb ng (Function.update S k (bs.map Sym.bit ++ rest)) hr
      (Function.update_self _ _ _)
    refine (Eval.loop_true ?_ e ih).of_eq (st_eqX rfl ?_) ?_
    · show oBit ((S k).head?, p, lb, ng) = true
      rw [hS']
      rfl
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

theorem dropBits_eval (k : K) (bs : List Bool) (rest : List Sym) (o p : Option Sym) (lb ng : Bool)
    (S : K → List Sym) (hr : TermOK rest) (hS : S k = bs.map Sym.bit ++ rest) :
    Eval [] (dropBits k) ⟨(o, p, lb, ng), S⟩
      ⟨(rest.head?, p, lb, ng), Function.update S k rest⟩ (3 * bs.length + 2) :=
  (Eval.seq (pkO_eval k _ S) (dropLoop_eval k bs rest p lb ng S hr hS)).of_eq rfl (by omega)

end Loops

end SubNLogN.Machine.K1.ShiftAux
