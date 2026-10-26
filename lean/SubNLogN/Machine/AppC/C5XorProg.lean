/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Leaves
import SubNLogN.Machine.K1.AddSub
import WP.W9comp.Kit

/-!
# `SubNLogN.Machine.AppC.C5XorProg`: programs and loops of the XOR gate (Proposition A.7 leaf L3)

Paper: Proposition A.7 (`prop:transfer11`) (the bit-network gates over
`𝔽₂`); contract `C5XorStmt` (`AppC/C5Leaves.lean`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

## Plan (program design, invariants, cost)
Layout `XK = KLoc (Fin 2) (Fin 2)`: named `a` (target), `b` (source); private: the output
buffer `T` and the copy buffer `T2` of `b`. Registers `o × p` (two symbol slots).
* Bit step (`bitBodyX`): pop the next bit `x` of `a` into `o` and `y` of `b` into `p`, push
  `x xor y` on `T` and `y` on `T2`, peek `a`. The bit loop runs while `a` shows a bit; the two
  records have the same width, so `b` shows its record end at the same time.
* Record (`recBodyX`): the bit loop, then pop both record ends, push `sep` on `T` and `T2`.
  The record loop runs while `a` shows a bit or `sep` (`BlkTerm ra` stops it).
* Main: guards `mark` on `T`, `T2`; the record loop; rewind `T` onto `a` (the reversal restores
  the record order) and `T2` onto `b` (restoring `b`).
* Cost: `6` per bit, `7` per record end, `3` per symbol per rewind: `C·(vol a + vol b + 1)`.

**Scope.** Programs and their evaluation lemmas (no `sorry`). Helpers live in
`SubNLogN.Machine.C5.XorAux`.
-/

namespace SubNLogN.Machine.C5.XorAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1.AddSubAux

/-! ## Registers, atoms, layout -/

/-- Registers: two symbol slots `o`, `p`. -/
abbrev XoReg : Type := Option Sym × Option Sym

/-- Programs of the XOR gate. -/
abbrev XoProg (K : Type) : Type := Prog K (fun _ => Sym) XoReg

/-- Lens onto the slot `o`, to run `TMFw.Lib` routines. -/
def lensXo : Lens XoReg (Option Sym) := Lens.fst _ _

/-- Run a `TMFw.Lib` routine on the slot `o`. -/
def liftXo {K : Type} (p : SProg K) : XoProg K := p.liftRegs lensXo

section Atoms

variable {K : Type}

/-- Peek `k` into `o`. -/
def xpkO (k : K) : XoProg K := .peek k fun v o => (o, v.2)
/-- Pop `k` into `o`. -/
def xppO (k : K) : XoProg K := .pop k fun v o => (o, v.2)
/-- Pop `k` into `p`. -/
def xppP (k : K) : XoProg K := .pop k fun v o => (v.1, o)
/-- Pop `k`, discarding the symbol. -/
def xpd (k : K) : XoProg K := .pop k fun v _ => v
/-- Push a constant on `k`. -/
def xpc (k : K) (x : Sym) : XoProg K := .push k fun _ => x
/-- Push `(bit in o) xor (bit in p)` on `k`. -/
def xpushX (k : K) : XoProg K := .push k fun v => .bit (Bool.xor (optBit v.1) (optBit v.2))
/-- Push the bit in `p` on `k`. -/
def xpushP (k : K) : XoProg K := .push k fun v => .bit (optBit v.2)
/-- The slot `o` holds a bit. -/
def xoBit (v : XoReg) : Bool := optIsBit v.1
/-- A record starts here: the slot `o` holds a bit or a record end. -/
def xisRec (v : XoReg) : Bool := optIsBit v.1 || decide (v.1 = some Sym.sep)

theorem st_eqX' {v v' : XoReg} {S S' : K → List Sym} (hv : v = v') (hS : S = S') :
    (⟨v, S⟩ : St K (fun _ => Sym) XoReg) = ⟨v', S'⟩ := by
  subst hv; subst hS; rfl

variable [DecidableEq K]

theorem xpkO_eval (k : K) (v : XoReg) (S : K → List Sym) :
    Eval [] (xpkO k) ⟨v, S⟩ ⟨((S k).head?, v.2), S⟩ 1 := Eval.peek _ _ _ _ _

theorem xpc_eval (k : K) (x : Sym) (v : XoReg) (S : K → List Sym) :
    Eval [] (xpc k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 := Eval.push _ _ _ _ _

theorem xpd_eval (k : K) (v : XoReg) (S : K → List Sym) (x : Sym) (L : List Sym)
    (h : S k = x :: L) : Eval [] (xpd k) ⟨v, S⟩ ⟨v, Function.update S k L⟩ 1 :=
  eval_pop_cons [] k _ v S x L h

end Atoms

/-- Stacks: two named (`a`, `b`) and two private (`T`, `T2`). -/
abbrev XK : Type := KLoc (Fin 2) (Fin 2)

/-- Target array `a`. -/
abbrev xkA : XK := .inl 0
/-- Source array `b`. -/
abbrev xkB : XK := .inl 1
/-- Output buffer. -/
abbrev xkT : XK := .inr 0
/-- Copy buffer of `b`. -/
abbrev xkT2 : XK := .inr 1

/-! ## Programs -/

/-- One bit step. -/
def bitBodyX : XoProg XK :=
  .seq (xppO xkA) (.seq (xppP xkB) (.seq (xpushX xkT) (.seq (xpushP xkT2) (xpkO xkA))))

/-- The bits of one record (while `a` shows a bit). -/
def bitLoopX : XoProg XK := .loop xoBit bitBodyX

/-- One record: its bits, then its end. -/
def recBodyX : XoProg XK :=
  .seq bitLoopX (.seq (xpd xkA) (.seq (xpd xkB) (.seq (xpc xkT .sep) (.seq (xpc xkT2 .sep)
    (xpkO xkA)))))

/-- The record loop. -/
def recLoopX : XoProg XK := .loop xisRec recBodyX

/-- The XOR gate. -/
def xMain : XoProg XK :=
  .seq (xpc xkT .mark) (.seq (xpc xkT2 .mark) (.seq (xpkO xkA) (.seq recLoopX
    (.seq (liftXo (WP.W9comp.rewindTo xkT xkA .mark))
      (liftXo (WP.W9comp.rewindTo xkT2 xkB .mark))))))

theorem closed_xMain : xMain.Closed := by
  simp [xMain, recLoopX, recBodyX, bitLoopX, bitBodyX, liftXo, xpkO, xppO, xppP, xpd, xpc,
    xpushX, xpushP, Prog.Closed, Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs,
    WP.W9comp.rewindTo, WP.W9comp.rewindBody, pushR, popR]

/-! ## Volumes -/

theorem volX_cons (q : List Bool) (a : List (List Bool)) : vol (q :: a) = q.length + 1 + vol a := by
  simp only [vol, arrSyms_cons, recSyms, List.length_append, List.length_map,
    List.length_singleton]

theorem vol_xorArr (w : ℕ) :
    ∀ (a b : List (List Bool)), a.length = b.length → (∀ q ∈ a, q.length = w) →
      (∀ q ∈ b, q.length = w) → vol (xorArr a b) = vol a
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | q :: a, r :: b, h, ha, hb => by
    have ih := vol_xorArr w a b (by simpa using h) (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    have hq := ha q List.mem_cons_self
    have hr := hb r List.mem_cons_self
    simp only [xorArr, List.zipWith_cons_cons] at ih ⊢
    rw [volX_cons, volX_cons, ih, List.length_zipWith, hq, hr, min_self]

/-! ## The bit loop and the record loop -/

theorem bitLoopX_eval (RA RB : List Sym) :
    ∀ (xs ys : List Bool) (p : Option Sym) (S : XK → List Sym), xs.length = ys.length →
      S xkA = xs.map Sym.bit ++ Sym.sep :: RA → S xkB = ys.map Sym.bit ++ Sym.sep :: RB →
      ∃ v' : XoReg, Eval [] bitLoopX ⟨((S xkA).head?, p), S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update S
          xkA (Sym.sep :: RA)) xkB (Sym.sep :: RB))
          xkT ((List.zipWith Bool.xor xs ys).reverse.map Sym.bit ++ S xkT))
          xkT2 (ys.reverse.map Sym.bit ++ S xkT2)⟩ (6 * xs.length + 1)
  | [], [], p, S, _, hA, hB => by
    have hA' : S xkA = Sym.sep :: RA := hA
    have hB' : S xkB = Sym.sep :: RB := hB
    refine ⟨_, (Eval.loop_false ?_).of_eq (st_eqX' rfl ?_) rfl⟩
    · show xoBit ((S xkA).head?, p) = false
      rw [hA']
      rfl
    · simp only [List.zipWith_nil_left, List.reverse_nil, List.map_nil, List.nil_append]
      rw [update_eq_of_eq hA', update_eq_of_eq hB', Function.update_eq_self,
        Function.update_eq_self]
  | [], _ :: _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | x :: xs, y :: ys, p, S, hlen, hA, hB => by
    have hA' : S xkA = Sym.bit x :: (xs.map Sym.bit ++ Sym.sep :: RA) := hA
    have hB' : S xkB = Sym.bit y :: (ys.map Sym.bit ++ Sym.sep :: RB) := hB
    have e1 := eval_pop_cons [] xkA (fun (v : XoReg) o => (o, v.2)) ((S xkA).head?, p) S
      (Sym.bit x) _ hA'
    set S1 := Function.update S xkA (xs.map Sym.bit ++ Sym.sep :: RA) with hS1
    have h1B : S1 xkB = Sym.bit y :: (ys.map Sym.bit ++ Sym.sep :: RB) := by simp [hS1, hB']
    have e2 := eval_pop_cons [] xkB (fun (v : XoReg) o => (v.1, o)) (some (Sym.bit x), p) S1
      (Sym.bit y) _ h1B
    set S2 := Function.update S1 xkB (ys.map Sym.bit ++ Sym.sep :: RB) with hS2
    have e3 := Eval.push [] xkT (fun (v : XoReg) => Sym.bit (Bool.xor (optBit v.1) (optBit v.2)))
      (some (Sym.bit x), some (Sym.bit y)) S2
    have h2T : S2 xkT = S xkT := by simp [hS2, hS1]
    rw [h2T] at e3
    set S3 := Function.update S2 xkT (Sym.bit (Bool.xor x y) :: S xkT) with hS3
    have e4 := Eval.push [] xkT2 (fun (v : XoReg) => Sym.bit (optBit v.2))
      (some (Sym.bit x), some (Sym.bit y)) S3
    have h3T2 : S3 xkT2 = S xkT2 := by simp [hS3, hS2, hS1]
    rw [h3T2] at e4
    set S4 := Function.update S3 xkT2 (Sym.bit y :: S xkT2) with hS4
    have e5 := xpkO_eval xkA (some (Sym.bit x), some (Sym.bit y)) S4
    obtain ⟨v', ih⟩ := bitLoopX_eval RA RB xs ys (some (Sym.bit y)) S4 (by simpa using hlen)
      (by simp [hS4, hS3, hS2, hS1]) (by simp [hS4, hS3, hS2])
    have h4T : S4 xkT = Sym.bit (Bool.xor x y) :: S xkT := by simp [hS4, hS3]
    have h4T2 : S4 xkT2 = Sym.bit y :: S xkT2 := by simp [hS4]
    rw [h4T, h4T2] at ih
    refine ⟨v', (Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))))
      ih).of_eq (st_eqX' rfl ?_) ?_⟩
    · show xoBit ((S xkA).head?, p) = true
      rw [hA']
      rfl
    · clear e1 e2 e3 e4 e5 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS4, hS3, hS2, hS1, List.zipWith_cons_cons, List.reverse_cons]
    · simp only [List.length_cons]
      omega

theorem xisRec_of_blkTerm {RA : List Sym} (h : BlkTerm RA) (p : Option Sym) :
    xisRec (RA.head?, p) = false := by
  cases RA with
  | nil => rfl
  | cons d l =>
    obtain ⟨h1, h2⟩ := h d rfl
    cases d <;> simp_all [xisRec, optIsBit, isDataSym]

theorem recLoopX_eval (w : ℕ) (RA RB : List Sym) (hRA : BlkTerm RA) :
    ∀ (a b : List (List Bool)) (o p : Option Sym) (S : XK → List Sym),
      a.length = b.length → (∀ q ∈ a, q.length = w) → (∀ q ∈ b, q.length = w) →
      S xkA = arrSyms a ++ RA → S xkB = arrSyms b ++ RB → o = (S xkA).head? →
      ∃ (v' : XoReg) (t : ℕ), t ≤ 7 * vol a + 1 ∧
        Eval [] recLoopX ⟨(o, p), S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S
            xkA RA) xkB RB) xkT ((arrSyms (xorArr a b)).reverse ++ S xkT))
            xkT2 ((arrSyms b).reverse ++ S xkT2)⟩ t
  | [], [], o, p, S, _, _, _, hA, hB, ho => by
    have hA' : S xkA = RA := hA
    have hB' : S xkB = RB := hB
    refine ⟨_, 1, by omega, (Eval.loop_false ?_).of_eq (st_eqX' rfl ?_) rfl⟩
    · rw [ho, hA']
      exact xisRec_of_blkTerm hRA p
    · simp only [xorArr, List.zipWith_nil_left, arrSyms_nil, List.reverse_nil, List.nil_append]
      rw [update_eq_of_eq hA', update_eq_of_eq hB', Function.update_eq_self,
        Function.update_eq_self]
  | [], _ :: _, _, _, _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _, _, _ => by simp at h
  | q :: a, r :: b, o, p, S, hlen, ha, hb, hA, hB, ho => by
    subst ho
    have hq := ha q List.mem_cons_self
    have hr := hb r List.mem_cons_self
    have hA' : S xkA = q.map Sym.bit ++ Sym.sep :: (arrSyms a ++ RA) := by
      rw [hA, arrSyms_cons, List.append_assoc, recSyms_append]
    have hB' : S xkB = r.map Sym.bit ++ Sym.sep :: (arrSyms b ++ RB) := by
      rw [hB, arrSyms_cons, List.append_assoc, recSyms_append]
    obtain ⟨⟨o1, p1⟩, e1⟩ := bitLoopX_eval (arrSyms a ++ RA) (arrSyms b ++ RB) q r p S
      (by rw [hq, hr]) hA' hB'
    set S1 := Function.update (Function.update (Function.update (Function.update S
      xkA (Sym.sep :: (arrSyms a ++ RA))) xkB (Sym.sep :: (arrSyms b ++ RB)))
      xkT ((List.zipWith Bool.xor q r).reverse.map Sym.bit ++ S xkT))
      xkT2 (r.reverse.map Sym.bit ++ S xkT2) with hS1
    have e2 := xpd_eval xkA (o1, p1) S1 Sym.sep (arrSyms a ++ RA) (by simp [hS1])
    set S2 := Function.update S1 xkA (arrSyms a ++ RA) with hS2
    have e3 := xpd_eval xkB (o1, p1) S2 Sym.sep (arrSyms b ++ RB) (by simp [hS2, hS1])
    set S3 := Function.update S2 xkB (arrSyms b ++ RB) with hS3
    have e4 := xpc_eval xkT Sym.sep (o1, p1) S3
    have h3T : S3 xkT = (List.zipWith Bool.xor q r).reverse.map Sym.bit ++ S xkT := by
      simp [hS3, hS2, hS1]
    rw [h3T] at e4
    set S4 := Function.update S3 xkT
      (Sym.sep :: ((List.zipWith Bool.xor q r).reverse.map Sym.bit ++ S xkT)) with hS4
    have e5 := xpc_eval xkT2 Sym.sep (o1, p1) S4
    have h4T2 : S4 xkT2 = r.reverse.map Sym.bit ++ S xkT2 := by simp [hS4, hS3, hS2, hS1]
    rw [h4T2] at e5
    set S5 := Function.update S4 xkT2 (Sym.sep :: (r.reverse.map Sym.bit ++ S xkT2)) with hS5
    have e6 := xpkO_eval xkA (o1, p1) S5
    obtain ⟨v', t, ht, ih⟩ := recLoopX_eval w RA RB hRA a b (S5 xkA).head? p1 S5
      (by simpa using hlen) (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      (by simp [hS5, hS4, hS3, hS2]) (by simp [hS5, hS4, hS3]) rfl
    have h5T : S5 xkT = Sym.sep :: ((List.zipWith Bool.xor q r).reverse.map Sym.bit ++
        S xkT) := by
      simp [hS5, hS4]
    have h5T2 : S5 xkT2 = Sym.sep :: (r.reverse.map Sym.bit ++ S xkT2) := by simp [hS5]
    rw [h5T, h5T2] at ih
    have hrec : xisRec ((S xkA).head?, p) = true := by
      rw [hA']
      cases q with
      | nil => rfl
      | cons x xs => rfl
    refine ⟨v', _, ?_, (Eval.loop_true hrec (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      (Eval.seq e5 e6))))) ih).of_eq (st_eqX' rfl ?_) rfl⟩
    · rw [volX_cons]
      omega
    · clear e1 e2 e3 e4 e5 e6 ih
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hS5, hS4, hS3, hS2, hS1, xorArr, arrSyms_cons, reverse_recSyms]

end SubNLogN.Machine.C5.XorAux
