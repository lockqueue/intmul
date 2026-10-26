/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.ShiftPre
import SubNLogN.Machine.Contracts.Arith

/-!
# `SubNLogN.Machine.Arith.CAddProg`: programs and per-field loops of the exact sum / difference

Paper: Lemma A.4(5) (`lem:transfer-streams`: "fixed-width coefficient
arithmetic uses ordinary carry scans"); contracts `CAddStmt`, `CSubStmt`
(`Contracts/Arith.lean`).

## Plan (program design, invariants, cost)
Registers `CReg = o × p × la × lb × c`: two symbol slots, the last bit read from each operand,
the carry. Unary rulers (runs of `bit true` above a `mark`): `R1` (`w1` tokens), `R2` (`w2`),
`R3` (`w3`) with used-token stacks `R1'`, `R2'`, `R3'`.
* One output step (`stepBody`): if `R1` has a token, pop the next bit of `u` into `la` (else
  keep `la`: sign extension); the same for `v` and `lb`; push the out bit of `f la lb c` on the
  output buffer `T`; update the carry; move one `R3` token. `stepLoop` runs `w3` steps.
* `dropTok`: discard the operand bits that were not read (when `w1 > w3`), one per token.
* `fieldC`: `c := false`; `stepLoop`; the two discards; restore the three rulers. Cost
  `O(w1 + w2 + w3)`.
Proved here: `readA_eval`, `readB_eval`, `stepLoop_eval`, `dropTok_eval`.

**Scope (honest summary).** Programs and proved evaluation lemmas only (no `sorry`). Helpers
live in `SubNLogN.Machine.Arith.CAddAux`.
-/

namespace SubNLogN.Machine.Arith.CAddAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux

/-! ## Registers and atoms -/

/-- Registers: slots `o`, `p`, the last bit of `a`, the last bit of `b`, the carry. -/
abbrev CReg : Type := Option Sym × Option Sym × Bool × Bool × Bool

/-- Programs of the sum / difference kernels. -/
abbrev CProg (K : Type) : Type := Prog K (fun _ => Sym) CReg

/-- Lens onto the first four registers, to run the `K1.ShiftAux` programs (`XReg`). -/
def lensC : Lens CReg XReg where
  get v := (v.1, v.2.1, v.2.2.1, v.2.2.2.1)
  set v w := (w.1, w.2.1, w.2.2.1, w.2.2.2, v.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the slot `o`, to run `TMFw.Lib` routines. -/
def lensCo : Lens CReg (Option Sym) := Lens.fst _ _

/-- Run a `K1.ShiftAux` program. -/
def liftC {K : Type} (p : XProg K) : CProg K := p.liftRegs lensC

/-- Run a `TMFw.Lib` routine on the slot `o`. -/
def liftCo {K : Type} (p : SProg K) : CProg K := p.liftRegs lensCo

section Atoms

variable {K : Type}

/-- Peek `k` into `o`. -/
def cpkO (k : K) : CProg K := .peek k fun v o => (o, v.2)
/-- Peek `k` into `p`. -/
def cpkP (k : K) : CProg K := .peek k fun v o => (v.1, o, v.2.2)
/-- Pop `k` into `o`. -/
def cppO (k : K) : CProg K := .pop k fun v o => (o, v.2)
/-- Pop `k`, discarding the symbol. -/
def cpd (k : K) : CProg K := .pop k fun v _ => v
/-- Push a constant on `k`. -/
def cpc (k : K) (x : Sym) : CProg K := .push k fun _ => x
/-- `la :=` the bit in `o`. -/
def setA : CProg K := .load fun v => (v.1, v.2.1, optBit v.1, v.2.2.2.1, v.2.2.2.2)
/-- `lb :=` the bit in `o`. -/
def setB : CProg K := .load fun v => (v.1, v.2.1, v.2.2.1, optBit v.1, v.2.2.2.2)
/-- Push the out bit of `f la lb c` on `k`. -/
def pushF (k : K) (f : Bool → Bool → Bool → Bool × Bool) : CProg K :=
  .push k fun v => .bit (f v.2.2.1 v.2.2.2.1 v.2.2.2.2).1
/-- `c :=` the carry of `f la lb c`. -/
def setCF (f : Bool → Bool → Bool → Bool × Bool) : CProg K :=
  .load fun v => (v.1, v.2.1, v.2.2.1, v.2.2.2.1, (f v.2.2.1 v.2.2.2.1 v.2.2.2.2).2)
/-- `c := false`. -/
def clrC : CProg K := .load fun v => (v.1, v.2.1, v.2.2.1, v.2.2.2.1, false)
/-- The slot `o` holds a bit. -/
def oBitC (v : CReg) : Bool := optIsBit v.1
/-- The slot `p` holds a bit. -/
def pBitC (v : CReg) : Bool := optIsBit v.2.1

variable [DecidableEq K]

theorem cpkO_eval (k : K) (v : CReg) (S : K → List Sym) :
    Eval [] (cpkO k) ⟨v, S⟩ ⟨((S k).head?, v.2), S⟩ 1 := Eval.peek _ _ _ _ _

theorem cpkP_eval (k : K) (v : CReg) (S : K → List Sym) :
    Eval [] (cpkP k) ⟨v, S⟩ ⟨(v.1, (S k).head?, v.2.2), S⟩ 1 := Eval.peek _ _ _ _ _

theorem cpd_eval (k : K) (v : CReg) (S : K → List Sym) (x : Sym) (L : List Sym)
    (h : S k = x :: L) : Eval [] (cpd k) ⟨v, S⟩ ⟨v, Function.update S k L⟩ 1 :=
  eval_pop_cons [] k _ v S x L h

theorem cpc_eval (k : K) (x : Sym) (v : CReg) (S : K → List Sym) :
    Eval [] (cpc k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 := Eval.push _ _ _ _ _

end Atoms

/-! ## Programs -/

section Programs

variable {K : Type}

/-- Read the next bit of `u` into `la` if the ruler `R` has a token (else keep `la`). -/
def readA (kU kR kR' : K) : CProg K :=
  .seq (cpkO kR) (.ite oBitC (.seq (cppO kU) (.seq setA (.seq (cpd kR) (cpc kR' (.bit true)))))
    skip)

/-- Read the next bit of `v` into `lb` if the ruler `R` has a token (else keep `lb`). -/
def readB (kV kR kR' : K) : CProg K :=
  .seq (cpkO kR) (.ite oBitC (.seq (cppO kV) (.seq setB (.seq (cpd kR) (cpc kR' (.bit true)))))
    skip)

/-- One output step. -/
def stepBody (kU kV kT kR1 kR1' kR2 kR2' kR3 kR3' : K) (f : Bool → Bool → Bool → Bool × Bool) :
    CProg K :=
  .seq (readA kU kR1 kR1') (.seq (readB kV kR2 kR2') (.seq (pushF kT f) (.seq (setCF f)
    (.seq (cpd kR3) (.seq (cpc kR3' (.bit true)) (cpkP kR3))))))

/-- The output steps of one field (while `R3` has a token). -/
def stepLoop (kU kV kT kR1 kR1' kR2 kR2' kR3 kR3' : K) (f : Bool → Bool → Bool → Bool × Bool) :
    CProg K :=
  .loop pBitC (stepBody kU kV kT kR1 kR1' kR2 kR2' kR3 kR3' f)

/-- Discard one unread operand bit per remaining token of `R`. -/
def dropTok (kX kR kR' : K) : CProg K :=
  .seq (cpkO kR) (.loop oBitC (.seq (cpd kX) (.seq (cpd kR) (.seq (cpc kR' (.bit true))
    (cpkO kR)))))

/-- One field: the output steps, the discards, and the ruler restores. -/
def fieldC (kU kV kT kR1 kR1' kR2 kR2' kR3 kR3' : K) (f : Bool → Bool → Bool → Bool × Bool) :
    CProg K :=
  .seq clrC (.seq (cpkP kR3) (.seq (stepLoop kU kV kT kR1 kR1' kR2 kR2' kR3 kR3' f)
  (.seq (dropTok kU kR1 kR1') (.seq (dropTok kV kR2 kR2')
  (.seq (liftCo (moveBlock kR1' kR1)) (.seq (liftCo (moveBlock kR2' kR2))
    (liftCo (moveBlock kR3' kR3))))))))

end Programs

/-! ## Small loops: evaluation -/

section Loops

theorem st_eqC {K : Type} {v v' : CReg} {S S' : K → List Sym} (hv : v = v') (hS : S = S') :
    (⟨v, S⟩ : St K (fun _ => Sym) CReg) = ⟨v', S'⟩ := by
  subst hv; subst hS; rfl

variable {K : Type} [DecidableEq K]

theorem readA_eval {kU kR kR' : K} (hUR : kU ≠ kR) (hUR' : kU ≠ kR') (hRR' : kR ≠ kR')
    (xa : List Bool) (RU R0 : List Sym) (o p : Option Sym) (la lb c : Bool) (S : K → List Sym)
    (hU : S kU = xa.map Sym.bit ++ RU) (hR : S kR = toks xa.length ++ Sym.mark :: R0) :
    ∃ (o' : Option Sym) (t : ℕ), t ≤ 6 ∧ Eval [] (readA kU kR kR') ⟨(o, p, la, lb, c), S⟩
      ⟨(o', p, xa.headD la, lb, c), Function.update (Function.update (Function.update S
        kU (xa.tail.map Sym.bit ++ RU)) kR (toks xa.tail.length ++ Sym.mark :: R0))
        kR' (toks (xa.length - xa.tail.length) ++ S kR')⟩ t := by
  cases xa with
  | nil =>
    have hR2 : S kR = Sym.mark :: R0 := hR
    have hU2 : S kU = RU := hU
    refine ⟨_, 1 + (1 + 1), by norm_num, (Eval.seq (cpkO_eval kR _ S)
      (Eval.ite_false ?_ (skip_eval _ _))).of_eq (st_eqC rfl ?_) rfl⟩
    · show oBitC ((S kR).head?, p, la, lb, c) = false
      rw [hR2]
      rfl
    · simp only [List.tail_nil, List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero,
        toks, List.replicate_zero]
      rw [update_eq_of_eq hU2, update_eq_of_eq hR2, Function.update_eq_self]
  | cons x xa' =>
    have hU' : S kU = Sym.bit x :: (xa'.map Sym.bit ++ RU) := hU
    have hR' : S kR = Sym.bit true :: (toks xa'.length ++ Sym.mark :: R0) := hR
    have e1 := cpkO_eval kR (o, p, la, lb, c) S
    have e2 := eval_pop_cons [] kU (fun (v : CReg) o => (o, v.2)) ((S kR).head?, p, la, lb, c) S
      (Sym.bit x) _ hU'
    set S1 := Function.update S kU (xa'.map Sym.bit ++ RU) with hS1
    have e3 := Eval.load [] (fun (v : CReg) => (v.1, v.2.1, optBit v.1, v.2.2.2.1, v.2.2.2.2))
      (some (Sym.bit x), p, la, lb, c) S1
    have h1R : S1 kR = Sym.bit true :: (toks xa'.length ++ Sym.mark :: R0) := by
      rw [hS1, Function.update_of_ne hUR.symm, hR']
    have e4 := cpd_eval kR (some (Sym.bit x), p, x, lb, c) S1 _ _ h1R
    set S2 := Function.update S1 kR (toks xa'.length ++ Sym.mark :: R0) with hS2
    have e5 := cpc_eval kR' (Sym.bit true) (some (Sym.bit x), p, x, lb, c) S2
    have h2R' : S2 kR' = S kR' := by
      rw [hS2, Function.update_of_ne hRR'.symm, hS1, Function.update_of_ne hUR'.symm]
    rw [h2R'] at e5
    refine ⟨some (Sym.bit x), 1 + (1 + (1 + (1 + (1 + 1)))), le_refl _, (Eval.seq e1
      (Eval.ite_true ?_ (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))))).of_eq (st_eqC rfl ?_) rfl⟩
    · show oBitC ((S kR).head?, p, la, lb, c) = true
      rw [hR']
      rfl
    · simp only [List.tail_cons, List.length_cons, Nat.add_sub_cancel_left]
      rfl

theorem readB_eval {kV kR kR' : K} (hVR : kV ≠ kR) (hVR' : kV ≠ kR') (hRR' : kR ≠ kR')
    (xb : List Bool) (RV R0 : List Sym) (o p : Option Sym) (la lb c : Bool) (S : K → List Sym)
    (hV : S kV = xb.map Sym.bit ++ RV) (hR : S kR = toks xb.length ++ Sym.mark :: R0) :
    ∃ (o' : Option Sym) (t : ℕ), t ≤ 6 ∧ Eval [] (readB kV kR kR') ⟨(o, p, la, lb, c), S⟩
      ⟨(o', p, la, xb.headD lb, c), Function.update (Function.update (Function.update S
        kV (xb.tail.map Sym.bit ++ RV)) kR (toks xb.tail.length ++ Sym.mark :: R0))
        kR' (toks (xb.length - xb.tail.length) ++ S kR')⟩ t := by
  cases xb with
  | nil =>
    have hR2 : S kR = Sym.mark :: R0 := hR
    have hV2 : S kV = RV := hV
    refine ⟨_, 1 + (1 + 1), by norm_num, (Eval.seq (cpkO_eval kR _ S)
      (Eval.ite_false ?_ (skip_eval _ _))).of_eq (st_eqC rfl ?_) rfl⟩
    · show oBitC ((S kR).head?, p, la, lb, c) = false
      rw [hR2]
      rfl
    · simp only [List.tail_nil, List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero,
        toks, List.replicate_zero]
      rw [update_eq_of_eq hV2, update_eq_of_eq hR2, Function.update_eq_self]
  | cons x xb' =>
    have hV' : S kV = Sym.bit x :: (xb'.map Sym.bit ++ RV) := hV
    have hR' : S kR = Sym.bit true :: (toks xb'.length ++ Sym.mark :: R0) := hR
    have e1 := cpkO_eval kR (o, p, la, lb, c) S
    have e2 := eval_pop_cons [] kV (fun (v : CReg) o => (o, v.2)) ((S kR).head?, p, la, lb, c) S
      (Sym.bit x) _ hV'
    set S1 := Function.update S kV (xb'.map Sym.bit ++ RV) with hS1
    have e3 := Eval.load [] (fun (v : CReg) => (v.1, v.2.1, v.2.2.1, optBit v.1, v.2.2.2.2))
      (some (Sym.bit x), p, la, lb, c) S1
    have h1R : S1 kR = Sym.bit true :: (toks xb'.length ++ Sym.mark :: R0) := by
      rw [hS1, Function.update_of_ne hVR.symm, hR']
    have e4 := cpd_eval kR (some (Sym.bit x), p, la, x, c) S1 _ _ h1R
    set S2 := Function.update S1 kR (toks xb'.length ++ Sym.mark :: R0) with hS2
    have e5 := cpc_eval kR' (Sym.bit true) (some (Sym.bit x), p, la, x, c) S2
    have h2R' : S2 kR' = S kR' := by
      rw [hS2, Function.update_of_ne hRR'.symm, hS1, Function.update_of_ne hVR'.symm]
    rw [h2R'] at e5
    refine ⟨some (Sym.bit x), 1 + (1 + (1 + (1 + (1 + 1)))), le_refl _, (Eval.seq e1
      (Eval.ite_true ?_ (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))))).of_eq (st_eqC rfl ?_) rfl⟩
    · show oBitC ((S kR).head?, p, la, lb, c) = true
      rw [hR']
      rfl
    · simp only [List.tail_cons, List.length_cons, Nat.add_sub_cancel_left]
      rfl

/-- The discard loop: one unread bit of `X` per token of `R`. -/
theorem dropTokLoop_eval {kX kR kR' : K} (hXR : kX ≠ kR) (hXR' : kX ≠ kR') (hRR' : kR ≠ kR')
    (RX R0 : List Sym) :
    ∀ (xs : List Bool) (p : Option Sym) (la lb c : Bool) (S : K → List Sym),
      S kX = xs.map Sym.bit ++ RX → S kR = toks xs.length ++ Sym.mark :: R0 →
      Eval [] (.loop oBitC (.seq (cpd kX) (.seq (cpd kR) (.seq (cpc kR' (.bit true))
        (cpkO kR))))) ⟨((S kR).head?, p, la, lb, c), S⟩
        ⟨(some Sym.mark, p, la, lb, c), Function.update (Function.update (Function.update S
          kX RX) kR (Sym.mark :: R0)) kR' (toks xs.length ++ S kR')⟩ (5 * xs.length + 1)
  | [], p, la, lb, c, S, hX, hR => by
    have hX' : S kX = RX := hX
    have hR' : S kR = Sym.mark :: R0 := hR
    refine (Eval.loop_false ?_).of_eq (st_eqC ?_ ?_) rfl
    · show oBitC ((S kR).head?, p, la, lb, c) = false
      rw [hR']
      rfl
    · rw [hR']
      rfl
    · rw [update_eq_of_eq hX', update_eq_of_eq hR']
      simp [toks]
  | x :: xs, p, la, lb, c, S, hX, hR => by
    have hX' : S kX = Sym.bit x :: (xs.map Sym.bit ++ RX) := hX
    have hR' : S kR = Sym.bit true :: (toks xs.length ++ Sym.mark :: R0) := hR
    have e1 := cpd_eval kX ((S kR).head?, p, la, lb, c) S _ _ hX'
    set S1 := Function.update S kX (xs.map Sym.bit ++ RX) with hS1
    have h1R : S1 kR = Sym.bit true :: (toks xs.length ++ Sym.mark :: R0) := by
      rw [hS1, Function.update_of_ne hXR.symm, hR']
    have e2 := cpd_eval kR ((S kR).head?, p, la, lb, c) S1 _ _ h1R
    set S2 := Function.update S1 kR (toks xs.length ++ Sym.mark :: R0) with hS2
    have e3 := cpc_eval kR' (Sym.bit true) ((S kR).head?, p, la, lb, c) S2
    have h2R' : S2 kR' = S kR' := by
      rw [hS2, Function.update_of_ne hRR'.symm, hS1, Function.update_of_ne hXR'.symm]
    rw [h2R'] at e3
    set S3 := Function.update S2 kR' (Sym.bit true :: S kR') with hS3
    have e4 := cpkO_eval kR ((S kR).head?, p, la, lb, c) S3
    have h3X : S3 kX = xs.map Sym.bit ++ RX := by
      rw [hS3, Function.update_of_ne hXR', hS2, Function.update_of_ne hXR, hS1,
        Function.update_self]
    have h3R : S3 kR = toks xs.length ++ Sym.mark :: R0 := by
      rw [hS3, Function.update_of_ne hRR', hS2, Function.update_self]
    have ih := dropTokLoop_eval hXR hXR' hRR' RX R0 xs p la lb c S3 h3X h3R
    have h3R' : S3 kR' = Sym.bit true :: S kR' := Function.update_self _ _ _
    rw [h3R'] at ih
    refine (Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) ih).of_eq
      (st_eqC rfl ?_) ?_
    · show oBitC ((S kR).head?, p, la, lb, c) = true
      rw [hR']
      rfl
    · clear e1 e2 e3 e4 ih
      funext k
      simp only [hS3, hS2, hS1, Function.update_apply, toks_succ', List.length_cons]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem dropTok_eval {kX kR kR' : K} (hXR : kX ≠ kR) (hXR' : kX ≠ kR') (hRR' : kR ≠ kR')
    (RX R0 : List Sym) (xs : List Bool) (o p : Option Sym) (la lb c : Bool) (S : K → List Sym)
    (hX : S kX = xs.map Sym.bit ++ RX) (hR : S kR = toks xs.length ++ Sym.mark :: R0) :
    Eval [] (dropTok kX kR kR') ⟨(o, p, la, lb, c), S⟩
      ⟨(some Sym.mark, p, la, lb, c), Function.update (Function.update (Function.update S
        kX RX) kR (Sym.mark :: R0)) kR' (toks xs.length ++ S kR')⟩ (5 * xs.length + 2) :=
  (Eval.seq (cpkO_eval kR (o, p, la, lb, c) S)
    (dropTokLoop_eval hXR hXR' hRR' RX R0 xs p la lb c S hX hR)).of_eq rfl (by omega)

end Loops

end SubNLogN.Machine.Arith.CAddAux
