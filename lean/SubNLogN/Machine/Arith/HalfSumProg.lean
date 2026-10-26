/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CAdd

/-!
# `SubNLogN.Machine.Arith.HalfSumProg`: programs of the normalized butterfly `tdiv (u ± v) 2`

Paper: Theorem 6.5 (`thm:direct-fft`, last-axis DIF step: form each half-sum and
half-difference exactly and truncate to the `q`-grid); contract `HalfSumDiffStmt`
(`Contracts/Arith.lean`).

## Plan (program design, invariants, cost)
Layout `HSK = KLoc (Fin 5) (Fin 13)`: named `u`, `v`, the two destinations, the counter `w`;
private: the output buffers `Ts`, `Td`, unary rulers `R1`, `R2` (`w` tokens) and `R3`
(`w + 1` tokens) with their used-token stacks, the field buffers `A`, `B`, a reversal buffer
`A'`, and the ruler-construction scratch `C`, `M`. Registers
`HReg = o × p × la × lb × c1 × c2` (two symbol slots, the last bits read, two carries).
* Per field (`fieldH`), with `a`, `b` the `w`-bit fields of `u`, `v`:
  1. `w + 1` ripple steps (`stepLoopH`, governed by `R3`): read the next bit of `a` and of `b`
     (sign extension once the `w` bits are read: the CAdd `readA`/`readB`), push the sum bit of
     `addBit` on `A` and the difference bit of `subBit` on `B`. Afterwards `A` holds
     `twosBits (w+1) (a+b)` reversed (sign on top), `B` the same for `a - b`
     (`ripOut_add`/`ripOut_sub` at width `w + 1`; both values fit `w + 1` bits).
  2. Restore the rulers (`fieldS` = steps 1-2).
  3. `emitH A Ts`, `emitH B Td`: halve with truncation toward zero (not an arithmetic floor
     shift). With `z = s₀ + 2·z'` and the sign `s_w` (the top of the buffer),
     `tdiv z 2 = z' + (s₀ ∧ s_w)` (`half_bits`). So: read the sign, reverse the buffer onto `A'`,
     pop `s₀`, and increment the remaining `w` bits by the carry `s₀ ∧ s_w` while pushing them
     on the output buffer (LSB first).
* Records: the field loop, then one `sep` on each output buffer. Main: guards, rulers via
  `K1.ShiftAux.buildU` (amortized `O(w)`), the record loop, both output buffers rewound onto
  their destinations, cleanup.
* Cost: `O(w)` per field, `O(1)` per record, `O(w)` setup: `C·(V_u + V_v + w + 1)`.

**Scope (honest summary).** Programs, atoms, their evaluation lemmas and pure lemmas (no
`sorry`). Helpers live in `SubNLogN.Machine.Arith.HalfSumAux`.
-/

namespace SubNLogN.Machine.Arith.HalfSumAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux SubNLogN.Machine.Arith.CAddAux

/-! ## Pure lemmas: halving toward zero -/

/-- Increment step: `a + c = out + 2·c'` (the second input is ignored). -/
def hsIncBit (a _b c : Bool) : Bool × Bool := (xor a c, a && c)

/-- The bits pushed by the increment loop from carry `c`. -/
def hsIncOut : Bool → List Bool → List Bool
  | _, [] => []
  | c, x :: xs => xor x c :: hsIncOut (x && c) xs

theorem linBit_hsInc : LinBit hsIncBit 1 0 1 := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [hsIncBit]

theorem hsIncOut_eq_ripOut : ∀ (c : Bool) (xs : List Bool), hsIncOut c xs = ripOut hsIncBit c xs xs
  | _, [] => rfl
  | c, x :: xs => by
    rw [ripOut_cons, ← hsIncOut_eq_ripOut]
    rfl

theorem hsIncOut_twosBits (w : ℕ) (x : ℤ) (c : Bool) :
    hsIncOut c (twosBits w x) = twosBits w (x + c.toNat) := by
  rw [hsIncOut_eq_ripOut, ripOut_twosBits linBit_hsInc]
  congr 1
  ring

/-- Truncating halving = floor halving, plus one for odd negative numbers. -/
theorem tdiv_two_eq' (z : ℤ) :
    z.tdiv 2 = z / 2 + ((decide (z % 2 = 1) && decide (z < 0)).toNat : ℤ) := by
  rcases le_or_gt 0 z with hz | hz
  · rw [Int.tdiv_eq_ediv_of_nonneg hz]
    simp [show ¬ z < 0 by omega]
  · have h1 : z.tdiv 2 = -((-z).tdiv 2) := by rw [← Int.neg_tdiv, neg_neg]
    rw [h1, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    by_cases h2 : z % 2 = 1
    · simp [h2, hz]
      omega
    · simp [h2]
      omega

/-- **Halving toward zero of a buffered `(w+1)`-bit field**: incrementing the upper `w` bits by
`s₀ ∧ sign` gives `tdiv z 2`. -/
theorem half_bits {w : ℕ} {z : ℤ} (hz : FitsTwos (w + 1) z) :
    hsIncOut (decide (z % 2 = 1) && lastOr (decide (z % 2 = 1)) (twosBits w (z / 2)))
      (twosBits w (z / 2)) = twosBits w (z.tdiv 2) := by
  have h1 : lastOr (decide (z % 2 = 1)) (twosBits w (z / 2)) = decide (z < 0) := by
    rw [← lastOr_cons false, ← twosBits_succ, lastOr_twosBits (by omega) hz]
  rw [h1, hsIncOut_twosBits, tdiv_two_eq' z]

theorem fitsTwos_add' {w : ℕ} (hw : 1 ≤ w) {a b : ℤ} (ha : FitsTwos w a) (hb : FitsTwos w b) :
    FitsTwos (w + 1) (a + b) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  unfold FitsTwos at *
  have e1 : k + 1 - 1 = k := by omega
  have e2 : k + 1 + 1 - 1 = k + 1 := by omega
  rw [e1] at ha hb
  rw [e2, pow_succ]
  generalize (2 : ℤ) ^ k = P at *
  omega

theorem fitsTwos_sub' {w : ℕ} (hw : 1 ≤ w) {a b : ℤ} (ha : FitsTwos w a) (hb : FitsTwos w b) :
    FitsTwos (w + 1) (a - b) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  unfold FitsTwos at *
  have e1 : k + 1 - 1 = k := by omega
  have e2 : k + 1 + 1 - 1 = k + 1 := by omega
  rw [e1] at ha hb
  rw [e2, pow_succ]
  generalize (2 : ℤ) ^ k = P at *
  omega

/-- The top of a reversed nonempty bit block is its last bit. -/
theorem head?_rev_map (s0 : Bool) (rest : List Bool) (L : List Sym) :
    ((s0 :: rest).reverse.map Sym.bit ++ L).head? = some (Sym.bit (lastOr s0 rest)) := by
  induction rest generalizing s0 L with
  | nil => rfl
  | cons x xs ih =>
    rw [lastOr_cons, ← ih x (Sym.bit s0 :: L)]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]

/-! ## Registers and atoms -/

/-- Registers: slots `o`, `p`, the last bits `la`, `lb`, the carries `c1` (sum; reused as the
increment carry) and `c2` (difference). -/
abbrev HReg : Type := Option Sym × Option Sym × Bool × Bool × Bool × Bool

/-- Programs of the half-sum / half-difference kernel. -/
abbrev HProg (K : Type) : Type := Prog K (fun _ => Sym) HReg

/-- Lens onto the first five registers, to run the CAdd programs (`CReg`). -/
def lensHC : Lens HReg CAddAux.CReg where
  get v := (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1)
  set v w := (w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2, v.2.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the first four registers, to run the `K1.ShiftAux` programs (`XReg`). -/
def lensHX : Lens HReg XReg where
  get v := (v.1, v.2.1, v.2.2.1, v.2.2.2.1)
  set v w := (w.1, w.2.1, w.2.2.1, w.2.2.2, v.2.2.2.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens onto the slot `o`, to run `TMFw.Lib` routines. -/
def lensHo : Lens HReg (Option Sym) := Lens.fst _ _

/-- Run a CAdd program. -/
def liftH {K : Type} (p : CAddAux.CProg K) : HProg K := p.liftRegs lensHC

/-- Run a `K1.ShiftAux` program. -/
def liftHX {K : Type} (p : XProg K) : HProg K := p.liftRegs lensHX

/-- Run a `TMFw.Lib` routine on the slot `o`. -/
def liftHo {K : Type} (p : SProg K) : HProg K := p.liftRegs lensHo

section Atoms

variable {K : Type}

/-- Peek `k` into `o`. -/
def qpkO (k : K) : HProg K := .peek k fun v o => (o, v.2)
/-- Peek `k` into `p`. -/
def qpkP (k : K) : HProg K := .peek k fun v o => (v.1, o, v.2.2)
/-- Pop `k` into `o`. -/
def qppO (k : K) : HProg K := .pop k fun v o => (o, v.2)
/-- Pop `k`, discarding the symbol. -/
def qpd (k : K) : HProg K := .pop k fun v _ => v
/-- Push a constant on `k`. -/
def qpc (k : K) (x : Sym) : HProg K := .push k fun _ => x
/-- Push the sum bit of `addBit la lb c1` on `k`. -/
def qpushS (k : K) : HProg K := .push k fun v => .bit (addBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.1).1
/-- `c1 :=` the carry of `addBit la lb c1`. -/
def qsetS : HProg K := .load fun v =>
  (v.1, v.2.1, v.2.2.1, v.2.2.2.1, (addBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.1).2, v.2.2.2.2.2)
/-- Push the difference bit of `subBit la lb c2` on `k`. -/
def qpushD (k : K) : HProg K := .push k fun v => .bit (subBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.2).1
/-- `c2 :=` the borrow of `subBit la lb c2`. -/
def qsetD : HProg K := .load fun v =>
  (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, (subBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.2).2)
/-- `c1 := false`, `c2 := false`. -/
def qclr : HProg K := .load fun v => (v.1, v.2.1, v.2.2.1, v.2.2.2.1, false, false)
/-- `la :=` the bit in `o` (the sign of a buffered field). -/
def qsetLa : HProg K := .load fun v =>
  (v.1, v.2.1, optBit v.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2)
/-- `c1 :=` (the bit in `o`) `∧ la`. -/
def qsetC1 : HProg K := .load fun v =>
  (v.1, v.2.1, v.2.2.1, v.2.2.2.1, optBit v.1 && v.2.2.1, v.2.2.2.2.2)
/-- Push the increment output bit `(the bit in o) xor c1` on `k`. -/
def qpushInc (k : K) : HProg K := .push k fun v => .bit (xor (optBit v.1) v.2.2.2.2.1)
/-- `c1 :=` (the bit in `o`) `∧ c1`. -/
def qsetInc : HProg K := .load fun v =>
  (v.1, v.2.1, v.2.2.1, v.2.2.2.1, optBit v.1 && v.2.2.2.2.1, v.2.2.2.2.2)
/-- The slot `o` holds a bit. -/
def qoBit (v : HReg) : Bool := optIsBit v.1
/-- The slot `p` holds a bit. -/
def qpBit (v : HReg) : Bool := optIsBit v.2.1
/-- A record starts here: the slot `o` holds a bit or a record end. -/
def qisRec (v : HReg) : Bool := optIsBit v.1 || decide (v.1 = some Sym.sep)

theorem st_eqH {v v' : HReg} {S S' : K → List Sym} (hv : v = v') (hS : S = S') :
    (⟨v, S⟩ : St K (fun _ => Sym) HReg) = ⟨v', S'⟩ := by
  subst hv; subst hS; rfl

variable [DecidableEq K]

theorem qpkO_eval (k : K) (v : HReg) (S : K → List Sym) :
    Eval [] (qpkO k) ⟨v, S⟩ ⟨((S k).head?, v.2), S⟩ 1 := Eval.peek _ _ _ _ _

theorem qpkP_eval (k : K) (v : HReg) (S : K → List Sym) :
    Eval [] (qpkP k) ⟨v, S⟩ ⟨(v.1, (S k).head?, v.2.2), S⟩ 1 := Eval.peek _ _ _ _ _

theorem qppO_eval (k : K) (v : HReg) (S : K → List Sym) (x : Sym) (L : List Sym)
    (h : S k = x :: L) : Eval [] (qppO k) ⟨v, S⟩ ⟨(some x, v.2), Function.update S k L⟩ 1 :=
  eval_pop_cons [] k _ v S x L h

theorem qpd_eval (k : K) (v : HReg) (S : K → List Sym) (x : Sym) (L : List Sym)
    (h : S k = x :: L) : Eval [] (qpd k) ⟨v, S⟩ ⟨v, Function.update S k L⟩ 1 :=
  eval_pop_cons [] k _ v S x L h

theorem qpc_eval (k : K) (x : Sym) (v : HReg) (S : K → List Sym) :
    Eval [] (qpc k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 := Eval.push _ _ _ _ _

end Atoms

/-! ## Layout -/

/-- Stacks: five named (`u`, `v`, the two destinations, the counter `w`) and thirteen private. -/
abbrev HSK : Type := KLoc (Fin 5) (Fin 13)

/-- Operand `u`. -/
abbrev hkU : HSK := .inl 0
/-- Operand `v`. -/
abbrev hkV : HSK := .inl 1
/-- Destination of the half-sums. -/
abbrev hkDs : HSK := .inl 2
/-- Destination of the half-differences. -/
abbrev hkDd : HSK := .inl 3
/-- Counter `w`. -/
abbrev hkW : HSK := .inl 4
/-- Output buffer of the half-sums. -/
abbrev hkTs : HSK := .inr 0
/-- Output buffer of the half-differences. -/
abbrev hkTd : HSK := .inr 1
/-- Ruler of `u` (`w` tokens). -/
abbrev hkR1 : HSK := .inr 2
/-- Used tokens of `R1`. -/
abbrev hkR1' : HSK := .inr 3
/-- Ruler of `v` (`w` tokens). -/
abbrev hkR2 : HSK := .inr 4
/-- Used tokens of `R2`. -/
abbrev hkR2' : HSK := .inr 5
/-- Ruler of the ripple steps (`w + 1` tokens). -/
abbrev hkR3 : HSK := .inr 6
/-- Used tokens of `R3`. -/
abbrev hkR3' : HSK := .inr 7
/-- Buffer of the `(w+1)`-bit sum field. -/
abbrev hkA : HSK := .inr 8
/-- Buffer of the `(w+1)`-bit difference field. -/
abbrev hkB : HSK := .inr 9
/-- Reversal buffer. -/
abbrev hkA' : HSK := .inr 10
/-- Binary counter copy (ruler construction). -/
abbrev hkC : HSK := .inr 11
/-- Temporary (decrement, copy). -/
abbrev hkM : HSK := .inr 12

/-! ## Programs -/

/-- One ripple step: read the next bits (or sign-extend), push the sum bit on `A` and the
difference bit on `B`, update both carries, move one `R3` token, peek `R3`. -/
def stepBodyH : HProg HSK :=
  .seq (liftH (readA hkU hkR1 hkR1')) (.seq (liftH (readB hkV hkR2 hkR2')) (.seq (qpushS hkA)
    (.seq qsetS (.seq (qpushD hkB) (.seq qsetD (.seq (qpd hkR3) (.seq (qpc hkR3' (.bit true))
      (qpkP hkR3))))))))

/-- The ripple steps of one field (while `R3` has a token). -/
def stepLoopH : HProg HSK := .loop qpBit stepBodyH

/-- The ripple part of one field, then the ruler restores. -/
def fieldS : HProg HSK :=
  .seq qclr (.seq (qpkP hkR3) (.seq stepLoopH (.seq (liftHo (moveBlock hkR1' hkR1))
    (.seq (liftHo (moveBlock hkR2' hkR2)) (liftHo (moveBlock hkR3' hkR3))))))

/-- The increment loop: pop a bit of `A'`, push `bit xor c1` on `T`, `c1 := bit ∧ c1`. -/
def incLoop (kT : HSK) : HProg HSK :=
  .loop qoBit (.seq (qppO hkA') (.seq (qpushInc kT) (.seq qsetInc (qpkO hkA'))))

/-- Halve the buffered field of `X` (sign on top) toward zero, onto `T` (LSB first). -/
def emitH (kX kT : HSK) : HProg HSK :=
  .seq (qpkO kX) (.seq qsetLa (.seq (liftHo (moveBlock kX hkA')) (.seq (qppO hkA')
    (.seq qsetC1 (.seq (qpkO hkA') (incLoop kT))))))

/-- One field: ripple, then the two halvings. -/
def fieldH : HProg HSK := .seq fieldS (.seq (emitH hkA hkTs) (emitH hkB hkTd))

/-- The fields of one record (while `u` shows a bit). -/
def fieldLoopH : HProg HSK := .loop qoBit (.seq fieldH (qpkO hkU))

/-- One record: its fields, then its end `sep` (consumed on both inputs, pushed on both
outputs). -/
def recBodyH : HProg HSK :=
  .seq fieldLoopH (.seq (qpd hkU) (.seq (qpd hkV) (.seq (qpc hkTs .sep) (.seq (qpc hkTd .sep)
    (qpkO hkU)))))

/-- The record loop. -/
def recLoopH : HProg HSK := .loop qisRec recBodyH

/-- Guards on the output buffers, the rulers and the field buffers. -/
def setupH : HProg HSK :=
  .seq (qpc hkTs .mark) (.seq (qpc hkTd .mark) (.seq (qpc hkR1 .mark) (.seq (qpc hkR1' .mark)
  (.seq (qpc hkR2 .mark) (.seq (qpc hkR2' .mark) (.seq (qpc hkR3 .mark) (.seq (qpc hkR3' .mark)
  (.seq (qpc hkA .mark) (.seq (qpc hkB .mark) (qpc hkA' .mark))))))))))

/-- Remove the rulers and the guards. -/
def cleanupH : HProg HSK :=
  .seq (liftHX (dropBits hkR1)) (.seq (qpd hkR1) (.seq (liftHX (dropBits hkR2)) (.seq (qpd hkR2)
  (.seq (liftHX (dropBits hkR3)) (.seq (qpd hkR3) (.seq (qpd hkR1') (.seq (qpd hkR2')
  (.seq (qpd hkR3') (.seq (qpd hkA) (.seq (qpd hkB) (qpd hkA')))))))))))

/-- The half-sum / half-difference kernel. -/
def hMain : HProg HSK :=
  .seq setupH
  (.seq (liftHX (buildU hkW hkC hkM hkR1)) (.seq (qpd hkC)
  (.seq (liftHX (buildU hkW hkC hkM hkR2)) (.seq (qpd hkC)
  (.seq (liftHX (buildU hkW hkC hkM hkR3)) (.seq (qpd hkC) (.seq (qpc hkR3 (.bit true))
  (.seq (qpkO hkU)
  (.seq recLoopH
  (.seq (liftHo (WP.W9comp.rewindTo hkTs hkDs .mark))
  (.seq (liftHo (WP.W9comp.rewindTo hkTd hkDd .mark))
    cleanupH)))))))))))

theorem closed_hMain : hMain.Closed := by
  simp [hMain, setupH, cleanupH, recLoopH, recBodyH, fieldLoopH, fieldH, fieldS, emitH, incLoop,
    stepLoopH, stepBodyH, readA, readB, liftH, liftHX, liftHo, qpkO, qpkP, qppO, qpd, qpc, qpushS,
    qsetS, qpushD, qsetD, qclr, qsetLa, qsetC1, qpushInc, qsetInc, cpkO, cppO, cpd, cpc, setA,
    setB, buildU, uLoop, uBody, dropBits, dropLoop, liftX, pkO, pc, pd, Prog.Closed,
    Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs, dec, copyBlock, moveBlock, moveBits,
    moveBitsDup, restoreR, WP.W9comp.rewindTo, pushC, popR, pushR, peekR, scanLoop, scanBody,
    decFix, skip, moveBitsBody, dupBody, WP.W9comp.rewindBody]

end SubNLogN.Machine.Arith.HalfSumAux
