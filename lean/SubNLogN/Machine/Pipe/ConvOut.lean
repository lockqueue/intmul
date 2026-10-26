/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.ConvBase

/-!
# K7 conversions (`Machine/Pipe/ConvOut.lean`): `ConvOutStmt`, two's-complement records → W9 entries

**Program.** Peek `dst`. If it holds no record (the top is not a bit), push `symLevel, symNode` on
`S`. Otherwise push a `mark` on the accumulator `t`, build a ruler of `w` ticks on `ra` (`rulerProg`,
from `wout`), and convert record by record (`recordsLoop`). Each coordinate (`fieldOut`): read its
`w` bits from `dst` onto `f` (`loopE`, one ruler tick per bit; `f` then holds the field most
significant bit on top), move the ruler back, read the sign from the top of `f` and push the sign
symbol on `t`, move `f` onto `g` (`mvG`, least significant bit on top), ripple `g` onto `t`
(`loopC`: the magnitude, least significant bit first) and strip the high zeros from the top of `t`
(`loopD`). The coordinates are separated by `sep2` and followed by `sep`; the record end of `dst`
is popped. Finally clear the ruler, push `symLevel, symNode` on `S` and move `t` onto `S` down to the
`mark` (`rewindTo`).

**Proved (no `sorry`).** `Pipe.convOut_holds : ConvOutStmt` (constant `C = 200`).
-/

namespace SubNLogN.Machine.Pipe.ConvAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
  SubNLogN.Machine.Pipe

/-! ## Programs -/

/-- One field bit: pop `dst`, push the bit on `f`, move a ruler tick `ra → rb`, peek `ra`. -/
def bodyE : CProg :=
  .seq (.pop kDst fun v o => (o, v.2))
  (.seq (.push kF fun v => v.1.getD .sep)
  (.seq (.pop kRA fun v _ => v)
  (.seq (.push kRB fun _ => tick)
    (.peek kRA fun v o => (o, v.2)))))

/-- Read a `w`-bit field (while `ra` holds ticks). -/
def loopE : CProg := .loop (fun v => optIsBit v.1) bodyE

/-- One magnitude bit: push the ripple bit on `t`, update the carry, pop `g`. -/
def bodyC : CProg :=
  .seq (.push kT fun v => .bit (xor (optBit v.1) (v.2.1 && v.2.2)))
  (.seq (.load fun v => (v.1, v.2.1, optBit v.1 || v.2.2))
    (.pop kG fun v o => (o, v.2)))

/-- The ripple loop over `g`. -/
def loopC : CProg := .loop (fun v => optIsBit v.1) bodyC

/-- One stripped zero: pop `t`, peek `t`. -/
def bodyD : CProg := .seq (.pop kT fun v _ => v) (.peek kT fun v o => (o, v.2))

/-- Strip high zeros from the top of `t`. -/
def loopD : CProg := .loop (fun v => decide (v.1 = some (Sym.bit false))) bodyD

/-- Read one `w`-bit field from `dst` onto `f`, above a `mark` (most significant bit on top), one
ruler tick per bit; then move the ruler back. -/
def readField : CProg :=
  .seq (.push kF fun _ => Sym.mark)
  (.seq (.seq (.peek kRA fun v o => (o, v.2)) loopE)
    ((moveBlock kRB kRA).liftRegs lC))

/-- Sign-magnitude of the field on `f`: the sign flag is its top bit; push the sign symbol on `t`,
move the field onto `g` (least significant bit on top), ripple it onto `t` and strip the high
zeros. -/
def signMag : CProg :=
  .seq (.peek kF fun _ o => (o, decide (o = some (Sym.bit true)), false))
  (.seq (.push kT fun v => if v.2.1 then Sym.neg else Sym.pos)
  (.seq (.push kG fun _ => Sym.mark)
  (.seq ((WP.W9b.mvG kF kG).liftRegs lC)
  (.seq (.seq (.pop kG fun v o => (o, v.2)) loopC)
    (.seq (.peek kT fun v o => (o, v.2)) loopD)))))

/-- One coordinate. -/
def fieldOut : CProg := .seq readField signMag

/-- One record: two coordinates, the separators, the record end; then peek `dst`. -/
def recordOut : CProg :=
  .seq fieldOut (.seq (.push kT fun _ => Sym.sep2) (.seq fieldOut (.seq (.push kT fun _ => Sym.sep)
    (.seq (.pop kDst fun v _ => v) (.peek kDst fun v o => (o, v.2))))))

/-- The record loop (while `dst` starts with a bit). -/
def recordsLoop : CProg := .loop (fun v => optIsBit v.1) recordOut

/-- The `ConvOut` program. -/
def convOutProg : CProg :=
  .seq (.peek kDst fun v o => (o, v.2))
  (.ite (fun v => optIsBit v.1)
    (.seq (.push kT fun _ => Sym.mark)
    (.seq (rulerProg kWout)
    (.seq (.seq (.peek kDst fun v o => (o, v.2)) recordsLoop)
    (.seq ((WP.Top.clearStk kRA).liftRegs lC)
    (.seq (.push kS fun _ => symLevel)
    (.seq (.push kS fun _ => symNode)
      ((WP.W9comp.rewindTo kT kS Sym.mark).liftRegs lC)))))))
    (.seq (.push kS fun _ => symLevel) (.push kS fun _ => symNode)))

theorem closed_convOutProg : convOutProg.Closed := by
  refine ⟨trivial, ⟨trivial, closed_rulerProg kWout, ?_, WP.W9comp.closed_liftRegs lC ?_, trivial,
    trivial, WP.W9comp.closed_rewind lC kT kS Sym.mark⟩, trivial, trivial⟩
  · simp [recordsLoop, recordOut, fieldOut, readField, signMag, loopE, bodyE, loopC, bodyC, loopD, bodyD,
      Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, pushR, popR, Lib.skip,
      Prog.liftRegs, WP.W9b.mvG, WP.W9b.mvGBody, WP.W9b.notMarkR]
  · simp [Prog.Closed, Prog.FreeBelow, WP.Top.clearStk, popR]

/-! ## Loops -/

theorem bodyE_eval (r : Option Sym) (neg c b : Bool) (n m : ℕ) (R : List Sym) (St : CK → List Sym)
    (hD : St kDst = Sym.bit b :: R) (hA : St kRA = ruler (n + 1)) (hB : St kRB = ruler m) :
    Eval [] bodyE ⟨(r, neg, c), St⟩
      ⟨((ruler n).head?, neg, c), Function.update (Function.update (Function.update
        (Function.update St kDst R) kF (Sym.bit b :: St kF)) kRA (ruler n)) kRB
        (ruler (m + 1))⟩ 5 := by
  refine (Eval.seq (Eval.pop [] kDst _ _ St) (Eval.seq (Eval.push [] kF _ _ _)
    (Eval.seq (Eval.pop [] kRA _ _ _) (Eval.seq (Eval.push [] kRB _ _ _)
      (Eval.peek [] kRA _ _ _))))).of_eq ?_ rfl
  congr 1
  · simp [Function.update_apply, hA, ruler_succ]
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [ruler_succ]

theorem loopE_eval (neg c : Bool) : ∀ (bs : List Bool) (m : ℕ) (R : List Sym)
    (St : CK → List Sym),
    St kDst = bs.map Sym.bit ++ R → St kRA = ruler bs.length → St kRB = ruler m →
    Eval [] loopE ⟨((ruler bs.length).head?, neg, c), St⟩
      ⟨(none, neg, c), Function.update (Function.update (Function.update (Function.update St kDst R)
        kF (bs.reverse.map Sym.bit ++ St kF)) kRA []) kRB (ruler (m + bs.length))⟩
      (6 * bs.length + 1)
  | [], m, R, St, hD, hA, hB => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    simp only [List.map_nil, List.nil_append, List.length_nil] at hD hA ⊢
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.map_nil, List.nil_append,
      Nat.add_zero]
    split_ifs <;> simp_all
  | b :: bs, m, R, St, hD, hA, hB => by
    have e1 := bodyE_eval ((ruler (bs.length + 1)).head?) neg c b bs.length m
      (bs.map Sym.bit ++ R) St hD hA hB
    have ih := loopE_eval neg c bs (m + 1) R
      (Function.update (Function.update (Function.update (Function.update St kDst
        (bs.map Sym.bit ++ R)) kF (Sym.bit b :: St kF)) kRA (ruler bs.length)) kRB (ruler (m + 1)))
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply])
    refine (Eval.loop_true (by rfl) e1 ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    have e : m + 1 + bs.length = m + (bs.length + 1) := by omega
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append, List.length_cons, e]
    split_ifs <;> simp_all

theorem bodyC_eval (neg c b : Bool) (L : List Sym) (St : CK → List Sym) (hG : St kG = L) :
    Eval [] bodyC ⟨(some (Sym.bit b), neg, c), St⟩
      ⟨(L.head?, neg, b || c), Function.update (Function.update St kT
        (Sym.bit (xor b (neg && c)) :: St kT)) kG L.tail⟩ 3 := by
  refine (Eval.seq (Eval.push [] kT _ _ St) (Eval.seq (Eval.load [] _ _ _)
    (Eval.pop [] kG _ _ _))).of_eq ?_ rfl
  congr 1
  · simp [Function.update_apply, hG]
  · funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem loopC_eval (neg : Bool) : ∀ (bs : List Bool) (c : Bool) (RG : List Sym)
    (St : CK → List Sym), TermOK RG → St kG = (bs.map Sym.bit ++ RG).tail →
    Eval [] loopC ⟨((bs.map Sym.bit ++ RG).head?, neg, c), St⟩
      ⟨(RG.head?, neg, bs.any id || c), Function.update (Function.update St kG RG.tail) kT
        ((rip neg c bs).reverse.map Sym.bit ++ St kT)⟩ (4 * bs.length + 1)
  | [], c, RG, St, hRG, hG => by
    refine (Eval.loop_false ?_).of_eq ?_ rfl
    · simpa using optIsBit_head?_of_termOK hRG
    · simp only [List.map_nil, List.nil_append, List.any_nil, Bool.false_or] at hG ⊢
      congr 1
      funext k
      simp only [Function.update_apply, rip_nil, List.reverse_nil, List.map_nil, List.nil_append]
      split_ifs <;> simp_all
  | b :: bs, c, RG, St, hRG, hG => by
    have hG' : St kG = bs.map Sym.bit ++ RG := hG
    have e1 := bodyC_eval neg c b _ St hG'
    have ih := loopC_eval neg bs (b || c) RG
      (Function.update (Function.update St kT (Sym.bit (xor b (neg && c)) :: St kT)) kG
        (bs.map Sym.bit ++ RG).tail) hRG (by simp)
    refine (Eval.loop_true (by rfl) e1 ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    have hc : (bs.any id || (b || c)) = ((b :: bs).any id || c) := by
      rw [List.any_cons]
      generalize bs.any id = a
      cases a <;> cases b <;> cases c <;> rfl
    rw [hc]
    congr 1
    funext k
    simp only [Function.update_apply, rip_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

theorem loopD_eval (r : Bool × Bool) : ∀ (k : ℕ) (L : List Sym) (St : CK → List Sym),
    St kT = List.replicate k (Sym.bit false) ++ L → L.head? ≠ some (Sym.bit false) →
    Eval [] loopD ⟨((List.replicate k (Sym.bit false) ++ L).head?, r), St⟩
      ⟨(L.head?, r), Function.update St kT L⟩ (3 * k + 1)
  | 0, L, St, hT, hL => by
    refine (Eval.loop_false ?_).of_eq ?_ rfl
    · simpa using hL
    · simp only [List.replicate_zero, List.nil_append] at hT ⊢
      rw [← hT, Function.update_eq_self]
  | k + 1, L, St, hT, hL => by
    have e1 : Eval [] bodyD ⟨(some (Sym.bit false), r), St⟩
        ⟨((List.replicate k (Sym.bit false) ++ L).head?, r),
          Function.update St kT (List.replicate k (Sym.bit false) ++ L)⟩ 2 := by
      refine (Eval.seq (Eval.pop [] kT _ _ St) (Eval.peek [] kT _ _ _)).of_eq ?_ rfl
      simp [hT, List.replicate_succ]
    have ih := loopD_eval r k L (Function.update St kT (List.replicate k (Sym.bit false) ++ L))
      (by simp) hL
    refine (Eval.loop_true ?_ e1 ih).of_eq ?_ (by omega)
    · simp
    · rw [Function.update_idem]

/-! ## Reading a field -/

theorem peekLoopE_eval (bs : List Bool) (r : CReg) (R : List Sym) (St : CK → List Sym)
    (hD : St kDst = bs.map Sym.bit ++ R) (hA : St kRA = ruler bs.length) (hB : St kRB = []) :
    Eval [] (.seq (.peek kRA fun v o => (o, v.2)) loopE) ⟨r, St⟩
      ⟨(none, r.2.1, r.2.2), Function.update (Function.update (Function.update
        (Function.update St kDst R) kF (bs.reverse.map Sym.bit ++ St kF)) kRA []) kRB
        (ruler (0 + bs.length))⟩ (1 + (6 * bs.length + 1)) :=
  Eval.seq ((Eval.peek [] kRA _ r St).of_eq (by simp [hA]) rfl)
    (loopE_eval r.2.1 r.2.2 bs 0 R St hD hA (by simp [hB]))

theorem readField_runs (bs : List Bool) (R : List Sym) (St : CK → List Sym)
    (hD : St kDst = bs.map Sym.bit ++ R) (hA : St kRA = ruler bs.length) (hB : St kRB = []) :
    Runs readField St (Function.update (Function.update St kDst R) kF
      (bs.reverse.map Sym.bit ++ Sym.mark :: St kF)) (fun _ => True) (9 * bs.length + 7) := by
  refine Runs.of_eval fun v => ⟨_, _, (Eval.seq (Eval.push [] kF (fun (_ : CReg) => Sym.mark) v St)
    (Eval.seq (peekLoopE_eval bs v R _ (by simp [Function.update_apply, hD])
      (by simp [Function.update_apply, hA]) (by simp [Function.update_apply, hB]))
    (moveBack_eval _ (0 + bs.length) _ (by simp [Function.update_apply])
      (by simp [Function.update_apply])))).of_eq (by
        refine congrArg₂ TMFw.St.mk rfl ?_
        funext k
        rcases k with p | e
        · cases p <;> simp [Function.update_apply]
        · cases e <;> simp [Function.update_apply, hA, hB]) rfl, trivial, by omega⟩

/-! ## Sign-magnitude of a field -/

/-- `mvG f g` through `lC`: the sign/carry registers are kept. -/
theorem mvGC_eval (r : CReg) (L rest : List Sym) (St : CK → List Sym)
    (hL : ∀ x ∈ L, x ≠ Sym.mark) (hF : St kF = L ++ Sym.mark :: rest) :
    Eval [] ((WP.W9b.mvG kF kG).liftRegs lC) ⟨r, St⟩
      ⟨(some Sym.mark, r.2), Function.update (Function.update St kF rest) kG (L.reverse ++ St kG)⟩
      (3 * L.length + 2) := by
  have h1 : Eval [] (popR kF) ⟨r.1, St⟩
      ⟨(L ++ Sym.mark :: rest).head?, Function.update St kF (L ++ Sym.mark :: rest).tail⟩ 1 := by
    refine (Eval.pop [] kF (fun _ o => o) r.1 St).of_eq ?_ rfl
    rw [hF]
  have h2 := WP.W9b.mvG_loop_eval (src := kF) (dst := kG) (by decide) L rest
    (Function.update St kF (L ++ Sym.mark :: rest).tail) hL (Function.update_self _ _ _)
  refine (Eval.liftRegs lC (Eval.seq h1 h2) r rfl).of_eq ?_ (by omega)
  congr 1
  funext k
  rcases k with p | e
  · cases p <;> simp [Function.update_apply]
  · cases e <;> simp [Function.update_apply]

theorem popLoopC_eval (neg : Bool) (bs : List Bool) (r : Option Sym) (G0 : List Sym)
    (St : CK → List Sym) (hG : St kG = bs.map Sym.bit ++ Sym.mark :: G0) :
    Eval [] (.seq (.pop kG fun v o => (o, v.2)) loopC) ⟨(r, neg, false), St⟩
      ⟨(some Sym.mark, neg, bs.any id || false), Function.update (Function.update St kG G0) kT
        ((rip neg false bs).reverse.map Sym.bit ++ St kT)⟩ (1 + (4 * bs.length + 1)) := by
  have e := loopC_eval neg bs false (Sym.mark :: G0)
    (Function.update St kG (bs.map Sym.bit ++ Sym.mark :: G0).tail) (TermOK.cons rfl _)
    (Function.update_self _ _ _)
  have h1 : Eval [] (.pop kG fun (v : CReg) o => (o, v.2) : CProg) ⟨(r, neg, false), St⟩
      ⟨((bs.map Sym.bit ++ Sym.mark :: G0).head?, neg, false),
        Function.update St kG (bs.map Sym.bit ++ Sym.mark :: G0).tail⟩ 1 :=
    (Eval.pop [] kG (fun (v : CReg) o => (o, v.2)) (r, neg, false) St).of_eq (by rw [hG]) rfl
  refine (Eval.seq h1 e).of_eq ?_ rfl
  refine congrArg₂ TMFw.St.mk (by simp) ?_
  funext k
  rcases k with p | e
  · cases p <;> simp [Function.update_apply]
  · cases e <;> simp [Function.update_apply]

theorem bits_ne_mark (bs : List Bool) : ∀ x ∈ bs.map Sym.bit, x ≠ Sym.mark := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  simp

theorem peekLoopD_eval (r : CReg) (k : ℕ) (L : List Sym) (St : CK → List Sym)
    (hT : St kT = List.replicate k (Sym.bit false) ++ L) (hL : L.head? ≠ some (Sym.bit false)) :
    Eval [] (.seq (.peek kT fun v o => (o, v.2)) loopD) ⟨r, St⟩
      ⟨(L.head?, r.2), Function.update St kT L⟩ (1 + (3 * k + 1)) :=
  Eval.seq ((Eval.peek [] kT _ r St).of_eq (by rw [hT]) rfl) (loopD_eval r.2 k L St hT hL)

/-- The most significant bit of a nonzero minimal binary code is `1`. -/
theorem cvo_encodeNat_reverse_head (n : ℕ) (hn : n ≠ 0) :
    ∃ rest, (encodeNat n).reverse = true :: rest := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [encodeNat_eq_cons hn, List.reverse_cons]
    by_cases h2 : n / 2 = 0
    · have h1 : n = 1 := by omega
      subst h1
      exact ⟨[], by simp [encodeNat_zero, Nat.testBit_zero]⟩
    · obtain ⟨rest, hr⟩ := ih (n / 2) (by omega) h2
      exact ⟨rest ++ [n.testBit 0], by rw [hr, List.cons_append]⟩

/-- The accumulator after the ripple: the high zeros above the reversed minimal magnitude. -/
theorem strip_T {w : ℕ} (hw : 1 ≤ w) {u : ℤ} (hu : FitsTwos w u) (L : List Sym) :
    (rip (decide (u < 0)) false (twosBits w u)).reverse.map Sym.bit ++ sgnSym u :: L =
      List.replicate (w - bitLen u.natAbs) (Sym.bit false) ++
        ((encodeNat u.natAbs).reverse.map Sym.bit ++ sgnSym u :: L) := by
  rw [rip_twosBits hu hw, bitsLE_eq_encodeNat_append w _ (natAbs_lt_two_pow hu hw),
    List.reverse_append, List.map_append, List.reverse_replicate, List.map_replicate,
    List.append_assoc]

theorem strip_head_ne (u : ℤ) (L : List Sym) :
    ((encodeNat u.natAbs).reverse.map Sym.bit ++ sgnSym u :: L).head? ≠ some (Sym.bit false) := by
  by_cases h0 : u.natAbs = 0
  · rw [h0, encodeNat_zero]
    unfold sgnSym
    split_ifs <;> simp
  · obtain ⟨rest, hr⟩ := cvo_encodeNat_reverse_head _ h0
    rw [hr]
    simp

theorem strip_intSyms (u : ℤ) (L : List Sym) :
    (encodeNat u.natAbs).reverse.map Sym.bit ++ sgnSym u :: L = (intSyms u).reverse ++ L := by
  simp [intSyms, natSyms]

theorem signMag_runs {w : ℕ} (hw : 1 ≤ w) {u : ℤ} (hu : FitsTwos w u) (F0 : List Sym)
    (St : CK → List Sym) (hF : St kF = (twosBits w u).reverse.map Sym.bit ++ Sym.mark :: F0) :
    Runs signMag St (Function.update (Function.update St kF F0) kT ((intSyms u).reverse ++ St kT))
      (fun _ => True) (11 * w + 11) := by
  obtain ⟨rest, hrev⟩ := twosBits_reverse_head hu hw
  have hF1 : (St kF).head? = some (Sym.bit (decide (u < 0))) := by
    rw [hF, hrev, List.map_cons, List.cons_append, List.head?_cons]
  have hlen : (twosBits w u).length = w := K1.length_twosBits w u
  have hlen2 : ((twosBits w u).reverse.map Sym.bit).length = w := by simp [hlen]
  have hTm := strip_T hw hu (St kT)
  have hL := strip_head_ne u (St kT)
  have hint := strip_intSyms u (St kT)
  refine Runs.of_eval fun v => ⟨_, _, (Eval.seq
    ((Eval.peek [] kF (fun (_ : CReg) o => (o, decide (o = some (Sym.bit true)), false)) v St).of_eq
      (s₂ := ⟨(some (Sym.bit (decide (u < 0))), decide (u < 0), false), St⟩) (by rw [hF1]; simp) rfl)
    (Eval.seq ((Eval.push [] kT (fun (v : CReg) => if v.2.1 then Sym.neg else Sym.pos) _ St).of_eq
      (s₂ := ⟨(some (Sym.bit (decide (u < 0))), decide (u < 0), false),
        Function.update St kT (sgnSym u :: St kT)⟩) (by simp [sgnSym]) rfl)
    (Eval.seq (Eval.push [] kG (fun (_ : CReg) => Sym.mark) _ _)
    (Eval.seq (mvGC_eval _ ((twosBits w u).reverse.map Sym.bit) F0 _
      (bits_ne_mark (twosBits w u).reverse) (by simp [Function.update_apply, hF]))
    (Eval.seq (popLoopC_eval (decide (u < 0)) (twosBits w u) _ (St kG) _
      (by simp [Function.update_apply]))
      (peekLoopD_eval _ (w - bitLen u.natAbs)
        ((encodeNat u.natAbs).reverse.map Sym.bit ++ sgnSym u :: St kT) _
        (by
          simp only [Function.update_apply, Sum.inr.injEq, reduceCtorEq, ↓reduceIte,
            eq_self_iff_true]
          exact hTm) hL)))))).of_eq (by
          refine congrArg₂ TMFw.St.mk rfl ?_
          funext k
          rcases k with p | e
          · cases p <;> simp [Function.update_apply]
          · cases e
            case t =>
              simp only [Function.update_apply, Sum.inr.injEq, reduceCtorEq, ↓reduceIte,
                eq_self_iff_true]
              exact hint
            all_goals simp [Function.update_apply]) rfl, trivial, by omega⟩

theorem fieldOut_runs {w : ℕ} (hw : 1 ≤ w) {u : ℤ} (hu : FitsTwos w u) (R : List Sym)
    (St : CK → List Sym) (hD : St kDst = (twosBits w u).map Sym.bit ++ R) (hA : St kRA = ruler w)
    (hB : St kRB = []) :
    Runs fieldOut St (Function.update (Function.update St kDst R) kT ((intSyms u).reverse ++ St kT))
      (fun _ => True) (20 * w + 18) := by
  have hlen : (twosBits w u).length = w := K1.length_twosBits w u
  refine WP.W9b.runs_post (WP.W9b.runs_seq
    (readField_runs (twosBits w u) R St hD (by rw [hlen]; exact hA) hB)
    (signMag_runs hw hu (St kF) _ (by simp [Function.update_apply]))) ?_ (by rw [hlen]; omega)
  funext k
  rcases k with p | e
  · cases p <;> simp [Function.update_apply]
  · cases e <;> simp [Function.update_apply]

/-! ## One record -/

theorem recSyms_crec (w : ℕ) (z : ℤ × ℤ) (R : List Sym) :
    recSyms (crecBits w [z]) ++ R =
      (twosBits w z.1).map Sym.bit ++ ((twosBits w z.2).map Sym.bit ++ Sym.sep :: R) := by
  simp [recSyms, crecBits, coefBits]

theorem entrySyms_rev (z : ℤ × ℤ) (L : List Sym) :
    (entrySyms z).reverse ++ L =
      Sym.sep :: ((intSyms z.2).reverse ++ Sym.sep2 :: ((intSyms z.1).reverse ++ L)) := by
  simp [entrySyms, List.reverse_append]

theorem recordOut_runs {w : ℕ} (hw : 1 ≤ w) {z : ℤ × ℤ} (hz : FitsTwos w z.1 ∧ FitsTwos w z.2)
    (R : List Sym) (St : CK → List Sym) (hD : St kDst = recSyms (crecBits w [z]) ++ R)
    (hA : St kRA = ruler w) (hB : St kRB = []) :
    Runs recordOut St (Function.update (Function.update St kDst R) kT
      ((entrySyms z).reverse ++ St kT)) (fun v => v.1 = R.head?) (40 * w + 40) := by
  rw [recSyms_crec] at hD
  refine WP.W9b.runs_post (WP.W9b.runs_mono (WP.W9b.runs_seq (fieldOut_runs hw hz.1 _ St hD hA hB)
    (WP.W9b.runs_seq (runs_pushK kT Sym.sep2 _)
    (WP.W9b.runs_seq (fieldOut_runs hw hz.2 (Sym.sep :: R) _ (by simp [Function.update_apply])
      (by simp [Function.update_apply, hA]) (by simp [Function.update_apply, hB]))
    (WP.W9b.runs_seq (runs_pushK kT Sym.sep _)
    (WP.W9b.runs_seq (runs_popK kDst Sym.sep R _ (by simp [Function.update_apply]))
      (runs_peekK kDst _)))))) ?_ le_rfl) ?_ (by omega)
  · intro v hv
    rw [hv]
    simp [Function.update_apply]
  · rw [entrySyms_rev]
    funext k
    rcases k with p | e
    · cases p <;> simp [Function.update_apply]
    · cases e <;> simp [Function.update_apply]

/-! ## The record loop -/

theorem cvo_optIsBit_of_blkTerm {L : List Sym} (h : BlkTerm L) : optIsBit L.head? = false := by
  rcases L with _ | ⟨y, L⟩
  · rfl
  · obtain ⟨hd, -⟩ := h y rfl
    rcases y with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [isDataSym]

theorem recHead_isBit (w : ℕ) (hw : 1 ≤ w) (z : ℤ × ℤ) (X : List Sym) :
    optIsBit (recSyms (crecBits w [z]) ++ X).head? = true := by
  rw [recSyms_crec]
  have hl : (twosBits w z.1).length = w := K1.length_twosBits _ _
  cases h : twosBits w z.1 with
  | nil => rw [h, List.length_nil] at hl; omega
  | cons b bs => rfl

theorem recordsLoop_eval {w : ℕ} (hw : 1 ≤ w) : ∀ (zs : List (ℤ × ℤ)) (rdst : List Sym)
    (St : CK → List Sym) (v : CReg), BlkTerm rdst → (∀ z ∈ zs, FitsTwos w z.1 ∧ FitsTwos w z.2) →
    St kDst = carrSyms w (zs.map fun z => [z]) ++ rdst → St kRA = ruler w → St kRB = [] →
    v.1 = (St kDst).head? →
    ∃ v' t, Eval [] recordsLoop ⟨v, St⟩ ⟨v', Function.update (Function.update St kDst rdst) kT
      ((blkE zs).reverse ++ St kT)⟩ t ∧ t ≤ zs.length * (40 * w + 41) + 1
  | [], rdst, St, v, hrdst, _, hD, _, _, hv => by
    have hD' : St kDst = rdst := by rw [hD, carrSyms_nil, List.nil_append]
    clear hD
    refine ⟨v, 1, (Eval.loop_false ?_).of_eq ?_ rfl, by simp⟩
    · show optIsBit v.1 = false
      rw [hv, hD']
      exact cvo_optIsBit_of_blkTerm hrdst
    · have hb : blkE ([] : List (ℤ × ℤ)) = [] := by simp [blkE, blk]
      rw [hb, List.reverse_nil, List.nil_append]
      congr 1
      funext k
      rcases k with p | e
      · cases p <;> simp [Function.update_apply, hD']
      · cases e <;> simp [Function.update_apply]
  | z :: zs, rdst, St, v, hrdst, hfit, hD, hA, hB, hv => by
    have hD' : St kDst = recSyms (crecBits w [z]) ++ (carrSyms w (zs.map fun z => [z]) ++ rdst) := by
      rw [hD, carrSyms_cons, List.append_assoc]
    obtain ⟨⟨v1, S1⟩, t1, e1, ⟨hS1, hv1⟩, ht1⟩ :=
      recordOut_runs hw (hfit z List.mem_cons_self) _ St hD' hA hB ⟨v, St⟩ rfl
    change S1 = _ at hS1
    subst hS1
    obtain ⟨v2, t2, e2, ht2⟩ := recordsLoop_eval hw zs rdst
      (Function.update (Function.update St kDst (carrSyms w (zs.map fun z => [z]) ++ rdst)) kT
        ((entrySyms z).reverse ++ St kT)) v1 hrdst
      (fun z' hz' => hfit z' (List.mem_cons_of_mem _ hz')) (by simp)
      (by simp [Function.update_apply, hA]) (by simp [Function.update_apply, hB])
      (by rw [hv1]; simp)
    refine ⟨v2, t1 + t2 + 1, (Eval.loop_true ?_ e1 e2).of_eq ?_ rfl, ?_⟩
    · show optIsBit v.1 = true
      rw [hv, hD']
      exact recHead_isBit w hw z _
    · congr 1
      rw [WP.W9b.blkE_cons, List.reverse_append, List.append_assoc]
      funext k
      rcases k with p | e
      · cases p <;> simp [Function.update_apply]
      · cases e <;> simp [Function.update_apply]
    · have e : (z :: zs).length * (40 * w + 41) = zs.length * (40 * w + 41) + (40 * w + 41) := by
        simp only [List.length_cons]; ring
      omega

/-! ## The program -/

theorem sgnSym_ne_mark (u : ℤ) : sgnSym u ≠ Sym.mark := by
  unfold sgnSym; split_ifs <;> simp

theorem mark_ne_sgnSym (u : ℤ) : Sym.mark ≠ sgnSym u := fun h => sgnSym_ne_mark u h.symm

theorem cvo_mark_not_mem_entrySyms (z : ℤ × ℤ) : Sym.mark ∉ entrySyms z := by
  simp [entrySyms, intSyms, natSyms, sgnSym_ne_mark, mark_ne_sgnSym]

theorem cvo_mark_not_mem_blkE : ∀ zs : List (ℤ × ℤ), Sym.mark ∉ blkE zs
  | [] => by simp [blkE, blk]
  | z :: zs => by
    rw [WP.W9b.blkE_cons, List.mem_append, not_or]
    exact ⟨cvo_mark_not_mem_entrySyms z, cvo_mark_not_mem_blkE zs⟩

theorem cvo_length_entrySyms_le {w : ℕ} (hw : 1 ≤ w) {z : ℤ × ℤ}
    (hz : FitsTwos w z.1 ∧ FitsTwos w z.2) : (entrySyms z).length ≤ 2 * w + 4 := by
  have h1 : (encodeNat z.1.natAbs).length ≤ w := bitLen_le_of_lt w _ (natAbs_lt_two_pow hz.1 hw)
  have h2 : (encodeNat z.2.natAbs).length ≤ w := bitLen_le_of_lt w _ (natAbs_lt_two_pow hz.2 hw)
  simp only [entrySyms, intSyms, natSyms, List.length_append, List.length_cons, List.length_map,
    List.length_nil]
  omega

theorem cvo_length_blkE_le {w : ℕ} (hw : 1 ≤ w) : ∀ zs : List (ℤ × ℤ),
    (∀ z ∈ zs, FitsTwos w z.1 ∧ FitsTwos w z.2) → (blkE zs).length ≤ zs.length * (2 * w + 4)
  | [], _ => by simp [blkE, blk]
  | z :: zs, h => by
    rw [WP.W9b.blkE_cons, List.length_append, List.length_cons]
    have h1 := cvo_length_entrySyms_le hw (h z List.mem_cons_self)
    have h2 := cvo_length_blkE_le hw zs (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))
    nlinarith

theorem convOut_runs {w : ℕ} (hw : 1 ≤ w) (zs : List (ℤ × ℤ)) (rdst rw : List Sym)
    (St : CK → List Sym) (hclean : KClean St) (hfit : ∀ z ∈ zs, FitsTwos w z.1 ∧ FitsTwos w z.2)
    (hrdst : BlkTerm rdst) (hD : St kDst = carrSyms w (zs.map fun z => [z]) ++ rdst)
    (hwout : St kWout = hdrSyms [w] ++ rw) :
    Runs convOutProg St (Function.update (Function.update St kDst rdst) kS
      (streamSyms [zs.toArray] ++ St kS)) (fun _ => True) (200 * (zs.length * (w + 1) + 1)) := by
  have hstr : streamSyms [zs.toArray] ++ St kS = blkE zs ++ symNode :: symLevel :: St kS := by
    simp [streamSyms, nodeSyms]
  rw [hstr]
  have hT0 : St kT = [] := hclean CE.t
  have hA0 : St kRA = [] := hclean CE.ra
  have hB0 : St kRB = [] := hclean CE.rb
  have hCN0 : St kCN = [] := hclean CE.cn
  rcases zs with _ | ⟨z, zs'⟩
  · have hD0 : St kDst = rdst := by rw [hD, carrSyms_nil, List.nil_append]
    refine WP.W9b.runs_post (WP.W9b.runs_ite_false
      (WP.W9b.runs_mono (runs_peekK kDst St) (fun v hv => by
        show optIsBit v.1 = false
        rw [hv, hD0]; exact cvo_optIsBit_of_blkTerm hrdst) le_rfl)
      (WP.W9b.runs_seq (runs_pushK kS symLevel St) (runs_pushK kS symNode _))) ?_ (by simp)
    have hb : blkE ([] : List (ℤ × ℤ)) = [] := by simp [blkE, blk]
    rw [hb, List.nil_append]
    funext k
    rcases k with p | e
    · cases p <;> simp [Function.update_apply, hD0]
    · cases e <;> simp [Function.update_apply]
  · have hD1 : St kDst = recSyms (crecBits w [z]) ++ (carrSyms w (zs'.map fun z => [z]) ++ rdst) := by
      rw [hD, carrSyms_cons, List.append_assoc]
    have hwout' : St kWout = natSyms w ++ Sym.mark :: rw := by rw [hwout]; simp [hdrSyms]
    have hg : Sym.mark ∉ (blkE (z :: zs')).reverse := by
      rw [List.mem_reverse]; exact cvo_mark_not_mem_blkE _
    have h3 : Runs (.seq (.peek kDst fun v o => (o, v.2)) recordsLoop)
        (Function.update (Function.update St kT (Sym.mark :: St kT)) kRA
          (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA))
        (Function.update (Function.update (Function.update (Function.update St kT
          (Sym.mark :: St kT)) kRA (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA)) kDst
          rdst) kT
          ((blkE (z :: zs')).reverse ++
            Function.update (Function.update St kT (Sym.mark :: St kT)) kRA
              (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA) kT))
        (fun _ => True) (1 + ((z :: zs').length * (40 * w + 41) + 1)) := by
      refine runs_seq_eval (runs_peekK kDst _) fun v hv => ?_
      obtain ⟨v', t, e, ht⟩ := recordsLoop_eval hw (z :: zs') rdst
        (Function.update (Function.update St kT (Sym.mark :: St kT)) kRA
          (ruler w ++ Function.update St kT (Sym.mark :: St kT) kRA)) v hrdst hfit
        (by simp [Function.update_apply, hD])
        (by simp [Function.update_apply, hA0]) (by simp [Function.update_apply, hB0]) hv
      exact ⟨v', t, e, trivial, ht⟩
    refine WP.W9b.runs_post (WP.W9b.runs_ite_true
      (WP.W9b.runs_mono (runs_peekK kDst St) (fun v hv => by
        show optIsBit v.1 = true
        rw [hv, hD1]; exact recHead_isBit w hw z _) le_rfl)
      (WP.W9b.runs_seq (runs_pushK kT Sym.mark St)
      (WP.W9b.runs_seq (rulerProg_runs kWout (by decide) (by decide) w (Sym.mark :: rw) _
          (TermOK.cons rfl _) (by simp [Function.update_apply, hwout'])
          (by simp [Function.update_apply, hCN0]))
      (WP.W9b.runs_seq h3
      (WP.W9b.runs_seq (runs_libC fun r => ⟨none, _, WP.Top.clearStk_eval kRA [] r _, le_refl _⟩)
      (WP.W9b.runs_seq (runs_pushK kS symLevel _)
      (WP.W9b.runs_seq (runs_pushK kS symNode _)
        (WP.W9comp.runs_rewind lC (src := kT) (dst := kS) (by decide) Sym.mark
          (blkE (z :: zs')).reverse [] _ hg
          (by simp [Function.update_apply, hT0]))))))))) ?_ ?_
    · rw [List.reverse_reverse]
      funext k
      rcases k with p | e
      · cases p <;> simp [Function.update_apply]
      · cases e <;> simp [Function.update_apply, hT0, hA0, hB0, hCN0]
    · have hb := bitLen_le_self w
      have hd := WP.W9b.decSum_le w
      have hlenE := cvo_length_blkE_le hw (z :: zs') hfit
      have hn : 1 ≤ (z :: zs').length := by simp
      have h4 : w ≤ (z :: zs').length * w := Nat.le_mul_of_pos_left w hn
      simp only [Function.update_apply, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte,
        eq_self_iff_true, hA0, List.append_nil, List.length_replicate, List.length_reverse, ruler]
      generalize (blkE (z :: zs')).length = m at hlenE ⊢
      generalize (z :: zs').length = n at hn h4 hlenE ⊢
      nlinarith [hn, h4, hb, hd, hlenE]

end SubNLogN.Machine.Pipe.ConvAux

namespace SubNLogN.Machine.Pipe

open TMFw TMFw.Contracts SubNLogN.Machine.Pipe.ConvAux

/-- **`ConvOutStmt`, proved.** The program `convOutProg` (`ConvAux`) with the scratch stacks `CE`,
registers `CReg` and constant `C = 200`. -/
theorem convOut_holds : ConvOutStmt := by
  refine ⟨200, fun _ => ⟨CE, inferInstance, inferInstance, CReg, convOutProg, inferInstance,
    ⟨(none, false, false)⟩, closed_convOutProg, ?_⟩⟩
  intro w zs rdst rw S hclean hw hfit hrdst hD hwout
  exact convOut_runs hw zs rdst rw S hclean hfit hrdst hD hwout

end SubNLogN.Machine.Pipe
