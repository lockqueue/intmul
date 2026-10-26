import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Basic
import WP.W7k1.IsqrtSpec

/-!
# WP.W7k1.IsqrtProg — the `W7_isqrt` machine program: primitives and loops

The kernel runs the digit-by-digit square root of `WP.W7k1.IsqrtSpec` on the machine.

* Stacks `IK = Loc 2 6`: `kA` (input `a`, restored), `kZ` (destination) and six scratch stacks:
  `kX` (the MSB-first padded bits of `a`), `kR` (remainder, LSB on top), `kQ` (root, LSB on top),
  `kD` (difference, MSB on top), `kC` (copy of the remainder, MSB on top), `kT` (subtrahend bits,
  MSB on top). Every scratch stack gets a `mark` pushed before use, and it is consumed afterwards,
  so scratch contents are arbitrary and restored.
* Registers `IReg = Option Sym × Option Sym × Bool`: two symbol slots and a flag (the borrow, or
  the parity during setup). Library macros run on slot 1 through the lens `L1` (`lift`).

This file: primitive steps with simplified `Eval` lemmas, the bit-serial subtraction loop
(`subLoop_eval`: exactly `subBits`), block dropping (`dropBlk_eval`) and the parity-tracking move
(`parLoop_eval`).
-/

namespace WP.W7k1

open TMFw TMFw.Lib TMFw.Contracts

/-! ## Registers, stacks, primitive steps -/

/-- Registers: two symbol slots and a flag. -/
abbrev IReg := Option Sym × Option Sym × Bool

/-- Local stacks: `.inl 0` = input, `.inl 1` = destination, six scratch stacks. -/
abbrev IK := Loc 2 6

/-- Programs of the kernel. -/
abbrev IProg := Prog IK (fun _ => Sym) IReg

abbrev kA : IK := .inl 0
abbrev kZ : IK := .inl 1
abbrev kX : IK := .inr 0
abbrev kR : IK := .inr 1
abbrev kQ : IK := .inr 2
abbrev kD : IK := .inr 3
abbrev kC : IK := .inr 4
abbrev kT : IK := .inr 5

/-- Pop into slot 1. -/
def pop1 (k : IK) : IProg := .pop k (fun v o => (o, v.2))
/-- Peek into slot 1. -/
def peek1 (k : IK) : IProg := .peek k (fun v o => (o, v.2))
/-- Peek into slot 2. -/
def peek2 (k : IK) : IProg := .peek k (fun v o => (v.1, o, v.2.2))
/-- Push slot 1. -/
def push1 (k : IK) : IProg := .push k (fun v => v.1.getD .sep)
/-- Push slot 2. -/
def push2 (k : IK) : IProg := .push k (fun v => v.2.1.getD .sep)
/-- Push a constant. -/
def pushK (k : IK) (x : Sym) : IProg := .push k (fun _ => x)
/-- Pop and discard. -/
def drop1 (k : IK) : IProg := .pop k (fun v _ => v)
/-- Set the flag. -/
def setF (b : Bool) : IProg := .load (fun v => (v.1, v.2.1, b))
/-- Do nothing (one step). -/
def skipI : IProg := .load id

/-- The library macros' register is slot 1. -/
def L1 : Lens IReg (Option Sym) := Lens.fst (Option Sym) (Option Sym × Bool)

/-- Run a library macro on slot 1. -/
def lift (p : SProg IK) : IProg := p.liftRegs L1

theorem pop1_eval (k : IK) (v : IReg) (S : IK → List Sym) :
    Eval [] (pop1 k) ⟨v, S⟩ ⟨((S k).head?, v.2), Function.update S k (S k).tail⟩ 1 :=
  Eval.pop _ _ _ _ _

theorem peek1_eval (k : IK) (v : IReg) (S : IK → List Sym) :
    Eval [] (peek1 k) ⟨v, S⟩ ⟨((S k).head?, v.2), S⟩ 1 :=
  Eval.peek _ _ _ _ _

theorem peek2_eval (k : IK) (v : IReg) (S : IK → List Sym) :
    Eval [] (peek2 k) ⟨v, S⟩ ⟨(v.1, (S k).head?, v.2.2), S⟩ 1 :=
  Eval.peek _ _ _ _ _

theorem push1_eval (k : IK) (x : Sym) (w : Option Sym × Bool) (S : IK → List Sym) :
    Eval [] (push1 k) ⟨(some x, w), S⟩ ⟨(some x, w), Function.update S k (x :: S k)⟩ 1 :=
  Eval.push _ _ _ _ _

theorem push2_eval (k : IK) (o : Option Sym) (x : Sym) (b : Bool) (S : IK → List Sym) :
    Eval [] (push2 k) ⟨(o, some x, b), S⟩ ⟨(o, some x, b), Function.update S k (x :: S k)⟩ 1 :=
  Eval.push _ _ _ _ _

theorem pushK_eval (k : IK) (x : Sym) (v : IReg) (S : IK → List Sym) :
    Eval [] (pushK k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 :=
  Eval.push _ _ _ _ _

theorem drop1_eval (k : IK) (v : IReg) (S : IK → List Sym) :
    Eval [] (drop1 k) ⟨v, S⟩ ⟨v, Function.update S k (S k).tail⟩ 1 :=
  Eval.pop _ _ _ _ _

theorem setF_eval (b : Bool) (v : IReg) (S : IK → List Sym) :
    Eval [] (setF b) ⟨v, S⟩ ⟨(v.1, v.2.1, b), S⟩ 1 :=
  Eval.load _ _ _ _

theorem skipI_eval (v : IReg) (S : IK → List Sym) : Eval [] skipI ⟨v, S⟩ ⟨v, S⟩ 1 :=
  Eval.load _ _ _ _

theorem lift_moveBlock_eval {src dst : IK} (hne : src ≠ dst) (v : IReg) (es : List Bool)
    (rest : List Sym) (S : IK → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    Eval [] (lift (moveBlock src dst)) ⟨v, S⟩
      ⟨(rest.head?, v.2), Function.update (Function.update S src rest) dst
        (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 4) :=
  Eval.liftRegs L1 (moveBlock_eval hne [] v.1 es rest S hrest hS) v rfl

theorem lift_copyBlock_eval {src dst tmp : IK} (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (v : IReg) (blk : List Bool) (rest : List Sym) (S : IK → List Sym)
    (hrest : TermOK rest) (hS : S src = blk.map Sym.bit ++ rest) :
    Eval [] (lift (copyBlock src dst tmp)) ⟨v, S⟩
      ⟨(some .mark, v.2), Function.update S dst (blk.map Sym.bit ++ S dst)⟩
      (7 * blk.length + 7) :=
  Eval.liftRegs L1 (copyBlock_eval hsd hst hdt [] v.1 blk rest S hrest hS) v rfl

theorem optBit_head?_of_termOK {rest : List Sym} (h : TermOK rest) :
    optBit rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    have := h d rfl
    cases d <;> simp_all [optBit]

/-- Stack functions on `IK` agree iff they agree on the eight named stacks. -/
theorem ik_ext {F G : IK → List Sym} (hA : F kA = G kA) (hZ : F kZ = G kZ) (hX : F kX = G kX)
    (hR : F kR = G kR) (hQ : F kQ = G kQ) (hD : F kD = G kD) (hC : F kC = G kC)
    (hT : F kT = G kT) : F = G := by
  funext k
  rcases k with ⟨i, hi⟩ | ⟨i, hi⟩
  · match i, hi with
    | 0, _ => exact hA
    | 1, _ => exact hZ
  · match i, hi with
    | 0, _ => exact hX
    | 1, _ => exact hR
    | 2, _ => exact hQ
    | 3, _ => exact hD
    | 4, _ => exact hC
    | 5, _ => exact hT

/-! ## Bit-serial subtraction loop -/

/-- One subtraction step: copy the remainder bit to `kC`; take the subtrahend bit from `kQ` (to
`kT`), or `0` once `kQ` shows its terminator; push the difference bit on `kD`; update the borrow;
pop the next remainder bit. -/
def subBody : IProg :=
  .seq (push1 kC) (.seq (peek2 kQ)
    (.seq (.ite (fun v => optIsBit v.2.1) (.seq (drop1 kQ) (push2 kT)) (.seq skipI skipI))
    (.seq (.push kD (fun v => .bit (dBit (optBit v.1) (optBit v.2.1) v.2.2)))
    (.seq (.load (fun v => (v.1, v.2.1, bOut (optBit v.1) (optBit v.2.1) v.2.2)))
      (pop1 kR)))))

/-- The subtraction loop, over the remainder bits. -/
def subLoop : IProg := .loop (fun v => optIsBit v.1) subBody

/-- The stacks after one subtraction step. -/
def subStepStk (e : Bool) (es ts : List Bool) (rest restQ : List Sym) (br : Bool)
    (S : IK → List Sym) : IK → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    kC (.bit e :: S kC)) kQ (ts.tail.map Sym.bit ++ restQ))
    kT ((ts.take 1).map Sym.bit ++ S kT))
    kD (.bit (dBit e (ts.headD false) br) :: S kD))
    kR (es.map Sym.bit ++ rest).tail

theorem subBody_eval (e : Bool) (es ts : List Bool) (rest restQ : List Sym) (s2 : Option Sym)
    (br : Bool) (S : IK → List Sym) (hrQ : TermOK restQ)
    (hR : S kR = es.map Sym.bit ++ rest) (hQ : S kQ = ts.map Sym.bit ++ restQ) :
    ∃ s2', Eval [] subBody ⟨(some (.bit e), s2, br), S⟩
      ⟨((es.map Sym.bit ++ rest).head?, s2', bOut e (ts.headD false) br),
        subStepStk e es ts rest restQ br S⟩ 8 := by
  cases ts with
  | nil =>
    have hc : optIsBit restQ.head? = false := optIsBit_head?_of_termOK hrQ
    have hb : optBit restQ.head? = false := optBit_head?_of_termOK hrQ
    have hQ1 : Function.update S kC (.bit e :: S kC) kQ = restQ := by
      rw [Function.update_of_ne (by decide), hQ]
      rfl
    refine ⟨restQ.head?, ?_⟩
    refine (Eval.seq (push1_eval kC (.bit e) (s2, br) S)
      (Eval.seq (peek2_eval kQ _ _)
      (Eval.seq (Eval.ite_false ?_ (Eval.seq (skipI_eval _ _) (skipI_eval _ _)))
      (Eval.seq (Eval.push [] kD _ _ _)
      (Eval.seq (Eval.load [] _ _ _) (pop1_eval kR _ _)))))).of_eq ?_ rfl
    · show optIsBit (Function.update S kC (.bit e :: S kC) kQ).head? = false
      rw [hQ1]
      exact hc
    · refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [subStepStk, hR, hQ, hb]
  | cons t ts =>
    have hQ1 : Function.update S kC (.bit e :: S kC) kQ = .bit t :: (ts.map Sym.bit ++ restQ) := by
      rw [Function.update_of_ne (by decide), hQ]
      rfl
    refine ⟨some (.bit t), ?_⟩
    refine (Eval.seq (push1_eval kC (.bit e) (s2, br) S)
      (Eval.seq (peek2_eval kQ _ _)
      (Eval.seq (Eval.ite_true ?_ (Eval.seq (drop1_eval kQ _ _) (Eval.push [] kT _ _ _)))
      (Eval.seq (Eval.push [] kD _ _ _)
      (Eval.seq (Eval.load [] _ _ _) (pop1_eval kR _ _)))))).of_eq ?_ rfl
    · show optIsBit (Function.update S kC (.bit e :: S kC) kQ).head? = true
      rw [hQ1]
      rfl
    · refine congrArg₂ St.mk ?_ (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [subStepStk, hR, hQ]

theorem subLoop_eval (es : List Bool) : ∀ (ts : List Bool) (br : Bool) (rest restQ : List Sym)
    (s2 : Option Sym) (S : IK → List Sym),
    ts.length ≤ es.length → TermOK rest → TermOK restQ →
    S kR = (es.map Sym.bit ++ rest).tail → S kQ = ts.map Sym.bit ++ restQ →
    ∃ s2', Eval [] subLoop ⟨((es.map Sym.bit ++ rest).head?, s2, br), S⟩
      ⟨(rest.head?, s2', (subBits es ts br).2),
        Function.update (Function.update (Function.update (Function.update (Function.update S
          kR rest.tail) kC (es.reverse.map Sym.bit ++ S kC)) kQ restQ)
          kT (ts.reverse.map Sym.bit ++ S kT))
          kD ((subBits es ts br).1.reverse.map Sym.bit ++ S kD)⟩ (9 * es.length + 1) := by
  induction es with
  | nil =>
    intro ts br rest restQ s2 S hl hrest _ hR hQ
    have hts : ts = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hts
    refine ⟨s2, (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl⟩
    have hR' : S kR = rest.tail := hR
    have hQ' : S kQ = restQ := hQ
    refine congrArg₂ St.mk rfl (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp +decide [hR', hQ', subBits]
  | cons e es ih =>
    intro ts br rest restQ s2 S hl hrest hrQ hR hQ
    have hR' : S kR = es.map Sym.bit ++ rest := hR
    obtain ⟨s2', hb⟩ := subBody_eval e es ts rest restQ s2 br S hrQ hR' hQ
    have hl' : ts.tail.length ≤ es.length := by
      rw [List.length_tail]
      simp only [List.length_cons] at hl
      omega
    have h1 : subStepStk e es ts rest restQ br S kR = (es.map Sym.bit ++ rest).tail := by
      simp [subStepStk]
    have h2 : subStepStk e es ts rest restQ br S kQ = ts.tail.map Sym.bit ++ restQ := by
      simp +decide [subStepStk]
    obtain ⟨s2'', hl2⟩ := ih ts.tail (bOut e (ts.headD false) br) rest restQ s2'
      (subStepStk e es ts rest restQ br S) hl' hrest hrQ h1 h2
    refine ⟨s2'', (Eval.loop_true (by rfl) hb hl2).of_eq ?_
      (by simp only [List.length_cons]; omega)⟩
    cases ts with
    | nil =>
      refine congrArg₂ St.mk rfl (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [subStepStk, subBits]
    | cons t ts =>
      refine congrArg₂ St.mk rfl (ik_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
        simp +decide [subStepStk, subBits]

/-! ## Dropping a block -/

/-- Pop a bit block and its terminator. -/
def dropBlk (k : IK) : IProg := .seq (pop1 k) (.loop (fun v => optIsBit v.1) (pop1 k))

theorem dropLoop_eval (k : IK) : ∀ (es : List Bool) (rest : List Sym) (w : Option Sym × Bool)
    (S : IK → List Sym), TermOK rest → S k = (es.map Sym.bit ++ rest).tail →
    Eval [] (.loop (fun v : IReg => optIsBit v.1) (pop1 k)) ⟨((es.map Sym.bit ++ rest).head?, w), S⟩
      ⟨(rest.head?, w), Function.update S k rest.tail⟩ (2 * es.length + 1)
  | [], rest, w, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    rw [← hS', Function.update_eq_self]
    rfl
  | e :: es, rest, w, S, hrest, hS => by
    have hS' : S k = es.map Sym.bit ++ rest := hS
    have ih := dropLoop_eval k es rest w (Function.update S k (S k).tail) hrest (by simp [hS'])
    have e1 := pop1_eval k (some (.bit e), w) S
    rw [hS'] at e1 ih
    refine (Eval.loop_true (by rfl) e1 ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

theorem dropBlk_eval (k : IK) (es : List Bool) (rest : List Sym) (v : IReg) (S : IK → List Sym)
    (hrest : TermOK rest) (hS : S k = es.map Sym.bit ++ rest) :
    Eval [] (dropBlk k) ⟨v, S⟩ ⟨(rest.head?, v.2), Function.update S k rest.tail⟩
      (2 * es.length + 2) := by
  have e1 := pop1_eval k v S
  have ih := dropLoop_eval k es rest v.2 (Function.update S k (S k).tail) hrest (by simp [hS])
  rw [hS] at e1 ih
  refine (Eval.seq e1 ih).of_eq ?_ (by omega)
  rw [Function.update_idem]

/-! ## Moving a block while tracking its parity -/

/-- Parity of a list's length. -/
def parity : List Bool → Bool
  | [] => false
  | _ :: l => !parity l

theorem parity_eq (l : List Bool) : parity l = decide (l.length % 2 = 1) := by
  induction l with
  | nil => rfl
  | cons _ l ih =>
    simp only [parity, ih, List.length_cons]
    by_cases h : l.length % 2 = 1
    · have h' : ¬ (l.length + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (l.length + 1) % 2 = 1 := by omega
      simp [h, h']

/-- Move one bit from `kC` to `kX`, toggling the flag. -/
def parBody : IProg := .seq (push1 kX) (.pop kC (fun v o => (o, v.2.1, !v.2.2)))

/-- Move a block from `kC` to `kX` (reversed), the flag accumulating its parity. -/
def parLoop : IProg := .loop (fun v => optIsBit v.1) parBody

theorem parLoop_eval : ∀ (es : List Bool) (rest : List Sym) (s2 : Option Sym) (f : Bool)
    (S : IK → List Sym), TermOK rest → S kC = (es.map Sym.bit ++ rest).tail →
    Eval [] parLoop ⟨((es.map Sym.bit ++ rest).head?, s2, f), S⟩
      ⟨(rest.head?, s2, xor f (parity es)), Function.update (Function.update S kC rest.tail) kX
        (es.reverse.map Sym.bit ++ S kX)⟩ (3 * es.length + 1)
  | [], rest, s2, f, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S kC = rest.tail := hS
    simp only [parity, Bool.xor_false, List.reverse_nil, List.map_nil, List.nil_append]
    rw [← hS', Function.update_eq_self, Function.update_eq_self]
  | e :: es, rest, s2, f, S, hrest, hS => by
    have hS' : S kC = es.map Sym.bit ++ rest := hS
    have e1 : Eval [] parBody ⟨(some (.bit e), s2, f), S⟩
        ⟨((es.map Sym.bit ++ rest).head?, s2, !f),
          Function.update (Function.update S kX (.bit e :: S kX)) kC (es.map Sym.bit ++ rest).tail⟩
        2 := by
      refine (Eval.seq (push1_eval kX (.bit e) (s2, f) S) (Eval.pop [] kC _ _ _)).of_eq ?_ rfl
      have hC : Function.update S kX (.bit e :: S kX) kC = es.map Sym.bit ++ rest := by
        rw [Function.update_of_ne (by decide), hS']
      rw [hC]
    have ih := parLoop_eval es rest s2 (!f)
      (Function.update (Function.update S kX (.bit e :: S kX)) kC (es.map Sym.bit ++ rest).tail)
      hrest (by simp)
    refine (Eval.loop_true (by rfl) e1 ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    have hp : xor (!f) (parity es) = xor f (parity (e :: es)) := by
      simp only [parity]
      cases f <;> cases parity es <;> rfl
    rw [hp]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all +decide

#assert_std_axioms pop1_eval peek1_eval peek2_eval push1_eval push2_eval pushK_eval drop1_eval
  setF_eval skipI_eval lift_moveBlock_eval lift_copyBlock_eval optBit_head?_of_termOK
  subBody_eval subLoop_eval dropLoop_eval dropBlk_eval parity_eq parLoop_eval

end WP.W7k1
