/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsList
import SubNLogN.Machine.Bridge.SolveRec

/-!
# SOL-PARAM-ROWS (2): ruler-counted bit loops

Bit-level programs of the solver parameter row kernel (`SolParamRowsStmt`), over an arbitrary stack
type `K` and the register `BReg = Option Sym × Bool` (a symbol and a carry bit):
* `rLoop RU RV src dst f`: while the ruler stack `RU` has a bit on top, move one ruler bit to `RV`,
  pop one bit `b` of `src` and push the output bit `(f b c).1` on `dst`, carry `c := (f b c).2`.
  Hence a ruler of `n` bits moves exactly `n` bits (`rLoop_eval`).
* `rField`: the loop from a given carry, followed by moving the ruler back (`rField_eval`).
With `f = fId` this moves a field reversed; with `f = fNeg` (the negation ripple `negBit` of
`K1/Twos.lean`) it negates a two's-complement field.

All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

/-- Register: a symbol and a carry bit. -/
abbrev BReg : Type := Option Sym × Bool

/-- Programs with register `BReg`. -/
abbrev BProg (K : Type) : Type := Prog K (fun _ => Sym) BReg

section Defs

variable {K : Type}

/-- The bit of the register symbol (`false` if it is not a bit). -/
def regBit (v : BReg) : Bool :=
  match v.1 with
  | some (.bit b) => b
  | _ => false

/-- Loop test: the register symbol is a bit. -/
def isBitB (v : BReg) : Bool :=
  match v.1 with
  | some (.bit _) => true
  | _ => false

def peekB (k : K) : BProg K := .peek k (fun v o => (o, v.2))
def popB (k : K) : BProg K := .pop k (fun v o => (o, v.2))
def pushCB (k : K) (x : Sym) : BProg K := .push k (fun _ => x)
/-- Push the register symbol. -/
def pushRB (k : K) : BProg K := .push k (fun v => v.1.getD .sep)
def pushFB (k : K) (f : Bool → Bool → Bool × Bool) : BProg K :=
  .push k (fun v => .bit (f (regBit v) v.2).1)
def carryFB (f : Bool → Bool → Bool × Bool) : BProg K := .load (fun v => (v.1, (f (regBit v) v.2).2))
def setCarry (c : Bool) : BProg K := .load (fun v => (v.1, c))

/-- One ruler step. -/
def rBody (RU RV src dst : K) (f : Bool → Bool → Bool × Bool) : BProg K :=
  .seq (popB RU) (.seq (pushCB RV (.bit false)) (.seq (popB src)
    (.seq (pushFB dst f) (.seq (carryFB f) (peekB RU)))))

/-- The ruler loop. -/
def rLoop (RU RV src dst : K) (f : Bool → Bool → Bool × Bool) : BProg K :=
  .loop isBitB (rBody RU RV src dst f)

/-- Output bits of the ripple of `f` from carry `c`. -/
def rip (f : Bool → Bool → Bool × Bool) : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: bs => (f b c).1 :: rip f (f b c).2 bs

/-- Final carry of the ripple. -/
def ripC (f : Bool → Bool → Bool × Bool) : Bool → List Bool → Bool
  | c, [] => c
  | c, b :: bs => ripC f (f b c).2 bs

/-- Identity bit function. -/
def fId (b c : Bool) : Bool × Bool := (b, c)

/-- Negation bit function (`K1.negBit` with the operand seen twice). -/
def fNeg (b c : Bool) : Bool × Bool := K1.negBit b b c

theorem rip_fId (c : Bool) : ∀ bs : List Bool, rip fId c bs = bs
  | [] => rfl
  | b :: bs => by simp [rip, fId, rip_fId c bs]

theorem rip_fNeg_eq (c : Bool) : ∀ bs : List Bool, rip fNeg c bs = K1.ripOut K1.negBit c bs bs
  | [] => rfl
  | b :: bs => by simp [rip, fNeg, rip_fNeg_eq _ bs]

theorem length_rip (f : Bool → Bool → Bool × Bool) : ∀ (c : Bool) (bs : List Bool),
    (rip f c bs).length = bs.length
  | _, [] => rfl
  | c, b :: bs => by simp [rip, length_rip f _ bs]

end Defs

section Eval

variable {K : Type} [DecidableEq K]

theorem rBody_eval {RU RV src dst : K} (h1 : RU ≠ RV) (h2 : RU ≠ src) (h3 : RU ≠ dst)
    (h4 : RV ≠ src) (h5 : RV ≠ dst) (h6 : src ≠ dst) (f : Bool → Bool → Bool × Bool)
    (x : Option Sym) (c b : Bool) (L LS : List Sym) (S : K → List Sym)
    (hRU : S RU = Sym.bit false :: L) (hsrc : S src = Sym.bit b :: LS) :
    Eval [] (rBody RU RV src dst f) ⟨(x, c), S⟩
      ⟨(L.head?, (f b c).2),
        Function.update (Function.update (Function.update (Function.update S RU L) RV
          (Sym.bit false :: S RV)) src LS) dst (Sym.bit (f b c).1 :: S dst)⟩ 6 := by
  set S1 := Function.update S RU L with hS1
  set S2 := Function.update S1 RV (Sym.bit false :: S RV) with hS2
  set S3 := Function.update S2 src LS with hS3
  set S4 := Function.update S3 dst (Sym.bit (f b c).1 :: S dst) with hS4
  have e1 : Eval [] (popB RU) ⟨(x, c), S⟩ ⟨(some (Sym.bit false), c), S1⟩ 1 := by
    have := Eval.pop [] RU (fun (v : BReg) o => (o, v.2)) (x, c) S
    rw [hRU] at this
    exact this
  have e2 : Eval [] (pushCB RV (Sym.bit false)) ⟨(some (Sym.bit false), c), S1⟩
      ⟨(some (Sym.bit false), c), S2⟩ 1 := by
    have := Eval.push [] RV (fun (_ : BReg) => Sym.bit false) (some (Sym.bit false), c) S1
    rw [hS1, Function.update_of_ne (Ne.symm h1)] at this
    exact this
  have hS2src : S2 src = Sym.bit b :: LS := by
    rw [hS2, hS1, Function.update_of_ne (Ne.symm h4), Function.update_of_ne (Ne.symm h2), hsrc]
  have e3 : Eval [] (popB src) ⟨(some (Sym.bit false), c), S2⟩ ⟨(some (Sym.bit b), c), S3⟩ 1 := by
    have := Eval.pop [] src (fun (v : BReg) o => (o, v.2)) (some (Sym.bit false), c) S2
    rw [hS2src] at this
    exact this
  have hS3dst : S3 dst = S dst := by
    rw [hS3, hS2, hS1, Function.update_of_ne (Ne.symm h6), Function.update_of_ne (Ne.symm h5),
      Function.update_of_ne (Ne.symm h3)]
  have e4 : Eval [] (pushFB dst f) ⟨(some (Sym.bit b), c), S3⟩ ⟨(some (Sym.bit b), c), S4⟩ 1 := by
    have := Eval.push [] dst (fun (v : BReg) => Sym.bit (f (regBit v) v.2).1) (some (Sym.bit b), c) S3
    rw [hS3dst] at this
    exact this
  have e5 : Eval [] (carryFB (K := K) f) ⟨(some (Sym.bit b), c), S4⟩
      ⟨(some (Sym.bit b), (f b c).2), S4⟩ 1 :=
    Eval.load [] _ _ _
  have hS4RU : S4 RU = L := by
    rw [hS4, hS3, hS2, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
      hS1, Function.update_self]
  have e6 : Eval [] (peekB RU) ⟨(some (Sym.bit b), (f b c).2), S4⟩ ⟨(L.head?, (f b c).2), S4⟩ 1 := by
    have := Eval.peek [] RU (fun (v : BReg) o => (o, v.2)) (some (Sym.bit b), (f b c).2) S4
    rw [hS4RU] at this
    exact this
  exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))

theorem isBitB_head?_of_termOK {L : List Sym} (h : TermOK L) (c : Bool) :
    isBitB (L.head?, c) = false := by
  cases L with
  | nil => rfl
  | cons a L =>
    have ha := h a rfl
    cases a <;> simp_all [isBitB, Sym.isBit]

/-- **The ruler loop**, exact: a ruler of `|bs|` bits moves the bits `bs` of `src` through `f`. -/
theorem rLoop_eval {RU RV src dst : K} (h1 : RU ≠ RV) (h2 : RU ≠ src) (h3 : RU ≠ dst)
    (h4 : RV ≠ src) (h5 : RV ≠ dst) (h6 : src ≠ dst) (f : Bool → Bool → Bool × Bool)
    (ruRest : List Sym) (hru : TermOK ruRest) :
    ∀ (bs : List Bool) (c : Bool) (srcRest : List Sym) (S : K → List Sym),
      S RU = List.replicate bs.length (Sym.bit false) ++ ruRest →
      S src = bs.map Sym.bit ++ srcRest →
      Eval [] (rLoop RU RV src dst f) ⟨((S RU).head?, c), S⟩
        ⟨(ruRest.head?, ripC f c bs),
          Function.update (Function.update (Function.update (Function.update S RU ruRest) RV
            (List.replicate bs.length (Sym.bit false) ++ S RV)) src srcRest) dst
            ((rip f c bs).reverse.map Sym.bit ++ S dst)⟩
        (7 * bs.length + 1)
  | [], c, srcRest, S, hRU, hsrc => by
    simp only [List.length_nil, List.replicate_zero, List.nil_append] at hRU hsrc
    have hc : isBitB ((S RU).head?, c) = false := by
      rw [hRU]; exact isBitB_head?_of_termOK hru c
    refine (Eval.loop_false hc).of_eq ?_ (by simp)
    congr 1
    · simp [hRU, ripC]
    · funext k
      simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append, rip,
        List.reverse_nil, List.map_nil]
      split_ifs with ha hb hc hd <;> subst_vars <;> simp_all
  | b :: bs, c, srcRest, S, hRU, hsrc => by
    have hRU' : S RU = Sym.bit false :: (List.replicate bs.length (Sym.bit false) ++ ruRest) := by
      rw [hRU]; simp [List.replicate_succ]
    have hsrc' : S src = Sym.bit b :: (bs.map Sym.bit ++ srcRest) := by rw [hsrc]; rfl
    have eb := rBody_eval h1 h2 h3 h4 h5 h6 f ((S RU).head?) c b _ _ S hRU' hsrc'
    set S' := Function.update (Function.update (Function.update (Function.update S RU
      (List.replicate bs.length (Sym.bit false) ++ ruRest)) RV (Sym.bit false :: S RV)) src
      (bs.map Sym.bit ++ srcRest)) dst (Sym.bit (f b c).1 :: S dst) with hS'
    have hS'RU : S' RU = List.replicate bs.length (Sym.bit false) ++ ruRest := by
      rw [hS', Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
        Function.update_self]
    have hS'src : S' src = bs.map Sym.bit ++ srcRest := by
      rw [hS', Function.update_of_ne h6, Function.update_self]
    have ih := rLoop_eval h1 h2 h3 h4 h5 h6 f ruRest hru bs (f b c).2 srcRest S' hS'RU hS'src
    rw [← hS'RU] at eb
    have hc : isBitB ((S RU).head?, c) = true := by rw [hRU']; rfl
    have hRV : S' RV = Sym.bit false :: S RV := by
      rw [hS', Function.update_of_ne h5, Function.update_of_ne h4, Function.update_self]
    have hdst : S' dst = Sym.bit (f b c).1 :: S dst := by rw [hS', Function.update_self]
    refine (Eval.loop_true hc eb ih).of_eq ?_ (by simp; ring)
    congr 1
    funext k
    simp only [Function.update_apply, hRV, hdst]
    split_ifs with ha hb hc hd <;> subst_vars <;>
      simp_all [rip, List.replicate_succ', List.reverse_cons]

/-- The ruler pass from carry `c0`: set the carry, run the loop, move the ruler back. -/
def rField (RU RV src dst : K) (f : Bool → Bool → Bool × Bool) (c0 : Bool) : BProg K :=
  .seq (setCarry c0) (.seq (peekB RU) (.seq (rLoop RU RV src dst f)
    ((moveBlock RV RU).liftRegs (Lens.fst (Option Sym) Bool))))

/-- **A ruler pass**, exact (`RV` holds no bit on top before; the ruler is restored). -/
theorem rField_eval {RU RV src dst : K} (h1 : RU ≠ RV) (h2 : RU ≠ src) (h3 : RU ≠ dst)
    (h4 : RV ≠ src) (h5 : RV ≠ dst) (h6 : src ≠ dst) (f : Bool → Bool → Bool × Bool) (c0 : Bool)
    (ruRest : List Sym) (hru : TermOK ruRest) (bs : List Bool) (srcRest : List Sym)
    (S : K → List Sym) (hRU : S RU = List.replicate bs.length (Sym.bit false) ++ ruRest)
    (hsrc : S src = bs.map Sym.bit ++ srcRest) (hRV : TermOK (S RV)) (v : BReg) :
    ∃ v', Eval [] (rField RU RV src dst f c0) ⟨v, S⟩
      ⟨v', Function.update (Function.update S src srcRest) dst
        ((rip f c0 bs).reverse.map Sym.bit ++ S dst)⟩ (10 * bs.length + 7) := by
  have e1 : Eval [] (setCarry (K := K) c0) ⟨v, S⟩ ⟨(v.1, c0), S⟩ 1 := Eval.load [] _ _ _
  have e2 : Eval [] (peekB RU) ⟨(v.1, c0), S⟩ ⟨((S RU).head?, c0), S⟩ 1 := Eval.peek [] _ _ _ _
  have e3 := rLoop_eval h1 h2 h3 h4 h5 h6 f ruRest hru bs c0 srcRest S hRU hsrc
  set S3 := Function.update (Function.update (Function.update (Function.update S RU ruRest) RV
    (List.replicate bs.length (Sym.bit false) ++ S RV)) src srcRest) dst
    ((rip f c0 bs).reverse.map Sym.bit ++ S dst) with hS3
  have hS3RV : S3 RV = (List.replicate bs.length false).map Sym.bit ++ S RV := by
    rw [hS3, Function.update_of_ne h5, Function.update_of_ne h4, Function.update_self,
      List.map_replicate]
  have e4 := Eval.liftRegs (Lens.fst (Option Sym) Bool)
    (moveBlock_eval (Ne.symm h1) [] ruRest.head? (List.replicate bs.length false) (S RV) S3 hRV hS3RV)
    (ruRest.head?, ripC f c0 bs) rfl
  refine ⟨((S RV).head?, ripC f c0 bs),
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ (by simp; ring)⟩
  congr 1
  funext k
  have hRU3 : S3 RU = ruRest := by
    rw [hS3, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
      Function.update_self]
  simp only [Function.update_apply, hRU3, List.reverse_replicate, List.map_replicate]
  split_ifs with ha hb hc hd <;> subst_vars <;> simp_all

end Eval

end SubNLogN.Machine.Bridge.SolveParamsAux
