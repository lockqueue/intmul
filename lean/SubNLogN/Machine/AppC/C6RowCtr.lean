/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RowCost
import SubNLogN.Machine.AppC.C6TArith
import WP.W6a.DivMod

/-!
# Lemma A.8 row padding: the counter kernel (`Machine/AppC/C6RowCtr.lean`)

`c6RowCtr_of : 2 ≤ q → C6TPushSpec q → C6WPushSpec → C6RowCtrSpec q` (0 `sorry`): from `e, G, B`
compute `K1 = R·Z` and `K2 = (R' − R)·Z` in binary (`R = c6R q e = q^{2t}`, `t = c6T q e`,
`R' = c6Rp q e = W·⌈R/W⌉`, `W = W_b^k`, `Z = c6Zq q e G B`). Steps: `t`, `W` by the kernels of
`C6TArith.lean`; `R := 1·(q²)^t` (`powMulN`); `R' := W·((R + W − 1)/W)` (`addN`, `subN`, the long
division `W6a_divModNat`, `mulN`); `ℓ := e − t`, `Z := G·q^ℓ·q^ℓ·B`; `K1 := R·Z`,
`K2 := (R' − R)·Z` pushed on the output stacks; every scratch value (each above a `mark`) is
dropped. Every cost term is polynomial in `E = bitLen (R·Z) + 2` (all values are `≤ 2·R·Z`, and
`e < E` since `R·Z ≥ q^{2e}`), and `E³ ≤ 48·R·Z`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6RowAux

open NatArith AppC.C6JoinAux

/-! ## Layout -/

/-- Private stacks of the counter kernel. -/
inductive CS where
  | t | W | R | one | a | b | Qt | Rm | Rp | l | Z | Z2 | Dd | A | Bs | Acc | Tm | Kc | Q | Td
  deriving DecidableEq

instance instFintypeCS : Fintype CS :=
  Fintype.ofList [.t, .W, .R, .one, .a, .b, .Qt, .Rm, .Rp, .l, .Z, .Z2, .Dd, .A, .Bs, .Acc, .Tm,
    .Kc, .Q, .Td] (by intro x; cases x <;> decide)

/-- Scratch of the counter kernel: private stacks, then the scratch of the `t`, `W` and division
kernels. -/
abbrev CE (ET EW : Type) (md : ℕ) : Type := CS ⊕ ET ⊕ EW ⊕ Fin md

instance instDecEqCE {ET EW : Type} {md : ℕ} [DecidableEq ET] [DecidableEq EW] :
    DecidableEq (CE ET EW md) :=
  inferInstanceAs (DecidableEq (CS ⊕ ET ⊕ EW ⊕ Fin md))

instance (priority := high) instDecEqKC {ET EW : Type} {md : ℕ} [DecidableEq ET]
    [DecidableEq EW] : DecidableEq (KLoc (Fin 5) (CE ET EW md)) :=
  @instDecidableEqSum (Fin 5) (CE ET EW md) _ instDecEqCE

instance instFintypeCE {ET EW : Type} {md : ℕ} [Fintype ET] [Fintype EW] :
    Fintype (CE ET EW md) :=
  inferInstanceAs (Fintype (CS ⊕ ET ⊕ EW ⊕ Fin md))

/-- Registers: the arithmetic registers, then those of the `t`, `W` and division kernels. -/
abbrev CR (RT RW RD : Type) : Type := NatArith.Reg × RT × RW × RD

section Lenses

variable {RT RW RD : Type}

def lN : Lens (CR RT RW RD) NatArith.Reg := Lens.fst _ _

def lT : Lens (CR RT RW RD) RT := (Lens.snd _ _).comp (Lens.fst _ _)

def lWk : Lens (CR RT RW RD) RW := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))

def lD : Lens (CR RT RW RD) RD := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))

end Lenses

section Layout

variable {ET EW : Type} {md : ℕ}

/-- A numeric code of a stack (named `0..4`, the call slots `t, W, b, Qt, Rm` `10..14`, other
private `50`, kernel scratch `100`). -/
def ccode : KLoc (Fin 5) (CE ET EW md) → ℕ
  | .inl i => i.val
  | .inr (.inl .t) => 10
  | .inr (.inl .W) => 11
  | .inr (.inl .b) => 12
  | .inr (.inl .Qt) => 13
  | .inr (.inl .Rm) => 14
  | .inr (.inl _) => 50
  | .inr (.inr _) => 100

/-- Stack map of the threshold kernel: `e` (named `0`), result on `t`. -/
def ιT : KLoc (Fin 2) ET → KLoc (Fin 5) (CE ET EW md)
  | .inl i => ![.inl 0, .inr (.inl .t)] i
  | .inr x => .inr (.inr (.inl x))

/-- Stack map of the `W_b^k` kernel: `e` (named `0`), result on `W`. -/
def ιW : KLoc (Fin 2) EW → KLoc (Fin 5) (CE ET EW md)
  | .inl i => ![.inl 0, .inr (.inl .W)] i
  | .inr x => .inr (.inr (.inr (.inl x)))

/-- Stack map of the long division: `b ÷ W`, quotient on `Qt`, remainder on `Rm`. -/
def ιD : Loc 4 md → KLoc (Fin 5) (CE ET EW md)
  | .inl i => ![.inr (.inl .b), .inr (.inl .W), .inr (.inl .Qt), .inr (.inl .Rm)] i
  | .inr x => .inr (.inr (.inr (.inr x)))

theorem ccode_ιT (k : Fin 2) :
    ccode (ιT (ET := ET) (EW := EW) (md := md) (.inl k)) = (![0, 10] k : ℕ) := by
  fin_cases k <;> rfl

theorem ccode_ιW (k : Fin 2) :
    ccode (ιW (ET := ET) (EW := EW) (md := md) (.inl k)) = (![0, 11] k : ℕ) := by
  fin_cases k <;> rfl

theorem ccode_ιD (k : Fin 4) :
    ccode (ιD (ET := ET) (EW := EW) (md := md) (.inl k)) = (![12, 11, 13, 14] k : ℕ) := by
  fin_cases k <;> rfl

theorem ιT_injective : Function.Injective (ιT (ET := ET) (EW := EW) (md := md)) := by
  have hv : Function.Injective (fun k : Fin 2 => (![0, 10] k : ℕ)) := by decide
  have hlt : ∀ k : Fin 2, (![0, 10] k : ℕ) < 50 := by decide
  rintro (a | a) (b | b) h
  · have := congrArg ccode h
    rw [ccode_ιT, ccode_ιT] at this
    exact congrArg Sum.inl (hv this)
  · have h1 : ccode (ιT (ET := ET) (EW := EW) (md := md) (.inl a)) = 100 := congrArg ccode h
    rw [ccode_ιT] at h1
    have := hlt a
    omega
  · have h1 : 100 = ccode (ιT (ET := ET) (EW := EW) (md := md) (.inl b)) := congrArg ccode h
    rw [ccode_ιT] at h1
    have := hlt b
    omega
  · simp only [ιT, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem ιW_injective : Function.Injective (ιW (ET := ET) (EW := EW) (md := md)) := by
  have hv : Function.Injective (fun k : Fin 2 => (![0, 11] k : ℕ)) := by decide
  have hlt : ∀ k : Fin 2, (![0, 11] k : ℕ) < 50 := by decide
  rintro (a | a) (b | b) h
  · have := congrArg ccode h
    rw [ccode_ιW, ccode_ιW] at this
    exact congrArg Sum.inl (hv this)
  · have h1 : ccode (ιW (ET := ET) (EW := EW) (md := md) (.inl a)) = 100 := congrArg ccode h
    rw [ccode_ιW] at h1
    have := hlt a
    omega
  · have h1 : 100 = ccode (ιW (ET := ET) (EW := EW) (md := md) (.inl b)) := congrArg ccode h
    rw [ccode_ιW] at h1
    have := hlt b
    omega
  · simp only [ιW, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem ιD_injective : Function.Injective (ιD (ET := ET) (EW := EW) (md := md)) := by
  have hv : Function.Injective (fun k : Fin 4 => (![12, 11, 13, 14] k : ℕ)) := by decide
  have hlt : ∀ k : Fin 4, (![12, 11, 13, 14] k : ℕ) < 50 := by decide
  rintro (a | a) (b | b) h
  · have := congrArg ccode h
    rw [ccode_ιD, ccode_ιD] at this
    exact congrArg Sum.inl (hv this)
  · have h1 : ccode (ιD (ET := ET) (EW := EW) (md := md) (.inl a)) = 100 := congrArg ccode h
    rw [ccode_ιD] at h1
    have := hlt a
    omega
  · have h1 : 100 = ccode (ιD (ET := ET) (EW := EW) (md := md) (.inl b)) := congrArg ccode h
    rw [ccode_ιD] at h1
    have := hlt b
    omega
  · simp only [ιD, Sum.inr.injEq] at h
    rw [h]

end Layout

/-! ## Programs -/

section Progs

variable {ET EW : Type} {md : ℕ}

/-- `R := 1·(q²)^t` above a `mark`. -/
def pR (q : ℕ) : Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) NatArith.Reg :=
  .seq (pushMark (.inr (.inl .R))) (.seq (pushNat (.inr (.inl .R)) 1)
    (powMulN (.inr (.inl .R)) (q ^ 2) (.inr (.inl .t)) (.inr (.inl .Kc)) (.inr (.inl .Tm))
      (.inr (.inl .Q)) (.inr (.inl .Td)) (.inr (.inl .A)) (.inr (.inl .Bs)) (.inr (.inl .Acc))))

/-- `one := 1`, `a := R + W`, `b := a − 1`, floors for the quotient and the remainder. -/
def pA : Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) NatArith.Reg :=
  .seq (pushMark (.inr (.inl .one))) (.seq (pushNat (.inr (.inl .one)) 1)
  (.seq (pushMark (.inr (.inl .a)))
  (.seq (addN (.inr (.inl .R)) (.inr (.inl .W)) (.inr (.inl .a)) (.inr (.inl .A)) (.inr (.inl .Bs))
      (.inr (.inl .Acc)))
  (.seq (pushMark (.inr (.inl .b)))
  (.seq (subN (.inr (.inl .a)) (.inr (.inl .one)) (.inr (.inl .b)) (.inr (.inl .A))
      (.inr (.inl .Bs)) (.inr (.inl .Acc)))
  (.seq (pushMark (.inr (.inl .Qt))) (pushMark (.inr (.inl .Rm)))))))))

/-- `Rp := W·Qt`; drop `Rm, Qt, b, a, one`. -/
def pC : Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) NatArith.Reg :=
  .seq (pushMark (.inr (.inl .Rp)))
  (.seq (mulN (.inr (.inl .W)) (.inr (.inl .Qt)) (.inr (.inl .Rp)) (.inr (.inl .A)) (.inr (.inl .Bs))
      (.inr (.inl .Acc)) (.inr (.inl .Tm)))
  (.seq (dropF (.inr (.inl .Rm))) (.seq (dropF (.inr (.inl .Qt))) (.seq (dropF (.inr (.inl .b)))
  (.seq (dropF (.inr (.inl .a))) (dropF (.inr (.inl .one))))))))

/-- `l := e − t`, `Z := G·q^l·q^l`, `Z2 := Z·B`; drop `Z, l`. -/
def pZ (q : ℕ) : Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) NatArith.Reg :=
  .seq (pushMark (.inr (.inl .l)))
  (.seq (subN (.inl 0) (.inr (.inl .t)) (.inr (.inl .l)) (.inr (.inl .A)) (.inr (.inl .Bs))
      (.inr (.inl .Acc)))
  (.seq (pushMark (.inr (.inl .Z)))
  (.seq (copyN (.inl 1) (.inr (.inl .Z)) (.inr (.inl .Tm)))
  (.seq (powMulN (.inr (.inl .Z)) q (.inr (.inl .l)) (.inr (.inl .Kc)) (.inr (.inl .Tm))
      (.inr (.inl .Q)) (.inr (.inl .Td)) (.inr (.inl .A)) (.inr (.inl .Bs)) (.inr (.inl .Acc)))
  (.seq (powMulN (.inr (.inl .Z)) q (.inr (.inl .l)) (.inr (.inl .Kc)) (.inr (.inl .Tm))
      (.inr (.inl .Q)) (.inr (.inl .Td)) (.inr (.inl .A)) (.inr (.inl .Bs)) (.inr (.inl .Acc)))
  (.seq (pushMark (.inr (.inl .Z2)))
  (.seq (mulN (.inr (.inl .Z)) (.inl 2) (.inr (.inl .Z2)) (.inr (.inl .A)) (.inr (.inl .Bs))
      (.inr (.inl .Acc)) (.inr (.inl .Tm)))
  (.seq (dropF (.inr (.inl .Z))) (dropF (.inr (.inl .l)))))))))))

/-- `K1 := R·Z2` onto `3`, `Dd := Rp − R`, `K2 := Dd·Z2` onto `4`; drop `Dd`. -/
def pK : Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) NatArith.Reg :=
  .seq (mulN (.inr (.inl .R)) (.inr (.inl .Z2)) (.inl 3) (.inr (.inl .A)) (.inr (.inl .Bs))
      (.inr (.inl .Acc)) (.inr (.inl .Tm)))
  (.seq (pushMark (.inr (.inl .Dd)))
  (.seq (subN (.inr (.inl .Rp)) (.inr (.inl .R)) (.inr (.inl .Dd)) (.inr (.inl .A))
      (.inr (.inl .Bs)) (.inr (.inl .Acc)))
  (.seq (mulN (.inr (.inl .Dd)) (.inr (.inl .Z2)) (.inl 4) (.inr (.inl .A)) (.inr (.inl .Bs))
      (.inr (.inl .Acc)) (.inr (.inl .Tm)))
  (dropF (.inr (.inl .Dd))))))

/-- Drop `Z2, Rp, R, W, t`. -/
def pDrop : Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) NatArith.Reg :=
  .seq (dropF (.inr (.inl .Z2))) (.seq (dropF (.inr (.inl .Rp))) (.seq (dropF (.inr (.inl .R)))
    (.seq (dropF (.inr (.inl .W))) (dropF (.inr (.inl .t))))))

variable {RT RW RD : Type}

/-- `t` and `W` by the kernels of `C6TArith.lean`, each above a `mark`. -/
def pTW (PT : Prog (KLoc (Fin 2) ET) (fun _ => Sym) RT)
    (PW : Prog (KLoc (Fin 2) EW) (fun _ => Sym) RW) :
    Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) (CR RT RW RD) :=
  .seq ((pushMark (.inr (.inl .t))).liftRegs lN) (.seq (callInj ιT lT PT)
    (.seq ((pushMark (.inr (.inl .W))).liftRegs lN) (callInj ιW lWk PW)))

/-- `R' = W·((R + W − 1)/W)` on `Rp`. -/
def pRp (PD : Prog (Loc 4 md) (fun _ => Sym) RD) :
    Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) (CR RT RW RD) :=
  .seq ((pA (ET := ET) (EW := EW) (md := md)).liftRegs lN)
    (.seq (callInj ιD lD PD) ((pC (ET := ET) (EW := EW) (md := md)).liftRegs lN))

/-- **The counter kernel.** -/
def ctrProg (q : ℕ) (PT : Prog (KLoc (Fin 2) ET) (fun _ => Sym) RT)
    (PW : Prog (KLoc (Fin 2) EW) (fun _ => Sym) RW) (PD : Prog (Loc 4 md) (fun _ => Sym) RD) :
    Prog (KLoc (Fin 5) (CE ET EW md)) (fun _ => Sym) (CR RT RW RD) :=
  .seq (pTW PT PW) (.seq ((pR q).liftRegs lN) (.seq (pRp PD) (.seq ((pZ q).liftRegs lN)
    (.seq ((pK).liftRegs lN) ((pDrop).liftRegs lN)))))

theorem closed_pR (q : ℕ) : (pR (ET := ET) (EW := EW) (md := md) q).Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _⟩

theorem closed_pA : (pA (ET := ET) (EW := EW) (md := md)).Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, closed_pushMark _, closed_addN _ _ _ _ _ _,
    closed_pushMark _, closed_subN _ _ _ _ _ _, closed_pushMark _, closed_pushMark _⟩

theorem closed_pC : (pC (ET := ET) (EW := EW) (md := md)).Closed :=
  ⟨closed_pushMark _, closed_mulN _ _ _ _ _ _ _, closed_dropF _, closed_dropF _, closed_dropF _,
    closed_dropF _, closed_dropF _⟩

theorem closed_pZ (q : ℕ) : (pZ (ET := ET) (EW := EW) (md := md) q).Closed :=
  ⟨closed_pushMark _, closed_subN _ _ _ _ _ _, closed_pushMark _, closed_copyN _ _ _,
    closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_pushMark _,
    closed_mulN _ _ _ _ _ _ _, closed_dropF _, closed_dropF _⟩

theorem closed_pK : (pK (ET := ET) (EW := EW) (md := md)).Closed :=
  ⟨closed_mulN _ _ _ _ _ _ _, closed_pushMark _, closed_subN _ _ _ _ _ _,
    closed_mulN _ _ _ _ _ _ _, closed_dropF _⟩

theorem closed_pDrop : (pDrop (ET := ET) (EW := EW) (md := md)).Closed :=
  ⟨closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _⟩

theorem closed_ctrProg (q : ℕ) {PT : Prog (KLoc (Fin 2) ET) (fun _ => Sym) RT}
    {PW : Prog (KLoc (Fin 2) EW) (fun _ => Sym) RW} {PD : Prog (Loc 4 md) (fun _ => Sym) RD}
    (hT : PT.Closed) (hW : PW.Closed) (hD : PD.Closed) : (ctrProg q PT PW PD).Closed :=
  ⟨⟨WP.W9comp.closed_liftRegs _ (closed_pushMark _), closed_callInj _ _ hT,
      WP.W9comp.closed_liftRegs _ (closed_pushMark _), closed_callInj _ _ hW⟩,
    WP.W9comp.closed_liftRegs _ (closed_pR q),
    ⟨WP.W9comp.closed_liftRegs _ closed_pA, closed_callInj _ _ hD,
      WP.W9comp.closed_liftRegs _ closed_pC⟩,
    WP.W9comp.closed_liftRegs _ (closed_pZ q), WP.W9comp.closed_liftRegs _ closed_pK,
    WP.W9comp.closed_liftRegs _ closed_pDrop⟩

end Progs

/-! ## Calls on injective sub-layouts -/

theorem ctrCall_upd1 {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B : K → List Sym} (x : L) (w : List Sym) {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) x w) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) w) (fun _ => True) T := by
  refine runs_callInj hι l (Q := Q) ?_ (fun k hk => Function.update_of_ne (fun h => hk x h.symm) _ _)
  rw [Function.update_comp_eq_of_injective B hι x w]
  exact h

theorem ctrCall_upd2 {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B : K → List Sym} (x0 x1 : L) (w0 w1 : List Sym) {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x0 w0) x1 w1) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update B (ι x0) w0) (ι x1) w1)
      (fun _ => True) T := by
  refine runs_callInj hι l (Q := Q) ?_ (fun k hk => ?_)
  · rw [Function.update_comp_eq_of_injective _ hι x1 w1,
      Function.update_comp_eq_of_injective B hι x0 w0]
    exact h
  · rw [Function.update_of_ne (fun h => hk x1 h.symm), Function.update_of_ne (fun h => hk x0 h.symm)]

/-! ## Runs of the arithmetic phases -/

section RunsArith

variable {ET EW : Type} {md : ℕ} [DecidableEq ET] [DecidableEq EW]

theorem runs_pR {q : ℕ} (hq : 1 ≤ q ^ 2) (t : ℕ) {rt : List Sym} (hrt : TermOK rt)
    (S : KLoc (Fin 5) (CE ET EW md) → List Sym) (ht : S (.inr (.inl .t)) = natSyms t ++ rt) :
    Runs (pR (ET := ET) (EW := EW) (md := md) q) S
      (Function.update S (.inr (.inl .R)) (natSyms (q ^ (2 * t)) ++ Sym.mark :: S (.inr (.inl .R))))
      (fun _ => True) (1 + ((bitLen 1 + 1) + powCost (q ^ 2) 1 t)) := by
  have h1 := runs_pushMark (.inr (.inl .R) : KLoc (Fin 5) (CE ET EW md)) S
  have h2 := runs_pushNat (.inr (.inl .R) : KLoc (Fin 5) (CE ET EW md)) 1
    (Function.update S (.inr (.inl .R)) (Sym.mark :: S (.inr (.inl .R))))
  rw [Function.update_self, Function.update_idem] at h2
  have h3 := runs_powMulN (k := (.inr (.inl .R) : KLoc (Fin 5) (CE ET EW md)))
    (ns := .inr (.inl .t)) (Kc := .inr (.inl .Kc)) (t := .inr (.inl .Tm)) (Q := .inr (.inl .Q))
    (Tdst := .inr (.inl .Td)) (A := .inr (.inl .A)) (Bs := .inr (.inl .Bs))
    (Acc := .inr (.inl .Acc)) (by simp) (q ^ 2) hq 1 t (Sym.mark :: S (.inr (.inl .R))) rt
    (Function.update S (.inr (.inl .R)) (natSyms 1 ++ Sym.mark :: S (.inr (.inl .R))))
    (NatArith.termOK_mark _) hrt (by simp) (by simp [ht])
  rw [Function.update_idem, one_mul, ← pow_mul] at h3
  exact WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 h3)

theorem runs_pA (Rv Wv : ℕ) (hRW : 1 ≤ Rv + Wv) {rR rW : List Sym} (hrR : TermOK rR)
    (hrW : TermOK rW) (S : KLoc (Fin 5) (CE ET EW md) → List Sym)
    (hR : S (.inr (.inl .R)) = natSyms Rv ++ rR) (hW : S (.inr (.inl .W)) = natSyms Wv ++ rW) :
    Runs (pA (ET := ET) (EW := EW) (md := md)) S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (.inr (.inl .one)) (natSyms 1 ++ Sym.mark :: S (.inr (.inl .one))))
        (.inr (.inl .a)) (natSyms (Rv + Wv) ++ Sym.mark :: S (.inr (.inl .a))))
        (.inr (.inl .b)) (natSyms (Rv + Wv - 1) ++ Sym.mark :: S (.inr (.inl .b))))
        (.inr (.inl .Qt)) (Sym.mark :: S (.inr (.inl .Qt))))
        (.inr (.inl .Rm)) (Sym.mark :: S (.inr (.inl .Rm))))
      (fun _ => True) (costA Rv Wv) := by
  have h1 := runs_pushMark (.inr (.inl .one) : KLoc (Fin 5) (CE ET EW md)) S
  have h2 := runs_pushNat (.inr (.inl .one) : KLoc (Fin 5) (CE ET EW md)) 1
    (Function.update S (.inr (.inl .one)) (Sym.mark :: S (.inr (.inl .one))))
  rw [Function.update_self, Function.update_idem] at h2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S (.inr (.inl .one))
      (natSyms 1 ++ Sym.mark :: S (.inr (.inl .one))) := ⟨_, rfl⟩
  rw [← hS2] at h2
  have h3 := runs_pushMark (.inr (.inl .a) : KLoc (Fin 5) (CE ET EW md)) S2
  have l3 : S2 (.inr (.inl .a)) = S (.inr (.inl .a)) := by rw [hS2]; simp
  rw [l3] at h3
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 (.inr (.inl .a))
      (Sym.mark :: S (.inr (.inl .a))) := ⟨_, rfl⟩
  rw [← hS3] at h3
  have h4 := runs_addN (x := (.inr (.inl .R) : KLoc (Fin 5) (CE ET EW md))) (y := .inr (.inl .W))
    (z := .inr (.inl .a)) (t1 := .inr (.inl .A)) (t2 := .inr (.inl .Bs)) (t3 := .inr (.inl .Acc))
    (by simp) Rv Wv rR rW S3 hrR hrW (by rw [hS3, hS2]; simp [hR]) (by rw [hS3, hS2]; simp [hW])
  have l4 : S3 (.inr (.inl .a)) = Sym.mark :: S (.inr (.inl .a)) := by rw [hS3]; simp
  rw [l4] at h4
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update S3 (.inr (.inl .a))
      (natSyms (Rv + Wv) ++ Sym.mark :: S (.inr (.inl .a))) := ⟨_, rfl⟩
  rw [← hS4] at h4
  have h5 := runs_pushMark (.inr (.inl .b) : KLoc (Fin 5) (CE ET EW md)) S4
  have l5 : S4 (.inr (.inl .b)) = S (.inr (.inl .b)) := by rw [hS4, hS3, hS2]; simp
  rw [l5] at h5
  obtain ⟨S5, hS5⟩ : ∃ S5, S5 = Function.update S4 (.inr (.inl .b))
      (Sym.mark :: S (.inr (.inl .b))) := ⟨_, rfl⟩
  rw [← hS5] at h5
  have h6 := runs_subN (x := (.inr (.inl .a) : KLoc (Fin 5) (CE ET EW md)))
    (y := .inr (.inl .one)) (z := .inr (.inl .b)) (t1 := .inr (.inl .A)) (t2 := .inr (.inl .Bs))
    (t3 := .inr (.inl .Acc)) (by simp) (Rv + Wv) 1 (Sym.mark :: S (.inr (.inl .a)))
    (Sym.mark :: S (.inr (.inl .one))) S5 (NatArith.termOK_mark _) (NatArith.termOK_mark _) hRW
    (by rw [hS5, hS4]; simp) (by rw [hS5, hS4, hS3, hS2]; simp)
  have l6 : S5 (.inr (.inl .b)) = Sym.mark :: S (.inr (.inl .b)) := by rw [hS5]; simp
  rw [l6] at h6
  obtain ⟨S6, hS6⟩ : ∃ S6, S6 = Function.update S5 (.inr (.inl .b))
      (natSyms (Rv + Wv - 1) ++ Sym.mark :: S (.inr (.inl .b))) := ⟨_, rfl⟩
  rw [← hS6] at h6
  have h7 := runs_pushMark (.inr (.inl .Qt) : KLoc (Fin 5) (CE ET EW md)) S6
  have l7 : S6 (.inr (.inl .Qt)) = S (.inr (.inl .Qt)) := by rw [hS6, hS5, hS4, hS3, hS2]; simp
  rw [l7] at h7
  obtain ⟨S7, hS7⟩ : ∃ S7, S7 = Function.update S6 (.inr (.inl .Qt))
      (Sym.mark :: S (.inr (.inl .Qt))) := ⟨_, rfl⟩
  rw [← hS7] at h7
  have h8 := runs_pushMark (.inr (.inl .Rm) : KLoc (Fin 5) (CE ET EW md)) S7
  have l8 : S7 (.inr (.inl .Rm)) = S (.inr (.inl .Rm)) := by
    rw [hS7, hS6, hS5, hS4, hS3, hS2]; simp
  rw [l8] at h8
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2
    (WP.W9comp.runs_seq h3 (WP.W9comp.runs_seq h4 (WP.W9comp.runs_seq h5
    (WP.W9comp.runs_seq h6 (WP.W9comp.runs_seq h7 h8))))))) ?_
  rw [hS7, hS6, hS5, hS4, hS3, hS2]
  simp only [Function.update_idem]

theorem runs_pC (Wv Qv Rv bv av : ℕ) {rW X1 X2 X3 X4 X5 : List Sym} (hrW : TermOK rW)
    (S : KLoc (Fin 5) (CE ET EW md) → List Sym)
    (hW : S (.inr (.inl .W)) = natSyms Wv ++ rW)
    (hQt : S (.inr (.inl .Qt)) = natSyms Qv ++ Sym.mark :: X1)
    (hRm : S (.inr (.inl .Rm)) = natSyms Rv ++ Sym.mark :: X2)
    (hb : S (.inr (.inl .b)) = natSyms bv ++ Sym.mark :: X3)
    (ha : S (.inr (.inl .a)) = natSyms av ++ Sym.mark :: X4)
    (hone : S (.inr (.inl .one)) = natSyms 1 ++ Sym.mark :: X5) :
    Runs (pC (ET := ET) (EW := EW) (md := md)) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S (.inr (.inl .Rp)) (natSyms (Wv * Qv) ++ Sym.mark :: S (.inr (.inl .Rp))))
        (.inr (.inl .Rm)) X2) (.inr (.inl .Qt)) X1) (.inr (.inl .b)) X3) (.inr (.inl .a)) X4)
        (.inr (.inl .one)) X5)
      (fun _ => True) (costC Wv Qv Rv bv av) := by
  have h1 := runs_pushMark (.inr (.inl .Rp) : KLoc (Fin 5) (CE ET EW md)) S
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S (.inr (.inl .Rp))
      (Sym.mark :: S (.inr (.inl .Rp))) := ⟨_, rfl⟩
  rw [← hS1] at h1
  have h2 := runs_mulN (x := (.inr (.inl .W) : KLoc (Fin 5) (CE ET EW md))) (y := .inr (.inl .Qt))
    (z := .inr (.inl .Rp)) (A := .inr (.inl .A)) (Bs := .inr (.inl .Bs)) (Acc := .inr (.inl .Acc))
    (T := .inr (.inl .Tm)) (by simp) Wv Qv rW (Sym.mark :: X1) S1 hrW (NatArith.termOK_mark _)
    (by rw [hS1]; simp [hW]) (by rw [hS1]; simp [hQt])
  have l2 : S1 (.inr (.inl .Rp)) = Sym.mark :: S (.inr (.inl .Rp)) := by rw [hS1]; simp
  rw [l2] at h2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 (.inr (.inl .Rp))
      (natSyms (Wv * Qv) ++ Sym.mark :: S (.inr (.inl .Rp))) := ⟨_, rfl⟩
  rw [← hS2] at h2
  have h3 := runs_dropF (.inr (.inl .Rm) : KLoc (Fin 5) (CE ET EW md)) Rv Sym.mark X2 S2 rfl
    (by rw [hS2, hS1]; simp [hRm])
  have h4 := runs_dropF (.inr (.inl .Qt) : KLoc (Fin 5) (CE ET EW md)) Qv Sym.mark X1
    (Function.update S2 (.inr (.inl .Rm)) X2) rfl (by rw [hS2, hS1]; simp [hQt])
  have h5 := runs_dropF (.inr (.inl .b) : KLoc (Fin 5) (CE ET EW md)) bv Sym.mark X3
    (Function.update (Function.update S2 (.inr (.inl .Rm)) X2) (.inr (.inl .Qt)) X1) rfl
    (by rw [hS2, hS1]; simp [hb])
  have h6 := runs_dropF (.inr (.inl .a) : KLoc (Fin 5) (CE ET EW md)) av Sym.mark X4
    (Function.update (Function.update (Function.update S2 (.inr (.inl .Rm)) X2)
      (.inr (.inl .Qt)) X1) (.inr (.inl .b)) X3) rfl (by rw [hS2, hS1]; simp [ha])
  have h7 := runs_dropF (.inr (.inl .one) : KLoc (Fin 5) (CE ET EW md)) 1 Sym.mark X5
    (Function.update (Function.update (Function.update (Function.update S2 (.inr (.inl .Rm)) X2)
      (.inr (.inl .Qt)) X1) (.inr (.inl .b)) X3) (.inr (.inl .a)) X4) rfl
    (by rw [hS2, hS1]; simp [hone])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2
    (WP.W9comp.runs_seq h3 (WP.W9comp.runs_seq h4 (WP.W9comp.runs_seq h5
    (WP.W9comp.runs_seq h6 h7)))))) ?_
  rw [hS2, hS1, Function.update_idem]

theorem runs_pZ {q : ℕ} (hq : 1 ≤ q) (e t G B : ℕ) (hte : t ≤ e) {r0 rt r1 r2 : List Sym}
    (hr0 : TermOK r0) (hrt : TermOK rt) (hr1 : TermOK r1) (hr2 : TermOK r2)
    (S : KLoc (Fin 5) (CE ET EW md) → List Sym)
    (h0 : S (.inl 0) = natSyms e ++ r0) (ht : S (.inr (.inl .t)) = natSyms t ++ rt)
    (h1 : S (.inl 1) = natSyms G ++ r1) (h2 : S (.inl 2) = natSyms B ++ r2) :
    Runs (pZ (ET := ET) (EW := EW) (md := md) q) S
      (Function.update S (.inr (.inl .Z2))
        (natSyms (G * q ^ (e - t) * q ^ (e - t) * B) ++ Sym.mark :: S (.inr (.inl .Z2))))
      (fun _ => True) (costZ q e t G B) := by
  have g1 := runs_pushMark (.inr (.inl .l) : KLoc (Fin 5) (CE ET EW md)) S
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S (.inr (.inl .l))
      (Sym.mark :: S (.inr (.inl .l))) := ⟨_, rfl⟩
  rw [← hS1] at g1
  have g2 := runs_subN (x := (.inl 0 : KLoc (Fin 5) (CE ET EW md))) (y := .inr (.inl .t))
    (z := .inr (.inl .l)) (t1 := .inr (.inl .A)) (t2 := .inr (.inl .Bs)) (t3 := .inr (.inl .Acc))
    (by simp) e t r0 rt S1 hr0 hrt hte (by rw [hS1]; simp [h0]) (by rw [hS1]; simp [ht])
  have l2 : S1 (.inr (.inl .l)) = Sym.mark :: S (.inr (.inl .l)) := by rw [hS1]; simp
  rw [l2] at g2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 (.inr (.inl .l))
      (natSyms (e - t) ++ Sym.mark :: S (.inr (.inl .l))) := ⟨_, rfl⟩
  rw [← hS2] at g2
  have g3 := runs_pushMark (.inr (.inl .Z) : KLoc (Fin 5) (CE ET EW md)) S2
  have l3 : S2 (.inr (.inl .Z)) = S (.inr (.inl .Z)) := by rw [hS2, hS1]; simp
  rw [l3] at g3
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 (.inr (.inl .Z))
      (Sym.mark :: S (.inr (.inl .Z))) := ⟨_, rfl⟩
  rw [← hS3] at g3
  have g4 := runs_copyN (src := (.inl 1 : KLoc (Fin 5) (CE ET EW md))) (dst := .inr (.inl .Z))
    (tmp := .inr (.inl .Tm)) (by simp) (by simp) (by simp) G r1 S3 hr1
    (by rw [hS3, hS2, hS1]; simp [h1])
  have l4 : S3 (.inr (.inl .Z)) = Sym.mark :: S (.inr (.inl .Z)) := by rw [hS3]; simp
  rw [l4] at g4
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update S3 (.inr (.inl .Z))
      (natSyms G ++ Sym.mark :: S (.inr (.inl .Z))) := ⟨_, rfl⟩
  rw [← hS4] at g4
  have g5 := runs_powMulN (k := (.inr (.inl .Z) : KLoc (Fin 5) (CE ET EW md)))
    (ns := .inr (.inl .l)) (Kc := .inr (.inl .Kc)) (t := .inr (.inl .Tm)) (Q := .inr (.inl .Q))
    (Tdst := .inr (.inl .Td)) (A := .inr (.inl .A)) (Bs := .inr (.inl .Bs))
    (Acc := .inr (.inl .Acc)) (by simp) q hq G (e - t) (Sym.mark :: S (.inr (.inl .Z)))
    (Sym.mark :: S (.inr (.inl .l))) S4 (NatArith.termOK_mark _) (NatArith.termOK_mark _)
    (by rw [hS4]; simp) (by rw [hS4, hS3, hS2]; simp)
  obtain ⟨S5, hS5⟩ : ∃ S5, S5 = Function.update S4 (.inr (.inl .Z))
      (natSyms (G * q ^ (e - t)) ++ Sym.mark :: S (.inr (.inl .Z))) := ⟨_, rfl⟩
  rw [← hS5] at g5
  have g6 := runs_powMulN (k := (.inr (.inl .Z) : KLoc (Fin 5) (CE ET EW md)))
    (ns := .inr (.inl .l)) (Kc := .inr (.inl .Kc)) (t := .inr (.inl .Tm)) (Q := .inr (.inl .Q))
    (Tdst := .inr (.inl .Td)) (A := .inr (.inl .A)) (Bs := .inr (.inl .Bs))
    (Acc := .inr (.inl .Acc)) (by simp) q hq (G * q ^ (e - t)) (e - t)
    (Sym.mark :: S (.inr (.inl .Z))) (Sym.mark :: S (.inr (.inl .l))) S5
    (NatArith.termOK_mark _) (NatArith.termOK_mark _)
    (by rw [hS5]; simp) (by rw [hS5, hS4, hS3, hS2]; simp)
  obtain ⟨S6, hS6⟩ : ∃ S6, S6 = Function.update S5 (.inr (.inl .Z))
      (natSyms (G * q ^ (e - t) * q ^ (e - t)) ++ Sym.mark :: S (.inr (.inl .Z))) := ⟨_, rfl⟩
  rw [← hS6] at g6
  have g7 := runs_pushMark (.inr (.inl .Z2) : KLoc (Fin 5) (CE ET EW md)) S6
  have l7 : S6 (.inr (.inl .Z2)) = S (.inr (.inl .Z2)) := by
    rw [hS6, hS5, hS4, hS3, hS2, hS1]; simp
  rw [l7] at g7
  obtain ⟨S7, hS7⟩ : ∃ S7, S7 = Function.update S6 (.inr (.inl .Z2))
      (Sym.mark :: S (.inr (.inl .Z2))) := ⟨_, rfl⟩
  rw [← hS7] at g7
  have g8 := runs_mulN (x := (.inr (.inl .Z) : KLoc (Fin 5) (CE ET EW md))) (y := .inl 2)
    (z := .inr (.inl .Z2)) (A := .inr (.inl .A)) (Bs := .inr (.inl .Bs)) (Acc := .inr (.inl .Acc))
    (T := .inr (.inl .Tm)) (by simp) (G * q ^ (e - t) * q ^ (e - t)) B
    (Sym.mark :: S (.inr (.inl .Z))) r2 S7 (NatArith.termOK_mark _) hr2
    (by rw [hS7, hS6]; simp) (by rw [hS7, hS6, hS5, hS4, hS3, hS2, hS1]; simp [h2])
  have l8 : S7 (.inr (.inl .Z2)) = Sym.mark :: S (.inr (.inl .Z2)) := by rw [hS7]; simp
  rw [l8] at g8
  obtain ⟨S8, hS8⟩ : ∃ S8, S8 = Function.update S7 (.inr (.inl .Z2))
      (natSyms (G * q ^ (e - t) * q ^ (e - t) * B) ++ Sym.mark :: S (.inr (.inl .Z2))) :=
    ⟨_, rfl⟩
  rw [← hS8] at g8
  have g9 := runs_dropF (.inr (.inl .Z) : KLoc (Fin 5) (CE ET EW md))
    (G * q ^ (e - t) * q ^ (e - t)) Sym.mark (S (.inr (.inl .Z))) S8 rfl
    (by rw [hS8, hS7, hS6]; simp)
  have g10 := runs_dropF (.inr (.inl .l) : KLoc (Fin 5) (CE ET EW md)) (e - t) Sym.mark
    (S (.inr (.inl .l))) (Function.update S8 (.inr (.inl .Z)) (S (.inr (.inl .Z)))) rfl
    (by rw [hS8, hS7, hS6, hS5, hS4, hS3, hS2]; simp)
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq g1 (WP.W9comp.runs_seq g2
    (WP.W9comp.runs_seq g3 (WP.W9comp.runs_seq g4 (WP.W9comp.runs_seq g5
    (WP.W9comp.runs_seq g6 (WP.W9comp.runs_seq g7 (WP.W9comp.runs_seq g8
    (WP.W9comp.runs_seq g9 g10))))))))) ?_
  rw [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  funext k
  rcases k with i | x | x | x | x
  · fin_cases i <;> simp
  · cases x <;> simp
  · simp
  · simp
  · simp

theorem runs_pK (Rv Zv Rpv : ℕ) (hRR : Rv ≤ Rpv) {rR rZ rRp : List Sym} (hrR : TermOK rR)
    (hrZ : TermOK rZ) (hrRp : TermOK rRp) (S : KLoc (Fin 5) (CE ET EW md) → List Sym)
    (hR : S (.inr (.inl .R)) = natSyms Rv ++ rR) (hZ : S (.inr (.inl .Z2)) = natSyms Zv ++ rZ)
    (hRp : S (.inr (.inl .Rp)) = natSyms Rpv ++ rRp) :
    Runs (pK (ET := ET) (EW := EW) (md := md)) S
      (Function.update (Function.update S (.inl 3) (natSyms (Rv * Zv) ++ S (.inl 3)))
        (.inl 4) (natSyms ((Rpv - Rv) * Zv) ++ S (.inl 4)))
      (fun _ => True) (costK Rv Zv Rpv) := by
  have k1 := runs_mulN (x := (.inr (.inl .R) : KLoc (Fin 5) (CE ET EW md))) (y := .inr (.inl .Z2))
    (z := .inl 3) (A := .inr (.inl .A)) (Bs := .inr (.inl .Bs)) (Acc := .inr (.inl .Acc))
    (T := .inr (.inl .Tm)) (by simp) Rv Zv rR rZ S hrR hrZ hR hZ
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S (.inl 3) (natSyms (Rv * Zv) ++ S (.inl 3)) :=
    ⟨_, rfl⟩
  rw [← hS1] at k1
  have k2 := runs_pushMark (.inr (.inl .Dd) : KLoc (Fin 5) (CE ET EW md)) S1
  have l2 : S1 (.inr (.inl .Dd)) = S (.inr (.inl .Dd)) := by rw [hS1]; simp
  rw [l2] at k2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 (.inr (.inl .Dd))
      (Sym.mark :: S (.inr (.inl .Dd))) := ⟨_, rfl⟩
  rw [← hS2] at k2
  have k3 := runs_subN (x := (.inr (.inl .Rp) : KLoc (Fin 5) (CE ET EW md)))
    (y := .inr (.inl .R)) (z := .inr (.inl .Dd)) (t1 := .inr (.inl .A)) (t2 := .inr (.inl .Bs))
    (t3 := .inr (.inl .Acc)) (by simp) Rpv Rv rRp rR S2 hrRp hrR hRR
    (by rw [hS2, hS1]; simp [hRp]) (by rw [hS2, hS1]; simp [hR])
  have l3 : S2 (.inr (.inl .Dd)) = Sym.mark :: S (.inr (.inl .Dd)) := by rw [hS2]; simp
  rw [l3] at k3
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 (.inr (.inl .Dd))
      (natSyms (Rpv - Rv) ++ Sym.mark :: S (.inr (.inl .Dd))) := ⟨_, rfl⟩
  rw [← hS3] at k3
  have k4 := runs_mulN (x := (.inr (.inl .Dd) : KLoc (Fin 5) (CE ET EW md)))
    (y := .inr (.inl .Z2)) (z := .inl 4) (A := .inr (.inl .A)) (Bs := .inr (.inl .Bs))
    (Acc := .inr (.inl .Acc)) (T := .inr (.inl .Tm)) (by simp) (Rpv - Rv) Zv
    (Sym.mark :: S (.inr (.inl .Dd))) rZ S3 (NatArith.termOK_mark _) hrZ
    (by rw [hS3]; simp) (by rw [hS3, hS2, hS1]; simp [hZ])
  have l4 : S3 (.inl 4) = S (.inl 4) := by rw [hS3, hS2, hS1]; simp
  rw [l4] at k4
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update S3 (.inl 4)
      (natSyms ((Rpv - Rv) * Zv) ++ S (.inl 4)) := ⟨_, rfl⟩
  rw [← hS4] at k4
  have k5 := runs_dropF (.inr (.inl .Dd) : KLoc (Fin 5) (CE ET EW md)) (Rpv - Rv) Sym.mark
    (S (.inr (.inl .Dd))) S4 rfl (by rw [hS4, hS3]; simp)
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq k1 (WP.W9comp.runs_seq k2
    (WP.W9comp.runs_seq k3 (WP.W9comp.runs_seq k4 k5)))) ?_
  rw [hS4, hS3, hS2, hS1]
  funext k
  rcases k with i | x | x | x | x
  · fin_cases i <;> simp
  · cases x <;> simp
  · simp
  · simp
  · simp

theorem runs_pDrop (Zv Rpv Rv Wv tv : ℕ) {X1 X2 X3 X4 X5 : List Sym}
    (S : KLoc (Fin 5) (CE ET EW md) → List Sym)
    (hZ : S (.inr (.inl .Z2)) = natSyms Zv ++ Sym.mark :: X1)
    (hRp : S (.inr (.inl .Rp)) = natSyms Rpv ++ Sym.mark :: X2)
    (hR : S (.inr (.inl .R)) = natSyms Rv ++ Sym.mark :: X3)
    (hW : S (.inr (.inl .W)) = natSyms Wv ++ Sym.mark :: X4)
    (ht : S (.inr (.inl .t)) = natSyms tv ++ Sym.mark :: X5) :
    Runs (pDrop (ET := ET) (EW := EW) (md := md)) S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (.inr (.inl .Z2)) X1) (.inr (.inl .Rp)) X2) (.inr (.inl .R)) X3) (.inr (.inl .W)) X4)
        (.inr (.inl .t)) X5)
      (fun _ => True) (costDrop Zv Rpv Rv Wv tv) := by
  have d1 := runs_dropF (.inr (.inl .Z2) : KLoc (Fin 5) (CE ET EW md)) Zv Sym.mark X1 S rfl hZ
  have d2 := runs_dropF (.inr (.inl .Rp) : KLoc (Fin 5) (CE ET EW md)) Rpv Sym.mark X2
    (Function.update S (.inr (.inl .Z2)) X1) rfl (by simp [hRp])
  have d3 := runs_dropF (.inr (.inl .R) : KLoc (Fin 5) (CE ET EW md)) Rv Sym.mark X3
    (Function.update (Function.update S (.inr (.inl .Z2)) X1) (.inr (.inl .Rp)) X2) rfl
    (by simp [hR])
  have d4 := runs_dropF (.inr (.inl .W) : KLoc (Fin 5) (CE ET EW md)) Wv Sym.mark X4
    (Function.update (Function.update (Function.update S (.inr (.inl .Z2)) X1)
      (.inr (.inl .Rp)) X2) (.inr (.inl .R)) X3) rfl (by simp [hW])
  have d5 := runs_dropF (.inr (.inl .t) : KLoc (Fin 5) (CE ET EW md)) tv Sym.mark X5
    (Function.update (Function.update (Function.update (Function.update S (.inr (.inl .Z2)) X1)
      (.inr (.inl .Rp)) X2) (.inr (.inl .R)) X3) (.inr (.inl .W)) X4) rfl (by simp [ht])
  exact WP.W9comp.runs_seq d1 (WP.W9comp.runs_seq d2 (WP.W9comp.runs_seq d3
    (WP.W9comp.runs_seq d4 d5)))

end RunsArith

/-! ## Runs of the phases with kernel calls -/

section RunsCalls

variable {ET EW : Type} {md : ℕ} [DecidableEq ET] [DecidableEq EW] {RT RW RD : Type}

theorem runs_pTW {q CT CW : ℕ} {PT : Prog (KLoc (Fin 2) ET) (fun _ => Sym) RT}
    {PW : Prog (KLoc (Fin 2) EW) (fun _ => Sym) RW}
    (hsT : ∀ (e : ℕ) (r0 : List Sym) (S : KLoc (Fin 2) ET → List Sym), TermOK r0 →
      S (.inl 0) = natSyms e ++ r0 →
      Runs PT S (Function.update S (.inl 1) (natSyms (c6T q e) ++ S (.inl 1))) (fun _ => True)
        (CT * (e + 1) ^ 3))
    (hsW : ∀ (e : ℕ) (r0 : List Sym) (S : KLoc (Fin 2) EW → List Sym), TermOK r0 →
      S (.inl 0) = natSyms e ++ r0 →
      Runs PW S (Function.update S (.inl 1) (natSyms (tripleWb 100 ^ c6K e) ++ S (.inl 1)))
        (fun _ => True) (CW * (e + 1) ^ 3))
    (e : ℕ) {r0 : List Sym} (hr0 : TermOK r0) (S : KLoc (Fin 5) (CE ET EW md) → List Sym)
    (hS0 : S (.inl 0) = natSyms e ++ r0) :
    Runs (pTW (RD := RD) PT PW) S
      (Function.update (Function.update S (.inr (.inl .t))
        (natSyms (c6T q e) ++ Sym.mark :: S (.inr (.inl .t)))) (.inr (.inl .W))
        (natSyms (tripleWb 100 ^ c6K e) ++ Sym.mark :: S (.inr (.inl .W))))
      (fun _ => True) (1 + (CT * (e + 1) ^ 3 + (1 + CW * (e + 1) ^ 3))) := by
  have h1 := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pushMark (.inr (.inl .t) : KLoc (Fin 5) (CE ET EW md)) S)
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S (.inr (.inl .t))
      (Sym.mark :: S (.inr (.inl .t))) := ⟨_, rfl⟩
  rw [← hS1] at h1
  have c1 := hsT e r0 (S1 ∘ ιT) hr0 (by show S1 (.inl 0) = _; rw [hS1]; simp [hS0])
  have h2 := ctrCall_upd1 ιT_injective (lT (RT := RT) (RW := RW) (RD := RD)) (.inl 1) _ c1
  have a1 : S1 (.inr (.inl .t)) = Sym.mark :: S (.inr (.inl .t)) := by rw [hS1]; simp
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 (.inr (.inl .t))
      (natSyms (c6T q e) ++ Sym.mark :: S (.inr (.inl .t))) := ⟨_, rfl⟩
  have h2' : Runs (callInj ιT (lT (RT := RT) (RW := RW) (RD := RD)) PT) S1 S2 (fun _ => True)
      (CT * (e + 1) ^ 3) := by
    refine WP.W9comp.runs_congr h2 ?_
    show Function.update S1 (.inr (.inl .t)) (natSyms (c6T q e) ++ S1 (.inr (.inl .t))) = S2
    rw [a1, hS2]
  have h3 := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pushMark (.inr (.inl .W) : KLoc (Fin 5) (CE ET EW md)) S2)
  have a2 : S2 (.inr (.inl .W)) = S (.inr (.inl .W)) := by rw [hS2, hS1]; simp
  rw [a2] at h3
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 (.inr (.inl .W))
      (Sym.mark :: S (.inr (.inl .W))) := ⟨_, rfl⟩
  rw [← hS3] at h3
  have c2 := hsW e r0 (S3 ∘ ιW) hr0 (by show S3 (.inl 0) = _; rw [hS3, hS2, hS1]; simp [hS0])
  have h4 := ctrCall_upd1 ιW_injective (lWk (RT := RT) (RW := RW) (RD := RD)) (.inl 1) _ c2
  have a3 : S3 (.inr (.inl .W)) = Sym.mark :: S (.inr (.inl .W)) := by rw [hS3]; simp
  have h4' : Runs (callInj ιW (lWk (RT := RT) (RW := RW) (RD := RD)) PW) S3
      (Function.update S3 (.inr (.inl .W))
        (natSyms (tripleWb 100 ^ c6K e) ++ Sym.mark :: S (.inr (.inl .W)))) (fun _ => True)
      (CW * (e + 1) ^ 3) := by
    refine WP.W9comp.runs_congr h4 ?_
    show Function.update S3 (.inr (.inl .W))
      (natSyms (tripleWb 100 ^ c6K e) ++ S3 (.inr (.inl .W))) = _
    rw [a3]
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2'
    (WP.W9comp.runs_seq h3 h4'))) ?_
  rw [hS3, hS2, hS1]
  simp only [Function.update_idem]

theorem runs_pRp {CD : ℕ} {PD : Prog (Loc 4 md) (fun _ => Sym) RD}
    (hsD : ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 md → List Sym), 0 < b → TermOK ra →
      TermOK rb → S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
      Runs PD S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
          (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
        (CD * (bitLen a * bitLen b + bitLen a + bitLen b + 1)))
    (Rv Wv : ℕ) (hW0 : 0 < Wv) {rR rW : List Sym} (hrR : TermOK rR) (hrW : TermOK rW)
    (S : KLoc (Fin 5) (CE ET EW md) → List Sym)
    (hR : S (.inr (.inl .R)) = natSyms Rv ++ rR) (hW : S (.inr (.inl .W)) = natSyms Wv ++ rW) :
    Runs (pRp (ET := ET) (EW := EW) (RT := RT) (RW := RW) PD) S
      (Function.update S (.inr (.inl .Rp))
        (natSyms (Wv * ((Rv + Wv - 1) / Wv)) ++ Sym.mark :: S (.inr (.inl .Rp))))
      (fun _ => True) (costRp CD Rv Wv) := by
  have hA := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pA (ET := ET) (EW := EW) (md := md) Rv Wv (by omega) hrR hrW S hR hW)
  obtain ⟨SA, hSA⟩ : ∃ SA, SA = Function.update (Function.update (Function.update
      (Function.update (Function.update S
        (.inr (.inl .one)) (natSyms 1 ++ Sym.mark :: S (.inr (.inl .one))))
        (.inr (.inl .a)) (natSyms (Rv + Wv) ++ Sym.mark :: S (.inr (.inl .a))))
        (.inr (.inl .b)) (natSyms (Rv + Wv - 1) ++ Sym.mark :: S (.inr (.inl .b))))
        (.inr (.inl .Qt)) (Sym.mark :: S (.inr (.inl .Qt))))
        (.inr (.inl .Rm)) (Sym.mark :: S (.inr (.inl .Rm))) := ⟨_, rfl⟩
  rw [← hSA] at hA
  have cD := hsD (Rv + Wv - 1) Wv (Sym.mark :: S (.inr (.inl .b))) rW (SA ∘ ιD) hW0
    (NatArith.termOK_mark _) hrW
    (by show SA (.inr (.inl .b)) = _; rw [hSA]; simp)
    (by show SA (.inr (.inl .W)) = _; rw [hSA]; simp [hW])
  have hD := ctrCall_upd2 ιD_injective (lD (RT := RT) (RW := RW) (RD := RD)) (.inl 2) (.inl 3)
    _ _ cD
  have aQ : SA (.inr (.inl .Qt)) = Sym.mark :: S (.inr (.inl .Qt)) := by rw [hSA]; simp
  have aR : SA (.inr (.inl .Rm)) = Sym.mark :: S (.inr (.inl .Rm)) := by rw [hSA]; simp
  obtain ⟨SB, hSB⟩ : ∃ SB, SB = Function.update (Function.update SA (.inr (.inl .Qt))
      (natSyms ((Rv + Wv - 1) / Wv) ++ Sym.mark :: S (.inr (.inl .Qt)))) (.inr (.inl .Rm))
      (natSyms ((Rv + Wv - 1) % Wv) ++ Sym.mark :: S (.inr (.inl .Rm))) := ⟨_, rfl⟩
  have hD' : Runs (callInj ιD (lD (RT := RT) (RW := RW) (RD := RD)) PD) SA SB (fun _ => True)
      (CD * (bitLen (Rv + Wv - 1) * bitLen Wv + bitLen (Rv + Wv - 1) + bitLen Wv + 1)) := by
    refine WP.W9comp.runs_congr hD ?_
    show Function.update (Function.update SA (.inr (.inl .Qt))
      (natSyms ((Rv + Wv - 1) / Wv) ++ SA (.inr (.inl .Qt)))) (.inr (.inl .Rm))
      (natSyms ((Rv + Wv - 1) % Wv) ++ SA (.inr (.inl .Rm))) = SB
    rw [aQ, aR, hSB]
  have hC := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pC (ET := ET) (EW := EW) (md := md) Wv ((Rv + Wv - 1) / Wv) ((Rv + Wv - 1) % Wv)
      (Rv + Wv - 1) (Rv + Wv) (X1 := S (.inr (.inl .Qt))) (X2 := S (.inr (.inl .Rm)))
      (X3 := S (.inr (.inl .b))) (X4 := S (.inr (.inl .a))) (X5 := S (.inr (.inl .one))) hrW SB
      (by rw [hSB, hSA]; simp [hW]) (by rw [hSB]; simp) (by rw [hSB]; simp)
      (by rw [hSB, hSA]; simp) (by rw [hSB, hSA]; simp) (by rw [hSB, hSA]; simp))
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq hA (WP.W9comp.runs_seq hD' hC)) ?_
  rw [hSB, hSA]
  funext k
  rcases k with i | x | x | x | x
  · fin_cases i <;> simp
  · cases x <;> simp
  · simp
  · simp
  · simp

end RunsCalls

/-! ## The counter kernel -/

/-- **The counter kernel** (`C6RowCtrSpec q`, for `2 ≤ q`) from the `t` and `W_b^k` kernels
(`C6TArith.lean`), the long division `W6a_divModNat` and the cost bound `CtrCostStmt`. -/
theorem c6RowCtr_of {q : ℕ} (hq : 2 ≤ q) (hT : C6TPushSpec q) (hW : C6WPushSpec)
    (hCost : ∀ CT CW CD : ℕ, CtrCostStmt q CT CW CD) : C6RowCtrSpec q := by
  obtain ⟨CT, hCT⟩ := hT
  obtain ⟨ET, iETf, iETd, RT, PT, hRTf, hRTn, hclT, hsT⟩ := hCT ()
  obtain ⟨CW, hCW⟩ := hW
  obtain ⟨EW, iEWf, iEWd, RW, PW, hRWf, hRWn, hclW, hsW⟩ := hCW ()
  obtain ⟨CD, hCD⟩ := WP.W6a.W6a_divModNat_holds WP.W3.W3_subNat_holds
  obtain ⟨md, RD, obsD, PD, hmd, hRDf, hRDn, hclD, hsD⟩ := hCD ()
  obtain ⟨C, hC⟩ := hCost CT CW CD
  refine ⟨C, fun _ => ⟨CE ET EW md, instFintypeCE, instDecEqCE, CR RT RW RD,
    ctrProg q PT PW PD, (by have := hRTf; have := hRWf; have := hRDf; infer_instance),
    (by have := hRTn; have := hRWn; have := hRDn; infer_instance),
    closed_ctrProg q hclT hclW hclD, ?_⟩⟩
  intro e G B r0 r1 r2 S he hG hB hr0 hr1 hr2 hS0 hS1 hS2
  have hte := C6Aux.c6T_lt hq he
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq1 : 1 ≤ q := by omega
  have hW0 : 0 < tripleWb 100 ^ c6K e := C6Aux.c6Wk_pos e
  have hRRp := C6Aux.c6R_le_c6Rp q e
  -- 1. `t` and `W`
  have P1 := runs_pTW (md := md) (RD := RD) hsT hsW e hr0 S hS0
  obtain ⟨t, htd⟩ : ∃ t, t = c6T q e := ⟨_, rfl⟩
  obtain ⟨Wv, hWv⟩ : ∃ Wv, Wv = tripleWb 100 ^ c6K e := ⟨_, rfl⟩
  rw [← htd, ← hWv] at P1
  rw [← htd] at hte
  rw [← hWv] at hW0
  obtain ⟨S1, hS1d⟩ : ∃ S1, S1 = Function.update (Function.update S (.inr (.inl .t))
      (natSyms t ++ Sym.mark :: S (.inr (.inl .t)))) (.inr (.inl .W))
      (natSyms Wv ++ Sym.mark :: S (.inr (.inl .W))) := ⟨_, rfl⟩
  rw [← hS1d] at P1
  -- 2. `R`
  have P2 := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pR (ET := ET) (EW := EW) (md := md) (rt := Sym.mark :: S (.inr (.inl .t))) hq2 t
      (NatArith.termOK_mark _) S1 (by rw [hS1d]; simp))
  have l2 : S1 (.inr (.inl .R)) = S (.inr (.inl .R)) := by rw [hS1d]; simp
  rw [l2] at P2
  obtain ⟨Rv, hRv⟩ : ∃ Rv, Rv = q ^ (2 * t) := ⟨_, rfl⟩
  rw [← hRv] at P2
  obtain ⟨S2, hS2d⟩ : ∃ S2, S2 = Function.update S1 (.inr (.inl .R))
      (natSyms Rv ++ Sym.mark :: S (.inr (.inl .R))) := ⟨_, rfl⟩
  rw [← hS2d] at P2
  -- 3. `R'`
  have P3 := runs_pRp (RT := RT) (RW := RW) hsD Rv Wv hW0
    (rR := Sym.mark :: S (.inr (.inl .R))) (rW := Sym.mark :: S (.inr (.inl .W)))
    (NatArith.termOK_mark _) (NatArith.termOK_mark _) S2
    (by rw [hS2d]; simp) (by rw [hS2d, hS1d]; simp)
  have l3 : S2 (.inr (.inl .Rp)) = S (.inr (.inl .Rp)) := by rw [hS2d, hS1d]; simp
  rw [l3] at P3
  obtain ⟨Rpv, hRpv⟩ : ∃ Rpv, Rpv = Wv * ((Rv + Wv - 1) / Wv) := ⟨_, rfl⟩
  rw [← hRpv] at P3
  obtain ⟨S3, hS3d⟩ : ∃ S3, S3 = Function.update S2 (.inr (.inl .Rp))
      (natSyms Rpv ++ Sym.mark :: S (.inr (.inl .Rp))) := ⟨_, rfl⟩
  rw [← hS3d] at P3
  -- 4. `Z`
  have P4 := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pZ (ET := ET) (EW := EW) (md := md) (rt := Sym.mark :: S (.inr (.inl .t))) hq1 e t G B
      hte.2.le hr0 (NatArith.termOK_mark _) hr1 hr2 S3
      (by rw [hS3d, hS2d, hS1d]; simp [hS0]) (by rw [hS3d, hS2d, hS1d]; simp)
      (by rw [hS3d, hS2d, hS1d]; simp [hS1]) (by rw [hS3d, hS2d, hS1d]; simp [hS2]))
  have l4 : S3 (.inr (.inl .Z2)) = S (.inr (.inl .Z2)) := by rw [hS3d, hS2d, hS1d]; simp
  rw [l4] at P4
  obtain ⟨Zv, hZv⟩ : ∃ Zv, Zv = G * q ^ (e - t) * q ^ (e - t) * B := ⟨_, rfl⟩
  rw [← hZv] at P4
  obtain ⟨S4, hS4d⟩ : ∃ S4, S4 = Function.update S3 (.inr (.inl .Z2))
      (natSyms Zv ++ Sym.mark :: S (.inr (.inl .Z2))) := ⟨_, rfl⟩
  rw [← hS4d] at P4
  -- 5. `K1`, `K2`
  have hRRp' : Rv ≤ Rpv := by subst hRpv hRv hWv htd; exact hRRp
  have P5 := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pK (ET := ET) (EW := EW) (md := md) Rv Zv Rpv hRRp'
      (rR := Sym.mark :: S (.inr (.inl .R))) (rZ := Sym.mark :: S (.inr (.inl .Z2)))
      (rRp := Sym.mark :: S (.inr (.inl .Rp))) (NatArith.termOK_mark _) (NatArith.termOK_mark _)
      (NatArith.termOK_mark _) S4
      (by rw [hS4d, hS3d, hS2d]; simp) (by rw [hS4d]; simp) (by rw [hS4d, hS3d]; simp))
  have l53 : S4 (.inl 3) = S (.inl 3) := by rw [hS4d, hS3d, hS2d, hS1d]; simp
  have l54 : S4 (.inl 4) = S (.inl 4) := by rw [hS4d, hS3d, hS2d, hS1d]; simp
  rw [l53, l54] at P5
  obtain ⟨S5, hS5d⟩ : ∃ S5, S5 = Function.update (Function.update S4 (.inl 3)
      (natSyms (Rv * Zv) ++ S (.inl 3))) (.inl 4) (natSyms ((Rpv - Rv) * Zv) ++ S (.inl 4)) :=
    ⟨_, rfl⟩
  rw [← hS5d] at P5
  -- 6. drops
  have P6 := WP.W0m.runs_liftRegs (lN (RT := RT) (RW := RW) (RD := RD))
    (runs_pDrop (ET := ET) (EW := EW) (md := md) Zv Rpv Rv Wv t (X1 := S (.inr (.inl .Z2)))
      (X2 := S (.inr (.inl .Rp))) (X3 := S (.inr (.inl .R))) (X4 := S (.inr (.inl .W)))
      (X5 := S (.inr (.inl .t))) S5
      (by rw [hS5d, hS4d]; simp) (by rw [hS5d, hS4d, hS3d]; simp)
      (by rw [hS5d, hS4d, hS3d, hS2d]; simp) (by rw [hS5d, hS4d, hS3d, hS2d, hS1d]; simp)
      (by rw [hS5d, hS4d, hS3d, hS2d, hS1d]; simp))
  have hall := WP.W9comp.runs_seq P1 (WP.W9comp.runs_seq P2 (WP.W9comp.runs_seq P3
    (WP.W9comp.runs_seq P4 (WP.W9comp.runs_seq P5 P6))))
  have eR : c6R q e = Rv := by subst hRv htd; rfl
  have eRp : c6Rp q e = Rpv := by subst hRpv hRv hWv htd; rfl
  have eZ : c6Zq q e G B = Zv := by subst hZv htd; unfold c6Zq; ring
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · rw [eR, eRp, eZ, hS5d, hS4d, hS3d, hS2d, hS1d]
    funext k
    rcases k with i | x | x | x | x
    · fin_cases i <;> simp
    · cases x <;> simp
    · simp
    · simp
    · simp
  · have h := hC e G B he hG hB
    subst hRpv hZv hRv
    subst htd hWv
    exact h

end AppC.C6RowAux

end SubNLogN.Machine
