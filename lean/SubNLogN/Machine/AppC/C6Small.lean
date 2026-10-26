/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6SmallAddr
import SubNLogN.Machine.AppC.C5StreamArith
import SubNLogN.Machine.AppC.C7Top

/-!
# Lemma A.8 in radix `q`, small widths (`Machine/AppC/C6Small.lean`)

Lemma A.8 (`lem:transfer12`, Appendix A.3;
small-width branch `e ≤ 34`): for `1 ≤ e ≤ 34`, the interchange of the two `e`-digit
chunks of `[A] × [q^e] × [G] × [q^e] × [B]` is done by `e` digit-pair swaps. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved here (0 `sorry`, no pending hypotheses):** `c6Small_holds q (hq : 2 ≤ q) : C6SmallStmt q`
(statement in `Machine/AppC/C6QLeaves.lean`).

**Program** (named stacks `Fin 5` = array, `e, G, B, w`; private stacks `E1 ⊕ Fin 13`, `E1` the
private stacks of the `K1` kernel; registers `NatArith.Reg × R1`):
1. Prelude: `N1 = G·q^{e-1}` (copy of `G`, then `NatArith.powMulN` with `e - 1` on a scratch
   counter) and `N2 = B`, both above guard marks.
2. Loop (`K1.Rot.nLoop`, `e` iterations, iteration `j`): guards on `D`, `T`; the proved `K1` kernel
   `k1PairPermMix_holds q swap` through `callInj` (source = array, destination = `D`, counters
   `N1`, `N2`), which swaps the digit pair of weight `q^j` (`Machine/AppC/C6SmallAddr.lean`);
   two guard rewinds `D → T → array` (in place); `N2 ← N2·q` (`NatArith.mulConstN`).
3. Postlude: drop both counters with their guards.

The `e ≤ 34` hypothesis is not needed by the program (it only bounds the cost by `34` iterations).

**Cost.** `≤ (34·C₁ + 200000 + 100000·(|q| + 2)^2) · (V + 1)`, `C₁` the constant of the `K1`
kernel: each of the `e ≤ 34` iterations costs `C₁(V+1) + 6V + O((lg M + |q|)^2)`, the counter
arithmetic is `O((lg M + |q|)^2)` and `(lg M)^2 ≤ 4M ≤ 4V` (`sq_bitLen_le`).

**Reused results.** `K1Digit.k1PairPermMix_holds` (`Machine/K1/DigitPairPermMix.lean`);
`NatArith.runs_powMulN`, `NatArith.runs_mulConstN` (`Machine/AppC/C5StreamArith.lean`);
`K1.Rot.runs_nLoop` (`Machine/K1/RotateBase.lean`); the guard and copy routines of
`Machine/AppC/C7TopArith.lean` and `Machine/AppC/C7Top.lean`. Address identity:
`Machine/AppC/C6SmallAddr.lean`.
-/

namespace SubNLogN.Machine.AppC.C6SmallAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine Computability

/-- Stacks: named `Fin 5`, private `E1 ⊕ Fin 13`. -/
abbrev SL (E1 : Type) := KLoc (Fin 5) (E1 ⊕ Fin 13)

section Layout

variable {E1 : Type}

def qv (i : Fin 13) : SL E1 := .inr (.inr i)

def aArr : SL E1 := .inl 0
def aE : SL E1 := .inl 1
def aG : SL E1 := .inl 2
def aB : SL E1 := .inl 3
def aD : SL E1 := qv 0
def aT : SL E1 := qv 1
def aN1 : SL E1 := qv 2
def aN2 : SL E1 := qv 3
def aKc : SL E1 := qv 4
def aTm : SL E1 := qv 5
def aQ : SL E1 := qv 6
def aTd : SL E1 := qv 7
def aA : SL E1 := qv 8
def aBs : SL E1 := qv 9
def aAcc : SL E1 := qv 10
def aT2 : SL E1 := qv 11
def aEc : SL E1 := qv 12

/-- `K1` named stacks: source = array, destination = `D`, counters `N1`, `N2`. -/
def kIdx6 (i : Fin 4) : SL E1 :=
  if i.val = 0 then aArr else if i.val = 1 then aD else if i.val = 2 then aN1 else aN2

def ιS : KLoc (Fin 4) E1 → SL E1
  | .inl i => kIdx6 i
  | .inr e => .inr (.inl e)

theorem ιS_inj [DecidableEq E1] : Function.Injective (ιS (E1 := E1)) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (of_decide_eq_false rfl)
  · fin_cases i <;> exact absurd h (of_decide_eq_false rfl)
  · fin_cases j <;> exact absurd h (of_decide_eq_false rfl)
  · simp only [ιS, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

end Layout

/-! ## Registers and lenses -/

/-- Lens to the `NatArith` registers. -/
def lN {R1 : Type} : Lens (NatArith.Reg × R1) NatArith.Reg := Lens.fst _ _

/-- Lens to the `K1` registers. -/
def lK {R1 : Type} : Lens (NatArith.Reg × R1) R1 := Lens.snd _ _

/-- Lens to the work register of the `Lib` routines. -/
def lO {R1 : Type} : Lens (NatArith.Reg × R1) (Option Sym) := (Lens.fst _ _).comp NatArith.lW

/-- A lifted component keeps its stack effect and cost. -/
theorem runs_liftG {K σ τ : Type} [DecidableEq K] (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  exact ⟨⟨l.set v s'.var, s'.stk⟩, t, Eval.liftRegs l e v rfl, ⟨hs', trivial⟩, ht⟩

/-! ## The program -/

section Prog

variable {E1 R1 : Type}

/-- Prelude: `N1 = G·q^{e-1}` and `N2 = B` above guards. -/
def prelude6 (q : ℕ) : Prog (SL E1) (fun _ => Sym) (NatArith.Reg × R1) :=
  .seq ((pushC aN1 .mark).liftRegs lO) (.seq ((copyBlock aG aN1 aTm).liftRegs lO)
  (.seq ((pushC aEc .mark).liftRegs lO) (.seq ((copyBlock aE aEc aTm).liftRegs lO)
  (.seq ((dec aEc aTm).liftRegs lO)
  (.seq ((NatArith.powMulN aN1 q aEc aKc aTm aQ aTd aA aBs aAcc).liftRegs lN)
  (.seq ((C7TopAux.dropTo aEc .mark).liftRegs lO)
  (.seq ((pushC aN2 .mark).liftRegs lO) ((copyBlock aB aN2 aTm).liftRegs lO))))))))

/-- One loop iteration: guards, the `K1` swap into `D`, rewinds back, `N2 ← N2·q`. -/
def step6 (q : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (SL E1) (fun _ => Sym) (NatArith.Reg × R1) :=
  .seq ((pushC aD .mark).liftRegs lO) (.seq ((pushC aT .mark).liftRegs lO)
  (.seq (callInj ιS lK P1)
  (.seq ((WP.W9comp.rewindTo aD aT .mark).liftRegs lO)
  (.seq ((WP.W9comp.rewindTo aT aArr .mark).liftRegs lO)
  ((NatArith.mulConstN aN2 q aQ aTd aA aBs aAcc aT2).liftRegs lN)))))

/-- Postlude: drop the counters with their guards. -/
def post6 : SProg (SL E1) := .seq (C7TopAux.dropTo aN1 .mark) (C7TopAux.dropTo aN2 .mark)

/-- **The Lemma A.8 small-width kernel.** -/
def smallProg (q : ℕ) (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) :
    Prog (SL E1) (fun _ => Sym) (NatArith.Reg × R1) :=
  .seq (prelude6 q) (.seq (K1.Rot.nLoop lO aE aKc aTm (step6 q P1)) (post6.liftRegs lO))

theorem smallProg_closed [DecidableEq E1] (q : ℕ) {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1}
    (hP1 : P1.Closed) : (smallProg q P1).Closed := by
  refine ⟨⟨WP.W9comp.closed_liftRegs _ trivial,
    WP.W9comp.closed_liftRegs _ (C7TopAux.copyBlock_closed _ _ _),
    WP.W9comp.closed_liftRegs _ trivial,
    WP.W9comp.closed_liftRegs _ (C7TopAux.copyBlock_closed _ _ _),
    WP.W9comp.closed_liftRegs _ (C7TopAux.dec_closed _ _),
    WP.W9comp.closed_liftRegs _ (NatArith.closed_powMulN _ _ _ _ _ _ _ _ _ _),
    WP.W9comp.closed_liftRegs _ (C7TopAux.dropTo_closed _ _),
    WP.W9comp.closed_liftRegs _ trivial,
    WP.W9comp.closed_liftRegs _ (C7TopAux.copyBlock_closed _ _ _)⟩,
    K1.Rot.closed_nLoop _ _ _ _ ⟨WP.W9comp.closed_liftRegs _ trivial,
      WP.W9comp.closed_liftRegs _ trivial, closed_callInj _ _ hP1,
      WP.W9comp.closed_liftRegs _ ⟨trivial, trivial, trivial⟩,
      WP.W9comp.closed_liftRegs _ ⟨trivial, trivial, trivial⟩,
      WP.W9comp.closed_liftRegs _ (NatArith.closed_mulConstN _ _ _ _ _ _ _ _)⟩,
    WP.W9comp.closed_liftRegs _ ⟨C7TopAux.dropTo_closed _ _, C7TopAux.dropTo_closed _ _⟩⟩

end Prog

/-! ## The array sequence -/

/-- The array after `j` digit-pair swaps (low weights first). -/
def uSeq (q e G B : ℕ) [NeZero q] (v : List (List Bool)) : ℕ → List (List Bool)
  | 0 => v
  | j + 1 => permByInv (pairPermMixAddr q (G * q ^ (e - 1)) (B * q ^ j)
      (Equiv.prodComm (Fin q) (Fin q)).symm) (uSeq q e G B v j)

theorem permByInv_id' {α : Type} [Inhabited α] (v : List α) : permByInv (fun y => y) v = v := by
  apply List.ext_getElem (by simp [AppC.C7Aux.permByInv_length])
  intro n h1 h2
  simp [permByInv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The shape of step `j`: `[A·q^{e-1-j}] × [q] × [G·q^{e-1}] × [q] × [B·q^j]`. -/
theorem len_step {q e j A G B : ℕ} (hj : j < e) :
    A * q ^ e * G * q ^ e * B = A * q ^ (e - 1 - j) * q * (G * q ^ (e - 1)) * q * (B * q ^ j) := by
  have h1 : q ^ e = q ^ (e - 1 - j) * q * q ^ j := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have h2 : q ^ (e - 1) = q ^ j * q ^ (e - 1 - j) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, h2]; ring

section USeq

variable {q e G B : ℕ} [NeZero q] {v : List (List Bool)}

theorem uSeq_length (j : ℕ) : (uSeq q e G B v j).length = v.length := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [uSeq, AppC.C7Aux.permByInv_length, ih]

theorem ppm_step_lt {A j y : ℕ} (hG : 0 < G) (hB : 0 < B) (hj : j < e)
    (hy : y < A * q ^ e * G * q ^ e * B) :
    pairPermMixAddr q (G * q ^ (e - 1)) (B * q ^ j) (Equiv.prodComm (Fin q) (Fin q)).symm y <
      A * q ^ e * G * q ^ e * B := by
  have hq : 0 < q := Nat.pos_of_neZero q
  rw [len_step hj] at hy ⊢
  exact ppm_lt _ (by positivity) (by positivity) hy

theorem uSeq_width {A w : ℕ} (hG : 0 < G) (hB : 0 < B)
    (hlen : v.length = A * q ^ e * G * q ^ e * B) (hw : ∀ p ∈ v, p.length = w) :
    ∀ j, j ≤ e → ∀ p ∈ uSeq q e G B v j, p.length = w
  | 0, _ => hw
  | j + 1, hj => fun p hp => by
    refine uSeq_width hG hB hlen hw j (by omega) p (AppC.C7Aux.permByInv_mem ?_ hp)
    intro y hy
    rw [uSeq_length, hlen] at hy ⊢
    exact ppm_step_lt hG hB (by omega) hy

/-- Closed form: the low `j` digit pairs are swapped. -/
theorem uSeq_phi {A : ℕ} (hG : 0 < G) (hB : 0 < B)
    (hlen : v.length = A * q ^ e * G * q ^ e * B) :
    ∀ j, j ≤ e → uSeq q e G B v j = permByInv (phi q (q ^ e) G B j) v
  | 0, _ => by
    show v = _
    rw [AppC.C7Aux.permByInv_congr (fun y _ => phi_zero q (q ^ e) G B y), permByInv_id']
  | j + 1, hj => by
    have hq : 0 < q := Nat.pos_of_neZero q
    have ih := uSeq_phi hG hB hlen j (by omega)
    show permByInv _ (uSeq q e G B v j) = _
    rw [ih, AppC.C7Aux.permByInv_permByInv (fun y hy => by
      rw [hlen] at hy ⊢
      exact ppm_step_lt hG hB (by omega) hy)]
    apply AppC.C7Aux.permByInv_congr
    intro y _
    have h1 : q ^ e = q ^ (e - 1 - j) * q * q ^ j := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    have h2 : q ^ (e - 1) = q ^ j * q ^ (e - 1 - j) := by
      rw [← pow_add]; congr 1; omega
    rw [h2]
    exact phi_succ h1 rfl (by positivity) hG hB (by positivity) y

theorem uSeq_full {A : ℕ} (hG : 0 < G) (hB : 0 < B)
    (hlen : v.length = A * q ^ e * G * q ^ e * B) :
    uSeq q e G B v e = permByInv (swapFieldsInv (q ^ e) G (q ^ e) B) v := by
  rw [uSeq_phi hG hB hlen e le_rfl]
  exact AppC.C7Aux.permByInv_congr (fun y _ => phi_full (Nat.pos_of_neZero q))

end USeq

/-! ## Loop states -/

section Sig

variable {E1 : Type} [DecidableEq E1]

theorem nd6 {a b : SL E1} (h : decide (a = b) = false) : a ≠ b := of_decide_eq_false h

/-- The loop state: `B0` with the array, `D`, `T`, `N2` and the loop counter overridden. -/
def sig (B0 : SL E1 → List Sym) (a d t n k : List Sym) : SL E1 → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B0 aArr a)
    aD d) aT t) aN2 n) aKc k

variable (B0 : SL E1 → List Sym) (a d t n k : List Sym)

theorem sig_Kc : sig B0 a d t n k aKc = k := Function.update_self _ _ _

theorem sig_N2 : sig B0 a d t n k aN2 = n := by
  unfold sig
  rw [Function.update_of_ne (nd6 rfl), Function.update_self]

theorem sig_T : sig B0 a d t n k aT = t := by
  unfold sig
  rw [Function.update_of_ne (show (aT : SL E1) ≠ aKc from nd6 rfl),
    Function.update_of_ne (show (aT : SL E1) ≠ aN2 from nd6 rfl), Function.update_self]

theorem sig_D : sig B0 a d t n k aD = d := by
  unfold sig
  rw [Function.update_of_ne (show (aD : SL E1) ≠ aKc from nd6 rfl),
    Function.update_of_ne (show (aD : SL E1) ≠ aN2 from nd6 rfl),
    Function.update_of_ne (show (aD : SL E1) ≠ aT from nd6 rfl), Function.update_self]

theorem sig_Arr : sig B0 a d t n k aArr = a := by
  unfold sig
  rw [Function.update_of_ne (show (aArr : SL E1) ≠ aKc from nd6 rfl),
    Function.update_of_ne (show (aArr : SL E1) ≠ aN2 from nd6 rfl),
    Function.update_of_ne (show (aArr : SL E1) ≠ aT from nd6 rfl),
    Function.update_of_ne (show (aArr : SL E1) ≠ aD from nd6 rfl), Function.update_self]

theorem sig_other {x : SL E1} (h1 : x ≠ aKc) (h2 : x ≠ aN2) (h3 : x ≠ aT) (h4 : x ≠ aD)
    (h5 : x ≠ aArr) : sig B0 a d t n k x = B0 x := by
  unfold sig
  rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5]

theorem sig_upd_Kc (k' : List Sym) :
    Function.update (sig B0 a d t n k) aKc k' = sig B0 a d t n k' := by
  unfold sig; rw [Function.update_idem]

theorem sig_upd_N2 (n' : List Sym) :
    Function.update (sig B0 a d t n k) aN2 n' = sig B0 a d t n' k := by
  unfold sig
  rw [Function.update_comm (show (aKc : SL E1) ≠ aN2 from nd6 rfl), Function.update_idem]

theorem sig_upd_T (t' : List Sym) :
    Function.update (sig B0 a d t n k) aT t' = sig B0 a d t' n k := by
  unfold sig
  rw [Function.update_comm (show (aKc : SL E1) ≠ aT from nd6 rfl),
    Function.update_comm (show (aN2 : SL E1) ≠ aT from nd6 rfl), Function.update_idem]

theorem sig_upd_D (d' : List Sym) :
    Function.update (sig B0 a d t n k) aD d' = sig B0 a d' t n k := by
  unfold sig
  rw [Function.update_comm (show (aKc : SL E1) ≠ aD from nd6 rfl),
    Function.update_comm (show (aN2 : SL E1) ≠ aD from nd6 rfl),
    Function.update_comm (show (aT : SL E1) ≠ aD from nd6 rfl), Function.update_idem]

theorem sig_upd_Arr (a' : List Sym) :
    Function.update (sig B0 a d t n k) aArr a' = sig B0 a' d t n k := by
  unfold sig
  rw [Function.update_comm (show (aKc : SL E1) ≠ aArr from nd6 rfl),
    Function.update_comm (show (aN2 : SL E1) ≠ aArr from nd6 rfl),
    Function.update_comm (show (aT : SL E1) ≠ aArr from nd6 rfl),
    Function.update_comm (show (aD : SL E1) ≠ aArr from nd6 rfl), Function.update_idem]

end Sig

/-! ## One loop iteration -/

section Step

variable {E1 R1 : Type} [DecidableEq E1] {q : ℕ} [NeZero q]

/-- The `K1` contract body for `π = swap` (the shape of `K1PairPermMixStmt q swap`). -/
def K1Spec (q : ℕ) [NeZero q] (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) (C1 : ℕ) :
    Prop :=
  ∀ (N0 N1 N2 : ℕ) (v : List (List Bool)) (rest r2 r3 : List Sym)
    (S : KLoc (Fin 4) E1 → List Sym),
    v.length = N0 * q * N1 * q * N2 → BlkTerm rest → TermOK r2 → TermOK r3 →
    S (.inl 0) = arrSyms v ++ rest → S (.inl 2) = natSyms N1 ++ r2 →
    S (.inl 3) = natSyms N2 ++ r3 →
    Runs P1 S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
      (arrSyms (permByInv (pairPermMixAddr q N1 N2 (Equiv.prodComm (Fin q) (Fin q)).symm) v) ++
        S (.inl 1))) (fun _ => True) (C1 * (vol v + 1))

theorem nodup_mul :
    [(aN2 : SL E1), aQ, aTd, aA, aBs, aAcc, aT2].Nodup := of_decide_eq_true rfl

/-- **One iteration**: the digit pair given by `(n1, n2)` is swapped in place and `N2 ← N2·q`. -/
theorem step6_runs {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1} {C1 : ℕ}
    (hspec : K1Spec q P1 C1) (B0 : SL E1 → List Sym) (u out : List (List Bool))
    (rest XD XT X1 X2 kc : List Sym) (N0 n1 n2 : ℕ) (hrest : BlkTerm rest)
    (hlen : u.length = N0 * q * n1 * q * n2) (hN1 : B0 aN1 = natSyms n1 ++ Sym.mark :: X1)
    (hout : out = permByInv (pairPermMixAddr q n1 n2 (Equiv.prodComm (Fin q) (Fin q)).symm) u) :
    Runs (step6 q P1) (sig B0 (arrSyms u ++ rest) XD XT (natSyms n2 ++ Sym.mark :: X2) kc)
      (sig B0 (arrSyms out ++ rest) XD XT (natSyms (n2 * q) ++ Sym.mark :: X2) kc)
      (fun _ => True)
      (1 + (1 + (C1 * (vol u + 1) + ((3 * (arrSyms out).length + 2) +
        ((3 * (arrSyms out).reverse.length + 2) + NatArith.mulConstCost n2 q))))) := by
  -- guards
  have q1 := runs_liftG (lO (R1 := R1)) (C7TopAux.pushC_runs aD Sym.mark
    (sig B0 (arrSyms u ++ rest) XD XT (natSyms n2 ++ Sym.mark :: X2) kc))
  rw [sig_D, sig_upd_D] at q1
  have q2 := runs_liftG (lO (R1 := R1)) (C7TopAux.pushC_runs aT Sym.mark
    (sig B0 (arrSyms u ++ rest) (Sym.mark :: XD) XT (natSyms n2 ++ Sym.mark :: X2) kc))
  rw [sig_T, sig_upd_T] at q2
  -- the K1 call
  have e0 : (sig B0 (arrSyms u ++ rest) (Sym.mark :: XD) (Sym.mark :: XT)
      (natSyms n2 ++ Sym.mark :: X2) kc ∘ ιS) (.inl 0) = arrSyms u ++ rest := sig_Arr _ _ _ _ _ _
  have e2 : (sig B0 (arrSyms u ++ rest) (Sym.mark :: XD) (Sym.mark :: XT)
      (natSyms n2 ++ Sym.mark :: X2) kc ∘ ιS) (.inl 2) = natSyms n1 ++ Sym.mark :: X1 := by
    show sig _ _ _ _ _ _ aN1 = _
    rw [sig_other _ _ _ _ _ _ (nd6 rfl) (nd6 rfl) (nd6 rfl) (nd6 rfl) (nd6 rfl)]
    exact hN1
  have e3 : (sig B0 (arrSyms u ++ rest) (Sym.mark :: XD) (Sym.mark :: XT)
      (natSyms n2 ++ Sym.mark :: X2) kc ∘ ιS) (.inl 3) = natSyms n2 ++ Sym.mark :: X2 :=
    sig_N2 _ _ _ _ _ _
  have hP := hspec N0 n1 n2 u rest (Sym.mark :: X1) (Sym.mark :: X2) _ hlen hrest
    (TermOK.cons rfl _) (TermOK.cons rfl _) e0 e2 e3
  rw [← hout] at hP
  have hι0 : ιS (E1 := E1) (.inl 0) = aArr := rfl
  have hι1 : ιS (E1 := E1) (.inl 1) = aD := rfl
  have hBk' : sig B0 rest (arrSyms out ++ Sym.mark :: XD) (Sym.mark :: XT)
      (natSyms n2 ++ Sym.mark :: X2) kc =
      Function.update (Function.update (sig B0 (arrSyms u ++ rest) (Sym.mark :: XD)
        (Sym.mark :: XT) (natSyms n2 ++ Sym.mark :: X2) kc) aArr rest) aD
        (arrSyms out ++ sig B0 (arrSyms u ++ rest) (Sym.mark :: XD) (Sym.mark :: XT)
          (natSyms n2 ++ Sym.mark :: X2) kc aD) := by
    rw [sig_upd_Arr, sig_upd_D, sig_D]
  have hcomp : sig B0 rest (arrSyms out ++ Sym.mark :: XD) (Sym.mark :: XT)
      (natSyms n2 ++ Sym.mark :: X2) kc ∘ ιS =
      Function.update (Function.update (sig B0 (arrSyms u ++ rest) (Sym.mark :: XD)
        (Sym.mark :: XT) (natSyms n2 ++ Sym.mark :: X2) kc ∘ ιS) (.inl 0) rest) (.inl 1)
        (arrSyms out ++ (sig B0 (arrSyms u ++ rest) (Sym.mark :: XD) (Sym.mark :: XT)
          (natSyms n2 ++ Sym.mark :: X2) kc ∘ ιS) (.inl 1)) := by
    rw [hBk', ← hι0, ← hι1, Function.update_comp_eq_of_injective _ ιS_inj,
      Function.update_comp_eq_of_injective _ ιS_inj]
    rfl
  have houts : ∀ k, (∀ x, ιS x ≠ k) →
      sig B0 rest (arrSyms out ++ Sym.mark :: XD) (Sym.mark :: XT)
        (natSyms n2 ++ Sym.mark :: X2) kc k =
      sig B0 (arrSyms u ++ rest) (Sym.mark :: XD) (Sym.mark :: XT)
        (natSyms n2 ++ Sym.mark :: X2) kc k := by
    intro k hk
    rw [hBk', Function.update_of_ne (fun h => hk (.inl 1) (hι1.trans h.symm)),
      Function.update_of_ne (fun h => hk (.inl 0) (hι0.trans h.symm))]
  have q3 := runs_callInj ιS_inj (lK (R1 := R1)) (by rw [hcomp]; exact hP) houts
  -- rewinds
  have q4 := runs_liftG (lO (R1 := R1)) (C7TopAux.rewind_runs (src := aD) (dst := aT) (nd6 rfl)
    Sym.mark (arrSyms out) XD (sig B0 rest (arrSyms out ++ Sym.mark :: XD) (Sym.mark :: XT)
      (natSyms n2 ++ Sym.mark :: X2) kc) (C7TopAux.mark_not_mem_arrSyms out) (sig_D _ _ _ _ _ _))
  rw [sig_upd_D, sig_T, sig_upd_T] at q4
  have q5 := runs_liftG (lO (R1 := R1)) (C7TopAux.rewind_runs (src := aT) (dst := aArr) (nd6 rfl)
    Sym.mark (arrSyms out).reverse XT (sig B0 rest XD ((arrSyms out).reverse ++ Sym.mark :: XT)
      (natSyms n2 ++ Sym.mark :: X2) kc) (by simpa using C7TopAux.mark_not_mem_arrSyms out)
      (sig_T _ _ _ _ _ _))
  rw [sig_upd_T, sig_Arr, sig_upd_Arr, List.reverse_reverse] at q5
  -- N2 ← N2 · q
  have q6 := runs_liftG (lN (R1 := R1)) (NatArith.runs_mulConstN nodup_mul q n2
    (Sym.mark :: X2) (sig B0 (arrSyms out ++ rest) XD XT (natSyms n2 ++ Sym.mark :: X2) kc)
    (TermOK.cons rfl _) (sig_N2 _ _ _ _ _ _))
  rw [sig_upd_N2] at q6
  exact WP.W9comp.runs_seq q1 (WP.W9comp.runs_seq q2 (WP.W9comp.runs_seq q3
    (WP.W9comp.runs_seq q4 (WP.W9comp.runs_seq q5 q6))))

end Step

/-! ## Prelude and postlude -/

section Ends

variable {E1 R1 : Type} [DecidableEq E1]

theorem dec_on {X t : SL E1} (hXt : X ≠ t) (Sx : SL E1 → List Sym) (W : List Sym)
    (hW : TermOK W) (n : ℕ) :
    Runs (dec X t) (Function.update Sx X (natSyms (n + 1) ++ W))
      (Function.update Sx X (natSyms n ++ W)) (fun _ => True)
      (6 * zerosLead (encodeNat (n + 1)) + 8) := by
  refine Runs.of_eval fun v => ?_
  have e := dec_eval hXt [] v n W (Function.update Sx X (natSyms (n + 1) ++ W)) hW
    (by rw [Function.update_self]; rfl)
  rw [Function.update_idem] at e
  exact ⟨_, _, e, trivial, le_rfl⟩

theorem nodup_pow :
    [(aN1 : SL E1), aEc, aKc, aTm, aQ, aTd, aA, aBs, aAcc].Nodup := of_decide_eq_true rfl

/-- **Prelude**: `N1 = G·q^{e-1}`, `N2 = B` above guards; every other stack restored. -/
theorem prelude6_runs (q : ℕ) (hq : 1 ≤ q) (S : SL E1 → List Sym) {e G B : ℕ}
    (r1 r2 r3 : List Sym) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (hS1 : S aE = natSyms e ++ r1) (hS2 : S aG = natSyms G ++ r2)
    (hS3 : S aB = natSyms B ++ r3) (he : 1 ≤ e) :
    Runs (prelude6 (R1 := R1) q) S
      (Function.update (Function.update S aN1 (natSyms (G * q ^ (e - 1)) ++ Sym.mark :: S aN1))
        aN2 (natSyms B ++ Sym.mark :: S aN2)) (fun _ => True)
      (1 + (7 * bitLen G + 7 + (1 + (7 * bitLen e + 7 + (6 * zerosLead (encodeNat (e - 1 + 1)) + 8 +
        (NatArith.powCost q G (e - 1) + (2 * (natSyms (e - 1)).length + 2 +
          (1 + (7 * bitLen B + 7))))))))) := by
  have q1 := runs_liftG (lO (R1 := R1)) (C7TopAux.pushC_runs aN1 Sym.mark S)
  have q2 := runs_liftG (lO (R1 := R1)) (C7TopAux.copy_on (src := aG) (X := aN1) (tmp := aTm)
    (nd6 rfl) (nd6 rfl) (nd6 rfl) S (Sym.mark :: S aN1) G r2 hr2 hS2)
  set S2 := Function.update S aN1 (natSyms G ++ Sym.mark :: S aN1) with hS2d
  have q3 := runs_liftG (lO (R1 := R1)) (C7TopAux.pushC_runs aEc Sym.mark S2)
  rw [show S2 aEc = S aEc from Function.update_of_ne (nd6 rfl) _ _] at q3
  have q4 := runs_liftG (lO (R1 := R1)) (C7TopAux.copy_on (src := aE) (X := aEc) (tmp := aTm)
    (nd6 rfl) (nd6 rfl) (nd6 rfl) S2 (Sym.mark :: S aEc) e r1 hr1
    (by rw [hS2d, Function.update_of_ne (nd6 rfl)]; exact hS1))
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have q5 := runs_liftG (lO (R1 := R1)) (dec_on (X := aEc) (t := aTm) (nd6 rfl) S2
    (Sym.mark :: S aEc) (TermOK.cons rfl _) e')
  have q6 := runs_liftG (lN (R1 := R1)) (NatArith.runs_powMulN nodup_pow q hq G e'
    (Sym.mark :: S aN1) (Sym.mark :: S aEc) (Function.update S2 aEc (natSyms e' ++ Sym.mark :: S aEc))
    (TermOK.cons rfl _) (TermOK.cons rfl _)
    (by rw [Function.update_of_ne (nd6 rfl), hS2d, Function.update_self])
    (Function.update_self _ _ _))
  have hc6 : Function.update (Function.update S2 aEc (natSyms e' ++ Sym.mark :: S aEc)) aN1
      (natSyms (G * q ^ e') ++ Sym.mark :: S aN1) =
      Function.update (Function.update S aN1 (natSyms (G * q ^ e') ++ Sym.mark :: S aN1)) aEc
        (natSyms e' ++ Sym.mark :: S aEc) := by
    rw [hS2d, Function.update_comm (show (aEc : SL E1) ≠ aN1 from nd6 rfl), Function.update_idem]
  rw [hc6] at q6
  have q7 := runs_liftG (lO (R1 := R1)) (C7TopAux.dropTo_runs aEc Sym.mark (natSyms e') (S aEc)
    (Function.update (Function.update S aN1 (natSyms (G * q ^ e') ++ Sym.mark :: S aN1)) aEc
      (natSyms e' ++ Sym.mark :: S aEc)) (C7TopAux.mark_not_mem_natSyms e')
    (Function.update_self _ _ _))
  rw [Function.update_idem, show S aEc = Function.update S aN1 (natSyms (G * q ^ e') ++
    Sym.mark :: S aN1) aEc from (Function.update_of_ne (nd6 rfl) _ _).symm,
    Function.update_eq_self] at q7
  have q8 := runs_liftG (lO (R1 := R1)) (C7TopAux.pushC_runs aN2 Sym.mark
    (Function.update S aN1 (natSyms (G * q ^ e') ++ Sym.mark :: S aN1)))
  rw [show Function.update S aN1 (natSyms (G * q ^ e') ++ Sym.mark :: S aN1) aN2 = S aN2 from
    Function.update_of_ne (nd6 rfl) _ _] at q8
  have q9 := runs_liftG (lO (R1 := R1)) (C7TopAux.copy_on (src := aB) (X := aN2) (tmp := aTm)
    (nd6 rfl) (nd6 rfl) (nd6 rfl)
    (Function.update S aN1 (natSyms (G * q ^ e') ++ Sym.mark :: S aN1)) (Sym.mark :: S aN2) B r3
    hr3 (by rw [Function.update_of_ne (nd6 rfl)]; exact hS3))
  simp only [Nat.add_sub_cancel]
  exact WP.W9comp.runs_seq q1 (WP.W9comp.runs_seq q2 (WP.W9comp.runs_seq q3
    (WP.W9comp.runs_seq q4 (WP.W9comp.runs_seq q5 (WP.W9comp.runs_seq q6
    (WP.W9comp.runs_seq q7 (WP.W9comp.runs_seq q8 q9)))))))

end Ends

/-! ## Loop-state normal form -/

theorem sig_eq_upd {E1 : Type} [DecidableEq E1] {B0 : SL E1 → List Sym} {a d t n k : List Sym}
    (hA : B0 aArr = a) (hD : B0 aD = d) (hT : B0 aT = t) (hK : B0 aKc = k) :
    sig B0 a d t n k = Function.update B0 aN2 n := by
  unfold sig
  rw [← hA, Function.update_eq_self, ← hD, Function.update_eq_self, ← hT, Function.update_eq_self,
    show k = Function.update B0 aN2 n aKc by
      rw [Function.update_of_ne (show (aKc : SL E1) ≠ aN2 from nd6 rfl), hK],
    Function.update_eq_self]

/-! ## Cost arithmetic -/

theorem sq_le_two_pow_succ : ∀ s : ℕ, s ^ 2 ≤ 2 ^ (s + 1)
  | 0 => by norm_num
  | s + 1 => by
    have ih := sq_le_two_pow_succ s
    have h1 : s < 2 ^ s := Nat.lt_two_pow_self
    have e1 : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
    have e2 : 2 ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by ring
    have e3 : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    omega

theorem sq_bitLen_le (M : ℕ) : bitLen M ^ 2 ≤ 4 * M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [bitLen, TMFw.encodeNat_zero]
  · have hs : bitLen M = Nat.size M := IntMulTM.length_encodeNat M
    have hpos : 0 < Nat.size M := Nat.size_pos.mpr hM
    have hlow : 2 ^ (Nat.size M - 1) ≤ M := by
      by_contra h
      push_neg at h
      have := Nat.size_le.mpr h
      omega
    have h1 := sq_le_two_pow_succ (Nat.size M)
    have h2 : 2 ^ (Nat.size M + 1) = 4 * 2 ^ (Nat.size M - 1) := by
      rw [show Nat.size M + 1 = (Nat.size M - 1) + 2 by omega, pow_add]; ring
    rw [hs]
    omega

theorem sq_add_le (x y : ℕ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  have h : (0 : ℤ) ≤ ((x : ℤ) - y) ^ 2 := sq_nonneg _
  have : (((x + y : ℕ) : ℤ)) ^ 2 ≤ 2 * (x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2 := by push_cast; nlinarith
  exact_mod_cast this

theorem le_of_dvd_shape {a b c : ℕ} (hc : 0 < c) (h : a * c = b) : a ≤ b := by
  rw [← h]; exact Nat.le_mul_of_pos_right a hc

end SubNLogN.Machine.AppC.C6SmallAux

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts AppC.C7Aux AppC.C6SmallAux Computability

/-- **[PROVED] Lemma A.8 in radix `q`, small widths** (`c6Small_holds`, 0 `sorry`; Lemma A.8 (`lem:transfer12`),
small-width radix-`q` branch). For every
`q ≥ 2`, `C6SmallStmt q` holds: the closed kernel `smallProg q P1` (`P1` the proved
`K1PairPermMixStmt q swap` kernel) interchanges the two `e`-digit chunks in place by `e`
digit-pair swaps, restores all counters and private stacks, and costs at most
`(34·C₁ + 200000 + 100000·(|q| + 2)^2) · (V + 1)`. -/
theorem c6Small_holds (q : ℕ) (hq : 2 ≤ q) : C6SmallStmt q := by
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨C1, hK1⟩ := K1Digit.k1PairPermMix_holds q (Equiv.prodComm (Fin q) (Fin q))
  obtain ⟨E1, i1, i2, R1, P1, hfin, hne, hcl, hspec⟩ := hK1 ()
  refine ⟨34 * C1 + 200000 + 100000 * (bitLen q + 2) ^ 2, fun _ => ⟨E1 ⊕ Fin 13, inferInstance,
    inferInstance, NatArith.Reg × R1, smallProg q P1, inferInstance,
    ⟨((none, (none, none, false), (none, none, .eq)), hne.some)⟩, smallProg_closed q hcl, ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he1 he34 hA hG hB hlen hw hrest hr1 hr2 hr3 hr4 hS0 hS1
    hS2 hS3 hS4
  have hq1 : 1 ≤ q := by omega
  have hqpos : 0 < q := by omega
  -- phase 1: prelude
  have rpre := prelude6_runs (R1 := R1) q hq1 S r1 r2 r3 hr1 hr2 hr3 hS1 hS2 hS3 he1
  obtain ⟨B0, hB0⟩ : ∃ B0 : SL E1 → List Sym,
      B0 = Function.update S aN1 (natSyms (G * q ^ (e - 1)) ++ Sym.mark :: S aN1) := ⟨_, rfl⟩
  have hB0o : ∀ x : SL E1, x ≠ aN1 → B0 x = S x := fun x hx => by
    rw [hB0, Function.update_of_ne hx]
  have hB0N1 : B0 aN1 = natSyms (G * q ^ (e - 1)) ++ Sym.mark :: S aN1 := by
    rw [hB0, Function.update_self]
  obtain ⟨St, hSt⟩ : ∃ St : ℕ → SL E1 → List Sym, ∀ j, St j = sig B0
      (arrSyms (uSeq q e G B v j) ++ rest) (S aD) (S aT)
      (natSyms (B * q ^ j) ++ Sym.mark :: S aN2) (S aKc) := ⟨_, fun j => rfl⟩
  have hSt0 : St 0 = Function.update (Function.update S aN1
      (natSyms (G * q ^ (e - 1)) ++ Sym.mark :: S aN1)) aN2 (natSyms B ++ Sym.mark :: S aN2) := by
    rw [hSt 0, pow_zero, Nat.mul_one, ← hB0]
    exact sig_eq_upd (by rw [hB0o _ (nd6 rfl)]; exact hS0) (hB0o _ (nd6 rfl))
      (hB0o _ (nd6 rfl)) (hB0o _ (nd6 rfl))
  rw [← hSt0] at rpre
  -- phase 2: the loop
  have rloop := K1.Rot.runs_nLoop (lO (R1 := R1)) (show (aE : SL E1) ≠ aKc from nd6 rfl)
    (show (aE : SL E1) ≠ aTm from nd6 rfl) (show (aKc : SL E1) ≠ aTm from nd6 rfl) (step6 q P1)
    St e r1 hr1
    (by rw [hSt 0, sig_other _ _ _ _ _ _ (nd6 rfl) (nd6 rfl) (nd6 rfl) (nd6 rfl) (nd6 rfl),
          hB0o _ (nd6 rfl)]; exact hS1)
    (by rw [hSt e, hSt 0, sig_Kc, sig_Kc])
    (fun j => 1 + (1 + (C1 * (vol (uSeq q e G B v j) + 1) +
      ((3 * (arrSyms (uSeq q e G B v (j + 1))).length + 2) +
        ((3 * (arrSyms (uSeq q e G B v (j + 1))).reverse.length + 2) +
          NatArith.mulConstCost (B * q ^ j) q)))))
    (fun j hj => by
      rw [hSt j, hSt (j + 1), sig_upd_Kc, sig_upd_Kc]
      have hs := step6_runs (P1 := P1) hspec B0 (uSeq q e G B v j) (uSeq q e G B v (j + 1)) rest
        (S aD) (S aT) (S aN1) (S aN2) (natSyms (e - (j + 1)) ++ Sym.mark :: St 0 aKc)
        (A * q ^ (e - 1 - j)) (G * q ^ (e - 1)) (B * q ^ j) hrest
        (by rw [uSeq_length, hlen, len_step hj]) hB0N1 rfl
      rw [show B * q ^ j * q = B * q ^ (j + 1) by ring] at hs
      exact hs)
  -- phase 3: postlude
  have p1 := AppC.C7TopAux.dropTo_runs aN1 Sym.mark (natSyms (G * q ^ (e - 1))) (S aN1) (St e)
    (AppC.C7TopAux.mark_not_mem_natSyms _)
    (by rw [hSt e, sig_other _ _ _ _ _ _ (nd6 rfl) (nd6 rfl) (nd6 rfl) (nd6 rfl) (nd6 rfl),
          hB0N1])
  have p2 := AppC.C7TopAux.dropTo_runs aN2 Sym.mark (natSyms (B * q ^ e)) (S aN2)
    (Function.update (St e) aN1 (S aN1)) (AppC.C7TopAux.mark_not_mem_natSyms _)
    (by rw [Function.update_of_ne (show (aN2 : SL E1) ≠ aN1 from nd6 rfl), hSt e, sig_N2])
  have rpost := runs_liftG (lO (R1 := R1)) (WP.W9comp.runs_seq p1 p2)
  have r := WP.W9comp.runs_seq rpre (WP.W9comp.runs_seq rloop rpost)
  -- final state
  have hfin : Function.update (Function.update (St e) aN1 (S aN1)) aN2 (S aN2) =
      Function.update S (.inl 0)
        (arrSyms (permByInv (swapFieldsInv (q ^ e) G (q ^ e) B) v) ++ rest) := by
    rw [hSt e, ← uSeq_full hG hB hlen]
    funext x
    by_cases h2 : x = aN2
    · subst h2
      rw [Function.update_self, Function.update_of_ne (show (aN2 : SL E1) ≠ .inl 0 from nd6 rfl)]
    by_cases h1 : x = aN1
    · subst h1
      rw [Function.update_of_ne (show (aN1 : SL E1) ≠ aN2 from nd6 rfl), Function.update_self,
        Function.update_of_ne (show (aN1 : SL E1) ≠ .inl 0 from nd6 rfl)]
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
    by_cases hk : x = aKc
    · subst hk
      rw [sig_Kc, Function.update_of_ne (show (aKc : SL E1) ≠ .inl 0 from nd6 rfl)]
    by_cases ht : x = aT
    · subst ht
      rw [sig_T, Function.update_of_ne (show (aT : SL E1) ≠ .inl 0 from nd6 rfl)]
    by_cases hd : x = aD
    · subst hd
      rw [sig_D, Function.update_of_ne (show (aD : SL E1) ≠ .inl 0 from nd6 rfl)]
    by_cases ha : x = aArr
    · subst ha
      rw [sig_Arr]
      exact (Function.update_self (Sum.inl 0 : SL E1) _ S).symm
    · rw [sig_other _ _ _ _ _ _ hk h2 ht hd ha, hB0o _ h1]
      exact (Function.update_of_ne (show x ≠ .inl 0 from ha) _ _).symm
  refine WP.W9comp.runs_congr (WP.W9comp.runs_mono r (fun _ _ => trivial) ?_) hfin
  -- cost
  have hV : vol v = v.length * (w + 1) := vol_of_len hw
  have hvolu : ∀ j, j ≤ e → vol (uSeq q e G B v j) = vol v := fun j hj => by
    rw [vol_of_len (uSeq_width hG hB hlen hw j hj), uSeq_length, hV]
  have hMpos : 0 < v.length := by
    rw [hlen]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA (pow_pos hqpos e)) hG)
      (pow_pos hqpos e)) hB
  have hMV : v.length ≤ vol v := by rw [hV]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hBj : ∀ j, j ≤ e → B * q ^ j ≤ v.length := fun j hj => by
    have h1 : q ^ e = q ^ j * q ^ (e - j) := by rw [← pow_add]; congr 1; omega
    rw [hlen, h1]
    exact le_of_dvd_shape (c := A * (q ^ j * q ^ (e - j)) * G * q ^ (e - j))
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA
        (Nat.mul_pos (pow_pos hqpos _) (pow_pos hqpos _))) hG) (pow_pos hqpos _)) (by ring)
  have hGM : G * q ^ (e - 1) ≤ v.length := by
    have h1 : q ^ e = q ^ (e - 1) * q := by rw [← pow_succ]; congr 1; omega
    rw [hlen, h1]
    exact le_of_dvd_shape (c := A * (q ^ (e - 1) * q) * q * B)
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA (Nat.mul_pos (pow_pos hqpos _) hqpos)) hqpos) hB)
      (by ring)
  have hGl : G ≤ v.length := le_trans (Nat.le_mul_of_pos_right G (pow_pos hqpos _)) hGM
  have hBl : B ≤ v.length := by have := hBj 0 (by omega); simpa using this
  have hbG := AppC.C7TopAux.bitLen_mono hGl
  have hbB := AppC.C7TopAux.bitLen_mono hBl
  have hbGq := AppC.C7TopAux.bitLen_mono hGM
  have hbBe := AppC.C7TopAux.bitLen_mono (hBj e le_rfl)
  have hbe : bitLen e ≤ 6 :=
    AppC.C7TopAux.bitLen_le_of_lt (lt_of_lt_of_le (show e < 64 by omega) (by norm_num))
  have hbe1 : bitLen (e - 1) ≤ 6 := le_trans (AppC.C7TopAux.bitLen_mono (Nat.sub_le e 1)) hbe
  have hzl : zerosLead (encodeNat (e - 1 + 1)) ≤ 6 := by
    rw [Nat.sub_add_cancel he1]
    exact le_trans (zerosLead_le_length _) hbe
  have hLM : bitLen v.length ≤ v.length := AppC.C7TopAux.bitLen_le_self _
  have hWb : (bitLen v.length + (bitLen q + 2)) ^ 2 ≤ 8 * v.length + 2 * (bitLen q + 2) ^ 2 := by
    have h1 := sq_add_le (bitLen v.length) (bitLen q + 2)
    have h2 := sq_bitLen_le v.length
    omega
  have hpow : NatArith.powCost q G (e - 1) ≤
      34 * (200 * (bitLen v.length + (bitLen q + 2)) ^ 2) := by
    unfold NatArith.powCost
    have h1 : e - 1 + 1 ≤ 34 := by omega
    have h2 : (bitLen (G * q ^ (e - 1)) + bitLen q + 2) ^ 2 ≤
        (bitLen v.length + (bitLen q + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ h2)
  have hmc : ∀ j, j < e → NatArith.mulConstCost (B * q ^ j) q ≤
      114 * (bitLen v.length + (bitLen q + 2)) ^ 2 + 9 * (bitLen v.length + bitLen q) := by
    intro j hj
    have hb := AppC.C7TopAux.bitLen_mono (hBj j (by omega))
    have h1 := NatArith.mulConstCost_le (c := q) hb
    have h2 : bitLen (B * q ^ j * q) ≤ bitLen v.length + bitLen q :=
      le_trans (NatArith.bitLen_mul_le' _ _) (by omega)
    have h3 : (bitLen v.length + bitLen q + 2) ^ 2 = (bitLen v.length + (bitLen q + 2)) ^ 2 := by
      ring
    omega
  have hTa : ∀ j, j < e → (fun j => 1 + (1 + (C1 * (vol (uSeq q e G B v j) + 1) +
      ((3 * (arrSyms (uSeq q e G B v (j + 1))).length + 2) +
        ((3 * (arrSyms (uSeq q e G B v (j + 1))).reverse.length + 2) +
          NatArith.mulConstCost (B * q ^ j) q))))) j ≤
      C1 * (vol v + 1) + 6 * vol v + 6 + (114 * (bitLen v.length + (bitLen q + 2)) ^ 2 +
        9 * (bitLen v.length + bitLen q)) := by
    intro j hj
    dsimp only
    have h1 := hvolu j (by omega)
    have h2 : (arrSyms (uSeq q e G B v (j + 1))).length = vol v := hvolu (j + 1) (by omega)
    rw [h1, List.length_reverse, h2]
    have := hmc j hj
    omega
  have hsum := NatArith.sum_range_le e hTa
  have hsum34 := Nat.mul_le_mul_right (C1 * (vol v + 1) + 6 * vol v + 6 +
    (114 * (bitLen v.length + (bitLen q + 2)) ^ 2 + 9 * (bitLen v.length + bitLen q))) he34
  have hbq2 : bitLen q ≤ (bitLen q + 2) ^ 2 := by nlinarith
  have e1 : C1 * (vol v + 1) = C1 * vol v + C1 := by ring
  have e2 : (34 * C1 + 200000 + 100000 * (bitLen q + 2) ^ 2) * (vol v + 1) =
      34 * (C1 * vol v) + 34 * C1 + 200000 * vol v + 200000 +
        100000 * ((bitLen q + 2) ^ 2 * vol v) + 100000 * (bitLen q + 2) ^ 2 := by ring
  simp only [length_natSyms]
  omega

end SubNLogN.Machine
