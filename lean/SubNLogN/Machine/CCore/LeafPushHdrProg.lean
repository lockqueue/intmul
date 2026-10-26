/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafHdrBase
import SubNLogN.Machine.CCore.LeafPushHdrDefs
import WP.Inst.W6a

/-!
# C-core leaf (2): push the child header, program and exact run (`CCore/LeafPushHdrProg.lean`)

The kernel of `PushChildHdrStmt` (`CCore/SkelDefs.lean:190`) and everything about it except the
cost bound: from `desc = t.hdr ++ tdesc` (with `1 ≤ t.k`) it pushes
`childHdr t a = hdrSyms [P, d, r, Δ, A/W, R/W, K, D, S, j0 + a·m^(k-1), k-1, ρ]` on `desc`.

## Program (`pushL a`, sub-layout `PL = Option PS`: `none` = `desc`, `some s` = scratch `s`)
1. `copyHdr`: copy the parent header onto `H`; copy its field `k` onto `Sk` (`extractField`).
2. `NatArith`: `Km1 := k - 1` (`subN`), `Wv := a · m^(k-1)` (`powMulN`, counter `Km1`).
3. Copy `j0` onto `J`; `Z2 := j0 + a · m^(k-1)` (`addN`).
4. Fields `9, 10` of `H` become `Z2`, `Km1` (`updField` with the kernel `repTop`, via
   `runs_updFieldV`, a variant of `Calculus.runs_updField` whose kernel may read other stacks).
5. The divisor `W` on `Bw`; for fields `4` (`A`) and `5` (`R`): copy the field onto `X`, divide by
   `W` with the long division `WP.W6a.divModProg WP.Inst.subNat.prog` (embedded by `callInj`), write
   the quotient back into the field (`updField`, `repTop`), drop `X`, `Qd`, `Rd`.
6. `copyHdr` the child header from `H` onto `desc`; `dropHdr H`; drop the remaining numbers.
Every scratch stack is empty at the end; `desc` is the only interface stack read or written.

## Results
* `runs_pushL`: the exact `Runs` fact on the sub-layout, final state and cost `costL t a`
  (`CCore/LeafPushHdrDefs.lean`).
* `pushChildHdr_of_cost`: `PushChildHdrStmt p` from a cost bound
  `costL t a ≤ C · t.volG` under `CCoreBands p 1 t` (the kernel is `(pushL a).mapStk pEmb`;
  safety from `readsIn_of_forall` and `SafeRunsIn.of_runs_readsIn`, since `desc` and the private
  scratch are unframed in `ccoreFramed`).
-/

namespace SubNLogN.Machine.CCore.PushHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability
open SubNLogN.Machine.CCore.LeafHdrAux

/-- Private scratch stacks of the push kernel. -/
inductive PS
  | H | Tt | Tq | Sk | One | Km1 | Wv | Kc | tP | QP | Tdst | Am | Bs | Acc | J | Z2
  | X | Bw | Qd | Rd | Td | Xd | Zd
  deriving DecidableEq

instance : Fintype PS :=
  Fintype.ofList [.H, .Tt, .Tq, .Sk, .One, .Km1, .Wv, .Kc, .tP, .QP, .Tdst, .Am, .Bs, .Acc, .J, .Z2,
    .X, .Bw, .Qd, .Rd, .Td, .Xd, .Zd] (fun x => by cases x <;> simp)

/-- Sub-layout: `none` is `desc`, `some s` is scratch `s`. -/
abbrev PL : Type := Option PS

abbrev pD : PL := none
abbrev pH : PL := some .H
abbrev pTt : PL := some .Tt
abbrev pTq : PL := some .Tq
abbrev pSk : PL := some .Sk
abbrev pOne : PL := some .One
abbrev pKm1 : PL := some .Km1
abbrev pWv : PL := some .Wv
abbrev pKc : PL := some .Kc
abbrev ptP : PL := some .tP
abbrev pQP : PL := some .QP
abbrev pTdst : PL := some .Tdst
abbrev pAm : PL := some .Am
abbrev pBs : PL := some .Bs
abbrev pAcc : PL := some .Acc
abbrev pJ : PL := some .J
abbrev pZ2 : PL := some .Z2
abbrev pX : PL := some .X
abbrev pBw : PL := some .Bw
abbrev pQd : PL := some .Qd
abbrev pRd : PL := some .Rd
abbrev pTd : PL := some .Td
abbrev pXd : PL := some .Xd
abbrev pZd : PL := some .Zd

/-- Registers: the long-division registers and the `NatArith` registers. -/
abbrev DR : Type := WP.W6a.DReg WP.Inst.subNat.R
abbrev PReg : Type := DR × NatArith.Reg

def lDv : Lens PReg DR := Lens.fst _ _
def lNt : Lens PReg NatArith.Reg := Lens.snd _ _
def lSy : Lens PReg (Option Sym) := (Lens.snd _ _).comp NatArith.lW

def sP (p : SProg PL) : Prog PL (fun _ => Sym) PReg := p.liftRegs lSy
def nP (p : Prog PL (fun _ => Sym) NatArith.Reg) : Prog PL (fun _ => Sym) PReg := p.liftRegs lNt

/-- The embedding of the long-division stacks `A B Q R T X Z`. -/
def dEmb : WP.W6a.DStk → PL
  | .inl i => if i.val = 0 then pX else if i.val = 1 then pBw else if i.val = 2 then pQd else pRd
  | .inr j => if j.val = 0 then pTd else if j.val = 1 then pXd else pZd

/-- Long division `X / Bw` into `Qd` (remainder into `Rd`). -/
def divP : Prog PL (fun _ => Sym) PReg :=
  callInj dEmb lDv (WP.W6a.divModProg WP.Inst.subNat.prog)

/-- Number kernel: replace the top number of `H` by a copy of the number on `V`. -/
def repTop (V : PL) : SProg PL := .seq (WP.W3.dropNum pH) (copyBlock V pH pTq)

/-! ## The program -/

/-- Phase 1: copy the parent header onto `H`; copy its field `k` onto `Sk` (above a floor). -/
def ph1 : SProg PL :=
  .seq (copyHdr 12 pD pH pTt) (.seq (pushC pSk .mark) (extractField 10 pH pSk pTt pTq))

/-- Phase 2: `Km1 := k - 1`, `Wv := a · m^(k-1)` (each above a floor). -/
def ph2 (a : ℕ) : Prog PL (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.pushMark pOne) (.seq (NatArith.pushNat pOne 1) (.seq (NatArith.pushMark pKm1)
    (.seq (NatArith.subN pSk pOne pKm1 pKc ptP pQP) (.seq (NatArith.pushMark pWv)
      (.seq (NatArith.pushNat pWv a)
        (NatArith.powMulN pWv mn pKm1 pKc ptP pQP pTdst pAm pBs pAcc))))))

/-- Phase 3: copy the field `j0` onto `J` (above a floor). -/
def ph3 : SProg PL := .seq (pushC pJ .mark) (extractField 9 pH pJ pTt pTq)

/-- Phase 4: `Z2 := j0 + a · m^(k-1)` (above a floor). -/
def ph4 : Prog PL (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.pushMark pZ2) (NatArith.addN pJ pWv pZ2 pKc ptP pQP)

/-- Phase 5: fields `9` and `10` of `H` become `j0 + a · m^(k-1)` and `k - 1`. -/
def ph5 : SProg PL := .seq (updField 9 pH pTt (repTop pZ2)) (updField 10 pH pTt (repTop pKm1))

/-- Phase 6: the divisor `W` on `Bw` (above a floor). -/
def ph6 : Prog PL (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.pushMark pBw) (NatArith.pushNat pBw Wn)

/-- Division of field `i`, setup: copy field `i` of `H` onto `X`; floors on `Qd`, `Rd`. -/
def dvA (i : ℕ) : SProg PL :=
  .seq (pushC pX .mark) (.seq (extractField i pH pX pTt pTq) (.seq (pushC pQd .mark) (pushC pRd .mark)))

/-- Division of field `i`, write-back of the quotient into field `i` of `H`. -/
def dvB (i : ℕ) : SProg PL := updField i pH pTt (repTop pQd)

/-- Division of field `i`, cleanup. -/
def dvC : Prog PL (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.dropF pQd) (.seq (NatArith.dropF pRd) (NatArith.dropF pX))

/-- Field `i` of `H` becomes `fs[i] / W`. -/
def dvField (i : ℕ) : Prog PL (fun _ => Sym) PReg :=
  .seq (sP (dvA i)) (.seq divP (.seq (sP (dvB i)) (nP dvC)))

/-- Phase 7: copy the child header from `H` onto `desc`; erase `H`. -/
def ph7 : SProg PL := .seq (copyHdr 12 pH pD pTt) (dropHdr pH 12)

/-- Phase 8: drop the remaining numbers with their floors. -/
def ph8 : Prog PL (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.dropF pBw) (.seq (NatArith.dropF pZ2) (.seq (NatArith.dropF pJ)
    (.seq (NatArith.dropF pWv) (.seq (NatArith.dropF pKm1) (.seq (NatArith.dropF pOne)
      (NatArith.dropF pSk))))))

/-- **The push program** on the sub-layout (slot `a`). -/
def pushL (a : ℕ) : Prog PL (fun _ => Sym) PReg :=
  .seq (.seq (sP ph1) (.seq (nP (ph2 a)) (.seq (sP ph3) (.seq (nP ph4) (.seq (sP ph5) (nP ph6))))))
    (.seq (.seq (dvField 4) (dvField 5)) (.seq (sP ph7) (nP ph8)))

/-! ## Closedness -/

theorem closed_copyBlock' (s d t : PL) : (copyBlock s d t).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, popR, pushR, pushC, Lib.skip]

theorem closed_repTop (V : PL) : (repTop V).Closed :=
  ⟨WP.W3.closed_of_noRec rfl, closed_copyBlock' _ _ _⟩

theorem closed_ph1 : ph1.Closed :=
  ⟨closed_copyHdr _ _ _ _, by simp [Prog.FreeBelow, pushC], closed_extractField _ _ _ _ _⟩

theorem closed_ph2 (a : ℕ) : (ph2 a).Closed :=
  ⟨NatArith.closed_pushMark _, NatArith.closed_pushNat _ _, NatArith.closed_pushMark _,
    NatArith.closed_subN _ _ _ _ _ _, NatArith.closed_pushMark _, NatArith.closed_pushNat _ _,
    NatArith.closed_powMulN _ _ _ _ _ _ _ _ _ _⟩

theorem closed_ph3 : ph3.Closed := ⟨by simp [Prog.FreeBelow, pushC], closed_extractField _ _ _ _ _⟩

theorem closed_ph4 : ph4.Closed := ⟨NatArith.closed_pushMark _, NatArith.closed_addN _ _ _ _ _ _⟩

theorem closed_ph5 : ph5.Closed :=
  ⟨closed_updField _ _ _ (closed_repTop _), closed_updField _ _ _ (closed_repTop _)⟩

theorem closed_ph6 : ph6.Closed := ⟨NatArith.closed_pushMark _, NatArith.closed_pushNat _ _⟩

theorem closed_dvField (i : ℕ) : (dvField i).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ ⟨by simp [Prog.FreeBelow, pushC], closed_extractField _ _ _ _ _,
      by simp [Prog.FreeBelow, pushC], by simp [Prog.FreeBelow, pushC]⟩,
    closed_callInj _ _ (WP.W6a.divModProg_closed _ WP.Inst.subNat.closed),
    WP.W9comp.closed_liftRegs _ (closed_updField _ _ _ (closed_repTop _)),
    WP.W9comp.closed_liftRegs _ ⟨NatArith.closed_dropF _, NatArith.closed_dropF _,
      NatArith.closed_dropF _⟩⟩

theorem closed_ph7 : ph7.Closed := ⟨closed_copyHdr _ _ _ _, closed_dropHdr _ _⟩

theorem closed_ph8 : ph8.Closed :=
  ⟨NatArith.closed_dropF _, NatArith.closed_dropF _, NatArith.closed_dropF _,
    NatArith.closed_dropF _, NatArith.closed_dropF _, NatArith.closed_dropF _,
    NatArith.closed_dropF _⟩

theorem closed_pushL (a : ℕ) : (pushL a).Closed :=
  ⟨⟨WP.W9comp.closed_liftRegs _ closed_ph1, WP.W9comp.closed_liftRegs _ (closed_ph2 a),
    WP.W9comp.closed_liftRegs _ closed_ph3, WP.W9comp.closed_liftRegs _ closed_ph4,
    WP.W9comp.closed_liftRegs _ closed_ph5, WP.W9comp.closed_liftRegs _ closed_ph6⟩,
    ⟨closed_dvField 4, closed_dvField 5⟩, WP.W9comp.closed_liftRegs _ closed_ph7,
    WP.W9comp.closed_liftRegs _ closed_ph8⟩

/-! ## Checkpoint states -/

/-- A checkpoint state of the sub-layout: the named stacks; every temporary is empty. -/
def stP (dsc h sk one km1 wv j z2 bw x qd rd : List Sym) : PL → List Sym
  | none => dsc
  | some .H => h
  | some .Sk => sk
  | some .One => one
  | some .Km1 => km1
  | some .Wv => wv
  | some .J => j
  | some .Z2 => z2
  | some .Bw => bw
  | some .X => x
  | some .Qd => qd
  | some .Rd => rd
  | some _ => []

section Upd

variable (dsc h sk one km1 wv j z2 bw x qd rd y : List Sym)

theorem stP_upd_D : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pD y =
    stP y h sk one km1 wv j z2 bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_H : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pH y =
    stP dsc y sk one km1 wv j z2 bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_Sk : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pSk y =
    stP dsc h y one km1 wv j z2 bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_One : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pOne y =
    stP dsc h sk y km1 wv j z2 bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_Km1 : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pKm1 y =
    stP dsc h sk one y wv j z2 bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_Wv : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pWv y =
    stP dsc h sk one km1 y j z2 bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_J : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pJ y =
    stP dsc h sk one km1 wv y z2 bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_Z2 : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pZ2 y =
    stP dsc h sk one km1 wv j y bw x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_Bw : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pBw y =
    stP dsc h sk one km1 wv j z2 y x qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_X : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pX y =
    stP dsc h sk one km1 wv j z2 bw y qd rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_Qd : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pQd y =
    stP dsc h sk one km1 wv j z2 bw x y rd := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

theorem stP_upd_Rd : Function.update (stP dsc h sk one km1 wv j z2 bw x qd rd) pRd y =
    stP dsc h sk one km1 wv j z2 bw x qd y := by
  funext k; rcases k with _ | s
  · rfl
  · cases s <;> rfl

end Upd

/-! ## Runs facts: helpers -/

theorem hdr_fsP (t : CCoreRT) : t.hdr = W9.hdrSyms (fsP t) := rfl

theorem termOK_markL (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl _

theorem runs_dropNumP {K : Type} [DecidableEq K] {k : K} (n : ℕ) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (WP.W3.dropNum k) S (Function.update S k rest) (fun _ => True) (2 * bitLen n + 4) :=
  Runs.of_eval fun v => ⟨_, _, WP.W3.dropNum_eval [] v (encodeNat n) rest S hrest hS, trivial,
    by unfold bitLen; omega⟩

/-- `repTop V`: the top number `f` of `H` is replaced by a copy of the number `g` on `V`. -/
theorem runs_repTop {V : PL} (hVH : V ≠ pH) (hVq : V ≠ pTq) (f g : ℕ) (rv tl' : List Sym)
    (S' : PL → List Sym) (hrv : TermOK rv) (htl : TermOK tl') (hH : S' pH = natSyms f ++ tl')
    (hV : S' V = natSyms g ++ rv) :
    Runs (repTop V) S' (Function.update S' pH (natSyms g ++ tl')) (fun _ => True)
      (2 * bitLen f + 7 * bitLen g + 11) := by
  have r1 := runs_dropNumP f tl' S' htl hH
  have r2 := HdrAux.runs_copyBlock (src := V) (dst := pH) (tmp := pTq) hVH hVq (by decide)
    (encodeNat g) rv (Function.update S' pH tl') hrv
    (by rw [Function.update_of_ne hVH]; exact hV)
  rw [Function.update_idem, Function.update_self] at r2
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 r2) (fun _ _ => trivial) ?_
  unfold bitLen
  omega

/-- **`updField` with a kernel that reads other stacks** (variant of `runs_updField`): the kernel
may use that every stack other than `d` and `t` is as in the initial state. -/
theorem runs_updFieldV {K : Type} [DecidableEq K] {d t : K} (hdt : d ≠ t) (ker : SProg K) {i : ℕ}
    {fs : List ℕ} (hi : i < fs.length) (g Tk : ℕ) (tl : List Sym) (S : K → List Sym)
    (hS : S d = W9.hdrSyms fs ++ tl) (ht : TermOK (S t))
    (hker : ∀ (tl' : List Sym) (S' : K → List Sym), TermOK tl' →
      S' d = natSyms fs[i] ++ tl' → (∀ k, k ≠ d → k ≠ t → S' k = S k) →
      Runs ker S' (Function.update S' d (natSyms g ++ tl')) (fun _ => True) Tk) :
    Runs (updField i d t ker) S (Function.update S d (W9.hdrSyms (fs.set i g) ++ tl))
      (fun _ => True) (2 * ((fs.take i).map fun f => 3 * bitLen f + 6).sum + Tk + 2) := by
  have hlen : (fs.take i).length = i := List.length_take_of_le hi.le
  have hsplit : fs = fs.take i ++ fs[i] :: fs.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i fs, List.drop_eq_getElem_cons hi]
  have hS1 : S d = W9.hdrSyms (fs.take i) ++
      (natSyms fs[i] ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl)) := by
    rw [hS]
    conv_lhs => rw [hsplit]
    rw [HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons]
    simp only [List.append_assoc, List.cons_append]
  have h1 := runs_moveFieldsTo hdt (fs.take i) _ S hS1
  rw [hlen] at h1
  have h2 := hker (Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl))
    (Function.update (Function.update S d (natSyms fs[i] ++ Sym.mark ::
      (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) t (movedFields (fs.take i) ++ S t))
    (TermOK.cons rfl _) (by rw [Function.update_of_ne hdt, Function.update_self])
    (fun k hkd hkt => by rw [Function.update_of_ne hkt, Function.update_of_ne hkd])
  have h3 := runs_moveFieldsBack (Ne.symm hdt) (fs.take i).reverse (S t)
    (Function.update (Function.update (Function.update S d (natSyms fs[i] ++ Sym.mark ::
      (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) t (movedFields (fs.take i) ++ S t)) d
      (natSyms g ++ Sym.mark :: (W9.hdrSyms (fs.drop (i + 1)) ++ tl))) ht
    (by rw [Function.update_of_ne (Ne.symm hdt), Function.update_self]; rfl)
  rw [List.length_reverse, hlen] at h3
  have hc := RunsIn.seq (RunsIn.iff_runs.mpr h1)
    (RunsIn.seq (RunsIn.iff_runs.mpr h2) (RunsIn.iff_runs.mpr h3))
  have hset : fs.set i g = fs.take i ++ g :: fs.drop (i + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hi]
  refine RunsIn.iff_runs.mp (RunsIn.congr hc ?_ ?_)
  · funext k
    rw [List.reverse_reverse]
    by_cases hkd : k = d
    · rw [hkd, Function.update_self, Function.update_self, Function.update_self, hset,
        HdrAux.hdrSyms_append, HdrAux.hdrSyms_cons]
      simp only [List.append_assoc, List.cons_append]
    · rw [Function.update_of_ne hkd, Function.update_of_ne hkd]
      by_cases hkt : k = t
      · rw [hkt, Function.update_self]
      · rw [Function.update_of_ne hkt, Function.update_of_ne hkd, Function.update_of_ne hkt,
          Function.update_of_ne hkd]
  · rw [List.map_reverse, List.sum_reverse]
    omega

theorem runs_sP {p : SProg PL} {S S' : PL → List Sym} {T : ℕ} (h : Runs p S S' (fun _ => True) T) :
    Runs (sP p) S S' (fun _ => True) T :=
  WP.W9comp.runs_mono (WP.W0m.runs_liftRegs lSy h) (fun _ _ => trivial) le_rfl

theorem runs_nP {p : Prog PL (fun _ => Sym) NatArith.Reg} {S S' : PL → List Sym} {T : ℕ}
    (h : Runs p S S' (fun _ => True) T) : Runs (nP p) S S' (fun _ => True) T :=
  WP.W9comp.runs_mono (WP.W0m.runs_liftRegs lNt h) (fun _ _ => trivial) le_rfl

/-! ## Runs facts: the phases -/

theorem one_le_mn : 1 ≤ mn := by norm_num [mn, tripleM]

theorem runs_ph1 (t : CCoreRT) (tdesc : List Sym) :
    Runs ph1 (stP (t.hdr ++ tdesc) [] [] [] [] [] [] [] [] [] [] [])
      (stP (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) (natSyms t.k ++ [Sym.mark]) [] [] [] [] [] [] [] [] [])
      (fun _ => True)
      ((((fsP t).map fun f => 13 * bitLen f + 20).sum + 2) + 1 +
        (2 * (((fsP t).take 10).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.k + 9)) := by
  have r1 : Runs (copyHdr 12 pD pH pTt) (stP (t.hdr ++ tdesc) [] [] [] [] [] [] [] [] [] [] [])
      (stP (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) [] [] [] [] [] [] [] [] [] []) (fun _ => True)
      (((fsP t).map fun f => 13 * bitLen f + 20).sum + 2) :=
    WP.W9comp.runs_congr (runs_copyHdr (src := pD) (dst := pH) (t := pTt) (by decide) (by decide)
      (by decide) (fsP t) tdesc _ rfl TermOK.nil) (by rw [stP_upd_H]; rfl)
  have r2 : Runs (pushC pSk Sym.mark) (stP (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) [] [] [] [] [] [] [] [] [] [])
      (stP (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) [Sym.mark] [] [] [] [] [] [] [] [] []) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_pushC pSk Sym.mark _) (by rw [stP_upd_Sk]; rfl)
  have r3 : Runs (extractField 10 pH pSk pTt pTq)
      (stP (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) [Sym.mark] [] [] [] [] [] [] [] [] [])
      (stP (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) (natSyms t.k ++ [Sym.mark]) [] [] [] [] [] [] [] [] [])
      (fun _ => True)
      (2 * (((fsP t).take 10).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.k + 9) :=
    WP.W9comp.runs_congr (runs_extractField (d := pH) (dst := pSk) (t := pTt) (tmp := pTq)
      (by decide) (by decide) (by decide) (by decide) (by decide) (i := 10) (fs := fsP t)
      (by simp [fsP]) [] _ rfl TermOK.nil) (by rw [stP_upd_Sk]; rfl)
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3))
    (fun _ _ => trivial) (by omega)

theorem runs_ph2 (dsc h : List Sym) (k a : ℕ) (hk : 1 ≤ k) :
    Runs (ph2 a) (stP dsc h (natSyms k ++ [Sym.mark]) [] [] [] [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms (k - 1) ++ [Sym.mark]) (natSyms (a * mn ^ (k - 1)) ++ [Sym.mark]) [] [] [] [] [] [])
      (fun _ => True)
      (1 + (bitLen 1 + 1) + 1 + 20 * (bitLen k + bitLen 1 + 1) + 1 + (bitLen a + 1) +
        NatArith.powCost mn a (k - 1)) := by
  have r1 : Runs (NatArith.pushMark pOne) (stP dsc h (natSyms k ++ [Sym.mark]) [] [] [] [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) [Sym.mark] [] [] [] [] [] [] [] []) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (NatArith.runs_pushMark pOne _) (by rw [stP_upd_One]; rfl)
  have r2 : Runs (NatArith.pushNat pOne 1)
      (stP dsc h (natSyms k ++ [Sym.mark]) [Sym.mark] [] [] [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) [] [] [] [] [] [] [] [])
      (fun _ => True) (bitLen 1 + 1) :=
    WP.W9comp.runs_congr (NatArith.runs_pushNat pOne 1 _) (by rw [stP_upd_One]; rfl)
  have r3 : Runs (NatArith.pushMark pKm1)
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) [] [] [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) [Sym.mark] [] [] [] [] [] [] [])
      (fun _ => True) 1 :=
    WP.W9comp.runs_congr (NatArith.runs_pushMark pKm1 _) (by rw [stP_upd_Km1]; rfl)
  have r4 : Runs (NatArith.subN pSk pOne pKm1 pKc ptP pQP)
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) [Sym.mark] [] [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (k - 1) ++ [Sym.mark])
        [] [] [] [] [] [] []) (fun _ => True) (20 * (bitLen k + bitLen 1 + 1)) :=
    WP.W9comp.runs_congr (NatArith.runs_subN (by decide) k 1 [Sym.mark] [Sym.mark] _
      (termOK_markL []) (termOK_markL []) hk rfl rfl) (by rw [stP_upd_Km1]; rfl)
  have r5 : Runs (NatArith.pushMark pWv)
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (k - 1) ++ [Sym.mark])
        [] [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (k - 1) ++ [Sym.mark])
        [Sym.mark] [] [] [] [] [] []) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (NatArith.runs_pushMark pWv _) (by rw [stP_upd_Wv]; rfl)
  have r6 : Runs (NatArith.pushNat pWv a)
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (k - 1) ++ [Sym.mark])
        [Sym.mark] [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (k - 1) ++ [Sym.mark])
        (natSyms a ++ [Sym.mark]) [] [] [] [] [] []) (fun _ => True) (bitLen a + 1) :=
    WP.W9comp.runs_congr (NatArith.runs_pushNat pWv a _) (by rw [stP_upd_Wv]; rfl)
  have r7 : Runs (NatArith.powMulN pWv mn pKm1 pKc ptP pQP pTdst pAm pBs pAcc)
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (k - 1) ++ [Sym.mark])
        (natSyms a ++ [Sym.mark]) [] [] [] [] [] [])
      (stP dsc h (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (k - 1) ++ [Sym.mark])
        (natSyms (a * mn ^ (k - 1)) ++ [Sym.mark]) [] [] [] [] [] [])
      (fun _ => True) (NatArith.powCost mn a (k - 1)) :=
    WP.W9comp.runs_congr (NatArith.runs_powMulN (by decide) mn one_le_mn a (k - 1) [Sym.mark]
      [Sym.mark] _ (termOK_markL []) (termOK_markL []) rfl rfl) (by rw [stP_upd_Wv])
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6 r7))))))
    (fun _ _ => trivial) (by omega)

theorem runs_ph3 (t : CCoreRT) (dsc sk one km1 wv : List Sym) :
    Runs ph3 (stP dsc (W9.hdrSyms (fsP t) ++ []) sk one km1 wv [] [] [] [] [] [])
      (stP dsc (W9.hdrSyms (fsP t) ++ []) sk one km1 wv (natSyms t.j0 ++ [Sym.mark]) [] [] [] [] [])
      (fun _ => True)
      (1 + (2 * (((fsP t).take 9).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.j0 + 9)) := by
  have r1 : Runs (pushC pJ Sym.mark) (stP dsc (W9.hdrSyms (fsP t) ++ []) sk one km1 wv [] [] [] [] [] [])
      (stP dsc (W9.hdrSyms (fsP t) ++ []) sk one km1 wv [Sym.mark] [] [] [] [] []) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_pushC pJ Sym.mark _) (by rw [stP_upd_J]; rfl)
  have r2 : Runs (extractField 9 pH pJ pTt pTq)
      (stP dsc (W9.hdrSyms (fsP t) ++ []) sk one km1 wv [Sym.mark] [] [] [] [] [])
      (stP dsc (W9.hdrSyms (fsP t) ++ []) sk one km1 wv (natSyms t.j0 ++ [Sym.mark]) [] [] [] [] [])
      (fun _ => True)
      (2 * (((fsP t).take 9).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.j0 + 9) :=
    WP.W9comp.runs_congr (runs_extractField (d := pH) (dst := pJ) (t := pTt) (tmp := pTq)
      (by decide) (by decide) (by decide) (by decide) (by decide) (i := 9) (fs := fsP t)
      (by simp [fsP]) [] _ rfl TermOK.nil) (by rw [stP_upd_J]; rfl)
  exact WP.W9comp.runs_seq r1 r2

theorem runs_ph4 (dsc h sk one km1 : List Sym) (j w : ℕ) :
    Runs ph4 (stP dsc h sk one km1 (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark]) [] [] [] [] [])
      (stP dsc h sk one km1 (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark])
        (natSyms (j + w) ++ [Sym.mark]) [] [] [] [])
      (fun _ => True) (1 + 20 * (bitLen j + bitLen w + 1)) := by
  have r1 : Runs (NatArith.pushMark pZ2)
      (stP dsc h sk one km1 (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark]) [] [] [] [] [])
      (stP dsc h sk one km1 (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark]) [Sym.mark] [] [] [] [])
      (fun _ => True) 1 :=
    WP.W9comp.runs_congr (NatArith.runs_pushMark pZ2 _) (by rw [stP_upd_Z2]; rfl)
  have r2 : Runs (NatArith.addN pJ pWv pZ2 pKc ptP pQP)
      (stP dsc h sk one km1 (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark]) [Sym.mark] [] [] [] [])
      (stP dsc h sk one km1 (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark])
        (natSyms (j + w) ++ [Sym.mark]) [] [] [] [])
      (fun _ => True) (20 * (bitLen j + bitLen w + 1)) :=
    WP.W9comp.runs_congr (NatArith.runs_addN (by decide) j w [Sym.mark] [Sym.mark] _
      (termOK_markL []) (termOK_markL []) rfl rfl) (by rw [stP_upd_Z2]; rfl)
  exact WP.W9comp.runs_seq r1 r2

theorem runs_ph5 (t : CCoreRT) (dsc : List Sym) (w : ℕ) :
    Runs ph5 (stP dsc (W9.hdrSyms (fsP t) ++ []) (natSyms t.k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms (t.k - 1) ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) (natSyms t.j0 ++ [Sym.mark])
        (natSyms (t.j0 + w) ++ [Sym.mark]) [] [] [] [])
      (stP dsc (W9.hdrSyms (fs2 t w) ++ []) (natSyms t.k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms (t.k - 1) ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) (natSyms t.j0 ++ [Sym.mark])
        (natSyms (t.j0 + w) ++ [Sym.mark]) [] [] [] [])
      (fun _ => True)
      ((2 * (((fsP t).take 9).map fun f => 3 * bitLen f + 6).sum +
          (2 * bitLen t.j0 + 7 * bitLen (t.j0 + w) + 11) + 2) +
        (2 * ((((fsP t).set 9 (t.j0 + w)).take 10).map fun f => 3 * bitLen f + 6).sum +
          (2 * bitLen t.k + 7 * bitLen (t.k - 1) + 11) + 2)) := by
  have r1 := runs_updFieldV (d := pH) (t := pTt) (by decide) (repTop pZ2) (i := 9) (fs := fsP t)
    (by simp [fsP]) (t.j0 + w) (2 * bitLen t.j0 + 7 * bitLen (t.j0 + w) + 11) []
    (stP dsc (W9.hdrSyms (fsP t) ++ []) (natSyms t.k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms (t.k - 1) ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) (natSyms t.j0 ++ [Sym.mark])
        (natSyms (t.j0 + w) ++ [Sym.mark]) [] [] [] []) rfl TermOK.nil
    (fun tl' S' htl hH hS' => runs_repTop (by decide) (by decide) t.j0 (t.j0 + w) [Sym.mark] tl' S'
      (termOK_markL []) htl hH (by rw [hS' pZ2 (by decide) (by decide)]; rfl))
  rw [stP_upd_H] at r1
  have r2 := runs_updFieldV (d := pH) (t := pTt) (by decide) (repTop pKm1) (i := 10)
    (fs := (fsP t).set 9 (t.j0 + w)) (by show _ < 12; omega) (t.k - 1)
    (2 * bitLen t.k + 7 * bitLen (t.k - 1) + 11) []
    (stP dsc (W9.hdrSyms ((fsP t).set 9 (t.j0 + w)) ++ []) (natSyms t.k ++ [Sym.mark])
        (natSyms 1 ++ [Sym.mark]) (natSyms (t.k - 1) ++ [Sym.mark]) (natSyms w ++ [Sym.mark])
        (natSyms t.j0 ++ [Sym.mark]) (natSyms (t.j0 + w) ++ [Sym.mark]) [] [] [] []) rfl TermOK.nil
    (fun tl' S' htl hH hS' => runs_repTop (by decide) (by decide) t.k (t.k - 1) [Sym.mark] tl' S'
      (termOK_markL []) htl hH (by rw [hS' pKm1 (by decide) (by decide)]; rfl))
  rw [stP_upd_H] at r2
  exact WP.W9comp.runs_seq r1 r2

theorem runs_ph6 (dsc h sk one km1 wv j z2 : List Sym) :
    Runs ph6 (stP dsc h sk one km1 wv j z2 [] [] [] [])
      (stP dsc h sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark]) [] [] [])
      (fun _ => True) (1 + (bitLen Wn + 1)) := by
  have r1 : Runs (NatArith.pushMark pBw) (stP dsc h sk one km1 wv j z2 [] [] [] [])
      (stP dsc h sk one km1 wv j z2 [Sym.mark] [] [] []) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (NatArith.runs_pushMark pBw _) (by rw [stP_upd_Bw]; rfl)
  have r2 : Runs (NatArith.pushNat pBw Wn) (stP dsc h sk one km1 wv j z2 [Sym.mark] [] [] [])
      (stP dsc h sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark]) [] [] []) (fun _ => True)
      (bitLen Wn + 1) :=
    WP.W9comp.runs_congr (NatArith.runs_pushNat pBw Wn _) (by rw [stP_upd_Bw]; rfl)
  exact WP.W9comp.runs_seq r1 r2

theorem dEmb_injective : Function.Injective dEmb := by
  intro x y h
  rcases x with ⟨_ | _ | _ | _ | n, hx⟩ | ⟨_ | _ | _ | n, hx⟩ <;>
    rcases y with ⟨_ | _ | _ | _ | m, hy⟩ | ⟨_ | _ | _ | m, hy⟩
  all_goals first
    | rfl
    | exact absurd hx (by omega)
    | exact absurd hy (by omega)
    | (simp [dEmb] at h)

theorem Wn_pos : 0 < Wn := by decide

theorem runs_dvField (dsc sk one km1 wv j z2 : List Sym) (F : List ℕ) (i : ℕ) (hi : i < F.length) :
    Runs (dvField i)
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark]) [] [] [])
      (stP dsc (W9.hdrSyms (F.set i (F[i] / Wn)) ++ []) sk one km1 wv j z2
        (natSyms Wn ++ [Sym.mark]) [] [] [])
      (fun _ => True) (dvCost F i F[i]) := by
  have a1 : Runs (pushC pX Sym.mark)
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark]) [] [] [])
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark]) [Sym.mark] [] [])
      (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_pushC pX Sym.mark _) (by rw [stP_upd_X]; rfl)
  have a2 : Runs (extractField i pH pX pTt pTq)
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark]) [Sym.mark] [] [])
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [] []) (fun _ => True)
      (2 * ((F.take i).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen F[i] + 9) :=
    WP.W9comp.runs_congr (runs_extractField (d := pH) (dst := pX) (t := pTt) (tmp := pTq)
      (by decide) (by decide) (by decide) (by decide) (by decide) hi [] _ rfl TermOK.nil)
      (by rw [stP_upd_X]; rfl)
  have a3 : Runs (pushC pQd Sym.mark)
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [] [])
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [Sym.mark] []) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_pushC pQd Sym.mark _) (by rw [stP_upd_Qd]; rfl)
  have a4 : Runs (pushC pRd Sym.mark)
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [Sym.mark] [])
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [Sym.mark] [Sym.mark]) (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_pushC pRd Sym.mark _) (by rw [stP_upd_Rd]; rfl)
  have b : Runs divP
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [Sym.mark] [Sym.mark])
      (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) (natSyms (F[i] / Wn) ++ [Sym.mark])
        (natSyms (F[i] % Wn) ++ [Sym.mark])) (fun _ => True)
      ((2 * 20 + 70) * (bitLen F[i] * bitLen Wn + bitLen F[i] + bitLen Wn + 1)) := by
    refine runs_callInj dEmb_injective lDv (Q := fun _ => True) ?_ ?_
    · refine WP.W9comp.runs_congr (WP.W6a.divModProg_spec (by decide) WP.Inst.subNat.subSpec F[i] Wn
        [Sym.mark] [Sym.mark] _ Wn_pos (termOK_markL []) (termOK_markL []) rfl rfl) ?_
      funext x
      rcases x with ⟨_ | _ | _ | _ | n, hx⟩ | ⟨_ | _ | _ | n, hx⟩
      all_goals first | rfl | exact absurd hx (by omega)
    · intro k hk
      rcases k with _ | s
      · rfl
      · cases s
        all_goals first | rfl | exact absurd rfl (hk WP.W6a.sQ) | exact absurd rfl (hk WP.W6a.sR)
  have c := runs_updFieldV (d := pH) (t := pTt) (by decide) (repTop pQd) hi (F[i] / Wn)
    (2 * bitLen F[i] + 7 * bitLen (F[i] / Wn) + 11) []
    (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) (natSyms (F[i] / Wn) ++ [Sym.mark])
        (natSyms (F[i] % Wn) ++ [Sym.mark])) rfl TermOK.nil
    (fun tl' S' htl hH hS' => runs_repTop (by decide) (by decide) F[i] (F[i] / Wn) [Sym.mark] tl' S'
      (termOK_markL []) htl hH (by rw [hS' pQd (by decide) (by decide)]; rfl))
  rw [stP_upd_H] at c
  have d1 := NatArith.runs_dropF pQd (F[i] / Wn) Sym.mark []
    (stP dsc (W9.hdrSyms (F.set i (F[i] / Wn)) ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) (natSyms (F[i] / Wn) ++ [Sym.mark])
        (natSyms (F[i] % Wn) ++ [Sym.mark])) rfl rfl
  rw [stP_upd_Qd] at d1
  have d2 := NatArith.runs_dropF pRd (F[i] % Wn) Sym.mark []
    (stP dsc (W9.hdrSyms (F.set i (F[i] / Wn)) ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [] (natSyms (F[i] % Wn) ++ [Sym.mark])) rfl rfl
  rw [stP_upd_Rd] at d2
  have d3 := NatArith.runs_dropF pX F[i] Sym.mark []
    (stP dsc (W9.hdrSyms (F.set i (F[i] / Wn)) ++ []) sk one km1 wv j z2 (natSyms Wn ++ [Sym.mark])
        (natSyms F[i] ++ [Sym.mark]) [] []) rfl rfl
  rw [stP_upd_X] at d3
  have hA := WP.W9comp.runs_seq a1 (WP.W9comp.runs_seq a2 (WP.W9comp.runs_seq a3 a4))
  have hC := WP.W9comp.runs_seq d1 (WP.W9comp.runs_seq d2 d3)
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq (runs_sP hA) (WP.W9comp.runs_seq b
    (WP.W9comp.runs_seq (runs_sP c) (runs_nP hC)))) (fun _ _ => trivial)
    (by simp only [dvCost]; omega)

theorem runs_ph7 (dsc sk one km1 wv j z2 bw : List Sym) (F : List ℕ) (hF : F.length = 12) :
    Runs ph7 (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 bw [] [] [])
      (stP (W9.hdrSyms F ++ dsc) [] sk one km1 wv j z2 bw [] [] [])
      (fun _ => True)
      (((F.map fun f => 13 * bitLen f + 20).sum + 2) + ((F.map fun f => 2 * bitLen f + 5).sum + 1)) := by
  have r1 := runs_copyHdr (src := pH) (dst := pD) (t := pTt) (by decide) (by decide) (by decide) F []
    (stP dsc (W9.hdrSyms F ++ []) sk one km1 wv j z2 bw [] [] []) rfl TermOK.nil
  rw [hF, stP_upd_D] at r1
  have r2 := runs_dropHdr pH F []
    (stP (W9.hdrSyms F ++ dsc) (W9.hdrSyms F ++ []) sk one km1 wv j z2 bw [] [] []) rfl
  rw [hF, stP_upd_H] at r2
  exact WP.W9comp.runs_seq r1 r2

theorem runs_ph8 (dsc : List Sym) (k km1 w j z : ℕ) :
    Runs ph8 (stP dsc [] (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms km1 ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark])
        (natSyms z ++ [Sym.mark]) (natSyms Wn ++ [Sym.mark]) [] [] [])
      (stP dsc [] [] [] [] [] [] [] [] [] [] [])
      (fun _ => True)
      ((2 * bitLen Wn + 2) + ((2 * bitLen z + 2) + ((2 * bitLen j + 2) + ((2 * bitLen w + 2) +
        ((2 * bitLen km1 + 2) + ((2 * bitLen 1 + 2) + (2 * bitLen k + 2))))))) := by
  have r1 := NatArith.runs_dropF pBw Wn Sym.mark []
    (stP dsc [] (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms km1 ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark])
        (natSyms z ++ [Sym.mark]) (natSyms Wn ++ [Sym.mark]) [] [] []) rfl rfl
  rw [stP_upd_Bw] at r1
  have r2 := NatArith.runs_dropF pZ2 z Sym.mark []
    (stP dsc [] (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms km1 ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark])
        (natSyms z ++ [Sym.mark]) [] [] [] []) rfl rfl
  rw [stP_upd_Z2] at r2
  have r3 := NatArith.runs_dropF pJ j Sym.mark []
    (stP dsc [] (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms km1 ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) (natSyms j ++ [Sym.mark])
        [] [] [] [] []) rfl rfl
  rw [stP_upd_J] at r3
  have r4 := NatArith.runs_dropF pWv w Sym.mark []
    (stP dsc [] (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms km1 ++ [Sym.mark]) (natSyms w ++ [Sym.mark]) [] [] [] [] [] []) rfl rfl
  rw [stP_upd_Wv] at r4
  have r5 := NatArith.runs_dropF pKm1 km1 Sym.mark []
    (stP dsc [] (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
        (natSyms km1 ++ [Sym.mark]) [] [] [] [] [] [] []) rfl rfl
  rw [stP_upd_Km1] at r5
  have r6 := NatArith.runs_dropF pOne 1 Sym.mark []
    (stP dsc [] (natSyms k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) [] [] [] [] [] [] [] []) rfl rfl
  rw [stP_upd_One] at r6
  have r7 := NatArith.runs_dropF pSk k Sym.mark []
    (stP dsc [] (natSyms k ++ [Sym.mark]) [] [] [] [] [] [] [] [] []) rfl rfl
  rw [stP_upd_Sk] at r7
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6 r7)))))

theorem fs4_eq (t : CCoreRT) (a : ℕ) : fs4 t a =
    [t.P, t.d, t.r, t.Δ, t.A / Wn, t.R / Wn, t.K, t.D, t.S, t.j0 + a * mn ^ (t.k - 1), t.k - 1, t.ρ] :=
  rfl

theorem childHdr_eq (t : CCoreRT) (a : Fin mn) : childHdr t a = W9.hdrSyms (fs4 t a.val) := rfl

/-- **`pushL`**, exact: the child header is pushed on `desc`; the scratch is empty again. -/
theorem runs_pushL (t : CCoreRT) (a : ℕ) (tdesc : List Sym) (hk : 1 ≤ t.k) :
    Runs (pushL a) (stP (t.hdr ++ tdesc) [] [] [] [] [] [] [] [] [] [] [])
      (stP (W9.hdrSyms (fs4 t a) ++ (t.hdr ++ tdesc)) [] [] [] [] [] [] [] [] [] [] [])
      (fun _ => True) (costL t a) := by
  have h1 := runs_sP (runs_ph1 t tdesc)
  have h2 := runs_nP (runs_ph2 (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) t.k a hk)
  have h3 := runs_sP (runs_ph3 t (t.hdr ++ tdesc) (natSyms t.k ++ [Sym.mark])
    (natSyms 1 ++ [Sym.mark]) (natSyms (t.k - 1) ++ [Sym.mark])
    (natSyms (a * mn ^ (t.k - 1)) ++ [Sym.mark]))
  have h4 := runs_nP (runs_ph4 (t.hdr ++ tdesc) (W9.hdrSyms (fsP t) ++ []) (natSyms t.k ++ [Sym.mark])
    (natSyms 1 ++ [Sym.mark]) (natSyms (t.k - 1) ++ [Sym.mark]) t.j0 (a * mn ^ (t.k - 1)))
  have h5 := runs_sP (runs_ph5 t (t.hdr ++ tdesc) (a * mn ^ (t.k - 1)))
  have h6 := runs_nP (runs_ph6 (t.hdr ++ tdesc) (W9.hdrSyms (fs2 t (a * mn ^ (t.k - 1))) ++ [])
    (natSyms t.k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark]) (natSyms (t.k - 1) ++ [Sym.mark])
    (natSyms (a * mn ^ (t.k - 1)) ++ [Sym.mark]) (natSyms t.j0 ++ [Sym.mark])
    (natSyms (t.j0 + a * mn ^ (t.k - 1)) ++ [Sym.mark]))
  have hA := WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 (WP.W9comp.runs_seq h3
    (WP.W9comp.runs_seq h4 (WP.W9comp.runs_seq h5 h6))))
  clear h1 h2 h3 h4 h5 h6
  have h7 := runs_dvField (t.hdr ++ tdesc) (natSyms t.k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
    (natSyms (t.k - 1) ++ [Sym.mark]) (natSyms (a * mn ^ (t.k - 1)) ++ [Sym.mark])
    (natSyms t.j0 ++ [Sym.mark]) (natSyms (t.j0 + a * mn ^ (t.k - 1)) ++ [Sym.mark])
    (fs2 t (a * mn ^ (t.k - 1))) 4 (by show _ < 12; omega)
  have e4 : (fs2 t (a * mn ^ (t.k - 1)))[4]'(by show _ < 12; omega) = t.A := rfl
  rw [e4] at h7
  have h8 := runs_dvField (t.hdr ++ tdesc) (natSyms t.k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
    (natSyms (t.k - 1) ++ [Sym.mark]) (natSyms (a * mn ^ (t.k - 1)) ++ [Sym.mark])
    (natSyms t.j0 ++ [Sym.mark]) (natSyms (t.j0 + a * mn ^ (t.k - 1)) ++ [Sym.mark])
    ((fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn)) 5 (by show _ < 12; omega)
  have e5 : ((fs2 t (a * mn ^ (t.k - 1))).set 4 (t.A / Wn))[5]'(by show _ < 12; omega) = t.R := rfl
  rw [e5] at h8
  have hB := WP.W9comp.runs_seq h7 h8
  clear h7 h8
  have h9 := runs_sP (runs_ph7 (t.hdr ++ tdesc) (natSyms t.k ++ [Sym.mark]) (natSyms 1 ++ [Sym.mark])
    (natSyms (t.k - 1) ++ [Sym.mark]) (natSyms (a * mn ^ (t.k - 1)) ++ [Sym.mark])
    (natSyms t.j0 ++ [Sym.mark]) (natSyms (t.j0 + a * mn ^ (t.k - 1)) ++ [Sym.mark])
    (natSyms Wn ++ [Sym.mark]) (fs4 t a) rfl)
  have h10 := runs_nP (runs_ph8 (W9.hdrSyms (fs4 t a) ++ (t.hdr ++ tdesc)) t.k (t.k - 1)
    (a * mn ^ (t.k - 1)) t.j0 (t.j0 + a * mn ^ (t.k - 1)))
  have hC := WP.W9comp.runs_seq h9 h10
  clear h9 h10
  have hall := WP.W9comp.runs_seq hA (WP.W9comp.runs_seq hB hC)
  refine WP.W9comp.runs_mono hall (fun _ _ => trivial) (le_of_eq ?_)
  rw [costL]
  omega

/-! ## Embedding into the kernel layout -/

/-- Embedding of the sub-layout into `CL PS`: `none ↦ desc`, `some s ↦ scratch s`. -/
def pEmb : PL → CL PS
  | none => descL
  | some s => .inr s

theorem pEmb_injective : Function.Injective pEmb := by
  intro x y h
  cases x <;> cases y <;> simp_all [pEmb]

theorem comp_pEmb (S : CL PS → List Sym) (hcl : KClean S) (dsc : List Sym) (hd : S descL = dsc) :
    S ∘ pEmb = stP dsc [] [] [] [] [] [] [] [] [] [] [] := by
  funext x
  rcases x with _ | s
  · exact hd
  · cases s <;> exact hcl _

theorem comp_pEmb_upd (S : CL PS → List Sym) (hcl : KClean S) (v : List Sym) :
    (Function.update S descL v) ∘ pEmb = stP v [] [] [] [] [] [] [] [] [] [] [] := by
  funext x
  rcases x with _ | s
  · exact Function.update_self _ _ _
  · cases s <;>
    · show Function.update S descL v (.inr _) = []
      rw [Function.update_of_ne (by simp)]
      exact hcl _

end SubNLogN.Machine.CCore.PushHdrAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability
open SubNLogN.Machine.CCore.LeafHdrAux SubNLogN.Machine.CCore.PushHdrAux

/-- **`PushChildHdrStmt` from the cost bound.** The kernel is `(pushL a).mapStk pEmb` with scratch
`PS`, registers `PReg`, cutoff `P₀ = 1` and the constant of the cost bound. -/
theorem pushChildHdr_of_cost (p : LayerParams)
    (hc : ∃ C : ℕ, ∀ (t : CCoreRT) (a : ℕ), CCoreBands p 1 t → 1 ≤ t.k → a < mn →
      costL t a ≤ C * t.volG) :
    PushChildHdrStmt p := by
  obtain ⟨C, hC⟩ := hc
  refine ⟨1, C, fun a => ⟨PS, inferInstance, inferInstance, PReg, (pushL a.val).mapStk pEmb,
    inferInstance, inferInstance, closed_mapStk _ (closed_pushL _), ?_⟩⟩
  intro t tdesc S hb hk hcl hd
  have hrun := runs_pushL t a.val tdesc hk
  have h2 : Runs ((pushL a.val).mapStk pEmb) S
      (Function.update S descL (childHdr t a ++ (t.hdr ++ tdesc))) (fun _ => True)
      (costL t a.val) := by
    refine runs_mapStk_post pEmb_injective ?_ ?_
    · rw [comp_pEmb S hcl _ hd, comp_pEmb_upd S hcl, childHdr_eq]
      exact hrun
    · intro k hk'
      rw [Function.update_of_ne]
      intro hkd
      exact hk' none hkd.symm
  exact SafeRunsIn.mono (SafeRunsIn.of_runs_readsIn h2 (closed_mapStk _ (closed_pushL _))
    (readsIn_mapStk pEmb _ _ (readsIn_of_forall (fun x => by cases x <;> simp [pEmb, ccoreFramed])
      _)) []) (fun _ _ => trivial) (hC t a.val hb hk a.isLt)

end SubNLogN.Machine.CCore
