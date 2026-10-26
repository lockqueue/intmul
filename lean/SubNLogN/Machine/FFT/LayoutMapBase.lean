/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutHdr
import WP.W7k2.Ops
import WP.W6a.DivMod

/-!
# K4.3c base (`Machine/FFT/LayoutMapBase.lean`): host, record states and rules of the map builders

Infrastructure for the builders of the runtime maps of `L` and `U` (`LayoutMapGenStmt`,
`Machine/FFT/LayoutCompile.lean`): the host (`Loc 2 24`, the proved contract instances `copyNat`,
`dropNat`, `isZeroNat`, `decNat`, `incNat`, `addNat`, `cmpNat`, `divModNat`), states as records
`MS` with one field per stack (`toF`, update lemmas `upd_…`), wrapper programs and their host rules,
and the generic passes over the axis exponents of the header (`passB`, `passC`) and the final move
of the emitted fields (`moveO`). No `sorry`.
-/

namespace SubNLogN.Machine.FFT.LayoutMapAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.LayoutHdrAux (savedF savedF_nil savedF_concat natSyms_zero'
  hdrSyms_cons' hdrSyms_nil' midHdr_eq' opY cost1_le cost2_le one_le_opY bitLen_le
  loopCost_le_of_le sum_take_le' take_succ_sum' drop_hdr' savedF_take_succ' C_le_opY lsc)

/-! ## 1. Host, instances -/

/-- The builders' stacks: named `.inl 0` (header), `.inl 1` (destination), scratch `.inr 0 … 23`. -/
abbrev LM := Loc 2 24

/-- The contract instances used by the builders. -/
structure HI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ic : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  cm : Inst 2 4 Ordering
  dm : Inst 4 6 Unit

namespace HI

variable (I : HI)

/-- Host registers: a symbol register, then one register file per instance. -/
abbrev R : Type :=
  Option Sym × I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ic.R × I.ad.R × I.cm.R × I.dm.R

def lS : Lens I.R (Option Sym) := Lens.fst _ _
def lcp : Lens I.R I.cp.R := lsc (Lens.fst _ _)
def ldr : Lens I.R I.dr.R := lsc (lsc (Lens.fst _ _))
def liz : Lens I.R I.iz.R := lsc (lsc (lsc (Lens.fst _ _)))
def ldc : Lens I.R I.dc.R := lsc (lsc (lsc (lsc (Lens.fst _ _))))
def lic : Lens I.R I.ic.R := lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))
def lad : Lens I.R I.ad.R := lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _))))))
def lcm : Lens I.R I.cm.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.fst _ _)))))))
def ldm : Lens I.R I.dm.R := lsc (lsc (lsc (lsc (lsc (lsc (lsc (Lens.snd _ _)))))))

theorem R_finite : Finite I.R := by
  have := I.cp.fin; have := I.dr.fin; have := I.iz.fin; have := I.dc.fin; have := I.ic.fin
  have := I.ad.fin; have := I.cm.fin; have := I.dm.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  have := I.cp.ne; have := I.dr.ne; have := I.iz.ne; have := I.dc.ne; have := I.ic.ne
  have := I.ad.ne; have := I.cm.ne; have := I.dm.ne
  infer_instance

/-- All contract bodies with one shared constant. -/
structure Spec (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ic : SpecInc I.ic C
  ad : SpecAddNat I.ad C
  cm : SpecCmpNat I.cm C
  dm : SpecDivMod I.dm C

end HI

/-- Builder programs. -/
abbrev HP (I : HI) : Type := Prog LM (fun _ => Sym) I.R

/-! ### Stack names -/

abbrev sH : LM := .inl 0
abbrev sP : LM := .inl 1
abbrev vq : LM := .inr 0
abbrev vD : LM := .inr 1
abbrev vl : LM := .inr 2
abbrev vK : LM := .inr 3
abbrev vw : LM := .inr 4
abbrev vm : LM := .inr 5
abbrev vA : LM := .inr 6
abbrev cnt : LM := .inr 7
abbrev sv : LM := .inr 8
abbrev t1 : LM := .inr 9
abbrev slc : LM := .inr 10
abbrev vJ : LM := .inr 11
abbrev vb : LM := .inr 12
abbrev vDK : LM := .inr 13
abbrev sck : LM := .inr 14
abbrev spf : LM := .inr 15
abbrev srr : LM := .inr 16
abbrev scj : LM := .inr 17
abbrev sval : LM := .inr 18
abbrev sc2 : LM := .inr 19
abbrev sc3 : LM := .inr 20
abbrev so : LM := .inr 21
abbrev sL1 : LM := .inr 22
abbrev scs : LM := .inr 23
/-- Default stack of `callMap` (never used: all call lists are in range). -/
abbrev d0 : LM := .inl 0

/-! ## 2. States: one record field per stack -/

/-- The machine state, one field per stack. -/
@[ext] structure MS where
  (h p q D l K w m A c s t lc J b DK ck pf rr cj v c2 c3 o L1 cs : List Sym)

/-- The stacks of a record. -/
def toF (M : MS) : LM → List Sym
  | .inl i => if (i : ℕ) = 0 then M.h else M.p
  | .inr j => if (j : ℕ) = 0 then M.q else if (j : ℕ) = 1 then M.D else
      if (j : ℕ) = 2 then M.l else if (j : ℕ) = 3 then M.K else if (j : ℕ) = 4 then M.w else
      if (j : ℕ) = 5 then M.m else if (j : ℕ) = 6 then M.A else if (j : ℕ) = 7 then M.c else
      if (j : ℕ) = 8 then M.s else if (j : ℕ) = 9 then M.t else if (j : ℕ) = 10 then M.lc else
      if (j : ℕ) = 11 then M.J else if (j : ℕ) = 12 then M.b else if (j : ℕ) = 13 then M.DK else
      if (j : ℕ) = 14 then M.ck else if (j : ℕ) = 15 then M.pf else
      if (j : ℕ) = 16 then M.rr else if (j : ℕ) = 17 then M.cj else
      if (j : ℕ) = 18 then M.v else if (j : ℕ) = 19 then M.c2 else
      if (j : ℕ) = 20 then M.c3 else if (j : ℕ) = 21 then M.o else
      if (j : ℕ) = 22 then M.L1 else M.cs

section Upd

variable (M : MS) (x : List Sym)

theorem upd_h : Function.update (toF M) sH x = toF {M with h := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_p : Function.update (toF M) sP x = toF {M with p := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_q : Function.update (toF M) vq x = toF {M with q := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_D : Function.update (toF M) vD x = toF {M with D := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_l : Function.update (toF M) vl x = toF {M with l := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_K : Function.update (toF M) vK x = toF {M with K := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_w : Function.update (toF M) vw x = toF {M with w := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_m : Function.update (toF M) vm x = toF {M with m := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_A : Function.update (toF M) vA x = toF {M with A := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_c : Function.update (toF M) cnt x = toF {M with c := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_s : Function.update (toF M) sv x = toF {M with s := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_t : Function.update (toF M) t1 x = toF {M with t := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_lc : Function.update (toF M) slc x = toF {M with lc := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_J : Function.update (toF M) vJ x = toF {M with J := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_b : Function.update (toF M) vb x = toF {M with b := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_DK : Function.update (toF M) vDK x = toF {M with DK := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_ck : Function.update (toF M) sck x = toF {M with ck := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_pf : Function.update (toF M) spf x = toF {M with pf := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_rr : Function.update (toF M) srr x = toF {M with rr := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_cj : Function.update (toF M) scj x = toF {M with cj := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_v : Function.update (toF M) sval x = toF {M with v := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_c2 : Function.update (toF M) sc2 x = toF {M with c2 := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_c3 : Function.update (toF M) sc3 x = toF {M with c3 := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_o : Function.update (toF M) so x = toF {M with o := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_L1 : Function.update (toF M) sL1 x = toF {M with L1 := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

theorem upd_cs : Function.update (toF M) scs x = toF {M with cs := x} := by
  funext y; rcases y with i | j
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl

end Upd

/-! ## 3. Wrappers -/

/-- The comparison test `o = eq`. -/
def eqB (o : Ordering) : Bool := decide (o = Ordering.eq)

theorem eqB_ordOf (u v : ℕ) : eqB (TMFw.Lib.ordOf u v) = true ↔ u = v := by
  unfold eqB TMFw.Lib.ordOf
  split_ifs with h1 h2 <;> simp <;> omega

section Wrappers

variable (I : HI)

def hcp (x y : LM) : HP I := callI I.cp [x, y] d0 I.lcp
def hdr (x : LM) : HP I := callI I.dr [x] d0 I.ldr
def hic (x : LM) : HP I := callI I.ic [x] d0 I.lic
def hdc (x : LM) : HP I := callI I.dc [x] d0 I.ldc
def had (x y z : LM) : HP I := callI I.ad [x, y, z] d0 I.lad
def hdm (x y q r : LM) : HP I := callI I.dm [x, y, q, r] d0 I.ldm
/-- `if x = y then p else q` (compare, then branch). -/
def hifEq (x y : LM) (p q : HP I) : HP I :=
  (callI I.cm [x, y] d0 I.lcm).seq (.ite (fun s => eqB (I.cm.obs (I.lcm.get s))) p q)
/-- Count-down loop on `c` (`while c ≠ 0 do (dec c; body)`). -/
def hcd (c : LM) (body : HP I) : HP I := cdLoop I.iz I.dc I.liz I.ldc c d0 body
/-- No operation. -/
def hskip : HP I := .load id
/-- Push the field `natSyms v ++ [mark]` of the number on `x` onto `dst`. -/
def wrF (x dst : LM) : HP I := (pushS dst Sym.mark).seq (hcp I x dst)
/-- Move the top field of `src` onto `dst`. -/
def mvF (src dst : LM) : HP I :=
  (pushS dst Sym.mark).seq ((hcp I src dst).seq ((hdr I src).seq (popS src)))
/-- Read the top field of the header into `x` (copy, drop, pop the `mark`). -/
def rdF (x : LM) : HP I := (hcp I sH x).seq ((hdr I sH).seq (popS sH))
/-- `x := x + y` (through `t1`). -/
def addTo (x y : LM) : HP I := (had I x y t1).seq ((hdr I x).seq ((hcp I t1 x).seq (hdr I t1)))

theorem closed_wrF (x dst : LM) : (wrF I x dst).Closed :=
  WP.W9comp.closed_seq trivial (callI_closed _ _ _ _)

theorem closed_mvF (src dst : LM) : (mvF I src dst).Closed :=
  WP.W9comp.closed_seq trivial (WP.W9comp.closed_seq (callI_closed _ _ _ _)
    (WP.W9comp.closed_seq (callI_closed _ _ _ _) trivial))

theorem closed_rdF (x : LM) : (rdF I x).Closed :=
  WP.W9comp.closed_seq (callI_closed _ _ _ _) (WP.W9comp.closed_seq (callI_closed _ _ _ _) trivial)

theorem closed_addTo (x y : LM) : (addTo I x y).Closed :=
  WP.W9comp.closed_seq (callI_closed _ _ _ _) (WP.W9comp.closed_seq (callI_closed _ _ _ _)
    (WP.W9comp.closed_seq (callI_closed _ _ _ _) (callI_closed _ _ _ _)))

theorem closed_hifEq (x y : LM) (p q : HP I) (hp : p.Closed) (hq : q.Closed) :
    (hifEq I x y p q).Closed :=
  WP.W9comp.closed_seq (callI_closed _ _ _ _) ⟨hp, hq⟩

theorem closed_hcd (c : LM) (body : HP I) (hb : body.Closed) : (hcd I c body).Closed :=
  cdLoop_closed _ _ _ _ _ _ _ hb

end Wrappers

/-! ## 4. Host rules -/

section Rules

variable {I : HI} {C : ℕ}

theorem ht_cp (hI : I.Spec C) (x y : LM) (hxy : [x, y].Nodup) (B : LM → List Sym) (v : ℕ)
    (r P0 : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hy : B y = P0) :
    HT [] B (hcp I x y) (Function.update B y (natSyms v ++ P0)) (C * (bitLen v + 1)) := by
  have h := HT.copyNat hI.cp d0 I.lcp x y hxy (by decide) B v r hr hB []
  rw [hy] at h
  exact h

theorem ht_cp0 (hI : I.Spec C) (x y : LM) (hxy : [x, y].Nodup) (B : LM → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hy : B y = []) :
    HT [] B (hcp I x y) (Function.update B y (natSyms v)) (C * (bitLen v + 1)) := by
  have h := ht_cp hI x y hxy B v r [] hr hB hy
  rw [List.append_nil] at h
  exact h

theorem ht_dr (hI : I.Spec C) (x : LM) (B : LM → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (hdr I x) (Function.update B x r) (C * (bitLen v + 1)) :=
  HT.dropNat hI.dr d0 I.ldr x (by decide) B v r hr hB []

theorem ht_ad0 (hI : I.Spec C) (x y z : LM) (hxyz : [x, y, z].Nodup) (B : LM → List Sym)
    (u v : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B x = natSyms u ++ rx) (hy : B y = natSyms v ++ ry) (hz : B z = []) :
    HT [] B (had I x y z) (Function.update B z (natSyms (u + v)))
      (C * (bitLen u + bitLen v + 1)) := by
  have h := HT.addNat hI.ad d0 I.lad x y z hxyz (by decide) B u v rx ry hrx hry hx hy []
  rw [hz, List.append_nil] at h
  exact h

theorem ht_ic (hI : I.Spec C) (x : LM) (B : LM → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (hic I x) (Function.update B x (natSyms (v + 1) ++ r))
      (C * (ones (Computability.encodeNat v) + 1)) :=
  HT.incNat hI.ic d0 I.lic x (by decide) B v r hr hB []

theorem ht_dc (hI : I.Spec C) (x : LM) (B : LM → List Sym) (k : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms (k + 1) ++ r) :
    HT [] B (hdc I x) (Function.update B x (natSyms k ++ r))
      (C * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
  HT.callI_upd I.dc [x] d0 (List.nodup_singleton _) rfl (by decide) I.ldc B (.inl 0) _
    (hI.dc k r _ hr hB) []

theorem ht_dm0 (hI : I.Spec C) (x y q r : LM) (hnd : [x, y, q, r].Nodup) (B : LM → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hv0 : 0 < v) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (hq : B q = []) (hr : B r = []) :
    HT [] B (hdm I x y q r)
      (Function.update (Function.update B q (natSyms (u / v))) r (natSyms (u % v)))
      (C * (bitLen u * bitLen v + bitLen u + bitLen v + 1)) := by
  have h := HT.divModNat hI.dm d0 I.ldm x y q r hnd (by decide) B u v ru rv hv0 hru hrv hx hy []
  rw [hq, hr, List.append_nil, List.append_nil] at h
  exact h

theorem ht_ifEq (hI : I.Spec C) (x y : LM) (hxy : [x, y].Nodup) (B B' : LM → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (p q : HP I) {T₁ T₂ : ℕ}
    (hp : u = v → HT [] B p B' T₁) (hq : u ≠ v → HT [] B q B' T₂) :
    HT [] B (hifEq I x y p q) B' (C * (bitLen u + bitLen v + 1) + (max T₁ T₂ + 1)) :=
  HT.cmpNat_ite hI.cm d0 I.lcm x y hxy (by decide) B B' u v ru rv hru hrv hx hy eqB p q []
    (fun h => hp ((eqB_ordOf u v).1 h))
    (fun h => hq (fun e => by rw [(eqB_ordOf u v).2 e] at h; exact Bool.noConfusion h))

theorem ht_push (k : LM) (x : Sym) (B : LM → List Sym) (P0 : List Sym) (hk : B k = P0) :
    HT (σ := I.R) [] B (pushS k x) (Function.update B k (x :: P0)) 1 := by
  have h := HT.pushS (σ := I.R) k x B []
  rw [hk] at h
  exact h

theorem ht_pop (k : LM) (B : LM → List Sym) (x : Sym) (rest : List Sym) (hk : B k = x :: rest) :
    HT (σ := I.R) [] B (popS k) (Function.update B k rest) 1 :=
  HT.popS (σ := I.R) k B x rest hk []

theorem ht_pushNat (k : LM) (c : ℕ) (B : LM → List Sym) (hk : B k = []) :
    HT (σ := I.R) [] B (pushNat k c) (Function.update B k (natSyms c)) (bitLen c + 1) := by
  have h := HT.pushNat (σ := I.R) k c B []
  rw [hk, List.append_nil] at h
  exact h

theorem ht_skip (B : LM → List Sym) : HT (σ := I.R) [] B (hskip I) B 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨_, 1, Eval.load [] id v S, rfl, le_rfl⟩

end Rules

/-! ## 5. Counted loops and their cost -/

section Loops

variable {σ : Type}

/-- **Counted loop rule** with the body needed only for the iterations that run (`i < N`)
(the rule `HT.cdLoop'` of `Machine/FFT/PhaseBase.lean`, restated on `LM`). -/
theorem ht_cdLoop {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ} (hz : SpecIsZero Iz Cz)
    (hd : SpecDec Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R) (ctr dflt : LM)
    (rc : List Sym) (hrc : TermOK rc) (St : ℕ → LM → List Sym)
    (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : Prog LM (fun _ => Sym) σ)
    (cb : ℕ → ℕ) (N : ℕ)
    (hbody : ∀ i, i < N →
      HT [] (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) (cb i)) :
    HT [] (St N) (cdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) N) := by
  have hcap : 4 + 1 ≤ 2 + 24 := by decide
  have htest : ∀ i, Triple [] (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i =>
    callI_same Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i)) []
  have h0 : Triple [] (fun s => s.stk = St N) (callI Iz [ctr] dflt lz)
      (fun s => N ≤ N ∧ s.stk = St N ∧ Iz.obs (lz.get s.var) = decide (N = 0)) Cz :=
    Triple.post (htest N) (fun s hs => ⟨le_rfl, hs.1, hs.2⟩)
  refine Triple.seq h0 ?_
  have hloop := Triple.loop (ρ := []) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun k s => k ≤ N ∧ s.stk = St k ∧ Iz.obs (lz.get s.var) = decide (k = 0))
    (B := fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) ?_ ?_ ?_ N
  · exact Triple.post hloop (fun s hs => hs.2.1)
  · intro k
    by_cases hk : k < N
    · have hdec : HT [] (St (k + 1)) (callI Id [ctr] dflt ld)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
        HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (k + 1)) (.inl 0) _
          (hd k rc _ hrc (hSt (k + 1))) []
      have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
        zerosLead_le_length _
      have h1 := Triple.seq (Triple.seq hdec (hbody k hk)) (htest k)
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) ?_
      have : Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤
          Cd * (bitLen (k + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      show _ ≤ Cd * (bitLen (k + 1) + 1) + cb k + Cz
      omega
    · intro s hs
      exact absurd hs.1 (by omega)
  · intro k s hs
    simp [hs.2.2]
  · intro s hs
    simp [hs.2.2]

/-- Cost of a counted loop of `N ≤ B` rounds with bodies of cost at most `cb`. -/
theorem loop_cost (C B N cb : ℕ) (hN : N ≤ B) (f : ℕ → ℕ) (hf : ∀ i, i < N → f i ≤ cb) :
    C + loopCost (fun i => C * (bitLen (i + 1) + 1) + f i + C) N ≤
      (B + 1) * (cb + 3 * opY C B) := by
  have hL := loopCost_le_of_le (fun i => C * (bitLen (i + 1) + 1) + f i + C) (cb + 2 * opY C B)
    N (fun i hi => by
      have h1 := cost1_le (C := C) (bitLen_le (show i + 1 ≤ B by omega))
      have h2 := C_le_opY C B
      have h3 := hf i hi
      show C * (bitLen (i + 1) + 1) + f i + C ≤ cb + 2 * opY C B
      omega)
  have h1 : N * (cb + 2 * opY C B + 1) ≤ B * (cb + 3 * opY C B) :=
    Nat.mul_le_mul hN (by have := one_le_opY C B; omega)
  have h2 : (B + 1) * (cb + 3 * opY C B) = B * (cb + 3 * opY C B) + (cb + 3 * opY C B) :=
    Nat.succ_mul _ _
  have h3 := C_le_opY C B
  have h4 := one_le_opY C B
  omega

end Loops

/-! ## 6. Composite rules (stack form) -/

section CompRules

variable {I : HI} {C : ℕ}

theorem ht_rdF (hI : I.Spec C) (x : LM) (hx : [sH, x].Nodup) (B : LM → List Sym) (v : ℕ)
    (rest : List Sym) (hB : B sH = natSyms v ++ Sym.mark :: rest) (hx0 : B x = []) :
    HT [] B (rdF I x)
      (Function.update (Function.update (Function.update B x (natSyms v)) sH
        (Sym.mark :: rest)) sH rest)
      (C * (bitLen v + 1) + (C * (bitLen v + 1) + 1)) := by
  have hne : sH ≠ x := by simpa using hx
  exact (ht_cp0 hI sH x hx B v (Sym.mark :: rest) (termOK_mark _) hB hx0).seq
    ((ht_dr hI sH _ v (Sym.mark :: rest) (termOK_mark _)
      (by rw [Function.update_of_ne hne]; exact hB)).seq
    (ht_pop sH _ Sym.mark rest (by simp)))

theorem ht_wrF (hI : I.Spec C) (x dst : LM) (hx : [x, dst].Nodup) (B : LM → List Sym) (v : ℕ)
    (r P0 : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hd : B dst = P0) :
    HT [] B (wrF I x dst)
      (Function.update (Function.update B dst (Sym.mark :: P0)) dst
        (natSyms v ++ Sym.mark :: P0))
      (1 + C * (bitLen v + 1)) := by
  have hne : x ≠ dst := by simpa using hx
  exact (ht_push dst Sym.mark B P0 hd).seq
    (ht_cp hI x dst hx _ v r (Sym.mark :: P0) hr
      (by rw [Function.update_of_ne hne]; exact hB) (by simp))

theorem ht_mvF (hI : I.Spec C) (src dst : LM) (hsd : [src, dst].Nodup) (B : LM → List Sym)
    (v : ℕ) (rest P0 : List Sym) (hB : B src = natSyms v ++ Sym.mark :: rest)
    (hd : B dst = P0) :
    HT [] B (mvF I src dst)
      (Function.update (Function.update (Function.update (Function.update B dst
        (Sym.mark :: P0)) dst (natSyms v ++ Sym.mark :: P0)) src (Sym.mark :: rest)) src rest)
      (1 + (C * (bitLen v + 1) + (C * (bitLen v + 1) + 1))) := by
  have hne : src ≠ dst := by simpa using hsd
  exact (ht_push dst Sym.mark B P0 hd).seq
    ((ht_cp hI src dst hsd _ v (Sym.mark :: rest) (Sym.mark :: P0) (termOK_mark _)
      (by rw [Function.update_of_ne hne]; exact hB) (by simp)).seq
    ((ht_dr hI src _ v (Sym.mark :: rest) (termOK_mark _)
      (by rw [Function.update_of_ne hne, Function.update_of_ne hne]; exact hB)).seq
    (ht_pop src _ Sym.mark rest (by simp))))

theorem ht_addTo (hI : I.Spec C) (x y : LM) (hxy : [x, y, t1].Nodup) (B : LM → List Sym)
    (u v : ℕ) (ry : List Sym) (hry : TermOK ry) (hx : B x = natSyms u)
    (hy : B y = natSyms v ++ ry) (ht : B t1 = []) :
    HT [] B (addTo I x y)
      (Function.update (Function.update (Function.update (Function.update B t1
        (natSyms (u + v))) x []) x (natSyms (u + v))) t1 [])
      (C * (bitLen u + bitLen v + 1) + (C * (bitLen u + 1) +
        (C * (bitLen (u + v) + 1) + C * (bitLen (u + v) + 1)))) := by
  have hxt : x ≠ t1 := by intro h; simp [h] at hxy
  have hyt : y ≠ t1 := by intro h; simp [h] at hxy
  have hxy' : x ≠ y := by intro h; simp [h] at hxy
  exact (ht_ad0 hI x y t1 hxy B u v [] ry TermOK.nil hry (by rw [hx, List.append_nil]) hy ht).seq
    ((ht_dr hI x _ u [] TermOK.nil
      (by rw [Function.update_of_ne hxt, hx, List.append_nil])).seq
    ((ht_cp0 hI t1 x (by simp [List.nodup_cons, hxt.symm]) _ (u + v) [] TermOK.nil
      (by rw [Function.update_of_ne hxt.symm, Function.update_self, List.append_nil])
      (by simp)).seq
    (ht_dr hI t1 _ (u + v) [] TermOK.nil
      (by rw [Function.update_of_ne hxt.symm, Function.update_of_ne hxt.symm,
        Function.update_self, List.append_nil]))))

end CompRules

theorem two_le_opY (C B : ℕ) : 2 ≤ opY C B := by unfold opY; omega

/-! ## 7. Record-form blocks shared by both builders -/

section Blocks

variable {I : HI} {C : ℕ}

/-- Block A: read the five leading header fields `q, D, ℓ, K, w`. -/
def blockA (I : HI) : HP I :=
  (rdF I vq).seq ((rdF I vD).seq ((rdF I vl).seq ((rdF I vK).seq (rdF I vw))))

theorem ht_blockA (hI : I.Spec C) (M : MS) (q D ℓ K w B : ℕ) (H0 : List Sym)
    (hh : M.h = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0)))))
    (hq : M.q = []) (hD : M.D = []) (hl : M.l = []) (hK : M.K = []) (hw : M.w = [])
    (hqB : q ≤ B) (hDB : D ≤ B) (hlB : ℓ ≤ B) (hKB : K ≤ B) (hwB : w ≤ B) :
    HT [] (toF M) (blockA I)
      (toF {M with
        h := H0, q := natSyms q, D := natSyms D, l := natSyms ℓ, K := natSyms K,
        w := natSyms w}) (15 * opY C B) := by
  unfold blockA
  refine HT.of_eq
    ((ht_rdF hI vq (by decide) _ q
        (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark ::
          (natSyms w ++ Sym.mark :: H0)))) (by simp [toF, hh]) (by simp [toF, hq])).seq
    ((ht_rdF hI vD (by decide) _ D
        (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0)))
        (by simp) (by simp [toF, hD])).seq
    ((ht_rdF hI vl (by decide) _ ℓ (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H0))
        (by simp) (by simp [toF, hl])).seq
    ((ht_rdF hI vK (by decide) _ K (natSyms w ++ Sym.mark :: H0) (by simp)
        (by simp [toF, hK])).seq
    (ht_rdF hI vw (by decide) _ w H0 (by simp) (by simp [toF, hw]))))))
    ?_ ?_
  · simp only [upd_h, upd_q, upd_D, upd_l, upd_K, upd_w]
  · have c1 := cost1_le (C := C) (bitLen_le hqB)
    have c2 := cost1_le (C := C) (bitLen_le hDB)
    have c3 := cost1_le (C := C) (bitLen_le hlB)
    have c4 := cost1_le (C := C) (bitLen_le hKB)
    have c5 := cost1_le (C := C) (bitLen_le hwB)
    have c6 := one_le_opY C B
    omega

/-- Block D: push back the five leading header fields. -/
def blockD (I : HI) : HP I :=
  (wrF I vw sH).seq ((wrF I vK sH).seq ((wrF I vl sH).seq ((wrF I vD sH).seq (wrF I vq sH))))

theorem ht_blockD (hI : I.Spec C) (M : MS) (q D ℓ K w B : ℕ)
    (hq : M.q = natSyms q) (hD : M.D = natSyms D) (hl : M.l = natSyms ℓ)
    (hK : M.K = natSyms K) (hw : M.w = natSyms w)
    (hqB : q ≤ B) (hDB : D ≤ B) (hlB : ℓ ≤ B) (hKB : K ≤ B) (hwB : w ≤ B) :
    HT [] (toF M) (blockD I)
      (toF {M with h := natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++
        Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: M.h))))})
      (10 * opY C B) := by
  unfold blockD
  refine HT.of_eq
    ((ht_wrF hI vw sH (by decide) _ w [] M.h TermOK.nil (by simp [toF, hw])
        (by simp [toF])).seq
    ((ht_wrF hI vK sH (by decide) _ K [] (natSyms w ++ Sym.mark :: M.h) TermOK.nil
        (by simp [toF, hK]) (by simp)).seq
    ((ht_wrF hI vl sH (by decide) _ ℓ []
        (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: M.h)) TermOK.nil
        (by simp [toF, hl]) (by simp)).seq
    ((ht_wrF hI vD sH (by decide) _ D []
        (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: M.h)))
        TermOK.nil (by simp [toF, hD]) (by simp)).seq
    (ht_wrF hI vq sH (by decide) _ q []
        (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark ::
          (natSyms w ++ Sym.mark :: M.h)))) TermOK.nil (by simp [toF, hq]) (by simp))))))
    ?_ ?_
  · simp only [upd_h]
  · have c1 := cost1_le (C := C) (bitLen_le hqB)
    have c2 := cost1_le (C := C) (bitLen_le hDB)
    have c3 := cost1_le (C := C) (bitLen_le hlB)
    have c4 := cost1_le (C := C) (bitLen_le hKB)
    have c5 := cost1_le (C := C) (bitLen_le hwB)
    have c6 := one_le_opY C B
    omega

/-- Save the header's top field (whose number is on `vA`) on `sv` and remove it. -/
def saveP (I : HI) : HP I :=
  (pushS sv Sym.mark).seq ((hcp I vA sv).seq ((hdr I vA).seq ((hdr I sH).seq (popS sH))))

/-- One element of a pass: `vA := a`, the body, save the field. -/
def elemP (I : HI) (bd : HP I) : HP I := (hcp I sH vA).seq (bd.seq (saveP I))

/-- A pass over the `D` axis exponents of the header, with body `bd`. -/
def passB (I : HI) (bd : HP I) : HP I := (hcp I vD cnt).seq (hcd I cnt (elemP I bd))

/-- Restore the header from the saved fields. -/
def passC (I : HI) : HP I := (hcp I vD cnt).seq (hcd I cnt (mvF I sv sH))

/-- Move the emitted fields from `so` onto the destination. -/
def moveO (I : HI) : HP I := (hcp I vm cnt).seq (hcd I cnt (mvF I so sP))

theorem closed_passB (bd : HP I) (hb : bd.Closed) : (passB I bd).Closed := by
  unfold passB elemP saveP
  repeat' (first
    | exact callI_closed _ _ _ _
    | exact trivial
    | exact hb
    | refine closed_hcd _ _ _ ?_
    | refine WP.W9comp.closed_seq ?_ ?_)

theorem closed_passC : (passC I).Closed :=
  WP.W9comp.closed_seq (callI_closed _ _ _ _) (closed_hcd _ _ _ (closed_mvF _ _ _))

theorem closed_moveO : (moveO I).Closed :=
  WP.W9comp.closed_seq (callI_closed _ _ _ _) (closed_hcd _ _ _ (closed_mvF _ _ _))

theorem ht_saveP (hI : I.Spec C) (M : MS) (x B : ℕ) (rest : List Sym)
    (hh : M.h = natSyms x ++ Sym.mark :: rest) (hA : M.A = natSyms x) (hxB : x ≤ B) :
    HT [] (toF M) (saveP I) (toF {M with h := rest, A := [], s := natSyms x ++ Sym.mark :: M.s})
      (4 * opY C B) := by
  unfold saveP
  refine HT.of_eq
    ((ht_push sv Sym.mark _ M.s (by simp [toF])).seq
    ((ht_cp hI vA sv (by decide) _ x [] (Sym.mark :: M.s) TermOK.nil (by simp [toF, hA])
        (by simp)).seq
    ((ht_dr hI vA _ x [] TermOK.nil (by simp [toF, hA])).seq
    ((ht_dr hI sH _ x (Sym.mark :: rest) (termOK_mark _) (by simp [toF, hh])).seq
    (ht_pop sH _ Sym.mark rest (by simp))))))
    ?_ ?_
  · simp only [upd_h, upd_A, upd_s]
  · have c1 := cost1_le (C := C) (bitLen_le hxB)
    have c5 := two_le_opY C B
    omega

/-- The state of a pass when its counter is `i` (`D - i` elements processed). -/
def stB (R : ℕ → MS) (as : List ℕ) (H0 : List Sym) (D i : ℕ) : LM → List Sym :=
  toF {R (D - i) with
    h := hdrSyms (as.drop (D - i)) ++ H0, A := [],
    s := savedF (as.take (D - i)), c := natSyms i ++ []}

/-- **A pass over the axis exponents**: element `j` runs `bd` with `vA = a_j`, taking the other
fields from `R j` to `R (j+1)`; the header ends with its exponent fields saved on `sv`. -/
theorem ht_passB (hI : I.Spec C) (bd : HP I) (as : List ℕ) (D B cb : ℕ) (H0 : List Sym)
    (R : ℕ → MS) (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B)
    (hR0 : (R 0).D = natSyms D)
    (hbd : ∀ j (hj : j < as.length) (i : ℕ), HT []
      (toF {R j with
        h := natSyms as[j] ++ Sym.mark :: (hdrSyms (as.drop (j + 1)) ++ H0),
        A := natSyms as[j], s := savedF (as.take j), c := natSyms i ++ []}) bd
      (toF {R (j + 1) with
        h := natSyms as[j] ++ Sym.mark :: (hdrSyms (as.drop (j + 1)) ++ H0),
        A := natSyms as[j], s := savedF (as.take j), c := natSyms i ++ []}) cb) :
    HT [] (toF {R 0 with h := hdrSyms as ++ H0, A := [], s := [], c := []}) (passB I bd)
      (toF {R D with h := H0, A := [], s := savedF as, c := []})
      ((B + 1) * (cb + 10 * opY C B)) := by
  unfold passB hcd
  have hc0 := HT.of_eq (ht_cp0 hI vD cnt (by decide)
      (toF {R 0 with h := hdrSyms as ++ H0, A := [], s := [], c := []}) D [] TermOK.nil
      (by simp [toF, hR0]) (by simp [toF]))
    (show _ = stB R as H0 D D by
      simp only [upd_c, stB, Nat.sub_self, List.drop_zero, List.take_zero, savedF_nil,
        List.append_nil])
    le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc cnt d0 [] TermOK.nil (stB R as H0 D)
    (fun i => by simp [stB, toF]) (elemP I bd) (fun _ => cb + 6 * opY C B) D (by
      intro i hi
      have hjl : D - (i + 1) < as.length := by omega
      have hj : D - i = D - (i + 1) + 1 := by omega
      have hxj := hxB _ (List.getElem_mem hjl)
      simp only [stB, upd_c]
      rw [hj, drop_hdr' as _ hjl H0, savedF_take_succ' as _ hjl]
      unfold elemP
      refine HT.of_eq
        ((HT.of_eq (ht_cp0 hI sH vA (by decide) _ as[D - (i + 1)]
            (Sym.mark :: (hdrSyms (as.drop (D - (i + 1) + 1)) ++ H0)) (termOK_mark _)
            (by simp [toF]) (by simp [toF]))
          (by rw [upd_A]) le_rfl).seq
        ((hbd (D - (i + 1)) hjl i).seq
        (ht_saveP hI _ as[D - (i + 1)] B (hdrSyms (as.drop (D - (i + 1) + 1)) ++ H0) rfl rfl
          hxj)))
        ?_ ?_
      · rfl
      · have c1 := cost1_le (C := C) (bitLen_le hxj)
        omega)
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stB, Nat.sub_zero, List.drop_of_length_le (le_of_eq hlen),
      List.take_of_length_le (le_of_eq hlen), hdrSyms_nil', List.nil_append, natSyms_zero',
      List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hDB)
    refine le_trans (Nat.add_le_add c1 (loop_cost C B D _ hDB _ (fun i _ => le_rfl))) ?_
    have h1 : (B + 1) * (cb + 10 * opY C B) =
        (B + 1) * (cb + 6 * opY C B + 3 * opY C B) + (B + 1) * opY C B := by ring
    have h2 : opY C B ≤ (B + 1) * opY C B := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The state of the restoring pass when its counter is `i` (`i` saved fields left). -/
def stC (M : MS) (as : List ℕ) (H0 : List Sym) (i : ℕ) : LM → List Sym :=
  toF {M with h := hdrSyms (as.drop i) ++ H0, s := savedF (as.take i), c := natSyms i ++ []}

/-- **Restoring pass**: the saved exponent fields move back onto the header. -/
theorem ht_passC (hI : I.Spec C) (M : MS) (as : List ℕ) (D B : ℕ) (H0 : List Sym)
    (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B) (hD : M.D = natSyms D)
    (hc : M.c = []) :
    HT [] (toF {M with h := H0, s := savedF as}) (passC I)
      (toF {M with h := hdrSyms as ++ H0, s := [], c := []}) ((B + 1) * (8 * opY C B)) := by
  unfold passC hcd
  have hc0 := HT.of_eq (ht_cp0 hI vD cnt (by decide) (toF {M with h := H0, s := savedF as}) D []
      TermOK.nil (by simp [toF, hD]) (by simp [toF, hc]))
    (show _ = stC M as H0 D by
      simp only [upd_c, stC, List.drop_of_length_le (le_of_eq hlen),
        List.take_of_length_le (le_of_eq hlen), hdrSyms_nil', List.nil_append, List.append_nil])
    le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc cnt d0 [] TermOK.nil (stC M as H0)
    (fun i => by simp [stC, toF]) (mvF I sv sH) (fun _ => 3 * opY C B) D (by
      intro i hi
      have hil : i < as.length := by omega
      have hxi := hxB _ (List.getElem_mem hil)
      simp only [stC, upd_c]
      rw [savedF_take_succ' as _ hil, drop_hdr' as _ hil H0]
      refine HT.of_eq (ht_mvF hI sv sH (by decide) _ as[i] (savedF (as.take i))
        (hdrSyms (as.drop (i + 1)) ++ H0) (by simp [toF]) (by simp [toF])) ?_ ?_
      · simp only [upd_h, upd_s]
      · have c1 := cost1_le (C := C) (bitLen_le hxi)
        have c2 := two_le_opY C B
        omega)
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stC, List.drop_zero, List.take_zero, savedF_nil, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hDB)
    refine le_trans (Nat.add_le_add c1 (loop_cost C B D _ hDB _ (fun i _ => le_rfl))) ?_
    have h1 : (B + 1) * (8 * opY C B) =
        (B + 1) * (3 * opY C B + 3 * opY C B) + (B + 1) * (2 * opY C B) := by ring
    have h2 : opY C B ≤ (B + 1) * (2 * opY C B) := by nlinarith [one_le_opY C B]
    omega

/-- The state of the final move when its counter is `i` (`i` emitted fields left). -/
def stO (M : MS) (L : List ℕ) (P0 : List Sym) (i : ℕ) : LM → List Sym :=
  toF {M with p := hdrSyms (L.drop i) ++ P0, o := savedF (L.take i), c := natSyms i ++ []}

/-- **Final move**: the emitted fields (`savedF L` on `so`) move onto the destination. -/
theorem ht_moveO (hI : I.Spec C) (M : MS) (L : List ℕ) (N B : ℕ) (P0 : List Sym)
    (hlen : L.length = N) (hNB : N ≤ B) (hxB : ∀ x ∈ L, x ≤ B) (hm : M.m = natSyms N)
    (hc : M.c = []) :
    HT [] (toF {M with p := P0, o := savedF L}) (moveO I)
      (toF {M with p := hdrSyms L ++ P0, o := [], c := []}) ((B + 1) * (8 * opY C B)) := by
  unfold moveO hcd
  have hc0 := HT.of_eq (ht_cp0 hI vm cnt (by decide) (toF {M with p := P0, o := savedF L}) N []
      TermOK.nil (by simp [toF, hm]) (by simp [toF, hc]))
    (show _ = stO M L P0 N by
      simp only [upd_c, stO, List.drop_of_length_le (le_of_eq hlen),
        List.take_of_length_le (le_of_eq hlen), hdrSyms_nil', List.nil_append, List.append_nil])
    le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc cnt d0 [] TermOK.nil (stO M L P0)
    (fun i => by simp [stO, toF]) (mvF I so sP) (fun _ => 3 * opY C B) N (by
      intro i hi
      have hil : i < L.length := by omega
      have hxi := hxB _ (List.getElem_mem hil)
      simp only [stO, upd_c]
      rw [savedF_take_succ' L _ hil, drop_hdr' L _ hil P0]
      refine HT.of_eq (ht_mvF hI so sP (by decide) _ L[i] (savedF (L.take i))
        (hdrSyms (L.drop (i + 1)) ++ P0) (by simp [toF]) (by simp [toF])) ?_ ?_
      · simp only [upd_p, upd_o]
      · have c1 := cost1_le (C := C) (bitLen_le hxi)
        have c2 := two_le_opY C B
        omega)
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stO, List.drop_zero, List.take_zero, savedF_nil, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hNB)
    refine le_trans (Nat.add_le_add c1 (loop_cost C B N _ hNB _ (fun i _ => le_rfl))) ?_
    have h1 : (B + 1) * (8 * opY C B) =
        (B + 1) * (3 * opY C B + 3 * opY C B) + (B + 1) * (2 * opY C B) := by ring
    have h2 : opY C B ≤ (B + 1) * (2 * opY C B) := by nlinarith [one_le_opY C B]
    omega

end Blocks

end SubNLogN.Machine.FFT.LayoutMapAux
