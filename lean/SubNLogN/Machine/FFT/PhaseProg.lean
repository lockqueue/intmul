/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PhaseBase

/-!
# K4-TW (`Machine/FFT/PhaseProg.lean`): the phase-table builder's host, instances and wrappers

**Scope (honest summary).** Definitions and host rules, all proved (no `sorry`):
* `PL = Loc 3 32`: the builder's stacks. This is the same type as the contract layout
  `KLoc (Fin 3) (Fin 32)` of `PhaseTableMachineStmt`: named `.inl 0, 1, 2`, private scratch
  `.inr 0 … .inr 31`.
* `PI`: the eleven proved contract instances the builder calls (W3 copy/drop/isZero/dec/add/sub,
  `shlConst 1`, `shlVar`, `shrVar`, `cmpNat`; W7 `stdChar` at `neg = false`), `PI.Spec` their
  bodies at one shared constant, lenses `PI.l…` into the host registers `PI.R`.
* Wrappers `pcp … psf`, `pcd` (count-down loop) and their host rules `HT.pcp …`.
* Stack names of the builder, and the update-chain normalisation lemmas `pupd_swap`,
  `pupd_eq_self_of` (the method of `WP/W7k2/B/Base.lean`).
-/

namespace SubNLogN.Machine.FFT.Phase

open TMFw TMFw.Contracts WP.W7k2

/-- The builder's stacks: the contract's named stacks `.inl 0, 1, 2` and 32 private scratch
stacks. -/
abbrev PL := Loc 3 32

/-! ## Update chains -/

/-- A numbering of the host stacks, used to sort update chains. -/
def pidx : PL → ℕ
  | .inl i => i.val
  | .inr j => 3 + j.val

theorem pupd_swap {f : PL → List Sym} {a b : PL} (v w : List Sym) (h : pidx b < pidx a) :
    Function.update (Function.update f a v) b w = Function.update (Function.update f b w) a v := by
  have hne : a ≠ b := fun e => by rw [e] at h; exact lt_irrefl _ h
  exact Function.update_comm hne v w f

theorem pupd_eq_self_of {f : PL → List Sym} {a : PL} {v : List Sym} (h : ValEq (f a) v) :
    Function.update f a v = f := by
  unfold ValEq at h
  rw [← h]
  exact Function.update_eq_self a f

/-! ## Stack names -/

/-- Header stack (contract stack `1`). -/
abbrev sH : PL := .inl 1
/-- Table stack (contract stack `2`). -/
abbrev sT : PL := .inl 2
abbrev vq : PL := .inr 0
abbrev vl : PL := .inr 1
abbrev vw : PL := .inr 2
abbrev vq6 : PL := .inr 3
abbrev vq3 : PL := .inr 4
abbrev vq11 : PL := .inr 5
abbrev vP : PL := .inr 6
abbrev vPw : PL := .inr 7
abbrev vden : PL := .inr 8
abbrev ctr : PL := .inr 9
abbrev pk : PL := .inr 10
abbrev tA : PL := .inr 11
abbrev tB : PL := .inr 12
abbrev tC : PL := .inr 13
abbrev tR : PL := .inr 14
abbrev tU : PL := .inr 15
abbrev x1 : PL := .inr 16
abbrev x2 : PL := .inr 17
abbrev fF : PL := .inr 18
abbrev uU : PL := .inr 19
abbrev wc : PL := .inr 20
/-- Default stack of `callMap` (never used: all call lists are in range). -/
abbrev pd0 : PL := .inl 0

/-! ## The instance bundle -/

/-- The builder's contract instances. -/
structure PI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  sb : Inst 3 4 Unit
  s1 : Inst 1 4 Unit
  sv : Inst 2 4 Unit
  rv : Inst 2 4 Unit
  cm : Inst 2 4 Ordering
  sf : Inst 4 16 Unit

namespace PI

variable (I : PI)

/-- Host registers: a symbol register, then one register file per instance. -/
abbrev R : Type :=
  Option Sym × I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ad.R × I.sb.R × I.s1.R × I.sv.R × I.rv.R ×
    I.cm.R × I.sf.R

def lS : Lens I.R (Option Sym) := Lens.fst _ _
def lcp : Lens I.R I.cp.R := (Lens.fst _ _).sc
def ldr : Lens I.R I.dr.R := (Lens.fst _ _).sc.sc
def liz : Lens I.R I.iz.R := (Lens.fst _ _).sc.sc.sc
def ldc : Lens I.R I.dc.R := (Lens.fst _ _).sc.sc.sc.sc
def lad : Lens I.R I.ad.R := (Lens.fst _ _).sc.sc.sc.sc.sc
def lsb : Lens I.R I.sb.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc
def ls1 : Lens I.R I.s1.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc
def lsv : Lens I.R I.sv.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc
def lrv : Lens I.R I.rv.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc
def lcm : Lens I.R I.cm.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lsf : Lens I.R I.sf.R := (Lens.snd _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc

theorem R_finite : Finite I.R := by
  have := I.cp.fin; have := I.dr.fin; have := I.iz.fin; have := I.dc.fin; have := I.ad.fin
  have := I.sb.fin; have := I.s1.fin; have := I.sv.fin; have := I.rv.fin; have := I.cm.fin
  have := I.sf.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  have := I.cp.ne; have := I.dr.ne; have := I.iz.ne; have := I.dc.ne; have := I.ad.ne
  have := I.sb.ne; have := I.s1.ne; have := I.sv.ne; have := I.rv.ne; have := I.cm.ne
  have := I.sf.ne
  infer_instance

/-- All eleven contract bodies, with one shared constant `C`. -/
structure Spec (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ad : SpecAddNat I.ad C
  sb : SpecSubNat I.sb C
  s1 : SpecShlConst 1 I.s1 C
  sv : SpecShlVar I.sv C
  rv : SpecShrVar I.rv C
  cm : SpecCmpNat I.cm C
  sf : SpecStdChar false I.sf C

end PI

/-- Builder programs. -/
abbrev PP (I : PI) : Type := Prog PL (fun _ => Sym) I.R

/-! ## Calls on host stacks -/

section Wrappers

variable (I : PI)

def pcp (x y : PL) : PP I := callI I.cp [x, y] pd0 I.lcp
def pdr (x : PL) : PP I := callI I.dr [x] pd0 I.ldr
def piz (x : PL) : PP I := callI I.iz [x] pd0 I.liz
def pdc (x : PL) : PP I := callI I.dc [x] pd0 I.ldc
def pad (x y z : PL) : PP I := callI I.ad [x, y, z] pd0 I.lad
def psb (x y z : PL) : PP I := callI I.sb [x, y, z] pd0 I.lsb
def ps1 (x : PL) : PP I := callI I.s1 [x] pd0 I.ls1
def psv (x c : PL) : PP I := callI I.sv [x, c] pd0 I.lsv
def prv (x c : PL) : PP I := callI I.rv [x, c] pd0 I.lrv
def pcm (x y : PL) : PP I := callI I.cm [x, y] pd0 I.lcm
def psf (q n d z : PL) : PP I := callI I.sf [q, n, d, z] pd0 I.lsf

/-- Count-down loop on `c` (`while c ≠ 0 do (dec c; body)`). -/
def pcd (c : PL) (body : PP I) : PP I := cdLoop I.iz I.dc I.liz I.ldc c pd0 body

/-- Emit the `w`-bit field of the number on `X` onto `fF` (counter `wc`, width on `vw`). -/
def pemit (X : PL) : PP I := emitBits I.cp I.iz I.dc I.lS I.lcp I.liz I.ldc vw wc X fF pd0

/-- `y += x + c`, using the temporary `t`. -/
def paddC (x : PL) (c : ℕ) (t y : PL) : PP I := (pushNat t c).seq ((pad I x t y).seq (pdr I t))

/-- `y += 2^c` (the exponent `c` on stack `cs`). -/
def ppow2 (cs y : PL) : PP I := (pushNat y 1).seq (psv I y cs)

end Wrappers

/-! ## Host rules -/

section Rules

variable {I : PI} {C : ℕ}

theorem HT.pcp (hI : I.Spec C) (x y : PL) (hxy : [x, y].Nodup) (B : PL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (pcp I x y) (Function.update B y (natSyms v ++ B y)) (C * (bitLen v + 1)) :=
  HT.copyNat hI.cp pd0 I.lcp x y hxy (by decide) B v r hr hB []

theorem HT.pdr (hI : I.Spec C) (x : PL) (B : PL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (pdr I x) (Function.update B x r) (C * (bitLen v + 1)) :=
  HT.dropNat hI.dr pd0 I.ldr x (by decide) B v r hr hB []

theorem HT.pdc (hI : I.Spec C) (x : PL) (B : PL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms (v + 1) ++ r) :
    HT [] B (pdc I x) (Function.update B x (natSyms v ++ r)) (C * (bitLen (v + 1) + 1)) :=
  (HT.callI_upd I.dc [x] pd0 (List.nodup_singleton _) rfl (by decide) I.ldc B (.inl 0) _
    (hI.dc v r _ hr hB) []).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (zerosLead_le_length _) 1))

theorem HT.pad (hI : I.Spec C) (x y z : PL) (hnd : [x, y, z].Nodup) (B : PL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) :
    HT [] B (pad I x y z) (Function.update B z (natSyms (u + v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.addNat hI.ad pd0 I.lad x y z hnd (by decide) B u v ru rv hru hrv hx hy []

theorem HT.psb (hI : I.Spec C) (x y z : PL) (hnd : [x, y, z].Nodup) (B : PL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv) (hvu : v ≤ u)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) :
    HT [] B (psb I x y z) (Function.update B z (natSyms (u - v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.subNat hI.sb pd0 I.lsb x y z hnd (by decide) B u v ru rv hru hrv hvu hx hy []

theorem HT.ps1 (hI : I.Spec C) (x : PL) (B : PL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (ps1 I x) (Function.update B x (natSyms (v * 2 ^ 1) ++ r)) (C * (1 + 1)) :=
  HT.shlConst hI.s1 pd0 I.ls1 x (by decide) B v r hr hB []

theorem HT.psv (hI : I.Spec C) (x c : PL) (hnd : [x, c].Nodup) (B : PL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) :
    HT [] B (psv I x c) (Function.update B x (natSyms (u * 2 ^ v) ++ ru))
      (C * (v + bitLen v + 1)) :=
  HT.shlVar hI.sv pd0 I.lsv x c hnd (by decide) B u v ru rv hru hrv hx hc []

theorem HT.prv (hI : I.Spec C) (x c : PL) (hnd : [x, c].Nodup) (B : PL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) :
    HT [] B (prv I x c) (Function.update B x (natSyms (u / 2 ^ v) ++ ru))
      (C * (min v (bitLen u) + bitLen v + 1)) :=
  HT.shrVar hI.rv pd0 I.lrv x c hnd (by decide) B u v ru rv hru hrv hx hc []

theorem HT.pcmIte (hI : I.Spec C) (x y : PL) (hnd : [x, y].Nodup) (B B' : PL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (f : Ordering → Bool)
    (p q : PP I) {T₁ T₂ : ℕ} (hp : f (Lib.ordOf u v) = true → HT [] B p B' T₁)
    (hq : f (Lib.ordOf u v) = false → HT [] B q B' T₂) :
    HT [] B ((pcm I x y).seq (.ite (fun s => f (I.cm.obs (I.lcm.get s))) p q)) B'
      (C * (bitLen u + bitLen v + 1) + (max T₁ T₂ + 1)) :=
  HT.cmpNat_ite hI.cm pd0 I.lcm x y hnd (by decide) B B' u v ru rv hru hrv hx hy f p q [] hp hq

theorem HT.pizIte (hI : I.Spec C) (x : PL) (B B' : PL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (p q : PP I) {T₁ T₂ : ℕ}
    (hp : v = 0 → HT [] B p B' T₁) (hq : v ≠ 0 → HT [] B q B' T₂) :
    HT [] B ((piz I x).seq (.ite (fun s => I.iz.obs (I.liz.get s)) p q)) B'
      (C + (max T₁ T₂ + 1)) :=
  HT.callI_test I.iz [x] pd0 (List.nodup_singleton _) rfl (by decide) I.liz B B' (fun b => b)
    (decide (v = 0)) (hI.iz v r _ hr hB) p q [] (fun h => hp (of_decide_eq_true h))
    (fun h => hq (of_decide_eq_false h))

theorem HT.psf (hI : I.Spec C) (sq sn sd z : PL) (hnd : [sq, sn, sd, z].Nodup)
    (B : PL → List Sym) (q num den : ℕ) (r0 r1 r2 : List Sym) (hden : 0 < den) (hnum : num ≤ den)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (e0 : B sq = natSyms q ++ r0)
    (e1 : B sn = natSyms num ++ r1) (e2 : B sd = natSyms den ++ r2) :
    HT [] B (psf I sq sn sd z)
      (Function.update B z
        (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den false).1 ++ B z))
      (C * (q + bitLen den + 1) ^ 4) :=
  HT.stdChar hI.sf pd0 I.lsf sq sn sd z hnd (by decide) B q num den r0 r1 r2 hden hnum h0 h1 h2
    e0 e1 e2 []

theorem HT.pemit (hI : I.Spec C) (X : PL) (hnd : [vw, wc, X, fF].Nodup) (B : PL → List Sym)
    (w N : ℕ) (rw rx : List Sym) (hrw : TermOK rw) (hrx : TermOK rx) (hwc : TermOK (B wc))
    (hvw : B vw = natSyms w ++ rw) (hX : B X = natSyms N ++ rx) (hN : N < 2 ^ w) :
    HT [] B (pemit I X)
      (Function.update (Function.update B X rx) fF
        ((SubNLogN.Machine.bitsLE w N).reverse.map Sym.bit ++ B fF))
      (emitCost C C C w) :=
  HT.emitBits hI.cp hI.iz hI.dc I.lS I.lcp I.liz I.ldc vw wc X fF pd0 hnd (by decide) B w N rw rx
    hrw hrx hwc hvw hX hN []

theorem HT.paddC (hI : I.Spec C) (x : PL) (c : ℕ) (t y : PL) (hnd : [x, t, y].Nodup)
    (B : PL → List Sym) (v : ℕ) (rx : List Sym) (hrx : TermOK rx) (hx : B x = natSyms v ++ rx)
    (ht : TermOK (B t)) :
    HT [] B (paddC I x c t y) (Function.update B y (natSyms (v + c) ++ B y))
      (bitLen c + 1 + (C * (bitLen v + bitLen c + 1) + C * (bitLen c + 1))) := by
  have hxt : x ≠ t := fun h => by simp [h] at hnd
  have hty : t ≠ y := fun h => by simp [h] at hnd
  refine (HT.seq (HT.pushNat t c B []) (HT.seq
    (HT.pad hI x t y hnd _ v c rx (B t) hrx ht (by simp [Function.update_apply, hxt, hx])
      (by simp))
    (HT.pdr hI t _ c (B t) ht (by simp [Function.update_apply, hty])))).of_eq ?_ le_rfl
  funext g
  by_cases hg : g = t
  · rw [hg]
    simp [Function.update_apply, hty]
  · simp [Function.update_apply, hg, hty.symm]

theorem HT.ppow2 (hI : I.Spec C) (c y : PL) (hnd : [y, c].Nodup) (B : PL → List Sym) (k : ℕ)
    (rc : List Sym) (hrc : TermOK rc) (hc : B c = natSyms k ++ rc) (hy : TermOK (B y)) :
    HT [] B (ppow2 I c y) (Function.update B y (natSyms (2 ^ k) ++ B y))
      (2 + C * (k + bitLen k + 1)) := by
  have hyc : y ≠ c := fun h => by simp [h] at hnd
  refine (HT.seq (HT.pushNat y 1 B []) (HT.psv hI y c hnd _ 1 k (B y) rc hy hrc (by simp)
    (by simp [hyc.symm, hc]))).of_eq ?_ (by rw [bitLen_one'])
  rw [Function.update_idem, one_mul]

theorem HT.pcd (hI : I.Spec C) (c : PL) (rc : List Sym) (hrc : TermOK rc)
    (St : ℕ → PL → List Sym) (hSt : ∀ i, St i c = natSyms i ++ rc) (body : PP I)
    (cb : ℕ → ℕ) (N : ℕ)
    (hbody : ∀ i, i < N →
      HT [] (Function.update (St (i + 1)) c (natSyms i ++ rc)) body (St i) (cb i)) :
    HT [] (St N) (pcd I c body) (St 0)
      (C + loopCost (fun i => C * (bitLen (i + 1) + 1) + cb i + C) N) :=
  HT.cdLoop' hI.iz hI.dc I.liz I.ldc c pd0 (by decide) rc hrc St hSt body cb [] N hbody

end Rules

end SubNLogN.Machine.FFT.Phase
