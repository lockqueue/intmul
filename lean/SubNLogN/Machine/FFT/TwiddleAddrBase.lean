/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PhaseBase
import SubNLogN.Machine.FFT.TwiddleAddrDefs

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrBase.lean`): host, instances and wrappers

**Scope (honest summary).** These are definitions and host rules for the twiddle-address routine
of `TwiddleAddrStmt` (`Machine/FFT/TwiddleAddrDefs.lean`). Everything is proved (no `sorry`):
* `TL = Loc 4 48`, the routine's stacks. This is the contract layout `KLoc (Fin 4) (Fin 48)`:
  named `.inl 0 … 3` (header, round `v`, record `n`, destination), private scratch
  `.inr 0 … .inr 47`.
* `TI`, the fourteen proved contract instances the routine calls: W3 copy, drop, isZero, dec, inc,
  add, sub, `shlConst 1`, `shrConst 1`, `shlVar`, `shrVar` and `cmpNat`; W5 `mulAt Mul`; and W6a
  `divModNat`. `TI.Spec Mul C KM` is their bodies at one shared constant `C`, together with
  `Mul w ≤ KM·(w+1)²`.
* Wrappers `tcp … tdm`, the conditionals `tcmIf`, `tizIf`, the count-down loop `tcd`, and the
  macros `tnm` (`z += x·y`), `accAdd` (`acc := x + acc`), `mvF`/`rsF` (park or unpark a header
  field). Each has a host rule. Every host rule charges the uniform unit
  `U C KM Q = C·(KM+2)·(Q+2)²`, provided the bit lengths involved are at most `Q`.

The program itself and its plan are in `Machine/FFT/TwiddleAddr.lean`.
-/

namespace SubNLogN.Machine.FFT.TwAddr

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine.FFT.Phase

/-- The routine's stacks: the contract's named stacks `.inl 0 … 3` and 48 private scratch stacks. -/
abbrev TL := Loc 4 48

/-! ## Update chains -/

/-- A numbering of the host stacks, used to sort update chains. -/
def tidx : TL → ℕ
  | .inl i => i.val
  | .inr j => 4 + j.val

theorem tupd_swap {f : TL → List Sym} {a b : TL} (v w : List Sym) (h : tidx b < tidx a) :
    Function.update (Function.update f a v) b w = Function.update (Function.update f b w) a v := by
  have hne : a ≠ b := fun e => by rw [e] at h; exact lt_irrefl _ h
  exact Function.update_comm hne v w f

theorem tupd_eq_self_of {f : TL → List Sym} {a : TL} {v : List Sym} (h : ValEq (f a) v) :
    Function.update f a v = f := by
  unfold ValEq at h
  rw [← h]
  exact Function.update_eq_self a f

/-! ## Stack names -/

/-- Header `midHdr q ℓ K w a` (contract stack `0`, restored). -/
abbrev sHd : TL := .inl 0
/-- Round index `v` (contract stack `1`, read only). -/
abbrev sV : TL := .inl 1
/-- Record index `n` (contract stack `2`, read only). -/
abbrev sN : TL := .inl 2
/-- Destination (contract stack `3`). -/
abbrev sOut : TL := .inl 3
/-- Park for header fields. -/
abbrev kPK : TL := .inr 0
abbrev kD : TL := .inr 1
abbrev kL : TL := .inr 2
abbrev kK : TL := .inr 3
abbrev kM : TL := .inr 4
abbrev kLc : TL := .inr 5
abbrev kM1 : TL := .inr 6
abbrev kL1 : TL := .inr 7
abbrev kL2 : TL := .inr 8
abbrev kB0 : TL := .inr 9
abbrev kB0D : TL := .inr 10
abbrev kDK : TL := .inr 11
abbrev kE : TL := .inr 12
abbrev kR : TL := .inr 13
abbrev kIx : TL := .inr 14
abbrev kC1 : TL := .inr 15
abbrev kAcc : TL := .inr 16
abbrev kIK : TL := .inr 17
abbrev xA : TL := .inr 18
abbrev xN : TL := .inr 19
abbrev xQ : TL := .inr 20
abbrev xP : TL := .inr 21
abbrev xB : TL := .inr 22
abbrev xLo : TL := .inr 23
abbrev kIb : TL := .inr 24
abbrev xK : TL := .inr 25
abbrev xU : TL := .inr 26
abbrev xV : TL := .inr 27
abbrev xF : TL := .inr 28
abbrev xG : TL := .inr 29
abbrev xM1 : TL := .inr 30
abbrev xM2 : TL := .inr 31
abbrev y1 : TL := .inr 32
abbrev y2 : TL := .inr 33
abbrev y3 : TL := .inr 34
abbrev y4 : TL := .inr 35
abbrev y5 : TL := .inr 36
abbrev y6 : TL := .inr 37
abbrev y7 : TL := .inr 38
abbrev xB2 : TL := .inr 39
abbrev xP2 : TL := .inr 40
/-- Default stack of `callMap` (never used: all call lists are in range). -/
abbrev td0 : TL := .inl 0

/-! ## The instance bundle -/

/-- The routine's contract instances. -/
structure TI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ic : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  sb : Inst 3 4 Unit
  s1 : Inst 1 4 Unit
  r1 : Inst 1 4 Unit
  sv : Inst 2 4 Unit
  rv : Inst 2 4 Unit
  cm : Inst 2 4 Ordering
  mu : Inst 3 8 Unit
  dm : Inst 4 6 Unit

namespace TI

variable (I : TI)

/-- Host registers: a symbol register, then one register file per instance. -/
abbrev R : Type :=
  Option Sym × I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ic.R × I.ad.R × I.sb.R × I.s1.R × I.r1.R ×
    I.sv.R × I.rv.R × I.cm.R × I.mu.R × I.dm.R

def lS : Lens I.R (Option Sym) := Lens.fst _ _
def lcp : Lens I.R I.cp.R := (Lens.fst _ _).sc
def ldr : Lens I.R I.dr.R := (Lens.fst _ _).sc.sc
def liz : Lens I.R I.iz.R := (Lens.fst _ _).sc.sc.sc
def ldc : Lens I.R I.dc.R := (Lens.fst _ _).sc.sc.sc.sc
def lic : Lens I.R I.ic.R := (Lens.fst _ _).sc.sc.sc.sc.sc
def lad : Lens I.R I.ad.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc
def lsb : Lens I.R I.sb.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc
def ls1 : Lens I.R I.s1.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc
def lr1 : Lens I.R I.r1.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc
def lsv : Lens I.R I.sv.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lrv : Lens I.R I.rv.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lcm : Lens I.R I.cm.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lmu : Lens I.R I.mu.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def ldm : Lens I.R I.dm.R := (Lens.snd _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc

theorem R_finite : Finite I.R := by
  have := I.cp.fin; have := I.dr.fin; have := I.iz.fin; have := I.dc.fin; have := I.ic.fin
  have := I.ad.fin; have := I.sb.fin; have := I.s1.fin; have := I.r1.fin; have := I.sv.fin
  have := I.rv.fin; have := I.cm.fin; have := I.mu.fin; have := I.dm.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  have := I.cp.ne; have := I.dr.ne; have := I.iz.ne; have := I.dc.ne; have := I.ic.ne
  have := I.ad.ne; have := I.sb.ne; have := I.s1.ne; have := I.r1.ne; have := I.sv.ne
  have := I.rv.ne; have := I.cm.ne; have := I.mu.ne; have := I.dm.ne
  infer_instance

/-- All fourteen contract bodies, with one shared constant `C`, and the multiplier's quadratic
cost bound `Mul w ≤ KM·(w+1)²`. -/
structure Spec (Mul : ℕ → ℕ) (C KM : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ic : SpecInc I.ic C
  ad : SpecAddNat I.ad C
  sb : SpecSubNat I.sb C
  s1 : SpecShlConst 1 I.s1 C
  r1 : SpecShrConst 1 I.r1 C
  sv : SpecShlVar I.sv C
  rv : SpecShrVar I.rv C
  cm : SpecCmpNat I.cm C
  mu : SpecMul Mul I.mu C
  dm : SpecDivMod I.dm C
  mq : ∀ w, Mul w ≤ KM * (w + 1) ^ 2

end TI

/-- Routine programs. -/
abbrev TP (I : TI) : Type := Prog TL (fun _ => Sym) I.R

/-! ## Calls on host stacks -/

section Wrappers

variable (I : TI)

def tcp (x y : TL) : TP I := callI I.cp [x, y] td0 I.lcp
def tdr (x : TL) : TP I := callI I.dr [x] td0 I.ldr
def tiz (x : TL) : TP I := callI I.iz [x] td0 I.liz
def tdc (x : TL) : TP I := callI I.dc [x] td0 I.ldc
def tic (x : TL) : TP I := callI I.ic [x] td0 I.lic
def tad (x y z : TL) : TP I := callI I.ad [x, y, z] td0 I.lad
def tsb (x y z : TL) : TP I := callI I.sb [x, y, z] td0 I.lsb
def ts1 (x : TL) : TP I := callI I.s1 [x] td0 I.ls1
def tr1 (x : TL) : TP I := callI I.r1 [x] td0 I.lr1
def tsv (x c : TL) : TP I := callI I.sv [x, c] td0 I.lsv
def trv (x c : TL) : TP I := callI I.rv [x, c] td0 I.lrv
def tcm (x y : TL) : TP I := callI I.cm [x, y] td0 I.lcm
def tmu (x y z : TL) : TP I := callI I.mu [x, y, z] td0 I.lmu
def tdm (x y q r : TL) : TP I := callI I.dm [x, y, q, r] td0 I.ldm

/-- Count-down loop on `c` (`while c ≠ 0 do (dec c; body)`). -/
def tcd (c : TL) (body : TP I) : TP I := cdLoop I.iz I.dc I.liz I.ldc c td0 body

/-- Do nothing. -/
def tskip : TP I := .load id

/-- `if f (compare x y) then p else q`. -/
def tcmIf (x y : TL) (f : Ordering → Bool) (p q : TP I) : TP I :=
  (tcm I x y).seq (.ite (fun s => f (I.cm.obs (I.lcm.get s))) p q)

/-- `if x = 0 then p else q`. -/
def tizIf (x : TL) (p q : TP I) : TP I :=
  (tiz I x).seq (.ite (fun s => I.iz.obs (I.liz.get s)) p q)

/-- `z += x·y` for naturals, through the signed multiplier (temporaries `xM1`, `xM2`). -/
def tnm (x y z : TL) : TP I :=
  (tcp I x xM1).seq <| (WP.W7k2.pushS xM1 .pos).seq <| (tcp I y xM2).seq <|
  (WP.W7k2.pushS xM2 .pos).seq <| (tmu I xM1 xM2 z).seq <| (WP.W7k2.popS z).seq <|
  (WP.W7k2.popS xM1).seq <| (tdr I xM1).seq <| (WP.W7k2.popS xM2).seq <| tdr I xM2

/-- `acc := x + acc` (temporary `xN`). -/
def accAdd (x acc : TL) : TP I :=
  (tad I x acc xN).seq <| (tdr I acc).seq <| (tcp I xN acc).seq (tdr I xN)

/-- Move a header field (`natSyms f ++ mark`) from `src` to `dst` (`mark` on top of `dst`). -/
def mvF (src dst : TL) : TP I :=
  (tcp I src dst).seq ((tdr I src).seq ((WP.W7k2.popS src).seq (WP.W7k2.pushS dst Sym.mark)))

/-- Move a parked field back from `dst` to `src` (inverse of `mvF`). -/
def rsF (src dst : TL) : TP I :=
  (WP.W7k2.popS dst).seq ((WP.W7k2.pushS src Sym.mark).seq ((tcp I dst src).seq (tdr I dst)))

theorem tnm_closed (x y z : TL) : (tnm I x y z).Closed :=
  ⟨callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _⟩

theorem accAdd_closed (x acc : TL) : (accAdd I x acc).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem mvF_closed (src dst : TL) : (mvF I src dst).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, trivial, trivial⟩

theorem rsF_closed (src dst : TL) : (rsF I src dst).Closed :=
  ⟨trivial, trivial, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem tcmIf_closed (x y : TL) (f : Ordering → Bool) (p q : TP I) (hp : p.Closed)
    (hq : q.Closed) : (tcmIf I x y f p q).Closed :=
  ⟨callI_closed _ _ _ _, hp, hq⟩

theorem tizIf_closed (x : TL) (p q : TP I) (hp : p.Closed) (hq : q.Closed) :
    (tizIf I x p q).Closed :=
  ⟨callI_closed _ _ _ _, hp, hq⟩

theorem tcd_closed (c : TL) (body : TP I) (hb : body.Closed) : (tcd I c body).Closed :=
  cdLoop_closed _ _ _ _ _ _ _ hb

end Wrappers

/-! ## The uniform cost unit -/

/-- The uniform cost unit: every kernel call on numbers of bit length `≤ Q` costs at most this. -/
def U (C KM Q : ℕ) : ℕ := C * (KM + 2) * (Q + 2) ^ 2

theorem qb {x Q : ℕ} (h : x ≤ 2 * Q + 4) : x ≤ (Q + 2) ^ 2 := by nlinarith

theorem cU {C KM Q x : ℕ} (h : x ≤ (Q + 2) ^ 2) : C * x ≤ U C KM Q := by
  unfold U
  calc C * x ≤ C * (Q + 2) ^ 2 := Nat.mul_le_mul_left _ h
    _ ≤ C * ((KM + 2) * (Q + 2) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    _ = C * (KM + 2) * (Q + 2) ^ 2 := by ring

theorem C_le_U (C KM Q : ℕ) : C ≤ U C KM Q := by
  have := cU (C := C) (KM := KM) (Q := Q) (x := 1) (qb (by omega))
  simpa using this

theorem mulU {Mul : ℕ → ℕ} {C KM Q w : ℕ} (hM : ∀ w, Mul w ≤ KM * (w + 1) ^ 2) (hw : w ≤ Q) :
    C * Mul w + C ≤ U C KM Q := by
  have h1 : Mul w ≤ KM * (Q + 2) ^ 2 :=
    le_trans (hM w) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have h2 : 1 ≤ (Q + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold U
  calc C * Mul w + C ≤ C * (KM * (Q + 2) ^ 2) + C * (Q + 2) ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) (by simpa using Nat.mul_le_mul_left C h2)
    _ ≤ C * (KM + 2) * (Q + 2) ^ 2 := by nlinarith

theorem loopCost_le (B : ℕ → ℕ) (b : ℕ) : ∀ N, (∀ i, i < N → B i + 1 ≤ b) →
    loopCost B N ≤ N * b + 1
  | 0, _ => by simp [loopCost]
  | N + 1, h => by
    have ih := loopCost_le B b N (fun i hi => h i (by omega))
    have hN := h N (by omega)
    simp only [loopCost]
    rw [Nat.succ_mul]
    omega

/-! ## Host rules (uniform cost `U C KM Q`) -/

section Rules

variable {I : TI} {Mul : ℕ → ℕ} {C KM : ℕ}

theorem HT.tskip (B : TL → List Sym) : HT [] B (tskip I) B 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨⟨v, S⟩, 1, Eval.load [] id v S, rfl, le_rfl⟩

theorem HT.tcp (hI : I.Spec Mul C KM) (Q : ℕ) (x y : TL) (hxy : [x, y].Nodup)
    (B : TL → List Sym) (v : ℕ) (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r)
    (hv : bitLen v ≤ Q) :
    HT [] B (tcp I x y) (Function.update B y (natSyms v ++ B y)) (U C KM Q) :=
  (HT.copyNat hI.cp td0 I.lcp x y hxy (by decide) B v r hr hB []).mono (cU (qb (by omega)))

theorem HT.tdr (hI : I.Spec Mul C KM) (Q : ℕ) (x : TL) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hv : bitLen v ≤ Q) :
    HT [] B (tdr I x) (Function.update B x r) (U C KM Q) :=
  (HT.dropNat hI.dr td0 I.ldr x (by decide) B v r hr hB []).mono (cU (qb (by omega)))

theorem HT.tdc (hI : I.Spec Mul C KM) (Q : ℕ) (x : TL) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms (v + 1) ++ r) (hv : bitLen (v + 1) ≤ Q) :
    HT [] B (tdc I x) (Function.update B x (natSyms v ++ r)) (U C KM Q) := by
  have h1 : HT [] B (callI I.dc [x] td0 I.ldc) (Function.update B x (natSyms v ++ r))
      (C * (bitLen (v + 1) + 1)) :=
    (HT.callI_upd I.dc [x] td0 (List.nodup_singleton _) rfl (by decide) I.ldc B (.inl 0) _
      (hI.dc v r _ hr hB) []).mono
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (zerosLead_le_length _) 1))
  exact h1.mono (cU (qb (by omega)))

theorem HT.tic (hI : I.Spec Mul C KM) (Q : ℕ) (x : TL) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hv : bitLen v ≤ Q) :
    HT [] B (tic I x) (Function.update B x (natSyms (v + 1) ++ r)) (U C KM Q) := by
  have h1 : HT [] B (callI I.ic [x] td0 I.lic) (Function.update B x (natSyms (v + 1) ++ r))
      (C * (bitLen v + 1)) :=
    (HT.incNat hI.ic td0 I.lic x (by decide) B v r hr hB []).mono
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (ones_le_length _) 1))
  exact h1.mono (cU (qb (by omega)))

theorem HT.tad (hI : I.Spec Mul C KM) (Q : ℕ) (x y z : TL) (hnd : [x, y, z].Nodup)
    (B : TL → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (hu : bitLen u ≤ Q)
    (hv : bitLen v ≤ Q) :
    HT [] B (tad I x y z) (Function.update B z (natSyms (u + v) ++ B z)) (U C KM Q) :=
  (HT.addNat hI.ad td0 I.lad x y z hnd (by decide) B u v ru rv hru hrv hx hy []).mono
    (cU (qb (by omega)))

theorem HT.tsb (hI : I.Spec Mul C KM) (Q : ℕ) (x y z : TL) (hnd : [x, y, z].Nodup)
    (B : TL → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hvu : v ≤ u) (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (hu : bitLen u ≤ Q)
    (hv : bitLen v ≤ Q) :
    HT [] B (tsb I x y z) (Function.update B z (natSyms (u - v) ++ B z)) (U C KM Q) :=
  (HT.subNat hI.sb td0 I.lsb x y z hnd (by decide) B u v ru rv hru hrv hvu hx hy []).mono
    (cU (qb (by omega)))

theorem HT.ts1 (hI : I.Spec Mul C KM) (Q : ℕ) (x : TL) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (ts1 I x) (Function.update B x (natSyms (v * 2 ^ 1) ++ r)) (U C KM Q) :=
  (HT.shlConst hI.s1 td0 I.ls1 x (by decide) B v r hr hB []).mono (cU (qb (by omega)))

theorem HT.tr1 (hI : I.Spec Mul C KM) (Q : ℕ) (x : TL) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (tr1 I x) (Function.update B x (natSyms (v / 2 ^ 1) ++ r)) (U C KM Q) :=
  (HT.shrConst hI.r1 td0 I.lr1 x (by decide) B v r hr hB []).mono (cU (qb (by omega)))

theorem HT.tsv (hI : I.Spec Mul C KM) (Q : ℕ) (x c : TL) (hnd : [x, c].Nodup)
    (B : TL → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) (hv : v ≤ Q) :
    HT [] B (tsv I x c) (Function.update B x (natSyms (u * 2 ^ v) ++ ru)) (U C KM Q) := by
  have hb := bitLen_le_self v
  exact (HT.shlVar hI.sv td0 I.lsv x c hnd (by decide) B u v ru rv hru hrv hx hc []).mono
    (cU (qb (by omega)))

theorem HT.trv (hI : I.Spec Mul C KM) (Q : ℕ) (x c : TL) (hnd : [x, c].Nodup)
    (B : TL → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) (hu : bitLen u ≤ Q)
    (hv : bitLen v ≤ Q) :
    HT [] B (trv I x c) (Function.update B x (natSyms (u / 2 ^ v) ++ ru)) (U C KM Q) :=
  (HT.shrVar hI.rv td0 I.lrv x c hnd (by decide) B u v ru rv hru hrv hx hc []).mono
    (cU (qb (by omega)))

theorem HT.tdm (hI : I.Spec Mul C KM) (Q : ℕ) (x y q r : TL) (hnd : [x, y, q, r].Nodup)
    (B : TL → List Sym) (u v : ℕ) (ru rv : List Sym) (hv0 : 0 < v) (hru : TermOK ru)
    (hrv : TermOK rv) (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv)
    (hu : bitLen u ≤ Q) (hv : bitLen v ≤ Q) :
    HT [] B (tdm I x y q r)
      (Function.update (Function.update B q (natSyms (u / v) ++ B q)) r (natSyms (u % v) ++ B r))
      (U C KM Q) := by
  have h1 := Nat.mul_le_mul hu hv
  exact (HT.divModNat hI.dm td0 I.ldm x y q r hnd (by decide) B u v ru rv hv0 hru hrv hx hy
    []).mono (cU (by nlinarith))

theorem HT.tcmIf (hI : I.Spec Mul C KM) (Q : ℕ) (x y : TL) (hnd : [x, y].Nodup)
    (B B' : TL → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (hu : bitLen u ≤ Q)
    (hv : bitLen v ≤ Q) (f : Ordering → Bool) (p q : TP I) (T : ℕ)
    (hp : f (Lib.ordOf u v) = true → HT [] B p B' T)
    (hq : f (Lib.ordOf u v) = false → HT [] B q B' T) :
    HT [] B (tcmIf I x y f p q) B' (U C KM Q + T + 1) := by
  have h1 : C * (bitLen u + bitLen v + 1) ≤ U C KM Q := cU (qb (by omega))
  refine (HT.cmpNat_ite hI.cm td0 I.lcm x y hnd (by decide) B B' u v ru rv hru hrv hx hy f p q []
    hp hq).mono ?_
  rw [max_self]
  omega

theorem HT.tizIf (hI : I.Spec Mul C KM) (Q : ℕ) (x : TL) (B B' : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (p q : TP I) (T : ℕ)
    (hp : v = 0 → HT [] B p B' T) (hq : v ≠ 0 → HT [] B q B' T) :
    HT [] B (tizIf I x p q) B' (U C KM Q + T + 1) := by
  have h1 := C_le_U C KM Q
  refine (HT.callI_test I.iz [x] td0 (List.nodup_singleton _) rfl (by decide) I.liz B B'
    (fun b => b) (decide (v = 0)) (hI.iz v r _ hr hB) p q [] (fun h => hp (of_decide_eq_true h))
    (fun h => hq (of_decide_eq_false h))).mono ?_
  rw [max_self]
  omega

theorem HT.tcd (hI : I.Spec Mul C KM) (Q : ℕ) (c : TL) (rc : List Sym) (hrc : TermOK rc)
    (St : ℕ → TL → List Sym) (hSt : ∀ i, St i c = natSyms i ++ rc) (body : TP I) (b N : ℕ)
    (hN : N ≤ Q)
    (hbody : ∀ i, i < N →
      HT [] (Function.update (St (i + 1)) c (natSyms i ++ rc)) body (St i) b) :
    HT [] (St N) (tcd I c body) (St 0) (N * (b + 2 * U C KM Q + 1) + U C KM Q + 1) := by
  refine (HT.cdLoop' hI.iz hI.dc I.liz I.ldc c td0 (by decide) rc hrc St hSt body (fun _ => b) []
    N hbody).mono ?_
  have h3 := C_le_U C KM Q
  have hl := loopCost_le (fun i => C * (bitLen (i + 1) + 1) + b + C) (b + 2 * U C KM Q + 1) N
    (fun i hi => by
      have h1 : bitLen (i + 1) ≤ Q := le_trans (bitLen_le_self _) (by omega)
      have h2 : C * (bitLen (i + 1) + 1) ≤ U C KM Q := cU (qb (by omega))
      omega)
  exact le_trans (Nat.add_le_add_left hl C) (by omega)

end Rules

/-! ## Host rules of the macros -/

section Macros

variable {I : TI} {Mul : ℕ → ℕ} {C KM : ℕ}

theorem HT.tnm (hI : I.Spec Mul C KM) (Q : ℕ) (x y z : TL) (hx1 : [x, xM1, xM2, z].Nodup)
    (hy1 : [y, xM1, xM2, z].Nodup) (B : TL → List Sym) (u v : ℕ) (ru rv : List Sym)
    (hru : TermOK ru) (hrv : TermOK rv) (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv)
    (h1 : TermOK (B xM1)) (h2 : TermOK (B xM2)) (hu : bitLen u ≤ Q) (hv : bitLen v ≤ Q) :
    HT [] B (tnm I x y z) (Function.update B z (natSyms (u * v) ++ B z)) (5 * U C KM Q + 5) := by
  have hxt1 : x ≠ xM1 := fun h => by simp [h] at hx1
  have hyt1 : y ≠ xM1 := fun h => by simp [h] at hy1
  have hyt2 : y ≠ xM2 := fun h => by simp [h] at hy1
  have ht12 : xM1 ≠ xM2 := by decide
  have ht1z : xM1 ≠ z := fun h => by simp [h] at hx1
  have ht2z : xM2 ≠ z := fun h => by simp [h] at hx1
  have eu : intSyms (u : ℤ) = Sym.pos :: natSyms u := intSyms_natCast u
  have ev : intSyms (v : ℤ) = Sym.pos :: natSyms v := intSyms_natCast v
  have euv : intSyms ((u : ℤ) * (v : ℤ)) = Sym.pos :: natSyms (u * v) := by
    rw [← Nat.cast_mul]
    exact intSyms_natCast _
  have hw1 : bitLen (u : ℤ).natAbs ≤ max (bitLen u) (bitLen v) := by simp
  have hw2 : bitLen (v : ℤ).natAbs ≤ max (bitLen u) (bitLen v) := by simp
  have hmU : C * Mul (max (bitLen u) (bitLen v)) + C ≤ U C KM Q := mulU hI.mq (by omega)
  refine (HT.seq (HT.tcp hI Q x xM1 (by simp [hxt1]) B u ru hru hx hu) <|
    HT.seq (HT.pushS xM1 .pos _ []) <|
    HT.seq (HT.tcp hI Q y xM2 (by simp [hyt2]) _ v rv hrv
      (by simp [hyt1, hy]) hv) <|
    HT.seq (HT.pushS xM2 .pos _ []) <|
    HT.seq (HT.mul hI.mu td0 I.lmu xM1 xM2 z (by simp [ht12, ht1z, ht2z]) (by decide) _
      (max (bitLen u) (bitLen v)) (u : ℤ) (v : ℤ) (B xM1) (B xM2) hw1 hw2 h1 h2
      (by simp [ht12, eu])
      (by simp [ht12.symm, ev]) []) <|
    HT.seq (HT.popS z _ .pos (natSyms (u * v) ++ B z)
      (by simp [euv, ht1z.symm, ht2z.symm]) []) <|
    HT.seq (HT.popS xM1 _ .pos (natSyms u ++ B xM1)
      (by simp [ht1z, ht12]) []) <|
    HT.seq (HT.tdr hI Q xM1 _ u (B xM1) h1 (by simp) hu) <|
    HT.seq (HT.popS xM2 _ .pos (natSyms v ++ B xM2)
      (by simp [ht12.symm, ht2z]) []) <|
    HT.tdr hI Q xM2 _ v (B xM2) h2 (by simp) hv).of_eq ?_ (by omega)
  funext g
  by_cases hg1 : g = xM1
  · rw [hg1]
    simp [ht12, ht1z]
  · by_cases hg2 : g = xM2
    · rw [hg2]
      simp [ht12.symm, ht2z]
    · by_cases hgz : g = z
      · rw [hgz]
        simp [ht1z.symm, ht2z.symm]
      · simp [hg1, hg2, hgz]

theorem HT.accAdd (hI : I.Spec Mul C KM) (Q : ℕ) (x acc : TL) (hnd : [x, acc, xN].Nodup)
    (B : TL → List Sym) (u v : ℕ) (ru ra : List Sym) (hru : TermOK ru) (hra : TermOK ra)
    (hx : B x = natSyms u ++ ru) (ha : B acc = natSyms v ++ ra) (hn : TermOK (B xN))
    (hu : bitLen u ≤ Q) (hv : bitLen v ≤ Q) (huv : bitLen (u + v) ≤ Q) :
    HT [] B (accAdd I x acc) (Function.update B acc (natSyms (u + v) ++ ra)) (4 * U C KM Q) := by
  have han : acc ≠ xN := fun h => by simp [h] at hnd
  refine (HT.seq (HT.tad hI Q x acc xN hnd B u v ru ra hru hra hx ha hu hv) <|
    HT.seq (HT.tdr hI Q acc _ v ra hra (by simp [han, ha]) hv) <|
    HT.seq (HT.tcp hI Q xN acc (by simp [han.symm]) _ (u + v) (B xN) hn
      (by simp [han.symm]) huv) <|
    HT.tdr hI Q xN _ (u + v) (B xN) hn (by simp [han.symm]) huv).of_eq ?_
    (by omega)
  funext g
  by_cases hg1 : g = xN
  · rw [hg1]
    simp [han.symm]
  · by_cases hg2 : g = acc
    · rw [hg2]
      simp [han]
    · simp [hg1, hg2]

theorem HT.mvF (hI : I.Spec Mul C KM) (Q : ℕ) (src dst : TL) (hne : src ≠ dst)
    (B : TL → List Sym) (f : ℕ) (tl : List Sym) (hB : B src = natSyms f ++ Sym.mark :: tl)
    (hf : bitLen f ≤ Q) :
    HT [] B (mvF I src dst)
      (Function.update (Function.update B src tl) dst (Sym.mark :: (natSyms f ++ B dst)))
      (2 * U C KM Q + 2) := by
  refine (HT.seq (HT.tcp hI Q src dst (by simp [hne]) B f (Sym.mark :: tl) (termOK_mark _) hB
      hf) <|
    HT.seq (HT.tdr hI Q src _ f (Sym.mark :: tl) (termOK_mark _)
      (by simp [hne, hB]) hf) <|
    HT.seq (HT.popS src _ Sym.mark tl (by simp) []) <|
    HT.pushS dst Sym.mark _ []).of_eq ?_ (by omega)
  funext g
  by_cases hg1 : g = dst
  · rw [hg1]
    simp [hne.symm]
  · by_cases hg2 : g = src
    · rw [hg2]
      simp [hne]
    · simp [hg1, hg2]

theorem HT.rsF (hI : I.Spec Mul C KM) (Q : ℕ) (src dst : TL) (hne : src ≠ dst)
    (B : TL → List Sym) (f : ℕ) (r : List Sym) (hr : TermOK r)
    (hB : B dst = Sym.mark :: (natSyms f ++ r)) (hf : bitLen f ≤ Q) :
    HT [] B (rsF I src dst)
      (Function.update (Function.update B dst r) src (natSyms f ++ Sym.mark :: B src))
      (2 * U C KM Q + 2) := by
  refine (HT.seq (HT.popS dst B Sym.mark _ hB []) <|
    HT.seq (HT.pushS src Sym.mark _ []) <|
    HT.seq (HT.tcp hI Q dst src (by simp [hne.symm]) _ f r hr
      (by simp [hne.symm]) hf) <|
    HT.tdr hI Q dst _ f r hr (by simp [hne.symm]) hf).of_eq ?_ (by omega)
  funext g
  by_cases hg1 : g = dst
  · rw [hg1]
    simp [hne.symm]
  · by_cases hg2 : g = src
    · rw [hg2]
      simp [hne]
    · simp [hg1, hg2]

end Macros

end SubNLogN.Machine.FFT.TwAddr
