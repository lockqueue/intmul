/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.W7k2.B.Rules

/-!
# K6 (`Machine/Tables/Host.lean`): the host layout and instance bundle of the table machine

**Scope (honest summary).** Infrastructure only (no contract of `Contracts/Tables.lean` is proved
here). The table generator and the table dropper of K6 (`BridgeTablesMachineStmt`,
`DropTablesStmt`, `SubNLogN/Machine/Contracts/Tables.lean`) run on the host stacks
`TL = Loc 3 61` and call proved machine contracts (W3 unsigned/signed arithmetic, W5 Toom-3
multiplication, W6a long division and rounding division, W7 evaluator kernels) through the
composition layer of W7k2 (`WP/W7k2/Call.lean`: `Inst`, `callI`, `HT`, `HT.callI_upd`).

## Plan of the K6 machine (all files of `Machine/Tables/`)
* **Host** (`TL`): `.inl 0` = `par` (the bridge header, restored), `.inl 1` = `tapTab`,
  `.inl 2` = `solTab`; `.inr j` (`j < 61`) are private scratch stacks, empty at entry and exit
  (`KClean`). The host program is embedded into `KLoc BrK (Fin 61)` by `callInj` (`Main.lean`).
* **Instances** (`TB`, one shared constant `C`): copy/drop/isZero/dec/inc/add/sub/shlVar/shrVar/
  cmp (W3, unsigned), addInt/subInt (W3, signed), mul (W5), divMod/divRound (W6a), stdChar,
  sincGaussianTap, c0c1, piScaled, log2Scaled (W7). Callee scratch lives on free host stacks
  (any stack not named by the call; callees restore it).
* **Discipline.** Every fragment lemma is an exact-stacks triple `HT ρ B frag B' T` for all host
  states `B` satisfying explicit hypotheses on the stacks it reads; temporaries are scratch stacks
  that are empty before and after the fragment, so `B'` is an explicit `Function.update` chain.
* **Header** (`Header.lean`): field `k` of `hdrSyms b.hdr` is fetched by moving `k` fields from
  `par` onto an empty temporary (marks included), copying the field, and moving everything back.
* **Drop** (`Drop.lean`): `d - 1` times pop one block (until `mark`) from `tapTab`, same for
  `solTab`.
* **Generation** (`Emit.lean`, `Tap*.lean`, `Sol*.lean`, `Main.lean`): records are pushed directly
  in their final orientation (last record first, last coefficient first, each `w`-bit field pushed
  so that its LSB ends on top: `natSyms (v + 2^w)` with `v = z mod 2^w` is reversed twice), so no
  buffer is needed; tap blocks for axes `1, …, d-1` (increasing; running product `A_i`), solver
  blocks for axes `d-1, …, 1` (decreasing; `A_i = A_{i+1} / t_i`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2

/-! ## The host stacks -/

/-- The table machine's host stacks: `.inl 0` = `par`, `.inl 1` = `tapTab`, `.inl 2` = `solTab`,
scratch `.inr 0 … .inr 60`. -/
abbrev TL := Loc 3 61

/-- Default stack of `callMap` (never used: all call lists are in range). -/
abbrev t0 : TL := .inl 0

/-- The header stack `par`. -/
abbrev sPar : TL := .inl 0
/-- The tap table stack. -/
abbrev sTap : TL := .inl 1
/-- The solver table stack. -/
abbrev sSol : TL := .inl 2

/-- A numbering of the host stacks, used to sort update chains. -/
def tidx : TL → ℕ
  | .inl i => i.val
  | .inr j => 3 + j.val

theorem tupd_swap {f : TL → List Sym} {a b : TL} (v w : List Sym) (h : tidx b < tidx a) :
    Function.update (Function.update f a v) b w = Function.update (Function.update f b w) a v := by
  have hne : a ≠ b := fun e => by rw [e] at h; exact lt_irrefl _ h
  exact Function.update_comm hne v w f

/-- A no-op update disappears (side condition kept opaque as `ValEq`, as in W7k2). -/
theorem tupd_eq_self_of {f : TL → List Sym} {a : TL} {v : List Sym} (h : ValEq (f a) v) :
    Function.update f a v = f := by
  unfold ValEq at h
  rw [← h]
  exact Function.update_eq_self a f

/-- The identity lens. -/
def lensId (σ : Type) : Lens σ σ where
  get v := v
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-! ## Contract bodies not covered by W7k2's `Spec*` -/

/-- Body of `W3_subNat`. -/
def SpecSubNat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_shrVar`. -/
def SpecShrVar (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_subInt`. -/
def SpecSubInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W6a_divRound`. -/
def SpecDivRound (I : Inst 3 6 Unit) (C : ℕ) : Prop :=
  ∀ (num : ℤ) (den : ℕ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym), 0 < den →
    TermOK ra → TermOK rb →
    S (.inl 0) = intSyms num ++ ra → S (.inl 1) = natSyms den ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (divRoundRatInt num den) ++ S (.inl 2)))
      (fun _ => True)
      (C * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1))

theorem SpecSubNat.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecSubNat I C) (hC : C ≤ C') :
    SpecSubNat I C' := fun a b rx ry S h1 h2 h3 h4 h5 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4 h5) (Nat.mul_le_mul_right _ hC)

theorem SpecShrVar.mono {I : Inst 2 4 Unit} {C C' : ℕ} (h : SpecShrVar I C) (hC : C ≤ C') :
    SpecShrVar I C' := fun a c rx rc S h1 h2 h3 h4 =>
  runs_mono (h a c rx rc S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecSubInt.mono {I : Inst 3 4 Unit} {C C' : ℕ} (h : SpecSubInt I C) (hC : C ≤ C') :
    SpecSubInt I C' := fun a b rx ry S h1 h2 h3 h4 =>
  runs_mono (h a b rx ry S h1 h2 h3 h4) (Nat.mul_le_mul_right _ hC)

theorem SpecDivRound.mono {I : Inst 3 6 Unit} {C C' : ℕ} (h : SpecDivRound I C) (hC : C ≤ C') :
    SpecDivRound I C' := fun n d ra rb S h1 h2 h3 h4 h5 =>
  runs_mono (h n d ra rb S h1 h2 h3 h4 h5) (Nat.mul_le_mul_right _ hC)

/-! ## The instance bundle -/

/-- The table machine's contract instances (one per contract and compile-time parameter). -/
structure TB : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ic : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  sb : Inst 3 4 Unit
  sv : Inst 2 4 Unit
  sr : Inst 2 4 Unit
  cm : Inst 2 4 Ordering
  ai : Inst 3 4 Unit
  si : Inst 3 4 Unit
  mu : Inst 3 8 Unit
  dm : Inst 4 6 Unit
  dv : Inst 3 6 Unit
  sf : Inst 4 16 Unit
  tp : Inst 8 16 Unit
  cc : Inst 5 16 Unit
  pi : Inst 2 16 Unit
  ln : Inst 2 16 Unit

namespace TB

variable (I : TB)

/-- Host registers: a symbol register, then one register file per instance. -/
abbrev R : Type :=
  Option Sym × I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ic.R × I.ad.R × I.sb.R × I.sv.R ×
    I.sr.R × I.cm.R × I.ai.R × I.si.R × I.mu.R × I.dm.R × I.dv.R × I.sf.R × I.tp.R × I.cc.R ×
    I.pi.R × I.ln.R

def lS : Lens I.R (Option Sym) := Lens.fst _ _
def lcp : Lens I.R I.cp.R := (Lens.fst _ _).sc
def ldr : Lens I.R I.dr.R := (Lens.fst _ _).sc.sc
def liz : Lens I.R I.iz.R := (Lens.fst _ _).sc.sc.sc
def ldc : Lens I.R I.dc.R := (Lens.fst _ _).sc.sc.sc.sc
def lic : Lens I.R I.ic.R := (Lens.fst _ _).sc.sc.sc.sc.sc
def lad : Lens I.R I.ad.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc
def lsb : Lens I.R I.sb.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc
def lsv : Lens I.R I.sv.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc
def lsr : Lens I.R I.sr.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc
def lcm : Lens I.R I.cm.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lai : Lens I.R I.ai.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lsi : Lens I.R I.si.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lmu : Lens I.R I.mu.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def ldm : Lens I.R I.dm.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def ldv : Lens I.R I.dv.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lsf : Lens I.R I.sf.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def ltp : Lens I.R I.tp.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lcc : Lens I.R I.cc.R :=
  (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lpi : Lens I.R I.pi.R :=
  (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lln : Lens I.R I.ln.R :=
  (Lens.snd _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc

theorem R_finite : Finite I.R := by
  have := I.cp.fin; have := I.dr.fin; have := I.iz.fin; have := I.dc.fin; have := I.ic.fin
  have := I.ad.fin; have := I.sb.fin; have := I.sv.fin; have := I.sr.fin; have := I.cm.fin
  have := I.ai.fin; have := I.si.fin; have := I.mu.fin; have := I.dm.fin; have := I.dv.fin
  have := I.sf.fin; have := I.tp.fin; have := I.cc.fin; have := I.pi.fin; have := I.ln.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  have := I.cp.ne; have := I.dr.ne; have := I.iz.ne; have := I.dc.ne; have := I.ic.ne
  have := I.ad.ne; have := I.sb.ne; have := I.sv.ne; have := I.sr.ne; have := I.cm.ne
  have := I.ai.ne; have := I.si.ne; have := I.mu.ne; have := I.dm.ne; have := I.dv.ne
  have := I.sf.ne; have := I.tp.ne; have := I.cc.ne; have := I.pi.ne; have := I.ln.ne
  infer_instance

/-- All twenty contract bodies, with one shared constant `C`. -/
structure Spec (Mul : ℕ → ℕ) (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ic : SpecInc I.ic C
  ad : SpecAddNat I.ad C
  sb : SpecSubNat I.sb C
  sv : SpecShlVar I.sv C
  sr : SpecShrVar I.sr C
  cm : SpecCmpNat I.cm C
  ai : SpecAddInt I.ai C
  si : SpecSubInt I.si C
  mu : SpecMul Mul I.mu C
  dm : SpecDivMod I.dm C
  dv : SpecDivRound I.dv C
  sf : SpecStdChar false I.sf C
  tp : SpecTap I.tp C
  cc : SpecC0C1 I.cc C
  pi : SpecPi I.pi C
  ln : SpecLn2 I.ln C

end TB

/-- Table-machine programs. -/
abbrev TP (I : TB) : Type := Prog TL (fun _ => Sym) I.R

/-! ## Calls on host stacks -/

section Wrappers

variable (I : TB)

def tcp (x y : TL) : TP I := callI I.cp [x, y] t0 I.lcp
def tdr (x : TL) : TP I := callI I.dr [x] t0 I.ldr
def tiz (x : TL) : TP I := callI I.iz [x] t0 I.liz
def tdc (x : TL) : TP I := callI I.dc [x] t0 I.ldc
def tic (x : TL) : TP I := callI I.ic [x] t0 I.lic
def tad (x y z : TL) : TP I := callI I.ad [x, y, z] t0 I.lad
def tsb (x y z : TL) : TP I := callI I.sb [x, y, z] t0 I.lsb
def tsv (x c : TL) : TP I := callI I.sv [x, c] t0 I.lsv
def tsr (x c : TL) : TP I := callI I.sr [x, c] t0 I.lsr
def tcm (x y : TL) : TP I := callI I.cm [x, y] t0 I.lcm
def tai (x y z : TL) : TP I := callI I.ai [x, y, z] t0 I.lai
def tsi (x y z : TL) : TP I := callI I.si [x, y, z] t0 I.lsi
def tmu (x y z : TL) : TP I := callI I.mu [x, y, z] t0 I.lmu
def tdm (x y q r : TL) : TP I := callI I.dm [x, y, q, r] t0 I.ldm
def tdv (x y z : TL) : TP I := callI I.dv [x, y, z] t0 I.ldv
def tsf (q n d z : TL) : TP I := callI I.sf [q, n, d, z] t0 I.lsf
def ttp (s0 s1 s2 s3 s4 s5 s6 z : TL) : TP I :=
  callI I.tp [s0, s1, s2, s3, s4, s5, s6, z] t0 I.ltp
def tcc (s0 s1 s2 s3 z : TL) : TP I := callI I.cc [s0, s1, s2, s3, z] t0 I.lcc
def tpi (x z : TL) : TP I := callI I.pi [x, z] t0 I.lpi
def tln (x z : TL) : TP I := callI I.ln [x, z] t0 I.lln

/-- Push a constant symbol. -/
def tpush (k : TL) (x : Sym) : TP I := pushS k x
/-- Drop the top symbol. -/
def tpop (k : TL) : TP I := popS k
/-- Push a constant natural number. -/
def tnat (k : TL) (c : ℕ) : TP I := pushNat k c

end Wrappers

section Closed

variable (I : TB)

theorem tcall_closed {n cap : ℕ} {O : Type} (J : Inst n cap O) (nm : List TL) (l : Lens I.R J.R) :
    (callI J nm t0 l).Closed := callI_closed J nm t0 l

end Closed

/-! ## Host rules -/

section Rules

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.tcp_spec (hI : I.Spec Mul C) (x y : TL) (hxy : [x, y].Nodup) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (TP I)) :
    HT ρ B (tcp I x y) (Function.update B y (natSyms v ++ B y)) (C * (bitLen v + 1)) :=
  HT.copyNat hI.cp t0 I.lcp x y hxy (by decide) B v r hr hB ρ

theorem HT.tdr_spec (hI : I.Spec Mul C) (x : TL) (B : TL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (TP I)) :
    HT ρ B (tdr I x) (Function.update B x r) (C * (bitLen v + 1)) :=
  HT.dropNat hI.dr t0 I.ldr x (by decide) B v r hr hB ρ

theorem HT.tdc_spec (hI : I.Spec Mul C) (x : TL) (B : TL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms (v + 1) ++ r) (ρ : List (TP I)) :
    HT ρ B (tdc I x) (Function.update B x (natSyms v ++ r)) (C * (bitLen (v + 1) + 1)) :=
  (HT.callI_upd I.dc [x] t0 (List.nodup_singleton _) rfl (by decide) I.ldc B (.inl 0) _
    (hI.dc v r _ hr hB) ρ).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (zerosLead_le_length _) 1))

theorem HT.tic_spec (hI : I.Spec Mul C) (x : TL) (B : TL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (TP I)) :
    HT ρ B (tic I x) (Function.update B x (natSyms (v + 1) ++ r)) (C * (bitLen v + 1)) :=
  (HT.incNat hI.ic t0 I.lic x (by decide) B v r hr hB ρ).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (ones_le_length _) 1))

theorem HT.tad_spec (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tad I x y z) (Function.update B z (natSyms (u + v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.addNat hI.ad t0 I.lad x y z hnd (by decide) B u v ru rv hru hrv hx hy ρ

theorem HT.tsb_spec (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv) (hvu : v ≤ u)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tsb I x y z) (Function.update B z (natSyms (u - v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.callI_upd I.sb [x, y, z] t0 hnd rfl (by decide) I.lsb B (.inl 2) _
    (hI.sb u v ru rv _ hru hrv hvu hx hy) ρ

theorem HT.tsv_spec (hI : I.Spec Mul C) (x c : TL) (hnd : [x, c].Nodup) (B : TL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tsv I x c) (Function.update B x (natSyms (u * 2 ^ v) ++ ru))
      (C * (v + bitLen v + 1)) :=
  HT.shlVar hI.sv t0 I.lsv x c hnd (by decide) B u v ru rv hru hrv hx hc ρ

theorem HT.tsr_spec (hI : I.Spec Mul C) (x c : TL) (hnd : [x, c].Nodup) (B : TL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tsr I x c) (Function.update B x (natSyms (u / 2 ^ v) ++ ru))
      (C * (min v (bitLen u) + bitLen v + 1)) :=
  HT.callI_upd I.sr [x, c] t0 hnd rfl (by decide) I.lsr B (.inl 0) _
    (hI.sr u v ru rv _ hru hrv hx hc) ρ

theorem HT.tcmIte_spec (hI : I.Spec Mul C) (x y : TL) (hnd : [x, y].Nodup) (B B' : TL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (f : Ordering → Bool)
    (p q : TP I) (ρ : List (TP I)) {T₁ T₂ : ℕ} (hp : f (Lib.ordOf u v) = true → HT ρ B p B' T₁)
    (hq : f (Lib.ordOf u v) = false → HT ρ B q B' T₂) :
    HT ρ B ((tcm I x y).seq (.ite (fun s => f (I.cm.obs (I.lcm.get s))) p q)) B'
      (C * (bitLen u + bitLen v + 1) + (max T₁ T₂ + 1)) :=
  HT.cmpNat_ite hI.cm t0 I.lcm x y hnd (by decide) B B' u v ru rv hru hrv hx hy f p q ρ hp hq

theorem HT.tizIte_spec (hI : I.Spec Mul C) (x : TL) (B B' : TL → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) (p q : TP I) (ρ : List (TP I)) {T₁ T₂ : ℕ}
    (hp : v = 0 → HT ρ B p B' T₁) (hq : v ≠ 0 → HT ρ B q B' T₂) :
    HT ρ B ((tiz I x).seq (.ite (fun s => I.iz.obs (I.liz.get s)) p q)) B'
      (C + (max T₁ T₂ + 1)) :=
  HT.callI_test I.iz [x] t0 (List.nodup_singleton _) rfl (by decide) I.liz B B' (fun b => b)
    (decide (v = 0)) (hI.iz v r _ hr hB) p q ρ (fun h => hp (of_decide_eq_true h))
    (fun h => hq (of_decide_eq_false h))

theorem HT.tai_spec (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tai I x y z) (Function.update B z (intSyms (u + v) ++ B z))
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1)) :=
  HT.addInt hI.ai t0 I.lai x y z hnd (by decide) B u v ru rv hru hrv hx hy ρ

theorem HT.tsi_spec (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tsi I x y z) (Function.update B z (intSyms (u - v) ++ B z))
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1)) :=
  HT.callI_upd I.si [x, y, z] t0 hnd rfl (by decide) I.lsi B (.inl 2) _
    (hI.si u v ru rv _ hru hrv hx hy) ρ

theorem HT.tmu_spec (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (w : ℕ) (u v : ℤ) (ru rv : List Sym) (hwu : bitLen u.natAbs ≤ w) (hwv : bitLen v.natAbs ≤ w)
    (hru : TermOK ru) (hrv : TermOK rv) (hx : B x = intSyms u ++ ru)
    (hy : B y = intSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tmu I x y z) (Function.update B z (intSyms (u * v) ++ B z)) (C * Mul w + C) :=
  HT.mul hI.mu t0 I.lmu x y z hnd (by decide) B w u v ru rv hwu hwv hru hrv hx hy ρ

theorem HT.tdm_spec (hI : I.Spec Mul C) (x y q r : TL) (hnd : [x, y, q, r].Nodup) (B : TL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hv : 0 < v) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (ρ : List (TP I)) :
    HT ρ B (tdm I x y q r)
      (Function.update (Function.update B q (natSyms (u / v) ++ B q)) r (natSyms (u % v) ++ B r))
      (C * (bitLen u * bitLen v + bitLen u + bitLen v + 1)) :=
  HT.divModNat hI.dm t0 I.ldm x y q r hnd (by decide) B u v ru rv hv hru hrv hx hy ρ

theorem HT.tdv_spec (hI : I.Spec Mul C) (x y z : TL) (hnd : [x, y, z].Nodup) (B : TL → List Sym)
    (n : ℤ) (d : ℕ) (rn rd : List Sym) (hd : 0 < d) (hrn : TermOK rn) (hrd : TermOK rd)
    (hx : B x = intSyms n ++ rn) (hy : B y = natSyms d ++ rd) (ρ : List (TP I)) :
    HT ρ B (tdv I x y z) (Function.update B z (intSyms (divRoundRatInt n d) ++ B z))
      (C * (bitLen n.natAbs * bitLen d + bitLen n.natAbs + bitLen d + 1)) :=
  HT.callI_upd I.dv [x, y, z] t0 hnd rfl (by decide) I.ldv B (.inl 2) _
    (hI.dv n d rn rd _ hd hrn hrd hx hy) ρ

theorem HT.tsf_spec (hI : I.Spec Mul C) (sq sn sd z : TL) (hnd : [sq, sn, sd, z].Nodup)
    (B : TL → List Sym) (q num den : ℕ) (r0 r1 r2 : List Sym) (hden : 0 < den) (hnum : num ≤ den)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (e0 : B sq = natSyms q ++ r0)
    (e1 : B sn = natSyms num ++ r1) (e2 : B sd = natSyms den ++ r2) (ρ : List (TP I)) :
    HT ρ B (tsf I sq sn sd z)
      (Function.update B z
        (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den false).1 ++ B z))
      (C * (q + bitLen den + 1) ^ 4) :=
  HT.stdChar hI.sf t0 I.lsf sq sn sd z hnd (by decide) B q num den r0 r1 r2 hden hnum h0 h1 h2
    e0 e1 e2 ρ

theorem HT.ttp_spec (hI : I.Spec Mul C) (s0 s1 s2 s3 s4 s5 s6 z : TL)
    (hnd : [s0, s1, s2, s3, s4, s5, s6, z].Nodup) (B : TL → List Sym) (p_work pSub t1 j1 s : ℕ)
    (r0 r1 r2 r3 r4 r5 r6 : List Sym) (a1 : 0 < p_work) (a2 : 0 < pSub) (a3 : 0 < t1)
    (a4 : j1 < t1) (a5 : s < 2 * pSub + 1)
    (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2) (b3 : TermOK r3) (b4 : TermOK r4)
    (b5 : TermOK r5) (b6 : TermOK r6)
    (e0 : B s0 = natSyms p_work ++ r0) (e1 : B s1 = natSyms pSub ++ r1)
    (e2 : B s2 = natSyms t1 ++ r2) (e3 : B s3 = natSyms j1 ++ r3) (e4 : B s4 = natSyms s ++ r4)
    (e5 : B s5 = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1 ++ r5)
    (e6 : B s6 = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1 ++ r6)
    (ρ : List (TP I)) :
    HT ρ B (ttp I s0 s1 s2 s3 s4 s5 s6 z)
      (Function.update B z
        (intSyms (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1 ++ B z))
      (C * (p_work + pSub + bitLen t1 + 1) ^ 4) :=
  HT.tap hI.tp t0 I.ltp s0 s1 s2 s3 s4 s5 s6 z hnd (by decide) B p_work pSub t1 j1 s
    r0 r1 r2 r3 r4 r5 r6 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 e0 e1 e2 e3 e4 e5 e6 ρ

theorem HT.tcc_spec (hI : I.Spec Mul C) (s0 s1 s2 s3 z : TL) (hnd : [s0, s1, s2, s3, z].Nodup)
    (B : TL → List Sym) (p_work pSub r u2 : ℕ) (r0 r1 r2 r3 : List Sym) (a1 : 0 < p_work)
    (a2 : 0 < r) (a3 : u2 < r) (b0 : TermOK r0) (b1 : TermOK r1) (b2 : TermOK r2)
    (b3 : TermOK r3) (e0 : B s0 = natSyms p_work ++ r0) (e1 : B s1 = natSyms pSub ++ r1)
    (e2 : B s2 = natSyms r ++ r2) (e3 : B s3 = natSyms u2 ++ r3) (ρ : List (TP I)) :
    HT ρ B (tcc I s0 s1 s2 s3 z)
      (Function.update B z
        (intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.1.1 ++
          intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.2.1 ++ B z))
      (C * (p_work + pSub + bitLen r + 1) ^ 4) :=
  HT.c0c1 hI.cc t0 I.lcc s0 s1 s2 s3 z hnd (by decide) B p_work pSub r u2 r0 r1 r2 r3 a1 a2 a3
    b0 b1 b2 b3 e0 e1 e2 e3 ρ

theorem HT.tpi_spec (hI : I.Spec Mul C) (x z : TL) (hnd : [x, z].Nodup) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (TP I)) :
    HT ρ B (tpi I x z)
      (Function.update B z (intSyms (IntMul.computablePiScaledWithCost v).1 ++ B z))
      (C * (v + 1) ^ 4) :=
  HT.piScaled hI.pi t0 I.lpi x z hnd (by decide) B v r hr hB ρ

theorem HT.tln_spec (hI : I.Spec Mul C) (x z : TL) (hnd : [x, z].Nodup) (B : TL → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (ρ : List (TP I)) :
    HT ρ B (tln I x z)
      (Function.update B z (intSyms (IntMul.computableLog2ScaledWithCost v).1 ++ B z))
      (C * (v + 1) ^ 4) :=
  HT.log2Scaled hI.ln t0 I.lln x z hnd (by decide) B v r hr hB ρ

theorem HT.tpush_spec (x : TL) (s : Sym) (B : TL → List Sym) (ρ : List (TP I)) :
    HT ρ B (tpush I x s) (Function.update B x (s :: B x)) 1 :=
  HT.pushS x s B ρ

theorem HT.tpop_spec (x : TL) (B : TL → List Sym) (s : Sym) (rest : List Sym) (hB : B x = s :: rest)
    (ρ : List (TP I)) : HT ρ B (tpop I x) (Function.update B x rest) 1 :=
  HT.popS x B s rest hB ρ

theorem HT.tnat_spec (x : TL) (c : ℕ) (B : TL → List Sym) (ρ : List (TP I)) :
    HT ρ B (tnat I x c) (Function.update B x (natSyms c ++ B x)) (bitLen c + 1) :=
  HT.pushNat x c B ρ

end Rules

/-! ## Countdown loops (bodies only for the iterations that run) -/

section Countdown

variable (I : TB)

/-- `while ctr ≠ 0 do (dec ctr; body)`. -/
def tcd (ctr : TL) (body : TP I) : TP I := cdLoop I.iz I.dc I.liz I.ldc ctr t0 body

theorem tcd_closed (ctr : TL) (body : TP I) (hb : body.Closed) : (tcd I ctr body).Closed :=
  cdLoop_closed _ _ _ _ _ _ _ hb

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

/-- **Countdown loop.** `St i` is the state with counter `i`; the body turns `St (i+1)` with the
counter already decremented to `i` into `St i`, for the iterations `i < n` that run. -/
theorem HT.tcd_spec (hI : I.Spec Mul C) (ctr : TL) (rc : List Sym) (hrc : TermOK rc)
    (St : ℕ → TL → List Sym) (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : TP I) (n : ℕ)
    (cb : ℕ → ℕ) (ρ : List (TP I))
    (hbody : ∀ i < n, HT ρ (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) (cb i)) :
    HT ρ (St n) (tcd I ctr body) (St 0)
      (C + loopCost (fun i => C * (bitLen (i + 1) + 1) + cb i + C) n) := by
  have htest : ∀ i, Triple ρ (fun s => s.stk = St i) (callI I.iz [ctr] t0 I.liz)
      (fun s => s.stk = St i ∧ I.iz.obs (I.liz.get s.var) = decide (i = 0)) C := fun i =>
    callI_same I.iz [ctr] t0 (List.nodup_singleton _) rfl (by decide) I.liz (St i)
      (hI.iz i rc _ hrc (hSt i)) ρ
  refine Triple.seq (htest n) ?_
  have hloop := Triple.loop (ρ := ρ) (c := fun v => !(I.iz.obs (I.liz.get v)))
    (p := ((callI I.dc [ctr] t0 I.ldc).seq body).seq (callI I.iz [ctr] t0 I.liz))
    (I := fun k s => k ≤ n ∧ s.stk = St k ∧ I.iz.obs (I.liz.get s.var) = decide (k = 0))
    (B := fun i => C * (bitLen (i + 1) + 1) + cb i + C) ?_ ?_ ?_ n
  · exact Triple.conseq hloop (fun s hs => ⟨le_rfl, hs⟩) (fun s hs => hs.2.1) le_rfl
  · intro k
    by_cases hk : k + 1 ≤ n
    · have hdec : HT ρ (St (k + 1)) (callI I.dc [ctr] t0 I.ldc)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (C * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
        HT.callI_upd I.dc [ctr] t0 (List.nodup_singleton _) rfl (by decide) I.ldc (St (k + 1))
          (.inl 0) _ (hI.dc k rc _ hrc (hSt (k + 1))) ρ
      have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
        zerosLead_le_length _
      have h1 := Triple.seq (Triple.seq hdec (hbody k (by omega))) (htest k)
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) ?_
      have : C * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤ C * (bitLen (k + 1) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      show _ ≤ C * (bitLen (k + 1) + 1) + cb k + C
      omega
    · intro s hs
      exact absurd hs.1 hk
  · intro k s hs
    simp [hs.2.2]
  · intro s hs
    simp [hs.2.2]

/-- A uniform bound for `loopCost`. -/
theorem loopCost_le_unif (B : ℕ → ℕ) (b n : ℕ) (h : ∀ k < n, B k ≤ b) :
    loopCost B n ≤ n * (b + 1) + 1 :=
  loopCost_le_of_lt B b n h

end Countdown

/-! ## Symbol loops: dropping and moving blocks -/

section SymLoops

variable (I : TB)

/-- Pop and discard symbols from `X` until a `mark` has been popped. -/
def dropBlock (X : TL) : TP I :=
  (popR' I.lS X).seq (.loop (fun v => decide (I.lS.get v ≠ some Sym.mark)) (popR' I.lS X))

theorem dropBlock_closed (X : TL) : (dropBlock I X).Closed := ⟨trivial, trivial⟩

/-- Pop all symbols of `X` (until it is empty) and push them onto `Y`. -/
def moveAll (X Y : TL) : TP I :=
  (popR' I.lS X).seq (.loop (fun v => (I.lS.get v).isSome)
    ((Prog.push Y (fun v => (I.lS.get v).getD .sep)).seq (popR' I.lS X)))

theorem moveAll_closed (X Y : TL) : (moveAll I X Y).Closed := ⟨trivial, ⟨trivial, trivial⟩⟩

/-- Move one header field (its bits and its `mark`) from `X` to `Y`. -/
def moveThru (X Y : TL) : TP I := (moveBlock I.lS X Y).seq (tpush I Y .mark)

theorem moveThru_closed (X Y : TL) : (moveThru I X Y).Closed := ⟨moveBlock_closed _ _ _, trivial⟩

end SymLoops

section SymRules

variable {I : TB}

theorem dropBlock_loop (X : TL) (ρ : List (TP I)) (rest : List Sym) :
    ∀ (seg : List Sym), Sym.mark ∉ seg → ∀ (B : TL → List Sym) (v : I.R) (h : Sym)
      (t : List Sym), h :: t = seg ++ Sym.mark :: rest → B X = t → I.lS.get v = some h →
      ∃ v', Eval ρ (.loop (fun v => decide (I.lS.get v ≠ some Sym.mark)) (popR' I.lS X)) ⟨v, B⟩
        ⟨v', Function.update B X rest⟩ (2 * seg.length + 1)
  | [], _, B, v, h, t, hht, hBX, hv => by
    simp only [List.nil_append, List.cons.injEq] at hht
    obtain ⟨hh, ht⟩ := hht
    rw [hh] at hv
    refine ⟨v, (Eval.loop_false (by simp [hv])).of_eq ?_ rfl⟩
    have h1 : Function.update B X rest = B := by rw [← ht, ← hBX, Function.update_eq_self]
    rw [h1]
  | x :: seg', hseg, B, v, h, t, hht, hBX, hv => by
    simp only [List.cons_append, List.cons.injEq] at hht
    obtain ⟨hh, ht⟩ := hht
    rw [ht] at hBX
    rw [hh] at hv
    have hx : x ≠ Sym.mark := fun e => hseg (by simp [e])
    have hseg' : Sym.mark ∉ seg' := fun hm => hseg (List.mem_cons_of_mem _ hm)
    obtain ⟨h', t', hht'⟩ : ∃ h' t', h' :: t' = seg' ++ Sym.mark :: rest := by
      cases seg' with
      | nil => exact ⟨Sym.mark, rest, rfl⟩
      | cons y ys => exact ⟨y, ys ++ Sym.mark :: rest, rfl⟩
    have hBX' : B X = h' :: t' := by rw [hBX, hht']
    have hB2X : (Function.update B X (B X).tail) X = t' := by
      rw [Function.update_self, hBX']
      rfl
    obtain ⟨v', e⟩ := dropBlock_loop X ρ rest seg' hseg' (Function.update B X (B X).tail)
      (I.lS.set v (B X).head?) h' t' hht' hB2X (by rw [I.lS.get_set, hBX']; rfl)
    have epop := Eval.pop ρ X (fun v o => I.lS.set v o) v B
    refine ⟨v', (Eval.loop_true (by simp [hv, hx]) epop e).of_eq ?_ ?_⟩
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

theorem HT.dropBlock_spec (X : TL) (ρ : List (TP I)) (seg rest : List Sym) (hseg : Sym.mark ∉ seg)
    (B : TL → List Sym) (hB : B X = seg ++ Sym.mark :: rest) :
    HT ρ B (dropBlock I X) (Function.update B X rest) (2 * seg.length + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨h, t, hht⟩ : ∃ h t, h :: t = seg ++ Sym.mark :: rest := by
    cases seg with
    | nil => exact ⟨Sym.mark, rest, rfl⟩
    | cons y ys => exact ⟨y, ys ++ Sym.mark :: rest, rfl⟩
  have hSX : S X = h :: t := by rw [hB, hht]
  have hS1X : (Function.update S X (S X).tail) X = t := by
    rw [Function.update_self, hSX]; rfl
  obtain ⟨v', e⟩ := dropBlock_loop X ρ rest seg hseg (Function.update S X (S X).tail)
    (I.lS.set v (S X).head?) h t hht hS1X (by rw [I.lS.get_set, hSX]; rfl)
  refine ⟨⟨v', _⟩, _, Eval.seq (Eval.pop ρ X (fun v o => I.lS.set v o) v S) e, ?_, ?_⟩
  · show Function.update (Function.update S X (S X).tail) X rest = Function.update S X rest
    rw [Function.update_idem]
  · omega

theorem moveAll_loop (X Y : TL) (hXY : X ≠ Y) (ρ : List (TP I)) :
    ∀ (L : List Sym) (B : TL → List Sym) (v : I.R), B X = L.tail → I.lS.get v = L.head? →
      ∃ v', Eval ρ (.loop (fun v => (I.lS.get v).isSome)
        ((Prog.push Y (fun v => (I.lS.get v).getD .sep)).seq (popR' I.lS X))) ⟨v, B⟩
        ⟨v', Function.update (Function.update B X []) Y (L.reverse ++ B Y)⟩ (3 * L.length + 1)
  | [], B, v, hBX, hv => by
    refine ⟨v, (Eval.loop_false (by simp [hv])).of_eq ?_ rfl⟩
    have h1 : Function.update B X [] = B := by
      rw [show ([] : List Sym) = B X from hBX.symm, Function.update_eq_self]
    simp [h1]
  | x :: t, B, v, hBX, hv => by
    simp only [List.tail_cons] at hBX
    simp only [List.head?_cons] at hv
    have hB1X : (Function.update B Y (x :: B Y)) X = t := by
      rw [Function.update_of_ne hXY, hBX]
    set B2 := Function.update (Function.update B Y (x :: B Y)) X
      ((Function.update B Y (x :: B Y)) X).tail with hB2
    have hB2X : B2 X = t.tail := by rw [hB2, Function.update_self, hB1X]
    obtain ⟨v', e⟩ := moveAll_loop X Y hXY ρ t B2
      (I.lS.set v ((Function.update B Y (x :: B Y)) X).head?) hB2X
      (by rw [I.lS.get_set, hB1X])
    have epush : Eval ρ (Prog.push Y (fun v => (I.lS.get v).getD .sep)) ⟨v, B⟩
        ⟨v, Function.update B Y (x :: B Y)⟩ 1 := by
      refine (Eval.push ρ Y _ v B).of_eq ?_ rfl
      simp [hv]
    have epop := Eval.pop ρ X (fun v o => I.lS.set v o) v (Function.update B Y (x :: B Y))
    refine ⟨v', (Eval.loop_true (by simp [hv]) (Eval.seq epush epop) e).of_eq ?_ ?_⟩
    · congr 1
      funext g
      by_cases hgY : g = Y
      · rw [hgY]
        simp [hB2, Function.update_apply, Ne.symm hXY]
      · by_cases hgX : g = X
        · rw [hgX]
          simp [hB2, Function.update_apply, hXY]
        · simp [hB2, Function.update_apply, hgX, hgY]
    · simp only [List.length_cons]
      omega

theorem HT.moveAll_spec (X Y : TL) (hXY : X ≠ Y) (ρ : List (TP I)) (L : List Sym)
    (B : TL → List Sym) (hB : B X = L) :
    HT ρ B (moveAll I X Y)
      (Function.update (Function.update B X []) Y (L.reverse ++ B Y)) (3 * L.length + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have hS1X : (Function.update S X (S X).tail) X = L.tail := by
    rw [Function.update_self, hB]
  obtain ⟨v', e⟩ := moveAll_loop X Y hXY ρ L (Function.update S X (S X).tail)
    (I.lS.set v (S X).head?) hS1X (by rw [I.lS.get_set, hB])
  refine ⟨⟨v', _⟩, _, Eval.seq (Eval.pop ρ X (fun v o => I.lS.set v o) v S) e, ?_, ?_⟩
  · show Function.update (Function.update (Function.update S X (S X).tail) X []) Y
        (L.reverse ++ (Function.update S X (S X).tail) Y) =
      Function.update (Function.update S X []) Y (L.reverse ++ S Y)
    rw [Function.update_idem, Function.update_of_ne (Ne.symm hXY)]
  · omega

theorem HT.moveThru_spec (X Y : TL) (hXY : X ≠ Y) (ρ : List (TP I)) (seg rest : List Sym)
    (hseg : Sym.mark ∉ seg) (B : TL → List Sym) (hB : B X = seg ++ Sym.mark :: rest) :
    HT ρ B (moveThru I X Y)
      (Function.update (Function.update B X rest) Y ((seg ++ [Sym.mark]).reverse ++ B Y))
      (3 * seg.length + 3) := by
  refine (HT.seq (HT.moveBlock I.lS X Y hXY ρ seg rest hseg B hB) (HT.tpush_spec Y .mark _ ρ)).of_eq
    ?_ le_rfl
  rw [Function.update_idem, Function.update_self]
  simp

end SymRules

