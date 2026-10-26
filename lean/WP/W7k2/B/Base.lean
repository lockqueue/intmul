import WP.W7k2.Emit
import WP.W7k2.Arith

/-!
# WP.W7k2.B.Base — the table builder's instances and operation wrappers

The table builder (`W7_buildTablesRef`) runs on the host stacks `BL = Loc 4 32` and calls twenty
contract instances, bundled in `BI`:

| field | contract | field | contract |
|---|---|---|---|
| `cp` | `W3_copyNat` | `ai` | `W3_addInt` |
| `dr` | `W3_dropNat` | `mu` | `W5_mulAt Mul` |
| `iz` | `W3_isZeroNat` | `dm` | `W6a_divModNat` |
| `dc` | `W3_decNat` | `sf`, `st` | `W7_stdChar false / true` |
| `ic` | `W3_incNat` | `tp` | `W7_sincGaussianTap` |
| `ad` | `W3_addNat` | `cc` | `W7_c0c1` |
| `s1`, `r1` | `W3_shlConst 1`, `W3_shrConst 1` | `cr` | `W7_colRecip` |
| `sv` | `W3_shlVar` | `pi`, `ln` | `W7_piScaled`, `W7_log2Scaled` |
| `cm` | `W3_cmpNat` | | |

`BI.Spec I Mul C` states all twenty contract bodies with one shared constant `C`.

Contents:
* `bcp`, `bdr`, … — the calls on host stacks (callee scratch on free host stacks); `bcd` (countdown
  loop) and `bwl` (`while x < y`). Their host rules are in `B/Rules.lean`.
* Update chains over `BL` are normalised by
  `simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap, Function.update_idem,
  upd_eq_self_of, Function.update_self, Function.update_of_ne, List.append_assoc, List.cons_append,
  List.nil_append]`: sort by stack index (`bidx`), merge duplicate keys, drop no-op updates
  (restored stacks), evaluate at literal stacks.
* `freeBelow_mono` (for code under a `fix`).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts

/-! ## `FreeBelow` is monotone -/

theorem freeBelow_mono {K σ : Type} {Γ : K → Type} :
    ∀ (p : Prog K Γ σ) {d d' : ℕ}, p.FreeBelow d → d ≤ d' → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hd => ⟨freeBelow_mono p h.1 hd, freeBelow_mono q h.2 hd⟩
  | .ite _ p q, _, _, h, hd => ⟨freeBelow_mono p h.1 hd, freeBelow_mono q h.2 hd⟩
  | .loop _ p, _, _, h, hd => freeBelow_mono p h hd
  | .fix b, _, _, h, hd => freeBelow_mono b h (by omega)
  | .recur _, _, _, h, hd => Nat.lt_of_lt_of_le h hd

/-! ## Host stacks and update chains -/

/-- The builder's host stacks: `0 TR, 1 L, 2 p, 3 K`, scratch `.inr 0 … .inr 31`. -/
abbrev BL := Loc 4 32

/-- Default stack of `callMap` (never used: all call lists are in range). -/
abbrev d0 : BL := .inl 0

/-- A numbering of the host stacks, used to sort update chains. -/
def bidx : BL → ℕ
  | .inl i => i.val
  | .inr j => 4 + j.val

theorem upd_swap {f : BL → List Sym} {a b : BL} (v w : List Sym) (h : bidx b < bidx a) :
    Function.update (Function.update f a v) b w = Function.update (Function.update f b w) a v := by
  have hne : a ≠ b := fun e => by rw [e] at h; exact lt_irrefl _ h
  exact Function.update_comm hne v w f

/-- Equality of stack contents, kept opaque so that `decide` never tries to evaluate it (it is
the side condition of `upd_eq_self_of`, discharged by evaluating the update chain). -/
def ValEq (x y : List Sym) : Prop := x = y

/-- A no-op update (e.g. a scratch stack restored to its content) disappears. -/
theorem upd_eq_self_of {f : BL → List Sym} {a : BL} {v : List Sym} (h : ValEq (f a) v) :
    Function.update f a v = f := by
  unfold ValEq at h
  rw [← h]
  exact Function.update_eq_self a f

example (B : BL → List Sym) (x : List Sym) :
    Function.update (Function.update (Function.update B (.inr 3) x) (.inr 1) [Sym.sep]) (.inr 3)
      (B (.inr 3)) = Function.update B (.inr 1) [Sym.sep] := by
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
    (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap, Function.update_idem,
    upd_eq_self_of, Function.update_self, Function.update_of_ne, List.append_assoc,
    List.cons_append, List.nil_append]

/-! ## The instance bundle -/

/-- The builder's contract instances (one per contract and compile-time parameter). -/
structure BI : Type 1 where
  cp : Inst 2 4 Unit
  dr : Inst 1 4 Unit
  iz : Inst 1 4 Bool
  dc : Inst 1 4 Unit
  ic : Inst 1 4 Unit
  ad : Inst 3 4 Unit
  s1 : Inst 1 4 Unit
  r1 : Inst 1 4 Unit
  sv : Inst 2 4 Unit
  cm : Inst 2 4 Ordering
  ai : Inst 3 4 Unit
  mu : Inst 3 8 Unit
  dm : Inst 4 6 Unit
  sf : Inst 4 16 Unit
  st : Inst 4 16 Unit
  tp : Inst 8 16 Unit
  cc : Inst 5 16 Unit
  cr : Inst 6 16 Unit
  pi : Inst 2 16 Unit
  ln : Inst 2 16 Unit

/-- Push a lens one product component to the right. -/
def _root_.TMFw.Lens.sc {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

namespace BI

variable (I : BI)

/-- Host registers: a symbol register, then one register file per instance. -/
abbrev R : Type :=
  Option Sym × I.cp.R × I.dr.R × I.iz.R × I.dc.R × I.ic.R × I.ad.R × I.s1.R × I.r1.R ×
    I.sv.R × I.cm.R × I.ai.R × I.mu.R × I.dm.R × I.sf.R × I.st.R × I.tp.R × I.cc.R × I.cr.R ×
    I.pi.R × I.ln.R

def lS : Lens I.R (Option Sym) := Lens.fst _ _
def lcp : Lens I.R I.cp.R := (Lens.fst _ _).sc
def ldr : Lens I.R I.dr.R := (Lens.fst _ _).sc.sc
def liz : Lens I.R I.iz.R := (Lens.fst _ _).sc.sc.sc
def ldc : Lens I.R I.dc.R := (Lens.fst _ _).sc.sc.sc.sc
def lic : Lens I.R I.ic.R := (Lens.fst _ _).sc.sc.sc.sc.sc
def lad : Lens I.R I.ad.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc
def ls1 : Lens I.R I.s1.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc
def lr1 : Lens I.R I.r1.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc
def lsv : Lens I.R I.sv.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc
def lcm : Lens I.R I.cm.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lai : Lens I.R I.ai.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lmu : Lens I.R I.mu.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def ldm : Lens I.R I.dm.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lsf : Lens I.R I.sf.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lst : Lens I.R I.st.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def ltp : Lens I.R I.tp.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lcc : Lens I.R I.cc.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lcr : Lens I.R I.cr.R := (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lpi : Lens I.R I.pi.R :=
  (Lens.fst _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc
def lln : Lens I.R I.ln.R :=
  (Lens.snd _ _).sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc.sc

theorem R_finite : Finite I.R := by
  haveI := I.cp.fin; haveI := I.dr.fin; haveI := I.iz.fin; haveI := I.dc.fin; haveI := I.ic.fin
  haveI := I.ad.fin; haveI := I.s1.fin; haveI := I.r1.fin; haveI := I.sv.fin; haveI := I.cm.fin
  haveI := I.ai.fin; haveI := I.mu.fin; haveI := I.dm.fin; haveI := I.sf.fin; haveI := I.st.fin
  haveI := I.tp.fin; haveI := I.cc.fin; haveI := I.cr.fin; haveI := I.pi.fin; haveI := I.ln.fin
  infer_instance

theorem R_nonempty : Nonempty I.R := by
  haveI := I.cp.ne; haveI := I.dr.ne; haveI := I.iz.ne; haveI := I.dc.ne; haveI := I.ic.ne
  haveI := I.ad.ne; haveI := I.s1.ne; haveI := I.r1.ne; haveI := I.sv.ne; haveI := I.cm.ne
  haveI := I.ai.ne; haveI := I.mu.ne; haveI := I.dm.ne; haveI := I.sf.ne; haveI := I.st.ne
  haveI := I.tp.ne; haveI := I.cc.ne; haveI := I.cr.ne; haveI := I.pi.ne; haveI := I.ln.ne
  infer_instance

/-- All twenty contract bodies, with one shared constant `C`. -/
structure Spec (Mul : ℕ → ℕ) (C : ℕ) : Prop where
  cp : SpecCopy I.cp C
  dr : SpecDrop I.dr C
  iz : SpecIsZero I.iz C
  dc : SpecDec I.dc C
  ic : SpecInc I.ic C
  ad : SpecAddNat I.ad C
  s1 : SpecShlConst 1 I.s1 C
  r1 : SpecShrConst 1 I.r1 C
  sv : SpecShlVar I.sv C
  cm : SpecCmpNat I.cm C
  ai : SpecAddInt I.ai C
  mu : SpecMul Mul I.mu C
  dm : SpecDivMod I.dm C
  sf : SpecStdChar false I.sf C
  st : SpecStdChar true I.st C
  tp : SpecTap I.tp C
  cc : SpecC0C1 I.cc C
  cr : SpecColRecip I.cr C
  pi : SpecPi I.pi C
  ln : SpecLn2 I.ln C

end BI

/-- Builder programs. -/
abbrev BP (I : BI) : Type := Prog BL (fun _ => Sym) I.R

/-! ## Calls on host stacks -/

section Wrappers

variable (I : BI)

def bcp (x y : BL) : BP I := callI I.cp [x, y] d0 I.lcp
def bdr (x : BL) : BP I := callI I.dr [x] d0 I.ldr
def biz (x : BL) : BP I := callI I.iz [x] d0 I.liz
def bdc (x : BL) : BP I := callI I.dc [x] d0 I.ldc
def bic (x : BL) : BP I := callI I.ic [x] d0 I.lic
def bad (x y z : BL) : BP I := callI I.ad [x, y, z] d0 I.lad
def bs1 (x : BL) : BP I := callI I.s1 [x] d0 I.ls1
def br1 (x : BL) : BP I := callI I.r1 [x] d0 I.lr1
def bsv (x c : BL) : BP I := callI I.sv [x, c] d0 I.lsv
def bcm (x y : BL) : BP I := callI I.cm [x, y] d0 I.lcm
def bai (x y z : BL) : BP I := callI I.ai [x, y, z] d0 I.lai
def bmu (x y z : BL) : BP I := callI I.mu [x, y, z] d0 I.lmu
def bdm (x y q r : BL) : BP I := callI I.dm [x, y, q, r] d0 I.ldm
def bsf (q n d z : BL) : BP I := callI I.sf [q, n, d, z] d0 I.lsf
def bst (q n d z : BL) : BP I := callI I.st [q, n, d, z] d0 I.lst
def btp (s0 s1 s2 s3 s4 s5 s6 z : BL) : BP I :=
  callI I.tp [s0, s1, s2, s3, s4, s5, s6, z] d0 I.ltp
def bcc (s0 s1 s2 s3 z : BL) : BP I := callI I.cc [s0, s1, s2, s3, z] d0 I.lcc
def bcr (s0 s1 s2 s3 s4 z : BL) : BP I := callI I.cr [s0, s1, s2, s3, s4, z] d0 I.lcr
def bpi (x z : BL) : BP I := callI I.pi [x, z] d0 I.lpi
def bln (x z : BL) : BP I := callI I.ln [x, z] d0 I.lln

/-- Countdown loop on `ctr` (`while ctr ≠ 0 do (dec ctr; body)`). -/
def bcd (ctr : BL) (body : BP I) : BP I := cdLoop I.iz I.dc I.liz I.ldc ctr d0 body

/-- `while x < y do body`, with a `cmpNat` test before every iteration. -/
def bwl (x y : BL) (body : BP I) : BP I :=
  (bcm I x y).seq (.loop (fun v => decide (I.cm.obs (I.lcm.get v) = .lt)) (body.seq (bcm I x y)))

theorem bcall_closed {n cap : ℕ} {O : Type} (J : Inst n cap O) (nm : List BL) (l : Lens I.R J.R) :
    (callI J nm d0 l).Closed := callI_closed J nm d0 l

theorem bcd_closed (ctr : BL) (body : BP I) (hb : body.Closed) : (bcd I ctr body).Closed :=
  cdLoop_closed _ _ _ _ _ _ _ hb

theorem bwl_closed (x y : BL) (body : BP I) (hb : body.Closed) : (bwl I x y body).Closed :=
  ⟨callI_closed _ _ _ _, ⟨hb, callI_closed _ _ _ _⟩⟩

end Wrappers

#assert_std_axioms freeBelow_mono upd_swap upd_eq_self_of BI.R_finite BI.R_nonempty
  bcall_closed bcd_closed bwl_closed

end WP.W7k2
