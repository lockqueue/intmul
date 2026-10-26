import WP.W0m.Steps

/-!
# WP.W0m.Work — the input stage's work program over local stacks

After copy-in, the work stack `inp` holds the input reversed: `bits(b)` MSB first, `sep`, then
`bits(a)` MSB first (`inputSyms`). The work program then runs eight phases:

| Phase | Effect (values on stacks, `natSyms` LSB on top) |
|---|---|
| A parse | `ob := b`, `oa := a` (two `moveBits`; `inp` empties) |
| B lengths | `la := bitLen a`, `lb := bitLen b` (`countBits`) |
| C `n` | `nn := max 1 (max la lb)` (`cmpNum`, `copyBlock`, `zeroTest`/`inc`); drop `la`, `lb` |
| D `b` | `bb := max 1 (bitLen n − 1)` (`countBits`, `dec`, `zeroTest`/`inc`) |
| E `k` | `kk := n / b + 1` (W6a `divMod` → `kk`, `rr`; drop `rr`; `inc`) |
| F `K0` | `k0 := max 4 (bitLen k + 2)` (`countBits`, `inc`², push the constant 4, `cmpNum`); drop `c4` |
| G `L` | `lf := bitLen (K0 − 1) − 1` (copy, `dec`, `countBits`, `dec`); drop `t1` |
| H `p0` | `p0 := 2·(b + K0 + 3)` (W3 `add`, `inc`³, copy, W3 `add`); drop `t2`, `t3` |

The program is parametrized by the W3 adder and W6a divider programs. They act on their own local
stacks `Loc n m` and are embedded at their call sites with `embL` (named stacks, plus the scratch
stacks `s i`). Every library macro runs through a register lens into
`Regs Ra Rd = Option Sym × CReg × Ra × Rd`.
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts

/-- Local work stacks of the input stage. -/
inductive Stk
  | inp | oa | ob | la | lb | nn | bb | kk | k0 | lf | p0 | rr | t1 | t2 | t3 | c4
  | tm | ct | cs | x0 | x1
  | s (i : Fin 6)
  deriving DecidableEq, Fintype

/-- Registers: the library macros' symbol register, the comparator's registers, and the private
registers of the adder and divider instances. -/
abbrev Regs (Ra Rd : Type) := Option Sym × CReg × Ra × Rd

/-- Lens: symbol register. -/
def lS {Ra Rd : Type} : Lens (Regs Ra Rd) (Option Sym) := Lens.fst _ _
/-- Lens: comparator registers. -/
def lC {Ra Rd : Type} : Lens (Regs Ra Rd) CReg := (Lens.snd _ _).comp (Lens.fst _ _)
/-- Lens: adder registers. -/
def lA {Ra Rd : Type} : Lens (Regs Ra Rd) Ra :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Lens: divider registers. -/
def lD {Ra Rd : Type} : Lens (Regs Ra Rd) Rd :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))

/-- Scratch stacks of an embedded contract instance. -/
def scr {m : ℕ} (hm : m ≤ 6) : Fin m → Stk := fun j => Stk.s (Fin.castLE hm j)

theorem scr_inj {m : ℕ} (hm : m ≤ 6) : Function.Injective (scr hm) := by
  intro i j h
  simp only [scr, Stk.s.injEq] at h
  exact Fin.castLE_inj.mp h

/-- Named stacks of an adder call site. -/
def nm3 (x y z : Stk) : Fin 3 → Stk := fun i => if i.val = 0 then x else if i.val = 1 then y else z

/-- Named stacks of the divider call site. -/
def nm4 (w x y z : Stk) : Fin 4 → Stk := fun i =>
  if i.val = 0 then w else if i.val = 1 then x else if i.val = 2 then y else z

/-- The work programs, over registers `Regs Ra Rd`. -/
abbrev WProg (Ra Rd : Type) := Prog Stk (fun _ => Sym) (Regs Ra Rd)

section Programs

variable {ma md : ℕ} {Ra Rd : Type}

/-- A symbol-register macro inside the work program. -/
def sym (p : SProg Stk) : WProg Ra Rd := p.liftRegs lS

/-- Comparator on `x`, `y` (temporaries `x0`, `x1`). -/
def cmpW (x y : Stk) : WProg Ra Rd := (cmpNum x y .x0 .x1).liftRegs lC

/-- Adder call: `z += x + y`. -/
def addW (Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra) (hma : ma ≤ 6) (x y z : Stk) : WProg Ra Rd :=
  (Padd.mapStk (embL (nm3 x y z) (scr hma))).liftRegs lA

/-- Divider call: `kk += nn / bb`, `rr += nn % bb`. -/
def divW (Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd) (hmd : md ≤ 6) : WProg Ra Rd :=
  (Pdiv.mapStk (embL (nm4 .nn .bb .kk .rr) (scr hmd))).liftRegs lD

/-- Branch: the comparator said `lt`. -/
def isLt (v : Regs Ra Rd) : Bool := decide ((lC.get v).2.2 = .lt)

/-- Branch: the symbol register holds a bit (a nonzero number was peeked). -/
def symIsBit (v : Regs Ra Rd) : Bool := optIsBit (lS.get v)

/-- Phase A: parse `inp` into `ob`, `oa`. -/
def phA : WProg Ra Rd := .seq (sym (moveBits .inp .ob)) (sym (moveBits .inp .oa))

/-- Phase B: bit lengths. -/
def phB : WProg Ra Rd :=
  .seq (sym (countBits .oa .cs .tm .la .ct)) (sym (countBits .ob .cs .tm .lb .ct))

/-- Phase C: `nn := max 1 (max la lb)`; drop `la`, `lb`. -/
def phC : WProg Ra Rd :=
  .seq (.seq (cmpW .la .lb) (.ite isLt (sym (copyBlock .lb .nn .tm)) (sym (copyBlock .la .nn .tm))))
    (.seq (sym (dropNat .la)) (.seq (sym (dropNat .lb))
      (.seq (sym (zeroTest .nn)) (.ite symIsBit (sym skip) (sym (inc .nn .ct))))))

/-- Phase D: `bb := max 1 (bitLen nn − 1)`. -/
def phD : WProg Ra Rd :=
  .seq (sym (countBits .nn .cs .tm .bb .ct)) (.seq (sym (dec .bb .ct))
    (.seq (sym (zeroTest .bb)) (.ite symIsBit (sym skip) (sym (inc .bb .ct)))))

/-- Phase E: `kk := nn / bb + 1` (divider), drop the remainder. -/
def phE (Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd) (hmd : md ≤ 6) : WProg Ra Rd :=
  .seq (divW Pdiv hmd) (.seq (sym (dropNat .rr)) (sym (inc .kk .ct)))

/-- Phase F: `k0 := max 4 (bitLen kk + 2)`. -/
def phF : WProg Ra Rd :=
  .seq (sym (countBits .kk .cs .tm .k0 .ct)) (.seq (sym (inc .k0 .ct)) (.seq (sym (inc .k0 .ct))
    (.seq (sym (pushC .c4 (.bit true))) (.seq (sym (pushC .c4 (.bit false)))
      (.seq (sym (pushC .c4 (.bit false)))
        (.seq (.seq (cmpW .k0 .c4)
            (.ite isLt (.seq (sym (dropNat .k0)) (sym (copyBlock .c4 .k0 .tm))) (sym skip)))
          (sym (dropNat .c4))))))))

/-- Phase G: `lf := bitLen (k0 − 1) − 1`. -/
def phG : WProg Ra Rd :=
  .seq (sym (copyBlock .k0 .t1 .tm)) (.seq (sym (dec .t1 .ct))
    (.seq (sym (countBits .t1 .cs .tm .lf .ct)) (.seq (sym (dec .lf .ct)) (sym (dropNat .t1)))))

/-- Phase H: `p0 := 2·(bb + k0 + 3)`. -/
def phH (Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra) (hma : ma ≤ 6) : WProg Ra Rd :=
  .seq (addW Padd hma .bb .k0 .t2) (.seq (sym (inc .t2 .ct)) (.seq (sym (inc .t2 .ct))
    (.seq (sym (inc .t2 .ct)) (.seq (sym (copyBlock .t2 .t3 .tm))
      (.seq (addW Padd hma .t2 .t3 .p0) (.seq (sym (dropNat .t2)) (sym (dropNat .t3))))))))

/-- **The work program.** -/
def workProg (Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra) (hma : ma ≤ 6)
    (Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd) (hmd : md ≤ 6) : WProg Ra Rd :=
  .seq phA (.seq phB (.seq phC (.seq phD (.seq (phE Pdiv hmd) (.seq phF (.seq phG (phH Padd hma)))))))

end Programs

/-- The input as it lies on `inp` after copy-in. -/
def inputSyms (a b : ℕ) : List Sym :=
  (encodeNat b).reverse.map Sym.bit ++ Sym.sep :: (encodeNat a).reverse.map Sym.bit

theorem natSyms_four : natSyms 4 = [Sym.bit false, Sym.bit false, Sym.bit true] := by
  show natSyms (0 + 1 + 1 + 1 + 1) = _
  rw [natSyms, encodeNat_succ, encodeNat_succ, encodeNat_succ, encodeNat_succ, encodeNat_zero]
  rfl

#assert_std_axioms scr_inj natSyms_four

end WP.W0m
