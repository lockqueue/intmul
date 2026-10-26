/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractKit
import SubNLogN.Machine.AppC.C5StreamArith
import WP.W6a.DivMod

/-!
# Lemma A.9 extraction, part 3: the concrete arithmetic kit (`Machine/AppC/C7ExtractInst.lean`)

`natKit K : XKit K` (the kit of `C7ExtractKit.lean`) for any stack type `K`:
* `add`, `sub`, `mul`: the shared `NatArith` programs `addN`, `subN`, `mulN`
  (`Machine/AppC/C5StreamArith.lean`), through the register lens `klN`;
* `cmp`: `Lib.cmpNum` through `klC` (spec from `Lib.cmpNum_eval`);
* `dm`: the W6a divider `WP.W6a.divModProg` over the W3 subtractor `WP.W3.addSubProg subBit`,
  embedded with `callInj` (spec from `WP.W6a.divModProg_spec`).
All temporaries are restored and may hold arbitrary content (restored convention). The uniform
cost constant is `110`. Everything here is proved (no `sorry`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Register file of the concrete kit: `NatArith`'s registers and the W6a divider's. -/
abbrev KReg : Type := NatArith.Reg × WP.W6a.DReg WP.W3.AReg

/-- Lens to the `NatArith` registers. -/
def klN : Lens KReg NatArith.Reg := Lens.fst _ _
/-- Lens to the divider registers. -/
def klD : Lens KReg (WP.W6a.DReg WP.W3.AReg) := Lens.snd _ _
/-- Lens to the one-symbol work register. -/
def klW : Lens KReg (Option Sym) := klN.comp NatArith.lW
/-- Lens to the compare register. -/
def klC : Lens KReg CReg := klN.comp NatArith.lC

/-- The concrete divider. -/
abbrev divProg : Prog WP.W6a.DStk (fun _ => Sym) (WP.W6a.DReg WP.W3.AReg) :=
  WP.W6a.divModProg (WP.W3.addSubProg WP.W3.subBit)

/-- The W3 subtraction spec of the concrete subtractor (constant `20`). -/
theorem subSpec_sub : WP.W6a.SubSpec 20 (WP.W3.addSubProg WP.W3.subBit) := by
  intro a b rx ry S hrx hry hab hx hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := WP.W3.addSubProg_eval WP.W3.subBit (encodeNat a) (encodeNat b) rx ry
    hrx hry S hx hy v
  have hle : bitsVal (encodeNat b) ≤ bitsVal (encodeNat a) := by
    rw [bitsVal_encodeNat, bitsVal_encodeNat]
    exact hab
  have hval : bitsVal (WP.W3.rip WP.W3.subBit (max (encodeNat a).length (encodeNat b).length)
      false (encodeNat a) (encodeNat b)) = a - b := by
    rw [WP.W3.bitsVal_rip_sub (max (encodeNat a).length (encodeNat b).length) (encodeNat a)
      (encodeNat b) (le_max_left _ _) (le_max_right _ _) hle, bitsVal_encodeNat,
      bitsVal_encodeNat]
  rw [hval] at e
  refine ⟨v', t, e, trivial, ?_⟩
  simp only [bitLen]
  omega

/-- Embedding of the seven stacks of the divider (`a, b, q, r` and three temporaries). -/
def dmEmb {K : Type} (x y q r d0 d1 d2 : K) : Loc 4 3 → K
  | .inl i => if i.val = 0 then x else if i.val = 1 then y else if i.val = 2 then q else r
  | .inr i => if i.val = 0 then d0 else if i.val = 1 then d1 else d2

theorem dmEmb_injective {K : Type} {x y q r d0 d1 d2 : K} (h : [x, y, q, r, d0, d1, d2].Nodup) :
    Function.Injective (dmEmb x y q r d0 d1 d2) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨hxy, hxq, hxr, hx0, hx1, hx2⟩, ⟨hyq, hyr, hy0, hy1, hy2⟩, ⟨hqr, hq0, hq1, hq2⟩,
    ⟨hr0, hr1, hr2⟩, ⟨h01, h02⟩, h12⟩ := h
  intro u v huv
  rcases u with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases v with ⟨b, hb⟩ | ⟨b, hb⟩
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp_all
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    simp_all
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp_all
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    simp_all

section Specs

variable {K : Type} [DecidableEq K]

theorem runs_dmK {x y q r d0 d1 d2 : K} (h : [x, y, q, r, d0, d1, d2].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hb : 0 < b) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (callInj (dmEmb x y q r d0 d1 d2) klD divProg) S
      (Function.update (Function.update S q (natSyms (a / b) ++ S q)) r
        (natSyms (a % b) ++ S r))
      (fun _ => True) (110 * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) := by
  have hι := dmEmb_injective h
  refine runs_callInj hι klD (Q := fun _ => True) ?_ ?_
  · have e1 : (Function.update (Function.update S q (natSyms (a / b) ++ S q)) r
        (natSyms (a % b) ++ S r)) ∘ dmEmb x y q r d0 d1 d2 =
        Function.update ((Function.update S q (natSyms (a / b) ++ S q)) ∘
          dmEmb x y q r d0 d1 d2) WP.W6a.sR (natSyms (a % b) ++ S r) :=
      Function.update_comp_eq_of_injective _ hι WP.W6a.sR _
    have e2 : (Function.update S q (natSyms (a / b) ++ S q)) ∘ dmEmb x y q r d0 d1 d2 =
        Function.update (S ∘ dmEmb x y q r d0 d1 d2) WP.W6a.sQ (natSyms (a / b) ++ S q) :=
      Function.update_comp_eq_of_injective _ hι WP.W6a.sQ _
    rw [e1, e2]
    exact WP.W6a.divModProg_spec (by norm_num) subSpec_sub a b rx ry _ hb hrx hry hx hy
  · intro k hk
    rw [Function.update_of_ne, Function.update_of_ne]
    · intro hkq
      exact hk (.inl 2) hkq.symm
    · intro hkr
      exact hk (.inl 3) hkr.symm

theorem runs_cmpK {x y t1 t2 : K} (h : [x, y, t1, t2].Nodup) (a b : ℕ) (rx ry : List Sym)
    (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S x = natSyms a ++ rx)
    (hy : S y = natSyms b ++ ry) :
    Runs ((cmpNum x y t1 t2).liftRegs klC) S S (fun v => (klC.get v).2.2 = Lib.ordOf a b)
      (15 * (bitLen a + bitLen b + 1)) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨hxy, hx1, hx2⟩, ⟨hy1, hy2⟩, h12⟩ := h
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  have e := cmpNum_eval hxy hx1 hx2 hy1 hy2 h12 (klC.get v) (encodeNat a) (encodeNat b) rx ry stk
    hrx hry hx hy
  refine ⟨⟨klC.set v _, stk⟩, _, Eval.liftRegs klC e v rfl, ⟨rfl, ?_⟩, ?_⟩
  · show (klC.get (klC.set v _)).2.2 = _
    rw [klC.get_set]
    show cmpAll .eq (encodeNat a) (encodeNat b) = _
    rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
      bitsVal_encodeNat]
  · have := Nat.min_le_left (encodeNat a).length (encodeNat b).length
    simp only [bitLen]
    omega

end Specs

/-- **The concrete arithmetic kit** over any stack type `K`. -/
def natKit (K : Type) [DecidableEq K] : XKit K where
  R := KReg
  finR := inferInstance
  neR := ⟨((none, (none, none, false), (none, none, .eq)), (none, false, (none, none, .eq),
    (none, none, false)))⟩
  lw := klW
  obs := fun v => (klC.get v).2.2
  c := 110
  add x y z t1 t2 t3 := (NatArith.addN x y z t1 t2 t3).liftRegs klN
  sub x y z t1 t2 t3 := (NatArith.subN x y z t1 t2 t3).liftRegs klN
  mul x y z A Bs Acc T := (NatArith.mulN x y z A Bs Acc T).liftRegs klN
  cmp x y t1 t2 := (cmpNum x y t1 t2).liftRegs klC
  dm x y q r d0 d1 d2 := callInj (dmEmb x y q r d0 d1 d2) klD divProg
  add_closed _ _ _ _ _ _ := WP.W9comp.closed_liftRegs _ (NatArith.closed_addN _ _ _ _ _ _)
  sub_closed _ _ _ _ _ _ := WP.W9comp.closed_liftRegs _ (NatArith.closed_subN _ _ _ _ _ _)
  mul_closed _ _ _ _ _ _ _ := WP.W9comp.closed_liftRegs _ (NatArith.closed_mulN _ _ _ _ _ _ _)
  cmp_closed _ _ _ _ := WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
  dm_closed _ _ _ _ _ _ _ := closed_callInj _ _
    (WP.W6a.divModProg_closed _ (WP.W3.addSubProg_closed _))
  add_spec h a b rx ry S hrx hry hx hy :=
    WP.W9comp.runs_mono (WP.W0m.runs_liftRegs klN
      (NatArith.runs_addN h a b rx ry S hrx hry hx hy)) (fun _ _ => trivial)
      (Nat.mul_le_mul_right _ (by norm_num))
  sub_spec h a b rx ry S hrx hry hab hx hy :=
    WP.W9comp.runs_mono (WP.W0m.runs_liftRegs klN
      (NatArith.runs_subN h a b rx ry S hrx hry hab hx hy)) (fun _ _ => trivial)
      (Nat.mul_le_mul_right _ (by norm_num))
  mul_spec h a b rx ry S hrx hry hx hy :=
    WP.W9comp.runs_mono (WP.W0m.runs_liftRegs klN
      (NatArith.runs_mulN h a b rx ry S hrx hry hx hy)) (fun _ _ => trivial)
      (by unfold NatArith.mulCost; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by norm_num))
  cmp_spec h a b rx ry S hrx hry hx hy :=
    WP.W9comp.runs_mono (runs_cmpK h a b rx ry S hrx hry hx hy) (fun _ h => h)
      (Nat.mul_le_mul_right _ (by norm_num))
  dm_spec h a b rx ry S hb hrx hry hx hy := runs_dmK h a b rx ry S hb hrx hry hx hy

end SubNLogN.Machine.AppC.C7ExtractAux
