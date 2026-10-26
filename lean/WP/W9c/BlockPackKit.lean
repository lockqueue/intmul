import WP.W9c.BlockPackTool
import WP.W9c.BlockPackPure

/-!
# WP.W9c.BlockPackKit — subroutine kit, registers and host stacks of the block-pack program

* `Kit`: the thirteen subroutine instances (one per W3 operation used); `Kit.OK K C`: all their
  specifications with one cost constant `C`.
* `Kit.Reg`: two symbol slots plus one register slot per subroutine; lenses `Kit.l*`.
* Host stacks `Loc 6 8`: the six named stacks of `W9c_blockPack` and eight scratch stacks
  (counter, two carries, two chunk stacks, two temporaries, sign).
* `HS`: the fourteen host stacks as a record; `HS.update_eq_set` turns `Function.update` into a
  record update, so stack states compose without function extensionality at each step.
* record-level rules `ht_*` for every call.
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

/-- The subroutine instances of the block-pack program. -/
structure Kit : Type 1 where
  /-- `W3_copyNat` -/
  iCopy : Inst 2 4 Unit
  /-- `W3_dropNat` -/
  iDrop : Inst 1 4 Unit
  /-- `W3_incNat` -/
  iInc : Inst 1 4 Unit
  /-- `W3_decNat` -/
  iDec : Inst 1 4 Unit
  /-- `W3_cmpNat` -/
  iCmp : Inst 2 4 Ordering
  /-- `W3_addNat` -/
  iAdd : Inst 3 4 Unit
  /-- `W3_subNat` -/
  iSub : Inst 3 4 Unit
  /-- `W3_shlVar` -/
  iShl : Inst 2 4 Unit
  /-- `W3_shrVar` -/
  iShr : Inst 2 4 Unit
  /-- `W3_shrConst` at `1` -/
  iShr1 : Inst 1 4 Unit
  /-- `W3_splitAt` -/
  iSplit : Inst 3 4 Unit
  /-- `W3_concatAt` -/
  iCat : Inst 3 4 Unit
  /-- `W3_subInt` -/
  iSubI : Inst 3 4 Unit

/-- All specifications, with one cost constant. -/
structure Kit.OK (K : Kit) (C : ℕ) : Prop where
  copy : SpecCopy K.iCopy C
  drop : SpecDrop K.iDrop C
  inc : SpecInc K.iInc C
  dec : SpecDec K.iDec C
  cmp : SpecCmpNat K.iCmp C
  add : SpecAdd K.iAdd C
  sub : SpecSub K.iSub C
  shl : SpecShlVar K.iShl C
  shr : SpecShrVar K.iShr C
  shr1 : SpecShrConst 1 K.iShr1 C
  split : SpecSplit K.iSplit C
  cat : SpecCat K.iCat C
  subI : SpecSubInt K.iSubI C

/-- Registers: two symbol slots, then one slot per subroutine. -/
abbrev Kit.Reg (K : Kit) : Type :=
  Option Sym × Option Sym × K.iCopy.R × K.iDrop.R × K.iInc.R × K.iDec.R × K.iCmp.R × K.iAdd.R ×
    K.iSub.R × K.iShl.R × K.iShr.R × K.iShr1.R × K.iSplit.R × K.iCat.R × K.iSubI.R

/-- Register lens `lS1`. -/
def Kit.lS1 (K : Kit) : Lens K.Reg (Option Sym) :=
  (Lens.fst _ _)

/-- Register lens `lS2`. -/
def Kit.lS2 (K : Kit) : Lens K.Reg (Option Sym) :=
  ((Lens.snd _ _).comp (Lens.fst _ _))

/-- Register lens `lCopy`. -/
def Kit.lCopy (K : Kit) : Lens K.Reg (K.iCopy.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))

/-- Register lens `lDrop`. -/
def Kit.lDrop (K : Kit) : Lens K.Reg (K.iDrop.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))

/-- Register lens `lInc`. -/
def Kit.lInc (K : Kit) : Lens K.Reg (K.iInc.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))

/-- Register lens `lDec`. -/
def Kit.lDec (K : Kit) : Lens K.Reg (K.iDec.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))

/-- Register lens `lCmp`. -/
def Kit.lCmp (K : Kit) : Lens K.Reg (K.iCmp.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))

/-- Register lens `lAdd`. -/
def Kit.lAdd (K : Kit) : Lens K.Reg (K.iAdd.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))))

/-- Register lens `lSub`. -/
def Kit.lSub (K : Kit) : Lens K.Reg (K.iSub.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))))

/-- Register lens `lShl`. -/
def Kit.lShl (K : Kit) : Lens K.Reg (K.iShl.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))))))

/-- Register lens `lShr`. -/
def Kit.lShr (K : Kit) : Lens K.Reg (K.iShr.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))))))

/-- Register lens `lShr1`. -/
def Kit.lShr1 (K : Kit) : Lens K.Reg (K.iShr1.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))))))))

/-- Register lens `lSplit`. -/
def Kit.lSplit (K : Kit) : Lens K.Reg (K.iSplit.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))))))))

/-- Register lens `lCat`. -/
def Kit.lCat (K : Kit) : Lens K.Reg (K.iCat.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))))))))))

/-- Register lens `lSubI`. -/
def Kit.lSubI (K : Kit) : Lens K.Reg (K.iSubI.R) :=
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))))))))))))))

theorem Kit.finite (K : Kit) : Finite K.Reg := by
  haveI := K.iCopy.fin; haveI := K.iDrop.fin; haveI := K.iInc.fin; haveI := K.iDec.fin
  haveI := K.iCmp.fin; haveI := K.iAdd.fin; haveI := K.iSub.fin; haveI := K.iShl.fin
  haveI := K.iShr.fin; haveI := K.iShr1.fin; haveI := K.iSplit.fin; haveI := K.iCat.fin
  haveI := K.iSubI.fin
  infer_instance

theorem Kit.nonempty (K : Kit) : Nonempty K.Reg := by
  obtain ⟨r1⟩ := K.iCopy.ne; obtain ⟨r2⟩ := K.iDrop.ne; obtain ⟨r3⟩ := K.iInc.ne
  obtain ⟨r4⟩ := K.iDec.ne; obtain ⟨r5⟩ := K.iCmp.ne; obtain ⟨r6⟩ := K.iAdd.ne
  obtain ⟨r7⟩ := K.iSub.ne; obtain ⟨r8⟩ := K.iShl.ne; obtain ⟨r9⟩ := K.iShr.ne
  obtain ⟨r10⟩ := K.iShr1.ne; obtain ⟨r11⟩ := K.iSplit.ne; obtain ⟨r12⟩ := K.iCat.ne
  obtain ⟨r13⟩ := K.iSubI.ne
  exact ⟨(none, none, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13)⟩

/-! ## Host stacks -/

/-- named: the number list `x` -/
abbrev kX : Loc 6 8 := .inl 0
/-- named: `k` -/
abbrev kK : Loc 6 8 := .inl 1
/-- named: `p_in` -/
abbrev kP : Loc 6 8 := .inl 2
/-- named: `q` -/
abbrev kQ : Loc 6 8 := .inl 3
/-- named: `W` -/
abbrev kW : Loc 6 8 := .inl 4
/-- named: the destination `d` -/
abbrev kD : Loc 6 8 := .inl 5
/-- scratch: the counter (copy of `W`) -/
abbrev kCW : Loc 6 8 := .inr 0
/-- scratch: carry of the positive chain, later its Horner accumulator -/
abbrev kCP : Loc 6 8 := .inr 1
/-- scratch: carry of the negative chain, later its Horner accumulator -/
abbrev kCN : Loc 6 8 := .inr 2
/-- scratch: chunks of the positive chain -/
abbrev kTP : Loc 6 8 := .inr 3
/-- scratch: chunks of the negative chain -/
abbrev kTN : Loc 6 8 := .inr 4
/-- scratch: temporary (`p_in + 1`, sums) -/
abbrev kU : Loc 6 8 := .inr 5
/-- scratch: temporary (shift amounts) -/
abbrev kSH : Loc 6 8 := .inr 6
/-- scratch: the sign of the current number -/
abbrev kSG : Loc 6 8 := .inr 7

/-- The host stacks as a record. -/
structure HS where
  /-- stack `x` -/
  x : List Sym
  /-- stack `k` -/
  k : List Sym
  /-- stack `p` -/
  p : List Sym
  /-- stack `q` -/
  q : List Sym
  /-- stack `w` -/
  w : List Sym
  /-- stack `d` -/
  d : List Sym
  /-- stack `cw` -/
  cw : List Sym
  /-- stack `cp` -/
  cp : List Sym
  /-- stack `cn` -/
  cn : List Sym
  /-- stack `tp` -/
  tp : List Sym
  /-- stack `tn` -/
  tn : List Sym
  /-- stack `u` -/
  u : List Sym
  /-- stack `sh` -/
  sh : List Sym
  /-- stack `sg` -/
  sg : List Sym

/-- The stack function of a record. -/
def HS.f (r : HS) : Loc 6 8 → List Sym
  | .inl ⟨0, _⟩ => r.x
  | .inl ⟨1, _⟩ => r.k
  | .inl ⟨2, _⟩ => r.p
  | .inl ⟨3, _⟩ => r.q
  | .inl ⟨4, _⟩ => r.w
  | .inl ⟨5, _⟩ => r.d
  | .inl ⟨n + 6, h⟩ => absurd h (by omega)
  | .inr ⟨0, _⟩ => r.cw
  | .inr ⟨1, _⟩ => r.cp
  | .inr ⟨2, _⟩ => r.cn
  | .inr ⟨3, _⟩ => r.tp
  | .inr ⟨4, _⟩ => r.tn
  | .inr ⟨5, _⟩ => r.u
  | .inr ⟨6, _⟩ => r.sh
  | .inr ⟨7, _⟩ => r.sg
  | .inr ⟨n + 8, h⟩ => absurd h (by omega)

/-- Record update at a host stack. -/
def HS.set (r : HS) (j : Loc 6 8) (l : List Sym) : HS :=
  match j with
  | .inl ⟨0, _⟩ => { r with x := l }
  | .inl ⟨1, _⟩ => { r with k := l }
  | .inl ⟨2, _⟩ => { r with p := l }
  | .inl ⟨3, _⟩ => { r with q := l }
  | .inl ⟨4, _⟩ => { r with w := l }
  | .inl ⟨5, _⟩ => { r with d := l }
  | .inl ⟨n + 6, h⟩ => absurd h (by omega)
  | .inr ⟨0, _⟩ => { r with cw := l }
  | .inr ⟨1, _⟩ => { r with cp := l }
  | .inr ⟨2, _⟩ => { r with cn := l }
  | .inr ⟨3, _⟩ => { r with tp := l }
  | .inr ⟨4, _⟩ => { r with tn := l }
  | .inr ⟨5, _⟩ => { r with u := l }
  | .inr ⟨6, _⟩ => { r with sh := l }
  | .inr ⟨7, _⟩ => { r with sg := l }
  | .inr ⟨n + 8, h⟩ => absurd h (by omega)

theorem HS.update_eq_set (r : HS) (j : Loc 6 8) (l : List Sym) :
    Function.update r.f j l = (r.set j l).f := by
  funext i
  rcases j with ⟨_ | _ | _ | _ | _ | _ | n, hn⟩ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hn⟩ <;>
    rcases i with ⟨_ | _ | _ | _ | _ | _ | m, hm⟩ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | m, hm⟩ <;>
    first | rfl | omega

theorem HS.f_ext (r : HS) : HS.mk (r.f kX) (r.f kK) (r.f kP) (r.f kQ) (r.f kW) (r.f kD) (r.f kCW)
    (r.f kCP) (r.f kCN) (r.f kTP) (r.f kTN) (r.f kU) (r.f kSH) (r.f kSG) = r := rfl

/-- Any stack function is the function of its record. -/
theorem HS.of_fun (S : Loc 6 8 → List Sym) :
    S = (HS.mk (S kX) (S kK) (S kP) (S kQ) (S kW) (S kD) (S kCW) (S kCP) (S kCN) (S kTP) (S kTN)
      (S kU) (S kSH) (S kSG)).f := by
  funext i
  rcases i with ⟨_ | _ | _ | _ | _ | _ | m, hm⟩ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | m, hm⟩ <;>
    first | rfl | omega

#assert_std_axioms Kit.finite Kit.nonempty HS.update_eq_set HS.f_ext HS.of_fun

end WP.W9c.BlockPack
