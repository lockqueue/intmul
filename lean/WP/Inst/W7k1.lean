import WP.Inst.W6a
import WP.W7k1.Isqrt
import WP.W7k1.LnDefs

/-!
# WP.Inst.W7k1 — concrete W7 kernels (isqrt, log2Scaled, piScaled) and `WP.W7k2.Inst` records

Same convention as `WP.Inst.W3`.
* `isqrt`: `WP.W7k1.isqrtProg` (closed, no subroutines); `isqrt.ok : W7_isqrt` for exactly this def.
* `<c>.inst : WP.W7k2.Inst n cap O`: the record form of every W3/W6a/W7k1 instance, as the call-layer
  kernels (W7k1, W7k2, W7k3) take them.
* `lnJ : WP.W7k1.LnInst` and `piJ : WP.W7k1.PiInst`: the twelve subroutines of the `ln 2` and `π` kernels,
  all from `WP.Inst` (`div` = `divModNat`, `isq` = `isqrt`).
* `log2Scaled.prog := WP.W7k1.lnProg lnJ`, `piScaled.prog := WP.W7k1.piProg piJ` (host `Loc 2 16`).
  The `ok` theorems for these two composite kernels would need per-instance `Spec*` lemmas; not done.
-/

namespace WP.Inst

open TMFw TMFw.Lib TMFw.Contracts Computability

namespace isqrt
abbrev m : ℕ := 6
abbrev R : Type := WP.W7k1.IReg
def r0 : R := (none, none, false)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 2 m) (fun _ => Sym) R := WP.W7k1.isqrtProg
theorem closed : prog.Closed := WP.W7k1.isqrtProg_closed
end isqrt

theorem isqrt.ok : W7_isqrt := by
  refine ⟨200, fun _ => ⟨6, WP.W7k1.IReg, fun _ => (), isqrt.prog, by decide, inferInstance,
    ⟨isqrt.r0⟩, isqrt.closed, ?_⟩⟩
  intro a ra S hra hA
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := WP.W7k1.isqrtProg_eval a ra v S hra hA
  exact ⟨v', t, e, trivial, ht⟩

/-! ## Instance records -/

def copyNat.inst : WP.W7k2.Inst 2 4 Unit :=
  ⟨copyNat.m, copyNat.R, copyNat.obs, copyNat.prog, by decide, inferInstance, ⟨copyNat.r0⟩,
    copyNat.closed⟩
def cmpNat.inst : WP.W7k2.Inst 2 4 Ordering :=
  ⟨cmpNat.m, cmpNat.R, cmpNat.obs, cmpNat.prog, by decide, inferInstance, ⟨cmpNat.r0⟩, cmpNat.closed⟩
def isZeroNat.inst : WP.W7k2.Inst 1 4 Bool :=
  ⟨isZeroNat.m, isZeroNat.R, isZeroNat.obs, isZeroNat.prog, by decide, inferInstance,
    ⟨isZeroNat.r0⟩, isZeroNat.closed⟩
def incNat.inst : WP.W7k2.Inst 1 4 Unit :=
  ⟨incNat.m, incNat.R, incNat.obs, incNat.prog, by decide, inferInstance, ⟨incNat.r0⟩, incNat.closed⟩
def decNat.inst : WP.W7k2.Inst 1 4 Unit :=
  ⟨decNat.m, decNat.R, decNat.obs, decNat.prog, by decide, inferInstance, ⟨decNat.r0⟩, decNat.closed⟩
def addNat.inst : WP.W7k2.Inst 3 4 Unit :=
  ⟨addNat.m, addNat.R, addNat.obs, addNat.prog, by decide, inferInstance, ⟨addNat.r0⟩, addNat.closed⟩
def subNat.inst : WP.W7k2.Inst 3 4 Unit :=
  ⟨subNat.m, subNat.R, subNat.obs, subNat.prog, by decide, inferInstance, ⟨subNat.r0⟩, subNat.closed⟩
def dropNat.inst : WP.W7k2.Inst 1 4 Unit :=
  ⟨dropNat.m, dropNat.R, dropNat.obs, dropNat.prog, by decide, inferInstance, ⟨dropNat.r0⟩,
    dropNat.closed⟩
def normNat.inst : WP.W7k2.Inst 1 4 Unit :=
  ⟨normNat.m, normNat.R, normNat.obs, normNat.prog, by decide, inferInstance, ⟨normNat.r0⟩,
    normNat.closed⟩
def splitAt.inst : WP.W7k2.Inst 3 4 Unit :=
  ⟨splitAt.m, splitAt.R, splitAt.obs, splitAt.prog, by decide, inferInstance, ⟨splitAt.r0⟩,
    splitAt.closed⟩
def concatAt.inst : WP.W7k2.Inst 3 4 Unit :=
  ⟨concatAt.m, concatAt.R, concatAt.obs, concatAt.prog, by decide, inferInstance, ⟨concatAt.r0⟩,
    concatAt.closed⟩
def shrVar.inst : WP.W7k2.Inst 2 4 Unit :=
  ⟨shrVar.m, shrVar.R, shrVar.obs, shrVar.prog, by decide, inferInstance, ⟨shrVar.r0⟩, shrVar.closed⟩
def shlVar.inst : WP.W7k2.Inst 2 4 Unit :=
  ⟨shlVar.m, shlVar.R, shlVar.obs, shlVar.prog, by decide, inferInstance, ⟨shlVar.r0⟩, shlVar.closed⟩
def shlConst.inst (k : ℕ) : WP.W7k2.Inst 1 4 Unit :=
  ⟨shlConst.m, shlConst.R, shlConst.obs, shlConst.prog k, by decide, inferInstance, ⟨shlConst.r0⟩,
    shlConst.closed k⟩
def shrConst.inst (k : ℕ) : WP.W7k2.Inst 1 4 Unit :=
  ⟨shrConst.m, shrConst.R, shrConst.obs, shrConst.prog k, by decide, inferInstance, ⟨shrConst.r0⟩,
    shrConst.closed k⟩
def divModNat.inst : WP.W7k2.Inst 4 6 Unit :=
  ⟨divModNat.m, divModNat.R, divModNat.obs, divModNat.prog, by decide, inferInstance,
    ⟨divModNat.r0⟩, divModNat.closed⟩
def divRound.inst : WP.W7k2.Inst 3 6 Unit :=
  ⟨divRound.m, divRound.R, divRound.obs, divRound.prog, by decide, inferInstance, ⟨divRound.r0⟩,
    divRound.closed⟩
def isqrt.inst : WP.W7k2.Inst 2 16 Unit :=
  ⟨isqrt.m, isqrt.R, isqrt.obs, isqrt.prog, by decide, inferInstance, ⟨isqrt.r0⟩, isqrt.closed⟩

/-! ## The `ln 2` and `π` kernels -/

/-- The subroutines of `W7_log2Scaled`. -/
def lnJ : WP.W7k1.LnInst :=
  ⟨copyNat.inst, incNat.inst, shlConst.inst 1, shlVar.inst, addNat.inst, subNat.inst, shrVar.inst,
    shrConst.inst 1, dropNat.inst, isZeroNat.inst, decNat.inst, divModNat.inst⟩

/-- The subroutines of `W7_piScaled`. -/
def piJ : WP.W7k1.PiInst :=
  ⟨copyNat.inst, incNat.inst, shlConst.inst 1, shlVar.inst, addNat.inst, subNat.inst, shrVar.inst,
    shrConst.inst 1, dropNat.inst, isZeroNat.inst, decNat.inst, isqrt.inst⟩

namespace log2Scaled
abbrev m : ℕ := 16
abbrev R : Type := copyNat.R × incNat.R × shlConst.R × shlVar.R × addNat.R × subNat.R × shrVar.R ×
  shrConst.R × dropNat.R × isZeroNat.R × decNat.R × divModNat.R
def r0 : R := (copyNat.r0, incNat.r0, shlConst.r0, shlVar.r0, addNat.r0, subNat.r0, shrVar.r0,
  shrConst.r0, dropNat.r0, isZeroNat.r0, decNat.r0, divModNat.r0)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 2 m) (fun _ => Sym) R := WP.W7k1.lnProg lnJ
theorem closed : prog.Closed := WP.W7k1.lnProg_closed lnJ
def inst : WP.W7k2.Inst 2 16 Unit := ⟨m, R, obs, prog, le_refl _, inferInstance, ⟨r0⟩, closed⟩
end log2Scaled

namespace piScaled
abbrev m : ℕ := 16
abbrev R : Type := copyNat.R × incNat.R × shlConst.R × shlVar.R × addNat.R × subNat.R × shrVar.R ×
  shrConst.R × dropNat.R × isZeroNat.R × decNat.R × isqrt.R
def r0 : R := (copyNat.r0, incNat.r0, shlConst.r0, shlVar.r0, addNat.r0, subNat.r0, shrVar.r0,
  shrConst.r0, dropNat.r0, isZeroNat.r0, decNat.r0, isqrt.r0)
def obs : R → Unit := fun _ => ()
def prog : Prog (Loc 2 m) (fun _ => Sym) R := WP.W7k1.piProg piJ
theorem closed : prog.Closed := WP.W7k1.piProg_closed piJ
def inst : WP.W7k2.Inst 2 16 Unit := ⟨m, R, obs, prog, le_refl _, inferInstance, ⟨r0⟩, closed⟩
end piScaled

end WP.Inst
