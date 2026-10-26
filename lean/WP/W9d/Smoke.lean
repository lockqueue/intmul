import WP.W9d.Final
import WP.W9dR.Smoke

/-!
# WP.W9d.Smoke — compiled runs of the twist kernels (test subroutines; test only)

The seven instances are **test-only, unverified** programs with finite registers:
* `mul`: `tMul`, a quadratic signed multiplier (count `|x|` down, adding `|y|` by increments; signs
  saved on a scratch stack and restored);
* `add`, `sub`: W3b's signed glue `addSubProg` over its test adder (`WP.W9dR.Smoke.tAdd`, flip);
* `rnd`: W9dR's round shift `rsProg` over its test instances (`WP.W9dR.Smoke.tJ`);
* `cp`, `shl1`, `inc`: framework `copyBlock`, "push a 0 bit on a nonzero number", framework `inc`.

`runTw` preloads the twiddle table on `TR` and the PRE header on `C0`, then runs
`kernel tJw stp` from `W0 = matSyms U` (W3b's `runMach`: Mathlib's `TM2.step` on the compiled
machine). The `#guard`s check `W0 = matSyms (w9P …)` / `matSyms (w9QPost …)` and
`TL = reverse (twSyms 2 tw)` on a `2 × 2` matrix. The step counts are printed next to the proved
bound `(17·D + 150)·twistBound` at `D = 50`, `Mul w = (w+1)²` (the test subroutines are not linear,
so this comparison is indicative only).
-/

namespace WP.W9d.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 WP.W9d TMFw.W3b TMFw.W3b.Smoke

/-- Push `neg` if the number on `z` is nonzero, else `pos`. -/
def tNegOrPos : SProg (Loc 3 5) :=
  .seq (peekR (.inl 2)) (.ite optIsBit (pushC (.inl 2) .neg) (pushC (.inl 2) .pos))

/-- **Test only, unverified, quadratic** signed multiplier `z += x·y` (scratch `t0..t4`). -/
def tMul : SProg (Loc 3 5) :=
  .seq (popR (.inl 0)) (.seq (pushR (.inr 3)) (.seq (popR (.inl 1)) (.seq (pushR (.inr 3))
  (.seq (pushC (.inr 0) .mark)
  (.seq (pushC (.inr 1) .mark) (.seq (copyBlock (.inl 0) (.inr 1) (.inr 4))
  (.seq (peekR (.inr 1)) (.seq (.loop optIsBit
      (.seq (pushC (.inr 2) .mark) (.seq (copyBlock (.inl 1) (.inr 2) (.inr 4))
      (.seq (peekR (.inr 2)) (.seq (.loop optIsBit (.seq (dec (.inr 2) (.inr 4))
        (.seq (inc (.inr 0) (.inr 4)) (peekR (.inr 2)))))
      (.seq (popR (.inr 2)) (.seq (dec (.inr 1) (.inr 4)) (peekR (.inr 1)))))))))
  (.seq (popR (.inr 1))
  (.seq (reverseBlock (.inr 0) (.inr 1) (.inr 2)) (.seq (moveBlock (.inr 0) (.inl 2))
  (.seq (popR (.inr 0))
  (.seq (popR (.inr 3)) (.seq (pushR (.inl 1))
  (.ite (fun r => decide (r = some .neg))
     (.seq (popR (.inr 3)) (.seq (pushR (.inl 0))
       (.ite (fun r => decide (r = some .neg)) (pushC (.inl 2) .pos) tNegOrPos)))
     (.seq (popR (.inr 3)) (.seq (pushR (.inl 0))
       (.ite (fun r => decide (r = some .neg)) tNegOrPos (pushC (.inl 2) .pos)))))))))))))))))))

/-- Test signed subtraction (W3b glue, flipped). -/
def tSub : Prog (Loc 3 4) (fun _ => Sym) (RegA (Option Sym) (Option Sym) CReg) :=
  addSubProg (le_refl 4) (le_refl 4) (by decide : 2 ≤ 4) (fun r : CReg => r.2.2) (tAddSub false)
    (tAddSub true) (cmpNum (.inl 0) (.inl 1) (.inr 0) (.inr 1)) true

/-- Test `shlConst 1`. -/
def tShl1 : SProg (Loc 1 0) := .seq (peekR (.inl 0)) (.ite optIsBit (pushC (.inl 0) (.bit false)) skip)

theorem tJ_finite : Finite WP.W9dR.Smoke.tJ.Reg := by
  haveI := WP.W9dR.Smoke.tJ.shlV.fin; haveI := WP.W9dR.Smoke.tJ.shr1.fin
  haveI := WP.W9dR.Smoke.tJ.n2i.fin; haveI := WP.W9dR.Smoke.tJ.add.fin
  haveI := WP.W9dR.Smoke.tJ.sgn.fin; haveI := WP.W9dR.Smoke.tJ.shrV.fin
  haveI := WP.W9dR.Smoke.tJ.dec.fin; haveI := WP.W9dR.Smoke.tJ.inc.fin
  haveI := WP.W9dR.Smoke.tJ.copy.fin; haveI := WP.W9dR.Smoke.tJ.drop.fin
  infer_instance

theorem tJ_nonempty : Nonempty WP.W9dR.Smoke.tJ.Reg := ⟨WP.W9dR.Smoke.σ0⟩

/-- The test instances. -/
def tJw : TwInst where
  mul := ⟨5, Option Sym, fun _ => (), tMul, by norm_num, inferInstance, inferInstance,
    WP.W9dR.Smoke.freeBelow_of_noRecur _ 0 rfl⟩
  add := ⟨4, RegA (Option Sym) (Option Sym) CReg, fun _ => (), WP.W9dR.Smoke.tAdd, le_rfl,
    inferInstance, inferInstance, WP.W9dR.Smoke.freeBelow_of_noRecur _ 0 rfl⟩
  sub := ⟨4, RegA (Option Sym) (Option Sym) CReg, fun _ => (), tSub, le_rfl, inferInstance,
    inferInstance, WP.W9dR.Smoke.freeBelow_of_noRecur _ 0 rfl⟩
  rnd := ⟨6, WP.W9dR.Smoke.tJ.Reg, fun _ => (), WP.W9dR.rsProg WP.W9dR.Smoke.tJ, le_rfl,
    tJ_finite, tJ_nonempty, WP.W9dR.rsProg_closed _⟩
  cp := ⟨1, Option Sym, fun _ => (), copyBlock (.inl 0) (.inl 1) (.inr 0), by norm_num,
    inferInstance, inferInstance, WP.W9dR.Smoke.freeBelow_of_noRecur _ 0 rfl⟩
  shl1 := ⟨0, Option Sym, fun _ => (), tShl1, by norm_num, inferInstance, inferInstance,
    WP.W9dR.Smoke.freeBelow_of_noRecur _ 0 rfl⟩
  inc := ⟨1, Option Sym, fun _ => (), inc (.inl 0) (.inr 0), by norm_num, inferInstance,
    inferInstance, WP.W9dR.Smoke.freeBelow_of_noRecur _ 0 rfl⟩

/-- Initial registers. -/
def σ0 : tJw.Reg :=
  ((none : Option Sym),
    ((none, none, none, none, (none, none, .eq)) : RegA (Option Sym) (Option Sym) CReg),
    ((none, none, none, none, (none, none, .eq)) : RegA (Option Sym) (Option Sym) CReg),
    WP.W9dR.Smoke.σ0, (none : Option Sym), (none : Option Sym), (none : Option Sym),
    (none : Option Sym))

/-- Preload the twiddle table and the header, then the twist kernel. -/
def twShow (pre : Bool) (pSub : ℕ) (tw : Array (ℤ × ℤ)) : Prog TwL (fun _ => Sym) tJw.Reg :=
  .seq (preload TR (twSyms 2 tw)) (.seq (preload C0 (hdrSyms (preTapeFields pSub 1 2 2)))
    (kernel tJw (if pre then stpPre tJw else stpPost tJw)))

/-- Run from `W0 = matSyms U`; report `(steps, stack out)`. -/
def runTw (pre : Bool) (pSub : ℕ) (tw : Array (ℤ × ℤ)) (U : Array (Array (ℤ × ℤ)))
    (out : TwL) : Option (ℕ × List Sym) :=
  runMach (twShow pre pSub tw) σ0 W0 out (matSyms U) 20000000

def tw0 : Array (ℤ × ℤ) := #[(2, 1), (1, -2)]
def U0 : Array (Array (ℤ × ℤ)) := #[#[(1, -1), (2, 1)], #[(-1, 2), (0, 1)]]

#guard (runTw true 0 tw0 U0 W0).map (·.2) = some (matSyms (w9P 0 2 2 tw0 U0))
#guard (runTw true 1 tw0 U0 W0).map (·.2) = some (matSyms (w9P 1 2 2 tw0 U0))
#guard (runTw false 1 tw0 U0 W0).map (·.2) = some (matSyms (w9QPost 1 2 2 tw0 U0))
#guard (runTw true 1 tw0 U0 TL).map (·.2) = some ((twSyms 2 tw0).reverse)

/-- Steps vs the proved bound `(17·50 + 150)·twistBound` (with `Mul w = (w+1)²`, `w = 4`). -/
def report (pre : Bool) (pSub : ℕ) : String :=
  let h : PreHdr := ⟨0, pSub, 1, 2, 2⟩
  match runTw pre pSub tw0 U0 W0 with
  | none => s!"pre={pre} pSub={pSub}: no halt"
  | some (n, z) =>
    let ok := if pre then decide (z = matSyms (w9P pSub 2 2 tw0 U0))
      else decide (z = matSyms (w9QPost pSub 2 2 tw0 U0))
    s!"pre={pre} pSub={pSub}: ok={ok} steps={n} " ++
      s!"bound={(17 * 50 + 150) * twistBound (fun w => (w + 1) * (w + 1)) 4 h}"

#eval [report true 2, report false 0]

end WP.W9d.Smoke
