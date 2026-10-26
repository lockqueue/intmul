/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPreMain

/-!
# K5 pre-scaling part: the contract (`Bridge/PrePostPreFin.lean`)

`preScale_holds_of (hTr : TruncShiftStmt) (hShl : ShlStmt) : PreScaleStmt`
(`SubNLogN/Machine/Contracts/Bridge.lean` §7; Section 4.4 (`sec:bridge-alg`), step (1); Theorem 4.7 (`thm:bridge-precision`)):
the program `preProg` (`Bridge/PrePostPreMain.lean`) with the two AR shift kernels
(`Contracts/Arith.lean`) as components; constant `preK Ct Cs = 6200·pK Ct Cs`.

**Scope (honest summary).** Proved from the two hypotheses `TruncShiftStmt`, `ShlStmt` (both proved
by AR: `Arith.truncShift_holds`, `Arith.shl_holds`); no `sorry` in this file.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Math.Common SubNLogN.Math.Bridge

section Final

variable {Et Es Rt Rs : Type} [DecidableEq Et] [DecidableEq Es]

omit [DecidableEq Et] [DecidableEq Es] in
theorem closed_preProg (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)
    (Ps : Prog (KLoc (Fin 5) Es) (fun _ => Sym) Rs) (hPt : Pt.Closed) (hPs : Ps.Closed) :
    (preProg Pt Ps).Closed := by
  have hl : ∀ {p : SProg (KLoc BrK (ZE Et Es))}, p.Closed →
      (p.liftRegs (lzO (Rt := Rt) (Rs := Rs))).Closed := fun hp => WP.W9comp.closed_liftRegs _ hp
  have hlP : ∀ {p : PProg (KLoc BrK (ZE Et Es))}, p.Closed →
      (p.liftRegs (lzP (Rt := Rt) (Rs := Rs))).Closed := fun hp => WP.W9comp.closed_liftRegs _ hp
  have hCB : ∀ a b c : KLoc BrK (ZE Et Es), (copyBlock a b c).Closed := fun a b c => by
    simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
      moveBitsDup, dupBody, restoreR, popR, pushR, pushC, skip]
  have hI : ∀ x : ZW, (zIncP (Et := Et) (Es := Es) (Rt := Rt) (Rs := Rs) x).Closed := fun x =>
    hl (by simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody, pushC, popR, skip,
      moveBits, moveBitsBody, pushR, restoreR])
  have hD : ∀ x : ZW, (zDropP (Et := Et) (Es := Es) (Rt := Rt) (Rs := Rs) x).Closed := fun x =>
    hl (by simp [Prog.Closed, Prog.FreeBelow, WP.W3.dropNum, WP.W3.dropBits, restoreR, popR,
      pushR, skip])
  have hmax : (preMax (Et := Et) (Es := Es) (Rt := Rt) (Rs := Rs)).Closed :=
    ⟨closed_callInj _ _ theW3Kit.clC, hl (hCB _ _ _), hl (hCB _ _ _)⟩
  have hlt : (preBrLt Pt Ps).Closed :=
    ⟨closed_callInj _ _ theW3Kit.clB, closed_callInj _ _ hPt, hD .NS⟩
  have hge : (preBrGe Pt Ps).Closed :=
    ⟨closed_callInj _ _ theW3Kit.clB, closed_callInj _ _ hPs, hD .NS⟩
  have hker : (preKer Pt Ps).Closed := ⟨closed_callInj _ _ theW3Kit.clC, hlt, hge⟩
  exact ⟨hl (BridgePSA.closed_psHdr _ _ _ _ _ _ _ _ _),
    hlP (BridgePSA.closed_psScan _ _ _ _ _ _ _ _ _), hmax, hl (closed_c2Block _ _ _),
    closed_callInj _ _ theW3Kit.clA, hI _, hI _, hI _, hI _, hI _,
    closed_callInj _ _ theW3Kit.clB, hI _, hI _, hker, hl (hCB _ _ _),
    hD _, hD _, hD _, hD _, hD _, hD _, hD _, hD _, hD _, hD _⟩

end Final

/-- The cost constant of the pre-scale contract. -/
noncomputable def preK (Ct Cs : ℕ) : ℕ := 6200 * pK Ct Cs

/-- **[K5] `PreScaleStmt` holds**, from the AR truncating shift and left shift kernels
(`Contracts/Arith.lean`). -/
theorem preScale_holds_of (hTr : TruncShiftStmt) (hShl : ShlStmt) : PreScaleStmt := by
  obtain ⟨Ct, ht⟩ := hTr
  obtain ⟨Cs, hs⟩ := hShl
  refine ⟨preK Ct Cs, fun _ => ?_⟩
  obtain ⟨Et, iEt1, iEt2, Rt, Pt, hRt1, hRt2, hPtC, hspecT⟩ := ht ()
  obtain ⟨Es, iEs1, iEs2, Rs, Ps, hRs1, hRs2, hPsC, hspecS⟩ := hs ()
  have := hRt1
  have := hRt2
  have := hRs1
  have := hRs2
  have := theW3Kit.finA
  have := theW3Kit.neA
  have := theW3Kit.finB
  have := theW3Kit.neB
  have := theW3Kit.finC
  have := theW3Kit.neC
  refine ⟨ZE Et Es, inferInstance, inferInstance, ZReg Rt Rs, preProg Pt Ps, inferInstance,
    inferInstance, closed_preProg Pt Ps hPtC hPsC, ?_⟩
  intro b x rsrc rpar S hclean hd1 hshape hwIn hwI hx hg hfitIn hfitI hrsrc hsrc hpar
  have hPt : ShiftSpec truncShiftC Ct Pt := hspecT
  have hPs : ShiftSpec shlC Cs Ps := hspecS
  refine WP.W9comp.runs_mono (runs_preProg Pt Ps Ct Cs hPt hPs b x rsrc rpar S hclean hd1 hshape
    hwIn hwI hx hg hfitIn hfitI hrsrc hsrc hpar) (fun _ _ => trivial) (le_of_eq ?_)
  unfold preK
  ring

end SubNLogN.Machine.BridgePP
