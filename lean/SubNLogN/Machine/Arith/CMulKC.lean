/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulTear
import SubNLogN.Machine.Arith.CMulClosedA
import SubNLogN.Machine.Arith.CMulClosedB

/-!
# AR4, products: closedness of the kernel (`Arith/CMulKC.lean`)

Everything is proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

theorem cmulKernel_closed {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} (hcl : Pm.Closed) :
    (cmulKernel Pm).Closed := by
  have hS := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) cmulSetup_closed
  have hO := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) (p := peekO (K := CK) (.inl 0))
    (by simp [Prog.Closed, Prog.FreeBelow, peekO])
  have hA := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) absAll_closed
  have hP := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) postAll_closed
  have hR := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) recTail_closed
  have hT := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) cmulTeardown_closed
  have hM1 := closed_callInj (mbι .Ma .Mc .P1) (Lens.snd AReg Rm) hcl
  have hM2 := closed_callInj (mbι .Mb .Md .P2) (Lens.snd AReg Rm) hcl
  have hM3 := closed_callInj (mbι .Ma .Md .P3) (Lens.snd AReg Rm) hcl
  have hM4 := closed_callInj (mbι .Mb .Mc .P4) (Lens.snd AReg Rm) hcl
  simp only [Prog.Closed] at hS hO hA hP hR hT hM1 hM2 hM3 hM4 ⊢
  simp only [cmulKernel, recLoopC, recBodyC, coefLoop, coefProg, mulAll, Prog.FreeBelow, hS, hO,
    hA, hP, hR, hT, hM1, hM2, hM3, hM4, and_self]

end SubNLogN.Machine.Arith
