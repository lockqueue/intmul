/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulTear

/-!
# AR4, products: closedness of setup and teardown (`Arith/CMulClosedB.lean`)

Everything is proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

theorem cmulSetup_closed : cmulSetup.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, cmulSetup, maxW, cmpSW, minSW, subSW, buildRuler, brLoop,
    brBody, double, dblLoop, copyRuler, subRuler, walk, walkLoop, walkStep, moveMarks, mmLoop,
    drainBits, dbLoop, mvBits, mvLoop, peekQ, peekR, peekO, drop1, pushS, skipA, Prog.liftRegs,
    Lib.cmpNum, Lib.cmpBody, Lib.pushC, Lib.popR, Lib.restoreR, Lib.moveBits, Lib.moveBitsBody,
    Lib.pushR, Lib.skip, Lib.copyBlock, Lib.moveBlock, Lib.moveBitsDup, Lib.dupBody]

theorem cmulTeardown_closed : cmulTeardown.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, cmulTeardown, clearMarks, cmLoop, drop1, peekR,
    Prog.liftRegs, WP.W9comp.rewindTo, WP.W9comp.rewindBody, Lib.pushR, Lib.popR]

end SubNLogN.Machine.Arith
