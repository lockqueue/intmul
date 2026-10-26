/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulDrv

/-!
# AR4, products: closedness of the per-coefficient programs (`Arith/CMulClosedA.lean`)

Everything is proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## Closedness -/

theorem absAll_closed : absAll.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, absAll, absProg, walk, walkLoop, walkStep, loadBody,
    moveMarks, mmLoop, mvBits, mvLoop, emitXBody, trimLoop, peekQ, peekR, popO, drop1, pushS,
    skipA]

theorem postAll_closed : postAll.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, postAll, drainBits, dbLoop, halfProg, toTwosProg,
    rippleProg, rippleBody, popQ, fieldProg, discBody, loadBody, emitBody, carryInit, walk,
    walkLoop, walkStep, moveMarks, mmLoop, mvBits, mvLoop, emitXBody, peekQ, peekR, peekO, popO,
    drop1, pushS, skipA]

theorem recTail_closed : recTail.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, recTail, drop1, pushS, peekO]

end SubNLogN.Machine.Arith
