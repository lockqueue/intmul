/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMul
import SubNLogN.Machine.Arith.CMulBRuns
import SubNLogN.Machine.MulBig.Main

/-!
# AR4/AR4b with the multiplier discharged (`Arith/CMulFinal.lean`)

**Scope (honest summary).** `cmulTrunc_holds'` and `cmulTruncBcast_holds'`: the kernel contracts of
`CMulTruncStmt` / `CMulTruncBcastStmt` (`Machine/Contracts/Arith.lean`) with their premise
`MulBigContract` discharged by `SubNLogN.Machine.MulBig.mulBig_holds`
(`Machine/MulBig/Main.lean`). Everything is proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-- `CMulTruncStmt` without premise (multiplier: `mulBig_holds`). -/
theorem cmulTrunc_holds' :
  KContract (Fin 7) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 w3 s : ℕ) (z θ : List (List CInt)) (rz rθ r3 r4 r5 r6 : List Sym)
      (S : KLoc (Fin 7) E → List Sym),
      KClean S → 1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 z → CArrFits w2 θ → CAligned z θ →
      CArrFits w3 (zipC (cmulTruncC s) z θ) →
      BlkTerm rz → BlkTerm rθ → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = carrSyms w1 z ++ rz → S (.inl 1) = carrSyms w2 θ ++ rθ →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 → S (.inl 6) = natSyms s ++ r6 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
          (carrSyms w3 (zipC (cmulTruncC s) z θ) ++ S (.inl 2)))
        (fun _ => True)
        (C * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 θ + cvol w3 z +
          (ncoef z + 1) * (bitLen s + 1) + w1 + w2 + w3)) :=
  cmulTrunc_holds SubNLogN.Machine.MulBig.mulBig_holds

/-- `CMulTruncBcastStmt` without premise (multiplier: `mulBig_holds`). -/
theorem cmulTruncBcast_holds' :
  KContract (Fin 7) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 w3 s : ℕ) (z : List (List CInt)) (θ : List CInt) (rz rθ r3 r4 r5 r6 : List Sym)
      (S : KLoc (Fin 7) E → List Sym),
      KClean S → 1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 z → CArrFits w2 (bcastArr θ) →
      z.length = θ.length → CArrFits w3 (cmulTruncBcast s z θ) →
      BlkTerm rz → BlkTerm rθ → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = carrSyms w1 z ++ rz → S (.inl 1) = carrSyms w2 (bcastArr θ) ++ rθ →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 → S (.inl 6) = natSyms s ++ r6 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
          (carrSyms w3 (cmulTruncBcast s z θ) ++ S (.inl 2)))
        (fun _ => True)
        (C * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 (bcastArr θ) + cvol w3 z +
          (ncoef z + 1) * (w2 + bitLen s + 1) + w1 + w2 + w3)) :=
  cmulTruncBcast_holds SubNLogN.Machine.MulBig.mulBig_holds

end SubNLogN.Machine.Arith
