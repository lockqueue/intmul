/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepLayout

/-!
# K5-SOLVE (1g): the sweep kernel contract (statement)

`SolveSweepStmt`: the two-pass cyclic sweep on one half of a deconvolution stage. Input: an
`L × M` row-major array of one-coefficient records on `dat` (column `s` is one cycle) and three
parameter rows of `M` records `(μ_s, 0)`, `(-â_s, 0)`, `(γ_s, 0)` on `mu`, `na`, `gm` (restored);
output: `sweepHalfI q L M mus nas gms ys` (`SolveSweepDefs.lean`) pushed on `dst`, `dat`
consumed. Counter stacks: `natSyms` of `wI`, `wI`, `wI + 1`, `wT`, `wI + wT + 1`, `q`, `0`
(restored). Premises: the multiplier and the three arithmetic leaves. Statement only; proved as
`solveSweep_holds` (`SolveSweep.lean`).
-/

namespace SubNLogN.Machine.Bridge

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Bridge.SolveAux

/-- **[CONTRACT] The sweep on one half of a deconvolution stage** (part 1 of `SolveAxisStmt`).
Named stacks `SwN`; clean private scratch. Cost: `O(mulW (wI + wT + 1) + log q)` per entry. -/
def SolveSweepStmt : Prop :=
  MulBigContract → CMulTruncStmt → RoundHalfUpShiftStmt → CAddStmt →
  KContract SwN Unit fun _ E _ _ _ C Pg =>
    ∀ (wI wT q L M : ℕ) (ys : List CInt) (mus nas gms : List ℤ)
      (rdat rmu rna rgm r1 r2 r3 r4 r5 r6 r7 : List Sym) (S : KLoc SwN E → List Sym),
      KClean S → 1 ≤ wI → 1 ≤ wT → 1 ≤ L → 1 ≤ M →
      ys.length = L * M → mus.length = M → nas.length = M → gms.length = M →
      (∀ y ∈ ys, Fits2 wI y) → (∀ m ∈ mus, FitsTwos wT m) → (∀ m ∈ nas, FitsTwos wT m) →
      (∀ m ∈ gms, FitsTwos wT m) →
      (∀ s, s < M → ColFitsI wI q (mus.getD s 0) (nas.getD s 0) (gms.getD s 0) L
        (fun j => ys.getD (j * M + s) 0)) →
      TermOK rdat → TermOK rmu → TermOK rna → TermOK rgm → TermOK r1 → TermOK r2 → TermOK r3 →
      TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 →
      S (.inl .dat) = rec1s wI ys ++ rdat →
      S (.inl .mu) = rec1s wT (mus.map fun m => (m, 0)) ++ rmu →
      S (.inl .na) = rec1s wT (nas.map fun m => (m, 0)) ++ rna →
      S (.inl .gm) = rec1s wT (gms.map fun m => (m, 0)) ++ rgm →
      S (.inl .cwI) = natSyms wI ++ r1 → S (.inl .cwI2) = natSyms wI ++ r2 →
      S (.inl .cwI1) = natSyms (wI + 1) ++ r3 → S (.inl .cwT) = natSyms wT ++ r4 →
      S (.inl .cwP) = natSyms (wI + wT + 1) ++ r5 → S (.inl .cq) = natSyms q ++ r6 →
      S (.inl .c0) = natSyms 0 ++ r7 →
      Runs Pg S
        (Function.update (Function.update S (.inl .dat) rdat) (.inl .dst)
          (rec1s wI (sweepHalfI q L M mus nas gms ys) ++ S (.inl .dst)))
        (fun _ => True) (C * (L * M * (mulW (wI + wT + 1) + bitLen q + 1) + 1))

end SubNLogN.Machine.Bridge
