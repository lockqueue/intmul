/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixRun
import SubNLogN.Machine.FFT.PrefixMath

/-!
# K4-PREFIX (`Machine/FFT/Prefix.lean`): the prefix-round contract `PrefixRoundStmt`

**Scope (honest summary).** Proved, no `sorry` in this file:
* `prefixRound_of (hPar : PrefixParamStmt) (hPass : PrefixPassStmt) (hTr : TruncShiftStmt) :
  PrefixRoundStmt`, with witnesses `J' = J + 2` (`J` the exponent of `PrefixParamStmt`) and
  `C = Cfin Cr Cp Ct = Cr + 10·Cp + 10·Ct + 200`.

`PrefixRoundStmt` (`Contracts/FFT.lean:239`; Theorem 6.5, `thm:direct-fft`, Section 6.4: prefix rounds
apply exact individual butterflies before a single truncation). For a non-chunk round `v < ℓ`,
the array becomes `truncArr q (hT (roundSet ℓ K a v) z)`: all participating `H_0` factors exactly,
then one `Q_q`. The header and the round index are restored; private scratch is empty at both ends.

**Proof.**
* `roundSet` is the position block `[pfS, pfS + pfN)` (M1).
* `H_T` on that block is `pfN` exact butterfly passes on the index bits `L, …, L + n - 1`,
  `L = D·pfY`, then one truncation by `2^n` (M2). The latter equals `n` truncations by `2` (M4).
  M1, M2, M4 are in `PrefixMath.lean`.
* The driver (`PrefixMain`/`PrefixRun`) runs these passes at width `w + D`; M3 gives the fits.
* The sub-kernels are taken as hypotheses:
  - `PrefixParamStmt` (header arithmetic, `PrefixParamSpec.lean`);
  - `PrefixPassStmt` (one exact pass, `PrefixPassSpec.lean`);
  - `TruncShiftStmt` (`Contracts/Arith.lean`).
* The cost bound is `prefCost_le` (`PrefixCost.lean`).
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- **The driver's value.** `n` exact passes on the bits `L, …, L + n - 1`, then `n` truncations by
`2` and the identity truncation, give `Q_q(H_T z)` for `T = roundSet ℓ K a v`. -/
theorem prefix_value {D : ℕ} (q ℓ K w v : ℕ) (a : Fin D → ℕ) (hshape : MidShapeOK q ℓ K w a)
    (hv : v < ℓ) (hnc : ¬ IsChunkRound ℓ K v) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
    (hz : ArrOnDiskGrid q z) :
    mapC (truncShiftC 0) ((mapC (truncShiftC 1))^[pfN ℓ K a v]
      (bflyIter (addrBits a) (D * pfY ℓ K v) (pfN ℓ K a v) (encCube q z))) =
      encCube q (truncArr q (hT (roundSet ℓ K a v) z)) := by
  have hb := pf_bound q ℓ K w v a hshape hv hnc
  rw [truncShift_iter, roundSet_eq_posBlock q ℓ K w v a hshape hv hnc,
    encCube_truncArr_hT_posBlock q (pfS ℓ K a v) (pfN ℓ K a v) (by omega) z
      (fun x k => (hz x k).1)]
  congr 2
  omega

theorem le_addrBits {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) (hshape : MidShapeOK q ℓ K w a) :
    D ≤ addrBits a := by
  obtain ⟨-, -, hℓ2, -, -, -, ha, -⟩ := hshape
  rw [LayoutPermAux.addrBits_eq ℓ a (by omega) ha]
  have : D ≤ D * (ℓ - 1) := Nat.le_mul_of_pos_right D (by omega)
  omega

/-- **`PrefixRoundStmt`** from the parameter phase, the exact pass and the truncation kernel. -/
theorem prefixRound_of (hPar : PrefixParamStmt) (hPass : PrefixPassStmt) (hTr : TruncShiftStmt) :
    PrefixRoundStmt := by
  obtain ⟨J, Cr, hCr⟩ := hPar
  obtain ⟨Er, iFr, iDr, Rr, Pr, hRrf, hRrn, hPrc, hPr⟩ := hCr ()
  obtain ⟨Cp, hCp⟩ := hPass
  obtain ⟨Ep, iFp, iDp, Rp, Pp, hRpf, hRpn, hPpc, hPp⟩ := hCp ()
  obtain ⟨Ct, hCt⟩ := hTr
  obtain ⟨Et, iFt, iDt, Rt, Pt, hRtf, hRtn, hPtc, hPt⟩ := hCt ()
  have hR : ParamSpec Er Rr Cr J Pr := hPr
  have hP : PassSpec Ep Rp Cp Pp := hPp
  have hT : TrSpec Et Rt Ct Pt := hPt
  refine ⟨J + 2, Cfin Cr Cp Ct, fun _ => ⟨PS ⊕ (Er ⊕ (Ep ⊕ Et)), inferInstance, inferInstance,
    Option Sym × (Rr × (Rp × Rt)), mainProg (Lens.fst _ _) ((Lens.snd _ _).comp (Lens.fst _ _))
      ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
      ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))) Pr Pp Pt, ?_, ?_,
    closed_mainProg _ _ _ _ _ _ _ hPrc hPpc hPtc, ?_⟩⟩
  · have := hRrf
    have := hRpf
    have := hRtf
    infer_instance
  · have := hRrn
    have := hRpn
    have := hRtn
    infer_instance
  · intro q ℓ K w D v a z rest hrest crest S hcl hshape hv hnc hz hrest' hcrest hS0 hS1 hS3
    have hb := pf_bound q ℓ K w v a hshape hv hnc
    have hnD := pfN_le ℓ K a v
    have hqw : q + 2 ≤ w := hshape.2.2.2.2.2.2.2
    have h := runs_main (Lens.fst _ _) ((Lens.snd _ _).comp (Lens.fst _ _))
      ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
      ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))) hR hP hT S hcl q ℓ K w D v a z
      rest hrest crest hshape hv hnc hz hrest' hcrest hS0 hS1 hS3
      (fun j hj => fits_bflyIter q _ j (w + D) (by omega) (by omega) z hz)
      _ (prefix_value q ℓ K w v a hshape hv hnc z hz)
      (fits_encCube hqw (diskGrid_truncArr_hT _ hz))
    refine runs_mono h (fun _ _ => trivial) ?_
    exact prefCost_le Cr Cp Ct J w D (addrBits a) ℓ (pfN ℓ K a v) (D * pfY ℓ K v) _ (by omega)
      hnD (le_addrBits q ℓ K w a hshape) (by omega)

end SubNLogN.Machine.FFT.PrefixAux
