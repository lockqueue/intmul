/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepPass
import SubNLogN.Machine.Bridge.SolveSweepStmt

/-!
# K5-SOLVE (1m): the sweep kernel, `solveSweep_holds : SolveSweepStmt`

The kernel program is `sweepBody` (`SolveSweepPass.lean`) over the three leaf kernels (exact
products `CMulTruncStmt`, half-up roundings `RoundHalfUpShiftStmt`, exact sums `CAddStmt`), with
private scratch `SwW ⊕ (Ecm ⊕ (Erh ⊕ Eca))` and registers `Option Sym × (Rcm × (Rrh × Rca))`.
* `closed_sweepBody`: the program is closed;
* `bodyCost_le`: its cost is at most `sweepC · (L·M·(mulW (wI+wT+1) + bitLen q + 1) + 1)`;
* `solveSweep_holds`: the contract.
All proved; the multiplier premise of the contract is passed to the `CMulTruncStmt` leaf.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

/-! ## Closedness -/

theorem closed_moveRec {K : Type} [DecidableEq K] (a b c : K) : (moveRec a b c).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveRec, moveBlock, moveBits, moveBitsBody, restoreR, skip,
    popR, pushC, pushR]

theorem closed_copyRec {K : Type} [DecidableEq K] (a b c : K) : (copyRec a b c).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyRec, copyBlock, moveBlock, moveBits, moveBitsBody,
    restoreR, skip, moveBitsDup, dupBody, popR, pushC, pushR]

theorem closed_eraseRec {K : Type} [DecidableEq K] (a : K) : (eraseRec a).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, eraseRec, popR]

theorem closed_drainRecs {K : Type} [DecidableEq K] (a b c : K) : (drainRecs a b c).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, drainRecs, drainBody, moveRec, moveBlock, moveBits,
    moveBitsBody, restoreR, skip, popR, pushC, pushR, peekR]

section Closed

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]
variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

theorem closed_sweepBody (hcm : G.Pcm.Closed) (hrh : G.Prh.Closed) (hca : G.Pca.Closed) :
    (sweepBody G).Closed := by
  have hCM : (cCM G).Closed := closed_callInj _ _ hcm
  have hRD : (cRD G).Closed := closed_callInj _ _ hrh
  have hRF : (cRF G).Closed := closed_callInj _ _ hrh
  have hCA : (cCA G).Closed := closed_callInj _ _ hca
  have hMV : ∀ x y, (MV x y : PS Ecm Erh Eca Rcm Rrh Rca).Closed := fun _ _ =>
    closed_liftRegs_sprog _ (closed_moveRec _ _ _)
  have hCP : ∀ x y, (CP x y : PS Ecm Erh Eca Rcm Rrh Rca).Closed := fun _ _ =>
    closed_liftRegs_sprog _ (closed_copyRec _ _ _)
  have hpk : ∀ x, (pk lS x : PS Ecm Erh Eca Rcm Rrh Rca).Closed := fun _ =>
    closed_liftRegs_sprog _ (by simp [Prog.Closed, Prog.FreeBelow, peekR])
  have hdr : ∀ x y, (drP lS x y : PS Ecm Erh Eca Rcm Rrh Rca).Closed := fun _ _ =>
    closed_liftRegs_sprog _ (closed_drainRecs _ _ _)
  have her : ∀ x, (erP lS x : PS Ecm Erh Eca Rcm Rrh Rca).Closed := fun _ =>
    closed_liftRegs_sprog _ (closed_eraseRec _)
  simp only [Prog.Closed] at hCM hRD hRF hCA hMV hCP hpk hdr her ⊢
  simp [sweepBody, prePass, secPass, finPass, r1, r2, r3, r4, e1, e2, e3, e4, whileP,
    Prog.FreeBelow, hCM, hRD, hRF, hCA, hMV, hCP, hpk, hdr, her]

end Closed

/-! ## Cost -/

/-- The cost constant of the sweep kernel. -/
def sweepC (Ccm Crh Cca : ℕ) : ℕ := 1080 + 72 * Ccm + 80 * Crh + 64 * Cca

theorem mul_le_of_le {a b c X : ℕ} (h : b ≤ c * X) : a * b ≤ c * (a * X) :=
  calc a * b ≤ a * (c * X) := Nat.mul_le_mul_left _ h
    _ = c * (a * X) := by ring

theorem bodyCost_le (Ccm Crh Cca wI wT q L M : ℕ) (hL : 1 ≤ L) (hM : 1 ≤ M) :
    bodyCost Ccm Crh Cca wI wT q L M ≤
      sweepC Ccm Crh Cca * (L * M * (mulW (wI + wT + 1) + bitLen q + 1) + 1) := by
  obtain ⟨X, hX⟩ : ∃ X, X = mulW (wI + wT + 1) + bitLen q + 1 := ⟨_, rfl⟩
  rw [← hX]
  have hn : wI + wT + 1 ≤ mulW (wI + wT + 1) := by
    unfold mulW
    have := Nat.le_mul_of_pos_right (wI + wT + 1)
      (show 0 < Nat.log2 (wI + wT + 1) + 1 by omega)
    omega
  have hwX : wI ≤ X := by omega
  have h1X : 1 ≤ X := by omega
  have hcm : cmCost wI wT ≤ 9 * X := by unfold cmCost; omega
  have hrh1 : rhCost (wI + wT + 1) wI q ≤ 10 * X := by unfold rhCost; omega
  have hrh2 : rhCost (wI + wT + 1) (wI + 1) q ≤ 10 * X := by unfold rhCost; omega
  have hca : caCost wI ≤ 16 * X := by unfold caCost; omega
  have pcm : Ccm * cmCost wI wT ≤ 9 * (Ccm * X) := mul_le_of_le hcm
  have prh1 : Crh * rhCost (wI + wT + 1) wI q ≤ 10 * (Crh * X) := mul_le_of_le hrh1
  have prh2 : Crh * rhCost (wI + wT + 1) (wI + 1) q ≤ 10 * (Crh * X) := mul_le_of_le hrh2
  have pca : Cca * caCost wI ≤ 16 * (Cca * X) := mul_le_of_le hca
  obtain ⟨A, hA⟩ : ∃ A, A = e2Cost Ccm Crh Cca wI wT q + 2 + (12 * wI + 12) +
      2 * (12 * wT + 12) := ⟨_, rfl⟩
  have hAX : A ≤ 238 * X + 18 * (Ccm * X) + 20 * (Crh * X) + 16 * (Cca * X) := by
    rw [hA]; unfold e2Cost; omega
  have ha1 : e1Cost Ccm Crh wI wT q + 2 + (12 * wI + 12) + (12 * wT + 12) ≤ A := by
    rw [hA]; unfold e1Cost e2Cost; omega
  have ha4 : e4Cost Ccm Crh Cca wI wT q + 2 + (12 * wI + 12) + (12 * wT + 12) ≤ A := by
    rw [hA]; unfold e4Cost e2Cost; omega
  have hML : M ≤ L * M := Nat.le_mul_of_pos_left M hL
  have hMA : M * A ≤ L * M * A := Nat.mul_le_mul_right A hML
  have hMW : M * wI ≤ L * M * wI := Nat.mul_le_mul_right wI hML
  have hr1 : r1Cost Ccm Crh wI wT q M ≤ L * M * A + 6 := by
    unfold r1Cost; have := Nat.mul_le_mul_left M ha1; omega
  have hr2 : r2Cost Ccm Crh Cca wI wT q M = M * A + 8 := by unfold r2Cost; rw [hA]
  have hr4 : r4Cost Ccm Crh Cca wI wT q M ≤ M * A + 6 := by
    unfold r4Cost; have := Nat.mul_le_mul_left M ha4; omega
  have q1 : (L - 1) * (r2Cost Ccm Crh Cca wI wT q M + 1 + 1) ≤ L * M * A + 10 * (L * M) := by
    rw [hr2]
    calc (L - 1) * (M * A + 8 + 1 + 1) ≤ L * (M * A + 10) :=
          Nat.mul_le_mul (Nat.sub_le L 1) (by omega)
      _ = L * M * A + 10 * L := by ring
      _ ≤ L * M * A + 10 * (L * M) := by have := Nat.le_mul_of_pos_right L hM; omega
  have q2 : L * (r4Cost Ccm Crh Cca wI wT q M + 1 + 1) ≤ L * M * A + 8 * (L * M) := by
    calc L * (r4Cost Ccm Crh Cca wI wT q M + 1 + 1) ≤ L * (M * A + 8) :=
          Nat.mul_le_mul_left L (by omega)
      _ = L * M * A + 8 * L := by ring
      _ ≤ L * M * A + 8 * (L * M) := by have := Nat.le_mul_of_pos_right L hM; omega
  have q3 : M * (4 * wI + 2 + (4 * wI + 2) + 1 + 1) = 8 * (M * wI) + 6 * M := by ring
  have q4 : M * (12 * wI + 12) = 12 * (M * wI) + 12 * M := by ring
  have q5 : (L - 1) * M * (12 * wI + 12) ≤ 12 * (L * M * wI) + 12 * (L * M) := by
    calc (L - 1) * M * (12 * wI + 12) ≤ L * M * (12 * wI + 12) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right M (Nat.sub_le L 1))
      _ = 12 * (L * M * wI) + 12 * (L * M) := by ring
  have q6 : L * M * (12 * wI + 12) = 12 * (L * M * wI) + 12 * (L * M) := by ring
  have hLMA : L * M * A ≤ 238 * (L * M * X) + 18 * (Ccm * (L * M * X)) +
      20 * (Crh * (L * M * X)) + 16 * (Cca * (L * M * X)) := by
    calc L * M * A ≤ L * M * (238 * X + 18 * (Ccm * X) + 20 * (Crh * X) + 16 * (Cca * X)) :=
          Nat.mul_le_mul_left _ hAX
      _ = _ := by ring
  have hPW : L * M * wI ≤ L * M * X := Nat.mul_le_mul_left _ hwX
  have hQ : L * M ≤ L * M * X := Nat.le_mul_of_pos_right _ h1X
  have hgoal : sweepC Ccm Crh Cca * (L * M * X + 1) = 1080 * (L * M * X) +
      72 * (Ccm * (L * M * X)) + 80 * (Crh * (L * M * X)) + 64 * (Cca * (L * M * X)) +
      (1080 + 72 * Ccm + 80 * Crh + 64 * Cca) := by unfold sweepC; ring
  rw [hgoal]
  unfold bodyCost
  rw [loopCost_const, loopCost_const, loopCost_const]
  omega

theorem mk_self {LE : Type} [DecidableEq LE] (S : KS LE → List Sym) :
    mk S (fun x => S (loc x)) = S := by
  funext k
  rcases h : toX k with _ | y
  · exact mk_of_toX_none _ _ h
  · rw [← loc_of_toX h, mk_loc]

end SubNLogN.Machine.Bridge.SolveAux

namespace SubNLogN.Machine.Bridge

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Bridge.SolveAux

/-- **The sweep kernel** (part 1 of `SolveAxisStmt`). -/
theorem solveSweep_holds : SolveSweepStmt := by
  intro hMul hCM hRH hCA
  obtain ⟨Ccm, hcm⟩ := hCM hMul
  obtain ⟨Crh, hrh⟩ := hRH
  obtain ⟨Cca, hca⟩ := hCA
  obtain ⟨Ecm, iEcm, dEcm, Rcm, Pcm, fRcm, nRcm, clcm, scm⟩ := hcm ()
  obtain ⟨Erh, iErh, dErh, Rrh, Prh, fRrh, nRrh, clrh, srh⟩ := hrh ()
  obtain ⟨Eca, iEca, dEca, Rca, Pca, fRca, nRca, clca, sca⟩ := hca ()
  refine ⟨sweepC Ccm Crh Cca, fun _ => ⟨SwW ⊕ LEs Ecm Erh Eca, inferInstance, inferInstance,
    σs Rcm Rrh Rca, sweepBody ⟨Pcm, Prh, Pca⟩, inferInstance, inferInstance,
    closed_sweepBody ⟨Pcm, Prh, Pca⟩ clcm clrh clca, ?_⟩⟩
  intro wI wT q L M ys mus nas gms rdat rmu rna rgm r1 r2 r3 r4 r5 r6 r7 S hcl hwI hwT hL hM hys
    hmus hnas hgms hy hmu hna hgm hcol trdat trmu trna trgm t1 t2 t3 t4 t5 t6 t7 hdat hmuS hnaS
    hgmS h1 h2 h3 h4 h5 h6 h7
  have hB : BaseOK S wI wT q := ⟨fun e => hcl (.inr e), ⟨r1, h1, t1⟩, ⟨r2, h2, t2⟩, ⟨r3, h3, t3⟩,
    ⟨r4, h4, t4⟩, ⟨r5, h5, t5⟩, ⟨r6, h6, t6⟩, ⟨r7, h7, t7⟩⟩
  have hI : SwIn (fun x => S (loc x)) wI wT ys mus nas gms rdat rmu rna rgm :=
    ⟨hdat, hmuS, hnaS, hgmS, fun w => hcl (.inl w)⟩
  have hF : SwFits q wI wT L M ys mus nas gms := ⟨hy, hmu, hna, hgm, hcol⟩
  have h := runs_sweepBody ⟨Pcm, Prh, Pca⟩ scm srh sca hB hwI hwT hL hM hI trdat trmu hys hmus
    hnas hgms hF
  rw [← update_mk, ← update_mk, mk_self] at h
  exact WP.W9comp.runs_mono h (fun _ _ => trivial) (bodyCost_le Ccm Crh Cca wI wT q L M hL hM)

end SubNLogN.Machine.Bridge
