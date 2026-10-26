/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PhaseTable
import WP.Top.Current6
import WP.W5.Main
import WP.W7k3.StdChar

/-!
# K4-TW (`Machine/FFT/PhaseHolds.lean`): `PhaseTableMachineStmt` holds

**Scope (honest summary).** Proves `SubNLogN.Machine.phaseTableMachine_holds :
PhaseTableMachineStmt` (`Machine/Contracts/FFT.lean`; Lemma 6.1, `lem:phase-table`, and
Section 6.4, `sec:direct-fft-thm`), with no hypotheses:
* the eleven contract instances of the builder come from proved contracts: W3 (`W3_all_holds`,
  `WP/Top/Current6.lean`) and W7's `stdChar` (`WP.W7k3.W7_stdChar_bind` at the Toom-3 multiplier
  of `WP.W5.W5_toom3Mul_holds`, with W6a `W6a_holds`);
* the builder `ptProg` and its host rule `HT.ptProg` (`PhaseTable.lean`);
* the explicit cost bound `costPT_le`: `costPT ≤ 2000·(C+1)·(2^ℓ·(w+1)^4 + |midHdr|)`, i.e.
  `J = 4`, charging the quartic per-entry `stdChar` cost directly (in place of the cubic `O(q^3)`
  per-entry schoolbook bound of Lemma 6.1).
-/

namespace SubNLogN.Machine.FFT.Phase

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh

/-- **The builder's instance bundle exists**, from proved contracts only. -/
theorem exists_PI : ∃ I : PI, ∃ C : ℕ, 1 ≤ C ∧ I.Spec C := by
  obtain ⟨hcopy, hdrop, -, hisz, hcmp, hadd, hsub, hshl, -, hshlV, hshrV, hsplit, -, -, hdec, -, -,
    -, -, -, -, haddI, hsubI, -, hsop⟩ := WP.Top.W3_all_holds
  have h5 : W5_toom3Mul := WP.W5.W5_toom3Mul_holds haddI hsubI hsop hsplit hshlV
  have h6 : W6a_all := WP.W6a.W6a_holds hsub
  obtain ⟨c0, c1, w0, hM⟩ := W5_toom3Mul_iff_mulAt.mp h5
  have hstd : W7_stdChar := WP.W7k3.W7_stdChar_bind _ hM (WP.W7k2.T3_le_quad c0 c1 w0)
    (WP.Top.W7_hyps_of WP.Top.W3_all_holds h5 h6)
  obtain ⟨C1, h1⟩ := exists_inst hcopy
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst hdrop
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst hisz
  obtain ⟨Iiz, hIiz⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst hdec
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5'⟩ := exists_inst hadd
  obtain ⟨Iad, hIad⟩ := h5' ()
  obtain ⟨C6, h6'⟩ := exists_inst hsub
  obtain ⟨Isb, hIsb⟩ := h6' ()
  obtain ⟨C7, h7⟩ := exists_inst hshl
  obtain ⟨Is1, hIs1⟩ := h7 1
  obtain ⟨C8, h8⟩ := exists_inst hshlV
  obtain ⟨Isv, hIsv⟩ := h8 ()
  obtain ⟨C9, h9⟩ := exists_inst hshrV
  obtain ⟨Irv, hIrv⟩ := h9 ()
  obtain ⟨C10, h10⟩ := exists_inst hcmp
  obtain ⟨Icm, hIcm⟩ := h10 ()
  obtain ⟨C11, h11⟩ := exists_inst hstd
  obtain ⟨Isf, hIsf⟩ := h11 false
  have s1 : SpecCopy Icp C1 := hIcp
  have s2 : SpecDrop Idr C2 := hIdr
  have s3 : SpecIsZero Iiz C3 := hIiz
  have s4 : SpecDec Idc C4 := hIdc
  have s5 : SpecAddNat Iad C5 := hIad
  have s6 : SpecSubNat Isb C6 := hIsb
  have s7 : SpecShlConst 1 Is1 C7 := hIs1
  have s8 : SpecShlVar Isv C8 := hIsv
  have s9 : SpecShrVar Irv C9 := hIrv
  have s10 : SpecCmpNat Icm C10 := hIcm
  have s11 : SpecStdChar false Isf C11 := hIsf
  refine ⟨⟨Icp, Idr, Iiz, Idc, Iad, Isb, Is1, Isv, Irv, Icm, Isf⟩,
    C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + 1, by omega, ?_⟩
  exact ⟨s1.mono (by omega), s2.mono (by omega), s3.mono (by omega), s4.mono (by omega),
    s5.mono (by omega), s6.mono (by omega), s7.mono (by omega), s8.mono (by omega),
    s9.mono (by omega), s10.mono (by omega), s11.mono (by omega)⟩

/-! ## The cost bound -/

theorem loopCost_le_mul (B : ℕ → ℕ) (b : ℕ) : ∀ N, (∀ i, i < N → B i + 1 ≤ b) →
    loopCost B N ≤ N * b + 1
  | 0, _ => by simp [loopCost]
  | N + 1, h => by
    have ih := loopCost_le_mul B b N (fun i hi => h i (by omega))
    have hN := h N (by omega)
    simp only [loopCost]
    rw [Nat.succ_mul]
    omega

theorem emitCost_le (C w : ℕ) :
    emitCost C C C w ≤ 4 * (C * (w + 1) ^ 2) + 6 * (w + 1) := by
  unfold emitCost
  have hl := loopCost_le_mul (fun i => C * (bitLen (i + 1) + 1) + 4 + C)
    (C * (w + 1) + C + 5) w (fun i hi => by
      have : bitLen (i + 1) ≤ w := le_trans (bitLen_le_self _) (by omega)
      have := Nat.mul_le_mul_left C (show bitLen (i + 1) + 1 ≤ w + 1 by omega)
      omega)
  have hb : bitLen w ≤ w := bitLen_le_self w
  have e1 : C * (bitLen w + 1) ≤ C * (w + 1) := Nat.mul_le_mul_left _ (by omega)
  have e2 : w * (C * (w + 1) + C + 5) ≤ C * (w + 1) ^ 2 + C * (w + 1) + 5 * (w + 1) := by
    have : w * (C * (w + 1) + C + 5) = w * (C * (w + 1)) + w * C + 5 * w := by ring
    rw [this]
    have h1 : w * (C * (w + 1)) ≤ C * (w + 1) ^ 2 := by
      calc w * (C * (w + 1)) ≤ (w + 1) * (C * (w + 1)) := Nat.mul_le_mul_right _ (by omega)
        _ = C * (w + 1) ^ 2 := by ring
    have h2 : w * C ≤ C * (w + 1) := by
      calc w * C ≤ (w + 1) * C := Nat.mul_le_mul_right _ (by omega)
        _ = C * (w + 1) := by ring
    omega
  have e3 : C ≤ C * (w + 1) := Nat.le_mul_of_pos_right C (by omega)
  have e4 : C * (w + 1) ≤ C * (w + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  omega

/-- **The builder's cost**: `J = 4`. -/
theorem costPT_le (C q D ℓ K w : ℕ) (a : Fin D → ℕ) (hsh : MidShapeOK q ℓ K w a) :
    costPT C q D ℓ K w ≤ 2000 * (C + 1) * (2 ^ ℓ * (w + 1) ^ 4 + (midHdr q ℓ K w a).length) := by
  obtain ⟨-, -, -, hlq, -, -, -, hw⟩ := hsh
  have hH := midHdr_length_ge q ℓ K w a
  have h2l : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hP1 : w + 1 ≤ (w + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hP2 : (w + 1) ^ 2 ≤ (w + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hPX : (w + 1) ^ 4 ≤ 2 ^ ℓ * (w + 1) ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
  have hlX : 2 ^ ℓ ≤ 2 ^ ℓ * (w + 1) ^ 4 := Nat.le_mul_of_pos_right _ (by positivity)
  have hE := emitCost_le C w
  have k1 : C * (w + 1) ≤ C * (w + 1) ^ 4 := Nat.mul_le_mul_left _ hP1
  have k2 : C * (w + 1) ^ 2 ≤ C * (w + 1) ^ 4 := Nat.mul_le_mul_left _ hP2
  have k3 : C * (3 * w + 3) = 3 * (C * (w + 1)) := by ring
  have hBody : costBody C w ≤ 414 * (C * (w + 1) ^ 4) + 24 * (w + 1) ^ 4 + 115 := by
    unfold costBody costVP costEI
    rw [k3]
    omega
  have hloop := loopCost_le_mul (fun i => C * (bitLen (i + 1) + 1) + costBody C w + C)
    (416 * (C * (w + 1) ^ 4) + 24 * (w + 1) ^ 4 + 116) (2 * 2 ^ ℓ) (fun i hi => by
      have hb : bitLen (i + 1) ≤ ℓ + 2 := bitLen_le_of_lt (by rw [pow_succ, pow_succ]; omega)
      have := Nat.mul_le_mul_left C (show bitLen (i + 1) + 1 ≤ w + 1 by omega)
      have hC : C ≤ C * (w + 1) ^ 4 := Nat.le_mul_of_pos_right C (by positivity)
      omega)
  have hL : 2 * 2 ^ ℓ * (416 * (C * (w + 1) ^ 4) + 24 * (w + 1) ^ 4 + 116) =
      832 * (C * (2 ^ ℓ * (w + 1) ^ 4)) + 48 * (2 ^ ℓ * (w + 1) ^ 4) + 232 * 2 ^ ℓ := by ring
  rw [hL] at hloop
  have hCX : C * (w + 1) ^ 4 ≤ C * (2 ^ ℓ * (w + 1) ^ 4) := Nat.mul_le_mul_left _ hPX
  have hC1 : C ≤ C * (2 ^ ℓ * (w + 1) ^ 4) := Nat.le_mul_of_pos_right C (by positivity)
  have hHR : costHR C q D ℓ K w ≤ 5 * (C * (midHdr q ℓ K w a).length) + 16 := by
    unfold costHR
    have := Nat.mul_le_mul_left C hH
    omega
  have hgoal : 2000 * (C + 1) * (2 ^ ℓ * (w + 1) ^ 4 + (midHdr q ℓ K w a).length) =
      2000 * (C * (2 ^ ℓ * (w + 1) ^ 4)) + 2000 * (2 ^ ℓ * (w + 1) ^ 4) +
      2000 * (C * (midHdr q ℓ K w a).length) + 2000 * (midHdr q ℓ K w a).length := by ring
  unfold costPT costSU costCL
  rw [hgoal]
  omega

/-- **K4.1, the phase table on the machine** (`PhaseTableMachineStmt`,
`Machine/Contracts/FFT.lean`; Lemma 6.1, `lem:phase-table`, and Section 6.4). Proved
with no hypotheses: the builder `ptProg` pushes `tabSyms w q ℓ (phaseTable q ℓ)` (the frozen
table, entries `phaseTableNum q ℓ j` computed by W7's `stdChar` kernel and exact shifts) on stack
`2`, restores the header on stack `1`, leaves stack `0` and all scratch unchanged, within
`2000·(C+1)·(2^ℓ·(w+1)^4 + |midHdr|)` steps (`J = 4`). -/
theorem _root_.SubNLogN.Machine.phaseTableMachine_holds : PhaseTableMachineStmt := by
  obtain ⟨I, C, -, hI⟩ := exists_PI
  refine ⟨4, 2000 * (C + 1), fun _ => ⟨Fin 32, inferInstance, inferInstance, I.R, ptProg I,
    I.R_finite, I.R_nonempty, ptProg_closed I, ?_⟩⟩
  intro q ℓ K w D a hrest S hcl hsh hS1
  exact HT.runs ((HT.ptProg hI S hcl q ℓ K w D a hrest hsh hS1).mono
    (costPT_le C q D ℓ K w a hsh))

end SubNLogN.Machine.FFT.Phase
