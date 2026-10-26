import WP.W9fN.Prologue

/-!
# WP.W9fN.PrologueRun — `prologue_runs`
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts

theorem prologue_runs (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) (q H μ : ℕ) (a : ℤ)
    (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (WP.W9f.solW H) o))
    (S : HK → List Sym) (Ys : Array (ℤ × ℤ)) (rIn r2 r3 r4 r6 : List Sym)
    (ht1 : 1 ≤ Ys.size) (hqH : q + 2 ≤ H) (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a)
    (haW : bitLen a.natAbs ≤ H) (hY : ArrW H Ys)
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr6 : TermOK r6)
    (hS0 : S kIN = blkE Ys.toList ++ rIn) (hS2 : S kPQ = natSyms q ++ r2)
    (hS3 : S kPH = natSyms H ++ r3) (hS4 : S kPMU = natSyms μ ++ r4)
    (hS6 : S kPA = intSyms a ++ r6) :
    ∃ Sx, LS q H μ a S Ys rIn 0 Sx ∧ RunsS (prologue I) S Sx (prologueCost C H) := by
  have r0 := LN.initVars_runs I S
  set env0 : V → ℤ := fun _ => 0 with henv0
  have r1 := LN.loadNat_runs I vL_ne_PQ vL_ne_TMP kP_ne_TMP.1 .T8 S S env0 q r2 hr2 hS2
  set envA := Function.update env0 .T8 (q : ℤ) with henvA
  have r2' := LN.loadNat_runs I vL_ne_PH vL_ne_TMP kP_ne_TMP.2.1 .HV S S envA H r3 hr3 hS3
  set envB := Function.update envA .HV (H : ℤ) with henvB
  have r3' := LN.loadNat_runs I vL_ne_PMU vL_ne_TMP kP_ne_TMP.2.2.1 .MU S S envB μ r4 hr4 hS4
  set envC := Function.update envB .MU (μ : ℤ) with henvC
  have r4' := LN.loadInt_runs I vL_ne_PA vL_ne_TMP kP_ne_TMP.2.2.2 .DA S S envC a r6 hr6 hS6
  set envD := Function.update envC .DA a with henvD
  have r5 := LN.hst_compile I (kap C Mul (WP.W9f.solW H)) hok pSetup S S envD
  have hD8 : envD .T8 = q := by simp [henvD, henvC, henvB, henvA]
  have hDH : envD .HV = H := by simp [henvD, henvC, henvB]
  have hDM : envD .MU = μ := by simp [henvD, henvC]
  have hDA : envD .DA = a := by simp [henvD]
  have hD0 : ∀ v, v ≠ .T8 → v ≠ .HV → v ≠ .MU → v ≠ .DA → envD v = 0 := by
    intro v h1 h2 h3 h4
    simp [henvD, henvC, henvB, henvA, henv0, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]
  obtain ⟨hE1, hET, hES2, hESS, hEMC, hEH, hEf⟩ := ev_pSetup envD q hD8
    (hD0 .ZERO (by decide) (by decide) (by decide) (by decide))
  set envE := ev pSetup envD with henvE
  have hIN0 : S kIN = entrySyms (read1D Ys 0) ++ (blkE (Ys.toList.drop 1) ++ rIn) := by
    have e := drop_read1D Ys 0 (by omega)
    rw [List.drop_zero] at e
    rw [hS0]
    conv_lhs => rw [e]
    rw [blkE_cons', List.append_assoc]
  have r6' := LN.popEntry_runs I (src := kIN) (tmp := kTMP) vL_ne_IN vL_ne_TMP kIN_ne_kTMP
    (v1 := .Y1) (v2 := .Y2) (by decide) S S envE (read1D Ys 0) _ hIN0
  set envF := Function.update (Function.update envE .Y1 (read1D Ys 0).1) .Y2 (read1D Ys 0).2
    with henvF
  set X1 := Function.update S kIN (blkE (Ys.toList.drop 1) ++ rIn) with hX1
  have r7 := LN.pushC_runs I vL_ne_ZS .mark S X1 envF
  set X2 := Function.update X1 kZS (.mark :: X1 kZS) with hX2
  have r8 := LN.pushEntry_runs I (dst := kZS) (tmp := kTMP) vL_ne_ZS vL_ne_TMP kZS_ne_kTMP
    .Z1 .Z2 S X2 envF
  -- values
  have hFE : ∀ v, v ≠ .Y1 → v ≠ .Y2 → envF v = envE v := by
    intro v h1 h2
    rw [henvF, Function.update_of_ne h2, Function.update_of_ne h1]
  have hFE' : ∀ v, v ≠ .Y1 → v ≠ .Y2 → v ≠ .ONE → v ≠ .T1 → v ≠ .S2 → v ≠ .SS → v ≠ .MC →
      v ≠ .HALF → envF v = envD v := by
    intro v h1 h2 h3 h4 h5 h6 h7 h8
    rw [hFE v h1 h2, hEf v h3 h4 h5 h6 h7 h8]
  have hFZ1 : envF .Z1 = 0 := by
    rw [hFE' .Z1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hD0 .Z1 (by decide) (by decide) (by decide) (by decide)]
  have hFZ2 : envF .Z2 = 0 := by
    rw [hFE' .Z2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hD0 .Z2 (by decide) (by decide) (by decide) (by decide)]
  -- the final non-variable stacks
  have hX : Function.update X2 kZS (entrySyms (envF .Z1, envF .Z2) ++ X2 kZS) =
      Xn S Ys rIn (W8.zPartNyqBarrett q H μ a Ys 0) 0 := by
    rw [hFZ1, hFZ2, hX2, Function.update_self, Function.update_idem, hX1,
      Function.update_of_ne kIN_ne_kZS.symm]
    have e : (W8.zPartNyqBarrett q H (μ : ℤ) a Ys 0).toList.reverse = [((0 : ℤ), (0 : ℤ))] := rfl
    rw [Xn, e, blkE_cons']
    simp [blkE, blk]
  have hy0 : EntryW H (read1D Ys 0) := hY _ (read1D_mem Ys 0 (by omega))
  have hp : Prm envF q H μ a a := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hFE .S2 (by decide) (by decide), hES2]
    · rw [hFE' .HV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hDH]
    · rw [hFE' .MU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hDM]
    · rw [hFE' .DA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hDA]
    · rw [hFE .MC (by decide) (by decide), hEMC, hDA]
    · rw [hFE' .ZERO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hD0 .ZERO (by decide) (by decide) (by decide) (by decide)]
    · rw [hFE .ONE (by decide) (by decide), hE1]
    · rw [hFE .SS (by decide) (by decide), hESS]
    · rw [hFE .HALF (by decide) (by decide), hEH]
  have hmu := bitLen_mu_le H μ a hμ
  have hsW : WP.W9f.solW H = 8 * (H + 1) := rfl
  have hw : ∀ v, bitLen (envF v).natAbs ≤ βstep H v := by
    intro v
    by_cases hY2 : v = .Y2
    · subst hY2
      rw [henvF, Function.update_self]
      exact hy0.2
    by_cases hY1 : v = .Y1
    · subst hY1
      rw [henvF, Function.update_of_ne (by decide), Function.update_self]
      exact hy0.1
    rw [hFE v hY1 hY2]
    by_cases h1 : v = .ONE
    · subst h1
      rw [hE1]
      exact le_of_eq bitLen_one'
    by_cases h2 : v = .T1
    · subst h2
      rw [hET]
      show bitLen 2 ≤ WP.W9f.solW H
      rw [bitLen_two', hsW]
      omega
    by_cases h3 : v = .S2
    · subst h3
      rw [hES2]
      show bitLen (q + 2) ≤ WP.W9f.solW H
      have := bitLen_le_self' (q + 2)
      rw [hsW]
      omega
    by_cases h4 : v = .SS
    · subst h4
      rw [hESS]
      show bitLen (2 ^ (q + 2)) ≤ H + 1
      exact bitLen_le_iff.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega))
    by_cases h5 : v = .MC
    · subst h5
      rw [hEMC, hDA]
      exact haW
    by_cases h6 : v = .HALF
    · subst h6
      rw [hEH]
      show bitLen (2 ^ (q + 1)) ≤ WP.W9f.solW H
      have := bitLen_le_iff.mpr (Nat.pow_lt_pow_right (by norm_num) (show q + 1 < q + 2 by omega))
      rw [hsW]
      omega
    rw [hEf v h1 h2 h3 h4 h5 h6]
    by_cases h7 : v = .T8
    · subst h7
      rw [hD8]
      show bitLen q ≤ WP.W9f.solW H
      have := bitLen_le_self' q
      rw [hsW]
      omega
    by_cases h8 : v = .HV
    · subst h8
      rw [hDH]
      exact bitLen_le_self' H
    by_cases h9 : v = .MU
    · subst h9
      rw [hDM]
      exact hmu
    by_cases h10 : v = .DA
    · subst h10
      rw [hDA]
      exact haW
    rw [hD0 v h7 h8 h9 h10]
    show bitLen 0 ≤ _
    rw [bitLen_zero']
    exact Nat.zero_le _
  have hz : (envF .Z1, envF .Z2) = read1D (W8.zPartNyqBarrett q H μ a Ys 0) 0 := by
    rw [hFZ1, hFZ2]
    rfl
  refine ⟨_, ⟨envF, by rw [hX], ⟨hp, hz, hw⟩⟩,
    (RunsS.seq r0 (RunsS.seq r1 (RunsS.seq r2' (RunsS.seq r3' (RunsS.seq r4'
      (RunsS.seq r5 (RunsS.seq r6' (RunsS.seq r7 r8)))))))).of_eq rfl ?_⟩
  -- cost
  have c5 := pSetup_cost C Mul (WP.W9f.solW H) envD q H hD8
    (hD0 .ZERO (by decide) (by decide) (by decide) (by decide)) hqH (by rw [hDA]; exact haW)
    ⟨hD0 .ONE (by decide) (by decide) (by decide) (by decide),
      hD0 .T1 (by decide) (by decide) (by decide) (by decide),
      hD0 .S2 (by decide) (by decide) (by decide) (by decide),
      hD0 .SS (by decide) (by decide) (by decide) (by decide),
      hD0 .MC (by decide) (by decide) (by decide) (by decide),
      hD0 .HALF (by decide) (by decide) (by decide) (by decide)⟩
  have eY1 : envE .Y1 = 0 := by
    rw [hEf .Y1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hD0 .Y1 (by decide) (by decide) (by decide) (by decide)]
  have eY2 : envE .Y2 = 0 := by
    rw [hEf .Y2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hD0 .Y2 (by decide) (by decide) (by decide) (by decide)]
  have e0 : env0 .T8 = 0 := rfl
  have eA : envA .HV = 0 := by simp [henvA, henv0]
  have eB : envB .MU = 0 := by simp [henvB, henvA, henv0]
  have eC : envC .DA = 0 := by simp [henvC, henvB, henvA, henv0]
  have hq' : bitLen q ≤ H := (bitLen_le_self' q).trans (by omega)
  have hH' : bitLen H ≤ H := bitLen_le_self' H
  rw [e0, eA, eB, eC, eY1, eY2, hFZ1, hFZ2]
  simp only [Int.natAbs_zero, bitLen_zero']
  have := hy0.1
  have := hy0.2
  unfold prologueCost
  omega

#assert_std_axioms prologue_runs

end WP.W9fN
