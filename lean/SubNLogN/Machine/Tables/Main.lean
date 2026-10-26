/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.MainCost
import SubNLogN.Machine.Tables.Embed
import SubNLogN.Machine.Tables.Inst

/-!
# K6 (`Machine/Tables/Main.lean`): the bridge tables on the machine

**Scope (honest summary).** Proves `BridgeTablesMachineStmt`
(`SubNLogN/Machine/Contracts/Tables.lean`, Lemma 4.6 (`lem:bridge-C`) (bridge Lemma C)(iii) and
Lemma B.3 (`lem:phase-tables`)) from two explicit fragment statements:
* `SetupStmt` (`SetupStmt.lean`: the parameter setup and cleanup programs), and
* `TapPhaseStmt` (`TapPhaseStmt.lean`: the whole tap phase).
The solver phase (all solver records `μ̂, â, γ̂` of `tabOf ω P t`, exact integers
`muN, ahN, gamN` of `SolMath.lean`) is proved here unconditionally (`SolEntry` … `SolLoop`).
The multiplier premise `MulBigContract` is not needed (the instances come from `exists_TB`).
Cost: `K · tabCost b` with `K = 4·Ks(C+1)(KM+1) + Kt(C+1)(KM+1) + 239355(C+1)(KM+1) + 24(C+7) +
7(C+10)` for the constants of the two pending statements, the instance constant `C` and the
multiplier constant `KM`.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt SubNLogN.Math.Common

theorem main_cost_le (C KM Ks Kt : ℕ) (b : BrPar) (hd : 2 ≤ b.d) (hS : ShapeOK b.t) :
    Ks * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1) +
      (Kt * (C + 1) * (KM + 1) * (tapPart b + tapTabLen b + b.setup) +
      (bitLen 8 + 1 + (fetchCost C (hdrSyms b.hdr).length + (C * (bitLen (b.d - 1 + 1) + 1) +
      (solLoopCost C KM b.wT b.t b.ω b.P +
        Ks * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1)))))) ≤
    (4 * (Ks * (C + 1) * (KM + 1)) + Kt * (C + 1) * (KM + 1) + 239355 * ((C + 1) * (KM + 1)) +
      24 * (C + 7) + 7 * (C + 10)) * tabCost b := by
  have hTdef : tabCost b = tapPart b + deconvPart b + tabOnce b + tapTabLen b + solTabLen b +
      b.setup := rfl
  have hw := solTabLen_ge b hd hS
  have hsetup : b.setup = ((hdrSyms b.hdr).length + 1) ^ 3 := rfl
  have hset1 : 1 ≤ b.setup := by rw [hsetup]; exact Nat.one_le_pow _ _ (by omega)
  have hdH : b.d ≤ (hdrSyms b.hdr).length :=
    le_trans (by simp [BrPar.hdr]; omega) (length_le_length_hdrSyms b.hdr)
  have hf : fetchCost C (hdrSyms b.hdr).length ≤ 4 * ((C + 3) * b.setup) := by
    unfold fetchCost
    rw [hsetup]
    have h1 : ((hdrSyms b.hdr).length + 2) ^ 2 ≤ 4 * ((hdrSyms b.hdr).length + 1) ^ 3 := by
      nlinarith
    calc (C + 3) * ((hdrSyms b.hdr).length + 2) ^ 2
        ≤ (C + 3) * (4 * ((hdrSyms b.hdr).length + 1) ^ 3) := Nat.mul_le_mul_left _ h1
      _ = 4 * ((C + 3) * ((hdrSyms b.hdr).length + 1) ^ 3) := by ring
  have hc : C * (bitLen (b.d - 1 + 1) + 1) ≤ C * b.setup := by
    apply Nat.mul_le_mul_left
    have h1 : bitLen (b.d - 1 + 1) ≤ b.d - 1 + 1 := bitLen_le_self _
    have h2 : (hdrSyms b.hdr).length + 1 ≤ ((hdrSyms b.hdr).length + 1) ^ 3 :=
      Nat.le_self_pow (by norm_num) _
    rw [hsetup]
    omega
  have hb8 : bitLen 8 + 1 ≤ 5 := by
    have := bitLen_le_of_lt (show 8 < 2 ^ 4 by norm_num); omega
  have hl := solLoopCost_le C KM b hS
  have hT1 : 1 ≤ tabCost b := by omega
  have p1 : Ks * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1) ≤
      2 * (Ks * (C + 1) * (KM + 1) * tabCost b) := by
    calc Ks * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1)
        ≤ Ks * (C + 1) * (KM + 1) * (2 * tabCost b) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Ks * (C + 1) * (KM + 1) * tabCost b) := by ring
  have p2 : Kt * (C + 1) * (KM + 1) * (tapPart b + tapTabLen b + b.setup) ≤
      Kt * (C + 1) * (KM + 1) * tabCost b := Nat.mul_le_mul_left _ (by omega)
  have p3 : 239355 * ((C + 1) * (KM + 1)) * deconvPart b ≤
      239355 * ((C + 1) * (KM + 1)) * tabCost b := Nat.mul_le_mul_left _ (by omega)
  have p4 : 24 * (C + 7) * solTabLen b ≤ 24 * (C + 7) * tabCost b :=
    Nat.mul_le_mul_left _ (by omega)
  have p5 : (C + 3) * b.setup ≤ (C + 3) * tabCost b := Nat.mul_le_mul_left _ (by omega)
  have p6 : C * b.setup ≤ C * tabCost b := Nat.mul_le_mul_left _ (by omega)
  have p7 : C + 6 ≤ (C + 6) * tabCost b := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith [p1, p2, p3, p4, p5, p6, p7, hf, hc, hb8, hl]

/-- **K6 (Lemma 4.6 (`lem:bridge-C`) (bridge Lemma C)(iii), Lemma B.3 (`lem:phase-tables`)) on the machine.** The bridge
tables of `tabOf ω P t` are generated within `K · tabCost b`, assuming the two fragment
statements `SetupStmt` (parameter setup/cleanup) and `TapPhaseStmt` (tap phase). -/
theorem bridgeTablesMachine_holds (hSetup : SetupStmt) (hTapPh : TapPhaseStmt) :
    BridgeTablesMachineStmt := by
  intro _
  obtain ⟨Mul, ⟨KM, hKM⟩, I, C, -, hI⟩ := exists_TB
  obtain ⟨Ks, hs⟩ := hSetup
  obtain ⟨setupP, cleanP, hsc, hcc, hsS, hcS⟩ := hs I Mul C KM hI hKM
  obtain ⟨Kt, ht⟩ := hTapPh
  obtain ⟨tapP, htc, htS⟩ := ht I Mul C KM hI hKM
  refine ⟨4 * (Ks * (C + 1) * (KM + 1)) + Kt * (C + 1) * (KM + 1) +
      239355 * ((C + 1) * (KM + 1)) + 24 * (C + 7) + 7 * (C + 10),
    fun _ => ⟨Fin 61, inferInstance, inferInstance, I.R,
    callInj tEmb (lensId I.R) (mainProg I setupP tapP cleanP), I.R_finite, I.R_nonempty,
    closed_callInj _ _ (mainProg_closed I hsc htc hcc), ?_⟩⟩
  intro b rpar S hcl hd hS hω hw hfit hpar
  refine runs_host ?_ (hout_update2 S _ _)
  rw [comp_tEmb_update2]
  exact (HT.mainProg_spec hI hKM
    (costS := fun b => Ks * (C + 1) * (KM + 1) * (tabOnce b + b.setup + b.wT + 1))
    (costT := fun b => Kt * (C + 1) * (KM + 1) * (tapPart b + tapTabLen b + b.setup))
    hsS hcS htS b rpar (S ∘ tEmb) hd hS hω hw hfit hpar (kclean_host hcl)).mono
    (main_cost_le C KM Ks Kt b hd hS)

end SubNLogN.Machine.Tables
