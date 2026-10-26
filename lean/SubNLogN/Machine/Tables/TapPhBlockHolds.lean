/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapPhBlock
import SubNLogN.Machine.Tables.TapPhRank

/-!
# K6: `TapBlockStmt` from `TapRecStmt` (`Machine/Tables/TapPhBlockHolds.lean`)

Instantiates `TapPhBlock.tapBlock_of` (`TapPhBlock.lean`) with the rank fragment
`TapPhAux.rankProg` (`HT.rankProg_spec`, `TapPhRank.lean`) and its cost bound
`rankCost C KM β ≤ 60·(C+1)(KM+1)(β+1)^3` (`rankCost_le`).

**Scope (honest summary).** `tapBlock_holds : TapRecStmt → TapBlockStmt`, fully proved; the only
hypothesis is the tap-record contract `TapRecStmt`.
-/

namespace SubNLogN.Machine.Tables.TapPhBlock

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables
  SubNLogN.Math.Bridge SubNLogN.Math.Common

theorem rankCost_le (C KM β : ℕ) :
    TapPhAux.rankCost C KM β ≤ 60 * (C + 1) * (KM + 1) * (β + 1) ^ 3 := by
  have hQ1 : 1 ≤ (C + 1) * (KM + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hCQ : C ≤ (C + 1) * (KM + 1) :=
    le_trans (Nat.le_succ C) (Nat.le_mul_of_pos_right _ (by omega))
  have hCK : C * KM ≤ (C + 1) * (KM + 1) := Nat.mul_le_mul (Nat.le_succ C) (Nat.le_succ KM)
  have hX2 : β + 1 ≤ (β + 1) ^ 2 := by nlinarith
  have hY1 : 1 ≤ (β + 1) ^ 2 := le_trans (by omega) hX2
  have hS : 17 * (C * (β + 1) ^ 2) + C * (KM * (β + 1) ^ 2) + C + 3 * β + 8 ≤
      30 * ((C + 1) * (KM + 1) * (β + 1) ^ 2) := by
    have a1 : C * (β + 1) ^ 2 ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 := Nat.mul_le_mul_right _ hCQ
    have a2 : C * (KM * (β + 1) ^ 2) ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 := by
      calc C * (KM * (β + 1) ^ 2) = C * KM * (β + 1) ^ 2 := by ring
        _ ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 := Nat.mul_le_mul_right _ hCK
    have a3 : C ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 :=
      le_trans hCQ (Nat.le_mul_of_pos_right _ hY1)
    have a4 : β + 1 ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 :=
      le_trans hX2 (Nat.le_mul_of_pos_left _ hQ1)
    omega
  have b1 : β * (17 * (C * (β + 1) ^ 2) + C * (KM * (β + 1) ^ 2) + C + 3 * β + 8) ≤
      30 * ((β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2)) := by
    calc β * (17 * (C * (β + 1) ^ 2) + C * (KM * (β + 1) ^ 2) + C + 3 * β + 8)
        ≤ (β + 1) * (30 * ((C + 1) * (KM + 1) * (β + 1) ^ 2)) :=
          Nat.mul_le_mul (Nat.le_succ β) hS
      _ = 30 * ((β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2)) := by ring
  have b2 : β * (C * (β + 1) + C + 1) ≤ 3 * ((β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2)) := by
    have c1 : C * (β + 1) + C + 1 ≤ 3 * ((C + 1) * (KM + 1) * (β + 1) ^ 2) := by
      have d1 : C * (β + 1) ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 := by
        calc C * (β + 1) ≤ (C + 1) * (KM + 1) * (β + 1) := Nat.mul_le_mul_right _ hCQ
          _ ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 := Nat.mul_le_mul_left _ hX2
      have d2 : C ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 :=
        le_trans hCQ (Nat.le_mul_of_pos_right _ hY1)
      have d3 : 1 ≤ (C + 1) * (KM + 1) * (β + 1) ^ 2 := Nat.mul_pos hQ1 hY1
      omega
    calc β * (C * (β + 1) + C + 1) ≤ (β + 1) * (3 * ((C + 1) * (KM + 1) * (β + 1) ^ 2)) :=
          Nat.mul_le_mul (Nat.le_succ β) c1
      _ = 3 * ((β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2)) := by ring
  have b3 : C * (β + 1) ≤ (β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2) := by
    calc C * (β + 1) ≤ ((C + 1) * (KM + 1) * (β + 1) ^ 2) * (β + 1) :=
          Nat.mul_le_mul_right _ (le_trans hCQ (Nat.le_mul_of_pos_right _ hY1))
      _ = (β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2) := by ring
  have b4 : β * (β + 1) ≤ (β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2) := by
    calc β * (β + 1) ≤ (β + 1) * (β + 1) := Nat.mul_le_mul_right _ (Nat.le_succ β)
      _ ≤ (β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (le_trans hX2 (Nat.le_mul_of_pos_left _ hQ1))
  have b5 : 1 ≤ (β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos hQ1 hY1)
  have eR : 60 * (C + 1) * (KM + 1) * (β + 1) ^ 3 =
      60 * ((β + 1) * ((C + 1) * (KM + 1) * (β + 1) ^ 2)) := by ring
  have e3 : β * (17 * (C * (β + 1) ^ 2) + C * (KM * (β + 1) ^ 2) + C + 3 * β + 8 +
      C * (β + 1) + C + 1) =
      β * (17 * (C * (β + 1) ^ 2) + C * (KM * (β + 1) ^ 2) + C + 3 * β + 8) +
        β * (C * (β + 1) + C + 1) := by ring
  unfold TapPhAux.rankCost TapPhAux.rkStepCost
  omega

/-- The rank fragment satisfies `RankProgSpec` (with all temporaries empty). -/
theorem rankProgSpec_holds : RankProgSpec TapPhAux.rankProg TapPhAux.rankCost := by
  intro I Mul C KM hI hMul
  refine ⟨TapPhAux.rankProg_closed I, ?_⟩
  intro B L r β hL hr hβA hβL hru hA hI' hSH hra htmp ρ
  exact TapPhAux.HT.rankProg_spec hI hMul B L r β hL hr hβA hβL hru hA hI' hSH hra
    (htmp 40 (by decide)) (htmp 41 (by decide)) (htmp 44 (by decide)) (htmp 45 (by decide))
    (htmp 46 (by decide)) (htmp 47 (by decide)) (htmp 48 (by decide)) (htmp 49 (by decide))
    (htmp 50 (by decide)) (htmp 51 (by decide)) (htmp 52 (by decide)) ρ

/-- **`TapBlockStmt` holds, given the tap-record machine** (`TapRecStmt`). -/
theorem tapBlock_holds (hTap : TapRecStmt) : TapBlockStmt :=
  tapBlock_of TapPhAux.rankProg TapPhAux.rankCost 60 rankCost_le rankProgSpec_holds hTap

end SubNLogN.Machine.Tables.TapPhBlock
