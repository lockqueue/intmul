/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedIODec
import SubNLogN.Machine.Walsh.PosPermSchedDefs

/-!
# Schedule compiler IO on the kernel stacks (`Machine/Walsh/PosPermSchedIOStk.lean`)

The generic decoders of `PosPermSchedIODec.lean` instantiated on `Stk = KLoc (Fin 3) Scr`
(`PosPermSchedState.lean`), proving the two decode phases of the schedule compiler in the form
agreed with the assembly (`PosPermSchedMain.lean`):

* `decHdr_holds : DecHdrStmt`: header on stack `0`, temporaries `B1`, `q5`, `q6`; the registers
  `d`, `K`, `m` receive `una d`, `una K`, `una m`; cost `80 ((m + d + K + 1)^2 + |permHdr|)`;
* `decPi_holds : DecPiStmt`: π on stack `1`, temporaries `B1`, `B2`, `q5`–`q8`;
  `PT := utab (finVals π) ++ PT`; cost `64 ((m + 1)^3 + |permSyms π|)`.

In both, every other stack ends exactly as it started (`Runs` fixes the final state).

**Scope (honest summary).** Proves `DecHdrStmt` and `DecPiStmt` (defined here), nothing else.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability

/-! ## The agreed statements -/

/-- **Header decode**: from `permHdr P d r w K m` on stack `0` and clean scratch, set the
registers `d, K, m`; everything else (stack `0` included) is restored. -/
def DecHdrSpec (P : SProg Stk) : Prop :=
  ∃ C k : ℕ, ∀ (Ph d r w K m : ℕ) (hrest : List Sym) (S : Stk → List Sym),
    KClean S → S (.inl 0) = permHdr Ph d r w K m ++ hrest →
    Runs P S
      (Function.update (Function.update (Function.update S (rg .d) (una d)) (rg .K) (una K))
        (rg .m) (una m))
      (fun _ => True) (C * ((m + d + K + 1) ^ k + (permHdr Ph d r w K m).length))

/-- Header decode, frozen target form. -/
def DecHdrStmt : Prop := ∃ P : SProg Stk, P.Closed ∧ DecHdrSpec P

/-- **Map decode**: from `permSyms π` on stack `1` and `m` in its register, push the table
`utab (finVals π)` onto `PT`; everything else (stack `1` included) is restored. -/
def DecPiSpec (P : SProg Stk) : Prop :=
  ∃ C k : ℕ, ∀ (m : ℕ) (π : Fin m → Fin m) (prest : List Sym) (S : Stk → List Sym),
    S (.inl 1) = permSyms π ++ prest → S (rg .m) = una m → ScrClean S [.m, .d, .K] →
    Runs P S (Function.update S (rs .PT) (utab (finVals π) ++ S (rs .PT)))
      (fun _ => True) (C * ((m + 1) ^ k + (permSyms π).length))

/-- Map decode, frozen target form. -/
def DecPiStmt : Prop := ∃ P : SProg Stk, P.Closed ∧ DecPiSpec P

namespace PSIO

/-- The header decoder on `Stk`. -/
def stkDecHdr : SProg Stk := decHdr (.inl 0) (rs .B1) (rg .d) (rg .K) (rg .m) (rg .q5) (rg .q6)

theorem stk_nodup_hdr :
    [(.inl 0 : Stk), rs .B1, rg .d, rg .K, rg .m, rg .q5, rg .q6].Nodup := by
  decide

/-- The π-table decoder on `Stk`. -/
def stkDecPi : SProg Stk :=
  decTbl (.inl 1) (rs .B1) (rg .m) (rs .PT) (rg .q7) (rg .q8) (rs .B2) (rg .q5) (rg .q6)

theorem stk_nodup_pi :
    [(.inl 1 : Stk), rs .B1, rg .m, rs .PT, rg .q7, rg .q8, rs .B2, rg .q5, rg .q6].Nodup := by
  decide

end PSIO

/-- **Header decode holds** (`PSIO.stkDecHdr`, `C = 80`, `k = 2`). -/
theorem decHdr_holds : DecHdrStmt := by
  refine ⟨PSIO.stkDecHdr, PSIO.closed_decHdr _ _ _ _ _ _ _, 80, 2,
    fun Ph d r w K m hrest S hK hh => ?_⟩
  refine runs_weak (PSIO.runs_decHdr PSIO.stk_nodup_hdr S Ph d r w K m hrest hh (hK _) (hK _)
    (hK _) (hK _) (hK _) (hK _)) rfl ?_
  have h1 : (d + 1) ^ 2 ≤ (m + d + K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (K + 1) ^ 2 ≤ (m + d + K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : (m + 1) ^ 2 ≤ (m + d + K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h4 : 1 ≤ (m + d + K + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **Map decode holds** (`PSIO.stkDecPi`, `C = 64`, `k = 3`). -/
theorem decPi_holds : DecPiStmt := by
  refine ⟨PSIO.stkDecPi, PSIO.closed_decTbl _ _ _ _ _ _ _ _ _, 64, 3,
    fun m π prest S hpi hn hsc => ?_⟩
  obtain ⟨hq, -, -, hB1, hB2, -, -⟩ := hsc
  refine runs_weak (PSIO.runs_decPi PSIO.stk_nodup_pi S π prest hpi hn hB1 (hq _ (by decide))
    (hq _ (by decide)) hB2 (hq _ (by decide)) (hq _ (by decide))) rfl ?_
  have hA : m * (22 * (m + 1) ^ 2 + 8 * m + 20) ≤
      (m + 1) * (22 * (m + 1) ^ 2 + 8 * (m + 1) + 20) := Nat.mul_le_mul (by omega) (by omega)
  have hB : (m + 1) * (22 * (m + 1) ^ 2 + 8 * (m + 1) + 20) =
      22 * (m + 1) ^ 3 + 8 * (m + 1) ^ 2 + 20 * (m + 1) := by ring
  have hC : (m + 1) ^ 2 ≤ (m + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hD : (m + 1) ^ 1 ≤ (m + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_one] at hD
  omega

end SubNLogN.Machine.Walsh.PosPermSchedAux
