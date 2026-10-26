/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.DropSegs
import SubNLogN.Machine.Tables.Embed
import SubNLogN.Machine.Tables.Inst

/-!
# K6 (`Machine/Tables/Drop.lean`): dropping the bridge tables — `DropTablesStmt` proved

**Scope (honest summary).** Proves `dropTables_holds : DropTablesStmt`
(`SubNLogN/Machine/Contracts/Tables.lean:93`) with **no hypotheses**.

Program (`dropProg`, host stacks `TL`, scratch `.inr 0 … .inr 3`): fetch the axis count `d`
(field 8 of `hdrSyms b.hdr`, `Header.lean`), compute `d - 1` (the number of blocks of each table:
`|spreadOrder d| = |deconvOrder d| = d - 1`), then pop `d - 1` `mark`-terminated blocks from
`tapTab` and from `solTab` (`DropSegs.lean`). Blocks contain only bits and `sep`
(`mark_not_mem_carrSyms`), so "pop until `mark`" removes exactly one block; the rest `rtap`,
`rsol` below the tables is never read. The bound `|tapTabSyms| ≤ tapTabLen b` uses that a tap block
lists distinct lower-digit tuples (`length_tapBlock_le`); the hypothesis `TablesFit` of the
contract is not needed. Cost `O(tapTabLen b + solTabLen b + b.setup)`.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge

/-- Scratch stacks of the dropper. -/
abbrev dK : TL := .inr 0
abbrev dT : TL := .inr 1
abbrev dD : TL := .inr 2
abbrev dE : TL := .inr 3

/-- **The table dropper.** -/
def dropProg (I : TB) : TP I :=
  (tnat I dK 8).seq ((fetchProg I dK dT dD).seq ((decPos I dD).seq ((tcp I dD dE).seq
    ((tcd I dD (dropBlock I sTap)).seq (tcd I dE (dropBlock I sSol))))))

theorem dropProg_closed (I : TB) : (dropProg I).Closed :=
  ⟨pushBits_closed _ _, ⟨fetchProg_closed I _ _ _, ⟨decPos_closed I _, ⟨callI_closed _ _ _ _,
    ⟨tcd_closed I _ _ (dropBlock_closed I _), tcd_closed I _ _ (dropBlock_closed I _)⟩⟩⟩⟩⟩

theorem hdr_length (b : BrPar) : b.hdr.length = 9 + b.d := by
  simp [BrPar.hdr]
  omega

theorem hdr_get8 (b : BrPar) (h : 8 < b.hdr.length) : b.hdr[8] = b.d := by
  simp [BrPar.hdr]

/-- The dropper's cost, piece by piece. -/
noncomputable def dropCost (C : ℕ) (b : BrPar) (T : BridgeTables b.t) : ℕ :=
  (bitLen 8 + 1) + fetchCost C (hdrSyms b.hdr).length + (C + (C * (bitLen b.d + 1) + 1) + 1) +
    C * (bitLen (b.d - 1) + 1) + dropSegsCost C (tapSegs b.wT b.P b.t T) +
    dropSegsCost C (solSegs b.wT b.P b.t T)

section Spec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.dropProg_spec (hI : I.Spec Mul C) (b : BrPar) (T : BridgeTables b.t)
    (rpar rtap rsol : List Sym) (B : TL → List Sym) (hcl : ∀ j, B (.inr j) = [])
    (hP : B sPar = hdrSyms b.hdr ++ rpar) (hT : B sTap = tapTabSyms b.wT b.P b.t T ++ rtap)
    (hS : B sSol = solTabSyms b.wT b.P b.t T ++ rsol) (ρ : List (TP I)) :
    HT ρ B (dropProg I) (Function.update (Function.update B sTap rtap) sSol rsol)
      (dropCost C b T) := by
  have hk : 8 < b.hdr.length := by rw [hdr_length]; omega
  have s1 := HT.tnat_spec (I := I) dK 8 B ρ
  rw [hcl] at s1
  have s2 := HT.fetch_spec hI dK dT dD (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (Function.update B dK (natSyms 8 ++ [])) b.hdr 8 hk [] rpar TermOK.nil
    (by rw [Function.update_self]) (by rw [Function.update_of_ne (by decide), hP])
    (by rw [Function.update_of_ne (by decide), hcl]) ρ
  rw [hdr_get8 b hk, Function.update_of_ne (by decide), hcl] at s2
  set B2 := Function.update (Function.update (Function.update B dK (natSyms 8 ++ [])) dK []) dD
    (natSyms b.d ++ []) with hB2
  have s3 := HT.decPos_spec hI dD B2 b.d [] TermOK.nil (by rw [hB2, Function.update_self]) ρ
  set B3 := Function.update B2 dD (natSyms (b.d - 1) ++ []) with hB3
  have s4 := HT.tcp_spec hI dD dE (by decide) B3 (b.d - 1) [] TermOK.nil
    (by rw [hB3, Function.update_self]) ρ
  set B4 := Function.update B3 dE (natSyms (b.d - 1) ++ B3 dE) with hB4
  have s5 := HT.dropSegs_spec hI sTap dD (by decide) (tapSegs b.wT b.P b.t T)
    (mark_not_mem_tapSegs _ _ _ _) rtap B4
    (by
      rw [hB4, hB3, hB2]
      simp (disch := decide) only [Function.update_of_ne]
      rw [hT, tapTabSyms_eq_segs])
    (by
      rw [hB4, hB3]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      rw [length_tapSegs, List.append_nil]) ρ
  set B5 := Function.update (Function.update B4 dD []) sTap rtap with hB5
  have s6 := HT.dropSegs_spec hI sSol dE (by decide) (solSegs b.wT b.P b.t T)
    (mark_not_mem_solSegs _ _ _ _) rsol B5
    (by
      rw [hB5, hB4, hB3, hB2]
      simp (disch := decide) only [Function.update_of_ne]
      rw [hS, solTabSyms_eq_segs])
    (by
      rw [hB5, hB4, hB3, hB2]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, hcl]
      rw [length_solSegs, List.append_nil]) ρ
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 (HT.seq s5 s6))))).of_eq ?_ ?_
  · rw [hB5, hB4, hB3, hB2]
    funext g
    by_cases h1 : g = sSol
    · subst h1; simp
    by_cases h2 : g = sTap
    · subst h2; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases h3 : g = dE
    · subst h3; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hcl]
    by_cases h4 : g = dD
    · subst h4; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hcl]
    by_cases h5 : g = dK
    · subst h5; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hcl]
    simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5]
  · unfold dropCost
    omega

end Spec

/-! ## Cost bound -/

theorem bitLen_le_hdr_d (b : BrPar) : b.d + 9 ≤ (hdrSyms b.hdr).length := by
  have := length_le_length_hdrSyms b.hdr
  rw [hdr_length] at this
  omega

theorem dropCost_le (C : ℕ) (b : BrPar) (T : BridgeTables b.t) :
    dropCost C b T ≤ 30 * (C + 10) * (tapTabLen b + solTabLen b + b.setup) := by
  set H := (hdrSyms b.hdr).length with hH
  have hdH := bitLen_le_hdr_d b
  rw [← hH] at hdH
  have hb1 : bitLen b.d ≤ H := le_trans (bitLen_le_self _) (by omega)
  have hb2 : bitLen (b.d - 1) ≤ H := le_trans (bitLen_le_self _) (by omega)
  have ht := sum_tapSegs_le b T
  have hs := sum_solSegs_eq b T
  have hnt : (tapSegs b.wT b.P b.t T).length ≤ H := by rw [length_tapSegs]; omega
  have hns : (solSegs b.wT b.P b.t T).length ≤ H := by rw [length_solSegs]; omega
  set X := (H + 1) ^ 3 with hX
  have hset : b.setup = X := rfl
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hHX : H + 1 ≤ X := by
    rw [hX]; calc H + 1 = (H + 1) ^ 1 := (pow_one _).symm
      _ ≤ (H + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hH2X : H * (H + 2) ≤ X := by rw [hX]; nlinarith
  have hpow : (H + 2) ^ 2 ≤ 4 * X := by rw [hX]; nlinarith
  set CX := C * X with hCX
  have f1 : fetchCost C H ≤ 4 * CX + 12 * X := by
    unfold fetchCost
    have := Nat.mul_le_mul_left (C + 3) hpow
    rw [hCX]; nlinarith
  have f2 : C * (bitLen b.d + 1) ≤ CX := Nat.mul_le_mul_left _ (by omega)
  have f3 : C * (bitLen (b.d - 1) + 1) ≤ CX := Nat.mul_le_mul_left _ (by omega)
  have f4 : ∀ n, n ≤ H → n * (C * (n + 1) + C + 3) ≤ CX + 3 * X := by
    intro n hn
    have e1 : n * (C * (n + 1) + C + 3) ≤ H * (C * (H + 1) + C + 3) :=
      Nat.mul_le_mul hn (by nlinarith)
    have e2 : H * (C * (H + 1) + C + 3) = C * (H * (H + 2)) + 3 * H := by ring
    have e3 : C * (H * (H + 2)) ≤ CX := Nat.mul_le_mul_left _ hH2X
    omega
  have g1 := f4 _ hnt
  have g2 := f4 _ hns
  have hC : C ≤ CX := by rw [hCX]; exact Nat.le_mul_of_pos_right _ hX1
  have h8 : bitLen 8 = 4 := by decide
  have key : dropCost C b T ≤ 11 * CX + 27 * X + 2 * tapTabLen b + 2 * solTabLen b := by
    unfold dropCost dropSegsCost
    rw [← hH, h8]
    omega
  have hfin : 11 * CX + 27 * X + 2 * tapTabLen b + 2 * solTabLen b ≤
      30 * (C + 10) * (tapTabLen b + solTabLen b + b.setup) := by
    rw [hset, hCX]
    nlinarith [Nat.zero_le (C * tapTabLen b), Nat.zero_le (C * solTabLen b)]
  exact le_trans key hfin

/-- **`DropTablesStmt` holds** (no hypotheses). -/
theorem dropTables_holds : DropTablesStmt := by
  obtain ⟨Mul, -, I, C, -, hI⟩ := exists_TB
  refine ⟨30 * (C + 10), fun _ => ⟨Fin 61, inferInstance, inferInstance, I.R,
    callInj tEmb (lensId I.R) (dropProg I), I.R_finite, I.R_nonempty,
    closed_callInj _ _ (dropProg_closed I), ?_⟩⟩
  intro b T rpar rtap rsol S hcl _ hpar htap hsol
  refine runs_host ?_ (hout_update2 S rtap rsol)
  rw [comp_tEmb_update2]
  exact (HT.dropProg_spec hI b T rpar rtap rsol (S ∘ tEmb) (kclean_host hcl) hpar htap hsol
    []).mono (dropCost_le C b T)

end SubNLogN.Machine.Tables
