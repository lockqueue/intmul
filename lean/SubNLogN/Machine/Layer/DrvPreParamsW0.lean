/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvCostKit
import SubNLogN.Machine.Layer.DrvArithBounds

/-!
# Layer driver, pre-phase parameters: the `w₀` kernel (`Machine/Layer/DrvPreParamsW0.lean`)

`w0N st` computes `w₀ = S·2^{K(D−1)+ρ}` (`drvW0`, `DrvParamsDefs.lean`). It reads `D, S, K, ρ` from
`st 0 … st 3` (restored) and pushes `natSyms w₀` onto `st 4`, on top of its old content. It uses
the floored work stacks `st 5 … st 8` (holding `D − 1`, `K(D−1)`, the exponent and `w₀`) and the
temporaries `st 9 … st 15`, all restored. `w0N2 st` is `w0N st` lifted to the long-division
register file (`lN`).

Results:
* `closed_w0N2`: the program is closed;
* `runs_w0N2`: its exact effect, with cost `w0Cost D S K ρ`;
* `w0Cost_le`: the cost is cubic in `bitLen D + bitLen S + bitLen K + K·D + ρ`.

The construction follows `runs_padRN` (`DrvArith.lean`), with interface matching
`DrvPreParams.lean`.

**Scope (honest summary).** Fully proved; no hypotheses beyond the stated ones.
-/

namespace SubNLogN.Machine.Layer.DrvPreParamsW0Aux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith

section W0

variable {K : Type}

/-- **`w₀ = S·2^{K(D−1)+ρ}`**: `D, S, K, ρ` on `st 0 … st 3` (restored) ↦ pushes `natSyms w₀` on
`st 4`; `st 5 … st 8` floored work stacks (`D − 1`, `K(D−1)`, the exponent, `w₀`), `st 9 … st 15`
temporaries. -/
def w0N (st : Fin 16 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (.seq (pushMark (st 5)) (.seq (copyN (st 0) (st 5) (st 9)) (decL (st 5) (st 9))))
  (.seq (.seq (pushMark (st 6)) (mulN (st 2) (st 5) (st 6) (st 9) (st 10) (st 11) (st 12)))
  (.seq (.seq (pushMark (st 7)) (addN (st 6) (st 3) (st 7) (st 9) (st 10) (st 11)))
  (.seq (.seq (pushMark (st 8)) (.seq (copyN (st 1) (st 8) (st 9))
      (powMulN (st 8) 2 (st 7) (st 9) (st 10) (st 11) (st 12) (st 13) (st 14) (st 15))))
  (.seq (copyN (st 8) (st 4) (st 9))
  (.seq (dropF (st 8)) (.seq (dropF (st 7)) (.seq (dropF (st 6)) (dropF (st 5)))))))))

/-- `w0N` on the long-division register file. -/
def w0N2 (st : Fin 16 → K) : Prog K (fun _ => Sym) Reg2 := (w0N st).liftRegs lN

/-- The cost of `w0N`. -/
def w0Cost (D Sv Kv ρ : ℕ) : ℕ :=
  (1 + ((7 * bitLen D + 7) + (6 * bitLen (D - 1 + 1) + 8))) + ((1 + mulCost Kv (D - 1)) +
  ((1 + 20 * (bitLen (Kv * (D - 1)) + bitLen ρ + 1)) +
  ((1 + ((7 * bitLen Sv + 7) + powCost 2 Sv (Kv * (D - 1) + ρ))) +
  ((7 * bitLen (Sv * 2 ^ (Kv * (D - 1) + ρ)) + 7) +
  ((2 * bitLen (Sv * 2 ^ (Kv * (D - 1) + ρ)) + 2) + ((2 * bitLen (Kv * (D - 1) + ρ) + 2) +
  ((2 * bitLen (Kv * (D - 1)) + 2) + (2 * bitLen (D - 1) + 2))))))))

theorem closed_w0N (st : Fin 16 → K) : (w0N st).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _)
    (WP.W9comp.closed_seq (closed_copyN _ _ _) (closed_decL _ _)))
  (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_mulN _ _ _ _ _ _ _))
  (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_addN _ _ _ _ _ _))
  (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
    (closed_copyN _ _ _) (closed_powMulN _ _ _ _ _ _ _ _ _ _)))
  (WP.W9comp.closed_seq (closed_copyN _ _ _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
    (WP.W9comp.closed_seq (closed_dropF _) (closed_dropF _))))))))

theorem closed_w0N2 (st : Fin 16 → K) : (w0N2 st).Closed :=
  WP.W9comp.closed_liftRegs lN (closed_w0N st)

end W0

section W0Spec

variable {K : Type} [DecidableEq K]

theorem runs_w0N {st : Fin 16 → K} (hst : Function.Injective st)
    (D Sv Kv ρ : ℕ) (hD1 : 1 ≤ D) (rD rS rK rρ : List Sym) (S : K → List Sym)
    (hrD : TermOK rD) (hrS : TermOK rS) (hrK : TermOK rK) (hrρ : TermOK rρ)
    (hD : S (st 0) = natSyms D ++ rD) (hS : S (st 1) = natSyms Sv ++ rS)
    (hK : S (st 2) = natSyms Kv ++ rK) (hρ : S (st 3) = natSyms ρ ++ rρ) :
    Runs (w0N st) S
      (Function.update S (st 4) (natSyms (Sv * 2 ^ (Kv * (D - 1) + ρ)) ++ S (st 4)))
      (fun _ => True) (w0Cost D Sv Kv ρ) := by
  have hnd : ∀ l : List (Fin 16), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (st 5) (D - 1) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ T, T = fl S1 (st 6) (Kv * (D - 1)) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ T, T = fl S2 (st 7) (Kv * (D - 1) + ρ) := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ T, T = fl S3 (st 8) (Sv * 2 ^ (Kv * (D - 1) + ρ)) := ⟨_, rfl⟩
  -- step 1: `D − 1`
  have r1 : Runs (.seq (pushMark (st 5)) (.seq (copyN (st 0) (st 5) (st 9)) (decL (st 5) (st 9))))
      S S1 (fun _ => True) (1 + ((7 * bitLen D + 7) + (6 * bitLen (D - 1 + 1) + 8))) := by
    rw [hS1]
    apply runs_fl
    have c1 := runs_copyN (src := st 0) (dst := st 5) (tmp := st 9) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) D rD
      (Function.update S (st 5) (Sym.mark :: S (st 5))) hrD
      (by rw [Function.update_of_ne (hst.ne (by decide)), hD])
    have c2 := runs_decL (k := st 5) (t := st 9) (hst.ne (by decide)) (D - 1)
      (Sym.mark :: S (st 5))
      (Function.update (Function.update S (st 5) (Sym.mark :: S (st 5))) (st 5)
        (natSyms D ++ Function.update S (st 5) (Sym.mark :: S (st 5)) (st 5)))
      (termOK_mark _)
      (by rw [Function.update_self, Function.update_self, Nat.sub_add_cancel hD1])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem]
  -- step 2: `K (D − 1)`
  have r2 : Runs (.seq (pushMark (st 6)) (mulN (st 2) (st 5) (st 6) (st 9) (st 10) (st 11)
      (st 12))) S1 S2 (fun _ => True) (1 + mulCost Kv (D - 1)) := by
    rw [hS2]
    apply runs_fl
    have c := runs_mulN (x := st 2) (y := st 5) (z := st 6) (A := st 9) (Bs := st 10)
      (Acc := st 11) (T := st 12) (hnd [2, 5, 6, 9, 10, 11, 12] (by decide)) Kv (D - 1)
      rK (Sym.mark :: S (st 5)) (Function.update S1 (st 6) (Sym.mark :: S1 (st 6)))
      hrK (termOK_mark _)
      (by simp +decide only [hS1, fl, Function.update_apply, hst.eq_iff, if_false]
          exact hK)
      (by simp +decide only [hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
    rw [Function.update_self] at c
    exact c
  -- step 3: the exponent `K (D − 1) + ρ`
  have r3 : Runs (.seq (pushMark (st 7)) (addN (st 6) (st 3) (st 7) (st 9) (st 10) (st 11)))
      S2 S3 (fun _ => True) (1 + 20 * (bitLen (Kv * (D - 1)) + bitLen ρ + 1)) := by
    rw [hS3]
    apply runs_fl
    have c := runs_addN (x := st 6) (y := st 3) (z := st 7) (t1 := st 9) (t2 := st 10)
      (t3 := st 11) (hnd [6, 3, 7, 9, 10, 11] (by decide)) (Kv * (D - 1)) ρ
      (Sym.mark :: S (st 6)) rρ (Function.update S2 (st 7) (Sym.mark :: S2 (st 7)))
      (termOK_mark _) hrρ
      (by simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
      (by simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_false]
          exact hρ)
    rw [Function.update_self] at c
    exact c
  -- step 4: `w₀ = S·2^{K(D−1)+ρ}`
  have r4 : Runs (.seq (pushMark (st 8)) (.seq (copyN (st 1) (st 8) (st 9))
      (powMulN (st 8) 2 (st 7) (st 9) (st 10) (st 11) (st 12) (st 13) (st 14) (st 15))))
      S3 S4 (fun _ => True) (1 + ((7 * bitLen Sv + 7) + powCost 2 Sv (Kv * (D - 1) + ρ))) := by
    rw [hS4]
    apply runs_fl
    have c1 := runs_copyN (src := st 1) (dst := st 8) (tmp := st 9) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) Sv rS
      (Function.update S3 (st 8) (Sym.mark :: S3 (st 8))) hrS
      (by simp +decide only [hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, 
            if_false]
          exact hS)
    have c2 := runs_powMulN (k := st 8) (ns := st 7) (Kc := st 9) (t := st 10) (Q := st 11)
      (Tdst := st 12) (A := st 13) (Bs := st 14) (Acc := st 15)
      (hnd [8, 7, 9, 10, 11, 12, 13, 14, 15] (by decide)) 2 (by norm_num) Sv (Kv * (D - 1) + ρ)
      (Sym.mark :: S3 (st 8)) (Sym.mark :: S (st 7))
      (Function.update (Function.update S3 (st 8) (Sym.mark :: S3 (st 8))) (st 8)
        (natSyms Sv ++ Function.update S3 (st 8) (Sym.mark :: S3 (st 8)) (st 8)))
      (termOK_mark _) (termOK_mark _)
      (by rw [Function.update_self, Function.update_self])
      (by simp +decide only [hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem]
  -- step 5: the output
  obtain ⟨E1, hE1⟩ : ∃ T, T = Function.update S4 (st 4)
      (natSyms (Sv * 2 ^ (Kv * (D - 1) + ρ)) ++ S (st 4)) := ⟨_, rfl⟩
  have b5 : Runs (copyN (st 8) (st 4) (st 9)) S4 E1 (fun _ => True)
      (7 * bitLen (Sv * 2 ^ (Kv * (D - 1) + ρ)) + 7) := by
    have c := runs_copyN (src := st 8) (dst := st 4) (tmp := st 9) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) (Sv * 2 ^ (Kv * (D - 1) + ρ))
      (Sym.mark :: S3 (st 8)) S4 (termOK_mark _) (by rw [hS4, fl_self])
    have e4 : S4 (st 4) = S (st 4) := by
      simp +decide only [hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, 
        if_false]
    rw [e4] at c
    rw [hE1]
    exact c
  -- the cleanup
  obtain ⟨E2, hE2⟩ : ∃ T, T = Function.update E1 (st 8) (S (st 8)) := ⟨_, rfl⟩
  obtain ⟨E3, hE3⟩ : ∃ T, T = Function.update E2 (st 7) (S (st 7)) := ⟨_, rfl⟩
  obtain ⟨E4, hE4⟩ : ∃ T, T = Function.update E3 (st 6) (S (st 6)) := ⟨_, rfl⟩
  obtain ⟨E5, hE5⟩ : ∃ T, T = Function.update E4 (st 5) (S (st 5)) := ⟨_, rfl⟩
  have d8 := runs_dropF (st 8) (Sv * 2 ^ (Kv * (D - 1) + ρ)) Sym.mark (S (st 8)) E1 rfl
    (by simp +decide only [hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff,
      if_true, if_false])
  have d7 := runs_dropF (st 7) (Kv * (D - 1) + ρ) Sym.mark (S (st 7)) E2 rfl
    (by simp +decide only [hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff,
      if_true, if_false])
  have d6 := runs_dropF (st 6) (Kv * (D - 1)) Sym.mark (S (st 6)) E3 rfl
    (by simp +decide only [hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false])
  have d5 := runs_dropF (st 5) (D - 1) Sym.mark (S (st 5)) E4 rfl
    (by simp +decide only [hE4, hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false])
  rw [← hE2] at d8
  rw [← hE3] at d7
  rw [← hE4] at d6
  rw [← hE5] at d5
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq b5 (WP.W9comp.runs_seq d8
    (WP.W9comp.runs_seq d7 (WP.W9comp.runs_seq d6 d5)))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) le_rfl
  funext k
  rcases eq_or_ne k (st 4) with rfl | h4
  · simp +decide only [hE5, hE4, hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 5) with rfl | h5
  · simp +decide only [hE5, hE4, hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 6) with rfl | h6
  · simp +decide only [hE5, hE4, hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 7) with rfl | h7
  · simp +decide only [hE5, hE4, hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 8) with rfl | h8
  · simp +decide only [hE5, hE4, hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply,
      hst.eq_iff, if_true, if_false]
  simp only [hE5, hE4, hE3, hE2, hE1, hS4, hS3, hS2, hS1, fl, Function.update_apply, h4, h5, h6,
    h7, h8, if_false]

/-- **The `w₀` kernel** (frozen statement): pushes `natSyms (S·2^{K(D−1)+ρ})` onto `st 4`. -/
theorem runs_w0N2 {st : Fin 16 → K} (hst : Function.Injective st)
    (D Sv Kv ρ : ℕ) (hD1 : 1 ≤ D) (rD rS rK rρ : List Sym) (S : K → List Sym)
    (hrD : TermOK rD) (hrS : TermOK rS) (hrK : TermOK rK) (hrρ : TermOK rρ)
    (hD : S (st 0) = natSyms D ++ rD) (hS : S (st 1) = natSyms Sv ++ rS)
    (hK : S (st 2) = natSyms Kv ++ rK) (hρ : S (st 3) = natSyms ρ ++ rρ) :
    Runs (w0N2 st) S
      (Function.update S (st 4) (natSyms (Sv * 2 ^ (Kv * (D - 1) + ρ)) ++ S (st 4)))
      (fun _ => True) (w0Cost D Sv Kv ρ) :=
  DrvParamsAux.runs_lN (runs_w0N hst D Sv Kv ρ hD1 rD rS rK rρ S hrD hrS hrK hrρ hD hS hK hρ)

end W0Spec

/-! ## The cost bound -/

theorem bitLen_pred_le (D : ℕ) : bitLen (D - 1) ≤ bitLen D := by
  apply bitLen_le_of_lt'
  have := lt_two_pow_bitLen D
  omega

theorem bitLen_pred_succ_le (D : ℕ) : bitLen (D - 1 + 1) ≤ bitLen D + 1 := by
  apply bitLen_le_of_lt'
  have := lt_two_pow_bitLen D
  rw [pow_succ]
  omega

/-- **The cost of the `w₀` kernel is cubic** in `bitLen D + bitLen S + bitLen K + K·D + ρ`
(frozen statement). -/
theorem w0Cost_le : ∃ c, ∀ D Sv Kv ρ,
    w0Cost D Sv Kv ρ ≤ c * (bitLen D + bitLen Sv + bitLen Kv + Kv * D + ρ + 1) ^ 3 := by
  refine ⟨100000, fun D Sv Kv ρ => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, X = bitLen D + bitLen Sv + bitLen Kv + Kv * D + ρ := ⟨_, rfl⟩
  rw [← hX]
  have hU : 1 ≤ X + 1 := by omega
  have hD1 := bitLen_pred_le D
  have hD2 := bitLen_pred_succ_le D
  have hmD : Kv * (D - 1) ≤ Kv * D := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hbm : bitLen (Kv * (D - 1)) ≤ X := le_trans (bitLen_le_self' _) (by omega)
  have hbn : bitLen (Kv * (D - 1) + ρ) ≤ X := le_trans (bitLen_le_self' _) (by omega)
  have hbw : bitLen (Sv * 2 ^ (Kv * (D - 1) + ρ)) ≤ X :=
    le_trans (bitLen_mul_two_pow_le _ _) (by omega)
  have hbρ : bitLen ρ ≤ X := le_trans (bitLen_le_self' _) (by omega)
  have hmul := DrvParamsAux.mulCost_le (a := Kv) (b := D - 1) (X := X) (by omega) (by omega)
  have hpow := DrvParamsAux.powCost_le (c := 2) (a := Sv) (n := Kv * (D - 1) + ρ) (X := X + 2)
    (by omega) (by omega) (by have := BoundsAux.bl_two_le; omega)
  have h3 : (X + 2 + 1) ^ 3 ≤ 27 * (X + 1) ^ 3 := by
    have h : X + 2 + 1 ≤ 3 * (X + 1) := by omega
    calc (X + 2 + 1) ^ 3 ≤ (3 * (X + 1)) ^ 3 := Nat.pow_le_pow_left h 3
      _ = 27 * (X + 1) ^ 3 := by ring
  have h2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right hU (by norm_num)
  have h1 : X + 1 ≤ (X + 1) ^ 3 := by
    have := Nat.pow_le_pow_right hU (show 1 ≤ 3 by norm_num)
    simpa using this
  unfold w0Cost
  omega

end SubNLogN.Machine.Layer.DrvPreParamsW0Aux
