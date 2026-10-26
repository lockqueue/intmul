/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolPow

/-!
# K6 (`Machine/Tables/SolEntry.lean`): one solver record

**Scope (honest summary).** The fragment `solEmit` (push the record `[(μ̂,0), (â,0), (γ̂,0)]` in the
format `recSyms ∘ crecBits wT` of `SubNLogN/Machine/Contracts/Records.lean` onto `solTab`) and
`solEntry` (one full solver entry of digit `u`: `solCoeffs2`, `solMuAh`, `solGam`, `solEmit`, then
the cleanup of all temporaries), with exact final state and the cost bound
`solEntryCost = 400·(C+1)(KM+1)U^5 + 24(C+7)(wT+1)`, uniform in `u`, where `U` bounds all bit widths
(Lemma 4.6 (`lem:bridge-C`) (bridge Lemma C)(iii) and Lemma B.3 (`lem:phase-tables`)). The
stored integers match `SolMath.lean`: `μ̂ = muN`, `â = ahN`, `γ̂ = gamN`.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt

/-! ## Width and budget facts -/

theorem bitLen_natAbs_le_of_fits {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (h : FitsTwos w z) :
    bitLen z.natAbs ≤ w := by
  have h1 : (z.natAbs : ℤ) ≤ 2 ^ (w - 1) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr ⟨h.1, h.2.le⟩
  have h2 : z.natAbs ≤ 2 ^ (w - 1) := by exact_mod_cast h1
  have := bitLen_le_of_le_two_pow h2
  omega

theorem fitsTwos_zero' (w : ℕ) : FitsTwos w 0 := by
  refine ⟨?_, by positivity⟩
  have : (0 : ℤ) ≤ 2 ^ (w - 1) := by positivity
  linarith

theorem emitCost_mono {C w zb : ℕ} (h : zb ≤ w) : emitCost C w zb ≤ emitCost C w w := by
  unfold emitCost
  have := Nat.mul_le_mul_left C (show zb + w + 3 ≤ w + w + 3 by omega)
  omega

theorem rhuDiv_nonneg {n d : ℤ} (hn : 0 ≤ n) (hd : 0 ≤ d) : 0 ≤ rhuDiv n d := by
  unfold rhuDiv
  rw [if_pos hd]
  exact Int.ediv_nonneg (by omega) (by omega)

/-- The generic per-entry budget `(C+1)(KM+1)U^5`. -/
def bud (C KM U : ℕ) : ℕ := (C + 1) * (KM + 1) * U ^ 5

theorem one_le_bud {C KM U : ℕ} (hU : 1 ≤ U) : 1 ≤ bud C KM U := by
  unfold bud
  have h1 : 1 ≤ U ^ 5 := Nat.one_le_pow _ _ hU
  have h2 : 1 ≤ (C + 1) * (KM + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 1 = 1 * 1 := rfl
    _ ≤ (C + 1) * (KM + 1) * U ^ 5 := Nat.mul_le_mul h2 h1

theorem C_pow_le_bud {C KM U j : ℕ} (hU : 1 ≤ U) (hj : j ≤ 5) : C * U ^ j ≤ bud C KM U := by
  unfold bud
  calc C * U ^ j ≤ (C + 1) * U ^ 5 :=
        Nat.mul_le_mul (Nat.le_succ C) (Nat.pow_le_pow_right hU hj)
    _ ≤ (C + 1) * (KM + 1) * U ^ 5 := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))

theorem CKM_pow_le_bud {C KM U j : ℕ} (hU : 1 ≤ U) (hj : j ≤ 5) :
    C * (KM * U ^ j) ≤ bud C KM U := by
  unfold bud
  calc C * (KM * U ^ j) ≤ (C + 1) * ((KM + 1) * U ^ 5) :=
        Nat.mul_le_mul (Nat.le_succ C) (Nat.mul_le_mul (Nat.le_succ KM)
          (Nat.pow_le_pow_right hU hj))
    _ = (C + 1) * (KM + 1) * U ^ 5 := by ring

theorem pow_le_bud {C KM U j : ℕ} (hU : 1 ≤ U) (hj : j ≤ 5) : U ^ j ≤ bud C KM U := by
  unfold bud
  calc U ^ j ≤ 1 * U ^ 5 := by rw [one_mul]; exact Nat.pow_le_pow_right hU hj
    _ ≤ (C + 1) * (KM + 1) * U ^ 5 :=
      Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr (by positivity)) le_rfl

theorem CU_le_bud {C KM U : ℕ} (hU : 1 ≤ U) : C * U ≤ bud C KM U := by
  have := C_pow_le_bud (C := C) (KM := KM) hU (j := 1) (by norm_num)
  rwa [pow_one] at this

theorem C_le_bud {C KM U : ℕ} (hU : 1 ≤ U) : C ≤ bud C KM U :=
  le_trans (by simpa using Nat.mul_le_mul_left C hU) (CU_le_bud (KM := KM) hU)

theorem U_le_bud {C KM U : ℕ} (hU : 1 ≤ U) : U ≤ bud C KM U := by
  have := pow_le_bud (C := C) (KM := KM) hU (j := 1) (by norm_num)
  rwa [pow_one] at this

/-! ## Component cost bounds -/

theorem coef_cost_le {C KM ω P t u U : ℕ} (hω : 1 ≤ ω) (hut : u < t)
    (hU : ω + coeffPrec P + bitLen (2 * t) + 4 ≤ U) :
    C * (bitLen u + 1) + (C * (bitLen u + bitLen u + 1) + (C * (bitLen u + 1) +
        (C * (bitLen (u + u) + 1) + (C * (bitLen (u + u) + 1) +
        (C * (ω + coeffPrec P + bitLen (2 * t) + 1) ^ 4 +
        ((C * (bitLen (u + u) + bitLen t + 1) +
          (2 * (C * (bitLen (c0Int ω P t u).natAbs + bitLen (c1Int ω P t u).natAbs + 2)) + 6 +
            1)) + (C * (bitLen (u + u + 1) + 1) + C * (bitLen (u + u) + 1)))))))) ≤
      22 * bud C KM U := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := c0c1_bounds ω (coeffPrec P) (2 * t) (2 * u + 1) (by omega)
    (by omega) (by omega)
  have hc0 : bitLen (c0Int ω P t u).natAbs ≤ coeffPrec P + 2 + 1 := bitLen_natAbs_le_of_le h1 h2
  have hc1 : bitLen (c1Int ω P t u).natAbs ≤ coeffPrec P + 2 + 1 := bitLen_natAbs_le_of_le h3 h4
  have b1 : bitLen u ≤ bitLen (2 * t) := bitLen_mono (by omega)
  have b2 : bitLen (u + u) ≤ bitLen (2 * t) := bitLen_mono (by omega)
  have b3 : bitLen (u + u + 1) ≤ bitLen (2 * t) := bitLen_mono (by omega)
  have b4 : bitLen t ≤ bitLen (2 * t) := bitLen_mono (by omega)
  have k1 : C * (bitLen u + 1) ≤ C * U := Nat.mul_le_mul_left C (by omega)
  have k2 : C * (bitLen u + bitLen u + 1) ≤ C * U + C * U := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left C (by omega)
  have k3 : C * (bitLen (u + u) + 1) ≤ C * U := Nat.mul_le_mul_left C (by omega)
  have k4 : C * (ω + coeffPrec P + bitLen (2 * t) + 1) ^ 4 ≤ C * U ^ 4 :=
    Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 4)
  have k5 : C * (bitLen (u + u) + bitLen t + 1) ≤ C * U + C * U := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left C (by omega)
  have k6 : C * (bitLen (c0Int ω P t u).natAbs + bitLen (c1Int ω P t u).natAbs + 2) ≤
      C * U + C * U := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left C (by omega)
  have k7 : C * (bitLen (u + u + 1) + 1) ≤ C * U := Nat.mul_le_mul_left C (by omega)
  have hU1 : 1 ≤ U := by omega
  have m1 : C * U ≤ bud C KM U := CU_le_bud hU1
  have m4 : C * U ^ 4 ≤ bud C KM U := C_pow_le_bud hU1 (by norm_num)
  have m0 : 1 ≤ bud C KM U := one_le_bud hU1
  omega

theorem muAh_cost_le {C KM ω P t u U : ℕ} {Mul : ℕ → ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (hω : 1 ≤ ω) (ht : Even t) (hut : u < t) (hU : coeffPrec P + (P + 2) + 6 ≤ U) :
    rdCost C (bitLen ((2 ^ (coeffPrec P + 2 + (P + 2)) : ℕ) : ℤ).natAbs)
        (bitLen (cmaxN ω P t u).natAbs) +
      ((C * Mul (bitLen (cminN ω P t u).natAbs + (P + 2) + 1) + C) +
      (rdCost C (bitLen (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ)).natAbs)
        (bitLen (cmaxN ω P t u).natAbs) +
      ((1 + (C * (bitLen (rhuDiv (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ))
        (cmaxN ω P t u)).natAbs + 1) + 1 + 1)) +
      (1 + C * (bitLen (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ)).natAbs + 1))))) ≤
      40 * bud C KM U := by
  obtain ⟨hc1, hc2, hc3⟩ := cmin_le_cmax (P := P) hω ht hut
  have e1 : bitLen ((2 ^ (coeffPrec P + 2 + (P + 2)) : ℕ) : ℤ).natAbs ≤
      coeffPrec P + (P + 2) + 4 := by
    rw [Int.natAbs_natCast, bitLen_two_pow]; omega
  have e2 : bitLen (cmaxN ω P t u).natAbs ≤ coeffPrec P + (P + 2) + 4 := by
    have := bitLen_natAbs_le_of_le (le_trans hc1 hc2) hc3; omega
  have e3 : bitLen (cminN ω P t u).natAbs ≤ coeffPrec P + 3 := by
    have := bitLen_natAbs_le_of_le hc1 (le_trans hc2 hc3); omega
  have hprod0 : 0 ≤ cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ) := by positivity
  have hprod : cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ) ≤ 2 ^ (coeffPrec P + 2 + (P + 2)) := by
    have hsplit : (2 : ℤ) ^ (coeffPrec P + 2 + (P + 2)) = 2 ^ (coeffPrec P + 2) * 2 ^ (P + 2) :=
      pow_add _ _ _
    rw [hsplit]; push_cast
    exact mul_le_mul_of_nonneg_right (le_trans hc2 hc3) (by positivity)
  have e4 : bitLen (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ)).natAbs ≤
      coeffPrec P + (P + 2) + 4 := by
    have := bitLen_natAbs_le_of_le hprod0 hprod; omega
  have hr0 : 0 ≤ rhuDiv (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ)) (cmaxN ω P t u) :=
    rhuDiv_nonneg hprod0 (le_trans hc1 hc2)
  have hr1 : rhuDiv (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ)) (cmaxN ω P t u) ≤ 2 ^ (P + 2) := by
    have := (ahN_bounds (P := P) hω ht hut).2
    unfold ahN at this
    push_cast
    exact le_trans (le_max_right _ _) this
  have e5 : bitLen (rhuDiv (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ))
      (cmaxN ω P t u)).natAbs ≤ coeffPrec P + (P + 2) + 4 := by
    have := bitLen_natAbs_le_of_le hr0 hr1; omega
  have r1 := rdCost_le (C := C) e1 e2
  have r2 := rdCost_le (C := C) e4 e2
  have mu1 : C * Mul (bitLen (cminN ω P t u).natAbs + (P + 2) + 1) ≤ C * (KM * U ^ 2) := by
    apply Nat.mul_le_mul_left
    exact le_trans (hMul _) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have k1 : C * (bitLen (rhuDiv (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ))
      (cmaxN ω P t u)).natAbs + 1) ≤ C * U := Nat.mul_le_mul_left C (by omega)
  have k2 : C * (bitLen (cminN ω P t u * ((2 ^ (P + 2) : ℕ) : ℤ)).natAbs + 1) ≤ C * U :=
    Nat.mul_le_mul_left C (by omega)
  have k3 : 4 * C * (coeffPrec P + (P + 2) + 4 + 2) ^ 2 ≤ 4 * (C * U ^ 2) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 2))
  have hU1 : 1 ≤ U := by omega
  have m1 : C * U ≤ bud C KM U := CU_le_bud hU1
  have m2 : C * U ^ 2 ≤ bud C KM U := C_pow_le_bud hU1 (by norm_num)
  have m3 : C * (KM * U ^ 2) ≤ bud C KM U := CKM_pow_le_bud hU1 (by norm_num)
  have m0 : 1 ≤ bud C KM U := one_le_bud hU1
  have m5 : C ≤ bud C KM U := C_le_bud hU1
  omega

theorem gam_cost_le {C KM A Q q U : ℕ} {Mul : ℕ → ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (hU : 2 * Q + q + 4 ≤ U) (hA : bitLen A + 1 ≤ U) :
    gamCost C (2 * Q + q + 2) A Q q Mul ≤ 200 * bud C KM U := by
  unfold gamCost stepCost
  have hU1 : 1 ≤ U := by omega
  have hbQ : bitLen Q ≤ Q := bitLen_le_self Q
  have hb1 : bitLen 1 ≤ 1 := bitLen_le_self 1
  have k1 : C * (Q + bitLen Q + 1) ≤ C * U := Nat.mul_le_mul_left C (by omega)
  have k2 : C * (bitLen A + 1) ≤ C * U := Nat.mul_le_mul_left C (by omega)
  have k3 : C * (2 * Q + q + 2 + (2 * Q + q + 2) + 1) ≤ C * U + C * U := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left C (by omega)
  have k4 : C * (2 * Q + q + 2 + 1) ≤ C * U := Nat.mul_le_mul_left C (by omega)
  have k5 : 4 * C * (2 * Q + q + 2 + 2) ^ 2 ≤ 4 * (C * U ^ 2) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 2))
  have k6 : C * Mul (2 * Q + q + 2) ≤ C * (KM * U ^ 2) :=
    Nat.mul_le_mul_left C (le_trans (hMul _) (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) 2)))
  have k7 : 12 * C * (2 * Q + q + 2 + 2) ≤ 12 * (C * U) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left C (by omega))
  have t1 : C * (KM * U ^ 2) ≤ (C + 1) * (KM + 1) * U ^ 2 := by
    calc C * (KM * U ^ 2) ≤ (C + 1) * ((KM + 1) * U ^ 2) :=
          Nat.mul_le_mul (Nat.le_succ C) (Nat.mul_le_mul (Nat.le_succ KM) le_rfl)
      _ = (C + 1) * (KM + 1) * U ^ 2 := by ring
  have hU2 : 1 ≤ U ^ 2 := Nat.one_le_pow _ _ hU1
  have hCK : 1 ≤ (C + 1) * (KM + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have t2 : C * U ≤ (C + 1) * (KM + 1) * U ^ 2 := by
    calc C * U ≤ (C + 1) * U ^ 2 :=
          Nat.mul_le_mul (Nat.le_succ C) (by nlinarith)
      _ ≤ (C + 1) * (KM + 1) * U ^ 2 := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have t4 : 1 ≤ (C + 1) * (KM + 1) * U ^ 2 := by
    calc 1 = 1 * 1 := rfl
      _ ≤ (C + 1) * (KM + 1) * U ^ 2 := Nat.mul_le_mul hCK hU2
  have t3 : C ≤ (C + 1) * (KM + 1) * U ^ 2 := le_trans (by simpa using Nat.mul_le_mul_left C hU1) t2
  have hS : 2 * (2 * (C * Mul (2 * Q + q + 2) + C) + 12 * C * (2 * Q + q + 2 + 2) + 30) + 3 ≤
      95 * ((C + 1) * (KM + 1) * U ^ 2) := by omega
  have hL : bitLen A * (2 * (2 * (C * Mul (2 * Q + q + 2) + C) + 12 * C * (2 * Q + q + 2 + 2) +
      30) + 3) ≤ 95 * bud C KM U := by
    calc _ ≤ U * (95 * ((C + 1) * (KM + 1) * U ^ 2)) := Nat.mul_le_mul (by omega) hS
      _ = 95 * ((C + 1) * (KM + 1) * U ^ 3) := by ring
      _ ≤ 95 * bud C KM U := by
        unfold bud
        exact Nat.mul_le_mul_left 95 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hU1 (by norm_num)))
  have m1 : C * U ≤ bud C KM U := CU_le_bud hU1
  have m2 : C * U ^ 2 ≤ bud C KM U := C_pow_le_bud hU1 (by norm_num)
  have m0 : 1 ≤ bud C KM U := one_le_bud hU1
  have mA : bitLen A ≤ bud C KM U := le_trans (by omega) (U_le_bud (C := C) (KM := KM) hU1)
  omega

theorem emit_cost_le (C wT : ℕ) : 6 * emitCost C wT wT + 1 ≤ 18 * ((C + 7) * (wT + 1)) := by
  unfold emitCost
  nlinarith [Nat.zero_le (C * wT)]

/-! ## Emitting the solver record -/

section Emit

variable (I : TB)

/-- Push the solver record `[(μ̂,0), (â,0), (γ̂,0)]` (`μ̂` on `x45`, `â` on `x47`, `γ̂` on `x54`)
onto `solTab`: the record end `sep` first, then the six fields bottom-up (temporaries `x55`,
`x56`). -/
def solEmit : TP I :=
  (tpush I sSol .sep).seq ((emitField I rZero rPW rPW1 x55 x56 sSol).seq
    ((emitField I x54 rPW rPW1 x55 x56 sSol).seq ((emitField I rZero rPW rPW1 x55 x56 sSol).seq
    ((emitField I x47 rPW rPW1 x55 x56 sSol).seq ((emitField I rZero rPW rPW1 x55 x56 sSol).seq
    (emitField I x45 rPW rPW1 x55 x56 sSol))))))

theorem solEmit_closed : (solEmit I).Closed :=
  ⟨trivial, ⟨emitField_closed I _ _ _ _ _ _, ⟨emitField_closed I _ _ _ _ _ _,
    ⟨emitField_closed I _ _ _ _ _ _, ⟨emitField_closed I _ _ _ _ _ _,
    ⟨emitField_closed I _ _ _ _ _ _, emitField_closed I _ _ _ _ _ _⟩⟩⟩⟩⟩⟩

end Emit

section EmitSpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.solEmit_spec (hI : I.Spec Mul C) (B : TL → List Sym) (w : ℕ) (mu ah gam : ℤ)
    (hw : 1 ≤ w) (hmu : FitsTwos w mu) (hah : FitsTwos w ah) (hgam : FitsTwos w gam)
    (h45 : B x45 = intSyms mu) (h47 : B x47 = intSyms ah) (h54 : B x54 = intSyms gam)
    (hZ : B rZero = intSyms 0) (hPW : B rPW = intSyms ((2 ^ w : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (w + 1) : ℕ) : ℤ)) (h55 : B x55 = []) (h56 : B x56 = [])
    (ρ : List (TP I)) :
    HT ρ B (solEmit I)
      (Function.update B sSol (recSyms (crecBits w [(mu, 0), (ah, 0), (gam, 0)]) ++ B sSol))
      (6 * emitCost C w w + 1) := by
  have hz0 := fitsTwos_zero' w
  refine (HT.seq (HT.tpush_spec sSol .sep B ρ)
    (HT.seq (HT.emitField_spec hI rZero rPW rPW1 x55 x56 sSol (by decide) _ w 0 [] [] [] hw hz0
      TermOK.nil TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hZ, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h55])
      (by simp (disch := decide) only [Function.update_of_ne, h56]) ρ)
    (HT.seq (HT.emitField_spec hI x54 rPW rPW1 x55 x56 sSol (by decide) _ w gam [] [] [] hw hgam
      TermOK.nil TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h54, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h55])
      (by simp (disch := decide) only [Function.update_of_ne, h56]) ρ)
    (HT.seq (HT.emitField_spec hI rZero rPW rPW1 x55 x56 sSol (by decide) _ w 0 [] [] [] hw hz0
      TermOK.nil TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hZ, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h55])
      (by simp (disch := decide) only [Function.update_of_ne, h56]) ρ)
    (HT.seq (HT.emitField_spec hI x47 rPW rPW1 x55 x56 sSol (by decide) _ w ah [] [] [] hw hah
      TermOK.nil TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h47, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h55])
      (by simp (disch := decide) only [Function.update_of_ne, h56]) ρ)
    (HT.seq (HT.emitField_spec hI rZero rPW rPW1 x55 x56 sSol (by decide) _ w 0 [] [] [] hw hz0
      TermOK.nil TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hZ, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h55])
      (by simp (disch := decide) only [Function.update_of_ne, h56]) ρ)
    (HT.emitField_spec hI x45 rPW rPW1 x55 x56 sSol (by decide) _ w mu [] [] [] hw hmu
      TermOK.nil TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h45, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h55])
      (by simp (disch := decide) only [Function.update_of_ne, h56]) ρ))))))).of_eq ?_ ?_
  · funext g
    by_cases hg : g = sSol
    · subst hg
      simp only [Function.update_self]
      simp [recSyms, crecBits, coefBits, List.map_append, List.append_assoc]
    · simp only [Function.update_of_ne hg]
  · have e0 := emitCost_mono (C := C) (bitLen_natAbs_le_of_fits hw hz0)
    have e1 := emitCost_mono (C := C) (bitLen_natAbs_le_of_fits hw hgam)
    have e2 := emitCost_mono (C := C) (bitLen_natAbs_le_of_fits hw hah)
    have e3 := emitCost_mono (C := C) (bitLen_natAbs_le_of_fits hw hmu)
    omega

end EmitSpec

/-! ## One solver entry -/

section Entry

variable (I : TB)

/-- One solver entry (digit `u` on `ru`): `x43, x44 := ĉ_max, ĉ_min`; `x45, x47 := μ̂, â`;
`x54 := γ̂`; push the record onto `solTab`; drop the five values. -/
def solEntry : TP I :=
  (solCoeffs2 I).seq ((solMuAh I).seq ((solGam I).seq ((solEmit I).seq
    ((intDrop I x54).seq ((intDrop I x47).seq ((intDrop I x45).seq
    ((intDrop I x43).seq (intDrop I x44))))))))

theorem solEntry_closed : (solEntry I).Closed :=
  ⟨solCoeffs2_closed I, ⟨solMuAh_closed I, ⟨solGam_closed I, ⟨solEmit_closed I,
    ⟨intDrop_closed I _, ⟨intDrop_closed I _, ⟨intDrop_closed I _, ⟨intDrop_closed I _,
      intDrop_closed I _⟩⟩⟩⟩⟩⟩⟩⟩

end Entry

/-- Cost bound of one solver entry: `400·(C+1)(KM+1)U^5` for the arithmetic (`U` bounds all bit
widths) plus `24(C+7)(wT+1)` for the emission and the cleanup of the `wT`-bit values. -/
def solEntryCost (C KM U wT : ℕ) : ℕ := 400 * bud C KM U + 24 * ((C + 7) * (wT + 1))

theorem drop_cost_fits {C w : ℕ} {z : ℤ} (hw : 1 ≤ w) (hz : FitsTwos w z) :
    1 + C * (bitLen z.natAbs + 1) ≤ 1 + C * (w + 1) := by
  have := Nat.mul_le_mul_left C (Nat.add_le_add_right (bitLen_natAbs_le_of_fits hw hz) 1)
  omega

theorem drop_cost_U {C U : ℕ} {z : ℤ} (h : bitLen z.natAbs + 1 ≤ U) :
    1 + C * (bitLen z.natAbs + 1) ≤ 1 + C * U := by
  have := Nat.mul_le_mul_left C h
  omega

section EntrySpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

/-- **One solver entry.** From the parameter stacks of axis `i` (`t = t_i`, `A = A_i`,
`Q = closurePrec (P+2) A t`) and the digit `u` on `ru`, push the solver record
`[(muN, 0), (ahN, 0), (gamN, 0)]` (`= solRec P (tabOf ω P t) i u`, `solRec_tabOf`) onto `solTab`;
all other stacks are restored. Hypotheses: `1 ≤ ω`, `t` even, `u < t`, `1 ≤ wT`, the three
stored values fit `wT` bits, `U` bounds the bit widths (`hU1 … hU4`), `Mul w ≤ KM (w+1)^2`. -/
theorem HT.solEntry_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (ω P t A u wT U : ℕ)
    (hω : 1 ≤ ω) (ht : Even t) (hut : u < t) (hw : 1 ≤ wT)
    (hU1 : ω + coeffPrec P + bitLen (2 * t) + 4 ≤ U) (hU2 : coeffPrec P + (P + 2) + 6 ≤ U)
    (hU3 : 2 * closurePrec (P + 2) A t + (P + 2) + 4 ≤ U) (hU4 : bitLen A + 1 ≤ U)
    (hfit : FitsTwos wT (muN ω P t u) ∧ FitsTwos wT (ahN ω P t u) ∧
      FitsTwos wT (gamN ω P t A u))
    (hu : B ru = natSyms u) (hW : B rW = natSyms ω) (hPC : B rPC = natSyms (coeffPrec P))
    (h2t : B r2t = natSyms (2 * t)) (hT : B rT = natSyms t)
    (hNmu : B rNmu = intSyms ((2 ^ (coeffPrec P + 2 + (P + 2)) : ℕ) : ℤ))
    (hPq : B rPq = intSyms ((2 ^ (P + 2) : ℕ) : ℤ)) (hA : B rA = natSyms A)
    (hQ : B rQ = natSyms (closurePrec (P + 2) A t)) (hq : B rq = natSyms (P + 2))
    (hPQ : B rPQ = intSyms ((2 ^ closurePrec (P + 2) A t : ℕ) : ℤ))
    (hPQq : B rPQq = intSyms ((2 ^ (closurePrec (P + 2) A t + (P + 2)) : ℕ) : ℤ))
    (hZ : B rZero = intSyms 0) (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ B (solEntry I)
      (Function.update B sSol (recSyms (crecBits wT [(muN ω P t u, 0), (ahN ω P t u, 0),
        (gamN ω P t A u, 0)]) ++ B sSol))
      (solEntryCost C KM U wT) := by
  have h40 : B x40 = [] := htmp 40 (by decide)
  have h41 : B x41 = [] := htmp 41 (by decide)
  have h42 : B x42 = [] := htmp 42 (by decide)
  have h43 : B x43 = [] := htmp 43 (by decide)
  have h44 : B x44 = [] := htmp 44 (by decide)
  have h45 : B x45 = [] := htmp 45 (by decide)
  have h46 : B x46 = [] := htmp 46 (by decide)
  have h47 : B x47 = [] := htmp 47 (by decide)
  have h48 : B x48 = [] := htmp 48 (by decide)
  have h49 : B x49 = [] := htmp 49 (by decide)
  have h50 : B x50 = [] := htmp 50 (by decide)
  have h51 : B x51 = [] := htmp 51 (by decide)
  have h52 : B x52 = [] := htmp 52 (by decide)
  have h53 : B x53 = [] := htmp 53 (by decide)
  have h54 : B x54 = [] := htmp 54 (by decide)
  have h55 : B x55 = [] := htmp 55 (by decide)
  have h56 : B x56 = [] := htmp 56 (by decide)
  have h57 : B x57 = [] := htmp 57 (by decide)
  have h58 : B x58 = [] := htmp 58 (by decide)
  have hU0 : 1 ≤ U := by omega
  have hah := ahN_bounds (P := P) hω ht hut
  obtain ⟨cm0, cm1, cm2⟩ := cmin_le_cmax (P := P) hω ht hut
  have hbmax : bitLen (cmaxN ω P t u).natAbs + 1 ≤ U := by
    have := bitLen_natAbs_le_of_le (le_trans cm0 cm1) cm2; unfold coeffPrec at *; omega
  have hbmin : bitLen (cminN ω P t u).natAbs + 1 ≤ U := by
    have := bitLen_natAbs_le_of_le cm0 (le_trans cm1 cm2); unfold coeffPrec at *; omega
  obtain ⟨Q, hQdef⟩ : ∃ Q, closurePrec (P + 2) A t = Q := ⟨_, rfl⟩
  rw [hQdef] at hQ hPQ hPQq hU3
  obtain ⟨aN, haN⟩ : ∃ a : ℕ, (a : ℤ) = ahN ω P t u := ⟨_, Int.toNat_of_nonneg hah.1⟩
  have haN2 : aN ≤ 2 ^ (P + 2) := by
    have h := hah.2
    rw [← haN] at h
    exact_mod_cast h
  have hg : rhuDiv (2 ^ (Q + (P + 2))) (2 ^ Q - powTruncInt Q (P + 2) (aN : ℤ) A) =
      gamN ω P t A u := by
    unfold gamN closureFixedInt
    rw [hQdef, haN]
  have hfg : FitsTwos wT (rhuDiv (2 ^ (Q + (P + 2))) (2 ^ Q - powTruncInt Q (P + 2) (aN : ℤ) A)) := by
    rw [hg]; exact hfit.2.2
  refine (HT.seq ((HT.solCoeffs2_spec hI B ω P t u hω hut hu hW hPC h2t hT h40 h41 h42 h43 h44
      ρ).mono (coef_cost_le (KM := KM) hω hut hU1))
    (HT.seq ((HT.solMuAh_spec hI _ (cmaxN ω P t u) (cminN ω P t u) (coeffPrec P) (P + 2)
      (by simp (disch := decide) only [Function.update_of_ne, hNmu])
      (by simp (disch := decide) only [Function.update_of_ne, hPq])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, h45])
      (by simp (disch := decide) only [Function.update_of_ne, h46])
      (by simp (disch := decide) only [Function.update_of_ne, h47])
      (by simp (disch := decide) only [Function.update_of_ne, h57])
      (by simp (disch := decide) only [Function.update_of_ne, h58]) ρ).mono
      (muAh_cost_le (KM := KM) hMul hω ht hut hU2))
    (HT.seq ((HT.solGam_spec hI _ aN A Q (P + 2) haN2
      (by simp (disch := decide) only [Function.update_self]; rw [haN]; rfl)
      (by simp (disch := decide) only [Function.update_of_ne, hA])
      (by simp (disch := decide) only [Function.update_of_ne, hQ])
      (by simp (disch := decide) only [Function.update_of_ne, hq])
      (by simp (disch := decide) only [Function.update_of_ne, hPQ])
      (by simp (disch := decide) only [Function.update_of_ne, hPQq])
      (by simp (disch := decide) only [Function.update_of_ne, h48])
      (by simp (disch := decide) only [Function.update_of_ne, h49])
      (by simp (disch := decide) only [Function.update_of_ne, h50])
      (by simp (disch := decide) only [Function.update_of_ne, h51])
      (by simp (disch := decide) only [Function.update_of_ne, h52])
      (by simp (disch := decide) only [Function.update_of_ne, h53])
      (by simp (disch := decide) only [Function.update_of_ne, h54])
      (by simp (disch := decide) only [Function.update_of_ne, h57])
      (by simp (disch := decide) only [Function.update_of_ne, h58]) ρ).mono
      (gam_cost_le (KM := KM) hMul hU3 hU4))
    (HT.seq ((HT.solEmit_spec hI _ wT (muN ω P t u) (ahN ω P t u)
      (rhuDiv (2 ^ (Q + (P + 2))) (2 ^ Q - powTruncInt Q (P + 2) (aN : ℤ) A)) hw hfit.1
      hfit.2.1 hfg
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self] <;> rfl)
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self] <;> rfl)
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, hZ])
      (by simp (disch := decide) only [Function.update_of_ne, hPW])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1])
      (by simp (disch := decide) only [Function.update_of_ne, h55])
      (by simp (disch := decide) only [Function.update_of_ne, h56]) ρ).mono
      (emit_cost_le C wT))
    (HT.seq ((HT.intDrop_spec hI x54 _
      (rhuDiv (2 ^ (Q + (P + 2))) (2 ^ Q - powTruncInt Q (P + 2) (aN : ℤ) A)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (drop_cost_fits hw hfg))
    (HT.seq ((HT.intDrop_spec hI x47 _ (ahN ω P t u) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil] <;> rfl) ρ).mono (drop_cost_fits hw hfit.2.1))
    (HT.seq ((HT.intDrop_spec hI x45 _ (muN ω P t u) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil] <;> rfl) ρ).mono (drop_cost_fits hw hfit.1))
    (HT.seq ((HT.intDrop_spec hI x43 _ (cmaxN ω P t u) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (drop_cost_U hbmax))
      ((HT.intDrop_spec hI x44 _ (cminN ω P t u) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (drop_cost_U hbmin)))))))))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = sSol
    · subst g1
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      rw [hg]
    by_cases g2 : g = x43
    · subst g2; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h43]
    by_cases g3 : g = x44
    · subst g3; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h44]
    by_cases g4 : g = x45
    · subst g4; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h45]
    by_cases g5 : g = x47
    · subst g5; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47]
    by_cases g6 : g = x54
    · subst g6; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h54]
    simp only [Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
      Function.update_of_ne g4, Function.update_of_ne g5, Function.update_of_ne g6]
  · unfold solEntryCost
    have m1 : C * U ≤ bud C KM U := CU_le_bud hU0
    have m0 : 1 ≤ bud C KM U := one_le_bud hU0
    have f1 : C * (wT + 1) ≤ (C + 7) * (wT + 1) := Nat.mul_le_mul_right _ (by omega)
    have f2 : 1 ≤ (C + 7) * (wT + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega

end EntrySpec

end SubNLogN.Machine.Tables
