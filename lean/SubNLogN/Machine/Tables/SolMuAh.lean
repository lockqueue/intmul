/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolCoef

/-!
# K6 (`Machine/Tables/SolMuAh.lean`): solver entries, part 2 — `μ̂` and `â`

**Scope (honest summary).** Value bounds for the W7 `c0c1` outputs (from
`IntMul.computableC0C1Core_spec`: `0 ≤ c_j ≤ 2^(pC+2)`, and for even `t` the orientation gives
`ĉ_min ≤ ĉ_max`), the resulting bound `0 ≤ â ≤ 2^q`, and the fragment `solMuAh`
(`x45 := intSyms μ̂`, `x47 := intSyms â` from `x43 = ĉ_max`, `x44 = ĉ_min`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt

/-! ## Value bounds -/

theorem c0c1_bounds (ω pC r u2 : ℕ) (hω : 0 < ω) (hr : 0 < r) (hu2 : u2 < r) :
    0 ≤ (IntMul.computableC0C1WithProgramCost ω pC r u2).1.1.1 ∧
    (IntMul.computableC0C1WithProgramCost ω pC r u2).1.1.1 ≤ (2 : ℤ) ^ (pC + 2) ∧
    0 ≤ (IntMul.computableC0C1WithProgramCost ω pC r u2).1.2.1 ∧
    (IntMul.computableC0C1WithProgramCost ω pC r u2).1.2.1 ≤ (2 : ℤ) ^ (pC + 2) ∧
    (2 * u2 < r → (IntMul.computableC0C1WithProgramCost ω pC r u2).1.2.1 ≤
      (IntMul.computableC0C1WithProgramCost ω pC r u2).1.1.1) ∧
    (r < 2 * u2 → (IntMul.computableC0C1WithProgramCost ω pC r u2).1.1.1 ≤
      (IntMul.computableC0C1WithProgramCost ω pC r u2).1.2.1) := by
  have h := IntMul.computableC0C1Core_spec ω pC (pC + 2) (pC + 2 + 2) (8 * ω + 1) (32 * ω + 1)
    ((pC + 2 + 2) + 2 * (8 * ω + 1) + 6) (4 * (32 * ω + 1) + (pC + 2 + 2) + (8 * ω + 1) + 4)
    ((pC + 2 + 2) + 2 * (4 * (32 * ω + 1) + (pC + 2 + 2) + (8 * ω + 1) + 4) +
      2 * ((32 * ω + 1) + (8 * ω + 1)) + 6)
    (((pC + 2 + 2) + 2 * (4 * (32 * ω + 1) + (pC + 2 + 2) + (8 * ω + 1) + 4) +
      2 * ((32 * ω + 1) + (8 * ω + 1)) + 6) + 4 * (4 * (32 * ω + 1) + (pC + 2 + 2) +
      (8 * ω + 1) + 4) + 2 * ((32 * ω + 1) + (8 * ω + 1)) +
      2 * ((pC + 2 + 2) + 2 * (8 * ω + 1) + 6) + (pC + 2 + 2) + 2 * ω + 2 * Nat.log2 r + 40)
    r u2 rfl rfl rfl rfl le_rfl le_rfl (by omega) hω hr hu2
  obtain ⟨-, -, h1, h2, h3, h4, -, -, h5, -, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- For even `t`, `2u < t ↔ 2(2u+1) < 2t`. -/
theorem two_u_lt_iff {t u : ℕ} (ht : Even t) : 2 * u < t ↔ 2 * (2 * u + 1) < 2 * t := by
  obtain ⟨k, rfl⟩ := ht
  omega

theorem cmin_le_cmax {ω P t u : ℕ} (hω : 1 ≤ ω) (ht : Even t) (hut : u < t) :
    0 ≤ cminN ω P t u ∧ cminN ω P t u ≤ cmaxN ω P t u ∧
      cmaxN ω P t u ≤ (2 : ℤ) ^ (coeffPrec P + 2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := c0c1_bounds ω (coeffPrec P) (2 * t) (2 * u + 1) (by omega)
    (by omega) (by omega)
  unfold cminN cmaxN c0Int c1Int
  by_cases h : 2 * u < t
  · rw [if_pos h, if_pos h]
    exact ⟨h3, h5 ((two_u_lt_iff ht).mp h), h2⟩
  · rw [if_neg h, if_neg h]
    have : 2 * t < 2 * (2 * u + 1) := by
      obtain ⟨k, rfl⟩ := ht
      omega
    exact ⟨h1, h6 this, h4⟩

theorem ahN_bounds {ω P t u : ℕ} (hω : 1 ≤ ω) (ht : Even t) (hut : u < t) :
    0 ≤ ahN ω P t u ∧ ahN ω P t u ≤ (2 : ℤ) ^ (P + 2) := by
  obtain ⟨h1, h2, -⟩ := cmin_le_cmax (P := P) hω ht hut
  refine ⟨le_max_left _ _, max_le (by positivity) ?_⟩
  unfold rhuDiv
  set c := cmaxN ω P t u
  rcases lt_or_eq_of_le (le_trans h1 h2 : (0 : ℤ) ≤ c) with hc | hc
  · rw [if_pos hc.le]
    refine Int.lt_add_one_iff.mp (Int.ediv_lt_of_lt_mul (by omega) ?_)
    nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℤ) ≤ 2 ^ (P + 2))]
  · rw [if_pos hc.le, ← hc]
    simp

theorem bitLen_natAbs_le_of_le {z : ℤ} {k : ℕ} (h0 : 0 ≤ z) (h : z ≤ (2 : ℤ) ^ k) :
    bitLen z.natAbs ≤ k + 1 := by
  apply bitLen_le_of_lt
  have : (z.natAbs : ℤ) ≤ 2 ^ k := by rw [Int.natAbs_of_nonneg h0]; exact h
  have h2 : z.natAbs ≤ 2 ^ k := by exact_mod_cast this
  calc z.natAbs ≤ 2 ^ k := h2
    _ < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem rdCost_le {C nb db Wd : ℕ} (h1 : nb ≤ Wd) (h2 : db ≤ Wd) :
    rdCost C nb db ≤ 4 * C * (Wd + 2) ^ 2 + 10 := by
  unfold rdCost
  have : nb * db ≤ Wd * Wd := Nat.mul_le_mul h1 h2
  nlinarith

/-! ## Part 2: `μ̂` and `â` -/

/-- `x45 := intSyms μ̂`, `x47 := intSyms â` (temporaries `x46`, `x57`, `x58`). -/
def solMuAh (I : TB) : TP I :=
  (rhuDivProg I rNmu x43 x45 x57 x58).seq ((tmu I x44 rPq x46).seq
    ((rhuDivProg I x46 x43 x47 x57 x58).seq ((maxZero I x47).seq (intDrop I x46))))

theorem solMuAh_closed (I : TB) : (solMuAh I).Closed :=
  ⟨rhuDivProg_closed I _ _ _ _ _, ⟨callI_closed _ _ _ _, ⟨rhuDivProg_closed I _ _ _ _ _,
    ⟨maxZero_closed I _, intDrop_closed I _⟩⟩⟩⟩

section MuAh

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.solMuAh_spec (hI : I.Spec Mul C) (B : TL → List Sym) (cmax cmin : ℤ)
    (pC q : ℕ) (hNmu : B rNmu = intSyms ((2 ^ (pC + 2 + q) : ℕ) : ℤ))
    (hPq : B rPq = intSyms ((2 ^ q : ℕ) : ℤ)) (h43 : B x43 = intSyms cmax)
    (h44 : B x44 = intSyms cmin) (h45 : B x45 = []) (h46 : B x46 = []) (h47 : B x47 = [])
    (h57 : B x57 = []) (h58 : B x58 = []) (ρ : List (TP I)) :
    HT ρ B (solMuAh I)
      (Function.update (Function.update B x45
        (intSyms (rhuDiv (2 ^ (pC + 2 + q)) cmax))) x47
        (intSyms (max 0 (rhuDiv (cmin * 2 ^ q) cmax))))
      (rdCost C (bitLen ((2 ^ (pC + 2 + q) : ℕ) : ℤ).natAbs) (bitLen cmax.natAbs) +
        ((C * Mul (bitLen cmin.natAbs + q + 1) + C) +
        (rdCost C (bitLen (cmin * ((2 ^ q : ℕ) : ℤ)).natAbs) (bitLen cmax.natAbs) +
        ((1 + (C * (bitLen (rhuDiv (cmin * ((2 ^ q : ℕ) : ℤ)) cmax).natAbs + 1) + 1 + 1)) +
        (1 + C * (bitLen (cmin * ((2 ^ q : ℕ) : ℤ)).natAbs + 1)))))) := by
  have hq : bitLen (((2 ^ q : ℕ) : ℤ)).natAbs ≤ bitLen cmin.natAbs + q + 1 := by
    rw [Int.natAbs_natCast, bitLen_two_pow]; omega
  refine (HT.seq (HT.rhuDivProg_spec hI rNmu x43 x45 x57 x58 (by decide) B _ cmax [] []
      TermOK.nil TermOK.nil (by rw [hNmu, List.append_nil]) (by rw [h43, List.append_nil]) h57 h58
      ρ)
    (HT.seq (HT.tmu_spec hI x44 rPq x46 (by decide) _ (bitLen cmin.natAbs + q + 1) cmin _ [] []
      (by omega) hq TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h44, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPq, List.append_nil]) ρ)
    (HT.seq (HT.rhuDivProg_spec hI x46 x43 x47 x57 x58 (by decide) _ (cmin * ((2 ^ q : ℕ) : ℤ))
      cmax [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h43, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h57])
      (by simp (disch := decide) only [Function.update_of_ne, h58]) ρ)
    (HT.seq (HT.maxZero_spec hI x47 _ _ [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47,
        List.append_nil]) ρ)
      (HT.intDrop_spec hI x46 _ (cmin * ((2 ^ q : ℕ) : ℤ)) [] TermOK.nil
        (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46,
          List.append_nil]) ρ))))).of_eq ?_ le_rfl
  push_cast
  simp (disch := first | decide | simp (config := { failIfUnchanged := false }) (disch := decide)
    only [ValEq.eq_1, Function.update_self, Function.update_of_ne, h45, h46, h47]) only [tupd_swap,
    Function.update_idem, tupd_eq_self_of, Function.update_self, Function.update_of_ne, h45, h46,
    h47, List.append_nil]

end MuAh

end SubNLogN.Machine.Tables
