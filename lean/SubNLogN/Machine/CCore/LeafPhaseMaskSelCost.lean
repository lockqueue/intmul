/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelCostDefs
import IntMulTM.SpecFacts
import Mathlib.Tactic.Linarith

/-!
# C-core phase leaf, record-wise sign selection: the cost bound, proved

**Theorem** (fully proved): `maskSelCost_holds : PhaseMaskAux.MaskSelCostStmt`
(`Machine/CCore/LeafPhaseMaskSelCostDefs.lean`), with the constant `C = 1000`.

Route: from `1 ≤ k` and `j0 + m^k ≤ D` (`m = mn = 10^6`): `m·m^{k-1} = m^k ≤ D`, hence `m ≤ D`,
`m^{k-1} ≤ D`, `k < 2^k ≤ m^k ≤ D`, `j0 ≤ D`, `1 ≤ D`; from `ρ < K`: `1 ≤ K`. Every product in
`cost0` is bounded by a quadratic form in `K, D`, and `K·D ≤ 2^{KD}`, `D² ≤ 4·2^D ≤ 4·2^{KD}`,
`K² ≤ 4·2^K ≤ 4·2^{KD}` (`n² ≤ 4·2^n`). The total is then linear in
`Vv, Vn, 2^{KD}, S, D, 1` with coefficients `≤ 500`.
-/

namespace SubNLogN.Machine.CCore.MaskSelCostAux

open TMFw TMFw.Contracts Computability SubNLogN.Machine.CCore.PhaseMaskAux

theorem sq_le_four_two_pow : ∀ n : ℕ, n * n ≤ 4 * 2 ^ n
  | 0 => by norm_num
  | n + 1 => by
    have ih := sq_le_four_two_pow n
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    rw [pow_succ]
    nlinarith

theorem bitLen_le_self_ms (n : ℕ) : bitLen n ≤ n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem two_le_mn : 2 ≤ mn := by
  show 2 ≤ tripleM 100
  unfold tripleM
  norm_num

/-- **The cost of the `MaskSelStmt` kernel is within its budget** (`C = 1000`). -/
theorem maskSelCost_holds : MaskSelCostStmt := by
  refine ⟨1000, fun K D S j0 k ρ Vv Vn N Vo a b c d hk hρ hj hS hN hVo ha hb hc hd => ?_⟩
  have hm2 := two_le_mn
  have hK : 1 ≤ K := by omega
  -- `m · m^{k-1} = m^k ≤ D`
  have hpow : mn * mn ^ (k - 1) = mn ^ k := by
    have h : mn ^ (k - 1 + 1) = mn ^ (k - 1) * mn := Nat.pow_succ mn (k - 1)
    rw [Nat.sub_add_cancel hk] at h
    rw [h, Nat.mul_comm]
  have hP1 : 1 ≤ mn ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hmP : mn * mn ^ (k - 1) ≤ D := by rw [hpow]; omega
  have hmn : mn ≤ D := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hmP
  have hPD : mn ^ (k - 1) ≤ D := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hmP
  have hkD : k ≤ D := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ mn ^ k := Nat.pow_le_pow_left hm2 k
    omega
  have hj0 : j0 ≤ D := by omega
  have hD : 1 ≤ D := by omega
  -- the budget `T = 2^{KD}`
  have hKD : K * D ≤ 2 ^ (K * D) := Nat.lt_two_pow_self.le
  have hDKD : D ≤ K * D := Nat.le_mul_of_pos_left _ (by omega)
  have hKKD : K ≤ K * D := Nat.le_mul_of_pos_right _ (by omega)
  have hD2 : D * D ≤ 4 * 2 ^ (K * D) :=
    le_trans (sq_le_four_two_pow D) (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) hDKD))
  have hK2 : K * K ≤ 4 * 2 ^ (K * D) :=
    le_trans (sq_le_four_two_pow K) (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) hKKD))
  have hbS := bitLen_le_self_ms S
  -- the products of `cost0`
  have hρm : ρ * (8 * K + 10 + 8 * ρ + 13) ≤ K * (16 * K + 23) :=
    Nat.mul_le_mul hρ.le (by omega)
  have hkm : (k - 1) * (8 * mn ^ (k - 1) + 6 + 8 * (k - 1) + 13) ≤ D * (16 * D + 19) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hjm : j0 * (8 * D + 30 * K + 40 + 8 * j0 + 13) ≤ D * (16 * D + 30 * K + 53) :=
    Nat.mul_le_mul hj0 (by omega)
  have hmm : mn * (mn ^ (k - 1) * (8 * D + 30 * K + 44) + 3 * mn ^ (k - 1) + 6 + 4) ≤
      D * (8 * D + 30 * K + 44) + 3 * D + 10 * D := by
    calc mn * (mn ^ (k - 1) * (8 * D + 30 * K + 44) + 3 * mn ^ (k - 1) + 6 + 4)
        = (mn * mn ^ (k - 1)) * (8 * D + 30 * K + 44) + 3 * (mn * mn ^ (k - 1)) + 10 * mn := by
          ring
      _ ≤ D * (8 * D + 30 * K + 44) + 3 * D + 10 * D :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hmP) (Nat.mul_le_mul_left 3 hmP))
            (Nat.mul_le_mul_left 10 hmn)
  unfold cost0
  nlinarith

end SubNLogN.Machine.CCore.MaskSelCostAux
