/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvArith

/-!
# Layer driver: cost bounds of the shared parameter arithmetic (`Machine/Layer/DrvArithBounds.lean`)

**Scope (honest summary).** Pure arithmetic; no machine programs; all proved (no `sorry`).
Polynomial bounds for the explicit costs of the parameter programs `q0N` and `padRN`
(`Machine/Layer/DrvArith.lean`), used by the cost clauses of the layer driver's parameter kernels
(`DrvPreParamsStmt`, `DrvPostParamsStmt`, `Machine/Layer/DrvParamsDefs.lean`) and of the piece
descriptors (`DrvDescStmt`):
* `q0Of_le`: `q₀ = ⌈lg W_c⌉·⌈log_m 2d⌉ ≤ ⌈lg W_c⌉·(bitLen d + 1)`;
* `q0Cost_le`: `∃ c, ∀ d, q0Cost d ≤ c·(bitLen d + 1)^3`;
* `padRCost_le`: `∃ c, ∀ d K, padRCost d K ≤ c·(bitLen d + q0Of d·K + bitLen K + 1)^3`.
The constants are explicit closed expressions in `bitLen m_H`, `⌈lg W_c⌉`, `bitLen W_c` (and the
constant of `q0Cost_le`); they are never evaluated: the proofs go through the generic forms
`BoundsAux.q0Cost_gen`, `BoundsAux.padRCost_gen`, stated for variables `W`, `m`, `L`, `q`, `Q` in
place of `W_c`, `m_H`, `⌈lg W_c⌉`, `q0Of d`, `q0Cost d`, and instantiated by syntactic matching
(avoiding kernel unfolding of the large network constant `W_c`).
-/

namespace SubNLogN.Machine.Layer.DrvArith

open TMFw TMFw.Contracts SubNLogN.Machine.NatArith

namespace BoundsAux

theorem bl_one_le : bitLen 1 ≤ 1 := bitLen_le_of_lt' (by norm_num)

theorem bl_two_le : bitLen 2 ≤ 2 := bitLen_le_of_lt' (by norm_num)

theorem bl_two_pow_le (n : ℕ) : bitLen (2 ^ n) ≤ n + 1 := by
  apply bitLen_le_of_lt'
  have h := Nat.one_le_two_pow (n := n)
  rw [pow_succ]
  omega

theorem bl_pow_le (a : ℕ) : ∀ n : ℕ, bitLen (a ^ n) ≤ n * bitLen a + 1
  | 0 => by simpa using bl_one_le
  | n + 1 => by
    have ih := bl_pow_le a n
    rw [pow_succ, Nat.succ_mul]
    have := bitLen_mul_le' (a ^ n) a
    omega

theorem bl_two_mul_le (d : ℕ) : bitLen (d + d) ≤ bitLen d + 1 := by
  apply bitLen_le_of_lt'
  have h := lt_two_pow_bitLen d
  rw [pow_succ]
  omega

theorem le_cube {U : ℕ} (hU : 1 ≤ U) : U ≤ U ^ 3 := by
  calc U = U ^ 1 := (pow_one U).symm
    _ ≤ U ^ 3 := Nat.pow_le_pow_right hU (by norm_num)

theorem sq_le_cube {U : ℕ} (hU : 1 ≤ U) : U * U ≤ U ^ 3 := by
  calc U * U = U ^ 2 := (sq U).symm
    _ ≤ U ^ 3 := Nat.pow_le_pow_right hU (by norm_num)

/-- **Generic form of `q0Cost_le`** (variables `L`, `m` for `⌈lg W_c⌉`, `m_H`). -/
theorem q0Cost_gen (L m : ℕ) (hm : 1 < m) (d : ℕ) :
    (1 + ((7 * bitLen d + 7) + 3)) + ((1 + clogCost m (d + d)) + ((2 * bitLen (d + d) + 2) +
      (mulConstCost (Nat.clog m (d + d)) L + (6 * bitLen (Nat.clog m (d + d) * L) + 5)))) ≤
      1000 * (bitLen m + bitLen L + 5) ^ 3 * (bitLen d + 1) ^ 3 := by
  have hdd : bitLen (d + d) ≤ bitLen d + 1 := bl_two_mul_le d
  have ha : Nat.clog m (d + d) ≤ bitLen d + 1 := (clog_le_bitLen hm).trans hdd
  have hba : bitLen (Nat.clog m (d + d)) ≤ bitLen d + 1 := (bitLen_le_self' _).trans ha
  have haL : bitLen (Nat.clog m (d + d) * L) ≤ bitLen d + 1 + bitLen L :=
    (bitLen_mul_le' _ _).trans (by omega)
  obtain ⟨U, hU⟩ : ∃ U, U = (bitLen m + bitLen L + 5) * (bitLen d + 1) := ⟨_, rfl⟩
  have hUe : U = (bitLen m + bitLen L) * bitLen d + (bitLen m + bitLen L) + 5 * bitLen d + 5 := by
    rw [hU]; ring
  have hU1 : 1 ≤ U := by omega
  have hUU := sq_le_cube hU1
  have hU3 := le_cube hU1
  have hc : clogCost m (d + d) ≤ 400 * U ^ 3 := by
    unfold clogCost
    exact Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left (by omega) 3)
  have hmc : mulCost (Nat.clog m (d + d)) L ≤ 100 * (U * U) := by
    unfold mulCost
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 100 (Nat.mul_le_mul (by omega) (by omega))
  have hR : 1000 * (bitLen m + bitLen L + 5) ^ 3 * (bitLen d + 1) ^ 3 = 1000 * U ^ 3 := by
    rw [hU, mul_pow, Nat.mul_assoc]
  rw [hR]
  unfold mulConstCost
  omega

/-- **Generic form of `padRCost_le`** (variables `W`, `m`, `L`, `q`, `Q` for `W_c`, `m_H`,
`⌈lg W_c⌉`, `q0Of d`, `q0Cost d`; the hypotheses are `q0Of_le` and `q0Cost_le`). -/
theorem padRCost_gen (W m L q Q c0 d K : ℕ) (hm : 1 < m) (hq : q ≤ L * (bitLen d + 1))
    (hQ : Q ≤ c0 * (bitLen d + 1) ^ 3) :
    (1 + clogCost m d) + (1 + ((bitLen 1 + 1) + powCost W 1 (Nat.clog m d))) +
    (1 + Q) + (1 + mulCost (q) K) +
    (1 + ((bitLen 1 + 1) + powCost 2 1 (q * K))) +
    (1 + (20 * (bitLen (2 ^ (q * K)) + bitLen (W ^ Nat.clog m d) + 1) +
      (6 * bitLen (2 ^ (q * K) + W ^ Nat.clog m d - 1 + 1) + 8))) + (1 + 1) +
    (2 * 20 + 70) * (bitLen (2 ^ (q * K) + W ^ Nat.clog m d - 1) *
      bitLen (W ^ Nat.clog m d) + bitLen (2 ^ (q * K) + W ^ Nat.clog m d - 1) +
      bitLen (W ^ Nat.clog m d) + 1) +
    mulCost (W ^ Nat.clog m d) ((2 ^ (q * K) + W ^ Nat.clog m d - 1) / W ^ Nat.clog m d) +
    (7 * bitLen (2 ^ (q * K)) + 7) +
    (2 * bitLen ((2 ^ (q * K) + W ^ Nat.clog m d - 1) % W ^ Nat.clog m d) + 2) +
    (2 * bitLen ((2 ^ (q * K) + W ^ Nat.clog m d - 1) / W ^ Nat.clog m d) + 2) +
    (2 * bitLen (2 ^ (q * K) + W ^ Nat.clog m d - 1) + 2) +
    (2 * bitLen (2 ^ (q * K)) + 2) + (2 * bitLen (q * K) + 2) + (2 * bitLen (q) + 2) +
    (2 * bitLen (W ^ Nat.clog m d) + 2) + (2 * bitLen (Nat.clog m d) + 2) ≤
      (100000 * (bitLen W + bitLen m + L + 10) ^ 3 + c0) * (bitLen d + q * K + bitLen K + 1) ^ 3 := by
  obtain ⟨k0, hk0d⟩ : ∃ k0, k0 = Nat.clog m d := ⟨_, rfl⟩
  obtain ⟨n, hnd⟩ : ∃ n, n = q * K := ⟨_, rfl⟩
  have hk0 : k0 ≤ bitLen d := hk0d ▸ clog_le_bitLen hm
  -- the cost bounds of the two powers (before naming them)
  have hpw1 : powCost W 1 k0 ≤ (k0 + 1) * (200 * (k0 * bitLen W + 1 + bitLen W + 2) ^ 2) := by
    unfold powCost
    rw [Nat.one_mul]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by have := bl_pow_le W k0; omega) 2))
  have hpw2 : powCost 2 1 n ≤ (n + 1) * (200 * (n + 1 + 2 + 2) ^ 2) := by
    unfold powCost
    rw [Nat.one_mul]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by have := bl_two_pow_le n; have := bl_two_le; omega) 2))
  rw [← hk0d, ← hnd]
  obtain ⟨X, hXd⟩ : ∃ X, X = 2 ^ n := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ M, M = W ^ k0 := ⟨_, rfl⟩
  have hX : bitLen X ≤ n + 1 := hXd ▸ bl_two_pow_le n
  have hX1 : 1 ≤ X := hXd ▸ Nat.one_le_two_pow
  have hM : bitLen M ≤ k0 * bitLen W + 1 := hMd ▸ bl_pow_le W k0
  rw [← hXd, ← hMd]
  have hN : bitLen (X + M - 1) ≤ bitLen X + bitLen M + 1 :=
    (bitLen_mono'' (Nat.sub_le _ _)).trans (bitLen_add_le' X M)
  have hN1 : bitLen (X + M - 1 + 1) ≤ bitLen X + bitLen M + 1 :=
    (bitLen_mono'' (by omega : X + M - 1 + 1 ≤ X + M)).trans (bitLen_add_le' X M)
  have hdiv : bitLen ((X + M - 1) / M) ≤ bitLen (X + M - 1) := bitLen_mono'' (Nat.div_le_self _ _)
  have hmod : bitLen ((X + M - 1) % M) ≤ bitLen (X + M - 1) := bitLen_mono'' (Nat.mod_le _ _)
  have hbn : bitLen n ≤ n := bitLen_le_self' n
  have hbq : bitLen q ≤ L * (bitLen d + 1) := (bitLen_le_self' q).trans hq
  have hbk0 : bitLen k0 ≤ bitLen d := (bitLen_le_self' k0).trans hk0
  have h1 := bl_one_le
  -- the scale `U = β·Z`
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = bitLen d + n + bitLen K + 1 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (bitLen W + bitLen m + L) * Z := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = (bitLen W + bitLen m + L + 10) * Z := ⟨_, rfl⟩
  have hUe : U = P + 10 * Z := by rw [hU, hP]; ring
  have hZ1 : 1 ≤ Z := by omega
  have hPW : bitLen W + bitLen m + L ≤ P := hP ▸ Nat.le_mul_of_pos_right _ hZ1
  have hk0W : k0 * bitLen W ≤ P := by
    rw [hP]
    calc k0 * bitLen W ≤ Z * (bitLen W + bitLen m + L) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = (bitLen W + bitLen m + L) * Z := Nat.mul_comm _ _
  have hLZ : L * (bitLen d + 1) ≤ P := by
    rw [hP]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hU1 : 1 ≤ U := by omega
  have hUU := sq_le_cube hU1
  have hU3 := le_cube hU1
  -- the nonlinear terms against `U`
  have b1 : clogCost m d ≤ 400 * U ^ 3 := by
    unfold clogCost
    exact Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left (by omega) 3)
  have b2 : powCost W 1 k0 ≤ 800 * U ^ 3 := by
    refine hpw1.trans ?_
    calc (k0 + 1) * (200 * (k0 * bitLen W + 1 + bitLen W + 2) ^ 2) ≤ U * (200 * (2 * U) ^ 2) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      _ = 800 * U ^ 3 := by ring
  have b3 : mulCost q K ≤ 100 * U ^ 3 := by
    unfold mulCost
    calc 100 * (bitLen q + 1) * (bitLen q + bitLen K + 2) ≤ 100 * U * U :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 100 * (U * U) := by ring
      _ ≤ 100 * U ^ 3 := Nat.mul_le_mul_left _ hUU
  have b4 : powCost 2 1 n ≤ 200 * U ^ 3 := by
    refine hpw2.trans ?_
    calc (n + 1) * (200 * (n + 1 + 2 + 2) ^ 2) ≤ U * (200 * U ^ 2) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      _ = 200 * U ^ 3 := by ring
  have b5 : bitLen (X + M - 1) * bitLen M ≤ 4 * U ^ 3 := by
    calc bitLen (X + M - 1) * bitLen M ≤ (2 * U) * (2 * U) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * (U * U) := by ring
      _ ≤ 4 * U ^ 3 := Nat.mul_le_mul_left _ hUU
  have b6 : mulCost M ((X + M - 1) / M) ≤ 1000 * U ^ 3 := by
    unfold mulCost
    calc 100 * (bitLen M + 1) * (bitLen M + bitLen ((X + M - 1) / M) + 2) ≤
          100 * (2 * U) * (5 * U) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 1000 * (U * U) := by ring
      _ ≤ 1000 * U ^ 3 := Nat.mul_le_mul_left _ hUU
  have bQ : Q ≤ c0 * Z ^ 3 := hQ.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have hR : (100000 * (bitLen W + bitLen m + L + 10) ^ 3 + c0) * (bitLen d + n + bitLen K + 1) ^ 3 =
      100000 * U ^ 3 + c0 * Z ^ 3 := by
    rw [← hZ, hU, mul_pow]; ring
  rw [hR]
  omega

/-- Generic form of `q0Of_le` (any `W` in place of `W_c`). -/
theorem mul_clog_le_gen (W m d : ℕ) (hm : 1 < m) :
    Nat.clog 2 W * Nat.clog m (2 * d) ≤ Nat.clog 2 W * (bitLen d + 1) := by
  have e : 2 * d = d + d := by omega
  rw [e]
  exact Nat.mul_le_mul_left _ ((clog_le_bitLen hm).trans (bl_two_mul_le d))

end BoundsAux

open BoundsAux SubNLogN.Math.Networks

/-- **`q₀ ≤ ⌈lg W_c⌉·(bitLen d + 1)`** (`⌈lg W_c⌉` symbolic, never evaluated). -/
theorem q0Of_le (d : ℕ) : q0Of d ≤ Nat.clog 2 Wc * (bitLen d + 1) :=
  mul_clog_le_gen Wc mH d (by norm_num [mH])

/-- **The cost of `q0N` is cubic in `bitLen d`** (`q0Cost_le`). The constant is
`1000·(bitLen m_H + bitLen ⌈lg W_c⌉ + 5)^3`. -/
theorem q0Cost_le : ∃ c, ∀ d, q0Cost d ≤ c * (bitLen d + 1) ^ 3 :=
  ⟨1000 * (bitLen mH + bitLen (Nat.clog 2 Wc) + 5) ^ 3,
    fun d => q0Cost_gen (Nat.clog 2 Wc) mH (by norm_num [mH]) d⟩

/-- **The cost of `padRN` is cubic in `bitLen d + q₀·K + bitLen K`** (`padRCost_le`). The constant is
`100000·(bitLen W_c + bitLen m_H + ⌈lg W_c⌉ + 10)^3 + c₀` with `c₀` the constant of `q0Cost_le`. -/
theorem padRCost_le : ∃ c, ∀ d K, padRCost d K ≤ c * (bitLen d + q0Of d * K + bitLen K + 1) ^ 3 := by
  obtain ⟨c0, h0⟩ := q0Cost_le
  exact ⟨100000 * (bitLen Wc + bitLen mH + Nat.clog 2 Wc + 10) ^ 3 + c0, fun d K =>
    padRCost_gen Wc mH (Nat.clog 2 Wc) (q0Of d) (q0Cost d) c0 d K (by norm_num [mH]) (q0Of_le d)
      (h0 d)⟩

end SubNLogN.Machine.Layer.DrvArith
