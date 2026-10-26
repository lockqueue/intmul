/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.AppC.C5StreamArith
import WP.W0m.Sched

/-!
# C-core header kernels: cost facts from the bands (`CCore/LeafHdrCost.lean`)

Elementary consequences of `CCoreBands p P₀ t` (`Contracts/CCore.lean:196`) for `1 ≤ P₀`, used to
bound the cost of the header kernels by `C · t.volG` (`t.volG = 2·M·r·w_g`):
* every descriptor field except `d` is at most `t.volG` (`fields_le_volG`), and
  `(k + 1)^3 ≤ m^k = e ≤ D ≤ t.volG`;
* the `d`-band `d ≤ b_d · P^ε` gives `(bitLen d + 1)^2 ≤ dConst p · P` (`bitLen_d_sq_le`), with
  `dConst p = 5 · (bitLen ⌈b_d⌉₊ + ⌈ε⌉₊ + 2)^2` (a constant of `p` only).
No `p.OK` is needed: only `1 ≤ P₀ ≤ P`, `0 < 2^x ≤ r`, `ρ < K`, `j0 + e ≤ D`, `1 ≤ A, S`, `R ∣ A`
and the upper `d`-band are used.
-/

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## Bit lengths -/

theorem bitLen_one_le : bitLen 1 ≤ 1 := WP.W0m.bitLen_le_self 1

/-- `bitLen (a ^ n) ≤ n · bitLen a + 1`. -/
theorem bitLen_pow_le (a : ℕ) : ∀ n, bitLen (a ^ n) ≤ n * bitLen a + 1
  | 0 => by simpa using bitLen_one_le
  | n + 1 => by
    have ih := bitLen_pow_le a n
    have hm := NatArith.bitLen_mul_le' (a ^ n) a
    rw [pow_succ, Nat.succ_mul]
    omega

theorem sq_le_five_two_pow : ∀ L : ℕ, (L + 2) ^ 2 ≤ 5 * 2 ^ L
  | 0 => by norm_num
  | 1 => by norm_num
  | L + 2 => by
    have ih := sq_le_five_two_pow (L + 1)
    have e : (2 : ℕ) ^ (L + 2) = 2 * 2 ^ (L + 1) := by ring
    have h0 : (L + 2 + 2) ^ 2 + (L * L + 4 * L + 2) = 2 * (L + 1 + 2) ^ 2 := by ring
    have h1 : (L + 2 + 2) ^ 2 ≤ 2 * (L + 1 + 2) ^ 2 := Nat.le.intro h0
    rw [e]
    calc (L + 2 + 2) ^ 2 ≤ 2 * (L + 1 + 2) ^ 2 := h1
      _ ≤ 2 * (5 * 2 ^ (L + 1)) := Nat.mul_le_mul_left 2 ih
      _ = 5 * (2 * 2 ^ (L + 1)) := by ring

/-- `(bitLen n + 1)^2 ≤ 5 n` for `n ≥ 1`. -/
theorem bitLen_succ_sq_le {n : ℕ} (hn : 1 ≤ n) : (bitLen n + 1) ^ 2 ≤ 5 * n := by
  have hs : bitLen n = Nat.size n := WP.W0m.bitLen_eq_size n
  have hpos : 0 < Nat.size n := Nat.size_pos.mpr hn
  obtain ⟨L, hL⟩ : ∃ L, Nat.size n = L + 1 := ⟨Nat.size n - 1, by omega⟩
  have h2 : 2 ^ L ≤ n := Nat.lt_size.mp (by omega)
  have h3 := sq_le_five_two_pow L
  rw [hs, hL]
  calc (L + 1 + 1) ^ 2 = (L + 2) ^ 2 := by ring
    _ ≤ 5 * 2 ^ L := h3
    _ ≤ 5 * n := Nat.mul_le_mul_left 5 h2

/-! ## The depth bound -/

theorem eight_le_mn : 8 ≤ mn := by norm_num [mn, tripleM]

/-- `(k + 1)^3 ≤ m^k`. -/
theorem pow3_le_mn_pow : ∀ k : ℕ, (k + 1) ^ 3 ≤ mn ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := pow3_le_mn_pow k
    have h1 : (k + 1 + 1) ^ 3 ≤ (2 * (k + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (2 * (k + 1)) ^ 3 = 8 * (k + 1) ^ 3 := by ring
    calc (k + 1 + 1) ^ 3 ≤ 8 * (k + 1) ^ 3 := h2 ▸ h1
      _ ≤ mn * mn ^ k := Nat.mul_le_mul eight_le_mn ih
      _ = mn ^ (k + 1) := by ring

/-! ## The `d`-band -/

/-- The constant of the `d`-band bound. -/
noncomputable def dConst (p : LayerParams) : ℕ := 5 * (bitLen ⌈p.b_d⌉₊ + ⌈p.ε⌉₊ + 2) ^ 2

theorem d_le_poly {p : LayerParams} {P d : ℕ} (hP : 1 ≤ P)
    (hd : (d : ℝ) ≤ p.b_d * (P : ℝ) ^ p.ε) : d ≤ ⌈p.b_d⌉₊ * P ^ ⌈p.ε⌉₊ := by
  have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have h1 : (P : ℝ) ^ p.ε ≤ (P : ℝ) ^ ((⌈p.ε⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP' (Nat.le_ceil _)
  rw [Real.rpow_natCast] at h1
  have h3 : 0 ≤ (P : ℝ) ^ p.ε := Real.rpow_nonneg (by positivity) _
  have h4 : (d : ℝ) ≤ (⌈p.b_d⌉₊ : ℝ) * (P : ℝ) ^ ⌈p.ε⌉₊ :=
    calc (d : ℝ) ≤ p.b_d * (P : ℝ) ^ p.ε := hd
      _ ≤ (⌈p.b_d⌉₊ : ℝ) * (P : ℝ) ^ p.ε := mul_le_mul_of_nonneg_right (Nat.le_ceil _) h3
      _ ≤ (⌈p.b_d⌉₊ : ℝ) * (P : ℝ) ^ ⌈p.ε⌉₊ := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  exact_mod_cast h4

/-- **The `d`-band in bit lengths**: `(bitLen d + 1)^2 ≤ dConst p · P`. -/
theorem bitLen_d_sq_le {p : LayerParams} {P d : ℕ} (hP : 1 ≤ P)
    (hd : (d : ℝ) ≤ p.b_d * (P : ℝ) ^ p.ε) : (bitLen d + 1) ^ 2 ≤ dConst p * P := by
  have h1 := d_le_poly hP hd
  have h2 : bitLen d ≤ bitLen ⌈p.b_d⌉₊ + (⌈p.ε⌉₊ * bitLen P + 1) :=
    le_trans (NatArith.bitLen_mono'' h1) (le_trans (NatArith.bitLen_mul_le' _ _)
      (Nat.add_le_add_left (bitLen_pow_le P _) _))
  have h3 : bitLen d + 1 ≤ (bitLen ⌈p.b_d⌉₊ + ⌈p.ε⌉₊ + 2) * (bitLen P + 1) := by
    nlinarith [h2, Nat.zero_le (bitLen P), Nat.zero_le (⌈p.ε⌉₊ * bitLen P)]
  have h4 := bitLen_succ_sq_le hP
  calc (bitLen d + 1) ^ 2 ≤ ((bitLen ⌈p.b_d⌉₊ + ⌈p.ε⌉₊ + 2) * (bitLen P + 1)) ^ 2 :=
        Nat.pow_le_pow_left h3 2
    _ = (bitLen ⌈p.b_d⌉₊ + ⌈p.ε⌉₊ + 2) ^ 2 * (bitLen P + 1) ^ 2 := by ring
    _ ≤ (bitLen ⌈p.b_d⌉₊ + ⌈p.ε⌉₊ + 2) ^ 2 * (5 * P) := Nat.mul_le_mul_left _ h4
    _ = dConst p * P := by simp only [dConst]; ring

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## Descriptor fields versus the guarded volume -/

/-- **Every descriptor field except `d` is at most `t.volG`**, and `(k + 1)^3 ≤ t.volG`
(from the bands: `0 < 2^x ≤ r`, `ρ < K`, `j0 + e ≤ D`, `1 ≤ A, S`, `R ∣ A`). -/
theorem fields_le_volG {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (h : CCoreBands p P₀ t) :
    t.P ≤ t.volG ∧ t.r ≤ t.volG ∧ t.Δ ≤ t.volG ∧ t.A ≤ t.volG ∧ t.R ≤ t.volG ∧
    t.K ≤ t.volG ∧ t.D ≤ t.volG ∧ t.S ≤ t.volG ∧ t.j0 ≤ t.volG ∧ t.k ≤ t.volG ∧
    t.ρ ≤ t.volG ∧ (t.k + 1) ^ 3 ≤ t.volG ∧ 1 ≤ t.volG := by
  obtain ⟨-, -, -, hr1, -, -, -, hA, hS, hRA, -, hjD, hρK, -⟩ := h
  have hr : 1 ≤ t.r := by
    have h0 : (0 : ℝ) < t.r := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) hr1
    exact_mod_cast h0
  have hK : 1 ≤ t.K := by omega
  have he : t.e = mn ^ t.k := rfl
  have he1 : 1 ≤ t.e := by rw [he]; exact Nat.one_le_pow _ _ (by norm_num [mn, tripleM])
  have hD : 1 ≤ t.D := by omega
  have hKD : t.D ≤ t.K * t.D := Nat.le_mul_of_pos_left _ hK
  have hKD' : t.K ≤ t.K * t.D := Nat.le_mul_of_pos_right _ hD
  have h2D : t.K * t.D < 2 ^ (t.K * t.D) := Nat.lt_two_pow_self
  have hM : t.M = t.A * t.S * 2 ^ (t.K * t.D) := rfl
  have hp1 : 1 ≤ 2 ^ (t.K * t.D) := Nat.one_le_two_pow
  have hAM : t.A ≤ t.M := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left t.A hS) hp1
    rw [hM]; simpa using this
  have hSM : t.S ≤ t.M := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_right t.S hA) hp1
    rw [hM]; simpa using this
  have h2M : 2 ^ (t.K * t.D) ≤ t.M := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hA hS) (le_refl (2 ^ (t.K * t.D)))
    rw [hM]; simpa using this
  have hwg : t.wg = t.P + 2 * t.Δ + 3 := rfl
  have hV : t.volG = 2 * t.M * t.r * t.wg := rfl
  have hM1 : 1 ≤ t.M := le_trans hp1 h2M
  have hwg1 : 1 ≤ t.wg := by rw [hwg]; omega
  have hMV : t.M ≤ t.volG := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ 2 by norm_num)
      (le_refl t.M)) hr) hwg1
    rw [hV]; simpa using this
  have hwgV : t.wg ≤ t.volG := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ 2 by norm_num) hM1) hr)
      (le_refl t.wg)
    rw [hV]; simpa using this
  have hrV : t.r ≤ t.volG := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ 2 by norm_num) hM1)
      (le_refl t.r)) hwg1
    rw [hV]; simpa using this
  have hRA' : t.R ≤ t.A := Nat.le_of_dvd (by omega) hRA
  have hkE : t.k < t.e := by rw [he]; exact Nat.lt_pow_self (by norm_num [mn, tripleM])
  have hk3 : (t.k + 1) ^ 3 ≤ t.e := by rw [he]; exact pow3_le_mn_pow t.k
  refine ⟨by omega, hrV, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

end SubNLogN.Machine.CCore.LeafHdrAux
