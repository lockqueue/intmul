/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Machine.Contracts.Arith

/-!
# K4-PREFIX, the cost of the driver (`Machine/FFT/PrefixCost.lean`)

`prefCost` is the exact cost of the driver run (`runs_main`, `Machine/FFT/PrefixRun.lean`), built
from its steps:
* the parameter phase;
* `ONE` and the copy of the working width;
* widening;
* the block count (case `v = ℓ - 1`);
* `n` passes;
* `n` truncations;
* narrowing;
* five drains.

`prefCost_le` bounds it by the contract cost of `PrefixRoundStmt` (`Contracts/FFT.lean:239`),
`Cfin·((D+1)·V_D + 2^{m₀}·(w + m₀ + 1)^{J+2} + |midHdr|)` with `V_D = cvolCube m₀ 2^ℓ (w + D)`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts

/-- Volume of `2^m` records of `2^ℓ` coefficients at width `W`. -/
def vW (W m ℓ : ℕ) : ℕ := 2 ^ m + 2 * W * (2 ^ m * 2 ^ ℓ)

/-- Cost of the block count of case `v = ℓ - 1`. -/
def cntCost (W m ℓ n L : ℕ) : ℕ :=
  (2 ^ n * (2 ^ L * (4 * (2 * W * 2 ^ ℓ) + 8) + 4 * 2 ^ L + 4 + 1 + 2) + 2) +
    ((4 * vW W m ℓ + 2) + 1)

/-- Cost bound of one iteration of the pass loop. -/
def passB (Cp W m ℓ n : ℕ) : ℕ :=
  (3 * 2 ^ n + 5) + ((4 * 2 ^ n + 2) + (1 + (Cp * (vW W m ℓ + W + 1) + ((13 * 2 ^ m + 9) + 1))))

/-- Cost of one iteration of the truncation loop. -/
def truncB (Ct W m ℓ : ℕ) : ℕ :=
  1 + (Ct * (vW W m ℓ + vW W m ℓ + W + W + bitLen 1 + 1) +
    ((4 * vW W m ℓ + 2) + (4 * vW W m ℓ + 2)))

/-- The cost of the driver. -/
def prefCost (Cr Cp Ct J w D m ℓ n L hd : ℕ) : ℕ :=
  Cr * (2 ^ m * (w + m + 1) ^ J + hd) +
  (1 + ((9 * bitLen (w + D) + 4) +
  (Ct * (vW w m ℓ + vW (w + D) m ℓ + w + (w + D) + bitLen 0 + 1) +
  ((1 + (cntCost (w + D) m ℓ n L + 1)) +
  ((n * (passB Cp (w + D) m ℓ n + 2) + 2) +
  ((n * (truncB Ct (w + D) m ℓ + 2) + 2) +
  (Ct * (vW (w + D) m ℓ + vW w m ℓ + (w + D) + w + bitLen 0 + 1) +
  ((3 * 2 ^ (L + n) + 2) + ((3 * bitLen (w + D) + 2) + ((3 * bitLen (w + D) + 2) +
  ((3 * bitLen w + 2) + (3 * 1 + 2))))))))))))

/-- The final constant. -/
def Cfin (Cr Cp Ct : ℕ) : ℕ := Cr + 10 * Cp + 10 * Ct + 200

/-- **The cost bound** for a prefix round. The hypotheses are what the driver supplies:
the passes act on the bits `L, …, L+n-1 < m`; `n ≤ D ≤ m`; `1 ≤ w`. -/
theorem prefCost_le (Cr Cp Ct J w D m ℓ n L hd : ℕ) (hLn : L + n ≤ m) (hnD : n ≤ D)
    (hDm : D ≤ m) (hw : 1 ≤ w) :
    prefCost Cr Cp Ct J w D m ℓ n L hd ≤
      Cfin Cr Cp Ct * ((D + 1) * cvolCube m (2 ^ ℓ) (w + D) + 2 ^ m * (w + m + 1) ^ (J + 2) + hd) := by
  -- elementary facts
  have hbit : ∀ x : ℕ, bitLen x ≤ x := fun _ =>
    WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self
  have hb0 : bitLen 0 = 0 := Nat.le_zero.1 (hbit 0)
  have hb1 : bitLen 1 ≤ 1 := hbit 1
  have hbW : bitLen (w + D) ≤ w + D := hbit (w + D)
  have hbw : bitLen w ≤ w := hbit w
  have hN : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLN : 2 ^ (L + n) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hLn
  have hNL : 2 ^ n * 2 ^ L ≤ 2 ^ m := by rw [← pow_add, Nat.add_comm]; exact hLN
  have hE1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hR1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hX : 1 ≤ 2 ^ m * 2 ^ ℓ := Nat.mul_le_mul hE1 hR1
  have hPP : (w + m + 1) ^ J ≤ (w + m + 1) ^ (J + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmP : m ≤ (w + m + 1) ^ (J + 2) := by
    calc m ≤ w + m + 1 := by omega
      _ = (w + m + 1) ^ 1 := (pow_one _).symm
      _ ≤ (w + m + 1) ^ (J + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hV : vW (w + D) m ℓ = 2 ^ m + 2 * (w + D) * (2 ^ m * 2 ^ ℓ) := rfl
  have hU : vW w m ℓ = 2 ^ m + 2 * w * (2 ^ m * 2 ^ ℓ) := rfl
  have hVW : 2 * (w + D) + 1 ≤ vW (w + D) m ℓ := by
    rw [hV]
    linarith [Nat.mul_le_mul_left (2 * (w + D)) hX, hE1]
  have hUV : vW w m ℓ ≤ vW (w + D) m ℓ := by
    rw [hV, hU]
    linarith [Nat.mul_le_mul_right (2 ^ m * 2 ^ ℓ) (show 2 * w ≤ 2 * (w + D) by omega)]
  have hEV : 2 ^ m ≤ vW (w + D) m ℓ := by rw [hV]; omega
  have hcnt : cntCost (w + D) m ℓ n L ≤ 27 * vW (w + D) m ℓ + 5 := by
    have h1 := Nat.mul_le_mul_left ((w + D) * 2 ^ ℓ) hNL
    have h0 : 0 ≤ (w + D) * (2 ^ m * 2 ^ ℓ) := Nat.zero_le _
    unfold cntCost
    rw [hV]
    linarith [h1, hNL, hN, hE1, h0]
  have hcv : cvolCube m (2 ^ ℓ) (w + D) = vW (w + D) m ℓ := by
    rw [hV]; unfold cvolCube; ring
  rw [hcv]
  -- separate the constants `Cr`, `Cp`, `Ct`
  have hsplit : prefCost Cr Cp Ct J w D m ℓ n L hd =
      Cr * (2 ^ m * (w + m + 1) ^ J + hd) + Cp * (n * (vW (w + D) m ℓ + (w + D) + 1)) +
      Ct * ((vW w m ℓ + vW (w + D) m ℓ + w + (w + D) + bitLen 0 + 1) +
        n * (vW (w + D) m ℓ + vW (w + D) m ℓ + (w + D) + (w + D) + bitLen 1 + 1) +
        (vW (w + D) m ℓ + vW w m ℓ + (w + D) + w + bitLen 0 + 1)) +
      (1 + (9 * bitLen (w + D) + 4) + (1 + (cntCost (w + D) m ℓ n L + 1)) +
        (n * ((3 * 2 ^ n + 5) + (4 * 2 ^ n + 2) + 1 + (13 * 2 ^ m + 9) + 1 + 2) + 2) +
        (n * (1 + (4 * vW (w + D) m ℓ + 2) + (4 * vW (w + D) m ℓ + 2) + 2) + 2) +
        (3 * 2 ^ (L + n) + 2) + (3 * bitLen (w + D) + 2) + (3 * bitLen (w + D) + 2) +
        (3 * bitLen w + 2) + (3 * 1 + 2)) := by
    unfold prefCost passB truncB
    ring
  rw [hsplit]
  -- abbreviations
  generalize hVd : vW (w + D) m ℓ = V at *
  generalize hUd : vW w m ℓ = U at *
  generalize hPd : (w + m + 1) ^ (J + 2) = P' at *
  have hT : Cfin Cr Cp Ct * ((D + 1) * V + 2 ^ m * P' + hd) =
      Cr * ((D + 1) * V + 2 ^ m * P' + hd) + Cp * (10 * ((D + 1) * V + 2 ^ m * P' + hd)) +
      Ct * (10 * ((D + 1) * V + 2 ^ m * P' + hd)) + 200 * ((D + 1) * V + 2 ^ m * P' + hd) := by
    unfold Cfin; ring
  rw [hT]
  have hDV : 0 ≤ D * V := Nat.zero_le _
  have hEP : 0 ≤ 2 ^ m * P' := Nat.zero_le _
  -- the four groups
  have hA : 2 ^ m * (w + m + 1) ^ J + hd ≤ (D + 1) * V + 2 ^ m * P' + hd := by
    have := Nat.mul_le_mul_left (2 ^ m) hPP
    omega
  have hB : n * (V + (w + D) + 1) ≤ 10 * ((D + 1) * V + 2 ^ m * P' + hd) := by
    have h1 : n * (V + (w + D) + 1) ≤ D * (2 * V) := Nat.mul_le_mul hnD (by omega)
    linarith [h1, hDV, hEP]
  have hC : (U + V + w + (w + D) + bitLen 0 + 1) +
        n * (V + V + (w + D) + (w + D) + bitLen 1 + 1) + (V + U + (w + D) + w + bitLen 0 + 1) ≤
      10 * ((D + 1) * V + 2 ^ m * P' + hd) := by
    have h1 : n * (V + V + (w + D) + (w + D) + bitLen 1 + 1) ≤ D * (4 * V) :=
      Nat.mul_le_mul hnD (by omega)
    linarith [h1, hUV, hVW, hb0, hDV, hEP]
  have hZ : 1 + (9 * bitLen (w + D) + 4) + (1 + (cntCost (w + D) m ℓ n L + 1)) +
        (n * ((3 * 2 ^ n + 5) + (4 * 2 ^ n + 2) + 1 + (13 * 2 ^ m + 9) + 1 + 2) + 2) +
        (n * (1 + (4 * V + 2) + (4 * V + 2) + 2) + 2) +
        (3 * 2 ^ (L + n) + 2) + (3 * bitLen (w + D) + 2) + (3 * bitLen (w + D) + 2) +
        (3 * bitLen w + 2) + (3 * 1 + 2) ≤ 200 * ((D + 1) * V + 2 ^ m * P' + hd) := by
    have h1 : n * ((3 * 2 ^ n + 5) + (4 * 2 ^ n + 2) + 1 + (13 * 2 ^ m + 9) + 1 + 2) ≤
        m * (40 * 2 ^ m) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : m * (40 * 2 ^ m) ≤ 40 * (2 ^ m * P') := by
      calc m * (40 * 2 ^ m) = 40 * (2 ^ m * m) := by ring
        _ ≤ 40 * (2 ^ m * P') := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmP)
    have h3 : n * (1 + (4 * V + 2) + (4 * V + 2) + 2) ≤ D * (15 * V) :=
      Nat.mul_le_mul hnD (by omega)
    linarith [h1, h2, h3, hcnt, hbW, hbw, hLN, hEV, hVW, hDV, hEP]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hA)
      (Nat.mul_le_mul_left _ hB)) (Nat.mul_le_mul_left _ hC)) hZ

end SubNLogN.Machine.FFT.PrefixAux
