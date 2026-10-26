import SubNLogN.Spec

/-!
# Component S1 (`Params.lean`): Closed-Form Triple Network Counts, Guard Constants & Deficits

Proves the closed-form identities and exact integer certificates at `h = 100` (`m = 10^6`)
for the bit and complex triple networks (`[OAI26, §3]`, Definition A.1 (`def:fixed-network-premises`),
Proposition A.2 (`prop:deficits`), Table 8 (`app:cert-closed`), and eq. (`eq:walsh-guard-constants`)).
-/

namespace SubNLogN.S1

open SubNLogN

/-- Exact factor-space dimension at `h = 100`: `m = 100^3 = 1000000`. -/
theorem tripleM_100 : tripleM 100 = 1000000 := by decide

/-- Exact number of triples at `h = 100`: `v = C(100, 3) = 161700`. -/
theorem tripleV_100 : tripleV 100 = 161700 := by decide

/-- Exact bit-network neighbor count at `h = 100`: `z_b = 3 C(97, 2) = 13968`. -/
theorem tripleZb_100 : tripleZb 100 = 13968 := by decide

/-- Exact complex-network neighbor count at `h = 100`: `z_c = C(97, 3) + 3 · 97 = 147731`. -/
theorem tripleZc_100 : tripleZc 100 = 147731 := by decide

/-- Exact role count of the bit triple network at `h = 100`: `W_b = 177176569091445000000`. -/
theorem tripleWb_100 : tripleWb 100 = 177176569091445000000 := by decide

/-- Exact edge-rank sum of the bit triple network at `h = 100`: `s_b = 177176569088785861287000000`. -/
theorem tripleSb_100 : tripleSb 100 = 177176569088785861287000000 := by decide

/-- Exact rank saving of the bit triple network at `h = 100`: `W_b m - s_b = 2659138713000000`. -/
theorem tripleSavingBit_100 :
    tripleWb 100 * tripleM 100 - tripleSb 100 = 2659138713000000 := by decide

/-- Exact role count of the complex triple network at `h = 100`: `W_c = 1873807244643542670000`. -/
theorem tripleWc_100 : tripleWc 100 = 1873807244643542670000 := by decide

/-- Exact residual-dimension sum of the complex triple network at `h = 100`:
`s_c = 1873807244636671267308000000`. -/
theorem tripleSc_100 : tripleSc 100 = 1873807244636671267308000000 := by decide

/-- Exact dimension saving of the complex triple network at `h = 100`:
`W_c m - s_c = 6871402692000000`. -/
theorem tripleSavingComplex_100 :
    tripleWc 100 * tripleM 100 - tripleSc 100 = 6871402692000000 := by decide

/-- Bit-network first saving threshold (Table 8 (`app:cert-closed`)): no saving at `h = 38`, positive saving at `h = 39`. -/
theorem bit_threshold_38_39 :
    tripleSb 38 > tripleWb 38 * tripleM 38 ∧
    tripleWb 39 * tripleM 39 - tripleSb 39 = 1085777173 := by decide

/-- Complex-network first saving threshold (Table 8 (`app:cert-closed`)): no saving at `h = 21`, positive saving at `h = 22`. -/
theorem complex_threshold_21_22 :
    tripleSc 21 > tripleWc 21 * tripleM 21 ∧
    tripleWc 22 * tripleM 22 - tripleSc 22 = 104350400 := by decide

/-- Certified deficit inequality for `τ = 1 - 2^{-40}` at `h = 100` (Proposition A.2 (`prop:deficits`)):
`(W_b m - s_b) · 2^{40} > 14 · W_b m`. -/
theorem bit_deficit_tau_40 :
    (tripleWb 100 * tripleM 100 - tripleSb 100) * (2 ^ 40) >
      14 * (tripleWb 100 * tripleM 100) := by decide

/-- Certified deficit inequality for `σ = 1 - 2^{-42}` at `h = 100` (Proposition A.2 (`prop:deficits`)):
`(W_c m - s_c) · 2^{42} > 14 · W_c m`. -/
theorem complex_deficit_sigma_42 :
    (tripleWc 100 * tripleM 100 - tripleSc 100) * (2 ^ 42) >
      14 * (tripleWc 100 * tripleM 100) := by decide

/-- Certified deficit inequalities for the printed exponent `1 - 2^{-50}` with crude bound `L = 20`:
`(W m - s) · 2^{50} > 20 · W m` for both networks at `h = 100`. -/
theorem printed_deficit_50 :
    (tripleWb 100 * tripleM 100 - tripleSb 100) * (2 ^ 50) >
      20 * (tripleWb 100 * tripleM 100) ∧
    (tripleWc 100 * tripleM 100 - tripleSc 100) * (2 ^ 50) >
      20 * (tripleWc 100 * tripleM 100) := by decide

/-- Sharpness witness (Remark A.3 (`rem:deficit-margins`)): the complex network at `h = 100` fails the `1 - 2^{-40}` test
even against `L = 10 < ln(10^6)`. -/
theorem complex_sharpness_40 :
    (tripleWc 100 * tripleM 100 - tripleSc 100) * (2 ^ 40) <
      10 * (tripleWc 100 * tripleM 100) := by decide

/-- Guard exponent certificate `ν_net = 11` (Proposition A.2 (`prop:deficits`), eq. (`eq:walsh-guard-constants`)):
`m^{10} < B_net ≤ m^{11}` at `h = 100`. -/
theorem guard_nu_11 :
    (tripleM 100) ^ 10 < guardBnet 100 ∧ guardBnet 100 ≤ (tripleM 100) ^ 11 := by decide

/-- Elementary Taylor partial-sum certificate for `e^7 > 1000` (Proposition A.2 (`prop:deficits`)), which gives
`ln(10^6) = 2 ln(1000) < 14`: multiplying by `11! = 39916800`,
`∑_{j=0}^{11} 7^j · (11! / j!) = 41438755442 > 39916800000 = 1000 · 11!`. -/
def exp7TaylorScaled11 : ℕ :=
  let fact11 := 39916800
  (7^0 * (fact11 / 1)) +
  (7^1 * (fact11 / 1)) +
  (7^2 * (fact11 / 2)) +
  (7^3 * (fact11 / 6)) +
  (7^4 * (fact11 / 24)) +
  (7^5 * (fact11 / 120)) +
  (7^6 * (fact11 / 720)) +
  (7^7 * (fact11 / 5040)) +
  (7^8 * (fact11 / 40320)) +
  (7^9 * (fact11 / 362880)) +
  (7^10 * (fact11 / 3628800)) +
  (7^11 * (fact11 / 39916800))

theorem exp7_gt_1000_certificate :
    exp7TaylorScaled11 > 1000 * 39916800 := by decide

end SubNLogN.S1
