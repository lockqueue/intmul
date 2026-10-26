/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulOne

/-!
# AR4, products: the cost arithmetic of the kernel (`Arith/CMulCost.lean`)

Pure arithmetic: the teardown cost (`tear_cost_le`), and the sum of the setup, record-loop and
teardown costs is at most
`(4·Cm + 1000)·(M·mulW (w1 + w2 + 1) + V_z + V_θ + V_out + (M + 1)·(bitLen s + 1) + w1 + w2 + w3)`
(`cmul_cost_le`). Everything is proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

theorem tear_cost_le (w1 w2 w3 s c3 : ℕ) :
    3 * c3 + 2 + (3 * w1 + 2) + (3 * w2 + 2) + (3 * w3 + 2) + (3 * (2 * max w1 w2 + 1) + 2) +
      (3 * min s (2 * max w1 w2 + 1) + 2) +
      (3 * (2 * max w1 w2 + 1 - min s (2 * max w1 w2 + 1)) + 2) ≤
    3 * c3 + 15 * (w1 + w2) + 3 * w3 + 20 := by
  have h1 : max w1 w2 ≤ w1 + w2 := by omega
  have h2 : min s (2 * max w1 w2 + 1) ≤ 2 * max w1 w2 + 1 := min_le_right _ _
  omega

theorem cmul_cost_le (Cm w1 w2 w3 s n L t1 t4 c1 c2 c3 : ℕ)
    (ht1 : t1 ≤ 300 * (w1 + w2 + w3 + bitLen s) + 300)
    (ht4 : t4 ≤ n * (coefBound Cm w1 w2 w3 + 1) + 6 * L + 1 +
      (3 * c3 + 15 * (w1 + w2) + 3 * w3 + 20))
    (hc1 : c1 = L + 2 * w1 * n) (hc2 : c2 = L + 2 * w2 * n) (hc3 : c3 = L + 2 * w3 * n) :
    t1 + (1 + t4) ≤ (4 * Cm + 1000) * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 +
      (n + 1) * (bitLen s + 1) + w1 + w2 + w3) := by
  have hkey : n * (coefBound Cm w1 w2 w3 + 1) = 4 * (Cm * (n * mulW (w1 + w2 + 1))) +
      400 * (n * w1) + 400 * (n * w2) + 400 * (n * w3) + 401 * n := by
    unfold coefBound; ring
  have hD : (n + 1) * (bitLen s + 1) = n * bitLen s + n + bitLen s + 1 := by ring
  have hc1' : c1 = L + 2 * (n * w1) := by rw [hc1]; ring
  have hc2' : c2 = L + 2 * (n * w2) := by rw [hc2]; ring
  have hc3' : c3 = L + 2 * (n * w3) := by rw [hc3]; ring
  have hexp : (4 * Cm + 1000) * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 +
      (n + 1) * (bitLen s + 1) + w1 + w2 + w3) =
      4 * (Cm * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 + (n + 1) * (bitLen s + 1) + w1 + w2 +
        w3)) + 1000 * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 + (n + 1) * (bitLen s + 1) + w1 +
        w2 + w3) := by ring
  have hXm : Cm * (n * mulW (w1 + w2 + 1)) ≤ Cm * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 +
      (n + 1) * (bitLen s + 1) + w1 + w2 + w3) := Nat.mul_le_mul_left _ (by omega)
  rw [hexp]
  rw [hkey] at ht4
  generalize Cm * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 + (n + 1) * (bitLen s + 1) + w1 + w2 +
    w3) = A1 at hXm ⊢
  generalize Cm * (n * mulW (w1 + w2 + 1)) = A2 at hXm ht4
  generalize n * mulW (w1 + w2 + 1) = E at hXm ⊢
  generalize (n + 1) * (bitLen s + 1) = D at hD ⊢
  generalize n * bitLen s = F at hD
  generalize n * w1 = B1 at hc1' ht4
  generalize n * w2 = B2 at hc2' ht4
  generalize n * w3 = B3 at hc3' ht4
  subst hc1' hc2' hc3' hD
  linarith

end SubNLogN.Machine.Arith
