import WP.W9fN.FinishSpec

/-!
# WP.W9fNF.Cost — the final cost arithmetic of the Nyquist finish (pure `ℕ`)

`finish_cost`: the six phase costs `T0 … T5` sum to at most
`(24·Cs + 32·Ca + 8·Cn + 32·Cf + 1000)·(t1·(H+k+1) + (H+1)²)`.

With `N := H + k + 1 ≥ 2` and `X := t1·N ≥ t1 ≥ k ≥ 1`, each phase is bounded by a linear
combination of `Cs·X, Ca·X, Cn·X, Cf·X, X`. The free constants sum to `39 + 203 + 201 + 163 + 208 + 49
= 863 ≤ 1000`. The `(H+1)²` term is slack.
-/

namespace WP.W9fNF

theorem finish_cost (Cs Ca Cn Cf H k t1 T0 T1 T2 T3 T4 T5 : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t1)
    (h0 : T0 ≤ 13 * k + 26)
    (h1 : T1 ≤ t1 * ((4 * Cs + 100) * (H + k + 2) + 1) + 1)
    (h2 : T2 ≤ 2 * ((2 * Cs + 2 * Ca + 4 * Cf + 20) * (H + k + 4)) + 7 * (H + k + 3) + 20)
    (h3 : T3 ≤ t1 * ((4 * Ca + 2 * Cn + 40) * (H + k + 4) + 1) + 1)
    (h4 : T4 ≤ 16 * (t1 * (2 * (H + k + 4) + 4) + 1))
    (h5 : T5 ≤ 9 * (H + k + 3) + 22) :
    T0 + (1 + T1) + T2 + (1 + T3) + T4 + T5 ≤
      (24 * Cs + 32 * Ca + 8 * Cn + 32 * Cf + 1000) * (t1 * (H + k + 1) + (H + 1) ^ 2) := by
  set N := H + k + 1 with hN
  set X := t1 * N with hX
  have ht1 : 1 ≤ t1 := le_trans hk hkt
  have hN1 : 1 ≤ N := by omega
  have hX1 : t1 ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_right t1 hN1
  have hXN : N ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_left N ht1
  have b1 : T1 ≤ 8 * (Cs * X) + 200 * X + t1 + 1 := by
    have e : t1 * ((4 * Cs + 100) * (H + k + 2) + 1) ≤ t1 * ((4 * Cs + 100) * (2 * N) + 1) :=
      Nat.mul_le_mul_left t1 (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1)
    have e2 : t1 * ((4 * Cs + 100) * (2 * N) + 1) = 8 * (Cs * X) + 200 * X + t1 := by
      rw [hX]; ring
    omega
  have b2 : T2 ≤ 16 * (Cs * X) + 16 * (Ca * X) + 32 * (Cf * X) + 160 * X + 21 * X + 20 := by
    have e : (2 * Cs + 2 * Ca + 4 * Cf + 20) * (H + k + 4) ≤
        (2 * Cs + 2 * Ca + 4 * Cf + 20) * (4 * X) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : (2 * Cs + 2 * Ca + 4 * Cf + 20) * (4 * X) =
        8 * (Cs * X) + 8 * (Ca * X) + 16 * (Cf * X) + 80 * X := by ring
    omega
  have b3 : T3 ≤ 16 * (Ca * X) + 8 * (Cn * X) + 160 * X + t1 + 1 := by
    have e : t1 * ((4 * Ca + 2 * Cn + 40) * (H + k + 4) + 1) ≤
        t1 * ((4 * Ca + 2 * Cn + 40) * (4 * N) + 1) :=
      Nat.mul_le_mul_left t1 (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1)
    have e2 : t1 * ((4 * Ca + 2 * Cn + 40) * (4 * N) + 1) =
        16 * (Ca * X) + 8 * (Cn * X) + 160 * X + t1 := by
      rw [hX]; ring
    omega
  have b4 : T4 ≤ 192 * X + 16 := by
    have e : t1 * (2 * (H + k + 4) + 4) ≤ t1 * (12 * N) := Nat.mul_le_mul_left t1 (by omega)
    have e2 : t1 * (12 * N) = 12 * X := by rw [hX]; ring
    omega
  have eR : (24 * Cs + 32 * Ca + 8 * Cn + 32 * Cf + 1000) * (X + (H + 1) ^ 2) =
      24 * (Cs * X) + 32 * (Ca * X) + 8 * (Cn * X) + 32 * (Cf * X) + 1000 * X +
        (24 * Cs + 32 * Ca + 8 * Cn + 32 * Cf + 1000) * (H + 1) ^ 2 := by ring
  rw [eR]
  omega

#assert_std_axioms finish_cost

end WP.W9fNF
