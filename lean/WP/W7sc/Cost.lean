import WP.W7sc.Math

/-!
# WP.W7sc.Cost — the `stdChar` kernel's cost in the contract's shape

`scProg_spec` bounds a run by `140·U + C·(q+7)⁴ + 2·Cs·(q+28)·(w+2)²` with `w = wv q den`,
`U = C·(K+8)·(2w+1)²`. Since `wv q den = 9q + 238 + 2·log₂ den ≤ 249·M` for
`M = q + |den| + 1` (`log₂ den ≤ |den|`), every term is at most a constant times `M⁴`:
`sc_cost_le` with the explicit constant `scC C K Cs`.
-/

namespace WP.W7sc

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3

/-- The contract's cost constant of the `stdChar` kernel. -/
def scC (C K Cs : ℕ) : ℕ := 140 * 249001 * (C * (K + 8)) + 2401 * C + 3528056 * Cs

theorem log2_le_bitLen (n : ℕ) : Nat.log2 n ≤ bitLen n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.log2_zero]
  · have h1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
    have h2 : n < 2 ^ bitLen n := lt_two_pow_bitLen n
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h1 h2))

theorem wv_le (q den : ℕ) : wv q den ≤ 249 * (q + bitLen den + 1) := by
  have := log2_le_bitLen den
  unfold wv
  omega

theorem sc_cost_le (C K Cs q den : ℕ) :
    140 * (C * (K + 8) * (2 * wv q den + 1) ^ 2) + C * (q + 2 + 4 + 1) ^ 4 +
      2 * (Cs * (q + 2 + 25 + 1) * (wv q den + 2) ^ 2) ≤
      scC C K Cs * (q + bitLen den + 1) ^ 4 := by
  have hw := wv_le q den
  obtain ⟨M, hM⟩ : ∃ M, M = q + bitLen den + 1 := ⟨_, rfl⟩
  rw [← hM] at hw ⊢
  have hM1 : 0 < M := by omega
  have m24 : M ^ 2 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by norm_num)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by norm_num)
  -- the twiddle-unit term
  have a2 : (2 * wv q den + 1) ^ 2 ≤ (499 * M) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a4 : (2 * wv q den + 1) ^ 2 ≤ 249001 * M ^ 4 := by
    calc _ ≤ (499 * M) ^ 2 := a2
      _ = 249001 * M ^ 2 := by ring
      _ ≤ 249001 * M ^ 4 := Nat.mul_le_mul_left _ m24
  -- the `π` term
  have b2 : (q + 2 + 4 + 1) ^ 4 ≤ (7 * M) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have b4 : (q + 2 + 4 + 1) ^ 4 ≤ 2401 * M ^ 4 := le_of_le_of_eq b2 (by ring)
  -- the series term
  have c3 : (wv q den + 2) ^ 2 ≤ (251 * M) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have c4 : (q + 2 + 25 + 1) * (wv q den + 2) ^ 2 ≤ (28 * M) * (251 * M) ^ 2 :=
    Nat.mul_le_mul (by omega) c3
  have c6 : (q + 2 + 25 + 1) * (wv q den + 2) ^ 2 ≤ 1764028 * M ^ 4 := by
    calc _ ≤ (28 * M) * (251 * M) ^ 2 := c4
      _ = 1764028 * M ^ 3 := by ring
      _ ≤ 1764028 * M ^ 4 := Nat.mul_le_mul_left _ m34
  have t1 : 140 * (C * (K + 8) * (2 * wv q den + 1) ^ 2) ≤
      140 * 249001 * (C * (K + 8)) * M ^ 4 := by
    calc 140 * (C * (K + 8) * (2 * wv q den + 1) ^ 2) ≤
          140 * (C * (K + 8) * (249001 * M ^ 4)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a4)
      _ = 140 * 249001 * (C * (K + 8)) * M ^ 4 := by ring
  have t2 : C * (q + 2 + 4 + 1) ^ 4 ≤ 2401 * C * M ^ 4 := by
    calc C * (q + 2 + 4 + 1) ^ 4 ≤ C * (2401 * M ^ 4) := Nat.mul_le_mul_left _ b4
      _ = 2401 * C * M ^ 4 := by ring
  have t3 : 2 * (Cs * (q + 2 + 25 + 1) * (wv q den + 2) ^ 2) ≤ 3528056 * Cs * M ^ 4 := by
    calc 2 * (Cs * (q + 2 + 25 + 1) * (wv q den + 2) ^ 2) =
          2 * (Cs * ((q + 2 + 25 + 1) * (wv q den + 2) ^ 2)) := by ring
      _ ≤ 2 * (Cs * (1764028 * M ^ 4)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c6)
      _ = 3528056 * Cs * M ^ 4 := by ring
  have e : scC C K Cs * M ^ 4 =
      140 * 249001 * (C * (K + 8)) * M ^ 4 + 2401 * C * M ^ 4 + 3528056 * Cs * M ^ 4 := by
    unfold scC
    ring
  rw [e]
  omega

#assert_std_axioms log2_le_bitLen wv_le sc_cost_le

end WP.W7sc
