import SubNLogN.Spec

/-!
# Component S3 (`PositionalPerm.lean`): 3-Stage XOR Swap & Two-Involution Cycle Decomposition

**Scope.** Proves `Bool` 3-stage XOR swap, modular cycle reflections on `[0, n)` (accompanying Lemma 5.7 (`lem:walsh-involutions`)),
and the `ℕ` slice-count inequality `K * ((J + d - 1) / d) ≤ m₀ / d + K` (`eq:walsh-slices`; full proofs of Lemma 5.7 & Theorem 5.8 (`thm:positional-perm`) live in `SubNLogN/{Math,Machine}/Walsh/`).
-/

namespace SubNLogN.S3

open SubNLogN

/-- **Three-Stage XOR Swap (Lemma 5.7 (`lem:walsh-involutions`)):**
`x ← x ⊕ y`, `y ← y ⊕ x`, `x ← x ⊕ y` swaps `(x, y)` to `(y, x)` for all `x y : Bool`. -/
theorem xor_swap_three_stage_correct (x y : Bool) :
    xorSwapThreeStage x y = (y, x) := by
  cases x <;> cases y <;> rfl

/-- **Two-Involution Cycle Decomposition (Lemma 5.7 (`lem:walsh-involutions`)):**
On a cycle `0 ↦ 1 ↦ … ↦ n - 1 ↦ 0` of length `n > 0`, the reflections
`I₀(j) = (n - j % n) % n` and `I₁(j) = (n + 1 - j % n) % n` are involutions on `[0, n)` whose
composition `I₁ (I₀ j)` equals `(j + 1) % n`. -/
theorem cycle_two_involutions (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    let i0 := fun k => (n - k % n) % n
    let i1 := fun k => (n + 1 - k % n) % n
    i0 (i0 j) = j ∧ i1 (i1 j) = j ∧ i1 (i0 j) = (j + 1) % n := by
  intro i0 i1
  have hjn : j % n = j := Nat.mod_eq_of_lt hj
  rcases Decidable.eq_or_ne n 1 with rfl | hn1
  · have hj0 : j = 0 := by omega
    subst hj0
    decide
  · have hn2 : 2 ≤ n := by omega
    have h_n_plus_1 : (n + 1) % n = 1 := by
      rw [Nat.add_comm, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hn2
    have h_one_mod : 1 % n = 1 := Nat.mod_eq_of_lt hn2
    refine ⟨?_, ?_, ?_⟩
    · dsimp [i0]
      rw [hjn]
      rcases Decidable.eq_or_ne j 0 with rfl | hj0
      · simp
      · have hnj : (n - j) % n = n - j := Nat.mod_eq_of_lt (by omega)
        rw [hnj, hnj]
        have : n - (n - j) = j := by omega
        rw [this, hjn]
    · dsimp [i1]
      rw [hjn]
      rcases Decidable.eq_or_ne j 0 with rfl | hj0
      · simp only [Nat.sub_zero, h_n_plus_1, h_one_mod, Nat.add_sub_cancel, Nat.mod_self]
      · rcases Decidable.eq_or_ne j 1 with rfl | hj1
        · simp only [Nat.add_sub_cancel, Nat.mod_self, Nat.zero_mod, Nat.sub_zero, h_n_plus_1]
        · have hnj : (n + 1 - j) % n = n + 1 - j := Nat.mod_eq_of_lt (by omega)
          rw [hnj, hnj]
          have : n + 1 - (n + 1 - j) = j := by omega
          rw [this, hjn]
    · dsimp [i0, i1]
      rw [hjn]
      rcases Decidable.eq_or_ne j 0 with rfl | hj0
      · simp only [Nat.sub_zero, Nat.mod_self, Nat.zero_mod, Nat.zero_add, h_n_plus_1, h_one_mod]
      · have hnj : (n - j) % n = n - j := Nat.mod_eq_of_lt (by omega)
        rw [hnj, hnj]
        have : n + 1 - (n - j) = j + 1 := by omega
        rw [this]

/-- **Slice Count Bound (`eq:walsh-slices`, Theorem 5.8 (`thm:positional-perm`)):**
With `J = m₀ / K` chunks grouped into `⌈J / d⌉ = (J + d - 1) / d` groups of at most `d` chunks,
the total number of slices `K * ((J + d - 1) / d)` is at most `m₀ / d + K`. -/
theorem walsh_slice_count_le (m₀ K d : ℕ) (hK : 0 < K) (hd : 0 < d) :
    let J := m₀ / K
    K * ((J + d - 1) / d) ≤ m₀ / d + K := by
  intro J
  have _ := hK
  have h1 : (J + d - 1) / d ≤ (J + d) / d := Nat.div_le_div_right (Nat.sub_le (J + d) 1)
  have h2 : (J + d) / d = J / d + 1 := Nat.add_div_right J hd
  have h3 : J / d = (m₀ / d) / K := by
    dsimp [J]
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
  have h4 : K * (J / d) ≤ m₀ / d := by
    rw [h3]
    exact Nat.mul_div_le (m₀ / d) K
  calc K * ((J + d - 1) / d)
      ≤ K * ((J + d) / d) := Nat.mul_le_mul_left K h1
    _ = K * (J / d + 1) := by rw [h2]
    _ = K * (J / d) + K := by ring
    _ ≤ m₀ / d + K := Nat.add_le_add_right h4 K

end SubNLogN.S3
