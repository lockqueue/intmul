import WP.W9h.Loop

/-!
# WP.W9h.RecVal — the carry pass and Horner evaluation behind `W9_reconstruct`

The machine reconstructs `Σ c_j·2^(b·j)` in two linear passes:
1. `carryRun b c cs`: bottom-up, `t = c_j + carry`, low part `t % 2^b`, new carry `t / 2^b`;
2. `horner b los R`: top-down, `acc ↦ lo + acc·2^b`, starting from the final carry `R`.

`horner_carryRun`: the result is `c + evalRadix (2^b) cs`, i.e. `reconstructChunksTree b cs` for
`c = 0` (`reconstructChunksTree_eq_evalRadix`). The carries stay below `2^(wD+K0)` when every digit
has at most `wD` bits and there are at most `2^K0` digits (`carryRun_snd_le`, `bitLen_carry_le`).
-/

namespace WP.W9h

open TMFw TMFw.Contracts IntMul WP.W7k2

/-- Carry pass: low parts in digit order, and the final carry. -/
def carryRun (b : ℕ) : ℕ → List ℕ → List ℕ × ℕ
  | c, [] => ([], c)
  | c, x :: xs =>
    ((x + c) % 2 ^ b :: (carryRun b ((x + c) / 2 ^ b) xs).1, (carryRun b ((x + c) / 2 ^ b) xs).2)

/-- Horner evaluation: `lo₀ + 2^b·(lo₁ + 2^b·(… + 2^b·R))`. -/
def horner (b : ℕ) : List ℕ → ℕ → ℕ
  | [], R => R
  | lo :: los, R => lo + horner b los R * 2 ^ b

theorem horner_carryRun (b : ℕ) : ∀ (c : ℕ) (cs : List ℕ),
    horner b (carryRun b c cs).1 (carryRun b c cs).2 = c + evalRadix (2 ^ b) cs
  | c, [] => by simp [carryRun, horner, evalRadix]
  | c, x :: xs => by
    simp only [carryRun, horner]
    rw [horner_carryRun b ((x + c) / 2 ^ b) xs]
    simp only [evalRadix]
    have h := Nat.mod_add_div' (x + c) (2 ^ b)
    rw [Nat.add_mul, ← Nat.add_assoc, h]
    ring

/-- The reconstructed value. -/
theorem horner_carryRun_zero (b : ℕ) (cs : List ℕ) :
    horner b (carryRun b 0 cs).1 (carryRun b 0 cs).2 = reconstructChunksTree b cs := by
  rw [horner_carryRun, reconstructChunksTree_eq_evalRadix, Nat.zero_add]

theorem carryRun_append (b : ℕ) : ∀ (c : ℕ) (xs : List ℕ) (x : ℕ),
    carryRun b c (xs ++ [x]) = ((carryRun b c xs).1 ++ [(x + (carryRun b c xs).2) % 2 ^ b],
      (x + (carryRun b c xs).2) / 2 ^ b)
  | c, [], x => by simp [carryRun]
  | c, y :: ys, x => by
    simp only [List.cons_append, carryRun]
    rw [carryRun_append b _ ys x]

theorem length_carryRun (b : ℕ) : ∀ (c : ℕ) (xs : List ℕ), (carryRun b c xs).1.length = xs.length
  | c, [] => rfl
  | c, x :: xs => by simp [carryRun, length_carryRun b _ xs]

theorem carryRun_lt (b : ℕ) : ∀ (c : ℕ) (xs : List ℕ), ∀ lo ∈ (carryRun b c xs).1, lo < 2 ^ b
  | c, [], lo, h => by simp [carryRun] at h
  | c, x :: xs, lo, h => by
    simp only [carryRun, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.mod_lt _ (Nat.two_pow_pos b)
    · exact carryRun_lt b _ xs lo h

theorem carryRun_snd_le (b : ℕ) : ∀ (c : ℕ) (xs : List ℕ), (carryRun b c xs).2 ≤ c + xs.sum
  | c, [] => by simp [carryRun]
  | c, x :: xs => by
    simp only [carryRun, List.sum_cons]
    have h1 := carryRun_snd_le b ((x + c) / 2 ^ b) xs
    have h2 : (x + c) / 2 ^ b ≤ x + c := Nat.div_le_self _ _
    omega

/-- Digits of at most `wD` bits sum below `len·2^wD`. -/
theorem sum_lt_of_bitLen {wD : ℕ} : ∀ xs : List ℕ, (∀ c ∈ xs, bitLen c ≤ wD) →
    xs.sum + 1 ≤ xs.length * (2 ^ wD - 1) + 1
  | [], _ => by simp
  | x :: xs, h => by
    have h1 := sum_lt_of_bitLen xs (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have h2 : x < 2 ^ wD :=
      lt_of_lt_of_le (lt_two_pow_bitLen x)
        (Nat.pow_le_pow_right (by norm_num) (h x (List.mem_cons_self ..)))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- A sum of at most `2^K0` digits of at most `wD` bits has at most `wD + K0` bits. -/
theorem bitLen_sum_le {wD K0 : ℕ} (xs : List ℕ) (h : ∀ c ∈ xs, bitLen c ≤ wD)
    (hlen : xs.length ≤ 2 ^ K0) {s : ℕ} (hs : s ≤ xs.sum) : bitLen s ≤ wD + K0 := by
  apply bitLen_le_of_lt
  have h1 := sum_lt_of_bitLen xs h
  have h2 : xs.length * (2 ^ wD - 1) ≤ 2 ^ K0 * (2 ^ wD - 1) := Nat.mul_le_mul_right _ hlen
  have h3 : 2 ^ K0 * (2 ^ wD - 1) < 2 ^ K0 * 2 ^ wD :=
    Nat.mul_lt_mul_of_pos_left (by have := Nat.two_pow_pos wD; omega) (Nat.two_pow_pos K0)
  rw [Nat.pow_add, Nat.mul_comm (2 ^ wD)]
  omega

#assert_std_axioms horner_carryRun horner_carryRun_zero carryRun_append length_carryRun carryRun_lt
  carryRun_snd_le sum_lt_of_bitLen bitLen_sum_le

end WP.W9h
