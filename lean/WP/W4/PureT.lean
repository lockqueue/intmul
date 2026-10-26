import WP.W4.Pure
import Mathlib.Tactic.Ring

/-!
# WP.W4.PureT — transposition by repeated unshuffles or riffles

For `v` of length `2^a · 2^b` (row-major `2^a × 2^b`):
* `unsh^[b] v = transposeL (2^a) (2^b) v` (`unsh_iterate_eq_transposeL`);
* `riff^[a] v = transposeL (2^a) (2^b) v` (`riff_iterate_eq_transposeL`).

One step: `transposeL R (2C) v = transposeL (2R) C (unsh v)` and
`transposeL (2R) C v = transposeL R (2C) (riff v)`.
-/

namespace TMFw.W4

open TMFw.Contracts

variable {β : Type} [Inhabited β]

theorem length_transposeL (R C : ℕ) (v : List β) : (transposeL R C v).length = C * R := by
  simp [transposeL]

theorem getElem?_transposeL (R C : ℕ) (v : List β) (k : ℕ) (hk : k < C * R) :
    (transposeL R C v)[k]? = some (v.getD ((k % R) * C + k / R) default) := by
  unfold transposeL
  rw [List.getElem?_map, List.getElem?_range hk]
  rfl

theorem transposeL_one_right (v : List β) : transposeL v.length 1 v = v := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 1 * v.length
  · rw [getElem?_transposeL _ _ _ _ hk]
    have hk' : k < v.length := by omega
    rw [Nat.mod_eq_of_lt hk', Nat.div_eq_of_lt hk', Nat.mul_one, Nat.add_zero,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    rfl
  · rw [List.getElem?_eq_none (by rw [length_transposeL]; omega),
      List.getElem?_eq_none (by omega)]

theorem transposeL_one_left (v : List β) : transposeL 1 v.length v = v := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < v.length * 1
  · rw [getElem?_transposeL _ _ _ _ hk]
    have hk' : k < v.length := by omega
    rw [Nat.mod_one, Nat.div_one, Nat.zero_mul, Nat.zero_add,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    rfl
  · rw [List.getElem?_eq_none (by rw [length_transposeL]; omega),
      List.getElem?_eq_none (by omega)]

/-- One unshuffle step. -/
theorem transposeL_unsh (R C : ℕ) (v : List β) (hR : 0 < R) (hv : v.length = R * (C * 2)) :
    transposeL R (C * 2) v = transposeL (R * 2) C (unsh v) := by
  apply List.ext_getElem?
  intro k
  have h2 : R * (C * 2) = 2 * (R * C) := by ring
  by_cases hk : k < C * 2 * R
  · rw [getElem?_transposeL _ _ _ _ hk,
      getElem?_transposeL _ _ _ _ (show k < C * (R * 2) by rw [show C * (R * 2) = C * 2 * R by ring]; exact hk)]
    congr 1
    simp only [List.getD_eq_getElem?_getD]
    congr 1
    rw [Nat.mod_mul, ← Nat.div_div_eq_div_mul]
    have hm : k / R < C * 2 := (Nat.div_lt_iff_lt_mul hR).2 hk
    have ht : k % R < R := Nat.mod_lt _ hR
    generalize k % R = t at hm ht ⊢
    generalize k / R = m at hm ht ⊢
    have h1 : t * C + C ≤ R * C := by
      have := Nat.mul_le_mul_right C (show t + 1 ≤ R by omega)
      rwa [Nat.add_mul, Nat.one_mul] at this
    have e2 : (v.length + 1) / 2 = R * C := by rw [hv, h2]; omega
    have e3 : t * (C * 2) = 2 * (t * C) := by ring
    rcases Nat.mod_two_eq_zero_or_one m with he | he
    · rw [he, Nat.mul_zero, Nat.add_zero, getElem?_unsh_lo v _ (by rw [e2]; omega), e3]
      congr 1
      omega
    · have e1 : (t + R * 1) * C + m / 2 = (v.length + 1) / 2 + (t * C + m / 2) := by
        rw [e2]; ring
      rw [he, e1, getElem?_unsh_hi, e3]
      congr 1
      omega
  · rw [List.getElem?_eq_none (by rw [length_transposeL]; omega),
      List.getElem?_eq_none (by rw [length_transposeL]; rw [show C * (R * 2) = C * 2 * R by ring]; omega)]

/-- One riffle step. -/
theorem transposeL_riff (R C : ℕ) (v : List β) (hR : 0 < R) (hv : v.length = R * 2 * C) :
    transposeL (R * 2) C v = transposeL R (C * 2) (riff v) := by
  apply List.ext_getElem?
  intro k
  have h2 : R * 2 * C = 2 * (R * C) := by ring
  have heven : v.length % 2 = 0 := by rw [hv, h2]; omega
  have hhalf : v.length / 2 = R * C := by rw [hv, h2]; omega
  by_cases hk : k < C * (R * 2)
  · rw [getElem?_transposeL _ _ _ _ hk,
      getElem?_transposeL _ _ _ _ (show k < C * 2 * R by rw [show C * 2 * R = C * (R * 2) by ring]; exact hk)]
    congr 1
    simp only [List.getD_eq_getElem?_getD]
    congr 1
    rw [Nat.mod_mul, ← Nat.div_div_eq_div_mul]
    have hm : k / R < C * 2 := (Nat.div_lt_iff_lt_mul hR).2 (by
      rw [show C * 2 * R = C * (R * 2) by ring]; exact hk)
    have ht : k % R < R := Nat.mod_lt _ hR
    generalize k % R = t at hm ht ⊢
    generalize k / R = m at hm ht ⊢
    have h1 : t * C + C ≤ R * C := by
      have := Nat.mul_le_mul_right C (show t + 1 ≤ R by omega)
      rwa [Nat.add_mul, Nat.one_mul] at this
    have e3 : t * (C * 2) = 2 * (t * C) := by ring
    rcases Nat.mod_two_eq_zero_or_one m with he | he
    · rw [he, Nat.mul_zero, Nat.add_zero,
        show t * (C * 2) + m = 2 * (t * C + m / 2) by rw [e3]; omega,
        getElem?_riff_even v heven _ (by rw [hhalf]; omega)]
    · rw [he, show t * (C * 2) + m = 2 * (t * C + m / 2) + 1 by rw [e3]; omega,
        getElem?_riff_odd v heven, hhalf]
      congr 1
      ring
  · rw [List.getElem?_eq_none (by rw [length_transposeL]; omega),
      List.getElem?_eq_none (by rw [length_transposeL]; rw [show C * 2 * R = C * (R * 2) by ring]; omega)]

/-- **Transposition by `b` unshuffles.** -/
theorem unsh_iterate_eq_transposeL : ∀ (b a : ℕ) (v : List β), v.length = 2 ^ a * 2 ^ b →
    unsh^[b] v = transposeL (2 ^ a) (2 ^ b) v
  | 0, a, v, hv => by
    rw [Function.iterate_zero, id, pow_zero]
    rw [pow_zero, Nat.mul_one] at hv
    rw [← hv, transposeL_one_right]
  | b + 1, a, v, hv => by
    rw [Function.iterate_succ_apply, unsh_iterate_eq_transposeL b (a + 1) (unsh v)
      (by rw [length_unsh, hv, pow_succ, pow_succ]; ring), pow_succ 2 a, pow_succ 2 b]
    exact (transposeL_unsh (2 ^ a) (2 ^ b) v (Nat.two_pow_pos a) (by rw [hv, pow_succ])).symm

/-- **Transposition by `a` riffles.** -/
theorem riff_iterate_eq_transposeL : ∀ (a b : ℕ) (v : List β), v.length = 2 ^ a * 2 ^ b →
    riff^[a] v = transposeL (2 ^ a) (2 ^ b) v
  | 0, b, v, hv => by
    rw [Function.iterate_zero, id, pow_zero]
    rw [pow_zero, Nat.one_mul] at hv
    rw [← hv, transposeL_one_left]
  | a + 1, b, v, hv => by
    have h2 : v.length = 2 * (2 ^ a * 2 ^ b) := by rw [hv, pow_succ]; ring
    have heven : v.length % 2 = 0 := by omega
    rw [Function.iterate_succ_apply, riff_iterate_eq_transposeL a (b + 1) (riff v)
      (by rw [length_riff v heven, h2, pow_succ]; ring), pow_succ 2 a, pow_succ 2 b]
    exact (transposeL_riff (2 ^ a) (2 ^ b) v (Nat.two_pow_pos a) (by rw [hv, pow_succ])).symm

/-! ## The record invariant -/

/-- `N` well-formed records of total size `L`. -/
def Good (N L : ℕ) (l : List (List Sym)) : Prop :=
  l.length = N ∧ l.flatten.length = L ∧ ∀ r ∈ l, RecOK r

theorem Good.of_perm {N L : ℕ} {l l' : List (List Sym)} (h : Good N L l) (hp : l'.Perm l) :
    Good N L l' :=
  ⟨hp.length_eq.trans h.1, (length_flatten_of_perm hp).trans h.2.1,
    fun r hr => h.2.2 r (hp.mem_iff.1 hr)⟩

theorem Good.unsh {N L : ℕ} {l : List (List Sym)} (h : Good N L l) : Good N L (unsh l) :=
  h.of_perm (perm_unsh l)

theorem Good.riff {N L : ℕ} {l : List (List Sym)} (h : Good N L l) (hN : N % 2 = 0) :
    Good N L (riff l) :=
  h.of_perm (perm_riff l (by rw [h.1]; exact hN))

#assert_std_axioms length_transposeL getElem?_transposeL transposeL_one_right transposeL_one_left
  transposeL_unsh transposeL_riff unsh_iterate_eq_transposeL riff_iterate_eq_transposeL
  Good.of_perm Good.unsh Good.riff

end TMFw.W4
