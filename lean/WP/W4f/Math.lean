import Contracts.Machine.W4
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# WP.W4f.Math — arithmetic of the bitwise Hensel lift

* `addBits s u c`: the machine's in-place addition: the sum bits of `s + u + c`, truncated to `|s|`
  bits (missing bits of `u` read as `0`). `addBits_dvd`: `2^|s| ∣ (s + u + c) − sum`.
* `hensel_step_false` / `hensel_step_true`: one step of the bitwise lift for `a = 2·u2 − 1`, with the
  invariant `2^L ∣ a·h + s` (`h` = output bits, `s` = the `L`-bit residual).
* `newton_dvd`: the snapshot's Newton iteration satisfies `2^min(m, 2^s) ∣ a·iter_s − 1`.
* `factor_spec`, `eq_of_inv`: the snapshot factor is an inverse of `a` mod `2^k` below `2^k`, and
  such inverses are unique; `hensel_correct` combines them.
* `length_encodeNat_le`, `bitsVal_lt`, `bitsVal_replicate_true`: size facts (`bitLen k ≤ k`
  bounds the counter work of the unary expansion).
-/

namespace WP.W4f

open TMFw TMFw.Contracts Computability

/-! ## Full adder -/

/-- Sum bit of three bits. -/
def xor3 (a b c : Bool) : Bool := xor (xor a b) c

/-- Carry (majority) of three bits. -/
def maj3 (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem toNat_add3 (a b c : Bool) :
    a.toNat + b.toNat + c.toNat = (xor3 a b c).toNat + 2 * (maj3 a b c).toNat := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## In-place addition -/

/-- Sum bits (LSB first) of `s + u + c`, truncated to `|s|` bits; missing bits of `u` are `0`. -/
def addBits : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | b :: s, u, c => xor3 b (u.headD false) c :: addBits s u.tail (maj3 b (u.headD false) c)

theorem length_addBits : ∀ (s u : List Bool) (c : Bool), (addBits s u c).length = s.length
  | [], _, _ => rfl
  | b :: s, u, c => by
    simp only [addBits, List.length_cons, length_addBits s]

theorem bitsVal_headD_tail (u : List Bool) :
    bitsVal u = bitsVal u.tail + bitsVal u.tail + (u.headD false).toNat := by
  cases u <;> rfl

theorem addBits_dvd : ∀ (s u : List Bool) (c : Bool),
    (2 : ℤ) ^ s.length ∣
      (bitsVal s : ℤ) + (bitsVal u : ℤ) + (c.toNat : ℤ) - (bitsVal (addBits s u c) : ℤ)
  | [], u, c => by
    rw [List.length_nil, pow_zero]
    exact one_dvd _
  | b :: s, u, c => by
    obtain ⟨q, hq⟩ := addBits_dvd s u.tail (maj3 b (u.headD false) c)
    have h3 := toNat_add3 b (u.headD false) c
    have hu := bitsVal_headD_tail u
    refine ⟨q, ?_⟩
    have e : (2 : ℤ) ^ (b :: s).length * q = 2 * ((2 : ℤ) ^ s.length * q) := by
      rw [List.length_cons, pow_succ]
      ring
    rw [e, ← hq]
    simp only [addBits, bitsVal_cons, Nat.cast_add]
    omega

/-! ## The bitwise Hensel step (`a = 2·u2 − 1`) -/

theorem hensel_step_false (u2 : ℕ) (s h : List Bool) (L : ℕ)
    (ih : (2 : ℤ) ^ L ∣ (2 * (u2 : ℤ) - 1) * (bitsVal h : ℤ) + (bitsVal s : ℤ)) :
    (2 : ℤ) ^ (L + 1) ∣
      (2 * (u2 : ℤ) - 1) * (bitsVal (false :: h) : ℤ) + (bitsVal (false :: s) : ℤ) := by
  obtain ⟨q, hq⟩ := ih
  refine ⟨q, ?_⟩
  simp only [bitsVal_cons, Bool.toNat_false, Nat.cast_add, Nat.cast_zero]
  rw [pow_succ]
  linear_combination 2 * hq

theorem hensel_step_true (u2 : ℕ) (s h : List Bool) (L : ℕ) (hL : s.length = L)
    (ih : (2 : ℤ) ^ L ∣ (2 * (u2 : ℤ) - 1) * (bitsVal h : ℤ) +
      (bitsVal (addBits s (encodeNat u2) false) : ℤ)) :
    (2 : ℤ) ^ (L + 1) ∣
      (2 * (u2 : ℤ) - 1) * (bitsVal (true :: h) : ℤ) + (bitsVal (true :: s) : ℤ) := by
  obtain ⟨q, hq⟩ := ih
  obtain ⟨r, hr⟩ := addBits_dvd s (encodeNat u2) false
  rw [hL, bitsVal_encodeNat] at hr
  refine ⟨q + r, ?_⟩
  simp only [bitsVal_cons, Bool.toNat_true, Bool.toNat_false, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero] at hr ⊢
  rw [pow_succ]
  linear_combination 2 * hq + 2 * hr

/-! ## The snapshot's Newton iteration -/

theorem min_two_pow_succ_le (m s : ℕ) :
    min m (2 ^ (s + 1)) ≤ min m (2 ^ s) + min m (2 ^ s) := by
  rw [pow_succ]
  omega

theorem newton_dvd (m : ℕ) (a : ℤ) (ha : (2 : ℤ) ∣ a - 1) :
    ∀ s, (2 : ℤ) ^ min m (2 ^ s) ∣ a * oddModInvPow2Iter m a s - 1
  | 0 => by
    show (2 : ℤ) ^ min m (2 ^ 0) ∣ a * 1 - 1
    rw [mul_one]
    refine (pow_dvd_pow 2 (by simp : min m (2 ^ 0) ≤ 1)).trans ?_
    rw [pow_one]
    exact ha
  | s + 1 => by
    have ih := newton_dvd m a ha s
    show (2 : ℤ) ^ min m (2 ^ (s + 1)) ∣
      a * (oddModInvPow2Iter m a s * (2 - a * oddModInvPow2Iter m a s) % ((2 ^ m : ℕ) : ℤ)) - 1
    generalize oddModInvPow2Iter m a s = x at ih ⊢
    have hM : ((2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m := by simp
    rw [hM, Int.emod_def]
    have e : a * (x * (2 - a * x) - 2 ^ m * (x * (2 - a * x) / 2 ^ m)) - 1 =
        -((a * x - 1) * (a * x - 1)) - 2 ^ m * (a * (x * (2 - a * x) / 2 ^ m)) := by ring
    rw [e]
    refine dvd_sub (dvd_neg.mpr ?_) ?_
    · refine (pow_dvd_pow 2 (min_two_pow_succ_le m s)).trans ?_
      rw [pow_add]
      exact mul_dvd_mul ih ih
    · exact (pow_dvd_pow 2 (min_le_left _ _)).trans (dvd_mul_right _ _)

theorem newton_inv (m u2 : ℕ) :
    (2 : ℤ) ^ m ∣ (2 * (u2 : ℤ) - 1) * oddModInvPow2Iter m (2 * (u2 : ℤ) - 1) m - 1 := by
  have h := newton_dvd m (2 * (u2 : ℤ) - 1) ⟨(u2 : ℤ) - 1, by ring⟩ m
  rwa [min_eq_left Nat.lt_two_pow_self.le] at h

/-- The snapshot factor is an inverse of `2·u2 − 1` modulo `2^k`, below `2^k`. -/
theorem factor_spec (k u2 : ℕ) (hk : k ≠ 0) :
    (computableOddStrideFactor k u2 : ℤ) < 2 ^ k ∧
      (2 : ℤ) ^ k ∣ (2 * (u2 : ℤ) - 1) * (computableOddStrideFactor k u2 : ℤ) - 1 := by
  have hM : ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by simp
  have hMpos : (0 : ℤ) < 2 ^ k := pow_pos zero_lt_two k
  have hinv := newton_inv k u2
  unfold computableOddStrideFactor computableOddStrideInvPow2
  rw [if_neg hk]
  simp only [hM, Nat.cast_one, mul_one]
  generalize oddModInvPow2Iter k (2 * (u2 : ℤ) - 1) k = inv at hinv ⊢
  have h0 : 0 ≤ (inv % 2 ^ k + 2 ^ k) % 2 ^ k := Int.emod_nonneg _ hMpos.ne'
  have h1 : (inv % 2 ^ k + 2 ^ k) % 2 ^ k < 2 ^ k := Int.emod_lt_of_pos _ hMpos
  have hr : (inv % 2 ^ k + 2 ^ k) % 2 ^ k = inv - 2 ^ k * (inv / 2 ^ k) := by
    rw [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod, Int.emod_emod, Int.emod_def]
  rw [Int.toNat_of_nonneg h0]
  refine ⟨h1, ?_⟩
  rw [hr]
  have e : (2 * (u2 : ℤ) - 1) * (inv - 2 ^ k * (inv / 2 ^ k)) - 1 =
      ((2 * (u2 : ℤ) - 1) * inv - 1) - 2 ^ k * ((2 * (u2 : ℤ) - 1) * (inv / 2 ^ k)) := by ring
  rw [e]
  exact dvd_sub hinv (dvd_mul_right _ _)

/-! ## Uniqueness of inverses modulo `2^k` -/

theorem two_pow_dvd_of_mul (a : ℤ) (ha : (2 : ℤ) ∣ a - 1) :
    ∀ (k : ℕ) (d : ℤ), (2 : ℤ) ^ k ∣ a * d → (2 : ℤ) ^ k ∣ d
  | 0, d, _ => by
    rw [pow_zero]
    exact one_dvd d
  | k + 1, d, h => by
    have h2 : (2 : ℤ) ∣ a * d := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h
    have hd : (2 : ℤ) ∣ d := by
      have e : d = a * d - (a - 1) * d := by ring
      rw [e]
      exact dvd_sub h2 (dvd_mul_of_dvd_left ha d)
    obtain ⟨c, rfl⟩ := hd
    have h' : (2 : ℤ) ^ k ∣ a * c := by
      rw [pow_succ', show a * (2 * c) = 2 * (a * c) by ring] at h
      exact (mul_dvd_mul_iff_left two_ne_zero).mp h
    rw [pow_succ']
    exact mul_dvd_mul_left 2 (two_pow_dvd_of_mul a ha k c h')

theorem eq_of_inv (k u2 w1 w2 : ℕ) (h1 : (w1 : ℤ) < 2 ^ k) (h2 : (w2 : ℤ) < 2 ^ k)
    (d1 : (2 : ℤ) ^ k ∣ (2 * (u2 : ℤ) - 1) * w1 - 1)
    (d2 : (2 : ℤ) ^ k ∣ (2 * (u2 : ℤ) - 1) * w2 - 1) : w1 = w2 := by
  have hd : (2 : ℤ) ^ k ∣ (2 * (u2 : ℤ) - 1) * ((w1 : ℤ) - w2) := by
    have e : (2 * (u2 : ℤ) - 1) * ((w1 : ℤ) - w2) =
        ((2 * (u2 : ℤ) - 1) * w1 - 1) - ((2 * (u2 : ℤ) - 1) * w2 - 1) := by ring
    rw [e]
    exact dvd_sub d1 d2
  have hd' := two_pow_dvd_of_mul _ ⟨(u2 : ℤ) - 1, by ring⟩ k _ hd
  have e := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd')
  rw [Int.emod_eq_of_lt (by omega) h1, Int.emod_eq_of_lt (by omega) h2] at e
  exact_mod_cast e

/-! ## Size facts and the combined statement -/

theorem bitsVal_lt : ∀ l : List Bool, bitsVal l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have := bitsVal_lt l
    rw [bitsVal_cons, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

theorem bitsVal_replicate_true : ∀ k : ℕ, bitsVal (List.replicate k true) + 1 = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    have := bitsVal_replicate_true k
    simp only [List.replicate_succ, bitsVal_cons, Bool.toNat_true, pow_succ]
    omega

theorem length_encodeNat_le (n : ℕ) : (encodeNat n).length ≤ n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · by_cases hk : k = 0
    · subst hk
      simp [encodeNat_zero]
    · have := ih k (by omega)
      rw [two_mul, encodeNat_add, if_neg (fun h => hk ((encodeNat_eq_nil_iff k).1 h)),
        List.length_cons]
      omega
  · have := ih k (by omega)
    rw [two_mul, encodeNat_add_add_one, List.length_cons]
    omega

/-- **Correctness of the bitwise lift**: output bits `h` (`|h| = k ≥ 1`) satisfying the final
invariant `2^k ∣ a·h + (2^k − 1)` encode the snapshot factor. -/
theorem hensel_correct (k u2 : ℕ) (hk : k ≠ 0) (h : List Bool) (hlen : h.length = k)
    (hdvd : (2 : ℤ) ^ k ∣ (2 * (u2 : ℤ) - 1) * (bitsVal h : ℤ) +
      (bitsVal (List.replicate k true) : ℤ)) :
    bitsVal h = computableOddStrideFactor k u2 := by
  obtain ⟨hf1, hf2⟩ := factor_spec k u2 hk
  have hlt : (bitsVal h : ℤ) < 2 ^ k := by
    have := bitsVal_lt h
    rw [hlen] at this
    exact_mod_cast this
  have hrep : (bitsVal (List.replicate k true) : ℤ) = 2 ^ k - 1 := by
    have h0 := bitsVal_replicate_true k
    have h1 : ((bitsVal (List.replicate k true) + 1 : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by rw [h0]
    push_cast at h1
    exact eq_sub_of_add_eq h1
  have hw : (2 : ℤ) ^ k ∣ (2 * (u2 : ℤ) - 1) * (bitsVal h : ℤ) - 1 := by
    have e : (2 * (u2 : ℤ) - 1) * (bitsVal h : ℤ) - 1 =
        ((2 * (u2 : ℤ) - 1) * (bitsVal h : ℤ) + (bitsVal (List.replicate k true) : ℤ)) - 2 ^ k := by
      rw [hrep]
      ring
    rw [e]
    exact dvd_sub hdvd (dvd_refl _)
  exact eq_of_inv k u2 _ _ hlt hf1 hw hf2

#assert_std_axioms toNat_add3 length_addBits bitsVal_headD_tail addBits_dvd hensel_step_false
  hensel_step_true min_two_pow_succ_le newton_dvd newton_inv factor_spec two_pow_dvd_of_mul
  eq_of_inv bitsVal_lt bitsVal_replicate_true length_encodeNat_le hensel_correct

end WP.W4f
