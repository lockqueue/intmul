/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Value
import SubNLogN.Machine.K1.Twos

/-!
# AR pure bit lemmas (`Arith/Pure.lean`): what the bit-serial passes compute

**Scope (honest summary).** Pure lemmas about `twosBits` fields and the bit-serial functions that
model the AR machine passes (`emitOut`, `discF`, `lastD`). Everything is proved (no `sorry`). The
peeling lemma `K1.twosBits_succ` comes from `SubNLogN/Machine/K1/Twos.lean`.

## Contents
* `twosBits_add`: `twosBits (a + b) z = twosBits a z ++ twosBits b (z / 2^a)` (floor division).
* `twosBits_ext`: when `q / 2^h ∈ {0, -1}` (`sgnI sg`), widening appends copies of the sign.
* `emitOut_twosBits`: the emit pass (bits of a buffer, then the sign, plus a carry) computes
  `twosBits n (q + c)`.
* `discF_snoc`, `any_twosBits`, `lastD_twosBits`: the discard pass computes the sticky information
  and the sign.
* `tdivPow_eq`, `rnePow_succ_eq`: the integer roundings as floor quotient plus a carry bit.
* `tdivPow_of_le`, `rnePow_of_le`: shifts by at least the width give `0`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## Integer helpers -/

/-- `z % (a·b) = z % a + a·((z / a) % b)` for positive `a`, `b` (floor division). -/
theorem emod_mul_eq (z a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    z % (a * b) = z % a + a * ((z / a) % b) := by
  have hA := Int.emod_add_mul_ediv z a
  have hB := Int.emod_add_mul_ediv (z / a) b
  have h0 := Int.emod_nonneg z ha.ne'
  have h1 := Int.emod_lt_of_pos z ha
  have h2 := Int.emod_nonneg (z / a) hb.ne'
  have h3 := Int.emod_lt_of_pos (z / a) hb
  have hab : 0 < a * b := mul_pos ha hb
  have key : z % a + a * ((z / a) % b) + a * b * ((z / a) / b) = z := by
    linear_combination hA + a * hB
  have hlt : z % a + a * ((z / a) % b) < a * b := by
    have : a * ((z / a) % b) ≤ a * (b - 1) := mul_le_mul_of_nonneg_left (by omega) ha.le
    nlinarith
  have hnn : 0 ≤ z % a + a * ((z / a) % b) := by positivity
  exact ((Int.ediv_emod_unique hab).2 ⟨key, hnn, hlt⟩).2

/-- The integer with all-`sg` infinite two's-complement expansion: `-1` or `0`. -/
def sgnI (sg : Bool) : ℤ := if sg then -1 else 0

/-- For `-2^k ≤ z < 2^k`, `z / 2^k` is `-1` or `0` according to the sign. -/
theorem ediv_pow_of_bounds {k : ℕ} {z : ℤ} (h1 : -(2 ^ k : ℤ) ≤ z) (h2 : z < 2 ^ k) :
    z / 2 ^ k = sgnI (decide (z < 0)) := by
  have hP : (0 : ℤ) < 2 ^ k := by positivity
  by_cases hneg : z < 0
  · simp only [hneg, decide_true, sgnI, if_true]
    exact ((Int.ediv_emod_unique hP).2
      ⟨(by ring : z + 2 ^ k + 2 ^ k * (-1) = z), by omega, by omega⟩).1
  · simp only [hneg, decide_false, sgnI, Bool.false_eq_true, if_false]
    exact ((Int.ediv_emod_unique hP).2 ⟨(by ring : z + 2 ^ k * 0 = z), by omega, by omega⟩).1

theorem pow_pred_mul_two {w : ℕ} (hw : 1 ≤ w) : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- For `z` fitting `w ≥ 1` bits, the bits from position `w - 1` on are all the sign. -/
theorem ediv_pow_pred_of_fits {w : ℕ} {z : ℤ} (hz : FitsTwos w z) :
    z / 2 ^ (w - 1) = sgnI (decide (z < 0)) :=
  ediv_pow_of_bounds hz.1 hz.2

theorem sgnI_emod_two (sg : Bool) : decide (sgnI sg % 2 = 1) = sg := by
  cases sg <;> decide

/-! ## Splitting fields -/

theorem twosBits_add (a b : ℕ) (z : ℤ) :
    twosBits (a + b) z = twosBits a z ++ twosBits b (z / 2 ^ a) := by
  induction a generalizing z with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, K1.twosBits_succ, ih, K1.twosBits_succ,
      List.cons_append, Int.ediv_ediv_of_nonneg (by norm_num), ← pow_succ']

theorem twosBits_one (z : ℤ) : twosBits 1 z = [decide (z % 2 = 1)] := by
  rw [K1.twosBits_succ, K1.twosBits_zero]

theorem twosBits_neg_one (k : ℕ) : twosBits k (-1) = List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [K1.twosBits_succ, List.replicate_succ, show (-1 : ℤ) / 2 = -1 by decide, ih]
    rfl

theorem twosBits_zero_val (k : ℕ) : twosBits k 0 = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [K1.twosBits_succ, List.replicate_succ, show (0 : ℤ) / 2 = 0 by decide, ih]
    rfl

/-- **Sign extension.** If the bits of `q` from position `h` on are all `sg`, widening the field
by `k` appends `k` copies of `sg`. -/
theorem twosBits_ext (h k : ℕ) (q : ℤ) (sg : Bool) (hq : q / 2 ^ h = sgnI sg) :
    twosBits (h + k) q = twosBits h q ++ List.replicate k sg := by
  rw [twosBits_add, hq]
  cases sg
  · simp [sgnI, twosBits_zero_val]
  · simp [sgnI, twosBits_neg_one]

/-- **Truncation of a field** to its low `n` bits. -/
theorem twosBits_take (n h : ℕ) (hn : n ≤ h) (q : ℤ) :
    (twosBits h q).take n = twosBits n q := by
  obtain ⟨k, rfl⟩ : ∃ k, h = n + k := ⟨h - n, by omega⟩
  rw [twosBits_add, List.take_left' (K1.length_twosBits n q)]

/-! ## The emit pass -/

/-- The emit pass: `n` output bits. Input bit `i` is `L[i]` while it exists and `sg` after it;
the output bit is input bit `xor` carry, and the new carry is input bit `&&` carry. -/
def emitOut : Bool → Bool → List Bool → ℕ → List Bool
  | _, _, _, 0 => []
  | c, sg, L, n + 1 => xor (L.headD sg) c :: emitOut (L.headD sg && c) sg L.tail n

theorem length_emitOut : ∀ (c sg : Bool) (L : List Bool) (n : ℕ), (emitOut c sg L n).length = n
  | _, _, _, 0 => rfl
  | c, sg, L, n + 1 => by simp only [emitOut, List.length_cons, length_emitOut]

theorem carry_step (q : ℤ) (c : Bool) :
    decide ((q + (c.toNat : ℤ)) % 2 = 1) = xor (decide (q % 2 = 1)) c ∧
    (q + (c.toNat : ℤ)) / 2 = q / 2 + ((decide (q % 2 = 1) && c).toNat : ℤ) := by
  rcases Int.emod_two_eq_zero_or_one q with h | h <;> cases c <;>
    simp only [h, Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one, add_zero,
      decide_true, decide_false, Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false,
      Bool.and_false, Bool.and_true, Bool.false_eq_true, true_and, and_true] <;>
    (first | (constructor <;> omega) | omega | (refine ⟨?_, ?_⟩ <;> simp <;> omega) | simp <;> omega)

/-- **The emit pass computes a carry addition.** If the bits of `q` from position `h` on are all
`sg`, then emitting `n` bits of `twosBits h q` (then `sg`) with carry `c` gives the `n`-bit field
of `q + c`. -/
theorem emitOut_twosBits : ∀ (n h : ℕ) (q : ℤ) (c sg : Bool), q / 2 ^ h = sgnI sg →
    emitOut c sg (twosBits h q) n = twosBits n (q + (c.toNat : ℤ))
  | 0, _, _, _, _, _ => rfl
  | n + 1, 0, q, c, sg, hq => by
    simp only [pow_zero, Int.ediv_one] at hq
    subst hq
    have ih := emitOut_twosBits n 0 (sgnI sg) (sg && c) sg (by simp)
    rw [K1.twosBits_zero] at ih
    rw [K1.twosBits_zero]
    simp only [emitOut, List.headD_nil, List.tail_nil]
    rw [ih, K1.twosBits_succ]
    congr 1
    · cases sg <;> cases c <;> decide
    · congr 1; cases sg <;> cases c <;> decide
  | n + 1, h + 1, q, c, sg, hq => by
    rw [K1.twosBits_succ h q]
    simp only [emitOut, List.headD_cons, List.tail_cons]
    have hq' : q / 2 / 2 ^ h = sgnI sg := by
      rw [Int.ediv_ediv_of_nonneg (by norm_num), ← pow_succ']; exact hq
    rw [emitOut_twosBits n h (q / 2) _ sg hq', K1.twosBits_succ n, (carry_step q c).1,
      (carry_step q c).2]

/-! ## The discard pass -/

/-- The discard pass on `(sticky, half)`: each discarded bit becomes the half bit, and the old half
bit joins the sticky bit. -/
def discF : Bool × Bool → List Bool → Bool × Bool
  | p, [] => p
  | (st, hf), b :: L => discF (st || hf, b) L

theorem discF_snoc : ∀ (st hf : Bool) (L : List Bool) (b : Bool),
    discF (st, hf) (L ++ [b]) = (st || hf || L.any id, b)
  | st, hf, [], b => by simp [discF]
  | st, hf, a :: L, b => by
    rw [List.cons_append, discF, discF_snoc]
    simp [Bool.or_assoc]

theorem discF_or : ∀ (st hf : Bool) (L : List Bool),
    ((discF (st, hf) L).1 || (discF (st, hf) L).2) = (st || hf || L.any id)
  | st, hf, [] => by simp [discF]
  | st, hf, a :: L => by
    rw [discF, discF_or]
    simp [Bool.or_assoc]

/-- The last bit of a list, with default `d` for the empty list. -/
def lastD : Bool → List Bool → Bool
  | d, [] => d
  | _, b :: L => lastD b L

theorem lastD_append : ∀ (d : Bool) (L M : List Bool), lastD d (L ++ M) = lastD (lastD d L) M
  | _, [], _ => rfl
  | _, b :: L, M => lastD_append b L M

/-- **The last bit of a field is the sign** (for `z` fitting `w ≥ 1` bits). -/
theorem lastD_twosBits {w : ℕ} {z : ℤ} (hz : FitsTwos w z) (hw : 1 ≤ w) (d : Bool) :
    lastD d (twosBits w z) = decide (z < 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [twosBits_add k 1, twosBits_one, lastD_append]
  show decide ((z / 2 ^ k) % 2 = 1) = decide (z < 0)
  have h := ediv_pow_pred_of_fits hz
  simp only [Nat.add_sub_cancel] at h
  rw [h, sgnI_emod_two]

/-- **The sticky information**: some bit of the low `k` bits is set iff `z % 2^k ≠ 0`. -/
theorem any_twosBits : ∀ (k : ℕ) (z : ℤ), (twosBits k z).any id = decide (z % 2 ^ k ≠ 0)
  | 0, z => by simp
  | k + 1, z => by
    rw [K1.twosBits_succ, List.any_cons, any_twosBits k (z / 2), pow_succ',
      emod_mul_eq z 2 (2 ^ k) (by norm_num) (by positivity)]
    have h0 := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
    have h2 := Int.emod_nonneg (z / 2) (by positivity : (2 : ℤ) ^ k ≠ 0)
    rw [Bool.eq_iff_iff]
    simp only [id, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
    omega

/-! ## The integer roundings as floor quotient plus a carry -/

/-- **Truncation toward zero** is the floor quotient plus one exactly when `z < 0` and the
discarded bits are not all zero. -/
theorem tdivPow_eq (z : ℤ) (s : ℕ) :
    tdivPow z s = z / 2 ^ s + (if z < 0 ∧ z % 2 ^ s ≠ 0 then 1 else 0) := by
  have hpos : (0 : ℤ) < 2 ^ s := by positivity
  unfold tdivPow
  rw [Int.tdiv_eq_ediv, Int.sign_eq_one_of_pos hpos]
  congr 1
  by_cases h1 : 0 ≤ z
  · rw [if_pos (Or.inl h1), if_neg (by omega)]
  · by_cases h2 : z % 2 ^ s = 0
    · rw [if_pos (Or.inr (Int.dvd_of_emod_eq_zero h2)), if_neg (fun h => h.2 h2)]
    · rw [if_neg (by
          rintro (h | h)
          · exact h1 h
          · exact h2 (Int.emod_eq_zero_of_dvd h)), if_pos ⟨by omega, h2⟩]

theorem rnePow_zero (z : ℤ) : rnePow z 0 = z := by
  unfold rnePow
  simp

private theorem rne_aux (Q u m e : ℤ) (_hm : 0 < m) (hu0 : 0 ≤ u) (hu1 : u < m)
    (he : e = 0 ∨ e = 1) (hq : Q % 2 = 0 ∨ Q % 2 = 1) :
    (if 2 * (u + m * e) < 2 * m then Q else if 2 * m < 2 * (u + m * e) then Q + 1
      else if Q % 2 = 0 then Q else Q + 1) =
    Q + (if e = 1 ∧ (u ≠ 0 ∨ Q % 2 = 1) then 1 else 0) := by
  rcases he with rfl | rfl <;> simp only [mul_zero, mul_one, add_zero] <;> split_ifs <;>
    simp_all <;> omega

/-- **Nearest rounding, ties to even** by `2^(t+1)`: the floor quotient plus one exactly when the
half bit (bit `t`) is set and either a lower bit is set or the quotient is odd. -/
theorem rnePow_succ_eq (z : ℤ) (t : ℕ) :
    rnePow z (t + 1) = z / 2 ^ (t + 1) +
      (if (z / 2 ^ t) % 2 = 1 ∧ (z % 2 ^ t ≠ 0 ∨ (z / 2 ^ (t + 1)) % 2 = 1) then 1 else 0) := by
  have hm : (0 : ℤ) < 2 ^ t := by positivity
  have hr : z % 2 ^ (t + 1) = z % 2 ^ t + 2 ^ t * ((z / 2 ^ t) % 2) := by
    rw [pow_succ]; exact emod_mul_eq z (2 ^ t) 2 hm (by norm_num)
  have hu0 := Int.emod_nonneg z hm.ne'
  have hu1 := Int.emod_lt_of_pos z hm
  have he := Int.emod_two_eq_zero_or_one (z / 2 ^ t)
  unfold rnePow
  rw [hr, pow_succ']
  exact rne_aux (z / (2 * 2 ^ t)) (z % 2 ^ t) (2 ^ t) (z / 2 ^ t % 2) hm hu0 hu1 he
    (Int.emod_two_eq_zero_or_one _)

theorem rhuPow_zero (z : ℤ) : rhuPow z 0 = z := by
  unfold rhuPow
  simp

/-- **Nearest rounding, ties toward `+∞`** by `2^(t+1)`: the floor quotient plus the half bit
(bit `t`). -/
theorem rhuPow_succ_eq (z : ℤ) (t : ℕ) :
    rhuPow z (t + 1) = z / 2 ^ (t + 1) + (if (z / 2 ^ t) % 2 = 1 then 1 else 0) := by
  have hm : (0 : ℤ) < 2 ^ t := by positivity
  have hr : z % 2 ^ (t + 1) = z % 2 ^ t + 2 ^ t * ((z / 2 ^ t) % 2) := by
    rw [pow_succ]; exact emod_mul_eq z (2 ^ t) 2 hm (by norm_num)
  have hu0 := Int.emod_nonneg z hm.ne'
  have hu1 := Int.emod_lt_of_pos z hm
  have he := Int.emod_two_eq_zero_or_one (z / 2 ^ t)
  have hz := Int.emod_add_mul_ediv z (2 ^ (t + 1))
  unfold rhuPow
  have h2 : (2 : ℤ) ^ (t + 1) / 2 = 2 ^ t := by rw [pow_succ]; simp
  rw [h2]
  rw [hr] at hz
  have hP : (2 : ℤ) ^ (t + 1) = 2 * 2 ^ t := pow_succ' 2 t
  rw [hP] at hz ⊢
  generalize z / (2 * 2 ^ t) = Q at hz ⊢
  generalize z / 2 ^ t % 2 = e at he hz ⊢
  generalize z % 2 ^ t = u at hu0 hu1 hz
  generalize (2 : ℤ) ^ t = m at hm hu0 hu1 hz ⊢
  have hzq : z + m = (u + m * e + m) + 2 * m * Q := by linear_combination -hz
  rw [hzq, Int.add_mul_ediv_left _ _ (by omega)]
  rcases he with rfl | rfl
  · rw [if_neg (by omega)]
    have : (u + m * 0 + m) / (2 * m) = 0 := by
      apply Int.ediv_eq_zero_of_lt <;> nlinarith
    rw [this]; ring
  · rw [if_pos rfl]
    have : (u + m * 1 + m) / (2 * m) = 1 :=
      ((Int.ediv_emod_unique (by omega)).2 ⟨(by ring : u + 2 * m * 1 = u + m * 1 + m), hu0,
        by omega⟩).1
    rw [this]; ring

/-- Truncation by at least the width gives `0`. -/
theorem tdivPow_of_le {w s : ℕ} {z : ℤ} (hz : FitsTwos w z) (hw : 1 ≤ w) (hs : w ≤ s) :
    tdivPow z s = 0 := by
  have hP : (0 : ℤ) < 2 ^ s := by positivity
  have hQ : (2 : ℤ) ^ (w - 1) * 2 ≤ 2 ^ s := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨h1, h2⟩ := hz
  rw [tdivPow_eq]
  by_cases hneg : z < 0
  · have hd := (Int.ediv_emod_unique hP).2
      ⟨(by ring : z + 2 ^ s + 2 ^ s * (-1) = z), by omega, by omega⟩
    rw [hd.1, hd.2, if_pos ⟨hneg, by omega⟩]
    norm_num
  · have hd := (Int.ediv_emod_unique hP).2 ⟨(by ring : z + 2 ^ s * 0 = z), by omega, by omega⟩
    rw [hd.1, if_neg (fun h => hneg h.1)]
    norm_num

/-- Nearest rounding by at least the width gives `0`. -/
theorem rnePow_of_le {w s : ℕ} {z : ℤ} (hz : FitsTwos w z) (hw : 1 ≤ w) (hs : w ≤ s) :
    rnePow z s = 0 := by
  have hP : (0 : ℤ) < 2 ^ s := by positivity
  have hQ : (2 : ℤ) ^ (w - 1) * 2 ≤ 2 ^ s := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨h1, h2⟩ := hz
  unfold rnePow
  by_cases hneg : z < 0
  · have hd := (Int.ediv_emod_unique hP).2
      ⟨(by ring : z + 2 ^ s + 2 ^ s * (-1) = z), by omega, by omega⟩
    rw [hd.1, hd.2, if_neg (by omega)]
    split_ifs with h3 h4
    · norm_num
    · norm_num at h4
    · norm_num
  · have hd := (Int.ediv_emod_unique hP).2 ⟨(by ring : z + 2 ^ s * 0 = z), by omega, by omega⟩
    rw [hd.1, hd.2, if_pos (by omega)]

end SubNLogN.Machine.Arith
