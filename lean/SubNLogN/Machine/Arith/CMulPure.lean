/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Pure

/-!
# AR, products: pure bit lemmas (`Arith/CMulPure.lean`)

**Scope (honest summary).** Pure lemmas for the conversions between two's-complement fields and
sign-magnitude `natSyms` used by the product kernel. Everything is proved (no `sorry`).
* `bitsVal_bitsLE`, `bitsLE_bitsVal`, `twosBits_natCast`: fields of naturals are their binary
  digits, padded with zeros.
* `twosBits_map_not`: complementing a field is `x ↦ -1 - x`.
* `emitOut_len`: the emit pass over a full-length field is a carry addition (no sign condition).
* `emitOut_pad`, `emitOut_xor`: a masked emit pass computes `|x|` resp. `±p`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

theorem bitsLE_zero_val (n : ℕ) : bitsLE n 0 = List.replicate n false := by
  simp [bitsLE, Nat.zero_testBit, List.map_const']

theorem bitsVal_bitsLE : ∀ (w d : ℕ), bitsVal (bitsLE w d) = d % 2 ^ w
  | 0, d => by simp [bitsLE, Nat.mod_one]
  | w + 1, d => by
    rw [K1.bitsLE_succ, bitsVal_cons, bitsVal_bitsLE w (d / 2), Nat.testBit_zero, pow_succ',
      Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h] <;> omega

theorem bitsLE_bitsVal : ∀ (L : List Bool) (n : ℕ), L.length ≤ n →
    bitsLE n (bitsVal L) = L ++ List.replicate (n - L.length) false
  | [], n, _ => by simp [bitsLE_zero_val]
  | b :: L, n + 1, h => by
    have hd : bitsVal (b :: L) / 2 = bitsVal L := by
      simp only [bitsVal_cons]; cases b <;> simp <;> omega
    have ht : (bitsVal (b :: L)).testBit 0 = b := by
      simp only [bitsVal_cons, Nat.testBit_zero]; cases b <;> simp <;> omega
    rw [K1.bitsLE_succ, hd, ht, bitsLE_bitsVal L n (by simpa using h)]
    simp
  | _ :: _, 0, h => by simp at h

theorem twosBits_natCast {w p : ℕ} (h : p < 2 ^ w) :
    twosBits w (p : ℤ) = encodeNat p ++ List.replicate (w - bitLen p) false := by
  have hp : ((p : ℤ) % 2 ^ w) = p := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h)
  have hb : bitLen p ≤ w := WP.W9comp.bitLen_le_of_lt_two_pow h
  unfold twosBits
  rw [hp, Int.toNat_natCast]
  conv_lhs => rw [← bitsVal_encodeNat p]
  exact bitsLE_bitsVal (encodeNat p) w hb

theorem twosBits_map_not : ∀ (w : ℕ) (x : ℤ), (twosBits w x).map not = twosBits w (-1 - x)
  | 0, _ => rfl
  | w + 1, x => by
    rw [K1.twosBits_succ, K1.twosBits_succ, List.map_cons, twosBits_map_not w (x / 2)]
    have h1 : (-1 - x) / 2 = -1 - x / 2 := by omega
    rw [h1]
    congr 1
    rcases Int.emod_two_eq_zero_or_one x with h | h
    · have : (-1 - x) % 2 = 1 := by omega
      simp [h, this]
    · have : (-1 - x) % 2 = 0 := by omega
      simp [h, this]

/-- **The emit pass over a full-length field** computes the carry addition, with no condition on
the sign. -/
theorem emitOut_len : ∀ (n : ℕ) (q : ℤ) (c sg : Bool),
    emitOut c sg (twosBits n q) n = twosBits n (q + (c.toNat : ℤ))
  | 0, _, _, _ => rfl
  | n + 1, q, c, sg => by
    rw [K1.twosBits_succ n q]
    simp only [emitOut, List.headD_cons, List.tail_cons]
    rw [emitOut_len n (q / 2), K1.twosBits_succ n, (carry_step q c).1, (carry_step q c).2]

/-- Padding with the padding bit does not change the emit pass. -/
theorem emitOut_pad : ∀ (n : ℕ) (c pd : Bool) (L : List Bool) (k : ℕ),
    emitOut c pd L n = emitOut c pd (L ++ List.replicate k pd) n
  | 0, _, _, _, _ => rfl
  | n + 1, c, pd, [], k => by
    rcases k with _ | k
    · rfl
    · simp only [emitOut, List.nil_append, List.headD_nil, List.tail_nil, List.replicate_succ,
        List.headD_cons, List.tail_cons]
      rw [emitOut_pad n _ pd [] k]
      rfl
  | n + 1, c, pd, b :: L, k => by
    simp only [emitOut, List.cons_append, List.headD_cons, List.tail_cons]
    rw [emitOut_pad n _ pd L k]

/-- **The masked emit pass**: mask `m` and carry `m` over a field give `x` or `-x`. -/
theorem emitOut_xor (w : ℕ) (x : ℤ) (m pd : Bool) :
    emitOut m pd ((twosBits w x).map (xor m)) w = twosBits w (if m then -x else x) := by
  cases m
  · have h0 : (xor false : Bool → Bool) = id := by funext b; cases b <;> rfl
    rw [h0, List.map_id, emitOut_len]
    simp
  · have h1 : (xor true : Bool → Bool) = not := by funext b; cases b <;> rfl
    rw [h1, twosBits_map_not, emitOut_len]
    simp only [Bool.toNat_true, Nat.cast_one, if_true]
    congr 1
    ring


theorem bitsVal_append_zeros : ∀ (L : List Bool) (k : ℕ),
    bitsVal (L ++ List.replicate k false) = bitsVal L
  | [], k => by
    induction k with
    | zero => rfl
    | succ k ih =>
      have h0 : bitsVal ([] : List Bool) = 0 := rfl
      simp only [List.nil_append, List.replicate_succ, bitsVal_cons, Bool.toNat_false, h0] at ih ⊢
      omega
  | b :: L, k => by
    simp only [List.cons_append, bitsVal_cons, bitsVal_append_zeros L k]

/-- The magnitude field of `x`, stripped of high zeros, is `encodeNat |x|`. -/
theorem abs_strip {w : ℕ} {x : ℤ} (hz : FitsTwos w x) (hw : 1 ≤ w) :
    (((twosBits w (x.natAbs : ℤ)).reverse.dropWhile (fun b => !b)).reverse) =
      encodeNat x.natAbs := by
  have hlt : x.natAbs < 2 ^ w := by
    obtain ⟨h1, h2⟩ := hz
    have hp : (2 : ℤ) ^ (w - 1) < 2 ^ w := pow_lt_pow_right₀ (by norm_num) (by omega)
    have : (x.natAbs : ℤ) < 2 ^ w := by
      rcases Int.natAbs_eq x with h | h <;> omega
    exact_mod_cast this
  rw [reverse_dropWhile_eq_encodeNat, List.reverse_reverse, twosBits_natCast hlt,
    bitsVal_append_zeros, bitsVal_encodeNat]

/-- The masked emit pass on a field gives its magnitude field. -/
theorem emitOut_abs {w : ℕ} (x : ℤ) (pd : Bool) :
    emitOut (decide (x < 0)) pd ((twosBits w x).map (xor (decide (x < 0)))) w =
      twosBits w (x.natAbs : ℤ) := by
  rw [emitOut_xor]
  congr 1
  by_cases h : x < 0
  · simp only [h, decide_true, if_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; omega

/-- The masked emit pass on a magnitude (padded with zeros) gives the signed field. -/
theorem emitOut_signed {W p : ℕ} (hp : p < 2 ^ W) (s : Bool) :
    emitOut s s ((encodeNat p).map (xor s)) W = twosBits W (if s then -(p : ℤ) else p) := by
  rw [emitOut_pad W s s ((encodeNat p).map (xor s)) (W - bitLen p)]
  have h : (encodeNat p).map (xor s) ++ List.replicate (W - bitLen p) s =
      (twosBits W (p : ℤ)).map (xor s) := by
    rw [twosBits_natCast hp, List.map_append, List.map_replicate]
    simp
  rw [h, emitOut_xor]

/-- Ripple addition of a field and a masked field. -/
theorem ripOut_signed (W : ℕ) (u v : ℤ) (sub : Bool) :
    K1.ripOut K1.addBit sub (twosBits W u) ((twosBits W v).map (xor sub)) =
      twosBits W (if sub then u - v else u + v) := by
  cases sub
  · have h0 : (xor false : Bool → Bool) = id := by funext b; cases b <;> rfl
    rw [h0, List.map_id, K1.ripOut_add]
    simp
  · have h1 : (xor true : Bool → Bool) = not := by funext b; cases b <;> rfl
    rw [h1, twosBits_map_not, K1.ripOut_twosBits K1.linBit_add]
    simp only [Bool.toNat_true, Nat.cast_one, if_true]
    congr 1
    ring

end SubNLogN.Machine.Arith
