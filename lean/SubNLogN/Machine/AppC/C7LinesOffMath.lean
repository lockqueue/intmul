/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7LinesAddr
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# Lemma A.9 offset routine: the value layer (`Machine/AppC/C7LinesOffMath.lean`)

The offset of a packed line (`lineOff ε par xF k1 k2 b c1 c2`, `C7LinesAddr.lean`) as the value of a
bit stream computed by one scan over the positions `p < b`, for `ε = ±1` and `k1 ≥ 1`
(`bitsVal_outs`; `lineOff_k1_zero` for `k1 = 0`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

* The scan keeps a distance counter `distR k1 k2 p` (`k2` at `p = 0`, reloaded with `k1 - 1` after a
  zero, else decremented); `distR p = 0` iff `p = k2 + i k1` (`distR_eq_zero_iff`).
* Position `p` is selected (`selB`) iff `distR p = 0` and `2 k1 - k2 ≤ b - p`, i.e. `p = k2 + i k1` with
  `(i + 2) k1 ≤ b` (`selB_iff`); its bit `sBit` is set iff moreover `x_p = 1` and `o_p = par`.
* `lineSum k1 k2 (b / k1) par x o ≡ Σ_{p<b} 2^p sBit p (mod 2^b)` (`lineSum_emod`).
* For `ε = -1` the scan emits the two's complement on the fly: after the first set bit every bit is
  inverted (`outBit`, `bitsVal_twos`).
-/

namespace SubNLogN.Machine.AppC.C7LinesOffAux

open TMFw TMFw.Contracts SubNLogN.Math.Networks SubNLogN.Machine.AppC.C7Aux
  SubNLogN.Machine.AppC.C7LinesAux

/-! ## The distance counter -/

/-- Distance counter of the scan: `k2` at position `0`; after a position where it is `0` it is
reloaded with `k1 - 1`, otherwise it decreases by one. -/
def distR (k1 k2 : ℕ) : ℕ → ℕ
  | 0 => k2
  | p + 1 => if distR k1 k2 p = 0 then k1 - 1 else distR k1 k2 p - 1

theorem distR_below (k1 k2 : ℕ) : ∀ p, p ≤ k2 → distR k1 k2 p = k2 - p
  | 0, _ => by simp [distR]
  | p + 1, h => by
    have ih := distR_below k1 k2 p (by omega)
    simp only [distR, ih]
    rw [if_neg (by omega)]
    omega

theorem succ_mod_eq {t k : ℕ} (hk : 1 ≤ k) :
    (t + 1) % k = if t % k + 1 = k then 0 else t % k + 1 := by
  have h := Nat.mod_add_div t k
  have hr := Nat.mod_lt t (by omega : 0 < k)
  split_ifs with h1
  · have e : t + 1 = k * (t / k + 1) := by rw [mul_add, mul_one]; omega
    rw [e, Nat.mul_mod_right]
  · have e : t + 1 = (t % k + 1) + k * (t / k) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem distR_above (k1 k2 : ℕ) (hk1 : 1 ≤ k1) :
    ∀ t, distR k1 k2 (k2 + t) = (k1 - t % k1) % k1
  | 0 => by
    rw [Nat.add_zero, distR_below k1 k2 k2 le_rfl, Nat.sub_self, Nat.zero_mod, Nat.sub_zero,
      Nat.mod_self]
  | t + 1 => by
    have ih := distR_above k1 k2 hk1 t
    rw [show k2 + (t + 1) = (k2 + t) + 1 by ring, distR, ih, succ_mod_eq hk1]
    have hr := Nat.mod_lt t (by omega : 0 < k1)
    by_cases h0 : t % k1 = 0
    · rw [h0, Nat.sub_zero, Nat.mod_self, if_pos rfl]
      by_cases h1 : 0 + 1 = k1
      · rw [if_pos h1, Nat.sub_zero, Nat.mod_self]
        omega
      · rw [if_neg h1, Nat.mod_eq_of_lt (by omega)]
    · have hne : (k1 - t % k1) % k1 = k1 - t % k1 := Nat.mod_eq_of_lt (by omega)
      rw [hne, if_neg (by omega)]
      by_cases h1 : t % k1 + 1 = k1
      · rw [if_pos h1, Nat.sub_zero, Nat.mod_self]
        omega
      · have e2 : (k1 - (t % k1 + 1)) % k1 = k1 - (t % k1 + 1) := Nat.mod_eq_of_lt (by omega)
        rw [if_neg h1, e2]
        omega

/-- The distance counter vanishes exactly at the candidate positions `k2 + i k1`. -/
theorem distR_eq_zero_iff (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (p : ℕ) :
    distR k1 k2 p = 0 ↔ k2 ≤ p ∧ (p - k2) % k1 = 0 := by
  by_cases hp : k2 ≤ p
  · obtain ⟨t, rfl⟩ : ∃ t, p = k2 + t := ⟨p - k2, by omega⟩
    rw [distR_above k1 k2 hk1 t, Nat.add_sub_cancel_left]
    have hr := Nat.mod_lt t (by omega : 0 < k1)
    constructor
    · intro h
      refine ⟨hp, ?_⟩
      by_contra hne
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    · intro h
      rw [h.2, Nat.sub_zero, Nat.mod_self]
  · rw [distR_below k1 k2 p (by omega)]
    omega

/-! ## Selected positions and the output bits -/

/-- Selection test of position `p` (for `p < b`; `b - p` is the scan counter). -/
def selB (k1 k2 b p : ℕ) : Bool := decide (distR k1 k2 p = 0 ∧ 2 * k1 - k2 ≤ b - p)

/-- The selected positions are `k2 + i k1` with `(i + 2) k1 ≤ b`. -/
theorem selB_iff {k1 : ℕ} (hk1 : 1 ≤ k1) (k2 b : ℕ) {p : ℕ} (hp : p < b) :
    selB k1 k2 b p = true ↔ ∃ i, i + 2 ≤ b / k1 ∧ p = k2 + i * k1 := by
  unfold selB
  rw [decide_eq_true_iff, distR_eq_zero_iff k1 k2 hk1]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨(p - k2) / k1, ?_, ?_⟩
    · rw [Nat.le_div_iff_mul_le (by omega)]
      have hd := Nat.div_add_mod (p - k2) k1
      rw [h2, Nat.add_zero] at hd
      have : (p - k2) / k1 * k1 = p - k2 := by rw [Nat.mul_comm]; exact hd
      rw [add_mul, this]
      omega
    · have hd := Nat.div_add_mod (p - k2) k1
      rw [h2, Nat.add_zero] at hd
      rw [Nat.mul_comm] at hd
      omega
  · rintro ⟨i, hi, rfl⟩
    rw [Nat.le_div_iff_mul_le (by omega), add_mul] at hi
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    rw [Nat.add_sub_cancel_left, Nat.mul_mod_left]

/-- Indicator bit of position `p`: selected, `x_p = 1` and `o_p = par`. -/
def sBit (k1 k2 b par x o p : ℕ) : Bool :=
  selB k1 k2 b p && decide (bitAt x p = 1 ∧ bitAt o p = par)

/-- Has some position before `p` its bit set? -/
def seenB (g : ℕ → Bool) (p : ℕ) : Bool := (List.range p).any g

/-- Output bit at position `p`; with `neg` the two's complement of the bit stream `g`. -/
def outBit (neg : Bool) (g : ℕ → Bool) (p : ℕ) : Bool := if neg && seenB g p then !g p else g p

/-! ## Values of bit streams -/

theorem bitsVal_map_range (g : ℕ → Bool) : ∀ n,
    bitsVal ((List.range n).map g) = ∑ p ∈ Finset.range n, 2 ^ p * (g p).toNat
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      SubNLogN.Machine.NatArith.bitsVal_append_single, List.length_map, List.length_range,
      bitsVal_map_range g n, Finset.sum_range_succ]

theorem bitsVal_eq_zero_iff : ∀ l : List Bool, bitsVal l = 0 ↔ ∀ b ∈ l, b = false
  | [] => by simp
  | b :: l => by
    rw [bitsVal_cons, List.forall_mem_cons, ← bitsVal_eq_zero_iff l]
    cases b <;> simp

theorem seenB_iff (g : ℕ → Bool) (n : ℕ) :
    seenB g n = true ↔ 0 < bitsVal ((List.range n).map g) := by
  unfold seenB
  rw [Nat.pos_iff_ne_zero, Ne, bitsVal_eq_zero_iff, List.any_eq_true]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨p, hp, hg⟩ h
    exact absurd (h p hp) (by rw [hg]; decide)
  · intro h
    by_contra hne
    exact h (fun p hp => by
      cases hq : g p
      · rfl
      · exact absurd ⟨p, hp, hq⟩ hne)

/-- **Two's complement on the fly.** -/
theorem bitsVal_twos (g : ℕ → Bool) : ∀ n,
    bitsVal ((List.range n).map (outBit true g)) =
      (2 ^ n - bitsVal ((List.range n).map g)) % 2 ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bitsVal_twos g n
    have hlt := SubNLogN.Machine.NatArith.bitsVal_lt_two_pow ((List.range n).map g)
    rw [List.length_map, List.length_range] at hlt
    have hseen := seenB_iff g n
    rw [List.range_succ, List.map_append, List.map_append, List.map_cons, List.map_cons,
      List.map_nil, List.map_nil, SubNLogN.Machine.NatArith.bitsVal_append_single,
      SubNLogN.Machine.NatArith.bitsVal_append_single]
    simp only [List.length_map, List.length_range]
    rw [ih]
    generalize hG : bitsVal ((List.range n).map g) = G at hlt hseen
    have hp : 0 < 2 ^ n := by positivity
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    unfold outBit
    by_cases hG0 : G = 0
    · have hs : seenB g n = false := by
        rcases h : seenB g n with _ | _
        · rfl
        · exact absurd (hseen.mp h) (by omega)
      rw [hs, hG0]
      simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.mod_self,
        zero_add]
      cases g n <;> simp [h2] <;> omega
    · have hs : seenB g n = true := hseen.mpr (by omega)
      rw [hs]
      simp only [Bool.and_self, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega : 2 ^ n - G < 2 ^ n)]
      cases g n
      · simp only [Bool.not_false, Bool.toNat_true, mul_one, Bool.toNat_false, mul_zero,
          add_zero]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [Bool.not_true, Bool.toNat_false, mul_zero, add_zero, Bool.toNat_true,
          mul_one]
        have e3 : (2 ^ (n + 1) - (G + 2 ^ n)) % 2 ^ (n + 1) = 2 ^ (n + 1) - (G + 2 ^ n) :=
          Nat.mod_eq_of_lt (by omega)
        rw [e3]
        omega

theorem outBit_false (g : ℕ → Bool) (p : ℕ) : outBit false g p = g p := by
  simp [outBit]

/-! ## The line sum modulo `2^b` -/

/-- Term of `lineSum` at position `p`. -/
def lineTerm (par x o p : ℕ) : ℤ :=
  (2 : ℤ) ^ p * (if bitAt x p = 1 ∧ bitAt o p = par then 1 else 0)

theorem lineSum_eq_sum (k1 k2 f par x o : ℕ) :
    lineSum k1 k2 f par x o = ∑ i ∈ Finset.range (f - 1), lineTerm par x o (k2 + i * k1) := rfl

/-- The terms of `lineSum` at positions `≥ b` vanish modulo `2^b`; the others are the selected
positions of the scan. -/
theorem lineSum_emod {k1 : ℕ} (hk1 : 1 ≤ k1) (k2 b par x o : ℕ) :
    lineSum k1 k2 (b / k1) par x o % (2 : ℤ) ^ b =
      (bitsVal ((List.range b).map (sBit k1 k2 b par x o)) : ℤ) := by
  classical
  have hlt := SubNLogN.Machine.NatArith.bitsVal_lt_two_pow
    ((List.range b).map (sBit k1 k2 b par x o))
  rw [List.length_map, List.length_range] at hlt
  rw [bitsVal_map_range] at hlt ⊢
  rw [lineSum_eq_sum, ← Finset.sum_filter_add_sum_filter_not _ (fun i => k2 + i * k1 < b)]
  -- the far terms are multiples of `2^b`
  have hdvd : (2 : ℤ) ^ b ∣ ∑ i ∈ (Finset.range (b / k1 - 1)).filter (fun i => ¬ k2 + i * k1 < b),
      lineTerm par x o (k2 + i * k1) := by
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
  obtain ⟨q, hq⟩ := hdvd
  -- the near terms are the selected positions
  have himg : ((Finset.range (b / k1 - 1)).filter (fun i => k2 + i * k1 < b)).image
      (fun i => k2 + i * k1) = (Finset.range b).filter (fun p => selB k1 k2 b p = true) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      exact ⟨hi2, (selB_iff hk1 k2 b hi2).mpr ⟨i, by omega, rfl⟩⟩
    · rintro ⟨hp, hs⟩
      obtain ⟨i, hi, rfl⟩ := (selB_iff hk1 k2 b hp).mp hs
      exact ⟨i, ⟨by omega, hp⟩, rfl⟩
  have hnear : ∑ i ∈ (Finset.range (b / k1 - 1)).filter (fun i => k2 + i * k1 < b),
      lineTerm par x o (k2 + i * k1) =
        ∑ p ∈ (Finset.range b).filter (fun p => selB k1 k2 b p = true), lineTerm par x o p := by
    rw [← himg, Finset.sum_image]
    intro i _ j _ hij
    have h' : i * k1 = j * k1 := Nat.add_left_cancel hij
    exact Nat.eq_of_mul_eq_mul_right (by omega) h'
  have hsel : ∑ p ∈ (Finset.range b).filter (fun p => selB k1 k2 b p = true), lineTerm par x o p =
      ((∑ p ∈ Finset.range b, 2 ^ p * (sBit k1 k2 b par x o p).toNat : ℕ) : ℤ) := by
    rw [Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    unfold sBit lineTerm
    by_cases hs : selB k1 k2 b p = true
    · rw [if_pos hs, hs, Bool.true_and]
      by_cases hc : bitAt x p = 1 ∧ bitAt o p = par
      · rw [if_pos hc, decide_eq_true hc]
        simp
      · rw [if_neg hc, decide_eq_false hc]
        simp
    · rw [if_neg hs]
      rw [Bool.not_eq_true] at hs
      rw [hs]
      simp
  rw [hnear, hsel, hq, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)

/-- **The scan computes the offset** (`k1 ≥ 1`, `ε = ±1`). -/
theorem bitsVal_outs {k1 : ℕ} (hk1 : 1 ≤ k1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (par : ℕ) (xF : Bool)
    (k2 b c1 c2 : ℕ) :
    bitsVal ((List.range b).map (outBit (decide (ε = -1))
      (sBit k1 k2 b par (if xF then c1 else c2) (if xF then c2 else c1)))) =
      lineOff ε par xF k1 k2 b c1 c2 := by
  unfold lineOff
  have he := lineSum_emod hk1 k2 b par (if xF then c1 else c2) (if xF then c2 else c1)
  generalize lineSum k1 k2 (b / k1) par (if xF then c1 else c2) (if xF then c2 else c1) = S at he
  generalize sBit k1 k2 b par (if xF then c1 else c2) (if xF then c2 else c1) = g at he ⊢
  rcases hε with rfl | rfl
  · rw [show decide ((1 : ℤ) = -1) = false by decide,
      show outBit false g = g from funext (outBit_false g), one_mul, he, Int.toNat_natCast]
  · rw [show decide ((-1 : ℤ) = -1) = true by decide, bitsVal_twos]
    have hlt := SubNLogN.Machine.NatArith.bitsVal_lt_two_pow ((List.range b).map g)
    rw [List.length_map, List.length_range] at hlt
    generalize bitsVal ((List.range b).map g) = G at he hlt
    have hm : S ≡ (G : ℤ) [ZMOD 2 ^ b] := by
      unfold Int.ModEq
      rw [he, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]
    have hm2 : -S ≡ (2 : ℤ) ^ b - G [ZMOD 2 ^ b] := by
      refine hm.neg.trans ?_
      rw [Int.modEq_iff_dvd]
      exact ⟨1, by ring⟩
    have h1 : (-1 * S) % (2 : ℤ) ^ b = (((2 ^ b - G) % 2 ^ b : ℕ) : ℤ) := by
      rw [Int.natCast_emod, Nat.cast_sub hlt.le]
      push_cast
      rw [neg_one_mul]
      exact hm2
    rw [h1, Int.toNat_natCast]

/-- With `k1 = 0` the offset is `0`. -/
theorem lineOff_k1_zero (ε : ℤ) (par : ℕ) (xF : Bool) (k2 b c1 c2 : ℕ) :
    lineOff ε par xF 0 k2 b c1 c2 = 0 := by
  simp [lineOff, lineSum]

/-! ## Reading the bits of a number -/

/-- The lowest bit of a nonzero number heads its LSB-first code. -/
theorem natSyms_div2 {m : ℕ} (hm : m ≠ 0) :
    natSyms m = Sym.bit (decide (m % 2 = 1)) :: natSyms (m / 2) := by
  have hd := Nat.div_add_mod m 2
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have hh : m / 2 ≠ 0 := by omega
    have e : m = m / 2 + m / 2 := by omega
    conv_lhs => rw [e]
    rw [SubNLogN.Machine.NatArith.natSyms_add_self hh, h]
    rfl
  · have e : m = m / 2 + m / 2 + 1 := by omega
    conv_lhs => rw [e]
    simp only [natSyms, encodeNat_add_add_one, List.map_cons, h]
    rfl

theorem bitAt_eq (x p : ℕ) : x / 2 ^ p % 2 = bitAt x p := rfl

theorem div_two_pow_succ (x p : ℕ) : x / 2 ^ p / 2 = x / 2 ^ (p + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

end SubNLogN.Machine.AppC.C7LinesOffAux
