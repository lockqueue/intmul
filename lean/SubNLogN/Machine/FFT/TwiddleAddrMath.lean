/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PhaseMath
import SubNLogN.Math.Walsh.IntForms.Address
import WP.W7k2.Arith

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrMath.lean`): pure facts for the twiddle address

**Scope (honest summary).** Pure (machine-free) lemmas, all proved (no `sorry`), that rewrite
the integer twiddle index `twJNat ℓ K a v n` (`Math/Walsh/IntForms/Address.lean:352`; Section 6.3,
`sec:direct-fft-twiddle`) into the form the routine computes:
* `npos`: the closed-form slot position `newPosNat` with `longCount`, `longRank` as parameters
  (`newPosNat_eq_npos`, by `rfl`); `bitN m n p ∈ {0,1}`: the address bit `addrBit m n p` as a
  number (`addrBit_iff`, `ite_addrBit`).
* `hsum f k v = ∑_{b ∈ [k,v)} f b·2^{b-k}`, the Horner value (`hsum_step`, `hsum_zero`,
  `hsum_lt`).
* `tmN`: the program's term of one axis; `twJNat_eq_tm`: `twJNat` is the sum of the terms mod
  `2^ℓ`.
* List facts for the header walk (`pkS`, `take_succ_ofFn`, `drop_ofFn`), and value bounds.
-/

namespace SubNLogN.Machine.FFT.TwAddr

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh

/-! ## 1. Positions and bits -/

/-- The slot position of `newPosNat` (`Address.lean:196`), with `L = longCount`,
`R = longRank i` as parameters and `b₀ = layoutB0 ℓ K = (ℓ-1) % K` unfolded. -/
def npos (ℓ K D L R i b : ℕ) : ℕ :=
  if b = ℓ - 1 then R
  else if b < (ℓ - 1) % K then L + ((ℓ - 1) % K - 1 - b) * D + i
  else L + (ℓ - 1) % K * D + (ℓ - 2 - b) / K * D * K + i * K + (ℓ - 2 - b) % K

theorem newPosNat_eq_npos {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (i : Fin D) (b : ℕ) :
    IntForms.newPosNat ℓ K a i b =
      npos ℓ K D (IntForms.longCount ℓ a) (IntForms.longRank ℓ a i) i b := rfl

/-- The address bit `addrBit m n p` as a number. -/
def bitN (m n p : ℕ) : ℕ := if p < m then n / 2 ^ (m - 1 - p) % 2 else 0

theorem bitN_le_one (m n p : ℕ) : bitN m n p ≤ 1 := by
  unfold bitN
  split_ifs <;> omega

theorem addrBit_iff (m n p : ℕ) : IntForms.addrBit m n p = true ↔ bitN m n p = 1 := by
  unfold IntForms.addrBit bitN
  by_cases h : p < m
  · rw [Nat.testBit_eq_decide_div_mod_eq]
    simp [h]
  · simp [h]

theorem ite_addrBit (m n p c : ℕ) :
    (if IntForms.addrBit m n p = true then c else 0) = bitN m n p * c := by
  have h1 := bitN_le_one m n p
  by_cases hb : IntForms.addrBit m n p = true
  · rw [if_pos hb, (addrBit_iff m n p).mp hb, one_mul]
  · have h2 : bitN m n p = 0 := by
      have := (addrBit_iff m n p).not.mp hb
      omega
    rw [if_neg hb, h2, zero_mul]

/-! ## 2. Horner values -/

/-- `∑_{b ∈ [k, v)} f b · 2^{b-k}`. -/
def hsum (f : ℕ → ℕ) (k v : ℕ) : ℕ := ∑ b ∈ Finset.Ico k v, f b * 2 ^ (b - k)

theorem hsum_self (f : ℕ → ℕ) (v : ℕ) : hsum f v v = 0 := by simp [hsum]

theorem hsum_step (f : ℕ → ℕ) {k v : ℕ} (hk : k < v) :
    hsum f k v = hsum f (k + 1) v * 2 + f k := by
  unfold hsum
  rw [Finset.sum_eq_sum_Ico_succ_bot hk, Nat.sub_self, pow_zero, mul_one, Finset.sum_mul]
  have e : ∑ b ∈ Finset.Ico (k + 1) v, f b * 2 ^ (b - k) =
      ∑ b ∈ Finset.Ico (k + 1) v, f b * 2 ^ (b - (k + 1)) * 2 := by
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := (Finset.mem_Ico.mp hb).1
    have e1 : b - k = (b - (k + 1)) + 1 := by omega
    rw [e1, pow_succ, mul_assoc]
  rw [e]
  ring

theorem hsum_zero (f : ℕ → ℕ) (v : ℕ) : hsum f 0 v = ∑ b ∈ Finset.range v, f b * 2 ^ b := by
  unfold hsum
  rw [Finset.range_eq_Ico]
  simp only [Nat.sub_zero]

theorem hsum_lt (f : ℕ → ℕ) (hf : ∀ b, f b ≤ 1) (v : ℕ) :
    ∀ d k, k + d = v → hsum f k v < 2 ^ d
  | 0, k, h => by
    subst h
    simp [hsum]
  | d + 1, k, h => by
    have hk : k < v := by omega
    rw [hsum_step f hk]
    have ih := hsum_lt f hf v d (k + 1) (by omega)
    have := hf k
    rw [pow_succ]
    omega

/-! ## 3. The term of one axis -/

/-- The routine's term for axis `i` (exponent `x = a_i`, long rank `R`): `0` unless `v < x` and
the bit at the slot `(i, v)` is set; otherwise the Horner value of the bits at the slots `(i, b)`,
`b < v`, shifted by `ℓ-1-v`. -/
def tmN (ℓ K D L m n v x R i : ℕ) : ℕ :=
  if v < x then
    (if bitN m n (npos ℓ K D L R i v) = 0 then 0
      else hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v))
  else 0

/-- The exponents as a total function on `ℕ`. -/
def aN {D : ℕ} (a : Fin D → ℕ) (i : ℕ) : ℕ := if h : i < D then a ⟨i, h⟩ else 0

/-- **`twJNat` is the sum of the routine's terms, mod `2^ℓ`.** -/
theorem twJNat_eq_tm {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v n : ℕ) :
    IntForms.twJNat ℓ K a v n = (∑ i ∈ Finset.range D, tmN ℓ K D (IntForms.longCount ℓ a)
      (addrBits a) n v (aN a i) (IntForms.longRank ℓ a i) i) % 2 ^ ℓ := by
  unfold IntForms.twJNat
  congr 1
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hai : aN a i = a i := by simp [aN, i.isLt]
  have hnp : ∀ b, IntForms.newPosNat ℓ K a i b =
      npos ℓ K D (IntForms.longCount ℓ a) (IntForms.longRank ℓ a i) i b := fun b => rfl
  have hsumeq : (∑ b ∈ Finset.range v,
      if IntForms.addrBit (addrBits a) n (IntForms.newPosNat ℓ K a i b) = true then 2 ^ b else 0) =
      hsum (fun b => bitN (addrBits a) n
        (npos ℓ K D (IntForms.longCount ℓ a) (IntForms.longRank ℓ a i) i b)) 0 v := by
    rw [hsum_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ite_addrBit, hnp]
  unfold tmN
  rw [hai, hsumeq]
  by_cases hv : v < a i
  · have h1 := bitN_le_one (addrBits a) n
      (npos ℓ K D (IntForms.longCount ℓ a) (IntForms.longRank ℓ a i) i v)
    by_cases hb : bitN (addrBits a) n
        (npos ℓ K D (IntForms.longCount ℓ a) (IntForms.longRank ℓ a i) i v) = 0
    · have hf : ¬ (v < a i ∧
          IntForms.addrBit (addrBits a) n (IntForms.newPosNat ℓ K a i v) = true) := by
        rintro ⟨-, h⟩
        rw [addrBit_iff, hnp, hb] at h
        exact absurd h (by norm_num)
      rw [if_neg hf, if_pos hv, if_pos hb]
    · have ht : v < a i ∧
          IntForms.addrBit (addrBits a) n (IntForms.newPosNat ℓ K a i v) = true := by
        refine ⟨hv, ?_⟩
        rw [addrBit_iff, hnp]
        omega
      have e : ℓ - v - 1 = ℓ - 1 - v := by omega
      rw [if_pos ht, if_pos hv, if_neg hb, e]
      ring
  · rw [if_neg (fun h => hv h.1), if_neg hv]

/-! ## 4. The header walk -/

/-- Parked header fields, the most recently parked on top. -/
def pkS (l : List ℕ) : List Sym := l.reverse.flatMap (fun x => Sym.mark :: natSyms x)

theorem pkS_nil : pkS [] = [] := rfl

theorem pkS_append_one (l : List ℕ) (x : ℕ) :
    pkS (l ++ [x]) = Sym.mark :: (natSyms x ++ pkS l) := by
  simp [pkS]

theorem take_succ_ofFn {D : ℕ} (a : Fin D → ℕ) {k : ℕ} (hk : k < D) :
    (List.ofFn a).take (k + 1) = (List.ofFn a).take k ++ [aN a k] := by
  have hl : k < (List.ofFn a).length := by simpa using hk
  rw [List.take_add_one, List.getElem?_eq_getElem hl]
  simp [aN, hk]

theorem drop_ofFn {D : ℕ} (a : Fin D → ℕ) {k : ℕ} (hk : k < D) :
    (List.ofFn a).drop k = aN a k :: (List.ofFn a).drop (k + 1) := by
  have hl : k < (List.ofFn a).length := by simpa using hk
  rw [List.drop_eq_getElem_cons hl]
  simp [aN, hk]

theorem sum_take_succ {D : ℕ} (a : Fin D → ℕ) {k : ℕ} (hk : k < D) :
    ((List.ofFn a).take (k + 1)).sum = ((List.ofFn a).take k).sum + aN a k := by
  rw [take_succ_ofFn a hk, List.sum_append, List.sum_singleton]

theorem count_take_succ {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) {k : ℕ} (hk : k < D) :
    ((List.ofFn a).take (k + 1)).count ℓ =
      ((List.ofFn a).take k).count ℓ + (if aN a k = ℓ then 1 else 0) := by
  rw [take_succ_ofFn a hk, List.count_append]
  by_cases h : aN a k = ℓ
  · simp [h]
  · simp [h]

theorem take_ofFn_D {D : ℕ} (a : Fin D → ℕ) : (List.ofFn a).take D = List.ofFn a :=
  List.take_of_length_le (by simp)

theorem drop_ofFn_D {D : ℕ} (a : Fin D → ℕ) : (List.ofFn a).drop D = [] :=
  List.drop_of_length_le (by simp)

/-! ## 5. Bounds -/

theorem count_take_le {D : ℕ} (a : Fin D → ℕ) (ℓ k : ℕ) : ((List.ofFn a).take k).count ℓ ≤ D :=
  le_trans (List.count_le_length) (by simp)

theorem count_le {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) : (List.ofFn a).count ℓ ≤ D :=
  le_trans (List.count_le_length) (by simp)

theorem addrBits_ge {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    (ℓ - 1) * D ≤ addrBits a := by
  unfold addrBits
  rw [List.sum_ofFn]
  calc (ℓ - 1) * D = ∑ _i : Fin D, (ℓ - 1) := by simp [mul_comm]
    _ ≤ ∑ i : Fin D, a i := Finset.sum_le_sum fun i _ => by rcases ha i with h | h <;> omega

theorem aN_le {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (i : ℕ) :
    aN a i ≤ ℓ := by
  unfold aN
  split_ifs with h
  · rcases ha ⟨i, h⟩ with e | e <;> omega
  · omega

theorem npos_le {ℓ K D L R i b m : ℕ} (hK : 1 ≤ K) (hKl : K ≤ ℓ - 1) (hL : L ≤ D) (hR : R ≤ D)
    (hi : i < D) (hDm : (ℓ - 1) * D ≤ m) (hl2 : 2 ≤ ℓ) : npos ℓ K D L R i b ≤ 4 * m + ℓ := by
  have hD : D ≤ m := le_trans (Nat.le_mul_of_pos_left D (by omega)) hDm
  have hb0 : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have h2 : ((ℓ - 1) % K - 1 - b) * D ≤ m :=
    le_trans (Nat.mul_le_mul_right D (by omega)) hDm
  have h1 : (ℓ - 1) % K * D ≤ m := le_trans (Nat.mul_le_mul_right D (by omega)) hDm
  have h3 : (ℓ - 2 - b) / K * D * K ≤ m := by
    have e : (ℓ - 2 - b) / K * D * K = (ℓ - 2 - b) / K * K * D := by ring
    rw [e]
    exact le_trans (Nat.mul_le_mul_right D (le_trans (Nat.div_mul_le_self _ _) (by omega))) hDm
  have h4 : i * K ≤ m :=
    le_trans (Nat.mul_le_mul (le_of_lt hi) hKl) (by rw [mul_comm]; exact hDm)
  have h5 : (ℓ - 2 - b) % K < K := Nat.mod_lt _ (by omega)
  unfold npos
  split_ifs <;> omega

theorem tmN_lt {ℓ K D L m n v x R i : ℕ} (hv : v < ℓ) : tmN ℓ K D L m n v x R i < 2 ^ ℓ := by
  unfold tmN
  have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  split_ifs
  · exact hpos
  · have h1 := hsum_lt (fun b => bitN m n (npos ℓ K D L R i b)) (fun b => bitN_le_one _ _ _) v v
      0 (by omega)
    calc hsum (fun b => bitN m n (npos ℓ K D L R i b)) 0 v * 2 ^ (ℓ - 1 - v)
        < 2 ^ v * 2 ^ (ℓ - 1 - v) := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ (ℓ - 1) := by rw [← pow_add]; congr 1; omega
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exact hpos

theorem sum_Ico_le (f : ℕ → ℕ) (c i D : ℕ) (h : ∀ j, f j ≤ c) :
    ∑ j ∈ Finset.Ico i D, f j ≤ (D - i) * c := by
  calc ∑ j ∈ Finset.Ico i D, f j ≤ ∑ _j ∈ Finset.Ico i D, c := Finset.sum_le_sum fun j _ => h j
    _ = (D - i) * c := by simp [Nat.card_Ico]

theorem bitLen_le_of_le_mul {S D ℓ : ℕ} (hS : S ≤ D * 2 ^ ℓ) : bitLen S ≤ D + ℓ := by
  apply WP.W7k2.bitLen_le_of_lt
  calc S ≤ D * 2 ^ ℓ := hS
    _ < 2 ^ D * 2 ^ ℓ := Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos ℓ)
    _ = 2 ^ (D + ℓ) := by rw [pow_add]

end SubNLogN.Machine.FFT.TwAddr
