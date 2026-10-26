/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseDefs
import SubNLogN.Machine.Arith.Value
import SubNLogN.Math.Networks.LayoutEncodingLayer
import SubNLogN.Math.Networks.Proofs.LayerSpecPad

/-!
# Layer driver post-phase: value bridge (`Machine/Layer/DrvPostMath.lean`)

**Scope (honest summary).** Pure math, no machine. Relates the stored output of the post-phase,
`encLayer P (drvStageOut t h y)` (rows case) and `encLayer P (drvSmallOut t y)` (no-rows case), to
integer-level operations on the stored input: unpad (`List.take` per block), the phase scan
(`phaseRec`) and the truncating shift (`truncShiftC`).

* `post_num`: one coefficient, `gridInt P (truncC P (b^D · i^s · gridVal (P+Δ) n))`
  `= truncShiftC (Δ + ⌊D/2⌋ + D mod 2) ((1-i)^{D mod 2} · i^{s + postC D} · n)`.
* `selCount_eq_sum`, `sDiag_sum_eq`: the selected-bit sum of `sDiag` at the lexicographic address `i` is
  `selCount S K ρ D i`.
* `unpad_addr`: the row reshape `mergeAddr` in lexicographic order is the block index map
  `i ↦ ⌊i/keep⌋·(keep + Npad) + i mod keep`.

Helpers live in `SubNLogN.Machine.Layer.DrvPPAux`.
-/

namespace SubNLogN.Machine.Layer.DrvPPAux

open SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks (bD kb layerLayout selField encodeAddr decodeAddr mergeAddr layerPhase3
  topClass sDiag restrictArr encodeArr decodeArr padR q0Of)
open SubNLogN.Math.Networks.Model (ProcK Step RowClass)
open SubNLogN.Math.Networks.Model (layerBit)

/-! ## Grid values -/

theorem gridUnit_mul_pow' (F : ℕ) : gridUnit F * (2 : ℝ) ^ F = 1 := by
  unfold gridUnit; field_simp

theorem gridInt_gridVal' (F : ℕ) (c : CInt) : gridInt F (gridVal F c) = c := by
  obtain ⟨a, b⟩ := c
  simp [gridInt, gridVal, mul_assoc, gridUnit_mul_pow']

theorem gridVal_gridInt' {F : ℕ} {z : ℂ} (hz : OnGrid F z) : gridVal F (gridInt F z) = z := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  apply Complex.ext
  · simp [gridVal, gridInt, ha, mul_assoc, gridUnit_mul_pow']
  · simp [gridVal, gridInt, hb, mul_assoc, gridUnit_mul_pow']

theorem gridVal_re (F : ℕ) (c : CInt) : (gridVal F c).re = (c.1 : ℝ) * gridUnit F := rfl
theorem gridVal_im (F : ℕ) (c : CInt) : (gridVal F c).im = (c.2 : ℝ) * gridUnit F := rfl

theorem I_pow_mod4 (e : ℕ) : Complex.I ^ e = Complex.I ^ (e % 4) := by
  conv_lhs => rw [← Nat.div_add_mod e 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem gridVal_rotC (F e : ℕ) (c : CInt) :
    gridVal F (rotC e c) = Complex.I ^ e * gridVal F c := by
  rw [I_pow_mod4]
  have h4 : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold rotC
  rcases (by omega : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3) with h | h | h | h
  · rw [if_pos h, h, pow_zero, one_mul]
  · rw [if_neg (by omega), if_pos h, h, pow_one]
    apply Complex.ext <;> simp [gridVal_re, gridVal_im]
  · rw [if_neg (by omega), if_neg (by omega), if_pos h, h]
    apply Complex.ext <;> simp [gridVal_re, gridVal_im]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), h]
    apply Complex.ext <;> simp [gridVal_re, gridVal_im, pow_succ]

theorem gridVal_omiC (F : ℕ) (c : CInt) :
    gridVal F (omiC c) = (1 - Complex.I) * gridVal F c := by
  apply Complex.ext
  · simp [omiC, gridVal_re, gridVal_im]; try ring
  · simp [omiC, gridVal_re, gridVal_im]; try ring

theorem gridUnit_add'' (p q : ℕ) : gridUnit (p + q) = gridUnit p * gridUnit q := by
  unfold gridUnit; rw [pow_add, mul_inv]

theorem gridVal_eq (F : ℕ) (c : CInt) :
    gridVal F c = ((c.1 : ℂ) + (c.2 : ℂ) * Complex.I) * ((gridUnit F : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [gridVal_re, gridVal_im]

theorem gridVal_add_prec (F k : ℕ) (c : CInt) :
    gridVal (F + k) c = gridVal F c * ((gridUnit k : ℝ) : ℂ) := by
  rw [gridVal_eq, gridVal_eq, gridUnit_add'']
  push_cast
  ring

theorem gridUnit_cast (k : ℕ) : ((gridUnit k : ℝ) : ℂ) = ((2 : ℂ) ^ k)⁻¹ := by
  unfold gridUnit; push_cast; rfl

/-! ## One coefficient of phase 3 -/

/-- The phase offset of the post-phase: `i^{postC D} = (-i)^{⌊D/2⌋}`. -/
def postC (D : ℕ) : ℕ := (4 - D / 2 % 4) % 4

theorem I_pow_postC (D : ℕ) : Complex.I ^ postC D = (-Complex.I) ^ (D / 2) := by
  have hneg : (-Complex.I) = Complex.I ^ 3 := by
    rw [pow_succ, pow_two, Complex.I_mul_I]; ring
  rw [hneg, ← pow_mul, I_pow_mod4 (3 * (D / 2)), I_pow_mod4 (postC D)]
  unfold postC
  congr 1
  omega

/-- The numerator form of phase 3 on one coefficient. -/
def postNum (s D : ℕ) (n : CInt) : CInt :=
  if D % 2 = 1 then omiC (rotC (s + postC D) n) else rotC (s + postC D) n

theorem bD_smul_gridVal (P Δ D s : ℕ) (n : CInt) :
    bD D • (Complex.I ^ s • gridVal (P + Δ) n) =
      gridVal (P + (Δ + D / 2 + D % 2)) (postNum s D n) := by
  have hbD : bD D = Complex.I ^ postC D / (2 : ℂ) ^ (D / 2) * kb ^ (D % 2) := by
    unfold bD
    rw [I_pow_postC, div_pow]
  have hkb : kb = (1 - Complex.I) / 2 := rfl
  have hR : gridVal ((P + Δ) + (D / 2 + D % 2)) (postNum s D n) =
      gridVal (P + Δ) (postNum s D n) * ((2 : ℂ) ^ (D / 2 + D % 2))⁻¹ := by
    rw [gridVal_add_prec, gridUnit_cast]
  rw [show P + (Δ + D / 2 + D % 2) = (P + Δ) + (D / 2 + D % 2) by ring, hR, smul_eq_mul,
    smul_eq_mul, hbD, hkb]
  unfold postNum
  set g := gridVal (P + Δ) n with hg
  rcases Nat.mod_two_eq_zero_or_one D with h | h
  · rw [if_neg (by omega), h, gridVal_rotC, ← hg, pow_add Complex.I s (postC D)]
    simp only [pow_zero, mul_one, add_zero]
    field_simp
  · rw [if_pos h, h, gridVal_omiC, gridVal_rotC, ← hg, pow_add Complex.I s (postC D)]
    simp only [pow_succ]
    field_simp

/-- **One coefficient of phase 3 at the integer level.** -/
theorem post_num (P Δ D s : ℕ) (n : CInt) :
    gridInt P (truncC P (bD D • (Complex.I ^ s • gridVal (P + Δ) n))) =
      truncShiftC (Δ + D / 2 + D % 2) (postNum s D n) := by
  rw [bD_smul_gridVal, ← gridVal_truncShiftC, gridInt_gridVal']


/-! ## Bits of the lexicographic address -/

theorem bit_eq_div_mod (n t : ℕ) : (if n.testBit t then 1 else 0) = n / 2 ^ t % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ t) with h | h <;> simp [h]

/-- Binary expansion: `Σ_{t<K} 2^t [bit t of n] = n mod 2^K`. -/
theorem sum_testBit (n K : ℕ) :
    ∑ t ∈ Finset.range K, 2 ^ t * (if n.testBit t then 1 else 0) = n % 2 ^ K := by
  induction K with
  | zero => simp [Nat.mod_one]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, bit_eq_div_mod, pow_succ, Nat.mod_mul]

/-- Bit `t` of chunk `j` of the lexicographic address `i` is bit `K(D-1-j) + t` of `i / S`. -/
theorem layerAddr_bit {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) (i j t : ℕ) (hj : j < D)
    (ht : t < K) :
    (layerAddrOfIndex A K D S hA hS i).2.1 ⟨j, hj⟩ ⟨t, ht⟩ =
      (i / S).testBit (K * (D - 1 - j) + t) := by
  have h1 : t + K * (D - 1 - j) < K * D := by
    have : K * (D - 1 - j) + K ≤ K * D := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left K (by omega)
    omega
  show ((i / S) % 2 ^ (K * D) / 2 ^ (K * (D - 1 - j)) % 2 ^ K).testBit t = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  simp only [ht, h1, decide_true, Bool.true_and]
  rw [Nat.add_comm]

/-- The `0/1` value of bit `t` of chunk `j` of the lexicographic address `i`. -/
theorem layerBit_layerAddr {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) (i j t : ℕ) (hj : j < D)
    (ht : t < K) :
    layerBit (layerAddrOfIndex A K D S hA hS i) j t =
      if (i / S).testBit (K * (D - 1 - j) + t) then 1 else 0 := by
  unfold layerBit
  rw [dif_pos ⟨hj, ht⟩, layerAddr_bit]

/-- The selected-bit field of chunk `j` holds bit `ρ` of chunk `j`. -/
theorem blockVal_selField {A K D S : ℕ} (x : LayerAddr A K D S) {ρ j : ℕ} (hρ : ρ < K)
    (hj : j < D) :
    (layerLayout A K D S).blockVal (selField K ρ j) (selField K ρ j + 1) (encodeAddr x) =
      layerBit x j ρ := by
  have hle : j * K + K ≤ D * K := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right K hj
  have hp : selField K ρ j < (layerLayout A K D S).n := by
    unfold selField; show 1 + j * K + (K - 1 - ρ) < D * K + 2; omega
  rw [SubNLogN.Math.Networks.Model.LayoutEncodingAux.lay_blockVal_field _ hp]
  have h := SubNLogN.Math.Networks.Model.LayoutEncodingAux.lay_encode_bit x hj (show K - 1 - ρ < K by omega)
    (by unfold selField at hp; exact hp)
  unfold selField
  rw [h, show K - 1 - (K - 1 - ρ) = ρ by omega]

theorem selCount_succ (S K ρ D x : ℕ) :
    selCount S K ρ (D + 1) x =
      selCount S K ρ D x + (if (x / S).testBit (ρ + K * D) then 1 else 0) := by
  unfold selCount
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : (x / S).testBit (ρ + K * D) <;> simp [h]

theorem selCount_eq_sum (S K ρ D x : ℕ) :
    selCount S K ρ D x =
      ∑ j ∈ Finset.range D, (if (x / S).testBit (ρ + K * j) then 1 else 0) := by
  induction D with
  | zero => simp [selCount]
  | succ D ih => rw [selCount_succ, ih, Finset.sum_range_succ]

/-- **The exponent of `𝒮_D`** at the lexicographic address `i` is `selCount S K ρ D i`. -/
theorem sDiag_sum_eq {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) {ρ : ℕ} (hρ : ρ < K) (i : ℕ) :
    (∑ j ∈ Finset.range D, (layerLayout A K D S).blockVal (selField K ρ j) (selField K ρ j + 1)
      (encodeAddr (layerAddrOfIndex A K D S hA hS i))) = selCount S K ρ D i := by
  rw [Finset.sum_congr rfl fun j hj => by
      rw [blockVal_selField _ hρ (Finset.mem_range.mp hj),
        layerBit_layerAddr hA hS i j ρ (Finset.mem_range.mp hj) hρ],
    selCount_eq_sum]
  rw [← Finset.sum_range_reflect (fun j => if (i / S).testBit (ρ + K * j) then 1 else 0) D]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.add_comm]

/-! ## Chunk values and the row reshape -/

theorem mod_div_mod_eq {n m a K : ℕ} (h : a + K ≤ m) :
    n % 2 ^ m / 2 ^ a % 2 ^ K = n / 2 ^ a % 2 ^ K := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases ht : t < K
  · have h2 : t + a < m := by omega
    simp [ht, h2]
  · simp [ht]

theorem chunkVal_layerAddr {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) (i j : ℕ) (hj : j < D) :
    SubNLogN.Math.Networks.Model.chunkVal (layerAddrOfIndex A K D S hA hS i) j = (i / S) / 2 ^ (K * (D - 1 - j)) % 2 ^ K := by
  unfold SubNLogN.Math.Networks.Model.chunkVal
  rw [← sum_testBit]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [layerBit_layerAddr hA hS i j t hj (Finset.mem_range.mp ht), Nat.testBit_div_two_pow,
    Nat.add_comm t]

/-- The value of the first `d` chunks of the lexicographic address `i`. -/
theorem chunks_value {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) (i : ℕ) :
    ∀ d, d ≤ D → ∑ j ∈ Finset.range d,
        SubNLogN.Math.Networks.Model.chunkVal (layerAddrOfIndex A K D S hA hS i) j * 2 ^ (K * (d - 1 - j)) =
      (i / S) % 2 ^ (K * D) / 2 ^ (K * (D - d)) := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [Finset.sum_range_zero, Nat.sub_zero, Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity))]
  | succ d ih =>
    intro hd
    have hdD : d < D := by omega
    rw [Finset.sum_range_succ, show d + 1 - 1 - d = 0 by omega, Nat.mul_zero, pow_zero, mul_one,
      chunkVal_layerAddr hA hS i d hdD]
    have hsum : ∑ j ∈ Finset.range d,
        SubNLogN.Math.Networks.Model.chunkVal (layerAddrOfIndex A K D S hA hS i) j * 2 ^ (K * (d + 1 - 1 - j)) =
        (∑ j ∈ Finset.range d,
          SubNLogN.Math.Networks.Model.chunkVal (layerAddrOfIndex A K D S hA hS i) j * 2 ^ (K * (d - 1 - j))) * 2 ^ K := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [mul_assoc, ← pow_add, show K * (d + 1 - 1 - j) = K * (d - 1 - j) + K by
        rw [show d + 1 - 1 - j = d - 1 - j + 1 by omega, Nat.mul_succ]]
    rw [hsum, ih (by omega), show D - 1 - d = D - (d + 1) by omega]
    have hK : K * (D - (d + 1)) + K = K * (D - d) := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hle : K * (D - (d + 1)) + K ≤ K * D := by
      rw [hK]; exact Nat.mul_le_mul_left K (Nat.sub_le D d)
    conv_rhs => rw [← Nat.div_add_mod' ((i / S) % 2 ^ (K * D) / 2 ^ (K * (D - (d + 1)))) (2 ^ K),
      Nat.div_div_eq_div_mul, ← pow_add, hK, mod_div_mod_eq hle]

/-- The prefix field of the reshaped address. -/
theorem mergeAddr_zero {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (z : (layerLayout A K D S).Addr) (h0 : 0 < (layerLayout (A * R) K (D - q) S).n) :
    (mergeAddr A K D S q R hR hq z ⟨0, h0⟩).val =
      (z ⟨0, by simp [layerLayout]⟩).val * R + (layerLayout A K D S).blockVal 1 (1 + q * K) z % R := by
  simp [mergeAddr]

/-- A chunk-bit field of the reshaped address. -/
theorem mergeAddr_bit {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (z : (layerLayout A K D S).Addr) (f : ℕ) (hf0 : f ≠ 0) (hf : f ≤ (D - q) * K)
    (hn : f < (layerLayout (A * R) K (D - q) S).n) (hn' : f + q * K < (layerLayout A K D S).n) :
    (mergeAddr A K D S q R hR hq z ⟨f, hn⟩).val = (z ⟨f + q * K, hn'⟩).val := by
  simp [mergeAddr, hf0, hf]

/-- The suffix field of the reshaped address. -/
theorem mergeAddr_suffix {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (z : (layerLayout A K D S).Addr)
    (hn : (D - q) * K + 1 < (layerLayout (A * R) K (D - q) S).n) :
    (mergeAddr A K D S q R hR hq z ⟨(D - q) * K + 1, hn⟩).val =
      (z ⟨D * K + 1, by simp [layerLayout]⟩).val := by
  simp [mergeAddr]


theorem testBit_mul_pow_add (c m n p : ℕ) (hp : p < m) : (c * 2 ^ m + n).testBit p = n.testBit p := by
  have h1 : ((c * 2 ^ m + n) % 2 ^ m).testBit p = (c * 2 ^ m + n).testBit p := by
    rw [Nat.testBit_mod_two_pow]; simp [hp]
  have h2 : (n % 2 ^ m).testBit p = n.testBit p := by
    rw [Nat.testBit_mod_two_pow]; simp [hp]
  rw [← h1, ← h2, Nat.add_comm, Nat.add_mul_mod_self_right]

theorem testBit_mod_pow_of_lt (n M p : ℕ) (hp : p < M) : (n % 2 ^ M).testBit p = n.testBit p := by
  rw [Nat.testBit_mod_two_pow]; simp [hp]

/-- **The row reshape in lexicographic order**: the record at lexicographic index `i` of the
original layout comes from index `⌊i/keep⌋·(R·B') + i mod keep` of the reshaped layout, where
`keep = 2^{KD}·S` and `B' = 2^{K(D-q)}·S`. -/
theorem unpad_addr {A K D S q R : ℕ} (hA : 0 < A) (hS : 0 < S) (hR : 0 < R) (hq : q ≤ D)
    (hRq : 2 ^ (K * q) ≤ R) (i : ℕ) (hi : i < A * (2 ^ (K * D) * S)) :
    decodeAddr (mergeAddr A K D S q R hR hq (encodeAddr (layerAddrOfIndex A K D S hA hS i))) =
      layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS
        (i / (2 ^ (K * D) * S) * (R * (2 ^ (K * (D - q)) * S)) + i % (2 ^ (K * D) * S)) := by
  set x := layerAddrOfIndex A K D S hA hS i with hx
  set keep := 2 ^ (K * D) * S with hkeep
  set i' := i / keep * (R * (2 ^ (K * (D - q)) * S)) + i % keep with hi'
  have hkpos : 0 < keep := by positivity
  have ha : i / keep < A := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have hdecomp : 2 ^ (K * D) = 2 ^ (K * q) * 2 ^ (K * (D - q)) := by
    rw [← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' hq]
  have hmodS : i % keep / S = i / S % 2 ^ (K * D) := by
    rw [hkeep, Nat.mod_mul_left_div_self]
  have hfac : i / keep * (R * (2 ^ (K * (D - q)) * S)) =
      (i / keep * R * 2 ^ (K * (D - q))) * S := by ring
  have hi'S : i' / S = i / keep * R * 2 ^ (K * (D - q)) + i / S % 2 ^ (K * D) := by
    rw [hi', hfac, Nat.add_comm, Nat.add_mul_div_right _ _ hS, hmodS, Nat.add_comm]
  have hi'mod : i' % S = i % S := by
    rw [hi', hfac, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_mod_of_dvd _ (Dvd.intro_left _ rfl)]
  set v := i / S % 2 ^ (K * D) / 2 ^ (K * (D - q)) with hv
  have hvlt : v < 2 ^ (K * q) := by
    rw [hv, Nat.div_lt_iff_lt_mul (by positivity), ← hdecomp]
    exact Nat.mod_lt _ (by positivity)
  have hz0 : ((encodeAddr x) ⟨0, by simp [layerLayout]⟩).val = i / keep := by
    show (layerAddrOfIndex A K D S hA hS i).1.val = i / keep
    exact Nat.mod_eq_of_lt ha
  have hblk : (layerLayout A K D S).blockVal 1 (1 + q * K) (encodeAddr x) = v := by
    rw [SubNLogN.Math.Networks.Model.LayoutEncodingAux.lay_blockVal_chunks x q hq,
      chunks_value hA hS i q hq]
  have hpre : i' / (2 ^ (K * (D - q)) * S) % (A * R) = i / keep * R + v := by
    have h1 : i' / (2 ^ (K * (D - q)) * S) = i / keep * R + v := by
      rw [Nat.mul_comm (2 ^ (K * (D - q))) S, ← Nat.div_div_eq_div_mul, hi'S, Nat.add_comm,
        Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ (K * (D - q))), Nat.add_comm]
    rw [h1, Nat.mod_eq_of_lt]
    calc i / keep * R + v < i / keep * R + R := by
          have := lt_of_lt_of_le hvlt hRq; omega
      _ = (i / keep + 1) * R := by ring
      _ ≤ A * R := Nat.mul_le_mul_right R ha
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    show (mergeAddr A K D S q R hR hq (encodeAddr x) ⟨0, by simp [layerLayout]⟩).val =
      i' / (2 ^ (K * (D - q)) * S) % (A * R)
    rw [mergeAddr_zero, hz0, hblk, hpre, Nat.mod_eq_of_lt (lt_of_lt_of_le hvlt hRq)]
  · funext j t
    have hj := j.isLt
    have ht := t.isLt
    have hjK : (j : ℕ) * K + K ≤ (D - q) * K := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right K hj
    have hjq : (j : ℕ) + q < D := by omega
    have hjqK : ((j : ℕ) + q) * K + K ≤ D * K := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right K hjq
    have hf0 : 1 + (j : ℕ) * K + (K - 1 - (t : ℕ)) ≠ 0 := by omega
    have hf : 1 + (j : ℕ) * K + (K - 1 - (t : ℕ)) ≤ (D - q) * K := by omega
    have hn : 1 + (j : ℕ) * K + (K - 1 - (t : ℕ)) < (layerLayout (A * R) K (D - q) S).n := by
      show 1 + (j : ℕ) * K + (K - 1 - (t : ℕ)) < (D - q) * K + 2; omega
    have hidx : 1 + (j : ℕ) * K + (K - 1 - (t : ℕ)) + q * K =
        1 + ((j : ℕ) + q) * K + (K - 1 - (t : ℕ)) := by ring
    have hn'' : 1 + ((j : ℕ) + q) * K + (K - 1 - (t : ℕ)) < (layerLayout A K D S).n := by
      show 1 + ((j : ℕ) + q) * K + (K - 1 - (t : ℕ)) < D * K + 2; omega
    have hn' : 1 + (j : ℕ) * K + (K - 1 - (t : ℕ)) + q * K < (layerLayout A K D S).n := by
      rw [hidx]; exact hn''
    show decide ((mergeAddr A K D S q R hR hq (encodeAddr x)
        ⟨1 + (j : ℕ) * K + (K - 1 - (t : ℕ)), hn⟩).val = 1) =
      (layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS i').2.1 j t
    have hfin : (⟨1 + (j : ℕ) * K + (K - 1 - (t : ℕ)) + q * K, hn'⟩ : Fin (layerLayout A K D S).n) =
        ⟨1 + ((j : ℕ) + q) * K + (K - 1 - (t : ℕ)), hn''⟩ := Fin.ext hidx
    rw [mergeAddr_bit hR hq _ _ hf0 hf hn hn', hfin,
      SubNLogN.Math.Networks.Model.LayoutEncodingAux.lay_encode_bit x hjq
        (show K - 1 - (t : ℕ) < K by omega) hn'',
      show K - 1 - (K - 1 - (t : ℕ)) = (t : ℕ) by omega, layerBit_layerAddr hA hS i _ _ hjq ht]
    have hR' := layerAddr_bit (Nat.mul_pos hA hR) hS i' (j : ℕ) (t : ℕ) hj ht
    simp only [Fin.eta] at hR'
    rw [hR', hi'S]
    have hp : K * (D - q - 1 - (j : ℕ)) + (t : ℕ) < K * (D - q) := by
      have : K * (D - q - 1 - (j : ℕ)) + K ≤ K * (D - q) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left K (by omega)
      omega
    rw [testBit_mul_pow_add _ _ _ _ hp, testBit_mod_pow_of_lt _ _ _
      (lt_of_lt_of_le hp (Nat.mul_le_mul_left K (Nat.sub_le D q))),
      show K * (D - q - 1 - (j : ℕ)) = K * (D - 1 - ((j : ℕ) + q)) by congr 1; omega]
    by_cases hb : (i / S).testBit (K * (D - 1 - ((j : ℕ) + q)) + (t : ℕ)) <;> simp [hb]
  · apply Fin.ext
    show (mergeAddr A K D S q R hR hq (encodeAddr x) ⟨(D - q) * K + 1, by simp [layerLayout]⟩).val =
      i' % S
    rw [mergeAddr_suffix, hi'mod]
    simp only [encodeAddr, dif_neg (show D * K + 1 ≠ 0 by omega),
      dif_neg (show ¬ D * K + 1 ≤ D * K by omega)]
    rfl

/-! ## Lists over index ranges -/

/-- `k` chunks of `n` consecutive elements. -/
def chunksOf {α : Type} (n : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | k + 1, l => l.take n :: chunksOf n k (l.drop n)

theorem chunksOf_flatten {α : Type} (n : ℕ) : ∀ (k : ℕ) (l : List α), l.length = n * k →
    (chunksOf n k l).flatten = l
  | 0, l, h => by
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at h
    simp [chunksOf, h]
  | k + 1, l, h => by
    simp only [chunksOf, List.flatten_cons]
    rw [chunksOf_flatten n k (l.drop n) (by rw [List.length_drop, h, Nat.mul_succ]; omega)]
    exact List.take_append_drop n l

theorem chunksOf_length_mem {α : Type} (n : ℕ) : ∀ (k : ℕ) (l : List α), l.length = n * k →
    ∀ c ∈ chunksOf n k l, c.length = n
  | 0, _, _ => by simp [chunksOf]
  | k + 1, l, h => by
    intro c hc
    simp only [chunksOf, List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [List.length_take, h, Nat.mul_succ]; omega
    · exact chunksOf_length_mem n k (l.drop n)
        (by rw [List.length_drop, h, Nat.mul_succ]; omega) c hc

theorem chunksOf_length {α : Type} (n : ℕ) : ∀ (k : ℕ) (l : List α), (chunksOf n k l).length = k
  | 0, _ => rfl
  | k + 1, l => by simp [chunksOf, chunksOf_length n k (l.drop n)]

theorem take_chunksOf_map_range {β : Type} (n m : ℕ) (hm : m ≤ n) (hm0 : 0 < m) :
    ∀ (k : ℕ) (g : ℕ → β),
      ((chunksOf n k ((List.range (k * n)).map g)).map (List.take m)).flatten =
        (List.range (k * m)).map fun i => g (i / m * n + i % m)
  | 0, g => by simp [chunksOf]
  | k + 1, g => by
    rw [show (k + 1) * n = n + k * n by ring, show (k + 1) * m = m + k * m by ring,
      List.range_add, List.range_add, List.map_append, List.map_append]
    have hlen : ((List.range n).map g).length = n := by simp
    simp only [chunksOf, List.map_cons, List.flatten_cons]
    rw [List.take_left' hlen, List.drop_left' hlen, List.map_map,
      take_chunksOf_map_range n m hm hm0 k (g ∘ (n + ·)), ← List.map_take, List.take_range,
      Nat.min_eq_left hm, List.map_map]
    congr 1
    · refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      simp [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp]
      congr 1
      rw [Nat.add_comm m i, Nat.add_div_right _ hm0, Nat.add_mod_right]
      ring

theorem mapIdx_map_range {β γ : Type} (f : ℕ → β → γ) (g : ℕ → β) (n : ℕ) :
    ((List.range n).map g).mapIdx f = (List.range n).map fun i => f i (g i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-! ## Phase 3 pointwise -/

theorem phase3_apply {A K D S r : ℕ} (ρ P : ℕ) (Y : (layerLayout A K D S).Addr → Fin r → ℂ)
    (z : (layerLayout A K D S).Addr) (k : Fin r) :
    ProcK.run 0 (layerPhase3 A K D S r ρ P) (topClass A K D S) Y z k =
      truncC P (bD D • (Complex.I ^ (∑ j ∈ Finset.range D, (layerLayout A K D S).blockVal
        (selField K ρ j) (selField K ρ j + 1) z) • Y z k)) := by
  simp [ProcK.run, layerPhase3, Step.runIn, Step.run, sDiag, topClass, RowClass.top,
    RowClass.mem, Nat.mod_one, Pi.smul_apply, smul_eq_mul]

/-- `padR` dominates `2^{q₀K}`. -/
theorem le_padR (d K : ℕ) : 2 ^ (K * q0Of d) ≤ padR d K := by
  unfold padR
  have hT : 0 < SubNLogN.Math.Networks.Wc ^ SubNLogN.Math.Networks.k0Of d :=
    pow_pos SubNLogN.Math.Networks.Wc_pos _
  rw [Nat.mul_comm K]
  set T := SubNLogN.Math.Networks.Wc ^ SubNLogN.Math.Networks.k0Of d
  set R0 := 2 ^ (q0Of d * K)
  have h := Nat.div_add_mod (R0 + T - 1) T
  have h2 := Nat.mod_lt (R0 + T - 1) hT
  omega

/-! ## The post-phase output (integer level) -/

/-- Records per prefix block kept by the unpad, `2^{KD}·S`. -/
def postKeep (t : LayerRT) : ℕ := 2 ^ (t.K * t.D) * t.S

/-- Records per prefix block of the padded stage array, `padR · 2^{K(D-q₀)}·S`. -/
noncomputable def postBlk (t : LayerRT) : ℕ :=
  padR t.d t.K * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S)

/-- The total right shift of the post-phase, `Δ + ⌊D/2⌋ + D mod 2`. -/
def postShift (t : LayerRT) : ℕ := drvDelta t + t.D / 2 + t.D % 2

theorem encArr_layerAddrs {A K D S r : ℕ} (hA : 0 < A) (hS : 0 < S) (F : ℕ)
    (z : RArr (LayerAddr A K D S) r) :
    encArr F (layerAddrs A K D S hA hS) z =
      (List.range (A * 2 ^ (K * D) * S)).map fun i =>
        (List.finRange r).map fun k => gridInt F (z (layerAddrOfIndex A K D S hA hS i) k) := by
  unfold encArr layerAddrs
  rw [List.map_map]
  rfl

theorem post_coef (P Δ D s : ℕ) (z : ℂ) (n : CInt) (hz : z = gridVal (P + Δ) n) :
    gridInt P (truncC P (bD D • (Complex.I ^ s • z))) =
      truncShiftC (Δ + D / 2 + D % 2)
        (if D % 2 = 1 then omiC (rotC (s + postC D) n) else rotC (s + postC D) n) := by
  subst hz
  exact post_num P Δ D s n

theorem postKeep_le_postBlk (t : LayerRT) (h : DrvRows t) : postKeep t ≤ postBlk t := by
  unfold postKeep postBlk
  have hdec : 2 ^ (t.K * t.D) = 2 ^ (t.K * q0Of t.d) * 2 ^ (t.K * (t.D - q0Of t.d)) := by
    rw [← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' h.1.le]
  rw [hdec, mul_assoc]
  exact Nat.mul_le_mul_right _ (le_padR t.d t.K)

/-- **The post-phase output, rows case**: the stored output is the truncating shift of the phase
scan of the unpadded stored input. -/
theorem post_enc_rows (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (h : DrvRows t)
    (hρ : t.ρ < t.K) (b : ℕ) (hb : b ≤ drvDelta t)
    (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) (hy : ArrGrowth t.P b y) :
    encLayer hA hS t.P (drvStageOut t h y) =
      mapC (truncShiftC (postShift t))
        ((((chunksOf (postBlk t) t.A
            (encArr (t.P + drvDelta t)
              (layerAddrs (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA h.2) hS) y)).map
            (List.take (postKeep t))).flatten).mapIdx
          (phaseRec t.S t.K t.ρ t.D (postC t.D) (t.D % 2))) := by
  have hkpos : 0 < postKeep t := by unfold postKeep; positivity
  have hRq : 2 ^ (t.K * q0Of t.d) ≤ padR t.d t.K := le_padR t.d t.K
  rw [encArr_layerAddrs (Nat.mul_pos hA h.2) hS,
    show drvA' t * 2 ^ (t.K * drvD' t) * t.S = t.A * postBlk t by
      unfold postBlk drvA' drvD'; ring,
    show t.A * postBlk t = t.A * postBlk t from rfl,
    take_chunksOf_map_range _ _ (postKeep_le_postBlk t h) hkpos, mapIdx_map_range]
  unfold encLayer
  rw [encArr_layerAddrs hA hS, show t.A * 2 ^ (t.K * t.D) * t.S = t.A * postKeep t by
      unfold postKeep; ring]
  unfold mapC
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  simp only [Function.comp, phaseRec, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  have hiM : i < t.A * (2 ^ (t.K * t.D) * t.S) := hi
  have haddr := unpad_addr hA hS h.2 h.1.le hRq i hiM
  show gridInt t.P (ProcK.run 0 (layerPhase3 t.A t.K t.D t.S t.r t.ρ t.P)
    (topClass t.A t.K t.D t.S) (restrictArr h.2 h.1.le (encodeArr y))
    (encodeAddr (layerAddrOfIndex t.A t.K t.D t.S hA hS i)) k) = _
  rw [phase3_apply, sDiag_sum_eq hA hS hρ]
  have hval : restrictArr h.2 h.1.le (encodeArr y)
      (encodeAddr (layerAddrOfIndex t.A t.K t.D t.S hA hS i)) k =
      y (layerAddrOfIndex (drvA' t) t.K (drvD' t) t.S (Nat.mul_pos hA h.2) hS
        (i / postKeep t * postBlk t + i % postKeep t)) k := by
    show y (decodeAddr (mergeAddr t.A t.K t.D t.S (q0Of t.d) (padR t.d t.K) h.2 h.1.le
      (encodeAddr (layerAddrOfIndex t.A t.K t.D t.S hA hS i)))) k = _
    rw [haddr]
    rfl
  rw [hval]
  have hgrid : OnGrid (t.P + drvDelta t) (y (layerAddrOfIndex (drvA' t) t.K (drvD' t) t.S
      (Nat.mul_pos hA h.2) hS (i / postKeep t * postBlk t + i % postKeep t)) k) :=
    OnGrid.mono (by omega) (hy _ k).1
  exact post_coef t.P (drvDelta t) t.D _ _ _ (gridVal_gridInt' hgrid).symm

/-- **The post-phase output, no-rows case.** -/
theorem post_enc_small (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K)
    (b : ℕ) (hb : b ≤ drvDelta t) (y : RArr (LayerAddr t.A t.K t.D t.S) t.r)
    (hy : ArrGrowth t.P b y) :
    encLayer hA hS t.P (drvSmallOut t y) =
      mapC (truncShiftC (postShift t))
        ((encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) y).mapIdx
          (phaseRec t.S t.K t.ρ t.D (postC t.D) (t.D % 2))) := by
  unfold encLayer
  rw [encArr_layerAddrs hA hS, encArr_layerAddrs hA hS, mapIdx_map_range]
  unfold mapC
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, phaseRec, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  show gridInt t.P (ProcK.run 0 (layerPhase3 t.A t.K t.D t.S t.r t.ρ t.P)
    (topClass t.A t.K t.D t.S) (encodeArr y)
    (encodeAddr (layerAddrOfIndex t.A t.K t.D t.S hA hS i)) k) = _
  rw [phase3_apply, sDiag_sum_eq hA hS hρ]
  have hval : encodeArr y (encodeAddr (layerAddrOfIndex t.A t.K t.D t.S hA hS i)) k =
      y (layerAddrOfIndex t.A t.K t.D t.S hA hS i) k := by
    show y (decodeAddr (encodeAddr _)) k = _
    rw [SubNLogN.Math.Networks.LayerSpecPadAux.decodeAddr_encodeAddr]
  rw [hval]
  have hgrid : OnGrid (t.P + drvDelta t) (y (layerAddrOfIndex t.A t.K t.D t.S hA hS i) k) :=
    OnGrid.mono (by omega) (hy _ k).1
  exact post_coef t.P (drvDelta t) t.D _ _ _ (gridVal_gridInt' hgrid).symm

end SubNLogN.Machine.Layer.DrvPPAux
