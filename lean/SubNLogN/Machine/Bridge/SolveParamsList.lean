/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsDefs
import SubNLogN.Machine.K1.Twos

/-!
# SOL-PARAM-ROWS (1): list and bit identities for `SolParamRowsStmt`

Pure facts (no machine programs) used by the solver parameter row kernel
(`Bridge/SolveParams*.lean`, contract `SolParamRowsStmt` of `Bridge/SolveParamsDefs.lean`):
* replication: under `ShapeOK`, `solHalfM b i = (t_i/2)·U` and `solRep b i = U` with
  `U = suffixProd t i`, and `solParamRow b i h g` is the concatenation over the `t_i/2` digits of
  the half of `U` copies of the digit's record (`solParamRow_eq`);
* bits: `twosBits w 0` is all zeros, sign extension `twosBits (w+1) z = twosBits w z ++ [z < 0]`
  for `FitsTwos w z`, the last bit of `twosBits w z` is the sign, and the negation as the ripple
  `K1.ripOut negBit`;
* records: the payload of a solver record `[μ̂, â, γ̂]` as six fields.

All proved; helpers live in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## Replication -/

/-- Column `s` of `n` groups of `U` columns belongs to group `s / U`. -/
theorem range_mul_map_div {α : Type} (f : ℕ → α) {U : ℕ} (hU : 0 < U) :
    ∀ n : ℕ, (List.range (n * U)).map (fun s => f (s / U)) =
      (List.range n).flatMap (fun j => List.replicate U (f j))
  | 0 => by simp
  | n + 1 => by
    rw [show (n + 1) * U = n * U + U by ring, List.range_add, List.map_append,
      range_mul_map_div f hU n, List.range_succ, List.flatMap_append]
    congr 1
    rw [List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    have hs' := List.mem_range.1 hs
    simp only [Function.comp_apply]
    congr 1
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hU, Nat.div_eq_of_lt hs', Nat.zero_add]

/-- An axis length of a valid shape is a power of two `2^a` with `a ≥ 1`. -/
theorem shape_pow {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) (i : Fin d) :
    ∃ a, 1 ≤ a ∧ t i = 2 ^ a := by
  obtain ⟨h2, a, ha⟩ := hS i
  refine ⟨a, ?_, ha⟩
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0; rw [ha] at h2; norm_num at h2
  · exact h0

theorem shape_even {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) (i : Fin d) :
    2 * (t i / 2) = t i := by
  obtain ⟨a, ha1, ha⟩ := shape_pow hS i
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  rw [ha, pow_succ]
  omega

theorem suffixProd_pos {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) (i : Fin d) :
    0 < suffixProd t i := by
  unfold suffixProd
  exact Finset.prod_pos fun l _ => lt_of_lt_of_le (by norm_num) (hS l).1

theorem prefixProd_pos'' {d : ℕ} {t : Fin d → ℕ} (hS : ShapeOK t) (k : ℕ) :
    0 < prefixProd t k := by
  unfold prefixProd
  exact Finset.prod_pos fun l _ => lt_of_lt_of_le (by norm_num) (hS l).1

/-- `M = (t_i/2)·U`. -/
theorem solHalfM_eq (b : BrPar) (i : Fin b.d) (hS : ShapeOK b.t) :
    solHalfM b i = (b.t i / 2) * suffixProd b.t i := by
  unfold solHalfM
  have h1 := prefixProd_mul_mul_suffixProd b.t i
  have hA := prefixProd_pos'' hS i
  have h2 : totalLen b.t / prefixProd b.t i = b.t i * suffixProd b.t i := by
    rw [← h1, mul_assoc, Nat.mul_div_cancel_left _ hA]
  rw [h2]
  have he := shape_even hS i
  have : b.t i * suffixProd b.t i = 2 * ((b.t i / 2) * suffixProd b.t i) := by
    rw [← mul_assoc, he]
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

/-- `U = solRep b i = suffixProd t i`. -/
theorem solRep_eq (b : BrPar) (i : Fin b.d) (hS : ShapeOK b.t) :
    solRep b i = suffixProd b.t i := by
  unfold solRep
  rw [solHalfM_eq b i hS, ← mul_assoc, shape_even hS i]
  exact Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) (hS i).1)

/-- **The parameter row as replicated digit records.** -/
theorem solParamRow_eq (b : BrPar) (i : Fin b.d) (h : ℕ) (g : ℕ → ℤ) (hS : ShapeOK b.t) :
    solParamRow b i h g = (List.range (b.t i / 2)).flatMap
      (fun j => List.replicate (suffixProd b.t i) [(g (solU0 b i h + j), 0)]) := by
  unfold solParamRow
  rw [solHalfM_eq b i hS, solRep_eq b i hS]
  exact range_mul_map_div (fun j => [(g (solU0 b i h + j), 0)]) (suffixProd_pos hS i) _

/-! ## Bits -/

theorem twosBits_zero (w : ℕ) : twosBits w 0 = List.replicate w false := by
  unfold twosBits bitsLE
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun x hx => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  simp

theorem bitsLE_succ_right (w d : ℕ) : bitsLE (w + 1) d = bitsLE w d ++ [d.testBit w] := by
  unfold bitsLE
  rw [List.range_succ, List.map_append]
  rfl

/-- For `d < 2·2^k`, bit `k` of `d` is `2^k ≤ d`. -/
theorem testBit_of_lt_two_mul {d k : ℕ} (hd : d < 2 * 2 ^ k) :
    d.testBit k = decide (2 ^ k ≤ d) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : d / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul hk]; linarith
  by_cases h : 2 ^ k ≤ d
  · have h1 : 1 ≤ d / 2 ^ k := (Nat.le_div_iff_mul_le hk).2 (by linarith)
    have : d / 2 ^ k = 1 := by omega
    simp [this, h]
  · have h0 : d / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    simp [h0, h]

/-- The last bit of the representative of `z mod 2^{k+1}`, for `-2^{k} ≤ z < 2^{k}` scaled: if
`-P ≤ z < P` and `2·P ≤ 2^{k+1}`... stated directly: the sign. -/
theorem testBit_emod_sign {k : ℕ} {z : ℤ} (hlo : -(2 ^ k : ℤ) ≤ z) (hhi : z < 2 ^ k) :
    ((z % (2 ^ (k + 1) : ℤ)).toNat).testBit k = decide (z < 0) := by
  have hP : (0 : ℤ) < 2 ^ k := by positivity
  have h2 : (2 ^ (k + 1) : ℤ) = 2 * 2 ^ k := by ring
  set P : ℤ := 2 ^ k with hPdef
  have hm : z % (2 ^ (k + 1) : ℤ) = if z < 0 then z + 2 * P else z := by
    rw [h2]
    split_ifs with hz
    · have e : (z + 2 * P) % (2 * P) = z % (2 * P) := by
        simpa using Int.add_mul_emod_self_left z (2 * P) 1
      rw [← e]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    · exact Int.emod_eq_of_lt (by omega) (by omega)
  have hlt : ((z % (2 ^ (k + 1) : ℤ)).toNat) < 2 * 2 ^ k := by
    rw [hm]; split_ifs with hz
    · have : (z + 2 * P).toNat < 2 * 2 ^ k := by
        have : ((z + 2 * P).toNat : ℤ) < 2 * 2 ^ k := by
          rw [Int.toNat_of_nonneg (by omega)]; omega
        exact_mod_cast this
      exact this
    · have : ((z.toNat : ℕ) : ℤ) < 2 * 2 ^ k := by
        rw [Int.toNat_of_nonneg (by omega)]; omega
      exact_mod_cast this
  rw [testBit_of_lt_two_mul hlt, hm]
  split_ifs with hz
  · have : (2 ^ k : ℕ) ≤ (z + 2 * P).toNat := by
      have : ((2 ^ k : ℕ) : ℤ) ≤ ((z + 2 * P).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega)]; push_cast; omega
      exact_mod_cast this
    simp [this, hz]
  · have : ¬ (2 ^ k : ℕ) ≤ z.toNat := by
      intro hle
      have : ((2 ^ k : ℕ) : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast hle
      rw [Int.toNat_of_nonneg (by omega)] at this; push_cast at this; omega
    simp [this, hz]

/-- **Sign extension**: for `FitsTwos w z` (`w ≥ 1`), the `(w+1)`-bit field is the `w`-bit field
followed by the sign bit. -/
theorem twosBits_succ_eq_append {w : ℕ} {z : ℤ} (hz : FitsTwos w z) :
    twosBits (w + 1) z = twosBits w z ++ [decide (z < 0)] := by
  obtain ⟨hlo, hhi⟩ := hz
  have hP : (2 : ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (Nat.sub_le w 1)
  unfold twosBits
  rw [bitsLE_succ_right]
  congr 1
  · apply (K1.twosBits_eq_bitsLE ?_).symm
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
    exact Int.emod_emod_of_dvd z (pow_dvd_pow 2 (Nat.le_succ w))
  · rw [testBit_emod_sign (k := w) (by omega) (by omega)]

/-- The last bit of a `w`-bit field (`w ≥ 1`, `FitsTwos w z`) is the sign. -/
theorem twosBits_eq_init_sign {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (hz : FitsTwos w z) :
    twosBits w z = twosBits (w - 1) z ++ [decide (z < 0)] := by
  obtain ⟨hlo, hhi⟩ := hz
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlo hhi ⊢
  unfold twosBits
  rw [bitsLE_succ_right]
  congr 1
  · apply (K1.twosBits_eq_bitsLE ?_).symm
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
    exact Int.emod_emod_of_dvd z (pow_dvd_pow 2 (Nat.le_succ k))
  · rw [testBit_emod_sign hlo hhi]

/-- Negation of a field as the ripple `negBit` (any second operand of the same length). -/
theorem twosBits_neg (w : ℕ) (z : ℤ) :
    twosBits w (-z) = K1.ripOut K1.negBit false (twosBits w z) (twosBits w z) :=
  (K1.ripOut_neg w z z).symm

/-! ## Records -/

theorem crecBits_one (w : ℕ) (c : CInt) : crecBits w [c] = twosBits w c.1 ++ twosBits w c.2 := by
  simp [crecBits, coefBits]

theorem crecBits_solRec {d : ℕ} {t : Fin d → ℕ} (wT P : ℕ) (T : BridgeTables t) (i : Fin d)
    (u : ℕ) :
    crecBits wT (solRec P T i u) =
      twosBits wT (solGMu P T i u) ++ twosBits wT 0 ++ twosBits wT (-(solGNa P T i u)) ++
        twosBits wT 0 ++ twosBits wT (solGGm P T i u) ++ twosBits wT 0 := by
  simp [crecBits, coefBits, solRec, solGMu, solGNa, solGGm, List.append_assoc]

end SubNLogN.Machine.Bridge.SolveParamsAux
