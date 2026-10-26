/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.FFT
import WP.W7k2.Loops

/-!
# K4-TW (`Machine/FFT/PhaseMath.lean`): pure facts for the phase-table builder

**Scope (honest summary).** Pure (machine-free) lemmas, all proved (no `sorry`), linking the
frozen table `phaseTable q ℓ` (`Math/Walsh/PhaseTable.lean`; Lemma 6.1,
`lem:phase-table`) to the integer operations of the builder:
* `gridInt_phaseTable`: the stored numerators are `phaseTableNum q ℓ j`;
* `tabSyms_phaseTable`: the table stack content is `sfx (entrySyms w q ℓ) 0 (2·2^ℓ)` (the shape
  emitted by a count-down loop, `WP/W7k2/Loops.lean`);
* `midHdr_eq`: the header fields `q, D, ℓ, K, w` as stack symbols;
* `tdiv_shrink`: the shrink-and-truncate step `tdiv (a·(2^{q+3}-1)) 2^{q+11}` of
  `phaseTableNum` in sign-magnitude form (shift, subtract, shift; Lemma 6.1, `lem:phase-table`);
* `twosBits_natCast`, `twosBits_neg`: two's-complement fields as unsigned `w`-bit fields;
* `stdChar_natAbs_le`: the IntMul `stdChar` evaluator's outputs are at most `2^{q'+3}` in
  magnitude (from its certified error bound `computableStdCharWithProgramCost_error_le`);
* `root_iff`, `root_quot_lt`: the root test `(2j) mod 2^ℓ = 0` by shifts.
-/

namespace SubNLogN.Machine.FFT.Phase

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Math.Walsh SubNLogN.Math.Common
  SubNLogN.Machine

/-! ## 1. The table entries -/

/-- Table entry `j` as stack symbols: the record `[(re, im)]` of `phaseTableNum q ℓ j` at width
`w` (`recSyms (crecBits w [·])`). -/
def entrySyms (w q ℓ j : ℕ) : List Sym :=
  (twosBits w (phaseTableNum q ℓ j).1 ++ twosBits w (phaseTableNum q ℓ j).2).map Sym.bit ++
    [Sym.sep]

theorem gridInt_phaseTable (q ℓ j : ℕ) : gridInt q (phaseTable q ℓ j) = phaseTableNum q ℓ j := by
  have h2 : gridUnit q * 2 ^ q = 1 := by
    unfold gridUnit; exact inv_mul_cancel₀ (by positivity)
  unfold gridInt phaseTable
  simp only [mul_assoc, h2, mul_one, round_intCast]

theorem tabSyms_phaseTable (w q ℓ : ℕ) :
    tabSyms w q ℓ (phaseTable q ℓ) = sfx (entrySyms w q ℓ) 0 (2 * 2 ^ ℓ) := by
  rw [sfx_zero]
  unfold tabSyms carrSyms arrSyms tabRecs blk
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [entrySyms, recSyms, crecBits, coefBits, gridInt_phaseTable]

/-! ## 2. The header -/

theorem hdrSyms_cons (x : ℕ) (xs : List ℕ) :
    hdrSyms (x :: xs) = natSyms x ++ Sym.mark :: hdrSyms xs := by
  simp [hdrSyms]

theorem midHdr_eq (q ℓ K w : ℕ) {D : ℕ} (a : Fin D → ℕ) :
    midHdr q ℓ K w a = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++
      Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: hdrSyms (List.ofFn a))))) := by
  unfold midHdr
  simp only [List.cons_append, List.nil_append, hdrSyms_cons]

theorem midHdr_length_ge (q ℓ K w : ℕ) {D : ℕ} (a : Fin D → ℕ) :
    bitLen q + bitLen D + bitLen ℓ + bitLen K + bitLen w + 5 ≤ (midHdr q ℓ K w a).length := by
  rw [midHdr_eq]
  simp only [List.length_append, List.length_cons, length_natSyms]
  omega

/-! ## 3. Shrink and truncate -/

/-- The shrunk magnitude `(n·2^{q+3} - n) / 2^{q+11}`. -/
def shrM (q n : ℕ) : ℕ := (n * 2 ^ (q + 3) - n) / 2 ^ (q + 11)

/-- `tdiv (a·(2^{q+3}-1)) 2^{q+11}` with `n = |a|`: sign of `a`, magnitude `shrM q n`. -/
theorem tdiv_shrink (q : ℕ) (a : ℤ) :
    Int.tdiv (a * (2 ^ (q + 3) - 1)) (2 ^ (q + 11)) =
      if a < 0 then -((shrM q a.natAbs : ℕ) : ℤ) else ((shrM q a.natAbs : ℕ) : ℤ) := by
  have h1 : 1 ≤ 2 ^ (q + 3) := Nat.one_le_two_pow
  have hc : (2 : ℤ) ^ (q + 3) - 1 = ((2 ^ (q + 3) - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub h1]; push_cast; ring
  have hd : (2 : ℤ) ^ (q + 11) = ((2 ^ (q + 11) : ℕ) : ℤ) := by push_cast; ring
  have key : shrM q a.natAbs = a.natAbs * (2 ^ (q + 3) - 1) / 2 ^ (q + 11) := by
    unfold shrM; rw [Nat.mul_sub_one]
  rw [key, hc, hd]
  split_ifs with ha
  · have ha' : a = -((a.natAbs : ℕ) : ℤ) := by omega
    rw [ha', neg_mul, Int.neg_tdiv, Int.natAbs_neg, Int.natAbs_natCast, ← Nat.cast_mul,
      ← Int.ofNat_tdiv]
  · have ha' : a = ((a.natAbs : ℕ) : ℤ) := by omega
    rw [ha', Int.natAbs_natCast, ← Nat.cast_mul, ← Int.ofNat_tdiv]

theorem shrink_le (q n : ℕ) (hn : n ≤ 2 ^ (q + 9)) : shrM q n ≤ 2 ^ (q + 1) := by
  unfold shrM
  apply Nat.div_le_of_le_mul
  calc n * 2 ^ (q + 3) - n ≤ n * 2 ^ (q + 3) := Nat.sub_le _ _
    _ ≤ 2 ^ (q + 9) * 2 ^ (q + 3) := Nat.mul_le_mul_right _ hn
    _ = 2 ^ (q + 11) * 2 ^ (q + 1) := by rw [← pow_add, ← pow_add]; ring_nf

/-! ## 4. Two's-complement fields as unsigned fields -/

theorem twosBits_natCast {w M : ℕ} (h : M < 2 ^ w) : twosBits w (M : ℤ) = bitsLE w M := by
  unfold twosBits
  have : (M : ℤ) % 2 ^ w = (M : ℤ) := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h)
  rw [this, Int.toNat_natCast]

theorem twosBits_neg {w M : ℕ} (h1 : 1 ≤ M) (h2 : M ≤ 2 ^ w) :
    twosBits w (-(M : ℤ)) = bitsLE w (2 ^ w - M) := by
  unfold twosBits
  have hp : (0 : ℤ) < 2 ^ w := by positivity
  have e1 : -(M : ℤ) % 2 ^ w = (-(M : ℤ) + 2 ^ w) % 2 ^ w := by rw [Int.add_emod_right]
  have e2 : -(M : ℤ) + 2 ^ w = ((2 ^ w - M : ℕ) : ℤ) := by
    rw [Nat.cast_sub h2]; push_cast; ring
  have e3 : ((2 ^ w - M : ℕ) : ℤ) % 2 ^ w = ((2 ^ w - M : ℕ) : ℤ) := by
    apply Int.emod_eq_of_lt (by positivity)
    have : 2 ^ w - M < 2 ^ w := by omega
    exact_mod_cast this
  rw [e1, e2, e3, Int.toNat_natCast]

/-! ## 5. The `stdChar` evaluator's outputs are small -/

theorem stdChar_natAbs_le (q' num den : ℕ) (hden : 0 < den) (hnum : num ≤ den) :
    ((IntMul.computableStdCharWithProgramCost q' num den false).1.1).natAbs ≤ 2 ^ (q' + 3) ∧
      ((IntMul.computableStdCharWithProgramCost q' num den false).1.2).natAbs ≤ 2 ^ (q' + 3) := by
  set A := (IntMul.computableStdCharWithProgramCost q' num den false).1 with hA
  have herr := IntMul.computableStdCharWithProgramCost_error_le q' num den false hden hnum
  rw [← hA] at herr
  set z := IntMul.toScaledComplex q' A with hz
  set s := IntMul.stdChar ((if false = true then -(num : ℝ) else (num : ℝ)) / (den : ℝ)) with hs
  have hsn : ‖s‖ = 1 := IntMul.norm_stdChar _
  have hq : (2 : ℝ) ^ (-((q' : ℤ) + 2)) ≤ 1 / 4 := by
    rw [zpow_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (q' : ℤ) := one_le_zpow₀ (by norm_num) (by omega)
    rw [zpow_two]
    rw [show (2 : ℝ) ^ (q' : ℤ) * (2 * 2) = 4 * 2 ^ (q' : ℤ) by ring]
    rw [mul_inv, inv_eq_one_div 4, one_div]
    have h2 : ((2 : ℝ) ^ (q' : ℤ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    nlinarith [inv_pos.mpr (show (0 : ℝ) < 4 by norm_num)]
  have hsq : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    · exact Real.sqrt_le_sqrt (by norm_num)
  have hE : 2 * IntMul.complexQuantizeMaxErr q' ≤ 1 := by
    unfold IntMul.complexQuantizeMaxErr
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (-((q' : ℤ) + 2)) := by positivity
    nlinarith [Real.sqrt_nonneg 2]
  have hzn : ‖z‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' z s
    have h3 : ‖z - s‖ ≤ 1 := le_trans herr hE
    linarith [norm_sub_rev z s]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (q' + 2) := by positivity
  have hre : |(A.1 : ℝ)| ≤ 2 ^ (q' + 3) := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : z.re = (A.1 : ℝ) / (2 : ℝ) ^ (q' + 2) := rfl
    rw [h2, abs_div, abs_of_pos hpos] at h1
    rw [div_le_iff₀ hpos] at h1
    calc |(A.1 : ℝ)| ≤ ‖z‖ * 2 ^ (q' + 2) := h1
      _ ≤ 2 * 2 ^ (q' + 2) := mul_le_mul_of_nonneg_right hzn hpos.le
      _ = 2 ^ (q' + 3) := by ring
  have him : |(A.2 : ℝ)| ≤ 2 ^ (q' + 3) := by
    have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have h2 : z.im = (A.2 : ℝ) / (2 : ℝ) ^ (q' + 2) := rfl
    rw [h2, abs_div, abs_of_pos hpos] at h1
    rw [div_le_iff₀ hpos] at h1
    calc |(A.2 : ℝ)| ≤ ‖z‖ * 2 ^ (q' + 2) := h1
      _ ≤ 2 * 2 ^ (q' + 2) := mul_le_mul_of_nonneg_right hzn hpos.le
      _ = 2 ^ (q' + 3) := by ring
  constructor
  · have : ((A.1.natAbs : ℕ) : ℝ) ≤ ((2 ^ (q' + 3) : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; exact hre
    exact_mod_cast this
  · have : ((A.2.natAbs : ℕ) : ℝ) ≤ ((2 ^ (q' + 3) : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; exact him
    exact_mod_cast this

/-! ## 6. The root test -/

theorem root_iff (j ℓ : ℕ) : (2 * j) % 2 ^ ℓ = 0 ↔ j * 2 ^ 1 = j * 2 ^ 1 / 2 ^ ℓ * 2 ^ ℓ := by
  have e : j * 2 ^ 1 = 2 * j := by ring
  rw [e]
  constructor
  · intro h
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm
  · intro h
    have := Nat.mod_add_div (2 * j) (2 ^ ℓ)
    have h2 : 2 ^ ℓ * (2 * j / 2 ^ ℓ) = 2 * j / 2 ^ ℓ * 2 ^ ℓ := Nat.mul_comm _ _
    omega

theorem root_quot_lt (j ℓ : ℕ) (hj : j < 2 * 2 ^ ℓ) : j * 2 ^ 1 / 2 ^ ℓ < 4 := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  have : j * 2 ^ 1 = 2 * j := by ring
  omega

end SubNLogN.Machine.FFT.Phase
