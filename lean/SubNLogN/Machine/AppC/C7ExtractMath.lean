/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7RepairDefs
import SubNLogN.Machine.AppC.C7Addr
import WP.W3s.Math

/-!
# Lemma A.9 extraction, part 2: the value layer (`Machine/AppC/C7ExtractMath.lean`)

Pure arithmetic facts that connect the numbers computed by the extraction kernel
(`C7ExtractStmt`, `Machine/AppC/C7RepairDefs.lean`) to the specification:

* decoding: the three chunk slots of a record index by divisions (`slot0_eq` … `slot2_eq`) and
  the destination `c7Dest` as a Horner rank of the decoded coordinates (`dest_eq`);
* guards: `badB` is the disjunction of the per-segment guard failures of `y` and `z`
  (`badB_eq`, `anyBad`);
* lines: the line sum `lsum` (bit-test form), the packed line in machine form (`packedLine_eq`),
  `packedS0inv` as a fold of the negated lines (`packedS0inv_eq`);
* `T₀`: the selected-bit XOR as one addition and one subtraction of line sums (`xor_mask_eq`);
* keys: `natSyms (d + 2^A)` is the `A`-bit key of `d` followed by a `1` (`natSyms_add_two_pow`),
  and `bitLen = Nat.size` (`bitLen_eq_size`);
* the hole and bank streams as flat maps over the record indices (`holeSyms_holes`,
  `bankSyms_bank`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

Everything here is proved (no `sorry`).
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Contracts Computability SubNLogN.Math.Networks SubNLogN.Machine.AppC.C7Aux
  SubNLogN.Machine.AppC.C7RepairAux.Math SubNLogN.Machine.AppC.Corr SubNLogN.Machine.AppC.C7RadixAux

/-! ## Decoding and re-encoding a record index -/

theorem slot2_eq (L N1 N2 N3 p : ℕ) : c7Slot L N1 N2 N3 2 p = p / N3 % 2 ^ L := rfl

theorem slot1_eq (L N1 N2 N3 p : ℕ) : c7Slot L N1 N2 N3 1 p = p / N3 / 2 ^ L / N2 % 2 ^ L := by
  show p / (N3 * 2 ^ L * N2) % 2 ^ L = _
  simp only [Nat.div_div_eq_div_mul, Nat.mul_assoc]

theorem slot0_eq (L N1 N2 N3 p : ℕ) :
    c7Slot L N1 N2 N3 0 p = p / N3 / 2 ^ L / N2 / 2 ^ L / N1 % 2 ^ L := by
  show p / (N3 * 2 ^ L * N2 * 2 ^ L * N1) % 2 ^ L = _
  simp only [Nat.div_div_eq_div_mul, Nat.mul_assoc]

/-- **The destination in decoded coordinates**: the Horner rank of the decoded spectator
coordinates with the new chunk values. -/
theorem dest_eq (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) (hN1 : 0 < N1)
    (hN2 : 0 < N2) (hN3 : 0 < N3) :
    c7Dest K ρ f N1 N2 N3 σ p = c7Rank (f * K) N1 N2 N3
      (p / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) / N1 / 2 ^ (f * K))
      (p / N3 / 2 ^ (f * K) / N2 / 2 ^ (f * K) % N1) (p / N3 / 2 ^ (f * K) % N2) (p % N3)
      (fun j => nameGet (packedT0 K ρ f (packedS0inv (f * K) K ρ f
        (c7Tri (f * K) N1 N2 N3 σ p))) (σ j)) := by
  unfold c7Dest
  rw [c7Lift_eq hN1 hN2 hN3]
  simp only [Nat.div_div_eq_div_mul, Nat.mul_assoc] <;> rfl

/-! ## Guards -/

/-- Guard segment `i` of the chunk `v` is bad. -/
def segBad (K ρ i v : ℕ) : Bool :=
  decide (guardVal K ρ i v < 10) || decide (2 ^ (K - 1) < guardVal K ρ i v + 11)

/-- Some guard among the first `m` segments of `v` is bad. -/
def anyBad (K ρ v : ℕ) : ℕ → Bool
  | 0 => false
  | m + 1 => anyBad K ρ v m || segBad K ρ m v

theorem anyBad_iff (K ρ v m : ℕ) : anyBad K ρ v m = true ↔
    ∃ i < m, ¬(10 ≤ guardVal K ρ i v ∧ guardVal K ρ i v + 11 ≤ 2 ^ (K - 1)) := by
  induction m with
  | zero => simp [anyBad]
  | succ m ih =>
    rw [show anyBad K ρ v (m + 1) = (anyBad K ρ v m || segBad K ρ m v) from rfl,
      Bool.or_eq_true, ih]
    unfold segBad
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro (⟨i, hi, h⟩ | h | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨m, by omega, by omega⟩
      · exact ⟨m, by omega, by omega⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_ge i m with h' | h'
      · exact Or.inl ⟨i, h', h⟩
      · obtain rfl : i = m := by omega
        right
        omega

/-- **Exceptional records** are those with a bad guard in `y` or in `z`. -/
theorem badB_eq (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (p : ℕ) :
    badB K ρ f N1 N2 N3 σ p = (anyBad K ρ (c7Tri (f * K) N1 N2 N3 σ p).2.1 (f - 1) ||
      anyBad K ρ (c7Tri (f * K) N1 N2 N3 σ p).2.2 (f - 1)) := by
  have hb : badB K ρ f N1 N2 N3 σ p = true ↔
      ¬ packedGood K ρ f (c7Tri (f * K) N1 N2 N3 σ p) := by
    unfold badB
    rw [← goodB_iff]
    cases goodB K ρ f (c7Tri (f * K) N1 N2 N3 σ p) <;> simp
  apply Bool.eq_iff_iff.mpr
  rw [hb, Bool.or_eq_true, anyBad_iff, anyBad_iff]
  generalize c7Tri (f * K) N1 N2 N3 σ p = t
  unfold packedGood
  constructor
  · intro h
    by_contra hc
    apply h
    intro i hi
    have h1 : 10 ≤ guardVal K ρ i t.2.1 ∧ guardVal K ρ i t.2.1 + 11 ≤ 2 ^ (K - 1) := by
      by_contra h1
      exact hc (Or.inl ⟨i, hi, h1⟩)
    have h2 : 10 ≤ guardVal K ρ i t.2.2 ∧ guardVal K ρ i t.2.2 + 11 ≤ 2 ^ (K - 1) := by
      by_contra h2
      exact hc (Or.inr ⟨i, hi, h2⟩)
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  · rintro (⟨i, hi, h1⟩ | ⟨i, hi, h2⟩) hall
    · exact h1 ⟨(hall i hi).1, (hall i hi).2.1⟩
    · exact h2 ⟨(hall i hi).2.2.1, (hall i hi).2.2.2⟩

/-- The guard windows of `v`, by repeated division. -/
theorem guard_div (K ρ i v : ℕ) :
    v / 2 ^ (ρ + i * K + 1) / 2 ^ K = v / 2 ^ (ρ + (i + 1) * K + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  ring

theorem guard_div0 (K ρ v : ℕ) : v / 2 ^ (ρ + 1) = v / 2 ^ (ρ + 0 * K + 1) := by
  simp

/-! ## Line sums and packed lines -/

/-- Line sum in bit-test form: `Σ_{i<m} 2^{ρ+iK} [x_{ρ+iK} = 1 ∧ (o_{ρ+iK} = 1) = par]`. -/
def lsum (K ρ x o : ℕ) (par : Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lsum K ρ x o par m +
      if x / 2 ^ (ρ + m * K) % 2 = 1 ∧ decide (o / 2 ^ (ρ + m * K) % 2 = 1) = par then
        2 ^ (ρ + m * K) else 0

theorem pow_step (K ρ m : ℕ) (hK : 1 ≤ K) : 2 ^ (ρ + m * K) * 2 ≤ 2 ^ (ρ + (m + 1) * K) := by
  rw [← pow_succ]
  exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul, Nat.one_mul]; omega)

theorem lsum_lt (K ρ x o : ℕ) (par : Bool) (hK : 1 ≤ K) :
    ∀ m, lsum K ρ x o par m < 2 ^ (ρ + m * K)
  | 0 => by simp [lsum]
  | m + 1 => by
    have ih := lsum_lt K ρ x o par hK m
    have h2 := pow_step K ρ m hK
    simp only [lsum]
    split_ifs <;> omega

/-- The packed line's offset sum is the line sum (for a parity `par ≤ 1`). -/
theorem offset_eq (K ρ x o par : ℕ) (hpar : par ≤ 1) : ∀ m,
    (∑ i ∈ Finset.range m, (2 : ℤ) ^ (ρ + i * K) *
      (if bitAt x (ρ + i * K) = 1 ∧ bitAt o (ρ + i * K) = par then 1 else 0)) =
      ((lsum K ρ x o (decide (par = 1)) m : ℕ) : ℤ)
  | 0 => by simp [lsum]
  | m + 1 => by
    rw [Finset.sum_range_succ, offset_eq K ρ x o par hpar m]
    have hc : (bitAt x (ρ + m * K) = 1 ∧ bitAt o (ρ + m * K) = par) ↔
        (x / 2 ^ (ρ + m * K) % 2 = 1 ∧
          decide (o / 2 ^ (ρ + m * K) % 2 = 1) = decide (par = 1)) := by
      unfold bitAt
      have hb2 : o / 2 ^ (ρ + m * K) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rcases (show o / 2 ^ (ρ + m * K) % 2 = 0 ∨ o / 2 ^ (ρ + m * K) % 2 = 1 by omega)
          with hb | hb <;>
        rcases (show par = 0 ∨ par = 1 by omega) with hp | hp <;>
        simp [hb, hp] at h2 ⊢
    simp only [lsum]
    by_cases h : x / 2 ^ (ρ + m * K) % 2 = 1 ∧
        decide (o / 2 ^ (ρ + m * K) % 2 = 1) = decide (par = 1)
    · rw [if_pos (hc.mpr h), if_pos h]
      push_cast
      ring
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
      push_cast
      ring

theorem toNat_add_emod (t S L : ℕ) :
    (((t : ℤ) + 1 * ((S : ℕ) : ℤ)) % (2 : ℤ) ^ L).toNat = (t + S) % 2 ^ L := by
  rw [one_mul, show (2 : ℤ) ^ L = ((2 ^ L : ℕ) : ℤ) by norm_num, ← Nat.cast_add,
    ← Int.natCast_mod, Int.toNat_natCast]

theorem toNat_sub_emod (t S L : ℕ) (hS : S ≤ 2 ^ L) :
    (((t : ℤ) + -1 * ((S : ℕ) : ℤ)) % (2 : ℤ) ^ L).toNat = (t + 2 ^ L - S) % 2 ^ L := by
  have e : (t : ℤ) + -1 * (S : ℤ) = ((t + 2 ^ L - S : ℕ) : ℤ) + (-1) * ((2 ^ L : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    ring
  rw [e, show (2 : ℤ) ^ L = ((2 ^ L : ℕ) : ℤ) by norm_num, Int.add_mul_emod_self_right,
    ← Int.natCast_mod, Int.toNat_natCast]

/-- New value of the target chunk under the packed line `op` (machine form): add the line sum,
or add `2^L` and subtract it, then reduce modulo `2^L`. -/
def lineNew (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) (x o t : ℕ) : ℕ :=
  if op.2.1 = 1 then (t + lsum K ρ x o (decide (op.2.2 = 1)) (f - 1)) % 2 ^ L
  else (t + 2 ^ L - lsum K ρ x o (decide (op.2.2 = 1)) (f - 1)) % 2 ^ L

theorem packedLine_unfold (L K ρ f : ℕ) (b : Bool) (ε : ℤ) (par : ℕ) (hpar : par ≤ 1)
    (x y z : ℕ) :
    packedLine L K ρ f (b, ε, par) (x, y, z) =
      if b then
        (x, (((y : ℤ) + ε * ((lsum K ρ x z (decide (par = 1)) (f - 1) : ℕ) : ℤ)) % 2 ^ L).toNat, z)
      else
        (x, y, (((z : ℤ) + ε * ((lsum K ρ x y (decide (par = 1)) (f - 1) : ℕ) : ℤ)) % 2 ^ L).toNat) := by
  cases b <;> simp only [packedLine, Bool.false_eq_true, eq_self_iff_true, if_true, if_false,
    offset_eq K ρ x _ par hpar]

/-- **One packed line in machine form.** -/
theorem packedLine_eq (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) (hop : op.2.1 = 1 ∨ op.2.1 = -1)
    (hpar : op.2.2 ≤ 1) (hK : 1 ≤ K) (hL : ρ + (f - 1) * K ≤ L) (x y z : ℕ) :
    packedLine L K ρ f op (x, y, z) =
      if op.1 then (x, lineNew L K ρ f op x z y, z) else (x, y, lineNew L K ρ f op x y z) := by
  obtain ⟨b, ε, par⟩ := op
  simp only at hop hpar ⊢
  rw [packedLine_unfold L K ρ f b ε par hpar]
  have hlt : ∀ o, lsum K ρ x o (decide (par = 1)) (f - 1) ≤ 2 ^ L := fun o =>
    le_of_lt (lt_of_lt_of_le (lsum_lt K ρ x o _ hK (f - 1))
      (Nat.pow_le_pow_right (by norm_num) hL))
  rcases hop with rfl | rfl
  · simp only [lineNew, toNat_add_emod, eq_self_iff_true, if_true]
  · simp only [lineNew, toNat_sub_emod _ _ _ (hlt _), eq_false (show ¬((-1 : ℤ) = 1) by decide),
      if_false]

/-- The negated line `(b, -ε, par)` (the lines of `S₀⁻¹`). -/
def negL (op : Bool × ℤ × ℕ) : Bool × ℤ × ℕ := (op.1, -op.2.1, op.2.2)

theorem packedS0inv_eq (L K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) :
    SubNLogN.Machine.AppC.C7Aux.packedS0inv L K ρ f xyz =
      (eightOps.reverse.map negL).foldl (fun p op => packedLine L K ρ f op p) xyz := by
  rw [List.foldl_map]
  rfl

theorem negL_ok : ∀ op ∈ eightOps.reverse.map negL, (op.2.1 = 1 ∨ op.2.1 = -1) ∧ op.2.2 ≤ 1 := by
  decide

/-! ## `T₀` as one addition and one subtraction -/

theorem xor_two_pow_of_false {z j : ℕ} (h : z.testBit j = false) : z ^^^ 2 ^ j = z + 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h0 : z / 2 ^ j % 2 = 0 := by
    have h2 := Nat.mod_lt (z / 2 ^ j) (show 0 < 2 by norm_num)
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not] at h
    omega
  have hmod : z % 2 ^ (j + 1) < 2 ^ j := by
    rw [Nat.mod_pow_succ, h0, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_lt _ (Nat.two_pow_pos j)
  have e : z + 2 ^ j = 2 ^ (j + 1) * (z / 2 ^ (j + 1)) + (2 ^ j + z % 2 ^ (j + 1)) := by
    have := Nat.div_add_mod z (2 ^ (j + 1))
    omega
  have hlt : 2 ^ j + z % 2 ^ (j + 1) < 2 ^ (j + 1) := by
    calc 2 ^ j + z % 2 ^ (j + 1) < 2 ^ j + 2 ^ j := by omega
      _ = 2 ^ (j + 1) := by ring
  rw [e, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hij : i < j + 1
  · rw [if_pos hij]
    rcases Nat.lt_or_ge i j with hi | hi
    · rw [Nat.testBit_two_pow_add_gt hi, Nat.testBit_mod_two_pow]
      simp [hij, show j ≠ i by omega]
    · obtain rfl : i = j := by omega
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_mod_two_pow]
      simp [h]
  · rw [if_neg hij, Nat.testBit_div_two_pow, show i - (j + 1) + (j + 1) = i by omega]
    simp [show j ≠ i by omega]

theorem xor_two_pow_of_true {z j : ℕ} (h : z.testBit j = true) : z ^^^ 2 ^ j = z - 2 ^ j := by
  have hw : (z ^^^ 2 ^ j).testBit j = false := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self, h]
    rfl
  have e := xor_two_pow_of_false hw
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at e
  omega

/-- The selected mask of `x` over the first `m` segments. -/
def selMaskM (K ρ x : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => selMaskM K ρ x m + 2 ^ (ρ + m * K) * bitAt x (ρ + m * K)

theorem selMaskM_eq (K ρ x m : ℕ) :
    selMaskM K ρ x m = ∑ i ∈ Finset.range m, 2 ^ (ρ + i * K) * bitAt x (ρ + i * K) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.sum_range_succ, ← ih]; rfl

theorem selMaskM_lt (K ρ x : ℕ) (hK : 1 ≤ K) : ∀ m, selMaskM K ρ x m < 2 ^ (ρ + m * K)
  | 0 => by simp [selMaskM]
  | m + 1 => by
    have ih := selMaskM_lt K ρ x hK m
    have h2 := pow_step K ρ m hK
    have hb : bitAt x (ρ + m * K) ≤ 1 := by unfold bitAt; omega
    have h3 : 2 ^ (ρ + m * K) * bitAt x (ρ + m * K) ≤ 2 ^ (ρ + m * K) := by nlinarith
    simp only [selMaskM]
    omega

/-- **`T₀` in machine form**: XOR with the selected mask is one addition and one subtraction of
line sums (bits where `y` is `0`, resp. `1`). -/
theorem xor_mask_eq (K ρ x y : ℕ) (hK : 1 ≤ K) : ∀ m,
    y ^^^ selMaskM K ρ x m = y + lsum K ρ x y false m - lsum K ρ x y true m ∧
      lsum K ρ x y true m ≤ y + lsum K ρ x y false m
  | 0 => by simp [selMaskM, lsum]
  | m + 1 => by
    obtain ⟨ih, hle⟩ := xor_mask_eq K ρ x y hK m
    have hMlt := selMaskM_lt K ρ x hK m
    have hMj : (selMaskM K ρ x m).testBit (ρ + m * K) = false := Nat.testBit_lt_two_pow hMlt
    simp only [selMaskM, lsum]
    by_cases hx : x / 2 ^ (ρ + m * K) % 2 = 1
    · have hb : bitAt x (ρ + m * K) = 1 := hx
      rw [hb, Nat.mul_one, ← xor_two_pow_of_false hMj, ← Nat.xor_assoc, ih]
      have hz : (y + lsum K ρ x y false m - lsum K ρ x y true m).testBit (ρ + m * K) =
          y.testBit (ρ + m * K) := by
        rw [← ih, Nat.testBit_xor, hMj, Bool.xor_false]
      by_cases hy : y / 2 ^ (ρ + m * K) % 2 = 1
      · have hyt : y.testBit (ρ + m * K) = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq]; simp [hy]
        rw [xor_two_pow_of_true (hz.trans hyt)]
        have hge := Nat.ge_two_pow_of_testBit (hz.trans hyt)
        have e1 : (if x / 2 ^ (ρ + m * K) % 2 = 1 ∧
            decide (y / 2 ^ (ρ + m * K) % 2 = 1) = false then 2 ^ (ρ + m * K) else 0) = 0 :=
          if_neg (by simp [hy])
        have e2 : (if x / 2 ^ (ρ + m * K) % 2 = 1 ∧
            decide (y / 2 ^ (ρ + m * K) % 2 = 1) = true then 2 ^ (ρ + m * K) else 0) =
            2 ^ (ρ + m * K) := if_pos (by simp [hx, hy])
        rw [e1, e2]
        constructor <;> omega
      · have hyf : y.testBit (ρ + m * K) = false := by
          rw [Nat.testBit_eq_decide_div_mod_eq]; simp [hy]
        rw [xor_two_pow_of_false (hz.trans hyf)]
        have e1 : (if x / 2 ^ (ρ + m * K) % 2 = 1 ∧
            decide (y / 2 ^ (ρ + m * K) % 2 = 1) = false then 2 ^ (ρ + m * K) else 0) =
            2 ^ (ρ + m * K) := if_pos (by simp [hx, hy])
        have e2 : (if x / 2 ^ (ρ + m * K) % 2 = 1 ∧
            decide (y / 2 ^ (ρ + m * K) % 2 = 1) = true then 2 ^ (ρ + m * K) else 0) = 0 :=
          if_neg (by simp [hy])
        rw [e1, e2]
        constructor <;> omega
    · have hb : bitAt x (ρ + m * K) = 0 := by unfold bitAt; omega
      rw [hb, Nat.mul_zero, Nat.add_zero, ih, if_neg (by simp [hx]), if_neg (by simp [hx])]
      exact ⟨by omega, by omega⟩

theorem packedT0_eq (K ρ f : ℕ) (hK : 1 ≤ K) (x y z : ℕ) :
    packedT0 K ρ f (x, y, z) =
      (x, y + lsum K ρ x y false (f - 1) - lsum K ρ x y true (f - 1), z) := by
  show (x, Nat.xor y _, z) = _
  rw [Nat.xor_eq, ← selMaskM_eq, (xor_mask_eq K ρ x y hK (f - 1)).1]

/-! ## Keys -/

theorem bitsLE_zero' (A : ℕ) : bitsLE A 0 = List.replicate A false := by
  rw [List.eq_replicate_iff]
  simp [bitsLE]

theorem bitsLE_eq_encodeNat : ∀ (A d : ℕ), d < 2 ^ A →
    bitsLE A d = encodeNat d ++ List.replicate (A - bitLen d) false
  | 0, d, hd => by
    obtain rfl : d = 0 := by simpa using hd
    simp [bitsLE, TMFw.W3s.bitLen_zero, encodeNat_zero]
  | A + 1, d, hd => by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [bitsLE_zero', encodeNat_zero, TMFw.W3s.bitLen_zero]
      rfl
    · have hsucc : bitsLE (A + 1) d = d.testBit 0 :: bitsLE A (d / 2) := by
        simp only [bitsLE, List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        refine List.map_congr_left (fun i _ => ?_)
        simp [Nat.testBit_div_two]
      rw [hsucc, TMFw.W3s.encodeNat_pos d hpos, TMFw.W3s.bitLen_pos d hpos,
        bitsLE_eq_encodeNat A (d / 2) (by rw [Nat.pow_succ] at hd; omega), Nat.testBit_zero]
      simp only [List.cons_append]
      rw [show A + 1 - (bitLen (d / 2) + 1) = A - bitLen (d / 2) by omega]

/-- **The key stream**: `natSyms (d + 2^A)` is the `A`-bit key of `d`, then a `1`. -/
theorem natSyms_add_two_pow (A d : ℕ) (hd : d < 2 ^ A) :
    natSyms (d + 2 ^ A) = (bitsLE A d).map Sym.bit ++ [Sym.bit true] := by
  have h := TMFw.W3s.encodeNat_concat d 1 A one_ne_zero hd
  rw [Nat.one_mul, show encodeNat 1 = [true] from rfl] at h
  rw [natSyms, h, bitsLE_eq_encodeNat A d hd]
  simp

theorem natSyms_two_pow (A : ℕ) :
    natSyms (2 ^ A) = List.replicate A (Sym.bit false) ++ [Sym.bit true] := by
  have h := natSyms_add_two_pow A 0 (Nat.two_pow_pos A)
  rw [Nat.zero_add, bitsLE_zero'] at h
  rw [h, List.map_replicate]

theorem bitLen_eq_size (n : ℕ) : bitLen n = Nat.size n :=
  le_antisymm (TMFw.W3s.bitLen_le_of_lt (Nat.lt_size_self n))
    (Nat.size_le.mpr (TMFw.W3s.lt_two_pow_bitLen n))

/-! ## The hole and bank streams -/

/-- The hole-stream segment of record `p`. -/
def hseg (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (w : List (List Bool)) (p : ℕ) :
    List Sym :=
  if badB K ρ f N1 N2 N3 σ p then [Sym.tag 8] else SubNLogN.Machine.recSyms (w.getD p default)

/-- The bank-stream segment of record `q`. -/
def bseg (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (A : ℕ) (w : List (List Bool))
    (q : ℕ) : List Sym :=
  if badB K ρ f N1 N2 N3 σ q then
    keyedSyms (bitsLE A (c7Dest K ρ f N1 N2 N3 σ q), w.getD q default)
  else []

theorem holeSyms_holes (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (w : List (List Bool)) :
    holeSyms (holes K ρ f N1 N2 N3 σ w) =
      (List.range w.length).flatMap (hseg K ρ f N1 N2 N3 σ w) := by
  unfold holeSyms holes
  rw [List.flatMap_map]
  congr 1
  funext p
  unfold hseg
  split_ifs <;> rfl

theorem flatMap_filter_map {α β γ : Type} (l : List α) (p : α → Bool) (g : α → β)
    (h : β → List γ) :
    ((l.filter p).map g).flatMap h = l.flatMap (fun a => if p a then h (g a) else []) := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases ha : p a <;> simp [List.filter_cons, ha, ih]

theorem bankSyms_bank (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (A : ℕ)
    (w : List (List Bool)) :
    bankSyms (bank K ρ f N1 N2 N3 σ A w) =
      (List.range w.length).flatMap (bseg K ρ f N1 N2 N3 σ A w) := by
  unfold bankSyms bank
  rw [flatMap_filter_map]
  rfl

theorem flatMap_drop_succ {β : Type} (F : ℕ → List β) (M n : ℕ) (hn : n < M) :
    ((List.range M).drop n).flatMap F = F n ++ ((List.range M).drop (n + 1)).flatMap F := by
  rw [List.drop_eq_getElem_cons (by simpa using hn), List.flatMap_cons, List.getElem_range]

/-! ## The reversed array buffer -/

theorem arrSyms_take_succ (w : List (List Bool)) (n : ℕ) (hn : n < w.length) :
    SubNLogN.Machine.arrSyms (w.take (n + 1)) =
      SubNLogN.Machine.arrSyms (w.take n) ++ SubNLogN.Machine.recSyms w[n] := by
  have h : w.take (n + 1) = w.take n ++ [w[n]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hn]
    rfl
  rw [h]
  simp only [SubNLogN.Machine.arrSyms, blk, List.map_append, List.flatten_append, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem rev_arr_take_succ (w : List (List Bool)) (n : ℕ) (hn : n < w.length) (X : List Sym) :
    (SubNLogN.Machine.arrSyms (w.take (n + 1))).reverse ++ X =
      Sym.sep :: ((w[n]).map Sym.bit).reverse ++ ((SubNLogN.Machine.arrSyms (w.take n)).reverse ++ X) := by
  rw [arrSyms_take_succ w n hn]
  simp [SubNLogN.Machine.recSyms]

theorem rev_arr_sep (l : List (List Bool)) (X : List Sym) :
    ∃ Y, (SubNLogN.Machine.arrSyms l).reverse ++ Sym.sep :: X = Sym.sep :: Y := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', r, rfl⟩
  · exact ⟨X, by simp [SubNLogN.Machine.arrSyms, blk]⟩
  · refine ⟨((r.map Sym.bit).reverse ++
      ((SubNLogN.Machine.arrSyms l').reverse ++ Sym.sep :: X)), ?_⟩
    simp [SubNLogN.Machine.arrSyms, blk, SubNLogN.Machine.recSyms]

end SubNLogN.Machine.AppC.C7ExtractAux
