import IntMul.TMStages

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform Delimited-Frame Slot Packing/Unpacking & Base-Case Arithmetic Stages (`IntMul.TMArithStages`)

This module builds the base-case arithmetic and signed Kronecker bit-manipulation stages on top of
`IntMul.TMStages` for the uniform 8-stack binary machine (`Turing.FinTM2`; see Section 3.3 (`sec:tables`), Lemma 6.2 (`lem:kronecker`), and Section 8 (`sec:lean`)):

1. **Signed Kronecker Slot Bit-List Packer (`bmPackSignedSlotsBits`, Stage 30)**:
   Single-pass $O(m \cdot B_{\text{slot}})$ two's-complement bit-list slot packer computing
   `packSignedSlotsBits B_slot cs.length cs` on `kIO`.
2. **Signed Kronecker Slot Bit-List Unpacker (`bmUnpackSignedSlotsBits`, Stage 31)**:
   Single-pass $O(m \cdot B_{\text{slot}} + |bs|)$ two's-complement bit-list slot unpacker computing
   `encList (encodeSignedWord B_slot) (unpackSignedSlotsBits B_slot m bs)` on `kIO`.
3. **Shift-and-Add Unsigned Word Multiplier (`bmShiftAddMulBits`, Stage 32)**:
   $O(w^2)$ bit-by-bit shift-and-add multiplier computing `encodeNatBits (2 * w) (a * b)` on `kIO`.
4. **Restoring Binary Division (`bmRestoringDivMod`, Stage 33)**:
   $O(w^2)$ bit-by-bit restoring division computing
   `(encodeNatBits w (a / b), encodeNatBits w (a % b))` on `kIO`.
5. **Restoring Binary Square Root (`bmRestoringSqrt`, Stage 34)**:
   $O(w^2)$ bit-by-bit restoring square root computing `encodeNatBits (w + 1) m.sqrt` on `kIO`.
-/

namespace IntMul

open Turing

/-! ## 1. Signed Kronecker Slot Bit-List Packer (`bmPackSignedSlotsBits`, Stage 30) -/

theorem encodeNatBits_succ_mod_div (w x : ℕ) :
    encodeNatBits (w + 1) x = decide (x % 2 = 1) :: encodeNatBits w (x / 2) := by
  rw [encodeNatBits_succ_eq, Nat.testBit_zero]

theorem encodeNatBits_add_mod_div (w1 w2 x : ℕ) :
    encodeNatBits (w1 + w2) x =
      encodeNatBits w1 (x % 2 ^ w1) ++ encodeNatBits w2 (x / 2 ^ w1) := by
  rw [encodeNatBits_add w1 w2 x, encodeNatBits_mod_two_pow_of_le (le_refl w1) x]

theorem encodeNatBits_two_pow_sub_one :
    ∀ w : ℕ, encodeNatBits w (2 ^ w - 1) = List.replicate w true
  | 0 => rfl
  | w + 1 => by
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    have hmod : (2 ^ (w + 1) - 1) % 2 = 1 := by
      rw [Nat.pow_succ]
      omega
    have hdiv : (2 ^ (w + 1) - 1) / 2 = 2 ^ w - 1 := by
      rw [Nat.pow_succ]
      omega
    rw [encodeNatBits_succ_mod_div, hmod, hdiv, encodeNatBits_two_pow_sub_one w,
      List.replicate_succ]
    rfl

theorem encodeNatBits_one_succ (d : ℕ) :
    encodeNatBits (d + 1) 1 = true :: List.replicate d false := by
  rw [encodeNatBits_succ_mod_div]
  simp [encodeNatBits_zero]

/-- For any carry `carry ∈ {-1, 0, 1}` (`encodeSignedWord 1 carry = [b0, b1]`) and `d : ℕ`,
`encodeSignedWord (d + 1) carry = b0 :: (List.replicate d (!b1) ++ [b1])`. -/
theorem encodeSignedWord_succ_of_carry (d : ℕ) (carry : ℤ)
    (h1 : -1 ≤ carry) (h2 : carry ≤ 1) :
    let w1 := encodeSignedWord 1 carry
    let b0 := w1.headD false
    let b1 := w1.tail.headD false
    w1 = [b0, b1] ∧
      b0 :: (List.replicate d (!b1) ++ [b1]) = encodeSignedWord (d + 1) carry := by
  have hcases : carry = -1 ∨ carry = 0 ∨ carry = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · have hw1 : encodeSignedWord 1 (-1) = [true, false] := by decide
    refine ⟨by simp [hw1], ?_⟩
    simp only [hw1, List.headD_cons, List.tail_cons, Bool.not_false]
    unfold encodeSignedWord
    have htoNat : (-1 + (2 : ℤ) ^ (d + 1)).toNat = 2 ^ (d + 1) - 1 := by
      have hp : (1 : ℤ) ≤ (2 : ℤ) ^ (d + 1) := one_le_pow₀ (by norm_num)
      zify [Nat.one_le_two_pow]
      omega
    have hlt : 2 ^ (d + 1) - 1 < 2 ^ (d + 1) := by
      have hp : 0 < 2 ^ (d + 1) := Nat.two_pow_pos (d + 1)
      omega
    rw [htoNat, show d + 1 + 1 = (d + 1) + 1 from rfl,
      encodeNatBits_add_mod_div (d + 1) 1 (2 ^ (d + 1) - 1),
      Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt,
      encodeNatBits_two_pow_sub_one (d + 1), List.replicate_succ, List.cons_append]
    rfl
  · have hw1 : encodeSignedWord 1 0 = [false, true] := by decide
    refine ⟨by simp [hw1], ?_⟩
    simp only [hw1, List.headD_cons, List.tail_cons, Bool.not_true]
    unfold encodeSignedWord
    have htoNat : (0 + (2 : ℤ) ^ (d + 1)).toNat = 2 ^ (d + 1) := by
      have hp : (0 : ℤ) ≤ 0 + (2 : ℤ) ^ (d + 1) := by positivity
      zify
      rw [Int.toNat_of_nonneg hp, zero_add]
    rw [htoNat, show d + 1 + 1 = (d + 1) + 1 from rfl,
      encodeNatBits_add_mod_div (d + 1) 1 (2 ^ (d + 1)),
      Nat.mod_self, Nat.div_self (Nat.two_pow_pos (d + 1)),
      encodeNatBits_zero (d + 1), List.replicate_succ, List.cons_append]
    rfl
  · have hw1 : encodeSignedWord 1 1 = [true, true] := by decide
    refine ⟨by simp [hw1], ?_⟩
    simp only [hw1, List.headD_cons, List.tail_cons, Bool.not_true]
    unfold encodeSignedWord
    have htoNat : (1 + (2 : ℤ) ^ (d + 1)).toNat = 1 + 2 ^ (d + 1) := by
      have hp : (0 : ℤ) ≤ 1 + (2 : ℤ) ^ (d + 1) := by positivity
      zify
      rw [Int.toNat_of_nonneg hp]
    have hlt : 1 < 2 ^ (d + 1) := by
      calc 1 < 2 ^ 1 := by decide
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hmod : (1 + 2 ^ (d + 1)) % 2 ^ (d + 1) = 1 := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    have hdiv : (1 + 2 ^ (d + 1)) / 2 ^ (d + 1) = 1 := by
      have : 1 + 2 ^ (d + 1) = 1 + 2 ^ (d + 1) * 1 := by ring
      rw [this, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (d + 1)),
        Nat.div_eq_of_lt hlt, Nat.zero_add]
    rw [htoNat, show d + 1 + 1 = (d + 1) + 1 from rfl,
      encodeNatBits_add_mod_div (d + 1) 1 (1 + 2 ^ (d + 1)),
      hmod, hdiv, encodeNatBits_one_succ d, List.cons_append]
    rfl

theorem fitsSignedWord_of_carry {B_slot : ℕ} (hB : 1 ≤ B_slot) {carry : ℤ}
    (h1 : -1 ≤ carry) (h2 : carry ≤ 1) :
    FitsSignedWord B_slot carry := by
  unfold FitsSignedWord
  have hp : (2 : ℤ) ≤ (2 : ℤ) ^ B_slot := by
    calc (2 : ℤ) = (2 : ℤ) ^ 1 := rfl
      _ ≤ (2 : ℤ) ^ B_slot := pow_le_pow_right₀ (by norm_num) hB
  rw [_root_.abs_lt]
  omega

/-- Splitting `encodeSignedWord (B_slot + 1) (c + carry)` at bit `B_slot` yields the unsigned slot
word `encodeNatBits B_slot ((c + carry) % 2 ^ B_slot).toNat` and the 1-bit signed carry word
`encodeSignedWord 1 ((c + carry) / 2 ^ B_slot)`. -/
theorem encodeSignedWord_succ_split {B_slot : ℕ} (hB : 1 ≤ B_slot)
    {c carry : ℤ} (hc : FitsSignedWord B_slot c) (h1 : -1 ≤ carry) (h2 : carry ≤ 1) :
    let total := c + carry
    let rem := (total % ((2 : ℤ) ^ B_slot)).toNat
    let carry' := total / ((2 : ℤ) ^ B_slot)
    (-1 ≤ carry' ∧ carry' ≤ 1) ∧
      encodeSignedWord (B_slot + 1) total =
        encodeNatBits B_slot rem ++ encodeSignedWord 1 carry' := by
  intro total rem carry'
  set M : ℤ := (2 : ℤ) ^ B_slot
  have hM_pos : 0 < M := by positivity
  have hM_ge2 : 2 ≤ M := by
    dsimp [M]
    calc (2 : ℤ) = (2 : ℤ) ^ 1 := rfl
      _ ≤ (2 : ℤ) ^ B_slot := pow_le_pow_right₀ (by norm_num) hB
  have hc_lo : -M < c := hc.neg_pow_lt
  have hc_hi : c < M := hc.lt_pow
  have hrem_nn : 0 ≤ total % M := Int.emod_nonneg total (ne_of_gt hM_pos)
  have hrem_lt : total % M < M := Int.emod_lt_of_pos total hM_pos
  have hdiv_mod : total % M + M * carry' = total := Int.emod_add_mul_ediv total M
  have hcarry'_bounds : -1 ≤ carry' ∧ carry' ≤ 1 := by
    constructor <;> nlinarith
  refine ⟨hcarry'_bounds, ?_⟩
  unfold encodeSignedWord
  have hrem_nat_lt : rem < 2 ^ B_slot := by
    zify
    rw [Int.toNat_of_nonneg hrem_nn]
    exact hrem_lt
  have hsum_nat :
      (total + (2 : ℤ) ^ (B_slot + 1)).toNat =
        rem + 2 ^ B_slot * (carry' + (2 : ℤ) ^ 1).toNat := by
    have hnn1 : 0 ≤ total + (2 : ℤ) ^ (B_slot + 1) := by
      rw [pow_succ]
      change 0 ≤ total + M * 2
      omega
    have hnn2 : 0 ≤ carry' + (2 : ℤ) ^ 1 := by omega
    zify
    rw [Int.toNat_of_nonneg hnn1, Int.toNat_of_nonneg hrem_nn, Int.toNat_of_nonneg hnn2]
    change total + M * 2 = total % M + M * (carry' + 2)
    linarith
  have hmod : (rem + 2 ^ B_slot * (carry' + (2 : ℤ) ^ 1).toNat) % 2 ^ B_slot = rem := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_nat_lt]
  have hdiv : (rem + 2 ^ B_slot * (carry' + (2 : ℤ) ^ 1).toNat) / 2 ^ B_slot =
      (carry' + (2 : ℤ) ^ 1).toNat := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos B_slot),
      Nat.div_eq_of_lt hrem_nat_lt, Nat.zero_add]
  rw [hsum_nat, show B_slot + 1 + 1 = B_slot + 2 from rfl,
    encodeNatBits_add_mod_div B_slot 2, hmod, hdiv]

/-- Sign-extension gadget converting `encodeSignedWord 1 carry` (`kIO`) into
`encodeSignedWord (d + 1) carry` (`kIO`) using `encodeDelimWord (encUnary d)` on `kWork3`
in `≤ 4 * d + 11` `TM2.step` transitions. -/
def tmSignExtendCarry1 : BitMachine :=
  (tmPushEmpty kWork1).seq
    ((tmPopBitOrZero kIO kWork1).seq
      ((BitMachine.branchDelimBit kIO
          ((tmPushBitWord false kIO).seq
            ((tmDupWord kWork3 kWork0 kSched).seq
              ((tmConsBit true kIO).loopDelimWord kSched)))
          ((tmPushBitWord true kIO).seq
            ((tmDupWord kWork3 kWork0 kSched).seq
              ((tmConsBit false kIO).loopDelimWord kSched)))).seq
        (tmConcatRevWord kWork1 kIO)))

theorem tmSignExtendCarry1_computesInTime (d : ℕ) (carry : ℤ)
    (h1 : -1 ≤ carry) (h2 : carry ≤ 1)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 4 * d + 11,
      tmSignExtendCarry1.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord 1 carry))
          [] [] tW2 (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (d + 1) carry))
          [] [] tW2 (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch) t := by
  rcases encodeSignedWord_succ_of_carry d carry h1 h2 with ⟨hw1, hext⟩
  set b0 := (encodeSignedWord 1 carry).headD false
  set b1 := (encodeSignedWord 1 carry).tail.headD false
  rw [hw1, ← hext]
  cases hb1 : b1 with
  | false =>
    have s1 := tmPushEmpty_computesInTime kWork1
      (mkTapes8 (encodeDelimWord [b0, false]) [] [] tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, mkTapes8_kWork1, List.append_nil] at s1
    have s2 := tmPopBitOrZero_computesInTime kIO kWork1 (by decide)
      [b0, false] [] [] []
      (mkTapes8 [] [] [] tW2 (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
      List.headD_cons, List.tail_cons] at s2
    have c1 := tmPushBitWord_computesInTime false kIO
      (mkTapes8 [] [] (encodeDelimWord [b0]) tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at c1
    have c2 := tmDupWord_computesInTime kWork3 kWork0 kSched (by decide) (by decide) (by decide)
      (encUnary d) tW3 [] tSch
      (mkTapes8 (encodeDelimWord [false]) [] (encodeDelimWord [b0]) tW2 [] tW4 tW5 [])
    simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kSched,
      length_encUnary] at c2
    have c3 := consBit_loopDelimWord_computesInTime true kSched kIO (by decide)
      (encUnary d) tSch [false] []
      (mkTapes8 [] [] (encodeDelimWord [b0]) tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 [])
    simp only [update_mkTapes8_kSched, update_mkTapes8_kIO, List.append_nil,
      length_encUnary] at c3
    have br := BitMachine.ComputesInTime.branchDelimBit kIO
      (M_false := (tmPushBitWord false kIO).seq
        ((tmDupWord kWork3 kWork0 kSched).seq ((tmConsBit true kIO).loopDelimWord kSched)))
      (M_true := (tmPushBitWord true kIO).seq
        ((tmDupWord kWork3 kWork0 kSched).seq ((tmConsBit false kIO).loopDelimWord kSched)))
      false []
      (T₁ := mkTapes8 [] [] (encodeDelimWord [b0]) tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
      (by simpa only [update_mkTapes8_kIO, Bool.false_eq_true, ↓reduceIte] using c1.seq (c2.seq c3))
    simp only [update_mkTapes8_kIO, List.append_nil] at br
    have s4 := tmConcatRevWord_computesInTime kWork1 kIO (by decide)
      [b0] (List.replicate d true ++ [false]) [] []
      (mkTapes8 [] [] [] tW2 (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.reverse_singleton,
      List.singleton_append, List.length_singleton, List.append_nil] at s4
    exact ⟨_, by omega, s1.seq (s2.seq (br.seq s4))⟩
  | true =>
    have s1 := tmPushEmpty_computesInTime kWork1
      (mkTapes8 (encodeDelimWord [b0, true]) [] [] tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, mkTapes8_kWork1, List.append_nil] at s1
    have s2 := tmPopBitOrZero_computesInTime kIO kWork1 (by decide)
      [b0, true] [] [] []
      (mkTapes8 [] [] [] tW2 (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
      List.headD_cons, List.tail_cons] at s2
    have c1 := tmPushBitWord_computesInTime true kIO
      (mkTapes8 [] [] (encodeDelimWord [b0]) tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at c1
    have c2 := tmDupWord_computesInTime kWork3 kWork0 kSched (by decide) (by decide) (by decide)
      (encUnary d) tW3 [] tSch
      (mkTapes8 (encodeDelimWord [true]) [] (encodeDelimWord [b0]) tW2 [] tW4 tW5 [])
    simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kSched,
      length_encUnary] at c2
    have c3 := consBit_loopDelimWord_computesInTime false kSched kIO (by decide)
      (encUnary d) tSch [true] []
      (mkTapes8 [] [] (encodeDelimWord [b0]) tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 [])
    simp only [update_mkTapes8_kSched, update_mkTapes8_kIO, List.append_nil,
      length_encUnary] at c3
    have br := BitMachine.ComputesInTime.branchDelimBit kIO
      (M_false := (tmPushBitWord false kIO).seq
        ((tmDupWord kWork3 kWork0 kSched).seq ((tmConsBit true kIO).loopDelimWord kSched)))
      (M_true := (tmPushBitWord true kIO).seq
        ((tmDupWord kWork3 kWork0 kSched).seq ((tmConsBit false kIO).loopDelimWord kSched)))
      true []
      (T₁ := mkTapes8 [] [] (encodeDelimWord [b0]) tW2
        (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
      (by simpa only [update_mkTapes8_kIO, ↓reduceIte] using c1.seq (c2.seq c3))
    simp only [update_mkTapes8_kIO, List.append_nil] at br
    have s4 := tmConcatRevWord_computesInTime kWork1 kIO (by decide)
      [b0] (List.replicate d false ++ [true]) [] []
      (mkTapes8 [] [] [] tW2 (encodeDelimWord (encUnary d) ++ tW3) tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.reverse_singleton,
      List.singleton_append, List.length_singleton, List.append_nil] at s4
    exact ⟨_, by omega, s1.seq (s2.seq (br.seq s4))⟩

/-- Pure step function for `bmPackSignedSlotsBits` over bounded signed slots. -/
def packSlotSubStep (B_slot : ℕ) (c : { x : ℤ // FitsSignedWord B_slot x })
    (st : { q : ℤ // -1 ≤ q ∧ q ≤ 1 } × List Bool) :
    { q : ℤ // -1 ≤ q ∧ q ≤ 1 } × List Bool :=
  let total : ℤ := c.1 + st.1.1
  let rem : ℕ := (total % ((2 : ℤ) ^ B_slot)).toNat
  let carry' : ℤ := total / ((2 : ℤ) ^ B_slot)
  have hcarry' : -1 ≤ carry' ∧ carry' ≤ 1 := by
    by_cases hB : 1 ≤ B_slot
    · exact (encodeSignedWord_succ_split hB c.2 st.1.2.1 st.1.2.2).1
    · have hB0 : B_slot = 0 := by omega
      subst hB0
      have hc0 : c.1 = 0 := by
        have h := c.2
        unfold FitsSignedWord at h
        rw [_root_.abs_lt] at h
        omega
      dsimp [carry', total]
      rw [hc0]
      have hq := st.1.2
      omega
  (⟨carry', hcarry'⟩, (encodeNatBits B_slot rem).reverse ++ st.2)

theorem loopListFinalState_packSlotSubStep_spec (B_slot : ℕ) :
    ∀ (cs : List { x : ℤ // FitsSignedWord B_slot x })
      (carry : { q : ℤ // -1 ≤ q ∧ q ≤ 1 }) (accRev : List Bool),
      let stF := loopListFinalState (packSlotSubStep B_slot) cs (carry, accRev)
      stF.2.reverse =
        accRev.reverse ++
          (packSignedSlotsBitsAux B_slot cs.length (cs.map Subtype.val) carry.1).1
  | [], carry, accRev => by
    simp [packSignedSlotsBitsAux]
  | c :: cs, carry, accRev => by
    dsimp only
    rw [loopListFinalState_cons]
    have ih := loopListFinalState_packSlotSubStep_spec B_slot cs
      (packSlotSubStep B_slot c (carry, accRev)).1
      (packSlotSubStep B_slot c (carry, accRev)).2
    dsimp only at ih
    rw [ih]
    dsimp only [packSlotSubStep, List.length_cons, List.map_cons, packSignedSlotsBitsAux,
      List.headD_cons, List.tail_cons]
    simp [List.reverse_append, List.reverse_reverse, List.append_assoc]

theorem loopListStepsAux_packSlotSubStep_le (B_slot : ℕ) :
    ∀ (cs : List { x : ℤ // FitsSignedWord B_slot x })
      (st : { q : ℤ // -1 ≤ q ∧ q ≤ 1 } × List Bool),
      loopListStepsAux (packSlotSubStep B_slot)
        (fun _ _ _ => 55 * B_slot + 140) cs st ≤
      cs.length * (55 * B_slot + 141) + 1
  | [], _ => by simp [loopListStepsAux]
  | c :: cs, st => by
    simp only [loopListStepsAux_cons, List.length_cons]
    have ih := loopListStepsAux_packSlotSubStep_le B_slot cs (packSlotSubStep B_slot c st)
    nlinarith

theorem length_encList_encodeSignedWord (w : ℕ) {α : Type} (val : α → ℤ) :
    ∀ (cs : List α),
      (encList (fun c => encodeSignedWord w (val c)) cs).length = cs.length * (2 * w + 4)
  | [] => by simp
  | c :: cs => by
    simp only [encList_cons, List.length_append, length_encodeDelimWord, length_encodeSignedWord,
      List.length_cons, length_encList_encodeSignedWord w val cs]
    ring

/-- **Stage 30 (`bmPackSignedSlotsBits`)**:
Consumes `encPair encUnary (encList (encodeSignedWord B_slot)) (B_slot - 1, cs)` on `kIO`
(`B_slot = d + 1 ≥ 1`) and produces `packSignedSlotsBits B_slot cs.length cs` on `kIO` in
**strictly linear** $O(|cs| \cdot B_{\text{slot}})$ `TM2.step` transitions
(`≤ cs.length * (65 * B_slot + 160) + 25 * B_slot + 90`). -/
def bmPackSignedSlotsBits : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork5).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kWork2).seq
            ((tmPushBitWord true kWork3).seq
              ((tmDupWord kWork5 kWork0 kWork1).seq
                ((tmConsBit false kWork1).seq
                  (((tmConsBit false kWork3).loopDelimWord kWork1).seq
                    ((tmPushEmpty kWork4).seq
                      ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                          ((tmRevMoveWord kWork0 kIO).seq
                            ((tmRevMoveWord kWork3 kWork0).seq
                              (tmPackPairFromRevSwapped.seq
                                (bmRippleAdd.seq
                                  ((tmDupWord kWork5 kWork0 kWork1).seq
                                    ((tmConsBit false kWork1).seq
                                      ((tmRevMoveWord kWork1 kWork0).seq
                                        (tmPackPairFromRev.seq
                                          (bmSliceDropBits.seq
                                            ((tmPopFirstSubwordRev kIO kWork0).seq
                                              ((tmRevMoveWord kWork0 kWork1).seq
                                                ((tmConcatRevWord kWork1 kWork4).seq
                                                  ((tmPopFirstSubwordRev kIO kWork0).seq
                                                    ((tmDropWord kIO).seq
                                                      ((tmRevMoveWord kWork0 kIO).seq
                                                        ((tmDupWord kWork5 kWork0 kWork3).seq
                                                          (tmSignExtendCarry1.seq
                                                            ((tmDropWord kWork3).seq
                                                              (tmMoveWord kIO kWork0 kWork3)))))))))))))))))))).loopNonEmptyWord kWork2).seq
                        ((tmDropWord kWork3).seq
                          ((tmDropWord kWork5).seq
                            (tmRevMoveWord kWork4 kIO)))))))))))))

set_option maxHeartbeats 800000 in
theorem bmPackSignedSlotsBits_computesInTime {d : ℕ}
    (cs : List { x : ℤ // FitsSignedWord (d + 1) x })
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    ∃ t ≤ cs.length * (65 * B_slot + 160) + 25 * B_slot + 90,
      bmPackSignedSlotsBits.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary
          (encList (fun c : { x : ℤ // FitsSignedWord B_slot x } => encodeSignedWord B_slot c.1))
          (d, cs)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (packSignedSlotsBits B_slot cs.length (cs.map Subtype.val)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot
  have hB1 : 1 ≤ B_slot := by omega
  let encC : { x : ℤ // FitsSignedWord B_slot x } → List Bool :=
    fun c => encodeSignedWord B_slot c.1
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary d) ++ encodeDelimWord (encList encC cs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork5 (by decide)
    (encUnary d).reverse [] tW5
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encC cs))) [] [] tW2 tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork5, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encC cs)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 (encodeDelimWord (encUnary d) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encC cs).reverse) []
      tW2 tW3 tW4 (encodeDelimWord (encUnary d) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encC cs).reverse [] tW2
    (mkTapes8 [] [] [] [] tW3 tW4 (encodeDelimWord (encUnary d) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushBitWord_computesInTime true kWork3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encC cs) ++ tW2)
      tW3 tW4 (encodeDelimWord (encUnary d) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s6
  have s7 := tmDupWord_computesInTime kWork5 kWork0 kWork1 (by decide) (by decide) (by decide)
    (encUnary d) tW5 [] []
    (mkTapes8 [] [] [] (encodeDelimWord (encList encC cs) ++ tW2)
      (encodeDelimWord [true] ++ tW3) tW4 [] tSch)
  simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
    List.append_nil, length_encUnary] at s7
  have s8 := tmConsBit_computesInTime false kWork1
    (mkTapes8 [] [] (encodeDelimWord (encUnary d))
      (encodeDelimWord (encList encC cs) ++ tW2)
      (encodeDelimWord [true] ++ tW3) tW4 (encodeDelimWord (encUnary d) ++ tW5) tSch)
    (encUnary d) [] (by simp)
  simp only [update_mkTapes8_kWork1, List.append_nil] at s8
  have h_encB : false :: encUnary d = encUnary B_slot := by
    change false :: List.replicate d false = List.replicate (d + 1) false
    exact List.replicate_succ.symm
  rw [h_encB] at s8
  have s9 := consBit_loopDelimWord_computesInTime false kWork1 kWork3 (by decide)
    (encUnary B_slot) [] [true] tW3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encC cs) ++ tW2)
      [] tW4 (encodeDelimWord (encUnary d) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork3, List.append_nil,
    length_encUnary] at s9
  have hzero_signed : List.replicate B_slot false ++ [true] = encodeSignedWord B_slot 0 := by
    rcases encodeSignedWord_succ_of_carry d 0 (by omega) (by omega) with ⟨hw1, hext⟩
    have hw1_eq : encodeSignedWord 1 0 = [false, true] := by decide
    simp only [hw1_eq, List.headD_cons, List.tail_cons, Bool.not_true] at hext
    rw [← hext, List.replicate_succ, List.cons_append]
  rw [hzero_signed] at s9
  have s10 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord (encList encC cs) ++ tW2)
      (encodeDelimWord (encodeSignedWord B_slot 0) ++ tW3)
      tW4 (encodeDelimWord (encUnary d) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s10
  let stepBound : { x : ℤ // FitsSignedWord B_slot x } →
      List { x : ℤ // FitsSignedWord B_slot x } →
      { q : ℤ // -1 ≤ q ∧ q ≤ 1 } × List Bool → ℕ :=
    fun _ _ _ => 55 * B_slot + 140
  let stkOf : { q : ℤ // -1 ≤ q ∧ q ≤ 1 } × List Bool →
      (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] []
      (encodeDelimWord (encodeSignedWord B_slot st.1.1) ++ tW3)
      (encodeDelimWord st.2 ++ tW4)
      (encodeDelimWord (encUnary d) ++ tW5) tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encC
    (packSlotSubStep B_slot) stepBound stkOf
    (fun c rem st restW2 => by
      rcases st with ⟨carry, accRev⟩
      dsimp only [stkOf, packSlotSubStep, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encC c) ++ encodeWordStack (rem.map encC)) restW2 []
        (mkTapes8 [] [] [] []
          (encodeDelimWord (encodeSignedWord B_slot carry.1) ++ tW3)
          (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
        (encC c).reverse [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          (encodeDelimWord (encodeSignedWord B_slot carry.1) ++ tW3)
          (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2
      have b3 := tmRevMoveWord_computesInTime kWork3 kWork0 (by decide)
        (encodeSignedWord B_slot carry.1) tW3 []
        (mkTapes8 (encodeDelimWord (encC c)) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          [] (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0,
        List.append_nil, length_encodeSignedWord] at b3
      have b4 := tmPackPairFromRevSwapped_computesInTime
        (encC c) (encodeSignedWord B_slot carry.1)
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord accRev ++ tW4)
        (encodeDelimWord (encUnary d) ++ tW5) tSch
      have hcarry_fits : FitsSignedWord B_slot carry.1 :=
        fitsSignedWord_of_carry hB1 carry.2.1 carry.2.2
      rcases bmRippleAdd_signed_computesInTime B_slot c.1 carry.1 c.2 hcarry_fits
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord accRev ++ tW4)
        (encodeDelimWord (encUnary d) ++ tW5) tSch with ⟨tAdd, htAdd, b5⟩
      have b6 := tmDupWord_computesInTime kWork5 kWork0 kWork1 (by decide) (by decide) (by decide)
        (encUnary d) tW5 [] []
        (mkTapes8 (encodeDelimWord (encodeSignedWord (B_slot + 1) (c.1 + carry.1))) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4) [] tSch)
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kWork1,
        List.append_nil, length_encUnary] at b6
      have b7 := tmConsBit_computesInTime false kWork1
        (mkTapes8 (encodeDelimWord (encodeSignedWord (B_slot + 1) (c.1 + carry.1))) []
          (encodeDelimWord (encUnary d))
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
        (encUnary d) [] (by simp)
      simp only [update_mkTapes8_kWork1, List.append_nil, h_encB] at b7
      have b8 := tmRevMoveWord_computesInTime kWork1 kWork0 (by decide)
        (encUnary B_slot) [] []
        (mkTapes8 (encodeDelimWord (encodeSignedWord (B_slot + 1) (c.1 + carry.1))) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, List.append_nil,
        length_encUnary] at b8
      have b9 := tmPackPairFromRev_computesInTime
        (encUnary B_slot) (encodeSignedWord (B_slot + 1) (c.1 + carry.1))
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord accRev ++ tW4)
        (encodeDelimWord (encUnary d) ++ tW5) tSch
      rcases bmSliceDropBits_computesStageLe
        (B_slot, encodeSignedWord (B_slot + 1) (c.1 + carry.1))
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord accRev ++ tW4)
        (encodeDelimWord (encUnary d) ++ tW5) tSch with ⟨tSlice, htSlice, b10⟩
      dsimp only [encBits, id] at htSlice b10
      rcases encodeSignedWord_succ_split hB1 c.2 carry.2.1 carry.2.2 with ⟨hcarry'_bds, hsplit⟩
      set total := c.1 + carry.1
      set rem_val := (total % ((2 : ℤ) ^ B_slot)).toNat
      set carry' := total / ((2 : ℤ) ^ B_slot)
      have htake : takePadBits B_slot (encodeSignedWord (B_slot + 1) total) =
          encodeNatBits B_slot rem_val := by
        rw [hsplit, takePadBits_eq_take_of_le B_slot _ (by simp),
          List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
      have hdrop : (encodeSignedWord (B_slot + 1) total).drop B_slot =
          encodeSignedWord 1 carry' := by
        rw [hsplit, List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append,
          encodeNatBits_length, Nat.sub_self, List.drop]
      rw [htake, hdrop] at b10
      have b11 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
        (encodeDelimWord (encodeNatBits B_slot rem_val) ++
          encodeDelimWord (encodeSignedWord 1 carry')) [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b11
      have b11b := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
        (encodeNatBits B_slot rem_val).reverse [] []
        (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeSignedWord 1 carry'))) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord accRev ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.length_reverse,
        List.reverse_reverse, encodeNatBits_length, List.append_nil] at b11b
      have b12 := tmConcatRevWord_computesInTime kWork1 kWork4 (by decide)
        (encodeNatBits B_slot rem_val) accRev [] tW4
        (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeSignedWord 1 carry'))) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 [] (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork4,
        encodeNatBits_length, List.append_nil] at b12
      have b13 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
        (encodeDelimWord (encodeSignedWord 1 carry')) [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord ((encodeNatBits B_slot rem_val).reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord] at b13
      have b14 := tmDropWord_computesInTime kIO [] []
        (mkTapes8 [] (encodeDelimWord (encodeSignedWord 1 carry').reverse) []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord ((encodeNatBits B_slot rem_val).reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at b14
      have b15 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
        (encodeSignedWord 1 carry').reverse [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          tW3 (encodeDelimWord ((encodeNatBits B_slot rem_val).reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
        List.reverse_reverse, length_encodeSignedWord, List.append_nil] at b15
      have b16 := tmDupWord_computesInTime kWork5 kWork0 kWork3 (by decide) (by decide) (by decide)
        (encUnary d) tW5 [] tW3
        (mkTapes8 (encodeDelimWord (encodeSignedWord 1 carry')) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          [] (encodeDelimWord ((encodeNatBits B_slot rem_val).reverse ++ accRev) ++ tW4) [] tSch)
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
        length_encUnary] at b16
      rcases tmSignExtendCarry1_computesInTime d carry' hcarry'_bds.1 hcarry'_bds.2
        (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
        tW3 (encodeDelimWord ((encodeNatBits B_slot rem_val).reverse ++ accRev) ++ tW4)
        (encodeDelimWord (encUnary d) ++ tW5) tSch with ⟨tExt, htExt, b17⟩
      have b18 := tmDropWord_computesInTime kWork3 (encUnary d) tW3
        (mkTapes8 (encodeDelimWord (encodeSignedWord B_slot carry')) [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          [] (encodeDelimWord ((encodeNatBits B_slot rem_val).reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork3, length_encUnary] at b18
      have b19 := tmMoveWord_computesInTime kIO kWork0 kWork3 (by decide) (by decide) (by decide)
        (encodeSignedWord B_slot carry') [] [] tW3
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encC)) ++ restW2)
          [] (encodeDelimWord ((encodeNatBits B_slot rem_val).reverse ++ accRev) ++ tW4)
          (encodeDelimWord (encUnary d) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
        List.append_nil, length_encodeSignedWord] at b19
      have hseq := b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (b6.seq (b7.seq (b8.seq (b9.seq
        (b10.seq (b11.seq (b11b.seq (b12.seq (b13.seq (b14.seq (b15.seq (b16.seq (b17.seq
          (b18.seq b19))))))))))))))))))
      have hB_def : B_slot = d + 1 := rfl
      simp only [encC, length_encUnary, length_encodeSignedWord,
        encodeNatBits_length] at hseq htSlice
      refine ⟨_, ?_, hseq⟩
      linarith only [hB_def, htAdd, htSlice, htExt, hB1])
    cs tW2 (⟨0, by omega⟩, []) with ⟨tL, htL, s11⟩
  dsimp only [stkOf, stepBound] at htL s11
  simp only [update_mkTapes8_kWork2] at s11
  set stF := loopListFinalState (packSlotSubStep B_slot) cs (⟨0, by omega⟩, [])
  have hbitsF := loopListFinalState_packSlotSubStep_spec B_slot cs ⟨0, by omega⟩ []
  simp only [List.reverse_nil, List.nil_append] at hbitsF
  have hbitsF' : stF.2.reverse = packSignedSlotsBits B_slot cs.length (cs.map Subtype.val) :=
    hbitsF
  have s12 := tmDropWord_computesInTime kWork3 (encodeSignedWord B_slot stF.1.1) tW3
    (mkTapes8 [] [] [] tW2 [] (encodeDelimWord stF.2 ++ tW4)
      (encodeDelimWord (encUnary d) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork3, length_encodeSignedWord] at s12
  have s13 := tmDropWord_computesInTime kWork5 (encUnary d) tW5
    (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord stF.2 ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5, length_encUnary] at s13
  have s14 := tmRevMoveWord_computesInTime kWork4 kIO (by decide)
    stF.2 tW4 []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kIO, List.append_nil] at s14
  have hlen_stF : stF.2.length = cs.length * B_slot := by
    rw [← List.length_reverse, hbitsF', length_packSignedSlotsBits]
  rw [hbitsF', hlen_stF] at s14
  have hlen_cs : (encList encC cs).length = cs.length * (2 * B_slot + 4) :=
    length_encList_encodeSignedWord B_slot Subtype.val cs
  have hbL := loopListStepsAux_packSlotSubStep_le B_slot cs (⟨0, by omega⟩, [])
  simp only [encPair, length_encUnary, hlen_cs] at s1 s2 s3 s5 ⊢
  have hB_def : B_slot = d + 1 := rfl
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
      (s11.seq (s12.seq (s13.seq s14))))))))))))⟩
  nlinarith

/-! ## 2. Signed Kronecker Slot Bit-List Unpacker (`bmUnpackSignedSlotsBits`, Stage 31) -/

/-- Exact bit-level characterization of `extractSignedSlot` and `stepSignedSlot` on
`total = u + carryBit.toNat` (`u < 2 ^ (d + 1)`):
1. `(encodeNatBits (d + 2) total).reverse = b_d1 :: b_d :: low_d.reverse`,
2. `(encodeSignedWord (d + 1) (extractSignedSlot (d + 1) total)).reverse = (!b_d) :: b_d :: low_d.reverse`,
3. `stepSignedSlot (d + 1) total = ((b_d || b_d1).toNat : ℤ)`. -/
theorem extractSignedSlot_bits_spec (d u : ℕ) (hu : u < 2 ^ (d + 1)) (carryBit : Bool) :
    let total : ℕ := u + carryBit.toNat
    let low_d := encodeNatBits d (total % 2 ^ d)
    let b_d := decide ((total / 2 ^ d) % 2 = 1)
    let b_d1 := decide ((total / 2 ^ (d + 1)) % 2 = 1)
    (encodeNatBits (d + 2) total).reverse = b_d1 :: b_d :: low_d.reverse ∧
      (encodeSignedWord (d + 1) (extractSignedSlot (d + 1) (total : ℤ))).reverse =
        (!b_d) :: b_d :: low_d.reverse ∧
      stepSignedSlot (d + 1) (total : ℤ) = ((b_d || b_d1).toNat : ℤ) := by
  intro total low_d b_d b_d1
  set r0 := total % 2 ^ d
  set q0 := total / 2 ^ d
  have hcarry_le : carryBit.toNat ≤ 1 := Bool.toNat_le carryBit
  have hpow_succ : 2 ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
  have htotal_le : total ≤ 2 ^ d * 2 := by omega
  have hdiv_d1 : q0 / 2 = total / 2 ^ (d + 1) := by
    dsimp [q0]
    rw [Nat.div_div_eq_div_mul, ← hpow_succ]
  have h2bits : encodeNatBits 2 q0 = [b_d, b_d1] := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, encodeNatBits_succ_mod_div 1 q0,
      encodeNatBits_succ_mod_div 0 (q0 / 2), hdiv_d1]
    rfl
  have hbits_total : encodeNatBits (d + 2) total = low_d ++ [b_d, b_d1] := by
    rw [encodeNatBits_add_mod_div d 2 total]
    change low_d ++ encodeNatBits 2 q0 = low_d ++ [b_d, b_d1]
    rw [h2bits]
  have hrev_total : (encodeNatBits (d + 2) total).reverse = b_d1 :: b_d :: low_d.reverse := by
    rw [hbits_total, List.reverse_append]
    rfl
  refine ⟨hrev_total, ?_⟩
  have hr0_lt : r0 < 2 ^ d := Nat.mod_lt total (Nat.two_pow_pos d)
  have hdiv_mod : r0 + 2 ^ d * q0 = total := Nat.mod_add_div total (2 ^ d)
  have hq0_le : q0 ≤ 2 := by
    calc q0 = total / 2 ^ d := rfl
      _ ≤ (2 ^ d * 2) / 2 ^ d := Nat.div_le_div_right htotal_le
      _ = 2 := Nat.mul_div_cancel_left 2 (Nat.two_pow_pos d)
  have hq0_cases : q0 = 0 ∨ q0 = 1 ∨ q0 = 2 := by
    revert hq0_le
    generalize q0 = q
    omega
  rcases hq0_cases with hq0 | hq0 | hq0
  · have hb_d : b_d = false := by
      change decide (q0 % 2 = 1) = false
      rw [hq0]; decide
    have hb_d1 : b_d1 = false := by
      change decide ((total / 2 ^ (d + 1)) % 2 = 1) = false
      rw [← hdiv_d1, hq0]; decide
    have htot_eq : total = r0 := by
      rw [hq0, Nat.mul_zero, Nat.add_zero] at hdiv_mod
      exact hdiv_mod.symm
    have htot_lt_d1 : (total : ℤ) < (2 : ℤ) ^ (d + 1) := by
      have : total < 2 ^ (d + 1) := by omega
      exact_mod_cast this
    have htot_lt_d : (total : ℤ) < (2 : ℤ) ^ d := by
      rw [htot_eq]
      exact_mod_cast hr0_lt
    have hextr : extractSignedSlot (d + 1) (total : ℤ) = (r0 : ℤ) := by
      unfold extractSignedSlot
      simp only [Nat.add_sub_cancel]
      rw [Int.emod_eq_of_lt (by positivity) htot_lt_d1,
        if_neg (not_le.mpr htot_lt_d), htot_eq]
    have hstep : stepSignedSlot (d + 1) (total : ℤ) = 0 := by
      unfold stepSignedSlot
      rw [hextr, htot_eq, sub_self, Int.zero_ediv]
    have hsw : encodeSignedWord (d + 1) (r0 : ℤ) = low_d ++ [false, true] := by
      unfold encodeSignedWord
      have htoNat : ((r0 : ℤ) + (2 : ℤ) ^ (d + 1)).toNat = r0 + 2 ^ d * 2 := by
        have hp : (0 : ℤ) ≤ (r0 : ℤ) + (2 : ℤ) ^ (d + 1) := by positivity
        zify
        rw [Int.toNat_of_nonneg hp, pow_succ]
      have hmod : (r0 + 2 ^ d * 2) % 2 ^ d = r0 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr0_lt]
      have hdiv : (r0 + 2 ^ d * 2) / 2 ^ d = 2 := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos d),
          Nat.div_eq_of_lt hr0_lt, Nat.zero_add]
      rw [htoNat, show d + 1 + 1 = d + 2 from rfl, encodeNatBits_add_mod_div d 2, hmod, hdiv]
      rfl
    rw [hextr, hsw, hb_d, hb_d1, List.reverse_append]
    exact ⟨rfl, hstep⟩
  · have hb_d : b_d = true := by
      change decide (q0 % 2 = 1) = true
      rw [hq0]; decide
    have hb_d1 : b_d1 = false := by
      change decide ((total / 2 ^ (d + 1)) % 2 = 1) = false
      rw [← hdiv_d1, hq0]; decide
    have htot_eq : total = r0 + 2 ^ d := by
      rw [hq0, Nat.mul_one] at hdiv_mod
      exact hdiv_mod.symm
    have htot_lt_d1 : (total : ℤ) < (2 : ℤ) ^ (d + 1) := by
      have : total < 2 ^ (d + 1) := by omega
      exact_mod_cast this
    have htot_ge_d : (total : ℤ) ≥ (2 : ℤ) ^ d := by
      have : 2 ^ d ≤ total := by omega
      exact_mod_cast this
    have hextr : extractSignedSlot (d + 1) (total : ℤ) = (total : ℤ) - (2 : ℤ) ^ (d + 1) := by
      unfold extractSignedSlot
      simp only [Nat.add_sub_cancel]
      rw [Int.emod_eq_of_lt (by positivity) htot_lt_d1, if_pos htot_ge_d]
    have hstep : stepSignedSlot (d + 1) (total : ℤ) = 1 := by
      unfold stepSignedSlot
      rw [hextr, sub_sub_cancel, Int.ediv_self (by positivity)]
    have hsw : encodeSignedWord (d + 1) ((total : ℤ) - (2 : ℤ) ^ (d + 1)) =
        low_d ++ [true, false] := by
      unfold encodeSignedWord
      have htoNat : ((total : ℤ) - (2 : ℤ) ^ (d + 1) + (2 : ℤ) ^ (d + 1)).toNat =
          r0 + 2 ^ d * 1 := by
        rw [sub_add_cancel, Int.toNat_natCast, htot_eq, Nat.mul_one]
      have hmod : (r0 + 2 ^ d * 1) % 2 ^ d = r0 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr0_lt]
      have hdiv : (r0 + 2 ^ d * 1) / 2 ^ d = 1 := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos d),
          Nat.div_eq_of_lt hr0_lt, Nat.zero_add]
      rw [htoNat, show d + 1 + 1 = d + 2 from rfl, encodeNatBits_add_mod_div d 2, hmod, hdiv]
      rfl
    rw [hextr, hsw, hb_d, hb_d1, List.reverse_append]
    exact ⟨rfl, hstep⟩
  · have hr0 : r0 = 0 := by
      rw [hq0] at hdiv_mod
      omega
    have hb_d : b_d = false := by
      change decide (q0 % 2 = 1) = false
      rw [hq0]; decide
    have hb_d1 : b_d1 = true := by
      change decide ((total / 2 ^ (d + 1)) % 2 = 1) = true
      rw [← hdiv_d1, hq0]; decide
    have htot_eq : total = 2 ^ (d + 1) := by
      rw [hq0, hr0, Nat.zero_add] at hdiv_mod
      rw [← hdiv_mod, ← hpow_succ]
    have hextr : extractSignedSlot (d + 1) (total : ℤ) = 0 := by
      unfold extractSignedSlot
      simp only [Nat.add_sub_cancel, htot_eq, Nat.cast_pow, Nat.cast_ofNat, Int.emod_self]
      have hp : ¬ ((0 : ℤ) ≥ (2 : ℤ) ^ d) := not_le.mpr (by positivity)
      rw [if_neg hp]
    have hstep : stepSignedSlot (d + 1) (total : ℤ) = 1 := by
      unfold stepSignedSlot
      rw [hextr, sub_zero, htot_eq, Nat.cast_pow, Nat.cast_ofNat,
        Int.ediv_self (by positivity)]
    have hsw : encodeSignedWord (d + 1) 0 = low_d ++ [false, true] := by
      unfold encodeSignedWord
      have htoNat : ((0 : ℤ) + (2 : ℤ) ^ (d + 1)).toNat = 0 + 2 ^ d * 2 := by
        have hp : (0 : ℤ) ≤ (0 : ℤ) + (2 : ℤ) ^ (d + 1) := by positivity
        zify
        rw [Int.toNat_of_nonneg hp, pow_succ]
      have hmod : (0 + 2 ^ d * 2) % 2 ^ d = 0 := by
        rw [Nat.add_mul_mod_self_left, Nat.zero_mod]
      have hdiv : (0 + 2 ^ d * 2) / 2 ^ d = 2 := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos d), Nat.zero_div, Nat.zero_add]
      have hlow : low_d = encodeNatBits d 0 := by
        change encodeNatBits d r0 = encodeNatBits d 0
        rw [hr0]
      rw [htoNat, show d + 1 + 1 = d + 2 from rfl, encodeNatBits_add_mod_div d 2,
        hmod, hdiv, ← hlow]
      rfl
    rw [hextr, hsw, hb_d, hb_d1, List.reverse_append]
    exact ⟨rfl, hstep⟩

/-- Extracts `(encodeSignedWord (d + 1) (extractSignedSlot (d + 1) total)).reverse` onto `kIO`
and `[b_d || b_d1]` onto `kWork1` from `(encodeNatBits (d + 2) total).reverse` on `kIO` in
`≤ 10` `TM2.step` transitions. -/
def tmExtractSignedSlotFromRev : BitMachine :=
  (tmPushEmpty kWork1).seq
    ((tmPopBitOrZero kIO kWork1).seq
      ((tmPushEmpty kWork0).seq
        ((tmPopBitOrZero kIO kWork0).seq
          (BitMachine.branchDelimBit kWork0
            ((tmConsBit false kIO).seq (tmConsBit true kIO))
            ((tmConsBit true kIO).seq
              ((tmConsBit false kIO).seq
                ((tmDropWord kWork1).seq (tmPushBitWord true kWork1))))))))

theorem tmExtractSignedSlotFromRev_computesInTime (d u : ℕ) (hu : u < 2 ^ (d + 1))
    (carryBit : Bool) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let total : ℕ := u + carryBit.toNat
    let slot : ℤ := extractSignedSlot (d + 1) (total : ℤ)
    let nextBit : Bool :=
      decide ((total / 2 ^ d) % 2 = 1) || decide ((total / 2 ^ (d + 1)) % 2 = 1)
    ∃ t ≤ 10,
      tmExtractSignedSlotFromRev.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeNatBits (d + 2) total).reverse)
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord (d + 1) slot).reverse)
          [] (encodeDelimWord [nextBit]) tW2 tW3 tW4 tW5 tSch) t := by
  intro total slot nextBit
  rcases extractSignedSlot_bits_spec d u hu carryBit with ⟨hrev_tot, hrev_slot, _⟩
  set low_d := encodeNatBits d (total % 2 ^ d)
  set b_d := decide ((total / 2 ^ d) % 2 = 1)
  set b_d1 := decide ((total / 2 ^ (d + 1)) % 2 = 1)
  rw [hrev_tot, hrev_slot]
  cases hb : b_d with
  | false =>
    have s1 := tmPushEmpty_computesInTime kWork1
      (mkTapes8 (encodeDelimWord (b_d1 :: false :: low_d.reverse))
        [] [] tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, mkTapes8_kWork1, List.append_nil] at s1
    have s2 := tmPopBitOrZero_computesInTime kIO kWork1 (by decide)
      (b_d1 :: false :: low_d.reverse) [] [] []
      (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
      List.headD_cons, List.tail_cons] at s2
    have s3 := tmPushEmpty_computesInTime kWork0
      (mkTapes8 (encodeDelimWord (false :: low_d.reverse))
        [] (encodeDelimWord [b_d1]) tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, mkTapes8_kWork0, List.append_nil] at s3
    have s4 := tmPopBitOrZero_computesInTime kIO kWork0 (by decide)
      (false :: low_d.reverse) [] [] []
      (mkTapes8 [] [] (encodeDelimWord [b_d1]) tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
      List.headD_cons, List.tail_cons] at s4
    have c1 := tmConsBit_computesInTime false kIO
      (mkTapes8 (encodeDelimWord low_d.reverse) [] (encodeDelimWord [b_d1])
        tW2 tW3 tW4 tW5 tSch)
      low_d.reverse [] (by simp)
    simp only [update_mkTapes8_kIO, List.append_nil] at c1
    have c2 := tmConsBit_computesInTime true kIO
      (mkTapes8 (encodeDelimWord (false :: low_d.reverse)) [] (encodeDelimWord [b_d1])
        tW2 tW3 tW4 tW5 tSch)
      (false :: low_d.reverse) [] (by simp)
    simp only [update_mkTapes8_kIO, List.append_nil] at c2
    have br := BitMachine.ComputesInTime.branchDelimBit kWork0
      (M_false := (tmConsBit false kIO).seq (tmConsBit true kIO))
      (M_true := (tmConsBit true kIO).seq
        ((tmConsBit false kIO).seq ((tmDropWord kWork1).seq (tmPushBitWord true kWork1))))
      false []
      (T₁ := mkTapes8 (encodeDelimWord low_d.reverse) [] (encodeDelimWord [b_d1])
        tW2 tW3 tW4 tW5 tSch)
      (by simpa only [update_mkTapes8_kWork0, Bool.false_eq_true, ↓reduceIte] using c1.seq c2)
    simp only [update_mkTapes8_kWork0, List.append_nil] at br
    have hnext : nextBit = b_d1 := by
      change (b_d || b_d1) = b_d1
      rw [hb, Bool.false_or]
    rw [hnext]
    exact ⟨_, by omega, s1.seq (s2.seq (s3.seq (s4.seq br)))⟩
  | true =>
    have s1 := tmPushEmpty_computesInTime kWork1
      (mkTapes8 (encodeDelimWord (b_d1 :: true :: low_d.reverse))
        [] [] tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, mkTapes8_kWork1, List.append_nil] at s1
    have s2 := tmPopBitOrZero_computesInTime kIO kWork1 (by decide)
      (b_d1 :: true :: low_d.reverse) [] [] []
      (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
      List.headD_cons, List.tail_cons] at s2
    have s3 := tmPushEmpty_computesInTime kWork0
      (mkTapes8 (encodeDelimWord (true :: low_d.reverse))
        [] (encodeDelimWord [b_d1]) tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork0, mkTapes8_kWork0, List.append_nil] at s3
    have s4 := tmPopBitOrZero_computesInTime kIO kWork0 (by decide)
      (true :: low_d.reverse) [] [] []
      (mkTapes8 [] [] (encodeDelimWord [b_d1]) tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
      List.headD_cons, List.tail_cons] at s4
    have c1 := tmConsBit_computesInTime true kIO
      (mkTapes8 (encodeDelimWord low_d.reverse) [] (encodeDelimWord [b_d1])
        tW2 tW3 tW4 tW5 tSch)
      low_d.reverse [] (by simp)
    simp only [update_mkTapes8_kIO, List.append_nil] at c1
    have c2 := tmConsBit_computesInTime false kIO
      (mkTapes8 (encodeDelimWord (true :: low_d.reverse)) [] (encodeDelimWord [b_d1])
        tW2 tW3 tW4 tW5 tSch)
      (true :: low_d.reverse) [] (by simp)
    simp only [update_mkTapes8_kIO, List.append_nil] at c2
    have c3 := tmDropWord_computesInTime kWork1 [b_d1] []
      (mkTapes8 (encodeDelimWord (false :: true :: low_d.reverse)) [] []
        tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, List.append_nil, List.length_singleton] at c3
    have c4 := tmPushBitWord_computesInTime true kWork1
      (mkTapes8 (encodeDelimWord (false :: true :: low_d.reverse)) [] []
        tW2 tW3 tW4 tW5 tSch)
    simp only [update_mkTapes8_kWork1, mkTapes8_kWork1, List.append_nil] at c4
    have br := BitMachine.ComputesInTime.branchDelimBit kWork0
      (M_false := (tmConsBit false kIO).seq (tmConsBit true kIO))
      (M_true := (tmConsBit true kIO).seq
        ((tmConsBit false kIO).seq ((tmDropWord kWork1).seq (tmPushBitWord true kWork1))))
      true []
      (T₁ := mkTapes8 (encodeDelimWord low_d.reverse) [] (encodeDelimWord [b_d1])
        tW2 tW3 tW4 tW5 tSch)
      (by simpa only [update_mkTapes8_kWork0, ↓reduceIte] using c1.seq (c2.seq (c3.seq c4)))
    simp only [update_mkTapes8_kWork0, List.append_nil] at br
    have hnext : nextBit = true := by
      change (b_d || b_d1) = true
      rw [hb, Bool.true_or]
    rw [hnext]
    exact ⟨_, by omega, s1.seq (s2.seq (s3.seq (s4.seq br)))⟩

/-- Bounded chunk slicer refining `sliceBitChunks b R bs` with the proof `< 2 ^ b` for each chunk. -/
def sliceBitChunksBounded (b : ℕ) : ℕ → List Bool → List { x : ℕ // x < 2 ^ b }
  | 0, _ => []
  | R + 1, bs =>
    ⟨decodeNatBits (bs.take b), by
      have h := decodeNatBits_lt (bs.take b)
      exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (List.length_take_le b bs))⟩ ::
      sliceBitChunksBounded b R (bs.drop b)

@[simp]
theorem map_val_sliceBitChunksBounded (b : ℕ) :
    ∀ (R : ℕ) (bs : List Bool),
      (sliceBitChunksBounded b R bs).map Subtype.val = sliceBitChunks b R bs
  | 0, bs => by rw [sliceBitChunksBounded, sliceBitChunks_zero, List.map_nil]
  | R + 1, bs => by
    rw [sliceBitChunksBounded, sliceBitChunks_succ, List.map_cons,
      map_val_sliceBitChunksBounded b R (bs.drop b)]

@[simp]
theorem length_sliceBitChunksBounded (b R : ℕ) (bs : List Bool) :
    (sliceBitChunksBounded b R bs).length = R := by
  induction R generalizing bs with
  | zero => rfl
  | succ R ih => simp [sliceBitChunksBounded, ih]

theorem encList_sliceBitChunksBounded (b R : ℕ) (bs : List Bool) :
    encList (fun u : { x : ℕ // x < 2 ^ b } => encNatWord b u.1)
      (sliceBitChunksBounded b R bs) =
    encList (encNatWord b) (sliceBitChunks b R bs) := by
  unfold encList
  congr 1
  rw [← map_val_sliceBitChunksBounded b R bs, List.map_map]
  rfl

/-- Pure step function for `bmUnpackSignedSlotsLoop` over bounded unsigned chunk words. -/
def unpackSlotRevStep (d : ℕ) (u : { x : ℕ // x < 2 ^ (d + 1) })
    (st : Bool × List ℤ) : Bool × List ℤ :=
  let total : ℕ := u.1 + st.1.toNat
  let slot : ℤ := extractSignedSlot (d + 1) (total : ℤ)
  let nextBit : Bool :=
    decide ((total / 2 ^ d) % 2 = 1) || decide ((total / 2 ^ (d + 1)) % 2 = 1)
  (nextBit, slot :: st.2)

theorem loopListFinalState_unpackSlotRevStep_spec (d : ℕ) :
    ∀ (m : ℕ) (bs : List Bool) (carryBit : Bool) (accRev : List ℤ),
      (loopListFinalState (unpackSlotRevStep d)
        (sliceBitChunksBounded (d + 1) m bs) (carryBit, accRev)).2.reverse =
      accRev.reverse ++ unpackSignedSlotsBitsAux (d + 1) m bs (carryBit.toNat : ℤ)
  | 0, bs, carryBit, accRev => by
    simp [sliceBitChunksBounded, unpackSignedSlotsBitsAux]
  | m + 1, bs, carryBit, accRev => by
    rw [sliceBitChunksBounded, loopListFinalState_cons]
    set u := decodeNatBits (bs.take (d + 1))
    have hu : u < 2 ^ (d + 1) := by
      have h := decodeNatBits_lt (bs.take (d + 1))
      exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (List.length_take_le (d + 1) bs))
    rcases extractSignedSlot_bits_spec d u hu carryBit with ⟨_, _, hstep⟩
    set total : ℕ := u + carryBit.toNat
    set slot : ℤ := extractSignedSlot (d + 1) (total : ℤ)
    set nextBit : Bool :=
      decide ((total / 2 ^ d) % 2 = 1) || decide ((total / 2 ^ (d + 1)) % 2 = 1)
    have ih := loopListFinalState_unpackSlotRevStep_spec d m (bs.drop (d + 1))
      nextBit (slot :: accRev)
    dsimp only [unpackSlotRevStep]
    rw [ih]
    have htot_z : ((decodeNatBits (bs.take (d + 1)) : ℤ) + (carryBit.toNat : ℤ)) = (total : ℤ) := by
      dsimp [total, u]
    dsimp only [unpackSignedSlotsBitsAux]
    rw [htot_z, hstep]
    dsimp only [slot]
    simp [List.reverse_cons, List.append_assoc]

theorem length_loopListFinalState_unpackSlotRevStep (d : ℕ) :
    ∀ (us : List { x : ℕ // x < 2 ^ (d + 1) }) (carryBit : Bool) (accRev : List ℤ),
      (loopListFinalState (unpackSlotRevStep d) us (carryBit, accRev)).2.length =
        us.length + accRev.length
  | [], carryBit, accRev => by simp [loopListFinalState]
  | u :: us, carryBit, accRev => by
    simp only [loopListFinalState_cons, unpackSlotRevStep,
      length_loopListFinalState_unpackSlotRevStep d us, List.length_cons]
    omega

theorem loopListStepsAux_unpackSlotRevStep_le (d : ℕ) :
    ∀ (us : List { x : ℕ // x < 2 ^ (d + 1) }) (st : Bool × List ℤ),
      loopListStepsAux (unpackSlotRevStep d)
        (fun _ _ _ => 24 * (d + 1) + 55) us st ≤
      us.length * (24 * (d + 1) + 56) + 1
  | [], _ => by simp [loopListStepsAux]
  | u :: us, st => by
    simp only [loopListStepsAux_cons, List.length_cons]
    have ih := loopListStepsAux_unpackSlotRevStep_le d us (unpackSlotRevStep d u st)
    nlinarith

theorem encodeNatBits_bool_toNat (d : ℕ) (b : Bool) :
    b :: List.replicate d false = encodeNatBits (d + 1) b.toNat := by
  cases b <;> simp [encodeNatBits_succ_mod_div, encodeNatBits_zero]

/-- Loop kernel of `bmUnpackSignedSlotsBits`: consumes `(d, us)` on `kIO`
(`us : List { x : ℕ // x < 2 ^ (d + 1) }`) and produces the list of unpacked signed slot words on
`kIO` in $O(|us| \cdot (d + 1))$ `TM2.step` transitions. -/
def bmUnpackSignedSlotsLoop : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork1).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmDropWord kIO).seq
          ((tmRevMoveWord kWork0 kWork2).seq
            ((tmPushEmpty kWork5).seq
              (((tmConsBit false kWork5).loopDelimWord kWork1).seq
                ((tmDupWord kWork5 kWork0 kWork3).seq
                  ((tmConsBit false kWork3).seq
                    ((tmPushEmpty kWork4).seq
                      ((((tmPopFirstSubwordRev kWork2 kWork0).seq
                          ((tmRevMoveWord kWork0 kIO).seq
                            ((tmRevMoveWord kWork3 kWork0).seq
                              (tmPackPairFromRevSwapped.seq
                                (bmRippleAdd.seq
                                  ((tmRevMoveWord kIO kWork0).seq
                                    ((tmMoveWord kWork0 kWork1 kIO).seq
                                      (tmExtractSignedSlotFromRev.seq
                                        ((tmPrependRevWord kIO kWork4).seq
                                          ((tmDupWord kWork5 kWork0 kWork3).seq
                                            (tmConcatRevWord kWork1 kWork3))))))))))).loopNonEmptyWord kWork2).seq
                        ((tmDropWord kWork3).seq
                          ((tmDropWord kWork5).seq
                            ((tmMoveWord kWork4 kWork0 kIO).seq bmRevList)))))))))))))

theorem bmUnpackSignedSlotsLoop_computesInTime {d : ℕ}
    (us : List { x : ℕ // x < 2 ^ (d + 1) })
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    let stF := loopListFinalState (unpackSlotRevStep d) us (false, [])
    ∃ t ≤ us.length * (65 * B_slot + 115) + 25 * B_slot + 90,
      bmUnpackSignedSlotsLoop.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary
          (encList (fun u : { x : ℕ // x < 2 ^ B_slot } => encNatWord B_slot u.1))
          (d, us)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encodeSignedWord B_slot) stF.2.reverse))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot stF
  let encU : { x : ℕ // x < 2 ^ B_slot } → List Bool := fun u => encNatWord B_slot u.1
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary d) ++ encodeDelimWord (encList encU us)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
    (encUnary d).reverse [] []
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encList encU us))) [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s2
  have s3 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encList encU us)) [] []
    (mkTapes8 [] [] (encodeDelimWord (encUnary d)) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s3
  have s4 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encList encU us).reverse)
      (encodeDelimWord (encUnary d)) tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s4
  have s5 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    (encList encU us).reverse [] tW2
    (mkTapes8 [] [] (encodeDelimWord (encUnary d)) [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s5
  have s6 := tmPushEmpty_computesInTime kWork5
    (mkTapes8 [] [] (encodeDelimWord (encUnary d))
      (encodeDelimWord (encList encU us) ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork5, mkTapes8_kWork5] at s6
  have s7 := consBit_loopDelimWord_computesInTime false kWork1 kWork5 (by decide)
    (encUnary d) [] [] tW5
    (mkTapes8 [] [] [] (encodeDelimWord (encList encU us) ++ tW2) tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork5, List.append_nil,
    length_encUnary] at s7
  have s8 := tmDupWord_computesInTime kWork5 kWork0 kWork3 (by decide) (by decide) (by decide)
    (List.replicate d false) tW5 [] tW3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encU us) ++ tW2) [] tW4 [] tSch)
  simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
    List.length_replicate] at s8
  have s9 := tmConsBit_computesInTime false kWork3
    (mkTapes8 [] [] [] (encodeDelimWord (encList encU us) ++ tW2)
      (encodeDelimWord (List.replicate d false) ++ tW3)
      tW4 (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
    (List.replicate d false) tW3 (by simp)
  simp only [update_mkTapes8_kWork3, encodeNatBits_bool_toNat d false] at s9
  have s10 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord (encList encU us) ++ tW2)
      (encodeDelimWord (encodeNatBits B_slot (false.toNat)) ++ tW3)
      tW4 (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s10
  let stepBound : { x : ℕ // x < 2 ^ B_slot } →
      List { x : ℕ // x < 2 ^ B_slot } → Bool × List ℤ → ℕ :=
    fun _ _ _ => 24 * B_slot + 55
  let stkOf : Bool × List ℤ → (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] []
      (encodeDelimWord (encodeNatBits B_slot st.1.toNat) ++ tW3)
      (encodeDelimWord (encList (encodeSignedWord B_slot) st.2) ++ tW4)
      (encodeDelimWord (List.replicate d false) ++ tW5) tSch
  rcases BitMachine.ComputesInTime.loopNonEmptyWord_list_le kWork2 encU
    (unpackSlotRevStep d) stepBound stkOf
    (fun u rem st restW2 => by
      rcases st with ⟨carryBit, accRev⟩
      dsimp only [stkOf, unpackSlotRevStep, stepBound]
      simp only [update_mkTapes8_kWork2]
      have b1 := tmPopFirstSubwordRev_computesInTime kWork2 kWork0 (by decide)
        (encodeDelimWord (encU u) ++ encodeWordStack (rem.map encU)) restW2 []
        (mkTapes8 [] [] [] []
          (encodeDelimWord (encodeNatBits B_slot carryBit.toNat) ++ tW3)
          (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
          (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, List.append_nil,
        unconsDelimWord_encodeDelimWord_append] at b1
      have b2 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
        (encU u).reverse [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
          (encodeDelimWord (encodeNatBits B_slot carryBit.toNat) ++ tW3)
          (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
          (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
        List.reverse_reverse, List.append_nil] at b2
      have b3 := tmRevMoveWord_computesInTime kWork3 kWork0 (by decide)
        (encodeNatBits B_slot carryBit.toNat) tW3 []
        (mkTapes8 (encodeDelimWord (encU u)) [] []
          (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
          [] (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
          (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0,
        List.append_nil, encodeNatBits_length] at b3
      have b4 := tmPackPairFromRevSwapped_computesInTime
        (encU u) (encodeNatBits B_slot carryBit.toNat)
        (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
        tW3 (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
        (encodeDelimWord (List.replicate d false) ++ tW5) tSch
      have hcarry_lt : carryBit.toNat < 2 ^ B_slot := by
        have h1 : carryBit.toNat < 2 ^ 1 := by cases carryBit <;> decide
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))
      rcases bmRippleAdd_unsigned_computesInTime B_slot u.1 carryBit.toNat u.2 hcarry_lt
        (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
        tW3 (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
        (encodeDelimWord (List.replicate d false) ++ tW5) tSch with ⟨tAdd, htAdd, b5⟩
      set total : ℕ := u.1 + carryBit.toNat
      set slot : ℤ := extractSignedSlot B_slot (total : ℤ)
      set nextBit : Bool :=
        decide ((total / 2 ^ d) % 2 = 1) || decide ((total / 2 ^ (d + 1)) % 2 = 1)
      have b6 := tmRevMoveWord_computesInTime kIO kWork0 (by decide)
        (encodeNatBits (B_slot + 1) total) [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
          tW3 (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
          (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
        encodeNatBits_length] at b6
      have b7 := tmMoveWord_computesInTime kWork0 kWork1 kIO (by decide) (by decide) (by decide)
        (encodeNatBits (B_slot + 1) total).reverse [] [] []
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
          tW3 (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
          (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, update_mkTapes8_kIO,
        List.length_reverse, encodeNatBits_length, List.append_nil] at b7
      rcases tmExtractSignedSlotFromRev_computesInTime d u.1 u.2 carryBit
        (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
        tW3 (encodeDelimWord (encList (encodeSignedWord B_slot) accRev) ++ tW4)
        (encodeDelimWord (List.replicate d false) ++ tW5) tSch with ⟨tExtr, htExtr, b8⟩
      have b9 := tmPrependRevWord_computesInTime kIO kWork4 (by decide)
        (encodeSignedWord B_slot slot).reverse
        (encList (encodeSignedWord B_slot) accRev) [] tW4
        (mkTapes8 [] [] (encodeDelimWord [nextBit])
          (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
          tW3 [] (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork4, List.length_reverse,
        List.reverse_reverse, length_encodeSignedWord, List.append_nil] at b9
      have b10 := tmDupWord_computesInTime kWork5 kWork0 kWork3 (by decide) (by decide) (by decide)
        (List.replicate d false) tW5 [] tW3
        (mkTapes8 [] [] (encodeDelimWord [nextBit])
          (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
          [] (encodeDelimWord (encodeDelimWord (encodeSignedWord B_slot slot) ++
            encList (encodeSignedWord B_slot) accRev) ++ tW4) [] tSch)
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
        List.length_replicate] at b10
      have b11 := tmConcatRevWord_computesInTime kWork1 kWork3 (by decide)
        [nextBit] (List.replicate d false) [] tW3
        (mkTapes8 [] [] []
          (encodeDelimWord (encodeWordStack (rem.map encU)) ++ restW2)
          [] (encodeDelimWord (encodeDelimWord (encodeSignedWord B_slot slot) ++
            encList (encodeSignedWord B_slot) accRev) ++ tW4)
          (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork3, List.reverse_singleton,
        List.singleton_append, List.length_singleton, List.append_nil,
        encodeNatBits_bool_toNat d nextBit] at b11
      have hseq := b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (b6.seq (b7.seq (b8.seq
        (b9.seq (b10.seq b11)))))))))
      simp only [encU, encNatWord, encodeNatBits_length] at hseq
      exact ⟨_, by omega, hseq⟩)
    us tW2 (false, []) with ⟨tL, htL, s11⟩
  dsimp only [stkOf, stepBound] at htL s11
  simp only [update_mkTapes8_kWork2, encList_nil] at s11
  have s12 := tmDropWord_computesInTime kWork3 (encodeNatBits B_slot stF.1.toNat) tW3
    (mkTapes8 [] [] [] tW2 []
      (encodeDelimWord (encList (encodeSignedWord B_slot) stF.2) ++ tW4)
      (encodeDelimWord (List.replicate d false) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork3, encodeNatBits_length] at s12
  have s13 := tmDropWord_computesInTime kWork5 (List.replicate d false) tW5
    (mkTapes8 [] [] [] tW2 tW3
      (encodeDelimWord (encList (encodeSignedWord B_slot) stF.2) ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5, List.length_replicate] at s13
  have s14 := tmMoveWord_computesInTime kWork4 kWork0 kIO (by decide) (by decide) (by decide)
    (encList (encodeSignedWord B_slot) stF.2) tW4 [] []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s14
  rcases bmRevList_computesStageLe (encodeSignedWord B_slot) stF.2
    tW2 tW3 tW4 tW5 tSch with ⟨tR, htR, s15⟩
  dsimp only at htR
  have hlen_us : (encList encU us).length = us.length * (2 * B_slot + 2) :=
    length_encList_encNatWord B_slot Subtype.val us
  have hlen_stF2 : stF.2.length = us.length := by
    have h := length_loopListFinalState_unpackSlotRevStep d us false []
    simpa [stF] using h
  have hlen_enc_stF2 :
      (encList (encodeSignedWord B_slot) stF.2).length = us.length * (2 * B_slot + 4) := by
    have h := length_encList_encodeSignedWord B_slot id stF.2
    dsimp only [id] at h
    rw [h, hlen_stF2]
  have hbL := loopListStepsAux_unpackSlotRevStep_le d us (false, [])
  simp only [hlen_enc_stF2] at s14 htR
  simp only [encPair, length_encUnary, hlen_us] at s1 s2 s3 s5 ⊢
  have hB_def : B_slot = d + 1 := rfl
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
      (s11.seq (s12.seq (s13.seq (s14.seq s15)))))))))))))⟩
  nlinarith

/-- **Stage 31 (`bmUnpackSignedSlotsBits`)**:
Consumes `(d, (m, (d + 1, bs)))` on `kIO` (`B_slot = d + 1 ≥ 1`) and produces
`encList (encodeSignedWord B_slot) (unpackSignedSlotsBits B_slot m bs)` on `kIO` in
**strictly linear** $O(m \cdot B_{\text{slot}} + |bs|)$ `TM2.step` transitions. -/
def bmUnpackSignedSlotsBits : BitMachine :=
  bmSeq (bmPairMap bmId bmSliceBitChunks) bmUnpackSignedSlotsLoop

theorem bmUnpackSignedSlotsBits_computesInTime (d m : ℕ) (bs : List Bool)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let B_slot := d + 1
    ∃ t ≤ m * (110 * B_slot + 200) + 60 * bs.length + 110 * B_slot + 400,
      bmUnpackSignedSlotsBits.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary
          (encPair encUnary (encPair encUnary encBits))
          (d, (m, (B_slot, bs)))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encList (encodeSignedWord B_slot)
          (unpackSignedSlotsBits B_slot m bs)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro B_slot
  let S_slice := Unit
  have hslice_stage : ComputesStageLe bmSliceBitChunks
      (fun _ : S_slice => encPair encUnary (encPair encUnary encBits) (m, (B_slot, bs)))
      (fun _ : S_slice => encList (encNatWord B_slot) (sliceBitChunks B_slot m bs))
      (fun _ => ())
      (fun _ => 30 * m * (B_slot + 1) + 7 * bs.length + 12 * B_slot + 55) := by
    intro _ u2 u3 u4 u5 uS
    exact bmSliceBitChunks_computesInTime m B_slot bs u2 u3 u4 u5 uS
  have p1 := bmPairMap_computesStageLe (bmId_computesStageLe encUnary) hslice_stage
  rcases p1 (d, ()) tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  dsimp only [id] at ht1 s1
  rw [← encList_sliceBitChunksBounded B_slot m bs] at s1
  rcases bmUnpackSignedSlotsLoop_computesInTime (sliceBitChunksBounded B_slot m bs)
    tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  have hspec := loopListFinalState_unpackSlotRevStep_spec d m bs false []
  simp only [List.reverse_nil, List.nil_append] at hspec
  have hspec' :
      (loopListFinalState (unpackSlotRevStep d)
        (sliceBitChunksBounded B_slot m bs) (false, [])).2.reverse =
      unpackSignedSlotsBits B_slot m bs := hspec
  rw [hspec'] at s2
  have hlen_ch := length_encList_sliceBitChunks B_slot m bs
  simp only [length_sliceBitChunksBounded] at ht2
  simp only [encPair, encBits, id, length_encUnary, hlen_ch,
    List.length_append, length_encodeDelimWord] at ht1
  have hB_def : B_slot = d + 1 := rfl
  exact ⟨t1 + t2, by nlinarith, s1.seq s2⟩

/-! ## 3. Base-Case $O(w^2)$ Shift-and-Add Multiplication (`bmBitMulAddDirect`, `bmShiftAddMulBits`, Stage 32) -/

/-- Pushes `encodeDelimWord []` (`[true, false]`) onto the 5 stacks `kWork2..kWork5` and `kSched`
in `1` `TM2.step` transition (`|Λ| = 1`), framing a 3-stack machine whose inputs sit on `kIO`, `kWork0`, and `kWork1`
(`threeTapeWorkStk ms xs ys`). -/
def tmFramePush3Tape : BitMachine where
  Λ := Unit
  main := ()
  m := fun _ =>
    Turing.TM2.Stmt.push kWork2 (fun _ => false)
      (Turing.TM2.Stmt.push kWork2 (fun _ => true)
        (Turing.TM2.Stmt.push kWork3 (fun _ => false)
          (Turing.TM2.Stmt.push kWork3 (fun _ => true)
            (Turing.TM2.Stmt.push kWork4 (fun _ => false)
              (Turing.TM2.Stmt.push kWork4 (fun _ => true)
                (Turing.TM2.Stmt.push kWork5 (fun _ => false)
                  (Turing.TM2.Stmt.push kWork5 (fun _ => true)
                    (Turing.TM2.Stmt.push kSched (fun _ => false)
                      (Turing.TM2.Stmt.push kSched (fun _ => true)
                        Turing.TM2.Stmt.halt)))))))))

@[simp] theorem numLabels_tmFramePush3Tape : tmFramePush3Tape.numLabels = 1 := rfl

theorem tmFramePush3Tape_computesInTime (ms xs ys tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    tmFramePush3Tape.ComputesInTime
      (mkTapes8 (encodeDelimWord ms ++ tIO) (encodeDelimWord xs ++ tW0)
        (encodeDelimWord ys ++ tW1) tW2 tW3 tW4 tW5 tSch)
      (embedDelimFrame (threeTapeWorkStk ms xs ys)
        (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch))
      1 := by
  refine ⟨EvalsToInTime.step_one ?_⟩
  simp only [tmFramePush3Tape, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, Option.some.injEq, Turing.TM2.Cfg.mk.injEq,
    true_and]
  funext k; fin_cases k <;> rfl

/-- Direct delimited-frame wrapper around `tmUniformBitMulAdd`: consumes `encodeDelimWord [mBit]`
on `kIO`, `encodeDelimWord (encodeNatBits w acc)` on `kWork0`, and `encodeDelimWord (encodeNatBits w b)`
on `kWork1`, and produces `encodeDelimWord (encodeNatBits (w + 1) (acc + if mBit then b else 0))`
on `kIO` in `5 * w + 8` `TM2.step` transitions. -/
def bmBitMulAddDirect : BitMachine :=
  tmFramePush3Tape.seq
    ((BitMachine.ofButterflyDelim BitMulAddLabel .popMulBit tmUniformBitMulAdd.m).seq
      tmFramePop7)

theorem bmBitMulAddDirect_computesInTime (mBit : Bool) (w acc b : ℕ)
    (hacc : acc < 2 ^ w) (hb : b < 2 ^ w)
    (tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    bmBitMulAddDirect.ComputesInTime
      (mkTapes8 (encodeDelimWord [mBit] ++ tIO)
        (encodeDelimWord (encodeNatBits w acc) ++ tW0)
        (encodeDelimWord (encodeNatBits w b) ++ tW1)
        tW2 tW3 tW4 tW5 tSch)
      (mkTapes8 (encodeDelimWord (encodeNatBits (w + 1) (acc + if mBit then b else 0)) ++ tIO)
        tW0 tW1 tW2 tW3 tW4 tW5 tSch)
      (1 + ((5 * w + 6) + 1)) := by
  have s1 := tmFramePush3Tape_computesInTime [mBit] (encodeNatBits w acc) (encodeNatBits w b)
    tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch
  have s2 := BitMachine.ofButterflyDelim_computesInTime (Λ := BitMulAddLabel)
    .popMulBit tmUniformBitMulAdd.m
    (stk₁ := threeTapeWorkStk [mBit] (encodeNatBits w acc) (encodeNatBits w b))
    (stk₂ := singleTapeStk (encodeNatBits (w + 1) (acc + if mBit then b else 0)))
    (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch)
    (tmUniformBitMulAdd_encodeNatBits_evalsToInTime_concrete mBit w acc b hacc hb)
  have s3 := tmFramePop7_computesInTime
    (encodeNatBits (w + 1) (acc + if mBit then b else 0))
    tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch
  exact s1.seq (s2.seq s3)

/-- `takePadBits w bs` is the `w`-bit unsigned binary encoding of `decodeNatBits (bs.take w)`. -/
@[simp]
theorem takePadBits_eq_encodeNatBits_decodeNatBits_take (w : ℕ) (bs : List Bool) :
    takePadBits w bs = encodeNatBits w (decodeNatBits (bs.take w)) := by
  induction w generalizing bs with
  | zero =>
    simp [takePadBits, encodeNatBits]
  | succ w ih =>
    cases bs with
    | nil =>
      simp only [takePadBits, List.headD_nil, List.tail_nil, List.take_nil, decodeNatBits,
        encodeNatBits_zero, List.replicate_succ]
      rw [ih [], List.take_nil, decodeNatBits, encodeNatBits_zero]
    | cons bit rest =>
      simp only [takePadBits, List.headD_cons, List.tail_cons, List.take_succ_cons, decodeNatBits]
      rw [ih rest, encodeNatBits_succ_mod_div]
      cases bit <;> simp only [cond_false, cond_true, Nat.zero_add]
      · simp
      · have hm : (1 + 2 * decodeNatBits (rest.take w)) % 2 = 1 := by omega
        have hd : (1 + 2 * decodeNatBits (rest.take w)) / 2 = decodeNatBits (rest.take w) := by omega
        simp [hm, hd]

/-- Pure state step for `bmShiftAddMulFixedWidth`: pops the next multiplier bit `mBit` from `aBits`,
adds `if mBit then b else 0` to `acc < 2 ^ w`, shifts out the low bit `decide (total % 2 = 1)` onto
`lowRev`, and keeps `total / 2 < 2 ^ w` as the new accumulator. -/
def shiftAddMulPureStep (w b : ℕ) (hb : b < 2 ^ w)
    (st : { x : ℕ // x < 2 ^ w } × List Bool × List Bool) :
    { x : ℕ // x < 2 ^ w } × List Bool × List Bool :=
  let acc := st.1.1
  let aBits := st.2.1
  let lowRev := st.2.2
  let mBit := aBits.headD false
  let total := acc + if mBit then b else 0
  have htot : total < 2 ^ (w + 1) := by
    have hacc := st.1.2
    rw [Nat.pow_succ]
    dsimp only [total]
    split_ifs <;> omega
  have hdiv : total / 2 < 2 ^ w := by
    rw [Nat.pow_succ] at htot
    omega
  (⟨total / 2, hdiv⟩, aBits.tail, decide (total % 2 = 1) :: lowRev)

theorem loopFinalState_shiftAddMulPureStep_spec (w b : ℕ) (hb : b < 2 ^ w) :
    ∀ (k : ℕ) (a_rem : ℕ) (_ha : a_rem < 2 ^ k)
      (acc : { x : ℕ // x < 2 ^ w }) (lowRev : List Bool),
      let stF := loopFinalState (shiftAddMulPureStep w b hb) (encUnary k)
        (acc, encodeNatBits k a_rem, lowRev)
      stF.2.1 = [] ∧
        stF.2.2.reverse ++ encodeNatBits w stF.1.1 =
          lowRev.reverse ++ encodeNatBits (k + w) (acc.1 + a_rem * b)
  | 0, a_rem, ha, acc, lowRev => by
    have ha0 : a_rem = 0 := by omega
    subst ha0
    simp [encUnary, encodeNatBits]
  | k + 1, a_rem, ha, acc, lowRev => by
    have ha2 : a_rem / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at ha
      omega
    have hcons : encUnary (k + 1) = false :: encUnary k := List.replicate_succ
    dsimp only
    rw [hcons, loopFinalState_cons, encodeNatBits_succ_mod_div k a_rem]
    dsimp only [shiftAddMulPureStep, List.headD_cons, List.tail_cons]
    set mBit := decide (a_rem % 2 = 1)
    set total := acc.1 + if mBit then b else 0
    have htot_lt : total < 2 ^ (w + 1) := by
      have hacc := acc.2
      rw [Nat.pow_succ]
      dsimp only [total]
      split_ifs <;> omega
    have hdiv_lt : total / 2 < 2 ^ w := by
      rw [Nat.pow_succ] at htot_lt
      omega
    rcases loopFinalState_shiftAddMulPureStep_spec w b hb k (a_rem / 2) ha2
      ⟨total / 2, hdiv_lt⟩ (decide (total % 2 = 1) :: lowRev) with ⟨hempty, hbits⟩
    refine ⟨hempty, ?_⟩
    rw [hbits]
    have htot_eq : total + 2 * ((a_rem / 2) * b) = acc.1 + a_rem * b := by
      have hmod : a_rem % 2 = 0 ∨ a_rem % 2 = 1 := Nat.mod_two_eq_zero_or_one a_rem
      have hdecomp : 2 * (a_rem / 2) + a_rem % 2 = a_rem := Nat.div_add_mod a_rem 2
      rcases hmod with h0 | h1
      · have hm : mBit = false := by simp [mBit, h0]
        have ht : total = acc.1 := by simp [total, hm]
        nlinarith
      · have hm : mBit = true := by simp [mBit, h1]
        have ht : total = acc.1 + b := by simp [total, hm]
        nlinarith
    have hdiv_sum : total / 2 + (a_rem / 2) * b = (acc.1 + a_rem * b) / 2 := by
      rw [← htot_eq, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
    have hmod_sum : decide (total % 2 = 1) = decide ((acc.1 + a_rem * b) % 2 = 1) := by
      rw [← htot_eq, Nat.add_mul_mod_self_left]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append,
      hmod_sum, hdiv_sum, ← encodeNatBits_succ_mod_div (k + w) (acc.1 + a_rem * b),
      Nat.succ_add]

theorem loopStepsAux_shiftAddMulPureStep_eq (w b : ℕ) (hb : b < 2 ^ w) :
    ∀ (u : List Bool) (st : { x : ℕ // x < 2 ^ w } × List Bool × List Bool),
      loopStepsAux (shiftAddMulPureStep w b hb) (fun _ => 11 * w + 23) u st =
        u.length * (11 * w + 24) + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: u, st => by
    simp only [loopStepsAux_cons, List.length_cons,
      loopStepsAux_shiftAddMulPureStep_eq w b hb u]
    ring

/-- Fixed-width shift-and-add kernel consuming `(w, (encodeNatBits w a, encodeNatBits w b))` on
`kIO` and producing `encodeNatBits (2 * w) (a * b)` on `kIO` in $O(w^2)$ `TM2.step` transitions. -/
def bmShiftAddMulFixedWidth : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork1).seq
      ((tmDupWord kWork1 kWork0 kSched).seq
        ((tmPushEmpty kWork3).seq
          (((tmConsBit false kWork3).loopDelimWord kWork1).seq
            ((tmPopFirstSubwordRev kIO kWork0).seq
              ((tmDropWord kIO).seq
                ((tmRevMoveWord kWork0 kIO).seq
                  ((tmPopFirstSubwordRev kIO kWork0).seq
                    ((tmRevMoveWord kWork0 kWork2).seq
                      ((tmPopFirstSubwordRev kIO kWork0).seq
                        ((tmDropWord kIO).seq
                          ((tmRevMoveWord kWork0 kWork5).seq
                            ((tmPushEmpty kWork4).seq
                              ((((tmPushEmpty kIO).seq
                                  ((tmPopBitOrZero kWork2 kIO).seq
                                    ((tmMoveWord kWork3 kWork1 kWork0).seq
                                      ((tmDupWord kWork5 kWork3 kWork1).seq
                                        (bmBitMulAddDirect.seq
                                          ((tmPopBitOrZero kIO kWork4).seq
                                            (tmMoveWord kIO kWork0 kWork3))))))).loopDelimWord kSched).seq
                                ((tmDropWord kWork2).seq
                                  ((tmDropWord kWork5).seq
                                    ((tmMoveWord kWork3 kWork0 kIO).seq
                                      (tmConcatRevWord kWork4 kIO))))))))))))))))))

theorem bmShiftAddMulFixedWidth_computesInTime (w a b : ℕ)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 11 * w * w + 55 * w + 50,
      bmShiftAddMulFixedWidth.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encPair encBits encBits)
          (w, (encodeNatBits w a, encodeNatBits w b))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeNatBits (2 * w) (a * b)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  set aBits := encodeNatBits w a
  set bBits := encodeNatBits w b
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary w) ++
      encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
    (encUnary w).reverse [] []
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.length_reverse,
    List.reverse_reverse, List.append_nil, length_encUnary] at s2
  have s3 := tmDupWord_computesInTime kWork1 kWork0 kSched (by decide) (by decide) (by decide)
    (encUnary w) [] [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, update_mkTapes8_kSched,
    List.append_nil, length_encUnary] at s3
  have s4 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] (encodeDelimWord (encUnary w)) tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s4
  have s5 := consBit_loopDelimWord_computesInTime false kWork1 kWork3 (by decide)
    (encUnary w) [] [] tW3
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] [] tW2 [] tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork3, List.append_nil,
    length_encUnary] at s5
  have hzero_w : List.replicate w false = encodeNatBits w 0 := (encodeNatBits_zero w).symm
  rw [hzero_w] at s5
  have s6 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)) [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s6
  have s7 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits).reverse) []
      tW2 (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s7
  have s8 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encodeDelimWord aBits ++ encodeDelimWord bBits).reverse [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s8
  have s9 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord aBits ++ encodeDelimWord bBits) [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s9
  have s10 := tmRevMoveWord_computesInTime kWork0 kWork2 (by decide)
    aBits.reverse [] tW2
    (mkTapes8 (encodeDelimWord (encodeDelimWord bBits)) [] [] []
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork2, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s10
  have s11 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord bBits) [] []
    (mkTapes8 [] [] [] (encodeDelimWord aBits ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s11
  have s12 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord bBits.reverse) [] (encodeDelimWord aBits ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s12
  have s13 := tmRevMoveWord_computesInTime kWork0 kWork5 (by decide)
    bBits.reverse [] tW5
    (mkTapes8 [] [] [] (encodeDelimWord aBits ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 [] (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork5, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s13
  have s14 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord aBits ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 (encodeDelimWord bBits ++ tW5) (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s14
  let stkOf : { x : ℕ // x < 2 ^ w } × List Bool × List Bool →
      (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] (encodeDelimWord st.2.1 ++ tW2)
      (encodeDelimWord (encodeNatBits w st.1.1) ++ tW3)
      (encodeDelimWord st.2.2 ++ tW4)
      (encodeDelimWord bBits ++ tW5) []
  have hloop := BitMachine.ComputesInTime.loopDelimWord_state kSched
    (shiftAddMulPureStep w b hb) (fun _ => 11 * w + 23) stkOf
    (fun st tailSch => by
      rcases st with ⟨acc, remA, lowRev⟩
      dsimp only [stkOf, shiftAddMulPureStep]
      simp only [update_mkTapes8_kSched]
      have b1 := tmPushEmpty_computesInTime kIO
        (mkTapes8 [] [] [] (encodeDelimWord remA ++ tW2)
          (encodeDelimWord (encodeNatBits w acc.1) ++ tW3)
          (encodeDelimWord lowRev ++ tW4)
          (encodeDelimWord bBits ++ tW5) tailSch)
      simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at b1
      have b2 := tmPopBitOrZero_computesInTime kWork2 kIO (by decide)
        remA [] tW2 []
        (mkTapes8 [] [] [] []
          (encodeDelimWord (encodeNatBits w acc.1) ++ tW3)
          (encodeDelimWord lowRev ++ tW4)
          (encodeDelimWord bBits ++ tW5) tailSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kIO, List.append_nil] at b2
      have b3 := tmMoveWord_computesInTime kWork3 kWork1 kWork0 (by decide) (by decide) (by decide)
        (encodeNatBits w acc.1) tW3 [] []
        (mkTapes8 (encodeDelimWord [remA.headD false]) [] []
          (encodeDelimWord remA.tail ++ tW2) []
          (encodeDelimWord lowRev ++ tW4)
          (encodeDelimWord bBits ++ tW5) tailSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
        List.append_nil, encodeNatBits_length] at b3
      have b4 := tmDupWord_computesInTime kWork5 kWork3 kWork1 (by decide) (by decide) (by decide)
        bBits tW5 tW3 []
        (mkTapes8 (encodeDelimWord [remA.headD false])
          (encodeDelimWord (encodeNatBits w acc.1)) []
          (encodeDelimWord remA.tail ++ tW2) []
          (encodeDelimWord lowRev ++ tW4) [] tailSch)
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork3, update_mkTapes8_kWork1,
        List.append_nil, bBits, encodeNatBits_length] at b4
      have b5 := bmBitMulAddDirect_computesInTime (remA.headD false) w acc.1 b acc.2 hb
        [] [] []
        (encodeDelimWord remA.tail ++ tW2) tW3
        (encodeDelimWord lowRev ++ tW4)
        (encodeDelimWord (encodeNatBits w b) ++ tW5) tailSch
      simp only [List.append_nil] at b5
      set total := acc.1 + if remA.headD false then b else 0
      have htot_split : encodeNatBits (w + 1) total =
          decide (total % 2 = 1) :: encodeNatBits w (total / 2) :=
        encodeNatBits_succ_mod_div w total
      rw [htot_split] at b5
      have b6 := tmPopBitOrZero_computesInTime kIO kWork4 (by decide)
        (decide (total % 2 = 1) :: encodeNatBits w (total / 2)) lowRev [] tW4
        (mkTapes8 [] [] []
          (encodeDelimWord remA.tail ++ tW2) tW3 []
          (encodeDelimWord (encodeNatBits w b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork4, List.append_nil,
        List.headD_cons, List.tail_cons] at b6
      have b7 := tmMoveWord_computesInTime kIO kWork0 kWork3 (by decide) (by decide) (by decide)
        (encodeNatBits w (total / 2)) [] [] tW3
        (mkTapes8 [] [] []
          (encodeDelimWord remA.tail ++ tW2) []
          (encodeDelimWord (decide (total % 2 = 1) :: lowRev) ++ tW4)
          (encodeDelimWord (encodeNatBits w b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork3,
        List.append_nil, encodeNatBits_length] at b7
      have hseq := b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (b6.seq b7)))))
      exact hseq.mono (by omega))
    (encUnary w) tSch (⟨0, Nat.two_pow_pos w⟩, aBits, [])
  dsimp only [stkOf] at hloop
  simp only [update_mkTapes8_kSched] at hloop
  set stF := loopFinalState (shiftAddMulPureStep w b hb) (encUnary w)
    (⟨0, Nat.two_pow_pos w⟩, aBits, [])
  rcases loopFinalState_shiftAddMulPureStep_spec w b hb w a ha ⟨0, Nat.two_pow_pos w⟩ [] with
    ⟨hremF, hbitsF⟩
  simp only [List.reverse_nil, List.nil_append, Nat.zero_add,
    show w + w = 2 * w by ring] at hbitsF
  have hremF' : stF.2.1 = [] := hremF
  have hbitsF' : stF.2.2.reverse ++ encodeNatBits w stF.1.1 = encodeNatBits (2 * w) (a * b) :=
    hbitsF
  rw [hremF'] at hloop
  have s15 := tmDropWord_computesInTime kWork2 [] tW2
    (mkTapes8 [] [] [] []
      (encodeDelimWord (encodeNatBits w stF.1.1) ++ tW3)
      (encodeDelimWord stF.2.2 ++ tW4)
      (encodeDelimWord bBits ++ tW5) tSch)
  simp only [update_mkTapes8_kWork2, List.length_nil] at s15
  have s16 := tmDropWord_computesInTime kWork5 bBits tW5
    (mkTapes8 [] [] [] tW2
      (encodeDelimWord (encodeNatBits w stF.1.1) ++ tW3)
      (encodeDelimWord stF.2.2 ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5, bBits, encodeNatBits_length] at s16
  have s17 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encodeNatBits w stF.1.1) tW3 [] []
    (mkTapes8 [] [] [] tW2 [] (encodeDelimWord stF.2.2 ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil, encodeNatBits_length] at s17
  have s18 := tmConcatRevWord_computesInTime kWork4 kIO (by decide)
    stF.2.2 (encodeNatBits w stF.1.1) tW4 []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kIO, List.append_nil] at s18
  have hlen_stF2 : stF.2.2.length = w := by
    have h := congrArg List.length hbitsF'
    simp only [List.length_append, List.length_reverse, encodeNatBits_length] at h
    omega
  rw [hbitsF', hlen_stF2] at s18
  rw [loopStepsAux_shiftAddMulPureStep_eq w b hb (encUnary w), length_encUnary] at hloop
  simp only [aBits, bBits, encPair, encBits, id, length_encUnary, encodeNatBits_length,
    List.length_append, length_encodeDelimWord] at s1 s6 s8 s9 s10 s11 s13 ⊢
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
      (s11.seq (s12.seq (s13.seq (s14.seq (hloop.seq (s15.seq (s16.seq (s17.seq s18)))))))))))))))))⟩
  nlinarith

/-- Helper routing `(w, (aBits, bBits))` to `(w, ((w, aBits), (w, bBits)))` on `kIO`. -/
def bmDistributeWidthPair : BitMachine :=
  bmFanout bmFst
    (bmFanout
      (bmFanout bmFst (bmSeq bmSnd bmFst))
      (bmFanout bmFst (bmSeq bmSnd bmSnd)))

theorem bmDistributeWidthPair_computesStageLe :
    ComputesStageLe bmDistributeWidthPair
      (encPair encUnary (encPair encBits encBits))
      (encPair encUnary (encPair (encPair encUnary encBits) (encPair encUnary encBits)))
      (fun p => (p.1, ((p.1, p.2.1), (p.1, p.2.2))))
      (fun p => 85 * p.1 + 120 * p.2.1.length + 120 * p.2.2.length + 750) := by
  have p_w := bmFst_computesStageLe encUnary (encPair encBits encBits)
  have p_ab := bmSnd_computesStageLe encUnary (encPair encBits encBits)
  have p_a := bmSeq_computesStageLe p_ab (bmFst_computesStageLe encBits encBits)
  have p_b := bmSeq_computesStageLe p_ab (bmSnd_computesStageLe encBits encBits)
  have p_wa := bmFanout_computesStageLe p_w p_a
  have p_wb := bmFanout_computesStageLe p_w p_b
  have p_pair := bmFanout_computesStageLe p_wa p_wb
  refine (bmFanout_computesStageLe p_w p_pair).mono (fun ⟨w, aBits, bBits⟩ => ?_)
  dsimp only [encPair, encBits, id]
  simp only [length_encUnary, List.length_append, length_encodeDelimWord]
  omega

/-- **Stage 32 (`bmShiftAddMulBits`)**:
Consumes `(w, (aBits, bBits))` on `kIO` and produces
`(binaryShiftAddMulBitsTracked w aBits bBits).1 = encodeNatBits (2 * w) (decodeNatBits (aBits.take w) * decodeNatBits (bBits.take w))`
on `kIO` in $O(w^2 + |aBits| + |bBits|)$ `TM2.step` transitions. -/
def bmShiftAddMulBits : BitMachine :=
  (bmSeq bmDistributeWidthPair
    (bmPairMap bmId (bmPairMap bmTakePadBits bmTakePadBits))).seq
    bmShiftAddMulFixedWidth

theorem bmShiftAddMulBits_computesInTime (w : ℕ) (aBits bBits : List Bool)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 11 * w * w + 350 * w + 200 * aBits.length + 200 * bBits.length + 1300,
      bmShiftAddMulBits.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encPair encBits encBits)
          (w, (aBits, bBits))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (binaryShiftAddMulBitsTracked w aBits bBits).1)
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have p_pad := bmPairMap_computesStageLe bmTakePadBits_computesStageLe bmTakePadBits_computesStageLe
  have p_mid := bmSeq_computesStageLe bmDistributeWidthPair_computesStageLe
    (bmPairMap_computesStageLe (bmId_computesStageLe encUnary) p_pad)
  rcases p_mid (w, (aBits, bBits)) tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  simp only [id, takePadBits_eq_encodeNatBits_decodeNatBits_take] at s1
  set a := decodeNatBits (aBits.take w)
  set b := decodeNatBits (bBits.take w)
  have ha : a < 2 ^ w := decodeNatBits_take_lt w aBits
  have hb : b < 2 ^ w := decodeNatBits_take_lt w bBits
  rcases bmShiftAddMulFixedWidth_computesInTime w a b ha hb tW2 tW3 tW4 tW5 tSch with
    ⟨t2, ht2, s2⟩
  rw [← binaryShiftAddMulBitsTracked_fst w aBits bBits] at s2
  dsimp only [id] at ht1
  simp only [encPair, encBits, id, length_encUnary, length_takePadBits,
    List.length_append, length_encodeDelimWord] at ht1
  exact ⟨t1 + t2, by nlinarith, s1.seq s2⟩

/-! ## 4. $O(w^2)$ Restoring Binary Division (`bmCondSubDirect`, `bmRestoringDivMod`, Stage 33) -/

/-- Direct delimited-frame wrapper around `tmUniformCondSubStep`: consumes
`encodeDelimWord (encodeNatBits w R)` on `kWork0` and `encodeDelimWord (encodeNatBits w D)` on
`kWork1`, and produces `encodeDelimWord (encodeNatBits w (if D ≤ R then R - D else R))` on `kIO`
and `encodeDelimWord [decide (D ≤ R)]` on `kWork0` in `7 * w + 5` `TM2.step` transitions. -/
def bmCondSubDirect : BitMachine :=
  tmFramePush5.seq
    ((BitMachine.ofButterflyDelim CondSubStepLabel .popA tmUniformCondSubStep.m).seq
      tmFramePop6)

theorem bmCondSubDirect_computesInTime (w R D : ℕ) (hR : R < 2 ^ w) (hD : D < 2 ^ w)
    (tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    bmCondSubDirect.ComputesInTime
      (mkTapes8 tIO (encodeDelimWord (encodeNatBits w R) ++ tW0)
        (encodeDelimWord (encodeNatBits w D) ++ tW1)
        tW2 tW3 tW4 tW5 tSch)
      (mkTapes8 (encodeDelimWord (encodeNatBits w (if D ≤ R then R - D else R)) ++ tIO)
        (encodeDelimWord [decide (D ≤ R)] ++ tW0)
        tW1 tW2 tW3 tW4 tW5 tSch)
      (1 + ((7 * w + 3) + 1)) := by
  have s1 := tmFramePush5_computesInTime (encodeNatBits w R) (encodeNatBits w D)
    tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch
  have s2 := BitMachine.ofButterflyDelim_computesInTime (Λ := CondSubStepLabel)
    .popA tmUniformCondSubStep.m
    (stk₁ := threeTapeWorkStk [] (encodeNatBits w R) (encodeNatBits w D))
    (stk₂ := twoTapeStk (encodeNatBits w (if D ≤ R then R - D else R)) [decide (D ≤ R)])
    (mkTapes8 tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch)
    (tmUniformCondSubStep_encodeNatBits_evalsToInTime_concrete w R D hR hD)
  have s3 := tmFramePop6_computesInTime
    (encodeNatBits w (if D ≤ R then R - D else R)) [decide (D ≤ R)]
    tIO tW0 tW1 tW2 tW3 tW4 tW5 tSch
  exact s1.seq (s2.seq s3)

theorem loopFinalState_append {α : Type} (step : α → α) :
    ∀ (xs ys : List Bool) (st : α),
      loopFinalState step (xs ++ ys) st =
        loopFinalState step ys (loopFinalState step xs st)
  | [], _, _ => rfl
  | _ :: xs, ys, st => loopFinalState_append step xs ys (step st)

theorem encUnary_succ_append (k : ℕ) :
    encUnary (k + 1) = encUnary k ++ [false] := by
  simp [encUnary, List.replicate_succ']

theorem encodeNatBits_succ_eq_append_false {w r : ℕ} (hr : r < 2 ^ w) :
    encodeNatBits (w + 1) r = encodeNatBits w r ++ [false] := by
  rw [encodeNatBits_add_mod_div w 1 r, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr]
  rfl

/-- Pure state step for `bmRestoringDivMod` over `w`-bit unsigned numerator and divisor `0 < b < 2 ^ w`. -/
def restoringDivPureStep (b : ℕ) (_hb : 0 < b)
    (st : { r : ℕ // r < b } × List Bool × List Bool) :
    { r : ℕ // r < b } × List Bool × List Bool :=
  let r' := st.1.1
  let remA := st.2.1
  let qBits := st.2.2
  let bit := remA.headD false
  let r_dbl := 2 * r' + bit.toNat
  let qBit := decide (b ≤ r_dbl)
  let r := if b ≤ r_dbl then r_dbl - b else r_dbl
  have hr : r < b := by
    have hr' := st.1.2
    have hbit : bit.toNat ≤ 1 := Bool.toNat_le bit
    dsimp [r, r_dbl]
    split_ifs <;> omega
  (⟨r, hr⟩, remA.tail, qBit :: qBits)

theorem loopFinalState_restoringDivPureStep_spec (w b : ℕ) (hb : 0 < b) :
    ∀ (k a : ℕ) (_ha : a < 2 ^ k) (rest : List Bool),
      loopFinalState (restoringDivPureStep b hb) (encUnary k)
        (⟨0, hb⟩, (encodeNatBits k a).reverse ++ rest, []) =
      (⟨a % b, Nat.mod_lt a hb⟩, rest, encodeNatBits k (a / b))
  | 0, a, ha, rest => by
    have ha0 : a = 0 := by omega
    subst ha0
    simp [encUnary, encodeNatBits]
  | k + 1, a, ha, rest => by
    have ha2 : a / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at ha
      omega
    have hrev_a : (encodeNatBits (k + 1) a).reverse ++ rest =
        (encodeNatBits k (a / 2)).reverse ++ (decide (a % 2 = 1) :: rest) := by
      rw [encodeNatBits_succ_mod_div k a, List.reverse_cons, List.append_assoc,
        List.singleton_append]
    rw [encUnary_succ_append k, hrev_a, loopFinalState_append,
      loopFinalState_restoringDivPureStep_spec w b hb k (a / 2) ha2 (decide (a % 2 = 1) :: rest)]
    dsimp only [loopFinalState, restoringDivPureStep, List.headD_cons, List.tail_cons]
    have hbit_toNat : (decide (a % 2 = 1)).toNat = a % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
    have hstep := binaryRestoringDivModRegAux_fst w b ha
    simp only [binaryRestoringDivModRegAux, binaryRestoringDivModRegAux_fst w b ha2,
      if_neg (ne_of_gt hb)] at hstep
    have hq_eq : (if b ≤ 2 * ((a / 2) % b) + a % 2 then 2 * ((a / 2) / b) + 1 else 2 * ((a / 2) / b)) =
        a / b := congrArg Prod.fst hstep
    have hr_eq : (if b ≤ 2 * ((a / 2) % b) + a % 2 then 2 * ((a / 2) % b) + a % 2 - b else 2 * ((a / 2) % b) + a % 2) =
        a % b := congrArg Prod.snd hstep
    have hq_bits : decide (b ≤ 2 * ((a / 2) % b) + (decide (a % 2 = 1)).toNat) ::
        encodeNatBits k ((a / 2) / b) = encodeNatBits (k + 1) (a / b) := by
      rw [hbit_toNat, ← hq_eq, encodeNatBits_succ_mod_div k]
      by_cases hcmp : b ≤ 2 * ((a / 2) % b) + a % 2
      · simp only [if_pos hcmp, decide_eq_true hcmp]
        have hm : (2 * ((a / 2) / b) + 1) % 2 = 1 := by omega
        have hd : (2 * ((a / 2) / b) + 1) / 2 = (a / 2) / b := by omega
        simp [hm, hd]
      · simp only [if_neg hcmp, decide_eq_false hcmp]
        have hm : (2 * ((a / 2) / b)) % 2 = 0 := by omega
        have hd : (2 * ((a / 2) / b)) / 2 = (a / 2) / b := by omega
        simp [hm, hd]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext rfl hq_bits)
    simp only [hbit_toNat, hr_eq]

theorem loopStepsAux_restoringDivPureStep_eq (w b : ℕ) (hb : 0 < b) :
    ∀ (u : List Bool) (st : { r : ℕ // r < b } × List Bool × List Bool),
      loopStepsAux (restoringDivPureStep b hb) (fun _ => 13 * w + 38) u st =
        u.length * (13 * w + 39) + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: u, st => by
    simp only [loopStepsAux_cons, List.length_cons,
      loopStepsAux_restoringDivPureStep_eq w b hb u]
    ring

/-- **Stage 33 (`bmRestoringDivMod`)**:
Consumes `(w, (encodeNatBits w a, encodeNatBits w b))` on `kIO` (`a < 2 ^ w`, `0 < b < 2 ^ w`)
and produces `(encodeNatBits w (a / b), encodeNatBits w (a % b))`
(`(binaryRestoringDivModRegTracked w a b).1`) on `kIO` in $O(w^2)$ `TM2.step` transitions. -/
def bmRestoringDivMod : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork1).seq
      ((tmDupWord kWork1 kWork0 kSched).seq
        ((tmPushEmpty kWork3).seq
          (((tmConsBit false kWork3).loopDelimWord kWork1).seq
            ((tmPopFirstSubwordRev kIO kWork0).seq
              ((tmDropWord kIO).seq
                ((tmRevMoveWord kWork0 kIO).seq
                  ((tmPopFirstSubwordRev kIO kWork2).seq
                    ((tmPopFirstSubwordRev kIO kWork0).seq
                      ((tmDropWord kIO).seq
                        ((tmConsBit false kWork0).seq
                          ((tmRevMoveWord kWork0 kWork5).seq
                            ((tmPushEmpty kWork4).seq
                              ((((tmPopBitOrZero kWork2 kWork3).seq
                                  ((tmMoveWord kWork3 kWork1 kWork0).seq
                                    ((tmDupWord kWork5 kWork3 kWork1).seq
                                      (bmCondSubDirect.seq
                                        ((tmConcatRevWord kWork0 kWork4).seq
                                          ((tmRevMoveWord kIO kWork1).seq
                                            ((tmPushEmpty kIO).seq
                                              ((tmPopBitOrZero kWork1 kIO).seq
                                                ((tmDropWord kIO).seq
                                                  (tmRevMoveWord kWork1 kWork3)))))))))).loopDelimWord kSched).seq
                                ((tmDropWord kWork2).seq
                                  ((tmDropWord kWork5).seq
                                    ((tmMoveWord kWork3 kWork0 kIO).seq
                                      ((tmRevMoveWord kWork4 kWork0).seq
                                        tmPackPairFromRev))))))))))))))))))

theorem bmRestoringDivMod_computesInTime (w a b : ℕ)
    (ha : a < 2 ^ w) (hb0 : 0 < b) (hb : b < 2 ^ w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 13 * w * w + 75 * w + 65,
      bmRestoringDivMod.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encPair encBits encBits)
          (w, (encodeNatBits w a, encodeNatBits w b))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair encBits encBits
          (encodeNatBits w (a / b), encodeNatBits w (a % b))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  set aBits := encodeNatBits w a
  set bBits := encodeNatBits w b
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary w) ++
      encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
    (encUnary w).reverse [] []
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.length_reverse,
    List.reverse_reverse, List.append_nil, length_encUnary] at s2
  have s3 := tmDupWord_computesInTime kWork1 kWork0 kSched (by decide) (by decide) (by decide)
    (encUnary w) [] [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, update_mkTapes8_kSched,
    List.append_nil, length_encUnary] at s3
  have s4 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] (encodeDelimWord (encUnary w)) tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s4
  have s5 := consBit_loopDelimWord_computesInTime false kWork1 kWork3 (by decide)
    (encUnary w) [] [] tW3
    (mkTapes8 (encodeDelimWord (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)))
      [] [] tW2 [] tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork3, List.append_nil,
    length_encUnary] at s5
  have hzero_w : List.replicate w false = encodeNatBits w 0 := (encodeNatBits_zero w).symm
  rw [hzero_w] at s5
  have s6 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits)) [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s6
  have s7 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord (encodeDelimWord aBits ++ encodeDelimWord bBits).reverse) []
      tW2 (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s7
  have s8 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    (encodeDelimWord aBits ++ encodeDelimWord bBits).reverse [] []
    (mkTapes8 [] [] [] tW2 (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at s8
  have s9 := tmPopFirstSubwordRev_computesInTime kIO kWork2 (by decide)
    (encodeDelimWord aBits ++ encodeDelimWord bBits) [] tW2
    (mkTapes8 [] [] [] [] (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork2, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s9
  have s10 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord bBits) [] []
    (mkTapes8 [] [] [] (encodeDelimWord aBits.reverse ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s10
  have s11 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord bBits.reverse) [] (encodeDelimWord aBits.reverse ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s11
  have s12 := tmConsBit_computesInTime false kWork0
    (mkTapes8 [] (encodeDelimWord bBits.reverse) [] (encodeDelimWord aBits.reverse ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
    bBits.reverse [] (by simp)
  simp only [update_mkTapes8_kWork0, List.append_nil] at s12
  have s13 := tmRevMoveWord_computesInTime kWork0 kWork5 (by decide)
    (false :: bBits.reverse) [] tW5
    (mkTapes8 [] [] [] (encodeDelimWord aBits.reverse ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 [] (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork5, List.length_cons,
    List.length_reverse, List.reverse_cons, List.reverse_reverse, List.append_nil] at s13
  have hb_w1 : bBits ++ [false] = encodeNatBits (w + 1) b :=
    (encodeNatBits_succ_eq_append_false hb).symm
  rw [hb_w1] at s13
  have s14 := tmPushEmpty_computesInTime kWork4
    (mkTapes8 [] [] [] (encodeDelimWord aBits.reverse ++ tW2)
      (encodeDelimWord (encodeNatBits w 0) ++ tW3)
      tW4 (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5)
      (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork4, mkTapes8_kWork4] at s14
  let stkOf : { r : ℕ // r < b } × List Bool × List Bool →
      (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] (encodeDelimWord st.2.1 ++ tW2)
      (encodeDelimWord (encodeNatBits w st.1.1) ++ tW3)
      (encodeDelimWord st.2.2 ++ tW4)
      (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) []
  have hloop := BitMachine.ComputesInTime.loopDelimWord_state kSched
    (restoringDivPureStep b hb0) (fun _ => 13 * w + 38) stkOf
    (fun st tailSch => by
      rcases st with ⟨r', remA, qBits⟩
      dsimp only [stkOf, restoringDivPureStep]
      simp only [update_mkTapes8_kSched]
      set bit := remA.headD false
      set r_dbl := 2 * r'.1 + bit.toNat
      set qBit := decide (b ≤ r_dbl)
      set r := if b ≤ r_dbl then r_dbl - b else r_dbl
      have hr'_w : r'.1 < 2 ^ w := lt_trans r'.2 hb
      have hr_dbl_w1 : r_dbl < 2 ^ (w + 1) := by
        have hbit : bit.toNat ≤ 1 := Bool.toNat_le bit
        rw [Nat.pow_succ]
        omega
      have hb_w1_lt : b < 2 ^ (w + 1) := by
        rw [Nat.pow_succ]
        omega
      have hr_lt_b : r < b := by
        have hr' := r'.2
        have hbit : bit.toNat ≤ 1 := Bool.toNat_le bit
        dsimp [r, r_dbl]
        split_ifs <;> omega
      have hr_w : r < 2 ^ w := lt_trans hr_lt_b hb
      have hr_dbl_bits : bit :: encodeNatBits w r'.1 = encodeNatBits (w + 1) r_dbl := by
        rw [encodeNatBits_succ_mod_div w r_dbl]
        have hm : decide (r_dbl % 2 = 1) = bit := by
          dsimp only [r_dbl]
          by_cases h : bit = true <;> simp [h, Bool.toNat]
        have hd : r_dbl / 2 = r'.1 := by
          dsimp only [r_dbl]
          (by_cases h : bit = true <;> simp [h, Bool.toNat]); omega
        rw [hm, hd]
      have b1 := tmPopBitOrZero_computesInTime kWork2 kWork3 (by decide)
        remA (encodeNatBits w r'.1) tW2 tW3
        (mkTapes8 [] [] [] [] []
          (encodeDelimWord qBits ++ tW4)
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork3] at b1
      rw [hr_dbl_bits] at b1
      have b2 := tmMoveWord_computesInTime kWork3 kWork1 kWork0 (by decide) (by decide) (by decide)
        (encodeNatBits (w + 1) r_dbl) tW3 [] []
        (mkTapes8 [] [] [] (encodeDelimWord remA.tail ++ tW2) []
          (encodeDelimWord qBits ++ tW4)
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
        List.append_nil, encodeNatBits_length] at b2
      have b3 := tmDupWord_computesInTime kWork5 kWork3 kWork1 (by decide) (by decide) (by decide)
        (encodeNatBits (w + 1) b) tW5 tW3 []
        (mkTapes8 [] (encodeDelimWord (encodeNatBits (w + 1) r_dbl)) []
          (encodeDelimWord remA.tail ++ tW2) []
          (encodeDelimWord qBits ++ tW4) [] tailSch)
      simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork3, update_mkTapes8_kWork1,
        List.append_nil, encodeNatBits_length] at b3
      have b4 := bmCondSubDirect_computesInTime (w + 1) r_dbl b hr_dbl_w1 hb_w1_lt
        [] [] [] (encodeDelimWord remA.tail ++ tW2) tW3
        (encodeDelimWord qBits ++ tW4)
        (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch
      simp only [List.append_nil] at b4
      have b5 := tmConcatRevWord_computesInTime kWork0 kWork4 (by decide)
        [qBit] qBits [] tW4
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 1) r)) [] []
          (encodeDelimWord remA.tail ++ tW2) tW3 []
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork4, List.reverse_singleton,
        List.singleton_append, List.length_singleton, List.append_nil] at b5
      have hr_w1_rev : (encodeNatBits (w + 1) r).reverse =
          false :: (encodeNatBits w r).reverse := by
        rw [encodeNatBits_succ_eq_append_false hr_w, List.reverse_append,
          List.reverse_singleton, List.singleton_append]
      have b6 := tmRevMoveWord_computesInTime kIO kWork1 (by decide)
        (encodeNatBits (w + 1) r) [] []
        (mkTapes8 [] [] [] (encodeDelimWord remA.tail ++ tW2) tW3
          (encodeDelimWord (qBit :: qBits) ++ tW4)
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
        encodeNatBits_length, hr_w1_rev] at b6
      have b7 := tmPushEmpty_computesInTime kIO
        (mkTapes8 [] [] (encodeDelimWord (false :: (encodeNatBits w r).reverse))
          (encodeDelimWord remA.tail ++ tW2) tW3
          (encodeDelimWord (qBit :: qBits) ++ tW4)
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at b7
      have b8 := tmPopBitOrZero_computesInTime kWork1 kIO (by decide)
        (false :: (encodeNatBits w r).reverse) [] [] []
        (mkTapes8 [] [] [] (encodeDelimWord remA.tail ++ tW2) tW3
          (encodeDelimWord (qBit :: qBits) ++ tW4)
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.append_nil,
        List.headD_cons, List.tail_cons] at b8
      have b9 := tmDropWord_computesInTime kIO [false] []
        (mkTapes8 [] [] (encodeDelimWord (encodeNatBits w r).reverse)
          (encodeDelimWord remA.tail ++ tW2) tW3
          (encodeDelimWord (qBit :: qBits) ++ tW4)
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kIO, List.append_nil, List.length_singleton] at b9
      have b10 := tmRevMoveWord_computesInTime kWork1 kWork3 (by decide)
        (encodeNatBits w r).reverse [] tW3
        (mkTapes8 [] [] [] (encodeDelimWord remA.tail ++ tW2) []
          (encodeDelimWord (qBit :: qBits) ++ tW4)
          (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tailSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork3, List.length_reverse,
        List.reverse_reverse, encodeNatBits_length, List.append_nil] at b10
      have hseq := b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (b6.seq (b7.seq (b8.seq (b9.seq b10))))))))
      exact hseq.mono (by omega))
    (encUnary w) tSch (⟨0, hb0⟩, aBits.reverse, [])
  dsimp only [stkOf] at hloop
  simp only [update_mkTapes8_kSched] at hloop
  have hspec := loopFinalState_restoringDivPureStep_spec w b hb0 w a ha []
  simp only [List.append_nil] at hspec
  change loopFinalState (restoringDivPureStep b hb0) (encUnary w)
      (⟨0, hb0⟩, aBits.reverse, []) =
    (⟨a % b, Nat.mod_lt a hb0⟩, [], encodeNatBits w (a / b)) at hspec
  rw [hspec, loopStepsAux_restoringDivPureStep_eq w b hb0 (encUnary w), length_encUnary] at hloop
  dsimp only at hloop
  have s15 := tmDropWord_computesInTime kWork2 [] tW2
    (mkTapes8 [] [] [] []
      (encodeDelimWord (encodeNatBits w (a % b)) ++ tW3)
      (encodeDelimWord (encodeNatBits w (a / b)) ++ tW4)
      (encodeDelimWord (encodeNatBits (w + 1) b) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork2, List.length_nil] at s15
  have s16 := tmDropWord_computesInTime kWork5 (encodeNatBits (w + 1) b) tW5
    (mkTapes8 [] [] [] tW2
      (encodeDelimWord (encodeNatBits w (a % b)) ++ tW3)
      (encodeDelimWord (encodeNatBits w (a / b)) ++ tW4) [] tSch)
  simp only [update_mkTapes8_kWork5, encodeNatBits_length] at s16
  have s17 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encodeNatBits w (a % b)) tW3 [] []
    (mkTapes8 [] [] [] tW2 [] (encodeDelimWord (encodeNatBits w (a / b)) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil, encodeNatBits_length] at s17
  have s18 := tmRevMoveWord_computesInTime kWork4 kWork0 (by decide)
    (encodeNatBits w (a / b)) tW4 []
    (mkTapes8 (encodeDelimWord (encodeNatBits w (a % b))) [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, List.append_nil,
    encodeNatBits_length] at s18
  have s19 := tmPackPairFromRev_computesInTime
    (encodeNatBits w (a / b)) (encodeNatBits w (a % b))
    tW2 tW3 tW4 tW5 tSch
  simp only [encodeNatBits_length] at s19
  simp only [aBits, bBits, encPair, encBits, id, length_encUnary, encodeNatBits_length,
    List.length_append, length_encodeDelimWord] at s1 s6 s8 s9 s10 s12 s13 ⊢
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
      (s11.seq (s12.seq (s13.seq (s14.seq (hloop.seq (s15.seq (s16.seq (s17.seq (s18.seq s19))))))))))))))))))⟩
  nlinarith

/-! ## 5. $O(w^2)$ Restoring Binary Square Root (`bmRestoringSqrt`, Stage 34) -/

theorem reverse_encodeNatBits_succ_eq (n x : ℕ) :
    (encodeNatBits (n + 1) x).reverse =
      decide ((x / 2 ^ n) % 2 = 1) :: (encodeNatBits n (x % 2 ^ n)).reverse := by
  have h1 : encodeNatBits 1 (x / 2 ^ n) = [decide ((x / 2 ^ n) % 2 = 1)] :=
    encodeNatBits_succ_mod_div 0 (x / 2 ^ n)
  rw [encodeNatBits_add_mod_div n 1 x, h1, List.reverse_append, List.reverse_singleton,
    List.singleton_append]

theorem reverse_encodeNatBits_add_two_eq (n x : ℕ) :
    (encodeNatBits (n + 2) x).reverse =
      decide ((x / 2 ^ (n + 1)) % 2 = 1) ::
        decide (((x % 2 ^ (n + 1)) / 2 ^ n) % 2 = 1) ::
          (encodeNatBits n (x % 2 ^ n)).reverse := by
  have h1 := reverse_encodeNatBits_succ_eq (n + 1) x
  have h2 := reverse_encodeNatBits_succ_eq n (x % 2 ^ (n + 1))
  have hmod : (x % 2 ^ (n + 1)) % 2 ^ n = x % 2 ^ n :=
    Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (Nat.le_succ n))
  rw [hmod] at h2
  rw [h1, h2]

theorem cons_encodeNatBits_eq (n x : ℕ) (b0 : Bool) :
    b0 :: encodeNatBits n x =
      encodeNatBits (n + 1) (2 * x + b0.toNat) := by
  have h1 := encodeNatBits_succ_mod_div n (2 * x + b0.toNat)
  have hm0 : decide ((2 * x + b0.toNat) % 2 = 1) = b0 := by
    cases b0 <;> simp [Bool.toNat]
  have hd0 : (2 * x + b0.toNat) / 2 = x := by
    (cases b0 <;> simp [Bool.toNat]); omega
  rw [h1, hm0, hd0]

theorem cons_cons_encodeNatBits_eq (n x : ℕ) (b0 b1 : Bool) :
    b0 :: b1 :: encodeNatBits n x =
      encodeNatBits (n + 2) (4 * x + 2 * b1.toNat + b0.toNat) := by
  rw [cons_encodeNatBits_eq n x b1, cons_encodeNatBits_eq (n + 1) (2 * x + b1.toNat) b0]
  have heq : 2 * (2 * x + b1.toNat) + b0.toNat = 4 * x + 2 * b1.toNat + b0.toNat := by ring
  rw [heq]

theorem four_pow_eq_two_pow_mul_two_pow :
    ∀ k : ℕ, 4 ^ k = 2 ^ k * 2 ^ k
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, four_pow_eq_two_pow_mul_two_pow k]
    ring

theorem binaryRestoringSqrtRegAux_lt (w : ℕ) {k m : ℕ} (hm : m < 4 ^ k) :
    (binaryRestoringSqrtRegAux w k m).1.1 < 2 ^ k ∧
      (binaryRestoringSqrtRegAux w k m).1.2 < 2 ^ (k + 1) := by
  rcases binaryRestoringSqrtRegAux_spec w hm with ⟨hsq, hrem⟩
  set s := (binaryRestoringSqrtRegAux w k m).1.1
  set r := (binaryRestoringSqrtRegAux w k m).1.2
  have h4 : 4 ^ k = 2 ^ k * 2 ^ k := four_pow_eq_two_pow_mul_two_pow k
  have hs : s < 2 ^ k := by
    by_contra hge
    have hle : 2 ^ k ≤ s := Nat.le_of_not_lt hge
    have hmul : 2 ^ k * 2 ^ k ≤ s * s := Nat.mul_le_mul hle hle
    omega
  have hr : r < 2 ^ (k + 1) := by
    rw [Nat.pow_succ]
    omega
  exact ⟨hs, hr⟩

/-- Pure state step for `bmRestoringSqrt` over `(w + 1)`-bit root/remainder registers. -/
def restoringSqrtPureStep (w : ℕ)
    (st : { x : ℕ // x < 2 ^ (w + 1) } × { x : ℕ // x < 2 ^ (w + 1) } × List Bool) :
    { x : ℕ // x < 2 ^ (w + 1) } × { x : ℕ // x < 2 ^ (w + 1) } × List Bool :=
  let s' := st.1.1
  let r' := st.2.1.1
  let remM := st.2.2
  let b_hi := remM.headD false
  let b_lo := remM.tail.headD false
  let r_quad := 4 * r' + 2 * b_hi.toNat + b_lo.toNat
  let cand := 4 * s' + 1
  let qBit := decide (cand ≤ r_quad)
  let s := 2 * s' + qBit.toNat
  let r := if cand ≤ r_quad then r_quad - cand else r_quad
  (⟨s % 2 ^ (w + 1), Nat.mod_lt _ (Nat.two_pow_pos (w + 1))⟩,
   ⟨r % 2 ^ (w + 1), Nat.mod_lt _ (Nat.two_pow_pos (w + 1))⟩,
   remM.tail.tail)

theorem loopFinalState_restoringSqrtPureStep_spec (w : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ w) (m : ℕ) (hm : m < 4 ^ k) (rest : List Bool),
      loopFinalState (restoringSqrtPureStep w) (encUnary k)
        (⟨0, Nat.two_pow_pos (w + 1)⟩, ⟨0, Nat.two_pow_pos (w + 1)⟩,
          (encodeNatBits (2 * k) m).reverse ++ rest) =
      (⟨(binaryRestoringSqrtRegAux w k m).1.1,
          lt_of_lt_of_le (binaryRestoringSqrtRegAux_lt w hm).1
            (Nat.pow_le_pow_right (by decide) (Nat.le_succ_of_le hk))⟩,
       ⟨(binaryRestoringSqrtRegAux w k m).1.2,
          lt_of_lt_of_le (binaryRestoringSqrtRegAux_lt w hm).2
            (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ hk))⟩,
       rest)
  | 0, _, m, hm, rest => by
    have hm0 : m = 0 := by omega
    subst hm0
    simp [encUnary, encodeNatBits, binaryRestoringSqrtRegAux]
  | k + 1, hk, m, hm, rest => by
    have hk_le : k ≤ w := Nat.le_of_succ_le hk
    have hm4 : m / 4 < 4 ^ k := by
      rw [Nat.pow_succ] at hm
      omega
    have hsplit_m : encodeNatBits (2 * (k + 1)) m =
        decide (m % 2 = 1) :: decide ((m / 2) % 2 = 1) :: encodeNatBits (2 * k) (m / 4) := by
      have h2k : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h2k, encodeNatBits_succ_mod_div (2 * k + 1) m,
        encodeNatBits_succ_mod_div (2 * k) (m / 2), Nat.div_div_eq_div_mul]
    have hrev_m : (encodeNatBits (2 * (k + 1)) m).reverse ++ rest =
        (encodeNatBits (2 * k) (m / 4)).reverse ++
          (decide ((m / 2) % 2 = 1) :: decide (m % 2 = 1) :: rest) := by
      rw [hsplit_m, List.reverse_cons, List.reverse_cons, List.append_assoc,
        List.append_assoc, List.singleton_append, List.singleton_append]
    rw [encUnary_succ_append k, hrev_m, loopFinalState_append,
      loopFinalState_restoringSqrtPureStep_spec w k hk_le (m / 4) hm4
        (decide ((m / 2) % 2 = 1) :: decide (m % 2 = 1) :: rest)]
    dsimp only [loopFinalState, restoringSqrtPureStep, List.headD_cons, List.tail_cons]
    have hb_hi : (decide ((m / 2) % 2 = 1)).toNat = (m / 2) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one (m / 2) with h | h <;> simp [h]
    have hb_lo : (decide (m % 2 = 1)).toNat = m % 2 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
    rcases binaryRestoringSqrtRegAux_lt w hm with ⟨hs_lt, hr_lt⟩
    have hs_w1 : (binaryRestoringSqrtRegAux w (k + 1) m).1.1 < 2 ^ (w + 1) :=
      lt_of_lt_of_le hs_lt (Nat.pow_le_pow_right (by decide) (Nat.le_succ_of_le hk))
    have hr_w1 : (binaryRestoringSqrtRegAux w (k + 1) m).1.2 < 2 ^ (w + 1) :=
      lt_of_lt_of_le hr_lt (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ hk))
    set s' := (binaryRestoringSqrtRegAux w k (m / 4)).1.1
    set r' := (binaryRestoringSqrtRegAux w k (m / 4)).1.2
    have hr_quad_eq : 4 * r' + 2 * (decide ((m / 2) % 2 = 1)).toNat + (decide (m % 2 = 1)).toNat =
        (r' + r') + (r' + r') + m % 4 := by
      rw [hb_hi, hb_lo]
      omega
    have hcand_eq : 4 * s' + 1 = (s' + s') + (s' + s') + 1 := by ring
    have hs_def : (binaryRestoringSqrtRegAux w (k + 1) m).1.1 =
        (if (s' + s') + (s' + s') + 1 ≤ (r' + r') + (r' + r') + m % 4
         then (s' + s') + 1 else s' + s') := rfl
    have hr_def : (binaryRestoringSqrtRegAux w (k + 1) m).1.2 =
        (if (s' + s') + (s' + s') + 1 ≤ (r' + r') + (r' + r') + m % 4
         then (r' + r') + (r' + r') + m % 4 - ((s' + s') + (s' + s') + 1)
         else (r' + r') + (r' + r') + m % 4) := rfl
    have hs_step_eq : 2 * s' + (decide (4 * s' + 1 ≤
          4 * r' + 2 * (decide ((m / 2) % 2 = 1)).toNat + (decide (m % 2 = 1)).toNat)).toNat =
        (binaryRestoringSqrtRegAux w (k + 1) m).1.1 := by
      rw [hs_def, hr_quad_eq, hcand_eq]
      by_cases hcmp : (s' + s') + (s' + s') + 1 ≤ (r' + r') + (r' + r') + m % 4
      · simp only [if_pos hcmp, decide_eq_true hcmp, Bool.toNat, cond_true]
        omega
      · simp only [if_neg hcmp, decide_eq_false hcmp, Bool.toNat, cond_false]
        omega
    have hr_step_eq : (if 4 * s' + 1 ≤
          4 * r' + 2 * (decide ((m / 2) % 2 = 1)).toNat + (decide (m % 2 = 1)).toNat
        then 4 * r' + 2 * (decide ((m / 2) % 2 = 1)).toNat + (decide (m % 2 = 1)).toNat - (4 * s' + 1)
        else 4 * r' + 2 * (decide ((m / 2) % 2 = 1)).toNat + (decide (m % 2 = 1)).toNat) =
        (binaryRestoringSqrtRegAux w (k + 1) m).1.2 := by
      rw [hr_def, hr_quad_eq, hcand_eq]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) rfl)
    · dsimp only
      rw [hs_step_eq, Nat.mod_eq_of_lt hs_w1]
    · dsimp only
      rw [hr_step_eq, Nat.mod_eq_of_lt hr_w1]

theorem loopStepsAux_restoringSqrtPureStep_eq (w : ℕ) :
    ∀ (u : List Bool)
      (st : { x : ℕ // x < 2 ^ (w + 1) } × { x : ℕ // x < 2 ^ (w + 1) } × List Bool),
      loopStepsAux (restoringSqrtPureStep w) (fun _ => 15 * w + 85) u st =
        u.length * (15 * w + 86) + 1
  | [], _ => by simp [loopStepsAux]
  | _ :: u, st => by
    simp only [loopStepsAux_cons, List.length_cons,
      loopStepsAux_restoringSqrtPureStep_eq w u]
    ring

/-- **Stage 34 (`bmRestoringSqrt`)**:
Consumes `(w, encodeNatBits (2 * w) m)` on `kIO` (`m < 4 ^ w`) and produces
`(encodeNatBits (w + 1) (binaryRestoringSqrtRegTracked w m).1.1, encodeNatBits (w + 1) (binaryRestoringSqrtRegTracked w m).1.2)`
on `kIO` in $O(w^2)$ `TM2.step` transitions. -/
def bmRestoringSqrt : BitMachine :=
  (tmPopFirstSubwordRev kIO kWork0).seq
    ((tmRevMoveWord kWork0 kWork1).seq
      ((tmDupWord kWork1 kWork0 kSched).seq
        ((tmConsBit false kWork1).seq
          ((tmPushEmpty kWork3).seq
            (((tmConsBit false kWork3).loopDelimWord kWork1).seq
              ((tmDupWord kWork3 kWork0 kWork4).seq
                ((tmPopFirstSubwordRev kIO kWork2).seq
                  ((tmDropWord kIO).seq
                    ((((tmPopBitOrZero kWork2 kWork3).seq
                        ((tmPopBitOrZero kWork2 kWork3).seq
                          ((tmMoveWord kWork3 kWork1 kWork0).seq
                            ((tmDupWord kWork4 kWork3 kWork1).seq
                              ((tmConsBit false kWork1).seq
                                ((tmConsBit true kWork1).seq
                                  (bmCondSubDirect.seq
                                    ((tmConcatRevWord kWork0 kWork4).seq
                                      ((tmRevMoveWord kWork4 kWork1).seq
                                        ((tmPushEmpty kWork0).seq
                                          ((tmPopBitOrZero kWork1 kWork0).seq
                                            ((tmDropWord kWork0).seq
                                              ((tmRevMoveWord kWork1 kWork4).seq
                                                ((tmRevMoveWord kIO kWork1).seq
                                                  ((tmPushEmpty kIO).seq
                                                    ((tmPopBitOrZero kWork1 kIO).seq
                                                      ((tmPopBitOrZero kWork1 kIO).seq
                                                        ((tmDropWord kIO).seq
                                                          (tmRevMoveWord kWork1 kWork3))))))))))))))))))).loopDelimWord kSched).seq
                      ((tmDropWord kWork2).seq
                        ((tmMoveWord kWork3 kWork0 kIO).seq
                          ((tmRevMoveWord kWork4 kWork0).seq
                            tmPackPairFromRev))))))))))))

theorem bmRestoringSqrt_computesInTime (w m : ℕ) (hm : m < 4 ^ w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 15 * w * w + 120 * w + 95,
      bmRestoringSqrt.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encBits
          (w, encodeNatBits (2 * w) m)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encPair encBits encBits
          (encodeNatBits (w + 1) (binaryRestoringSqrtRegTracked w m).1.1,
           encodeNatBits (w + 1) (binaryRestoringSqrtRegTracked w m).1.2)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  set mBits := encodeNatBits (2 * w) m
  have s1 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord (encUnary w) ++ encodeDelimWord mBits) [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord_append] at s1
  have s2 := tmRevMoveWord_computesInTime kWork0 kWork1 (by decide)
    (encUnary w).reverse [] []
    (mkTapes8 (encodeDelimWord (encodeDelimWord mBits))
      [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork1, List.length_reverse,
    List.reverse_reverse, List.append_nil, length_encUnary] at s2
  have s3 := tmDupWord_computesInTime kWork1 kWork0 kSched (by decide) (by decide) (by decide)
    (encUnary w) [] [] tSch
    (mkTapes8 (encodeDelimWord (encodeDelimWord mBits))
      [] [] tW2 tW3 tW4 tW5 [])
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, update_mkTapes8_kSched,
    List.append_nil, length_encUnary] at s3
  have s4 := tmConsBit_computesInTime false kWork1
    (mkTapes8 (encodeDelimWord (encodeDelimWord mBits))
      [] (encodeDelimWord (encUnary w)) tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
    (encUnary w) [] (by simp)
  simp only [update_mkTapes8_kWork1, List.append_nil] at s4
  have hcons_w1 : false :: encUnary w = encUnary (w + 1) := List.replicate_succ.symm
  rw [hcons_w1] at s4
  have s5 := tmPushEmpty_computesInTime kWork3
    (mkTapes8 (encodeDelimWord (encodeDelimWord mBits))
      [] (encodeDelimWord (encUnary (w + 1))) tW2 tW3 tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork3, mkTapes8_kWork3] at s5
  have s6 := consBit_loopDelimWord_computesInTime false kWork1 kWork3 (by decide)
    (encUnary (w + 1)) [] [] tW3
    (mkTapes8 (encodeDelimWord (encodeDelimWord mBits))
      [] [] tW2 [] tW4 tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork3, List.append_nil,
    length_encUnary] at s6
  have hzero_w1 : List.replicate (w + 1) false = encodeNatBits (w + 1) 0 :=
    (encodeNatBits_zero (w + 1)).symm
  rw [hzero_w1] at s6
  have s7 := tmDupWord_computesInTime kWork3 kWork0 kWork4 (by decide) (by decide) (by decide)
    (encodeNatBits (w + 1) 0) tW3 [] tW4
    (mkTapes8 (encodeDelimWord (encodeDelimWord mBits))
      [] [] tW2 [] [] tW5 (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kWork4,
    encodeNatBits_length] at s7
  have s12 := tmPopFirstSubwordRev_computesInTime kIO kWork2 (by decide)
    (encodeDelimWord mBits) [] tW2
    (mkTapes8 [] [] [] [] (encodeDelimWord (encodeNatBits (w + 1) 0) ++ tW3)
      (encodeDelimWord (encodeNatBits (w + 1) 0) ++ tW4) tW5
      (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork2, List.append_nil,
    unconsDelimWord_encodeDelimWord] at s12
  have s13 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] [] [] (encodeDelimWord mBits.reverse ++ tW2)
      (encodeDelimWord (encodeNatBits (w + 1) 0) ++ tW3)
      (encodeDelimWord (encodeNatBits (w + 1) 0) ++ tW4) tW5
      (encodeDelimWord (encUnary w) ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s13
  let stkOf : { x : ℕ // x < 2 ^ (w + 1) } × { x : ℕ // x < 2 ^ (w + 1) } × List Bool →
      (∀ k : TapeIdx, List (BitTapeAlphabet k)) := fun st =>
    mkTapes8 [] [] [] (encodeDelimWord st.2.2 ++ tW2)
      (encodeDelimWord (encodeNatBits (w + 1) st.2.1.1) ++ tW3)
      (encodeDelimWord (encodeNatBits (w + 1) st.1.1) ++ tW4)
      tW5 []
  have hloop := BitMachine.ComputesInTime.loopDelimWord_state kSched
    (restoringSqrtPureStep w) (fun _ => 15 * w + 85) stkOf
    (fun st tailSch => by
      rcases st with ⟨s', r', remM⟩
      dsimp only [stkOf, restoringSqrtPureStep]
      simp only [update_mkTapes8_kSched]
      set b_hi := remM.headD false
      set b_lo := remM.tail.headD false
      set r_quad := 4 * r'.1 + 2 * b_hi.toNat + b_lo.toNat
      set cand := 4 * s'.1 + 1
      set qBit := decide (cand ≤ r_quad)
      set s := 2 * s'.1 + qBit.toNat
      set r := if cand ≤ r_quad then r_quad - cand else r_quad
      have hr_quad_lt : r_quad < 2 ^ (w + 3) := by
        have hr' := r'.2
        have hhi : b_hi.toNat ≤ 1 := Bool.toNat_le b_hi
        have hlo : b_lo.toNat ≤ 1 := Bool.toNat_le b_lo
        have hpow : 2 ^ (w + 3) = 4 * 2 ^ (w + 1) := by
          rw [show w + 3 = (w + 1) + 2 by ring, Nat.pow_add]
          ring
        omega
      have hcand_lt : cand < 2 ^ (w + 3) := by
        have hs' := s'.2
        have hpow : 2 ^ (w + 3) = 4 * 2 ^ (w + 1) := by
          rw [show w + 3 = (w + 1) + 2 by ring, Nat.pow_add]
          ring
        omega
      have b1 := tmPopBitOrZero_computesInTime kWork2 kWork3 (by decide)
        remM (encodeNatBits (w + 1) r'.1) tW2 tW3
        (mkTapes8 [] [] [] [] []
          (encodeDelimWord (encodeNatBits (w + 1) s'.1) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork3] at b1
      have b2 := tmPopBitOrZero_computesInTime kWork2 kWork3 (by decide)
        remM.tail (b_hi :: encodeNatBits (w + 1) r'.1) tW2 tW3
        (mkTapes8 [] [] [] [] []
          (encodeDelimWord (encodeNatBits (w + 1) s'.1) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork3] at b2
      have hr_quad_bits : b_lo :: b_hi :: encodeNatBits (w + 1) r'.1 =
          encodeNatBits (w + 3) r_quad := cons_cons_encodeNatBits_eq (w + 1) r'.1 b_lo b_hi
      rw [hr_quad_bits] at b2
      have b3 := tmMoveWord_computesInTime kWork3 kWork1 kWork0 (by decide) (by decide) (by decide)
        (encodeNatBits (w + 3) r_quad) tW3 [] []
        (mkTapes8 [] [] [] (encodeDelimWord remM.tail.tail ++ tW2) []
          (encodeDelimWord (encodeNatBits (w + 1) s'.1) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork1, update_mkTapes8_kWork0,
        List.append_nil, encodeNatBits_length] at b3
      have b4 := tmDupWord_computesInTime kWork4 kWork3 kWork1 (by decide) (by decide) (by decide)
        (encodeNatBits (w + 1) s'.1) tW4 tW3 []
        (mkTapes8 [] (encodeDelimWord (encodeNatBits (w + 3) r_quad)) []
          (encodeDelimWord remM.tail.tail ++ tW2) [] [] tW5 tailSch)
      simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork3, update_mkTapes8_kWork1,
        List.append_nil, encodeNatBits_length] at b4
      have b5 := tmConsBit_computesInTime false kWork1
        (mkTapes8 [] (encodeDelimWord (encodeNatBits (w + 3) r_quad))
          (encodeDelimWord (encodeNatBits (w + 1) s'.1))
          (encodeDelimWord remM.tail.tail ++ tW2) tW3
          (encodeDelimWord (encodeNatBits (w + 1) s'.1) ++ tW4) tW5 tailSch)
        (encodeNatBits (w + 1) s'.1) [] (by simp)
      simp only [update_mkTapes8_kWork1, List.append_nil] at b5
      have b6 := tmConsBit_computesInTime true kWork1
        (mkTapes8 [] (encodeDelimWord (encodeNatBits (w + 3) r_quad))
          (encodeDelimWord (false :: encodeNatBits (w + 1) s'.1))
          (encodeDelimWord remM.tail.tail ++ tW2) tW3
          (encodeDelimWord (encodeNatBits (w + 1) s'.1) ++ tW4) tW5 tailSch)
        (false :: encodeNatBits (w + 1) s'.1) [] (by simp)
      simp only [update_mkTapes8_kWork1, List.append_nil] at b6
      have hcand_bits : true :: false :: encodeNatBits (w + 1) s'.1 =
          encodeNatBits (w + 3) cand := by
        rw [cons_cons_encodeNatBits_eq (w + 1) s'.1 true false]
        rfl
      rw [hcand_bits] at b6
      have b7 := bmCondSubDirect_computesInTime (w + 3) r_quad cand hr_quad_lt hcand_lt
        [] [] [] (encodeDelimWord remM.tail.tail ++ tW2) tW3
        (encodeDelimWord (encodeNatBits (w + 1) s'.1) ++ tW4) tW5 tailSch
      simp only [List.append_nil] at b7
      have b8 := tmConcatRevWord_computesInTime kWork0 kWork4 (by decide)
        [qBit] (encodeNatBits (w + 1) s'.1) [] tW4
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 3) r)) [] []
          (encodeDelimWord remM.tail.tail ++ tW2) tW3 [] tW5 tailSch)
      simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork4, List.reverse_singleton,
        List.singleton_append, List.length_singleton, List.append_nil] at b8
      have hs_bits : qBit :: encodeNatBits (w + 1) s'.1 = encodeNatBits (w + 2) s :=
        cons_encodeNatBits_eq (w + 1) s'.1 qBit
      rw [hs_bits] at b8
      have b9 := tmRevMoveWord_computesInTime kWork4 kWork1 (by decide)
        (encodeNatBits (w + 2) s) tW4 []
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 3) r)) [] []
          (encodeDelimWord remM.tail.tail ++ tW2) tW3 [] tW5 tailSch)
      simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork1, List.append_nil,
        encodeNatBits_length, reverse_encodeNatBits_succ_eq (w + 1) s] at b9
      set msb_s := decide ((s / 2 ^ (w + 1)) % 2 = 1)
      have b10 := tmPushEmpty_computesInTime kWork0
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 3) r)) []
          (encodeDelimWord (msb_s :: (encodeNatBits (w + 1) (s % 2 ^ (w + 1))).reverse))
          (encodeDelimWord remM.tail.tail ++ tW2) tW3 tW4 tW5 tailSch)
      simp only [update_mkTapes8_kWork0, mkTapes8_kWork0, List.append_nil] at b10
      have b11 := tmPopBitOrZero_computesInTime kWork1 kWork0 (by decide)
        (msb_s :: (encodeNatBits (w + 1) (s % 2 ^ (w + 1))).reverse) [] [] []
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 3) r)) [] []
          (encodeDelimWord remM.tail.tail ++ tW2) tW3 tW4 tW5 tailSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork0, List.append_nil,
        List.headD_cons, List.tail_cons] at b11
      have b12 := tmDropWord_computesInTime kWork0 [msb_s] []
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 3) r)) []
          (encodeDelimWord (encodeNatBits (w + 1) (s % 2 ^ (w + 1))).reverse)
          (encodeDelimWord remM.tail.tail ++ tW2) tW3 tW4 tW5 tailSch)
      simp only [update_mkTapes8_kWork0, List.append_nil, List.length_singleton] at b12
      have b13 := tmRevMoveWord_computesInTime kWork1 kWork4 (by decide)
        (encodeNatBits (w + 1) (s % 2 ^ (w + 1))).reverse [] tW4
        (mkTapes8 (encodeDelimWord (encodeNatBits (w + 3) r)) [] []
          (encodeDelimWord remM.tail.tail ++ tW2) tW3 [] tW5 tailSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork4, List.length_reverse,
        List.reverse_reverse, encodeNatBits_length, List.append_nil] at b13
      have b14 := tmRevMoveWord_computesInTime kIO kWork1 (by decide)
        (encodeNatBits (w + 3) r) [] []
        (mkTapes8 [] [] [] (encodeDelimWord remM.tail.tail ++ tW2) tW3
          (encodeDelimWord (encodeNatBits (w + 1) (s % 2 ^ (w + 1))) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kIO, update_mkTapes8_kWork1, List.append_nil,
        encodeNatBits_length, reverse_encodeNatBits_add_two_eq (w + 1) r] at b14
      set msb2_r := decide ((r / 2 ^ (w + 1 + 1)) % 2 = 1)
      set msb1_r := decide (((r % 2 ^ (w + 1 + 1)) / 2 ^ (w + 1)) % 2 = 1)
      have b15 := tmPushEmpty_computesInTime kIO
        (mkTapes8 [] []
          (encodeDelimWord (msb2_r :: msb1_r :: (encodeNatBits (w + 1) (r % 2 ^ (w + 1))).reverse))
          (encodeDelimWord remM.tail.tail ++ tW2) tW3
          (encodeDelimWord (encodeNatBits (w + 1) (s % 2 ^ (w + 1))) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at b15
      have b16 := tmPopBitOrZero_computesInTime kWork1 kIO (by decide)
        (msb2_r :: msb1_r :: (encodeNatBits (w + 1) (r % 2 ^ (w + 1))).reverse) [] [] []
        (mkTapes8 [] [] [] (encodeDelimWord remM.tail.tail ++ tW2) tW3
          (encodeDelimWord (encodeNatBits (w + 1) (s % 2 ^ (w + 1))) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO,
        List.append_nil, List.headD_cons, List.tail_cons] at b16
      have b17 := tmPopBitOrZero_computesInTime kWork1 kIO (by decide)
        (msb1_r :: (encodeNatBits (w + 1) (r % 2 ^ (w + 1))).reverse) [msb2_r] [] []
        (mkTapes8 [] [] [] (encodeDelimWord remM.tail.tail ++ tW2) tW3
          (encodeDelimWord (encodeNatBits (w + 1) (s % 2 ^ (w + 1))) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kIO, List.append_nil,
        List.headD_cons, List.tail_cons] at b17
      have b18 := tmDropWord_computesInTime kIO [msb1_r, msb2_r] []
        (mkTapes8 [] [] (encodeDelimWord (encodeNatBits (w + 1) (r % 2 ^ (w + 1))).reverse)
          (encodeDelimWord remM.tail.tail ++ tW2) tW3
          (encodeDelimWord (encodeNatBits (w + 1) (s % 2 ^ (w + 1))) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kIO, List.append_nil, List.length_cons, List.length_nil] at b18
      have b19 := tmRevMoveWord_computesInTime kWork1 kWork3 (by decide)
        (encodeNatBits (w + 1) (r % 2 ^ (w + 1))).reverse [] tW3
        (mkTapes8 [] [] [] (encodeDelimWord remM.tail.tail ++ tW2) []
          (encodeDelimWord (encodeNatBits (w + 1) (s % 2 ^ (w + 1))) ++ tW4) tW5 tailSch)
      simp only [update_mkTapes8_kWork1, update_mkTapes8_kWork3, List.length_reverse,
        List.reverse_reverse, encodeNatBits_length, List.append_nil] at b19
      have hseq := b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (b6.seq (b7.seq (b8.seq (b9.seq (b10.seq
        (b11.seq (b12.seq (b13.seq (b14.seq (b15.seq (b16.seq (b17.seq (b18.seq b19)))))))))))))))))
      exact hseq.mono (by omega))
    (encUnary w) tSch
    (⟨0, Nat.two_pow_pos (w + 1)⟩, ⟨0, Nat.two_pow_pos (w + 1)⟩, mBits.reverse)
  dsimp only [stkOf] at hloop
  simp only [update_mkTapes8_kSched] at hloop
  have hspec := loopFinalState_restoringSqrtPureStep_spec w w (le_refl w) m hm []
  simp only [List.append_nil] at hspec
  change loopFinalState (restoringSqrtPureStep w) (encUnary w)
      (⟨0, Nat.two_pow_pos (w + 1)⟩, ⟨0, Nat.two_pow_pos (w + 1)⟩, mBits.reverse) =
    (⟨(binaryRestoringSqrtRegTracked w m).1.1,
        lt_of_lt_of_le (binaryRestoringSqrtRegAux_lt w hm).1
          (Nat.pow_le_pow_right (by decide) (Nat.le_succ w))⟩,
     ⟨(binaryRestoringSqrtRegTracked w m).1.2,
        (binaryRestoringSqrtRegAux_lt w hm).2⟩,
     []) at hspec
  rw [hspec, loopStepsAux_restoringSqrtPureStep_eq w (encUnary w), length_encUnary] at hloop
  dsimp only at hloop
  set sF := (binaryRestoringSqrtRegTracked w m).1.1
  set rF := (binaryRestoringSqrtRegTracked w m).1.2
  have s14 := tmDropWord_computesInTime kWork2 [] tW2
    (mkTapes8 [] [] [] []
      (encodeDelimWord (encodeNatBits (w + 1) rF) ++ tW3)
      (encodeDelimWord (encodeNatBits (w + 1) sF) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork2, List.length_nil] at s14
  have s15 := tmMoveWord_computesInTime kWork3 kWork0 kIO (by decide) (by decide) (by decide)
    (encodeNatBits (w + 1) rF) tW3 [] []
    (mkTapes8 [] [] [] tW2 [] (encodeDelimWord (encodeNatBits (w + 1) sF) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork3, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil, encodeNatBits_length] at s15
  have s16 := tmRevMoveWord_computesInTime kWork4 kWork0 (by decide)
    (encodeNatBits (w + 1) sF) tW4 []
    (mkTapes8 (encodeDelimWord (encodeNatBits (w + 1) rF)) [] [] tW2 tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, List.append_nil,
    encodeNatBits_length] at s16
  have s17 := tmPackPairFromRev_computesInTime
    (encodeNatBits (w + 1) sF) (encodeNatBits (w + 1) rF)
    tW2 tW3 tW4 tW5 tSch
  simp only [encodeNatBits_length] at s17
  simp only [mBits, encPair, encBits, id, length_encUnary, encodeNatBits_length,
    length_encodeDelimWord] at s1 s12 ⊢
  refine ⟨_, ?_,
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq
      (s12.seq (s13.seq (hloop.seq (s14.seq (s15.seq (s16.seq s17))))))))))))⟩
  nlinarith

#print axioms bmPackSignedSlotsBits_computesInTime
#print axioms bmUnpackSignedSlotsBits_computesInTime
#print axioms bmShiftAddMulBits_computesInTime
#print axioms bmRestoringDivMod_computesInTime
#print axioms bmRestoringSqrt_computesInTime

end IntMul
