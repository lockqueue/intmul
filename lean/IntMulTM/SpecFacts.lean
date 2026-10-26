import IntMulTM.Spec
import Mathlib.Data.Num.Lemmas
import Mathlib.Data.Nat.Size

/-!
# Facts about the specification's encodings (W0)

Equivalence between operand bit-width and pair encoding length: for the input `(a, b)`, put
`L = |encNatPair (a, b)|` and `n = max 1 (max |bits a| |bits b|)`. Then `a, b < 2 ^ n` and
`n ≤ L ≤ 2 n + 1`, so a bound `C · n · log n` in the operand length and a bound `C' · L · log L` in the
input length are equivalent up to constants, also for unbalanced operands.
-/

namespace IntMulTM

open Computability

theorem length_encodePosNum (p : PosNum) : (encodePosNum p).length = p.natSize := by
  induction p with
  | one => rfl
  | bit1 p ih => simp [encodePosNum, PosNum.natSize, ih]
  | bit0 p ih => simp [encodePosNum, PosNum.natSize, ih]

theorem length_encodeNum (n : Num) : (encodeNum n).length = n.natSize := by
  cases n with
  | zero => rfl
  | pos p => exact length_encodePosNum p

/-- The binary code of `n` has exactly `Nat.size n` bits. -/
theorem length_encodeNat (n : ℕ) : (encodeNat n).length = Nat.size n := by
  simp only [encodeNat]
  rw [length_encodeNum, Num.natSize_to_nat, Num.to_of_nat]

theorem lt_two_pow_length_encodeNat (n : ℕ) : n < 2 ^ (encodeNat n).length := by
  rw [length_encodeNat]
  exact Nat.lt_size_self n

/-- The operand bit length the machine works with. -/
def operandBits (a b : ℕ) : ℕ := max 1 (max (encodeNat a).length (encodeNat b).length)

/-- **Input bridge.** Both operands fit in `operandBits a b` bits, and the input length `L` satisfies
`n ≤ L ≤ 2 n + 1` for `n = operandBits a b`. -/
theorem input_bridge (a b : ℕ) :
    a < 2 ^ operandBits a b ∧ b < 2 ^ operandBits a b ∧
      operandBits a b ≤ (encNatPair.encode (a, b)).length ∧
      (encNatPair.encode (a, b)).length ≤ 2 * operandBits a b + 1 := by
  rw [encNatPair_encode_length]
  have ha : (encodeNat a).length ≤ operandBits a b :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hb : (encodeNat b).length ≤ operandBits a b :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨?_, ?_, ?_, by omega⟩
  · exact lt_of_lt_of_le (lt_two_pow_length_encodeNat a) (Nat.pow_le_pow_right (by decide) ha)
  · exact lt_of_lt_of_le (lt_two_pow_length_encodeNat b) (Nat.pow_le_pow_right (by decide) hb)
  · exact max_le (by omega) (max_le (by omega) (by omega))

/-- The output code is Mathlib's `encodeNat`: LSB-first, normalized, with `0 ↦ []`. -/
theorem finEncodingNatBool_encode (m : ℕ) :
    @Eq (List Bool) (finEncodingNatBool.encode m) (encodeNat m) := rfl

theorem encodeNat_zero : encodeNat 0 = [] :=
  List.eq_nil_of_length_eq_zero (by rw [length_encodeNat, Nat.size_zero])

end IntMulTM
