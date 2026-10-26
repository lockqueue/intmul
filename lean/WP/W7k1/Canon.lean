import IntMul.MaterializedAndComputable.ComputableTranscendentals
import Contracts.Machine.W6a
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W7k1.Canon — canonical straight-line forms of the snapshot's `π` and `ln 2` evaluators

W7 reproduces the snapshot's table integers bit-exactly. This module restates the two constant
evaluators of `ComputableTranscendentals.lean` (CTr) as explicit loops over `+`, `−`, `×`,
`divRoundRatInt` (W6a's restatement), shifts and `Nat.sqrt`, and proves them **equal** to the
snapshot's functions.

Two levels per evaluator:
* **Ref** (`piRef`, `log2Ref`): verbatim, operation by operation (the snapshot's `BitCostM`
  bookkeeping removed). Equalities `piRef_eq`, `log2Ref_eq`.
* **Nat** (`piNat`, `log2Nat`): all-natural machine forms. Every operand is non-negative, the
  final rounding divisions become shifts:
  * `π`: `S = 4B+20`, `A₀ = 0`, `A_{k+1} = ⌊√((A_k + 2^(S+1))·2^S)⌋` (`B+4` steps),
    `d = ⌊√((2^(S+1) − A)·2^S)⌋`, result `(d / 2^(2B+14) + 1) / 2`;
  * `ln 2`: `a₀ = 2^(3B+11)`, `a_{k+1} = (a_k·(k+1) + (k+2)) / (2(k+2))`, `s_{k+1} = s_k + a_k`
    (`B+2` steps), result `(s / 2^(2B+11) + 1) / 2`.
  Equalities `piNat_eq`, `log2Nat_eq` (as integers). `piIter_le` bounds the Archimedes iterates
  (`A_k ≤ 2^(S+1)`, so the machine's subtraction is in range).

Snapshot references: `sqrtTwoAddIntIter` (CTr:894), `computablePiScaledCore` (CTr:957),
`computablePiScaledWithCost` (CTr:968), `recurrenceStepCosted` (CTr:112),
`runRecurrenceSeriesCosted` (CTr:126), `computableLog2ScaledWithCost` (CTr:1221).
-/

namespace WP.W7k1

open TMFw.Contracts

/-! ## Rounding division -/

/-- W6a's restatement of `divRoundRatInt` is the snapshot's function. -/
theorem divRoundRatInt_eq_snap (num den : ℤ) :
    TMFw.Contracts.divRoundRatInt num den = IntMul.divRoundRatInt num den := rfl

/-- On naturals, `divRoundRatInt` is the natural division `(2x + y) / (2y)`. -/
theorem divRoundRatInt_natCast (x y : ℕ) (hy : 0 < y) :
    TMFw.Contracts.divRoundRatInt (x : ℤ) (y : ℤ) = (((2 * x + y) / (2 * y) : ℕ) : ℤ) := by
  unfold TMFw.Contracts.divRoundRatInt
  rw [if_pos (by exact_mod_cast hy)]
  simp only [Int.natCast_ediv, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- Rounding division by a power of two, as shifts: `round(x·2^m / 2^(m+j+1)) = (x/2^j + 1)/2`. -/
theorem divRoundRatInt_shift (x m j : ℕ) :
    TMFw.Contracts.divRoundRatInt ((x * 2 ^ m : ℕ) : ℤ) ((2 ^ (m + j + 1) : ℕ) : ℤ) =
      (((x / 2 ^ j + 1) / 2 : ℕ) : ℤ) := by
  rw [divRoundRatInt_natCast _ _ (by positivity)]
  congr 1
  have h1 : 2 * (x * 2 ^ m) + 2 ^ (m + j + 1) = 2 ^ (m + 1) * (x + 2 ^ j) := by ring
  have h2 : 2 * 2 ^ (m + j + 1) = 2 ^ (m + 1) * (2 ^ j * 2) := by ring
  rw [h1, h2, Nat.mul_div_mul_left _ _ (by positivity), ← Nat.div_div_eq_div_mul,
    Nat.add_div_right _ (by positivity)]

/-! ## `π`: the Archimedes iteration -/

/-- One Archimedes step at scale `2^S` (CTr:898). -/
def piStep (S A : ℕ) : ℕ := Nat.sqrt (2 * 2 ^ (2 * S) + A * 2 ^ S)

/-- `A_k` of the Archimedes iteration (CTr:894): `A₀ = 0`, `A_{k+1} = piStep S A_k`. -/
def piIter (S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => piStep S (piIter S k)

theorem piIter_eq (S k : ℕ) : (IntMul.sqrtTwoAddIntIter S k).1 = piIter S k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show Nat.sqrt (2 * 2 ^ (2 * S) + (IntMul.sqrtTwoAddIntIter S k).1 * 2 ^ S) = _
    rw [ih]
    rfl

/-- **Ref form of `π`** (CTr:957-971), operation by operation. -/
def piRef (B : ℕ) : ℤ :=
  divRoundRatInt
    (((2 ^ (B + 4 + 1) *
        Nat.sqrt (2 * 2 ^ (2 * (2 * (B + 4 + B + 6))) -
          piIter (2 * (B + 4 + B + 6)) (B + 4) * 2 ^ (2 * (B + 4 + B + 6))) : ℕ) : ℤ) *
      ((2 ^ B : ℕ) : ℤ))
    ((2 ^ (2 * (B + 4 + B + 6)) : ℕ) : ℤ)

theorem piRef_eq (B : ℕ) : (IntMul.computablePiScaledWithCost B).1 = piRef B := by
  unfold IntMul.computablePiScaledWithCost IntMul.computablePiScaledCore piRef
  simp only [IntMul.costedNatSqrt, IntMul.costedDivRoundRatInt, piIter_eq,
    divRoundRatInt_eq_snap]

/-- Machine form of the Archimedes step. -/
theorem piStep_eq (S A : ℕ) : piStep S A = Nat.sqrt ((A + 2 ^ (S + 1)) * 2 ^ S) := by
  unfold piStep
  congr 1
  ring

/-- The Archimedes iterates stay below `2^(S+1)` (so `2^(S+1) − A` is exact). -/
theorem piIter_le (S k : ℕ) : piIter S k ≤ 2 ^ (S + 1) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [piIter, piStep_eq]
    have hle : (piIter S k + 2 ^ (S + 1)) * 2 ^ S ≤ 2 ^ (S + 1) * 2 ^ (S + 1) := by
      calc (piIter S k + 2 ^ (S + 1)) * 2 ^ S ≤ (2 ^ (S + 1) + 2 ^ (S + 1)) * 2 ^ S :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ (S + 1) * 2 ^ (S + 1) := by ring
    calc Nat.sqrt ((piIter S k + 2 ^ (S + 1)) * 2 ^ S)
        ≤ Nat.sqrt (2 ^ (S + 1) * 2 ^ (S + 1)) := Nat.sqrt_le_sqrt hle
      _ = 2 ^ (S + 1) := Nat.sqrt_eq _

/-- The final square root of the `π` evaluator, in machine form. -/
def piD (B : ℕ) : ℕ :=
  Nat.sqrt ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) * 2 ^ (4 * B + 20))

/-- **Nat form of `π`**: `(d / 2^(2B+14) + 1) / 2`. -/
def piNat (B : ℕ) : ℕ := (piD B / 2 ^ (2 * B + 14) + 1) / 2

theorem piNat_eq (B : ℕ) : (IntMul.computablePiScaledWithCost B).1 = (piNat B : ℤ) := by
  rw [piRef_eq]
  unfold piRef piNat
  rw [show 2 * (B + 4 + B + 6) = 4 * B + 20 by ring,
    show 2 * 2 ^ (2 * (4 * B + 20)) = 2 ^ (4 * B + 20 + 1) * 2 ^ (4 * B + 20) by ring,
    ← Nat.sub_mul]
  change divRoundRatInt (((2 ^ (B + 4 + 1) * piD B : ℕ) : ℤ) * ((2 ^ B : ℕ) : ℤ))
    ((2 ^ (4 * B + 20) : ℕ) : ℤ) = _
  rw [← Nat.cast_mul, show 2 ^ (B + 4 + 1) * piD B * 2 ^ B = piD B * 2 ^ (2 * B + 5) by ring,
    show 4 * B + 20 = (2 * B + 5) + (2 * B + 14) + 1 by ring, divRoundRatInt_shift]

/-! ## `ln 2`: the fixed-point series -/

/-- One step of the snapshot's `ln 2` recurrence: `recurrenceStepCosted` (CTr:112) with
`stepNum = 1`, `baseDen = 2`, `stepNumFactor k = k + 1`, `stepDenFactor k = k + 2`. -/
def lnStep (k : ℕ) (st : ℤ × ℤ) : ℤ × ℤ :=
  (divRoundRatInt (st.1 * 1 * ((k + 1 : ℕ) : ℤ)) (((k + 2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ)),
    st.2 + st.1)

/-- The state `(a_k, s_k)` after `k` steps (CTr:126). -/
def lnIter (a0 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (a0, 0)
  | k + 1 => lnStep k (lnIter a0 k)

theorem lnIter_eq (w : ℕ) (a0 : ℤ) (k : ℕ) :
    (IntMul.runRecurrenceSeriesCosted w a0 1 2 (fun k => k + 1) (fun k => k + 2) k).1 =
      lnIter a0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (IntMul.recurrenceStepCosted w 1 2 (fun k => k + 1) (fun k => k + 2) k
      (IntMul.runRecurrenceSeriesCosted w a0 1 2 (fun k => k + 1) (fun k => k + 2) k).1).1 = _
    rw [ih]
    rfl

/-- **Ref form of `ln 2`** (CTr:1221-1230), operation by operation. -/
def log2Ref (B : ℕ) : ℤ :=
  divRoundRatInt
    ((lnIter (divRoundRatInt ((2 ^ (B + 2 * (B + 2) + 8) : ℕ) : ℤ) 2) (B + 2)).2 *
      ((2 ^ B : ℕ) : ℤ))
    ((2 ^ (B + 2 * (B + 2) + 8) : ℕ) : ℤ)

theorem log2Ref_eq (B : ℕ) : (IntMul.computableLog2ScaledWithCost B).1 = log2Ref B := by
  unfold IntMul.computableLog2ScaledWithCost log2Ref
  simp only [IntMul.costedDivRoundRatInt, lnIter_eq, divRoundRatInt_eq_snap]

/-- The natural-number `ln 2` state `(a_k, s_k)`. -/
def lnNatIter (B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (2 ^ (3 * B + 11), 0)
  | k + 1 =>
    (((lnNatIter B k).1 * (k + 1) + (k + 2)) / (2 * (k + 2)),
      (lnNatIter B k).2 + (lnNatIter B k).1)

/-- **Nat form of `ln 2`**: `(s / 2^(2B+11) + 1) / 2`. -/
def log2Nat (B : ℕ) : ℕ := ((lnNatIter B (B + 2)).2 / 2 ^ (2 * B + 11) + 1) / 2

theorem lnA0 (B : ℕ) :
    divRoundRatInt ((2 ^ (B + 2 * (B + 2) + 8) : ℕ) : ℤ) 2 = ((2 ^ (3 * B + 11) : ℕ) : ℤ) := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, divRoundRatInt_natCast _ _ (by norm_num)]
  congr 1
  rw [show B + 2 * (B + 2) + 8 = 3 * B + 11 + 1 by ring, pow_succ]
  generalize 2 ^ (3 * B + 11) = x
  omega

theorem lnStep_natCast (k a s : ℕ) :
    lnStep k ((a : ℤ), (s : ℤ)) =
      ((((a * (k + 1) + (k + 2)) / (2 * (k + 2)) : ℕ) : ℤ), ((s + a : ℕ) : ℤ)) := by
  unfold lnStep
  have hnum : (a : ℤ) * 1 * ((k + 1 : ℕ) : ℤ) = ((a * (k + 1) : ℕ) : ℤ) := by push_cast; ring
  have hden : ((k + 2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) = (((k + 2) * 2 : ℕ) : ℤ) := by push_cast; ring
  rw [hnum, hden, divRoundRatInt_natCast _ _ (by positivity)]
  have e1 : 2 * (a * (k + 1)) + (k + 2) * 2 = 2 * (a * (k + 1) + (k + 2)) := by ring
  have e2 : 2 * ((k + 2) * 2) = 2 * (2 * (k + 2)) := by ring
  rw [e1, e2, Nat.mul_div_mul_left _ _ (by norm_num)]
  push_cast
  rfl

theorem lnIter_natCast (B k : ℕ) :
    lnIter ((2 ^ (3 * B + 11) : ℕ) : ℤ) k =
      (((lnNatIter B k).1 : ℤ), ((lnNatIter B k).2 : ℤ)) := by
  induction k with
  | zero => simp [lnIter, lnNatIter]
  | succ k ih =>
    rw [lnIter, ih, lnStep_natCast, lnNatIter]

theorem log2Nat_eq (B : ℕ) : (IntMul.computableLog2ScaledWithCost B).1 = (log2Nat B : ℤ) := by
  rw [log2Ref_eq]
  unfold log2Ref
  rw [lnA0, lnIter_natCast]
  dsimp only
  rw [← Nat.cast_mul, show B + 2 * (B + 2) + 8 = B + (2 * B + 11) + 1 by ring,
    divRoundRatInt_shift]
  rfl

/-! ## Evaluated checks against the snapshot (no proof terms) -/

#guard (List.range 24).all fun B =>
  decide ((IntMul.computablePiScaledWithCost B).1 = (piNat B : ℤ))
#guard (List.range 24).all fun B =>
  decide ((IntMul.computableLog2ScaledWithCost B).1 = (log2Nat B : ℤ))
-- `π·2^10 ≈ 3216.99`, `ln 2·2^10 ≈ 709.78`.
#guard 3215 ≤ piNat 10 ∧ piNat 10 ≤ 3218 ∧ 708 ≤ log2Nat 10 ∧ log2Nat 10 ≤ 711

#assert_std_axioms divRoundRatInt_eq_snap divRoundRatInt_natCast divRoundRatInt_shift piIter_eq
  piRef_eq piStep_eq piIter_le piNat_eq lnIter_eq log2Ref_eq lnA0 lnStep_natCast lnIter_natCast
  log2Nat_eq

end WP.W7k1
