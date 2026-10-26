import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives
import IntMul.TMComposition
import IntMul.FastDFT
import IntMul.ComputableSchedule
import IntMul.ComputableCore
import IntMul.TrackedCore
import IntMul.TMCompiler
import IntMul.TMStages
import IntMul.TMArithStages
import IntMul.TMStageEval

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# Uniform 8-Stack `Turing.FinTM2` Schedule & Transcendental Table Generator (`IntMul.TMSchedule`)

This module compiles the pure-integer transcendental Taylor series (`approxLogTwoFixed`,
`arctanInvTaylorFixed`, `approxPiFixed`, `expTwoPiIFixed`, `sincTaylorFixed`, `expTaylorFixed`,
`erfIntegralTaylorFixed`, `computeFilterTapFixed`, `computeGHatMantissaFixed`) and the recursive
multi-level schedule tree constructor `computeScheduleIntTree` into concrete, uniform 8-stack `BitMachine` (`Turing.FinTM2`)
stages (`Fintype.card Λ = O(1)`, `|σ| = 32`, `|Γ| = 2`; see Lemma 3.2 (`lem:elementary`),
Section 3.3 (`sec:tables`), and Section 8 (`sec:lean`)).
-/

namespace IntMul

open Turing

/-! ## 1. Signed-Word Primitives (`bmSignedOne`, `bmSignedSucc`, `bmSignedTwoPow`, `bmSignedMax`, `bmSignedMin`) -/

theorem StageEval.signedZero {S : Type} (W : S → ℕ) :
    StageEval bmSignedZero (fun s => encUnary (W s))
      (fun s => encodeSignedWord (W s) 0) (fun s => 15 * W s + 45) :=
  fun s => bmSignedZero_computesInTime (W s)

/-- Consumes `encUnary W` (`1 ≤ W`) on `kIO` and emits `encodeSignedWord W 1` in `≤ 80 * W + 220` steps. -/
def bmSignedOne : BitMachine :=
  bmSeq (bmFanout bmId (bmConstBool true)) bmNatToSigned

theorem bmSignedOne_computesInTime (W : ℕ) (hW : 1 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 80 * W + 220,
      bmSignedOne.ComputesInTime
        (mkTapes8 (encodeDelimWord (encUnary W)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W 1)) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have p1 := StageEval.fanout
    (StageEval.id_stage (fun _ : S => encUnary W))
    (StageEval.of_computesStageLe (bmConstBool_computesStageLe true encUnary) (fun _ : S => W))
  have h1_lt1 : 1 < 2 ^ 1 := by decide
  have h1_ltW : 1 < 2 ^ W := lt_of_lt_of_le h1_lt1 (Nat.pow_le_pow_right (by decide) hW)
  have p2 := StageEval.const (S := S) (bmNatToSigned_computesInTime W 1 1 h1_lt1 h1_ltW)
  have p1' : StageEval (S := S) (bmFanout bmId (bmConstBool true))
      (fun _ => encUnary W)
      (fun _ => encPair encUnary encBits (W, encodeNatBits 1 1))
      (fun _ => 11 * W + 30) := by
    refine (StageEval.congr_out p1 (fun _ => rfl)).mono (fun _ => ?_)
    simp [encBool, length_encUnary]; omega
  rcases StageEval.seq p1' p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp
  exact ⟨t, by omega, hcomp⟩

/-- Increment a `W`-bit signed integer (`1 ≤ W`):
`encodeSignedWord W x ↦ encodeSignedWord W (x + 1)` in `≤ 800 * W + 2000` steps. -/
def bmSignedSucc : BitMachine :=
  bmSeq (bmFanout bmId (bmSeq bmSignedWidth bmSignedOne)) bmSignedAdd

theorem bmSignedSucc_computesInTime (W : ℕ) (hW : 1 ≤ W) (x : ℤ)
    (hx : FitsSignedWord W x) (hx1 : FitsSignedWord W (x + 1))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 800 * W + 2000,
      bmSignedSucc.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (x + 1))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have h1_fits : FitsSignedWord W 1 := by
    rw [fitsSignedWord_iff_abs_lt]
    have : (1 : ℤ) < (2 : ℤ) ^ 1 := by decide
    exact lt_of_lt_of_le this (pow_le_pow_right₀ (by decide) hW)
  have pW := StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => x)
  have pOne := StageEval.seq pW (StageEval.const (S := S) (bmSignedOne_computesInTime W hW))
  have pPair := StageEval.fanout (StageEval.id_stage (fun _ : S => encodeSignedWord W x)) pOne
  have pAdd := StageEval.seq pPair
    (StageEval.const (S := S) (bmSignedAdd_computesInTime W x 1 hx h1_fits hx1))
  rcases pAdd () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Double a `W`-bit signed integer:
`encodeSignedWord W x ↦ encodeSignedWord W (2 * x)` in `≤ 600 * W + 1400` steps. -/
def bmSignedDouble : BitMachine :=
  bmSeq bmDup bmSignedAdd

theorem bmSignedDouble_computesInTime (W : ℕ) (x : ℤ)
    (hx : FitsSignedWord W x) (h2x : FitsSignedWord W (2 * x))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 600 * W + 1400,
      bmSignedDouble.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W x)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (2 * x))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  have hxx : FitsSignedWord W (x + x) := by rwa [← two_mul]
  let S := Unit
  have p1 := StageEval.dup (fun _ : S => encodeSignedWord W x)
  have p2 := StageEval.const (S := S) (bmSignedAdd_computesInTime W x x hx hx hxx)
  have p3 := StageEval.congr_out (v2 := fun _ => encodeSignedWord W (2 * x))
    (StageEval.seq p1 p2) (fun _ => by rw [two_mul])
  rcases p3 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Construct `encodeSignedWord W ((2 : ℤ) ^ k)` from `encPair encUnary encUnary (W, k)`
(`1 ≤ W`, `k < W`) in `≤ 3000 * W + 3000 * k + 6000` steps. -/
def bmSignedTwoPow : BitMachine :=
  let bmOneW := bmSeq bmFst bmSignedOne
  let bmShifted := bmSeq (bmFanout bmSnd bmOneW) bmShiftLeftSigned
  bmSeq (bmFanout bmFst bmShifted) bmResizeSignedWord

theorem bmSignedTwoPow_computesInTime (W k : ℕ) (hW : 1 ≤ W) (hk : k < W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 3000 * W + 3000 * k + 6000,
      bmSignedTwoPow.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (W, k)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W ((2 : ℤ) ^ k)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have pW := StageEval.fst (fun _ : S => encUnary W) (fun _ : S => encUnary k)
  have pK := StageEval.snd (fun _ : S => encUnary W) (fun _ : S => encUnary k)
  have pOne := StageEval.seq pW (StageEval.const (S := S) (bmSignedOne_computesInTime W hW))
  have h1_fits : FitsSignedWord W 1 := by
    rw [fitsSignedWord_iff_abs_lt]
    have : (1 : ℤ) < (2 : ℤ) ^ 1 := by decide
    exact lt_of_lt_of_le this (pow_le_pow_right₀ (by decide) hW)
  have pShifted := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord (k + W) ((2 : ℤ) ^ k))
    (StageEval.seq (StageEval.fanout pK pOne)
      (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime k W 1 h1_fits)))
    (fun _ => by rw [one_mul])
  have hk_fits1 : FitsSignedWord (k + W) ((2 : ℤ) ^ k) :=
    (FitsSignedWord.two_pow k).mono (by omega)
  have hk_fits2 : FitsSignedWord W ((2 : ℤ) ^ k) :=
    (FitsSignedWord.two_pow k).mono hk
  have pOut := StageEval.seq (StageEval.fanout pW pShifted)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime (k + W) W ((2 : ℤ) ^ k) hk_fits1 hk_fits2))
  rcases pOut () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Signed comparison test `[decide (a < b)]` on `encPair (encodeSignedWord W) (encodeSignedWord W) (a, b)`. -/
def bmSignedLt : BitMachine :=
  bmSeq bmSignedSubExt bmSignedIsNeg

theorem bmSignedLt_computesInTime (W : ℕ) (a b : ℤ)
    (ha : FitsSignedWord W a) (hb : FitsSignedWord W b)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 200 * W + 400,
      bmSignedLt.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (a, b)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord [decide (a < b)])
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have hab : FitsSignedWord (W + 1) (a - b) := by
    rw [fitsSignedWord_iff_abs_lt] at ha hb ⊢
    rw [pow_succ']
    linarith [abs_sub a b]
  have p1 := StageEval.const (S := S) (bmSignedSubExt_computesInTime W a b ha hb)
  have p2 := StageEval.const (S := S) (bmSignedIsNeg_computesInTime (W + 1) (a - b) hab)
  have hiff : decide (a - b < 0) = decide (a < b) := by
    simp only [decide_eq_decide]; omega
  rcases StageEval.congr_out (v2 := fun _ => [decide (a < b)])
    (StageEval.seq p1 p2) (fun _ => by rw [encBool, hiff]) ()
    tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Signed maximum `max a b` on `encPair (encodeSignedWord W) (encodeSignedWord W) (a, b)`. -/
def bmSignedMax : BitMachine :=
  bmIte bmSignedLt bmSnd bmFst

theorem bmSignedMax_computesInTime (W : ℕ) (a b : ℤ)
    (ha : FitsSignedWord W a) (hb : FitsSignedWord W b)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 300 * W + 600,
      bmSignedMax.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (a, b)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (max a b)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have pCond := StageEval.const (S := S) (bmSignedLt_computesInTime W a b ha hb)
  have pT := StageEval.snd (fun _ : S => encodeSignedWord W a) (fun _ : S => encodeSignedWord W b)
  have pF := StageEval.fst (fun _ : S => encodeSignedWord W a) (fun _ : S => encodeSignedWord W b)
  have hmax : (if decide (a < b) = true then encodeSignedWord W b else encodeSignedWord W a) =
      encodeSignedWord W (max a b) := by
    by_cases h : a < b
    · rw [decide_eq_true h, if_pos rfl, max_eq_right (le_of_lt h)]
    · rw [decide_eq_false h, if_neg Bool.false_ne_true, max_eq_left (not_lt.mp h)]
  rcases StageEval.congr_out (StageEval.ite_stage pCond pT pF) (fun _ => hmax) ()
    tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encPair, length_encodeSignedWord] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- Signed minimum `min a b` on `encPair (encodeSignedWord W) (encodeSignedWord W) (a, b)`. -/
def bmSignedMin : BitMachine :=
  bmIte bmSignedLt bmFst bmSnd

theorem bmSignedMin_computesInTime (W : ℕ) (a b : ℤ)
    (ha : FitsSignedWord W a) (hb : FitsSignedWord W b)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 300 * W + 600,
      bmSignedMin.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (a, b)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (min a b)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have pCond := StageEval.const (S := S) (bmSignedLt_computesInTime W a b ha hb)
  have pT := StageEval.fst (fun _ : S => encodeSignedWord W a) (fun _ : S => encodeSignedWord W b)
  have pF := StageEval.snd (fun _ : S => encodeSignedWord W a) (fun _ : S => encodeSignedWord W b)
  have hmin : (if decide (a < b) = true then encodeSignedWord W a else encodeSignedWord W b) =
      encodeSignedWord W (min a b) := by
    by_cases h : a < b
    · rw [decide_eq_true h, if_pos rfl, min_eq_left (le_of_lt h)]
    · rw [decide_eq_false h, if_neg Bool.false_ne_true, min_eq_right (not_lt.mp h)]
  rcases StageEval.congr_out (StageEval.ite_stage pCond pT pF) (fun _ => hmin) ()
    tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encPair, length_encodeSignedWord] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- Clamping below by `0`: `encodeSignedWord W a ↦ encodeSignedWord W (max 0 a)`. -/
def bmSignedMaxZero : BitMachine :=
  bmIte bmSignedIsNeg (bmSeq bmSignedWidth bmSignedZero) bmId

theorem bmSignedMaxZero_computesInTime (W : ℕ) (a : ℤ) (ha : FitsSignedWord W a)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 100 * W + 250,
      bmSignedMaxZero.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W a)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (max 0 a))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have pCond := StageEval.const (S := S) (bmSignedIsNeg_computesInTime W a ha)
  have pT := StageEval.seq
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => a))
    (StageEval.const (S := S) (bmSignedZero_computesInTime W))
  have pF := StageEval.id_stage (fun _ : S => encodeSignedWord W a)
  have hmax : (if decide (a < 0) = true then encodeSignedWord W 0 else encodeSignedWord W a) =
      encodeSignedWord W (max 0 a) := by
    by_cases h : a < 0
    · rw [decide_eq_true h, if_pos rfl, max_eq_left (le_of_lt h)]
    · rw [decide_eq_false h, if_neg Bool.false_ne_true, max_eq_right (not_lt.mp h)]
  rcases StageEval.congr_out (StageEval.ite_stage pCond pT pF) (fun _ => hmax) ()
    tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encodeSignedWord] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-! ## 2. $O(W)$ Sign-Bit Extraction (`bmAltSignMulSigned`, `bmIPowReMulSigned`, `bmIPowImMulSigned`) -/

/-- Extract bit 0 (`[decide (m % 2 = 1)]`) from `encodeSignedWord W (m : ℤ)` (`1 ≤ W`, `m < 2 ^ W`). -/
def bmSignedBit0 : BitMachine :=
  bmSeq (bmFanout (bmUnaryConst 1) bmId) bmTakePadBits

theorem takePadBits_one_encodeSignedWord (W m : ℕ) (hW : 1 ≤ W) (hm : m < 2 ^ W) :
    takePadBits 1 (encodeSignedWord W (m : ℤ)) = [decide (m % 2 = 1)] := by
  rw [← encodeSignedWord_of_nat W m hm]
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rw [encodeNatBits_succ_mod_div W' m]
  rfl

theorem bmSignedBit0_computesInTime (W m : ℕ) (hW : 1 ≤ W) (hm : m < 2 ^ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 40 * W + 100,
      bmSignedBit0.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (m : ℤ))) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord [decide (m % 2 = 1)]) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encodeSignedWord W (m : ℤ)
  have pOne := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 1 id) uIn
  have pTake := StageEval.congr_out (v2 := fun _ => [decide (m % 2 = 1)])
    (StageEval.seq (StageEval.fanout pOne (StageEval.id_stage uIn))
      (StageEval.takePadBits_stage (fun _ : S => 1) uIn))
    (fun _ => takePadBits_one_encodeSignedWord W m hW hm)
  rcases pTake () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht
  simp only [length_encodeSignedWord, length_encUnary] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Extract bit 1 (`[decide ((m / 2) % 2 = 1)]`) from `encodeSignedWord W (m : ℤ)` (`2 ≤ W`, `m < 2 ^ W`). -/
def bmSignedBit1 : BitMachine :=
  bmSeq (bmSeq (bmFanout (bmUnaryConst 1) bmId) bmDropBits)
    (bmSeq (bmFanout (bmUnaryConst 1) bmId) bmTakePadBits)

theorem takePadBits_one_drop_one_encodeSignedWord (W m : ℕ) (hW : 2 ≤ W) (hm : m < 2 ^ W) :
    takePadBits 1 ((encodeSignedWord W (m : ℤ)).drop 1) = [decide ((m / 2) % 2 = 1)] := by
  rw [← encodeSignedWord_of_nat W m hm]
  obtain ⟨W'', rfl⟩ : ∃ W'', W = W'' + 2 := ⟨W - 2, by omega⟩
  rw [show W'' + 2 = (W'' + 1) + 1 by omega, encodeNatBits_succ_mod_div (W'' + 1) m,
    encodeNatBits_succ_mod_div W'' (m / 2)]
  rfl

theorem bmSignedBit1_computesInTime (W m : ℕ) (hW : 2 ≤ W) (hm : m < 2 ^ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 80 * W + 220,
      bmSignedBit1.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (m : ℤ))) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord [decide ((m / 2) % 2 = 1)]) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encodeSignedWord W (m : ℤ)
  let uDrop : S → List Bool := fun _ => (encodeSignedWord W (m : ℤ)).drop 1
  have pOne := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 1 id) uIn
  have pDrop := StageEval.seq (StageEval.fanout pOne (StageEval.id_stage uIn))
    (StageEval.dropBits (fun _ : S => 1) uIn)
  have pOne2 := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 1 id) uDrop
  have pTake := StageEval.congr_out (v2 := fun _ => [decide ((m / 2) % 2 = 1)])
    (StageEval.seq pDrop
      (StageEval.seq (StageEval.fanout pOne2 (StageEval.id_stage uDrop))
        (StageEval.takePadBits_stage (fun _ : S => 1) uDrop)))
    (fun _ => takePadBits_one_drop_one_encodeSignedWord W m hW hm)
  rcases pTake () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uDrop, id] at ht
  simp only [length_encodeSignedWord, List.length_drop, length_encUnary] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Alternating sign multiplication `(encodeSignedWord W (m : ℤ), encodeSignedWord W x) ↦
encodeSignedWord W (altSign m * x)` in `≤ 800 * W + 2000` steps. -/
def bmAltSignMulSigned : BitMachine :=
  bmIte (bmSeq bmFst bmSignedBit0) (bmSeq bmSnd bmSignedNeg) bmSnd

theorem bmAltSignMulSigned_computesInTime (W m : ℕ) (hW : 1 ≤ W) (hm : m < 2 ^ W) (x : ℤ)
    (hx : FitsSignedWord W x) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 800 * W + 2000,
      bmAltSignMulSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) ((m : ℤ), x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (altSign m * x)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encodeSignedWord W (m : ℤ)
  let u2 : S → List Bool := fun _ => encodeSignedWord W x
  have pCond := StageEval.seq (StageEval.fst u1 u2)
    (StageEval.const (S := S) (bmSignedBit0_computesInTime W m hW hm))
  have pT := StageEval.seq (StageEval.snd u1 u2)
    (StageEval.const (S := S) (bmSignedNeg_computesInTime W x hx))
  have pF := StageEval.snd u1 u2
  have halt : (if decide (m % 2 = 1) = true then encodeSignedWord W (-x) else encodeSignedWord W x) =
      encodeSignedWord W (altSign m * x) := by
    unfold altSign
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · simp [h0]
    · simp [h1]
  rcases StageEval.congr_out (StageEval.ite_stage pCond pT pF) (fun _ => halt) ()
    tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [u1, u2, id] at ht
  simp only [length_encDepPair, length_encodeSignedWord] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- Real part of $i^m$ multiplication: `(encodeSignedWord W (m : ℤ), encodeSignedWord W x) ↦
encodeSignedWord W (iPowRe m * x)` in `≤ 1100 * W + 2800` steps. -/
def bmIPowReMulSigned : BitMachine :=
  bmIte (bmSeq bmFst bmSignedBit0)
    (bmSeq (bmSeq bmSnd bmSignedWidth) bmSignedZero)
    (bmIte (bmSeq bmFst bmSignedBit1) (bmSeq bmSnd bmSignedNeg) bmSnd)

theorem bmIPowReMulSigned_computesInTime (W m : ℕ) (hW : 2 ≤ W) (hm : m < 2 ^ W) (x : ℤ)
    (hx : FitsSignedWord W x) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 1100 * W + 2800,
      bmIPowReMulSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) ((m : ℤ), x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (iPowRe m * x)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encodeSignedWord W (m : ℤ)
  let u2 : S → List Bool := fun _ => encodeSignedWord W x
  have pC0 := StageEval.seq (StageEval.fst u1 u2)
    (StageEval.const (S := S) (bmSignedBit0_computesInTime W m (by omega) hm))
  have pC1 := StageEval.seq (StageEval.fst u1 u2)
    (StageEval.const (S := S) (bmSignedBit1_computesInTime W m hW hm))
  have pZero := StageEval.seq
    (StageEval.seq (StageEval.snd u1 u2)
      (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => x)))
    (StageEval.const (S := S) (bmSignedZero_computesInTime W))
  have pNeg := StageEval.seq (StageEval.snd u1 u2)
    (StageEval.const (S := S) (bmSignedNeg_computesInTime W x hx))
  have pId := StageEval.snd u1 u2
  have hipow :
      (if decide (m % 2 = 1) = true then encodeSignedWord W 0
       else if decide ((m / 2) % 2 = 1) = true then encodeSignedWord W (-x)
       else encodeSignedWord W x) =
      encodeSignedWord W (iPowRe m * x) := by
    unfold iPowRe
    have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · have h0 : m % 2 = 0 := by omega
      have h1 : (m / 2) % 2 = 0 := by omega
      simp [h, h0, h1]
    · have h0 : m % 2 = 1 := by omega
      simp [h, h0]
    · have h0 : m % 2 = 0 := by omega
      have h1 : (m / 2) % 2 = 1 := by omega
      simp [h, h0, h1]
    · have h0 : m % 2 = 1 := by omega
      simp [h, h0]
  rcases StageEval.congr_out (StageEval.ite_stage pC0 pZero (StageEval.ite_stage pC1 pNeg pId))
    (fun _ => hipow) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [u1, u2, id] at ht
  simp only [length_encDepPair, length_encodeSignedWord] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- Imaginary part of $i^m$ multiplication: `(encodeSignedWord W (m : ℤ), encodeSignedWord W x) ↦
encodeSignedWord W (iPowIm m * x)` in `≤ 1100 * W + 2800` steps. -/
def bmIPowImMulSigned : BitMachine :=
  bmIte (bmSeq bmFst bmSignedBit0)
    (bmIte (bmSeq bmFst bmSignedBit1) (bmSeq bmSnd bmSignedNeg) bmSnd)
    (bmSeq (bmSeq bmSnd bmSignedWidth) bmSignedZero)

theorem bmIPowImMulSigned_computesInTime (W m : ℕ) (hW : 2 ≤ W) (hm : m < 2 ^ W) (x : ℤ)
    (hx : FitsSignedWord W x) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 1100 * W + 2800,
      bmIPowImMulSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) ((m : ℤ), x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (iPowIm m * x)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encodeSignedWord W (m : ℤ)
  let u2 : S → List Bool := fun _ => encodeSignedWord W x
  have pC0 := StageEval.seq (StageEval.fst u1 u2)
    (StageEval.const (S := S) (bmSignedBit0_computesInTime W m (by omega) hm))
  have pC1 := StageEval.seq (StageEval.fst u1 u2)
    (StageEval.const (S := S) (bmSignedBit1_computesInTime W m hW hm))
  have pZero := StageEval.seq
    (StageEval.seq (StageEval.snd u1 u2)
      (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => x)))
    (StageEval.const (S := S) (bmSignedZero_computesInTime W))
  have pNeg := StageEval.seq (StageEval.snd u1 u2)
    (StageEval.const (S := S) (bmSignedNeg_computesInTime W x hx))
  have pId := StageEval.snd u1 u2
  have hipow :
      (if decide (m % 2 = 1) = true then
         if decide ((m / 2) % 2 = 1) = true then encodeSignedWord W (-x)
         else encodeSignedWord W x
       else encodeSignedWord W 0) =
      encodeSignedWord W (iPowIm m * x) := by
    unfold iPowIm
    have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · have h0 : m % 2 = 0 := by omega
      simp [h, h0]
    · have h0 : m % 2 = 1 := by omega
      have h1 : (m / 2) % 2 = 0 := by omega
      simp [h, h0, h1]
    · have h0 : m % 2 = 0 := by omega
      simp [h, h0]
    · have h0 : m % 2 = 1 := by omega
      have h1 : (m / 2) % 2 = 1 := by omega
      simp [h, h0, h1]
  rcases StageEval.congr_out (StageEval.ite_stage pC0 (StageEval.ite_stage pC1 pNeg pId) pZero)
    (fun _ => hipow) () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [u1, u2, id] at ht
  simp only [length_encDepPair, length_encodeSignedWord] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-! ## 3. Signed-Counter Loop (`bmIterLoopSigned`), Tabulation (`bmTabulateSigned`), and Sum Combinators -/

/-- Convert `encPair encUnary encUnary (W, k)` (`1 ≤ W`, `k < 2 ^ W`) to `encodeSignedWord W (k : ℤ)`. -/
def bmUnaryToSigned : BitMachine :=
  bmSeq (bmSeq bmSwap (bmMapSnd bmSignedZero)) (bmIterLoop bmSignedSucc)

theorem bmUnaryToSigned_computesInTime (W k : ℕ) (hW : 1 ≤ W) (hk : k < 2 ^ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ k * (800 * W + 2010) + 60 * W + 40 * k + 200,
      bmUnaryToSigned.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (W, k)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (k : ℤ)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  have pSwap := StageEval.swap (fun _ : S => encUnary W) (fun _ : S => encUnary k)
  have pInit := StageEval.congr_out
    (v2 := encDepPair (fun _ => encUnary k) (fun _ => encodeSignedWord W ((0 : ℕ) : ℤ)))
    (StageEval.seq pSwap
      (StageEval.mapSnd (u1 := fun _ : S => encUnary k)
        (StageEval.const (S := S) (bmSignedZero_computesInTime W))))
    (fun _ => rfl)
  have pLoop := StageEval.iterLoop_idx (S := S) (k := fun _ => k)
    (u := fun _ i => encodeSignedWord W (i : ℤ))
    (B := fun _ => 800 * W + 2000)
    (fun ⟨⟨_, i⟩, hi⟩ u2 u3 u4 u5 uSc => by
      dsimp only at hi ⊢
      have hf0 : FitsSignedWord W (i : ℤ) := by
        rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
      have hf1 : FitsSignedWord W ((i : ℤ) + 1) := by
        have : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; rfl
        rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
      rcases bmSignedSucc_computesInTime W hW (i : ℤ) hf0 hf1 u2 u3 u4 u5 uSc with ⟨t, ht, hc⟩
      have hcast : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast] at hc
      exact ⟨t, ht, hc⟩)
  rcases StageEval.seq pInit pLoop () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- **Signed-Counter Iterative Loop (`bmIterLoopSigned bodyM`)**:
Consumes `encPair (encPair (encPair encCtx encUnary) encUnary) encSt (((ctx, W), N), st 0)` on `kIO`
(`1 ≤ W`, `N < 2 ^ W`) and runs `N` iterations (`i = 0, ..., N - 1`), passing
`(((ctx, W), encodeSignedWord W (i : ℤ)), st i)` to `bodyM` at each step, and emitting `st N` on `kIO`. -/
def bmIterLoopSigned (bodyM : BitMachine) : BitMachine :=
  let bmCW := bmSeq bmFst bmFst
  let bmZeroIdx := bmSeq (bmSeq bmCW bmSnd) bmSignedZero
  let bmInit :=
    bmFanout
      (bmSeq bmFst bmSnd)
      (bmFanout (bmFanout bmCW bmZeroIdx) bmSnd)
  let bmStep := bmFanout (bmSeq bmFst (bmMapSnd bmSignedSucc)) bodyM
  bmSeq bmInit (bmSeq (bmIterLoop bmStep) bmSnd)

/-- **Stage Evaluation Theorem for `bmIterLoopSigned` (`StageEval.iterLoopSigned`)**:
Runs `N s` iterations with a fixed-width signed loop counter `encodeSignedWord (W s) (i : ℤ)`
in $O(N \cdot (B + W + L_{\text{ctx}} + L_{\text{st}}))$ steps, with **zero** $O(N^2)$ counter overhead. -/
theorem StageEval.iterLoopSigned {S : Type} {bodyM : BitMachine}
    {uCtx : S → List Bool} {W N : S → ℕ} {uSt : S → ℕ → List Bool}
    {B L_ctx L_st : S → ℕ}
    (hW : ∀ s, 1 ≤ W s)
    (hN : ∀ s, N s < 2 ^ W s)
    (hbody : ∀ (i : ℕ),
      StageEval (S := { s : S // i < N s }) bodyM
        (encDepPair
          (encDepPair (encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val)))
            (fun s => encodeSignedWord (W s.val) (i : ℤ)))
          (fun s => uSt s.val i))
        (fun s => uSt s.val (i + 1))
        (fun s => B s.val))
    (hL_ctx : ∀ s, (uCtx s).length ≤ L_ctx s)
    (hL_st : ∀ (s : S) (i : ℕ), i ≤ N s → (uSt s i).length ≤ L_st s) :
    StageEval (bmIterLoopSigned bodyM)
      (encDepPair
        (encDepPair (encDepPair uCtx (fun s => encUnary (W s))) (fun s => encUnary (N s)))
        (fun s => uSt s 0))
      (fun s => uSt s (N s))
      (fun s =>
        N s * (B s + 1000 * W s + 100 * L_ctx s + 20 * L_st s + 2500) +
        300 * L_ctx s + 450 * W s + 150 * N s + 100 * L_st s + 900) := by
  let uCW : S → List Bool := encDepPair uCtx (fun s => encUnary (W s))
  let uCWN : S → List Bool := encDepPair uCW (fun s => encUnary (N s))
  let uFullSt : S → ℕ → List Bool := fun s i =>
    encDepPair (encDepPair uCW (fun s => encodeSignedWord (W s) (i : ℤ))) (fun s => uSt s i) s
  have pCW := StageEval.seq (StageEval.fst uCWN (fun s => uSt s 0))
    (StageEval.fst uCW (fun s => encUnary (N s)))
  have pZero := StageEval.congr_out
    (v2 := fun s => encodeSignedWord (W s) ((0 : ℕ) : ℤ))
    (StageEval.seq (StageEval.seq pCW (StageEval.snd uCtx (fun s => encUnary (W s))))
      (StageEval.signedZero W))
    (fun _ => rfl)
  have pInit := StageEval.fanout
    (StageEval.seq (StageEval.fst uCWN (fun s => uSt s 0))
      (StageEval.snd uCW (fun s => encUnary (N s))))
    (StageEval.fanout (StageEval.fanout pCW pZero) (StageEval.snd uCWN (fun s => uSt s 0)))
  have pLoop := StageEval.iterLoop_idx (S := S) (k := N) (u := uFullSt)
    (B := fun s => B s + 1000 * W s + 100 * L_ctx s + 20 * L_st s + 2400)
    (fun ⟨⟨s, i⟩, hi⟩ u2 u3 u4 u5 uSc => by
      dsimp only [id] at hi ⊢
      let SubS := { s' : S // i < N s' }
      let uCW' : SubS → List Bool := encDepPair (fun s' => uCtx s'.val) (fun s' => encUnary (W s'.val))
      let uIdx : SubS → List Bool := fun s' => encodeSignedWord (W s'.val) (i : ℤ)
      let uIdx1 : SubS → List Bool := fun s' => encodeSignedWord (W s'.val) ((i + 1 : ℕ) : ℤ)
      let uS : SubS → List Bool := fun s' => uSt s'.val i
      have pSucc : StageEval (S := SubS) bmSignedSucc uIdx uIdx1
          (fun s' => 800 * W s'.val + 2000) := by
        intro s' v2 v3 v4 v5 vSc
        have hs' : i < N s'.val := s'.property
        have hN' : N s'.val < 2 ^ W s'.val := hN s'.val
        have hf0 : FitsSignedWord (W s'.val) (i : ℤ) := by
          rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        have hf1 : FitsSignedWord (W s'.val) ((i : ℤ) + 1) := by
          have : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; rfl
          rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        rcases bmSignedSucc_computesInTime (W s'.val) (hW s'.val) (i : ℤ) hf0 hf1 v2 v3 v4 v5 vSc
          with ⟨t, ht, hc⟩
        have hcast : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; rfl
        rw [hcast] at hc
        exact ⟨t, ht, hc⟩
      have pLeft := StageEval.seq (StageEval.fst (encDepPair uCW' uIdx) uS)
        (StageEval.mapSnd (u1 := uCW') pSucc)
      have pFan := StageEval.fanout pLeft (hbody i)
      rcases pFan ⟨s, hi⟩ u2 u3 u4 u5 uSc with ⟨t, ht, hc⟩
      dsimp only [uCW', uIdx, uIdx1, uS, id] at ht hc
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
      have hlc := hL_ctx s
      have hls := hL_st s i (le_of_lt hi)
      have hls1 := hL_st s (i + 1) hi
      exact ⟨t, by omega, hc⟩)
  have pEnd := StageEval.snd
    (encDepPair uCW (fun s => encodeSignedWord (W s) ((N s : ℕ) : ℤ)))
    (fun s => uSt s (N s))
  refine (StageEval.seq pInit (StageEval.seq pLoop pEnd)).mono (fun s => ?_)
  dsimp only [uCWN, uCW, uFullSt]
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
  have hlc := hL_ctx s
  have hls0 := hL_st s 0 (Nat.zero_le _)
  have hlsN := hL_st s (N s) (le_refl _)
  have hmul :
      N s * (B s + 1000 * W s + 100 * L_ctx s + 20 * L_st s + 2400 + 3) ≤
      N s * (B s + 1000 * W s + 100 * L_ctx s + 20 * L_st s + 2500) :=
    Nat.mul_le_mul_left (N s) (by omega)
  omega

/-- **Signed-Counter Tabulation Combinator (`bmTabulateSigned emitM`)**:
Consumes `encPair (encPair encCtx encUnary) encUnary ((ctx, W), N)` on `kIO` (`1 ≤ W`, `N < 2 ^ W`)
and tabulates `encList encElem ((List.range N).map (fn s))` on `kIO` in
$O(N \cdot (B_{\text{emit}} + W + L_{\text{ctx}} + L_{\text{elem}}))$ steps, with **zero** $O(N^2)$ overhead. -/
def bmTabulateSigned (emitM : BitMachine) : BitMachine :=
  let bmInit := bmFanout bmFst (bmSeq (bmSeq bmFst bmSnd) bmSignedZero)
  let bmSetup :=
    (tmDupWord kIO kWork0 kWork2).seq
      (bmSnd.seq
        ((tmMoveWord kIO kWork0 kWork4).seq
          ((tmPushEmpty kWork5).seq
            ((tmMoveWord kWork2 kWork0 kIO).seq bmInit))))
  let bmStepBody :=
    (bmFanout emitM (bmMapSnd bmSignedSucc)).seq
      ((tmPopFirstSubwordRev kIO kWork0).seq
        ((tmPrependRevWord kWork0 kWork5).seq
          ((tmPopFirstSubwordRev kIO kWork0).seq
            ((tmDropWord kIO).seq
              (tmRevMoveWord kWork0 kIO)))))
  bmSetup.seq
    ((bmStepBody.loopDelimWord kWork4).seq
      ((tmDropWord kIO).seq
        ((tmMoveWord kWork5 kWork0 kIO).seq bmRevList)))

theorem bmTabulateSigned_loop_le {S α : Type} {emitM : BitMachine}
    {uCtx : S → List Bool} {W N : S → ℕ} {encElem : S → α → List Bool}
    {fn : S → ℕ → α}
    {B L_ctx L_elem : S → ℕ}
    (hW : ∀ s, 1 ≤ W s)
    (hN : ∀ s, N s < 2 ^ W s)
    (hemit : ∀ (i : ℕ),
      StageEval (S := { s : S // i < N s }) emitM
        (encDepPair (encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val)))
          (fun s => encodeSignedWord (W s.val) (i : ℤ)))
        (fun s => encElem s.val (fn s.val i))
        (fun s => B s.val))
    (hL_ctx : ∀ s, (uCtx s).length ≤ L_ctx s)
    (hL_elem : ∀ (s : S) (i : ℕ), i < N s → (encElem s (fn s i)).length ≤ L_elem s)
    (s : S) :
    ∀ (rem idx : ℕ) (_hsum : idx + rem = N s)
      (tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ rem * (B s + 1000 * W s + 100 * L_ctx s + 10 * L_elem s + 2400) + 1,
        (((bmFanout emitM (bmMapSnd bmSignedSucc)).seq
            ((tmPopFirstSubwordRev kIO kWork0).seq
              ((tmPrependRevWord kWork0 kWork5).seq
                ((tmPopFirstSubwordRev kIO kWork0).seq
                  ((tmDropWord kIO).seq
                    (tmRevMoveWord kWork0 kIO)))))).loopDelimWord kWork4).ComputesInTime
          (mkTapes8 (encodeDelimWord
            (encDepPair (encDepPair uCtx (fun s' => encUnary (W s')))
              (fun s' => encodeSignedWord (W s') (idx : ℤ)) s)) [] []
            tW2 tW3 (encodeDelimWord (encUnary rem) ++ tW4)
            (encodeDelimWord (encList (encElem s) (((List.range idx).map (fn s)).reverse)) ++ tW5) tSch)
          (mkTapes8 (encodeDelimWord
            (encDepPair (encDepPair uCtx (fun s' => encUnary (W s')))
              (fun s' => encodeSignedWord (W s') ((N s : ℕ) : ℤ)) s)) [] []
            tW2 tW3 tW4
            (encodeDelimWord (encList (encElem s) (((List.range (N s)).map (fn s)).reverse)) ++ tW5) tSch) t
  | 0, idx, hsum, tW2, tW3, tW4, tW5, tSch => by
    have hidx : idx = N s := by omega
    subst hidx
    simp only [Nat.zero_mul, encUnary, List.replicate_zero]
    refine ⟨1, le_rfl, ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [BitMachine.loopDelimWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_nil, List.cons_append,
      List.nil_append, mkTapes8_kWork4, update_mkTapes8_kWork4, List.head?_cons, List.tail_cons,
      Option.getD_some, cond_true]
  | rem + 1, idx, hsum, tW2, tW3, tW4, tW5, tSch => by
    have hlt : idx < N s := by omega
    let body :=
      (bmFanout emitM (bmMapSnd bmSignedSucc)).seq
        ((tmPopFirstSubwordRev kIO kWork0).seq
          ((tmPrependRevWord kWork0 kWork5).seq
            ((tmPopFirstSubwordRev kIO kWork0).seq
              ((tmDropWord kIO).seq
                (tmRevMoveWord kWork0 kIO)))))
    let curWord :=
      encDepPair (encDepPair uCtx (fun s => encUnary (W s)))
        (fun s => encodeSignedWord (W s) (idx : ℤ)) s
    let nextWord :=
      encDepPair (encDepPair uCtx (fun s => encUnary (W s)))
        (fun s => encodeSignedWord (W s) ((idx + 1 : ℕ) : ℤ)) s
    let elemWord := encElem s (fn s idx)
    let acc := ((List.range idx).map (fn s)).reverse
    have hpop : (body.loopDelimWord kWork4).toFinTM2.step
        ⟨some none, default,
          mkTapes8 (encodeDelimWord curWord) [] []
            tW2 tW3 (encodeDelimWord (encUnary (rem + 1)) ++ tW4)
            (encodeDelimWord (encList (encElem s) acc) ++ tW5) tSch⟩ =
        some ⟨some (some body.main), default,
          mkTapes8 (encodeDelimWord curWord) [] []
            tW2 tW3 (encodeDelimWord (encUnary rem) ++ tW4)
            (encodeDelimWord (encList (encElem s) acc) ++ tW5) tSch⟩ := by
      simp only [encUnary, List.replicate_succ, BitMachine.loopDelimWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons,
        List.cons_append, mkTapes8_kWork4, update_mkTapes8_kWork4, List.head?_cons, List.tail_cons,
        Option.getD_some, cond_false]
    let SubS := { s' : S // idx < N s' }
    let uCW : SubS → List Bool := encDepPair (fun s' => uCtx s'.val) (fun s' => encUnary (W s'.val))
    let uIdx : SubS → List Bool := fun s' => encodeSignedWord (W s'.val) (idx : ℤ)
    let uIdx1 : SubS → List Bool := fun s' => encodeSignedWord (W s'.val) ((idx + 1 : ℕ) : ℤ)
    have pSucc : StageEval (S := SubS) bmSignedSucc uIdx uIdx1
        (fun s' => 800 * W s'.val + 2000) := by
      intro s' u2 u3 u4 u5 uSc
      have hs' : idx < N s'.val := s'.property
      have hN' : N s'.val < 2 ^ W s'.val := hN s'.val
      have hf0 : FitsSignedWord (W s'.val) (idx : ℤ) := by
        rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
      have hf1 : FitsSignedWord (W s'.val) ((idx : ℤ) + 1) := by
        have : (idx : ℤ) + 1 = ((idx + 1 : ℕ) : ℤ) := by push_cast; rfl
        rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
      rcases bmSignedSucc_computesInTime (W s'.val) (hW s'.val) (idx : ℤ) hf0 hf1 u2 u3 u4 u5 uSc
        with ⟨t, ht, hc⟩
      have hcast1 : (idx : ℤ) + 1 = ((idx + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast1] at hc
      exact ⟨t, ht, hc⟩
    have pFan := StageEval.fanout (hemit idx) (StageEval.mapSnd (u1 := uCW) pSucc)
    rcases pFan ⟨s, hlt⟩ tW2 tW3 (encodeDelimWord (encUnary rem) ++ tW4)
      (encodeDelimWord (encList (encElem s) acc) ++ tW5) tSch with ⟨tF, htF, b3⟩
    dsimp only [uCW, uIdx, uIdx1, id] at htF b3
    have b4 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
      (encodeDelimWord elemWord ++ encodeDelimWord nextWord) [] []
      (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord (encUnary rem) ++ tW4)
        (encodeDelimWord (encList (encElem s) acc) ++ tW5) tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
      unconsDelimWord_encodeDelimWord_append] at b4
    have b5 := tmPrependRevWord_computesInTime kWork0 kWork5 (by decide)
      elemWord.reverse (encList (encElem s) acc) [] tW5
      (mkTapes8 (encodeDelimWord (encodeDelimWord nextWord)) [] [] tW2 tW3
        (encodeDelimWord (encUnary rem) ++ tW4) [] tSch)
    simp only [update_mkTapes8_kWork0, update_mkTapes8_kWork5, List.length_reverse,
      List.reverse_reverse, List.append_nil] at b5
    have hacc_next : fn s idx :: acc = ((List.range (idx + 1)).map (fn s)).reverse := by
      dsimp only [acc]
      rw [List.range_succ, List.map_append, List.map_singleton, List.reverse_append,
        List.reverse_singleton, List.singleton_append]
    have b6 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
      (encodeDelimWord nextWord) [] []
      (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord (encUnary rem) ++ tW4)
        (encodeDelimWord (encList (encElem s) (fn s idx :: acc)) ++ tW5) tSch)
    simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
      unconsDelimWord_encodeDelimWord] at b6
    have b7 := tmDropWord_computesInTime kIO [] []
      (mkTapes8 [] (encodeDelimWord nextWord.reverse) [] tW2 tW3
        (encodeDelimWord (encUnary rem) ++ tW4)
        (encodeDelimWord (encList (encElem s) (fn s idx :: acc)) ++ tW5) tSch)
    simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at b7
    have b8 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
      nextWord.reverse [] []
      (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord (encUnary rem) ++ tW4)
        (encodeDelimWord (encList (encElem s) (fn s idx :: acc)) ++ tW5) tSch)
    simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
      List.reverse_reverse, List.append_nil] at b8
    have ⟨hbody_run⟩ := b3.seq (b4.seq (b5.seq (b6.seq (b7.seq b8))))
    rw [hacc_next] at hbody_run
    have hbody_lifted := BitMachine.loopDelimWord_body_evalsToInTime_concrete kWork4 body hbody_run
    rcases bmTabulateSigned_loop_le hW hN hemit hL_ctx hL_elem s rem (idx + 1) (by omega)
      tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, ⟨hih⟩⟩
    have hcomb := EvalsToInTime.trans' (EvalsToInTime.of_step hpop hbody_lifted) hih
    dsimp only [nextWord, elemWord] at htF b4 b5 b6 b8
    simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at htF b4 b5 b6 b8
    have hlc := hL_ctx s
    have hle := hL_elem s idx hlt
    refine ⟨_, ?_, ⟨hcomb⟩⟩
    have hstep_le :
        (tF + ((elemWord.length + 2) + ((elemWord.length + 2) +
          ((nextWord.length + 2) + (1 + (nextWord.length + 2)))))) + 1 ≤
        B s + 1000 * W s + 100 * L_ctx s + 10 * L_elem s + 2400 := by
      dsimp only [elemWord, nextWord]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega
    calc (tF + ((elemWord.length + 2) + ((elemWord.length + 2) +
          ((nextWord.length + 2) + ((0 + 1) + (nextWord.length + 2)))))) + 1 + t2
        ≤ (B s + 1000 * W s + 100 * L_ctx s + 10 * L_elem s + 2400) +
            (rem * (B s + 1000 * W s + 100 * L_ctx s + 10 * L_elem s + 2400) + 1) := by omega
      _ = (rem + 1) * (B s + 1000 * W s + 100 * L_ctx s + 10 * L_elem s + 2400) + 1 := by ring

theorem map_finRange_eq_map_range {α : Type} (N : ℕ) (f : ℕ → α) :
    (List.finRange N).map (fun i : Fin N => f i.val) = (List.range N).map f := by
  rw [← List.ofFn_eq_map, List.range_eq_range']
  have h : ∀ (s n : ℕ) (h : s + n ≤ N),
      List.ofFn (fun i : Fin n => f (s + i.val)) = (List.range' s n).map f := by
    intro s n h
    induction n generalizing s with
    | zero => rfl
    | succ n ih =>
      rw [List.ofFn_succ, List.range'_succ, List.map_cons]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      congr 1
      convert ih (s + 1) (by omega) using 2
      ext ⟨i, hi⟩
      ac_rfl
  simpa using h 0 N (by omega)

/-- **Stage Evaluation Theorem for `bmTabulateSigned` (`StageEval.tabulateSigned`)**:
Tabulates `(List.finRange (N s)).map (fun i : Fin (N s) => fn s i.val)` in
$O(N \cdot (B + W + L_{\text{ctx}} + L_{\text{elem}}))$ steps. -/
theorem StageEval.tabulateSigned {S α : Type} {emitM : BitMachine}
    {uCtx : S → List Bool} {W N : S → ℕ} {encElem : S → α → List Bool}
    {fn : S → ℕ → α}
    {B L_ctx L_elem : S → ℕ}
    (hW : ∀ s, 1 ≤ W s)
    (hN : ∀ s, N s < 2 ^ W s)
    (hemit : ∀ (i : ℕ),
      StageEval (S := { s : S // i < N s }) emitM
        (encDepPair (encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val)))
          (fun s => encodeSignedWord (W s.val) (i : ℤ)))
        (fun s => encElem s.val (fn s.val i))
        (fun s => B s.val))
    (hL_ctx : ∀ s, (uCtx s).length ≤ L_ctx s)
    (hL_elem : ∀ (s : S) (i : ℕ), i < N s → (encElem s (fn s i)).length ≤ L_elem s) :
    StageEval (bmTabulateSigned emitM)
      (encDepPair (encDepPair uCtx (fun s => encUnary (W s))) (fun s => encUnary (N s)))
      (fun s => encList (encElem s) ((List.finRange (N s)).map (fun i : Fin (N s) => fn s i.val)))
      (fun s =>
        N s * (B s + 1000 * W s + 100 * L_ctx s + 50 * L_elem s + 2500) +
        100 * L_ctx s + 150 * W s + 50 * N s + 400) := by
  intro s tW2 tW3 tW4 tW5 tSch
  dsimp only [id]
  let uCW : S → List Bool := encDepPair uCtx (fun s => encUnary (W s))
  let uIn : S → List Bool := encDepPair uCW (fun s => encUnary (N s))
  have s1 := tmDupWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
    (uIn s) [] [] tW2
    (mkTapes8 [] [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
    List.append_nil] at s1
  have pExtractN := StageEval.snd uCW (fun s => encUnary (N s))
  rcases pExtractN s (encodeDelimWord (uIn s) ++ tW2) tW3 tW4 tW5 tSch with ⟨tN, htN, s2⟩
  have s3 := tmMoveWord_computesInTime kIO kWork0 kWork4 (by decide) (by decide) (by decide)
    (encUnary (N s)) [] [] tW4
    (mkTapes8 [] [] [] (encodeDelimWord (uIn s) ++ tW2) tW3 [] tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork4,
    List.append_nil, length_encUnary] at s3
  have s4 := tmPushEmpty_computesInTime kWork5
    (mkTapes8 [] [] [] (encodeDelimWord (uIn s) ++ tW2) tW3
      (encodeDelimWord (encUnary (N s)) ++ tW4) tW5 tSch)
  simp only [update_mkTapes8_kWork5, mkTapes8_kWork5] at s4
  have s5 := tmMoveWord_computesInTime kWork2 kWork0 kIO (by decide) (by decide) (by decide)
    (uIn s) tW2 [] []
    (mkTapes8 [] [] [] [] tW3 (encodeDelimWord (encUnary (N s)) ++ tW4)
      (encodeDelimWord (encList (encElem s) []) ++ tW5) tSch)
  simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil, encList_nil] at s5
  have pZero := StageEval.congr_out
    (v2 := fun s => encodeSignedWord (W s) ((0 : ℕ) : ℤ))
    (StageEval.seq
      (StageEval.seq (StageEval.fst uCW (fun s => encUnary (N s)))
        (StageEval.snd uCtx (fun s => encUnary (W s))))
      (StageEval.signedZero W))
    (fun _ => rfl)
  have pInit := StageEval.fanout (StageEval.fst uCW (fun s => encUnary (N s))) pZero
  rcases pInit s tW2 tW3 (encodeDelimWord (encUnary (N s)) ++ tW4)
    (encodeDelimWord [] ++ tW5) tSch with ⟨tI, htI, s6⟩
  rcases bmTabulateSigned_loop_le hW hN hemit hL_ctx hL_elem s (N s) 0 (by omega)
    tW2 tW3 tW4 tW5 tSch with ⟨tL, htL, s7⟩
  simp only [List.range_zero, List.map_nil, List.reverse_nil, encList_nil] at s7
  let revOut := ((List.range (N s)).map (fn s)).reverse
  have s9 := tmDropWord_computesInTime kIO
    (encDepPair uCW (fun s' => encodeSignedWord (W s') ((N s : ℕ) : ℤ)) s) []
    (mkTapes8 [] [] [] tW2 tW3 tW4 (encodeDelimWord (encList (encElem s) revOut) ++ tW5) tSch)
  simp only [update_mkTapes8_kIO, List.append_nil] at s9
  have s10 := tmMoveWord_computesInTime kWork5 kWork0 kIO (by decide) (by decide) (by decide)
    (encList (encElem s) revOut) tW5 [] []
    (mkTapes8 [] [] [] tW2 tW3 tW4 [] tSch)
  simp only [update_mkTapes8_kWork5, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s10
  rcases (StageEval.revList (S := S) encElem (fun _ => revOut)) s tW2 tW3 tW4 tW5 tSch with
    ⟨tR, htR, s11⟩
  dsimp only [id] at htR s11
  rw [List.reverse_reverse, ← map_finRange_eq_map_range] at s11
  have hlen_rev : (encList (encElem s) revOut).length ≤ N s * (2 * L_elem s + 2) := by
    have h := length_encList_le_of_forall_le (encElem s) (L_elem s) revOut
      (fun y hy => by
        rcases List.mem_map.mp (List.mem_reverse.mp hy) with ⟨i, hi, rfl⟩
        exact hL_elem s i (List.mem_range.mp hi))
    simpa [revOut, List.length_reverse, List.length_map, List.length_range] using h
  dsimp only [uIn, uCW] at s1 htN s5 htI s9
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at s1 htN s5 htI s9
  have hlc := hL_ctx s
  have hsetup := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))
  have hrest := s7.seq (s9.seq (s10.seq s11))
  have hmul :
      N s * (B s + 1000 * W s + 100 * L_ctx s + 10 * L_elem s + 2400) +
        9 * (N s * (2 * L_elem s + 2)) ≤
      N s * (B s + 1000 * W s + 100 * L_ctx s + 50 * L_elem s + 2500) := by
    nlinarith
  refine ⟨_, ?_, hsetup.seq hrest⟩
  omega

/-- **Signed-Counter Summation Combinator (`bmSumRangeSigned termM`)**:
Consumes `encPair (encPair encCtx encUnary) encUnary ((ctx, W), N)` on `kIO` (`1 ≤ W`, `N < 2 ^ W`)
and computes `encodeSignedWord W (∑ i ∈ Finset.range N, fn ctx i)` in
$O(N \cdot (B_{\text{term}} + W + L_{\text{ctx}}))$ steps. -/
def bmSumRangeSigned (termM : BitMachine) : BitMachine :=
  let bmInit := bmFanout bmId (bmSeq (bmSeq bmFst bmSnd) bmSignedZero)
  let bmBody := bmSeq (bmFanout bmSnd (bmSeq bmFst termM)) bmSignedAdd
  bmSeq bmInit (bmIterLoopSigned bmBody)

theorem StageEval.sumRangeSigned {S : Type} {termM : BitMachine}
    {uCtx : S → List Bool} {W N : S → ℕ} {fn : S → ℕ → ℤ}
    {B L_ctx : S → ℕ}
    (hW : ∀ s, 1 ≤ W s)
    (hN : ∀ s, N s < 2 ^ W s)
    (hterm : ∀ (i : ℕ),
      StageEval (S := { s : S // i < N s }) termM
        (encDepPair (encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val)))
          (fun s => encodeSignedWord (W s.val) (i : ℤ)))
        (fun s => encodeSignedWord (W s.val) (fn s.val i))
        (fun s => B s.val))
    (hfits_term : ∀ (s : S) (i : ℕ), i < N s → FitsSignedWord (W s) (fn s i))
    (hfits_sum : ∀ (s : S) (i : ℕ), i ≤ N s →
      FitsSignedWord (W s) (∑ m ∈ Finset.range i, fn s m))
    (hL_ctx : ∀ s, (uCtx s).length ≤ L_ctx s) :
    StageEval (bmSumRangeSigned termM)
      (encDepPair (encDepPair uCtx (fun s => encUnary (W s))) (fun s => encUnary (N s)))
      (fun s => encodeSignedWord (W s) (∑ m ∈ Finset.range (N s), fn s m))
      (fun s =>
        N s * (B s + 2000 * W s + 200 * L_ctx s + 4500) +
        400 * L_ctx s + 700 * W s + 200 * N s + 1600) := by
  let uCW : S → List Bool := encDepPair uCtx (fun s => encUnary (W s))
  let uIn : S → List Bool := encDepPair uCW (fun s => encUnary (N s))
  let uSt : S → ℕ → List Bool := fun s i =>
    encodeSignedWord (W s) (∑ m ∈ Finset.range i, fn s m)
  have pZero : StageEval (bmSeq (bmSeq bmFst bmSnd) bmSignedZero) uIn
      (fun s => uSt s 0) (fun s => 20 * L_ctx s + 40 * W s + 20 * N s + 100) := by
    have pW := StageEval.seq (StageEval.fst uCW (fun s => encUnary (N s)))
      (StageEval.snd uCtx (fun s => encUnary (W s)))
    have pZ := StageEval.congr_out (v2 := fun s => uSt s 0)
      (StageEval.seq pW (StageEval.signedZero W))
      (fun s => by simp [uSt])
    refine pZ.mono (fun s => ?_)
    dsimp only [uCW]
    simp only [length_encDepPair, length_encUnary]
    have hlc := hL_ctx s
    omega
  have pInit := StageEval.fanout (StageEval.id_stage uIn) pZero
  have pLoop := StageEval.iterLoopSigned (uCtx := uCtx) (W := W) (N := N) (uSt := uSt)
    (B := fun s => B s + 800 * W s + 60 * L_ctx s + 1600)
    (L_ctx := L_ctx) (L_st := fun s => W s + 1)
    hW hN
    (fun i => by
      let SubS := { s : S // i < N s }
      let uCWI : SubS → List Bool :=
        encDepPair (encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val)))
          (fun s => encodeSignedWord (W s.val) (i : ℤ))
      let uAcc : SubS → List Bool := fun s => uSt s.val i
      have pPair := StageEval.fanout (StageEval.snd uCWI uAcc)
        (StageEval.seq (StageEval.fst uCWI uAcc) (hterm i))
      have pAdd : StageEval (S := SubS) bmSignedAdd
          (encDepPair uAcc (fun s => encodeSignedWord (W s.val) (fn s.val i)))
          (fun s => uSt s.val (i + 1))
          (fun s => 580 * W s.val + 1300) := by
        intro s' u2 u3 u4 u5 uSc
        have hi : i < N s'.val := s'.property
        rcases bmSignedAdd_computesInTime (W s'.val)
          (∑ m ∈ Finset.range i, fn s'.val m) (fn s'.val i)
          (hfits_sum s'.val i (le_of_lt hi)) (hfits_term s'.val i hi)
          (by simpa [Finset.sum_range_succ] using hfits_sum s'.val (i + 1) hi)
          u2 u3 u4 u5 uSc with ⟨t, ht, hc⟩
        simpa [uSt, Finset.sum_range_succ] using ⟨t, ht, hc⟩
      refine (StageEval.seq pPair pAdd).mono (fun s' => ?_)
      dsimp only [uCWI, uAcc, uSt]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      have hlc := hL_ctx s'.val
      omega)
    hL_ctx
    (fun s i _ => by simp [uSt])
  refine (StageEval.seq pInit pLoop).mono (fun s => ?_)
  dsimp only [uIn, uCW, uSt]
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
  have hlc := hL_ctx s
  have hmul :
      N s * (B s + 800 * W s + 60 * L_ctx s + 1600 + 1000 * W s + 100 * L_ctx s + 20 * (W s + 1) + 2500) ≤
      N s * (B s + 2000 * W s + 200 * L_ctx s + 4500) :=
    Nat.mul_le_mul_left (N s) (by omega)
  omega

/-- **Signed-Counter Recurrence + Summation Combinator (`bmRecurrenceSumSigned stepM termM`)**:
Consumes `encPair (encPair (encPair encCtx encUnary) encUnary) (encodeSignedWord W) (((ctx, W), M), T_0)`
on `kIO` (`1 ≤ W`, `M + 1 < 2 ^ W`) and computes
`encodeSignedWord W (∑ m ∈ Finset.range (M + 1), term ctx m ((buildRecurrenceArray T_0 (step ctx) M).1.getD m 0))`
in a single pass of `M` steps with **zero** array allocation or quadratic indexing overhead. -/
def bmRecurrenceSumSigned (stepM termM : BitMachine) : BitMachine :=
  let bmCW := bmSeq bmFst bmFst
  let bmW := bmSeq bmCW bmSnd
  let bmZeroIdx := bmSeq bmW bmSignedZero
  let bmTerm0 := bmSeq (bmFanout bmCW (bmFanout bmZeroIdx bmSnd)) termM
  let bmInit := bmFanout bmFst (bmFanout bmSnd bmTerm0)
  let bmNextT :=
    bmSeq
      (bmFanout (bmSeq bmFst bmFst) (bmFanout (bmSeq bmFst bmSnd) (bmSeq bmSnd bmFst)))
      stepM
  let bmNextIdx := bmSeq (bmSeq bmFst bmSnd) bmSignedSucc
  let bmBody :=
    bmSeq (bmFanout bmId bmNextT)
      (bmFanout bmSnd
        (bmSeq
          (bmFanout
            (bmSeq (bmSeq bmFst bmSnd) bmSnd)
            (bmSeq
              (bmFanout
                (bmSeq (bmSeq bmFst bmFst) bmFst)
                (bmFanout (bmSeq bmFst bmNextIdx) bmSnd))
              termM))
          bmSignedAdd))
  bmSeq bmInit (bmSeq (bmIterLoopSigned bmBody) bmSnd)

theorem sum_range_getD_buildRecurrenceArray_eq (T_0 : ℤ) (step term : ℕ → ℤ → ℤ) (M : ℕ) :
    (∑ m ∈ Finset.range (M + 1),
      term m ((buildRecurrenceArray T_0 step M).1.getD m 0)) =
    ∑ m ∈ Finset.range (M + 1),
      term m (buildRecurrenceArray T_0 step m).2 := by
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm_le : m ≤ M := by
    rw [Finset.mem_range] at hm; omega
  rw [getD_default_buildRecurrenceArray T_0 0 step hm_le]

theorem StageEval.recurrenceSumSigned {S : Type} {stepM termM : BitMachine}
    {uCtx : S → List Bool} {W M : S → ℕ} {T_0 : S → ℤ}
    {step term : S → ℕ → ℤ → ℤ}
    {B_step B_term L_ctx : S → ℕ}
    (hW : ∀ s, 1 ≤ W s)
    (hM : ∀ s, M s + 1 < 2 ^ W s)
    (hstep : ∀ (m : ℕ),
      StageEval (S := { s : S // m < M s }) stepM
        (encDepPair
          (encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val)))
          (encDepPair
            (fun s => encodeSignedWord (W s.val) (m : ℤ))
            (fun s => encodeSignedWord (W s.val)
              (buildRecurrenceArray (T_0 s.val) (step s.val) m).2)))
        (fun s => encodeSignedWord (W s.val)
          (step s.val m (buildRecurrenceArray (T_0 s.val) (step s.val) m).2))
        (fun s => B_step s.val))
    (hterm : ∀ (m : ℕ),
      StageEval (S := { s : S // m ≤ M s }) termM
        (encDepPair
          (encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val)))
          (encDepPair
            (fun s => encodeSignedWord (W s.val) (m : ℤ))
            (fun s => encodeSignedWord (W s.val)
              (buildRecurrenceArray (T_0 s.val) (step s.val) m).2)))
        (fun s => encodeSignedWord (W s.val)
          (term s.val m (buildRecurrenceArray (T_0 s.val) (step s.val) m).2))
        (fun s => B_term s.val))
    (hfits_term : ∀ (s : S) (m : ℕ), m ≤ M s →
      FitsSignedWord (W s) (term s m (buildRecurrenceArray (T_0 s) (step s) m).2))
    (hfits_sum : ∀ (s : S) (m : ℕ), m ≤ M s →
      FitsSignedWord (W s)
        (∑ j ∈ Finset.range (m + 1), term s j (buildRecurrenceArray (T_0 s) (step s) j).2))
    (hL_ctx : ∀ s, (uCtx s).length ≤ L_ctx s) :
    StageEval (bmRecurrenceSumSigned stepM termM)
      (encDepPair
        (encDepPair (encDepPair uCtx (fun s => encUnary (W s))) (fun s => encUnary (M s)))
        (fun s => encodeSignedWord (W s) (T_0 s)))
      (fun s => encodeSignedWord (W s)
        (∑ m ∈ Finset.range (M s + 1),
          term s m ((buildRecurrenceArray (T_0 s) (step s) (M s)).1.getD m 0)))
      (fun s =>
        (M s + 1) * (B_step s + B_term s + 4500 * W s + 800 * L_ctx s + 10000) +
        1000 * L_ctx s + 1500 * W s + 400 * M s + 5000) := by
  let uCW : S → List Bool := encDepPair uCtx (fun s => encUnary (W s))
  let uCWM : S → List Bool := encDepPair uCW (fun s => encUnary (M s))
  let uT : S → ℕ → List Bool := fun s m =>
    encodeSignedWord (W s) (buildRecurrenceArray (T_0 s) (step s) m).2
  let uSum : S → ℕ → List Bool := fun s m =>
    encodeSignedWord (W s)
      (∑ j ∈ Finset.range (m + 1), term s j (buildRecurrenceArray (T_0 s) (step s) j).2)
  let uSt : S → ℕ → List Bool := fun s m => encDepPair (fun s' => uT s' m) (fun s' => uSum s' m) s
  let uIn : S → List Bool := encDepPair uCWM (fun s => uT s 0)
  have pCW := StageEval.seq (StageEval.fst uCWM (fun s => uT s 0))
    (StageEval.fst uCW (fun s => encUnary (M s)))
  have pW := StageEval.seq pCW (StageEval.snd uCtx (fun s => encUnary (W s)))
  have pZeroIdx : StageEval (bmSeq (bmSeq (bmSeq bmFst bmFst) bmSnd) bmSignedZero)
      uIn (fun s => encodeSignedWord (W s) ((0 : ℕ) : ℤ))
      (fun s => 30 * L_ctx s + 50 * W s + 20 * M s + 100) := by
    refine (StageEval.congr_out
      (v2 := fun s => encodeSignedWord (W s) ((0 : ℕ) : ℤ))
      (StageEval.seq pW (StageEval.signedZero W)) (fun _ => rfl)).mono (fun s => ?_)
    dsimp only [uCWM, uCW, uT]
    simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
    have hlc := hL_ctx s
    omega
  have pTerm0 : StageEval
      (bmSeq (bmFanout (bmSeq bmFst bmFst)
        (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmFst) bmSnd) bmSignedZero) bmSnd)) termM)
      uIn (fun s => uSum s 0)
      (fun s => B_term s + 150 * L_ctx s + 250 * W s + 100 * M s + 600) := by
    have pArg := StageEval.fanout pCW (StageEval.fanout pZeroIdx (StageEval.snd uCWM (fun s => uT s 0)))
    have pT0 : StageEval (S := S) termM
        (encDepPair uCW (encDepPair (fun s => encodeSignedWord (W s) ((0 : ℕ) : ℤ)) (fun s => uT s 0)))
        (fun s => uSum s 0) B_term := by
      intro s' u2 u3 u4 u5 uSc
      simpa [uSum, uT, uCW] using hterm 0 ⟨s', Nat.zero_le _⟩ u2 u3 u4 u5 uSc
    refine (StageEval.seq pArg pT0).mono (fun s => ?_)
    dsimp only [uIn, uCWM, uCW, uT, uSum]
    simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
    have hlc := hL_ctx s
    omega
  have pInit := StageEval.fanout (StageEval.fst uCWM (fun s => uT s 0))
    (StageEval.fanout (StageEval.snd uCWM (fun s => uT s 0)) pTerm0)
  have pLoop := StageEval.iterLoopSigned (uCtx := uCtx) (W := W) (N := M) (uSt := uSt)
    (B := fun s => B_step s + B_term s + 3000 * W s + 600 * L_ctx s + 7000)
    (L_ctx := L_ctx) (L_st := fun s => 4 * W s + 8)
    hW (fun s => lt_trans (Nat.lt_succ_self _) (hM s))
    (fun m => by
      let SubS := { s : S // m < M s }
      let uCW' : SubS → List Bool := encDepPair (fun s => uCtx s.val) (fun s => encUnary (W s.val))
      let uIdx : SubS → List Bool := fun s => encodeSignedWord (W s.val) (m : ℤ)
      let uIdx1 : SubS → List Bool := fun s => encodeSignedWord (W s.val) ((m + 1 : ℕ) : ℤ)
      let uCWI : SubS → List Bool := encDepPair uCW' uIdx
      let uTm : SubS → List Bool := fun s => uT s.val m
      let uTm1 : SubS → List Bool := fun s => uT s.val (m + 1)
      let uSm : SubS → List Bool := fun s => uSum s.val m
      let uStm : SubS → List Bool := encDepPair uTm uSm
      let uBIn : SubS → List Bool := encDepPair uCWI uStm
      have pNextT := StageEval.seq
        (StageEval.fanout
          (StageEval.seq (StageEval.fst uCWI uStm) (StageEval.fst uCW' uIdx))
          (StageEval.fanout
            (StageEval.seq (StageEval.fst uCWI uStm) (StageEval.snd uCW' uIdx))
            (StageEval.seq (StageEval.snd uCWI uStm) (StageEval.fst uTm uSm))))
        (hstep m)
      have pWithT := StageEval.fanout (StageEval.id_stage uBIn) pNextT
      have pSucc : StageEval (S := SubS) bmSignedSucc uIdx uIdx1
          (fun s => 800 * W s.val + 2000) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m < M s'.val := s'.property
        have hM' : M s'.val + 1 < 2 ^ W s'.val := hM s'.val
        have hf0 : FitsSignedWord (W s'.val) (m : ℤ) := by
          rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        have hf1 : FitsSignedWord (W s'.val) ((m : ℤ) + 1) := by
          have : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
          rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        rcases bmSignedSucc_computesInTime (W s'.val) (hW s'.val) (m : ℤ) hf0 hf1 u2 u3 u4 u5 uSc
          with ⟨t, ht, hc⟩
        have hcast1 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
        rw [hcast1] at hc
        exact ⟨t, ht, hc⟩
      have pNextIdx := StageEval.seq
        (StageEval.seq (StageEval.fst uCWI uStm) (StageEval.snd uCW' uIdx)) pSucc
      have pTerm1Sub : StageEval (S := SubS) termM
          (encDepPair uCW' (encDepPair uIdx1 uTm1))
          (fun s => encodeSignedWord (W s.val)
            (term s.val (m + 1) (buildRecurrenceArray (T_0 s.val) (step s.val) (m + 1)).2))
          (fun s => B_term s.val) := by
        intro s' u2 u3 u4 u5 uSc
        exact hterm (m + 1) ⟨s'.val, s'.property⟩ u2 u3 u4 u5 uSc
      have pTerm1 := StageEval.seq
        (StageEval.fanout
          (StageEval.seq (StageEval.seq (StageEval.fst uBIn uTm1) (StageEval.fst uCWI uStm))
            (StageEval.fst uCW' uIdx))
          (StageEval.fanout
            (StageEval.seq (StageEval.fst uBIn uTm1) pNextIdx)
            (StageEval.snd uBIn uTm1)))
        pTerm1Sub
      have pPrevSum := StageEval.seq
        (StageEval.seq (StageEval.fst uBIn uTm1) (StageEval.snd uCWI uStm))
        (StageEval.snd uTm uSm)
      have pAddSub : StageEval (S := SubS) bmSignedAdd
          (encDepPair uSm (fun s => encodeSignedWord (W s.val)
            (term s.val (m + 1) (buildRecurrenceArray (T_0 s.val) (step s.val) (m + 1)).2)))
          (fun s => uSum s.val (m + 1))
          (fun s => 580 * W s.val + 1300) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m < M s'.val := s'.property
        rcases bmSignedAdd_computesInTime (W s'.val)
          (∑ j ∈ Finset.range (m + 1), term s'.val j (buildRecurrenceArray (T_0 s'.val) (step s'.val) j).2)
          (term s'.val (m + 1) (buildRecurrenceArray (T_0 s'.val) (step s'.val) (m + 1)).2)
          (hfits_sum s'.val m (le_of_lt hm'))
          (hfits_term s'.val (m + 1) hm')
          (by simpa [Finset.sum_range_succ] using hfits_sum s'.val (m + 1) hm')
          u2 u3 u4 u5 uSc with ⟨t, ht, hc⟩
        have hsum_eq : uSum s'.val (m + 1) =
            encodeSignedWord (W s'.val)
              ((∑ j ∈ Finset.range (m + 1), term s'.val j (buildRecurrenceArray (T_0 s'.val) (step s'.val) j).2) +
                term s'.val (m + 1) (buildRecurrenceArray (T_0 s'.val) (step s'.val) (m + 1)).2) := by
          dsimp only [uSum]
          rw [Finset.sum_range_succ]
        dsimp only [id]
        rw [hsum_eq]
        exact ⟨t, ht, hc⟩
      have pNextSum := StageEval.seq (StageEval.fanout pPrevSum pTerm1) pAddSub
      have pBody := StageEval.seq pWithT (StageEval.fanout (StageEval.snd uBIn uTm1) pNextSum)
      refine pBody.mono (fun s' => ?_)
      dsimp only [uBIn, uCWI, uCW', uIdx, uIdx1, uStm, uTm, uTm1, uSm, uT, uSum]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      have hlc := hL_ctx s'.val
      omega)
    hL_ctx
    (fun s m _ => by
      dsimp only [uSt, uT, uSum]
      simp only [length_encDepPair, length_encodeSignedWord]
      omega)
  have pAll := StageEval.congr_out
    (v2 := fun s => encodeSignedWord (W s)
      (∑ m ∈ Finset.range (M s + 1),
        term s m ((buildRecurrenceArray (T_0 s) (step s) (M s)).1.getD m 0)))
    (StageEval.seq pInit
      (StageEval.seq pLoop
        (StageEval.snd (fun s => uT s (M s)) (fun s => uSum s (M s)))))
    (fun s => by
      dsimp only [uSum]
      rw [sum_range_getD_buildRecurrenceArray_eq])
  refine pAll.mono (fun s => ?_)
  dsimp only [uIn, uCWM, uCW, uT, uSum, uSt]
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
  have hlc := hL_ctx s
  nlinarith

/-! ## 4. Pure-Integer Taylor Series & Schedule Entry Stages (`bmApproxLogTwo`, `bmApproxPi`,
`bmExpTwoPiIWith`, `bmSincTaylorWith`, `bmExpTaylorWith`, `bmFilterTapEntryWith`,
`bmErfTaylorWith`, `bmGHatEntryWith`) -/

theorem StageEval.unaryConst {S : Type} (c : ℕ) (u : S → List Bool) :
    StageEval (bmUnaryConst c) u (fun _ => encUnary c)
      (fun s => (u s).length + c + 2) :=
  StageEval.of_computesStageLe (bmUnaryConst_computesStageLe c id) u

/-- **Width-Unifying Rounded Division (`bmRoundDivResize`)**:
Consumes `encPair encUnary (encPair (encodeSignedWord W1) (encodeSignedWord W2)) (WOut, (num, den))`
on `kIO`, resizes both `num` and `den` to their sum width `W1 + W2` (which is unconditionally
`≥ W1` and `≥ W2`), runs `bmRoundDivInt`, and resizes the quotient to `WOut`. -/
def bmRoundDivResize : BitMachine :=
  let bmWOut := bmFst
  let bmNum := bmSeq bmSnd bmFst
  let bmDen := bmSeq bmSnd bmSnd
  let bmW1 := bmSeq bmNum bmSignedWidth
  let bmW2 := bmSeq bmDen bmSignedWidth
  let bmW12 := bmSeq (bmFanout bmW1 bmW2) bmUnaryAdd
  let bmNum12 := bmSeq (bmFanout bmW12 bmNum) bmResizeSignedWord
  let bmDen12 := bmSeq (bmFanout bmW12 bmDen) bmResizeSignedWord
  let bmQuo12 := bmSeq (bmFanout bmNum12 bmDen12) bmRoundDivInt
  bmSeq (bmFanout bmWOut bmQuo12) bmResizeSignedWord

theorem bmRoundDivResize_computesInTime (WOut W1 W2 : ℕ) (num den : ℤ)
    (hnum : FitsSignedWord W1 num) (hden : FitsSignedWord W2 den)
    (hout : FitsSignedWord WOut (roundDivInt num den))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 300 * (W1 + W2) * (W1 + W2) + 80000 * (W1 + W2) + 4000 * WOut + 200000,
      bmRoundDivResize.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair (encodeSignedWord W1) (encodeSignedWord W2))
            (WOut, (num, den))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord WOut (roundDivInt num den)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uND : S → List Bool :=
    encDepPair (fun _ => encodeSignedWord W1 num) (fun _ => encodeSignedWord W2 den)
  let uIn : S → List Bool := encDepPair (fun _ => encUnary WOut) uND
  have hnum12 : FitsSignedWord (W1 + W2) num := hnum.mono (Nat.le_add_right W1 W2)
  have hden12 : FitsSignedWord (W1 + W2) den := hden.mono (Nat.le_add_left W2 W1)
  have hquo12 : FitsSignedWord (W1 + W2) (roundDivInt num den) := hnum12.roundDivInt den
  have pWOut := StageEval.fst (fun _ : S => encUnary WOut) uND
  have pND := StageEval.snd (fun _ : S => encUnary WOut) uND
  have pNum := StageEval.seq pND
    (StageEval.fst (fun _ : S => encodeSignedWord W1 num) (fun _ : S => encodeSignedWord W2 den))
  have pDen := StageEval.seq pND
    (StageEval.snd (fun _ : S => encodeSignedWord W1 num) (fun _ : S => encodeSignedWord W2 den))
  have pW1 := StageEval.seq pNum
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W1) (fun _ : S => num))
  have pW2 := StageEval.seq pDen
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W2) (fun _ : S => den))
  have pW12 := StageEval.seq (StageEval.fanout pW1 pW2)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (W1, W2)))
  have pNum12 := StageEval.seq (StageEval.fanout pW12 pNum)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W1 (W1 + W2) num hnum hnum12))
  have pDen12 := StageEval.seq (StageEval.fanout pW12 pDen)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime W2 (W1 + W2) den hden hden12))
  have pQuo12 := StageEval.seq (StageEval.fanout pNum12 pDen12)
    (StageEval.const (S := S) (bmRoundDivInt_computesInTime (W1 + W2) num den hnum12 hden12))
  have hall := StageEval.seq (StageEval.fanout pWOut pQuo12)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime (W1 + W2) WOut (roundDivInt num den) hquo12 hout))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uND, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

theorem StageEval.roundDivResize {S : Type} (WOut W1 W2 : S → ℕ) (num den : S → ℤ)
    (hnum : ∀ s, FitsSignedWord (W1 s) (num s))
    (hden : ∀ s, FitsSignedWord (W2 s) (den s))
    (hout : ∀ s, FitsSignedWord (WOut s) (roundDivInt (num s) (den s))) :
    StageEval bmRoundDivResize
      (encDepPair (fun s => encUnary (WOut s))
        (encDepPair (fun s => encodeSignedWord (W1 s) (num s))
          (fun s => encodeSignedWord (W2 s) (den s))))
      (fun s => encodeSignedWord (WOut s) (roundDivInt (num s) (den s)))
      (fun s => 300 * (W1 s + W2 s) * (W1 s + W2 s) +
        80000 * (W1 s + W2 s) + 4000 * WOut s + 200000) := by
  intro s tW2 tW3 tW4 tW5 tSch
  exact bmRoundDivResize_computesInTime (WOut s) (W1 s) (W2 s) (num s) (den s)
    (hnum s) (hden s) (hout s) tW2 tW3 tW4 tW5 tSch

/-- **Fixed-Width Signed Multiplication (`bmSignedMulSameWith bmMul`)**:
Consumes `encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)` on `kIO` and emits
`encodeSignedWord W (x * y)` when `FitsSignedWord W x`, `FitsSignedWord W y`, and
`FitsSignedWord W (x * y)`. -/
def bmSignedMulSameWith (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmFanout (bmSeq bmFst bmSignedWidth) (bmSignedMulWith bmMul)) bmResizeSignedWord

theorem bmSignedMulSameWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W : ℕ) (x y : ℤ) (hx : FitsSignedWord W x) (hy : FitsSignedWord W y)
    (hxy : FitsSignedWord W (x * y))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * mulTime W + 12000 * W + 25000,
      (bmSignedMulSameWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encodeSignedWord W) (encodeSignedWord W) (x, y)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (x * y)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool :=
    encDepPair (fun _ => encodeSignedWord W x) (fun _ => encodeSignedWord W y)
  have hxy2 : FitsSignedWord (2 * W) (x * y) := by
    simpa [Nat.two_mul] using hx.mul hy
  have pW := StageEval.seq
    (StageEval.fst (fun _ : S => encodeSignedWord W x) (fun _ : S => encodeSignedWord W y))
    (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ : S => x))
  have pProd := StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W x y hx hy)
  have hall := StageEval.seq (StageEval.fanout pW pProd)
    (StageEval.const (S := S) (bmResizeSignedWord_computesInTime (2 * W) W (x * y) hxy2 hxy))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

theorem StageEval.signedMulSameWith {S : Type} {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W : S → ℕ) (x y : S → ℤ)
    (hx : ∀ s, FitsSignedWord (W s) (x s))
    (hy : ∀ s, FitsSignedWord (W s) (y s))
    (hxy : ∀ s, FitsSignedWord (W s) (x s * y s)) :
    StageEval (bmSignedMulSameWith bmMul)
      (encDepPair (fun s => encodeSignedWord (W s) (x s))
        (fun s => encodeSignedWord (W s) (y s)))
      (fun s => encodeSignedWord (W s) (x s * y s))
      (fun s => 2 * mulTime (W s) + 12000 * W s + 25000) := by
  intro s tW2 tW3 tW4 tW5 tSch
  exact bmSignedMulSameWith_computesInTime hmul (W s) (x s) (y s)
    (hx s) (hy s) (hxy s) tW2 tW3 tW4 tW5 tSch

/-! ### 4.1 Pure-Integer $\ln 2$ Series (`bmApproxLogTwo`) -/

theorem roundShiftInt_two_mul (x : ℤ) : roundShiftInt (2 * x) 1 = x := by
  unfold roundShiftInt
  simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_self, pow_zero, pow_one]
  have h : 2 * x + 1 = 1 + x * 2 := by ring
  rw [h, Int.add_mul_ediv_right 1 x (by decide)]
  omega

theorem buildRecurrenceArray_logTwoPow_snd (q_acc : ℕ) :
    ∀ i : ℕ, i + 1 ≤ q_acc →
      (buildRecurrenceArray ((2 : ℤ) ^ (q_acc - 1))
        (fun _ T => roundShiftInt T 1) i).2 = (2 : ℤ) ^ (q_acc - (i + 1))
  | 0, _ => rfl
  | i + 1, hi => by
    simp only [buildRecurrenceArray]
    rw [buildRecurrenceArray_logTwoPow_snd q_acc i (by omega)]
    have hpow : (2 : ℤ) ^ (q_acc - (i + 1)) = 2 * (2 : ℤ) ^ (q_acc - (i + 2)) := by
      conv_lhs => rw [show q_acc - (i + 1) = (q_acc - (i + 2)) + 1 by omega, pow_succ']
    rw [hpow, roundShiftInt_two_mul]

theorem approxLogTwoTermFixed_nonneg (q_acc i : ℕ) :
    0 ≤ approxLogTwoTermFixed q_acc i := by
  unfold approxLogTwoTermFixed
  rw [roundDivInt_eq_floor_div_add_half]
  exact Int.floor_nonneg.mpr (by positivity)

theorem sum_range_approxLogTwoTermFixed_le (S m : ℕ) (hm : m ≤ S + 1) :
    ∑ j ∈ Finset.range (m + 1), approxLogTwoTermFixed (S + (S + 2)) j ≤
      approxLogTwoFixed S := by
  unfold approxLogTwoFixed
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => approxLogTwoTermFixed_nonneg _ i)
  intro j hj
  rw [Finset.mem_range] at hj ⊢
  omega

/-- **Pure-Integer $\ln 2$ Series Stage (`bmApproxLogTwo`)**:
Consumes `encPair encUnary encUnary (W, S)` on `kIO` (`2 * S + 4 ≤ W`) and emits
`encodeSignedWord W (approxLogTwoFixed S)` in $O((S + 1) \cdot W^2)$ `TM2.step` transitions. -/
def bmApproxLogTwo : BitMachine :=
  let bmW := bmFst
  let bmS := bmSnd
  let bmS1 := bmSeq bmS bmUnarySucc
  let bmS2 := bmSeq bmS1 bmUnarySucc
  let bmQAcc := bmSeq (bmFanout bmS bmS2) bmUnaryAdd
  let bmQAccPred := bmSeq bmQAcc bmUnaryPred
  let bmT0 := bmSeq (bmFanout bmW bmQAccPred) bmSignedTwoPow
  let bmCtxW := bmFanout (bmUnaryConst 0) bmW
  let bmHeader := bmFanout (bmFanout bmCtxW bmS1) bmT0
  let bmStep := bmSeq (bmSeq bmSnd bmSnd) bmHalfRoundedSigned
  let bmTerm :=
    bmSeq
      (bmFanout (bmSeq bmSnd bmSnd) (bmSeq (bmSeq bmSnd bmFst) bmSignedSucc))
      bmRoundDivInt
  bmSeq bmHeader (bmRecurrenceSumSigned bmStep bmTerm)

theorem bmApproxLogTwo_computesInTime (W S : ℕ) (hW : 2 * S + 4 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (S + 2) * (250 * W * W + 80000 * W + 200000) + 10000 * W + 50000,
      bmApproxLogTwo.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (W, S)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (approxLogTwoFixed S)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let St := Unit
  let q_acc : ℕ := S + (S + 2)
  let uIn : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary S)
  have pW := StageEval.fst (fun _ : St => encUnary W) (fun _ => encUnary S)
  have pS := StageEval.snd (fun _ : St => encUnary W) (fun _ => encUnary S)
  have pS1 := StageEval.seq pS
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => S))
  have pS2 := StageEval.seq pS1
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => S + 1))
  have pQAcc := StageEval.seq (StageEval.fanout pS pS2)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (S, S + 2)))
  have pQAccPred := StageEval.seq pQAcc
    (StageEval.of_computesStageLe bmUnaryPred_computesStageLe (fun _ : St => q_acc))
  have hqp_lt : q_acc - 1 < W := by dsimp [q_acc]; omega
  have pT0 := StageEval.seq (StageEval.fanout pW pQAccPred)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W (q_acc - 1) (by omega) hqp_lt))
  have pCtx := StageEval.unaryConst 0 uIn
  have pHeader := StageEval.fanout (StageEval.fanout (StageEval.fanout pCtx pW) pS1) pT0
  have hS1_pow : S + 1 + 1 < 2 ^ W :=
    lt_of_le_of_lt (by omega : S + 2 ≤ W) Nat.lt_two_pow_self
  have hRec := StageEval.recurrenceSumSigned
    (S := St)
    (uCtx := fun _ => encUnary 0)
    (W := fun _ => W)
    (M := fun _ => S + 1)
    (T_0 := fun _ => (2 : ℤ) ^ (q_acc - 1))
    (step := fun _ _ T => roundShiftInt T 1)
    (term := fun _ i T => roundDivInt T ((i + 1 : ℕ) : ℤ))
    (B_step := fun _ => 5100 * W + 25000)
    (B_term := fun _ => 250 * W * W + 62000 * W + 155000)
    (L_ctx := fun _ => 1)
    (fun _ => by omega)
    (fun _ => hS1_pow)
    (fun m => by
      let SubS := { s : St // m < S + 1 }
      by_cases hm_lt : m < S + 1
      · let uCW : SubS → List Bool := encDepPair (fun _ => encUnary 0) (fun _ => encUnary W)
        let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
        let uTm : SubS → List Bool := fun _ =>
          encodeSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ (q_acc - 1)) (fun _ T => roundShiftInt T 1) m).2
        have hm_le : m + 1 ≤ q_acc := by dsimp [q_acc]; omega
        have hTm_fits : FitsSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ (q_acc - 1)) (fun _ T => roundShiftInt T 1) m).2 := by
          rw [buildRecurrenceArray_logTwoPow_snd q_acc m hm_le]
          exact (FitsSignedWord.two_pow (q_acc - (m + 1))).mono (by dsimp [q_acc]; omega)
        have pGetTm := StageEval.seq (StageEval.snd uCW (encDepPair uIdx uTm))
          (StageEval.snd uIdx uTm)
        have pHalf := StageEval.const (S := SubS)
          (bmHalfRoundedSigned_computesInTime W _ hTm_fits)
        refine (StageEval.seq pGetTm pHalf).mono (fun _ => ?_)
        dsimp only [uCW, uIdx, uTm]
        simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
        omega
      · intro s'; exact False.elim (hm_lt s'.property))
    (fun m => by
      let SubS := { s : St // m ≤ S + 1 }
      let uCW : SubS → List Bool := encDepPair (fun _ => encUnary 0) (fun _ => encUnary W)
      let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
      let uTm : SubS → List Bool := fun _ =>
        encodeSignedWord W
          (buildRecurrenceArray ((2 : ℤ) ^ (q_acc - 1)) (fun _ T => roundShiftInt T 1) m).2
      have pPair := StageEval.snd uCW (encDepPair uIdx uTm)
      have pGetTm := StageEval.seq pPair (StageEval.snd uIdx uTm)
      have pGetIdx := StageEval.seq pPair (StageEval.fst uIdx uTm)
      have pIdx1 : StageEval (S := SubS) bmSignedSucc uIdx
          (fun _ => encodeSignedWord W ((m + 1 : ℕ) : ℤ))
          (fun _ => 800 * W + 2000) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m ≤ S + 1 := s'.property
        have hf0 : FitsSignedWord W (m : ℤ) := by
          rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        have hf1 : FitsSignedWord W ((m : ℤ) + 1) := by
          have : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
          rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        rcases bmSignedSucc_computesInTime W (by omega) (m : ℤ) hf0 hf1 u2 u3 u4 u5 uSc
          with ⟨t, ht, hc⟩
        have hcast : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
        rw [hcast] at hc
        exact ⟨t, ht, hc⟩
      have pDiv : StageEval (S := SubS) bmRoundDivInt
          (encDepPair uTm (fun _ => encodeSignedWord W ((m + 1 : ℕ) : ℤ)))
          (fun _ => encodeSignedWord W
            (roundDivInt
              (buildRecurrenceArray ((2 : ℤ) ^ (q_acc - 1)) (fun _ T => roundShiftInt T 1) m).2
              ((m + 1 : ℕ) : ℤ)))
          (fun _ => 250 * W * W + 60000 * W + 150000) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m ≤ S + 1 := s'.property
        have hm_le : m + 1 ≤ q_acc := by dsimp [q_acc]; omega
        have hTm_fits : FitsSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ (q_acc - 1)) (fun _ T => roundShiftInt T 1) m).2 := by
          rw [buildRecurrenceArray_logTwoPow_snd q_acc m hm_le]
          exact (FitsSignedWord.two_pow (q_acc - (m + 1))).mono (by dsimp [q_acc]; omega)
        have hf1 : FitsSignedWord W ((m + 1 : ℕ) : ℤ) := by
          rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        exact bmRoundDivInt_computesInTime W _ _ hTm_fits hf1 u2 u3 u4 u5 uSc
      refine (StageEval.seq (StageEval.fanout pGetTm (StageEval.seq pGetIdx pIdx1)) pDiv).mono
        (fun _ => ?_)
      dsimp only [uCW, uIdx, uTm]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega)
    (fun _ m hm => by
      have hm_le : m + 1 ≤ q_acc := by dsimp [q_acc]; omega
      rw [buildRecurrenceArray_logTwoPow_snd q_acc m hm_le]
      exact ((FitsSignedWord.two_pow (q_acc - (m + 1))).roundDivInt _).mono
        (by dsimp [q_acc]; omega))
    (fun _ m hm => by
      have hsum_eq :
          (∑ j ∈ Finset.range (m + 1),
            roundDivInt
              (buildRecurrenceArray ((2 : ℤ) ^ (q_acc - 1)) (fun _ T => roundShiftInt T 1) j).2
              ((j + 1 : ℕ) : ℤ)) =
          ∑ j ∈ Finset.range (m + 1), approxLogTwoTermFixed q_acc j := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        rw [buildRecurrenceArray_logTwoPow_snd q_acc j (by dsimp [q_acc]; omega)]
        rfl
      rw [hsum_eq]
      have hnn : 0 ≤ ∑ j ∈ Finset.range (m + 1), approxLogTwoTermFixed q_acc j :=
        Finset.sum_nonneg (fun j _ => approxLogTwoTermFixed_nonneg q_acc j)
      have hle : ∑ j ∈ Finset.range (m + 1), approxLogTwoTermFixed q_acc j ≤
          2 * (2 : ℤ) ^ q_acc :=
        (sum_range_approxLogTwoTermFixed_le S m hm).trans (approxLogTwoFixed_le S)
      unfold FitsSignedWord
      rw [abs_of_nonneg hnn]
      have hlt : 2 * (2 : ℤ) ^ q_acc < (2 : ℤ) ^ (2 * S + 4) := by
        have : (2 : ℤ) ^ (2 * S + 4) = 4 * (2 : ℤ) ^ q_acc := by
          rw [show 2 * S + 4 = q_acc + 2 by dsimp [q_acc]; omega, pow_add]; ring
        have hpos : (0 : ℤ) < (2 : ℤ) ^ q_acc := by positivity
        linarith
      exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt (pow_le_pow_right₀ (by decide) hW)))
    (fun _ => by simp [length_encUnary])
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W (approxLogTwoFixed S))
    (StageEval.seq pHeader hRec)
    (fun _ => by
      dsimp only [approxLogTwoFixed]
      congr 1
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mem_range] at hm
      rw [getD_default_buildRecurrenceArray _ 0 _ (by omega : m ≤ S + 1),
        buildRecurrenceArray_logTwoPow_snd q_acc m (by dsimp [q_acc]; omega)]
      rfl)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  have hqp_le : q_acc - 1 ≤ 2 * S + 1 := by dsimp [q_acc]; omega
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-! ### 4.2 Pure-Integer $\arctan(1/k)$ and Machin $\pi$ Series (`bmArctanInvTaylor`, `bmApproxPi`) -/

/-- **Pure-Integer $\arctan(1/k)$ Taylor Series Stage (`bmArctanInvTaylor`)**:
Consumes `encPair encUnary (encPair encUnary encUnary) (W, (N, k))` on `kIO`
(`1 ≤ k`, `k * k < 2 ^ W`, `5 * N + 10 ≤ W`) and emits
`encodeSignedWord W (arctanInvTaylorFixed N k)` in $O((N + 1) \cdot W^2 + k^2)$ `TM2.step` transitions. -/
def bmArctanInvTaylor : BitMachine :=
  let bmW := bmFst
  let bmN := bmSeq bmSnd bmFst
  let bmK := bmSeq bmSnd bmSnd
  let bmFourN := bmSeq (bmSeq bmN bmUnaryDouble) bmUnaryDouble
  let bmQAcc := bmSeq (bmFanout bmFourN (bmUnaryConst 6)) bmUnaryAdd
  let bmTwoPowQAcc := bmSeq (bmFanout bmW bmQAcc) bmSignedTwoPow
  let bmKSigned := bmSeq (bmFanout bmW bmK) bmUnaryToSigned
  let bmK2Unary := bmSeq (bmFanout bmK bmK) bmUnaryMul
  let bmK2Signed := bmSeq (bmFanout bmW bmK2Unary) bmUnaryToSigned
  let bmT0 := bmSeq (bmFanout bmTwoPowQAcc bmKSigned) bmRoundDivInt
  let bmCtxW := bmFanout bmK2Signed bmW
  let bmHeader := bmFanout (bmFanout bmCtxW bmN) bmT0
  let bmStep := bmSeq (bmFanout (bmSeq bmSnd bmSnd) (bmSeq bmFst bmFst)) bmRoundDivInt
  let bmMSigned := bmSeq bmSnd bmFst
  let bmPm := bmSeq bmSnd bmSnd
  let bmTwoM1 := bmSeq (bmSeq bmMSigned bmSignedDouble) bmSignedSucc
  let bmDiv := bmSeq (bmFanout bmPm bmTwoM1) bmRoundDivInt
  let bmTerm := bmSeq (bmFanout bmMSigned bmDiv) bmAltSignMulSigned
  bmSeq bmHeader (bmRecurrenceSumSigned bmStep bmTerm)

theorem bmArctanInvTaylor_computesInTime (W N k : ℕ)
    (hk1 : 1 ≤ k) (hk2 : k * k < 2 ^ W) (hW : 5 * N + 10 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (N + 1) * (500 * W * W + 150000 * W + 360000) +
        300 * W * W + 100000 * W + k * k * (2000 * W + 50 * k + 5000) + 300000,
      bmArctanInvTaylor.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair encUnary encUnary) (W, (N, k))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (arctanInvTaylorFixed N k)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let St := Unit
  let q_acc : ℕ := 2 * (2 * N) + 6
  have hq_eq : q_acc = 4 * N + 6 := by dsimp [q_acc]; omega
  let uNK : St → List Bool := encDepPair (fun _ => encUnary N) (fun _ => encUnary k)
  let uIn : St → List Bool := encDepPair (fun _ => encUnary W) uNK
  have hk_lt : k < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_self k) hk2
  have hk_fits : FitsSignedWord W (k : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact hk_lt
  have hk2_fits : FitsSignedWord W ((k * k : ℕ) : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact hk2
  have pW := StageEval.fst (fun _ : St => encUnary W) uNK
  have pNK := StageEval.snd (fun _ : St => encUnary W) uNK
  have pN := StageEval.seq pNK (StageEval.fst (fun _ : St => encUnary N) (fun _ => encUnary k))
  have pK := StageEval.seq pNK (StageEval.snd (fun _ : St => encUnary N) (fun _ => encUnary k))
  have pTwoN := StageEval.seq pN
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => N))
  have pFourN := StageEval.seq pTwoN
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * N))
  have pQAcc := StageEval.seq
    (StageEval.fanout pFourN (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (2 * (2 * N), 6)))
  have hq_lt : q_acc < W := by omega
  have pTwoPowQAcc := StageEval.seq (StageEval.fanout pW pQAcc)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W q_acc (by omega) hq_lt))
  have pKSigned := StageEval.seq (StageEval.fanout pW pK)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W k (by omega) hk_lt))
  have pK2Unary := StageEval.seq (StageEval.fanout pK pK)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (k, k)))
  have pK2Signed := StageEval.seq (StageEval.fanout pW pK2Unary)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W (k * k) (by omega) hk2))
  have h2q_fits : FitsSignedWord W ((2 : ℤ) ^ q_acc) :=
    (FitsSignedWord.two_pow q_acc).mono (by omega)
  have pT0 := StageEval.seq (StageEval.fanout pTwoPowQAcc pKSigned)
    (StageEval.const (S := St) (bmRoundDivInt_computesInTime W ((2 : ℤ) ^ q_acc) (k : ℤ)
      h2q_fits hk_fits))
  have pHeader := StageEval.fanout
    (StageEval.fanout (StageEval.fanout pK2Signed pW) pN) pT0
  have hN_pow : N + 1 < 2 ^ W :=
    lt_of_le_of_lt (by omega : N + 1 ≤ W) Nat.lt_two_pow_self
  have hPm_fits : ∀ m : ℕ,
      FitsSignedWord (q_acc + 2)
        (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
          (arctanInvPowStepFixed k) m).2 :=
    fitsSignedWord_buildRecurrenceArray_arctanInvPowStepFixed k q_acc
  have hterm_fits_q : ∀ m : ℕ,
      FitsSignedWord (q_acc + 2)
        (altSign m * roundDivInt
          (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
            (arctanInvPowStepFixed k) m).2
          ((2 * m + 1 : ℕ) : ℤ)) := by
    intro m
    have hd : FitsSignedWord (q_acc + 2)
        (roundDivInt
          (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
            (arctanInvPowStepFixed k) m).2
          ((2 * m + 1 : ℕ) : ℤ)) :=
      (hPm_fits m).roundDivInt _
    rcases altSign_eq_one_or_neg_one m with h1 | h1
    · rw [h1, one_mul]; exact hd
    · rw [h1, neg_one_mul]; exact hd.neg
  have hRec := StageEval.recurrenceSumSigned
    (S := St)
    (uCtx := fun _ => encodeSignedWord W ((k * k : ℕ) : ℤ))
    (W := fun _ => W)
    (M := fun _ => N)
    (T_0 := fun _ => roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
    (step := fun _ => arctanInvPowStepFixed k)
    (term := fun _ m P_m => altSign m * roundDivInt P_m ((2 * m + 1 : ℕ) : ℤ))
    (B_step := fun _ => 250 * W * W + 62000 * W + 155000)
    (B_term := fun _ => 250 * W * W + 70000 * W + 175000)
    (L_ctx := fun _ => 2 * W + 2)
    (fun _ => by omega)
    (fun _ => hN_pow)
    (fun m => by
      let SubS := { s : St // m < N }
      let uCW : SubS → List Bool :=
        encDepPair (fun _ => encodeSignedWord W ((k * k : ℕ) : ℤ)) (fun _ => encUnary W)
      let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
      let uPm : SubS → List Bool := fun _ =>
        encodeSignedWord W
          (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
            (arctanInvPowStepFixed k) m).2
      have pGetPm := StageEval.seq (StageEval.snd uCW (encDepPair uIdx uPm))
        (StageEval.snd uIdx uPm)
      have pGetK2 := StageEval.seq (StageEval.fst uCW (encDepPair uIdx uPm))
        (StageEval.fst (fun _ : SubS => encodeSignedWord W ((k * k : ℕ) : ℤ))
          (fun _ => encUnary W))
      have pDiv := StageEval.const (S := SubS)
        (bmRoundDivInt_computesInTime W _ _ ((hPm_fits m).mono (by omega)) hk2_fits)
      refine (StageEval.seq (StageEval.fanout pGetPm pGetK2) pDiv).mono (fun _ => ?_)
      dsimp only [uCW, uIdx, uPm]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega)
    (fun m => by
      let SubS := { s : St // m ≤ N }
      let uCW : SubS → List Bool :=
        encDepPair (fun _ => encodeSignedWord W ((k * k : ℕ) : ℤ)) (fun _ => encUnary W)
      let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
      let uPm : SubS → List Bool := fun _ =>
        encodeSignedWord W
          (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
            (arctanInvPowStepFixed k) m).2
      have pPair := StageEval.snd uCW (encDepPair uIdx uPm)
      have pGetIdx := StageEval.seq pPair (StageEval.fst uIdx uPm)
      have pGetPm := StageEval.seq pPair (StageEval.snd uIdx uPm)
      have pTwoM : StageEval (S := SubS) bmSignedDouble uIdx
          (fun _ => encodeSignedWord W (2 * (m : ℤ)))
          (fun _ => 600 * W + 1400) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m ≤ N := s'.property
        have hf0 : FitsSignedWord W (m : ℤ) := by
          rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
        have hf2 : FitsSignedWord W (2 * (m : ℤ)) := by
          have : 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) := by push_cast; rfl
          rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
          exact lt_of_le_of_lt (by omega : 2 * m ≤ W) Nat.lt_two_pow_self
        exact bmSignedDouble_computesInTime W (m : ℤ) hf0 hf2 u2 u3 u4 u5 uSc
      have pTwoM1 : StageEval (S := SubS) bmSignedSucc
          (fun _ => encodeSignedWord W (2 * (m : ℤ)))
          (fun _ => encodeSignedWord W ((2 * m + 1 : ℕ) : ℤ))
          (fun _ => 800 * W + 2000) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m ≤ N := s'.property
        have hf2 : FitsSignedWord W (2 * (m : ℤ)) := by
          have : 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) := by push_cast; rfl
          rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
          exact lt_of_le_of_lt (by omega : 2 * m ≤ W) Nat.lt_two_pow_self
        have hf21 : FitsSignedWord W (2 * (m : ℤ) + 1) := by
          have : 2 * (m : ℤ) + 1 = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; rfl
          rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
          exact lt_of_le_of_lt (by omega : 2 * m + 1 ≤ W) Nat.lt_two_pow_self
        rcases bmSignedSucc_computesInTime W (by omega) (2 * (m : ℤ)) hf2 hf21 u2 u3 u4 u5 uSc
          with ⟨t, ht, hc⟩
        have hcast : 2 * (m : ℤ) + 1 = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; rfl
        rw [hcast] at hc
        exact ⟨t, ht, hc⟩
      have pDen := StageEval.seq (StageEval.seq pGetIdx pTwoM) pTwoM1
      have pDiv : StageEval (S := SubS) bmRoundDivInt
          (encDepPair uPm (fun _ => encodeSignedWord W ((2 * m + 1 : ℕ) : ℤ)))
          (fun _ => encodeSignedWord W
            (roundDivInt
              (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
                (arctanInvPowStepFixed k) m).2
              ((2 * m + 1 : ℕ) : ℤ)))
          (fun _ => 250 * W * W + 60000 * W + 150000) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m ≤ N := s'.property
        have hf21 : FitsSignedWord W ((2 * m + 1 : ℕ) : ℤ) := by
          rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
          exact lt_of_le_of_lt (by omega : 2 * m + 1 ≤ W) Nat.lt_two_pow_self
        exact bmRoundDivInt_computesInTime W _ _ ((hPm_fits m).mono (by omega)) hf21
          u2 u3 u4 u5 uSc
      have pAlt : StageEval (S := SubS) bmAltSignMulSigned
          (encDepPair uIdx
            (fun _ => encodeSignedWord W
              (roundDivInt
                (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
                  (arctanInvPowStepFixed k) m).2
                ((2 * m + 1 : ℕ) : ℤ))))
          (fun _ => encodeSignedWord W
            (altSign m * roundDivInt
              (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
                (arctanInvPowStepFixed k) m).2
              ((2 * m + 1 : ℕ) : ℤ)))
          (fun _ => 800 * W + 2000) := by
        intro s' u2 u3 u4 u5 uSc
        have hm' : m ≤ N := s'.property
        have hm_pow : m < 2 ^ W :=
          lt_of_le_of_lt (by omega : m ≤ W) Nat.lt_two_pow_self
        have hd_fits : FitsSignedWord W
            (roundDivInt
              (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
                (arctanInvPowStepFixed k) m).2
              ((2 * m + 1 : ℕ) : ℤ)) :=
          ((hPm_fits m).roundDivInt _).mono (by omega)
        exact bmAltSignMulSigned_computesInTime W m (by omega) hm_pow _ hd_fits u2 u3 u4 u5 uSc
      refine (StageEval.seq (StageEval.fanout pGetIdx (StageEval.seq (StageEval.fanout pGetPm pDen) pDiv)) pAlt).mono
        (fun _ => ?_)
      dsimp only [uCW, uIdx, uPm]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega)
    (fun _ m _ => (hterm_fits_q m).mono (by omega))
    (fun _ m hm => by
      have hm1_pow : m + 1 ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
      have hsum := fitsSignedWord_sum_range (m + 1) hm1_pow
        (fun j => altSign j * roundDivInt
          (buildRecurrenceArray (roundDivInt ((2 : ℤ) ^ q_acc) (k : ℤ))
            (arctanInvPowStepFixed k) j).2
          ((2 * j + 1 : ℕ) : ℤ))
        (fun j _ => hterm_fits_q j)
      exact hsum.mono (by omega))
    (fun _ => by simp [length_encodeSignedWord]; omega)
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W (arctanInvTaylorFixed N k))
    (StageEval.seq pHeader hRec)
    (fun _ => by
      unfold arctanInvTaylorFixed arctanInvPowArrayFixed
      dsimp only
      rw [← hq_eq])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uNK, q_acc, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  have hk_le : k ≤ k * k := Nat.le_mul_self k
  have hmulN :
      (N + 1) * (250 * W * W + 62000 * W + 155000 + (250 * W * W + 70000 * W + 175000) +
        4500 * W + 800 * (2 * W + 2) + 10000) ≤
      (N + 1) * (500 * W * W + 150000 * W + 360000) :=
    Nat.mul_le_mul_left (N + 1) (by nlinarith)
  have hkW_le : k * (800 * W + 2010) ≤ k * k * (800 * W + 2010) :=
    Nat.mul_le_mul_right (800 * W + 2010) hk_le
  have hk3_eq : 40 * k * k * k = (k * k) * (40 * k) := by ring
  have hmulK :
      40 * k * k * k + 80 * k * k + 100 * k + 50 * k + 200 +
        (k * k * (800 * W + 2010) + 60 * W + 40 * (k * k) + 200) +
        (k * (800 * W + 2010) + 60 * W + 40 * k + 200) ≤
      k * k * (2000 * W + 50 * k + 5000) + 200 * W + 1000 := by
    have h1 : (k * k) * (40 * k) + (k * k) * (800 * W + 2010) + (k * k) * (800 * W + 2010) ≤
        (k * k) * (1600 * W + 40 * k + 4020) := by
      have : (k * k) * (40 * k) + (k * k) * (800 * W + 2010) + (k * k) * (800 * W + 2010) =
          (k * k) * (1600 * W + 40 * k + 4020) := by ring
      omega
    have h2 : (k * k) * (1600 * W + 40 * k + 4020) + 120 * (k * k) + 190 * k ≤
        (k * k) * (2000 * W + 50 * k + 5000) := by
      have : (k * k) * (1600 * W + 40 * k + 4020) + (k * k) * (400 * W + 10 * k + 980) =
          (k * k) * (2000 * W + 50 * k + 5000) := by ring
      nlinarith
    nlinarith
  exact ⟨t, by nlinarith, hcomp⟩

theorem fitsSignedWord_arctanInvTaylorFixed (N k : ℕ) {W : ℕ}
    (hW : 5 * N + 9 ≤ W) :
    FitsSignedWord W (arctanInvTaylorFixed N k) := by
  unfold arctanInvTaylorFixed
  set q_acc : ℕ := 4 * N + 6
  have hN1_pow : N + 1 ≤ 2 ^ (N + 1) := le_of_lt Nat.lt_two_pow_self
  have hsum := fitsSignedWord_sum_range (N + 1) hN1_pow
    (fun m => altSign m * roundDivInt ((arctanInvPowArrayFixed k q_acc N).getD m 0) ((2 * m + 1 : ℕ) : ℤ))
    (fun m _ => by
      have hd : FitsSignedWord (q_acc + 2)
          (roundDivInt ((arctanInvPowArrayFixed k q_acc N).getD m 0) ((2 * m + 1 : ℕ) : ℤ)) :=
        (fitsSignedWord_arctanInvPowArrayFixed_getD k q_acc N m).roundDivInt _
      rcases altSign_eq_one_or_neg_one m with h1 | h1
      · rw [h1, one_mul]; exact hd
      · rw [h1, neg_one_mul]; exact hd.neg)
  exact hsum.mono (by dsimp [q_acc]; omega)

/-- **Pure-Integer Machin $\pi$ Stage (`bmApproxPi`)**:
Consumes `encPair encUnary encUnary (W, S)` on `kIO` (`5 * S + 30 ≤ W`) and emits
`encodeSignedWord W (approxPiFixed S)` in $O((S + 4) \cdot W^2)$ `TM2.step` transitions. -/
def bmApproxPi : BitMachine :=
  let bmW := bmFst
  let bmN := bmSeq (bmFanout bmSnd (bmUnaryConst 3)) bmUnaryAdd
  let bmA2 := bmSeq (bmFanout bmW (bmFanout bmN (bmUnaryConst 2))) bmArctanInvTaylor
  let bmA3 := bmSeq (bmFanout bmW (bmFanout bmN (bmUnaryConst 3))) bmArctanInvTaylor
  let bmSum := bmSeq (bmFanout bmA2 bmA3) bmSignedAdd
  bmSeq (bmSeq bmSum bmSignedDouble) bmSignedDouble

theorem bmApproxPi_computesInTime (W S : ℕ) (hW : 5 * S + 30 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (S + 4) * (1000 * W * W + 320000 * W + 800000) +
        600 * W * W + 300000 * W + 900000,
      bmApproxPi.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (W, S)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (approxPiFixed S)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let St := Unit
  let N : ℕ := S + 3
  let uIn : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary S)
  have pW := StageEval.fst (fun _ : St => encUnary W) (fun _ => encUnary S)
  have pS := StageEval.snd (fun _ : St => encUnary W) (fun _ => encUnary S)
  have pN := StageEval.seq
    (StageEval.fanout pS (StageEval.unaryConst 3 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (S, 3)))
  have h2_pow : 2 * 2 < 2 ^ W :=
    lt_of_le_of_lt (by omega : 4 ≤ W) Nat.lt_two_pow_self
  have h3_pow : 3 * 3 < 2 ^ W :=
    lt_of_le_of_lt (by omega : 9 ≤ W) Nat.lt_two_pow_self
  have hNW : 5 * N + 10 ≤ W := by dsimp [N]; omega
  have pA2 := StageEval.seq
    (StageEval.fanout pW
      (StageEval.fanout pN (StageEval.unaryConst 2 uIn)))
    (StageEval.const (S := St) (bmArctanInvTaylor_computesInTime W N 2 (by decide) h2_pow hNW))
  have pA3 := StageEval.seq
    (StageEval.fanout pW
      (StageEval.fanout pN (StageEval.unaryConst 3 uIn)))
    (StageEval.const (S := St) (bmArctanInvTaylor_computesInTime W N 3 (by decide) h3_pow hNW))
  set a2 := arctanInvTaylorFixed N 2
  set a3 := arctanInvTaylorFixed N 3
  have ha2_fits : FitsSignedWord (5 * N + 9) a2 :=
    fitsSignedWord_arctanInvTaylorFixed N 2 (le_refl _)
  have ha3_fits : FitsSignedWord (5 * N + 9) a3 :=
    fitsSignedWord_arctanInvTaylorFixed N 3 (le_refl _)
  have hsum_fits10 : FitsSignedWord (5 * N + 10) (a2 + a3) := ha2_fits.add ha3_fits
  have h2sum_fits11 : FitsSignedWord (5 * N + 11) (2 * (a2 + a3)) := by
    have : 2 * (a2 + a3) = (a2 + a3) + (a2 + a3) := by ring
    rw [this]; exact hsum_fits10.add hsum_fits10
  have h4sum_fits12 : FitsSignedWord (5 * N + 12) (2 * (2 * (a2 + a3))) := by
    have : 2 * (2 * (a2 + a3)) = 2 * (a2 + a3) + 2 * (a2 + a3) := by ring
    rw [this]; exact h2sum_fits11.add h2sum_fits11
  have pSum := StageEval.seq (StageEval.fanout pA2 pA3)
    (StageEval.const (S := St)
      (bmSignedAdd_computesInTime W a2 a3
        (ha2_fits.mono (by dsimp [N]; omega))
        (ha3_fits.mono (by dsimp [N]; omega))
        (hsum_fits10.mono (by dsimp [N]; omega))))
  have pDbl1 := StageEval.seq pSum
    (StageEval.const (S := St)
      (bmSignedDouble_computesInTime W (a2 + a3)
        (hsum_fits10.mono (by dsimp [N]; omega))
        (h2sum_fits11.mono (by dsimp [N]; omega))))
  have pDbl2 := StageEval.seq pDbl1
    (StageEval.const (S := St)
      (bmSignedDouble_computesInTime W (2 * (a2 + a3))
        (h2sum_fits11.mono (by dsimp [N]; omega))
        (h4sum_fits12.mono (by dsimp [N]; omega))))
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W (approxPiFixed S))
    pDbl2
    (fun _ => by
      dsimp only [approxPiFixed, a2, a3, N]
      congr 1; ring)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, N, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-! ### 4.3 Common Exponential Taylor Recurrence Step & Sum (`bmExpTermStepWith`, `bmExpRecurrenceSumWith`) -/

/-- **Exponential Taylor Power-Factorial Recurrence Step (`bmExpTermStepWith bmMul`)**:
Consumes `(((q_r, r_mant), W), (m_signed, T_m))` on `kIO` and emits
`encodeSignedWord W (expTermStepFixed q_r r_mant m T_m)` via `bmSignedMulWith bmMul`,
`bmShiftLeftSigned`, and `bmRoundDivResize`. -/
def bmExpTermStepWith (bmMul : BitMachine) : BitMachine :=
  let bmQR := bmSeq (bmSeq bmFst bmFst) bmFst
  let bmRMant := bmSeq (bmSeq bmFst bmFst) bmSnd
  let bmW := bmSeq bmFst bmSnd
  let bmM := bmSeq bmSnd bmFst
  let bmTm := bmSeq bmSnd bmSnd
  let bmProd := bmSeq (bmFanout bmTm bmRMant) (bmSignedMulWith bmMul)
  let bmM1 := bmSeq bmM bmSignedSucc
  let bmDen := bmSeq (bmFanout bmQR bmM1) bmShiftLeftSigned
  bmSeq (bmFanout bmW (bmFanout bmProd bmDen)) bmRoundDivResize

theorem bmExpTermStepWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W q_r m : ℕ) (r_mant T_m : ℤ)
    (hW : 1 ≤ W) (hqr : q_r ≤ W) (hm : m + 1 ≤ W)
    (hr : FitsSignedWord W r_mant) (hT : FitsSignedWord W T_m)
    (hout : FitsSignedWord W (expTermStepFixed q_r r_mant m T_m))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * mulTime W + 5000 * W * W + 420000 * W + 450000,
      (bmExpTermStepWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary (encodeSignedWord W)) encUnary)
            (encPair (encodeSignedWord W) (encodeSignedWord W))
            (((q_r, r_mant), W), ((m : ℤ), T_m))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (expTermStepFixed q_r r_mant m T_m)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uCtx : S → List Bool :=
    encDepPair (fun _ => encUnary q_r) (fun _ => encodeSignedWord W r_mant)
  let uCW : S → List Bool := encDepPair uCtx (fun _ => encUnary W)
  let uMT : S → List Bool :=
    encDepPair (fun _ => encodeSignedWord W (m : ℤ)) (fun _ => encodeSignedWord W T_m)
  let uIn : S → List Bool := encDepPair uCW uMT
  have pCW := StageEval.fst uCW uMT
  have pMT := StageEval.snd uCW uMT
  have pCtx := StageEval.seq pCW (StageEval.fst uCtx (fun _ : S => encUnary W))
  have pW := StageEval.seq pCW (StageEval.snd uCtx (fun _ : S => encUnary W))
  have pQR := StageEval.seq pCtx
    (StageEval.fst (fun _ : S => encUnary q_r) (fun _ => encodeSignedWord W r_mant))
  have pRMant := StageEval.seq pCtx
    (StageEval.snd (fun _ : S => encUnary q_r) (fun _ => encodeSignedWord W r_mant))
  have pM := StageEval.seq pMT
    (StageEval.fst (fun _ : S => encodeSignedWord W (m : ℤ)) (fun _ => encodeSignedWord W T_m))
  have pTm := StageEval.seq pMT
    (StageEval.snd (fun _ : S => encodeSignedWord W (m : ℤ)) (fun _ => encodeSignedWord W T_m))
  have pProd := StageEval.seq (StageEval.fanout pTm pRMant)
    (StageEval.const (S := S) (bmSignedMulWith_computesInTime hmul W T_m r_mant hT hr))
  have hf0 : FitsSignedWord W (m : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  have hf1 : FitsSignedWord W ((m + 1 : ℕ) : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact lt_of_le_of_lt hm Nat.lt_two_pow_self
  have hf1_add : FitsSignedWord W ((m : ℤ) + 1) := by
    have : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
    rwa [this]
  have pM1 := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W ((m + 1 : ℕ) : ℤ))
    (StageEval.seq pM (StageEval.const (S := S) (bmSignedSucc_computesInTime W hW (m : ℤ) hf0 hf1_add)))
    (fun _ => by push_cast; rfl)
  have pDen := StageEval.seq (StageEval.fanout pQR pM1)
    (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime q_r W ((m + 1 : ℕ) : ℤ) hf1))
  have hprod_fits : FitsSignedWord (2 * W) (T_m * r_mant) := by
    simpa [Nat.two_mul] using hT.mul hr
  have hden_fits : FitsSignedWord (q_r + W) (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r) := by
    simpa [Nat.add_comm] using hf1.mul_two_pow q_r
  have pDiv := StageEval.const (S := S)
    (bmRoundDivResize_computesInTime W (2 * W) (q_r + W)
      (T_m * r_mant) (((m + 1 : ℕ) : ℤ) * (2 : ℤ) ^ q_r)
      hprod_fits hden_fits hout)
  have hall := StageEval.seq (StageEval.fanout pW (StageEval.fanout pProd pDen)) pDiv
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uCW, uCtx, uMT, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-- **Common Exponential Taylor Recurrence Sum (`bmExpRecurrenceSumWith bmMul termM`)**:
Consumes `((((q_r, r_mant), W), M), q_acc)` on `kIO`, initializes `T_0 = (2 : ℤ) ^ q_acc` via
`bmSignedTwoPow`, and runs `bmRecurrenceSumSigned (bmExpTermStepWith bmMul) termM` over
`m ∈ {0, ..., M}` to emit
`encodeSignedWord W (∑ m ∈ Finset.range (M + 1), term m ((expTermArrayFixed q_r q_acc M r_mant).getD m 0))`. -/
def bmExpRecurrenceSumWith (bmMul termM : BitMachine) : BitMachine :=
  let bmW := bmSeq (bmSeq bmFst bmFst) bmSnd
  let bmT0 := bmSeq (bmFanout bmW bmSnd) bmSignedTwoPow
  bmSeq (bmFanout bmFst bmT0) (bmRecurrenceSumSigned (bmExpTermStepWith bmMul) termM)

set_option maxHeartbeats 800000 in
theorem StageEval.expRecurrenceSumWith {S : Type} {bmMul termM : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (B W q_r q_acc M : S → ℕ) (r_mant : S → ℤ)
    (term : S → ℕ → ℤ → ℤ) (B_term : S → ℕ)
    (hr : ∀ s, |r_mant s| ≤ (B s : ℤ) * (2 : ℤ) ^ (q_r s))
    (hM_qacc : ∀ s, M s ≤ q_acc s)
    (hW_T : ∀ s, q_acc s + 2 * B s + 2 ≤ W s)
    (hW_r : ∀ s, q_r s + B s + 1 ≤ W s)
    (hterm : ∀ (m : ℕ),
      StageEval (S := { s : S // m ≤ M s }) termM
        (encDepPair
          (encDepPair
            (encDepPair (fun s => encUnary (q_r s.val))
              (fun s => encodeSignedWord (W s.val) (r_mant s.val)))
            (fun s => encUnary (W s.val)))
          (encDepPair
            (fun s => encodeSignedWord (W s.val) (m : ℤ))
            (fun s => encodeSignedWord (W s.val)
              (buildRecurrenceArray ((2 : ℤ) ^ (q_acc s.val))
                (expTermStepFixed (q_r s.val) (r_mant s.val)) m).2)))
        (fun s => encodeSignedWord (W s.val)
          (term s.val m
            (buildRecurrenceArray ((2 : ℤ) ^ (q_acc s.val))
              (expTermStepFixed (q_r s.val) (r_mant s.val)) m).2))
        (fun s => B_term s.val))
    (hfits_term : ∀ (s : S) (m : ℕ), m ≤ M s →
      FitsSignedWord (W s)
        (term s m
          (buildRecurrenceArray ((2 : ℤ) ^ (q_acc s))
            (expTermStepFixed (q_r s) (r_mant s)) m).2))
    (hfits_sum : ∀ (s : S) (m : ℕ), m ≤ M s →
      FitsSignedWord (W s)
        (∑ j ∈ Finset.range (m + 1),
          term s j
            (buildRecurrenceArray ((2 : ℤ) ^ (q_acc s))
              (expTermStepFixed (q_r s) (r_mant s)) j).2)) :
    StageEval (bmExpRecurrenceSumWith bmMul termM)
      (encDepPair
        (encDepPair
          (encDepPair
            (encDepPair (fun s => encUnary (q_r s))
              (fun s => encodeSignedWord (W s) (r_mant s)))
            (fun s => encUnary (W s)))
          (fun s => encUnary (M s)))
        (fun s => encUnary (q_acc s)))
      (fun s => encodeSignedWord (W s)
        (∑ m ∈ Finset.range (M s + 1),
          term s m ((expTermArrayFixed (q_r s) (q_acc s) (M s) (r_mant s)).getD m 0)))
      (fun s =>
        (M s + 1) * (2 * mulTime (W s) + B_term s + 5000 * W s * W s + 450000 * W s + 500000) +
        10000 * W s + 50000) := by
  let uCtx : S → List Bool :=
    encDepPair (fun s => encUnary (q_r s)) (fun s => encodeSignedWord (W s) (r_mant s))
  let uCW : S → List Bool := encDepPair uCtx (fun s => encUnary (W s))
  let uCWM : S → List Bool := encDepPair uCW (fun s => encUnary (M s))
  let uIn : S → List Bool := encDepPair uCWM (fun s => encUnary (q_acc s))
  have pCWM := StageEval.fst uCWM (fun s => encUnary (q_acc s))
  have pQAcc := StageEval.snd uCWM (fun s => encUnary (q_acc s))
  have pCW := StageEval.seq pCWM (StageEval.fst uCW (fun s => encUnary (M s)))
  have pW := StageEval.seq pCW (StageEval.snd uCtx (fun s => encUnary (W s)))
  have pT0 : StageEval bmSignedTwoPow
      (encDepPair (fun s => encUnary (W s)) (fun s => encUnary (q_acc s)))
      (fun s => encodeSignedWord (W s) ((2 : ℤ) ^ (q_acc s)))
      (fun s => 3000 * W s + 3000 * q_acc s + 6000) := by
    intro s u2 u3 u4 u5 uSc
    have hq_lt : q_acc s < W s := by have := hW_T s; omega
    exact bmSignedTwoPow_computesInTime (W s) (q_acc s) (by omega) hq_lt u2 u3 u4 u5 uSc
  have pInit := StageEval.fanout pCWM (StageEval.seq (StageEval.fanout pW pQAcc) pT0)
  have hRec := StageEval.recurrenceSumSigned
    (uCtx := uCtx)
    (W := W)
    (M := M)
    (T_0 := fun s => (2 : ℤ) ^ (q_acc s))
    (step := fun s => expTermStepFixed (q_r s) (r_mant s))
    (term := term)
    (B_step := fun s => 2 * mulTime (W s) + 5000 * W s * W s + 420000 * W s + 450000)
    (B_term := B_term)
    (L_ctx := fun s => 4 * W s + 8)
    (fun s => by have := hW_T s; omega)
    (fun s => by
      have h1 : M s + 1 ≤ W s := by have := hM_qacc s; have := hW_T s; omega
      exact lt_of_le_of_lt h1 Nat.lt_two_pow_self)
    (fun m => by
      intro s' u2 u3 u4 u5 uSc
      have hm_le : m ≤ q_acc s'.val := (le_of_lt s'.property).trans (hM_qacc s'.val)
      have hm1_le : m + 1 ≤ q_acc s'.val := (Nat.succ_le_of_lt s'.property).trans (hM_qacc s'.val)
      exact bmExpTermStepWith_computesInTime hmul (W s'.val) (q_r s'.val) m
        (r_mant s'.val)
        (buildRecurrenceArray ((2 : ℤ) ^ (q_acc s'.val))
          (expTermStepFixed (q_r s'.val) (r_mant s'.val)) m).2
        (by have := hW_T s'.val; omega)
        (by have := hW_r s'.val; omega)
        (by have := hW_T s'.val; omega)
        (fitsSignedWord_of_abs_le_mul_two_pow (hr s'.val) (hW_r s'.val))
        (fitsSignedWord_buildRecurrenceArray_expTermStepFixed
          (B s'.val) (q_r s'.val) (q_acc s'.val) (r_mant s'.val)
          (hr s'.val) hm_le (hW_T s'.val))
        (fitsSignedWord_buildRecurrenceArray_expTermStepFixed
          (B s'.val) (q_r s'.val) (q_acc s'.val) (r_mant s'.val)
          (hr s'.val) hm1_le (hW_T s'.val))
        u2 u3 u4 u5 uSc)
    hterm
    hfits_term
    hfits_sum
    (fun s => by
      dsimp only [uCtx]
      have hqr_le : q_r s ≤ W s := by have := hW_r s; omega
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega)
  have hall := StageEval.congr_out
    (v2 := fun s => encodeSignedWord (W s)
      (∑ m ∈ Finset.range (M s + 1),
        term s m ((expTermArrayFixed (q_r s) (q_acc s) (M s) (r_mant s)).getD m 0)))
    (StageEval.seq pInit hRec)
    (fun _ => rfl)
  refine hall.mono (fun s => ?_)
  dsimp only [uIn, uCWM, uCW, uCtx]
  have hqr_le : q_r s ≤ W s := by have := hW_r s; omega
  have hqacc_le : q_acc s ≤ W s := by have := hW_T s; omega
  have hM_le : M s ≤ W s := (hM_qacc s).trans hqacc_le
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
  nlinarith

/-! ### 4.4 Pure-Integer Unit Root, Sinc, Exp, and Erf Series Stages
(`bmModSignedPos`, `bmExpTwoPiIWith`, `bmSincTaylorWith`, `bmExpTaylorWith`, `bmErfTaylorWith`) -/

theorem emod_eq_if_neg_of_bounds {num : ℤ} {den : ℕ}
    (hlo : -(den : ℤ) ≤ num) (hhi : num < (den : ℤ)) :
    num % (den : ℤ) = if num < 0 then num + (den : ℤ) else num := by
  split_ifs with hneg
  · have h1 : num = (num + (den : ℤ)) + (den : ℤ) * (-1) := by ring
    conv_lhs => rw [h1, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · exact Int.emod_eq_of_lt (by omega) hhi

/-- **Signed Modular Reduction in $[-\text{den}, \text{den})$ (`bmModSignedPos`)**:
Consumes `encPair (encodeSignedWord W) (encodeSignedWord W) (num, (den : ℤ))` on `kIO`
(`-(den : ℤ) ≤ num < (den : ℤ)`) and emits `encodeSignedWord W (num % (den : ℤ))` in $O(W)$ steps. -/
def bmModSignedPos : BitMachine :=
  bmIte (bmSeq bmFst bmSignedIsNeg) bmSignedAdd bmFst

theorem bmModSignedPos_computesInTime (W : ℕ) (num : ℤ) (den : ℕ)
    (hlo : -(den : ℤ) ≤ num) (hhi : num < (den : ℤ))
    (hnum : FitsSignedWord W num) (hden : FitsSignedWord W (den : ℤ))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 1000 * W + 2500,
      bmModSignedPos.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encodeSignedWord W) (encodeSignedWord W) (num, (den : ℤ))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (num % (den : ℤ))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let u1 : S → List Bool := fun _ => encodeSignedWord W num
  let u2 : S → List Bool := fun _ => encodeSignedWord W (den : ℤ)
  let uIn : S → List Bool := encDepPair u1 u2
  have pCond := StageEval.seq (StageEval.fst u1 u2)
    (StageEval.const (S := S) (bmSignedIsNeg_computesInTime W num hnum))
  have pThen : ∀ s : S, decide (num < 0) = true →
      ∀ tW2 tW3 tW4 tW5 tSch : List Bool,
        ∃ t ≤ (fun _ : S => 580 * W + 1300) s,
          bmSignedAdd.ComputesInTime
            (mkTapes8 (encodeDelimWord (uIn s)) [] [] tW2 tW3 tW4 tW5 tSch)
            (mkTapes8 (encodeDelimWord (encodeSignedWord W (num % (den : ℤ))))
              [] [] tW2 tW3 tW4 tW5 tSch) t := by
    intro _ hs v2 v3 v4 v5 vSc
    have hneg : num < 0 := of_decide_eq_true hs
    have hmod : num % (den : ℤ) = num + (den : ℤ) := by
      rw [emod_eq_if_neg_of_bounds hlo hhi, if_pos hneg]
    have hsum_fits : FitsSignedWord W (num + (den : ℤ)) := by
      rw [fitsSignedWord_iff_abs_lt] at hden ⊢
      rw [abs_of_nonneg (by omega : 0 ≤ (den : ℤ))] at hden
      rw [abs_of_nonneg (by omega : 0 ≤ num + (den : ℤ))]
      omega
    rcases bmSignedAdd_computesInTime W num (den : ℤ) hnum hden hsum_fits v2 v3 v4 v5 vSc
      with ⟨t, ht, hc⟩
    rw [← hmod] at hc
    exact ⟨t, ht, hc⟩
  have pElse : ∀ s : S, decide (num < 0) = false →
      ∀ tW2 tW3 tW4 tW5 tSch : List Bool,
        ∃ t ≤ (fun _ : S => 6 * W + 13) s,
          bmFst.ComputesInTime
            (mkTapes8 (encodeDelimWord (uIn s)) [] [] tW2 tW3 tW4 tW5 tSch)
            (mkTapes8 (encodeDelimWord (encodeSignedWord W (num % (den : ℤ))))
              [] [] tW2 tW3 tW4 tW5 tSch) t := by
    intro s hs v2 v3 v4 v5 vSc
    have hnn : ¬ num < 0 := of_decide_eq_false hs
    have hmod : num % (den : ℤ) = num := by
      rw [emod_eq_if_neg_of_bounds hlo hhi, if_neg hnn]
    rcases StageEval.fst u1 u2 s v2 v3 v4 v5 vSc with ⟨t, ht, hc⟩
    dsimp only [u1, u2, id] at ht hc ⊢
    simp only [length_encodeSignedWord] at ht
    have hc' : bmFst.ComputesInTime
        (mkTapes8 (encodeDelimWord (uIn s)) [] [] v2 v3 v4 v5 vSc)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (num % (den : ℤ))))
          [] [] v2 v3 v4 v5 vSc) t := by
      rw [hmod]; exact hc
    exact ⟨t, by omega, hc'⟩
  have pIte := StageEval.ite pCond pThen pElse
  rcases pIte () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, u1, u2, id] at ht hcomp
  simp only [length_encDepPair, length_encodeSignedWord] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- **Pure-Integer Unit Root Stage (`bmExpTwoPiIWith bmMul`)**:
Consumes `(((W, (WOut, q)), piFixed), (num, den_signed))` on `kIO`
(`4 ≤ q`, `100 * q ≤ W`, `q + 2 ≤ WOut`, `0 < den`, `den ≤ 2 ^ q`, `-(den : ℤ) ≤ num < (den : ℤ)`)
and emits `encComplex WOut (expTwoPiIFixed q num den)` in $O((q + 60) \cdot (M_{\text{mul}}(W) + W^2))$ steps. -/
def bmExpTwoPiIWith (bmMul : BitMachine) : BitMachine :=
  let bmHeader := bmSeq bmFst bmFst
  let bmW := bmSeq bmHeader bmFst
  let bmWOut := bmSeq (bmSeq bmHeader bmSnd) bmFst
  let bmQ := bmSeq (bmSeq bmHeader bmSnd) bmSnd
  let bmPi := bmSeq bmFst bmSnd
  let bmNum := bmSeq bmSnd bmFst
  let bmDen := bmSeq bmSnd bmSnd
  let bmM := bmSeq (bmFanout bmQ (bmUnaryConst 57)) bmUnaryAdd
  let bmQR := bmSeq bmM bmUnaryDouble
  let bmQAcc := bmSeq (bmFanout (bmSeq (bmFanout bmM bmQR) bmUnaryAdd) (bmUnaryConst 6)) bmUnaryAdd
  let bmQPi := bmSeq (bmFanout (bmSeq (bmSeq bmQ bmUnaryDouble) bmUnaryDouble) (bmUnaryConst 58)) bmUnaryAdd
  let bmNumMod := bmSeq (bmFanout bmNum bmDen) bmModSignedPos
  let bmProdPi := bmSeq (bmFanout bmPi bmNumMod) (bmSignedMulWith bmMul)
  let bmThetaNum := bmSeq (bmFanout (bmUnaryConst 1) bmProdPi) bmShiftLeftSigned
  let bmThetaShift := bmSeq (bmFanout bmQR bmThetaNum) bmShiftLeftSigned
  let bmThetaDen := bmSeq (bmFanout bmQPi bmDen) bmShiftLeftSigned
  let bmRMant := bmSeq (bmFanout bmW (bmFanout bmThetaShift bmThetaDen)) bmRoundDivResize
  let bmRecIn := bmFanout (bmFanout (bmFanout (bmFanout bmQR bmRMant) bmW) bmM) bmQAcc
  let bmReSum := bmSeq bmRecIn (bmExpRecurrenceSumWith bmMul (bmSeq bmSnd bmIPowReMulSigned))
  let bmImSum := bmSeq bmRecIn (bmExpRecurrenceSumWith bmMul (bmSeq bmSnd bmIPowImMulSigned))
  let bmReShift := bmSeq (bmFanout bmQ bmReSum) bmShiftLeftSigned
  let bmImShift := bmSeq (bmFanout bmQ bmImSum) bmShiftLeftSigned
  let bmTwoPowQAcc := bmSeq (bmFanout bmW bmQAcc) bmSignedTwoPow
  let bmReOut := bmSeq (bmFanout bmWOut (bmFanout bmReShift bmTwoPowQAcc)) bmRoundDivResize
  let bmImOut := bmSeq (bmFanout bmWOut (bmFanout bmImShift bmTwoPowQAcc)) bmRoundDivResize
  bmFanout bmReOut bmImOut

set_option maxHeartbeats 800000 in
theorem bmExpTwoPiIWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W WOut q den : ℕ) (num : ℤ)
    (hq : 4 ≤ q) (hW : 100 * q ≤ W) (hWOut : q + 2 ≤ WOut) (hWOut_le : WOut ≤ W)
    (hden_pos : 0 < den) (hden_le : den ≤ 2 ^ q)
    (hlo : -(den : ℤ) ≤ num) (hhi : num < (den : ℤ))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let piFixed := approxPiFixed (q + 10)
    ∃ t ≤ (q + 58) * (4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000) +
        4 * mulTime W + 30000 * W * W + 2000000 * W + 2000000,
      (bmExpTwoPiIWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair
            (encPair (encPair encUnary (encPair encUnary encUnary)) (encodeSignedWord W))
            (encPair (encodeSignedWord W) (encodeSignedWord W))
            (((W, (WOut, q)), piFixed), (num, (den : ℤ)))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex WOut (expTwoPiIFixed q num den)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro piFixed
  let St := Unit
  let S : ℕ := q + 10
  let q_pi : ℕ := 2 * (2 * q) + 58
  have hqpi_eq : q_pi = 4 * (S + 3) + 6 := by dsimp [q_pi, S]; omega
  let N : ℕ := 4 * 10 + S + 1
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = q + 57 := ⟨q + 57, rfl⟩
  have hM_eq : M = N + 6 := by dsimp [N, S]; omega
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := (M + q_r) + 6
  have hqacc_eq : q_acc = 3 * M + 6 := by dsimp [q_acc, q_r]; omega
  let uWQ : St → List Bool := encDepPair (fun _ => encUnary WOut) (fun _ => encUnary q)
  let uHdr : St → List Bool := encDepPair (fun _ => encUnary W) uWQ
  let uFst : St → List Bool := encDepPair uHdr (fun _ => encodeSignedWord W piFixed)
  let uSnd : St → List Bool :=
    encDepPair (fun _ => encodeSignedWord W num) (fun _ => encodeSignedWord W (den : ℤ))
  let uIn : St → List Bool := encDepPair uFst uSnd
  have pFst := StageEval.fst uFst uSnd
  have pSnd := StageEval.snd uFst uSnd
  have pHdr := StageEval.seq pFst (StageEval.fst uHdr (fun _ : St => encodeSignedWord W piFixed))
  have pPi := StageEval.seq pFst (StageEval.snd uHdr (fun _ : St => encodeSignedWord W piFixed))
  have pW := StageEval.seq pHdr (StageEval.fst (fun _ : St => encUnary W) uWQ)
  have pWQ := StageEval.seq pHdr (StageEval.snd (fun _ : St => encUnary W) uWQ)
  have pWOut := StageEval.seq pWQ (StageEval.fst (fun _ : St => encUnary WOut) (fun _ => encUnary q))
  have pQ := StageEval.seq pWQ (StageEval.snd (fun _ : St => encUnary WOut) (fun _ => encUnary q))
  have pNum := StageEval.seq pSnd
    (StageEval.fst (fun _ : St => encodeSignedWord W num) (fun _ => encodeSignedWord W (den : ℤ)))
  have pDen := StageEval.seq pSnd
    (StageEval.snd (fun _ : St => encodeSignedWord W num) (fun _ => encodeSignedWord W (den : ℤ)))
  have pM := StageEval.congr_out
    (v2 := fun _ => encUnary M)
    (StageEval.seq (StageEval.fanout pQ (StageEval.unaryConst 57 uIn))
      (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (q, 57))))
    (fun _ => by dsimp only; rw [← hM_def])
  have pQR := StageEval.seq pM
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => M))
  have pMQR := StageEval.seq (StageEval.fanout pM pQR)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M, q_r)))
  have pQAcc := StageEval.seq (StageEval.fanout pMQR (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M + q_r, 6)))
  have p2Q := StageEval.seq pQ
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => q))
  have p4Q := StageEval.seq p2Q
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * q))
  have pQPi := StageEval.seq (StageEval.fanout p4Q (StageEval.unaryConst 58 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (2 * (2 * q), 58)))
  have hden_z : (den : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast hden_le
  have hden_lt_W : (den : ℤ) < (2 : ℤ) ^ W :=
    lt_of_le_of_lt hden_z (pow_lt_pow_right₀ (by decide) (by omega))
  have hden_fits : FitsSignedWord W (den : ℤ) := by
    rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg (by positivity)]
    exact hden_lt_W
  have hnum_fits : FitsSignedWord W num := by
    rw [fitsSignedWord_iff_abs_lt]
    have habs : |num| ≤ (den : ℤ) := abs_le.mpr ⟨hlo, le_of_lt hhi⟩
    exact lt_of_le_of_lt habs hden_lt_W
  set numMod : ℤ := num % (den : ℤ)
  have hden_z_pos : (0 : ℤ) < (den : ℤ) := by positivity
  have hmod_abs : |numMod| < (den : ℤ) := by
    rw [abs_of_nonneg (Int.emod_nonneg num (ne_of_gt hden_z_pos))]
    exact Int.emod_lt_of_pos num hden_z_pos
  have hmod_fits : FitsSignedWord W numMod := by
    rw [fitsSignedWord_iff_abs_lt]
    exact lt_of_lt_of_le hmod_abs (le_of_lt hden_lt_W)
  have pNumMod := StageEval.seq (StageEval.fanout pNum pDen)
    (StageEval.const (S := St)
      (bmModSignedPos_computesInTime W num den hlo hhi hnum_fits hden_fits))
  have hpi_fits : FitsSignedWord W piFixed :=
    fitsSignedWord_approxPiFixed S (by dsimp [S]; omega)
  have pProdPi := StageEval.seq (StageEval.fanout pPi pNumMod)
    (StageEval.const (S := St) (bmSignedMulWith_computesInTime hmul W piFixed numMod hpi_fits hmod_fits))
  have hprod_fits : FitsSignedWord (2 * W) (piFixed * numMod) := by
    simpa [Nat.two_mul] using hpi_fits.mul hmod_fits
  have pThetaNum := StageEval.seq (StageEval.fanout (StageEval.unaryConst 1 uIn) pProdPi)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime 1 (2 * W) (piFixed * numMod) hprod_fits))
  have htheta_fits : FitsSignedWord (1 + 2 * W) ((piFixed * numMod) * (2 : ℤ) ^ 1) := by
    simpa [Nat.add_comm] using hprod_fits.mul_two_pow 1
  have pThetaShift := StageEval.seq (StageEval.fanout pQR pThetaNum)
    (StageEval.const (S := St)
      (bmShiftLeftSigned_computesInTime q_r (1 + 2 * W) ((piFixed * numMod) * (2 : ℤ) ^ 1) htheta_fits))
  have pThetaDen := StageEval.seq (StageEval.fanout pQPi pDen)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime q_pi W (den : ℤ) hden_fits))
  set θNum : ℤ := 2 * (piFixed * numMod)
  set θDen : ℤ := (den : ℤ) * (2 : ℤ) ^ q_pi
  have htheta_eq : ((piFixed * numMod) * (2 : ℤ) ^ 1) * (2 : ℤ) ^ q_r = θNum * (2 : ℤ) ^ q_r := by
    dsimp [θNum]; ring
  have hthetaShift_fits : FitsSignedWord (q_r + (1 + 2 * W)) (θNum * (2 : ℤ) ^ q_r) := by
    rw [← htheta_eq]
    simpa [Nat.add_comm] using htheta_fits.mul_two_pow q_r
  have hthetaDen_fits : FitsSignedWord (q_pi + W) θDen := by
    simpa [Nat.add_comm] using hden_fits.mul_two_pow q_pi
  have hθ_bound : |θNum| ≤ (10 : ℤ) * θDen := by
    have hpi_nn : 0 ≤ piFixed := approxPiFixed_nonneg S
    have hpi_le : piFixed ≤ 5 * (2 : ℤ) ^ q_pi := by
      rw [hqpi_eq]; exact approxPiFixed_le S
    have hmod_le : |numMod| ≤ (den : ℤ) := le_of_lt hmod_abs
    have hmod_nn : 0 ≤ |numMod| := abs_nonneg numMod
    calc |θNum| = 2 * piFixed * |numMod| := by
          dsimp [θNum]; rw [abs_mul, abs_mul, abs_of_pos (by decide), abs_of_nonneg hpi_nn]; ring
      _ ≤ 2 * (5 * (2 : ℤ) ^ q_pi) * (den : ℤ) := by nlinarith only [hpi_le, hmod_le, hpi_nn, hmod_nn]
      _ = (10 : ℤ) * θDen := by dsimp [θDen]; ring
  set r_mant : ℤ := roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen
  have hr_bound : |r_mant| ≤ (10 : ℤ) * (2 : ℤ) ^ q_r :=
    abs_roundDivInt_mul_two_pow_le_of_pos 10 q_r (by positivity) hθ_bound
  have hr_fits : FitsSignedWord W r_mant :=
    fitsSignedWord_of_abs_le_mul_two_pow hr_bound (by dsimp [q_r]; omega)
  have pRMant := StageEval.seq
    (StageEval.fanout pW
      (StageEval.fanout
        (StageEval.congr_out
          (v2 := fun _ => encodeSignedWord (q_r + (1 + 2 * W)) (θNum * (2 : ℤ) ^ q_r))
          pThetaShift (fun _ => by rw [htheta_eq]))
        pThetaDen))
    (StageEval.const (S := St)
      (bmRoundDivResize_computesInTime W (q_r + (1 + 2 * W)) (q_pi + W)
        (θNum * (2 : ℤ) ^ q_r) θDen hthetaShift_fits hthetaDen_fits hr_fits))
  have pRecIn := StageEval.fanout
    (StageEval.fanout (StageEval.fanout (StageEval.fanout pQR pRMant) pW) pM) pQAcc
  have hT_fits : ∀ m ≤ M,
      FitsSignedWord (q_acc + 22)
        (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 := by
    intro m hm
    exact fitsSignedWord_buildRecurrenceArray_expTermStepFixed 10 q_r q_acc r_mant hr_bound
      (by dsimp [q_acc, q_r] at *; omega) (le_refl _)
  have pReSum := StageEval.seq pRecIn
    (StageEval.expRecurrenceSumWith (S := St) hmul
      (fun _ => 10) (fun _ => W) (fun _ => q_r) (fun _ => q_acc) (fun _ => M) (fun _ => r_mant)
      (fun _ m T_m => iPowRe m * T_m) (fun _ => 1300 * W + 3200)
      (fun _ => hr_bound)
      (fun _ => by dsimp [q_acc, q_r]; omega)
      (fun _ => by dsimp [q_acc, q_r]; omega)
      (fun _ => by dsimp [q_r]; omega)
      (fun m => by
        let SubS := { s : St // m ≤ M }
        let uCW : SubS → List Bool :=
          encDepPair
            (encDepPair (fun _ => encUnary q_r) (fun _ => encodeSignedWord W r_mant))
            (fun _ => encUnary W)
        let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
        let uTm : SubS → List Bool := fun _ =>
          encodeSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
        have pPair := StageEval.snd uCW (encDepPair uIdx uTm)
        have pMul : StageEval (S := SubS) bmIPowReMulSigned (encDepPair uIdx uTm)
            (fun _ => encodeSignedWord W
              (iPowRe m * (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2))
            (fun _ => 1100 * W + 2800) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hm_pow : m < 2 ^ W :=
            lt_of_le_of_lt (by omega : m ≤ W) Nat.lt_two_pow_self
          exact bmIPowReMulSigned_computesInTime W m (by omega) hm_pow _
            ((hT_fits m hm').mono (by dsimp [q_acc, q_r]; omega)) u2 u3 u4 u5 uSc
        refine (StageEval.seq pPair pMul).mono (fun _ => ?_)
        dsimp only [uCW, uIdx, uTm]
        have hqr_le : q_r ≤ W := by dsimp [q_r]; omega
        simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
        omega)
      (fun _ m hm => by
        rw [fitsSignedWord_iff_abs_lt, abs_mul]
        have hi := abs_iPowRe_int_le_one m
        have ha := (fitsSignedWord_iff_abs_lt _ _).mp (hT_fits m hm)
        have hnn := abs_nonneg (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
        have h1 : |iPowRe m| *
            |(buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2| <
            (2 : ℤ) ^ (q_acc + 22) := by nlinarith only [hi, ha, hnn]
        exact lt_of_lt_of_le h1 (pow_le_pow_right₀ (by decide) (by dsimp [q_acc, q_r]; omega)))
      (fun _ m hm => by
        have hm1_pow : m + 1 ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
        have hsum := fitsSignedWord_sum_range (w := q_acc + 22) (m + 1) hm1_pow
          (fun j => iPowRe j * (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) j).2)
          (fun j hj => by
            rw [fitsSignedWord_iff_abs_lt, abs_mul]
            have hi := abs_iPowRe_int_le_one j
            have ha := (fitsSignedWord_iff_abs_lt _ _).mp (hT_fits j (by omega))
            have hnn := abs_nonneg (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) j).2
            nlinarith only [hi, ha, hnn])
        exact hsum.mono (by dsimp [q_acc, q_r] at *; omega)))
  have pImSum := StageEval.seq pRecIn
    (StageEval.expRecurrenceSumWith (S := St) hmul
      (fun _ => 10) (fun _ => W) (fun _ => q_r) (fun _ => q_acc) (fun _ => M) (fun _ => r_mant)
      (fun _ m T_m => iPowIm m * T_m) (fun _ => 1300 * W + 3200)
      (fun _ => hr_bound)
      (fun _ => by dsimp [q_acc, q_r]; omega)
      (fun _ => by dsimp [q_acc, q_r]; omega)
      (fun _ => by dsimp [q_r]; omega)
      (fun m => by
        let SubS := { s : St // m ≤ M }
        let uCW : SubS → List Bool :=
          encDepPair
            (encDepPair (fun _ => encUnary q_r) (fun _ => encodeSignedWord W r_mant))
            (fun _ => encUnary W)
        let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
        let uTm : SubS → List Bool := fun _ =>
          encodeSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
        have pPair := StageEval.snd uCW (encDepPair uIdx uTm)
        have pMul : StageEval (S := SubS) bmIPowImMulSigned (encDepPair uIdx uTm)
            (fun _ => encodeSignedWord W
              (iPowIm m * (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2))
            (fun _ => 1100 * W + 2800) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hm_pow : m < 2 ^ W :=
            lt_of_le_of_lt (by omega : m ≤ W) Nat.lt_two_pow_self
          exact bmIPowImMulSigned_computesInTime W m (by omega) hm_pow _
            ((hT_fits m hm').mono (by dsimp [q_acc, q_r]; omega)) u2 u3 u4 u5 uSc
        refine (StageEval.seq pPair pMul).mono (fun _ => ?_)
        dsimp only [uCW, uIdx, uTm]
        have hqr_le : q_r ≤ W := by dsimp [q_r]; omega
        simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
        omega)
      (fun _ m hm => by
        rw [fitsSignedWord_iff_abs_lt, abs_mul]
        have hi := abs_iPowIm_int_le_one m
        have ha := (fitsSignedWord_iff_abs_lt _ _).mp (hT_fits m hm)
        have hnn := abs_nonneg (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
        have h1 : |iPowIm m| *
            |(buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2| <
            (2 : ℤ) ^ (q_acc + 22) := by nlinarith only [hi, ha, hnn]
        exact lt_of_lt_of_le h1 (pow_le_pow_right₀ (by decide) (by dsimp [q_acc, q_r]; omega)))
      (fun _ m hm => by
        have hm1_pow : m + 1 ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
        have hsum := fitsSignedWord_sum_range (w := q_acc + 22) (m + 1) hm1_pow
          (fun j => iPowIm j * (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) j).2)
          (fun j hj => by
            rw [fitsSignedWord_iff_abs_lt, abs_mul]
            have hi := abs_iPowIm_int_le_one j
            have ha := (fitsSignedWord_iff_abs_lt _ _).mp (hT_fits j (by omega))
            have hnn := abs_nonneg (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) j).2
            nlinarith only [hi, ha, hnn])
        exact hsum.mono (by dsimp [q_acc, q_r] at *; omega)))
  set arr := expTermArrayFixed q_r q_acc M r_mant
  set reSum : ℤ := ∑ m ∈ Finset.range (M + 1), iPowRe m * arr.getD m 0
  set imSum : ℤ := ∑ m ∈ Finset.range (M + 1), iPowIm m * arr.getD m 0
  have hreSum_fits : FitsSignedWord W reSum := by
    have hM1_pow : M + 1 ≤ 2 ^ (M + 1) := le_of_lt Nat.lt_two_pow_self
    have hsum := fitsSignedWord_sum_range (w := q_acc + 22) (M + 1) hM1_pow
      (fun m => iPowRe m * arr.getD m 0)
      (fun m hm => by
        rw [fitsSignedWord_iff_abs_lt, abs_mul]
        have hi := abs_iPowRe_int_le_one m
        have ha : |arr.getD m 0| < (2 : ℤ) ^ (q_acc + 22) :=
          lt_of_le_of_lt (abs_expTermArrayFixed_getD_le 10 q_r q_acc M r_mant hr_bound
            (by dsimp [q_acc, q_r]; omega) m)
            (pow_lt_pow_right₀ (by decide) (by omega))
        have hnn := abs_nonneg (arr.getD m 0)
        nlinarith only [hi, ha, hnn])
    exact hsum.mono (by dsimp [q_acc, q_r]; omega)
  have himSum_fits : FitsSignedWord W imSum := by
    have hM1_pow : M + 1 ≤ 2 ^ (M + 1) := le_of_lt Nat.lt_two_pow_self
    have hsum := fitsSignedWord_sum_range (w := q_acc + 22) (M + 1) hM1_pow
      (fun m => iPowIm m * arr.getD m 0)
      (fun m hm => by
        rw [fitsSignedWord_iff_abs_lt, abs_mul]
        have hi := abs_iPowIm_int_le_one m
        have ha : |arr.getD m 0| < (2 : ℤ) ^ (q_acc + 22) :=
          lt_of_le_of_lt (abs_expTermArrayFixed_getD_le 10 q_r q_acc M r_mant hr_bound
            (by dsimp [q_acc, q_r]; omega) m)
            (pow_lt_pow_right₀ (by decide) (by omega))
        have hnn := abs_nonneg (arr.getD m 0)
        nlinarith only [hi, ha, hnn])
    exact hsum.mono (by dsimp [q_acc, q_r]; omega)
  have pReShift := StageEval.seq (StageEval.fanout pQ pReSum)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime q W reSum hreSum_fits))
  have pImShift := StageEval.seq (StageEval.fanout pQ pImSum)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime q W imSum himSum_fits))
  have hqacc_lt_W : q_acc < W := by dsimp [q_acc, q_r]; omega
  have pTwoPowQAcc := StageEval.seq (StageEval.fanout pW pQAcc)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W q_acc (by omega) hqacc_lt_W))
  have h2qacc_fits : FitsSignedWord W ((2 : ℤ) ^ q_acc) :=
    (FitsSignedWord.two_pow q_acc).mono (by dsimp [q_acc, q_r]; omega)
  have hreShift_fits : FitsSignedWord (q + W) (reSum * (2 : ℤ) ^ q) := by
    simpa [Nat.add_comm] using hreSum_fits.mul_two_pow q
  have himShift_fits : FitsSignedWord (q + W) (imSum * (2 : ℤ) ^ q) := by
    simpa [Nat.add_comm] using himSum_fits.mul_two_pow q
  have hout_bds : WordWidthBounds WOut (expTwoPiIFixed q num den) := by
    have h1 : WordWidthBounds (q + 2) (expTwoPiIFixed q num den) := by
      apply wordWidthBounds_of_approx_norm_le_one (norm_expTwoPiI ((num : ℝ) / (den : ℝ))).le
      have herr : ‖(expTwoPiIFixed q num den).toComplex - expTwoPiI ((num : ℝ) / (den : ℝ))‖ ≤
          (18 / 25 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) := by
        rw [show expTwoPiIFixed q = expTwoPiIRatFixed q from
          expTwoPiIFixedWithMul_eq_expTwoPiIRatFixed q]
        exact norm_expTwoPiIRatFixed_sub_expTwoPiI_le q num hden_pos
      have hq1 : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      linarith only [herr, hq1]
    exact h1.mono hWOut
  have hroot_eq : expTwoPiIFixed q num den =
      ⟨roundDivInt (reSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc),
       roundDivInt (imSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)⟩ := by
    unfold expTwoPiIFixed expTwoPiIFixedWithMul
    dsimp only
    rw [if_neg (ne_of_gt hden_pos), ← hqpi_eq, ← hM_eq, ← hqacc_eq,
      expTermArrayFixedWithMul_mul_eq]
  have hreOut_fits : FitsSignedWord WOut (roundDivInt (reSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)) := by
    have := hout_bds.1; rwa [hroot_eq] at this
  have himOut_fits : FitsSignedWord WOut (roundDivInt (imSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)) := by
    have := hout_bds.2; rwa [hroot_eq] at this
  have pReOut := StageEval.seq (StageEval.fanout pWOut (StageEval.fanout pReShift pTwoPowQAcc))
    (StageEval.const (S := St)
      (bmRoundDivResize_computesInTime WOut (q + W) W
        (reSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc) hreShift_fits h2qacc_fits hreOut_fits))
  have pImOut := StageEval.seq (StageEval.fanout pWOut (StageEval.fanout pImShift pTwoPowQAcc))
    (StageEval.const (S := St)
      (bmRoundDivResize_computesInTime WOut (q + W) W
        (imSum * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc) himShift_fits h2qacc_fits himOut_fits))
  have hall := StageEval.congr_out
    (v2 := fun _ => encComplex WOut (expTwoPiIFixed q num den))
    (StageEval.fanout pReOut pImOut)
    (fun _ => by rw [hroot_eq]; rfl)
  have hq_le : q ≤ W := by omega
  have hM_le : M ≤ W := by omega
  have hqr_le : q_r ≤ W := by dsimp [q_r]; omega
  have hqacc_le : q_acc ≤ W := by dsimp [q_acc, q_r]; omega
  have hqpi_le : q_pi ≤ W := by dsimp [q_pi]; omega
  have hlen_uWQ : (uWQ ()).length ≤ 8 * W + 8 := by
    dsimp only [uWQ]; simp only [length_encDepPair, length_encUnary]; omega
  have hlen_uHdr : (uHdr ()).length ≤ 20 * W + 20 := by
    dsimp only [uHdr]; simp only [length_encDepPair, length_encUnary]; omega
  have hlen_uFst : (uFst ()).length ≤ 44 * W + 48 := by
    dsimp only [uFst]; simp only [length_encDepPair, length_encodeSignedWord]; omega
  have hlen_uSnd : (uSnd ()).length ≤ 8 * W + 16 := by
    dsimp only [uSnd]; simp only [length_encDepPair, length_encodeSignedWord]; omega
  have hlen_uIn : (uIn ()).length ≤ 104 * W + 132 := by
    dsimp only [uIn]; simp only [length_encDepPair]; omega
  have hsq1 : 300 * (q_r + (1 + 2 * W) + (q_pi + W)) * (q_r + (1 + 2 * W) + (q_pi + W)) ≤
      7500 * W * W + 3000 * W + 300 := by
    nlinarith only [hqr_le, hqpi_le]
  have hsq2 : 300 * (q + W + W) * (q + W + W) ≤ 2700 * W * W := by
    nlinarith only [hq_le]
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uFst, uSnd, uHdr, uWQ, q_r, q_acc, q_pi, id] at hcomp
  dsimp only [id] at ht
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  have hmulM :
      (M + 1) * (2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000) +
        (M + 1) * (2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000) ≤
      (q + 58) * (4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000) := by
    have hM1 : M + 1 = q + 58 := by omega
    rw [hM1]
    have h1 := Nat.mul_le_mul_left (q + 58)
      (show 2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000 +
              (2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000) ≤
            4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000 by nlinarith only [])
    have h2 :
        (q + 58) * (2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000) +
          (q + 58) * (2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000) =
        (q + 58) * (2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000 +
          (2 * mulTime W + (1300 * W + 3200) + 5000 * W * W + 450000 * W + 500000)) := by ring
    linarith only [h1, h2]
  have ht_bound : t ≤ (q + 58) * (4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000) +
      4 * mulTime W + 30000 * W * W + 2000000 * W + 2000000 := by
    nlinarith only [ht, hmulM, hsq1, hsq2, hlen_uWQ, hlen_uHdr, hlen_uFst, hlen_uSnd,
      hlen_uIn, hqr_le, hqpi_le, hqacc_le, hq_le, hM_le, hWOut_le]
  exact ⟨t, ht_bound, hcomp⟩

/-- **Pure-Integer Clamped $\operatorname{sinc}$ Taylor Stage (`bmSincTaylorWith bmMul`)**:
Consumes `((W, N), (θNum, θDen))` on `kIO` (`encodeSignedWord W θNum`, `encodeSignedWord W θDen`)
and emits `encodeSignedWord W (sincTaylorFixed N θNum θDen)` in
$O((N + 7) \cdot (M_{\text{mul}}(W) + W^2))$ `TM2.step` transitions. -/
def bmSincTaylorWith (bmMul : BitMachine) : BitMachine :=
  let bmW := bmSeq bmFst bmFst
  let bmN := bmSeq bmFst bmSnd
  let bmThetaNum := bmSeq bmSnd bmFst
  let bmThetaDen := bmSeq bmSnd bmSnd
  let bmM := bmSeq (bmFanout bmN (bmUnaryConst 6)) bmUnaryAdd
  let bmQR := bmSeq bmM bmUnaryDouble
  let bmQAcc := bmSeq (bmFanout (bmSeq (bmFanout bmM bmQR) bmUnaryAdd) (bmUnaryConst 6)) bmUnaryAdd
  let bmThetaShift := bmSeq (bmFanout bmQR bmThetaNum) bmShiftLeftSigned
  let bmRMant := bmSeq (bmFanout bmW (bmFanout bmThetaShift bmThetaDen)) bmRoundDivResize
  let bmRecIn := bmFanout (bmFanout (bmFanout (bmFanout bmQR bmRMant) bmW) bmM) bmQAcc
  let bmM1 := bmSeq (bmSeq bmSnd bmFst) bmSignedSucc
  let bmDiv := bmSeq (bmFanout (bmSeq bmSnd bmSnd) bmM1) bmRoundDivInt
  let bmTermSinc := bmSeq (bmFanout bmM1 bmDiv) bmIPowImMulSigned
  let bmSRaw := bmSeq bmRecIn (bmExpRecurrenceSumWith bmMul bmTermSinc)
  let bmTwoPow := bmSeq (bmFanout bmW bmQAcc) bmSignedTwoPow
  let bmNegTwoPow := bmSeq bmTwoPow bmSignedNeg
  bmSeq (bmFanout bmNegTwoPow (bmSeq (bmFanout bmTwoPow bmSRaw) bmSignedMin)) bmSignedMax

set_option maxHeartbeats 800000 in
theorem bmSincTaylorWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (B W N : ℕ) (θNum θDen : ℤ)
    (hθNum : FitsSignedWord W θNum) (hθDen : FitsSignedWord W θDen)
    (hden_pos : 0 < θDen) (hθ_le : |θNum| ≤ (B : ℤ) * θDen)
    (hW_T : (3 * (N + 6) + 6) + 2 * B + (N + 6) + 4 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (N + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
        15000 * W * W + 1000000 * W + 1000000,
      (bmSincTaylorWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encodeSignedWord W) (encodeSignedWord W))
            ((W, N), (θNum, θDen))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (sincTaylorFixed N θNum θDen)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let St := Unit
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := (M + q_r) + 6
  have hqacc_eq : q_acc = 3 * M + 6 := by dsimp [q_acc, q_r]; omega
  let uWN : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary N)
  let uTh : St → List Bool :=
    encDepPair (fun _ => encodeSignedWord W θNum) (fun _ => encodeSignedWord W θDen)
  let uIn : St → List Bool := encDepPair uWN uTh
  have pWN := StageEval.fst uWN uTh
  have pTh := StageEval.snd uWN uTh
  have pW := StageEval.seq pWN (StageEval.fst (fun _ : St => encUnary W) (fun _ => encUnary N))
  have pN := StageEval.seq pWN (StageEval.snd (fun _ : St => encUnary W) (fun _ => encUnary N))
  have pThetaNum := StageEval.seq pTh
    (StageEval.fst (fun _ : St => encodeSignedWord W θNum) (fun _ => encodeSignedWord W θDen))
  have pThetaDen := StageEval.seq pTh
    (StageEval.snd (fun _ : St => encodeSignedWord W θNum) (fun _ => encodeSignedWord W θDen))
  have pM := StageEval.seq (StageEval.fanout pN (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (N, 6)))
  have pQR := StageEval.seq pM
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => M))
  have pMQR := StageEval.seq (StageEval.fanout pM pQR)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M, q_r)))
  have pQAcc := StageEval.seq (StageEval.fanout pMQR (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M + q_r, 6)))
  have pThetaShift := StageEval.seq (StageEval.fanout pQR pThetaNum)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime q_r W θNum hθNum))
  have hthetaShift_fits : FitsSignedWord (q_r + W) (θNum * (2 : ℤ) ^ q_r) := by
    simpa [Nat.add_comm] using hθNum.mul_two_pow q_r
  set r_mant : ℤ := roundDivInt (θNum * (2 : ℤ) ^ q_r) θDen
  have hr_bound : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r :=
    abs_roundDivInt_mul_two_pow_le_of_pos B q_r hden_pos hθ_le
  have hr_fits : FitsSignedWord W r_mant :=
    fitsSignedWord_of_abs_le_mul_two_pow hr_bound (by dsimp [q_r, M] at *; omega)
  have pRMant := StageEval.seq (StageEval.fanout pW (StageEval.fanout pThetaShift pThetaDen))
    (StageEval.const (S := St)
      (bmRoundDivResize_computesInTime W (q_r + W) W
        (θNum * (2 : ℤ) ^ q_r) θDen hthetaShift_fits hθDen hr_fits))
  have pRecIn := StageEval.fanout
    (StageEval.fanout (StageEval.fanout (StageEval.fanout pQR pRMant) pW) pM) pQAcc
  have hT_fits : ∀ m ≤ M,
      FitsSignedWord (q_acc + 2 * B + 2)
        (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 := by
    intro m hm
    exact fitsSignedWord_buildRecurrenceArray_expTermStepFixed B q_r q_acc r_mant hr_bound
      (by dsimp [q_acc, q_r, M] at *; omega) (le_refl _)
  have hterm_fits_q : ∀ m ≤ M,
      FitsSignedWord (q_acc + 2 * B + 2)
        (iPowIm (m + 1) *
          roundDivInt
            (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
            ((m + 1 : ℕ) : ℤ)) := by
    intro m hm
    rw [fitsSignedWord_iff_abs_lt, abs_mul]
    have hi := abs_iPowIm_int_le_one (m + 1)
    have hd : FitsSignedWord (q_acc + 2 * B + 2)
        (roundDivInt
          (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
          ((m + 1 : ℕ) : ℤ)) :=
      (hT_fits m hm).roundDivInt _
    have ha := (fitsSignedWord_iff_abs_lt _ _).mp hd
    nlinarith [abs_nonneg (roundDivInt (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 ((m + 1 : ℕ) : ℤ))]
  have pSRaw := StageEval.seq pRecIn
    (StageEval.expRecurrenceSumWith (S := St) hmul
      (fun _ => B) (fun _ => W) (fun _ => q_r) (fun _ => q_acc) (fun _ => M) (fun _ => r_mant)
      (fun _ m T_m => iPowIm (m + 1) * roundDivInt T_m ((m + 1 : ℕ) : ℤ))
      (fun _ => 250 * W * W + 70000 * W + 175000)
      (fun _ => hr_bound)
      (fun _ => by dsimp [q_acc, q_r]; omega)
      (fun _ => by dsimp [q_acc, q_r, M] at *; omega)
      (fun _ => by dsimp [q_r, M] at *; omega)
      (fun m => by
        let SubS := { s : St // m ≤ M }
        let uCW : SubS → List Bool :=
          encDepPair
            (encDepPair (fun _ => encUnary q_r) (fun _ => encodeSignedWord W r_mant))
            (fun _ => encUnary W)
        let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
        let uTm : SubS → List Bool := fun _ =>
          encodeSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
        have pPair := StageEval.snd uCW (encDepPair uIdx uTm)
        have pIdx := StageEval.seq pPair (StageEval.fst uIdx uTm)
        have pTm := StageEval.seq pPair (StageEval.snd uIdx uTm)
        have pM1Sub : StageEval (S := SubS) bmSignedSucc uIdx
            (fun _ => encodeSignedWord W ((m + 1 : ℕ) : ℤ))
            (fun _ => 800 * W + 2000) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hf0 : FitsSignedWord W (m : ℤ) := by
            rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : m ≤ W) Nat.lt_two_pow_self
          have hf1 : FitsSignedWord W ((m : ℤ) + 1) := by
            have : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
            rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : m + 1 ≤ W) Nat.lt_two_pow_self
          rcases bmSignedSucc_computesInTime W (by omega) (m : ℤ) hf0 hf1 u2 u3 u4 u5 uSc
            with ⟨t, ht, hc⟩
          have hcast : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
          rw [hcast] at hc
          exact ⟨t, ht, hc⟩
        have pM1 := StageEval.seq pIdx pM1Sub
        have pDivSub : StageEval (S := SubS) bmRoundDivInt
            (encDepPair uTm (fun _ => encodeSignedWord W ((m + 1 : ℕ) : ℤ)))
            (fun _ => encodeSignedWord W
              (roundDivInt
                (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
                ((m + 1 : ℕ) : ℤ)))
            (fun _ => 250 * W * W + 60000 * W + 150000) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hf1 : FitsSignedWord W ((m + 1 : ℕ) : ℤ) := by
            rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : m + 1 ≤ W) Nat.lt_two_pow_self
          exact bmRoundDivInt_computesInTime W _ _
            ((hT_fits m hm').mono (by dsimp [q_acc, q_r, M] at *; omega)) hf1 u2 u3 u4 u5 uSc
        have pDiv := StageEval.seq (StageEval.fanout pTm pM1) pDivSub
        have pMulSub : StageEval (S := SubS) bmIPowImMulSigned
            (encDepPair (fun _ => encodeSignedWord W ((m + 1 : ℕ) : ℤ))
              (fun _ => encodeSignedWord W
                (roundDivInt
                  (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
                  ((m + 1 : ℕ) : ℤ))))
            (fun _ => encodeSignedWord W
              (iPowIm (m + 1) *
                roundDivInt
                  (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
                  ((m + 1 : ℕ) : ℤ)))
            (fun _ => 1100 * W + 2800) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hm1_pow : m + 1 < 2 ^ W :=
            lt_of_le_of_lt (by dsimp [M] at *; omega : m + 1 ≤ W) Nat.lt_two_pow_self
          have hd_fits : FitsSignedWord W
              (roundDivInt
                (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
                ((m + 1 : ℕ) : ℤ)) :=
            ((hT_fits m hm').roundDivInt _).mono (by dsimp [q_acc, q_r, M] at *; omega)
          exact bmIPowImMulSigned_computesInTime W (m + 1) (by omega) hm1_pow _ hd_fits
            u2 u3 u4 u5 uSc
        refine (StageEval.seq (StageEval.fanout pM1 pDiv) pMulSub).mono (fun _ => ?_)
        dsimp only [uCW, uIdx, uTm]
        have hqr_le : q_r ≤ W := by dsimp [q_r, M] at *; omega
        simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
        omega)
      (fun _ m hm => (hterm_fits_q m hm).mono (by dsimp [q_acc, q_r, M] at *; omega))
      (fun _ m hm => by
        have hm1_pow : m + 1 ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
        have hsum := fitsSignedWord_sum_range (w := q_acc + 2 * B + 2) (m + 1) hm1_pow
          (fun j => iPowIm (j + 1) *
            roundDivInt
              (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) j).2
              ((j + 1 : ℕ) : ℤ))
          (fun j hj => hterm_fits_q j (by omega))
        exact hsum.mono (by dsimp [q_acc, q_r, M] at *; omega)))
  set arr := expTermArrayFixed q_r q_acc M r_mant
  set sRaw : ℤ := ∑ m ∈ Finset.range (M + 1),
    iPowIm (m + 1) * roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ)
  have hsRaw_fits : FitsSignedWord W sRaw := by
    have hM1_pow : M + 1 ≤ 2 ^ (M + 1) := le_of_lt Nat.lt_two_pow_self
    have hsum := fitsSignedWord_sum_range (w := q_acc + 2 * B + 2) (M + 1) hM1_pow
      (fun m => iPowIm (m + 1) * roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ))
      (fun m _ => by
        rw [fitsSignedWord_iff_abs_lt, abs_mul]
        have hi := abs_iPowIm_int_le_one (m + 1)
        have ha : FitsSignedWord (q_acc + 2 * B + 2) (arr.getD m 0) := by
          rw [fitsSignedWord_iff_abs_lt]
          exact lt_of_le_of_lt (abs_expTermArrayFixed_getD_le B q_r q_acc M r_mant hr_bound
            (by dsimp [q_acc, q_r]; omega) m)
            (pow_lt_pow_right₀ (by decide) (by omega))
        have hd := (fitsSignedWord_iff_abs_lt _ _).mp (ha.roundDivInt ((m + 1 : ℕ) : ℤ))
        nlinarith [abs_nonneg (roundDivInt (arr.getD m 0) ((m + 1 : ℕ) : ℤ))])
    exact hsum.mono (by dsimp [q_acc, q_r, M] at *; omega)
  have hqacc_lt_W : q_acc < W := by dsimp [q_acc, q_r, M] at *; omega
  have h2qacc_fits : FitsSignedWord W ((2 : ℤ) ^ q_acc) :=
    (FitsSignedWord.two_pow q_acc).mono (by dsimp [q_acc, q_r, M] at *; omega)
  have hneg2qacc_fits : FitsSignedWord W (-(2 : ℤ) ^ q_acc) := h2qacc_fits.neg
  have pTwoPow := StageEval.seq (StageEval.fanout pW pQAcc)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W q_acc (by omega) hqacc_lt_W))
  have pNegTwoPow := StageEval.seq pTwoPow
    (StageEval.const (S := St) (bmSignedNeg_computesInTime W ((2 : ℤ) ^ q_acc) h2qacc_fits))
  have pMin := StageEval.seq (StageEval.fanout pTwoPow pSRaw)
    (StageEval.const (S := St)
      (bmSignedMin_computesInTime W ((2 : ℤ) ^ q_acc) sRaw h2qacc_fits hsRaw_fits))
  have hmin_fits : FitsSignedWord W (min ((2 : ℤ) ^ q_acc) sRaw) := by
    rcases min_cases ((2 : ℤ) ^ q_acc) sRaw with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · exact h2qacc_fits
    · exact hsRaw_fits
  have pMax := StageEval.seq (StageEval.fanout pNegTwoPow pMin)
    (StageEval.const (S := St)
      (bmSignedMax_computesInTime W (-(2 : ℤ) ^ q_acc) (min ((2 : ℤ) ^ q_acc) sRaw)
        hneg2qacc_fits hmin_fits))
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W (sincTaylorFixed N θNum θDen))
    pMax
    (fun _ => by
      unfold sincTaylorFixed sincTaylorFixedWithMul
      dsimp only
      rw [← hqacc_eq, expTermArrayFixedWithMul_mul_eq])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uWN, uTh, M, q_r, q_acc, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  have hmulM :
      (N + 6 + 1) * (2 * mulTime W + (250 * W * W + 70000 * W + 175000) +
        5000 * W * W + 450000 * W + 500000) ≤
      (N + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) :=
    Nat.mul_le_mul_left (N + 7) (by nlinarith)
  exact ⟨t, by nlinarith, hcomp⟩

/-- **Pure-Integer Clamped $\exp$ Taylor Stage (`bmExpTaylorWith bmMul`)**:
Consumes `((W, N), (gNum, gDen))` on `kIO` (`encodeSignedWord W gNum`, `encodeSignedWord W gDen`)
and emits `encodeSignedWord W (expTaylorFixed N gNum gDen)` in
$O((N + 7) \cdot (M_{\text{mul}}(W) + W^2))$ `TM2.step` transitions. -/
def bmExpTaylorWith (bmMul : BitMachine) : BitMachine :=
  let bmW := bmSeq bmFst bmFst
  let bmN := bmSeq bmFst bmSnd
  let bmGNum := bmSeq bmSnd bmFst
  let bmGDen := bmSeq bmSnd bmSnd
  let bmM := bmSeq (bmFanout bmN (bmUnaryConst 6)) bmUnaryAdd
  let bmQR := bmSeq bmM bmUnaryDouble
  let bmQAcc := bmSeq (bmFanout (bmSeq (bmFanout bmM bmQR) bmUnaryAdd) (bmUnaryConst 6)) bmUnaryAdd
  let bmGShift := bmSeq (bmFanout bmQR bmGNum) bmShiftLeftSigned
  let bmRMant := bmSeq (bmFanout bmW (bmFanout bmGShift bmGDen)) bmRoundDivResize
  let bmRecIn := bmFanout (bmFanout (bmFanout (bmFanout bmQR bmRMant) bmW) bmM) bmQAcc
  let bmERaw := bmSeq bmRecIn (bmExpRecurrenceSumWith bmMul (bmSeq bmSnd bmSnd))
  let bmTwoPow := bmSeq (bmFanout bmW bmQAcc) bmSignedTwoPow
  bmSeq (bmSeq (bmFanout bmTwoPow bmERaw) bmSignedMin) bmSignedMaxZero

set_option maxHeartbeats 800000 in
theorem bmExpTaylorWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (B W N : ℕ) (gNum gDen : ℤ)
    (hgNum : FitsSignedWord W gNum) (hgDen : FitsSignedWord W gDen)
    (hden_pos : 0 < gDen) (hg_le : |gNum| ≤ (B : ℤ) * gDen)
    (hW_T : (3 * (N + 6) + 6) + 2 * B + (N + 6) + 4 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (N + 7) * (2 * mulTime W + 5500 * W * W + 500000 * W + 600000) +
        15000 * W * W + 1000000 * W + 1000000,
      (bmExpTaylorWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encodeSignedWord W) (encodeSignedWord W))
            ((W, N), (gNum, gDen))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (expTaylorFixed N gNum gDen)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let St := Unit
  let M : ℕ := N + 6
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := (M + q_r) + 6
  have hqacc_eq : q_acc = 3 * M + 6 := by dsimp [q_acc, q_r]; omega
  let uWN : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary N)
  let uG : St → List Bool :=
    encDepPair (fun _ => encodeSignedWord W gNum) (fun _ => encodeSignedWord W gDen)
  let uIn : St → List Bool := encDepPair uWN uG
  have pWN := StageEval.fst uWN uG
  have pG := StageEval.snd uWN uG
  have pW := StageEval.seq pWN (StageEval.fst (fun _ : St => encUnary W) (fun _ => encUnary N))
  have pN := StageEval.seq pWN (StageEval.snd (fun _ : St => encUnary W) (fun _ => encUnary N))
  have pGNum := StageEval.seq pG
    (StageEval.fst (fun _ : St => encodeSignedWord W gNum) (fun _ => encodeSignedWord W gDen))
  have pGDen := StageEval.seq pG
    (StageEval.snd (fun _ : St => encodeSignedWord W gNum) (fun _ => encodeSignedWord W gDen))
  have pM := StageEval.seq (StageEval.fanout pN (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (N, 6)))
  have pQR := StageEval.seq pM
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => M))
  have pMQR := StageEval.seq (StageEval.fanout pM pQR)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M, q_r)))
  have pQAcc := StageEval.seq (StageEval.fanout pMQR (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M + q_r, 6)))
  have pGShift := StageEval.seq (StageEval.fanout pQR pGNum)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime q_r W gNum hgNum))
  have hgShift_fits : FitsSignedWord (q_r + W) (gNum * (2 : ℤ) ^ q_r) := by
    simpa [Nat.add_comm] using hgNum.mul_two_pow q_r
  set r_mant : ℤ := roundDivInt (gNum * (2 : ℤ) ^ q_r) gDen
  have hr_bound : |r_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_r :=
    abs_roundDivInt_mul_two_pow_le_of_pos B q_r hden_pos hg_le
  have hr_fits : FitsSignedWord W r_mant :=
    fitsSignedWord_of_abs_le_mul_two_pow hr_bound (by dsimp [q_r, M] at *; omega)
  have pRMant := StageEval.seq (StageEval.fanout pW (StageEval.fanout pGShift pGDen))
    (StageEval.const (S := St)
      (bmRoundDivResize_computesInTime W (q_r + W) W
        (gNum * (2 : ℤ) ^ q_r) gDen hgShift_fits hgDen hr_fits))
  have pRecIn := StageEval.fanout
    (StageEval.fanout (StageEval.fanout (StageEval.fanout pQR pRMant) pW) pM) pQAcc
  have hT_fits : ∀ m ≤ M,
      FitsSignedWord (q_acc + 2 * B + 2)
        (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 := by
    intro m hm
    exact fitsSignedWord_buildRecurrenceArray_expTermStepFixed B q_r q_acc r_mant hr_bound
      (by dsimp [q_acc, q_r, M] at *; omega) (le_refl _)
  have pERaw := StageEval.seq pRecIn
    (StageEval.expRecurrenceSumWith (S := St) hmul
      (fun _ => B) (fun _ => W) (fun _ => q_r) (fun _ => q_acc) (fun _ => M) (fun _ => r_mant)
      (fun _ _ T_m => T_m)
      (fun _ => 200 * W + 400)
      (fun _ => hr_bound)
      (fun _ => by dsimp [q_acc, q_r]; omega)
      (fun _ => by dsimp [q_acc, q_r, M] at *; omega)
      (fun _ => by dsimp [q_r, M] at *; omega)
      (fun m => by
        let SubS := { s : St // m ≤ M }
        let uCW : SubS → List Bool :=
          encDepPair
            (encDepPair (fun _ => encUnary q_r) (fun _ => encodeSignedWord W r_mant))
            (fun _ => encUnary W)
        let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
        let uTm : SubS → List Bool := fun _ =>
          encodeSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
        have pPair := StageEval.snd uCW (encDepPair uIdx uTm)
        have pTm := StageEval.seq pPair (StageEval.snd uIdx uTm)
        refine pTm.mono (fun _ => ?_)
        dsimp only [uCW, uIdx, uTm]
        have hqr_le : q_r ≤ W := by dsimp [q_r, M] at *; omega
        simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
        omega)
      (fun _ m hm => (hT_fits m hm).mono (by dsimp [q_acc, q_r, M] at *; omega))
      (fun _ m hm => by
        have hm1_pow : m + 1 ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
        have hsum := fitsSignedWord_sum_range (w := q_acc + 2 * B + 2) (m + 1) hm1_pow
          (fun j => (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) j).2)
          (fun j hj => hT_fits j (by omega))
        exact hsum.mono (by dsimp [q_acc, q_r, M] at *; omega)))
  set arr := expTermArrayFixed q_r q_acc M r_mant
  set eRaw : ℤ := ∑ m ∈ Finset.range (M + 1), arr.getD m 0
  have heRaw_fits : FitsSignedWord W eRaw := by
    have hM1_pow : M + 1 ≤ 2 ^ (M + 1) := le_of_lt Nat.lt_two_pow_self
    have hsum := fitsSignedWord_sum_range (w := q_acc + 2 * B + 2) (M + 1) hM1_pow
      (fun m => arr.getD m 0)
      (fun m _ => by
        rw [fitsSignedWord_iff_abs_lt]
        exact lt_of_le_of_lt (abs_expTermArrayFixed_getD_le B q_r q_acc M r_mant hr_bound
          (by dsimp [q_acc, q_r]; omega) m)
          (pow_lt_pow_right₀ (by decide) (by omega)))
    exact hsum.mono (by dsimp [q_acc, q_r, M] at *; omega)
  have hqacc_lt_W : q_acc < W := by dsimp [q_acc, q_r, M] at *; omega
  have h2qacc_fits : FitsSignedWord W ((2 : ℤ) ^ q_acc) :=
    (FitsSignedWord.two_pow q_acc).mono (by dsimp [q_acc, q_r, M] at *; omega)
  have pTwoPow := StageEval.seq (StageEval.fanout pW pQAcc)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W q_acc (by omega) hqacc_lt_W))
  have pMin := StageEval.seq (StageEval.fanout pTwoPow pERaw)
    (StageEval.const (S := St)
      (bmSignedMin_computesInTime W ((2 : ℤ) ^ q_acc) eRaw h2qacc_fits heRaw_fits))
  have hmin_fits : FitsSignedWord W (min ((2 : ℤ) ^ q_acc) eRaw) := by
    rcases min_cases ((2 : ℤ) ^ q_acc) eRaw with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · exact h2qacc_fits
    · exact heRaw_fits
  have pMax0 := StageEval.seq pMin
    (StageEval.const (S := St)
      (bmSignedMaxZero_computesInTime W (min ((2 : ℤ) ^ q_acc) eRaw) hmin_fits))
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W (expTaylorFixed N gNum gDen))
    pMax0
    (fun _ => by
      unfold expTaylorFixed expTaylorFixedWithMul
      dsimp only
      rw [← hqacc_eq, expTermArrayFixedWithMul_mul_eq])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uWN, uG, M, q_r, q_acc, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  have hmulM :
      (N + 6 + 1) * (2 * mulTime W + (200 * W + 400) +
        5000 * W * W + 450000 * W + 500000) ≤
      (N + 7) * (2 * mulTime W + 5500 * W * W + 500000 * W + 600000) :=
    Nat.mul_le_mul_left (N + 7) (by nlinarith)
  exact ⟨t, by nlinarith, hcomp⟩

/-- **Pure-Integer $\int_0^z e^{-t^2}\,dt$ Taylor Stage (`bmErfTaylorWith bmMul`)**:
Consumes `((W, N), (zNum, zDen))` on `kIO` (`encodeSignedWord W zNum`, `encodeSignedWord W zDen`)
and emits `encodeSignedWord W (erfIntegralTaylorFixed N zNum zDen)` in
$O((N + 7) \cdot (M_{\text{mul}}(W) + W^2))$ `TM2.step` transitions. -/
def bmErfTaylorWith (bmMul : BitMachine) : BitMachine :=
  let bmW := bmSeq bmFst bmFst
  let bmN := bmSeq bmFst bmSnd
  let bmZNum := bmSeq bmSnd bmFst
  let bmZDen := bmSeq bmSnd bmSnd
  let bmM := bmSeq (bmFanout bmN (bmUnaryConst 6)) bmUnaryAdd
  let bmQR := bmSeq bmM bmUnaryDouble
  let bmQAcc := bmSeq (bmFanout (bmSeq (bmFanout bmM bmQR) bmUnaryAdd) (bmUnaryConst 6)) bmUnaryAdd
  let bmZShift := bmSeq (bmFanout bmM bmZNum) bmShiftLeftSigned
  let bmZMant := bmSeq (bmFanout bmW (bmFanout bmZShift bmZDen)) bmRoundDivResize
  let bmRMant := bmSeq (bmSeq (bmFanout bmZMant bmZMant) (bmSignedMulSameWith bmMul)) bmSignedNeg
  let bmRecIn := bmFanout (bmFanout (bmFanout (bmFanout bmQR bmRMant) bmW) bmM) bmQAcc
  let bmTwoM1 := bmSeq (bmSeq (bmSeq bmSnd bmFst) bmSignedDouble) bmSignedSucc
  let bmTermErf := bmSeq (bmFanout (bmSeq bmSnd bmSnd) bmTwoM1) bmRoundDivInt
  let bmSInner := bmSeq bmRecIn (bmExpRecurrenceSumWith bmMul bmTermErf)
  bmSeq (bmFanout bmZMant bmSInner) (bmSignedMulSameWith bmMul)

set_option maxHeartbeats 800000 in
theorem bmErfTaylorWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (B W N : ℕ) (zNum zDen : ℤ)
    (hzNum : FitsSignedWord W zNum) (hzDen : FitsSignedWord W zDen)
    (hden_pos : 0 < zDen) (hz_le : |zNum| ≤ (B : ℤ) * zDen)
    (hW_all : 5 * (N + 6) + 2 * (B * B) + B + 12 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (N + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
        6 * mulTime W + 20000 * W * W + 1200000 * W + 1500000,
      (bmErfTaylorWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encodeSignedWord W) (encodeSignedWord W))
            ((W, N), (zNum, zDen))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (erfIntegralTaylorFixed N zNum zDen)))
          [] [] tW2 tW3 tW4 tW5 tSch) t ∧
      FitsSignedWord (5 * (N + 6) + 2 * (B * B) + B + 12) (erfIntegralTaylorFixed N zNum zDen) := by
  let St := Unit
  let M : ℕ := N + 6
  let q_z : ℕ := M
  let q_r : ℕ := 2 * M
  let q_acc : ℕ := (M + q_r) + 6
  have hqacc_eq : q_acc = 3 * M + 6 := by dsimp [q_acc, q_r]; omega
  let uWN : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary N)
  let uZ : St → List Bool :=
    encDepPair (fun _ => encodeSignedWord W zNum) (fun _ => encodeSignedWord W zDen)
  let uIn : St → List Bool := encDepPair uWN uZ
  have pWN := StageEval.fst uWN uZ
  have pZ := StageEval.snd uWN uZ
  have pW := StageEval.seq pWN (StageEval.fst (fun _ : St => encUnary W) (fun _ => encUnary N))
  have pN := StageEval.seq pWN (StageEval.snd (fun _ : St => encUnary W) (fun _ => encUnary N))
  have pZNum := StageEval.seq pZ
    (StageEval.fst (fun _ : St => encodeSignedWord W zNum) (fun _ => encodeSignedWord W zDen))
  have pZDen := StageEval.seq pZ
    (StageEval.snd (fun _ : St => encodeSignedWord W zNum) (fun _ => encodeSignedWord W zDen))
  have pM := StageEval.seq (StageEval.fanout pN (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (N, 6)))
  have pQR := StageEval.seq pM
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => M))
  have pMQR := StageEval.seq (StageEval.fanout pM pQR)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M, q_r)))
  have pQAcc := StageEval.seq (StageEval.fanout pMQR (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (M + q_r, 6)))
  have pZShift := StageEval.seq (StageEval.fanout pM pZNum)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime M W zNum hzNum))
  have hzShift_fits : FitsSignedWord (M + W) (zNum * (2 : ℤ) ^ M) := by
    simpa [Nat.add_comm] using hzNum.mul_two_pow M
  set z_mant : ℤ := roundDivInt (zNum * (2 : ℤ) ^ q_z) zDen
  have hz_bound : |z_mant| ≤ (B : ℤ) * (2 : ℤ) ^ q_z :=
    abs_roundDivInt_mul_two_pow_le_of_pos B q_z hden_pos hz_le
  have hz_fits_small : FitsSignedWord (q_z + B + 1) z_mant :=
    fitsSignedWord_of_abs_le_mul_two_pow hz_bound (le_refl _)
  have hz_fits : FitsSignedWord W z_mant :=
    hz_fits_small.mono (by dsimp [q_z, M] at *; omega)
  have pZMant := StageEval.seq (StageEval.fanout pW (StageEval.fanout pZShift pZDen))
    (StageEval.const (S := St)
      (bmRoundDivResize_computesInTime W (M + W) W
        (zNum * (2 : ℤ) ^ M) zDen hzShift_fits hzDen hz_fits))
  set r_mant : ℤ := -(z_mant * z_mant)
  have hr_bound : |r_mant| ≤ ((B * B : ℕ) : ℤ) * (2 : ℤ) ^ q_r := by
    dsimp [r_mant]
    rw [abs_neg, abs_mul]
    calc |z_mant| * |z_mant|
        ≤ ((B : ℤ) * (2 : ℤ) ^ q_z) * ((B : ℤ) * (2 : ℤ) ^ q_z) :=
          mul_le_mul hz_bound hz_bound (abs_nonneg _) (by positivity)
      _ = ((B * B : ℕ) : ℤ) * (2 : ℤ) ^ q_r := by
          dsimp [q_r, q_z]; rw [Nat.two_mul, pow_add]; push_cast; ring
  have hzSq_fits : FitsSignedWord W (z_mant * z_mant) := by
    have hr : FitsSignedWord W r_mant :=
      fitsSignedWord_of_abs_le_mul_two_pow hr_bound (by dsimp [q_r, M] at *; omega)
    dsimp [r_mant] at hr
    simpa using hr.neg
  have hr_fits : FitsSignedWord W r_mant := hzSq_fits.neg
  have pZSq := StageEval.seq (StageEval.fanout pZMant pZMant)
    (StageEval.const (S := St) (bmSignedMulSameWith_computesInTime hmul W z_mant z_mant hz_fits hz_fits hzSq_fits))
  have pRMant := StageEval.seq pZSq
    (StageEval.const (S := St) (bmSignedNeg_computesInTime W (z_mant * z_mant) hzSq_fits))
  have pRecIn := StageEval.fanout
    (StageEval.fanout (StageEval.fanout (StageEval.fanout pQR pRMant) pW) pM) pQAcc
  have hT_fits : ∀ m ≤ M,
      FitsSignedWord (q_acc + 2 * (B * B) + 2)
        (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2 := by
    intro m hm
    exact fitsSignedWord_buildRecurrenceArray_expTermStepFixed (B * B) q_r q_acc r_mant hr_bound
      (by dsimp [q_acc, q_r, M] at *; omega) (le_refl _)
  have pSInner := StageEval.seq pRecIn
    (StageEval.expRecurrenceSumWith (S := St) hmul
      (fun _ => B * B) (fun _ => W) (fun _ => q_r) (fun _ => q_acc) (fun _ => M) (fun _ => r_mant)
      (fun _ m T_m => roundDivInt T_m ((2 * m + 1 : ℕ) : ℤ))
      (fun _ => 250 * W * W + 65000 * W + 165000)
      (fun _ => hr_bound)
      (fun _ => by dsimp [q_acc, q_r]; omega)
      (fun _ => by dsimp [q_acc, q_r, M] at *; omega)
      (fun _ => by dsimp [q_r, M] at *; omega)
      (fun m => by
        let SubS := { s : St // m ≤ M }
        let uCW : SubS → List Bool :=
          encDepPair
            (encDepPair (fun _ => encUnary q_r) (fun _ => encodeSignedWord W r_mant))
            (fun _ => encUnary W)
        let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (m : ℤ)
        let uTm : SubS → List Bool := fun _ =>
          encodeSignedWord W
            (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
        have pPair := StageEval.snd uCW (encDepPair uIdx uTm)
        have pIdx := StageEval.seq pPair (StageEval.fst uIdx uTm)
        have pTm := StageEval.seq pPair (StageEval.snd uIdx uTm)
        have pTwoMSub : StageEval (S := SubS) bmSignedDouble uIdx
            (fun _ => encodeSignedWord W (2 * (m : ℤ)))
            (fun _ => 600 * W + 1400) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hf0 : FitsSignedWord W (m : ℤ) := by
            rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : m ≤ W) Nat.lt_two_pow_self
          have hf2 : FitsSignedWord W (2 * (m : ℤ)) := by
            have : 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) := by push_cast; rfl
            rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : 2 * m ≤ W) Nat.lt_two_pow_self
          exact bmSignedDouble_computesInTime W (m : ℤ) hf0 hf2 u2 u3 u4 u5 uSc
        have pTwoM1Sub : StageEval (S := SubS) bmSignedSucc
            (fun _ => encodeSignedWord W (2 * (m : ℤ)))
            (fun _ => encodeSignedWord W ((2 * m + 1 : ℕ) : ℤ))
            (fun _ => 800 * W + 2000) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hf2 : FitsSignedWord W (2 * (m : ℤ)) := by
            have : 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) := by push_cast; rfl
            rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : 2 * m ≤ W) Nat.lt_two_pow_self
          have hf21 : FitsSignedWord W (2 * (m : ℤ) + 1) := by
            have : 2 * (m : ℤ) + 1 = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; rfl
            rw [this, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : 2 * m + 1 ≤ W) Nat.lt_two_pow_self
          rcases bmSignedSucc_computesInTime W (by dsimp [M] at *; omega) (2 * (m : ℤ))
            hf2 hf21 u2 u3 u4 u5 uSc with ⟨t, ht, hc⟩
          have hcast : 2 * (m : ℤ) + 1 = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; rfl
          rw [hcast] at hc
          exact ⟨t, ht, hc⟩
        have pTwoM1 := StageEval.seq (StageEval.seq pIdx pTwoMSub) pTwoM1Sub
        have pDivSub : StageEval (S := SubS) bmRoundDivInt
            (encDepPair uTm (fun _ => encodeSignedWord W ((2 * m + 1 : ℕ) : ℤ)))
            (fun _ => encodeSignedWord W
              (roundDivInt
                (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) m).2
                ((2 * m + 1 : ℕ) : ℤ)))
            (fun _ => 250 * W * W + 60000 * W + 150000) := by
          intro s' u2 u3 u4 u5 uSc
          have hm' : m ≤ M := s'.property
          have hf21 : FitsSignedWord W ((2 * m + 1 : ℕ) : ℤ) := by
            rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
            exact lt_of_le_of_lt (by dsimp [M] at *; omega : 2 * m + 1 ≤ W) Nat.lt_two_pow_self
          exact bmRoundDivInt_computesInTime W _ _
            ((hT_fits m hm').mono (by dsimp [q_acc, q_r, M] at *; omega)) hf21 u2 u3 u4 u5 uSc
        refine (StageEval.seq (StageEval.fanout pTm pTwoM1) pDivSub).mono (fun _ => ?_)
        dsimp only [uCW, uIdx, uTm]
        have hqr_le : q_r ≤ W := by dsimp [q_r, M] at *; omega
        simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
        omega)
      (fun _ m hm => ((hT_fits m hm).roundDivInt _).mono (by dsimp [q_acc, q_r, M] at *; omega))
      (fun _ m hm => by
        have hm1_pow : m + 1 ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
        have hsum := fitsSignedWord_sum_range (w := q_acc + 2 * (B * B) + 2) (m + 1) hm1_pow
          (fun j => roundDivInt
            (buildRecurrenceArray ((2 : ℤ) ^ q_acc) (expTermStepFixed q_r r_mant) j).2
            ((2 * j + 1 : ℕ) : ℤ))
          (fun j hj => (hT_fits j (by omega)).roundDivInt _)
        exact hsum.mono (by dsimp [q_acc, q_r, M] at *; omega)))
  set arr := expTermArrayFixed q_r q_acc M r_mant
  set S_inner : ℤ := ∑ m ∈ Finset.range (M + 1),
    roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ)
  have hS_fits_small : FitsSignedWord ((q_acc + 2 * (B * B) + 2) + (M + 1)) S_inner := by
    have hM1_pow : M + 1 ≤ 2 ^ (M + 1) := le_of_lt Nat.lt_two_pow_self
    exact fitsSignedWord_sum_range (M + 1) hM1_pow
      (fun m => roundDivInt (arr.getD m 0) ((2 * m + 1 : ℕ) : ℤ))
      (fun m _ => by
        have ha : FitsSignedWord (q_acc + 2 * (B * B) + 2) (arr.getD m 0) := by
          rw [fitsSignedWord_iff_abs_lt]
          exact lt_of_le_of_lt (abs_expTermArrayFixed_getD_le (B * B) q_r q_acc M r_mant hr_bound
            (by dsimp [q_acc, q_r]; omega) m)
            (pow_lt_pow_right₀ (by decide) (by omega))
        exact ha.roundDivInt _)
  have hS_fits : FitsSignedWord W S_inner :=
    hS_fits_small.mono (by dsimp [q_acc, q_r, M] at *; omega)
  have hout_fits_small : FitsSignedWord (5 * (N + 6) + 2 * (B * B) + B + 12) (z_mant * S_inner) :=
    (hz_fits_small.mul hS_fits_small).mono (by dsimp [q_acc, q_r, q_z, M] at *; omega)
  have hout_fits : FitsSignedWord W (z_mant * S_inner) := hout_fits_small.mono hW_all
  have pOut := StageEval.seq (StageEval.fanout pZMant pSInner)
    (StageEval.const (S := St)
      (bmSignedMulSameWith_computesInTime hmul W z_mant S_inner hz_fits hS_fits hout_fits))
  have herf_eq : erfIntegralTaylorFixed N zNum zDen = z_mant * S_inner := by
    unfold erfIntegralTaylorFixed erfIntegralTaylorFixedWithMul
    dsimp only
    rw [← hqacc_eq, expTermArrayFixedWithMul_mul_eq]
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W (erfIntegralTaylorFixed N zNum zDen))
    pOut (fun _ => by rw [herf_eq])
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uWN, uZ, M, q_r, q_acc, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  have hmulM :
      (N + 6 + 1) * (2 * mulTime W + (250 * W * W + 65000 * W + 165000) +
        5000 * W * W + 450000 * W + 500000) ≤
      (N + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) :=
    Nat.mul_le_mul_left (N + 7) (by nlinarith)
  rw [← herf_eq] at hout_fits_small
  exact ⟨t, by nlinarith, hcomp, hout_fits_small⟩

/-- Context encoding for `bmFilterTapEntryWith`:
`(((W, W_out), (N_s, N_e)), ((q, (q_l2, q_tot)), ((t1_s, m1_s), (piFixed, (θDen, gDen)))))`. -/
def encTapEntryCtx (W W_out N_s N_e q q_l2 q_tot : ℕ)
    (t1_s m1_s piFixed θDen gDen : ℤ) : List Bool :=
  encPair
    (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
    (encPair
      (encPair encUnary (encPair encUnary encUnary))
      (encPair
        (encPair (encodeSignedWord W) (encodeSignedWord W))
        (encPair (encodeSignedWord W) (encPair (encodeSignedWord W) (encodeSignedWord W)))))
    (((W, W_out), (N_s, N_e)), ((q, (q_l2, q_tot)), ((t1_s, m1_s), (piFixed, (θDen, gDen)))))

@[simp]
theorem length_encTapEntryCtx (W W_out N_s N_e q q_l2 q_tot : ℕ)
    (t1_s m1_s piFixed θDen gDen : ℤ) :
    (encTapEntryCtx W W_out N_s N_e q q_l2 q_tot t1_s m1_s piFixed θDen gDen).length =
      2 * (2 * (2 * W + 2 * W_out + 4) + 2 * (2 * N_s + 2 * N_e + 4) + 4) +
      2 * (2 * (2 * q + 2 * (2 * q_l2 + 2 * q_tot + 4) + 4) +
        2 * (2 * (2 * (W + 1) + 2 * (W + 1) + 4) +
          2 * (2 * (W + 1) + 2 * (2 * (W + 1) + 2 * (W + 1) + 4) + 4) + 4) + 4) + 4 := by
  simp [encTapEntryCtx]

/-- **Pure-Integer Sinc-Gaussian Filter Tap Entry Stage (`bmFilterTapEntryWith bmMul`)**:
Consumes `((ctxTap, j1_s), k_s)` on `kIO` (where `j1_s = encodeSignedWord W (j1 : ℤ)` and
`k_s = encodeSignedWord W (k : ℤ)`, corresponding to offset `d = k - m1`) and emits
`encodeSignedWord W_out (computeFilterTapFixed K p j1 d)`. -/
def bmFilterTapEntryWith (bmMul : BitMachine) : BitMachine :=
  let bmCtx := bmSeq bmFst bmFst
  let bmJ1 := bmSeq bmFst bmSnd
  let bmK := bmSnd
  let bmLeft := bmSeq bmCtx bmFst
  let bmRight := bmSeq bmCtx bmSnd
  let bmW := bmSeq (bmSeq bmLeft bmFst) bmFst
  let bmWOut := bmSeq (bmSeq bmLeft bmFst) bmSnd
  let bmNs := bmSeq (bmSeq bmLeft bmSnd) bmFst
  let bmNe := bmSeq (bmSeq bmLeft bmSnd) bmSnd
  let bmQ := bmSeq (bmSeq bmRight bmFst) bmFst
  let bmQl2 := bmSeq (bmSeq (bmSeq bmRight bmFst) bmSnd) bmFst
  let bmQtot := bmSeq (bmSeq (bmSeq bmRight bmFst) bmSnd) bmSnd
  let bmT1s := bmSeq (bmSeq (bmSeq bmRight bmSnd) bmFst) bmFst
  let bmM1s := bmSeq (bmSeq (bmSeq bmRight bmSnd) bmFst) bmSnd
  let bmPi := bmSeq (bmSeq (bmSeq bmRight bmSnd) bmSnd) bmFst
  let bmThDen := bmSeq (bmSeq (bmSeq (bmSeq bmRight bmSnd) bmSnd) bmSnd) bmFst
  let bmGDen := bmSeq (bmSeq (bmSeq (bmSeq bmRight bmSnd) bmSnd) bmSnd) bmSnd
  let bmD := bmSeq (bmFanout bmK bmM1s) bmSignedSub
  let bmDT1 := bmSeq (bmFanout bmD bmT1s) (bmSignedMulSameWith bmMul)
  let bmTNum := bmSeq (bmFanout bmDT1 bmJ1) bmSignedSub
  let bmThNum := bmSeq (bmFanout bmPi bmTNum) (bmSignedMulSameWith bmMul)
  let bmSinc := bmSeq (bmFanout (bmFanout bmW bmNs) (bmFanout bmThNum bmThDen)) (bmSincTaylorWith bmMul)
  let bmThSq := bmSeq (bmFanout bmThNum bmThNum) (bmSignedMulSameWith bmMul)
  let bmGNumShift := bmSeq (bmFanout bmQl2 bmThSq) bmShiftLeftSigned
  let bmGNumRes := bmSeq (bmFanout bmW bmGNumShift) bmResizeSignedWord
  let bmGNum := bmSeq bmGNumRes bmSignedNeg
  let bmExp := bmSeq (bmFanout (bmFanout bmW bmNe) (bmFanout bmGNum bmGDen)) (bmExpTaylorWith bmMul)
  let bmProdSE := bmSeq (bmFanout bmSinc bmExp) (bmSignedMulSameWith bmMul)
  let bmShifted := bmSeq (bmFanout bmQ bmProdSE) bmShiftLeftSigned
  let bmRounded := bmSeq (bmFanout bmQtot bmShifted) bmRoundShiftSigned
  bmSeq (bmFanout bmWOut bmRounded) bmResizeSignedWord

theorem fitsSignedWord_max_min_symm (q_acc w : ℕ) (x : ℤ) (hw : q_acc < w) :
    FitsSignedWord w (max (-((2 : ℤ) ^ q_acc)) (min ((2 : ℤ) ^ q_acc) x)) := by
  rw [fitsSignedWord_iff_abs_lt]
  have h2 : (0 : ℤ) ≤ (2 : ℤ) ^ q_acc := by positivity
  have habs : |max (-((2 : ℤ) ^ q_acc)) (min ((2 : ℤ) ^ q_acc) x)| ≤ (2 : ℤ) ^ q_acc :=
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith only [h2]) (min_le_left _ _)⟩
  exact lt_of_le_of_lt habs (pow_lt_pow_right₀ (by decide) hw)

theorem fitsSignedWord_max_zero_min (q_acc w : ℕ) (x : ℤ) (hw : q_acc < w) :
    FitsSignedWord w (max 0 (min ((2 : ℤ) ^ q_acc) x)) := by
  rw [fitsSignedWord_iff_abs_lt]
  have habs : |max 0 (min ((2 : ℤ) ^ q_acc) x)| ≤ (2 : ℤ) ^ q_acc := by
    rw [abs_of_nonneg (le_max_left 0 _)]
    exact max_le (by positivity) (min_le_left _ _)
  exact lt_of_le_of_lt habs (pow_lt_pow_right₀ (by decide) hw)

theorem abs_sincTaylorFixed_le (N : ℕ) (θNum θDen : ℤ) :
    |sincTaylorFixed N θNum θDen| ≤ (2 : ℤ) ^ (3 * (N + 6) + 6) := by
  unfold sincTaylorFixed sincTaylorFixedWithMul
  dsimp only
  have h2 : (0 : ℤ) ≤ (2 : ℤ) ^ (3 * (N + 6) + 6) := by positivity
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith only [h2]) (min_le_left _ _)⟩

theorem abs_expTaylorFixed_le (N : ℕ) (xNum xDen : ℤ) :
    |expTaylorFixed N xNum xDen| ≤ (2 : ℤ) ^ (3 * (N + 6) + 6) := by
  unfold expTaylorFixed expTaylorFixedWithMul
  dsimp only
  rw [abs_of_nonneg (le_max_left 0 _)]
  exact max_le (by positivity) (min_le_left _ _)

theorem fitsSignedWord_sincTaylorFixed (N : ℕ) (θNum θDen : ℤ) :
    FitsSignedWord (3 * (N + 6) + 7) (sincTaylorFixed N θNum θDen) := by
  unfold sincTaylorFixed sincTaylorFixedWithMul
  dsimp only
  exact fitsSignedWord_max_min_symm (3 * (N + 6) + 6) (3 * (N + 6) + 7) _ (by omega)

theorem fitsSignedWord_expTaylorFixed (N : ℕ) (xNum xDen : ℤ) :
    FitsSignedWord (3 * (N + 6) + 7) (expTaylorFixed N xNum xDen) := by
  unfold expTaylorFixed expTaylorFixedWithMul
  dsimp only
  exact fitsSignedWord_max_zero_min (3 * (N + 6) + 6) (3 * (N + 6) + 7) _ (by omega)

theorem fitsSignedWord_sincTaylorFixed_mul_expTaylorFixed (N_s N_e : ℕ) (θNum θDen gNum gDen : ℤ) :
    FitsSignedWord ((3 * (N_s + 6) + 6) + (3 * (N_e + 6) + 6) + 1)
      (sincTaylorFixed N_s θNum θDen * expTaylorFixed N_e gNum gDen) := by
  rw [fitsSignedWord_iff_abs_lt, abs_mul]
  have hs := abs_sincTaylorFixed_le N_s θNum θDen
  have he := abs_expTaylorFixed_le N_e gNum gDen
  have hprod : |sincTaylorFixed N_s θNum θDen| * |expTaylorFixed N_e gNum gDen| ≤
      (2 : ℤ) ^ ((3 * (N_s + 6) + 6) + (3 * (N_e + 6) + 6)) := by
    rw [pow_add]
    exact mul_le_mul hs he (abs_nonneg _) (by positivity)
  exact lt_of_le_of_lt hprod (pow_lt_pow_right₀ (by decide) (Nat.lt_succ_self _))

theorem roundDivInt_two_pow_eq_roundShiftInt (m : ℤ) (k : ℕ) :
    roundDivInt m ((2 : ℤ) ^ k) = roundShiftInt m k := by
  rw [roundDivInt_eq_floor_div_add_half, roundShiftInt_eq_quantizeRealMantissa]
  push_cast
  rfl

theorem computeFilterTapAuxFixedWithMul_of_le (m1 t1 pW pC q S : ℕ) (j1 : Fin t1) (d : ℤ)
    (hd : |d| ≤ (m1 : ℤ)) :
    let q_pi := 4 * (S + 3) + 6
    let piFixed := approxPiFixed S
    let q_l2 := S + (S + 2)
    let l2Fixed := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S)
    let B_sinc := 5 * (m1 + 1)
    let N_s := 4 * B_sinc + S + 1
    let q_accs := 3 * (N_s + 6) + 6
    let B_exp := 25 * (pC + 1)
    let N_e := 4 * B_exp + S + 1
    let q_acce := 3 * (N_e + 6) + 6
    let tNum : ℤ := d * (t1 : ℤ) - (j1.val : ℤ)
    let θNum : ℤ := piFixed * tNum
    let θDen : ℤ := (t1 : ℤ) * (2 : ℤ) ^ q_pi
    let sincFixed : ℤ := sincTaylorFixed N_s θNum θDen
    let gNum : ℤ := -(θNum * θNum * (2 : ℤ) ^ q_l2)
    let gDen : ℤ := (4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)
    let expFixed : ℤ := expTaylorFixed N_e gNum gDen
    computeFilterTapAuxFixedWithMul (· * ·) m1 t1 pW pC q S j1 d =
      roundShiftInt ((sincFixed * expFixed) * (2 : ℤ) ^ q) (q_accs + q_acce) := by
  intro q_pi piFixed q_l2 l2Fixed B_sinc N_s q_accs B_exp N_e q_acce
    tNum θNum θDen sincFixed gNum gDen expFixed
  unfold computeFilterTapAuxFixedWithMul
  dsimp only
  rw [if_pos hd]
  exact roundDivInt_two_pow_eq_roundShiftInt ((sincFixed * expFixed) * (2 : ℤ) ^ q) (q_accs + q_acce)

theorem computeFilterTapFixed_of_le (K p : ℕ) (j1 : Fin (t1Ell K)) (d : ℤ)
    (hd : |d| ≤ (computeM1Ell K p : ℤ))
    (sincVal expVal : ℤ)
    (hsinc : sincVal = sincTaylorFixed
      (4 * (5 * (computeM1Ell K p + 1)) + (qChildEll K p + 3 * pChildEll K p + 20) + 1)
      (approxPiFixed (qChildEll K p + 3 * pChildEll K p + 20) * (d * (t1Ell K : ℤ) - (j1.val : ℤ)))
      ((t1Ell K : ℤ) * (2 : ℤ) ^ (4 * ((qChildEll K p + 3 * pChildEll K p + 20) + 3) + 6)))
    (hexp : expVal = expTaylorFixed
      (4 * (25 * (pChildEll K p + 1)) + (qChildEll K p + 3 * pChildEll K p + 20) + 1)
      (-((approxPiFixed (qChildEll K p + 3 * pChildEll K p + 20) * (d * (t1Ell K : ℤ) - (j1.val : ℤ))) *
         (approxPiFixed (qChildEll K p + 3 * pChildEll K p + 20) * (d * (t1Ell K : ℤ) - (j1.val : ℤ))) *
         (2 : ℤ) ^ ((qChildEll K p + 3 * pChildEll K p + 20) + ((qChildEll K p + 3 * pChildEll K p + 20) + 2))))
      ((4 * (pWorkEll K p : ℤ) * (t1Ell K : ℤ) * (t1Ell K : ℤ)) *
        max ((2 : ℤ) ^ (((qChildEll K p + 3 * pChildEll K p + 20) + ((qChildEll K p + 3 * pChildEll K p + 20) + 2)) - 1))
          (approxLogTwoFixed (qChildEll K p + 3 * pChildEll K p + 20)) *
        (2 : ℤ) ^ (2 * (4 * ((qChildEll K p + 3 * pChildEll K p + 20) + 3) + 6)))) :
    computeFilterTapFixed K p j1 d =
      roundShiftInt ((sincVal * expVal) * (2 : ℤ) ^ (qChildEll K p))
        ((3 * ((4 * (5 * (computeM1Ell K p + 1)) + (qChildEll K p + 3 * pChildEll K p + 20) + 1) + 6) + 6) +
         (3 * ((4 * (25 * (pChildEll K p + 1)) + (qChildEll K p + 3 * pChildEll K p + 20) + 1) + 6) + 6)) := by
  rw [← computeFilterTapFixedWithMul_eq_computeFilterTapFixed, hsinc, hexp]
  exact computeFilterTapAuxFixedWithMul_of_le (computeM1Ell K p) (t1Ell K) (pWorkEll K p)
    (pChildEll K p) (qChildEll K p) (qChildEll K p + 3 * pChildEll K p + 20) j1 d hd

theorem encTapEntryCtx_input_eq (W W_out N_s N_e q q_l2 q_tot : ℕ)
    (t1_s m1_s piFixed θDen gDen j1_s k_s : ℤ) :
    encDepPair (S := Unit)
      (encDepPair
        (encDepPair
          (encDepPair (encDepPair (fun _ => encUnary W) (fun _ => encUnary W_out))
            (encDepPair (fun _ => encUnary N_s) (fun _ => encUnary N_e)))
          (encDepPair
            (encDepPair (fun _ => encUnary q)
              (encDepPair (fun _ => encUnary q_l2) (fun _ => encUnary q_tot)))
            (encDepPair
              (encDepPair (fun _ => encodeSignedWord W t1_s) (fun _ => encodeSignedWord W m1_s))
              (encDepPair (fun _ => encodeSignedWord W piFixed)
                (encDepPair (fun _ => encodeSignedWord W θDen) (fun _ => encodeSignedWord W gDen))))))
        (fun _ => encodeSignedWord W j1_s))
      (fun _ => encodeSignedWord W k_s) () =
      encPair (encPair (fun x => x) (encodeSignedWord W)) (encodeSignedWord W)
        ((encTapEntryCtx W W_out N_s N_e q q_l2 q_tot t1_s m1_s piFixed θDen gDen, j1_s), k_s) :=
  rfl

set_option maxHeartbeats 800000 in
theorem bmFilterTapEntryWith_aux_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W W_out B_sinc N_s B_exp_m1 N_e q q_l2 q_tot : ℕ)
    (t1_s m1_s piFixed θDen gDen j1_s k_s sincVal expVal outVal : ℤ)
    (hW_out_le : W_out ≤ W)
    (hNs_le : N_s ≤ W) (hNe_le : N_e ≤ W) (hql2_le : q_l2 ≤ W) (hqtot_le : q_tot ≤ W) (hq_le : q ≤ W)
    (hWsinc : (3 * (N_s + 6) + 6) + 2 * B_sinc + (N_s + 6) + 4 ≤ W)
    (hWexp : (3 * (N_e + 6) + 6) + 2 * B_exp_m1 + (N_e + 6) + 4 ≤ W)
    (hk_fits : FitsSignedWord W k_s)
    (hm1_fits : FitsSignedWord W m1_s)
    (ht1_fits : FitsSignedWord W t1_s)
    (hj1_fits : FitsSignedWord W j1_s)
    (hpi_fits : FitsSignedWord W piFixed)
    (hθDen_fits : FitsSignedWord W θDen) (hθDen_pos : 0 < θDen)
    (hgDen_fits : FitsSignedWord W gDen) (hgDen_pos : 0 < gDen)
    (hd_fits : FitsSignedWord W (k_s - m1_s))
    (hdt1_fits : FitsSignedWord W ((k_s - m1_s) * t1_s))
    (htNum_fits : FitsSignedWord W ((k_s - m1_s) * t1_s - j1_s))
    (hθNum_fits : FitsSignedWord W (piFixed * ((k_s - m1_s) * t1_s - j1_s)))
    (hθ_bound : |piFixed * ((k_s - m1_s) * t1_s - j1_s)| ≤ (B_sinc : ℤ) * θDen)
    (hθSq_fits : FitsSignedWord W ((piFixed * ((k_s - m1_s) * t1_s - j1_s)) * (piFixed * ((k_s - m1_s) * t1_s - j1_s))))
    (hgShift_fits : FitsSignedWord W (((piFixed * ((k_s - m1_s) * t1_s - j1_s)) * (piFixed * ((k_s - m1_s) * t1_s - j1_s))) * (2 : ℤ) ^ q_l2))
    (hg_bound : |-(((piFixed * ((k_s - m1_s) * t1_s - j1_s)) * (piFixed * ((k_s - m1_s) * t1_s - j1_s))) * (2 : ℤ) ^ q_l2)| ≤ (B_exp_m1 : ℤ) * gDen)
    (hsincVal : sincVal = sincTaylorFixed N_s (piFixed * ((k_s - m1_s) * t1_s - j1_s)) θDen)
    (hexpVal : expVal = expTaylorFixed N_e (-(((piFixed * ((k_s - m1_s) * t1_s - j1_s)) * (piFixed * ((k_s - m1_s) * t1_s - j1_s))) * (2 : ℤ) ^ q_l2)) gDen)
    (hsinc_fits : FitsSignedWord W sincVal)
    (hexp_fits : FitsSignedWord W expVal)
    (hprodSE_fits : FitsSignedWord W (sincVal * expVal))
    (hround_fits : FitsSignedWord W_out (roundShiftInt ((sincVal * expVal) * (2 : ℤ) ^ q) q_tot))
    (houtVal : outVal = roundShiftInt ((sincVal * expVal) * (2 : ℤ) ^ q) q_tot)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (N_s + N_e + 14) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
        16 * mulTime W + 45000 * W * W + 3000000 * W + 4000000,
      (bmFilterTapEntryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (fun x => x) (encodeSignedWord W)) (encodeSignedWord W)
            ((encTapEntryCtx W W_out N_s N_e q q_l2 q_tot t1_s m1_s piFixed θDen gDen,
              j1_s), k_s)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W_out outVal))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let St := Unit
  let d : ℤ := k_s - m1_s
  let tNum : ℤ := d * t1_s - j1_s
  let θNum : ℤ := piFixed * tNum
  let gNum : ℤ := -((θNum * θNum) * (2 : ℤ) ^ q_l2)
  have hgNum_fits : FitsSignedWord W gNum := hgShift_fits.neg
  let uL1 : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary W_out)
  let uL2 : St → List Bool := encDepPair (fun _ => encUnary N_s) (fun _ => encUnary N_e)
  let uLeft : St → List Bool := encDepPair uL1 uL2
  let uR1 : St → List Bool := encDepPair (fun _ => encUnary q)
    (encDepPair (fun _ => encUnary q_l2) (fun _ => encUnary q_tot))
  let uR21 : St → List Bool := encDepPair (fun _ => encodeSignedWord W t1_s)
    (fun _ => encodeSignedWord W m1_s)
  let uR22 : St → List Bool := encDepPair (fun _ => encodeSignedWord W piFixed)
    (encDepPair (fun _ => encodeSignedWord W θDen) (fun _ => encodeSignedWord W gDen))
  let uR2 : St → List Bool := encDepPair uR21 uR22
  let uRight : St → List Bool := encDepPair uR1 uR2
  let uCtx : St → List Bool := encDepPair uLeft uRight
  let uCtxJ1 : St → List Bool := encDepPair uCtx (fun _ => encodeSignedWord W j1_s)
  let pCtx := StageEval.seq (StageEval.fst uCtxJ1 (fun _ => encodeSignedWord W k_s))
    (StageEval.fst uCtx (fun _ => encodeSignedWord W j1_s))
  let pJ1 := StageEval.seq (StageEval.fst uCtxJ1 (fun _ => encodeSignedWord W k_s))
    (StageEval.snd uCtx (fun _ => encodeSignedWord W j1_s))
  let pK := StageEval.snd uCtxJ1 (fun _ => encodeSignedWord W k_s)
  let pLeft := StageEval.seq pCtx (StageEval.fst uLeft uRight)
  let pRight := StageEval.seq pCtx (StageEval.snd uLeft uRight)
  let pWidth := StageEval.seq (StageEval.seq pLeft (StageEval.fst uL1 uL2))
    (StageEval.fst (fun _ => encUnary W) (fun _ => encUnary W_out))
  let pWOut := StageEval.seq (StageEval.seq pLeft (StageEval.fst uL1 uL2))
    (StageEval.snd (fun _ => encUnary W) (fun _ => encUnary W_out))
  let pNs := StageEval.seq (StageEval.seq pLeft (StageEval.snd uL1 uL2))
    (StageEval.fst (fun _ => encUnary N_s) (fun _ => encUnary N_e))
  let pNe := StageEval.seq (StageEval.seq pLeft (StageEval.snd uL1 uL2))
    (StageEval.snd (fun _ => encUnary N_s) (fun _ => encUnary N_e))
  let pQ := StageEval.seq (StageEval.seq pRight (StageEval.fst uR1 uR2))
    (StageEval.fst (fun _ => encUnary q) (encDepPair (fun _ => encUnary q_l2) (fun _ => encUnary q_tot)))
  let pQl2 := StageEval.seq
    (StageEval.seq (StageEval.seq pRight (StageEval.fst uR1 uR2))
      (StageEval.snd (fun _ => encUnary q) (encDepPair (fun _ => encUnary q_l2) (fun _ => encUnary q_tot))))
    (StageEval.fst (fun _ => encUnary q_l2) (fun _ => encUnary q_tot))
  let pQtot := StageEval.seq
    (StageEval.seq (StageEval.seq pRight (StageEval.fst uR1 uR2))
      (StageEval.snd (fun _ => encUnary q) (encDepPair (fun _ => encUnary q_l2) (fun _ => encUnary q_tot))))
    (StageEval.snd (fun _ => encUnary q_l2) (fun _ => encUnary q_tot))
  let pT1s := StageEval.seq (StageEval.seq (StageEval.seq pRight (StageEval.snd uR1 uR2))
    (StageEval.fst uR21 uR22))
    (StageEval.fst (fun _ => encodeSignedWord W t1_s) (fun _ => encodeSignedWord W m1_s))
  let pM1s := StageEval.seq (StageEval.seq (StageEval.seq pRight (StageEval.snd uR1 uR2))
    (StageEval.fst uR21 uR22))
    (StageEval.snd (fun _ => encodeSignedWord W t1_s) (fun _ => encodeSignedWord W m1_s))
  let pPi := StageEval.seq (StageEval.seq (StageEval.seq pRight (StageEval.snd uR1 uR2))
    (StageEval.snd uR21 uR22))
    (StageEval.fst (fun _ => encodeSignedWord W piFixed)
      (encDepPair (fun _ => encodeSignedWord W θDen) (fun _ => encodeSignedWord W gDen)))
  let pThDen := StageEval.seq
    (StageEval.seq (StageEval.seq (StageEval.seq pRight (StageEval.snd uR1 uR2))
      (StageEval.snd uR21 uR22))
      (StageEval.snd (fun _ => encodeSignedWord W piFixed)
        (encDepPair (fun _ => encodeSignedWord W θDen) (fun _ => encodeSignedWord W gDen))))
    (StageEval.fst (fun _ => encodeSignedWord W θDen) (fun _ => encodeSignedWord W gDen))
  let pGDen := StageEval.seq
    (StageEval.seq (StageEval.seq (StageEval.seq pRight (StageEval.snd uR1 uR2))
      (StageEval.snd uR21 uR22))
      (StageEval.snd (fun _ => encodeSignedWord W piFixed)
        (encDepPair (fun _ => encodeSignedWord W θDen) (fun _ => encodeSignedWord W gDen))))
    (StageEval.snd (fun _ => encodeSignedWord W θDen) (fun _ => encodeSignedWord W gDen))
  have pD := StageEval.seq (StageEval.fanout pK pM1s)
    (StageEval.const (S := St) (bmSignedSub_computesInTime W k_s m1_s hk_fits hm1_fits hd_fits))
  have pDT1 := StageEval.seq (StageEval.fanout pD pT1s)
    (StageEval.const (S := St) (bmSignedMulSameWith_computesInTime hmul W d t1_s hd_fits ht1_fits hdt1_fits))
  have pTNum := StageEval.seq (StageEval.fanout pDT1 pJ1)
    (StageEval.const (S := St) (bmSignedSub_computesInTime W (d * t1_s) j1_s hdt1_fits hj1_fits htNum_fits))
  have pThNum := StageEval.seq (StageEval.fanout pPi pTNum)
    (StageEval.const (S := St) (bmSignedMulSameWith_computesInTime hmul W piFixed tNum hpi_fits htNum_fits hθNum_fits))
  have pSincRaw := StageEval.seq
    (StageEval.fanout (StageEval.fanout pWidth pNs) (StageEval.fanout pThNum pThDen))
    (StageEval.const (S := St)
      (bmSincTaylorWith_computesInTime hmul B_sinc W N_s θNum θDen
        hθNum_fits hθDen_fits hθDen_pos hθ_bound hWsinc))
  have pSinc := StageEval.congr_out (v2 := fun _ => encodeSignedWord W sincVal) pSincRaw
    (fun _ => congrArg (encodeSignedWord W) hsincVal.symm)
  have pThSq := StageEval.seq (StageEval.fanout pThNum pThNum)
    (StageEval.const (S := St) (bmSignedMulSameWith_computesInTime hmul W θNum θNum hθNum_fits hθNum_fits hθSq_fits))
  have pGNumShift := StageEval.seq (StageEval.fanout pQl2 pThSq)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime q_l2 W (θNum * θNum) hθSq_fits))
  have hgShift_W : FitsSignedWord (q_l2 + W) ((θNum * θNum) * (2 : ℤ) ^ q_l2) := by
    simpa [Nat.add_comm] using hθSq_fits.mul_two_pow q_l2
  have pGNumRes := StageEval.seq (StageEval.fanout pWidth pGNumShift)
    (StageEval.const (S := St)
      (bmResizeSignedWord_computesInTime (q_l2 + W) W ((θNum * θNum) * (2 : ℤ) ^ q_l2)
        hgShift_W hgShift_fits))
  have pGNum := StageEval.seq pGNumRes
    (StageEval.const (S := St) (bmSignedNeg_computesInTime W ((θNum * θNum) * (2 : ℤ) ^ q_l2) hgShift_fits))
  have pExpRaw := StageEval.seq
    (StageEval.fanout (StageEval.fanout pWidth pNe) (StageEval.fanout pGNum pGDen))
    (StageEval.const (S := St)
      (bmExpTaylorWith_computesInTime hmul B_exp_m1 W N_e gNum gDen
        hgNum_fits hgDen_fits hgDen_pos hg_bound hWexp))
  have pExp := StageEval.congr_out (v2 := fun _ => encodeSignedWord W expVal) pExpRaw
    (fun _ => congrArg (encodeSignedWord W) hexpVal.symm)
  have pProdSE := StageEval.seq (StageEval.fanout pSinc pExp)
    (StageEval.const (S := St)
      (bmSignedMulSameWith_computesInTime hmul W sincVal expVal hsinc_fits hexp_fits hprodSE_fits))
  have pShifted := StageEval.seq (StageEval.fanout pQ pProdSE)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime q W (sincVal * expVal) hprodSE_fits))
  have hsh_W : FitsSignedWord (q + W) ((sincVal * expVal) * (2 : ℤ) ^ q) := by
    simpa [Nat.add_comm] using hprodSE_fits.mul_two_pow q
  have pRounded := StageEval.seq (StageEval.fanout pQtot pShifted)
    (StageEval.const (S := St)
      (bmRoundShiftSigned_computesInTime (q + W) q_tot ((sincVal * expVal) * (2 : ℤ) ^ q) hsh_W))
  have pOut := StageEval.seq (StageEval.fanout pWOut pRounded)
    (StageEval.const (S := St)
      (bmResizeSignedWord_computesInTime (q + W) W_out
        (roundShiftInt ((sincVal * expVal) * (2 : ℤ) ^ q) q_tot)
        (hsh_W.roundShiftInt q_tot) hround_fits))
  have hall := StageEval.congr_in
    (u2 := fun _ => encPair (encPair (fun x => x) (encodeSignedWord W)) (encodeSignedWord W)
      ((encTapEntryCtx W W_out N_s N_e q q_l2 q_tot t1_s m1_s piFixed θDen gDen,
        j1_s), k_s))
    (StageEval.congr_out
      (v2 := fun _ => encodeSignedWord W_out outVal)
      pOut (fun _ => congrArg (encodeSignedWord W_out) houtVal.symm))
    (fun _ => encTapEntryCtx_input_eq W W_out N_s N_e q q_l2 q_tot
      t1_s m1_s piFixed θDen gDen j1_s k_s)
  have hlen_uL1 : (uL1 ()).length ≤ 8 * W + 8 := by
    dsimp only [uL1]; simp only [length_encDepPair, length_encUnary]; omega
  have hlen_uL2 : (uL2 ()).length ≤ 8 * W + 8 := by
    dsimp only [uL2]; simp only [length_encDepPair, length_encUnary]; omega
  have hlen_uLeft : (uLeft ()).length ≤ 32 * W + 36 := by
    dsimp only [uLeft]; simp only [length_encDepPair]; omega
  have hlen_uR1 : (uR1 ()).length ≤ 16 * W + 20 := by
    dsimp only [uR1]; simp only [length_encDepPair, length_encUnary]; omega
  have hlen_uR21 : (uR21 ()).length ≤ 8 * W + 16 := by
    dsimp only [uR21]; simp only [length_encDepPair, length_encodeSignedWord]; omega
  have hlen_uR22 : (uR22 ()).length ≤ 16 * W + 36 := by
    dsimp only [uR22]; simp only [length_encDepPair, length_encodeSignedWord]; omega
  have hlen_uR2 : (uR2 ()).length ≤ 48 * W + 108 := by
    dsimp only [uR2]; simp only [length_encDepPair]; omega
  have hlen_uRight : (uRight ()).length ≤ 128 * W + 260 := by
    dsimp only [uRight]; simp only [length_encDepPair]; omega
  have hlen_uCtx : (uCtx ()).length ≤ 320 * W + 600 := by
    dsimp only [uCtx]; simp only [length_encDepPair]; omega
  have hlen_uCtxJ1 : (uCtxJ1 ()).length ≤ 644 * W + 1212 := by
    dsimp only [uCtxJ1]; simp only [length_encDepPair, length_encodeSignedWord]; omega
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  have hcomb :
      (N_s + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
      (N_e + 7) * (2 * mulTime W + 5500 * W * W + 500000 * W + 600000) ≤
      (N_s + N_e + 14) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) := by
    have h1 := Nat.mul_le_mul_left (N_e + 7)
      (show 2 * mulTime W + 5500 * W * W + 500000 * W + 600000 ≤
            2 * mulTime W + 5500 * W * W + 550000 * W + 800000 by nlinarith only [])
    have h2 :
        (N_s + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
        (N_e + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) =
        (N_s + N_e + 14) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) := by ring
    linarith only [h1, h2]
  have ht_bound : t ≤ (N_s + N_e + 14) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
      16 * mulTime W + 45000 * W * W + 3000000 * W + 4000000 := by
    nlinarith only [ht, hcomb, hlen_uL1, hlen_uL2, hlen_uLeft, hlen_uR1, hlen_uR21, hlen_uR22,
      hlen_uR2, hlen_uRight, hlen_uCtx, hlen_uCtxJ1, hNs_le, hNe_le, hql2_le, hqtot_le,
      hq_le, hW_out_le]
  exact ⟨t, ht_bound, hcomp⟩

private lemma gNum_abs_le_fifty_mul_gDen (m1 pW t1 q_pi q_l2 : ℕ) (θNum l2Fixed : ℤ)
    (hq_l2 : 1 ≤ q_l2) (hm1_pW : m1 + 1 ≤ 4 * pW)
    (hl2_ge : (2 : ℤ) ^ (q_l2 - 1) ≤ l2Fixed)
    (hθ_bound : |θNum| ≤ ((5 * (m1 + 1) : ℕ) : ℤ) * ((t1 : ℤ) * (2 : ℤ) ^ q_pi)) :
    |-((θNum * θNum) * (2 : ℤ) ^ q_l2)| ≤
      ((50 * (m1 + 1) : ℕ) : ℤ) *
        ((4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)) := by
  set θDen : ℤ := (t1 : ℤ) * (2 : ℤ) ^ q_pi
  have hθDen_nn : 0 ≤ θDen := mul_nonneg (Nat.cast_nonneg t1) (by positivity)
  have hl2_pos : 0 < l2Fixed := lt_of_lt_of_le (by positivity) hl2_ge
  have h2l2 : (2 : ℤ) ^ q_l2 ≤ 2 * l2Fixed := by
    calc (2 : ℤ) ^ q_l2 = 2 * (2 : ℤ) ^ (q_l2 - 1) := by
          conv_lhs => rw [show q_l2 = (q_l2 - 1) + 1 by omega, pow_succ']
      _ ≤ 2 * l2Fixed := mul_le_mul_of_nonneg_left hl2_ge (by decide)
  have hm1_pW_z : ((m1 + 1 : ℕ) : ℤ) ≤ 4 * (pW : ℤ) := by exact_mod_cast hm1_pW
  have hθ_sq_le : |θNum| * |θNum| ≤
      (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) * (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) :=
    mul_le_mul hθ_bound hθ_bound (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hθDen_nn)
  have hDen_sq : θDen * θDen = (t1 : ℤ) * (t1 : ℤ) * (2 : ℤ) ^ (2 * q_pi) := by
    dsimp only [θDen]; rw [Nat.two_mul, pow_add]; ring
  have hsq_id : (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) * (((5 * (m1 + 1) : ℕ) : ℤ) * θDen) =
      25 * ((m1 + 1 : ℕ) : ℤ) * ((m1 + 1 : ℕ) : ℤ) * (θDen * θDen) := by
    push_cast; ring
  have htail_nn : 0 ≤ (t1 : ℤ) * (t1 : ℤ) * l2Fixed * (2 : ℤ) ^ (2 * q_pi) :=
    mul_nonneg (mul_nonneg (mul_self_nonneg (t1 : ℤ)) (le_of_lt hl2_pos)) (by positivity)
  rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ q_l2)]
  calc (|θNum| * |θNum|) * (2 : ℤ) ^ q_l2
      ≤ ((((5 * (m1 + 1) : ℕ) : ℤ) * θDen) * (((5 * (m1 + 1) : ℕ) : ℤ) * θDen)) *
          (2 * l2Fixed) :=
        mul_le_mul hθ_sq_le h2l2 (by positivity) (mul_self_nonneg _)
    _ = 50 * ((m1 + 1 : ℕ) : ℤ) * ((m1 + 1 : ℕ) : ℤ) *
          ((t1 : ℤ) * (t1 : ℤ) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)) := by
        rw [hsq_id, hDen_sq]; ring
    _ ≤ 50 * ((m1 + 1 : ℕ) : ℤ) * (4 * (pW : ℤ)) *
          ((t1 : ℤ) * (t1 : ℤ) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm1_pW_z (mul_nonneg (by decide) (Nat.cast_nonneg _)))
          htail_nn
    _ = ((50 * (m1 + 1) : ℕ) : ℤ) *
          ((4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)) := by
        push_cast; ring

theorem bmFilterTapEntryWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W W_out K p : ℕ) (hK : 2 ≤ K) (hW : 1000 * qChildEll K p ≤ W)
    (hW_out : qChildEll K p + 2 ≤ W_out) (hW_out_le : W_out ≤ W)
    (j1 : Fin (t1Ell K)) (k : ℕ) (hk : k ≤ 2 * computeM1Ell K p)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let pC := pChildEll K p
    let pW := pWorkEll K p
    let m1 := computeM1Ell K p
    let t1 := t1Ell K
    let S := q + 3 * pC + 20
    let q_pi := 4 * (S + 3) + 6
    let q_l2 := S + (S + 2)
    let B_sinc := 5 * (m1 + 1)
    let N_s := 4 * B_sinc + S + 1
    let q_accs := 3 * (N_s + 6) + 6
    let B_exp := 25 * (pC + 1)
    let N_e := 4 * B_exp + S + 1
    let q_acce := 3 * (N_e + 6) + 6
    let q_tot := q_accs + q_acce
    let piFixed := approxPiFixed S
    let l2Fixed := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed S)
    let θDen : ℤ := (t1 : ℤ) * (2 : ℤ) ^ q_pi
    let gDen : ℤ := (4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)
    let d : ℤ := (k : ℤ) - (m1 : ℤ)
    ∃ t ≤ (N_s + N_e + 14) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
        16 * mulTime W + 45000 * W * W + 3000000 * W + 4000000,
      (bmFilterTapEntryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (fun x => x) (encodeSignedWord W)) (encodeSignedWord W)
            ((encTapEntryCtx W W_out N_s N_e q q_l2 q_tot (t1 : ℤ) (m1 : ℤ) piFixed θDen gDen,
              (j1.val : ℤ)), (k : ℤ))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W_out (computeFilterTapFixed K p j1 d)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro q pC pW m1 t1 S q_pi q_l2 B_sinc N_s q_accs B_exp N_e q_acce q_tot piFixed l2Fixed θDen gDen d
  have hqW : 1000 * q ≤ W := hW
  have hq_eq : q = p + 2 * K + 14 := by unfold q qChildEll pChildEll pWorkEll; omega
  have hpC_eq : pC = p + 2 * K + 12 := by unfold pC pChildEll pWorkEll; omega
  have hpW_eq : pW = p + K + 6 := by unfold pW pWorkEll; rfl
  have hm1_le : m1 ≤ pC := computeM1Ell_le_pChildEll K p
  have ht1_pos : 0 < t1 := t1Ell_pos K
  have ht1_le : t1 ≤ 2 ^ K := t1Ell_le_two_pow K
  have ht1_z : (0 : ℤ) < (t1 : ℤ) := by exact_mod_cast ht1_pos
  have hpi_fits_small : FitsSignedWord (4 * S + 22) piFixed :=
    fitsSignedWord_approxPiFixed S (by dsimp only [S]; omega)
  have hpi_fits : FitsSignedWord W piFixed := hpi_fits_small.mono (by dsimp only [S]; omega)
  have hpi_nn : 0 ≤ piFixed := approxPiFixed_nonneg S
  have hpi_le : piFixed ≤ 5 * (2 : ℤ) ^ q_pi := approxPiFixed_le S
  have hl2_ge : (2 : ℤ) ^ (q_l2 - 1) ≤ l2Fixed := le_max_left _ _
  have hl2_pos : 0 < l2Fixed := lt_of_lt_of_le (by positivity) hl2_ge
  have hl2_fits_small : FitsSignedWord (2 * S + 4) l2Fixed :=
    fitsSignedWord_max_approxLogTwoFixed S (le_refl _)
  have ht1_pow_q : t1 ≤ 2 ^ q := ht1_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have ht1_lt_q1 : t1 < 2 ^ (q + 1) :=
    lt_of_le_of_lt ht1_pow_q (Nat.pow_lt_pow_right (by decide) (by omega))
  have ht1_fits_q : FitsSignedWord (q + 1) (t1 : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact ht1_lt_q1
  have ht1_fits : FitsSignedWord W (t1 : ℤ) := ht1_fits_q.mono (by omega)
  have hm1_lt_q : m1 + 1 < 2 ^ q :=
    lt_of_le_of_lt (by omega : m1 + 1 ≤ q) Nat.lt_two_pow_self
  have hm1_fits_q : FitsSignedWord q (m1 : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
  have hm1_fits : FitsSignedWord W (m1 : ℤ) := hm1_fits_q.mono (by omega)
  have hk_fits_q : FitsSignedWord (q + 1) (k : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    have : 2 * m1 < 2 ^ (q + 1) := by
      have : 2 ^ (q + 1) = 2 * 2 ^ q := by rw [pow_succ']
      omega
    omega
  have hk_fits : FitsSignedWord W (k : ℤ) := hk_fits_q.mono (by omega)
  have hj1_fits_q : FitsSignedWord (q + 1) (j1.val : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact lt_of_lt_of_le j1.isLt (le_of_lt ht1_lt_q1)
  have hj1_fits : FitsSignedWord W (j1.val : ℤ) := hj1_fits_q.mono (by omega)
  have hd_abs : |d| ≤ (m1 : ℤ) := by
    dsimp only [d]; rw [abs_le]; constructor <;> omega
  have hd_fits_q : FitsSignedWord q d :=
    (fitsSignedWord_iff_abs_lt q d).mpr
      (lt_of_le_of_lt hd_abs (by exact_mod_cast (lt_of_le_of_lt (Nat.le_succ m1) hm1_lt_q)))
  have hd_fits : FitsSignedWord W d := hd_fits_q.mono (by omega)
  have hdt1_fits_small := hd_fits_q.mul ht1_fits_q
  have hdt1_fits : FitsSignedWord W (d * (t1 : ℤ)) := hdt1_fits_small.mono (by omega)
  set tNum : ℤ := d * (t1 : ℤ) - (j1.val : ℤ)
  have htNum_fits_small : FitsSignedWord (2 * q + 2) tNum :=
    (hdt1_fits_small.mono (by omega : q + (q + 1) ≤ 2 * q + 1)).sub
      (hj1_fits_q.mono (by omega : q + 1 ≤ 2 * q + 1))
  have htNum_fits : FitsSignedWord W tNum := htNum_fits_small.mono (by omega)
  have htNum_abs : |tNum| ≤ ((m1 + 1 : ℕ) : ℤ) * (t1 : ℤ) := by
    have hj1_lt : (j1.val : ℤ) < (t1 : ℤ) := by exact_mod_cast j1.isLt
    have hj1_nn : (0 : ℤ) ≤ (j1.val : ℤ) := Nat.cast_nonneg j1.val
    have hdt1_abs : |d * (t1 : ℤ)| ≤ (m1 : ℤ) * (t1 : ℤ) := by
      rw [abs_mul, abs_of_pos ht1_z]
      exact mul_le_mul_of_nonneg_right hd_abs (le_of_lt ht1_z)
    have htri := abs_sub (d * (t1 : ℤ)) (j1.val : ℤ)
    rw [abs_of_nonneg hj1_nn] at htri
    have hcast : (((m1 + 1 : ℕ) : ℤ) * (t1 : ℤ)) = (m1 : ℤ) * (t1 : ℤ) + (t1 : ℤ) := by
      push_cast; ring
    rw [hcast]
    linarith only [hj1_lt, hj1_nn, hdt1_abs, htri]
  set θNum : ℤ := piFixed * tNum
  have hθNum_fits_small := hpi_fits_small.mul htNum_fits_small
  have hθNum_fits : FitsSignedWord W θNum := hθNum_fits_small.mono (by dsimp only [S]; omega)
  have hθDen_pos : 0 < θDen := mul_pos ht1_z (by positivity)
  have hθDen_fits_small := ht1_fits_q.mul_two_pow q_pi
  have hθDen_fits : FitsSignedWord W θDen :=
    hθDen_fits_small.mono (by dsimp only [q_pi, S]; omega)
  have hθ_bound : |θNum| ≤ (B_sinc : ℤ) * θDen := by
    calc |θNum| = piFixed * |tNum| := by
          dsimp only [θNum]; rw [abs_mul, abs_of_nonneg hpi_nn]
      _ ≤ (5 * (2 : ℤ) ^ q_pi) * (((m1 + 1 : ℕ) : ℤ) * (t1 : ℤ)) :=
          mul_le_mul hpi_le htNum_abs (abs_nonneg _) (by positivity)
      _ = (B_sinc : ℤ) * θDen := by dsimp only [B_sinc, θDen]; push_cast; ring
  have hθSq_fits_small := hθNum_fits_small.mul hθNum_fits_small
  have hθSq_fits : FitsSignedWord W (θNum * θNum) :=
    hθSq_fits_small.mono (by dsimp only [S]; omega)
  have hgShift_fits_small := hθSq_fits_small.mul_two_pow q_l2
  have hgShift_fits : FitsSignedWord W ((θNum * θNum) * (2 : ℤ) ^ q_l2) :=
    hgShift_fits_small.mono (by dsimp only [q_l2, S]; omega)
  set gNum : ℤ := -((θNum * θNum) * (2 : ℤ) ^ q_l2)
  have hpW_z : (0 : ℤ) < (pW : ℤ) := by exact_mod_cast (by omega : 0 < pW)
  have hgDen_pos : 0 < gDen :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by decide) hpW_z) ht1_z) ht1_z) hl2_pos) (by positivity)
  have hpW4_fits : FitsSignedWord (q + 2) (4 * (pW : ℤ)) := by
    have hcast : (4 * (pW : ℤ)) = ((4 * pW : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    have h1 : 4 * pW < 2 ^ q := lt_of_le_of_lt (by omega : 4 * pW ≤ 4 * q) (four_mul_lt_two_pow (by omega))
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))
  have hgDen_fits_small :
      FitsSignedWord ((q + 2) + (q + 1) + (q + 1) + (2 * S + 4) + 2 * q_pi) gDen :=
    ((((hpW4_fits.mul ht1_fits_q).mul ht1_fits_q).mul hl2_fits_small).mul_two_pow (2 * q_pi))
  have hgDen_fits : FitsSignedWord W gDen :=
    hgDen_fits_small.mono (by dsimp only [q_pi, S]; omega)
  have hg_bound : |gNum| ≤ ((50 * (m1 + 1) : ℕ) : ℤ) * gDen :=
    gNum_abs_le_fifty_mul_gDen m1 pW t1 q_pi q_l2 θNum l2Fixed
      (by dsimp only [q_l2, S]; omega) (by omega) hl2_ge hθ_bound
  obtain ⟨sincVal, hsincVal⟩ : ∃ v : ℤ, v = sincTaylorFixed N_s θNum θDen := ⟨_, rfl⟩
  obtain ⟨expVal, hexpVal⟩ : ∃ v : ℤ, v = expTaylorFixed N_e gNum gDen := ⟨_, rfl⟩
  have hsinc_fits_small : FitsSignedWord (q_accs + 1) sincVal :=
    hsincVal ▸ fitsSignedWord_sincTaylorFixed N_s θNum θDen
  have hexp_fits_small : FitsSignedWord (q_acce + 1) expVal :=
    hexpVal ▸ fitsSignedWord_expTaylorFixed N_e gNum gDen
  have hsinc_fits : FitsSignedWord W sincVal :=
    hsinc_fits_small.mono (by dsimp only [q_accs, N_s, B_sinc, S]; omega)
  have hexp_fits : FitsSignedWord W expVal :=
    hexp_fits_small.mono (by dsimp only [q_acce, N_e, B_exp, S]; omega)
  have hprodSE_fits_small : FitsSignedWord (q_tot + 1) (sincVal * expVal) := by
    rw [hsincVal, hexpVal]
    exact fitsSignedWord_sincTaylorFixed_mul_expTaylorFixed N_s N_e θNum θDen gNum gDen
  have hprodSE_fits : FitsSignedWord W (sincVal * expVal) :=
    hprodSE_fits_small.mono (by dsimp only [q_tot, q_accs, q_acce, N_s, N_e, B_sinc, B_exp, S]; omega)
  have hround_fits : FitsSignedWord W_out (roundShiftInt ((sincVal * expVal) * (2 : ℤ) ^ q) q_tot) := by
    have hsh : FitsSignedWord ((q + 1) + q_tot) ((sincVal * expVal) * (2 : ℤ) ^ q) :=
      (hprodSE_fits_small.mul_two_pow q).mono (by omega)
    exact (FitsSignedWord.roundShiftInt_sub (w := q + 1) (k := q_tot) hsh).mono hW_out
  have htap_eq :
      computeFilterTapFixed K p j1 d =
        roundShiftInt ((sincVal * expVal) * (2 : ℤ) ^ q) q_tot :=
    computeFilterTapFixed_of_le K p j1 d hd_abs sincVal expVal hsincVal hexpVal
  exact bmFilterTapEntryWith_aux_computesInTime hmul
    W W_out B_sinc N_s (50 * (m1 + 1)) N_e q q_l2 q_tot
    (t1 : ℤ) (m1 : ℤ) piFixed θDen gDen (j1.val : ℤ) (k : ℤ)
    sincVal expVal (computeFilterTapFixed K p j1 d)
    hW_out_le
    (by dsimp only [N_s, B_sinc, S]; omega)
    (by dsimp only [N_e, B_exp, S]; omega)
    (by dsimp only [q_l2, S]; omega)
    (by dsimp only [q_tot, q_accs, q_acce, N_s, N_e, B_sinc, B_exp, S]; omega)
    (by omega)
    (by dsimp only [N_s, B_sinc, S]; omega)
    (by dsimp only [N_e, B_exp, S]; omega)
    hk_fits hm1_fits ht1_fits hj1_fits hpi_fits hθDen_fits hθDen_pos hgDen_fits hgDen_pos
    hd_fits hdt1_fits htNum_fits hθNum_fits hθ_bound hθSq_fits hgShift_fits hg_bound
    hsincVal hexpVal hsinc_fits hexp_fits hprodSE_fits hround_fits htap_eq
    tW2 tW3 tW4 tW5 tSch

theorem fitsSignedWord_sqrtPiFixed (S : ℕ) :
    FitsSignedWord (S + 3)
      (max ((2 : ℤ) ^ S) (approxSqrtFixed (6 * S + 18) (approxPiFixed (2 * S)))) := by
  have hpi_nn : 0 ≤ approxPiFixed (2 * S) := approxPiFixed_nonneg (2 * S)
  have hpi_fits : FitsSignedWord (8 * S + 22) (approxPiFixed (2 * S)) :=
    fitsSignedWord_approxPiFixed (2 * S) (by omega)
  have hdiv_lt : (max 0 (approxPiFixed (2 * S))).toNat / 2 ^ (6 * S + 18) < 4 ^ (S + 2) := by
    have hlt : (max 0 (approxPiFixed (2 * S))).toNat < 2 ^ (8 * S + 22) := by
      have h1 : approxPiFixed (2 * S) < (2 : ℤ) ^ (8 * S + 22) := (abs_lt.mp hpi_fits).2
      have h2 : max 0 (approxPiFixed (2 * S)) = approxPiFixed (2 * S) := max_eq_right hpi_nn
      rw [h2]
      exact (Int.toNat_lt hpi_nn).mpr h1
    have hpow : 2 ^ (8 * S + 22) = 4 ^ (S + 2) * 2 ^ (6 * S + 18) := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← Nat.pow_mul, ← pow_add]
      congr 1; omega
    exact Nat.div_lt_of_lt_mul (by linarith only [hlt, hpow])
  have hsq_lt : Nat.sqrt ((max 0 (approxPiFixed (2 * S))).toNat / 2 ^ (6 * S + 18)) < 2 ^ (S + 2) := by
    have h4 : 4 ^ (S + 2) = (2 ^ (S + 2)) ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
    exact Nat.sqrt_lt'.mpr (by rw [← h4]; exact hdiv_lt)
  have hraw_lt : approxSqrtFixed (6 * S + 18) (approxPiFixed (2 * S)) < (2 : ℤ) ^ (S + 3) := by
    unfold approxSqrtFixed
    have h1 : (Nat.sqrt ((max 0 (approxPiFixed (2 * S))).toNat / 2 ^ (6 * S + 18)) : ℤ) <
        (2 : ℤ) ^ (S + 2) := by exact_mod_cast hsq_lt
    exact lt_of_lt_of_le h1 (pow_le_pow_right₀ (by decide) (by omega))
  rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg (le_trans (by positivity) (le_max_left _ _))]
  exact max_lt (pow_lt_pow_right₀ (by decide) (by omega)) hraw_lt

/-- Context encoding for `bmGHatEntryWith`:
`(((W, W_out), (N_erf, Sq)), ((r_s, cFixed), (zDen, denOut)))`. -/
def encGHatEntryCtx (W W_out N_erf Sq : ℕ) (r_s cFixed zDen denOut : ℤ) : List Bool :=
  encPair
    (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
    (encPair
      (encPair (encodeSignedWord W) (encodeSignedWord W))
      (encPair (encodeSignedWord W) (encodeSignedWord W)))
    (((W, W_out), (N_erf, Sq)), ((r_s, cFixed), (zDen, denOut)))

@[simp]
theorem length_encGHatEntryCtx (W W_out N_erf Sq : ℕ) (r_s cFixed zDen denOut : ℤ) :
    (encGHatEntryCtx W W_out N_erf Sq r_s cFixed zDen denOut).length =
      2 * (2 * (2 * W + 2 * W_out + 4) + 2 * (2 * N_erf + 2 * Sq + 4) + 4) +
      2 * (2 * (2 * (W + 1) + 2 * (W + 1) + 4) + 2 * (2 * (W + 1) + 2 * (W + 1) + 4) + 4) + 4 := by
  simp [encGHatEntryCtx]

/-- **Pure-Integer Passband $\hat{g}_{\alpha_\ell}$ Mantissa Entry Stage (`bmGHatEntryWith bmMul`)**:
Consumes `(ctxGHat, yNum_s)` on `kIO` (where `yNum_s = encodeSignedWord W yNum`) and emits
`encodeSignedWord W_out (computeGHatMantissaFixed K p yNum (rEll K))`. -/
def bmGHatEntryWith (bmMul : BitMachine) : BitMachine :=
  let bmCtx := bmFst
  let bmY := bmSnd
  let bmLeft := bmSeq bmCtx bmFst
  let bmRight := bmSeq bmCtx bmSnd
  let bmW := bmSeq (bmSeq bmLeft bmFst) bmFst
  let bmWOut := bmSeq (bmSeq bmLeft bmFst) bmSnd
  let bmNerf := bmSeq (bmSeq bmLeft bmSnd) bmFst
  let bmSq := bmSeq (bmSeq bmLeft bmSnd) bmSnd
  let bmRs := bmSeq (bmSeq bmRight bmFst) bmFst
  let bmCFixed := bmSeq (bmSeq bmRight bmFst) bmSnd
  let bmZDen := bmSeq (bmSeq bmRight bmSnd) bmFst
  let bmDenOut := bmSeq (bmSeq bmRight bmSnd) bmSnd
  let bmTwoY := bmSeq bmY bmSignedDouble
  let bmDiff1 := bmSeq (bmFanout bmRs bmTwoY) bmSignedSub
  let bmZ1Num := bmSeq (bmFanout bmCFixed bmDiff1) (bmSignedMulSameWith bmMul)
  let bmI1 := bmSeq (bmFanout (bmFanout bmW bmNerf) (bmFanout bmZ1Num bmZDen)) (bmErfTaylorWith bmMul)
  let bmSum2 := bmSeq (bmFanout bmRs bmTwoY) bmSignedAdd
  let bmZ2Num := bmSeq (bmFanout bmCFixed bmSum2) (bmSignedMulSameWith bmMul)
  let bmI2 := bmSeq (bmFanout (bmFanout bmW bmNerf) (bmFanout bmZ2Num bmZDen)) (bmErfTaylorWith bmMul)
  let bmSumI := bmSeq (bmFanout bmI1 bmI2) bmSignedAdd
  let bmShifted := bmSeq (bmFanout bmSq bmSumI) bmShiftLeftSigned
  let bmNumOut := bmSeq (bmFanout bmW bmShifted) bmResizeSignedWord
  let bmDiv := bmSeq (bmFanout bmNumOut bmDenOut) bmRoundDivInt
  let bmMax := bmSeq bmDiv bmSignedMaxZero
  bmSeq (bmFanout bmWOut bmMax) bmResizeSignedWord

theorem computeGHatMantissaAuxFixedWithMul_eq_max_roundDivInt (q pW S : ℕ) (yNum : ℤ) (r : ℕ) :
    let q_l2 := 2 * S + (2 * S + 2)
    let l2Fixed := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed (2 * S))
    let cBound := Nat.sqrt (3 * pW) + 1
    let cRawFixed := approxSqrtFixed (2 * S + 2) (4 * (pW : ℤ) * l2Fixed)
    let cFixed := min ((cBound : ℤ) * (2 : ℤ) ^ S) cRawFixed
    let B_erf := 2 * cBound
    let N_erf := 4 * B_erf ^ 2 + (S + B_erf) + 1
    let M := N_erf + 6
    let q_z := M
    let q_acc := 3 * M + 6
    let pi2SFixed := approxPiFixed (2 * S)
    let sqrtPiRawFixed := approxSqrtFixed (6 * S + 18) pi2SFixed
    let sqrtPiFixed := max ((2 : ℤ) ^ S) sqrtPiRawFixed
    let zDen : ℤ := 2 * (r : ℤ) * (2 : ℤ) ^ S
    let denOut : ℤ := sqrtPiFixed * (2 : ℤ) ^ (q_z + q_acc)
    let z1Num : ℤ := cFixed * ((r : ℤ) - 2 * yNum)
    let z2Num : ℤ := cFixed * ((r : ℤ) + 2 * yNum)
    let I1 : ℤ := erfIntegralTaylorFixed N_erf z1Num zDen
    let I2 : ℤ := erfIntegralTaylorFixed N_erf z2Num zDen
    computeGHatMantissaAuxFixedWithMul (· * ·) q pW S yNum r =
      max 0 (roundDivInt ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut) := by
  intro q_l2 l2Fixed cBound cRawFixed cFixed B_erf N_erf M q_z q_acc
    pi2SFixed sqrtPiRawFixed sqrtPiFixed zDen denOut z1Num z2Num I1 I2
  unfold computeGHatMantissaAuxFixedWithMul
  dsimp only
  congr 1
  congr 1
  rw [pow_add, mul_assoc]

set_option maxHeartbeats 800000 in
theorem bmGHatEntryWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W W_out K p : ℕ) (hK : 2 ≤ K) (hW : 1000 * qChildEll K p ≤ W)
    (hW_out_le : W_out ≤ W)
    (yNum : ℤ) (hy0 : 0 ≤ yNum) (hyr : yNum ≤ (rEll K : ℤ))
    (hfits_out : FitsSignedWord W_out (computeGHatMantissaFixed K p yNum (rEll K)))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let pW := pWorkEll K p
    let r := rEll K
    let S := q + 2 * pW + 20
    let q_l2 := 2 * S + (2 * S + 2)
    let l2Fixed := max ((2 : ℤ) ^ (q_l2 - 1)) (approxLogTwoFixed (2 * S))
    let cBound := Nat.sqrt (3 * pW) + 1
    let cRawFixed := approxSqrtFixed (2 * S + 2) (4 * (pW : ℤ) * l2Fixed)
    let cFixed := min ((cBound : ℤ) * (2 : ℤ) ^ S) cRawFixed
    let B_erf := 2 * cBound
    let N_erf := 4 * B_erf ^ 2 + (S + B_erf) + 1
    let M := N_erf + 6
    let q_z := M
    let q_acc := 3 * M + 6
    let pi2SFixed := approxPiFixed (2 * S)
    let sqrtPiRawFixed := approxSqrtFixed (6 * S + 18) pi2SFixed
    let sqrtPiFixed := max ((2 : ℤ) ^ S) sqrtPiRawFixed
    let zDen : ℤ := 2 * (r : ℤ) * (2 : ℤ) ^ S
    let denOut : ℤ := sqrtPiFixed * (2 : ℤ) ^ (q_z + q_acc)
    ∃ t ≤ 2 * (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
        16 * mulTime W + 42000 * W * W + 3000000 * W + 4000000,
      (bmGHatEntryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (fun x => x) (encodeSignedWord W)
            (encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFixed zDen denOut, yNum)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W_out (computeGHatMantissaFixed K p yNum r)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro q pW r S q_l2 l2Fixed cBound cRawFixed cFixed B_erf N_erf M q_z q_acc
    pi2SFixed sqrtPiRawFixed sqrtPiFixed zDen denOut
  let St := Unit
  have hq_eq : q = p + 2 * K + 14 := by unfold q qChildEll pChildEll pWorkEll; omega
  have hpW_eq : pW = p + K + 6 := by unfold pW pWorkEll; rfl
  have hr_pos : 0 < r := rEll_pos K
  have hr_le : r ≤ 2 ^ K := rEll_le_two_pow K
  have hsqrt_sq : Nat.sqrt (3 * pW) * Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le (3 * pW)
  have hsqrt_le : Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le_self (3 * pW)
  have hcBound_sq : cBound * cBound ≤ 9 * pW + 1 := by
    change (Nat.sqrt (3 * pW) + 1) * (Nat.sqrt (3 * pW) + 1) ≤ 9 * pW + 1
    nlinarith only [hsqrt_sq, hsqrt_le]
  have hBerf_sq : B_erf ^ 2 ≤ 36 * pW + 4 := by
    change (2 * cBound) ^ 2 ≤ 36 * pW + 4
    nlinarith only [hcBound_sq]
  have hBerf_mul : B_erf * B_erf ≤ 36 * pW + 4 := by
    change (2 * cBound) * (2 * cBound) ≤ 36 * pW + 4
    nlinarith only [hcBound_sq]
  have hcRaw_nn : 0 ≤ cRawFixed := by unfold cRawFixed approxSqrtFixed; positivity
  have hcFixed_nn : 0 ≤ cFixed := le_min (by positivity) hcRaw_nn
  have hcFixed_le : cFixed ≤ (cBound : ℤ) * (2 : ℤ) ^ S := min_le_left _ _
  have hcFixed_fits_small : FitsSignedWord (S + q) cFixed := by
    rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg hcFixed_nn]
    have hc_pow : (cBound : ℤ) < (2 : ℤ) ^ q := by
      have : cBound < 2 ^ q :=
        lt_of_le_of_lt (by omega : cBound ≤ 4 * q) (four_mul_lt_two_pow (by omega))
      exact_mod_cast this
    calc cFixed ≤ (cBound : ℤ) * (2 : ℤ) ^ S := hcFixed_le
      _ < (2 : ℤ) ^ q * (2 : ℤ) ^ S := mul_lt_mul_of_pos_right hc_pow (by positivity)
      _ = (2 : ℤ) ^ (S + q) := by rw [← pow_add, add_comm]
  have hcFixed_fits : FitsSignedWord W cFixed :=
    hcFixed_fits_small.mono (by dsimp [S] at *; omega)
  have hr_pow : 3 * (r : ℤ) < (2 : ℤ) ^ q := by
    have hr_z : (r : ℤ) ≤ (2 : ℤ) ^ K := by exact_mod_cast hr_le
    have hK_pow : (4 : ℤ) * (2 : ℤ) ^ K ≤ (2 : ℤ) ^ q := by
      have : 2 ^ (K + 2) ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by omega)
      simpa [pow_add, mul_comm] using (by exact_mod_cast this : (2 : ℤ) ^ (K + 2) ≤ (2 : ℤ) ^ q)
    have h2K_pos : (0 : ℤ) < (2 : ℤ) ^ K := by positivity
    linarith only [hr_z, hK_pow, h2K_pos]
  have hr_z_nn : (0 : ℤ) ≤ (r : ℤ) := Nat.cast_nonneg r
  have hr_fits_q : FitsSignedWord q (r : ℤ) :=
    (fitsSignedWord_iff_abs_lt q _).mpr (by rw [abs_of_nonneg hr_z_nn]; linarith only [hr_pow, hr_z_nn])
  have hr_fits : FitsSignedWord W (r : ℤ) := hr_fits_q.mono (by omega)
  have hy_fits_q : FitsSignedWord q yNum :=
    (fitsSignedWord_iff_abs_lt q _).mpr (by rw [abs_of_nonneg hy0]; linarith only [hy0, hyr, hr_pow])
  have hy_fits : FitsSignedWord W yNum := hy_fits_q.mono (by omega)
  have h2y_fits_q : FitsSignedWord q (2 * yNum) :=
    (fitsSignedWord_iff_abs_lt q _).mpr
      (by rw [abs_of_nonneg (by linarith only [hy0])]; linarith only [hy0, hyr, hr_pow])
  have h2y_fits : FitsSignedWord W (2 * yNum) := h2y_fits_q.mono (by omega)
  have hy1_abs : |(r : ℤ) - 2 * yNum| ≤ 2 * (r : ℤ) := by
    rw [abs_le]; constructor <;> linarith only [hy0, hyr]
  have hy2_abs : |(r : ℤ) + 2 * yNum| ≤ 3 * (r : ℤ) := by
    rw [abs_le]; constructor <;> linarith only [hy0, hyr]
  have hy1_abs_3 : |(r : ℤ) - 2 * yNum| ≤ 3 * (r : ℤ) := by
    linarith only [hy1_abs, hr_z_nn]
  have hy1_fits_q : FitsSignedWord q ((r : ℤ) - 2 * yNum) :=
    (fitsSignedWord_iff_abs_lt q _).mpr (lt_of_le_of_lt hy1_abs_3 hr_pow)
  have hy2_fits_q : FitsSignedWord q ((r : ℤ) + 2 * yNum) :=
    (fitsSignedWord_iff_abs_lt q _).mpr (lt_of_le_of_lt hy2_abs hr_pow)
  have hy1_fits : FitsSignedWord W ((r : ℤ) - 2 * yNum) := hy1_fits_q.mono (by omega)
  have hy2_fits : FitsSignedWord W ((r : ℤ) + 2 * yNum) := hy2_fits_q.mono (by omega)
  set z1Num : ℤ := cFixed * ((r : ℤ) - 2 * yNum)
  set z2Num : ℤ := cFixed * ((r : ℤ) + 2 * yNum)
  have hz1_fits_small : FitsSignedWord (S + 2 * q) z1Num :=
    (hcFixed_fits_small.mul hy1_fits_q).mono (by omega)
  have hz2_fits_small : FitsSignedWord (S + 2 * q) z2Num :=
    (hcFixed_fits_small.mul hy2_fits_q).mono (by omega)
  have hz1_fits : FitsSignedWord W z1Num := hz1_fits_small.mono (by dsimp [S] at *; omega)
  have hz2_fits : FitsSignedWord W z2Num := hz2_fits_small.mono (by dsimp [S] at *; omega)
  have hzDen_pos : 0 < zDen := by dsimp [zDen]; positivity
  have hzDen_fits_small : FitsSignedWord (S + q + 1) zDen := by
    have h2r : FitsSignedWord (q + 1) (2 * (r : ℤ)) := by
      have : 2 * (r : ℤ) = (r : ℤ) + (r : ℤ) := by ring
      rw [this]; exact hr_fits_q.add hr_fits_q
    exact (h2r.mul_two_pow S).mono (by omega)
  have hzDen_fits : FitsSignedWord W zDen :=
    hzDen_fits_small.mono (by dsimp [S] at *; omega)
  have hz1_bound : |z1Num| ≤ (B_erf : ℤ) * zDen := by
    rw [abs_mul, abs_of_nonneg hcFixed_nn]
    calc cFixed * |(r : ℤ) - 2 * yNum|
        ≤ ((cBound : ℤ) * (2 : ℤ) ^ S) * (3 * (r : ℤ)) :=
          mul_le_mul hcFixed_le hy1_abs_3 (abs_nonneg _) (by positivity)
      _ ≤ (B_erf : ℤ) * zDen := by
          have hnn : (0 : ℤ) ≤ (cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S := by positivity
          have hid1 : ((cBound : ℤ) * (2 : ℤ) ^ S) * (3 * (r : ℤ)) =
              3 * ((cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S) := by ring
          have hid2 : (B_erf : ℤ) * zDen = 4 * ((cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S) := by
            dsimp [B_erf, zDen]; ring
          linarith only [hnn, hid1, hid2]
  have hz2_bound : |z2Num| ≤ (B_erf : ℤ) * zDen := by
    rw [abs_mul, abs_of_nonneg hcFixed_nn]
    calc cFixed * |(r : ℤ) + 2 * yNum|
        ≤ ((cBound : ℤ) * (2 : ℤ) ^ S) * (3 * (r : ℤ)) :=
          mul_le_mul hcFixed_le hy2_abs (abs_nonneg _) (by positivity)
      _ ≤ (B_erf : ℤ) * zDen := by
          have hnn : (0 : ℤ) ≤ (cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S := by positivity
          have hid1 : ((cBound : ℤ) * (2 : ℤ) ^ S) * (3 * (r : ℤ)) =
              3 * ((cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S) := by ring
          have hid2 : (B_erf : ℤ) * zDen = 4 * ((cBound : ℤ) * (r : ℤ) * (2 : ℤ) ^ S) := by
            dsimp [B_erf, zDen]; ring
          linarith only [hnn, hid1, hid2]
  have hdenOut_fits_small : FitsSignedWord (S + 3 + (q_z + q_acc)) denOut :=
    (fitsSignedWord_sqrtPiFixed S).mul_two_pow (q_z + q_acc)
  have hdenOut_fits : FitsSignedWord W denOut :=
    hdenOut_fits_small.mono (by dsimp [q_z, q_acc, M, N_erf, S] at *; omega)
  have hW_erf : 5 * (N_erf + 6) + 2 * (B_erf * B_erf) + B_erf + 12 ≤ W := by
    dsimp [N_erf, B_erf, S] at *; omega
  let uL1 : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary W_out)
  let uL2 : St → List Bool := encDepPair (fun _ => encUnary N_erf) (fun _ => encUnary (S + q))
  let uLeft : St → List Bool := encDepPair uL1 uL2
  let uR1 : St → List Bool := encDepPair (fun _ => encodeSignedWord W (r : ℤ))
    (fun _ => encodeSignedWord W cFixed)
  let uR2 : St → List Bool := encDepPair (fun _ => encodeSignedWord W zDen)
    (fun _ => encodeSignedWord W denOut)
  let uRight : St → List Bool := encDepPair uR1 uR2
  let uCtx : St → List Bool := encDepPair uLeft uRight
  let pCtx := StageEval.fst uCtx (fun _ => encodeSignedWord W yNum)
  let pY := StageEval.snd uCtx (fun _ => encodeSignedWord W yNum)
  let pLeft := StageEval.seq pCtx (StageEval.fst uLeft uRight)
  let pRight := StageEval.seq pCtx (StageEval.snd uLeft uRight)
  let pWidth := StageEval.seq (StageEval.seq pLeft (StageEval.fst uL1 uL2))
    (StageEval.fst (fun _ => encUnary W) (fun _ => encUnary W_out))
  let pWOut := StageEval.seq (StageEval.seq pLeft (StageEval.fst uL1 uL2))
    (StageEval.snd (fun _ => encUnary W) (fun _ => encUnary W_out))
  let pNerf := StageEval.seq (StageEval.seq pLeft (StageEval.snd uL1 uL2))
    (StageEval.fst (fun _ => encUnary N_erf) (fun _ => encUnary (S + q)))
  let pSq := StageEval.seq (StageEval.seq pLeft (StageEval.snd uL1 uL2))
    (StageEval.snd (fun _ => encUnary N_erf) (fun _ => encUnary (S + q)))
  let pRs := StageEval.seq (StageEval.seq pRight (StageEval.fst uR1 uR2))
    (StageEval.fst (fun _ => encodeSignedWord W (r : ℤ)) (fun _ => encodeSignedWord W cFixed))
  let pCFixed := StageEval.seq (StageEval.seq pRight (StageEval.fst uR1 uR2))
    (StageEval.snd (fun _ => encodeSignedWord W (r : ℤ)) (fun _ => encodeSignedWord W cFixed))
  let pZDen := StageEval.seq (StageEval.seq pRight (StageEval.snd uR1 uR2))
    (StageEval.fst (fun _ => encodeSignedWord W zDen) (fun _ => encodeSignedWord W denOut))
  let pDenOut := StageEval.seq (StageEval.seq pRight (StageEval.snd uR1 uR2))
    (StageEval.snd (fun _ => encodeSignedWord W zDen) (fun _ => encodeSignedWord W denOut))
  have pTwoY := StageEval.seq pY
    (StageEval.const (S := St) (bmSignedDouble_computesInTime W yNum hy_fits h2y_fits))
  have pDiff1 := StageEval.seq (StageEval.fanout pRs pTwoY)
    (StageEval.const (S := St) (bmSignedSub_computesInTime W (r : ℤ) (2 * yNum) hr_fits h2y_fits hy1_fits))
  have pZ1Num := StageEval.seq (StageEval.fanout pCFixed pDiff1)
    (StageEval.const (S := St) (bmSignedMulSameWith_computesInTime hmul W cFixed ((r : ℤ) - 2 * yNum) hcFixed_fits hy1_fits hz1_fits))
  have pI1 : StageEval (S := St)
      (bmSeq (bmFanout (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmFst) bmFst) bmFst)
        (bmSeq (bmSeq (bmSeq bmFst bmFst) bmSnd) bmFst))
        (bmFanout (bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmFst) bmSnd)
          (bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmFst) bmFst)
            (bmSeq bmSnd bmSignedDouble)) bmSignedSub)) (bmSignedMulSameWith bmMul))
          (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmFst)))
        (bmErfTaylorWith bmMul))
      (encDepPair uCtx (fun _ => encodeSignedWord W yNum))
      (fun _ => encodeSignedWord W (erfIntegralTaylorFixed N_erf z1Num zDen))
      _ :=
    StageEval.seq
      (StageEval.fanout (StageEval.fanout pWidth pNerf) (StageEval.fanout pZ1Num pZDen))
      (StageEval.const (S := St) (fun u2 u3 u4 u5 uSc => by
        rcases bmErfTaylorWith_computesInTime hmul B_erf W N_erf z1Num zDen
          hz1_fits hzDen_fits hzDen_pos hz1_bound hW_erf u2 u3 u4 u5 uSc with ⟨t, ht, hc, _⟩
        exact ⟨t, ht, hc⟩))
  have hI1_fits_small :
      FitsSignedWord (5 * (N_erf + 6) + 2 * (B_erf * B_erf) + B_erf + 12)
        (erfIntegralTaylorFixed N_erf z1Num zDen) := by
    rcases bmErfTaylorWith_computesInTime hmul B_erf W N_erf z1Num zDen
      hz1_fits hzDen_fits hzDen_pos hz1_bound hW_erf [] [] [] [] [] with ⟨_, _, _, hf⟩
    exact hf
  have pSum2 := StageEval.seq (StageEval.fanout pRs pTwoY)
    (StageEval.const (S := St) (bmSignedAdd_computesInTime W (r : ℤ) (2 * yNum) hr_fits h2y_fits hy2_fits))
  have pZ2Num := StageEval.seq (StageEval.fanout pCFixed pSum2)
    (StageEval.const (S := St) (bmSignedMulSameWith_computesInTime hmul W cFixed ((r : ℤ) + 2 * yNum) hcFixed_fits hy2_fits hz2_fits))
  have pI2 : StageEval (S := St)
      (bmSeq (bmFanout (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmFst) bmFst) bmFst)
        (bmSeq (bmSeq (bmSeq bmFst bmFst) bmSnd) bmFst))
        (bmFanout (bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmFst) bmSnd)
          (bmSeq (bmFanout (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmFst) bmFst)
            (bmSeq bmSnd bmSignedDouble)) bmSignedAdd)) (bmSignedMulSameWith bmMul))
          (bmSeq (bmSeq (bmSeq bmFst bmSnd) bmSnd) bmFst)))
        (bmErfTaylorWith bmMul))
      (encDepPair uCtx (fun _ => encodeSignedWord W yNum))
      (fun _ => encodeSignedWord W (erfIntegralTaylorFixed N_erf z2Num zDen))
      _ :=
    StageEval.seq
      (StageEval.fanout (StageEval.fanout pWidth pNerf) (StageEval.fanout pZ2Num pZDen))
      (StageEval.const (S := St) (fun u2 u3 u4 u5 uSc => by
        rcases bmErfTaylorWith_computesInTime hmul B_erf W N_erf z2Num zDen
          hz2_fits hzDen_fits hzDen_pos hz2_bound hW_erf u2 u3 u4 u5 uSc with ⟨t, ht, hc, _⟩
        exact ⟨t, ht, hc⟩))
  have hI2_fits_small :
      FitsSignedWord (5 * (N_erf + 6) + 2 * (B_erf * B_erf) + B_erf + 12)
        (erfIntegralTaylorFixed N_erf z2Num zDen) := by
    rcases bmErfTaylorWith_computesInTime hmul B_erf W N_erf z2Num zDen
      hz2_fits hzDen_fits hzDen_pos hz2_bound hW_erf [] [] [] [] [] with ⟨_, _, _, hf⟩
    exact hf
  set I1 := erfIntegralTaylorFixed N_erf z1Num zDen
  set I2 := erfIntegralTaylorFixed N_erf z2Num zDen
  have hI1_fits : FitsSignedWord W I1 := hI1_fits_small.mono hW_erf
  have hI2_fits : FitsSignedWord W I2 := hI2_fits_small.mono hW_erf
  have hSumI_fits_small :
      FitsSignedWord (5 * (N_erf + 6) + 2 * (B_erf * B_erf) + B_erf + 13) (I1 + I2) :=
    hI1_fits_small.add hI2_fits_small
  have hSumI_fits : FitsSignedWord W (I1 + I2) :=
    hSumI_fits_small.mono (by dsimp [N_erf, B_erf, S] at *; omega)
  have hNumOut_fits : FitsSignedWord W ((I1 + I2) * (2 : ℤ) ^ (S + q)) :=
    (hSumI_fits_small.mul_two_pow (S + q)).mono (by dsimp [N_erf, B_erf, S] at *; omega)
  have hDiv_fits : FitsSignedWord W (roundDivInt ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut) :=
    hNumOut_fits.roundDivInt denOut
  have hMax_fits : FitsSignedWord W (max 0 (roundDivInt ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut)) := by
    rw [fitsSignedWord_iff_abs_lt] at hDiv_fits ⊢
    rw [abs_of_nonneg (le_max_left 0 _)]
    exact max_lt (by positivity) (abs_lt.mp hDiv_fits).2
  have pSumI := StageEval.seq (StageEval.fanout pI1 pI2)
    (StageEval.const (S := St) (bmSignedAdd_computesInTime W I1 I2 hI1_fits hI2_fits hSumI_fits))
  have pShifted := StageEval.seq (StageEval.fanout pSq pSumI)
    (StageEval.const (S := St) (bmShiftLeftSigned_computesInTime (S + q) W (I1 + I2) hSumI_fits))
  have hsh_W : FitsSignedWord ((S + q) + W) ((I1 + I2) * (2 : ℤ) ^ (S + q)) := by
    simpa [Nat.add_comm] using hSumI_fits.mul_two_pow (S + q)
  have pNumOut := StageEval.seq (StageEval.fanout pWidth pShifted)
    (StageEval.const (S := St)
      (bmResizeSignedWord_computesInTime ((S + q) + W) W ((I1 + I2) * (2 : ℤ) ^ (S + q))
        hsh_W hNumOut_fits))
  have pDiv := StageEval.seq (StageEval.fanout pNumOut pDenOut)
    (StageEval.const (S := St)
      (bmRoundDivInt_computesInTime W ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut hNumOut_fits hdenOut_fits))
  have pMax := StageEval.seq pDiv
    (StageEval.const (S := St)
      (bmSignedMaxZero_computesInTime W (roundDivInt ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut) hDiv_fits))
  have hghat_eq :
      computeGHatMantissaFixed K p yNum r =
        max 0 (roundDivInt ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut) :=
    computeGHatMantissaAuxFixedWithMul_eq_max_roundDivInt q pW S yNum r
  have hfits_out' : FitsSignedWord W_out (max 0 (roundDivInt ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut)) :=
    hghat_eq ▸ hfits_out
  have pOut := StageEval.seq (StageEval.fanout pWOut pMax)
    (StageEval.const (S := St)
      (bmResizeSignedWord_computesInTime W W_out
        (max 0 (roundDivInt ((I1 + I2) * (2 : ℤ) ^ (S + q)) denOut)) hMax_fits hfits_out'))
  have hall := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W_out (computeGHatMantissaFixed K p yNum r))
    pOut (fun _ => congrArg (encodeSignedWord W_out) hghat_eq.symm)
  have hNerf_le : N_erf ≤ W := by dsimp [N_erf, B_erf, S] at *; omega
  have hSq_le : S + q ≤ W := by dsimp [S] at *; omega
  have hlen_uL1 : (uL1 ()).length ≤ 8 * W + 8 := by
    dsimp only [uL1]; simp only [length_encDepPair, length_encUnary]; omega
  have hlen_uL2 : (uL2 ()).length ≤ 8 * W + 8 := by
    dsimp only [uL2]; simp only [length_encDepPair, length_encUnary]; omega
  have hlen_uLeft : (uLeft ()).length ≤ 32 * W + 36 := by
    dsimp only [uLeft]; simp only [length_encDepPair]; omega
  have hlen_uR1 : (uR1 ()).length ≤ 8 * W + 16 := by
    dsimp only [uR1]; simp only [length_encDepPair, length_encodeSignedWord]; omega
  have hlen_uR2 : (uR2 ()).length ≤ 8 * W + 16 := by
    dsimp only [uR2]; simp only [length_encDepPair, length_encodeSignedWord]; omega
  have hlen_uRight : (uRight ()).length ≤ 32 * W + 68 := by
    dsimp only [uRight]; simp only [length_encDepPair]; omega
  have hlen_uCtx : (uCtx ()).length ≤ 128 * W + 212 := by
    dsimp only [uCtx]; simp only [length_encDepPair]; omega
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  have hcomb :
      (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
      (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) =
      2 * (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) := by ring
  have ht_bound : t ≤ 2 * (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
      16 * mulTime W + 42000 * W * W + 3000000 * W + 4000000 := by
    nlinarith only [ht, hcomb, hlen_uL1, hlen_uL2, hlen_uLeft, hlen_uR1, hlen_uR2,
      hlen_uRight, hlen_uCtx, hNerf_le, hSq_le, hW_out_le]
  exact ⟨t, ht_bound, hcomp⟩

end IntMul
