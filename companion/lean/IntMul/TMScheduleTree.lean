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
import IntMul.EndToEnd
import IntMul.TMCompiler
import IntMul.TMStages
import IntMul.TMArithStages
import IntMul.TMStageEval
import IntMul.TMSchedule

set_option maxRecDepth 20000

/-!
# Uniform 8-Stack `Turing.FinTM2` Schedule Parameter & Multi-Level `ScheduleIntTree` Generator (`IntMul.TMScheduleTree`)

This module compiles all data-independent schedule parameter functions (`chunkBits`, `numChunks`,
`rootK0`, `rootR0`, `rootP0`, `k1Ell`, `k2Ell`, `t1Ell`, `rEll`, `c1Ell`, `pWorkEll`, `pChildEll`,
`qChildEll`, `qBaseEll`, `computeM1Ell`, `isBaseLeaf`, `childScheduleBIn`, `foldedHalfWidth`,
`numBlocks`, `scheduleSlotBits`) and the complete multi-level schedule tree constructor
`computeScheduleIntTree` into concrete, uniform 8-stack `BitMachine` (`Turing.FinTM2`) stages (`Fintype.card Λ = O(1)`,
`|σ| = 32`, `|Γ| = 2`; see Section 3.3 (`sec:tables`), schedule (34) (`eq:cert-sched`), and
Section 8 (`sec:lean`)).
-/

namespace IntMul

open Turing

/-! ## 1. Unary Integer Square Root (`bmUnarySqrt`) -/

/-- Pure step function for unary integer square root (`Nat.sqrt m`):
subtracts consecutive odd integers `2 * s + 1` from remainder `r` while `2 * s + 1 ≤ r`. -/
def unarySqrtStep (p : ℕ × ℕ) : ℕ × ℕ :=
  if 2 * p.2 + 1 ≤ p.1 then (p.1 - (2 * p.2 + 1), p.2 + 1) else p

/-- `k`-step iteration of `unarySqrtStep` starting from `(m, 0)`. -/
def unarySqrtIter (m k : ℕ) : ℕ × ℕ :=
  unarySqrtStep^[k] (m, 0)

@[simp]
theorem unarySqrtIter_zero (m : ℕ) : unarySqrtIter m 0 = (m, 0) := rfl

theorem unarySqrtIter_succ (m k : ℕ) :
    unarySqrtIter m (k + 1) = unarySqrtStep (unarySqrtIter m k) :=
  Function.iterate_succ_apply' unarySqrtStep k (m, 0)

theorem unarySqrtIter_inv (m : ℕ) :
    ∀ k : ℕ,
      (unarySqrtIter m k).1 + (unarySqrtIter m k).2 * (unarySqrtIter m k).2 = m ∧
      (unarySqrtIter m k).2 ≤ k ∧
      ((unarySqrtIter m k).2 < k → (unarySqrtIter m k).1 < 2 * (unarySqrtIter m k).2 + 1)
  | 0 => ⟨by simp, le_rfl, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  | k + 1 => by
    rcases unarySqrtIter_inv m k with ⟨hsum, hle, hlt⟩
    rw [unarySqrtIter_succ, unarySqrtStep]
    set r := (unarySqrtIter m k).1
    set s := (unarySqrtIter m k).2
    by_cases hcond : 2 * s + 1 ≤ r
    · rw [if_pos hcond]
      dsimp only
      have hs_eq : s = k := by
        by_contra hne
        have hs_lt : s < k := lt_of_le_of_ne hle hne
        have hr_lt := hlt hs_lt
        omega
      refine ⟨?_, by omega, fun h => by omega⟩
      have hsq : (s + 1) * (s + 1) = s * s + (2 * s + 1) := by ring
      omega
    · rw [if_neg hcond]
      exact ⟨hsum, by omega, fun _ => by omega⟩

theorem unarySqrtIter_sum_le (m k : ℕ) :
    (unarySqrtIter m k).1 + (unarySqrtIter m k).2 ≤ m := by
  have hsum := (unarySqrtIter_inv m k).1
  have hsq : (unarySqrtIter m k).2 ≤ (unarySqrtIter m k).2 * (unarySqrtIter m k).2 :=
    Nat.le_mul_self _
  omega

theorem unarySqrtIter_snd_self (m : ℕ) :
    (unarySqrtIter m m).2 = Nat.sqrt m := by
  have hinv := unarySqrtIter_inv m m
  set r := (unarySqrtIter m m).1
  set s := (unarySqrtIter m m).2
  rcases hinv with ⟨hsum, hle, hlt⟩
  have h1 : s ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
  have h2 : Nat.sqrt m < s + 1 := by
    rw [Nat.sqrt_lt]
    have hs_le : s ≤ s * s := Nat.le_mul_self s
    have hsq : (s + 1) * (s + 1) = s * s + (2 * s + 1) := by ring
    by_cases hs : s < m
    · have hr := hlt hs
      omega
    · omega
  omega

/-- **Unary Square Root Step (`bmUnarySqrtStep`)**:
Transforms `encPair encUnary encUnary (r, s)` into `encPair encUnary encUnary (unarySqrtStep (r, s))`. -/
def bmUnarySqrtStep : BitMachine :=
  let bm2S1 := bmSeq (bmSeq bmSnd bmUnaryDouble) bmUnarySucc
  bmIte (bmSeq (bmFanout bm2S1 bmFst) bmUnaryLe)
    (bmFanout (bmSeq (bmFanout bmFst bm2S1) bmUnarySub) (bmSeq bmSnd bmUnarySucc))
    bmId

theorem bmUnarySqrtStep_computesStageLe :
    ComputesStageLe bmUnarySqrtStep (encPair encUnary encUnary) (encPair encUnary encUnary)
      unarySqrtStep (fun p => 400 * p.1 + 900 * p.2 + 700) := by
  intro ⟨r, s⟩ tW2 tW3 tW4 tW5 tSch
  let S := Unit
  let uR : S → List Bool := fun _ => encUnary r
  let uS : S → List Bool := fun _ => encUnary s
  let uIn : S → List Bool := encDepPair uR uS
  have pR := StageEval.fst uR uS
  have pS := StageEval.snd uR uS
  have p2S := StageEval.seq pS
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : S => s))
  have p2S1 := StageEval.seq p2S
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => 2 * s))
  have pCond := StageEval.seq (StageEval.fanout p2S1 pR)
    (StageEval.of_computesStageLe bmUnaryLe_computesStageLe (fun _ : S => (2 * s + 1, r)))
  have pSub := StageEval.seq (StageEval.fanout pR p2S1)
    (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (r, 2 * s + 1)))
  have pSuccS := StageEval.seq pS
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : S => s))
  have pThen := StageEval.fanout pSub pSuccS
  have pElse := StageEval.id_stage uIn
  have pIte := StageEval.congr_out
    (v2 := fun _ => encPair encUnary encUnary (unarySqrtStep (r, s)))
    (StageEval.ite_stage pCond pThen pElse)
    (fun _ => by
      dsimp only [unarySqrtStep, uIn, uR, uS, encDepPair, encPair]
      by_cases h : 2 * s + 1 ≤ r
      · rw [decide_eq_true h, if_pos rfl, if_pos h]
      · rw [decide_eq_false h, if_neg Bool.false_ne_true, if_neg h])
  rcases pIte () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uR, uS, id] at ht hcomp ⊢
  have hsub_le : r - (2 * s + 1) ≤ r := Nat.sub_le _ _
  simp only [length_encDepPair, length_encUnary] at ht
  split_ifs at ht <;> exact ⟨t, by omega, hcomp⟩

/-- **Unary Square Root Stage (`bmUnarySqrt`)**:
Consumes `encUnary m` on `kIO` and emits `encUnary (Nat.sqrt m)` on `kIO` in $O(m^2)$ steps. -/
def bmUnarySqrt : BitMachine :=
  bmSeq
    (bmFanout bmId (bmFanout bmId bmUnaryZero))
    (bmSeq (bmIterLoop bmUnarySqrtStep) bmSnd)

theorem bmUnarySqrt_computesStageLe :
    ComputesStageLe bmUnarySqrt encUnary encUnary Nat.sqrt
      (fun m => 1000 * m * m + 800 * m + 300) := by
  intro m tW2 tW3 tW4 tW5 tSch
  let S := Unit
  let uM : S → List Bool := fun _ => encUnary m
  have pInit := StageEval.congr_out
    (v2 := encDepPair uM (fun _ => encPair encUnary encUnary (unarySqrtIter m 0)))
    (StageEval.fanout (StageEval.id_stage uM)
      (StageEval.fanout (StageEval.id_stage uM) (StageEval.constEmpty uM)))
    (fun _ => rfl)
  have pLoop := StageEval.iterLoop_idx (S := S) (k := fun _ => m)
    (u := fun _ i => encPair encUnary encUnary (unarySqrtIter m i))
    (B := fun _ => 900 * m + 700)
    (fun ⟨⟨_, i⟩, _⟩ u2 u3 u4 u5 uSc => by
      rcases bmUnarySqrtStep_computesStageLe (unarySqrtIter m i) u2 u3 u4 u5 uSc with ⟨t, ht, hc⟩
      rw [← unarySqrtIter_succ] at hc
      have hsum := unarySqrtIter_sum_le m i
      dsimp only at ht ⊢
      exact ⟨t, by omega, hc⟩)
  have pSnd := StageEval.congr_out
    (v2 := fun _ => encUnary (Nat.sqrt m))
    (StageEval.snd
      (fun _ : S => encUnary (unarySqrtIter m m).1)
      (fun _ : S => encUnary (unarySqrtIter m m).2))
    (fun _ => congrArg encUnary (unarySqrtIter_snd_self m))
  have hall := StageEval.seq pInit (StageEval.seq pLoop pSnd)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uM, encDepPair, id] at ht hcomp ⊢
  have hsum_m := unarySqrtIter_sum_le m m
  simp only [unarySqrtIter_zero, length_encPair, length_encUnary, List.length_nil,
    List.length_append, length_encodeDelimWord] at ht
  exact ⟨t, by nlinarith, hcomp⟩

/-! ## 2. Unary Schedule Parameter Stages (`bmK1Ell` .. `bmRootP0`) -/

/-- Logical AND on `encPair encBool encBool`. -/
def bmBoolAnd : BitMachine :=
  bmIte bmFst bmSnd (bmConstBool false)

theorem bmBoolAnd_computesStageLe :
    ComputesStageLe bmBoolAnd (encPair encBool encBool) encBool
      (fun p => p.1 && p.2) (fun _ => 100) := by
  have h := bmIte_computesStageLe (bmFst_computesStageLe encBool encBool)
    (bmSnd_computesStageLe encBool encBool)
    (bmConstBool_computesStageLe false (encPair encBool encBool))
  refine (ComputesStageLe.congr_fn h (fun ⟨a, b⟩ => by cases a <;> rfl)).mono (fun ⟨a, b⟩ => ?_)
  cases a <;> cases b <;> decide

/-- Convert `encBool b` into `encUnary (cond b 1 0)` (`[false]` if `true`, `[]` if `false`). -/
def bmBoolToUnaryFlag : BitMachine :=
  bmIte bmId (bmUnaryConst 1) bmUnaryZero

theorem bmBoolToUnaryFlag_computesStageLe :
    ComputesStageLe bmBoolToUnaryFlag encBool encUnary
      (fun b => cond b 1 0) (fun _ => 30) := by
  have h := bmIte_computesStageLe (bmId_computesStageLe encBool)
    (bmUnaryConst_computesStageLe 1 encBool)
    (bmUnaryConst_computesStageLe 0 encBool)
  refine (ComputesStageLe.congr_fn h (fun b => by cases b <;> rfl)).mono (fun b => ?_)
  cases b <;> decide

/-- `K ↦ k1Ell K = K / 2`. -/
def bmK1Ell : BitMachine :=
  bmHalfLenUnary

theorem bmK1Ell_computesStageLe :
    ComputesStageLe bmK1Ell encUnary encUnary k1Ell (fun K => 6 * K + 12) := by
  refine (ComputesStageLe.congr_fn (bmHalfLenUnary_computesStageLe encUnary)
    (fun K => by simp [k1Ell, length_encUnary])).mono (fun K => ?_)
  simp [length_encUnary]

/-- `K ↦ k2Ell K = (K + 1) / 2`. -/
def bmK2Ell : BitMachine :=
  bmSeq bmUnarySucc bmHalfLenUnary

theorem bmK2Ell_computesStageLe :
    ComputesStageLe bmK2Ell encUnary encUnary k2Ell (fun K => 6 * K + 20) := by
  have h := bmSeq_computesStageLe bmUnarySucc_computesStageLe
    (bmHalfLenUnary_computesStageLe encUnary)
  refine (ComputesStageLe.congr_fn h (fun K => by simp [k2Ell, length_encUnary])).mono (fun K => ?_)
  simp [length_encUnary]; omega

/-- `K ↦ t1Ell K = 2 ^ (k1Ell K)`. -/
def bmT1Ell : BitMachine :=
  bmSeq bmK1Ell bmUnaryTwoPow

theorem bmT1Ell_computesStageLe :
    ComputesStageLe bmT1Ell encUnary encUnary t1Ell
      (fun K => 10 * K * t1Ell K + 50 * K + 100) := by
  have h := bmSeq_computesStageLe bmK1Ell_computesStageLe bmUnaryTwoPow_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun K => ?_)
  dsimp only [t1Ell]
  have hk1 : k1Ell K ≤ K := by unfold k1Ell; omega
  have hmul : 10 * k1Ell K * 2 ^ k1Ell K ≤ 10 * K * 2 ^ k1Ell K :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 hk1)
  omega

/-- `K ↦ rEll K = 2 ^ (k2Ell K)`. -/
def bmREll : BitMachine :=
  bmSeq bmK2Ell bmUnaryTwoPow

theorem bmREll_computesStageLe :
    ComputesStageLe bmREll encUnary encUnary rEll
      (fun K => 10 * (K + 1) * rEll K + 50 * K + 120) := by
  have h := bmSeq_computesStageLe bmK2Ell_computesStageLe bmUnaryTwoPow_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun K => ?_)
  dsimp only [rEll]
  have hk2 : k2Ell K ≤ K + 1 := by unfold k2Ell; omega
  have hmul : 10 * k2Ell K * 2 ^ k2Ell K ≤ 10 * (K + 1) * 2 ^ k2Ell K :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 hk2)
  omega

/-- `K ↦ c1Ell K = rEll K / t1Ell K = rEll K / 2 ^ (k1Ell K)`. -/
def bmC1Ell : BitMachine :=
  bmSeq (bmFanout bmK1Ell bmREll) bmUnaryShiftRight

theorem bmC1Ell_computesStageLe :
    ComputesStageLe bmC1Ell encUnary encUnary c1Ell
      (fun K => 25 * (K + 1) * rEll K + 120 * K + 300) := by
  have h1 := bmFanout_computesStageLe bmK1Ell_computesStageLe bmREll_computesStageLe
  have h := bmSeq_computesStageLe h1 bmUnaryShiftRight_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun K => ?_)
  dsimp only
  simp only [length_encUnary]
  have hk1 : k1Ell K ≤ K := by unfold k1Ell; omega
  have hr_pos : 1 ≤ rEll K := rEll_pos K
  have hsh : k1Ell K * (6 * rEll K + 15) ≤ K * (6 * rEll K + 15) :=
    Nat.mul_le_mul_right _ hk1
  nlinarith

/-- `(K, p) ↦ pWorkEll K p = p + K + 6`. -/
def bmPWorkEll : BitMachine :=
  bmSeq bmUnaryAdd (bmSeq (bmFanout bmId (bmUnaryConst 6)) bmUnaryAdd)

theorem bmPWorkEll_computesStageLe :
    ComputesStageLe bmPWorkEll (encPair encUnary encUnary) encUnary
      (fun p => pWorkEll p.1 p.2)
      (fun p => 25 * p.1 + 25 * p.2 + 100) := by
  have h1 := bmFanout_computesStageLe (bmId_computesStageLe encUnary)
    (bmUnaryConst_computesStageLe 6 encUnary)
  have h := bmSeq_computesStageLe bmUnaryAdd_computesStageLe
    (bmSeq_computesStageLe h1 bmUnaryAdd_computesStageLe)
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => by
    dsimp only [pWorkEll, id]; congr 1; omega)).mono (fun ⟨K, p⟩ => ?_)
  dsimp only [id]
  simp only [length_encUnary]
  omega

/-- `(K, p) ↦ pChildEll K p = pWorkEll K p + K + 6`. -/
def bmPChildEll : BitMachine :=
  bmSeq (bmFanout bmFst bmPWorkEll) bmPWorkEll

theorem bmPChildEll_computesStageLe :
    ComputesStageLe bmPChildEll (encPair encUnary encUnary) encUnary
      (fun p => pChildEll p.1 p.2)
      (fun p => 120 * p.1 + 80 * p.2 + 500) := by
  have h1 := bmFanout_computesStageLe (bmFst_computesStageLe encUnary encUnary)
    bmPWorkEll_computesStageLe
  have h := bmSeq_computesStageLe h1 bmPWorkEll_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => rfl)).mono (fun ⟨K, p⟩ => ?_)
  dsimp only [pWorkEll]
  simp only [length_encPair, length_encUnary]
  omega

/-- `(K, p) ↦ qChildEll K p = pChildEll K p + 2`. -/
def bmQChildEll : BitMachine :=
  bmSeq bmPChildEll (bmSeq bmUnarySucc bmUnarySucc)

theorem bmQChildEll_computesStageLe :
    ComputesStageLe bmQChildEll (encPair encUnary encUnary) encUnary
      (fun p => qChildEll p.1 p.2)
      (fun p => 120 * p.1 + 80 * p.2 + 510) := by
  have h := bmSeq_computesStageLe bmPChildEll_computesStageLe
    (bmSeq_computesStageLe bmUnarySucc_computesStageLe bmUnarySucc_computesStageLe)
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => rfl)).mono (fun ⟨K, p⟩ => ?_)
  dsimp only; omega

/-- `(K, p) ↦ qBaseEll K p = p + K + 4`. -/
def bmQBaseEll : BitMachine :=
  bmSeq bmUnaryAdd (bmSeq (bmFanout bmId (bmUnaryConst 4)) bmUnaryAdd)

theorem bmQBaseEll_computesStageLe :
    ComputesStageLe bmQBaseEll (encPair encUnary encUnary) encUnary
      (fun p => qBaseEll p.1 p.2)
      (fun p => 25 * p.1 + 25 * p.2 + 100) := by
  have h1 := bmFanout_computesStageLe (bmId_computesStageLe encUnary)
    (bmUnaryConst_computesStageLe 4 encUnary)
  have h := bmSeq_computesStageLe bmUnaryAdd_computesStageLe
    (bmSeq_computesStageLe h1 bmUnaryAdd_computesStageLe)
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => by
    dsimp only [qBaseEll, id]; congr 1; omega)).mono (fun ⟨K, p⟩ => ?_)
  dsimp only [id]
  simp only [length_encUnary]
  omega

/-- `(K, p) ↦ computeM1Ell K p = Nat.sqrt (pWorkEll K p * pChildEll K p) + 1`. -/
def bmComputeM1Ell : BitMachine :=
  bmSeq (bmSeq (bmFanout bmPWorkEll bmPChildEll) bmUnaryMul)
    (bmSeq bmUnarySqrt bmUnarySucc)

theorem bmComputeM1Ell_computesStageLe :
    ComputesStageLe bmComputeM1Ell (encPair encUnary encUnary) encUnary
      (fun p => computeM1Ell p.1 p.2)
      (fun p =>
        let q := qChildEll p.1 p.2
        1100 * q * q * q * q + 2000 * q * q + 5000) := by
  have h1 := bmFanout_computesStageLe bmPWorkEll_computesStageLe bmPChildEll_computesStageLe
  have h2 := bmSeq_computesStageLe h1 bmUnaryMul_computesStageLe
  have h := bmSeq_computesStageLe h2
    (bmSeq_computesStageLe bmUnarySqrt_computesStageLe bmUnarySucc_computesStageLe)
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun ⟨K, p⟩ => ?_)
  dsimp only
  simp only [length_encPair, length_encUnary]
  set q := qChildEll K p
  have hq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hpW : pWorkEll K p ≤ q := by unfold pWorkEll; omega
  have hpC : pChildEll K p ≤ q := by rw [pChildEll_eq]; omega
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ q * q := Nat.le_mul_self q
  have hq4 : q * q ≤ q * q * q * q := by nlinarith
  have hprod : pWorkEll K p * pChildEll K p ≤ q * q := Nat.mul_le_mul hpW hpC
  have hmul3 : pWorkEll K p * pWorkEll K p * pChildEll K p ≤ q * q * q * q := by
    calc pWorkEll K p * pWorkEll K p * pChildEll K p
        ≤ q * q * q := Nat.mul_le_mul (Nat.mul_le_mul hpW hpW) hpC
      _ ≤ q * q * q * q := Nat.le_mul_of_pos_right _ hq1
  have hsq4 :
      (pWorkEll K p * pChildEll K p) * (pWorkEll K p * pChildEll K p) ≤ q * q * q * q := by
    calc (pWorkEll K p * pChildEll K p) * (pWorkEll K p * pChildEll K p)
        ≤ (q * q) * (q * q) := Nat.mul_le_mul hprod hprod
      _ = q * q * q * q := by ring
  nlinarith

theorem two_pow_le_iff_lt_bitLength (K m : ℕ) :
    2 ^ K ≤ m ↔ K < bitLength m := by
  rw [← clog2_succ_eq_bitLength m, ← not_le, ← not_lt,
    Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  omega

/-- `(K, p) ↦ isBaseLeaf K p = decide (2 ^ K ≤ 4 * p * p) = decide (K < bitLength (4 * p * p))`.
Evaluated in $O(K + p^3)$ unary steps via `bmUnaryBitLength` without computing $2^K$ in unary. -/
def bmIsBaseLeaf : BitMachine :=
  let bmTwoP := bmSeq bmSnd bmUnaryDouble
  let bmFourP2 := bmSeq (bmFanout bmTwoP bmTwoP) bmUnaryMul
  let bmBitLen := bmSeq bmFourP2 bmUnaryBitLength
  bmSeq (bmFanout bmFst bmBitLen) bmUnaryLt

theorem bitLength_le_self (m : ℕ) : bitLength m ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [bitLength_pos hm]
      have hdiv := ih (m / 2) (Nat.div_lt_self hm (by decide))
      omega

theorem bmIsBaseLeaf_computesStageLe :
    ComputesStageLe bmIsBaseLeaf (encPair encUnary encUnary) encBool
      (fun p => isBaseLeaf p.1 p.2)
      (fun p => 500 * p.2 * p.2 * p.2 + 1200 * p.2 * p.2 + 300 * p.1 + 1000 * p.2 + 1000) := by
  have pK := bmFst_computesStageLe encUnary encUnary
  have pP := bmSnd_computesStageLe encUnary encUnary
  have p2P := bmSeq_computesStageLe pP bmUnaryDouble_computesStageLe
  have p4P2 := bmSeq_computesStageLe (bmFanout_computesStageLe p2P p2P) bmUnaryMul_computesStageLe
  have pBitLen := bmSeq_computesStageLe p4P2 bmUnaryBitLength_computesStageLe
  have h := bmSeq_computesStageLe (bmFanout_computesStageLe pK pBitLen) bmUnaryLt_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => ?_)).mono (fun ⟨K, p⟩ => ?_)
  · dsimp only [isBaseLeaf]
    have h4 : 2 * p * (2 * p) = 4 * p * p := by ring
    rw [h4]
    exact congrArg encBool (decide_eq_decide.mpr (two_pow_le_iff_lt_bitLength K (4 * p * p)).symm)
  · dsimp only
    simp only [length_encPair, length_encUnary]
    have hb : bitLength (2 * p * (2 * p)) ≤ 4 * p * p := by
      have h4 : 2 * p * (2 * p) = 4 * p * p := by ring
      rw [h4]; exact bitLength_le_self (4 * p * p)
    nlinarith

/-- Predicate `(!isBaseLeaf K p) && decide (2 ≤ K)` characterizing internal schedule tree nodes. -/
def isInternalScheduleNode (K p : ℕ) : Bool :=
  (!isBaseLeaf K p) && decide (2 ≤ K)

theorem isInternalScheduleNode_eq_true_iff (K p : ℕ) :
    isInternalScheduleNode K p = true ↔ (!isBaseLeaf K p) = true ∧ 2 ≤ K := by
  simp [isInternalScheduleNode]

/-- `(K, p) ↦ isInternalScheduleNode K p`. -/
def bmIsInternalNode : BitMachine :=
  bmSeq
    (bmFanout
      (bmSeq bmIsBaseLeaf bmBoolNot)
      (bmSeq (bmFanout (bmUnaryConst 2) bmFst) bmUnaryLe))
    bmBoolAnd

theorem bmIsInternalNode_computesStageLe :
    ComputesStageLe bmIsInternalNode (encPair encUnary encUnary) encBool
      (fun p => isInternalScheduleNode p.1 p.2)
      (fun p => 500 * p.2 * p.2 * p.2 + 1200 * p.2 * p.2 + 500 * p.1 + 1200 * p.2 + 2000) := by
  have pNotLeaf := bmSeq_computesStageLe bmIsBaseLeaf_computesStageLe bmBoolNot_computesStageLe
  have pK2 := bmSeq_computesStageLe
    (bmFanout_computesStageLe
      (bmUnaryConst_computesStageLe 2 (encPair encUnary encUnary))
      (bmFst_computesStageLe encUnary encUnary))
    bmUnaryLe_computesStageLe
  have h := bmSeq_computesStageLe (bmFanout_computesStageLe pNotLeaf pK2) bmBoolAnd_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨K, p⟩ => rfl)).mono (fun ⟨K, p⟩ => ?_)
  dsimp only [encBool]
  simp only [length_encPair, length_encUnary, List.length_singleton]
  omega

/-- `((K, p), B_in) ↦ childScheduleBIn K p B_in = B_in + Nat.clog 2 (2 * pChildEll K p + 4)`. -/
def bmChildScheduleBIn : BitMachine :=
  let bmPC := bmSeq bmFst bmPChildEll
  let bmTwoPC := bmSeq bmPC bmUnaryDouble
  let bmArg := bmSeq (bmFanout bmTwoPC (bmUnaryConst 4)) bmUnaryAdd
  let bmClog := bmSeq bmArg bmUnaryClog2
  bmSeq (bmFanout bmSnd bmClog) bmUnaryAdd

theorem bmChildScheduleBIn_computesStageLe :
    ComputesStageLe bmChildScheduleBIn (encPair (encPair encUnary encUnary) encUnary) encUnary
      (fun x => childScheduleBIn x.1.1 x.1.2 x.2)
      (fun x => 2000 * x.1.1 + 1500 * x.1.2 + 50 * x.2 + 12000) := by
  let encIn := encPair (encPair encUnary encUnary) encUnary
  have pKP := bmFst_computesStageLe (encPair encUnary encUnary) encUnary
  have pB := bmSnd_computesStageLe (encPair encUnary encUnary) encUnary
  have pPC := bmSeq_computesStageLe pKP bmPChildEll_computesStageLe
  have p2PC := bmSeq_computesStageLe pPC bmUnaryDouble_computesStageLe
  have pArg := bmSeq_computesStageLe
    (bmFanout_computesStageLe p2PC (bmUnaryConst_computesStageLe 4 encIn))
    bmUnaryAdd_computesStageLe
  have pClog := bmSeq_computesStageLe pArg bmUnaryClog2_computesStageLe
  have h := bmSeq_computesStageLe (bmFanout_computesStageLe pB pClog) bmUnaryAdd_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨⟨K, p⟩, B_in⟩ => rfl)).mono (fun ⟨⟨K, p⟩, B_in⟩ => ?_)
  dsimp only [encIn]
  have hpC_eq := pChildEll_eq K p
  have hclog_le : Nat.clog 2 (2 * pChildEll K p + 4) ≤ 2 * pChildEll K p + 4 := by
    rw [clog2_eq_bitLength_pred]
    have hbit : ∀ m : ℕ, bitLength m ≤ m := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · rw [bitLength_pos hm]
          have hdiv := ih (m / 2) (Nat.div_lt_self hm (by decide))
          omega
    exact (hbit _).trans (Nat.sub_le _ 1)
  simp only [length_encPair, length_encUnary]
  omega

/-- `((K, p), B_in) ↦ ((k2Ell K, pChildEll K p), childScheduleBIn K p B_in)`. -/
def bmNextScheduleParams : BitMachine :=
  bmFanout
    (bmSeq bmFst (bmFanout (bmSeq bmFst bmK2Ell) bmPChildEll))
    bmChildScheduleBIn

theorem bmNextScheduleParams_computesStageLe :
    ComputesStageLe bmNextScheduleParams
      (encPair (encPair encUnary encUnary) encUnary)
      (encPair (encPair encUnary encUnary) encUnary)
      (fun x => ((k2Ell x.1.1, pChildEll x.1.1 x.1.2), childScheduleBIn x.1.1 x.1.2 x.2))
      (fun x => 2500 * x.1.1 + 2000 * x.1.2 + 100 * x.2 + 15000) := by
  have pKP := bmFst_computesStageLe (encPair encUnary encUnary) encUnary
  have pK2 := bmSeq_computesStageLe (bmFst_computesStageLe encUnary encUnary) bmK2Ell_computesStageLe
  have pLeft := bmSeq_computesStageLe pKP (bmFanout_computesStageLe pK2 bmPChildEll_computesStageLe)
  have h := bmFanout_computesStageLe pLeft bmChildScheduleBIn_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨⟨K, p⟩, B_in⟩ => rfl)).mono (fun ⟨⟨K, p⟩, B_in⟩ => ?_)
  dsimp only
  have hk2 : k2Ell K ≤ K := by unfold k2Ell; omega
  have hpC_eq := pChildEll_eq K p
  have hB_le : childScheduleBIn K p B_in ≤ B_in + 2 * pChildEll K p + 4 := by
    unfold childScheduleBIn
    have hbit : ∀ m : ℕ, bitLength m ≤ m := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · rw [bitLength_pos hm]
          have hdiv := ih (m / 2) (Nat.div_lt_self hm (by decide))
          omega
    have hc : Nat.clog 2 (2 * pChildEll K p + 4) ≤ 2 * pChildEll K p + 4 := by
      rw [clog2_eq_bitLength_pred]
      exact (hbit _).trans (Nat.sub_le _ 1)
    omega
  simp only [length_encPair, length_encUnary]
  omega

/-- `(W, r) ↦ foldedHalfWidth W r = min W r`. -/
def bmFoldedHalfWidth : BitMachine :=
  bmUnaryMin

theorem bmFoldedHalfWidth_computesStageLe :
    ComputesStageLe bmFoldedHalfWidth (encPair encUnary encUnary) encUnary
      (fun p => foldedHalfWidth p.1 p.2)
      (fun p => 160 * p.1 + 25 * p.2 + 120) :=
  bmUnaryMin_computesStageLe

/-- `(r, W_tilde) ↦ numBlocks r W_tilde = ceilDiv r W_tilde` (`0 < W_tilde`). -/
def bmNumBlocks : BitMachine :=
  bmUnaryCeilDiv

theorem bmNumBlocks_computesInTime (r W_tilde : ℕ) (hW : 0 < W_tilde)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 20 * r + 10 * W_tilde + 25,
      bmNumBlocks.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (r, W_tilde)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encUnary (numBlocks r W_tilde)))
          [] [] tW2 tW3 tW4 tW5 tSch) t :=
  bmUnaryCeilDiv_computesInTime r W_tilde hW tW2 tW3 tW4 tW5 tSch

/-- `((q_child, B_in), W_tilde) ↦ kroneckerSlotBitsWithIn q_child B_in W_tilde`. -/
def bmKroneckerSlotBitsWithIn : BitMachine :=
  let bm2Q := bmSeq (bmSeq bmFst bmFst) bmUnaryDouble
  let bmB := bmSeq bmFst bmSnd
  let bm2QB := bmSeq (bmFanout bm2Q bmB) bmUnaryAdd
  let bm2W1 := bmSeq (bmSeq bmSnd bmUnaryDouble) bmUnarySucc
  let bmClog := bmSeq bm2W1 bmUnaryClog2
  let bmSum1 := bmSeq (bmFanout bm2QB bmClog) bmUnaryAdd
  bmSeq (bmFanout bmSum1 (bmUnaryConst 4)) bmUnaryAdd

theorem bmKroneckerSlotBitsWithIn_computesStageLe :
    ComputesStageLe bmKroneckerSlotBitsWithIn
      (encPair (encPair encUnary encUnary) encUnary) encUnary
      (fun x => kroneckerSlotBitsWithIn x.1.1 x.1.2 x.2)
      (fun x => 200 * x.1.1 + 100 * x.1.2 + 500 * x.2 + 1000) := by
  let encIn := encPair (encPair encUnary encUnary) encUnary
  have pFst := bmFst_computesStageLe (encPair encUnary encUnary) encUnary
  have pSnd := bmSnd_computesStageLe (encPair encUnary encUnary) encUnary
  have pQ := bmSeq_computesStageLe pFst (bmFst_computesStageLe encUnary encUnary)
  have pB := bmSeq_computesStageLe pFst (bmSnd_computesStageLe encUnary encUnary)
  have p2Q := bmSeq_computesStageLe pQ bmUnaryDouble_computesStageLe
  have p2QB := bmSeq_computesStageLe (bmFanout_computesStageLe p2Q pB) bmUnaryAdd_computesStageLe
  have p2W1 := bmSeq_computesStageLe
    (bmSeq_computesStageLe pSnd bmUnaryDouble_computesStageLe)
    bmUnarySucc_computesStageLe
  have pClog := bmSeq_computesStageLe p2W1 bmUnaryClog2_computesStageLe
  have pSum1 := bmSeq_computesStageLe (bmFanout_computesStageLe p2QB pClog) bmUnaryAdd_computesStageLe
  have h := bmSeq_computesStageLe
    (bmFanout_computesStageLe pSum1 (bmUnaryConst_computesStageLe 4 encIn))
    bmUnaryAdd_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨⟨q_c, B_in⟩, W_t⟩ => rfl)).mono
    (fun ⟨⟨q_c, B_in⟩, W_t⟩ => ?_)
  dsimp only [encIn]
  have hbit : ∀ m : ℕ, bitLength m ≤ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [bitLength_pos hm]
        have hdiv := ih (m / 2) (Nat.div_lt_self hm (by decide))
        omega
  have hc : Nat.clog 2 (2 * W_t + 1) ≤ 2 * W_t + 1 := by
    rw [clog2_eq_bitLength_pred]
    exact (hbit _).trans (Nat.sub_le _ 1)
  simp only [length_encPair, length_encUnary]
  omega

/-- `((K, p), (B_in, m1)) ↦ scheduleSlotBits K p B_in m1`. -/
def bmScheduleSlotBits : BitMachine :=
  let bmKP := bmFst
  let bmK := bmSeq bmKP bmFst
  let bmBIn := bmSeq bmSnd bmFst
  let bmM1 := bmSeq bmSnd bmSnd
  let bmQ := bmSeq bmKP bmQChildEll
  let bm2M1_1 := bmSeq (bmSeq bmM1 bmUnaryDouble) bmUnarySucc
  let bmClogM1 := bmSeq bm2M1_1 bmUnaryClog2
  let bmQRaw := bmSeq (bmFanout (bmSeq bmQ bmUnarySucc) bmClogM1) bmUnaryAdd
  let bmK4 := bmSeq (bmFanout bmK (bmUnaryConst 4)) bmUnaryAdd
  let bmB1 := bmSeq bmBIn bmUnarySucc
  let bmMaxB := bmSeq (bmFanout bmK4 bmB1) bmUnaryMax
  let bmR := bmSeq bmK bmREll
  let bmWTilde := bmSeq (bmFanout bmM1 bmR) bmFoldedHalfWidth
  bmSeq (bmFanout (bmFanout bmQRaw bmMaxB) bmWTilde) bmKroneckerSlotBitsWithIn

theorem bmScheduleSlotBits_computesStageLe :
    ComputesStageLe bmScheduleSlotBits
      (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)) encUnary
      (fun x => scheduleSlotBits x.1.1 x.1.2 x.2.1 x.2.2)
      (fun x =>
        50 * (x.1.1 + 1) * rEll x.1.1 + 3000 * x.1.1 + 2500 * x.1.2 +
        500 * x.2.1 + 2500 * x.2.2 + 20000) := by
  let encU := encUnary
  let encP := encPair encU encU
  let encIn := encPair encP encP
  have pKP := bmFst_computesStageLe encP encP
  have pBM := bmSnd_computesStageLe encP encP
  have pK := bmSeq_computesStageLe pKP (bmFst_computesStageLe encU encU)
  have pBIn := bmSeq_computesStageLe pBM (bmFst_computesStageLe encU encU)
  have pM1 := bmSeq_computesStageLe pBM (bmSnd_computesStageLe encU encU)
  have pQ := bmSeq_computesStageLe pKP bmQChildEll_computesStageLe
  have p2M1_1 := bmSeq_computesStageLe
    (bmSeq_computesStageLe pM1 bmUnaryDouble_computesStageLe)
    bmUnarySucc_computesStageLe
  have pClogM1 := bmSeq_computesStageLe p2M1_1 bmUnaryClog2_computesStageLe
  have pQRaw := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmSeq_computesStageLe pQ bmUnarySucc_computesStageLe) pClogM1)
    bmUnaryAdd_computesStageLe
  have pK4 := bmSeq_computesStageLe
    (bmFanout_computesStageLe pK (bmUnaryConst_computesStageLe 4 encIn))
    bmUnaryAdd_computesStageLe
  have pB1 := bmSeq_computesStageLe pBIn bmUnarySucc_computesStageLe
  have pMaxB := bmSeq_computesStageLe (bmFanout_computesStageLe pK4 pB1) bmUnaryMax_computesStageLe
  have pR := bmSeq_computesStageLe pK bmREll_computesStageLe
  have pWTilde := bmSeq_computesStageLe
    (bmFanout_computesStageLe pM1 pR) bmFoldedHalfWidth_computesStageLe
  have h := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmFanout_computesStageLe pQRaw pMaxB) pWTilde)
    bmKroneckerSlotBitsWithIn_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun ⟨⟨K, p⟩, ⟨B_in, m1⟩⟩ => rfl)).mono
    (fun ⟨⟨K, p⟩, ⟨B_in, m1⟩⟩ => ?_)
  dsimp only [encIn, encP, encU]
  have hc : Nat.clog 2 (2 * m1 + 1) ≤ 2 * m1 + 1 := by
    rw [clog2_eq_bitLength_pred]
    exact (bitLength_le_self _).trans (Nat.sub_le _ 1)
  have hq_eq := qChildEll_eq K p
  have hW_le : foldedHalfWidth m1 (rEll K) ≤ m1 := min_le_left _ _
  have hmax_le : max (K + 4) (B_in + 1) ≤ K + B_in + 5 := by omega
  have hr_pos : 1 ≤ rEll K := rEll_pos K
  have hr_le : rEll K ≤ (K + 1) * rEll K := Nat.le_mul_of_pos_left _ (by omega)
  simp only [length_encPair, length_encUnary]
  nlinarith

/-- `n ↦ chunkBits n = max 4 (Nat.log 2 n)`. -/
def bmChunkBits : BitMachine :=
  bmSeq (bmFanout (bmUnaryConst 4) bmUnaryLog2) bmUnaryMax

theorem bmChunkBits_computesStageLe :
    ComputesStageLe bmChunkBits encUnary encUnary chunkBits
      (fun n => 120 * n + 850) := by
  have h := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmUnaryConst_computesStageLe 4 encUnary) bmUnaryLog2_computesStageLe)
    bmUnaryMax_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun n => ?_)
  dsimp only
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  simp only [length_encUnary]
  omega

/-- `n ↦ numChunks n = ceilDiv n (chunkBits n)`. -/
def bmNumChunks : BitMachine :=
  bmSeq (bmFanout bmId bmChunkBits) bmUnaryCeilDiv

theorem bmNumChunks_computesStageLe :
    ComputesStageLe bmNumChunks encUnary encUnary numChunks
      (fun n => 180 * n + 1000) := by
  intro n tW2 tW3 tW4 tW5 tSch
  let S := Unit
  have p1 := StageEval.fanout
    (StageEval.id_stage (fun _ : S => encUnary n))
    (StageEval.of_computesStageLe bmChunkBits_computesStageLe (fun _ => n))
  have hb_pos : 0 < chunkBits n := by unfold chunkBits; omega
  have p2 := StageEval.const (S := S) (bmUnaryCeilDiv_computesInTime n (chunkBits n) hb_pos)
  rcases StageEval.seq p1 p2 () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id] at ht hcomp ⊢
  have hb_le : chunkBits n ≤ n + 4 := by
    unfold chunkBits
    have := Nat.log_le_self 2 n
    omega
  simp only [length_encUnary] at ht
  exact ⟨t, by omega, hcomp⟩

/-- `n ↦ rootK0 n = max 2 (Nat.clog 2 (2 * max 1 (numChunks n)))`. -/
def bmRootK0 : BitMachine :=
  let bmMax1N := bmSeq (bmFanout (bmUnaryConst 1) bmNumChunks) bmUnaryMax
  let bmClog := bmSeq (bmSeq bmMax1N bmUnaryDouble) bmUnaryClog2
  bmSeq (bmFanout (bmUnaryConst 2) bmClog) bmUnaryMax

theorem bmRootK0_computesStageLe :
    ComputesStageLe bmRootK0 encUnary encUnary rootK0
      (fun n => 600 * n + 3500) := by
  have pMax1N := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmUnaryConst_computesStageLe 1 encUnary) bmNumChunks_computesStageLe)
    bmUnaryMax_computesStageLe
  have pClog := bmSeq_computesStageLe
    (bmSeq_computesStageLe pMax1N bmUnaryDouble_computesStageLe)
    bmUnaryClog2_computesStageLe
  have h := bmSeq_computesStageLe
    (bmFanout_computesStageLe (bmUnaryConst_computesStageLe 2 encUnary) pClog)
    bmUnaryMax_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun n => ?_)
  dsimp only
  have hN_le : numChunks n ≤ n := ceilDiv_le_self n (chunkBits n)
  have hc : Nat.clog 2 (2 * max 1 (numChunks n)) ≤ 2 * n + 2 := by
    rw [clog2_eq_bitLength_pred]
    have hm : 2 * max 1 (numChunks n) - 1 ≤ 2 * n + 2 := by omega
    exact (bitLength_le_self _).trans hm
  simp only [length_encUnary]
  omega

/-- `n ↦ rootR0 n = 2 ^ rootK0 n`. -/
def bmRootR0 : BitMachine :=
  bmSeq bmRootK0 bmUnaryTwoPow

theorem bmRootR0_computesStageLe :
    ComputesStageLe bmRootR0 encUnary encUnary rootR0
      (fun n => 10 * rootK0 n * rootR0 n + 700 * n + 4000) := by
  have h := bmSeq_computesStageLe bmRootK0_computesStageLe bmUnaryTwoPow_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun n => ?_)
  dsimp only [rootR0]
  have hK0 : rootK0 n ≤ 2 * n + 4 := by
    unfold rootK0
    have hN_le : numChunks n ≤ n := ceilDiv_le_self n (chunkBits n)
    have hc : Nat.clog 2 (2 * max 1 (numChunks n)) ≤ 2 * n + 2 := by
      rw [clog2_eq_bitLength_pred]
      have hm : 2 * max 1 (numChunks n) - 1 ≤ 2 * n + 2 := by omega
      exact (bitLength_le_self _).trans hm
    omega
  nlinarith

/-- `n ↦ rootP0 n = 2 * chunkBits n + 2 * rootK0 n + 6`. -/
def bmRootP0 : BitMachine :=
  let bm2B := bmSeq bmChunkBits bmUnaryDouble
  let bm2K := bmSeq bmRootK0 bmUnaryDouble
  let bmSum1 := bmSeq (bmFanout bm2B bm2K) bmUnaryAdd
  bmSeq (bmFanout bmSum1 (bmUnaryConst 6)) bmUnaryAdd

theorem bmRootP0_computesStageLe :
    ComputesStageLe bmRootP0 encUnary encUnary rootP0
      (fun n => 1000 * n + 6000) := by
  have p2B := bmSeq_computesStageLe bmChunkBits_computesStageLe bmUnaryDouble_computesStageLe
  have p2K := bmSeq_computesStageLe bmRootK0_computesStageLe bmUnaryDouble_computesStageLe
  have pSum1 := bmSeq_computesStageLe (bmFanout_computesStageLe p2B p2K) bmUnaryAdd_computesStageLe
  have h := bmSeq_computesStageLe
    (bmFanout_computesStageLe pSum1 (bmUnaryConst_computesStageLe 6 encUnary))
    bmUnaryAdd_computesStageLe
  refine (ComputesStageLe.congr_fn h (fun _ => rfl)).mono (fun n => ?_)
  dsimp only
  have hb_le : chunkBits n ≤ n + 4 := by
    unfold chunkBits; have := Nat.log_le_self 2 n; omega
  have hK0 : rootK0 n ≤ 2 * n + 4 := by
    unfold rootK0
    have hN_le : numChunks n ≤ n := ceilDiv_le_self n (chunkBits n)
    have hbit : ∀ m : ℕ, bitLength m ≤ m := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · rw [bitLength_pos hm]
          have hdiv := ih (m / 2) (Nat.div_lt_self hm (by decide))
          omega
    have hc : Nat.clog 2 (2 * max 1 (numChunks n)) ≤ 2 * n + 2 := by
      rw [clog2_eq_bitLength_pred]
      have hm : 2 * max 1 (numChunks n) - 1 ≤ 2 * n + 2 := by omega
      exact (hbit _).trans hm
    omega
  simp only [length_encUnary]
  omega

/-! ## 3. Leaf Schedule Encoding & Generator (`encLeafSchedule`, `bmLeafScheduleWith`) -/

/-- Encoded leaf twiddle table of length `2 ^ K` at working bit-width `6 * qBaseEll K p`. -/
def encLeafTwiddleTable (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p)) : List Bool :=
  encList (encComplex (6 * qBaseEll K p)) ((List.finRange (2 ^ K)).map leafTwiddles)

/-- Encoded leaf schedule `(((K, p), B_in), encLeafTwiddleTable K p leafTwiddles)`. -/
def encLeafSchedule (K p B_in : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p)) : List Bool :=
  encPair (encPair (encPair encUnary encUnary) encUnary) id
    (((K, p), B_in), encLeafTwiddleTable K p leafTwiddles)

/-- Emitter inside `bmLeafScheduleWith`: transforms
`((((WOut, qBase), (piLeaf, den_s)), W), u_s)` into
`(((W, (WOut, qBase)), piLeaf), (u_s, den_s))` and invokes `bmExpTwoPiIWith bmMul`. -/
def bmLeafTwiddleEmitWith (bmMul : BitMachine) : BitMachine :=
  let bmCtx := bmSeq bmFst bmFst
  let bmW := bmSeq bmFst bmSnd
  let bmU := bmSnd
  let bmWQ := bmSeq bmCtx bmFst
  let bmPi := bmSeq (bmSeq bmCtx bmSnd) bmFst
  let bmDen := bmSeq (bmSeq bmCtx bmSnd) bmSnd
  bmSeq
    (bmFanout (bmFanout (bmFanout bmW bmWQ) bmPi) (bmFanout bmU bmDen))
    (bmExpTwoPiIWith bmMul)

/-- **LeafTwiddles Table Generator (`bmLeafTwiddleTableWith bmMul`)**:
Consumes `(K, p)` on `kIO` and emits
`encLeafTwiddleTable K p (fun u => expTwoPiIFixed (qBaseEll K p) (u.val : ℤ) (2 ^ K))`. -/
def bmLeafTwiddleTableWith (bmMul : BitMachine) : BitMachine :=
  let bmK := bmFst
  let bmQ := bmQBaseEll
  let bmW := bmSeq (bmFanout (bmUnaryConst 100) bmQ) bmUnaryMul
  let bmWOut := bmSeq (bmFanout (bmUnaryConst 6) bmQ) bmUnaryMul
  let bmSPi := bmSeq (bmFanout bmQ (bmUnaryConst 10)) bmUnaryAdd
  let bmPi := bmSeq (bmFanout bmW bmSPi) bmApproxPi
  let bmTwoPowK := bmSeq bmK bmUnaryTwoPow
  let bmDenS := bmSeq (bmFanout bmW bmTwoPowK) bmUnaryToSigned
  let bmCtx := bmFanout (bmFanout bmWOut bmQ) (bmFanout bmPi bmDenS)
  bmSeq (bmFanout (bmFanout bmCtx bmW) bmTwoPowK)
    (bmTabulateSigned (bmLeafTwiddleEmitWith bmMul))

theorem mul_le_scheduleSeriesTerms {L Q K1 K2 q M : ℕ}
    (hL : L ≤ K1 * (q + 1)) (hQ : Q ≤ K2 * ((q + 1) * (q + M))) :
    L * Q ≤ (K1 * K2) * (scheduleSeriesTerms q * (q + M)) := by
  unfold scheduleSeriesTerms
  have h1 : L * Q ≤ (K1 * (q + 1)) * (K2 * ((q + 1) * (q + M))) := Nat.mul_le_mul hL hQ
  have h2 : (K1 * (q + 1)) * (K2 * ((q + 1) * (q + M))) =
      (K1 * K2) * ((q + 1) * (q + 1) * (q + M)) := by ring
  have h3 : (q + 1) * (q + 1) * (q + M) ≤ 120 * (q + 1) * (q + 1) * (q + M) := by
    have : 1 * ((q + 1) * (q + 1) * (q + M)) ≤ 120 * ((q + 1) * (q + 1) * (q + M)) :=
      Nat.mul_le_mul_right _ (by decide)
    linarith [show 120 * ((q + 1) * (q + 1) * (q + M)) = 120 * (q + 1) * (q + 1) * (q + M) by ring]
  exact le_trans (h2 ▸ h1) (Nat.mul_le_mul_left (K1 * K2) h3)

theorem quad_le_scheduleSeriesTerms {Q K2 q M : ℕ}
    (hQ : Q ≤ K2 * ((q + 1) * (q + M))) :
    Q ≤ K2 * (scheduleSeriesTerms q * (q + M)) := by
  have h := mul_le_scheduleSeriesTerms (L := 1) (K1 := 1) (by omega) hQ
  simpa using h

theorem linear_le_scheduleSeriesTerms (q M : ℕ) (hq : 1 ≤ q + M) :
    120 * (q + 1) ≤ scheduleSeriesTerms q * (q + M) := by
  unfold scheduleSeriesTerms
  have h1 : 1 ≤ (q + 1) * (q + M) := Nat.mul_pos (by omega) hq
  have h2 := Nat.mul_le_mul_left (120 * (q + 1)) h1
  linarith [show 120 * (q + 1) * 1 = 120 * (q + 1) by ring,
            show 120 * (q + 1) * ((q + 1) * (q + M)) =
              120 * (q + 1) * (q + 1) * (q + M) by ring]

theorem cube_le_scheduleSeriesTerms (q M : ℕ) :
    120 * (q * q * q) ≤ scheduleSeriesTerms q * (q + M) := by
  unfold scheduleSeriesTerms
  have h1 : q * q ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (q * q) * q ≤ ((q + 1) * (q + 1)) * (q + M) := Nat.mul_le_mul h1 (by omega)
  have h3 := Nat.mul_le_mul_left 120 h2
  linarith [show 120 * ((q * q) * q) = 120 * (q * q * q) by ring,
            show 120 * (((q + 1) * (q + 1)) * (q + M)) =
              120 * (q + 1) * (q + 1) * (q + M) by ring]

theorem qChildEll_le_twelve_mul_rEll_of_internal {K p : ℕ}
    (hleaf : (!isBaseLeaf K p) = true) (hK2 : 2 ≤ K) :
    qChildEll K p ≤ 12 * rEll K := by
  have hlt : 4 * p * p < 2 ^ K := by
    unfold isBaseLeaf at hleaf
    rw [Bool.not_eq_true', decide_eq_false_iff_not, not_le] at hleaf
    exact hleaf
  have ht1_le_r : t1Ell K ≤ rEll K := by
    unfold t1Ell rEll k1Ell k2Ell
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have ht1r : t1Ell K * rEll K = 2 ^ K := t1Ell_mul_rEll K
  have h2p_lt_r : 2 * p < rEll K := by
    have hsq : (2 * p) * (2 * p) < rEll K * rEll K := by
      calc (2 * p) * (2 * p) = 4 * p * p := by ring
        _ < 2 ^ K := hlt
        _ = t1Ell K * rEll K := ht1r.symm
        _ ≤ rEll K * rEll K := Nat.mul_le_mul_right (rEll K) ht1_le_r
    nlinarith
  have hk2_ge1 : 1 ≤ k2Ell K := by unfold k2Ell; omega
  have hr_ge2 : 2 ≤ rEll K := by
    unfold rEll
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k2Ell K := Nat.pow_le_pow_right (by norm_num) hk2_ge1
  have hk2_le_r : k2Ell K ≤ rEll K := le_of_lt Nat.lt_two_pow_self
  have hK_le_2r : K ≤ 2 * rEll K := by
    have h1 : K ≤ 2 * k2Ell K := by unfold k2Ell; omega
    omega
  have hq := qChildEll_eq K p
  omega

set_option maxHeartbeats 800000 in
theorem bmLeafTwiddleTableWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let qBase := qBaseEll K p
    let S_leaf := scheduleSeriesTerms qBase * (qBase + scaledSubMulCost mulTime qBase)
    ∃ t ≤ 3000000000 * ((2 ^ K) * S_leaf),
      (bmLeafTwiddleTableWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (K, p)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encLeafTwiddleTable K p (fun u => expTwoPiIFixed qBase (u.val : ℤ) (2 ^ K))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro qBase S_leaf
  let St := Unit
  let W : ℕ := 100 * qBase
  let WOut : ℕ := 6 * qBase
  let S_pi : ℕ := qBase + 10
  let piLeaf : ℤ := approxPiFixed S_pi
  have hqBase_eq : qBase = p + K + 4 := rfl
  have hqBase4 : 4 ≤ qBase := by omega
  have hW_pos : 1 ≤ W := by dsimp [W]; omega
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have h2K_le_q : 2 ^ K ≤ 2 ^ qBase := Nat.pow_le_pow_right (by decide) (by omega)
  have h2K_lt_W : 2 ^ K < 2 ^ W := Nat.pow_lt_pow_right (by decide) (by dsimp [W]; omega)
  have hpi_W : 5 * S_pi + 30 ≤ W := by dsimp [S_pi, W]; omega
  let uK : St → List Bool := fun _ => encUnary K
  let uP : St → List Bool := fun _ => encUnary p
  let uIn : St → List Bool := encDepPair uK uP
  have pK := StageEval.fst uK uP
  have pQ := StageEval.of_computesStageLe bmQBaseEll_computesStageLe (fun _ : St => (K, p))
  have pW := StageEval.seq (StageEval.fanout (StageEval.unaryConst 100 uIn) pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (100, qBase)))
  have pWOut := StageEval.seq (StageEval.fanout (StageEval.unaryConst 6 uIn) pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (6, qBase)))
  have pSPi := StageEval.seq (StageEval.fanout pQ (StageEval.unaryConst 10 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (qBase, 10)))
  have pPi := StageEval.seq (StageEval.fanout pW pSPi)
    (StageEval.const (S := St) (bmApproxPi_computesInTime W S_pi hpi_W))
  have pTwoPowK := StageEval.seq pK
    (StageEval.of_computesStageLe bmUnaryTwoPow_computesStageLe (fun _ : St => K))
  have pDenS := StageEval.seq (StageEval.fanout pW pTwoPowK)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W (2 ^ K) hW_pos h2K_lt_W))
  let uWQ : St → List Bool := encDepPair (fun _ => encUnary WOut) (fun _ => encUnary qBase)
  let uPiDen : St → List Bool :=
    encDepPair (fun _ => encodeSignedWord W piLeaf) (fun _ => encodeSignedWord W ((2 ^ K : ℕ) : ℤ))
  let uCtx : St → List Bool := encDepPair uWQ uPiDen
  have pCtx := StageEval.fanout (StageEval.fanout pWOut pQ) (StageEval.fanout pPi pDenS)
  have pSetup := StageEval.fanout (StageEval.fanout pCtx pW) pTwoPowK
  have hlen_ctx : (uCtx ()).length ≤ 10 * W + 30 := by
    dsimp only [uCtx, uWQ, uPiDen, WOut, W]
    simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]; omega
  let B_emit : ℕ :=
    (qBase + 58) * (4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000) +
    4 * mulTime W + 30000 * W * W + 2050000 * W + 2100000
  have pTab := StageEval.tabulateSigned (S := St) (emitM := bmLeafTwiddleEmitWith bmMul)
    (uCtx := uCtx) (W := fun _ => W) (N := fun _ => 2 ^ K)
    (encElem := fun _ => encComplex WOut)
    (fn := fun _ u => expTwoPiIFixed qBase (u : ℤ) (2 ^ K))
    (B := fun _ => B_emit)
    (L_ctx := fun _ => 10 * W + 30)
    (L_elem := fun _ => 4 * W + 6)
    (fun _ => hW_pos)
    (fun _ => h2K_lt_W)
    (fun u => by
      let SubS := { _s : St // u < 2 ^ K }
      by_cases hu : u < 2 ^ K
      · let uCW : SubS → List Bool := encDepPair (fun _ => uCtx ()) (fun _ => encUnary W)
        let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (u : ℤ)
        have pF1 := StageEval.fst uCW uIdx
        have pU := StageEval.snd uCW uIdx
        have pC := StageEval.seq pF1 (StageEval.fst (fun _ : SubS => uCtx ()) (fun _ => encUnary W))
        have pW' := StageEval.seq pF1 (StageEval.snd (fun _ : SubS => uCtx ()) (fun _ => encUnary W))
        have pWQ' := StageEval.seq pC (StageEval.fst (fun _ : SubS => uWQ ()) (fun _ => uPiDen ()))
        have pPD := StageEval.seq pC (StageEval.snd (fun _ : SubS => uWQ ()) (fun _ => uPiDen ()))
        have pPi' := StageEval.seq pPD
          (StageEval.fst (fun _ : SubS => encodeSignedWord W piLeaf)
            (fun _ => encodeSignedWord W ((2 ^ K : ℕ) : ℤ)))
        have pDen' := StageEval.seq pPD
          (StageEval.snd (fun _ : SubS => encodeSignedWord W piLeaf)
            (fun _ => encodeSignedWord W ((2 ^ K : ℕ) : ℤ)))
        have pRearr := StageEval.fanout
          (StageEval.fanout (StageEval.fanout pW' pWQ') pPi')
          (StageEval.fanout pU pDen')
        have hu_lo : -((2 ^ K : ℕ) : ℤ) ≤ (u : ℤ) := by omega
        have hu_hi : (u : ℤ) < ((2 ^ K : ℕ) : ℤ) := by exact_mod_cast hu
        have pExp := StageEval.const (S := SubS)
          (bmExpTwoPiIWith_computesInTime hmul W WOut qBase (2 ^ K) (u : ℤ)
            hqBase4 (le_refl W) (by dsimp [WOut]; omega) (by dsimp [WOut, W]; omega)
            h2K_pos h2K_le_q hu_lo hu_hi)
        refine (StageEval.seq pRearr pExp).mono (fun _ => ?_)
        dsimp only [uCW, uIdx, uCtx, uWQ, uPiDen, B_emit, WOut, W]
        simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
        omega
      · intro s'; exact False.elim (hu s'.property))
    (fun _ => hlen_ctx)
    (fun _ _ _ => by simp [encComplex, encPair, length_encodeSignedWord]; dsimp [WOut, W]; omega)
  have hall := StageEval.seq pSetup pTab
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uK, uP, uCtx, uWQ, uPiDen, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encodeSignedWord] at ht
  have hmW : mulTime W ≤ scaledSubMulCost mulTime qBase := le_scaledSubMulCost_hundred mulTime qBase
  have hB1 :
      (qBase + 58) * (4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000) ≤
      (15 * 120000000) * S_leaf :=
    mul_le_scheduleSeriesTerms (by omega) (by dsimp only [W]; nlinarith)
  have hB2 :
      4 * mulTime W + 30000 * W * W + 2050000 * W + 2100000 +
      1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500 + 50 ≤
      400000000 * S_leaf :=
    quad_le_scheduleSeriesTerms (by dsimp only [W]; nlinarith)
  have hB_le :
      B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500 + 50 ≤
      2200000000 * S_leaf := by
    dsimp only [B_emit]; omega
  have h2K_mul :
      2 ^ K * (B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500) + 50 * 2 ^ K ≤
      2200000000 * (2 ^ K * S_leaf) := by
    have hm := Nat.mul_le_mul_left (2 ^ K) hB_le
    linarith [show 2 ^ K * (2200000000 * S_leaf) = 2200000000 * (2 ^ K * S_leaf) by ring,
              show 2 ^ K * (B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500 + 50) =
                2 ^ K * (B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500) + 50 * 2 ^ K by ring]
  have hK_le : K ≤ qBase := by omega
  have hS_2K : S_leaf ≤ 2 ^ K * S_leaf := Nat.le_mul_of_pos_left _ h2K_pos
  have hS_lin0 := linear_le_scheduleSeriesTerms qBase (scaledSubMulCost mulTime qBase) (by omega)
  have hS_lin : qBase + 1 ≤ S_leaf := by dsimp only [S_leaf]; omega
  have h2K_W : 2 ^ K * (800 * W + 2010) + 10 * K * 2 ^ K + 300 * 2 ^ K ≤ 1000000 * (2 ^ K * S_leaf) := by
    have h1 : 800 * W + 2010 + 10 * K + 300 ≤ 1000000 * S_leaf := by
      dsimp only [W]; omega
    have hm := Nat.mul_le_mul_left (2 ^ K) h1
    linarith [show 2 ^ K * (1000000 * S_leaf) = 1000000 * (2 ^ K * S_leaf) by ring,
              show 2 ^ K * (800 * W + 2010 + 10 * K + 300) =
                2 ^ K * (800 * W + 2010) + 10 * K * 2 ^ K + 300 * 2 ^ K by ring]
  have hpi1 :
      (S_pi + 4) * (1000 * W * W + 320000 * W + 800000) ≤ (5 * 20000000) * S_leaf :=
    mul_le_scheduleSeriesTerms (by dsimp only [S_pi]; omega) (by dsimp only [W]; nlinarith)
  have hpi2 :
      600 * W * W + 300000 * W + 900000 + 500000 * qBase + 5000000 ≤ 50000000 * S_leaf :=
    quad_le_scheduleSeriesTerms (by dsimp only [W]; nlinarith)
  have hpi_le :
      (S_pi + 4) * (1000 * W * W + 320000 * W + 800000) + 600 * W * W + 300000 * W + 900000 +
      500000 * qBase + 5000000 ≤ 150000000 * S_leaf := by omega
  have hW_def : W = 100 * qBase := rfl
  have hWOut_def : WOut = 6 * qBase := rfl
  have hSpi_def : S_pi = qBase + 10 := rfl
  have hq_def : qBaseEll K p = qBase := rfl
  rw [hq_def] at ht
  exact ⟨t, by omega, hcomp⟩

theorem length_encLeafTwiddleTable_le (K p : ℕ)
    (tbl : Fin (2 ^ K) → FixedComplex (qBaseEll K p)) :
    (encLeafTwiddleTable K p tbl).length ≤ 2 ^ K * (48 * qBaseEll K p + 18) := by
  unfold encLeafTwiddleTable
  have h := StageEval.length_encList_le_of_forall_le (encComplex (6 * qBaseEll K p))
    (24 * qBaseEll K p + 8) ((List.finRange (2 ^ K)).map tbl)
    (fun z _ => by simp only [length_encComplex]; omega)
  rw [List.length_map, List.length_finRange] at h
  exact le_trans h (Nat.mul_le_mul_left _ (by omega))

/-- **Leaf Schedule Stage (`bmLeafScheduleWith bmMul`)**:
Consumes `((K, p), B_in)` on `kIO` and emits
`encLeafSchedule K p B_in (memoizeFin (fun u => expTwoPiIFixedWithMul (· * ·) (qBaseEll K p) (u.val : ℤ) (2 ^ K)))`. -/
def bmLeafScheduleWith (bmMul : BitMachine) : BitMachine :=
  bmFanout bmId (bmSeq bmFst (bmLeafTwiddleTableWith bmMul))

theorem bmLeafScheduleWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p B_in : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let qBase := qBaseEll K p
    let S_leaf := scheduleSeriesTerms qBase * (qBase + scaledSubMulCost mulTime qBase)
    ∃ t ≤ 3100000000 * ((2 ^ K) * S_leaf) + 20 * B_in,
      (bmLeafScheduleWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encLeafSchedule K p B_in
            (memoizeFin (fun u => expTwoPiIFixedWithMul (· * ·) qBase (u.val : ℤ) (2 ^ K)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro qBase S_leaf
  let St := Unit
  let uKP : St → List Bool := fun _ => encPair encUnary encUnary (K, p)
  let uB : St → List Bool := fun _ => encUnary B_in
  let uIn : St → List Bool := encDepPair uKP uB
  have pTbl := StageEval.seq (StageEval.fst uKP uB)
    (StageEval.const (S := St) (bmLeafTwiddleTableWith_computesInTime hmul K p))
  have hall := StageEval.congr_out
    (v2 := fun _ => encLeafSchedule K p B_in
      (memoizeFin (fun u => expTwoPiIFixedWithMul (· * ·) qBase (u.val : ℤ) (2 ^ K))))
    (StageEval.fanout (StageEval.id_stage uIn) pTbl)
    (fun _ => by
      dsimp only [encLeafSchedule, uIn, uKP, uB, encDepPair]
      rw [memoizeFin_eq]
      rfl)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uKP, uB, id] at ht hcomp
  have htbl_len :
      (encLeafTwiddleTable K p (fun u => expTwoPiIFixed (qBaseEll K p) (u.val : ℤ) (2 ^ K))).length ≤
      2 ^ K * (48 * qBase + 18) :=
    length_encLeafTwiddleTable_le K p _
  have hqBase_eq : qBase = p + K + 4 := rfl
  have hS1_0 := linear_le_scheduleSeriesTerms qBase (scaledSubMulCost mulTime qBase) (by omega)
  have hS1 : 48 * qBase + 18 ≤ S_leaf := by dsimp only [S_leaf]; omega
  have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hS_2K : S_leaf ≤ 2 ^ K * S_leaf := Nat.le_mul_of_pos_left _ h2K_pos
  have htbl_S : 2 ^ K * (48 * qBase + 18) ≤ 2 ^ K * S_leaf :=
    Nat.mul_le_mul_left (2 ^ K) hS1
  have hS_def :
      scheduleSeriesTerms (qBaseEll K p) * (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p)) =
      S_leaf := rfl
  rw [hS_def] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary] at ht
  exact ⟨t, by omega, hcomp⟩

/-! ## 4. Internal Node Schedule Encoding & Generators (`encNodeSchedule`, `bmNodeTwistTablesWith`, `bmNodeTapTableWith`, `bmNodeGHatTablesWith`, `bmNodeScheduleWith`) -/

/-- Encoded 2D filter tap table of shape `t1Ell K × (2 * m1 + 1)` at width `qChildEll K p + 2`. -/
def encTapTable (K p m1 : ℕ) (filterTap : Fin (t1Ell K) → ℤ → ℤ) : List Bool :=
  encList (encList (encodeSignedWord (qChildEll K p + 2)))
    ((List.finRange (t1Ell K)).map (fun j1 =>
      (List.finRange (2 * m1 + 1)).map (fun k => filterTap j1 ((k.val : ℤ) - (m1 : ℤ)))))

/-- Encoded pre/post-twist root table of length `rEll K` at working width `10 * qChildEll K p`. -/
def encTwistTable (K p : ℕ) (tbl : Fin (rEll K) → FixedComplex (qChildEll K p)) : List Bool :=
  encList (encComplex (10 * qChildEll K p)) ((List.finRange (rEll K)).map tbl)

/-- Encoded passband weight mantissa table (`c0` or `c1`) of length `rEll K` at working width `10 * qChildEll K p`. -/
def encMantissaTable (K p : ℕ) (tbl : Fin (rEll K) → ℤ) : List Bool :=
  encList (encodeSignedWord (10 * qChildEll K p)) ((List.finRange (rEll K)).map tbl)

/-- Complete encoded internal node schedule at level `(K, p, B_in)`. -/
def encNodeSchedule (K p B_in m1 : ℕ)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ) : List Bool :=
  encPair
    (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
    (encPair (encPair id (encPair id id)) (encPair id id))
    (((K, p), (B_in, m1)),
      ((encTapTable K p m1 filterTap,
        (encTwistTable K p preTwistRoot, encTwistTable K p postTwistRoot)),
        (encMantissaTable K p c0Mantissa, encMantissaTable K p c1Mantissa)))

/-! ### 4.1 Pre/Post-Twist Root Tables (`bmNodeTwistTablesWith`) -/

/-- Emitter for `preTwistRoot`: transforms `((((WOut, q), (piRoot, twoR_s)), W), k2_s)` into
`(((W, (WOut, q)), piRoot), (k2_s, twoR_s))` and calls `bmExpTwoPiIWith bmMul`. -/
def bmPreTwistEmitWith (bmMul : BitMachine) : BitMachine :=
  bmLeafTwiddleEmitWith bmMul

/-- Emitter for `postTwistRoot`: negates `k2_s` via `bmSignedNeg` and calls `bmPreTwistEmitWith bmMul`. -/
def bmPostTwistEmitWith (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmMapSnd bmSignedNeg) (bmPreTwistEmitWith bmMul)

/-- **Pre/Post-Twist Tables Generator (`bmNodeTwistTablesWith bmMul`)**:
Consumes `(K, p)` on `kIO` and emits `(encTwistTable K p preTwistRoot, encTwistTable K p postTwistRoot)`. -/
def bmNodeTwistTablesWith (bmMul : BitMachine) : BitMachine :=
  let bmK := bmFst
  let bmQ := bmQChildEll
  let bmW := bmSeq (bmFanout (bmUnaryConst 1000) bmQ) bmUnaryMul
  let bmWOut := bmSeq (bmFanout (bmUnaryConst 10) bmQ) bmUnaryMul
  let bmSPi := bmSeq (bmFanout bmQ (bmUnaryConst 10)) bmUnaryAdd
  let bmPi := bmSeq (bmFanout bmW bmSPi) bmApproxPi
  let bmR := bmSeq bmK bmREll
  let bmTwoR := bmSeq bmR bmUnaryDouble
  let bmDenS := bmSeq (bmFanout bmW bmTwoR) bmUnaryToSigned
  let bmCtx := bmFanout (bmFanout bmWOut bmQ) (bmFanout bmPi bmDenS)
  let bmTabIn := bmFanout (bmFanout bmCtx bmW) bmR
  bmSeq bmTabIn
    (bmFanout
      (bmTabulateSigned (bmPreTwistEmitWith bmMul))
      (bmTabulateSigned (bmPostTwistEmitWith bmMul)))

theorem length_encTwistTable_le (K p : ℕ)
    (tbl : Fin (rEll K) → FixedComplex (qChildEll K p)) :
    (encTwistTable K p tbl).length ≤ rEll K * (80 * qChildEll K p + 18) := by
  unfold encTwistTable
  have h := StageEval.length_encList_le_of_forall_le (encComplex (10 * qChildEll K p))
    (40 * qChildEll K p + 8) ((List.finRange (rEll K)).map tbl)
    (fun z _ => by simp only [length_encComplex]; omega)
  rw [List.length_map, List.length_finRange] at h
  exact le_trans h (Nat.mul_le_mul_left _ (by omega))

set_option maxHeartbeats 800000 in
theorem bmNodeTwistTablesWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let r := rEll K
    let S_term := scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q)
    ∃ t ≤ 260000000000 * (r * S_term),
      (bmNodeTwistTablesWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (K, p)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair id id
            (encTwistTable K p (fun k2 => expTwoPiIFixed q (k2.val : ℤ) (2 * r)),
             encTwistTable K p (fun k2 => expTwoPiIFixed q (-(k2.val : ℤ)) (2 * r)))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro q r S_term
  let St := Unit
  let W : ℕ := 1000 * q
  let WOut : ℕ := 10 * q
  let S_pi : ℕ := q + 10
  let piRoot : ℤ := approxPiFixed S_pi
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hq14 : 14 ≤ q := by omega
  have hq4 : 4 ≤ q := by omega
  have hW_pos : 1 ≤ W := by dsimp [W]; omega
  have hr_pos : 1 ≤ r := rEll_pos K
  have hr_le_2K : r ≤ 2 ^ K := rEll_le_two_pow K
  have h2r_pos : 0 < 2 * r := by omega
  have h2r_le_q : 2 * r ≤ 2 ^ q := by
    calc 2 * r ≤ 2 * 2 ^ K := Nat.mul_le_mul_left 2 hr_le_2K
      _ = 2 ^ (K + 1) := (Nat.pow_succ' ).symm
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by omega)
  have h2r_lt_W : 2 * r < 2 ^ W :=
    lt_of_le_of_lt h2r_le_q (Nat.pow_lt_pow_right (by decide) (by dsimp [W]; omega))
  have hr_lt_W : r < 2 ^ W := lt_of_le_of_lt (by omega : r ≤ 2 * r) h2r_lt_W
  have hpi_W : 5 * S_pi + 30 ≤ W := by dsimp [S_pi, W]; omega
  let uK : St → List Bool := fun _ => encUnary K
  let uP : St → List Bool := fun _ => encUnary p
  let uIn : St → List Bool := encDepPair uK uP
  have pK := StageEval.fst uK uP
  have pQ := StageEval.of_computesStageLe bmQChildEll_computesStageLe (fun _ : St => (K, p))
  have pW := StageEval.seq (StageEval.fanout (StageEval.unaryConst 1000 uIn) pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (1000, q)))
  have pWOut := StageEval.seq (StageEval.fanout (StageEval.unaryConst 10 uIn) pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (10, q)))
  have pSPi := StageEval.seq (StageEval.fanout pQ (StageEval.unaryConst 10 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (q, 10)))
  have pPi := StageEval.seq (StageEval.fanout pW pSPi)
    (StageEval.const (S := St) (bmApproxPi_computesInTime W S_pi hpi_W))
  have pR := StageEval.seq pK
    (StageEval.of_computesStageLe bmREll_computesStageLe (fun _ : St => K))
  have pTwoR := StageEval.seq pR
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => r))
  have pDenS := StageEval.seq (StageEval.fanout pW pTwoR)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W (2 * r) hW_pos h2r_lt_W))
  let uWQ : St → List Bool := encDepPair (fun _ => encUnary WOut) (fun _ => encUnary q)
  let uPiDen : St → List Bool :=
    encDepPair (fun _ => encodeSignedWord W piRoot) (fun _ => encodeSignedWord W ((2 * r : ℕ) : ℤ))
  let uCtx : St → List Bool := encDepPair uWQ uPiDen
  have pCtx := StageEval.fanout (StageEval.fanout pWOut pQ) (StageEval.fanout pPi pDenS)
  have pTabIn := StageEval.fanout (StageEval.fanout pCtx pW) pR
  have hlen_ctx : (uCtx ()).length ≤ 10 * W + 30 := by
    dsimp only [uCtx, uWQ, uPiDen, WOut, W]
    simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]; omega
  let B_emit : ℕ :=
    (q + 58) * (4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000) +
    4 * mulTime W + 30000 * W * W + 2100000 * W + 2200000
  have hemitPre : ∀ (k2 : ℕ),
      StageEval (S := { _s : St // k2 < r }) (bmPreTwistEmitWith bmMul)
        (encDepPair (encDepPair (fun _ => uCtx ()) (fun _ => encUnary W))
          (fun _ => encodeSignedWord W (k2 : ℤ)))
        (fun _ => encComplex WOut (expTwoPiIFixed q (k2 : ℤ) (2 * r)))
        (fun _ => B_emit) := fun k2 => by
    let SubS := { _s : St // k2 < r }
    by_cases hk2 : k2 < r
    · let uCW : SubS → List Bool := encDepPair (fun _ => uCtx ()) (fun _ => encUnary W)
      let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (k2 : ℤ)
      have pF1 := StageEval.fst uCW uIdx
      have pU := StageEval.snd uCW uIdx
      have pC := StageEval.seq pF1 (StageEval.fst (fun _ : SubS => uCtx ()) (fun _ => encUnary W))
      have pW' := StageEval.seq pF1 (StageEval.snd (fun _ : SubS => uCtx ()) (fun _ => encUnary W))
      have pWQ' := StageEval.seq pC (StageEval.fst (fun _ : SubS => uWQ ()) (fun _ => uPiDen ()))
      have pPD := StageEval.seq pC (StageEval.snd (fun _ : SubS => uWQ ()) (fun _ => uPiDen ()))
      have pPi' := StageEval.seq pPD
        (StageEval.fst (fun _ : SubS => encodeSignedWord W piRoot)
          (fun _ => encodeSignedWord W ((2 * r : ℕ) : ℤ)))
      have pDen' := StageEval.seq pPD
        (StageEval.snd (fun _ : SubS => encodeSignedWord W piRoot)
          (fun _ => encodeSignedWord W ((2 * r : ℕ) : ℤ)))
      have pRearr := StageEval.fanout
        (StageEval.fanout (StageEval.fanout pW' pWQ') pPi')
        (StageEval.fanout pU pDen')
      have hk_lo : -((2 * r : ℕ) : ℤ) ≤ (k2 : ℤ) := by omega
      have hk_hi : (k2 : ℤ) < ((2 * r : ℕ) : ℤ) := by exact_mod_cast (by omega : k2 < 2 * r)
      have pExp := StageEval.const (S := SubS)
        (bmExpTwoPiIWith_computesInTime hmul W WOut q (2 * r) (k2 : ℤ)
          hq4 (by dsimp [W]; omega) (by dsimp [WOut]; omega) (by dsimp [WOut, W]; omega)
          h2r_pos h2r_le_q hk_lo hk_hi)
      refine (StageEval.seq pRearr pExp).mono (fun _ => ?_)
      dsimp only [uCW, uIdx, uCtx, uWQ, uPiDen, B_emit, WOut, W]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega
    · intro s'; exact False.elim (hk2 s'.property)
  have hemitPost : ∀ (k2 : ℕ),
      StageEval (S := { _s : St // k2 < r }) (bmPostTwistEmitWith bmMul)
        (encDepPair (encDepPair (fun _ => uCtx ()) (fun _ => encUnary W))
          (fun _ => encodeSignedWord W (k2 : ℤ)))
        (fun _ => encComplex WOut (expTwoPiIFixed q (-(k2 : ℤ)) (2 * r)))
        (fun _ => B_emit) := fun k2 => by
    let SubS := { _s : St // k2 < r }
    by_cases hk2 : k2 < r
    · let uCW : SubS → List Bool := encDepPair (fun _ => uCtx ()) (fun _ => encUnary W)
      let uIdx : SubS → List Bool := fun _ => encodeSignedWord W (k2 : ℤ)
      let uNegIdx : SubS → List Bool := fun _ => encodeSignedWord W (-(k2 : ℤ))
      have hk2_fits : FitsSignedWord W (k2 : ℤ) := by
        rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
      have pNeg := StageEval.mapSnd (u1 := uCW)
        (StageEval.const (S := SubS) (bmSignedNeg_computesInTime W (k2 : ℤ) hk2_fits))
      have pF1 := StageEval.fst uCW uNegIdx
      have pU := StageEval.snd uCW uNegIdx
      have pC := StageEval.seq pF1 (StageEval.fst (fun _ : SubS => uCtx ()) (fun _ => encUnary W))
      have pW' := StageEval.seq pF1 (StageEval.snd (fun _ : SubS => uCtx ()) (fun _ => encUnary W))
      have pWQ' := StageEval.seq pC (StageEval.fst (fun _ : SubS => uWQ ()) (fun _ => uPiDen ()))
      have pPD := StageEval.seq pC (StageEval.snd (fun _ : SubS => uWQ ()) (fun _ => uPiDen ()))
      have pPi' := StageEval.seq pPD
        (StageEval.fst (fun _ : SubS => encodeSignedWord W piRoot)
          (fun _ => encodeSignedWord W ((2 * r : ℕ) : ℤ)))
      have pDen' := StageEval.seq pPD
        (StageEval.snd (fun _ : SubS => encodeSignedWord W piRoot)
          (fun _ => encodeSignedWord W ((2 * r : ℕ) : ℤ)))
      have pRearr := StageEval.fanout
        (StageEval.fanout (StageEval.fanout pW' pWQ') pPi')
        (StageEval.fanout pU pDen')
      have hk_lo : -((2 * r : ℕ) : ℤ) ≤ -(k2 : ℤ) := by
        have : (k2 : ℤ) ≤ ((2 * r : ℕ) : ℤ) := by exact_mod_cast (by omega : k2 ≤ 2 * r)
        omega
      have hk_hi : -(k2 : ℤ) < ((2 * r : ℕ) : ℤ) := by
        have : (0 : ℤ) < ((2 * r : ℕ) : ℤ) := by exact_mod_cast h2r_pos
        omega
      have pExp := StageEval.const (S := SubS)
        (bmExpTwoPiIWith_computesInTime hmul W WOut q (2 * r) (-(k2 : ℤ))
          hq4 (by dsimp [W]; omega) (by dsimp [WOut]; omega) (by dsimp [WOut, W]; omega)
          h2r_pos h2r_le_q hk_lo hk_hi)
      refine (StageEval.seq pNeg (StageEval.seq pRearr pExp)).mono (fun _ => ?_)
      dsimp only [uCW, uIdx, uNegIdx, uCtx, uWQ, uPiDen, B_emit, WOut, W]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega
    · intro s'; exact False.elim (hk2 s'.property)
  have pPre := StageEval.tabulateSigned (S := St) (emitM := bmPreTwistEmitWith bmMul)
    (uCtx := uCtx) (W := fun _ => W) (N := fun _ => r)
    (encElem := fun _ => encComplex WOut)
    (fn := fun _ k2 => expTwoPiIFixed q (k2 : ℤ) (2 * r))
    (B := fun _ => B_emit)
    (L_ctx := fun _ => 10 * W + 30)
    (L_elem := fun _ => 4 * W + 6)
    (fun _ => hW_pos) (fun _ => hr_lt_W) hemitPre (fun _ => hlen_ctx)
    (fun _ _ _ => by simp [encComplex, encPair, length_encodeSignedWord]; dsimp [WOut, W]; omega)
  have pPost := StageEval.tabulateSigned (S := St) (emitM := bmPostTwistEmitWith bmMul)
    (uCtx := uCtx) (W := fun _ => W) (N := fun _ => r)
    (encElem := fun _ => encComplex WOut)
    (fn := fun _ k2 => expTwoPiIFixed q (-(k2 : ℤ)) (2 * r))
    (B := fun _ => B_emit)
    (L_ctx := fun _ => 10 * W + 30)
    (L_elem := fun _ => 4 * W + 6)
    (fun _ => hW_pos) (fun _ => hr_lt_W) hemitPost (fun _ => hlen_ctx)
    (fun _ _ _ => by simp [encComplex, encPair, length_encodeSignedWord]; dsimp [WOut, W]; omega)
  have hall := StageEval.seq pTabIn (StageEval.fanout pPre pPost)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uK, uP, uCtx, uWQ, uPiDen, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encodeSignedWord] at ht
  have hmW : mulTime W ≤ scaledSubMulCost mulTime q := le_scaledSubMulCost_thousand mulTime q
  have hpre_len :
      (encList (encComplex WOut)
        (List.map (fun i => expTwoPiIFixed q (i.val : ℤ) (2 * r)) (List.finRange r))).length ≤
      r * (80 * q + 18) :=
    length_encTwistTable_le K p _
  have hpost_len :
      (encList (encComplex WOut)
        (List.map (fun i => expTwoPiIFixed q (-(i.val : ℤ)) (2 * r)) (List.finRange r))).length ≤
      r * (80 * q + 18) :=
    length_encTwistTable_le K p _
  have hB1 :
      (q + 58) * (4 * mulTime W + 11000 * W * W + 1000000 * W + 1200000) ≤
      (6 * 12000000000) * S_term :=
    mul_le_scheduleSeriesTerms (by omega) (by dsimp only [W]; nlinarith)
  have hB2 :
      4 * mulTime W + 30000 * W * W + 2100000 * W + 2200000 +
      1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500 + 200 ≤
      32000000000 * S_term :=
    quad_le_scheduleSeriesTerms (by dsimp only [W]; nlinarith)
  have hB_le :
      B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500 + 200 ≤
      104000000000 * S_term := by
    dsimp only [B_emit]; omega
  have hr_mul :
      2 * (r * (B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500)) + 200 * r ≤
      208000000000 * (r * S_term) := by
    have hm := Nat.mul_le_mul_left r hB_le
    linarith [show r * (104000000000 * S_term) = 104000000000 * (r * S_term) by ring,
              show r * (B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500 + 200) =
                r * (B_emit + 1000 * W + 100 * (10 * W + 30) + 50 * (4 * W + 6) + 2500) + 200 * r by ring]
  have hK_le : K ≤ q := by omega
  have hS_r : S_term ≤ r * S_term := Nat.le_mul_of_pos_left _ hr_pos
  have hS_lin0 := linear_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q) (by omega)
  have hS_lin : 80 * q + 18 ≤ S_term := by dsimp only [S_term]; omega
  have hr_W : 2 * r * (800 * W + 2010) + 10 * (K + 1) * r + 500 * r ≤ 20000000 * (r * S_term) := by
    have h1 : 1600 * W + 4020 + 10 * (K + 1) + 500 ≤ 20000000 * S_term := by
      dsimp only [W]; omega
    have hm := Nat.mul_le_mul_left r h1
    linarith [show r * (20000000 * S_term) = 20000000 * (r * S_term) by ring,
              show r * (1600 * W + 4020 + 10 * (K + 1) + 500) =
                2 * r * (800 * W + 2010) + 10 * (K + 1) * r + 500 * r by ring]
  have hpi1 :
      (S_pi + 4) * (1000 * W * W + 320000 * W + 800000) ≤ (2 * 1100000000) * S_term :=
    mul_le_scheduleSeriesTerms (by dsimp only [S_pi]; omega) (by dsimp only [W]; nlinarith)
  have hpi2 :
      600 * W * W + 300000 * W + 900000 + 50000000 * q + 50000000 ≤ 700000000 * S_term :=
    quad_le_scheduleSeriesTerms (by dsimp only [W]; nlinarith)
  have hpi_le :
      (S_pi + 4) * (1000 * W * W + 320000 * W + 800000) + 600 * W * W + 300000 * W + 900000 +
      50000000 * q + 50000000 ≤ 2900000000 * S_term := by omega
  have hr_q : r * (80 * q + 18) ≤ r * S_term :=
    Nat.mul_le_mul_left r hS_lin
  have hW_def : W = 1000 * q := rfl
  have hWOut_def : WOut = 10 * q := rfl
  have hSpi_def : S_pi = q + 10 := rfl
  have hq_def : qChildEll K p = q := rfl
  have hr_def : rEll K = r := rfl
  rw [hq_def, hr_def] at ht
  exact ⟨t, by omega, hcomp⟩

/-! ### 4.2 2D Sinc-Gaussian Filter Tap Table (`bmNodeTapTableWith`) -/

/-- Encoding of the precomputed unary parameter bundle for `bmNodeTapTableWith`:
`(((W, W_out), (N_s, N_e)), ((q, (q_l2, q_tot)), ((S, (q_pi, two_q_pi)), ((t1, winLen), (m1, fourPW)))))`. -/
def encTapUnaryBundle (W W_out N_s N_e q q_l2 q_tot S q_pi two_q_pi t1 winLen m1 fourPW : ℕ) :
    List Bool :=
  encPair
    (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
    (encPair
      (encPair encUnary (encPair encUnary encUnary))
      (encPair
        (encPair encUnary (encPair encUnary encUnary))
        (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))))
    (((W, W_out), (N_s, N_e)),
      ((q, (q_l2, q_tot)), ((S, (q_pi, two_q_pi)), ((t1, winLen), (m1, fourPW)))))

@[simp]
theorem length_encTapUnaryBundle
    (W W_out N_s N_e q q_l2 q_tot S q_pi two_q_pi t1 winLen m1 fourPW : ℕ) :
    (encTapUnaryBundle W W_out N_s N_e q q_l2 q_tot S q_pi two_q_pi t1 winLen m1 fourPW).length =
      2 * (2 * (2 * W + 2 * W_out + 4) + 2 * (2 * N_s + 2 * N_e + 4) + 4) +
      2 * (2 * (2 * q + 2 * (2 * q_l2 + 2 * q_tot + 4) + 4) +
        2 * (2 * (2 * S + 2 * (2 * q_pi + 2 * two_q_pi + 4) + 4) +
          2 * (2 * (2 * t1 + 2 * winLen + 4) + 2 * (2 * m1 + 2 * fourPW + 4) + 4) + 4) + 4) + 4 := by
  simp [encTapUnaryBundle]

/-- Unary parameter stage for `bmNodeTapTableWith`: consumes `(K, p)` on `kIO` and emits
`encTapUnaryBundle`. -/
def bmTapUnaryBundle : BitMachine :=
  let bmK := bmFst
  let bmQ := bmQChildEll
  let bmPC := bmPChildEll
  let bmPW := bmPWorkEll
  let bmM1 := bmComputeM1Ell
  let bmT1 := bmSeq bmK bmT1Ell
  let bmW := bmSeq (bmFanout (bmUnaryConst 1000) bmQ) bmUnaryMul
  let bmWOut := bmSeq bmQ (bmSeq bmUnarySucc bmUnarySucc)
  let bmThreePC := bmSeq (bmFanout (bmUnaryConst 3) bmPC) bmUnaryMul
  let bmQ3PC := bmSeq (bmFanout bmQ bmThreePC) bmUnaryAdd
  let bmS := bmSeq (bmFanout bmQ3PC (bmUnaryConst 20)) bmUnaryAdd
  let bmS3 := bmSeq (bmFanout bmS (bmUnaryConst 3)) bmUnaryAdd
  let bmFourS3 := bmSeq (bmSeq bmS3 bmUnaryDouble) bmUnaryDouble
  let bmQPi := bmSeq (bmFanout bmFourS3 (bmUnaryConst 6)) bmUnaryAdd
  let bmTwoQPi := bmSeq bmQPi bmUnaryDouble
  let bmS2 := bmSeq bmS (bmSeq bmUnarySucc bmUnarySucc)
  let bmQl2 := bmSeq (bmFanout bmS bmS2) bmUnaryAdd
  let bmM1_1 := bmSeq bmM1 bmUnarySucc
  let bmBSinc := bmSeq (bmFanout (bmUnaryConst 5) bmM1_1) bmUnaryMul
  let bmFourBS := bmSeq (bmSeq bmBSinc bmUnaryDouble) bmUnaryDouble
  let bmNs := bmSeq (bmSeq (bmFanout bmFourBS bmS) bmUnaryAdd) bmUnarySucc
  let bmNs6 := bmSeq (bmFanout bmNs (bmUnaryConst 6)) bmUnaryAdd
  let bmThreeNs6 := bmSeq (bmFanout (bmUnaryConst 3) bmNs6) bmUnaryMul
  let bmQAccs := bmSeq (bmFanout bmThreeNs6 (bmUnaryConst 6)) bmUnaryAdd
  let bmPC1 := bmSeq bmPC bmUnarySucc
  let bmBExp := bmSeq (bmFanout (bmUnaryConst 25) bmPC1) bmUnaryMul
  let bmFourBE := bmSeq (bmSeq bmBExp bmUnaryDouble) bmUnaryDouble
  let bmNe := bmSeq (bmSeq (bmFanout bmFourBE bmS) bmUnaryAdd) bmUnarySucc
  let bmNe6 := bmSeq (bmFanout bmNe (bmUnaryConst 6)) bmUnaryAdd
  let bmThreeNe6 := bmSeq (bmFanout (bmUnaryConst 3) bmNe6) bmUnaryMul
  let bmQAcce := bmSeq (bmFanout bmThreeNe6 (bmUnaryConst 6)) bmUnaryAdd
  let bmQTot := bmSeq (bmFanout bmQAccs bmQAcce) bmUnaryAdd
  let bmWinLen := bmSeq (bmSeq bmM1 bmUnaryDouble) bmUnarySucc
  let bmFourPW := bmSeq (bmSeq bmPW bmUnaryDouble) bmUnaryDouble
  bmFanout
    (bmFanout (bmFanout bmW bmWOut) (bmFanout bmNs bmNe))
    (bmFanout
      (bmFanout bmQ (bmFanout bmQl2 bmQTot))
      (bmFanout
        (bmFanout bmS (bmFanout bmQPi bmTwoQPi))
        (bmFanout (bmFanout bmT1 bmWinLen) (bmFanout bmM1 bmFourPW))))

set_option maxHeartbeats 800000 in
theorem bmTapUnaryBundle_computesInTime (K p : ℕ)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let pC := pChildEll K p
    let pW := pWorkEll K p
    let m1 := computeM1Ell K p
    let t1 := t1Ell K
    let W := 1000 * q
    let W_out := q + 2
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
    ∃ t ≤ 100 * K * t1 + 500 * t1 + 5000 * q * q * q * q + 500000000 * q + 500000000,
      bmTapUnaryBundle.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (K, p)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encTapUnaryBundle W W_out N_s N_e q q_l2 q_tot S q_pi (2 * q_pi)
            t1 (2 * m1 + 1) m1 (4 * pW)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro q pC pW m1 t1 W W_out S q_pi q_l2 B_sinc N_s q_accs B_exp N_e q_acce q_tot
  let St := Unit
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hpC_eq : pC = p + 2 * K + 12 := pChildEll_eq K p
  have hpW_eq : pW = p + K + 6 := rfl
  have hm1_le : m1 ≤ pC := computeM1Ell_le_pChildEll K p
  let uK : St → List Bool := fun _ => encUnary K
  let uP : St → List Bool := fun _ => encUnary p
  let uIn : St → List Bool := encDepPair uK uP
  have pK := StageEval.fst uK uP
  have pQ := StageEval.of_computesStageLe bmQChildEll_computesStageLe (fun _ : St => (K, p))
  have pPC := StageEval.of_computesStageLe bmPChildEll_computesStageLe (fun _ : St => (K, p))
  have pPW := StageEval.of_computesStageLe bmPWorkEll_computesStageLe (fun _ : St => (K, p))
  have pM1 := StageEval.of_computesStageLe bmComputeM1Ell_computesStageLe (fun _ : St => (K, p))
  have pT1 := StageEval.seq pK (StageEval.of_computesStageLe bmT1Ell_computesStageLe (fun _ : St => K))
  have pWidth := StageEval.seq (StageEval.fanout (StageEval.unaryConst 1000 uIn) pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (1000, q)))
  have pWOut := StageEval.seq pQ
    (StageEval.seq
      (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => q))
      (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => q + 1)))
  have p3PC := StageEval.seq (StageEval.fanout (StageEval.unaryConst 3 uIn) pPC)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (3, pC)))
  have pQ3PC := StageEval.seq (StageEval.fanout pQ p3PC)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (q, 3 * pC)))
  have pS := StageEval.seq (StageEval.fanout pQ3PC (StageEval.unaryConst 20 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (q + 3 * pC, 20)))
  have pS3 := StageEval.seq (StageEval.fanout pS (StageEval.unaryConst 3 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (S, 3)))
  have p4S3 := StageEval.congr_out (v2 := fun _ => encUnary (4 * (S + 3)))
    (StageEval.seq
      (StageEval.seq pS3 (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => S + 3)))
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * (S + 3))))
    (fun _ => by rw [← Nat.mul_assoc])
  have pQPi := StageEval.seq (StageEval.fanout p4S3 (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (4 * (S + 3), 6)))
  have pTwoQPi := StageEval.seq pQPi
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => q_pi))
  have pS2 := StageEval.seq pS
    (StageEval.seq
      (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => S))
      (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => S + 1)))
  have pQl2 := StageEval.seq (StageEval.fanout pS pS2)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (S, S + 2)))
  have pM1_1 := StageEval.seq pM1
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => m1))
  have pBSinc := StageEval.seq (StageEval.fanout (StageEval.unaryConst 5 uIn) pM1_1)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (5, m1 + 1)))
  have p4BS := StageEval.congr_out (v2 := fun _ => encUnary (4 * B_sinc))
    (StageEval.seq
      (StageEval.seq pBSinc (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => B_sinc)))
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * B_sinc)))
    (fun _ => by rw [← Nat.mul_assoc])
  have pNs := StageEval.seq
    (StageEval.seq (StageEval.fanout p4BS pS)
      (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (4 * B_sinc, S))))
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => 4 * B_sinc + S))
  have pNs6 := StageEval.seq (StageEval.fanout pNs (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (N_s, 6)))
  have p3Ns6 := StageEval.seq (StageEval.fanout (StageEval.unaryConst 3 uIn) pNs6)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (3, N_s + 6)))
  have pQAccs := StageEval.seq (StageEval.fanout p3Ns6 (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (3 * (N_s + 6), 6)))
  have pPC1 := StageEval.seq pPC
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => pC))
  have pBExp := StageEval.seq (StageEval.fanout (StageEval.unaryConst 25 uIn) pPC1)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (25, pC + 1)))
  have p4BE := StageEval.congr_out (v2 := fun _ => encUnary (4 * B_exp))
    (StageEval.seq
      (StageEval.seq pBExp (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => B_exp)))
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * B_exp)))
    (fun _ => by rw [← Nat.mul_assoc])
  have pNe := StageEval.seq
    (StageEval.seq (StageEval.fanout p4BE pS)
      (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (4 * B_exp, S))))
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => 4 * B_exp + S))
  have pNe6 := StageEval.seq (StageEval.fanout pNe (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (N_e, 6)))
  have p3Ne6 := StageEval.seq (StageEval.fanout (StageEval.unaryConst 3 uIn) pNe6)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (3, N_e + 6)))
  have pQAcce := StageEval.seq (StageEval.fanout p3Ne6 (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (3 * (N_e + 6), 6)))
  have pQTot := StageEval.seq (StageEval.fanout pQAccs pQAcce)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (q_accs, q_acce)))
  have pWinLen := StageEval.seq
    (StageEval.seq pM1 (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => m1)))
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => 2 * m1))
  have p4PW := StageEval.congr_out (v2 := fun _ => encUnary (4 * pW))
    (StageEval.seq
      (StageEval.seq pPW (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => pW)))
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * pW)))
    (fun _ => by rw [← Nat.mul_assoc])
  have hall := StageEval.fanout
    (StageEval.fanout (StageEval.fanout pWidth pWOut) (StageEval.fanout pNs pNe))
    (StageEval.fanout
      (StageEval.fanout pQ (StageEval.fanout pQl2 pQTot))
      (StageEval.fanout
        (StageEval.fanout pS (StageEval.fanout pQPi pTwoQPi))
        (StageEval.fanout (StageEval.fanout pT1 pWinLen) (StageEval.fanout pM1 p4PW))))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hW_def : W = 1000 * q := rfl
  have hWout_def : W_out = q + 2 := rfl
  have hS_def : S = q + 3 * pC + 20 := rfl
  have hqpi_def : q_pi = 4 * (S + 3) + 6 := rfl
  have hql2_def : q_l2 = S + (S + 2) := rfl
  have hBsinc_def : B_sinc = 5 * (m1 + 1) := rfl
  have hNs_def : N_s = 4 * B_sinc + S + 1 := rfl
  have hqaccs_def : q_accs = 3 * (N_s + 6) + 6 := rfl
  have hBexp_def : B_exp = 25 * (pC + 1) := rfl
  have hNe_def : N_e = 4 * B_exp + S + 1 := rfl
  have hqacce_def : q_acce = 3 * (N_e + 6) + 6 := rfl
  have hqtot_def : q_tot = q_accs + q_acce := rfl
  have hq_def : qChildEll K p = q := rfl
  have hpC_def : pChildEll K p = pC := rfl
  have hpW_def : pWorkEll K p = pW := rfl
  have hm1_def : computeM1Ell K p = m1 := rfl
  have ht1_def : t1Ell K = t1 := rfl
  have hKt1 : 10 * K * t1 ≤ 100 * K * t1 :=
    Nat.mul_le_mul_right t1 (by omega)
  have hq4_poly :
      4 * (1100 * q * q * q * q) + 4 * (2000 * q * q) ≤ 5000 * q * q * q * q := by
    have hq14 : 14 ≤ q := by omega
    have hq24 : 8000 * (q * q) ≤ 600 * (q * q * q * q) := by
      have : 8000 ≤ 600 * (q * q) := by nlinarith only [hq14]
      calc 8000 * (q * q) ≤ (600 * (q * q)) * (q * q) := Nat.mul_le_mul_right _ this
        _ = 600 * (q * q * q * q) := by ring
    linarith [show 4 * (1100 * q * q * q * q) = 4400 * (q * q * q * q) by ring,
              show 4 * (2000 * q * q) = 8000 * (q * q) by ring,
              show 5000 * q * q * q * q = 5000 * (q * q * q * q) by ring]
  dsimp only [uIn, uK, uP, id] at ht hcomp ⊢
  simp only [length_encDepPair, length_encPair, length_encUnary,
    hq_def, hpC_def, hm1_def, ht1_def] at ht
  exact ⟨t, by omega, hcomp⟩

theorem fitsSignedWord_approxLogTwoFixed (S : ℕ) {w : ℕ} (hw : 2 * S + 4 ≤ w) :
    FitsSignedWord w (approxLogTwoFixed S) := by
  unfold FitsSignedWord
  rw [abs_of_nonneg (approxLogTwoFixed_nonneg S)]
  have hle := approxLogTwoFixed_le S
  have hlt : 2 * (2 : ℤ) ^ (S + (S + 2)) < (2 : ℤ) ^ (2 * S + 4) := by
    have : (2 : ℤ) ^ (2 * S + 4) = 4 * (2 : ℤ) ^ (S + (S + 2)) := by
      rw [show 2 * S + 4 = (S + (S + 2)) + 2 by omega, pow_add]; ring
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (S + (S + 2)) := by positivity
    linarith
  exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt (pow_le_pow_right₀ (by decide) hw))

/-- Stage that consumes `(W, S)` on `kIO` and emits
`encodeSignedWord W (max ((2 : ℤ) ^ ((S + (S + 2)) - 1)) (approxLogTwoFixed S))`. -/
def bmMaxApproxLogTwo : BitMachine :=
  let bmW := bmFst
  let bmS := bmSnd
  let bmS1 := bmSeq bmS bmUnarySucc
  let bmQl2m1 := bmSeq (bmFanout bmS bmS1) bmUnaryAdd
  let bmTwoPow := bmSeq (bmFanout bmW bmQl2m1) bmSignedTwoPow
  bmSeq (bmFanout bmTwoPow bmApproxLogTwo) bmSignedMax

theorem bmMaxApproxLogTwo_computesInTime (W S : ℕ) (hW : 2 * S + 4 ≤ W)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (S + 2) * (250 * W * W + 80000 * W + 200000) + 20000 * W + 60000,
      bmMaxApproxLogTwo.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (W, S)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encodeSignedWord W (max ((2 : ℤ) ^ ((S + (S + 2)) - 1)) (approxLogTwoFixed S))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let St := Unit
  let uIn : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary S)
  have pW := StageEval.fst (fun _ : St => encUnary W) (fun _ => encUnary S)
  have pS := StageEval.snd (fun _ : St => encUnary W) (fun _ => encUnary S)
  have pS1 := StageEval.seq pS
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => S))
  have pQl2m1 := StageEval.seq (StageEval.fanout pS pS1)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (S, S + 1)))
  have hlt_W : S + (S + 1) < W := by omega
  have pTwoPow := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W ((2 : ℤ) ^ ((S + (S + 2)) - 1)))
    (StageEval.seq (StageEval.fanout pW pQl2m1)
      (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W (S + (S + 1)) (by omega) hlt_W)))
    (fun _ => rfl)
  have pL2 := StageEval.const (S := St) (bmApproxLogTwo_computesInTime W S hW)
  have h2_fits : FitsSignedWord W ((2 : ℤ) ^ ((S + (S + 2)) - 1)) :=
    (FitsSignedWord.two_pow ((S + (S + 2)) - 1)).mono (by omega)
  have hl2_fits : FitsSignedWord W (approxLogTwoFixed S) :=
    fitsSignedWord_approxLogTwoFixed S hW
  have hall := StageEval.seq (StageEval.fanout pTwoPow pL2)
    (StageEval.const (S := St)
      (bmSignedMax_computesInTime W ((2 : ℤ) ^ ((S + (S + 2)) - 1)) (approxLogTwoFixed S)
        h2_fits hl2_fits))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Stage that consumes `encTapUnaryBundle` on `kIO` and emits
`(((tapCtx, 2 * m1 + 1), W), t1)`. -/
def bmTapCtxFromUnaryWith (bmMul : BitMachine) : BitMachine :=
  let bmLeft := bmFst
  let bmR1 := bmSeq bmSnd bmFst
  let bmR2 := bmSeq bmSnd bmSnd
  let bmW := bmSeq (bmSeq bmLeft bmFst) bmFst
  let bmS := bmSeq (bmSeq bmR2 bmFst) bmFst
  let bmQPi := bmSeq (bmSeq (bmSeq bmR2 bmFst) bmSnd) bmFst
  let bmTwoQPi := bmSeq (bmSeq (bmSeq bmR2 bmFst) bmSnd) bmSnd
  let bmT1 := bmSeq (bmSeq (bmSeq bmR2 bmSnd) bmFst) bmFst
  let bmWinLen := bmSeq (bmSeq (bmSeq bmR2 bmSnd) bmFst) bmSnd
  let bmM1 := bmSeq (bmSeq (bmSeq bmR2 bmSnd) bmSnd) bmFst
  let bmFourPW := bmSeq (bmSeq (bmSeq bmR2 bmSnd) bmSnd) bmSnd
  let bmPiFixed := bmSeq (bmFanout bmW bmS) bmApproxPi
  let bmL2Fixed := bmSeq (bmFanout bmW bmS) bmMaxApproxLogTwo
  let bmT1s := bmSeq (bmFanout bmW bmT1) bmUnaryToSigned
  let bmM1s := bmSeq (bmFanout bmW bmM1) bmUnaryToSigned
  let bmFourPWs := bmSeq (bmFanout bmW bmFourPW) bmUnaryToSigned
  let bmTwoPowQPi := bmSeq (bmFanout bmW bmQPi) bmSignedTwoPow
  let bmTwoPow2QPi := bmSeq (bmFanout bmW bmTwoQPi) bmSignedTwoPow
  let bmThDen := bmSeq (bmFanout bmT1s bmTwoPowQPi) (bmSignedMulSameWith bmMul)
  let bmFourPWT1 := bmSeq (bmFanout bmFourPWs bmT1s) (bmSignedMulSameWith bmMul)
  let bmFourPWT1Sq := bmSeq (bmFanout bmFourPWT1 bmT1s) (bmSignedMulSameWith bmMul)
  let bmGDenPre := bmSeq (bmFanout bmFourPWT1Sq bmL2Fixed) (bmSignedMulSameWith bmMul)
  let bmGDen := bmSeq (bmFanout bmGDenPre bmTwoPow2QPi) (bmSignedMulSameWith bmMul)
  let bmR2Ctx := bmFanout (bmFanout bmT1s bmM1s) (bmFanout bmPiFixed (bmFanout bmThDen bmGDen))
  let bmTapCtx := bmFanout bmLeft (bmFanout bmR1 bmR2Ctx)
  bmFanout (bmFanout (bmFanout bmTapCtx bmWinLen) bmW) bmT1

set_option maxHeartbeats 800000 in
theorem bmTapCtxFromUnaryWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ) (hK : 2 ≤ K) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let pC := pChildEll K p
    let pW := pWorkEll K p
    let m1 := computeM1Ell K p
    let t1 := t1Ell K
    let W := 1000 * q
    let W_out := q + 2
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
    ∃ t ≤ (S + 4) * (1250 * W * W + 400000 * W + 1000000) +
        10 * mulTime W + 3000 * W * W + 10000000 * W + t1 * (4000 * W + 100000) + 10000000,
      (bmTapCtxFromUnaryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encTapUnaryBundle W W_out N_s N_e q q_l2 q_tot S q_pi (2 * q_pi)
            t1 (2 * m1 + 1) m1 (4 * pW)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair (encPair id encUnary) encUnary) encUnary
            (((encTapEntryCtx W W_out N_s N_e q q_l2 q_tot (t1 : ℤ) (m1 : ℤ) piFixed θDen gDen,
              2 * m1 + 1), W), t1)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro q pC pW m1 t1 W W_out S q_pi q_l2 B_sinc N_s q_accs B_exp N_e q_acce q_tot
    piFixed l2Fixed θDen gDen
  obtain ⟨W0, hW0_def⟩ : ∃ x : ℕ, x = W := ⟨_, rfl⟩
  obtain ⟨fourPW, h4pW_def⟩ : ∃ x : ℕ, x = 4 * pW := ⟨_, rfl⟩
  rw [← hW0_def, ← h4pW_def]
  let St := Unit
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hpC_eq : pC = p + 2 * K + 12 := pChildEll_eq K p
  have hpW_eq : pW = p + K + 6 := rfl
  have hm1_le : m1 ≤ pC := computeM1Ell_le_pChildEll K p
  have hW_eq : W0 = 1000 * q := hW0_def
  have hW_pos : 1 ≤ W0 := by omega
  have ht1_le : t1 ≤ 2 ^ K := t1Ell_le_two_pow K
  have ht1_pow_q : t1 ≤ 2 ^ q := ht1_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have ht1_lt_q1 : t1 < 2 ^ (q + 1) :=
    lt_of_le_of_lt ht1_pow_q (Nat.pow_lt_pow_right (by decide) (by omega))
  have ht1_lt_W : t1 < 2 ^ W0 :=
    lt_of_lt_of_le ht1_lt_q1 (Nat.pow_le_pow_right (by decide) (by omega))
  have hm1_lt_q : m1 + 1 < 2 ^ q :=
    lt_of_le_of_lt (by omega : m1 + 1 ≤ q) Nat.lt_two_pow_self
  have hm1_lt_W : m1 < 2 ^ W0 :=
    lt_of_lt_of_le (lt_of_le_of_lt (Nat.le_succ m1) hm1_lt_q)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have h4pW_lt_q : fourPW < 2 ^ q :=
    lt_of_le_of_lt (by omega : fourPW ≤ 4 * q) (four_mul_lt_two_pow (by omega))
  have h4pW_lt_W : fourPW < 2 ^ W0 :=
    lt_of_lt_of_le h4pW_lt_q (Nat.pow_le_pow_right (by decide) (by omega))
  have hqpi_lt_W : q_pi < W0 := by dsimp [q_pi, S]; omega
  have h2qpi_lt_W : 2 * q_pi < W0 := by dsimp [q_pi, S]; omega
  have hpi_W : 5 * S + 30 ≤ W0 := by dsimp [S]; omega
  have hl2_W : 2 * S + 4 ≤ W0 := by dsimp [S]; omega
  have ht1_fits_q : FitsSignedWord (q + 1) (t1 : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact ht1_lt_q1
  have ht1_fits : FitsSignedWord W0 (t1 : ℤ) := ht1_fits_q.mono (by omega)
  have hm1_fits_q : FitsSignedWord q (m1 : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; omega
  have hm1_fits : FitsSignedWord W0 (m1 : ℤ) := hm1_fits_q.mono (by omega)
  have h4pW_fits_q : FitsSignedWord (q + 2) (fourPW : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact lt_of_lt_of_le h4pW_lt_q (Nat.pow_le_pow_right (by decide) (by omega))
  have h4pW_fits : FitsSignedWord W0 (fourPW : ℤ) := h4pW_fits_q.mono (by omega)
  have h2qpi_fits : FitsSignedWord W0 ((2 : ℤ) ^ q_pi) :=
    (FitsSignedWord.two_pow q_pi).mono (by dsimp [q_pi, S]; omega)
  have h2_2qpi_fits : FitsSignedWord W0 ((2 : ℤ) ^ (2 * q_pi)) :=
    (FitsSignedWord.two_pow (2 * q_pi)).mono (by dsimp [q_pi, S]; omega)
  have hθDen_fits_small := ht1_fits_q.mul_two_pow q_pi
  have hθDen_fits : FitsSignedWord W0 θDen :=
    hθDen_fits_small.mono (by dsimp [q_pi, S]; omega)
  have hl2_fits_small : FitsSignedWord (2 * S + 4) l2Fixed :=
    fitsSignedWord_max_approxLogTwoFixed S (le_refl _)
  have hl2_fits : FitsSignedWord W0 l2Fixed := hl2_fits_small.mono hl2_W
  have h4pWt1_fits_small := h4pW_fits_q.mul ht1_fits_q
  have h4pWt1_fits : FitsSignedWord W0 ((fourPW : ℤ) * (t1 : ℤ)) :=
    h4pWt1_fits_small.mono (by omega)
  have h4pWt1sq_fits_small := h4pWt1_fits_small.mul ht1_fits_q
  have h4pWt1sq_fits : FitsSignedWord W0 (((fourPW : ℤ) * (t1 : ℤ)) * (t1 : ℤ)) :=
    h4pWt1sq_fits_small.mono (by omega)
  have hgDenPre_fits_small := h4pWt1sq_fits_small.mul hl2_fits_small
  have hgDenPre_fits : FitsSignedWord W0 ((((fourPW : ℤ) * (t1 : ℤ)) * (t1 : ℤ)) * l2Fixed) :=
    hgDenPre_fits_small.mono (by dsimp [S]; omega)
  have hgDen_eq : ((((fourPW : ℤ) * (t1 : ℤ)) * (t1 : ℤ)) * l2Fixed) * (2 : ℤ) ^ (2 * q_pi) =
      gDen := by rw [h4pW_def]; rfl
  have hgDen_fits_small := hgDenPre_fits_small.mul_two_pow (2 * q_pi)
  have hgDen_fits : FitsSignedWord W0
      (((((fourPW : ℤ) * (t1 : ℤ)) * (t1 : ℤ)) * l2Fixed) * (2 : ℤ) ^ (2 * q_pi)) :=
    hgDen_fits_small.mono (by dsimp [q_pi, S]; omega)
  let uL1 : St → List Bool := encDepPair (fun _ => encUnary W0) (fun _ => encUnary W_out)
  let uL2 : St → List Bool := encDepPair (fun _ => encUnary N_s) (fun _ => encUnary N_e)
  let uLeft : St → List Bool := encDepPair uL1 uL2
  let uR1 : St → List Bool := encDepPair (fun _ => encUnary q)
    (encDepPair (fun _ => encUnary q_l2) (fun _ => encUnary q_tot))
  let uR21 : St → List Bool := encDepPair (fun _ => encUnary S)
    (encDepPair (fun _ => encUnary q_pi) (fun _ => encUnary (2 * q_pi)))
  let uR221 : St → List Bool := encDepPair (fun _ => encUnary t1) (fun _ => encUnary (2 * m1 + 1))
  let uR222 : St → List Bool := encDepPair (fun _ => encUnary m1) (fun _ => encUnary fourPW)
  let uR22 : St → List Bool := encDepPair uR221 uR222
  let uR2 : St → List Bool := encDepPair uR21 uR22
  let uRight : St → List Bool := encDepPair uR1 uR2
  let uIn : St → List Bool := encDepPair uLeft uRight
  have pLeft := StageEval.fst uLeft uRight
  have pRight := StageEval.snd uLeft uRight
  have pR1 := StageEval.seq pRight (StageEval.fst uR1 uR2)
  have pR2 := StageEval.seq pRight (StageEval.snd uR1 uR2)
  have pWidth := StageEval.seq (StageEval.seq pLeft (StageEval.fst uL1 uL2))
    (StageEval.fst (fun _ : St => encUnary W0) (fun _ => encUnary W_out))
  have pR21 := StageEval.seq pR2 (StageEval.fst uR21 uR22)
  have pR22 := StageEval.seq pR2 (StageEval.snd uR21 uR22)
  have pS := StageEval.seq pR21
    (StageEval.fst (fun _ : St => encUnary S)
      (encDepPair (fun _ => encUnary q_pi) (fun _ => encUnary (2 * q_pi))))
  have pQPiPair := StageEval.seq pR21
    (StageEval.snd (fun _ : St => encUnary S)
      (encDepPair (fun _ => encUnary q_pi) (fun _ => encUnary (2 * q_pi))))
  have pQPi := StageEval.seq pQPiPair
    (StageEval.fst (fun _ : St => encUnary q_pi) (fun _ => encUnary (2 * q_pi)))
  have pTwoQPi := StageEval.seq pQPiPair
    (StageEval.snd (fun _ : St => encUnary q_pi) (fun _ => encUnary (2 * q_pi)))
  have pR221 := StageEval.seq pR22 (StageEval.fst uR221 uR222)
  have pR222 := StageEval.seq pR22 (StageEval.snd uR221 uR222)
  have pT1 := StageEval.seq pR221
    (StageEval.fst (fun _ : St => encUnary t1) (fun _ => encUnary (2 * m1 + 1)))
  have pWinLen := StageEval.seq pR221
    (StageEval.snd (fun _ : St => encUnary t1) (fun _ => encUnary (2 * m1 + 1)))
  have pM1 := StageEval.seq pR222
    (StageEval.fst (fun _ : St => encUnary m1) (fun _ => encUnary fourPW))
  have pFourPW := StageEval.seq pR222
    (StageEval.snd (fun _ : St => encUnary m1) (fun _ => encUnary fourPW))
  have pPiFixed := StageEval.seq (StageEval.fanout pWidth pS)
    (StageEval.const (S := St) (bmApproxPi_computesInTime W0 S hpi_W))
  have pL2Fixed := StageEval.seq (StageEval.fanout pWidth pS)
    (StageEval.const (S := St) (bmMaxApproxLogTwo_computesInTime W0 S hl2_W))
  have pT1s := StageEval.seq (StageEval.fanout pWidth pT1)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W0 t1 hW_pos ht1_lt_W))
  have pM1s := StageEval.seq (StageEval.fanout pWidth pM1)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W0 m1 hW_pos hm1_lt_W))
  have pFourPWs := StageEval.seq (StageEval.fanout pWidth pFourPW)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W0 fourPW hW_pos h4pW_lt_W))
  have pTwoPowQPi := StageEval.seq (StageEval.fanout pWidth pQPi)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W0 q_pi hW_pos hqpi_lt_W))
  have pTwoPow2QPi := StageEval.seq (StageEval.fanout pWidth pTwoQPi)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W0 (2 * q_pi) hW_pos h2qpi_lt_W))
  have pThDen := StageEval.seq (StageEval.fanout pT1s pTwoPowQPi)
    (StageEval.signedMulSameWith hmul (fun _ => W0) (fun _ => (t1 : ℤ)) (fun _ => (2 : ℤ) ^ q_pi)
      (fun _ => ht1_fits) (fun _ => h2qpi_fits) (fun _ => hθDen_fits))
  have pFourPWT1 := StageEval.seq (StageEval.fanout pFourPWs pT1s)
    (StageEval.signedMulSameWith hmul (fun _ => W0) (fun _ => (fourPW : ℤ)) (fun _ => (t1 : ℤ))
      (fun _ => h4pW_fits) (fun _ => ht1_fits) (fun _ => h4pWt1_fits))
  have pFourPWT1Sq := StageEval.seq (StageEval.fanout pFourPWT1 pT1s)
    (StageEval.signedMulSameWith hmul (fun _ => W0)
      (fun _ => (fourPW : ℤ) * (t1 : ℤ)) (fun _ => (t1 : ℤ))
      (fun _ => h4pWt1_fits) (fun _ => ht1_fits) (fun _ => h4pWt1sq_fits))
  have pGDenPre := StageEval.seq (StageEval.fanout pFourPWT1Sq pL2Fixed)
    (StageEval.signedMulSameWith hmul (fun _ => W0)
      (fun _ => ((fourPW : ℤ) * (t1 : ℤ)) * (t1 : ℤ)) (fun _ => l2Fixed)
      (fun _ => h4pWt1sq_fits) (fun _ => hl2_fits) (fun _ => hgDenPre_fits))
  have pGDen := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 gDen)
    (StageEval.seq (StageEval.fanout pGDenPre pTwoPow2QPi)
      (StageEval.signedMulSameWith hmul (fun _ => W0)
        (fun _ => (((fourPW : ℤ) * (t1 : ℤ)) * (t1 : ℤ)) * l2Fixed)
        (fun _ => (2 : ℤ) ^ (2 * q_pi))
        (fun _ => hgDenPre_fits) (fun _ => h2_2qpi_fits) (fun _ => hgDen_fits)))
    (fun _ => congrArg (encodeSignedWord W0) hgDen_eq)
  have pR2Ctx := StageEval.fanout (StageEval.fanout pT1s pM1s)
    (StageEval.fanout pPiFixed (StageEval.fanout pThDen pGDen))
  have pTapCtx := StageEval.fanout pLeft (StageEval.fanout pR1 pR2Ctx)
  have hall := StageEval.fanout (StageEval.fanout (StageEval.fanout pTapCtx pWinLen) pWidth) pT1
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  clear pLeft pRight pR1 pR2 pWidth pR21 pR22 pS pQPiPair pQPi pTwoQPi pR221 pR222
    pT1 pWinLen pM1 pFourPW pPiFixed pL2Fixed pT1s pM1s pFourPWs pTwoPowQPi pTwoPow2QPi
    pThDen pFourPWT1 pFourPWT1Sq pGDenPre pGDen pR2Ctx pTapCtx hall
  have hWout_def : W_out = q + 2 := rfl
  have hS_def : S = q + 3 * pC + 20 := rfl
  have hqpi_def : q_pi = 4 * (S + 3) + 6 := rfl
  have hql2_def : q_l2 = S + (S + 2) := rfl
  have hBsinc_def : B_sinc = 5 * (m1 + 1) := rfl
  have hNs_def : N_s = 4 * B_sinc + S + 1 := rfl
  have hqaccs_def : q_accs = 3 * (N_s + 6) + 6 := rfl
  have hBexp_def : B_exp = 25 * (pC + 1) := rfl
  have hNe_def : N_e = 4 * B_exp + S + 1 := rfl
  have hqacce_def : q_acce = 3 * (N_e + 6) + 6 := rfl
  have hqtot_def : q_tot = q_accs + q_acce := rfl
  have hpi_l2_comb :
      (S + 4) * (1000 * W0 * W0 + 320000 * W0 + 800000) +
      (S + 2) * (250 * W0 * W0 + 80000 * W0 + 200000) ≤
      (S + 4) * (1250 * W0 * W0 + 400000 * W0 + 1000000) := by
    have h1 : (S + 2) * (250 * W0 * W0 + 80000 * W0 + 200000) ≤
        (S + 4) * (250 * W0 * W0 + 80000 * W0 + 200000) :=
      Nat.mul_le_mul_right _ (by linarith only)
    have h2 :
        (S + 4) * (1000 * W0 * W0 + 320000 * W0 + 800000) +
        (S + 4) * (250 * W0 * W0 + 80000 * W0 + 200000) =
        (S + 4) * (1250 * W0 * W0 + 400000 * W0 + 1000000) := by ring
    linarith only [h1, h2]
  have hm1_W : m1 * (800 * W0 + 2010) ≤ 800 * W0 * W0 + 2010 * W0 := by
    have h1 : m1 ≤ W0 := by linarith only [hm1_le, hpC_eq, hq_eq, hW_eq]
    have h2 := Nat.mul_le_mul_right (800 * W0 + 2010) h1
    have hr : W0 * (800 * W0 + 2010) = 800 * W0 * W0 + 2010 * W0 := by ring
    linarith only [h2, hr]
  have h4pW_W : fourPW * (800 * W0 + 2010) ≤ 800 * W0 * W0 + 2010 * W0 := by
    have h1 : fourPW ≤ W0 := by linarith only [h4pW_def, hpW_eq, hq_eq, hW_eq]
    have h2 := Nat.mul_le_mul_right (800 * W0 + 2010) h1
    have hr : W0 * (800 * W0 + 2010) = 800 * W0 * W0 + 2010 * W0 := by ring
    linarith only [h2, hr]
  have ht1_W : 4 * (t1 * (800 * W0 + 2010)) + 10000 * t1 ≤ t1 * (4000 * W0 + 100000) := by
    have h1 : 3200 * W0 + 18040 ≤ 4000 * W0 + 100000 := by linarith only
    have h2 := Nat.mul_le_mul_left t1 h1
    have hr : 4 * (t1 * (800 * W0 + 2010)) + 10000 * t1 = t1 * (3200 * W0 + 18040) := by ring
    linarith only [h2, hr]
  have hW0_sq : 600 * W0 * W0 + 800 * W0 * W0 + 800 * W0 * W0 ≤ 3000 * W0 * W0 := by
    have h1 := Nat.mul_le_mul_right W0 (by linarith only : 2200 * W0 ≤ 3000 * W0)
    have hr : 600 * W0 * W0 + 800 * W0 * W0 + 800 * W0 * W0 = 2200 * W0 * W0 := by ring
    linarith only [h1, hr]
  dsimp (config := { zeta := false }) only
    [uIn, uLeft, uRight, uL1, uL2, uR1, uR2, uR21, uR22, uR221, uR222, id] at ht hcomp
  simp (config := { zeta := false }) only
    [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  refine ⟨t, ?_, hcomp⟩
  clear hcomp uIn uLeft uRight uL1 uL2 uR1 uR2 uR21 uR22 uR221 uR222 St
    piFixed l2Fixed θDen gDen hgDen_fits hgDen_fits_small hgDen_eq hgDenPre_fits hgDenPre_fits_small
    h4pWt1sq_fits h4pWt1sq_fits_small h4pWt1_fits h4pWt1_fits_small hl2_fits hl2_fits_small
    hθDen_fits hθDen_fits_small h2_2qpi_fits h2qpi_fits h4pW_fits h4pW_fits_q hm1_fits hm1_fits_q
    ht1_fits ht1_fits_q ht1_le ht1_pow_q ht1_lt_q1 ht1_lt_W hm1_lt_q hm1_lt_W h4pW_lt_q h4pW_lt_W
  linarith

/-- Element emitter for `bmNodeTapTableWith`: transforms `(((tapCtx, j1_s), W), k_s)` into
`((tapCtx, j1_s), k_s)` and calls `bmFilterTapEntryWith bmMul`. -/
def bmTapElemEmitWith (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmMapFst bmFst) (bmFilterTapEntryWith bmMul)

/-- Row emitter for `bmNodeTapTableWith`: consumes `(((tapCtx, winLen), W), j1_s)` on `kIO`,
rearranges to `(((tapCtx, j1_s), W), winLen)`, and tabulates `bmTapElemEmitWith bmMul`. -/
def bmTapRowEmitWith (bmMul : BitMachine) : BitMachine :=
  let bmOuter := bmSeq bmFst bmFst
  let bmTapCtx := bmSeq bmOuter bmFst
  let bmWinLen := bmSeq bmOuter bmSnd
  let bmW := bmSeq bmFst bmSnd
  let bmJ1 := bmSnd
  let bmRowIn := bmFanout (bmFanout (bmFanout bmTapCtx bmJ1) bmW) bmWinLen
  bmSeq bmRowIn (bmTabulateSigned (bmTapElemEmitWith bmMul))

/-- **2D Sinc-Gaussian Filter Tap Table Stage (`bmNodeTapTableWith bmMul`)**:
Consumes `(K, p)` on `kIO` and emits
`encTapTable K p (computeM1Ell K p) (computeFilterTapFixed K p)`. -/
def bmNodeTapTableWith (bmMul : BitMachine) : BitMachine :=
  bmSeq bmTapUnaryBundle
    (bmSeq (bmTapCtxFromUnaryWith bmMul)
      (bmTabulateSigned (bmTapRowEmitWith bmMul)))

theorem length_encTapTable_row_le (K p m1 : ℕ)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ) (j1 : Fin (t1Ell K)) :
    (encList (encodeSignedWord (qChildEll K p + 2))
      ((List.finRange (2 * m1 + 1)).map (fun k => filterTap j1 ((k.val : ℤ) - (m1 : ℤ))))).length ≤
      (2 * m1 + 1) * (4 * qChildEll K p + 14) := by
  have h := StageEval.length_encList_le_of_forall_le (encodeSignedWord (qChildEll K p + 2))
    (2 * qChildEll K p + 6)
    ((List.finRange (2 * m1 + 1)).map (fun k => filterTap j1 ((k.val : ℤ) - (m1 : ℤ))))
    (fun x _ => by simp only [length_encodeSignedWord]; omega)
  rw [List.length_map, List.length_finRange] at h
  exact le_trans h (Nat.mul_le_mul_left _ (by omega))

theorem length_encTapTable_le (K p m1 : ℕ) (filterTap : Fin (t1Ell K) → ℤ → ℤ) :
    (encTapTable K p m1 filterTap).length ≤
      t1Ell K * ((2 * m1 + 1) * (8 * qChildEll K p + 30)) := by
  unfold encTapTable
  have h := StageEval.length_encList_le_of_forall_le
    (encList (encodeSignedWord (qChildEll K p + 2)))
    ((2 * m1 + 1) * (4 * qChildEll K p + 14))
    ((List.finRange (t1Ell K)).map (fun j1 =>
      (List.finRange (2 * m1 + 1)).map (fun k => filterTap j1 ((k.val : ℤ) - (m1 : ℤ)))))
    (fun row hrow => by
      rcases List.mem_map.mp hrow with ⟨j1, _, rfl⟩
      exact length_encTapTable_row_le K p m1 filterTap j1)
  have h2 :
      2 * ((2 * m1 + 1) * (4 * qChildEll K p + 14)) + 2 ≤
      (2 * m1 + 1) * (8 * qChildEll K p + 30) := by
    have : 1 ≤ 2 * m1 + 1 := by omega
    nlinarith
  exact le_trans (by simpa [List.length_map, List.length_finRange] using h)
    (Nat.mul_le_mul_left (t1Ell K) h2)

set_option maxHeartbeats 4000000 in
theorem bmNodeTapTableWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ) (hleaf : (!isBaseLeaf K p) = true) (hK : 2 ≤ K)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let t1 := t1Ell K
    let m1 := computeM1Ell K p
    let r := rEll K
    let S_term := scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q)
    ∃ t ≤ 1000000000000 * ((t1 * (2 * m1 + 1) + r) * S_term),
      (bmNodeTapTableWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (K, p)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encTapTable K p m1 (computeFilterTapFixed K p)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  obtain ⟨tapFn, htapFn⟩ : ∃ f : Fin (t1Ell K) → ℤ → ℤ, f = computeFilterTapFixed K p := ⟨_, rfl⟩
  rw [← htapFn]
  have hRowLen : ∀ j1 : Fin (t1Ell K),
      (encList (encodeSignedWord (qChildEll K p + 2))
        ((List.finRange (2 * computeM1Ell K p + 1)).map (fun k =>
          tapFn j1 ((k.val : ℤ) - (computeM1Ell K p : ℤ))))).length ≤
      (2 * computeM1Ell K p + 1) * (4 * qChildEll K p + 14) :=
    length_encTapTable_row_le K p (computeM1Ell K p) tapFn
  unfold encTapTable
  generalize hq_def : qChildEll K p = q at hRowLen ⊢
  generalize hpC_def : pChildEll K p = pC
  generalize hpW_def : pWorkEll K p = pW
  generalize hm1_def : computeM1Ell K p = m1 at hRowLen ⊢
  generalize hr_def : rEll K = r
  let t1 := t1Ell K
  let S_term := scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q)
  let St := Unit
  let winLen := 2 * m1 + 1
  let W := 1000 * q
  let W_out := q + 2
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
  let tapCtx := encTapEntryCtx W W_out N_s N_e q q_l2 q_tot (t1 : ℤ) (m1 : ℤ) piFixed θDen gDen
  have hq_eq : q = p + 2 * K + 14 := hq_def.symm.trans (qChildEll_eq K p)
  have hpC_eq : pC = p + 2 * K + 12 := hpC_def.symm.trans (pChildEll_eq K p)
  have hpW_eq : pW = p + K + 6 := hpW_def.symm
  have hm1_le : m1 ≤ pC := by rw [← hm1_def, ← hpC_def]; exact computeM1Ell_le_pChildEll K p
  have hW_pos : 1 ≤ W := by dsimp [W]; omega
  have ht1_pos : 1 ≤ t1 := t1Ell_pos K
  have hr_pos : 1 ≤ r := by rw [← hr_def]; exact rEll_pos K
  have hwin_pos : 1 ≤ winLen := by dsimp [winLen]; omega
  have ht1_le : t1 ≤ 2 ^ K := t1Ell_le_two_pow K
  have ht1_pow_q : t1 ≤ 2 ^ q := ht1_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have ht1_lt_W : t1 < 2 ^ W :=
    lt_of_le_of_lt ht1_pow_q (Nat.pow_lt_pow_right (by decide) (by dsimp [W]; omega))
  have hwin_lt_W : winLen < 2 ^ W :=
    lt_of_le_of_lt (by dsimp [winLen, W]; omega : winLen ≤ W) Nat.lt_two_pow_self
  have hlen_tapCtx : tapCtx.length ≤ 320 * W + 600 := by
    dsimp only [tapCtx, W_out, N_s, N_e, B_sinc, B_exp, q_l2, q_tot, q_accs, q_acce, S, W]
    simp only [length_encTapEntryCtx]
    omega
  let uOuterCtx : St → List Bool := encDepPair (fun _ => tapCtx) (fun _ => encUnary winLen)
  have hlen_outerCtx : (uOuterCtx ()).length ≤ 650 * W + 1300 := by
    dsimp only [uOuterCtx, winLen]
    simp only [length_encDepPair, length_encUnary]
    omega
  let B_elem : ℕ :=
    (N_s + N_e + 14) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
    16 * mulTime W + 45000 * W * W + 3050000 * W + 4100000
  let B_row : ℕ := winLen * (B_elem + 1866000 * W + 3530000)
  have hemitRow : ∀ (j1 : ℕ),
      StageEval (S := { _s : St // j1 < t1 }) (bmTapRowEmitWith bmMul)
        (encDepPair (encDepPair (fun _ => uOuterCtx ()) (fun _ => encUnary W))
          (fun _ => encodeSignedWord W (j1 : ℤ)))
        (fun _ => encList (encodeSignedWord W_out)
          (if hj1 : j1 < t1 then
            (List.finRange winLen).map (fun k => tapFn ⟨j1, hj1⟩ ((k.val : ℤ) - (m1 : ℤ)))
          else []))
        (fun _ => B_row) := fun j1 => by
    let RowS := { _s : St // j1 < t1 }
    by_cases hj1 : j1 < t1
    · rw [dif_pos hj1]
      let j1Fin : Fin t1 := ⟨j1, hj1⟩
      let uOCW : RowS → List Bool := encDepPair (fun _ => uOuterCtx ()) (fun _ => encUnary W)
      let uJ1 : RowS → List Bool := fun _ => encodeSignedWord W (j1 : ℤ)
      have pF1 := StageEval.fst uOCW uJ1
      have pJ1 := StageEval.snd uOCW uJ1
      have pOC := StageEval.seq pF1
        (StageEval.fst (fun _ : RowS => uOuterCtx ()) (fun _ => encUnary W))
      have pW' := StageEval.seq pF1
        (StageEval.snd (fun _ : RowS => uOuterCtx ()) (fun _ => encUnary W))
      have pTC := StageEval.seq pOC
        (StageEval.fst (fun _ : RowS => tapCtx) (fun _ => encUnary winLen))
      have pWL := StageEval.seq pOC
        (StageEval.snd (fun _ : RowS => tapCtx) (fun _ => encUnary winLen))
      have pRowIn := StageEval.fanout (StageEval.fanout (StageEval.fanout pTC pJ1) pW') pWL
      let uRowCtx : RowS → List Bool :=
        encDepPair (fun _ => tapCtx) (fun _ => encodeSignedWord W (j1 : ℤ))
      have hlen_rowCtx : (uRowCtx ⟨(), hj1⟩).length ≤ 644 * W + 1208 := by
        dsimp only [uRowCtx]
        simp only [length_encDepPair, length_encodeSignedWord]
        omega
      have hemitElem : ∀ (k : ℕ),
          StageEval (S := { _r : RowS // k < winLen }) (bmTapElemEmitWith bmMul)
            (encDepPair (encDepPair (fun _ => uRowCtx ⟨(), hj1⟩) (fun _ => encUnary W))
              (fun _ => encodeSignedWord W (k : ℤ)))
            (fun _ => encodeSignedWord W_out
              (tapFn j1Fin ((k : ℤ) - (m1 : ℤ))))
            (fun _ => B_elem) := fun k => by
        let ElemS := { _r : RowS // k < winLen }
        by_cases hk : k < winLen
        · let uRCW : ElemS → List Bool :=
            encDepPair (fun _ => uRowCtx ⟨(), hj1⟩) (fun _ => encUnary W)
          let uK : ElemS → List Bool := fun _ => encodeSignedWord W (k : ℤ)
          have pDropW := StageEval.mapFst (u2 := uK)
            (StageEval.fst (fun _ : ElemS => uRowCtx ⟨(), hj1⟩) (fun _ => encUnary W))
          have hk_le : k ≤ 2 * computeM1Ell K p := by rw [hm1_def]; dsimp [winLen] at hk; omega
          have hEntry := bmFilterTapEntryWith_computesInTime hmul W W_out K p hK
            (by rw [hq_def]) (by rw [hq_def])
            (by dsimp [W_out, W]; omega) j1Fin k hk_le
          dsimp only at hEntry
          rw [← htapFn, hq_def, hpC_def, hpW_def, hm1_def] at hEntry
          have pEntry := StageEval.const (S := ElemS) hEntry
          refine (StageEval.seq pDropW pEntry).mono (fun _ => ?_)
          dsimp only [uRCW, uK, uRowCtx, B_elem, N_s, N_e, B_sinc, B_exp, S]
          simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
          omega
        · intro s'; exact False.elim (hk s'.property)
      have pTabElem := StageEval.tabulateSigned (S := RowS) (emitM := bmTapElemEmitWith bmMul)
        (uCtx := uRowCtx) (W := fun _ => W) (N := fun _ => winLen)
        (encElem := fun _ => encodeSignedWord W_out)
        (fn := fun _ k => tapFn j1Fin ((k : ℤ) - (m1 : ℤ)))
        (B := fun _ => B_elem)
        (L_ctx := fun _ => 644 * W + 1208)
        (L_elem := fun _ => 2 * W_out + 2)
        (fun _ => hW_pos) (fun _ => hwin_lt_W) hemitElem
        (fun _ => hlen_rowCtx)
        (fun _ _ _ => by simp only [length_encodeSignedWord]; omega)
      refine (StageEval.seq pRowIn pTabElem).mono (fun _ => ?_)
      dsimp only [uOCW, uJ1, uOuterCtx, uRowCtx]
      simp only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      clear pF1 pJ1 pOC pW' pTC pWL pRowIn hemitElem pTabElem hlen_rowCtx uOCW uJ1 uRowCtx
      have h1 :
          B_elem + 1000 * W + 100 * (644 * W + 1208) + 50 * (2 * W_out + 2) + 2500 + 60 ≤
          B_elem + 66000 * W + 130000 := by
        dsimp only [W_out, W]; linarith only [hq_eq]
      have hm1_mul := Nat.mul_le_mul_left winLen h1
      have h2 :
          2500 * (644 * W + 1208) + 10000 * W + 30000 +
          (20 * (2 * (2 * (2 * tapCtx.length + 2 * (2 * winLen + 1) + 4) + 2 * (2 * W + 1) + 4) +
            2 * (2 * (W + 1) + 2) + 4) + 20) +
          (20 * (2 * (2 * tapCtx.length + 2 * (2 * winLen + 1) + 4) + 2 * (2 * W + 1) + 4) + 20) +
          (20 * (2 * tapCtx.length + 2 * (2 * winLen + 1) + 4) + 20) +
          (20 * (2 * (2 * tapCtx.length + 2 * (2 * (W + 1) + 2) + 4) + 2 * (2 * W + 1) + 4) + 100) +
          (20 * (2 * tapCtx.length + 2 * (2 * (W + 1) + 2) + 4) + 100) + 300 ≤
          1800000 * W + 3400000 := by
        dsimp only [winLen, W] at hlen_tapCtx ⊢; linarith only [hlen_tapCtx, hm1_le, hpC_eq, hq_eq]
      have hm2_mul : 1800000 * W + 3400000 ≤ winLen * (1800000 * W + 3400000) :=
        Nat.le_mul_of_pos_left _ hwin_pos
      dsimp only [B_row]
      linarith only [hm1_mul, h2, hm2_mul,
                show winLen * (B_elem + 66000 * W + 130000) + winLen * (1800000 * W + 3400000) =
                  winLen * (B_elem + 1866000 * W + 3530000) by ring,
                show winLen * (B_elem + 1000 * W + 100 * (644 * W + 1208) + 50 * (2 * W_out + 2) + 2500 + 60) =
                  winLen * (B_elem + 1000 * W + 100 * (644 * W + 1208) + 50 * (2 * W_out + 2) + 2500) +
                  50 * winLen + 10 * winLen by ring]
    · intro s'; exact False.elim (hj1 s'.property)
  have hUnary := bmTapUnaryBundle_computesInTime K p
  dsimp only at hUnary
  rw [hq_def, hpC_def, hpW_def, hm1_def] at hUnary
  have pUnary := StageEval.const (S := St) hUnary
  have hCtx := bmTapCtxFromUnaryWith_computesInTime hmul K p hK
  dsimp only at hCtx
  rw [hq_def, hpC_def, hpW_def, hm1_def] at hCtx
  have pCtx := StageEval.const (S := St) hCtx
  have pTabRows := StageEval.tabulateSigned (S := St) (emitM := bmTapRowEmitWith bmMul)
    (uCtx := uOuterCtx) (W := fun _ => W) (N := fun _ => t1)
    (encElem := fun _ => encList (encodeSignedWord W_out))
    (fn := fun _ j1 => if hj1 : j1 < t1 then
      (List.finRange winLen).map (fun k => tapFn ⟨j1, hj1⟩ ((k.val : ℤ) - (m1 : ℤ)))
      else [])
    (B := fun _ => B_row)
    (L_ctx := fun _ => 650 * W + 1300)
    (L_elem := fun _ => winLen * (4 * q + 14))
    (fun _ => hW_pos) (fun _ => ht1_lt_W) hemitRow
    (fun _ => hlen_outerCtx)
    (fun _ j1 hj1 => by
      rw [dif_pos hj1]
      exact hRowLen ⟨j1, hj1⟩)
  have hall := StageEval.congr_out
    (v2 := fun _ => encList (encList (encodeSignedWord (q + 2)))
      ((List.finRange (t1Ell K)).map (fun j1 =>
        (List.finRange (2 * m1 + 1)).map (fun k => tapFn j1 ((k.val : ℤ) - (m1 : ℤ))))))
    (StageEval.seq pUnary (StageEval.seq pCtx pTabRows))
    (fun _ => by
      congr 1
      rw [List.map_congr_left]
      intro j1 _
      exact dif_pos j1.isLt)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  clear hemitRow hUnary pUnary hCtx pCtx pTabRows hall
  refine ⟨t, ?_, hcomp⟩
  clear hcomp hRowLen htapFn
  dsimp (config := { zeta := false }) only [uOuterCtx, id] at ht hlen_outerCtx
  simp (config := { zeta := false }) only [length_encDepPair, length_encUnary] at ht hlen_outerCtx
  change (encTapEntryCtx W W_out N_s N_e q q_l2 q_tot (t1 : ℤ) (m1 : ℤ) piFixed θDen gDen).length ≤
    320 * W + 600 at hlen_tapCtx
  generalize (encTapEntryCtx W W_out N_s N_e q q_l2 q_tot (t1 : ℤ) (m1 : ℤ) piFixed θDen gDen).length =
    lenTapCtx at ht hlen_tapCtx hlen_outerCtx
  clear uOuterCtx tapCtx piFixed l2Fixed θDen gDen St
  have hmW : mulTime W ≤ scaledSubMulCost mulTime q := le_scaledSubMulCost_thousand mulTime q
  have hB1 :
      (N_s + N_e + 14) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) ≤
      (130 * 6000000000) * S_term :=
    mul_le_scheduleSeriesTerms (by clear ht; dsimp only [N_s, N_e, B_sinc, B_exp, S]; omega)
      (by clear ht; dsimp only [W]; nlinarith)
  have hB2 :
      16 * mulTime W + 45000 * W * W + 3050000 * W + 4100000 + 2100000 * W + 3800000 ≤
      50000000000 * S_term :=
    quad_le_scheduleSeriesTerms (by clear ht; dsimp only [W]; nlinarith)
  have hBelem_le : B_elem + 2100000 * W + 3800000 ≤ 830000000000 * S_term := by
    dsimp only [B_elem]; linarith only [hB1, hB2]
  have hBrow_le :
      B_row + 1000 * W + 100 * (650 * W + 1300) + 50 * (winLen * (4 * q + 14)) + 2500 + 60 ≤
      830000000000 * (winLen * S_term) := by
    have h1 :
        1000 * W + 100 * (650 * W + 1300) + 2500 + 60 ≤
        winLen * (100000 * W + 200000) := by
      have : 1000 * W + 100 * (650 * W + 1300) + 2500 + 60 ≤ 100000 * W + 200000 := by
        dsimp only [W]; linarith only
      exact le_trans this (Nat.le_mul_of_pos_left _ hwin_pos)
    have h2 : 50 * (winLen * (4 * q + 14)) ≤ winLen * (100000 * W) := by
      have : 50 * (4 * q + 14) ≤ 100000 * W := by dsimp only [W]; linarith only [hq_eq]
      calc 50 * (winLen * (4 * q + 14))
          = winLen * (50 * (4 * q + 14)) := by ring
        _ ≤ winLen * (100000 * W) := Nat.mul_le_mul_left winLen this
    have h3 : B_row + 1000 * W + 100 * (650 * W + 1300) + 50 * (winLen * (4 * q + 14)) + 2500 + 60 ≤
        winLen * (B_elem + 2100000 * W + 3800000) := by
      dsimp only [B_row]
      linarith only [h1, h2,
                show winLen * (B_elem + 1866000 * W + 3530000) +
                  winLen * (100000 * W + 200000) + winLen * (100000 * W) ≤
                  winLen * (B_elem + 2100000 * W + 3800000) by
                  have : B_elem + 1866000 * W + 3530000 + (100000 * W + 200000) + 100000 * W ≤
                    B_elem + 2100000 * W + 3800000 := by linarith only
                  calc winLen * (B_elem + 1866000 * W + 3530000) +
                      winLen * (100000 * W + 200000) + winLen * (100000 * W)
                      = winLen * (B_elem + 1866000 * W + 3530000 + (100000 * W + 200000) + 100000 * W) := by ring
                    _ ≤ winLen * (B_elem + 2100000 * W + 3800000) := Nat.mul_le_mul_left winLen this]
    have hm := Nat.mul_le_mul_left winLen hBelem_le
    linarith only [h3, hm, show winLen * (830000000000 * S_term) = 830000000000 * (winLen * S_term) by ring]
  have ht1_mul :
      t1 * (B_row + 1000 * W + 100 * (650 * W + 1300) + 50 * (winLen * (4 * q + 14)) + 2500) +
      50 * t1 + 10 * t1 ≤
      830000000000 * ((t1 * winLen) * S_term) := by
    have hm := Nat.mul_le_mul_left t1 hBrow_le
    linarith only [hm,
              show t1 * (830000000000 * (winLen * S_term)) =
                830000000000 * ((t1 * winLen) * S_term) by ring,
              show t1 * (B_row + 1000 * W + 100 * (650 * W + 1300) +
                50 * (winLen * (4 * q + 14)) + 2500 + 60) =
                t1 * (B_row + 1000 * W + 100 * (650 * W + 1300) +
                50 * (winLen * (4 * q + 14)) + 2500) + 50 * t1 + 10 * t1 by ring]
  clear hB1 hB2 hBelem_le hBrow_le
  have hctx1 :
      (S + 4) * (1250 * W * W + 400000 * W + 1000000) ≤ (6 * 1300000000) * S_term :=
    mul_le_scheduleSeriesTerms (by clear ht ht1_mul; dsimp only [S]; omega)
      (by clear ht ht1_mul; dsimp only [W]; nlinarith)
  have hctx2 :
      10 * mulTime W + 3000 * W * W + 10000000 * W + 10000000 +
      2500 * (650 * W + 1300) + 10000 * W + 30000 + 500000000 * q + 500000000 ≤
      5000000000 * S_term :=
    quad_le_scheduleSeriesTerms (by clear ht ht1_mul hctx1; dsimp only [W]; nlinarith)
  have hq_12r : q ≤ 12 * r := by
    rw [← hq_def, ← hr_def]
    exact qChildEll_le_twelve_mul_rEll_of_internal hleaf hK
  have hcube := cube_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q)
  have hq4_le : 5000 * q * q * q * q ≤ 500 * (r * S_term) := by
    have h1 : 5000 * q * q * q * q = 5000 * q * (q * q * q) := by ring
    have h2 : 5000 * q ≤ 500 * r * 120 := by clear ht ht1_mul hctx1 hctx2 hcube; omega
    have h3 : (5000 * q) * (q * q * q) ≤ (500 * r * 120) * (q * q * q) :=
      Nat.mul_le_mul_right (q * q * q) h2
    have h4 : (500 * r) * (120 * (q * q * q)) ≤ (500 * r) * S_term :=
      Nat.mul_le_mul_left (500 * r) hcube
    linarith only [h1, h3, h4,
              show (500 * r * 120) * (q * q * q) = (500 * r) * (120 * (q * q * q)) by ring,
              show (500 * r) * S_term = 500 * (r * S_term) by ring]
  have hS_lin0 := linear_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q)
    (by clear ht ht1_mul hctx1 hctx2 hcube hq4_le; omega)
  have hK_S : K ≤ S_term := by
    clear ht ht1_mul hctx1 hctx2 hcube hq4_le; dsimp only [S_term] at hS_lin0 ⊢; omega
  have h1_S : 1 ≤ S_term := by
    clear ht ht1_mul hctx1 hctx2 hcube hq4_le; dsimp only [S_term] at hS_lin0 ⊢; omega
  have hKt1 : 100 * K * t1 + 500 * t1 + t1 * (4000 * W + 100000) ≤ 5000000 * ((t1 * winLen) * S_term) := by
    have h1 : 100 * K + 500 + (4000 * W + 100000) ≤ 5000000 * S_term := by
      clear ht ht1_mul hctx1 hctx2 hcube hq4_le
      dsimp only [W, S_term] at hS_lin0 ⊢; omega
    have h2 : 5000000 * S_term ≤ 5000000 * (winLen * S_term) :=
      Nat.mul_le_mul_left 5000000 (Nat.le_mul_of_pos_left S_term hwin_pos)
    have h3 := Nat.mul_le_mul_left t1 (le_trans h1 h2)
    linarith only [h3,
              show t1 * (100 * K + 500 + (4000 * W + 100000)) =
                100 * K * t1 + 500 * t1 + t1 * (4000 * W + 100000) by ring,
              show t1 * (5000000 * (winLen * S_term)) = 5000000 * ((t1 * winLen) * S_term) by ring]
  have hS_tw : S_term ≤ (t1 * winLen) * S_term :=
    Nat.le_mul_of_pos_left S_term (Nat.mul_pos ht1_pos hwin_pos)
  have hcomb_tw_r :
      (t1 * winLen) * S_term + r * S_term = (t1 * winLen + r) * S_term := by ring
  change t ≤ 1000000000000 * ((t1 * winLen + r) * S_term)
  generalize (B_row : ℕ) = Brow0 at ht ht1_mul
  generalize (S_term : ℕ) = Sterm0 at ht1_mul hctx1 hctx2 hq4_le hK_S h1_S hKt1 hS_tw hcomb_tw_r ⊢
  clear B_row B_elem S_term hcube hS_lin0
  dsimp only [t1, winLen, W, W_out, S, q_pi, q_l2, B_sinc, N_s, q_accs,
    B_exp, N_e, q_acce, q_tot] at ht hlen_tapCtx hlen_outerCtx ht1_mul hctx1 hctx2 hq4_le hKt1 hS_tw hcomb_tw_r h1_S ⊢
  omega

/-! ### 4.3 Passband Weight Mantissa Tables (`bmNodeGHatTablesWith`) -/

/-- Every entry produced by `computeGHatMantissaFixed K p yNum (rEll K)` for `0 ≤ yNum ≤ rEll K`
fits in `qChildEll K p + 2` signed bits (and hence in `10 * qChildEll K p` signed bits). -/
theorem fitsSignedWord_computeGHatMantissaFixed (K p : ℕ) (yNum : ℤ)
    (hy0 : 0 ≤ yNum) (hyr : yNum ≤ (rEll K : ℤ)) :
    FitsSignedWord (qChildEll K p + 2) (computeGHatMantissaFixed K p yNum (rEll K)) := by
  unfold computeGHatMantissaFixed
  set r := rEll K
  set q := qChildEll K p
  have hr_pos : 0 < r := rEll_pos K
  rw [computeGHatMantissaFixedWithMul_eq_computeGHatMantissa K p yNum hr_pos]
  set yRat : ℚ := (yNum : ℚ) / (r : ℚ)
  have hr_q : (0 : ℚ) < (r : ℚ) := Nat.cast_pos.mpr hr_pos
  have hy0_q : 0 ≤ yRat := div_nonneg (by exact_mod_cast hy0) hr_q.le
  have hy1_q : yRat ≤ 1 := (div_le_one hr_q).mpr (by exact_mod_cast hyr)
  have hnn : 0 ≤ computeGHatMantissa K p yRat := computeGHatMantissa_nonneg K p yRat
  have herr := abs_computeGHatMantissa_sub_gHat_le K p hy0_q hy1_q
  have hg_le1 : gHat (alphaEll K p) (yRat : ℝ) ≤ 1 := gHat_le_one _ _
  have h2q_le1 : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hval_lt : (computeGHatMantissa K p yRat : ℝ) * (2 : ℝ) ^ (-(q : ℤ)) < 2 := by
    have h1 := (abs_le.mp herr).2
    linarith
  have hmul : (computeGHatMantissa K p yRat : ℝ) < (2 : ℝ) ^ (q + 2 : ℕ) := by
    have h2 : (computeGHatMantissa K p yRat : ℝ) =
        ((computeGHatMantissa K p yRat : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * (2 : ℝ) ^ (q : ℤ) := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num), neg_add_cancel, zpow_zero, mul_one]
    have h3 : ((computeGHatMantissa K p yRat : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) * (2 : ℝ) ^ (q : ℤ) <
        2 * (2 : ℝ) ^ (q : ℤ) :=
      mul_lt_mul_of_pos_right hval_lt (zpow_pos (by norm_num) _)
    have h4 : (2 : ℝ) * (2 : ℝ) ^ (q : ℤ) ≤ (2 : ℝ) ^ (q + 2 : ℕ) := by
      rw [zpow_natCast]
      have : (2 : ℝ) * (2 : ℝ) ^ q = (2 : ℝ) ^ (q + 1) := by ring
      rw [this]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [fitsSignedWord_iff_abs_lt, abs_of_nonneg hnn]
  exact_mod_cast hmul

theorem FitsSignedWord.approxSqrtFixed {w : ℕ} {x : ℤ} (k : ℕ) (hx : FitsSignedWord w x) :
    FitsSignedWord w (IntMul.approxSqrtFixed k x) := by
  rw [fitsSignedWord_iff_natAbs_lt]
  unfold IntMul.approxSqrtFixed
  rw [Int.natAbs_natCast]
  have hm_lt : (max 0 x).toNat < 2 ^ w := by
    rcases lt_or_ge x 0 with hneg | hnn
    · rw [max_eq_left (le_of_lt hneg)]; exact Nat.two_pow_pos w
    · have hto : x.toNat = x.natAbs := by omega
      rw [max_eq_right hnn, hto]
      exact (fitsSignedWord_iff_natAbs_lt w x).mp hx
  exact lt_of_le_of_lt (le_trans (Nat.sqrt_le_self _) (Nat.div_le_self _ _)) hm_lt

theorem FitsSignedWord.min {w : ℕ} {a b : ℤ} (ha : FitsSignedWord w a) (hb : FitsSignedWord w b) :
    FitsSignedWord w (Min.min a b) := by
  rcases min_choice a b with h | h <;> rwa [h]

theorem FitsSignedWord.max {w : ℕ} {a b : ℤ} (ha : FitsSignedWord w a) (hb : FitsSignedWord w b) :
    FitsSignedWord w (Max.max a b) := by
  rcases max_choice a b with h | h <;> rwa [h]

/-- Same-width fixed-point square root wrapper: consumes `(sh, x_s)` where `x_s = encodeSignedWord W x`
and emits `encodeSignedWord W (approxSqrtFixed sh x)`. -/
def bmApproxSqrtSame : BitMachine :=
  let bmSh := bmFst
  let bmX := bmSnd
  let bmW := bmSeq bmX bmSignedWidth
  bmSeq (bmFanout (bmFanout bmW (bmFanout bmW bmSh)) bmX) bmApproxSqrtFixed

theorem bmApproxSqrtSame_computesInTime (W sh : ℕ) (x : ℤ)
    (hx : FitsSignedWord W x) (_hout : FitsSignedWord W (approxSqrtFixed sh x))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 40 * W * W + 15000 * W + 6000 * sh + 30000,
      bmApproxSqrtSame.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary (encodeSignedWord W) (sh, x)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W (approxSqrtFixed sh x)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := encDepPair (fun _ => encUnary sh) (fun _ => encodeSignedWord W x)
  have pSh := StageEval.fst (fun _ : S => encUnary sh) (fun _ => encodeSignedWord W x)
  have pX := StageEval.snd (fun _ : S => encUnary sh) (fun _ => encodeSignedWord W x)
  have pW := StageEval.seq pX (StageEval.of_computesStageLe (bmSignedWidth_computesStageLe W) (fun _ => x))
  have h_out : (approxSqrtFixed sh x).natAbs < 2 ^ W :=
    (fitsSignedWord_iff_natAbs_lt W _).mp (hx.approxSqrtFixed sh)
  have hm_lt : (max 0 x).toNat < 2 ^ W := by
    rcases lt_or_ge x 0 with hneg | hnn
    · rw [max_eq_left (le_of_lt hneg)]; exact Nat.two_pow_pos W
    · have hto : x.toNat = x.natAbs := by omega
      rw [max_eq_right hnn, hto]
      exact (fitsSignedWord_iff_natAbs_lt W x).mp hx
  have h_lt4w : (max 0 x).toNat / 2 ^ sh < 4 ^ W :=
    lt_of_le_of_lt (Nat.div_le_self _ _)
      (lt_of_lt_of_le hm_lt (Nat.pow_le_pow_left (by decide) W))
  have pSq := StageEval.const (S := S) (bmApproxSqrtFixed_computesInTime W W W sh x hx h_lt4w h_out)
  have hall := StageEval.seq (StageEval.fanout (StageEval.fanout pW (StageEval.fanout pW pSh)) pX) pSq
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  have hW_sq : 30 * W * W ≤ 40 * W * W := by nlinarith
  dsimp only [uIn, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  exact ⟨t, by linarith only [ht, hW_sq], hcomp⟩

/-- Encoding of the precomputed unary parameter bundle for `bmNodeGHatTablesWith`:
`(((W, W_out), (N_erf, Sq)), (((S, twoS), (cBound, fourPW)), ((sh_c, sh_pi), (q_za, r))))`. -/
def encGHatUnaryBundle (W W_out N_erf Sq S twoS cBound fourPW sh_c sh_pi q_za r : ℕ) :
    List Bool :=
  encPair
    (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
    (encPair
      (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
      (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))
    (((W, W_out), (N_erf, Sq)), (((S, twoS), (cBound, fourPW)), ((sh_c, sh_pi), (q_za, r))))

@[simp]
theorem length_encGHatUnaryBundle
    (W W_out N_erf Sq S twoS cBound fourPW sh_c sh_pi q_za r : ℕ) :
    (encGHatUnaryBundle W W_out N_erf Sq S twoS cBound fourPW sh_c sh_pi q_za r).length =
      2 * (2 * (2 * W + 2 * W_out + 4) + 2 * (2 * N_erf + 2 * Sq + 4) + 4) +
      2 * (2 * (2 * (2 * S + 2 * twoS + 4) + 2 * (2 * cBound + 2 * fourPW + 4) + 4) +
        2 * (2 * (2 * sh_c + 2 * sh_pi + 4) + 2 * (2 * q_za + 2 * r + 4) + 4) + 4) + 4 := by
  simp [encGHatUnaryBundle]

/-- Unary parameter stage for `bmNodeGHatTablesWith`: consumes `(K, p)` on `kIO` and emits
`encGHatUnaryBundle`. -/
def bmGHatUnaryBundle : BitMachine :=
  let bmK := bmFst
  let bmQ := bmQChildEll
  let bmPW := bmPWorkEll
  let bmR := bmSeq bmK bmREll
  let bmW := bmSeq (bmFanout (bmUnaryConst 1000) bmQ) bmUnaryMul
  let bmWOut := bmSeq (bmFanout (bmUnaryConst 10) bmQ) bmUnaryMul
  let bmTwoPW := bmSeq bmPW bmUnaryDouble
  let bmFourPW := bmSeq bmTwoPW bmUnaryDouble
  let bmQ2PW := bmSeq (bmFanout bmQ bmTwoPW) bmUnaryAdd
  let bmS := bmSeq (bmFanout bmQ2PW (bmUnaryConst 20)) bmUnaryAdd
  let bmTwoS := bmSeq bmS bmUnaryDouble
  let bmSq := bmSeq (bmFanout bmS bmQ) bmUnaryAdd
  let bmThreePW := bmSeq (bmFanout (bmUnaryConst 3) bmPW) bmUnaryMul
  let bmCBound := bmSeq (bmSeq bmThreePW bmUnarySqrt) bmUnarySucc
  let bmBErf := bmSeq bmCBound bmUnaryDouble
  let bmBErfSq := bmSeq (bmFanout bmBErf bmBErf) bmUnaryMul
  let bmFourBErfSq := bmSeq (bmSeq bmBErfSq bmUnaryDouble) bmUnaryDouble
  let bmSBErf := bmSeq (bmFanout bmS bmBErf) bmUnaryAdd
  let bmNerf := bmSeq (bmSeq (bmFanout bmFourBErfSq bmSBErf) bmUnaryAdd) bmUnarySucc
  let bmM := bmSeq (bmFanout bmNerf (bmUnaryConst 6)) bmUnaryAdd
  let bmFourM := bmSeq (bmSeq bmM bmUnaryDouble) bmUnaryDouble
  let bmQZa := bmSeq (bmFanout bmFourM (bmUnaryConst 6)) bmUnaryAdd
  let bmShC := bmSeq (bmSeq bmTwoS bmUnarySucc) bmUnarySucc
  let bmSixS := bmSeq (bmFanout (bmUnaryConst 6) bmS) bmUnaryMul
  let bmShPi := bmSeq (bmFanout bmSixS (bmUnaryConst 18)) bmUnaryAdd
  bmFanout
    (bmFanout (bmFanout bmW bmWOut) (bmFanout bmNerf bmSq))
    (bmFanout
      (bmFanout (bmFanout bmS bmTwoS) (bmFanout bmCBound bmFourPW))
      (bmFanout (bmFanout bmShC bmShPi) (bmFanout bmQZa bmR)))

set_option maxHeartbeats 800000 in
theorem bmGHatUnaryBundle_computesInTime (K p : ℕ) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let pW := pWorkEll K p
    let r := rEll K
    let W := 1000 * q
    let W_out := 10 * q
    let S := q + 2 * pW + 20
    let cBound := Nat.sqrt (3 * pW) + 1
    let B_erf := 2 * cBound
    let N_erf := 4 * B_erf ^ 2 + (S + B_erf) + 1
    let M := N_erf + 6
    let q_z := M
    let q_acc := 3 * M + 6
    ∃ t ≤ 100 * (K + 1) * r + 500 * r + 50000 * (q * q * q) + 600000000 * (q * q) + 500000000,
      bmGHatUnaryBundle.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (K, p)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encGHatUnaryBundle W W_out N_erf (S + q) S (2 * S) cBound (4 * pW)
            (2 * S + 2) (6 * S + 18) (q_z + q_acc) r))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro q pW r W W_out S cBound B_erf N_erf M q_z q_acc
  let St := Unit
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hpW_eq : pW = p + K + 6 := rfl
  let uK : St → List Bool := fun _ => encUnary K
  let uP : St → List Bool := fun _ => encUnary p
  let uIn : St → List Bool := encDepPair uK uP
  have pK := StageEval.fst uK uP
  have pQ := StageEval.of_computesStageLe bmQChildEll_computesStageLe (fun _ : St => (K, p))
  have pPW := StageEval.of_computesStageLe bmPWorkEll_computesStageLe (fun _ : St => (K, p))
  have pR := StageEval.seq pK
    (StageEval.of_computesStageLe bmREll_computesStageLe (fun _ : St => K))
  have pWidth := StageEval.seq (StageEval.fanout (StageEval.unaryConst 1000 uIn) pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (1000, q)))
  have pWOut := StageEval.seq (StageEval.fanout (StageEval.unaryConst 10 uIn) pQ)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (10, q)))
  have pTwoPW := StageEval.seq pPW
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => pW))
  have pFourPW := StageEval.congr_out (v2 := fun _ => encUnary (4 * pW))
    (StageEval.seq pTwoPW
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * pW)))
    (fun _ => congrArg encUnary (by omega))
  have pQ2PW := StageEval.seq (StageEval.fanout pQ pTwoPW)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (q, 2 * pW)))
  have pS := StageEval.seq (StageEval.fanout pQ2PW (StageEval.unaryConst 20 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (q + 2 * pW, 20)))
  have pTwoS := StageEval.seq pS
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => S))
  have pSq := StageEval.seq (StageEval.fanout pS pQ)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (S, q)))
  have pThreePW := StageEval.seq (StageEval.fanout (StageEval.unaryConst 3 uIn) pPW)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (3, pW)))
  have pSqrt3PW := StageEval.seq pThreePW
    (StageEval.of_computesStageLe bmUnarySqrt_computesStageLe (fun _ : St => 3 * pW))
  have pCBound := StageEval.seq pSqrt3PW
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => Nat.sqrt (3 * pW)))
  have pBErf := StageEval.seq pCBound
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => cBound))
  have pBErfSq := StageEval.seq (StageEval.fanout pBErf pBErf)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (B_erf, B_erf)))
  have p2BErfSq := StageEval.seq pBErfSq
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => B_erf * B_erf))
  have pFourBErfSq := StageEval.congr_out (v2 := fun _ => encUnary (4 * B_erf ^ 2))
    (StageEval.seq p2BErfSq
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * (B_erf * B_erf))))
    (fun _ => congrArg encUnary (by ring))
  have pSBErf := StageEval.seq (StageEval.fanout pS pBErf)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (S, B_erf)))
  have pNerfPre := StageEval.seq (StageEval.fanout pFourBErfSq pSBErf)
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (4 * B_erf ^ 2, S + B_erf)))
  have pNerf := StageEval.seq pNerfPre
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => 4 * B_erf ^ 2 + (S + B_erf)))
  have pM := StageEval.seq (StageEval.fanout pNerf (StageEval.unaryConst 6 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (N_erf, 6)))
  have p2M := StageEval.seq pM
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => M))
  have pFourM := StageEval.congr_out (v2 := fun _ => encUnary (4 * M))
    (StageEval.seq p2M
      (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : St => 2 * M)))
    (fun _ => congrArg encUnary (by omega))
  have pQZa := StageEval.congr_out (v2 := fun _ => encUnary (q_z + q_acc))
    (StageEval.seq (StageEval.fanout pFourM (StageEval.unaryConst 6 uIn))
      (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (4 * M, 6))))
    (fun _ => congrArg encUnary (by dsimp [q_z, q_acc]; omega))
  have pShC1 := StageEval.seq pTwoS
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => 2 * S))
  have pShC := StageEval.seq pShC1
    (StageEval.of_computesStageLe bmUnarySucc_computesStageLe (fun _ : St => 2 * S + 1))
  have pSixS := StageEval.seq (StageEval.fanout (StageEval.unaryConst 6 uIn) pS)
    (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : St => (6, S)))
  have pShPi := StageEval.seq (StageEval.fanout pSixS (StageEval.unaryConst 18 uIn))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : St => (6 * S, 18)))
  have pLeft := StageEval.fanout (StageEval.fanout pWidth pWOut) (StageEval.fanout pNerf pSq)
  have pR1 := StageEval.fanout (StageEval.fanout pS pTwoS) (StageEval.fanout pCBound pFourPW)
  have pR2 := StageEval.fanout (StageEval.fanout pShC pShPi) (StageEval.fanout pQZa pR)
  have hall := StageEval.fanout pLeft (StageEval.fanout pR1 pR2)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  clear pK pQ pPW pR pWidth pWOut pTwoPW pFourPW pQ2PW pS pTwoS pSq pThreePW pSqrt3PW
    pCBound pBErf pBErfSq p2BErfSq pFourBErfSq pSBErf pNerfPre pNerf pM p2M pFourM
    pQZa pShC1 pShC pSixS pShPi pLeft pR1 pR2 hall
  have hsqrt_sq : Nat.sqrt (3 * pW) * Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le (3 * pW)
  have hsqrt_le : Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le_self (3 * pW)
  have hcBound_le : cBound ≤ 3 * q := by dsimp [cBound]; omega
  have hBerf_le : B_erf ≤ 6 * q := by dsimp [B_erf]; omega
  have hBerf_sq : B_erf ^ 2 ≤ 36 * pW + 4 := by
    change (2 * (Nat.sqrt (3 * pW) + 1)) ^ 2 ≤ 36 * pW + 4
    nlinarith only [hsqrt_sq, hsqrt_le]
  have hBerf_mul : B_erf * B_erf ≤ 36 * pW + 4 := by
    change (2 * (Nat.sqrt (3 * pW) + 1)) * (2 * (Nat.sqrt (3 * pW) + 1)) ≤ 36 * pW + 4
    nlinarith only [hsqrt_sq, hsqrt_le]
  have hq1 : 1 ≤ q := by omega
  have hpW_q : pW ≤ q := by omega
  have h_l : 1000 * (3 * pW) * (3 * pW) ≤ 9000 * (q * q) := by
    calc 1000 * (3 * pW) * (3 * pW) = 9000 * (pW * pW) := by ring
      _ ≤ 9000 * (q * q) := Nat.mul_le_mul_left 9000 (Nat.mul_le_mul hpW_q hpW_q)
  have h_m : 40 * B_erf * B_erf * B_erf ≤ 8640 * (q * q * q) := by
    calc 40 * B_erf * B_erf * B_erf = 40 * (B_erf * B_erf * B_erf) := by ring
      _ ≤ 40 * ((6 * q) * (6 * q) * (6 * q)) :=
        Nat.mul_le_mul_left 40 (Nat.mul_le_mul (Nat.mul_le_mul hBerf_le hBerf_le) hBerf_le)
      _ = 8640 * (q * q * q) := by ring
  have h_n : 80 * B_erf * B_erf ≤ 2880 * (q * q) := by
    calc 80 * B_erf * B_erf = 80 * (B_erf * B_erf) := by ring
      _ ≤ 80 * ((6 * q) * (6 * q)) := Nat.mul_le_mul_left 80 (Nat.mul_le_mul hBerf_le hBerf_le)
      _ = 2880 * (q * q) := by ring
  have h_s : 10 * (K + 1) * r ≤ 100 * (K + 1) * r := by
    calc 10 * (K + 1) * r = 10 * ((K + 1) * r) := by ring
      _ ≤ 100 * ((K + 1) * r) := Nat.mul_le_mul_right _ (by decide)
      _ = 100 * (K + 1) * r := by ring
  have h_q1_q2 : q ≤ q * q := Nat.le_mul_self q
  have h_q2_pos : 1 ≤ q * q := Nat.mul_le_mul hq1 hq1
  have h_q3_pos : 1 ≤ q * q * q := Nat.mul_le_mul h_q2_pos hq1
  have hW_def : W = 1000 * q := rfl
  have hWout_def : W_out = 10 * q := rfl
  have hS_def : S = q + 2 * pW + 20 := rfl
  have hcBound_def : cBound = Nat.sqrt (3 * pW) + 1 := rfl
  have hBerf_def : B_erf = 2 * cBound := rfl
  have hNerf_def : N_erf = 4 * B_erf ^ 2 + (S + B_erf) + 1 := rfl
  have hM_def : M = N_erf + 6 := rfl
  have hqz_def : q_z = M := rfl
  have hqacc_def : q_acc = 3 * M + 6 := rfl
  have hq_def : qChildEll K p = q := rfl
  have hpW_def : pWorkEll K p = pW := rfl
  have hr_def : rEll K = r := rfl
  dsimp (config := { zeta := false }) only [uIn, uK, uP, id, Prod.fst, Prod.snd] at ht hcomp ⊢
  simp (config := { zeta := false }) only [length_encDepPair, length_encPair, length_encUnary,
    hq_def, hpW_def, hr_def] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Context builder for `bmNodeGHatTablesWith`: consumes `encGHatUnaryBundle` on `kIO` and emits
`((ctxGHat, W), r)` where `ctxGHat = encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFixed zDen denOut`. -/
def bmGHatCtxFromUnaryWith (bmMul : BitMachine) : BitMachine :=
  let bmLeft := bmFst
  let bmRight := bmSnd
  let bmR1 := bmSeq bmRight bmFst
  let bmR2 := bmSeq bmRight bmSnd
  let bmW := bmSeq (bmSeq bmLeft bmFst) bmFst
  let bmS := bmSeq (bmSeq bmR1 bmFst) bmFst
  let bmTwoS := bmSeq (bmSeq bmR1 bmFst) bmSnd
  let bmCBound := bmSeq (bmSeq bmR1 bmSnd) bmFst
  let bmFourPW := bmSeq (bmSeq bmR1 bmSnd) bmSnd
  let bmShC := bmSeq (bmSeq bmR2 bmFst) bmFst
  let bmShPi := bmSeq (bmSeq bmR2 bmFst) bmSnd
  let bmQZa := bmSeq (bmSeq bmR2 bmSnd) bmFst
  let bmR := bmSeq (bmSeq bmR2 bmSnd) bmSnd
  let bmL2Fixed := bmSeq (bmFanout bmW bmTwoS) bmMaxApproxLogTwo
  let bmPi2SFixed := bmSeq (bmFanout bmW bmTwoS) bmApproxPi
  let bmRs := bmSeq (bmFanout bmW bmR) bmUnaryToSigned
  let bmCBoundS := bmSeq (bmFanout bmW bmCBound) bmUnaryToSigned
  let bmFourPWs := bmSeq (bmFanout bmW bmFourPW) bmUnaryToSigned
  let bmTwoPowS := bmSeq (bmFanout bmW bmS) bmSignedTwoPow
  let bmTwoPowQZa := bmSeq (bmFanout bmW bmQZa) bmSignedTwoPow
  let bmCRawArg := bmSeq (bmFanout bmFourPWs bmL2Fixed) (bmSignedMulSameWith bmMul)
  let bmCRawFixed := bmSeq (bmFanout bmShC bmCRawArg) bmApproxSqrtSame
  let bmCCap := bmSeq (bmFanout bmCBoundS bmTwoPowS) (bmSignedMulSameWith bmMul)
  let bmCFixed := bmSeq (bmFanout bmCCap bmCRawFixed) bmSignedMin
  let bmSqrtPiRaw := bmSeq (bmFanout bmShPi bmPi2SFixed) bmApproxSqrtSame
  let bmSqrtPiFixed := bmSeq (bmFanout bmTwoPowS bmSqrtPiRaw) bmSignedMax
  let bmTwoRs := bmSeq bmRs bmSignedDouble
  let bmZDen := bmSeq (bmFanout bmTwoRs bmTwoPowS) (bmSignedMulSameWith bmMul)
  let bmDenOut := bmSeq (bmFanout bmSqrtPiFixed bmTwoPowQZa) (bmSignedMulSameWith bmMul)
  let bmRightCtx := bmFanout (bmFanout bmRs bmCFixed) (bmFanout bmZDen bmDenOut)
  let bmGHatCtx := bmFanout bmLeft bmRightCtx
  bmFanout (bmFanout bmGHatCtx bmW) bmR

set_option maxHeartbeats 800000 in
theorem bmGHatCtxFromUnaryWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ) (hK : 2 ≤ K) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let pW := pWorkEll K p
    let r := rEll K
    let W := 1000 * q
    let W_out := 10 * q
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
    ∃ t ≤ (2 * S + 4) * (1250 * W * W + 400000 * W + 1000000) +
        10 * mulTime W + 3000 * W * W + 10000000 * W + r * (4000 * W + 100000) + 10000000,
      (bmGHatCtxFromUnaryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encGHatUnaryBundle W W_out N_erf (S + q) S (2 * S) cBound (4 * pW)
            (2 * S + 2) (6 * S + 18) (q_z + q_acc) r))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair id encUnary) encUnary
            ((encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFixed zDen denOut, W), r)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro q pW r W W_out S q_l2 l2Fixed cBound cRawFixed cFixed B_erf N_erf M q_z q_acc
    pi2SFixed sqrtPiRawFixed sqrtPiFixed zDen denOut
  obtain ⟨W0, hW0_def⟩ : ∃ x : ℕ, x = W := ⟨_, rfl⟩
  obtain ⟨fourPW, h4pW_def⟩ : ∃ x : ℕ, x = 4 * pW := ⟨_, rfl⟩
  obtain ⟨l2_0, hl2_def⟩ : ∃ x : ℤ, x = l2Fixed := ⟨_, rfl⟩
  obtain ⟨pi2S_0, hpi_def⟩ : ∃ x : ℤ, x = pi2SFixed := ⟨_, rfl⟩
  obtain ⟨cRaw0, hcRaw_def⟩ : ∃ x : ℤ, x = cRawFixed := ⟨_, rfl⟩
  obtain ⟨cFix0, hcFix_def⟩ : ∃ x : ℤ, x = cFixed := ⟨_, rfl⟩
  obtain ⟨spRaw0, hspRaw_def⟩ : ∃ x : ℤ, x = sqrtPiRawFixed := ⟨_, rfl⟩
  obtain ⟨spFix0, hspFix_def⟩ : ∃ x : ℤ, x = sqrtPiFixed := ⟨_, rfl⟩
  obtain ⟨zDen0, hzDen_def⟩ : ∃ x : ℤ, x = zDen := ⟨_, rfl⟩
  obtain ⟨denOut0, hdenOut_def⟩ : ∃ x : ℤ, x = denOut := ⟨_, rfl⟩
  rw [← hW0_def, ← h4pW_def, ← hcFix_def, ← hzDen_def, ← hdenOut_def]
  let St := Unit
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hpW_eq : pW = p + K + 6 := rfl
  have hW_eq : W0 = 1000 * q := hW0_def
  have hWout_def : W_out = 10 * q := rfl
  have hS_def : S = q + 2 * pW + 20 := rfl
  have hcBound_def : cBound = Nat.sqrt (3 * pW) + 1 := rfl
  have hBerf_def : B_erf = 2 * cBound := rfl
  have hNerf_def : N_erf = 4 * B_erf ^ 2 + (S + B_erf) + 1 := rfl
  have hM_def : M = N_erf + 6 := rfl
  have hqz_def : q_z = M := rfl
  have hqacc_def : q_acc = 3 * M + 6 := rfl
  have hr_le : r ≤ 2 ^ K := rEll_le_two_pow K
  have hl2_fits_small : FitsSignedWord (4 * S + 4) l2_0 := by
    rw [hl2_def]; exact fitsSignedWord_max_approxLogTwoFixed (2 * S) (by omega)
  have hpi2S_fits_small : FitsSignedWord (10 * S + 30) pi2S_0 := by
    rw [hpi_def]; exact fitsSignedWord_approxPiFixed (2 * S) (by omega)
  have hsqrtPiRaw_fits_small : FitsSignedWord (10 * S + 30) spRaw0 := by
    rw [hspRaw_def]
    exact (fitsSignedWord_approxPiFixed (2 * S) (by omega)).approxSqrtFixed (6 * S + 18)
  have hsqrtPiFixed_fits_small : FitsSignedWord (S + 3) spFix0 := by
    rw [hspFix_def]; exact fitsSignedWord_sqrtPiFixed S
  have hl2_eq : max ((2 : ℤ) ^ ((2 * S + (2 * S + 2)) - 1)) (approxLogTwoFixed (2 * S)) = l2_0 :=
    hl2_def.symm
  have hpi_eq : approxPiFixed (2 * S) = pi2S_0 := hpi_def.symm
  have hspRaw_eq : approxSqrtFixed (6 * S + 18) pi2S_0 = spRaw0 := by
    rw [hpi_def]; exact hspRaw_def.symm
  have hsp_eq : max ((2 : ℤ) ^ S) spRaw0 = spFix0 := by
    rw [hspRaw_def]; exact hspFix_def.symm
  have hzDen_eq : 2 * (r : ℤ) * (2 : ℤ) ^ S = zDen0 := hzDen_def.symm
  have hdenOut_eq : spFix0 * (2 : ℤ) ^ (q_z + q_acc) = denOut0 := by
    rw [hspFix_def]; exact hdenOut_def.symm
  have hcRaw_eq : approxSqrtFixed (2 * S + 2) ((fourPW : ℤ) * l2_0) = cRaw0 := by
    have h4pW_cast : (fourPW : ℤ) * l2_0 = 4 * (pW : ℤ) * l2Fixed := by
      rw [h4pW_def, hl2_def]
      push_cast
      ring
    exact (congrArg (approxSqrtFixed (2 * S + 2)) h4pW_cast).trans hcRaw_def.symm
  have hcFixed_eq : min ((cBound : ℤ) * (2 : ℤ) ^ S) cRaw0 = cFix0 := by
    rw [hcRaw_def]; exact hcFix_def.symm
  clear W l2Fixed pi2SFixed cRawFixed cFixed sqrtPiRawFixed sqrtPiFixed zDen denOut
    hW0_def hl2_def hpi_def hcRaw_def hcFix_def hspRaw_def hspFix_def hzDen_def hdenOut_def
  have hW_pos : 1 ≤ W0 := by omega
  have hr_pow_q : r ≤ 2 ^ q := hr_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hr_lt_q1 : r < 2 ^ (q + 1) :=
    lt_of_le_of_lt hr_pow_q (Nat.pow_lt_pow_right (by decide) (by omega))
  have hr_lt_W : r < 2 ^ W0 :=
    lt_of_lt_of_le hr_lt_q1 (Nat.pow_le_pow_right (by decide) (by omega))
  have hsqrt_sq : Nat.sqrt (3 * pW) * Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le (3 * pW)
  have hsqrt_le : Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le_self (3 * pW)
  have hcBound_le : cBound ≤ 3 * q := by omega
  have hBerf_le : B_erf ≤ 6 * q := by omega
  have hBerf_sq : B_erf ^ 2 ≤ 36 * pW + 4 := by
    rw [hBerf_def, hcBound_def]
    nlinarith only [hsqrt_sq, hsqrt_le]
  have hcBound_lt_q : cBound < 2 ^ q :=
    lt_of_le_of_lt (by omega : cBound ≤ 4 * q) (four_mul_lt_two_pow (by omega))
  have hcBound_lt_W : cBound < 2 ^ W0 :=
    lt_of_lt_of_le hcBound_lt_q (Nat.pow_le_pow_right (by decide) (by omega))
  have h4pW_lt_q : fourPW < 2 ^ q :=
    lt_of_le_of_lt (by omega : fourPW ≤ 4 * q) (four_mul_lt_two_pow (by omega))
  have h4pW_lt_W : fourPW < 2 ^ W0 :=
    lt_of_lt_of_le h4pW_lt_q (Nat.pow_le_pow_right (by decide) (by omega))
  have hS_lt_W : S < W0 := by omega
  have hqza_lt_W : q_z + q_acc < W0 := by omega
  have hpi_W : 5 * (2 * S) + 30 ≤ W0 := by omega
  have hl2_W : 2 * (2 * S) + 4 ≤ W0 := by omega
  have hr_fits_q : FitsSignedWord (q + 1) (r : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact hr_lt_q1
  have hr_fits : FitsSignedWord W0 (r : ℤ) := hr_fits_q.mono (by omega)
  have h2r_fits_q : FitsSignedWord (q + 2) (2 * (r : ℤ)) := by
    have : 2 * (r : ℤ) = (r : ℤ) + (r : ℤ) := by ring
    rw [this]; exact hr_fits_q.add hr_fits_q
  have h2r_fits : FitsSignedWord W0 (2 * (r : ℤ)) := h2r_fits_q.mono (by omega)
  have hcBound_fits_q : FitsSignedWord q (cBound : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact hcBound_lt_q
  have hcBound_fits : FitsSignedWord W0 (cBound : ℤ) := hcBound_fits_q.mono (by omega)
  have h4pW_fits_q : FitsSignedWord (q + 2) (fourPW : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact lt_of_lt_of_le h4pW_lt_q (Nat.pow_le_pow_right (by decide) (by omega))
  have h4pW_fits : FitsSignedWord W0 (fourPW : ℤ) := h4pW_fits_q.mono (by omega)
  have h2S_fits : FitsSignedWord W0 ((2 : ℤ) ^ S) :=
    (FitsSignedWord.two_pow S).mono (by omega)
  have h2qza_fits : FitsSignedWord W0 ((2 : ℤ) ^ (q_z + q_acc)) :=
    (FitsSignedWord.two_pow (q_z + q_acc)).mono (by omega)
  have hl2_fits : FitsSignedWord W0 l2_0 := hl2_fits_small.mono (by omega)
  have hcRawArg_fits_small := h4pW_fits_q.mul hl2_fits_small
  have hcRawArg_fits : FitsSignedWord W0 ((fourPW : ℤ) * l2_0) :=
    hcRawArg_fits_small.mono (by omega)
  have hcRaw_fits : FitsSignedWord W0 (approxSqrtFixed (2 * S + 2) ((fourPW : ℤ) * l2_0)) :=
    hcRawArg_fits.approxSqrtFixed (2 * S + 2)
  have hcRaw_fits' : FitsSignedWord W0 cRaw0 := by
    rw [← hcRaw_eq]; exact hcRaw_fits
  have hcCap_fits_small := hcBound_fits_q.mul_two_pow S
  have hcCap_fits : FitsSignedWord W0 ((cBound : ℤ) * (2 : ℤ) ^ S) :=
    hcCap_fits_small.mono (by omega)
  have hpi2S_fits : FitsSignedWord W0 pi2S_0 := hpi2S_fits_small.mono (by omega)
  have hsqrtPiRaw_fits_expr : FitsSignedWord W0 (approxSqrtFixed (6 * S + 18) pi2S_0) :=
    hpi2S_fits.approxSqrtFixed (6 * S + 18)
  have hsqrtPiRaw_fits : FitsSignedWord W0 spRaw0 :=
    hsqrtPiRaw_fits_small.mono (by omega)
  have hsqrtPiFixed_fits : FitsSignedWord W0 spFix0 :=
    hsqrtPiFixed_fits_small.mono (by omega)
  have hzDen_fits_small := h2r_fits_q.mul_two_pow S
  have hzDen_fits_expr : FitsSignedWord W0 (2 * (r : ℤ) * (2 : ℤ) ^ S) :=
    hzDen_fits_small.mono (by omega)
  have hdenOut_fits_small := hsqrtPiFixed_fits_small.mul_two_pow (q_z + q_acc)
  have hdenOut_fits_expr : FitsSignedWord W0 (spFix0 * (2 : ℤ) ^ (q_z + q_acc)) :=
    hdenOut_fits_small.mono (by omega)
  let uL1 : St → List Bool := encDepPair (fun _ => encUnary W0) (fun _ => encUnary W_out)
  let uL2 : St → List Bool := encDepPair (fun _ => encUnary N_erf) (fun _ => encUnary (S + q))
  let uLeft : St → List Bool := encDepPair uL1 uL2
  let uR11 : St → List Bool := encDepPair (fun _ => encUnary S) (fun _ => encUnary (2 * S))
  let uR12 : St → List Bool := encDepPair (fun _ => encUnary cBound) (fun _ => encUnary fourPW)
  let uR1 : St → List Bool := encDepPair uR11 uR12
  let uR21 : St → List Bool := encDepPair (fun _ => encUnary (2 * S + 2)) (fun _ => encUnary (6 * S + 18))
  let uR22 : St → List Bool := encDepPair (fun _ => encUnary (q_z + q_acc)) (fun _ => encUnary r)
  let uR2 : St → List Bool := encDepPair uR21 uR22
  let uRight : St → List Bool := encDepPair uR1 uR2
  let uIn : St → List Bool := encDepPair uLeft uRight
  have pLeft := StageEval.fst uLeft uRight
  have pRight := StageEval.snd uLeft uRight
  have pR1 := StageEval.seq pRight (StageEval.fst uR1 uR2)
  have pR2 := StageEval.seq pRight (StageEval.snd uR1 uR2)
  have pWidth := StageEval.seq (StageEval.seq pLeft (StageEval.fst uL1 uL2))
    (StageEval.fst (fun _ : St => encUnary W0) (fun _ => encUnary W_out))
  have pR11 := StageEval.seq pR1 (StageEval.fst uR11 uR12)
  have pR12 := StageEval.seq pR1 (StageEval.snd uR11 uR12)
  have pS := StageEval.seq pR11
    (StageEval.fst (fun _ : St => encUnary S) (fun _ => encUnary (2 * S)))
  have pTwoS := StageEval.seq pR11
    (StageEval.snd (fun _ : St => encUnary S) (fun _ => encUnary (2 * S)))
  have pCBound := StageEval.seq pR12
    (StageEval.fst (fun _ : St => encUnary cBound) (fun _ => encUnary fourPW))
  have pFourPW := StageEval.seq pR12
    (StageEval.snd (fun _ : St => encUnary cBound) (fun _ => encUnary fourPW))
  have pR21 := StageEval.seq pR2 (StageEval.fst uR21 uR22)
  have pR22 := StageEval.seq pR2 (StageEval.snd uR21 uR22)
  have pShC := StageEval.seq pR21
    (StageEval.fst (fun _ : St => encUnary (2 * S + 2)) (fun _ => encUnary (6 * S + 18)))
  have pShPi := StageEval.seq pR21
    (StageEval.snd (fun _ : St => encUnary (2 * S + 2)) (fun _ => encUnary (6 * S + 18)))
  have pQZa := StageEval.seq pR22
    (StageEval.fst (fun _ : St => encUnary (q_z + q_acc)) (fun _ => encUnary r))
  have pR := StageEval.seq pR22
    (StageEval.snd (fun _ : St => encUnary (q_z + q_acc)) (fun _ => encUnary r))
  have pL2Fixed := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 l2_0)
    (StageEval.seq (StageEval.fanout pWidth pTwoS)
      (StageEval.const (S := St) (bmMaxApproxLogTwo_computesInTime W0 (2 * S) hl2_W)))
    (fun _ => congrArg (encodeSignedWord W0) hl2_eq)
  have pPi2SFixed := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 pi2S_0)
    (StageEval.seq (StageEval.fanout pWidth pTwoS)
      (StageEval.const (S := St) (bmApproxPi_computesInTime W0 (2 * S) hpi_W)))
    (fun _ => congrArg (encodeSignedWord W0) hpi_eq)
  have pRs := StageEval.seq (StageEval.fanout pWidth pR)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W0 r hW_pos hr_lt_W))
  have pCBoundS := StageEval.seq (StageEval.fanout pWidth pCBound)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W0 cBound hW_pos hcBound_lt_W))
  have pFourPWs := StageEval.seq (StageEval.fanout pWidth pFourPW)
    (StageEval.const (S := St) (bmUnaryToSigned_computesInTime W0 fourPW hW_pos h4pW_lt_W))
  have pTwoPowS := StageEval.seq (StageEval.fanout pWidth pS)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W0 S hW_pos hS_lt_W))
  have pTwoPowQZa := StageEval.seq (StageEval.fanout pWidth pQZa)
    (StageEval.const (S := St) (bmSignedTwoPow_computesInTime W0 (q_z + q_acc) hW_pos hqza_lt_W))
  have pCRawArg := StageEval.seq (StageEval.fanout pFourPWs pL2Fixed)
    (StageEval.signedMulSameWith hmul (fun _ => W0) (fun _ => (fourPW : ℤ)) (fun _ => l2_0)
      (fun _ => h4pW_fits) (fun _ => hl2_fits) (fun _ => hcRawArg_fits))
  have pCRawFixed := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 cRaw0)
    (StageEval.seq (StageEval.fanout pShC pCRawArg)
      (StageEval.const (S := St)
        (bmApproxSqrtSame_computesInTime W0 (2 * S + 2) ((fourPW : ℤ) * l2_0)
          hcRawArg_fits hcRaw_fits)))
    (fun _ => congrArg (encodeSignedWord W0) hcRaw_eq)
  have pCCap := StageEval.seq (StageEval.fanout pCBoundS pTwoPowS)
    (StageEval.signedMulSameWith hmul (fun _ => W0) (fun _ => (cBound : ℤ)) (fun _ => (2 : ℤ) ^ S)
      (fun _ => hcBound_fits) (fun _ => h2S_fits) (fun _ => hcCap_fits))
  have pCFixed := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 cFix0)
    (StageEval.seq (StageEval.fanout pCCap pCRawFixed)
      (StageEval.const (S := St)
        (bmSignedMin_computesInTime W0 ((cBound : ℤ) * (2 : ℤ) ^ S) cRaw0
          hcCap_fits hcRaw_fits')))
    (fun _ => congrArg (encodeSignedWord W0) hcFixed_eq)
  have pSqrtPiRaw := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 spRaw0)
    (StageEval.seq (StageEval.fanout pShPi pPi2SFixed)
      (StageEval.const (S := St)
        (bmApproxSqrtSame_computesInTime W0 (6 * S + 18) pi2S_0 hpi2S_fits
          hsqrtPiRaw_fits_expr)))
    (fun _ => congrArg (encodeSignedWord W0) hspRaw_eq)
  have pSqrtPiFixed := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 spFix0)
    (StageEval.seq (StageEval.fanout pTwoPowS pSqrtPiRaw)
      (StageEval.const (S := St)
        (bmSignedMax_computesInTime W0 ((2 : ℤ) ^ S) spRaw0
          h2S_fits hsqrtPiRaw_fits)))
    (fun _ => congrArg (encodeSignedWord W0) hsp_eq)
  have pTwoRs := StageEval.seq pRs
    (StageEval.const (S := St) (bmSignedDouble_computesInTime W0 (r : ℤ) hr_fits h2r_fits))
  have pZDen := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 zDen0)
    (StageEval.seq (StageEval.fanout pTwoRs pTwoPowS)
      (StageEval.signedMulSameWith hmul (fun _ => W0) (fun _ => 2 * (r : ℤ)) (fun _ => (2 : ℤ) ^ S)
        (fun _ => h2r_fits) (fun _ => h2S_fits) (fun _ => hzDen_fits_expr)))
    (fun _ => congrArg (encodeSignedWord W0) hzDen_eq)
  have pDenOut := StageEval.congr_out
    (v2 := fun _ => encodeSignedWord W0 denOut0)
    (StageEval.seq (StageEval.fanout pSqrtPiFixed pTwoPowQZa)
      (StageEval.signedMulSameWith hmul (fun _ => W0)
        (fun _ => spFix0) (fun _ => (2 : ℤ) ^ (q_z + q_acc))
        (fun _ => hsqrtPiFixed_fits) (fun _ => h2qza_fits) (fun _ => hdenOut_fits_expr)))
    (fun _ => congrArg (encodeSignedWord W0) hdenOut_eq)
  have pRightCtx := StageEval.fanout (StageEval.fanout pRs pCFixed) (StageEval.fanout pZDen pDenOut)
  have pGHatCtx := StageEval.fanout pLeft pRightCtx
  have hall := StageEval.fanout (StageEval.fanout pGHatCtx pWidth) pR
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  clear pLeft pRight pR1 pR2 pWidth pR11 pR12 pS pTwoS pCBound pFourPW pR21 pR22
    pShC pShPi pQZa pR pL2Fixed pPi2SFixed pRs pCBoundS pFourPWs pTwoPowS pTwoPowQZa
    pCRawArg pCRawFixed pCCap pCFixed pSqrtPiRaw pSqrtPiFixed pTwoRs pZDen pDenOut
    pRightCtx pGHatCtx hall
  have hpi_l2_comb :
      (2 * S + 4) * (1000 * W0 * W0 + 320000 * W0 + 800000) +
      (2 * S + 2) * (250 * W0 * W0 + 80000 * W0 + 200000) ≤
      (2 * S + 4) * (1250 * W0 * W0 + 400000 * W0 + 1000000) := by
    have h1 : (2 * S + 2) * (250 * W0 * W0 + 80000 * W0 + 200000) ≤
        (2 * S + 4) * (250 * W0 * W0 + 80000 * W0 + 200000) :=
      Nat.mul_le_mul_right _ (by linarith only)
    have h2 :
        (2 * S + 4) * (1000 * W0 * W0 + 320000 * W0 + 800000) +
        (2 * S + 4) * (250 * W0 * W0 + 80000 * W0 + 200000) =
        (2 * S + 4) * (1250 * W0 * W0 + 400000 * W0 + 1000000) := by ring
    linarith only [h1, h2]
  have hcBound_W : cBound * (800 * W0 + 2010) ≤ 800 * W0 * W0 + 2010 * W0 := by
    have h1 : cBound ≤ W0 := by
      have hs := Nat.sqrt_le_self (3 * pW)
      linarith only [hcBound_def, hs, hpW_eq, hq_eq, hW_eq]
    have h2 := Nat.mul_le_mul_right (800 * W0 + 2010) h1
    have hr : W0 * (800 * W0 + 2010) = 800 * W0 * W0 + 2010 * W0 := by ring
    linarith only [h2, hr]
  have h4pW_W : fourPW * (800 * W0 + 2010) ≤ 800 * W0 * W0 + 2010 * W0 := by
    have h1 : fourPW ≤ W0 := by linarith only [h4pW_def, hpW_eq, hq_eq, hW_eq]
    have h2 := Nat.mul_le_mul_right (800 * W0 + 2010) h1
    have hr : W0 * (800 * W0 + 2010) = 800 * W0 * W0 + 2010 * W0 := by ring
    linarith only [h2, hr]
  have hr_W : 2 * (r * (800 * W0 + 2010)) + 10000 * r ≤ r * (4000 * W0 + 100000) := by
    have h1 : 1600 * W0 + 14020 ≤ 4000 * W0 + 100000 := by linarith only
    have h2 := Nat.mul_le_mul_left r h1
    have hr : 2 * (r * (800 * W0 + 2010)) + 10000 * r = r * (1600 * W0 + 14020) := by ring
    linarith only [h2, hr]
  have hW0_sq :
      600 * W0 * W0 + 800 * W0 * W0 + 800 * W0 * W0 + 40 * W0 * W0 + 40 * W0 * W0 ≤
      3000 * W0 * W0 := by
    have h1 := Nat.mul_le_mul_right W0 (by linarith only : 2280 * W0 ≤ 3000 * W0)
    have hr : 600 * W0 * W0 + 800 * W0 * W0 + 800 * W0 * W0 + 40 * W0 * W0 + 40 * W0 * W0 =
      2280 * W0 * W0 := by ring
    linarith only [h1, hr]
  dsimp (config := { zeta := false }) only
    [uIn, uLeft, uRight, uL1, uL2, uR1, uR2, uR11, uR12, uR21, uR22, id] at ht hcomp
  simp (config := { zeta := false }) only
    [length_encDepPair, length_encUnary, length_encodeSignedWord] at ht
  refine ⟨t, ?_, hcomp⟩
  clear hcomp uIn uLeft uRight uL1 uL2 uR1 uR2 uR11 uR12 uR21 uR22 St
    hl2_eq hpi_eq hspRaw_eq hsp_eq hzDen_eq hdenOut_eq hcRaw_eq hcFixed_eq
    hl2_fits_small hpi2S_fits_small hsqrtPiRaw_fits_small hsqrtPiFixed_fits_small
    hr_le hr_pow_q hr_lt_q1 hr_lt_W hsqrt_sq hsqrt_le
    hcBound_lt_q hcBound_lt_W h4pW_lt_q h4pW_lt_W
    hr_fits_q hr_fits h2r_fits_q h2r_fits hcBound_fits_q hcBound_fits h4pW_fits_q h4pW_fits
    h2S_fits h2qza_fits hl2_fits hcRawArg_fits_small hcRawArg_fits hcRaw_fits hcRaw_fits'
    hcCap_fits_small hcCap_fits hpi2S_fits hsqrtPiRaw_fits_expr hsqrtPiRaw_fits
    hsqrtPiFixed_fits hzDen_fits_small hzDen_fits_expr hdenOut_fits_small hdenOut_fits_expr
    l2_0 pi2S_0 cRaw0 cFix0 spRaw0 spFix0 zDen0 denOut0
  linarith

/-- Emitter for `c0Mantissa`: transforms `((ctxGHat, W), u2_s)` into `(ctxGHat, u2_s)` and calls
`bmGHatEntryWith bmMul`. -/
def bmC0EmitWith (bmMul : BitMachine) : BitMachine :=
  bmSeq (bmMapFst bmFst) (bmGHatEntryWith bmMul)

/-- Emitter for `c1Mantissa`: transforms `((ctxGHat, W), u2_s)` into `(ctxGHat, r_s - u2_s)` (where
`r_s` is extracted from `ctxGHat.2.1.1`) and calls `bmGHatEntryWith bmMul`. -/
def bmC1EmitWith (bmMul : BitMachine) : BitMachine :=
  let bmCtx := bmSeq bmFst bmFst
  let bmU2 := bmSnd
  let bmRs := bmSeq (bmSeq (bmSeq bmCtx bmSnd) bmFst) bmFst
  let bmDiff := bmSeq (bmFanout bmRs bmU2) bmSignedSub
  bmSeq (bmFanout bmCtx bmDiff) (bmGHatEntryWith bmMul)

/-- **Passband Weight Mantissa Tables Stage (`bmNodeGHatTablesWith bmMul`)**:
Consumes `(K, p)` on `kIO` and emits
`(encMantissaTable K p (computePassbandC0Mantissa K p), encMantissaTable K p (computePassbandC1Mantissa K p))`. -/
def bmNodeGHatTablesWith (bmMul : BitMachine) : BitMachine :=
  bmSeq bmGHatUnaryBundle
    (bmSeq (bmGHatCtxFromUnaryWith bmMul)
      (bmFanout
        (bmTabulateSigned (bmC0EmitWith bmMul))
        (bmTabulateSigned (bmC1EmitWith bmMul))))

theorem length_encMantissaTable_le (K p : ℕ) (tbl : Fin (rEll K) → ℤ) :
    (encMantissaTable K p tbl).length ≤ rEll K * (40 * qChildEll K p + 10) := by
  unfold encMantissaTable
  have h := StageEval.length_encList_le_of_forall_le (encodeSignedWord (10 * qChildEll K p))
    (20 * qChildEll K p + 2) ((List.finRange (rEll K)).map tbl)
    (fun z _ => by simp only [length_encodeSignedWord]; omega)
  rw [List.length_map, List.length_finRange] at h
  exact le_trans h (Nat.mul_le_mul_left _ (by omega))

theorem bmGHatUnaryBundle_computesInTime_gen
    (K p q pW r W W_out S cBound B_erf N_erf qza : ℕ)
    (hq : q = qChildEll K p) (hpW : pW = pWorkEll K p) (hr : r = rEll K)
    (hW : W = 1000 * q) (hW_out : W_out = 10 * q) (hS : S = q + 2 * pW + 20)
    (hcBound : cBound = Nat.sqrt (3 * pW) + 1) (hBerf : B_erf = 2 * cBound)
    (hNerf : N_erf = 4 * B_erf ^ 2 + (S + B_erf) + 1)
    (hqza : qza = (N_erf + 6) + (3 * (N_erf + 6) + 6))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 100 * (K + 1) * r + 500 * r + 50000 * (q * q * q) + 600000000 * (q * q) + 500000000,
      bmGHatUnaryBundle.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (K, p)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encGHatUnaryBundle W W_out N_erf (S + q) S (2 * S) cBound (4 * pW)
            (2 * S + 2) (6 * S + 18) qza r))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  subst hqza hNerf hBerf hcBound hS hW_out hW hr hpW hq
  exact bmGHatUnaryBundle_computesInTime K p tW2 tW3 tW4 tW5 tSch

theorem bmGHatCtxFromUnaryWith_computesInTime_gen {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p q pW r W W_out S cBound B_erf N_erf qza : ℕ)
    (cFix0 zDen0 denOut0 : ℤ) (hK : 2 ≤ K)
    (hq : q = qChildEll K p) (hpW : pW = pWorkEll K p) (hr : r = rEll K)
    (hW : W = 1000 * q) (hW_out : W_out = 10 * q) (hS : S = q + 2 * pW + 20)
    (hcBound : cBound = Nat.sqrt (3 * pW) + 1) (hBerf : B_erf = 2 * cBound)
    (hNerf : N_erf = 4 * B_erf ^ 2 + (S + B_erf) + 1)
    (hqza : qza = (N_erf + 6) + (3 * (N_erf + 6) + 6))
    (hcFix : cFix0 = min ((cBound : ℤ) * (2 : ℤ) ^ S)
      (approxSqrtFixed (2 * S + 2)
        (4 * (pW : ℤ) * max ((2 : ℤ) ^ ((2 * S + (2 * S + 2)) - 1)) (approxLogTwoFixed (2 * S)))))
    (hzDen : zDen0 = 2 * (r : ℤ) * (2 : ℤ) ^ S)
    (hdenOut : denOut0 = max ((2 : ℤ) ^ S)
      (approxSqrtFixed (6 * S + 18) (approxPiFixed (2 * S))) * (2 : ℤ) ^ qza)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ (2 * S + 4) * (1250 * W * W + 400000 * W + 1000000) +
        10 * mulTime W + 3000 * W * W + 10000000 * W + r * (4000 * W + 100000) + 10000000,
      (bmGHatCtxFromUnaryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encGHatUnaryBundle W W_out N_erf (S + q) S (2 * S) cBound (4 * pW)
            (2 * S + 2) (6 * S + 18) qza r))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair id encUnary) encUnary
            ((encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFix0 zDen0 denOut0, W), r)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  subst hdenOut hzDen hcFix hqza hNerf hBerf hcBound hS hW_out hW hr hpW hq
  exact bmGHatCtxFromUnaryWith_computesInTime hmul K p hK tW2 tW3 tW4 tW5 tSch

theorem bmGHatEntryWith_computesInTime_gen {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (W W_out K p q pW r S cBound B_erf N_erf qza : ℕ)
    (cFix0 zDen0 denOut0 : ℤ) (hK : 2 ≤ K)
    (hq : q = qChildEll K p) (hpW : pW = pWorkEll K p) (hr : r = rEll K)
    (hS : S = q + 2 * pW + 20)
    (hcBound : cBound = Nat.sqrt (3 * pW) + 1) (hBerf : B_erf = 2 * cBound)
    (hNerf : N_erf = 4 * B_erf ^ 2 + (S + B_erf) + 1)
    (hqza : qza = (N_erf + 6) + (3 * (N_erf + 6) + 6))
    (hcFix : cFix0 = min ((cBound : ℤ) * (2 : ℤ) ^ S)
      (approxSqrtFixed (2 * S + 2)
        (4 * (pW : ℤ) * max ((2 : ℤ) ^ ((2 * S + (2 * S + 2)) - 1)) (approxLogTwoFixed (2 * S)))))
    (hzDen : zDen0 = 2 * (r : ℤ) * (2 : ℤ) ^ S)
    (hdenOut : denOut0 = max ((2 : ℤ) ^ S)
      (approxSqrtFixed (6 * S + 18) (approxPiFixed (2 * S))) * (2 : ℤ) ^ qza)
    (hW : 1000 * q ≤ W) (hW_out_le : W_out ≤ W)
    (yNum : ℤ) (hy0 : 0 ≤ yNum) (hyr : yNum ≤ (r : ℤ))
    (hfits_out : FitsSignedWord W_out (computeGHatMantissaFixed K p yNum r))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
        16 * mulTime W + 42000 * W * W + 3000000 * W + 4000000,
      (bmGHatEntryWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (fun x => x) (encodeSignedWord W)
            (encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFix0 zDen0 denOut0, yNum)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W_out (computeGHatMantissaFixed K p yNum r)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  subst hdenOut hzDen hcFix hqza hNerf hBerf hcBound hS hr hpW hq
  exact bmGHatEntryWith_computesInTime hmul W W_out K p hK hW hW_out_le yNum hy0 hyr hfits_out
    tW2 tW3 tW4 tW5 tSch

set_option maxHeartbeats 1200000 in
theorem bmNodeGHatTablesWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p : ℕ) (_hleaf : (!isBaseLeaf K p) = true) (hK : 2 ≤ K)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let r := rEll K
    let S_term := scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q)
    ∃ t ≤ 4000000000000 * (r * S_term),
      (bmNodeGHatTablesWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnary encUnary (K, p)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair id id
            (encMantissaTable K p (computePassbandC0MantissaWithMul (· * ·) K p),
             encMantissaTable K p (computePassbandC1MantissaWithMul (· * ·) K p))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  unfold computePassbandC0MantissaWithMul computePassbandC1MantissaWithMul
  dsimp only
  rw [show computeGHatMantissaFixedWithMul (· * ·) K p = computeGHatMantissaFixed K p from rfl]
  obtain ⟨ghatFn, hghatFn⟩ : ∃ f : ℤ → ℕ → ℤ, f = computeGHatMantissaFixed K p := ⟨_, rfl⟩
  rw [← hghatFn]
  have hc0_len :
      (encMantissaTable K p (fun u2 : Fin (rEll K) => ghatFn (u2.val : ℤ) (rEll K))).length ≤
      rEll K * (40 * qChildEll K p + 10) :=
    length_encMantissaTable_le K p _
  have hc1_len :
      (encMantissaTable K p (fun u2 : Fin (rEll K) => ghatFn ((rEll K : ℤ) - (u2.val : ℤ)) (rEll K))).length ≤
      rEll K * (40 * qChildEll K p + 10) :=
    length_encMantissaTable_le K p _
  unfold encMantissaTable at hc0_len hc1_len ⊢
  have hq_ge : 4 ≤ qChildEll K p := by have := qChildEll_eq K p; omega
  have hfits_c0 : ∀ u2 : ℕ, u2 < rEll K →
      FitsSignedWord (10 * qChildEll K p) (ghatFn (u2 : ℤ) (rEll K)) := by
    intro u2 hu2
    rw [hghatFn]
    exact (fitsSignedWord_computeGHatMantissaFixed K p (u2 : ℤ)
      (Nat.cast_nonneg u2) (by exact_mod_cast (le_of_lt hu2))).mono (by omega)
  have hfits_c1 : ∀ u2 : ℕ, u2 < rEll K →
      FitsSignedWord (10 * qChildEll K p) (ghatFn ((rEll K : ℤ) - (u2 : ℤ)) (rEll K)) := by
    intro u2 hu2
    rw [hghatFn]
    have hu2_z : (0 : ℤ) ≤ (u2 : ℤ) := Nat.cast_nonneg u2
    have hu2_lt : (u2 : ℤ) < (rEll K : ℤ) := by exact_mod_cast hu2
    exact (fitsSignedWord_computeGHatMantissaFixed K p ((rEll K : ℤ) - (u2 : ℤ))
      (by omega) (by omega)).mono (by omega)
  generalize hq_def : qChildEll K p = q at hc0_len hc1_len hfits_c0 hfits_c1 ⊢
  generalize hpW_def : pWorkEll K p = pW
  generalize hr_def : rEll K = r at hc0_len hc1_len hfits_c0 hfits_c1 ⊢
  obtain ⟨S_term, hSterm_def⟩ :
      ∃ x : ℕ, x = scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q) := ⟨_, rfl⟩
  rw [← hSterm_def]
  obtain ⟨W, hW_def⟩ : ∃ x : ℕ, x = 1000 * q := ⟨_, rfl⟩
  obtain ⟨W_out, hWout_def⟩ : ∃ x : ℕ, x = 10 * q := ⟨_, rfl⟩
  rw [← hWout_def] at hc0_len hc1_len hfits_c0 hfits_c1 ⊢
  obtain ⟨S, hS_def⟩ : ∃ x : ℕ, x = q + 2 * pW + 20 := ⟨_, rfl⟩
  obtain ⟨cBound, hcBound_def⟩ : ∃ x : ℕ, x = Nat.sqrt (3 * pW) + 1 := ⟨_, rfl⟩
  obtain ⟨B_erf, hBerf_def⟩ : ∃ x : ℕ, x = 2 * cBound := ⟨_, rfl⟩
  obtain ⟨N_erf, hNerf_def⟩ : ∃ x : ℕ, x = 4 * B_erf ^ 2 + (S + B_erf) + 1 := ⟨_, rfl⟩
  obtain ⟨qza, hqza_def⟩ : ∃ x : ℕ, x = (N_erf + 6) + (3 * (N_erf + 6) + 6) := ⟨_, rfl⟩
  obtain ⟨cFix0, hcFix_def⟩ : ∃ x : ℤ, x = min ((cBound : ℤ) * (2 : ℤ) ^ S)
    (approxSqrtFixed (2 * S + 2)
      (4 * (pW : ℤ) * max ((2 : ℤ) ^ ((2 * S + (2 * S + 2)) - 1)) (approxLogTwoFixed (2 * S)))) :=
    ⟨_, rfl⟩
  obtain ⟨zDen0, hzDen_def⟩ : ∃ x : ℤ, x = 2 * (r : ℤ) * (2 : ℤ) ^ S := ⟨_, rfl⟩
  obtain ⟨denOut0, hdenOut_def⟩ : ∃ x : ℤ, x = max ((2 : ℤ) ^ S)
    (approxSqrtFixed (6 * S + 18) (approxPiFixed (2 * S))) * (2 : ℤ) ^ qza := ⟨_, rfl⟩
  have hUnary := bmGHatUnaryBundle_computesInTime_gen K p q pW r W W_out S cBound B_erf N_erf qza
    hq_def.symm hpW_def.symm hr_def.symm hW_def hWout_def hS_def hcBound_def hBerf_def
    hNerf_def hqza_def
  have hCtx := bmGHatCtxFromUnaryWith_computesInTime_gen hmul K p q pW r W W_out S cBound B_erf
    N_erf qza cFix0 zDen0 denOut0 hK hq_def.symm hpW_def.symm hr_def.symm hW_def hWout_def
    hS_def hcBound_def hBerf_def hNerf_def hqza_def hcFix_def hzDen_def hdenOut_def
  have hW_ge : 1000 * q ≤ W := by omega
  have hW_out_le : W_out ≤ W := by omega
  have hEntryGen : ∀ (yNum : ℤ), 0 ≤ yNum → yNum ≤ (r : ℤ) →
      FitsSignedWord W_out (ghatFn yNum r) →
      ∀ tW2' tW3' tW4' tW5' tSch',
      ∃ t ≤ 2 * (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
          16 * mulTime W + 42000 * W * W + 3000000 * W + 4000000,
        (bmGHatEntryWith bmMul).ComputesInTime
          (mkTapes8 (encodeDelimWord
            (encPair id (encodeSignedWord W)
              (encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFix0 zDen0 denOut0, yNum)))
            [] [] tW2' tW3' tW4' tW5' tSch')
          (mkTapes8 (encodeDelimWord (encodeSignedWord W_out (ghatFn yNum r)))
            [] [] tW2' tW3' tW4' tW5' tSch') t := by
    intro yNum hy0 hyr hfits tW2' tW3' tW4' tW5' tSch'
    have h0 := bmGHatEntryWith_computesInTime_gen hmul W W_out K p q pW r S cBound B_erf N_erf qza
      cFix0 zDen0 denOut0 hK hq_def.symm hpW_def.symm hr_def.symm hS_def hcBound_def hBerf_def
      hNerf_def hqza_def hcFix_def hzDen_def hdenOut_def hW_ge hW_out_le yNum hy0 hyr
      (by rw [← hghatFn]; exact hfits) tW2' tW3' tW4' tW5' tSch'
    rw [← hghatFn] at h0
    exact h0
  clear hcFix_def hzDen_def hdenOut_def hqza_def hghatFn hW_ge hW_out_le
  let St := Unit
  have hq_eq : q = p + 2 * K + 14 := hq_def.symm.trans (qChildEll_eq K p)
  have hpW_eq : pW = p + K + 6 := hpW_def.symm
  have hW_pos : 1 ≤ W := by omega
  have hr_pos : 1 ≤ r := by rw [← hr_def]; exact rEll_pos K
  have hr_le : r ≤ 2 ^ K := by rw [← hr_def]; exact rEll_le_two_pow K
  have hr_pow_q : r ≤ 2 ^ q := hr_le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hr_lt_q1 : r < 2 ^ (q + 1) :=
    lt_of_le_of_lt hr_pow_q (Nat.pow_lt_pow_right (by decide) (by omega))
  have hr_lt_W : r < 2 ^ W :=
    lt_of_lt_of_le hr_lt_q1 (Nat.pow_le_pow_right (by decide) (by omega))
  have hsqrt_sq : Nat.sqrt (3 * pW) * Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le (3 * pW)
  have hsqrt_le : Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le_self (3 * pW)
  have hcBound_le : cBound ≤ 3 * q := by omega
  have hBerf_le : B_erf ≤ 6 * q := by omega
  have hBerf_sq : B_erf ^ 2 ≤ 36 * pW + 4 := by
    rw [hBerf_def, hcBound_def]
    nlinarith only [hsqrt_sq, hsqrt_le]
  let uL1 : St → List Bool := encDepPair (fun _ => encUnary W) (fun _ => encUnary W_out)
  let uL2 : St → List Bool := encDepPair (fun _ => encUnary N_erf) (fun _ => encUnary (S + q))
  let uLeft : St → List Bool := encDepPair uL1 uL2
  let uR1 : St → List Bool := encDepPair (fun _ => encodeSignedWord W (r : ℤ))
    (fun _ => encodeSignedWord W cFix0)
  let uR2 : St → List Bool := encDepPair (fun _ => encodeSignedWord W zDen0)
    (fun _ => encodeSignedWord W denOut0)
  let uRight : St → List Bool := encDepPair uR1 uR2
  let uGHatCtx : St → List Bool := encDepPair uLeft uRight
  have hlen_ghatCtx : (uGHatCtx ()).length ≤ 130 * W + 250 := by
    dsimp (config := { zeta := false }) only [uGHatCtx, uLeft, uRight, uL1, uL2, uR1, uR2]
    simp (config := { zeta := false }) only [length_encDepPair, length_encUnary, length_encodeSignedWord]
    omega
  obtain ⟨B_elem, hBelem_def⟩ : ∃ x : ℕ, x =
      2 * (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) +
      16 * mulTime W + 42000 * W * W + 3060000 * W + 4100000 := ⟨_, rfl⟩
  have hemitC0 : ∀ (u2 : ℕ),
      StageEval (S := { _s : St // u2 < r }) (bmC0EmitWith bmMul)
        (encDepPair (encDepPair (fun _ => uGHatCtx ()) (fun _ => encUnary W))
          (fun _ => encodeSignedWord W (u2 : ℤ)))
        (fun _ => encodeSignedWord W_out (ghatFn (u2 : ℤ) r))
        (fun _ => B_elem) := fun u2 => by
    let SubS := { _s : St // u2 < r }
    by_cases hu2 : u2 < r
    · let uCW : SubS → List Bool := encDepPair (fun _ => uGHatCtx ()) (fun _ => encUnary W)
      let uU2 : SubS → List Bool := fun _ => encodeSignedWord W (u2 : ℤ)
      have pDropW := StageEval.mapFst (u2 := uU2)
        (StageEval.fst (fun _ : SubS => uGHatCtx ()) (fun _ => encUnary W))
      have hu2_le : (u2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast (le_of_lt hu2)
      have pEntry := StageEval.const (S := SubS)
        (hEntryGen (u2 : ℤ) (Nat.cast_nonneg u2) hu2_le (hfits_c0 u2 hu2))
      refine (StageEval.seq pDropW pEntry).mono (fun _ => ?_)
      dsimp (config := { zeta := false }) only [uCW, uU2]
      simp (config := { zeta := false }) only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega
    · intro s'; exact False.elim (hu2 s'.property)
  have hemitC1 : ∀ (u2 : ℕ),
      StageEval (S := { _s : St // u2 < r }) (bmC1EmitWith bmMul)
        (encDepPair (encDepPair (fun _ => uGHatCtx ()) (fun _ => encUnary W))
          (fun _ => encodeSignedWord W (u2 : ℤ)))
        (fun _ => encodeSignedWord W_out (ghatFn ((r : ℤ) - (u2 : ℤ)) r))
        (fun _ => B_elem) := fun u2 => by
    let SubS := { _s : St // u2 < r }
    by_cases hu2 : u2 < r
    · let uCW : SubS → List Bool := encDepPair (fun _ => uGHatCtx ()) (fun _ => encUnary W)
      let uU2 : SubS → List Bool := fun _ => encodeSignedWord W (u2 : ℤ)
      have pF1 := StageEval.fst uCW uU2
      have pU2 := StageEval.snd uCW uU2
      have pCtx := StageEval.seq pF1
        (StageEval.fst (fun _ : SubS => uGHatCtx ()) (fun _ => encUnary W))
      have pRight' := StageEval.seq pCtx
        (StageEval.snd (fun _ : SubS => uLeft ()) (fun _ => uRight ()))
      have pR1' := StageEval.seq pRight'
        (StageEval.fst (fun _ : SubS => uR1 ()) (fun _ => uR2 ()))
      have pRs := StageEval.seq pR1'
        (StageEval.fst (fun _ : SubS => encodeSignedWord W (r : ℤ))
          (fun _ => encodeSignedWord W cFix0))
      have hr_fits : FitsSignedWord W (r : ℤ) := by
        rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]; exact hr_lt_W
      have hu2_fits : FitsSignedWord W (u2 : ℤ) := by
        rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
        exact lt_trans hu2 hr_lt_W
      have hdiff_fits : FitsSignedWord W ((r : ℤ) - (u2 : ℤ)) := by
        rw [fitsSignedWord_iff_abs_lt]
        have h1 : (0 : ℤ) ≤ (r : ℤ) - (u2 : ℤ) := by
          have : (u2 : ℤ) < (r : ℤ) := by exact_mod_cast hu2
          omega
        rw [abs_of_nonneg h1]
        have h2 : (r : ℤ) - (u2 : ℤ) ≤ (r : ℤ) := by
          have : (0 : ℤ) ≤ (u2 : ℤ) := Nat.cast_nonneg u2
          omega
        have h3 : (r : ℤ) < (2 : ℤ) ^ W := by exact_mod_cast hr_lt_W
        omega
      have pDiff := StageEval.seq (StageEval.fanout pRs pU2)
        (StageEval.const (S := SubS)
          (bmSignedSub_computesInTime W (r : ℤ) (u2 : ℤ) hr_fits hu2_fits hdiff_fits))
      have pIn := StageEval.fanout pCtx pDiff
      have hdiff_nn : (0 : ℤ) ≤ (r : ℤ) - (u2 : ℤ) := by
        have : (u2 : ℤ) < (r : ℤ) := by exact_mod_cast hu2
        omega
      have hdiff_le : (r : ℤ) - (u2 : ℤ) ≤ (r : ℤ) := by
        have : (0 : ℤ) ≤ (u2 : ℤ) := Nat.cast_nonneg u2
        omega
      have pEntry := StageEval.const (S := SubS)
        (hEntryGen ((r : ℤ) - (u2 : ℤ)) hdiff_nn hdiff_le (hfits_c1 u2 hu2))
      refine (StageEval.seq pIn pEntry).mono (fun _ => ?_)
      have hLeft_len : (uLeft ()).length ≤ (uGHatCtx ()).length := by
        dsimp (config := { zeta := false }) only [uGHatCtx]
        simp (config := { zeta := false }) only [length_encDepPair]; omega
      dsimp (config := { zeta := false }) only [uCW, uU2, uRight, uR1, uR2]
      simp (config := { zeta := false }) only [length_encDepPair, length_encUnary, length_encodeSignedWord]
      omega
    · intro s'; exact False.elim (hu2 s'.property)
  have pUnary := StageEval.const (S := St) hUnary
  have pCtx := StageEval.const (S := St) hCtx
  have pTabC0 := StageEval.tabulateSigned (S := St) (emitM := bmC0EmitWith bmMul)
    (uCtx := uGHatCtx) (W := fun _ => W) (N := fun _ => r)
    (encElem := fun _ => encodeSignedWord W_out)
    (fn := fun _ u2 => ghatFn (u2 : ℤ) r)
    (B := fun _ => B_elem)
    (L_ctx := fun _ => 130 * W + 250)
    (L_elem := fun _ => 2 * W_out + 2)
    (fun _ => hW_pos) (fun _ => hr_lt_W) hemitC0
    (fun _ => hlen_ghatCtx)
    (fun _ _ _ => by simp only [length_encodeSignedWord]; omega)
  have pTabC1 := StageEval.tabulateSigned (S := St) (emitM := bmC1EmitWith bmMul)
    (uCtx := uGHatCtx) (W := fun _ => W) (N := fun _ => r)
    (encElem := fun _ => encodeSignedWord W_out)
    (fn := fun _ u2 => ghatFn ((r : ℤ) - (u2 : ℤ)) r)
    (B := fun _ => B_elem)
    (L_ctx := fun _ => 130 * W + 250)
    (L_elem := fun _ => 2 * W_out + 2)
    (fun _ => hW_pos) (fun _ => hr_lt_W) hemitC1
    (fun _ => hlen_ghatCtx)
    (fun _ _ _ => by simp only [length_encodeSignedWord]; omega)
  have hall := StageEval.seq pUnary (StageEval.seq pCtx (StageEval.fanout pTabC0 pTabC1))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  clear hemitC0 hemitC1 hUnary hCtx hEntryGen pUnary pCtx pTabC0 pTabC1 hall
  dsimp (config := { zeta := false }) only [id, Prod.fst, Prod.snd] at ht hc0_len hc1_len
  simp (config := { zeta := false }) only [length_encPair, length_encUnary] at ht
  dsimp (config := { zeta := false }) only [id] at ht
  refine ⟨t, ?_, hcomp⟩
  change (encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFix0 zDen0 denOut0).length ≤
    130 * W + 250 at hlen_ghatCtx
  generalize (encGHatEntryCtx W W_out N_erf (S + q) (r : ℤ) cFix0 zDen0 denOut0).length = lenCtx
    at ht hlen_ghatCtx
  clear hcomp uGHatCtx uRight uR2 uR1 uLeft uL2 uL1 St
  have hmW : mulTime W ≤ scaledSubMulCost mulTime q := by
    rw [hW_def]; exact le_scaledSubMulCost_thousand mulTime q
  have hB1 :
      2 * (N_erf + 7) * (2 * mulTime W + 5500 * W * W + 550000 * W + 800000) ≤
      (310 * 6000000000) * S_term := by
    rw [hSterm_def]
    exact mul_le_scheduleSeriesTerms
      (by nlinarith only [hNerf_def, hS_def, hBerf_sq, hBerf_le, hq_eq, hpW_eq])
      (by nlinarith only [hW_def, hmW, hq_eq])
  have hB2 :
      16 * mulTime W + 42000 * W * W + 3060000 * W + 4100000 +
      1000 * W + 100 * (130 * W + 250) + 50 * (2 * W_out + 2) + 2500 + 200 ≤
      50000000000 * S_term := by
    rw [hSterm_def]
    exact quad_le_scheduleSeriesTerms (by nlinarith only [hWout_def, hW_def, hmW, hq_eq])
  have hBelem_le :
      B_elem + 1000 * W + 100 * (130 * W + 250) + 50 * (2 * W_out + 2) + 2500 + 200 ≤
      1910000000000 * S_term := by
    linarith only [hBelem_def, hB1, hB2]
  have hr_mul :
      2 * (r * (B_elem + 1000 * W + 100 * (130 * W + 250) + 50 * (2 * W_out + 2) + 2500)) +
      200 * r ≤
      3820000000000 * (r * S_term) := by
    have hm := Nat.mul_le_mul_left r hBelem_le
    have hr1 : r * (1910000000000 * S_term) = 1910000000000 * (r * S_term) := by ring
    have hr2 : r * (B_elem + 1000 * W + 100 * (130 * W + 250) + 50 * (2 * W_out + 2) + 2500 + 200) =
        r * (B_elem + 1000 * W + 100 * (130 * W + 250) + 50 * (2 * W_out + 2) + 2500) + 200 * r := by ring
    linarith only [hm, hr1, hr2]
  have hctx1 :
      (2 * S + 4) * (1250 * W * W + 400000 * W + 1000000) ≤ (8 * 1300000000) * S_term := by
    rw [hSterm_def]
    exact mul_le_scheduleSeriesTerms (by omega) (by nlinarith only [hW_def, hmW, hq_eq])
  have hctx2 :
      10 * mulTime W + 3000 * W * W + 10000000 * W + 10000000 +
      50000 * (q * q * q) + 600000000 * (q * q) + 500000000 ≤
      6000000000 * S_term := by
    have hcube := cube_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q)
    have hcube50 : 50000 * (q * q * q) ≤ 1000000000 * S_term := by
      have h1 : 50000 * (q * q * q) ≤ 500 * (120 * (q * q * q)) := by omega
      have h2 : 500 * (120 * (q * q * q)) ≤ 500 * S_term := by
        rw [hSterm_def]; exact Nat.mul_le_mul_left 500 hcube
      omega
    have hq_quad :
        10 * mulTime W + 3000 * W * W + 10000000 * W + 10000000 +
        600000000 * (q * q) + 500000000 ≤
        5000000000 * S_term := by
      rw [hSterm_def]
      exact quad_le_scheduleSeriesTerms (by nlinarith only [hW_def, hmW, hq_eq])
    omega
  have hS_lin0 := linear_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q) (by omega)
  have hS_lin : 1000 * q + 10 ≤ 10 * S_term := by omega
  have hr_q : r * (40 * q + 10) ≤ r * S_term := by
    have h1 : 40 * q + 10 ≤ S_term := by omega
    exact Nat.mul_le_mul_left r h1
  have hKr : 100 * (K + 1) * r + 500 * r + r * (4000 * W + 100000) ≤ 5000000 * (r * S_term) := by
    have h1 : 100 * (K + 1) + 500 + (4000 * W + 100000) ≤ 5000000 * S_term := by
      clear hB1 hB2 hBelem_le hBelem_def hSterm_def hr_mul hctx1 hctx2 hNerf_def hBerf_def hcBound_def
      omega
    have h2 := Nat.mul_le_mul_left r h1
    have hr1 : r * (100 * (K + 1) + 500 + (4000 * W + 100000)) =
        100 * (K + 1) * r + 500 * r + r * (4000 * W + 100000) := by ring
    have hr2 : r * (5000000 * S_term) = 5000000 * (r * S_term) := by ring
    omega
  have hS_r : S_term ≤ r * S_term := Nat.le_mul_of_pos_left S_term hr_pos
  have hW_S : W ≤ 1000 * S_term := by omega
  clear hB1 hB2 hBelem_le hBelem_def hSterm_def hNerf_def hBerf_def hcBound_def hS_def hWout_def hW_def
  omega

/-! ### 4.4 Combined Internal Node Schedule (`bmNodeScheduleWith`) -/

/-- **Combined Internal Node Schedule Generator (`bmNodeScheduleWith bmMul`)**:
Consumes `((K, p), B_in)` on `kIO` and emits `encNodeSchedule K p B_in ...`. -/
def bmNodeScheduleWith (bmMul : BitMachine) : BitMachine :=
  let bmKP := bmFst
  let bmBIn := bmSnd
  let bmM1 := bmSeq bmKP bmComputeM1Ell
  let bmHeader := bmFanout bmKP (bmFanout bmBIn bmM1)
  let bmTaps := bmSeq bmKP (bmNodeTapTableWith bmMul)
  let bmTwists := bmSeq bmKP (bmNodeTwistTablesWith bmMul)
  let bmGHats := bmSeq bmKP (bmNodeGHatTablesWith bmMul)
  let bmTables := bmFanout (bmFanout bmTaps bmTwists) bmGHats
  bmFanout bmHeader bmTables

theorem length_encNodeSchedule_le (K p B_in m1 : ℕ)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ) :
    (encNodeSchedule K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa).length ≤
      16 * K + 16 * p + 16 * B_in + 16 * m1 +
      8 * (t1Ell K * ((2 * m1 + 1) * (8 * qChildEll K p + 30))) +
      32 * (rEll K * (80 * qChildEll K p + 18)) +
      16 * (rEll K * (40 * qChildEll K p + 10)) + 120 := by
  unfold encNodeSchedule
  have htap := length_encTapTable_le K p m1 filterTap
  have hpre := length_encTwistTable_le K p preTwistRoot
  have hpost := length_encTwistTable_le K p postTwistRoot
  have hc0 := length_encMantissaTable_le K p c0Mantissa
  have hc1 := length_encMantissaTable_le K p c1Mantissa
  simp only [length_encPair, length_encUnary, id]
  omega

set_option maxHeartbeats 800000 in
theorem bmNodeScheduleWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p B_in : ℕ) (hleaf : (!isBaseLeaf K p) = true) (hK : 2 ≤ K)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let q := qChildEll K p
    let t1 := t1Ell K
    let m1 := computeM1Ell K p
    let r := rEll K
    let S_term := scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q)
    let expRoot := expTwoPiIFixedWithMul (· * ·) q
    ∃ t ≤ 6000000000000 * ((t1 * (2 * m1 + 1) + r) * S_term) + 1000 * B_in,
      (bmNodeScheduleWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encNodeSchedule K p B_in m1
            (memoizeFilterTap m1 (computeFilterTapFixedWithMul (· * ·) K p))
            (memoizeFin (fun k2 => expRoot (k2.val : ℤ) (2 * r)))
            (memoizeFin (fun k2 => expRoot (-(k2.val : ℤ)) (2 * r)))
            (memoizeFin (computePassbandC0MantissaWithMul (· * ·) K p))
            (memoizeFin (computePassbandC1MantissaWithMul (· * ·) K p))))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  have hmemo_tap :
      encTapTable K p (computeM1Ell K p)
        (memoizeFilterTap (computeM1Ell K p) (computeFilterTapFixedWithMul (· * ·) K p)) =
      encTapTable K p (computeM1Ell K p) (computeFilterTapFixed K p) := by
    rw [computeFilterTapFixedWithMul_eq_computeFilterTapFixed, memoizeFilterTap_computeFilterTapFixed]
  let St := Unit
  let uKP : St → List Bool := fun _ => encPair encUnary encUnary (K, p)
  let uB : St → List Bool := fun _ => encUnary B_in
  let uIn : St → List Bool := encDepPair uKP uB
  have pKP := StageEval.fst uKP uB
  have pB := StageEval.snd uKP uB
  have pM1 := StageEval.seq pKP
    (StageEval.of_computesStageLe bmComputeM1Ell_computesStageLe (fun _ : St => (K, p)))
  have pHeader := StageEval.fanout pKP (StageEval.fanout pB pM1)
  have pTaps := StageEval.seq pKP
    (StageEval.const (S := St) (bmNodeTapTableWith_computesInTime hmul K p hleaf hK))
  have pTwists := StageEval.seq pKP
    (StageEval.const (S := St) (bmNodeTwistTablesWith_computesInTime hmul K p))
  have pGHats := StageEval.seq pKP
    (StageEval.const (S := St) (bmNodeGHatTablesWith_computesInTime hmul K p hleaf hK))
  have pTables := StageEval.fanout (StageEval.fanout pTaps pTwists) pGHats
  have hall := StageEval.congr_out
    (v2 := fun _ => encNodeSchedule K p B_in (computeM1Ell K p)
      (memoizeFilterTap (computeM1Ell K p) (computeFilterTapFixedWithMul (· * ·) K p))
      (memoizeFin (fun k2 => expTwoPiIFixedWithMul (· * ·) (qChildEll K p) (k2.val : ℤ) (2 * rEll K)))
      (memoizeFin (fun k2 => expTwoPiIFixedWithMul (· * ·) (qChildEll K p) (-(k2.val : ℤ)) (2 * rEll K)))
      (memoizeFin (computePassbandC0MantissaWithMul (· * ·) K p))
      (memoizeFin (computePassbandC1MantissaWithMul (· * ·) K p)))
    (StageEval.fanout pHeader pTables)
    (fun _ => by
      dsimp only [encNodeSchedule, uKP, uB, encDepPair]
      rw [hmemo_tap, memoizeFin_eq, memoizeFin_eq, memoizeFin_eq, memoizeFin_eq]
      rfl)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  clear pKP pB pM1 pHeader pTaps pTwists pGHats pTables hall
  let q := qChildEll K p
  let t1 := t1Ell K
  let m1 := computeM1Ell K p
  let r := rEll K
  let S_term := scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q)
  have htap_len := length_encTapTable_le K p m1 (computeFilterTapFixed K p)
  have hpre_len := length_encTwistTable_le K p
    (fun k2 => expTwoPiIFixed q (k2.val : ℤ) (2 * r))
  have hpost_len := length_encTwistTable_le K p
    (fun k2 => expTwoPiIFixed q (-(k2.val : ℤ)) (2 * r))
  have hc0_len := length_encMantissaTable_le K p
    (computePassbandC0MantissaWithMul (· * ·) K p)
  have hc1_len := length_encMantissaTable_le K p
    (computePassbandC1MantissaWithMul (· * ·) K p)
  have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
  have hpC_eq : pChildEll K p = p + 2 * K + 12 := pChildEll_eq K p
  have hm1_le : m1 ≤ q := by
    have := computeM1Ell_le_pChildEll K p
    dsimp [m1]; omega
  have hq_12r : q ≤ 12 * r := qChildEll_le_twelve_mul_rEll_of_internal hleaf hK
  have hcube := cube_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q)
  have hq4_le : 1100 * q * q * q * q + 2000 * q * q + 5000 ≤ 200 * (r * S_term) := by
    have hq1 : 1 ≤ q := by omega
    have hq14 : 14 ≤ q := by omega
    have h1_q4 : 100 ≤ q * q * q * q := by
      calc 100 ≤ 14 * 14 * 1 * 1 := by decide
        _ ≤ q * q * q * q := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hq14 hq14) hq1) hq1
    have ha : 100 * (q * q) ≤ q * q * q * q := by
      calc 100 * (q * q) ≤ (q * q) * (q * q) := Nat.mul_le_mul_right _ (by nlinarith)
        _ = q * q * q * q := by ring
    have h1 : 1100 * q * q * q * q + 2000 * q * q + 5000 ≤ (1200 * q) * (q * q * q) := by
      calc 1100 * q * q * q * q + 2000 * q * q + 5000
          = 1100 * (q * q * q * q) + 20 * (100 * (q * q)) + 50 * 100 := by ring
        _ ≤ 1100 * (q * q * q * q) + 20 * (q * q * q * q) + 50 * (q * q * q * q) :=
            Nat.add_le_add (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 20 ha))
              (Nat.mul_le_mul_left 50 h1_q4)
        _ = 1170 * (q * q * q * q) := by ring
        _ ≤ 1200 * (q * q * q * q) := Nat.mul_le_mul_right _ (by decide)
        _ = (1200 * q) * (q * q * q) := by ring
    have h2 : 1200 * q ≤ 200 * r * 120 := by omega
    have h3 := Nat.mul_le_mul_right (q * q * q) h2
    have h4 : (200 * r) * (120 * (q * q * q)) ≤ (200 * r) * S_term :=
      Nat.mul_le_mul_left (200 * r) hcube
    have hr1 : (200 * r * 120) * (q * q * q) = (200 * r) * (120 * (q * q * q)) := by ring
    have hr2 : (200 * r) * S_term = 200 * (r * S_term) := by ring
    omega
  have hS_lin0 := linear_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q) (by omega)
  have hS_tap : 8 * q + 30 ≤ S_term := by dsimp only [S_term] at *; omega
  have hS_tw : 80 * q + 18 ≤ S_term := by dsimp only [S_term] at *; omega
  have hS_gh : 40 * q + 10 ≤ S_term := by dsimp only [S_term] at *; omega
  have htap_S : t1 * ((2 * m1 + 1) * (8 * q + 30)) ≤ (t1 * (2 * m1 + 1)) * S_term := by
    have hm := Nat.mul_le_mul_left (t1 * (2 * m1 + 1)) hS_tap
    have hr1 : t1 * ((2 * m1 + 1) * (8 * q + 30)) = (t1 * (2 * m1 + 1)) * (8 * q + 30) := by ring
    omega
  have htw_S : r * (80 * q + 18) ≤ r * S_term := Nat.mul_le_mul_left r hS_tw
  have hgh_S : r * (40 * q + 10) ≤ r * S_term := Nat.mul_le_mul_left r hS_gh
  have hr_pos : 1 ≤ r := rEll_pos K
  have hS_r : S_term ≤ r * S_term := Nat.le_mul_of_pos_left S_term hr_pos
  have hq_S : q ≤ S_term := by dsimp only [S_term] at *; omega
  have h1_S : 1 ≤ S_term := by dsimp only [S_term] at *; omega
  have hcomb :
      (t1 * (2 * m1 + 1)) * S_term + r * S_term = (t1 * (2 * m1 + 1) + r) * S_term := by ring
  dsimp only at ht
  dsimp only [uIn, uKP, uB, id] at ht
  simp only [length_encDepPair, length_encPair, length_encUnary, id] at ht
  refine ⟨t, ?_, hcomp⟩
  dsimp only [q, t1, m1, r, S_term] at *
  omega

/-! ## 5. Multi-Level Schedule Stream Encoding & Generator (`encScheduleStream`, `bmScheduleTreeWith`) -/

/-- At any internal schedule tree node (`(!isBaseLeaf K p) = true` and `2 ≤ K`), `B_in ≤ p` implies
`childScheduleBIn K p B_in ≤ pChildEll K p`. -/
theorem childScheduleBIn_le_pChildEll_of_internal {K p B_in : ℕ}
    (hleaf : (!isBaseLeaf K p) = true) (hK2 : 2 ≤ K) (hB : B_in ≤ p) :
    childScheduleBIn K p B_in ≤ pChildEll K p := by
  unfold childScheduleBIn
  have hq := qChildEll_le_twelve_mul_rEll_of_internal hleaf hK2
  have hpC_eq := pChildEll_eq K p
  have hq_eq := qChildEll_eq K p
  have hr_le : rEll K ≤ 2 ^ K := rEll_le_two_pow K
  have harg_le : 2 * pChildEll K p + 4 ≤ 2 ^ (K + 5) := by
    calc 2 * pChildEll K p + 4 ≤ 2 * qChildEll K p := by omega
      _ ≤ 2 * (12 * rEll K) := Nat.mul_le_mul_left 2 hq
      _ ≤ 2 * (12 * 2 ^ K) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 12 hr_le)
      _ ≤ 32 * 2 ^ K := by omega
      _ = 2 ^ (K + 5) := by rw [Nat.pow_add]; ring
  have hclog : Nat.clog 2 (2 * pChildEll K p + 4) ≤ K + 5 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr harg_le
  omega

/-- List of per-level schedule words from root to leaf for `tree : ScheduleIntTree K p B_in`. -/
def schedLevelWords {K p B_in : ℕ} (tree : ScheduleIntTree K p B_in) : List (List Bool) :=
  match tree with
  | .leaf K p B_in leafTwiddles =>
      [encPair encBool id (false, encLeafSchedule K p B_in leafTwiddles)]
  | .node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child =>
      encPair encBool id
        (true, encNodeSchedule K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa) ::
      schedLevelWords child

/-- Flat delimited-word stream encoding of `tree : ScheduleIntTree K p B_in` on `kSched`
(`encodeWordStack (schedLevelWords tree)`). -/
def encScheduleStream {K p B_in : ℕ} (tree : ScheduleIntTree K p B_in) : List Bool :=
  encodeWordStack (schedLevelWords tree)

@[simp]
theorem encScheduleStream_leaf (K p B_in : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p)) :
    encScheduleStream (.leaf K p B_in leafTwiddles) =
      encodeDelimWord (encPair encBool id (false, encLeafSchedule K p B_in leafTwiddles)) := by
  simp [encScheduleStream, schedLevelWords]

@[simp]
theorem encScheduleStream_node (K p B_in m1 : ℕ)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (c0Mantissa c1Mantissa : Fin (rEll K) → ℤ)
    (child : ScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) :
    encScheduleStream (.node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child) =
      encodeDelimWord
        (encPair encBool id
          (true, encNodeSchedule K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa)) ++
      encScheduleStream child := by
  simp [encScheduleStream, schedLevelWords]

theorem schedLevelWords_mem_ne_nil {K p B_in : ℕ} (tree : ScheduleIntTree K p B_in) :
    ∀ w ∈ schedLevelWords tree, w ≠ [] := by
  induction tree with
  | leaf K p B_in leafTwiddles =>
    intro w hw
    simp only [schedLevelWords, List.mem_singleton] at hw
    subst hw
    simp [encPair, encBool]
  | node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child ih =>
    intro w hw
    simp only [schedLevelWords, List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp [encPair, encBool]
    · exact ih w hw

@[simp]
theorem length_encodeWordStack_reverse (ws : List (List Bool)) :
    (encodeWordStack ws.reverse).length = (encodeWordStack ws).length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.reverse_cons, encodeWordStack_append, encodeWordStack_cons,
      encodeWordStack_nil, List.append_nil, List.length_append, ih]
    omega

set_option backward.isDefEq.respectTransparency false

/-- Unwraps `encodeDelimWord (encPair id id (w1, w2))` on `kIO`, pushing `encodeDelimWord w1`
onto `kWork2` and leaving `encodeDelimWord w2` on `kIO`. -/
def bmUnwrapToWork2 : BitMachine :=
  (tmPopStreamWord kIO kWork0 kWork2).seq bmFst

theorem bmUnwrapToWork2_computesInTime (w1 w2 tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 2 * w1.length + 2 * w2.length + 12,
      bmUnwrapToWork2.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair id id (w1, w2))) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord w2) [] [] (encodeDelimWord w1 ++ tW2) tW3 tW4 tW5 tSch) t := by
  have h1 := tmPopStreamWord_computesInTime kIO kWork0 kWork2 (by decide) (by decide) (by decide)
    (encodeDelimWord w1 ++ encodeDelimWord w2) [] [] tW2
    (mkTapes8 [] [] [] [] tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, update_mkTapes8_kWork2,
    List.append_nil, unconsDelimWord_encodeDelimWord_append] at h1
  have h2 := tmPopFirstSubwordRev_computesInTime kIO kWork0 (by decide)
    (encodeDelimWord w2) [] []
    (mkTapes8 [] [] [] (encodeDelimWord w1 ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil,
    unconsDelimWord_encodeDelimWord] at h2
  have h3 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] (encodeDelimWord w2.reverse) [] (encodeDelimWord w1 ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at h3
  have h4 := tmRevMoveWord_computesInTime kWork0 kIO (by decide)
    w2.reverse [] []
    (mkTapes8 [] [] [] (encodeDelimWord w1 ++ tW2) tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h4
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq h4))⟩
  omega

/-- Per-level schedule step computation on `kIO`:
consumes `((K, p), B_in)` on `kIO` and emits `(levelWord, nextParams)`. -/
def bmSchedStepComputeWith (bmMul : BitMachine) : BitMachine :=
  bmIte (bmSeq bmFst bmIsInternalNode)
    (bmFanout
      (bmFanout (bmConstBool true) (bmNodeScheduleWith bmMul))
      bmNextScheduleParams)
    (bmFanout
      (bmFanout (bmConstBool false) (bmLeafScheduleWith bmMul))
      bmUnaryZero)

/-- Per-level top-down schedule step: computes `(levelWord, nextParams)` on `kIO`, pushes
`encodeDelimWord levelWord` onto `kWork2`, and leaves `encodeDelimWord nextParams` on `kIO`. -/
def bmSchedTopDownStepWith (bmMul : BitMachine) : BitMachine :=
  (bmSchedStepComputeWith bmMul).seq bmUnwrapToWork2

/-- Top-down schedule loop over `kIO`: generates all levels of `computeScheduleIntTree K p B_in`
and pushes their encoded words in leaf-to-root order onto `kWork2`. -/
def bmSchedTopDownLoopWith (bmMul : BitMachine) : BitMachine :=
  (bmSchedTopDownStepWith bmMul).loopNonEmptyWord kIO

/-- Second-pass loop that pops each level schedule word from `kWork2` and pushes it onto `kSched`
until reaching the empty sentinel word `encodeDelimWord []` on `kWork2`. -/
def bmSchedPopToSchedLoop : BitMachine :=
  (tmMoveWord kWork2 kWork0 kSched).loopNonEmptyWord kWork2

/-- **Multi-Level Schedule Tree Generator (`bmScheduleTreeWith bmMul`)**:
Consumes `encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in))` on `kIO`,
pushes `encScheduleStream (computeScheduleIntTree K p B_in)` onto `kSched`, and leaves
`encodeDelimWord []` on `kIO` while preserving `kWork2..kWork5`. -/
def bmScheduleTreeWith (bmMul : BitMachine) : BitMachine :=
  (tmPushEmpty kWork2).seq
    ((bmSchedTopDownLoopWith bmMul).seq
      (bmSchedPopToSchedLoop.seq (tmPushEmpty kIO)))

theorem encPair_ne_nil {α β : Type} (f : α → List Bool) (g : β → List Bool) (p : α × β) :
    encPair f g p ≠ [] := by
  unfold encPair
  cases f p.1 <;> simp

theorem step_loopNonEmptyWord_kIO_of_ne_nil (body : BitMachine) {w : List Bool} (hw : w ≠ [])
    (tW0 tW1 tW2 tW3 tW4 tW5 tSch : List Bool) :
    (body.loopNonEmptyWord kIO).toFinTM2.step
      ⟨some none, default, mkTapes8 (encodeDelimWord w) tW0 tW1 tW2 tW3 tW4 tW5 tSch⟩ =
    some ⟨some (some body.main), default, mkTapes8 (encodeDelimWord w) tW0 tW1 tW2 tW3 tW4 tW5 tSch⟩ := by
  rcases List.exists_cons_of_ne_nil hw with ⟨b, w', rfl⟩
  simp only [BitMachine.loopNonEmptyWord, BitMachine.toFinTM2, mkBitFinTM2, Turing.FinTM2.step,
    Turing.TM2.step, Turing.TM2.stepAux, encodeDelimWord_cons, mkTapes8_kIO, List.head?_cons,
    List.tail_cons, Option.getD_some, cond_false, update_mkTapes8_kIO]

theorem bmSchedPopToSchedLoop_computesInTime :
    ∀ (ws : List (List Bool)) (_hne : ∀ w ∈ ws, w ≠ [])
      (acc tW2 tW3 tW4 tW5 tSch : List Bool),
      ∃ t ≤ 3 * (encodeWordStack ws).length + 1,
        bmSchedPopToSchedLoop.ComputesInTime
          (mkTapes8 [] [] [] (encodeWordStack ws ++ encodeDelimWord [] ++ tW2) tW3 tW4 tW5 (acc ++ tSch))
          (mkTapes8 [] [] [] tW2 tW3 tW4 tW5 (encodeWordStack ws.reverse ++ acc ++ tSch)) t
  | [], _, acc, tW2, tW3, tW4, tW5, tSch => by
    refine ⟨1, by simp, ⟨EvalsToInTime.step_one ?_⟩⟩
    simp only [bmSchedPopToSchedLoop, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
      mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
      encodeWordStack_nil, List.nil_append, encodeDelimWord_nil, List.cons_append,
      mkTapes8_kWork2, List.head?_cons, List.tail_cons, Option.getD_some, cond_true,
      update_mkTapes8_kWork2, List.reverse_nil]
  | w :: ws, hne, acc, tW2, tW3, tW4, tW5, tSch => by
    have hw_ne : w ≠ [] := hne w List.mem_cons_self
    rcases List.exists_cons_of_ne_nil hw_ne with ⟨b, w', rfl⟩
    have hpop : bmSchedPopToSchedLoop.toFinTM2.step
        ⟨some none, default,
          mkTapes8 [] [] [] (encodeWordStack ((b :: w') :: ws) ++ encodeDelimWord [] ++ tW2)
            tW3 tW4 tW5 (acc ++ tSch)⟩ =
        some ⟨some (some (tmMoveWord kWork2 kWork0 kSched).main), default,
          mkTapes8 [] [] [] (encodeDelimWord (b :: w') ++ (encodeWordStack ws ++ encodeDelimWord [] ++ tW2))
            tW3 tW4 tW5 (acc ++ tSch)⟩ := by
      simp only [bmSchedPopToSchedLoop, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
        mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
        encodeWordStack_cons, List.append_assoc, encodeDelimWord_cons, List.cons_append,
        mkTapes8_kWork2, List.head?_cons, List.tail_cons, Option.getD_some, cond_false,
        update_mkTapes8_kWork2]
    have hmove := tmMoveWord_computesInTime kWork2 kWork0 kSched (by decide) (by decide) (by decide)
      (b :: w') (encodeWordStack ws ++ encodeDelimWord [] ++ tW2) [] (acc ++ tSch)
      (mkTapes8 [] [] [] [] tW3 tW4 tW5 [])
    simp only [update_mkTapes8_kWork2, update_mkTapes8_kWork0, update_mkTapes8_kSched] at hmove
    rcases hmove with ⟨hbody⟩
    have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete
      kWork2 (tmMoveWord kWork2 kWork0 kSched) hbody
    have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
    rcases bmSchedPopToSchedLoop_computesInTime ws (fun u hu => hne u (List.mem_cons_of_mem _ hu))
      (encodeDelimWord (b :: w') ++ acc) tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, ⟨hih⟩⟩
    simp only [List.append_assoc] at hstep1 hih ⊢
    have hcomb := EvalsToInTime.trans' hstep1 hih
    have hrev : encodeWordStack ((b :: w') :: ws).reverse ++ (acc ++ tSch) =
        encodeWordStack ws.reverse ++ (encodeDelimWord (b :: w') ++ (acc ++ tSch)) := by
      simp [encodeWordStack_append]
    rw [hrev]
    refine ⟨((2 * (b :: w').length + 4) + 1) + t2, ?_, ⟨hcomb⟩⟩
    simp only [encodeWordStack_cons, List.length_append, length_encodeDelimWord, List.length_cons]
    omega

theorem length_encLeafSchedule_le (K p B_in : ℕ)
    (tbl : Fin (2 ^ K) → FixedComplex (qBaseEll K p)) :
    (encLeafSchedule K p B_in tbl).length ≤
      16 * K + 16 * p + 8 * B_in + 2 * (2 ^ K * (48 * qBaseEll K p + 18)) + 30 := by
  unfold encLeafSchedule
  have htbl := length_encLeafTwiddleTable_le K p tbl
  simp only [length_encPair, length_encUnary, id]
  omega

set_option maxHeartbeats 800000 in
theorem bmSchedTopDownLoopWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime) (K : ℕ) :
    ∀ (p B_in : ℕ) (_hB : B_in ≤ p) (tW2 tW3 tW4 tW5 tSch : List Bool),
      (encScheduleStream (computeScheduleIntTree K p B_in)).length ≤
        20 * scheduleTreeGenOps (scaledSubMulCost mulTime) K p ∧
      ∃ t ≤ 6500000000000 * scheduleTreeGenOps (scaledSubMulCost mulTime) K p,
        (bmSchedTopDownLoopWith bmMul).ComputesInTime
          (mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
            [] [] tW2 tW3 tW4 tW5 tSch)
          (mkTapes8 [] [] []
            (encodeWordStack (schedLevelWords (computeScheduleIntTree K p B_in)).reverse ++ tW2)
            tW3 tW4 tW5 tSch) t := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in hB tW2 tW3 tW4 tW5 tSch
    rw [computeScheduleIntTree, scheduleTreeGenOps]
    let St := Unit
    let uKP : St → List Bool := fun _ => encPair encUnary encUnary (K, p)
    let uB : St → List Bool := fun _ => encUnary B_in
    let uIn : St → List Bool := encDepPair uKP uB
    have pKP := StageEval.fst uKP uB
    have pCond := StageEval.seq pKP
      (StageEval.of_computesStageLe bmIsInternalNode_computesStageLe (fun _ : St => (K, p)))
    by_cases hcond : (!isBaseLeaf K p) = true ∧ 2 ≤ K
    · rw [if_pos hcond, if_pos hcond]
      rcases hcond with ⟨hleaf, hK2⟩
      have hcond_bool : isInternalScheduleNode K p = true :=
        (isInternalScheduleNode_eq_true_iff K p).mpr ⟨hleaf, hK2⟩
      have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      have hB_child : childScheduleBIn K p B_in ≤ pChildEll K p :=
        childScheduleBIn_le_pChildEll_of_internal hleaf hK2 hB
      let q := qChildEll K p
      let t1 := t1Ell K
      let m1 := computeM1Ell K p
      let r := rEll K
      let S_term := scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q)
      let expRoot := expTwoPiIFixedWithMul (· * ·) q
      let nodeSched := encNodeSchedule K p B_in m1
        (memoizeFilterTap m1 (computeFilterTapFixedWithMul (· * ·) K p))
        (memoizeFin (fun k2 => expRoot (k2.val : ℤ) (2 * r)))
        (memoizeFin (fun k2 => expRoot (-(k2.val : ℤ)) (2 * r)))
        (memoizeFin (computePassbandC0MantissaWithMul (· * ·) K p))
        (memoizeFin (computePassbandC1MantissaWithMul (· * ·) K p))
      let wNode := encPair encBool id (true, nodeSched)
      let nextParams := encPair (encPair encUnary encUnary) encUnary
        ((k2Ell K, pChildEll K p), childScheduleBIn K p B_in)
      have pNode := StageEval.const (S := St)
        (bmNodeScheduleWith_computesInTime hmul K p B_in hleaf hK2)
      have pTrue := StageEval.of_computesStageLe
        (bmConstBool_computesStageLe true (encPair (encPair encUnary encUnary) encUnary))
        (fun _ : St => ((K, p), B_in))
      have pNext := StageEval.of_computesStageLe bmNextScheduleParams_computesStageLe
        (fun _ : St => ((K, p), B_in))
      have pThen := StageEval.fanout (StageEval.fanout pTrue pNode) pNext
      have pStepCompute := StageEval.ite
        (mFalse := bmFanout (bmFanout (bmConstBool false) (bmLeafScheduleWith bmMul)) bmUnaryZero)
        (bFalse := fun _ => 0)
        pCond
        (fun s _ => pThen s)
        (fun _ hs => by rw [hcond_bool] at hs; cases hs)
      rcases pStepCompute () tW2 tW3 tW4 tW5 tSch with ⟨t_comp, ht_comp, hcomp⟩
      clear pKP pCond pNode pTrue pNext pThen pStepCompute
      rcases bmUnwrapToWork2_computesInTime wNode nextParams tW2 tW3 tW4 tW5 tSch with
        ⟨t_unw, ht_unw, hunw⟩
      rcases hcomp.seq hunw with ⟨hbody_eval⟩
      have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete
        kIO (bmSchedTopDownStepWith bmMul) hbody_eval
      have hpop : (bmSchedTopDownLoopWith bmMul).toFinTM2.step
          ⟨some none, default,
            mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
              [] [] tW2 tW3 tW4 tW5 tSch⟩ =
          some ⟨some (some (bmSchedTopDownStepWith bmMul).main), default,
            mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
              [] [] tW2 tW3 tW4 tW5 tSch⟩ :=
        step_loopNonEmptyWord_kIO_of_ne_nil (bmSchedTopDownStepWith bmMul)
          (encPair_ne_nil (encPair encUnary encUnary) encUnary ((K, p), B_in))
          [] [] tW2 tW3 tW4 tW5 tSch
      have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
      rcases ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in) hB_child
        (encodeDelimWord wNode ++ tW2) tW3 tW4 tW5 tSch with ⟨hlen_ch, t_ch, ht_ch, ⟨hch_eval⟩⟩
      have hcomb := EvalsToInTime.trans' hstep1 hch_eval
      have hnode_len := length_encNodeSchedule_le K p B_in m1
        (memoizeFilterTap m1 (computeFilterTapFixedWithMul (· * ·) K p))
        (memoizeFin (fun k2 => expRoot (k2.val : ℤ) (2 * r)))
        (memoizeFin (fun k2 => expRoot (-(k2.val : ℤ)) (2 * r)))
        (memoizeFin (computePassbandC0MantissaWithMul (· * ·) K p))
        (memoizeFin (computePassbandC1MantissaWithMul (· * ·) K p))
      have hwNode_len : wNode.length = 2 * nodeSched.length + 6 := by
        simp [wNode, encPair, encBool]
      have hk2_le : k2Ell K ≤ K := by unfold k2Ell; omega
      have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
      have hpC_eq : pChildEll K p = p + 2 * K + 12 := pChildEll_eq K p
      have hm1_le : m1 ≤ q := by
        have := computeM1Ell_le_pChildEll K p
        dsimp [m1]; omega
      have hnext_len : nextParams.length ≤ 16 * q := by
        simp only [nextParams, length_encPair, length_encUnary]
        omega
      have hS_lin0 := linear_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q) (by omega)
      have hcube := cube_le_scheduleSeriesTerms q (scaledSubMulCost mulTime q)
      have hq14 : 14 ≤ q := by omega
      have hq3_ge : 196 * q ≤ q * q * q := by
        have h1 : 196 ≤ q * q := by nlinarith only [hq14]
        calc 196 * q ≤ (q * q) * q := Nat.mul_le_mul_right q h1
          _ = q * q * q := by ring
      have hS_big : 23520 * q ≤ S_term := by
        calc 23520 * q = 120 * (196 * q) := by ring
          _ ≤ 120 * (q * q * q) := Nat.mul_le_mul_left 120 hq3_ge
          _ ≤ S_term := hcube
      have hS_tap : 32 * (8 * q + 30) ≤ S_term := by dsimp only [S_term] at *; omega
      have hS_tw : 64 * (80 * q + 18) ≤ S_term := by dsimp only [S_term] at *; omega
      have hS_gh : 64 * (40 * q + 10) ≤ S_term := by dsimp only [S_term] at *; omega
      have htap_S : 8 * (t1 * ((2 * m1 + 1) * (8 * q + 30))) ≤ (t1 * (2 * m1 + 1)) * S_term := by
        have h1 : 8 * (8 * q + 30) ≤ S_term := by omega
        have hm := Nat.mul_le_mul_left (t1 * (2 * m1 + 1)) h1
        have hr1 : 8 * (t1 * ((2 * m1 + 1) * (8 * q + 30))) =
            (t1 * (2 * m1 + 1)) * (8 * (8 * q + 30)) := by ring
        omega
      have htw_S : 32 * (r * (80 * q + 18)) ≤ r * S_term := by
        have h1 : 32 * (80 * q + 18) ≤ S_term := by omega
        have hm := Nat.mul_le_mul_left r h1
        have hr1 : 32 * (r * (80 * q + 18)) = r * (32 * (80 * q + 18)) := by ring
        omega
      have hgh_S : 16 * (r * (40 * q + 10)) ≤ r * S_term := by
        have h1 : 16 * (40 * q + 10) ≤ S_term := by omega
        have hm := Nat.mul_le_mul_left r h1
        have hr1 : 16 * (r * (40 * q + 10)) = r * (16 * (40 * q + 10)) := by ring
        omega
      have hr_pos : 1 ≤ r := rEll_pos K
      have ht1_pos : 1 ≤ t1 := t1Ell_pos K
      have hS_r : S_term ≤ r * S_term := Nat.le_mul_of_pos_left S_term hr_pos
      have hq_S : q ≤ S_term := by dsimp only [S_term] at *; omega
      have h1_S : 1 ≤ S_term := by dsimp only [S_term] at *; omega
      have hentries_assoc :
          scheduleNodeTableEntries K p * scheduleSeriesTerms q * (q + scaledSubMulCost mulTime q) =
          (t1 * (2 * m1 + 1)) * S_term + 4 * (r * S_term) := by
        dsimp only [scheduleNodeTableEntries, t1, m1, r, S_term]
        ring
      have hcomb_S :
          (t1 * (2 * m1 + 1) + r) * S_term = (t1 * (2 * m1 + 1)) * S_term + r * S_term := by ring
      have hp_cube : 500 * p * p * p + 1200 * p * p ≤ 20 * S_term := by
        have hp_q : p ≤ q := by omega
        have hp2_q2 : p * p ≤ q * q := Nat.mul_le_mul hp_q hp_q
        have hp3_q3 : p * p * p ≤ q * q * q := Nat.mul_le_mul hp2_q2 hp_q
        have hq2_q3 : q * q ≤ q * q * q := by
          calc q * q = (q * q) * 1 := (mul_one _).symm
            _ ≤ (q * q) * q := Nat.mul_le_mul_left (q * q) (by omega)
        calc 500 * p * p * p + 1200 * p * p
            = 500 * (p * p * p) + 1200 * (p * p) := by ring
          _ ≤ 500 * (q * q * q) + 1200 * (q * q * q) :=
              Nat.add_le_add (Nat.mul_le_mul_left 500 hp3_q3)
                (Nat.mul_le_mul_left 1200 (le_trans hp2_q2 hq2_q3))
          _ = 1700 * (q * q * q) := by ring
          _ ≤ 20 * (120 * (q * q * q)) := by
              rw [show 20 * (120 * (q * q * q)) = 2400 * (q * q * q) by ring]
              exact Nat.mul_le_mul_right _ (by decide)
          _ ≤ 20 * S_term := Nat.mul_le_mul_left 20 hcube
      dsimp only at ht_comp ht_unw
      dsimp only [uIn, uKP, uB, id] at ht_comp ht_unw
      rw [hcond_bool] at ht_comp
      simp only [↓reduceIte, length_encDepPair, length_encPair, length_encUnary, encBool,
        List.length_singleton] at ht_comp ht_unw
      dsimp only [q, t1, m1, r, S_term, nodeSched, wNode, nextParams, expRoot] at *
      constructor
      · simp only [encScheduleStream_node, List.length_append, length_encodeDelimWord,
          length_encPair, encBool, List.length_singleton, id]
        omega
      · simp only [schedLevelWords, List.reverse_cons, encodeWordStack_append,
          encodeWordStack_cons, encodeWordStack_nil, List.append_nil, List.append_assoc]
        refine ⟨((t_comp + t_unw) + 1) + t_ch, ?_, ⟨hcomb⟩⟩
        omega
    · rw [if_neg hcond, if_neg hcond]
      have hcond_bool : isInternalScheduleNode K p = false :=
        Bool.eq_false_iff.mpr (fun h => hcond ((isInternalScheduleNode_eq_true_iff K p).mp h))
      let qBase := qBaseEll K p
      let S_leaf := scheduleSeriesTerms qBase * (qBase + scaledSubMulCost mulTime qBase)
      let expLeaf := expTwoPiIFixedWithMul (· * ·) qBase
      let leafSched := encLeafSchedule K p B_in
        (memoizeFin (fun u => expLeaf (u.val : ℤ) (2 ^ K)))
      let wLeaf := encPair encBool id (false, leafSched)
      have pLeaf := StageEval.const (S := St) (bmLeafScheduleWith_computesInTime hmul K p B_in)
      have pFalse := StageEval.of_computesStageLe
        (bmConstBool_computesStageLe false (encPair (encPair encUnary encUnary) encUnary))
        (fun _ : St => ((K, p), B_in))
      have pZero := StageEval.constEmpty uIn
      have pElse := StageEval.fanout (StageEval.fanout pFalse pLeaf) pZero
      have pStepCompute := StageEval.congr_out
        (v2 := fun _ => encPair id id (wLeaf, ([] : List Bool)))
        (StageEval.ite
          (mTrue := bmFanout (bmFanout (bmConstBool true) (bmNodeScheduleWith bmMul)) bmNextScheduleParams)
          (bTrue := fun _ => 0)
          pCond
          (fun _ hs => by rw [hcond_bool] at hs; cases hs)
          (fun s _ => pElse s))
        (fun _ => rfl)
      rcases pStepCompute () tW2 tW3 tW4 tW5 tSch with ⟨t_comp, ht_comp, hcomp⟩
      clear pKP pCond pLeaf pFalse pZero pElse pStepCompute
      rcases bmUnwrapToWork2_computesInTime wLeaf [] tW2 tW3 tW4 tW5 tSch with
        ⟨t_unw, ht_unw, hunw⟩
      rcases hcomp.seq hunw with ⟨hbody_eval⟩
      have hbody_lifted := BitMachine.loopNonEmptyWord_body_evalsToInTime_concrete
        kIO (bmSchedTopDownStepWith bmMul) hbody_eval
      have hpop : (bmSchedTopDownLoopWith bmMul).toFinTM2.step
          ⟨some none, default,
            mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
              [] [] tW2 tW3 tW4 tW5 tSch⟩ =
          some ⟨some (some (bmSchedTopDownStepWith bmMul).main), default,
            mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
              [] [] tW2 tW3 tW4 tW5 tSch⟩ :=
        step_loopNonEmptyWord_kIO_of_ne_nil (bmSchedTopDownStepWith bmMul)
          (encPair_ne_nil (encPair encUnary encUnary) encUnary ((K, p), B_in))
          [] [] tW2 tW3 tW4 tW5 tSch
      have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
      have hhalt : StateTransition.EvalsToInTime (bmSchedTopDownLoopWith bmMul).toFinTM2.step
          ⟨some none, default,
            mkTapes8 (encodeDelimWord []) [] [] (encodeDelimWord wLeaf ++ tW2) tW3 tW4 tW5 tSch⟩
          (some ⟨none, default,
            mkTapes8 [] [] [] (encodeDelimWord wLeaf ++ tW2) tW3 tW4 tW5 tSch⟩) 1 := by
        refine EvalsToInTime.step_one ?_
        simp only [bmSchedTopDownLoopWith, BitMachine.loopNonEmptyWord, BitMachine.toFinTM2,
          mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux,
          encodeDelimWord_nil, mkTapes8_kIO, List.head?_cons, List.tail_cons,
          Option.getD_some, cond_true, update_mkTapes8_kIO]
      have hcomb := EvalsToInTime.trans' hstep1 hhalt
      have hleaf_len := length_encLeafSchedule_le K p B_in
        (memoizeFin (fun u => expLeaf (u.val : ℤ) (2 ^ K)))
      have hwLeaf_len : wLeaf.length = 2 * leafSched.length + 6 := by
        simp [wLeaf, encPair, encBool]
      have hqBase_eq : qBase = p + K + 4 := rfl
      have hS_lin0 := linear_le_scheduleSeriesTerms qBase (scaledSubMulCost mulTime qBase) (by omega)
      have hS_tw : 48 * qBase + 18 ≤ S_leaf := by dsimp only [S_leaf] at *; omega
      have htw_S : 2 ^ K * (48 * qBase + 18) ≤ 2 ^ K * S_leaf := Nat.mul_le_mul_left (2 ^ K) hS_tw
      have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
      have hS_2K : S_leaf ≤ 2 ^ K * S_leaf := Nat.le_mul_of_pos_left S_leaf h2K_pos
      have hq_S : qBase ≤ S_leaf := by dsimp only [S_leaf] at *; omega
      have h1_S : 1 ≤ S_leaf := by dsimp only [S_leaf] at *; omega
      have hleaf_assoc :
          2 ^ K * scheduleSeriesTerms qBase * (qBase + scaledSubMulCost mulTime qBase) =
          2 ^ K * S_leaf := by
        dsimp only [S_leaf]
        ring
      have hcube := cube_le_scheduleSeriesTerms qBase (scaledSubMulCost mulTime qBase)
      have hp_cube : 500 * p * p * p + 1200 * p * p ≤ 20 * S_leaf := by
        have hp_q : p ≤ qBase := by omega
        have hp2_q2 : p * p ≤ qBase * qBase := Nat.mul_le_mul hp_q hp_q
        have hp3_q3 : p * p * p ≤ qBase * qBase * qBase := Nat.mul_le_mul hp2_q2 hp_q
        have hq2_q3 : qBase * qBase ≤ qBase * qBase * qBase := by
          calc qBase * qBase = (qBase * qBase) * 1 := (mul_one _).symm
            _ ≤ (qBase * qBase) * qBase := Nat.mul_le_mul_left (qBase * qBase) (by omega)
        calc 500 * p * p * p + 1200 * p * p
            = 500 * (p * p * p) + 1200 * (p * p) := by ring
          _ ≤ 500 * (qBase * qBase * qBase) + 1200 * (qBase * qBase * qBase) :=
              Nat.add_le_add (Nat.mul_le_mul_left 500 hp3_q3)
                (Nat.mul_le_mul_left 1200 (le_trans hp2_q2 hq2_q3))
          _ = 1700 * (qBase * qBase * qBase) := by ring
          _ ≤ 20 * (120 * (qBase * qBase * qBase)) := by
              rw [show 20 * (120 * (qBase * qBase * qBase)) = 2400 * (qBase * qBase * qBase) by ring]
              exact Nat.mul_le_mul_right _ (by decide)
          _ ≤ 20 * S_leaf := Nat.mul_le_mul_left 20 hcube
      dsimp only at ht_comp ht_unw
      dsimp only [uIn, uKP, uB, id] at ht_comp ht_unw
      rw [hcond_bool] at ht_comp
      simp only [Bool.false_eq_true, ↓reduceIte, length_encDepPair, length_encPair,
        length_encUnary, encBool, List.length_singleton, List.length_nil] at ht_comp ht_unw
      dsimp only [qBase, S_leaf, leafSched, wLeaf, expLeaf] at *
      constructor
      · simp only [encScheduleStream_leaf, length_encodeDelimWord, length_encPair,
          encBool, List.length_singleton, id]
        omega
      · simp only [schedLevelWords, List.reverse_singleton, encodeWordStack_cons,
          encodeWordStack_nil, List.append_nil]
        refine ⟨((t_comp + t_unw) + 1) + 1, ?_, ⟨hcomb⟩⟩
        omega

/-- **Complete Uniform `BitMachine` Theorem for Multi-Level Schedule Tree Generation
(`bmScheduleTreeWith_computesInTime`, Section 3.3 (`sec:tables`) and equation (8) (`eq:table-precomp`))**:
Given `((K, p), B_in)` (`B_in ≤ p`) on `kIO`, `bmScheduleTreeWith bmMul` generates and pushes
`encScheduleStream (computeScheduleIntTree K p B_in)` onto `kSched` in
`t ≤ 7000000000000 * scheduleTreeGenOps (scaledSubMulCost mulTime) K p` steps. -/
theorem bmScheduleTreeWith_computesInTime {bmMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmMul mulTime)
    (K p B_in : ℕ) (hB : B_in ≤ p) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 7000000000000 * scheduleTreeGenOps (scaledSubMulCost mulTime) K p,
      (bmScheduleTreeWith bmMul).ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord []) [] [] tW2 tW3 tW4 tW5
          (encScheduleStream (computeScheduleIntTree K p B_in) ++ tSch)) t := by
  have hpush1 := tmPushEmpty_computesInTime kWork2
    (mkTapes8 (encodeDelimWord (encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)))
      [] [] tW2 tW3 tW4 tW5 tSch)
  simp only [update_mkTapes8_kWork2, mkTapes8_kWork2] at hpush1
  rcases bmSchedTopDownLoopWith_computesInTime hmul K p B_in hB
    (encodeDelimWord [] ++ tW2) tW3 tW4 tW5 tSch with ⟨hlen_stream, t_top, ht_top, htop⟩
  let ws := (schedLevelWords (computeScheduleIntTree K p B_in)).reverse
  have hne : ∀ w ∈ ws, w ≠ [] := by
    intro w hw
    exact schedLevelWords_mem_ne_nil _ w (List.mem_reverse.mp hw)
  rcases bmSchedPopToSchedLoop_computesInTime ws hne [] tW2 tW3 tW4 tW5 tSch with
    ⟨t_pop, ht_pop, hpop⟩
  simp only [ws, List.reverse_reverse, List.nil_append, List.append_assoc] at hpop ht_pop
  rw [length_encodeWordStack_reverse] at ht_pop
  change t_pop ≤ 3 * (encScheduleStream (computeScheduleIntTree K p B_in)).length + 1 at ht_pop
  have hpush2 := tmPushEmpty_computesInTime kIO
    (mkTapes8 [] [] [] tW2 tW3 tW4 tW5
      (encScheduleStream (computeScheduleIntTree K p B_in) ++ tSch))
  simp only [update_mkTapes8_kIO, mkTapes8_kIO, List.append_nil] at hpush2
  have hall := hpush1.seq (htop.seq (hpop.seq hpush2))
  have hops_pos : 1 ≤ scheduleTreeGenOps (scaledSubMulCost mulTime) K p := by
    rw [scheduleTreeGenOps]
    split_ifs with hcond
    · have hq : 4 ≤ qChildEll K p := by have := qChildEll_eq K p; omega
      have h1 := linear_le_scheduleSeriesTerms (qChildEll K p)
        (scaledSubMulCost mulTime (qChildEll K p)) (by omega)
      have hr : 1 ≤ rEll K := rEll_pos K
      have hent : 1 ≤ scheduleNodeTableEntries K p := by
        unfold scheduleNodeTableEntries; omega
      have hm := Nat.mul_le_mul hent (show 1 ≤ scheduleSeriesTerms (qChildEll K p) *
        (qChildEll K p + scaledSubMulCost mulTime (qChildEll K p)) by omega)
      have hassoc : scheduleNodeTableEntries K p *
          (scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + scaledSubMulCost mulTime (qChildEll K p))) =
          scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + scaledSubMulCost mulTime (qChildEll K p)) := by ring
      omega
    · have hq : 4 ≤ qBaseEll K p := by unfold qBaseEll; omega
      have h1 := linear_le_scheduleSeriesTerms (qBaseEll K p)
        (scaledSubMulCost mulTime (qBaseEll K p)) (by omega)
      have h2K : 1 ≤ 2 ^ K := Nat.one_le_two_pow
      have hm := Nat.mul_le_mul h2K (show 1 ≤ scheduleSeriesTerms (qBaseEll K p) *
        (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p)) by omega)
      have hassoc : 2 ^ K *
          (scheduleSeriesTerms (qBaseEll K p) *
            (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p))) =
          2 ^ K * scheduleSeriesTerms (qBaseEll K p) *
            (qBaseEll K p + scaledSubMulCost mulTime (qBaseEll K p)) := by ring
      omega
  refine ⟨1 + (t_top + (t_pop + 1)), ?_, hall⟩
  omega

end IntMul



