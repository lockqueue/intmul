import IntMul.TMFastDFTRecursive
import IntMul.EndToEnd

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-!
# End-to-End Uniform 8-Stack `Turing.FinTM2` $O(n \log n)$ Integer Multiplier (`IntMul.TMEndToEnd`)

This module completes the end-to-end compilation of the sinc-Gaussian fractional-shift
polynomial-transform (`syntheticFFT` in this development) integer multiplication pipeline into a
single, concrete, inhabited, parameter-free uniform 8-stack binary machine
`tmIntMul : Turing.FinTM2` (`Fintype.card tmIntMul.Λ = (bmRunRaw bmIntMulCore).numLabels = O(1)`,
`Fintype.card σ = 32`, `Fintype.card (Γ k) = 2`, `Fintype.card K = 8`, independent of
$n, K, p, R, A, B$), and proves the unconditional single-statement coupled correctness and
$O(n \log n)$ `TM2.step` transition-bound theorem (`tmIntMul_evalsToInTime_n_log_n`,
Theorem 2 (`thm:lean`) in Section 1.2 (`sec:intro-results`) and Section 8 (`sec:lean`)):
$$\exists C > 0,\ \forall n \ge 2,\ \forall A, B < 2^n,\ \exists t \le C \cdot n \cdot \lfloor\log_2 n\rfloor,\
  \text{Turing.EvalsToInTime } \text{tmIntMul.step }
    (\text{Turing.initList tmIntMul } (\text{encodeInputBits } n\ A\ B))\
    (\text{some } (\text{Turing.haltList tmIntMul } (\text{encodeNatBits } (2 * n)\ (A * B))))\ t.$$
-/

namespace IntMul

open Turing StageEval

/-! ## 1. Positive-Domain Congruence & Scaling for `intMulAlgorithmSteps` -/

/-- `scheduleTreeGenOps M K p` depends on `M` only at positive widths `q ≥ 1`. -/
theorem scheduleTreeGenOps_congr_pos {M1 M2 : ℕ → ℕ}
    (hM : ∀ q, 1 ≤ q → M1 q = M2 q) (K : ℕ) :
    ∀ p : ℕ, scheduleTreeGenOps M1 K p = scheduleTreeGenOps M2 K p := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p
    conv_lhs => rw [scheduleTreeGenOps]
    conv_rhs => rw [scheduleTreeGenOps]
    split_ifs with hcond
    · have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      have hq1 : 1 ≤ qChildEll K p := by have := qChildEll_eq K p; omega
      have hrec := ih (k2Ell K) hk2_lt (pChildEll K p)
      rw [hM (qChildEll K p) hq1, hrec]
    · have hq1 : 1 ≤ qBaseEll K p := by unfold qBaseEll; omega
      rw [hM (qBaseEll K p) hq1]

/-- `fastDFTRecursiveSteps M K p B_in` depends on `M` only at positive widths `q ≥ 1` whenever `18 ≤ p`. -/
theorem fastDFTRecursiveSteps_congr_pos {M1 M2 : ℕ → ℕ}
    (hM : ∀ q, 1 ≤ q → M1 q = M2 q) (K : ℕ) :
    ∀ (p B_in : ℕ), 18 ≤ p →
      fastDFTRecursiveSteps M1 K p B_in = fastDFTRecursiveSteps M2 K p B_in := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in hp
    conv_lhs => rw [fastDFTRecursiveSteps]
    conv_rhs => rw [fastDFTRecursiveSteps]
    split_ifs with hcond
    · have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      have hm1_pos : 1 ≤ computeM1Ell K p := computeM1Ell_pos K p
      have hr_pos : 1 ≤ rEll K := rEll_pos K
      have hW_pos : 1 ≤ foldedHalfWidth (computeM1Ell K p) (rEll K) := by
        unfold foldedHalfWidth
        exact le_min hm1_pos hr_pos
      have hB_pos : 1 ≤ scheduleSlotBits K p B_in (computeM1Ell K p) :=
        kroneckerSlotBitsRaw_pos _ _ _ _
      have hQ_pos : 1 ≤ kroneckerPackedBitLength
          (foldedHalfWidth (computeM1Ell K p) (rEll K))
          (scheduleSlotBits K p B_in (computeM1Ell K p)) := by
        unfold kroneckerPackedBitLength
        exact Nat.mul_pos (by omega) hB_pos
      have hqc_pos : 1 ≤ qChildEll K p := by have := qChildEll_eq K p; omega
      have hmuls : stepFixedPointMuls K p B_in M1 = stepFixedPointMuls K p B_in M2 := by
        unfold stepFixedPointMuls
        dsimp only
        rw [hM _ hQ_pos, hM _ hqc_pos]
      have hp_child : 18 ≤ pChildEll K p := by have := pChildEll_eq K p; omega
      have hrec := ih (k2Ell K) hk2_lt (pChildEll K p)
        (childScheduleBIn K p B_in) hp_child
      rw [hmuls, hrec]
    · unfold leafDFTOps
      have hqb_pos : 1 ≤ qBaseEll K p := by unfold qBaseEll; omega
      rw [hM (qBaseEll K p) hqb_pos]

/-- `intMulAlgorithmSteps M n` depends on `M` only at positive widths `q ≥ 1`. -/
theorem intMulAlgorithmSteps_congr_pos {M1 M2 : ℕ → ℕ}
    (hM : ∀ q, 1 ≤ q → M1 q = M2 q) (n : ℕ) :
    intMulAlgorithmSteps M1 n = intMulAlgorithmSteps M2 n := by
  unfold intMulAlgorithmSteps
  have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
  rw [scheduleTreeGenOps_congr_pos hM (rootK0 n) (rootP0 n),
    fastDFTRecursiveSteps_congr_pos hM (rootK0 n) (rootP0 n)
      (levelScheduleBIn (rootK0 n) (rootP0 n) 0) hp0,
    hM (rootP0 n + 2) (by omega)]

/-- Bounded positive-domain scaling of `intMulAlgorithmSteps`: if `M1 q ≤ C * M2 q` for all
`1 ≤ q ≤ 2736 * (rootP0 n * rootP0 n)`, then `intMulAlgorithmSteps M1 n ≤ C * intMulAlgorithmSteps M2 n`. -/
theorem intMulAlgorithmSteps_scale_le_of_pos_bounded {M1 M2 : ℕ → ℕ} {n C : ℕ} (hC : 1 ≤ C)
    (hM : ∀ q, 1 ≤ q → q ≤ 2736 * (rootP0 n * rootP0 n) → M1 q ≤ C * M2 q) :
    intMulAlgorithmSteps M1 n ≤ C * intMulAlgorithmSteps M2 n := by
  let M1' : ℕ → ℕ := fun q => if q = 0 then 0 else M1 q
  have hcongr : intMulAlgorithmSteps M1 n = intMulAlgorithmSteps M1' n :=
    intMulAlgorithmSteps_congr_pos (fun q hq => by dsimp [M1']; rw [if_neg (by omega)]) n
  rw [hcongr]
  refine intMulAlgorithmSteps_scale_le_of_bounded hC (fun q hq => ?_)
  dsimp [M1']
  split_ifs with h0
  · exact Nat.zero_le _
  · exact hM q (by omega) hq

/-! ## 2. Chunk Slicing & Fixed-Point Complex Packing (`bmPackSingleChunk`, `bmPackChunkPair`, `bmFastNatMulPrep`) -/

theorem map_finRange_sliceBitChunkFn (b R : ℕ) (bs : List Bool) :
    (List.finRange R).map (sliceBitChunkFn b R bs) = sliceBitChunks b R bs := by
  rw [sliceBitChunkFn_eq_natChunkFn, sliceBitChunks_eq_extractNatChunks]
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp [getElem_extractNatChunks]

theorem sliceBitChunkFn_lt (b R : ℕ) (bs : List Bool) (i : Fin R) :
    sliceBitChunkFn b R bs i < 2 ^ b := by
  rw [sliceBitChunkFn_eq_natChunkFn, natChunkFn_eq_natChunk]
  unfold natChunk
  exact Nat.mod_lt _ (Nat.two_pow_pos b)

theorem mem_sliceBitChunks_lt {b R : ℕ} {bs : List Bool} {c : ℕ}
    (hc : c ∈ sliceBitChunks b R bs) : c < 2 ^ b := by
  rw [← map_finRange_sliceBitChunkFn] at hc
  rcases List.mem_map.mp hc with ⟨i, _, rfl⟩
  exact sliceBitChunkFn_lt b R bs i

/-- Convert an unsigned chunk `encNatWord b c = encodeNatBits b c` (`c < 2 ^ b`) with context
`(W_io, sh)` (`sh + b ≤ W_io`) into `encodeSignedWord W_io ((c : ℤ) * (2 : ℤ) ^ sh)`. -/
def bmPackSingleChunk : BitMachine :=
  let bmWOut := bmSeq bmFst bmFst
  let bmSh := bmSeq bmFst bmSnd
  let bmCSigned := bmSeq bmSnd (bmSeq (bmFanout bmLenUnary bmId) bmNatToSigned)
  let bmShifted := bmSeq (bmFanout bmSh bmCSigned) bmShiftLeftSigned
  bmSeq (bmFanout bmWOut bmShifted) bmResizeSignedWord

theorem bmPackSingleChunk_computesInTime (W_io sh b c : ℕ)
    (hc : c < 2 ^ b) (hW : sh + b ≤ W_io)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 6000 * W_io + 6000 * sh + 6000 * b + 20000,
      bmPackSingleChunk.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encNatWord b) ((W_io, sh), c)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeSignedWord W_io ((c : ℤ) * (2 : ℤ) ^ sh)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uCtx : S → List Bool := fun _ => encPair encUnary encUnary (W_io, sh)
  let uC : S → List Bool := fun _ => encodeNatBits b c
  have hc_fits : FitsSignedWord b (c : ℤ) := by
    rw [fitsSignedWord_iff_natAbs_lt, Int.natAbs_natCast]
    exact hc
  have hsh_fits : FitsSignedWord (sh + b) ((c : ℤ) * (2 : ℤ) ^ sh) := by
    simpa [Nat.add_comm] using hc_fits.mul_two_pow sh
  have hW_fits : FitsSignedWord W_io ((c : ℤ) * (2 : ℤ) ^ sh) := hsh_fits.mono hW
  have pFst := StageEval.fst uCtx uC
  have pSnd := StageEval.snd uCtx uC
  have pWOut := StageEval.seq pFst
    (StageEval.fst (fun _ : S => encUnary W_io) (fun _ : S => encUnary sh))
  have pSh := StageEval.seq pFst
    (StageEval.snd (fun _ : S => encUnary W_io) (fun _ : S => encUnary sh))
  have pLenC : StageEval (S := S) bmLenUnary uC (fun _ => encUnary b) (fun _ => 4 * b + 6) :=
    (StageEval.congr_out (v2 := fun _ => encUnary b)
      (StageEval.of_computesStageLe (bmLenUnary_computesStageLe encBits) (fun _ : S => encodeNatBits b c))
      (fun _ => by simp [encBits])).mono (fun _ => by simp [encBits])
  have pCSigned := StageEval.seq pSnd
    (StageEval.seq (StageEval.fanout pLenC (StageEval.id_stage uC))
      (StageEval.const (S := S) (bmNatToSigned_computesInTime b b c hc hc)))
  have pShifted := StageEval.seq (StageEval.fanout pSh pCSigned)
    (StageEval.const (S := S) (bmShiftLeftSigned_computesInTime sh b (c : ℤ) hc_fits))
  have hall := StageEval.seq (StageEval.fanout pWOut pShifted)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime (sh + b) W_io ((c : ℤ) * (2 : ℤ) ^ sh) hsh_fits hW_fits))
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uCtx, uC, encNatWord] at ht hcomp ⊢
  simp only [length_encDepPair, length_encPair, length_encUnary,
    length_encodeSignedWord, encodeNatBits_length] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Pack a pair of unsigned chunks `(a_i, b_i)` with context `(W_io, sh)` into
`encComplex W_io ⟨(a_i : ℤ) * 2^sh, (b_i : ℤ) * 2^sh⟩`. -/
def bmPackChunkPair : BitMachine :=
  bmFanout
    (bmSeq (bmMapSnd bmFst) bmPackSingleChunk)
    (bmSeq (bmMapSnd bmSnd) bmPackSingleChunk)

theorem bmPackChunkPair_computesInTime (W_io sh b q a_i b_i : ℕ)
    (ha : a_i < 2 ^ b) (hb : b_i < 2 ^ b) (hW : sh + b ≤ W_io)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 13000 * W_io + 13000 * sh + 13000 * b + 50000,
      bmPackChunkPair.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary)
            (encPair (encNatWord b) (encNatWord b)) ((W_io, sh), (a_i, b_i))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encComplex W_io (q := q)
            ⟨(a_i : ℤ) * (2 : ℤ) ^ sh, (b_i : ℤ) * (2 : ℤ) ^ sh⟩))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uCtx : S → List Bool := fun _ => encPair encUnary encUnary (W_io, sh)
  let uA : S → List Bool := fun _ => encNatWord b a_i
  let uB : S → List Bool := fun _ => encNatWord b b_i
  have pRe := StageEval.seq
    (StageEval.mapSnd (u1 := uCtx) (StageEval.fst uA uB))
    (StageEval.const (S := S) (bmPackSingleChunk_computesInTime W_io sh b a_i ha hW))
  have pIm := StageEval.seq
    (StageEval.mapSnd (u1 := uCtx) (StageEval.snd uA uB))
    (StageEval.const (S := S) (bmPackSingleChunk_computesInTime W_io sh b b_i hb hW))
  rcases StageEval.fanout pRe pIm () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uCtx, uA, uB, encNatWord] at ht hcomp ⊢
  simp only [length_encDepPair, length_encPair, length_encUnary,
    length_encodeSignedWord, encodeNatBits_length] at ht
  exact ⟨t, by omega, hcomp⟩

theorem zipWith_packChunksFixed_eq (w : ℕ) (aBits bBits : List Bool) :
    let b := chunkBits w
    let R0 := rootR0 w
    let p0 := rootP0 w
    let sh := p0 + 2 - b
    List.zipWith
      (fun a_i b_i : ℕ =>
        (⟨(a_i : ℤ) * (2 : ℤ) ^ sh, (b_i : ℤ) * (2 : ℤ) ^ sh⟩ : FixedComplex (p0 + 2)))
      (sliceBitChunks b R0 aBits)
      (sliceBitChunks b R0 bBits) =
    (List.finRange R0).map
      (packChunksFixed w (sliceBitChunkFn b R0 aBits, sliceBitChunkFn b R0 bBits)) := by
  intro b R0 p0 sh
  rw [← map_finRange_sliceBitChunkFn b R0 aBits,
    ← map_finRange_sliceBitChunkFn b R0 bBits,
    List.zipWith_map_left, List.zipWith_map_right, List.zipWith_self]
  apply List.map_congr_left
  intro j _
  unfold packChunksFixed
  dsimp only
  rw [Nat.mod_eq_of_lt (sliceBitChunkFn_lt b R0 aBits j),
    Nat.mod_eq_of_lt (sliceBitChunkFn_lt b R0 bBits j)]

/-- **Stage A (`bmFastNatMulPrep`)**:
Consumes `encPair encUnary (encPair encBits encBits) (w, (aBits, bBits))` on `kIO`
(`aBits.length = w`, `bBits.length = w`), computes the root parameters `(w, (rootK0 w, rootP0 w))`,
slices `aBits` and `bBits` into `rootR0 w` chunks of width `chunkBits w` via `bmSliceBitChunks`,
and packs them into `encFinVec (rootR0 w) (10 * (rootP0 w + 2)) (rootP0 w + 2) zFixed`. -/
def bmFastNatMulPrep : BitMachine :=
  let bmW := bmFst
  let bmB := bmSeq bmW bmChunkBits
  let bmK0 := bmSeq bmW bmRootK0
  let bmR0 := bmSeq bmK0 bmUnaryTwoPow
  let bmP0 := bmSeq bmW bmRootP0
  let bmP0Plus2 := bmSeq bmP0 (bmSeq bmUnarySucc bmUnarySucc)
  let bmWio := bmSeq (bmFanout (bmUnaryConst 10) bmP0Plus2) bmUnaryMul
  let bmSh := bmSeq (bmFanout bmP0Plus2 bmB) bmUnarySub
  let bmABits := bmSeq bmSnd bmFst
  let bmBBits := bmSeq bmSnd bmSnd
  let bmAChunks := bmSeq (bmFanout bmR0 (bmFanout bmB bmABits)) bmSliceBitChunks
  let bmBChunks := bmSeq (bmFanout bmR0 (bmFanout bmB bmBBits)) bmSliceBitChunks
  let bmZFixed := bmSeq
    (bmFanout (bmFanout bmWio bmSh) (bmFanout bmAChunks bmBChunks))
    (bmZipWithCtx bmPackChunkPair)
  bmFanout (bmFanout bmW (bmFanout bmK0 bmP0)) bmZFixed

set_option maxHeartbeats 800000 in
theorem bmFastNatMulPrep_computesInTime (w : ℕ) (aBits bBits : List Bool)
    (ha : aBits.length = w) (hb : bBits.length = w)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let b := chunkBits w
    let K0 := rootK0 w
    let R0 := rootR0 w
    let p0 := rootP0 w
    let W_io := 10 * (p0 + 2)
    let aChunks := sliceBitChunkFn b R0 aBits
    let bChunks := sliceBitChunkFn b R0 bBits
    let zFixed := packChunksFixed w (aChunks, bChunks)
    ∃ t ≤ 500000 * R0 * p0 + 100000 * w,
      bmFastNatMulPrep.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair encUnary (encPair encBits encBits) (w, (aBits, bBits))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encFinVec R0 W_io (p0 + 2)) ((w, (K0, p0)), zFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  intro b K0 R0 p0 W_io aChunks bChunks zFixed
  let S := Unit
  let sh := p0 + 2 - b
  let aList := sliceBitChunks b R0 aBits
  let bList := sliceBitChunks b R0 bBits
  have hb4 : 4 ≤ b := chunkBits_ge_four w
  have hK02 : 2 ≤ K0 := rootK0_ge_two w
  have hR04 : 4 ≤ R0 := rootR0_ge_four w
  have hp018 : 18 ≤ p0 := rootP0_ge_eighteen w
  have hp0_eq : p0 = 2 * b + 2 * K0 + 6 := rfl
  have hb_p0 : b ≤ p0 := by omega
  have hK0_p0 : K0 ≤ p0 := by omega
  have hsh_p0 : sh ≤ p0 + 2 := Nat.sub_le (p0 + 2) b
  have hsh_b_Wio : sh + b ≤ W_io := by dsimp [sh, W_io]; omega
  have hRP_ge72 : 72 ≤ R0 * p0 := by nlinarith
  have pW := StageEval.fst
    (fun _ : S => encUnary w)
    (fun _ : S => encPair encBits encBits (aBits, bBits))
  have pAB := StageEval.snd
    (fun _ : S => encUnary w)
    (fun _ : S => encPair encBits encBits (aBits, bBits))
  have pABits := StageEval.seq pAB
    (StageEval.fst (fun _ : S => aBits) (fun _ : S => bBits))
  have pBBits := StageEval.seq pAB
    (StageEval.snd (fun _ : S => aBits) (fun _ : S => bBits))
  have pB := StageEval.seq pW
    (StageEval.of_computesStageLe bmChunkBits_computesStageLe (fun _ : S => w))
  have pK0 := StageEval.seq pW
    (StageEval.of_computesStageLe bmRootK0_computesStageLe (fun _ : S => w))
  have pR0 := StageEval.congr_out
    (v2 := fun _ : S => encUnary R0)
    (StageEval.seq pK0 (StageEval.of_computesStageLe bmUnaryTwoPow_computesStageLe (fun _ : S => K0)))
    (fun _ => rfl)
  have pP0 := StageEval.seq pW
    (StageEval.of_computesStageLe bmRootP0_computesStageLe (fun _ : S => w))
  have pP0Plus2 : StageEval (S := S)
      (bmSeq (bmSeq bmFst bmRootP0) (bmSeq bmUnarySucc bmUnarySucc))
      (fun _ => encPair encUnary (encPair encBits encBits) (w, (aBits, bBits)))
      (fun _ => encUnary (p0 + 2))
      (fun _ => 1010 * w + 6030) := by
    have pSucc2 := bmSeq_computesStageLe bmUnarySucc_computesStageLe bmUnarySucc_computesStageLe
    refine (StageEval.seq pP0 (StageEval.of_computesStageLe pSucc2 (fun _ : S => p0))).mono
      (fun _ => by simp only [length_encPair, length_encUnary, encBits, id, ha, hb]; omega)
  have p10 := StageEval.of_computesStageLe
    (bmUnaryConst_computesStageLe 10 (encPair encUnary (encPair encBits encBits)))
    (fun _ : S => (w, (aBits, bBits)))
  have pWio := StageEval.congr_out
    (v2 := fun _ : S => encUnary W_io)
    (StageEval.seq (StageEval.fanout p10 pP0Plus2)
      (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (10, p0 + 2))))
    (fun _ => rfl)
  have pSh := StageEval.congr_out
    (v2 := fun _ : S => encUnary sh)
    (StageEval.seq (StageEval.fanout pP0Plus2 pB)
      (StageEval.of_computesStageLe bmUnarySub_computesStageLe (fun _ : S => (p0 + 2, b))))
    (fun _ => rfl)
  have pAChunks := StageEval.seq
    (StageEval.fanout pR0 (StageEval.fanout pB pABits))
    (StageEval.const (S := S) (bmSliceBitChunks_computesInTime R0 b aBits))
  have pBChunks := StageEval.seq
    (StageEval.fanout pR0 (StageEval.fanout pB pBBits))
    (StageEval.const (S := S) (bmSliceBitChunks_computesInTime R0 b bBits))
  have hlen_aList : aList.length = R0 := by
    dsimp [aList]; rw [sliceBitChunks_eq_extractNatChunks, length_extractNatChunks]
  have hlen_bList : bList.length = R0 := by
    dsimp [bList]; rw [sliceBitChunks_eq_extractNatChunks, length_extractNatChunks]
  have pZip := StageEval.zipWithCtx_uniform
    (S := S)
    (ctx := fun _ => encPair encUnary encUnary (W_io, sh))
    (xs := fun _ => aList)
    (ys := fun _ => bList)
    (fun _ => by rw [hlen_aList, hlen_bList])
    (encA := fun _ => encNatWord b)
    (encB := fun _ => encNatWord b)
    (encD := fun _ => encComplex W_io (q := p0 + 2))
    (fn := fun _ a_i b_i => ⟨(a_i : ℤ) * (2 : ℤ) ^ sh, (b_i : ℤ) * (2 : ℤ) ^ sh⟩)
    (B := fun _ => 13000 * W_io + 13000 * sh + 13000 * b + 50000)
    (L_A := fun _ => b)
    (L_B := fun _ => b)
    (L_D := fun _ => 4 * W_io + 8)
    (fun p => by
      rcases mem_of_mem_zip p.property with ⟨haMem, hbMem⟩
      exact bmPackChunkPair_computesInTime W_io sh b (p0 + 2) p.val.2.1 p.val.2.2
        (mem_sliceBitChunks_lt haMem) (mem_sliceBitChunks_lt hbMem) hsh_b_Wio)
    (fun _ _ _ => by simp [encNatWord])
    (fun _ _ _ => by simp [encNatWord])
    (fun _ _ _ => by simp [length_encComplex])
  have pZFixed := StageEval.congr_out
    (v2 := fun _ : S => encFinVec R0 W_io (p0 + 2) zFixed)
    (StageEval.seq
      (StageEval.fanout (StageEval.fanout pWio pSh) (StageEval.fanout pAChunks pBChunks))
      pZip)
    (fun _ => by
      dsimp only [zFixed, aList, bList, encFinVec]
      rw [zipWith_packChunksFixed_eq w aBits bBits])
  have pCtx := StageEval.fanout pW (StageEval.fanout pK0 pP0)
  have hall := StageEval.fanout pCtx pZFixed
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [id, W_io, sh] at ht hcomp
  have hlen_encA : (encList (encNatWord b) (sliceBitChunks b R0 aBits)).length ≤ 2 * (R0 * p0) + 2 * R0 := by
    calc (encList (encNatWord b) (sliceBitChunks b R0 aBits)).length
        ≤ aList.length * (2 * b + 2) :=
          length_encList_le_of_forall_le (encNatWord b) b aList (fun _ _ => by simp [encNatWord])
      _ = R0 * (2 * b + 2) := by rw [hlen_aList]
      _ ≤ R0 * (2 * p0 + 2) := Nat.mul_le_mul_left R0 (by omega)
      _ = 2 * (R0 * p0) + 2 * R0 := by ring
  have hlen_encB : (encList (encNatWord b) (sliceBitChunks b R0 bBits)).length ≤ 2 * (R0 * p0) + 2 * R0 := by
    calc (encList (encNatWord b) (sliceBitChunks b R0 bBits)).length
        ≤ bList.length * (2 * b + 2) :=
          length_encList_le_of_forall_le (encNatWord b) b bList (fun _ _ => by simp [encNatWord])
      _ = R0 * (2 * b + 2) := by rw [hlen_bList]
      _ ≤ R0 * (2 * p0 + 2) := Nat.mul_le_mul_left R0 (by omega)
      _ = 2 * (R0 * p0) + 2 * R0 := by ring
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encFinVec,
    encBits, id, ha, hb, hlen_aList] at ht
  have hb_def : chunkBits w = b := rfl
  have hK0_def : rootK0 w = K0 := rfl
  have hp0_def : rootP0 w = p0 := rfl
  have hR0_def : 2 ^ K0 = R0 := rfl
  rw [hb_def, hK0_def, hp0_def, hR0_def] at ht
  have hsub_le : p0 + 2 - b ≤ p0 + 2 := Nat.sub_le (p0 + 2) b
  have hKR0 : 10 * K0 * R0 ≤ 10 * (R0 * p0) := by nlinarith
  have hRb : 30 * R0 * (b + 1) ≤ 30 * (R0 * p0) + 30 * R0 := by nlinarith
  have hFinVec : R0 * (8 * (10 * (p0 + 2)) + 18) = 80 * (R0 * p0) + 178 * R0 := by ring
  have hR0_le_RP : 18 * R0 ≤ R0 * p0 := by
    calc 18 * R0 = R0 * 18 := Nat.mul_comm 18 R0
      _ ≤ R0 * p0 := Nat.mul_le_mul_left R0 hp018
  have hp0_le_RP : p0 ≤ R0 * p0 := by
    calc p0 = 1 * p0 := (Nat.one_mul p0).symm
      _ ≤ R0 * p0 := Nat.mul_le_mul_right p0 (by omega)
  have hzip_prod :
      R0 * (13000 * (10 * (p0 + 2)) + 13000 * (p0 + 2 - b) + 13000 * b + 50000 +
        4 * (2 * (10 * (p0 + 2)) + 2 * (p0 + 2 - b) + 4) +
        340 * b + 340 * b + 24 * (4 * (10 * (p0 + 2)) + 8) + 600) ≤
      180000 * (R0 * p0) := by
    calc R0 * (13000 * (10 * (p0 + 2)) + 13000 * (p0 + 2 - b) + 13000 * b + 50000 +
          4 * (2 * (10 * (p0 + 2)) + 2 * (p0 + 2 - b) + 4) +
          340 * b + 340 * b + 24 * (4 * (10 * (p0 + 2)) + 8) + 600)
        ≤ R0 * (180000 * p0) := Nat.mul_le_mul_left R0 (by linarith)
      _ = 180000 * (R0 * p0) := by ring
  refine ⟨t, ?_, hcomp⟩
  change t ≤ 500000 * R0 * p0 + 100000 * w
  have hgoal_eq : 500000 * R0 * p0 = 500000 * (R0 * p0) := by ring
  rw [hgoal_eq]
  linarith

/-! ## 3. Schedule Generation + `FastDFT` Execution (`bmRunFastDFTWithSched`, `bmRunFastDFTKeepCtx`) -/

/-- Consumes `encPair (encFinVec (2 ^ K) W_io (p + 2)) (encPair (encPair encUnary encUnary) encUnary) (xFixed, ((K, p), B_in))`
on `kIO`: stashes `xFixed` on `kWork4`, generates `computeScheduleIntTree K p B_in` onto `kSched`,
restores `xFixed` onto `kIO`, and runs `bmFastDFTRecursiveWith bmSubMul`. -/
def bmRunFastDFTWithSched (bmSubMul : BitMachine) : BitMachine :=
  bmUnwrapToWork4.seq
    ((bmScheduleTreeWith bmSubMul).seq
      ((tmDropWord kIO).seq
        ((tmMoveWord kWork4 kWork0 kIO).seq
          (bmFastDFTRecursiveWith bmSubMul))))

theorem bmRunFastDFTWithSched_computesInTime {bmSubMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmSubMul mulTime)
    (K p B_in : ℕ) (hp : 8 ≤ p) (hB_in : B_in ≤ p)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W_io := 10 * (p + 2)
    let tree := computeScheduleIntTree K p B_in
    let outFixed := computableFastDFTRecursive tree xFixed
    ∃ t ≤ 7000000000000 * scheduleTreeGenOps (scaledSubMulCost mulTime) K p +
          2300000000 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in,
      (bmRunFastDFTWithSched bmSubMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encFinVec (2 ^ K) W_io (p + 2))
            (encPair (encPair encUnary encUnary) encUnary)
            (xFixed, ((K, p), B_in))))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encFinVec (2 ^ K) W_io (p + 2) outFixed))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  let W_io := 10 * (p + 2)
  let tree := computeScheduleIntTree K p B_in
  let outFixed := computableFastDFTRecursive tree xFixed
  let wX := encFinVec (2 ^ K) W_io (p + 2) xFixed
  let wParams := encPair (encPair encUnary encUnary) encUnary ((K, p), B_in)
  rcases bmUnwrapToWork4_computesInTime wX wParams tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmScheduleTreeWith_computesInTime hmul K p B_in hB_in
    tW2 tW3 (encodeDelimWord wX ++ tW4) tW5 tSch with ⟨t2, ht2, s2⟩
  have s3 := tmDropWord_computesInTime kIO [] []
    (mkTapes8 [] [] [] tW2 tW3 (encodeDelimWord wX ++ tW4) tW5
      (encScheduleStream tree ++ tSch))
  simp only [update_mkTapes8_kIO, List.append_nil, List.length_nil] at s3
  have s4 := tmMoveWord_computesInTime kWork4 kWork0 kIO (by decide) (by decide) (by decide)
    wX tW4 [] []
    (mkTapes8 [] [] [] tW2 tW3 [] tW5 (encScheduleStream tree ++ tSch))
  simp only [update_mkTapes8_kWork4, update_mkTapes8_kWork0, update_mkTapes8_kIO,
    List.append_nil] at s4
  rcases bmFastDFTRecursiveWith_computesInTime hmul K p B_in hp hB_in xFixed hx
    tW2 tW3 tW4 tW5 tSch with ⟨t5, ht5, s5⟩
  have hall := s1.seq (s2.seq (s3.seq (s4.seq s5)))
  have hf_ge := mul_le_fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in
  have h1_le : 1 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in :=
    le_trans (by have := Nat.one_le_two_pow (n := K); nlinarith) hf_ge
  have hwX_le : wX.length ≤ 100 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in := by
    dsimp [wX, W_io]
    rw [length_encFinVec]
    calc 2 ^ K * (8 * (10 * (p + 2)) + 18)
        ≤ 2 ^ K * (100 * (p + 4)) := Nat.mul_le_mul_left _ (by omega)
      _ = 100 * (2 ^ K * (p + 4)) := by ring
      _ ≤ 100 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in :=
          Nat.mul_le_mul_left 100 hf_ge
  have hwParams_le : wParams.length ≤ 20 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in := by
    have hlen : wParams.length = 4 * K + 4 * p + 2 * B_in + 12 := by
      simp only [wParams, length_encPair, length_encUnary]
      ring
    have hK_le : K ≤ 2 ^ K := le_of_lt Nat.lt_two_pow_self
    have h2K_pos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    rw [hlen]
    calc 4 * K + 4 * p + 2 * B_in + 12
        ≤ 20 * (2 ^ K * (p + 4)) := by nlinarith
      _ ≤ 20 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K p B_in :=
          Nat.mul_le_mul_left 20 hf_ge
  refine ⟨t1 + (t2 + (1 + ((2 * wX.length + 4) + t5))), ?_, hall⟩
  linarith

/-- Context-preserving wrapper around `bmRunFastDFTWithSched bmSubMul`:
consumes `((w, (K0, p0)), xFixed)` on `kIO` and emits `((w, (K0, p0)), computableFastDFTRecursive tree xFixed)`
on `kIO`. -/
def bmRunFastDFTKeepCtx (bmSubMul : BitMachine) : BitMachine :=
  bmFanout
    bmFst
    (bmSeq
      (bmFanout bmSnd (bmFanout (bmSeq bmFst bmSnd) (bmUnaryConst 2)))
      (bmRunFastDFTWithSched bmSubMul))

theorem bmRunFastDFTKeepCtx_computesInTime {bmSubMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmSubMul mulTime) (w : ℕ)
    (xFixed : Fin (rootR0 w) → FixedComplex (rootP0 w + 2))
    (hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ 2)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let K0 := rootK0 w
    let p0 := rootP0 w
    let R0 := rootR0 w
    let W_io := 10 * (p0 + 2)
    let tree := computeScheduleIntTree K0 p0 2
    let outFixed := computableFastDFTRecursive tree xFixed
    ∃ t ≤ 7200000000000 * scheduleTreeGenOps (scaledSubMulCost mulTime) K0 p0 +
          2500000000 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 +
          1000 * w,
      (bmRunFastDFTKeepCtx bmSubMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encFinVec R0 W_io (p0 + 2))
            ((w, (K0, p0)), xFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encFinVec R0 W_io (p0 + 2))
            ((w, (K0, p0)), outFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  let K0 := rootK0 w
  let p0 := rootP0 w
  let R0 := rootR0 w
  let W_io := 10 * (p0 + 2)
  let tree := computeScheduleIntTree K0 p0 2
  let outFixed := computableFastDFTRecursive tree xFixed
  have hp018 : 18 ≤ p0 := rootP0_ge_eighteen w
  have hp0 : 8 ≤ p0 := by omega
  have hB0 : 2 ≤ p0 := by omega
  let S := Unit
  let uCtx : S → List Bool := fun _ =>
    encPair encUnary (encPair encUnary encUnary) (w, (K0, p0))
  let uX : S → List Bool := fun _ => encFinVec R0 W_io (p0 + 2) xFixed
  let uIn : S → List Bool := encDepPair uCtx uX
  have pCtx := StageEval.fst uCtx uX
  have pX := StageEval.snd uCtx uX
  have pK0P0 := StageEval.seq pCtx
    (StageEval.snd (fun _ : S => encUnary w)
      (fun _ : S => encPair encUnary encUnary (K0, p0)))
  have pTwo := StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 2 uIn) (fun _ : S => ())
  have pPrep := StageEval.fanout pX (StageEval.fanout pK0P0 pTwo)
  have pDFT := StageEval.const (S := S)
    (bmRunFastDFTWithSched_computesInTime hmul K0 p0 2 hp0 hB0 xFixed hx)
  have hall := StageEval.fanout pCtx (StageEval.seq pPrep pDFT)
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uCtx, uX, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encFinVec] at ht
  have hf_ge := mul_le_fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2
  have h1_le : 1 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 :=
    le_trans (by have := Nat.one_le_two_pow (n := K0); nlinarith) hf_ge
  have hvec1 : 2 ^ K0 * (8 * (10 * (p0 + 2)) + 18) ≤
      100 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 := by
    calc 2 ^ K0 * (8 * (10 * (p0 + 2)) + 18)
        ≤ 2 ^ K0 * (100 * (p0 + 4)) := Nat.mul_le_mul_left _ (by omega)
      _ = 100 * (2 ^ K0 * (p0 + 4)) := by ring
      _ ≤ 100 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 :=
          Nat.mul_le_mul_left 100 hf_ge
  have hK0_f : K0 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 := by
    have hK0_2K0 : K0 ≤ 2 ^ K0 := le_of_lt Nat.lt_two_pow_self
    exact le_trans (by nlinarith) hf_ge
  have hp0_f : p0 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 :=
    le_trans (by have := Nat.one_le_two_pow (n := K0); nlinarith) hf_ge
  dsimp only [R0, W_io] at ht
  have hR0_def : rootR0 w = 2 ^ K0 := rfl
  rw [hR0_def] at ht
  refine ⟨t, ?_, hcomp⟩
  change t ≤ 7200000000000 * scheduleTreeGenOps (scaledSubMulCost mulTime) K0 p0 +
      2500000000 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 + 1000 * w
  linarith

/-! ## 4. Pointwise Frequency-Domain Squaring & Unpacking (`bmFreqSquareElemWith`, `bmFreqSquareKeepCtxWith`) -/

/-- Pointwise frequency-domain squaring & unpacking element machine (`bmFreqSquareElemWith bmSubMul`):
consumes `((W_io, p0 + 3), z)` on `kIO` (where `z : FixedComplex (p0 + 2)` is encoded at width `W_io`)
and emits
`encComplex W_io ((⟨roundShiftInt (2 * z.re * z.im) (p0 + 3), roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj)`
on `kIO`. -/
def bmFreqSquareElemWith (bmSubMul : BitMachine) : BitMachine :=
  let bmWio := bmSeq bmFst bmFst
  let bmSh := bmSeq bmFst bmSnd
  let bmZRe := bmSeq bmSnd bmFst
  let bmZIm := bmSeq bmSnd bmSnd
  let bm2ZRe := bmSeq bmZRe bmSignedDouble
  let bmProdRe := bmSeq (bmFanout bm2ZRe bmZIm) (bmSignedMulWith bmSubMul)
  let bmImSq := bmSeq (bmFanout bmZIm bmZIm) (bmSignedMulWith bmSubMul)
  let bmReSq := bmSeq (bmFanout bmZRe bmZRe) (bmSignedMulWith bmSubMul)
  let bmDiffIm := bmSeq (bmFanout bmImSq bmReSq) bmSignedSubExt
  let bmRoundRe := bmSeq (bmFanout bmSh bmProdRe) bmRoundShiftSigned
  let bmRoundIm := bmSeq (bmFanout bmSh bmDiffIm) bmRoundShiftSigned
  let bmResRe := bmSeq (bmFanout bmWio bmRoundRe) bmResizeSignedWord
  let bmResIm := bmSeq (bmFanout bmWio bmRoundIm) bmResizeSignedWord
  bmSeq (bmFanout bmResRe bmResIm) bmComplexConj

theorem bmFreqSquareElemWith_computesInTime {bmSubMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmSubMul mulTime)
    (p0 : ℕ) (z : FixedComplex (p0 + 2)) (hz : WordWidthBounds (3 * (p0 + 2)) z)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let W_io := 10 * (p0 + 2)
    let w_elem : FixedComplex (p0 + 2) :=
      (⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
        roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj
    ∃ t ≤ 6 * mulTime W_io + 600000 * p0 + 1500000,
      (bmFreqSquareElemWith bmSubMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary encUnary) (encComplex W_io (q := p0 + 2))
            ((W_io, p0 + 3), z)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encComplex W_io (q := p0 + 2) w_elem))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  let W_io := 10 * (p0 + 2)
  let w_elem : FixedComplex (p0 + 2) :=
    (⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
      roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj
  have hre_Wio : FitsSignedWord W_io z.re := hz.1.mono (by unfold W_io; omega)
  have him_Wio : FitsSignedWord W_io z.im := hz.2.mono (by unfold W_io; omega)
  have h2re_3p : FitsSignedWord (3 * (p0 + 2) + 1) (2 * z.re) := by
    have h : 2 * z.re = z.re * (2 : ℤ) ^ 1 := by ring
    rw [h]; simpa [Nat.add_comm] using hz.1.mul_two_pow 1
  have h2re_Wio : FitsSignedWord W_io (2 * z.re) := h2re_3p.mono (by unfold W_io; omega)
  have hprodRe_6p : FitsSignedWord (6 * (p0 + 2) + 1) (2 * z.re * z.im) := by
    have h := h2re_3p.mul hz.2
    exact h.mono (by omega)
  have hprodRe_2W : FitsSignedWord (2 * W_io) (2 * z.re * z.im) :=
    hprodRe_6p.mono (by unfold W_io; omega)
  have himSq_6p : FitsSignedWord (6 * (p0 + 2)) (z.im * z.im) := by
    have h := hz.2.mul hz.2
    exact h.mono (by omega)
  have hreSq_6p : FitsSignedWord (6 * (p0 + 2)) (z.re * z.re) := by
    have h := hz.1.mul hz.1
    exact h.mono (by omega)
  have himSq_2W : FitsSignedWord (2 * W_io) (z.im * z.im) :=
    himSq_6p.mono (by unfold W_io; omega)
  have hreSq_2W : FitsSignedWord (2 * W_io) (z.re * z.re) :=
    hreSq_6p.mono (by unfold W_io; omega)
  have hdiff_6p : FitsSignedWord (6 * (p0 + 2) + 1) (z.im * z.im - z.re * z.re) :=
    himSq_6p.sub hreSq_6p
  have hdiff_2W1 : FitsSignedWord (2 * W_io + 1) (z.im * z.im - z.re * z.re) :=
    hdiff_6p.mono (by unfold W_io; omega)
  have hroundRe_6p : FitsSignedWord (6 * (p0 + 2) + 1) (roundShiftInt (2 * z.re * z.im) (p0 + 3)) :=
    hprodRe_6p.roundShiftInt (p0 + 3)
  have hroundRe_2W : FitsSignedWord (2 * W_io) (roundShiftInt (2 * z.re * z.im) (p0 + 3)) :=
    hprodRe_2W.roundShiftInt (p0 + 3)
  have hroundRe_Wio : FitsSignedWord W_io (roundShiftInt (2 * z.re * z.im) (p0 + 3)) :=
    hroundRe_6p.mono (by unfold W_io; omega)
  have hroundIm_6p : FitsSignedWord (6 * (p0 + 2) + 1)
      (roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)) :=
    hdiff_6p.roundShiftInt (p0 + 3)
  have hroundIm_2W1 : FitsSignedWord (2 * W_io + 1)
      (roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)) :=
    hdiff_2W1.roundShiftInt (p0 + 3)
  have hroundIm_Wio : FitsSignedWord W_io
      (roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)) :=
    hroundIm_6p.mono (by unfold W_io; omega)
  let S := Unit
  let uCtx : S → List Bool := fun _ => encPair encUnary encUnary (W_io, p0 + 3)
  let uZ : S → List Bool := fun _ => encComplex W_io z
  let uIn : S → List Bool := encDepPair uCtx uZ
  have pCtx := StageEval.fst uCtx uZ
  have pZ := StageEval.snd uCtx uZ
  have pWio := StageEval.seq pCtx
    (StageEval.fst (fun _ : S => encUnary W_io) (fun _ : S => encUnary (p0 + 3)))
  have pSh := StageEval.seq pCtx
    (StageEval.snd (fun _ : S => encUnary W_io) (fun _ : S => encUnary (p0 + 3)))
  have pZRe := StageEval.seq pZ
    (StageEval.fst (fun _ : S => encodeSignedWord W_io z.re)
      (fun _ : S => encodeSignedWord W_io z.im))
  have pZIm := StageEval.seq pZ
    (StageEval.snd (fun _ : S => encodeSignedWord W_io z.re)
      (fun _ : S => encodeSignedWord W_io z.im))
  have p2ZRe := StageEval.seq pZRe
    (StageEval.const (S := S) (bmSignedDouble_computesInTime W_io z.re hre_Wio h2re_Wio))
  have pProdRe := StageEval.seq (StageEval.fanout p2ZRe pZIm)
    (StageEval.const (S := S)
      (bmSignedMulWith_computesInTime hmul W_io (2 * z.re) z.im h2re_Wio him_Wio))
  have pImSq := StageEval.seq (StageEval.fanout pZIm pZIm)
    (StageEval.const (S := S)
      (bmSignedMulWith_computesInTime hmul W_io z.im z.im him_Wio him_Wio))
  have pReSq := StageEval.seq (StageEval.fanout pZRe pZRe)
    (StageEval.const (S := S)
      (bmSignedMulWith_computesInTime hmul W_io z.re z.re hre_Wio hre_Wio))
  have pDiffIm := StageEval.seq (StageEval.fanout pImSq pReSq)
    (StageEval.const (S := S)
      (bmSignedSubExt_computesInTime (2 * W_io) (z.im * z.im) (z.re * z.re) himSq_2W hreSq_2W))
  have pRoundRe := StageEval.seq (StageEval.fanout pSh pProdRe)
    (StageEval.const (S := S)
      (bmRoundShiftSigned_computesInTime (2 * W_io) (p0 + 3) (2 * z.re * z.im) hprodRe_2W))
  have pRoundIm := StageEval.seq (StageEval.fanout pSh pDiffIm)
    (StageEval.const (S := S)
      (bmRoundShiftSigned_computesInTime (2 * W_io + 1) (p0 + 3)
        (z.im * z.im - z.re * z.re) hdiff_2W1))
  have pResRe := StageEval.seq (StageEval.fanout pWio pRoundRe)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime (2 * W_io) W_io
        (roundShiftInt (2 * z.re * z.im) (p0 + 3)) hroundRe_2W hroundRe_Wio))
  have pResIm := StageEval.seq (StageEval.fanout pWio pRoundIm)
    (StageEval.const (S := S)
      (bmResizeSignedWord_computesInTime (2 * W_io + 1) W_io
        (roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)) hroundIm_2W1 hroundIm_Wio))
  let preConj : FixedComplex (p0 + 2) :=
    ⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
     roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩
  have hpreConj : WordWidthBounds W_io preConj := ⟨hroundRe_Wio, hroundIm_Wio⟩
  have pConj := StageEval.seq (StageEval.fanout pResRe pResIm)
    (StageEval.const (S := S) (bmComplexConj_computesInTime W_io preConj hpreConj))
  rcases pConj () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uCtx, uZ, W_io, id] at ht hcomp
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encComplex,
    length_encodeSignedWord] at ht
  exact ⟨t, by linarith only [ht], hcomp⟩

/-- Context-preserving vector map of `bmFreqSquareElemWith bmSubMul`:
consumes `((w, (K0, p0)), ZFixed)` on `kIO` and emits `((w, (K0, p0)), W_conjFixed)` on `kIO`. -/
def bmFreqSquareKeepCtxWith (bmSubMul : BitMachine) : BitMachine :=
  let bmP0 := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmP0Plus2 := bmSeq (bmFanout bmP0 (bmUnaryConst 2)) bmUnaryAdd
  let bmWio := bmSeq (bmFanout (bmUnaryConst 10) bmP0Plus2) bmUnaryMul
  let bmP0Plus3 := bmSeq (bmFanout bmP0 (bmUnaryConst 3)) bmUnaryAdd
  bmFanout
    bmFst
    (bmSeq
      (bmFanout (bmFanout bmWio bmP0Plus3) bmSnd)
      (bmMapWithCtx (bmFreqSquareElemWith bmSubMul)))

theorem bmFreqSquareKeepCtxWith_computesInTime {bmSubMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmSubMul mulTime) (w : ℕ)
    (ZFixed : Fin (rootR0 w) → FixedComplex (rootP0 w + 2))
    (hZ : ∀ u : Fin (rootR0 w), WordWidthBounds (3 * (rootP0 w + 2)) (ZFixed u))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let K0 := rootK0 w
    let p0 := rootP0 w
    let R0 := rootR0 w
    let W_io := 10 * (p0 + 2)
    let W_conjFixed : Fin R0 → FixedComplex (p0 + 2) := fun u =>
      (⟨roundShiftInt (2 * (ZFixed u).re * (ZFixed u).im) (p0 + 3),
        roundShiftInt ((ZFixed u).im * (ZFixed u).im - (ZFixed u).re * (ZFixed u).re) (p0 + 3)⟩ :
        FixedComplex (p0 + 2)).conj
    ∃ t ≤ R0 * (6 * scaledSubMulCost mulTime (p0 + 2) + 700000 * p0 + 1800000) + 1000 * w,
      (bmFreqSquareKeepCtxWith bmSubMul).ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encFinVec R0 W_io (p0 + 2))
            ((w, (K0, p0)), ZFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encFinVec R0 W_io (p0 + 2))
            ((w, (K0, p0)), W_conjFixed)))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  let K0 := rootK0 w
  let p0 := rootP0 w
  let R0 := rootR0 w
  let W_io := 10 * (p0 + 2)
  let W_conjFixed : Fin R0 → FixedComplex (p0 + 2) := fun u =>
    (⟨roundShiftInt (2 * (ZFixed u).re * (ZFixed u).im) (p0 + 3),
      roundShiftInt ((ZFixed u).im * (ZFixed u).im - (ZFixed u).re * (ZFixed u).re) (p0 + 3)⟩ :
      FixedComplex (p0 + 2)).conj
  let zList : List (FixedComplex (p0 + 2)) := List.ofFn ZFixed
  have hz_mem : ∀ z ∈ zList, WordWidthBounds (3 * (p0 + 2)) z := by
    intro z hz
    rcases List.mem_ofFn.mp hz with ⟨u, rfl⟩
    exact hZ u
  let S := Unit
  let uCtx : S → List Bool := fun _ =>
    encPair encUnary (encPair encUnary encUnary) (w, (K0, p0))
  let uZ : S → List Bool := fun _ => encFinVec R0 W_io (p0 + 2) ZFixed
  let uIn : S → List Bool := encDepPair uCtx uZ
  have pCtx := StageEval.fst uCtx uZ
  have pZ := StageEval.snd uCtx uZ
  have pK0P0 := StageEval.seq pCtx
    (StageEval.snd (fun _ : S => encUnary w)
      (fun _ : S => encPair encUnary encUnary (K0, p0)))
  have pP0 := StageEval.seq pK0P0
    (StageEval.snd (fun _ : S => encUnary K0) (fun _ : S => encUnary p0))
  have pP0Plus2 := StageEval.seq
    (StageEval.fanout pP0 (StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 2 uIn) (fun _ : S => ())))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (p0, 2)))
  have pWio := StageEval.congr_out (v2 := fun _ : S => encUnary W_io)
    (StageEval.seq
      (StageEval.fanout
        (StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 10 uIn) (fun _ : S => ()))
        pP0Plus2)
      (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (10, p0 + 2))))
    (fun _ => rfl)
  have pP0Plus3 := StageEval.seq
    (StageEval.fanout pP0 (StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 3 uIn) (fun _ : S => ())))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (p0, 3)))
  have pMap := StageEval.mapWithCtx_uniform
    (S := S)
    (ctx := fun _ => encPair encUnary encUnary (W_io, p0 + 3))
    (xs := fun _ => zList)
    (encA := fun _ => encComplex W_io (q := p0 + 2))
    (encB := fun _ => encComplex W_io (q := p0 + 2))
    (fn := fun _ z =>
      (⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
        roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj)
    (B := fun _ => 6 * mulTime W_io + 600000 * p0 + 1500000)
    (L_A := fun _ => 4 * W_io + 8)
    (L_B := fun _ => 4 * W_io + 8)
    (fun p => bmFreqSquareElemWith_computesInTime hmul p0 p.val.2 (hz_mem p.val.2 p.property))
    (fun _ _ _ => by simp [length_encComplex])
    (fun _ _ _ => by simp [length_encComplex])
  have pZList : StageEval (S := S) bmSnd uIn
      (fun _ => encList (encComplex W_io (q := p0 + 2)) zList)
      (fun s => 3 * (uIn s).length + 6) := by
    refine (StageEval.congr_out (v2 := fun _ => encList (encComplex W_io (q := p0 + 2)) zList)
      pZ (fun _ => by dsimp [uZ, zList, encFinVec]; rw [List.ofFn_eq_map])).mono
      (fun _ => by simp only [uIn, length_encDepPair]; omega)
  have pMapped := StageEval.congr_out
    (v2 := fun _ : S => encFinVec R0 W_io (p0 + 2) W_conjFixed)
    (StageEval.seq (StageEval.fanout (StageEval.fanout pWio pP0Plus3) pZList) pMap)
    (fun _ => by
      dsimp only [zList, W_conjFixed, encFinVec]
      rw [List.map_ofFn, List.ofFn_eq_map]
      rfl)
  have hall := StageEval.fanout pCtx pMapped
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uCtx, uZ, W_io, zList, id] at ht hcomp
  have hlen_zList :
      (encList (encComplex (10 * (p0 + 2))) (List.ofFn ZFixed)).length =
      R0 * (8 * (10 * (p0 + 2)) + 18) := by
    rw [List.ofFn_eq_map]
    exact length_encFinVec R0 (10 * (p0 + 2)) (p0 + 2) ZFixed
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encFinVec,
    List.length_ofFn, hlen_zList] at ht
  have hR0_def : rootR0 w = R0 := rfl
  rw [hR0_def] at ht
  have hmul_le : mulTime (10 * (p0 + 2)) ≤ scaledSubMulCost mulTime (p0 + 2) :=
    le_scaledSubMulCost_ten mulTime (p0 + 2)
  have h1_R0 : 1 ≤ R0 := by have := rootR0_ge_four w; omega
  have hK0_R0 : K0 ≤ R0 := le_of_lt Nat.lt_two_pow_self
  have hp0_RP : p0 ≤ R0 * p0 := by
    calc p0 = 1 * p0 := (Nat.one_mul p0).symm
      _ ≤ R0 * p0 := Nat.mul_le_mul_right p0 h1_R0
  have hFinVec : R0 * (8 * (10 * (p0 + 2)) + 18) = 80 * (R0 * p0) + 178 * R0 := by ring
  have hbody_le :
      R0 * (6 * mulTime (10 * (p0 + 2)) + 600000 * p0 + 1500000 +
        4 * (2 * (10 * (p0 + 2)) + 2 * (p0 + 3) + 4) +
        6 * (4 * (10 * (p0 + 2)) + 8) + 20 * (4 * (10 * (p0 + 2)) + 8) + 40) ≤
      6 * (R0 * scaledSubMulCost mulTime (p0 + 2)) + 620000 * (R0 * p0) + 1550000 * R0 := by
    calc R0 * (6 * mulTime (10 * (p0 + 2)) + 600000 * p0 + 1500000 +
          4 * (2 * (10 * (p0 + 2)) + 2 * (p0 + 3) + 4) +
          6 * (4 * (10 * (p0 + 2)) + 8) + 20 * (4 * (10 * (p0 + 2)) + 8) + 40)
        ≤ R0 * (6 * scaledSubMulCost mulTime (p0 + 2) + 620000 * p0 + 1550000) :=
          Nat.mul_le_mul_left R0 (by omega)
      _ = 6 * (R0 * scaledSubMulCost mulTime (p0 + 2)) + 620000 * (R0 * p0) + 1550000 * R0 := by ring
  refine ⟨t, ?_, hcomp⟩
  change t ≤ R0 * (6 * scaledSubMulCost mulTime (p0 + 2) + 700000 * p0 + 1800000) + 1000 * w
  have hgoal_eq :
      R0 * (6 * scaledSubMulCost mulTime (p0 + 2) + 700000 * p0 + 1800000) =
      6 * (R0 * scaledSubMulCost mulTime (p0 + 2)) + 700000 * (R0 * p0) + 1800000 * R0 := by ring
  rw [hgoal_eq]
  linarith

/-! ## 5. Post-DFT Convolution Extraction & Carry-Save Product Emission (`bmConvPostExtractElem`, `bmFastNatMulFinish`, `bmFastNatMulWith`) -/

theorem natAbs_max_zero_eq_toNat (x : ℤ) : (max 0 x).natAbs = x.toNat := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [max_eq_left (le_of_lt hx), Int.toNat_of_nonpos (le_of_lt hx)]; rfl
  · rw [max_eq_right hx]; omega

/-- Extract the unsigned convolution chunk `encNatWord W_io (roundShiftInt z.conj.re 8).toNat`
from `(ctx, encComplex W_io z)` on `kIO`. -/
def bmConvPostExtractElem : BitMachine :=
  bmSeq
    (bmSeq
      (bmSeq (bmFanout (bmSeq bmSnd (bmUnaryConst 8)) (bmSeq (bmSeq bmSnd bmComplexConj) bmFst))
        bmRoundShiftSigned)
      bmSignedMaxZero)
    bmSignedMagBits

theorem bmConvPostExtractElem_computesInTime {q : ℕ} (W_io : ℕ) (z : FixedComplex q)
    (hz : WordWidthBounds W_io z) (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ 10000 * W_io + 70000,
      bmConvPostExtractElem.ComputesInTime
        (mkTapes8 (encodeDelimWord (encPair encUnit (encComplex W_io) ((), z)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encNatWord W_io (roundShiftInt z.conj.re 8).toNat))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let S := Unit
  let uIn : S → List Bool := fun _ => encPair encUnit (encComplex W_io) ((), z)
  have pZ := StageEval.snd (fun _ : S => encUnit ()) (fun _ : S => encComplex W_io z)
  have pConj := StageEval.seq pZ
    (StageEval.const (S := S) (bmComplexConj_computesInTime W_io z hz))
  have pRe := StageEval.seq pConj
    (StageEval.fst (fun _ : S => encodeSignedWord W_io z.conj.re)
      (fun _ : S => encodeSignedWord W_io z.conj.im))
  have pEight := StageEval.of_computesStageLe
    (bmUnaryConst_computesStageLe 8 (encComplex W_io)) (fun _ : S => z)
  have p8Re := StageEval.fanout (StageEval.seq pZ pEight) pRe
  have hre_conj : FitsSignedWord W_io z.conj.re := hz.1
  have hround_fits : FitsSignedWord W_io (roundShiftInt z.conj.re 8) :=
    hre_conj.roundShiftInt 8
  have hmax_fits : FitsSignedWord W_io (max 0 (roundShiftInt z.conj.re 8)) := by
    rcases lt_or_ge (roundShiftInt z.conj.re 8) 0 with hneg | hpos
    · rw [max_eq_left (le_of_lt hneg)]; exact FitsSignedWord.zero W_io
    · rw [max_eq_right hpos]; exact hround_fits
  have pRound := StageEval.seq p8Re
    (StageEval.const (S := S) (bmRoundShiftSigned_computesInTime W_io 8 z.conj.re hre_conj))
  have pMax := StageEval.seq pRound
    (StageEval.const (S := S)
      (bmSignedMaxZero_computesInTime W_io (roundShiftInt z.conj.re 8) hround_fits))
  have pMag := StageEval.congr_out
    (v2 := fun _ : S => encNatWord W_io (roundShiftInt z.conj.re 8).toNat)
    (StageEval.seq pMax
      (StageEval.const (S := S)
        (bmSignedMagBits_computesInTime W_io (max 0 (roundShiftInt z.conj.re 8)) hmax_fits)))
    (fun _ => by dsimp [encNatWord]; rw [natAbs_max_zero_eq_toNat])
  rcases pMag () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, encUnit, id] at ht hcomp
  simp only [length_encDepPair, length_encComplex, length_encodeSignedWord,
    length_encUnary, List.length_nil] at ht
  exact ⟨t, by omega, hcomp⟩

/-- Post-DFT extraction and carry-save bit-stream emission (`bmFastNatMulFinish`):
consumes `((w, (K0, p0)), C_raw)` on `kIO` and emits
`carrySaveEmitBits (chunkBits w) (2 * w) (List.ofFn (fun k : Fin (rootR0 w) => (roundShiftInt (C_raw k).conj.re 8).toNat)) 0`
on `kIO`. -/
def bmFastNatMulFinish : BitMachine :=
  let bmW := bmSeq bmFst bmFst
  let bm2W := bmSeq bmW bmUnaryDouble
  let bmB := bmSeq bmW bmChunkBits
  let bmP0 := bmSeq (bmSeq bmFst bmSnd) bmSnd
  let bmP0Plus2 := bmSeq (bmFanout bmP0 (bmUnaryConst 2)) bmUnaryAdd
  let bmWio := bmSeq (bmFanout (bmUnaryConst 10) bmP0Plus2) bmUnaryMul
  let bmCs := bmSeq (bmFanout bmConstEmpty bmSnd) (bmMapWithCtx bmConvPostExtractElem)
  bmSeq (bmFanout bm2W (bmFanout (bmFanout bmB bmWio) bmCs)) bmCarrySaveEmitBits

theorem bmFastNatMulFinish_computesInTime (w : ℕ)
    (C_raw : Fin (rootR0 w) → FixedComplex (rootP0 w + 2))
    (hC : ∀ k : Fin (rootR0 w), WordWidthBounds (10 * (rootP0 w + 2)) (C_raw k))
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    let K0 := rootK0 w
    let p0 := rootP0 w
    let R0 := rootR0 w
    let b := chunkBits w
    let W_io := 10 * (p0 + 2)
    let cs : List ℕ := List.ofFn (fun k : Fin R0 => (roundShiftInt (C_raw k).conj.re 8).toNat)
    ∃ t ≤ 120000 * R0 * p0 + 400000 * R0 + 1000 * w + 200000,
      bmFastNatMulFinish.ComputesInTime
        (mkTapes8 (encodeDelimWord
          (encPair (encPair encUnary (encPair encUnary encUnary))
            (encFinVec R0 W_io (p0 + 2))
            ((w, (K0, p0)), C_raw)))
          [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (carrySaveEmitBits b (2 * w) cs 0))
          [] [] tW2 tW3 tW4 tW5 tSch) t := by
  dsimp only
  let K0 := rootK0 w
  let p0 := rootP0 w
  let R0 := rootR0 w
  let b := chunkBits w
  let W_io := 10 * (p0 + 2)
  let cList : List (FixedComplex (p0 + 2)) := List.ofFn C_raw
  have hc_mem : ∀ z ∈ cList, WordWidthBounds W_io z := by
    intro z hz
    rcases List.mem_ofFn.mp hz with ⟨k, rfl⟩
    exact hC k
  have hc_lt : ∀ k : Fin R0, (roundShiftInt (C_raw k).conj.re 8).toNat < 2 ^ W_io := by
    intro k
    have hfits : FitsSignedWord W_io (max 0 (roundShiftInt (C_raw k).conj.re 8)) := by
      have hr : FitsSignedWord W_io (roundShiftInt (C_raw k).conj.re 8) :=
        (hC k).1.roundShiftInt 8
      rcases lt_or_ge (roundShiftInt (C_raw k).conj.re 8) 0 with hneg | hpos
      · rw [max_eq_left (le_of_lt hneg)]; exact FitsSignedWord.zero W_io
      · rw [max_eq_right hpos]; exact hr
    rw [← natAbs_max_zero_eq_toNat]
    exact (fitsSignedWord_iff_natAbs_lt W_io _).mp hfits
  let csSub : List { x : ℕ // x < 2 ^ W_io } :=
    List.ofFn (fun k : Fin R0 => ⟨(roundShiftInt (C_raw k).conj.re 8).toNat, hc_lt k⟩)
  have hcsSub_val : csSub.map Subtype.val =
      List.ofFn (fun k : Fin R0 => (roundShiftInt (C_raw k).conj.re 8).toNat) := by
    dsimp [csSub]
    rw [List.map_ofFn]
    rfl
  let S := Unit
  let uCtx : S → List Bool := fun _ =>
    encPair encUnary (encPair encUnary encUnary) (w, (K0, p0))
  let uC : S → List Bool := fun _ => encFinVec R0 W_io (p0 + 2) C_raw
  let uIn : S → List Bool := encDepPair uCtx uC
  have pCtx := StageEval.fst uCtx uC
  have pC := StageEval.snd uCtx uC
  have pW := StageEval.seq pCtx
    (StageEval.fst (fun _ : S => encUnary w)
      (fun _ : S => encPair encUnary encUnary (K0, p0)))
  have p2W := StageEval.seq pW
    (StageEval.of_computesStageLe bmUnaryDouble_computesStageLe (fun _ : S => w))
  have pB := StageEval.seq pW
    (StageEval.of_computesStageLe bmChunkBits_computesStageLe (fun _ : S => w))
  have pK0P0 := StageEval.seq pCtx
    (StageEval.snd (fun _ : S => encUnary w)
      (fun _ : S => encPair encUnary encUnary (K0, p0)))
  have pP0 := StageEval.seq pK0P0
    (StageEval.snd (fun _ : S => encUnary K0) (fun _ : S => encUnary p0))
  have pP0Plus2 := StageEval.seq
    (StageEval.fanout pP0 (StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 2 uIn) (fun _ : S => ())))
    (StageEval.of_computesStageLe bmUnaryAdd_computesStageLe (fun _ : S => (p0, 2)))
  have pWio := StageEval.congr_out (v2 := fun _ : S => encUnary W_io)
    (StageEval.seq
      (StageEval.fanout
        (StageEval.of_computesStageLe (bmUnaryConst_computesStageLe 10 uIn) (fun _ : S => ()))
        pP0Plus2)
      (StageEval.of_computesStageLe bmUnaryMul_computesStageLe (fun _ : S => (10, p0 + 2))))
    (fun _ => rfl)
  have pCList : StageEval (S := S) bmSnd uIn
      (fun _ => encList (encComplex W_io (q := p0 + 2)) cList)
      (fun s => 3 * (uIn s).length + 6) := by
    refine (StageEval.congr_out (v2 := fun _ => encList (encComplex W_io (q := p0 + 2)) cList)
      pC (fun _ => by dsimp [uC, cList, encFinVec]; rw [List.ofFn_eq_map])).mono
      (fun _ => by simp only [uIn, length_encDepPair]; omega)
  have pMap := StageEval.mapWithCtx_uniform
    (S := S)
    (ctx := fun _ => encUnit ())
    (xs := fun _ => cList)
    (encA := fun _ => encComplex W_io (q := p0 + 2))
    (encB := fun _ => encNatWord W_io)
    (fn := fun _ z => (roundShiftInt z.conj.re 8).toNat)
    (B := fun _ => 10000 * W_io + 70000)
    (L_A := fun _ => 4 * W_io + 8)
    (L_B := fun _ => W_io)
    (fun p => bmConvPostExtractElem_computesInTime W_io p.val.2 (hc_mem p.val.2 p.property))
    (fun _ _ _ => by simp [length_encComplex])
    (fun _ _ _ => by simp [encNatWord])
  have pCs := StageEval.congr_out
    (v2 := fun _ : S => encList (fun c : { x : ℕ // x < 2 ^ W_io } => encNatWord W_io c.1) csSub)
    (StageEval.seq (StageEval.fanout (StageEval.constEmpty uIn) pCList) pMap)
    (fun _ => by
      simp only [cList, csSub, encList, List.map_ofFn, Function.comp_def]
      rfl)
  have hb1 : 1 ≤ b := chunkBits_pos w
  have hbW : b ≤ W_io := by unfold W_io p0 rootP0 b; omega
  have pEmit := StageEval.congr_out
    (v2 := fun _ : S =>
      carrySaveEmitBits b (2 * w)
        (List.ofFn (fun k : Fin R0 => (roundShiftInt (C_raw k).conj.re 8).toNat)) 0)
    (StageEval.seq
      (StageEval.fanout p2W (StageEval.fanout (StageEval.fanout pB pWio) pCs))
      (StageEval.const (S := S) (bmCarrySaveEmitBits_computesInTime hb1 hbW (2 * w) csSub)))
    (fun _ => by rw [hcsSub_val])
  rcases pEmit () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, uCtx, uC, W_io, cList, csSub, encUnit, id] at ht hcomp
  have hlen_csSub :
      (encList (fun c : { x : ℕ // x < 2 ^ (10 * (p0 + 2)) } => encNatWord (10 * (p0 + 2)) c.1)
        (List.ofFn (fun k : Fin R0 => ⟨(roundShiftInt (C_raw k).conj.re 8).toNat, hc_lt k⟩))).length =
      R0 * (2 * (10 * (p0 + 2)) + 2) := by
    rw [length_encList_encNatWord, List.length_ofFn]
  have hlen_cList :
      (encList (encComplex (10 * (p0 + 2))) (List.ofFn C_raw)).length =
      R0 * (8 * (10 * (p0 + 2)) + 18) := by
    rw [List.ofFn_eq_map]
    exact length_encFinVec R0 (10 * (p0 + 2)) (p0 + 2) C_raw
  simp only [length_encDepPair, length_encPair, length_encUnary, length_encFinVec,
    List.length_ofFn, List.length_nil, hlen_csSub, hlen_cList] at ht
  have hb_def : chunkBits w = b := rfl
  have hR0_def : rootR0 w = R0 := rfl
  rw [hb_def, hR0_def] at ht
  have hb_le_p0 : b ≤ p0 := by unfold p0 rootP0 b; omega
  have hK0_le_R0 : K0 ≤ R0 := le_of_lt Nat.lt_two_pow_self
  have hR0_pos : 1 ≤ R0 := by have := rootR0_ge_four w; omega
  have hp0_RP : p0 ≤ R0 * p0 := by
    calc p0 = 1 * p0 := (Nat.one_mul p0).symm
      _ ≤ R0 * p0 := Nat.mul_le_mul_right p0 hR0_pos
  have h1 : R0 * (8 * (10 * (p0 + 2)) + 18) = 80 * (R0 * p0) + 178 * R0 := by ring
  have h2 : R0 * (2 * (10 * (p0 + 2)) + 2) = 20 * (R0 * p0) + 42 * R0 := by ring
  have h3 :
      R0 * (10000 * (10 * (p0 + 2)) + 70000 + 4 * 0 + 6 * (4 * (10 * (p0 + 2)) + 8) +
        20 * (10 * (p0 + 2)) + 40) =
      100440 * (R0 * p0) + 270968 * R0 := by ring
  have h4 : R0 * (460 * (10 * (p0 + 2)) + 950) = 4600 * (R0 * p0) + 10150 * R0 := by ring
  refine ⟨t, ?_, hcomp⟩
  change t ≤ 120000 * R0 * p0 + 400000 * R0 + 1000 * w + 200000
  have hgoal_eq : 120000 * R0 * p0 = 120000 * (R0 * p0) := by ring
  rw [hgoal_eq]
  linarith

/-- **Single-Tier Recursive `FastDFT` Bit-List Multiplier (`bmFastNatMulWith bmSubMul`)**:
Consumes `(w, (aBits, bBits))` on `kIO`, slices chunks and packs `zFixed` (`bmFastNatMulPrep`),
runs the forward `FastDFT` (`bmRunFastDFTKeepCtx bmSubMul`), performs pointwise frequency squaring
and unpacking (`bmFreqSquareKeepCtxWith bmSubMul`), runs the inverse `FastDFT`
(`bmRunFastDFTKeepCtx bmSubMul`), and emits the $2w$-bit product via `bmFastNatMulFinish`. -/
def bmFastNatMulWith (bmSubMul : BitMachine) : BitMachine :=
  bmSeq bmFastNatMulPrep
    (bmSeq (bmRunFastDFTKeepCtx bmSubMul)
      (bmSeq (bmFreqSquareKeepCtxWith bmSubMul)
        (bmSeq (bmRunFastDFTKeepCtx bmSubMul)
          bmFastNatMulFinish)))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
theorem isBitMulMachine_bmFastNatMulWith {bmSubMul : BitMachine} {mulTime : ℕ → ℕ}
    (hmul : IsBitMulMachine bmSubMul mulTime) :
    IsBitMulMachine (bmFastNatMulWith bmSubMul)
      (fun w => 15000000000000 * intMulAlgorithmSteps (scaledSubMulCost mulTime) w) := by
  intro w aBits bBits ha hb tW2 tW3 tW4 tW5 tSch
  let K0 := rootK0 w
  let p0 := rootP0 w
  let R0 := rootR0 w
  let b := chunkBits w
  let W_io := 10 * (p0 + 2)
  let tree := computeScheduleIntTree K0 p0 2
  let aChunks := sliceBitChunkFn b R0 aBits
  let bChunks := sliceBitChunkFn b R0 bBits
  let zFixed : Fin R0 → FixedComplex (p0 + 2) := packChunksFixed w (aChunks, bChunks)
  let ZFixed : Fin R0 → FixedComplex (p0 + 2) := computableFastDFTRecursive tree zFixed
  let W_conjFixed : Fin R0 → FixedComplex (p0 + 2) := fun u =>
    (⟨roundShiftInt (2 * (ZFixed u).re * (ZFixed u).im) (p0 + 3),
      roundShiftInt ((ZFixed u).im * (ZFixed u).im - (ZFixed u).re * (ZFixed u).re) (p0 + 3)⟩ :
      FixedComplex (p0 + 2)).conj
  let C_raw : Fin R0 → FixedComplex (p0 + 2) := computableFastDFTRecursive tree W_conjFixed
  have htree : ValidScheduleIntTree tree := validScheduleIntTree_computeScheduleIntTree K0 p0 2
  have hp018 : 18 ≤ p0 := rootP0_ge_eighteen w
  have hp0_ge8 : 8 ≤ p0 := by omega
  have hB0_le : 2 ≤ p0 := by omega
  have hz_sqrt2 : vecInfNorm (fun j => (zFixed j).toComplex) ≤ Real.sqrt 2 :=
    vecInfNorm_packChunksFixed_le_sqrt_two w aChunks bChunks
  have hz_B0 : vecInfNorm (fun j => (zFixed j).toComplex) ≤ (2 : ℝ) ^ 2 :=
    hz_sqrt2.trans (sqrt_two_le.trans (by norm_num))
  have hZ_bds : ∀ u : Fin R0, WordWidthBounds (3 * (p0 + 2)) (ZFixed u) :=
    wordWidthBounds_computableFastDFTRecursive_of_valid htree hp0_ge8 hB0_le zFixed hz_B0
  have hZ_norm : ∀ u : Fin R0, ‖(ZFixed u).toComplex‖ ≤ 2 := by
    intro u
    have hacc := (norm_le_vecInfNorm _ u).trans
      (vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow htree hp0_ge8 zFixed hz_B0)
    have hdft := ((norm_normDFT1D_le (fun j => (zFixed j).toComplex) u).trans hz_sqrt2).trans sqrt_two_le
    have h2p0_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (1 / 16 : ℝ) := by
      calc (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (2 : ℝ) ^ (-4 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 1 / 16 := by norm_num
    have hmax : max 1 (vecInfNorm (fun j => (zFixed j).toComplex)) ≤ 4 :=
      max_le (by norm_num) (by norm_num [hz_B0] at *; linarith)
    have hm := mul_le_mul h2p0_le hmax (by positivity) (by positivity)
    have htri := norm_add_le
      ((ZFixed u).toComplex - normDFT1D (fun j => (zFixed j).toComplex) u)
      (normDFT1D (fun j => (zFixed j).toComplex) u)
    rw [sub_add_cancel] at htri
    change ‖(ZFixed u).toComplex - normDFT1D (fun j => (zFixed j).toComplex) u‖ ≤
      (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm (fun j => (zFixed j).toComplex)) at hacc
    linarith
  have hW_B0 : vecInfNorm (fun u => (W_conjFixed u).toComplex) ≤ (2 : ℝ) ^ 2 := by
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    apply vecInfNorm_le _ (by norm_num)
    intro u
    have htoC : (W_conjFixed u).toComplex =
        starRingEnd ℂ (quantizeComplex (p0 + 2) (((ZFixed u).toComplex * (ZFixed u).toComplex) / (2 * Complex.I))) :=
      toComplex_freqSquareConjFixed (ZFixed u)
    rw [htoC, RCLike.norm_conj]
    set wC : ℂ := ((ZFixed u).toComplex * (ZFixed u).toComplex) / (2 * Complex.I)
    have hw_le : ‖wC‖ ≤ 2 := by
      dsimp [wC]
      rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      have hsq : ‖(ZFixed u).toComplex‖ * ‖(ZFixed u).toComplex‖ ≤ 4 := by
        nlinarith [hZ_norm u, norm_nonneg (ZFixed u).toComplex]
      linarith
    have hq := norm_quantizeComplex_sub_self_le (p0 + 2) wC
    have h2p : (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    have hsqrt := sqrt_two_le
    have hq1 : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) ≤ 1 := by
      nlinarith [hsqrt, h2p, zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((p0 + 2 : ℕ) : ℤ))]
    have htri := norm_add_le (quantizeComplex (p0 + 2) wC - wC) wC
    rw [sub_add_cancel] at htri
    linarith
  have hC_bds : ∀ k : Fin R0, WordWidthBounds W_io (C_raw k) := fun k =>
    (wordWidthBounds_computableFastDFTRecursive_of_valid htree hp0_ge8 hB0_le W_conjFixed hW_B0 k).mono
      (by unfold W_io; omega)
  rcases bmFastNatMulPrep_computesInTime w aBits bBits ha hb tW2 tW3 tW4 tW5 tSch with ⟨t1, ht1, s1⟩
  rcases bmRunFastDFTKeepCtx_computesInTime hmul w zFixed hz_B0 tW2 tW3 tW4 tW5 tSch with ⟨t2, ht2, s2⟩
  rcases bmFreqSquareKeepCtxWith_computesInTime hmul w ZFixed hZ_bds tW2 tW3 tW4 tW5 tSch with ⟨t3, ht3, s3⟩
  rcases bmRunFastDFTKeepCtx_computesInTime hmul w W_conjFixed hW_B0 tW2 tW3 tW4 tW5 tSch with ⟨t4, ht4, s4⟩
  rcases bmFastNatMulFinish_computesInTime w C_raw hC_bds tW2 tW3 tW4 tW5 tSch with ⟨t5, ht5, s5⟩
  have hall := s1.seq (s2.seq (s3.seq (s4.seq s5)))
  have hA_lt : decodeNatBits aBits < 2 ^ w := by rw [← ha]; exact decodeNatBits_lt aBits
  have hB_lt : decodeNatBits bBits < 2 ^ w := by rw [← hb]; exact decodeNatBits_lt bBits
  have hout_eq :
      carrySaveEmitBits b (2 * w)
        (List.ofFn (fun k : Fin R0 => (roundShiftInt (C_raw k).conj.re 8).toNat)) 0 =
      encodeNatBits (2 * w) (decodeNatBits aBits * decodeNatBits bBits) := by
    rw [carrySaveEmitBits_eq_encodeNatBits, zero_add]
    have hconv_eq :
        (fun k : Fin R0 => (roundShiftInt (C_raw k).conj.re 8).toNat) =
        (fun k : Fin R0 =>
          (computableFastTwoCallDFTConv w tree (decodeNatBits aBits) (decodeNatBits bBits) k).toNat) := by
      funext k
      unfold computableFastTwoCallDFTConv
      dsimp only [C_raw, W_conjFixed, ZFixed, zFixed, aChunks, bChunks, b, R0, p0, K0]
      simp only [memoizeFin_eq, sliceBitChunkFn_eq_natChunkFn]
    rw [hconv_eq]
    change encodeNatBits (2 * w)
      (computableReconstructProduct w tree (decodeNatBits aBits) (decodeNatBits bBits)) = _
    exact congrArg (encodeNatBits (2 * w))
      (computableReconstructProduct_computeScheduleIntTree_eq_mul w
        (decodeNatBits aBits) (decodeNatBits bBits) hA_lt hB_lt)
  rw [hout_eq] at hall
  have hK0_def : rootK0 w = K0 := rfl
  have hp0_def : rootP0 w = p0 := rfl
  have hR0_def : rootR0 w = R0 := rfl
  simp only [hK0_def, hp0_def, hR0_def] at ht1 ht2 ht3 ht4 ht5
  have ht1' : t1 ≤ 500000 * (R0 * p0) + 100000 * w := by
    calc t1 ≤ 500000 * R0 * p0 + 100000 * w := ht1
      _ = 500000 * (R0 * p0) + 100000 * w := by ring
  have ht3' :
      t3 ≤ 6 * (R0 * scaledSubMulCost mulTime (p0 + 2)) + 700000 * (R0 * p0) + 1800000 * R0 + 1000 * w := by
    calc t3 ≤ R0 * (6 * scaledSubMulCost mulTime (p0 + 2) + 700000 * p0 + 1800000) + 1000 * w := ht3
      _ = 6 * (R0 * scaledSubMulCost mulTime (p0 + 2)) + 700000 * (R0 * p0) + 1800000 * R0 + 1000 * w := by ring
  have ht5' : t5 ≤ 120000 * (R0 * p0) + 400000 * R0 + 1000 * w + 200000 := by
    calc t5 ≤ 120000 * R0 * p0 + 400000 * R0 + 1000 * w + 200000 := ht5
      _ = 120000 * (R0 * p0) + 400000 * R0 + 1000 * w + 200000 := by ring
  have hstep_def : intMulAlgorithmSteps (scaledSubMulCost mulTime) w =
      scheduleBitsLen w + fullScheduleTableBitsLen w +
      scheduleTreeGenOps (scaledSubMulCost mulTime) K0 p0 +
      2 * w +
      2 * fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 +
      3 * (R0 * scaledSubMulCost mulTime (p0 + 2)) + 4 * w := by
    unfold intMulAlgorithmSteps
    dsimp only [K0, p0, R0, levelScheduleBIn]
    ring
  have hf_ge : R0 * (p0 + 4) ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 :=
    mul_le_fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2
  have hR0_pos : 1 ≤ R0 := by have := rootR0_ge_four w; omega
  have hRP_f : R0 * p0 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 :=
    le_trans (by nlinarith) hf_ge
  have hR0_f : R0 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 :=
    le_trans (by nlinarith) hf_ge
  have h1_f : 1 ≤ fastDFTRecursiveSteps (scaledSubMulCost mulTime) K0 p0 2 :=
    le_trans (by nlinarith) hf_ge
  have h0_sb : 0 ≤ scheduleBitsLen w := Nat.zero_le _
  have h0_fs : 0 ≤ fullScheduleTableBitsLen w := Nat.zero_le _
  have h0_st : 0 ≤ scheduleTreeGenOps (scaledSubMulCost mulTime) K0 p0 := Nat.zero_le _
  have h0_sm : 0 ≤ R0 * scaledSubMulCost mulTime (p0 + 2) := Nat.zero_le _
  have h0_w : 0 ≤ w := Nat.zero_le _
  refine ⟨t1 + (t2 + (t3 + (t4 + t5))), ?_, hall⟩
  dsimp only
  rw [hstep_def]
  linarith only [ht1', ht2, ht3', ht4, ht5', hRP_f, hR0_f, h1_f, h0_sb, h0_fs, h0_st, h0_sm, h0_w]

/-! ## 6. The Concrete 3-Tier Multiplier (`bmMulTier0/1/2`), `tmIntMul : Turing.FinTM2` & End-to-End $O(n \log n)$ Theorem (Theorem 2 (`thm:lean`), Section 8 (`sec:lean`)) -/

/-- Depth `d = 0` uniform `BitMachine` multiplier: bit-by-bit shift-and-add (`bmShiftAddMulBits`). -/
def bmMulTier0 : BitMachine := bmShiftAddMulBits

/-- Step bound for `bmMulTier0`. -/
def mulTimeTier0 (w : ℕ) : ℕ := 11 * w * w + 750 * w + 1300

theorem isBitMulMachine_bmMulTier0 : IsBitMulMachine bmMulTier0 mulTimeTier0 :=
  isBitMulMachine_bmShiftAddMulBits

theorem mulTimeTier0_le_schoolbook {w : ℕ} (hw : 1 ≤ w) :
    mulTimeTier0 w ≤ 2061 * schoolbookSubMulBitOps w := by
  unfold mulTimeTier0 schoolbookSubMulBitOps
  have hw2 : w ≤ w * w := Nat.le_mul_self w
  have h1 : 1 ≤ w * w := by nlinarith
  nlinarith

theorem scaledSubMulCost_mulTimeTier0_le {q : ℕ} (hq : 1 ≤ q) :
    scaledSubMulCost mulTimeTier0 q ≤ (1010141 * 2061) * schoolbookSubMulBitOps q := by
  unfold scaledSubMulCost
  have hq1 := mulTimeTier0_le_schoolbook hq
  have hq2 := mulTimeTier0_le_schoolbook (show 1 ≤ 2 * q by omega)
  have hq6 := mulTimeTier0_le_schoolbook (show 1 ≤ 6 * q by omega)
  have hq10 := mulTimeTier0_le_schoolbook (show 1 ≤ 10 * q by omega)
  have hq100 := mulTimeTier0_le_schoolbook (show 1 ≤ 100 * q by omega)
  have hq1000 := mulTimeTier0_le_schoolbook (show 1 ≤ 1000 * q by omega)
  unfold schoolbookSubMulBitOps at *
  nlinarith

/-- Depth `d = 1` uniform `BitMachine` multiplier: `bmFastNatMulWith bmMulTier0`. -/
def bmMulTier1 : BitMachine := bmFastNatMulWith bmMulTier0

/-- Step bound for `bmMulTier1`. -/
def mulTimeTier1 (w : ℕ) : ℕ :=
  15000000000000 * intMulAlgorithmSteps (scaledSubMulCost mulTimeTier0) w

theorem isBitMulMachine_bmMulTier1 : IsBitMulMachine bmMulTier1 mulTimeTier1 :=
  isBitMulMachine_bmFastNatMulWith isBitMulMachine_bmMulTier0

/-- Explicit uniform constant bounding `mulTimeTier1 w ≤ C_tm_d1 * nestedSubMulBitOps w`. -/
def C_tm_d1 : ℕ := 15000000000000 * (1010141 * 2061)

theorem mulTimeTier1_le_nestedSubMulBitOps {w : ℕ} (hw : 1 ≤ w) :
    mulTimeTier1 w ≤ C_tm_d1 * nestedSubMulBitOps w := by
  unfold mulTimeTier1 C_tm_d1 nestedSubMulBitOps
  rw [if_neg (by omega : w ≠ 0)]
  have hscale := intMulAlgorithmSteps_scale_le_of_pos_bounded
    (M1 := scaledSubMulCost mulTimeTier0) (M2 := schoolbookSubMulBitOps)
    (n := w) (C := 1010141 * 2061) (by decide)
    (fun _ hq _ => scaledSubMulCost_mulTimeTier0_le hq)
  linarith

theorem scaledSubMulCost_mulTimeTier1_le {q : ℕ} (hq : 1 ≤ q) :
    scaledSubMulCost mulTimeTier1 q ≤ C_tm_d1 * scaledSubMulCost nestedSubMulBitOps q := by
  unfold scaledSubMulCost
  have h1 := mulTimeTier1_le_nestedSubMulBitOps hq
  have h2 := mulTimeTier1_le_nestedSubMulBitOps (show 1 ≤ 2 * q by omega)
  have h6 := mulTimeTier1_le_nestedSubMulBitOps (show 1 ≤ 6 * q by omega)
  have h10 := mulTimeTier1_le_nestedSubMulBitOps (show 1 ≤ 10 * q by omega)
  have h100 := mulTimeTier1_le_nestedSubMulBitOps (show 1 ≤ 100 * q by omega)
  have h1000 := mulTimeTier1_le_nestedSubMulBitOps (show 1 ≤ 1000 * q by omega)
  linarith

/-- Depth `d = 2` (top-level) uniform `BitMachine` multiplier: `bmFastNatMulWith bmMulTier1`. -/
def bmMulTier2 : BitMachine := bmFastNatMulWith bmMulTier1

/-- Step bound for `bmMulTier2`. -/
def mulTimeTier2 (n : ℕ) : ℕ :=
  15000000000000 * intMulAlgorithmSteps (scaledSubMulCost mulTimeTier1) n

theorem isBitMulMachine_bmMulTier2 : IsBitMulMachine bmMulTier2 mulTimeTier2 :=
  isBitMulMachine_bmFastNatMulWith isBitMulMachine_bmMulTier1

/-- Explicit uniform constant bounding `mulTimeTier2 n ≤ C_tm_d2 * n * Nat.log 2 n` for all `n ≥ 2`. -/
def C_tm_d2 : ℕ := 15000000000000 * C_tm_d1 * (2 * C_nested_total)

theorem mulTimeTier2_le_n_log_n {n : ℕ} (hn : 2 ≤ n) :
    mulTimeTier2 n ≤ C_tm_d2 * n * Nat.log 2 n := by
  unfold mulTimeTier2 C_tm_d2
  have hC1 : 1 ≤ C_tm_d1 := by unfold C_tm_d1; decide
  have hscale := intMulAlgorithmSteps_scale_le_of_pos_bounded
    (M1 := scaledSubMulCost mulTimeTier1) (M2 := scaledSubMulCost nestedSubMulBitOps)
    (n := n) (C := C_tm_d1) hC1
    (fun _ hq _ => scaledSubMulCost_mulTimeTier1_le hq)
  have hnested := intMulAlgorithmSteps_scaled_nestedSubMulBitOps_le_n_log_n hn
  calc 15000000000000 * intMulAlgorithmSteps (scaledSubMulCost mulTimeTier1) n
      ≤ 15000000000000 * (C_tm_d1 * intMulAlgorithmSteps (scaledSubMulCost nestedSubMulBitOps) n) :=
        Nat.mul_le_mul_left _ hscale
    _ ≤ 15000000000000 * (C_tm_d1 * ((2 * C_nested_total) * n * Nat.log 2 n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hnested)
    _ = (15000000000000 * C_tm_d1 * (2 * C_nested_total)) * n * Nat.log 2 n := by ring

/-- Core delimited-I/O `BitMachine` for `tmIntMul`:
consumes `encodeDelimWord (encodeInputBits n A B)` on `kIO`, recovers `n = inBits.length / 2` via
`bmHalfLenUnary`, splits `inBits` into `(encodeNatBits n A, encodeNatBits n B)`, and runs `bmMulTier2`. -/
def bmIntMulCore : BitMachine :=
  bmSeq
    (bmSeq
      (bmFanout bmHalfLenUnary bmId)
      (bmFanout bmFst (bmFanout bmTakePadBits bmDropBits)))
    bmMulTier2

theorem bmIntMulCore_computesInTime (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (tW2 tW3 tW4 tW5 tSch : List Bool) :
    ∃ t ≤ mulTimeTier2 n + 200 * n + 200,
      bmIntMulCore.ComputesInTime
        (mkTapes8 (encodeDelimWord (encodeInputBits n A B)) [] [] tW2 tW3 tW4 tW5 tSch)
        (mkTapes8 (encodeDelimWord (encodeNatBits (2 * n) (A * B))) [] [] tW2 tW3 tW4 tW5 tSch) t := by
  let inBits := encodeInputBits n A B
  have hin_len : inBits.length = 2 * n := encodeInputBits_length n A B
  have hhalf : inBits.length / 2 = n := by rw [hin_len]; omega
  let S := Unit
  let uIn : S → List Bool := fun _ => inBits
  have pN := StageEval.congr_out (v2 := fun _ : S => encUnary n)
    (StageEval.of_computesStageLe (bmHalfLenUnary_computesStageLe id) uIn)
    (fun _ => by dsimp [uIn]; rw [hhalf])
  have pId := StageEval.id_stage uIn
  have pPair := StageEval.fanout pN pId
  have pN2 := StageEval.fst (fun _ : S => encUnary n) uIn
  have pTake := StageEval.congr_out (v2 := fun _ : S => encodeNatBits n A)
    (StageEval.takePadBits_stage (fun _ : S => n) uIn)
    (fun _ => by
      dsimp only [uIn, inBits]
      unfold encodeInputBits
      have h := takePadBits_append_of_length_eq (encodeNatBits n A) (encodeNatBits n B)
      rwa [encodeNatBits_length] at h)
  have pDrop := StageEval.congr_out (v2 := fun _ : S => encodeNatBits n B)
    (StageEval.dropBits (fun _ : S => n) uIn)
    (fun _ => by dsimp only [uIn, inBits]; exact drop_encodeInputBits n A B)
  have pMulInput := StageEval.seq pPair (StageEval.fanout pN2 (StageEval.fanout pTake pDrop))
  have pMul : StageEval (S := S) bmMulTier2
      (encDepPair (fun _ => encUnary n)
        (encDepPair (fun _ => encodeNatBits n A) (fun _ => encodeNatBits n B)))
      (fun _ => encodeNatBits (2 * n) (A * B))
      (fun _ => mulTimeTier2 n) := by
    intro _ u2 u3 u4 u5 uS
    have hm := isBitMulMachine_bmMulTier2 n (encodeNatBits n A) (encodeNatBits n B)
      (encodeNatBits_length n A) (encodeNatBits_length n B) u2 u3 u4 u5 uS
    simpa only [encDepPair, encPair, encBits, id,
      decodeNatBits_encodeNatBits n A hA, decodeNatBits_encodeNatBits n B hB] using hm
  have hall := StageEval.seq pMulInput pMul
  rcases hall () tW2 tW3 tW4 tW5 tSch with ⟨t, ht, hcomp⟩
  dsimp only [uIn, inBits, id] at ht hcomp
  simp only [length_encDepPair, length_encUnary, encodeInputBits_length,
    encodeNatBits_length] at ht
  exact ⟨t, by omega, hcomp⟩

/-- **The Concrete, Inhabited, Parameter-Free Uniform 8-Stack Binary Machine (`tmIntMul`,
Theorem 2 (`thm:lean`), Section 8 (`sec:lean`))**:
A single fixed `Turing.FinTM2` machine (independent of $n, K, p, R, A, B$) with 8 binary stacks
(`Γ k = Bool`), 32 internal register states (`σ = DelimReg`), and $O(1)$ finite control labels `Λ`
that evaluates `Turing.initList tmIntMul (encodeInputBits n A B)` to
`some (Turing.haltList tmIntMul (encodeNatBits (2 * n) (A * B)))` in $O(n \log n)$ `TM2.step` transitions. -/
def tmIntMul : Turing.FinTM2 :=
  (bmRunRaw bmIntMulCore).toFinTM2

/-- Uniform state-space theorem (`IsUniformFinTM2`) for `tmIntMul` (Section 8 (`sec:lean`)). -/
theorem isUniformFinTM2_tmIntMul :
    IsUniformFinTM2 tmIntMul (bmRunRaw bmIntMulCore).numLabels 32 2 :=
  (bmRunRaw bmIntMulCore).isUniform le_rfl

/-- Explicit uniform constant `C_tm_total > 0` for the end-to-end `tmIntMul` $O(n \log n)$ theorem. -/
def C_tm_total : ℕ := C_tm_d2 + 500

theorem C_tm_total_pos : 0 < C_tm_total := by
  unfold C_tm_total; omega

/-- **End-to-End $O(n \log n)$ Time-Complexity & Bit-Exactness Theorem on `Turing.FinTM2`
(`tmIntMul_evalsToInTime_n_log_n`, Theorem 2 (`thm:lean`), Section 8 (`sec:lean`))**:
There exists an explicit uniform constant $C > 0$ (`C_tm_total`) such that for all $n \ge 2$ and all
$n$-bit integers $A, B < 2^n$, the single uniform 8-stack binary machine `tmIntMul : Turing.FinTM2`
evaluates `Turing.initList tmIntMul (encodeInputBits n A B)` to
`some (Turing.haltList tmIntMul (encodeNatBits (2 * n) (A * B)))` in
$t \le C \cdot n \cdot \lfloor\log_2 n\rfloor$ `TM2.step` transitions. -/
theorem tmIntMul_evalsToInTime_n_log_n :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      ∃ t ≤ C * n * Nat.log 2 n,
        Turing.EvalsToInTime tmIntMul.step
          (Turing.initList tmIntMul (encodeInputBits n A B))
          (some (Turing.haltList tmIntMul (encodeNatBits (2 * n) (A * B)))) t := by
  refine ⟨C_tm_total, C_tm_total_pos, ?_⟩
  intro n hn A B hA hB
  let inBits := encodeInputBits n A B
  let outBits := encodeNatBits (2 * n) (A * B)
  have h1 := tmRawToDelimRev_computesInTime kIO kWork0 (by decide) inBits []
    (mkTapes8 [] [] [] [] [] [] [] [])
  simp only [update_mkTapes8_kIO, update_mkTapes8_kWork0, List.append_nil] at h1
  have h2 := tmRevMoveWord_computesInTime kWork0 kIO (by decide) inBits.reverse [] []
    (mkTapes8 [] [] [] [] [] [] [] [])
  simp only [update_mkTapes8_kWork0, update_mkTapes8_kIO, List.length_reverse,
    List.reverse_reverse, List.append_nil] at h2
  rcases bmIntMulCore_computesInTime n A B hA hB [] [] [] [] [] with ⟨tm, htm, h3⟩
  have h4 := tmDelimIOToRawIO_computesInTime outBits
  have hall := h1.seq (h2.seq (h3.seq h4))
  rw [← initList_stk_eq_mkTapes8 (bmRunRaw bmIntMulCore) inBits,
    ← haltList_stk_eq_mkTapes8 (bmRunRaw bmIntMulCore) outBits] at hall
  rcases hall with ⟨heval⟩
  have hin_len : inBits.length = 2 * n := encodeInputBits_length n A B
  have hout_len : outBits.length = 2 * n := encodeNatBits_length (2 * n) (A * B)
  have htier2 := mulTimeTier2_le_n_log_n hn
  have hlog1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hn_le : n ≤ n * Nat.log 2 n := Nat.le_mul_of_pos_right n hlog1
  have h1_le : 1 ≤ n * Nat.log 2 n := le_trans (by omega) hn_le
  refine ⟨(inBits.length + 2) + ((inBits.length + 2) + (tm + (2 * outBits.length + 3))), ?_, ⟨heval⟩⟩
  rw [hin_len, hout_len]
  unfold C_tm_total
  nlinarith

/-- **Complete End-to-End Unconditional Formalization Summary (`intMul_complete_endToEnd_summary`,
Theorem 1 (`thm:main`) and Theorem 2 (`thm:lean`), Section 8 (`sec:lean`))**:
Combines into a single theorem:
1. The uniform state-space bound `IsUniformFinTM2 tmIntMul (bmRunRaw bmIntMulCore).numLabels 32 2`;
2. The unconditional $O(n \log n)$ `Turing.FinTM2` evaluation theorem
   (`tmIntMul_evalsToInTime_n_log_n`); and
3. Exactness and unconditional $O(n \log n)$ `CostM` bit-operation bounds for
   `computableNatMulBitsTracked` and `computableNatMulTracked`
   (`computableNatMulBitsTracked_spec`, `computableNatMulTracked_spec`). -/
theorem intMul_complete_endToEnd_summary :
    IsUniformFinTM2 tmIntMul (bmRunRaw bmIntMulCore).numLabels 32 2 ∧
    (∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      ∃ t ≤ C * n * Nat.log 2 n,
        Turing.EvalsToInTime tmIntMul.step
          (Turing.initList tmIntMul (encodeInputBits n A B))
          (some (Turing.haltList tmIntMul (encodeNatBits (2 * n) (A * B)))) t) ∧
    (∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      ((computableNatMulBitsTracked n (encodeInputBits n A B)).1 =
          encodeNatBits (2 * n) (A * B) ∧
        (computableNatMulBitsTracked n (encodeInputBits n A B)).2 ≤
          C * n * Nat.log 2 n) ∧
      ((computableNatMulTracked n A B).1 = A * B ∧
        (computableNatMulTracked n A B).2 ≤ C * n * Nat.log 2 n)) :=
  ⟨isUniformFinTM2_tmIntMul,
   tmIntMul_evalsToInTime_n_log_n,
   ⟨C_tracked_total, C_tracked_total_pos,
    fun n hn A B hA hB =>
      ⟨⟨computableNatMulBitsTracked_fst_encodeInputBits n A B hA hB,
        computableNatMulBitsTracked_snd_le hn (encodeInputBits n A B)⟩,
       ⟨computableNatMulTracked_fst n A B hA hB,
        computableNatMulTracked_snd_le hn hA hB⟩⟩⟩⟩

end IntMul

#print axioms IntMul.tmIntMul
#print axioms IntMul.isUniformFinTM2_tmIntMul
#print axioms IntMul.tmIntMul_evalsToInTime_n_log_n
#print axioms IntMul.intMul_complete_endToEnd_summary

