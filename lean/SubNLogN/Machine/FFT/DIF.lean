/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFRun
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Machine.MulBig.Main

/-!
# K4-DIF (`Machine/FFT/DIF.lean`): the record DIF contract `RecordDIFStmt`

**Scope (honest summary).** The main theorems are proved (no `sorry`, no axiom beyond the
standard ones), from the two arithmetic contracts of `Contracts/Arith.lean` taken as hypotheses:
* `recordDIF_of (hHSD : HalfSumDiffStmt) (hCM : CMulTruncStmt) (hMul : MulBigContract) :
  RecordDIFStmt`;
* `recordDIF_holds (hHSD : HalfSumDiffStmt) (hCM : CMulTruncStmt) : RecordDIFStmt`, using the
  proved multiplier `SubNLogN.Machine.MulBig.mulBig_holds`.

`RecordDIFStmt` (`Contracts/FFT.lean`, stage (i) of Theorem 6.5, `thm:direct-fft`, Section 6.4,
"Last axis"): every record of the cube array gets the rounded normalized
DIF levels (half-sum and half-difference exactly, then `Q_q`; the lower output times its table
phase, exact product, then `Q_q`) and then the bit reversal of the coefficient index; the array
becomes `lastAxisFFT q ℓ θt z` (`Math/Walsh/DirectFFT.lean:73`). The header and the table are
restored; private scratch is empty at both ends. Cost
`C·(ℓ·R·mulW(2w+1) + (ℓ+1)·V + 2^ℓ·(w+1)^2 + |header|)`, `R = 2^{m₀}·2^ℓ`, `V = cvolCube m₀ 2^ℓ w`.
Witnesses: `J = 2`, `C = Cfin Ch Cc = 2000 + 10·Ch + 30·Cc`, where `Ch`, `Cc` are the constants of
the two arithmetic contracts. Only `q + 2 ≤ w` is used from `MidShapeOK`.

The sub-kernels are called through `HSDSpec`/`CMSpec` (`DIFLevel.lean`). These are definitional
copies of the bodies of `HalfSumDiffStmt`/`CMulTruncStmt`; `recordDIF_of` checks this by
`have hH : HSDSpec … := hPh`. The arithmetic cost bounds `levelCost_le` and `brCost_le` live in
`DIFFacts.lean`.

**Implementation** (files `DIFBase`, `DIFPass`, `DIFMath`, `DIFLevel`, `DIFMain`, `DIFFacts`,
`DIFRun`): the array is worked on as a blocked array (level `s`: `2^{m₀+s}` records of
`2^{ℓ-s}` coefficients); per level: one stage table gathered from the phase table (Section 6.4),
split of every block into halves, `HalfSumDiffStmt`, the stage table replicated once per block,
`CMulTruncStmt`, record interleave; then `ℓ` bit-reversal passes (deal + coefficientwise merge of
record pairs). Only header field `q` and `w` are read (the cost has the header length);
`ℓ` and `r` are derived from the data (unit rulers).
-/

namespace SubNLogN.Machine.FFT.DIF

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Math.Common SubNLogN.Math.Walsh

theorem midHdr_eq {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) (hrest : List Sym) :
    midHdr q ℓ K w a ++ hrest = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark ::
      (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark ::
        (W9.hdrSyms (List.ofFn a) ++ hrest))))) := by
  simp [midHdr, W9.hdrSyms]

theorem tabSyms_eq (w q ℓ : ℕ) (θt : ℕ → ℂ) :
    tabSyms w q ℓ θt = carrSyms w ((tabInt q ℓ θt).map fun c => [c]) := by
  simp [tabSyms, tabRecs, tabInt, List.map_map, Function.comp_def]

theorem length_carrSyms_encCube (w q m ℓ : ℕ) (z : RArr (Cube m) (2 ^ ℓ)) :
    (carrSyms w (encCube q z)).length = cvolCube m (2 ^ ℓ) w := by
  have h1 : (carrSyms w (encCube q z)).length = cvol w (encCube q z) := rfl
  rw [h1, cvol_eq, ncoef_uniform _ (2 ^ ℓ) (fun row hr => by
    simp only [encCube, encArr, List.mem_map] at hr
    obtain ⟨x, -, rfl⟩ := hr
    simp)]
  simp [encCube, encArr, cubeAddrs, cvolCube]
  ring

theorem length_midHdr {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) :
    bitLen q + bitLen D + bitLen ℓ + bitLen K + bitLen w + 5 ≤ (midHdr q ℓ K w a).length := by
  have := congrArg List.length (midHdr_eq q ℓ K w a [])
  simp only [List.append_nil] at this
  rw [this]
  simp [length_natSyms]
  omega

/-- The final constant. -/
def Cfin (Ch Cc : ℕ) : ℕ := 2000 + 10 * Ch + 30 * Cc

theorem dif_bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  rw [show bitLen n = Nat.size n from IntMulTM.length_encodeNat n]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem mainCost_le (Ch Cc q ℓ m f1 f2 f3 w Hd : ℕ) (hqw : q + 2 ≤ w)
    (hHd : bitLen q + bitLen f1 + bitLen f2 + bitLen f3 + bitLen w + 5 ≤ Hd) :
    setupCost q f1 f2 f3 w ℓ (cvolCube m (2 ^ ℓ) w) +
        (ℓ * (LB Ch Cc w q (2 ^ m * 2 ^ ℓ) + 2) + 2 +
        (ℓ * (BB w (2 ^ m * 2 ^ ℓ) + 2) + 2 +
        (4 * cvolCube m (2 ^ ℓ) w + 2 + cleanupCost w q ℓ))) ≤
      Cfin Ch Cc * (ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + (ℓ + 1) * cvolCube m (2 ^ ℓ) w +
        2 ^ ℓ * (w + 1) ^ 2 + Hd) := by
  have hw1 : 1 ≤ w := by omega
  have hbq : bitLen q + 1 ≤ w := by have := dif_bitLen_le_self q; omega
  have hP1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hT1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hV : cvolCube m (2 ^ ℓ) w = 2 * w * (2 ^ m * 2 ^ ℓ) + 2 ^ m := by
    unfold cvolCube; ring
  have hwR1 : w ≤ w * (2 ^ m * 2 ^ ℓ) := Nat.le_mul_of_pos_right w (by positivity)
  have hwR : (w + 1) * (2 ^ m * 2 ^ ℓ) ≤ cvolCube m (2 ^ ℓ) w := by
    rw [hV]; nlinarith [Nat.mul_le_mul_right (2 ^ m * 2 ^ ℓ) hw1]
  have hqR : (2 ^ m * 2 ^ ℓ + 1) * (bitLen q + 1) ≤ cvolCube m (2 ^ ℓ) w := by
    rw [hV]
    have h1 := Nat.mul_le_mul_left (2 ^ m * 2 ^ ℓ + 1) hbq
    nlinarith [h1, hwR1]
  have h3w : 3 * w ≤ 2 * cvolCube m (2 ^ ℓ) w := by rw [hV]; nlinarith [hwR1]
  have hV1 : 1 ≤ cvolCube m (2 ^ ℓ) w := by rw [hV]; nlinarith [hwR1]
  have hLB : LB Ch Cc w q (2 ^ m * 2 ^ ℓ) + 2 ≤ 262 * cvolCube m (2 ^ ℓ) w +
      3 * (Ch * cvolCube m (2 ^ ℓ) w) + 9 * (Cc * cvolCube m (2 ^ ℓ) w) +
      Cc * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1)) := by
    unfold LB
    have a1 := Nat.mul_le_mul_left Ch hwR
    have a2 : Cc * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + 6 * ((w + 1) * (2 ^ m * 2 ^ ℓ)) +
        (2 ^ m * 2 ^ ℓ + 1) * (bitLen q + 1) + 3 * w) ≤
        Cc * (2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + 9 * cvolCube m (2 ^ ℓ) w) :=
      Nat.mul_le_mul_left Cc (by omega)
    nlinarith [a1, a2, hwR, hV1]
  have hBB : BB w (2 ^ m * 2 ^ ℓ) + 2 ≤ 72 * cvolCube m (2 ^ ℓ) w := by
    unfold BB; omega
  have hL := Nat.mul_le_mul_left ℓ hLB
  have hB := Nat.mul_le_mul_left ℓ hBB
  have hT2 : 2 ^ (ℓ + 1) - 1 ≤ 2 * 2 ^ ℓ := by rw [pow_succ]; omega
  have hTw : w ≤ 2 ^ ℓ * w := Nat.le_mul_of_pos_left w (by positivity)
  unfold setupCost cleanupCost Cfin
  nlinarith [hL, hB, hHd, hT2, hTw, hV1, hT1, hw1,
    Nat.zero_le (ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1)),
    Nat.zero_le (Ch * (ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1))),
    Nat.zero_le (Cc * (ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1))),
    Nat.zero_le (ℓ * cvolCube m (2 ^ ℓ) w), Nat.zero_le (Ch * (ℓ * cvolCube m (2 ^ ℓ) w)),
    Nat.zero_le (Cc * (ℓ * cvolCube m (2 ^ ℓ) w)), Nat.zero_le (Ch * cvolCube m (2 ^ ℓ) w),
    Nat.zero_le (Cc * cvolCube m (2 ^ ℓ) w), Nat.zero_le (2 ^ ℓ * w * w),
    Nat.zero_le (Ch * (2 ^ ℓ * w * w)), Nat.zero_le (Cc * (2 ^ ℓ * w * w)),
    Nat.zero_le (Ch * (2 ^ ℓ * w)), Nat.zero_le (Cc * (2 ^ ℓ * w)),
    Nat.zero_le (Ch * 2 ^ ℓ), Nat.zero_le (Cc * 2 ^ ℓ), Nat.zero_le (Ch * Hd),
    Nat.zero_le (Cc * Hd)]

/-- **`RecordDIFStmt` from the half-sum contract, the product contract and the multiplier
contract** (`CMulTruncStmt` is applied to its premise `hMul`). -/
theorem recordDIF_of (hHSD : HalfSumDiffStmt) (hCM : CMulTruncStmt) (hMul : MulBigContract) :
    RecordDIFStmt := by
  obtain ⟨Ch, hCh⟩ := hHSD
  obtain ⟨Eh, iFh, iDh, Rh, Ph, hRhf, hRhn, hPhc, hPh⟩ := hCh ()
  obtain ⟨Cc, hCc⟩ := hCM hMul
  obtain ⟨Ec, iFc, iDc, Rc, Pc, hRcf, hRcn, hPcc, hPc⟩ := hCc ()
  have hH : HSDSpec Eh Rh Ch Ph := hPh
  have hC : CMSpec Ec Rc Cc Pc := hPc
  refine ⟨2, Cfin Ch Cc, fun _ => ⟨DS ⊕ (Eh ⊕ Ec), inferInstance, inferInstance,
    Option Sym × (Rh × Rc), mainProg (Lens.fst _ _) ((Lens.snd _ _).comp (Lens.fst _ _))
      ((Lens.snd _ _).comp (Lens.snd _ _)) Ph Pc, ?_, ?_,
    closed_mainProg _ _ _ hPhc hPcc, ?_⟩⟩
  · have := hRhf
    have := hRcf
    infer_instance
  · have := hRhn
    have := hRcn
    infer_instance
  · intro q ℓ K w D a θt z rest hrest trest S hcl hshape htab hz hrest' hS0 hS1 hS2
    obtain ⟨-, -, -, -, -, -, -, hqw⟩ := hshape
    have h := runs_main (Lens.fst _ _) ((Lens.snd _ _).comp (Lens.fst _ _))
      ((Lens.snd _ _).comp (Lens.snd _ _)) hH hC S hcl q ℓ (addrBits a) D ℓ K w
      (W9.hdrSyms (List.ofFn a) ++ hrest) θt z rest trest hqw htab hz hrest' hS0
      (by show S (.inl 1) = _; rw [hS1, midHdr_eq])
      (by show S (.inl 2) = _; rw [hS2, tabSyms_eq])
    rw [length_carrSyms_encCube, length_carrSyms_encCube] at h
    exact runs_mono h (fun _ _ => trivial)
      (mainCost_le Ch Cc q ℓ (addrBits a) D ℓ K w _ hqw (length_midHdr q ℓ K w a))

/-- **`RecordDIFStmt`** from the arithmetic contracts `HalfSumDiffStmt` and `CMulTruncStmt`
(`Contracts/Arith.lean`), with the proved multiplier `mulBig_holds`. -/
theorem recordDIF_holds (hHSD : HalfSumDiffStmt) (hCM : CMulTruncStmt) : RecordDIFStmt :=
  recordDIF_of hHSD hCM MulBig.mulBig_holds

end SubNLogN.Machine.FFT.DIF
