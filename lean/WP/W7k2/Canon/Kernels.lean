import WP.W7k2.Canon.Series

/-!
# WP.W7k2.Canon.Kernels — canonical straight-line forms of the four W7k2 kernels

Step (1) of W7k2. Each kernel of `Contracts.W7.Kernels` is the `.1` of a snapshot primitive in
`ComputableTranscendentals.lean` (CTr). Here each one is restated as a straight-line definition
whose `let`s are single machine operations (one W3 / W5 / W6a call, a kernel call, or the series
loop `serState`), and proved equal to the snapshot's value:

| Canonical form | Snapshot value (`.1`) | Theorem |
|---|---|---|
| `stdCharC q num den neg πN` | `computableStdCharWithProgramCost q num den neg` (CTr:2372) | `stdCharC_eq` |
| `sincClampC`, `expClampC` | `computableSincRationalClamp`, `computableExpNegRationalClamp` (CTr:3263, 3366) | `sincClampC_eq`, `expClampC_eq` |
| `tapC p_work pSub t1 j1 s πN lnN` | `computableSincGaussianTapWithProgramCost` (CTr:3619) | `tapC_eq` |
| `halfErfC` | `computableHalfErfScaledInner` (CTr:4826) | `halfErfC_eq` |
| `c0c1C p_work pSub r u2 πN lnN` | real parts of `computableC0C1WithProgramCost` (CTr:5068) | `c0c1C_eq` |
| `colRecipC H d` | `W7.colRecip H r u2 a c` (W6b's `μ`) | `colRecip_eq_colRecipC` |

`π` and `ln 2` enter as **natural numbers** `πN = πZ.toNat`, `lnN = lnZ.toNat`, exactly where the
snapshot applies `Int.toNat`. The machine reads the signed values `W7_piScaled` / `W7_log2Scaled`
push and strips the sign; `piScaled_pos` and `log2Scaled_pos` show the sign is `pos`, so stripping is
`toNat`. All other `Int.toNat`s of the snapshot are applied to products of naturals and disappear
(`toNat_natCast_mul`).

**Positivity facts the machine needs** (W6a's `divRound` requires a positive denominator):
* `π·2^B ≥ 1` for every `B` (`piScaled_pos`); hence `P = Nat.sqrt πN ≥ 1` (`sqrt_piN_pos`).
* `ln 2·2^B ≥ 1` for `B ≥ 1` (`log2Scaled_pos`).
-/

namespace WP.W7k2

open IntMul

/-! ## Small arithmetic helpers -/

theorem toNat_natCast_mul (a b : ℕ) : ((a : ℤ) * (b : ℤ)).toNat = a * b := by
  rw [← Nat.cast_mul, Int.toNat_natCast]

theorem toNat_natCast_mul4 (a b c d : ℕ) :
    (((a : ℤ) * (b : ℤ)) * ((c : ℤ) * (d : ℤ))).toNat = a * b * (c * d) := by
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul, Int.toNat_natCast]

/-! ## `π` and `ln 2` are positive -/

theorem piScaled_nonneg (B : ℕ) : 0 ≤ (computablePiScaledWithCost B).1 :=
  (computablePiScaledWithCost_error_le B).2

theorem piScaled_pos (B : ℕ) : 1 ≤ (computablePiScaledWithCost B).1 := by
  obtain ⟨herr, -⟩ := computablePiScaledWithCost_error_le B
  have hpow : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hzp : (2 : ℝ) ^ (-(B : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have h1 := (abs_le.mp herr).1
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hdiv : (0 : ℝ) < ((computablePiScaledWithCost B).1 : ℝ) / (2 : ℝ) ^ B := by linarith
  have hx : (0 : ℝ) < ((computablePiScaledWithCost B).1 : ℝ) := by
    have := (div_pos_iff_of_pos_right hpow).mp hdiv
    exact this
  have : (0 : ℤ) < (computablePiScaledWithCost B).1 := by exact_mod_cast hx
  omega

theorem log2Scaled_pos (B : ℕ) (hB : 1 ≤ B) : 1 ≤ (computableLog2ScaledWithCost B).1 := by
  have herr := computableLog2ScaledWithCost_error_le B
  have hpow : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hzp : (2 : ℝ) ^ (-(B : ℤ)) ≤ 1 / 2 := by
    rw [zpow_neg, zpow_natCast, one_div]
    have h2B : (2 : ℝ) ≤ 2 ^ B := by
      have := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hB
      simpa using this
    exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr h2B
  have h1 := (abs_le.mp herr).1
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hdiv : (0 : ℝ) < ((computableLog2ScaledWithCost B).1 : ℝ) / (2 : ℝ) ^ B := by linarith
  have hx : (0 : ℝ) < ((computableLog2ScaledWithCost B).1 : ℝ) :=
    (div_pos_iff_of_pos_right hpow).mp hdiv
  have : (0 : ℤ) < (computableLog2ScaledWithCost B).1 := by exact_mod_cast hx
  omega

/-- The natural `π` value is the signed one (it is non-negative). -/
theorem piScaled_toNat_cast (B : ℕ) :
    (((computablePiScaledWithCost B).1.toNat : ℕ) : ℤ) = (computablePiScaledWithCost B).1 :=
  Int.toNat_of_nonneg (piScaled_nonneg B)

theorem log2Scaled_toNat_cast (B : ℕ) (hB : 1 ≤ B) :
    (((computableLog2ScaledWithCost B).1.toNat : ℕ) : ℤ) = (computableLog2ScaledWithCost B).1 :=
  Int.toNat_of_nonneg (by have := log2Scaled_pos B hB; omega)

theorem piN_pos (B : ℕ) : 1 ≤ (computablePiScaledWithCost B).1.toNat := by
  have := piScaled_pos B
  omega

theorem lnN_pos (B : ℕ) (hB : 1 ≤ B) : 1 ≤ (computableLog2ScaledWithCost B).1.toNat := by
  have := log2Scaled_pos B hB
  omega

theorem sqrt_piN_pos (B : ℕ) : 1 ≤ Nat.sqrt (computablePiScaledWithCost B).1.toNat := by
  have h := piN_pos B
  rw [Nat.le_sqrt]
  omega

/-! ## `stdChar` (CTr:2335-2378) -/

/-- `stdChar` with symbolic precision parameters (`B`, `B_pi`, `N`, `Bint`); `πN = π·2^B_pi`. -/
def stdCharGen (B Bpi N Bint num den : ℕ) (neg : Bool) (πN : ℕ) : ℤ × ℤ :=
  let numTheta : ℕ := 2 * πN * num
  let denTheta : ℕ := den * 2 ^ Bpi
  let negSq : ℤ := -((numTheta : ℤ) * (numTheta : ℤ))
  let denSq : ℕ := denTheta * denTheta
  let cosS : ℤ := (serState ((2 ^ Bint : ℕ) : ℤ) negSq denSq (fun _ => 1)
    (fun k => (2 * k + 1) * (2 * k + 2)) N).2
  let re : ℤ := IntMul.divRoundRatInt (cosS * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  let sinA0 : ℤ := IntMul.divRoundRatInt ((numTheta : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denTheta : ℤ)
  let sinS : ℤ := (serState sinA0 negSq denSq (fun _ => 1)
    (fun k => (2 * k + 2) * (2 * k + 3)) N).2
  let imPos : ℤ := IntMul.divRoundRatInt (sinS * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  (re, if neg then -imPos else imPos)

/-- Canonical `stdChar((±num)/den)` on the `2^(q+2)` grid. `πN = π·2^(q+6)` (natural). -/
def stdCharC (q num den : ℕ) (neg : Bool) (πN : ℕ) : ℤ × ℤ :=
  stdCharGen (q + 2) (q + 2 + 4) (q + 2 + 25) (q + 2 + 2 * (q + 2 + 25) + 22) num den neg πN

/-- The snapshot's `computableStdCharCore` (CTr:2335) with the `π` result `piRes` abstracted
(verbatim copy of the value part; `stdCharCore_given` is `rfl`). -/
def stdCharCoreGiven (B B_pi N Bint w num den : ℕ) (neg : Bool) (piRes : BitCostM ℤ) : ℤ × ℤ :=
  let piNat := piRes.1.toNat
  let numThetaRes := costedMulInt w ((2 * piNat : ℕ) : ℤ) (num : ℤ)
  let numTheta : ℕ := numThetaRes.1.toNat
  let denThetaRes := costedShiftLeftNat w den B_pi
  let denTheta : ℕ := denThetaRes.1
  let numThetaSqRes := costedMulInt w (numTheta : ℤ) (numTheta : ℤ)
  let negNumThetaSqRes := costedNegInt0 numThetaSqRes.1
  let negNumThetaSq : ℤ := negNumThetaSqRes.1
  let denThetaSqRes := costedMulInt w (denTheta : ℤ) (denTheta : ℤ)
  let denThetaSq : ℕ := denThetaSqRes.1.toNat
  let cosSeriesRes := runRecurrenceSeriesCosted w ((2 ^ Bint : ℕ) : ℤ)
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 1) * (2 * k + 2)) N
  let cosShiftRes := costedShiftLeftInt w cosSeriesRes.1.2 B
  let reRes := costedDivRoundRatInt w cosShiftRes.1 ((2 ^ Bint : ℕ) : ℤ)
  let sinA0ShiftRes := costedShiftLeftInt w (numTheta : ℤ) Bint
  let sinA0Res := costedDivRoundRatInt w sinA0ShiftRes.1 (denTheta : ℤ)
  let sinSeriesRes := runRecurrenceSeriesCosted w sinA0Res.1
    negNumThetaSq denThetaSq (fun _ => 1) (fun k => (2 * k + 2) * (2 * k + 3)) N
  let sinShiftRes := costedShiftLeftInt w sinSeriesRes.1.2 B
  let imPosRes := costedDivRoundRatInt w sinShiftRes.1 ((2 ^ Bint : ℕ) : ℤ)
  let imIntRes := costedCondNegInt0 neg imPosRes.1
  (reRes.1, imIntRes.1)

theorem stdCharCore_given (B B_pi N Bint w num den : ℕ) (neg : Bool) :
    (computableStdCharCore B B_pi N Bint w num den neg).1 =
      stdCharCoreGiven B B_pi N Bint w num den neg (computablePiScaledWithCost B_pi) := rfl

theorem stdCharGen_eq_given (B Bpi N Bint w num den : ℕ) (neg : Bool) (piRes : BitCostM ℤ) :
    stdCharGen B Bpi N Bint num den neg piRes.1.toNat =
      stdCharCoreGiven B Bpi N Bint w num den neg piRes := by
  simp only [stdCharGen, stdCharCoreGiven, costedMulInt, costedDivRoundRatInt,
    runRecurrenceSeriesCosted_fst_eq, toNat_natCast_mul]

theorem stdCharC_eq (q num den : ℕ) (neg : Bool) :
    stdCharC q num den neg (computablePiScaledWithCost (q + 2 + 4)).1.toNat =
      (computableStdCharWithProgramCost q num den neg).1 :=
  (stdCharGen_eq_given _ _ _ _ _ num den neg _).trans (stdCharCore_given _ _ _ _ _ _ _ _).symm

/-! ## Sinc·Gaussian tap (CTr:3263-3626) -/

/-- Canonical `normSinc` clamp (CTr:3263). -/
def sincClampC (B N Bint numTheta denTheta : ℕ) : ℤ :=
  let negSq : ℤ := -((numTheta : ℤ) * (numTheta : ℤ))
  let denSq : ℕ := denTheta * denTheta
  let S : ℤ := (serState ((2 ^ Bint : ℕ) : ℤ) negSq denSq (fun _ => 1)
    (fun k => (2 * k + 2) * (2 * k + 3)) N).2
  let raw : ℤ := IntMul.divRoundRatInt (S * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  max (-((2 ^ B : ℕ) : ℤ)) (min ((2 ^ B : ℕ) : ℤ) raw)

/-- Canonical `exp(-y)` clamp (CTr:3366). -/
def expClampC (B N Bint numY denY : ℕ) : ℤ :=
  let S : ℤ := (serState ((2 ^ Bint : ℕ) : ℤ) (-(numY : ℤ)) denY (fun _ => 1)
    (fun k => k + 1) N).2
  let raw : ℤ := IntMul.divRoundRatInt (S * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Bint : ℕ) : ℤ)
  max (-((2 ^ B : ℕ) : ℤ)) (min ((2 ^ B : ℕ) : ℤ) raw)

theorem sincClampC_eq (B N Bint w numTheta denTheta : ℕ) :
    sincClampC B N Bint numTheta denTheta =
      (computableSincRationalClamp B N Bint w numTheta denTheta).1 := by
  simp only [sincClampC, computableSincRationalClamp, costedMulInt, costedDivRoundRatInt,
    runRecurrenceSeriesCosted_fst_eq, toNat_natCast_mul]

theorem expClampC_eq (B N Bint w numY denY : ℕ) :
    expClampC B N Bint numY denY = (computableExpNegRationalClamp B N Bint w numY denY).1 := by
  simp only [expClampC, computableExpNegRationalClamp, costedDivRoundRatInt,
    runRecurrenceSeriesCosted_fst_eq]

/-- Canonical tap at `(s - pSub) - j1/t1`. `πN`, `lnN` are `π`, `ln 2` at `W7.tapPrec pSub`. -/
def tapC (p_work pSub t1 j1 s πN lnN : ℕ) : ℤ :=
  let B := pSub + 2
  let Mθ := 4 * (pSub + 1)
  let N := 4 * Mθ + B + 4
  let Bc := B + N + 3 * Mθ + 6
  let Bint := B + 2 * N + 2 * Mθ + 6
  let numT : ℕ := (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ) - (j1 : ℤ)).natAbs
  let numTheta : ℕ := πN * numT
  let denTheta : ℕ := t1 * 2 ^ Bc
  let numY : ℕ := numTheta * numTheta
  let denY : ℕ := 4 * p_work * lnN * (t1 * t1) * 2 ^ Bc
  if (((B + 2 : ℕ) : ℤ) * (denY : ℤ)) ≤ (numY : ℤ) then 0
  else
    let prod : ℤ := sincClampC B N Bint numTheta denTheta * expClampC B N Bint numY denY
    let rnd : ℤ := IntMul.divRoundRatInt (prod * ((2 ^ pSub : ℕ) : ℤ)) ((2 ^ (2 * B) : ℕ) : ℤ)
    max (-((2 ^ pSub : ℕ) : ℤ)) (min ((2 ^ pSub : ℕ) : ℤ) rnd)

theorem tapC_eq_given (p_work pSub t1 j1 s : ℕ) (piRes log2Res : BitCostM ℤ) :
    tapC p_work pSub t1 j1 s piRes.1.toNat log2Res.1.toNat =
      (computableSincGaussianTapGivenPiLog2 p_work pSub t1 piRes log2Res j1 s).1 := by
  simp only [tapC, computableSincGaussianTapGivenPiLog2, computableSincGaussianTapInner,
    costedMulInt, costedDivRoundRatInt, toNat_natCast_mul, toNat_natCast_mul4,
    ← sincClampC_eq, ← expClampC_eq]
  split_ifs <;> rfl

theorem tapC_eq (p_work pSub t1 j1 s : ℕ) :
    tapC p_work pSub t1 j1 s (computablePiScaledWithCost (TMFw.Contracts.W7.tapPrec pSub)).1.toNat
        (computableLog2ScaledWithCost (TMFw.Contracts.W7.tapPrec pSub)).1.toNat =
      (computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1 := by
  rw [tapC_eq_given, TMFw.Contracts.W7.tapGiven_eq]

/-! ## Passband coefficients `c0`, `c1` (CTr:4826, 5029-5078) -/

/-- Canonical half-erf (CTr:4826), with `A = √(4·p_work·ln 2)` and `P = √π` (scaled). -/
def halfErfC (Be S N Bint A P numX denX : ℕ) : ℤ :=
  let numZ : ℕ := A * numX
  let denZ : ℕ := denX * 2 ^ S
  let negSq : ℤ := -((numZ : ℤ) * (numZ : ℤ))
  let denSq : ℕ := denZ * denZ
  let a0 : ℤ := IntMul.divRoundRatInt ((numZ : ℤ) * ((2 ^ Bint : ℕ) : ℤ)) (denZ : ℤ)
  let E : ℤ := (serState a0 negSq denSq (fun k => 2 * k + 1)
    (fun k => (k + 1) * (2 * k + 3)) N).2
  IntMul.divRoundRatInt (E * ((2 ^ S : ℕ) : ℤ) * ((2 ^ Be : ℕ) : ℤ)) ((P * 2 ^ Bint : ℕ) : ℤ)

theorem halfErfC_eq (Be S N Bint w A P numX denX : ℕ) :
    halfErfC Be S N Bint A P numX denX =
      (computableHalfErfScaledInner Be S N Bint w A P numX denX).1 := by
  simp only [halfErfC, computableHalfErfScaledInner, costedMulInt, costedDivRoundRatInt,
    runRecurrenceSeriesCosted_fst_eq, toNat_natCast_mul]

/-- Canonical `(c0.re, c1.re)` from the three half-erf values (CTr:5029-5050). -/
def c0c1InnerC (B Be S N Bint r u2 A P : ℕ) : ℤ × ℤ :=
  let u2' : ℕ := min u2 (r - u2)
  let hPlus := halfErfC Be S N Bint A P (r + 2 * u2') (2 * r)
  let hMinus := halfErfC Be S N Bint A P (r - 2 * u2') (2 * r)
  let hThree := halfErfC Be S N Bint A P (3 * r - 2 * u2') (2 * r)
  let rawHi : ℤ := IntMul.divRoundRatInt ((hPlus + hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Be : ℕ) : ℤ)
  let hiInt : ℤ := max 0 (min ((2 ^ B : ℕ) : ℤ) rawHi)
  let rawLo : ℤ := IntMul.divRoundRatInt ((hThree - hMinus) * ((2 ^ B : ℕ) : ℤ)) ((2 ^ Be : ℕ) : ℤ)
  let loInt : ℤ := min (max 0 (min ((2 ^ B : ℕ) : ℤ) rawLo)) hiInt
  if 2 * u2 < r then (hiInt, loInt) else if 2 * u2 = r then (hiInt, hiInt) else (loInt, hiInt)

/-- The `S` of the c0/c1 evaluator (CTr:5074); `π`, `ln 2` are evaluated at `2·S`. -/
def c0c1S (p_work pSub : ℕ) : ℕ := (pSub + 2 + 2) + 2 * (8 * p_work + 1) + 6

/-- Canonical `(c0.re, c1.re)`. `πN`, `lnN` are `π`, `ln 2` at `2·c0c1S p_work pSub`. -/
def c0c1C (p_work pSub r u2 πN lnN : ℕ) : ℤ × ℤ :=
  let B := pSub + 2
  let Be := B + 2
  let Mz := 8 * p_work + 1
  let Mz2 := 32 * p_work + 1
  let Merf := Mz2 + Mz
  let S := Be + 2 * Mz + 6
  let N := 4 * Mz2 + Be + Mz + 4
  let Bint := Be + 2 * N + 2 * Merf + 6
  c0c1InnerC B Be S N Bint r u2 (Nat.sqrt (4 * p_work * lnN)) (Nat.sqrt πN)

theorem c0c1InnerC_eq (pSub B Be S N Bint w r u2 A P : ℕ) :
    c0c1InnerC B Be S N Bint r u2 A P =
      ((computableC0C1Inner pSub B Be S N Bint w r u2 A P).1.1.1,
        (computableC0C1Inner pSub B Be S N Bint w r u2 A P).1.2.1) := by
  simp only [c0c1InnerC, computableC0C1Inner, costedDivRoundRatInt, costedClampInt,
    ← halfErfC_eq]
  split_ifs <;> rfl

/-- The snapshot's `computableC0C1Core` (CTr:5054) with the `π`, `ln 2` results abstracted
(verbatim copy of the value part; `c0c1Core_given` is `rfl`). -/
def c0c1CoreGiven (p_work pSub B B_e S N Bint w r u2 : ℕ) (piRes log2Res : BitCostM ℤ) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  let pLogRes := costedMulInt w ((4 * p_work : ℕ) : ℤ) (log2Res.1.toNat : ℤ)
  let sqrtLogRes := costedNatSqrt w pLogRes.1.toNat
  let sqrtPiRes := costedNatSqrt w piRes.1.toNat
  (computableC0C1Inner pSub B B_e S N Bint w r u2 sqrtLogRes.1 sqrtPiRes.1).1

theorem c0c1Core_given (p_work pSub B B_e S N Bint w r u2 : ℕ) :
    (computableC0C1Core p_work pSub B B_e S N Bint w r u2).1 =
      c0c1CoreGiven p_work pSub B B_e S N Bint w r u2 (computablePiScaledWithCost (2 * S))
        (computableLog2ScaledWithCost (2 * S)) := rfl

theorem c0c1C_eq_given (p_work pSub r u2 w : ℕ) (piRes log2Res : BitCostM ℤ) :
    c0c1C p_work pSub r u2 piRes.1.toNat log2Res.1.toNat =
      ((c0c1CoreGiven p_work pSub (pSub + 2) (pSub + 2 + 2) (c0c1S p_work pSub)
          (4 * (32 * p_work + 1) + (pSub + 2 + 2) + (8 * p_work + 1) + 4)
          ((pSub + 2 + 2) + 2 * (4 * (32 * p_work + 1) + (pSub + 2 + 2) + (8 * p_work + 1) + 4) +
            2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6) w r u2 piRes log2Res).1.1,
        (c0c1CoreGiven p_work pSub (pSub + 2) (pSub + 2 + 2) (c0c1S p_work pSub)
          (4 * (32 * p_work + 1) + (pSub + 2 + 2) + (8 * p_work + 1) + 4)
          ((pSub + 2 + 2) + 2 * (4 * (32 * p_work + 1) + (pSub + 2 + 2) + (8 * p_work + 1) + 4) +
            2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6) w r u2 piRes log2Res).2.1) := by
  simp only [c0c1C, c0c1CoreGiven, c0c1S, costedMulInt, costedNatSqrt, toNat_natCast_mul]
  exact c0c1InnerC_eq _ _ _ _ _ _ _ _ _ _ _

theorem c0c1C_eq (p_work pSub r u2 : ℕ) :
    c0c1C p_work pSub r u2 (computablePiScaledWithCost (2 * c0c1S p_work pSub)).1.toNat
        (computableLog2ScaledWithCost (2 * c0c1S p_work pSub)).1.toNat =
      ((computableC0C1WithProgramCost p_work pSub r u2).1.1.1,
        (computableC0C1WithProgramCost p_work pSub r u2).1.2.1) :=
  (c0c1C_eq_given p_work pSub r u2 _ _ _).trans
    (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => (z.1.1, z.2.1))
      (c0c1Core_given _ _ _ _ _ _ _ _ _ _)).symm

/-! ## Column reciprocal `μ` (W6b) -/

/-- Canonical `μ = ⌊2^H / d⌋` for a positive divisor `d` (as a natural number). -/
def colRecipC (H d : ℕ) : ℕ := 2 ^ H / d

theorem colRecip_eq_colRecipC (H r u2 : ℕ) (a c : ℤ)
    (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 a c) :
    TMFw.Contracts.W7.colRecip H r u2 a c =
      ((colRecipC H (IntMulTM.Contracts.W8.columnDivisor r u2 a c).toNat : ℕ) : ℤ) := by
  unfold TMFw.Contracts.W7.colRecip colRecipC
  conv_lhs => rw [← Int.toNat_of_nonneg hd.le]
  rw [Int.natCast_div]

#assert_std_axioms toNat_natCast_mul toNat_natCast_mul4 piScaled_nonneg piScaled_pos log2Scaled_pos
  piScaled_toNat_cast log2Scaled_toNat_cast piN_pos lnN_pos sqrt_piN_pos stdCharCore_given
  stdCharGen_eq_given stdCharC_eq sincClampC_eq expClampC_eq tapC_eq_given tapC_eq halfErfC_eq
  c0c1InnerC_eq c0c1Core_given c0c1C_eq_given c0c1C_eq colRecip_eq_colRecipC

end WP.W7k2
