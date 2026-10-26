import IntMul.MaterializedAndComputable.WordWidthBounds
import IntMul.MaterializedAndComputable.MaterializedArrays

/-!
# Part 1 — Computable Fixed-Point (`ℤ × ℤ`) Primitives, `toScaledComplex` Bridge, and Contiguous Overlap-Add Spread
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## Fully Computable Fixed-Point Pipeline (`ℤ × ℤ`, Zero `Real`/`Complex`) -/

/-- Nearest-integer arithmetic right shift by `s` bits (`divRoundPow2 x s = ⌊(x + 2^(s-1)) / 2^s⌋`
for `s > 0`, and `x` for `s = 0`). Uses `((2 ^ s : ℕ) : ℤ)` so `Nat.pow` reduces in 1 kernel step. -/
def divRoundPow2 (x : ℤ) (s : ℕ) : ℤ :=
  if s = 0 then x else (x + ((2 ^ (s - 1) : ℕ) : ℤ)) / ((2 ^ s : ℕ) : ℤ)

/-- Exact rounding error bound in `ℤ` for `divRoundPow2`:
for every `s > 0` and `x : ℤ`, `|divRoundPow2 x s * 2^s - x| ≤ 2^(s - 1)`. -/
theorem abs_divRoundPow2_mul_sub_le (x : ℤ) (s : ℕ) (hs : 0 < s) :
    |divRoundPow2 x s * (2 : ℤ) ^ s - x| ≤ (2 : ℤ) ^ (s - 1) := by
  unfold divRoundPow2
  rw [if_neg (by omega)]
  push_cast
  have hpow : (2 : ℤ) ^ s = 2 * (2 : ℤ) ^ (s - 1) := by
    have : s = (s - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ']
  have hpos : (0 : ℤ) < (2 : ℤ) ^ s := by positivity
  have hdiv := Int.mul_ediv_add_emod (x + (2 : ℤ) ^ (s - 1)) ((2 : ℤ) ^ s)
  have hcomm : (2 : ℤ) ^ s * ((x + (2 : ℤ) ^ (s - 1)) / (2 : ℤ) ^ s) =
      ((x + (2 : ℤ) ^ (s - 1)) / (2 : ℤ) ^ s) * (2 : ℤ) ^ s := mul_comm _ _
  have hmod_nonneg : 0 ≤ (x + (2 : ℤ) ^ (s - 1)) % (2 : ℤ) ^ s :=
    Int.emod_nonneg _ hpos.ne'
  have hmod_lt : (x + (2 : ℤ) ^ (s - 1)) % (2 : ℤ) ^ s < (2 : ℤ) ^ s :=
    Int.emod_lt_of_pos _ hpos
  rw [abs_le]
  constructor <;> linarith

/-- Direct Hensel-lifting / Newton-iteration modular inverse of an odd integer `a` modulo `2 ^ m`:
starting from `inv = 1` (inverse mod `2`), `m` iterations of `inv' = (inv * (2 - a * inv)) mod 2^m`
compute the inverse in `ℤ / 2^m ℤ` in `m` arithmetic steps with zero `ZMod` or `WellFounded.fix`. -/
def oddModInvPow2Iter (m : ℕ) (a : ℤ) : ℕ → ℤ
  | 0 => 1
  | s + 1 =>
    let inv := oddModInvPow2Iter m a s
    (inv * (2 - a * inv)) % ((2 ^ m : ℕ) : ℤ)

/-- Direct computable odd-stride column inverse `v1 < 2 ^ k1` satisfying
`(2 * u2 - 1) * v1 ≡ u1 (mod 2 ^ k1)`. -/
def computableOddStrideInvPow2 (k1 u2 u1 : ℕ) : ℕ :=
  let M : ℤ := ((2 ^ k1 : ℕ) : ℤ)
  let a : ℤ := 2 * (u2 : ℤ) - 1
  let inv : ℤ := oddModInvPow2Iter k1 a k1
  (((inv * (u1 : ℤ)) % M + M) % M).toNat

/-- Computable fixed-point Gaussian integer addition (`(a, b) + (c, d)`). -/
def gAdd (z w : ℤ × ℤ) : ℤ × ℤ := (z.1 + w.1, z.2 + w.2)

/-- Computable fixed-point Gaussian integer subtraction (`(a, b) - (c, d)`). -/
def gSub (z w : ℤ × ℤ) : ℤ × ℤ := (z.1 - w.1, z.2 - w.2)

/-- Computable fixed-point Gaussian integer negation (`-(a, b)`). -/
def gNeg (z : ℤ × ℤ) : ℤ × ℤ := (-z.1, -z.2)

/-- Computable fixed-point Gaussian integer conjugation (`(a, -b)`). -/
def gConj (z : ℤ × ℤ) : ℤ × ℤ := (z.1, -z.2)

/-- Computable fixed-point complex multiplication rounded to scale `2^q`:
`gMulScaled q z w = (divRoundPow2 (z.1 * w.1 - z.2 * w.2) q, divRoundPow2 (z.1 * w.2 + z.2 * w.1) q)`. -/
def gMulScaled (q : ℕ) (z w : ℤ × ℤ) : ℤ × ℤ :=
  (divRoundPow2 (z.1 * w.1 - z.2 * w.2) q,
   divRoundPow2 (z.1 * w.2 + z.2 * w.1) q)

/-- Computable fixed-point complex division rounded to scale `2^q`:
for `z, w` scaled by `2^q`, computes `round((z / w) * 2^q)`. -/
def gDivScaled (q : ℕ) (z w : ℤ × ℤ) : ℤ × ℤ :=
  let denom : ℤ := w.1 * w.1 + w.2 * w.2
  if denom = 0 then (0, 0)
  else
    let S : ℤ := ((2 ^ q : ℕ) : ℤ)
    let numRe : ℤ := (z.1 * w.1 + z.2 * w.2) * S
    let numIm : ℤ := (z.2 * w.1 - z.1 * w.2) * S
    ((numRe + denom / 2) / denom, (numIm + denom / 2) / denom)

/-- Computable single-step negacyclic shift in `ℤ[i][y]/(y^r + 1)` on an `Array (ℤ × ℤ)` of length `r`. -/
def computableNegacyclicStep (r : ℕ) (f : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  Array.ofFn (fun k : Fin r =>
    if k.val = 0 then gNeg (f.getD (r - 1) (0, 0))
    else f.getD (k.val - 1) (0, 0))

/-- Computable `s`-step negacyclic shift in `ℤ[i][y]/(y^r + 1)`. -/
def computableNegacyclicIter (r : ℕ) : ℕ → Array (ℤ × ℤ) → Array (ℤ × ℤ)
  | 0, f => f
  | s + 1, f => computableNegacyclicStep r (computableNegacyclicIter r s f)

/-- Single-pass $O(r)$ direct negacyclic shift (`computableNegacyclicDirect`, `[MS]` §3.5, Lemma 3.5):
reduces `sMod := s % (2 * r)` once before the loop and shifts the length-`r` array `f` in a single
$O(r)$ pass with zero per-step allocation and zero `/` or `%` inside the `Fin r` loop. -/
def computableNegacyclicDirect (r s : ℕ) (f : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  if r = 0 then #[]
  else
    let sMod := s % (2 * r)
    if sMod ≤ r then
      Array.ofFn (fun k : Fin r =>
        if k.val < sMod then gNeg (f.getD (k.val + r - sMod) (0, 0))
        else f.getD (k.val - sMod) (0, 0))
    else
      let s' := sMod - r
      Array.ofFn (fun k : Fin r =>
        if k.val < s' then f.getD (k.val + r - s') (0, 0)
        else gNeg (f.getD (k.val - s') (0, 0)))

/-- Computable multi-stage Radix-2 Synthetic FFT (`computableSyntheticFFTRadix2`) with per-stage
1-bit rounding `divRoundPow2 (... + ...) 1` at each butterfly stage (`100%` computable, zero `Real`/`Complex`),
materializing period-$2^k \times r$ arrays at stage $k$ and using the single-pass $O(r)$
`computableNegacyclicDirect` shift. -/
def computableSyntheticFFTRadix2 (V r : ℕ) :
    ℕ → ℕ → Array (Array (ℤ × ℤ)) → Array (Array (ℤ × ℤ))
  | 0, _, P =>
    Array.ofFn (fun _ : Fin 1 =>
      Array.ofFn (fun k2 : Fin r => (P.getD 0 #[]).getD k2.val (0, 0)))
  | k + 1, c1, P =>
    let Peven := Array.ofFn (fun j1 : Fin (2 ^ k) => P.getD (2 * j1.val) #[])
    let Podd := Array.ofFn (fun j1 : Fin (2 ^ k) => P.getD (2 * j1.val + 1) #[])
    let Y0 := computableSyntheticFFTRadix2 V r k (2 * c1) Peven
    let Y1 := computableSyntheticFFTRadix2 V r k (2 * c1) Podd
    Array.ofFn (fun v1 : Fin (2 ^ (k + 1)) =>
      let y0_row := Y0.getD (v1.val % 2 ^ k) #[]
      let y1_shifted := computableNegacyclicDirect r (2 * c1 * v1.val) (Y1.getD (v1.val % 2 ^ k) #[])
      Array.ofFn (fun k2 : Fin r =>
        let a := y0_row.getD k2.val (0, 0)
        let b := y1_shifted.getD k2.val (0, 0)
        (divRoundPow2 (a.1 + b.1) 1, divRoundPow2 (a.2 + b.2) 1)))

/-- **Period-$2^k \times r$ Array Dimensions of `computableSyntheticFFTRadix2`
(`computableSyntheticFFTRadix2_size`, `[MS]` §3.5, Lemma 3.5)**:
At stage `k`, `computableSyntheticFFTRadix2 V r k c1 P` produces an outer `Array` of size
`2 ^ k` whose rows each have size `r`. -/
@[simp]
theorem computableSyntheticFFTRadix2_size (V r k c1 : ℕ) (P : Array (Array (ℤ × ℤ))) :
    (computableSyntheticFFTRadix2 V r k c1 P).size = 2 ^ k ∧
    ∀ v1 : Fin (computableSyntheticFFTRadix2 V r k c1 P).size,
      ((computableSyntheticFFTRadix2 V r k c1 P)[v1]).size = r := by
  cases k with
  | zero =>
    refine ⟨by simp [computableSyntheticFFTRadix2], fun v1 => ?_⟩
    rw [Fin.getElem_fin]
    simp [computableSyntheticFFTRadix2]
  | succ k =>
    refine ⟨by simp [computableSyntheticFFTRadix2], fun v1 => ?_⟩
    rw [Fin.getElem_fin]
    simp [computableSyntheticFFTRadix2]

/-- Structural-recursion base-2 logarithm (`natLog2Fuel fuel n`) avoiding `WellFounded.fix`
during kernel symbolic reduction (`decide`). -/
def natLog2Fuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n ≥ 2 then natLog2Fuel fuel (n / 2) + 1 else 0

theorem natLog2Fuel_eq_log2 : ∀ fuel n : ℕ, n ≤ fuel → natLog2Fuel fuel n = Nat.log2 n
  | 0, n, hn => by
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | fuel + 1, n, hn => by
    unfold natLog2Fuel
    rw [Nat.log2_def]
    split_ifs with h2
    · rw [natLog2Fuel_eq_log2 fuel (n / 2) (by omega)]
    · rfl

@[simp]
theorem natLog2Fuel_self (n : ℕ) : natLog2Fuel n n = Nat.log2 n :=
  natLog2Fuel_eq_log2 n n le_rfl

/-- Structural-recursion integer sum over `0 .. n - 1` (avoiding `Finset.sum` / `Multiset`
quotients during kernel evaluation via `decide`). -/
def sumRangeInt (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumRangeInt f n + f n

@[simp]
theorem sumRangeInt_eq_sum (f : ℕ → ℤ) (n : ℕ) :
    sumRangeInt f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRangeInt, ih, Finset.sum_range_succ]

theorem sumRangeInt_ite_eq_sum_filter (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℤ) :
    sumRangeInt (fun i => if p i then f i else 0) n =
      ∑ i ∈ (Finset.range n).filter p, f i := by
  rw [sumRangeInt_eq_sum, Finset.sum_filter]

/-- Structural-recursion Gaussian-integer sum over `0 .. n - 1` (avoiding `Finset.sum` / `Multiset`
quotients during kernel evaluation via `decide`). -/
def sumRangePair (f : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => gAdd (sumRangePair f n) (f n)

@[simp]
theorem sumRangePair_eq_sum (f : ℕ → ℤ × ℤ) (n : ℕ) :
    sumRangePair f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRangePair, ih, Finset.sum_range_succ]
    rfl

/-- Kernel-evaluatable Kronecker bit-stride (`computableKroneckerBitStride f g = kroneckerBitStride f g`)
using `natLog2Fuel` instead of `WellFounded.fix`-based `Nat.log2`. -/
def computableKroneckerBitStride (f g : List ℤ) : ℕ :=
  let M := (f.length + g.length + 1) * (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1)
  natLog2Fuel M M + 2

@[simp]
theorem computableKroneckerBitStride_eq (f g : List ℤ) :
    computableKroneckerBitStride f g = kroneckerBitStride f g := by
  dsimp only [computableKroneckerBitStride, kroneckerBitStride]
  rw [natLog2Fuel_self]

/-- Kernel-evaluatable signed-Kronecker polynomial multiplier (`polyMulKroneckerSignedComputable q f g = polyMulKroneckerSigned q f g`)
using `((2 ^ (q - 1) : ℕ) : ℤ)` so `Nat.pow` reduces in one kernel step. -/
def polyMulKroneckerSignedComputable (q : ℕ) (f g : List ℤ) : List ℤ :=
  polyMulKroneckerSignedH (((2 ^ (q - 1) : ℕ) : ℤ)) f g

@[simp]
theorem polyMulKroneckerSignedComputable_eq (q : ℕ) (f g : List ℤ) :
    polyMulKroneckerSignedComputable q f g = polyMulKroneckerSigned q f g := by
  unfold polyMulKroneckerSignedComputable polyMulKroneckerSigned polyMulKroneckerSignedH
  simp [Nat.cast_pow]

/-- Exact integer 8th root of unity table `(cos(2π m / 8), sin(2π m / 8))` scaled by `S = 2^q`,
using `round(√2 / 2 * 2^q)` for the odd 8th roots (`100%` computable). -/
def eighthRootScaled (q : ℕ) (sqrtHalfScaled : ℤ) (m : ℕ) : ℤ × ℤ :=
  let S : ℤ := ((2 ^ q : ℕ) : ℤ)
  match m % 8 with
  | 0 => (S, 0)
  | 1 => (sqrtHalfScaled, sqrtHalfScaled)
  | 2 => (0, S)
  | 3 => (-sqrtHalfScaled, sqrtHalfScaled)
  | 4 => (-S, 0)
  | 5 => (-sqrtHalfScaled, -sqrtHalfScaled)
  | 6 => (0, -S)
  | _ => (sqrtHalfScaled, -sqrtHalfScaled)

/-- **Kernel-Verified Execution Test 1 (`computableSyntheticFFTRadix2_test`)**:
Verifies `computableSyntheticFFTRadix2` on a concrete `2 × 4` array in the Lean kernel via `decide`. -/
theorem computableSyntheticFFTRadix2_test :
    computableSyntheticFFTRadix2 2 4 1 2
      #[#[(100, 0), (40, 0), (0, 0), (0, 0)],
        #[(60, 0), (20, 0), (0, 0), (0, 0)]] =
      #[#[(80, 0), (30, 0), (0, 0), (0, 0)],
        #[(20, 0), (10, 0), (0, 0), (0, 0)]] := by
  decide

/-! ### Semantic Equivalence Between the Computable `ℤ × ℤ` Operators and Quantized `ℂ` Operators -/

/-- Exact equivalence between `⌊(A : ℝ) / (B : ℝ)⌋` and Euclidean integer division `A / B` for `0 < B`. -/
theorem floor_intCast_div_eq_ediv (A B : ℤ) (hB : 0 < B) :
    ⌊(A : ℝ) / (B : ℝ)⌋ = A / B := by
  rw [Int.floor_eq_iff]
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hdiv := Int.mul_ediv_add_emod A B
  have hcomm : B * (A / B) = (A / B) * B := mul_comm _ _
  have hmod0 : 0 ≤ A % B := Int.emod_nonneg A hB.ne'
  have hmod1 : A % B < B := Int.emod_lt_of_pos A hB
  constructor
  · rw [le_div_iff₀ hB_pos]
    exact_mod_cast (by linarith : (A / B) * B ≤ A)
  · rw [div_lt_iff₀ hB_pos]
    exact_mod_cast (by linarith : A < (A / B + 1) * B)

/-- **Exact Equivalence of `divRoundPow2` and `realQuantizeInt` (`divRoundPow2_eq_realQuantizeInt`)**:
For any precision parameter `p : ℕ` (bit scale `q = p + 2`) and unscaled integer product `m : ℤ`,
arithmetic right shift with rounding `divRoundPow2 m (p + 2)` equals
`realQuantizeInt p ((m : ℝ) / (2^(p + 2) * 2^(p + 2)))`. -/
theorem divRoundPow2_eq_realQuantizeInt (p : ℕ) (m : ℤ) :
    divRoundPow2 m (p + 2) =
      realQuantizeInt p ((m : ℝ) / ((2 : ℝ) ^ (p + 2) * (2 : ℝ) ^ (p + 2))) := by
  unfold divRoundPow2 realQuantizeInt
  rw [if_neg (by omega)]
  have hpow : (2 : ℝ) ^ (p + 2) = 2 * (2 : ℝ) ^ (p + 1) := by ring
  have hq1_pos : (0 : ℝ) < (2 : ℝ) ^ (p + 1) := by positivity
  have hsub : p + 2 - 1 = p + 1 := by omega
  rw [hsub]
  have hval : ((m : ℝ) / ((2 : ℝ) ^ (p + 2) * (2 : ℝ) ^ (p + 2))) * (2 : ℝ) ^ (p + 2) + 1 / 2 =
      (((m + ((2 ^ (p + 1) : ℕ) : ℤ) : ℤ) : ℝ) / (((2 ^ (p + 2) : ℕ) : ℤ) : ℝ)) := by
    push_cast
    rw [hpow]
    field_simp [hq1_pos.ne']
  rw [hval]
  exact (floor_intCast_div_eq_ediv (m + ((2 ^ (p + 1) : ℕ) : ℤ)) ((2 ^ (p + 2) : ℕ) : ℤ) (by positivity)).symm

/-- **Exact Equivalence of 1-Bit Butterfly Rounding (`divRoundPow2_one_eq_realQuantizeInt`)**:
For any precision `p : ℕ` (bit scale `p + 2`) and scaled integers `a, b : ℤ`, 1-bit rounded halving
`divRoundPow2 (a + b) 1` equals `realQuantizeInt p (((a / 2^(p + 2)) + (b / 2^(p + 2))) / 2)`. -/
theorem divRoundPow2_one_eq_realQuantizeInt (p : ℕ) (a b : ℤ) :
    divRoundPow2 (a + b) 1 =
      realQuantizeInt p (((a : ℝ) / (2 : ℝ) ^ (p + 2) + (b : ℝ) / (2 : ℝ) ^ (p + 2)) / 2) := by
  unfold divRoundPow2 realQuantizeInt
  rw [if_neg (by omega)]
  have hq_pos : (0 : ℝ) < (2 : ℝ) ^ (p + 2) := by positivity
  have hval : (((a : ℝ) / (2 : ℝ) ^ (p + 2) + (b : ℝ) / (2 : ℝ) ^ (p + 2)) / 2) * (2 : ℝ) ^ (p + 2) + 1 / 2 =
      (((a + b + ((2 ^ (1 - 1) : ℕ) : ℤ) : ℤ) : ℝ) / (((2 ^ 1 : ℕ) : ℤ) : ℝ)) := by
    push_cast
    field_simp [hq_pos.ne']
  rw [hval]
  exact (floor_intCast_div_eq_ediv (a + b + ((2 ^ (1 - 1) : ℕ) : ℤ)) ((2 ^ 1 : ℕ) : ℤ) (by decide)).symm

/-- Dequantization map interpreting a fixed-point Gaussian integer `z : ℤ × ℤ` at precision `p`
(scale `2^(p + 2)`, matching `realQuantize p` / `complexQuantize p`) in `ℂ`. -/
noncomputable def toScaledComplex (p : ℕ) (z : ℤ × ℤ) : ℂ :=
  ⟨(z.1 : ℝ) / (2 : ℝ) ^ (p + 2), (z.2 : ℝ) / (2 : ℝ) ^ (p + 2)⟩

@[simp]
theorem toScaledComplex_zero (p : ℕ) : toScaledComplex p (0, 0) = 0 := by
  apply Complex.ext <;> simp [toScaledComplex]

theorem toScaledComplex_gNeg (p : ℕ) (z : ℤ × ℤ) :
    toScaledComplex p (gNeg z) = -toScaledComplex p z := by
  apply Complex.ext <;> simp [toScaledComplex, gNeg, neg_div]

/-- **Exact Equivalence of `gMulScaled` and `complexQuantize` (`toScaledComplex_gMulScaled_eq_complexQuantize_mul`)**:
For any precision `p : ℕ` (scale `q = p + 2`) and fixed-point Gaussian integers `z, w : ℤ × ℤ`,
`toScaledComplex p (gMulScaled (p + 2) z w) = complexQuantize p (toScaledComplex p z * toScaledComplex p w)`. -/
theorem toScaledComplex_gMulScaled_eq_complexQuantize_mul (p : ℕ) (z w : ℤ × ℤ) :
    toScaledComplex p (gMulScaled (p + 2) z w) =
      complexQuantize p (toScaledComplex p z * toScaledComplex p w) := by
  have hre : (toScaledComplex p z * toScaledComplex p w).re =
      ((z.1 * w.1 - z.2 * w.2 : ℤ) : ℝ) / ((2 : ℝ) ^ (p + 2) * (2 : ℝ) ^ (p + 2)) := by
    simp only [Complex.mul_re, toScaledComplex]
    push_cast
    ring
  have him : (toScaledComplex p z * toScaledComplex p w).im =
      ((z.1 * w.2 + z.2 * w.1 : ℤ) : ℝ) / ((2 : ℝ) ^ (p + 2) * (2 : ℝ) ^ (p + 2)) := by
    simp only [Complex.mul_im, toScaledComplex]
    push_cast
    ring
  apply Complex.ext
  · change ((divRoundPow2 (z.1 * w.1 - z.2 * w.2) (p + 2) : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) =
      realQuantize p (toScaledComplex p z * toScaledComplex p w).re
    rw [hre, realQuantize_eq_realQuantizeInt_div, divRoundPow2_eq_realQuantizeInt p (z.1 * w.1 - z.2 * w.2)]
  · change ((divRoundPow2 (z.1 * w.2 + z.2 * w.1) (p + 2) : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) =
      realQuantize p (toScaledComplex p z * toScaledComplex p w).im
    rw [him, realQuantize_eq_realQuantizeInt_div, divRoundPow2_eq_realQuantizeInt p (z.1 * w.2 + z.2 * w.1)]

/-- **Exact Equivalence of 1-Bit Complex Butterfly Rounding (`toScaledComplex_divRoundPow2_one_eq_complexQuantize_avg`)**:
For any `p : ℕ` and `a, b : ℤ × ℤ`,
`toScaledComplex p (divRoundPow2 (a.1 + b.1) 1, divRoundPow2 (a.2 + b.2) 1) = complexQuantize p ((toScaledComplex p a + toScaledComplex p b) / 2)`. -/
theorem toScaledComplex_divRoundPow2_one_eq_complexQuantize_avg (p : ℕ) (a b : ℤ × ℤ) :
    toScaledComplex p (divRoundPow2 (a.1 + b.1) 1, divRoundPow2 (a.2 + b.2) 1) =
      complexQuantize p ((toScaledComplex p a + toScaledComplex p b) / 2) := by
  have hre : ((toScaledComplex p a + toScaledComplex p b) / 2).re =
      ((a.1 : ℝ) / (2 : ℝ) ^ (p + 2) + (b.1 : ℝ) / (2 : ℝ) ^ (p + 2)) / 2 := by
    simp [toScaledComplex]
  have him : ((toScaledComplex p a + toScaledComplex p b) / 2).im =
      ((a.2 : ℝ) / (2 : ℝ) ^ (p + 2) + (b.2 : ℝ) / (2 : ℝ) ^ (p + 2)) / 2 := by
    simp [toScaledComplex]
  apply Complex.ext
  · change ((divRoundPow2 (a.1 + b.1) 1 : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) =
      realQuantize p ((toScaledComplex p a + toScaledComplex p b) / 2).re
    rw [hre, realQuantize_eq_realQuantizeInt_div, divRoundPow2_one_eq_realQuantizeInt p a.1 b.1]
  · change ((divRoundPow2 (a.2 + b.2) 1 : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) =
      realQuantize p ((toScaledComplex p a + toScaledComplex p b) / 2).im
    rw [him, realQuantize_eq_realQuantizeInt_div, divRoundPow2_one_eq_realQuantizeInt p a.2 b.2]

/-- Single-step negacyclic shift equivalence between `computableNegacyclicStep` and `negacyclicShiftStep`. -/
theorem toScaledComplex_computableNegacyclicStep_eq
    (p r : ℕ) (f : Array (ℤ × ℤ)) (k2 : ℕ) (hk2 : k2 < r) :
    toScaledComplex p ((computableNegacyclicStep r f).getD k2 (0, 0)) =
      negacyclicShiftStep r (fun m => toScaledComplex p (f.getD m (0, 0))) k2 := by
  unfold computableNegacyclicStep negacyclicShiftStep
  rw [array_getD_ofFn_of_lt r _ (0, 0) k2 hk2]
  dsimp only
  split_ifs with h0
  · exact toScaledComplex_gNeg p (f.getD (r - 1) (0, 0))
  · rfl

/-- Iterated negacyclic shift equivalence between `computableNegacyclicIter` and `negacyclicShiftIter`. -/
theorem toScaledComplex_computableNegacyclicIter_eq
    (p r s : ℕ) (f : Array (ℤ × ℤ)) (k2 : ℕ) (hk2 : k2 < r) :
    toScaledComplex p ((computableNegacyclicIter r s f).getD k2 (0, 0)) =
      negacyclicShiftIter r s (fun m => toScaledComplex p (f.getD m (0, 0))) k2 := by
  have hr : 0 < r := by omega
  induction s generalizing k2 with
  | zero => rfl
  | succ s ih =>
    simp only [computableNegacyclicIter, negacyclicShiftIter, Function.iterate_succ_apply']
    rw [toScaledComplex_computableNegacyclicStep_eq p r (computableNegacyclicIter r s f) k2 hk2]
    exact negacyclicShiftStep_congr_lt r hr
      (fun m => toScaledComplex p ((computableNegacyclicIter r s f).getD m (0, 0)))
      ((negacyclicShiftStep r)^[s] (fun m => toScaledComplex p (f.getD m (0, 0))))
      (fun m hm => ih m hm) k2 hk2

/-- If two polynomial arrays `P, Q : ℕ → ℕ → ℂ` agree on all `(j1, k2)` with `j1 < 2 ^ m` and `k2 < r`,
then `syntheticFFTRadix2Quantized p r m c1 P` and `syntheticFFTRadix2Quantized p r m c1 Q` agree on
all `(v1, k2)` with `k2 < r`. -/
theorem syntheticFFTRadix2Quantized_congr_lt
    (p r m c1 : ℕ) (P Q : ℕ → ℕ → ℂ)
    (hPQ : ∀ j1 < 2 ^ m, ∀ k2 < r, P j1 k2 = Q j1 k2)
    (v1 k2 : ℕ) (hk2 : k2 < r) :
    syntheticFFTRadix2Quantized p r m c1 P v1 k2 =
      syntheticFFTRadix2Quantized p r m c1 Q v1 k2 := by
  have hr : 0 < r := by omega
  induction m generalizing c1 P Q k2 with
  | zero =>
    dsimp only [syntheticFFTRadix2Quantized]
    exact hPQ 0 (by simp) k2 hk2
  | succ m ih =>
    dsimp only [syntheticFFTRadix2Quantized]
    have hY0 := ih (2 * c1) (fun j1 => P (2 * j1)) (fun j1 => Q (2 * j1))
      (fun j1 hj1 m' hm' => hPQ (2 * j1) (by rw [pow_succ']; omega) m' hm') k2 hk2
    have hY1_shift := negacyclicShiftIter_congr_lt r (2 * c1 * v1) hr
      (syntheticFFTRadix2Quantized p r m (2 * c1) (fun j1 => P (2 * j1 + 1)) v1)
      (syntheticFFTRadix2Quantized p r m (2 * c1) (fun j1 => Q (2 * j1 + 1)) v1)
      (fun m' hm' => ih (2 * c1) (fun j1 => P (2 * j1 + 1)) (fun j1 => Q (2 * j1 + 1))
        (fun j1 hj1 k' hk' => hPQ (2 * j1 + 1) (by rw [pow_succ']; omega) k' hk') m' hm')
      k2 hk2
    rw [hY0, hY1_shift]

/-- Exact equivalence between the single-pass $O(r)$ `computableNegacyclicDirect` and `negacyclicShiftIter`. -/
theorem toScaledComplex_computableNegacyclicDirect_eq
    (p r s : ℕ) (f : Array (ℤ × ℤ)) (k2 : ℕ) (hk2 : k2 < r) :
    toScaledComplex p ((computableNegacyclicDirect r s f).getD k2 (0, 0)) =
      negacyclicShiftIter r s (fun m => toScaledComplex p (f.getD m (0, 0))) k2 := by
  have hr : 0 < r := by omega
  have hr0 : r ≠ 0 := by omega
  unfold computableNegacyclicDirect
  rw [if_neg hr0]
  dsimp only
  set sMod := s % (2 * r)
  have hs_decomp : s = sMod + 2 * r * (s / (2 * r)) := by
    dsimp [sMod]
    linarith [Nat.div_add_mod s (2 * r)]
  have hsMod_lt : sMod < 2 * r := Nat.mod_lt s (by omega)
  conv_rhs =>
    rw [hs_decomp, negacyclicShiftIter_add_two_mul_r_mul r sMod (s / (2 * r)) _ k2 hk2]
  split_ifs with hle
  · rw [array_getD_ofFn_of_lt r _ (0, 0) k2 hk2]
    dsimp only
    rw [negacyclicShiftIter_closed_form_of_le r sMod hle _ k2 hk2]
    split_ifs with hlt
    · exact toScaledComplex_gNeg p (f.getD (k2 + r - sMod) (0, 0))
    · rfl
  · rw [array_getD_ofFn_of_lt r _ (0, 0) k2 hk2]
    dsimp only
    have hs'_eq : sMod = r + (sMod - r) := by omega
    have hs'_le : sMod - r ≤ r := by omega
    conv_rhs =>
      rw [hs'_eq,
          negacyclicShiftIter_add_r r (sMod - r) _ k2 hk2,
          negacyclicShiftIter_closed_form_of_le r (sMod - r) hs'_le _ k2 hk2]
    split_ifs with hlt
    · rw [neg_neg]
    · exact toScaledComplex_gNeg p (f.getD (k2 - (sMod - r)) (0, 0))

/-- **Exact Semantic Equivalence of `computableSyntheticFFTRadix2` and `syntheticFFTRadix2Quantized`**:
For every `p, m, V, r, c1 : ℕ` (`2 ^ m * c1 = r`) and 2D array `P : Array (Array (ℤ × ℤ))`, dequantizing the pure-integer
output of `computableSyntheticFFTRadix2 V r m c1 P` at `(v1, k2)` with `v1 < 2 ^ m` and `k2 < r`
equals `syntheticFFTRadix2Quantized p r m c1` applied to the dequantized input `P`. -/
theorem toScaledComplex_computableSyntheticFFTRadix2_eq
    (p V r m c1 : ℕ) (hc1 : 2 ^ m * c1 = r)
    (P : Array (Array (ℤ × ℤ))) (v1 k2 : ℕ) (hv1 : v1 < 2 ^ m) (hk2 : k2 < r) :
    toScaledComplex p (((computableSyntheticFFTRadix2 V r m c1 P).getD v1 #[]).getD k2 (0, 0)) =
      syntheticFFTRadix2Quantized p r m c1
        (fun j1 k2 => toScaledComplex p ((P.getD j1 #[]).getD k2 (0, 0))) v1 k2 := by
  have hr : 0 < r := by omega
  induction m generalizing c1 P v1 k2 with
  | zero =>
    dsimp only [computableSyntheticFFTRadix2, syntheticFFTRadix2Quantized]
    have hv0 : v1 < 1 := by simpa using hv1
    rw [array_getD_ofFn_of_lt 1 _ #[] v1 hv0, array_getD_ofFn_of_lt r _ (0, 0) k2 hk2]
  | succ m ih =>
    dsimp only [computableSyntheticFFTRadix2, syntheticFFTRadix2Quantized]
    set Peven := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val) #[])
    set Podd := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val + 1) #[])
    set Y0 := computableSyntheticFFTRadix2 V r m (2 * c1) Peven
    set Y1 := computableSyntheticFFTRadix2 V r m (2 * c1) Podd
    rw [array_getD_ofFn_of_lt (2 ^ (m + 1)) _ #[] v1 hv1, array_getD_ofFn_of_lt r _ (0, 0) k2 hk2]
    dsimp only
    rw [toScaledComplex_divRoundPow2_one_eq_complexQuantize_avg]
    have hc1' : 2 ^ m * (2 * c1) = r := by
      calc 2 ^ m * (2 * c1) = 2 ^ (m + 1) * c1 := by rw [pow_succ]; ring
        _ = r := hc1
    have hv1_mod : v1 % 2 ^ m < 2 ^ m := Nat.mod_lt v1 (pow_pos zero_lt_two m)
    have hY0 : toScaledComplex p ((Y0.getD (v1 % 2 ^ m) #[]).getD k2 (0, 0)) =
        syntheticFFTRadix2Quantized p r m (2 * c1)
          (fun j1 k2 => toScaledComplex p ((P.getD (2 * j1) #[]).getD k2 (0, 0))) v1 k2 := by
      rw [ih (2 * c1) hc1' Peven (v1 % 2 ^ m) k2 hv1_mod hk2,
          syntheticFFTRadix2Quantized_mod_two_pow p r m (2 * c1) hc1' _ v1 k2 hk2]
      exact syntheticFFTRadix2Quantized_congr_lt p r m (2 * c1) _ _
        (fun j1 hj1 m' _ => by
          dsimp only [Peven]
          rw [array_getD_ofFn_of_lt (2 ^ m) _ #[] j1 hj1]) v1 k2 hk2
    have hY1_shift :
        toScaledComplex p ((computableNegacyclicDirect r (2 * c1 * v1) (Y1.getD (v1 % 2 ^ m) #[])).getD k2 (0, 0)) =
        negacyclicShiftIter r (2 * c1 * v1)
          (syntheticFFTRadix2Quantized p r m (2 * c1)
            (fun j1 k2 => toScaledComplex p ((P.getD (2 * j1 + 1) #[]).getD k2 (0, 0))) v1) k2 := by
      rw [toScaledComplex_computableNegacyclicDirect_eq p r (2 * c1 * v1) (Y1.getD (v1 % 2 ^ m) #[]) k2 hk2]
      exact negacyclicShiftIter_congr_lt r (2 * c1 * v1) hr _ _
        (fun m' hm' => by
          rw [ih (2 * c1) hc1' Podd (v1 % 2 ^ m) m' hv1_mod hm',
              syntheticFFTRadix2Quantized_mod_two_pow p r m (2 * c1) hc1' _ v1 m' hm']
          exact syntheticFFTRadix2Quantized_congr_lt p r m (2 * c1) _ _
            (fun j1 hj1 k'' _ => by
              dsimp only [Podd]
              rw [array_getD_ofFn_of_lt (2 ^ m) _ #[] j1 hj1]) v1 m' hm')
        k2 hk2
    rw [hY0, hY1_shift]

/-- **Hensel-Lifting Modular Inverse Correctness (`oddModInvPow2Iter_dvd`)**:
For any odd integer `a` (`2 ∣ a - 1`) and any `m, s : ℕ`,
`2^(min (s + 1) m) ∣ (a * oddModInvPow2Iter m a s - 1)`. -/
theorem oddModInvPow2Iter_dvd (m : ℕ) (a : ℤ) (ha : (2 : ℤ) ∣ a - 1) :
    ∀ s : ℕ, ((2 ^ min (s + 1) m : ℕ) : ℤ) ∣ (a * oddModInvPow2Iter m a s - 1)
  | 0 => by
    simp only [oddModInvPow2Iter, mul_one, Nat.zero_add]
    have hle : min 1 m ≤ 1 := Nat.min_le_left 1 m
    have hdvd2 : ((2 ^ min 1 m : ℕ) : ℤ) ∣ (2 : ℤ) := by
      interval_cases min 1 m <;> decide
    exact dvd_trans hdvd2 ha
  | s + 1 => by
    simp only [oddModInvPow2Iter]
    set inv := oddModInvPow2Iter m a s
    have ih := oddModInvPow2Iter_dvd m a ha s
    have hsq_dvd : ((2 ^ (2 * min (s + 1) m) : ℕ) : ℤ) ∣ (a * inv - 1) * (a * inv - 1) := by
      have hmul := mul_dvd_mul ih ih
      push_cast at hmul ⊢
      rwa [← pow_add, ← two_mul] at hmul
    have hmin_le : min (s + 1 + 1) m ≤ 2 * min (s + 1) m := by omega
    have hpow_dvd : ((2 ^ min (s + 1 + 1) m : ℕ) : ℤ) ∣ ((2 ^ (2 * min (s + 1) m) : ℕ) : ℤ) := by
      push_cast
      exact pow_dvd_pow 2 hmin_le
    have hstep_dvd : ((2 ^ min (s + 1 + 1) m : ℕ) : ℤ) ∣ (a * (inv * (2 - a * inv)) - 1) := by
      have hid : a * (inv * (2 - a * inv)) - 1 = -((a * inv - 1) * (a * inv - 1)) := by ring
      rw [hid, dvd_neg]
      exact dvd_trans hpow_dvd hsq_dvd
    have hm_dvd : ((2 ^ min (s + 1 + 1) m : ℕ) : ℤ) ∣ ((2 ^ m : ℕ) : ℤ) := by
      push_cast
      exact pow_dvd_pow 2 (Nat.min_le_right _ _)
    have hmod_eq : (inv * (2 - a * inv)) % ((2 ^ m : ℕ) : ℤ) =
        inv * (2 - a * inv) - ((2 ^ m : ℕ) : ℤ) * ((inv * (2 - a * inv)) / ((2 ^ m : ℕ) : ℤ)) := by
      linarith [Int.mul_ediv_add_emod (inv * (2 - a * inv)) ((2 ^ m : ℕ) : ℤ)]
    rw [hmod_eq]
    have hsplit : a * (inv * (2 - a * inv) - ((2 ^ m : ℕ) : ℤ) * ((inv * (2 - a * inv)) / ((2 ^ m : ℕ) : ℤ))) - 1 =
        (a * (inv * (2 - a * inv)) - 1) -
          ((2 ^ m : ℕ) : ℤ) * (a * ((inv * (2 - a * inv)) / ((2 ^ m : ℕ) : ℤ))) := by ring
    rw [hsplit]
    exact dvd_sub hstep_dvd (dvd_mul_of_dvd_left hm_dvd _)

/-- **Exact Congruence & Equivalence of `computableOddStrideInvPow2` and `oddStrideInvPow2`**:
For every `k1, u2, u1 : ℕ`, the Hensel-lifting `computableOddStrideInvPow2 k1 u2 u1` equals the
`ZMod`-based `oddStrideInvPow2 k1 u2 u1`. -/
theorem computableOddStrideInvPow2_eq_oddStrideInvPow2 (k1 u2 u1 : ℕ) :
    computableOddStrideInvPow2 k1 u2 u1 = oddStrideInvPow2 k1 u2 u1 := by
  unfold computableOddStrideInvPow2
  dsimp only
  set a : ℤ := 2 * (u2 : ℤ) - 1
  set inv : ℤ := oddModInvPow2Iter k1 a k1
  set r : ℤ := ((inv * (u1 : ℤ)) % ((2 ^ k1 : ℕ) : ℤ) + ((2 ^ k1 : ℕ) : ℤ)) % ((2 ^ k1 : ℕ) : ℤ)
  have hM_pos : (0 : ℤ) < ((2 ^ k1 : ℕ) : ℤ) := by positivity
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg _ hM_pos.ne'
  have hr_lt : r < ((2 ^ k1 : ℕ) : ℤ) := Int.emod_lt_of_pos _ hM_pos
  have ha_odd : (2 : ℤ) ∣ a - 1 := ⟨(u2 : ℤ) - 1, by dsimp [a]; ring⟩
  have hdvd_inv : ((2 ^ k1 : ℕ) : ℤ) ∣ (a * inv - 1) := by
    have h := oddModInvPow2Iter_dvd k1 a ha_odd k1
    have hmin : min (k1 + 1) k1 = k1 := Nat.min_eq_right (by omega)
    rwa [hmin] at h
  have hdvd_r : ((2 ^ k1 : ℕ) : ℤ) ∣ (a * r - (u1 : ℤ)) := by
    have hd1 := Int.mul_ediv_add_emod (inv * (u1 : ℤ)) ((2 ^ k1 : ℕ) : ℤ)
    have hd2 := Int.mul_ediv_add_emod ((inv * (u1 : ℤ)) % ((2 ^ k1 : ℕ) : ℤ) + ((2 ^ k1 : ℕ) : ℤ)) ((2 ^ k1 : ℕ) : ℤ)
    have hdvd_diff : ((2 ^ k1 : ℕ) : ℤ) ∣ (r - inv * (u1 : ℤ)) := by
      refine ⟨1 - (inv * (u1 : ℤ)) / ((2 ^ k1 : ℕ) : ℤ) -
        (((inv * (u1 : ℤ)) % ((2 ^ k1 : ℕ) : ℤ) + ((2 ^ k1 : ℕ) : ℤ)) / ((2 ^ k1 : ℕ) : ℤ)), ?_⟩
      change r - inv * (u1 : ℤ) = _
      linarith
    have hid : a * r - (u1 : ℤ) = a * (r - inv * (u1 : ℤ)) + (a * inv - 1) * (u1 : ℤ) := by ring
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_right hdvd_diff a) (dvd_mul_of_dvd_left hdvd_inv (u1 : ℤ))
  rcases oddStrideInvPow2_congr k1 u2 u1 with ⟨q2, hq2⟩
  have hdvd_v2 : ((2 ^ k1 : ℕ) : ℤ) ∣ (a * (oddStrideInvPow2 k1 u2 u1 : ℤ) - (u1 : ℤ)) := ⟨q2, by linarith⟩
  have hr_toNat : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr_nonneg
  have hdvd_sub : ((2 ^ k1 : ℕ) : ℤ) ∣ a * ((r.toNat : ℤ) - (oddStrideInvPow2 k1 u2 u1 : ℤ)) := by
    rw [hr_toNat]
    have hid : a * (r - (oddStrideInvPow2 k1 u2 u1 : ℤ)) =
        (a * r - (u1 : ℤ)) - (a * (oddStrideInvPow2 k1 u2 u1 : ℤ) - (u1 : ℤ)) := by ring
    rw [hid]
    exact dvd_sub hdvd_r hdvd_v2
  have hcop : IsCoprime a ((2 ^ k1 : ℕ) : ℤ) := by
    have hcop2 : IsCoprime a 2 := ⟨1, -(u2 : ℤ) + 1, by dsimp [a]; ring⟩
    have hM_eq : ((2 ^ k1 : ℕ) : ℤ) = (2 : ℤ) ^ k1 := by push_cast; rfl
    rw [hM_eq]
    exact hcop2.pow_right
  have hdvd_diff_v : ((2 ^ k1 : ℕ) : ℤ) ∣ ((r.toNat : ℤ) - (oddStrideInvPow2 k1 u2 u1 : ℤ)) :=
    hcop.symm.dvd_of_dvd_mul_left hdvd_sub
  have hv2_lt : oddStrideInvPow2 k1 u2 u1 < 2 ^ k1 := by
    haveI : NeZero (2 ^ k1) := ⟨pow_ne_zero k1 (by decide)⟩
    unfold oddStrideInvPow2
    cases u2 <;> exact ZMod.val_lt _
  have hv2_lt_int : (oddStrideInvPow2 k1 u2 u1 : ℤ) < ((2 ^ k1 : ℕ) : ℤ) := by exact_mod_cast hv2_lt
  rcases hdvd_diff_v with ⟨k, hk⟩
  have hk0 : k = 0 := by
    by_contra hk_ne
    have habs : ((2 ^ k1 : ℕ) : ℤ) ≤ |((2 ^ k1 : ℕ) : ℤ) * k| := by
      rw [abs_mul, abs_of_pos hM_pos]
      have : 1 ≤ |k| := Int.one_le_abs hk_ne
      nlinarith
    have hlt : |(r.toNat : ℤ) - (oddStrideInvPow2 k1 u2 u1 : ℤ)| < ((2 ^ k1 : ℕ) : ℤ) := by
      rw [abs_lt]
      constructor <;> linarith
    rw [hk] at hlt
    linarith
  have heq : (r.toNat : ℤ) = (oddStrideInvPow2 k1 u2 u1 : ℤ) := by
    rw [hk0, mul_zero] at hk
    linarith
  exact_mod_cast heq

/-! ### Exact End-to-End Equivalence of the Computable `ℤ × ℤ` Pipeline and `sincGaussianFastDFTQuantized` / `quantizedFastDFTMultiply` -/

/-- Exact nearest-integer rational rounding `⌊(num : ℝ) / (den : ℝ) + 1 / 2⌋` for any integer
numerator `num : ℤ` and non-negative integer denominator `den : ℤ` (`0 ≤ den`, returning `0` when
`den = 0` to match Lean's `/ 0 = 0`), computed in pure integer arithmetic as
`(2 * num + den) / (2 * den)`. -/
def divRoundRatInt (num den : ℤ) : ℤ :=
  if 0 < den then (2 * num + den) / (2 * den) else 0

/-- For any `0 < den`, `divRoundRatInt num den = ⌊(num : ℝ) / (den : ℝ) + 1 / 2⌋`. -/
theorem divRoundRatInt_eq_floor (num den : ℤ) (hden : 0 < den) :
    divRoundRatInt num den = ⌊(num : ℝ) / (den : ℝ) + 1 / 2⌋ := by
  unfold divRoundRatInt
  rw [if_pos hden]
  have hden_pos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hval : (num : ℝ) / (den : ℝ) + 1 / 2 =
      (((2 * num + den : ℤ) : ℝ) / ((2 * den : ℤ) : ℝ)) := by
    push_cast
    field_simp [hden_pos.ne']
  rw [hval]
  exact (floor_intCast_div_eq_ediv (2 * num + den) (2 * den) (by omega)).symm

@[simp]
theorem realQuantizeInt_zero (p : ℕ) : realQuantizeInt p 0 = 0 := by
  unfold realQuantizeInt
  rw [zero_mul, zero_add]
  rw [Int.floor_eq_iff]
  norm_num

/-- For any `p : ℕ`, `num : ℤ`, and `0 ≤ den`, `divRoundRatInt num den` equals
`realQuantizeInt p ((num : ℝ) / ((den : ℝ) * 2^(p + 2)))`. -/
theorem divRoundRatInt_eq_realQuantizeInt_nonneg (p : ℕ) (num den : ℤ) (hden : 0 ≤ den) :
    divRoundRatInt num den =
      realQuantizeInt p ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ (p + 2))) := by
  rcases eq_or_lt_of_le hden with rfl | hpos
  · simp [divRoundRatInt]
  · rw [divRoundRatInt_eq_floor num den hpos]
    unfold realQuantizeInt
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (p + 2) := by positivity
    have hden_r : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hpos
    have hsimp : ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ (p + 2))) * (2 : ℝ) ^ (p + 2) =
        (num : ℝ) / (den : ℝ) := by
      field_simp [hpow.ne', hden_r.ne']
    rw [hsimp]

/-- Unscaled Gaussian integer multiplication `(a + b i)(c + d i) = (ac - bd, ad + bc)`. -/
def gMulUnit (z w : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Pure-integer complex rational rounding `(divRoundRatInt numRe den, divRoundRatInt numIm den)`. -/
def gQuantizeRat (numRe numIm den : ℤ) : ℤ × ℤ :=
  (divRoundRatInt numRe den, divRoundRatInt numIm den)

/-- **Master Rational Quantization Bridge (`toScaledComplex_gQuantizeRat_eq_complexQuantize`)**:
Whenever `z : ℂ` has real and imaginary parts `numRe / (den * 2^(p + 2))` and
`numIm / (den * 2^(p + 2))` with `0 ≤ den`, dequantizing `gQuantizeRat numRe numIm den` at
precision `p` equals `complexQuantize p z`. -/
theorem toScaledComplex_gQuantizeRat_eq_complexQuantize
    (p : ℕ) (numRe numIm den : ℤ) (hden : 0 ≤ den) (z : ℂ)
    (hre : z.re = (numRe : ℝ) / ((den : ℝ) * (2 : ℝ) ^ (p + 2)))
    (him : z.im = (numIm : ℝ) / ((den : ℝ) * (2 : ℝ) ^ (p + 2))) :
    toScaledComplex p (gQuantizeRat numRe numIm den) = complexQuantize p z := by
  apply Complex.ext
  · change ((divRoundRatInt numRe den : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) = realQuantize p z.re
    rw [hre, realQuantize_eq_realQuantizeInt_div,
        divRoundRatInt_eq_realQuantizeInt_nonneg p numRe den hden]
  · change ((divRoundRatInt numIm den : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) = realQuantize p z.im
    rw [him, realQuantize_eq_realQuantizeInt_div,
        divRoundRatInt_eq_realQuantizeInt_nonneg p numIm den hden]

theorem toScaledComplex_gAdd (p : ℕ) (z w : ℤ × ℤ) :
    toScaledComplex p (gAdd z w) = toScaledComplex p z + toScaledComplex p w := by
  apply Complex.ext <;> simp [toScaledComplex, gAdd, add_div]

theorem toScaledComplex_gSub (p : ℕ) (z w : ℤ × ℤ) :
    toScaledComplex p (gSub z w) = toScaledComplex p z - toScaledComplex p w := by
  apply Complex.ext <;> simp [toScaledComplex, gSub, sub_div]

theorem toScaledComplex_gConj (p : ℕ) (z : ℤ × ℤ) :
    toScaledComplex p (gConj z) = star (toScaledComplex p z) := by
  apply Complex.ext <;> simp [toScaledComplex, gConj, neg_div]

/-- Pure-integer precision rescaling from `p_in` (`2^(p_in + 2)`) to `p_out` (`2^(p_out + 2)`),
exact integer counterpart of `complexQuantize p_out (toScaledComplex p_in z)`. -/
def gRescale (p_in p_out : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  let S_out : ℤ := ((2 ^ (p_out + 2) : ℕ) : ℤ)
  let S_in : ℤ := ((2 ^ (p_in + 2) : ℕ) : ℤ)
  gQuantizeRat (z.1 * S_out) (z.2 * S_out) S_in

theorem toScaledComplex_gRescale_eq (p_in p_out : ℕ) (z : ℤ × ℤ) :
    toScaledComplex p_out (gRescale p_in p_out z) =
      complexQuantize p_out (toScaledComplex p_in z) := by
  unfold gRescale
  dsimp only
  have hpos : (0 : ℤ) ≤ ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (p_out + 2) := by positivity
  refine toScaledComplex_gQuantizeRat_eq_complexQuantize p_out
    (z.1 * ((2 ^ (p_out + 2) : ℕ) : ℤ))
    (z.2 * ((2 ^ (p_out + 2) : ℕ) : ℤ))
    ((2 ^ (p_in + 2) : ℕ) : ℤ) hpos (toScaledComplex p_in z) ?_ ?_
  · dsimp [toScaledComplex]
    push_cast
    field_simp [hpow.ne']
  · dsimp [toScaledComplex]
    push_cast
    field_simp [hpow.ne']

/-- Pure-integer counterpart of `quantizeInt q ((toScaledComplex p_in z).re)` (or `.im`). -/
def gQuantizeCoordToScale (p_in q : ℕ) (v : ℤ) : ℤ :=
  divRoundRatInt (v * ((2 ^ q : ℕ) : ℤ)) ((2 ^ (p_in + 2) : ℕ) : ℤ)

theorem gQuantizeCoordToScale_eq_quantizeInt (p_in q : ℕ) (v : ℤ) :
    gQuantizeCoordToScale p_in q v =
      quantizeInt q ((v : ℝ) / (2 : ℝ) ^ (p_in + 2)) := by
  unfold gQuantizeCoordToScale quantizeInt
  have hden : (0 : ℤ) < ((2 ^ (p_in + 2) : ℕ) : ℤ) := by positivity
  rw [divRoundRatInt_eq_floor _ _ hden]
  congr 1
  push_cast
  ring

/-- Fast-reducing computable bit-cost proxy `w * lw * (natLog2Fuel lw lw + 1)` (`lw = natLog2Fuel w w + 1`)
matching `mulBitCost w` without `WellFounded.fix`. -/
def computableMulBitCost (w : ℕ) : ℕ :=
  let lw := natLog2Fuel w w + 1
  w * lw * (natLog2Fuel lw lw + 1)

@[simp]
theorem computableMulBitCost_eq (w : ℕ) : computableMulBitCost w = mulBitCost w := by
  unfold computableMulBitCost mulBitCost
  dsimp only
  rw [natLog2Fuel_self, natLog2Fuel_self]

/-- Contiguous-row real block extractor (`computableSpreadRowBlockReContiguous`, `[MS]` §6.2):
reads contiguous elements `read1D xRow (b * W_eff + a)` from row `j1` of the transposed input tape,
eliminating stride-`t1` random access (`j1 + t1 * i`). -/
def computableSpreadRowBlockReContiguous
    (p_in q m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun a =>
    if b * W_eff + a < r then
      gQuantizeCoordToScale p_in q (read1D xRow (b * W_eff + a)).1
    else 0)

/-- Contiguous-row imaginary block extractor (`computableSpreadRowBlockImContiguous`, `[MS]` §6.2):
reads contiguous elements `read1D xRow (b * W_eff + a)` from row `j1` of the transposed input tape,
eliminating stride-`t1` random access (`j1 + t1 * i`). -/
def computableSpreadRowBlockImContiguous
    (p_in q m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun a =>
    if b * W_eff + a < r then
      gQuantizeCoordToScale p_in q (read1D xRow (b * W_eff + a)).2
    else 0)

theorem computableSpreadRowBlockReContiguous_eq
    (p_in q m1 t1 r : ℕ) (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 : ℕ)
    (hx : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) (b : ℕ) :
    computableSpreadRowBlockReContiguous p_in q m1 r xRow b =
      kroneckerSpreadRowBlockRe q m1 t1 r x j1 b := by
  unfold computableSpreadRowBlockReContiguous kroneckerSpreadRowBlockRe
  dsimp only
  refine List.map_congr_left fun a _ => ?_
  split_ifs with hlt
  · rw [hx (b * effectiveFilterWidth m1 r + a) hlt]
    exact gQuantizeCoordToScale_eq_quantizeInt p_in q _
  · rfl

theorem computableSpreadRowBlockImContiguous_eq
    (p_in q m1 t1 r : ℕ) (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 : ℕ)
    (hx : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) (b : ℕ) :
    computableSpreadRowBlockImContiguous p_in q m1 r xRow b =
      kroneckerSpreadRowBlockIm q m1 t1 r x j1 b := by
  unfold computableSpreadRowBlockImContiguous kroneckerSpreadRowBlockIm
  dsimp only
  refine List.map_congr_left fun a _ => ?_
  split_ifs with hlt
  · rw [hx (b * effectiveFilterWidth m1 r + a) hlt]
    exact gQuantizeCoordToScale_eq_quantizeInt p_in q _
  · rfl

/-- Single $O(1)$ in-place bucket update on a 1D integer array `acc : Array ℤ`:
adds `v` to `acc[idx]` when `idx < acc.size`. -/
def accumBucketInt (acc : Array ℤ) (idx : ℕ) (v : ℤ) : Array ℤ :=
  if h : idx < acc.size then acc.set idx (acc[idx] + v) else acc

@[simp]
theorem size_accumBucketInt (acc : Array ℤ) (idx : ℕ) (v : ℤ) :
    (accumBucketInt acc idx v).size = acc.size := by
  unfold accumBucketInt
  split_ifs with h <;> simp

theorem read1D_accumBucketInt_of_lt (acc : Array ℤ) (idx : ℕ) (v : ℤ) (k2 : ℕ) (hk2 : k2 < acc.size) :
    read1D (accumBucketInt acc idx v) k2 = read1D acc k2 + (if idx = k2 then v else 0) := by
  unfold accumBucketInt
  by_cases h : idx < acc.size
  · rw [dif_pos h]
    unfold read1D
    have hk2' : k2 < (acc.set idx (acc[idx] + v)).size := by simp [hk2]
    rw [dif_pos hk2', dif_pos hk2, Array.getElem_set]
    by_cases heq : idx = k2
    · subst heq
      simp
    · simp [heq]
  · rw [dif_neg h]
    have hne : idx ≠ k2 := by omega
    rw [if_neg hne, add_zero]

/-- Single-pass inner loop over `i ∈ 0 .. n - 1` accumulating `valFn i` into bucket `idxFn i`
via $O(1)$ `accumBucketInt` updates. -/
def accumBucketsRange (idxFn : ℕ → ℕ) (valFn : ℕ → ℤ) : ℕ → Array ℤ → Array ℤ
  | 0, acc => acc
  | n + 1, acc =>
    let acc' := accumBucketsRange idxFn valFn n acc
    accumBucketInt acc' (idxFn n) (valFn n)

@[simp]
theorem size_accumBucketsRange (idxFn : ℕ → ℕ) (valFn : ℕ → ℤ) (n : ℕ) (acc : Array ℤ) :
    (accumBucketsRange idxFn valFn n acc).size = acc.size := by
  induction n with
  | zero => rfl
  | succ n ih => simp [accumBucketsRange, ih]

theorem read1D_accumBucketsRange_of_lt (idxFn : ℕ → ℕ) (valFn : ℕ → ℤ) (n : ℕ) (acc : Array ℤ)
    (k2 : ℕ) (hk2 : k2 < acc.size) :
    read1D (accumBucketsRange idxFn valFn n acc) k2 =
      read1D acc k2 + sumRangeInt (fun i => if idxFn i = k2 then valFn i else 0) n := by
  induction n with
  | zero =>
    simp [accumBucketsRange, sumRangeInt]
  | succ n ih =>
    dsimp only [accumBucketsRange, sumRangeInt]
    have hk2' : k2 < (accumBucketsRange idxFn valFn n acc).size := by simp [hk2]
    rw [read1D_accumBucketInt_of_lt _ _ _ k2 hk2', ih, add_assoc]

/-- Single-pass 2-level overlap-add bucket accumulation helper over `b ∈ 0 .. numBlocks - 1`
and `i ∈ 0 .. W2 - 1`. -/
def overlapAddBucketsSinglePassAux (W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) :
    ℕ → Array ℤ → Array ℤ
  | 0, acc => acc
  | b + 1, acc =>
    let acc' := overlapAddBucketsSinglePassAux W2 idxFn valFn b acc
    accumBucketsRange (idxFn b) (valFn b) W2 acc'

@[simp]
theorem size_overlapAddBucketsSinglePassAux (W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ)
    (b : ℕ) (acc : Array ℤ) :
    (overlapAddBucketsSinglePassAux W2 idxFn valFn b acc).size = acc.size := by
  induction b with
  | zero => rfl
  | succ b ih => simp [overlapAddBucketsSinglePassAux, ih]

theorem read1D_overlapAddBucketsSinglePassAux_of_lt
    (W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) (b : ℕ) (acc : Array ℤ)
    (k2 : ℕ) (hk2 : k2 < acc.size) :
    read1D (overlapAddBucketsSinglePassAux W2 idxFn valFn b acc) k2 =
      read1D acc k2 +
        sumRangeInt (fun b' => sumRangeInt (fun i => if idxFn b' i = k2 then valFn b' i else 0) W2) b := by
  induction b with
  | zero =>
    simp [overlapAddBucketsSinglePassAux, sumRangeInt]
  | succ b ih =>
    dsimp only [overlapAddBucketsSinglePassAux, sumRangeInt]
    have hk2' : k2 < (overlapAddBucketsSinglePassAux W2 idxFn valFn b acc).size := by simp [hk2]
    rw [read1D_accumBucketsRange_of_lt _ _ W2 _ k2 hk2', ih, add_assoc]

/-- **Single-Pass $O(r)$ Overlap-Add Bucket Accumulator (`overlapAddBucketsSinglePass`, `[MS]` §6.2)**:
Initializes an array of `r` zero buckets `Array.replicate r 0` and performs a single pass over
`b ∈ 0 .. numBlocks - 1` and `i ∈ 0 .. W2 - 1` (at most `4 * r` steps per row by
`kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le`), updating the target bucket in $O(1)$
at each step instead of scanning all `(b, i)` pairs separately for each of the `r` output buckets. -/
def overlapAddBucketsSinglePass (r numBlocks W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) : Array ℤ :=
  overlapAddBucketsSinglePassAux W2 idxFn valFn numBlocks (Array.replicate r 0)

theorem read1D_overlapAddBucketsSinglePass_of_lt
    (r numBlocks W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) (k2 : ℕ) (hk2 : k2 < r) :
    read1D (overlapAddBucketsSinglePass r numBlocks W2 idxFn valFn) k2 =
      sumRangeInt (fun b => sumRangeInt (fun i => if idxFn b i = k2 then valFn b i else 0) W2) numBlocks := by
  unfold overlapAddBucketsSinglePass
  have hk2_sz : k2 < (Array.replicate r (0 : ℤ)).size := by simp [hk2]
  rw [read1D_overlapAddBucketsSinglePassAux_of_lt W2 idxFn valFn numBlocks _ k2 hk2_sz]
  have hzero : read1D (Array.replicate r (0 : ℤ)) k2 = 0 := by
    unfold read1D
    simp [hk2]
  rw [hzero, zero_add]

theorem emod_toNat_eq_iff_of_lt (x : ℤ) (r k2 : ℕ) (hk2 : k2 < r) :
    ((x % (r : ℤ)).toNat = k2) ↔ (x % (r : ℤ) = (k2 : ℤ)) := by
  have hr_pos : (0 : ℤ) < (r : ℤ) := by omega
  have hnonneg : 0 ≤ x % (r : ℤ) := Int.emod_nonneg x hr_pos.ne'
  rw [← Int.ofNat_inj, Int.toNat_of_nonneg hnonneg]

/-- Pure-integer contiguous-row Kronecker spread with runtime operation-cost accumulation
(`computableSpreadRowContiguousWithCost`, `[MS]` §6.2):
given the pre-folded integer tap polynomial `gTapFold : List ℤ` and contiguous row `xRow : Array (ℤ × ℤ)`,
computes the real and imaginary block products `prodRe`, `prodIm` and their runtime bit-operation cost
for each block `b < numBlocks`, converts each block product to `Array ℤ` for $O(1)$ indexing, and
accumulates all block products into `r` buckets in a single $O(r)$ pass via `overlapAddBucketsSinglePass`
(performing $\le 4r$ bucket updates per row instead of $\Theta(r^2)$ per-output scans). -/
def computableSpreadRowContiguousWithCost
    (p_in q m1 r : ℕ) (gTapFold : List ℤ) (xRow : Array (ℤ × ℤ)) : Array (ℤ × ℤ) × ℕ :=
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let blockPairs : Array ((Array ℤ × Array ℤ) × ℕ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockRe := computableSpreadRowBlockReContiguous p_in q m1 r xRow b.val
    let fBlockIm := computableSpreadRowBlockImContiguous p_in q m1 r xRow b.val
    let sRe := computableKroneckerBitStride fBlockRe gTapFold
    let sIm := computableKroneckerBitStride fBlockIm gTapFold
    let prodRe := polyMulKroneckerSignedComputable sRe fBlockRe gTapFold
    let prodIm := polyMulKroneckerSignedComputable sIm fBlockIm gTapFold
    let blockCost :=
      computableMulBitCost (fBlockRe.length * sRe) +
      computableMulBitCost (fBlockIm.length * sIm) +
      2 * W_eff * addBitCost sRe +
      2 * W_eff * addBitCost sIm
    ((prodRe.toArray, prodIm.toArray), blockCost))
  let idxFn := fun b i => ((((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat
  let bucketsRe := overlapAddBucketsSinglePass r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodReArr := if hb : b < blockPairs.size then blockPairs[b].1.1 else #[]
      read1D prodReArr i)
  let bucketsIm := overlapAddBucketsSinglePass r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodImArr := if hb : b < blockPairs.size then blockPairs[b].1.2 else #[]
      read1D prodImArr i)
  let outArr : Array (ℤ × ℤ) := Array.ofFn (fun k2 : Fin r =>
    (read1D bucketsRe k2.val, read1D bucketsIm k2.val))
  (outArr, sumArrayCosts blockPairs)

/-- Contiguous-row pure-integer Kronecker spread (`computableSpreadRowContiguous`, `[MS]` §6.2). -/
def computableSpreadRowContiguous
    (p_in q m1 r : ℕ) (gTapFold : List ℤ) (xRow : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (computableSpreadRowContiguousWithCost p_in q m1 r gTapFold xRow).1

theorem computableSpreadRowContiguousWithCost_eq_kroneckerSincGaussianSpreadArray
    (α : ℝ) (p_in q m1 t1 r : ℕ) (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 k2 : ℕ)
    (hx : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) (hk2 : k2 < r) :
    let uRaw := read1D (computableSpreadRowContiguousWithCost p_in q m1 r
      (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) xRow).1 k2
    (⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q),
      (uRaw.2 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q)⟩ : ℂ) =
      kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2 := by
  dsimp only [computableSpreadRowContiguousWithCost, kroneckerSincGaussianSpreadArray]
  rw [read1D_ofFn_of_lt r _ hk2]
  dsimp only
  rw [read1D_overlapAddBucketsSinglePass_of_lt r _ _ _ _ k2 hk2,
      read1D_overlapAddBucketsSinglePass_of_lt r _ _ _ _ k2 hk2]
  simp only [emod_toNat_eq_iff_of_lt _ r k2 hk2, sumRangeInt_eq_sum, ← Finset.sum_filter,
    polyMulKroneckerSignedComputable_eq, computableKroneckerBitStride_eq]
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  set gTapFold := kroneckerSpreadFilterTapsFolded α q m1 t1 r j1
  have hRe_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodReArr :=
          if hb : b < numBlocks then
            let fBlockRe := computableSpreadRowBlockReContiguous p_in q m1 r xRow b
            (polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold).toArray
          else #[]
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          read1D prodReArr i) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b
        let prodRe := polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    simp only [hb, ↓reduceDIte, read1D_toArray_eq_getD,
      computableSpreadRowBlockReContiguous_eq p_in q m1 t1 r xRow x j1 hx b]
  have hIm_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodImArr :=
          if hb : b < numBlocks then
            let fBlockIm := computableSpreadRowBlockImContiguous p_in q m1 r xRow b
            (polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold).toArray
          else #[]
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          read1D prodImArr i) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b
        let prodIm := polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    simp only [hb, ↓reduceDIte, read1D_toArray_eq_getD,
      computableSpreadRowBlockImContiguous_eq p_in q m1 t1 r xRow x j1 hx b]
  simp only [Array.size_ofFn, Array.getElem_ofFn]
  rw [hRe_sum, hIm_sum]

theorem computableSpreadRowContiguousWithCost_snd_eq
    (α : ℝ) (p_in q m1 t1 r : ℕ) (xRow : Array (ℤ × ℤ)) (x : ℕ → ℂ) (j1 : ℕ)
    (hx : ∀ i < r, x (j1 + t1 * i) = toScaledComplex p_in (read1D xRow i)) :
    (computableSpreadRowContiguousWithCost p_in q m1 r
      (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) xRow).2 =
      ∑ b ∈ Finset.range (kroneckerSpreadNumBlocks m1 r),
        (mulBitCost
            ((kroneckerSpreadRowBlockRe q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          mulBitCost
            ((kroneckerSpreadRowBlockIm q m1 t1 r x j1 b).length *
              kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * effectiveFilterWidth m1 r *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockRe q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1)) +
          2 * effectiveFilterWidth m1 r *
            addBitCost
              (kroneckerBitStride (kroneckerSpreadRowBlockIm q m1 t1 r x j1 b)
                (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1))) := by
  unfold computableSpreadRowContiguousWithCost
  dsimp only
  refine sumArrayCosts_ofFn_eq_sum (kroneckerSpreadNumBlocks m1 r) _ _ (fun b _ => ?_)
  dsimp only
  simp only [computableMulBitCost_eq, computableKroneckerBitStride_eq,
    computableSpreadRowBlockReContiguous_eq p_in q m1 t1 r xRow x j1 hx b,
    computableSpreadRowBlockImContiguous_eq p_in q m1 t1 r xRow x j1 hx b]

/-- Step-instrumented pure-integer multi-stage Radix-2 Synthetic FFT (`computableSyntheticFFTRadix2WithCost`, `[MS]` §3.5 (Lemma 3.5)):
materializes period-$2^m \times r$ arrays at stage $m$, uses the single-pass $O(r)$ `computableNegacyclicDirect`
shift, and accumulates `2 * addBitCost (4 * p')` across each of the `2 * r` complex outputs of each of the
`2 ^ m` Radix-2 butterflies in stage `m + 1`. -/
def computableSyntheticFFTRadix2WithCost (p' V r : ℕ) :
    ℕ → ℕ → Array (Array (ℤ × ℤ)) → Array (Array (ℤ × ℤ)) × ℕ
  | 0, _, P =>
    (Array.ofFn (fun _ : Fin 1 =>
      Array.ofFn (fun k2 : Fin r => (P.getD 0 #[]).getD k2.val (0, 0))), 0)
  | m + 1, c1, P =>
    let Peven := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val) #[])
    let Podd := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val + 1) #[])
    let Y0_res := computableSyntheticFFTRadix2WithCost p' V r m (2 * c1) Peven
    let Y1_res := computableSyntheticFFTRadix2WithCost p' V r m (2 * c1) Podd
    let outMat := Array.ofFn (fun v1 : Fin (2 ^ (m + 1)) =>
      let y0_row := Y0_res.1.getD (v1.val % 2 ^ m) #[]
      let y1_shifted := computableNegacyclicDirect r (2 * c1 * v1.val) (Y1_res.1.getD (v1.val % 2 ^ m) #[])
      Array.ofFn (fun k2 : Fin r =>
        let a := y0_row.getD k2.val (0, 0)
        let b := y1_shifted.getD k2.val (0, 0)
        (divRoundPow2 (a.1 + b.1) 1, divRoundPow2 (a.2 + b.2) 1)))
    let stageCost := (2 ^ m) * ((2 * r) * (2 * addBitCost (4 * p')))
    (outMat, Y0_res.2 + Y1_res.2 + stageCost)

@[simp]
theorem computableSyntheticFFTRadix2WithCost_fst
    (p' V r m c1 : ℕ) (P : Array (Array (ℤ × ℤ))) :
    (computableSyntheticFFTRadix2WithCost p' V r m c1 P).1 =
      computableSyntheticFFTRadix2 V r m c1 P := by
  induction m generalizing c1 P with
  | zero => rfl
  | succ m ih =>
    dsimp only [computableSyntheticFFTRadix2WithCost, computableSyntheticFFTRadix2]
    rw [ih, ih]

@[simp]
theorem computableSyntheticFFTRadix2WithCost_snd
    (p' V r m c1 : ℕ) (P : Array (Array (ℤ × ℤ))) :
    (computableSyntheticFFTRadix2WithCost p' V r m c1 P).2 =
      2 * syntheticFFTRadix2AddOps r m * addBitCost (4 * p') := by
  induction m generalizing c1 P with
  | zero => simp [computableSyntheticFFTRadix2WithCost, syntheticFFTRadix2AddOps]
  | succ m ih =>
    dsimp only [computableSyntheticFFTRadix2WithCost, syntheticFFTRadix2AddOps]
    rw [ih, ih]
    ring

/-- Pure-integer row block for `kroneckerSpreadRowBlockRe` on `xArr : Array (ℤ × ℤ)` at input precision `p_in`. -/
def computableSpreadRowBlockRe (p_in q m1 t1 r : ℕ) (xArr : Array (ℤ × ℤ)) (j1 b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun a =>
    if b * W_eff + a < r then
      gQuantizeCoordToScale p_in q (read1D xArr (j1 + t1 * (b * W_eff + a))).1
    else 0)

/-- Pure-integer row block for `kroneckerSpreadRowBlockIm` on `xArr : Array (ℤ × ℤ)` at input precision `p_in`. -/
def computableSpreadRowBlockIm (p_in q m1 t1 r : ℕ) (xArr : Array (ℤ × ℤ)) (j1 b : ℕ) : List ℤ :=
  let W_eff := effectiveFilterWidth m1 r
  (List.range W_eff).map (fun a =>
    if b * W_eff + a < r then
      gQuantizeCoordToScale p_in q (read1D xArr (j1 + t1 * (b * W_eff + a))).2
    else 0)

theorem computableSpreadRowBlockRe_eq
    (p_in q m1 t1 r : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < t1 * r, x k = toScaledComplex p_in (read1D xArr k))
    (j1 : ℕ) (hj1 : j1 < t1) (b : ℕ) :
    computableSpreadRowBlockRe p_in q m1 t1 r xArr j1 b =
      kroneckerSpreadRowBlockRe q m1 t1 r x j1 b := by
  unfold computableSpreadRowBlockRe kroneckerSpreadRowBlockRe
  dsimp only
  refine List.map_congr_left fun a _ => ?_
  split_ifs with hlt
  · have hidx_lt : j1 + t1 * (b * effectiveFilterWidth m1 r + a) < t1 * r := by
      have hle : b * effectiveFilterWidth m1 r + a + 1 ≤ r := hlt
      calc j1 + t1 * (b * effectiveFilterWidth m1 r + a)
          < t1 + t1 * (b * effectiveFilterWidth m1 r + a) := Nat.add_lt_add_right hj1 _
        _ = t1 * (b * effectiveFilterWidth m1 r + a + 1) := by ring
        _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
    rw [hx _ hidx_lt]
    exact gQuantizeCoordToScale_eq_quantizeInt p_in q _
  · rfl

theorem computableSpreadRowBlockIm_eq
    (p_in q m1 t1 r : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < t1 * r, x k = toScaledComplex p_in (read1D xArr k))
    (j1 : ℕ) (hj1 : j1 < t1) (b : ℕ) :
    computableSpreadRowBlockIm p_in q m1 t1 r xArr j1 b =
      kroneckerSpreadRowBlockIm q m1 t1 r x j1 b := by
  unfold computableSpreadRowBlockIm kroneckerSpreadRowBlockIm
  dsimp only
  refine List.map_congr_left fun a _ => ?_
  split_ifs with hlt
  · have hidx_lt : j1 + t1 * (b * effectiveFilterWidth m1 r + a) < t1 * r := by
      have hle : b * effectiveFilterWidth m1 r + a + 1 ≤ r := hlt
      calc j1 + t1 * (b * effectiveFilterWidth m1 r + a)
          < t1 + t1 * (b * effectiveFilterWidth m1 r + a) := Nat.add_lt_add_right hj1 _
        _ = t1 * (b * effectiveFilterWidth m1 r + a + 1) := by ring
        _ ≤ t1 * r := Nat.mul_le_mul_left t1 hle
    rw [hx _ hidx_lt]
    exact gQuantizeCoordToScale_eq_quantizeInt p_in q _
  · rfl

/-- Pure-integer row-materialized Kronecker spread (`computableSpreadRowExact`, `[MS]` §6.2):
given the pre-folded integer tap polynomial `gTapFold : List ℤ` for row `j1`, computes the real and
imaginary block products `blockProdsRe` and `blockProdsIm` once per block `b < numBlocks` via
`polyMulKroneckerSignedComputable` and accumulates them into `r` buckets in a single $O(r)$ pass via
`overlapAddBucketsSinglePass` (representing `U(j_1, k_2)` scaled by `2^{2q}`). -/
def computableSpreadRowExact
    (p_in q m1 t1 r : ℕ) (gTapFold : List ℤ) (xArr : Array (ℤ × ℤ)) (j1 : ℕ) : Array (ℤ × ℤ) :=
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let blockProdsRe : Array (Array ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockRe := computableSpreadRowBlockRe p_in q m1 t1 r xArr j1 b.val
    (polyMulKroneckerSignedComputable (computableKroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold).toArray)
  let blockProdsIm : Array (Array ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockIm := computableSpreadRowBlockIm p_in q m1 t1 r xArr j1 b.val
    (polyMulKroneckerSignedComputable (computableKroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold).toArray)
  let idxFn := fun b i => ((((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat
  let bucketsRe := overlapAddBucketsSinglePass r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodReArr := if hb : b < blockProdsRe.size then blockProdsRe[b] else #[]
      read1D prodReArr i)
  let bucketsIm := overlapAddBucketsSinglePass r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodImArr := if hb : b < blockProdsIm.size then blockProdsIm[b] else #[]
      read1D prodImArr i)
  Array.ofFn (fun k2 : Fin r =>
    (read1D bucketsRe k2.val, read1D bucketsIm k2.val))

/-- Exact equivalence between `computableSpreadRowExact` and `kroneckerSincGaussianSpreadArray`. -/
theorem computableSpreadRowExact_eq_kroneckerSincGaussianSpreadArray
    (α : ℝ) (p_in q m1 t1 r : ℕ) (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < t1 * r, x k = toScaledComplex p_in (read1D xArr k))
    (j1 k2 : ℕ) (hj1 : j1 < t1) (hk2 : k2 < r) :
    let uRaw := read1D (computableSpreadRowExact p_in q m1 t1 r
      (kroneckerSpreadFilterTapsFolded α q m1 t1 r j1) xArr j1) k2
    (⟨(uRaw.1 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q),
      (uRaw.2 : ℝ) / ((2 : ℝ) ^ q * (2 : ℝ) ^ q)⟩ : ℂ) =
      kroneckerSincGaussianSpreadArray α q m1 t1 r x j1 k2 := by
  dsimp only [computableSpreadRowExact, kroneckerSincGaussianSpreadArray]
  rw [read1D_ofFn_of_lt r _ hk2]
  dsimp only
  rw [read1D_overlapAddBucketsSinglePass_of_lt r _ _ _ _ k2 hk2,
      read1D_overlapAddBucketsSinglePass_of_lt r _ _ _ _ k2 hk2]
  simp only [emod_toNat_eq_iff_of_lt _ r k2 hk2, sumRangeInt_eq_sum, ← Finset.sum_filter,
    polyMulKroneckerSignedComputable_eq, computableKroneckerBitStride_eq]
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  set gTapFold := kroneckerSpreadFilterTapsFolded α q m1 t1 r j1
  set blockProdsRe : Array (Array ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockRe := computableSpreadRowBlockRe p_in q m1 t1 r xArr j1 b.val
    (polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold).toArray)
  set blockProdsIm : Array (Array ℤ) := Array.ofFn (fun b : Fin numBlocks =>
    let fBlockIm := computableSpreadRowBlockIm p_in q m1 t1 r xArr j1 b.val
    (polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold).toArray)
  have hRe_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodReArr := if hb : b < blockProdsRe.size then blockProdsRe[b] else #[]
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          read1D prodReArr i) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockRe := kroneckerSpreadRowBlockRe q m1 t1 r x j1 b
        let prodRe := polyMulKroneckerSigned (kroneckerBitStride fBlockRe gTapFold) fBlockRe gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodRe.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    have hb_sz : b < blockProdsRe.size := by simp [blockProdsRe, hb]
    simp only [hb_sz, ↓reduceDIte, blockProdsRe, Array.getElem_ofFn, read1D_toArray_eq_getD,
      computableSpreadRowBlockRe_eq p_in q m1 t1 r xArr x hx j1 hj1 b]
  have hIm_sum :
      (∑ b ∈ Finset.range numBlocks,
        let prodImArr := if hb : b < blockProdsIm.size then blockProdsIm[b] else #[]
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          read1D prodImArr i) =
      ∑ b ∈ Finset.range numBlocks,
        let fBlockIm := kroneckerSpreadRowBlockIm q m1 t1 r x j1 b
        let prodIm := polyMulKroneckerSigned (kroneckerBitStride fBlockIm gTapFold) fBlockIm gTapFold
        ∑ i ∈ (Finset.range (2 * effectiveFilterWidth m1 r)).filter
            (fun i => (((b * effectiveFilterWidth m1 r + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          prodIm.getD i 0 := by
    refine Finset.sum_congr rfl fun b hb_mem => ?_
    have hb : b < numBlocks := Finset.mem_range.mp hb_mem
    have hb_sz : b < blockProdsIm.size := by simp [blockProdsIm, hb]
    simp only [hb_sz, ↓reduceDIte, blockProdsIm, Array.getElem_ofFn, read1D_toArray_eq_getD,
      computableSpreadRowBlockIm_eq p_in q m1 t1 r xArr x hx j1 hj1 b]
  rw [hRe_sum, hIm_sum]

end IntMul
