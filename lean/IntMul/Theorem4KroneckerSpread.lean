import IntMul.Preliminaries

/-!
# `[MS]` Section 6.2: Lemma 6.2 & Theorem 6.3 — Overlap-Add & Signed Two's-Complement Kronecker Substitution

This module is part of our independent formalization of `[MS]` Section 6.2 (Lemma 6.2 and Theorem 6.3)
(companion manuscript `[MS]`, *Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*):

1. **Pre-Folded Filter Width (`effectiveFilterWidth`)**:
   - `W̃_ℓ = min(2 m_{1,ℓ} + 1, r_ℓ) ≤ r_ℓ`.
2. **Signed Two's-Complement Slot Packing & Exact Extraction (`extractSignedSlot`, `unpackSignedKronecker`)**:
   - For half-slot `H > 0` (`M = 2 H = 2^{B_slot}`) and any signed coefficient `c_0 ∈ [-H, H)` and
     upper word `C_rest ∈ ℤ`, the two's-complement extraction rule
     `raw = C % (2 H)`, `coeff = if raw ≥ H then raw - 2 H else raw`
     satisfies `extractSignedSlot H (c_0 + 2 H * C_rest) = c_0` and
     `shiftSignedSlot H (c_0 + 2 H * C_rest) = C_rest` **identically**.
   - By induction over any list of signed convolution coefficients `cs : List ℤ` bounded in `[-H, H)`,
     `unpackSignedKronecker H cs.length (packSignedKronecker (2 * H) cs) = cs` holds with **zero
     bias-correction multiplications**.
3. **Convolution Magnitude & Slot Headroom Bound (`signed_conv_coeff_bound`)**:
   - If `|a_i| ≤ A_max` and `|b_i| ≤ B_max` across `W̃` taps, then `|∑ a_i b_i| ≤ W̃ * A_max * B_max`.
4. **`[MS]` Theorem 6.3 Window-Width Cancellation (`theorem4_window_width_cancellation`; historical `theorem4_*` identifier retained)**:
   - Across `R / W̃` Overlap-Add blocks of bit-length `W̃ * B_slot * log(...)`, the window width
     `W̃` cancels identically between block count and block size.
-/

namespace IntMul

open scoped BigOperators

/-! ## 1. Pre-Folded Effective Filter Width (`[MS]` §§6.1–6.2) -/

/-- Effective filter length after pre-folding modulo `r`: `W̃ = min(2 m_1 + 1, r)`. -/
def effectiveFilterWidth (m1 r : ℕ) : ℕ :=
  min (2 * m1 + 1) r

theorem effectiveFilterWidth_le_r (m1 r : ℕ) :
    effectiveFilterWidth m1 r ≤ r :=
  Nat.min_le_right _ _

theorem effectiveFilterWidth_le_full (m1 r : ℕ) :
    effectiveFilterWidth m1 r ≤ 2 * m1 + 1 :=
  Nat.min_le_left _ _

/-! ## 2. Signed Two's-Complement Kronecker Packing and Exact Unpacking (`[MS]` §6.2, Lemma 6.2, eq. (30)) -/

/-- Pack a list of signed integer coefficients `cs : List ℤ` at radix `M = 2^{B_slot}`:
`packSignedKronecker M [c_0, c_1, ...] = c_0 + M * (c_1 + M * ...)`. -/
def packSignedKronecker (M : ℤ) : List ℤ → ℤ
  | [] => 0
  | c :: cs => c + M * packSignedKronecker M cs

/-- Extract the lowest signed coefficient in `[-H, H)` from a packed integer `C` at radix `2 H`
(`[MS]`, Section 6.2, Lemma 6.2 & Theorem 6.3):
`raw = C % (2 H)`, `if raw ≥ H then raw - 2 H else raw`. -/
def extractSignedSlot (H C : ℤ) : ℤ :=
  let raw := C % (2 * H)
  if raw ≥ H then raw - 2 * H else raw

/-- Shift out the extracted signed coefficient to obtain the remaining upper slots
(`[MS]`, Section 6.2, Lemma 6.2 & Theorem 6.3): `(C - extractSignedSlot H C) / (2 H)`. -/
def shiftSignedSlot (H C : ℤ) : ℤ :=
  (C - extractSignedSlot H C) / (2 * H)

/-- Iteratively unpack `k` signed coefficients in `[-H, H)` from a Kronecker-packed integer `C`. -/
def unpackSignedKronecker (H : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | k + 1, C => extractSignedSlot H C :: unpackSignedKronecker H k (shiftSignedSlot H C)

/-- **Key Lemma (Exact Two's-Complement Single-Slot Recovery)**:
For any `H > 0`, `c_0 ∈ [-H, H)`, and `C_rest ∈ ℤ`, `extractSignedSlot H (c_0 + (2 * H) * C_rest) = c_0`. -/
theorem extractSignedSlot_add_mul (H c0 C_rest : ℤ)
    (hH : 0 < H) (hlo : -H ≤ c0) (hhi : c0 < H) :
    extractSignedSlot H (c0 + (2 * H) * C_rest) = c0 := by
  unfold extractSignedSlot
  dsimp only
  rw [Int.add_mul_emod_self_left]
  by_cases hc0 : 0 ≤ c0
  · have hmod : c0 % (2 * H) = c0 := Int.emod_eq_of_lt hc0 (by omega)
    rw [hmod, if_neg (by omega)]
  · push_neg at hc0
    have h1 : c0 + 2 * H = c0 + (2 * H) * 1 := by ring
    have hmod : c0 % (2 * H) = c0 + 2 * H := by
      have h2 : (c0 + (2 * H) * 1) % (2 * H) = c0 % (2 * H) := Int.add_mul_emod_self_left c0 (2 * H) 1
      rw [← h1] at h2
      have h3 : (c0 + 2 * H) % (2 * H) = c0 + 2 * H :=
        Int.emod_eq_of_lt (by omega) (by omega)
      omega
    rw [hmod, if_pos (by omega)]
    ring

/-- **Key Lemma (Exact Two's-Complement Upper-Word Shift)**:
For any `H > 0`, `c_0 ∈ [-H, H)`, and `C_rest ∈ ℤ`, `shiftSignedSlot H (c_0 + (2 * H) * C_rest) = C_rest`. -/
theorem shiftSignedSlot_add_mul (H c0 C_rest : ℤ)
    (hH : 0 < H) (hlo : -H ≤ c0) (hhi : c0 < H) :
    shiftSignedSlot H (c0 + (2 * H) * C_rest) = C_rest := by
  unfold shiftSignedSlot
  rw [extractSignedSlot_add_mul H c0 C_rest hH hlo hhi]
  have hsub : c0 + 2 * H * C_rest - c0 = (2 * H) * C_rest := by ring
  rw [hsub, Int.mul_ediv_cancel_left C_rest (by omega)]

/-- **`[MS]` Lemma 6.2 & Theorem 6.3 (Part 1: Exactness of Signed Two's-Complement Kronecker Packing & Unpacking, §6.2, eq. (30))**:
For any half-slot `H > 0` (`M = 2 H = 2^{B_slot}`) and any list of signed convolution coefficients
`cs : List ℤ` satisfying `∀ c ∈ cs, -H ≤ c ∧ c < H`, unpacking `packSignedKronecker (2 * H) cs`
recovers `cs` **100% bit-for-bit exactly** without any bias-correction products. -/
theorem theorem4_unpack_pack_signed_kronecker (H : ℤ) (hH : 0 < H) (cs : List ℤ)
    (hbounds : ∀ c ∈ cs, -H ≤ c ∧ c < H) :
    unpackSignedKronecker H cs.length (packSignedKronecker (2 * H) cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c0 rest ih =>
    have hc0 : -H ≤ c0 ∧ c0 < H := hbounds c0 List.mem_cons_self
    have hrest : ∀ c ∈ rest, -H ≤ c ∧ c < H := fun c hc =>
      hbounds c (List.mem_cons_of_mem c0 hc)
    simp only [List.length_cons, packSignedKronecker, unpackSignedKronecker]
    rw [extractSignedSlot_add_mul H c0 (packSignedKronecker (2 * H) rest) hH hc0.1 hc0.2]
    rw [shiftSignedSlot_add_mul H c0 (packSignedKronecker (2 * H) rest) hH hc0.1 hc0.2]
    rw [ih hrest]

/-- Pointwise addition of two polynomial coefficient lists over `ℤ`. -/
def polyAddInt : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: polyAddInt xs ys

/-- Scalar multiplication of a polynomial coefficient list over `ℤ` by `c : ℤ`. -/
def polyScaleInt (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | y :: ys => (c * y) :: polyScaleInt c ys

/-- Acyclic polynomial convolution (multiplication in `ℤ[X]`) of two signed coefficient lists. -/
def polyMulInt : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, ys => polyAddInt (polyScaleInt x ys) (0 :: polyMulInt xs ys)

/-- `packSignedKronecker B` is additive with respect to `polyAddInt`. -/
theorem packSignedKronecker_polyAddInt (B : ℤ) (xs ys : List ℤ) :
    packSignedKronecker B (polyAddInt xs ys) =
      packSignedKronecker B xs + packSignedKronecker B ys := by
  induction xs generalizing ys with
  | nil => simp [polyAddInt, packSignedKronecker]
  | cons x xs ih =>
    cases ys with
    | nil => simp [polyAddInt, packSignedKronecker]
    | cons y ys =>
      simp only [polyAddInt, packSignedKronecker, ih]
      ring

/-- `packSignedKronecker B` commutes with scalar multiplication `polyScaleInt`. -/
theorem packSignedKronecker_polyScaleInt (B c : ℤ) (ys : List ℤ) :
    packSignedKronecker B (polyScaleInt c ys) = c * packSignedKronecker B ys := by
  induction ys with
  | nil => simp [polyScaleInt, packSignedKronecker]
  | cons y ys ih =>
    simp only [polyScaleInt, packSignedKronecker, ih]
    ring

/-- **Polynomial Evaluation Homomorphism for `packSignedKronecker`**:
Evaluating the discrete signed polynomial convolution `polyMulInt xs ys` at Kronecker radix `B`
equals the product of the Kronecker evaluations `packSignedKronecker B xs * packSignedKronecker B ys`. -/
theorem packSignedKronecker_polyMulInt (B : ℤ) (xs ys : List ℤ) :
    packSignedKronecker B (polyMulInt xs ys) =
      packSignedKronecker B xs * packSignedKronecker B ys := by
  induction xs with
  | nil => simp [polyMulInt, packSignedKronecker]
  | cons x xs ih =>
    simp only [polyMulInt, packSignedKronecker_polyAddInt, packSignedKronecker_polyScaleInt,
      packSignedKronecker, ih]
    ring

/-- **Signed Two's-Complement Kronecker Convolution Correctness Theorem**:
For any half-slot `H > 0` (`M = 2 H = 2^{B_slot}`) and any signed integer polynomials `f, g : List ℤ`
whose acyclic convolution `polyMulInt f g` has coefficients strictly within `[-H, H)`,
multiplying their Kronecker-packed integers `packSignedKronecker (2 * H) f * packSignedKronecker (2 * H) g`
and unpacking via two's-complement extraction `unpackSignedKronecker H` recovers the exact signed
acyclic polynomial product `polyMulInt f g` with zero bias-correction multiplications. -/
theorem theorem4_signed_kronecker_polyMul_correct
    (H : ℤ) (hH : 0 < H) (f g : List ℤ)
    (h_headroom : ∀ c ∈ polyMulInt f g, -H ≤ c ∧ c < H) :
    unpackSignedKronecker H (polyMulInt f g).length
      (packSignedKronecker (2 * H) f * packSignedKronecker (2 * H) g) =
      polyMulInt f g := by
  rw [← packSignedKronecker_polyMulInt (2 * H) f g]
  exact theorem4_unpack_pack_signed_kronecker H hH (polyMulInt f g) h_headroom

/-! ## 3. Signed Convolution Magnitude Bound & Window-Width Cancellation (`[MS]` §6.2, Theorem 6.3) -/

/-- Triangle-inequality bound for a signed convolution coefficient of length `W_eff`:
if `|a i| ≤ A_max` and `|b i| ≤ B_max` for all `i < W_eff`, then
`|∑_{i=0}^{W_eff-1} a i * b i| ≤ W_eff * A_max * B_max`. -/
theorem signed_conv_coeff_abs_le (W_eff : ℕ) (a b : ℕ → ℤ) (A_max B_max : ℤ)
    (hA_nonneg : 0 ≤ A_max)
    (ha : ∀ i ∈ Finset.range W_eff, |a i| ≤ A_max)
    (hb : ∀ i ∈ Finset.range W_eff, |b i| ≤ B_max) :
    |∑ i ∈ Finset.range W_eff, a i * b i| ≤ (W_eff : ℤ) * (A_max * B_max) := by
  calc |∑ i ∈ Finset.range W_eff, a i * b i|
      ≤ ∑ i ∈ Finset.range W_eff, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range W_eff, |a i| * |b i| := by
        refine Finset.sum_congr rfl fun i _ => abs_mul (a i) (b i)
    _ ≤ ∑ _i ∈ Finset.range W_eff, A_max * B_max := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul (ha i hi) (hb i hi) (abs_nonneg (b i)) hA_nonneg
    _ = (W_eff : ℤ) * (A_max * B_max) := by
        simp [Finset.sum_const]

/-- **`[MS]` Theorem 6.3 (Part 2: Cancellation of the Effective Window Width `W̃_ℓ`, §6.2, eq. (33))**:
Across `(R / W̃)` Overlap-Add blocks, each multiplying packed integers of bit-length `W̃ * B_slot`,
the effective window width `W̃ > 0` cancels identically between the block count and the packed
integer bit-length:
`(R / W̃) * ((W̃ * B_slot) * logFactor) = R * B_slot * logFactor`. -/
theorem theorem4_window_width_cancellation (R W_eff B_slot logFactor : ℝ) (hW : W_eff ≠ 0) :
    (R / W_eff) * ((W_eff * B_slot) * logFactor) = R * B_slot * logFactor := by
  field_simp [hW]

/-! ## 4. Executable `polyMulKroneckerSigned`, Headroom Bounds, and Pre-Folded Overlap-Add Cancellation (`[MS]` §6.2, Lemma 6.2 & Theorem 6.3) -/

@[simp]
theorem getD_cons_zero {α : Type*} (x : α) (xs : List α) (d : α) :
    (x :: xs).getD 0 d = x := rfl

@[simp]
theorem getD_cons_succ {α : Type*} (x : α) (xs : List α) (k : ℕ) (d : α) :
    (x :: xs).getD (k + 1) d = xs.getD k d := rfl

/-- Accessing `xs.getD k d` at any index `k ≥ xs.length` returns the default value `d`. -/
theorem getD_eq_default_of_le {α : Type*} (xs : List α) (k : ℕ) (d : α)
    (hk : xs.length ≤ k) : xs.getD k d = d := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hk
      exact ih k hk

/-- Executable polynomial multiplication of two signed integer coefficient lists `f` and `g`
using Signed Two's-Complement Kronecker Substitution (`packSignedKronecker` and
`unpackSignedKronecker`) at bit-stride `q` (`pack_signed_kronecker` /
`unpack_signed_kronecker` in `[MS]` §6.2, Lemma 6.2; executable Python specification of an earlier `[MS]` draft omitted in the current `[MS]`). -/
def polyMulKroneckerSigned (q : ℕ) (f g : List ℤ) : List ℤ :=
  let outLen := if f = [] then 0 else if g = [] then f.length else f.length + g.length - 1
  let H : ℤ := (2 : ℤ) ^ (q - 1)
  let Pf := packSignedKronecker (2 * H) f
  let Pg := packSignedKronecker (2 * H) g
  unpackSignedKronecker H outLen (Pf * Pg)

/-- Executable polynomial multiplication of two signed integer coefficient lists `f` and `g`
using Signed Two's-Complement Kronecker Substitution at arbitrary half-slot headroom `H : ℤ`. -/
def polyMulKroneckerSignedH (H : ℤ) (f g : List ℤ) : List ℤ :=
  let outLen := if f = [] then 0 else if g = [] then f.length else f.length + g.length - 1
  let Pf := packSignedKronecker (2 * H) f
  let Pg := packSignedKronecker (2 * H) g
  unpackSignedKronecker H outLen (Pf * Pg)

/-- Maximum absolute value (as `ℕ`) across all elements of a signed integer list `xs : List ℤ`. -/
def listMaxNatAbs (xs : List ℤ) : ℕ :=
  xs.foldr (fun x acc => max x.natAbs acc) 0

/-- Universal half-slot headroom bound for `polyMulInt f g`:
every coefficient `c ∈ polyMulInt f g` satisfies `-kroneckerHeadroom f g ≤ c < kroneckerHeadroom f g`. -/
def kroneckerHeadroom (f g : List ℤ) : ℤ :=
  ((f.length + g.length + 1 : ℕ) : ℤ) *
    ((listMaxNatAbs f + 1 : ℕ) : ℤ) *
    ((listMaxNatAbs g + 1 : ℕ) : ℤ)

/-- Universal two's-complement bit-stride `q : ℕ` for `polyMulKroneckerSigned` guaranteeing
`kroneckerHeadroom f g ≤ 2 ^ (q - 1)`. -/
def kroneckerBitStride (f g : List ℤ) : ℕ :=
  Nat.log2 ((f.length + g.length + 1) * (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1)) + 2

/-- Fold an acyclic convolution coefficient list `conv` of length `≤ 2 R` into a cyclic
length-`R` list modulo `X^R - 1`: coefficient `j` (`0 ≤ j < R`) receives `conv[j] + conv[j + R]`. -/
def overlapAddCyclic (R : ℕ) (conv : List ℤ) : List ℤ :=
  (List.range R).map fun j =>
    conv.getD j 0 + conv.getD (j + R) 0

/-- Length of `polyAddInt as bs` is `max as.length bs.length`. -/
theorem length_polyAddInt (as bs : List ℤ) :
    (polyAddInt as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [polyAddInt]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAddInt]
    | cons b bs =>
      simp only [polyAddInt, List.length_cons, ih]
      omega

/-- Length of `polyScaleInt c ys` is `ys.length`. -/
theorem length_polyScaleInt (c : ℤ) (ys : List ℤ) :
    (polyScaleInt c ys).length = ys.length := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [polyScaleInt, ih]

/-- For any non-empty signed polynomial lists `f, g : List ℤ` (`f ≠ []`, `g ≠ []`),
`(polyMulInt f g).length = f.length + g.length - 1`. -/
theorem length_polyMulInt_of_ne_nil (f g : List ℤ) (hf : f ≠ []) (hg : g ≠ []) :
    (polyMulInt f g).length = f.length + g.length - 1 := by
  have hg_pos : 1 ≤ g.length := by
    cases g with
    | nil => contradiction
    | cons _ _ => simp
  induction f with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [polyMulInt, length_polyAddInt, length_polyScaleInt, List.length_cons,
        List.length_nil]
      omega
    | cons x2 xs2 =>
      have hxs_ne : x2 :: xs2 ≠ [] := List.cons_ne_nil x2 xs2
      have hih := ih hxs_ne
      simp only [polyMulInt, length_polyAddInt, length_polyScaleInt, List.length_cons] at hih ⊢
      omega

/-- When `g = []`, `polyMulInt f []` is a list of `f.length` zeros. -/
theorem length_polyMulInt_nil_right (f : List ℤ) :
    (polyMulInt f []).length = f.length := by
  induction f with
  | nil => rfl
  | cons x xs ih => simp [polyMulInt, polyScaleInt, polyAddInt, ih]

/-- Exact output length of `polyMulInt f g` for all `f, g : List ℤ` (including empty lists). -/
theorem length_polyMulInt_eq (f g : List ℤ) :
    (polyMulInt f g).length =
      (if f = [] then 0 else if g = [] then f.length else f.length + g.length - 1) := by
  by_cases hf : f = []
  · subst hf; rfl
  · by_cases hg : g = []
    · subst hg; simp [hf, length_polyMulInt_nil_right]
    · simp [hf, hg, length_polyMulInt_of_ne_nil f g hf hg]

/-- Length of `polyMulInt xs ys` is bounded by `xs.length + ys.length`. -/
theorem length_polyMulInt_le (xs ys : List ℤ) :
    (polyMulInt xs ys).length ≤ xs.length + ys.length := by
  induction xs with
  | nil => simp [polyMulInt]
  | cons x xs ih =>
    simp only [polyMulInt, length_polyAddInt, length_polyScaleInt, List.length_cons]
    omega

/-- Coefficient extraction for `polyAddInt`. -/
theorem polyAddInt_getD (as bs : List ℤ) (k : ℕ) :
    (polyAddInt as bs).getD k 0 = as.getD k 0 + bs.getD k 0 := by
  induction as generalizing bs k with
  | nil => simp [polyAddInt]
  | cons a as ih =>
    cases bs with
    | nil => simp [polyAddInt]
    | cons b bs =>
      cases k with
      | zero => simp [polyAddInt]
      | succ k => exact ih bs k

/-- Coefficient extraction for `polyScaleInt`. -/
theorem polyScaleInt_getD (c : ℤ) (ys : List ℤ) (k : ℕ) :
    (polyScaleInt c ys).getD k 0 = c * ys.getD k 0 := by
  induction ys generalizing k with
  | nil => simp [polyScaleInt]
  | cons y ys ih =>
    cases k with
    | zero => simp [polyScaleInt]
    | succ k => exact ih k

/-- **Cauchy Convolution Coefficient Identity for `polyMulInt`**:
The `k`-th coefficient of `polyMulInt xs ys` equals the discrete Cauchy product
`∑_{j=0}^k xs[j] * ys[k - j]`. -/
theorem polyMulInt_getD (xs ys : List ℤ) (k : ℕ) :
    (polyMulInt xs ys).getD k 0 =
      ∑ j ∈ Finset.range (k + 1), xs.getD j 0 * ys.getD (k - j) 0 := by
  induction xs generalizing k with
  | nil => simp [polyMulInt]
  | cons x xs ih =>
    rw [polyMulInt, polyAddInt_getD, polyScaleInt_getD, Finset.sum_range_succ']
    cases k with
    | zero => simp
    | succ k =>
      simp only [getD_cons_zero, getD_cons_succ, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, ih k]
      ring

/-- Every `getD k 0` entry of `xs : List ℤ` has `natAbs ≤ listMaxNatAbs xs`. -/
theorem getD_natAbs_le_listMaxNatAbs (xs : List ℤ) (k : ℕ) :
    (xs.getD k 0).natAbs ≤ listMaxNatAbs xs := by
  induction xs generalizing k with
  | nil => simp [listMaxNatAbs]
  | cons x xs ih =>
    simp only [listMaxNatAbs, List.foldr_cons]
    cases k with
    | zero =>
      simp only [getD_cons_zero]
      exact le_max_left _ _
    | succ k =>
      simp only [getD_cons_succ]
      exact (ih k).trans (le_max_right _ _)

/-- Every `getD k 0` entry of `xs : List ℤ` has `|xs.getD k 0| ≤ (listMaxNatAbs xs : ℤ)`. -/
theorem abs_getD_le_listMaxNatAbs (xs : List ℤ) (k : ℕ) :
    |xs.getD k 0| ≤ (listMaxNatAbs xs : ℤ) := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast getD_natAbs_le_listMaxNatAbs xs k

/-- Every element `c ∈ xs` appears at some index `k < xs.length` as `xs.getD k d = c`. -/
theorem exists_getD_of_mem {α : Type*} (xs : List α) (d : α) {c : α} (hc : c ∈ xs) :
    ∃ k < xs.length, xs.getD k d = c := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact ⟨0, Nat.succ_pos _, rfl⟩
    · rcases ih hmem with ⟨k, hk, rfl⟩
      exact ⟨k + 1, Nat.succ_lt_succ hk, rfl⟩

/-- `kroneckerHeadroom f g` is strictly positive for all `f, g : List ℤ`. -/
theorem kroneckerHeadroom_pos (f g : List ℤ) : 0 < kroneckerHeadroom f g := by
  unfold kroneckerHeadroom
  positivity

/-- **Universal Coefficient Headroom Bound for `polyMulInt` (`polyMulInt_mem_bounds_kroneckerHeadroom`, `[MS]` §6.2, Lemma 6.2 & Theorem 6.3)**:
For all signed polynomial lists `f, g : List ℤ`, every coefficient `c ∈ polyMulInt f g` satisfies
`-kroneckerHeadroom f g ≤ c ∧ c < kroneckerHeadroom f g`. -/
theorem polyMulInt_mem_bounds_kroneckerHeadroom (f g : List ℤ) :
    ∀ c ∈ polyMulInt f g, -kroneckerHeadroom f g ≤ c ∧ c < kroneckerHeadroom f g := by
  intro c hc
  obtain ⟨k, hk_len, rfl⟩ := exists_getD_of_mem (polyMulInt f g) 0 hc
  have hk_le : k < f.length + g.length := hk_len.trans_le (length_polyMulInt_le f g)
  rw [polyMulInt_getD]
  have habs_le := signed_conv_coeff_abs_le (k + 1)
    (fun j => f.getD j 0) (fun j => g.getD (k - j) 0)
    (listMaxNatAbs f : ℤ) (listMaxNatAbs g : ℤ)
    (Nat.cast_nonneg _)
    (fun j _ => abs_getD_le_listMaxNatAbs f j)
    (fun j _ => abs_getD_le_listMaxNatAbs g (k - j))
  have hlt :
      ((k + 1 : ℕ) : ℤ) * ((listMaxNatAbs f : ℤ) * (listMaxNatAbs g : ℤ)) <
        kroneckerHeadroom f g := by
    unfold kroneckerHeadroom
    have hnat :
        (k + 1) * (listMaxNatAbs f * listMaxNatAbs g) <
          (f.length + g.length + 1) * (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1) := by
      have h1 : k + 1 ≤ f.length + g.length + 1 := by omega
      have h2 : listMaxNatAbs f * listMaxNatAbs g <
          (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1) := by nlinarith
      calc (k + 1) * (listMaxNatAbs f * listMaxNatAbs g)
          ≤ (f.length + g.length + 1) * (listMaxNatAbs f * listMaxNatAbs g) :=
            Nat.mul_le_mul_right _ h1
        _ < (f.length + g.length + 1) * ((listMaxNatAbs f + 1) * (listMaxNatAbs g + 1)) :=
            Nat.mul_lt_mul_of_pos_left h2 (by omega)
        _ = (f.length + g.length + 1) * (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1) := by ring
    exact_mod_cast hnat
  have habs_lt : |∑ j ∈ Finset.range (k + 1), f.getD j 0 * g.getD (k - j) 0| <
      kroneckerHeadroom f g := habs_le.trans_lt hlt
  rcases abs_lt.mp habs_lt with ⟨hlo, hhi⟩
  exact ⟨hlo.le, hhi⟩

/-- The power-of-two half-slot `2 ^ (kroneckerBitStride f g - 1)` is at least `kroneckerHeadroom f g`. -/
theorem kroneckerHeadroom_le_two_pow_kroneckerBitStride (f g : List ℤ) :
    kroneckerHeadroom f g ≤ (2 : ℤ) ^ (kroneckerBitStride f g - 1) := by
  unfold kroneckerHeadroom kroneckerBitStride
  set N : ℕ := (f.length + g.length + 1) * (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1)
  have hN_pos : 0 < N := by positivity
  have hN_lt : N < 2 ^ (Nat.log2 N + 1) :=
    (Nat.log2_lt hN_pos.ne').mp (Nat.lt_succ_self _)
  have hsub : Nat.log2 N + 2 - 1 = Nat.log2 N + 1 := by omega
  rw [hsub]
  change ((f.length + g.length + 1 : ℕ) : ℤ) *
      ((listMaxNatAbs f + 1 : ℕ) : ℤ) *
      ((listMaxNatAbs g + 1 : ℕ) : ℤ) ≤ (2 : ℤ) ^ (Nat.log2 N + 1)
  exact_mod_cast hN_lt.le

/-- **General Correctness of `polyMulKroneckerSignedH` (`polyMulKroneckerSignedH_eq_polyMulInt`, `[MS]` §6.2, Lemma 6.2)**:
For any half-slot `H > 0` and any signed polynomial lists `f, g : List ℤ` whose acyclic convolution
`polyMulInt f g` has coefficients in `[-H, H)`, `polyMulKroneckerSignedH H f g = polyMulInt f g`. -/
theorem polyMulKroneckerSignedH_eq_polyMulInt
    (H : ℤ) (hH : 0 < H) (f g : List ℤ)
    (h_headroom : ∀ c ∈ polyMulInt f g, -H ≤ c ∧ c < H) :
    polyMulKroneckerSignedH H f g = polyMulInt f g := by
  unfold polyMulKroneckerSignedH
  dsimp only
  rw [← length_polyMulInt_eq f g]
  exact theorem4_signed_kronecker_polyMul_correct H hH f g h_headroom

/-- **Unconditional Signed-Kronecker Polynomial Multiplication Correctness at `kroneckerHeadroom` (`polyMulKroneckerSignedH_kroneckerHeadroom_eq`, `[MS]` §6.2, Lemma 6.2 & Theorem 6.3)**:
For ALL signed polynomial lists `f, g : List ℤ` (with zero preconditions),
`polyMulKroneckerSignedH (kroneckerHeadroom f g) f g = polyMulInt f g`. -/
theorem polyMulKroneckerSignedH_kroneckerHeadroom_eq (f g : List ℤ) :
    polyMulKroneckerSignedH (kroneckerHeadroom f g) f g = polyMulInt f g :=
  polyMulKroneckerSignedH_eq_polyMulInt (kroneckerHeadroom f g)
    (kroneckerHeadroom_pos f g) f g (polyMulInt_mem_bounds_kroneckerHeadroom f g)

/-- **General Correctness of `polyMulKroneckerSigned` (`polyMulKroneckerSigned_eq_polyMulInt`, `[MS]` §6.2, Lemma 6.2)**:
Whenever every convolution coefficient `c ∈ polyMulInt f g` lies in the two's-complement half-slot
`[-2^{q-1}, 2^{q-1})`, `polyMulKroneckerSigned q f g` recovers the exact signed polynomial product
`polyMulInt f g`. -/
theorem polyMulKroneckerSigned_eq_polyMulInt
    (q : ℕ) (f g : List ℤ)
    (_hlen : (polyMulInt f g).length = f.length + g.length - 1)
    (h_headroom : ∀ c ∈ polyMulInt f g, -((2 : ℤ) ^ (q - 1)) ≤ c ∧ c < (2 : ℤ) ^ (q - 1)) :
    polyMulKroneckerSigned q f g = polyMulInt f g := by
  unfold polyMulKroneckerSigned
  dsimp only
  rw [← length_polyMulInt_eq f g]
  have hH : (0 : ℤ) < (2 : ℤ) ^ (q - 1) := by positivity
  exact theorem4_signed_kronecker_polyMul_correct ((2 : ℤ) ^ (q - 1)) hH f g h_headroom

/-- **General Correctness of `polyMulKroneckerSigned` for Non-Empty Input Polynomials**:
For any non-empty `f, g : List ℤ` (`f ≠ []`, `g ≠ []`) whose acyclic convolution `polyMulInt f g`
has coefficients in `[-2^{q-1}, 2^{q-1})`, `polyMulKroneckerSigned q f g = polyMulInt f g`. -/
theorem polyMulKroneckerSigned_eq_polyMulInt_of_ne_nil
    (q : ℕ) (f g : List ℤ) (hf : f ≠ []) (hg : g ≠ [])
    (h_headroom : ∀ c ∈ polyMulInt f g, -((2 : ℤ) ^ (q - 1)) ≤ c ∧ c < (2 : ℤ) ^ (q - 1)) :
    polyMulKroneckerSigned q f g = polyMulInt f g :=
  polyMulKroneckerSigned_eq_polyMulInt q f g (length_polyMulInt_of_ne_nil f g hf hg) h_headroom

/-- **Unconditional Signed-Kronecker Polynomial Multiplication Correctness at `kroneckerBitStride` (`polyMulKroneckerSigned_kroneckerHeadroom_eq`, `[MS]` §6.2, Lemma 6.2 & Theorem 6.3)**:
For ALL signed polynomial lists `f, g : List ℤ` (with zero preconditions),
`polyMulKroneckerSigned (kroneckerBitStride f g) f g = polyMulInt f g`. -/
theorem polyMulKroneckerSigned_kroneckerHeadroom_eq (f g : List ℤ) :
    polyMulKroneckerSigned (kroneckerBitStride f g) f g = polyMulInt f g := by
  unfold polyMulKroneckerSigned
  dsimp only
  rw [← length_polyMulInt_eq f g]
  set H : ℤ := (2 : ℤ) ^ (kroneckerBitStride f g - 1)
  have hH : 0 < H := by positivity
  have hle : kroneckerHeadroom f g ≤ H := kroneckerHeadroom_le_two_pow_kroneckerBitStride f g
  refine theorem4_signed_kronecker_polyMul_correct H hH f g fun c hc => ?_
  rcases polyMulInt_mem_bounds_kroneckerHeadroom f g c hc with ⟨hlo, hhi⟩
  exact ⟨by linarith, hhi.trans_le hle⟩

/-- Alias `polyMulKroneckerSigned_kroneckerBitStride_eq` for `polyMulKroneckerSigned_kroneckerHeadroom_eq`. -/
theorem polyMulKroneckerSigned_kroneckerBitStride_eq (f g : List ℤ) :
    polyMulKroneckerSigned (kroneckerBitStride f g) f g = polyMulInt f g :=
  polyMulKroneckerSigned_kroneckerHeadroom_eq f g

/-- Number of overlap-add blocks `⌈r / W_eff⌉` of length `W_eff = effectiveFilterWidth m1 r`
covering a row of length `r` (`[MS]` §6.2, Theorem 6.3). -/
def kroneckerSpreadNumBlocks (m1 r : ℕ) : ℕ :=
  let W_eff := effectiveFilterWidth m1 r
  (r + W_eff - 1) / W_eff

/-- **Concrete Integer Window-Width Cancellation Bound (`kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le`, `[MS]` §6.2, Theorem 6.3)**:
For any window half-width `m1 : ℕ` and row length `r > 0`, the integer block count
`kroneckerSpreadNumBlocks m1 r = ⌈r / W_eff⌉` multiplied by the pre-folded effective filter width
`W_eff = effectiveFilterWidth m1 r = min(2 m_1 + 1, r)` satisfies:
`kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r ≤ 2 * r`,
with **zero dependence on `m1`** (even when `2 m_1 + 1 ≫ r`). -/
theorem kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le (m1 r : ℕ) :
    kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r ≤ 2 * r := by
  unfold kroneckerSpreadNumBlocks
  dsimp only
  set W_eff := effectiveFilterWidth m1 r
  have hW_le_r : W_eff ≤ r := effectiveFilterWidth_le_r m1 r
  have hdiv_le : ((r + W_eff - 1) / W_eff) * W_eff ≤ r + W_eff - 1 :=
    Nat.div_mul_le_self (r + W_eff - 1) W_eff
  omega

/-- **`[MS]` Theorem 6.3 (Concrete Integer Overlap-Add Block Work Cancellation, §6.2, eq. (33))**:
Across `kroneckerSpreadNumBlocks m1 r = ⌈r / W_eff⌉` Overlap-Add blocks, each multiplying packed
integers of bit-length `W_eff * B_slot` at per-bit cost factor `L_cost ≥ 0`, the pre-folded
window width `W_eff = effectiveFilterWidth m1 r` cancels against the integer ceiling block count:
`(kroneckerSpreadNumBlocks m1 r : ℝ) * (((effectiveFilterWidth m1 r * B_slot : ℕ) : ℝ) * L_cost) ≤
  2 * (r : ℝ) * (B_slot : ℝ) * L_cost`. -/
theorem theorem4_overlapAdd_block_work_cancellation
    (m1 r B_slot : ℕ) (L_cost : ℝ) (hL : 0 ≤ L_cost) :
    (kroneckerSpreadNumBlocks m1 r : ℝ) *
        (((effectiveFilterWidth m1 r * B_slot : ℕ) : ℝ) * L_cost) ≤
      2 * (r : ℝ) * (B_slot : ℝ) * L_cost := by
  have hprod :
      ((kroneckerSpreadNumBlocks m1 r * effectiveFilterWidth m1 r : ℕ) : ℝ) ≤
        ((2 * r : ℕ) : ℝ) := by
    exact_mod_cast kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le m1 r
  push_cast at hprod ⊢
  have hB : (0 : ℝ) ≤ (B_slot : ℝ) * L_cost := mul_nonneg (Nat.cast_nonneg B_slot) hL
  calc (kroneckerSpreadNumBlocks m1 r : ℝ) * ((effectiveFilterWidth m1 r : ℝ) * (B_slot : ℝ) * L_cost)
      = ((kroneckerSpreadNumBlocks m1 r : ℝ) * (effectiveFilterWidth m1 r : ℝ)) *
          ((B_slot : ℝ) * L_cost) := by ring
    _ ≤ (2 * (r : ℝ)) * ((B_slot : ℝ) * L_cost) := mul_le_mul_of_nonneg_right hprod hB
    _ = 2 * (r : ℝ) * (B_slot : ℝ) * L_cost := by ring

/-- Lookup in `(List.range n).map f` at index `i`: equals `f i` if `i < n`, and `0` otherwise. -/
theorem getD_map_range (n : ℕ) (f : ℕ → ℤ) (i : ℕ) :
    ((List.range n).map f).getD i 0 = if i < n then f i else 0 := by
  by_cases hi : i < n
  · rw [if_pos hi]
    have hlen : i < ((List.range n).map f).length := by simp [hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some,
      List.getElem_map, List.getElem_range]
  · rw [if_neg hi]
    have hlen : ((List.range n).map f).length ≤ i := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none]

/-- Reindexing `∑ j ∈ Finset.range M, F (M - 1 - j) = ∑ s ∈ Finset.range M, F s`. -/
theorem sum_range_sub_eq_sum_range {E : Type*} [AddCommMonoid E] (M : ℕ) (F : ℕ → E) :
    (∑ j ∈ Finset.range M, F (M - 1 - j)) = ∑ s ∈ Finset.range M, F s := by
  refine Finset.sum_bij (fun j _ => M - 1 - j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro j1 hj1 j2 hj2 heq
    rw [Finset.mem_range] at hj1 hj2
    omega
  · intro s hs
    rw [Finset.mem_range] at hs
    refine ⟨M - 1 - s, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro j _
    rfl

/-- Exact coefficient extraction at index `k + W` (`W = 2 * m1`) of the discrete
polynomial product `polyMulInt ((List.range N).map f) ((List.range (W + 1)).map g)` when `k + W < N`:
`(polyMulInt ((List.range N).map f) ((List.range (W + 1)).map g)).getD (k + W) 0 =
  ∑ s ∈ Finset.range (W + 1), f (k + W - s) * g s`. -/
theorem polyMulInt_map_range_getD_add (N W k : ℕ) (hk : k + W < N) (f g : ℕ → ℤ) :
    (polyMulInt ((List.range N).map f) ((List.range (W + 1)).map g)).getD (k + W) 0 =
      ∑ s ∈ Finset.range (W + 1), f (k + W - s) * g s := by
  rw [polyMulInt_getD]
  have hsplit : k + W + 1 = k + (W + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h1 :
      ∑ i ∈ Finset.range k,
        ((List.range N).map f).getD i 0 * ((List.range (W + 1)).map g).getD (k + W - i) 0 = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [getD_map_range (W + 1) g (k + W - i), if_neg (by omega), mul_zero]
  rw [h1, zero_add]
  have h2 :
      ∑ j ∈ Finset.range (W + 1),
        ((List.range N).map f).getD (k + j) 0 *
          ((List.range (W + 1)).map g).getD (k + W - (k + j)) 0 =
      ∑ j ∈ Finset.range (W + 1), f (k + W - (W - j)) * g (W - j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hkj : k + j < N := by omega
    have hwj : k + W - (k + j) = W - j := by omega
    have hkwj : k + W - (W - j) = k + j := by omega
    rw [getD_map_range N f (k + j), if_pos hkj, hwj,
      getD_map_range (W + 1) g (W - j), if_pos (by omega), hkwj]
  rw [h2]
  have h3 := sum_range_sub_eq_sum_range (W + 1) (fun s => f (k + W - s) * g s)
  simpa [Nat.add_sub_cancel] using h3

/-- Reindexing `∑ m ∈ Finset.Icc a (a + (n : ℤ)), F m = ∑ s ∈ Finset.range (n + 1), F (a + (s : ℤ))`. -/
theorem sum_Icc_add_nat_eq_sum_range {E : Type*} [AddCommMonoid E] (a : ℤ) (n : ℕ) (F : ℤ → E) :
    (∑ m ∈ Finset.Icc a (a + (n : ℤ)), F m) =
      ∑ s ∈ Finset.range (n + 1), F (a + (s : ℤ)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hstep : a + ((n + 1 : ℕ) : ℤ) = (a + (n : ℤ)) + 1 := by omega
    rw [hstep, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
        Finset.sum_insert (by simp), ih,
        Finset.sum_range_succ (fun s => F (a + (s : ℤ))) (n + 1),
        hstep, add_comm]

/-- Reindexing a symmetric integer interval `Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)` to `Finset.range (2 * m1 + 1)`. -/
theorem sum_Icc_neg_eq_sum_range_two_mul_add_one {E : Type*} [AddCommMonoid E] (m1 : ℕ) (F : ℤ → E) :
    (∑ m ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), F m) =
      ∑ s ∈ Finset.range (2 * m1 + 1), F ((s : ℤ) - (m1 : ℤ)) := by
  have hIcc : Finset.Icc (-(m1 : ℤ)) (m1 : ℤ) =
      Finset.Icc (-(m1 : ℤ)) (-(m1 : ℤ) + ((2 * m1 : ℕ) : ℤ)) := by
    congr 1
    push_cast
    ring
  rw [hIcc, sum_Icc_add_nat_eq_sum_range (-(m1 : ℤ)) (2 * m1) F]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  ring

/-- Coefficient `i` of the acyclic product of two length-`W` mapped lists `(List.range W).map f₀`
and `(List.range W).map g₀` written as a sum over `a ∈ Finset.range W`. -/
theorem polyMulInt_map_range_getD_eq_sum_range (W : ℕ) (f₀ g₀ : ℕ → ℤ) (i : ℕ) :
    (polyMulInt ((List.range W).map f₀) ((List.range W).map g₀)).getD i 0 =
      ∑ a ∈ Finset.range W, if a ≤ i ∧ i - a < W then f₀ a * g₀ (i - a) else 0 := by
  rw [polyMulInt_getD]
  have h1 :
      ∑ a ∈ Finset.range (i + 1),
        ((List.range W).map f₀).getD a 0 * ((List.range W).map g₀).getD (i - a) 0 =
      ∑ a ∈ Finset.range (i + 1),
        if a < W ∧ i - a < W then f₀ a * g₀ (i - a) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [getD_map_range W f₀ a, getD_map_range W g₀ (i - a)]
    by_cases ha : a < W <;> by_cases hia : i - a < W <;> simp [ha, hia]
  rw [h1, ← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Filtered sum over `i ∈ Finset.range (2 * W)` of `(polyMulInt ((List.range W).map f₀) ((List.range W).map g₀)).getD i 0`
equals the double sum over `a, u ∈ Finset.range W` at `i = a + u`. -/
theorem sum_filter_polyMulInt_map_range_eq (W : ℕ) (f₀ g₀ : ℕ → ℤ)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ i ∈ (Finset.range (2 * W)).filter P,
      (polyMulInt ((List.range W).map f₀) ((List.range W).map g₀)).getD i 0) =
    ∑ a ∈ Finset.range W, ∑ u ∈ Finset.range W,
      if P (a + u) then f₀ a * g₀ u else 0 := by
  rw [Finset.sum_filter]
  have h1 :
      (∑ i ∈ Finset.range (2 * W),
        if P i then (polyMulInt ((List.range W).map f₀) ((List.range W).map g₀)).getD i 0 else 0) =
      ∑ i ∈ Finset.range (2 * W), ∑ a ∈ Finset.range W,
        if P i ∧ a ≤ i ∧ i - a < W then f₀ a * g₀ (i - a) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [polyMulInt_map_range_getD_eq_sum_range]
    by_cases hP : P i <;> simp [hP]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine (Finset.sum_bij (fun u _ => a + u) ?_ ?_ ?_ ?_).symm
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
    exact ⟨by omega, hu.2, by omega, by omega⟩
  · intro u1 _ u2 _ heq
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨i - a, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have heq : a + (i - a) = i := by omega
    rw [heq]
    exact hi.2.1
  · intro u _
    rw [Nat.add_sub_cancel_left]

/-- Block-flattening identity: summing over `b < M` and `a < W` at `b * W + a` equals
summing over `k < M * W`. -/
theorem sum_range_mul_range {E : Type*} [AddCommMonoid E] (M W : ℕ) (f : ℕ → E) :
    (∑ b ∈ Finset.range M, ∑ a ∈ Finset.range W, f (b * W + a)) =
      ∑ k ∈ Finset.range (M * W), f k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, ← Finset.sum_range_add, Nat.succ_mul]

/-- Partitioning `Finset.range r` into `⌈r / W⌉` blocks of length `W > 0`. -/
theorem sum_blocks_eq_sum_range {E : Type*} [AddCommMonoid E]
    (r W : ℕ) (hW : 0 < W) (H : ℕ → E) :
    (∑ b ∈ Finset.range ((r + W - 1) / W),
      ∑ a ∈ Finset.range W,
        if b * W + a < r then H (b * W + a) else 0) =
    ∑ j2 ∈ Finset.range r, H j2 := by
  rw [sum_range_mul_range ((r + W - 1) / W) W (fun k => if k < r then H k else 0)]
  rw [← Finset.sum_filter]
  have hr_le : r ≤ ((r + W - 1) / W) * W := by
    have hdiv := Nat.div_add_mod' (r + W - 1) W
    have hmod := Nat.mod_lt (r + W - 1) hW
    omega
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Unique modular match in `Finset.range r` for `((j2 : ℤ) + δ) % r = k2` when `k2 < r`. -/
theorem sum_range_ite_emod_eq (r k2 : ℕ) (hk2 : k2 < r) (δ : ℤ) (F : ℕ → ℤ) :
    (∑ j2 ∈ Finset.range r,
      if ((j2 : ℤ) + δ) % (r : ℤ) = (k2 : ℤ) then F j2 else 0) =
    F ((((k2 : ℤ) - δ) % (r : ℤ)).toNat) := by
  set j2₀ : ℕ := (((k2 : ℤ) - δ) % (r : ℤ)).toNat
  have hr_pos : (0 : ℤ) < (r : ℤ) := by omega
  have hmod_nonneg : 0 ≤ ((k2 : ℤ) - δ) % (r : ℤ) := Int.emod_nonneg _ (by omega)
  have hmod_lt : ((k2 : ℤ) - δ) % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos _ hr_pos
  have hj2₀_cast : (j2₀ : ℤ) = ((k2 : ℤ) - δ) % (r : ℤ) := Int.toNat_of_nonneg hmod_nonneg
  have hj2₀_lt : j2₀ < r := by omega
  have hcongr :
      (∑ j2 ∈ Finset.range r,
        if ((j2 : ℤ) + δ) % (r : ℤ) = (k2 : ℤ) then F j2 else 0) =
      ∑ j2 ∈ Finset.range r, if j2 = j2₀ then F j2 else 0 := by
    refine Finset.sum_congr rfl fun j2 hj2 => ?_
    rw [Finset.mem_range] at hj2
    have hiff : ((j2 : ℤ) + δ) % (r : ℤ) = (k2 : ℤ) ↔ j2 = j2₀ := by
      constructor
      · intro h
        have h1 : (((j2 : ℤ) + δ) % (r : ℤ) - δ) % (r : ℤ) = ((k2 : ℤ) - δ) % (r : ℤ) := by
          rw [h]
        have h2 : (((j2 : ℤ) + δ) % (r : ℤ) - δ) % (r : ℤ) = (j2 : ℤ) := by
          rw [Int.emod_sub_emod, add_sub_cancel_right]
          exact Int.emod_eq_of_lt (by omega) (by omega)
        omega
      · intro h
        rw [h, hj2₀_cast, Int.emod_add_emod, sub_add_cancel]
        exact Int.emod_eq_of_lt (by omega) (by omega)
    by_cases h : j2 = j2₀
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hm => h (hiff.mp hm)), if_neg h]
  rw [hcongr, Finset.sum_ite_eq' (Finset.range r) j2₀ F,
    if_pos (Finset.mem_range.mpr hj2₀_lt)]

/-- Unfolding the pre-folded filter sum over `u ∈ Finset.range (effectiveFilterWidth m1 r)`
back to the full `2 * m1 + 1` filter taps. -/
theorem sum_folded_filter_eq (m1 r k2 : ℕ) (hk2 : k2 < r) (F G : ℕ → ℤ) :
    (∑ u ∈ Finset.range (effectiveFilterWidth m1 r),
      F ((((k2 : ℤ) - ((u : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) *
        (∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % effectiveFilterWidth m1 r = u), G s)) =
    ∑ s ∈ Finset.range (2 * m1 + 1),
      F ((((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) * G s := by
  set W_eff := effectiveFilterWidth m1 r
  have hW_pos : 0 < W_eff := by
    unfold W_eff effectiveFilterWidth
    omega
  have h_idx_eq : ∀ s < 2 * m1 + 1,
      (((k2 : ℤ) - (((s % W_eff : ℕ) : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat =
        (((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat := by
    intro s hs
    congr 1
    by_cases hle : 2 * m1 + 1 ≤ r
    · have hW : W_eff = 2 * m1 + 1 := by
        unfold W_eff effectiveFilterWidth
        omega
      rw [hW, Nat.mod_eq_of_lt hs]
    · have hW : W_eff = r := by
        unfold W_eff effectiveFilterWidth
        omega
      rw [hW, Int.natCast_emod]
      have h1 : (k2 : ℤ) - ((s : ℤ) % (r : ℤ) - (m1 : ℤ)) =
          ((k2 : ℤ) + (m1 : ℤ)) - (s : ℤ) % (r : ℤ) := by ring
      have h2 : (k2 : ℤ) - ((s : ℤ) - (m1 : ℤ)) =
          ((k2 : ℤ) + (m1 : ℤ)) - (s : ℤ) := by ring
      rw [h1, h2, Int.sub_emod_emod]
  have h1 :
      (∑ u ∈ Finset.range W_eff,
        F ((((k2 : ℤ) - ((u : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) *
          (∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % W_eff = u), G s)) =
      ∑ u ∈ Finset.range W_eff,
        ∑ s ∈ Finset.range (2 * m1 + 1),
          if s % W_eff = u then
            F ((((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) * G s
          else 0 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    by_cases hsu : s % W_eff = u
    · rw [if_pos hsu, if_pos hsu, ← hsu, h_idx_eq s hs]
    · rw [if_neg hsu, if_neg hsu]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_ite_eq (Finset.range W_eff) (s % W_eff),
    if_pos (Finset.mem_range.mpr (Nat.mod_lt s hW_pos))]

/-- **Overlap-Add with Pre-Folded Filter Equivalence Lemma (`[MS]` §6.2, Theorem 6.3)**:
For any row sequence `F : ℕ → ℤ`, filter tap sequence `G : ℕ → ℤ`, and output index `k2 < r`,
summing the acyclic block convolutions `polyMulInt (fBlock b) gTapFold` across all
`b < kroneckerSpreadNumBlocks m1 r` and `i < 2 * W_eff` with `(b * W_eff + i - m1) % r = k2`
recovers the exact cyclic windowed convolution sum over `s ∈ Finset.range (2 * m1 + 1)`. -/
theorem overlapAdd_folded_polyMulInt_eq
    (m1 r k2 : ℕ) (hk2 : k2 < r) (F G : ℕ → ℤ) :
    let W_eff := effectiveFilterWidth m1 r
    let numBlocks := kroneckerSpreadNumBlocks m1 r
    let gTapFold := (List.range W_eff).map (fun u =>
      ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % W_eff = u), G s)
    (∑ b ∈ Finset.range numBlocks,
      let fBlock := (List.range W_eff).map (fun a =>
        if b * W_eff + a < r then F (b * W_eff + a) else 0)
      ∑ i ∈ (Finset.range (2 * W_eff)).filter
          (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
        (polyMulInt fBlock gTapFold).getD i 0) =
    ∑ s ∈ Finset.range (2 * m1 + 1),
      F ((((k2 : ℤ) - ((s : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) * G s := by
  dsimp only
  set W_eff := effectiveFilterWidth m1 r
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  set g₀ : ℕ → ℤ := fun u =>
    ∑ s ∈ (Finset.range (2 * m1 + 1)).filter (fun s => s % W_eff = u), G s
  have hW_pos : 0 < W_eff := by
    unfold W_eff effectiveFilterWidth
    omega
  have hstep1 :
      (∑ b ∈ Finset.range numBlocks,
        ∑ i ∈ (Finset.range (2 * W_eff)).filter
            (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ)),
          (polyMulInt ((List.range W_eff).map (fun a =>
              if b * W_eff + a < r then F (b * W_eff + a) else 0))
            ((List.range W_eff).map g₀)).getD i 0) =
      ∑ b ∈ Finset.range numBlocks,
        ∑ a ∈ Finset.range W_eff,
          ∑ u ∈ Finset.range W_eff,
            (if b * W_eff + a < r then
              (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                F (b * W_eff + a)
              else 0)
            else 0) * g₀ u := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sum_filter_polyMulInt_map_range_eq W_eff
      (fun a => if b * W_eff + a < r then F (b * W_eff + a) else 0) g₀
      (fun i => (((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ))]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    have hassoc : b * W_eff + (a + u) = b * W_eff + a + u := by omega
    rw [hassoc]
    split_ifs <;> ring
  rw [hstep1]
  have hswap :
      (∑ b ∈ Finset.range numBlocks,
        ∑ a ∈ Finset.range W_eff,
          ∑ u ∈ Finset.range W_eff,
            (if b * W_eff + a < r then
              (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                F (b * W_eff + a)
              else 0)
            else 0) * g₀ u) =
      ∑ u ∈ Finset.range W_eff,
        (∑ b ∈ Finset.range numBlocks,
          ∑ a ∈ Finset.range W_eff,
            if b * W_eff + a < r then
              (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                F (b * W_eff + a)
              else 0)
            else 0) * g₀ u := by
    calc (∑ b ∈ Finset.range numBlocks,
            ∑ a ∈ Finset.range W_eff,
              ∑ u ∈ Finset.range W_eff,
                (if b * W_eff + a < r then
                  (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                    F (b * W_eff + a)
                  else 0)
                else 0) * g₀ u)
        = ∑ b ∈ Finset.range numBlocks,
            ∑ u ∈ Finset.range W_eff,
              ∑ a ∈ Finset.range W_eff,
                (if b * W_eff + a < r then
                  (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                    F (b * W_eff + a)
                  else 0)
                else 0) * g₀ u := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ u ∈ Finset.range W_eff,
            ∑ b ∈ Finset.range numBlocks,
              ∑ a ∈ Finset.range W_eff,
                (if b * W_eff + a < r then
                  (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                    F (b * W_eff + a)
                  else 0)
                else 0) * g₀ u := Finset.sum_comm
      _ = ∑ u ∈ Finset.range W_eff,
            (∑ b ∈ Finset.range numBlocks,
              ∑ a ∈ Finset.range W_eff,
                if b * W_eff + a < r then
                  (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                    F (b * W_eff + a)
                  else 0)
                else 0) * g₀ u := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
  rw [hswap]
  have hstep2 :
      (∑ u ∈ Finset.range W_eff,
        (∑ b ∈ Finset.range numBlocks,
          ∑ a ∈ Finset.range W_eff,
            if b * W_eff + a < r then
              (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
                F (b * W_eff + a)
              else 0)
            else 0) * g₀ u) =
      ∑ u ∈ Finset.range W_eff,
        F ((((k2 : ℤ) - ((u : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat) * g₀ u := by
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    have hblk := sum_blocks_eq_sum_range r W_eff hW_pos
      (fun j2 => if (((j2 + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then F j2 else 0)
    change (∑ b ∈ Finset.range ((r + W_eff - 1) / W_eff),
        ∑ a ∈ Finset.range W_eff,
          if b * W_eff + a < r then
            (if (((b * W_eff + a + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then
              F (b * W_eff + a)
            else 0)
          else 0) =
      F ((((k2 : ℤ) - ((u : ℤ) - (m1 : ℤ))) % (r : ℤ)).toNat)
    rw [hblk]
    have hcast :
        (∑ j2 ∈ Finset.range r,
          if (((j2 + u : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ) = (k2 : ℤ) then F j2 else 0) =
        ∑ j2 ∈ Finset.range r,
          if ((j2 : ℤ) + ((u : ℤ) - (m1 : ℤ))) % (r : ℤ) = (k2 : ℤ) then F j2 else 0 := by
      refine Finset.sum_congr rfl fun j2 _ => ?_
      have heq : (((j2 + u : ℕ) : ℤ) - (m1 : ℤ)) = (j2 : ℤ) + ((u : ℤ) - (m1 : ℤ)) := by
        push_cast
        ring
      rw [heq]
    rw [hcast]
    exact sum_range_ite_emod_eq r k2 hk2 ((u : ℤ) - (m1 : ℤ)) F
  rw [hstep2]
  exact sum_folded_filter_eq m1 r k2 hk2 F G

/-- Bound `listMaxNatAbs xs` when every element of `xs` has `natAbs ≤ B`. -/
theorem listMaxNatAbs_le (xs : List ℤ) (B : ℕ) (h : ∀ c ∈ xs, c.natAbs ≤ B) :
    listMaxNatAbs xs ≤ B := by
  induction xs with
  | nil => simp [listMaxNatAbs]
  | cons x xs ih =>
    simp only [listMaxNatAbs, List.foldr_cons, max_le_iff]
    exact ⟨h x List.mem_cons_self, ih (fun c hc => h c (List.mem_cons_of_mem x hc))⟩

/-- Triangle inequality for `Int.natAbs` over a `Finset` sum. -/
theorem natAbs_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℤ) (K : ℕ)
    (h : ∀ s ∈ S, (f s).natAbs ≤ K) :
    (∑ s ∈ S, f s).natAbs ≤ S.card * K := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih =>
    rw [Finset.sum_cons, Finset.card_cons]
    have ha_le : (f a).natAbs ≤ K := h a (Finset.mem_cons_self a S)
    have hS_le : (∑ s ∈ S, f s).natAbs ≤ S.card * K :=
      ih (fun s hs => h s (Finset.mem_cons_of_mem hs))
    have htri := Int.natAbs_add_le (f a) (∑ s ∈ S, f s)
    calc (f a + ∑ s ∈ S, f s).natAbs
        ≤ (f a).natAbs + (∑ s ∈ S, f s).natAbs := htri
      _ ≤ K + S.card * K := Nat.add_le_add ha_le hS_le
      _ = (S.card + 1) * K := by ring

/-- General `kroneckerBitStride ≤ 6 * P` bound from polynomial length and coefficient magnitude bounds
for `P ≥ 17`. -/
theorem kroneckerBitStride_le_six_mul_of_bounds
    (P : ℕ) (hP : 17 ≤ P) (f g : List ℤ)
    (hf_len : f.length ≤ 4 * P + 1)
    (hg_len : g.length ≤ 4 * P + 1)
    (hf_max : listMaxNatAbs f ≤ 2 ^ (3 * P) + 1)
    (hg_max : listMaxNatAbs g ≤ (4 * P + 1) * (2 ^ (2 * P) + 1)) :
    kroneckerBitStride f g ≤ 6 * P := by
  unfold kroneckerBitStride
  set N := (f.length + g.length + 1) * (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1)
  have hN_pos : 0 < N := by positivity
  have hpoly : ∀ d : ℕ, (8 * (17 + d) + 3) * (4 * (17 + d) + 2) * 8 < 2 ^ (17 + d) := by
    intro d
    induction d with
    | zero => decide
    | succ d ih =>
      have hstep :
          (8 * (17 + (d + 1)) + 3) * (4 * (17 + (d + 1)) + 2) * 8 ≤
            2 * ((8 * (17 + d) + 3) * (4 * (17 + d) + 2) * 8) := by
        nlinarith
      have hpow : 2 ^ (17 + (d + 1)) = 2 * 2 ^ (17 + d) := by
        have heq : 17 + (d + 1) = (17 + d) + 1 := by omega
        rw [heq, pow_succ']
      omega
  have hpolyP : (8 * P + 3) * (4 * P + 2) * 8 < 2 ^ P := by
    have h1 := hpoly (P - 17)
    have heq : 17 + (P - 17) = P := by omega
    rwa [heq] at h1
  have hpowP : 2 ^ P = 2 ^ (P - 1) * 2 := by
    have heq : P = (P - 1) + 1 := by omega
    conv_lhs => rw [heq, pow_succ]
  have hpoly4 : (8 * P + 3) * (4 * P + 2) * 4 < 2 ^ (P - 1) := by omega
  have hpow3P : 2 ≤ 2 ^ (3 * P) := by
    have h1 : 1 ≤ 3 * P := by omega
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ (3 * P) := Nat.pow_le_pow_right (by omega) h1
  have hpow2P : 1 ≤ 2 ^ (2 * P) := Nat.one_le_two_pow
  have hL : f.length + g.length + 1 ≤ 8 * P + 3 := by omega
  have hA : listMaxNatAbs f + 1 ≤ 2 * 2 ^ (3 * P) := by omega
  have hB : listMaxNatAbs g + 1 ≤ (4 * P + 2) * (2 * 2 ^ (2 * P)) := by
    calc listMaxNatAbs g + 1
        ≤ (4 * P + 1) * (2 ^ (2 * P) + 1) + 1 := by omega
      _ ≤ (4 * P + 2) * (2 * 2 ^ (2 * P)) := by nlinarith
  have hN_le : N ≤ ((8 * P + 3) * (4 * P + 2) * 4) * (2 ^ (3 * P) * 2 ^ (2 * P)) := by
    calc N = (f.length + g.length + 1) * (listMaxNatAbs f + 1) * (listMaxNatAbs g + 1) := rfl
      _ ≤ (8 * P + 3) * (2 * 2 ^ (3 * P)) * ((4 * P + 2) * (2 * 2 ^ (2 * P))) :=
          Nat.mul_le_mul (Nat.mul_le_mul hL hA) hB
      _ = ((8 * P + 3) * (4 * P + 2) * 4) * (2 ^ (3 * P) * 2 ^ (2 * P)) := by ring
  have hN_lt : N < 2 ^ (6 * P - 1) := by
    have hpos : 0 < 2 ^ (3 * P) * 2 ^ (2 * P) := by positivity
    have hlt := Nat.mul_lt_mul_of_pos_right hpoly4 hpos
    have hpow_comb : 2 ^ (P - 1) * (2 ^ (3 * P) * 2 ^ (2 * P)) = 2 ^ (6 * P - 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    omega
  have hlog : Nat.log2 N < 6 * P - 1 := (Nat.log2_lt hN_pos.ne').mpr hN_lt
  omega

end IntMul
