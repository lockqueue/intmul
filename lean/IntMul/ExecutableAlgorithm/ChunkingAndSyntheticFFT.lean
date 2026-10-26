/-
Copyright (c) 2026 The Authors. All rights reserved.

Executable reference components for our independent formalization of `[MS]`
(*Integer multiplication in O(n log n) time on a single two-dimensional grid, with a machine-checked proof*,
2026; corresponds to `[MS]` Section 7.1, Listing 1 and the executable Python specification
of an earlier `[MS]` draft, omitted in the current `[MS]`).

This module provides an executable, machine-verified Lean 4 implementation of the core
algorithmic components (cf. `[MS]` §§3.5, 6.2, 6.3, 7.1; earlier `[MS]` draft Python specification omitted in current `[MS]`):
1. Radix-`2^b` chunking (`splitChunks`), polynomial radix evaluation (`evalRadix`), and
   carry-propagating integer reconstruction (`reconstructChunks`), with machine-checked
   proofs that `reconstructChunks b cs = evalRadix (2^b) cs` and
   `reconstructChunks b (splitChunks b k A) = A` whenever `A < (2^b)^k`.
2. Executable Negacyclic Quotient Ring `ℤ[y]/(y^r + 1)` arithmetic (`negacyclicShiftInt`,
   `negacyclicAddInt`, `negacyclicSubInt`) and addition-only Radix-2
   Synthetic FFT / IFFT butterflies (`syntheticFFTButterflyInt`, `syntheticIFFTButterflyInt`),
   proving exact multiplication-free inversion `syntheticIFFTButterflyInt (syntheticFFTButterflyInt P0 P1) = (2 • P0, 2 • P1)`.
3. Executable Signed Two's-Complement Kronecker polynomial multiplication (`polyMulKroneckerSigned`)
   and cyclic overlap-add folding (`overlapAddCyclic`).
4. Executable verification test suite proved by `decide` / `rfl` covering multi-word integer
   multiplication, signed two's-complement Kronecker convolution with negative coefficients,
   addition-only Synthetic FFT butterflies over `ℤ[y]/(y^r + 1)`, and the additive precision schedule (`[MS]` §6.3, Lemma 6.5, eq. (34)).
-/

import IntMul.Preliminaries
import IntMul.Theorem1TwistedDuality
import IntMul.Theorem2PoissonIdentity
import IntMul.Theorem3BidiagonalAndSchedule
import IntMul.Theorem4KroneckerSpread
import IntMul.Theorem5ComplexityAndCorrectness
import IntMul.Theorem6And7Barriers

namespace IntMul

/-! ## 1. Radix-`2^b` Chunking and Carry-Propagating Reconstruction (`[MS]` §7.1, Listing 1) -/

/-- Evaluate a list of natural-number chunks `cs = [c_0, c_1, ..., c_{k-1}]` in radix `B`:
`evalRadix B cs = ∑_{j=0}^{k-1} c_j B^j`. -/
def evalRadix (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + B * evalRadix B cs

/-- Split a natural number `A` into `k` chunks in base `2^b` (`split_chunks` in an earlier `[MS]` draft's Python specification, omitted in current `[MS]`; cf. `[MS]` §7.1, Listing 1). -/
def splitChunks (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, A => (A % (2 ^ b)) :: splitChunks b k (A / (2 ^ b))

/-- Length of `splitChunks b k A` is `k`. -/
@[simp]
theorem length_splitChunks (b k A : ℕ) : (splitChunks b k A).length = k := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => simp [splitChunks, ih]

/-- **Exact Chunking Identity**:
Evaluating `splitChunks b k A` in radix `2^b` yields `A % (2^b)^k`. -/
theorem evalRadix_splitChunks (b k A : ℕ) :
    evalRadix (2 ^ b) (splitChunks b k A) = A % ((2 ^ b) ^ k) := by
  induction k generalizing A with
  | zero =>
    simp [splitChunks, evalRadix, Nat.mod_one]
  | succ k ih =>
    simp only [splitChunks, evalRadix, ih, pow_succ']
    rw [← Nat.mod_mul_right_div_self]
    have hmod : A % (2 ^ b) = (A % (2 ^ b * (2 ^ b) ^ k)) % (2 ^ b) :=
      (Nat.mod_mul_right_mod A (2 ^ b) ((2 ^ b) ^ k)).symm
    rw [hmod, Nat.mod_add_div]

/-- When `A < (2^b)^k`, `splitChunks b k A` is a lossless representation of `A`. -/
theorem evalRadix_splitChunks_of_lt (b k A : ℕ) (hA : A < (2 ^ b) ^ k) :
    evalRadix (2 ^ b) (splitChunks b k A) = A := by
  rw [evalRadix_splitChunks, Nat.mod_eq_of_lt hA]

/-- Helper for carry-propagating reconstruction (`reconstruct_chunks` in an earlier `[MS]` draft's Python specification, omitted in current `[MS]`; cf. `[MS]` §7.1, Listing 1):
accumulates `(c + carry) % 2^b` at each radix-`2^b` position and propagates
`carry' = (c + carry) / 2^b`. -/
def reconstructChunksAux (B : ℕ) : List ℕ → ℕ → ℕ
  | [], carry => carry
  | c :: cs, carry =>
    ((c + carry) % B) + B * reconstructChunksAux B cs ((c + carry) / B)

/-- Carry-propagating integer reconstruction in base `2^b` (`reconstruct_chunks` in an earlier `[MS]` draft's Python specification, omitted in current `[MS]`; cf. `[MS]` §7.1, Listing 1). -/
def reconstructChunks (b : ℕ) (cs : List ℕ) : ℕ :=
  reconstructChunksAux (2 ^ b) cs 0

/-- **Carry-Propagation Exactness**:
For any base `B > 0`, `reconstructChunksAux B cs carry = carry + evalRadix B cs`. -/
theorem reconstructChunksAux_eq_add_evalRadix (B : ℕ) (cs : List ℕ) (carry : ℕ) :
    reconstructChunksAux B cs carry = carry + evalRadix B cs := by
  induction cs generalizing carry with
  | nil =>
    simp [reconstructChunksAux, evalRadix]
  | cons c cs ih =>
    simp only [reconstructChunksAux, evalRadix, ih]
    have hdiv : (c + carry) % B + B * ((c + carry) / B) = c + carry := by
      rw [add_comm, Nat.div_add_mod]
    calc
      (c + carry) % B + B * ((c + carry) / B + evalRadix B cs)
        = ((c + carry) % B + B * ((c + carry) / B)) + B * evalRadix B cs := by ring
      _ = (c + carry) + B * evalRadix B cs := by rw [hdiv]
      _ = carry + (c + B * evalRadix B cs) := by ring

/-- **Theorem (`reconstructChunks` equals `evalRadix`)**:
Carry-propagating reconstruction `reconstructChunks b cs` computes the exact radix-`2^b` value
`evalRadix (2^b) cs`. -/
theorem reconstructChunks_eq_evalRadix (b : ℕ) (cs : List ℕ) :
    reconstructChunks b cs = evalRadix (2 ^ b) cs := by
  unfold reconstructChunks
  rw [reconstructChunksAux_eq_add_evalRadix, zero_add]

/-- **Round-Trip Theorem (`reconstructChunks` inverts `splitChunks`)**:
For any `A < (2^b)^k`, `reconstructChunks b (splitChunks b k A) = A`. -/
theorem reconstructChunks_splitChunks_of_lt (b k A : ℕ) (hA : A < (2 ^ b) ^ k) :
    reconstructChunks b (splitChunks b k A) = A := by
  rw [reconstructChunks_eq_evalRadix, evalRadix_splitChunks_of_lt b k A hA]

/-- **Chunk Splitting Block-Concatenation Identity**:
Splitting `A` into `k1 + k2` chunks in base `2^b` equals splitting the low `k1`-chunk part
`A % (2^b)^k1` into `k1` chunks followed by splitting the high `k2`-chunk part
`A / (2^b)^k1` into `k2` chunks. -/
theorem splitChunks_add (b k1 k2 A : ℕ) :
    splitChunks b (k1 + k2) A =
      splitChunks b k1 (A % ((2 ^ b) ^ k1)) ++ splitChunks b k2 (A / ((2 ^ b) ^ k1)) := by
  induction k1 generalizing A with
  | zero =>
    simp [splitChunks]
  | succ k1 ih =>
    have hadd : k1 + 1 + k2 = (k1 + k2) + 1 := by omega
    rw [hadd]
    simp only [splitChunks, List.cons_append, pow_succ']
    have hmod : (A % (2 ^ b * (2 ^ b) ^ k1)) % (2 ^ b) = A % (2 ^ b) :=
      Nat.mod_mul_right_mod A (2 ^ b) ((2 ^ b) ^ k1)
    have hdiv_mod : (A % (2 ^ b * (2 ^ b) ^ k1)) / (2 ^ b) = (A / (2 ^ b)) % ((2 ^ b) ^ k1) :=
      Nat.mod_mul_right_div_self A (2 ^ b) ((2 ^ b) ^ k1)
    have hdiv_div : A / (2 ^ b * (2 ^ b) ^ k1) = (A / (2 ^ b)) / ((2 ^ b) ^ k1) := by
      rw [Nat.div_div_eq_div_mul]
    rw [hmod, hdiv_mod, hdiv_div, ← ih (A / (2 ^ b))]

/-- Structural-recursion helper for balanced divide-and-conquer binary-tree chunk splitting
(avoiding `WellFounded.fix` so both `dsimp` and kernel `decide` reduce in one step). -/
def splitChunksTreeAux : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | fuel + 1, b, k, A =>
    if k = 0 then []
    else if k = 1 then [A % (2 ^ b)]
    else
      let k1 := k / 2
      let k2 := k - k1
      let M := (2 ^ b) ^ k1
      splitChunksTreeAux fuel b k1 (A % M) ++ splitChunksTreeAux fuel b k2 (A / M)

/-- **Balanced Divide-and-Conquer Binary-Tree Chunk Splitting (`splitChunksTree`; `[MS]` §7.1)**:
Splits `A` into `k` chunks in base `2^b` via a balanced binary tree of depth `⌈log_2 k⌉`,
halving the chunk count `k = k1 + k2` (`k1 = k / 2`, `k2 = k - k1`) at each node via
`A % (2^b)^k1` and `A / (2^b)^k1`. When `2^b` is word/bit-aligned (or via fast division),
this avoids the `Θ(k^2 b)` schoolbook loop of `splitChunks`. -/
def splitChunksTree (b k A : ℕ) : List ℕ :=
  splitChunksTreeAux k b k A

theorem splitChunksTreeAux_eq_splitChunks :
    ∀ fuel b k A : ℕ, k ≤ fuel → splitChunksTreeAux fuel b k A = splitChunks b k A
  | 0, _, k, _, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  | fuel + 1, b, k, A, hk => by
    unfold splitChunksTreeAux
    split_ifs with h0 h1
    · subst h0; rfl
    · subst h1; simp [splitChunks]
    · dsimp only
      have hk1 : k / 2 ≤ fuel := by omega
      have hk2 : k - k / 2 ≤ fuel := by omega
      have hsum : k = k / 2 + (k - k / 2) := by omega
      rw [splitChunksTreeAux_eq_splitChunks fuel b (k / 2) _ hk1,
          splitChunksTreeAux_eq_splitChunks fuel b (k - k / 2) _ hk2]
      conv_rhs => rw [hsum, splitChunks_add]

/-- **Equivalence of Balanced Binary-Tree Chunk Splitting (`splitChunksTree_eq_splitChunks`)**:
`splitChunksTree b k A` produces the exact same chunk list as `splitChunks b k A`. -/
theorem splitChunksTree_eq_splitChunks (b k A : ℕ) :
    splitChunksTree b k A = splitChunks b k A :=
  splitChunksTreeAux_eq_splitChunks k b k A le_rfl

/-- **Radix Evaluation over List Concatenation**:
`evalRadix B (xs ++ ys) = evalRadix B xs + B ^ xs.length * evalRadix B ys`. -/
theorem evalRadix_append (B : ℕ) (xs ys : List ℕ) :
    evalRadix B (xs ++ ys) = evalRadix B xs + B ^ xs.length * evalRadix B ys := by
  induction xs with
  | nil =>
    simp [evalRadix]
  | cons x xs ih =>
    simp only [List.cons_append, evalRadix, List.length_cons, ih, pow_succ']
    ring

/-- Structural-recursion helper for balanced divide-and-conquer binary-tree radix reconstruction
(avoiding `WellFounded.fix` so both `dsimp` and kernel `decide` reduce in one step). -/
def reconstructChunksTreeAux : ℕ → ℕ → ℕ → List ℕ → ℕ
  | 0, _, _, _ => 0
  | fuel + 1, B, k, cs =>
    if k = 0 then 0
    else if k = 1 then cs.headD 0
    else
      let k1 := k / 2
      let k2 := k - k1
      reconstructChunksTreeAux fuel B k1 (cs.take k1) +
        (B ^ k1) * reconstructChunksTreeAux fuel B k2 (cs.drop k1)

/-- **Balanced Divide-and-Conquer Binary-Tree Reconstruction (`reconstructChunksTree`; `[MS]` §7.1)**:
Reconstructs `cs` in base `2^b` via a balanced binary tree of depth `⌈log_2 cs.length⌉`,
combining `cs.take k1` and `cs.drop k1` via a single radix shift `(2^b)^k1` at each node. -/
def reconstructChunksTree (b : ℕ) (cs : List ℕ) : ℕ :=
  reconstructChunksTreeAux cs.length (2 ^ b) cs.length cs

/-- `reconstructChunksTreeAux fuel B cs.length cs = evalRadix B cs` whenever `cs.length ≤ fuel`. -/
theorem reconstructChunksTreeAux_eq_evalRadix :
    ∀ (fuel B k : ℕ) (cs : List ℕ), cs.length = k → k ≤ fuel →
      reconstructChunksTreeAux fuel B k cs = evalRadix B cs
  | 0, _, k, cs, hlen, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    cases cs with
    | nil => rfl
    | cons _ _ => contradiction
  | fuel + 1, B, k, cs, hlen, hk => by
    unfold reconstructChunksTreeAux
    split_ifs with h0 h1
    · subst h0
      cases cs with
      | nil => rfl
      | cons _ _ => contradiction
    · subst h1
      cases cs with
      | nil => contradiction
      | cons c rest =>
        cases rest with
        | nil => simp [evalRadix]
        | cons _ _ => simp at hlen
    · dsimp only
      set k1 := k / 2
      set k2 := k - k1
      have hk1 : k1 ≤ fuel := by omega
      have hk2 : k2 ≤ fuel := by omega
      have hlen_take : (cs.take k1).length = k1 := by
        rw [List.length_take, hlen]
        omega
      have hlen_drop : (cs.drop k1).length = k2 := by
        rw [List.length_drop, hlen]
      rw [reconstructChunksTreeAux_eq_evalRadix fuel B k1 (cs.take k1) hlen_take hk1,
          reconstructChunksTreeAux_eq_evalRadix fuel B k2 (cs.drop k1) hlen_drop hk2]
      have happ := evalRadix_append B (cs.take k1) (cs.drop k1)
      rw [List.take_append_drop, hlen_take] at happ
      exact happ.symm

/-- **Equivalence of Balanced Binary-Tree Reconstruction (`reconstructChunksTree_eq_reconstructChunks`)**:
`reconstructChunksTree b cs` computes the exact same integer as `reconstructChunks b cs`
and `evalRadix (2^b) cs`. -/
theorem reconstructChunksTree_eq_evalRadix (b : ℕ) (cs : List ℕ) :
    reconstructChunksTree b cs = evalRadix (2 ^ b) cs :=
  reconstructChunksTreeAux_eq_evalRadix cs.length (2 ^ b) cs.length cs rfl le_rfl

theorem reconstructChunksTree_eq_reconstructChunks (b : ℕ) (cs : List ℕ) :
    reconstructChunksTree b cs = reconstructChunks b cs := by
  rw [reconstructChunksTree_eq_evalRadix, reconstructChunks_eq_evalRadix]

/-- **Balanced Tree Round-Trip Theorem (`reconstructChunksTree` inverts `splitChunksTree`)**:
For any `A < (2^b)^k`, `reconstructChunksTree b (splitChunksTree b k A) = A`. -/
theorem reconstructChunksTree_splitChunksTree_of_lt (b k A : ℕ) (hA : A < (2 ^ b) ^ k) :
    reconstructChunksTree b (splitChunksTree b k A) = A := by
  rw [reconstructChunksTree_eq_reconstructChunks, splitChunksTree_eq_splitChunks,
    reconstructChunks_splitChunks_of_lt b k A hA]

/-- Pointwise addition of two polynomial coefficient lists over `ℕ`. -/
def polyAddList : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: polyAddList xs ys

/-- Scalar multiplication of a polynomial coefficient list over `ℕ` by `c : ℕ`. -/
def polyScaleList (c : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => (c * y) :: polyScaleList c ys

/-- Acyclic polynomial convolution (multiplication in `ℕ[X]`) of two coefficient lists. -/
def polyMulList : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: xs, ys => polyAddList (polyScaleList x ys) (0 :: polyMulList xs ys)

/-- `evalRadix B` is additive with respect to `polyAddList`. -/
theorem evalRadix_polyAddList (B : ℕ) (xs ys : List ℕ) :
    evalRadix B (polyAddList xs ys) = evalRadix B xs + evalRadix B ys := by
  induction xs generalizing ys with
  | nil => simp [polyAddList, evalRadix]
  | cons x xs ih =>
    cases ys with
    | nil => simp [polyAddList, evalRadix]
    | cons y ys =>
      simp only [polyAddList, evalRadix, ih]
      ring

/-- `evalRadix B` commutes with scalar multiplication `polyScaleList`. -/
theorem evalRadix_polyScaleList (B c : ℕ) (ys : List ℕ) :
    evalRadix B (polyScaleList c ys) = c * evalRadix B ys := by
  induction ys with
  | nil => simp [polyScaleList, evalRadix]
  | cons y ys ih =>
    simp only [polyScaleList, evalRadix, ih]
    ring

/-- **Polynomial Evaluation Homomorphism for `polyMulList`**:
Evaluating the discrete polynomial convolution `polyMulList xs ys` at radix `B` equals the
product of the radix evaluations `evalRadix B xs * evalRadix B ys`. -/
theorem evalRadix_polyMulList (B : ℕ) (xs ys : List ℕ) :
    evalRadix B (polyMulList xs ys) = evalRadix B xs * evalRadix B ys := by
  induction xs with
  | nil => simp [polyMulList, evalRadix]
  | cons x xs ih =>
    simp only [polyMulList, evalRadix_polyAddList, evalRadix_polyScaleList, evalRadix, ih]
    ring

/-- **End-to-End Radix-`2^b` Chunked Convolution & Carry-Reconstruction Theorem**:
For any chunk width `b` and any natural numbers `A < (2^b)^{k_1}` and `B < (2^b)^{k_2}`,
splitting `A` and `B` into radix-`2^b` chunks, convolving the chunk polynomials via `polyMulList`,
and applying carry-propagating reconstruction `reconstructChunks b` yields the exact integer
product `A * B`. -/
theorem reconstructChunks_polyMulList_splitChunks
    (b k1 k2 A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    reconstructChunks b (polyMulList (splitChunks b k1 A) (splitChunks b k2 B)) = A * B := by
  rw [reconstructChunks_eq_evalRadix, evalRadix_polyMulList,
      evalRadix_splitChunks_of_lt b k1 A hA, evalRadix_splitChunks_of_lt b k2 B hB]

/-! ## 2. Executable Addition-Only Synthetic FFT over `ℤ[y]/(y^r + 1)` (`[MS]` §3.5, Lemma 3.5) -/

/-- Executable negacyclic shift of a degree-`< r` integer polynomial `P : Fin r → ℤ` by `s` steps
modulo `y^r + 1` (`negacyclic_shift` in an earlier `[MS]` draft's Python specification, omitted in current `[MS]`; cf. `[MS]` §7.1, Listing 1).
Uses only index permutation and sign negation (zero multiplications). -/
def negacyclicShiftInt {r : ℕ} (s : ℕ) (P : Fin r → ℤ) : Fin r → ℤ :=
  fun m =>
    let s_mod := s % (2 * r)
    let raw := m.val + 2 * r - s_mod
    let idx := raw % r
    have hidx : idx < r := Nat.mod_lt _ (by have := m.isLt; omega)
    if (raw / r) % 2 = 0 then
      P ⟨idx, hidx⟩
    else
      -P ⟨idx, hidx⟩

/-- Pointwise addition of two elements in `ℤ[y]/(y^r + 1)`. -/
def negacyclicAddInt {r : ℕ} (P Q : Fin r → ℤ) : Fin r → ℤ :=
  fun m => P m + Q m

/-- Pointwise subtraction of two elements in `ℤ[y]/(y^r + 1)`. -/
def negacyclicSubInt {r : ℕ} (P Q : Fin r → ℤ) : Fin r → ℤ :=
  fun m => P m - Q m

/-- Executable addition-only Radix-2 Synthetic FFT butterfly over `ℤ[y]/(y^r + 1)`:
Given inputs `(P0, P1)` and synthetic twiddle shift `s`, computes
`T = y^s P1 (mod y^r + 1)` via `negacyclicShiftInt s P1` and returns `(P0 + T, P0 - T)`. -/
def syntheticFFTButterflyInt {r : ℕ} (s : ℕ) (P0 P1 : Fin r → ℤ) :
    (Fin r → ℤ) × (Fin r → ℤ) :=
  let T := negacyclicShiftInt s P1
  (negacyclicAddInt P0 T, negacyclicSubInt P0 T)

/-- Executable addition-only Radix-2 Synthetic IFFT butterfly over `ℤ[y]/(y^r + 1)`:
Given frequency-domain pair `(Q0, Q1)` and twiddle shift `s`, recovers
`(Q0 + Q1, y^{2r - s} (Q0 - Q1)) = (2 P0, 2 P1)`. -/
def syntheticIFFTButterflyInt {r : ℕ} (s : ℕ) (Q0 Q1 : Fin r → ℤ) :
    (Fin r → ℤ) × (Fin r → ℤ) :=
  let diff := negacyclicSubInt Q0 Q1
  (negacyclicAddInt Q0 Q1, negacyclicShiftInt (2 * r - s % (2 * r)) diff)

/-- **Exact First-Output Inversion of the Addition-Only Butterfly**:
For every shift `s` and every index `m`, the first output of `syntheticIFFTButterflyInt`
applied to `syntheticFFTButterflyInt s P0 P1` equals `2 * P0 m`. -/
theorem syntheticIFFTButterflyInt_fst_eq {r : ℕ} (s : ℕ) (P0 P1 : Fin r → ℤ) (m : Fin r) :
    (syntheticIFFTButterflyInt s
      (syntheticFFTButterflyInt s P0 P1).1
      (syntheticFFTButterflyInt s P0 P1).2).1 m = 2 * P0 m := by
  simp only [syntheticIFFTButterflyInt, syntheticFFTButterflyInt, negacyclicAddInt, negacyclicSubInt]
  ring

/-- Negacyclic shift by `0` is the identity on `Fin r → ℤ`. -/
theorem negacyclicShiftInt_zero {r : ℕ} (P : Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt 0 P m = P m := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by have := m.isLt; omega)
  simp only [negacyclicShiftInt, Nat.zero_mod, Nat.sub_zero]
  have hdiv : (m.val + 2 * r) / r = m.val / r + 2 := by
    have := Nat.add_mul_div_right m.val 2 hr
    simpa [Nat.mul_comm] using this
  have hlt : m.val / r = 0 := Nat.div_eq_of_lt m.isLt
  have hpar : ((m.val + 2 * r) / r) % 2 = 0 := by omega
  have hmod : (m.val + 2 * r) % r = m.val := by
    have : m.val + 2 * r = m.val + r * 2 := by ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt m.isLt]
  simp [hpar, hmod]

/-- `negacyclicShiftInt` commutes with scalar multiplication over `ℤ`. -/
theorem negacyclicShiftInt_smul {r : ℕ} (s : ℕ) (c : ℤ) (P : Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt s (fun idx => c * P idx) m = c * negacyclicShiftInt s P m := by
  dsimp only [negacyclicShiftInt]
  split_ifs <;> ring

/-- **Exact Inversion of Negacyclic Monomial Shifts in `ℤ[y]/(y^r + 1)`**:
Shifting by `s` modulo `y^r + 1` followed by shifting by `2r - (s mod 2r)` recovers `P`
identically at every coefficient `m : Fin r`. -/
theorem negacyclicShiftInt_inv {r : ℕ} (s : ℕ) (P : Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt (2 * r - s % (2 * r)) (negacyclicShiftInt s P) m = P m := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by have := m.isLt; omega)
  have hm : m.val < r := m.isLt
  dsimp only [negacyclicShiftInt]
  set s1 := s % (2 * r)
  have hs1 : s1 < 2 * r := Nat.mod_lt s (by omega)
  set s2 := (2 * r - s1) % (2 * r)
  have hs2 : s2 < 2 * r := Nat.mod_lt (2 * r - s1) (by omega)
  set raw2 := m.val + 2 * r - s2
  set idx2 := raw2 % r
  have hidx2 : idx2 < r := Nat.mod_lt raw2 hr
  have hdiv2 : (raw2 / r) * r + idx2 = raw2 := Nat.div_add_mod' raw2 r
  set raw1 := idx2 + 2 * r - s1
  set idx1 := raw1 % r
  have hidx1 : idx1 < r := Nat.mod_lt raw1 hr
  have hdiv1 : (raw1 / r) * r + idx1 = raw1 := Nat.div_add_mod' raw1 r
  have hs12 : s1 + s2 = 0 ∨ s1 + s2 = 2 * r := by
    by_cases h0 : s1 = 0
    · left
      have : (2 * r - s1) % (2 * r) = 0 := by rw [h0, Nat.sub_zero, Nat.mod_self]
      omega
    · right
      have hlt : 2 * r - s1 < 2 * r := by omega
      have : (2 * r - s1) % (2 * r) = 2 * r - s1 := Nat.mod_eq_of_lt hlt
      omega
  have hsum : idx1 + r * (raw1 / r + raw2 / r) = m.val + 4 * r - (s1 + s2) := by
    have hlin : (raw1 / r) * r + idx1 + (raw2 / r) * r = idx1 + r * (raw1 / r + raw2 / r) := by ring
    omega
  have hidx1_eq : idx1 = m.val ∧ (raw1 / r + raw2 / r = 4 ∨ raw1 / r + raw2 / r = 2) := by
    rcases hs12 with hzero | h2r
    · have hsum0 : idx1 + r * (raw1 / r + raw2 / r) = m.val + r * 4 := by omega
      have hle : raw1 / r + raw2 / r ≤ 4 := by nlinarith
      have hge : 4 ≤ raw1 / r + raw2 / r := by nlinarith
      have hq : raw1 / r + raw2 / r = 4 := by omega
      refine ⟨?_, Or.inl hq⟩
      rw [hq] at hsum0
      omega
    · have hsum2 : idx1 + r * (raw1 / r + raw2 / r) = m.val + r * 2 := by omega
      have hle : raw1 / r + raw2 / r ≤ 2 := by nlinarith
      have hge : 2 ≤ raw1 / r + raw2 / r := by nlinarith
      have hq : raw1 / r + raw2 / r = 2 := by omega
      refine ⟨?_, Or.inr hq⟩
      rw [hq] at hsum2
      omega
  have hfin : (⟨idx1, hidx1⟩ : Fin r) = m := Fin.ext hidx1_eq.1
  have hpar : (raw2 / r) % 2 = 0 ↔ (raw1 / r) % 2 = 0 := by
    rcases hidx1_eq.2 with h4 | h2 <;> omega
  change (if (raw2 / r) % 2 = 0 then
      (if (raw1 / r) % 2 = 0 then P ⟨idx1, hidx1⟩ else -P ⟨idx1, hidx1⟩)
    else
      -(if (raw1 / r) % 2 = 0 then P ⟨idx1, hidx1⟩ else -P ⟨idx1, hidx1⟩)) = P m
  by_cases hp2 : (raw2 / r) % 2 = 0
  · have hp1 : (raw1 / r) % 2 = 0 := hpar.mp hp2
    simp [hp2, hp1, hfin]
  · have hp1 : ¬((raw1 / r) % 2 = 0) := fun h => hp2 (hpar.mpr h)
    simp [hp2, hp1, hfin]

/-- **Exact Second-Output Inversion of the Addition-Only Butterfly**:
For every shift `s` and every index `m`, the second output of `syntheticIFFTButterflyInt`
applied to `syntheticFFTButterflyInt s P0 P1` equals `2 * P1 m`. -/
theorem syntheticIFFTButterflyInt_snd_eq {r : ℕ} (s : ℕ) (P0 P1 : Fin r → ℤ) (m : Fin r) :
    (syntheticIFFTButterflyInt s
      (syntheticFFTButterflyInt s P0 P1).1
      (syntheticFFTButterflyInt s P0 P1).2).2 m = 2 * P1 m := by
  simp only [syntheticIFFTButterflyInt, syntheticFFTButterflyInt]
  have hdiff : negacyclicSubInt (negacyclicAddInt P0 (negacyclicShiftInt s P1))
      (negacyclicSubInt P0 (negacyclicShiftInt s P1)) =
      fun idx => 2 * negacyclicShiftInt s P1 idx := by
    ext idx
    simp only [negacyclicSubInt, negacyclicAddInt]
    ring
  rw [hdiff, negacyclicShiftInt_smul, negacyclicShiftInt_inv]

/-- **Full Pairwise Inversion of the Addition-Only Radix-2 Synthetic Butterfly**:
For any `r`, shift `s`, and polynomials `P0, P1 : Fin r → ℤ`, applying `syntheticFFTButterflyInt`
followed by `syntheticIFFTButterflyInt` returns `(2 • P0, 2 • P1)`. -/
theorem syntheticIFFTButterflyInt_eq {r : ℕ} (s : ℕ) (P0 P1 : Fin r → ℤ) :
    syntheticIFFTButterflyInt s
      (syntheticFFTButterflyInt s P0 P1).1
      (syntheticFFTButterflyInt s P0 P1).2 =
    (fun m => 2 * P0 m, fun m => 2 * P1 m) := by
  ext m
  · exact syntheticIFFTButterflyInt_fst_eq s P0 P1 m
  · exact syntheticIFFTButterflyInt_snd_eq s P0 P1 m

/-- Complete binary tree of length `t_1 = 2^k` over the negacyclic ring `ℤ[y]/(y^r + 1)`:
- `FFTVec r 0 = (Fin r → ℤ)` (1 ring element)
- `FFTVec r (k + 1) = FFTVec r k × FFTVec r k` (`2^{k+1}` ring elements). -/
def FFTVec (r : ℕ) : ℕ → Type
  | 0 => Fin r → ℤ
  | k + 1 => FFTVec r k × FFTVec r k

/-- Pointwise scalar multiplication of all `2^k` ring elements in `FFTVec r k` by `c : ℤ`. -/
def scaleFFTVec {r : ℕ} : (k : ℕ) → ℤ → FFTVec r k → FFTVec r k
  | 0, c, P => fun m => c * P m
  | k + 1, c, (X0, X1) => (scaleFFTVec k c X0, scaleFFTVec k c X1)

theorem scaleFFTVec_mul {r : ℕ} (k : ℕ) (a b : ℤ) (X : FFTVec r k) :
    scaleFFTVec k a (scaleFFTVec k b X) = scaleFFTVec k (a * b) X := by
  induction k with
  | zero =>
    funext m
    simp only [scaleFFTVec]
    ring
  | succ k ih =>
    rcases X with ⟨X0, X1⟩
    simp only [scaleFFTVec, ih]
    rfl

/-- Apply a parallel stage of `2^k` addition-only Radix-2 Synthetic FFT butterflies across two
half-vectors `X0, X1 : FFTVec r k` using twiddle shift schedule `tw : ℕ → ℕ`. -/
def butterflyStageFFTVec {r : ℕ} : (k : ℕ) → (ℕ → ℕ) → FFTVec r k → FFTVec r k →
    FFTVec r k × FFTVec r k
  | 0, tw, P0, P1 => syntheticFFTButterflyInt (tw 0) P0 P1
  | k + 1, tw, (X00, X01), (X10, X11) =>
    let B0 := butterflyStageFFTVec k (fun j => tw (2 * j)) X00 X10
    let B1 := butterflyStageFFTVec k (fun j => tw (2 * j + 1)) X01 X11
    ((B0.1, B1.1), (B0.2, B1.2))

/-- Apply a parallel stage of `2^k` addition-only Radix-2 Synthetic IFFT butterflies across two
half-vectors `Y0, Y1 : FFTVec r k` using twiddle shift schedule `tw : ℕ → ℕ`. -/
def ibutterflyStageFFTVec {r : ℕ} : (k : ℕ) → (ℕ → ℕ) → FFTVec r k → FFTVec r k →
    FFTVec r k × FFTVec r k
  | 0, tw, Q0, Q1 => syntheticIFFTButterflyInt (tw 0) Q0 Q1
  | k + 1, tw, (Y00, Y01), (Y10, Y11) =>
    let B0 := ibutterflyStageFFTVec k (fun j => tw (2 * j)) Y00 Y10
    let B1 := ibutterflyStageFFTVec k (fun j => tw (2 * j + 1)) Y01 Y11
    ((B0.1, B1.1), (B0.2, B1.2))

/-- `ibutterflyStageFFTVec` inverts `butterflyStageFFTVec` up to factor `2` for any depth `k`. -/
theorem ibutterflyStageFFTVec_inverts {r : ℕ} (k : ℕ) (tw : ℕ → ℕ) (X0 X1 : FFTVec r k) :
    ibutterflyStageFFTVec k tw
      (butterflyStageFFTVec k tw X0 X1).1
      (butterflyStageFFTVec k tw X0 X1).2 =
    (scaleFFTVec k 2 X0, scaleFFTVec k 2 X1) := by
  induction k generalizing tw with
  | zero =>
    exact syntheticIFFTButterflyInt_eq (tw 0) X0 X1
  | succ k ih =>
    rcases X0 with ⟨X00, X01⟩
    rcases X1 with ⟨X10, X11⟩
    dsimp only [butterflyStageFFTVec, ibutterflyStageFFTVec, scaleFFTVec]
    have h0 := ih (fun j => tw (2 * j)) X00 X10
    have h1 := ih (fun j => tw (2 * j + 1)) X01 X11
    have h0_1 := congrArg Prod.fst h0
    have h0_2 := congrArg Prod.snd h0
    have h1_1 := congrArg Prod.fst h1
    have h1_2 := congrArg Prod.snd h1
    rw [h0_1, h0_2, h1_1, h1_2]

/-- `ibutterflyStageFFTVec` commutes with `scaleFFTVec`. -/
theorem ibutterflyStageFFTVec_scale {r : ℕ} (k : ℕ) (c : ℤ) (tw : ℕ → ℕ) (Y0 Y1 : FFTVec r k) :
    ibutterflyStageFFTVec k tw (scaleFFTVec k c Y0) (scaleFFTVec k c Y1) =
    (scaleFFTVec k c (ibutterflyStageFFTVec k tw Y0 Y1).1,
     scaleFFTVec k c (ibutterflyStageFFTVec k tw Y0 Y1).2) := by
  induction k generalizing tw with
  | zero =>
    dsimp only [ibutterflyStageFFTVec, scaleFFTVec, syntheticIFFTButterflyInt]
    ext m
    · simp only [negacyclicAddInt]
      ring
    · dsimp only
      have hsub : negacyclicSubInt (fun m => c * Y0 m) (fun m => c * Y1 m) =
          fun m => c * negacyclicSubInt Y0 Y1 m := by
        ext idx
        simp only [negacyclicSubInt]
        ring
      rw [hsub, negacyclicShiftInt_smul]
  | succ k ih =>
    rcases Y0 with ⟨Y00, Y01⟩
    rcases Y1 with ⟨Y10, Y11⟩
    dsimp only [ibutterflyStageFFTVec, scaleFFTVec]
    have h0 := ih (fun j => tw (2 * j)) Y00 Y10
    have h1 := ih (fun j => tw (2 * j + 1)) Y01 Y11
    have h0_1 := congrArg Prod.fst h0
    have h0_2 := congrArg Prod.snd h0
    have h1_1 := congrArg Prod.fst h1
    have h1_2 := congrArg Prod.snd h1
    rw [h0_1, h0_2, h1_1, h1_2]

/-- Multi-stage recursive Radix-2 Synthetic FFT of depth `k` (`t_1 = 2^k` points) over `ℤ[y]/(y^r + 1)`:
recursively transforms the two half-vectors of length `2^{k-1}` and combines them with a parallel
stage of `2^{k-1}` addition-only Radix-2 Synthetic butterflies. -/
def syntheticFFTRadix2 {r : ℕ} : (k : ℕ) → (ℕ → ℕ → ℕ) → FFTVec r k → FFTVec r k
  | 0, _, P => P
  | k + 1, tw, (X0, X1) =>
    let Y0 := syntheticFFTRadix2 k (fun s j => tw s (2 * j)) X0
    let Y1 := syntheticFFTRadix2 k (fun s j => tw s (2 * j + 1)) X1
    butterflyStageFFTVec k (tw k) Y0 Y1

/-- Multi-stage recursive Radix-2 Inverse Synthetic FFT of depth `k` (`t_1 = 2^k` points) over `ℤ[y]/(y^r + 1)`:
undoes the outer stage of `2^{k-1}` addition-only Radix-2 Synthetic butterflies and recursively
inverts the two half-vectors of length `2^{k-1}`. -/
def syntheticIFFTRadix2 {r : ℕ} : (k : ℕ) → (ℕ → ℕ → ℕ) → FFTVec r k → FFTVec r k
  | 0, _, Q => Q
  | k + 1, tw, (Z0, Z1) =>
    let B := ibutterflyStageFFTVec k (tw k) Z0 Z1
    (syntheticIFFTRadix2 k (fun s j => tw s (2 * j)) B.1,
     syntheticIFFTRadix2 k (fun s j => tw s (2 * j + 1)) B.2)

/-- `syntheticIFFTRadix2` commutes with scalar multiplication `scaleFFTVec`. -/
theorem syntheticIFFTRadix2_scale {r : ℕ} (k : ℕ) (c : ℤ) (tw : ℕ → ℕ → ℕ) (Z : FFTVec r k) :
    syntheticIFFTRadix2 k tw (scaleFFTVec k c Z) =
      scaleFFTVec k c (syntheticIFFTRadix2 k tw Z) := by
  induction k generalizing tw with
  | zero => rfl
  | succ k ih =>
    rcases Z with ⟨Z0, Z1⟩
    dsimp only [syntheticIFFTRadix2, scaleFFTVec]
    have hstage := ibutterflyStageFFTVec_scale k c (tw k) Z0 Z1
    have hs1 := congrArg Prod.fst hstage
    have hs2 := congrArg Prod.snd hstage
    rw [hs1, hs2, ih, ih]

/-- **Multi-Stage Recursive Radix-2 Synthetic FFT Exact Inversion Theorem**:
For any recursion depth `k ∈ ℕ` (`t_1 = 2^k`), any ring degree `r`, and any synthetic twiddle
shift schedule `tw : ℕ → ℕ → ℕ`, the addition-only multi-stage `syntheticIFFTRadix2 k tw`
inverts `syntheticFFTRadix2 k tw` up to the exact scale factor `2^k`. -/
theorem syntheticIFFTRadix2_inverts_syntheticFFTRadix2 {r : ℕ} (k : ℕ)
    (tw : ℕ → ℕ → ℕ) (X : FFTVec r k) :
    syntheticIFFTRadix2 k tw (syntheticFFTRadix2 k tw X) =
      scaleFFTVec k ((2 : ℤ) ^ k) X := by
  induction k generalizing tw with
  | zero =>
    funext m
    simp [syntheticFFTRadix2, syntheticIFFTRadix2, scaleFFTVec]
  | succ k ih =>
    rcases X with ⟨X0, X1⟩
    dsimp only [syntheticFFTRadix2, syntheticIFFTRadix2]
    have hstage := ibutterflyStageFFTVec_inverts k (tw k)
      (syntheticFFTRadix2 k (fun s j => tw s (2 * j)) X0)
      (syntheticFFTRadix2 k (fun s j => tw s (2 * j + 1)) X1)
    have hs1 := congrArg Prod.fst hstage
    have hs2 := congrArg Prod.snd hstage
    rw [hs1, hs2, syntheticIFFTRadix2_scale, syntheticIFFTRadix2_scale, ih, ih]
    dsimp only [scaleFFTVec]
    rw [scaleFFTVec_mul, scaleFFTVec_mul, pow_succ']

/-- Instrumented single Radix-2 Synthetic FFT butterfly over `ℤ[y]/(y^r + 1)`, returning
`(out0, out1)` together with `(addOps, mulOps) = (2 * r, 0)` (since `negacyclicAddInt` and
`negacyclicSubInt` each perform `r` integer additions/subtractions and `0` multiplications). -/
def syntheticFFTButterflyIntWithCost {r : ℕ} (s : ℕ) (P0 P1 : Fin r → ℤ) :
    ((Fin r → ℤ) × (Fin r → ℤ)) × (ℕ × ℕ) :=
  (syntheticFFTButterflyInt s P0 P1, (2 * r, 0))

/-- Instrumented parallel stage of `2^k` addition-only Radix-2 Synthetic FFT butterflies,
accumulating the exact `(addOps, mulOps)` counts across both half-trees. -/
def butterflyStageFFTVecWithCost {r : ℕ} :
    (k : ℕ) → (ℕ → ℕ) → FFTVec r k → FFTVec r k → (FFTVec r k × FFTVec r k) × (ℕ × ℕ)
  | 0, tw, P0, P1 => syntheticFFTButterflyIntWithCost (tw 0) P0 P1
  | k + 1, tw, (X00, X01), (X10, X11) =>
    let B0 := butterflyStageFFTVecWithCost k (fun j => tw (2 * j)) X00 X10
    let B1 := butterflyStageFFTVecWithCost k (fun j => tw (2 * j + 1)) X01 X11
    (((B0.1.1, B1.1.1), (B0.1.2, B1.1.2)), (B0.2.1 + B1.2.1, B0.2.2 + B1.2.2))

/-- Instrumented `k`-stage recursive Radix-2 Synthetic FFT over `ℤ[y]/(y^r + 1)`,
accumulating the exact `(addOps, mulOps)` counts of the two recursive half-transforms and the
butterfly combine stage. -/
def syntheticFFTRadix2WithCost {r : ℕ} :
    (k : ℕ) → (ℕ → ℕ → ℕ) → FFTVec r k → FFTVec r k × (ℕ × ℕ)
  | 0, _, P => (P, (0, 0))
  | k + 1, tw, (X0, X1) =>
    let R0 := syntheticFFTRadix2WithCost k (fun s j => tw s (2 * j)) X0
    let R1 := syntheticFFTRadix2WithCost k (fun s j => tw s (2 * j + 1)) X1
    let B := butterflyStageFFTVecWithCost k (tw k) R0.1 R1.1
    (B.1, (R0.2.1 + R1.2.1 + B.2.1, R0.2.2 + R1.2.2 + B.2.2))

/-- **Exact Output and Operation Count of `butterflyStageFFTVecWithCost`**:
For any depth `k`, `butterflyStageFFTVecWithCost k tw X0 X1` returns the exact butterfly stage
output `butterflyStageFFTVec k tw X0 X1` together with `(2^k * (2 * r), 0)` operations. -/
theorem butterflyStageFFTVecWithCost_eq {r : ℕ} (k : ℕ) (tw : ℕ → ℕ) (X0 X1 : FFTVec r k) :
    butterflyStageFFTVecWithCost k tw X0 X1 =
      (butterflyStageFFTVec k tw X0 X1, (2 ^ k * (2 * r), 0)) := by
  induction k generalizing tw with
  | zero =>
    simp [butterflyStageFFTVecWithCost, syntheticFFTButterflyIntWithCost, butterflyStageFFTVec]
    rfl
  | succ k ih =>
    rcases X0 with ⟨X00, X01⟩
    rcases X1 with ⟨X10, X11⟩
    dsimp only [butterflyStageFFTVecWithCost, butterflyStageFFTVec]
    rw [ih (fun j => tw (2 * j)) X00 X10, ih (fun j => tw (2 * j + 1)) X01 X11]
    dsimp only
    congr 1
    exact Prod.ext (by rw [pow_succ']; ring) rfl

/-- **Exact Output and Recurrence Operation Count of `syntheticFFTRadix2WithCost`**:
For any recursion depth `k`, `syntheticFFTRadix2WithCost k tw X` computes the exact output
`syntheticFFTRadix2 k tw X` and accumulates
`(syntheticFFTRadix2AddOps r k, syntheticFFTRadix2MulOps r k)` operations. -/
theorem syntheticFFTRadix2WithCost_eq {r : ℕ} (k : ℕ) (tw : ℕ → ℕ → ℕ) (X : FFTVec r k) :
    syntheticFFTRadix2WithCost k tw X =
      (syntheticFFTRadix2 k tw X,
       (syntheticFFTRadix2AddOps r k, syntheticFFTRadix2MulOps r k)) := by
  induction k generalizing tw with
  | zero =>
    rfl
  | succ k ih =>
    rcases X with ⟨X0, X1⟩
    dsimp only [syntheticFFTRadix2WithCost, syntheticFFTRadix2,
      syntheticFFTRadix2AddOps, syntheticFFTRadix2MulOps]
    rw [ih (fun s j => tw s (2 * j)) X0, ih (fun s j => tw s (2 * j + 1)) X1]
    dsimp only
    rw [butterflyStageFFTVecWithCost_eq]
    dsimp only
    congr 1
    exact Prod.ext (by ring) (by ring)

/-- **Closed-Form Operation Counts of Instrumented `syntheticFFTRadix2WithCost`**:
For any ring degree `r` and stage count `k` (`t_1 = 2^k`), the instrumented executable
`syntheticFFTRadix2WithCost k tw X` returns `syntheticFFTRadix2 k tw X` and performs
`k * (2^k * r)` integer additions/subtractions and `0` multiplications. -/
theorem syntheticFFTRadix2WithCost_closed_form {r : ℕ} (k : ℕ) (tw : ℕ → ℕ → ℕ) (X : FFTVec r k) :
    (syntheticFFTRadix2WithCost k tw X).1 = syntheticFFTRadix2 k tw X ∧
    (syntheticFFTRadix2WithCost k tw X).2 = (k * (2 ^ k * r), 0) := by
  rw [syntheticFFTRadix2WithCost_eq]
  have hclosed := syntheticFFTRadix2Ops_closed_form r k
  refine ⟨rfl, ?_⟩
  dsimp only
  rw [hclosed.1, hclosed.2.1]

/-- `negacyclicShiftInt` is additive over `Fin r → ℤ`. -/
theorem negacyclicShiftInt_add {r : ℕ} (s : ℕ) (P Q : Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt s (negacyclicAddInt P Q) m =
      negacyclicAddInt (negacyclicShiftInt s P) (negacyclicShiftInt s Q) m := by
  dsimp only [negacyclicShiftInt, negacyclicAddInt]
  split_ifs <;> ring

/-- `negacyclicShiftInt` commutes with finite sums over `ℤ`. -/
theorem negacyclicShiftInt_sum {ι : Type*} {r : ℕ} (s : ℕ) (S : Finset ι)
    (f : ι → Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt s (fun idx => ∑ i ∈ S, f i idx) m =
      ∑ i ∈ S, negacyclicShiftInt s (f i) m := by
  induction S using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    have := negacyclicShiftInt_smul s 0 (fun _ => 0) m
    simpa using this
  | cons a S ha ih =>
    simp only [Finset.sum_cons]
    have hadd := negacyclicShiftInt_add s (f a) (fun idx => ∑ i ∈ S, f i idx) m
    unfold negacyclicAddInt at hadd
    rw [hadd, ih]

/-- Euclidean division uniqueness helper: if `a < r`, `b < r`, and `a + r * q1 = b + r * q2`,
then `a = b` and `q1 = q2`. -/
theorem nat_eq_and_quo_eq_of_add_mul_eq {r a b q1 q2 : ℕ} (ha : a < r) (hb : b < r)
    (h : a + r * q1 = b + r * q2) : a = b ∧ q1 = q2 := by
  have hr : 0 < r := by omega
  have hmod : (a + r * q1) % r = (b + r * q2) % r := congrArg (· % r) h
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  refine ⟨hmod, ?_⟩
  subst hmod
  exact Nat.eq_of_mul_eq_mul_left hr (by omega)

/-- **Semigroup Law for `negacyclicShiftInt` in `ℤ[y]/(y^r + 1)`**:
Shifting by `s1 + s2` modulo `y^r + 1` equals shifting by `s2` followed by shifting by `s1`. -/
theorem negacyclicShiftInt_add_steps {r : ℕ} (s1 s2 : ℕ) (P : Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt (s1 + s2) P m =
      negacyclicShiftInt s1 (negacyclicShiftInt s2 P) m := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by have := m.isLt; omega)
  have hm : m.val < r := m.isLt
  dsimp only [negacyclicShiftInt]
  set s1' := s1 % (2 * r)
  have hs1' : s1' < 2 * r := Nat.mod_lt s1 (by omega)
  set s2' := s2 % (2 * r)
  have hs2' : s2' < 2 * r := Nat.mod_lt s2 (by omega)
  set s12' := (s1 + s2) % (2 * r)
  have hs12' : s12' < 2 * r := Nat.mod_lt (s1 + s2) (by omega)
  set raw1 := m.val + 2 * r - s1'
  set idx1 := raw1 % r
  have hidx1 : idx1 < r := Nat.mod_lt raw1 hr
  have hdiv1 : (raw1 / r) * r + idx1 = raw1 := Nat.div_add_mod' raw1 r
  set raw2 := idx1 + 2 * r - s2'
  set idx2 := raw2 % r
  have hidx2 : idx2 < r := Nat.mod_lt raw2 hr
  have hdiv2 : (raw2 / r) * r + idx2 = raw2 := Nat.div_add_mod' raw2 r
  set raw12 := m.val + 2 * r - s12'
  set idx12 := raw12 % r
  have hidx12 : idx12 < r := Nat.mod_lt raw12 hr
  have hdiv12 : (raw12 / r) * r + idx12 = raw12 := Nat.div_add_mod' raw12 r
  have hs_mod_eq : s12' = (s1' + s2') % (2 * r) := Nat.add_mod s1 s2 (2 * r)
  have hs_cases : s1' + s2' = s12' ∨ s1' + s2' = s12' + 2 * r := by
    by_cases hlt : s1' + s2' < 2 * r
    · left
      rw [hs_mod_eq, Nat.mod_eq_of_lt hlt]
    · right
      have hlt2 : s1' + s2' - 2 * r < 2 * r := by omega
      have hmod2 : (s1' + s2') % (2 * r) = s1' + s2' - 2 * r := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
      omega
  have hsum2 : idx2 + r * (raw1 / r + raw2 / r) = m.val + 4 * r - (s1' + s2') := by
    have hlin : (raw2 / r) * r + idx2 + (raw1 / r) * r = idx2 + r * (raw1 / r + raw2 / r) := by ring
    omega
  have hidx_and_par : idx12 = idx2 ∧ ((raw12 / r) % 2 = 0 ↔ ((raw1 / r) % 2 = 0 ↔ (raw2 / r) % 2 = 0)) := by
    rcases hs_cases with heq | heq2
    · have hcomb : idx12 + r * (raw12 / r + 2) = idx2 + r * (raw1 / r + raw2 / r) := by
        have hlin : (raw12 / r) * r + idx12 + 2 * r = idx12 + r * (raw12 / r + 2) := by ring
        omega
      rcases nat_eq_and_quo_eq_of_add_mul_eq hidx12 hidx2 hcomb with ⟨hidx_eq, hq_eq⟩
      refine ⟨hidx_eq, by omega⟩
    · have hcomb : idx12 + r * (raw12 / r) = idx2 + r * (raw1 / r + raw2 / r) := by
        have hlin : (raw12 / r) * r + idx12 = idx12 + r * (raw12 / r) := by ring
        omega
      rcases nat_eq_and_quo_eq_of_add_mul_eq hidx12 hidx2 hcomb with ⟨hidx_eq, hq_eq⟩
      refine ⟨hidx_eq, by omega⟩
  have hfin : (⟨idx12, hidx12⟩ : Fin r) = ⟨idx2, hidx2⟩ := Fin.ext hidx_and_par.1
  change (if (raw12 / r) % 2 = 0 then P ⟨idx12, hidx12⟩ else -P ⟨idx12, hidx12⟩) =
    (if (raw1 / r) % 2 = 0 then
      (if (raw2 / r) % 2 = 0 then P ⟨idx2, hidx2⟩ else -P ⟨idx2, hidx2⟩)
    else
      -(if (raw2 / r) % 2 = 0 then P ⟨idx2, hidx2⟩ else -P ⟨idx2, hidx2⟩))
  rw [hfin]
  by_cases hp1 : (raw1 / r) % 2 = 0 <;> by_cases hp2 : (raw2 / r) % 2 = 0
  · have hp12 : (raw12 / r) % 2 = 0 := hidx_and_par.2.mpr (iff_of_true hp1 hp2)
    simp [hp1, hp2, hp12]
  · have hp12 : ¬((raw12 / r) % 2 = 0) := fun h => hp2 ((hidx_and_par.2.mp h).mp hp1)
    simp [hp1, hp2, hp12]
  · have hp12 : ¬((raw12 / r) % 2 = 0) := fun h => hp1 ((hidx_and_par.2.mp h).mpr hp2)
    simp [hp1, hp2, hp12]
  · have hp12 : (raw12 / r) % 2 = 0 := hidx_and_par.2.mpr (iff_of_false hp1 hp2)
    simp [hp1, hp2, hp12]

/-- Negacyclic shift by `r` negates every coefficient (`y^r ≡ -1 (mod y^r + 1)`). -/
theorem negacyclicShiftInt_r {r : ℕ} (P : Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt r P m = -P m := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by have := m.isLt; omega)
  dsimp only [negacyclicShiftInt]
  have hs : r % (2 * r) = r := Nat.mod_eq_of_lt (by omega)
  have hraw : m.val + 2 * r - r % (2 * r) = m.val + r * 1 := by omega
  have hdiv : (m.val + 2 * r - r % (2 * r)) / r = 1 := by
    rw [hraw, Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt m.isLt]
  have hmod : (m.val + 2 * r - r % (2 * r)) % r = m.val := by
    rw [hraw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt m.isLt]
  simp [hdiv, hmod]

/-- Negacyclic shift by `q * r` multiplies by `(-1)^q` (`y^{q r} ≡ (-1)^q (mod y^r + 1)`). -/
theorem negacyclicShiftInt_mul_r {r : ℕ} (q : ℕ) (P : Fin r → ℤ) (m : Fin r) :
    negacyclicShiftInt (q * r) P m = (-1 : ℤ) ^ q * P m := by
  induction q generalizing P m with
  | zero =>
    simp [negacyclicShiftInt_zero]
  | succ q ih =>
    have h : (q + 1) * r = r + q * r := by ring
    rw [h, negacyclicShiftInt_add_steps, negacyclicShiftInt_r, ih, pow_succ']
    ring

/-- Construct a binary tree `FFTVec r k` from an indexed family `P : ℕ → Fin r → ℤ`
by recursive even/odd decimation-in-time (`P (2 * j)` in the left subtree, `P (2 * j + 1)` in the right subtree). -/
def ofFnFFTVec {r : ℕ} : (k : ℕ) → (ℕ → Fin r → ℤ) → FFTVec r k
  | 0, P => P 0
  | k + 1, P =>
    (ofFnFFTVec k (fun j => P (2 * j)),
     ofFnFFTVec k (fun j => P (2 * j + 1)))

/-- Extract the `v`-th ring element (`0 ≤ v < 2^k`) from `FFTVec r k`. -/
def getFFTVec {r : ℕ} : (k : ℕ) → FFTVec r k → ℕ → Fin r → ℤ
  | 0, P, _ => P
  | k + 1, (X0, X1), v =>
    if v % 2 = 0 then getFFTVec k X0 (v / 2) else getFFTVec k X1 (v / 2)

/-- `k`-bit reversal of `v`: maps the tree path index `v < 2^k` in `getFFTVec k` to the
corresponding natural frequency index `u < 2^k`. -/
def bitRev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, v => bitRev k (v / 2) + 2 ^ k * (v % 2)

/-- Concrete Cooley-Tukey twiddle shift schedule for `syntheticFFTRadix2` at depth `K` and base stride `c1`. -/
def cooleyTukeyTwiddle (K c1 : ℕ) (s m : ℕ) : ℕ :=
  2 * (c1 * 2 ^ (K - 1 - s)) * bitRev s (m / 2 ^ (K - 1 - s))

/-- `syntheticFFTRadix2 k tw X` depends on `tw s j` only for stages `s < k`. -/
theorem syntheticFFTRadix2_congr_tw {r : ℕ} (k : ℕ) (tw1 tw2 : ℕ → ℕ → ℕ) (X : FFTVec r k)
    (htw : ∀ s < k, ∀ j, tw1 s j = tw2 s j) :
    syntheticFFTRadix2 k tw1 X = syntheticFFTRadix2 k tw2 X := by
  induction k generalizing tw1 tw2 with
  | zero => rfl
  | succ k ih =>
    rcases X with ⟨X0, X1⟩
    dsimp only [syntheticFFTRadix2]
    have h0 := ih (fun s j => tw1 s (2 * j)) (fun s j => tw2 s (2 * j)) X0
      (fun s hs j => htw s (Nat.lt_succ_of_lt hs) (2 * j))
    have h1 := ih (fun s j => tw1 s (2 * j + 1)) (fun s j => tw2 s (2 * j + 1)) X1
      (fun s hs j => htw s (Nat.lt_succ_of_lt hs) (2 * j + 1))
    have hk : tw1 k = tw2 k := funext (htw k (Nat.lt_succ_self k))
    rw [h0, h1, hk]

/-- For stages `s < k`, `cooleyTukeyTwiddle (k + 1) c1 s (2 * j)` restricts to `cooleyTukeyTwiddle k (2 * c1) s j`. -/
theorem cooleyTukeyTwiddle_even (k c1 s j : ℕ) (hs : s < k) :
    cooleyTukeyTwiddle (k + 1) c1 s (2 * j) = cooleyTukeyTwiddle k (2 * c1) s j := by
  unfold cooleyTukeyTwiddle
  have hsub : k + 1 - 1 - s = (k - 1 - s) + 1 := by omega
  rw [hsub, pow_succ']
  have hdiv : (2 * j) / (2 * 2 ^ (k - 1 - s)) = j / 2 ^ (k - 1 - s) :=
    Nat.mul_div_mul_left j (2 ^ (k - 1 - s)) zero_lt_two
  rw [hdiv]
  ring

/-- For stages `s < k`, `cooleyTukeyTwiddle (k + 1) c1 s (2 * j + 1)` restricts to `cooleyTukeyTwiddle k (2 * c1) s j`. -/
theorem cooleyTukeyTwiddle_odd (k c1 s j : ℕ) (hs : s < k) :
    cooleyTukeyTwiddle (k + 1) c1 s (2 * j + 1) = cooleyTukeyTwiddle k (2 * c1) s j := by
  unfold cooleyTukeyTwiddle
  have hsub : k + 1 - 1 - s = (k - 1 - s) + 1 := by omega
  rw [hsub, pow_succ']
  have hdiv : (2 * j + 1) / (2 * 2 ^ (k - 1 - s)) = j / 2 ^ (k - 1 - s) := by
    rw [← Nat.div_div_eq_div_mul]
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [h2]
  rw [hdiv]
  ring

/-- Accessing the first output of `butterflyStageFFTVec` at `v < 2^k` applies the `+` butterfly with twiddle `tw v`. -/
theorem getFFTVec_butterflyStageFFTVec_fst {r : ℕ} (k : ℕ) (tw : ℕ → ℕ)
    (Y0 Y1 : FFTVec r k) (v : ℕ) (hv : v < 2 ^ k) :
    getFFTVec k (butterflyStageFFTVec k tw Y0 Y1).1 v =
      (syntheticFFTButterflyInt (tw v) (getFFTVec k Y0 v) (getFFTVec k Y1 v)).1 := by
  induction k generalizing tw v with
  | zero =>
    have hv0 : v = 0 := by omega
    subst hv0
    rfl
  | succ k ih =>
    rcases Y0 with ⟨Y00, Y01⟩
    rcases Y1 with ⟨Y10, Y11⟩
    dsimp only [butterflyStageFFTVec, getFFTVec]
    have hv_div : v / 2 < 2 ^ k := by rw [pow_succ'] at hv; omega
    split_ifs with hmod
    · rw [ih (fun j => tw (2 * j)) Y00 Y10 (v / 2) hv_div]
      have h2 : 2 * (v / 2) = v := by omega
      rw [h2]
    · rw [ih (fun j => tw (2 * j + 1)) Y01 Y11 (v / 2) hv_div]
      have h2 : 2 * (v / 2) + 1 = v := by omega
      rw [h2]

/-- Accessing the second output of `butterflyStageFFTVec` at `v < 2^k` applies the `-` butterfly with twiddle `tw v`. -/
theorem getFFTVec_butterflyStageFFTVec_snd {r : ℕ} (k : ℕ) (tw : ℕ → ℕ)
    (Y0 Y1 : FFTVec r k) (v : ℕ) (hv : v < 2 ^ k) :
    getFFTVec k (butterflyStageFFTVec k tw Y0 Y1).2 v =
      (syntheticFFTButterflyInt (tw v) (getFFTVec k Y0 v) (getFFTVec k Y1 v)).2 := by
  induction k generalizing tw v with
  | zero =>
    have hv0 : v = 0 := by omega
    subst hv0
    rfl
  | succ k ih =>
    rcases Y0 with ⟨Y00, Y01⟩
    rcases Y1 with ⟨Y10, Y11⟩
    dsimp only [butterflyStageFFTVec, getFFTVec]
    have hv_div : v / 2 < 2 ^ k := by rw [pow_succ'] at hv; omega
    split_ifs with hmod
    · rw [ih (fun j => tw (2 * j)) Y00 Y10 (v / 2) hv_div]
      have h2 : 2 * (v / 2) = v := by omega
      rw [h2]
    · rw [ih (fun j => tw (2 * j + 1)) Y01 Y11 (v / 2) hv_div]
      have h2 : 2 * (v / 2) + 1 = v := by omega
      rw [h2]

/-- **Multi-Stage Radix-2 Synthetic FFT Equivalence over `ℤ[y]/(y^r + 1)`**:
When `c1 * 2 ^ k = r`, running the executable `k`-stage addition-only Radix-2 Cooley-Tukey
transform `syntheticFFTRadix2 k (cooleyTukeyTwiddle k c1) (ofFnFFTVec k P)` computes the
exact unnormalized Synthetic DFT sum `∑_{j_1 < 2^k} y^{2 c_1 j_1 u} P(j_1) mod (y^r + 1)`
at every frequency `u = bitRev k v` (`v < 2^k`). -/
theorem syntheticFFTRadix2_eq_direct {r : ℕ} (k c1 : ℕ) (hc1 : c1 * 2 ^ k = r)
    (P : ℕ → Fin r → ℤ) (v : ℕ) (hv : v < 2 ^ k) (m : Fin r) :
    getFFTVec k (syntheticFFTRadix2 k (cooleyTukeyTwiddle k c1) (ofFnFFTVec k P)) v m =
      ∑ j1 ∈ Finset.range (2 ^ k),
        negacyclicShiftInt (2 * c1 * j1 * bitRev k v) (P j1) m := by
  induction k generalizing c1 P v m with
  | zero =>
    simp [ofFnFFTVec, syntheticFFTRadix2, getFFTVec, bitRev, negacyclicShiftInt_zero]
  | succ k ih =>
    dsimp only [ofFnFFTVec, syntheticFFTRadix2, getFFTVec]
    have hc1' : (2 * c1) * 2 ^ k = r := by
      calc (2 * c1) * 2 ^ k = c1 * (2 * 2 ^ k) := by ring
        _ = c1 * 2 ^ (k + 1) := by rw [← pow_succ']
        _ = r := hc1
    have hv_div : v / 2 < 2 ^ k := by rw [pow_succ'] at hv; omega
    have htw0 := syntheticFFTRadix2_congr_tw k
      (fun s j => cooleyTukeyTwiddle (k + 1) c1 s (2 * j))
      (cooleyTukeyTwiddle k (2 * c1))
      (ofFnFFTVec k (fun j => P (2 * j)))
      (fun s hs j => cooleyTukeyTwiddle_even k c1 s j hs)
    have htw1 := syntheticFFTRadix2_congr_tw k
      (fun s j => cooleyTukeyTwiddle (k + 1) c1 s (2 * j + 1))
      (cooleyTukeyTwiddle k (2 * c1))
      (ofFnFFTVec k (fun j => P (2 * j + 1)))
      (fun s hs j => cooleyTukeyTwiddle_odd k c1 s j hs)
    rw [htw0, htw1]
    set Y0 := syntheticFFTRadix2 k (cooleyTukeyTwiddle k (2 * c1)) (ofFnFFTVec k (fun j => P (2 * j)))
    set Y1 := syntheticFFTRadix2 k (cooleyTukeyTwiddle k (2 * c1)) (ofFnFFTVec k (fun j => P (2 * j + 1)))
    set u := bitRev k (v / 2)
    have htw_k : cooleyTukeyTwiddle (k + 1) c1 k (v / 2) = 2 * c1 * u := by
      unfold cooleyTukeyTwiddle
      have hsub : k + 1 - 1 - k = 0 := by omega
      rw [hsub, pow_zero, mul_one, Nat.div_one]
    have hY0 : getFFTVec k Y0 (v / 2) m =
        ∑ j ∈ Finset.range (2 ^ k),
          negacyclicShiftInt (2 * c1 * (2 * j) * u) (P (2 * j)) m := by
      rw [ih (2 * c1) hc1' (fun j => P (2 * j)) (v / 2) hv_div m]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hexp : 2 * (2 * c1) * j * u = 2 * c1 * (2 * j) * u := by ring
      rw [hexp]
    have hY1_fun : getFFTVec k Y1 (v / 2) =
        fun idx => ∑ j ∈ Finset.range (2 ^ k),
          negacyclicShiftInt (2 * (2 * c1) * j * u) (P (2 * j + 1)) idx := by
      funext idx
      exact ih (2 * c1) hc1' (fun j => P (2 * j + 1)) (v / 2) hv_div idx
    have hY1 : negacyclicShiftInt (2 * c1 * u) (getFFTVec k Y1 (v / 2)) m =
        ∑ j ∈ Finset.range (2 ^ k),
          negacyclicShiftInt (2 * c1 * (2 * j + 1) * u) (P (2 * j + 1)) m := by
      rw [hY1_fun, negacyclicShiftInt_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← negacyclicShiftInt_add_steps]
      have hexp : 2 * c1 * u + 2 * (2 * c1) * j * u = 2 * c1 * (2 * j + 1) * u := by ring
      rw [hexp]
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    split_ifs with hmod
    · rw [getFFTVec_butterflyStageFFTVec_fst k (cooleyTukeyTwiddle (k + 1) c1 k) Y0 Y1 (v / 2) hv_div]
      dsimp only [syntheticFFTButterflyInt, negacyclicAddInt]
      have hbit : bitRev (k + 1) v = u := by
        dsimp [bitRev]
        rw [hmod, mul_zero, add_zero]
      rw [htw_k, hY0, hY1, hbit, hpow,
          sum_range_two_mul_even_odd (2 ^ k)
            (fun j1 => negacyclicShiftInt (2 * c1 * j1 * u) (P j1) m)]
    · rw [getFFTVec_butterflyStageFFTVec_snd k (cooleyTukeyTwiddle (k + 1) c1 k) Y0 Y1 (v / 2) hv_div]
      dsimp only [syntheticFFTButterflyInt, negacyclicSubInt]
      have hmod1 : v % 2 = 1 := by omega
      have hbit : bitRev (k + 1) v = u + 2 ^ k := by
        dsimp [bitRev]
        rw [hmod1, mul_one]
      rw [htw_k, hY0, hY1, hbit, hpow,
          sum_range_two_mul_even_odd (2 ^ k)
            (fun j1 => negacyclicShiftInt (2 * c1 * j1 * (u + 2 ^ k)) (P j1) m)]
      have heven_eq :
          (∑ j ∈ Finset.range (2 ^ k),
            negacyclicShiftInt (2 * c1 * (2 * j) * (u + 2 ^ k)) (P (2 * j)) m) =
          ∑ j ∈ Finset.range (2 ^ k),
            negacyclicShiftInt (2 * c1 * (2 * j) * u) (P (2 * j)) m := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hexp : 2 * c1 * (2 * j) * (u + 2 ^ k) =
            (2 * j) * r + 2 * c1 * (2 * j) * u := by
          calc 2 * c1 * (2 * j) * (u + 2 ^ k)
              = (2 * j) * ((2 * c1) * 2 ^ k) + 2 * c1 * (2 * j) * u := by ring
            _ = (2 * j) * r + 2 * c1 * (2 * j) * u := by rw [hc1']
        rw [hexp, negacyclicShiftInt_add_steps, negacyclicShiftInt_mul_r]
        have hpow_even : (-1 : ℤ) ^ (2 * j) = 1 := by
          rw [pow_mul, neg_one_sq, one_pow]
        rw [hpow_even, one_mul]
      have hodd_eq :
          (∑ j ∈ Finset.range (2 ^ k),
            negacyclicShiftInt (2 * c1 * (2 * j + 1) * (u + 2 ^ k)) (P (2 * j + 1)) m) =
          -(∑ j ∈ Finset.range (2 ^ k),
            negacyclicShiftInt (2 * c1 * (2 * j + 1) * u) (P (2 * j + 1)) m) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hexp : 2 * c1 * (2 * j + 1) * (u + 2 ^ k) =
            (2 * j + 1) * r + 2 * c1 * (2 * j + 1) * u := by
          calc 2 * c1 * (2 * j + 1) * (u + 2 ^ k)
              = (2 * j + 1) * ((2 * c1) * 2 ^ k) + 2 * c1 * (2 * j + 1) * u := by ring
            _ = (2 * j + 1) * r + 2 * c1 * (2 * j + 1) * u := by rw [hc1']
        rw [hexp, negacyclicShiftInt_add_steps, negacyclicShiftInt_mul_r]
        have hpow_odd : (-1 : ℤ) ^ (2 * j + 1) = -1 := by
          rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
        rw [hpow_odd, neg_one_mul]
      rw [heven_eq, hodd_eq]
      ring

/-! ## 3. Executable Signed Two's-Complement Kronecker Convolution & Cyclic Overlap-Add (`[MS]` §6.2)

Note: `polyMulKroneckerSigned`, `polyMulKroneckerSignedH`, `listMaxNatAbs`, `kroneckerHeadroom`,
`kroneckerBitStride`, and `overlapAddCyclic` are defined in `IntMul/Theorem4KroneckerSpread.lean`. -/

/-- Convert a list of non-negative `ℤ` coefficients to `List ℕ` and reconstruct via
carry propagation in base `2^b`. -/
def reconstructFromIntCoeffs (b : ℕ) (cs : List ℤ) : ℕ :=
  reconstructChunks b (cs.map Int.toNat)

/-- Executable end-to-end integer multiplication pipeline using radix-`2^b` chunking,
Signed Two's-Complement Kronecker polynomial convolution, cyclic overlap-add folding,
and carry-propagating reconstruction. -/
def kroneckerCyclicIntMul (b R q : ℕ) (A B : ℕ) : ℕ :=
  let aChunks := (splitChunks b R A).map Int.ofNat
  let bChunks := (splitChunks b R B).map Int.ofNat
  let acyclic := polyMulKroneckerSigned q aChunks bChunks
  let cyclic := overlapAddCyclic R acyclic
  reconstructFromIntCoeffs b cyclic

/-! ## 4. Machine-Checked Executable Verification Suite (`decide` / `rfl`) -/

/-- **Test 1 (Chunking & Carry-Propagating Reconstruction)**:
Splitting `A = 0x123456789ABCDEF0` into `R = 8` chunks of `b = 8` bits and reconstructing
recovers `A` identically. -/
theorem test_chunk_split_reconstruct :
    reconstructChunks 8 (splitChunks 8 8 0x123456789ABCDEF0) = 0x123456789ABCDEF0 := by
  decide

/-- **Test 2 (Signed Two's-Complement Kronecker Polynomial Multiplication with Negative Coefficients)**:
Verify that `polyMulKroneckerSigned 16 [3, -5, 7, -2] [4, 6, -3, 5]` computes the exact
acyclic product over `ℤ[X]` (where negative intermediate coefficients borrow across the
`2^{16}` two's-complement boundaries and are losslessly recovered). -/
theorem test_signed_kronecker_negative_poly_mul :
    polyMulKroneckerSigned 16 [3, -5, 7, -2] [4, 6, -3, 5] =
      [12, -2, -11, 64, -58, 41, -10] := by
  decide

/-- **Test 3 (Addition-Only Synthetic FFT Butterfly Inversion over `ℤ[y]/(y^4 + 1)`)**:
Verify that for `r = 4` and twiddle shift `s = 3`, applying `syntheticFFTButterflyInt` followed by
`syntheticIFFTButterflyInt` on `P0 = ![10, -20, 30, -40]` and `P1 = ![5, 15, -25, 35]`
recovers `(2 • P0, 2 • P1)` using purely additions, subtractions, and cyclic sign-flipped shifts. -/
theorem test_synthetic_fft_butterfly_inversion :
    let P0 : Fin 4 → ℤ := ![10, -20, 30, -40]
    let P1 : Fin 4 → ℤ := ![5, 15, -25, 35]
    let (Q0, Q1) := syntheticFFTButterflyInt 3 P0 P1
    let (R0, R1) := syntheticIFFTButterflyInt 3 Q0 Q1
    (List.ofFn R0, List.ofFn R1) = ([20, -40, 60, -80], [10, 30, -50, 70]) := by
  decide

/-- **Test 4 (Concrete 16-Chunk `kroneckerCyclicIntMul` Verification)**:
Verify exact integer multiplication for `A = 987654321012345` and `B = 123456789098765`
using `b = 12`-bit chunks, `R = 16` cyclic length, and `q = 32`-bit Kronecker stride. -/
theorem test_end_to_end_intmul :
    kroneckerCyclicIntMul 12 16 32 987654321012345 123456789098765 =
      987654321012345 * 123456789098765 := by
  decide

/-- **Test 5 (Concrete Parameter & Precision Schedule Verification, `[MS]` §6.3 & §7.1)**:
Verify the paper's parameter schedule rules for `n = 2^{34}` and `b = ⌊log_2 n⌋ = 34`:
- `N = ⌈2^{34} / 34⌉ = 505290271` and `2 N - 1 = 1010580541` (`2^{29} < 2 N - 1 ≤ 2^{30}`), so `K_0 = 30`,
- `p_0 = rootPrecision 34 30 = 134` bits (`2b + 2K_0 + 6 = 68 + 60 + 6 = 134`),
- `p_1 = pChild 134 30 = 206` bits (`134 + 2*30 + 12 = 206`),
- `K_1 = K_0 / 2 = 15` (`r_1 = 2^{15} = 32768 ≤ 4 * p_1^2 = 169744`, so the `4 p_ℓ^2` leaf rule stops at `L = 1`),
- `p_2 = pChild 206 15 = 248` bits (`206 + 2*15 + 12 = 248`). -/
theorem test_table1_precision_schedule :
    (2 ^ 34 + 33) / 34 = 505290271 ∧
    2 ^ 29 < 2 * 505290271 - 1 ∧
    2 * 505290271 - 1 ≤ 2 ^ 30 ∧
    rootPrecision 34 30 = 134 ∧
    pChild 134 30 = 206 ∧
    pChild 206 15 = 248 ∧
    2 ^ 15 ≤ 4 * 206 ^ 2 := by
  decide

/-- **Test 6 (Multi-Stage Recursive Radix-2 Synthetic FFT & IFFT over `ℤ[y]/(y^4 + 1)`, `k = 2`, `t_1 = 4`)**:
Verify that a 2-stage (`t_1 = 4`) recursive `syntheticFFTRadix2` followed by `syntheticIFFTRadix2`
with synthetic twiddle shifts `tw s j = s + 2 * j + 1` recovers `2^2 = 4` times every input
polynomial across all 4 ring slots. -/
theorem test_multistage_synthetic_fft_radix2 :
    let P00 : Fin 4 → ℤ := ![1, -2, 3, -4]
    let P01 : Fin 4 → ℤ := ![5, 6, -7, 8]
    let P10 : Fin 4 → ℤ := ![-9, 10, 11, -12]
    let P11 : Fin 4 → ℤ := ![13, -14, -15, 16]
    let X : FFTVec 4 2 := ((P00, P01), (P10, P11))
    let tw : ℕ → ℕ → ℕ := fun s j => s + 2 * j + 1
    let Y := syntheticIFFTRadix2 2 tw (syntheticFFTRadix2 2 tw X)
    (List.ofFn Y.1.1, List.ofFn Y.1.2, List.ofFn Y.2.1, List.ofFn Y.2.2) =
      ([4, -8, 12, -16], [20, 24, -28, 32], [-36, 40, 44, -48], [52, -56, -60, 64]) := by
  decide


end IntMul
