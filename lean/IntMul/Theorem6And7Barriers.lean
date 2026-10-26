import IntMul.Preliminaries
import IntMul.Theorem1TwistedDuality
import IntMul.Theorem3BidiagonalAndSchedule
import IntMul.Theorem5ComplexityAndCorrectness

/-!
# Structural Algebraic Identities and Restricted-Model Lower Bounds (Earlier `[MS]` Draft Barrier Discussion, Omitted in Current `[MS]`)

This module formalizes algebraic decompositions and restricted-model barrier statements from an earlier `[MS]` draft
(omitted in the current `[MS]`; historical Lean identifier prefixes `theorem6_*` and `theorem7_*` are retained for stability):

1. **Canonical Subring Decomposition of Radix-`B` Synthetic Butterflies (`theorem6_radixB_stage_eq_decoupled_MB`; omitted earlier `[MS]` draft barrier discussion)**:
   - Coset invariance: for `k_2 = m * d + β` (`0 ≤ β < d`), multiplying by `ω_B^{j u} = y^{d j u}`
     maps exponent `k_2` to `(m + j u) d + β`, preserving the residue `β = k_2 % d` modulo `d`.
   - Operator isomorphism (`negacyclicShiftIter_cosetExtract_eq` and
     `theorem6_radixB_stage_eq_decoupled_MB`): for even radix `B` (`(B / 2) * d = r` with `0 < B / 2`
     and `0 < d`, so `d = 2 r / B` when `B` is even), a single Radix-`B` Synthetic FFT stage
     `radixBSyntheticStage B r d P` over `R_r = ℂ[y]/(y^r + 1)` decomposes identically into `d`
     decoupled copies of the core radix-`B` operator `radixBMBOperator B` over
     `R_{B/2} = ℂ[z]/(z^{B/2} + 1)` acting on each `β`-coset `cosetExtract d β P`.
2. **Model-Specific Bit-Slice Linearity & Dynamic-Range Expansion for `M_B` (`theorem7_1_*`; omitted earlier `[MS]` draft barrier discussion)**:
   - *Model scope*: Linear radix-`2^s` bit-slicing of the integer operator `radixBMBOperatorInt` over
     `ℤ[z]/(z^{B/2} + 1)` (`theorem7_1_MB_bitSlice_linearity`), together with explicit extremal
     `s`-bit slice witnesses (`extremalSlice` at `u = 0` and `signedExtremalSlice` for arbitrary
     `u, m`) showing that `M_{2^k}` expands `s`-bit slices to `2^k (2^s - 1) ≥ 2^{s + k - 1}`
     (`theorem7_1_MB_extremal_witness`, `theorem7_1_MB_signed_extremal_witness`), and the arithmetic
     cost comparison under a linear-slicing cost model.
3. **Model-Specific Floyd Entropy Potential & 2-Register Packet Transposition Lower Bound (`theorem7_2_*`; omitted earlier `[MS]` draft barrier discussion)**:
   - *Model scope*: Floyd's two-register packet-routing model (`PacketMatrix B := Fin B → Fin B → ℕ`,
     initial state `initPacketMatrix B`, target transposed state `targetPacketMatrix B`, potential
     `floydMatrixPotential B a = ∑ i, ∑ j, floydPhi (a i j)`, and 2-register partition-and-merge step
     relation `ValidTwoRegStep B a a'`). Proves unconditionally within this 2-register packet model
     that every valid step increases `floydMatrixPotential` by at most `2 * B * log 2`
     (`theorem7_2_validTwoRegStep_potential_diff_le`) and any valid transposition trace for
     `B = 2^k` has length `trace.length ≥ k * 2^k / 2` (`theorem7_2_floyd_trace_lower_bound`).
4. **Model-Specific Bluestein Chirp Identity & Non-Shift-Invariance of Radix-`B` Exponents (`theorem7_3_*`; omitted earlier `[MS]` draft barrier discussion)**:
   - *Model scope*: Algebraic Bluestein chirp identity `2 j u = j^2 + u^2 - (u - j)^2`
     (`theorem7_3_bluestein_chirp_identity`), non-shift-invariance of the radix-`B` exponent table
     `(j, u) ↦ (j * u) % B` (`theorem7_3_exponent_not_shift_invariant`), and cost comparison under
     prescribed Kronecker-convolution and matrix-multiplication cost models.
5. **Model-Specific Recursive Chunk-Splitting Tree Work Identity & Leaf Blowup (`theorem7_4_*`; omitted earlier `[MS]` draft barrier discussion)**:
   - *Model scope*: Prescribed additive recurrence on an arbitrary-depth inductive schedule tree
     `ChunkSplitTree`, proving by structural induction that under the unit-expansion recurrence
     `transformWork`, total work telescopes to `c * T.bitLen * log (T.bitLen / T.leafBitLen)`
     (`theorem7_4_tree_transform_work_eq`), while acyclic zero-padding (`R ≥ 2 * (b / child.bitLen)`)
     spawns at least `2 ^ T.depth * (T.bitLen / T.leafBitLen)` leaf subproblems
     (`theorem7_4_tree_spawnedLeaves_ge`, `theorem7_4_tree_zeroPaddedWork_ge`).
6. **Exact Multiplicative Order `2r` in `R_r` & Schedule-Specific Ring-Divisibility Depth Bound (`theorem7_5_*`; omitted earlier `[MS]` draft barrier discussion)**:
   - *Model scope*: Unconditional algebraic proof that `y` has exact multiplicative order `2 * r` in
     `R_r = ℂ[y]/(y^r + 1)` (`negacyclicShiftIter_delta0_eval`,
     `theorem7_5_negacyclicShiftIter_exact_order_two_mul_r`), together with the depth lower bound
     `K 0 + 1 ≤ 2 ^ L * (K L + 1)` (`theorem7_5_admissible_schedule_depth_lower_bound`) for any
     schedule satisfying the `[MS]` §3.5 / Proposition 4.1 ring-divisibility condition
     `2 ^ (K ℓ - K (ℓ + 1)) ∣ 2 * 2 ^ (K (ℓ + 1))` (`AdmissibleRingSchedule`).
7. **Model-Specific Convolution Peak Witness, Quantizer Pigeonhole Bound & Modular Carry Sensitivity (`theorem7_6_*`; omitted earlier `[MS]` draft barrier discussion)**:
   - *Model scope*: Explicit max-digit chunk sequence `maxChunkSeq b N` achieving convolution peak
     `N * (2^b - 1)^2` at index `N - 1` (`theorem7_6_max_chunk_convolution_peak`), finite-set
     Pigeonhole bound (`Fintype.card_le_of_injective`) for any single-scalar quantizer injective on
     `[0, 2^{K_0 - 1} (2^b - 1)^2]` into `Fin (2 ^ (p + 2))`
     (`theorem7_6_precision_lower_bound_from_dynamic_range`), and boolean carry-propagation
     sensitivity of `W`-bit modular addition `addMod2Pow W`
     (`theorem7_6_packed_addition_sensitivity`).
-/

namespace IntMul

open scoped BigOperators
open Real

/-! ## 1. Canonical Subring Decomposition of Radix-`B` Synthetic Butterflies (Omitted Earlier `[MS]` Draft Barrier Discussion) -/

/-- **Radix-`B` Subring Decomposition (Part 1: `β`-Coset Invariance under Radix-`B` Monomial Shifts; omitted earlier `[MS]` draft)**:
For `d > 0` (`d = 2 r / B`) and any polynomial index `k_2 = α * d + β` with `β < d`, shifting the
exponent by `d * (m * v)` preserves the coset index `β` modulo `d`:
`((α * d + β) + d * (m * v)) % d = β`. -/
theorem theorem6_coset_invariance (d α β m v : ℕ) (hβ : β < d) :
    ((α * d + β) + d * (m * v)) % d = β := by
  have h1 : (α * d + β) + d * (m * v) = β + d * (α + m * v) := by ring
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hβ]

/-- **Radix-`B` Subring Decomposition (Part 2: Decoupled Intra-Butterfly Operator `M_B` over `R_{B/2}`; omitted earlier `[MS]` draft)**:
For `B_half = B / 2` and a single `β`-coset `x_coset : ℕ → ℕ → ℤ`, the decoupled radix-`B`
operator `M_B` evaluates output `(v, γ)` using only entries within the same `β`-coset. -/
def radixBSubringOp (B B_half : ℕ) (x_coset : ℕ → ℕ → ℤ) (v γ : ℕ) : ℤ :=
  ∑ m ∈ Finset.range B,
    let diff : ℤ := (γ : ℤ) - (m : ℤ) * (v : ℤ)
    let q : ℤ := diff / (B_half : ℤ)
    let rem : ℕ := (diff % (B_half : ℤ)).toNat
    (if q % 2 = 0 then 1 else -1) * x_coset m rem

/-- The core radix-`B` Synthetic FFT operator `M_B` over `R_{B/2} = ℂ[z]/(z^{B/2} + 1)` (`radixBMBOperator`; omitted earlier `[MS]` draft barrier discussion):
Given `B` input polynomials `A : ℕ → ℕ → ℂ` of degree `< B / 2`, evaluates output frequency `u < B`
at coefficient `m < B / 2` via `∑_{j < B} z^{j u} A_j(z) mod (z^{B/2} + 1)`. -/
noncomputable def radixBMBOperator (B : ℕ) (A : ℕ → ℕ → ℂ) (u m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range B, negacyclicShiftIter (B / 2) (j * u) (A j) m

/-- A single Radix-`B` Synthetic FFT butterfly stage over `R_r = ℂ[y]/(y^r + 1)` with stride `d`
(where `(B / 2) * d = r`, i.e., `d = 2 r / B` so `ω_B = y^d` has order `B` in `R_r`):
evaluates `∑_{j < B} y^{d j u} P_j(y) mod (y^r + 1)` at coefficient `k_2 < r`. -/
noncomputable def radixBSyntheticStage (B r d : ℕ) (P : ℕ → ℕ → ℂ) (u k2 : ℕ) : ℂ :=
  ∑ j ∈ Finset.range B, negacyclicShiftIter r (d * (j * u)) (P j) k2

/-- Extraction of the `β`-coset (`0 ≤ β < d`) from an array of polynomials `P : ℕ → ℕ → ℂ`
in `R_r = ℂ[y]/(y^r + 1)`, producing an array of polynomials in `R_{B/2} = ℂ[z]/(z^{B/2} + 1)`
via `A^{(\beta)}_j(m) = P_j(m * d + β)`. -/
def cosetExtract (d β : ℕ) (P : ℕ → ℕ → ℂ) (j m : ℕ) : ℂ :=
  P j (m * d + β)

/-- When the shift count `s` is at most the target index `k`, `negacyclicShiftIter r s f k`
simply shifts the index down by `s` without wrapping around `0`. -/
theorem negacyclicShiftIter_of_le (r s : ℕ) (f : ℕ → ℂ) (k : ℕ) (h : s ≤ k) :
    negacyclicShiftIter r s f k = f (k - s) := by
  induction s generalizing f k with
  | zero =>
    simp [negacyclicShiftIter]
  | succ s ih =>
    simp only [negacyclicShiftIter, Function.iterate_succ_apply']
    have hk : k ≠ 0 := by omega
    simp only [negacyclicShiftStep, hk, ↓reduceIte]
    have hs : s ≤ k - 1 := by omega
    have hsub := ih f (k - 1) hs
    unfold negacyclicShiftIter at hsub
    rw [hsub]
    congr 1
    omega

/-- When `β < d` and `d ≤ r`, shifting by `d` steps in `R_r` wraps around `0` exactly once,
negating the coefficient at index `r - d + β`. -/
theorem negacyclicShiftIter_of_lt_le (r d : ℕ) (f : ℕ → ℂ) (β : ℕ) (hβ : β < d) (hdr : d ≤ r) :
    negacyclicShiftIter r d f β = -f (r - d + β) := by
  have hd_eq : d = β + (1 + (d - 1 - β)) := by omega
  rw [hd_eq, negacyclicShiftIter_add_steps,
      negacyclicShiftIter_of_le r β _ β (le_refl β), Nat.sub_self,
      negacyclicShiftIter_add_steps]
  simp only [negacyclicShiftIter, Function.iterate_one, negacyclicShiftStep, ↓reduceIte]
  have hle : d - 1 - β ≤ r - 1 := by omega
  have hsub := negacyclicShiftIter_of_le r (d - 1 - β) f (r - 1) hle
  unfold negacyclicShiftIter at hsub
  rw [hsub]
  congr 2
  omega

/-- Single-stride (`s = 1`) coset shift lemma: when `(B / 2) * d = r`, shifting by `d` in `R_r`
at index `m * d + β` (`m < B / 2`, `β < d`) equals a single step `negacyclicShiftStep (B / 2)`
on the extracted `β`-coset `fun m' => f (m' * d + β)` at index `m`. -/
theorem negacyclicShiftIter_d_coset
    (B r d β : ℕ) (hB : 0 < B / 2) (_hd : 0 < d) (hr : (B / 2) * d = r) (hβ : β < d)
    (f : ℕ → ℂ) (m : ℕ) (_hm : m < B / 2) :
    negacyclicShiftIter r d f (m * d + β) =
      negacyclicShiftStep (B / 2) (fun m' => f (m' * d + β)) m := by
  by_cases hm0 : m = 0
  · subst hm0
    simp only [zero_mul, zero_add, negacyclicShiftStep, ↓reduceIte]
    have hdr : d ≤ r := by
      rw [← hr]
      exact Nat.le_mul_of_pos_left d hB
    rw [negacyclicShiftIter_of_lt_le r d f β hβ hdr]
    congr 2
    have hmul : (B / 2 - 1) * d + d = r := by
      rw [← hr]
      cases h : B / 2 with
      | zero => omega
      | succ n =>
        simp only [Nat.add_sub_cancel]
        ring
    omega
  · simp only [negacyclicShiftStep, hm0, ↓reduceIte]
    have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm0
    have hle : d ≤ m * d + β := by
      have : 1 * d ≤ m * d := Nat.mul_le_mul_right d hm_pos
      omega
    rw [negacyclicShiftIter_of_le r d f (m * d + β) hle]
    congr 1
    have hmul : (m - 1) * d + d = m * d := by
      cases m with
      | zero => contradiction
      | succ n =>
        simp only [Nat.add_sub_cancel]
        ring
    omega

/-- Congruence of `negacyclicShiftStep M` for functions agreeing on `0 .. M - 1`. -/
theorem negacyclicShiftStep_congr_lt
    (M : ℕ) (hM : 0 < M) (g1 g2 : ℕ → ℂ) (hg : ∀ m' < M, g1 m' = g2 m')
    (m : ℕ) (hm : m < M) :
    negacyclicShiftStep M g1 m = negacyclicShiftStep M g2 m := by
  unfold negacyclicShiftStep
  split_ifs with hm0
  · rw [hg (M - 1) (by omega)]
  · rw [hg (m - 1) (by omega)]

/-- **Key Algebraic Coset-Extraction Lemma (`negacyclicShiftIter_cosetExtract_eq`; omitted earlier `[MS]` draft barrier discussion)**:
When `0 < B / 2`, `0 < d`, `(B / 2) * d = r`, `β < d`, and `m < B / 2`, shifting any polynomial
`f : ℕ → ℂ` by `d * s` in `R_r = ℂ[y]/(y^r + 1)` and evaluating at `m * d + β` is identical to
extracting the `β`-coset `m' ↦ f (m' * d + β)` and shifting by `s` in `R_{B/2} = ℂ[z]/(z^{B/2} + 1)`. -/
theorem negacyclicShiftIter_cosetExtract_eq
    (B r d β s : ℕ) (hB : 0 < B / 2) (hd : 0 < d) (hr : (B / 2) * d = r) (hβ : β < d)
    (f : ℕ → ℂ) (m : ℕ) (hm : m < B / 2) :
    negacyclicShiftIter r (d * s) f (m * d + β) =
      negacyclicShiftIter (B / 2) s (fun m' => f (m' * d + β)) m := by
  induction s generalizing m with
  | zero =>
    simp [negacyclicShiftIter]
  | succ s ih =>
    have hds : d * (s + 1) = d + d * s := by ring
    rw [hds, negacyclicShiftIter_add_steps,
        negacyclicShiftIter_d_coset B r d β hB hd hr hβ (negacyclicShiftIter r (d * s) f) m hm]
    have hstep :
        negacyclicShiftIter (B / 2) (s + 1) (fun m' => f (m' * d + β)) m =
          negacyclicShiftStep (B / 2) (negacyclicShiftIter (B / 2) s (fun m' => f (m' * d + β))) m := by
      simp [negacyclicShiftIter, Function.iterate_succ_apply']
    rw [hstep]
    exact negacyclicShiftStep_congr_lt (B / 2) hB _ _ (fun m' hm' => ih m' hm') m hm

/-- **Substantive Operator Isomorphism of Radix-`B` Stage & `d` Decoupled `M_B` Copies (`theorem6_radixB_stage_eq_decoupled_MB`; omitted earlier `[MS]` draft)**:
When `(B / 2) * d = r` with `0 < B / 2` and `0 < d`:
1. For every `u`, `m < B / 2`, and `β < d`, `radixBSyntheticStage B r d P u (m * d + β)` equals
   `radixBMBOperator B (cosetExtract d β P) u m`.
2. Consequently, for every `k_2 < r`, `radixBSyntheticStage B r d P u k_2` is evaluated completely
   within the `(k_2 % d)`-coset at coordinate `k_2 / d < B / 2`. -/
theorem theorem6_radixB_stage_eq_decoupled_MB
    (B r d : ℕ) (hB : 0 < B / 2) (hd : 0 < d) (hr : (B / 2) * d = r)
    (P : ℕ → ℕ → ℂ) (u : ℕ) :
    (∀ m < B / 2, ∀ β < d,
      radixBSyntheticStage B r d P u (m * d + β) =
        radixBMBOperator B (cosetExtract d β P) u m) ∧
    (∀ k2 < r,
      radixBSyntheticStage B r d P u k2 =
        radixBMBOperator B (cosetExtract d (k2 % d) P) u (k2 / d)) := by
  have hpart1 : ∀ m < B / 2, ∀ β < d,
      radixBSyntheticStage B r d P u (m * d + β) =
        radixBMBOperator B (cosetExtract d β P) u m := by
    intro m hm β hβ
    unfold radixBSyntheticStage radixBMBOperator cosetExtract
    refine Finset.sum_congr rfl fun j _ => ?_
    exact negacyclicShiftIter_cosetExtract_eq B r d β (j * u) hB hd hr hβ (P j) m hm
  refine ⟨hpart1, ?_⟩
  intro k2 hk2
  have hβ : k2 % d < d := Nat.mod_lt k2 hd
  have hm : k2 / d < B / 2 := by
    rw [← hr, mul_comm] at hk2
    exact Nat.div_lt_of_lt_mul hk2
  have hk2_eq : (k2 / d) * d + k2 % d = k2 := Nat.div_add_mod' k2 d
  have h := hpart1 (k2 / d) hm (k2 % d) hβ
  rwa [hk2_eq] at h

/-! ## 2. Bit-Slice Output Expansion for `M_B` (Omitted Earlier `[MS]` Draft Barrier Discussion) -/

/-- **Bit-Slice Output Expansion (Part 1: Signed Sum Output Expansion by `k` Bits; omitted earlier `[MS]` draft)**:
Each row of `M_B` sums `B = 2^k` signed entries from `[-(2^s - 1), 2^s - 1]`, whose magnitude
is bounded by `2^k * (2^s - 1) < 2^{s + k}` and attains `2^k * (2^s - 1)` when all signs align. -/
theorem theorem7_1_bitslice_magnitude_expansion (k s : ℕ) :
    (2 ^ k : ℤ) * ((2 ^ s : ℤ) - 1) < (2 ^ (s + k) : ℤ) := by
  rw [pow_add]
  have hk : (0 : ℤ) < (2 ^ k : ℤ) := by positivity
  linarith

/-- Single-step negacyclic shift `f(z) ↦ z f(z) mod (z^M + 1)` over `ℤ`. -/
def negacyclicShiftStepInt (M : ℕ) (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  if m = 0 then -f (M - 1) else f (m - 1)

/-- `s`-step iterated negacyclic shift `f(z) ↦ z^s f(z) mod (z^M + 1)` over `ℤ`. -/
def negacyclicShiftIterInt (M s : ℕ) (f : ℕ → ℤ) : ℕ → ℤ :=
  (negacyclicShiftStepInt M)^[s] f

/-- The core integer radix-`B` Synthetic FFT operator `M_B` over `ℤ[z]/(z^{B/2} + 1)`. -/
def radixBMBOperatorInt (B : ℕ) (A : ℕ → ℕ → ℤ) (u m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range B, negacyclicShiftIterInt (B / 2) (j * u) (A j) m

theorem negacyclicShiftStepInt_add (M : ℕ) (f g : ℕ → ℤ) :
    negacyclicShiftStepInt M (fun m => f m + g m) =
      fun m => negacyclicShiftStepInt M f m + negacyclicShiftStepInt M g m := by
  funext m
  unfold negacyclicShiftStepInt
  split_ifs <;> ring

theorem negacyclicShiftStepInt_smul (M : ℕ) (c : ℤ) (f : ℕ → ℤ) :
    negacyclicShiftStepInt M (fun m => c * f m) =
      fun m => c * negacyclicShiftStepInt M f m := by
  funext m
  unfold negacyclicShiftStepInt
  split_ifs <;> ring

theorem negacyclicShiftIterInt_add (M s : ℕ) (f g : ℕ → ℤ) (m : ℕ) :
    negacyclicShiftIterInt M s (fun idx => f idx + g idx) m =
      negacyclicShiftIterInt M s f m + negacyclicShiftIterInt M s g m := by
  induction s generalizing f g m with
  | zero => rfl
  | succ s ih =>
    simp only [negacyclicShiftIterInt, Function.iterate_succ_apply]
    rw [negacyclicShiftStepInt_add]
    exact ih _ _ m

theorem negacyclicShiftIterInt_smul (M s : ℕ) (c : ℤ) (f : ℕ → ℤ) (m : ℕ) :
    negacyclicShiftIterInt M s (fun idx => c * f idx) m =
      c * negacyclicShiftIterInt M s f m := by
  induction s generalizing f m with
  | zero => rfl
  | succ s ih =>
    simp only [negacyclicShiftIterInt, Function.iterate_succ_apply]
    rw [negacyclicShiftStepInt_smul]
    exact ih _ m

theorem negacyclicShiftIterInt_sum {ι : Type*} (M s : ℕ) (S : Finset ι) (f : ι → ℕ → ℤ) (m : ℕ) :
    negacyclicShiftIterInt M s (fun idx => ∑ i ∈ S, f i idx) m =
      ∑ i ∈ S, negacyclicShiftIterInt M s (f i) m := by
  induction S using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    have := negacyclicShiftIterInt_smul M s 0 (fun _ => 0) m
    simpa using this
  | cons a S ha ih =>
    simp only [Finset.sum_cons]
    rw [negacyclicShiftIterInt_add, ih]

/-- **Substantive Linearity of `radixBMBOperatorInt` over `s`-Bit Slices (`theorem7_1_MB_bitSlice_linearity`; omitted earlier `[MS]` draft)**:
If an integer polynomial array `A` is decomposed into `S` radix-`2^s` bit-slices `A_slice q` via
`A j m = ∑_{q < S} 2^{q s} A_slice q j m`, then `radixBMBOperatorInt B A u m` equals the
radix-`2^s` linear combination of `radixBMBOperatorInt B (A_slice q) u m`. -/
theorem theorem7_1_MB_bitSlice_linearity
    (B S s : ℕ) (A : ℕ → ℕ → ℤ) (A_slice : ℕ → ℕ → ℕ → ℤ)
    (hA : ∀ j m, A j m = ∑ q ∈ Finset.range S, (2 : ℤ) ^ (q * s) * A_slice q j m)
    (u m : ℕ) :
    radixBMBOperatorInt B A u m =
      ∑ q ∈ Finset.range S, (2 : ℤ) ^ (q * s) * radixBMBOperatorInt B (A_slice q) u m := by
  unfold radixBMBOperatorInt
  have hsum :
      (∑ j ∈ Finset.range B, negacyclicShiftIterInt (B / 2) (j * u) (A j) m) =
      ∑ j ∈ Finset.range B, ∑ q ∈ Finset.range S,
        (2 : ℤ) ^ (q * s) * negacyclicShiftIterInt (B / 2) (j * u) (A_slice q j) m := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : A j = fun idx => ∑ q ∈ Finset.range S, (2 : ℤ) ^ (q * s) * A_slice q j idx :=
      funext (hA j)
    rw [hj, negacyclicShiftIterInt_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact negacyclicShiftIterInt_smul (B / 2) (j * u) ((2 : ℤ) ^ (q * s)) (A_slice q j) m
  rw [hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]

/-- Extremal `s`-bit slice witness whose entries all equal `2^s - 1 ∈ [0, 2^s - 1]`. -/
def extremalSlice (s : ℕ) : ℕ → ℕ → ℤ :=
  fun _ _ => (2 : ℤ) ^ s - 1

/-- **Sharp Dynamic-Range Lower Bound via Extremal Slice Witness at `u = 0` (`theorem7_1_MB_extremal_witness`; omitted earlier `[MS]` draft)**:
For any `k : ℕ` (`B = 2^k`) and `s ≥ 1`, the valid `s`-bit slice `extremalSlice s` (with entries in
`[0, 2^s - 1]`) causes `radixBMBOperatorInt (2^k) (extremalSlice s) 0 m` to reach
`2^k * (2^s - 1) ≥ 2^{s + k - 1}`, proving unconditionally that `M_{2^k}` outputs cannot fit in
fewer than `s + k` unsigned bits (or `s + k + 1` signed bits). -/
theorem theorem7_1_MB_extremal_witness (k s m : ℕ) (hs : 1 ≤ s) :
    (∀ j idx, 0 ≤ extremalSlice s j idx ∧ extremalSlice s j idx ≤ (2 : ℤ) ^ s - 1) ∧
    radixBMBOperatorInt (2 ^ k) (extremalSlice s) 0 m = (2 ^ k : ℤ) * ((2 : ℤ) ^ s - 1) ∧
    (2 : ℤ) ^ (s + k - 1) ≤ radixBMBOperatorInt (2 ^ k) (extremalSlice s) 0 m ∧
    radixBMBOperatorInt (2 ^ k) (extremalSlice s) 0 m < (2 : ℤ) ^ (s + k) := by
  have hvalid : ∀ j idx, 0 ≤ extremalSlice s j idx ∧ extremalSlice s j idx ≤ (2 : ℤ) ^ s - 1 := by
    intro j idx
    unfold extremalSlice
    have : (1 : ℤ) ≤ (2 : ℤ) ^ s := one_le_pow₀ (by norm_num)
    exact ⟨by linarith, le_refl _⟩
  have heval : radixBMBOperatorInt (2 ^ k) (extremalSlice s) 0 m =
      (2 ^ k : ℤ) * ((2 : ℤ) ^ s - 1) := by
    unfold radixBMBOperatorInt
    simp [negacyclicShiftIterInt, extremalSlice, Finset.sum_const]
    ring
  refine ⟨hvalid, heval, ?_, ?_⟩
  · rw [heval]
    have hs_eq : s = (s - 1) + 1 := by omega
    have hpow_s : (2 : ℤ) ^ (s - 1) ≤ (2 : ℤ) ^ s - 1 := by
      have h1 : (2 : ℤ) ^ s = 2 * (2 : ℤ) ^ (s - 1) := by
        conv_lhs => rw [hs_eq, pow_succ']
      have h2 : (1 : ℤ) ≤ (2 : ℤ) ^ (s - 1) := one_le_pow₀ (by norm_num)
      linarith
    have hpow_sk : (2 : ℤ) ^ (s + k - 1) = (2 ^ k : ℤ) * (2 : ℤ) ^ (s - 1) := by
      have hsk : s + k - 1 = k + (s - 1) := by omega
      rw [hsk, pow_add]
    rw [hpow_sk]
    exact mul_le_mul_of_nonneg_left hpow_s (by positivity)
  · rw [heval]
    exact theorem7_1_bitslice_magnitude_expansion k s

/-- Source index and sign `(src, sgn)` of `negacyclicShiftIterInt M t f m` (`sgn ∈ {-1, 1}`). -/
def negacyclicShiftSourceAndSign (M : ℕ) : ℕ → ℕ → ℕ × ℤ
  | 0, m => (m, 1)
  | t + 1, m =>
    let p := negacyclicShiftSourceAndSign M t m
    if p.1 = 0 then (M - 1, -p.2) else (p.1 - 1, p.2)

theorem negacyclicShiftIterInt_eq_sourceAndSign (M t : ℕ) (f : ℕ → ℤ) (m : ℕ) :
    negacyclicShiftIterInt M t f m =
      (negacyclicShiftSourceAndSign M t m).2 * f (negacyclicShiftSourceAndSign M t m).1 := by
  induction t generalizing f m with
  | zero =>
    simp [negacyclicShiftIterInt, negacyclicShiftSourceAndSign]
  | succ t ih =>
    simp only [negacyclicShiftIterInt, Function.iterate_succ_apply]
    have h := ih (negacyclicShiftStepInt M f) m
    unfold negacyclicShiftIterInt at h
    rw [h]
    dsimp only [negacyclicShiftSourceAndSign, negacyclicShiftStepInt]
    split_ifs <;> ring

theorem negacyclicShiftSourceAndSign_sq_eq_one (M t m : ℕ) :
    ((negacyclicShiftSourceAndSign M t m).2) ^ 2 = 1 ∧
    |(negacyclicShiftSourceAndSign M t m).2| = 1 := by
  induction t generalizing m with
  | zero =>
    simp [negacyclicShiftSourceAndSign]
  | succ t ih =>
    dsimp only [negacyclicShiftSourceAndSign]
    rcases ih m with ⟨hsq, habs⟩
    split_ifs
    · simp [hsq, abs_neg, habs]
    · exact ⟨hsq, habs⟩

/-- Non-DC signed `s`-bit extremal slice witness for arbitrary frequency `u` and coordinate `m`. -/
def signedExtremalSlice (B s u m : ℕ) (j _idx : ℕ) : ℤ :=
  (negacyclicShiftSourceAndSign (B / 2) (j * u) m).2 * ((2 : ℤ) ^ s - 1)

/-- **Non-DC Signed Extremal Slice Witness for Arbitrary `u` and `m` (`theorem7_1_MB_signed_extremal_witness`; omitted earlier `[MS]` draft)**:
For every frequency `u : ℕ` and coordinate `m : ℕ`, `signedExtremalSlice (2^k) s u m` has all
entries bounded in magnitude by `2^s - 1` and achieves the exact worst-case output
`radixBMBOperatorInt (2^k) (signedExtremalSlice (2^k) s u m) u m = 2^k * (2^s - 1) ≥ 2^{s + k - 1}`. -/
theorem theorem7_1_MB_signed_extremal_witness (k s u m : ℕ) (hs : 1 ≤ s) :
    (∀ j idx, |signedExtremalSlice (2 ^ k) s u m j idx| = (2 : ℤ) ^ s - 1) ∧
    radixBMBOperatorInt (2 ^ k) (signedExtremalSlice (2 ^ k) s u m) u m =
      (2 ^ k : ℤ) * ((2 : ℤ) ^ s - 1) ∧
    (2 : ℤ) ^ (s + k - 1) ≤
      radixBMBOperatorInt (2 ^ k) (signedExtremalSlice (2 ^ k) s u m) u m := by
  have hpos : (0 : ℤ) ≤ (2 : ℤ) ^ s - 1 := by
    have : (1 : ℤ) ≤ (2 : ℤ) ^ s := one_le_pow₀ (by norm_num)
    linarith
  have habs : ∀ j idx, |signedExtremalSlice (2 ^ k) s u m j idx| = (2 : ℤ) ^ s - 1 := by
    intro j idx
    unfold signedExtremalSlice
    rw [abs_mul, (negacyclicShiftSourceAndSign_sq_eq_one (2 ^ k / 2) (j * u) m).2,
        one_mul, abs_of_nonneg hpos]
  have heval : radixBMBOperatorInt (2 ^ k) (signedExtremalSlice (2 ^ k) s u m) u m =
      (2 ^ k : ℤ) * ((2 : ℤ) ^ s - 1) := by
    unfold radixBMBOperatorInt
    have hterm : ∀ j ∈ Finset.range (2 ^ k),
        negacyclicShiftIterInt (2 ^ k / 2) (j * u) (signedExtremalSlice (2 ^ k) s u m j) m =
          (2 : ℤ) ^ s - 1 := by
      intro j _
      rw [negacyclicShiftIterInt_eq_sourceAndSign]
      unfold signedExtremalSlice
      have hsq := (negacyclicShiftSourceAndSign_sq_eq_one (2 ^ k / 2) (j * u) m).1
      calc (negacyclicShiftSourceAndSign (2 ^ k / 2) (j * u) m).2 *
            ((negacyclicShiftSourceAndSign (2 ^ k / 2) (j * u) m).2 * ((2 : ℤ) ^ s - 1))
          = ((negacyclicShiftSourceAndSign (2 ^ k / 2) (j * u) m).2) ^ 2 * ((2 : ℤ) ^ s - 1) := by ring
        _ = (2 : ℤ) ^ s - 1 := by rw [hsq, one_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    rfl
  refine ⟨habs, heval, ?_⟩
  rw [heval, ← (theorem7_1_MB_extremal_witness k s m hs).2.1]
  exact (theorem7_1_MB_extremal_witness k s m hs).2.2.1

/-! ## 3. Floyd's Potential & 2-Register Conserved-Packet Transposition Bound (Omitted Earlier `[MS]` Draft Barrier Discussion) -/

/-- **First-Principles Sub-Additivity of Floyd's Cell Entropy (`floydPhi_add_le`; omitted earlier `[MS]` draft barrier discussion)**:
When two packet sub-counts `x > 0` and `y > 0` are combined into `x + y` by a register instruction,
the entropy increase `(x + y) log(x + y) - x log x - y log y` is bounded above by `(x + y) * log 2`
(corresponding to at most `x + y` bits in base-2 logarithm).
Proved from first principles via `Real.log_le_sub_one_of_pos` (`log u ≤ u - 1` applied to
`u = (x + y) / (2 x)` and `u = (x + y) / (2 y)`). -/
theorem theorem7_2_floyd_cell_merge_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x + y) * Real.log (x + y) - x * Real.log x - y * Real.log y ≤ (x + y) * Real.log 2 := by
  have hxy : 0 < x + y := add_pos hx hy
  have h2x : 0 < 2 * x := by linarith
  have h2y : 0 < 2 * y := by linarith
  have hu1 : Real.log ((x + y) / (2 * x)) ≤ (x + y) / (2 * x) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hxy h2x)
  have hu2 : Real.log ((x + y) / (2 * y)) ≤ (x + y) / (2 * y) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hxy h2y)
  have hlog1 : Real.log ((x + y) / (2 * x)) = Real.log (x + y) - Real.log 2 - Real.log x := by
    rw [Real.log_div hxy.ne' h2x.ne', Real.log_mul two_ne_zero hx.ne', sub_sub]
  have hlog2 : Real.log ((x + y) / (2 * y)) = Real.log (x + y) - Real.log 2 - Real.log y := by
    rw [Real.log_div hxy.ne' h2y.ne', Real.log_mul two_ne_zero hy.ne', sub_sub]
  have hm1 : x * (Real.log (x + y) - Real.log 2 - Real.log x) ≤ x * ((x + y) / (2 * x) - 1) := by
    rw [← hlog1]
    exact mul_le_mul_of_nonneg_left hu1 hx.le
  have hm2 : y * (Real.log (x + y) - Real.log 2 - Real.log y) ≤ y * ((x + y) / (2 * y) - 1) := by
    rw [← hlog2]
    exact mul_le_mul_of_nonneg_left hu2 hy.le
  have hrhs : x * ((x + y) / (2 * x) - 1) + y * ((x + y) / (2 * y) - 1) = 0 := by
    have hx_ne : x ≠ 0 := hx.ne'
    have hy_ne : y ≠ 0 := hy.ne'
    field_simp [hx_ne, hy_ne]
    ring
  linarith

/-- Concrete `B × B` packet distribution matrix: `a i j` is the number of sub-word packets
destined for target column `j : Fin B` currently stored in register/word `i : Fin B`. -/
abbrev PacketMatrix (B : ℕ) : Type := Fin B → Fin B → ℕ

/-- Initial untransposed `B × B` packet state: every register `i` holds 1 packet for each column `j`. -/
def initPacketMatrix (B : ℕ) : PacketMatrix B :=
  fun _ _ => 1

/-- Target transposed `B × B` packet state: register `i` holds all `B` packets for column `i`. -/
def targetPacketMatrix (B : ℕ) : PacketMatrix B :=
  fun i j => if i = j then B else 0

/-- Floyd's scalar cell entropy function `φ(x) = x log x` on natural packet counts `x : ℕ`
(with `φ(0) = 0` and `φ(1) = 0`). -/
noncomputable def floydPhi (x : ℕ) : ℝ :=
  (x : ℝ) * Real.log (x : ℝ)

@[simp]
theorem floydPhi_zero : floydPhi 0 = 0 := by
  simp [floydPhi]

@[simp]
theorem floydPhi_one : floydPhi 1 = 0 := by
  simp [floydPhi]

/-- Floyd's matrix potential `Φ(a) = ∑_{i : Fin B} ∑_{j : Fin B} φ(a_{i, j})`. -/
noncomputable def floydMatrixPotential (B : ℕ) (a : PacketMatrix B) : ℝ :=
  ∑ i : Fin B, ∑ j : Fin B, floydPhi (a i j)

/-- In the initial state `initPacketMatrix B`, `floydMatrixPotential` is identically `0`. -/
theorem floydMatrixPotential_init (B : ℕ) :
    floydMatrixPotential B (initPacketMatrix B) = 0 := by
  simp [floydMatrixPotential, initPacketMatrix]

/-- In the target transposed state `targetPacketMatrix B`, `floydMatrixPotential` equals
`B^2 * log B`. -/
theorem floydMatrixPotential_target (B : ℕ) :
    floydMatrixPotential B (targetPacketMatrix B) = (B : ℝ) ^ 2 * Real.log (B : ℝ) := by
  unfold floydMatrixPotential targetPacketMatrix
  have hinner : ∀ i : Fin B,
      (∑ j : Fin B, floydPhi (if i = j then B else 0)) = (B : ℝ) * Real.log (B : ℝ) := by
    intro i
    have hite : ∀ j : Fin B,
        floydPhi (if i = j then B else 0) = if i = j then floydPhi B else 0 := by
      intro j
      split_ifs <;> simp
    simp_rw [hite]
    simp [floydPhi]
  simp_rw [hinner]
  simp [Finset.sum_const, nsmul_eq_mul, sq]
  ring

/-- When `B = 2^k`, `floydMatrixPotential (2^k) (targetPacketMatrix (2^k)) = k * (2^k)^2 * log 2`. -/
theorem floydMatrixPotential_target_pow2 (k : ℕ) :
    floydMatrixPotential (2 ^ k) (targetPacketMatrix (2 ^ k)) =
      (k : ℝ) * ((2 ^ k : ℝ) ^ 2) * Real.log 2 := by
  rw [floydMatrixPotential_target]
  push_cast
  rw [Real.log_pow]
  ring

/-- Super-additivity of `floydPhi` under partitioning: splitting `x + y` into `x` and `y` satisfies
`floydPhi x + floydPhi y ≤ floydPhi (x + y)` for all `x, y : ℕ`. -/
theorem floydPhi_superadditive (x y : ℕ) :
    floydPhi x + floydPhi y ≤ floydPhi (x + y) := by
  by_cases hx : x = 0
  · subst hx; simp
  · by_cases hy : y = 0
    · subst hy; simp
    · unfold floydPhi
      have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx)
      have hy_pos : (0 : ℝ) < (y : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hy)
      have hlogx : Real.log (x : ℝ) ≤ Real.log ((x + y : ℕ) : ℝ) := by
        apply Real.log_le_log hx_pos
        exact_mod_cast Nat.le_add_right x y
      have hlogy : Real.log (y : ℝ) ≤ Real.log ((x + y : ℕ) : ℝ) := by
        apply Real.log_le_log hy_pos
        exact_mod_cast Nat.le_add_left y x
      have hm1 := mul_le_mul_of_nonneg_left hlogx hx_pos.le
      have hm2 := mul_le_mul_of_nonneg_left hlogy hy_pos.le
      push_cast at hm1 hm2 ⊢
      linarith

/-- Merging bound for `floydPhi` on natural numbers (including `0`):
`floydPhi (x + z) ≤ floydPhi x + floydPhi z + (x + z) * log 2`. -/
theorem floydPhi_merge_le (x z : ℕ) :
    floydPhi (x + z) ≤ floydPhi x + floydPhi z + ((x : ℝ) + (z : ℝ)) * Real.log 2 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hx : x = 0
  · subst hx
    simp only [zero_add, floydPhi_zero, Nat.cast_zero]
    have : 0 ≤ (z : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg z) hlog2
    linarith
  · by_cases hz : z = 0
    · subst hz
      simp only [add_zero, floydPhi_zero, Nat.cast_zero]
      have : 0 ≤ (x : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg x) hlog2
      linarith
    · have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx)
      have hz_pos : (0 : ℝ) < (z : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
      have h := theorem7_2_floyd_cell_merge_bound (x : ℝ) (z : ℝ) hx_pos hz_pos
      unfold floydPhi
      push_cast
      linarith

/-- **2-Cell Partition-and-Merge Entropy Bound**:
When cell counts `x + y` and `z + w` are partitioned into `(x, y)` and `(z, w)` and re-merged into
`x + z` and `y + w`, the net change in `floydPhi` is at most `((x + y) + (z + w)) * log 2`. -/
theorem theorem7_2_floyd_two_cell_partition_merge_bound (x y z w : ℕ) :
    floydPhi (x + z) + floydPhi (y + w) - floydPhi (x + y) - floydPhi (z + w) ≤
      (((x + y : ℕ) : ℝ) + ((z + w : ℕ) : ℝ)) * Real.log 2 := by
  have hm1 := floydPhi_merge_le x z
  have hm2 := floydPhi_merge_le y w
  have hs1 := floydPhi_superadditive x y
  have hs2 := floydPhi_superadditive z w
  push_cast
  linarith

/-- A valid 2-register partition-and-merge step on a `B × B` packet distribution matrix:
selects two distinct registers `i1 ≠ i2` (each holding at most `B` packets), partitions their
column counts into `a i1 j = x j + y j` and `a i2 j = z j + w j`, merges them into
`a' i1 j = x j + z j` and `a' i2 j = y j + w j`, and leaves all other registers unchanged. -/
def ValidTwoRegStep (B : ℕ) (a a' : PacketMatrix B) : Prop :=
  ∃ (i1 i2 : Fin B) (_hne : i1 ≠ i2) (x y z w : Fin B → ℕ),
    (∑ j : Fin B, a i1 j ≤ B) ∧
    (∑ j : Fin B, a i2 j ≤ B) ∧
    (∀ j : Fin B, a i1 j = x j + y j) ∧
    (∀ j : Fin B, a i2 j = z j + w j) ∧
    (∀ j : Fin B, a' i1 j = x j + z j) ∧
    (∀ j : Fin B, a' i2 j = y j + w j) ∧
    (∀ i : Fin B, i ≠ i1 → i ≠ i2 → ∀ j : Fin B, a' i j = a i j)

/-- **1-Step Matrix Potential Increase Bound for Any `ValidTwoRegStep` (`theorem7_2_validTwoRegStep_potential_diff_le`; omitted earlier `[MS]` draft)**:
Every valid 2-register partition-and-merge step `ValidTwoRegStep B a a'` increases
`floydMatrixPotential B` by at most `2 * B * log 2`. -/
theorem theorem7_2_validTwoRegStep_potential_diff_le
    (B : ℕ) (a a' : PacketMatrix B) (hstep : ValidTwoRegStep B a a') :
    floydMatrixPotential B a' - floydMatrixPotential B a ≤ 2 * (B : ℝ) * Real.log 2 := by
  rcases hstep with ⟨i1, i2, hne, x, y, z, w, hcap1, hcap2, ha1, ha2, ha'1, ha'2, hframe⟩
  unfold floydMatrixPotential
  let rowPot (m : PacketMatrix B) (i : Fin B) : ℝ := ∑ j : Fin B, floydPhi (m i j)
  change (∑ i ∈ Finset.univ, rowPot a' i) - (∑ i ∈ Finset.univ, rowPot a i) ≤
    2 * (B : ℝ) * Real.log 2
  have hi1 : i1 ∈ (Finset.univ : Finset (Fin B)) := Finset.mem_univ i1
  have hi2 : i2 ∈ (Finset.univ : Finset (Fin B)).erase i1 :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i2⟩
  have hsplit_a' : (∑ i ∈ Finset.univ, rowPot a' i) =
      rowPot a' i1 + (rowPot a' i2 + ∑ i ∈ (Finset.univ.erase i1).erase i2, rowPot a' i) := by
    rw [← Finset.add_sum_erase _ _ hi1, ← Finset.add_sum_erase _ _ hi2]
  have hsplit_a : (∑ i ∈ Finset.univ, rowPot a i) =
      rowPot a i1 + (rowPot a i2 + ∑ i ∈ (Finset.univ.erase i1).erase i2, rowPot a i) := by
    rw [← Finset.add_sum_erase _ _ hi1, ← Finset.add_sum_erase _ _ hi2]
  have hrest : (∑ i ∈ (Finset.univ.erase i1).erase i2, rowPot a' i) =
      ∑ i ∈ (Finset.univ.erase i1).erase i2, rowPot a i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_ne2 : i ≠ i2 := (Finset.mem_erase.mp hi).1
    have hi_ne1 : i ≠ i1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    dsimp [rowPot]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hframe i hi_ne1 hi_ne2 j]
  have hdiff : (∑ i ∈ Finset.univ, rowPot a' i) - (∑ i ∈ Finset.univ, rowPot a i) =
      ∑ j : Fin B, (floydPhi (a' i1 j) + floydPhi (a' i2 j) - floydPhi (a i1 j) - floydPhi (a i2 j)) := by
    rw [hsplit_a', hsplit_a, hrest]
    have hring : rowPot a' i1 + (rowPot a' i2 + ∑ i ∈ (Finset.univ.erase i1).erase i2, rowPot a i) -
        (rowPot a i1 + (rowPot a i2 + ∑ i ∈ (Finset.univ.erase i1).erase i2, rowPot a i)) =
        rowPot a' i1 + rowPot a' i2 - rowPot a i1 - rowPot a i2 := by ring
    rw [hring]
    dsimp [rowPot]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hdiff]
  have hcell : (∑ j : Fin B,
      (floydPhi (a' i1 j) + floydPhi (a' i2 j) - floydPhi (a i1 j) - floydPhi (a i2 j))) ≤
      ∑ j : Fin B, (((a i1 j : ℝ) + (a i2 j : ℝ)) * Real.log 2) := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [ha'1 j, ha'2 j, ha1 j, ha2 j]
    exact theorem7_2_floyd_two_cell_partition_merge_bound (x j) (y j) (z j) (w j)
  rw [← Finset.sum_mul, Finset.sum_add_distrib] at hcell
  have hcap1_real : (∑ j : Fin B, (a i1 j : ℝ)) ≤ (B : ℝ) := by exact_mod_cast hcap1
  have hcap2_real : (∑ j : Fin B, (a i2 j : ℝ)) ≤ (B : ℝ) := by exact_mod_cast hcap2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2B : ((∑ j : Fin B, (a i1 j : ℝ)) + (∑ j : Fin B, (a i2 j : ℝ))) * Real.log 2 ≤
      2 * (B : ℝ) * Real.log 2 := by
    have : (∑ j : Fin B, (a i1 j : ℝ)) + (∑ j : Fin B, (a i2 j : ℝ)) ≤ 2 * (B : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right this hlog2
  exact hcell.trans h2B

/-- Inductive multi-step execution trace of valid 2-register partition-and-merge operations
transforming packet matrix `a` into `b`. -/
inductive ValidTransposeTrace (B : ℕ) : PacketMatrix B → List (PacketMatrix B) → PacketMatrix B → Prop
  | nil (a : PacketMatrix B) : ValidTransposeTrace B a [] a
  | cons {a a1 b : PacketMatrix B} {rest : List (PacketMatrix B)}
      (hstep : ValidTwoRegStep B a a1)
      (htrace : ValidTransposeTrace B a1 rest b) :
      ValidTransposeTrace B a (a1 :: rest) b

/-- By structural induction on any `ValidTransposeTrace B a trace b`, the net potential gain
`floydMatrixPotential B b - floydMatrixPotential B a` is bounded above by
`trace.length * (2 * B * log 2)`. -/
theorem validTransposeTrace_potential_diff_le
    (B : ℕ) (a b : PacketMatrix B) (trace : List (PacketMatrix B))
    (htrace : ValidTransposeTrace B a trace b) :
    floydMatrixPotential B b - floydMatrixPotential B a ≤
      (trace.length : ℝ) * (2 * (B : ℝ) * Real.log 2) := by
  induction htrace with
  | nil a =>
    simp
  | cons hstep _ ih =>
    have h1 := theorem7_2_validTwoRegStep_potential_diff_le B _ _ hstep
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- **Unconditional 2-Register Conserved-Packet Trace Lower Bound for `2^k × 2^k` Transposition (`theorem7_2_floyd_trace_lower_bound`; omitted earlier `[MS]` draft)**:
For any valid execution trace `trace` of 2-register operations transforming `initPacketMatrix (2^k)`
into `targetPacketMatrix (2^k)` (with zero assumed `h_total` or `hPhi` hypotheses!), the number of
2-register steps `trace.length` satisfies `k * 2^k ≤ 2 * trace.length`, i.e.,
`trace.length ≥ k * 2^k / 2`. -/
theorem theorem7_2_floyd_trace_lower_bound
    (k : ℕ) (trace : List (PacketMatrix (2 ^ k)))
    (htrace : ValidTransposeTrace (2 ^ k) (initPacketMatrix (2 ^ k)) trace (targetPacketMatrix (2 ^ k))) :
    (k : ℝ) * (2 ^ k : ℝ) ≤ 2 * (trace.length : ℝ) ∧
    (k : ℝ) * (2 ^ k : ℝ) / 2 ≤ (trace.length : ℝ) := by
  have hdiff := validTransposeTrace_potential_diff_le (2 ^ k)
    (initPacketMatrix (2 ^ k)) (targetPacketMatrix (2 ^ k)) trace htrace
  rw [floydMatrixPotential_init, floydMatrixPotential_target_pow2, sub_zero] at hdiff
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB_pos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
  have h1 : (k : ℝ) * ((2 ^ k : ℝ) ^ 2) ≤ (trace.length : ℝ) * (2 * (2 ^ k : ℝ)) := by
    push_cast at hdiff
    have hmul : (k : ℝ) * ((2 ^ k : ℝ) ^ 2) * Real.log 2 ≤
        ((trace.length : ℝ) * (2 * (2 ^ k : ℝ))) * Real.log 2 := by
      linarith
    exact le_of_mul_le_mul_right hmul hlog2_pos
  have h2 : (k : ℝ) * (2 ^ k : ℝ) ≤ 2 * (trace.length : ℝ) := by
    have hmul2 : ((k : ℝ) * (2 ^ k : ℝ)) * (2 ^ k : ℝ) ≤
        (2 * (trace.length : ℝ)) * (2 ^ k : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right hmul2 hB_pos
  refine ⟨h2, ?_⟩
  linarith

/-! ## 4. Bluestein Chirp Identity & Non-Shift-Invariance of Radix-`B` Exponents (Omitted Earlier `[MS]` Draft Barrier Discussion) -/

/-- **Bluestein Chirp Identity (`theorem7_3_bluestein_chirp_identity`; omitted earlier `[MS]` draft barrier discussion)**:
Reduction of the bilinear exponent `2 j u` to the shift-invariant difference `(u - j)^2` plus
diagonal chirp factors `j^2` and `u^2`. -/
theorem theorem7_3_bluestein_chirp_identity (j u : ℤ) :
    2 * j * u = j ^ 2 + u ^ 2 - (u - j) ^ 2 := by
  ring

/-- **Non-Shift-Invariance of the Radix-`B` Exponent Kernel (`theorem7_3_exponent_not_shift_invariant`; omitted earlier `[MS]` draft barrier discussion)**:
For every `B ≥ 2`, the bilinear exponent map `(j, u) ↦ (j * u) % B` is NOT a function of the
difference `u - j`: the pairs `(0, 0)` and `(1, 1)` have the same difference `0 - 0 = 1 - 1 = 0`
(even modulo `B`), but `(0 * 0) % B = 0 ≠ 1 = (1 * 1) % B`. -/
theorem theorem7_3_exponent_not_shift_invariant (B : ℕ) (hB : 2 ≤ B) :
    ¬∃ g : ℤ → ℕ, ∀ j < B, ∀ u < B, (j * u) % B = g ((u : ℤ) - (j : ℤ)) := by
  rintro ⟨g, hg⟩
  have h00 := hg 0 (by omega) 0 (by omega)
  have h11 := hg 1 (by omega) 1 (by omega)
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.cast_zero, sub_self,
             Nat.one_mul, Nat.cast_one] at h00 h11
  rw [Nat.mod_eq_of_lt hB] at h11
  omega

/-! ## 5. Prescribed Chunk-Splitting Tree Recurrence Telescoping (Omitted Earlier `[MS]` Draft Barrier Discussion) -/

/-- Recursive chunk-splitting schedule tree of arbitrary depth:
- `leaf b`: base chunk of bit-length `b`
- `node b R child`: splits a `b`-bit chunk into `b / child.bitLen` sub-chunks of bit-length
  `child.bitLen` using a length-`R` transform (`R ≥ 2 * (b / child.bitLen)`). -/
inductive ChunkSplitTree : Type
  | leaf (b : ℕ) : ChunkSplitTree
  | node (b R : ℕ) (child : ChunkSplitTree) : ChunkSplitTree

/-- Root chunk bit-length of a `ChunkSplitTree`. -/
def ChunkSplitTree.bitLen : ChunkSplitTree → ℕ
  | .leaf b => b
  | .node b _ _ => b

/-- Leaf chunk bit-length at the bottom of a `ChunkSplitTree`. -/
def ChunkSplitTree.leafBitLen : ChunkSplitTree → ℕ
  | .leaf b => b
  | .node _ _ child => child.leafBitLen

/-- Number of chunk-splitting levels in a `ChunkSplitTree`. -/
def ChunkSplitTree.depth : ChunkSplitTree → ℕ
  | .leaf _ => 0
  | .node _ _ child => child.depth + 1

/-- Validity predicate for a `ChunkSplitTree`:
every chunk bit-length is positive, each internal node strictly reduces the chunk bit-length
(`child.bitLen < b`) with exact divisibility (`child.bitLen ∣ b`), and the acyclic convolution
transform length satisfies `R ≥ 2 * (b / child.bitLen)`. -/
def ChunkSplitTree.Valid : ChunkSplitTree → Prop
  | .leaf b => 0 < b
  | .node b R child =>
      0 < b ∧ child.bitLen < b ∧ (child.bitLen ∣ b) ∧
      2 * (b / child.bitLen) ≤ R ∧ child.Valid

/-- Optimistic (unit-expansion) transform work across a `ChunkSplitTree`:
each internal node incurs transform overhead `c * b * Real.log (b / child.bitLen)` plus
`(b / child.bitLen)` recursive sub-calls of `child.transformWork c`. -/
noncomputable def ChunkSplitTree.transformWork (c : ℝ) : ChunkSplitTree → ℝ
  | .leaf _ => 0
  | .node b _ child =>
      c * (b : ℝ) * Real.log ((b : ℝ) / (child.bitLen : ℝ)) +
        ((b : ℝ) / (child.bitLen : ℝ)) * child.transformWork c

/-- Total number of leaf subproblems spawned when each internal node branches into `R` recursive
pointwise sub-products. -/
def ChunkSplitTree.spawnedLeaves : ChunkSplitTree → ℕ
  | .leaf _ => 1
  | .node _ R child => R * child.spawnedLeaves

theorem ChunkSplitTree.Valid.bitLen_pos {T : ChunkSplitTree} (hT : T.Valid) :
    0 < T.bitLen ∧ 0 < T.leafBitLen := by
  induction T with
  | leaf b =>
    exact ⟨hT, hT⟩
  | node b R child ih =>
    rcases hT with ⟨hb, _, _, _, hchild⟩
    exact ⟨hb, (ih hchild).2⟩

/-- **Chunk-Splitting Tree Recurrence (Part A: Structural Induction Telescoping of `ChunkSplitTree.transformWork`; omitted earlier `[MS]` draft)**:
For any valid recursive chunk-splitting tree `T : ChunkSplitTree` of arbitrary depth, even under
unit expansion (`b / child.bitLen` subproblems), the total transform overhead equals
`c * T.bitLen * log(T.bitLen / T.leafBitLen)` identically, independent of the intermediate split
schedule. -/
theorem theorem7_4_tree_transform_work_eq
    (c : ℝ) (T : ChunkSplitTree) (hT : T.Valid) :
    T.transformWork c =
      c * (T.bitLen : ℝ) * Real.log ((T.bitLen : ℝ) / (T.leafBitLen : ℝ)) := by
  induction T with
  | leaf b =>
    have hb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
    simp [ChunkSplitTree.transformWork, ChunkSplitTree.bitLen, ChunkSplitTree.leafBitLen,
          div_self hb]
  | node b R child ih =>
    rcases hT with ⟨hb, _, _, _, hchild⟩
    rcases ChunkSplitTree.Valid.bitLen_pos hchild with ⟨hc_pos, hl_pos⟩
    have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
    have hc_rpos : (0 : ℝ) < (child.bitLen : ℝ) := Nat.cast_pos.mpr hc_pos
    have hl_rpos : (0 : ℝ) < (child.leafBitLen : ℝ) := Nat.cast_pos.mpr hl_pos
    change c * (b : ℝ) * Real.log ((b : ℝ) / (child.bitLen : ℝ)) +
        ((b : ℝ) / (child.bitLen : ℝ)) * child.transformWork c =
      c * (b : ℝ) * Real.log ((b : ℝ) / (child.leafBitLen : ℝ))
    rw [ih hchild]
    have hdiv_mul : ((b : ℝ) / (child.bitLen : ℝ)) * ((child.bitLen : ℝ) / (child.leafBitLen : ℝ)) =
        (b : ℝ) / (child.leafBitLen : ℝ) := by
      field_simp [hc_rpos.ne', hl_rpos.ne']
    have hlog : Real.log ((b : ℝ) / (child.bitLen : ℝ)) +
        Real.log ((child.bitLen : ℝ) / (child.leafBitLen : ℝ)) =
        Real.log ((b : ℝ) / (child.leafBitLen : ℝ)) := by
      rw [← Real.log_mul (div_pos hb_pos hc_rpos).ne' (div_pos hc_rpos hl_rpos).ne', hdiv_mul]
    have hcancel : ((b : ℝ) / (child.bitLen : ℝ)) *
        (c * (child.bitLen : ℝ) * Real.log ((child.bitLen : ℝ) / (child.leafBitLen : ℝ))) =
        c * (b : ℝ) * Real.log ((child.bitLen : ℝ) / (child.leafBitLen : ℝ)) := by
      field_simp [hc_rpos.ne']
    rw [hcancel, ← mul_add, hlog]

/-- **Chunk-Splitting Tree Recurrence (Part B: Exponential `2^depth` Subproblem Blowup under Zero-Padded Splits; omitted earlier `[MS]` draft)**:
In any valid `ChunkSplitTree`, because acyclic convolution requires `R ≥ 2 * (b / child.bitLen)`
at each internal node, the total number of leaf subproblems satisfies
`T.spawnedLeaves ≥ 2 ^ T.depth * (T.bitLen / T.leafBitLen)`. -/
theorem theorem7_4_tree_spawnedLeaves_ge
    (T : ChunkSplitTree) (hT : T.Valid) :
    (T.leafBitLen ∣ T.bitLen) ∧
    2 ^ T.depth * (T.bitLen / T.leafBitLen) ≤ T.spawnedLeaves := by
  induction T with
  | leaf b =>
    refine ⟨dvd_refl b, ?_⟩
    simp [ChunkSplitTree.depth, ChunkSplitTree.bitLen, ChunkSplitTree.leafBitLen,
          ChunkSplitTree.spawnedLeaves, Nat.div_self hT]
  | node b R child ih =>
    rcases hT with ⟨_, _, hdvd, hR, hchild⟩
    rcases ih hchild with ⟨hdvd_leaf, hleaves⟩
    rcases ChunkSplitTree.Valid.bitLen_pos hchild with ⟨hc_pos, hl_pos⟩
    refine ⟨dvd_trans hdvd_leaf hdvd, ?_⟩
    dsimp only [ChunkSplitTree.depth, ChunkSplitTree.bitLen, ChunkSplitTree.leafBitLen,
                ChunkSplitTree.spawnedLeaves]
    have hdiv_mul : (b / child.bitLen) * (child.bitLen / child.leafBitLen) =
        b / child.leafBitLen := by
      rcases hdvd with ⟨q1, hq1⟩
      rcases hdvd_leaf with ⟨q2, hq2⟩
      have h1 : b / child.bitLen = q1 := by
        rw [hq1, Nat.mul_div_right q1 hc_pos]
      have h2 : child.bitLen / child.leafBitLen = q2 := by
        rw [hq2, Nat.mul_div_right q2 hl_pos]
      have h3 : b / child.leafBitLen = q1 * q2 := by
        have hb_eq : b = child.leafBitLen * (q2 * q1) := by
          rw [hq1, hq2, mul_assoc]
        rw [hb_eq, Nat.mul_div_right (q2 * q1) hl_pos, mul_comm]
      rw [h1, h2, h3]
    calc 2 ^ (child.depth + 1) * (b / child.leafBitLen)
        = (2 * (b / child.bitLen)) * (2 ^ child.depth * (child.bitLen / child.leafBitLen)) := by
            rw [← hdiv_mul, pow_succ']
            ring
      _ ≤ R * child.spawnedLeaves := Nat.mul_le_mul hR hleaves

/-- Zero-padded recursive work across a `ChunkSplitTree`:
each internal node spawns `R ≥ 2 * (b / child.bitLen)` subproblems of size `child.bitLen` and
incurs transform overhead `c * R * child.bitLen * Real.log (b / child.bitLen)`. -/
noncomputable def ChunkSplitTree.zeroPaddedWork (c : ℝ) : ChunkSplitTree → ℝ
  | .leaf b => (b : ℝ)
  | .node b R child =>
      c * (R : ℝ) * (child.bitLen : ℝ) * Real.log ((b : ℝ) / (child.bitLen : ℝ)) +
        (R : ℝ) * child.zeroPaddedWork c

/-- **Chunk-Splitting Tree Recurrence (Part C: Zero-Padded Recursive Work Lower Bound `≥ 2^depth * b_0`; omitted earlier `[MS]` draft)**:
For any valid `ChunkSplitTree` and `c ≥ 0`, `T.zeroPaddedWork c` is at least
`T.spawnedLeaves * T.leafBitLen ≥ 2 ^ T.depth * T.bitLen`. -/
theorem theorem7_4_tree_zeroPaddedWork_ge
    (c : ℝ) (hc : 0 ≤ c) (T : ChunkSplitTree) (hT : T.Valid) :
    (T.spawnedLeaves : ℝ) * (T.leafBitLen : ℝ) ≤ T.zeroPaddedWork c ∧
    (2 : ℝ) ^ T.depth * (T.bitLen : ℝ) ≤ T.zeroPaddedWork c := by
  have h1 : (T.spawnedLeaves : ℝ) * (T.leafBitLen : ℝ) ≤ T.zeroPaddedWork c := by
    induction T with
    | leaf b =>
      simp [ChunkSplitTree.spawnedLeaves, ChunkSplitTree.leafBitLen, ChunkSplitTree.zeroPaddedWork]
    | node b R child ih =>
      rcases hT with ⟨_, hlt, _, _, hchild⟩
      rcases ChunkSplitTree.Valid.bitLen_pos hchild with ⟨hc_pos, _⟩
      have hc_rpos : (0 : ℝ) < (child.bitLen : ℝ) := Nat.cast_pos.mpr hc_pos
      have hdiv_ge_one : (1 : ℝ) ≤ (b : ℝ) / (child.bitLen : ℝ) := by
        rw [le_div_iff₀ hc_rpos, one_mul]
        exact_mod_cast hlt.le
      have hlog_nonneg : 0 ≤ Real.log ((b : ℝ) / (child.bitLen : ℝ)) :=
        Real.log_nonneg hdiv_ge_one
      have hovh_nonneg :
          0 ≤ c * (R : ℝ) * (child.bitLen : ℝ) * Real.log ((b : ℝ) / (child.bitLen : ℝ)) := by
        positivity
      have hrec : (R : ℝ) * ((child.spawnedLeaves : ℝ) * (child.leafBitLen : ℝ)) ≤
          (R : ℝ) * child.zeroPaddedWork c :=
        mul_le_mul_of_nonneg_left (ih hchild) (Nat.cast_nonneg R)
      change ((R * child.spawnedLeaves : ℕ) : ℝ) * (child.leafBitLen : ℝ) ≤
        c * (R : ℝ) * (child.bitLen : ℝ) * Real.log ((b : ℝ) / (child.bitLen : ℝ)) +
          (R : ℝ) * child.zeroPaddedWork c
      push_cast
      linarith
  refine ⟨h1, ?_⟩
  rcases theorem7_4_tree_spawnedLeaves_ge T hT with ⟨hdvd, hleaves⟩
  have hmul : (2 ^ T.depth * (T.bitLen / T.leafBitLen)) * T.leafBitLen ≤
      T.spawnedLeaves * T.leafBitLen :=
    Nat.mul_le_mul_right T.leafBitLen hleaves
  have hdiv_cancel : (T.bitLen / T.leafBitLen) * T.leafBitLen = T.bitLen :=
    Nat.div_mul_cancel hdvd
  have hnat : 2 ^ T.depth * T.bitLen ≤ T.spawnedLeaves * T.leafBitLen := by
    calc 2 ^ T.depth * T.bitLen
        = (2 ^ T.depth * (T.bitLen / T.leafBitLen)) * T.leafBitLen := by
          rw [mul_assoc, hdiv_cancel]
      _ ≤ T.spawnedLeaves * T.leafBitLen := hmul
  have hreal : (2 : ℝ) ^ T.depth * (T.bitLen : ℝ) ≤
      (T.spawnedLeaves : ℝ) * (T.leafBitLen : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans h1

/-! ## 6. Exact Multiplicative Order `2r` in `R_r` & Ring-Divisibility Depth Bound (Omitted Earlier `[MS]` Draft Barrier Discussion) -/

/-- The unit polynomial `1 ∈ ℂ[y]/(y^r + 1)`, represented by its coefficient sequence
`δ_0(k) = if k = 0 then 1 else 0`. -/
def delta0Poly (k : ℕ) : ℂ :=
  if k = 0 then 1 else 0

/-- **Explicit Evaluation of `negacyclicShiftIter r s delta0Poly` in `R_r` (`negacyclicShiftIter_delta0_eval`)**:
For any `r > 0`, `s : ℕ`, and `k < r`, shifting the unit polynomial `delta0Poly` by `s` steps in
`R_r = ℂ[y]/(y^r + 1)` places `(-1)^{s / r}` at index `s % r` and `0` everywhere else. -/
theorem negacyclicShiftIter_delta0_eval (r s : ℕ) (hr : 0 < r) (k : ℕ) (hk : k < r) :
    negacyclicShiftIter r s delta0Poly k =
      if k = s % r then (-1 : ℂ) ^ (s / r) else 0 := by
  induction s generalizing k with
  | zero =>
    simp [negacyclicShiftIter, delta0Poly, Nat.zero_mod, Nat.zero_div]
  | succ s ih =>
    have hstep : negacyclicShiftIter r (s + 1) delta0Poly k =
        negacyclicShiftStep r (negacyclicShiftIter r s delta0Poly) k := by
      simp [negacyclicShiftIter, Function.iterate_succ_apply']
    rw [hstep]
    have hmod_lt : s % r < r := Nat.mod_lt s hr
    have hdiv_mod : r * (s / r) + s % r = s := Nat.div_add_mod s r
    by_cases hwrap : s % r + 1 < r
    · have hs1_mod : (s + 1) % r = s % r + 1 := by
        have h1 : s + 1 = (s % r + 1) + r * (s / r) := by omega
        rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hwrap]
      have hs1_div : (s + 1) / r = s / r := by
        have h1 : s + 1 = (s % r + 1) + r * (s / r) := by omega
        rw [h1, Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hwrap, zero_add]
      rw [hs1_mod, hs1_div]
      unfold negacyclicShiftStep
      by_cases hk0 : k = 0
      · subst hk0
        simp only [↓reduceIte, ih (r - 1) (by omega)]
        have hne1 : r - 1 ≠ s % r := by omega
        simp [hne1]
      · simp only [hk0, ↓reduceIte, ih (k - 1) (by omega)]
        have heq : (k - 1 = s % r) ↔ (k = s % r + 1) := by omega
        simp [heq]
    · have hsr : s % r + 1 = r := by omega
      have hs1_mod : (s + 1) % r = 0 := by
        have h1 : s + 1 = r * (s / r + 1) := by
          calc s + 1 = r * (s / r) + (s % r + 1) := by omega
            _ = r * (s / r) + r := by rw [hsr]
            _ = r * (s / r + 1) := by ring
        rw [h1, Nat.mul_mod_right]
      have hs1_div : (s + 1) / r = s / r + 1 := by
        have h1 : s + 1 = r * (s / r + 1) := by
          calc s + 1 = r * (s / r) + (s % r + 1) := by omega
            _ = r * (s / r) + r := by rw [hsr]
            _ = r * (s / r + 1) := by ring
        rw [h1, Nat.mul_div_right _ hr]
      rw [hs1_mod, hs1_div]
      unfold negacyclicShiftStep
      by_cases hk0 : k = 0
      · subst hk0
        simp only [↓reduceIte, ih (r - 1) (by omega)]
        have heq : r - 1 = s % r := by omega
        rw [if_pos heq, pow_succ]
        ring
      · simp only [hk0, ↓reduceIte, ih (k - 1) (by omega)]
        have hne : k - 1 ≠ s % r := by omega
        simp [hne]

/-- **Substantive Exact Multiplicative Order `2r` of `negacyclicShiftIter` in `R_r` (`theorem7_5_negacyclicShiftIter_exact_order_two_mul_r`; omitted earlier `[MS]` draft)**:
For any `r > 0`:
1. Shifting by `2 * r` is the identity on `delta0Poly` across `0 ≤ k < r`, and
2. For every `0 < s < 2 * r`, `negacyclicShiftIter r s delta0Poly` is NOT the identity on `0 .. r - 1`
   (specifically, its coefficient at `k = 0` is either `0` or `-1`, never `1 = delta0Poly 0`). -/
theorem theorem7_5_negacyclicShiftIter_exact_order_two_mul_r (r : ℕ) (hr : 0 < r) :
    (∀ k < r, negacyclicShiftIter r (2 * r) delta0Poly k = delta0Poly k) ∧
    (∀ s : ℕ, 0 < s → s < 2 * r → ∃ k < r, negacyclicShiftIter r s delta0Poly k ≠ delta0Poly k) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [negacyclicShiftIter_delta0_eval r (2 * r) hr k hk]
    have hmod : (2 * r) % r = 0 := Nat.mul_mod_left 2 r
    have hdiv : (2 * r) / r = 2 := Nat.mul_div_left 2 hr
    rw [hmod, hdiv]
    norm_num [delta0Poly]
  · intro s hs_pos hs_lt
    refine ⟨0, hr, ?_⟩
    rw [negacyclicShiftIter_delta0_eval r s hr 0 hr]
    simp only [delta0Poly, ↓reduceIte]
    by_cases hmod : 0 = s % r
    · rw [if_pos hmod]
      have hdiv_mod : r * (s / r) + s % r = s := Nat.div_add_mod s r
      have hq : s / r = 1 := by
        set q := s / r
        have hmul : r * q = s := by omega
        have hge : 1 ≤ q := by
          rcases Nat.eq_zero_or_pos q with h0 | hpos
          · rw [h0, mul_zero] at hmul
            omega
          · exact hpos
        have hle : q < 2 := by
          by_contra hgt
          have h2 : 2 * r ≤ q * r := Nat.mul_le_mul_right r (by omega)
          have h3 : q * r = s := by rw [mul_comm, hmul]
          omega
        omega
      rw [hq]
      norm_num
    · rw [if_neg hmod]
      exact zero_ne_one

/-- `[MS]` §3.5 / Proposition 4.1 ring-divisibility admissibility for a multi-level log-size schedule `K : ℕ → ℕ`:
at every level `ℓ < L`, the Synthetic FFT size `t_{1,ℓ} = 2^{K_ℓ - K_{ℓ+1}}` divides the exact
multiplicative order `2 r_ℓ = 2 * 2^{K_{ℓ+1}}` of `y ∈ R_{r_ℓ}^×` proved in
`theorem7_5_negacyclicShiftIter_exact_order_two_mul_r`. -/
def AdmissibleRingSchedule (L : ℕ) (K : ℕ → ℕ) : Prop :=
  ∀ l < L, K (l + 1) ≤ K l ∧ 2 ^ (K l - K (l + 1)) ∣ 2 * 2 ^ (K (l + 1))

/-- **Ring-Divisibility Depth Bound for Admissible Schedules (`theorem7_5_admissible_schedule_depth_lower_bound`; omitted earlier `[MS]` draft)**:
For any schedule `K : ℕ → ℕ` satisfying `AdmissibleRingSchedule L K`, the ring divisibility
`2 ^ (K ℓ - K (ℓ + 1)) ∣ 2 * 2 ^ (K (ℓ + 1))` implies `K ℓ ≤ 2 * K (ℓ + 1) + 1` at every level
`ℓ < L`, and induction on `L` yields `K 0 + 1 ≤ 2 ^ L * (K L + 1)`. -/
theorem theorem7_5_admissible_schedule_depth_lower_bound
    (L : ℕ) (K : ℕ → ℕ) (hK : AdmissibleRingSchedule L K) :
    (∀ l < L, K l ≤ 2 * K (l + 1) + 1) ∧
    K 0 + 1 ≤ 2 ^ L * (K L + 1) := by
  have hstep : ∀ l < L, K l ≤ 2 * K (l + 1) + 1 := by
    intro l hl
    rcases hK l hl with ⟨hle, hdvd⟩
    have hpow : 2 * 2 ^ (K (l + 1)) = 2 ^ (K (l + 1) + 1) := by
      rw [pow_succ']
    rw [hpow] at hdvd
    have hle_pow : 2 ^ (K l - K (l + 1)) ≤ 2 ^ (K (l + 1) + 1) :=
      Nat.le_of_dvd (by positivity) hdvd
    have hexp : K l - K (l + 1) ≤ K (l + 1) + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle_pow
    omega
  refine ⟨hstep, ?_⟩
  clear hK
  induction L with
  | zero =>
    simp
  | succ L ih =>
    have ih' := ih (fun l hl => hstep l (Nat.lt_succ_of_lt hl))
    have hL : K L + 1 ≤ 2 * (K (L + 1) + 1) := by
      have := hstep L (Nat.lt_succ_self L)
      omega
    calc K 0 + 1 ≤ 2 ^ L * (K L + 1) := ih'
      _ ≤ 2 ^ L * (2 * (K (L + 1) + 1)) := Nat.mul_le_mul_left (2 ^ L) hL
      _ = 2 ^ (L + 1) * (K (L + 1) + 1) := by rw [pow_succ]; ring

/-! ## 7. Convolution Peak Witness, Pigeonhole Precision Bound & Carry Sensitivity (Omitted Earlier `[MS]` Draft Barrier Discussion) -/

/-- Max-digit radix-`2^b` chunk sequence of length `N`: every active chunk equals `2^b - 1`. -/
def maxChunkSeq (b N j : ℕ) : ℕ :=
  if j < N then 2 ^ b - 1 else 0

/-- **Convolution Peak & Precision Bound (Part A1: Unconditional Convolution Peak Witness; omitted earlier `[MS]` draft)**:
For any chunk width `b ≥ 1` and chunk count `N > 0`, the discrete convolution of `maxChunkSeq b N`
with itself at index `N - 1` equals `N * (2^b - 1)^2`, which is at least `N * 2^{2(b - 1)}`. -/
theorem theorem7_6_max_chunk_convolution_peak (b N : ℕ) (hb : 1 ≤ b) (_hN : 0 < N) :
    (∑ j ∈ Finset.range N, maxChunkSeq b N j * maxChunkSeq b N (N - 1 - j)) =
      N * (2 ^ b - 1) ^ 2 ∧
    N * 2 ^ (2 * (b - 1)) ≤
      ∑ j ∈ Finset.range N, maxChunkSeq b N j * maxChunkSeq b N (N - 1 - j) := by
  have hpeak : (∑ j ∈ Finset.range N, maxChunkSeq b N j * maxChunkSeq b N (N - 1 - j)) =
      N * (2 ^ b - 1) ^ 2 := by
    have hterm : ∀ j ∈ Finset.range N,
        maxChunkSeq b N j * maxChunkSeq b N (N - 1 - j) = (2 ^ b - 1) ^ 2 := by
      intro j hj
      have hj_lt : j < N := Finset.mem_range.mp hj
      have hsub_lt : N - 1 - j < N := by omega
      unfold maxChunkSeq
      rw [if_pos hj_lt, if_pos hsub_lt, sq]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
  refine ⟨hpeak, ?_⟩
  rw [hpeak]
  have hb_pow : 2 ^ (b - 1) ≤ 2 ^ b - 1 := by
    have hb_eq : b = (b - 1) + 1 := by omega
    have h1 : 2 ^ b = 2 * 2 ^ (b - 1) := by
      conv_lhs => rw [hb_eq, pow_succ']
    have h2 : 1 ≤ 2 ^ (b - 1) := Nat.one_le_pow (b - 1) 2 (by norm_num)
    omega
  have hsq : 2 ^ (2 * (b - 1)) ≤ (2 ^ b - 1) ^ 2 := by
    have : 2 ^ (2 * (b - 1)) = (2 ^ (b - 1)) ^ 2 := by
      rw [mul_comm, pow_mul]
    rw [this]
    exact Nat.pow_le_pow_left hb_pow 2
  exact Nat.mul_le_mul_left N hsq

/-- **Convolution Peak & Precision Bound (Part A2: Pigeonhole Precision Lower Bound from Convolution Peak; omitted earlier `[MS]` draft)**:
At `N = 2^{K_0 - 1}` (`1 ≤ K_0`, `1 ≤ b`), the convolution peak of `maxChunkSeq b N` is
`peak = 2^{K_0 - 1} * (2^b - 1)^2 ≥ 2^{K_0 - 1 + 2(b - 1)}`. By the finite-set Pigeonhole Principle
(`Fintype.card_le_of_injective`), any quantizer `Q : Fin (peak + 1) → Fin (2 ^ (p + 2))` that
injectively distinguishes the integer values `0 .. peak` must satisfy `K_0 + 2 * (b - 1) ≤ p + 2`. -/
theorem theorem7_6_precision_lower_bound_from_dynamic_range
    (b K0 p : ℕ) (hb : 1 ≤ b) (hK0 : 1 ≤ K0)
    (Q : Fin (2 ^ (K0 - 1) * (2 ^ b - 1) ^ 2 + 1) → Fin (2 ^ (p + 2)))
    (hQ : Function.Injective Q) :
    K0 + 2 * (b - 1) ≤ p + 2 := by
  have hcard : 2 ^ (K0 - 1) * (2 ^ b - 1) ^ 2 + 1 ≤ 2 ^ (p + 2) := by
    have h := Fintype.card_le_of_injective Q hQ
    simpa only [Fintype.card_fin] using h
  have hres : 2 ^ (K0 - 1) * (2 ^ b - 1) ^ 2 < 2 ^ (p + 2) := by omega
  have hpeak := (theorem7_6_max_chunk_convolution_peak b (2 ^ (K0 - 1)) hb (by positivity)).2
  rw [(theorem7_6_max_chunk_convolution_peak b (2 ^ (K0 - 1)) hb (by positivity)).1] at hpeak
  rw [← pow_add] at hpeak
  have hlt : 2 ^ (K0 - 1 + 2 * (b - 1)) < 2 ^ (p + 2) := lt_of_le_of_lt hpeak hres
  have hexp : K0 - 1 + 2 * (b - 1) < p + 2 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  omega

/-- `W`-bit modular addition `(x + y) mod 2^W` in a machine word. -/
def addMod2Pow (W x y : ℕ) : ℕ :=
  (x + y) % (2 ^ W)

/-- **Convolution Peak & Precision Bound (Part B: Boolean Carry-Propagation Sensitivity of Packed `W`-Bit Addition; omitted earlier `[MS]` draft)**:
For every bit position `i < W`, flipping bit `i` of the first operand from `x = 0` to `x' = 2^i`
when adding to `y = 2^W - 2^i < 2^W` triggers a carry ripple across all `W - i` upper bit positions
`i .. W - 1`, flipping the `W`-bit sum from `2^W - 2^i = 2^i * (2^{W - i} - 1) ≠ 0` to `0` (and
symmetrically for the second operand). Thus `addMod2Pow W` depends essentially on every input bit
`i < W` of both operands. -/
theorem theorem7_6_packed_addition_sensitivity (W i : ℕ) (hi : i < W) :
    let x := 0
    let x' := 2 ^ i
    let y := 2 ^ W - 2 ^ i
    x < 2 ^ W ∧ x' < 2 ^ W ∧ y < 2 ^ W ∧
    addMod2Pow W x y = 2 ^ W - 2 ^ i ∧
    addMod2Pow W x' y = 0 ∧
    addMod2Pow W x y ≠ addMod2Pow W x' y ∧
    addMod2Pow W y x ≠ addMod2Pow W y x' ∧
    addMod2Pow W x y / 2 ^ i = 2 ^ (W - i) - 1 := by
  dsimp only
  have hi_pow : 2 ^ i < 2 ^ W := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr hi
  have hi_pos : 0 < 2 ^ i := by positivity
  have hW_pos : 0 < 2 ^ W := by positivity
  have hy_lt : 2 ^ W - 2 ^ i < 2 ^ W := by omega
  have hxy : addMod2Pow W 0 (2 ^ W - 2 ^ i) = 2 ^ W - 2 ^ i := by
    unfold addMod2Pow
    rw [zero_add, Nat.mod_eq_of_lt hy_lt]
  have hx'y : addMod2Pow W (2 ^ i) (2 ^ W - 2 ^ i) = 0 := by
    unfold addMod2Pow
    have hsum : 2 ^ i + (2 ^ W - 2 ^ i) = 2 ^ W := by omega
    rw [hsum, Nat.mod_self]
  have hne : addMod2Pow W 0 (2 ^ W - 2 ^ i) ≠ addMod2Pow W (2 ^ i) (2 ^ W - 2 ^ i) := by
    rw [hxy, hx'y]
    omega
  have hne_symm : addMod2Pow W (2 ^ W - 2 ^ i) 0 ≠ addMod2Pow W (2 ^ W - 2 ^ i) (2 ^ i) := by
    unfold addMod2Pow at hne ⊢
    rwa [add_comm (2 ^ W - 2 ^ i) 0, add_comm (2 ^ W - 2 ^ i) (2 ^ i)]
  have hdiv : addMod2Pow W 0 (2 ^ W - 2 ^ i) / 2 ^ i = 2 ^ (W - i) - 1 := by
    rw [hxy]
    have hW_eq : W = i + (W - i) := by omega
    have hmul : 2 ^ W - 2 ^ i = 2 ^ i * (2 ^ (W - i) - 1) := by
      have h1 : 2 ^ W = 2 ^ i * 2 ^ (W - i) := by
        conv_lhs => rw [hW_eq, pow_add]
      rw [h1, Nat.mul_sub_left_distrib, mul_one]
    rw [hmul, Nat.mul_div_right _ hi_pos]
  exact ⟨hW_pos, hi_pow, hy_lt, hxy, hx'y, hne, hne_symm, hdiv⟩

end IntMul
