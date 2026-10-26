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

set_option backward.isDefEq.respectTransparency false

/-!
# End-to-End $O(n \log n)$ Complexity Recurrence, Computable Pipeline & Uniform `FinTM2` Primitives (`IntMul.EndToEnd`)

This module implements:
1. **Multi-Level Recurrence Work Summation, Program-Synchronized Step Recurrence,
   and Unconditional $O(n \log n)$ Upper Bound (Theorem 1 (`thm:main`), proof Parts 2–3 in
   Section 7.2 (`sec:cost-proof`), and Section 8 (`sec:lean`))**:
   - Exact grid conservation `numSubproblems_mul_levelR_eq` (`numSubproblems K0 ell * levelR K0 ell = levelR K0 0`).
   - Log-length halving bounds `two_pow_mul_levelK_le_add_pow`, `two_pow_mul_levelK_le`,
     `two_pow_succ_mul_k1Ell_levelK_le`, and exact geometric butterfly contraction
     `two_pow_mul_k1Ell_levelK_le` / `k1Ell_levelK_le_mul_zpow_neg`.
   - Per-level polynomial-transform (`syntheticFFT` in this development) butterfly stage work
     contraction (`levelButterflyStageWork_le_geom`, `multiLevel_work_sum_lt_two_mul_of_level_le`,
     `levelButterflyStageWork_sum_lt_two_mul`, and explicit bridge
     `subproblemButterflyStageWork_le_step2SyntheticFFTOps`, corresponding to equation (38) (`eq:syn-route-total`)).
   - **Computable Program-Synchronized Recursive Step/Operation Recurrence
     (`computableFastDFTRecursiveSteps`, `fastDFTRecursiveSteps`, `scheduleTreeGenOps`,
     `intMulAlgorithmSteps`)**:
     counts the exact recursive operations of `computeScheduleIntTree` and
     `computableFastDFTRecursive` / `fastDFTRecursiveSched` across internal nodes (`step1SpreadOps`
     for blocked Kronecker Overlap-Add, `step2SyntheticFFTOps` for the multiplication-free
     $\mathbb{C}[y]/(y^r+1)$ butterfly stages, `stepFixedPointMuls` for the $O(R_\ell)$ blocked
     Kronecker, pre/post-twist, and bidiagonal multiplications with zero butterfly twiddle
     multiplications, `t1Ell K` recursive child calls, and `step3DeconvOps`) and leaf nodes
     (`leafDFTOps` for the $O(K \cdot 2^K)$ Cooley–Tukey radix-2 butterfly leaf FFT).
   - **Unconditional $O(n \log n)$ Upper Bound Theorems (`fastDFTRecursiveSteps_level_le`,
     `fastDFTRecursiveSteps_root_le`, `scheduleTreeGenOps_root_le`,
     `scheduleTreeGenOps_subMulBitOps_root_le`, `scheduleTreeGenOps_nestedSubMulBitOps_root_le`,
     `intMulAlgorithmSteps_le_n_log_n_succ`, `intMulAlgorithmSteps_le_n_log_n`,
     `exists_uniform_C_intMulAlgorithmSteps_le`, `subMulBitOps`, `leafDFTOps_subMulBitOps_level_le`,
     `fastDFTRecursiveSteps_subMulBitOps_level_le`, `fastDFTRecursiveSteps_subMulBitOps_root_le`,
     `intMulAlgorithmSteps_subMulBitOps_le_n_log_n_succ`, `intMulAlgorithmSteps_subMulBitOps_le_n_log_n`,
     `exists_uniform_C_intMulAlgorithmSteps_subMulBitOps_le`)**:
     proves that for all $n \ge 2$, `intMulAlgorithmSteps (fun q => q) n ≤ 554318656216818525452 * n * Nat.log 2 n`,
     `intMulAlgorithmSteps subMulBitOps n ≤ 554318656216922194220 * n * Nat.log 2 n`, and
     `intMulAlgorithmSteps nestedSubMulBitOps n = O(n \log n)`.

2. **End-to-End Bit-Level Multiplication Pipelines & Intrinsically Operation-Tracking `CostM`
   Execution (`intMulPipelineBits`, `intMulSchedPipelineBits`, `computableIntMulPipelineBits`,
   `computableIntMulBits`, `computableNatMulBits`, `computableNatMulTracked`,
   `computableNatMulBitsTracked`)**:
   - Unconditional bit-exactness of the analytic `fastDFTRecursive` pipeline (`intMulPipelineBits_encodeInputBits`),
     the schedule-driven `fastDFTRecursiveSched` pipeline (`intMulSchedPipelineBits_encodeInputBits`),
     the computable pure-integer `computableReconstructProduct` pipeline on `canonicalScheduleIntTree`
     (`computableIntMulPipelineBits_canonical_encodeInputBits`) and on `computeScheduleIntTree`
     (`computableIntMulPipelineBits_computeScheduleIntTree_encodeInputBits`), the parameter-free
     computable pipeline `computableIntMulBits` (`computableIntMulBits_encodeInputBits`), and
     the self-recursive pure-integer pipeline `computableNatMulBits` (`computableNatMulBits_encodeInputBits`).
   - Intrinsically operation-tracking `CostM` functions (`computeScheduleIntTreeWithMulTracked`,
     `computableFastDFTRecursiveWithMulTracked`, `computableConvFromChunksWithMulTracked`,
     `carrySaveEmitBitsTracked`, `computableNatMulBitsAuxTracked`,
     `computableNatMulTracked`, `computableNatMulBitsTracked`) that accumulate operation counts
     bottom-up with **zero** calls to any formula cost and **no** free `M_mul` parameter on the
     self-recursive multiplier, paired with single-statement $O(n \log n)$ theorems
     (`computableNatMulTracked_spec`, `computableNatMulBitsTracked_spec`, Table 3 (`tab:lean-map`) in Section 8 (`sec:lean`)).

3. **Inhabited Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Suites, Compile-Time AST Audit,
   and Unconditional End-to-End Summary**:
   - Packages the 9 inhabited single-machine uniform 8-stack binary machine (`Turing.FinTM2`)
     primitives (`tmUniformRevCopy`, `tmUniformIdCopy`, `tmUniformDeinterleave`, `tmUniformInterleave`,
     `tmUniformRippleAdd`, `tmUniformRippleSub`, `tmUniformButterflyAddSub`, `tmUniformBitMulAdd`,
     `tmUniformCondSubStep`) into `UniformTMPrimitiveSuite` (`canonicalUniformTMPrimitiveSuite`),
     and packages the composed multi-stage 8-stack binary machines (`Turing.FinTM2`) in
     `IntMul.TMComposition` (`seqBitFinTM2`, `loopTapeBitFinTM2`, `tmComposedIdCopy`,
     `tmComposedDeinterleaveInterleave`, `tmComposedOrderPreservingShuffle`,
     `tmComposedMultiPassTranspose`, `tmComposedButterflyStage`, `tmComposedCondSubPass`,
     `tmUniformSignedButterflyAddSub`, `tmComposedSignedButterflyStage`, `tmSingleTapeSignedAdd`,
     `tmSingleTapeSignedButterfly`) into `UniformTMCompositionSuite`
     (`canonicalUniformTMCompositionSuite`), while the end-to-end 8-stack binary machine
     (`Turing.FinTM2`) `tmIntMul` (`tmIntMul_evalsToInTime_n_log_n` in `TM2.step` transitions on 8 binary stacks,
     `intMul_complete_endToEnd_summary`, Theorem 2 (`thm:lean`) in Section 8 (`sec:lean`)) is
     constructed and proved in `IntMul.TMEndToEnd`.
   - Executes a compile-time metaprogramming AST audit (`auditTrackedDeclarations`,
     `#verify_tracked_declarations_ast_audit`) over all `IntMul.*Tracked` definitions in
     the Lean environment, verifying that no `*Tracked` declaration references any closed-form
     `*Ops` / `intMulAlgorithmSteps` cost formula, any forbidden wide-integer Horner packing/unpacking
     helper (`evalSignedSlots`, `unpackSignedSlots`, `extractNatChunks`, `natChunkFn`,
     `evalBaseChunks`), or any untracked composite pipeline function.
-/

namespace IntMul

open scoped BigOperators ComplexConjugate

/-! ## 1. Multi-Level Recurrence Work Summation, Program-Synchronized Step Recurrence & Unconditional $O(n \log n)$ Bound (Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`)) -/

/-- Number of recursive subproblems $\prod_{j < \ell} t_{1,j} = R_0 / R_\ell$ at recursion depth $\ell$
(Section 7.2 (`sec:cost-proof`)). -/
def numSubproblems (K0 ell : ℕ) : ℕ :=
  ∏ j ∈ Finset.range ell, t1Ell (levelK K0 j)

@[simp]
theorem numSubproblems_zero (K0 : ℕ) : numSubproblems K0 0 = 1 := rfl

theorem numSubproblems_succ (K0 ell : ℕ) :
    numSubproblems K0 (ell + 1) = numSubproblems K0 ell * t1Ell (levelK K0 ell) := by
  unfold numSubproblems
  exact Finset.prod_range_succ _ ell

/-- **Exact Subproblem Grid Conservation (`numSubproblems_mul_levelR_eq`, Section 7.2 (`sec:cost-proof`))**:
At every recursion depth $\ell$, the number of subproblems times the subproblem size $R_\ell$
equals $R_0 = 2^{K_0}$ with zero grid expansion. -/
theorem numSubproblems_mul_levelR_eq (K0 ell : ℕ) :
    numSubproblems K0 ell * levelR K0 ell = levelR K0 0 := by
  induction ell with
  | zero =>
    simp [numSubproblems_zero]
  | succ ell ih =>
    rw [numSubproblems_succ, mul_assoc]
    have hstep : t1Ell (levelK K0 ell) * levelR K0 (ell + 1) = levelR K0 ell := by
      change t1Ell (levelK K0 ell) * rEll (levelK K0 ell) = 2 ^ levelK K0 ell
      exact t1Ell_mul_rEll (levelK K0 ell)
    rw [hstep, ih]

/-- **Log-Length Halving Bound (`two_pow_mul_levelK_le_add_pow`, Section 7.2 (`sec:cost-proof`))**:
At every recursion depth $\ell$, $2^\ell \cdot K_\ell \le K_0 + 2^\ell$. -/
theorem two_pow_mul_levelK_le_add_pow (K0 ell : ℕ) :
    2 ^ ell * levelK K0 ell ≤ K0 + 2 ^ ell := by
  have h1 := levelK_le_div_two_pow_add_one K0 ell
  have h2 : 2 ^ ell * ((K0 - 1) / 2 ^ ell) ≤ K0 - 1 :=
    Nat.mul_div_le (K0 - 1) (2 ^ ell)
  calc
    2 ^ ell * levelK K0 ell ≤ 2 ^ ell * ((K0 - 1) / 2 ^ ell + 1) :=
      Nat.mul_le_mul_left (2 ^ ell) h1
    _ = 2 ^ ell * ((K0 - 1) / 2 ^ ell) + 2 ^ ell := by ring
    _ ≤ (K0 - 1) + 2 ^ ell := Nat.add_le_add_right h2 (2 ^ ell)
    _ ≤ K0 + 2 ^ ell := by omega

/-- Corollary of `two_pow_mul_levelK_le_add_pow`: $2^\ell \cdot K_\ell \le K_0 + 2^{\ell + 1}$ (Section 7.2 (`sec:cost-proof`)). -/
theorem two_pow_mul_levelK_le (K0 ell : ℕ) :
    2 ^ ell * levelK K0 ell ≤ K0 + 2 ^ (ell + 1) := by
  have h := two_pow_mul_levelK_le_add_pow K0 ell
  have hpow : 2 ^ ell ≤ 2 ^ (ell + 1) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_succ ell)
  omega

/-- **First-Axis Butterfly Stage Halving Bound (`two_pow_succ_mul_k1Ell_levelK_le`, Section 7.2 (`sec:cost-proof`))**:
At every recursion depth $\ell$, the number of polynomial-transform (`syntheticFFT` in this
development) butterfly stages $k_{1,\ell} = \lfloor K_\ell / 2 \rfloor = \log_2 t_{1,\ell}$ satisfies
$2^{\ell + 1} \cdot k_{1,\ell} \le K_0 + 2^\ell$. -/
theorem two_pow_succ_mul_k1Ell_levelK_le (K0 ell : ℕ) :
    2 ^ (ell + 1) * k1Ell (levelK K0 ell) ≤ K0 + 2 ^ ell := by
  unfold k1Ell
  have hdiv : 2 * (levelK K0 ell / 2) ≤ levelK K0 ell := Nat.mul_div_le (levelK K0 ell) 2
  have h := two_pow_mul_levelK_le_add_pow K0 ell
  calc
    2 ^ (ell + 1) * (levelK K0 ell / 2)
      = 2 ^ ell * (2 * (levelK K0 ell / 2)) := by rw [pow_succ]; ring
    _ ≤ 2 ^ ell * levelK K0 ell := Nat.mul_le_mul_left (2 ^ ell) hdiv
    _ ≤ K0 + 2 ^ ell := h

/-- **Exact Butterfly Stage Geometric Contraction (`two_pow_mul_k1Ell_levelK_le`, Section 7.2 (`sec:cost-proof`))**:
At every recursion depth $\ell$, $2^\ell \cdot k_{1,\ell} \le K_0$ with zero additive slack, since
$k_{1,\ell} = \lfloor K_\ell / 2 \rfloor \le \lfloor (\lfloor (K_0 - 1)/2^\ell \rfloor + 1)/2 \rfloor \le \lfloor (K_0 - 1)/2^\ell \rfloor$. -/
theorem two_pow_mul_k1Ell_levelK_le (K0 ell : ℕ) :
    2 ^ ell * k1Ell (levelK K0 ell) ≤ K0 := by
  have h1 : levelK K0 ell ≤ (K0 - 1) / 2 ^ ell + 1 :=
    levelK_le_div_two_pow_add_one K0 ell
  have hdiv2 : ∀ m a : ℕ, m ≤ a + 1 → m / 2 ≤ a := by omega
  have h2 : k1Ell (levelK K0 ell) ≤ (K0 - 1) / 2 ^ ell :=
    hdiv2 (levelK K0 ell) ((K0 - 1) / 2 ^ ell) h1
  have h3 : 2 ^ ell * ((K0 - 1) / 2 ^ ell) ≤ K0 - 1 :=
    Nat.mul_div_le (K0 - 1) (2 ^ ell)
  calc
    2 ^ ell * k1Ell (levelK K0 ell)
      ≤ 2 ^ ell * ((K0 - 1) / 2 ^ ell) := Nat.mul_le_mul_left (2 ^ ell) h2
    _ ≤ K0 - 1 := h3
    _ ≤ K0 := Nat.sub_le K0 1

/-- Real geometric decay bound $k_{1,\ell} \le K_0 \cdot 2^{-\ell}$ derived from
`two_pow_mul_k1Ell_levelK_le` (Section 7.2 (`sec:cost-proof`)). -/
theorem k1Ell_levelK_le_mul_zpow_neg (K0 ell : ℕ) :
    (k1Ell (levelK K0 ell) : ℝ) ≤ (K0 : ℝ) * (2 : ℝ) ^ (-(ell : ℤ)) := by
  have hnat := two_pow_mul_k1Ell_levelK_le K0 ell
  have hreal : (2 : ℝ) ^ ell * (k1Ell (levelK K0 ell) : ℝ) ≤ (K0 : ℝ) := by
    exact_mod_cast hnat
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ (-(ell : ℤ)) := zpow_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_right hreal (le_of_lt hzpos)
  have hcancel : (2 : ℝ) ^ ell * (k1Ell (levelK K0 ell) : ℝ) * (2 : ℝ) ^ (-(ell : ℤ)) =
      (k1Ell (levelK K0 ell) : ℝ) := by
    calc
      (2 : ℝ) ^ ell * (k1Ell (levelK K0 ell) : ℝ) * (2 : ℝ) ^ (-(ell : ℤ))
        = ((2 : ℝ) ^ ell * (2 : ℝ) ^ (-(ell : ℤ))) * (k1Ell (levelK K0 ell) : ℝ) := by ring
      _ = (k1Ell (levelK K0 ell) : ℝ) := by rw [two_pow_mul_two_zpow_neg ell, one_mul]
  rwa [hcancel] at hmul

/-- Uniform linear precision bound across all active recursion levels $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$:
`levelP (rootK0 n) (rootP0 n) ell ≤ 11 * rootP0 n` (Section 7.2 (`sec:cost-proof`)). -/
theorem levelP_le_eleven_mul_rootP0 {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n)) :
    levelP (rootK0 n) (rootP0 n) ell ≤ 11 * rootP0 n := by
  have hp_le := levelP_le (rootK0 n) (rootP0 n) ell
  have hrec := recursionDepth_le_K0 (rootK0 n) (rootP0 n)
  have hp0_eq : rootP0 n = 2 * chunkBits n + 2 * rootK0 n + 6 := rfl
  omega

/-- **Conditional Geometric Contraction of Multi-Level Work (`multiLevel_work_sum_lt_two_mul_of_level_le`,
Theorem 1 (`thm:main`), proof Part 2 in Section 7.2 (`sec:cost-proof`), equation (38) (`eq:syn-route-total`))**:
Under the positivity hypothesis `hW0 : 0 < W0` and the per-level geometric contraction hypothesis
`hlevel : ∀ ell ∈ Finset.range L, W ell ≤ W0 * (2 : ℝ) ^ (-(ell : ℤ))`, the cumulative work
`∑ ell ∈ Finset.range L, W ell` across all $L$ levels is strictly bounded by `2 * W0`. -/
theorem multiLevel_work_sum_lt_two_mul_of_level_le {L : ℕ} {W : ℕ → ℝ} {W0 : ℝ}
    (hW0 : 0 < W0)
    (hlevel : ∀ ell ∈ Finset.range L, W ell ≤ W0 * (2 : ℝ) ^ (-(ell : ℤ))) :
    (∑ ell ∈ Finset.range L, W ell) < 2 * W0 := by
  calc
    (∑ ell ∈ Finset.range L, W ell)
      ≤ ∑ ell ∈ Finset.range L, W0 * (2 : ℝ) ^ (-(ell : ℤ)) :=
        Finset.sum_le_sum hlevel
    _ = W0 * ∑ ell ∈ Finset.range L, (2 : ℝ) ^ (-(ell : ℤ)) := by
        rw [← Finset.mul_sum]
    _ < W0 * 2 :=
        mul_lt_mul_of_pos_left (geom_sum_two_zpow_neg_lt_two L) hW0
    _ = 2 * W0 := mul_comm W0 2

/-- Per-subproblem polynomial-transform (`syntheticFFT` in this development) butterfly stage bit-work
at log-size $K_\ell$ and precision $p_\ell$:
$R_\ell \cdot p_\ell \cdot k_{1,\ell} = 2^{K_\ell} \cdot p_\ell \cdot \lfloor K_\ell / 2 \rfloor$
(Theorem 1 (`thm:main`), proof Part 2 in Section 7.2 (`sec:cost-proof`)). -/
noncomputable def subproblemButterflyStageWork (K p : ℕ) : ℝ :=
  ((2 ^ K : ℕ) : ℝ) * (p : ℝ) * (k1Ell K : ℝ)

/-- Per-level polynomial-transform butterfly stage bit-work across all `numSubproblems (rootK0 n) ell`
subproblems at recursion depth $\ell$ for `cSpec n` (Theorem 1 (`thm:main`), proof Part 2 in Section 7.2 (`sec:cost-proof`)). -/
noncomputable def levelButterflyStageWork (n ell : ℕ) : ℝ :=
  (numSubproblems (rootK0 n) ell : ℝ) *
    subproblemButterflyStageWork (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)

/-- **Per-Level Geometric Contraction Theorem for `levelButterflyStageWork`
(`levelButterflyStageWork_le_geom`, Theorem 1 (`thm:main`), proof Part 2 in Section 7.2 (`sec:cost-proof`))**:
For every $n \in \mathbb{N}$ and every active recursion level $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$,
$$\text{levelButterflyStageWork } n \, \ell \le \left(11 \cdot R_0 \cdot p_0 \cdot K_0\right) 2^{-\ell}.$$ -/
theorem levelButterflyStageWork_le_geom {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n)) :
    levelButterflyStageWork n ell ≤
      (11 * (rootR0 n : ℝ) * (rootP0 n : ℝ) * (rootK0 n : ℝ)) * (2 : ℝ) ^ (-(ell : ℤ)) := by
  unfold levelButterflyStageWork subproblemButterflyStageWork
  have hgrid : (numSubproblems (rootK0 n) ell : ℝ) * ((2 ^ levelK (rootK0 n) ell : ℕ) : ℝ) =
      (rootR0 n : ℝ) := by
    have hnat : numSubproblems (rootK0 n) ell * 2 ^ levelK (rootK0 n) ell = rootR0 n :=
      numSubproblems_mul_levelR_eq (rootK0 n) ell
    exact_mod_cast hnat
  have hp : (levelP (rootK0 n) (rootP0 n) ell : ℝ) ≤ 11 * (rootP0 n : ℝ) := by
    exact_mod_cast levelP_le_eleven_mul_rootP0 hell
  have hk1 : (k1Ell (levelK (rootK0 n) ell) : ℝ) ≤
      (rootK0 n : ℝ) * (2 : ℝ) ^ (-(ell : ℤ)) :=
    k1Ell_levelK_le_mul_zpow_neg (rootK0 n) ell
  have hR0_nn : (0 : ℝ) ≤ (rootR0 n : ℝ) := Nat.cast_nonneg _
  have hp0_nn : (0 : ℝ) ≤ 11 * (rootP0 n : ℝ) := by positivity
  calc
    (numSubproblems (rootK0 n) ell : ℝ) *
        (((2 ^ levelK (rootK0 n) ell : ℕ) : ℝ) *
          (levelP (rootK0 n) (rootP0 n) ell : ℝ) *
          (k1Ell (levelK (rootK0 n) ell) : ℝ))
      = ((numSubproblems (rootK0 n) ell : ℝ) * ((2 ^ levelK (rootK0 n) ell : ℕ) : ℝ)) *
          ((levelP (rootK0 n) (rootP0 n) ell : ℝ) * (k1Ell (levelK (rootK0 n) ell) : ℝ)) := by ring
    _ = (rootR0 n : ℝ) *
          ((levelP (rootK0 n) (rootP0 n) ell : ℝ) * (k1Ell (levelK (rootK0 n) ell) : ℝ)) := by
        rw [hgrid]
    _ ≤ (rootR0 n : ℝ) *
          ((11 * (rootP0 n : ℝ)) * ((rootK0 n : ℝ) * (2 : ℝ) ^ (-(ell : ℤ)))) := by
        apply mul_le_mul_of_nonneg_left _ hR0_nn
        exact mul_le_mul hp hk1 (Nat.cast_nonneg _) hp0_nn
    _ = (11 * (rootR0 n : ℝ) * (rootP0 n : ℝ) * (rootK0 n : ℝ)) * (2 : ℝ) ^ (-(ell : ℤ)) := by ring

/-- **Unconditional Multi-Level Butterfly Stage Work Summation Bound for `cSpec n`
(`levelButterflyStageWork_sum_lt_two_mul`, Theorem 1 (`thm:main`), proof Part 2 in
Section 7.2 (`sec:cost-proof`), equation (38) (`eq:syn-route-total`))**:
For every $n \in \mathbb{N}$, the cumulative polynomial-transform butterfly stage bit-work across all
recursion levels $\ell < \text{recursionDepth (rootK0 n) (rootP0 n)}$ satisfies
`∑ ell ∈ Finset.range (recursionDepth (rootK0 n) (rootP0 n)), levelButterflyStageWork n ell ≤ 2 * (11 * rootR0 n * rootP0 n * rootK0 n)`. -/
theorem levelButterflyStageWork_sum_lt_two_mul (n : ℕ) :
    (∑ ell ∈ Finset.range (recursionDepth (rootK0 n) (rootP0 n)), levelButterflyStageWork n ell) ≤
      2 * (11 * (rootR0 n : ℝ) * (rootP0 n : ℝ) * (rootK0 n : ℝ)) := by
  have hR0 : 0 < (rootR0 n : ℝ) := by
    have := rootR0_ge_four n
    positivity
  have hp0 : 0 < (rootP0 n : ℝ) := by
    have := rootP0_ge_eighteen n
    positivity
  have hK0 : 0 < (rootK0 n : ℝ) := by
    have := rootK0_ge_two n
    positivity
  have hW0 : 0 < 11 * (rootR0 n : ℝ) * (rootP0 n : ℝ) * (rootK0 n : ℝ) := by positivity
  have hlt := multiLevel_work_sum_lt_two_mul_of_level_le
    (L := recursionDepth (rootK0 n) (rootP0 n))
    (W := levelButterflyStageWork n)
    (W0 := 11 * (rootR0 n : ℝ) * (rootP0 n : ℝ) * (rootK0 n : ℝ))
    hW0
    (fun ell hell => levelButterflyStageWork_le_geom (le_of_lt (Finset.mem_range.mp hell)))
  exact le_of_lt hlt

/-- **Step 1 Blocked Kronecker Overlap-Add Bit-Operation Count (`step1SpreadOps`,
Theorem 4.2 (`thm:poisson`), Theorem 6.3 (`thm:spread`), and Section 7.2 (`sec:cost-proof`))**:
Computable bit-operation count of Step 1 (`kroneckerMatrixSpreadFixedWithMul`) at an internal node
`(K, p, B_in)`: across `t1Ell K` rows and `numBlocks (rEll K) W_tilde` blocks per row
(where `W_tilde = foldedHalfWidth (computeM1Ell K p) (rEll K)` and
`B_slot = scheduleSlotBits K p B_in (computeM1Ell K p)`), packs/unpacks the two Kronecker
integers (`P_re`, `P_im`) of bit-length `kroneckerPackedBitLength W_tilde B_slot = 3 * W_tilde * B_slot`. -/
def step1SpreadOps (K p B_in : ℕ) : ℕ :=
  let W_tilde := foldedHalfWidth (computeM1Ell K p) (rEll K)
  let B_slot := scheduleSlotBits K p B_in (computeM1Ell K p)
  2 * (t1Ell K * numBlocks (rEll K) W_tilde * kroneckerPackedBitLength W_tilde B_slot)

/-- **Window-Width Cancellation for `step1SpreadOps` (`step1SpreadOps_le`,
Theorem 6.3 (`thm:spread`) and equation (33) (`eq:spread-cost`))**:
Across all `t1Ell K * numBlocks (rEll K) W_tilde` blocks, the block half-width `W_tilde` cancels
via `totalKroneckerPackedBits_le`, bounding `step1SpreadOps K p B_in` by
`12 * (2 ^ K) * scheduleSlotBits K p B_in (computeM1Ell K p)`. -/
theorem step1SpreadOps_le (K p B_in : ℕ) :
    step1SpreadOps K p B_in ≤
      12 * (2 ^ K) * scheduleSlotBits K p B_in (computeM1Ell K p) := by
  unfold step1SpreadOps
  dsimp only
  set W_tilde := foldedHalfWidth (computeM1Ell K p) (rEll K)
  set B_slot := scheduleSlotBits K p B_in (computeM1Ell K p)
  have hpack := totalKroneckerPackedBits_le (t1Ell K) (rEll K) W_tilde B_slot
    (foldedHalfWidth_le_right (computeM1Ell K p) (rEll K))
  have ht1r : t1Ell K * rEll K = 2 ^ K := t1Ell_mul_rEll K
  rw [ht1r] at hpack
  calc 2 * (t1Ell K * numBlocks (rEll K) W_tilde * kroneckerPackedBitLength W_tilde B_slot)
      ≤ 2 * (6 * (2 ^ K) * B_slot) := Nat.mul_le_mul_left 2 hpack
    _ = 12 * (2 ^ K) * B_slot := by ring

/-- **Step 2 Polynomial-Transform Bit-Operation Count (`step2SyntheticFFTOps`,
Lemma 3.5 (`lem:syn-fft`) and Proposition 4.1 (`thm:twisted`))**:
Counts the linear bit-shift and butterfly addition operations of Step 2 (`FixedComplex.mulRoundedWith` /
`FixedComplex.mulRounded` pre- and post-twists plus `radix2SyntheticFFTFixed` across `k1Ell K`
multiplication-free butterfly stages in $\mathbb{C}[y]/(y^r+1)$) across all `2 ^ K` grid points at `qChildEll K p`. -/
def step2SyntheticFFTOps (K p : ℕ) : ℕ :=
  (2 + k1Ell K) * (2 ^ K) * qChildEll K p

/-- Explicit bridge between `subproblemButterflyStageWork` and `step2SyntheticFFTOps`:
`subproblemButterflyStageWork K p ≤ (step2SyntheticFFTOps K p : ℝ)`. -/
theorem subproblemButterflyStageWork_le_step2SyntheticFFTOps (K p : ℕ) :
    subproblemButterflyStageWork K p ≤ (step2SyntheticFFTOps K p : ℝ) := by
  unfold subproblemButterflyStageWork step2SyntheticFFTOps
  have h1 : k1Ell K ≤ 2 + k1Ell K := by omega
  have h2 : p ≤ qChildEll K p := by
    unfold qChildEll pChildEll pWorkEll
    omega
  have hnat : (2 ^ K) * p * k1Ell K ≤ (2 + k1Ell K) * (2 ^ K) * qChildEll K p := by
    calc
      (2 ^ K) * p * k1Ell K
        = k1Ell K * (2 ^ K) * p := by ring
      _ ≤ (2 + k1Ell K) * (2 ^ K) * qChildEll K p :=
        Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) h1) h2
  exact_mod_cast hnat

/-- **Step 3 Cyclic Bidiagonal Deconvolution Bit-Operation Count (`step3DeconvOps`,
Theorem 5.1 (`thm:deconv`) and Section 5.2 (`sec:solvers`))**:
Counts the linear column-sweep operations of Step 3 (`cyclicBidiagPrevSolveFixed` /
`nyquistColumnSolveFixed` and `freqScatter`) across all `2 ^ K` grid points at working precision
`qChildEll K p`. -/
def step3DeconvOps (K p : ℕ) : ℕ :=
  8 * (2 ^ K) * qChildEll K p

/-- **Internal-Node Fixed-Point Sub-Multiplication & Division Operation Count (`stepFixedPointMuls`,
Section 7.2 (`sec:cost-proof`))**:
Computable count of all fixed-point multiplications and divisions at an internal node `(K, p, B_in)`
given a sub-multiplication cost function `M_mul : ℕ → ℕ`:
- Step 1 blocked Kronecker substitution products: `2 * t1Ell K * numBlocks (rEll K) W_tilde`
  packed integer products of bit-length `kroneckerPackedBitLength W_tilde B_slot = 3 * W_tilde * B_slot`
  (where `W_tilde = foldedHalfWidth (computeM1Ell K p) (rEll K)` and
  `B_slot = scheduleSlotBits K p B_in (computeM1Ell K p)`),
- Step 2 pre-twist and post-twist (`8` real sub-multiplications per grid point; **zero** inside the
  $k_{1,\ell}$ multiplication-free $\mathbb{C}[y]/(y^r+1)$ butterfly stages), and
- Step 3 bidiagonal column-sweep multiplications and `divScalarFixed` divisions (`8` per grid point). -/
def stepFixedPointMuls (K p B_in : ℕ) (M_mul : ℕ → ℕ) : ℕ :=
  let W_tilde := foldedHalfWidth (computeM1Ell K p) (rEll K)
  let B_slot := scheduleSlotBits K p B_in (computeM1Ell K p)
  2 * (t1Ell K * numBlocks (rEll K) W_tilde * M_mul (kroneckerPackedBitLength W_tilde B_slot)) +
    16 * (2 ^ K) * M_mul (qChildEll K p)

/-- **Base-Case Cooley–Tukey Radix-2 Leaf FFT Operation Count (`leafDFTOps`,
Lemma 6.5(2) (`lem:forward`) and Section 7.2 (`sec:cost-proof`))**:
Counts the operations of the $K$-stage Cooley–Tukey radix-2 butterfly leaf FFT (`baseRadix2FFTFixed` /
`radix2FFT1DFixed` when `2 ^ K ≤ 4 * p ^ 2` or `K < 2`) across `K + 1` stages of `2 ^ K` points
at leaf precision `qBaseEll K p`, including both butterfly additions/subtractions and twiddle
sub-multiplications `M_mul (qBaseEll K p)`. -/
def leafDFTOps (K p : ℕ) (M_mul : ℕ → ℕ) : ℕ :=
  (K + 1) * (2 ^ K) * (qBaseEll K p + M_mul (qBaseEll K p))

/-- **Computable Program-Synchronized Recursive Step/Operation Recurrence for `computableFastDFTRecursive`
(`computableFastDFTRecursiveSteps`, Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`))**:
Follows the **exact same `ScheduleIntTree` recursion tree** as `computableFastDFTRecursive`,
passing each node's `B_in` into `step1SpreadOps` and `stepFixedPointMuls`. -/
def computableFastDFTRecursiveSteps (M_mul : ℕ → ℕ) {K p B_in : ℕ}
    (tree : ScheduleIntTree K p B_in) : ℕ :=
  match tree with
  | .leaf K p _B_in _leafRoots =>
    leafDFTOps K p M_mul
  | .node K p B_in _m1 _filterTap _pre _post _c0 _c1 child =>
    step1SpreadOps K p B_in +
      step2SyntheticFFTOps K p +
      stepFixedPointMuls K p B_in M_mul +
      t1Ell K * computableFastDFTRecursiveSteps M_mul child +
      step3DeconvOps K p

/-- **Computable Program-Synchronized Recursive Step/Operation Recurrence for `fastDFTRecursiveSched` /
`computableFastDFTRecursive` (`fastDFTRecursiveSteps`, Section 7.1 (`sec:alg-spec`) and
Section 7.2 (`sec:cost-proof`))**:
Follows the **exact same recursion tree and branching condition** `(!isBaseLeaf K p) = true ∧ 2 ≤ K`
as `computeScheduleIntTree`, `canonicalScheduleIntTree`, `fastDFTRecursiveSched`, and
`computableFastDFTRecursive`:
- At an internal node (`!isBaseLeaf K p = true ∧ 2 ≤ K`), sums `step1SpreadOps K p B_in`,
  `step2SyntheticFFTOps K p`, `stepFixedPointMuls K p B_in M_mul`, `t1Ell K` recursive child calls
  `fastDFTRecursiveSteps M_mul (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)`, and
  `step3DeconvOps K p`.
- At a base-case leaf (`isBaseLeaf K p = true ∨ K < 2`), returns `leafDFTOps K p M_mul`. -/
def fastDFTRecursiveSteps (M_mul : ℕ → ℕ) (K p B_in : ℕ) : ℕ :=
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    step1SpreadOps K p B_in +
      step2SyntheticFFTOps K p +
      stepFixedPointMuls K p B_in M_mul +
      t1Ell K * fastDFTRecursiveSteps M_mul (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) +
      step3DeconvOps K p
  else
    leafDFTOps K p M_mul
termination_by K
decreasing_by
  unfold k2Ell
  omega

/-- Exact agreement between `computableFastDFTRecursiveSteps` on `canonicalScheduleIntTree`
and `fastDFTRecursiveSteps`. -/
theorem computableFastDFTRecursiveSteps_canonical_eq (M_mul : ℕ → ℕ) (K : ℕ) :
    ∀ (p B_in : ℕ),
      computableFastDFTRecursiveSteps M_mul (canonicalScheduleIntTree K p B_in) =
        fastDFTRecursiveSteps M_mul K p B_in := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [canonicalScheduleIntTree, fastDFTRecursiveSteps]
    split_ifs with hcond
    · have hk2 : k2Ell K < K := by
        have hK2 : 2 ≤ K := hcond.2
        unfold k2Ell
        omega
      simp [computableFastDFTRecursiveSteps,
        ih (k2Ell K) hk2 (pChildEll K p) (childScheduleBIn K p B_in)]
    · rfl

/-- Exact agreement between `computableFastDFTRecursiveSteps` on the computable schedule tree
`computeScheduleIntTree` and `fastDFTRecursiveSteps`. -/
theorem computableFastDFTRecursiveSteps_computeScheduleIntTree_eq (M_mul : ℕ → ℕ) (K : ℕ) :
    ∀ (p B_in : ℕ),
      computableFastDFTRecursiveSteps M_mul (computeScheduleIntTree K p B_in) =
        fastDFTRecursiveSteps M_mul K p B_in := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [computeScheduleIntTree, fastDFTRecursiveSteps]
    split_ifs with hcond
    · have hk2 : k2Ell K < K := by
        have hK2 : 2 ≤ K := hcond.2
        unfold k2Ell
        omega
      simp [computableFastDFTRecursiveSteps,
        ih (k2Ell K) hk2 (pChildEll K p) (childScheduleBIn K p B_in)]
    · rfl

/-- Exact agreement between `computableFastDFTRecursiveSteps` on `computeScheduleIntTreeWithMul natMul`
and `fastDFTRecursiveSteps`. -/
@[simp]
theorem computableFastDFTRecursiveSteps_computeScheduleIntTreeWithMul_eq
    (M_mul : ℕ → ℕ) (natMul : ℕ → ℕ → ℕ) (K : ℕ) :
    ∀ (p B_in : ℕ),
      computableFastDFTRecursiveSteps M_mul (computeScheduleIntTreeWithMul natMul K p B_in) =
        fastDFTRecursiveSteps M_mul K p B_in := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [computeScheduleIntTreeWithMul, fastDFTRecursiveSteps]
    dsimp only
    split_ifs with hcond
    · have hk2 : k2Ell K < K := by
        have hK2 : 2 ≤ K := hcond.2
        unfold k2Ell
        omega
      simp [computableFastDFTRecursiveSteps,
        ih (k2Ell K) hk2 (pChildEll K p) (childScheduleBIn K p B_in)]
    · rfl

/-- Exact unfolding of `fastDFTRecursiveSteps` at an internal node (`!isBaseLeaf K p = true` and `2 ≤ K`). -/
theorem fastDFTRecursiveSteps_of_internal (M_mul : ℕ → ℕ) {K p B_in : ℕ}
    (hleaf : (!isBaseLeaf K p) = true) (hK : 2 ≤ K) :
    fastDFTRecursiveSteps M_mul K p B_in =
      step1SpreadOps K p B_in +
        step2SyntheticFFTOps K p +
        stepFixedPointMuls K p B_in M_mul +
        t1Ell K * fastDFTRecursiveSteps M_mul (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) +
        step3DeconvOps K p := by
  rw [fastDFTRecursiveSteps, if_pos ⟨hleaf, hK⟩]

/-- Exact unfolding of `fastDFTRecursiveSteps` at a leaf node (`isBaseLeaf K p = true ∨ K < 2`). -/
theorem fastDFTRecursiveSteps_of_leaf (M_mul : ℕ → ℕ) {K p B_in : ℕ}
    (hleaf : ¬ ((!isBaseLeaf K p) = true ∧ 2 ≤ K)) :
    fastDFTRecursiveSteps M_mul K p B_in = leafDFTOps K p M_mul := by
  rw [fastDFTRecursiveSteps, if_neg hleaf]

/-- Exact marginal table entry count generated at an internal node `(K, p)` of `computeScheduleIntTree`:
`t1Ell K * (2 * computeM1Ell K p + 1)` filter taps + `2 * rEll K` pre/post-twist roots +
`2 * rEll K` passband weights `c0, c1`. -/
def scheduleNodeTableEntries (K p : ℕ) : ℕ :=
  t1Ell K * (2 * computeM1Ell K p + 1) + 4 * rEll K

/-- At every internal node (`!isBaseLeaf K p = true ∧ 2 ≤ K`), the marginal table entry count
`scheduleNodeTableEntries K p` is at most `26 * (2 ^ K)`. -/
theorem scheduleNodeTableEntries_le_of_internal {K p : ℕ}
    (hleaf : (!isBaseLeaf K p) = true) (hK2 : 2 ≤ K) :
    scheduleNodeTableEntries K p ≤ 26 * (2 ^ K) := by
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
  have hm1 : computeM1Ell K p ≤ p + 2 * K + 12 := by
    rw [← pChildEll_eq K p]
    exact computeM1Ell_le_pChildEll K p
  have hwin : 2 * computeM1Ell K p + 1 ≤ 22 * rEll K := by omega
  have ht1_pos : 1 ≤ t1Ell K := t1Ell_pos K
  have h1 : t1Ell K * (2 * computeM1Ell K p + 1) ≤ 22 * (2 ^ K) := by
    calc t1Ell K * (2 * computeM1Ell K p + 1)
        ≤ t1Ell K * (22 * rEll K) := Nat.mul_le_mul_left (t1Ell K) hwin
      _ = 22 * (t1Ell K * rEll K) := by ring
      _ = 22 * (2 ^ K) := by rw [ht1r]
  have h2 : 4 * rEll K ≤ 4 * (2 ^ K) := by
    calc 4 * rEll K = 4 * (1 * rEll K) := by ring
      _ ≤ 4 * (t1Ell K * rEll K) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (rEll K) ht1_pos)
      _ = 4 * (2 ^ K) := by rw [ht1r]
  unfold scheduleNodeTableEntries
  linarith

/-- Per-entry series-iteration factor `scheduleSeriesTerms q = 120 * (q + 1) * (q + 1)` accounting
for the $O(q)$ single-pass series recurrence terms and $\Theta(q)$ per-term bit-step cost when
synthesizing each $q$-bit schedule table entry in `computeScheduleIntTreeWithMul`. -/
def scheduleSeriesTerms (q : ℕ) : ℕ :=
  120 * (q + 1) * (q + 1)

/-- **Computable Operation Count for Generating `ScheduleIntTree` (`scheduleTreeGenOps`)**:
Counts the operations of `computeScheduleIntTree` / `computeScheduleIntTreeWithMul` across the
recursion tree using the exact marginal table entry count
`scheduleNodeTableEntries K p = t1Ell K * (2 * computeM1Ell K p + 1) + 4 * rEll K` and the
per-entry series-iteration factor `scheduleSeriesTerms`:
- At an internal node (`!isBaseLeaf K p = true ∧ 2 ≤ K`), computes the `t1Ell K * (2 * computeM1Ell K p + 1)`
  filter taps, `2 * rEll K` pre/post-twist roots, and `2 * rEll K` passband weights `c0, c1` at
  precision `qChildEll K p` using `scheduleSeriesTerms (qChildEll K p)` recurrence steps per entry,
  plus 1 recursive call to generate the child schedule tree at `(k2Ell K, pChildEll K p)`.
- At a leaf (`isBaseLeaf K p = true ∨ K < 2`), computes `2 ^ K` leaf twiddle roots at precision
  `qBaseEll K p` using `scheduleSeriesTerms (qBaseEll K p)` recurrence steps per entry. -/
def scheduleTreeGenOps (M_mul : ℕ → ℕ) (K p : ℕ) : ℕ :=
  if (!isBaseLeaf K p) = true ∧ 2 ≤ K then
    scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
      (qChildEll K p + M_mul (qChildEll K p)) +
      scheduleTreeGenOps M_mul (k2Ell K) (pChildEll K p)
  else
    (2 ^ K) * scheduleSeriesTerms (qBaseEll K p) *
      (qBaseEll K p + M_mul (qBaseEll K p))
termination_by K
decreasing_by
  unfold k2Ell
  omega

/-- Monotonicity/scaling of `scheduleTreeGenOps` with respect to the sub-multiplication cost model
`M_mul`. -/
theorem scheduleTreeGenOps_scale_le {M1 M2 : ℕ → ℕ} {C : ℕ} (hC : 1 ≤ C)
    (hM : ∀ q : ℕ, M1 q ≤ C * M2 q) (K : ℕ) :
    ∀ p : ℕ, scheduleTreeGenOps M1 K p ≤ C * scheduleTreeGenOps M2 K p := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p
    conv_lhs => rw [scheduleTreeGenOps]
    conv_rhs => rw [scheduleTreeGenOps]
    split_ifs with hcond
    · have hk2 : k2Ell K < K := by
        have hK2 : 2 ≤ K := hcond.2
        unfold k2Ell; omega
      have hrec := ih (k2Ell K) hk2 (pChildEll K p)
      have hq : qChildEll K p + M1 (qChildEll K p) ≤ C * (qChildEll K p + M2 (qChildEll K p)) := by
        have h1 : qChildEll K p ≤ C * qChildEll K p := by
          calc qChildEll K p = 1 * qChildEll K p := (one_mul _).symm
            _ ≤ C * qChildEll K p := Nat.mul_le_mul_right _ hC
        have h2 := hM (qChildEll K p)
        linarith
      have hnode :
          scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + M1 (qChildEll K p)) ≤
          C * (scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + M2 (qChildEll K p))) := by
        calc scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
              (qChildEll K p + M1 (qChildEll K p))
            ≤ scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
                (C * (qChildEll K p + M2 (qChildEll K p))) := Nat.mul_le_mul_left _ hq
          _ = C * (scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
                (qChildEll K p + M2 (qChildEll K p))) := by ring
      linarith
    · have hq : qBaseEll K p + M1 (qBaseEll K p) ≤ C * (qBaseEll K p + M2 (qBaseEll K p)) := by
        have h1 : qBaseEll K p ≤ C * qBaseEll K p := by
          calc qBaseEll K p = 1 * qBaseEll K p := (one_mul _).symm
            _ ≤ C * qBaseEll K p := Nat.mul_le_mul_right _ hC
        have h2 := hM (qBaseEll K p)
        linarith
      calc (2 ^ K) * scheduleSeriesTerms (qBaseEll K p) * (qBaseEll K p + M1 (qBaseEll K p))
          ≤ (2 ^ K) * scheduleSeriesTerms (qBaseEll K p) *
              (C * (qBaseEll K p + M2 (qBaseEll K p))) := Nat.mul_le_mul_left _ hq
        _ = C * ((2 ^ K) * scheduleSeriesTerms (qBaseEll K p) *
              (qBaseEll K p + M2 (qBaseEll K p))) := by ring

/-- Monotonicity/scaling of `fastDFTRecursiveSteps` with respect to the sub-multiplication cost
model `M_mul`. -/
theorem fastDFTRecursiveSteps_scale_le {M1 M2 : ℕ → ℕ} {C : ℕ} (hC : 1 ≤ C)
    (hM : ∀ q : ℕ, M1 q ≤ C * M2 q) (K : ℕ) :
    ∀ p B_in : ℕ,
      fastDFTRecursiveSteps M1 K p B_in ≤ C * fastDFTRecursiveSteps M2 K p B_in := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    conv_lhs => rw [fastDFTRecursiveSteps]
    conv_rhs => rw [fastDFTRecursiveSteps]
    split_ifs with hcond
    · have hk2 : k2Ell K < K := by
        have hK2 : 2 ≤ K := hcond.2
        unfold k2Ell; omega
      have hrec := ih (k2Ell K) hk2 (pChildEll K p) (childScheduleBIn K p B_in)
      have hchild :
          t1Ell K * fastDFTRecursiveSteps M1 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) ≤
          C * (t1Ell K * fastDFTRecursiveSteps M2 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) := by
        calc t1Ell K * fastDFTRecursiveSteps M1 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
            ≤ t1Ell K * (C * fastDFTRecursiveSteps M2 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) :=
              Nat.mul_le_mul_left _ hrec
          _ = C * (t1Ell K * fastDFTRecursiveSteps M2 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) := by
              ring
      have hmuls : stepFixedPointMuls K p B_in M1 ≤ C * stepFixedPointMuls K p B_in M2 := by
        unfold stepFixedPointMuls
        dsimp only
        set Q_kron := kroneckerPackedBitLength (foldedHalfWidth (computeM1Ell K p) (rEll K))
          (scheduleSlotBits K p B_in (computeM1Ell K p))
        have h1 := hM Q_kron
        have h2 := hM (qChildEll K p)
        have h3 : 2 * t1Ell K * numBlocks (rEll K) (foldedHalfWidth (computeM1Ell K p) (rEll K)) * M1 Q_kron ≤
            2 * t1Ell K * numBlocks (rEll K) (foldedHalfWidth (computeM1Ell K p) (rEll K)) * (C * M2 Q_kron) :=
          Nat.mul_le_mul_left _ h1
        have h4 : 16 * (2 ^ K) * M1 (qChildEll K p) ≤ 16 * (2 ^ K) * (C * M2 (qChildEll K p)) :=
          Nat.mul_le_mul_left _ h2
        linarith
      have hadd :
          step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p ≤
            C * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p) := by
        calc step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p
            = 1 * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p) := (one_mul _).symm
          _ ≤ C * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p) :=
              Nat.mul_le_mul_right _ hC
      linarith
    · unfold leafDFTOps
      have hq : qBaseEll K p + M1 (qBaseEll K p) ≤ C * (qBaseEll K p + M2 (qBaseEll K p)) := by
        have h1 : qBaseEll K p ≤ C * qBaseEll K p := by
          calc qBaseEll K p = 1 * qBaseEll K p := (one_mul _).symm
            _ ≤ C * qBaseEll K p := Nat.mul_le_mul_right _ hC
        have h2 := hM (qBaseEll K p)
        linarith
      calc (K + 1) * (2 ^ K) * (qBaseEll K p + M1 (qBaseEll K p))
          ≤ (K + 1) * (2 ^ K) * (C * (qBaseEll K p + M2 (qBaseEll K p))) := Nat.mul_le_mul_left _ hq
        _ = C * ((K + 1) * (2 ^ K) * (qBaseEll K p + M2 (qBaseEll K p))) := by ring

/-- **Computable Full End-to-End Multiplication Algorithm Operation Recurrence
(`computableIntMulAlgorithmSteps`, Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`))**. -/
def computableIntMulAlgorithmSteps (M_mul : ℕ → ℕ) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)) : ℕ :=
  scheduleBitsLen n +
    fullScheduleTableBitsLen n +
    scheduleTreeGenOps M_mul (rootK0 n) (rootP0 n) +
    2 * n +
    2 * computableFastDFTRecursiveSteps M_mul tree +
    3 * rootR0 n * M_mul (rootP0 n + 2) +
    4 * n

/-- **Computable Full End-to-End Multiplication Algorithm Operation Recurrence (`intMulAlgorithmSteps`,
Section 7.1 (`sec:alg-spec`) and Section 7.2 (`sec:cost-proof`))**:
Counts the total operations of `computableIntMulBits` / `computableReconstructProduct` on $n$-bit
inputs given sub-multiplication cost `M_mul : ℕ → ℕ`:
- `scheduleBitsLen n + fullScheduleTableBitsLen n + scheduleTreeGenOps M_mul (rootK0 n) (rootP0 n)`
  for generating the root schedule, multi-level schedule table, and `ScheduleIntTree` via `computeScheduleIntTree`,
- `2 * n` for base-$2^b$ chunk unpacking (`unpackInputChunks`),
- `2 * fastDFTRecursiveSteps M_mul (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)`
  for the forward and conjugate-reflected inverse calls to `computableFastDFTRecursive`,
- `3 * rootR0 n * M_mul (rootP0 n + 2)` for the `rootR0 n` pointwise complex squarings at the root, and
- `4 * n` for the base-$2^b$ carry-save reconstruction (`reconstructProductFromChunks`). -/
def intMulAlgorithmSteps (M_mul : ℕ → ℕ) (n : ℕ) : ℕ :=
  scheduleBitsLen n +
    fullScheduleTableBitsLen n +
    scheduleTreeGenOps M_mul (rootK0 n) (rootP0 n) +
    2 * n +
    2 * fastDFTRecursiveSteps M_mul (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0) +
    3 * rootR0 n * M_mul (rootP0 n + 2) +
    4 * n

/-- Elementary exponential bound `2 * m + 1 ≤ 2 ^ (m + 1)` for all $m \in \mathbb{N}$. -/
theorem two_mul_add_one_le_two_pow_succ (m : ℕ) : 2 * m + 1 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h1 : 2 ≤ 2 ^ (m + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
      _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) := Nat.add_le_add ih h1
      _ = 2 ^ (m + 2) := by rw [pow_succ']; ring

/-- Corollary: `Nat.clog 2 (2 * m + 1) ≤ m + 1` for all $m \in \mathbb{N}$. -/
theorem clog_two_mul_add_one_le (m : ℕ) : Nat.clog 2 (2 * m + 1) ≤ m + 1 :=
  Nat.clog_le_of_le_pow (two_mul_add_one_le_two_pow_succ m)

/-- Closed-form sum representation of `levelScheduleBIn`. -/
theorem levelScheduleBIn_eq_sum (K0 p0 ell : ℕ) :
    levelScheduleBIn K0 p0 ell =
      2 + ∑ j ∈ Finset.range ell, Nat.clog 2 (2 * pChildEll (levelK K0 j) (levelP K0 p0 j) + 4) := by
  induction ell with
  | zero => simp [levelScheduleBIn]
  | succ ell ih =>
    simp only [levelScheduleBIn, childScheduleBIn, ih, Finset.sum_range_succ, Nat.add_assoc]

/-- Per-step logarithmic headroom increment bound at any active level `j < recursionDepth (rootK0 n) (rootP0 n)`. -/
theorem clog_two_mul_pChildEll_add_four_le_of_lt_depth {n j : ℕ}
    (hj : j < recursionDepth (rootK0 n) (rootP0 n)) :
    Nat.clog 2 (2 * pChildEll (levelK (rootK0 n) j) (levelP (rootK0 n) (rootP0 n) j) + 4) ≤
      levelK (rootK0 n) j + 3 := by
  set K := levelK (rootK0 n) j
  set p := levelP (rootK0 n) (rootP0 n) j
  have hlt : 4 * p * p < 2 ^ K :=
    four_mul_sq_lt_levelR_of_lt_recursionDepth (rootK0 n) (rootP0 n) j hj
  have hp_ge18 : 18 ≤ p :=
    le_trans (rootP0_ge_eighteen n) (levelP_ge_p0 (rootK0 n) (rootP0 n) j)
  have h2p : 2 * p + 28 ≤ 4 * p * p := by nlinarith
  have hK_pow : K ≤ 2 ^ K := le_of_lt Nat.lt_two_pow_self
  have hpC : pChildEll K p = p + 2 * K + 12 := pChildEll_eq K p
  have hpow3 : 2 ^ (K + 3) = 8 * (2 ^ K) := by rw [pow_add]; ring
  apply Nat.clog_le_of_le_pow
  omega

/-- **Unconditional Schedule Headroom Linear Bound (`levelScheduleBIn_le`)**:
Across all active recursion levels $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$, the
cumulative data-independent headroom `levelScheduleBIn (rootK0 n) (rootP0 n) ell` satisfies
`levelScheduleBIn (rootK0 n) (rootP0 n) ell ≤ 2 + 6 * rootK0 n ≤ 3 * rootP0 n`. -/
theorem levelScheduleBIn_le {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n)) :
    levelScheduleBIn (rootK0 n) (rootP0 n) ell ≤ 2 + 6 * rootK0 n ∧
      levelScheduleBIn (rootK0 n) (rootP0 n) ell ≤ 3 * rootP0 n := by
  rw [levelScheduleBIn_eq_sum]
  have hsum_le :
      (∑ j ∈ Finset.range ell,
        Nat.clog 2 (2 * pChildEll (levelK (rootK0 n) j) (levelP (rootK0 n) (rootP0 n) j) + 4)) ≤
      ∑ j ∈ Finset.range ell, (levelK (rootK0 n) j + 3) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    exact clog_two_mul_pChildEll_add_four_le_of_lt_depth (lt_of_lt_of_le hj hell)
  have hsum_split :
      (∑ j ∈ Finset.range ell, (levelK (rootK0 n) j + 3)) =
        (∑ j ∈ Finset.range ell, levelK (rootK0 n) j) + 3 * ell := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  have hK_sum := sum_levelK_le (rootK0 n) ell
  have hrec := recursionDepth_le_K0 (rootK0 n) (rootP0 n)
  have hp0_eq : rootP0 n = 2 * chunkBits n + 2 * rootK0 n + 6 := rfl
  omega

/-- General linear upper bound on `scheduleSlotBits K p B_in m1` whenever `m1 ≤ pChildEll K p`. -/
theorem scheduleSlotBits_le (K p B_in m1 : ℕ) (hm1 : m1 ≤ pChildEll K p) :
    scheduleSlotBits K p B_in m1 ≤ 6 * qChildEll K p + B_in + 7 := by
  unfold scheduleSlotBits kroneckerSlotBitsRaw kroneckerSlotBitsWithIn
  have hc1 : Nat.clog 2 (2 * m1 + 1) ≤ m1 + 1 := clog_two_mul_add_one_le m1
  have hfold : foldedHalfWidth m1 (rEll K) ≤ m1 := foldedHalfWidth_le_left m1 (rEll K)
  have hc2 : Nat.clog 2 (2 * foldedHalfWidth m1 (rEll K) + 1) ≤ foldedHalfWidth m1 (rEll K) + 1 :=
    clog_two_mul_add_one_le (foldedHalfWidth m1 (rEll K))
  have hq : qChildEll K p = p + 2 * K + 14 := qChildEll_eq K p
  have hpC : pChildEll K p = p + 2 * K + 12 := pChildEll_eq K p
  omega

/-- Leaf precision bound along the schedule (`ell ≤ recursionDepth (rootK0 n) (rootP0 n)`):
`qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) ≤ 12 * rootP0 n`. -/
theorem qBaseEll_level_le {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n)) :
    qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) ≤ 12 * rootP0 n := by
  unfold qBaseEll
  have hp := levelP_le_eleven_mul_rootP0 hell
  have hK := levelK_le_K0 (rootK0 n) ell
  have hp0_eq : rootP0 n = 2 * chunkBits n + 2 * rootK0 n + 6 := rfl
  omega

/-- Child working precision bound at any internal level (`ell < recursionDepth (rootK0 n) (rootP0 n)`):
`qChildEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) ≤ 12 * rootP0 n`. -/
theorem qChildEll_level_le {n ell : ℕ}
    (hlt : ell < recursionDepth (rootK0 n) (rootP0 n)) :
    qChildEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) ≤ 12 * rootP0 n := by
  unfold qChildEll
  have hstep : pChildEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) =
      levelP (rootK0 n) (rootP0 n) (ell + 1) := rfl
  rw [hstep]
  have hp : levelP (rootK0 n) (rootP0 n) (ell + 1) ≤ 11 * rootP0 n :=
    levelP_le_eleven_mul_rootP0 (by omega)
  have hp0 := rootP0_ge_eighteen n
  omega

/-- **Unconditional Data-Independent Slot Bit-Width Linear Bound (`scheduleSlotBits_level_le`)**:
At any active recursion level $\ell < \text{recursionDepth (rootK0 n) (rootP0 n)}$ and any
headroom $B_{\text{in}} \le \text{levelScheduleBIn (rootK0 n) (rootP0 n) } \ell$,
$$\text{scheduleSlotBits } K_\ell \, p_\ell \, B_{\text{in}} \, (\text{computeM1Ell } K_\ell \, p_\ell) \le 76 \cdot p_0(n).$$ -/
theorem scheduleSlotBits_level_le {n ell B_in : ℕ}
    (hlt : ell < recursionDepth (rootK0 n) (rootP0 n))
    (hB_in : B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) ell) :
    let K := levelK (rootK0 n) ell
    let p := levelP (rootK0 n) (rootP0 n) ell
    scheduleSlotBits K p B_in (computeM1Ell K p) ≤ 76 * rootP0 n := by
  intro K p
  have h1 := scheduleSlotBits_le K p B_in (computeM1Ell K p) (computeM1Ell_le_pChildEll K p)
  have hq : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
  have hB : levelScheduleBIn (rootK0 n) (rootP0 n) ell ≤ 3 * rootP0 n :=
    (levelScheduleBIn_le (le_of_lt hlt)).2
  have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
  omega

/-- At any active recursion level $\ell < \text{recursionDepth (rootK0 n) (rootP0 n)}$ with
$B_{\text{in}} \le \text{levelScheduleBIn (rootK0 n) (rootP0 n) } \ell$, the blocked Kronecker
Overlap-Add bit-operation count satisfies
`step1SpreadOps K_ell p_ell B_in ≤ 912 * rootP0 n * (2 ^ K_ell)`. -/
theorem step1SpreadOps_level_le {n ell B_in : ℕ}
    (hlt : ell < recursionDepth (rootK0 n) (rootP0 n))
    (hB_in : B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) ell) :
    let K := levelK (rootK0 n) ell
    let p := levelP (rootK0 n) (rootP0 n) ell
    step1SpreadOps K p B_in ≤ 912 * rootP0 n * (2 ^ K) := by
  intro K p
  have h1 := step1SpreadOps_le K p B_in
  have h2 := scheduleSlotBits_level_le hlt hB_in
  calc step1SpreadOps K p B_in
      ≤ 12 * (2 ^ K) * scheduleSlotBits K p B_in (computeM1Ell K p) := h1
    _ ≤ 12 * (2 ^ K) * (76 * rootP0 n) := Nat.mul_le_mul_left _ h2
    _ = 912 * rootP0 n * (2 ^ K) := by ring

/-- Leaf step-count bound along the schedule (`ell ≤ recursionDepth (rootK0 n) (rootP0 n)`):
`leafDFTOps K_ell p_ell (fun q => q) ≤ 2148 * rootP0 n * (2 ^ K_ell) * (K_ell + 1)`. -/
theorem leafDFTOps_level_le {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n)) :
    leafDFTOps (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) (fun q => q) ≤
      2148 * rootP0 n * (2 ^ levelK (rootK0 n) ell) * (levelK (rootK0 n) ell + 1) := by
  set K := levelK (rootK0 n) ell
  set p := levelP (rootK0 n) (rootP0 n) ell
  unfold leafDFTOps
  have hqb : qBaseEll K p ≤ 12 * rootP0 n := qBaseEll_level_le hell
  have hq : qBaseEll K p + qBaseEll K p ≤ 2148 * rootP0 n := by omega
  calc
    (K + 1) * (2 ^ K) * (qBaseEll K p + qBaseEll K p)
      ≤ (K + 1) * (2 ^ K) * (2148 * rootP0 n) := Nat.mul_le_mul_left _ hq
    _ = 2148 * rootP0 n * (2 ^ K) * (K + 1) := by ring

/-- **Unconditional Multi-Level Step-Count Telescoping Bound for `fastDFTRecursiveSteps`
(`fastDFTRecursiveSteps_level_le`, Theorem 1 (`thm:main`), proof Part 2 in Section 7.2 (`sec:cost-proof`))**:
For every $n \in \mathbb{N}$, every active recursion level $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$,
and every input slot headroom $B_{\text{in}} \le \text{levelScheduleBIn (rootK0 n) (rootP0 n) } \ell$,
$$\text{fastDFTRecursiveSteps } (\lambda q.\, q) \, K_\ell \, p_\ell \, B_{\text{in}} \le 2148 \cdot p_0(n) \cdot 2^{K_\ell} \cdot (K_\ell + 1).$$ -/
theorem fastDFTRecursiveSteps_level_le (n : ℕ) :
    ∀ (d ell B_in : ℕ),
      ell ≤ recursionDepth (rootK0 n) (rootP0 n) →
      B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) ell →
      recursionDepth (rootK0 n) (rootP0 n) - ell = d →
      fastDFTRecursiveSteps (fun q => q)
        (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) B_in ≤
        2148 * rootP0 n * (2 ^ levelK (rootK0 n) ell) * (levelK (rootK0 n) ell + 1) := by
  intro d
  induction d with
  | zero =>
    intro ell B_in hell _hB_in hd
    have hell_eq : ell = recursionDepth (rootK0 n) (rootP0 n) := by omega
    subst hell_eq
    have hp0 : 1 ≤ rootP0 n := by
      have := rootP0_ge_eighteen n
      omega
    have hleaf_true :
        isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
          (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) = true :=
      isBaseLeaf_recursionDepth (rootK0 n) (rootP0 n) hp0
    have hnot :
        ¬ ((!isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) = true ∧
          2 ≤ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) := by
      simp [hleaf_true]
    rw [fastDFTRecursiveSteps_of_leaf _ hnot]
    exact leafDFTOps_level_le hell
  | succ d ih =>
    intro ell B_in hell hB_in hd
    have hlt : ell < recursionDepth (rootK0 n) (rootP0 n) := by omega
    rw [fastDFTRecursiveSteps]
    split_ifs with hcond
    · set K := levelK (rootK0 n) ell
      set p := levelP (rootK0 n) (rootP0 n) ell
      have hK2 : 2 ≤ K := hcond.2
      have hk1_pos : 1 ≤ k1Ell K := by
        unfold k1Ell
        omega
      have hq : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
      have hstep1 : step1SpreadOps K p B_in ≤ 912 * rootP0 n * (2 ^ K) :=
        step1SpreadOps_level_le hlt hB_in
      have hmuls :
          stepFixedPointMuls K p B_in (fun q => q) ≤ 1104 * rootP0 n * (2 ^ K) := by
        have hdef : stepFixedPointMuls K p B_in (fun q => q) =
            step1SpreadOps K p B_in + 16 * (2 ^ K) * qChildEll K p := rfl
        rw [hdef]
        have h16 : 16 * (2 ^ K) * qChildEll K p ≤ 192 * rootP0 n * (2 ^ K) := by
          calc 16 * (2 ^ K) * qChildEll K p
              ≤ 16 * (2 ^ K) * (12 * rootP0 n) := Nat.mul_le_mul_left _ hq
            _ = 192 * rootP0 n * (2 ^ K) := by ring
        calc step1SpreadOps K p B_in + 16 * (2 ^ K) * qChildEll K p
            ≤ 912 * rootP0 n * (2 ^ K) + 192 * rootP0 n * (2 ^ K) := Nat.add_le_add hstep1 h16
          _ = 1104 * rootP0 n * (2 ^ K) := by ring
      have hstep23 :
          step2SyntheticFFTOps K p + step3DeconvOps K p ≤
            (120 + 12 * k1Ell K) * rootP0 n * (2 ^ K) := by
        unfold step2SyntheticFFTOps step3DeconvOps
        calc (2 + k1Ell K) * (2 ^ K) * qChildEll K p + 8 * (2 ^ K) * qChildEll K p
            = (10 + k1Ell K) * (2 ^ K) * qChildEll K p := by ring
          _ ≤ (10 + k1Ell K) * (2 ^ K) * (12 * rootP0 n) := Nat.mul_le_mul_left _ hq
          _ = (120 + 12 * k1Ell K) * rootP0 n * (2 ^ K) := by ring
      have hinternal :
          step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
            stepFixedPointMuls K p B_in (fun q => q) + step3DeconvOps K p ≤
            2148 * rootP0 n * (2 ^ K) * k1Ell K := by
        have hsum :
            step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
              stepFixedPointMuls K p B_in (fun q => q) + step3DeconvOps K p ≤
              (2136 + 12 * k1Ell K) * rootP0 n * (2 ^ K) := by
          calc step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
                stepFixedPointMuls K p B_in (fun q => q) + step3DeconvOps K p
              = step1SpreadOps K p B_in + stepFixedPointMuls K p B_in (fun q => q) +
                  (step2SyntheticFFTOps K p + step3DeconvOps K p) := by ring
            _ ≤ 912 * rootP0 n * (2 ^ K) + 1104 * rootP0 n * (2 ^ K) +
                  (120 + 12 * k1Ell K) * rootP0 n * (2 ^ K) :=
                Nat.add_le_add (Nat.add_le_add hstep1 hmuls) hstep23
            _ = (2136 + 12 * k1Ell K) * rootP0 n * (2 ^ K) := by ring
        have h2148 : 2136 + 12 * k1Ell K ≤ 2148 * k1Ell K := by omega
        calc step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
              stepFixedPointMuls K p B_in (fun q => q) + step3DeconvOps K p
            ≤ (2136 + 12 * k1Ell K) * rootP0 n * (2 ^ K) := hsum
          _ = (2136 + 12 * k1Ell K) * (rootP0 n * (2 ^ K)) := by ring
          _ ≤ (2148 * k1Ell K) * (rootP0 n * (2 ^ K)) := Nat.mul_le_mul_right _ h2148
          _ = 2148 * rootP0 n * (2 ^ K) * k1Ell K := by ring
      have hB_child :
          childScheduleBIn K p B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) (ell + 1) := by
        unfold levelScheduleBIn childScheduleBIn
        exact Nat.add_le_add_right hB_in _
      have hrec :
          fastDFTRecursiveSteps (fun q => q) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) ≤
            2148 * rootP0 n * (2 ^ k2Ell K) * (k2Ell K + 1) :=
        ih (ell + 1) (childScheduleBIn K p B_in) (Nat.succ_le_of_lt hlt) hB_child (by omega)
      have hchild :
          t1Ell K * fastDFTRecursiveSteps (fun q => q) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) ≤
            2148 * rootP0 n * (2 ^ K) * (k2Ell K + 1) := by
        have ht1r : t1Ell K * (2 ^ k2Ell K) = 2 ^ K := t1Ell_mul_rEll K
        calc
          t1Ell K * fastDFTRecursiveSteps (fun q => q) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
            ≤ t1Ell K * (2148 * rootP0 n * (2 ^ k2Ell K) * (k2Ell K + 1)) :=
              Nat.mul_le_mul_left (t1Ell K) hrec
          _ = 2148 * rootP0 n * (t1Ell K * (2 ^ k2Ell K)) * (k2Ell K + 1) := by ring
          _ = 2148 * rootP0 n * (2 ^ K) * (k2Ell K + 1) := by rw [ht1r]
      have hk_add : k1Ell K + (k2Ell K + 1) = K + 1 := by
        have := k1Ell_add_k2Ell K
        omega
      calc
        step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
            stepFixedPointMuls K p B_in (fun q => q) +
            t1Ell K * fastDFTRecursiveSteps (fun q => q) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) +
            step3DeconvOps K p
          = (step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
              stepFixedPointMuls K p B_in (fun q => q) + step3DeconvOps K p) +
              t1Ell K * fastDFTRecursiveSteps (fun q => q) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) := by
            ring
        _ ≤ 2148 * rootP0 n * (2 ^ K) * k1Ell K + 2148 * rootP0 n * (2 ^ K) * (k2Ell K + 1) :=
            Nat.add_le_add hinternal hchild
        _ = 2148 * rootP0 n * (2 ^ K) * (k1Ell K + (k2Ell K + 1)) := by ring
        _ = 2148 * rootP0 n * (2 ^ K) * (K + 1) := by rw [hk_add]
    · exact leafDFTOps_level_le hell

/-- **Unconditional Root Step-Count Bound for `fastDFTRecursiveSteps` (`fastDFTRecursiveSteps_root_le`,
Theorem 1 (`thm:main`), proof Part 2 in Section 7.2 (`sec:cost-proof`))**:
For every $n \in \mathbb{N}$ and every root headroom $B_{\text{in}} \le \text{levelScheduleBIn (rootK0 n) (rootP0 n) } 0$,
$$\text{fastDFTRecursiveSteps } (\lambda q.\, q) \, (K_0(n)) \, (p_0(n)) \, B_{\text{in}} \le 4296 \cdot R_0(n) \cdot p_0(n) \cdot K_0(n).$$ -/
theorem fastDFTRecursiveSteps_root_le (n B_in : ℕ)
    (hB_in : B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) 0) :
    fastDFTRecursiveSteps (fun q => q) (rootK0 n) (rootP0 n) B_in ≤
      4296 * rootR0 n * rootP0 n * rootK0 n := by
  have h0 := fastDFTRecursiveSteps_level_le n
    (recursionDepth (rootK0 n) (rootP0 n)) 0 B_in (Nat.zero_le _) hB_in (Nat.sub_zero _)
  change fastDFTRecursiveSteps (fun q => q) (rootK0 n) (rootP0 n) B_in ≤
    2148 * rootP0 n * rootR0 n * (rootK0 n + 1) at h0
  have hK0 : rootK0 n + 1 ≤ 2 * rootK0 n := by
    have := rootK0_ge_two n
    omega
  calc
    fastDFTRecursiveSteps (fun q => q) (rootK0 n) (rootP0 n) B_in
      ≤ 2148 * rootP0 n * rootR0 n * (rootK0 n + 1) := h0
    _ ≤ 2148 * rootP0 n * rootR0 n * (2 * rootK0 n) := Nat.mul_le_mul_left _ hK0
    _ = 4296 * rootR0 n * rootP0 n * rootK0 n := by ring

/-- Upper bound on `fullScheduleTableBitsLen n` for all $n \ge 1$:
`fullScheduleTableBitsLen n ≤ 330 * n * (Nat.log 2 n + 1)`. -/
theorem fullScheduleTableBitsLen_le_succ {n : ℕ} (hn : 1 ≤ n) :
    fullScheduleTableBitsLen n ≤ 330 * n * (Nat.log 2 n + 1) := by
  unfold fullScheduleTableBitsLen scheduleFieldBits
  have hrec : recursionDepth (rootK0 n) (rootP0 n) + 1 ≤ 3 * (Nat.log 2 n + 1) := by
    have h1 := recursionDepth_le_K0 (rootK0 n) (rootP0 n)
    have h2 := rootK0_le_log_add_two n
    omega
  have hfield : 11 * (2 * n + 8) ≤ 110 * n := by omega
  calc
    (recursionDepth (rootK0 n) (rootP0 n) + 1) * (11 * (2 * n + 8))
      ≤ (3 * (Nat.log 2 n + 1)) * (110 * n) := Nat.mul_le_mul hrec hfield
    _ = 330 * n * (Nat.log 2 n + 1) := by ring

/-- Monotonicity/scaling of `intMulAlgorithmSteps` with respect to the sub-multiplication cost model
`M_mul`. -/
theorem intMulAlgorithmSteps_scale_le {M1 M2 : ℕ → ℕ} {C : ℕ} (hC : 1 ≤ C)
    (hM : ∀ q : ℕ, M1 q ≤ C * M2 q) (n : ℕ) :
    intMulAlgorithmSteps M1 n ≤ C * intMulAlgorithmSteps M2 n := by
  unfold intMulAlgorithmSteps
  have htree := scheduleTreeGenOps_scale_le hC hM (rootK0 n) (rootP0 n)
  have hfast := fastDFTRecursiveSteps_scale_le hC hM (rootK0 n) (rootP0 n)
    (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
  have hsq : 3 * rootR0 n * M1 (rootP0 n + 2) ≤ C * (3 * rootR0 n * M2 (rootP0 n + 2)) := by
    calc 3 * rootR0 n * M1 (rootP0 n + 2)
        ≤ 3 * rootR0 n * (C * M2 (rootP0 n + 2)) := Nat.mul_le_mul_left _ (hM (rootP0 n + 2))
      _ = C * (3 * rootR0 n * M2 (rootP0 n + 2)) := by ring
  have hlin :
      scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n ≤
        C * (scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n) := by
    calc scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n
        = 1 * (scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n) := (one_mul _).symm
      _ ≤ C * (scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n) :=
          Nat.mul_le_mul_right _ hC
  linarith

/-- **Recursive Sub-Multiplication Bit-Operation Cost (`subMulBitOps`, Theorem 1 (`thm:main`),
proof Part 3 in Section 7.2 (`sec:cost-proof`))**:
Costs each $q$-bit integer sub-multiplication inside `computableFastDFTRecursiveWithMul` /
`computableReconstructProductWithMul` / `computeScheduleIntTreeWithMul` at $q \cdot (\lfloor \log_2 q \rfloor + 1)$
bit operations (matching the self-recursive $O(q \log q)$ bootstrap `computableNatMul`). -/
def subMulBitOps (q : ℕ) : ℕ :=
  q * (Nat.log 2 q + 1)

theorem le_subMulBitOps (q : ℕ) : q ≤ subMulBitOps q := by
  unfold subMulBitOps
  calc q = q * 1 := (mul_one q).symm
    _ ≤ q * (Nat.log 2 q + 1) := Nat.mul_le_mul_left q (by omega)

/-- Elementary exponential domination `(m + 1) * (m + 1) ≤ 3 * 2 ^ m` for all $m \in \mathbb{N}$. -/
theorem add_one_sq_le_three_mul_two_pow (m : ℕ) : (m + 1) * (m + 1) ≤ 3 * 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rcases lt_or_ge m 3 with hlt | hge
    · interval_cases m <;> norm_num
    · have h1 : 2 * m + 3 ≤ (m + 1) * (m + 1) := by nlinarith
      calc (m + 1 + 1) * (m + 1 + 1)
          = (m + 1) * (m + 1) + (2 * m + 3) := by ring
        _ ≤ (m + 1) * (m + 1) + (m + 1) * (m + 1) := Nat.add_le_add_left h1 _
        _ = 2 * ((m + 1) * (m + 1)) := by ring
        _ ≤ 2 * (3 * 2 ^ m) := Nat.mul_le_mul_left 2 ih
        _ = 3 * 2 ^ (m + 1) := by rw [pow_succ']; ring

/-- Corollary of `add_one_sq_le_three_mul_two_pow`: for every $L \in \mathbb{N}$,
`(L + 1) * (L + 1) ≤ 12 * 2 ^ (L / 2)`. -/
theorem add_one_sq_le_twelve_mul_two_pow_div_two (L : ℕ) :
    (L + 1) * (L + 1) ≤ 12 * 2 ^ (L / 2) := by
  have h1 : L + 1 ≤ 2 * (L / 2 + 1) := by omega
  calc (L + 1) * (L + 1)
      ≤ (2 * (L / 2 + 1)) * (2 * (L / 2 + 1)) := Nat.mul_le_mul h1 h1
    _ = 4 * ((L / 2 + 1) * (L / 2 + 1)) := by ring
    _ ≤ 4 * (3 * 2 ^ (L / 2)) := Nat.mul_le_mul_left 4 (add_one_sq_le_three_mul_two_pow (L / 2))
    _ = 12 * 2 ^ (L / 2) := by ring

/-- Elementary fourth-power exponential domination `((u + 1) * (u + 1)) * ((u + 1) * (u + 1)) ≤ 144 * 2 ^ u`. -/
theorem add_one_fourth_le_mul_two_pow (u : ℕ) :
    ((u + 1) * (u + 1)) * ((u + 1) * (u + 1)) ≤ 144 * 2 ^ u := by
  have h := add_one_sq_le_twelve_mul_two_pow_div_two u
  have hpow : 2 ^ (u / 2) * 2 ^ (u / 2) ≤ 2 ^ u := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc ((u + 1) * (u + 1)) * ((u + 1) * (u + 1))
      ≤ (12 * 2 ^ (u / 2)) * (12 * 2 ^ (u / 2)) := Nat.mul_le_mul h h
    _ = 144 * (2 ^ (u / 2) * 2 ^ (u / 2)) := by ring
    _ ≤ 144 * 2 ^ u := Nat.mul_le_mul_left 144 hpow

/-- Corollary of `add_one_fourth_le_mul_two_pow`: for every $L \in \mathbb{N}$,
`(L * L) * (L * L) ≤ 2304 * 2 ^ (L / 2)`. -/
theorem fourth_le_2304_mul_two_pow_div_two (L : ℕ) :
    (L * L) * (L * L) ≤ 2304 * 2 ^ (L / 2) := by
  have h1 : L ≤ 2 * (L / 2 + 1) := by omega
  have h2 : L * L ≤ (2 * (L / 2 + 1)) * (2 * (L / 2 + 1)) := Nat.mul_le_mul h1 h1
  calc (L * L) * (L * L)
      ≤ ((2 * (L / 2 + 1)) * (2 * (L / 2 + 1))) *
          ((2 * (L / 2 + 1)) * (2 * (L / 2 + 1))) := Nat.mul_le_mul h2 h2
    _ = 16 * (((L / 2 + 1) * (L / 2 + 1)) * ((L / 2 + 1) * (L / 2 + 1))) := by ring
    _ ≤ 16 * (144 * 2 ^ (L / 2)) :=
        Nat.mul_le_mul_left 16 (add_one_fourth_le_mul_two_pow (L / 2))
    _ = 2304 * 2 ^ (L / 2) := by ring

/-- Elementary cubic exponential domination `(m + 1) * (m + 1) * (m + 1) ≤ 9 * 2 ^ m` for all $m \in \mathbb{N}$. -/
theorem add_one_cube_le_nine_mul_two_pow (m : ℕ) :
    (m + 1) * (m + 1) * (m + 1) ≤ 9 * 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rcases lt_or_ge m 6 with hlt | hge
    · interval_cases m <;> norm_num
    · have h1 : 3 * m * m + 9 * m + 7 ≤ 6 * ((m + 1) * (m + 1)) := by nlinarith
      have h2 : 6 * ((m + 1) * (m + 1)) ≤ (m + 1) * ((m + 1) * (m + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : 3 * m * m + 9 * m + 7 ≤ (m + 1) * (m + 1) * (m + 1) := by linarith
      calc (m + 1 + 1) * (m + 1 + 1) * (m + 1 + 1)
          = (m + 1) * (m + 1) * (m + 1) + (3 * m * m + 9 * m + 7) := by ring
        _ ≤ (m + 1) * (m + 1) * (m + 1) + (m + 1) * (m + 1) * (m + 1) := Nat.add_le_add_left h3 _
        _ = 2 * ((m + 1) * (m + 1) * (m + 1)) := by ring
        _ ≤ 2 * (9 * 2 ^ m) := Nat.mul_le_mul_left 2 ih
        _ = 9 * 2 ^ (m + 1) := by rw [pow_succ']; ring

/-- Corollary of `add_one_cube_le_nine_mul_two_pow`: for every $L \in \mathbb{N}$,
`L * L * L ≤ 72 * 2 ^ (L / 2)`. -/
theorem cube_le_seventy_two_mul_two_pow_div_two (L : ℕ) :
    L * L * L ≤ 72 * 2 ^ (L / 2) := by
  have h1 : L ≤ 2 * (L / 2 + 1) := by omega
  have h2 : L * L ≤ (2 * (L / 2 + 1)) * (2 * (L / 2 + 1)) := Nat.mul_le_mul h1 h1
  calc L * L * L
      ≤ ((2 * (L / 2 + 1)) * (2 * (L / 2 + 1))) * (2 * (L / 2 + 1)) := Nat.mul_le_mul h2 h1
    _ = 8 * ((L / 2 + 1) * (L / 2 + 1) * (L / 2 + 1)) := by ring
    _ ≤ 8 * (9 * 2 ^ (L / 2)) := Nat.mul_le_mul_left 8 (add_one_cube_le_nine_mul_two_pow (L / 2))
    _ = 72 * 2 ^ (L / 2) := by ring

theorem sq_le_twelve_mul_two_pow_div_two (L : ℕ) :
    L * L ≤ 12 * 2 ^ (L / 2) := by
  have h1 : L ≤ L + 1 := Nat.le_succ L
  calc L * L ≤ (L + 1) * (L + 1) := Nat.mul_le_mul h1 h1
    _ ≤ 12 * 2 ^ (L / 2) := add_one_sq_le_twelve_mul_two_pow_div_two L

theorem two_pow_rootK0_div_two_mul_self_le_rootR0 (n : ℕ) :
    2 ^ (rootK0 n / 2) * 2 ^ (rootK0 n / 2) ≤ rootR0 n := by
  unfold rootR0
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem two_pow_rootK0_div_two_mul_cube_le (n : ℕ) :
    2 ^ (rootK0 n / 2) * (rootK0 n * rootK0 n * rootK0 n) ≤ 72 * rootR0 n := by
  calc 2 ^ (rootK0 n / 2) * (rootK0 n * rootK0 n * rootK0 n)
      ≤ 2 ^ (rootK0 n / 2) * (72 * 2 ^ (rootK0 n / 2)) :=
        Nat.mul_le_mul_left _ (cube_le_seventy_two_mul_two_pow_div_two (rootK0 n))
    _ = 72 * (2 ^ (rootK0 n / 2) * 2 ^ (rootK0 n / 2)) := by ring
    _ ≤ 72 * rootR0 n := Nat.mul_le_mul_left 72 (two_pow_rootK0_div_two_mul_self_le_rootR0 n)

theorem rootK0_fifth_le (n : ℕ) :
    (rootK0 n * rootK0 n) * (rootK0 n * rootK0 n * rootK0 n) ≤ 864 * rootR0 n := by
  calc (rootK0 n * rootK0 n) * (rootK0 n * rootK0 n * rootK0 n)
      ≤ (12 * 2 ^ (rootK0 n / 2)) * (72 * 2 ^ (rootK0 n / 2)) :=
        Nat.mul_le_mul (sq_le_twelve_mul_two_pow_div_two (rootK0 n))
          (cube_le_seventy_two_mul_two_pow_div_two (rootK0 n))
    _ = 864 * (2 ^ (rootK0 n / 2) * 2 ^ (rootK0 n / 2)) := by ring
    _ ≤ 864 * rootR0 n := Nat.mul_le_mul_left 864 (two_pow_rootK0_div_two_mul_self_le_rootR0 n)

theorem two_pow_rootK0_div_two_mul_fourth_le (n : ℕ) :
    2 ^ (rootK0 n / 2) * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n)) ≤
      2304 * rootR0 n := by
  calc 2 ^ (rootK0 n / 2) * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))
      ≤ 2 ^ (rootK0 n / 2) * (2304 * 2 ^ (rootK0 n / 2)) :=
        Nat.mul_le_mul_left _ (fourth_le_2304_mul_two_pow_div_two (rootK0 n))
    _ = 2304 * (2 ^ (rootK0 n / 2) * 2 ^ (rootK0 n / 2)) := by ring
    _ ≤ 2304 * rootR0 n := Nat.mul_le_mul_left 2304 (two_pow_rootK0_div_two_mul_self_le_rootR0 n)

theorem rootK0_sixth_le (n : ℕ) :
    (rootK0 n * rootK0 n) * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n)) ≤
      27648 * rootR0 n := by
  calc (rootK0 n * rootK0 n) * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))
      ≤ (12 * 2 ^ (rootK0 n / 2)) * (2304 * 2 ^ (rootK0 n / 2)) :=
        Nat.mul_le_mul (sq_le_twelve_mul_two_pow_div_two (rootK0 n))
          (fourth_le_2304_mul_two_pow_div_two (rootK0 n))
    _ = 27648 * (2 ^ (rootK0 n / 2) * 2 ^ (rootK0 n / 2)) := by ring
    _ ≤ 27648 * rootR0 n := Nat.mul_le_mul_left 27648 (two_pow_rootK0_div_two_mul_self_le_rootR0 n)

/-- Root chunk bit-width is bounded linearly by `rootK0 n`: `chunkBits n ≤ 2 * rootK0 n + 2` for all $n$. -/
theorem chunkBits_le_two_mul_rootK0_add_two (n : ℕ) :
    chunkBits n ≤ 2 * rootK0 n + 2 := by
  set b := chunkBits n
  set K0 := rootK0 n
  have hK0_ge : 2 ≤ K0 := rootK0_ge_two n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change max 4 (Nat.log 2 0) ≤ 2 * K0 + 2
    have : Nat.log 2 0 = 0 := rfl
    omega
  · rcases le_total (Nat.log 2 n) 4 with hlog | hlog
    · have hb4 : b = 4 := by
        change max 4 (Nat.log 2 n) = 4
        exact max_eq_left hlog
      omega
    · have hb_eq : b = Nat.log 2 n := by
        change max 4 (Nat.log 2 n) = Nat.log 2 n
        exact max_eq_right hlog
      have hpow_b : 2 ^ b ≤ n := by
        rw [hb_eq]
        exact Nat.pow_log_le_self 2 (by omega)
      have hn_le : 2 * n ≤ (2 ^ K0) * b := by
        have h1 := n_le_numChunks_mul_chunkBits n
        have h2 := two_mul_numChunks_le_rootR0 n
        unfold rootR0 at h2
        calc 2 * n ≤ 2 * (numChunks n * b) := Nat.mul_le_mul_left 2 h1
          _ = (2 * numChunks n) * b := by ring
          _ ≤ (2 ^ K0) * b := Nat.mul_le_mul_right b h2
      have hb_pow : b < 2 ^ (b / 2 + 2) := by
        have hsq := add_one_sq_le_three_mul_two_pow (b / 2)
        have hb_div : b ≤ 2 * (b / 2) + 1 := by omega
        have hb_le_sq : b + 1 ≤ (b / 2 + 1) * (b / 2 + 1) := by nlinarith
        have h3_lt : 3 * 2 ^ (b / 2) < 4 * 2 ^ (b / 2) := by
          have : 0 < 2 ^ (b / 2) := Nat.two_pow_pos (b / 2)
          omega
        have h4_eq : 4 * 2 ^ (b / 2) = 2 ^ (b / 2 + 2) := by
          rw [pow_add]; ring
        omega
      have hpow_lt : 2 ^ (b + 1) < 2 ^ (K0 + (b / 2 + 2)) := by
        have h2K0_pos : 0 < 2 ^ K0 := Nat.two_pow_pos K0
        calc 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ']
          _ ≤ 2 * n := Nat.mul_le_mul_left 2 hpow_b
          _ ≤ (2 ^ K0) * b := hn_le
          _ < (2 ^ K0) * 2 ^ (b / 2 + 2) := Nat.mul_lt_mul_of_pos_left hb_pow h2K0_pos
          _ = 2 ^ (K0 + (b / 2 + 2)) := (pow_add 2 K0 (b / 2 + 2)).symm
      have hexp_lt : b + 1 < K0 + (b / 2 + 2) := by
        by_contra hge
        push_neg at hge
        exact not_le_of_gt hpow_lt (Nat.pow_le_pow_right (by norm_num) hge)
      omega

/-- Root precision is bounded linearly by `rootK0 n`: `rootP0 n ≤ 11 * rootK0 n` for all $n \in \mathbb{N}$. -/
theorem rootP0_le_eleven_mul_rootK0 (n : ℕ) : rootP0 n ≤ 11 * rootK0 n := by
  unfold rootP0
  have hb := chunkBits_le_two_mul_rootK0_add_two n
  have hK0 := rootK0_ge_two n
  omega

/-- Per-entry series operation bound `scheduleSeriesTerms q * (q + subMulBitOps q) ≤ 2801937600 * rootK0 n ^ 4`
for any precision `q ≤ 12 * rootP0 n` along the schedule. -/
theorem scheduleSeriesCost_le_of_le {n q : ℕ} (hq : q ≤ 12 * rootP0 n) :
    scheduleSeriesTerms q * (q + subMulBitOps q) ≤
      2801937600 * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n)) := by
  have hp0_K0 : rootP0 n ≤ 11 * rootK0 n := rootP0_le_eleven_mul_rootK0 n
  have hK0_ge2 : 2 ≤ rootK0 n := rootK0_ge_two n
  have hq_K0 : q ≤ 132 * rootK0 n := by omega
  have hq1_K0 : q + 1 ≤ 133 * rootK0 n := by omega
  have hterms : scheduleSeriesTerms q ≤ 2122680 * (rootK0 n * rootK0 n) := by
    unfold scheduleSeriesTerms
    calc 120 * (q + 1) * (q + 1)
        = 120 * ((q + 1) * (q + 1)) := by ring
      _ ≤ 120 * ((133 * rootK0 n) * (133 * rootK0 n)) :=
          Nat.mul_le_mul_left 120 (Nat.mul_le_mul hq1_K0 hq1_K0)
      _ = 2122680 * (rootK0 n * rootK0 n) := by ring
  have hlog_q : Nat.log 2 q + 1 ≤ 5 * rootK0 n := by
    rcases Nat.eq_zero_or_pos q with rfl | hq_pos
    · simp; omega
    · have hK0_pow : rootK0 n ≤ 2 ^ (rootK0 n) := le_of_lt Nat.lt_two_pow_self
      have h1_pow : 1 ≤ 2 ^ (rootK0 n) := Nat.one_le_two_pow
      have hpow8 : 2 ^ (rootK0 n + 8) = 256 * 2 ^ (rootK0 n) := by rw [pow_add]; ring
      have hlt_pow : q < 2 ^ (rootK0 n + 8) := by omega
      have hlog_lt : Nat.log 2 q < rootK0 n + 8 := Nat.log_lt_of_lt_pow (by omega) hlt_pow
      omega
  have hmul_cost : q + subMulBitOps q ≤ 1320 * (rootK0 n * rootK0 n) := by
    unfold subMulBitOps
    have h1 : q + q * (Nat.log 2 q + 1) ≤ (2 * q) * (Nat.log 2 q + 1) := by nlinarith
    have h2q : 2 * q ≤ 264 * rootK0 n := by omega
    calc q + q * (Nat.log 2 q + 1)
        ≤ (2 * q) * (Nat.log 2 q + 1) := h1
      _ ≤ (264 * rootK0 n) * (5 * rootK0 n) := Nat.mul_le_mul h2q hlog_q
      _ = 1320 * (rootK0 n * rootK0 n) := by ring
  calc scheduleSeriesTerms q * (q + subMulBitOps q)
      ≤ (2122680 * (rootK0 n * rootK0 n)) * (1320 * (rootK0 n * rootK0 n)) :=
        Nat.mul_le_mul hterms hmul_cost
    _ = 2801937600 * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n)) := by ring

/-- At any internal level $\ell < \text{recursionDepth (rootK0 n) (rootP0 n)}$, the marginal table
entry count `scheduleNodeTableEntries K_ell p_ell` is at most `33 * rootP0 n * (2 ^ (rootK0 n / 2))`. -/
theorem scheduleNodeTableEntries_level_le {n ell : ℕ}
    (hlt : ell < recursionDepth (rootK0 n) (rootP0 n)) :
    let K := levelK (rootK0 n) ell
    let p := levelP (rootK0 n) (rootP0 n) ell
    scheduleNodeTableEntries K p ≤ 33 * rootP0 n * (2 ^ (rootK0 n / 2)) := by
  intro K p
  have hK_le : K ≤ rootK0 n := levelK_le_K0 (rootK0 n) ell
  have ht1_le : t1Ell K ≤ 2 ^ (rootK0 n / 2) := by
    unfold t1Ell k1Ell
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr_le : rEll K ≤ 2 * 2 ^ (rootK0 n / 2) := by
    unfold rEll k2Ell
    calc 2 ^ ((K + 1) / 2)
        ≤ 2 ^ (rootK0 n / 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ (rootK0 n / 2) := by rw [pow_succ']
  have hq : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
  have hm1 : computeM1Ell K p ≤ qChildEll K p := by
    have h1 := computeM1Ell_le_pChildEll K p
    unfold qChildEll
    omega
  have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
  have hwin : 2 * computeM1Ell K p + 1 ≤ 25 * rootP0 n := by omega
  have hpart1 : t1Ell K * (2 * computeM1Ell K p + 1) ≤ 25 * rootP0 n * (2 ^ (rootK0 n / 2)) := by
    calc t1Ell K * (2 * computeM1Ell K p + 1)
        ≤ (2 ^ (rootK0 n / 2)) * (25 * rootP0 n) := Nat.mul_le_mul ht1_le hwin
      _ = 25 * rootP0 n * (2 ^ (rootK0 n / 2)) := by ring
  have hpart2 : 4 * rEll K ≤ 8 * rootP0 n * (2 ^ (rootK0 n / 2)) := by
    calc 4 * rEll K
        ≤ 4 * (2 * 2 ^ (rootK0 n / 2)) := Nat.mul_le_mul_left 4 hr_le
      _ = 8 * (1 * (2 ^ (rootK0 n / 2))) := by ring
      _ ≤ 8 * (rootP0 n * (2 ^ (rootK0 n / 2))) :=
          Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right _ (by omega))
      _ = 8 * rootP0 n * (2 ^ (rootK0 n / 2)) := by ring
  unfold scheduleNodeTableEntries
  linarith

/-- At any leaf level along the schedule, `2 ^ K_ell ≤ 5324 * rootP0 n * (rootK0 n * rootK0 n)`. -/
theorem leafTableEntries_level_le {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n))
    (hleaf : ¬ ((!isBaseLeaf (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)) = true ∧
      2 ≤ levelK (rootK0 n) ell)) :
    2 ^ levelK (rootK0 n) ell ≤ 5324 * rootP0 n * (rootK0 n * rootK0 n) := by
  set K := levelK (rootK0 n) ell
  set p := levelP (rootK0 n) (rootP0 n) ell
  have hp0_ge18 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
  have hp_ge_p0 : rootP0 n ≤ p := levelP_ge_p0 (rootK0 n) (rootP0 n) ell
  have hp_le : p ≤ 11 * rootP0 n := levelP_le_eleven_mul_rootP0 hell
  have hp0_K0 : rootP0 n ≤ 11 * rootK0 n := rootP0_le_eleven_mul_rootK0 n
  have hK0_ge2 : 2 ≤ rootK0 n := rootK0_ge_two n
  have h2K_le_4p2 : 2 ^ K ≤ 4 * p * p := by
    by_cases hK2 : 2 ≤ K
    · have hbase : isBaseLeaf K p = true := by
        cases h : isBaseLeaf K p
        · exfalso; exact hleaf ⟨by simp [h], hK2⟩
        · rfl
      unfold isBaseLeaf at hbase
      rw [decide_eq_true_eq] at hbase
      exact hbase
    · have hK_le1 : K ≤ 1 := by omega
      have h2K : 2 ^ K ≤ 2 := by
        calc 2 ^ K ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hK_le1
          _ = 2 := by norm_num
      nlinarith
  have hp_K02 : p ≤ 121 * (rootK0 n * rootK0 n) := by nlinarith
  calc 2 ^ K ≤ 4 * p * p := h2K_le_4p2
    _ = 4 * (p * p) := by ring
    _ ≤ 4 * ((11 * rootP0 n) * (121 * (rootK0 n * rootK0 n))) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul hp_le hp_K02)
    _ = 5324 * rootP0 n * (rootK0 n * rootK0 n) := by ring

/-- **Unconditional Multi-Level Bound on `scheduleTreeGenOps subMulBitOps`
(`scheduleTreeGenOps_subMulBitOps_level_le`)**:
For every $n \in \mathbb{N}$ and every active recursion level $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$
with remaining depth $d = \text{recursionDepth (rootK0 n) (rootP0 n)} - \ell$,
$$\text{scheduleTreeGenOps } \text{subMulBitOps} \, K_\ell \, p_\ell \le 412439476351795200 \cdot R_0(n) \cdot p_0(n) \cdot (d + 1).$$ -/
theorem scheduleTreeGenOps_subMulBitOps_level_le (n : ℕ) :
    ∀ (d ell : ℕ),
      ell ≤ recursionDepth (rootK0 n) (rootP0 n) →
      recursionDepth (rootK0 n) (rootP0 n) - ell = d →
      scheduleTreeGenOps subMulBitOps
        (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) ≤
        412439476351795200 * rootR0 n * rootP0 n * (d + 1) := by
  intro d
  induction d with
  | zero =>
    intro ell hell hd
    have hell_eq : ell = recursionDepth (rootK0 n) (rootP0 n) := by omega
    subst hell_eq
    have hp0 : 1 ≤ rootP0 n := by have := rootP0_ge_eighteen n; omega
    have hleaf_true :
        isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
          (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) = true :=
      isBaseLeaf_recursionDepth (rootK0 n) (rootP0 n) hp0
    have hnot :
        ¬ ((!isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) = true ∧
          2 ≤ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) := by
      simp [hleaf_true]
    rw [scheduleTreeGenOps, if_neg hnot]
    have hentries := leafTableEntries_level_le hell hnot
    have hseries := scheduleSeriesCost_le_of_le (qBaseEll_level_le hell)
    have hsixth := rootK0_sixth_le n
    calc (2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) *
          scheduleSeriesTerms (qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) *
          (qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) +
            subMulBitOps (qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
              (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))))
        = (2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) *
            (scheduleSeriesTerms (qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
              (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) *
            (qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
              (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) +
              subMulBitOps (qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
                (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))))) := by ring
      _ ≤ (5324 * rootP0 n * (rootK0 n * rootK0 n)) *
            (2801937600 * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))) :=
          Nat.mul_le_mul hentries hseries
      _ = 14917515782400 * rootP0 n *
            ((rootK0 n * rootK0 n) * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))) := by ring
      _ ≤ 14917515782400 * rootP0 n * (27648 * rootR0 n) := Nat.mul_le_mul_left _ hsixth
      _ = 412439476351795200 * rootR0 n * rootP0 n * (0 + 1) := by ring
  | succ d ih =>
    intro ell hell hd
    have hlt : ell < recursionDepth (rootK0 n) (rootP0 n) := by omega
    rw [scheduleTreeGenOps]
    split_ifs with hcond
    · set K := levelK (rootK0 n) ell
      set p := levelP (rootK0 n) (rootP0 n) ell
      have hentries : scheduleNodeTableEntries K p ≤ 33 * rootP0 n * (2 ^ (rootK0 n / 2)) :=
        scheduleNodeTableEntries_level_le hlt
      have hseries := scheduleSeriesCost_le_of_le (qChildEll_level_le hlt)
      have hfourth := two_pow_rootK0_div_two_mul_fourth_le n
      have hnode :
          scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + subMulBitOps (qChildEll K p)) ≤
            412439476351795200 * rootR0 n * rootP0 n := by
        have h1 :
            scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
              (qChildEll K p + subMulBitOps (qChildEll K p)) ≤
              213036919603200 * rootR0 n * rootP0 n := by
          calc scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
                (qChildEll K p + subMulBitOps (qChildEll K p))
              = scheduleNodeTableEntries K p *
                  (scheduleSeriesTerms (qChildEll K p) *
                    (qChildEll K p + subMulBitOps (qChildEll K p))) := by ring
            _ ≤ (33 * rootP0 n * (2 ^ (rootK0 n / 2))) *
                  (2801937600 * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))) :=
                Nat.mul_le_mul hentries hseries
            _ = 92463940800 * rootP0 n *
                  (2 ^ (rootK0 n / 2) * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))) := by ring
            _ ≤ 92463940800 * rootP0 n * (2304 * rootR0 n) := Nat.mul_le_mul_left _ hfourth
            _ = 213036919603200 * rootR0 n * rootP0 n := by ring
        exact le_trans h1 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
      have hchild :
          scheduleTreeGenOps subMulBitOps (k2Ell K) (pChildEll K p) ≤
            412439476351795200 * rootR0 n * rootP0 n * (d + 1) :=
        ih (ell + 1) (Nat.succ_le_of_lt hlt) (by omega)
      calc scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + subMulBitOps (qChildEll K p)) +
            scheduleTreeGenOps subMulBitOps (k2Ell K) (pChildEll K p)
          ≤ 412439476351795200 * rootR0 n * rootP0 n +
              412439476351795200 * rootR0 n * rootP0 n * (d + 1) := Nat.add_le_add hnode hchild
        _ = 412439476351795200 * rootR0 n * rootP0 n * (d + 1 + 1) := by ring
    · have hentries := leafTableEntries_level_le hell hcond
      have hseries := scheduleSeriesCost_le_of_le (qBaseEll_level_le hell)
      have hsixth := rootK0_sixth_le n
      have hleaf_cost :
          (2 ^ levelK (rootK0 n) ell) *
            scheduleSeriesTerms (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)) *
            (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) +
              subMulBitOps (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell))) ≤
            412439476351795200 * rootR0 n * rootP0 n := by
        calc (2 ^ levelK (rootK0 n) ell) *
              scheduleSeriesTerms (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)) *
              (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) +
                subMulBitOps (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)))
            = (2 ^ levelK (rootK0 n) ell) *
                (scheduleSeriesTerms (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)) *
                (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) +
                  subMulBitOps (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)))) := by ring
          _ ≤ (5324 * rootP0 n * (rootK0 n * rootK0 n)) *
                (2801937600 * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))) :=
              Nat.mul_le_mul hentries hseries
          _ = 14917515782400 * rootP0 n *
                ((rootK0 n * rootK0 n) * ((rootK0 n * rootK0 n) * (rootK0 n * rootK0 n))) := by ring
          _ ≤ 14917515782400 * rootP0 n * (27648 * rootR0 n) := Nat.mul_le_mul_left _ hsixth
          _ = 412439476351795200 * rootR0 n * rootP0 n := by ring
      calc (2 ^ levelK (rootK0 n) ell) *
            scheduleSeriesTerms (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)) *
            (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) +
              subMulBitOps (qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)))
          ≤ (412439476351795200 * rootR0 n * rootP0 n) * 1 := by linarith
        _ ≤ (412439476351795200 * rootR0 n * rootP0 n) * (d + 1 + 1) :=
            Nat.mul_le_mul_left _ (by omega)

/-- **Unconditional Root Operation Bound for `scheduleTreeGenOps subMulBitOps`
(`scheduleTreeGenOps_subMulBitOps_root_le`)**:
For every $n \in \mathbb{N}$,
$$\text{scheduleTreeGenOps } \text{subMulBitOps} \, (K_0(n)) \, (p_0(n)) \le 824878952703590400 \cdot R_0(n) \cdot p_0(n) \cdot K_0(n).$$ -/
theorem scheduleTreeGenOps_subMulBitOps_root_le (n : ℕ) :
    scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) ≤
      824878952703590400 * rootR0 n * rootP0 n * rootK0 n := by
  have h0 := scheduleTreeGenOps_subMulBitOps_level_le n
    (recursionDepth (rootK0 n) (rootP0 n)) 0 (Nat.zero_le _) (Nat.sub_zero _)
  change scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) ≤
    412439476351795200 * rootR0 n * rootP0 n * (recursionDepth (rootK0 n) (rootP0 n) + 1) at h0
  have hrec : recursionDepth (rootK0 n) (rootP0 n) + 1 ≤ 2 * rootK0 n := by
    have h1 := recursionDepth_le_K0 (rootK0 n) (rootP0 n)
    have h2 := rootK0_ge_two n
    omega
  calc scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n)
      ≤ 412439476351795200 * rootR0 n * rootP0 n * (recursionDepth (rootK0 n) (rootP0 n) + 1) := h0
    _ ≤ 412439476351795200 * rootR0 n * rootP0 n * (2 * rootK0 n) := Nat.mul_le_mul_left _ hrec
    _ = 824878952703590400 * rootR0 n * rootP0 n * rootK0 n := by ring

/-- Root operation bound for `scheduleTreeGenOps (fun q => q)`. -/
theorem scheduleTreeGenOps_root_le (n : ℕ) :
    scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n) ≤
      824878952703590400 * rootR0 n * rootP0 n * rootK0 n := by
  have hmono : scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n) ≤
      1 * scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) :=
    scheduleTreeGenOps_scale_le (le_refl 1) (fun q => by rw [one_mul]; exact le_subMulBitOps q)
      (rootK0 n) (rootP0 n)
  rw [one_mul] at hmono
  exact le_trans hmono (scheduleTreeGenOps_subMulBitOps_root_le n)

/-- **Unconditional $O(n \log n)$ Upper Bound on `intMulAlgorithmSteps` for all $n \ge 1$
(`intMulAlgorithmSteps_le_n_log_n_succ`, Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`))**:
For every $n \ge 1$, the full end-to-end recursive multiplication algorithm operation count
`intMulAlgorithmSteps (fun q => q) n` (including schedule & `ScheduleIntTree` generation with
$O(q)$ series recurrence iterations per table entry, chunk unpacking, forward & inverse
`fastDFTRecursive`, pointwise squaring, and carry-save reconstruction) is bounded by
`277159328108409262726 * n * (Nat.log 2 n + 1)`. -/
theorem intMulAlgorithmSteps_le_n_log_n_succ {n : ℕ} (hn : 1 ≤ n) :
    intMulAlgorithmSteps (fun q => q) n ≤ 277159328108409262726 * n * (Nat.log 2 n + 1) := by
  unfold intMulAlgorithmSteps
  have hlog_pos : 1 ≤ Nat.log 2 n + 1 := by omega
  have hsched : scheduleBitsLen n ≤ 70 * n * (Nat.log 2 n + 1) := by
    rw [scheduleBitsLen_eq]
    have h1 : 14 * n + 56 ≤ 70 * n := by omega
    calc
      14 * n + 56 ≤ 70 * n := h1
      _ = (70 * n) * 1 := (mul_one _).symm
      _ ≤ 70 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (70 * n) hlog_pos
  have htable := fullScheduleTableBitsLen_le_succ hn
  have hfast :
      fastDFTRecursiveSteps (fun q => q) (rootK0 n) (rootP0 n)
        (levelScheduleBIn (rootK0 n) (rootP0 n) 0) ≤
        1443456 * n * (Nat.log 2 n + 1) := by
    calc
      fastDFTRecursiveSteps (fun q => q) (rootK0 n) (rootP0 n)
          (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
        ≤ 4296 * rootR0 n * rootP0 n * rootK0 n := fastDFTRecursiveSteps_root_le n _ (le_refl _)
      _ = 4296 * (rootR0 n * rootP0 n * rootK0 n) := by ring
      _ ≤ 4296 * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left 4296 (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 1443456 * n * (Nat.log 2 n + 1) := by ring
  have htree :
      scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n) ≤
        277159328108406374400 * n * (Nat.log 2 n + 1) := by
    calc
      scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n)
        ≤ 824878952703590400 * rootR0 n * rootP0 n * rootK0 n := scheduleTreeGenOps_root_le n
      _ = 824878952703590400 * (rootR0 n * rootP0 n * rootK0 n) := by ring
      _ ≤ 824878952703590400 * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left 824878952703590400 (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 277159328108406374400 * n * (Nat.log 2 n + 1) := by ring
  have hsq : 3 * rootR0 n * (rootP0 n + 2) ≤ 1008 * n * (Nat.log 2 n + 1) := by
    have hp2 : rootP0 n + 2 ≤ 2 * rootP0 n := by
      have := rootP0_ge_eighteen n
      omega
    have hRP := rootR0_mul_rootP0_le hn
    have h1 : 3 * rootR0 n * (rootP0 n + 2) ≤ 1008 * n := by
      calc
        3 * rootR0 n * (rootP0 n + 2)
          ≤ 3 * rootR0 n * (2 * rootP0 n) := Nat.mul_le_mul_left (3 * rootR0 n) hp2
        _ = 6 * (rootR0 n * rootP0 n) := by ring
        _ ≤ 6 * (168 * n) := Nat.mul_le_mul_left 6 hRP
        _ = 1008 * n := by ring
    calc
      3 * rootR0 n * (rootP0 n + 2) ≤ 1008 * n := h1
      _ = (1008 * n) * 1 := (mul_one _).symm
      _ ≤ 1008 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (1008 * n) hlog_pos
  have hlin2 : 2 * n ≤ 2 * n * (Nat.log 2 n + 1) := by
    calc
      2 * n = (2 * n) * 1 := (mul_one _).symm
      _ ≤ 2 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (2 * n) hlog_pos
  have hlin4 : 4 * n ≤ 4 * n * (Nat.log 2 n + 1) := by
    calc
      4 * n = (4 * n) * 1 := (mul_one _).symm
      _ ≤ 4 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (4 * n) hlog_pos
  dsimp only
  calc
    scheduleBitsLen n + fullScheduleTableBitsLen n +
        scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n) + 2 * n +
        2 * fastDFTRecursiveSteps (fun q => q) (rootK0 n) (rootP0 n)
          (levelScheduleBIn (rootK0 n) (rootP0 n) 0) +
        3 * rootR0 n * (rootP0 n + 2) + 4 * n
      ≤ 70 * n * (Nat.log 2 n + 1) + 330 * n * (Nat.log 2 n + 1) +
          277159328108406374400 * n * (Nat.log 2 n + 1) + 2 * n * (Nat.log 2 n + 1) +
          2 * (1443456 * n * (Nat.log 2 n + 1)) +
          1008 * n * (Nat.log 2 n + 1) + 4 * n * (Nat.log 2 n + 1) := by
        refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsched htable) htree) hlin2)
          (Nat.mul_le_mul_left 2 hfast)) hsq) hlin4
    _ = 277159328108409262726 * n * (Nat.log 2 n + 1) := by ring

/-- **Unconditional $O(n \log n)$ Upper Bound on `intMulAlgorithmSteps` for all $n \ge 2$
(`intMulAlgorithmSteps_le_n_log_n`, Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`))**:
For every $n \ge 2$,
$$\text{intMulAlgorithmSteps } (\lambda q.\, q) \, n \le 554318656216818525452 \cdot n \cdot \lfloor \log_2 n \rfloor.$$ -/
theorem intMulAlgorithmSteps_le_n_log_n {n : ℕ} (hn : 2 ≤ n) :
    intMulAlgorithmSteps (fun q => q) n ≤ 554318656216818525452 * n * Nat.log 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hlog1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hlog_succ : Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n := by omega
  calc
    intMulAlgorithmSteps (fun q => q) n
      ≤ 277159328108409262726 * n * (Nat.log 2 n + 1) := intMulAlgorithmSteps_le_n_log_n_succ hn1
    _ ≤ 277159328108409262726 * n * (2 * Nat.log 2 n) :=
        Nat.mul_le_mul_left (277159328108409262726 * n) hlog_succ
    _ = 554318656216818525452 * n * Nat.log 2 n := by ring

/-- **Uniform Constant $O(n \log n)$ Step-Count Theorem for Linear Sub-Multiplication Weight
(`exists_uniform_C_intMulAlgorithmSteps_le`, Theorem 1 (`thm:main`), Section 7.2 (`sec:cost-proof`))**:
With quantifier order $\exists C > 0, \forall n \ge 2$, both `intMulAlgorithmSteps (fun q => q) n`
and `computableIntMulAlgorithmSteps (fun q => q) n (computeScheduleIntTree ...)` are bounded by
$C \cdot n \cdot \lfloor \log_2 n \rfloor$. -/
theorem exists_uniform_C_intMulAlgorithmSteps_le :
    ∃ C : ℕ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        intMulAlgorithmSteps (fun q => q) n ≤ C * n * Nat.log 2 n ∧
          computableIntMulAlgorithmSteps (fun q => q) n
            (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)) ≤
            C * n * Nat.log 2 n := by
  refine ⟨554318656216818525452, by norm_num, fun n hn => ?_⟩
  have h1 := intMulAlgorithmSteps_le_n_log_n hn
  have heq :
      computableIntMulAlgorithmSteps (fun q => q) n
        (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)) =
        intMulAlgorithmSteps (fun q => q) n := by
    unfold computableIntMulAlgorithmSteps intMulAlgorithmSteps
    rw [computableFastDFTRecursiveSteps_computeScheduleIntTree_eq]
  exact ⟨h1, heq.symm ▸ h1⟩

/-- Leaf step-count bound with $O(q \log q)$ sub-multiplications (`subMulBitOps`) at any
base-case leaf along the schedule (Theorem 1 (`thm:main`), proof Part 3 in Section 7.2 (`sec:cost-proof`)):
`leafDFTOps K_ell p_ell subMulBitOps ≤ 69696 * rootP0 n * (2 ^ K_ell) * rootK0 n`. -/
theorem leafDFTOps_subMulBitOps_level_le {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n))
    (hleaf : ¬ ((!isBaseLeaf (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)) = true ∧
      2 ≤ levelK (rootK0 n) ell)) :
    leafDFTOps (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) subMulBitOps ≤
      69696 * rootP0 n * (2 ^ levelK (rootK0 n) ell) * rootK0 n := by
  set K := levelK (rootK0 n) ell
  set p := levelP (rootK0 n) (rootP0 n) ell
  set qBase := qBaseEll K p
  have hp0_ge18 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
  have hp_ge_p0 : rootP0 n ≤ p := by
    dsimp [p]
    rw [levelP_eq_sum]
    omega
  have hp_le : p ≤ 11 * rootP0 n := levelP_le_eleven_mul_rootP0 hell
  have hqb_le : qBase ≤ 12 * rootP0 n := qBaseEll_level_le hell
  have hp0_K0 : rootP0 n ≤ 11 * rootK0 n := rootP0_le_eleven_mul_rootK0 n
  have h2K_le_4p2 : 2 ^ K ≤ (2 * p) * (2 * p) := by
    by_cases hK2 : 2 ≤ K
    · have hbase : isBaseLeaf K p = true := by
        cases h : isBaseLeaf K p
        · exfalso; exact hleaf ⟨by simp [h], hK2⟩
        · rfl
      unfold isBaseLeaf at hbase
      rw [decide_eq_true_eq] at hbase
      linarith
    · have hK_le1 : K ≤ 1 := by omega
      have h2K : 2 ^ K ≤ 2 := by
        calc 2 ^ K ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hK_le1
          _ = 2 := by norm_num
      nlinarith
  have h2K_half : 2 ^ (K / 2) ≤ 2 * p := by
    have hsq : (2 ^ (K / 2)) * (2 ^ (K / 2)) ≤ (2 * p) * (2 * p) := by
      calc (2 ^ (K / 2)) * (2 ^ (K / 2))
          = 2 ^ (K / 2 + K / 2) := (pow_add 2 (K / 2) (K / 2)).symm
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ (2 * p) * (2 * p) := h2K_le_4p2
    nlinarith
  have hqb_pos : qBase ≠ 0 := by unfold qBase qBaseEll; omega
  have h2log_qb : 2 ^ (Nat.log 2 qBase / 2) ≤ qBase := by
    calc 2 ^ (Nat.log 2 qBase / 2)
        ≤ 2 ^ (Nat.log 2 qBase) := Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ 2)
      _ ≤ qBase := Nat.pow_log_le_self 2 hqb_pos
  set L := max K (Nat.log 2 qBase)
  have h2L_half : 2 ^ (L / 2) ≤ 242 * rootK0 n := by
    rcases le_total K (Nat.log 2 qBase) with hle | hle
    · have hL : L = Nat.log 2 qBase := max_eq_right hle
      rw [hL]
      calc 2 ^ (Nat.log 2 qBase / 2) ≤ qBase := h2log_qb
        _ ≤ 12 * rootP0 n := hqb_le
        _ ≤ 22 * (11 * rootK0 n) := by omega
        _ = 242 * rootK0 n := by ring
    · have hL : L = K := max_eq_left hle
      rw [hL]
      calc 2 ^ (K / 2) ≤ 2 * p := h2K_half
        _ ≤ 22 * rootP0 n := by omega
        _ ≤ 22 * (11 * rootK0 n) := Nat.mul_le_mul_left 22 hp0_K0
        _ = 242 * rootK0 n := by ring
  have hprod_L : (K + 1) * (Nat.log 2 qBase + 1) ≤ 2904 * rootK0 n := by
    have hK_L : K + 1 ≤ L + 1 := Nat.add_le_add_right (le_max_left K _) 1
    have hlog_L : Nat.log 2 qBase + 1 ≤ L + 1 := Nat.add_le_add_right (le_max_right K _) 1
    calc (K + 1) * (Nat.log 2 qBase + 1)
        ≤ (L + 1) * (L + 1) := Nat.mul_le_mul hK_L hlog_L
      _ ≤ 12 * 2 ^ (L / 2) := add_one_sq_le_twelve_mul_two_pow_div_two L
      _ ≤ 12 * (242 * rootK0 n) := Nat.mul_le_mul_left 12 h2L_half
      _ = 2904 * rootK0 n := by ring
  unfold leafDFTOps subMulBitOps
  have hqb_factor : qBase + qBase * (Nat.log 2 qBase + 1) ≤
      (24 * rootP0 n) * (Nat.log 2 qBase + 1) := by
    have h1 : qBase + qBase * (Nat.log 2 qBase + 1) ≤ (2 * qBase) * (Nat.log 2 qBase + 1) := by
      nlinarith
    have h2 : 2 * qBase ≤ 24 * rootP0 n := by omega
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)
  calc (K + 1) * (2 ^ K) * (qBase + qBase * (Nat.log 2 qBase + 1))
      ≤ (K + 1) * (2 ^ K) * ((24 * rootP0 n) * (Nat.log 2 qBase + 1)) :=
        Nat.mul_le_mul_left _ hqb_factor
    _ = 24 * rootP0 n * (2 ^ K) * ((K + 1) * (Nat.log 2 qBase + 1)) := by ring
    _ ≤ 24 * rootP0 n * (2 ^ K) * (2904 * rootK0 n) :=
        Nat.mul_le_mul_left _ hprod_L
    _ = 69696 * rootP0 n * (2 ^ K) * rootK0 n := by ring

/-- **Unconditional Multi-Level Step-Count Telescoping Bound for `fastDFTRecursiveSteps subMulBitOps`
(`fastDFTRecursiveSteps_subMulBitOps_level_le`, Theorem 1 (`thm:main`), proof Parts 2–3 in
Section 7.2 (`sec:cost-proof`))**:
For every $n \in \mathbb{N}$, every active recursion level $\ell \le \text{recursionDepth (rootK0 n) (rootP0 n)}$,
and every input slot headroom $B_{\text{in}} \le \text{levelScheduleBIn (rootK0 n) (rootP0 n) } \ell$,
$$\text{fastDFTRecursiveSteps } \text{subMulBitOps} \, K_\ell \, p_\ell \, B_{\text{in}} \le
  11700 \cdot p_0(n) \cdot 2^{K_\ell} \cdot K_\ell + 69696 \cdot p_0(n) \cdot 2^{K_\ell} \cdot K_0(n).$$ -/
theorem fastDFTRecursiveSteps_subMulBitOps_level_le (n : ℕ) :
    ∀ (d ell B_in : ℕ),
      ell ≤ recursionDepth (rootK0 n) (rootP0 n) →
      B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) ell →
      recursionDepth (rootK0 n) (rootP0 n) - ell = d →
      fastDFTRecursiveSteps subMulBitOps
        (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) B_in ≤
        11700 * rootP0 n * (2 ^ levelK (rootK0 n) ell) * levelK (rootK0 n) ell +
          69696 * rootP0 n * (2 ^ levelK (rootK0 n) ell) * rootK0 n := by
  intro d
  induction d with
  | zero =>
    intro ell B_in hell _hB_in hd
    have hell_eq : ell = recursionDepth (rootK0 n) (rootP0 n) := by omega
    subst hell_eq
    have hp0 : 1 ≤ rootP0 n := by have := rootP0_ge_eighteen n; omega
    have hleaf_true :
        isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
          (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) = true :=
      isBaseLeaf_recursionDepth (rootK0 n) (rootP0 n) hp0
    have hnot :
        ¬ ((!isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) = true ∧
          2 ≤ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) := by
      simp [hleaf_true]
    rw [fastDFTRecursiveSteps_of_leaf _ hnot]
    have hleaf_le := leafDFTOps_subMulBitOps_level_le hell hnot
    omega
  | succ d ih =>
    intro ell B_in hell hB_in hd
    have hlt : ell < recursionDepth (rootK0 n) (rootP0 n) := by omega
    rw [fastDFTRecursiveSteps]
    split_ifs with hcond
    · set K := levelK (rootK0 n) ell
      set p := levelP (rootK0 n) (rootP0 n) ell
      have hK2 : 2 ≤ K := hcond.2
      have hk1_pos : 1 ≤ k1Ell K := by unfold k1Ell; omega
      have hK_le_k1 : K ≤ 3 * k1Ell K := by unfold k1Ell; omega
      have hq : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
      have hleaf_lt : 4 * p * p < 2 ^ K := by
        have h := hcond.1
        unfold isBaseLeaf at h
        rw [Bool.not_eq_true', decide_eq_false_iff_not, not_le] at h
        exact h
      have hlog_q : Nat.log 2 (qChildEll K p) + 1 ≤ 8 * k1Ell K := by
        have hp_lt : p < 2 ^ K := by
          rcases Nat.eq_zero_or_pos p with hp0 | hp_pos
          · rw [hp0]; exact Nat.two_pow_pos K
          · nlinarith
        have hK_le_pow : K ≤ 2 ^ K := le_of_lt Nat.lt_two_pow_self
        have h1_le_pow : 1 ≤ 2 ^ K := Nat.one_le_two_pow
        have hq_lt_pow : qChildEll K p < 2 ^ (K + 5) := by
          have hq_eq : qChildEll K p = p + 2 * K + 14 := qChildEll_eq K p
          have hpow5 : 2 ^ (K + 5) = 32 * 2 ^ K := by rw [pow_add]; ring
          omega
        have hlog_lt : Nat.log 2 (qChildEll K p) < K + 5 :=
          Nat.log_lt_of_lt_pow (by unfold qChildEll pChildEll pWorkEll; omega) hq_lt_pow
        omega
      set W_tilde := foldedHalfWidth (computeM1Ell K p) (rEll K)
      set B_slot := scheduleSlotBits K p B_in (computeM1Ell K p)
      set Q_kron := kroneckerPackedBitLength W_tilde B_slot
      have hlog_kron : Nat.log 2 Q_kron + 1 ≤ 10 * k1Ell K := by
        have hW_le_pow : W_tilde ≤ 2 ^ K := by
          have h1 : W_tilde ≤ rEll K := foldedHalfWidth_le_right (computeM1Ell K p) (rEll K)
          have h2 : rEll K ≤ 2 ^ K := by
            unfold rEll k2Ell
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          exact le_trans h1 h2
        have hB_le : B_slot ≤ 76 * rootP0 n := scheduleSlotBits_level_le hlt hB_in
        have hp0_ge18 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
        have hp_ge_p0 : rootP0 n ≤ p := levelP_ge_p0 (rootK0 n) (rootP0 n) ell
        have hB_lt_pow : B_slot < 5 * (2 ^ K) := by nlinarith
        have hQ_lt_pow : Q_kron < 2 ^ (2 * K + 4) := by
          have hpow4 : 2 ^ (2 * K + 4) = 16 * (2 ^ K) * (2 ^ K) := by
            rw [pow_add, Nat.two_mul, pow_add]; ring
          unfold Q_kron kroneckerPackedBitLength
          nlinarith
        have hlog_lt : Nat.log 2 Q_kron < 2 * K + 4 := by
          rcases Nat.eq_zero_or_pos Q_kron with h0 | hpos
          · rw [h0]; simp
          · exact Nat.log_lt_of_lt_pow (by omega) hQ_lt_pow
        omega
      have hstep1 : step1SpreadOps K p B_in ≤ 912 * rootP0 n * (2 ^ K) :=
        step1SpreadOps_level_le hlt hB_in
      have hmuls :
          stepFixedPointMuls K p B_in subMulBitOps ≤
            10656 * rootP0 n * (2 ^ K) * k1Ell K := by
        have hdef : stepFixedPointMuls K p B_in subMulBitOps =
            step1SpreadOps K p B_in * (Nat.log 2 Q_kron + 1) +
              16 * (2 ^ K) * (qChildEll K p * (Nat.log 2 (qChildEll K p) + 1)) := by
          unfold stepFixedPointMuls step1SpreadOps subMulBitOps
          dsimp only [W_tilde, B_slot, Q_kron]
          ring
        rw [hdef]
        have hm1 :
            step1SpreadOps K p B_in * (Nat.log 2 Q_kron + 1) ≤
              9120 * rootP0 n * (2 ^ K) * k1Ell K := by
          calc step1SpreadOps K p B_in * (Nat.log 2 Q_kron + 1)
              ≤ (912 * rootP0 n * (2 ^ K)) * (10 * k1Ell K) := Nat.mul_le_mul hstep1 hlog_kron
            _ = 9120 * rootP0 n * (2 ^ K) * k1Ell K := by ring
        have hm2 :
            16 * (2 ^ K) * (qChildEll K p * (Nat.log 2 (qChildEll K p) + 1)) ≤
              1536 * rootP0 n * (2 ^ K) * k1Ell K := by
          calc 16 * (2 ^ K) * (qChildEll K p * (Nat.log 2 (qChildEll K p) + 1))
              ≤ 16 * (2 ^ K) * ((12 * rootP0 n) * (8 * k1Ell K)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul hq hlog_q)
            _ = 1536 * rootP0 n * (2 ^ K) * k1Ell K := by ring
        calc step1SpreadOps K p B_in * (Nat.log 2 Q_kron + 1) +
              16 * (2 ^ K) * (qChildEll K p * (Nat.log 2 (qChildEll K p) + 1))
            ≤ 9120 * rootP0 n * (2 ^ K) * k1Ell K + 1536 * rootP0 n * (2 ^ K) * k1Ell K :=
              Nat.add_le_add hm1 hm2
          _ = 10656 * rootP0 n * (2 ^ K) * k1Ell K := by ring
      have hstep23 :
          step2SyntheticFFTOps K p + step3DeconvOps K p ≤
            132 * rootP0 n * (2 ^ K) * k1Ell K := by
        unfold step2SyntheticFFTOps step3DeconvOps
        have h11 : 10 + k1Ell K ≤ 11 * k1Ell K := by omega
        calc (2 + k1Ell K) * (2 ^ K) * qChildEll K p + 8 * (2 ^ K) * qChildEll K p
            = (10 + k1Ell K) * (2 ^ K) * qChildEll K p := by ring
          _ ≤ (11 * k1Ell K) * (2 ^ K) * (12 * rootP0 n) :=
              Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) h11) hq
          _ = 132 * rootP0 n * (2 ^ K) * k1Ell K := by ring
      have hstep1_k1 : step1SpreadOps K p B_in ≤ 912 * rootP0 n * (2 ^ K) * k1Ell K := by
        calc step1SpreadOps K p B_in
            ≤ (912 * rootP0 n * (2 ^ K)) * 1 := by linarith
          _ ≤ (912 * rootP0 n * (2 ^ K)) * k1Ell K := Nat.mul_le_mul_left _ hk1_pos
      have hinternal :
          step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
            stepFixedPointMuls K p B_in subMulBitOps + step3DeconvOps K p ≤
            11700 * rootP0 n * (2 ^ K) * k1Ell K := by
        calc step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
              stepFixedPointMuls K p B_in subMulBitOps + step3DeconvOps K p
            = step1SpreadOps K p B_in + (step2SyntheticFFTOps K p + step3DeconvOps K p) +
                stepFixedPointMuls K p B_in subMulBitOps := by ring
          _ ≤ 912 * rootP0 n * (2 ^ K) * k1Ell K + 132 * rootP0 n * (2 ^ K) * k1Ell K +
                10656 * rootP0 n * (2 ^ K) * k1Ell K :=
              Nat.add_le_add (Nat.add_le_add hstep1_k1 hstep23) hmuls
          _ = 11700 * rootP0 n * (2 ^ K) * k1Ell K := by ring
      have hB_child :
          childScheduleBIn K p B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) (ell + 1) := by
        unfold levelScheduleBIn childScheduleBIn
        exact Nat.add_le_add_right hB_in _
      have hrec :
          fastDFTRecursiveSteps subMulBitOps (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) ≤
            11700 * rootP0 n * (2 ^ k2Ell K) * k2Ell K +
              69696 * rootP0 n * (2 ^ k2Ell K) * rootK0 n :=
        ih (ell + 1) (childScheduleBIn K p B_in) (Nat.succ_le_of_lt hlt) hB_child (by omega)
      have hchild :
          t1Ell K * fastDFTRecursiveSteps subMulBitOps (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) ≤
            11700 * rootP0 n * (2 ^ K) * k2Ell K +
              69696 * rootP0 n * (2 ^ K) * rootK0 n := by
        have ht1r : t1Ell K * (2 ^ k2Ell K) = 2 ^ K := t1Ell_mul_rEll K
        calc t1Ell K * fastDFTRecursiveSteps subMulBitOps (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
            ≤ t1Ell K * (11700 * rootP0 n * (2 ^ k2Ell K) * k2Ell K +
                69696 * rootP0 n * (2 ^ k2Ell K) * rootK0 n) :=
              Nat.mul_le_mul_left (t1Ell K) hrec
          _ = 11700 * rootP0 n * (t1Ell K * (2 ^ k2Ell K)) * k2Ell K +
                69696 * rootP0 n * (t1Ell K * (2 ^ k2Ell K)) * rootK0 n := by ring
          _ = 11700 * rootP0 n * (2 ^ K) * k2Ell K +
                69696 * rootP0 n * (2 ^ K) * rootK0 n := by rw [ht1r]
      have hk_add : k1Ell K + k2Ell K = K := k1Ell_add_k2Ell K
      calc step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
            stepFixedPointMuls K p B_in subMulBitOps +
            t1Ell K * fastDFTRecursiveSteps subMulBitOps (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) +
            step3DeconvOps K p
          = (step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
              stepFixedPointMuls K p B_in subMulBitOps + step3DeconvOps K p) +
              t1Ell K * fastDFTRecursiveSteps subMulBitOps (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) := by
            ring
        _ ≤ 11700 * rootP0 n * (2 ^ K) * k1Ell K +
              (11700 * rootP0 n * (2 ^ K) * k2Ell K + 69696 * rootP0 n * (2 ^ K) * rootK0 n) :=
            Nat.add_le_add hinternal hchild
        _ = 11700 * rootP0 n * (2 ^ K) * (k1Ell K + k2Ell K) +
              69696 * rootP0 n * (2 ^ K) * rootK0 n := by ring
        _ = 11700 * rootP0 n * (2 ^ K) * K + 69696 * rootP0 n * (2 ^ K) * rootK0 n := by rw [hk_add]
    · have hleaf_le := leafDFTOps_subMulBitOps_level_le hell hcond
      omega

/-- **Unconditional Root Step-Count Bound for `fastDFTRecursiveSteps subMulBitOps`
(`fastDFTRecursiveSteps_subMulBitOps_root_le`, Theorem 1 (`thm:main`), proof Parts 2–3 in
Section 7.2 (`sec:cost-proof`))**:
For every $n \in \mathbb{N}$ and every root headroom $B_{\text{in}} \le \text{levelScheduleBIn (rootK0 n) (rootP0 n) } 0$,
$$\text{fastDFTRecursiveSteps } \text{subMulBitOps} \, (K_0(n)) \, (p_0(n)) \, B_{\text{in}} \le
  81396 \cdot R_0(n) \cdot p_0(n) \cdot K_0(n).$$ -/
theorem fastDFTRecursiveSteps_subMulBitOps_root_le (n B_in : ℕ)
    (hB_in : B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) 0) :
    fastDFTRecursiveSteps subMulBitOps (rootK0 n) (rootP0 n) B_in ≤
      81396 * rootR0 n * rootP0 n * rootK0 n := by
  have h0 := fastDFTRecursiveSteps_subMulBitOps_level_le n
    (recursionDepth (rootK0 n) (rootP0 n)) 0 B_in (Nat.zero_le _) hB_in (Nat.sub_zero _)
  change fastDFTRecursiveSteps subMulBitOps (rootK0 n) (rootP0 n) B_in ≤
    11700 * rootP0 n * rootR0 n * rootK0 n + 69696 * rootP0 n * rootR0 n * rootK0 n at h0
  calc fastDFTRecursiveSteps subMulBitOps (rootK0 n) (rootP0 n) B_in
      ≤ 11700 * rootP0 n * rootR0 n * rootK0 n + 69696 * rootP0 n * rootR0 n * rootK0 n := h0
    _ = 81396 * rootR0 n * rootP0 n * rootK0 n := by ring

/-- **Unconditional $O(n \log n)$ Upper Bound on `intMulAlgorithmSteps subMulBitOps` for all $n \ge 1$
(`intMulAlgorithmSteps_subMulBitOps_le_n_log_n_succ`, Theorem 1 (`thm:main`), proof Parts 2–3 in
Section 7.2 (`sec:cost-proof`))**:
With $O(q \log q)$ sub-multiplication cost `subMulBitOps q = q * (Nat.log 2 q + 1)`,
the full end-to-end recursive multiplication algorithm operation count
`intMulAlgorithmSteps subMulBitOps n` is bounded by `277159328108461097110 * n * (Nat.log 2 n + 1)`. -/
theorem intMulAlgorithmSteps_subMulBitOps_le_n_log_n_succ {n : ℕ} (hn : 1 ≤ n) :
    intMulAlgorithmSteps subMulBitOps n ≤ 277159328108461097110 * n * (Nat.log 2 n + 1) := by
  unfold intMulAlgorithmSteps
  have hlog_pos : 1 ≤ Nat.log 2 n + 1 := by omega
  have hsched : scheduleBitsLen n ≤ 70 * n * (Nat.log 2 n + 1) := by
    rw [scheduleBitsLen_eq]
    have h1 : 14 * n + 56 ≤ 70 * n := by omega
    calc 14 * n + 56 ≤ 70 * n := h1
      _ = (70 * n) * 1 := (mul_one _).symm
      _ ≤ 70 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (70 * n) hlog_pos
  have htable := fullScheduleTableBitsLen_le_succ hn
  have hfast :
      fastDFTRecursiveSteps subMulBitOps (rootK0 n) (rootP0 n)
        (levelScheduleBIn (rootK0 n) (rootP0 n) 0) ≤
        27349056 * n * (Nat.log 2 n + 1) := by
    calc fastDFTRecursiveSteps subMulBitOps (rootK0 n) (rootP0 n)
          (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
        ≤ 81396 * rootR0 n * rootP0 n * rootK0 n :=
          fastDFTRecursiveSteps_subMulBitOps_root_le n _ (le_refl _)
      _ = 81396 * (rootR0 n * rootP0 n * rootK0 n) := by ring
      _ ≤ 81396 * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left 81396 (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 27349056 * n * (Nat.log 2 n + 1) := by ring
  have htree :
      scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) ≤
        277159328108406374400 * n * (Nat.log 2 n + 1) := by
    calc scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n)
        ≤ 824878952703590400 * rootR0 n * rootP0 n * rootK0 n :=
          scheduleTreeGenOps_subMulBitOps_root_le n
      _ = 824878952703590400 * (rootR0 n * rootP0 n * rootK0 n) := by ring
      _ ≤ 824878952703590400 * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left 824878952703590400 (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 277159328108406374400 * n * (Nat.log 2 n + 1) := by ring
  have hsq : 3 * rootR0 n * subMulBitOps (rootP0 n + 2) ≤ 24192 * n * (Nat.log 2 n + 1) := by
    unfold subMulBitOps
    have hp0_ge18 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    have hK0_ge2 : 2 ≤ rootK0 n := rootK0_ge_two n
    have hp2 : rootP0 n + 2 ≤ 2 * rootP0 n := by omega
    have hlog_p2 : Nat.log 2 (rootP0 n + 2) + 1 ≤ 12 * rootK0 n := by
      have hsq := add_one_sq_le_three_mul_two_pow (rootP0 n)
      have hlt_sq : 3 * (rootP0 n + 2) < (rootP0 n + 1) * (rootP0 n + 1) := by nlinarith
      have hlt_pow : rootP0 n + 2 < 2 ^ (rootP0 n) := by omega
      have h1 : Nat.log 2 (rootP0 n + 2) < rootP0 n :=
        Nat.log_lt_of_lt_pow (by omega) hlt_pow
      have h2 : rootP0 n ≤ 11 * rootK0 n := rootP0_le_eleven_mul_rootK0 n
      omega
    calc 3 * rootR0 n * ((rootP0 n + 2) * (Nat.log 2 (rootP0 n + 2) + 1))
        ≤ 3 * rootR0 n * ((2 * rootP0 n) * (12 * rootK0 n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hp2 hlog_p2)
      _ = 72 * (rootR0 n * rootP0 n * rootK0 n) := by ring
      _ ≤ 72 * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left 72 (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 24192 * n * (Nat.log 2 n + 1) := by ring
  have hlin2 : 2 * n ≤ 2 * n * (Nat.log 2 n + 1) := by
    calc 2 * n = (2 * n) * 1 := (mul_one _).symm
      _ ≤ 2 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (2 * n) hlog_pos
  have hlin4 : 4 * n ≤ 4 * n * (Nat.log 2 n + 1) := by
    calc 4 * n = (4 * n) * 1 := (mul_one _).symm
      _ ≤ 4 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (4 * n) hlog_pos
  calc scheduleBitsLen n + fullScheduleTableBitsLen n +
        scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) + 2 * n +
        2 * fastDFTRecursiveSteps subMulBitOps (rootK0 n) (rootP0 n)
          (levelScheduleBIn (rootK0 n) (rootP0 n) 0) +
        3 * rootR0 n * subMulBitOps (rootP0 n + 2) + 4 * n
      ≤ 70 * n * (Nat.log 2 n + 1) + 330 * n * (Nat.log 2 n + 1) +
          277159328108406374400 * n * (Nat.log 2 n + 1) + 2 * n * (Nat.log 2 n + 1) +
          2 * (27349056 * n * (Nat.log 2 n + 1)) +
          24192 * n * (Nat.log 2 n + 1) + 4 * n * (Nat.log 2 n + 1) := by
        refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsched htable) htree) hlin2)
          (Nat.mul_le_mul_left 2 hfast)) hsq) hlin4
    _ = 277159328108461097110 * n * (Nat.log 2 n + 1) := by ring

/-- **Unconditional $O(n \log n)$ Upper Bound on `intMulAlgorithmSteps subMulBitOps` for all $n \ge 2$
(`intMulAlgorithmSteps_subMulBitOps_le_n_log_n`, Theorem 1 (`thm:main`), proof Parts 2–3 in
Section 7.2 (`sec:cost-proof`), equation (37) (`eq:main-bound`))**:
For every $n \ge 2$, with $O(q \log q)$ sub-multiplication cost `subMulBitOps`:
$$\text{intMulAlgorithmSteps } \text{subMulBitOps} \, n \le 554318656216922194220 \cdot n \cdot \lfloor \log_2 n \rfloor.$$ -/
theorem intMulAlgorithmSteps_subMulBitOps_le_n_log_n {n : ℕ} (hn : 2 ≤ n) :
    intMulAlgorithmSteps subMulBitOps n ≤ 554318656216922194220 * n * Nat.log 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hlog1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hlog_succ : Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n := by omega
  calc intMulAlgorithmSteps subMulBitOps n
      ≤ 277159328108461097110 * n * (Nat.log 2 n + 1) := intMulAlgorithmSteps_subMulBitOps_le_n_log_n_succ hn1
    _ ≤ 277159328108461097110 * n * (2 * Nat.log 2 n) :=
        Nat.mul_le_mul_left (277159328108461097110 * n) hlog_succ
    _ = 554318656216922194220 * n * Nat.log 2 n := by ring

/-- **Uniform Constant $O(n \log n)$ Step-Count Theorem with Recursive $O(q \log q)$ Sub-Multiplications
(`exists_uniform_C_intMulAlgorithmSteps_subMulBitOps_le`, Theorem 1 (`thm:main`), proof Parts 2–3 in
Section 7.2 (`sec:cost-proof`))**:
With quantifier order $\exists C > 0, \forall n \ge 2$, both `intMulAlgorithmSteps subMulBitOps n`
and `computableIntMulAlgorithmSteps subMulBitOps n (computeScheduleIntTree ...)` (charging
$q (\lfloor \log_2 q \rfloor + 1)$ bit operations for every $q$-bit sub-multiplication) are bounded
by $C \cdot n \cdot \lfloor \log_2 n \rfloor$. -/
theorem exists_uniform_C_intMulAlgorithmSteps_subMulBitOps_le :
    ∃ C : ℕ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        intMulAlgorithmSteps subMulBitOps n ≤ C * n * Nat.log 2 n ∧
          computableIntMulAlgorithmSteps subMulBitOps n
            (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)) ≤
            C * n * Nat.log 2 n := by
  refine ⟨554318656216922194220, by norm_num, fun n hn => ?_⟩
  have h1 := intMulAlgorithmSteps_subMulBitOps_le_n_log_n hn
  have heq :
      computableIntMulAlgorithmSteps subMulBitOps n
        (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)) =
        intMulAlgorithmSteps subMulBitOps n := by
    unfold computableIntMulAlgorithmSteps intMulAlgorithmSteps
    rw [computableFastDFTRecursiveSteps_computeScheduleIntTree_eq]
  exact ⟨h1, heq.symm ▸ h1⟩

/-- By depth $\ell = \lfloor \log_2 K_0 \rfloor + 1$, the log-length reaches $K_\ell \le 1$. -/
theorem levelK_log_add_one_le_one (K0 : ℕ) :
    levelK K0 (Nat.log 2 K0 + 1) ≤ 1 := by
  have hlt : K0 - 1 < 2 ^ (Nat.log 2 K0 + 1) :=
    lt_of_le_of_lt (Nat.sub_le K0 1) (Nat.lt_pow_succ_log_self (by norm_num) K0)
  have hdiv : (K0 - 1) / 2 ^ (Nat.log 2 K0 + 1) = 0 := Nat.div_eq_of_lt hlt
  have hsub := levelK_sub_one_eq K0 (Nat.log 2 K0 + 1)
  omega

/-- Whenever $p_0 \ge 1$, the base-case stopping rule `isBaseLeaf` holds by depth $\ell = \lfloor \log_2 K_0 \rfloor + 1$. -/
theorem isBaseLeaf_at_log_add_one (K0 p0 : ℕ) (hp0 : 1 ≤ p0) :
    isBaseLeaf (levelK K0 (Nat.log 2 K0 + 1)) (levelP K0 p0 (Nat.log 2 K0 + 1)) = true := by
  unfold isBaseLeaf
  rw [decide_eq_true_eq]
  have hk : levelK K0 (Nat.log 2 K0 + 1) ≤ 1 := levelK_log_add_one_le_one K0
  have hpow : 2 ^ levelK K0 (Nat.log 2 K0 + 1) ≤ 2 := by
    calc 2 ^ levelK K0 (Nat.log 2 K0 + 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 2 := by norm_num
  have hp : 1 ≤ levelP K0 p0 (Nat.log 2 K0 + 1) := le_trans hp0 (levelP_ge_p0 K0 p0 _)
  have hp2 : 4 ≤ 4 * levelP K0 p0 (Nat.log 2 K0 + 1) * levelP K0 p0 (Nat.log 2 K0 + 1) := by
    nlinarith
  omega

/-- **Logarithmic Recursion Depth Bound (`recursionDepth_le_log_add_one`,
Section 3.2 (`sec:prelim-model`) and Section 7.2 (`sec:cost-proof`))**:
For every $K_0 \in \mathbb{N}$ and $p_0 \ge 1$, $\text{recursionDepth } K_0 \, p_0 \le \lfloor \log_2 K_0 \rfloor + 1$. -/
theorem recursionDepth_le_log_add_one (K0 p0 : ℕ) (hp0 : 1 ≤ p0) :
    recursionDepth K0 p0 ≤ Nat.log 2 K0 + 1 := by
  by_contra hgt
  push_neg at hgt
  have hfalse := not_isBaseLeaf_of_lt_recursionDepth K0 p0 (Nat.log 2 K0 + 1) hgt
  have htrue := isBaseLeaf_at_log_add_one K0 p0 hp0
  rw [htrue] at hfalse
  contradiction

/-- For every $n \in \mathbb{N}$, $(\lfloor \log_2 K_0(n) \rfloor + 1)^4 \le 144 \cdot K_0(n)$. -/
theorem log_rootK0_add_one_fourth_le (n : ℕ) :
    let L := Nat.log 2 (rootK0 n) + 1
    (L * L) * (L * L) ≤ 144 * rootK0 n := by
  intro L
  have h1 := add_one_fourth_le_mul_two_pow (Nat.log 2 (rootK0 n))
  have hK0_pos : rootK0 n ≠ 0 := by have := rootK0_ge_two n; omega
  have h2 : 2 ^ Nat.log 2 (rootK0 n) ≤ rootK0 n := Nat.pow_log_le_self 2 hK0_pos
  exact le_trans h1 (Nat.mul_le_mul_left 144 h2)

/-- At any leaf level along the schedule of $n$, $K_\ell + 1 \le 19 \cdot (\lfloor \log_2 K_0(n) \rfloor + 1)$. -/
theorem leaf_levelK_add_one_le_of_leaf {n ell : ℕ}
    (hell : ell ≤ recursionDepth (rootK0 n) (rootP0 n))
    (hleaf : ¬ ((!isBaseLeaf (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)) = true ∧
      2 ≤ levelK (rootK0 n) ell)) :
    levelK (rootK0 n) ell + 1 ≤ 19 * (Nat.log 2 (rootK0 n) + 1) := by
  set K := levelK (rootK0 n) ell
  set L := Nat.log 2 (rootK0 n) + 1
  have h2K_le := leafTableEntries_level_le hell hleaf
  have hp0_K0 : rootP0 n ≤ 11 * rootK0 n := rootP0_le_eleven_mul_rootK0 n
  have hK0_lt : rootK0 n < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) (rootK0 n)
  have hK0_le : rootK0 n ≤ 2 ^ L := le_of_lt hK0_lt
  have h2K_lt : 2 ^ K < 2 ^ (3 * L + 16) := by
    have h1 : 5324 * rootP0 n * (rootK0 n * rootK0 n) ≤
        58564 * (rootK0 n * (rootK0 n * rootK0 n)) := by
      calc 5324 * rootP0 n * (rootK0 n * rootK0 n)
          ≤ 5324 * (11 * rootK0 n) * (rootK0 n * rootK0 n) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5324 hp0_K0)
        _ = 58564 * (rootK0 n * (rootK0 n * rootK0 n)) := by ring
    have h2 : rootK0 n * (rootK0 n * rootK0 n) ≤ 2 ^ L * (2 ^ L * 2 ^ L) :=
      Nat.mul_le_mul hK0_le (Nat.mul_le_mul hK0_le hK0_le)
    have hpow : 2 ^ (3 * L + 16) = 65536 * (2 ^ L * (2 ^ L * 2 ^ L)) := by
      have h3L : 3 * L + 16 = L + L + L + 16 := by omega
      rw [h3L, pow_add, pow_add, pow_add]
      ring
    have hpos : 0 < 2 ^ L * (2 ^ L * 2 ^ L) := by positivity
    linarith
  have hK_lt : K < 3 * L + 16 := by
    by_contra hge
    push_neg at hge
    exact not_lt_of_ge (Nat.pow_le_pow_right (by norm_num) hge) h2K_lt
  have hL_pos : 1 ≤ L := by omega
  omega

/-- At any internal level $\ell < \text{recursionDepth (rootK0 n) (rootP0 n)}$ and
$B_{\text{in}} \le \text{levelScheduleBIn (rootK0 n) (rootP0 n) } \ell$, the Kronecker packed
bit-length `kroneckerPackedBitLength W_tilde B_slot` is at most `2736 * (rootP0 n * rootP0 n)`. -/
theorem kroneckerPackedBitLength_level_le {n ell B_in : ℕ}
    (hlt : ell < recursionDepth (rootK0 n) (rootP0 n))
    (hB_in : B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) ell) :
    let K := levelK (rootK0 n) ell
    let p := levelP (rootK0 n) (rootP0 n) ell
    kroneckerPackedBitLength
      (foldedHalfWidth (computeM1Ell K p) (rEll K))
      (scheduleSlotBits K p B_in (computeM1Ell K p)) ≤
      2736 * (rootP0 n * rootP0 n) := by
  intro K p
  have hW1 : foldedHalfWidth (computeM1Ell K p) (rEll K) ≤ computeM1Ell K p :=
    foldedHalfWidth_le_left (computeM1Ell K p) (rEll K)
  have hm1 : computeM1Ell K p ≤ pChildEll K p := computeM1Ell_le_pChildEll K p
  have hq : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
  have hW : foldedHalfWidth (computeM1Ell K p) (rEll K) ≤ 12 * rootP0 n := by
    unfold qChildEll at hq
    omega
  have hB : scheduleSlotBits K p B_in (computeM1Ell K p) ≤ 76 * rootP0 n :=
    scheduleSlotBits_level_le hlt hB_in
  unfold kroneckerPackedBitLength
  calc 3 * foldedHalfWidth (computeM1Ell K p) (rEll K) *
        scheduleSlotBits K p B_in (computeM1Ell K p)
      = 3 * (foldedHalfWidth (computeM1Ell K p) (rEll K) *
          scheduleSlotBits K p B_in (computeM1Ell K p)) := by ring
    _ ≤ 3 * ((12 * rootP0 n) * (76 * rootP0 n)) :=
        Nat.mul_le_mul_left 3 (Nat.mul_le_mul hW hB)
    _ = 2736 * (rootP0 n * rootP0 n) := by ring

/-- Bounded-domain scaling of `scheduleTreeGenOps` along the schedule of $n$. -/
theorem scheduleTreeGenOps_scale_le_of_bounded {M1 M2 : ℕ → ℕ} {n C : ℕ} (hC : 1 ≤ C)
    (hM : ∀ q ≤ 2736 * (rootP0 n * rootP0 n), M1 q ≤ C * M2 q) :
    ∀ (d ell : ℕ),
      ell ≤ recursionDepth (rootK0 n) (rootP0 n) →
      recursionDepth (rootK0 n) (rootP0 n) - ell = d →
      scheduleTreeGenOps M1 (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) ≤
        C * scheduleTreeGenOps M2 (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) := by
  intro d
  induction d with
  | zero =>
    intro ell hell hd
    have hell_eq : ell = recursionDepth (rootK0 n) (rootP0 n) := by omega
    subst hell_eq
    have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    have hleaf_true :
        isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
          (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) = true :=
      isBaseLeaf_recursionDepth (rootK0 n) (rootP0 n) (by omega)
    have hnot :
        ¬ ((!isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) = true ∧
          2 ≤ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) := by
      simp [hleaf_true]
    conv_lhs => rw [scheduleTreeGenOps, if_neg hnot]
    conv_rhs => rw [scheduleTreeGenOps, if_neg hnot]
    set qBase := qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
      (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))
    have hqb1 : qBase ≤ 12 * rootP0 n := qBaseEll_level_le hell
    have hqb2 : qBase ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
    have hq : qBase + M1 qBase ≤ C * (qBase + M2 qBase) := by
      have h1 : qBase ≤ C * qBase := by
        calc qBase = 1 * qBase := (one_mul _).symm
          _ ≤ C * qBase := Nat.mul_le_mul_right _ hC
      have h2 := hM qBase hqb2
      linarith
    calc (2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) *
          scheduleSeriesTerms qBase * (qBase + M1 qBase)
        ≤ (2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) *
            scheduleSeriesTerms qBase * (C * (qBase + M2 qBase)) := Nat.mul_le_mul_left _ hq
      _ = C * ((2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) *
            scheduleSeriesTerms qBase * (qBase + M2 qBase)) := by ring
  | succ d ih =>
    intro ell hell hd
    have hlt : ell < recursionDepth (rootK0 n) (rootP0 n) := by omega
    have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    conv_lhs => rw [scheduleTreeGenOps]
    conv_rhs => rw [scheduleTreeGenOps]
    split_ifs with hcond
    · set K := levelK (rootK0 n) ell
      set p := levelP (rootK0 n) (rootP0 n) ell
      have hqc1 : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
      have hqc2 : qChildEll K p ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
      have hq : qChildEll K p + M1 (qChildEll K p) ≤ C * (qChildEll K p + M2 (qChildEll K p)) := by
        have h1 : qChildEll K p ≤ C * qChildEll K p := by
          calc qChildEll K p = 1 * qChildEll K p := (one_mul _).symm
            _ ≤ C * qChildEll K p := Nat.mul_le_mul_right _ hC
        have h2 := hM (qChildEll K p) hqc2
        linarith
      have hnode :
          scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + M1 (qChildEll K p)) ≤
          C * (scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
            (qChildEll K p + M2 (qChildEll K p))) := by
        calc scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
              (qChildEll K p + M1 (qChildEll K p))
            ≤ scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
                (C * (qChildEll K p + M2 (qChildEll K p))) := Nat.mul_le_mul_left _ hq
          _ = C * (scheduleNodeTableEntries K p * scheduleSeriesTerms (qChildEll K p) *
                (qChildEll K p + M2 (qChildEll K p))) := by ring
      have hrec :
          scheduleTreeGenOps M1 (k2Ell K) (pChildEll K p) ≤
            C * scheduleTreeGenOps M2 (k2Ell K) (pChildEll K p) :=
        ih (ell + 1) (Nat.succ_le_of_lt hlt) (by omega)
      linarith
    · set qBase := qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)
      have hqb1 : qBase ≤ 12 * rootP0 n := qBaseEll_level_le hell
      have hqb2 : qBase ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
      have hq : qBase + M1 qBase ≤ C * (qBase + M2 qBase) := by
        have h1 : qBase ≤ C * qBase := by
          calc qBase = 1 * qBase := (one_mul _).symm
            _ ≤ C * qBase := Nat.mul_le_mul_right _ hC
        have h2 := hM qBase hqb2
        linarith
      calc (2 ^ levelK (rootK0 n) ell) * scheduleSeriesTerms qBase * (qBase + M1 qBase)
          ≤ (2 ^ levelK (rootK0 n) ell) * scheduleSeriesTerms qBase *
              (C * (qBase + M2 qBase)) := Nat.mul_le_mul_left _ hq
        _ = C * ((2 ^ levelK (rootK0 n) ell) * scheduleSeriesTerms qBase *
              (qBase + M2 qBase)) := by ring

/-- Bounded-domain scaling of `fastDFTRecursiveSteps` along the schedule of $n$. -/
theorem fastDFTRecursiveSteps_scale_le_of_bounded {M1 M2 : ℕ → ℕ} {n C : ℕ} (hC : 1 ≤ C)
    (hM : ∀ q ≤ 2736 * (rootP0 n * rootP0 n), M1 q ≤ C * M2 q) :
    ∀ (d ell B_in : ℕ),
      ell ≤ recursionDepth (rootK0 n) (rootP0 n) →
      B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) ell →
      recursionDepth (rootK0 n) (rootP0 n) - ell = d →
      fastDFTRecursiveSteps M1 (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) B_in ≤
        C * fastDFTRecursiveSteps M2 (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) B_in := by
  intro d
  induction d with
  | zero =>
    intro ell B_in hell _hB_in hd
    have hell_eq : ell = recursionDepth (rootK0 n) (rootP0 n) := by omega
    subst hell_eq
    have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    have hleaf_true :
        isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
          (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) = true :=
      isBaseLeaf_recursionDepth (rootK0 n) (rootP0 n) (by omega)
    have hnot :
        ¬ ((!isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) = true ∧
          2 ≤ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) := by
      simp [hleaf_true]
    rw [fastDFTRecursiveSteps_of_leaf _ hnot, fastDFTRecursiveSteps_of_leaf _ hnot]
    unfold leafDFTOps
    set qBase := qBaseEll (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
      (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))
    have hqb1 : qBase ≤ 12 * rootP0 n := qBaseEll_level_le hell
    have hqb2 : qBase ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
    have hq : qBase + M1 qBase ≤ C * (qBase + M2 qBase) := by
      have h1 : qBase ≤ C * qBase := by
        calc qBase = 1 * qBase := (one_mul _).symm
          _ ≤ C * qBase := Nat.mul_le_mul_right _ hC
      have h2 := hM qBase hqb2
      linarith
    calc (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)) + 1) *
          (2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) * (qBase + M1 qBase)
        ≤ (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)) + 1) *
            (2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) *
            (C * (qBase + M2 qBase)) := Nat.mul_le_mul_left _ hq
      _ = C * ((levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)) + 1) *
            (2 ^ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) *
            (qBase + M2 qBase)) := by ring
  | succ d ih =>
    intro ell B_in hell hB_in hd
    have hlt : ell < recursionDepth (rootK0 n) (rootP0 n) := by omega
    have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    conv_lhs => rw [fastDFTRecursiveSteps]
    conv_rhs => rw [fastDFTRecursiveSteps]
    split_ifs with hcond
    · set K := levelK (rootK0 n) ell
      set p := levelP (rootK0 n) (rootP0 n) ell
      have hB_child :
          childScheduleBIn K p B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) (ell + 1) := by
        unfold levelScheduleBIn childScheduleBIn
        exact Nat.add_le_add_right hB_in _
      have hrec := ih (ell + 1) (childScheduleBIn K p B_in) (Nat.succ_le_of_lt hlt) hB_child (by omega)
      have hchild :
          t1Ell K * fastDFTRecursiveSteps M1 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) ≤
          C * (t1Ell K * fastDFTRecursiveSteps M2 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) := by
        calc t1Ell K * fastDFTRecursiveSteps M1 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
            ≤ t1Ell K * (C * fastDFTRecursiveSteps M2 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) :=
              Nat.mul_le_mul_left _ hrec
          _ = C * (t1Ell K * fastDFTRecursiveSteps M2 (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) := by
              ring
      have hmuls : stepFixedPointMuls K p B_in M1 ≤ C * stepFixedPointMuls K p B_in M2 := by
        unfold stepFixedPointMuls
        dsimp only
        set Q_kron := kroneckerPackedBitLength (foldedHalfWidth (computeM1Ell K p) (rEll K))
          (scheduleSlotBits K p B_in (computeM1Ell K p))
        have hQ_le : Q_kron ≤ 2736 * (rootP0 n * rootP0 n) :=
          kroneckerPackedBitLength_level_le hlt hB_in
        have hqc1 : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
        have hqc2 : qChildEll K p ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
        have h1 := hM Q_kron hQ_le
        have h2 := hM (qChildEll K p) hqc2
        have h3 : 2 * t1Ell K * numBlocks (rEll K) (foldedHalfWidth (computeM1Ell K p) (rEll K)) * M1 Q_kron ≤
            2 * t1Ell K * numBlocks (rEll K) (foldedHalfWidth (computeM1Ell K p) (rEll K)) * (C * M2 Q_kron) :=
          Nat.mul_le_mul_left _ h1
        have h4 : 16 * (2 ^ K) * M1 (qChildEll K p) ≤ 16 * (2 ^ K) * (C * M2 (qChildEll K p)) :=
          Nat.mul_le_mul_left _ h2
        linarith
      have hadd :
          step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p ≤
            C * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p) := by
        calc step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p
            = 1 * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p) := (one_mul _).symm
          _ ≤ C * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p + step3DeconvOps K p) :=
              Nat.mul_le_mul_right _ hC
      linarith
    · unfold leafDFTOps
      set qBase := qBaseEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)
      have hqb1 : qBase ≤ 12 * rootP0 n := qBaseEll_level_le hell
      have hqb2 : qBase ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
      have hq : qBase + M1 qBase ≤ C * (qBase + M2 qBase) := by
        have h1 : qBase ≤ C * qBase := by
          calc qBase = 1 * qBase := (one_mul _).symm
            _ ≤ C * qBase := Nat.mul_le_mul_right _ hC
        have h2 := hM qBase hqb2
        linarith
      calc (levelK (rootK0 n) ell + 1) * (2 ^ levelK (rootK0 n) ell) * (qBase + M1 qBase)
          ≤ (levelK (rootK0 n) ell + 1) * (2 ^ levelK (rootK0 n) ell) *
              (C * (qBase + M2 qBase)) := Nat.mul_le_mul_left _ hq
        _ = C * ((levelK (rootK0 n) ell + 1) * (2 ^ levelK (rootK0 n) ell) *
              (qBase + M2 qBase)) := by ring

/-- Bounded-domain scaling of `intMulAlgorithmSteps`. -/
theorem intMulAlgorithmSteps_scale_le_of_bounded {M1 M2 : ℕ → ℕ} {n C : ℕ} (hC : 1 ≤ C)
    (hM : ∀ q ≤ 2736 * (rootP0 n * rootP0 n), M1 q ≤ C * M2 q) :
    intMulAlgorithmSteps M1 n ≤ C * intMulAlgorithmSteps M2 n := by
  unfold intMulAlgorithmSteps
  have htree := scheduleTreeGenOps_scale_le_of_bounded hC hM
    (recursionDepth (rootK0 n) (rootP0 n)) 0 (Nat.zero_le _) (Nat.sub_zero _)
  change scheduleTreeGenOps M1 (rootK0 n) (rootP0 n) ≤
    C * scheduleTreeGenOps M2 (rootK0 n) (rootP0 n) at htree
  have hfast := fastDFTRecursiveSteps_scale_le_of_bounded hC hM
    (recursionDepth (rootK0 n) (rootP0 n)) 0 (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
    (Nat.zero_le _) (le_refl _) (Nat.sub_zero _)
  change fastDFTRecursiveSteps M1 (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0) ≤
    C * fastDFTRecursiveSteps M2 (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0) at hfast
  have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
  have hp2_le : rootP0 n + 2 ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
  have hsq : 3 * rootR0 n * M1 (rootP0 n + 2) ≤ C * (3 * rootR0 n * M2 (rootP0 n + 2)) := by
    calc 3 * rootR0 n * M1 (rootP0 n + 2)
        ≤ 3 * rootR0 n * (C * M2 (rootP0 n + 2)) := Nat.mul_le_mul_left _ (hM (rootP0 n + 2) hp2_le)
      _ = C * (3 * rootR0 n * M2 (rootP0 n + 2)) := by ring
  have hlin :
      scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n ≤
        C * (scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n) := by
    calc scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n
        = 1 * (scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n) := (one_mul _).symm
      _ ≤ C * (scheduleBitsLen n + fullScheduleTableBitsLen n + 2 * n + 4 * n) :=
          Nat.mul_le_mul_right _ hC
  linarith

/-- **Quadratic Base-Case Sub-Multiplication Bit-Operation Cost (`schoolbookSubMulBitOps`)**:
Charges each $q$-bit integer multiplication at depth `d = 0` (`computableNatMulAux 0 = binaryShiftAddMul`)
at the quadratic bit-operation cost $q^2$. -/
def schoolbookSubMulBitOps (q : ℕ) : ℕ :=
  q * q

/-- **Grounded Nested Recursive Sub-Multiplication Cost (`nestedSubMulBitOps`)**:
Charges each $q$-bit integer sub-multiplication inside `computableNatMul = computableNatMulAux 2`
at the full recursive fast-DFT multiplication step count `intMulAlgorithmSteps schoolbookSubMulBitOps q`
grounded at the quadratic `d = 0` schoolbook cost `schoolbookSubMulBitOps q0 = q0 * q0`. -/
def nestedSubMulBitOps (q : ℕ) : ℕ :=
  if q = 0 then 0 else intMulAlgorithmSteps schoolbookSubMulBitOps q

/-- Constant `C_nested_d1 = 1324224 * 277159328108409262726` bounding `nestedSubMulBitOps q` by
`C_nested_d1 * q * (Nat.log 2 q + 1) ^ 3`. -/
def C_nested_d1 : ℕ :=
  1324224 * 277159328108409262726

theorem nestedSubMulBitOps_le_log_cube (q : ℕ) :
    nestedSubMulBitOps q ≤
      C_nested_d1 * q * ((Nat.log 2 q + 1) * (Nat.log 2 q + 1) * (Nat.log 2 q + 1)) := by
  unfold nestedSubMulBitOps C_nested_d1
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · rw [if_neg (ne_of_gt hq)]
    have hp0 : 18 ≤ rootP0 q := rootP0_ge_eighteen q
    have hC : 1 ≤ 2736 * (rootP0 q * rootP0 q) := by nlinarith
    have hscale :
        intMulAlgorithmSteps schoolbookSubMulBitOps q ≤
          (2736 * (rootP0 q * rootP0 q)) * intMulAlgorithmSteps (fun q0 => q0) q :=
      intMulAlgorithmSteps_scale_le_of_bounded hC
        (fun q0 hq0 => by unfold schoolbookSubMulBitOps; exact Nat.mul_le_mul_right q0 hq0)
    have hlin := intMulAlgorithmSteps_le_n_log_n_succ hq
    have hp0_log : rootP0 q ≤ 22 * (Nat.log 2 q + 1) := by
      have h1 := rootP0_le_eleven_mul_rootK0 q
      have h2 := rootK0_le_log_add_two q
      omega
    have h2736 :
        2736 * (rootP0 q * rootP0 q) ≤
          1324224 * ((Nat.log 2 q + 1) * (Nat.log 2 q + 1)) := by
      calc 2736 * (rootP0 q * rootP0 q)
          ≤ 2736 * ((22 * (Nat.log 2 q + 1)) * (22 * (Nat.log 2 q + 1))) :=
            Nat.mul_le_mul_left 2736 (Nat.mul_le_mul hp0_log hp0_log)
        _ = 1324224 * ((Nat.log 2 q + 1) * (Nat.log 2 q + 1)) := by ring
    calc intMulAlgorithmSteps schoolbookSubMulBitOps q
        ≤ (2736 * (rootP0 q * rootP0 q)) * intMulAlgorithmSteps (fun q0 => q0) q := hscale
      _ ≤ (1324224 * ((Nat.log 2 q + 1) * (Nat.log 2 q + 1))) *
            (277159328108409262726 * q * (Nat.log 2 q + 1)) :=
          Nat.mul_le_mul h2736 hlin
      _ = 1324224 * 277159328108409262726 * q *
            ((Nat.log 2 q + 1) * (Nat.log 2 q + 1) * (Nat.log 2 q + 1)) := by ring

/-- Multi-scale sub-multiplication cost envelope covering the fixed-width multiples
`(w, 2*w, 6*w, 10*w, 100*w, 1000*w)` used across the bottom-up `CostM` primitives. -/
def scaledSubMulCost (M_mul : ℕ → ℕ) (w : ℕ) : ℕ :=
  M_mul w + M_mul (2 * w) + M_mul (6 * w) + M_mul (10 * w) + M_mul (100 * w) + M_mul (1000 * w)

theorem le_scaledSubMulCost_one (M_mul : ℕ → ℕ) (w : ℕ) :
    M_mul w ≤ scaledSubMulCost M_mul w := by
  unfold scaledSubMulCost; omega

theorem le_scaledSubMulCost_two (M_mul : ℕ → ℕ) (w : ℕ) :
    M_mul (2 * w) ≤ scaledSubMulCost M_mul w := by
  unfold scaledSubMulCost; omega

theorem le_scaledSubMulCost_six (M_mul : ℕ → ℕ) (w : ℕ) :
    M_mul (6 * w) ≤ scaledSubMulCost M_mul w := by
  unfold scaledSubMulCost; omega

theorem le_scaledSubMulCost_ten (M_mul : ℕ → ℕ) (w : ℕ) :
    M_mul (10 * w) ≤ scaledSubMulCost M_mul w := by
  unfold scaledSubMulCost; omega

theorem le_scaledSubMulCost_hundred (M_mul : ℕ → ℕ) (w : ℕ) :
    M_mul (100 * w) ≤ scaledSubMulCost M_mul w := by
  unfold scaledSubMulCost; omega

theorem le_scaledSubMulCost_thousand (M_mul : ℕ → ℕ) (w : ℕ) :
    M_mul (1000 * w) ≤ scaledSubMulCost M_mul w := by
  unfold scaledSubMulCost; omega

theorem scaledSubMulCost_const_mul (c : ℕ) (M_mul : ℕ → ℕ) (w : ℕ) :
    scaledSubMulCost (fun w' => c * M_mul w') w = c * scaledSubMulCost M_mul w := by
  unfold scaledSubMulCost; ring

theorem scaledSubMulCost_schoolbook (c w : ℕ) :
    scaledSubMulCost (fun w' => c * schoolbookSubMulBitOps w') w =
      (1010141 * c) * schoolbookSubMulBitOps w := by
  unfold scaledSubMulCost schoolbookSubMulBitOps; ring

/-- Constant `C_nested_base = 1119 * 32768 * C_nested_d1` bounding `nestedSubMulBitOps q` and
`scaledSubMulCost nestedSubMulBitOps q` along the schedule of $n$. -/
def C_nested_base : ℕ :=
  1119 * 32768 * C_nested_d1

theorem C_nested_base_pos : 1 ≤ C_nested_base := by
  unfold C_nested_base C_nested_d1
  norm_num

theorem nestedSubMulBitOps_le_of_bounded_1000 {n q : ℕ}
    (hq : q ≤ 2736000 * (rootP0 n * rootP0 n)) :
    let L := Nat.log 2 (rootK0 n) + 1
    nestedSubMulBitOps q ≤ (32768 * C_nested_d1 * (L * L * L)) * q := by
  intro L
  rcases Nat.eq_zero_or_pos q with rfl | hq_pos
  · simp [nestedSubMulBitOps]
  · have hp0_K0 : rootP0 n ≤ 11 * rootK0 n := rootP0_le_eleven_mul_rootK0 n
    have hK0_lt : rootK0 n < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) (rootK0 n)
    have hK0_le : rootK0 n ≤ 2 ^ L := le_of_lt hK0_lt
    have hq_lt_pow : q < 2 ^ (2 * L + 30) := by
      have h1 : 2736000 * (rootP0 n * rootP0 n) ≤ 331056000 * (rootK0 n * rootK0 n) := by
        calc 2736000 * (rootP0 n * rootP0 n)
            ≤ 2736000 * ((11 * rootK0 n) * (11 * rootK0 n)) :=
              Nat.mul_le_mul_left 2736000 (Nat.mul_le_mul hp0_K0 hp0_K0)
          _ = 331056000 * (rootK0 n * rootK0 n) := by ring
      have h2 : rootK0 n * rootK0 n ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hK0_le hK0_le
      have hpow : 2 ^ (2 * L + 30) = 1073741824 * (2 ^ L * 2 ^ L) := by
        have h2L : 2 * L + 30 = L + L + 30 := by omega
        rw [h2L, pow_add, pow_add]
        ring
      have hpos : 0 < 2 ^ L * 2 ^ L := by positivity
      linarith
    have hlog_lt : Nat.log 2 q < 2 * L + 30 :=
      Nat.log_lt_of_lt_pow (by omega) hq_lt_pow
    have hL_pos : 1 ≤ L := by omega
    have hlog_le : Nat.log 2 q + 1 ≤ 32 * L := by omega
    have hcube :
        (Nat.log 2 q + 1) * (Nat.log 2 q + 1) * (Nat.log 2 q + 1) ≤
          32768 * (L * L * L) := by
      calc (Nat.log 2 q + 1) * (Nat.log 2 q + 1) * (Nat.log 2 q + 1)
          ≤ (32 * L) * (32 * L) * (32 * L) :=
            Nat.mul_le_mul (Nat.mul_le_mul hlog_le hlog_le) hlog_le
        _ = 32768 * (L * L * L) := by ring
    have h1 := nestedSubMulBitOps_le_log_cube q
    calc nestedSubMulBitOps q
        ≤ C_nested_d1 * q * ((Nat.log 2 q + 1) * (Nat.log 2 q + 1) * (Nat.log 2 q + 1)) := h1
      _ ≤ C_nested_d1 * q * (32768 * (L * L * L)) := Nat.mul_le_mul_left _ hcube
      _ = (32768 * C_nested_d1 * (L * L * L)) * q := by ring

/-- Along the schedule of $n$, for every sub-multiplication width $q \le 2736 \cdot p_0(n)^2$,
`scaledSubMulCost nestedSubMulBitOps q ≤ (C_nested_base * (Nat.log 2 (rootK0 n) + 1) ^ 3) * q`. -/
theorem scaledSubMulCost_nestedSubMulBitOps_le_of_bounded {n q : ℕ}
    (hq : q ≤ 2736 * (rootP0 n * rootP0 n)) :
    let L := Nat.log 2 (rootK0 n) + 1
    scaledSubMulCost nestedSubMulBitOps q ≤ (C_nested_base * (L * L * L)) * q := by
  intro L
  unfold scaledSubMulCost C_nested_base
  have h1 := nestedSubMulBitOps_le_of_bounded_1000 (n := n) (q := q) (by omega)
  have h2 := nestedSubMulBitOps_le_of_bounded_1000 (n := n) (q := 2 * q) (by omega)
  have h6 := nestedSubMulBitOps_le_of_bounded_1000 (n := n) (q := 6 * q) (by omega)
  have h10 := nestedSubMulBitOps_le_of_bounded_1000 (n := n) (q := 10 * q) (by omega)
  have h100 := nestedSubMulBitOps_le_of_bounded_1000 (n := n) (q := 100 * q) (by omega)
  have h1000 := nestedSubMulBitOps_le_of_bounded_1000 (n := n) (q := 1000 * q) (by omega)
  dsimp only [L] at *
  calc nestedSubMulBitOps q + nestedSubMulBitOps (2 * q) + nestedSubMulBitOps (6 * q) +
        nestedSubMulBitOps (10 * q) + nestedSubMulBitOps (100 * q) + nestedSubMulBitOps (1000 * q)
      ≤ _ + _ + _ + _ + _ + _ :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h6) h10) h100) h1000
    _ = 1119 * 32768 * C_nested_d1 *
          ((Nat.log 2 (rootK0 n) + 1) * (Nat.log 2 (rootK0 n) + 1) * (Nat.log 2 (rootK0 n) + 1)) * q := by
        ring

/-- Along the schedule of $n$, for every sub-multiplication width $q \le 2736 \cdot p_0(n)^2$,
`nestedSubMulBitOps q ≤ (C_nested_base * (Nat.log 2 (rootK0 n) + 1) ^ 3) * q`. -/
theorem nestedSubMulBitOps_le_of_bounded {n q : ℕ}
    (hq : q ≤ 2736 * (rootP0 n * rootP0 n)) :
    let L := Nat.log 2 (rootK0 n) + 1
    nestedSubMulBitOps q ≤ (C_nested_base * (L * L * L)) * q :=
  le_trans (le_scaledSubMulCost_one nestedSubMulBitOps q)
    (scaledSubMulCost_nestedSubMulBitOps_le_of_bounded hq)

/-- Multi-level bound on `fastDFTRecursiveSteps M` for any sub-multiplication cost $M$ bounded by
$C_{\text{mul}} \cdot q$ along the schedule of $n$. -/
theorem fastDFTRecursiveSteps_bounded_level_le {M : ℕ → ℕ} {n C_mul : ℕ} (hC : 1 ≤ C_mul)
    (hM : ∀ q ≤ 2736 * (rootP0 n * rootP0 n), M q ≤ C_mul * q) :
    ∀ (d ell B_in : ℕ),
      ell ≤ recursionDepth (rootK0 n) (rootP0 n) →
      B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) ell →
      recursionDepth (rootK0 n) (rootP0 n) - ell = d →
      fastDFTRecursiveSteps M
        (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) B_in ≤
        1044 * rootP0 n * (2 ^ levelK (rootK0 n) ell) * levelK (rootK0 n) ell +
          1104 * C_mul * rootP0 n * (2 ^ levelK (rootK0 n) ell) *
            (d + (Nat.log 2 (rootK0 n) + 1)) := by
  intro d
  induction d with
  | zero =>
    intro ell B_in hell _hB_in hd
    have hell_eq : ell = recursionDepth (rootK0 n) (rootP0 n) := by omega
    subst hell_eq
    have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    have hleaf_true :
        isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
          (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))) = true :=
      isBaseLeaf_recursionDepth (rootK0 n) (rootP0 n) (by omega)
    have hnot :
        ¬ ((!isBaseLeaf (levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n)))
            (levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n)))) = true ∧
          2 ≤ levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))) := by
      simp [hleaf_true]
    rw [fastDFTRecursiveSteps_of_leaf _ hnot]
    unfold leafDFTOps
    set K := levelK (rootK0 n) (recursionDepth (rootK0 n) (rootP0 n))
    set p := levelP (rootK0 n) (rootP0 n) (recursionDepth (rootK0 n) (rootP0 n))
    set qBase := qBaseEll K p
    have hK_leaf : K + 1 ≤ 19 * (Nat.log 2 (rootK0 n) + 1) :=
      leaf_levelK_add_one_le_of_leaf hell hnot
    have hqb1 : qBase ≤ 12 * rootP0 n := qBaseEll_level_le hell
    have hqb2 : qBase ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
    have hMq : qBase + M qBase ≤ 24 * C_mul * rootP0 n := by
      have h1 := hM qBase hqb2
      have h2 : qBase ≤ C_mul * qBase := by
        calc qBase = 1 * qBase := (one_mul _).symm
          _ ≤ C_mul * qBase := Nat.mul_le_mul_right _ hC
      have h3 : qBase + M qBase ≤ 2 * C_mul * qBase := by linarith
      calc qBase + M qBase ≤ 2 * C_mul * qBase := h3
        _ ≤ 2 * C_mul * (12 * rootP0 n) := Nat.mul_le_mul_left _ hqb1
        _ = 24 * C_mul * rootP0 n := by ring
    have hleaf_prod :
        (K + 1) * (2 ^ K) * (qBase + M qBase) ≤
          456 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1) := by
      calc (K + 1) * (2 ^ K) * (qBase + M qBase)
          ≤ (19 * (Nat.log 2 (rootK0 n) + 1)) * (2 ^ K) * (24 * C_mul * rootP0 n) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) hK_leaf) hMq
        _ = 456 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1) := by ring
    have h456 :
        456 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1) ≤
          1104 * C_mul * rootP0 n * (2 ^ K) * (0 + (Nat.log 2 (rootK0 n) + 1)) := by
      rw [zero_add]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (by norm_num))))
    exact le_trans (le_trans hleaf_prod h456) (Nat.le_add_left _ _)
  | succ d ih =>
    intro ell B_in hell hB_in hd
    have hlt : ell < recursionDepth (rootK0 n) (rootP0 n) := by omega
    have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    rw [fastDFTRecursiveSteps]
    split_ifs with hcond
    · set K := levelK (rootK0 n) ell
      set p := levelP (rootK0 n) (rootP0 n) ell
      have hK2 : 2 ≤ K := hcond.2
      have hk1_pos : 1 ≤ k1Ell K := by unfold k1Ell; omega
      have hq : qChildEll K p ≤ 12 * rootP0 n := qChildEll_level_le hlt
      have hstep1 : step1SpreadOps K p B_in ≤ 912 * rootP0 n * (2 ^ K) :=
        step1SpreadOps_level_le hlt hB_in
      have hstep1_k1 : step1SpreadOps K p B_in ≤ 912 * rootP0 n * (2 ^ K) * k1Ell K := by
        calc step1SpreadOps K p B_in
            ≤ (912 * rootP0 n * (2 ^ K)) * 1 := by linarith
          _ ≤ (912 * rootP0 n * (2 ^ K)) * k1Ell K := Nat.mul_le_mul_left _ hk1_pos
      have hstep23 :
          step2SyntheticFFTOps K p + step3DeconvOps K p ≤
            132 * rootP0 n * (2 ^ K) * k1Ell K := by
        unfold step2SyntheticFFTOps step3DeconvOps
        have h11 : 10 + k1Ell K ≤ 11 * k1Ell K := by omega
        calc (2 + k1Ell K) * (2 ^ K) * qChildEll K p + 8 * (2 ^ K) * qChildEll K p
            = (10 + k1Ell K) * (2 ^ K) * qChildEll K p := by ring
          _ ≤ (11 * k1Ell K) * (2 ^ K) * (12 * rootP0 n) :=
              Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) h11) hq
          _ = 132 * rootP0 n * (2 ^ K) * k1Ell K := by ring
      have hmuls :
          stepFixedPointMuls K p B_in M ≤ 1104 * C_mul * rootP0 n * (2 ^ K) := by
        have hscale_muls :
            stepFixedPointMuls K p B_in M ≤ C_mul * stepFixedPointMuls K p B_in (fun q => q) := by
          unfold stepFixedPointMuls
          dsimp only
          set Q_kron := kroneckerPackedBitLength (foldedHalfWidth (computeM1Ell K p) (rEll K))
            (scheduleSlotBits K p B_in (computeM1Ell K p))
          have hQ_le : Q_kron ≤ 2736 * (rootP0 n * rootP0 n) :=
            kroneckerPackedBitLength_level_le hlt hB_in
          have hqc2 : qChildEll K p ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
          have h1 := hM Q_kron hQ_le
          have h2 := hM (qChildEll K p) hqc2
          have h3 : 2 * t1Ell K * numBlocks (rEll K) (foldedHalfWidth (computeM1Ell K p) (rEll K)) * M Q_kron ≤
              2 * t1Ell K * numBlocks (rEll K) (foldedHalfWidth (computeM1Ell K p) (rEll K)) * (C_mul * Q_kron) :=
            Nat.mul_le_mul_left _ h1
          have h4 : 16 * (2 ^ K) * M (qChildEll K p) ≤ 16 * (2 ^ K) * (C_mul * qChildEll K p) :=
            Nat.mul_le_mul_left _ h2
          linarith
        have hlin_muls : stepFixedPointMuls K p B_in (fun q => q) ≤ 1104 * rootP0 n * (2 ^ K) := by
          have hdef : stepFixedPointMuls K p B_in (fun q => q) =
              step1SpreadOps K p B_in + 16 * (2 ^ K) * qChildEll K p := rfl
          rw [hdef]
          have h16 : 16 * (2 ^ K) * qChildEll K p ≤ 192 * rootP0 n * (2 ^ K) := by
            calc 16 * (2 ^ K) * qChildEll K p
                ≤ 16 * (2 ^ K) * (12 * rootP0 n) := Nat.mul_le_mul_left _ hq
              _ = 192 * rootP0 n * (2 ^ K) := by ring
          linarith
        calc stepFixedPointMuls K p B_in M
            ≤ C_mul * stepFixedPointMuls K p B_in (fun q => q) := hscale_muls
          _ ≤ C_mul * (1104 * rootP0 n * (2 ^ K)) := Nat.mul_le_mul_left C_mul hlin_muls
          _ = 1104 * C_mul * rootP0 n * (2 ^ K) := by ring
      have hB_child :
          childScheduleBIn K p B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) (ell + 1) := by
        unfold levelScheduleBIn childScheduleBIn
        exact Nat.add_le_add_right hB_in _
      have hrec := ih (ell + 1) (childScheduleBIn K p B_in) (Nat.succ_le_of_lt hlt) hB_child (by omega)
      have hchild :
          t1Ell K * fastDFTRecursiveSteps M (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) ≤
            1044 * rootP0 n * (2 ^ K) * k2Ell K +
              1104 * C_mul * rootP0 n * (2 ^ K) * (d + (Nat.log 2 (rootK0 n) + 1)) := by
        have ht1r : t1Ell K * (2 ^ k2Ell K) = 2 ^ K := t1Ell_mul_rEll K
        calc t1Ell K * fastDFTRecursiveSteps M (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
            ≤ t1Ell K * (1044 * rootP0 n * (2 ^ k2Ell K) * k2Ell K +
                1104 * C_mul * rootP0 n * (2 ^ k2Ell K) * (d + (Nat.log 2 (rootK0 n) + 1))) :=
              Nat.mul_le_mul_left (t1Ell K) hrec
          _ = 1044 * rootP0 n * (t1Ell K * (2 ^ k2Ell K)) * k2Ell K +
                1104 * C_mul * rootP0 n * (t1Ell K * (2 ^ k2Ell K)) * (d + (Nat.log 2 (rootK0 n) + 1)) := by ring
          _ = 1044 * rootP0 n * (2 ^ K) * k2Ell K +
                1104 * C_mul * rootP0 n * (2 ^ K) * (d + (Nat.log 2 (rootK0 n) + 1)) := by rw [ht1r]
      have hk_add : k1Ell K + k2Ell K = K := k1Ell_add_k2Ell K
      calc step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
            stepFixedPointMuls K p B_in M +
            t1Ell K * fastDFTRecursiveSteps M (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) +
            step3DeconvOps K p
          = (step1SpreadOps K p B_in + (step2SyntheticFFTOps K p + step3DeconvOps K p)) +
              stepFixedPointMuls K p B_in M +
              t1Ell K * fastDFTRecursiveSteps M (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) := by ring
        _ ≤ (912 * rootP0 n * (2 ^ K) * k1Ell K + 132 * rootP0 n * (2 ^ K) * k1Ell K) +
              1104 * C_mul * rootP0 n * (2 ^ K) +
              (1044 * rootP0 n * (2 ^ K) * k2Ell K +
                1104 * C_mul * rootP0 n * (2 ^ K) * (d + (Nat.log 2 (rootK0 n) + 1))) :=
            Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hstep1_k1 hstep23) hmuls) hchild
        _ = 1044 * rootP0 n * (2 ^ K) * (k1Ell K + k2Ell K) +
              1104 * C_mul * rootP0 n * (2 ^ K) * (d + 1 + (Nat.log 2 (rootK0 n) + 1)) := by ring
        _ = 1044 * rootP0 n * (2 ^ K) * K +
              1104 * C_mul * rootP0 n * (2 ^ K) * (d + 1 + (Nat.log 2 (rootK0 n) + 1)) := by rw [hk_add]
    · unfold leafDFTOps
      set K := levelK (rootK0 n) ell
      set p := levelP (rootK0 n) (rootP0 n) ell
      set qBase := qBaseEll K p
      have hK_leaf : K + 1 ≤ 19 * (Nat.log 2 (rootK0 n) + 1) :=
        leaf_levelK_add_one_le_of_leaf hell hcond
      have hqb1 : qBase ≤ 12 * rootP0 n := qBaseEll_level_le hell
      have hqb2 : qBase ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
      have hMq : qBase + M qBase ≤ 24 * C_mul * rootP0 n := by
        have h1 := hM qBase hqb2
        have h2 : qBase ≤ C_mul * qBase := by
          calc qBase = 1 * qBase := (one_mul _).symm
            _ ≤ C_mul * qBase := Nat.mul_le_mul_right _ hC
        have h3 : qBase + M qBase ≤ 2 * C_mul * qBase := by linarith
        calc qBase + M qBase ≤ 2 * C_mul * qBase := h3
          _ ≤ 2 * C_mul * (12 * rootP0 n) := Nat.mul_le_mul_left _ hqb1
          _ = 24 * C_mul * rootP0 n := by ring
      have hleaf_prod :
          (K + 1) * (2 ^ K) * (qBase + M qBase) ≤
            456 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1) := by
        calc (K + 1) * (2 ^ K) * (qBase + M qBase)
            ≤ (19 * (Nat.log 2 (rootK0 n) + 1)) * (2 ^ K) * (24 * C_mul * rootP0 n) :=
              Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) hK_leaf) hMq
          _ = 456 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1) := by ring
      have h456 :
          456 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1) ≤
            1104 * C_mul * rootP0 n * (2 ^ K) * (d + 1 + (Nat.log 2 (rootK0 n) + 1)) := by
        calc 456 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1)
            ≤ 1104 * C_mul * rootP0 n * (2 ^ K) * (Nat.log 2 (rootK0 n) + 1) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
                (Nat.mul_le_mul_right _ (by norm_num))))
          _ ≤ 1104 * C_mul * rootP0 n * (2 ^ K) * (d + 1 + (Nat.log 2 (rootK0 n) + 1)) :=
              Nat.mul_le_mul_left _ (by omega)
      exact le_trans (le_trans hleaf_prod h456) (Nat.le_add_left _ _)

/-- Root bound on `scheduleTreeGenOps M` for any `M` bounded by `(C_nested_base * L^3) * q`. -/
theorem scheduleTreeGenOps_bounded_nested_root_le {M : ℕ → ℕ} (n : ℕ)
    (hM : ∀ q ≤ 2736 * (rootP0 n * rootP0 n),
      M q ≤ (C_nested_base * ((Nat.log 2 (rootK0 n) + 1) * (Nat.log 2 (rootK0 n) + 1) *
        (Nat.log 2 (rootK0 n) + 1))) * q) :
    scheduleTreeGenOps M (rootK0 n) (rootP0 n) ≤
      (118782569189317017600 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n := by
  set L := Nat.log 2 (rootK0 n) + 1
  have hL_pos : 1 ≤ L := by omega
  have hC_pos : 1 ≤ C_nested_base * (L * L * L) :=
    le_trans C_nested_base_pos (Nat.le_mul_of_pos_right _ (by positivity))
  have hscale := scheduleTreeGenOps_scale_le_of_bounded hC_pos hM
    (recursionDepth (rootK0 n) (rootP0 n)) 0 (Nat.zero_le _) (Nat.sub_zero _)
  change scheduleTreeGenOps M (rootK0 n) (rootP0 n) ≤
    (C_nested_base * (L * L * L)) * scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n) at hscale
  have hlin_le_sub :
      scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n) ≤
        scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) := by
    have hmono : scheduleTreeGenOps (fun q => q) (rootK0 n) (rootP0 n) ≤
        1 * scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) :=
      scheduleTreeGenOps_scale_le (le_refl 1)
        (fun q => by rw [one_mul]; exact le_subMulBitOps q) (rootK0 n) (rootP0 n)
    rw [one_mul] at hmono
    exact hmono
  have hsub_level := scheduleTreeGenOps_subMulBitOps_level_le n
    (recursionDepth (rootK0 n) (rootP0 n)) 0 (Nat.zero_le _) (Nat.sub_zero _)
  change scheduleTreeGenOps subMulBitOps (rootK0 n) (rootP0 n) ≤
    412439476351795200 * rootR0 n * rootP0 n * (recursionDepth (rootK0 n) (rootP0 n) + 1) at hsub_level
  have hp0 : 1 ≤ rootP0 n := by have := rootP0_ge_eighteen n; omega
  have hrec_L : recursionDepth (rootK0 n) (rootP0 n) + 1 ≤ 2 * L := by
    have := recursionDepth_le_log_add_one (rootK0 n) (rootP0 n) hp0
    omega
  have hfourth : (L * L) * (L * L) ≤ 144 * rootK0 n := log_rootK0_add_one_fourth_le n
  calc scheduleTreeGenOps M (rootK0 n) (rootP0 n)
      ≤ (C_nested_base * (L * L * L)) *
          (412439476351795200 * rootR0 n * rootP0 n * (recursionDepth (rootK0 n) (rootP0 n) + 1)) :=
        le_trans hscale (Nat.mul_le_mul_left _ (le_trans hlin_le_sub hsub_level))
    _ ≤ (C_nested_base * (L * L * L)) * (412439476351795200 * rootR0 n * rootP0 n * (2 * L)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrec_L)
    _ = 824878952703590400 * C_nested_base * rootR0 n * rootP0 n * ((L * L) * (L * L)) := by ring
    _ ≤ 824878952703590400 * C_nested_base * rootR0 n * rootP0 n * (144 * rootK0 n) :=
        Nat.mul_le_mul_left _ hfourth
    _ = (118782569189317017600 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n := by ring

/-- Root bound on `scheduleTreeGenOps nestedSubMulBitOps`. -/
theorem scheduleTreeGenOps_nestedSubMulBitOps_root_le (n : ℕ) :
    scheduleTreeGenOps nestedSubMulBitOps (rootK0 n) (rootP0 n) ≤
      (118782569189317017600 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n :=
  scheduleTreeGenOps_bounded_nested_root_le n (fun _ hq => nestedSubMulBitOps_le_of_bounded hq)

/-- Root bound on `fastDFTRecursiveSteps M` for any `M` bounded by `(C_nested_base * L^3) * q`. -/
theorem fastDFTRecursiveSteps_bounded_nested_root_le {M : ℕ → ℕ} (n B_in : ℕ)
    (hB_in : B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) 0)
    (hM : ∀ q ≤ 2736 * (rootP0 n * rootP0 n),
      M q ≤ (C_nested_base * ((Nat.log 2 (rootK0 n) + 1) * (Nat.log 2 (rootK0 n) + 1) *
        (Nat.log 2 (rootK0 n) + 1))) * q) :
    fastDFTRecursiveSteps M (rootK0 n) (rootP0 n) B_in ≤
      (1044 + 317952 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n := by
  set L := Nat.log 2 (rootK0 n) + 1
  have hL_pos : 1 ≤ L := by omega
  have hC_pos : 1 ≤ C_nested_base * (L * L * L) :=
    le_trans C_nested_base_pos (Nat.le_mul_of_pos_right _ (by positivity))
  have h0 := fastDFTRecursiveSteps_bounded_level_le hC_pos hM
    (recursionDepth (rootK0 n) (rootP0 n)) 0 B_in (Nat.zero_le _) hB_in (Nat.sub_zero _)
  change fastDFTRecursiveSteps M (rootK0 n) (rootP0 n) B_in ≤
    1044 * rootP0 n * rootR0 n * rootK0 n +
      1104 * (C_nested_base * (L * L * L)) * rootP0 n * rootR0 n *
        (recursionDepth (rootK0 n) (rootP0 n) + L) at h0
  have hp0 : 1 ≤ rootP0 n := by have := rootP0_ge_eighteen n; omega
  have hrec_L : recursionDepth (rootK0 n) (rootP0 n) + L ≤ 2 * L := by
    have := recursionDepth_le_log_add_one (rootK0 n) (rootP0 n) hp0
    omega
  have hfourth : (L * L) * (L * L) ≤ 144 * rootK0 n := log_rootK0_add_one_fourth_le n
  have hpart2 :
      1104 * (C_nested_base * (L * L * L)) * rootP0 n * rootR0 n *
          (recursionDepth (rootK0 n) (rootP0 n) + L) ≤
        (317952 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n := by
    calc 1104 * (C_nested_base * (L * L * L)) * rootP0 n * rootR0 n *
            (recursionDepth (rootK0 n) (rootP0 n) + L)
        ≤ 1104 * (C_nested_base * (L * L * L)) * rootP0 n * rootR0 n * (2 * L) :=
          Nat.mul_le_mul_left _ hrec_L
      _ = 2208 * C_nested_base * rootR0 n * rootP0 n * ((L * L) * (L * L)) := by ring
      _ ≤ 2208 * C_nested_base * rootR0 n * rootP0 n * (144 * rootK0 n) :=
          Nat.mul_le_mul_left _ hfourth
      _ = (317952 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n := by ring
  calc fastDFTRecursiveSteps M (rootK0 n) (rootP0 n) B_in
      ≤ 1044 * rootP0 n * rootR0 n * rootK0 n +
          (317952 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n :=
        le_trans h0 (Nat.add_le_add_left hpart2 _)
    _ = (1044 + 317952 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n := by ring

/-- Root bound on `fastDFTRecursiveSteps nestedSubMulBitOps`. -/
theorem fastDFTRecursiveSteps_nestedSubMulBitOps_root_le (n B_in : ℕ)
    (hB_in : B_in ≤ levelScheduleBIn (rootK0 n) (rootP0 n) 0) :
    fastDFTRecursiveSteps nestedSubMulBitOps (rootK0 n) (rootP0 n) B_in ≤
      (1044 + 317952 * C_nested_base) * rootR0 n * rootP0 n * rootK0 n :=
  fastDFTRecursiveSteps_bounded_nested_root_le n B_in hB_in
    (fun _ hq => nestedSubMulBitOps_le_of_bounded hq)

/-- Constant `C_nested_total` for the grounded 3-tier (`d = 2 -> d = 1 -> d = 0`) step bound. -/
def C_nested_total : ℕ :=
  701974 + 336 * (118782569189317654368 * C_nested_base)

theorem C_nested_total_pos : 0 < C_nested_total := by
  unfold C_nested_total C_nested_base C_nested_d1
  positivity

/-- General $O(n \log n)$ upper bound on `intMulAlgorithmSteps M n` for any `M` bounded by
`(C_nested_base * L^3) * q` along the schedule of $n$. -/
theorem intMulAlgorithmSteps_bounded_nested_le_n_log_n_succ {M : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n)
    (hM : ∀ q ≤ 2736 * (rootP0 n * rootP0 n),
      M q ≤ (C_nested_base * ((Nat.log 2 (rootK0 n) + 1) * (Nat.log 2 (rootK0 n) + 1) *
        (Nat.log 2 (rootK0 n) + 1))) * q) :
    intMulAlgorithmSteps M n ≤
      C_nested_total * n * (Nat.log 2 n + 1) := by
  unfold intMulAlgorithmSteps C_nested_total
  have hlog_pos : 1 ≤ Nat.log 2 n + 1 := by omega
  have hsched : scheduleBitsLen n ≤ 70 * n * (Nat.log 2 n + 1) := by
    rw [scheduleBitsLen_eq]
    have h1 : 14 * n + 56 ≤ 70 * n := by omega
    calc 14 * n + 56 ≤ 70 * n := h1
      _ = (70 * n) * 1 := (mul_one _).symm
      _ ≤ 70 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (70 * n) hlog_pos
  have htable := fullScheduleTableBitsLen_le_succ hn
  have htree :
      scheduleTreeGenOps M (rootK0 n) (rootP0 n) ≤
        336 * (118782569189317017600 * C_nested_base) * n * (Nat.log 2 n + 1) := by
    calc scheduleTreeGenOps M (rootK0 n) (rootP0 n)
        ≤ (118782569189317017600 * C_nested_base) * (rootR0 n * rootP0 n * rootK0 n) := by
          have := scheduleTreeGenOps_bounded_nested_root_le n hM
          linarith
      _ ≤ (118782569189317017600 * C_nested_base) * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left _ (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 336 * (118782569189317017600 * C_nested_base) * n * (Nat.log 2 n + 1) := by ring
  have hfast :
      fastDFTRecursiveSteps M (rootK0 n) (rootP0 n)
        (levelScheduleBIn (rootK0 n) (rootP0 n) 0) ≤
        336 * (1044 + 317952 * C_nested_base) * n * (Nat.log 2 n + 1) := by
    calc fastDFTRecursiveSteps M (rootK0 n) (rootP0 n)
          (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
        ≤ (1044 + 317952 * C_nested_base) * (rootR0 n * rootP0 n * rootK0 n) := by
          have := fastDFTRecursiveSteps_bounded_nested_root_le n _ (le_refl _) hM
          linarith
      _ ≤ (1044 + 317952 * C_nested_base) * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left _ (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 336 * (1044 + 317952 * C_nested_base) * n * (Nat.log 2 n + 1) := by ring
  have hsq :
      3 * rootR0 n * M (rootP0 n + 2) ≤
        336 * (864 * C_nested_base) * n * (Nat.log 2 n + 1) := by
    set L := Nat.log 2 (rootK0 n) + 1
    have hp0 : 18 ≤ rootP0 n := rootP0_ge_eighteen n
    have hp2_le : rootP0 n + 2 ≤ 2736 * (rootP0 n * rootP0 n) := by nlinarith
    have hp2_two : rootP0 n + 2 ≤ 2 * rootP0 n := by omega
    have h1 := hM (rootP0 n + 2) hp2_le
    have hL_pos : 1 ≤ L := by omega
    have hcube_fourth : L * L * L ≤ (L * L) * (L * L) := by
      calc L * L * L = (L * L) * (L * 1) := by ring
        _ ≤ (L * L) * (L * L) := Nat.mul_le_mul_left (L * L) (Nat.mul_le_mul_left L hL_pos)
    have hfourth : (L * L) * (L * L) ≤ 144 * rootK0 n := log_rootK0_add_one_fourth_le n
    have hcube_K0 : L * L * L ≤ 144 * rootK0 n := le_trans hcube_fourth hfourth
    calc 3 * rootR0 n * M (rootP0 n + 2)
        ≤ 3 * rootR0 n * ((C_nested_base * (L * L * L)) * (rootP0 n + 2)) :=
          Nat.mul_le_mul_left _ h1
      _ ≤ 3 * rootR0 n * ((C_nested_base * (144 * rootK0 n)) * (2 * rootP0 n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hcube_K0) hp2_two)
      _ = (864 * C_nested_base) * (rootR0 n * rootP0 n * rootK0 n) := by ring
      _ ≤ (864 * C_nested_base) * (336 * n * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul_left _ (rootR0_mul_rootP0_mul_rootK0_le_succ hn)
      _ = 336 * (864 * C_nested_base) * n * (Nat.log 2 n + 1) := by ring
  have hlin2 : 2 * n ≤ 2 * n * (Nat.log 2 n + 1) := by
    calc 2 * n = (2 * n) * 1 := (mul_one _).symm
      _ ≤ 2 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (2 * n) hlog_pos
  have hlin4 : 4 * n ≤ 4 * n * (Nat.log 2 n + 1) := by
    calc 4 * n = (4 * n) * 1 := (mul_one _).symm
      _ ≤ 4 * n * (Nat.log 2 n + 1) := Nat.mul_le_mul_left (4 * n) hlog_pos
  calc scheduleBitsLen n + fullScheduleTableBitsLen n +
        scheduleTreeGenOps M (rootK0 n) (rootP0 n) + 2 * n +
        2 * fastDFTRecursiveSteps M (rootK0 n) (rootP0 n)
          (levelScheduleBIn (rootK0 n) (rootP0 n) 0) +
        3 * rootR0 n * M (rootP0 n + 2) + 4 * n
      ≤ 70 * n * (Nat.log 2 n + 1) + 330 * n * (Nat.log 2 n + 1) +
          336 * (118782569189317017600 * C_nested_base) * n * (Nat.log 2 n + 1) +
          2 * n * (Nat.log 2 n + 1) +
          2 * (336 * (1044 + 317952 * C_nested_base) * n * (Nat.log 2 n + 1)) +
          336 * (864 * C_nested_base) * n * (Nat.log 2 n + 1) +
          4 * n * (Nat.log 2 n + 1) := by
        refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsched htable) htree) hlin2)
          (Nat.mul_le_mul_left 2 hfast)) hsq) hlin4
    _ = (701974 + 336 * (118782569189317654368 * C_nested_base)) * n * (Nat.log 2 n + 1) := by ring

/-- **Unconditional $O(n \log n)$ Upper Bound when `M_mul` is the Grounded Nested Recursive Step-Count
`nestedSubMulBitOps` for all $n \ge 1$ (`intMulAlgorithmSteps_nestedSubMulBitOps_le_n_log_n_succ`)**:
When every $q_1$-bit sub-multiplication at depth `d = 2` is charged at the full nested recursive
algorithm step count `nestedSubMulBitOps q1 = intMulAlgorithmSteps schoolbookSubMulBitOps q1`
(which in turn charges every $q_0$-bit base multiplication at `d = 0` at the quadratic schoolbook
cost `schoolbookSubMulBitOps q0 = q0 * q0`), the total operation count
`intMulAlgorithmSteps nestedSubMulBitOps n` is bounded by `C_nested_total * n * (Nat.log 2 n + 1)`. -/
theorem intMulAlgorithmSteps_nestedSubMulBitOps_le_n_log_n_succ {n : ℕ} (hn : 1 ≤ n) :
    intMulAlgorithmSteps nestedSubMulBitOps n ≤
      C_nested_total * n * (Nat.log 2 n + 1) :=
  intMulAlgorithmSteps_bounded_nested_le_n_log_n_succ hn (fun _ hq => nestedSubMulBitOps_le_of_bounded hq)

theorem intMulAlgorithmSteps_scaled_nestedSubMulBitOps_le_n_log_n {n : ℕ} (hn : 2 ≤ n) :
    intMulAlgorithmSteps (scaledSubMulCost nestedSubMulBitOps) n ≤
      (2 * C_nested_total) * n * Nat.log 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hlog1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hlog_succ : Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n := by omega
  have h1 := intMulAlgorithmSteps_bounded_nested_le_n_log_n_succ hn1
    (fun _ hq => scaledSubMulCost_nestedSubMulBitOps_le_of_bounded hq)
  calc intMulAlgorithmSteps (scaledSubMulCost nestedSubMulBitOps) n
      ≤ C_nested_total * n * (Nat.log 2 n + 1) := h1
    _ ≤ C_nested_total * n * (2 * Nat.log 2 n) :=
        Nat.mul_le_mul_left (C_nested_total * n) hlog_succ
    _ = (2 * C_nested_total) * n * Nat.log 2 n := by ring

/-- **Unconditional $O(n \log n)$ Upper Bound when `M_mul` is the Grounded Nested Recursive Step-Count
`nestedSubMulBitOps` for all $n \ge 2$ (`intMulAlgorithmSteps_nestedSubMulBitOps_le_n_log_n`)**:
For every $n \ge 2$, the 3-tier grounded operation count `intMulAlgorithmSteps nestedSubMulBitOps n`
(grounded at `schoolbookSubMulBitOps q0 = q0 * q0` at depth `d = 0`) is bounded by
`(2 * C_nested_total) * n * Nat.log 2 n`. -/
theorem intMulAlgorithmSteps_nestedSubMulBitOps_le_n_log_n {n : ℕ} (hn : 2 ≤ n) :
    intMulAlgorithmSteps nestedSubMulBitOps n ≤
      (2 * C_nested_total) * n * Nat.log 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hlog1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hlog_succ : Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n := by omega
  have h1 := intMulAlgorithmSteps_nestedSubMulBitOps_le_n_log_n_succ hn1
  calc intMulAlgorithmSteps nestedSubMulBitOps n
      ≤ C_nested_total * n * (Nat.log 2 n + 1) := h1
    _ ≤ C_nested_total * n * (2 * Nat.log 2 n) :=
        Nat.mul_le_mul_left (C_nested_total * n) hlog_succ
    _ = (2 * C_nested_total) * n * Nat.log 2 n := by ring

/-! ## 2. End-to-End Bit-Level Multiplication Pipelines: Analytic, Schedule-Driven, and Computable Pure-Integer -/

/-- Unpack an integer `m` into `numChunks n` base-$2^b$ chunks (`natChunk (chunkBits n) (m % 2 ^ n) i`)
and reassemble the chunk polynomial $\sum_{i < N} a_i 2^{i b}$ (Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`)). -/
def unpackReassembleChunks (n m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (numChunks n),
    natChunk (chunkBits n) (m % 2 ^ n) i * (2 ^ chunkBits n) ^ i

/-- **Base-$2^b$ Chunk Unpack-Reassemble Identity (`unpackReassembleChunks_eq_mod`,
Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`))**:
For every $n, m \in \mathbb{N}$, unpacking `m % 2 ^ n` into `numChunks n` base-$2^b$ chunks
`natChunk (chunkBits n)` and evaluating the chunk sum recovers `m % 2 ^ n` bit-exactly. -/
@[simp]
theorem unpackReassembleChunks_eq_mod (n m : ℕ) :
    unpackReassembleChunks n m = m % 2 ^ n := by
  unfold unpackReassembleChunks
  exact sum_natChunk_root_eq (Nat.mod_lt m (Nat.two_pow_pos n))

/-- For any bit list `xs : List Bool` of length `n`, unpacking `decodeNatBits xs` into `numChunks n`
base-$2^b$ chunks and re-encoding into `n` bits recovers `xs` bit-exactly. -/
@[simp]
theorem encodeNatBits_unpackReassembleChunks_decodeNatBits (n : ℕ) (xs : List Bool)
    (hxs : xs.length = n) :
    encodeNatBits n (unpackReassembleChunks n (decodeNatBits xs)) = xs := by
  rw [unpackReassembleChunks_eq_mod]
  have hlt : decodeNatBits xs < 2 ^ n := hxs ▸ decodeNatBits_lt xs
  rw [Nat.mod_eq_of_lt hlt]
  exact hxs ▸ encodeNatBits_decodeNatBits xs

/-- Analytic end-to-end bit-level transformation computing the $2n$-bit product encoding from the
$2n$-bit input tape `inBits` via `reconstructProductViaFastDFT` (Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`)). -/
noncomputable def intMulPipelineBits (n : ℕ) (inBits : List Bool) : List Bool :=
  encodeNatBits (2 * n)
    (reconstructProductViaFastDFT n
      (decodeNatBits (inBits.take n))
      (decodeNatBits (inBits.drop n)))

@[simp]
theorem length_intMulPipelineBits (n : ℕ) (inBits : List Bool) :
    (intMulPipelineBits n inBits).length = 2 * n := by
  simp [intMulPipelineBits]

/-- **Unconditional Analytic Pipeline Bit-Exactness Theorem (`intMulPipelineBits_encodeInputBits`,
Theorem 1 (`thm:main`), proof Part 1 in Section 7.2 (`sec:cost-proof`))**:
For every $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$,
`intMulPipelineBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B)` via
`reconstructProductViaFastDFT_eq_mul`. -/
@[simp]
theorem intMulPipelineBits_encodeInputBits (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    intMulPipelineBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) := by
  unfold intMulPipelineBits
  rw [take_encodeInputBits, drop_encodeInputBits,
    decodeNatBits_encodeNatBits n A hA, decodeNatBits_encodeNatBits n B hB,
    reconstructProductViaFastDFT_eq_mul n A B hA hB]

/-- **Schedule-Driven End-to-End Bit-Level Pipeline (`intMulSchedPipelineBits`)**:
Computes the $2n$-bit product encoding from `inBits` via `reconstructProductViaScheduleFastDFT`
(which sizes every Kronecker slot bit-width from the data-independent schedule `scheduleSlotBits`
and `levelScheduleBIn` rather than runtime `vecInfNorm`). -/
noncomputable def intMulSchedPipelineBits (n : ℕ) (inBits : List Bool) : List Bool :=
  encodeNatBits (2 * n)
    (reconstructProductViaScheduleFastDFT n
      (decodeNatBits (inBits.take n))
      (decodeNatBits (inBits.drop n)))

@[simp]
theorem length_intMulSchedPipelineBits (n : ℕ) (inBits : List Bool) :
    (intMulSchedPipelineBits n inBits).length = 2 * n := by
  simp [intMulSchedPipelineBits]

/-- **Unconditional Schedule-Driven Pipeline Bit-Exactness Theorem
(`intMulSchedPipelineBits_encodeInputBits`)**:
For every $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$,
`intMulSchedPipelineBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B)` via
`reconstructProductViaScheduleFastDFT_eq_mul`. -/
@[simp]
theorem intMulSchedPipelineBits_encodeInputBits (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    intMulSchedPipelineBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) := by
  unfold intMulSchedPipelineBits
  rw [take_encodeInputBits, drop_encodeInputBits,
    decodeNatBits_encodeNatBits n A hA, decodeNatBits_encodeNatBits n B hB,
    reconstructProductViaScheduleFastDFT_eq_mul n A B hA hB]

/-- **Computable Pure-Integer End-to-End Bit-Level Pipeline (`computableIntMulPipelineBits`)**:
Computes the $2n$-bit product encoding from `inBits` and an integer schedule tree
`tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)` via
single-pass bit-list chunk slicing (`sliceBitChunkFn`), `computableConvFromChunksWithMul`, and
single-pass carry-save bit emission (`carrySaveEmitBits`), using **zero** `noncomputable`, **zero**
`ℝ`, **zero** `ℂ`, and **zero** monolithic $n$-bit or $2n$-bit `ℕ` decode/encode passes. -/
def computableIntMulPipelineBits (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (inBits : List Bool) : List Bool :=
  let b := chunkBits n
  let R0 := rootR0 n
  let aChunks := sliceBitChunkFn b R0 (inBits.take n)
  let bChunks := sliceBitChunkFn b R0 (inBits.drop n)
  let conv := computableConvFromChunksWithMul (· * ·) n tree aChunks bChunks
  carrySaveEmitBits b (2 * n) (List.ofFn (fun k : Fin R0 => (conv k).toNat)) 0

/-- Exact equivalence between the single-pass carry-save bit pipeline `computableIntMulPipelineBits`
and `encodeNatBits (2 * n) (computableReconstructProduct ...)`. -/
theorem computableIntMulPipelineBits_eq_encodeNatBits_reconstruct (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (inBits : List Bool) :
    computableIntMulPipelineBits n tree inBits =
      encodeNatBits (2 * n)
        (computableReconstructProduct n tree
          (decodeNatBits (inBits.take n))
          (decodeNatBits (inBits.drop n))) := by
  unfold computableIntMulPipelineBits
  rw [carrySaveEmitBits_conv_eq_encodeNatBits_reconstruct,
    computableReconstructProductWithMul_eq_of_mul_eq (· * ·) (fun _ _ => rfl)]

@[simp]
theorem length_computableIntMulPipelineBits (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (inBits : List Bool) :
    (computableIntMulPipelineBits n tree inBits).length = 2 * n := by
  rw [computableIntMulPipelineBits_eq_encodeNatBits_reconstruct, encodeNatBits_length]

/-- **Exact Bridge Between Computable Integer Pipeline and Schedule-Driven Pipeline
(`computableIntMulPipelineBits_canonical_eq_intMulSchedPipelineBits`)**:
For every $n \in \mathbb{N}$ and every input bit list `inBits`, evaluating the computable pure-integer
pipeline `computableIntMulPipelineBits` on `canonicalScheduleIntTree` produces the exact same
$2n$-bit output list as `intMulSchedPipelineBits n inBits`. -/
theorem computableIntMulPipelineBits_canonical_eq_intMulSchedPipelineBits (n : ℕ)
    (inBits : List Bool) :
    computableIntMulPipelineBits n
      (canonicalScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
      inBits = intMulSchedPipelineBits n inBits := by
  rw [computableIntMulPipelineBits_eq_encodeNatBits_reconstruct]
  unfold intMulSchedPipelineBits
  congr 1
  unfold computableReconstructProduct reconstructProductViaScheduleFastDFT
  dsimp only
  rw [evalBaseChunks_ofFn_eq_sum]
  simp_rw [computableFastTwoCallDFTConv_canonical_eq]

/-- **Unconditional Bit-Exactness of the Computable Pure-Integer End-to-End Pipeline on `canonicalScheduleIntTree`
(`computableIntMulPipelineBits_canonical_encodeInputBits`)**:
For every $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, the computable pure-integer
bit-level pipeline `computableIntMulPipelineBits` evaluated on `canonicalScheduleIntTree` and
`encodeInputBits n A B` outputs `encodeNatBits (2 * n) (A * B)` bit-exactly. -/
@[simp]
theorem computableIntMulPipelineBits_canonical_encodeInputBits (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableIntMulPipelineBits n
      (canonicalScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
      (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) := by
  rw [computableIntMulPipelineBits_canonical_eq_intMulSchedPipelineBits,
    intMulSchedPipelineBits_encodeInputBits n A B hA hB]

/-- **Unconditional Bit-Exactness of `computableIntMulPipelineBits` on `computeScheduleIntTree`
(`computableIntMulPipelineBits_computeScheduleIntTree_encodeInputBits`)**:
For every $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, the computable pure-integer
bit-level pipeline `computableIntMulPipelineBits` evaluated on the dynamically Taylor-synthesized
schedule tree `computeScheduleIntTree` (with **zero** `noncomputable`, **zero** `ℝ`, and **zero** `ℂ`)
outputs `encodeNatBits (2 * n) (A * B)` bit-exactly. -/
@[simp]
theorem computableIntMulPipelineBits_computeScheduleIntTree_encodeInputBits (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableIntMulPipelineBits n
      (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
      (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) := by
  exact computableIntMulBits_encodeInputBits n A B hA hB

/-! ### 2.2 Intrinsically Operation-Tracking Pipeline Bounds & Single-Statement Theorems -/

theorem taylorPerTermStep_le_of_w_le {w q M : ℕ} (hw : w ≤ 1000 * q) (hq : 1 ≤ q) :
    M + 25 * w * w + 70 * w + 50 ≤ 25100000 * ((q + 1) * (q + M)) := by
  have hw2 : w * w ≤ 1000000 * (q * q) := by
    calc w * w ≤ (1000 * q) * (1000 * q) := Nat.mul_le_mul hw hw
      _ = 1000000 * (q * q) := by ring
  nlinarith only [hw, hw2, hq]

theorem taylorLoopStep_le {L K w q M : ℕ} (hL : L ≤ K * (q + 1))
    (hw : w ≤ 1000 * q) (hq : 1 ≤ q) :
    L * (M + 25 * w * w + 70 * w + 50) ≤
      (25100000 * K) * ((q + 1) * (q + 1) * (q + M)) := by
  calc L * (M + 25 * w * w + 70 * w + 50)
      ≤ (K * (q + 1)) * (25100000 * ((q + 1) * (q + M))) :=
        Nat.mul_le_mul hL (taylorPerTermStep_le_of_w_le hw hq)
    _ = (25100000 * K) * ((q + 1) * (q + 1) * (q + M)) := by ring

theorem taylorLoopStep_exp_le {L K w q M : ℕ} (hL : L ≤ K * (q + 1))
    (hw : w ≤ 1000 * q) (hq : 1 ≤ q) :
    L * (M + 20 * w * w + 50 * w + 35) ≤
      (25100000 * K) * ((q + 1) * (q + 1) * (q + M)) := by
  have h1 : M + 20 * w * w + 50 * w + 35 ≤ M + 25 * w * w + 70 * w + 50 := by nlinarith
  exact le_trans (Nat.mul_le_mul_left L h1) (taylorLoopStep_le hL hw hq)

theorem taylorDivWidthSq_le_of_le {u q M : ℕ} (hu : u ≤ 2500 * (q + 1)) (hq : 1 ≤ q) :
    60 * u * u + 20 * u + 100 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) := by
  have hu2 : 60 * u * u + 20 * u + 100 ≤ 380000000 * ((q + 1) * (q + 1)) := by
    have hsq : u * u ≤ 6250000 * ((q + 1) * (q + 1)) := by
      calc u * u ≤ (2500 * (q + 1)) * (2500 * (q + 1)) := Nat.mul_le_mul hu hu
        _ = 6250000 * ((q + 1) * (q + 1)) := by ring
    nlinarith only [hu, hsq, hq]
  have hqM : 1 ≤ q + M := by omega
  calc 60 * u * u + 20 * u + 100
      ≤ (380000000 * ((q + 1) * (q + 1))) * 1 := by linarith only [hu2]
    _ ≤ (380000000 * ((q + 1) * (q + 1))) * (q + M) := Nat.mul_le_mul_left _ hqM
    _ = 380000000 * ((q + 1) * (q + 1) * (q + M)) := by ring

theorem roundDivIntTracked_snd_le_taylor {u q M : ℕ} (num den : ℤ)
    (hu : u ≤ 2500 * (q + 1)) (hq : 1 ≤ q) :
    (roundDivIntTracked u num den).2 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) := by
  have h0 := roundDivIntTracked_snd_le u num den
  have h1 : 5 * u * u + 20 * u + 13 ≤ 60 * u * u + 20 * u + 100 := by nlinarith
  exact le_trans h0 (le_trans h1 (taylorDivWidthSq_le_of_le hu hq))

theorem expTwoPiIFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ) (w q : ℕ)
    (hw : w ≤ 1000 * q) (hq : 1 ≤ q) (piFixed : ℤ) (num : ℤ) (den : ℕ) (M : ℕ)
    (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 8 * w + 10) :
    (expTwoPiIFixedWithMulTracked smulTracked w q piFixed num den).2 ≤
      25000000 * scheduleSeriesTerms q * (q + M) := by
  unfold expTwoPiIFixedWithMulTracked scheduleSeriesTerms
  split_ifs with hden
  · dsimp only
    have hpos : 1 ≤ (q + 1) * (q + 1) * (q + M) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hrhs : 25000000 * (120 * (q + 1) * (q + 1)) * (q + M) =
        3000000000 * ((q + 1) * (q + 1) * (q + M)) := by ring
    rw [hrhs]; omega
  · dsimp only
    set S : ℕ := q + 10
    set q_pi : ℕ := 4 * (S + 3) + 6
    set N : ℕ := 4 * 10 + S + 1
    set M_terms : ℕ := N + 6
    set q_r : ℕ := 2 * M_terms
    set q_acc : ℕ := 3 * M_terms + 6
    set prodPi := smulTracked piFixed (num % (den : ℤ))
    set r_mant := roundDivIntTracked (2 * w + q_r + 2)
      (2 * prodPi.1 * (2 : ℤ) ^ q_r) ((den : ℤ) * (2 : ℤ) ^ q_pi)
    set arr := expTermArrayFixedWithMulTracked smulTracked w q_r q_acc M_terms r_mant.1
    set reSum := sumRangeTracked w (M_terms + 1) (fun m => (iPowRe m * arr.1.getD m 0, 2))
    set imSum := sumRangeTracked w (M_terms + 1) (fun m => (iPowIm m * arr.1.getD m 0, 2))
    set reOut := roundDivIntTracked (w + M_terms + q + 2) (reSum.1 * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)
    set imOut := roundDivIntTracked (w + M_terms + q + 2) (imSum.1 * (2 : ℤ) ^ q) ((2 : ℤ) ^ q_acc)
    have hprod : prodPi.2 ≤ M + 8 * w + 10 := hM _ _
    have hM_terms : M_terms = q + 57 := by dsimp [M_terms, N, S]; omega
    have hq_r : q_r = 2 * (q + 57) := by dsimp [q_r]; omega
    have hrm : r_mant.2 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      roundDivIntTracked_snd_le_taylor _ _ (by omega) hq
    have harr0 : arr.2 ≤ M_terms * (M + 8 * w + 10 + 20 * w * w + 40 * w + 17) + 4 :=
      expTermArrayFixedWithMulTracked_snd_le smulTracked w q_r q_acc M_terms r_mant.1
        (M + 8 * w + 10) hM
    have hMt_le : M_terms ≤ 29 * (q + 1) := by omega
    have harr : arr.2 ≤ (25100000 * 29) * ((q + 1) * (q + 1) * (q + M)) + 4 := by
      have hsub : M + 8 * w + 10 + 20 * w * w + 40 * w + 17 ≤ M + 25 * w * w + 70 * w + 50 := by
        nlinarith
      have h1 := le_trans (Nat.mul_le_mul_left M_terms hsub) (taylorLoopStep_le hMt_le hw hq)
      linarith only [harr0, h1]
    have hre : reSum.2 ≤ (M_terms + 1) * (2 + w + 2) + 2 :=
      sumRangeTracked_snd_le w (M_terms + 1) _ 2 (fun _ _ => le_rfl)
    have him : imSum.2 ≤ (M_terms + 1) * (2 + w + 2) + 2 :=
      sumRangeTracked_snd_le w (M_terms + 1) _ 2 (fun _ _ => le_rfl)
    have hreOut : reOut.2 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      roundDivIntTracked_snd_le_taylor _ _ (by omega) hq
    have himOut : imOut.2 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      roundDivIntTracked_snd_le_taylor _ _ (by omega) hq
    have hmod : 5 * w * w + 20 * w + 13 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      le_trans (by nlinarith) (taylorDivWidthSq_le_of_le (u := w) (by omega) hq)
    have hre_im : reSum.2 + imSum.2 + prodPi.2 + w + q + 8 ≤
        100000 * ((q + 1) * (q + 1) * (q + M)) := by
      rw [hM_terms] at hre him
      have hqM : q + M ≤ (q + 1) * (q + M) := Nat.le_mul_of_pos_left _ (by omega)
      have hq2 : (q + 1) * (q + 1) ≤ (q + 1) * (q + 1) * (q + M) :=
        Nat.le_mul_of_pos_right _ (by omega)
      nlinarith only [hw, hq, hprod, hre, him, hqM, hq2]
    clear_value prodPi r_mant arr reSum imSum reOut imOut
    have hrhs : 25000000 * (120 * (q + 1) * (q + 1)) * (q + M) =
        3000000000 * ((q + 1) * (q + 1) * (q + M)) := by ring
    rw [hrhs]
    linarith only [hrm, harr, hreOut, himOut, hmod, hre_im]

theorem computeFilterTapEntryTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    (w m1 t1 pW pC q S : ℕ) (hw : w ≤ 1000 * q) (hq : 1 ≤ q) (hm1 : m1 ≤ q) (hpC : pC ≤ q)
    (hS : S ≤ 4 * q + 20) (piFixed l2Fixed : ℤ) (j1 : Fin t1) (d : ℤ) (M : ℕ)
    (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 8 * w + 10) :
    (computeFilterTapEntryTracked smulTracked w m1 t1 pW pC q S piFixed l2Fixed j1 d).2 ≤
      50000000 * scheduleSeriesTerms q * (q + M) := by
  unfold computeFilterTapEntryTracked scheduleSeriesTerms
  split_ifs with hd
  · dsimp only
    set q_pi : ℕ := 4 * (S + 3) + 6
    set q_l2 : ℕ := S + (S + 2)
    set N_s : ℕ := 4 * (5 * (m1 + 1)) + S + 1
    set q_accs : ℕ := 3 * (N_s + 6) + 6
    set N_e : ℕ := 4 * (25 * (pC + 1)) + S + 1
    set q_acce : ℕ := 3 * (N_e + 6) + 6
    set θNumP := smulTracked piFixed (d * (t1 : ℤ) - (j1.val : ℤ))
    set θDen : ℤ := (t1 : ℤ) * (2 : ℤ) ^ q_pi
    set sincFixed := sincTaylorFixedWithMulTracked smulTracked w N_s θNumP.1 θDen
    set θSq := smulTracked θNumP.1 θNumP.1
    set gNum : ℤ := -(θSq.1 * (2 : ℤ) ^ q_l2)
    set gDen : ℤ := (4 * (pW : ℤ) * (t1 : ℤ) * (t1 : ℤ)) * l2Fixed * (2 : ℤ) ^ (2 * q_pi)
    set expFixed := expTaylorFixedWithMulTracked smulTracked w N_e gNum gDen
    set prodSE := smulTracked sincFixed.1 expFixed.1
    set res := roundDivIntTracked (2 * w + q + 2) (prodSE.1 * (2 : ℤ) ^ q) ((2 : ℤ) ^ (q_accs + q_acce))
    have hNs : N_s + 7 ≤ 48 * (q + 1) := by dsimp [N_s]; omega
    have hNe : N_e + 7 ≤ 128 * (q + 1) := by dsimp [N_e]; omega
    have hp1 : θNumP.2 ≤ M + 8 * w + 10 := hM _ _
    have hsinc0 : sincFixed.2 ≤
        (N_s + 7) * (M + 25 * w * w + 70 * w + 50) +
          28 * (w + N_s + 7) * (w + N_s + 7) + 30 :=
      sincTaylorFixedWithMulTracked_snd_le smulTracked w N_s θNumP.1 θDen M hM
    have hp2 : θSq.2 ≤ M + 8 * w + 10 := hM _ _
    have hexp0 : expFixed.2 ≤
        (N_e + 7) * (M + 20 * w * w + 50 * w + 35) +
          55 * (w + N_e + 7) * (w + N_e + 7) + 30 :=
      expTaylorFixedWithMulTracked_snd_le smulTracked w N_e gNum gDen M hM
    have hp3 : prodSE.2 ≤ M + 8 * w + 10 := hM _ _
    have hsinc_main :
        (N_s + 7) * (M + 25 * w * w + 70 * w + 50) ≤
          (25100000 * 48) * ((q + 1) * (q + 1) * (q + M)) :=
      taylorLoopStep_le hNs hw hq
    have hsinc_tail :
        28 * (w + N_s + 7) * (w + N_s + 7) + 30 ≤
          380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      le_trans (by nlinarith) (taylorDivWidthSq_le_of_le (u := w + N_s + 7) (by omega) hq)
    have hexp_main :
        (N_e + 7) * (M + 20 * w * w + 50 * w + 35) ≤
          (25100000 * 128) * ((q + 1) * (q + 1) * (q + M)) :=
      taylorLoopStep_exp_le hNe hw hq
    have hexp_tail :
        55 * (w + N_e + 7) * (w + N_e + 7) + 30 ≤
          380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      le_trans (by nlinarith) (taylorDivWidthSq_le_of_le (u := w + N_e + 7) (by omega) hq)
    have hres : res.2 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      roundDivIntTracked_snd_le_taylor _ _ (by omega) hq
    have hsc : 4 * w * w + 20 * w + 16 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) :=
      le_trans (by nlinarith) (taylorDivWidthSq_le_of_le (u := w) (by omega) hq)
    have hrem : θNumP.2 + θSq.2 + prodSE.2 + (2 * w + q + 2) + 8 ≤
        100000 * ((q + 1) * (q + 1) * (q + M)) := by
      have hqM : q + M ≤ (q + 1) * (q + M) := Nat.le_mul_of_pos_left _ (by omega)
      have hq2 : (q + 1) * (q + 1) ≤ (q + 1) * (q + 1) * (q + M) :=
        Nat.le_mul_of_pos_right _ (by omega)
      nlinarith only [hw, hq, hp1, hp2, hp3, hqM, hq2]
    clear_value θNumP sincFixed θSq expFixed prodSE res
    have hrhs : 50000000 * (120 * (q + 1) * (q + 1)) * (q + M) =
        6000000000 * ((q + 1) * (q + 1) * (q + M)) := by ring
    rw [hrhs]
    linarith only [hsinc0, hsinc_main, hsinc_tail, hexp0, hexp_main, hexp_tail, hres, hsc, hrem]
  · dsimp only
    have hpos : 1 ≤ (q + 1) * (q + 1) * (q + M) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hrhs : 50000000 * (120 * (q + 1) * (q + 1)) * (q + M) =
        6000000000 * ((q + 1) * (q + 1) * (q + M)) := by ring
    rw [hrhs]; omega

theorem computeGHatMantissaEntryTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ)
    (w q S N_erf : ℕ) (hw : w ≤ 1000 * q) (hq : 1 ≤ q) (hS : S ≤ 3 * q + 20)
    (hN : N_erf + 7 ≤ 200 * (q + 1)) (cFixed sqrtPiFixed : ℤ) (yNum : ℤ) (r : ℕ) (M : ℕ)
    (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 8 * w + 10) :
    (computeGHatMantissaEntryTracked smulTracked w q S N_erf cFixed sqrtPiFixed yNum r).2 ≤
      100000000 * scheduleSeriesTerms q * (q + M) := by
  unfold computeGHatMantissaEntryTracked scheduleSeriesTerms
  dsimp only
  set zDen : ℤ := 2 * (r : ℤ) * (2 : ℤ) ^ S
  set z1Num := smulTracked cFixed ((r : ℤ) - 2 * yNum)
  set I1Fixed := erfIntegralTaylorFixedWithMulTracked smulTracked w N_erf z1Num.1 zDen
  set z2Num := smulTracked cFixed ((r : ℤ) + 2 * yNum)
  set I2Fixed := erfIntegralTaylorFixedWithMulTracked smulTracked w N_erf z2Num.1 zDen
  set div := roundDivIntTracked (2 * w + S + q + 2) (((I1Fixed.1 + I2Fixed.1) * (2 : ℤ) ^ S) * (2 : ℤ) ^ q)
    (sqrtPiFixed * (2 : ℤ) ^ (N_erf + 6 + (3 * (N_erf + 6) + 6)))
  have hz1 : z1Num.2 ≤ M + 8 * w + 10 := hM _ _
  have hI1 : I1Fixed.2 ≤
      (N_erf + 7) * (M + 25 * w * w + 70 * w + 50) +
        2 * M + 28 * (w + N_erf + 7) * (w + N_erf + 7) + 16 * w + 50 :=
    erfIntegralTaylorFixedWithMulTracked_snd_le smulTracked w N_erf z1Num.1 zDen M hM
  have hz2 : z2Num.2 ≤ M + 8 * w + 10 := hM _ _
  have hI2 : I2Fixed.2 ≤
      (N_erf + 7) * (M + 25 * w * w + 70 * w + 50) +
        2 * M + 28 * (w + N_erf + 7) * (w + N_erf + 7) + 16 * w + 50 :=
    erfIntegralTaylorFixedWithMulTracked_snd_le smulTracked w N_erf z2Num.1 zDen M hM
  have herf_main :
      (N_erf + 7) * (M + 25 * w * w + 70 * w + 50) ≤
        (25100000 * 200) * ((q + 1) * (q + 1) * (q + M)) :=
    taylorLoopStep_le hN hw hq
  have herf_tail :
      28 * (w + N_erf + 7) * (w + N_erf + 7) + 50 ≤
        380000000 * ((q + 1) * (q + 1) * (q + M)) :=
    le_trans (by nlinarith) (taylorDivWidthSq_le_of_le (u := w + N_erf + 7) (by omega) hq)
  have hdiv : div.2 ≤ 380000000 * ((q + 1) * (q + 1) * (q + M)) :=
    roundDivIntTracked_snd_le_taylor _ _ (by omega) hq
  have hrem : z1Num.2 + z2Num.2 + 4 * M + 32 * w + (2 * w + q + 2) + 8 ≤
      100000 * ((q + 1) * (q + 1) * (q + M)) := by
    have hqM : q + M ≤ (q + 1) * (q + M) := Nat.le_mul_of_pos_left _ (by omega)
    have hq2 : (q + 1) * (q + 1) ≤ (q + 1) * (q + 1) * (q + M) :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith only [hw, hq, hz1, hz2, hqM, hq2]
  clear_value z1Num I1Fixed z2Num I2Fixed div
  have hrhs : 100000000 * (120 * (q + 1) * (q + 1)) * (q + M) =
      12000000000 * ((q + 1) * (q + 1) * (q + M)) := by ring
  rw [hrhs]
  linarith only [hI1, hI2, herf_main, herf_tail, hdiv, hrem]

set_option maxRecDepth 4000 in
/-- **Bottom-Up Step-Count Upper Bound for `computeScheduleIntTreeWithMulTracked`
(`computeScheduleIntTreeWithMulTracked_snd_le`)**:
For any tracked bit-list sub-multiplier `subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)`
whose `.2` cost at bit-width $w \ge 1$ is bounded by `M_mul w`, the bottom-up accumulated step count
`(computeScheduleIntTreeWithMulTracked subMulBits K p B_in).2` is bounded by
`150000000 * scheduleTreeGenOps (scaledSubMulCost M_mul) K p`. -/
theorem computeScheduleIntTreeWithMulTracked_snd_le
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)) (M_mul : ℕ → ℕ)
    (hM : ∀ (w : ℕ) (xs ys : List Bool), 1 ≤ w → (subMulBits w xs ys).2 ≤ M_mul w) (K : ℕ) :
    ∀ p B_in : ℕ,
      (computeScheduleIntTreeWithMulTracked subMulBits K p B_in).2 ≤
        150000000 * scheduleTreeGenOps (scaledSubMulCost M_mul) K p := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in
    rw [computeScheduleIntTreeWithMulTracked, scheduleTreeGenOps]
    split_ifs with hcond
    · have hK2 : 2 ≤ K := hcond.2
      have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      dsimp only
      set q := qChildEll K p
      set w := 1000 * q
      set pW := pWorkEll K p
      set pC := pChildEll K p
      set m1 := computeM1Ell K p
      set r := rEll K
      set t1 := t1Ell K
      set smul := signedMulFromTrackedBitMul w (subMulBits w)
      set piRoot := approxPiFixedTracked w (q + 10)
      set S_tap := q + 3 * pC + 20
      set q_l2_tap := S_tap + (S_tap + 2)
      set piTap := approxPiFixedTracked w S_tap
      set l2Tap := approxLogTwoFixedTracked w S_tap
      set l2TapFixed := max ((2 : ℤ) ^ (q_l2_tap - 1)) l2Tap.1
      set S_ghat := q + 2 * pW + 20
      set q_l2_ghat := 2 * S_ghat + (2 * S_ghat + 2)
      set l2GHat := approxLogTwoFixedTracked w (2 * S_ghat)
      set l2GHatFixed := max ((2 : ℤ) ^ (q_l2_ghat - 1)) l2GHat.1
      set cBoundSq := binaryRestoringSqrtRegTracked w (3 * pW)
      set cBound := cBoundSq.1.1 + 1
      set cRaw := approxSqrtFixedTracked w (2 * S_ghat + 2) (4 * (pW : ℤ) * l2GHatFixed)
      set cFixed := min ((cBound : ℤ) * (2 : ℤ) ^ S_ghat) cRaw.1
      set B_erf := 2 * cBound
      set N_erf := 4 * B_erf ^ 2 + (S_ghat + B_erf) + 1
      set pi2S := approxPiFixedTracked w (2 * S_ghat)
      set sqrtPiRaw := approxSqrtFixedTracked w (6 * S_ghat + 18) pi2S.1
      set sqrtPiFixed := max ((2 : ℤ) ^ S_ghat) sqrtPiRaw.1
      set tapTbl := memoizeFilterTapTracked m1
        (computeFilterTapEntryTracked smul w m1 t1 pW pC q S_tap piTap.1 l2TapFixed)
      set preTbl := memoizeFinTracked (fun k2 : Fin r =>
        expTwoPiIFixedWithMulTracked smul w q piRoot.1 (k2.val : ℤ) (2 * r))
      set postTbl := memoizeFinTracked (fun k2 : Fin r =>
        expTwoPiIFixedWithMulTracked smul w q piRoot.1 (-(k2.val : ℤ)) (2 * r))
      set c0Tbl := memoizeFinTracked (fun u2 : Fin r =>
        computeGHatMantissaEntryTracked smul w q S_ghat N_erf cFixed sqrtPiFixed (u2.val : ℤ) r)
      set c1Tbl := memoizeFinTracked (fun u2 : Fin r =>
        computeGHatMantissaEntryTracked smul w q S_ghat N_erf cFixed sqrtPiFixed
          ((r : ℤ) - (u2.val : ℤ)) r)
      set child := computeScheduleIntTreeWithMulTracked subMulBits
        (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
      set S_term := scheduleSeriesTerms q * (q + scaledSubMulCost M_mul q)
      have hq_eq : q = p + 2 * K + 14 := qChildEll_eq K p
      have hpC_eq : pC = p + 2 * K + 12 := pChildEll_eq K p
      have hq14 : 14 ≤ q := by omega
      have hq1 : 1 ≤ q := by omega
      have hw_eq : w = 1000 * q := rfl
      have hw1 : 1 ≤ w := by omega
      have hpC_le : pC ≤ q := by omega
      have hpW_le : pW ≤ q := by
        have : pW ≤ pC := by unfold pC pChildEll; omega
        omega
      have hm1_le : m1 ≤ q := le_trans (computeM1Ell_le_pChildEll K p) hpC_le
      have hm1_pos : 1 ≤ m1 := computeM1Ell_pos K p
      have ht1_pos : 1 ≤ t1 := t1Ell_pos K
      have hr_pos : 1 ≤ r := rEll_pos K
      have hsmul : ∀ x y : ℤ, (smul x y).2 ≤ scaledSubMulCost M_mul q + 8 * w + 10 :=
        signedMulFromTrackedBitMul_snd_le w (subMulBits w) (scaledSubMulCost M_mul q)
          (fun xs ys => le_trans (hM w xs ys hw1) (le_scaledSubMulCost_thousand M_mul q))
      have hS_tap : S_tap ≤ 4 * q + 20 := by dsimp [S_tap]; omega
      have hS_ghat : S_ghat ≤ 3 * q + 20 := by dsimp [S_ghat]; omega
      have hcBound_lt : 3 * pW < 4 ^ w := (lt_of_le_of_lt (by omega : 3 * pW ≤ w)
        Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by decide) w)
      have hcBound_eq : cBoundSq.1.1 = Nat.sqrt (3 * pW) :=
        binaryRestoringSqrtRegTracked_fst_fst hcBound_lt
      have hsqrt_sq : Nat.sqrt (3 * pW) * Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le (3 * pW)
      have hsqrt_le : Nat.sqrt (3 * pW) ≤ 3 * pW := Nat.sqrt_le_self (3 * pW)
      have hNerf : N_erf + 7 ≤ 200 * (q + 1) := by
        dsimp [N_erf, B_erf, cBound]
        rw [hcBound_eq]
        nlinarith only [hpW_le, hq14, hS_ghat, hsqrt_sq, hsqrt_le]
      have hpiRoot0 := approxPiFixedTracked_snd_le w (q + 10)
      have hpiTap0 := approxPiFixedTracked_snd_le w S_tap
      have hl2Tap0 := approxLogTwoFixedTracked_snd_le w S_tap
      have hl2GHat0 := approxLogTwoFixedTracked_snd_le w (2 * S_ghat)
      have hcBoundSq0 := binaryRestoringSqrtRegTracked_snd_le w (3 * pW)
      have hcRaw0 := approxSqrtFixedTracked_snd_le w (2 * S_ghat + 2) (4 * (pW : ℤ) * l2GHatFixed)
      have hpi2S0 := approxPiFixedTracked_snd_le w (2 * S_ghat)
      have hsqrtPiRaw0 := approxSqrtFixedTracked_snd_le w (6 * S_ghat + 18) pi2S.1
      have hpiRoot : piRoot.2 ≤ 200000000 * ((q + 1) * ((q + 1) * (q + 1))) + w + 24 := by
        have h1 : q + 10 + 4 ≤ 2 * (q + 1) := by omega
        have h2 : 70 * (w + 4 * (q + 10) + 20) * (w + 4 * (q + 10) + 20) ≤
            100000000 * ((q + 1) * (q + 1)) := by
          rw [hw_eq]; nlinarith only [hq14]
        exact le_trans hpiRoot0 (Nat.add_le_add (Nat.add_le_add
          (le_trans (Nat.mul_le_mul h1 h2) (by ring_nf; exact le_rfl)) le_rfl) le_rfl)
      have hpiTap : piTap.2 ≤ 600000000 * ((q + 1) * ((q + 1) * (q + 1))) + w + 24 := by
        have h1 : S_tap + 4 ≤ 6 * (q + 1) := by omega
        have h2 : 70 * (w + 4 * S_tap + 20) * (w + 4 * S_tap + 20) ≤
            100000000 * ((q + 1) * (q + 1)) := by
          rw [hw_eq]; nlinarith only [hq14, hS_tap]
        exact le_trans hpiTap0 (Nat.add_le_add (Nat.add_le_add
          (le_trans (Nat.mul_le_mul h1 h2) (by ring_nf; exact le_rfl)) le_rfl) le_rfl)
      have hl2Tap : l2Tap.2 ≤ 120000000 * ((q + 1) * ((q + 1) * (q + 1))) + 4 := by
        have h1 : S_tap + 2 ≤ 6 * (q + 1) := by omega
        have h2 : 15 * (w + 2 * S_tap + 4) * (w + 2 * S_tap + 4) ≤
            20000000 * ((q + 1) * (q + 1)) := by
          rw [hw_eq]; nlinarith only [hq14, hS_tap]
        exact le_trans hl2Tap0 (Nat.add_le_add
          (le_trans (Nat.mul_le_mul h1 h2) (by ring_nf; exact le_rfl)) le_rfl)
      have hl2GHat : l2GHat.2 ≤ 160000000 * ((q + 1) * ((q + 1) * (q + 1))) + 4 := by
        have h1 : 2 * S_ghat + 2 ≤ 8 * (q + 1) := by omega
        have h2 : 15 * (w + 2 * (2 * S_ghat) + 4) * (w + 2 * (2 * S_ghat) + 4) ≤
            20000000 * ((q + 1) * (q + 1)) := by
          rw [hw_eq]; nlinarith only [hq14, hS_ghat]
        exact le_trans hl2GHat0 (Nat.add_le_add
          (le_trans (Nat.mul_le_mul h1 h2) (by ring_nf; exact le_rfl)) le_rfl)
      have hpi2S : pi2S.2 ≤ 800000000 * ((q + 1) * ((q + 1) * (q + 1))) + w + 24 := by
        have h1 : 2 * S_ghat + 4 ≤ 8 * (q + 1) := by omega
        have h2 : 70 * (w + 4 * (2 * S_ghat) + 20) * (w + 4 * (2 * S_ghat) + 20) ≤
            100000000 * ((q + 1) * (q + 1)) := by
          rw [hw_eq]; nlinarith only [hq14, hS_ghat]
        exact le_trans hpi2S0 (Nat.add_le_add (Nat.add_le_add
          (le_trans (Nat.mul_le_mul h1 h2) (by ring_nf; exact le_rfl)) le_rfl) le_rfl)
      have hsqrt_all :
          cBoundSq.2 + cRaw.2 + sqrtPiRaw.2 + 3 * w + (4 * w * w + 20 * w + 16) + 100 ≤
            25000000 * ((q + 1) * ((q + 1) * (q + 1))) := by
        have hq3 : (q + 1) * (q + 1) ≤ (q + 1) * ((q + 1) * (q + 1)) :=
          Nat.le_mul_of_pos_left _ (by omega)
        rw [hw_eq] at hcBoundSq0 hcRaw0 hsqrtPiRaw0 ⊢
        nlinarith only [hq14, hS_ghat, hcBoundSq0, hcRaw0, hsqrtPiRaw0, hq3]
      have hhoist :
          piRoot.2 + piTap.2 + l2Tap.2 + l2GHat.2 + cBoundSq.2 + cRaw.2 +
            pi2S.2 + sqrtPiRaw.2 + (4 * w * w + 20 * w + 16) ≤ 35000000 * S_term := by
        have hq3_le : (q + 1) * ((q + 1) * (q + 1)) ≤ 2 * ((q + 1) * (q + 1) * (q + scaledSubMulCost M_mul q)) := by
          have : q + 1 ≤ 2 * (q + scaledSubMulCost M_mul q) := by omega
          calc (q + 1) * ((q + 1) * (q + 1))
              = ((q + 1) * (q + 1)) * (q + 1) := by ring
            _ ≤ ((q + 1) * (q + 1)) * (2 * (q + scaledSubMulCost M_mul q)) := Nat.mul_le_mul_left _ this
            _ = 2 * ((q + 1) * (q + 1) * (q + scaledSubMulCost M_mul q)) := by ring
        have hS_eq : 35000000 * S_term = 4200000000 * ((q + 1) * (q + 1) * (q + scaledSubMulCost M_mul q)) := by
          dsimp [S_term, scheduleSeriesTerms]; ring
        rw [hS_eq]
        clear_value piRoot piTap l2Tap l2GHat cBoundSq cRaw pi2S sqrtPiRaw q w S_term
        omega
      have htap : tapTbl.2 ≤ t1 * ((2 * m1 + 1) * (50000000 * S_term)) + t1 * (2 * m1 + 1) + 1 :=
        memoizeFilterTapTracked_snd_le m1
          (computeFilterTapEntryTracked smul w m1 t1 pW pC q S_tap piTap.1 l2TapFixed)
          (50000000 * S_term)
          (fun j1 d => by
            simpa [S_term, mul_assoc] using
              computeFilterTapEntryTracked_snd_le smul w m1 t1 pW pC q S_tap
                (le_refl w) hq1 hm1_le hpC_le hS_tap piTap.1 l2TapFixed j1 d
                (scaledSubMulCost M_mul q) hsmul)
      have hpre : preTbl.2 ≤ r * (25000000 * S_term) + r + 1 :=
        memoizeFinTracked_snd_le
          (fun k2 : Fin r => expTwoPiIFixedWithMulTracked smul w q piRoot.1 (k2.val : ℤ) (2 * r))
          (25000000 * S_term)
          (fun k2 => by
            simpa [S_term, mul_assoc] using
              expTwoPiIFixedWithMulTracked_snd_le smul w q (le_refl w) hq1 piRoot.1 (k2.val : ℤ) (2 * r)
                (scaledSubMulCost M_mul q) hsmul)
      have hpost : postTbl.2 ≤ r * (25000000 * S_term) + r + 1 :=
        memoizeFinTracked_snd_le
          (fun k2 : Fin r => expTwoPiIFixedWithMulTracked smul w q piRoot.1 (-(k2.val : ℤ)) (2 * r))
          (25000000 * S_term)
          (fun k2 => by
            simpa [S_term, mul_assoc] using
              expTwoPiIFixedWithMulTracked_snd_le smul w q (le_refl w) hq1 piRoot.1 (-(k2.val : ℤ)) (2 * r)
                (scaledSubMulCost M_mul q) hsmul)
      have hc0 : c0Tbl.2 ≤ r * (100000000 * S_term) + r + 1 :=
        memoizeFinTracked_snd_le
          (fun u2 : Fin r =>
            computeGHatMantissaEntryTracked smul w q S_ghat N_erf cFixed sqrtPiFixed (u2.val : ℤ) r)
          (100000000 * S_term)
          (fun u2 => by
            simpa [S_term, mul_assoc] using
              computeGHatMantissaEntryTracked_snd_le smul w q S_ghat N_erf
                (le_refl w) hq1 hS_ghat hNerf cFixed sqrtPiFixed (u2.val : ℤ) r
                (scaledSubMulCost M_mul q) hsmul)
      have hc1 : c1Tbl.2 ≤ r * (100000000 * S_term) + r + 1 :=
        memoizeFinTracked_snd_le
          (fun u2 : Fin r =>
            computeGHatMantissaEntryTracked smul w q S_ghat N_erf cFixed sqrtPiFixed
              ((r : ℤ) - (u2.val : ℤ)) r)
          (100000000 * S_term)
          (fun u2 => by
            simpa [S_term, mul_assoc] using
              computeGHatMantissaEntryTracked_snd_le smul w q S_ghat N_erf
                (le_refl w) hq1 hS_ghat hNerf cFixed sqrtPiFixed ((r : ℤ) - (u2.val : ℤ)) r
                (scaledSubMulCost M_mul q) hsmul)
      have hchild : child.2 ≤ 150000000 * scheduleTreeGenOps (scaledSubMulCost M_mul) (k2Ell K) pC :=
        ih (k2Ell K) hk2_lt pC (childScheduleBIn K p B_in)
      have hentries : scheduleNodeTableEntries K p = t1 * (2 * m1 + 1) + 4 * r := rfl
      have hS_pos : 120 ≤ S_term := by
        dsimp [S_term, scheduleSeriesTerms]
        exact le_trans (Nat.le_mul_of_pos_right 120 (by omega))
          (le_trans (Nat.le_mul_of_pos_right _ (by omega))
            (Nat.le_mul_of_pos_right _ (by omega)))
      set A_tap := t1 * (2 * m1 + 1)
      have hent_pos : 1 ≤ A_tap + 4 * r := by omega
      have hdom : S_term ≤ A_tap * S_term + 4 * (r * S_term) := by
        have h1 : S_term ≤ (A_tap + 4 * r) * S_term := Nat.le_mul_of_pos_left _ hent_pos
        have h2 : (A_tap + 4 * r) * S_term = A_tap * S_term + 4 * (r * S_term) := by ring
        omega
      have hA_S : A_tap ≤ A_tap * S_term := Nat.le_mul_of_pos_right _ (by omega)
      have hr_S : r ≤ r * S_term := Nat.le_mul_of_pos_right _ (by omega)
      have htap' : tapTbl.2 ≤ 50000000 * (A_tap * S_term) + A_tap + 1 := by
        have : t1 * ((2 * m1 + 1) * (50000000 * S_term)) = 50000000 * (A_tap * S_term) := by dsimp [A_tap]; ring
        omega
      have hr25 : r * (25000000 * S_term) = 25000000 * (r * S_term) := by ring
      have hr100 : r * (100000000 * S_term) = 100000000 * (r * S_term) := by ring
      rw [hr25] at hpre hpost
      rw [hr100] at hc0 hc1
      have hrhs :
          scheduleNodeTableEntries K p * scheduleSeriesTerms q * (q + scaledSubMulCost M_mul q) =
            A_tap * S_term + 4 * (r * S_term) := by
        rw [hentries]; dsimp [S_term, A_tap]; ring
      rw [hrhs]
      dsimp only [pC] at hchild ⊢
      clear_value piRoot piTap l2Tap l2TapFixed l2GHat l2GHatFixed cBoundSq cBound cRaw cFixed
        B_erf N_erf pi2S sqrtPiRaw sqrtPiFixed tapTbl preTbl postTbl c0Tbl c1Tbl child S_term A_tap
      omega
    · dsimp only
      set qBase := qBaseEll K p
      set wLeaf := 100 * qBase
      have hqBase : p + 4 ≤ qBase := by unfold qBase qBaseEll; omega
      have hqBase4 : 4 ≤ qBase := by omega
      have hqBase1 : 1 ≤ qBase := by omega
      have hwLeaf_le : wLeaf ≤ 1000 * qBase := by unfold wLeaf; omega
      have hwLeaf1 : 1 ≤ wLeaf := by unfold wLeaf; omega
      have h2K : 1 ≤ 2 ^ K := Nat.one_le_two_pow
      have hsmulLeaf : ∀ x y : ℤ,
          (signedMulFromTrackedBitMul wLeaf (subMulBits wLeaf) x y).2 ≤
            scaledSubMulCost M_mul qBase + 8 * wLeaf + 10 :=
        signedMulFromTrackedBitMul_snd_le wLeaf (subMulBits wLeaf) (scaledSubMulCost M_mul qBase)
          (fun xs ys => le_trans (hM wLeaf xs ys hwLeaf1) (le_scaledSubMulCost_hundred M_mul qBase))
      have hpiLeaf0 := approxPiFixedTracked_snd_le wLeaf (qBase + 10)
      have hleafTbl :
          (memoizeFinTracked (fun u : Fin (2 ^ K) =>
            expTwoPiIFixedWithMulTracked (signedMulFromTrackedBitMul wLeaf (subMulBits wLeaf))
              wLeaf qBase (approxPiFixedTracked wLeaf (qBase + 10)).1
              (u.val : ℤ) (2 ^ K))).2 ≤
            2 ^ K * (25000000 * (scheduleSeriesTerms qBase * (qBase + scaledSubMulCost M_mul qBase))) +
              2 ^ K + 1 :=
        memoizeFinTracked_snd_le _
          (25000000 * (scheduleSeriesTerms qBase * (qBase + scaledSubMulCost M_mul qBase)))
          (fun u => by
            simpa [mul_assoc] using
              expTwoPiIFixedWithMulTracked_snd_le _ wLeaf qBase hwLeaf_le hqBase1 _ (u.val : ℤ) (2 ^ K)
                (scaledSubMulCost M_mul qBase) hsmulLeaf)
      refine le_trans (Nat.add_le_add (Nat.add_le_add hpiLeaf0 hleafTbl) le_rfl) ?_
      set S_leaf := scheduleSeriesTerms qBase * (qBase + scaledSubMulCost M_mul qBase)
      have hpi_bound :
          (qBase + 10 + 4) * (70 * (wLeaf + 4 * (qBase + 10) + 20) * (wLeaf + 4 * (qBase + 10) + 20)) +
            wLeaf + 24 + 3 ≤ 10000000 * S_leaf := by
        have h1 : qBase + 10 + 4 ≤ 4 * (qBase + 1) := by omega
        have h2 : 70 * (wLeaf + 4 * (qBase + 10) + 20) * (wLeaf + 4 * (qBase + 10) + 20) + wLeaf + 27 ≤
            2000000 * ((qBase + 1) * (qBase + 1)) := by
          dsimp [wLeaf]; nlinarith only [hqBase4]
        have h3 : (qBase + 10 + 4) * (70 * (wLeaf + 4 * (qBase + 10) + 20) * (wLeaf + 4 * (qBase + 10) + 20)) +
            wLeaf + 24 + 3 ≤ 8000000 * ((qBase + 1) * ((qBase + 1) * (qBase + 1))) := by
          have hm := Nat.mul_le_mul h1 h2
          have hr : (4 * (qBase + 1)) * (2000000 * ((qBase + 1) * (qBase + 1))) =
              8000000 * ((qBase + 1) * ((qBase + 1) * (qBase + 1))) := by ring
          rw [hr] at hm
          nlinarith only [hm, hqBase4]
        have hq3_le : (qBase + 1) * ((qBase + 1) * (qBase + 1)) ≤
            2 * ((qBase + 1) * (qBase + 1) * (qBase + scaledSubMulCost M_mul qBase)) := by
          have : qBase + 1 ≤ 2 * (qBase + scaledSubMulCost M_mul qBase) := by omega
          calc (qBase + 1) * ((qBase + 1) * (qBase + 1))
              = ((qBase + 1) * (qBase + 1)) * (qBase + 1) := by ring
            _ ≤ ((qBase + 1) * (qBase + 1)) * (2 * (qBase + scaledSubMulCost M_mul qBase)) :=
                Nat.mul_le_mul_left _ this
            _ = 2 * ((qBase + 1) * (qBase + 1) * (qBase + scaledSubMulCost M_mul qBase)) := by ring
        have hS_eq : 10000000 * S_leaf = 1200000000 * ((qBase + 1) * (qBase + 1) * (qBase + scaledSubMulCost M_mul qBase)) := by
          dsimp [S_leaf, scheduleSeriesTerms]; ring
        rw [hS_eq]
        clear_value qBase wLeaf S_leaf
        exact le_trans h3 (le_trans (Nat.mul_le_mul_left 8000000 hq3_le)
          (by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by norm_num)))
      have hS_pos : 120 ≤ S_leaf := by
        dsimp [S_leaf, scheduleSeriesTerms]
        exact le_trans (Nat.le_mul_of_pos_right 120 (by omega))
          (le_trans (Nat.le_mul_of_pos_right _ (by omega))
            (Nat.le_mul_of_pos_right _ (by omega)))
      have hdom : S_leaf ≤ 2 ^ K * S_leaf := Nat.le_mul_of_pos_left _ h2K
      have h2K_le : 2 ^ K ≤ 2 ^ K * S_leaf := Nat.le_mul_of_pos_right _ (by omega)
      have hrhs :
          2 ^ K * scheduleSeriesTerms qBase * (qBase + scaledSubMulCost M_mul qBase) =
            2 ^ K * S_leaf := by
        dsimp [S_leaf]
        ring
      have h25000000 : 2 ^ K * (25000000 * S_leaf) = 25000000 * (2 ^ K * S_leaf) := by ring
      rw [hrhs, h25000000]
      clear_value S_leaf
      linarith only [hpi_bound, hdom, h2K_le, hS_pos]

theorem baseRadix2FFTFixedWithMulTracked_snd_le (smulTracked : ℤ → ℤ → CostM ℤ) (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (M : ℕ) (hM : ∀ x y : ℤ, (smulTracked x y).2 ≤ M + 48 * qBaseEll K p + 10) :
    (baseRadix2FFTFixedWithMulTracked smulTracked K p leafTwiddles xFixed).2 ≤
      250 * leafDFTOps K p (fun _ => M) := by
  unfold baseRadix2FFTFixedWithMulTracked leafDFTOps
  dsimp only
  set xBase := memoizeFinTracked (fun j : Fin (2 ^ K) =>
    FixedComplex.rescaleTracked (qBaseEll K p) (xFixed j))
  set yBase := radix2FFT1DFixedWithMulTracked smulTracked K (qBaseEll K p) leafTwiddles K (le_refl K) xBase.1
  set out := memoizeFinTracked (fun u : Fin (2 ^ K) =>
    FixedComplex.rescaleTracked (p + 2) (yBase.1 u))
  have hqBase : p + 4 ≤ qBaseEll K p := by unfold qBaseEll; omega
  have hqBase4 : 4 ≤ qBaseEll K p := by unfold qBaseEll; omega
  have h2K : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hx : xBase.2 ≤ 2 ^ K * (2 * (p + 2 + qBaseEll K p) + 4) + 2 ^ K + 1 :=
    memoizeFinTracked_snd_le
      (fun j : Fin (2 ^ K) => FixedComplex.rescaleTracked (qBaseEll K p) (xFixed j))
      (2 * (p + 2 + qBaseEll K p) + 4) (fun _ => le_rfl)
  have hy0 := radix2FFT1DFixedWithMulTracked_snd_le smulTracked K (qBaseEll K p) leafTwiddles
    (M + 48 * qBaseEll K p + 10) hM K (le_refl K) xBase.1
  have hy : yBase.2 ≤ K * 2 ^ K * (4 * (M + 48 * qBaseEll K p + 10) + 12 * qBaseEll K p + 22) + 5 * 2 ^ K :=
    le_trans hy0 (Nat.sub_le _ 3)
  have hout : out.2 ≤ 2 ^ K * (2 * (qBaseEll K p + (p + 2)) + 4) + 2 ^ K + 1 :=
    memoizeFinTracked_snd_le
      (fun u : Fin (2 ^ K) => FixedComplex.rescaleTracked (p + 2) (yBase.1 u))
      (2 * (qBaseEll K p + (p + 2)) + 4) (fun _ => le_rfl)
  clear_value xBase yBase out
  have hx' : xBase.2 ≤ 5 * (2 ^ K * qBaseEll K p) := by
    calc xBase.2
        ≤ 2 ^ K * (2 * (p + 2 + qBaseEll K p) + 4) + 2 ^ K + 1 := hx
      _ ≤ 2 ^ K * (4 * qBaseEll K p) + 2 ^ K + 2 ^ K :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) le_rfl) h2K
      _ = 4 * (2 ^ K * qBaseEll K p) + 2 ^ K * 2 := by ring
      _ ≤ 4 * (2 ^ K * qBaseEll K p) + 2 ^ K * qBaseEll K p :=
          Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (by omega))
      _ = 5 * (2 ^ K * qBaseEll K p) := by ring
  have hout' : out.2 ≤ 5 * (2 ^ K * qBaseEll K p) := by
    calc out.2
        ≤ 2 ^ K * (2 * (qBaseEll K p + (p + 2)) + 4) + 2 ^ K + 1 := hout
      _ ≤ 2 ^ K * (4 * qBaseEll K p) + 2 ^ K + 2 ^ K :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) le_rfl) h2K
      _ = 4 * (2 ^ K * qBaseEll K p) + 2 ^ K * 2 := by ring
      _ ≤ 4 * (2 ^ K * qBaseEll K p) + 2 ^ K * qBaseEll K p :=
          Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (by omega))
      _ = 5 * (2 ^ K * qBaseEll K p) := by ring
  have hy' :
      yBase.2 ≤ 4 * (K * 2 ^ K * M) + 220 * (K * 2 ^ K * qBaseEll K p) + 2 * (2 ^ K * qBaseEll K p) := by
    calc yBase.2
        ≤ K * 2 ^ K * (4 * (M + 48 * qBaseEll K p + 10) + 12 * qBaseEll K p + 22) + 5 * 2 ^ K := hy
      _ ≤ K * 2 ^ K * (4 * M + 220 * qBaseEll K p) + 2 ^ K * 8 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 4 * (K * 2 ^ K * M) + 220 * (K * 2 ^ K * qBaseEll K p) + 2 ^ K * (2 * 4) := by ring
      _ ≤ 4 * (K * 2 ^ K * M) + 220 * (K * 2 ^ K * qBaseEll K p) + 2 ^ K * (2 * qBaseEll K p) :=
          Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hqBase4))
      _ = 4 * (K * 2 ^ K * M) + 220 * (K * 2 ^ K * qBaseEll K p) + 2 * (2 ^ K * qBaseEll K p) := by ring
  have hdist : 250 * ((K + 1) * 2 ^ K * (qBaseEll K p + M)) =
      250 * (K * 2 ^ K * M) + 250 * (K * 2 ^ K * qBaseEll K p) +
        250 * (2 ^ K * qBaseEll K p) + 250 * (2 ^ K * M) := by ring
  rw [hdist]
  omega

/-- **Bottom-Up Step-Count Upper Bound for `computableFastDFTRecursiveWithMulTracked`
(`computableFastDFTRecursiveWithMulTracked_snd_le`)**:
For any tracked bit-list sub-multiplier `subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)`
whose `.2` cost at bit-width $w \ge 1$ is bounded by `M_mul w`, the bottom-up accumulated step count
`(computableFastDFTRecursiveWithMulTracked subMulBits (computeScheduleIntTree K p B_in) xFixed).2` is
bounded by `12000 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) K p B_in`. -/
theorem computableFastDFTRecursiveWithMulTracked_snd_le
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)) (M_mul : ℕ → ℕ)
    (hM : ∀ (w : ℕ) (xs ys : List Bool), 1 ≤ w → (subMulBits w xs ys).2 ≤ M_mul w) (K : ℕ) :
    ∀ (p B_in : ℕ) (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)),
      (computableFastDFTRecursiveWithMulTracked subMulBits
        (computeScheduleIntTree K p B_in) xFixed).2 ≤
        12000 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) K p B_in := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in xFixed
    rw [computeScheduleIntTree, fastDFTRecursiveSteps]
    split_ifs with hcond
    · have hK2 : 2 ≤ K := hcond.2
      have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      have hk1_pos : 1 ≤ k1Ell K := by unfold k1Ell; omega
      have hk2_pos : 1 ≤ k2Ell K := by unfold k2Ell; omega
      have hq_t1 : qChildEll K p ≤ 14 * t1Ell K :=
        qChildEll_le_fourteen_mul_t1Ell_of_internal hcond.1 hcond.2
      dsimp only
      set filterTap := memoizeFilterTap (computeM1Ell K p) (computeFilterTapFixedWithMul (· * ·) K p)
      set preTwistRoot := memoizeFin (fun k2 : Fin (rEll K) =>
        expTwoPiIFixedWithMul (· * ·) (qChildEll K p) (k2.val : ℤ) (2 * rEll K))
      set postTwistRoot := memoizeFin (fun k2 : Fin (rEll K) =>
        expTwoPiIFixedWithMul (· * ·) (qChildEll K p) (-(k2.val : ℤ)) (2 * rEll K))
      set c0Mantissa := memoizeFin (computePassbandC0MantissaWithMul (· * ·) K p)
      set c1Mantissa := memoizeFin (computePassbandC1MantissaWithMul (· * ·) K p)
      clear_value filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa
      unfold computableFastDFTRecursiveWithMulTracked
      dsimp only
      set m1 := computeM1Ell K p
      set B_slot := scheduleSlotBits K p B_in m1
      set W_tilde := foldedHalfWidth m1 (rEll K)
      set wKron := kroneckerPackedBitLength W_tilde B_slot
      set smulChild := signedMulFromTrackedBitMul (10 * qChildEll K p) (subMulBits (10 * qChildEll K p))
      have ht1_pos : 1 ≤ t1Ell K := t1Ell_pos K
      have hr_ge2 : 2 ≤ rEll K := by
        unfold rEll
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ k2Ell K := Nat.pow_le_pow_right (by norm_num) hk2_pos
      have hr_pos : 0 < rEll K := by omega
      haveI : NeZero (t1Ell K) := ⟨ne_of_gt ht1_pos⟩
      have ht1r : t1Ell K * rEll K = 2 ^ K := t1Ell_mul_rEll K
      have hqChild_eq : qChildEll K p = p + 2 * K + 14 := qChildEll_eq K p
      have hqChild14 : 14 ≤ qChildEll K p := by omega
      have hqChild1 : 1 ≤ qChildEll K p := by omega
      have hm1_pos : 1 ≤ m1 := computeM1Ell_pos K p
      have hm1_le : m1 ≤ qChildEll K p := by
        have h1 := computeM1Ell_le_pChildEll K p
        have h2 := pChildEll_eq K p
        omega
      have hW_pos : 1 ≤ W_tilde := by
        unfold W_tilde foldedHalfWidth
        exact le_min hm1_pos (by omega)
      have hB_slot_ge : qChildEll K p ≤ B_slot := by
        unfold B_slot scheduleSlotBits
        rw [kroneckerSlotBitsRaw, kroneckerSlotBitsWithIn]
        omega
      have hwKron_eq : wKron = 3 * W_tilde * B_slot := rfl
      have hwKron1 : 1 ≤ wKron := by nlinarith only [hW_pos, hB_slot_ge, hqChild1, hwKron_eq]
      have hnumB_pos : 1 ≤ numBlocks (rEll K) W_tilde := by
        have h0 : 0 < numBlocks (rEll K) W_tilde := by
          simpa using div_lt_numBlocks (j := 0) hW_pos hr_pos
        omega
      have hsubKron : ∀ xs ys : List Bool, (subMulBits wKron xs ys).2 ≤ scaledSubMulCost M_mul wKron :=
        fun xs ys => le_trans (hM wKron xs ys hwKron1) (le_scaledSubMulCost_one M_mul wKron)
      have hsmulChild : ∀ x y : ℤ,
          (smulChild x y).2 ≤ scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10 := by
        have h0 : ∀ x y : ℤ,
            (smulChild x y).2 ≤ scaledSubMulCost M_mul (qChildEll K p) + 8 * (10 * qChildEll K p) + 10 :=
          signedMulFromTrackedBitMul_snd_le (10 * qChildEll K p)
            (subMulBits (10 * qChildEll K p)) (scaledSubMulCost M_mul (qChildEll K p))
            (fun xs ys => le_trans (hM (10 * qChildEll K p) xs ys (by omega))
              (le_scaledSubMulCost_ten M_mul (qChildEll K p)))
        intro x y
        have hxy := h0 x y
        omega
      set U_gathered := memoizeFin2Tracked (fun (j1 : Fin (t1Ell K)) (j2 : Fin (rEll K)) =>
        let rs := FixedComplex.rescaleTracked (qChildEll K p)
          (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K) xFixed j1 j2)
        (rs.1, rs.2 + (2 * qChildEll K p + 4) * (k1Ell K + 1)))
      set U_spreadFixed := kroneckerMatrixSpreadFixedWithMulTracked (subMulBits wKron)
        (t1Ell K) (rEll K) m1 B_slot (qChildEll K p) (qChildEll K p) hr_pos U_gathered.1 filterTap
      set U_preFixed := memoizeFin2Tracked (fun (j1 : Fin (t1Ell K)) (k2 : Fin (rEll K)) =>
        FixedComplex.mulRoundedWithTracked smulChild (preTwistRoot k2) (U_spreadFixed.1 j1 k2))
      set Q_synFixed := radix2SyntheticFFTFixedTracked (k1Ell K) (c1Ell K) U_preFixed.1
      set Q_postFixed := memoizeFin2Tracked (fun (v1 : Fin (t1Ell K)) (k2 : Fin (rEll K)) =>
        FixedComplex.mulRoundedWithTracked smulChild (postTwistRoot k2) (Q_synFixed.1 v1 k2))
      set Q_hatRows := memoizeFinTracked (fun v1 : Fin (t1Ell K) =>
        computableFastDFTRecursiveWithMulTracked subMulBits
          (computeScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
          (Q_postFixed.1 v1))
      set Y_matFixed := memoizeFin2Tracked (fun (m : Fin (t1Ell K)) (u2 : Fin (rEll K)) =>
        (oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hatRows.1 m u2,
          (4 * qChildEll K p + 8) * (k1Ell K + 1)))
      set altFixed := nyquistModeSumFixedTracked K p xFixed
      set Z_colsRows := memoizeFinTracked (fun u2 : Fin (rEll K) =>
        if u2.val = rEll K / 2 then
          nyquistColumnSolveFixedWithMulTracked smulChild (c0Mantissa u2)
            (fun m => Y_matFixed.1 m u2) altFixed.1
        else
          cyclicBidiagPrevSolveFixedWithMulTracked smulChild (c0Mantissa u2) (c1Mantissa u2)
            (fun m => Y_matFixed.1 m u2))
      set Z_matFixed := memoizeFin2Tracked (fun (u1 : Fin (t1Ell K)) (u2 : Fin (rEll K)) =>
        (Z_colsRows.1 u2 u1, (2 * qChildEll K p + 4) * (k1Ell K + 1)))
      set outVec := memoizeFinTracked (fun u : Fin (2 ^ K) =>
        let rs := FixedComplex.rescaleTracked (p + 2) (freqScatter (t1Ell K) (rEll K) ht1r.symm Z_matFixed.1 u)
        (rs.1, rs.2 + (2 * qChildEll K p + 4) * (k1Ell K + 1)))
      change U_gathered.2 + U_spreadFixed.2 + U_preFixed.2 + Q_synFixed.2 + Q_postFixed.2 +
          Q_hatRows.2 + Y_matFixed.2 + altFixed.2 + Z_colsRows.2 + Z_matFixed.2 + outVec.2 ≤
        12000 * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
          stepFixedPointMuls K p B_in (scaledSubMulCost M_mul) +
          t1Ell K * fastDFTRecursiveSteps (scaledSubMulCost M_mul)
            (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) +
          step3DeconvOps K p)
      have ht1_le_r : t1Ell K ≤ rEll K := by
        unfold t1Ell rEll k1Ell k2Ell
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hr_le_nb : rEll K ≤ numBlocks (rEll K) W_tilde * W_tilde := by
        have hdiv : (rEll K - 1) / W_tilde < numBlocks (rEll K) W_tilde :=
          div_lt_numBlocks (j := rEll K - 1) hW_pos (by omega)
        have hmod := Nat.div_add_mod (rEll K - 1) W_tilde
        have hlt := Nat.mod_lt (rEll K - 1) hW_pos
        have hle : (rEll K - 1) / W_tilde + 1 ≤ numBlocks (rEll K) W_tilde := hdiv
        have hmul := Nat.mul_le_mul_right W_tilde hle
        have hmul' : W_tilde * ((rEll K - 1) / W_tilde) + W_tilde =
            ((rEll K - 1) / W_tilde + 1) * W_tilde := by ring
        omega
      have hq_le_nb : qChildEll K p ≤ 14 * (numBlocks (rEll K) W_tilde * W_tilde) :=
        hq_t1.trans ((Nat.mul_le_mul_left 14 ht1_le_r).trans (Nat.mul_le_mul_left 14 hr_le_nb))
      have hm1_le_nb : m1 ≤ 14 * (numBlocks (rEll K) W_tilde * W_tilde) :=
        hm1_le.trans hq_le_nb
      have hU_gath :
          U_gathered.2 ≤
            t1Ell K * (rEll K * (2 * (p + 2 + qChildEll K p) + 4 + (2 * qChildEll K p + 4) * (k1Ell K + 1))) +
              t1Ell K * rEll K + 1 :=
        memoizeFin2Tracked_snd_le _
          (2 * (p + 2 + qChildEll K p) + 4 + (2 * qChildEll K p + 4) * (k1Ell K + 1))
          (fun _ _ => le_rfl)
      have hU_spr0 :
          U_spreadFixed.2 ≤
            t1Ell K *
              (2 * (numBlocks (rEll K) W_tilde *
                    (scaledSubMulCost M_mul wKron + 9 * W_tilde * (B_slot + 4) + 10) +
                  3 * W_tilde * (B_slot + 4) + (2 * m1 + 2 * rEll K + 1) * (B_slot + 2) + 9) +
                rEll K * (2 * qChildEll K p + 2 * B_slot + 8) + 4) + 3 :=
        kroneckerMatrixSpreadFixedWithMulTracked_snd_le (subMulBits wKron)
          (t1Ell K) (rEll K) m1 B_slot (qChildEll K p) (qChildEll K p) hr_pos U_gathered.1 filterTap
          (scaledSubMulCost M_mul wKron) hsubKron
      have hspr_blk :
          numBlocks (rEll K) W_tilde *
            (scaledSubMulCost M_mul wKron + 9 * W_tilde * (B_slot + 4) + 10) ≤
          numBlocks (rEll K) W_tilde * (scaledSubMulCost M_mul wKron + 14 * (W_tilde * B_slot)) := by
        apply Nat.mul_le_mul_left
        nlinarith only [hW_pos, hB_slot_ge, hqChild14]
      have hspr_rem :
          3 * W_tilde * (B_slot + 4) + (2 * m1 + 2 * rEll K + 1) * (B_slot + 2) + 9 ≤
            75 * (numBlocks (rEll K) W_tilde * (W_tilde * B_slot)) := by
        have h1 : 3 * W_tilde * (B_slot + 4) + 9 ≤
            5 * (numBlocks (rEll K) W_tilde * (W_tilde * B_slot)) := by
          have ha : 3 * W_tilde * (B_slot + 4) + 9 ≤ 5 * (W_tilde * B_slot) := by
            nlinarith only [hW_pos, hB_slot_ge, hqChild14]
          have hb : W_tilde * B_slot ≤ numBlocks (rEll K) W_tilde * (W_tilde * B_slot) :=
            Nat.le_mul_of_pos_left _ hnumB_pos
          linarith only [ha, hb]
        have h2 : (2 * m1 + 2 * rEll K + 1) * (B_slot + 2) ≤
            70 * (numBlocks (rEll K) W_tilde * (W_tilde * B_slot)) := by
          have hnbW_pos : 1 ≤ numBlocks (rEll K) W_tilde * W_tilde := Nat.mul_pos hnumB_pos hW_pos
          have ha : 2 * m1 + 2 * rEll K + 1 ≤ 35 * (numBlocks (rEll K) W_tilde * W_tilde) := by
            omega
          have hb : B_slot + 2 ≤ 2 * B_slot := by omega
          have hc := Nat.mul_le_mul ha hb
          nlinarith only [hc]
        linarith only [h1, h2]
      have hr_Bslot :
          rEll K * (2 * B_slot) ≤ 2 * (numBlocks (rEll K) W_tilde * (W_tilde * B_slot)) := by
        nlinarith only [hr_le_nb]
      have hspr_inner :
          2 * (numBlocks (rEll K) W_tilde *
                (scaledSubMulCost M_mul wKron + 9 * W_tilde * (B_slot + 4) + 10) +
              3 * W_tilde * (B_slot + 4) + (2 * m1 + 2 * rEll K + 1) * (B_slot + 2) + 9) +
            rEll K * (2 * qChildEll K p + 2 * B_slot + 8) + 4 ≤
          2 * (numBlocks (rEll K) W_tilde * scaledSubMulCost M_mul wKron) +
            180 * (numBlocks (rEll K) W_tilde * (W_tilde * B_slot)) +
            2 * (rEll K * qChildEll K p) + 14 * rEll K := by
        linarith only [hspr_blk, hspr_rem, hr_Bslot, hr_ge2]
      have hU_spr :
          U_spreadFixed.2 ≤
            2 * (t1Ell K * numBlocks (rEll K) W_tilde * scaledSubMulCost M_mul wKron) +
              180 * (t1Ell K * numBlocks (rEll K) W_tilde * W_tilde * B_slot) +
              2 * (t1Ell K * rEll K * qChildEll K p) + 14 * (t1Ell K * rEll K) + 3 := by
        have hmul := Nat.mul_le_mul_left (t1Ell K) hspr_inner
        have hmul_eq :
             t1Ell K * (2 * (numBlocks (rEll K) W_tilde * scaledSubMulCost M_mul wKron) +
              180 * (numBlocks (rEll K) W_tilde * (W_tilde * B_slot)) +
              2 * (rEll K * qChildEll K p) + 14 * rEll K) =
            2 * (t1Ell K * numBlocks (rEll K) W_tilde * scaledSubMulCost M_mul wKron) +
              180 * (t1Ell K * numBlocks (rEll K) W_tilde * W_tilde * B_slot) +
              2 * (t1Ell K * rEll K * qChildEll K p) + 14 * (t1Ell K * rEll K) := by ring
        rw [hmul_eq] at hmul
        linarith only [hU_spr0, hmul]
      have hU_pre :
          U_preFixed.2 ≤
            t1Ell K * (rEll K * (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8)) +
              t1Ell K * rEll K + 1 :=
        memoizeFin2Tracked_snd_le _ (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8)
          (fun j1 k2 => FixedComplex.mulRoundedWithTracked_snd_le smulChild
            (preTwistRoot k2) (U_spreadFixed.1 j1 k2) (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) hsmulChild)
      have hQ_syn :
          Q_synFixed.2 ≤ k1Ell K * t1Ell K * (rEll K * (8 * qChildEll K p + 18)) + 5 * t1Ell K :=
        le_trans (radix2SyntheticFFTFixedTracked_snd_le (k1Ell K) (c1Ell K) U_preFixed.1)
          (Nat.sub_le _ 3)
      have hQ_post :
          Q_postFixed.2 ≤
            t1Ell K * (rEll K * (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8)) +
              t1Ell K * rEll K + 1 :=
        memoizeFin2Tracked_snd_le _ (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8)
          (fun v1 k2 => FixedComplex.mulRoundedWithTracked_snd_le smulChild
            (postTwistRoot k2) (Q_synFixed.1 v1 k2) (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) hsmulChild)
      have hQ_hat : Q_hatRows.2 ≤
          t1Ell K * (12000 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) +
            t1Ell K + 1 :=
        memoizeFinTracked_snd_le _
          (12000 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
          (fun v1 => ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in) (Q_postFixed.1 v1))
      have hY_mat :
          Y_matFixed.2 ≤
            t1Ell K * (rEll K * ((4 * qChildEll K p + 8) * (k1Ell K + 1))) + t1Ell K * rEll K + 1 :=
        memoizeFin2Tracked_snd_le _ ((4 * qChildEll K p + 8) * (k1Ell K + 1)) (fun _ _ => le_rfl)
      have halt0 : altFixed.2 ≤ 10 * (2 ^ K) * qChildEll K p :=
        nyquistModeSumFixedTracked_snd_le K p xFixed
      have hcol_q2 : 6000 * qChildEll K p * qChildEll K p ≤ t1Ell K * (84000 * qChildEll K p) := by
        calc 6000 * qChildEll K p * qChildEll K p
            = 6000 * (qChildEll K p * qChildEll K p) := by ring
          _ ≤ 6000 * ((14 * t1Ell K) * qChildEll K p) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq_t1)
          _ = t1Ell K * (84000 * qChildEll K p) := by ring
      have hZ_cols :
          Z_colsRows.2 ≤
            rEll K * (t1Ell K * (7 * scaledSubMulCost M_mul (qChildEll K p) + 84650 * qChildEll K p)) + rEll K + 1 :=
        memoizeFinTracked_snd_le _
          (t1Ell K * (7 * scaledSubMulCost M_mul (qChildEll K p) + 84650 * qChildEll K p))
          (fun u2 => by
            split_ifs
            · have h0 := nyquistColumnSolveFixedWithMulTracked_snd_le smulChild ht1_pos hqChild14
                (c0Mantissa u2) (fun m => Y_matFixed.1 m u2) altFixed.1
                (scaledSubMulCost M_mul (qChildEll K p)) hsmulChild
              linarith only [h0, hcol_q2]
            · have h0 := cyclicBidiagPrevSolveFixedWithMulTracked_snd_le smulChild hqChild14
                (c0Mantissa u2) (c1Mantissa u2) (fun m => Y_matFixed.1 m u2)
                (scaledSubMulCost M_mul (qChildEll K p)) hsmulChild
              linarith only [h0, hcol_q2])
      have hZ_mat :
          Z_matFixed.2 ≤
            t1Ell K * (rEll K * ((2 * qChildEll K p + 4) * (k1Ell K + 1))) + t1Ell K * rEll K + 1 :=
        memoizeFin2Tracked_snd_le _ ((2 * qChildEll K p + 4) * (k1Ell K + 1)) (fun _ _ => le_rfl)
      have hout0 :
          outVec.2 ≤
            (2 ^ K) * (2 * (qChildEll K p + (p + 2)) + 4 + (2 * qChildEll K p + 4) * (k1Ell K + 1)) +
              2 ^ K + 1 :=
        memoizeFinTracked_snd_le _
          (2 * (qChildEll K p + (p + 2)) + 4 + (2 * qChildEll K p + 4) * (k1Ell K + 1))
          (fun _ => le_rfl)
      clear_value U_gathered U_spreadFixed U_preFixed Q_synFixed Q_postFixed Q_hatRows
        Y_matFixed altFixed Z_colsRows Z_matFixed outVec smulChild
      have hTR_pos : 1 ≤ t1Ell K * rEll K := by nlinarith only [ht1_pos, hr_ge2]
      have hU_gath' :
          U_gathered.2 ≤
            3 * (k1Ell K * (t1Ell K * rEll K) * qChildEll K p) +
              8 * (t1Ell K * rEll K * qChildEll K p) := by
        have hstep :
            2 * (p + 2 + qChildEll K p) + 4 + (2 * qChildEll K p + 4) * (k1Ell K + 1) ≤
              3 * (k1Ell K * qChildEll K p) + 7 * qChildEll K p := by
          nlinarith only [hqChild_eq, hqChild14, hk1_pos]
        have hm := Nat.mul_le_mul_left (t1Ell K * rEll K) hstep
        nlinarith only [hU_gath, hm, hTR_pos, hqChild14]
      have hU_spr' :
          U_spreadFixed.2 ≤
            2 * (t1Ell K * numBlocks (rEll K) W_tilde * scaledSubMulCost M_mul wKron) +
              180 * (t1Ell K * numBlocks (rEll K) W_tilde * W_tilde * B_slot) +
              4 * (t1Ell K * rEll K * qChildEll K p) := by
        have h14 : 14 * (t1Ell K * rEll K) + 3 ≤ 2 * (t1Ell K * rEll K * qChildEll K p) := by
          calc 14 * (t1Ell K * rEll K) + 3
              ≤ 14 * (t1Ell K * rEll K) + 14 * (t1Ell K * rEll K) :=
                Nat.add_le_add le_rfl (by linarith only [hTR_pos])
            _ = (t1Ell K * rEll K) * 28 := by ring
            _ ≤ (t1Ell K * rEll K) * (2 * qChildEll K p) := Nat.mul_le_mul_left _ (by omega)
            _ = 2 * (t1Ell K * rEll K * qChildEll K p) := by ring
        linarith only [hU_spr, h14]
      have hU_pre' :
          U_preFixed.2 ≤
            4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
              335 * (t1Ell K * rEll K * qChildEll K p) := by
        calc U_preFixed.2
            ≤ t1Ell K * (rEll K * (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8)) +
                t1Ell K * rEll K + 1 := hU_pre
          _ = (t1Ell K * rEll K) * (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8) +
                t1Ell K * rEll K + 1 := by ring
          _ ≤ (t1Ell K * rEll K) * (4 * scaledSubMulCost M_mul (qChildEll K p) + 334 * qChildEll K p) +
                t1Ell K * rEll K + t1Ell K * rEll K :=
              Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) le_rfl) hTR_pos
          _ = 4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                334 * (t1Ell K * rEll K * qChildEll K p) + (t1Ell K * rEll K) * 2 := by ring
          _ ≤ 4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                334 * (t1Ell K * rEll K * qChildEll K p) + (t1Ell K * rEll K) * qChildEll K p :=
              Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (by omega))
          _ = 4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                335 * (t1Ell K * rEll K * qChildEll K p) := by ring
      have hQ_syn' :
          Q_synFixed.2 ≤
            10 * (k1Ell K * (t1Ell K * rEll K) * qChildEll K p) +
              (t1Ell K * rEll K * qChildEll K p) := by
        have h5t1 : 5 * t1Ell K ≤ (t1Ell K * rEll K) * qChildEll K p := by
          calc 5 * t1Ell K = t1Ell K * (1 * 5) := by ring
            _ ≤ t1Ell K * (rEll K * qChildEll K p) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
            _ = (t1Ell K * rEll K) * qChildEll K p := by ring
        calc Q_synFixed.2
            ≤ k1Ell K * t1Ell K * (rEll K * (8 * qChildEll K p + 18)) + 5 * t1Ell K := hQ_syn
          _ = (k1Ell K * (t1Ell K * rEll K)) * (8 * qChildEll K p + 18) + 5 * t1Ell K := by ring
          _ ≤ (k1Ell K * (t1Ell K * rEll K)) * (10 * qChildEll K p) +
                (t1Ell K * rEll K) * qChildEll K p :=
              Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) h5t1
          _ = 10 * (k1Ell K * (t1Ell K * rEll K) * qChildEll K p) +
                (t1Ell K * rEll K * qChildEll K p) := by ring
      have hQ_post' :
          Q_postFixed.2 ≤
            4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
              335 * (t1Ell K * rEll K * qChildEll K p) := by
        calc Q_postFixed.2
            ≤ t1Ell K * (rEll K * (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8)) +
                t1Ell K * rEll K + 1 := hQ_post
          _ = (t1Ell K * rEll K) * (4 * (scaledSubMulCost M_mul (qChildEll K p) + 80 * qChildEll K p + 10) + 6 * qChildEll K p + 8) +
                t1Ell K * rEll K + 1 := by ring
          _ ≤ (t1Ell K * rEll K) * (4 * scaledSubMulCost M_mul (qChildEll K p) + 334 * qChildEll K p) +
                t1Ell K * rEll K + t1Ell K * rEll K :=
              Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) le_rfl) hTR_pos
          _ = 4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                334 * (t1Ell K * rEll K * qChildEll K p) + (t1Ell K * rEll K) * 2 := by ring
          _ ≤ 4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                334 * (t1Ell K * rEll K * qChildEll K p) + (t1Ell K * rEll K) * qChildEll K p :=
              Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (by omega))
          _ = 4 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                335 * (t1Ell K * rEll K * qChildEll K p) := by ring
      have hQ_hat' :
          Q_hatRows.2 ≤
            12000 * (t1Ell K * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) +
              (t1Ell K * rEll K * qChildEll K p) := by
        have ht1_le : t1Ell K + 1 ≤ t1Ell K * rEll K * qChildEll K p := by
          calc t1Ell K + 1 ≤ t1Ell K * 2 := by omega
            _ = t1Ell K * (2 * 1) := by ring
            _ ≤ t1Ell K * (rEll K * qChildEll K p) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul hr_ge2 hqChild1)
            _ = t1Ell K * rEll K * qChildEll K p := by ring
        calc Q_hatRows.2
            ≤ t1Ell K * (12000 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) +
                t1Ell K + 1 := hQ_hat
          _ = 12000 * (t1Ell K * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) +
                (t1Ell K + 1) := by ring
          _ ≤ 12000 * (t1Ell K * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) +
                (t1Ell K * rEll K * qChildEll K p) := Nat.add_le_add le_rfl ht1_le
      have hY_mat' :
          Y_matFixed.2 ≤
            5 * (k1Ell K * (t1Ell K * rEll K) * qChildEll K p) +
              6 * (t1Ell K * rEll K * qChildEll K p) := by
        have hstep : (4 * qChildEll K p + 8) * (k1Ell K + 1) ≤
            5 * (k1Ell K * qChildEll K p) + 5 * qChildEll K p := by
          nlinarith only [hqChild14, hk1_pos]
        have hm := Nat.mul_le_mul_left (t1Ell K * rEll K) hstep
        nlinarith only [hY_mat, hm, hTR_pos, hqChild14]
      have halt' : altFixed.2 ≤ 10 * (t1Ell K * rEll K * qChildEll K p) := by
        calc altFixed.2 ≤ 10 * (2 ^ K) * qChildEll K p := halt0
          _ = 10 * (t1Ell K * rEll K * qChildEll K p) := by rw [← ht1r]; ring
      have hZ_cols' :
          Z_colsRows.2 ≤
            7 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
              84651 * (t1Ell K * rEll K * qChildEll K p) := by
        have hr_le : rEll K + 1 ≤ t1Ell K * rEll K * qChildEll K p := by
          calc rEll K + 1 ≤ 1 * rEll K * 2 := by omega
            _ ≤ t1Ell K * rEll K * qChildEll K p :=
                Nat.mul_le_mul (Nat.mul_le_mul_right _ ht1_pos) (by omega)
        calc Z_colsRows.2
            ≤ rEll K * (t1Ell K * (7 * scaledSubMulCost M_mul (qChildEll K p) + 84650 * qChildEll K p)) + rEll K + 1 := hZ_cols
          _ = 7 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                84650 * (t1Ell K * rEll K * qChildEll K p) + (rEll K + 1) := by ring
          _ ≤ 7 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                84650 * (t1Ell K * rEll K * qChildEll K p) + t1Ell K * rEll K * qChildEll K p :=
              Nat.add_le_add le_rfl hr_le
          _ = 7 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
                84651 * (t1Ell K * rEll K * qChildEll K p) := by ring
      have hZ_mat' :
          Z_matFixed.2 ≤
            3 * (k1Ell K * (t1Ell K * rEll K) * qChildEll K p) +
              4 * (t1Ell K * rEll K * qChildEll K p) := by
        have hstep : (2 * qChildEll K p + 4) * (k1Ell K + 1) ≤
            3 * (k1Ell K * qChildEll K p) + 3 * qChildEll K p := by
          nlinarith only [hqChild14, hk1_pos]
        have hm := Nat.mul_le_mul_left (t1Ell K * rEll K) hstep
        nlinarith only [hZ_mat, hm, hTR_pos, hqChild14]
      have hout' :
          outVec.2 ≤
            3 * (k1Ell K * (t1Ell K * rEll K) * qChildEll K p) +
              8 * (t1Ell K * rEll K * qChildEll K p) := by
        have hout0' :
            outVec.2 ≤
              (t1Ell K * rEll K) *
                (2 * (qChildEll K p + (p + 2)) + 4 + (2 * qChildEll K p + 4) * (k1Ell K + 1)) +
              (t1Ell K * rEll K) + 1 := by
          simpa only [ht1r] using hout0
        have hstep :
            2 * (qChildEll K p + (p + 2)) + 4 + (2 * qChildEll K p + 4) * (k1Ell K + 1) ≤
              3 * (k1Ell K * qChildEll K p) + 7 * qChildEll K p := by
          nlinarith only [hqChild_eq, hqChild14, hk1_pos]
        have hm := Nat.mul_le_mul_left (t1Ell K * rEll K) hstep
        nlinarith only [hout0', hm, hTR_pos, hqChild14]
      have hstep1_eq : step1SpreadOps K p B_in =
          2 * (t1Ell K * numBlocks (rEll K) W_tilde * (3 * W_tilde * B_slot)) := rfl
      have hstep2_eq : step2SyntheticFFTOps K p = (2 + k1Ell K) * (t1Ell K * rEll K) * qChildEll K p := by
        unfold step2SyntheticFFTOps; rw [← ht1r]
      have hmuls_eq : stepFixedPointMuls K p B_in (scaledSubMulCost M_mul) =
          2 * (t1Ell K * numBlocks (rEll K) W_tilde * scaledSubMulCost M_mul wKron) +
            16 * (t1Ell K * rEll K) * scaledSubMulCost M_mul (qChildEll K p) := by
        unfold stepFixedPointMuls; rw [← ht1r]
      have hstep3_eq : step3DeconvOps K p = 8 * (t1Ell K * rEll K) * qChildEll K p := by
        unfold step3DeconvOps; rw [← ht1r]
      have hrhs_expand :
          12000 * (step1SpreadOps K p B_in + step2SyntheticFFTOps K p +
            stepFixedPointMuls K p B_in (scaledSubMulCost M_mul) +
            t1Ell K * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in) +
            step3DeconvOps K p) =
          72000 * (t1Ell K * numBlocks (rEll K) W_tilde * W_tilde * B_slot) +
            24000 * (t1Ell K * numBlocks (rEll K) W_tilde * scaledSubMulCost M_mul wKron) +
            120000 * (t1Ell K * rEll K * qChildEll K p) +
            12000 * (k1Ell K * (t1Ell K * rEll K) * qChildEll K p) +
            192000 * (t1Ell K * rEll K * scaledSubMulCost M_mul (qChildEll K p)) +
            12000 * (t1Ell K * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)) := by
        rw [hstep1_eq, hstep2_eq, hmuls_eq, hstep3_eq]
        ring
      rw [hrhs_expand]
      omega
    · unfold computableFastDFTRecursiveWithMulTracked
      dsimp only
      set qBase := qBaseEll K p
      have hqBase1 : 1 ≤ qBase := by unfold qBase qBaseEll; omega
      have hsmulLeaf : ∀ x y : ℤ,
          (signedMulFromTrackedBitMul (6 * qBase) (subMulBits (6 * qBase)) x y).2 ≤
            scaledSubMulCost M_mul qBase + 48 * qBase + 10 := by
        have h0 := signedMulFromTrackedBitMul_snd_le (6 * qBase) (subMulBits (6 * qBase))
          (scaledSubMulCost M_mul qBase)
          (fun xs ys => le_trans (hM (6 * qBase) xs ys (by omega)) (le_scaledSubMulCost_six M_mul qBase))
        intro x y
        have hxy := h0 x y
        omega
      refine le_trans (baseRadix2FFTFixedWithMulTracked_snd_le _ K p _ xFixed
        (scaledSubMulCost M_mul qBase) hsmulLeaf) ?_
      unfold leafDFTOps
      dsimp only [qBase]
      omega

theorem mul_le_fastDFTRecursiveSteps (M_mul : ℕ → ℕ) (K p B_in : ℕ) :
    (2 ^ K) * (p + 4) ≤ fastDFTRecursiveSteps M_mul K p B_in := by
  rw [fastDFTRecursiveSteps]
  split_ifs with hcond
  · unfold step3DeconvOps
    have hq : p + 2 * K + 14 = qChildEll K p := (qChildEll_eq K p).symm
    have h1 : 2 ^ K * (p + 4) ≤ 8 * 2 ^ K * qChildEll K p := by
      rw [mul_assoc 8]
      exact le_trans (Nat.mul_le_mul_left (2 ^ K) (by omega))
        (Nat.le_mul_of_pos_left _ (by decide))
    omega
  · unfold leafDFTOps
    have hq : p + K + 4 = qBaseEll K p := rfl
    calc 2 ^ K * (p + 4)
        ≤ 2 ^ K * (qBaseEll K p + M_mul (qBaseEll K p)) :=
          Nat.mul_le_mul_left (2 ^ K) (by omega)
      _ = 1 * 2 ^ K * (qBaseEll K p + M_mul (qBaseEll K p)) := by ring
      _ ≤ (K + 1) * 2 ^ K * (qBaseEll K p + M_mul (qBaseEll K p)) := by
          gcongr; omega

theorem computableConvFromChunksWithMulTracked_snd_le
    (subMulBits : ℕ → List Bool → List Bool → CostM (List Bool)) (M_mul : ℕ → ℕ)
    (hM : ∀ (w : ℕ) (xs ys : List Bool), 1 ≤ w → (subMulBits w xs ys).2 ≤ M_mul w) (n : ℕ)
    (aChunks bChunks : Fin (rootR0 n) → ℕ) :
    (computableConvFromChunksWithMulTracked subMulBits n
      (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
      aChunks bChunks).2 ≤
      12100 * (2 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (rootK0 n) (rootP0 n)
        (levelScheduleBIn (rootK0 n) (rootP0 n) 0) +
        3 * rootR0 n * scaledSubMulCost M_mul (rootP0 n + 2)) := by
  unfold computableConvFromChunksWithMulTracked
  dsimp only
  set p0 := rootP0 n
  set B0 := levelScheduleBIn (rootK0 n) (rootP0 n) 0
  set smulRoot := signedMulFromTrackedBitMul (2 * (p0 + 2)) (subMulBits (2 * (p0 + 2)))
  set zFixed := memoizeFinTracked (fun j : Fin (rootR0 n) =>
    (packChunksFixed n (aChunks, bChunks) j, 2 * (p0 + 2) + 4))
  set Z_hat := computableFastDFTRecursiveWithMulTracked subMulBits
    (computeScheduleIntTree (rootK0 n) p0 B0) zFixed.1
  set W_conj := memoizeFinTracked (fun u : Fin (rootR0 n) =>
    let Zu := Z_hat.1 u
    let p_re_im := smulRoot (2 * Zu.re) Zu.im
    let p_im_sq := smulRoot Zu.im Zu.im
    let p_re_sq := smulRoot Zu.re Zu.re
    let r_re := roundShiftIntTracked p_re_im.1 (p0 + 3)
    let r_im := roundShiftIntTracked (p_im_sq.1 - p_re_sq.1) (p0 + 3)
    let w : FixedComplex (p0 + 2) := ⟨r_re.1, r_im.1⟩
    let wc := w.conjTracked
    (wc.1, p_re_im.2 + p_im_sq.2 + p_re_sq.2 + r_re.2 + r_im.2 + wc.2 + 2 * p0 + 6))
  set C_bar := computableFastDFTRecursiveWithMulTracked subMulBits
    (computeScheduleIntTree (rootK0 n) p0 B0) W_conj.1
  set C_inv := memoizeFinTracked (fun m : Fin (rootR0 n) => (C_bar.1 m).conjTracked)
  set out := memoizeFinTracked (fun k : Fin (rootR0 n) =>
    let rs := roundShiftIntTracked (C_inv.1 k).re 8
    (rs.1, rs.2 + p0 + 4))
  have hp0 : 18 ≤ p0 := rootP0_ge_eighteen n
  have hR0 : 4 ≤ rootR0 n := rootR0_ge_four n
  have hsmulRoot : ∀ x y : ℤ,
      (smulRoot x y).2 ≤ scaledSubMulCost M_mul (p0 + 2) + 8 * (2 * (p0 + 2)) + 10 :=
    signedMulFromTrackedBitMul_snd_le (2 * (p0 + 2)) (subMulBits (2 * (p0 + 2)))
      (scaledSubMulCost M_mul (p0 + 2))
      (fun xs ys => le_trans (hM (2 * (p0 + 2)) xs ys (by omega)) (le_scaledSubMulCost_two M_mul (p0 + 2)))
  have hzFixed : zFixed.2 ≤ rootR0 n * (2 * (p0 + 2) + 4) + rootR0 n + 1 :=
    memoizeFinTracked_snd_le _ (2 * (p0 + 2) + 4) (fun _ => le_rfl)
  have hdft1 : Z_hat.2 ≤ 12000 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (rootK0 n) p0 B0 :=
    computableFastDFTRecursiveWithMulTracked_snd_le subMulBits M_mul hM (rootK0 n) p0 B0 zFixed.1
  have hW_conj : W_conj.2 ≤
      rootR0 n * (3 * (scaledSubMulCost M_mul (p0 + 2) + 8 * (2 * (p0 + 2)) + 10) + 5 * p0 + 20) +
        rootR0 n + 1 :=
    memoizeFinTracked_snd_le _
      (3 * (scaledSubMulCost M_mul (p0 + 2) + 8 * (2 * (p0 + 2)) + 10) + 5 * p0 + 20)
      (fun u => by
        dsimp only
        simp only [roundShiftIntTracked_snd, FixedComplex.conjTracked_snd]
        have hp1 := hsmulRoot (2 * (Z_hat.1 u).re) (Z_hat.1 u).im
        have hp2 := hsmulRoot (Z_hat.1 u).im (Z_hat.1 u).im
        have hp3 := hsmulRoot (Z_hat.1 u).re (Z_hat.1 u).re
        omega)
  have hdft2 : C_bar.2 ≤ 12000 * fastDFTRecursiveSteps (scaledSubMulCost M_mul) (rootK0 n) p0 B0 :=
    computableFastDFTRecursiveWithMulTracked_snd_le subMulBits M_mul hM (rootK0 n) p0 B0 W_conj.1
  have hC_inv : C_inv.2 ≤ rootR0 n * (p0 + 4) + rootR0 n + 1 :=
    memoizeFinTracked_snd_le _ (p0 + 4) (fun _ => le_rfl)
  have hout : out.2 ≤ rootR0 n * (p0 + 14) + rootR0 n + 1 :=
    memoizeFinTracked_snd_le _ (p0 + 14) (fun _ => by
      dsimp only
      simp only [roundShiftIntTracked_snd]
      omega)
  have hbase : rootR0 n * (p0 + 4) ≤ fastDFTRecursiveSteps (scaledSubMulCost M_mul) (rootK0 n) p0 B0 :=
    mul_le_fastDFTRecursiveSteps (scaledSubMulCost M_mul) (rootK0 n) p0 B0
  nlinarith

theorem computableNatMulBitsAuxTracked_snd_le_zero (w : ℕ) (aBits bBits : List Bool) (hw : 1 ≤ w) :
    (computableNatMulBitsAuxTracked 0 w aBits bBits).2 ≤ 27 * schoolbookSubMulBitOps w := by
  unfold computableNatMulBitsAuxTracked schoolbookSubMulBitOps
  exact binaryShiftAddMulBitsTracked_snd_le hw aBits bBits

theorem computableNatMulBitsAuxTracked_snd_le_step
    (d : ℕ) (M_mul : ℕ → ℕ)
    (hM : ∀ (w' : ℕ) (xs ys : List Bool), 1 ≤ w' →
      (computableNatMulBitsAuxTracked d w' xs ys).2 ≤ M_mul w')
    (w : ℕ) (aBits bBits : List Bool) (hw : 1 ≤ w) :
    (computableNatMulBitsAuxTracked (d + 1) w aBits bBits).2 ≤
      150000000 * intMulAlgorithmSteps (scaledSubMulCost M_mul) w := by
  unfold computableNatMulBitsAuxTracked intMulAlgorithmSteps
  rw [if_pos hw]
  dsimp only
  have hfst : (computeScheduleIntTreeWithMulTracked
      (fun w' xs ys => computableNatMulBitsAuxTracked d w' xs ys)
      (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0)).1 =
      computeScheduleIntTree (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0) :=
    computeScheduleIntTreeWithMulTracked_fst_of_mul_eq _ (computableNatMulBitsAuxTracked_fst d)
      (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0)
  set tree := computeScheduleIntTree (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0)
  set aCh := sliceBitChunkFnTracked (chunkBits w) (rootR0 w) (aBits.take w)
  set bCh := sliceBitChunkFnTracked (chunkBits w) (rootR0 w) (bBits.take w)
  set conv := computableConvFromChunksWithMulTracked
    (fun w' xs ys => computableNatMulBitsAuxTracked d w' xs ys) w tree aCh.1 bCh.1
  set emitCh := carrySaveEmitBitsTracked (chunkBits w) (2 * w)
    (List.ofFn (fun k : Fin (rootR0 w) => (conv.1 k).toNat)) 0
  have hsched := computeScheduleIntTreeWithMulTracked_snd_le
    (fun w' xs ys => computableNatMulBitsAuxTracked d w' xs ys) M_mul hM
    (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0)
  have hconv : conv.2 ≤
      12100 * (2 * fastDFTRecursiveSteps (scaledSubMulCost M_mul)
        (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0) +
        3 * rootR0 w * scaledSubMulCost M_mul (rootP0 w + 2)) :=
    computableConvFromChunksWithMulTracked_snd_le
      (fun w' xs ys => computableNatMulBitsAuxTracked d w' xs ys) M_mul hM w aCh.1 bCh.1
  have haCh : aCh.2 = rootR0 w * (2 * chunkBits w + 3) + 4 := sliceBitChunkFnTracked_snd _ _ _
  have hbCh : bCh.2 = rootR0 w * (2 * chunkBits w + 3) + 4 := sliceBitChunkFnTracked_snd _ _ _
  have hemit : emitCh.2 ≤ rootR0 w * (2 * chunkBits w + 2) + 2 * w + 2 := by
    have h := carrySaveEmitBitsTracked_snd_le (chunkBits w)
      (List.ofFn (fun k : Fin (rootR0 w) => (conv.1 k).toNat)) (2 * w) 0
    rwa [List.length_ofFn] at h
  have hp0_eq : rootP0 w = 2 * chunkBits w + 2 * rootK0 w + 6 := rfl
  have hbase : rootR0 w * (rootP0 w + 4) ≤
      fastDFTRecursiveSteps (scaledSubMulCost M_mul)
        (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0) :=
    mul_le_fastDFTRecursiveSteps _ (rootK0 w) (rootP0 w) _
  have hR0 : 4 ≤ rootR0 w := rootR0_ge_four w
  rw [hfst]
  change aCh.2 + bCh.2 +
    (computeScheduleIntTreeWithMulTracked
      (fun w' xs ys => computableNatMulBitsAuxTracked d w' xs ys)
      (rootK0 w) (rootP0 w) (levelScheduleBIn (rootK0 w) (rootP0 w) 0)).2 +
    conv.2 + emitCh.2 + 2 * w + rootR0 w + 4 ≤ _
  nlinarith

/-- Constant `C_tracked_d1 = 150000000 * (1010141 * 27)` bounding `(computableNatMulBitsAuxTracked 1 w aBits bBits).2`
by `C_tracked_d1 * nestedSubMulBitOps w`. -/
def C_tracked_d1 : ℕ :=
  150000000 * (1010141 * 27)

theorem C_tracked_d1_pos : 1 ≤ C_tracked_d1 := by decide

theorem computableNatMulBitsAuxTracked_snd_le_one (w : ℕ) (aBits bBits : List Bool) (hw : 1 ≤ w) :
    (computableNatMulBitsAuxTracked 1 w aBits bBits).2 ≤ C_tracked_d1 * nestedSubMulBitOps w := by
  unfold C_tracked_d1
  have h1 := computableNatMulBitsAuxTracked_snd_le_step 0
    (fun w' => 27 * schoolbookSubMulBitOps w')
    computableNatMulBitsAuxTracked_snd_le_zero w aBits bBits hw
  have hscale :
      intMulAlgorithmSteps (scaledSubMulCost (fun w' => 27 * schoolbookSubMulBitOps w')) w ≤
        (1010141 * 27) * intMulAlgorithmSteps schoolbookSubMulBitOps w :=
    intMulAlgorithmSteps_scale_le_of_bounded (by norm_num)
      (fun q _ => le_of_eq (scaledSubMulCost_schoolbook 27 q))
  have hnest : intMulAlgorithmSteps schoolbookSubMulBitOps w = nestedSubMulBitOps w := by
    unfold nestedSubMulBitOps
    rw [if_neg (ne_of_gt hw)]
  linarith

/-- Uniform constant `C_tracked_total = 300000000 * C_tracked_d1 * C_nested_total + 20` for the
bottom-up `CostM` step bounds. -/
def C_tracked_total : ℕ :=
  300000000 * C_tracked_d1 * C_nested_total + 20

theorem C_tracked_total_pos : 0 < C_tracked_total := by
  unfold C_tracked_total
  omega

theorem computableNatMulBitsTracked_snd_le_aux {n : ℕ} (hn : 2 ≤ n) (inBits : List Bool) :
    (computableNatMulBitsTracked n inBits).2 ≤
      300000000 * C_tracked_d1 * C_nested_total * n * Nat.log 2 n := by
  unfold computableNatMulBitsTracked
  dsimp only
  have hfst : (computeScheduleIntTreeWithMulTracked
      (fun w xs ys => computableNatMulBitsAuxTracked 1 w xs ys)
      (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)).1 =
      computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0) :=
    computeScheduleIntTreeWithMulTracked_fst_of_mul_eq _ (computableNatMulBitsAuxTracked_fst 1)
      (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
  set tree := computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
  set aCh := sliceBitChunkFnTracked (chunkBits n) (rootR0 n) (inBits.take n)
  set bCh := sliceBitChunkFnTracked (chunkBits n) (rootR0 n) (inBits.drop n)
  set conv := computableConvFromChunksWithMulTracked
    (fun w xs ys => computableNatMulBitsAuxTracked 1 w xs ys) n tree aCh.1 bCh.1
  set emitCh := carrySaveEmitBitsTracked (chunkBits n) (2 * n)
    (List.ofFn (fun k : Fin (rootR0 n) => (conv.1 k).toNat)) 0
  have hsched := computeScheduleIntTreeWithMulTracked_snd_le
    (fun w xs ys => computableNatMulBitsAuxTracked 1 w xs ys)
    (fun w' => C_tracked_d1 * nestedSubMulBitOps w')
    computableNatMulBitsAuxTracked_snd_le_one
    (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
  have hconv : conv.2 ≤
      12100 * (2 * fastDFTRecursiveSteps (scaledSubMulCost (fun w' => C_tracked_d1 * nestedSubMulBitOps w'))
        (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0) +
        3 * rootR0 n * scaledSubMulCost (fun w' => C_tracked_d1 * nestedSubMulBitOps w') (rootP0 n + 2)) :=
    computableConvFromChunksWithMulTracked_snd_le
      (fun w xs ys => computableNatMulBitsAuxTracked 1 w xs ys)
      (fun w' => C_tracked_d1 * nestedSubMulBitOps w')
      computableNatMulBitsAuxTracked_snd_le_one n aCh.1 bCh.1
  have haCh : aCh.2 = rootR0 n * (2 * chunkBits n + 3) + 4 := sliceBitChunkFnTracked_snd _ _ _
  have hbCh : bCh.2 = rootR0 n * (2 * chunkBits n + 3) + 4 := sliceBitChunkFnTracked_snd _ _ _
  have hemit : emitCh.2 ≤ rootR0 n * (2 * chunkBits n + 2) + 2 * n + 2 := by
    have h := carrySaveEmitBitsTracked_snd_le (chunkBits n)
      (List.ofFn (fun k : Fin (rootR0 n) => (conv.1 k).toNat)) (2 * n) 0
    rwa [List.length_ofFn] at h
  have hp0_eq : rootP0 n = 2 * chunkBits n + 2 * rootK0 n + 6 := rfl
  have hbase : rootR0 n * (rootP0 n + 4) ≤
      fastDFTRecursiveSteps (scaledSubMulCost (fun w' => C_tracked_d1 * nestedSubMulBitOps w'))
        (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0) :=
    mul_le_fastDFTRecursiveSteps _ (rootK0 n) (rootP0 n) _
  have hR0 : 4 ≤ rootR0 n := rootR0_ge_four n
  rw [hfst]
  have hstep :
      aCh.2 + bCh.2 +
        (computeScheduleIntTreeWithMulTracked
          (fun w xs ys => computableNatMulBitsAuxTracked 1 w xs ys)
          (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)).2 +
        conv.2 + emitCh.2 + 2 * n + rootR0 n + 4 ≤
      150000000 * intMulAlgorithmSteps
        (scaledSubMulCost (fun w' => C_tracked_d1 * nestedSubMulBitOps w')) n := by
    unfold intMulAlgorithmSteps
    nlinarith
  have hscale :
      intMulAlgorithmSteps (scaledSubMulCost (fun w' => C_tracked_d1 * nestedSubMulBitOps w')) n ≤
        C_tracked_d1 * intMulAlgorithmSteps (scaledSubMulCost nestedSubMulBitOps) n :=
    intMulAlgorithmSteps_scale_le_of_bounded C_tracked_d1_pos
      (fun q _ => le_of_eq (scaledSubMulCost_const_mul C_tracked_d1 nestedSubMulBitOps q))
  have htop := intMulAlgorithmSteps_scaled_nestedSubMulBitOps_le_n_log_n hn
  change aCh.2 + bCh.2 +
    (computeScheduleIntTreeWithMulTracked
      (fun w xs ys => computableNatMulBitsAuxTracked 1 w xs ys)
      (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)).2 +
    conv.2 + emitCh.2 + 2 * n + rootR0 n + 4 ≤ _
  nlinarith only [hstep, hscale, htop]

/-- **Bottom-Up Step-Count Upper Bound for Parameter-Free `computableNatMulBitsTracked`
(`computableNatMulBitsTracked_snd_le`)**:
For every $n \ge 2$ and every input bit-list `inBits`, the bottom-up accumulated step count
`(computableNatMulBitsTracked n inBits).2` is bounded by
`C_tracked_total * n * Nat.log 2 n`. -/
theorem computableNatMulBitsTracked_snd_le {n : ℕ} (hn : 2 ≤ n) (inBits : List Bool) :
    (computableNatMulBitsTracked n inBits).2 ≤
      C_tracked_total * n * Nat.log 2 n := by
  have h := computableNatMulBitsTracked_snd_le_aux hn inBits
  unfold C_tracked_total
  nlinarith only [h]

/-- **Bottom-Up Step-Count Upper Bound for `computableNatMulTracked`
(`computableNatMulTracked_snd_le`)**:
For every $n \ge 2$ and all $A, B < 2 ^ n$, the bottom-up accumulated step count
`(computableNatMulTracked n A B).2` is bounded by
`C_tracked_total * n * Nat.log 2 n`. -/
theorem computableNatMulTracked_snd_le {n A B : ℕ} (hn : 2 ≤ n) (_hA : A < 2 ^ n) (_hB : B < 2 ^ n) :
    (computableNatMulTracked n A B).2 ≤ C_tracked_total * n * Nat.log 2 n := by
  unfold computableNatMulTracked
  dsimp only
  have ha : (encodeNatBitsTracked n A).2 = 2 * n + 2 := encodeNatBitsTracked_snd n A
  have hb : (encodeNatBitsTracked n B).2 = 2 * n + 2 := encodeNatBitsTracked_snd n B
  have hd : (decodeNatBitsTracked (2 * n)
      (computableNatMulBitsTracked n ((encodeNatBitsTracked n A).1 ++ (encodeNatBitsTracked n B).1)).1).2 =
      2 * (2 * n) + 2 :=
    decodeNatBitsTracked_snd (2 * n) _
  have hbits := computableNatMulBitsTracked_snd_le_aux hn
    ((encodeNatBitsTracked n A).1 ++ (encodeNatBitsTracked n B).1)
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by decide) hn
  unfold C_tracked_total
  nlinarith only [ha, hb, hd, hbits, hn, hlog]

/-- **Single-Statement Coupled Correctness & $O(n \log n)$ Step-Bound Theorem for
`computableNatMulTracked` (`computableNatMulTracked_spec`)**:
There exists a uniform constant $C = C_{\text{tracked,total}} > 0$ such that for all
$n \ge 2$ and all $n$-bit integers $A, B < 2^n$, the single bottom-up operation-tracking execution
`let (out, steps) := computableNatMulTracked n A B` simultaneously satisfies
`out = A * B` and `steps ≤ C * n * Nat.log 2 n`. -/
theorem computableNatMulTracked_spec :
    ∃ C : ℕ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
        let (out, steps) := computableNatMulTracked n A B
        out = A * B ∧
          steps ≤ C * n * Nat.log 2 n := by
  refine ⟨C_tracked_total, C_tracked_total_pos,
    fun n hn A B hA hB => ?_⟩
  exact ⟨computableNatMulTracked_fst n A B hA hB, computableNatMulTracked_snd_le hn hA hB⟩

/-- **Single-Statement Coupled Correctness & $O(n \log n)$ Step-Bound Theorem for Parameter-Free
`computableNatMulBitsTracked` (`computableNatMulBitsTracked_spec`)**:
There exists a uniform constant $C = C_{\text{tracked,total}} > 0$ such that for all
$n \ge 2$ and all $n$-bit integers $A, B < 2^n$, the single parameter-free bottom-up
operation-tracking execution
`let (outBits, steps) := computableNatMulBitsTracked n (encodeInputBits n A B)`
(taking ONLY `(n, inBits)` with **zero** `M_mul` parameter and **zero** calls to any formula cost)
simultaneously satisfies `outBits = encodeNatBits (2 * n) (A * B)` and
`steps ≤ C * n * Nat.log 2 n`. -/
theorem computableNatMulBitsTracked_spec :
    ∃ C : ℕ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
        let (outBits, steps) := computableNatMulBitsTracked n (encodeInputBits n A B)
        outBits = encodeNatBits (2 * n) (A * B) ∧
          steps ≤ C * n * Nat.log 2 n := by
  refine ⟨C_tracked_total, C_tracked_total_pos,
    fun n hn A B hA hB => ?_⟩
  exact ⟨computableNatMulBitsTracked_fst_encodeInputBits n A B hA hB,
    computableNatMulBitsTracked_snd_le hn (encodeInputBits n A B)⟩

/-! ## 3. Inhabited Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Suite, AST Audit & End-to-End Summary

### 3.1 Architectural Summary
1. **Unconditional, Inhabited Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Data-Movement,
   Arithmetic, Butterfly, Bit-Multiply-Accumulate, Conditional Subtract-Mux & Interleave Machines (`IntMul.TMPrimitives`)**:
   `tmUniformRevCopy`, `tmUniformIdCopy`, `tmUniformDeinterleave`, `tmUniformInterleave`,
   `tmUniformRippleAdd`, `tmUniformRippleSub`, `tmUniformButterflyAddSub`, `tmUniformBitMulAdd`, and
   `tmUniformCondSubStep` are concrete, inhabited single uniform 8-stack binary machines (`Turing.FinTM2`,
   `IsUniformFinTM2`, bounding `card K ≤ 8`, `card Λ`, `card σ`, and `card (Γ k)` across all 8
   binary stacks `k : Fin 8`) independent of $w$ or $n$ (Section 8 (`sec:lean`)).
2. **Unconditional Self-Recursive Operation-Tracking `CostM` Multiplication Pipeline & $O(n \log n)$
   Step-Count Theorem (`IntMul.FixedPoint`, `IntMul.KroneckerSpread`, `IntMul.ComputableCore`,
   `IntMul.TrackedCore` & Part 2.2 above)**:
   `computableNatMulBitsTracked` and `computableNatMulTracked` take only `(n, inBits)` / `(n, A, B)`
   and accumulate their `.2` step count bottom-up from the primitive leaf `CostM` operations;
   `computableNatMulBitsTracked_spec` and `computableNatMulTracked_spec` prove coupled correctness
   and $O(n \log n)$ step bounds (Table 3 (`tab:lean-map`) in Section 8 (`sec:lean`)).
3. **Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Primitives, Multi-Stage Composition, and Full
   End-to-End Machine (`tmIntMul`)**:
   - **Layer 1 (`CostM` Log-Cost Bit-Operation Model)**: The multi-level recursive `FastDFT`
     pipeline, pure-integer schedule generation, and their $O(n \log n)$ bit-operation bound are
     formalized at the computable functional `CostM` level (`computableNatMulBitsTracked_spec`,
     `computableNatMulTracked_spec`), where every multi-bit integer operation, modular index
     computation, and matrix transpose/routing step is charged proportional to operand bit-width
     (`costLinearWordOp`, `bitStepRegCost`).
   - **Layer 2 (Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Primitives, Composition, & Complete
     End-to-End `tmIntMul : Turing.FinTM2`)**: `canonicalUniformTMPrimitiveSuite` packages the 9
     standalone uniform 8-stack binary machine (`Turing.FinTM2`) primitives, `canonicalUniformTMCompositionSuite`
     (`IntMul.TMComposition`) proves the uniform 8-stack sequential and loop composition
     combinators (`seqBitFinTM2`, `loopTapeBitFinTM2`), and `IntMul.TMEndToEnd` compiles the entire
     multi-level recursive `FastDFT` pipeline and 3-tier multiplier into a single concrete, inhabited,
     parameter-free 8-stack binary machine (`Turing.FinTM2`) `tmIntMul` (`TM2.step` transitions on 8 binary stacks;
     `isUniformFinTM2_tmIntMul`, `tmIntMul_evalsToInTime_n_log_n`,
     `intMul_complete_endToEnd_summary`, Theorem 2 (`thm:lean`) in Section 8 (`sec:lean`)). -/

/-- **Inhabited Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Primitive, Butterfly,
Bit-Multiply-Accumulate, Conditional Subtract-Mux & Interleave Suite (`UniformTMPrimitiveSuite`)**:
Packages the 9 concrete, inhabited uniform 8-stack binary machines (`Turing.FinTM2`, 8 binary stacks)
with their $O(1)$ state-space proofs (`IsUniformFinTM2`) and linear-time `TM2.step` transition bounds (`EvalsToInTime`). -/
structure UniformTMPrimitiveSuite : Prop where
  /-- `tmUniformRevCopy` has constant state space `(2, 8, 2)` and reverses any bit-list `xs` in `≤ 2 * xs.length + 1` steps. -/
  revCopy_spec :
    IsUniformFinTM2 tmUniformRevCopy 2 8 2 ∧
      ∀ xs : List Bool,
        ∃ t ≤ 2 * xs.length + 1,
          Turing.EvalsToInTime tmUniformRevCopy.step
            (Turing.initList tmUniformRevCopy xs)
            (some ⟨none, default, twoTapeStk [] xs.reverse⟩) t
  /-- `tmUniformIdCopy` has constant state space `(4, 8, 2)` and preserves order in `≤ 4 * xs.length + 2` steps. -/
  idCopy_spec :
    IsUniformFinTM2 tmUniformIdCopy 4 8 2 ∧
      ∀ xs : List Bool,
        ∃ t ≤ 4 * xs.length + 2,
          Turing.EvalsToInTime tmUniformIdCopy.step
            (Turing.initList tmUniformIdCopy xs)
            (some (Turing.haltList tmUniformIdCopy xs)) t
  /-- `tmUniformDeinterleave` has constant state space `(4, 8, 2)` and splits even/odd bits in `≤ 4 * ps.length + 1` steps. -/
  deinterleave_spec :
    IsUniformFinTM2 tmUniformDeinterleave 4 8 2 ∧
      ∀ ps : List (Bool × Bool),
        ∃ t ≤ 4 * ps.length + 1,
          Turing.EvalsToInTime tmUniformDeinterleave.step
            (Turing.initList tmUniformDeinterleave (flattenBitPairs ps))
            (some ⟨none, default,
              threeTapeWorkStk [] (ps.map Prod.fst).reverse (ps.map Prod.snd).reverse⟩) t
  /-- `tmUniformInterleave` has constant state space `(6, 8, 2)` and interleaves equal-length streams on `kWork0`/`kWork1` in `≤ 8 * ps.length + 2` steps. -/
  interleave_spec :
    IsUniformFinTM2 tmUniformInterleave 6 8 2 ∧
      ∀ ps : List (Bool × Bool),
        ∃ t ≤ 8 * ps.length + 2,
          Turing.EvalsToInTime tmUniformInterleave.step
            ⟨some .popEven, default,
              threeTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd)⟩
            (some (Turing.haltList tmUniformInterleave (flattenBitPairs ps))) t
  /-- `tmUniformRippleAdd` has constant state space `(6, 8, 2)` and adds any $w$-bit integers `A, B < 2 ^ w` in `≤ 5 * w + 5` steps. -/
  rippleAdd_spec :
    IsUniformFinTM2 tmUniformRippleAdd 6 8 2 ∧
      ∀ w A B : ℕ, A < 2 ^ w → B < 2 ^ w →
        ∃ t ≤ 5 * w + 5,
          Turing.EvalsToInTime tmUniformRippleAdd.step
            ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
            (some (Turing.haltList tmUniformRippleAdd (encodeNatBits (w + 1) (A + B)))) t
  /-- `tmUniformRippleSub` has constant state space `(5, 8, 2)` and subtracts any $w$-bit integers `B ≤ A < 2 ^ w` in `≤ 5 * w + 2` steps. -/
  rippleSub_spec :
    IsUniformFinTM2 tmUniformRippleSub 5 8 2 ∧
      ∀ w A B : ℕ, B ≤ A → A < 2 ^ w →
        ∃ t ≤ 5 * w + 2,
          Turing.EvalsToInTime tmUniformRippleSub.step
            ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
            (some (Turing.haltList tmUniformRippleSub (encodeNatBits w (A - B)))) t
  /-- `tmUniformButterflyAddSub` has constant state space `(9, 16, 2)` and computes the simultaneous radix-2 butterfly sum and difference in `≤ 8 * w + 6` steps. -/
  butterflyAddSub_spec :
    IsUniformFinTM2 tmUniformButterflyAddSub 9 16 2 ∧
      ∀ w A B : ℕ, B ≤ A → A < 2 ^ w →
        ∃ t ≤ 8 * w + 6,
          Turing.EvalsToInTime tmUniformButterflyAddSub.step
            ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
            (some ⟨none, default,
              twoTapeStk (encodeNatBits (w + 1) (A + B)) (encodeNatBits w (A - B))⟩) t
  /-- `tmUniformBitMulAdd` has constant state space `(7, 16, 2)` and computes the 1-bit gated partial-product accumulation `acc + if mBit then B else 0` in `≤ 5 * w + 6` steps. -/
  bitMulAdd_spec :
    IsUniformFinTM2 tmUniformBitMulAdd 7 16 2 ∧
      ∀ (mBit : Bool) (w acc B : ℕ), acc < 2 ^ w → B < 2 ^ w →
        ∃ t ≤ 5 * w + 6,
          Turing.EvalsToInTime tmUniformBitMulAdd.step
            ⟨some .popMulBit, default,
              threeTapeWorkStk [mBit] (encodeNatBits w acc) (encodeNatBits w B)⟩
            (some (Turing.haltList tmUniformBitMulAdd
              (encodeNatBits (w + 1) (acc + if mBit then B else 0)))) t
  /-- `tmUniformCondSubStep` has constant state space `(8, 16, 2)` and computes the conditional subtract-mux step of $w$-bit restoring division/sqrt (`if D ≤ R then R - D else R` on `kIO`, `[decide (D ≤ R)]` on `kWork0`) in `≤ 7 * w + 3` steps. -/
  condSubStep_spec :
    IsUniformFinTM2 tmUniformCondSubStep 8 16 2 ∧
      ∀ w R D : ℕ, R < 2 ^ w → D < 2 ^ w →
        ∃ t ≤ 7 * w + 3,
          Turing.EvalsToInTime tmUniformCondSubStep.step
            ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w R) (encodeNatBits w D)⟩
            (some ⟨none, default,
              twoTapeStk (encodeNatBits w (if D ≤ R then R - D else R)) [decide (D ≤ R)]⟩) t

/-- **Concrete Inhabitation of `UniformTMPrimitiveSuite` (`canonicalUniformTMPrimitiveSuite`)**:
Unconditionally inhabits `UniformTMPrimitiveSuite` using the 9 verified uniform `FinTM2` machines. -/
theorem canonicalUniformTMPrimitiveSuite : UniformTMPrimitiveSuite where
  revCopy_spec := ⟨isUniformFinTM2_tmUniformRevCopy, tmUniformRevCopy_evalsToInTime⟩
  idCopy_spec := ⟨isUniformFinTM2_tmUniformIdCopy, tmUniformIdCopy_evalsToInTime⟩
  deinterleave_spec := ⟨isUniformFinTM2_tmUniformDeinterleave, tmUniformDeinterleave_evalsToInTime⟩
  interleave_spec := ⟨isUniformFinTM2_tmUniformInterleave, tmUniformInterleave_evalsToInTime⟩
  rippleAdd_spec := ⟨isUniformFinTM2_tmUniformRippleAdd, tmUniformRippleAdd_encodeNatBits_evalsToInTime⟩
  rippleSub_spec := ⟨isUniformFinTM2_tmUniformRippleSub, tmUniformRippleSub_encodeNatBits_evalsToInTime⟩
  butterflyAddSub_spec := ⟨isUniformFinTM2_tmUniformButterflyAddSub, tmUniformButterflyAddSub_encodeNatBits_evalsToInTime⟩
  bitMulAdd_spec := ⟨isUniformFinTM2_tmUniformBitMulAdd, tmUniformBitMulAdd_encodeNatBits_evalsToInTime⟩
  condSubStep_spec := ⟨isUniformFinTM2_tmUniformCondSubStep, tmUniformCondSubStep_encodeNatBits_evalsToInTime⟩

/-! ### 3.2 Compile-Time Metaprogramming (`MetaM`) AST Audit of All `*Tracked` Declarations -/

/-- Closed-form cost-bound formula names that are **strictly forbidden** inside any `*Tracked`
program definition. -/
def forbiddenTrackedFormulaNames : List String :=
  [ "IntMul.intMulAlgorithmSteps",
    "IntMul.fastDFTRecursiveSteps",
    "IntMul.computableFastDFTRecursiveSteps",
    "IntMul.scheduleTreeGenOps",
    "IntMul.subMulBitOps",
    "IntMul.nestedSubMulBitOps",
    "IntMul.schoolbookSubMulBitOps",
    "IntMul.step1SpreadOps",
    "IntMul.step2SyntheticFFTOps",
    "IntMul.step3DeconvOps",
    "IntMul.stepFixedPointMuls",
    "IntMul.leafDFTOps",
    "IntMul.levelButterflyStageWork",
    "IntMul.subproblemButterflyStageWork" ]

/-- Wide-integer Horner packing/unpacking helpers and untracked composite pipeline functions that
are **strictly forbidden** inside any `*Tracked` or `*RegAux` program definition. -/
def forbiddenTrackedHelperNames : List String :=
  [ "IntMul.evalSignedSlots",
    "IntMul.evalSignedSlotsTracked",
    "IntMul.unpackSignedSlots",
    "IntMul.unpackSignedSlotsTracked",
    "IntMul.extractNatChunks",
    "IntMul.extractNatChunksTracked",
    "IntMul.natChunkFn",
    "IntMul.natChunkFnTracked",
    "IntMul.evalBaseChunks",
    "IntMul.evalBaseChunksTracked",
    "IntMul.roundDivInt",
    "IntMul.binaryRestoringDivMod",
    "IntMul.binaryRestoringSqrtRem",
    "IntMul.binaryShiftAddMul",
    "IntMul.FixedComplex.mulRounded",
    "IntMul.FixedComplex.mulRoundedWith",
    "IntMul.FixedComplex.scaleRounded",
    "IntMul.FixedComplex.scaleRoundedWith",
    "IntMul.divScalarFixed",
    "IntMul.divNatFixed",
    "IntMul.approxSqrtFixed",
    "IntMul.approxLogTwoFixed",
    "IntMul.approxPiFixed",
    "IntMul.kroneckerOverlapAddScalar",
    "IntMul.kroneckerOverlapAddScalarWithMul",
    "IntMul.kroneckerRowSpreadFixed",
    "IntMul.kroneckerRowSpreadFixedWithMul",
    "IntMul.kroneckerMatrixSpreadFixed",
    "IntMul.kroneckerMatrixSpreadFixedWithMul",
    "IntMul.radix2SyntheticFFTFixed",
    "IntMul.radix2FFT1DFixed",
    "IntMul.radix2FFT1DFixedWithMul",
    "IntMul.baseRadix2FFTFixed",
    "IntMul.baseRadix2FFTFixedWithMul",
    "IntMul.bidiagSweepFixed",
    "IntMul.bidiagSweepFixedWithMul",
    "IntMul.nyquistColumnSolveFixed",
    "IntMul.nyquistColumnSolveFixedWithMul",
    "IntMul.cyclicBidiagPrevSolveFixed",
    "IntMul.cyclicBidiagPrevSolveFixedWithMul",
    "IntMul.cyclicBidiagSolveFixed",
    "IntMul.cyclicBidiagSolveFixedWithMul",
    "IntMul.computableFastDFTRecursive",
    "IntMul.computableFastDFTRecursiveWithMul",
    "IntMul.computableFastTwoCallDFTConv",
    "IntMul.computableFastTwoCallDFTConvWithMul",
    "IntMul.computableConvFromChunksWithMul",
    "IntMul.computableReconstructProduct",
    "IntMul.computableReconstructProductWithMul",
    "IntMul.computableReconstructProductBitsWithMul",
    "IntMul.computeScheduleIntTree",
    "IntMul.computeScheduleIntTreeWithMul",
    "IntMul.computableIntMulBits",
    "IntMul.computableIntMulPipelineBits",
    "IntMul.computableNatMulAux",
    "IntMul.computableNatMulBitsAux",
    "IntMul.computableNatMul",
    "IntMul.computableNatMulBits",
    "IntMul.scatterAddRange1D",
    "IntMul.scatterAddRange2D",
    "IntMul.preFoldedFilterFast",
    "IntMul.nyquistModeSumFixed" ]

/-- Explicit allowlist of `IntMul.*` data types/constructors/projections, `CostM` primitives, and
$O(1)$/scalar schedule-index helpers permitted inside `*Tracked` and `*RegAux` definitions. Any `IntMul.*` constant referenced by a `*Tracked` or `*RegAux` definition must
either be another `*Tracked`/`*RegAux` declaration, belong to `allowedIntMulDataAndIndexInTracked`,
or be one of the 8 leaf primitive wrappers verified by `isAllowedIntMulLeafWrapperCall`. -/
def allowedIntMulDataAndIndexInTracked : List String :=
  [ "IntMul.CostM", "IntMul.costLinearWordOp", "IntMul.bitStepRegCost",
    "IntMul.FixedComplex", "IntMul.FixedComplex.mk", "IntMul.FixedComplex.re", "IntMul.FixedComplex.im",
    "IntMul.FixedComplex.instOfNatZero", "IntMul.FixedComplex.instInhabited",
    "IntMul.FixedComplex.instZero", "IntMul.FixedComplex.instSub",
    "IntMul.instInhabitedFixedComplex", "IntMul.instOfNatFixedComplex",
    "IntMul.FixedComplex.add", "IntMul.FixedComplex.sub", "IntMul.FixedComplex.conj",
    "IntMul.FixedComplex.halfRounded", "IntMul.FixedComplex.rescale",
    "IntMul.roundShiftInt", "IntMul.negacyclicShiftFixed",
    "IntMul.evenSubIndex", "IntMul.oddSubIndex", "IntMul.mul_two_pow_sub_lt",
    "IntMul.qBaseEll", "IntMul.qChildEll", "IntMul.pChildEll", "IntMul.pWorkEll",
    "IntMul.k1Ell", "IntMul.k2Ell", "IntMul.t1Ell", "IntMul.rEll", "IntMul.c1Ell",
    "IntMul.t1Ell_pos", "IntMul.rEll_pos", "IntMul.t1Ell_mul_rEll",
    "IntMul.computeM1Ell", "IntMul.scheduleSlotBits", "IntMul.foldedHalfWidth",
    "IntMul.kroneckerPackedBitLength", "IntMul.childScheduleBIn", "IntMul.isBaseLeaf",
    "IntMul.rootK0", "IntMul.rootP0", "IntMul.rootR0", "IntMul.chunkBits", "IntMul.levelScheduleBIn",
    "IntMul.altSign", "IntMul.iPowRe", "IntMul.iPowIm", "IntMul.nyquistOpenChainStep",
    "IntMul.ScheduleIntTree", "IntMul.ScheduleIntTree.leaf", "IntMul.ScheduleIntTree.node",
    "IntMul.ScheduleIntTree.casesOn", "IntMul.ScheduleIntTree.rec",
    "IntMul.oddStrideGather", "IntMul.oddColScatter", "IntMul.freqScatter", "IntMul.cyclicNext",
    "IntMul.cyclicModIndex", "IntMul.shiftedFilter", "IntMul.numBlocks", "IntMul.signalBlock",
    "IntMul.packChunksFixed" ]

/-- Check whether `nm` is `target` or one of its compiler-generated auxiliary declarations. -/
def isDeclOrAux (nm : Lean.Name) (target : String) : Bool :=
  let s := nm.toString
  s == target || s.startsWith (target ++ ".")

/-- Strict caller-scoped allowlist for the 8 leaf primitive wrappers in `IntMul.*Tracked`. -/
def isAllowedIntMulLeafWrapperCall (nm : Lean.Name) (uStr : String) : Bool :=
  (uStr == "IntMul.memoizeFin" &&
    (isDeclOrAux nm "IntMul.memoizeFinTracked" || isDeclOrAux nm "IntMul.memoizeFilterTapTracked")) ||
  (uStr == "IntMul.memoizeFin2" &&
    (isDeclOrAux nm "IntMul.memoizeFin2Tracked" || isDeclOrAux nm "IntMul.memoizeFilterTapTracked")) ||
  (uStr == "IntMul.memoizeFilterTap" && isDeclOrAux nm "IntMul.memoizeFilterTapTracked") ||
  (uStr == "IntMul.memoizeRange" && isDeclOrAux nm "IntMul.memoizeRangeTracked") ||
  (uStr == "IntMul.encodeNatBits" &&
    (isDeclOrAux nm "IntMul.encodeNatBitsTracked" ||
     isDeclOrAux nm "IntMul.carrySaveEmitBitsTracked" ||
     isDeclOrAux nm "IntMul.packSignedSlotsBitsAuxTracked")) ||
  (uStr == "IntMul.decodeNatBits" &&
    (isDeclOrAux nm "IntMul.decodeNatBitsTracked" ||
     isDeclOrAux nm "IntMul.sliceBitChunksTracked" ||
     isDeclOrAux nm "IntMul.unpackSignedSlotsBitsAuxTracked")) ||
  ((uStr == "IntMul.extractSignedSlot" || uStr == "IntMul.stepSignedSlot") &&
    isDeclOrAux nm "IntMul.unpackSignedSlotsBitsAuxTracked")

def isTrackedSeg (s : String) : Bool :=
  s.endsWith "Tracked" || s.endsWith "RegAux" || s == "signedMulFromTrackedBitMul"

/-- Compile-time AST denylist + allowlist audit over every `IntMul.*Tracked` and `IntMul.*RegAux`
definition (and all of their auxiliary `_unary`, `_mutual`, and `match_*` definitions) in the Lean
`Environment`:
1. Verifies that no `*Tracked` or `*RegAux` definition references any closed-form cost-bound formula
   in `forbiddenTrackedFormulaNames` or any `IntMul.*Ops` constant.
2. Verifies that no `*Tracked` or `*RegAux` definition references any forbidden wide-integer Horner
   packing/unpacking helper, untracked scatter/gather/transpose helper, or untracked composite
   pipeline function in `forbiddenTrackedHelperNames`.
3. Enforces a strict **allowlist** over every `IntMul.*` constant referenced by a `*Tracked` or
   `*RegAux` definition: every such `u` must either be another `*Tracked`/`*RegAux` declaration,
   belong to `allowedIntMulDataAndIndexInTracked`, or satisfy `isAllowedIntMulLeafWrapperCall nm u`. -/
def auditTrackedDeclarations (env : Lean.Environment) : Except String Nat :=
  let (count, errs) := env.constants.fold (init := (0, ([] : List String))) fun (count, errs) nm cinfo =>
    match cinfo with
    | .defnInfo defnVal =>
      let segs := nm.toString.splitOn "."
      if nm.getRoot == `IntMul && segs.any isTrackedSeg then
        let used := defnVal.value.getUsedConstants
        let errs := used.foldl (init := errs) fun errs u =>
          let uStr := u.toString
          let errs :=
            if forbiddenTrackedFormulaNames.contains uStr ||
               (u.getRoot == `IntMul && uStr.endsWith "Ops") then
              s!"AST Audit Violation: {nm} references closed-form cost formula {uStr}" :: errs
            else errs
          let errs :=
            if forbiddenTrackedHelperNames.contains uStr then
              s!"AST Audit Violation: {nm} references forbidden untracked/Horner helper {uStr}" :: errs
            else errs
          if u.getRoot == `IntMul then
            let uSegs := uStr.splitOn "."
            let isTrackedOrRegAux :=
              uSegs.any (fun s => isTrackedSeg s || s.startsWith "match_")
            let isAllowedDataOrIdx :=
              allowedIntMulDataAndIndexInTracked.contains uStr ||
              uStr.startsWith "IntMul.ScheduleIntTree." ||
              uStr.startsWith "IntMul.FixedComplex.mk."
            let isAllowedLeaf := isAllowedIntMulLeafWrapperCall nm uStr
            if !(isTrackedOrRegAux || isAllowedDataOrIdx || isAllowedLeaf) then
              s!"AST Allowlist Violation: {nm} references non-allowlisted IntMul declaration {uStr}" :: errs
            else errs
          else errs
        (count + 1, errs)
      else
        (count, errs)
    | _ => (count, errs)
  if errs.isEmpty then .ok count
  else .error ("\n".intercalate errs.reverse)

open Lean Elab Command in
/-- Compile-time command executing `auditTrackedDeclarations` on the current environment and
failing compilation if any `IntMul.*Tracked` declaration violates the AST denylist or allowlist. -/
elab "#verify_tracked_declarations_ast_audit" : command => do
  let env ← getEnv
  match auditTrackedDeclarations env with
  | .ok count =>
    if count < 40 then
      throwError "AST Audit Error: expected at least 40 *Tracked definitions, found {count}"
  | .error msg =>
    throwError "{msg}"

#verify_tracked_declarations_ast_audit

/-- **Unconditional Correctness & Bottom-Up `CostM` $O(n \log n)$ Step-Count Summary Theorem for the
Self-Recursive Computable Integer Multiplication Pipeline (`intMul_endToEnd_unconditional_summary`,
Section 8 (`sec:lean`))**:
Combines in a single unconditional statement:
1. **Self-Recursive Parameter-Free Bottom-Up `CostM` Correctness & $O(n \log n)$ Step-Bound**:
   $\exists C > 0, \forall n \ge 2, \forall A, B < 2^n$, the single parameter-free bottom-up
   operation-tracking execution `let (outBits, steps) := computableNatMulBitsTracked n (encodeInputBits n A B)`
   and `let (out, stepsNat) := computableNatMulTracked n A B` simultaneously satisfy
   `outBits = encodeNatBits (2 * n) (A * B)`, `out = A * B`, `steps ≤ C * n * Nat.log 2 n`, and
   `stepsNat ≤ C * n * Nat.log 2 n`.
2. **Self-Recursive & Reference Pipeline Bit-Exactness**:
   Bit-exactness of `computableNatMulBits`, `computableNatMul`, `computableIntMulBits`,
   `computableIntMulPipelineBits`, `intMulSchedPipelineBits`, and `intMulPipelineBits` for all $n \in \mathbb{N}$
   and $A, B < 2^n$.
3. **Inhabited Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Primitive & Composition Suites**:
   `UniformTMPrimitiveSuite ∧ UniformTMCompositionSuite` inhabited unconditionally by
   `⟨canonicalUniformTMPrimitiveSuite, canonicalUniformTMCompositionSuite⟩`. -/
theorem intMul_endToEnd_unconditional_summary :
    (∃ C : ℕ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
        (let (outBits, steps) := computableNatMulBitsTracked n (encodeInputBits n A B)
         outBits = encodeNatBits (2 * n) (A * B) ∧ steps ≤ C * n * Nat.log 2 n) ∧
        (let (out, stepsNat) := computableNatMulTracked n A B
         out = A * B ∧ stepsNat ≤ C * n * Nat.log 2 n)) ∧
    (∀ n A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      computableNatMulBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) ∧
      computableNatMul n A B = A * B ∧
      computableIntMulBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) ∧
      computableIntMulPipelineBits n
        (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
        (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) ∧
      intMulPipelineBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) ∧
      intMulSchedPipelineBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) ∧
      computableIntMulPipelineBits n
        (canonicalScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
        (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B)) ∧
    (UniformTMPrimitiveSuite ∧ UniformTMCompositionSuite) := by
  refine ⟨⟨C_tracked_total, C_tracked_total_pos,
    fun n hn A B hA hB =>
      ⟨⟨computableNatMulBitsTracked_fst_encodeInputBits n A B hA hB,
        computableNatMulBitsTracked_snd_le hn (encodeInputBits n A B)⟩,
       ⟨computableNatMulTracked_fst n A B hA hB,
        computableNatMulTracked_snd_le hn hA hB⟩⟩⟩,
    fun n A B hA hB =>
      ⟨computableNatMulBits_encodeInputBits n A B hA hB,
       computableNatMul_eq_mul n A B hA hB,
       computableIntMulBits_encodeInputBits n A B hA hB,
       computableIntMulPipelineBits_computeScheduleIntTree_encodeInputBits n A B hA hB,
       intMulPipelineBits_encodeInputBits n A B hA hB,
       intMulSchedPipelineBits_encodeInputBits n A B hA hB,
       computableIntMulPipelineBits_canonical_encodeInputBits n A B hA hB⟩,
    ⟨canonicalUniformTMPrimitiveSuite, canonicalUniformTMCompositionSuite⟩⟩

end IntMul

#print axioms IntMul.fastDFTRecursiveSteps_root_le
#print axioms IntMul.intMulAlgorithmSteps_le_n_log_n
#print axioms IntMul.exists_uniform_C_intMulAlgorithmSteps_le
#print axioms IntMul.intMulAlgorithmSteps_subMulBitOps_le_n_log_n
#print axioms IntMul.exists_uniform_C_intMulAlgorithmSteps_subMulBitOps_le
#print axioms IntMul.intMulAlgorithmSteps_nestedSubMulBitOps_le_n_log_n
#print axioms IntMul.unpackReassembleChunks_eq_mod
#print axioms IntMul.intMulPipelineBits_encodeInputBits
#print axioms IntMul.intMulSchedPipelineBits_encodeInputBits
#print axioms IntMul.computableIntMulPipelineBits
#print axioms IntMul.computableIntMulPipelineBits_canonical_eq_intMulSchedPipelineBits
#print axioms IntMul.computableIntMulPipelineBits_canonical_encodeInputBits
#print axioms IntMul.computableIntMulPipelineBits_computeScheduleIntTree_encodeInputBits
#print axioms IntMul.computableNatMulTracked_spec
#print axioms IntMul.computableNatMulBitsTracked_spec
#print axioms IntMul.tmUniformBitMulAdd_encodeNatBits_evalsToInTime
#print axioms IntMul.canonicalUniformTMPrimitiveSuite
#print axioms IntMul.canonicalUniformTMCompositionSuite
#print axioms IntMul.intMul_endToEnd_unconditional_summary
