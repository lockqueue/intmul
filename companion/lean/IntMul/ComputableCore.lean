import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives
import IntMul.FastDFT
import IntMul.ComputableSchedule

set_option backward.isDefEq.respectTransparency false

namespace IntMul

/-!
# Computable Pure-Integer Multi-Level `FastDFT` & Multiplication Pipeline (`IntMul.ComputableCore`)

This module implements the computable integer execution of the recursive `FastDFT` transform and
two-call integer multiplication pipeline (Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`),
Lemma 6.5 (`lem:forward`) in Section 6.3 (`sec:forward-error`), and Section 8 (`sec:lean`)), together
with its equivalence to the analytic specification in `IntMul.FastDFT` and unconditional accuracy
and bit-exactness proofs on any valid `ScheduleIntTree`.

### 1. Computable Multi-Level Recursive `FastDFT` with Blocked Kronecker Multiplication
-/

/-- **Computable Pure-Integer Multi-Level Recursive `FastDFT` with Parameterized Integer Multiplier
(`computableFastDFTRecursiveWithMul`, Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`))**:
Executes the complete multi-level sinc-Gaussian polynomial-transform DFT algorithm (`syntheticFFT`
in this development) using **only** computable integer and fixed-point arithmetic
(`FixedComplex`, `ℤ`, `ℕ`, `ℚ`), the precomputed integer schedule tree `ScheduleIntTree`, and a
parameterized natural-number multiplier `natMul : ℕ → ℕ → ℕ` for the Step 1 blocked Kronecker
Overlap-Add product, with **zero** `noncomputable`, **zero** `ℝ`, and **zero** `ℂ`:
- Leaf case: executes the $O(K \cdot 2^K)$ recursive Cooley–Tukey radix-2 butterfly FFT
  `baseRadix2FFTFixed` indexing into the 1D leaf twiddle table of length $2^K$.
- Recursive step:
  1. **Step 1**: Odd-stride gather + 2-product blocked Kronecker Overlap-Add row spreading via
     `kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul natMul)`.
  2. **Step 2**: Quantized pre-twist, $k_1$-stage negacyclic `radix2SyntheticFFTFixed`, quantized
     post-twist, $t_1$ recursive child calls, and `oddColScatter`.
  3. **Step 3**: Column-level $O(t_1)$ 2-pass open-chain + cyclic rank-1 correction Nyquist solver
     `nyquistColumnSolveFixed` at $u_2 = r/2$ and `cyclicBidiagPrevSolveFixed` at $u_2 \ne r/2$
     (hoisted outside the row loop $u_1 \in \text{Fin } t_1$), followed by `freqScatter`. -/
def computableFastDFTRecursiveWithMul (natMul : ℕ → ℕ → ℕ)
    {K p B_in : ℕ} (tree : ScheduleIntTree K p B_in)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    Fin (2 ^ K) → FixedComplex (p + 2) :=
  let smul := signedMulFromNatMul natMul
  match tree with
  | .leaf K p _B_in leafTwiddles =>
    baseRadix2FFTFixedWithMul smul K p leafTwiddles xFixed
  | .node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child =>
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let B_slot := scheduleSlotBits K p B_in m1
    have hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    have ht1_pos : 0 < t1 := t1Ell_pos K
    have hr_pos : 0 < r := rEll_pos K
    haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
    have hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    -- Step 1: Odd-stride gather + 2-product blocked Kronecker Overlap-Add row spreading
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (oddStrideGather t1 r hR_pos (fun j => FixedComplex.rescale qChild (xFixed j)))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixedWithMul smul
        t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap
    -- Step 2: Quantized pre-twist, radix-2 polynomial transform (`radix2SyntheticFFTFixed`), quantized post-twist, recursive child calls, oddColScatter
    let U_preFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun j1 k2 => FixedComplex.mulRoundedWith smul (preTwistRoot k2) (U_spreadFixed j1 k2))
    let Q_synFixed : Fin t1 → Fin r → FixedComplex qChild :=
      radix2SyntheticFFTFixed (k1Ell K) c1 U_preFixed
    let Q_postFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun v1 k2 => FixedComplex.mulRoundedWith smul (postTwistRoot k2) (Q_synFixed v1 k2))
    let Q_hatFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun v1 => computableFastDFTRecursiveWithMul natMul child (Q_postFixed v1))
    let Y_matFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hatFixed)
    -- Step 3: Column-sweep deconvolution (hoisted outside u1) + Nyquist open-chain solver at u2 = r / 2
    let altFixed : FixedComplex qChild := nyquistModeSumFixed K p xFixed
    let Z_colsFixed : Fin r → Fin t1 → FixedComplex qChild :=
      memoizeFin2 (fun u2 =>
        if u2.val = r / 2 then
          nyquistColumnSolveFixedWithMul smul (c0Mantissa u2) (fun m => Y_matFixed m u2) altFixed
        else
          cyclicBidiagPrevSolveFixedWithMul smul (c0Mantissa u2) (c1Mantissa u2) (fun m => Y_matFixed m u2))
    let Z_matFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun u1 u2 => Z_colsFixed u2 u1)
    memoizeFin (fun u => FixedComplex.rescale (p + 2) (freqScatter t1 r hR_eq Z_matFixed u))

/-- **Computable Pure-Integer Multi-Level Recursive `FastDFT` (`computableFastDFTRecursive`)**:
Reference computable integer recursive `FastDFT` with standard integer multiplication. -/
def computableFastDFTRecursive {K p B_in : ℕ} (tree : ScheduleIntTree K p B_in)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    Fin (2 ^ K) → FixedComplex (p + 2) :=
  match tree with
  | .leaf K p _B_in leafTwiddles =>
    baseRadix2FFTFixed K p leafTwiddles xFixed
  | .node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child =>
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let B_slot := scheduleSlotBits K p B_in m1
    have hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    have ht1_pos : 0 < t1 := t1Ell_pos K
    have hr_pos : 0 < r := rEll_pos K
    haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
    have hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (oddStrideGather t1 r hR_pos (fun j => FixedComplex.rescale qChild (xFixed j)))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
        t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap
    let U_preFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun j1 k2 => FixedComplex.mulRounded (preTwistRoot k2) (U_spreadFixed j1 k2))
    let Q_synFixed : Fin t1 → Fin r → FixedComplex qChild :=
      radix2SyntheticFFTFixed (k1Ell K) c1 U_preFixed
    let Q_postFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun v1 k2 => FixedComplex.mulRounded (postTwistRoot k2) (Q_synFixed v1 k2))
    let Q_hatFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun v1 => computableFastDFTRecursive child (Q_postFixed v1))
    let Y_matFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hatFixed)
    let altFixed : FixedComplex qChild := nyquistModeSumFixed K p xFixed
    let Z_colsFixed : Fin r → Fin t1 → FixedComplex qChild :=
      memoizeFin2 (fun u2 =>
        if u2.val = r / 2 then
          nyquistColumnSolveFixed (c0Mantissa u2) (fun m => Y_matFixed m u2) altFixed
        else
          cyclicBidiagPrevSolveFixed (c0Mantissa u2) (c1Mantissa u2) (fun m => Y_matFixed m u2))
    let Z_matFixed : Fin t1 → Fin r → FixedComplex qChild :=
      memoizeFin2 (fun u1 u2 => Z_colsFixed u2 u1)
    memoizeFin (fun u => FixedComplex.rescale (p + 2) (freqScatter t1 r hR_eq Z_matFixed u))

/-- Equivalence between `computableFastDFTRecursiveWithMul natMul` and `computableFastDFTRecursive`
for any natural-number multiplier `natMul` satisfying `∀ a b, natMul a b = a * b`. -/
theorem computableFastDFTRecursiveWithMul_eq_of_mul_eq (natMul : ℕ → ℕ → ℕ)
    (hmul : ∀ a b : ℕ, natMul a b = a * b)
    {K p B_in : ℕ} (tree : ScheduleIntTree K p B_in)
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    computableFastDFTRecursiveWithMul natMul tree xFixed =
      computableFastDFTRecursive tree xFixed := by
  have hsmul : ∀ a b : ℤ, signedMulFromNatMul natMul a b = a * b :=
    signedMulFromNatMul_eq_mul natMul hmul
  have hsmul_std : ∀ a b : ℤ, signedMulFromNatMul (· * ·) a b = a * b :=
    signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
  induction tree with
  | leaf K p B_in leafTwiddles =>
    unfold computableFastDFTRecursiveWithMul computableFastDFTRecursive
    exact baseRadix2FFTFixedWithMul_eq_baseRadix2FFTFixed _ hsmul K p leafTwiddles xFixed
  | node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child ih =>
    unfold computableFastDFTRecursiveWithMul computableFastDFTRecursive
    dsimp only
    simp only [memoizeFin_eq, memoizeFin2_eq]
    have hspread :
        kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul natMul)
          (t1Ell K) (rEll K) m1 (scheduleSlotBits K p B_in m1) (qChildEll K p) (qChildEll K p)
          (rEll_pos K)
          (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K)
            (fun j => FixedComplex.rescale (qChildEll K p) (xFixed j)))
          filterTap =
        kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
          (t1Ell K) (rEll K) m1 (scheduleSlotBits K p B_in m1) (qChildEll K p) (qChildEll K p)
          (rEll_pos K)
          (oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K)
            (fun j => FixedComplex.rescale (qChildEll K p) (xFixed j)))
          filterTap := by
      rw [kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq _ hsmul,
        kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq _ hsmul_std]
    rw [hspread]
    simp only [FixedComplex.mulRoundedWith_eq_mulRounded _ hsmul,
      nyquistColumnSolveFixedWithMul_eq_nyquistColumnSolveFixed _ hsmul,
      cyclicBidiagPrevSolveFixedWithMul_eq_cyclicBidiagPrevSolveFixed _ hsmul, ih]

theorem toComplex_freqScatter {t1 r R q : ℕ} (hR : R = t1 * r)
    (M : Fin t1 → Fin r → FixedComplex q) (u : Fin R) :
    (freqScatter t1 r hR M u).toComplex =
      freqScatter t1 r hR (fun u1 u2 => (M u1 u2).toComplex) u := rfl

/-- **Exact Bridge Between Computable Integer `computableFastDFTRecursive` and Analytic
`fastDFTRecursiveSched` (`computableFastDFTRecursive_canonical_eq_fastDFTRecursiveSched`)**:
For every `(K, p, B_in)` and every fixed-point input vector `xFixed : Fin (2 ^ K) → FixedComplex (p + 2)`,
running the computable pure-integer operator `computableFastDFTRecursive` on
`canonicalScheduleIntTree K p B_in` produces the **exact same** `FixedComplex (p + 2)` output
as `fastDFTRecursiveSched K p B_in (fun j => (xFixed j).toComplex)`. -/
theorem computableFastDFTRecursive_canonical_eq_fastDFTRecursiveSched (K : ℕ) :
    ∀ (p B_in : ℕ) (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)),
      computableFastDFTRecursive (canonicalScheduleIntTree K p B_in) xFixed =
        fastDFTRecursiveSched K p B_in (fun j => (xFixed j).toComplex) := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro p B_in xFixed
    rw [canonicalScheduleIntTree, fastDFTRecursiveSched]
    split_ifs with hcond
    · have hK2 : 2 ≤ K := hcond.2
      have hk2_lt : k2Ell K < K := by unfold k2Ell; omega
      haveI : NeZero (t1Ell K) := ⟨ne_of_gt (t1Ell_pos K)⟩
      unfold computableFastDFTRecursive
      dsimp only
      simp only [memoizeFin_eq, memoizeFin2_eq]
      have hsmul_std : ∀ a b : ℤ, signedMulFromNatMul (· * ·) a b = a * b :=
        signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
      rw [kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq _ hsmul_std]
      have hresc_in :
          (fun j : Fin (2 ^ K) => FixedComplex.rescale (qChildEll K p) (xFixed j)) =
            (fun j : Fin (2 ^ K) => quantizeComplexFixed (qChildEll K p) (xFixed j).toComplex) := by
        funext j
        exact FixedComplex.rescale_eq_quantizeComplexFixed _ _
      rw [hresc_in]
      set U_gathered : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
        oddStrideGather (t1Ell K) (rEll K) (Nat.two_pow_pos K)
          (fun j => quantizeComplexFixed (qChildEll K p) (xFixed j).toComplex)
      set U_spreadFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
        kroneckerMatrixSpreadFixed (t1Ell K) (rEll K) (m1Ell K p)
          (scheduleSlotBits K p B_in (m1Ell K p)) (qChildEll K p) (qChildEll K p) (rEll_pos K)
          U_gathered (levelFilterTapFixed K p)
      set U_preFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
        fun j1 k2 =>
          FixedComplex.mulRounded
            (quantizeComplexFixed (qChildEll K p) (zetaPow (rEll K) (k2.val : ℤ)))
            (U_spreadFixed j1 k2)
      set Q_synFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
        radix2SyntheticFFTFixed (k1Ell K) (c1Ell K) U_preFixed
      set Q_postFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
        fun v1 k2 =>
          FixedComplex.mulRounded
            (quantizeComplexFixed (qChildEll K p) (zetaPow (rEll K) (-(k2.val : ℤ))))
            (Q_synFixed v1 k2)
      have hU_pre : (fun j1 k2 => (U_preFixed j1 k2).toComplex) =
          preTwistQuantRoots (qChildEll K p) (fun j1 k2 => (U_spreadFixed j1 k2).toComplex) := by
        funext j1 k2
        exact toComplex_mulRounded_zetaPow_eq_preTwistQuantRoots (qChildEll K p) U_spreadFixed j1 k2
      have hQ_syn : (fun v1 k2 => (Q_synFixed v1 k2).toComplex) =
          radix2SyntheticFFTQuant (qChildEll K p) (k1Ell K) (c1Ell K)
            (preTwistQuantRoots (qChildEll K p) (fun j1 k2 => (U_spreadFixed j1 k2).toComplex)) := by
        funext v1 k2
        rw [toComplex_radix2SyntheticFFTFixed]
        exact congrFun (congrFun (congrArg (radix2SyntheticFFTQuant (qChildEll K p) (k1Ell K) (c1Ell K)) hU_pre) v1) k2
      have hQ_post : ∀ v1 : Fin (t1Ell K),
          (fun k2 => (Q_postFixed v1 k2).toComplex) =
            postTwistQuantRoots (qChildEll K p)
              (radix2SyntheticFFTQuant (qChildEll K p) (k1Ell K) (c1Ell K)
                (preTwistQuantRoots (qChildEll K p) (fun j1 k2 => (U_spreadFixed j1 k2).toComplex))) v1 := by
        intro v1
        funext k2
        rw [toComplex_mulRounded_zetaPow_eq_postTwistQuantRoots (qChildEll K p) Q_synFixed v1 k2, hQ_syn]
      set Q_hatFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
        fun v1 =>
          computableFastDFTRecursive
            (canonicalScheduleIntTree (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
            (Q_postFixed v1)
      set Y_matFixed : Fin (t1Ell K) → Fin (rEll K) → FixedComplex (qChildEll K p) :=
        oddColScatter (t1Ell_pos K) ⟨k1Ell K, rfl⟩ Q_hatFixed
      have hY_mat : ∀ (u2 : Fin (rEll K)),
          (fun m : Fin (t1Ell K) => (Y_matFixed m u2).toComplex) =
            (fun m : Fin (t1Ell K) =>
              oddColScatter (t1Ell_pos K) ⟨k1Ell K, rfl⟩
                (fun v1 u2 =>
                  (fastDFTRecursiveSched (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in)
                    (postTwistQuantRoots (qChildEll K p)
                      (radix2SyntheticFFTQuant (qChildEll K p) (k1Ell K) (c1Ell K)
                        (preTwistQuantRoots (qChildEll K p)
                          (fun j1 k2 => (U_spreadFixed j1 k2).toComplex))) v1)
                    u2).toComplex) m u2) := by
        intro u2
        funext u1
        unfold Y_matFixed oddColScatter Q_hatFixed
        dsimp only
        let v1 := oddColKeyMinusInv (t1Ell K) (t1Ell_pos K) u2.val u1
        have h1 := congrFun
          (ih (k2Ell K) hk2_lt (pChildEll K p) (childScheduleBIn K p B_in) (Q_postFixed v1)) u2
        have h2 := congrFun
          (congrArg (fastDFTRecursiveSched (k2Ell K) (pChildEll K p) (childScheduleBIn K p B_in))
            (hQ_post v1)) u2
        exact congrArg FixedComplex.toComplex (h1.trans h2)
      funext u
      rw [FixedComplex.rescale_eq_quantizeComplexFixed]
      congr 1
      rw [toComplex_freqScatter]
      refine congrFun (congrArg (freqScatter (t1Ell K) (rEll K) (t1Ell_mul_rEll K).symm) ?_) u
      funext u1 u2
      split_ifs with hu2
      · rw [nyquistModeSumFixed_eq_quantizeComplexFixed,
          toComplex_nyquistColumnSolveFixed, hY_mat]
        rfl
      · rw [toComplex_cyclicBidiagPrevSolveFixed, hY_mat]
        rfl
    · funext u
      exact baseRadix2FFTFixed_canonical_eq K p xFixed u

/-- $m$-stage radix-2 butterfly FFT error bound for `radix2FFT1DFixed` with any leaf twiddle table
satisfying the $(18/25) \cdot 2^{-q}$ approximation bound. -/
theorem vecInfNorm_radix2FFT1DFixed_sub_normDFT1D_le_of_roots (K q : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex q)
    (hroots : ∀ u : Fin (2 ^ K),
      ‖(leafTwiddles u).toComplex - expTwoPiI ((u.val : ℝ) / ((2 ^ K : ℕ) : ℝ))‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(q : ℤ)))
    (m : ℕ) (hm : m ≤ K) :
    ∀ (xBase : Fin (2 ^ m) → FixedComplex q) (x : Fin (2 ^ m) → ℂ)
      (_hx : ∀ j : Fin (2 ^ m), (xBase j).toComplex = x j),
      vecInfNorm (fun u =>
        (radix2FFT1DFixed K q leafTwiddles m hm xBase u).toComplex - normDFT1D x u) ≤
        (4 * ((2 ^ m : ℕ) : ℝ) - 3) * ((18 / 25 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))) *
          max 1 (vecInfNorm x) := by
  set ε : ℝ := (18 / 25 : ℝ) * (2 : ℝ) ^ (-(q : ℤ))
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(q : ℤ)) := zpow_pos (by norm_num) _
  have hε_pos : 0 < ε := mul_pos (by norm_num) h2q_pos
  have hε_le_one : ε ≤ 1 := by
    have h1 : (2 : ℝ) ^ (-(q : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    dsimp [ε]
    nlinarith
  have hq_le_ε : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) ≤ ε := by
    dsimp [ε]
    have hsqrt := sqrt_two_le
    nlinarith
  induction m with
  | zero =>
    intro xBase x hx
    have hM_nn : 0 ≤ max 1 (vecInfNorm x) := le_trans zero_le_one (le_max_left 1 _)
    apply vecInfNorm_le _ (by positivity)
    intro u
    rw [← radix2FFT1DExact_eq_normDFT1D 0 x u]
    unfold radix2FFT1DFixed radix2FFT1DFixedWithMul radix2FFT1DExact
    rw [hx u, sub_self, norm_zero]
    positivity
  | succ m ih =>
    intro xBase x hx
    set M : ℝ := max 1 (vecInfNorm x)
    have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
    have hM_ge_norm : vecInfNorm x ≤ M := le_max_right 1 (vecInfNorm x)
    have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
    set hm' : m ≤ K := Nat.le_of_succ_le hm
    let xE : Fin (2 ^ m) → ℂ := fun j => x (evenSubIndex m j)
    let xO : Fin (2 ^ m) → ℂ := fun j => x (oddSubIndex m j)
    let xBaseE : Fin (2 ^ m) → FixedComplex q := fun j => xBase (evenSubIndex m j)
    let xBaseO : Fin (2 ^ m) → FixedComplex q := fun j => xBase (oddSubIndex m j)
    have hxE_norm : vecInfNorm xE ≤ M :=
      vecInfNorm_le xE hM_pos.le (fun j => (norm_le_vecInfNorm x (evenSubIndex m j)).trans hM_ge_norm)
    have hxO_norm : vecInfNorm xO ≤ M :=
      vecInfNorm_le xO hM_pos.le (fun j => (norm_le_vecInfNorm x (oddSubIndex m j)).trans hM_ge_norm)
    have hxE_max : max 1 (vecInfNorm xE) ≤ M := max_le hM_ge_one hxE_norm
    have hxO_max : max 1 (vecInfNorm xO) ≤ M := max_le hM_ge_one hxO_norm
    set Cm : ℝ := 4 * ((2 ^ m : ℕ) : ℝ) - 3
    have h2m_ge_one : (1 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have hCm_pos : 0 < Cm := by change 0 < 4 * ((2 ^ m : ℕ) : ℝ) - 3; linarith
    have h2m1_pos : 0 < 4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3 := by
      have h2m1_ge : (1 : ℝ) ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
      linarith
    apply vecInfNorm_le _ (by positivity)
    intro u
    rw [← radix2FFT1DExact_eq_normDFT1D (m + 1) x u]
    unfold radix2FFT1DFixed radix2FFT1DFixedWithMul radix2FFT1DExact
    dsimp only
    simp only [memoizeFin_eq]
    rw [radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl),
      radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl),
      FixedComplex.mulRoundedWith_eq_mulRounded (· * ·) (fun _ _ => rfl)]
    set v : Fin (2 ^ m) := ⟨u.val % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩
    set wIdx : Fin (2 ^ K) := ⟨v.val * 2 ^ (K - (m + 1)), mul_two_pow_sub_lt hm v⟩
    set w_true : ℂ := expTwoPiI ((v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ))
    set wFixed : FixedComplex q := leafTwiddles wIdx
    set w : ℂ := wFixed.toComplex
    set EFixed : FixedComplex q := radix2FFT1DFixed K q leafTwiddles m hm' xBaseE v
    set OFixed : FixedComplex q := radix2FFT1DFixed K q leafTwiddles m hm' xBaseO v
    set Ev : ℂ := EFixed.toComplex
    set Ov : ℂ := OFixed.toComplex
    set Ev_true : ℂ := radix2FFT1DExact m xE v
    set Ov_true : ℂ := radix2FFT1DExact m xO v
    set tFixed : FixedComplex q := FixedComplex.mulRounded wFixed OFixed
    set t : ℂ := tFixed.toComplex
    have ht_eq : t = quantizeComplex q (w * Ov) :=
      FixedComplex.toComplex_mulRounded wFixed OFixed
    have hEv_eq : Ev_true = normDFT1D xE v := radix2FFT1DExact_eq_normDFT1D m xE v
    have hOv_eq : Ov_true = normDFT1D xO v := radix2FFT1DExact_eq_normDFT1D m xO v
    have hEv_err : ‖Ev - Ev_true‖ ≤ Cm * ε * M := by
      rw [hEv_eq]
      calc ‖Ev - normDFT1D xE v‖
          ≤ vecInfNorm (fun k => (radix2FFT1DFixed K q leafTwiddles m hm' xBaseE k).toComplex - normDFT1D xE k) :=
            norm_le_vecInfNorm (fun k => (radix2FFT1DFixed K q leafTwiddles m hm' xBaseE k).toComplex - normDFT1D xE k) v
        _ ≤ Cm * ε * max 1 (vecInfNorm xE) :=
            ih hm' xBaseE xE (fun j => hx (evenSubIndex m j))
        _ ≤ Cm * ε * M := mul_le_mul_of_nonneg_left hxE_max (by positivity)
    have hOv_err : ‖Ov - Ov_true‖ ≤ Cm * ε * M := by
      rw [hOv_eq]
      calc ‖Ov - normDFT1D xO v‖
          ≤ vecInfNorm (fun k => (radix2FFT1DFixed K q leafTwiddles m hm' xBaseO k).toComplex - normDFT1D xO k) :=
            norm_le_vecInfNorm (fun k => (radix2FFT1DFixed K q leafTwiddles m hm' xBaseO k).toComplex - normDFT1D xO k) v
        _ ≤ Cm * ε * max 1 (vecInfNorm xO) :=
            ih hm' xBaseO xO (fun j => hx (oddSubIndex m j))
        _ ≤ Cm * ε * M := mul_le_mul_of_nonneg_left hxO_max (by positivity)
    have hOv_true_norm : ‖Ov_true‖ ≤ M := by
      rw [hOv_eq]; exact (norm_normDFT1D_le xO v).trans hxO_norm
    have hpowK : (2 ^ K : ℕ) = 2 ^ (m + 1) * 2 ^ (K - (m + 1)) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hm]
    have harg : ((wIdx.val : ℝ) / ((2 ^ K : ℕ) : ℝ)) =
        (v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) := by
      have hpos : ((2 ^ (K - (m + 1)) : ℕ) : ℝ) ≠ 0 := by positivity
      change (((v.val * 2 ^ (K - (m + 1)) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) =
        (v.val : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)
      rw [hpowK]; push_cast; field_simp [hpos]
    have hw_sub : ‖w - w_true‖ ≤ ε := by
      dsimp [w, wFixed, w_true]
      rw [← harg]
      exact hroots wIdx
    have hw_norm : ‖w‖ ≤ 2 := by
      have htri : ‖w‖ ≤ ‖w - w_true‖ + ‖w_true‖ := by simpa using norm_add_le (w - w_true) w_true
      have hw1 : ‖w_true‖ = 1 := norm_expTwoPiI _
      linarith
    have ht_err : ‖t - w_true * Ov_true‖ ≤ (2 * Cm + 2) * ε * M := by
      have hdecomp : t - w_true * Ov_true =
          (t - w * Ov) + (w * (Ov - Ov_true) + (w - w_true) * Ov_true) := by ring
      rw [hdecomp]
      have h0 : ‖t - w * Ov‖ ≤ ε * M := by
        rw [ht_eq]
        have hq : ‖quantizeComplex q (w * Ov) - w * Ov‖ ≤ ε :=
          (norm_quantizeComplex_sub_self_le q (w * Ov)).trans hq_le_ε
        calc ‖quantizeComplex q (w * Ov) - w * Ov‖ ≤ ε * 1 := by linarith
          _ ≤ ε * M := by gcongr
      have h1 : ‖w * (Ov - Ov_true)‖ ≤ 2 * Cm * ε * M := by
        rw [norm_mul]
        calc ‖w‖ * ‖Ov - Ov_true‖ ≤ 2 * (Cm * ε * M) :=
              mul_le_mul hw_norm hOv_err (norm_nonneg _) (by positivity)
          _ = 2 * Cm * ε * M := by ring
      have h2 : ‖(w - w_true) * Ov_true‖ ≤ ε * M := by
        rw [norm_mul]
        exact mul_le_mul hw_sub hOv_true_norm (norm_nonneg _) hε_pos.le
      have htri1 := norm_add_le (t - w * Ov) (w * (Ov - Ov_true) + (w - w_true) * Ov_true)
      have htri2 := norm_add_le (w * (Ov - Ov_true)) ((w - w_true) * Ov_true)
      linarith
    have hcoeff_step : ((3 / 2 : ℝ) * Cm + 2) * ε * M ≤
        (4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3) * ε * M := by
      have hlin : (3 / 2 : ℝ) * Cm + 2 ≤ 4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3 := by
        change (3 / 2 : ℝ) * (4 * ((2 ^ m : ℕ) : ℝ) - 3) + 2 ≤
          4 * ((2 ^ (m + 1) : ℕ) : ℝ) - 3
        have hpow : ((2 ^ (m + 1) : ℕ) : ℝ) = 2 * ((2 ^ m : ℕ) : ℝ) := by
          rw [Nat.pow_succ', Nat.cast_mul, Nat.cast_ofNat]
        rw [hpow]; linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlin hε_pos.le) hM_pos.le
    change ‖(if u.val < 2 ^ m then (EFixed + tFixed).halfRounded
        else (EFixed - tFixed).halfRounded).toComplex -
        (if u.val < 2 ^ m then (Ev_true + w_true * Ov_true) / 2
        else (Ev_true - w_true * Ov_true) / 2)‖ ≤ _
    split_ifs with hu
    · rw [FixedComplex.toComplex_halfRounded, FixedComplex.toComplex_add_op]
      have hhalf : ‖(Ev + t) / 2 - (Ev_true + w_true * Ov_true) / 2‖ ≤
          ((3 / 2 : ℝ) * Cm + 1) * ε * M := by
        have hsub : (Ev + t) / 2 - (Ev_true + w_true * Ov_true) / 2 =
            ((Ev - Ev_true) + (t - w_true * Ov_true)) / 2 := by ring
        rw [hsub, norm_div, Complex.norm_ofNat]
        have htri := norm_add_le (Ev - Ev_true) (t - w_true * Ov_true)
        linarith
      have hq_out : ‖quantizeComplex q ((Ev + t) / 2) - (Ev + t) / 2‖ ≤ ε * M := by
        have hq : ‖quantizeComplex q ((Ev + t) / 2) - (Ev + t) / 2‖ ≤ ε :=
          (norm_quantizeComplex_sub_self_le q ((Ev + t) / 2)).trans hq_le_ε
        calc ‖quantizeComplex q ((Ev + t) / 2) - (Ev + t) / 2‖ ≤ ε * 1 := by linarith
          _ ≤ ε * M := by gcongr
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (quantizeComplex q ((Ev + t) / 2)) ((Ev + t) / 2) ((Ev_true + w_true * Ov_true) / 2)
      linarith
    · rw [FixedComplex.toComplex_halfRounded, FixedComplex.toComplex_sub_op]
      have hhalf : ‖(Ev - t) / 2 - (Ev_true - w_true * Ov_true) / 2‖ ≤
          ((3 / 2 : ℝ) * Cm + 1) * ε * M := by
        have hsub : (Ev - t) / 2 - (Ev_true - w_true * Ov_true) / 2 =
            ((Ev - Ev_true) - (t - w_true * Ov_true)) / 2 := by ring
        rw [hsub, norm_div, Complex.norm_ofNat]
        have htri := norm_sub_le (Ev - Ev_true) (t - w_true * Ov_true)
        linarith
      have hq_out : ‖quantizeComplex q ((Ev - t) / 2) - (Ev - t) / 2‖ ≤ ε * M := by
        have hq : ‖quantizeComplex q ((Ev - t) / 2) - (Ev - t) / 2‖ ≤ ε :=
          (norm_quantizeComplex_sub_self_le q ((Ev - t) / 2)).trans hq_le_ε
        calc ‖quantizeComplex q ((Ev - t) / 2) - (Ev - t) / 2‖ ≤ ε * 1 := by linarith
          _ ≤ ε * M := by gcongr
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (quantizeComplex q ((Ev - t) / 2)) ((Ev - t) / 2) ((Ev_true - w_true * Ov_true) / 2)
      linarith

/-- Base-leaf radix-2 FFT error bound for `baseRadix2FFTFixed` with any leaf twiddle table
satisfying the $(18/25) \cdot 2^{-q_{\text{base}}}$ approximation bound. -/
theorem vecInfNorm_baseRadix2FFTFixed_sub_normDFT1D_le_of_roots (K p : ℕ)
    (leafTwiddles : Fin (2 ^ K) → FixedComplex (qBaseEll K p))
    (hroots : ∀ u : Fin (2 ^ K),
      ‖(leafTwiddles u).toComplex - expTwoPiI ((u.val : ℝ) / ((2 ^ K : ℕ) : ℝ))‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qBaseEll K p : ℤ)))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2)) :
    let x : Fin (2 ^ K) → ℂ := fun j => (xFixed j).toComplex
    vecInfNorm (fun u =>
      (baseRadix2FFTFixed K p leafTwiddles xFixed u).toComplex - normDFT1D x u) ≤
      (2 : ℝ) ^ (-(p : ℤ)) * max 1 (vecInfNorm x) := by
  intro x
  let qBase : ℕ := qBaseEll K p
  let M : ℝ := max 1 (vecInfNorm x)
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hp_le_qBase : p + 2 ≤ qBase := by unfold qBase qBaseEll; omega
  let xBase : Fin (2 ^ K) → FixedComplex qBase := fun j => FixedComplex.rescale qBase (xFixed j)
  have hxBase : ∀ j : Fin (2 ^ K), (xBase j).toComplex = x j :=
    fun j => FixedComplex.toComplex_rescale_of_le hp_le_qBase (xFixed j)
  have hloop := vecInfNorm_radix2FFT1DFixed_sub_normDFT1D_le_of_roots K qBase leafTwiddles
    hroots K (le_refl K) xBase x hxBase
  have hpow_qBase :
      ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(qBase : ℤ)) =
        (1 / 16 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    have hexp : -(qBase : ℤ) = -(K : ℤ) + (-(p : ℤ) + (-4 : ℤ)) := by
      change -((p + K + 4 : ℕ) : ℤ) = -(K : ℤ) + (-(p : ℤ) + (-4 : ℤ)); omega
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    have hcancel : ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(K : ℤ)) = 1 := by
      push_cast; exact two_pow_mul_two_zpow_neg K
    calc ((2 ^ K : ℕ) : ℝ) * ((2 : ℝ) ^ (-(K : ℤ)) * ((2 : ℝ) ^ (-(p : ℤ)) * (2 : ℝ) ^ (-4 : ℤ)))
        = (((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(K : ℤ))) *
            ((2 : ℝ) ^ (-4 : ℤ) * (2 : ℝ) ^ (-(p : ℤ))) := by ring
      _ = (1 / 16 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by rw [hcancel, one_mul]; norm_num
  have hloop_bound :
      (4 * ((2 ^ K : ℕ) : ℝ) - 3) * ((18 / 25 : ℝ) * (2 : ℝ) ^ (-(qBase : ℤ))) * M ≤
        (18 / 100 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hle1 : 4 * ((2 ^ K : ℕ) : ℝ) - 3 ≤ 4 * ((2 ^ K : ℕ) : ℝ) := by linarith
    calc (4 * ((2 ^ K : ℕ) : ℝ) - 3) * ((18 / 25 : ℝ) * (2 : ℝ) ^ (-(qBase : ℤ))) * M
        ≤ (4 * ((2 ^ K : ℕ) : ℝ)) * ((18 / 25 : ℝ) * (2 : ℝ) ^ (-(qBase : ℤ))) * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle1 (by positivity)) hM_pos.le
      _ = (72 / 25 : ℝ) * (((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(qBase : ℤ))) * M := by ring
      _ = (18 / 100 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by rw [hpow_qBase]; ring
  apply vecInfNorm_le _ (by positivity)
  intro u
  unfold baseRadix2FFTFixed baseRadix2FFTFixedWithMul
  simp only [memoizeFin_eq]
  rw [radix2FFT1DFixedWithMul_eq_radix2FFT1DFixed (· * ·) (fun _ _ => rfl),
    FixedComplex.toComplex_rescale]
  set y : ℂ := (radix2FFT1DFixed K qBase leafTwiddles K (le_refl K) xBase u).toComplex
  have hy_err : ‖y - normDFT1D x u‖ ≤ (18 / 100 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    (norm_le_vecInfNorm _ u).trans (hloop.trans hloop_bound)
  have hout_sub : ‖quantizeComplex (p + 2) y - y‖ ≤
      (18 / 100 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have h := norm_quantizeComplex_sub_self_le (p + 2) y
    have hexp : -((p + 2 : ℕ) : ℤ) = -(p : ℤ) + (-2 : ℤ) := by push_cast; ring
    have hpow : (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
      rw [hexp, zpow_add₀ (by norm_num)]; norm_num; ring
    rw [hpow] at h
    have hsqrt := sqrt_two_le
    have h1 : ‖quantizeComplex (p + 2) y - y‖ ≤ (18 / 100 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * 1 := by
      nlinarith
    exact h1.trans (by gcongr)
  have htri := norm_sub_le_norm_sub_add_norm_sub (quantizeComplex (p + 2) y) y (normDFT1D x u)
  have hcoeff : (36 / 100 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M ≤ (2 : ℝ) ^ (-(p : ℤ)) * M := by
    nlinarith
  linarith

/-- Generalized per-level error budget contraction for any window length $W \le 2 p_{\text{child}} + 1$
(`level_error_budget_le_of_W_le`, Lemma 6.5(1)–(2) (`lem:forward`)). -/
theorem level_error_budget_le_of_W_le {K p : ℕ} {W : ℝ}
    (hK : 1 ≤ K) (hp : 1 ≤ p) (hleaf : 4 * p * p < 2 ^ K)
    (hW_nn : 0 ≤ W) (hW : W ≤ 2 * (pChildEll K p : ℝ) + 1) :
    (236 / 100 : ℝ) * (t1Ell K : ℝ) *
      ((((W + 4) * (2 : ℝ) ^ (-(pChildEll K p : ℤ))) +
        (W + (54 / 100 : ℝ) * (K : ℝ) + 7) *
          (2 : ℝ) ^ (-(pChildEll K p : ℤ)) +
        (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ)))) +
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) ≤
      (2 : ℝ) ^ (-(p : ℤ)) := by
  have hp_le : p ≤ 2 ^ K := by nlinarith
  have hK_le : K ≤ 2 ^ K := le_of_lt Nat.lt_two_pow_self
  have h1_le : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  set R : ℝ := ((2 ^ K : ℕ) : ℝ)
  have ht1_le : (t1Ell K : ℝ) ≤ R := Nat.cast_le.mpr (t1Ell_le_two_pow K)
  have hp_cast : (p : ℝ) ≤ R := Nat.cast_le.mpr hp_le
  have hK_cast : (K : ℝ) ≤ R := Nat.cast_le.mpr hK_le
  have h1_cast : (1 : ℝ) ≤ R := by
    simpa [R] using (Nat.cast_le.mpr h1_le : ((1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ))
  have hpChild_eq : (pChildEll K p : ℝ) = (p : ℝ) + 2 * (K : ℝ) + 12 := by
    have h := pChildEll_eq K p
    exact_mod_cast h
  have hW_le_R : W ≤ 31 * R := by linarith
  have hcoeff_bound : 2 * W + (54 / 100 : ℝ) * (K : ℝ) + 11 ≤ 74 * R := by linarith
  have hprod_bound :
      (t1Ell K : ℝ) * (2 * W + (54 / 100 : ℝ) * (K : ℝ) + 11) ≤ 74 * (R * R) := by
    calc (t1Ell K : ℝ) * (2 * W + (54 / 100 : ℝ) * (K : ℝ) + 11)
        ≤ R * (74 * R) := mul_le_mul ht1_le hcoeff_bound (by positivity) (by positivity)
      _ = 74 * (R * R) := by ring
  have hzpos : (0 : ℝ) < (2 : ℝ) ^ (-(pChildEll K p : ℤ)) := zpow_pos (by norm_num) _
  have hchild :
      (t1Ell K : ℝ) * (2 * W + (54 / 100 : ℝ) * (K : ℝ) + 11) *
        (2 : ℝ) ^ (-(pChildEll K p : ℤ)) ≤
      (74 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
    calc (t1Ell K : ℝ) * (2 * W + (54 / 100 : ℝ) * (K : ℝ) + 11) *
          (2 : ℝ) ^ (-(pChildEll K p : ℤ))
        ≤ 74 * (((2 ^ K : ℕ) : ℝ) * ((2 ^ K : ℕ) : ℝ)) * (2 : ℝ) ^ (-(pChildEll K p : ℤ)) :=
          mul_le_mul_of_nonneg_right hprod_bound hzpos.le
      _ = 74 * (((2 ^ K : ℕ) : ℝ) * ((2 ^ K : ℕ) : ℝ) * (2 : ℝ) ^ (-(pChildEll K p : ℤ))) := by ring
      _ = (74 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
          rw [two_pow_sq_mul_two_zpow_neg_pChildEll]; ring
  have hwork := t1Ell_mul_two_zpow_neg_pWorkEll_le (p := p) hK
  have hquant := sqrt_two_div_four_le
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hexpand :
      (236 / 100 : ℝ) * (t1Ell K : ℝ) *
        ((((W + 4) * (2 : ℝ) ^ (-(pChildEll K p : ℤ))) +
          (W + (54 / 100 : ℝ) * (K : ℝ) + 7) *
            (2 : ℝ) ^ (-(pChildEll K p : ℤ)) +
          (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ)))) =
      (236 / 100 : ℝ) * (91 / 100 : ℝ) * ((t1Ell K : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ))) +
        (236 / 100 : ℝ) *
          ((t1Ell K : ℝ) * (2 * W + (54 / 100 : ℝ) * (K : ℝ) + 11) *
            (2 : ℝ) ^ (-(pChildEll K p : ℤ))) := by ring
  rw [hexpand]
  have hterm1 :
      (236 / 100 : ℝ) * (91 / 100 : ℝ) * ((t1Ell K : ℝ) * (2 : ℝ) ^ (-(pWorkEll K p : ℤ))) ≤
      (236 / 100 : ℝ) * (91 / 100 : ℝ) * ((1 / 128 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) :=
    mul_le_mul_of_nonneg_left hwork (by norm_num)
  have hterm2 :
      (236 / 100 : ℝ) *
        ((t1Ell K : ℝ) * (2 * W + (54 / 100 : ℝ) * (K : ℝ) + 11) *
          (2 : ℝ) ^ (-(pChildEll K p : ℤ))) ≤
      (236 / 100 : ℝ) * ((74 / 4096 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) :=
    mul_le_mul_of_nonneg_left hchild (by norm_num)
  have hterm3 :
      (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) ≤ (18 / 50 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) :=
    mul_le_mul_of_nonneg_right hquant hp_pos.le
  linarith

/-- Matrix $\ell_\infty$ error bound for `FixedComplex.mulRounded` against unit-norm twist roots
(`matInfNorm_mulRounded_root_sub_le`). -/
theorem matInfNorm_mulRounded_root_sub_le {q t1 r : ℕ}
    (rootFixed : Fin r → FixedComplex q) (rootTrue : Fin r → ℂ)
    (P_fixed : Fin t1 → Fin r → FixedComplex q) (P_true : Fin t1 → Fin r → ℂ)
    {ε : ℝ} (hε_nn : 0 ≤ ε)
    (hroot : ∀ k2 : Fin r, ‖(rootFixed k2).toComplex - rootTrue k2‖ ≤ ε)
    (hroot_norm : ∀ k2 : Fin r, ‖rootTrue k2‖ = 1)
    (hq : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(q : ℤ)) ≤ ε) :
    matInfNorm (fun j1 k2 =>
      (FixedComplex.mulRounded (rootFixed k2) (P_fixed j1 k2)).toComplex -
        rootTrue k2 * P_true j1 k2) ≤
      matInfNorm (fun j1 k2 => (P_fixed j1 k2).toComplex - P_true j1 k2) +
        (1 + matInfNorm (fun j1 k2 => (P_fixed j1 k2).toComplex)) * ε := by
  have h_rhs_nn : 0 ≤ matInfNorm (fun j1 k2 => (P_fixed j1 k2).toComplex - P_true j1 k2) +
      (1 + matInfNorm (fun j1 k2 => (P_fixed j1 k2).toComplex)) * ε := by
    have := matInfNorm_nonneg (fun j1 k2 => (P_fixed j1 k2).toComplex - P_true j1 k2)
    have := matInfNorm_nonneg (fun j1 k2 => (P_fixed j1 k2).toComplex)
    positivity
  apply matInfNorm_le _ h_rhs_nn
  intro j1 k2
  rw [FixedComplex.toComplex_mulRounded]
  set z_q : ℂ := (rootFixed k2).toComplex
  set z : ℂ := rootTrue k2
  set p_q : ℂ := (P_fixed j1 k2).toComplex
  set p : ℂ := P_true j1 k2
  set w_q : ℂ := z_q * p_q
  set w : ℂ := z * p
  have h_decomp : w_q - w = z * (p_q - p) + (z_q - z) * p_q := by dsimp [w_q, w]; ring
  have hw_diff : ‖w_q - w‖ ≤ ‖p_q - p‖ + ‖p_q‖ * ε := by
    rw [h_decomp]
    calc ‖z * (p_q - p) + (z_q - z) * p_q‖
        ≤ ‖z * (p_q - p)‖ + ‖(z_q - z) * p_q‖ := norm_add_le _ _
      _ = ‖p_q - p‖ + ‖z_q - z‖ * ‖p_q‖ := by rw [norm_mul, hroot_norm k2, one_mul, norm_mul]
      _ ≤ ‖p_q - p‖ + ε * ‖p_q‖ := by gcongr; exact hroot k2
      _ = ‖p_q - p‖ + ‖p_q‖ * ε := by ring
  have hq_err : ‖quantizeComplex q w_q - w_q‖ ≤ ε :=
    (norm_quantizeComplex_sub_self_le q w_q).trans hq
  have hpt : ‖quantizeComplex q w_q - w‖ ≤ ‖p_q - p‖ + (1 + ‖p_q‖) * ε := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (quantizeComplex q w_q) w_q w
    linarith
  have h1 : ‖p_q - p‖ ≤ matInfNorm (fun i1 i2 => (P_fixed i1 i2).toComplex - P_true i1 i2) :=
    norm_le_matInfNorm (fun i1 i2 => (P_fixed i1 i2).toComplex - P_true i1 i2) j1 k2
  have h2 : ‖p_q‖ ≤ matInfNorm (fun i1 i2 => (P_fixed i1 i2).toComplex) :=
    norm_le_matInfNorm (fun i1 i2 => (P_fixed i1 i2).toComplex) j1 k2
  have h3 : (1 + ‖p_q‖) * ε ≤ (1 + matInfNorm (fun i1 i2 => (P_fixed i1 i2).toComplex)) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε_nn
  linarith

/-- Step 1 Sinc-Gaussian row-spreading error and norm bound for `computableFastDFTRecursive`
on any valid node (`matInfNorm_computableFastDFTRecursive_step1_sub_le`). -/
theorem matInfNorm_computableFastDFTRecursive_step1_sub_le {K p B_in m1 : ℕ}
    (_hp : 8 ≤ p) (hm1_ge : m1Ell K p ≤ m1) (hm1_le : m1 ≤ pChildEll K p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (htap_fits : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      FitsSignedWord (qChildEll K p + 1) (filterTap j1 d))
    (htap_abs : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))| ≤ 1)
    (htap_err : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
        IntMul.filterTap (alphaEll K p) m1 (t1Ell K) j1 d| ≤
        (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in) :
    let t1 := t1Ell K
    let r := rEll K
    let qChild := qChildEll K p
    let pChild := pChildEll K p
    let alpha := alphaEll K p
    let B_slot := scheduleSlotBits K p B_in m1
    let hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    let hr_pos : 0 < r := rEll_pos K
    let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let x : Fin (2 ^ K) → ℂ := fun j => (xFixed j).toComplex
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => FixedComplex.rescale qChild (xFixed j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
        t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap
    let U_spread : Fin t1 → Fin r → ℂ := fun j1 k2 => (U_spreadFixed j1 k2).toComplex
    let U_true : Fin t1 → Fin r → ℂ :=
      spreadArray hr_pos m1 xCast (fun j1 d => (IntMul.filterTap alpha m1 t1 j1 d : ℂ))
    let W := ((2 * m1 + 1 : ℕ) : ℝ)
    let M := max 1 (vecInfNorm x)
    matInfNorm U_true ≤ W * M ∧
      matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) ≤
        (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M ∧
      matInfNorm U_spread ≤ (W + 1) * M := by
  intro t1 r qChild pChild alpha B_slot hR_pos hr_pos hR_eq x xCast
    U_gathered U_spreadFixed U_spread U_true W M
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_ge_norm : vecInfNorm x ≤ M := le_max_right 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have hcard_Icc : (Finset.Icc (-(m1 : ℤ)) (m1 : ℤ)).card = 2 * m1 + 1 := by
    rw [Int.card_Icc]; omega
  have hW_pos : 0 < W := by change 0 < ((2 * m1 + 1 : ℕ) : ℝ); positivity
  have hU_true_le : matInfNorm U_true ≤ W * M := by
    apply matInfNorm_le _ (by positivity)
    intro j1 k2
    unfold U_true spreadArray
    have hterm : ∀ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
        ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
          (IntMul.filterTap alpha m1 t1 j1 d : ℂ)‖ ≤ M := by
      intro d _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hx_le : ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))‖ ≤ M :=
        (norm_le_vecInfNorm x _).trans hM_ge_norm
      have hf_le : |IntMul.filterTap alpha m1 t1 j1 d| ≤ 1 := abs_filterTap_le_one alpha m1 t1 j1 d
      calc ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))‖ *
            |IntMul.filterTap alpha m1 t1 j1 d|
          ≤ M * 1 := mul_le_mul hx_le hf_le (abs_nonneg _) hM_pos.le
        _ = M := mul_one M
    calc ‖∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
          xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
            (IntMul.filterTap alpha m1 t1 j1 d : ℂ)‖
        ≤ ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
            ‖xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
              (IntMul.filterTap alpha m1 t1 j1 d : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), M := Finset.sum_le_sum hterm
      _ = W * M := by simp [Finset.sum_const, hcard_Icc, W, nsmul_eq_mul]
  have hm1_pos : 0 < m1 := lt_of_lt_of_le (m1Ell_pos K p) hm1_ge
  have hfold_pos : 0 < foldedHalfWidth m1 r := by
    unfold foldedHalfWidth; exact lt_min hm1_pos hr_pos
  have hsmul_std : ∀ a b : ℤ, signedMulFromNatMul (· * ·) a b = a * b :=
    signedMulFromNatMul_eq_mul (· * ·) (fun _ _ => rfl)
  have hstep1_eq : U_spreadFixed =
      refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered filterTap := by
    dsimp [U_spreadFixed]
    rw [kroneckerMatrixSpreadFixedWithMul_eq_of_mul_eq _ hsmul_std]
    funext j1 k2
    exact kroneckerMatrixSpreadFixed_eq_refMatrixSpreadFixed_of_raw_bounds
      t1 r m1 qChild (max (K + 4) (B_in + 1)) qChild qChild hr_pos hfold_pos
      U_gathered filterTap
      (fun i1 i2 => by
        dsimp [U_gathered, oddStrideGather]
        rw [FixedComplex.rescale_eq_quantizeComplexFixed]
        exact wordWidthBounds_quantizeComplexFixed_of_vecInfNorm_le K qChild B_in x hx _)
      htap_fits j1 k2
  have h2q_eq : (2 : ℝ) ^ (-(qChild : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
    have hexp : -(qChild : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by
      change -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ); omega
    rw [hexp, zpow_add₀ (by norm_num)]; norm_num; ring
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(qChild : ℤ)) := zpow_pos (by norm_num) _
  have hsqrt_le : Real.sqrt 2 ≤ (71 / 50 : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 71 / 50)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsub_le : matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) ≤
      (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    apply matInfNorm_le _ (by positivity)
    intro j1 k2
    have hU_ref : U_spread j1 k2 =
        (refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered filterTap j1 k2).toComplex :=
      congrArg FixedComplex.toComplex (congrFun (congrFun hstep1_eq j1) k2)
    rw [hU_ref]
    let fQuant : ℤ → ℝ := fun d => (filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))
    let S_unrounded : ℂ :=
      ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
        quantizeComplex qChild (xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))) *
          (fQuant d : ℂ)
    have hU_gath : ∀ m : Fin r,
        (U_gathered j1 m).toComplex = quantizeComplex qChild (xCast (strideFin j1 m)) := by
      intro m
      dsimp [U_gathered, oddStrideGather]
      rw [FixedComplex.rescale_eq_quantizeComplexFixed]
      change (quantizeComplexFixed qChild (x (strideModIndex t1 r (2 ^ K) hR_pos j1 m))).toComplex = _
      rw [strideModIndex_eq_cast_strideFin hR_pos hR_eq j1 m]
      rfl
    have hround_diff :
        ‖(refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered filterTap j1 k2).toComplex -
            S_unrounded‖ ≤
          (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) := by
      let S_re : ℤ := rawCyclicConv r m1 hr_pos (fun j2 => (U_gathered j1 j2).re) (filterTap j1) k2
      let S_im : ℤ := rawCyclicConv r m1 hr_pos (fun j2 => (U_gathered j1 j2).im) (filterTap j1) k2
      have hre_eq : S_unrounded.re = (S_re : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [S_unrounded, S_re, rawCyclicConv, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        have hmod : cyclicModIndex r hr_pos ((k2.val : ℤ) - d) =
            intModFin r hr_pos ((k2.val : ℤ) - d) := rfl
        rw [hmod, ← hU_gath]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          FixedComplex.toComplex_re, fQuant, Int.cast_mul, zpow_neg, zpow_natCast]
        ring
      have him_eq : S_unrounded.im = (S_im : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [S_unrounded, S_im, rawCyclicConv, Complex.im_sum, Int.cast_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        have hmod : cyclicModIndex r hr_pos ((k2.val : ℤ) - d) =
            intModFin r hr_pos ((k2.val : ℤ) - d) := rfl
        rw [hmod, ← hU_gath]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          FixedComplex.toComplex_im, fQuant, Int.cast_mul, zpow_neg, zpow_natCast]
        ring
      have hre_le :
          |((refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered filterTap j1 k2).toComplex -
              S_unrounded).re| ≤
            (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [refMatrixSpreadFixed, refRowSpreadFixed, Complex.sub_re,
          FixedComplex.toComplex_re, hre_eq]
        change |(roundShiftInt S_re qChild : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) -
          (S_re : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ))| ≤ _
        rw [← sub_mul, abs_mul, abs_of_pos h2q_pos]
        exact mul_le_mul_of_nonneg_right (abs_roundShiftInt_sub_div_le S_re qChild) h2q_pos.le
      have him_le :
          |((refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered filterTap j1 k2).toComplex -
              S_unrounded).im| ≤
            (1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) := by
        simp only [refMatrixSpreadFixed, refRowSpreadFixed, Complex.sub_im,
          FixedComplex.toComplex_im, him_eq]
        change |(roundShiftInt S_im qChild : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) -
          (S_im : ℝ) / (2 : ℝ) ^ qChild * (2 : ℝ) ^ (-(qChild : ℤ))| ≤ _
        rw [← sub_mul, abs_mul, abs_of_pos h2q_pos]
        exact mul_le_mul_of_nonneg_right (abs_roundShiftInt_sub_div_le S_im qChild) h2q_pos.le
      calc ‖(refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered filterTap j1 k2).toComplex -
            S_unrounded‖
          ≤ Real.sqrt 2 * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) :=
            norm_complex_le_of_re_im_le (by positivity) hre_le him_le
        _ = (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) := by ring
    have hsum_diff :
        ‖S_unrounded - U_true j1 k2‖ ≤
          W * ((Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ)) * M) := by
      unfold S_unrounded U_true spreadArray
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
          ‖quantizeComplex qChild (xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))) *
              (fQuant d : ℂ) -
            xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d))) *
              (IntMul.filterTap alpha m1 t1 j1 d : ℂ)‖ ≤
            (Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
        intro d _
        let z : ℂ := xCast (strideFin j1 (intModFin r hr_pos ((k2.val : ℤ) - d)))
        let f : ℝ := IntMul.filterTap alpha m1 t1 j1 d
        have hz_norm : ‖z‖ ≤ M := (norm_le_vecInfNorm x _).trans hM_ge_norm
        have hqf_le : |fQuant d| ≤ 1 := htap_abs j1 d
        have hqf_sub : |fQuant d - f| ≤ (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) :=
          htap_err j1 d
        have hqz_sub : ‖quantizeComplex qChild z - z‖ ≤
            (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) :=
          norm_quantizeComplex_sub_self_le qChild z
        have hdecomp :
            quantizeComplex qChild z * (fQuant d : ℂ) - z * (f : ℂ) =
              (quantizeComplex qChild z - z) * (fQuant d : ℂ) +
                z * ((fQuant d - f : ℝ) : ℂ) := by push_cast; ring
        rw [hdecomp]
        have h1 : ‖(quantizeComplex qChild z - z) * (fQuant d : ℂ)‖ ≤
            (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc ‖quantizeComplex qChild z - z‖ * |fQuant d|
              ≤ ((Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ))) * 1 :=
                mul_le_mul hqz_sub hqf_le (abs_nonneg _) (by positivity)
            _ = (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * 1 := by ring
            _ ≤ (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by gcongr
        have h2 : ‖z * ((fQuant d - f : ℝ) : ℂ)‖ ≤
            (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc ‖z‖ * |fQuant d - f|
              ≤ M * ((51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) :=
                mul_le_mul hz_norm hqf_sub (abs_nonneg _) hM_pos.le
            _ = (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by ring
        have htri := norm_add_le
          ((quantizeComplex qChild z - z) * (fQuant d : ℂ))
          (z * ((fQuant d - f : ℝ) : ℂ))
        linarith
      calc ‖∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), _‖
          ≤ ∑ d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ), ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ _d ∈ Finset.Icc (-(m1 : ℤ)) (m1 : ℤ),
              ((Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ)) * M) :=
            Finset.sum_le_sum hterm
        _ = W * ((Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ)) * M) := by
            simp [Finset.sum_const, hcard_Icc, W, nsmul_eq_mul]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (refMatrixSpreadFixed t1 r m1 qChild qChild hr_pos U_gathered filterTap j1 k2).toComplex
      S_unrounded (U_true j1 k2)
    have hround_M : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
        (Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ)) * M := by
      have : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
          (Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ)) * 1 := by nlinarith
      exact this.trans (by gcongr)
    have hcoeff : (Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤
        (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
      rw [h2q_eq]; nlinarith
    have hsum_le2 :
        (W + 1) * ((Real.sqrt 2 / 2 + 51 / 100) * (2 : ℝ) ^ (-(qChild : ℤ))) * M ≤
          (W + 1) * ((122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) * M := by
      have : 0 ≤ (W + 1) * M := by positivity
      nlinarith
    nlinarith
  have hU_spread_le : matInfNorm U_spread ≤ (W + 1) * M := by
    have hW_le : W ≤ 2 * (pChild : ℝ) + 1 := by
      have h1 : (m1 : ℝ) ≤ (pChild : ℝ) := Nat.cast_le.mpr hm1_le
      dsimp [W]
      push_cast
      linarith
    have hpow_le : ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 := by
      have h1 : pChild + 1 ≤ 2 ^ pChild := Nat.lt_two_pow_self
      have h1r : (pChild : ℝ) + 1 ≤ (2 : ℝ) ^ pChild := by exact_mod_cast h1
      calc ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (2 : ℝ) ^ pChild * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right h1r h2p_pos.le
        _ = 1 := two_pow_mul_two_zpow_neg pChild
    have herr_le_M : (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M ≤ M := by
      have h1 : (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 := by
        have hW1 : W + 1 ≤ 2 * ((pChild : ℝ) + 1) := by linarith
        calc (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))
            ≤ (2 * ((pChild : ℝ) + 1)) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by nlinarith
          _ = (244 / 400 : ℝ) * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
          _ ≤ (244 / 400 : ℝ) * 1 := by nlinarith
          _ ≤ 1 := by norm_num
      nlinarith
    apply matInfNorm_le _ (by positivity)
    intro j1 k2
    have h1 := (norm_le_matInfNorm (fun i1 i2 => U_spread i1 i2 - U_true i1 i2) j1 k2).trans hsub_le
    have h2 := (norm_le_matInfNorm U_true j1 k2).trans hU_true_le
    have htri : ‖U_spread j1 k2‖ ≤ ‖U_spread j1 k2 - U_true j1 k2‖ + ‖U_true j1 k2‖ := by
      simpa using norm_add_le (U_spread j1 k2 - U_true j1 k2) (U_true j1 k2)
    linarith
  exact ⟨hU_true_le, hsub_le, hU_spread_le⟩

/-- Step 2 pre-twist, negacyclic polynomial transform (`radix2SyntheticFFTFixed`), and post-twist
error and headroom bounds for `computableFastDFTRecursive` on any valid node
(`computableFastDFTRecursive_step2_bounds`). -/
theorem computableFastDFTRecursive_step2_bounds {K p B_in m1 : ℕ}
    (hp : 8 ≤ p) (hm1_ge : m1Ell K p ≤ m1) (hm1_le : m1 ≤ pChildEll K p)
    (filterTap : Fin (t1Ell K) → ℤ → ℤ)
    (htap_fits : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      FitsSignedWord (qChildEll K p + 1) (filterTap j1 d))
    (htap_abs : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))| ≤ 1)
    (htap_err : ∀ (j1 : Fin (t1Ell K)) (d : ℤ),
      |((filterTap j1 d : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ))) -
        IntMul.filterTap (alphaEll K p) m1 (t1Ell K) j1 d| ≤
        (51 / 100 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (preTwistRoot postTwistRoot : Fin (rEll K) → FixedComplex (qChildEll K p))
    (hpre_err : ∀ k2 : Fin (rEll K),
      ‖(preTwistRoot k2).toComplex - zetaPow (rEll K) (k2.val : ℤ)‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (hpost_err : ∀ k2 : Fin (rEll K),
      ‖(postTwistRoot k2).toComplex - zetaPow (rEll K) (-(k2.val : ℤ))‖ ≤
        (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChildEll K p : ℤ)))
    (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
    (hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in) :
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let pChild := pChildEll K p
    let alpha := alphaEll K p
    let B_slot := scheduleSlotBits K p B_in m1
    let hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    let hr_pos : 0 < r := rEll_pos K
    let hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let x : Fin (2 ^ K) → ℂ := fun j => (xFixed j).toComplex
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => FixedComplex.rescale qChild (xFixed j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
        t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap
    let U_spread : Fin t1 → Fin r → ℂ := fun j1 k2 => (U_spreadFixed j1 k2).toComplex
    let U_true : Fin t1 → Fin r → ℂ :=
      spreadArray hr_pos m1 xCast (fun j1 d => (IntMul.filterTap alpha m1 t1 j1 d : ℂ))
    let U_preFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun j1 k2 => FixedComplex.mulRounded (preTwistRoot k2) (U_spreadFixed j1 k2)
    let Q_synFixed : Fin t1 → Fin r → FixedComplex qChild :=
      radix2SyntheticFFTFixed (k1Ell K) c1 U_preFixed
    let Q_postFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun v1 k2 => FixedComplex.mulRounded (postTwistRoot k2) (Q_synFixed v1 k2)
    let Q_post : Fin t1 → Fin r → ℂ := fun v1 k2 => (Q_postFixed v1 k2).toComplex
    let Q_post_true : Fin t1 → Fin r → ℂ :=
      postTwistExact (syntheticFFT c1 (preTwistExact U_true))
    let W := ((2 * m1 + 1 : ℕ) : ℝ)
    let M := max 1 (vecInfNorm x)
    matInfNorm U_spread ≤ (W + 1) * M ∧
      matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤
        (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M ∧
      (∀ v1 : Fin t1, max 1 (vecInfNorm (Q_post v1)) ≤ (W + 3) * M) ∧
      (∀ v1 : Fin t1, vecInfNorm (Q_post v1) ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in)) := by
  intro t1 r c1 qChild pChild alpha B_slot hR_pos hr_pos hR_eq x xCast
    U_gathered U_spreadFixed U_spread U_true U_preFixed Q_synFixed Q_postFixed
    Q_post Q_post_true W M
  have ht1_pos : 0 < t1 := t1Ell_pos K
  let U_pre : Fin t1 → Fin r → ℂ := fun j1 k2 => (U_preFixed j1 k2).toComplex
  let Q_syn : Fin t1 → Fin r → ℂ := fun v1 k2 => (Q_synFixed v1 k2).toComplex
  have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have hW_pos : 0 < W := by change 0 < ((2 * m1 + 1 : ℕ) : ℝ); positivity
  have hW_le : W ≤ 2 * (pChild : ℝ) + 1 := by
    have h1 : (m1 : ℝ) ≤ (pChild : ℝ) := Nat.cast_le.mpr hm1_le
    dsimp [W]
    push_cast
    linarith
  have hK_le : (K : ℝ) ≤ (pChild : ℝ) := by
    have : K ≤ pChild := by unfold pChild pChildEll pWorkEll; omega
    exact_mod_cast this
  have h2c_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
  have h2q_eq : (2 : ℝ) ^ (-(qChild : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
    have hexp : -(qChild : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by
      change -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ); omega
    rw [hexp, zpow_add₀ (by norm_num)]; norm_num; ring
  have hpow_le : ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 1 := by
    have h1 : pChild + 1 ≤ 2 ^ pChild := Nat.lt_two_pow_self
    have h1r : (pChild : ℝ) + 1 ≤ (2 : ℝ) ^ pChild := by exact_mod_cast h1
    calc ((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))
        ≤ (2 : ℝ) ^ pChild * (2 : ℝ) ^ (-(pChild : ℤ)) :=
          mul_le_mul_of_nonneg_right h1r h2c_pos.le
      _ = 1 := two_pow_mul_two_zpow_neg pChild
  have hstep1 := matInfNorm_computableFastDFTRecursive_step1_sub_le hp hm1_ge hm1_le
    filterTap htap_fits htap_abs htap_err xFixed hx
  have hU_true_le : matInfNorm U_true ≤ W * M := hstep1.1
  have hU_sub_le : matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) ≤
      (W + 1) * (122 / 400 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := hstep1.2.1
  have hU_spread_le : matInfNorm U_spread ≤ (W + 1) * M := hstep1.2.2
  clear hstep1
  let U_pre_true : Fin t1 → Fin r → ℂ := preTwistExact U_true
  let Q_syn_true : Fin t1 → Fin r → ℂ := syntheticFFT c1 U_pre_true
  have hU_pre_true_le : matInfNorm U_pre_true ≤ W * M :=
    (matInfNorm_preTwistExact_le U_true).trans hU_true_le
  have hQ_syn_true_le : matInfNorm Q_syn_true ≤ W * M :=
    (matInfNorm_syntheticFFT_le ht1_pos c1 U_pre_true).trans hU_pre_true_le
  have hQ_post_true_le : matInfNorm Q_post_true ≤ W * M :=
    (matInfNorm_postTwistExact_le Q_syn_true).trans hQ_syn_true_le
  set ε_twist : ℝ := (18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))
  have hε_twist_eq : (18 / 25 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) = ε_twist := by
    dsimp [ε_twist]; rw [h2q_eq]; ring
  have h2q_le_ε : (Real.sqrt 2 / 2) * (2 : ℝ) ^ (-(qChild : ℤ)) ≤ ε_twist := by
    rw [← hε_twist_eq]
    have hsqrt := sqrt_two_le
    have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ (-(qChild : ℤ)) := zpow_pos (by norm_num) _
    nlinarith
  have hU_pre_sub : matInfNorm (fun j1 k2 => U_pre j1 k2 - U_pre_true j1 k2) ≤
      ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ)) *
        (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    have h1 := matInfNorm_mulRounded_root_sub_le preTwistRoot
      (fun k2 => zetaPow r (k2.val : ℤ)) U_spreadFixed U_true (by positivity)
      (fun k2 => by rw [← hε_twist_eq]; exact hpre_err k2)
      (fun k2 => norm_zetaPow r (k2.val : ℤ)) h2q_le_ε
    change matInfNorm (fun j1 k2 => U_pre j1 k2 - U_pre_true j1 k2) ≤
      matInfNorm (fun j1 k2 => U_spread j1 k2 - U_true j1 k2) +
        (1 + matInfNorm U_spread) * ε_twist at h1
    have h2 : 1 + matInfNorm U_spread ≤ (W + 2) * M := by linarith only [hU_spread_le, hM_ge_one]
    have h3 : (1 + matInfNorm U_spread) * ε_twist ≤
        ((W + 2) * M) * ((18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith only [h1, h3, hU_sub_le]
  have hQ_syn_eq : ∀ v1 k2, Q_syn v1 k2 = radix2SyntheticFFTQuant qChild (k1Ell K) c1 U_pre v1 k2 :=
    fun v1 k2 => toComplex_radix2SyntheticFFTFixed (k1Ell K) c1 U_preFixed v1 k2
  have hQ_syn_sub : matInfNorm (fun v1 k2 => Q_syn v1 k2 - Q_syn_true v1 k2) ≤
      ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) + (18 / 100 : ℝ) * (K : ℝ)) *
        (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    apply matInfNorm_le _ (by positivity)
    intro v1 k2
    have hsyn_err := syntheticFFT_rounding_error_le K pChild c1 (t1Ell_mul_c1Ell K) U_pre v1
    have h1 : ‖Q_syn v1 k2 - syntheticFFT c1 U_pre v1 k2‖ ≤
        (18 / 100 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
      have h1a : ‖Q_syn v1 k2 - syntheticFFT c1 U_pre v1 k2‖ ≤
          (0.18 : ℝ) * (K : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) * 1 := by
        have h1b := (norm_le_vecInfNorm
          (fun m => radix2SyntheticFFTQuant qChild (k1Ell K) c1 U_pre v1 m - syntheticFFT c1 U_pre v1 m) k2).trans
          (hsyn_err.1.trans hsyn_err.2)
        rw [← hQ_syn_eq v1 k2] at h1b
        linarith only [h1b]
      exact h1a.trans (by gcongr; norm_num)
    have h2 : ‖syntheticFFT c1 U_pre v1 k2 - Q_syn_true v1 k2‖ ≤
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ)) *
          (2 : ℝ) ^ (-(pChild : ℤ)) * M :=
      (norm_le_matInfNorm (fun i1 i2 => syntheticFFT c1 U_pre i1 i2 - Q_syn_true i1 i2) v1 k2).trans
        ((matInfNorm_syntheticFFT_sub_le ht1_pos c1 U_pre U_pre_true).trans hU_pre_sub)
    have htri := norm_sub_le_norm_sub_add_norm_sub (Q_syn v1 k2)
      (syntheticFFT c1 U_pre v1 k2) (Q_syn_true v1 k2)
    linarith only [htri, h1, h2]
  have hQ_syn_le : matInfNorm Q_syn ≤ (W + 2) * M := by
    have hcoeff : ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
        (18 / 100 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 2 := by
      have hlin : (W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) ≤ 2 * ((pChild : ℝ) + 1) := by linarith only [hW_le, hK_le]
      calc ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
            (18 / 100 : ℝ) * (K : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (2 * ((pChild : ℝ) + 1)) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right hlin h2c_pos.le
        _ = 2 * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        _ ≤ 2 * 1 := by linarith only [hpow_le]
        _ = 2 := by ring
    have herr_le : matInfNorm (fun v1 k2 => Q_syn v1 k2 - Q_syn_true v1 k2) ≤ 2 * M :=
      hQ_syn_sub.trans (mul_le_mul_of_nonneg_right hcoeff hM_pos.le)
    apply matInfNorm_le _ (by positivity)
    intro v1 k2
    have h1 := (norm_le_matInfNorm (fun i1 i2 => Q_syn i1 i2 - Q_syn_true i1 i2) v1 k2).trans herr_le
    have h2 := (norm_le_matInfNorm Q_syn_true v1 k2).trans hQ_syn_true_le
    have htri : ‖Q_syn v1 k2‖ ≤ ‖Q_syn v1 k2 - Q_syn_true v1 k2‖ + ‖Q_syn_true v1 k2‖ := by
      simpa using norm_add_le (Q_syn v1 k2 - Q_syn_true v1 k2) (Q_syn_true v1 k2)
    linarith only [htri, h1, h2]
  have hQ_post_sub : matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤
      (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
    have h1 := matInfNorm_mulRounded_root_sub_le postTwistRoot
      (fun k2 => zetaPow r (-(k2.val : ℤ))) Q_synFixed Q_syn_true (by positivity)
      (fun k2 => by rw [← hε_twist_eq]; exact hpost_err k2)
      (fun k2 => norm_zetaPow r (-(k2.val : ℤ))) h2q_le_ε
    change matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤
      matInfNorm (fun v1 k2 => Q_syn v1 k2 - Q_syn_true v1 k2) +
        (1 + matInfNorm Q_syn) * ε_twist at h1
    have h2 : 1 + matInfNorm Q_syn ≤ (W + 3) * M := by linarith only [hQ_syn_le, hM_ge_one]
    have h3 : (1 + matInfNorm Q_syn) * ε_twist ≤
        ((W + 3) * M) * ((18 / 100 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ))) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have hsum :
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) + (W + 3) * (18 / 100 : ℝ)) ≤
        W + (18 / 100 : ℝ) * (K : ℝ) + 2 := by linarith only [hW_pos]
    have hprod_pos : 0 ≤ (2 : ℝ) ^ (-(pChild : ℤ)) * M := by positivity
    have h4 : matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤
        ((W + 1) * (122 / 400 : ℝ) + (W + 2) * (18 / 100 : ℝ) +
          (18 / 100 : ℝ) * (K : ℝ) + (W + 3) * (18 / 100 : ℝ)) *
        ((2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
      linarith only [h1, h3, hQ_syn_sub]
    calc matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2)
        ≤ (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * ((2 : ℝ) ^ (-(pChild : ℤ)) * M) :=
          h4.trans (mul_le_mul_of_nonneg_right hsum hprod_pos)
      _ = (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by ring
  have hQ_post_WM : ∀ v1 : Fin t1, vecInfNorm (Q_post v1) ≤ (W + 3) * M := by
    have hcoeff : (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤ 3 := by
      have hlin : W + (18 / 100 : ℝ) * (K : ℝ) + 2 ≤ 3 * ((pChild : ℝ) + 1) := by
        linarith only [hW_le, hK_le]
      calc (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ))
          ≤ (3 * ((pChild : ℝ) + 1)) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right hlin h2c_pos.le
        _ = 3 * (((pChild : ℝ) + 1) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        _ ≤ 3 * 1 := by linarith only [hpow_le]
        _ = 3 := by ring
    have herr_le : matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤ 3 * M :=
      hQ_post_sub.trans (mul_le_mul_of_nonneg_right hcoeff hM_pos.le)
    intro v1
    apply vecInfNorm_le _ (by positivity)
    intro k2
    have h1 := (norm_le_matInfNorm (fun i1 i2 => Q_post i1 i2 - Q_post_true i1 i2) v1 k2).trans herr_le
    have h2 := (norm_le_matInfNorm Q_post_true v1 k2).trans hQ_post_true_le
    have htri : ‖Q_post v1 k2‖ ≤ ‖Q_post v1 k2 - Q_post_true v1 k2‖ + ‖Q_post_true v1 k2‖ := by
      simpa using norm_add_le (Q_post v1 k2 - Q_post_true v1 k2) (Q_post_true v1 k2)
    linarith only [htri, h1, h2]
  have hQ_post_le : ∀ v1 : Fin t1, max 1 (vecInfNorm (Q_post v1)) ≤ (W + 3) * M := by
    have h1_le_WM : 1 ≤ (W + 3) * M := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (W + 3) * M := mul_le_mul (by linarith only [hW_pos]) hM_ge_one zero_le_one
            (by linarith only [hW_pos])
    exact fun v1 => max_le h1_le_WM (hQ_post_WM v1)
  have hQ_post_B_in : ∀ v1 : Fin t1, vecInfNorm (Q_post v1) ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in) := by
    have hM_le_pow : M ≤ (2 : ℝ) ^ B_in := max_le (one_le_pow₀ (by norm_num)) hx
    have hW3_le_pow : W + 3 ≤ (2 : ℝ) ^ (Nat.clog 2 (2 * pChild + 4)) := by
      have h1 : W + 3 ≤ ((2 * pChild + 4 : ℕ) : ℝ) := by push_cast; linarith only [hW_le]
      have h2 : 2 * pChild + 4 ≤ 2 ^ (Nat.clog 2 (2 * pChild + 4)) :=
        Nat.le_pow_clog (by omega) (2 * pChild + 4)
      have h2r : ((2 * pChild + 4 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (2 * pChild + 4)) := by
        exact_mod_cast h2
      exact h1.trans h2r
    intro v1
    calc vecInfNorm (Q_post v1) ≤ (W + 3) * M := hQ_post_WM v1
      _ ≤ (2 : ℝ) ^ (Nat.clog 2 (2 * pChild + 4)) * (2 : ℝ) ^ B_in :=
        mul_le_mul hW3_le_pow hM_le_pow hM_pos.le (by positivity)
      _ = (2 : ℝ) ^ (childScheduleBIn K p B_in) := by
        unfold childScheduleBIn pChild
        rw [pow_add (2 : ℝ) B_in (Nat.clog 2 (2 * pChildEll K p + 4)), mul_comm]
  exact ⟨hU_spread_le, hQ_post_sub, hQ_post_le, hQ_post_B_in⟩

/-- **Unconditional Multi-Level Accuracy Theorem for `computableFastDFTRecursive` on Any Valid
`ScheduleIntTree` (`vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow`)**:
For any `tree : ScheduleIntTree K p B_in` satisfying `ValidScheduleIntTree tree`, any $p \ge 8$,
and any input `xFixed : Fin (2 ^ K) → FixedComplex (p + 2)` satisfying the schedule headroom bound
`vecInfNorm (fun j => (xFixed j).toComplex) ≤ 2 ^ B_in`, the pure-integer operator
`computableFastDFTRecursive tree xFixed` approximates the exact 1D DFT `normDFT1D` within
$2^{-p} \max(1, \|x\|_\infty)$. -/
theorem vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow
    {K p B_in : ℕ} {tree : ScheduleIntTree K p B_in}
    (htree : ValidScheduleIntTree tree) :
    ∀ (_hp : 8 ≤ p) (xFixed : Fin (2 ^ K) → FixedComplex (p + 2))
      (_hx : vecInfNorm (fun j => (xFixed j).toComplex) ≤ (2 : ℝ) ^ B_in),
      vecInfNorm (fun u =>
        (computableFastDFTRecursive tree xFixed u).toComplex -
          normDFT1D (fun j => (xFixed j).toComplex) u) ≤
        (2 : ℝ) ^ (-(p : ℤ)) * max 1 (vecInfNorm (fun j => (xFixed j).toComplex)) := by
  induction htree with
  | leaf K p B_in leafTwiddles _hcond hroots =>
    intro _hp xFixed _hx
    exact vecInfNorm_baseRadix2FFTFixed_sub_normDFT1D_le_of_roots K p leafTwiddles hroots xFixed
  | node K p B_in m1 filterTap preTwistRoot postTwistRoot c0Mantissa c1Mantissa child
      hcond hm1_ge hm1_le htap_fits htap_abs htap_err hpre_err hpost_err hc0_nn hc1_nn
      hc0_err hc1_err _hchild ih =>
    intro hp xFixed hx
    have hK2 : 2 ≤ K := hcond.2
    have hleaf_bool : isBaseLeaf K p = false := by
      have h := hcond.1
      simpa using h
    have hleaf : 4 * p * p < 2 ^ K := by
      have h := hleaf_bool
      unfold isBaseLeaf at h
      rw [decide_eq_false_iff_not, not_le] at h
      exact h
    let t1 := t1Ell K
    let r := rEll K
    let c1 := c1Ell K
    let qChild := qChildEll K p
    let pChild := pChildEll K p
    let pWork := pWorkEll K p
    let alpha := alphaEll K p
    let B_slot := scheduleSlotBits K p B_in m1
    have hR_pos : 0 < 2 ^ K := Nat.two_pow_pos K
    have ht1_pos : 0 < t1 := t1Ell_pos K
    have hr_pos : 0 < r := rEll_pos K
    haveI : NeZero t1 := ⟨ne_of_gt ht1_pos⟩
    have hR_eq : 2 ^ K = t1 * r := (t1Ell_mul_rEll K).symm
    let x : Fin (2 ^ K) → ℂ := fun j => (xFixed j).toComplex
    let xCast : Fin (t1 * r) → ℂ := fun idx => x (Fin.cast hR_eq.symm idx)
    let U_gathered : Fin t1 → Fin r → FixedComplex qChild :=
      oddStrideGather t1 r hR_pos (fun j => FixedComplex.rescale qChild (xFixed j))
    let U_spreadFixed : Fin t1 → Fin r → FixedComplex qChild :=
      kroneckerMatrixSpreadFixedWithMul (signedMulFromNatMul (· * ·))
        t1 r m1 B_slot qChild qChild hr_pos U_gathered filterTap
    let U_true : Fin t1 → Fin r → ℂ :=
      spreadArray hr_pos m1 xCast (fun j1 d => (IntMul.filterTap alpha m1 t1 j1 d : ℂ))
    let U_preFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun j1 k2 => FixedComplex.mulRounded (preTwistRoot k2) (U_spreadFixed j1 k2)
    let Q_synFixed : Fin t1 → Fin r → FixedComplex qChild :=
      radix2SyntheticFFTFixed (k1Ell K) c1 U_preFixed
    let Q_postFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun v1 k2 => FixedComplex.mulRounded (postTwistRoot k2) (Q_synFixed v1 k2)
    let Q_hatFixed : Fin t1 → Fin r → FixedComplex qChild :=
      fun v1 => computableFastDFTRecursive child (Q_postFixed v1)
    let Y_matFixed : Fin t1 → Fin r → FixedComplex qChild :=
      oddColScatter ht1_pos ⟨k1Ell K, rfl⟩ Q_hatFixed
    let altFixed : FixedComplex qChild := nyquistModeSumFixed K p xFixed
    let Z_colsFixed : Fin r → Fin t1 → FixedComplex qChild :=
      fun u2 =>
        if u2.val = r / 2 then
          nyquistColumnSolveFixed (c0Mantissa u2) (fun m => Y_matFixed m u2) altFixed
        else
          cyclicBidiagPrevSolveFixed (c0Mantissa u2) (c1Mantissa u2) (fun m => Y_matFixed m u2)
    let Z_matFixed : Fin t1 → Fin r → FixedComplex qChild := fun u1 u2 => Z_colsFixed u2 u1
    let Q_post : Fin t1 → Fin r → ℂ := fun v1 k2 => (Q_postFixed v1 k2).toComplex
    let Q_hat : Fin t1 → Fin r → ℂ := fun v1 u2 => (Q_hatFixed v1 u2).toComplex
    let Y_mat : Fin t1 → Fin r → ℂ := fun u1 u2 => (Y_matFixed u1 u2).toComplex
    let Z_mat : Fin t1 → Fin r → ℂ := fun u1 u2 => (Z_matFixed u1 u2).toComplex
    let W := ((2 * m1 + 1 : ℕ) : ℝ)
    let M := max 1 (vecInfNorm x)
    have hM_ge_one : 1 ≤ M := le_max_left 1 (vecInfNorm x)
    have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
    have hW_pos : 0 < W := by change 0 < ((2 * m1 + 1 : ℕ) : ℝ); positivity
    have hW_le : W ≤ 2 * (pChild : ℝ) + 1 := by
      have h1 : (m1 : ℝ) ≤ (pChild : ℝ) := Nat.cast_le.mpr hm1_le
      dsimp [W]
      push_cast
      linarith
    have hpChild : 8 ≤ pChild := by unfold pChild pChildEll pWorkEll; omega
    have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
    have h2c_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild : ℤ)) := zpow_pos (by norm_num) _
    have h2w_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pWork : ℤ)) := zpow_pos (by norm_num) _
    have h2q_eq : (2 : ℝ) ^ (-(qChild : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
      have hexp : -(qChild : ℤ) = -(pChild : ℤ) + (-2 : ℤ) := by
        change -((pChild + 2 : ℕ) : ℤ) = -(pChild : ℤ) + (-2 : ℤ); omega
      rw [hexp, zpow_add₀ (by norm_num)]; norm_num; ring
    let U_pre_true : Fin t1 → Fin r → ℂ := preTwistExact U_true
    let Q_syn_true : Fin t1 → Fin r → ℂ := syntheticFFT c1 U_pre_true
    let Q_post_true : Fin t1 → Fin r → ℂ := postTwistExact Q_syn_true
    have hstep2 := computableFastDFTRecursive_step2_bounds hp hm1_ge hm1_le
      filterTap htap_fits htap_abs htap_err preTwistRoot postTwistRoot hpre_err hpost_err xFixed hx
    have hQ_post_sub : matInfNorm (fun v1 k2 => Q_post v1 k2 - Q_post_true v1 k2) ≤
        (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := hstep2.2.1
    have hQ_post_le : ∀ v1 : Fin t1, max 1 (vecInfNorm (Q_post v1)) ≤ (W + 3) * M := hstep2.2.2.1
    have hQ_post_B_in : ∀ v1 : Fin t1, vecInfNorm (Q_post v1) ≤ (2 : ℝ) ^ (childScheduleBIn K p B_in) :=
      hstep2.2.2.2
    clear hstep2
    set E_child : ℝ := (2 : ℝ) ^ (-(pChild : ℤ))
    have hE_pos : 0 ≤ E_child := h2c_pos.le
    have hE_le : E_child ≤ (2 : ℝ) ^ (-(pChild : ℤ)) := le_refl _
    have hY_step2 : ∀ (u1 : Fin t1) (u2 : Fin r),
        ‖Y_mat u1 u2 - normDFT2D U_true u1 u2‖ ≤
          (((W + 3) * E_child) +
            (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ))) * M := by
      intro u1 u2
      let v1 : Fin t1 := oddColKeyMinusInv t1 ht1_pos u2.val u1
      have hY_eq : Y_mat u1 u2 = Q_hat v1 u2 := rfl
      have hkey_eq : oddStrideIndex u2.val v1 = u1 := by
        rw [← oddColKeyMinus_eq_oddStrideIndex ht1_pos u2.val v1]
        exact oddColKeyMinus_oddColKeyMinusInv t1 ht1_pos ⟨k1Ell K, rfl⟩ u2.val u1
      have hduality : normDFT2D U_true u1 u2 = normDFT1D (Q_post_true v1) u2 := by
        rw [← hkey_eq]
        exact ((twisted_fourier_duality_reduction (t1Ell_mul_c1Ell K) U_true v1 u2).2).symm
      rw [hY_eq, hduality]
      have hchild_v1 : ‖Q_hat v1 u2 - normDFT1D (Q_post v1) u2‖ ≤ (W + 3) * E_child * M := by
        have hih := ih hpChild (Q_postFixed v1) (hQ_post_B_in v1)
        calc ‖Q_hat v1 u2 - normDFT1D (Q_post v1) u2‖
            ≤ vecInfNorm (fun m => Q_hat v1 m - normDFT1D (Q_post v1) m) :=
              norm_le_vecInfNorm (fun m => Q_hat v1 m - normDFT1D (Q_post v1) m) u2
          _ ≤ E_child * max 1 (vecInfNorm (Q_post v1)) := hih
          _ ≤ E_child * ((W + 3) * M) :=
              mul_le_mul_of_nonneg_left (hQ_post_le v1) hE_pos
          _ = (W + 3) * E_child * M := by ring
      have hdft_diff : ‖normDFT1D (Q_post v1) u2 - normDFT1D (Q_post_true v1) u2‖ ≤
          (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := by
        rw [← normDFT1D_sub]
        calc ‖normDFT1D (fun m => Q_post v1 m - Q_post_true v1 m) u2‖
            ≤ vecInfNorm (fun m => Q_post v1 m - Q_post_true v1 m) := norm_normDFT1D_le _ u2
          _ ≤ matInfNorm (fun i1 i2 => Q_post i1 i2 - Q_post_true i1 i2) := by
              apply vecInfNorm_le _ (matInfNorm_nonneg _)
              intro m
              exact norm_le_matInfNorm (fun i1 i2 => Q_post i1 i2 - Q_post_true i1 i2) v1 m
          _ ≤ (W + (18 / 100 : ℝ) * (K : ℝ) + 2) * (2 : ℝ) ^ (-(pChild : ℤ)) * M := hQ_post_sub
      have htri := norm_sub_le_norm_sub_add_norm_sub (Q_hat v1 u2)
        (normDFT1D (Q_post v1) u2) (normDFT1D (Q_post_true v1) u2)
      linarith only [htri, hchild_v1, hdft_diff]
    have hZ_step3 : ∀ (u1 : Fin t1) (u2 : Fin r),
        ‖Z_mat u1 u2 - normDFT1D xCast (freqFin u1 u2)‖ ≤
          (236 / 100 : ℝ) * (t1 : ℝ) *
            ((((W + 4) * E_child) +
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ)))) * M := by
      intro u1 u2
      have ht1_ge_one : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1_pos
      let Z_col : Fin t1 → ℂ := fun m => normDFT1D xCast (freqFin m u2)
      let c0 := passbandC0 K p u2
      let c1_pb := passbandC1 K p u2
      let B_true : Fin t1 → ℂ := fun m => (c0 : ℂ) * Z_col m + (c1_pb : ℂ) * Z_col (cyclicPrev m)
      let B_step2 : Fin t1 → ℂ := fun m => Y_mat m u2
      have hpoiss := normDFT2D_spreadArray_twoMode_sub_le_of_ge hp hm1_ge x u2
      have hZ_col_le : vecInfNorm Z_col ≤ M := hpoiss.1
      have hB_true_le : vecInfNorm B_true ≤ M := hpoiss.2.1
      have hB_diff_le : vecInfNorm (fun m => B_step2 m - B_true m) ≤
          (((W + 3) * E_child) +
            (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
            (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) * M := by
        apply vecInfNorm_le _ (by positivity)
        intro m
        have h1 := hY_step2 m u2
        have h2 := hpoiss.2.2 m
        have htri := norm_sub_le_norm_sub_add_norm_sub (B_step2 m) (normDFT2D U_true m u2) (B_true m)
        linarith only [htri, h1, h2]
      clear hpoiss
      have hamp_le_M :
          (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) ≤ M := by
        have hbudget := level_error_budget_le_of_W_le (by omega : 1 ≤ K) (by omega : 1 ≤ p) hleaf hW_pos.le hW_le
        have hp_le_one : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
          zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
        have hsqrt_pos : (0 : ℝ) ≤ (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) := by positivity
        have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
        have hE_child_term : (W + 3) * E_child ≤ (W + 4) * (2 : ℝ) ^ (-(pChild : ℤ)) := by
          calc (W + 3) * E_child ≤ (W + 4) * E_child := by linarith only [hE_pos]
            _ ≤ (W + 4) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
              mul_le_mul_of_nonneg_left hE_le (by positivity)
        have hinner_le :
            (((W + 3) * E_child) +
              (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤
            (((W + 4) * (2 : ℝ) ^ (-(pChild : ℤ))) +
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) := by
          have hmid : (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right (by linarith only [hK_nn]) h2c_pos.le
          linarith only [hE_child_term, hmid, h2w_pos]
        have hprod_le_one :
            (236 / 100 : ℝ) * (t1 : ℝ) *
              (((W + 3) * E_child) +
                (W + (18 / 100 : ℝ) * (K : ℝ) + (24 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
                (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤ 1 := by
          have h1 := mul_le_mul_of_nonneg_left hinner_le
            (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
          linarith only [h1, hbudget, hp_le_one, hsqrt_pos]
        have hamp1 := mul_le_mul_of_nonneg_left hB_diff_le
          (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
        have hamp2 := mul_le_mul_of_nonneg_right hprod_le_one hM_pos.le
        linarith only [hamp1, hamp2]
      have hB_diff_le_M : vecInfNorm (fun m => B_step2 m - B_true m) ≤ M := by
        have hnn : 0 ≤ vecInfNorm (fun m => B_step2 m - B_true m) := vecInfNorm_nonneg _
        have h1 : 1 * vecInfNorm (fun m => B_step2 m - B_true m) ≤
            ((236 / 100 : ℝ) * (t1 : ℝ)) * vecInfNorm (fun m => B_step2 m - B_true m) :=
          mul_le_mul_of_nonneg_right (by linarith only [ht1_ge_one]) hnn
        linarith only [h1, hamp_le_M]
      have hB_step2_le : vecInfNorm B_step2 ≤ 2 * M := by
        apply vecInfNorm_le _ (by positivity)
        intro m
        have h1 := (norm_le_vecInfNorm (fun k => B_step2 k - B_true k) m).trans hB_diff_le_M
        have h2 := (norm_le_vecInfNorm B_true m).trans hB_true_le
        have htri : ‖B_step2 m‖ ≤ ‖B_step2 m - B_true m‖ + ‖B_true m‖ := by
          simpa using norm_add_le (B_step2 m - B_true m) (B_true m)
        linarith only [htri, h1, h2]
      have hquant_bound :
          (2 : ℝ) ^ (-(qChild : ℤ)) +
            2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (3 * M) ≤
          (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
        rw [h2q_eq]
        have h1 : 1 ≤ (236 / 100 : ℝ) * (t1 : ℝ) * M := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ ((236 / 100 : ℝ) * (t1 : ℝ)) * M :=
              mul_le_mul (by linarith only [ht1_ge_one]) hM_ge_one zero_le_one
                (by linarith only [ht1_ge_one])
            _ = (236 / 100 : ℝ) * (t1 : ℝ) * M := by ring
        have h2 : (1 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
            ((236 / 100 : ℝ) * (t1 : ℝ) * M) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
          mul_le_mul_of_nonneg_right h1 h2c_pos.le
        have hlhs : (1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)) +
            2 * ((236 / 100 : ℝ) * (t1 : ℝ) * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-(pChild : ℤ)))) * (3 * M) =
            (1 / 4 : ℝ) * (1 * (2 : ℝ) ^ (-(pChild : ℤ))) +
              (3 / 2 : ℝ) * (((236 / 100 : ℝ) * (t1 : ℝ) * M) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        have hrhs : (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) =
            2 * (((236 / 100 : ℝ) * (t1 : ℝ) * M) * (2 : ℝ) ^ (-(pChild : ℤ))) := by ring
        rw [hlhs, hrhs]
        linarith only [h2, h2c_pos]
      dsimp only [Z_mat, Z_matFixed, Z_colsFixed]
      split_ifs with hu2
      · -- Nyquist column u2.val = r / 2
        have hZ_nyq :
            (nyquistColumnSolveFixed (c0Mantissa u2) (fun m => Y_matFixed m u2) altFixed u1).toComplex =
              nyquistColumnSolveQuantWithMantissa qChild (c0Mantissa u2) B_step2
                (nyquistModeSum K x) u1 := by
          dsimp [altFixed, B_step2, Y_mat]
          rw [nyquistModeSumFixed_eq_quantizeComplexFixed]
          exact toComplex_nyquistColumnSolveFixed_withMantissa (c0Mantissa u2)
            (fun m => Y_matFixed m u2) (nyquistModeSum K x) u1
        rw [hZ_nyq]
        have hc1_eq : c1_pb = c0 := passbandC1_eq_passbandC0_of_nyquist hK2 p u2 hu2
        have hmax : (49999999 / 100000000 : ℝ) ≤ max c0 c1_pb := passbandC0_passbandC1_max_ge hp u2
        rw [hc1_eq, max_self] at hmax
        have hc0_ne : c0 ≠ 0 := by linarith only [hmax]
        have halt : (∑ m : Fin t1, (-1 : ℂ) ^ m.val * Z_col m) = nyquistModeSum K x :=
          sum_alternating_normDFT1D_freqFin_eq_nyquistModeSum hK2 x u2 hu2
        have hrec : ∀ m : Fin t1, (c0 : ℂ) * Z_col m + (c0 : ℂ) * Z_col (cyclicPrev m) = B_true m := by
          intro m; dsimp [B_true]; rw [hc1_eq]
        have hZ_spec : Z_col u1 = nyquistColumnSolve c0 B_true (nyquistModeSum K x) u1 :=
          nyquistColumnSolve_spec hc0_ne B_true Z_col (nyquistModeSum K x) hrec halt u1
        have hexact_diff :
            ‖nyquistColumnSolve c0 B_step2 (nyquistModeSum K x) u1 - Z_col u1‖ ≤
              (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) := by
          rw [hZ_spec, nyquistColumnSolve_sub_same_alt]
          have hcond_nyq := passbandC0_nyquist_conditioning_le_236_t1 hK2 hp u2 hu2
            (fun m => B_step2 m - B_true m) 0
          simp only [norm_zero, zero_div, add_zero] at hcond_nyq
          exact (norm_le_vecInfNorm _ u1).trans hcond_nyq
        have hquant_diff :
            ‖nyquistColumnSolveQuantWithMantissa qChild (c0Mantissa u2) B_step2
                (nyquistModeSum K x) u1 -
              nyquistColumnSolve c0 B_step2 (nyquistModeSum K x) u1‖ ≤
              (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
          have hq := (norm_le_vecInfNorm _ u1).trans
            (vecInfNorm_nyquistColumnSolveQuantWithMantissa_sub_le_of_bounds hmax
              (qChildEll_step3_precision_le_quarter K p) (hc0_err u2) B_step2 (nyquistModeSum K x))
          have h1B : 1 + vecInfNorm B_step2 ≤ 3 * M := by linarith only [hB_step2_le, hM_ge_one]
          have hmul :
              2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (1 + vecInfNorm B_step2) ≤
              2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (3 * M) :=
            mul_le_mul_of_nonneg_left h1B (by positivity)
          linarith only [hq, hmul, hquant_bound]
        have htri := norm_sub_le_norm_sub_add_norm_sub
          (nyquistColumnSolveQuantWithMantissa qChild (c0Mantissa u2) B_step2 (nyquistModeSum K x) u1)
          (nyquistColumnSolve c0 B_step2 (nyquistModeSum K x) u1)
          (Z_col u1)
        have hamp_diff := mul_le_mul_of_nonneg_left hB_diff_le
          (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
        have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
        have hcoeff_le :
            (((W + 3) * E_child) +
              (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤
            (((W + 4) * E_child) +
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) := by
          have hmid : (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right (by linarith only [hK_nn]) h2c_pos.le
          linarith only [hE_pos, hmid, h2w_pos]
        have hcoeff_mul := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcoeff_le hM_pos.le)
          (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
        linarith only [htri, hquant_diff, hexact_diff, hamp_diff, hcoeff_mul]
      · -- Non-Nyquist column u2.val ≠ r / 2
        have hZ_prev :
            (cyclicBidiagPrevSolveFixed (c0Mantissa u2) (c1Mantissa u2)
              (fun m => Y_matFixed m u2) u1).toComplex =
            cyclicBidiagPrevSolveQuantWithMantissa qChild (c0Mantissa u2) (c1Mantissa u2)
              B_step2 u1 :=
          toComplex_cyclicBidiagPrevSolveFixed_withMantissa (c0Mantissa u2) (c1Mantissa u2)
            (fun m => Y_matFixed m u2) u1
        rw [hZ_prev]
        have hexact_vec :
            vecInfNorm (fun m => cyclicBidiagPrevSolve c0 c1_pb B_step2 m - Z_col m) ≤
              (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) := by
          rw [passbandC0_passbandC1_prevSolve_sub_eq hK2 hp u2 hu2 B_step2 Z_col B_true (fun _ => rfl)]
          exact passbandC0_passbandC1_prev_conditioning_le_236_t1 hK2 hp u2 hu2
            (fun m => B_step2 m - B_true m)
        have hexact_diff :
            ‖cyclicBidiagPrevSolve c0 c1_pb B_step2 u1 - Z_col u1‖ ≤
              (236 / 100 : ℝ) * (t1 : ℝ) * vecInfNorm (fun m => B_step2 m - B_true m) :=
          (norm_le_vecInfNorm _ u1).trans hexact_vec
        have hsolve_le : vecInfNorm (cyclicBidiagPrevSolve c0 c1_pb B_step2) ≤ 2 * M := by
          apply vecInfNorm_le _ (by positivity)
          intro m
          have h1 := (norm_le_vecInfNorm (fun k => cyclicBidiagPrevSolve c0 c1_pb B_step2 k - Z_col k) m).trans
            (hexact_vec.trans hamp_le_M)
          have h2 := (norm_le_vecInfNorm Z_col m).trans hZ_col_le
          have htri : ‖cyclicBidiagPrevSolve c0 c1_pb B_step2 m‖ ≤
              ‖cyclicBidiagPrevSolve c0 c1_pb B_step2 m - Z_col m‖ + ‖Z_col m‖ := by
            simpa using norm_add_le (cyclicBidiagPrevSolve c0 c1_pb B_step2 m - Z_col m) (Z_col m)
          linarith only [htri, h1, h2]
        have hc0_nn_r : 0 ≤ (c0Mantissa u2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) :=
          mul_nonneg (by exact_mod_cast hc0_nn u2) (zpow_pos (by norm_num) _).le
        have hc1_nn_r : 0 ≤ (c1Mantissa u2 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ)) :=
          mul_nonneg (by exact_mod_cast hc1_nn u2) (zpow_pos (by norm_num) _).le
        have hquant_diff :
            ‖cyclicBidiagPrevSolveQuantWithMantissa qChild (c0Mantissa u2) (c1Mantissa u2) B_step2 u1 -
              cyclicBidiagPrevSolve c0 c1_pb B_step2 u1‖ ≤
              (236 / 100 : ℝ) * (t1 : ℝ) * (2 * (2 : ℝ) ^ (-(pChild : ℤ)) * M) := by
          have hq := (norm_le_vecInfNorm _ u1).trans
            (vecInfNorm_cyclicBidiagPrevSolveQuantWithMantissa_sub_le_of_bounds
              (passbandC0_passbandC1_max_ge hp u2)
              (max_le (gHat_le_one _ _) (gHat_le_one _ _))
              (passbandC0_passbandC1_min_nonneg K p u2)
              (gHat_ratio_pow_t1_le_015 K p hK2 hp u2 hu2)
              (qChildEll_step3_precision_le_quarter K p)
              (hc0_err u2) (hc1_err u2) hc0_nn_r hc1_nn_r B_step2)
          have h1S : 1 + vecInfNorm (cyclicBidiagPrevSolve c0 c1_pb B_step2) ≤ 3 * M := by
            linarith only [hsolve_le, hM_ge_one]
          have hmul :
              2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) *
                (1 + vecInfNorm (cyclicBidiagPrevSolve c0 c1_pb B_step2)) ≤
              2 * ((236 / 100 : ℝ) * (t1 : ℝ) * (2 : ℝ) ^ (-(qChild : ℤ))) * (3 * M) :=
            mul_le_mul_of_nonneg_left h1S (by positivity)
          linarith only [hq, hmul, hquant_bound]
        have htri := norm_sub_le_norm_sub_add_norm_sub
          (cyclicBidiagPrevSolveQuantWithMantissa qChild (c0Mantissa u2) (c1Mantissa u2) B_step2 u1)
          (cyclicBidiagPrevSolve c0 c1_pb B_step2 u1)
          (Z_col u1)
        have hamp_diff := mul_le_mul_of_nonneg_left hB_diff_le
          (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
        have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
        have hcoeff_le :
            (((W + 3) * E_child) +
              (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (15 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) ≤
            (((W + 4) * E_child) +
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) +
              (91 / 100 : ℝ) * (2 : ℝ) ^ (-(pWork : ℤ))) := by
          have hmid : (W + (18 / 100 : ℝ) * (K : ℝ) + (44 / 10 : ℝ)) * (2 : ℝ) ^ (-(pChild : ℤ)) ≤
              (W + (54 / 100 : ℝ) * (K : ℝ) + 7) * (2 : ℝ) ^ (-(pChild : ℤ)) :=
            mul_le_mul_of_nonneg_right (by linarith only [hK_nn]) h2c_pos.le
          linarith only [hE_pos, hmid, h2w_pos]
        have hcoeff_mul := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcoeff_le hM_pos.le)
          (by positivity : (0 : ℝ) ≤ (236 / 100 : ℝ) * (t1 : ℝ))
        linarith only [htri, hquant_diff, hexact_diff, hamp_diff, hcoeff_mul]
    have hbudget := level_error_budget_le_of_W_le (by omega : 1 ≤ K) (by omega : 1 ≤ p) hleaf hW_pos.le hW_le
    apply vecInfNorm_le _ (by positivity)
    intro u
    have hunfold :
        (computableFastDFTRecursive
          (ScheduleIntTree.node K p B_in m1 filterTap preTwistRoot postTwistRoot
            c0Mantissa c1Mantissa child) xFixed u).toComplex =
        quantizeComplex (p + 2) (freqScatter t1 r hR_eq Z_mat u) := by
      unfold computableFastDFTRecursive
      dsimp only
      simp only [memoizeFin_eq, memoizeFin2_eq]
      rw [FixedComplex.toComplex_rescale, toComplex_freqScatter]
    rw [hunfold]
    let u1 : Fin t1 := ⟨u.val / r, by rw [Nat.div_lt_iff_lt_mul hr_pos]; simpa [hR_eq] using u.isLt⟩
    let u2 : Fin r := ⟨u.val % r, Nat.mod_lt u.val hr_pos⟩
    have hfreq_eq : freqScatter t1 r hR_eq Z_mat u = Z_mat u1 u2 := rfl
    have hu_cast : Fin.cast hR_eq.symm (freqFin u1 u2) = u := by
      ext; simp only [Fin.val_cast, freqFin, u1, u2]; exact Nat.mod_add_div u.val r
    have hdft_eq : normDFT1D x u = normDFT1D xCast (freqFin u1 u2) := by
      rw [normDFT1D_comp_cast hR_eq x (freqFin u1 u2), hu_cast]
    rw [hfreq_eq, hdft_eq]
    have hq_out : ‖quantizeComplex (p + 2) (Z_mat u1 u2) - Z_mat u1 u2‖ ≤
        (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      have h := norm_quantizeComplex_sub_self_le (p + 2) (Z_mat u1 u2)
      have hexp : -((p + 2 : ℕ) : ℤ) = -(p : ℤ) + (-2 : ℤ) := by push_cast; ring
      have hpow : (2 : ℝ) ^ (-((p + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
        rw [hexp, zpow_add₀ (by norm_num)]; norm_num; ring
      rw [hpow] at h
      have hprod_pos : 0 ≤ Real.sqrt 2 * (2 : ℝ) ^ (-(p : ℤ)) := by positivity
      have h1 : ‖quantizeComplex (p + 2) (Z_mat u1 u2) - Z_mat u1 u2‖ ≤
          (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) * 1 := by
        calc ‖quantizeComplex (p + 2) (Z_mat u1 u2) - Z_mat u1 u2‖
          ≤ (Real.sqrt 2 / 2) * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) := h
          _ = (1 / 8 : ℝ) * (Real.sqrt 2 * (2 : ℝ) ^ (-(p : ℤ))) := by ring
          _ ≤ (1 / 4 : ℝ) * (Real.sqrt 2 * (2 : ℝ) ^ (-(p : ℤ))) :=
            mul_le_mul_of_nonneg_right (by norm_num) hprod_pos
          _ = (Real.sqrt 2 / 4) * (2 : ℝ) ^ (-(p : ℤ)) * 1 := by ring
      exact h1.trans (by gcongr)
    have hZ_diff := hZ_step3 u1 u2
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (quantizeComplex (p + 2) (Z_mat u1 u2)) (Z_mat u1 u2) (normDFT1D xCast (freqFin u1 u2))
    have hbudget_M := mul_le_mul_of_nonneg_right hbudget hM_pos.le
    linarith only [htri, hq_out, hZ_diff, hbudget_M]

/-! ### 2. Pointwise Complex Squaring Convolution & Parameter-Free Computable Pipeline -/

/-- **Computable Pure-Integer 2-Call Complex-Packed Convolution Directly From Chunk Arrays
(`computableConvFromChunksWithMul`)**:
Computes the 2-call complex-packed convolution directly from pre-sliced base-$2^b$ chunk vectors
`(aChunks, bChunks : Fin (rootR0 n) → ℕ)` using only `FixedComplex`, `ℤ`, `roundShiftInt`, and
`computableFastDFTRecursiveWithMul natMul` on a `ScheduleIntTree`. -/
def computableConvFromChunksWithMul (natMul : ℕ → ℕ → ℕ) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (aChunks bChunks : Fin (rootR0 n) → ℕ) : Fin (rootR0 n) → ℤ :=
  let p0 := rootP0 n
  let R0 := rootR0 n
  let smul := signedMulFromNatMul natMul
  let zFixed : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (packChunksFixed n (aChunks, bChunks))
  let Z : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (computableFastDFTRecursiveWithMul natMul tree zFixed)
  let W_conj : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (fun u =>
      let z := Z u
      (⟨roundShiftInt (smul (2 * z.re) z.im) (p0 + 3),
        roundShiftInt (smul z.im z.im - smul z.re z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj)
  let C_inv : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (fun m => (computableFastDFTRecursiveWithMul natMul tree W_conj m).conj)
  memoizeFin (fun k => roundShiftInt (C_inv k).re 8)

/-- **Computable Pure-Integer 2-Call Complex-Packed Convolution Parameterized by Sub-Multiplication
(`computableFastTwoCallDFTConvWithMul`)**:
Computes the 2-call complex-packed convolution of $A$ and $B$ using single-pass $O(n)$ chunk
extraction (`natChunkFn`), `FixedComplex`, `ℤ`, `roundShiftInt`, and
`computableFastDFTRecursiveWithMul natMul` on a `ScheduleIntTree`, with **zero** `ℝ` or `ℂ`, and
using **pointwise complex squaring** $\overline{\mathrm{Round}_{p_0+2}(Z[u]^2 / (2i))}$
(Lemma 3.4 (`lem:two-call`) in Section 3.5 (`sec:prelim-dft`), and Listing 1 (`lst:multiply`) in
Section 7.1 (`sec:alg-spec`)) with zero cross-tape index reversal $u \mapsto (-u) \bmod R_0$.
All multi-bit word multiplications (both inside `computableFastDFTRecursiveWithMul` and in the
pointwise frequency squaring `z.re * z.im`, `z.im * z.im`, `z.re * z.re`) are routed through
`signedMulFromNatMul natMul`. -/
def computableFastTwoCallDFTConvWithMul (natMul : ℕ → ℕ → ℕ) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (A B : ℕ) : Fin (rootR0 n) → ℤ :=
  computableConvFromChunksWithMul natMul n tree
    (natChunkFn (chunkBits n) (rootR0 n) A)
    (natChunkFn (chunkBits n) (rootR0 n) B)

/-- **Computable Pure-Integer End-to-End Product Reconstruction Parameterized by Sub-Multiplication
(`computableReconstructProductWithMul`)**:
Reconstructs $A \cdot B$ from `computableFastTwoCallDFTConvWithMul natMul` via single-pass Horner
base-$2^b$ evaluation (`evalBaseChunks`), binding the memoized convolution array once outside
`List.ofFn`, and using **only** computable integer arithmetic (`ℕ`, `ℤ`, `FixedComplex`) with
**zero** `ℝ` or `ℂ`. -/
def computableReconstructProductWithMul (natMul : ℕ → ℕ → ℕ) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (A B : ℕ) : ℕ :=
  let conv := computableFastTwoCallDFTConvWithMul natMul n tree A B
  evalBaseChunks (chunkBits n) (List.ofFn (fun k : Fin (rootR0 n) => (conv k).toNat))

/-- **Computable Pure-Integer 2-Call Complex-Packed Convolution (`computableFastTwoCallDFTConv`)**:
Computes the 2-call complex-packed convolution of $A$ and $B$ using single-pass $O(n)$ chunk
extraction (`natChunkFn`), `FixedComplex`, `ℤ`, `roundShiftInt`, and `computableFastDFTRecursive`
on a `ScheduleIntTree`, with **zero** `ℝ` or `ℂ`, and using **pointwise complex squaring**
$\overline{\mathrm{Round}_{p_0+2}(Z[u]^2 / (2i))}$ (Lemma 3.4 (`lem:two-call`) in
Section 3.5 (`sec:prelim-dft`), and Listing 1 (`lst:multiply`) in Section 7.1 (`sec:alg-spec`))
with zero cross-tape index reversal $u \mapsto (-u) \bmod R_0$. -/
def computableFastTwoCallDFTConv (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (A B : ℕ) : Fin (rootR0 n) → ℤ :=
  let p0 := rootP0 n
  let R0 := rootR0 n
  let zFixed : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (packChunksFixed n (natChunkFn (chunkBits n) R0 A,
                                   natChunkFn (chunkBits n) R0 B))
  let Z : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (computableFastDFTRecursive tree zFixed)
  let W_conj : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (fun u =>
      let z := Z u
      (⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
        roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj)
  let C_inv : Fin R0 → FixedComplex (p0 + 2) :=
    memoizeFin (fun m => (computableFastDFTRecursive tree W_conj m).conj)
  memoizeFin (fun k => roundShiftInt (C_inv k).re 8)

/-- **Computable Pure-Integer End-to-End Product Reconstruction (`computableReconstructProduct`)**:
Reconstructs $A \cdot B$ from `computableFastTwoCallDFTConv` via single-pass Horner base-$2^b$
evaluation (`evalBaseChunks`), binding the memoized convolution array once outside `List.ofFn`, and
using **only** computable integer arithmetic (`ℕ`, `ℤ`, `FixedComplex`) with **zero** `ℝ` or `ℂ`. -/
def computableReconstructProduct (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (A B : ℕ) : ℕ :=
  let conv := computableFastTwoCallDFTConv n tree A B
  evalBaseChunks (chunkBits n) (List.ofFn (fun k : Fin (rootR0 n) => (conv k).toNat))

/-- Bridge theorem equating the single-pass bit-slice + carry-save bit-stream pipeline to
`encodeNatBits (2 * n) (computableReconstructProductWithMul ...)`. -/
theorem carrySaveEmitBits_conv_eq_encodeNatBits_reconstruct
    (natMul : ℕ → ℕ → ℕ) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (inBits : List Bool) :
    let b := chunkBits n
    let R0 := rootR0 n
    let aChunks := sliceBitChunkFn b R0 (inBits.take n)
    let bChunks := sliceBitChunkFn b R0 (inBits.drop n)
    let conv := computableConvFromChunksWithMul natMul n tree aChunks bChunks
    carrySaveEmitBits b (2 * n) (List.ofFn (fun k : Fin R0 => (conv k).toNat)) 0 =
      encodeNatBits (2 * n)
        (computableReconstructProductWithMul natMul n tree
          (decodeNatBits (inBits.take n)) (decodeNatBits (inBits.drop n))) := by
  dsimp only
  rw [carrySaveEmitBits_eq_encodeNatBits, zero_add]
  unfold computableReconstructProductWithMul computableFastTwoCallDFTConvWithMul
  dsimp only
  rw [sliceBitChunkFn_eq_natChunkFn, sliceBitChunkFn_eq_natChunkFn]

/-- For any multiplication operator `natMul` satisfying `∀ a b, natMul a b = a * b`,
`computableFastTwoCallDFTConvWithMul natMul` is identical to `computableFastTwoCallDFTConv`. -/
theorem computableFastTwoCallDFTConvWithMul_eq_of_mul_eq (natMul : ℕ → ℕ → ℕ)
    (hmul : ∀ a b : ℕ, natMul a b = a * b) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (A B : ℕ) (k : Fin (rootR0 n)) :
    computableFastTwoCallDFTConvWithMul natMul n tree A B k =
      computableFastTwoCallDFTConv n tree A B k := by
  have hsmul : ∀ a b : ℤ, signedMulFromNatMul natMul a b = a * b :=
    signedMulFromNatMul_eq_mul natMul hmul
  unfold computableFastTwoCallDFTConvWithMul computableConvFromChunksWithMul computableFastTwoCallDFTConv
  dsimp only
  simp only [memoizeFin_eq]
  simp_rw [computableFastDFTRecursiveWithMul_eq_of_mul_eq natMul hmul, hsmul]

/-- For any multiplication operator `natMul` satisfying `∀ a b, natMul a b = a * b`,
`computableReconstructProductWithMul natMul` is identical to `computableReconstructProduct`. -/
theorem computableReconstructProductWithMul_eq_of_mul_eq (natMul : ℕ → ℕ → ℕ)
    (hmul : ∀ a b : ℕ, natMul a b = a * b) (n : ℕ)
    (tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    (A B : ℕ) :
    computableReconstructProductWithMul natMul n tree A B =
      computableReconstructProduct n tree A B := by
  unfold computableReconstructProductWithMul computableReconstructProduct
  simp_rw [computableFastTwoCallDFTConvWithMul_eq_of_mul_eq natMul hmul]

theorem toComplex_freqSquareConjFixed {p0 : ℕ} (z : FixedComplex (p0 + 2)) :
    ((⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
       roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj).toComplex =
      starRingEnd ℂ (quantizeComplex (p0 + 2) ((z.toComplex * z.toComplex) / (2 * Complex.I))) := by
  rw [FixedComplex.toComplex_conj]
  congr 1
  have hshift :
      (⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
        roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)) =
      FixedComplex.rescale (p0 + 2)
        (⟨2 * z.re * z.im, z.im * z.im - z.re * z.re⟩ : FixedComplex (2 * p0 + 5)) := by
    have hsub1 : (p0 + 2) - (2 * p0 + 5) = 0 := by omega
    have hsub2 : (2 * p0 + 5) - (p0 + 2) = p0 + 3 := by omega
    ext <;> simp [FixedComplex.rescale, hsub1, hsub2]
  rw [hshift, FixedComplex.toComplex_rescale]
  congr 1
  have h2p : (2 : ℝ) ^ (-((2 * p0 + 5 : ℕ) : ℤ)) =
      (1 / 2 : ℝ) * ((2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ))) := by
    have hexp : -((2 * p0 + 5 : ℕ) : ℤ) = (-1 : ℤ) + (-((p0 + 2 : ℕ) : ℤ) + -((p0 + 2 : ℕ) : ℤ)) := by
      omega
    rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    norm_num
  have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  apply mul_right_cancel₀ hI
  rw [div_mul_cancel₀ _ hI]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.I_re, Complex.I_im, FixedComplex.toComplex_re, FixedComplex.toComplex_im,
      h2p, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.I_re, Complex.I_im, FixedComplex.toComplex_re, FixedComplex.toComplex_im,
      h2p, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    ring

/-- Exact equivalence between `computableFastTwoCallDFTConv` on the canonical integer schedule tree
and `⌊(fastTwoCallDFTConvSched n A B k).re + 1/2⌋` for all `A, B < 2 ^ n`. -/
theorem computableFastTwoCallDFTConv_canonical_eq (n A B : ℕ)
    (k : Fin (rootR0 n)) :
    computableFastTwoCallDFTConv n
      (canonicalScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
      A B k =
    ⌊(fastTwoCallDFTConvSched n A B k).re + (1 / 2 : ℝ)⌋ := by
  let K0 := rootK0 n
  let p0 := rootP0 n
  let R0 := rootR0 n
  let b := chunkBits n
  let B0 := levelScheduleBIn K0 p0 0
  have hb_le : chunkBits n ≤ rootP0 n + 2 := by unfold rootP0; omega
  have hpow_b : (2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-(chunkBits n : ℤ)) := by
    have hadd : (rootP0 n + 2 - chunkBits n) + chunkBits n = rootP0 n + 2 := Nat.sub_add_cancel hb_le
    have h1 : (2 : ℝ) ^ (chunkBits n) * (2 : ℝ) ^ (-(chunkBits n : ℤ)) = 1 :=
      two_pow_mul_two_zpow_neg (chunkBits n)
    have h2 : (2 : ℝ) ^ (rootP0 n + 2) * (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)) = 1 :=
      two_pow_mul_two_zpow_neg (rootP0 n + 2)
    have h3 : (2 : ℝ) ^ (rootP0 n + 2) = (2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (chunkBits n) := by
      rw [← pow_add, hadd]
    apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ (chunkBits n) ≠ 0)
    calc
      (2 : ℝ) ^ (chunkBits n) * ((2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)))
        = ((2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (chunkBits n)) *
            (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)) := by ring
      _ = 1 := by rw [← h3, h2]
      _ = (2 : ℝ) ^ (chunkBits n) * (2 : ℝ) ^ (-(chunkBits n : ℤ)) := h1.symm
  let zFixed : Fin R0 → FixedComplex (p0 + 2) :=
    packChunksFixed n (fun i => natChunk b A i.val, fun i => natChunk b B i.val)
  let aVec : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let bVec : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let zVec : Fin R0 → ℂ := packRealComplex aVec bVec
  have hz_toC : (fun j => (zFixed j).toComplex) = zVec := by
    funext j
    unfold zFixed packChunksFixed zVec packRealComplex aVec bVec b p0
    dsimp only
    have hmodA : natChunk (chunkBits n) A j.val % 2 ^ (chunkBits n) = natChunk (chunkBits n) A j.val :=
      Nat.mod_eq_of_lt (natChunk_lt (chunkBits n) A j.val)
    have hmodB : natChunk (chunkBits n) B j.val % 2 ^ (chunkBits n) = natChunk (chunkBits n) B j.val :=
      Nat.mod_eq_of_lt (natChunk_lt (chunkBits n) B j.val)
    apply Complex.ext
    · rw [FixedComplex.toComplex_re, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
        hmodA, mul_assoc, hpow_b]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    · rw [FixedComplex.toComplex_im, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
        hmodB, mul_assoc, hpow_b]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  let tree := canonicalScheduleIntTree K0 p0 B0
  let ZFixed : Fin R0 → FixedComplex (p0 + 2) := computableFastDFTRecursive tree zFixed
  have hZFixed : ZFixed = fastDFTRecursiveSched K0 p0 B0 zVec := by
    change computableFastDFTRecursive tree zFixed = _
    rw [computableFastDFTRecursive_canonical_eq_fastDFTRecursiveSched]
    exact congrArg (fastDFTRecursiveSched K0 p0 B0) hz_toC
  let Z : Fin R0 → ℂ := fun u => (fastDFTRecursiveSched K0 p0 B0 zVec u).toComplex
  let W_conj : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
  let W_conjFixed : Fin R0 → FixedComplex (p0 + 2) :=
    fun u =>
      let z := ZFixed u
      (⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
        roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj
  have hW_toC : (fun u => (W_conjFixed u).toComplex) = W_conj := by
    funext u
    dsimp only [W_conjFixed, W_conj, Z]
    rw [toComplex_freqSquareConjFixed (ZFixed u), hZFixed]
  have hC_inv :
      computableFastDFTRecursive tree W_conjFixed k =
        fastDFTRecursiveSched K0 p0 B0 W_conj k := by
    rw [computableFastDFTRecursive_canonical_eq_fastDFTRecursiveSched]
    exact congrFun (congrArg (fastDFTRecursiveSched K0 p0 B0) hW_toC) k
  unfold computableFastTwoCallDFTConv fastTwoCallDFTConvSched
  dsimp only
  simp only [memoizeFin_eq, natChunkFn_eq_natChunk_fun]
  change roundShiftInt ((computableFastDFTRecursive tree W_conjFixed k).conj).re 8 =
    ⌊(((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) *
      (starRingEnd ℂ (fastDFTRecursiveSched K0 p0 B0 W_conj k).toComplex)))).re + (1 / 2 : ℝ)⌋
  rw [hC_inv, roundShiftInt_eq_quantizeRealMantissa]
  set cFixed : FixedComplex (p0 + 2) := fastDFTRecursiveSched K0 p0 B0 W_conj k
  congr 2
  have hp0_eq : p0 + 2 = (2 * b + 2 * K0) + 8 := by
    unfold p0 rootP0 b K0
    omega
  have hzpow : (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-((2 * b + 2 * K0 : ℕ) : ℤ)) * ((2 : ℝ) ^ 8)⁻¹ := by
    rw [hp0_eq]
    push_cast
    rw [neg_add_rev, add_comm, zpow_add₀ (by norm_num), zpow_neg]
    norm_num
  have hR0_pow : ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * (R0 : ℝ)) =
      (2 : ℝ) ^ (2 * b + 2 * K0) := by
    change ((2 ^ (2 * b) : ℕ) : ℝ) * (((2 ^ K0 : ℕ) : ℝ) * ((2 ^ K0 : ℕ) : ℝ)) = _
    rw [Nat.two_mul K0, pow_add (2 : ℝ) (2 * b), pow_add (2 : ℝ) K0 K0]
    push_cast
    rfl
  have hre_rhs :
      (((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) * (starRingEnd ℂ cFixed.toComplex)))).re =
        ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * ((R0 : ℝ) * ((cFixed.re : ℝ) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ))))) := by
    rw [← FixedComplex.toComplex_conj]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
      FixedComplex.toComplex_re, FixedComplex.conj]
  rw [hre_rhs]
  change (cFixed.re : ℝ) / (2 : ℝ) ^ 8 = _
  calc
    (cFixed.re : ℝ) / (2 : ℝ) ^ 8
      = ((2 : ℝ) ^ (2 * b + 2 * K0) * (2 : ℝ) ^ (-((2 * b + 2 * K0 : ℕ) : ℤ))) *
          ((cFixed.re : ℝ) * ((2 : ℝ) ^ 8)⁻¹) := by
        rw [two_pow_mul_two_zpow_neg, one_mul, div_eq_mul_inv]
    _ = (((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * (R0 : ℝ))) *
          ((cFixed.re : ℝ) * ((2 : ℝ) ^ (-((2 * b + 2 * K0 : ℕ) : ℤ)) * ((2 : ℝ) ^ 8)⁻¹)) := by
        rw [hR0_pow]; ring
    _ = ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * ((R0 : ℝ) * ((cFixed.re : ℝ) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ))))) := by
        rw [← hzpow]; ring

/-- **Unconditional Bit-Exactness of the Computable Pure-Integer Product Reconstruction
(`computableReconstructProduct_canonical_eq_mul`)**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, the computable pure-integer
algorithm `computableReconstructProduct` (which uses **zero** `ℝ` or `ℂ` in its definition)
evaluated on `canonicalScheduleIntTree` recovers `A * B` bit-exactly. -/
@[simp]
theorem computableReconstructProduct_canonical_eq_mul (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableReconstructProduct n
      (canonicalScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
      A B = A * B := by
  unfold computableReconstructProduct
  dsimp only
  rw [evalBaseChunks_ofFn_eq_sum]
  simp_rw [computableFastTwoCallDFTConv_canonical_eq]
  exact reconstructProductViaScheduleFastDFT_eq_mul n A B hA hB

/-- **Unconditional Nearest-Integer Rounding Recovery of `computableFastTwoCallDFTConv` on Any Valid
`ScheduleIntTree` (`computableFastTwoCallDFTConv_toNat_eq_linearConvCoeff_of_validScheduleIntTree`)**:
For all $n \in \mathbb{N}$, any `tree` satisfying `ValidScheduleIntTree tree`, all $n$-bit integers
$A, B < 2^n$, and every slot $k \in \text{Fin (rootR0 } n)$,
`(computableFastTwoCallDFTConv n tree A B k).toNat = linearConvCoeff (chunkBits n) (numChunks n) A B k.val`. -/
theorem computableFastTwoCallDFTConv_toNat_eq_linearConvCoeff_of_validScheduleIntTree (n : ℕ)
    {tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)}
    (htree : ValidScheduleIntTree tree) (A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) (k : Fin (rootR0 n)) :
    (computableFastTwoCallDFTConv n tree A B k).toNat =
      linearConvCoeff (chunkBits n) (numChunks n) A B k.val := by
  let K0 := rootK0 n
  let p0 := rootP0 n
  let R0 := rootR0 n
  let b := chunkBits n
  let B0 := levelScheduleBIn K0 p0 0
  have hb_le : chunkBits n ≤ rootP0 n + 2 := by unfold rootP0; omega
  have hpow_b : (2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-(chunkBits n : ℤ)) := by
    have hadd : (rootP0 n + 2 - chunkBits n) + chunkBits n = rootP0 n + 2 := Nat.sub_add_cancel hb_le
    have h1 : (2 : ℝ) ^ (chunkBits n) * (2 : ℝ) ^ (-(chunkBits n : ℤ)) = 1 :=
      two_pow_mul_two_zpow_neg (chunkBits n)
    have h2 : (2 : ℝ) ^ (rootP0 n + 2) * (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)) = 1 :=
      two_pow_mul_two_zpow_neg (rootP0 n + 2)
    have h3 : (2 : ℝ) ^ (rootP0 n + 2) = (2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (chunkBits n) := by
      rw [← pow_add, hadd]
    apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ (chunkBits n) ≠ 0)
    calc
      (2 : ℝ) ^ (chunkBits n) * ((2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)))
        = ((2 : ℝ) ^ (rootP0 n + 2 - chunkBits n) * (2 : ℝ) ^ (chunkBits n)) *
            (2 : ℝ) ^ (-((rootP0 n + 2 : ℕ) : ℤ)) := by ring
      _ = 1 := by rw [← h3, h2]
      _ = (2 : ℝ) ^ (chunkBits n) * (2 : ℝ) ^ (-(chunkBits n : ℤ)) := h1.symm
  let zFixed : Fin R0 → FixedComplex (p0 + 2) :=
    packChunksFixed n (fun i => natChunk b A i.val, fun i => natChunk b B i.val)
  let aVec : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let bVec : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
  let zVec : Fin R0 → ℂ := packRealComplex aVec bVec
  have hz_toC : (fun j => (zFixed j).toComplex) = zVec := by
    funext j
    unfold zFixed packChunksFixed zVec packRealComplex aVec bVec b p0
    dsimp only
    have hmodA : natChunk (chunkBits n) A j.val % 2 ^ (chunkBits n) = natChunk (chunkBits n) A j.val :=
      Nat.mod_eq_of_lt (natChunk_lt (chunkBits n) A j.val)
    have hmodB : natChunk (chunkBits n) B j.val % 2 ^ (chunkBits n) = natChunk (chunkBits n) B j.val :=
      Nat.mod_eq_of_lt (natChunk_lt (chunkBits n) B j.val)
    apply Complex.ext
    · rw [FixedComplex.toComplex_re, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
        hmodA, mul_assoc, hpow_b]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    · rw [FixedComplex.toComplex_im, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
        hmodB, mul_assoc, hpow_b]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  let ZFixed : Fin R0 → FixedComplex (p0 + 2) := computableFastDFTRecursive tree zFixed
  let Z : Fin R0 → ℂ := fun u => (ZFixed u).toComplex
  let Z_true : Fin R0 → ℂ := normDFT1D zVec
  let W_conjFixed : Fin R0 → FixedComplex (p0 + 2) :=
    fun u =>
      let z := ZFixed u
      (⟨roundShiftInt (2 * z.re * z.im) (p0 + 3),
        roundShiftInt (z.im * z.im - z.re * z.re) (p0 + 3)⟩ : FixedComplex (p0 + 2)).conj
  let W_conj : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
  let W_true : Fin R0 → ℂ :=
    fun u => starRingEnd ℂ ((Z_true u * Z_true u) / (2 * Complex.I))
  let cFixed : FixedComplex (p0 + 2) := computableFastDFTRecursive tree W_conjFixed k
  let C_inv_k : ℂ := starRingEnd ℂ cFixed.toComplex
  let cVec : Fin R0 → ℂ := fun m =>
    (linearConvCoeff b (numChunks n) A B m.val : ℂ) -
      (Complex.I / 2) *
        ((linearConvCoeff b (numChunks n) A A m.val : ℂ) -
         (linearConvCoeff b (numChunks n) B B m.val : ℂ))
  have hW_toC : (fun u => (W_conjFixed u).toComplex) = W_conj :=
    funext (fun u => toComplex_freqSquareConjFixed (ZFixed u))
  have hp0_ge18 : 18 ≤ p0 := rootP0_ge_eighteen n
  have hp0_ge8 : 8 ≤ p0 := by omega
  have h2p0_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p0 : ℤ)) := zpow_pos (by norm_num) _
  have h2p0_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (1 / 16 : ℝ) := by
    calc (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (2 : ℝ) ^ (-4 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have ha_le : ∀ j : Fin R0, ‖(aVec j : ℂ)‖ ≤ 1 := by
    intro j
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlt : (natChunk b A j.val : ℝ) ≤ (2 : ℝ) ^ b := by
      exact_mod_cast le_of_lt (natChunk_lt b A j.val)
    calc (natChunk b A j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ)) :=
          mul_le_mul_of_nonneg_right hlt (le_of_lt (zpow_pos (by norm_num) _))
      _ = 1 := two_pow_mul_two_zpow_neg b
  have hb_le : ∀ j : Fin R0, ‖(bVec j : ℂ)‖ ≤ 1 := by
    intro j
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hlt : (natChunk b B j.val : ℝ) ≤ (2 : ℝ) ^ b := by
      exact_mod_cast le_of_lt (natChunk_lt b B j.val)
    calc (natChunk b B j.val : ℝ) * (2 : ℝ) ^ (-(b : ℤ))
        ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ)) :=
          mul_le_mul_of_nonneg_right hlt (le_of_lt (zpow_pos (by norm_num) _))
      _ = 1 := two_pow_mul_two_zpow_neg b
  have hz_sqrt2 : vecInfNorm zVec ≤ Real.sqrt 2 := by
    apply vecInfNorm_le zVec (by positivity)
    intro j
    have hre : |(zVec j).re| ≤ 1 := by simpa [zVec, packRealComplex, Complex.norm_real] using ha_le j
    have him : |(zVec j).im| ≤ 1 := by simpa [zVec, packRealComplex, Complex.norm_real] using hb_le j
    simpa using norm_complex_le_of_re_im_le zero_le_one hre him
  have hz_B0 : vecInfNorm (fun j => (zFixed j).toComplex) ≤ (2 : ℝ) ^ B0 := by
    have hpow_B0 : (2 : ℝ) ^ B0 = 4 := by change (2 : ℝ) ^ 2 = 4; norm_num
    rw [hz_toC, hpow_B0]
    exact hz_sqrt2.trans (sqrt_two_le.trans (by norm_num))
  have hz_max : max 1 (vecInfNorm zVec) ≤ 2 := by
    apply max_le (by norm_num)
    exact hz_sqrt2.trans (sqrt_two_le.trans (by norm_num))
  have hZ_err : ∀ u : Fin R0, ‖Z u - Z_true u‖ ≤ 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    have h2 := vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow htree hp0_ge8 zFixed hz_B0
    change vecInfNorm (fun u => Z u - normDFT1D (fun j => (zFixed j).toComplex) u) ≤
      (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm (fun j => (zFixed j).toComplex)) at h2
    rw [hz_toC] at h2
    intro u
    have h1 := norm_le_vecInfNorm (fun v => Z v - Z_true v) u
    calc ‖Z u - Z_true u‖ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm zVec) := h1.trans h2
      _ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * 2 := mul_le_mul_of_nonneg_left hz_max (le_of_lt h2p0_pos)
      _ = 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by ring
  have hZ_true_le : ∀ u : Fin R0, ‖Z_true u‖ ≤ Real.sqrt 2 :=
    fun u => (norm_normDFT1D_le zVec u).trans hz_sqrt2
  have hWt_le : ∀ u : Fin R0, ‖W_true u‖ ≤ 1 := by
    intro u
    unfold W_true
    rw [RCLike.norm_conj, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    have hsq : ‖Z_true u‖ * ‖Z_true u‖ ≤ 2 := by
      calc ‖Z_true u‖ * ‖Z_true u‖ ≤ Real.sqrt 2 * Real.sqrt 2 :=
          mul_self_le_mul_self (norm_nonneg _) (hZ_true_le u)
        _ = 2 := Real.mul_self_sqrt (by norm_num)
    linarith
  have hW_err : ∀ u : Fin R0, ‖W_conj u - W_true u‖ ≤ (11 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    intro u
    unfold W_conj W_true
    rw [← map_sub, RCLike.norm_conj]
    have hZt_144 : ‖Z_true u‖ ≤ 72 / 50 := (hZ_true_le u).trans sqrt_two_le
    have hZ_sum : ‖Z u + Z_true u‖ ≤ 5 := by
      have h1 := norm_add_le (Z u - Z_true u) (Z_true u + Z_true u)
      have h2 := norm_add_le (Z_true u) (Z_true u)
      have heq : (Z u - Z_true u) + (Z_true u + Z_true u) = Z u + Z_true u := by ring
      rw [heq] at h1
      linarith [hZ_err u, hZt_144, h2p0_le]
    have hprod_sub : (Z u * Z u) / (2 * Complex.I) - (Z_true u * Z_true u) / (2 * Complex.I) =
        ((Z u + Z_true u) * (Z u - Z_true u)) / (2 * Complex.I) := by ring
    have hprod_err :
        ‖(Z u * Z u) / (2 * Complex.I) - (Z_true u * Z_true u) / (2 * Complex.I)‖ ≤
          5 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      rw [hprod_sub, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      have hm : ‖Z u + Z_true u‖ * ‖Z u - Z_true u‖ ≤ 5 * (2 * (2 : ℝ) ^ (-(p0 : ℤ))) :=
        mul_le_mul hZ_sum (hZ_err u) (norm_nonneg _) (by norm_num)
      linarith
    have hq_err :
        ‖quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)) -
          (Z u * Z u) / (2 * Complex.I)‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      have hq := norm_quantizeComplex_sub_self_le (p0 + 2) ((Z u * Z u) / (2 * Complex.I))
      have hexp : -((p0 + 2 : ℕ) : ℤ) = -(p0 : ℤ) + (-2 : ℤ) := by omega
      have hpow : (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
        rw [hexp, zpow_add₀ (by norm_num)]; norm_num; ring
      rw [hpow] at hq
      have hsqrt := sqrt_two_le
      nlinarith only [hq, hsqrt, h2p0_pos]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (quantizeComplex (p0 + 2) ((Z u * Z u) / (2 * Complex.I)))
      ((Z u * Z u) / (2 * Complex.I))
      ((Z_true u * Z_true u) / (2 * Complex.I))
    linarith
  have hW_norm_le : vecInfNorm W_conj ≤ 2 := by
    apply vecInfNorm_le W_conj (by norm_num)
    intro u
    have htri := norm_add_le (W_conj u - W_true u) (W_true u)
    rw [sub_add_cancel] at htri
    linarith [hW_err u, hWt_le u, h2p0_le]
  have hW_B0 : vecInfNorm (fun u => (W_conjFixed u).toComplex) ≤ (2 : ℝ) ^ B0 := by
    have hpow_B0 : (2 : ℝ) ^ B0 = 4 := by change (2 : ℝ) ^ 2 = 4; norm_num
    rw [hW_toC, hpow_B0]
    exact hW_norm_le.trans (by norm_num)
  have hW_max : max 1 (vecInfNorm W_conj) ≤ 2 := max_le (by norm_num) hW_norm_le
  have hC_inv_err : ‖C_inv_k - starRingEnd ℂ (normDFT1D W_true k)‖ ≤
      8 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    unfold C_inv_k
    rw [← map_sub, RCLike.norm_conj]
    let CFixed_vec : Fin R0 → FixedComplex (p0 + 2) := computableFastDFTRecursive tree W_conjFixed
    have h1 : ‖cFixed.toComplex - normDFT1D W_conj k‖ ≤ 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      have hb := vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow htree hp0_ge8 W_conjFixed hW_B0
      change vecInfNorm (fun m => (CFixed_vec m).toComplex - normDFT1D (fun j => (W_conjFixed j).toComplex) m) ≤
        (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm (fun j => (W_conjFixed j).toComplex)) at hb
      rw [hW_toC] at hb
      have ha : ‖cFixed.toComplex - normDFT1D W_conj k‖ ≤
          vecInfNorm (fun m => (CFixed_vec m).toComplex - normDFT1D W_conj m) :=
        norm_le_vecInfNorm (fun m => (CFixed_vec m).toComplex - normDFT1D W_conj m) k
      calc ‖cFixed.toComplex - normDFT1D W_conj k‖
          ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 (vecInfNorm W_conj) := ha.trans hb
        _ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * 2 := mul_le_mul_of_nonneg_left hW_max (le_of_lt h2p0_pos)
        _ = 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by ring
    have h2 : ‖normDFT1D W_conj k - normDFT1D W_true k‖ ≤
        (11 / 2 : ℝ) * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      rw [← normDFT1D_sub]
      exact (norm_normDFT1D_le (fun u => W_conj u - W_true u) k).trans
        (vecInfNorm_le _ (by positivity) hW_err)
    have htri := norm_sub_le_norm_sub_add_norm_sub
      cFixed.toComplex (normDFT1D W_conj k) (normDFT1D W_true k)
    linarith
  have hW_true_id : ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) *
      starRingEnd ℂ (normDFT1D W_true k))) = cVec k := by
    have hR0_pos_nat : 0 < R0 := by have := rootR0_ge_four n; omega
    have hR0_ne_c : (R0 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hR0_pos_nat)
    have hscale_real : ((2 ^ (2 * b) : ℕ) : ℝ) *
        ((2 : ℝ) ^ (-(b : ℤ)) * (2 : ℝ) ^ (-(b : ℤ))) = 1 := by
      have h2b : ((2 ^ (2 * b) : ℕ) : ℝ) = (2 : ℝ) ^ b * (2 : ℝ) ^ b := by
        rw [Nat.two_mul, pow_add]; push_cast; rfl
      calc ((2 ^ (2 * b) : ℕ) : ℝ) * ((2 : ℝ) ^ (-(b : ℤ)) * (2 : ℝ) ^ (-(b : ℤ)))
          = ((2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ))) * ((2 : ℝ) ^ b * (2 : ℝ) ^ (-(b : ℤ))) := by
            rw [h2b]; ring
        _ = 1 := by rw [two_pow_mul_two_zpow_neg b, mul_one]
    have hscale_c : ((2 ^ (2 * b) : ℕ) : ℂ) *
        ((((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hscale_real
    let aVec0 : Fin R0 → ℝ := fun j => (natChunk b A j.val : ℝ)
    let bVec0 : Fin R0 → ℝ := fun j => (natChunk b B j.val : ℝ)
    let zVec0 : Fin R0 → ℂ := packRealComplex aVec0 bVec0
    let Z0 : Fin R0 → ℂ := normDFT1D zVec0
    have hz_scale : zVec = fun j => (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * zVec0 j := by
      funext j
      unfold zVec zVec0 packRealComplex aVec bVec aVec0 bVec0
      push_cast
      ring
    have hZ_scale : ∀ u : Fin R0, Z_true u = (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * Z0 u := by
      intro u
      dsimp [Z_true, Z0]
      rw [hz_scale, normDFT1D_smul]
    have hconj_sum :
        (R0 : ℂ) * starRingEnd ℂ (normDFT1D W_true k) =
          ∑ u : Fin R0,
            ((Z_true u * Z_true u) / (2 * Complex.I)) *
              expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R0 : ℝ)) := by
      unfold normDFT1D W_true
      rw [map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
      push_cast
      rw [← mul_assoc, mul_inv_cancel₀ hR0_ne_c, one_mul]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, conj_expTwoPiI]
    dsimp only [cVec, b]
    rw [hconj_sum, ← twoCallDFTConv_eq_linearConvCoeff n A B hA hB k]
    unfold twoCallDFTConv
    dsimp only
    rw [← mul_assoc, mul_comm ((2 ^ (2 * b) : ℕ) : ℂ) (R0 : ℂ), mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hZ_scale u]
    calc ((2 ^ (2 * b) : ℕ) : ℂ) *
          ((((((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * Z0 u) *
            ((((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * Z0 u) / (2 * Complex.I)) *
            expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R0 : ℝ)))
        = (((2 ^ (2 * b) : ℕ) : ℂ) *
            ((((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (-(b : ℤ)) : ℝ) : ℂ))) *
          (((Z0 u * Z0 u) / (2 * Complex.I)) *
            expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R0 : ℝ))) := by ring
      _ = ((Z0 u * Z0 u) / (2 * Complex.I)) *
            expNegTwoPiI (((u.val * k.val : ℕ) : ℝ) / (R0 : ℝ)) := by
          rw [hscale_c, one_mul]
  let conv_c : ℂ := ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) * C_inv_k))
  have hfloor_eq : computableFastTwoCallDFTConv n tree A B k = ⌊conv_c.re + (1 / 2 : ℝ)⌋ := by
    unfold computableFastTwoCallDFTConv
    dsimp only
    simp only [memoizeFin_eq, natChunkFn_eq_natChunk_fun]
    change roundShiftInt (cFixed.conj).re 8 = ⌊conv_c.re + (1 / 2 : ℝ)⌋
    rw [roundShiftInt_eq_quantizeRealMantissa]
    congr 2
    have hp0_eq : p0 + 2 = (2 * b + 2 * K0) + 8 := by unfold p0 rootP0 b K0; omega
    have hzpow : (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ)) =
        (2 : ℝ) ^ (-((2 * b + 2 * K0 : ℕ) : ℤ)) * ((2 : ℝ) ^ 8)⁻¹ := by
      rw [hp0_eq]; push_cast; rw [neg_add_rev, add_comm, zpow_add₀ (by norm_num), zpow_neg]; norm_num
    have hR0_pow : ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * (R0 : ℝ)) =
        (2 : ℝ) ^ (2 * b + 2 * K0) := by
      change ((2 ^ (2 * b) : ℕ) : ℝ) * (((2 ^ K0 : ℕ) : ℝ) * ((2 ^ K0 : ℕ) : ℝ)) = _
      rw [Nat.two_mul K0, pow_add (2 : ℝ) (2 * b), pow_add (2 : ℝ) K0 K0]; push_cast; rfl
    have hre_rhs :
        conv_c.re =
          ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * ((R0 : ℝ) * ((cFixed.re : ℝ) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ))))) := by
      dsimp only [conv_c, C_inv_k]
      rw [← FixedComplex.toComplex_conj]
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
        FixedComplex.toComplex_re, FixedComplex.conj]
    rw [hre_rhs]
    change (cFixed.re : ℝ) / (2 : ℝ) ^ 8 = _
    calc (cFixed.re : ℝ) / (2 : ℝ) ^ 8
        = ((2 : ℝ) ^ (2 * b + 2 * K0) * (2 : ℝ) ^ (-((2 * b + 2 * K0 : ℕ) : ℤ))) *
            ((cFixed.re : ℝ) * ((2 : ℝ) ^ 8)⁻¹) := by
          rw [two_pow_mul_two_zpow_neg, one_mul, div_eq_mul_inv]
      _ = (((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * (R0 : ℝ))) *
            ((cFixed.re : ℝ) * ((2 : ℝ) ^ (-((2 * b + 2 * K0 : ℕ) : ℤ)) * ((2 : ℝ) ^ 8)⁻¹)) := by
          rw [hR0_pow]; ring
      _ = ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * ((R0 : ℝ) * ((cFixed.re : ℝ) * (2 : ℝ) ^ (-((p0 + 2 : ℕ) : ℤ))))) := by
          rw [← hzpow]; ring
  have hR0_pos : (0 : ℝ) < (R0 : ℝ) := by have := rootR0_ge_four n; positivity
  have hR0_ne : (R0 : ℝ) ≠ 0 := ne_of_gt hR0_pos
  have hsub_c : conv_c - cVec k =
      ((2 ^ (2 * b) : ℕ) : ℂ) * ((R0 : ℂ) * ((R0 : ℂ) *
        (C_inv_k - starRingEnd ℂ (normDFT1D W_true k)))) := by
    rw [← hW_true_id]; dsimp [conv_c]; ring
  have hre_div : |conv_c.re / (R0 : ℝ) -
      (linearConvCoeff b (numChunks n) A B k.val : ℝ) / (R0 : ℝ)| ≤
      ‖conv_c - cVec k‖ / (R0 : ℝ) := by
    have hre : conv_c.re / (R0 : ℝ) -
        (linearConvCoeff b (numChunks n) A B k.val : ℝ) / (R0 : ℝ) =
        (conv_c - cVec k).re / (R0 : ℝ) := by
      simp [cVec, sub_div]
    rw [hre, abs_div, abs_of_pos hR0_pos]
    exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (le_of_lt hR0_pos)
  have hnorm_sub : ‖conv_c - cVec k‖ / (R0 : ℝ) =
      (2 : ℝ) ^ (2 * b + K0) * ‖C_inv_k - starRingEnd ℂ (normDFT1D W_true k)‖ := by
    rw [hsub_c, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have hpow_R0 : ((2 ^ (2 * b) : ℕ) : ℝ) * (R0 : ℝ) = (2 : ℝ) ^ (2 * b + K0) := by
      change ((2 ^ (2 * b) : ℕ) : ℝ) * ((2 ^ K0 : ℕ) : ℝ) = (2 : ℝ) ^ (2 * b + K0)
      rw [pow_add]; push_cast; rfl
    calc ((2 ^ (2 * b) : ℕ) : ℝ) * ((R0 : ℝ) * ((R0 : ℝ) *
          ‖C_inv_k - starRingEnd ℂ (normDFT1D W_true k)‖)) / (R0 : ℝ)
        = (((2 ^ (2 * b) : ℕ) : ℝ) * (R0 : ℝ)) *
            ‖C_inv_k - starRingEnd ℂ (normDFT1D W_true k)‖ * ((R0 : ℝ) / (R0 : ℝ)) := by ring
      _ = (2 : ℝ) ^ (2 * b + K0) * ‖C_inv_k - starRingEnd ℂ (normDFT1D W_true k)‖ := by
        rw [div_self hR0_ne, mul_one, hpow_R0]
  have happrox : |conv_c.re / (R0 : ℝ) -
      (linearConvCoeff b (numChunks n) A B k.val : ℝ) / (R0 : ℝ)| ≤
      8 * (2 : ℝ) ^ (-(p0 : ℤ)) * (2 : ℝ) ^ (2 * b + K0) := by
    calc |conv_c.re / (R0 : ℝ) - (linearConvCoeff b (numChunks n) A B k.val : ℝ) / (R0 : ℝ)|
        ≤ ‖conv_c - cVec k‖ / (R0 : ℝ) := hre_div
      _ = (2 : ℝ) ^ (2 * b + K0) * ‖C_inv_k - starRingEnd ℂ (normDFT1D W_true k)‖ := hnorm_sub
      _ ≤ (2 : ℝ) ^ (2 * b + K0) * (8 * (2 : ℝ) ^ (-(p0 : ℤ))) :=
          mul_le_mul_of_nonneg_left hC_inv_err (by positivity)
      _ = 8 * (2 : ℝ) ^ (-(p0 : ℤ)) * (2 : ℝ) ^ (2 * b + K0) := by ring
  have hrec := (root_conv_recovery_of_fastDFT_approx n A B k.val (conv_c.re / (R0 : ℝ)) happrox).2
  have hmul : (R0 : ℝ) * (conv_c.re / (R0 : ℝ)) = conv_c.re := mul_div_cancel₀ _ hR0_ne
  rw [hmul] at hrec
  rw [hfloor_eq, hrec, Int.toNat_natCast]

/-- **Unconditional Bit-Exactness of `computableReconstructProduct` on Any Valid `ScheduleIntTree`
(`computableReconstructProduct_eq_mul_of_validScheduleIntTree`)**:
For all $n \in \mathbb{N}$, any `tree` satisfying `ValidScheduleIntTree tree`, and all $n$-bit
integers $A, B < 2^n$, `computableReconstructProduct n tree A B = A * B`. -/
theorem computableReconstructProduct_eq_mul_of_validScheduleIntTree (n : ℕ)
    {tree : ScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)}
    (htree : ValidScheduleIntTree tree) (A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableReconstructProduct n tree A B = A * B := by
  unfold computableReconstructProduct
  dsimp only
  rw [evalBaseChunks_ofFn_eq_sum]
  have hterm : ∀ k : Fin (rootR0 n),
      (computableFastTwoCallDFTConv n tree A B k).toNat * 2 ^ (k.val * chunkBits n) =
        linearConvCoeff (chunkBits n) (numChunks n) A B k.val * 2 ^ (k.val * chunkBits n) := by
    intro k
    rw [computableFastTwoCallDFTConv_toNat_eq_linearConvCoeff_of_validScheduleIntTree n htree A B hA hB k]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range
      (fun k => linearConvCoeff (chunkBits n) (numChunks n) A B k * 2 ^ (k * chunkBits n))
      (rootR0 n)]
  exact reconstructProductFromChunks_eq_mul n A B hA hB

/-- **Unconditional Bit-Exactness of `computableReconstructProduct` on `computeScheduleIntTree`
(`computableReconstructProduct_computeScheduleIntTree_eq_mul`)**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, the computable pure-integer
pipeline `computableReconstructProduct` evaluated on the dynamically Taylor-synthesized schedule tree
`computeScheduleIntTree` (with **zero** `noncomputable`, **zero** `ℝ`, and **zero** `ℂ`) recovers
`A * B` bit-exactly. -/
@[simp]
theorem computableReconstructProduct_computeScheduleIntTree_eq_mul (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableReconstructProduct n
      (computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
      A B = A * B :=
  computableReconstructProduct_eq_mul_of_validScheduleIntTree n
    (validScheduleIntTree_computeScheduleIntTree (rootK0 n) (rootP0 n)
      (levelScheduleBIn (rootK0 n) (rootP0 n) 0))
    A B hA hB

/-- **Computable Parameter-Free End-to-End Integer Multiplication Bit-List Pipeline
(`computableIntMulBits`)**:
A computable (`def`, zero `noncomputable`, zero `ℝ`, zero `ℂ`, zero `ℚ`) function taking only
`(n, inBits)` with zero external schedule parameter: slices `inBits` directly into $b$-bit chunks via
`sliceBitChunkFn` (never materializing a monolithic $n$-bit `ℕ`), generates the integer schedule tree
via `computeScheduleIntTree`, runs `computableConvFromChunksWithMul`, and emits the $2n$-bit product
bitstream via the single-pass carry-save emitter `carrySaveEmitBits` (never materializing a
monolithic $2n$-bit `ℕ`). -/
def computableIntMulBits (n : ℕ) (inBits : List Bool) : List Bool :=
  let b := chunkBits n
  let R0 := rootR0 n
  let aChunks := sliceBitChunkFn b R0 (inBits.take n)
  let bChunks := sliceBitChunkFn b R0 (inBits.drop n)
  let tree := computeScheduleIntTree (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
  let conv := computableConvFromChunksWithMul (· * ·) n tree aChunks bChunks
  carrySaveEmitBits b (2 * n) (List.ofFn (fun k : Fin R0 => (conv k).toNat)) 0

/-- **Unconditional Bit-Exact Correctness of the Parameter-Free Computable Pipeline
`computableIntMulBits` (`computableIntMulBits_encodeInputBits`)**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, the parameter-free computable
bit-list pipeline `computableIntMulBits n (encodeInputBits n A B)` equals `encodeNatBits (2 * n) (A * B)`
with **zero** `noncomputable` dependencies and **zero** external schedule parameters. -/
@[simp]
theorem computableIntMulBits_encodeInputBits (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableIntMulBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) := by
  unfold computableIntMulBits
  rw [carrySaveEmitBits_conv_eq_encodeNatBits_reconstruct]
  rw [take_encodeInputBits, drop_encodeInputBits,
    decodeNatBits_encodeNatBits n A hA, decodeNatBits_encodeNatBits n B hB,
    computableReconstructProductWithMul_eq_of_mul_eq (· * ·) (fun _ _ => rfl),
    computableReconstructProduct_computeScheduleIntTree_eq_mul n A B hA hB]

/-- Depth-bounded self-recursive computable integer multiplication (`computableNatMulAux`):
- At bootstrap depth `d = 0`, evaluates explicit bit-by-bit shift-and-add multiplication
  `binaryShiftAddMul A B` (with **zero** calls to Lean's built-in `(· * ·)`).
- At depth `d + 1`, generates the integer schedule tree via `computeScheduleIntTreeWithMul` and
  executes `computableReconstructProductWithMul`, routing every sub-word multiplication `(a, b)`
  (both in the schedule series recurrences and in the FFT/Kronecker/deconvolution pipeline) to
  `computableNatMulAux d (operandBitWidth a b) a b` at the true operand bit-width
  `operandBitWidth a b = O(\log n)`. -/
def computableNatMulAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _n, A, B => binaryShiftAddMul A B
  | d + 1, n, A, B =>
    let subMul : ℕ → ℕ → ℕ := fun a b => computableNatMulAux d (operandBitWidth a b) a b
    let tree := computeScheduleIntTreeWithMul subMul
      (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
    computableReconstructProductWithMul subMul n tree A B

/-- **Self-Recursive Computable Integer Multiplication Pipeline (`computableNatMul`)**:
Executes `computableNatMulAux 2 n A B` (2 levels of fast-DFT recursion from $n$ bits down to
$O(\log n)$-bit Kronecker/fixed-point sub-products and then $O(\log \log n)$-bit base cases,
with **zero** calls to Lean's built-in `(· * ·)`). -/
def computableNatMul (n A B : ℕ) : ℕ :=
  computableNatMulAux 2 n A B

/-- **Unconditional Exactness of `computableNatMulAux` (`computableNatMulAux_eq_mul`)**:
For all depths $d \in \mathbb{N}$, all $n \in \mathbb{N}$, and all $n$-bit integers $A, B < 2^n$,
`computableNatMulAux d n A B = A * B`. -/
@[simp]
theorem computableNatMulAux_eq_mul (d : ℕ) :
    ∀ n A B : ℕ, A < 2 ^ n → B < 2 ^ n → computableNatMulAux d n A B = A * B := by
  induction d with
  | zero =>
    intro n A B _ _
    exact binaryShiftAddMul_eq_mul A B
  | succ d ih =>
    intro n A B hA hB
    unfold computableNatMulAux
    have hsub : ∀ a b : ℕ, computableNatMulAux d (operandBitWidth a b) a b = a * b :=
      fun a b => ih (operandBitWidth a b) a b
        (lt_two_pow_operandBitWidth_left a b) (lt_two_pow_operandBitWidth_right a b)
    dsimp only
    rw [computableReconstructProductWithMul_eq_of_mul_eq _ hsub,
      computeScheduleIntTreeWithMul_eq_computeScheduleIntTree hsub]
    exact computableReconstructProduct_computeScheduleIntTree_eq_mul n A B hA hB

/-- **Unconditional Exactness of the Self-Recursive Computable Multiplication `computableNatMul`
(`computableNatMul_eq_mul`)**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$, `computableNatMul n A B = A * B`. -/
@[simp]
theorem computableNatMul_eq_mul (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableNatMul n A B = A * B :=
  computableNatMulAux_eq_mul 2 n A B hA hB

/-- **Self-Recursive Parameter-Free Computable Bit-List Multiplication (`computableNatMulBits`)**:
Slices `inBits` directly into $b$-bit chunks via `sliceBitChunkFn` (never materializing a
monolithic $n$-bit `ℕ`), runs the self-recursive `computableConvFromChunksWithMul` with
`computeScheduleIntTreeWithMul`, and emits the $2n$-bit product bitstream via the single-pass
carry-save emitter `carrySaveEmitBits` (never materializing a monolithic $2n$-bit `ℕ`). -/
def computableNatMulBits (n : ℕ) (inBits : List Bool) : List Bool :=
  let b := chunkBits n
  let R0 := rootR0 n
  let aChunks := sliceBitChunkFn b R0 (inBits.take n)
  let bChunks := sliceBitChunkFn b R0 (inBits.drop n)
  let subMul : ℕ → ℕ → ℕ := fun x y => computableNatMulAux 1 (operandBitWidth x y) x y
  let tree := computeScheduleIntTreeWithMul subMul
    (rootK0 n) (rootP0 n) (levelScheduleBIn (rootK0 n) (rootP0 n) 0)
  let conv := computableConvFromChunksWithMul subMul n tree aChunks bChunks
  carrySaveEmitBits b (2 * n) (List.ofFn (fun k : Fin R0 => (conv k).toNat)) 0

/-- **Unconditional Bit-Exact Correctness of `computableNatMulBits`
(`computableNatMulBits_encodeInputBits`)**:
For all $n \in \mathbb{N}$ and all $n$-bit integers $A, B < 2^n$,
`computableNatMulBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B)`. -/
@[simp]
theorem computableNatMulBits_encodeInputBits (n A B : ℕ)
    (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    computableNatMulBits n (encodeInputBits n A B) = encodeNatBits (2 * n) (A * B) := by
  unfold computableNatMulBits
  rw [carrySaveEmitBits_conv_eq_encodeNatBits_reconstruct]
  rw [take_encodeInputBits, drop_encodeInputBits,
    decodeNatBits_encodeNatBits n A hA, decodeNatBits_encodeNatBits n B hB]
  change encodeNatBits (2 * n) (computableNatMul n A B) = encodeNatBits (2 * n) (A * B)
  rw [computableNatMul_eq_mul n A B hA hB]

end IntMul

#print axioms IntMul.radix2FFT1DFixed_toComplex_eq_radix2FFT1DQuant
#print axioms IntMul.baseRadix2FFTFixed_canonical_eq
#print axioms IntMul.toComplex_cyclicBidiagPrevSolveFixed
#print axioms IntMul.toComplex_nyquistColumnSolveFixed
#print axioms IntMul.computeScheduleIntTree
#print axioms IntMul.validScheduleIntTree_computeScheduleIntTree
#print axioms IntMul.vecInfNorm_computableFastDFTRecursive_sub_normDFT1D_le_two_zpow
#print axioms IntMul.computableFastDFTRecursive
#print axioms IntMul.computableFastDFTRecursiveWithMul_eq_of_mul_eq
#print axioms IntMul.computableFastDFTRecursive_canonical_eq_fastDFTRecursiveSched
#print axioms IntMul.computableReconstructProduct
#print axioms IntMul.computableFastTwoCallDFTConv_canonical_eq
#print axioms IntMul.computableReconstructProduct_canonical_eq_mul
#print axioms IntMul.computableReconstructProduct_computeScheduleIntTree_eq_mul
#print axioms IntMul.computableIntMulBits
#print axioms IntMul.computableIntMulBits_encodeInputBits
#print axioms IntMul.computableNatMul
#print axioms IntMul.computableNatMul_eq_mul
#print axioms IntMul.computableNatMulBits_encodeInputBits
