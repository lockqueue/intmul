import IntMul.ExecutableAlgorithm

/-!
# Adaptive Leaf-Stopping Schedule (`buildQuantizedSpecPaperStop`) and `BaseRadix2FFT` Leaves
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## Adaptive Leaf-Stopping Schedule (`buildQuantizedSpecPaperStop`, `[MS]` §7) and `BaseRadix2FFT` Leaf

Note: The raw-tap and series-evaluation precomputation cost `precomputeStepRawTapBitCost`,
`QuantizedFastDFTSpec.precomputeRawTapCost`, `buildQuantizedSpec_precomputeRawTapCost_le`, and
`buildQuantizedSpec_precomputeRawTapCost_le_quad_of_sq_le_sqrt` are defined in `IntMul.ExecutableAlgorithm`
and directly incorporated into `quantizedFastDFTMultiplyIntrinsicCost` and `quantizedMultiplyOfBitLength`.
Below we formalize:
1. The paper's adaptive stopping-rule schedule builder `buildQuantizedSpecPaperStop`
   (halting at $2^K \le 4 p^2$, i.e., $R_\ell \le 4 p_\ell^2$), proving unconditional validity
   `buildQuantizedSpecPaperStop_valid` for all $L, K$ and $8 \le p$.
2. The paper's Radix-2 Cooley-Tukey FFT leaf `baseRadix2FFTExact`, `baseRadix2FFTQuantizedCore`,
   and `baseRadix2FFTQuantized` (performing $R_L \log_2 R_L$ quantized butterflies with per-stage
   division-by-2 rounding `complexQuantize q_leaf ((Y0 + prod_q) / 2)`), proving exact algebraic
   equivalence `baseRadix2FFTExact_eq_dft1D` and the leaf error bound
   `norm_baseRadix2FFTQuantized_sub_dft1D_le` ($\le 2^{-p} M$).
3. The multi-level quantized Sinc-Gaussian transform `sincGaussianFastDFTRadix2Leaf` and integer
   multiplier `quantizedFastDFTMultiplyRadix2Leaf` using `baseRadix2FFTQuantized` at every leaf,
   together with `[MS]` Theorem 1's three-term complexity bound (`C_syn+route + C_ovh + C_base` where
   $C_{\text{base}} = O(R_0 (\log_2 P + 1) \operatorname{subMulRate}(P)) = O(n (\log \log n)^2 \log \log \log n)$).
4. The fallback comparison `buildQuantizedSpec_intrinsicCostLeafMul_eq` showing that for the deep
   fallback schedule `buildQuantizedSpec` ($R_L \le 4$, twiddles $\in \{\pm 1, \pm i\}$), leaf
   multiplication pricing leaves its cost identically unchanged. -/

/-- Monotonicity of `K ↦ K - K / 2`: if `a ≤ b`, then `a - a / 2 ≤ b - b / 2`. -/
theorem sub_half_mono {a b : ℕ} (h : a ≤ b) : a - a / 2 ≤ b - b / 2 := by
  omega

/-- Paper-schedule multi-level builder (`buildQuantizedSpecPaperStop L p K`, `[MS]` §7):
halts recursion and emits `.base p (2 ^ K)` as soon as the paper's leaf threshold
`2 ^ K ≤ 4 * p * p` ($R_\ell \le 4 p_\ell^2$) is reached (or when the fuel `L` reaches `0`),
and otherwise recurses via `quantizedBoxGaussianStepSpec p K`. -/
def buildQuantizedSpecPaperStop : ℕ → ℕ → ℕ → QuantizedFastDFTSpec
  | 0, p, K => .base p (2 ^ K)
  | L + 1, p, K =>
    if 2 ^ K ≤ 4 * p * p then
      .base p (2 ^ K)
    else
      quantizedBoxGaussianStepSpec p K
        (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2))

@[simp]
theorem buildQuantizedSpecPaperStop_size (L p K : ℕ) :
    (buildQuantizedSpecPaperStop L p K).size = 2 ^ K := by
  cases L with
  | zero => rfl
  | succ L =>
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs
    · rfl
    · dsimp [quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.size]
      rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]

@[simp]
theorem buildQuantizedSpecPaperStop_p (L p K : ℕ) :
    (buildQuantizedSpecPaperStop L p K).p = p := by
  cases L with
  | zero => rfl
  | succ L =>
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs <;> rfl

/-- **Unconditional Validity of `buildQuantizedSpecPaperStop` (`buildQuantizedSpecPaperStop_valid`, `[MS]` §7)**:
For ANY fuel `L`, ANY log-length `K`, and any precision `8 ≤ p` (with zero requirement that `2 ^ L ≤ K`),
`buildQuantizedSpecPaperStop L p K` satisfies `QuantizedFastDFTSpec.Valid` because any node that
does not halt at `2 ^ K ≤ 4 * p * p` has `2 ^ K > 4 * 8^2 = 256`, hence `K ≥ 9 ≥ 2`. -/
theorem buildQuantizedSpecPaperStop_valid (L p K : ℕ) (hp : 8 ≤ p) :
    (buildQuantizedSpecPaperStop L p K).Valid := by
  induction L generalizing p K with
  | zero =>
    exact QuantizedFastDFTSpec.Valid.base p (2 ^ K)
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · exact QuantizedFastDFTSpec.Valid.base p (2 ^ K)
    · have hK2 : 2 ≤ K := by
        by_contra hlt
        have hpow : 2 ^ K ≤ 2 ^ 1 := Nat.pow_le_pow_right zero_lt_two (by omega)
        have hp2 : 256 ≤ 4 * p * p := by nlinarith
        omega
      have hp_child : 8 ≤ pChild p K := by
        unfold pChild pWork
        omega
      exact quantizedBoxGaussianStepSpec_valid p K hp hK2
        (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2))
        (buildQuantizedSpecPaperStop_size L (pChild p K) (K - K / 2))
        (buildQuantizedSpecPaperStop_p L (pChild p K) (K - K / 2))
        (ih (pChild p K) (K - K / 2) hp_child)

/-- Periodicity of `stdChar` when reducing the numerator modulo `N`. -/
theorem stdChar_mod_div_eq (N u : ℕ) (hN : 0 < N) :
    stdChar (((u % N : ℕ) : ℝ) / (N : ℝ)) = stdChar ((u : ℝ) / (N : ℝ)) := by
  have hdiv : (u : ℤ) = (u % N : ℕ) + (u / N : ℕ) * (N : ℤ) := by
    have hnat : u = u % N + (u / N) * N := by
      have h := Nat.mod_add_div u N
      linarith
    exact_mod_cast hnat
  have hmod := stdChar_mod_t1_eq N hN 1 (u % N : ℕ) (u : ℤ) (u / N : ℕ) hdiv
  simpa only [Int.cast_one, one_mul, Int.cast_natCast] using hmod.symm

/-- **Exact Normalized Radix-2 Cooley-Tukey FFT (`baseRadix2FFTExact`, `[MS]` §7)**:
Recursively computes the normalized 1D DFT `dft1D (2 ^ K) x u` by splitting into even and odd
sub-transforms `Y0`, `Y1` of length `2 ^ (K - 1)` and combining via `(Y0 + ω * Y1) / 2`. -/
noncomputable def baseRadix2FFTExact : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x, _ => x 0
  | K + 1, x, u =>
    let Y0 := baseRadix2FFTExact K (fun j => x (2 * j)) u
    let Y1 := baseRadix2FFTExact K (fun j => x (2 * j + 1)) u
    let ω := stdChar (((u % 2 ^ (K + 1) : ℕ) : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ))
    (Y0 + ω * Y1) / 2

/-- **Algebraic Equivalence of `baseRadix2FFTExact` and `dft1D (2 ^ K)` (`baseRadix2FFTExact_eq_dft1D`, `[MS]` §7)**:
For every log-length `K`, input `x : ℕ → ℂ`, and frequency index `u : ℕ`,
`baseRadix2FFTExact K x u = dft1D (2 ^ K) x u`. -/
theorem baseRadix2FFTExact_eq_dft1D (K : ℕ) (x : ℕ → ℂ) (u : ℕ) :
    baseRadix2FFTExact K x u = dft1D (2 ^ K) x u := by
  induction K generalizing x u with
  | zero =>
    dsimp [baseRadix2FFTExact, dft1D]
    simp [stdChar_zero]
  | succ K ih =>
    dsimp only [baseRadix2FFTExact]
    rw [ih (fun j => x (2 * j)) u, ih (fun j => x (2 * j + 1)) u]
    have hpow_pos : 0 < 2 ^ (K + 1) := pow_pos zero_lt_two (K + 1)
    rw [stdChar_mod_div_eq (2 ^ (K + 1)) u hpow_pos]
    unfold dft1D
    have h2K : 2 ^ (K + 1) = 2 * 2 ^ K := pow_succ' 2 K
    have h2K_pos : (0 : ℝ) < ((2 ^ K : ℕ) : ℝ) := by positivity
    have h2K_ne : ((2 ^ K : ℕ) : ℝ) ≠ 0 := h2K_pos.ne'
    have h2K_c_ne : ((2 ^ K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h2K_ne
    have hsum_split :
        ∑ j ∈ Finset.range (2 ^ (K + 1)),
          x j * stdChar (((j * u : ℕ) : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ)) =
        (∑ m ∈ Finset.range (2 ^ K),
          x (2 * m) * stdChar (((m * u : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ))) +
        stdChar ((u : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ)) *
          (∑ m ∈ Finset.range (2 ^ K),
            x (2 * m + 1) * stdChar (((m * u : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ))) := by
      conv_lhs =>
        arg 1
        rw [h2K]
      rw [sum_range_two_mul_even_odd (2 ^ K)
        (fun j => x j * stdChar (((j * u : ℕ) : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ)))]
      congr 1
      · refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        congr 1
        rw [h2K]
        push_cast
        field_simp [h2K_ne]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have harg :
            (((2 * m + 1) * u : ℕ) : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ) =
              (u : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ) +
                ((m * u : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) := by
          rw [h2K]
          push_cast
          field_simp [h2K_ne]
          ring
        rw [harg, stdChar_add]
        ring
    dsimp only
    rw [hsum_split]
    have hcast_2K1 : ((2 ^ (K + 1) : ℕ) : ℂ) = 2 * ((2 ^ K : ℕ) : ℂ) := by
      rw [h2K]
      push_cast
      ring
    rw [hcast_2K1]
    field_simp [h2K_c_ne]

/-- **Quantized Radix-2 Cooley-Tukey FFT Core (`baseRadix2FFTQuantizedCore`, `[MS]` §7)**:
Executes `K` stages of radix-2 Cooley-Tukey butterflies at working precision `q_leaf`, quantizing
inputs, twiddle factors, twiddle products, and per-stage `/ 2` butterfly averages via `complexQuantize q_leaf`. -/
noncomputable def baseRadix2FFTQuantizedCore (q_leaf : ℕ) : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x, _ => complexQuantize q_leaf (x 0)
  | K + 1, x, u =>
    let Y0 := baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j)) u
    let Y1 := baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j + 1)) u
    let ω_q := complexQuantize q_leaf
      (stdChar (((u % 2 ^ (K + 1) : ℕ) : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ)))
    let prod_q := complexQuantize q_leaf (ω_q * Y1)
    complexQuantize q_leaf ((Y0 + prod_q) / 2)

/-- Periodicity of `baseRadix2FFTQuantizedCore q_leaf K x u` modulo `2 ^ K`:
enables materializing the two recursive calls `Y0`, `Y1` as arrays of size `2 ^ K` and indexing
them at `u % 2 ^ K` to produce all `2 ^ (K + 1)` outputs in `O(K * 2 ^ K)` operations. -/
theorem baseRadix2FFTQuantizedCore_mod (q_leaf K : ℕ) (x : ℕ → ℂ) (u : ℕ) :
    baseRadix2FFTQuantizedCore q_leaf K x (u % 2 ^ K) =
      baseRadix2FFTQuantizedCore q_leaf K x u := by
  induction K generalizing x u with
  | zero => rfl
  | succ K ih =>
    dsimp only [baseRadix2FFTQuantizedCore]
    have hdvd : 2 ^ K ∣ 2 ^ (K + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ K)
    have hmod_K : (u % 2 ^ (K + 1)) % 2 ^ K = u % 2 ^ K := Nat.mod_mod_of_dvd u hdvd
    have hY0 :
        baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j)) (u % 2 ^ (K + 1)) =
          baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j)) u := by
      rw [← ih (fun j => x (2 * j)) (u % 2 ^ (K + 1)), hmod_K, ih (fun j => x (2 * j)) u]
    have hY1 :
        baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j + 1)) (u % 2 ^ (K + 1)) =
          baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j + 1)) u := by
      rw [← ih (fun j => x (2 * j + 1)) (u % 2 ^ (K + 1)), hmod_K, ih (fun j => x (2 * j + 1)) u]
    rw [hY0, hY1, Nat.mod_mod]

/-- **Per-Stage Error Closure for `baseRadix2FFTQuantizedCore` (`norm_baseRadix2FFTQuantizedCore_sub_exact_le`, `[MS]` §7)**:
Because each normalized butterfly divides the sum of its two sub-transforms by `2`, the recursive
errors of `Y0` and `Y1` average rather than double at each stage, accumulating linearly as
`((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf * M`. -/
theorem norm_baseRadix2FFTQuantizedCore_sub_exact_le
    (q_leaf K : ℕ)
    (hq : ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf ≤ 1)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < 2 ^ K, ‖x k‖ ≤ M) (u : ℕ) :
    ‖baseRadix2FFTQuantizedCore q_leaf K x u - baseRadix2FFTExact K x u‖ ≤
      ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf * M := by
  induction K generalizing x u with
  | zero =>
    dsimp only [baseRadix2FFTQuantizedCore, baseRadix2FFTExact]
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr q_leaf := by
      unfold complexQuantizeMaxErr; positivity
    have h1 : ‖complexQuantize q_leaf (x 0) - x 0‖ ≤ complexQuantizeMaxErr q_leaf :=
      norm_complexQuantize_sub_le q_leaf (x 0)
    push_cast
    nlinarith
  | succ K ih =>
    dsimp only [baseRadix2FFTQuantizedCore, baseRadix2FFTExact]
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr q_leaf := by
      unfold complexQuantizeMaxErr; positivity
    have hq_K : ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf ≤ 1 := by
      have hle : ((K + 1 : ℕ) : ℝ) ≤ ((K + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (K + 1)
      nlinarith
    have hx0 : ∀ j < 2 ^ K, ‖x (2 * j)‖ ≤ M := by
      intro j hj
      have hlt : 2 * j < 2 ^ (K + 1) := by
        rw [pow_succ']
        omega
      exact hx (2 * j) hlt
    have hx1 : ∀ j < 2 ^ K, ‖x (2 * j + 1)‖ ≤ M := by
      intro j hj
      have hlt : 2 * j + 1 < 2 ^ (K + 1) := by
        rw [pow_succ']
        omega
      exact hx (2 * j + 1) hlt
    set Y0 := baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j)) u
    set Y0_ex := baseRadix2FFTExact K (fun j => x (2 * j)) u
    set Y1 := baseRadix2FFTQuantizedCore q_leaf K (fun j => x (2 * j + 1)) u
    set Y1_ex := baseRadix2FFTExact K (fun j => x (2 * j + 1)) u
    set ω := stdChar (((u % 2 ^ (K + 1) : ℕ) : ℝ) / ((2 ^ (K + 1) : ℕ) : ℝ))
    set ω_q := complexQuantize q_leaf ω
    set prod_q := complexQuantize q_leaf (ω_q * Y1)
    set E_K : ℝ := ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf * M
    have hY0_err : ‖Y0 - Y0_ex‖ ≤ E_K := ih hq_K (fun j => x (2 * j)) hx0 u
    have hY1_err : ‖Y1 - Y1_ex‖ ≤ E_K := ih hq_K (fun j => x (2 * j + 1)) hx1 u
    have hY1_ex_norm : ‖Y1_ex‖ ≤ M := by
      dsimp [Y1_ex]
      rw [baseRadix2FFTExact_eq_dft1D]
      exact dft1D_norm_le (2 ^ K) (pow_pos zero_lt_two K) (fun j => x (2 * j + 1)) M
        (fun j hj => hx1 j (Finset.mem_range.mp hj)) u
    have hEK_le_M : E_K ≤ M := by
      dsimp [E_K]
      nlinarith
    have hY1_norm : ‖Y1‖ ≤ 2 * M := by
      have htri := norm_add_le (Y1 - Y1_ex) Y1_ex
      rw [sub_add_cancel] at htri
      linarith
    have hprod_err : ‖prod_q - ω * Y1_ex‖ ≤ 3 * complexQuantizeMaxErr q_leaf * M + E_K := by
      have hsplit : prod_q - ω * Y1_ex =
          (prod_q - ω_q * Y1) + (ω_q - ω) * Y1 + ω * (Y1 - Y1_ex) := by ring
      rw [hsplit]
      have h1 : ‖prod_q - ω_q * Y1‖ ≤ complexQuantizeMaxErr q_leaf :=
        norm_complexQuantize_sub_le q_leaf (ω_q * Y1)
      have h2_tw : ‖ω_q - ω‖ ≤ complexQuantizeMaxErr q_leaf :=
        norm_complexQuantize_sub_le q_leaf ω
      have h2 : ‖(ω_q - ω) * Y1‖ ≤ complexQuantizeMaxErr q_leaf * (2 * M) := by
        rw [norm_mul]
        exact mul_le_mul h2_tw hY1_norm (norm_nonneg _) hq_nonneg
      have h3 : ‖ω * (Y1 - Y1_ex)‖ ≤ E_K := by
        rw [norm_mul, norm_stdChar, one_mul]
        exact hY1_err
      have htri1 := norm_add_le ((prod_q - ω_q * Y1) + (ω_q - ω) * Y1) (ω * (Y1 - Y1_ex))
      have htri2 := norm_add_le (prod_q - ω_q * Y1) ((ω_q - ω) * Y1)
      nlinarith
    have havg_err :
        ‖(Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2‖ ≤
          E_K + (1.5 : ℝ) * complexQuantizeMaxErr q_leaf * M := by
      have hsub : (Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2 =
          ((Y0 - Y0_ex) + (prod_q - ω * Y1_ex)) / 2 := by ring
      rw [hsub, norm_div, Complex.norm_ofNat]
      have htri := norm_add_le (Y0 - Y0_ex) (prod_q - ω * Y1_ex)
      linarith
    have hout_round :
        ‖complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0 + prod_q) / 2‖ ≤
          complexQuantizeMaxErr q_leaf :=
      norm_complexQuantize_sub_le q_leaf ((Y0 + prod_q) / 2)
    have htri_out :
        ‖complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0_ex + ω * Y1_ex) / 2‖ ≤
          ‖complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0 + prod_q) / 2‖ +
            ‖(Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2‖ := by
      have hsplit :
          complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0_ex + ω * Y1_ex) / 2 =
            (complexQuantize q_leaf ((Y0 + prod_q) / 2) - (Y0 + prod_q) / 2) +
              ((Y0 + prod_q) / 2 - (Y0_ex + ω * Y1_ex) / 2) := by ring
      rw [hsplit]
      exact norm_add_le _ _
    have hcast : ((K + 1 + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf * M =
        E_K + 3 * complexQuantizeMaxErr q_leaf * M := by
      dsimp [E_K]
      push_cast
      ring
    rw [hcast]
    nlinarith

/-- **Quantized Radix-2 Cooley-Tukey FFT Leaf (`baseRadix2FFTQuantized`, `[MS]` §7)**:
Executes `baseRadix2FFTQuantizedCore` at working precision `q_leaf = 2 * p + K + 8` and quantizes
the final output to `p + 2` fractional bits via `complexQuantize p`. -/
noncomputable def baseRadix2FFTQuantized (p K : ℕ) (x : ℕ → ℂ) (u : ℕ) : ℂ :=
  let q_leaf := 2 * p + K + 8
  complexQuantize p (baseRadix2FFTQuantizedCore q_leaf K x u)

/-- Helper bound: for `q_leaf = 2 * p + K + 8`,
`((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf ≤ (0.005 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))`. -/
theorem baseRadix2FFTQuantized_core_err_factor_le (p K : ℕ) :
    ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr (2 * p + K + 8) ≤
      (0.005 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by
  set q_leaf := 2 * p + K + 8
  have hK_le : ((K + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast add_one_le_two_pow K
  have hq_lt : complexQuantizeMaxErr q_leaf < (0.354 : ℝ) * (2 : ℝ) ^ (-(q_leaf : ℤ)) :=
    complexQuantizeMaxErr_lt q_leaf
  have hpow_le :
      (2 : ℝ) ^ (-(q_leaf : ℤ)) ≤
        (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 256 : ℝ) := by
    have hexp : -(q_leaf : ℤ) ≤ -(K : ℤ) + -(p : ℤ) + (-8 : ℤ) := by
      dsimp [q_leaf]
      omega
    calc (2 : ℝ) ^ (-(q_leaf : ℤ))
        ≤ (2 : ℝ) ^ (-(K : ℤ) + -(p : ℤ) + (-8 : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) hexp
      _ = (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) * (2 : ℝ) ^ (-8 : ℤ) := by
          rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
      _ = (2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 256 : ℝ) := by norm_num
  have hK_cancel : (2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ)) = 1 := by
    rw [← zpow_add₀ (by norm_num), add_neg_cancel, zpow_zero]
  have hpow_p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hq_nonneg : 0 ≤ complexQuantizeMaxErr q_leaf := by
    unfold complexQuantizeMaxErr; positivity
  calc ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf
      ≤ (2 : ℝ) ^ (K : ℤ) * 3 *
          ((0.354 : ℝ) * ((2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 256 : ℝ))) := by
        have h1 : ((K + 1 : ℕ) : ℝ) * 3 ≤ (2 : ℝ) ^ (K : ℤ) * 3 := by linarith
        have h2 : complexQuantizeMaxErr q_leaf ≤
            (0.354 : ℝ) * ((2 : ℝ) ^ (-(K : ℤ)) * (2 : ℝ) ^ (-(p : ℤ)) * (1 / 256 : ℝ)) := by
          linarith
        exact mul_le_mul h1 h2 hq_nonneg (by positivity)
    _ = ((2 : ℝ) ^ (K : ℤ) * (2 : ℝ) ^ (-(K : ℤ))) *
          (3 * (0.354 : ℝ) * (1 / 256 : ℝ)) * (2 : ℝ) ^ (-(p : ℤ)) := by ring
    _ = (3 * (0.354 : ℝ) * (1 / 256 : ℝ)) * (2 : ℝ) ^ (-(p : ℤ)) := by
        rw [hK_cancel, one_mul]
    _ ≤ (0.005 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) := by nlinarith

/-- **Unconditional Error Bound for `baseRadix2FFTQuantized` (`norm_baseRadix2FFTQuantized_sub_dft1D_le`, `[MS]` §7)**:
For all `p, K : ℕ`, any `1 ≤ M` with `∀ k < 2 ^ K, ‖x k‖ ≤ M`, and any `u : ℕ`,
`‖baseRadix2FFTQuantized p K x u - dft1D (2 ^ K) x u‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) * M`. -/
theorem norm_baseRadix2FFTQuantized_sub_dft1D_le
    (p K : ℕ) (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < 2 ^ K, ‖x k‖ ≤ M) (u : ℕ) :
    ‖baseRadix2FFTQuantized p K x u - dft1D (2 ^ K) x u‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) * M := by
  unfold baseRadix2FFTQuantized
  dsimp only
  set q_leaf := 2 * p + K + 8
  have hfac := baseRadix2FFTQuantized_core_err_factor_le p K
  have hpow_le_one : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hq_cond : ((K + 1 : ℕ) : ℝ) * 3 * complexQuantizeMaxErr q_leaf ≤ 1 := by
    linarith
  have hcore := norm_baseRadix2FFTQuantizedCore_sub_exact_le q_leaf K hq_cond x M hM1 hx u
  rw [baseRadix2FFTExact_eq_dft1D] at hcore
  have hM_pos : 0 < M := by linarith
  have hcore_le :
      ‖baseRadix2FFTQuantizedCore q_leaf K x u - dft1D (2 ^ K) x u‖ ≤
        (0.005 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
    hcore.trans (mul_le_mul_of_nonneg_right hfac hM_pos.le)
  have hout_le :
      ‖complexQuantize p (baseRadix2FFTQuantizedCore q_leaf K x u) -
        baseRadix2FFTQuantizedCore q_leaf K x u‖ ≤
        (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr p := by unfold complexQuantizeMaxErr; positivity
    have h1 := norm_complexQuantize_sub_le p (baseRadix2FFTQuantizedCore q_leaf K x u)
    have h2 := (complexQuantizeMaxErr_lt p).le
    nlinarith
  have htri :
      ‖complexQuantize p (baseRadix2FFTQuantizedCore q_leaf K x u) - dft1D (2 ^ K) x u‖ ≤
        ‖complexQuantize p (baseRadix2FFTQuantizedCore q_leaf K x u) -
          baseRadix2FFTQuantizedCore q_leaf K x u‖ +
          ‖baseRadix2FFTQuantizedCore q_leaf K x u - dft1D (2 ^ K) x u‖ := by
    have hsplit :
        complexQuantize p (baseRadix2FFTQuantizedCore q_leaf K x u) - dft1D (2 ^ K) x u =
          (complexQuantize p (baseRadix2FFTQuantizedCore q_leaf K x u) -
            baseRadix2FFTQuantizedCore q_leaf K x u) +
            (baseRadix2FFTQuantizedCore q_leaf K x u - dft1D (2 ^ K) x u) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  have hpow_M_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M := by positivity
  linarith

/-- Predicate asserting that every `.base p R` leaf of a `QuantizedFastDFTSpec` has power-of-2 size
`2 ^ (Nat.log2 R) = R`. -/
def QuantizedFastDFTSpec.BasePow2 : QuantizedFastDFTSpec → Prop
  | .base _ R => 2 ^ (Nat.log2 R) = R
  | .step _ _ _ _ _ _ child => child.BasePow2

theorem buildQuantizedSpec_basePow2 (L p K : ℕ) :
    (buildQuantizedSpec L p K).BasePow2 := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpec, QuantizedFastDFTSpec.BasePow2]
    rw [nat_log2_two_pow]
  | succ L ih =>
    dsimp [buildQuantizedSpec, quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.BasePow2]
    exact ih (pChild p K) (K - K / 2)

theorem buildQuantizedSpecPaperStop_basePow2 (L p K : ℕ) :
    (buildQuantizedSpecPaperStop L p K).BasePow2 := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpecPaperStop, QuantizedFastDFTSpec.BasePow2]
    rw [nat_log2_two_pow]
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs
    · dsimp [QuantizedFastDFTSpec.BasePow2]
      rw [nat_log2_two_pow]
    · dsimp [quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.BasePow2]
      exact ih (pChild p K) (K - K / 2)

/-- **Multi-Level Quantized Windowed Sinc-Gaussian `FastDFT` with `BaseRadix2FFT` Leaves (`sincGaussianFastDFTRadix2Leaf`, `[MS]` §§5 & 7)**:
Identical to `sincGaussianFastDFTQuantized` at internal `.step` nodes, and executes the quantized
Cooley-Tukey radix-2 FFT `baseRadix2FFTQuantized p (Nat.log2 R)` at `.base p R` leaves. -/
noncomputable def sincGaussianFastDFTRadix2Leaf : QuantizedFastDFTSpec → (ℕ → ℂ) → ℕ → ℂ
  | .base p R, x, u => baseRadix2FFTQuantized p (Nat.log2 R) x u
  | .step p K t1 r _c1 v1Of child, x, u =>
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * pChild p K
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTRadix2Leaf child (qPost v1) u2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
    let u2 := u % r
    let u1_tilde := u / r
    let y := (u2 : ℝ) / (r : ℝ)
    let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
    let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
    let z_sub :=
      if 2 * u2 < r then
        solveBidiagonalFwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquistQuantized pSub t1 c0 (Y u2) (complexQuantize pSub (nyquistAltSum t1 r x)) u1_tilde
      else
        solveBidiagonalBwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
    complexQuantize p z_sub

/-- **Multi-Level Error Closure Theorem for `sincGaussianFastDFTRadix2Leaf` (`sincGaussianFastDFTRadix2Leaf_error_le`, `[MS]` Lemma 6.5, §6.3 & §7)**:
For any valid specification `spec` with power-of-2 leaves (`spec.BasePow2`), `sincGaussianFastDFTRadix2Leaf`
satisfies the exact same `2 ^ (-spec.p) * M` error bound as `sincGaussianFastDFTQuantized`. -/
theorem sincGaussianFastDFTRadix2Leaf_error_le
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hbase : spec.BasePow2)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < spec.size, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < spec.size) :
    ‖sincGaussianFastDFTRadix2Leaf spec x u - dft1D spec.size x u‖ ≤
      (2 : ℝ) ^ (-(spec.p : ℤ)) * M := by
  induction hvalid generalizing x M u with
  | base p R =>
    dsimp only [sincGaussianFastDFTRadix2Leaf, QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p,
      QuantizedFastDFTSpec.BasePow2] at hbase hx ⊢
    conv_lhs =>
      arg 1; arg 2
      rw [← hbase]
    exact norm_baseRadix2FFTQuantized_sub_dft1D_le p (Nat.log2 R) x M hM1
      (fun k hk => hx k (by rwa [← hbase])) u
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p _hchild hv1 _hv1_lt ih =>
    dsimp only [sincGaussianFastDFTRadix2Leaf, QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p,
      QuantizedFastDFTSpec.BasePow2] at hbase hx hu ⊢
    exact sincGaussianFastDFTStep_error_le hp hK ht1 ht1_le hr hr_le hsize hc1 heven hv1
      (sincGaussianFastDFTRadix2Leaf child)
      (fun x' M' hM1' hx' u' hu' => by
        rw [← hchild_p, ← hchild_size]
        exact ih hbase x' M' hM1' (by rwa [hchild_size]) u' (by rwa [hchild_size]))
      x M hM1 hx u hu

/-- Approximate real convolution coefficient `C_approx(j)` using `sincGaussianFastDFTRadix2Leaf` (`[MS]` §7). -/
noncomputable def quantizedFastDFTConvApproxRadix2Leaf
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B j : ℕ) : ℝ :=
  let x_AB := packNormalizedChunks b k1 k2 A B
  let y : ℕ → ℂ := sincGaussianFastDFTRadix2Leaf spec x_AB
  let p0 := rootPrecision b K0
  let S_tilde : ℕ → ℂ := fun u => complexQuantize p0 ((y u) ^ 2)
  let z_tilde : ℂ := star (sincGaussianFastDFTRadix2Leaf spec (fun u => star (S_tilde u)) j)
  (z_tilde.im) * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)

/-- **End-to-End Quantized Windowed Sinc-Gaussian `FastDFT` Integer Multiplier with `BaseRadix2FFT` Leaves (`quantizedFastDFTMultiplyRadix2Leaf`, `[MS]` §7)**: -/
noncomputable def quantizedFastDFTMultiplyRadix2Leaf
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ :=
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j =>
      ⌊quantizedFastDFTConvApproxRadix2Leaf spec b K0 k1 k2 A B j + (1 / 2 : ℝ)⌋.toNat)
  reconstructChunks b convNat

theorem quantizedFastDFTConvApproxRadix2Leaf_round_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hbase : spec.BasePow2)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) (j : ℕ) (hj : j < 2 ^ K0) :
    ⌊quantizedFastDFTConvApproxRadix2Leaf spec b K0 k1 k2 A B j + (1 / 2 : ℝ)⌋ =
      ((polyMulList (splitChunks b k1 A) (splitChunks b k2 B)).getD j 0 : ℤ) := by
  unfold quantizedFastDFTConvApproxRadix2Leaf
  exact dftApproxConvApprox_round_eq (sincGaussianFastDFTRadix2Leaf spec) b K0 k1 k2 A B
    (fun x M hM1 hx u hu => by
      rw [← hp0, ← hsize]
      exact sincGaussianFastDFTRadix2Leaf_error_le spec hvalid hbase x M hM1
        (by rwa [hsize]) u (by rwa [hsize]))
    hk j hj

/-- **Exact Integer Multiplication Recovery for `quantizedFastDFTMultiplyRadix2Leaf` (`quantizedFastDFTMultiplyRadix2Leaf_eq_mul`, `[MS]` §7)**: -/
theorem quantizedFastDFTMultiplyRadix2Leaf_eq_mul
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid) (hbase : spec.BasePow2)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    quantizedFastDFTMultiplyRadix2Leaf spec b K0 k1 k2 A B = A * B := by
  unfold quantizedFastDFTMultiplyRadix2Leaf
  set xs := splitChunks b k1 A
  set ys := splitChunks b k2 B
  have hmap :
      (List.range (k1 + k2)).map
        (fun j => ⌊quantizedFastDFTConvApproxRadix2Leaf spec b K0 k1 k2 A B j + (1 / 2 : ℝ)⌋.toNat) =
      (List.range (k1 + k2)).map (fun j => (polyMulList xs ys).getD j 0) := by
    refine List.map_congr_left fun j hj_mem => ?_
    have hj_lt : j < k1 + k2 := List.mem_range.mp hj_mem
    have hj_R0 : j < 2 ^ K0 := by omega
    rw [quantizedFastDFTConvApproxRadix2Leaf_round_eq spec hvalid hbase b K0 k1 k2 A B hsize hp0 hk j hj_R0,
        Int.toNat_natCast]
  have hpoly_len : (polyMulList xs ys).length ≤ k1 + k2 := by
    have := length_polyMulList_le xs ys
    rw [length_splitChunks, length_splitChunks] at this
    exact this
  dsimp only
  rw [hmap, reconstructChunks_eq_evalRadix, evalRadix_range_getD (2 ^ b) _ (k1 + k2) hpoly_len,
      ← reconstructChunks_eq_evalRadix]
  exact reconstructChunks_polyMulList_splitChunks b k1 k2 A B hA hB

/-- **Fallback Leaf-Multiplication Intrinsic Cost (`QuantizedFastDFTSpec.intrinsicCostLeafMul`, `[MS]` §7.2)**:
Used to document the deep fallback schedule `buildQuantizedSpec` (which recurses down to `R ≤ 4`,
where twiddles are in `{±1, ±i}` and require zero non-trivial multiplications):
charges `R * R * addBitCost p` when `R ≤ 4` and `R * R * (mulBitCost p + addBitCost p)` when `4 < R`. -/
def QuantizedFastDFTSpec.intrinsicCostLeafMul : QuantizedFastDFTSpec → ℝ
  | .base p R =>
    if R ≤ 4 then ((R * R * addBitCost p : ℕ) : ℝ)
    else ((R * R * (mulBitCost p + addBitCost p) : ℕ) : ℝ)
  | .step p K t1 r _ _ child =>
    let p' := pChild p K
    ((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ) +
      ((kroneckerSpreadStepBitCost t1 r p' : ℕ) : ℝ) +
      ((twistAndSolverStepBitCost t1 r p' : ℕ) : ℝ) +
      ((routingAndStreamingStepBitCost t1 r p' : ℕ) : ℝ) +
      (t1 : ℝ) * child.intrinsicCostLeafMul

/-- **Exact Equality of `intrinsicCostLeafMul` and `intrinsicCost` on Fallback `buildQuantizedSpec` (`[MS]` §7.2)**:
Whenever `K ≤ 2 ^ (L + 1)`, every `.base` leaf of `buildQuantizedSpec L p K` has radix `R ≤ 4`,
so pricing `R > 4` leaves at `R^2 * (mulBitCost p + addBitCost p)` leaves the cost of
`buildQuantizedSpec L p K` identically unchanged. -/
theorem buildQuantizedSpec_intrinsicCostLeafMul_eq
    (L p K : ℕ) (hK_high : K ≤ 2 ^ (L + 1)) :
    (buildQuantizedSpec L p K).intrinsicCostLeafMul =
      (buildQuantizedSpec L p K).intrinsicCost := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpec, QuantizedFastDFTSpec.intrinsicCostLeafMul,
      QuantizedFastDFTSpec.intrinsicCost]
    have hK2 : K ≤ 2 := by simpa using hK_high
    have hpow4 : 2 ^ K ≤ 4 := by
      calc 2 ^ K ≤ 2 ^ 2 := Nat.pow_le_pow_right zero_lt_two hK2
        _ = 4 := by decide
    rw [if_pos hpow4]
  | succ L ih =>
    dsimp [buildQuantizedSpec, quantizedBoxGaussianStepSpec,
      QuantizedFastDFTSpec.intrinsicCostLeafMul, QuantizedFastDFTSpec.intrinsicCost]
    have hK' : K - K / 2 ≤ 2 ^ (L + 1) := by
      have hpow : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
      omega
    rw [ih (pChild p K) (K - K / 2) hK']

/-- For any `q ≤ P`, `mulBitCost q ≤ subMulRate P`. -/
theorem mulBitCost_le_subMulRate (q P : ℕ) (hqP : q ≤ P) :
    mulBitCost q ≤ subMulRate P := by
  unfold mulBitCost subMulRate
  rcases Nat.eq_zero_or_pos q with rfl | hq_pos
  · simp
  · have hP_lt : P < 2 ^ (Nat.log2 P + 1) := lt_two_pow_log2_succ P
    have hq_lt : q < 2 ^ (Nat.log2 P + 1) := hqP.trans_lt hP_lt
    have hlog_lt : Nat.log2 q < Nat.log2 P + 1 :=
      (Nat.log2_lt (by omega)).mpr hq_lt
    have hlog_le : Nat.log2 q + 1 ≤ Nat.log2 P + 1 := by omega
    have hLL_lt : Nat.log2 P + 1 < 2 ^ (Nat.log2 (Nat.log2 P + 1) + 1) :=
      lt_two_pow_log2_succ (Nat.log2 P + 1)
    have hqLL_lt : Nat.log2 q + 1 < 2 ^ (Nat.log2 (Nat.log2 P + 1) + 1) :=
      hlog_le.trans_lt hLL_lt
    have hllog_lt : Nat.log2 (Nat.log2 q + 1) < Nat.log2 (Nat.log2 P + 1) + 1 :=
      (Nat.log2_lt (by omega)).mpr hqLL_lt
    have hllog_le : Nat.log2 (Nat.log2 q + 1) + 1 ≤ Nat.log2 (Nat.log2 P + 1) + 1 := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul hqP hlog_le) hllog_le

/-- For any `q ≤ P`, `addBitCost q ≤ subMulRate P`. -/
theorem addBitCost_le_subMulRate (q P : ℕ) (hqP : q ≤ P) :
    addBitCost q ≤ subMulRate P := by
  unfold addBitCost subMulRate
  calc q = q * 1 * 1 := by ring
    _ ≤ P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hqP (by omega)) (by omega)

/-- For all `1 ≤ P`, `(Nat.log2 P + 1) * subMulRate P ≤ 27 * P * P`. -/
theorem log2_succ_mul_subMulRate_le_27_sq (P : ℕ) (hP : 1 ≤ P) :
    (Nat.log2 P + 1) * subMulRate P ≤ 27 * P * P := by
  unfold subMulRate
  have h2 : Nat.log2 (Nat.log2 P + 1) + 1 ≤ Nat.log2 P + 1 :=
    Nat.add_le_add_right (log2_add_one_le_self (Nat.log2 P)) 1
  have hcube :
      (Nat.log2 P + 1) * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1) ≤ 27 * P := by
    calc (Nat.log2 P + 1) * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)
        ≤ (Nat.log2 P + 1) * (Nat.log2 P + 1) * (Nat.log2 P + 1) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ 27 * P := log2_succ_cube_le_27_mul P hP
  calc (Nat.log2 P + 1) * (P * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1))
      = P * ((Nat.log2 P + 1) * (Nat.log2 P + 1) * (Nat.log2 (Nat.log2 P + 1) + 1)) := by ring
    _ ≤ P * (27 * P) := Nat.mul_le_mul_left P hcube
    _ = 27 * P * P := by ring

/-- Non-negativity of `QuantizedFastDFTSpec.precomputeRawTapCost`. -/
theorem precomputeRawTapCost_nonneg (spec : QuantizedFastDFTSpec) :
    0 ≤ spec.precomputeRawTapCost := by
  induction spec with
  | base p R => simp [QuantizedFastDFTSpec.precomputeRawTapCost]
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [QuantizedFastDFTSpec.precomputeRawTapCost]
    exact add_nonneg (Nat.cast_nonneg _) ih

/-- **Precomputation Cost Monotonicity for `buildQuantizedSpecPaperStop` (`[MS]` §7)**:
Halting early at the paper's leaf threshold `2 ^ K ≤ 4 * p * p` never increases the raw-tap
precomputation cost relative to `buildQuantizedSpec L p K`. -/
theorem buildQuantizedSpecPaperStop_precomputeRawTapCost_le (L p K : ℕ) :
    (buildQuantizedSpecPaperStop L p K).precomputeRawTapCost ≤
      (buildQuantizedSpec L p K).precomputeRawTapCost := by
  induction L generalizing p K with
  | zero => rfl
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop, buildQuantizedSpec]
    split_ifs with hstop
    · dsimp only [QuantizedFastDFTSpec.precomputeRawTapCost]
      exact precomputeRawTapCost_nonneg _
    · dsimp only [quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.precomputeRawTapCost]
      linarith [ih (pChild p K) (K - K / 2)]

/-- **`[MS]` Theorem 1 Intrinsic Cost with `BaseRadix2FFT` Leaves (`QuantizedFastDFTSpec.intrinsicCostRadix2Leaf`, §7.2)**:
Prices each `.base p R` leaf using `BaseRadix2FFT` (`R * (Nat.log2 R + 1)` butterflies at precision `p`,
costing `R * (Nat.log2 R + 1) * (mulBitCost p + addBitCost p)`), matching `[MS]` Theorem 1 leaf
cost $C_{\text{base}} = (R_0 / R_L) \cdot R_L \log_2 R_L \cdot M(p_L)$. -/
def QuantizedFastDFTSpec.intrinsicCostRadix2Leaf : QuantizedFastDFTSpec → ℝ
  | .base p R => ((R * (Nat.log2 R + 1) * (mulBitCost p + addBitCost p) : ℕ) : ℝ)
  | .step p K t1 r _ _ child =>
    let p' := pChild p K
    ((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ) +
      ((kroneckerSpreadStepBitCost t1 r p' : ℕ) : ℝ) +
      ((twistAndSolverStepBitCost t1 r p' : ℕ) : ℝ) +
      ((routingAndStreamingStepBitCost t1 r p' : ℕ) : ℝ) +
      (t1 : ℝ) * child.intrinsicCostRadix2Leaf

/-- Non-negativity of `QuantizedFastDFTSpec.intrinsicCostRadix2Leaf`. -/
theorem QuantizedFastDFTSpec.intrinsicCostRadix2Leaf_nonneg (spec : QuantizedFastDFTSpec) :
    0 ≤ spec.intrinsicCostRadix2Leaf := by
  induction spec with
  | base p R =>
    dsimp [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
    positivity
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
    positivity

/-- `[MS]` Theorem 1 leaf term $C_{\text{base}} = (R_0 / R_L) \cdot R_L (\log_2 R_L + 1) (M(p_L) + A(p_L))$
(`QuantizedFastDFTSpec.radix2LeafCost`, `[MS]` §7.2). -/
def QuantizedFastDFTSpec.radix2LeafCost : QuantizedFastDFTSpec → ℝ
  | .base p R => ((R * (Nat.log2 R + 1) * (mulBitCost p + addBitCost p) : ℕ) : ℝ)
  | .step _ _ t1 _ _ _ child => (t1 : ℝ) * child.radix2LeafCost

/-- `[MS]` Theorem 1 Synthetic FFT and routing term $C_{\text{syn+route}}$
(`QuantizedFastDFTSpec.synAndRouteCost`, `[MS]` §7.2). -/
def QuantizedFastDFTSpec.synAndRouteCost : QuantizedFastDFTSpec → ℝ
  | .base _ _ => 0
  | .step p K t1 r _ _ child =>
    let p' := pChild p K
    ((syntheticFFTStepBitCost t1 r p' : ℕ) : ℝ) +
      ((routingAndStreamingStepBitCost t1 r p' : ℕ) : ℝ) +
      (t1 : ℝ) * child.synAndRouteCost

/-- `[MS]` Theorem 1 Kronecker spread and twist/solver overhead term $C_{\text{ovh}}$
(`QuantizedFastDFTSpec.stepOverheadCost`, `[MS]` §7.2). -/
def QuantizedFastDFTSpec.stepOverheadCost : QuantizedFastDFTSpec → ℝ
  | .base _ _ => 0
  | .step p K t1 r _ _ child =>
    let p' := pChild p K
    ((kroneckerSpreadStepBitCost t1 r p' : ℕ) : ℝ) +
      ((twistAndSolverStepBitCost t1 r p' : ℕ) : ℝ) +
      (t1 : ℝ) * child.stepOverheadCost

/-- **`[MS]` Theorem 1 Three-Term Cost Decomposition (`QuantizedFastDFTSpec.paperStopTotalCost_eq_three_terms`, §7.2)**:
Decomposes `spec.intrinsicCostRadix2Leaf` into $C_{\text{syn+route}} + C_{\text{ovh}} + C_{\text{base}}$. -/
theorem QuantizedFastDFTSpec.paperStopTotalCost_eq_three_terms (spec : QuantizedFastDFTSpec) :
    spec.intrinsicCostRadix2Leaf =
      spec.synAndRouteCost + spec.stepOverheadCost + spec.radix2LeafCost := by
  induction spec with
  | base p R =>
    dsimp [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf,
      QuantizedFastDFTSpec.synAndRouteCost,
      QuantizedFastDFTSpec.stepOverheadCost,
      QuantizedFastDFTSpec.radix2LeafCost]
    ring
  | step p K t1 r c1 v1Of child ih =>
    dsimp only [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf,
      QuantizedFastDFTSpec.synAndRouteCost,
      QuantizedFastDFTSpec.stepOverheadCost,
      QuantizedFastDFTSpec.radix2LeafCost]
    rw [ih]
    ring

/-- If `2 ^ K ≤ 4 * P * P`, then `K + 1 ≤ 4 * (Nat.log2 P + 1)`. -/
theorem log_len_add_one_le_of_two_pow_le_four_mul_sq (K P : ℕ) (hstop : 2 ^ K ≤ 4 * P * P) :
    K + 1 ≤ 4 * (Nat.log2 P + 1) := by
  rcases Nat.eq_zero_or_pos P with rfl | hP_pos
  · have h2K_pos : 0 < 2 ^ K := pow_pos zero_lt_two K
    omega
  · have hP_lt : P < 2 ^ (Nat.log2 P + 1) := lt_two_pow_log2_succ P
    have h4P2_lt : 4 * P * P < 2 ^ (2 * Nat.log2 P + 4) := by
      have hpow_eq : 2 ^ (2 * Nat.log2 P + 4) = 4 * 2 ^ (Nat.log2 P + 1) * 2 ^ (Nat.log2 P + 1) := by
        have : 2 * Nat.log2 P + 4 = 2 + (Nat.log2 P + 1) + (Nat.log2 P + 1) := by omega
        rw [this, pow_add, pow_add]
        ring
      rw [hpow_eq, mul_assoc, mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' hP_lt hP_lt) (by decide)
    have h2K_lt : 2 ^ K < 2 ^ (2 * Nat.log2 P + 4) := hstop.trans_lt h4P2_lt
    have hK_lt : K < 2 * Nat.log2 P + 4 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2K_lt
    omega

/-- **`[MS]` Theorem 1 Three-Term Intrinsic Cost Bound for `buildQuantizedSpecPaperStop` with `BaseRadix2FFT` Leaves
(`buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le`, `[MS]` §7.2)**:
For any depth `L`, root precision `p`, and root log-length `K`, with `P = leafPrecision L p K`,
`(buildQuantizedSpecPaperStop L p K).intrinsicCostRadix2Leaf ≤
  ((2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P +
    (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ)`.
Here the three terms are literally `[MS]` Theorem 1's `C_syn+route`, `C_ovh`, and `C_base`! -/
theorem buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le (L p K : ℕ) :
    let P := leafPrecision L p K
    (buildQuantizedSpecPaperStop L p K).intrinsicCostRadix2Leaf ≤
      ((2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P +
        (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpecPaperStop, QuantizedFastDFTSpec.intrinsicCostRadix2Leaf,
      leafPrecision, sumLogLen, leafLogLen]
    rw [nat_log2_two_pow]
    have hmul_le : mulBitCost p ≤ subMulRate p := mulBitCost_le_subMulRate p p (le_refl p)
    have hadd_le : addBitCost p ≤ subMulRate p := addBitCost_le_subMulRate p p (le_refl p)
    have hop_le : mulBitCost p + addBitCost p ≤ 2 * subMulRate p := by omega
    have hK_le : K + 1 ≤ K + 4 * (Nat.log2 p + 1) := by omega
    have h1 : (K + 1) * (mulBitCost p + addBitCost p) ≤
        (K + 4 * (Nat.log2 p + 1)) * (2 * subMulRate p) :=
      Nat.mul_le_mul hK_le hop_le
    have hnat : 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p) ≤
        2 ^ K * (36 * 0 * p + 1424 * 0 * subMulRate p +
          (K + 4 * (Nat.log2 p + 1)) * (2 * subMulRate p)) := by
      calc 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p)
          = 2 ^ K * ((K + 1) * (mulBitCost p + addBitCost p)) := by ring
        _ ≤ 2 ^ K * ((K + 4 * (Nat.log2 p + 1)) * (2 * subMulRate p)) :=
            Nat.mul_le_mul_left (2 ^ K) h1
        _ = 2 ^ K * (36 * 0 * p + 1424 * 0 * subMulRate p +
              (K + 4 * (Nat.log2 p + 1)) * (2 * subMulRate p)) := by ring
    exact_mod_cast hnat
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop, leafPrecision, sumLogLen, leafLogLen]
    set P := leafPrecision L (pChild p K) (K - K / 2)
    set p' := pChild p K
    set K' := K - K / 2
    have hp'_le : p' ≤ P := le_leafPrecision L p' K'
    have hp_le : p ≤ P := by
      have hp_p' : p ≤ p' := by
        dsimp [p']
        rw [pChild_eq_additive]
        omega
      exact hp_p'.trans hp'_le
    split_ifs with hstop
    · dsimp only [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
      rw [nat_log2_two_pow]
      have h4P2 : 2 ^ K ≤ 4 * P * P :=
        hstop.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp_le) hp_le)
      have hK_bound : K + 1 ≤ leafLogLen L K' + 4 * (Nat.log2 P + 1) :=
        (log_len_add_one_le_of_two_pow_le_four_mul_sq K P h4P2).trans
          (Nat.le_add_left (4 * (Nat.log2 P + 1)) (leafLogLen L K'))
      have hmul_le : mulBitCost p ≤ subMulRate P := mulBitCost_le_subMulRate p P hp_le
      have hadd_le : addBitCost p ≤ subMulRate P := addBitCost_le_subMulRate p P hp_le
      have hop_le : mulBitCost p + addBitCost p ≤ 2 * subMulRate P := by omega
      have h1 : (K + 1) * (mulBitCost p + addBitCost p) ≤
          (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P) :=
        Nat.mul_le_mul hK_bound hop_le
      have hnat : 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p) ≤
          2 ^ K * (36 * (K + sumLogLen L K') * P + 1424 * (L + 1) * subMulRate P +
            (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) := by
        calc 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p)
            = 2 ^ K * ((K + 1) * (mulBitCost p + addBitCost p)) := by ring
          _ ≤ 2 ^ K * ((leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) :=
              Nat.mul_le_mul_left (2 ^ K) h1
          _ ≤ 2 ^ K * (36 * (K + sumLogLen L K') * P + 1424 * (L + 1) * subMulRate P +
                (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) :=
              Nat.mul_le_mul_left (2 ^ K)
                (Nat.le_add_left ((leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P))
                  (36 * (K + sumLogLen L K') * P + 1424 * (L + 1) * subMulRate P))
      exact_mod_cast hnat
    · dsimp only [quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
      have hpow_split : 2 ^ (K / 2) * 2 ^ K' = 2 ^ K := by
        dsimp [K']
        rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
      have hsyn_nat :
          syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
            2 ^ K * (4 * K * P) := by
        unfold syntheticFFTStepBitCost addBitCost
        rw [(syntheticFFTRadix2Ops_closed_form (2 ^ K') (Nat.log2 (2 ^ (K / 2)))).2.2,
            nat_log2_two_pow (K / 2), hpow_split]
        have h2K : 2 * (K / 2) ≤ K := Nat.mul_div_le K 2
        have h4p' : 4 * p' ≤ 4 * P := by omega
        calc 2 * (K / 2) * 2 ^ K * (4 * p')
            ≤ K * 2 ^ K * (4 * P) := Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ K) h2K) h4p'
          _ = 2 ^ K * (4 * K * P) := by ring
      have hovh_nat :
          kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
            2 ^ K * (32 * K * P) + 2 ^ K * (1424 * subMulRate P) := by
        have h1 := kroneckerSpreadStepBitCost_le (2 ^ (K / 2)) (2 ^ K') p' P hp'_le
        have h2 := twistAndSolverStepBitCost_le (2 ^ (K / 2)) (2 ^ K') p' P hp'_le
        have h3 := routingAndStreamingStepBitCost_le K p' P hp'_le
        rw [hpow_split] at h1 h2
        calc kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p'
            ≤ 2 ^ K * (720 * subMulRate P) + 2 ^ K * (640 * subMulRate P) +
              (2 ^ K * (32 * K * P) + 2 ^ K * (64 * subMulRate P)) :=
              Nat.add_le_add (Nat.add_le_add h1 h2) h3
          _ = 2 ^ K * (32 * K * P) + 2 ^ K * (1424 * subMulRate P) := by ring
      have hstep_nat :
          syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
            routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p' ≤
            2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) := by
        calc syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p'
            = syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
              (kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
                twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' +
                routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p') := by ring
          _ ≤ 2 ^ K * (4 * K * P) + (2 ^ K * (32 * K * P) + 2 ^ K * (1424 * subMulRate P)) :=
              Nat.add_le_add hsyn_nat hovh_nat
          _ = 2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) := by ring
      have hstep_real :
          ((syntheticFFTStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) +
            ((kroneckerSpreadStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) +
            ((twistAndSolverStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) +
            ((routingAndStreamingStepBitCost (2 ^ (K / 2)) (2 ^ K') p' : ℕ) : ℝ) ≤
            ((2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) : ℕ) : ℝ) := by
        rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
        exact_mod_cast hstep_nat
      have hchild_real :
          ((2 ^ (K / 2) : ℕ) : ℝ) * (buildQuantizedSpecPaperStop L p' K').intrinsicCostRadix2Leaf ≤
            ((2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P +
              (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) := by
        calc ((2 ^ (K / 2) : ℕ) : ℝ) * (buildQuantizedSpecPaperStop L p' K').intrinsicCostRadix2Leaf
            ≤ ((2 ^ (K / 2) : ℕ) : ℝ) *
                ((2 ^ K' * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P +
                  (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (ih p' K') (by positivity)
          _ = ((2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P +
                (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) := by
              rw [← Nat.cast_mul, ← mul_assoc, hpow_split]
      have hcomb_nat :
          (2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P)) +
            2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P +
              (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) =
          2 ^ K * (36 * (K + sumLogLen L K') * P + 1424 * (L + 1) * subMulRate P +
            (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) := by
        ring
      have hcomb_real :
          ((2 ^ K * (36 * K * P) + 2 ^ K * (1424 * subMulRate P) : ℕ) : ℝ) +
            ((2 ^ K * (36 * sumLogLen L K' * P + 1424 * L * subMulRate P +
              (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) =
          ((2 ^ K * (36 * (K + sumLogLen L K') * P + 1424 * (L + 1) * subMulRate P +
            (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) := by
        rw [← Nat.cast_add, hcomb_nat]
      linarith

/-- **Quadratic `39024 * 2^K * P^2` Upper Bound for `buildQuantizedSpecPaperStop` with `BaseRadix2FFT` Leaves
(`buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le_quad`, `[MS]` §7.2)**:
When `1 ≤ p` and `2 ^ L ≤ K ≤ 2 ^ (L + 1)`, with `P = leafPrecision L p K`,
- $C_{\text{syn+route}} \le 252 \cdot 2^K \cdot P^2$,
- $C_{\text{ovh}} \le 38448 \cdot 2^K \cdot P^2$, and
- $C_{\text{base}} \le 12 \cdot 2^K \cdot (\log_2 P + 1) \cdot \operatorname{subMulRate}(P) \le 324 \cdot 2^K \cdot P^2$,
yielding `(buildQuantizedSpecPaperStop L p K).intrinsicCostRadix2Leaf ≤ ((39024 * 2 ^ K * P * P : ℕ) : ℝ)`. -/
theorem buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le_quad
    (L p K : ℕ) (hp : 1 ≤ p) (hK_low : 2 ^ L ≤ K) (hK_high : K ≤ 2 ^ (L + 1)) :
    let P := leafPrecision L p K
    (buildQuantizedSpecPaperStop L p K).intrinsicCostRadix2Leaf ≤
      ((39024 * 2 ^ K * P * P : ℕ) : ℝ) := by
  dsimp only
  set P := leafPrecision L p K
  have hP_eq : P = p + 2 * sumLogLen L K + 12 * L := leafPrecision_eq L p K
  have h1_le_P : 1 ≤ P := by omega
  have h2L_le_P : 2 ^ L ≤ P := by
    cases L with
    | zero => dsimp [sumLogLen] at hP_eq; omega
    | succ L => dsimp [sumLogLen] at hP_eq; omega
  have hL_le_log2 : L ≤ Nat.log2 P := (Nat.le_log2 (by omega)).mpr h2L_le_P
  have hK_le_P2 : K ≤ P + 2 := by
    cases L with
    | zero => dsimp [sumLogLen] at hP_eq; omega
    | succ L => dsimp [sumLogLen] at hP_eq; omega
  have hsum_le : sumLogLen L K ≤ 7 * P := by
    have := sumLogLen_le L K
    omega
  have hsub_le : L * subMulRate P ≤ 27 * P * P :=
    subMulRate_mul_le_27_sq L P h1_le_P hL_le_log2
  have hleaf_log : leafLogLen L K + 4 * (Nat.log2 P + 1) ≤ 6 * (Nat.log2 P + 1) := by
    have hle2 := leafLogLen_le_two L K hK_high
    omega
  have hbase_le :
      (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P) ≤ 324 * P * P := by
    have hlog_sub := log2_succ_mul_subMulRate_le_27_sq P h1_le_P
    calc (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)
        ≤ (6 * (Nat.log2 P + 1)) * (2 * subMulRate P) :=
          Nat.mul_le_mul_right (2 * subMulRate P) hleaf_log
      _ = 12 * ((Nat.log2 P + 1) * subMulRate P) := by ring
      _ ≤ 12 * (27 * P * P) := Nat.mul_le_mul_left 12 hlog_sub
      _ = 324 * P * P := by ring
  have hinner :
      36 * sumLogLen L K * P + 1424 * L * subMulRate P +
        (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P) ≤
        39024 * P * P := by
    have h1 : 36 * sumLogLen L K * P ≤ 252 * P * P := by
      calc 36 * sumLogLen L K * P = 36 * (sumLogLen L K * P) := by ring
        _ ≤ 36 * ((7 * P) * P) := Nat.mul_le_mul_left 36 (Nat.mul_le_mul_right P hsum_le)
        _ = 252 * P * P := by ring
    have h2 : 1424 * L * subMulRate P ≤ 38448 * P * P := by
      calc 1424 * L * subMulRate P
          = 1424 * (L * subMulRate P) := by ring
        _ ≤ 1424 * (27 * P * P) := Nat.mul_le_mul_left 1424 hsub_le
        _ = 38448 * P * P := by ring
    calc 36 * sumLogLen L K * P + 1424 * L * subMulRate P +
          (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)
        ≤ 252 * P * P + 38448 * P * P + 324 * P * P :=
          Nat.add_le_add (Nat.add_le_add h1 h2) hbase_le
      _ = 39024 * P * P := by ring
  have htotal :
      2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P +
        (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) ≤
        39024 * 2 ^ K * P * P := by
    calc 2 ^ K * (36 * sumLogLen L K * P + 1424 * L * subMulRate P +
          (leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P))
        ≤ 2 ^ K * (39024 * P * P) := Nat.mul_le_mul_left (2 ^ K) hinner
      _ = 39024 * 2 ^ K * P * P := by ring
  exact (buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le L p K).trans (by exact_mod_cast htotal)

/-- **Leaf Cost Upper Bound for `buildQuantizedSpecPaperStop` (`buildQuantizedSpecPaperStop_radix2LeafCost_le`, `[MS]` §7.2)**:
Bounds the leaf `BaseRadix2FFT` cost term $C_{\text{base}} = \text{radix2LeafCost}$ across all leaves
halting at $2^K \le 4 p^2$ or $L = 0$. -/
theorem buildQuantizedSpecPaperStop_radix2LeafCost_le (L p K : ℕ) :
    let P := leafPrecision L p K
    (buildQuantizedSpecPaperStop L p K).radix2LeafCost ≤
      ((2 ^ K * ((leafLogLen L K + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) := by
  induction L generalizing p K with
  | zero =>
    dsimp [buildQuantizedSpecPaperStop, QuantizedFastDFTSpec.radix2LeafCost,
      leafPrecision, leafLogLen]
    rw [nat_log2_two_pow]
    have hmul_le : mulBitCost p ≤ subMulRate p := mulBitCost_le_subMulRate p p (le_refl p)
    have hadd_le : addBitCost p ≤ subMulRate p := addBitCost_le_subMulRate p p (le_refl p)
    have hop_le : mulBitCost p + addBitCost p ≤ 2 * subMulRate p := by omega
    have hK_le : K + 1 ≤ K + 4 * (Nat.log2 p + 1) := by omega
    have h1 : (K + 1) * (mulBitCost p + addBitCost p) ≤
        (K + 4 * (Nat.log2 p + 1)) * (2 * subMulRate p) :=
      Nat.mul_le_mul hK_le hop_le
    have hnat : 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p) ≤
        2 ^ K * ((K + 4 * (Nat.log2 p + 1)) * (2 * subMulRate p)) := by
      calc 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p)
          = 2 ^ K * ((K + 1) * (mulBitCost p + addBitCost p)) := by ring
        _ ≤ 2 ^ K * ((K + 4 * (Nat.log2 p + 1)) * (2 * subMulRate p)) :=
            Nat.mul_le_mul_left (2 ^ K) h1
    exact_mod_cast hnat
  | succ L ih =>
    dsimp only [buildQuantizedSpecPaperStop, leafPrecision, leafLogLen]
    set P := leafPrecision L (pChild p K) (K - K / 2)
    set p' := pChild p K
    set K' := K - K / 2
    have hp'_le : p' ≤ P := le_leafPrecision L p' K'
    have hp_le : p ≤ P := by
      have hp_p' : p ≤ p' := by
        dsimp [p']
        rw [pChild_eq_additive]
        omega
      exact hp_p'.trans hp'_le
    split_ifs with hstop
    · dsimp only [QuantizedFastDFTSpec.radix2LeafCost]
      rw [nat_log2_two_pow]
      have h4P2 : 2 ^ K ≤ 4 * P * P :=
        hstop.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp_le) hp_le)
      have hK_bound : K + 1 ≤ leafLogLen L K' + 4 * (Nat.log2 P + 1) :=
        (log_len_add_one_le_of_two_pow_le_four_mul_sq K P h4P2).trans
          (Nat.le_add_left (4 * (Nat.log2 P + 1)) (leafLogLen L K'))
      have hmul_le : mulBitCost p ≤ subMulRate P := mulBitCost_le_subMulRate p P hp_le
      have hadd_le : addBitCost p ≤ subMulRate P := addBitCost_le_subMulRate p P hp_le
      have hop_le : mulBitCost p + addBitCost p ≤ 2 * subMulRate P := by omega
      have h1 : (K + 1) * (mulBitCost p + addBitCost p) ≤
          (leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P) :=
        Nat.mul_le_mul hK_bound hop_le
      have hnat : 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p) ≤
          2 ^ K * ((leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) := by
        calc 2 ^ K * (K + 1) * (mulBitCost p + addBitCost p)
            = 2 ^ K * ((K + 1) * (mulBitCost p + addBitCost p)) := by ring
          _ ≤ 2 ^ K * ((leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) :=
              Nat.mul_le_mul_left (2 ^ K) h1
      exact_mod_cast hnat
    · dsimp only [quantizedBoxGaussianStepSpec, QuantizedFastDFTSpec.radix2LeafCost]
      have hpow_split : 2 ^ (K / 2) * 2 ^ K' = 2 ^ K := by
        dsimp [K']
        rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
      calc ((2 ^ (K / 2) : ℕ) : ℝ) * (buildQuantizedSpecPaperStop L p' K').radix2LeafCost
          ≤ ((2 ^ (K / 2) : ℕ) : ℝ) *
              ((2 ^ K' * ((leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (ih p' K') (by positivity)
        _ = ((2 ^ K * ((leafLogLen L K' + 4 * (Nat.log2 P + 1)) * (2 * subMulRate P)) : ℕ) : ℝ) := by
            rw [← Nat.cast_mul, ← mul_assoc, hpow_split]

/-- Alias for `buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le_quad`
(`buildQuantizedSpecPaperStop_paperStopTotalCost_le_quad`, `[MS]` §7.2). -/
theorem buildQuantizedSpecPaperStop_paperStopTotalCost_le_quad
    (L p K : ℕ) (hp : 1 ≤ p) (hK_low : 2 ^ L ≤ K) (hK_high : K ≤ 2 ^ (L + 1)) :
    let P := leafPrecision L p K
    (buildQuantizedSpecPaperStop L p K).intrinsicCostRadix2Leaf ≤
      ((39024 * 2 ^ K * P * P : ℕ) : ℝ) :=
  buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le_quad L p K hp hK_low hK_high

/-- Pairs `quantizedFastDFTMultiplyRadix2Leaf` with its `[MS]` Theorem 1 `intrinsicCostRadix2Leaf` +
precomputation + root pipeline cost. -/
noncomputable def quantizedFastDFTMultiplyRadix2LeafCost
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ × ℝ :=
  (quantizedFastDFTMultiplyRadix2Leaf spec b K0 k1 k2 A B,
    2 * spec.intrinsicCostRadix2Leaf + spec.precomputeRawTapCost +
      ((rootPipelineBitCost (2 ^ K0) (rootPrecision b K0) : ℕ) : ℝ))

/-- **Parameter-Free Multiplier Under the Paper's Stopping Rule and `BaseRadix2FFT` Leaves
(`quantizedMultiplyOfBitLengthPaperStop`, `[MS]` §7)**:
Executes `quantizedFastDFTMultiplyRadix2LeafCost` on `buildQuantizedSpecPaperStop L p0 K0`
(halting as soon as $2^K \le 4 p^2$ and running `BaseRadix2FFT` at every leaf). -/
noncomputable def quantizedMultiplyOfBitLengthPaperStop (n A B : ℕ) : ℕ × ℝ :=
  let b := max 1 (Nat.log2 n)
  let k := n / b + 1
  let K0 := max 4 (Nat.log2 (2 * k) + 2)
  let L := Nat.log2 (K0 - 1)
  let p0 := rootPrecision b K0
  let spec := buildQuantizedSpecPaperStop L p0 K0
  quantizedFastDFTMultiplyRadix2LeafCost spec b K0 k k A B

/-- **Unconditional Exact Multiplication Under the Paper's Stopping Rule and `BaseRadix2FFT` Leaves
(`quantizedMultiplyOfBitLengthPaperStop_fst_eq_mul`, `[MS]` §7)**:
For all `n, A, B : ℕ` with `A < 2 ^ n` and `B < 2 ^ n`,
`(quantizedMultiplyOfBitLengthPaperStop n A B).1 = A * B`. -/
theorem quantizedMultiplyOfBitLengthPaperStop_fst_eq_mul
    (n A B : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n) :
    (quantizedMultiplyOfBitLengthPaperStop n A B).1 = A * B := by
  dsimp only [quantizedMultiplyOfBitLengthPaperStop, quantizedFastDFTMultiplyRadix2LeafCost]
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set spec := buildQuantizedSpecPaperStop L p0 K0
  have hb_pos : 1 ≤ b := le_max_left 1 (Nat.log2 n)
  have hK0_ge4 : 4 ≤ K0 := le_max_left 4 (Nat.log2 (2 * k) + 2)
  have hp0 : 8 ≤ p0 := by dsimp [p0, rootPrecision]; omega
  have hvalid : spec.Valid := buildQuantizedSpecPaperStop_valid L p0 K0 hp0
  have hbase : spec.BasePow2 := buildQuantizedSpecPaperStop_basePow2 L p0 K0
  have hsize : spec.size = 2 ^ K0 := buildQuantizedSpecPaperStop_size L p0 K0
  have hp_eq : spec.p = rootPrecision b K0 := buildQuantizedSpecPaperStop_p L p0 K0
  have hk : k + k ≤ 2 ^ K0 := by
    have hlt := lt_two_pow_log2_succ (2 * k)
    have hle_exp : Nat.log2 (2 * k) + 1 ≤ K0 := by
      have : Nat.log2 (2 * k) + 2 ≤ K0 := le_max_right 4 (Nat.log2 (2 * k) + 2)
      omega
    have hpow_le : 2 ^ (Nat.log2 (2 * k) + 1) ≤ 2 ^ K0 :=
      Nat.pow_le_pow_right zero_lt_two hle_exp
    omega
  have hbk : n ≤ b * k := by
    dsimp [k]
    have hdiv := Nat.div_add_mod n b
    have hmod : n % b < b := Nat.mod_lt n (by omega)
    have hmul : b * (n / b + 1) = b * (n / b) + b := by ring
    omega
  have hpow_bk : 2 ^ n ≤ (2 ^ b) ^ k := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right zero_lt_two hbk
  exact quantizedFastDFTMultiplyRadix2Leaf_eq_mul
    spec hvalid hbase b K0 k k hsize hp_eq hk A B (hA.trans_le hpow_bk) (hB.trans_le hpow_bk)

/-- **Tight Asymptotic $O(n \log n)$ Upper Bound for `quantizedMultiplyOfBitLengthPaperStop`
(`quantizedMultiplyOfBitLengthPaperStop_snd_le_n_log_n_of_log2_ge_96`, `[MS]` Theorem 1, §7)**:
Under the paper's stopping rule $R_\ell \le 4 p_\ell^2$ paired with `BaseRadix2FFT` leaves,
the total cost (including $C_{\text{syn+route}}$, $C_{\text{ovh}}$, $C_{\text{base}}$, raw-tap
series precomputation, and root-level operations) is bounded by $O(n \log n)$. -/
theorem quantizedMultiplyOfBitLengthPaperStop_snd_le_n_log_n_of_log2_ge_96
    (n A B : ℕ) (hb96 : 96 ≤ Nat.log2 n) :
    (quantizedMultiplyOfBitLengthPaperStop n A B).2 ≤
      (7879984640 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
  dsimp only [quantizedMultiplyOfBitLengthPaperStop, quantizedFastDFTMultiplyRadix2LeafCost]
  set b := max 1 (Nat.log2 n)
  set k := n / b + 1
  set K0 := max 4 (Nat.log2 (2 * k) + 2)
  set L := Nat.log2 (K0 - 1)
  set p0 := rootPrecision b K0
  set spec := buildQuantizedSpecPaperStop L p0 K0
  set P := leafPrecision L p0 K0
  have hn : 16 ≤ n := by
    have h1 : 2 ^ 96 ≤ 2 ^ (Nat.log2 n) := Nat.pow_le_pow_right zero_lt_two hb96
    have hn_pos : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      simp at hb96
    have h2 : 2 ^ (Nat.log2 n) ≤ n := two_pow_log2_le n hn_pos
    have h3 : 16 ≤ 2 ^ 96 := by decide
    omega
  have hb_eq : b = Nat.log2 n := Nat.max_eq_right (by omega)
  have hb_ge4 : 4 ≤ b := by omega
  have h2b_le_n : 2 ^ b ≤ n := by rw [hb_eq]; exact two_pow_log2_le n (by omega)
  have hb_le_n : b ≤ n := by have := add_one_le_two_pow b; omega
  have hdiv_pos : 1 ≤ n / b := Nat.div_pos hb_le_n (by omega)
  have hk_ge2 : 2 ≤ k := by dsimp [k]; omega
  have hbk_le : b * k ≤ 2 * n := by
    have hk_le : k ≤ 2 * (n / b) := by dsimp [k]; omega
    have hmul_div : b * (n / b) ≤ n := Nat.mul_div_le n b
    calc b * k ≤ b * (2 * (n / b)) := Nat.mul_le_mul_left b hk_le
      _ = 2 * (b * (n / b)) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hmul_div
  have hk_le_n : k ≤ n := by
    dsimp [k]
    have hdiv_le : n / b ≤ n / 4 := Nat.div_le_div_left hb_ge4 (by decide)
    omega
  have hlog_2k_ge2 : 2 ≤ Nat.log2 (2 * k) := by
    refine (Nat.le_log2 (by omega)).mpr ?_
    calc 2 ^ 2 = 4 := by decide
      _ ≤ 2 * k := by omega
  have hK0_eq : K0 = Nat.log2 (2 * k) + 2 := Nat.max_eq_right (by omega)
  have hK0_ge4 : 4 ≤ K0 := by omega
  have h2K0_le : 2 ^ K0 ≤ 8 * k := by
    rw [hK0_eq, pow_add]
    have hpow_2k : 2 ^ (Nat.log2 (2 * k)) ≤ 2 * k := two_pow_log2_le (2 * k) (by omega)
    calc 2 ^ (Nat.log2 (2 * k)) * 2 ^ 2
        ≤ (2 * k) * 4 := Nat.mul_le_mul_right 4 hpow_2k
      _ = 8 * k := by ring
  have hK0_le_2b : K0 ≤ 2 * b := by
    have hn_lt : n < 2 ^ (b + 1) := by rw [hb_eq]; exact lt_two_pow_log2_succ n
    have h2k_lt : 2 * k < 2 ^ (b + 2) := by
      have hpow_b2 : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by ring
      omega
    have hlog_lt : Nat.log2 (2 * k) < b + 2 := (Nat.log2_lt (by omega)).mpr h2k_lt
    omega
  have h2L_le_K0 : 2 ^ L ≤ K0 :=
    (two_pow_log2_le (K0 - 1) (by omega)).trans (Nat.sub_le K0 1)
  have hK0_le_2L1 : K0 ≤ 2 ^ (L + 1) := by
    have h : K0 - 1 < 2 ^ (L + 1) := lt_two_pow_log2_succ (K0 - 1)
    omega
  have hL_le_K0 : L ≤ K0 := by have := add_one_le_two_pow L; omega
  have hp0_eq : p0 = 2 * b + 2 * K0 + 6 := rfl
  have hp0_pos : 1 ≤ p0 := by omega
  have hp0_le_P : p0 ≤ P := le_leafPrecision L p0 K0
  have hP_le : P ≤ 44 * b := by
    have h1 : P ≤ p0 + 4 * K0 + 14 * L := leafPrecision_le L p0 K0
    omega
  have hP_sq : P * P ≤ 2 ^ (K0 / 2) :=
    quantizedMultiplyOfBitLength_leafPrecision_sq_le_two_pow_half_K0 n hb96
  have hcost_spec : spec.intrinsicCostRadix2Leaf ≤ ((39024 * 2 ^ K0 * P * P : ℕ) : ℝ) :=
    buildQuantizedSpecPaperStop_intrinsicCostRadix2Leaf_le_quad L p0 K0 hp0_pos h2L_le_K0 hK0_le_2L1
  have hpre_spec : spec.precomputeRawTapCost ≤ ((49140 * 2 ^ K0 * P * P : ℕ) : ℝ) :=
    (buildQuantizedSpecPaperStop_precomputeRawTapCost_le L p0 K0).trans
      (buildQuantizedSpec_precomputeRawTapCost_le_quad_of_sq_le_sqrt L p0 K0 hp0_pos h2L_le_K0 hP_sq)
  have hroot_nat : rootPipelineBitCost (2 ^ K0) p0 ≤ 7 * 2 ^ K0 * P * P :=
    rootPipelineBitCost_le_quad (2 ^ K0) p0 P hp0_pos hp0_le_P
  have hroot_real : ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) ≤ ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) := by
    exact_mod_cast hroot_nat
  have hquad_nat : 127195 * 2 ^ K0 * P * P ≤ 3939992320 * n * b := by
    have h1 : 127195 * 2 ^ K0 * P * P ≤ 127195 * (8 * k) * (44 * b) * (44 * b) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left 127195 h2K0_le) hP_le)
        hP_le
    calc 127195 * 2 ^ K0 * P * P
        ≤ 127195 * (8 * k) * (44 * b) * (44 * b) := h1
      _ = 1969996160 * (b * k) * b := by ring
      _ ≤ 1969996160 * (2 * n) * b :=
          Nat.mul_le_mul_right b (Nat.mul_le_mul_left 1969996160 hbk_le)
      _ = 3939992320 * n * b := by ring
  have hquad_real :
       2 * (((39024 * 2 ^ K0 * P * P : ℕ) : ℝ)) +
        ((49140 * 2 ^ K0 * P * P : ℕ) : ℝ) +
        ((7 * 2 ^ K0 * P * P : ℕ) : ℝ) ≤
        ((3939992320 * n * b : ℕ) : ℝ) := by
    have hcomb :
        2 * (39024 * 2 ^ K0 * P * P) + 49140 * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P =
          127195 * 2 ^ K0 * P * P := by ring
    have hle :
        2 * (39024 * 2 ^ K0 * P * P) + 49140 * 2 ^ K0 * P * P + 7 * 2 ^ K0 * P * P ≤
          3939992320 * n * b := by
      rw [hcomb]
      exact hquad_nat
    exact_mod_cast hle
  have htotal_le :
      2 * spec.intrinsicCostRadix2Leaf + spec.precomputeRawTapCost +
        ((rootPipelineBitCost (2 ^ K0) p0 : ℕ) : ℝ) ≤
        (3939992320 : ℝ) * (n : ℝ) * (b : ℝ) := by
    have hcast : ((3939992320 * n * b : ℕ) : ℝ) = (3939992320 : ℝ) * (n : ℝ) * (b : ℝ) := by
      push_cast
      ring
    linarith
  have hb_real : (b : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    rw [hb_eq]
    exact nat_log2_real_le_two_mul_log n (by omega)
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_nonneg : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  nlinarith

/-- **Headline Correctness and $O(n \log n)$ Complexity Theorem for `quantizedMultiplyOfBitLengthPaperStop`
(`quantizedMultiplyOfBitLengthPaperStop_correct_and_isBigO`, `[MS]` Theorem 1, §7)**:
Under the paper's stopping rule $R_\ell \le 4 p_\ell^2$ paired with `BaseRadix2FFT` leaves:
1. For all `n, A, B : ℕ` with `A < 2 ^ n` and `B < 2 ^ n`, `(quantizedMultiplyOfBitLengthPaperStop n A B).1 = A * B`,
2. For all `n, A, B : ℕ` with `96 ≤ Nat.log2 n`, `(quantizedMultiplyOfBitLengthPaperStop n A B).2 ≤ (7879984640 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))`, and
3. For any operand sequences `A, B : ℕ → ℕ`, `(fun n : ℕ => (quantizedMultiplyOfBitLengthPaperStop n (A n) (B n)).2) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))`. -/
theorem quantizedMultiplyOfBitLengthPaperStop_correct_and_isBigO :
    (∀ n A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      (quantizedMultiplyOfBitLengthPaperStop n A B).1 = A * B) ∧
    (∀ n A B : ℕ, 96 ≤ Nat.log2 n →
      (quantizedMultiplyOfBitLengthPaperStop n A B).2 ≤
        (7879984640 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) ∧
    (∀ A B : ℕ → ℕ,
      (fun n : ℕ => (quantizedMultiplyOfBitLengthPaperStop n (A n) (B n)).2) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))) := by
  refine ⟨quantizedMultiplyOfBitLengthPaperStop_fst_eq_mul,
    quantizedMultiplyOfBitLengthPaperStop_snd_le_n_log_n_of_log2_ge_96, fun A B => ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨(7879984640 : ℝ), Filter.eventually_atTop.mpr ⟨2 ^ 96, fun n hn => ?_⟩⟩
  have hb96 : 96 ≤ Nat.log2 n := (Nat.le_log2 (by positivity)).mpr hn
  have hle := quantizedMultiplyOfBitLengthPaperStop_snd_le_n_log_n_of_log2_ge_96 n (A n) (B n) hb96
  have hnonneg : 0 ≤ (quantizedMultiplyOfBitLengthPaperStop n (A n) (B n)).2 := by
    dsimp only [quantizedMultiplyOfBitLengthPaperStop, quantizedFastDFTMultiplyRadix2LeafCost]
    have h1 := QuantizedFastDFTSpec.intrinsicCostRadix2Leaf_nonneg
      (buildQuantizedSpecPaperStop (Nat.log2 (max 4 (Nat.log2 (2 * (n / max 1 (Nat.log2 n) + 1)) + 2) - 1))
        (rootPrecision (max 1 (Nat.log2 n)) (max 4 (Nat.log2 (2 * (n / max 1 (Nat.log2 n) + 1)) + 2)))
        (max 4 (Nat.log2 (2 * (n / max 1 (Nat.log2 n) + 1)) + 2)))
    have h2 := precomputeRawTapCost_nonneg
      (buildQuantizedSpecPaperStop (Nat.log2 (max 4 (Nat.log2 (2 * (n / max 1 (Nat.log2 n) + 1)) + 2) - 1))
        (rootPrecision (max 1 (Nat.log2 n)) (max 4 (Nat.log2 (2 * (n / max 1 (Nat.log2 n) + 1)) + 2)))
        (max 4 (Nat.log2 (2 * (n / max 1 (Nat.log2 n) + 1)) + 2)))
    positivity
  have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by
    have : 2 ≤ n := by
      calc 2 ≤ 2 ^ 96 := by decide
        _ ≤ n := hn
    exact_mod_cast this
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hrhs_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg (by positivity) hlog_nonneg
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hrhs_nonneg]
  exact hle

end IntMul
