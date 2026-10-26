import IntMul.Defs

/-!
# Schedule Properties & Additive Precision Recurrence (`IntMul.Schedule`)

This module proves the structural identities and bounds for the data-independent
parameter schedule `cSpec(n)` and the multi-level recursion parameters `(levelK, levelR, levelP)`
defined in `IntMul.Defs` (Section 3.5 (`sec:prelim-dft`), Section 6.3 (`sec:forward-error`),
Section 7.1 (`sec:alg-spec`), Section 7.2 (`sec:cost-proof`)):
1. Dimension and divisibility identities (`k1Ell_add_k2Ell`, `t1Ell_mul_rEll`, `t1Ell_dvd_rEll`,
   `c1Ell_eq_one_or_two`, `t1Ell_mul_c1Ell`).
2. Root schedule inequalities (`chunkBits_ge_four`, `n_le_numChunks_mul_chunkBits`,
   `rootK0_ge_two`, `two_mul_numChunks_le_rootR0`, `cSpec_fields`).
3. Multi-level recursion invariants:
   - Purely additive precision step `pChildEll_eq : pChildEll K p = p + 2 * K + 12`
     (schedule (34) (`eq:cert-sched`)).
   - Exact halving identity `levelK_sub_one_eq : levelK K0 ell - 1 = (K0 - 1) / 2 ^ ell`.
   - Cumulative log-length bound `sum_levelK_le : ∑ j ∈ Finset.range ell, levelK K0 j ≤ 2 * K0 + ell`.
   - Uniform additive precision bound `levelP_le : levelP K0 p0 ell ≤ p0 + 4 * K0 + 16 * ell`.
   - Geometric contraction identity `geom_sum_two_zpow_neg` and bound `geom_sum_two_zpow_neg_lt_two`.
   - Well-founded termination depth `recursionDepth K0 p0 ≤ K0` and `isBaseLeaf_recursionDepth`.
-/

namespace IntMul

/-! ## 1. Dimension & Divisibility Identities (Section 3.5 (`sec:prelim-dft`), Section 7.1 (`sec:alg-spec`)) -/

/-- Exact exponent partition $\lfloor K/2 \rfloor + \lceil K/2 \rceil = K$ (Section 3.5 (`sec:prelim-dft`), Section 7.1 (`sec:alg-spec`)). -/
@[simp]
theorem k1Ell_add_k2Ell (K : ℕ) : k1Ell K + k2Ell K = K := by
  unfold k1Ell k2Ell
  omega

/-- First-axis log-dimension is at most second-axis log-dimension: $\lfloor K/2 \rfloor \le \lceil K/2 \rceil$. -/
theorem k1Ell_le_k2Ell (K : ℕ) : k1Ell K ≤ k2Ell K := by
  unfold k1Ell k2Ell
  omega

/-- Second-axis log-dimension exceeds first-axis log-dimension by at most $1$. -/
theorem k2Ell_le_k1Ell_add_one (K : ℕ) : k2Ell K ≤ k1Ell K + 1 := by
  unfold k1Ell k2Ell
  omega

/-- Dichotomy $\lceil K/2 \rceil = \lfloor K/2 \rfloor$ or $\lceil K/2 \rceil = \lfloor K/2 \rfloor + 1$. -/
theorem k2Ell_eq_k1Ell_or_add_one (K : ℕ) :
    k2Ell K = k1Ell K ∨ k2Ell K = k1Ell K + 1 := by
  unfold k1Ell k2Ell
  omega

/-- Exact 2D factorization $t_{1,\ell} \cdot r_\ell = 2^{K_\ell}$ (Section 3.5 (`sec:prelim-dft`), Section 7.1 (`sec:alg-spec`)). -/
@[simp]
theorem t1Ell_mul_rEll (K : ℕ) : t1Ell K * rEll K = 2 ^ K := by
  unfold t1Ell rEll
  rw [← pow_add, k1Ell_add_k2Ell]

/-- Positivity of $t_{1,\ell} = 2^{\lfloor K/2 \rfloor} > 0$. -/
theorem t1Ell_pos (K : ℕ) : 0 < t1Ell K := by
  unfold t1Ell
  positivity

/-- Positivity of $r_\ell = 2^{\lceil K/2 \rceil} > 0$. -/
theorem rEll_pos (K : ℕ) : 0 < rEll K := by
  unfold rEll
  positivity

/-- First-axis dimension divides second-axis dimension: $t_{1,\ell} \mid r_\ell$ (Section 3.5 (`sec:prelim-dft`)). -/
theorem t1Ell_dvd_rEll (K : ℕ) : t1Ell K ∣ rEll K := by
  unfold t1Ell rEll
  exact Nat.pow_dvd_pow 2 (k1Ell_le_k2Ell K)

/-- Inequality $t_{1,\ell} \le r_\ell$. -/
theorem t1Ell_le_rEll (K : ℕ) : t1Ell K ≤ rEll K :=
  Nat.le_of_dvd (rEll_pos K) (t1Ell_dvd_rEll K)

/-- Explicit power-of-two formula for $c_{1,\ell} = r_\ell / t_{1,\ell} = 2^{k_{2,\ell} - k_{1,\ell}}$. -/
theorem c1Ell_eq_two_pow (K : ℕ) : c1Ell K = 2 ^ (k2Ell K - k1Ell K) := by
  unfold c1Ell rEll t1Ell
  exact Nat.pow_div (k1Ell_le_k2Ell K) (by norm_num)

/-- The step ratio $c_{1,\ell} = r_\ell / t_{1,\ell}$ is always $1$ or $2$ (Section 3.5 (`sec:prelim-dft`)). -/
theorem c1Ell_eq_one_or_two (K : ℕ) : c1Ell K = 1 ∨ c1Ell K = 2 := by
  rw [c1Ell_eq_two_pow]
  rcases k2Ell_eq_k1Ell_or_add_one K with h | h
  · left
    rw [h, Nat.sub_self, pow_zero]
  · right
    rw [h, Nat.add_sub_cancel_left, pow_one]

/-- Exact quotient relation $t_{1,\ell} \cdot c_{1,\ell} = r_\ell$ (Section 3.5 (`sec:prelim-dft`)). -/
@[simp]
theorem t1Ell_mul_c1Ell (K : ℕ) : t1Ell K * c1Ell K = rEll K := by
  unfold c1Ell
  exact Nat.mul_div_cancel' (t1Ell_dvd_rEll K)

/-- Positivity of $c_{1,\ell}$. -/
theorem c1Ell_pos (K : ℕ) : 0 < c1Ell K := by
  rcases c1Ell_eq_one_or_two K with h | h <;> omega

/-- Upper bound $c_{1,\ell} \le 2$. -/
theorem c1Ell_le_two (K : ℕ) : c1Ell K ≤ 2 := by
  rcases c1Ell_eq_one_or_two K with h | h <;> omega

/-- Upper bound $r_\ell \le 2 t_{1,\ell}$. -/
theorem rEll_le_two_mul_t1Ell (K : ℕ) : rEll K ≤ 2 * t1Ell K := by
  rw [← t1Ell_mul_c1Ell K, mul_comm]
  exact Nat.mul_le_mul_right (t1Ell K) (c1Ell_le_two K)

/-! ## 2. Root Schedule Properties (`cSpec`, Section 7.1 (`sec:alg-spec`)) -/

/-- Root chunk bit-width satisfies $b \ge 4$ for all $n$ (Section 7.1 (`sec:alg-spec`)). -/
theorem chunkBits_ge_four (n : ℕ) : 4 ≤ chunkBits n := by
  unfold chunkBits
  exact le_max_left 4 (Nat.log 2 n)

/-- Positivity of root chunk bit-width $b > 0$. -/
theorem chunkBits_pos (n : ℕ) : 0 < chunkBits n := by
  have := chunkBits_ge_four n
  omega

/-- $N = \lceil n / b \rceil$ chunks of $b$ bits cover all $n$ input bits: $n \le N \cdot b$ (Section 7.1 (`sec:alg-spec`)). -/
theorem n_le_numChunks_mul_chunkBits (n : ℕ) : n ≤ numChunks n * chunkBits n := by
  unfold numChunks
  have hb : 0 < chunkBits n := chunkBits_pos n
  have hdiv := Nat.div_add_mod (n + chunkBits n - 1) (chunkBits n)
  have hmod := Nat.mod_lt (n + chunkBits n - 1) hb
  rw [mul_comm] at hdiv
  omega

/-- Root log-length satisfies $K_0 \ge 2$ for all $n$ (Section 7.1 (`sec:alg-spec`)). -/
theorem rootK0_ge_two (n : ℕ) : 2 ≤ rootK0 n := by
  unfold rootK0
  exact le_max_left 2 _

/-- Root transform length satisfies $R_0 = 2^{K_0} \ge 4$ for all $n$. -/
theorem rootR0_ge_four (n : ℕ) : 4 ≤ rootR0 n := by
  unfold rootR0
  calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ rootK0 n := Nat.pow_le_pow_right (by norm_num) (rootK0_ge_two n)

/-- Zero-oversampling linear convolution guard $2 N \le R_0$ (Section 7.1 (`sec:alg-spec`)). -/
theorem two_mul_numChunks_le_rootR0 (n : ℕ) : 2 * numChunks n ≤ rootR0 n := by
  unfold rootR0 rootK0
  have h1 : 2 * numChunks n ≤ 2 * max 1 (numChunks n) := by
    have : numChunks n ≤ max 1 (numChunks n) := le_max_right 1 (numChunks n)
    omega
  have h2 : 2 * max 1 (numChunks n) ≤ 2 ^ Nat.clog 2 (2 * max 1 (numChunks n)) :=
    Nat.le_pow_clog (by norm_num) (2 * max 1 (numChunks n))
  have h3 : 2 ^ Nat.clog 2 (2 * max 1 (numChunks n)) ≤
      2 ^ max 2 (Nat.clog 2 (2 * max 1 (numChunks n))) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right 2 _)
  exact le_trans h1 (le_trans h2 h3)

/-- Root precision satisfies $p_0 \ge 18$ (and in particular $p_0 \ge 8$) for all $n$ (Section 7.1 (`sec:alg-spec`)). -/
theorem rootP0_ge_eighteen (n : ℕ) : 18 ≤ rootP0 n := by
  unfold rootP0
  have hb := chunkBits_ge_four n
  have hk := rootK0_ge_two n
  omega

/-- Root precision satisfies $p_0 \ge 8$ for all $n$ (Section 6.3 (`sec:forward-error`), Section 7.1 (`sec:alg-spec`)). -/
theorem rootP0_ge_eight (n : ℕ) : 8 ≤ rootP0 n := by
  have := rootP0_ge_eighteen n
  omega

@[simp] theorem cSpec_n (n : ℕ) : (cSpec n).n = n := rfl
@[simp] theorem cSpec_b (n : ℕ) : (cSpec n).b = chunkBits n := rfl
@[simp] theorem cSpec_N (n : ℕ) : (cSpec n).N = numChunks n := rfl
@[simp] theorem cSpec_K0 (n : ℕ) : (cSpec n).K0 = rootK0 n := rfl
@[simp] theorem cSpec_R0 (n : ℕ) : (cSpec n).R0 = rootR0 n := rfl
@[simp] theorem cSpec_p0 (n : ℕ) : (cSpec n).p0 = rootP0 n := rfl

/-- Bundled field equations for the canonical schedule `cSpec n` (Section 7.1 (`sec:alg-spec`)). -/
theorem cSpec_fields (n : ℕ) :
    (cSpec n).n = n ∧
    (cSpec n).b = chunkBits n ∧
    (cSpec n).N = numChunks n ∧
    (cSpec n).K0 = rootK0 n ∧
    (cSpec n).R0 = rootR0 n ∧
    (cSpec n).p0 = rootP0 n :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Multi-Level Recursion Invariants (Section 6.3 (`sec:forward-error`), Section 7.2 (`sec:cost-proof`)) -/

/-- Purely additive child precision recurrence $p_{\ell+1} = p_\ell + 2 K_\ell + 12$ (Lemma 6.5 (`lem:forward`), schedule (34) (`eq:cert-sched`)). -/
@[simp]
theorem pChildEll_eq (K p : ℕ) : pChildEll K p = p + 2 * K + 12 := by
  unfold pChildEll pWorkEll
  omega

/-- Child fixed-point quantization precision $q_{\text{child},\ell} = p_\ell + 2 K_\ell + 14$ (Lemma 6.5 (`lem:forward`), schedule (34) (`eq:cert-sched`)). -/
@[simp]
theorem qChildEll_eq (K p : ℕ) : qChildEll K p = p + 2 * K + 14 := by
  unfold qChildEll pChildEll pWorkEll
  omega

@[simp]
theorem levelK_zero (K0 : ℕ) : levelK K0 0 = K0 := rfl

@[simp]
theorem levelK_succ (K0 ell : ℕ) : levelK K0 (ell + 1) = k2Ell (levelK K0 ell) := rfl

/-- Each recursion step does not increase the log-length: $K_{\ell+1} \le K_\ell$. -/
theorem levelK_succ_le (K0 ell : ℕ) : levelK K0 (ell + 1) ≤ levelK K0 ell := by
  simp only [levelK_succ, k2Ell]
  omega

/-- Log-length at any depth $\ell$ is bounded by $K_0$. -/
theorem levelK_le_K0 (K0 ell : ℕ) : levelK K0 ell ≤ K0 := by
  induction ell with
  | zero => simp
  | succ ell ih => exact le_trans (levelK_succ_le K0 ell) ih

/-- When $K_\ell \ge 2$, the next recursion level has strictly smaller log-length $K_{\ell+1} < K_\ell$. -/
theorem levelK_StrictMono_of_ge_two (K0 ell : ℕ) (h : 2 ≤ levelK K0 ell) :
    levelK K0 (ell + 1) < levelK K0 ell := by
  simp only [levelK_succ, k2Ell]
  omega

/-- Exact halving identity for shifted log-length: $K_\ell - 1 = \lfloor (K_0 - 1) / 2^\ell \rfloor$. -/
theorem levelK_sub_one_eq (K0 ell : ℕ) : levelK K0 ell - 1 = (K0 - 1) / 2 ^ ell := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    have hstep : levelK K0 (ell + 1) - 1 = (levelK K0 ell - 1) / 2 := by
      simp only [levelK_succ, k2Ell]
      omega
    rw [hstep, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- Geometric decay upper bound $K_\ell \le (K_0 - 1) / 2^\ell + 1$. -/
theorem levelK_le_div_two_pow_add_one (K0 ell : ℕ) :
    levelK K0 ell ≤ (K0 - 1) / 2 ^ ell + 1 := by
  have := levelK_sub_one_eq K0 ell
  omega

/-- Geometric decay upper bound $K_\ell \le K_0 / 2^\ell + 2$ (Section 7.2 (`sec:cost-proof`)). -/
theorem levelK_le_div_two_pow_add_two (K0 ell : ℕ) :
    levelK K0 ell ≤ K0 / 2 ^ ell + 2 := by
  have h1 := levelK_le_div_two_pow_add_one K0 ell
  have h2 : (K0 - 1) / 2 ^ ell ≤ K0 / 2 ^ ell :=
    Nat.div_le_div_right (Nat.sub_le K0 1)
  omega

/-- Telescoping invariant for the cumulative sum of log-lengths:
$\bigl(\sum_{j < \ell} K_j\bigr) + 2 K_\ell \le 2 K_0 + \ell$. -/
theorem sum_levelK_add_two_mul_levelK_le (K0 ell : ℕ) :
    (∑ j ∈ Finset.range ell, levelK K0 j) + 2 * levelK K0 ell ≤ 2 * K0 + ell := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    rw [Finset.sum_range_succ]
    have hstep : levelK K0 ell + 2 * levelK K0 (ell + 1) ≤ 2 * levelK K0 ell + 1 := by
      simp only [levelK_succ, k2Ell]
      omega
    omega

/-- Cumulative log-length bound $\sum_{j < \ell} K_j \le 2 K_0 + \ell$ (Section 7.2 (`sec:cost-proof`)). -/
theorem sum_levelK_le (K0 ell : ℕ) :
    ∑ j ∈ Finset.range ell, levelK K0 j ≤ 2 * K0 + ell := by
  have := sum_levelK_add_two_mul_levelK_le K0 ell
  omega

/-- Cumulative log-length bound $\sum_{j < \ell} K_j \le 2 K_0 + 2 \ell$ (Section 6.3 (`sec:forward-error`), Section 7.2 (`sec:cost-proof`)). -/
theorem sum_levelK_le_two_K0_add_two_ell (K0 ell : ℕ) :
    ∑ j ∈ Finset.range ell, levelK K0 j ≤ 2 * K0 + 2 * ell := by
  have := sum_levelK_le K0 ell
  omega

@[simp]
theorem levelP_zero (K0 p0 : ℕ) : levelP K0 p0 0 = p0 := rfl

@[simp]
theorem levelP_succ (K0 p0 ell : ℕ) :
    levelP K0 p0 (ell + 1) = levelP K0 p0 ell + 2 * levelK K0 ell + 12 := by
  simp [levelP, pChildEll_eq]

/-- Closed-form expression for `levelP` in terms of the cumulative sum of `levelK`. -/
theorem levelP_eq_sum (K0 p0 ell : ℕ) :
    levelP K0 p0 ell = p0 + 2 * (∑ j ∈ Finset.range ell, levelK K0 j) + 12 * ell := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    rw [levelP_succ, ih, Finset.sum_range_succ]
    ring

/-- Precision `levelP` is non-decreasing with depth: $p_0 \le p_\ell$. -/
theorem levelP_ge_p0 (K0 p0 ell : ℕ) : p0 ≤ levelP K0 p0 ell := by
  rw [levelP_eq_sum]
  omega

/-- **Additive Precision Bound (Section 6.3 (`sec:forward-error`), Section 7.2 (`sec:cost-proof`))**:
Across all recursion levels $\ell$, $p_\ell \le p_0 + 4 K_0 + 16 \ell$. -/
theorem levelP_le (K0 p0 ell : ℕ) :
    levelP K0 p0 ell ≤ p0 + 4 * K0 + 16 * ell := by
  rw [levelP_eq_sum]
  have := sum_levelK_le K0 ell
  omega

/-! ## 4. Geometric Contraction across Levels (Section 6.3 (`sec:forward-error`), Section 7.2 (`sec:cost-proof`)) -/

/-- Closed-form geometric sum $\sum_{\ell=0}^{L-1} 2^{-\ell} = 2 - 2^{-(L - 1)}$ (Section 6.3 (`sec:forward-error`), Section 7.2 (`sec:cost-proof`)). -/
theorem geom_sum_two_zpow_neg (L : ℕ) :
    (∑ ell ∈ Finset.range L, (2 : ℝ) ^ (-(ell : ℤ))) = 2 - (2 : ℝ) ^ (-((L : ℤ) - 1)) := by
  induction L with
  | zero =>
    simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have hexp : -((L : ℤ) - 1) = -(L : ℤ) + 1 := by ring
    have hpow : (2 : ℝ) ^ (-((L : ℤ) - 1)) = 2 * (2 : ℝ) ^ (-(L : ℤ)) := by
      rw [hexp, zpow_add₀ (by norm_num), zpow_one, mul_comm]
    have hcast : -(((L + 1 : ℕ) : ℤ) - 1) = -(L : ℤ) := by push_cast; ring
    rw [hpow, hcast]
    ring

/-- The per-level geometric contraction factor $\sum_{\ell=0}^{L-1} 2^{-\ell}$ is strictly bounded by $2$ (Section 7.2 (`sec:cost-proof`)). -/
theorem geom_sum_two_zpow_neg_lt_two (L : ℕ) :
    (∑ ell ∈ Finset.range L, (2 : ℝ) ^ (-(ell : ℤ))) < 2 := by
  rw [geom_sum_two_zpow_neg]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((L : ℤ) - 1)) := zpow_pos (by norm_num) _
  linarith

/-! ## 5. Recursion Depth Termination (`recursionDepth`, Section 7.1 (`sec:alg-spec`), Section 7.2 (`sec:cost-proof`)) -/

/-- By depth $\ell = K_0$, the log-length reaches $K_{K_0} \le 1$. -/
theorem levelK_self_le_one (K0 : ℕ) : levelK K0 K0 ≤ 1 := by
  have hlt : K0 - 1 < 2 ^ K0 :=
    lt_of_le_of_lt (Nat.sub_le K0 1) (Nat.lt_two_pow_self)
  have hdiv : (K0 - 1) / 2 ^ K0 = 0 := Nat.div_eq_of_lt hlt
  have hsub := levelK_sub_one_eq K0 K0
  omega

/-- Whenever $p_0 \ge 1$, the base-case stopping condition `isBaseLeaf` holds by depth $\ell = K_0$. -/
theorem isBaseLeaf_at_K0 (K0 p0 : ℕ) (hp0 : 1 ≤ p0) :
    isBaseLeaf (levelK K0 K0) (levelP K0 p0 K0) = true := by
  unfold isBaseLeaf
  rw [decide_eq_true_eq]
  have hk : levelK K0 K0 ≤ 1 := levelK_self_le_one K0
  have hpow : 2 ^ levelK K0 K0 ≤ 2 := by
    calc
      2 ^ levelK K0 K0 ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 2 := by norm_num
  have hp : 1 ≤ levelP K0 p0 K0 := le_trans hp0 (levelP_ge_p0 K0 p0 K0)
  have hp2 : 4 ≤ 4 * levelP K0 p0 K0 * levelP K0 p0 K0 := by nlinarith
  omega

/-- Auxiliary bounded search for the first recursion level in `[cur, cur + fuel]` satisfying `isBaseLeaf`. -/
def recursionDepthAux (K0 p0 : ℕ) : ℕ → ℕ → ℕ
  | 0, cur => cur
  | fuel + 1, cur =>
    if isBaseLeaf (levelK K0 cur) (levelP K0 p0 cur) then cur
    else recursionDepthAux K0 p0 fuel (cur + 1)

theorem recursionDepthAux_bounds (K0 p0 fuel cur : ℕ) :
    cur ≤ recursionDepthAux K0 p0 fuel cur ∧ recursionDepthAux K0 p0 fuel cur ≤ cur + fuel := by
  induction fuel generalizing cur with
  | zero =>
    simp [recursionDepthAux]
  | succ fuel ih =>
    simp only [recursionDepthAux]
    split_ifs
    · omega
    · have := ih (cur + 1)
      omega

theorem isBaseLeaf_recursionDepthAux (K0 p0 fuel cur : ℕ)
    (hend : isBaseLeaf (levelK K0 (cur + fuel)) (levelP K0 p0 (cur + fuel)) = true) :
    isBaseLeaf (levelK K0 (recursionDepthAux K0 p0 fuel cur))
      (levelP K0 p0 (recursionDepthAux K0 p0 fuel cur)) = true := by
  induction fuel generalizing cur with
  | zero =>
    simpa [recursionDepthAux] using hend
  | succ fuel ih =>
    simp only [recursionDepthAux]
    split_ifs with h
    · exact h
    · apply ih (cur + 1)
      have heq : cur + 1 + fuel = cur + (fuel + 1) := by omega
      rwa [heq]

theorem not_isBaseLeaf_of_lt_recursionDepthAux (K0 p0 fuel cur ell : ℕ)
    (hcur : cur ≤ ell) (hlt : ell < recursionDepthAux K0 p0 fuel cur) :
    isBaseLeaf (levelK K0 ell) (levelP K0 p0 ell) = false := by
  induction fuel generalizing cur with
  | zero =>
    simp [recursionDepthAux] at hlt
    omega
  | succ fuel ih =>
    simp only [recursionDepthAux] at hlt
    split_ifs at hlt with h
    · omega
    · rcases eq_or_lt_of_le hcur with rfl | hgt
      · exact Bool.eq_false_iff.mpr h
      · exact ih (cur + 1) hgt hlt

/-- The recursion depth $L \le K_0$: the smallest $\ell \le K_0$ where
`isBaseLeaf (levelK K0 ell) (levelP K0 p0 ell) = true` (Section 6.3 (`sec:forward-error`), Section 7.1 (`sec:alg-spec`)). -/
def recursionDepth (K0 p0 : ℕ) : ℕ :=
  recursionDepthAux K0 p0 K0 0

/-- The recursion depth never exceeds $K_0$. -/
theorem recursionDepth_le_K0 (K0 p0 : ℕ) : recursionDepth K0 p0 ≤ K0 := by
  have := (recursionDepthAux_bounds K0 p0 K0 0).2
  simpa [recursionDepth] using this

/-- Whenever $p_0 \ge 1$, `isBaseLeaf` holds at `recursionDepth K0 p0`. -/
theorem isBaseLeaf_recursionDepth (K0 p0 : ℕ) (hp0 : 1 ≤ p0) :
    isBaseLeaf (levelK K0 (recursionDepth K0 p0)) (levelP K0 p0 (recursionDepth K0 p0)) = true := by
  unfold recursionDepth
  apply isBaseLeaf_recursionDepthAux
  simpa using isBaseLeaf_at_K0 K0 p0 hp0

/-- For every level $\ell < \text{recursionDepth } K_0 \, p_0$, `isBaseLeaf` is false ($R_\ell > 4 p_\ell^2$). -/
theorem not_isBaseLeaf_of_lt_recursionDepth (K0 p0 ell : ℕ) (hlt : ell < recursionDepth K0 p0) :
    isBaseLeaf (levelK K0 ell) (levelP K0 p0 ell) = false :=
  not_isBaseLeaf_of_lt_recursionDepthAux K0 p0 K0 0 ell (Nat.zero_le ell) hlt

/-- Explicit non-base-leaf inequality $4 p_\ell^2 < 2^{K_\ell}$ for all $\ell < \text{recursionDepth } K_0 \, p_0$ (Lemma 6.5 (`lem:forward`)). -/
theorem four_mul_sq_lt_levelR_of_lt_recursionDepth (K0 p0 ell : ℕ)
    (hlt : ell < recursionDepth K0 p0) :
    4 * levelP K0 p0 ell * levelP K0 p0 ell < levelR K0 ell := by
  have hfalse := not_isBaseLeaf_of_lt_recursionDepth K0 p0 ell hlt
  unfold isBaseLeaf at hfalse
  rw [decide_eq_false_iff_not, not_le] at hfalse
  exact hfalse

/-- Upper bound `chunkBits n ≤ n + 4`. -/
theorem chunkBits_le_add_four (n : ℕ) : chunkBits n ≤ n + 4 := by
  unfold chunkBits
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  omega

/-- Upper bound `numChunks n ≤ n`. -/
theorem numChunks_le_self (n : ℕ) : numChunks n ≤ n := by
  unfold numChunks
  have hb : 4 ≤ chunkBits n := chunkBits_ge_four n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h4 : chunkBits 0 = 4 := by rfl
    rw [h4]
  · have h1 : n ≤ n * chunkBits n := Nat.le_mul_of_pos_right n (by omega)
    have h2 : (n + 1) * chunkBits n = n * chunkBits n + chunkBits n :=
      Nat.succ_mul n (chunkBits n)
    have hlt : n + chunkBits n - 1 < (n + 1) * chunkBits n := by omega
    have hdiv : (n + chunkBits n - 1) / chunkBits n < n + 1 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr hlt
    omega

/-- Upper bound `rootK0 n ≤ n + 2`. -/
theorem rootK0_le_add_two (n : ℕ) : rootK0 n ≤ n + 2 := by
  unfold rootK0
  have hN : numChunks n ≤ n := numChunks_le_self n
  have hmax : max 1 (numChunks n) ≤ n + 1 := by omega
  have h1 : n + 1 ≤ 2 ^ (n + 1) := le_of_lt Nat.lt_two_pow_self
  have h2 : 2 * max 1 (numChunks n) ≤ 2 ^ (n + 2) := by
    calc
      2 * max 1 (numChunks n) ≤ 2 * (n + 1) := by omega
      _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 h1
      _ = 2 ^ (n + 2) := by rw [← pow_succ']
  have hclog : Nat.clog 2 (2 * max 1 (numChunks n)) ≤ n + 2 := by
    calc
      Nat.clog 2 (2 * max 1 (numChunks n)) ≤ Nat.clog 2 (2 ^ (n + 2)) :=
        Nat.clog_mono_right 2 h2
      _ = n + 2 := Nat.clog_pow 2 (n + 2) (by norm_num)
  omega

/-- For any $m \ge 1$, $2^{\lceil \log_2 m \rceil} \le 2 m$. -/
theorem two_pow_clog_le_two_mul {m : ℕ} (hm : 1 ≤ m) :
    2 ^ Nat.clog 2 m ≤ 2 * m := by
  rcases eq_or_lt_of_le hm with rfl | hgt
  · simp
  · set k := Nat.clog 2 m
    have hk_pos : 0 < k := Nat.clog_pos (by norm_num) hgt
    have hnot : ¬ m ≤ 2 ^ (k - 1) := by
      intro hle
      have hck : k ≤ k - 1 := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hle
      omega
    have hlt : 2 ^ (k - 1) < m := Nat.lt_of_not_ge hnot
    have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
    rw [hk_eq, pow_succ']
    omega

/-- Upper bound `rootR0 n ≤ 4 * max 1 (numChunks n)` (Section 7.1 (`sec:alg-spec`)). -/
theorem rootR0_le_four_mul_max_numChunks (n : ℕ) :
    rootR0 n ≤ 4 * max 1 (numChunks n) := by
  unfold rootR0 rootK0
  set m := 2 * max 1 (numChunks n)
  have hm_ge_two : 2 ≤ m := by
    have : 1 ≤ max 1 (numChunks n) := le_max_left 1 (numChunks n)
    omega
  rcases le_total 2 (Nat.clog 2 m) with hle | hle
  · rw [max_eq_right hle]
    calc
      2 ^ Nat.clog 2 m ≤ 2 * m := two_pow_clog_le_two_mul (by omega)
      _ = 4 * max 1 (numChunks n) := by ring
  · rw [max_eq_left hle]
    have : 1 ≤ max 1 (numChunks n) := le_max_left 1 (numChunks n)
    omega

/-- Product bound `max 1 (numChunks n) * chunkBits n ≤ n + chunkBits n` (Section 7.1 (`sec:alg-spec`)). -/
theorem max_numChunks_mul_chunkBits_le (n : ℕ) :
    max 1 (numChunks n) * chunkBits n ≤ n + chunkBits n := by
  rcases le_total 1 (numChunks n) with hle | hle
  · rw [max_eq_right hle]
    unfold numChunks
    have hmul : ((n + chunkBits n - 1) / chunkBits n) * chunkBits n ≤ n + chunkBits n - 1 :=
      Nat.div_mul_le_self (n + chunkBits n - 1) (chunkBits n)
    omega
  · rw [max_eq_left hle]
    omega

/-- For $n \ge 1$, `chunkBits n ≤ 5 * n`. -/
theorem chunkBits_le_five_mul {n : ℕ} (hn : 1 ≤ n) : chunkBits n ≤ 5 * n := by
  unfold chunkBits
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  omega

/-- For $n \ge 1$, `rootR0 n * chunkBits n ≤ 24 * n` (Section 7.1 (`sec:alg-spec`), Section 7.2 (`sec:cost-proof`)). -/
theorem rootR0_mul_chunkBits_le {n : ℕ} (hn : 1 ≤ n) :
    rootR0 n * chunkBits n ≤ 24 * n := by
  calc
    rootR0 n * chunkBits n
      ≤ (4 * max 1 (numChunks n)) * chunkBits n :=
        Nat.mul_le_mul_right (chunkBits n) (rootR0_le_four_mul_max_numChunks n)
    _ = 4 * (max 1 (numChunks n) * chunkBits n) := by ring
    _ ≤ 4 * (n + chunkBits n) := Nat.mul_le_mul_left 4 (max_numChunks_mul_chunkBits_le n)
    _ ≤ 4 * (n + 5 * n) := by
        have := chunkBits_le_five_mul hn
        omega
    _ = 24 * n := by ring

/-- Logarithmic upper bound `rootK0 n ≤ Nat.log 2 n + 2` for all $n \in \mathbb{N}$ (Section 7.1 (`sec:alg-spec`)). -/
theorem rootK0_le_log_add_two (n : ℕ) : rootK0 n ≤ Nat.log 2 n + 2 := by
  unfold rootK0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hN0 : numChunks 0 = 0 := by rfl
    rw [hN0]
    decide
  · have hN : numChunks n ≤ n := numChunks_le_self n
    have hmax : max 1 (numChunks n) ≤ n := max_le hn hN
    have hlt_pow : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h2max : 2 * max 1 (numChunks n) ≤ 2 ^ (Nat.log 2 n + 2) := by
      calc
        2 * max 1 (numChunks n) ≤ 2 * n := Nat.mul_le_mul_left 2 hmax
        _ ≤ 2 * 2 ^ (Nat.log 2 n + 1) := Nat.mul_le_mul_left 2 (le_of_lt hlt_pow)
        _ = 2 ^ (Nat.log 2 n + 2) := by rw [← pow_succ']
    have hclog : Nat.clog 2 (2 * max 1 (numChunks n)) ≤ Nat.log 2 n + 2 := by
      calc
        Nat.clog 2 (2 * max 1 (numChunks n)) ≤ Nat.clog 2 (2 ^ (Nat.log 2 n + 2)) :=
          Nat.clog_mono_right 2 h2max
        _ = Nat.log 2 n + 2 := Nat.clog_pow 2 (Nat.log 2 n + 2) (by norm_num)
    omega

/-- Root precision bound `rootP0 n ≤ 7 * chunkBits n` (Section 7.1 (`sec:alg-spec`)). -/
theorem rootP0_le_seven_mul_chunkBits (n : ℕ) : rootP0 n ≤ 7 * chunkBits n := by
  unfold rootP0
  have hb4 : 4 ≤ chunkBits n := chunkBits_ge_four n
  have hlog : Nat.log 2 n ≤ chunkBits n := le_max_right 4 (Nat.log 2 n)
  have hK0 : rootK0 n ≤ chunkBits n + 2 := by
    have := rootK0_le_log_add_two n
    omega
  omega

/-- **Linear Root Grid-Precision Product Bound (`rootR0_mul_rootP0_le`, Section 7.2 (`sec:cost-proof`), Theorem 1 (`thm:main`))**:
For all $n \ge 1$, $R_0(n) \cdot p_0(n) \le 168 n$. -/
theorem rootR0_mul_rootP0_le {n : ℕ} (hn : 1 ≤ n) :
    rootR0 n * rootP0 n ≤ 168 * n := by
  calc
    rootR0 n * rootP0 n
      ≤ rootR0 n * (7 * chunkBits n) :=
        Nat.mul_le_mul_left (rootR0 n) (rootP0_le_seven_mul_chunkBits n)
    _ = 7 * (rootR0 n * chunkBits n) := by ring
    _ ≤ 7 * (24 * n) := Nat.mul_le_mul_left 7 (rootR0_mul_chunkBits_le hn)
    _ = 168 * n := by ring

/-- **Asymptotic $O(n \log n)$ Root Work Product Bound for $n \ge 1$ (`rootR0_mul_rootP0_mul_rootK0_le_succ`,
Section 7.2 (`sec:cost-proof`), Theorem 1 (`thm:main`))**:
For all $n \ge 1$, $R_0(n) \cdot p_0(n) \cdot K_0(n) \le 336 \cdot n \cdot (\lfloor \log_2 n \rfloor + 1)$. -/
theorem rootR0_mul_rootP0_mul_rootK0_le_succ {n : ℕ} (hn : 1 ≤ n) :
    rootR0 n * rootP0 n * rootK0 n ≤ 336 * n * (Nat.log 2 n + 1) := by
  have hRP := rootR0_mul_rootP0_le hn
  have hK0 : rootK0 n ≤ 2 * (Nat.log 2 n + 1) := by
    have := rootK0_le_log_add_two n
    omega
  calc
    rootR0 n * rootP0 n * rootK0 n
      ≤ (168 * n) * (2 * (Nat.log 2 n + 1)) := Nat.mul_le_mul hRP hK0
    _ = 336 * n * (Nat.log 2 n + 1) := by ring

/-- **Asymptotic $O(n \log n)$ Root Work Product Bound for $n \ge 2$ (`rootR0_mul_rootP0_mul_rootK0_le`,
Section 7.2 (`sec:cost-proof`), Theorem 1 (`thm:main`))**:
For all $n \ge 2$, $R_0(n) \cdot p_0(n) \cdot K_0(n) \le 504 \cdot n \cdot \lfloor \log_2 n \rfloor$. -/
theorem rootR0_mul_rootP0_mul_rootK0_le {n : ℕ} (hn : 2 ≤ n) :
    rootR0 n * rootP0 n * rootK0 n ≤ 504 * n * Nat.log 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hlog1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hRP := rootR0_mul_rootP0_le hn1
  have hK0 : rootK0 n ≤ 3 * Nat.log 2 n := by
    have := rootK0_le_log_add_two n
    omega
  calc
    rootR0 n * rootP0 n * rootK0 n
      ≤ (168 * n) * (3 * Nat.log 2 n) := Nat.mul_le_mul hRP hK0
    _ = 504 * n * Nat.log 2 n := by ring

theorem t1Ell_le_two_pow_qChildEll (K p : ℕ) :
    t1Ell K ≤ 2 ^ (qChildEll K p) := by
  unfold t1Ell k1Ell qChildEll pChildEll pWorkEll
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem clog_two_mul_pChildEll_add_four_le {K p : ℕ}
    (hleaf : ¬ isBaseLeaf K p = true) :
    Nat.clog 2 (2 * pChildEll K p + 4) ≤ 2 * K + 12 := by
  unfold isBaseLeaf at hleaf
  rw [decide_eq_true_eq, not_le] at hleaf
  have hp_lt : p < 2 ^ K := by nlinarith [Nat.one_le_two_pow (n := K)]
  have hK_lt : K < 2 ^ K := Nat.lt_two_pow_self
  have hpos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hpow : 2 ^ (2 * K + 12) = 4096 * (2 ^ K * 2 ^ K) := by
    have h1 : 2 * K + 12 = (K + K) + 12 := by omega
    rw [h1, pow_add, pow_add]
    ring
  have hle : 2 * pChildEll K p + 4 ≤ 2 ^ (2 * K + 12) := by
    rw [pChildEll_eq, hpow]
    nlinarith
  exact (Nat.clog_le_iff_le_pow (by decide)).mpr hle

end IntMul

#print axioms IntMul.t1Ell_mul_rEll
#print axioms IntMul.two_mul_numChunks_le_rootR0
#print axioms IntMul.levelP_le
#print axioms IntMul.geom_sum_two_zpow_neg_lt_two
#print axioms IntMul.isBaseLeaf_recursionDepth
#print axioms IntMul.rootR0_mul_rootP0_le
#print axioms IntMul.rootR0_mul_rootP0_mul_rootK0_le_succ
#print axioms IntMul.rootR0_mul_rootP0_mul_rootK0_le
