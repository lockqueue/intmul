import IntMul.Theorem5ComplexityAndCorrectness
import IntMulTM.Framework.AxiomGuard

/-!
# W14 (1/11): schedules

Per-node schedule constants of the sinc-Gaussian FastDFT, as a parameter of the pipeline, the table
faithfulness predicate and the error closure.

* `StepSchedule`: `pSub` (sub-step grid; `complexQuantize pSub` rounds to `pSub + 2` fractional bits, and
  the spread uses `quantizeInt pSub`, as the snapshot's computable pipeline does), `m1` (window half-width)
  and `qLeaf` (leaf internal grid).
* `snapshotSchedule`: the snapshot's choices (`2 * pChild`, `2 * pChild`, `2p + K + 8`).
* `paperSchedule`: `[MS]`'s schedule (`[MS]` Lemma 6.5, Theorem 6.3, Theorem 1): `pSub = pChild` (q_child = p_{l+1} + 2 bits),
  `m1 = ⌈(2 ln 2 / π) √(pWork pChild)⌉` (computed with the rational constant 4412713/10^7, see `m1Paper`),
  `qLeaf = p + K + 2` (q_base = p + K + 4 bits).
* `RootParams`, `paperRoot`: the paper's root chunking `b = max 4 ⌊log₂ n⌋`, `N = max 1 ⌈n/b⌉`
  (limb count), `K0 = ⌈log₂ 2N⌉`; `snapshotRoot` is the snapshot's.

Window rules (`WindowRules`) are proved for `m1Paper`; they feed the snapshot's generic tail lemma.
-/

namespace WP.W14

open IntMul

/-- Per-node schedule constants (functions of the node's target precision `p` and log-length `K`). -/
structure StepSchedule where
  /-- Sub-step grid exponent (also the spread's `quantizeInt` grid). -/
  pSub : ℕ → ℕ → ℕ
  /-- Window half-width. -/
  m1 : ℕ → ℕ → ℕ
  /-- Leaf internal grid exponent. -/
  qLeaf : ℕ → ℕ → ℕ

/-- The snapshot's schedule (QFD:44–45, FTP:251). -/
def snapshotSchedule : StepSchedule where
  pSub p K := 2 * pChild p K
  m1 p K := 2 * pChild p K
  qLeaf p K := 2 * p + K + 8

/-- Ceiling square root on `ℕ`. -/
def ceilSqrt (n : ℕ) : ℕ :=
  if Nat.sqrt n * Nat.sqrt n = n then Nat.sqrt n else Nat.sqrt n + 1

/-- Numerator of the window constant `4412713 / 10^7 > 2 ln 2 / π = 0.44127120…`. -/
def m1A : ℕ := 4412713

/-- Denominator of the window constant. -/
def m1B : ℕ := 10000000

/-- The paper's window half-width `⌈(2 ln 2/π) √(pWork · pChild)⌉`, computed exactly as
`⌈(m1A/m1B) √(pWork · pChild)⌉` (the least `m` with `m1B² m² ≥ m1A² · pWork · pChild`). The exact
real ceiling is not effectively computable without the irrationality of `π / ln 2`; this value equals it
or exceeds it by one. -/
def m1Paper (p K : ℕ) : ℕ :=
  (ceilSqrt (m1A * m1A * (pWork p K * pChild p K)) + m1B - 1) / m1B

/-- The paper's schedule. -/
def paperSchedule : StepSchedule where
  pSub p K := pChild p K
  m1 := m1Paper
  qLeaf p K := p + K + 2

/-- Root chunking parameters: chunk width `b`, limb count `k`, root log-length `K0`. -/
structure RootParams where
  b : ℕ
  k : ℕ
  K0 : ℕ

/-- `[MS]`'s root (`[MS]` §7.1, Listing 1; Theorem 1, §7.2, Part 1): `b = max 4 ⌊log₂ n⌋`, `N = max 1 ⌈n/b⌉`, `K0 = ⌈log₂ 2N⌉`. -/
def paperRoot (n : ℕ) : RootParams :=
  ⟨max 4 (Nat.log2 n), max 1 ((n + max 4 (Nat.log2 n) - 1) / max 4 (Nat.log2 n)),
    Nat.clog 2 (2 * max 1 ((n + max 4 (Nat.log2 n) - 1) / max 4 (Nat.log2 n)))⟩

/-- The snapshot's root (CSWS:2264–2266). -/
def snapshotRoot (n : ℕ) : RootParams :=
  ⟨max 1 (Nat.log2 n), n / max 1 (Nat.log2 n) + 1,
    max 4 (Nat.log2 (2 * (n / max 1 (Nat.log2 n) + 1)) + 2)⟩

/-! ### Window rules -/

/-- The hypotheses of the snapshot's generic tail lemma (T3:1886) at window `m1`, node `(p, K)`. -/
def WindowRules (m1 p K : ℕ) : Prop :=
  0 < alphaSchedule (pWork p K) ∧ 8 ≤ m1 ∧
    (pChild p K : ℝ) * Real.log 2 ≤ Real.pi * (m1 : ℝ) ^ 2 / (alphaSchedule (pWork p K)) ^ 2 ∧
    (1 / 2 : ℝ) ≤ 2 * Real.pi * (m1 : ℝ) / (alphaSchedule (pWork p K)) ^ 2

theorem windowRules_snapshot (p K : ℕ) : WindowRules (snapshotSchedule.m1 p K) p K :=
  lemma2_spatial_window_rules_two_mul_pChild p K

/-! ### `ceilSqrt` -/

theorem le_ceilSqrt_mul_self (n : ℕ) : n ≤ ceilSqrt n * ceilSqrt n := by
  unfold ceilSqrt
  split_ifs with h
  · exact h.ge
  · exact (Nat.lt_succ_sqrt n).le

theorem ceilSqrt_le_of_le_mul_self {n s : ℕ} (h : n ≤ s * s) : ceilSqrt n ≤ s := by
  unfold ceilSqrt
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  split_ifs with heq
  · exact Nat.mul_self_le_mul_self_iff.mp (heq.le.trans h)
  · have hlt : Nat.sqrt n * Nat.sqrt n < s * s := lt_of_lt_of_le (lt_of_le_of_ne hsq heq) h
    exact Nat.mul_self_lt_mul_self_iff.mp hlt

/-! ### `m1Paper`: integer bounds -/

theorem pWork_le_pChild (p K : ℕ) : pWork p K ≤ pChild p K := by
  unfold pChild pWork; omega

/-- Lower bound: `m1A² · pWork · pChild ≤ (m1B · m1Paper)²`. -/
theorem m1Paper_lower (p K : ℕ) :
    m1A * m1A * (pWork p K * pChild p K) ≤ (m1B * m1Paper p K) * (m1B * m1Paper p K) := by
  set c := ceilSqrt (m1A * m1A * (pWork p K * pChild p K))
  have hc := le_ceilSqrt_mul_self (m1A * m1A * (pWork p K * pChild p K))
  have hB : 0 < m1B := by unfold m1B; norm_num
  have hcB : c ≤ m1B * m1Paper p K := by
    unfold m1Paper
    have h1 := Nat.div_add_mod (c + m1B - 1) m1B
    have h2 := Nat.mod_lt (c + m1B - 1) hB
    change c ≤ m1B * ((c + m1B - 1) / m1B)
    omega
  exact hc.trans (Nat.mul_le_mul hcB hcB)

/-- Upper bound: `2 m1Paper + 1 ≤ pChild` once `pChild ≥ 26`. -/
theorem m1Paper_upper (p K : ℕ) (h : 26 ≤ pChild p K) : 2 * m1Paper p K + 1 ≤ pChild p K := by
  set pc := pChild p K
  set pw := pWork p K
  have hpw : pw ≤ pc := pWork_le_pChild p K
  have hle : m1A * m1A * (pw * pc) ≤ (m1A * pc) * (m1A * pc) := by
    have : pw * pc ≤ pc * pc := Nat.mul_le_mul_right pc hpw
    calc m1A * m1A * (pw * pc) ≤ m1A * m1A * (pc * pc) := Nat.mul_le_mul_left _ this
      _ = (m1A * pc) * (m1A * pc) := by ring
  have hc : ceilSqrt (m1A * m1A * (pw * pc)) ≤ m1A * pc := ceilSqrt_le_of_le_mul_self hle
  have hB : 0 < m1B := by unfold m1B; norm_num
  have hdiv : m1Paper p K * m1B ≤ ceilSqrt (m1A * m1A * (pw * pc)) + m1B - 1 := by
    unfold m1Paper
    exact Nat.div_mul_le_self _ _
  have hA : m1A = 4412713 := rfl
  have hB' : m1B = 10000000 := rfl
  rw [hA] at hc
  rw [hA, hB'] at hdiv
  omega

/-- `m1Paper ≥ 8` for `p ≥ 8`, `K ≥ 2` (in fact `≥ 9` under the schedule of `[MS]` Lemma 6.5, eq. (34)). -/
theorem m1Paper_ge_eight (p K : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) : 8 ≤ m1Paper p K := by
  by_contra hlt
  push_neg at hlt
  have h7 : m1Paper p K ≤ 7 := by omega
  have hN : 384 ≤ pWork p K * pChild p K := by
    have h1 : 16 ≤ pWork p K := by unfold pWork; omega
    have h2 : 24 ≤ pChild p K := by unfold pChild pWork; omega
    calc 384 = 16 * 24 := by norm_num
      _ ≤ pWork p K * pChild p K := Nat.mul_le_mul h1 h2
  have hlow := m1Paper_lower p K
  have hm : m1B * m1Paper p K ≤ m1B * 7 := Nat.mul_le_mul_left _ h7
  have hsq := Nat.mul_le_mul hm hm
  have hA : m1A * m1A * 384 ≤ m1A * m1A * (pWork p K * pChild p K) := Nat.mul_le_mul_left _ hN
  have hfin : m1A * m1A * 384 ≤ (m1B * 7) * (m1B * 7) := hA.trans (hlow.trans hsq)
  unfold m1A m1B at hfin
  norm_num at hfin

/-! ### `m1Paper`: real window rules -/

/-- The rational window constant dominates the paper's: `2 ln 2 · m1B ≤ π · m1A`. -/
theorem two_log_two_mul_m1B_le : 2 * Real.log 2 * (m1B : ℝ) ≤ Real.pi * (m1A : ℝ) := by
  have hL := Real.log_two_lt_d9
  have hP := Real.pi_gt_d20
  have hA : (m1A : ℝ) = 4412713 := by unfold m1A; norm_num
  have hB : (m1B : ℝ) = 10000000 := by unfold m1B; norm_num
  rw [hA, hB]
  nlinarith

theorem m1Paper_lower_real (p K : ℕ) :
    (m1A : ℝ) ^ 2 * ((pWork p K : ℝ) * (pChild p K : ℝ)) ≤ (m1B : ℝ) ^ 2 * (m1Paper p K : ℝ) ^ 2 := by
  have h := m1Paper_lower p K
  have h' : ((m1A * m1A * (pWork p K * pChild p K) : ℕ) : ℝ) ≤
      (((m1B * m1Paper p K) * (m1B * m1Paper p K) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  nlinarith [h']

theorem windowRules_paper (p K : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) :
    WindowRules (paperSchedule.m1 p K) p K := by
  change WindowRules (m1Paper p K) p K
  set pw := pWork p K
  set pc := pChild p K
  set m := m1Paper p K
  set α := alphaSchedule pw
  have hpw_pos : 0 < pw := by unfold pw pWork; omega
  have hα : 0 < α := alphaSchedule_pos pw hpw_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hL0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpa : Real.pi * α ^ 2 = 4 * (pw : ℝ) * Real.log 2 := pi_mul_alphaSchedule_sq pw hpw_pos
  have hα2 : α ^ 2 = 4 * (pw : ℝ) * Real.log 2 / Real.pi := by
    field_simp; linarith
  have hlow := m1Paper_lower_real p K
  have hkey := two_log_two_mul_m1B_le
  have hA0 : (0 : ℝ) < (m1A : ℝ) := by unfold m1A; norm_num
  have hB0 : (0 : ℝ) < (m1B : ℝ) := by unfold m1B; norm_num
  have hpwR : (0 : ℝ) < (pw : ℝ) := by exact_mod_cast hpw_pos
  have hpcR : (pw : ℝ) ≤ (pc : ℝ) := by exact_mod_cast pWork_le_pChild p K
  have hm8 : 8 ≤ m := m1Paper_ge_eight p K hp hK
  have hmR : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm8
  -- (2 L B)^2 ≤ (π A)^2
  have hsq : (2 * Real.log 2 * (m1B : ℝ)) ^ 2 ≤ (Real.pi * (m1A : ℝ)) ^ 2 := by
    have h0 : 0 ≤ 2 * Real.log 2 * (m1B : ℝ) := by positivity
    exact pow_le_pow_left₀ h0 hkey 2
  -- 4 L² pw pc ≤ π² m²
  have hmain : 4 * Real.log 2 ^ 2 * ((pw : ℝ) * (pc : ℝ)) ≤ Real.pi ^ 2 * (m : ℝ) ^ 2 := by
    have hppos : 0 ≤ (pw : ℝ) * (pc : ℝ) := by positivity
    have h1 : (2 * Real.log 2 * (m1B : ℝ)) ^ 2 * ((pw : ℝ) * (pc : ℝ)) ≤
        (Real.pi * (m1A : ℝ)) ^ 2 * ((pw : ℝ) * (pc : ℝ)) := mul_le_mul_of_nonneg_right hsq hppos
    have h2 : (Real.pi * (m1A : ℝ)) ^ 2 * ((pw : ℝ) * (pc : ℝ)) ≤
        Real.pi ^ 2 * ((m1B : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hlow (sq_nonneg Real.pi)
      nlinarith [this]
    have h3 : (m1B : ℝ) ^ 2 * (4 * Real.log 2 ^ 2 * ((pw : ℝ) * (pc : ℝ))) ≤
        (m1B : ℝ) ^ 2 * (Real.pi ^ 2 * (m : ℝ) ^ 2) := by nlinarith [h1, h2]
    exact le_of_mul_le_mul_left h3 (by positivity)
  refine ⟨hα, hm8, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity), hα2]
    have h4 : (pc : ℝ) * Real.log 2 * (4 * (pw : ℝ) * Real.log 2 / Real.pi) =
        (4 * Real.log 2 ^ 2 * ((pw : ℝ) * (pc : ℝ))) / Real.pi := by ring
    rw [h4, div_le_iff₀ hpi]
    nlinarith [hmain]
  · rw [le_div_iff₀ (by positivity), hα2]
    -- need pw · ln 2 ≤ π² m (since 4π m ≥ α² = 4 pw ln2/π)
    -- from (A pw)^2 ≤ A² pw pc ≤ (B m)^2: A pw ≤ B m
    have hApw : (m1A : ℝ) * (pw : ℝ) ≤ (m1B : ℝ) * (m : ℝ) := by
      have hsq2 : ((m1A : ℝ) * (pw : ℝ)) ^ 2 ≤ ((m1B : ℝ) * (m : ℝ)) ^ 2 := by
        have : (m1A : ℝ) ^ 2 * ((pw : ℝ) * (pw : ℝ)) ≤ (m1A : ℝ) ^ 2 * ((pw : ℝ) * (pc : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hpcR hpwR.le
        nlinarith [this, hlow]
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq2
    have hA : (m1A : ℝ) = 4412713 := by unfold m1A; norm_num
    have hB : (m1B : ℝ) = 10000000 := by unfold m1B; norm_num
    rw [hA, hB] at hApw
    have hgoal : 1 / 2 * (4 * (pw : ℝ) * Real.log 2 / Real.pi) ≤ 2 * Real.pi * (m : ℝ) := by
      rw [div_eq_mul_inv]
      have hpinv : Real.pi⁻¹ ≤ 1 / 3 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hpi3.le
      have hpinv0 : 0 < Real.pi⁻¹ := inv_pos.mpr hpi
      nlinarith [hApw, hpinv, hL1, hmR]
    linarith [hgoal]

/-! ### Root parameters -/

theorem paperRoot_b (n : ℕ) : (paperRoot n).b = max 4 (Nat.log2 n) := rfl

theorem paperRoot_b_ge (n : ℕ) : 4 ≤ (paperRoot n).b := le_max_left _ _

theorem paperRoot_k_pos (n : ℕ) : 1 ≤ (paperRoot n).k := le_max_left _ _

/-- `k1 + k2 ≤ 2^K0` at `k1 = k2 = N`. -/
theorem paperRoot_hk (n : ℕ) : (paperRoot n).k + (paperRoot n).k ≤ 2 ^ (paperRoot n).K0 := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * (paperRoot n).k)
  change (paperRoot n).k + (paperRoot n).k ≤ 2 ^ Nat.clog 2 (2 * (paperRoot n).k)
  omega

/-- The limbs cover the input: `n ≤ b · N`. -/
theorem paperRoot_cover (n : ℕ) : n ≤ (paperRoot n).b * (paperRoot n).k := by
  set b := max 4 (Nat.log2 n) with hb
  have hb4 : 4 ≤ b := le_max_left _ _
  change n ≤ b * max 1 ((n + b - 1) / b)
  have h1 := Nat.div_add_mod (n + b - 1) b
  have h2 := Nat.mod_lt (n + b - 1) (by omega : 0 < b)
  have h3 : (n + b - 1) / b ≤ max 1 ((n + b - 1) / b) := le_max_right _ _
  have h4 : b * ((n + b - 1) / b) ≤ b * max 1 ((n + b - 1) / b) := Nat.mul_le_mul_left _ h3
  omega

theorem paperRoot_lt_of_lt (n A : ℕ) (hA : A < 2 ^ n) :
    A < (2 ^ (paperRoot n).b) ^ (paperRoot n).k := by
  rw [← pow_mul]
  exact lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (paperRoot_cover n))

theorem paperRoot_p0_ge (n : ℕ) : 8 ≤ rootPrecision (paperRoot n).b (paperRoot n).K0 := by
  have := paperRoot_b_ge n
  unfold rootPrecision; omega

#assert_std_axioms le_ceilSqrt_mul_self ceilSqrt_le_of_le_mul_self m1Paper_lower m1Paper_upper
  m1Paper_ge_eight two_log_two_mul_m1B_le m1Paper_lower_real windowRules_paper windowRules_snapshot
  paperRoot_hk paperRoot_cover paperRoot_lt_of_lt paperRoot_p0_ge

end WP.W14
