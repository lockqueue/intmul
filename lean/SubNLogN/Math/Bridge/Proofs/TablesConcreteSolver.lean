import SubNLogN.Math.Bridge.TablesConcrete
import SubNLogN.Math.Bridge.Proofs.Kernel
import SubNLogN.Math.Bridge.Proofs.LemmaB_Tails
import SubNLogN.Math.Bridge.Proofs.LemmaC_Tables

/-!
# Bridge: the solver entries of the concrete tables `TabConcrete`

Proves the `μ̂, â, γ̂` clauses of `TablesCertifiedR rr` for the concrete entries `muConcreteR rr`,
`ahatConcreteR rr`, `gamConcreteR rr` of `SubNLogN/Math/Bridge/TablesConcrete.lean`, for every
nearest rounding `rr` (`IsNearestRounding rr`), at `α = alphaDefault ω` (Lemma 4.6 (bridge Lemma C)(iii) solver entries,
Lemma B.3 (`lem:phase-tables`)). The main result is
`TablesConcreteSolverProof.solverConcreteR_certified`.

* `c0Hat_c1Hat_err`: IntMul's certified evaluator `computableC0C1WithProgramCost ω pC (2t) (2u+1)`
  (`pC = coeffPrec P = P + 6`) evaluates `c0Coeff, c1Coeff (realErfScaled α)` at
  `y = (2u+1)/(2t) = (u+½)/t` within `2·realQuantizeMaxErr pC = 2^{-(P+8)}`
  (`IntMul.computableC0C1Core_spec`, which needs only `ω > 0`). By `LemmaBTails.kernelG_eq_c0` and
  `LemmaBTails.kernelG_sub_one_eq_c1` these are `G(y) = coeffC0 α t u` and
  `G(y-1) = coeffC1 α t u`. So `|ĉ_i - c_i| ≤ 2^{-(P+8)} ≤ 2^{-((q+1)+4)}` with `q = P + 2`.
* `coeff_orient`: the exact orientation `c_1 < c_0 ⟺ 2u < t` and `c_0 ≠ c_1` for even `t`
  (`G` is even and strictly decreasing on `[0,∞)`: `kernelG_neg`, `kernelG_strictAntiOn`).
* `solverConcreteR_certified`: `lemmaC_iii_solver rr hrr` with `u_S = 0` (the stored values are an
  exact division followed by one nearest rounding `rr q`), `lemmaB_iii` for `c_max > 0.49999999`,
  `kernelG_pos`; grid membership of `rr q x` (`rr_onGridR`) and of `max 0 (rr q x)`; `γ̂` holds by
  definition. Only the two defining properties of a nearest rounding are used (no tie rule).

Hypotheses: `IsNearestRounding rr`, `8 ≤ ω`, `t ≥ 2` a power of two, `u < t`. No pending contract is
assumed.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common

namespace TablesConcreteSolverProof

/-- IntMul's `(c₀, c₁)` evaluator accuracy for `p_work > 0` (the proof of
`IntMul.computableC0C1WithProgramCost_spec` only uses `0 < p_work`). -/
theorem c0c1_spec_of_pos (p_work pSub r u2 : ℕ) (hp_work : 0 < p_work) (hr : 0 < r)
    (hu2 : u2 < r) :
    |(IntMul.toScaledComplex pSub
          (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.1).re -
        IntMul.c0Coeff (IntMul.realErfScaled (IntMul.alphaSchedule p_work))
          ((u2 : ℝ) / (r : ℝ))| ≤ 2 * IntMul.realQuantizeMaxErr pSub ∧
      |(IntMul.toScaledComplex pSub
          (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.2).re -
        IntMul.c1Coeff (IntMul.realErfScaled (IntMul.alphaSchedule p_work))
          ((u2 : ℝ) / (r : ℝ))| ≤ 2 * IntMul.realQuantizeMaxErr pSub := by
  have h := IntMul.computableC0C1Core_spec p_work pSub
    (pSub + 2) ((pSub + 2) + 2) (8 * p_work + 1) (32 * p_work + 1)
    (((pSub + 2) + 2) + 2 * (8 * p_work + 1) + 6)
    (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4)
    (((pSub + 2) + 2) + 2 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6)
    ((((pSub + 2) + 2) + 2 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) + 6) +
      4 * (4 * (32 * p_work + 1) + ((pSub + 2) + 2) + (8 * p_work + 1) + 4) +
      2 * ((32 * p_work + 1) + (8 * p_work + 1)) +
      2 * (((pSub + 2) + 2) + 2 * (8 * p_work + 1) + 6) +
      ((pSub + 2) + 2) + 2 * p_work + 2 * Nat.log2 r + 40)
    r u2 rfl rfl rfl rfl le_rfl le_rfl (by omega) hp_work hr hu2
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-- `alphaDefault ω = 2√(ω ln2/π)` is admissible (lower end of eq. (`eq:alpha`)). -/
theorem alphaDefault_admissible (ω : ℕ) : AlphaAdmissible ω (alphaDefault ω) := by
  have h0 : 0 ≤ Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) := Real.sqrt_nonneg _
  unfold AlphaAdmissible alphaDefault IntMul.alphaSchedule
  constructor <;> linarith

/-- The sample point of the evaluator call: `(2u+1)/(2t) = (u+½)/t`. -/
theorem samplePt_eq (t u : ℕ) (ht : 0 < t) :
    ((2 * u + 1 : ℕ) : ℝ) / ((2 * t : ℕ) : ℝ) = ((u : ℝ) + 1 / 2) / (t : ℝ) := by
  have : (t : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Error of the evaluated `ĉ_0, ĉ_1`: within `2^{-((q+1)+4)}` of `c_0 = G((u+½)/t)`,
`c_1 = G((u+½)/t - 1)`, where `q = P + 2` and `α = alphaDefault ω`. -/
theorem c0Hat_c1Hat_err (ω P t u : ℕ) (hω : 0 < ω) (ht : 0 < t) (hu : u < t) :
    |c0Hat ω P t u - coeffC0 (alphaDefault ω) t u| ≤
        (2 : ℝ) ^ (-(((P + 2 + 1) + 4 : ℕ) : ℤ)) ∧
      |c1Hat ω P t u - coeffC1 (alphaDefault ω) t u| ≤
        (2 : ℝ) ^ (-(((P + 2 + 1) + 4 : ℕ) : ℤ)) := by
  obtain ⟨h0, h1⟩ := c0c1_spec_of_pos ω (coeffPrec P) (2 * t) (2 * u + 1) hω (by omega)
    (by omega)
  have hα : 0 < alphaDefault ω := IntMul.alphaSchedule_pos ω hω
  have herr : 2 * IntMul.realQuantizeMaxErr (coeffPrec P) ≤
      (2 : ℝ) ^ (-(((P + 2 + 1) + 4 : ℕ) : ℤ)) := by
    unfold IntMul.realQuantizeMaxErr coeffPrec
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
    exact zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
  have hy := samplePt_eq t u ht
  constructor
  · unfold c0Hat coeffC0
    rw [LemmaBTails.kernelG_eq_c0 _ _ hα, ← hy]
    exact h0.trans herr
  · unfold c1Hat coeffC1
    rw [LemmaBTails.kernelG_sub_one_eq_c1 _ _ hα, ← hy]
    exact h1.trans herr

/-- Exact orientation for even `t` (Lemma B.3 (`lem:phase-tables`), Lemma 4.4 (`lem:bridge-B`)(iii)):
`c_1 < c_0 ⟺ 2u < t`, and `c_0 ≠ c_1`, where `c_0 = G((u+½)/t)`, `c_1 = G((u+½)/t - 1)`. -/
theorem coeff_orient (α : ℝ) (hα : 0 < α) (t u : ℕ) (ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a)
    (hu : u < t) :
    (coeffC1 α t u < coeffC0 α t u ↔ 2 * u < t) ∧ coeffC0 α t u ≠ coeffC1 α t u := by
  obtain ⟨ht2, a, hta⟩ := ht
  have heven : 2 ∣ t := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at hta; omega
    · rw [hta]; exact dvd_pow_self 2 (by omega)
  obtain ⟨c, hc⟩ := heven
  have htpos : (0 : ℝ) < (t : ℝ) := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hanti := kernelG_strictAntiOn α hα
  set y : ℝ := ((u : ℝ) + 1 / 2) / (t : ℝ) with hy
  have hc0 : coeffC0 α t u = kernelG α y := rfl
  have hc1 : coeffC1 α t u = kernelG α (1 - y) := by
    unfold coeffC1
    rw [← kernelG_neg α (1 - y)]
    congr 1
    rw [hy]
    ring
  have hy0 : 0 ≤ y := by positivity
  have hy1 : 0 ≤ 1 - y := by
    have h3 : (u : ℝ) + 1 ≤ t := by exact_mod_cast hu
    have h4 : y ≤ 1 := by
      rw [hy, div_le_one htpos]
      linarith
    linarith
  rcases Nat.lt_or_ge (2 * u) t with h | h
  · -- `2u + 2 ≤ t`, so `y < 1 - y` and `c_1 < c_0`
    have hlt : y < 1 - y := by
      have h3 : 2 * (u : ℝ) + 1 < t := by
        have : 2 * u + 1 < t := by omega
        exact_mod_cast this
      have h4 : 2 * y < 1 := by
        rw [hy, mul_div_assoc', div_lt_one htpos]
        linarith
      linarith
    have hlt' : coeffC1 α t u < coeffC0 α t u := by
      rw [hc0, hc1]
      exact hanti hy0 hy1 hlt
    exact ⟨⟨fun _ => h, fun _ => hlt'⟩, hlt'.ne'⟩
  · -- `t ≤ 2u`, so `1 - y < y` and `c_0 < c_1`
    have hlt : 1 - y < y := by
      have h3 : (t : ℝ) < 2 * (u : ℝ) + 1 := by
        have : t < 2 * u + 1 := by omega
        exact_mod_cast this
      have h4 : 1 < 2 * y := by
        rw [hy, mul_div_assoc', one_lt_div htpos]
        linarith
      linarith
    have hlt' : coeffC0 α t u < coeffC1 α t u := by
      rw [hc0, hc1]
      exact hanti hy1 hy0 hlt
    refine ⟨⟨fun h' => absurd h' (not_lt.mpr hlt'.le), fun h' => absurd h' (by omega)⟩, hlt'.ne⟩

/-- The solver clauses of `TablesCertifiedR rr` for the concrete entries (Lemma 4.6 (bridge Lemma C)(iii) solver
entries, Lemma B.3 (`lem:phase-tables`)), for any nearest rounding `rr`, at `α = alphaDefault ω` and
`q = P + 2`: `μ̂ = muConcreteR rr`, `â = ahatConcreteR rr` lie on the `q`-grid,
`|μ̂ - c_max^{-1}| ≤ v`, `|â - c_min/c_max| ≤ v`, `â ≥ 0`, and `γ̂ = gamConcreteR rr` is the closure
computed from `â` (by definition). -/
theorem solverConcreteR_certified (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) (ω P t A u : ℕ)
    (hω : 8 ≤ ω) (ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (hu : u < t) :
    OnGridR (P + 2) (muConcreteR rr ω P t u) ∧ OnGridR (P + 2) (ahatConcreteR rr ω P t u) ∧
      |muConcreteR rr ω P t u -
          (max (coeffC0 (alphaDefault ω) t u) (coeffC1 (alphaDefault ω) t u))⁻¹| ≤
        gridUnit (P + 2) ∧
      |ahatConcreteR rr ω P t u -
          min (coeffC0 (alphaDefault ω) t u) (coeffC1 (alphaDefault ω) t u) /
            max (coeffC0 (alphaDefault ω) t u) (coeffC1 (alphaDefault ω) t u)| ≤
        gridUnit (P + 2) ∧
      0 ≤ ahatConcreteR rr ω P t u ∧
      gamConcreteR rr ω P t A u =
        closureFixedR rr (P + 2) (closurePrec (P + 2) A t) (ahatConcreteR rr ω P t u) A := by
  have hα : 0 < alphaDefault ω := IntMul.alphaSchedule_pos ω (by omega)
  have ht0 : 0 < t := by omega
  obtain ⟨he0, he1⟩ := c0Hat_c1Hat_err ω P t u (by omega) ht0 hu
  obtain ⟨horient, hne⟩ := coeff_orient (alphaDefault ω) hα t u ht hu
  have hB := lemmaB_iii ω hω (alphaDefault ω) (alphaDefault_admissible ω) t ht u hu
  have hmax : (0.49999999 : ℝ) <
      max (coeffC0 (alphaDefault ω) t u) (coeffC1 (alphaDefault ω) t u) :=
    lt_of_lt_of_le hB.2 hB.1
  have hc0 : 0 ≤ coeffC0 (alphaDefault ω) t u := (kernelG_pos _ hα _).le
  have hc1 : 0 ≤ coeffC1 (alphaDefault ω) t u := (kernelG_pos _ hα _).le
  have hμ : |(if 2 * u < t then (c0Hat ω P t u)⁻¹ else (c1Hat ω P t u)⁻¹) -
      (if coeffC1 (alphaDefault ω) t u < coeffC0 (alphaDefault ω) t u then c0Hat ω P t u
        else c1Hat ω P t u)⁻¹| ≤ 0 := by
    by_cases h : 2 * u < t
    · rw [if_pos h, if_pos (horient.mpr h), sub_self, abs_zero]
    · rw [if_neg h, if_neg (fun h' => h (horient.mp h')), sub_self, abs_zero]
  have ha : |(if 2 * u < t then c1Hat ω P t u / c0Hat ω P t u
        else c0Hat ω P t u / c1Hat ω P t u) -
      (if coeffC1 (alphaDefault ω) t u < coeffC0 (alphaDefault ω) t u then
        c1Hat ω P t u / c0Hat ω P t u else c0Hat ω P t u / c1Hat ω P t u)| ≤ 0 := by
    by_cases h : 2 * u < t
    · rw [if_pos h, if_pos (horient.mpr h), sub_self, abs_zero]
    · rw [if_neg h, if_neg (fun h' => h (horient.mp h')), sub_self, abs_zero]
  have hsol := lemmaC_iii_solver rr hrr (P + 2) (coeffC0 (alphaDefault ω) t u)
    (coeffC1 (alphaDefault ω) t u) (c0Hat ω P t u) (c1Hat ω P t u)
    (if 2 * u < t then (c0Hat ω P t u)⁻¹ else (c1Hat ω P t u)⁻¹)
    (if 2 * u < t then c1Hat ω P t u / c0Hat ω P t u else c0Hat ω P t u / c1Hat ω P t u) 0
    hc0 hc1 hmax hne he0 he1 ⟨le_rfl, by positivity⟩ hμ ha
  refine ⟨rr_onGridR hrr _ _, ?_, hsol.1.le, hsol.2.le, le_max_left _ _, rfl⟩
  -- grid membership of `max 0 (rr q a'')`
  unfold ahatConcreteR
  rcases le_total 0 (rr (P + 2) (if 2 * u < t then c1Hat ω P t u / c0Hat ω P t u
      else c0Hat ω P t u / c1Hat ω P t u)) with h | h
  · rw [max_eq_right h]; exact rr_onGridR hrr _ _
  · rw [max_eq_left h]; exact ⟨0, by simp⟩

end TablesConcreteSolverProof

end SubNLogN.Math.Bridge
