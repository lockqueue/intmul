import SubNLogN.Math.Bridge.TablesConcrete
import SubNLogN.Math.Bridge.LemmaC_Tables
import SubNLogN.Math.Bridge.Proofs.TablesConcreteSolver

/-!
# Bridge: certification of the concrete tables `TabConcrete` (Lemma 4.6 (bridge Lemma C)(iii), taps part)

Proves the tap clauses of `TablesCertifiedR rr` for `TabConcreteR rr` (`TapsCertified`, one axis at a
time), for every nearest rounding `rr` (`IsNearestRounding rr`), from `LemmaC_iii_tapStmt` and IntMul's
certified evaluators:
* phase: `IntMul.computableStdCharWithProgramCost_error_le` at `num/den`, `den = 2tA`,
  `num = (-(sA+a)) mod 2tA`. By the integer periodicity of `stdChar` this is the point
  `e^{-πi(s+a/A)/t}`, the modulated carrier phase at `s + δ`, `δ = a/A` (`stdChar_reduced`).
  Error `2·complexQuantizeMaxErr B = (√2/2)·2^{-B}`.
* kernel: `IntMul.computableSincGaussianTapWithProgramCost_spec` with `t1 = A`, `j1 = a`,
  `s_IntMul = (B - s).toNat`. This is the point `-(s + a/A)`, so by evenness `sinc·Gauss(s + a/A)`
  at `α = alphaSchedule ω = alphaDefault ω` (`sincGaussHat_err`). Error `2^{-B}`.
* product: `‖ĝ - g‖ ≤ 0.71·2^{-B}(1 + 2^{-B}) + 2^{-B} ≤ 4·2^{-B} = 2^{-(q+g+4)}`, because
  `B = tapPrec P = q + g + 6` (`sample_err`). This is exactly the sample tolerance of
  `LemmaC_iii_tapStmt`, which then gives the `< 0.71 v ≤ 2v` tap bound.
* parameters: from `WalshOK`, `ω ≤ P` (via `d < K0`), every `t_i ≥ 2` is a power of two, and
  `LemmaCParams P ω (alphaDefault ω)` holds with `λ_G = 1`.

All helpers live in the namespace `SubNLogN.Math.Bridge.TabConcreteCert`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost
open scoped BigOperators

namespace TabConcreteCert

theorem onGridR_quantR (q : ℕ) (x : ℝ) : OnGridR q (quantR q x) := ⟨_, rfl⟩

theorem onGridR_zero (q : ℕ) : OnGridR q 0 := ⟨0, by simp⟩

theorem onGridR_max_zero {q : ℕ} {x : ℝ} (hx : OnGridR q x) : OnGridR q (max 0 x) := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right h]; exact hx
  · rw [max_eq_left h]; exact onGridR_zero q

theorem crnd_zero {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ) : crnd rr q 0 = 0 :=
  crnd_eq_self hrr (onGrid_zero q)

theorem lg_le_self {n : ℕ} (hn : 1 ≤ n) : lg n ≤ n := by
  unfold lg
  exact max_le (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le) hn

theorem shape_facts {ρ : RowExps} {p0 K0 : ℕ} (h : WalshOK ρ p0 K0 = true)
    (i : Fin (fnewD ρ K0 + 1)) :
    2 ≤ fnewShape ρ K0 i ∧ ∃ a : ℕ, fnewShape ρ K0 i = 2 ^ a := by
  obtain ⟨⟨hd, hl, -⟩, -⟩ := (WalshOK_iff ρ p0 K0).mp h
  refine ⟨?_, _, rfl⟩
  unfold fnewShape
  have hexp : 1 ≤ (if h : (i : ℕ) < fnewD ρ K0 then fnewA ρ K0 ⟨i, h⟩ else fnewL ρ K0) := by
    split_ifs
    · unfold fnewA; split_ifs <;> omega
    · unfold fnewL; omega
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp

theorem omega_le_P {ρ : RowExps} {p0 K0 : ℕ} (h : WalshOK ρ p0 K0 = true) :
    schedOmega p0 K0 (fnewD ρ K0 + 1) ≤ schedP p0 K0 := by
  obtain ⟨⟨hd, hl, hdl, -⟩, -⟩ := (WalshOK_iff ρ p0 K0).mp h
  have hD : fnewD ρ K0 + 1 = dK ρ K0 := by unfold fnewD; omega
  have hmul : 2 * dK ρ K0 ≤ dK ρ K0 * lK ρ K0 := by nlinarith
  have hdK : dK ρ K0 ≤ K0 := by omega
  have hlg : lg (dK ρ K0) ≤ dK ρ K0 := lg_le_self (by omega)
  unfold schedOmega schedP
  rw [hD]
  omega

theorem alphaDefault_sq (ω : ℕ) :
    alphaDefault ω ^ 2 = 4 * (ω : ℝ) * Real.log 2 / Real.pi := by
  unfold alphaDefault IntMul.alphaSchedule
  rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg one_le_two)) Real.pi_pos.le)]
  ring

theorem lemmaCParams_of {P ω : ℕ} (hP : 20 ≤ P) (hω : 8 ≤ ω) (hωP : ω ≤ P) :
    LemmaCParams P ω (alphaDefault ω) :=
  ⟨hP, hω, hωP, IntMul.alphaSchedule_pos ω (by omega), 1, le_rfl, by norm_num, by
    rw [alphaDefault_sq]; push_cast; ring⟩

theorem alphaAdmissible_default (ω : ℕ) : AlphaAdmissible ω (alphaDefault ω) := by
  refine ⟨le_rfl, ?_⟩
  unfold alphaDefault IntMul.alphaSchedule
  have := Real.sqrt_nonneg ((ω : ℝ) * Real.log 2 / Real.pi)
  linarith

theorem stdChar_reduced (t A a : ℕ) (s : ℤ) (ht : 0 < t) (hA : 0 < A) :
    IntMul.stdChar ((((-(s * (A : ℤ) + (a : ℤ))) % ((2 * t * A : ℕ) : ℤ)).toNat : ℝ) /
        ((2 * t * A : ℕ) : ℝ)) =
      IntMul.stdChar (-(((s : ℝ) + (a : ℝ) / (A : ℝ)) / (2 * (t : ℝ)))) := by
  have hD : (0 : ℤ) < ((2 * t * A : ℕ) : ℤ) := by positivity
  have hn0 : 0 ≤ (-(s * (A : ℤ) + (a : ℤ))) % ((2 * t * A : ℕ) : ℤ) := Int.emod_nonneg _ hD.ne'
  have hcast : ((((-(s * (A : ℤ) + (a : ℤ))) % ((2 * t * A : ℕ) : ℤ)).toNat : ℕ) : ℝ) =
      (((-(s * (A : ℤ) + (a : ℤ))) % ((2 * t * A : ℕ) : ℤ) : ℤ) : ℝ) := by
    have h1 := Int.toNat_of_nonneg hn0
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
  rw [hcast, Int.emod_def]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have key : (((-(s * (A : ℤ) + (a : ℤ))) - ((2 * t * A : ℕ) : ℤ) *
        ((-(s * (A : ℤ) + (a : ℤ))) / ((2 * t * A : ℕ) : ℤ)) : ℤ) : ℝ) / ((2 * t * A : ℕ) : ℝ) =
      -(((s : ℝ) + (a : ℝ) / (A : ℝ)) / (2 * (t : ℝ))) +
        ((-((-(s * (A : ℤ) + (a : ℤ))) / ((2 * t * A : ℕ) : ℤ)) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [key, IntMul.stdChar_add_int]

theorem sincGaussHat_err (ω B A a : ℕ) (s : ℤ) (hω : 0 < ω) (hB : 0 < B) (hA : 0 < A)
    (ha : a < A) (hs1 : s ≤ (B : ℤ)) (hs2 : -(B : ℤ) ≤ s) :
    ‖sincGaussHat ω B A a s -
        (IntMul.sincGaussian (IntMul.alphaSchedule ω) ((s : ℝ) + (a : ℝ) / (A : ℝ)) : ℂ)‖ ≤
      (2 : ℝ) ^ (-(B : ℤ)) := by
  have htn : (((B : ℤ) - s).toNat : ℤ) = (B : ℤ) - s := Int.toNat_of_nonneg (by omega)
  have hlt : ((B : ℤ) - s).toNat < 2 * B + 1 := by omega
  obtain ⟨hspec, -⟩ := IntMul.computableSincGaussianTapWithProgramCost_spec ω B A a
    ((B : ℤ) - s).toNat hω hB hA ha hlt
  rw [htn] at hspec
  have hpt : (((B : ℤ) - s : ℤ) : ℝ) - (((B : ℕ) : ℤ) : ℝ) - (a : ℝ) / (A : ℝ) =
      -((s : ℝ) + (a : ℝ) / (A : ℝ)) := by
    push_cast; ring
  rw [hpt, IntMul.sincGaussian_even] at hspec
  unfold sincGaussHat
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hspec


/-- The tap precision `B = tapPrec P` is `N + 2`, where `2^{-N}` is the sample tolerance of
`LemmaC_iii_tapStmt`. -/
theorem tapPrec_eq (P : ℕ) : tapPrec P = (P + 2 + (lg (2 * P + 2) + 12) + 4) + 2 := by
  unfold tapPrec tapGuard; ring

/-- Sample error: `‖phaseHat · sincGaussHat - carrier α t (s + a/A)‖ ≤ 2^{-(q+g+4)}` for
`s ∈ [-P, P]`, with `α = alphaDefault ω`. -/
theorem sample_err (ω P t A a : ℕ) (s : ℤ) (hω : 0 < ω) (ht : 0 < t) (hA : 0 < A) (ha : a < A)
    (hs : s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ)) :
    ‖phaseHat (tapPrec P) t A a s * sincGaussHat ω (tapPrec P) A a s -
        carrier (alphaDefault ω) t ((s : ℝ) + (a : ℝ) / (A : ℝ))‖ ≤
      (2 : ℝ) ^ (-((P + 2 + (lg (2 * P + 2) + 12) + 4 : ℕ) : ℤ)) := by
  obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.mp hs
  have hB := tapPrec_eq P
  set N : ℕ := P + 2 + (lg (2 * P + 2) + 12) + 4 with hN
  set B : ℕ := tapPrec P with hBdef
  -- phase evaluator
  have hden : 0 < 2 * t * A := by positivity
  have hD : (0 : ℤ) < ((2 * t * A : ℕ) : ℤ) := by positivity
  have hnum : ((-(s * (A : ℤ) + (a : ℤ))) % ((2 * t * A : ℕ) : ℤ)).toNat ≤ 2 * t * A := by
    have h1 := Int.emod_lt_of_pos (-(s * (A : ℤ) + (a : ℤ))) hD
    have h2 := Int.emod_nonneg (-(s * (A : ℤ) + (a : ℤ))) hD.ne'
    omega
  have hph := IntMul.computableStdCharWithProgramCost_error_le B _ (2 * t * A) false hden hnum
  simp only [Bool.false_eq_true, ↓reduceIte] at hph
  rw [stdChar_reduced t A a s ht hA] at hph
  -- tap evaluator
  have hsg := sincGaussHat_err ω B A a s hω (by omega) hA ha (by omega) (by omega)
  -- abbreviations
  set phat : ℂ := phaseHat B t A a s with hphat
  set shat : ℂ := sincGaussHat ω B A a s with hshat
  set e : ℂ := IntMul.stdChar (-(((s : ℝ) + (a : ℝ) / (A : ℝ)) / (2 * (t : ℝ)))) with he
  set g : ℂ := (IntMul.sincGaussian (IntMul.alphaSchedule ω) ((s : ℝ) + (a : ℝ) / (A : ℝ)) : ℂ)
    with hg
  have hcar : carrier (alphaDefault ω) t ((s : ℝ) + (a : ℝ) / (A : ℝ)) = e * g := rfl
  have hph' : ‖phat - e‖ ≤ 2 * IntMul.complexQuantizeMaxErr B := hph
  have hen : ‖e‖ = 1 := IntMul.norm_stdChar _
  have hgn : ‖g‖ ≤ 1 := by
    rw [hg, Complex.norm_real, Real.norm_eq_abs]
    exact IntMul.abs_sincGaussian_le_one _ _
  set ε : ℝ := (2 : ℝ) ^ (-(B : ℤ)) with hε
  have hε0 : 0 < ε := zpow_pos (by norm_num) _
  have hε1 : ε ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hcq : 2 * IntMul.complexQuantizeMaxErr B ≤ 0.71 * ε := by
    rw [IntMul.complexQuantizeMaxErr_eq]
    have := IntMul.sqrt_two_lt_1416
    nlinarith
  have hshn : ‖shat‖ ≤ 1 + ε := by
    have h1 : ‖shat‖ ≤ ‖g‖ + ‖shat - g‖ := by
      have := norm_add_le g (shat - g)
      simpa using this
    linarith
  have hsplit : phat * shat - e * g = (phat - e) * shat + e * (shat - g) := by ring
  have hNB : (2 : ℝ) ^ (-(N : ℤ)) = 4 * ε := by
    rw [hε, hB]
    push_cast
    rw [IntMul.two_zpow_neg_add_two]
    ring
  rw [hcar, hsplit, hNB]
  calc ‖(phat - e) * shat + e * (shat - g)‖
      ≤ ‖phat - e‖ * ‖shat‖ + ‖e‖ * ‖shat - g‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (0.71 * ε) * (1 + ε) + 1 * ε := by
        rw [hen]
        gcongr
        · exact hph'.trans hcq
    _ ≤ 4 * ε := by nlinarith


theorem prefixProd_pos' {d : ℕ} {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) (k : ℕ) :
    0 < prefixProd t k :=
  Finset.prod_pos fun i _ => ht i

/-- Lemma 4.6 (bridge Lemma C)(iii) taps for the concrete family (one axis), for any nearest rounding `rr`: the four
clauses of `TapsCertified`. -/
theorem tapConcreteR_certified (htap : LemmaC_iii_tapStmt) {rr : ℕ → ℝ → ℝ}
    (hrr : IsNearestRounding rr) {ω P t A : ℕ}
    (hC : LemmaCParams P ω (alphaDefault ω)) (ht : 0 < t) (hA : 0 < A) (a : ℕ) (ha : a < A)
    (e : ℤ) :
    OnGrid (P + 2) (tapConcreteR rr ω P t A a e) ∧
    ‖tapConcreteR rr ω P t A a e - truncFoldedFilter (alphaDefault ω) t P ((a : ℝ) / (A : ℝ)) e‖ ≤
      2 * gridUnit (P + 2) ∧
    ((∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (t : ℤ) ≠ e % (t : ℤ)) →
      tapConcreteR rr ω P t A a e = 0) ∧
    tapConcreteR rr ω P t A a (e + (t : ℤ)) = tapConcreteR rr ω P t A a e := by
  refine ⟨crnd_onGrid hrr _ _, ?_, ?_, ?_⟩
  · have hω : 0 < ω := by have := hC.2.1; omega
    have h : ‖tapConcreteR rr ω P t A a e -
        truncFoldedFilter (alphaDefault ω) t P ((a : ℝ) / (A : ℝ)) e‖ <
        0.71 * gridUnit (P + 2) :=
      htap rr hrr P ω (alphaDefault ω) hC t ht ((a : ℝ) / (A : ℝ)) e
        (fun s => phaseHat (tapPrec P) t A a s * sincGaussHat ω (tapPrec P) A a s)
        (fun s hs => sample_err ω P t A a s hω ht hA ha hs)
    have hv := gridUnit_pos (P + 2)
    linarith
  · intro hno
    unfold tapConcreteR
    rw [Finset.sum_eq_zero (fun s hs => if_neg (hno s hs)), crnd_zero hrr]
  · unfold tapConcreteR
    simp only [Int.add_emod_right]

end TabConcreteCert

/-- **Lemma 4.6 (bridge Lemma C)(iii) for the concrete tables** (`TabConcrete_certifiedStmt`), for every nearest
rounding `rr`, from the tap contract `LemmaC_iii_tapStmt`. The taps are certified here
(`TabConcreteCert.tapConcreteR_certified`); the solver entries `μ̂, â, γ̂` come from
`TablesConcreteSolverProof.solverConcreteR_certified` (`Proofs/TablesConcreteSolver.lean`). -/
theorem tabConcrete_certified_of (htap : LemmaC_iii_tapStmt) : TabConcrete_certifiedStmt := by
  intro rr hrr ρ p0 K0 hW i _hi
  have hωP := TabConcreteCert.omega_le_P hW
  have hP20 : 20 ≤ schedP p0 K0 := by unfold schedP; omega
  have hω8 : 8 ≤ schedOmega p0 K0 (fnewD ρ K0 + 1) := by unfold schedOmega; omega
  have hC := TabConcreteCert.lemmaCParams_of hP20 hω8 hωP
  have htpos : ∀ j, 0 < fnewShape ρ K0 j := fun j => by
    have := (TabConcreteCert.shape_facts hW j).1
    omega
  have hApos := TabConcreteCert.prefixProd_pos' htpos (i : ℕ)
  refine ⟨fun a ha e => TabConcreteCert.tapConcreteR_certified htap hrr hC (htpos i) hApos a ha e,
    fun u hu => ?_⟩
  exact TablesConcreteSolverProof.solverConcreteR_certified rr hrr _ _ _ _ u hω8
    (TabConcreteCert.shape_facts hW i) hu

/-- **Lemma 4.6 (bridge Lemma C)(iii) for the concrete tables**, unconditional: `tabConcrete_certified_of` with the
proved tap contract `lemmaC_iii_tap` (`Proofs/LemmaC_Tables.lean`). -/
theorem tabConcrete_certified : TabConcrete_certifiedStmt :=
  tabConcrete_certified_of lemmaC_iii_tap

end SubNLogN.Math.Bridge
