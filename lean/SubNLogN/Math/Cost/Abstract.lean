import Mathlib
import SubNLogN.S5.HeadlineCost
import SubNLogN.Math.Cost.Absorb

/-!
# Cost: the abstract cost theorem

Paper: Section 7.4 (`sec:main-gaps`, slack absorption), Section 7.6 (`sec:main-thm`) (all normalized cost bounds
are at most `C P^{1-g_min} (lg(2P))^j`), and Section 7.6 (`sec:main-thm`) (proof of Theorem 1 (`thm:main`): `M(n) = O(RP·P^{1-κ})`,
`RP = Θ(n)`, `P = Θ(lg n)`; below the cutoff the cost is a constant absorbed into the constant).

* `monoEnv T n = max_{m ≤ n} T m`, the monotone envelope (`HeadlineCost` requires monotonicity).
* `StageTerm`: a term `A · V · P^{1-g} · (lg(2P))^j` of the paper's shape, where `V = RP` is the
  volume and `P^{1-g} (lg(2P))^j` a normalized cost with gap `g` (Table 5 (`tab:cost-walsh`)).
* `realBound_of_stageTerms` (any `0 ≤ κ ≤ 1`): if, above a cutoff, `T n` is at most a finite sum of
  stage terms with gaps `g > κ` plus `B·n`, with `0 ≤ V n ≤ c_V n` and `2 ≤ P n ≤ c_P ⌊log₂ n⌋`,
  then `T n ≤ C n ⌊log₂ n⌋^{1-κ}` above a cutoff.
* `headlineCost_monoEnv_of_realBound`: at `κ = 2^{-46}` such a real bound gives
  `HeadlineCost (monoEnv T) C N` for natural `C, N` (the `2^46`-th power form of the challenge).
* `headlineCost_of_stageTerms`: the composition (the abstract cost theorem).

`V` and `P` are arbitrary real functions here; `Walsh46.lean` instantiates them with `V = RP`,
`P = P` of `Params.lean` and discharges the hypotheses with Lemma 7.1 (`Asymptotics.lean`).

Theorems tagged CONTRACT are the contract statements; all of them are proved in this file.
-/

namespace SubNLogN.Math.Cost

open SubNLogN.S5 (HeadlineCost)

/-! ## The monotone envelope -/

/-- The monotone envelope `monoEnv T n = max_{m ≤ n} T m`. -/
def monoEnv (T : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup T

/-- CONTRACT: the monotone envelope is monotone. -/
theorem monoEnv_mono (T : ℕ → ℕ) : Monotone (monoEnv T) := by
  intro a b hab
  exact Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hab))

/-- CONTRACT: `T n ≤ monoEnv T n`. -/
theorem le_monoEnv (T : ℕ → ℕ) (n : ℕ) : T n ≤ monoEnv T n :=
  Finset.le_sup (Finset.self_mem_range_succ n)

/-- CONTRACT: `monoEnv T n ≤ a ↔ ∀ m ≤ n, T m ≤ a`. -/
theorem monoEnv_le_iff (T : ℕ → ℕ) (n a : ℕ) : monoEnv T n ≤ a ↔ ∀ m ≤ n, T m ≤ a := by
  unfold monoEnv
  rw [Finset.sup_le_iff]
  simp [Finset.mem_range]

/-- CONTRACT: a monotone function is its own envelope. -/
theorem monoEnv_eq_of_monotone {T : ℕ → ℕ} (hT : Monotone T) : monoEnv T = T := by
  funext n
  apply le_antisymm
  · exact (monoEnv_le_iff T n (T n)).2 (fun m hm => hT hm)
  · exact le_monoEnv T n

/-! ## Stage terms -/

/-- A stage term of the paper's shape `A · V · P^{1-g} · (lg(2P))^j` (Table 5 (`tab:cost-walsh`) and Section 7.6 (`sec:main-thm`)):
`A` a constant, `g` the gap below `P^1`, `j` the power of `lg(2P)`. -/
structure StageTerm where
  /-- the constant `A` -/
  A : ℝ
  /-- the gap `g` -/
  g : ℝ
  /-- the power `j` of `lg(2P)` -/
  j : ℕ

/-- Value `A · V · P^{1-g} · (lg(2P))^j` of a stage term at volume `V` and precision `P`
(`lg = Real.logb 2`, real power `P^{1-g}`). -/
noncomputable def StageTerm.eval (s : StageTerm) (V P : ℝ) : ℝ :=
  s.A * V * P ^ (1 - s.g) * Real.logb 2 (2 * P) ^ s.j

/-- Sum of a finite list of stage terms at `(V, P)`. -/
noncomputable def stageSum (terms : List StageTerm) (V P : ℝ) : ℝ :=
  (terms.map fun s => s.eval V P).sum

@[simp] theorem stageSum_nil (V P : ℝ) : stageSum [] V P = 0 := rfl

@[simp] theorem stageSum_cons (s : StageTerm) (terms : List StageTerm) (V P : ℝ) :
    stageSum (s :: terms) V P = s.eval V P + stageSum terms V P := by
  simp [stageSum]

/-! ## The abstract cost theorem -/

/-- CONTRACT (real form of the cost conclusion; Section 7.4 (`sec:main-gaps`) and Section 7.6 (`sec:main-thm`)).
Let `0 ≤ κ ≤ 1`. Suppose that for all `n ≥ N₀`: `0 ≤ V n ≤ c_V · n`, `2 ≤ P n ≤ c_P · ⌊log₂ n⌋`,
and `T n ≤ Σ_{s ∈ terms} s.A · V n · (P n)^{1 - s.g} · (lg(2 P n))^{s.j} + B · n`, where every
term has gap `s.g > κ`. Then there is a real `C` with `T n ≤ C · n · ⌊log₂ n⌋^{1-κ}` for all
`n ≥ max N₀ 2` (real power). -/
theorem realBound_of_stageTerms {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (T : ℕ → ℕ) (V P : ℕ → ℝ) (terms : List StageTerm) (cV cP B : ℝ) (N₀ : ℕ)
    (hgap : ∀ s ∈ terms, κ < s.g)
    (hV : ∀ n ≥ N₀, 0 ≤ V n ∧ V n ≤ cV * n)
    (hP : ∀ n ≥ N₀, 2 ≤ P n ∧ P n ≤ cP * (Nat.log2 n : ℝ))
    (hT : ∀ n ≥ N₀, (T n : ℝ) ≤ stageSum terms (V n) (P n) + B * n) :
    ∃ C : ℝ, ∀ n ≥ max N₀ 2, (T n : ℝ) ≤ C * n * (Nat.log2 n : ℝ) ^ (1 - κ) := by
  have _hκ0' : 0 ≤ κ := hκ0
  set K : StageTerm → ℝ := fun s => |s.A| * |cV| * (Nat.factorial s.j : ℝ) *
    (4 / (s.g - κ)) ^ s.j * |cP| ^ (1 - κ) with hK
  refine ⟨(terms.map K).sum + |B|, fun n hn => ?_⟩
  have hnN : N₀ ≤ n := le_of_max_le_left hn
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  obtain ⟨hV0, hV1⟩ := hV n hnN
  obtain ⟨hP2, hP1⟩ := hP n hnN
  have hlog1 : (1 : ℝ) ≤ Nat.log2 n := by
    have : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).2 (by simpa using hn2)
    exact_mod_cast this
  have hκ1' : 0 ≤ 1 - κ := by linarith
  set L : ℝ := (Nat.log2 n : ℝ) ^ (1 - κ) with hL
  have hL1 : 1 ≤ L := Real.one_le_rpow hlog1 hκ1'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hterm : ∀ s ∈ terms, s.eval (V n) (P n) ≤ K s * (n * L) := by
    intro s hs
    have hgs := hgap s hs
    have hP0 : 0 < P n := by linarith
    have hlogb : 0 ≤ Real.logb 2 (2 * P n) := Real.logb_nonneg (by norm_num) (by linarith)
    have habs := rpow_mul_logb_pow_le hP2 hgs s.j
    have hPle : P n ≤ |cP| * Nat.log2 n :=
      le_trans hP1 (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hPk : P n ^ (1 - κ) ≤ |cP| ^ (1 - κ) * L := by
      rw [hL, ← Real.mul_rpow (abs_nonneg _) (by positivity)]
      exact Real.rpow_le_rpow hP0.le hPle hκ1'
    have hVle : V n ≤ |cV| * n :=
      le_trans hV1 (mul_le_mul_of_nonneg_right (le_abs_self _) hn0.le)
    have hsg : 0 < s.g - κ := sub_pos.2 hgs
    have hX0 : 0 ≤ P n ^ (1 - s.g) * Real.logb 2 (2 * P n) ^ s.j := by positivity
    unfold StageTerm.eval
    calc s.A * V n * P n ^ (1 - s.g) * Real.logb 2 (2 * P n) ^ s.j
        = (s.A * V n) * (P n ^ (1 - s.g) * Real.logb 2 (2 * P n) ^ s.j) := by ring
      _ ≤ (|s.A| * (|cV| * n)) *
            ((Nat.factorial s.j : ℝ) * (4 / (s.g - κ)) ^ s.j * (|cP| ^ (1 - κ) * L)) := by
          apply mul_le_mul _ _ hX0 (by positivity)
          · calc s.A * V n ≤ |s.A| * V n := mul_le_mul_of_nonneg_right (le_abs_self _) hV0
              _ ≤ |s.A| * (|cV| * n) := mul_le_mul_of_nonneg_left hVle (abs_nonneg _)
          · calc P n ^ (1 - s.g) * Real.logb 2 (2 * P n) ^ s.j
                ≤ (Nat.factorial s.j : ℝ) * (4 / (s.g - κ)) ^ s.j * P n ^ (1 - κ) := habs
              _ ≤ (Nat.factorial s.j : ℝ) * (4 / (s.g - κ)) ^ s.j * (|cP| ^ (1 - κ) * L) := by
                  apply mul_le_mul_of_nonneg_left hPk
                  positivity
      _ = K s * (n * L) := by simp only [hK]; ring
  have hsum : stageSum terms (V n) (P n) ≤ (terms.map K).sum * (n * L) := by
    unfold stageSum
    calc (terms.map fun s => s.eval (V n) (P n)).sum
        ≤ (terms.map fun s => K s * (n * L)).sum := List.sum_le_sum (fun s hs => hterm s hs)
      _ = (terms.map K).sum * (n * L) := List.sum_map_mul_right ..
  have hB : B * n ≤ |B| * n * L := by
    have h1 : B * n ≤ |B| * n := mul_le_mul_of_nonneg_right (le_abs_self _) hn0.le
    have h2 : |B| * n ≤ |B| * n * L := le_mul_of_one_le_right (by positivity) hL1
    linarith
  calc (T n : ℝ) ≤ stageSum terms (V n) (P n) + B * n := hT n hnN
    _ ≤ (terms.map K).sum * (n * L) + |B| * n * L := add_le_add hsum hB
    _ = ((terms.map K).sum + |B|) * n * L := by ring

/-- CONTRACT (conversion to the headline shape; Section 7.6 (`sec:main-thm`), proof of Theorem 1 (`thm:main`), "below `n_*` ... absorbed after
enlarging the implied constant"). If `T n ≤ C · n · ⌊log₂ n⌋^{1 - 2^{-46}}` (real `C`, real
power) for all `n ≥ N`, then for some natural `C', N'` the monotone envelope satisfies
`HeadlineCost (monoEnv T) C' N'`, i.e. it is monotone, `0 < C'`, `2 ≤ N'`, and
`(monoEnv T n + 1)^{2^46} ≤ (C' n)^{2^46} (log₂ n)^{2^46 - 1}` for `n ≥ N'`. -/
theorem headlineCost_monoEnv_of_realBound (T : ℕ → ℕ) (C : ℝ) (N : ℕ)
    (h : ∀ n ≥ N, (T n : ℝ) ≤ C * n * (Nat.log2 n : ℝ) ^ (1 - ((2 : ℝ) ^ 46)⁻¹)) :
    ∃ C' N' : ℕ, HeadlineCost (monoEnv T) C' N' := by
  set κ : ℝ := ((2 : ℝ) ^ 46)⁻¹ with hκ
  have hκ1 : 0 ≤ 1 - κ := by rw [hκ]; norm_num
  set N1 : ℕ := max N 2 with hN1
  set M0 : ℝ := (monoEnv T N1 : ℝ) with hM0
  have hM0' : 0 ≤ M0 := by rw [hM0]; positivity
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  refine ⟨⌈M0 + 1 + Cp⌉₊, N1, monoEnv_mono T, Nat.ceil_pos.2 (by positivity),
    le_max_right _ _, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hlog1n : 1 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).2 (by simpa using hn2)
  have hlog1 : (1 : ℝ) ≤ Nat.log2 n := by exact_mod_cast hlog1n
  set L : ℝ := (Nat.log2 n : ℝ) ^ (1 - κ) with hL
  have hL1 : 1 ≤ L := Real.one_le_rpow hlog1 hκ1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hbound : ∀ m ≤ n, (T m : ℝ) ≤ M0 + Cp * n * L := by
    intro m hm
    by_cases hmN : m ≤ N1
    · have h1 : T m ≤ monoEnv T N1 := (monoEnv_le_iff T N1 _).1 le_rfl m hmN
      have h1' : (T m : ℝ) ≤ M0 := by rw [hM0]; exact_mod_cast h1
      have h0 : 0 ≤ Cp * n * L := by positivity
      linarith
    · have hmN' : N ≤ m := le_trans (le_max_left _ _) (not_le.1 hmN).le
      have h1 := h m hmN'
      have hlogm : (Nat.log2 m : ℝ) ≤ Nat.log2 n := by
        exact_mod_cast SubNLogN.S5.headlineCost_log2_mono hm
      have hlogm0 : (0 : ℝ) ≤ Nat.log2 m := by positivity
      have hLm : (Nat.log2 m : ℝ) ^ (1 - κ) ≤ L := Real.rpow_le_rpow hlogm0 hlogm hκ1
      have hLm0 : 0 ≤ (Nat.log2 m : ℝ) ^ (1 - κ) := Real.rpow_nonneg hlogm0 _
      have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have h2 : C * m * (Nat.log2 m : ℝ) ^ (1 - κ) ≤ Cp * n * L := by
        calc C * m * (Nat.log2 m : ℝ) ^ (1 - κ) ≤ Cp * m * (Nat.log2 m : ℝ) ^ (1 - κ) := by
              apply mul_le_mul_of_nonneg_right _ hLm0
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
          _ ≤ Cp * n * L := by
              apply mul_le_mul _ hLm hLm0 (by positivity)
              exact mul_le_mul_of_nonneg_left hmn hCp0
      linarith
  have henv : (monoEnv T n : ℝ) ≤ M0 + Cp * n * L := by
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup (Finset.range (n + 1)) ⟨0, by simp⟩ T
    have hme : monoEnv T n = T m := hmeq
    rw [hme]
    exact hbound m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))
  have hnL : 1 ≤ (n : ℝ) * L := one_le_mul_of_one_le_of_one_le hn1 hL1
  have hfinal : ((monoEnv T n + 1 : ℕ) : ℝ) ≤ (⌈M0 + 1 + Cp⌉₊ : ℝ) * n * L := by
    have hc : M0 + 1 + Cp ≤ (⌈M0 + 1 + Cp⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    have hM1 := mul_le_mul_of_nonneg_left hnL (by positivity : (0 : ℝ) ≤ M0 + 1)
    calc (monoEnv T n : ℝ) + 1 ≤ M0 + Cp * n * L + 1 := by linarith
      _ ≤ (M0 + 1) * (n * L) + Cp * (n * L) := by nlinarith
      _ = (M0 + 1 + Cp) * n * L := by ring
      _ ≤ (⌈M0 + 1 + Cp⌉₊ : ℝ) * n * L := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
          positivity
  have hLpow : L ^ (2 ^ 46 : ℕ) = (Nat.log2 n : ℝ) ^ (2 ^ 46 - 1 : ℕ) := by
    rw [hL, ← Real.rpow_natCast ((Nat.log2 n : ℝ) ^ (1 - κ)), ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast (Nat.log2 n : ℝ)]
    congr 1
    rw [hκ, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    norm_num
  have hpow := pow_le_pow_left₀ (by positivity) hfinal (2 ^ 46)
  rw [mul_pow, hLpow] at hpow
  exact_mod_cast hpow

/-- CONTRACT (the abstract cost theorem, `κ = 2^{-46}`; Section 7.4 (`sec:main-gaps`) and Section 7.6 (`sec:main-thm`)).
Suppose that for all `n ≥ N₀`: `0 ≤ V n ≤ c_V · n`, `2 ≤ P n ≤ c_P · ⌊log₂ n⌋`, and
`T n ≤ Σ_{s ∈ terms} s.A · V n · (P n)^{1 - s.g} · (lg(2 P n))^{s.j} + B · n`, where every term has
gap `s.g > 2^{-46}`. Then `HeadlineCost (monoEnv T) C N` for some natural `C, N`. -/
theorem headlineCost_of_stageTerms (T : ℕ → ℕ) (V P : ℕ → ℝ) (terms : List StageTerm)
    (cV cP B : ℝ) (N₀ : ℕ)
    (hgap : ∀ s ∈ terms, ((2 : ℝ) ^ 46)⁻¹ < s.g)
    (hV : ∀ n ≥ N₀, 0 ≤ V n ∧ V n ≤ cV * n)
    (hP : ∀ n ≥ N₀, 2 ≤ P n ∧ P n ≤ cP * (Nat.log2 n : ℝ))
    (hT : ∀ n ≥ N₀, (T n : ℝ) ≤ stageSum terms (V n) (P n) + B * n) :
    ∃ C N : ℕ, HeadlineCost (monoEnv T) C N := by
  obtain ⟨C, hC⟩ := realBound_of_stageTerms (κ := ((2 : ℝ) ^ 46)⁻¹) (by positivity)
    (by norm_num) T V P terms cV cP B N₀ hgap hV hP hT
  exact headlineCost_monoEnv_of_realBound T C (max N₀ 2) hC

end SubNLogN.Math.Cost
