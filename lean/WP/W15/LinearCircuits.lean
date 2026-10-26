import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Fintype.Card
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W15.LinearCircuits: bounded-coefficient linear circuits and Morgenstern's determinant bound

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every result in this file holds only in the
restricted model defined explicitly below.

**Model (b): fan-in-2 linear straight-line programs** (`LinSLP 𝕜 n`) over a normed field `𝕜`
(e.g. `ℂ`). The `n` inputs are the unit linear forms `e₀, …, e_{n-1}`. Gate `t` computes
`α • v a + β • v b` from two earlier values (a reference past the end reads the zero form); fan-out
is unbounded. A program *computes* a matrix `A` if every row of `A` is one of its values. Only exact
linear computation is modelled: no rounding, no bit operations, no table lookup. Gates are counted;
nothing here is a bit-operation count.

**What is proved.**
* `LinSLP.norm_det_le_weight` (Morgenstern 1973's determinant argument): if `P` computes a square
  `A`, then `‖det A‖ ≤ ∏_gates max(1, ‖α‖ + ‖β‖)`. Sign flips and other one-input gates of modulus
  `≤ 1` contribute a factor `1`.
* `LinSLP.norm_det_le_two_pow`: with all coefficients of modulus `≤ 1`,
  `‖det A‖ ≤ 2^(number of genuinely two-input gates)`.
* `LinSLP.exists_computes` (non-vacuity): every matrix with entries of modulus `≤ 1` is computed by
  some program with coefficients of modulus `≤ 1`.
-/

namespace WP.W15

open scoped BigOperators

/-! ## The model -/

/-- A fan-in-2 linear gate: the value `α • v a + β • v b`. -/
structure LinGate (𝕜 : Type*) where
  a : ℕ
  b : ℕ
  α : 𝕜
  β : 𝕜

/-- A fan-in-2 linear straight-line program on `n` inputs. -/
structure LinSLP (𝕜 : Type*) (n : ℕ) where
  gates : List (LinGate 𝕜)

section Defs

variable {𝕜 : Type*} [Ring 𝕜] {n : ℕ}

/-- The linear form computed by gate `g` from the forms `acc` computed so far. -/
def LinGate.row (g : LinGate 𝕜) (acc : List (Fin n → 𝕜)) : Fin n → 𝕜 :=
  g.α • acc.getD g.a 0 + g.β • acc.getD g.b 0

/-- One evaluation step: append the gate's linear form. -/
def stepRows (acc : List (Fin n → 𝕜)) (g : LinGate 𝕜) : List (Fin n → 𝕜) :=
  acc ++ [g.row acc]

/-- The input forms `e₀, …, e_{n-1}`. -/
def inputRows (n : ℕ) : List (Fin n → 𝕜) := List.ofFn fun i : Fin n => Pi.single i 1

/-- All values (linear forms) of a program: the inputs followed by one form per gate. -/
def LinSLP.rows (P : LinSLP 𝕜 n) : List (Fin n → 𝕜) := P.gates.foldl stepRows (inputRows n)

/-- `P` computes `A` if every row of `A` is a value of `P`. -/
def LinSLP.Computes {m : ℕ} (P : LinSLP 𝕜 n) (A : Matrix (Fin m) (Fin n) 𝕜) : Prop :=
  ∀ i, A i ∈ P.rows

/-- Append one gate. -/
def LinSLP.append (P : LinSLP 𝕜 n) (g : LinGate 𝕜) : LinSLP 𝕜 n := ⟨P.gates ++ [g]⟩

theorem LinSLP.rows_append (P : LinSLP 𝕜 n) (g : LinGate 𝕜) :
    (P.append g).rows = P.rows ++ [g.row P.rows] := by
  simp [LinSLP.append, LinSLP.rows, List.foldl_append, stepRows]

end Defs

section Norm

variable {𝕜 : Type*} [NormedField 𝕜] {n : ℕ}

/-- Morgenstern weight of a gate. -/
noncomputable def LinGate.weight (g : LinGate 𝕜) : ℝ := max 1 (‖g.α‖ + ‖g.β‖)

/-- Morgenstern weight of a program: the product of its gate weights. -/
noncomputable def LinSLP.weight (P : LinSLP 𝕜 n) : ℝ := (P.gates.map LinGate.weight).prod

/-- All gate coefficients have modulus at most `1`. -/
def LinSLP.CoeffsLeOne (P : LinSLP 𝕜 n) : Prop := ∀ g ∈ P.gates, ‖g.α‖ ≤ 1 ∧ ‖g.β‖ ≤ 1

/-- Whether a gate genuinely has two inputs (both coefficients nonzero). -/
noncomputable def LinGate.isTwoInput (g : LinGate 𝕜) : Bool :=
  @decide (g.α ≠ 0 ∧ g.β ≠ 0) (Classical.propDecidable _)

/-- The number of genuinely two-input gates. -/
noncomputable def LinSLP.twoInputGates (P : LinSLP 𝕜 n) : ℕ := P.gates.countP LinGate.isTwoInput

theorem LinGate.isTwoInput_iff (g : LinGate 𝕜) : g.isTwoInput = true ↔ g.α ≠ 0 ∧ g.β ≠ 0 := by
  unfold LinGate.isTwoInput
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem LinGate.one_le_weight (g : LinGate 𝕜) : 1 ≤ g.weight := le_max_left _ _

/-! ## Morgenstern's minor bound -/

/-- Every `n × n` matrix whose rows lie in `R` has determinant of norm at most `W`. -/
def MinorBound (R : Set (Fin n → 𝕜)) (W : ℝ) : Prop :=
  ∀ M : Matrix (Fin n) (Fin n) 𝕜, (∀ i, M i ∈ R) → ‖M.det‖ ≤ W

/-- Base case: rows that are zero or unit vectors give determinants of norm at most `1`. -/
theorem minorBound_base :
    MinorBound {v : Fin n → 𝕜 | v = 0 ∨ ∃ i, v = Pi.single i 1} 1 := by
  classical
  intro M hM
  by_cases hz : ∃ i, M i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Matrix.det_eq_zero_of_row_eq_zero i (fun j => by rw [hi]; rfl), norm_zero]
    exact zero_le_one
  · push_neg at hz
    have hsel : ∀ i, ∃ t, M i = Pi.single t 1 := fun i => (hM i).resolve_left (hz i)
    choose τ hτ using hsel
    by_cases hinj : Function.Injective τ
    · have hbij : Function.Bijective τ := Finite.injective_iff_bijective.mp hinj
      have hMσ : M = (1 : Matrix (Fin n) (Fin n) 𝕜).submatrix (Equiv.ofBijective τ hbij) id := by
        ext i j
        rw [hτ i, Matrix.submatrix_apply, Equiv.ofBijective_apply, id, Matrix.one_apply,
          Pi.single_apply]
        by_cases h : j = τ i
        · simp [h]
        · simp [h, Ne.symm h]
      rw [hMσ, Matrix.det_permute, Matrix.det_one, mul_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective τ hbij)) with h | h <;>
        simp [h]
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hij, hne⟩ := hinj
      rw [Matrix.det_zero_of_row_eq hne (by rw [hτ i, hτ j, hij]), norm_zero]
      exact zero_le_one

/-- Inductive step: adding the row `α • u + β • v` (with `u, v ∈ R`) multiplies the bound by
`max 1 (‖α‖ + ‖β‖)`. -/
theorem MinorBound.insert {R : Set (Fin n → 𝕜)} {W : ℝ} (hW : 0 ≤ W) (h : MinorBound R W)
    {u v : Fin n → 𝕜} (hu : u ∈ R) (hv : v ∈ R) (α β : 𝕜) :
    MinorBound (insert (α • u + β • v) R) (max 1 (‖α‖ + ‖β‖) * W) := by
  classical
  intro M hM
  have hmax0 : 0 ≤ max 1 (‖α‖ + ‖β‖) := le_trans zero_le_one (le_max_left _ _)
  have hmaxW : W ≤ max 1 (‖α‖ + ‖β‖) * W := le_mul_of_one_le_left hW (le_max_left _ _)
  by_cases hex : ∃ i0, M i0 = α • u + β • v
  · obtain ⟨i0, hi0⟩ := hex
    by_cases hdup : ∃ i1, i1 ≠ i0 ∧ M i1 = α • u + β • v
    · obtain ⟨i1, hne, hi1⟩ := hdup
      rw [Matrix.det_zero_of_row_eq hne (hi1.trans hi0.symm), norm_zero]
      exact mul_nonneg hmax0 hW
    · push_neg at hdup
      have hrest : ∀ i, i ≠ i0 → M i ∈ R := by
        intro i hi
        rcases (Set.mem_insert_iff.mp (hM i)) with h1 | h1
        · exact absurd h1 (hdup i hi)
        · exact h1
      have hMu : ∀ i, Matrix.updateRow M i0 u i ∈ R := by
        intro i
        by_cases hi : i = i0
        · subst hi
          rw [Matrix.updateRow_self]
          exact hu
        · rw [Matrix.updateRow_ne hi]
          exact hrest i hi
      have hMv : ∀ i, Matrix.updateRow M i0 v i ∈ R := by
        intro i
        by_cases hi : i = i0
        · subst hi
          rw [Matrix.updateRow_self]
          exact hv
        · rw [Matrix.updateRow_ne hi]
          exact hrest i hi
      have hdet : M.det =
          α * (Matrix.updateRow M i0 u).det + β * (Matrix.updateRow M i0 v).det := by
        calc M.det = (Matrix.updateRow M i0 (α • u + β • v)).det := by
              rw [← hi0, Matrix.updateRow_eq_self]
          _ = α * (Matrix.updateRow M i0 u).det + β * (Matrix.updateRow M i0 v).det := by
              rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]
      rw [hdet]
      calc ‖α * (Matrix.updateRow M i0 u).det + β * (Matrix.updateRow M i0 v).det‖
          ≤ ‖α‖ * ‖(Matrix.updateRow M i0 u).det‖ + ‖β‖ * ‖(Matrix.updateRow M i0 v).det‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ ‖α‖ * W + ‖β‖ * W := by
            gcongr
            · exact h _ hMu
            · exact h _ hMv
        _ = (‖α‖ + ‖β‖) * W := by ring
        _ ≤ max 1 (‖α‖ + ‖β‖) * W := mul_le_mul_of_nonneg_right (le_max_right _ _) hW
  · push_neg at hex
    have hall : ∀ i, M i ∈ R := fun i => (Set.mem_insert_iff.mp (hM i)).resolve_left (hex i)
    exact (h M hall).trans hmaxW

theorem getD_mem_zeroOr (acc : List (Fin n → 𝕜)) (k : ℕ) :
    acc.getD k 0 ∈ {v : Fin n → 𝕜 | v = 0 ∨ v ∈ acc} := by
  by_cases hk : k < acc.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact Or.inr (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inl rfl

theorem foldl_minorBound (gates : List (LinGate 𝕜)) :
    ∀ (acc : List (Fin n → 𝕜)) (W : ℝ), 1 ≤ W → MinorBound {v | v = 0 ∨ v ∈ acc} W →
      MinorBound {v | v = 0 ∨ v ∈ gates.foldl stepRows acc} ((gates.map LinGate.weight).prod * W) := by
  induction gates with
  | nil =>
    intro acc W _ h
    simpa using h
  | cons g gs ih =>
    intro acc W hW h
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have hset : {v : Fin n → 𝕜 | v = 0 ∨ v ∈ stepRows acc g} =
        insert (g.row acc) {v | v = 0 ∨ v ∈ acc} := by
      ext v
      simp only [stepRows, List.mem_append, List.mem_singleton, Set.mem_setOf_eq,
        Set.mem_insert_iff]
      tauto
    have hstep : MinorBound {v | v = 0 ∨ v ∈ stepRows acc g} (g.weight * W) := by
      rw [hset]
      exact MinorBound.insert (by linarith) h (getD_mem_zeroOr acc g.a) (getD_mem_zeroOr acc g.b)
        g.α g.β
    have hW' : 1 ≤ g.weight * W := one_le_mul_of_one_le_of_one_le g.one_le_weight hW
    have key := ih (stepRows acc g) (g.weight * W) hW' hstep
    have e : (gs.map LinGate.weight).prod * (g.weight * W) =
        g.weight * (gs.map LinGate.weight).prod * W := by ring
    rw [e] at key
    exact key

/-- **Morgenstern's determinant bound.** If `P` computes the square matrix `A`, then
`‖det A‖ ≤ weight P = ∏ max(1, ‖α‖ + ‖β‖)`. -/
theorem LinSLP.norm_det_le_weight (P : LinSLP 𝕜 n) {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : P.Computes A) : ‖A.det‖ ≤ P.weight := by
  have h0 : MinorBound {v : Fin n → 𝕜 | v = 0 ∨ v ∈ (inputRows n : List (Fin n → 𝕜))} 1 := by
    have hset : {v : Fin n → 𝕜 | v = 0 ∨ v ∈ (inputRows n : List (Fin n → 𝕜))} =
        {v | v = 0 ∨ ∃ i, v = Pi.single i 1} := by
      ext v
      simp only [inputRows, Set.mem_setOf_eq, List.mem_ofFn', Set.mem_range]
      constructor <;> rintro (h | ⟨i, hi⟩) <;> first | exact Or.inl h | exact Or.inr ⟨i, hi.symm⟩
    rw [hset]
    exact minorBound_base
  have h := foldl_minorBound P.gates (inputRows n) 1 le_rfl h0
  rw [mul_one] at h
  exact h A (fun i => Or.inr (hA i))

theorem prod_weight_le_two_pow (gs : List (LinGate 𝕜))
    (h : ∀ g ∈ gs, ‖g.α‖ ≤ 1 ∧ ‖g.β‖ ≤ 1) :
    (gs.map LinGate.weight).prod ≤ 2 ^ gs.countP LinGate.isTwoInput := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.map_cons, List.prod_cons, List.countP_cons]
    have hg := h g (by simp)
    have hrest := ih (fun g' hg' => h g' (by simp [hg']))
    have hprod0 : 0 ≤ (gs.map LinGate.weight).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨g', _, rfl⟩ := List.mem_map.mp hx
      exact le_trans zero_le_one g'.one_le_weight
    have hwg : g.weight ≤ if g.isTwoInput then 2 else 1 := by
      unfold LinGate.weight
      by_cases ht : g.isTwoInput = true
      · rw [if_pos ht]
        exact max_le (by norm_num) (by linarith [hg.1, hg.2])
      · rw [if_neg ht]
        rw [LinGate.isTwoInput_iff] at ht
        push_neg at ht
        apply max_le le_rfl
        by_cases hα : g.α = 0
        · rw [hα, norm_zero, zero_add]
          exact hg.2
        · rw [ht hα, norm_zero, add_zero]
          exact hg.1
    calc g.weight * (gs.map LinGate.weight).prod
        ≤ (if g.isTwoInput then 2 else 1) * 2 ^ gs.countP LinGate.isTwoInput :=
          mul_le_mul hwg hrest hprod0 (by split_ifs <;> norm_num)
      _ = 2 ^ (gs.countP LinGate.isTwoInput + if g.isTwoInput then 1 else 0) := by
          split_ifs <;> simp [pow_succ, mul_comm]

theorem LinSLP.weight_le_two_pow (P : LinSLP 𝕜 n) (hP : P.CoeffsLeOne) :
    P.weight ≤ 2 ^ P.twoInputGates :=
  prod_weight_le_two_pow P.gates hP

/-- **Morgenstern, unit-coefficient form.** With all coefficients of modulus `≤ 1`,
`‖det A‖ ≤ 2^(number of two-input gates)`. -/
theorem LinSLP.norm_det_le_two_pow (P : LinSLP 𝕜 n) (hP : P.CoeffsLeOne)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : P.Computes A) : ‖A.det‖ ≤ 2 ^ P.twoInputGates :=
  (P.norm_det_le_weight hA).trans (P.weight_le_two_pow hP)

/-! ## Non-vacuity: every matrix with entries of modulus `≤ 1` is computable -/

/-- `Q` extends `P` by gates whose coefficients have modulus `≤ 1`. -/
def LinSLP.ExtendsLeOne (P Q : LinSLP 𝕜 n) : Prop :=
  ∃ gs : List (LinGate 𝕜), Q.gates = P.gates ++ gs ∧ ∀ g ∈ gs, ‖g.α‖ ≤ 1 ∧ ‖g.β‖ ≤ 1

theorem LinSLP.ExtendsLeOne.refl (P : LinSLP 𝕜 n) : P.ExtendsLeOne P :=
  ⟨[], by simp, by simp⟩

theorem LinSLP.ExtendsLeOne.trans {P Q R : LinSLP 𝕜 n} (h1 : P.ExtendsLeOne Q)
    (h2 : Q.ExtendsLeOne R) : P.ExtendsLeOne R := by
  obtain ⟨gs1, e1, c1⟩ := h1
  obtain ⟨gs2, e2, c2⟩ := h2
  refine ⟨gs1 ++ gs2, by rw [e2, e1, List.append_assoc], ?_⟩
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact c1 g hg
  · exact c2 g hg

theorem foldl_stepRows_prefix (gs : List (LinGate 𝕜)) (acc : List (Fin n → 𝕜)) :
    acc <+: gs.foldl stepRows acc := by
  induction gs generalizing acc with
  | nil => exact List.prefix_refl _
  | cons g gs ih =>
    rw [List.foldl_cons]
    exact (List.prefix_append acc [g.row acc]).trans (ih _)

theorem LinSLP.ExtendsLeOne.rows_prefix {P Q : LinSLP 𝕜 n} (h : P.ExtendsLeOne Q) :
    P.rows <+: Q.rows := by
  obtain ⟨gs, e, _⟩ := h
  unfold LinSLP.rows
  rw [e, List.foldl_append]
  exact foldl_stepRows_prefix gs _

theorem LinSLP.ExtendsLeOne.coeffs {P Q : LinSLP 𝕜 n} (h : P.ExtendsLeOne Q)
    (hP : P.CoeffsLeOne) : Q.CoeffsLeOne := by
  obtain ⟨gs, e, c⟩ := h
  intro g hg
  rw [e] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hP g hg
  · exact c g hg

theorem exists_getD_eq (acc : List (Fin n → 𝕜)) (w : Fin n → 𝕜) (hw : w = 0 ∨ w ∈ acc) :
    ∃ k, acc.getD k 0 = w := by
  rcases hw with rfl | hw
  · exact ⟨acc.length, List.getD_eq_default _ _ le_rfl⟩
  · obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
    exact ⟨k, by rw [List.getD_eq_getElem _ _ hk, hkw]⟩

/-- One more gate computes `α • u + β • v` from computable `u`, `v`. -/
theorem LinSLP.extend_one (P : LinSLP 𝕜 n) {u v : Fin n → 𝕜} (hu : u = 0 ∨ u ∈ P.rows)
    (hv : v = 0 ∨ v ∈ P.rows) (α β : 𝕜) (hα : ‖α‖ ≤ 1) (hβ : ‖β‖ ≤ 1) :
    ∃ Q : LinSLP 𝕜 n, P.ExtendsLeOne Q ∧ α • u + β • v ∈ Q.rows := by
  obtain ⟨ka, hka⟩ := exists_getD_eq P.rows u hu
  obtain ⟨kb, hkb⟩ := exists_getD_eq P.rows v hv
  refine ⟨P.append ⟨ka, kb, α, β⟩, ⟨[⟨ka, kb, α, β⟩], rfl, ?_⟩, ?_⟩
  · intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact ⟨hα, hβ⟩
  · rw [LinSLP.rows_append]
    unfold LinGate.row
    rw [hka, hkb]
    simp

theorem inputRows_mem_rows (P : LinSLP 𝕜 n) (i : Fin n) :
    (Pi.single i 1 : Fin n → 𝕜) ∈ P.rows := by
  apply (foldl_stepRows_prefix P.gates (inputRows n)).subset
  simp only [inputRows, List.mem_ofFn', Set.mem_range]
  exact ⟨i, rfl⟩

/-- Partial sums `∑_{j < t} c j • e j` of a target form `c`. -/
def psum (c : Fin n → 𝕜) (t : ℕ) : Fin n → 𝕜 := fun j => if (j : ℕ) < t then c j else 0

theorem psum_zero (c : Fin n → 𝕜) : psum c 0 = 0 := by
  funext j
  simp [psum]

theorem psum_full (c : Fin n → 𝕜) : psum c n = c := by
  funext j
  simp [psum, j.isLt]

theorem psum_succ (c : Fin n → 𝕜) (t : ℕ) (ht : t < n) :
    psum c (t + 1) =
      (1 : 𝕜) • psum c t + c ⟨t, ht⟩ • (Pi.single (⟨t, ht⟩ : Fin n) (1 : 𝕜) : Fin n → 𝕜) := by
  funext j
  simp only [psum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, Pi.single_apply]
  by_cases h1 : (j : ℕ) < t
  · have h2 : j ≠ ⟨t, ht⟩ := fun h => by
      rw [h] at h1
      exact lt_irrefl _ h1
    have h3 : (j : ℕ) < t + 1 := by omega
    simp [h1, h2, h3]
  · by_cases h3 : (j : ℕ) = t
    · have h4 : j = ⟨t, ht⟩ := Fin.ext h3
      subst h4
      simp
    · have h5 : ¬ (j : ℕ) < t + 1 := by omega
      have h6 : j ≠ ⟨t, ht⟩ := fun h => h3 (by rw [h])
      simp [h1, h5, h6]

theorem exists_extend_psum (P : LinSLP 𝕜 n) (c : Fin n → 𝕜) (hc : ∀ j, ‖c j‖ ≤ 1) :
    ∀ t, t ≤ n → ∃ Q : LinSLP 𝕜 n, P.ExtendsLeOne Q ∧ (psum c t = 0 ∨ psum c t ∈ Q.rows)
  | 0, _ => ⟨P, LinSLP.ExtendsLeOne.refl P, Or.inl (psum_zero c)⟩
  | t + 1, ht => by
      obtain ⟨Q, hPQ, hQ⟩ := exists_extend_psum P c hc t (by omega)
      have he : (Pi.single (⟨t, by omega⟩ : Fin n) 1 : Fin n → 𝕜) = 0 ∨
          (Pi.single (⟨t, by omega⟩ : Fin n) 1 : Fin n → 𝕜) ∈ Q.rows :=
        Or.inr (inputRows_mem_rows Q _)
      obtain ⟨Q', hQQ', hmem⟩ := Q.extend_one hQ he 1 (c ⟨t, by omega⟩) (by simp) (hc _)
      refine ⟨Q', hPQ.trans hQQ', Or.inr ?_⟩
      rw [psum_succ c t (by omega)]
      exact hmem

theorem exists_computes_list (L : List (Fin n → 𝕜)) (hL : ∀ c ∈ L, ∀ j, ‖c j‖ ≤ 1) :
    ∃ P : LinSLP 𝕜 n, P.CoeffsLeOne ∧ ∀ c ∈ L, c ∈ P.rows := by
  induction L with
  | nil => exact ⟨⟨[]⟩, fun g hg => absurd hg (List.not_mem_nil), fun c hc => absurd hc (List.not_mem_nil)⟩
  | cons c L ih =>
    obtain ⟨P, hP, hPL⟩ := ih (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc'))
    obtain ⟨Q, hPQ, hQ⟩ := exists_extend_psum P c (hL c List.mem_cons_self) n le_rfl
    rw [psum_full] at hQ
    obtain ⟨Q', hQQ', hmem⟩ := Q.extend_one hQ (Or.inl rfl) 1 0 (by simp) (by simp)
    refine ⟨Q', (hPQ.trans hQQ').coeffs hP, ?_⟩
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · simpa using hmem
    · exact (hPQ.trans hQQ').rows_prefix.subset (hPL c' hc')

/-- **Non-vacuity of model (b).** Every matrix whose entries have modulus `≤ 1` is computed by a
program whose coefficients have modulus `≤ 1`. -/
theorem LinSLP.exists_computes {m : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ∃ P : LinSLP 𝕜 n, P.CoeffsLeOne ∧ P.Computes A := by
  obtain ⟨P, hP, hPL⟩ := exists_computes_list (List.ofFn A) (by
    intro c hc j
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' A c).mp hc
    exact hA i j)
  exact ⟨P, hP, fun i => hPL (A i) ((List.mem_ofFn' A (A i)).mpr ⟨i, rfl⟩)⟩

end Norm

/-! ## Smoke test (rule 7 analogue: this WP has no machine programs) -/

/-- The 2-point butterfly `(x₀ + x₁, x₀ − x₁)` as a program on two inputs. -/
def butterflyProg : LinSLP ℤ 2 := ⟨[⟨0, 1, 1, 1⟩, ⟨0, 1, 1, -1⟩]⟩

/-- info: [(1, 0), (0, 1), (1, 1), (1, -1)] -/
#guard_msgs in
#eval butterflyProg.rows.map fun v => (v 0, v 1)

#assert_std_axioms minorBound_base MinorBound.insert foldl_minorBound LinSLP.norm_det_le_weight
  prod_weight_le_two_pow LinSLP.weight_le_two_pow LinSLP.norm_det_le_two_pow
  LinSLP.extend_one exists_extend_psum exists_computes_list LinSLP.exists_computes

#assert_std_axioms LinSLP.rows_append LinGate.isTwoInput_iff LinGate.one_le_weight getD_mem_zeroOr
  LinSLP.ExtendsLeOne.refl LinSLP.ExtendsLeOne.trans foldl_stepRows_prefix
  LinSLP.ExtendsLeOne.rows_prefix LinSLP.ExtendsLeOne.coeffs exists_getD_eq inputRows_mem_rows
  psum_zero psum_full psum_succ

end WP.W15
