import SubNLogN.Math.Bridge.LemmaA

/-!
# Bridge: Lemma 4.2 (bridge Lemma A), operator form from the explicit form

Paper: Section 4.2 (`sec:bridge-A`), Lemma 4.2 (`lem:bridge-A`) (operator product `A_2 A_3 ⋯ A_d` in chronological order).
(Identifier names `LemmaA*`/`lemmaA*` reflect an earlier draft (bridge Lemma A), kept for stability.)

Main result: `lemmaA_of : LemmaA_explicitStmt → HasSum_kernelG_shiftStmt → LemmaAStmt`.
The hypothesis `HasSum_kernelG_shiftStmt` (`∑_m G(ξ - m) = 1`) is only used for the absolute
summability of the alias weights `m ↦ G(ξ - m)`.

Notation (0-based Lean axes, Lean axis `i` = paper axis `i+1`): `s_i = aliasStep t i = R/A_{i+1}`
is the weight of frequency digit `i-1`, and `y_i(f) = samplePt t i f = (u_i(f)+1/2)/t_i`.

Proof outline.
* `aliasMatrix_mulVec_hasSum`: `(A_i Z)_f = ∑_{m∈ℤ} G(y_i(f) - m) Z_{(f - m s_i) mod R}`
  (absolutely convergent), from the matrix entries `∑'_m [f - m s_i ≡ f'] G(y_i(f) - m)` by
  exchanging the finite sum over `f'` with the absolutely convergent sum over `m`.
* `encFreq_symm_shiftFin`: subtracting a multiple of `s_i` does not change the frequency digits
  `j ≥ i`, because `∏_{l ≥ j} t_l` divides both `s_i = ∏_{l ≥ i} t_l` and `R`
  (proof of Lemma 4.2 (`lem:bridge-A`): borrows propagate toward `u_1`).
* `ofFn_prod_mulVec_hasSum`: for a monotone family of axes `e : Fin n → Fin d`,
  `(A_{e 0} A_{e 1} ⋯ A_{e (n-1)} Z)_f = ∑_{m∈ℤ^n} ∏_k G(y_{e k}(f) - m_k) Z_{(f - ∑_k m_k s_{e k}) mod R}`,
  by induction on `n`: split `ℤ^{n+1} ≃ ℤ × ℤ^n`; the coefficients of the inner factors are read at
  the shifted frequency `f - m_0 s_{e 0}`, which has the same digits `≥ e 0` as `f`
  (proof of Lemma 4.2 (`lem:bridge-A`)).
* `aliasProd_mulVec_hasSum`: the case `e = (deconvOrder d).get` (axes `1 < 2 < ⋯ < d-1`),
  reindexed by `{i : Fin d // i ≠ 0}`; `aliasProd_mulVec_encFreq` evaluates it at `f = f(u)`
  (for an arbitrary vector `Z`, not only `Z = F_R x`).
* `lemmaA_of`: rewrite `F_t U` by the explicit form and conclude with `aliasProd_mulVec_encFreq`.

All helpers are in the namespace `SubNLogN.Math.Bridge.LemmaAOperatorProof`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators Matrix

variable {d : ℕ}

/-! Helper lemmas live in the namespace `LemmaAOperatorProof` (to avoid clashes with helpers of
the same name in other `Proofs/` files); only `lemmaA_of` is in `SubNLogN.Math.Bridge`. -/

namespace LemmaAOperatorProof

/-! ## Arithmetic of `shiftFin` -/

/-- The value of `shiftFin f n` as an integer: `(f + n) mod R`. -/
theorem shiftFin_val {R : ℕ} (f : Fin R) (n : ℤ) :
    ((shiftFin f n : ℕ) : ℤ) = ((f : ℕ) + n) % (R : ℤ) := by
  have hR : 0 < R := (Nat.zero_le _).trans_lt f.isLt
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hR.ne'))

theorem shiftFin_zero {R : ℕ} (f : Fin R) : shiftFin f 0 = f := by
  apply Fin.ext
  have h := shiftFin_val f 0
  rw [add_zero, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast f.isLt)] at h
  exact_mod_cast h

theorem shiftFin_shiftFin {R : ℕ} (f : Fin R) (a b : ℤ) :
    shiftFin (shiftFin f a) b = shiftFin f (a + b) := by
  apply Fin.ext
  have h1 := shiftFin_val (shiftFin f a) b
  rw [shiftFin_val f a, Int.emod_add_emod, add_assoc, ← shiftFin_val f (a + b)] at h1
  exact_mod_cast h1

/-- Shifting by a multiple of a divisor `Q` of `R` does not change the residue mod `Q`. -/
theorem shiftFin_mod_eq {R Q : ℕ} (hQR : Q ∣ R) (f : Fin R) (n : ℤ) (hn : (Q : ℤ) ∣ n) :
    (shiftFin f n : ℕ) % Q = (f : ℕ) % Q := by
  have key : ((shiftFin f n : ℕ) : ℤ) % (Q : ℤ) = ((f : ℕ) : ℤ) % (Q : ℤ) := by
    rw [shiftFin_val, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr hQR)]
    obtain ⟨c, rfl⟩ := hn
    exact Int.add_mul_emod_self_left _ _ _
  exact_mod_cast key

/-! ## Frequency digits under alias shifts -/

theorem prefixProd_pos {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) (k : ℕ) : 0 < prefixProd t k :=
  Finset.prod_pos fun i _ => ht i

/-- `s_i = R / A_{i+1} = t_i ∏_{l>i} t_l` (Lean axis `i`). -/
theorem aliasStep_eq {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) (i : Fin d) :
    aliasStep t i = t i * suffixProd t i := by
  unfold aliasStep
  rw [← prefixProd_mul_mul_suffixProd t i, mul_assoc]
  exact Nat.mul_div_cancel_left _ (prefixProd_pos ht _)

/-- For `i ≤ j`, `∏_{l ≥ j} t_l` divides `∏_{l ≥ i} t_l`. -/
theorem dvd_mul_suffixProd (t : Fin d → ℕ) {i j : Fin d} (hij : i ≤ j) :
    t j * suffixProd t j ∣ t i * suffixProd t i := by
  rcases hij.lt_or_eq with h | h
  · refine Dvd.dvd.mul_left ?_ _
    have hj : j ∉ Finset.univ.filter (fun l : Fin d => j < l) := by simp
    unfold suffixProd
    rw [← Finset.prod_insert (f := t) hj]
    apply Finset.prod_dvd_prod_of_subset
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    rcases hl with rfl | hl
    · exact h
    · exact h.trans hl
  · rw [h]

/-- Subtracting a multiple of `s_i = R/A_{i+1}` does not change the frequency digits `j ≥ i`
(proof of Lemma 4.2 (`lem:bridge-A`)). -/
theorem encFreq_symm_shiftFin {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) {i j : Fin d} (hij : i ≤ j)
    (f : Fin (totalLen t)) (m : ℤ) :
    (encFreq t).symm (shiftFin f (-(m * (aliasStep t i : ℤ)))) j = (encFreq t).symm f j := by
  have hQR : t j * suffixProd t j ∣ totalLen t := by
    rw [← prefixProd_mul_mul_suffixProd t j, mul_assoc]
    exact dvd_mul_left _ _
  have hQs : t j * suffixProd t j ∣ aliasStep t i := by
    rw [aliasStep_eq ht i]
    exact dvd_mul_suffixProd t hij
  have hn : ((t j * suffixProd t j : ℕ) : ℤ) ∣ -(m * (aliasStep t i : ℤ)) :=
    dvd_neg.mpr ((Int.natCast_dvd_natCast.mpr hQs).mul_left m)
  apply Fin.ext
  rw [encFreq_symm_apply, encFreq_symm_apply, ← Nat.mod_mul_right_div_self,
    ← Nat.mod_mul_right_div_self, mul_comm (suffixProd t j) (t j), shiftFin_mod_eq hQR f _ hn]

/-- The sample point of axis `j` is unchanged by a shift by a multiple of `s_i`, `i ≤ j`. -/
theorem samplePt_shiftFin {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) {i j : Fin d} (hij : i ≤ j)
    (f : Fin (totalLen t)) (m : ℤ) :
    samplePt t j (shiftFin f (-(m * (aliasStep t i : ℤ)))) = samplePt t j f := by
  unfold samplePt
  rw [encFreq_symm_shiftFin ht hij]

/-! ## One alias operator -/

theorem summable_abs_kernelG (hG : HasSum_kernelG_shiftStmt) {α : ℝ} (hα : 0 < α) (y : ℝ) :
    Summable (fun m : ℤ => |kernelG α (y - m)|) :=
  (hG α hα y).summable.abs

/-- `(A_i Z)_f = ∑_{m∈ℤ} G(y_i(f) - m) Z_{(f - m s_i) mod R}` (Section 4.2,
eq. (`eq:alias-op`)), as an absolutely convergent `HasSum`. -/
theorem aliasMatrix_mulVec_hasSum (hG : HasSum_kernelG_shiftStmt) {α : ℝ} (hα : 0 < α)
    (t : Fin d → ℕ) (i : Fin d) (v : Fin (totalLen t) → ℂ) (f : Fin (totalLen t)) :
    HasSum (fun m : ℤ => (kernelG α (samplePt t i f - m) : ℂ) *
      v (shiftFin f (-(m * (aliasStep t i : ℤ))))) ((aliasMatrix α t i *ᵥ v) f) := by
  have hsum : ∀ f' : Fin (totalLen t), Summable (fun m : ℤ =>
      if shiftFin f (-(m * (aliasStep t i : ℤ))) = f' then (kernelG α (samplePt t i f - m) : ℂ)
      else 0) := by
    intro f'
    refine Summable.of_norm_bounded (summable_abs_kernelG hG hα (samplePt t i f)) fun m => ?_
    split_ifs
    · simp only [Complex.norm_real, Real.norm_eq_abs, le_refl]
    · simp
  have h := hasSum_sum (s := Finset.univ) fun f' (_ : f' ∈ Finset.univ) =>
    (hsum f').hasSum.mul_right (v f')
  have hval : (aliasMatrix α t i *ᵥ v) f = ∑ f' ∈ Finset.univ,
      (∑' m : ℤ, if shiftFin f (-(m * (aliasStep t i : ℤ))) = f' then
        (kernelG α (samplePt t i f - m) : ℂ) else 0) * v f' := rfl
  rw [hval]
  refine h.congr_fun fun m => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-! ## Products of alias operators -/

/-- Products of nonnegative summable families are summable on `ℤ^n`. -/
theorem summable_pi_prod : ∀ {n : ℕ} (g : Fin n → ℤ → ℝ), (∀ k m, 0 ≤ g k m) →
    (∀ k, Summable (g k)) → Summable (fun m : Fin n → ℤ => ∏ k, g k (m k)) := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    exact (hasSum_single (fun k : Fin 0 => (Fin.elim0 k : ℤ))
      fun b hb => absurd (funext fun k => Fin.elim0 k) hb).summable
  | succ n ih =>
    intro g hg0 hg
    refine (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).summable_iff.mp ?_
    have h := (hg 0).mul_of_nonneg (ih (fun k => g k.succ) (fun k m => hg0 _ _) (fun k => hg _))
      (fun m => hg0 0 m) (fun m => Finset.prod_nonneg fun k _ => hg0 _ _)
    convert h using 1
    funext p
    simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]

/-- Expansion of `A_{e 0} A_{e 1} ⋯ A_{e (n-1)} Z` for a monotone family of axes `e`
(proof of Lemma 4.2 (`lem:bridge-A`)): every coefficient is evaluated at the digits of the original `f`. -/
theorem ofFn_prod_mulVec_hasSum (hG : HasSum_kernelG_shiftStmt) {α : ℝ} (hα : 0 < α)
    {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) (v : Fin (totalLen t) → ℂ) :
    ∀ (n : ℕ) (e : Fin n → Fin d), Monotone e → ∀ f : Fin (totalLen t),
    HasSum (fun m : Fin n → ℤ => (∏ k, (kernelG α (samplePt t (e k) f - m k) : ℂ)) *
        v (shiftFin f (-(∑ k, m k * (aliasStep t (e k) : ℤ)))))
      (((List.ofFn fun k => aliasMatrix α t (e k)).prod *ᵥ v) f) := by
  intro n
  induction n with
  | zero =>
    intro e _ f
    simp only [List.ofFn_zero, List.prod_nil, Matrix.one_mulVec, Fin.prod_univ_zero,
      Fin.sum_univ_zero, one_mul, neg_zero, shiftFin_zero]
    exact hasSum_single (fun k : Fin 0 => (Fin.elim0 k : ℤ))
      fun b hb => absurd (funext fun k => Fin.elim0 k) hb
  | succ n ih =>
    intro e he f
    have hmono : Monotone fun k : Fin n => e k.succ :=
      fun a b hab => he (Fin.succ_le_succ_iff.mpr hab)
    -- inner sums: the coefficients of the inner factors are read at the original digits
    have hin : ∀ a : ℤ, HasSum (fun m' : Fin n → ℤ =>
        (kernelG α (samplePt t (e 0) f - a) : ℂ) *
          ((∏ k, (kernelG α (samplePt t (e k.succ) f - m' k) : ℂ)) *
            v (shiftFin f (-(a * (aliasStep t (e 0) : ℤ)) +
              -(∑ k, m' k * (aliasStep t (e k.succ) : ℤ))))))
        ((kernelG α (samplePt t (e 0) f - a) : ℂ) *
          ((List.ofFn fun k : Fin n => aliasMatrix α t (e k.succ)).prod *ᵥ v)
            (shiftFin f (-(a * (aliasStep t (e 0) : ℤ))))) := by
      intro a
      have hpt : ∀ k : Fin n,
          samplePt t (e k.succ) (shiftFin f (-(a * (aliasStep t (e 0) : ℤ)))) =
            samplePt t (e k.succ) f :=
        fun k => samplePt_shiftFin ht (he (Fin.zero_le _)) f a
      have h := ih (fun k => e k.succ) hmono (shiftFin f (-(a * (aliasStep t (e 0) : ℤ))))
      simp only [hpt, shiftFin_shiftFin] at h
      exact h.mul_left _
    -- joint absolute summability over `ℤ × ℤ^n`
    have hFsum : Summable (fun p : ℤ × (Fin n → ℤ) =>
        (kernelG α (samplePt t (e 0) f - p.1) : ℂ) *
          ((∏ k, (kernelG α (samplePt t (e k.succ) f - p.2 k) : ℂ)) *
            v (shiftFin f (-(p.1 * (aliasStep t (e 0) : ℤ)) +
              -(∑ k, p.2 k * (aliasStep t (e k.succ) : ℤ)))))) := by
      have hdom := ((summable_abs_kernelG hG hα (samplePt t (e 0) f)).mul_of_nonneg
        (summable_pi_prod (fun k (m : ℤ) => |kernelG α (samplePt t (e k.succ) f - m)|)
          (fun _ _ => abs_nonneg _) (fun k => summable_abs_kernelG hG hα _))
        (fun _ => abs_nonneg _) (fun _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)).mul_right
          ‖v‖
      refine Summable.of_norm_bounded hdom fun p => ?_
      simp only [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v _)
        (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hF := hFsum.hasSum
    have h2 := (hF.prod_fiberwise hin).unique (aliasMatrix_mulVec_hasSum hG hα t (e 0)
      ((List.ofFn fun k : Fin n => aliasMatrix α t (e k.succ)).prod *ᵥ v) f)
    rw [h2] at hF
    rw [List.ofFn_succ, List.prod_cons, ← Matrix.mulVec_mulVec]
    refine (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).hasSum_iff.mp ?_
    convert hF using 1
    funext p
    simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, neg_add, mul_assoc]

/-! ## The product `A_2 A_3 ⋯ A_d` -/

theorem mem_deconvOrder {i : Fin d} : i ∈ deconvOrder d ↔ (i : ℕ) ≠ 0 := by
  simp [deconvOrder]

theorem aliasProd_eq_ofFn (α : ℝ) (t : Fin d → ℕ) :
    aliasProd α t = (List.ofFn fun k => aliasMatrix α t ((deconvOrder d).get k)).prod := by
  have h := congrArg (fun l => (l.map (aliasMatrix α t)).prod) (List.ofFn_get (deconvOrder d))
  simp only [List.map_ofFn] at h
  exact h.symm

/-- `(A_2 A_3 ⋯ A_d Z)_f = ∑_{m∈ℤ^{d-1}} ∏_{h≥2} G(y_h(f) - m_h) Z_{(f - ∑_h m_h R/A_h) mod R}`
for every frequency `f`, as an absolutely convergent `HasSum`. -/
theorem aliasProd_mulVec_hasSum (hG : HasSum_kernelG_shiftStmt) {α : ℝ} (hα : 0 < α)
    {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) (v : Fin (totalLen t) → ℂ) (f : Fin (totalLen t)) :
    HasSum (fun m : ({i : Fin d // (i : ℕ) ≠ 0} → ℤ) =>
        (∏ i, (kernelG α (samplePt t i.1 f - m i) : ℂ)) *
          v (shiftFin f (-(∑ i, m i * (aliasStep t i.1 : ℤ)))))
      ((aliasProd α t *ᵥ v) f) := by
  have hpw : (deconvOrder d).Pairwise (· < ·) := (List.pairwise_lt_finRange d).filter _
  have hnd : (deconvOrder d).Nodup := (List.nodup_finRange d).filter _
  have hmono : Monotone (deconvOrder d).get := hpw.sortedLT.strictMono_get.monotone
  have h := ofFn_prod_mulVec_hasSum hG hα ht v _ (deconvOrder d).get hmono f
  rw [← aliasProd_eq_ofFn] at h
  let E : Fin (deconvOrder d).length ≃ {i : Fin d // (i : ℕ) ≠ 0} :=
    (List.Nodup.getEquiv _ hnd).trans (Equiv.subtypeEquivRight fun _ => mem_deconvOrder)
  have hE : ∀ k, (E k).1 = (deconvOrder d).get k := fun k => rfl
  refine (E.arrowCongr (Equiv.refl ℤ)).hasSum_iff.mp ?_
  convert h using 1
  funext m
  have hm : ∀ i, (E.arrowCongr (Equiv.refl ℤ)) m i = m (E.symm i) := fun i => rfl
  simp only [Function.comp_apply, hm]
  rw [← E.prod_comp, ← E.sum_comp]
  simp only [Equiv.symm_apply_apply, hE]

/-- `(A_2 A_3 ⋯ A_d Z)_{f(u)}` is the explicit sum of eq. (`eq:lemma-A-explicit`) (Lemma 4.2 (`lem:bridge-A`)),
for every vector `Z`. -/
theorem aliasProd_mulVec_encFreq (hG : HasSum_kernelG_shiftStmt) {α : ℝ} (hα : 0 < α)
    {t : Fin d → ℕ} (ht : ∀ i, 0 < t i) (v : Fin (totalLen t) → ℂ) (u : Idx t) :
    (aliasProd α t *ᵥ v) (encFreq t u) =
      ∑' m : ({i : Fin d // (i : ℕ) ≠ 0} → ℤ),
        (∏ i : {i : Fin d // (i : ℕ) ≠ 0},
            (kernelG α ((((u i.1 : Fin (t i.1)) : ℕ) + 1 / 2 : ℝ) / (t i.1 : ℝ) - (m i : ℝ)) : ℂ)) *
          v (shiftFin (encFreq t u)
            (-(∑ i : {i : Fin d // (i : ℕ) ≠ 0}, m i * (aliasStep t i.1 : ℤ)))) := by
  have h := aliasProd_mulVec_hasSum hG hα ht v (encFreq t u)
  simp only [samplePt, Equiv.symm_apply_apply] at h
  exact h.tsum_eq.symm

/-! ## Lemma 4.2 (bridge Lemma A), operator form -/

theorem alpha_pos_of_admissible {ω : ℕ} (hω : 8 ≤ ω) {α : ℝ} (hα : AlphaAdmissible ω α) :
    0 < α := by
  have h1 : 0 < (ω : ℝ) * Real.log 2 / Real.pi :=
    div_pos (mul_pos (by exact_mod_cast (by omega : 0 < ω)) (Real.log_pos one_lt_two)) Real.pi_pos
  have h2 := Real.sqrt_pos.mpr h1
  linarith [hα.1]

end LemmaAOperatorProof

open LemmaAOperatorProof in
/-- **Lemma 4.2 (bridge Lemma A), operator form** (`lem:bridge-A`, eq. (`eq:lemma-A`)), derived from the explicit
form (eq. (`eq:lemma-A-explicit`)) and `∑_m G(ξ - m) = 1` (summability of the alias weights). -/
theorem lemmaA_of (hE : LemmaA_explicitStmt) (hG : HasSum_kernelG_shiftStmt) : LemmaAStmt := by
  intro d ω hω α hα t ht x u
  rw [hE ω hω α hα t ht x u]
  exact (aliasProd_mulVec_encFreq hG (alpha_pos_of_admissible hω hα)
    (fun i => by have := (ht i).1; omega) _ u).symm

end SubNLogN.Math.Bridge
