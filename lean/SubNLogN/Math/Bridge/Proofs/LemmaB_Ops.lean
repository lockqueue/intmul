import SubNLogN.Math.Bridge.LemmaB_Ops
import SubNLogN.Math.Bridge.LemmaC_Solver

/-!
# Bridge: proofs of Lemma 4.4 (bridge Lemma B)(i), B(ii), B(vi) and Lemma 4.6 (bridge Lemma C)(vi)

Proofs of the operator contracts `LemmaB_iStmt`, `LemmaB_iiStmt`, `LemmaB_viStmt`
(`SubNLogN/Math/Bridge/LemmaB_Ops.lean`, Lemma 4.4 (`lem:bridge-B`)) and `LemmaC_viStmt`
(`SubNLogN/Math/Bridge/LemmaC_Solver.lean`, `lem:bridge-C`). External sub-results enter only
as explicit contract hypotheses (`…Stmt`). (`LemmaB*`/`lemmaB*` and `LemmaC*`/`lemmaC*` reflect an earlier draft (bridge Lemmas B and C), kept for stability.)

* `lemmaB_i_of`: the row `f` of `A_h` is `∑' m, G(y-m)·e_{(f - m R/A_h) mod R}`; several `m` may
  hit the same column (short cycles), and the triangle inequality bounds the absolute row sum by
  `∑_m G(y-m) = 1`. The row of `B_h` has absolute sum `≤ c_0 + c_1 ≤ ∑_m G(y-m) = 1`.
* `lemmaB_ii_of`: the `m = 0` and `m = 1` terms of `A_h` are exactly the two terms of `B_h`, so
  the absolute row sums of `A_h - B_h` are `≤ ∑_{m ∉ {0,1}} G(y-m) = 1 - c_0 - c_1`, and
  `1 - c_0 - c_1 < 0.120·2^{-ω}` for the sample `y ∈ (0,1)` (contract `Omitted_weight_ltStmt`).
* `lemmaB_vi_of`: `(B_2⋯B_d)^{-1} = B_d^{-1}⋯B_2^{-1}` (`Matrix.mul_inv_rev`, which holds without
  invertibility hypotheses) and submultiplicativity give `∏_h 4t_h/7 = (4/7)^{d-1} R/t_1`. The
  product is invertible (its determinant is a product of units, B(v)), Lemma 4.2 (bridge Lemma A) gives
  `Y = A_2⋯A_d Z` with `Z = F_R x`, so `(B_2⋯B_d)^{-1} Y - Z = (B_2⋯B_d)^{-1}(A_2⋯A_d - B_2⋯B_d) Z`.
  The telescoping `A_2⋯A_d - B_2⋯B_d = ∑_h B_2⋯B_{h-1}(A_h - B_h)A_{h+1}⋯A_d` with (i), (ii)
  bounds the middle factor by `(d-1)·0.120·2^{-ω}`, and `‖F_R x‖ ≤ ‖x‖` (`norm_dft_le`).
* `lemmaC_vi_of`: the first two claims of B(vi).

Helper lemmas live in the namespace `SubNLogN.Math.Bridge.LemmaBOpsAux`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators Matrix

namespace LemmaBOpsAux

/-! ## Part 0: `opNormInf` of matrices -/

section MatrixNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Row-sum criterion: if every absolute row sum of `M` is `≤ C`, then `‖M‖_∞ ≤ C`. -/
theorem opNormInf_toLin'_le_of_rows (M : Matrix n n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ∑ j, ‖M i j‖ ≤ C) : opNormInf (Matrix.toLin' M) ≤ C := by
  unfold opNormInf
  rw [LinearMap.toMatrix'_toLin']
  have hle : (Finset.univ.sup fun i => ∑ j, ‖M i j‖₊) ≤ (⟨C, hC⟩ : NNReal) := by
    refine Finset.sup_le fun i _ => ?_
    have h' : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ ((⟨C, hC⟩ : NNReal) : ℝ) := by
      simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_mk] using h i
    exact NNReal.coe_le_coe.mp h'
  exact NNReal.coe_le_coe.mpr hle

/-- Strict row-sum criterion: if every absolute row sum of `M` is `< C` (`C > 0`), then
`‖M‖_∞ < C`. -/
theorem opNormInf_toLin'_lt_of_rows (M : Matrix n n ℂ) {C : ℝ} (hC : 0 < C)
    (h : ∀ i, ∑ j, ‖M i j‖ < C) : opNormInf (Matrix.toLin' M) < C := by
  unfold opNormInf
  rw [LinearMap.toMatrix'_toLin']
  have hbot : (⊥ : NNReal) < ⟨C, hC.le⟩ := by
    rw [NNReal.bot_eq_zero]
    exact NNReal.coe_pos.mp hC
  have hlt : (Finset.univ.sup fun i => ∑ j, ‖M i j‖₊) < (⟨C, hC.le⟩ : NNReal) := by
    refine (Finset.sup_lt_iff hbot).mpr fun i _ => ?_
    have h' : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) < ((⟨C, hC.le⟩ : NNReal) : ℝ) := by
      simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_mk] using h i
    exact NNReal.coe_lt_coe.mp h'
  exact NNReal.coe_lt_coe.mpr hlt

/-- `‖M v‖_∞ ≤ ‖M‖_∞ ‖v‖_∞` in matrix form. -/
theorem norm_mulVec_le_opNormInf (M : Matrix n n ℂ) (v : n → ℂ) :
    ‖M *ᵥ v‖ ≤ opNormInf (Matrix.toLin' M) * ‖v‖ := by
  have h := norm_apply_le_opNormInf (Matrix.toLin' M) v
  rwa [Matrix.toLin'_apply] at h

/-- Submultiplicativity in matrix form. -/
theorem opNormInf_toLin'_mul_le (M N : Matrix n n ℂ) :
    opNormInf (Matrix.toLin' (M * N)) ≤
      opNormInf (Matrix.toLin' M) * opNormInf (Matrix.toLin' N) := by
  rw [Matrix.toLin'_mul]
  exact opNormInf_comp_le _ _

/-- Triangle inequality in matrix form. -/
theorem opNormInf_toLin'_add_le (M N : Matrix n n ℂ) :
    opNormInf (Matrix.toLin' (M + N)) ≤
      opNormInf (Matrix.toLin' M) + opNormInf (Matrix.toLin' N) := by
  rw [opNormInf_le_iff _ (add_nonneg (opNormInf_nonneg _) (opNormInf_nonneg _))]
  intro x
  rw [map_add, LinearMap.add_apply, add_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_apply_le_opNormInf _ x) (norm_apply_le_opNormInf _ x))

theorem opNormInf_toLin'_one_le : opNormInf (Matrix.toLin' (1 : Matrix n n ℂ)) ≤ 1 := by
  rw [opNormInf_le_iff _ zero_le_one]
  intro x
  rw [Matrix.toLin'_one, LinearMap.id_apply, one_mul]

theorem opNormInf_toLin'_zero_le : opNormInf (Matrix.toLin' (0 : Matrix n n ℂ)) ≤ 0 := by
  rw [opNormInf_le_iff _ le_rfl]
  intro x
  simp

variable {ι : Type*}

/-- A product of matrices of norm `≤ 1` has norm `≤ 1`. -/
theorem opNormInf_listProd_le_one (L : List ι) (a : ι → Matrix n n ℂ)
    (ha : ∀ i ∈ L, opNormInf (Matrix.toLin' (a i)) ≤ 1) :
    opNormInf (Matrix.toLin' (L.map a).prod) ≤ 1 := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    exact opNormInf_toLin'_one_le
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons]
    have h1 := ha i List.mem_cons_self
    have h2 := ih fun j hj => ha j (List.mem_cons_of_mem i hj)
    calc opNormInf (Matrix.toLin' (a i * (L.map a).prod))
        ≤ opNormInf (Matrix.toLin' (a i)) * opNormInf (Matrix.toLin' (L.map a).prod) :=
          opNormInf_toLin'_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (opNormInf_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Telescoping bound: if `‖a_i‖, ‖b_i‖ ≤ 1` and `‖a_i - b_i‖ ≤ ε` for all `i ∈ L`, then
`‖∏ a_i - ∏ b_i‖ ≤ |L| ε` (products in list order; uses
`a P - b Q = (a - b) P + b (P - Q)`). -/
theorem opNormInf_listProd_sub_le (L : List ι) (a b : ι → Matrix n n ℂ) {ε : ℝ}
    (ha : ∀ i ∈ L, opNormInf (Matrix.toLin' (a i)) ≤ 1)
    (hb : ∀ i ∈ L, opNormInf (Matrix.toLin' (b i)) ≤ 1)
    (hab : ∀ i ∈ L, opNormInf (Matrix.toLin' (a i - b i)) ≤ ε) :
    opNormInf (Matrix.toLin' ((L.map a).prod - (L.map b).prod)) ≤ (L.length : ℝ) * ε := by
  induction L with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, sub_self, List.length_nil, Nat.cast_zero,
      zero_mul]
    exact opNormInf_toLin'_zero_le
  | cons i L ih =>
    have hai := ha i List.mem_cons_self
    have hbi := hb i List.mem_cons_self
    have habi := hab i List.mem_cons_self
    have hε : 0 ≤ ε := (opNormInf_nonneg _).trans habi
    have ih' := ih (fun j hj => ha j (List.mem_cons_of_mem i hj))
      (fun j hj => hb j (List.mem_cons_of_mem i hj)) (fun j hj => hab j (List.mem_cons_of_mem i hj))
    have hPA := opNormInf_listProd_le_one L a (fun j hj => ha j (List.mem_cons_of_mem i hj))
    have key : a i * (L.map a).prod - b i * (L.map b).prod =
        (a i - b i) * (L.map a).prod + b i * ((L.map a).prod - (L.map b).prod) := by
      rw [sub_mul, mul_sub]; abel
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, key, List.length_cons]
    calc opNormInf (Matrix.toLin' ((a i - b i) * (L.map a).prod +
          b i * ((L.map a).prod - (L.map b).prod)))
        ≤ opNormInf (Matrix.toLin' ((a i - b i) * (L.map a).prod)) +
            opNormInf (Matrix.toLin' (b i * ((L.map a).prod - (L.map b).prod))) :=
          opNormInf_toLin'_add_le _ _
      _ ≤ opNormInf (Matrix.toLin' (a i - b i)) * opNormInf (Matrix.toLin' (L.map a).prod) +
            opNormInf (Matrix.toLin' (b i)) *
              opNormInf (Matrix.toLin' ((L.map a).prod - (L.map b).prod)) :=
          add_le_add (opNormInf_toLin'_mul_le _ _) (opNormInf_toLin'_mul_le _ _)
      _ ≤ ε * 1 + 1 * ((L.length : ℝ) * ε) :=
          add_le_add (mul_le_mul habi hPA (opNormInf_nonneg _) hε)
            (mul_le_mul hbi ih' (opNormInf_nonneg _) zero_le_one)
      _ = ((L.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- `‖(∏ b_i)^{-1}‖ ≤ ∏ c_i` when `‖b_i^{-1}‖ ≤ c_i`; uses `(A B)^{-1} = B^{-1} A^{-1}`
(`Matrix.mul_inv_rev`, valid for all square matrices over a commutative ring). -/
theorem opNormInf_listProd_inv_le (L : List ι) (b : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hb : ∀ i ∈ L, opNormInf (Matrix.toLin' (b i)⁻¹) ≤ c i) :
    opNormInf (Matrix.toLin' ((L.map b).prod)⁻¹) ≤ (L.map c).prod := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, inv_one]
    exact opNormInf_toLin'_one_le
  | cons i L ih =>
    have h1 := hb i List.mem_cons_self
    have h2 := ih fun j hj => hb j (List.mem_cons_of_mem i hj)
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_inv_rev]
    calc opNormInf (Matrix.toLin' (((L.map b).prod)⁻¹ * (b i)⁻¹))
        ≤ opNormInf (Matrix.toLin' ((L.map b).prod)⁻¹) * opNormInf (Matrix.toLin' (b i)⁻¹) :=
          opNormInf_toLin'_mul_le _ _
      _ ≤ (L.map c).prod * c i :=
          mul_le_mul h2 h1 (opNormInf_nonneg _) ((opNormInf_nonneg _).trans h2)
      _ = c i * (L.map c).prod := mul_comm _ _

/-- A product of matrices with unit determinants has unit determinant. -/
theorem isUnit_det_listProd (L : List ι) (b : ι → Matrix n n ℂ)
    (hb : ∀ i ∈ L, IsUnit (b i).det) : IsUnit ((L.map b).prod).det := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, Matrix.det_mul]
    exact (hb i List.mem_cons_self).mul (ih fun j hj => hb j (List.mem_cons_of_mem i hj))

end MatrixNorm

/-! ## Part 1: absolute row sums of scattered rows -/

section RowSums

/-- A row `f' ↦ ∑' m, [col m = f'] w_m` with `w ≥ 0` summable has absolute sum `≤ ∑' m, w_m`
(several `m` may hit the same column; triangle inequality). -/
theorem rowSum_tsum_le {R : ℕ} (col : ℤ → Fin R) (w : ℤ → ℝ) (hw0 : ∀ m, 0 ≤ w m)
    (hw : Summable w) :
    ∑ f', ‖∑' m, (if col m = f' then (w m : ℂ) else 0)‖ ≤ ∑' m, w m := by
  have hnorm : ∀ f' m, ‖(if col m = f' then (w m : ℂ) else 0)‖ =
      if col m = f' then w m else 0 := by
    intro f' m
    split_ifs
    · exact Complex.norm_of_nonneg (hw0 m)
    · exact norm_zero
  have hsum : ∀ f', Summable (fun m => if col m = f' then w m else 0) := by
    intro f'
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hw
    · split_ifs
      · exact hw0 m
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hw0 m
  calc ∑ f', ‖∑' m, (if col m = f' then (w m : ℂ) else 0)‖
      ≤ ∑ f', ∑' m, (if col m = f' then w m else 0) := by
        refine Finset.sum_le_sum fun f' _ => ?_
        have hs : Summable (fun m => ‖(if col m = f' then (w m : ℂ) else 0)‖) :=
          (hsum f').congr fun m => (hnorm f' m).symm
        exact (norm_tsum_le_tsum_norm hs).trans (le_of_eq (tsum_congr (hnorm f')))
    _ = ∑' m, ∑ f', (if col m = f' then w m else 0) :=
        (Summable.tsum_finsetSum fun f' _ => hsum f').symm
    _ = ∑' m, w m := tsum_congr fun m => by simp

/-- A row with the two entries `c_0` at column `f` and `c_1` at column `s` (`c_0, c_1 ≥ 0`;
possibly `s = f`) has absolute sum `≤ c_0 + c_1`. -/
theorem rowSum_two_le {R : ℕ} (f s : Fin R) (c0 c1 : ℝ) (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) :
    ∑ f', ‖(if f' = f then (c0 : ℂ) else 0) + (if f' = s then (c1 : ℂ) else 0)‖ ≤ c0 + c1 := by
  have e0 : ∀ f', ‖(if f' = f then (c0 : ℂ) else 0)‖ = if f' = f then c0 else 0 := by
    intro f'
    split_ifs
    · exact Complex.norm_of_nonneg h0
    · exact norm_zero
  have e1 : ∀ f', ‖(if f' = s then (c1 : ℂ) else 0)‖ = if f' = s then c1 else 0 := by
    intro f'
    split_ifs
    · exact Complex.norm_of_nonneg h1
    · exact norm_zero
  calc ∑ f', ‖(if f' = f then (c0 : ℂ) else 0) + (if f' = s then (c1 : ℂ) else 0)‖
      ≤ ∑ f', (‖(if f' = f then (c0 : ℂ) else 0)‖ + ‖(if f' = s then (c1 : ℂ) else 0)‖) :=
        Finset.sum_le_sum fun f' _ => norm_add_le _ _
    _ = c0 + c1 := by
        rw [Finset.sum_add_distrib]
        simp only [e0, e1, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Removing the terms `m = 0, 1` from a scattered row. -/
theorem tsum_col_split {R : ℕ} (col : ℤ → Fin R) (w : ℤ → ℝ) (hw0 : ∀ m, 0 ≤ w m)
    (hw : Summable w) (f' : Fin R) :
    ∑' m, (if col m = f' then ((if m = 1 then 0 else if m = 0 then 0 else w m : ℝ) : ℂ)
        else 0) =
      (∑' m, (if col m = f' then (w m : ℂ) else 0)) - (if col 0 = f' then (w 0 : ℂ) else 0) -
        (if col 1 = f' then (w 1 : ℂ) else 0) := by
  have hg : Summable (fun m => if col m = f' then (w m : ℂ) else 0) := by
    refine Summable.of_norm_bounded hw fun m => ?_
    split_ifs
    · exact (Complex.norm_of_nonneg (hw0 m)).le
    · rw [norm_zero]; exact hw0 m
  have hfun : (fun n : ℤ => if n = 1 then 0 else if n = 0 then 0 else
        if col n = f' then (w n : ℂ) else 0) =
      fun m => if col m = f' then ((if m = 1 then 0 else if m = 0 then 0 else w m : ℝ) : ℂ)
        else 0 := by
    funext m
    by_cases h1 : m = 1
    · subst h1; simp
    · by_cases h0 : m = 0
      · subst h0; simp
      · simp [h1, h0]
  have h2 := hasSum_ite_sub_hasSum (hasSum_ite_sub_hasSum hg.hasSum 0) 1
  rw [hfun, if_neg (one_ne_zero : (1 : ℤ) ≠ 0)] at h2
  exact h2.tsum_eq

/-- Orientation of the equality test in an `ite`. -/
theorem ite_eq_comm_zero {R : ℕ} (a b : Fin R) (c : ℂ) :
    (if a = b then c else 0) = (if b = a then c else 0) := by
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

end RowSums

/-! ## Part 2: indices, sample points, `α > 0` -/

section Indices

/-- An admissible `α` (with `ω ≥ 8`) is positive. -/
theorem alpha_pos_of_admissible {ω : ℕ} (hω : 8 ≤ ω) {α : ℝ} (hα : AlphaAdmissible ω α) :
    0 < α := by
  have hω' : (0 : ℝ) < ω := by exact_mod_cast (show 0 < ω by omega)
  have h1 : 0 < Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) :=
    Real.sqrt_pos.mpr (div_pos (mul_pos hω' (Real.log_pos one_lt_two)) Real.pi_pos)
  linarith [hα.1]

/-- The sample `y = (u_h(f) + 1/2)/t_h` lies in `(0,1)`. -/
theorem samplePt_pos_lt_one {d : ℕ} (t : Fin d → ℕ) (ht : ShapeOK t) (i : Fin d)
    (f : Fin (totalLen t)) : 0 < samplePt t i f ∧ samplePt t i f < 1 := by
  have hu : (((encFreq t).symm f i : Fin (t i)) : ℕ) + 1 ≤ t i := ((encFreq t).symm f i).isLt
  have hti : (0 : ℝ) < (t i : ℝ) := by
    have h2 := (ht i).1
    exact_mod_cast (show 0 < t i by omega)
  have hu' : ((((encFreq t).symm f i : Fin (t i)) : ℕ) : ℝ) + 1 ≤ (t i : ℝ) := by
    exact_mod_cast hu
  unfold samplePt
  constructor
  · exact div_pos (by positivity) hti
  · rw [div_lt_one hti]; linarith

/-- `shiftFin f 0 = f`. -/
theorem shiftFin_zero' {R : ℕ} (f : Fin R) : shiftFin f 0 = f := by
  apply Fin.ext
  have h1 : ((f : ℕ) : ℤ) % (R : ℤ) = (f : ℕ) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast f.isLt)
  show ((((f : ℕ) : ℤ) + 0) % (R : ℤ)).toNat = (f : ℕ)
  rw [add_zero, h1, Int.toNat_natCast]

theorem deconvOrder_nodup (d : ℕ) : (deconvOrder d).Nodup :=
  (List.nodup_finRange d).filter _

theorem mem_deconvOrder {d : ℕ} {j : Fin d} : j ∈ deconvOrder d ↔ (j : ℕ) ≠ 0 := by
  simp [deconvOrder]

theorem deconvOrder_toFinset (d : ℕ) :
    (deconvOrder d).toFinset = Finset.univ.filter (fun j : Fin d => (j : ℕ) ≠ 0) := by
  ext j
  simp [mem_deconvOrder]

theorem deconvOrder_prod_map {M : Type*} [CommMonoid M] (d : ℕ) (g : Fin d → M) :
    ((deconvOrder d).map g).prod =
      ∏ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℕ) ≠ 0), g j := by
  rw [← List.prod_toFinset g (deconvOrder_nodup d), deconvOrder_toFinset]

theorem filter_ne_zero_eq_erase {d : ℕ} (hd : 1 ≤ d) :
    Finset.univ.filter (fun j : Fin d => (j : ℕ) ≠ 0) = Finset.univ.erase ⟨0, hd⟩ := by
  ext j
  simp [Fin.ext_iff]

theorem card_erase_zero {d : ℕ} (hd : 1 ≤ d) :
    (Finset.univ.erase (⟨0, hd⟩ : Fin d)).card = d - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem deconvOrder_length {d : ℕ} (hd : 1 ≤ d) : (deconvOrder d).length = d - 1 := by
  rw [← List.toFinset_card_of_nodup (deconvOrder_nodup d), deconvOrder_toFinset,
    filter_ne_zero_eq_erase hd, card_erase_zero hd]

/-- `∏_{h≥2} 4t_h/7 = (4/7)^{d-1} R/t_1`. -/
theorem deconvOrder_prod_bound {d : ℕ} (t : Fin d → ℕ) (hd : 1 ≤ d) (ht0 : t ⟨0, hd⟩ ≠ 0) :
    ((deconvOrder d).map (fun j => 4 * (t j : ℝ) / 7)).prod =
      (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) := by
  rw [deconvOrder_prod_map, filter_ne_zero_eq_erase hd]
  have hprod : (∏ j ∈ Finset.univ.erase (⟨0, hd⟩ : Fin d), (t j : ℝ)) =
      (totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast ht0),
      Finset.prod_erase_mul Finset.univ (fun j => (t j : ℝ)) (Finset.mem_univ (⟨0, hd⟩ : Fin d))]
    simp [totalLen, Nat.cast_prod]
  calc ∏ j ∈ Finset.univ.erase (⟨0, hd⟩ : Fin d), (4 * (t j : ℝ) / 7)
      = ∏ j ∈ Finset.univ.erase (⟨0, hd⟩ : Fin d), ((4 / 7 : ℝ) * (t j : ℝ)) :=
        Finset.prod_congr rfl fun j _ => by ring
    _ = (4 / 7 : ℝ) ^ (Finset.univ.erase (⟨0, hd⟩ : Fin d)).card *
          ∏ j ∈ Finset.univ.erase (⟨0, hd⟩ : Fin d), (t j : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) := by
        rw [card_erase_zero hd, hprod]

end Indices

end LemmaBOpsAux

open LemmaBOpsAux

/-! ## Part 3: Lemma 4.4 (bridge Lemma B)(i), B(ii) -/

/-- Lemma 4.4 (bridge Lemma B)(i) (`lem:bridge-B`): `‖A_h‖_∞ ≤ 1` and `‖B_h‖_∞ ≤ 1`, from
`∑_m G(y-m) = 1` with positive terms. -/
theorem lemmaB_i_of (hS : HasSum_kernelG_shiftStmt) (hpos : KernelG_posStmt) :
    LemmaB_iStmt := by
  intro d ω hω α hα t ht i _hi
  have hα0 : 0 < α := alpha_pos_of_admissible hω hα
  refine ⟨opNormInf_toLin'_le_of_rows _ zero_le_one fun f => ?_,
    opNormInf_toLin'_le_of_rows _ zero_le_one fun f => ?_⟩
  · have hw : HasSum (fun m : ℤ => kernelG α (samplePt t i f - m)) 1 := hS α hα0 _
    calc ∑ f', ‖aliasMatrix α t i f f'‖
        ≤ ∑' m : ℤ, kernelG α (samplePt t i f - m) :=
          rowSum_tsum_le (fun m : ℤ => shiftFin f (-(m * (aliasStep t i : ℤ))))
            (fun m : ℤ => kernelG α (samplePt t i f - m)) (fun m => (hpos α hα0 _).le)
            hw.summable
      _ = 1 := hw.tsum_eq
  · have hw : HasSum (fun m : ℤ => kernelG α (samplePt t i f - m)) 1 := hS α hα0 _
    have h01 : kernelG α (samplePt t i f) + kernelG α (samplePt t i f - 1) ≤ 1 := by
      have h := sum_le_hasSum ({0, 1} : Finset ℤ) (fun m _ => (hpos α hα0 _).le) hw
      rw [Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1)] at h
      simpa using h
    calc ∑ f', ‖truncMatrix α t i f f'‖
        ≤ kernelG α (samplePt t i f) + kernelG α (samplePt t i f - 1) :=
          rowSum_two_le f (shiftFin f (-(aliasStep t i : ℤ))) _ _ (hpos α hα0 _).le
            (hpos α hα0 _).le
      _ ≤ 1 := h01

/-- Lemma 4.4 (bridge Lemma B)(ii) (`lem:bridge-B`): `‖A_h - B_h‖_∞ < 0.120·2^{-ω}`. The terms `m = 0, 1`
of `A_h` are the two terms of `B_h`; the rest has absolute row sum `≤ 1 - c_0 - c_1`. -/
theorem lemmaB_ii_of (hS : HasSum_kernelG_shiftStmt) (hpos : KernelG_posStmt)
    (hO : Omitted_weight_ltStmt) : LemmaB_iiStmt := by
  intro d ω hω α hα t ht i _hi
  have hα0 : 0 < α := alpha_pos_of_admissible hω hα
  have hεpos : (0 : ℝ) < 0.120 * (2 : ℝ) ^ (-(ω : ℤ)) := by positivity
  refine opNormInf_toLin'_lt_of_rows _ hεpos fun f => ?_
  have hw : HasSum (fun m : ℤ => kernelG α (samplePt t i f - m)) 1 := hS α hα0 _
  have hw0 : ∀ m : ℤ, 0 ≤ kernelG α (samplePt t i f - m) := fun m => (hpos α hα0 _).le
  have hrow : ∀ f', (aliasMatrix α t i - truncMatrix α t i) f f' =
      ∑' m : ℤ, (if shiftFin f (-(m * (aliasStep t i : ℤ))) = f' then
        ((if m = 1 then 0 else if m = 0 then 0 else kernelG α (samplePt t i f - m) : ℝ) : ℂ)
        else 0) := by
    intro f'
    refine Eq.trans ?_ (tsum_col_split (fun m : ℤ => shiftFin f (-(m * (aliasStep t i : ℤ))))
      (fun m : ℤ => kernelG α (samplePt t i f - m)) hw0 hw.summable f').symm
    simp only [Matrix.sub_apply, aliasMatrix, truncMatrix, Int.cast_zero, Int.cast_one, zero_mul,
      one_mul, neg_zero, sub_zero, shiftFin_zero']
    rw [ite_eq_comm_zero f f', ite_eq_comm_zero (shiftFin f (-(aliasStep t i : ℤ))) f']
    ring
  have hW0 : ∀ m : ℤ,
      0 ≤ (if m = 1 then 0 else if m = 0 then 0 else kernelG α (samplePt t i f - m) : ℝ) := by
    intro m
    split_ifs
    · exact le_rfl
    · exact le_rfl
    · exact hw0 m
  have hWsum : HasSum
      (fun m : ℤ => (if m = 1 then 0 else if m = 0 then 0 else kernelG α (samplePt t i f - m) : ℝ))
      (1 - kernelG α (samplePt t i f) - kernelG α (samplePt t i f - 1)) := by
    have h2 := hasSum_ite_sub_hasSum (hasSum_ite_sub_hasSum hw 0) 1
    have hv : (1 : ℝ) - kernelG α (samplePt t i f) - kernelG α (samplePt t i f - 1) =
        1 - kernelG α (samplePt t i f - ((0 : ℤ) : ℝ)) -
          (if (1 : ℤ) = 0 then 0 else kernelG α (samplePt t i f - ((1 : ℤ) : ℝ))) := by
      simp
    rw [hv]
    exact h2
  calc ∑ f', ‖(aliasMatrix α t i - truncMatrix α t i) f f'‖
      = ∑ f', ‖∑' m : ℤ, (if shiftFin f (-(m * (aliasStep t i : ℤ))) = f' then
          ((if m = 1 then 0 else if m = 0 then 0 else kernelG α (samplePt t i f - m) : ℝ) : ℂ)
          else 0)‖ :=
        Finset.sum_congr rfl fun f' _ => by rw [hrow f']
    _ ≤ ∑' m : ℤ,
          (if m = 1 then 0 else if m = 0 then 0 else kernelG α (samplePt t i f - m) : ℝ) :=
        rowSum_tsum_le (fun m : ℤ => shiftFin f (-(m * (aliasStep t i : ℤ))))
          (fun m : ℤ =>
            (if m = 1 then 0 else if m = 0 then 0 else kernelG α (samplePt t i f - m) : ℝ))
          hW0 hWsum.summable
    _ = 1 - kernelG α (samplePt t i f) - kernelG α (samplePt t i f - 1) := hWsum.tsum_eq
    _ < 0.120 * (2 : ℝ) ^ (-(ω : ℤ)) := hO ω hω α hα _ (samplePt_pos_lt_one t ht i f)

/-! ## Part 4: Lemma 4.4 (bridge Lemma B)(vi) and Lemma 4.6 (bridge Lemma C)(vi) -/

/-- Lemma 4.4 (bridge Lemma B)(vi) (`lem:bridge-B`, eq. (`eq:lemma-B-total`)): `‖(B_2⋯B_d)^{-1}‖_∞ ≤ (4/7)^{d-1} R/t_1 ≤ R/t_1` and
`‖(B_2⋯B_d)^{-1} Y - F_R x‖_∞ ≤ 0.120 (d-1) (R/t_1) 2^{-ω} ‖x‖_∞` for `Y = F_t U`. -/
theorem lemmaB_vi_of (hA : LemmaAStmt) (hii : LemmaB_iiStmt) (hvax : LemmaB_v_axisStmt)
    (hi : LemmaB_iStmt) : LemmaB_viStmt := by
  intro d ω hω α hα t ht hd x
  have hmem : ∀ j ∈ deconvOrder d, (j : ℕ) ≠ 0 := fun j hj => mem_deconvOrder.mp hj
  have ht0 : t ⟨0, hd⟩ ≠ 0 := by
    have h2 := (ht ⟨0, hd⟩).1
    omega
  -- the norm of the inverse
  have hinv : opNormInf (Matrix.toLin' (truncProd α t)⁻¹) ≤
      (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) := by
    calc opNormInf (Matrix.toLin' (truncProd α t)⁻¹)
        ≤ ((deconvOrder d).map (fun j => 4 * (t j : ℝ) / 7)).prod :=
          opNormInf_listProd_inv_le (deconvOrder d) (truncMatrix α t) (fun j => 4 * (t j : ℝ) / 7)
            (fun j hj => (hvax ω hω α hα t ht j (hmem j hj)).2.1)
      _ = (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) :=
          deconvOrder_prod_bound t hd ht0
  have hRt : (0 : ℝ) ≤ (totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ) := by positivity
  have hle : (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) ≤
      (totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ) := by
    have h1 : (4 / 7 : ℝ) ^ (d - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ))
        ≤ 1 * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) := mul_le_mul_of_nonneg_right h1 hRt
      _ = (totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ) := one_mul _
  refine ⟨hinv, hle, ?_⟩
  -- Lemma 4.2 (bridge Lemma A): `Y = A_2⋯A_d Z`
  have hY : (fun f => dftTensor t (spreadAll α t (x ∘ encIn t)) ((encFreq t).symm f)) =
      aliasProd α t *ᵥ dft (totalLen t) x := by
    funext f
    rw [hA ω hω α hα t ht x ((encFreq t).symm f), Equiv.apply_symm_apply]
  rw [hY]
  have hdet : IsUnit (truncProd α t).det :=
    isUnit_det_listProd (deconvOrder d) (truncMatrix α t)
      (fun j hj => (hvax ω hω α hα t ht j (hmem j hj)).1)
  have hdiff : (truncProd α t)⁻¹ *ᵥ (aliasProd α t *ᵥ dft (totalLen t) x) - dft (totalLen t) x =
      (truncProd α t)⁻¹ *ᵥ ((aliasProd α t - truncProd α t) *ᵥ dft (totalLen t) x) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [hdiff]
  -- telescoping: `‖A_2⋯A_d - B_2⋯B_d‖ ≤ (d-1)·0.120·2^{-ω}`
  have hAB : opNormInf (Matrix.toLin' (aliasProd α t - truncProd α t)) ≤
      ((d : ℝ) - 1) * (0.120 * (2 : ℝ) ^ (-(ω : ℤ))) := by
    have h := opNormInf_listProd_sub_le (deconvOrder d) (aliasMatrix α t) (truncMatrix α t)
      (fun j hj => (hi ω hω α hα t ht j (hmem j hj)).1)
      (fun j hj => (hi ω hω α hα t ht j (hmem j hj)).2)
      (fun j hj => (hii ω hω α hα t ht j (hmem j hj)).le)
    rw [deconvOrder_length hd, Nat.cast_sub hd, Nat.cast_one] at h
    exact h
  have hZx : ‖dft (totalLen t) x‖ ≤ ‖x‖ := norm_dft_le _ x
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hε0 : (0 : ℝ) ≤ 0.120 * (2 : ℝ) ^ (-(ω : ℤ)) := by positivity
  calc ‖(truncProd α t)⁻¹ *ᵥ ((aliasProd α t - truncProd α t) *ᵥ dft (totalLen t) x)‖
      ≤ opNormInf (Matrix.toLin' (truncProd α t)⁻¹) *
          ‖(aliasProd α t - truncProd α t) *ᵥ dft (totalLen t) x‖ :=
        norm_mulVec_le_opNormInf _ _
    _ ≤ opNormInf (Matrix.toLin' (truncProd α t)⁻¹) *
          (opNormInf (Matrix.toLin' (aliasProd α t - truncProd α t)) *
            ‖dft (totalLen t) x‖) :=
        mul_le_mul_of_nonneg_left (norm_mulVec_le_opNormInf _ _) (opNormInf_nonneg _)
    _ ≤ ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) *
          ((((d : ℝ) - 1) * (0.120 * (2 : ℝ) ^ (-(ω : ℤ)))) * ‖x‖) :=
        mul_le_mul (hinv.trans hle) (mul_le_mul hAB hZx (norm_nonneg _) (mul_nonneg hd1 hε0))
          (mul_nonneg (opNormInf_nonneg _) (norm_nonneg _)) hRt
    _ = 0.120 * ((d : ℝ) - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) *
          (2 : ℝ) ^ (-(ω : ℤ)) * ‖x‖ := by
        ring

/-- Lemma 4.6 (bridge Lemma C)(vi) (`lem:bridge-C`): `‖(B_2⋯B_d)^{-1}‖_∞ ≤ R/t_1`, the first two claims
of Lemma 4.4 (bridge Lemma B)(vi). -/
theorem lemmaC_vi_of (hvi : LemmaB_viStmt) : LemmaC_viStmt := by
  intro d ω hω α hα t ht hd
  obtain ⟨h1, h2, -⟩ := hvi ω hω α hα t ht hd 0
  exact h1.trans h2

end SubNLogN.Math.Bridge
