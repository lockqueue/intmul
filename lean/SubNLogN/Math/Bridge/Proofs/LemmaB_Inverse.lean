import SubNLogN.Math.Bridge.LemmaB_Ops

/-!
# Bridge: Lemma 4.4 (bridge Lemma B)(v), the cyclic bidiagonal inverse (`lem:bridge-B`)

Proved here (names `LemmaB*`/`lemmaB*` reflect an earlier draft (bridge Lemma B), kept for stability):

* `lemmaB_v_of : LemmaB_ivStmt → LemmaB_vStmt`. For reals `x = c_0 ≥ 0`, `y = c_1 ≥ 0`, `x ≠ y`
  and every cycle length `L ≥ 1`, `B = x·I + y·S` (`(SZ)_j = Z_{(j-1) mod L}`, `S^L = I`) has the
  explicit inverse `(B^{-1})_{j j'} = D^{-1} (-y)^m x^{L-1-m}`, `m = (j - j') mod L`,
  `D = x^L - (-y)^L` (the geometric series of the paper, Lemma 4.4 (`lem:bridge-B`)(v), written without
  dividing by `c_max`). We check `B · B^{-1} = 1` entrywise (`cycBidiag_mul_cycInv`) and use
  `Matrix.inv_eq_right_inv`. Every row of `B^{-1}` has absolute sum `G/|D|` with
  `G = ∑_{m<L} y^m x^{L-1-m}`, and `G·|x - y| = |x^L - y^L| ≤ |D|`, with equality for even `L`
  (`D = x^L - y^L`); for odd `L`, `|D| = x^L + y^L`. Hence `‖B^{-1}‖_∞ ≤ 1/|x - y|`, with equality
  for even `L`. The degenerate cycle `L = 1` (`shiftFin j (-1) = j`, `B = [x + y]`) is covered by
  the same formula (`B^{-1} = [1/(x+y)]`). Nonnegativity of `c_0, c_1` is read off the integral
  defining `kernelG` (no `KernelG_posStmt` needed); `|c_0 - c_1| ≥ 7/(4t)` is B(iv).
* `lemmaB_v_axis_of : LemmaB_vStmt → LemmaB_v_axisStmt`. With `s = R/A_h = aliasStep t i` and
  `L = A_h = prefixProd t i` (`R = s·L`), `f ↦ (f - s) mod R` keeps `f mod s` and moves the cycle
  position `⌊f/s⌋ ∈ [L]` to `⌊f/s⌋ - 1 mod L`; the frequency digit `u_h(f) = (f mod s)/(R/A_{h+1})`
  is constant along each cycle. So `B_h` restricted to a residue class mod `s` is
  `cycBidiag c_0 c_1 L` with that class's coefficients; the explicit inverse `truncInv` is the
  inverse of that block (from B(v)) on each class and `0` across classes. Each row of `truncInv`
  is (an injective reindexing of) a row of a block inverse, so `‖B_h^{-1}‖_∞ ≤ 4t_h/7` by B(v).
  The bound holds for every Lean axis `i` (also `i = 0`, where `L = 1`); evenness of `L` is not
  needed for the inequality.

The digit/length facts used are the `SubNLogN.Math.Common` contracts `encFreq_symm_apply` and
`prefixProd_mul_mul_suffixProd` (`Common/DFT.lean`).
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

namespace LemmaBInverse

/-! ### Row sums and `opNormInf` -/

section RowSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A uniform bound on the absolute row sums bounds `opNormInf`. -/
theorem opNormInf_toLin'_le_of_rowSum (N : Matrix ι ι ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ∑ j, ‖N i j‖ ≤ C) : opNormInf (Matrix.toLin' N) ≤ C := by
  unfold opNormInf
  rw [LinearMap.toMatrix'_toLin']
  have hsup : (Finset.univ.sup fun i => ∑ j, ‖N i j‖₊) ≤ (⟨C, hC⟩ : NNReal) := by
    refine Finset.sup_le fun i _ => ?_
    have h' : ((∑ j, ‖N i j‖₊ : NNReal) : ℝ) ≤ ((⟨C, hC⟩ : NNReal) : ℝ) := by
      rw [NNReal.coe_sum]; exact h i
    exact NNReal.coe_le_coe.1 h'
  exact NNReal.coe_le_coe.2 hsup

/-- Every absolute row sum is at most `opNormInf`. -/
theorem rowSum_le_opNormInf_toLin' (N : Matrix ι ι ℂ) (i : ι) :
    ∑ j, ‖N i j‖ ≤ opNormInf (Matrix.toLin' N) := by
  unfold opNormInf
  rw [LinearMap.toMatrix'_toLin']
  have h : (∑ j, ‖N i j‖₊) ≤ Finset.univ.sup fun i => ∑ j, ‖N i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖N i j‖₊) (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.2 h
  rw [NNReal.coe_sum] at h'
  exact h'

/-- If all absolute row sums equal `C`, then `opNormInf = C`. -/
theorem opNormInf_toLin'_eq_of_rowSum [Nonempty ι] (N : Matrix ι ι ℂ) {C : ℝ}
    (h : ∀ i, ∑ j, ‖N i j‖ = C) : opNormInf (Matrix.toLin' N) = C := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hC : 0 ≤ C := by
    rw [← h i0]
    exact Finset.sum_nonneg fun j _ => norm_nonneg _
  refine le_antisymm (opNormInf_toLin'_le_of_rowSum N hC fun i => (h i).le) ?_
  rw [← h i0]
  exact rowSum_le_opNormInf_toLin' N i0

end RowSum

/-- A sum over `a` of `g (φ a)` restricted to `p a` is at most `∑_b g b` when `g ≥ 0` and `φ` is
injective on `{p}`. -/
theorem sum_ite_comp_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (p : α → Prop)
    [DecidablePred p] (φ : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b)
    (hinj : ∀ a a', p a → p a' → φ a = φ a' → a = a') :
    ∑ a, (if p a then g (φ a) else 0) ≤ ∑ b, g b := by
  rw [← Finset.sum_filter, ← Finset.sum_image (f := g) (s := Finset.univ.filter p) (g := φ)]
  · exact Finset.sum_le_univ_sum_of_nonneg hg
  · intro a ha a' ha' h
    exact hinj a a' (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 ha').2 h

/-! ### Index arithmetic -/

/-- `a mod L` for `-L ≤ a < L`. -/
theorem emod_eq_ite {a L : ℤ} (h1 : -L ≤ a) (h2 : a < L) :
    a % L = if 0 ≤ a then a else a + L := by
  split_ifs with h
  · exact Int.emod_eq_of_lt h h2
  · rw [← Int.add_mul_emod_self_right a 1 L, one_mul]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- `shiftFin f (-s)` for `s ≤ R`: `f - s`, wrapping around to `f + R - s`. -/
theorem shiftFin_neg_val {R : ℕ} (f : Fin R) {s : ℕ} (hs : s ≤ R) :
    ((shiftFin f (-(s : ℤ)) : Fin R) : ℕ) =
      if s ≤ (f : ℕ) then (f : ℕ) - s else (f : ℕ) + R - s := by
  have hf := f.isLt
  show ((((f : ℕ) : ℤ) + -((s : ℕ) : ℤ)) % ((R : ℕ) : ℤ)).toNat = _
  rw [emod_eq_ite (by omega) (by omega)]
  split_ifs <;> omega

/-- `shiftFin j (-1)` on a cycle `Fin L`: `j - 1`, or `L - 1` for `j = 0` (so `j` itself when
`L = 1`). -/
theorem shiftFin_neg_one_val {L : ℕ} (j : Fin L) :
    ((shiftFin j (-1) : Fin L) : ℕ) = if (j : ℕ) = 0 then L - 1 else (j : ℕ) - 1 := by
  have hj := j.isLt
  show ((((j : ℕ) : ℤ) + -1) % ((L : ℕ) : ℤ)).toNat = _
  rw [emod_eq_ite (by omega) (by omega)]
  split_ifs <;> omega

/-! ### The cyclic bidiagonal operator and its explicit inverse -/

/-- `(j - j') mod L` for `j, j' ∈ Fin L`. -/
def cycDist {L : ℕ} (j j' : Fin L) : ℕ :=
  if (j' : ℕ) ≤ (j : ℕ) then (j : ℕ) - (j' : ℕ) else (j : ℕ) + L - (j' : ℕ)

theorem cycDist_lt {L : ℕ} (j j' : Fin L) : cycDist j j' < L := by
  have := j.isLt; have := j'.isLt
  unfold cycDist; split_ifs <;> omega

theorem cycDist_self {L : ℕ} (j : Fin L) : cycDist j j = 0 := by
  unfold cycDist; simp

theorem cycDist_shift_self {L : ℕ} (j : Fin L) : cycDist (shiftFin j (-1)) j = L - 1 := by
  have := j.isLt
  unfold cycDist; rw [shiftFin_neg_one_val]; split_ifs <;> omega

theorem cycDist_shift_of_ne {L : ℕ} {j k : Fin L} (h : j ≠ k) :
    cycDist (shiftFin j (-1)) k + 1 = cycDist j k := by
  have := j.isLt; have := k.isLt
  have h' : (j : ℕ) ≠ (k : ℕ) := fun e => h (Fin.ext e)
  unfold cycDist; rw [shiftFin_neg_one_val]; split_ifs <;> omega

theorem cycDist_injective {L : ℕ} (j : Fin L) : Function.Injective (cycDist j) := by
  intro a b hab
  have := j.isLt; have := a.isLt; have := b.isLt
  unfold cycDist at hab
  apply Fin.ext
  split_ifs at hab <;> omega

/-- The explicit inverse of `cycBidiag x y L`: entries `D⁻¹ (-y)^m x^{L-1-m}`, `m = (j - j') mod L`,
`D = x^L - (-y)^L`. -/
noncomputable def cycInv (x y : ℂ) (L : ℕ) : Matrix (Fin L) (Fin L) ℂ :=
  fun j j' => (x ^ L - (-y) ^ L)⁻¹ * ((-y) ^ cycDist j j' * x ^ (L - 1 - cycDist j j'))

theorem cycBidiag_mul_apply (x y : ℂ) {L : ℕ} (P : Matrix (Fin L) (Fin L) ℂ) (j k : Fin L) :
    (cycBidiag x y L * P) j k = x * P j k + y * P (shiftFin j (-1)) k := by
  simp only [Matrix.mul_apply, cycBidiag, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `B · B^{-1} = 1` for the explicit inverse (any `L ≥ 1`, any `x, y` with `D ≠ 0`). -/
theorem cycBidiag_mul_cycInv (x y : ℂ) {L : ℕ} (hL : 1 ≤ L) (hD : x ^ L - (-y) ^ L ≠ 0) :
    cycBidiag x y L * cycInv x y L = 1 := by
  ext j k
  rw [cycBidiag_mul_apply]
  simp only [cycInv]
  by_cases hjk : j = k
  · subst hjk
    rw [cycDist_shift_self, cycDist_self, Matrix.one_apply_eq, Nat.sub_self, Nat.sub_zero,
      pow_zero, pow_zero, one_mul, mul_one]
    obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    linear_combination inv_mul_cancel₀ hD
  · rw [Matrix.one_apply_ne hjk]
    have h1 := cycDist_shift_of_ne hjk
    have h2 := cycDist_lt j k
    rw [← h1]
    obtain ⟨e, he⟩ : ∃ e, L - 1 - cycDist (shiftFin j (-1)) k = e + 1 :=
      ⟨L - 1 - cycDist (shiftFin j (-1)) k - 1, by omega⟩
    have he' : L - 1 - (cycDist (shiftFin j (-1)) k + 1) = e := by omega
    rw [he, he']
    ring

/-- Every absolute row sum of the explicit inverse is `|D|⁻¹ ∑_{m<L} |y|^m |x|^{L-1-m}`. -/
theorem cycInv_rowSum (x y : ℂ) {L : ℕ} (j : Fin L) :
    ∑ j', ‖cycInv x y L j j'‖ =
      ‖x ^ L - (-y) ^ L‖⁻¹ * ∑ m ∈ Finset.range L, ‖y‖ ^ m * ‖x‖ ^ (L - 1 - m) := by
  simp only [cycInv, norm_mul, norm_inv, norm_pow, norm_neg]
  rw [← Finset.mul_sum]
  congr 1
  have hbij : Function.Bijective (fun j' : Fin L => (⟨cycDist j j', cycDist_lt j j'⟩ : Fin L)) :=
    Finite.injective_iff_bijective.1 fun a b hab => cycDist_injective j (congrArg Fin.val hab)
  rw [← Fin.sum_univ_eq_sum_range (fun m => ‖y‖ ^ m * ‖x‖ ^ (L - 1 - m)) L]
  exact hbij.sum_comp (fun m : Fin L => ‖y‖ ^ (m : ℕ) * ‖x‖ ^ (L - 1 - (m : ℕ)))

/-- The real estimate behind B(v): for `x, y ≥ 0`, `x ≠ y`, `L ≥ 1`, `D = x^L - (-y)^L ≠ 0` and
`|D|⁻¹ ∑_{m<L} y^m x^{L-1-m} ≤ 1/|x - y|`, with equality for even `L`. -/
theorem real_rowSum_bound {c0 c1 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (hne : c0 ≠ c1) {L : ℕ}
    (hL : 1 ≤ L) :
    c0 ^ L - (-c1) ^ L ≠ 0 ∧
      |c0 ^ L - (-c1) ^ L|⁻¹ * (∑ m ∈ Finset.range L, c1 ^ m * c0 ^ (L - 1 - m)) ≤
        1 / |c0 - c1| ∧
      (Even L → |c0 ^ L - (-c1) ^ L|⁻¹ * (∑ m ∈ Finset.range L, c1 ^ m * c0 ^ (L - 1 - m)) =
        1 / |c0 - c1|) := by
  set G := ∑ m ∈ Finset.range L, c1 ^ m * c0 ^ (L - 1 - m) with hGdef
  set D := c0 ^ L - (-c1) ^ L with hDdef
  have hG : G * (c1 - c0) = c1 ^ L - c0 ^ L := geom_sum₂_mul c1 c0 L
  have hGnn : 0 ≤ G := Finset.sum_nonneg fun m _ => mul_nonneg (pow_nonneg h1 _) (pow_nonneg h0 _)
  have hGabs : G * |c0 - c1| = |c0 ^ L - c1 ^ L| := by
    rw [abs_sub_comm c0 c1, abs_sub_comm (c0 ^ L) (c1 ^ L), ← hG, abs_mul, abs_of_nonneg hGnn]
  have hpow : c0 ^ L ≠ c1 ^ L := fun h => hne ((pow_left_inj₀ h0 h1 (by omega)).1 h)
  have hpos : 0 < |c0 ^ L - c1 ^ L| := abs_pos.2 (sub_ne_zero.2 hpow)
  have hDge : |c0 ^ L - c1 ^ L| ≤ |D| := by
    rcases Nat.even_or_odd L with he | ho
    · rw [hDdef, he.neg_pow]
    · rw [hDdef, ho.neg_pow, sub_neg_eq_add,
        abs_of_nonneg (add_nonneg (pow_nonneg h0 _) (pow_nonneg h1 _))]
      exact abs_sub_le_iff.2 ⟨by linarith [pow_nonneg h1 L], by linarith [pow_nonneg h0 L]⟩
  have hD : D ≠ 0 := fun h => by rw [h, abs_zero] at hDge; linarith
  have hDpos : 0 < |D| := abs_pos.2 hD
  have hsub : 0 < |c0 - c1| := abs_pos.2 (sub_ne_zero.2 hne)
  refine ⟨hD, ?_, fun he => ?_⟩
  · rw [inv_mul_eq_div, div_le_div_iff₀ hDpos hsub, one_mul, hGabs]
    exact hDge
  · have hDeq : |D| = |c0 ^ L - c1 ^ L| := by rw [hDdef, he.neg_pow]
    rw [inv_mul_eq_div, div_eq_div_iff hDpos.ne' hsub.ne', one_mul, hGabs, hDeq]

/-- B(v) for real coefficients `c_0, c_1 ≥ 0`, `c_0 ≠ c_1`, on a cycle of any length `L ≥ 1`:
`cycBidiag c_0 c_1 L` is invertible, `‖B^{-1}‖_∞ ≤ 1/|c_0 - c_1|`, with equality for even `L`. -/
theorem cycBidiag_inverse_real {c0 c1 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (hne : c0 ≠ c1) {L : ℕ}
    (hL : 1 ≤ L) :
    IsUnit (cycBidiag (c0 : ℂ) (c1 : ℂ) L).det ∧
      opNormInf (Matrix.toLin' (cycBidiag (c0 : ℂ) (c1 : ℂ) L)⁻¹) ≤ 1 / |c0 - c1| ∧
      (Even L →
        opNormInf (Matrix.toLin' (cycBidiag (c0 : ℂ) (c1 : ℂ) L)⁻¹) = 1 / |c0 - c1|) := by
  obtain ⟨hD, hle, heq⟩ := real_rowSum_bound h0 h1 hne hL
  have hDc : (c0 : ℂ) ^ L - (-(c1 : ℂ)) ^ L ≠ 0 := by
    exact_mod_cast Complex.ofReal_ne_zero.2 hD
  have hmul := cycBidiag_mul_cycInv (c0 : ℂ) (c1 : ℂ) hL hDc
  have hinv : (cycBidiag (c0 : ℂ) (c1 : ℂ) L)⁻¹ = cycInv (c0 : ℂ) (c1 : ℂ) L :=
    Matrix.inv_eq_right_inv hmul
  have hn : ‖(c0 : ℂ) ^ L - (-(c1 : ℂ)) ^ L‖ = |c0 ^ L - (-c1) ^ L| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, Complex.ofReal_pow,
      Complex.ofReal_pow, Complex.ofReal_neg]
  have hrow : ∀ j : Fin L, ∑ j', ‖cycInv (c0 : ℂ) (c1 : ℂ) L j j'‖ =
      |c0 ^ L - (-c1) ^ L|⁻¹ * ∑ m ∈ Finset.range L, c1 ^ m * c0 ^ (L - 1 - m) := by
    intro j
    rw [cycInv_rowSum, hn, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h0,
      Real.norm_of_nonneg h1]
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hnorm := opNormInf_toLin'_eq_of_rowSum _ hrow
  refine ⟨Matrix.isUnit_det_of_right_inverse hmul, ?_, fun he => ?_⟩
  · rw [hinv, hnorm]; exact hle
  · rw [hinv, hnorm]; exact heq he

/-- `G = kernelG α ≥ 0` for `α ≥ 0` (integral of a nonnegative function over `[ξ-½, ξ+½]`). -/
theorem kernelG_nonneg {α : ℝ} (hα : 0 ≤ α) (ξ : ℝ) : 0 ≤ kernelG α ξ := by
  unfold kernelG
  exact intervalIntegral.integral_nonneg (by linarith) fun v _ =>
    mul_nonneg hα (Real.exp_pos _).le

/-- An admissible `α` is nonnegative. -/
theorem alpha_nonneg_of_admissible {ω : ℕ} {α : ℝ} (hα : AlphaAdmissible ω α) : 0 ≤ α :=
  le_trans (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hα.1

end LemmaBInverse

open LemmaBInverse in
/-- **Lemma 4.4 (bridge Lemma B)(v)** (`lem:bridge-B`), from B(iv). -/
theorem lemmaB_v_of (hiv : LemmaB_ivStmt) : LemmaB_vStmt := by
  intro ω hω α hα t ht u hu L hL c0 c1
  have hα0 : 0 ≤ α := alpha_nonneg_of_admissible hα
  have h0 : 0 ≤ c0 := kernelG_nonneg hα0 _
  have h1 : 0 ≤ c1 := kernelG_nonneg hα0 _
  have hsep : 7 / (4 * (t : ℝ)) ≤ |c0 - c1| := hiv ω hω α hα t ht u hu
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hsep_pos : 0 < 7 / (4 * (t : ℝ)) := by positivity
  have hne : c0 ≠ c1 := fun h => by rw [h, sub_self, abs_zero] at hsep; linarith
  obtain ⟨hunit, hle, heven⟩ := cycBidiag_inverse_real h0 h1 hne hL
  refine ⟨hunit, hle, ?_, heven⟩
  calc 1 / |c0 - c1| ≤ 1 / (7 / (4 * (t : ℝ))) := one_div_le_one_div_of_le hsep_pos hsep
    _ = 4 * (t : ℝ) / 7 := by rw [one_div_div]

namespace LemmaBInverse

variable {d : ℕ}

/-! ### The axis operator `B_h`: cycles of `f ↦ (f - R/A_h) mod R` -/

theorem prefixProd_pos {t : Fin d → ℕ} (ht : ShapeOK t) (k : ℕ) : 0 < prefixProd t k :=
  Finset.prod_pos fun l _ => by have := (ht l).1; omega

theorem suffixProd_pos {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) : 0 < suffixProd t i :=
  Finset.prod_pos fun l _ => by have := (ht l).1; omega

/-- `R/A_h = t_h · ∏_{l>h} t_l`. -/
theorem aliasStep_eq {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    aliasStep t i = t i * suffixProd t i := by
  unfold aliasStep
  rw [← prefixProd_mul_mul_suffixProd t i, mul_assoc]
  exact Nat.mul_div_cancel_left _ (prefixProd_pos ht i)

theorem aliasStep_pos {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) : 0 < aliasStep t i := by
  rw [aliasStep_eq ht i]
  exact Nat.mul_pos (by have := (ht i).1; omega) (suffixProd_pos ht i)

/-- `R = (R/A_h) · A_h`. -/
theorem totalLen_eq_mul {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    totalLen t = aliasStep t i * prefixProd t i := by
  rw [aliasStep_eq ht i, ← prefixProd_mul_mul_suffixProd t i]
  ring

/-- Subtracting `s` modulo `R = s·L` keeps the residue mod `s` and moves the quotient `⌊f/s⌋`
cyclically down by one. -/
theorem shift_mod_div {s L R f : ℕ} (hs : 0 < s) (hL : 0 < L) (hR : R = s * L) (hf : f < R) :
    (if s ≤ f then f - s else f + R - s) % s = f % s ∧
      (if s ≤ f then f - s else f + R - s) / s = if f / s = 0 then L - 1 else f / s - 1 := by
  subst hR
  by_cases h : s ≤ f
  · rw [if_pos h]
    obtain ⟨g, rfl⟩ : ∃ g, f = g + s := ⟨f - s, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mod_right, Nat.add_div_right g hs]
    simp
  · rw [if_neg h]
    obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
    have e : f + s * (K + 1) - s = f + s * K := by rw [mul_add_one]; omega
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hs,
      Nat.div_eq_of_lt (show f < s by omega)]
    simp

/-- The cycle position `⌊f/(R/A_h)⌋ ∈ [A_h]` of a frequency index `f`. -/
def qIdx {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t)) :
    Fin (prefixProd t i) :=
  ⟨(f : ℕ) / aliasStep t i, by
    rw [Nat.div_lt_iff_lt_mul (aliasStep_pos ht i)]
    have h : (f : ℕ) < aliasStep t i * prefixProd t i :=
      lt_of_lt_of_eq f.isLt (totalLen_eq_mul ht i)
    rw [Nat.mul_comm] at h
    exact h⟩

/-- `f ↦ (f - R/A_h) mod R` keeps `f mod (R/A_h)` and shifts the cycle position by `-1`. -/
theorem shiftFin_aliasStep {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t)) :
    ((shiftFin f (-(aliasStep t i : ℤ)) : Fin (totalLen t)) : ℕ) % aliasStep t i =
        (f : ℕ) % aliasStep t i ∧
      qIdx ht i (shiftFin f (-(aliasStep t i : ℤ))) = shiftFin (qIdx ht i f) (-1) := by
  have hs := aliasStep_pos ht i
  have hL := prefixProd_pos ht i
  have hR := totalLen_eq_mul ht i
  have hsR : aliasStep t i ≤ totalLen t := by
    rw [hR]; exact Nat.le_mul_of_pos_right _ hL
  have hval := shiftFin_neg_val f hsR
  obtain ⟨h1, h2⟩ := shift_mod_div hs hL hR f.isLt
  rw [← hval] at h1 h2
  refine ⟨h1, ?_⟩
  apply Fin.ext
  rw [shiftFin_neg_one_val]
  exact h2

/-- The frequency digit `u_h(f)` only depends on `f mod (R/A_h)`. -/
theorem encFreq_digit_eq {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t)) :
    (((encFreq t).symm f i : Fin (t i)) : ℕ) = ((f : ℕ) % aliasStep t i) / suffixProd t i := by
  rw [encFreq_symm_apply, aliasStep_eq ht i, Nat.mul_comm (t i), Nat.mod_mul_right_div_self]

/-- The sample point (hence `c_0, c_1`) is constant along the cycles of `B_h`. -/
theorem samplePt_shiftFin {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t)) :
    samplePt t i (shiftFin f (-(aliasStep t i : ℤ))) = samplePt t i f := by
  have h : (((encFreq t).symm (shiftFin f (-(aliasStep t i : ℤ))) i : Fin (t i)) : ℕ) =
      (((encFreq t).symm f i : Fin (t i)) : ℕ) := by
    rw [encFreq_digit_eq ht i, encFreq_digit_eq ht i, (shiftFin_aliasStep ht i f).1]
  unfold samplePt
  rw [h]

/-- The cyclic block of `B_h` through the row `f`: `cycBidiag c_0 c_1 A_h` with the coefficients
`c_0 = G(y)`, `c_1 = G(y-1)` of `f`'s sample point `y`. -/
noncomputable def axisBlock (α : ℝ) (t : Fin d → ℕ) (i : Fin d) (f : Fin (totalLen t)) :
    Matrix (Fin (prefixProd t i)) (Fin (prefixProd t i)) ℂ :=
  cycBidiag (kernelG α (samplePt t i f) : ℂ) (kernelG α (samplePt t i f - 1) : ℂ) (prefixProd t i)

/-- The inverse of `B_h`: on the residue class of `f` mod `R/A_h` it is the inverse of the class's
cyclic block (indexed by cycle positions `qIdx`), and `0` across classes. -/
noncomputable def truncInv (α : ℝ) {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    Matrix (Fin (totalLen t)) (Fin (totalLen t)) ℂ :=
  fun f f' => if (f : ℕ) % aliasStep t i = (f' : ℕ) % aliasStep t i then
    (axisBlock α t i f)⁻¹ (qIdx ht i f) (qIdx ht i f') else 0

theorem truncMatrix_mul_apply (α : ℝ) (t : Fin d → ℕ) (i : Fin d)
    (P : Matrix (Fin (totalLen t)) (Fin (totalLen t)) ℂ) (f k : Fin (totalLen t)) :
    (truncMatrix α t i * P) f k = (kernelG α (samplePt t i f) : ℂ) * P f k +
      (kernelG α (samplePt t i f - 1) : ℂ) * P (shiftFin f (-(aliasStep t i : ℤ))) k := by
  simp only [Matrix.mul_apply, truncMatrix, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem eq_of_mod_qIdx {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) {a b : Fin (totalLen t)}
    (hr : (a : ℕ) % aliasStep t i = (b : ℕ) % aliasStep t i) (hq : qIdx ht i a = qIdx ht i b) :
    a = b := by
  apply Fin.ext
  have hq' : (a : ℕ) / aliasStep t i = (b : ℕ) / aliasStep t i := congrArg Fin.val hq
  calc (a : ℕ) = aliasStep t i * ((a : ℕ) / aliasStep t i) + (a : ℕ) % aliasStep t i :=
        (Nat.div_add_mod _ _).symm
    _ = aliasStep t i * ((b : ℕ) / aliasStep t i) + (b : ℕ) % aliasStep t i := by rw [hq', hr]
    _ = b := Nat.div_add_mod _ _

/-- `B_h · truncInv = 1`, given that every cyclic block is invertible. -/
theorem truncMatrix_mul_truncInv {α : ℝ} {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d)
    (hunit : ∀ f, IsUnit (axisBlock α t i f).det) :
    truncMatrix α t i * truncInv α ht i = 1 := by
  ext f k
  rw [truncMatrix_mul_apply]
  obtain ⟨hmod, hq⟩ := shiftFin_aliasStep ht i f
  have hblock : axisBlock α t i (shiftFin f (-(aliasStep t i : ℤ))) = axisBlock α t i f := by
    simp only [axisBlock, samplePt_shiftFin ht i f]
  simp only [truncInv, hmod, hq, hblock]
  by_cases hr : (f : ℕ) % aliasStep t i = (k : ℕ) % aliasStep t i
  · rw [if_pos hr, if_pos hr]
    have hc : (axisBlock α t i f * (axisBlock α t i f)⁻¹) (qIdx ht i f) (qIdx ht i k) = _ :=
      cycBidiag_mul_apply _ _ _ _ _
    rw [Matrix.mul_nonsing_inv _ (hunit f)] at hc
    rw [← hc]
    by_cases hfk : f = k
    · rw [hfk, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · have hqne : qIdx ht i f ≠ qIdx ht i k := fun hqq => hfk (eq_of_mod_qIdx ht i hr hqq)
      rw [Matrix.one_apply_ne hfk, Matrix.one_apply_ne hqne]
  · rw [if_neg hr, if_neg hr, mul_zero, mul_zero, add_zero, Matrix.one_apply_ne]
    intro hfk
    exact hr (by rw [hfk])

end LemmaBInverse

open LemmaBInverse in
/-- **Lemma 4.4 (bridge Lemma B)(v), axis form** (`lem:bridge-B`), from B(v): `B_h` is invertible and
`‖B_h^{-1}‖_∞ ≤ 4t_h/7 ≤ t_h`. -/
theorem lemmaB_v_axis_of (hv : LemmaB_vStmt) : LemmaB_v_axisStmt := by
  intro d ω hω α hα t ht i _hi
  have hL := prefixProd_pos ht i
  have hrow : ∀ f : Fin (totalLen t), IsUnit (axisBlock α t i f).det ∧
      opNormInf (Matrix.toLin' (axisBlock α t i f)⁻¹) ≤ 4 * (t i : ℝ) / 7 := by
    intro f
    obtain ⟨h1, h2, h3, -⟩ := hv ω hω α hα (t i) (ht i)
      (((encFreq t).symm f i : Fin (t i)) : ℕ) ((encFreq t).symm f i).isLt (prefixProd t i) hL
    exact ⟨h1, h2.trans h3⟩
  have hmul := truncMatrix_mul_truncInv ht i (fun f => (hrow f).1)
  have hinv : (truncMatrix α t i)⁻¹ = truncInv α ht i := Matrix.inv_eq_right_inv hmul
  have ht0 : (0 : ℝ) ≤ t i := Nat.cast_nonneg _
  refine ⟨Matrix.isUnit_det_of_right_inverse hmul, ?_, by linarith⟩
  rw [hinv]
  refine opNormInf_toLin'_le_of_rowSum _ (by positivity) fun f => ?_
  calc ∑ f', ‖truncInv α ht i f f'‖
      = ∑ f' : Fin (totalLen t), (if (f : ℕ) % aliasStep t i = (f' : ℕ) % aliasStep t i then
          ‖(axisBlock α t i f)⁻¹ (qIdx ht i f) (qIdx ht i f')‖ else 0) := by
        refine Finset.sum_congr rfl fun f' _ => ?_
        simp only [truncInv]
        split_ifs <;> simp
    _ ≤ ∑ a, ‖(axisBlock α t i f)⁻¹ (qIdx ht i f) a‖ :=
        sum_ite_comp_le
          (fun f' : Fin (totalLen t) => (f : ℕ) % aliasStep t i = (f' : ℕ) % aliasStep t i)
          (qIdx ht i) (fun a => ‖(axisBlock α t i f)⁻¹ (qIdx ht i f) a‖) (fun _ => norm_nonneg _)
          (fun a a' (ha : (f : ℕ) % aliasStep t i = (a : ℕ) % aliasStep t i)
            (ha' : (f : ℕ) % aliasStep t i = (a' : ℕ) % aliasStep t i) hq =>
              eq_of_mod_qIdx ht i (ha.symm.trans ha') hq)
    _ ≤ opNormInf (Matrix.toLin' (axisBlock α t i f)⁻¹) := rowSum_le_opNormInf_toLin' _ _
    _ ≤ 4 * (t i : ℝ) / 7 := (hrow f).2

end SubNLogN.Math.Bridge
