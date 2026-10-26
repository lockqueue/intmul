import SubNLogN.Math.Bridge.Precision
import SubNLogN.Math.Bridge.Proofs.DeconvContract

/-!
# Proofs: the deconvolution chain (proof of Theorem 4.7 (`thm:bridge-precision`))

* `deconv_chain_of : … → Deconv_chainStmt`, conditional on Lemma 4.6 (bridge Lemma C)(iv), C(v), B(v), B(v)_axis.
  1. *Cycles.* For a deconvolution axis `h = i+1 ≥ 2` put `L = A_h = prefixProd t i` and
     `w = R/A_h = aliasStep t i = t_h · suffixProd t i`. The cycle of `f` in natural frequency
     order is `f_j = j·w + s` (`j < L`, `s = f mod w`), the frequency digit `u_h` is constant on
     it, and `f - w ≡ f_{j₀-1}` (`PrecisionDeconvProof.shiftFin_mul_val`).
  2. *Exact inverse per cycle.* `(B_h⁻¹ Y)_f = ((cycBidiag c₀ c₁ L)⁻¹ Y|_cycle)_{j₀}`. We prove
     `B_h Z = Y` for the cyclewise solution `Z` (B(v) for invertibility of each cycle block) and
     use invertibility of `B_h` (B(v)_axis).
  3. *Per stage.* `deconvAxisFixedR rr` runs the two-pass sweep of Lemma 4.6 (bridge Lemma C)(iv) on that cycle. The
     sweep only reads the cycle (`cycSweep_congr`), so C(iv) and C(v) for `γ̂` give
     `‖deconvAxisFixedR Y - B_h⁻¹ Y‖ ≤ 32 t_h² v max(1,‖Y‖)` and every output is
     `< 7 t_h max(1,‖Y‖)` (`deconvAxisFixed_stage`).
  4. *Chain.* `(B_2⋯B_d)⁻¹ = B_d⁻¹⋯B_2⁻¹` (`Matrix.mul_inv_rev`). An induction over the list of
     axes with invariant `‖Ẑ_m‖ ≤ K D_m (1 + 64 v S_m)` and error `≤ 64 v K D_m S_m`
     (`D_m = ∏ t`, `S_m = ∑ t` over the processed axes, `K = max(1,‖Y‖)`, `64 v S ≤ 1`) gives
     the paper's `E_solver ≤ 64 D v ∑_h t_h` (`chain_bound`). It uses `‖B_h⁻¹‖_∞ ≤ t_h`.
* `PrecisionDeconvProof.deconv_chain_list` also gives the intermediate-norm bound
  `‖Ẑ_l‖ ≤ max(1,‖Y‖) D_l (1 + 64 v S_l) ≤ 2 D_l max(1,‖Y‖)` for every list `l` of deconvolution
  axes (e.g. `(deconvOrder d).take m`), consumed by the widths table (`Proofs/Precision_Widths.lean`).

Everything is stated for an arbitrary nearest rounding `rr` (`IsNearestRounding rr`,
`Common/RoundNearest.lean`); `hrr` is only passed on to C(iv) and C(v).

Helpers live in `SubNLogN.Math.Bridge.PrecisionDeconvProof`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators Matrix

namespace PrecisionDeconvProof

variable {d : ℕ}

/-! ## Part 1: cycle coordinates of the alias step -/

theorem prefixProd_pos {t : Fin d → ℕ} (ht : ShapeOK t) (k : ℕ) : 0 < prefixProd t k :=
  Finset.prod_pos fun i _ => by have := (ht i).1; omega

theorem suffixProd_pos {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) : 0 < suffixProd t i :=
  Finset.prod_pos fun l _ => by have := (ht l).1; omega

theorem aliasStep_eq {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    aliasStep t i = t i * suffixProd t i := by
  unfold aliasStep
  rw [← prefixProd_mul_mul_suffixProd t i, mul_assoc]
  exact Nat.mul_div_cancel_left _ (prefixProd_pos ht i)

theorem aliasStep_pos {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) : 0 < aliasStep t i := by
  rw [aliasStep_eq ht i]
  exact Nat.mul_pos (by have := (ht i).1; omega) (suffixProd_pos ht i)

theorem prefixProd_mul_aliasStep {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    prefixProd t i * aliasStep t i = totalLen t := by
  rw [aliasStep_eq ht i, ← mul_assoc, prefixProd_mul_mul_suffixProd]

/-- Integer core of the cycle arithmetic: for `f < L w`,
`(f + n w) mod Lw = ((⌊f/w⌋ + n) mod L)·w + (f mod w)`. -/
theorem toNat_emod_cycle (f w L R : ℕ) (n : ℤ) (hw : 0 < w) (hL : 0 < L) (hR : R = L * w) :
    (((f : ℤ) + n * (w : ℤ)) % (R : ℤ)).toNat =
      ((((f / w : ℕ) : ℤ) + n) % (L : ℤ)).toNat * w + f % w := by
  subst hR
  set J : ℤ := ((f / w : ℕ) : ℤ) + n with hJ
  have h1 : (f : ℤ) = ((f / w : ℕ) : ℤ) * (w : ℤ) + ((f % w : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod' f w).symm
  have h2 : J % (L : ℤ) + (L : ℤ) * (J / (L : ℤ)) = J := Int.emod_add_mul_ediv J L
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  have h0 : 0 ≤ J % (L : ℤ) := Int.emod_nonneg J hL'.ne'
  have hlt : J % (L : ℤ) < L := Int.emod_lt_of_pos J hL'
  have hs : ((f % w : ℕ) : ℤ) < w := by exact_mod_cast Nat.mod_lt f hw
  have hs0 : (0 : ℤ) ≤ ((f % w : ℕ) : ℤ) := Int.natCast_nonneg _
  have h3 : (f : ℤ) + n * (w : ℤ) =
      (J % (L : ℤ) * w + ((f % w : ℕ) : ℤ)) + (J / (L : ℤ)) * ((L * w : ℕ) : ℤ) := by
    have h4 : (f : ℤ) + n * (w : ℤ) = J * w + ((f % w : ℕ) : ℤ) := by
      rw [h1, hJ]; ring
    rw [h4]
    conv_lhs => rw [← h2]
    push_cast
    ring
  rw [h3, Int.add_mul_emod_self_right]
  have h5 : J % (L : ℤ) * w + ((f % w : ℕ) : ℤ) < ((L * w : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    nlinarith [mul_le_mul_of_nonneg_right (show J % (L : ℤ) + 1 ≤ L by omega) hw'.le]
  rw [Int.emod_eq_of_lt (add_nonneg (mul_nonneg h0 hw'.le) hs0) h5]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, J % (L : ℤ) = (a : ℤ) :=
    ⟨(J % (L : ℤ)).toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [ha, Int.toNat_natCast]
  have h6 : (a : ℤ) * (w : ℤ) + ((f % w : ℕ) : ℤ) = ((a * w + f % w : ℕ) : ℤ) := by
    push_cast; ring
  rw [h6, Int.toNat_natCast]

/-- Shifting by a multiple of `w` moves along the cycle. -/
theorem shiftFin_mul_val {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t))
    (n : ℤ) :
    ((shiftFin f (n * (aliasStep t i : ℤ)) : Fin (totalLen t)) : ℕ) =
      (((((f : ℕ) / aliasStep t i : ℕ) : ℤ) + n) % (prefixProd t i : ℤ)).toNat *
        aliasStep t i + (f : ℕ) % aliasStep t i :=
  toNat_emod_cycle f (aliasStep t i) (prefixProd t i) (totalLen t) n (aliasStep_pos ht i)
    (prefixProd_pos ht i) (prefixProd_mul_aliasStep ht i).symm

/-- The cycle elements `f_j = j w + s`. -/
theorem shiftFin_cycle_val {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t))
    (j : ℕ) (hj : j < prefixProd t i) :
    ((shiftFin f (((j : ℤ) - (((f : ℕ) / aliasStep t i : ℕ) : ℤ)) * (aliasStep t i : ℤ)) :
      Fin (totalLen t)) : ℕ) = j * aliasStep t i + (f : ℕ) % aliasStep t i := by
  rw [shiftFin_mul_val ht i f]
  have h1 : (((f : ℕ) / aliasStep t i : ℕ) : ℤ) +
      ((j : ℤ) - (((f : ℕ) / aliasStep t i : ℕ) : ℤ)) = (j : ℤ) := by ring
  rw [h1, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hj), Int.toNat_natCast]

theorem shiftFin_mul_mod {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t))
    (n : ℤ) :
    ((shiftFin f (n * (aliasStep t i : ℤ)) : Fin (totalLen t)) : ℕ) % aliasStep t i =
      (f : ℕ) % aliasStep t i := by
  rw [shiftFin_mul_val ht i f, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem shiftFin_mul_div {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t))
    (n : ℤ) :
    ((shiftFin f (n * (aliasStep t i : ℤ)) : Fin (totalLen t)) : ℕ) / aliasStep t i =
      (((((f : ℕ) / aliasStep t i : ℕ) : ℤ) + n) % (prefixProd t i : ℤ)).toNat := by
  rw [shiftFin_mul_val ht i f]
  have hw := aliasStep_pos ht i
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (Nat.mod_lt _ hw), zero_add]

theorem shiftFin_zero_eq {R : ℕ} (f : Fin R) : shiftFin f 0 = f := by
  apply Fin.ext
  have h1 : ((f : ℕ) : ℤ) % (R : ℤ) = (f : ℕ) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast f.isLt)
  show ((((f : ℕ) : ℤ) + 0) % (R : ℤ)).toNat = (f : ℕ)
  rw [add_zero, h1, Int.toNat_natCast]

/-- The frequency digit `u_h` only depends on `f mod w`. -/
theorem digit_eq_of_mod {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) {g g' : Fin (totalLen t)}
    (h : (g : ℕ) % aliasStep t i = (g' : ℕ) % aliasStep t i) :
    (encFreq t).symm g i = (encFreq t).symm g' i := by
  apply Fin.ext
  rw [encFreq_symm_apply, encFreq_symm_apply]
  have key : ∀ x : ℕ, (x / suffixProd t i) % t i =
      ((x % aliasStep t i) / suffixProd t i) % t i := by
    intro x
    have hS := suffixProd_pos ht i
    have hx : x = x % aliasStep t i + (t i * (x / aliasStep t i)) * suffixProd t i := by
      have h0 := Nat.mod_add_div x (aliasStep t i)
      rw [aliasStep_eq ht i] at h0 ⊢
      calc x = x % (t i * suffixProd t i) + t i * suffixProd t i * (x / (t i * suffixProd t i)) :=
            h0.symm
        _ = _ := by ring
    conv_lhs => rw [hx]
    rw [Nat.add_mul_div_right _ _ hS, Nat.add_mul_mod_self_left]
  rw [key (g : ℕ), key (g' : ℕ), h]

theorem samplePt_eq_of_mod {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) {g g' : Fin (totalLen t)}
    (h : (g : ℕ) % aliasStep t i = (g' : ℕ) % aliasStep t i) :
    samplePt t i g = samplePt t i g' := by
  unfold samplePt
  rw [digit_eq_of_mod ht i h]

/-- Position `j₀ = ⌊f/w⌋ < L` of `f` on its cycle. -/
theorem cycPos_lt {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (f : Fin (totalLen t)) :
    (f : ℕ) / aliasStep t i < prefixProd t i := by
  apply Nat.div_lt_of_lt_mul
  rw [mul_comm, prefixProd_mul_aliasStep ht i]
  exact f.isLt

/-- The cycle of `f`, read from `j = 0`, as a vector of length `L` (the function passed to the
sweep by `deconvAxisFixed`, restricted to `j < L`). -/
def cycVec (t : Fin d → ℕ) (i : Fin d) (Y : Fin (totalLen t) → ℂ) (f : Fin (totalLen t)) :
    Fin (prefixProd t i) → ℂ :=
  fun j => Y (shiftFin f ((((j : ℕ) : ℤ) - (((f : ℕ) / aliasStep t i : ℕ) : ℤ)) *
    (aliasStep t i : ℤ)))

theorem cycVec_eq_of_mod {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) (Y : Fin (totalLen t) → ℂ)
    {g g' : Fin (totalLen t)} (h : (g : ℕ) % aliasStep t i = (g' : ℕ) % aliasStep t i) :
    cycVec t i Y g = cycVec t i Y g' := by
  funext j
  unfold cycVec
  congr 1
  apply Fin.ext
  rw [shiftFin_cycle_val ht i g j j.isLt, shiftFin_cycle_val ht i g' j j.isLt, h]

theorem norm_cycVec_le (t : Fin d → ℕ) (i : Fin d) (Y : Fin (totalLen t) → ℂ)
    (f : Fin (totalLen t)) : ‖cycVec t i Y f‖ ≤ ‖Y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2 fun _ => norm_le_pi_norm Y _

/-! ## Part 2: the exact inverse of `B_h` acts cycle by cycle -/

theorem truncMatrix_mulVec_apply (α : ℝ) (t : Fin d → ℕ) (i : Fin d) (Z : Fin (totalLen t) → ℂ)
    (f : Fin (totalLen t)) :
    (truncMatrix α t i *ᵥ Z) f = (kernelG α (samplePt t i f) : ℂ) * Z f +
      (kernelG α (samplePt t i f - 1) : ℂ) * Z (shiftFin f (-(aliasStep t i : ℤ))) := by
  simp only [Matrix.mulVec, dotProduct, truncMatrix, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cycBidiag_mulVec_apply (c0 c1 : ℂ) (L : ℕ) (z : Fin L → ℂ) (j : Fin L) :
    (cycBidiag c0 c1 L *ᵥ z) j = c0 * z j + c1 * z (shiftFin j (-1)) := by
  simp only [Matrix.mulVec, dotProduct, cycBidiag, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Under Lemma 4.6 (bridge Lemma C)'s hypotheses `α` satisfies eq. (`eq:alpha`). -/
theorem alphaAdmissible_of_params {P ω : ℕ} {α : ℝ} (hC : LemmaCParams P ω α) :
    AlphaAdmissible ω α := by
  obtain ⟨_, _, _, hα, lamG, hl1, hl4, hα2⟩ := hC
  have hX0 : 0 ≤ (ω : ℝ) * Real.log 2 / Real.pi :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg ω) (Real.log_nonneg one_le_two)) Real.pi_pos.le
  unfold AlphaAdmissible
  set s := Real.sqrt ((ω : ℝ) * Real.log 2 / Real.pi) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = (ω : ℝ) * Real.log 2 / Real.pi := Real.sq_sqrt hX0
  have hl1' : (1 : ℝ) ≤ lamG := by exact_mod_cast hl1
  have hl4' : (lamG : ℝ) ≤ 4 := by exact_mod_cast hl4
  have hα2' : α ^ 2 = 4 * (lamG : ℝ) * s ^ 2 := by rw [hα2, hss]; ring
  refine ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hl1' (sq_nonneg s)]
  · nlinarith [mul_le_mul_of_nonneg_right hl4' (sq_nonneg s)]

/-- **Exact inverse per cycle**: `(B_h⁻¹ Y)_f = ((cycBidiag c₀ c₁ L)⁻¹ (Y on the cycle of f))_{j₀}`. -/
theorem truncMatrix_inv_mulVec_apply (hBv : LemmaB_vStmt) (hBax : LemmaB_v_axisStmt)
    {ω : ℕ} (hω : 8 ≤ ω) {α : ℝ} (hα : AlphaAdmissible ω α) {t : Fin d → ℕ} (ht : ShapeOK t)
    {i : Fin d} (hi : (i : ℕ) ≠ 0) (Y : Fin (totalLen t) → ℂ) (f : Fin (totalLen t)) :
    ((truncMatrix α t i)⁻¹ *ᵥ Y) f =
      ((cycBidiag (kernelG α (samplePt t i f) : ℂ) (kernelG α (samplePt t i f - 1) : ℂ)
          (prefixProd t i))⁻¹ *ᵥ cycVec t i Y f) ⟨(f : ℕ) / aliasStep t i, cycPos_lt ht i f⟩ := by
  set Z : Fin (totalLen t) → ℂ := fun g =>
    ((cycBidiag (kernelG α (samplePt t i g) : ℂ) (kernelG α (samplePt t i g - 1) : ℂ)
      (prefixProd t i))⁻¹ *ᵥ cycVec t i Y g) ⟨(g : ℕ) / aliasStep t i, cycPos_lt ht i g⟩ with hZ
  have hunitC : ∀ g : Fin (totalLen t), IsUnit (cycBidiag (kernelG α (samplePt t i g) : ℂ)
      (kernelG α (samplePt t i g - 1) : ℂ) (prefixProd t i)).det := fun g =>
    (hBv ω hω α hα (t i) (ht i) _ ((encFreq t).symm g i).isLt (prefixProd t i)
      (prefixProd_pos ht i)).1
  have hBZ : truncMatrix α t i *ᵥ Z = Y := by
    funext g
    rw [truncMatrix_mulVec_apply]
    have hneg : -(aliasStep t i : ℤ) = (-1) * (aliasStep t i : ℤ) := by ring
    have hgm_mod : ((shiftFin g (-(aliasStep t i : ℤ)) : Fin (totalLen t)) : ℕ) % aliasStep t i =
        (g : ℕ) % aliasStep t i := by
      rw [hneg]; exact shiftFin_mul_mod ht i g (-1)
    have hs := samplePt_eq_of_mod ht i hgm_mod
    have hc := cycVec_eq_of_mod ht i Y hgm_mod
    have hpos : (⟨((shiftFin g (-(aliasStep t i : ℤ)) : Fin (totalLen t)) : ℕ) / aliasStep t i,
        cycPos_lt ht i _⟩ : Fin (prefixProd t i)) =
        shiftFin (⟨(g : ℕ) / aliasStep t i, cycPos_lt ht i g⟩ : Fin (prefixProd t i)) (-1) := by
      apply Fin.ext
      show ((shiftFin g (-(aliasStep t i : ℤ)) : Fin (totalLen t)) : ℕ) / aliasStep t i = _
      rw [hneg, shiftFin_mul_div ht i g (-1)]
      rfl
    simp only [hZ]
    rw [hs, hc, hpos]
    set C := cycBidiag (kernelG α (samplePt t i g) : ℂ) (kernelG α (samplePt t i g - 1) : ℂ)
      (prefixProd t i) with hC
    have hrow := cycBidiag_mulVec_apply (kernelG α (samplePt t i g) : ℂ)
      (kernelG α (samplePt t i g - 1) : ℂ) (prefixProd t i) (C⁻¹ *ᵥ cycVec t i Y g)
      ⟨(g : ℕ) / aliasStep t i, cycPos_lt ht i g⟩
    rw [← hC] at hrow
    rw [← hrow, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hunitC g), Matrix.one_mulVec]
    show Y (shiftFin g _) = Y g
    have h0 : ((((⟨(g : ℕ) / aliasStep t i, cycPos_lt ht i g⟩ : Fin (prefixProd t i)) : ℕ) : ℤ) -
        (((g : ℕ) / aliasStep t i : ℕ) : ℤ)) * (aliasStep t i : ℤ) = 0 := by
      simp
    rw [h0, shiftFin_zero_eq]
  have hunitB := (hBax ω hω α hα t ht i hi).1
  suffices h : (truncMatrix α t i)⁻¹ *ᵥ Y = Z from congrFun h f
  rw [← hBZ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunitB, Matrix.one_mulVec]

/-! ## Part 3: the sweep only reads its cycle -/

theorem sweepPrefix_congr (rr : ℕ → ℝ → ℝ) (q : ℕ) (a : ℝ) (b b' : ℕ → ℂ) (z : ℂ) (n : ℕ)
    (h : ∀ j ≤ n, b j = b' j) : sweepPrefixR rr q a b z n = sweepPrefixR rr q a b' z n := by
  induction n with
  | zero => simp only [sweepPrefixR]; rw [h 0 le_rfl]
  | succ n ih =>
    simp only [sweepPrefixR]
    rw [h (n + 1) le_rfl, ih (fun j hj => h j (by omega))]

theorem cycSweepFwd_congr (rr : ℕ → ℝ → ℝ) (q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (g g' : ℕ → ℂ)
    (hg : ∀ j < L, g j = g' j) (n : ℕ) (hn : n < L) :
    cycSweepFwdR rr q mu ahat gam L g n = cycSweepFwdR rr q mu ahat gam L g' n := by
  have hb : ∀ j < L, crnd rr q ((mu : ℂ) * g j) = crnd rr q ((mu : ℂ) * g' j) :=
    fun j hj => by rw [hg j hj]
  have h1 : sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * g j)) 0 (L - 1) =
      sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * g' j)) 0 (L - 1) :=
    sweepPrefix_congr _ _ _ _ _ _ _ (fun j hj => hb j (by omega))
  simp only [cycSweepFwdR]
  rw [h1]
  split_ifs
  · rfl
  · exact sweepPrefix_congr _ _ _ _ _ _ _ (fun j hj => hb j (by omega))

theorem reorientIn_congr (L : ℕ) (hL : 0 < L) (g g' : ℕ → ℂ) (hg : ∀ j < L, g j = g' j) :
    reorientIn L g = reorientIn L g' := by
  funext j
  exact hg _ (toNat_emod_lt hL _)

theorem cycSweep_congr (rr : ℕ → ℝ → ℝ) (fwd : Bool) (q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (hL : 0 < L)
    (g g' : ℕ → ℂ) (hg : ∀ j < L, g j = g' j) (n : ℕ) (hn : n < L) :
    cycSweepR rr fwd q mu ahat gam L g n = cycSweepR rr fwd q mu ahat gam L g' n := by
  unfold cycSweepR
  cases fwd
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, reorientIn_congr L hL g g' hg]
  · rw [if_pos rfl, if_pos rfl]
    exact cycSweepFwd_congr rr q mu ahat gam L g g' hg n hn

/-! ## Part 4: one deconvolution stage (Lemma 4.6 (bridge Lemma C)(iv) cycle by cycle) -/

/-- The cycle length `L = A_h` (`h ≥ 2`) is even: `t_1 ∣ A_h` and `t_1 ≥ 2` is a power of two. -/
theorem even_prefixProd {t : Fin d → ℕ} (ht : ShapeOK t) {i : Fin d} (hi : (i : ℕ) ≠ 0) :
    Even (prefixProd t i) := by
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hmem : (⟨0, hd⟩ : Fin d) ∈ Finset.univ.filter (fun l : Fin d => (l : ℕ) < (i : ℕ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show 0 < (i : ℕ)
    omega
  have hdvd : t ⟨0, hd⟩ ∣ prefixProd t i := Finset.dvd_prod_of_mem t hmem
  obtain ⟨h2, a, ha⟩ := ht ⟨0, hd⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at ha
    omega
  have h2dvd : 2 ∣ t ⟨0, hd⟩ := by rw [ha]; exact dvd_pow_self 2 ha0
  exact even_iff_two_dvd.mpr (h2dvd.trans hdvd)

/-- `‖B_h⁻¹ y‖ ≤ t_h ‖y‖` (B(v)_axis). -/
theorem norm_truncMatrix_inv_mulVec_le (hBax : LemmaB_v_axisStmt) {ω : ℕ} (hω : 8 ≤ ω) {α : ℝ}
    (hα : AlphaAdmissible ω α) {t : Fin d → ℕ} (ht : ShapeOK t) {i : Fin d} (hi : (i : ℕ) ≠ 0)
    (y : Fin (totalLen t) → ℂ) : ‖(truncMatrix α t i)⁻¹ *ᵥ y‖ ≤ (t i : ℝ) * ‖y‖ := by
  obtain ⟨_, h1, h2⟩ := hBax ω hω α hα t ht i hi
  have h := norm_apply_le_opNormInf (Matrix.toLin' (truncMatrix α t i)⁻¹) y
  rw [Matrix.toLin'_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_right (h1.trans h2) (norm_nonneg _))

/-- **One fixed-point deconvolution stage** (Lemma 4.6 (bridge Lemma C)(iv) applied cycle by cycle, with C(v) for the
closure constant): `‖deconvAxisFixedR Y - B_h⁻¹ Y‖_∞ ≤ 32 t_h² v max(1,‖Y‖_∞)`, and every output
(a state of the two-pass sweep) has modulus `< 7 t_h max(1,‖Y‖_∞)`. -/
theorem deconvAxisFixed_stage (hCiv : LemmaC_ivStmt) (hCv : LemmaC_vStmt) (hBv : LemmaB_vStmt)
    (hBax : LemmaB_v_axisStmt) (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) {P ω : ℕ} {α : ℝ}
    (hC : LemmaCParams P ω α) {t : Fin d → ℕ}
    (ht : ShapeOK t) {T : BridgeTables t} (hT : TablesCertifiedR rr α P t T) {i : Fin d}
    (hi : (i : ℕ) ≠ 0) (hv : gridUnit (P + 2) ≤ 1 / (64 * (t i : ℝ)))
    (Y : Fin (totalLen t) → ℂ) :
    ‖deconvAxisFixedR rr (P + 2) t T i Y - (truncMatrix α t i)⁻¹ *ᵥ Y‖ ≤
        32 * (t i : ℝ) ^ 2 * gridUnit (P + 2) * max 1 ‖Y‖ ∧
      ∀ f, ‖deconvAxisFixedR rr (P + 2) t T i Y f‖ < 7 * (t i : ℝ) * max 1 ‖Y‖ := by
  have hω : 8 ≤ ω := hC.2.1
  have hα : AlphaAdmissible ω α := alphaAdmissible_of_params hC
  have hL0 : 0 < prefixProd t i := prefixProd_pos ht i
  have hLe : Even (prefixProd t i) := even_prefixProd ht hi
  have hc32 : 0 ≤ 32 * (t i : ℝ) ^ 2 * gridUnit (P + 2) :=
    mul_nonneg (by positivity) (gridUnit_pos _).le
  have hpt : ∀ f : Fin (totalLen t),
      ‖deconvAxisFixedR rr (P + 2) t T i Y f - ((truncMatrix α t i)⁻¹ *ᵥ Y) f‖ ≤
        32 * (t i : ℝ) ^ 2 * gridUnit (P + 2) * max 1 ‖Y‖ ∧
      ‖deconvAxisFixedR rr (P + 2) t T i Y f‖ < 7 * (t i : ℝ) * max 1 ‖Y‖ := by
    intro f
    have hu : (((encFreq t).symm f i : Fin (t i)) : ℕ) < t i := ((encFreq t).symm f i).isLt
    obtain ⟨_, _, hmu, ha, ha0, hgam⟩ := (hT i hi).2 _ hu
    have hgam' : |T.gam i (((encFreq t).symm f i : Fin (t i)) : ℕ) -
        (1 - T.ahat i (((encFreq t).symm f i : Fin (t i)) : ℕ) ^ prefixProd t i)⁻¹| ≤
          gridUnit (P + 2) := by
      rw [hgam]
      exact hCv rr hrr P ω α hC (t i) (ht i) _ hu hv _ (prefixProd t i) hLe hL0 ha ha0
    obtain ⟨h1, -, h3⟩ := hCiv rr hrr P ω α hC (t i) (ht i) _ hu hv _ _ _ (prefixProd t i) hLe hL0 hmu
      ha ha0 hgam' (cycVec t i Y f)
    have hj0 := cycPos_lt ht i f
    have hsweep : deconvAxisFixedR rr (P + 2) t T i Y f =
        cycSweepR rr (decide (2 * (((encFreq t).symm f i : Fin (t i)) : ℕ) < t i)) (P + 2)
          (T.mu i (((encFreq t).symm f i : Fin (t i)) : ℕ))
          (T.ahat i (((encFreq t).symm f i : Fin (t i)) : ℕ))
          (T.gam i (((encFreq t).symm f i : Fin (t i)) : ℕ)) (prefixProd t i)
          (extNat (cycVec t i Y f)) ((f : ℕ) / aliasStep t i) := by
      simp only [deconvAxisFixedR]
      refine cycSweep_congr _ _ _ _ _ _ _ hL0 _ _ ?_ _ hj0
      intro j hj
      simp only [extNat, dif_pos hj]
      rfl
    have hinv := truncMatrix_inv_mulVec_apply hBv hBax hω hα ht hi Y f
    have hmax : max 1 ‖cycVec t i Y f‖ ≤ max 1 ‖Y‖ := max_le_max le_rfl (norm_cycVec_le t i Y f)
    constructor
    · rw [hsweep, hinv]
      exact (h1 ⟨(f : ℕ) / aliasStep t i, hj0⟩).trans (mul_le_mul_of_nonneg_left hmax hc32)
    · rw [hsweep]
      have hfin : 7 * (t i : ℝ) * max 1 ‖cycVec t i Y f‖ ≤ 7 * (t i : ℝ) * max 1 ‖Y‖ :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
      revert h3
      unfold cycSweepR
      generalize decide (2 * (((encFreq t).symm f i : Fin (t i)) : ℕ) < t i) = fw
      intro h3
      cases fw
      · rw [if_neg Bool.false_ne_true] at h3 ⊢
        exact (h3 _ (toNat_emod_lt hL0 _)).trans_le hfin
      · rw [if_pos rfl] at h3 ⊢
        exact (h3 _ hj0).trans_le hfin
  refine ⟨(pi_norm_le_iff_of_nonneg (mul_nonneg hc32 (by positivity))).2 fun f => (hpt f).1,
    fun f => (hpt f).2⟩

/-! ## Part 5: the exact chain and a generic perturbed-chain bound -/

theorem listProd_inv_mulVec {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*}
    (M : ι → Matrix n n ℂ) (l : List ι) (y : n → ℂ) :
    ((l.map M).prod)⁻¹ *ᵥ y = l.foldl (fun z i => (M i)⁻¹ *ᵥ z) y := by
  induction l generalizing y with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ih,
      List.foldl_cons]

theorem foldl_lin_bound {ι E : Type*} [NormedAddCommGroup E] (M : ι → E → E) (a : ι → ℝ)
    (l : List ι) (ha : ∀ i ∈ l, 0 ≤ a i)
    (hMsub : ∀ i ∈ l, ∀ y y' : E, M i y - M i y' = M i (y - y'))
    (hMnorm : ∀ i ∈ l, ∀ y : E, ‖M i y‖ ≤ a i * ‖y‖) (y y' : E) :
    ‖l.foldl (fun z i => M i z) y - l.foldl (fun z i => M i z) y'‖ ≤
      (l.map a).prod * ‖y - y'‖ := by
  induction l generalizing y y' with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have hP0 : 0 ≤ (l.map a).prod := List.prod_nonneg (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx; exact ha j (List.mem_cons_of_mem i hj))
    calc ‖l.foldl (fun z i => M i z) (M i y) - l.foldl (fun z i => M i z) (M i y')‖
        ≤ (l.map a).prod * ‖M i y - M i y'‖ :=
          ih (fun j hj => ha j (List.mem_cons_of_mem i hj))
            (fun j hj => hMsub j (List.mem_cons_of_mem i hj))
            (fun j hj => hMnorm j (List.mem_cons_of_mem i hj)) _ _
      _ ≤ (l.map a).prod * (a i * ‖y - y'‖) := by
          rw [hMsub i List.mem_cons_self]
          exact mul_le_mul_of_nonneg_left (hMnorm i List.mem_cons_self _) hP0
      _ = a i * (l.map a).prod * ‖y - y'‖ := by ring

/-- **Generic perturbed chain** (proof of Theorem 4.7 (`thm:bridge-precision`)): if each computed stage `F_i`
is within `32 a_i² v max(1,‖y‖)` of a linear stage `M_i` with `‖M_i‖ ≤ a_i` (`a_i ≥ 1`), then
starting from `‖z‖ ≤ K(1 + 64vσ)` (`K ≥ 1`, `64 v (σ + ∑ a) ≤ 1`) the computed chain satisfies
`‖Ẑ‖ ≤ K (∏ a)(1 + 64 v (σ + ∑ a))` and `‖Ẑ - Z‖ ≤ 64 v K (∏ a)(∑ a)`. -/
theorem chain_bound {ι E : Type*} [NormedAddCommGroup E] (F M : ι → E → E) (a : ι → ℝ) (v : ℝ)
    (hv : 0 ≤ v) (l : List ι) (ha : ∀ i ∈ l, 1 ≤ a i)
    (hMsub : ∀ i ∈ l, ∀ y y' : E, M i y - M i y' = M i (y - y'))
    (hMnorm : ∀ i ∈ l, ∀ y : E, ‖M i y‖ ≤ a i * ‖y‖)
    (hstage : ∀ i ∈ l, ∀ y : E, ‖F i y - M i y‖ ≤ 32 * a i ^ 2 * v * max 1 ‖y‖)
    (z : E) (K σ : ℝ) (hK : 1 ≤ K) (hσ : 0 ≤ σ) (hz : ‖z‖ ≤ K * (1 + 64 * v * σ))
    (hsum : 64 * v * (σ + (l.map a).sum) ≤ 1) :
    ‖l.foldl (fun y i => F i y) z‖ ≤ K * (l.map a).prod * (1 + 64 * v * (σ + (l.map a).sum)) ∧
      ‖l.foldl (fun y i => F i y) z - l.foldl (fun y i => M i y) z‖ ≤
        64 * v * K * (l.map a).prod * (l.map a).sum := by
  induction l generalizing z K σ with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.prod_nil, List.sum_nil, add_zero, mul_one,
      sub_self, norm_zero, mul_zero]
    exact ⟨hz, le_rfl⟩
  | cons i l ih =>
    have hai : 1 ≤ a i := ha i List.mem_cons_self
    have ha' : ∀ j ∈ l, 1 ≤ a j := fun j hj => ha j (List.mem_cons_of_mem i hj)
    have hMsub' : ∀ j ∈ l, ∀ y y' : E, M j y - M j y' = M j (y - y') :=
      fun j hj => hMsub j (List.mem_cons_of_mem i hj)
    have hMnorm' : ∀ j ∈ l, ∀ y : E, ‖M j y‖ ≤ a j * ‖y‖ :=
      fun j hj => hMnorm j (List.mem_cons_of_mem i hj)
    have hstage' : ∀ j ∈ l, ∀ y : E, ‖F j y - M j y‖ ≤ 32 * a j ^ 2 * v * max 1 ‖y‖ :=
      fun j hj => hstage j (List.mem_cons_of_mem i hj)
    have hS0 : 0 ≤ (l.map a).sum := List.sum_nonneg (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx; linarith [ha' j hj])
    have hP0 : 0 ≤ (l.map a).prod := List.prod_nonneg (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx; linarith [ha' j hj])
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, List.sum_cons] at hsum ⊢
    have hva : 0 ≤ v * a i := mul_nonneg hv (by linarith)
    have hvS : 0 ≤ v * (l.map a).sum := mul_nonneg hv hS0
    have h64σ : 64 * v * σ ≤ 1 := by nlinarith
    have h64a : 64 * v * a i ≤ 1 := by nlinarith
    have hN1 : 1 ≤ K * (1 + 64 * v * σ) := by nlinarith [mul_nonneg hv hσ]
    have hmaxz : max 1 ‖z‖ ≤ K * (1 + 64 * v * σ) := max_le hN1 hz
    have hst := hstage i List.mem_cons_self z
    have hMz := hMnorm i List.mem_cons_self z
    have h32 : 0 ≤ 32 * a i ^ 2 * v := mul_nonneg (by positivity) hv
    have hFz : ‖F i z‖ ≤ a i * K * (1 + 64 * v * (σ + a i)) := by
      have e1 : ‖F i z‖ ≤ ‖F i z - M i z‖ + ‖M i z‖ := by
        calc ‖F i z‖ = ‖(F i z - M i z) + M i z‖ := by rw [sub_add_cancel]
          _ ≤ ‖F i z - M i z‖ + ‖M i z‖ := norm_add_le _ _
      have e2 : ‖F i z - M i z‖ ≤ 32 * a i ^ 2 * v * (K * (1 + 64 * v * σ)) :=
        hst.trans (mul_le_mul_of_nonneg_left hmaxz h32)
      have e3 : ‖M i z‖ ≤ a i * (K * (1 + 64 * v * σ)) :=
        hMz.trans (mul_le_mul_of_nonneg_left hz (by linarith))
      have e4 := mul_le_mul_of_nonneg_left h64σ (mul_nonneg h32 (by linarith : (0 : ℝ) ≤ K))
      nlinarith
    obtain ⟨ih1, ih2⟩ := ih ha' hMsub' hMnorm' hstage' (F i z) (a i * K) (σ + a i)
      (by nlinarith) (by linarith) hFz (by linarith)
    have hlin := foldl_lin_bound M a l (fun j hj => by linarith [ha' j hj]) hMsub' hMnorm'
      (F i z) (M i z)
    constructor
    · calc ‖l.foldl (fun y i => F i y) (F i z)‖
          ≤ a i * K * (l.map a).prod * (1 + 64 * v * (σ + a i + (l.map a).sum)) := ih1
        _ = K * (a i * (l.map a).prod) * (1 + 64 * v * (σ + (a i + (l.map a).sum))) := by ring
    · have e5 : ‖l.foldl (fun y i => M i y) (F i z) - l.foldl (fun y i => M i y) (M i z)‖ ≤
          (l.map a).prod * (32 * a i ^ 2 * v * (K * (1 + 64 * v * σ))) :=
        hlin.trans (mul_le_mul_of_nonneg_left (hst.trans (mul_le_mul_of_nonneg_left hmaxz h32)) hP0)
      have e6 := mul_le_mul_of_nonneg_left h64σ
        (mul_nonneg (mul_nonneg h32 (by linarith : (0 : ℝ) ≤ K)) hP0)
      calc ‖l.foldl (fun y i => F i y) (F i z) - l.foldl (fun y i => M i y) (M i z)‖
          ≤ ‖l.foldl (fun y i => F i y) (F i z) - l.foldl (fun y i => M i y) (F i z)‖ +
            ‖l.foldl (fun y i => M i y) (F i z) - l.foldl (fun y i => M i y) (M i z)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 64 * v * (a i * K) * (l.map a).prod * (l.map a).sum +
            (l.map a).prod * (32 * a i ^ 2 * v * (K * (1 + 64 * v * σ))) := add_le_add ih2 e5
        _ ≤ 64 * v * K * (a i * (l.map a).prod) * (a i + (l.map a).sum) := by nlinarith

/-! ## Part 6: the bridge deconvolution chain -/

theorem deconvOrder_nodup' (d : ℕ) : (deconvOrder d).Nodup := (List.nodup_finRange d).filter _

theorem mem_deconvOrder' {j : Fin d} : j ∈ deconvOrder d ↔ (j : ℕ) ≠ 0 := by
  simp [deconvOrder]

theorem deconvOrder_toFinset' (d : ℕ) :
    (deconvOrder d).toFinset = Finset.univ.filter (fun j : Fin d => (j : ℕ) ≠ 0) := by
  ext j
  simp [mem_deconvOrder']

theorem deconvOrder_prod (t : Fin d → ℕ) :
    ((deconvOrder d).map (fun i => (t i : ℝ))).prod = (dimD t : ℝ) := by
  rw [← List.prod_toFinset _ (deconvOrder_nodup' d), deconvOrder_toFinset', dimD, Nat.cast_prod]

theorem deconvOrder_sum (t : Fin d → ℕ) :
    ((deconvOrder d).map (fun i => (t i : ℝ))).sum =
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ) := by
  rw [← List.sum_toFinset _ (deconvOrder_nodup' d), deconvOrder_toFinset']

/-- **Deconvolution chain over any list of deconvolution axes** (proof of Theorem 4.7 (`thm:bridge-precision`)):
with `D_l = ∏_{h∈l} t_h`, `S_l = ∑_{h∈l} t_h` and `64 v S_l ≤ 1`, the computed chain has
`‖Ẑ‖ ≤ max(1,‖Y‖) D_l (1 + 64 v S_l)` (`≤ 2 D_l max(1,‖Y‖)`) and differs from the exact chain
`B_{h_m}⁻¹⋯B_{h_1}⁻¹ Y` by at most `64 v max(1,‖Y‖) D_l S_l`. -/
theorem deconv_chain_list (hCiv : LemmaC_ivStmt) (hCv : LemmaC_vStmt) (hBv : LemmaB_vStmt)
    (hBax : LemmaB_v_axisStmt) (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) {P ω : ℕ} {α : ℝ}
    (hC : LemmaCParams P ω α) {t : Fin d → ℕ}
    (ht : ShapeOK t) {T : BridgeTables t} (hT : TablesCertifiedR rr α P t T) (l : List (Fin d))
    (hl : ∀ i ∈ l, (i : ℕ) ≠ 0)
    (hsum : 64 * gridUnit (P + 2) * (l.map (fun i => (t i : ℝ))).sum ≤ 1)
    (Y : Fin (totalLen t) → ℂ) :
    ‖l.foldl (fun Z i => deconvAxisFixedR rr (P + 2) t T i Z) Y‖ ≤
        max 1 ‖Y‖ * (l.map (fun i => (t i : ℝ))).prod *
          (1 + 64 * gridUnit (P + 2) * (l.map (fun i => (t i : ℝ))).sum) ∧
      ‖l.foldl (fun Z i => deconvAxisFixedR rr (P + 2) t T i Z) Y -
          l.foldl (fun Z i => (truncMatrix α t i)⁻¹ *ᵥ Z) Y‖ ≤
        64 * gridUnit (P + 2) * max 1 ‖Y‖ * (l.map (fun i => (t i : ℝ))).prod *
          (l.map (fun i => (t i : ℝ))).sum := by
  have hω : 8 ≤ ω := hC.2.1
  have hα : AlphaAdmissible ω α := alphaAdmissible_of_params hC
  have hv0 : 0 ≤ gridUnit (P + 2) := (gridUnit_pos _).le
  have hti : ∀ i ∈ l, (t i : ℝ) ≤ (l.map (fun i => (t i : ℝ))).sum := fun i hi =>
    List.single_le_sum (fun x hx => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; positivity) _
      (List.mem_map_of_mem hi)
  have hvi : ∀ i ∈ l, gridUnit (P + 2) ≤ 1 / (64 * (t i : ℝ)) := by
    intro i hi
    have h2 : (2 : ℝ) ≤ t i := by exact_mod_cast (ht i).1
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hti i hi]
  have h := chain_bound (fun i Z => deconvAxisFixedR rr (P + 2) t T i Z)
    (fun i Z => (truncMatrix α t i)⁻¹ *ᵥ Z) (fun i => (t i : ℝ)) (gridUnit (P + 2)) hv0 l
    (fun i _ => by exact_mod_cast (show 1 ≤ t i by have := (ht i).1; omega))
    (fun i _ y y' => (Matrix.mulVec_sub _ y y').symm)
    (fun i hi y => norm_truncMatrix_inv_mulVec_le hBax hω hα ht (hl i hi) y)
    (fun i hi y => (deconvAxisFixed_stage hCiv hCv hBv hBax rr hrr hC ht hT (hl i hi) (hvi i hi) y).1)
    Y (max 1 ‖Y‖) 0 (le_max_left _ _) le_rfl
    (by rw [mul_zero, add_zero, mul_one]; exact le_max_right _ _) (by rw [zero_add]; exact hsum)
  obtain ⟨h1, h2⟩ := h
  rw [zero_add] at h1
  exact ⟨h1, h2⟩

theorem one_le_list_prod {l : List ℝ} (h : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (h a List.mem_cons_self)
      (ih fun x hx => h x (List.mem_cons_of_mem a hx))

theorem take_prod_le {t : Fin d → ℕ} (ht : ShapeOK t) (l : List (Fin d)) (m : ℕ) :
    ((l.take m).map (fun i => (t i : ℝ))).prod ≤ (l.map (fun i => (t i : ℝ))).prod := by
  have h1 : ∀ x ∈ ((l.drop m).map (fun i => (t i : ℝ))), 1 ≤ x := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (show 1 ≤ t j by have := (ht j).1; omega)
  have h0 : 0 ≤ ((l.take m).map (fun i => (t i : ℝ))).prod := List.prod_nonneg (fun x hx => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; positivity)
  conv_rhs => rw [← List.take_append_drop m l]
  rw [List.map_append, List.prod_append]
  exact le_mul_of_one_le_right h0 (one_le_list_prod h1)

theorem take_sum_le (t : Fin d → ℕ) (l : List (Fin d)) (m : ℕ) :
    ((l.take m).map (fun i => (t i : ℝ))).sum ≤ (l.map (fun i => (t i : ℝ))).sum := by
  conv_rhs => rw [← List.take_append_drop m l]
  rw [List.map_append, List.sum_append]
  have : 0 ≤ ((l.drop m).map (fun i => (t i : ℝ))).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; positivity)
  linarith

/-- **Intermediate norms of the deconvolution chain** (proof of Theorem 4.7 (`thm:bridge-precision`)): if
`64 v ∑_{h≥2} t_h ≤ 1`, the array after the first `m` solver stages has norm
`≤ 2 D_m max(1,‖Y‖_∞)`, where `D_m` is the product of the first `m` deconvolution lengths, and
`D_m ≤ D = ∏_{h≥2} t_h`. -/
theorem deconv_prefix_norm_le (hCiv : LemmaC_ivStmt) (hCv : LemmaC_vStmt) (hBv : LemmaB_vStmt)
    (hBax : LemmaB_v_axisStmt) (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) {P ω : ℕ} {α : ℝ}
    (hC : LemmaCParams P ω α) {t : Fin d → ℕ}
    (ht : ShapeOK t) {T : BridgeTables t} (hT : TablesCertifiedR rr α P t T)
    (hsum : 64 * gridUnit (P + 2) *
      (∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), (t i : ℝ)) ≤ 1)
    (Y : Fin (totalLen t) → ℂ) (m : ℕ) :
    ‖((deconvOrder d).take m).foldl (fun Z i => deconvAxisFixedR rr (P + 2) t T i Z) Y‖ ≤
        2 * (((deconvOrder d).take m).map (fun i => (t i : ℝ))).prod * max 1 ‖Y‖ ∧
      (((deconvOrder d).take m).map (fun i => (t i : ℝ))).prod ≤ (dimD t : ℝ) := by
  have hl : ∀ i ∈ (deconvOrder d).take m, (i : ℕ) ≠ 0 :=
    fun i hi => mem_deconvOrder'.mp (List.mem_of_mem_take hi)
  have hS := take_sum_le t (deconvOrder d) m
  have hP := take_prod_le ht (deconvOrder d) m
  rw [deconvOrder_sum] at hS
  rw [deconvOrder_prod] at hP
  have hv0 : 0 ≤ gridUnit (P + 2) := (gridUnit_pos _).le
  have hS0 : 0 ≤ (((deconvOrder d).take m).map (fun i => (t i : ℝ))).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; positivity)
  have hsum' : 64 * gridUnit (P + 2) *
      (((deconvOrder d).take m).map (fun i => (t i : ℝ))).sum ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hS (mul_nonneg (by norm_num) hv0)) hsum
  obtain ⟨h1, -⟩ := deconv_chain_list hCiv hCv hBv hBax rr hrr hC ht hT _ hl hsum' Y
  have hP0 : 0 ≤ (((deconvOrder d).take m).map (fun i => (t i : ℝ))).prod :=
    List.prod_nonneg (fun x hx => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; positivity)
  have hK : 0 ≤ max 1 ‖Y‖ := le_trans zero_le_one (le_max_left _ _)
  refine ⟨?_, hP⟩
  calc _ ≤ max 1 ‖Y‖ * (((deconvOrder d).take m).map (fun i => (t i : ℝ))).prod *
        (1 + 64 * gridUnit (P + 2) *
          (((deconvOrder d).take m).map (fun i => (t i : ℝ))).sum) := h1
    _ ≤ max 1 ‖Y‖ * (((deconvOrder d).take m).map (fun i => (t i : ℝ))).prod * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK hP0)
    _ = 2 * (((deconvOrder d).take m).map (fun i => (t i : ℝ))).prod * max 1 ‖Y‖ := by ring

end PrecisionDeconvProof

open PrecisionDeconvProof in
/-- **Deconvolution chain** (proof of Theorem 4.7 (`thm:bridge-precision`)): `E_solver ≤ 64 D v ∑_{h≥2} t_h`
(times `max(1,‖Y‖)`), conditional on Lemma 4.6 (bridge Lemma C)(iv), C(v), B(v) and B(v)_axis. -/
theorem deconv_chain_of (hCiv : LemmaC_ivStmt) (hCv : LemmaC_vStmt) (hBv : LemmaB_vStmt)
    (hBvax : LemmaB_v_axisStmt) : Deconv_chainStmt := by
  intro rr hrr d P ω α hC t ht T hT hsum Y
  have hl : ∀ i ∈ deconvOrder d, (i : ℕ) ≠ 0 := fun i hi => mem_deconvOrder'.mp hi
  have hsum' : 64 * gridUnit (P + 2) * ((deconvOrder d).map (fun i => (t i : ℝ))).sum ≤ 1 := by
    rw [deconvOrder_sum]; exact hsum
  obtain ⟨-, h2⟩ := deconv_chain_list hCiv hCv hBv hBvax rr hrr hC ht hT (deconvOrder d) hl hsum' Y
  rw [deconvOrder_prod, deconvOrder_sum] at h2
  have hex : (truncProd α t)⁻¹ *ᵥ Y =
      (deconvOrder d).foldl (fun Z i => (truncMatrix α t i)⁻¹ *ᵥ Z) Y :=
    listProd_inv_mulVec (truncMatrix α t) (deconvOrder d) Y
  unfold deconvFixedR
  rw [hex]
  calc _ ≤ _ := h2
    _ = _ := by ring

end SubNLogN.Math.Bridge
