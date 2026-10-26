import Mathlib
import IntMul.Preliminaries

/-!
# Common: normalized DFTs, shapes and index encodings

Paper: Definition 3.2 (`def:dft`), index conventions of Section 4.1 (`sec:bridge-conventions`), eq. (`eq:freq-digits`).

* `dft R : (Fin R → ℂ) →ₗ[ℂ] (Fin R → ℂ)` is `F_R`, `(F_R x)_u = (1/R) ∑_j x_j e^{2πi ju/R}`.
* `Idx t = (i : Fin d) → Fin (t i)` are digit tuples; `dftTensor t` is `F_t` on `Idx t → ℂ`.
  Axes are 0-based: Lean axis `i` is the paper's axis `i+1`.
* `encIn t : Idx t ≃ Fin R` is the input identification `j = ∑_i j_i A_i` (axis 0 least significant);
  `encFreq t : Idx t ≃ Fin R` is the frequency identification `f(u) = ∑_i u_i R/A_{i+1}`
  (last axis least significant); `encFreq` is also the tape position in "natural order" with the
  last axis contiguous.
* The character is `IntMul.stdChar x = exp(2πix)` (reused from the IntMul development).
-/

namespace SubNLogN.Math.Common

open scoped BigOperators

/-- `lg n = max(⌈log₂ n⌉, 1)` ([OAI26] convention, Section 3.1 (`sec:notation`)). -/
def lg (n : ℕ) : ℕ := max (Nat.clog 2 n) 1

/-- Normalized positive DFT `F_R` (Definition 3.2 (`def:dft`)):
`(F_R x)_u = (1/R) ∑_{j ∈ [R]} x_j e^{2πi ju/R}`. -/
noncomputable def dft (R : ℕ) : (Fin R → ℂ) →ₗ[ℂ] (Fin R → ℂ) where
  toFun x u := (R : ℂ)⁻¹ *
    ∑ j : Fin R, x j * IntMul.stdChar ((((j : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ))
  map_add' x y := by
    funext u
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- Digit tuples `[t_1] × ⋯ × [t_d]` of a shape `t` (0-based axes). -/
abbrev Idx {d : ℕ} (t : Fin d → ℕ) : Type := (i : Fin d) → Fin (t i)

/-- The length `R = t_1 ⋯ t_d` of a shape. -/
abbrev totalLen {d : ℕ} (t : Fin d → ℕ) : ℕ := ∏ i, t i

/-- Normalized positive tensor DFT `F_t` (Definition 3.2 (`def:dft`)):
`(F_t U)_u = (1/R) ∑_j U_j exp(2πi ∑_i j_i u_i / t_i)`. -/
noncomputable def dftTensor {d : ℕ} (t : Fin d → ℕ) : (Idx t → ℂ) →ₗ[ℂ] (Idx t → ℂ) where
  toFun U u := (totalLen t : ℂ)⁻¹ *
    ∑ j : Idx t, U j * IntMul.stdChar (∑ i, (((j i : ℕ) * (u i : ℕ) : ℕ) : ℝ) / (t i : ℝ))
  map_add' U V := by
    funext u
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c U := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- `A_k = ∏_{i<k} t_i` (0-based). The paper's `A_h` (Section 4.1 (`sec:bridge-conventions`), 1-based `h`) is
`prefixProd t (h-1)`; `prefixProd t 0 = 1` and `prefixProd t d = R`. -/
def prefixProd {d : ℕ} (t : Fin d → ℕ) (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < k), t i

/-- `∏_{l>i} t_l`, the paper's `R/A_{h+1}` for `h = i+1`: the weight of frequency digit `i`. -/
def suffixProd {d : ℕ} (t : Fin d → ℕ) (i : Fin d) : ℕ :=
  ∏ l ∈ Finset.univ.filter (fun l : Fin d => i < l), t l

/-- Input identification `j = ∑_i j_i A_i` (axis 0 least significant; Section 4.1 (`sec:bridge-conventions`)). -/
def encIn {d : ℕ} (t : Fin d → ℕ) : Idx t ≃ Fin (totalLen t) := finPiFinEquiv

/-- Frequency identification `f(u) = ∑_i u_i R/A_{i+1}` (last axis least significant;
Section 4.1, eq. (`eq:freq-digits`)). -/
def encFreq {d : ℕ} (t : Fin d → ℕ) : Idx t ≃ Fin (totalLen t) :=
  (Equiv.piCongrLeft' (fun i => Fin (t i)) Fin.revPerm).trans
    ((finPiFinEquiv (n := fun b => t (Fin.revPerm.symm b))).trans
      (finCongr (Equiv.prod_comp Fin.revPerm.symm t)))

/-- Cyclic convolution on `ℤ/R` (Section 3.3 (`sec:prelim-dft`)): `(a ⊛ b)_j = ∑_k a_k b_{(j-k) mod R}`. -/
noncomputable def cycConv {R : ℕ} (a b : Fin R → ℂ) : Fin R → ℂ :=
  fun j => ∑ k : Fin R, a k * b (j - k)

/-! ## Helper lemmas (not contracts)

Unfolding lemmas for `dft`/`dftTensor`, the product identities behind Mathlib's `finPiFinEquiv`
(used by `encIn`/`encFreq`), and the character facts (periodicity, conjugation, orthogonality)
used in the proofs of the contracts below. -/

/-- Unfolding lemma for `dft` (holds by definition). -/
theorem dft_apply (R : ℕ) (x : Fin R → ℂ) (u : Fin R) :
    dft R x u = (R : ℂ)⁻¹ *
      ∑ j : Fin R, x j * IntMul.stdChar ((((j : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) :=
  rfl

/-- Unfolding lemma for `dftTensor` (holds by definition). -/
theorem dftTensor_apply {d : ℕ} (t : Fin d → ℕ) (U : Idx t → ℂ) (u : Idx t) :
    dftTensor t U u = (totalLen t : ℂ)⁻¹ *
      ∑ j : Idx t, U j * IntMul.stdChar (∑ i, (((j i : ℕ) * (u i : ℕ) : ℕ) : ℝ) / (t i : ℝ)) :=
  rfl

/-- `A_i = prefixProd t i` as the product over `Fin i` used by Mathlib's `finPiFinEquiv`. -/
theorem prefixProd_eq_prod_castLE {d : ℕ} (t : Fin d → ℕ) (i : Fin d) :
    prefixProd t i = ∏ k : Fin i, t (Fin.castLE i.is_lt.le k) := by
  unfold prefixProd
  symm
  refine Finset.prod_bij (fun k _ => Fin.castLE i.is_lt.le k) ?_ ?_ ?_ ?_
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.is_lt
  · intro k₁ _ k₂ _ h
    exact Fin.castLE_injective _ h
  · intro l hl
    exact ⟨⟨l, (Finset.mem_filter.1 hl).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro k _
    rfl

/-- `suffixProd t (rev b) = ∏_{l > rev b} t_l` as the product over `Fin b` that appears when
`finPiFinEquiv` is applied to the axis-reversed tuple (as in `encFreq`). -/
theorem suffixProd_rev_eq_prod {d : ℕ} (t : Fin d → ℕ) (b : Fin d) :
    suffixProd t (Fin.rev b) = ∏ k : Fin b, t (Fin.rev (Fin.castLE b.is_lt.le k)) := by
  unfold suffixProd
  symm
  refine Finset.prod_bij (fun k _ => Fin.rev (Fin.castLE b.is_lt.le k)) ?_ ?_ ?_ ?_
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.rev_lt_rev]
    exact k.is_lt
  · intro k₁ _ k₂ _ h
    exact Fin.castLE_injective _ (Fin.rev_injective h)
  · intro l hl
    have hlt : ((Fin.rev l : Fin d) : ℕ) < (b : ℕ) := Fin.rev_lt_iff.1 (Finset.mem_filter.1 hl).2
    refine ⟨⟨(Fin.rev l : ℕ), hlt⟩, Finset.mem_univ _, ?_⟩
    show Fin.rev (Fin.castLE b.is_lt.le ⟨(Fin.rev l : ℕ), hlt⟩) = l
    rw [show Fin.castLE b.is_lt.le ⟨(Fin.rev l : ℕ), hlt⟩ = Fin.rev l from Fin.ext rfl,
      Fin.rev_rev]
  · intro k _
    rfl

/-- Values of `(piCongrLeft' _ e).symm` on `Fin`-valued families (avoids the transport). -/
private theorem val_piCongrLeft'_symm_apply {α β : Type*} (n : α → ℕ) (e : α ≃ β)
    (g : ∀ b, Fin (n (e.symm b))) (a : α) :
    (((Equiv.piCongrLeft' (fun a => Fin (n a)) e).symm g a : Fin (n a)) : ℕ) =
      (g (e a) : ℕ) := by
  obtain ⟨b, rfl⟩ := e.symm.surjective a
  rw [Equiv.piCongrLeft'_symm_apply_apply, Equiv.apply_symm_apply]

/-- Digit extraction for Mathlib's `finPiFinEquiv` (holds by definition). -/
private theorem finPiFinEquiv_symm_apply_val {m : ℕ} {n : Fin m → ℕ} (a : Fin (∏ i, n i))
    (b : Fin m) :
    ((finPiFinEquiv.symm a b : Fin (n b)) : ℕ) =
      ((a : ℕ) / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b :=
  rfl

/-- `‖N⁻¹ ∑_j x_j c_j‖ ≤ ‖x‖_∞` when `‖c_j‖ = 1` and `N = #ι > 0`. -/
private theorem norm_inv_mul_sum_mul_le {ι : Type*} [Fintype ι] [Nonempty ι] {N : ℕ}
    (hN : Fintype.card ι = N) (x c : ι → ℂ) (hc : ∀ j, ‖c j‖ = 1) :
    ‖(N : ℂ)⁻¹ * ∑ j, x j * c j‖ ≤ ‖x‖ := by
  have hNpos : (0 : ℝ) < N := by
    rw [← hN]
    exact_mod_cast Fintype.card_pos
  have hsum : ‖∑ j, x j * c j‖ ≤ (N : ℝ) * ‖x‖ := by
    calc ‖∑ j, x j * c j‖ ≤ ∑ j, ‖x j * c j‖ := norm_sum_le _ _
      _ = ∑ j, ‖x j‖ := by simp only [norm_mul, hc, mul_one]
      _ ≤ ∑ _j : ι, ‖x‖ := Finset.sum_le_sum fun j _ => norm_le_pi_norm x j
      _ = (N : ℝ) * ‖x‖ := by rw [Finset.sum_const, Finset.card_univ, hN, nsmul_eq_mul]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j, x j * c j‖ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
    _ = ‖x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

/-- `e(a/R) = e(b/R)` whenever `a ≡ b (mod R)`. -/
private theorem stdChar_natCast_div_congr {R a b : ℕ} (h : a % R = b % R) :
    IntMul.stdChar ((a : ℝ) / (R : ℝ)) = IntMul.stdChar ((b : ℝ) / (R : ℝ)) := by
  have key : ∀ n : ℕ, IntMul.stdChar ((n : ℝ) / (R : ℝ)) =
      IntMul.stdChar (((n % R : ℕ) : ℝ) / (R : ℝ)) := by
    intro n
    rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR
      simp
    · have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
      have hn : (n : ℝ) = ((n % R : ℕ) : ℝ) + (R : ℝ) * ((n / R : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mod_add_div n R).symm
      have hsplit : (n : ℝ) / (R : ℝ) =
          ((n % R : ℕ) : ℝ) / (R : ℝ) + (((n / R : ℕ) : ℤ) : ℝ) := by
        rw [hn, Int.cast_natCast]
        field_simp
      rw [hsplit, IntMul.stdChar_add_int]
  rw [key a, key b, h]

/-- `e(n x) = e(x)^n`. -/
private theorem stdChar_natCast_mul_eq_pow (n : ℕ) (x : ℝ) :
    IntMul.stdChar ((n : ℝ) * x) = IntMul.stdChar x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, IntMul.stdChar_add, ih, pow_succ]

/-- Conjugation reverses the character: `conj e(x) = e(-x)`. -/
private theorem star_stdChar_eq (x : ℝ) : star (IntMul.stdChar x) = IntMul.stdChar (-x) := by
  unfold IntMul.stdChar
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `e(x) = 1` forces `x ∈ ℤ`. -/
private theorem eq_int_of_stdChar_eq_one {x : ℝ} (h : IntMul.stdChar x = 1) :
    ∃ n : ℤ, x = n := by
  unfold IntMul.stdChar at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have hn1 : ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I =
      (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have him : 2 * Real.pi * x = (n : ℝ) * (2 * Real.pi) :=
    Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hn1)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi (by rw [him]; ring)

/-- `e(ju/R) = e(ku/R) e(((j-k) mod R) u/R)` for `j k u : Fin R`. -/
private theorem stdChar_fin_sub_mul {R : ℕ} (j k u : Fin R) :
    IntMul.stdChar ((((j : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) =
      IntMul.stdChar ((((k : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) *
        IntMul.stdChar (((((j - k : Fin R) : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) := by
  rw [← IntMul.stdChar_add]
  have hsum : ((((k : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) +
      (((((j - k : Fin R) : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) =
      (((((k : ℕ) + ((j - k : Fin R) : ℕ)) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) := by
    push_cast
    ring
  rw [hsum]
  apply stdChar_natCast_div_congr
  apply Nat.ModEq.mul_right
  show (j : ℕ) % R = ((k : ℕ) + ((j - k : Fin R) : ℕ)) % R
  have hk := k.is_lt
  rw [Fin.val_sub, Nat.add_mod_mod]
  have h' : (k : ℕ) + (R - (k : ℕ) + (j : ℕ)) = R + (j : ℕ) := by omega
  rw [h', Nat.add_mod_left]

/-- Reindexing `j ↦ j - k` on `Fin R`. -/
theorem sum_fin_sub_right {M : Type*} [AddCommMonoid M] {R : ℕ} (f : Fin R → M) (k : Fin R) :
    ∑ j : Fin R, f (j - k) = ∑ m : Fin R, f m := by
  have : NeZero R := ⟨(Fin.pos k).ne'⟩
  exact Fintype.sum_equiv (Equiv.subRight k) _ _ fun _ => rfl

/-- Reindexing `k ↦ j - k` on `Fin R`: `∑_k b_k a_{j-k} = ∑_k a_k b_{j-k}`. -/
theorem sum_mul_fin_sub_comm {M : Type*} [CommSemiring M] {R : ℕ} (a b : Fin R → M)
    (j : Fin R) :
    ∑ k : Fin R, b k * a (j - k) = ∑ k : Fin R, a k * b (j - k) := by
  have : NeZero R := ⟨(Fin.pos j).ne'⟩
  refine Fintype.sum_equiv (Equiv.subLeft j) _ _ fun k => ?_
  rw [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

/-- Orthogonality of the characters of `ℤ/R`:
`∑_u conj(e(mu/R)) e(uj/R) = R·[m = j]` for `m j : Fin R`. -/
theorem sum_star_stdChar_mul_stdChar {R : ℕ} (m j : Fin R) :
    ∑ u : Fin R, star (IntMul.stdChar ((((m : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ))) *
        IntMul.stdChar ((((u : ℕ) * (j : ℕ) : ℕ) : ℝ) / (R : ℝ)) =
      if m = j then (R : ℂ) else 0 := by
  have hR : 0 < R := Fin.pos m
  have hRr : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hterm : ∀ u : Fin R, star (IntMul.stdChar ((((m : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ))) *
      IntMul.stdChar ((((u : ℕ) * (j : ℕ) : ℕ) : ℝ) / (R : ℝ)) =
      IntMul.stdChar ((((j : ℕ) : ℝ) - ((m : ℕ) : ℝ)) / (R : ℝ)) ^ (u : ℕ) := by
    intro u
    rw [star_stdChar_eq, ← IntMul.stdChar_add, ← stdChar_natCast_mul_eq_pow]
    congr 1
    push_cast
    ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range
    (fun u => IntMul.stdChar ((((j : ℕ) : ℝ) - ((m : ℕ) : ℝ)) / (R : ℝ)) ^ u) R]
  by_cases hmj : m = j
  · subst hmj
    simp
  · rw [if_neg hmj]
    have hpow : IntMul.stdChar ((((j : ℕ) : ℝ) - ((m : ℕ) : ℝ)) / (R : ℝ)) ^ R = 1 := by
      rw [← stdChar_natCast_mul_eq_pow]
      have h : (R : ℝ) * ((((j : ℕ) : ℝ) - ((m : ℕ) : ℝ)) / (R : ℝ)) =
          ((((j : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) : ℝ) := by
        push_cast
        field_simp
      rw [h, IntMul.stdChar_int]
    have hne : IntMul.stdChar ((((j : ℕ) : ℝ) - ((m : ℕ) : ℝ)) / (R : ℝ)) ≠ 1 := by
      intro h1
      obtain ⟨n, hn⟩ := eq_int_of_stdChar_eq_one h1
      have h3 : ((j : ℕ) : ℝ) - ((m : ℕ) : ℝ) = (n : ℝ) * (R : ℝ) := (div_eq_iff hRr).1 hn
      have h2 : (((j : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) = n * (R : ℤ) := by
        exact_mod_cast h3
      have hdvd : (R : ℤ) ∣ (((j : ℕ) : ℤ) - ((m : ℕ) : ℤ)) := ⟨n, by rw [h2]; ring⟩
      have hj := j.is_lt
      have hm := m.is_lt
      have habs : |(((j : ℕ) : ℤ) - ((m : ℕ) : ℤ))| < (R : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact hmj (Fin.ext (by omega))
    have hgeom := geom_sum_mul (IntMul.stdChar ((((j : ℕ) : ℝ) - ((m : ℕ) : ℝ)) / (R : ℝ))) R
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

/-- Conjugate inversion: `F_R(conj(F_R c))_j = conj(c_j) / R`. -/
theorem dft_star_dft (R : ℕ) (c : Fin R → ℂ) (j : Fin R) :
    dft R (fun u => star (dft R c u)) j = (R : ℂ)⁻¹ * star (c j) := by
  have hRc : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos j).ne'
  have hstar : ∀ u : Fin R, star (dft R c u) = (R : ℂ)⁻¹ * ∑ m : Fin R,
      star (c m) * star (IntMul.stdChar ((((m : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ))) := by
    intro u
    rw [dft_apply, star_mul', star_inv₀, star_natCast, star_sum]
    simp only [star_mul']
  rw [dft_apply]
  simp only [hstar]
  have hswap : ∀ u : Fin R, ((R : ℂ)⁻¹ * ∑ m : Fin R, star (c m) *
        star (IntMul.stdChar ((((m : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)))) *
        IntMul.stdChar ((((u : ℕ) * (j : ℕ) : ℕ) : ℝ) / (R : ℝ)) =
      ∑ m : Fin R, (R : ℂ)⁻¹ * (star (c m) *
        (star (IntMul.stdChar ((((m : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ))) *
          IntMul.stdChar ((((u : ℕ) * (j : ℕ) : ℕ) : ℝ) / (R : ℝ)))) := by
    intro u
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [hswap]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_star_stdChar_mul_stdChar, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

/-- For real `a, b`: `Im((a + ib) ⊛ (a + ib))_j = 2 (a ⊛ b)_j`. -/
theorem im_cycConv_add_mul_I {R : ℕ} (a b : Fin R → ℝ) (j : Fin R) :
    (cycConv (fun k => (a k : ℂ) + (b k : ℂ) * Complex.I)
      (fun k => (a k : ℂ) + (b k : ℂ) * Complex.I) j).im = 2 * ∑ k, a k * b (j - k) := by
  have h1 : (cycConv (fun k => (a k : ℂ) + (b k : ℂ) * Complex.I)
      (fun k => (a k : ℂ) + (b k : ℂ) * Complex.I) j).im =
      ∑ k, (a k * b (j - k) + b k * a (j - k)) := by
    simp only [cycConv, Complex.im_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [h1, Finset.sum_add_distrib, sum_mul_fin_sub_comm a b j, two_mul]

/-! ## Contracts -/

/-- CONTRACT (Section 4.1 (`sec:bridge-conventions`)): `encIn t j = ∑_i j_i A_i`. -/
theorem encIn_val {d : ℕ} (t : Fin d → ℕ) (j : Idx t) :
    ((encIn t j : Fin (totalLen t)) : ℕ) = ∑ i, (j i : ℕ) * prefixProd t i := by
  rw [encIn, finPiFinEquiv_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [prefixProd_eq_prod_castLE]

/-- CONTRACT (Section 4.1, eq. (`eq:freq-digits`)): `encFreq t u = ∑_i u_i R/A_{i+1}`. -/
theorem encFreq_val {d : ℕ} (t : Fin d → ℕ) (u : Idx t) :
    ((encFreq t u : Fin (totalLen t)) : ℕ) = ∑ i, (u i : ℕ) * suffixProd t i := by
  simp only [encFreq, Equiv.trans_apply, finCongr_apply_coe, finPiFinEquiv_apply,
    Equiv.piCongrLeft'_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun b => ?_
  show ((u (Fin.rev b) : Fin (t (Fin.rev b))) : ℕ) *
      ∏ k : Fin b, t (Fin.rev (Fin.castLE b.is_lt.le k)) =
    ((u (Fin.rev b) : Fin (t (Fin.rev b))) : ℕ) * suffixProd t (Fin.rev b)
  rw [suffixProd_rev_eq_prod]

/-- CONTRACT: input digit extraction `j_i = ⌊j / A_i⌋ mod t_i`. -/
theorem encIn_symm_apply {d : ℕ} (t : Fin d → ℕ) (j : Fin (totalLen t)) (i : Fin d) :
    (((encIn t).symm j i : Fin (t i)) : ℕ) = ((j : ℕ) / prefixProd t i) % t i := by
  rw [prefixProd_eq_prod_castLE]
  rfl

/-- CONTRACT (Section 4.1, eq. (`eq:freq-digits`)): frequency digit extraction `u_i = ⌊f / (R/A_{i+1})⌋ mod t_i`. -/
theorem encFreq_symm_apply {d : ℕ} (t : Fin d → ℕ) (f : Fin (totalLen t)) (i : Fin d) :
    (((encFreq t).symm f i : Fin (t i)) : ℕ) = ((f : ℕ) / suffixProd t i) % t i := by
  simp only [encFreq, Equiv.symm_trans_apply]
  rw [val_piCongrLeft'_symm_apply t Fin.revPerm, finPiFinEquiv_symm_apply_val]
  show ((f : ℕ) / ∏ k : Fin (Fin.rev i), t (Fin.rev (Fin.castLE (Fin.rev i).is_lt.le k))) %
      t (Fin.rev (Fin.rev i)) = ((f : ℕ) / suffixProd t i) % t i
  rw [← suffixProd_rev_eq_prod, Fin.rev_rev]

/-- CONTRACT: `A_i · t_i · ∏_{l>i} t_l = R`. -/
theorem prefixProd_mul_mul_suffixProd {d : ℕ} (t : Fin d → ℕ) (i : Fin d) :
    prefixProd t i * t i * suffixProd t i = totalLen t := by
  unfold prefixProd suffixProd totalLen
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun l : Fin d => (l : ℕ) < (i : ℕ)),
    mul_assoc]
  congr 1
  have hmem : i ∈ Finset.univ.filter (fun l : Fin d => ¬ (l : ℕ) < (i : ℕ)) := by simp
  rw [← Finset.mul_prod_erase _ _ hmem]
  congr 1
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext l
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
    Fin.lt_def, Fin.ext_iff]
  omega

/-- CONTRACT (Section 3.3 (`sec:prelim-dft`)): `‖F_R‖_∞ ≤ 1`. -/
theorem norm_dft_le (R : ℕ) (x : Fin R → ℂ) : ‖dft R x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun u => ?_
  have : Nonempty (Fin R) := ⟨u⟩
  rw [dft_apply]
  exact norm_inv_mul_sum_mul_le (Fintype.card_fin R) x _ fun j => IntMul.norm_stdChar _

/-- CONTRACT (Section 3.3 (`sec:prelim-dft`)): `‖F_t‖_∞ ≤ 1`. -/
theorem norm_dftTensor_le {d : ℕ} (t : Fin d → ℕ) (U : Idx t → ℂ) : ‖dftTensor t U‖ ≤ ‖U‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg U)).2 fun u => ?_
  have : Nonempty (Idx t) := ⟨u⟩
  rw [dftTensor_apply]
  exact norm_inv_mul_sum_mul_le (by simp [totalLen, Fintype.card_pi]) U _
    fun j => IntMul.norm_stdChar _

/-- CONTRACT (Section 3.3 (`sec:prelim-dft`)): `F_R(a ⊛ b) = R (F_R a) ⊙ (F_R b)`. -/
theorem dft_cycConv (R : ℕ) (a b : Fin R → ℂ) :
    dft R (cycConv a b) = fun u => (R : ℂ) * (dft R a u * dft R b u) := by
  funext u
  have hR' : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos u).ne'
  simp only [dft_apply]
  have key : ∑ j : Fin R, cycConv a b j *
        IntMul.stdChar ((((j : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) =
      (∑ k : Fin R, a k * IntMul.stdChar ((((k : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ))) *
        (∑ m : Fin R, b m * IntMul.stdChar ((((m : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ))) := by
    simp only [cycConv, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    conv_rhs => rw [← sum_fin_sub_right _ k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [stdChar_fin_sub_mul j k u]
    ring
  rw [key]
  field_simp

/-- `F_R(conj((F_R z) ⊙ (F_R z)))_j = conj((z ⊛ z)_j) / R²` (from `dft_cycConv` and
`dft_star_dft`). -/
theorem dft_star_sq_dft (R : ℕ) (z : Fin R → ℂ) (j : Fin R) :
    dft R (fun u => star (dft R z u * dft R z u)) j =
      ((R : ℂ) ^ 2)⁻¹ * star (cycConv z z j) := by
  have hRc : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos j).ne'
  have hsq : (fun u => star (dft R z u * dft R z u)) =
      (R : ℂ)⁻¹ • (fun u => star (dft R (cycConv z z) u)) := by
    funext u
    have h : dft R (cycConv z z) u = (R : ℂ) * (dft R z u * dft R z u) := by rw [dft_cycConv]
    rw [Pi.smul_apply, smul_eq_mul, h, star_mul' (R : ℂ), star_natCast, ← mul_assoc,
      inv_mul_cancel₀ hRc, one_mul]
  have hsq' : dft R (fun u => star (dft R z u * dft R z u)) j =
      dft R ((R : ℂ)⁻¹ • (fun u => star (dft R (cycConv z z) u))) j :=
    congrArg (fun f => dft R f j) hsq
  rw [hsq', map_smul, Pi.smul_apply, smul_eq_mul, dft_star_dft, ← mul_assoc, ← mul_inv, sq]

/-- CONTRACT (Section 3.3, eq. (`eq:two-call`), [MS] Lemma 3.4): for real `a, b` and `z = a + ib`,
`a ⊛ b = -(R²/2) Im F_R(conj((F_R z) ⊙ (F_R z)))`. -/
theorem two_call_identity (R : ℕ) (a b : Fin R → ℝ) (j : Fin R) :
    cycConv (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) j =
      ((-((R : ℝ) ^ 2 / 2) *
        (dft R (fun u => star (dft R (fun k => (a k : ℂ) + (b k : ℂ) * Complex.I) u *
          dft R (fun k => (a k : ℂ) + (b k : ℂ) * Complex.I) u)) j).im : ℝ) : ℂ) := by
  have hRr : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos j).ne'
  rw [dft_star_sq_dft, show ((R : ℂ) ^ 2)⁻¹ = ((((R : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) by
      rw [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast],
    Complex.im_ofReal_mul, Complex.star_def, Complex.conj_im, im_cycConv_add_mul_I]
  have hinv : (R : ℝ) ^ 2 * ((R : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hRr)
  have hreal : -((R : ℝ) ^ 2 / 2) * (((R : ℝ) ^ 2)⁻¹ * -(2 * ∑ k, a k * b (j - k))) =
      ∑ k, a k * b (j - k) := by
    linear_combination (∑ k, a k * b (j - k)) * hinv
  rw [hreal]
  simp only [cycConv, Complex.ofReal_sum, Complex.ofReal_mul]

/-- CONTRACT (reuse bridge to IntMul): `F_R` agrees with `IntMul.dft1D` on the zero extension. -/
theorem dft_eq_intMul_dft1D (R : ℕ) (x : Fin R → ℂ) (u : Fin R) :
    dft R x u = IntMul.dft1D R (fun j => if h : j < R then x ⟨j, h⟩ else 0) u := by
  rw [dft_apply, IntMul.dft1D, one_div, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dif_pos j.is_lt]

end SubNLogN.Math.Common
