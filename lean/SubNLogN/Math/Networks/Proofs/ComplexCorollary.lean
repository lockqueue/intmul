import SubNLogN.Math.Networks.AppCLayer

/-!
# Lemma A.10 (`lem:transfer-phase`) network part: the corrected complex array corollary

Proof of `ComplexArrayCorollaryStmt` (`AppCLayer.lean`) from
* the frame invariant (5) ([OAI26, §3.2, (5)]), `FrameInvariantStmt 100` (`Framed.lean`),
* [OAI26] Lemma 5 for the complex network, `Lemma5ComplexStmt 100` (C1, `Scalar.lean`),
* the Prop. 8 endpoint contracts `Prop8EndpointStmt`, `Prop8ZeroFullStmt` (C3) and the
  multiplicativity of tensor powers `TpowMulStmt` (all in `PhaseFrames.lean`).

Paper: Lemma A.10 (`lem:transfer-phase`), Appendix A.5 (`sec:transfer-frames`); [OAI26, §3.5, Prop. 8].

The invertibility of the phase frames `C_U` is proved here (it is not a hypothesis): with the
unnormalised Walsh matrix `W_{yz} = (−1)^{y·z}` one has `W² = 2^m I` (character orthogonality on
`𝔽₂^m`) and `C_U = 2^{−m} W diag(i^{q_U}) W`, so `2^{−m} W diag((−i)^{q_U}) W` is a right inverse
of `C_U` (`CU_mul_CUinv`).

Helper declarations are in the namespace `SubNLogN.Math.Networks.ComplexCorollary`; the main
theorem `complexArrayCorollary_of` is in `SubNLogN.Math.Networks`.

## Plan
1. `applyCol` algebra: linear in the array, `applyCol A ∘ applyCol B = applyCol (A * B)`,
   `applyCol 1 = id`; an invertible matrix `A` gives a `ℂ`-linear equivalence of arrays
   `applyColEquiv A` with inverse `applyCol A⁻¹`.
2. `tpow k 1 = 1`; with `TpowMulStmt`, `tpow k A * tpow k A⁻¹ = 1`, so `tpow k A` is invertible
   when `A` is.
3. `C_U` is invertible (closed-form inverse with `i^{−q_U} = (−i)^{q_U}`).
4. Frames `D_v := applyColEquiv (tpow k (frameC v))` (`cxFrame`). Then
   `D_v ∘ D_u⁻¹ = applyCol (tpow k C_V * (tpow k C_U)⁻¹)`, i.e. the frame-invariant edge operators
   are exactly `cxEdgeOps k`, and the frame invariant gives
   `framedNet … (cxPre k s) w' = D_{sink w'} (net (D_source⁻¹ ∘ cxPre k s) w')`.
5. C1 with `half = 2⁻¹` evaluates `net` at `Y a` (input at `X a`), at `X a` (minus the input at
   `Y a`) and on scratch (its input). Case analysis on `w`:
   * `w = X a` (`ρ w = Y a`): `i^{27k} Z_{a,k} · tpow C_{U_a^⊥} · (tpow C_{U_a})⁻¹ · Z_{a,k}`
     `= tpow Cfull` (`Prop8EndpointStmt`);
   * `w = Y a` (`ρ w = X a`): the negation in `cxPost` cancels the sign of the exchange; the frames
     are `sink (X a) ↦ Cfull` and `source (Y a) ↦ 1` (`Prop8ZeroFullStmt`);
   * scratch: frames `Cfull` (sink) and `1` (source) (`Prop8ZeroFullStmt`).
-/

namespace SubNLogN.Math.Networks

/- All helper declarations live in the sub-namespace `ComplexCorollary`, to avoid clashes with
helpers of the same name in other proof files (`Endpoints*.lean`, `Prop8Edge.lean`). -/
namespace ComplexCorollary

/-! ### 1. `applyCol` algebra -/

section ApplyCol

variable {ι σ : Type*} [Fintype ι]

lemma applyCol_add (A : Matrix ι ι ℂ) (f g : ι × σ → ℂ) :
    applyCol A (f + g) = applyCol A f + applyCol A g := by
  funext p
  simp only [applyCol, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma applyCol_smul (A : Matrix ι ι ℂ) (c : ℂ) (f : ι × σ → ℂ) :
    applyCol A (c • f) = c • applyCol A f := by
  funext p
  simp only [applyCol, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- `applyCol` is multiplicative. -/
lemma applyCol_applyCol (A B : Matrix ι ι ℂ) (f : ι × σ → ℂ) :
    applyCol A (applyCol B f) = applyCol (A * B) f := by
  funext p
  simp only [applyCol, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

lemma applyCol_one [DecidableEq ι] (f : ι × σ → ℂ) : applyCol (1 : Matrix ι ι ℂ) f = f := by
  funext p
  simp [applyCol, Matrix.one_apply]

/-- An invertible matrix acting on the column index, as a `ℂ`-linear equivalence of arrays. -/
noncomputable def applyColEquiv [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : IsUnit A.det) :
    (ι × σ → ℂ) ≃ₗ[ℂ] (ι × σ → ℂ) where
  toFun := applyCol A
  invFun := applyCol A⁻¹
  map_add' := applyCol_add A
  map_smul' c f := applyCol_smul A c f
  left_inv f := by
    show applyCol A⁻¹ (applyCol A f) = f
    rw [applyCol_applyCol, Matrix.nonsing_inv_mul A hA, applyCol_one]
  right_inv f := by
    show applyCol A (applyCol A⁻¹ f) = f
    rw [applyCol_applyCol, Matrix.mul_nonsing_inv A hA, applyCol_one]

lemma applyColEquiv_apply [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : IsUnit A.det)
    (f : ι × σ → ℂ) : applyColEquiv A hA f = applyCol A f := rfl

lemma applyColEquiv_symm_apply [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : IsUnit A.det)
    (f : ι × σ → ℂ) : (applyColEquiv A hA).symm f = applyCol A⁻¹ f := rfl

end ApplyCol

/-! ### 2. Tensor powers -/

lemma tpow_one {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    tpow k (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp only [tpow, Matrix.one_apply, Fintype.prod_boole]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy, if_neg]
    exact fun h => hxy (funext h)

/-- With `TpowMulStmt`, the tensor power of an invertible matrix is invertible
(`tpow k A * tpow k A⁻¹ = tpow k 1 = 1`). -/
lemma isUnit_det_tpow (hTP : TpowMulStmt) {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ)
    {A : Matrix ι ι ℂ} (hA : IsUnit A.det) : IsUnit (tpow k A).det :=
  Matrix.isUnit_det_of_right_inverse (B := tpow k A⁻¹)
    (by rw [← hTP, Matrix.mul_nonsing_inv A hA, tpow_one])

/-! ### 3. The phase frames are invertible -/

lemma neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

lemma zmod2_add_eq_zero_iff : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide

lemma zmod2_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

section Dot

variable {h : ℕ}

lemma dotC_comm (x y : Pt h) : dotC x y = dotC y x := by
  simp only [dotC, mul_comm]

lemma dotC_add_left (x y z : Pt h) : dotC (x + y) z = dotC x z + dotC y z := by
  simp only [dotC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotC_add_right (x y z : Pt h) : dotC x (y + z) = dotC x y + dotC x z := by
  simp only [dotC, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotC_zero_left (z : Pt h) : dotC 0 z = 0 := by
  simp only [dotC, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

lemma dotC_single (u : Pt h) (p : Cube h) : dotC u (Pi.single p 1) = u p := by
  simp [dotC, Pi.single_apply]

lemma pt_add_eq_zero_iff (x y : Pt h) : x + y = 0 ↔ x = y := by
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, zmod2_add_eq_zero_iff]

lemma card_pt : Fintype.card (Pt h) = 2 ^ (h ^ 3) := by
  rw [Fintype.card_fun, ZMod.card]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Character orthogonality on `𝔽₂^m`: `Σ_z (−1)^{u·z} = 2^m [u = 0]`. -/
lemma sum_neg_one_pow_dotC (u : Pt h) :
    ∑ z : Pt h, (-1 : ℂ) ^ (dotC u z).val = if u = 0 then (2 : ℂ) ^ (h ^ 3) else 0 := by
  split_ifs with hu
  · subst hu
    simp only [dotC_zero_left, ZMod.val_zero, pow_zero, Finset.sum_const, Finset.card_univ,
      card_pt, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp hu
    obtain ⟨e, he⟩ : ∃ e : Pt h, dotC u e = 1 :=
      ⟨Pi.single p 1, by rw [dotC_single]; exact zmod2_eq_one_of_ne_zero _ hp⟩
    -- shifting the summation variable by `e` multiplies every term by `(−1)^{u·e} = −1`
    have hshift := Equiv.sum_comp (Equiv.addRight e) (fun z : Pt h => (-1 : ℂ) ^ (dotC u z).val)
    simp only [Equiv.coe_addRight, dotC_add_right, neg_one_pow_val_add, he, ← Finset.sum_mul]
      at hshift
    have h1 : (-1 : ℂ) ^ (1 : ZMod 2).val = -1 := by
      rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
    rw [h1] at hshift
    linear_combination (-1 / 2 : ℂ) * hshift

end Dot

/-- The unnormalised Walsh–Hadamard matrix `W_{yz} = (−1)^{y·z}` on `𝔽₂^m`. -/
noncomputable def walshW (h : ℕ) : Matrix (Pt h) (Pt h) ℂ := fun y z => (-1 : ℂ) ^ (dotC y z).val

lemma walshW_mul_self (h : ℕ) :
    walshW h * walshW h = (2 : ℂ) ^ (h ^ 3) • (1 : Matrix (Pt h) (Pt h) ℂ) := by
  ext y x
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  have hz : ∀ z, walshW h y z * walshW h z x = (-1 : ℂ) ^ (dotC (y + x) z).val := by
    intro z
    simp only [walshW]
    rw [dotC_add_left, neg_one_pow_val_add, dotC_comm z x]
  rw [Finset.sum_congr rfl (fun z _ => hz z), sum_neg_one_pow_dotC]
  by_cases hyx : y = x
  · simp [hyx, (pt_add_eq_zero_iff x x).2 rfl]
  · simp [hyx, mt (pt_add_eq_zero_iff y x).1 hyx]

/-- `C_U = 2^{−m} W diag(i^{q_U}) W`. -/
lemma CU_eq_walsh {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) :
    CU U = ((2 : ℂ) ^ (h ^ 3))⁻¹ •
      (walshW h * Matrix.diagonal (fun z => Complex.I ^ qU U z) * walshW h) := by
  ext y x
  rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  simp only [CU, Matrix.mul_diagonal, walshW]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [dotC_add_left, neg_one_pow_val_add, dotC_comm z x]
  ring

/-- Closed form of `C_U⁻¹`: `2^{−m} W diag(i^{−q_U}) W` with `i^{−q} = (−i)^q`. -/
noncomputable def CUinv {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) : Matrix (Pt h) (Pt h) ℂ :=
  ((2 : ℂ) ^ (h ^ 3))⁻¹ •
    (walshW h * Matrix.diagonal (fun z => (-Complex.I) ^ qU U z) * walshW h)

lemma CU_mul_CUinv {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) : CU U * CUinv U = 1 := by
  have hc : ((2 : ℂ) ^ (h ^ 3)) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hD : Matrix.diagonal (fun z => Complex.I ^ qU U z) *
      Matrix.diagonal (fun z => (-Complex.I) ^ qU U z) = (1 : Matrix (Pt h) (Pt h) ℂ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext z
    rw [← mul_pow, mul_neg, Complex.I_mul_I, neg_neg, one_pow]
  have hW : walshW h * Matrix.diagonal (fun z => Complex.I ^ qU U z) * walshW h *
      (walshW h * Matrix.diagonal (fun z => (-Complex.I) ^ qU U z) * walshW h) =
      ((2 : ℂ) ^ (h ^ 3) * (2 : ℂ) ^ (h ^ 3)) • (1 : Matrix (Pt h) (Pt h) ℂ) := by
    calc _ = walshW h * Matrix.diagonal (fun z => Complex.I ^ qU U z) * (walshW h * walshW h) *
          Matrix.diagonal (fun z => (-Complex.I) ^ qU U z) * walshW h := by
            simp only [Matrix.mul_assoc]
      _ = (2 : ℂ) ^ (h ^ 3) • (walshW h * (Matrix.diagonal (fun z => Complex.I ^ qU U z) *
            Matrix.diagonal (fun z => (-Complex.I) ^ qU U z)) * walshW h) := by
            rw [walshW_mul_self]
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hD, Matrix.mul_one, walshW_mul_self, smul_smul]
  rw [CU_eq_walsh, CUinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW, smul_smul]
  rw [show ((2 : ℂ) ^ (h ^ 3))⁻¹ * ((2 : ℂ) ^ (h ^ 3))⁻¹ * ((2 : ℂ) ^ (h ^ 3) * (2 : ℂ) ^ (h ^ 3))
      = 1 by field_simp]
  exact one_smul _ _

/-- The phase frames `C_U` are invertible (every `h`, every binary label `U`). -/
theorem isUnit_det_CU {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) : IsUnit (CU U).det :=
  Matrix.isUnit_det_of_right_inverse (CU_mul_CUinv U)

theorem isUnit_det_frameC {h : ℕ} (v : Vertex .complex h) : IsUnit (frameC v).det :=
  isUnit_det_CU _

/-! ### 4. Frames as linear equivalences of arrays; the corollary -/

/-- The frame `D_v = C_{U_v}^{⊗k}` acting on arrays with `k` columns and spectators `σ`, as a
`ℂ`-linear equivalence (inverse `applyCol (tpow k C_{U_v})⁻¹`). -/
noncomputable def cxFrame (hTP : TpowMulStmt) (σ : Type) (k : ℕ) (v : Vertex .complex 100) :
    ((Fin k → Pt 100) × σ → ℂ) ≃ₗ[ℂ] ((Fin k → Pt 100) × σ → ℂ) :=
  applyColEquiv (tpow k (frameC v)) (isUnit_det_tpow hTP k (isUnit_det_frameC v))

lemma cxFrame_apply (hTP : TpowMulStmt) (σ : Type) (k : ℕ) (v : Vertex .complex 100)
    (f : (Fin k → Pt 100) × σ → ℂ) : cxFrame hTP σ k v f = applyCol (tpow k (frameC v)) f :=
  rfl

lemma cxFrame_symm_apply (hTP : TpowMulStmt) (σ : Type) (k : ℕ) (v : Vertex .complex 100)
    (f : (Fin k → Pt 100) × σ → ℂ) :
    (cxFrame hTP σ k v).symm f = applyCol (tpow k (frameC v))⁻¹ f := rfl

/-- The logical inputs `D_{source w}⁻¹ (cxPre k s w)` of the scalar network. -/
noncomputable def cxLogical (hTP : TpowMulStmt) (σ : Type) (k : ℕ)
    (s : Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ)) :
    Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ) :=
  fun w => (cxFrame hTP σ k (.source w)).symm (cxPre k s w)

/-- The frame-invariant edge operators `D_v ∘ D_u⁻¹` are the physical edge operators
`cxEdgeOps k`. -/
lemma cxEdgeOps_eq (hTP : TpowMulStmt) (σ : Type) (k : ℕ) :
    (cxEdgeOps k : EdgeOps .complex 100 ((Fin k → Pt 100) × σ → ℂ)) =
      fun _ e x => cxFrame hTP σ k e.2 ((cxFrame hTP σ k e.1).symm x) := by
  funext _ e x
  simp only [cxEdgeOps, cxFrame_apply, cxFrame_symm_apply, applyCol_applyCol]

/-- The frame invariant (5) ([OAI26, §3.2, (5)]) for the complex network on `k` columns, with the frames `cxFrame`. -/
lemma cxFramedNet_eq (hFI : FrameInvariantStmt 100) (hTP : TpowMulStmt) (σ : Type) (k : ℕ)
    (s : Role .complex 100 → ((Fin k → Pt 100) × σ → ℂ)) (w : Role .complex 100) :
    framedNet .complex (2⁻¹ : ℂ) (cxEdgeOps k) (cxPre k s) w =
      cxFrame hTP σ k (.sink w) (net .complex (2⁻¹ : ℂ) (cxLogical hTP σ k s) w) := by
  rw [cxEdgeOps_eq hTP σ k]
  exact hFI .complex (2⁻¹ : ℂ) (cxFrame hTP σ k) (cxPre k s) w

end ComplexCorollary

open ComplexCorollary in
/-- **Lemma A.10 (`lem:transfer-phase`), network part** ([OAI26, §3.5, Prop. 8]):
`ComplexArrayCorollaryStmt`, from the frame invariant (5) ([OAI26, §3.2, (5)]), C1 ([OAI26] Lemma 5, complex network), the
Prop. 8 endpoint contracts C3 and the multiplicativity of tensor powers. The invertibility of the
phase frames is proved in this file (`isUnit_det_frameC`), so it is not a hypothesis. -/
theorem complexArrayCorollary_of (hFI : FrameInvariantStmt 100) (hC1 : Lemma5ComplexStmt 100)
    (hEnd : Prop8EndpointStmt) (hZF : Prop8ZeroFullStmt) (hTP : TpowMulStmt) :
    ComplexArrayCorollaryStmt := by
  intro σ k hk s w
  obtain ⟨hY, hX, hS⟩ := hC1 (2⁻¹ : ℂ) (by norm_num) (cxLogical hTP σ k s)
  cases w with
  | X a =>
    show applyCol ((Complex.I ^ (27 * k)) • Zk k (ua a))
      (framedNet .complex (2⁻¹ : ℂ) (cxEdgeOps k) (cxPre k s) (.Y a)) = _
    rw [cxFramedNet_eq hFI hTP σ k s, hY a]
    show applyCol ((Complex.I ^ (27 * k)) • Zk k (ua a))
      (applyCol (tpow k (frameC (.sink (.Y a))))
        (applyCol (tpow k (frameC (.source (.X a))))⁻¹ (applyCol (Zk k (ua a)) (s (.X a))))) =
      applyCol (tpow k Cfull) (s (.X a))
    have hM : (Complex.I ^ (27 * k)) • Zk k (ua a) * tpow k (frameC (.sink (.Y a))) *
        (tpow k (frameC (.source (.X a))))⁻¹ * Zk k (ua a) = tpow k Cfull := by
      rw [← hEnd a k hk]
      simp only [Matrix.smul_mul]
    rw [applyCol_applyCol, applyCol_applyCol, applyCol_applyCol, hM]
  | Y a =>
    show -(framedNet .complex (2⁻¹ : ℂ) (cxEdgeOps k) (cxPre k s) (.X a)) = _
    rw [cxFramedNet_eq hFI hTP σ k s, hX a, map_neg, neg_neg]
    show applyCol (tpow k (frameC (.sink (.X a))))
      (applyCol (tpow k (frameC (.source (.Y a))))⁻¹ (s (.Y a))) =
      applyCol (tpow k Cfull) (s (.Y a))
    rw [(hZF (.X a)).2 (fun _ h => by cases h), (hZF (.Y a)).1 (fun _ h => by cases h),
      tpow_one, inv_one, applyCol_one]
  | side j ι p =>
    show framedNet .complex (2⁻¹ : ℂ) (cxEdgeOps k) (cxPre k s) (.side j ι p) = _
    rw [cxFramedNet_eq hFI hTP σ k s, hS (.side j ι p) trivial]
    show applyCol (tpow k (frameC (.sink (.side j ι p))))
      (applyCol (tpow k (frameC (.source (.side j ι p))))⁻¹ (s (.side j ι p))) = _
    rw [(hZF (.side j ι p)).2 (fun _ h => by cases h),
      (hZF (.side j ι p)).1 (fun _ h => by cases h), tpow_one, inv_one, applyCol_one]
  | center j ι c =>
    show framedNet .complex (2⁻¹ : ℂ) (cxEdgeOps k) (cxPre k s) (.center j ι c) = _
    rw [cxFramedNet_eq hFI hTP σ k s, hS (.center j ι c) trivial]
    show applyCol (tpow k (frameC (.sink (.center j ι c))))
      (applyCol (tpow k (frameC (.source (.center j ι c))))⁻¹ (s (.center j ι c))) = _
    rw [(hZF (.center j ι c)).2 (fun _ h => by cases h),
      (hZF (.center j ι c)).1 (fun _ h => by cases h), tpow_one, inv_one, applyCol_one]

end SubNLogN.Math.Networks
