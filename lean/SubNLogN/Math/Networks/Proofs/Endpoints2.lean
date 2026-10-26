import SubNLogN.Math.Networks.Proofs.Endpoints

/-!
# Endpoint certificates, part 2: the complex network (C3)

Proofs of `Prop8ZeroFullStmt` and `Prop8EndpointStmt` (`PhaseFrames.lean`) at `h = 100`
([OAI26, §3.5, Prop. 8]; Appendix D.2, Proposition D.3 (`oai:prop8`)). Both identities are proved for every `h`
(`EndpointsAux.prop8ZeroFull_gen`, `EndpointsAux.prop8Endpoint_gen`) and specialized to `h = 100`.
All helpers live in the namespace `SubNLogN.Math.Networks.EndpointsAux`.

## Plan
* Characters `χ(a) = (-1)^a` on `𝔽₂`; `Σ_z χ(v·z) = 2^m [v = 0]` (product over coordinates).
* Fourier matrices `F φ = 2^{-m} H diag(φ) H`, `H_{yz} = χ(y·z)`, entrywise the shape of `CU`:
  `C_U = F(i^{q_U})`. From `H² = 2^m I`: `F φ F ψ = F (φψ)`, `F 1 = I`; moreover
  `F(χ(u·)) = X_u` and `F(i^{wt}) = C^{⊗m}` (product over coordinates).
* `C_0 = I` (`P_0 = 0`), `C_𝓕 = C^{⊗m}` (`P_𝓕 = id`, `i^{wt mod 4} = i^{wt}`).
* `U_a = 𝔽₂ ∙ u_a`, `U_a^⊥ = labUperp a` (generic key lemma, `Endpoints.lean`), `u_a·u_a = 1`,
  `wt u_a = 27`; `P_{U_a} x = (u_a·x) u_a`, `P_{U_a^⊥} x = x - (u_a·x) u_a`;
  `wt(x - u) + 2|x ∩ u| = wt x + wt u` gives `i^{q_{U^⊥}(x)} i^{-q_U(x)} = i^{wt x} χ(u·x)`, hence
  `C_{U^⊥} C_U^{-1} = C^{⊗m} X_u` with the explicit inverse `C_U^{-1} = F(i^{-q_U})`.
* `i^{27} Z_u C^{⊗m} X_u Z_u = C^{⊗m}`: coordinatewise `i Z C X Z = C`.
* `k` columns: `tpow` is multiplicative, `Z_{a,k} = tpow k Z_u`, `(tpow k A)⁻¹ = tpow k A⁻¹`,
  `c^k • tpow k A = tpow k (c • A)`.
-/

namespace SubNLogN.Math.Networks

namespace EndpointsAux

open Matrix

/-! ### `𝔽₂` facts and the character `χ` -/

lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

lemma z2_val_zero : (0 : ZMod 2).val = 0 := rfl

lemma z2_val_one : (1 : ZMod 2).val = 1 := rfl

lemma z2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

lemma sum_zmod2 {M : Type*} [AddCommMonoid M] (g : ZMod 2 → M) :
    ∑ b : ZMod 2, g b = g 0 + g 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]

/-- The character `χ(a) = (-1)^a` of `𝔽₂`. -/
noncomputable def chi (a : ZMod 2) : ℂ := (-1 : ℂ) ^ a.val

lemma chi_zero : chi 0 = 1 := by
  rw [chi, z2_val_zero, pow_zero]

lemma chi_one : chi 1 = -1 := by
  rw [chi, z2_val_one, pow_one]

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rw [chi, chi, chi, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

lemma chi_sum {α : Type*} (s : Finset α) (f : α → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, chi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma pt_neg {h : ℕ} (y : Pt h) : -y = y := funext fun p => ZMod.neg_eq_self_mod_two (y p)

lemma pt_add_eq_zero_iff {h : ℕ} (x y : Pt h) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, pt_neg]

lemma pt_add_self {h : ℕ} (y : Pt h) : y + y = 0 := (pt_add_eq_zero_iff y y).2 rfl

/-! ### Dot products, weights, character sums -/

lemma dotC_add_left {h : ℕ} (x y z : Pt h) : dotC (x + y) z = dotC x z + dotC y z := by
  simp only [dotC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotC_comm {h : ℕ} (x y : Pt h) : dotC x y = dotC y x := by
  simp only [dotC, mul_comm]

lemma chi_dotC {h : ℕ} (x z : Pt h) : chi (dotC x z) = ∏ p, chi (x p * z p) := chi_sum _ _

lemma wt_eq_sum {h : ℕ} (x : Pt h) : wt x = ∑ p, (x p).val := by
  unfold wt
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  generalize x p = c
  revert c; decide

lemma wt_zero {h : ℕ} : wt (0 : Pt h) = 0 := by
  rw [wt_eq_sum]; simp

lemma sum_chi_mul (c : ZMod 2) : ∑ b : ZMod 2, chi (c * b) = if c = 0 then 2 else 0 := by
  rw [sum_zmod2, mul_zero, mul_one, chi_zero]
  rcases zmod2_cases c with rfl | rfl
  · rw [chi_zero, if_pos rfl]; norm_num
  · rw [chi_one, if_neg (by decide)]; norm_num

lemma sum_chi_dotC {h : ℕ} (v : Pt h) :
    ∑ z : Pt h, chi (dotC v z) = if v = 0 then (2 : ℂ) ^ (h ^ 3) else 0 := by
  simp only [chi_dotC]
  rw [show (∑ z : Pt h, ∏ p, chi (v p * z p)) = ∏ p, ∑ b : ZMod 2, chi (v p * b) from
    (Fintype.prod_sum (fun p b => chi (v p * b))).symm]
  simp only [sum_chi_mul]
  split_ifs with hv
  · subst hv
    have : ∀ p : Cube h, (if (0 : Pt h) p = 0 then (2 : ℂ) else 0) = 2 := fun p => if_pos rfl
    rw [Finset.prod_congr rfl (fun p _ => this p), Finset.prod_const, Finset.card_univ,
      card_cube]
  · obtain ⟨p, hp⟩ := Function.ne_iff.1 hv
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

/-! ### Fourier matrices `F φ = 2^{-m} H diag(φ) H` -/

/-- `F φ`, written entrywise exactly as `CU` (so `CU U = F (i^{q_U})` by definition). -/
noncomputable def Fm {h : ℕ} (φ : Pt h → ℂ) : Matrix (Pt h) (Pt h) ℂ :=
  fun y x => ((2 : ℂ) ^ (h ^ 3))⁻¹ * ∑ z : Pt h, (-1 : ℂ) ^ (dotC (x + y) z).val * φ z

lemma CU_eq_Fm {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) :
    CU U = Fm (fun z => Complex.I ^ qU U z) := rfl

/-- The unnormalized Walsh-Hadamard matrix `H_{yz} = (-1)^{y·z}`. -/
noncomputable def Hd {h : ℕ} : Matrix (Pt h) (Pt h) ℂ := fun y z => chi (dotC y z)

lemma two_pow_ne_zero (h : ℕ) : (2 : ℂ) ^ (h ^ 3) ≠ 0 := pow_ne_zero _ two_ne_zero

lemma Fm_eq {h : ℕ} (φ : Pt h → ℂ) :
    Fm φ = ((2 : ℂ) ^ (h ^ 3))⁻¹ • (Hd * Matrix.diagonal φ * Hd) := by
  ext y x
  rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  simp only [Matrix.mul_diagonal, Fm, Hd]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  show chi (dotC (x + y) z) * φ z = chi (dotC y z) * φ z * chi (dotC z x)
  rw [dotC_add_left, chi_add, dotC_comm z x]
  ring

lemma Hd_mul_Hd {h : ℕ} : (Hd : Matrix (Pt h) (Pt h) ℂ) * Hd = ((2 : ℂ) ^ (h ^ 3)) • 1 := by
  ext y x
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have e : ∀ z : Pt h, Hd y z * Hd z x = chi (dotC (y + x) z) := by
    intro z
    show chi (dotC y z) * chi (dotC z x) = _
    rw [dotC_add_left, chi_add, dotC_comm z x]
  simp only [e, sum_chi_dotC, pt_add_eq_zero_iff]
  split_ifs <;> simp

lemma Fm_mul {h : ℕ} (φ ψ : Pt h → ℂ) : Fm φ * Fm ψ = Fm (φ * ψ) := by
  have key : (Hd * diagonal φ * Hd) * (Hd * diagonal ψ * Hd) =
      ((2 : ℂ) ^ (h ^ 3)) • (Hd * diagonal (φ * ψ) * Hd) := by
    calc (Hd * diagonal φ * Hd) * (Hd * diagonal ψ * Hd)
        = Hd * diagonal φ * (Hd * Hd) * diagonal ψ * Hd := by simp only [Matrix.mul_assoc]
      _ = ((2 : ℂ) ^ (h ^ 3)) • (Hd * (diagonal φ * diagonal ψ) * Hd) := by
          rw [Hd_mul_Hd]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.diagonal_mul_diagonal]; rfl
  rw [Fm_eq, Fm_eq, Fm_eq, Matrix.smul_mul, Matrix.mul_smul, key, smul_smul, smul_smul]
  congr 1
  field_simp [two_pow_ne_zero h]

lemma Fm_one {h : ℕ} : Fm (fun _ : Pt h => (1 : ℂ)) = 1 := by
  rw [Fm_eq, Matrix.diagonal_one, Matrix.mul_one, Hd_mul_Hd, smul_smul,
    inv_mul_cancel₀ (two_pow_ne_zero h), one_smul]

/-- `F(χ(u·)) = X_u`: the character becomes a translation. -/
lemma Fm_chi {h : ℕ} (u : Pt h) : Fm (fun z => chi (dotC u z)) = Xv u := by
  ext y x
  simp only [Fm, Xv]
  have e : ∀ z, (-1 : ℂ) ^ (dotC (x + y) z).val * chi (dotC u z) = chi (dotC (x + y + u) z) := by
    intro z
    rw [dotC_add_left (x + y) u, chi_add]; rfl
  simp only [e, sum_chi_dotC]
  have hiff : x + y + u = 0 ↔ x = y + u := by rw [add_assoc, pt_add_eq_zero_iff]
  by_cases hc : x = y + u
  · rw [if_pos (hiff.2 hc), if_pos hc, inv_mul_cancel₀ (two_pow_ne_zero h)]
  · rw [if_neg (mt hiff.1 hc), if_neg hc, mul_zero]

lemma C2_00 : C2 0 0 = ka := by show (if (0 : ZMod 2) = 0 then ka else kb) = ka; exact if_pos rfl
lemma C2_11 : C2 1 1 = ka := by show (if (1 : ZMod 2) = 1 then ka else kb) = ka; exact if_pos rfl
lemma C2_01 : C2 0 1 = kb := by
  show (if (0 : ZMod 2) = 1 then ka else kb) = kb; exact if_neg (by decide)
lemma C2_10 : C2 1 0 = kb := by
  show (if (1 : ZMod 2) = 0 then ka else kb) = kb; exact if_neg (by decide)

lemma coord_iwt (a b : ZMod 2) :
    (2 : ℂ)⁻¹ * ∑ c : ZMod 2, chi ((a + b) * c) * Complex.I ^ c.val = C2 b a := by
  rw [sum_zmod2, mul_zero, mul_one, chi_zero, z2_val_zero, z2_val_one, pow_zero, pow_one]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rw [add_zero, chi_zero, C2_00, ka]; ring
  · rw [zero_add, chi_one, C2_10, kb]; ring
  · rw [add_zero, chi_one, C2_01, kb]; ring
  · rw [z2_one_add_one, chi_zero, C2_11, ka]; ring

/-- `F(i^{wt}) = C^{⊗m}` (product over coordinates). -/
lemma Fm_iwt {h : ℕ} : Fm (fun z : Pt h => Complex.I ^ wt z) = Cfull := by
  ext y x
  simp only [Fm, Cfull]
  have hz : ∀ z : Pt h, (-1 : ℂ) ^ (dotC (x + y) z).val * Complex.I ^ wt z =
      ∏ p, (chi ((x p + y p) * z p) * Complex.I ^ (z p).val) := by
    intro z
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← wt_eq_sum]
    show chi (dotC (x + y) z) * _ = _
    rw [chi_dotC]
    rfl
  simp only [hz]
  rw [show (∑ z : Pt h, ∏ p, (chi ((x p + y p) * z p) * Complex.I ^ (z p).val)) =
      ∏ p, ∑ b : ZMod 2, chi ((x p + y p) * b) * Complex.I ^ b.val from
    (Fintype.prod_sum (fun p b => chi ((x p + y p) * b) * Complex.I ^ b.val)).symm]
  have hc : ((2 : ℂ) ^ (h ^ 3))⁻¹ = ∏ _p : Cube h, (2 : ℂ)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, card_cube, inv_pow]
  rw [hc, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => coord_iwt (x p) (y p)

/-! ### Complex labels: forms, `u_a`, projections -/

lemma betaC3_apply {h : ℕ} (x y : Pt h) : betaC3 h x y = dotC x y := by
  rw [betaC3, Matrix.toBilin'_apply', Matrix.one_mulVec]; rfl

lemma betaC3_fac {h : ℕ} : CubeFac (betaC h) (betaC3 h) := by
  intro u v w u' v' w'
  have e : betaC3 h = Matrix.toBilin' (kron3 1 1 1) := by rw [kron3_one]; rfl
  rw [e]
  exact toBilin'_kron3_pure3 1 u v w u' v' w'

lemma betaC_ind_self {h : ℕ} (t : Tri h) : betaC h (ind t) (ind t) = 1 := by
  rw [betaC, Matrix.toBilin'_apply', Matrix.one_mulVec]
  simp only [dotProduct, ind_mul_self, sum_ind]
  decide

lemma betaC_ind_ne {h : ℕ} (t : Tri h) : betaC h (ind t) (ind t) ≠ 0 := by
  rw [betaC_ind_self]; exact one_ne_zero

lemma betaC3_symm {h : ℕ} (x y : Pt h) : betaC3 h x y = betaC3 h y x := by
  rw [betaC3_apply, betaC3_apply, dotC_comm]

lemma betaC3_nondeg {h : ℕ} (m : Pt h) (hm : ∀ n, betaC3 h n m = 0) : m = 0 :=
  toBilin'_nondeg (1 : Matrix (Cube h) (Cube h) (ZMod 2)) 1 (Matrix.mul_one 1) m hm

lemma ua_val {h : ℕ} (a : Addr h) (p : Cube h) :
    (ua a p).val = (if p.1 ∈ a.1.1 then 1 else 0) * (if p.2.1 ∈ a.2.1.1 then 1 else 0) *
      (if p.2.2 ∈ a.2.2.1 then 1 else 0) := by
  simp only [ua, ind]
  split_ifs <;> rfl

/-- `wt u_a = 27`. -/
lemma wt_ua {h : ℕ} (a : Addr h) : wt (ua a) = 27 := by
  rw [wt_eq_sum]
  simp only [ua_val]
  rw [sum_cube_mul (fun i => if i ∈ a.1.1 then 1 else 0) (fun i => if i ∈ a.2.1.1 then 1 else 0)
    (fun i => if i ∈ a.2.2.1 then 1 else 0)]
  simp only [Fintype.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one, a.1.2, a.2.1.2,
    a.2.2.2]
  rfl

lemma dotC_self_eq {h : ℕ} (x : Pt h) : dotC x x = ((wt x : ℕ) : ZMod 2) := by
  rw [wt_eq_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  generalize x p = c
  revert c; decide

lemma dotC_ua_self {h : ℕ} (a : Addr h) : dotC (ua a) (ua a) = 1 := by
  rw [dotC_self_eq, wt_ua]; decide

lemma betaC3_ua_ne {h : ℕ} (a : Addr h) : betaC3 h (ua a) (ua a) ≠ 0 := by
  rw [betaC3_apply, dotC_ua_self]; exact one_ne_zero

lemma labC_source_X {h : ℕ} (a : Addr h) :
    labC (Vertex.source (κ := .complex) (Role.X a)) = (ZMod 2) ∙ ua a :=
  labelSub_labU (betaC h) a

lemma labC_sink_Y {h : ℕ} (a : Addr h) :
    labC (Vertex.sink (κ := .complex) (Role.Y a)) = (betaC3 h).orthogonal ((ZMod 2) ∙ ua a) :=
  labelSub_labUperp (betaC h) (betaC3 h) betaC3_fac a (betaC_ind_ne _) (betaC_ind_ne _)
    (betaC_ind_ne _)

lemma proj_U_apply {h : ℕ} (a : Addr h) (z : Pt h) :
    projAlong (betaC3 h) ((ZMod 2) ∙ ua a) z = dotC (ua a) z • ua a := by
  rw [projAlong_span_apply _ (betaC3_ua_ne a) z, betaC3_apply, betaC3_apply, dotC_ua_self,
    div_one]

lemma proj_V_apply {h : ℕ} (a : Addr h) (z : Pt h) :
    projAlong (betaC3 h) ((betaC3 h).orthogonal ((ZMod 2) ∙ ua a)) z =
      z - dotC (ua a) z • ua a := by
  rw [projAlong_perp_apply _ betaC3_symm betaC3_nondeg (betaC3_ua_ne a) z, betaC3_apply,
    betaC3_apply, dotC_ua_self, div_one]

/-! ### Phase ratio on the route `X_a → Y_a` -/

lemma I_pow_mod4 (n : ℕ) : Complex.I ^ (n % 4) = Complex.I ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

/-- `wt(z - u) ≡ wt z + 1 (mod 4)` when `wt u = 27` and `u·z = 1`
(`wt(z - u) + 2|z ∩ u| = wt z + wt u`, `|z ∩ u|` odd). -/
lemma wt_sub_mod4 {h : ℕ} (u z : Pt h) (hu : wt u = 27) (hd : dotC u z = 1) :
    wt (z - u) % 4 = (wt z + 1) % 4 := by
  have key : wt (z - u) + 2 * (∑ p, (z p).val * (u p).val) = wt z + wt u := by
    simp only [wt_eq_sum, Pi.sub_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    generalize z p = a
    generalize u p = b
    revert a b; decide
  have hodd : (∑ p, (z p).val * (u p).val) % 2 = 1 := by
    have e : ((∑ p, (z p).val * (u p).val : ℕ) : ZMod 2) = 1 := by
      rw [Nat.cast_sum, ← hd, dotC]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_comm]
    have := congrArg ZMod.val e
    rw [ZMod.val_natCast] at this
    exact this
  omega

/-- `i^{q_{U_a^⊥}(z)} i^{-q_{U_a}(z)} = i^{wt z} (-1)^{u_a·z}` ([OAI26, §3.5, Prop. 8]). -/
lemma phase_ratio {h : ℕ} (a : Addr h) (z : Pt h) :
    Complex.I ^ qU (labC (Vertex.sink (κ := .complex) (Role.Y a))) z *
      (Complex.I ^ qU (labC (Vertex.source (κ := .complex) (Role.X a))) z)⁻¹ =
    Complex.I ^ wt z * chi (dotC (ua a) z) := by
  rw [qU, qU, labC_sink_Y, labC_source_X, proj_V_apply, proj_U_apply]
  rcases zmod2_cases (dotC (ua a) z) with hd | hd
  · rw [hd, zero_smul, sub_zero, wt_zero, Nat.zero_mod, pow_zero, inv_one, mul_one, chi_zero,
      mul_one, I_pow_mod4]
  · have h27 : (Complex.I ^ (27 % 4))⁻¹ = Complex.I := by
      rw [show 27 % 4 = 3 from rfl, pow_succ, Complex.I_sq, neg_one_mul, inv_neg, Complex.inv_I,
        neg_neg]
    rw [hd, one_smul, wt_ua, h27, wt_sub_mod4 (ua a) z (wt_ua a) hd, I_pow_mod4, chi_one,
      pow_succ, mul_assoc, ← sq, Complex.I_sq]

/-! ### Frames `C_0`, `C_𝓕`, `C_U^{-1}`, `C_{U^⊥} C_U^{-1}` -/

/-- The explicit inverse `C_U^{-1} = H^{⊗m} diag(i^{-q_U}) H^{⊗m}`. -/
noncomputable def CUinv {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) : Matrix (Pt h) (Pt h) ℂ :=
  Fm fun z => (Complex.I ^ qU U z)⁻¹

lemma CU_mul_CUinv {h : ℕ} (U : Submodule (ZMod 2) (Pt h)) : CU U * CUinv U = 1 := by
  have e : (fun z => Complex.I ^ qU U z) * (fun z => (Complex.I ^ qU U z)⁻¹) =
      fun _ => (1 : ℂ) := by
    funext z
    exact mul_inv_cancel₀ (pow_ne_zero _ Complex.I_ne_zero)
  rw [CU_eq_Fm, CUinv, Fm_mul, e, Fm_one]

/-- The zero label has frame `I`. -/
lemma CU_bot {h : ℕ} : CU (⊥ : Submodule (ZMod 2) (Pt h)) = 1 := by
  have e : (fun z : Pt h => Complex.I ^ qU ⊥ z) = fun _ => (1 : ℂ) := by
    funext z
    rw [qU, projAlong_bot, LinearMap.zero_apply, wt_zero, Nat.zero_mod, pow_zero]
  rw [CU_eq_Fm, e, Fm_one]

/-- The full label has frame `C^{⊗m}` (`q_𝓕(x) = wt x mod 4`). -/
lemma CU_top {h : ℕ} : CU (⊤ : Submodule (ZMod 2) (Pt h)) = Cfull := by
  have e : (fun z : Pt h => Complex.I ^ qU ⊤ z) = fun z => Complex.I ^ wt z := by
    funext z
    rw [qU, projAlong_top _ betaC3_nondeg, LinearMap.id_apply, I_pow_mod4]
  rw [CU_eq_Fm, e, Fm_iwt]

/-- `C_{U_a^⊥} C_{U_a}^{-1} = C^{⊗m} X_{u_a}`. -/
lemma frame_ratio {h : ℕ} (a : Addr h) :
    frameC (Vertex.sink (Role.Y a)) * CUinv (labC (Vertex.source (κ := .complex) (Role.X a))) =
      Cfull * Xv (ua a) := by
  show CU _ * CUinv _ = _
  rw [CU_eq_Fm, CUinv, Fm_mul, ← Fm_iwt, ← Fm_chi, Fm_mul]
  congr 1
  funext z
  exact phase_ratio a z

/-! ### Endpoint corrections -/

/-- `Z_u = diag((-1)^{u·x})` on one column. -/
noncomputable def Zd {h : ℕ} (u : Pt h) : Matrix (Pt h) (Pt h) ℂ :=
  Matrix.diagonal fun x => chi (dotC u x)

lemma mul_Xv_apply {h : ℕ} (M : Matrix (Pt h) (Pt h) ℂ) (u x y : Pt h) :
    (M * Xv u) x y = M x (y + u) := by
  rw [Matrix.mul_apply]
  have e : ∀ w : Pt h, M x w * Xv u w y = if w = y + u then M x w else 0 := by
    intro w
    have hiff : y = w + u ↔ w = y + u := by
      constructor
      · intro hy; rw [hy, add_assoc, pt_add_self, add_zero]
      · intro hw; rw [hw, add_assoc, pt_add_self, add_zero]
    simp only [Xv, hiff, mul_ite, mul_one, mul_zero]
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma I_mul_kb : Complex.I * kb = ka := by
  unfold ka kb; linear_combination (-1/2 : ℂ) * Complex.I_sq

lemma I_mul_ka : Complex.I * ka = -kb := by
  unfold ka kb; linear_combination (1/2 : ℂ) * Complex.I_sq

/-- Coordinatewise `i Z C X Z = C` (and the identity off `supp u`). -/
lemma coord_endpoint (b c d : ZMod 2) :
    Complex.I ^ b.val * (chi (b * c) * C2 c (d + b) * chi (b * d)) = C2 c d := by
  rcases zmod2_cases b with rfl | rfl
  · simp only [z2_val_zero, pow_zero, zero_mul, chi_zero, add_zero, one_mul, mul_one]
  · rw [z2_val_one, pow_one, one_mul c, one_mul d]
    rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;>
      simp only [zero_add, z2_one_add_one, chi_zero, chi_one, C2_00, C2_01, C2_10, C2_11,
        one_mul, mul_one, neg_one_mul, mul_neg, neg_neg, I_mul_ka, I_mul_kb]

/-- One column: `i^{27} Z_u C^{⊗m} X_u Z_u = C^{⊗m}` when `wt u = 27`. -/
lemma one_column {h : ℕ} (u : Pt h) (hu : wt u = 27) :
    Complex.I ^ 27 • (Zd u * (Cfull * Xv u) * Zd u) = Cfull := by
  ext x y
  simp only [Zd, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_Xv_apply,
    smul_eq_mul]
  rw [← hu, wt_eq_sum, ← Finset.prod_pow_eq_pow_sum, chi_dotC, chi_dotC]
  simp only [Cfull, Pi.add_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => coord_endpoint (u p) (x p) (y p)

/-! ### The endpoint identities for every `h` -/

/-- C3, trivial routes, every `h` ([OAI26, §3.5, Prop. 8]): the zero label has frame `I` and the full
label has frame `C^{⊗m}`. -/
theorem prop8ZeroFull_gen (h : ℕ) : ∀ w : Role .complex h,
    ((∀ a, w ≠ .X a) → frameC (.source w) = 1) ∧ ((∀ a, w ≠ .Y a) → frameC (.sink w) = Cfull) := by
  intro w
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · have hsrc : labC (Vertex.source (κ := .complex) (h := h) w) = ⊥ := by
      cases w with
      | X a => exact absurd rfl (hw a)
      | Y a => rfl
      | side j ι p => rfl
      | center j ι c => rfl
    show CU _ = 1
    rw [hsrc, CU_bot]
  · have hsnk : labC (Vertex.sink (κ := .complex) (h := h) w) = ⊤ := by
      cases w with
      | Y a => exact absurd rfl (hw a)
      | X a => exact labelSub_labFull (betaC h)
      | side j ι p => exact labelSub_labFull (betaC h)
      | center j ι c => exact labelSub_labFull (betaC h)
    show CU _ = Cfull
    rw [hsnk, CU_top]

/-- C3, every `h` and any number `k` of columns ([OAI26, §3.5, Prop. 8]):
`i^{27k} Z_{a,k} C_{U_a^⊥}^{⊗k} (C_{U_a}^{⊗k})^{-1} Z_{a,k} = C^{⊗mk}` (the hypothesis `1 ≤ k` is
not used). -/
theorem prop8Endpoint_gen (h : ℕ) : ∀ (a : Addr h) (k : ℕ), 1 ≤ k →
    (Complex.I ^ (27 * k)) • (Zk k (ua a) * tpow k (frameC (.sink (.Y a))) *
      (tpow k (frameC (.source (.X a))))⁻¹ * Zk k (ua a)) = tpow k Cfull := by
  intro a k _
  have hinv : (tpow k (frameC (Vertex.source (κ := .complex) (Role.X a))))⁻¹ =
      tpow k (CUinv (labC (Vertex.source (κ := .complex) (Role.X a)))) := by
    apply Matrix.inv_eq_right_inv
    rw [← tpow_mul]
    show tpow k (CU _ * CUinv _) = 1
    rw [CU_mul_CUinv, tpow_one]
  have hZ : Zk k (ua a) = tpow k (Zd (ua a)) := by
    rw [Zd, tpow_diagonal]; rfl
  rw [hinv, hZ, ← tpow_mul, ← tpow_mul, ← tpow_mul, pow_mul, ← tpow_smul,
    Matrix.mul_assoc (Zd (ua a)), frame_ratio a, one_column (ua a) (wt_ua a)]

end EndpointsAux

/-! ### Contract theorems -/

/-- **C3, trivial routes** ([OAI26, §3.5, Prop. 8]), `h = 100`: the zero label has frame `I` and the full
label has frame `C^{⊗m}`. -/
theorem prop8ZeroFull_holds : Prop8ZeroFullStmt := EndpointsAux.prop8ZeroFull_gen 100

/-- **C3** ([OAI26, §3.5, Prop. 8] (endpoint corrections)), `h = 100`, any `k` columns:
`i^{27k} Z_{a,k} C_{U_a^⊥}^{⊗k} (C_{U_a}^{⊗k})^{-1} Z_{a,k} = C^{⊗mk}`. -/
theorem prop8Endpoint_holds : Prop8EndpointStmt := EndpointsAux.prop8Endpoint_gen 100

end SubNLogN.Math.Networks
