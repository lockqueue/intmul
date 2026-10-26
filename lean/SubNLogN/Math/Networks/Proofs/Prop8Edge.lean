import SubNLogN.Math.Networks.PhaseFrames

/-!
# [OAI26] Prop. 8, edge factorization (contract C2)

We prove `Prop8EdgeStmt` (`PhaseFrames.lean`) from the Lemma 6 contracts `Lemma6NestedStmt` and
`Lemma6NondegComplexStmt` (`Labels.lean`), via two generic lemmas valid for every `h`:

* `CU_eq_kernels_mul_CU_of_le`: for subspaces `U ≤ V` of `𝔽₂^{[h]³}`, both nondegenerate for the
  dot product, and an orthonormal list `B` (`IsONB`) of `R = V ⊓ U^⊥`,
  `C_V = (Π_{v∈B} K(v, if wt v % 4 = 1 then 1 else -1)) · C_U`;
* `CU_eq_kernels_mul_CU_of_ge`: for `V ≤ U` (both nondegenerate) and `B` an orthonormal list of
  `U ⊓ V^⊥`, the same with the signs reversed.

## Plan ([OAI26, §3.5, Prop. 8]; Lemma A.10 (`lem:transfer-phase`))

Notation: `m = h³`, `χ_u(z) = (-1)^{u·z}`, `H_{y,z} = χ_y(z)` (unnormalised Hadamard) and
`Had f := 2^{-m} H diag(f) H`, i.e. `(Had f)_{y,x} = 2^{-m} Σ_z χ_{x+y}(z) f(z)`; by definition
`C_U = Had (i^{q_U})` (`CU_eq_hadT`, `rfl`).

1. Characters: `Σ_z χ_u(z) = 2^m [u = 0]` (`sum_chi`); hence `H·H = 2^m I`,
   `Had (f·g) = Had f · Had g`, `Had 1 = I`, `Had` is linear and `Had χ_v = X_v`.
2. Kernels: for `c ∈ 𝔽₂`, `e ≡ 1 (4)`: `i^{[c]e} = a + b(-1)^{[c]}`; `e ≡ 3 (4)`:
   `i^{[c]e} = b + a(-1)^{[c]}`. So `Had (z ↦ i^{[v·z] e}) = K(v, 1)` resp. `K(v, -1)`.
3. Weights: `wt(x+y) + 2 Σ_p [x_p][y_p] = wt x + wt y` and `Σ_p [x_p][y_p] ≡ x·y (mod 2)`, so the
   weight is additive mod 4 on pairwise orthogonal lists; `wt v` is odd when `v·v = 1`.
4. Projections: for `U ≤ V` nondegenerate and `B` an orthonormal list spanning
   `R = V ∩ U^⊥`: `P_V z = P_U z + Σ_{v∈B} (v·z) v` (`y ∈ V` and `z - y ∈ V^⊥` characterise `P_V z`;
   for `n ∈ V` split `n = P_U n + (n - P_U n)` with `n - P_U n ∈ R`).
5. Hence `i^{q_V(z)} = Π_{v∈B} i^{[v·z] wt v} · i^{q_U(z)}` and
   `C_V = Had(Π_v i^{[v·] wt v} · i^{q_U}) = Π_v K(v, ±1) · C_U`.  For `V ≤ U` apply this to
   `(V, U)` and use `i^{3[v·z] wt v} · i^{[v·z] wt v} = 1`.
6. `prop8Edge_of`: case split on `labC e.1 ≤ labC e.2` (otherwise nestedness gives `≥`);
   `epsC` reduces to the signs above.
-/

namespace SubNLogN.Math.Networks

namespace Prop8E

variable {h : ℕ}

/-! ### Scalars in `𝔽₂` -/

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem val_one2 : (1 : ZMod 2).val = 1 := rfl

theorem add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem val_eq_ite (a : ZMod 2) : (if a ≠ 0 then 1 else 0) = a.val := by
  revert a; decide

theorem val_add_aux (a b : ZMod 2) : (a + b).val + 2 * (a.val * b.val) = a.val + b.val := by
  revert a b; decide

theorem val_mul_self (a : ZMod 2) : a.val * a.val = a.val := by
  revert a; decide

theorem sgn_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← neg_one_pow_eq_pow_mod_two]

theorem sgn_add_one (a : ZMod 2) : (-1 : ℂ) ^ (a + 1).val = -(-1 : ℂ) ^ a.val := by
  rw [sgn_add, val_one2, pow_one, mul_neg_one]

theorem I_pow_mod4 (n : ℕ) : Complex.I ^ (n % 4) = Complex.I ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

theorem pow_list_sum_map {α : Type*} (a : ℂ) (L : List α) (g : α → ℕ) :
    a ^ (L.map g).sum = (L.map fun x => a ^ g x).prod := by
  induction L with
  | nil => simp
  | cons x L ih => rw [List.map_cons, List.sum_cons, pow_add, ih, List.map_cons, List.prod_cons]

/-! ### The dot product -/

theorem betaC3_apply (x y : Pt h) : betaC3 h x y = dotC x y := by
  simp [betaC3, Matrix.toBilin'_apply, Matrix.one_apply, dotC]

theorem dotC_comm (x y : Pt h) : dotC x y = dotC y x := by
  simp only [dotC, mul_comm]

theorem dotC_add_left (x y z : Pt h) : dotC (x + y) z = dotC x z + dotC y z := by
  simp only [dotC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dotC_add_right (x y z : Pt h) : dotC x (y + z) = dotC x y + dotC x z := by
  simp only [dotC, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dotC_sub_left (x y z : Pt h) : dotC (x - y) z = dotC x z - dotC y z := by
  simp only [dotC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dotC_sub_right (x y z : Pt h) : dotC x (y - z) = dotC x y - dotC x z := by
  simp only [dotC, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dotC_smul_left (c : ZMod 2) (x y : Pt h) : dotC (c • x) y = c * dotC x y := by
  simp only [dotC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem dotC_smul_right (c : ZMod 2) (x y : Pt h) : dotC x (c • y) = c * dotC x y := by
  simp only [dotC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem dotC_zero_left (y : Pt h) : dotC 0 y = 0 := by
  simp [dotC]

theorem dotC_list_sum_right (x : Pt h) (L : List (Pt h)) :
    dotC x L.sum = (L.map (dotC x)).sum := by
  induction L with
  | nil => simp [dotC]
  | cons a L ih => rw [List.sum_cons, dotC_add_right, ih, List.map_cons, List.sum_cons]

theorem dotC_single (u : Pt h) (p : Cube h) : dotC u (Pi.single p 1) = u p := by
  simp [dotC, Pi.single_apply]

/-! ### `𝔽₂^m` has exponent 2 -/

theorem Pt_add_self (x : Pt h) : x + x = 0 := funext fun p => add_self_zmod2 (x p)

theorem Pt_add_eq_zero_iff {x y : Pt h} : x + y = 0 ↔ x = y := by
  constructor
  · intro hxy
    calc x = x + y + y := by rw [add_assoc, Pt_add_self, add_zero]
      _ = y := by rw [hxy, zero_add]
  · rintro rfl
    exact Pt_add_self x

/-! ### Characters -/

theorem card_Pt : Fintype.card (Pt h) = 2 ^ (h ^ 3) := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  ring

theorem sum_chi (u : Pt h) :
    ∑ z : Pt h, (-1 : ℂ) ^ (dotC u z).val = if u = 0 then (2 : ℂ) ^ (h ^ 3) else 0 := by
  split_ifs with hu
  · subst hu
    have h1 : ∀ z : Pt h, (-1 : ℂ) ^ (dotC 0 z).val = 1 := fun z => by
      rw [dotC_zero_left, ZMod.val_zero, pow_zero]
    rw [Finset.sum_congr rfl (fun z _ => h1 z), Finset.sum_const, Finset.card_univ, card_Pt,
      nsmul_eq_mul, mul_one]
    norm_num
  · obtain ⟨p, hp⟩ := Function.ne_iff.1 hu
    have hp1 : u p = 1 := (zmod2_cases (u p)).resolve_left hp
    have h1 : ∑ z : Pt h, (-1 : ℂ) ^ (dotC u (z + Pi.single p 1)).val =
        ∑ z : Pt h, (-1 : ℂ) ^ (dotC u z).val :=
      Fintype.sum_equiv (Equiv.addRight (Pi.single p 1 : Pt h)) _ _ (fun z => rfl)
    have h2 : ∀ z : Pt h,
        (-1 : ℂ) ^ (dotC u (z + Pi.single p 1)).val = -(-1 : ℂ) ^ (dotC u z).val := by
      intro z
      rw [dotC_add_right, dotC_single, hp1, sgn_add_one]
    simp only [h2, Finset.sum_neg_distrib] at h1
    linear_combination (-1 / 2 : ℂ) * h1

theorem chi_mul (u w z : Pt h) :
    (-1 : ℂ) ^ (dotC u z).val * (-1 : ℂ) ^ (dotC w z).val = (-1 : ℂ) ^ (dotC (u + w) z).val := by
  rw [dotC_add_left, sgn_add]

/-! ### The Hadamard transform of a diagonal -/

/-- Unnormalised Walsh–Hadamard matrix `H_{y,z} = (-1)^{y·z}`. -/
noncomputable def Hm (h : ℕ) : Matrix (Pt h) (Pt h) ℂ := fun y z => (-1 : ℂ) ^ (dotC y z).val

/-- `Had f = 2^{-m} H diag(f) H`, entrywise `(Had f)_{y,x} = 2^{-m} Σ_z (-1)^{(x+y)·z} f(z)`. -/
noncomputable def hadT (f : Pt h → ℂ) : Matrix (Pt h) (Pt h) ℂ :=
  fun y x => ((2 : ℂ) ^ (h ^ 3))⁻¹ * ∑ z : Pt h, (-1 : ℂ) ^ (dotC (x + y) z).val * f z

/-- The phase frame is the Hadamard transform of the phase `i^{q_U}` (definitional). -/
theorem CU_eq_hadT (U : Submodule (ZMod 2) (Pt h)) :
    CU U = hadT (fun z => Complex.I ^ qU U z) := rfl

theorem twoPowM_ne_zero : (2 : ℂ) ^ (h ^ 3) ≠ 0 := pow_ne_zero _ two_ne_zero

theorem Hm_mul_Hm : Hm h * Hm h = (2 : ℂ) ^ (h ^ 3) • (1 : Matrix (Pt h) (Pt h) ℂ) := by
  ext y x
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hz : ∀ z, Hm h y z * Hm h z x = (-1 : ℂ) ^ (dotC (y + x) z).val := by
    intro z
    simp only [Hm]
    rw [dotC_comm z x, chi_mul]
  rw [Finset.sum_congr rfl (fun z _ => hz z), sum_chi]
  by_cases hyx : y = x
  · rw [if_pos (Pt_add_eq_zero_iff.2 hyx), if_pos hyx, mul_one]
  · rw [if_neg (mt Pt_add_eq_zero_iff.1 hyx), if_neg hyx, mul_zero]

theorem Hm_mul_Hm_mul (X : Matrix (Pt h) (Pt h) ℂ) :
    Hm h * (Hm h * X) = (2 : ℂ) ^ (h ^ 3) • X := by
  rw [← Matrix.mul_assoc, Hm_mul_Hm, Matrix.smul_mul, Matrix.one_mul]

theorem hadT_eq (f : Pt h → ℂ) :
    hadT f = ((2 : ℂ) ^ (h ^ 3))⁻¹ • (Hm h * Matrix.diagonal f * Hm h) := by
  ext y x
  rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  simp only [Matrix.mul_diagonal, Hm, hadT]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [dotC_comm z x, ← chi_mul x y z]
  ring

theorem hadT_mul (f g : Pt h → ℂ) : hadT (f * g) = hadT f * hadT g := by
  have key : Hm h * Matrix.diagonal f * Hm h * (Hm h * Matrix.diagonal g * Hm h) =
      (2 : ℂ) ^ (h ^ 3) • (Hm h * Matrix.diagonal (f * g) * Hm h) := by
    simp only [Matrix.mul_assoc, Hm_mul_Hm_mul, Matrix.mul_smul]
    rw [← Matrix.mul_assoc (Matrix.diagonal f), Matrix.diagonal_mul_diagonal, Pi.mul_def]
  rw [hadT_eq f, hadT_eq g, hadT_eq (f * g), Matrix.smul_mul, Matrix.mul_smul, smul_smul, key,
    smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ twoPowM_ne_zero, mul_one]

theorem hadT_one : hadT (1 : Pt h → ℂ) = 1 := by
  rw [hadT_eq, Matrix.diagonal_one', Matrix.mul_one, Hm_mul_Hm, smul_smul,
    inv_mul_cancel₀ twoPowM_ne_zero, one_smul]

theorem hadT_add (f g : Pt h → ℂ) : hadT (f + g) = hadT f + hadT g := by
  ext y x
  simp only [hadT, Matrix.add_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hadT_smul (c : ℂ) (f : Pt h → ℂ) : hadT (c • f) = c • hadT f := by
  ext y x
  simp only [hadT, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

theorem hadT_char (v : Pt h) : hadT (fun z => (-1 : ℂ) ^ (dotC v z).val) = Xv v := by
  ext y x
  simp only [hadT, Xv, chi_mul, sum_chi]
  have hiff : x + y + v = 0 ↔ x = y + v := by
    rw [add_assoc]; exact Pt_add_eq_zero_iff
  by_cases hxy : x = y + v
  · rw [if_pos (hiff.2 hxy), if_pos hxy, inv_mul_cancel₀ twoPowM_ne_zero]
  · rw [if_neg (mt hiff.1 hxy), if_neg hxy, mul_zero]

theorem hadT_list_prod {α : Type*} (L : List α) (φ : α → Pt h → ℂ) :
    hadT (L.map φ).prod = (L.map fun a => hadT (φ a)).prod := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil]; exact hadT_one
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, hadT_mul, ih, List.map_cons, List.prod_cons]

/-! ### Translation kernels -/

theorem I_pow_val_mul_of_one (c : ZMod 2) {e : ℕ} (he : e % 4 = 1) :
    Complex.I ^ (c.val * e) = ka + kb * (-1 : ℂ) ^ c.val := by
  rcases zmod2_cases c with rfl | rfl
  · rw [ZMod.val_zero, zero_mul, pow_zero, pow_zero, ka, kb]; ring
  · rw [val_one2, one_mul, ← I_pow_mod4, he, pow_one, pow_one, ka, kb]; ring

theorem I_pow_val_mul_of_three (c : ZMod 2) {e : ℕ} (he : e % 4 = 3) :
    Complex.I ^ (c.val * e) = kb + ka * (-1 : ℂ) ^ c.val := by
  rcases zmod2_cases c with rfl | rfl
  · rw [ZMod.val_zero, zero_mul, pow_zero, pow_zero, ka, kb]; ring
  · rw [val_one2, one_mul, ← I_pow_mod4, he, pow_one, ka, kb]
    linear_combination Complex.I * Complex.I_sq

/-- The phase `z ↦ i^{[v·z] e}`. -/
noncomputable def kerFun (v : Pt h) (e : ℕ) : Pt h → ℂ :=
  fun z => Complex.I ^ ((dotC v z).val * e)

theorem hadT_kerFun_of_one (v : Pt h) {e : ℕ} (he : e % 4 = 1) :
    hadT (kerFun v e) = Kv v 1 := by
  have hf : kerFun v e = ka • (1 : Pt h → ℂ) + kb • (fun z => (-1 : ℂ) ^ (dotC v z).val) := by
    funext z
    simp only [kerFun, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact I_pow_val_mul_of_one _ he
  rw [hf, hadT_add, hadT_smul, hadT_smul, hadT_one, hadT_char, Kv, if_pos rfl]

theorem hadT_kerFun_of_three (v : Pt h) {e : ℕ} (he : e % 4 = 3) :
    hadT (kerFun v e) = Kv v (-1) := by
  have hf : kerFun v e = kb • (1 : Pt h → ℂ) + ka • (fun z => (-1 : ℂ) ^ (dotC v z).val) := by
    funext z
    simp only [kerFun, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact I_pow_val_mul_of_three _ he
  rw [hf, hadT_add, hadT_smul, hadT_smul, hadT_one, hadT_char, Kv,
    if_neg (show (-1 : ℤ) ≠ 1 by norm_num)]

theorem kerFun_mul_three (v : Pt h) (e : ℕ) (z : Pt h) :
    kerFun v (3 * e) z * kerFun v e z = 1 := by
  simp only [kerFun, ← pow_add]
  rw [show (dotC v z).val * (3 * e) + (dotC v z).val * e = 4 * ((dotC v z).val * e) by ring,
    pow_mul, Complex.I_pow_four, one_pow]

/-! ### Hamming weight modulo 4 -/

theorem wt_eq_sum (x : Pt h) : wt x = ∑ p, (x p).val := by
  unfold wt
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun p _ => val_eq_ite (x p)

theorem wt_zero : wt (0 : Pt h) = 0 := by
  simp [wt]

theorem wt_add (x y : Pt h) : wt (x + y) + 2 * ∑ p, (x p).val * (y p).val = wt x + wt y := by
  simp only [wt_eq_sum, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => val_add_aux _ _

theorem cast_sum_val_mul (x y : Pt h) :
    ((∑ p, (x p).val * (y p).val : ℕ) : ZMod 2) = dotC x y := by
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val, dotC]

theorem wt_add_mod4 {x y : Pt h} (hxy : dotC x y = 0) :
    wt (x + y) % 4 = (wt x + wt y) % 4 := by
  have h1 := wt_add x y
  have h2 : 2 ∣ ∑ p, (x p).val * (y p).val := by
    rw [← ZMod.natCast_eq_zero_iff, cast_sum_val_mul, hxy]
  obtain ⟨k, hk⟩ := h2
  omega

theorem wt_list_sum_mod4 (L : List (Pt h)) (hL : L.Pairwise fun a b => dotC a b = 0) :
    wt L.sum % 4 = (L.map wt).sum % 4 := by
  induction L with
  | nil => simp [wt_zero]
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    have h0 : dotC a L.sum = 0 := by
      rw [dotC_list_sum_right]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      exact hL.1 b hb
    rw [List.sum_cons, List.map_cons, List.sum_cons, wt_add_mod4 h0, Nat.add_mod, ih hL.2,
      ← Nat.add_mod]

theorem wt_smul (c : ZMod 2) (v : Pt h) : wt (c • v) = c.val * wt v := by
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, wt_zero, ZMod.val_zero, zero_mul]
  · rw [one_smul, val_one2, one_mul]

theorem wt_odd_of_dotC_self {v : Pt h} (hv : dotC v v = 1) : wt v % 2 = 1 := by
  have h1 : wt v = ∑ p, (v p).val * (v p).val := by
    rw [wt_eq_sum]
    exact Finset.sum_congr rfl fun p _ => (val_mul_self (v p)).symm
  have h2 : ((wt v : ℕ) : ZMod 2) = 1 := by
    rw [h1, cast_sum_val_mul, hv]
  rw [← ZMod.val_natCast, h2]
  rfl

theorem hadT_kerFun_fwd {v : Pt h} (hv : dotC v v = 1) :
    hadT (kerFun v (wt v)) = Kv v (if wt v % 4 = 1 then 1 else -1) := by
  have hodd := wt_odd_of_dotC_self hv
  split_ifs with h1
  · exact hadT_kerFun_of_one v h1
  · exact hadT_kerFun_of_three v (by omega)

theorem hadT_kerFun_rev {v : Pt h} (hv : dotC v v = 1) :
    hadT (kerFun v (3 * wt v)) = Kv v (if wt v % 4 = 1 then -1 else 1) := by
  have hodd := wt_odd_of_dotC_self hv
  split_ifs with h1
  · exact hadT_kerFun_of_three v (by omega)
  · exact hadT_kerFun_of_one v (by omega)

/-! ### Projections along the orthogonal complement -/

theorem mem_orth_iff {N : Submodule (ZMod 2) (Pt h)} {m : Pt h} :
    m ∈ (betaC3 h).orthogonal N ↔ ∀ n ∈ N, dotC n m = 0 := by
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, betaC3_apply]

theorem projAlong_eq {U : Submodule (ZMod 2) (Pt h)}
    (hU : IsCompl U ((betaC3 h).orthogonal U)) :
    projAlong (betaC3 h) U = U.projection _ hU := by
  rw [projAlong, dif_pos hU]

theorem proj_eq_of {p q : Submodule (ZMod 2) (Pt h)} (hpq : IsCompl p q) {x y : Pt h}
    (hy : y ∈ p) (hxy : x - y ∈ q) : p.projection q hpq x = y := by
  have h2 := Submodule.projection_apply_of_mem_right hpq hxy
  rw [map_sub, Submodule.projection_apply_of_mem_left hpq hy] at h2
  exact sub_eq_zero.mp h2

theorem dotC_expand_mem {B : List (Pt h)} (hn : ∀ v ∈ B, dotC v v = 1)
    (hp : B.Pairwise fun u v => dotC u v = 0) (z : Pt h) {r : Pt h} (hr : r ∈ B) :
    dotC r z = (B.map fun v => dotC v z * dotC r v).sum := by
  induction B with
  | nil => simp at hr
  | cons a B ih =>
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hr with hra | hrB
    · rw [hra]
      have h0 : (B.map fun v => dotC v z * dotC a v).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
        rw [hp.1 b hb, mul_zero]
      rw [h0, hn a List.mem_cons_self, mul_one, add_zero]
    · have h1 : dotC r a = 0 := by
        rw [dotC_comm]; exact hp.1 r hrB
      rw [h1, mul_zero, zero_add]
      exact ih (fun v hv => hn v (List.mem_cons_of_mem _ hv)) hp.2 hrB

theorem dotC_expand_span {B : List (Pt h)} (hn : ∀ v ∈ B, dotC v v = 1)
    (hp : B.Pairwise fun u v => dotC u v = 0) (z : Pt h) {r : Pt h}
    (hr : r ∈ Submodule.span (ZMod 2) {v | v ∈ B}) :
    dotC r z = (B.map fun v => dotC v z * dotC r v).sum := by
  induction hr using Submodule.span_induction with
  | mem x hx => exact dotC_expand_mem hn hp z hx
  | zero =>
    rw [dotC_zero_left]
    symm
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
    rw [dotC_zero_left, mul_zero]
  | add x y _ _ hx hy =>
    rw [dotC_add_left, hx, hy, ← List.sum_map_add]
    apply congrArg
    apply List.map_congr_left
    intro v _
    rw [dotC_add_left, mul_add]
  | smul a x _ hx =>
    rw [dotC_smul_left, hx, ← List.sum_map_mul_left]
    apply congrArg
    apply List.map_congr_left
    intro v _
    rw [dotC_smul_left]
    ring

/-- For `U ≤ V` nondegenerate and `B` an orthonormal list spanning `V ⊓ U^⊥`:
`P_V z = P_U z + Σ_{v∈B} (v·z) v`. -/
theorem proj_formula {U V : Submodule (ZMod 2) (Pt h)} (hUV : U ≤ V)
    (hU : IsCompl U ((betaC3 h).orthogonal U)) (hV : IsCompl V ((betaC3 h).orthogonal V))
    {B : List (Pt h)} (hB : IsONB (V ⊓ (betaC3 h).orthogonal U) B) (z : Pt h) :
    V.projection _ hV z = U.projection _ hU z + (B.map fun v => dotC v z • v).sum := by
  obtain ⟨hn, hp, hspan⟩ := hB
  have hBR : ∀ v ∈ B, v ∈ V ⊓ (betaC3 h).orthogonal U := fun v hv => by
    rw [← hspan]; exact Submodule.subset_span hv
  have hSR : (B.map fun v => dotC v z • v).sum ∈ V ⊓ (betaC3 h).orthogonal U := by
    apply list_sum_mem
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    exact Submodule.smul_mem _ _ (hBR v hv)
  have hPUz : U.projection _ hU z ∈ U := Submodule.projection_apply_mem _ _
  apply proj_eq_of
  · exact add_mem (hUV hPUz) (Submodule.mem_inf.1 hSR).1
  · rw [mem_orth_iff]
    intro n hnV
    have hPUn : U.projection _ hU n ∈ U := Submodule.projection_apply_mem _ _
    have hr : n - U.projection _ hU n ∈ V ⊓ (betaC3 h).orthogonal U :=
      Submodule.mem_inf.2 ⟨sub_mem hnV (hUV hPUn), Submodule.sub_projection_mem _ _⟩
    have f1 := (mem_orth_iff.1 (Submodule.sub_projection_mem hU z)) _ hPUn
    have f2 := (mem_orth_iff.1 (Submodule.mem_inf.1 hSR).2) _ hPUn
    have f3 := (mem_orth_iff.1 (Submodule.mem_inf.1 hr).2) _ hPUz
    have f4 : dotC (n - U.projection _ hU n) (B.map fun v => dotC v z • v).sum =
        dotC (n - U.projection _ hU n) z := by
      have hrspan : n - U.projection _ hU n ∈ Submodule.span (ZMod 2) {v | v ∈ B} := by
        rw [hspan]; exact hr
      rw [dotC_expand_span hn hp z hrspan, dotC_list_sum_right, List.map_map]
      apply congrArg
      apply List.map_congr_left
      intro v _
      simp only [Function.comp_apply, dotC_smul_right]
    rw [dotC_comm] at f3
    simp only [dotC_sub_left, dotC_sub_right, dotC_add_right] at f1 f3 f4 ⊢
    linear_combination f1 - f2 - f3 - f4

/-! ### The phase identity -/

/-- `i^{q_V(z)} = Π_{v∈B} i^{[v·z] wt v} · i^{q_U(z)}` for `U ≤ V` nondegenerate and `B` an
orthonormal list spanning `V ⊓ U^⊥`. -/
theorem I_pow_qU_of_le {U V : Submodule (ZMod 2) (Pt h)} (hUV : U ≤ V)
    (hU : IsCompl U ((betaC3 h).orthogonal U)) (hV : IsCompl V ((betaC3 h).orthogonal V))
    {B : List (Pt h)} (hB : IsONB (V ⊓ (betaC3 h).orthogonal U) B) (z : Pt h) :
    Complex.I ^ qU V z = (B.map fun v => kerFun v (wt v) z).prod * Complex.I ^ qU U z := by
  have hPU : U.projection _ hU z ∈ U := Submodule.projection_apply_mem _ _
  have hL : (U.projection _ hU z :: B.map fun v => dotC v z • v).Pairwise
      (fun a b => dotC a b = 0) := by
    rw [List.pairwise_cons, List.pairwise_map]
    refine ⟨?_, hB.2.1.imp fun hab => ?_⟩
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      have hvR : v ∈ V ⊓ (betaC3 h).orthogonal U := by
        rw [← hB.2.2]; exact Submodule.subset_span hv
      simp only [dotC_smul_right, (mem_orth_iff.1 (Submodule.mem_inf.1 hvR).2) _ hPU, mul_zero]
    · simp only [dotC_smul_left, dotC_smul_right, hab, mul_zero]
  have hw := wt_list_sum_mod4 _ hL
  rw [List.sum_cons, ← proj_formula hUV hU hV hB z, List.map_cons, List.sum_cons,
    List.map_map] at hw
  simp only [qU, projAlong_eq hU, projAlong_eq hV]
  rw [hw, I_pow_mod4, I_pow_mod4, pow_add, pow_list_sum_map, mul_comm]
  congr 1
  apply congrArg
  apply List.map_congr_left
  intro v _
  simp only [Function.comp_apply, wt_smul, kerFun]

/-- Decreasing version: for `V ≤ U` nondegenerate and `B` an orthonormal list spanning
`U ⊓ V^⊥`, `i^{q_V(z)} = Π_{v∈B} i^{3 [v·z] wt v} · i^{q_U(z)}`. -/
theorem I_pow_qU_of_ge {U V : Submodule (ZMod 2) (Pt h)} (hVU : V ≤ U)
    (hU : IsCompl U ((betaC3 h).orthogonal U)) (hV : IsCompl V ((betaC3 h).orthogonal V))
    {B : List (Pt h)} (hB : IsONB (U ⊓ (betaC3 h).orthogonal V) B) (z : Pt h) :
    Complex.I ^ qU V z = (B.map fun v => kerFun v (3 * wt v) z).prod * Complex.I ^ qU U z := by
  rw [I_pow_qU_of_le hVU hV hU hB z, ← mul_assoc, ← List.prod_map_mul, List.prod_eq_one,
    one_mul]
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
  exact kerFun_mul_three v _ z

end Prop8E

open Prop8E

/-- Generic [OAI26, §3.5, Prop. 8] edge identity, increasing edge. For subspaces `U ≤ V` of
`𝔽₂^{[h]³}`, both nondegenerate for the dot product, and an orthonormal list `B` spanning
`V ⊓ U^⊥` (the residual `residual (betaC3 h) U V`), the phase frames satisfy
`C_V = (Π_{v∈B} K(v, ε_v)) · C_U` with `ε_v = 1` if `wt v ≡ 1 (mod 4)` and `ε_v = -1` otherwise. -/
theorem CU_eq_kernels_mul_CU_of_le {h : ℕ} {U V : Submodule (ZMod 2) (Pt h)} (hUV : U ≤ V)
    (hU : IsCompl U ((betaC3 h).orthogonal U)) (hV : IsCompl V ((betaC3 h).orthogonal V))
    {B : List (Pt h)} (hB : IsONB (V ⊓ (betaC3 h).orthogonal U) B) :
    CU V = (B.map fun v => Kv v (if wt v % 4 = 1 then 1 else -1)).prod * CU U := by
  have hfun : (fun z => Complex.I ^ qU V z) =
      (B.map fun v => kerFun v (wt v)).prod * (fun z => Complex.I ^ qU U z) := by
    funext z
    rw [Pi.mul_apply, Pi.list_prod_apply, List.map_map]
    exact I_pow_qU_of_le hUV hU hV hB z
  rw [CU_eq_hadT V, CU_eq_hadT U, hfun, hadT_mul, hadT_list_prod]
  congr 1
  apply congrArg
  apply List.map_congr_left
  intro v hv
  exact hadT_kerFun_fwd (hB.1 v hv)

/-- Generic [OAI26] Prop. 8 edge identity, decreasing edge. For subspaces `V ≤ U` of
`𝔽₂^{[h]³}`, both nondegenerate for the dot product, and an orthonormal list `B` spanning
`U ⊓ V^⊥`, `C_V = (Π_{v∈B} K(v, ε_v)) · C_U` with `ε_v = -1` if `wt v ≡ 1 (mod 4)` and `ε_v = 1`
otherwise. -/
theorem CU_eq_kernels_mul_CU_of_ge {h : ℕ} {U V : Submodule (ZMod 2) (Pt h)} (hVU : V ≤ U)
    (hU : IsCompl U ((betaC3 h).orthogonal U)) (hV : IsCompl V ((betaC3 h).orthogonal V))
    {B : List (Pt h)} (hB : IsONB (U ⊓ (betaC3 h).orthogonal V) B) :
    CU V = (B.map fun v => Kv v (if wt v % 4 = 1 then -1 else 1)).prod * CU U := by
  have hfun : (fun z => Complex.I ^ qU V z) =
      (B.map fun v => kerFun v (3 * wt v)).prod * (fun z => Complex.I ^ qU U z) := by
    funext z
    rw [Pi.mul_apply, Pi.list_prod_apply, List.map_map]
    exact I_pow_qU_of_ge hVU hU hV hB z
  rw [CU_eq_hadT V, CU_eq_hadT U, hfun, hadT_mul, hadT_list_prod]
  congr 1
  apply congrArg
  apply List.map_congr_left
  intro v hv
  exact hadT_kerFun_rev (hB.1 v hv)

/-- [OAI26] Prop. 8, edge factorization (contract C2), at `h = 100`, from the Lemma 6 contracts:
every edge label pair is comparable (`Lemma6NestedStmt`) and every complex vertex label is
nondegenerate (`Lemma6NondegComplexStmt`). Then for every edge and every orthonormal basis `B` of
its residual, `frameC head = (Π_{v∈B} K(v, epsC e v)) · frameC tail`. -/
theorem prop8Edge_of (hnest : Lemma6NestedStmt) (hU : Lemma6NondegComplexStmt) :
    Prop8EdgeStmt := by
  intro w e he B hB
  show CU (labC e.2) = _ * CU (labC e.1)
  by_cases hle : labC e.1 ≤ labC e.2
  · have hR : residC e = labC e.2 ⊓ (betaC3 100).orthogonal (labC e.1) := by
      simp only [residC, residual, if_pos hle]
    rw [hR] at hB
    have hmap : (B.map fun v => Kv v (epsC e v)) =
        B.map fun v => Kv v (if wt v % 4 = 1 then 1 else -1) := by
      apply List.map_congr_left
      intro v _
      simp only [epsC, if_pos hle, one_mul]
    rw [hmap]
    exact CU_eq_kernels_mul_CU_of_le hle (hU e.1) (hU e.2) hB
  · have hge : labC e.2 ≤ labC e.1 := (hnest.2 w e he).resolve_left hle
    have hR : residC e = labC e.1 ⊓ (betaC3 100).orthogonal (labC e.2) := by
      simp only [residC, residual, if_neg hle]
    rw [hR] at hB
    have hmap : (B.map fun v => Kv v (epsC e v)) =
        B.map fun v => Kv v (if wt v % 4 = 1 then -1 else 1) := by
      apply List.map_congr_left
      intro v _
      simp only [epsC, if_neg hle]
      split_ifs <;> norm_num
    rw [hmap]
    exact CU_eq_kernels_mul_CU_of_ge hge (hU e.1) (hU e.2) hB

end SubNLogN.Math.Networks
