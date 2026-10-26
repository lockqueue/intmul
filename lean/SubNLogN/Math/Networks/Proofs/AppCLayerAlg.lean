import SubNLogN.Math.Networks.AppCLayer

/-!
# Lemma A.10 (`lem:transfer-phase`) and Proposition A.11 (`prop:prop14-param`) algebra contracts of `AppCLayer.lean`

Proofs of `TranslationConjStmt`, `BinaryRowAdditionsStmt`, `H0TensorIdentityStmt` and
`Prop71FunctionalStmt` (statements in `SubNLogN/Math/Networks/AppCLayer.lean`), with no
hypotheses.

Paper: Lemma A.10 (`lem:transfer-phase`), Appendix A.5 (`sec:transfer-frames`, `H₀ = bSCS`, `C⁻¹ = −iZCZ`, `b² = −i/2`),
eq. (`eq:oai-h0`) (eq. (18) of [OAI26, §5.1]), and Proposition A.11 (`prop:prop14-param`).

## Proof plan
* `TranslationConjStmt`. From `M * M' = 1` get `M' * M = 1` (`mul_eq_one_comm`), hence
  `x = M y ↔ y = M' x`. Then `(P_M X_v P_{M'}) x y = Σ_z Σ_w [x = Mw][z = w+v][z = M'y]`
  `= [M'x + v = M'y] = [y = x + Mv]`.
* `BinaryRowAdditionsStmt`. Gauss–Jordan elimination over `𝔽₂`, column by column. Let `A = P M`
  (`P` a product of row additions, so `det A = det M` is a unit) have its first `k` columns equal
  to those of `1`. Since `A⁻¹ A = 1` and the first `k` columns of `A⁻¹` are also those of `1`,
  some row `r ≥ k` has `A r k = 1` (`exists_pivot`). One addition `row_k += row_r` (only if
  `A k k = 0`) makes the pivot `1`; then the additions `row_i += row_k` for the rows `i ≠ k` with
  `A i k = 1` (closed formula `prodL_col_mul_apply`) clear column `k` without disturbing the first
  `k` columns. This is at most `n + 1` additions per column, so `P M = 1` with
  `|P| ≤ n(n+1) ≤ n(n−1) + 3n`; as `rowAdd i j` is an involution for `i ≠ j`, `M` is the product
  of the reversed list.
* `H0TensorIdentityStmt`. Termwise: for all `e e'`,
  `2^{-D} (-1)^{|e ∧ e'|} = b^D i^{|e|} (∏_j C(e_j, e'_j)) i^{|e'|}`; both sides are products over
  `j` of the `2 × 2` identity `H₀ = b S C S` (`h0_entry`), and `bD D = b^D` since `b² = −i/2`.
* `Prop71FunctionalStmt`. The argument of the truncation equals `layerH ρ z` for every `z`
  (the disk-grid hypothesis is not even needed): at address `x`, with `sel x = (x_{j,ρ})_j` and
  `x = setSelBits ρ x (sel x)`, the hypothesis on `Csch` gives `C^{⊗D}` of the fibre
  `e ↦ i^{|e|} z(setSelBits ρ x e)`, and the tensor identity turns `b^D 𝒮_D C^{⊗D} 𝒮_D` into
  `H₀^{⊗D}`, which is `layerH ρ z x` (the count `selSignCount ρ x e` is the count of `H0D` at
  `sel x`).
-/

namespace SubNLogN.Math.Networks

open SubNLogN.Math.Walsh

/-! ## Eq. (`eq:oai-h0`) ([OAI26, §5.1, (18)]): `H₀^{⊗D} = b^D 𝒮_D C^{⊗D} 𝒮_D` -/

namespace AppCLayerAlg

/-- `b² = −i/2`. -/
theorem kb_sq : kb ^ 2 = -Complex.I / 2 := by
  unfold kb
  linear_combination (1 / 4 : ℂ) * Complex.I_sq

/-- `bD D = b^D` (since `b² = −i/2` and `D = 2⌊D/2⌋ + D mod 2`). -/
theorem bD_eq_kb_pow (D : ℕ) : bD D = kb ^ D := by
  unfold bD
  rw [← kb_sq, ← pow_mul, ← pow_add, Nat.div_add_mod D 2]

/-- The `2 × 2` identity `H₀ = b S C S`, entrywise: `b i^{u} C(u,v) i^{v} = ½ (−1)^{uv}`. -/
theorem h0_entry (u v : Bool) :
    kb * ((if u = true then Complex.I else 1) * ((if u = v then ka else kb) *
      (if v = true then Complex.I else 1))) =
    (2 : ℂ)⁻¹ * (if u = true ∧ v = true then -1 else 1) := by
  cases u <;> cases v <;> simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
    and_false, and_true, mul_one, one_mul] <;> simp only [ka, kb]
  · linear_combination (-1 / 4 : ℂ) * Complex.I_sq
  · linear_combination (Complex.I / 4 - 1 / 2) * Complex.I_sq
  · linear_combination (Complex.I / 4 - 1 / 2) * Complex.I_sq
  · linear_combination (-(Complex.I ^ 2 - 2) / 4) * Complex.I_sq

/-- `a^{|{j | p j}|} = ∏_j (if p j then a else 1)`. -/
theorem pow_card_filter_eq_prod {ι : Type*} [Fintype ι] (a : ℂ) (p : ι → Prop)
    [DecidablePred p] :
    a ^ (Finset.univ.filter p).card = ∏ j, if p j then a else 1 := by
  rw [Finset.prod_ite]
  simp

end AppCLayerAlg

open AppCLayerAlg

/-- **Eq. (18) of [OAI26]** (`H0TensorIdentityStmt`): `H₀^{⊗D} = b^D 𝒮_D C^{⊗D} 𝒮_D` on
functions of `D` selected bits, for every `D`. -/
theorem h0TensorIdentity_holds : H0TensorIdentityStmt := by
  intro D z
  funext e
  simp only [H0D, SD, CD, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  have key : ((2 : ℂ) ^ D)⁻¹ *
      (-1 : ℂ) ^ (Finset.univ.filter fun j => e j = true ∧ e' j = true).card =
      bD D * (Complex.I ^ (Finset.univ.filter fun j => e j = true).card *
        ((∏ j, (if e j = e' j then ka else kb)) *
          Complex.I ^ (Finset.univ.filter fun j => e' j = true).card)) := by
    have h2 : ((2 : ℂ) ^ D)⁻¹ = ∏ _j : Fin D, (2 : ℂ)⁻¹ := by rw [Fin.prod_const, inv_pow]
    have hb : kb ^ D = ∏ _j : Fin D, kb := by rw [Fin.prod_const]
    rw [bD_eq_kb_pow, pow_card_filter_eq_prod (-1 : ℂ), pow_card_filter_eq_prod Complex.I,
      pow_card_filter_eq_prod Complex.I, h2, hb]
    simp only [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (h0_entry (e j) (e' j)).symm
  calc ((2 : ℂ) ^ D)⁻¹ *
        ((-1 : ℂ) ^ (Finset.univ.filter fun j => e j = true ∧ e' j = true).card * z e')
      = (((2 : ℂ) ^ D)⁻¹ *
          (-1 : ℂ) ^ (Finset.univ.filter fun j => e j = true ∧ e' j = true).card) * z e' := by
        ring
    _ = _ := by rw [key]; ring

/-! ## Proposition A.11, value level -/

namespace AppCLayerAlg

/-- Bit `ρ` of chunk `j` of `setSelBits ρ x e` is `e j`. -/
theorem setSelBits_sel {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) (e : Fin D → Bool)
    (j : Fin D) : (setSelBits ρ x e).2.1 j ρ = e j := by
  simp [setSelBits]

/-- Writing back the selected bits of `x` gives `x`. -/
theorem setSelBits_self {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) :
    setSelBits ρ x (fun j => x.2.1 j ρ) = x := by
  rcases x with ⟨a, c, s⟩
  simp [setSelBits]

end AppCLayerAlg

/-- **Proposition A.11, value level** (`Prop71FunctionalStmt`): if `Csch` evaluates `C^{⊗D}` exactly on
the selected bits, then `Q_P ∘ (b^D 𝒮_D Csch 𝒮_D)` satisfies `LayerSpec`. In fact the function
inside `Q_P` equals `layerH ρ z` for every array `z` (the disk-grid hypothesis is unused). -/
theorem prop71Functional_holds : Prop71FunctionalStmt := by
  intro P r A K D S ρ Csch hC z _hz
  dsimp only
  congr 1
  funext x k
  have h1 := hC (fun y k' => Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card *
    z y k') x (fun j => x.2.1 j ρ) k
  rw [setSelBits_self] at h1
  rw [h1]
  simp only [setSelBits_sel]
  have h2 := congrFun (h0TensorIdentity_holds D (fun e => z (setSelBits ρ x e) k))
    (fun j => x.2.1 j ρ)
  simp only [H0D, SD, Pi.smul_apply, smul_eq_mul] at h2
  exact h2.symm

/-! ## Lemma A.10 (`lem:transfer-phase`): conjugating a translation by a move permutation -/

/-- **Lemma A.10 (`lem:transfer-phase`) coordinate kernels** (`TranslationConjStmt`): for binary `M, M'` with `M M' = 1`,
`P_M X_v P_{M'} = X_{Mv}` for every `v`. -/
theorem translationConj_holds : TranslationConjStmt := by
  intro h M M' hMM' v
  have hM'M : M' * M = 1 := mul_eq_one_comm.mp hMM'
  have key : ∀ a b : Pt h, a = M.mulVec b ↔ b = M'.mulVec a := by
    intro a b
    constructor
    · rintro rfl
      rw [Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
    · rintro rfl
      rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
  have hcond : ∀ x y : Pt h, M'.mulVec x + v = M'.mulVec y ↔ y = x + M.mulVec v := by
    intro x y
    rw [← key, Matrix.mulVec_add, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
  ext x y
  simp only [Matrix.mul_apply, permOp, Xv, key, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hcond]

/-! ## Lemma A.10 (`lem:transfer-phase`): invertible binary matrices are products of row additions -/

namespace AppCLayerAlg

variable {n : ℕ}

/-- `rowAdd i j` is Mathlib's transvection `1 + single i j 1`. -/
theorem rowAdd_eq_transvection (i j : Fin n) : rowAdd i j = Matrix.transvection i j 1 := rfl

/-- Left multiplication by `rowAdd i j` adds row `j` to row `i`. -/
theorem rowAdd_mul_apply (i j a b : Fin n) (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (rowAdd i j * A) a b = A a b + (if a = i then A j b else 0) := by
  by_cases h : a = i
  · subst h
    rw [rowAdd_eq_transvection, Matrix.transvection_mul_apply_same, if_pos rfl, one_mul]
  · rw [rowAdd_eq_transvection, Matrix.transvection_mul_apply_of_ne _ _ _ _ h, if_neg h,
      add_zero]

/-- `rowAdd i j` is an involution for `i ≠ j` (characteristic `2`). -/
theorem rowAdd_mul_self {i j : Fin n} (h : i ≠ j) : rowAdd i j * rowAdd i j = 1 := by
  rw [rowAdd_eq_transvection, Matrix.transvection_mul_transvection_same _ _ h]
  have h2 : (1 + 1 : ZMod 2) = 0 := by decide
  rw [h2, Matrix.transvection_zero]

theorem det_rowAdd {i j : Fin n} (h : i ≠ j) : (rowAdd i j).det = 1 := by
  rw [rowAdd_eq_transvection]
  exact Matrix.det_transvection_of_ne _ _ h 1

/-- The product of the row additions of a list (leftmost factor first). -/
def prodL (l : List (Fin n × Fin n)) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  (l.map fun p => rowAdd p.1 p.2).prod

/-- A list of row additions with `i ≠ j` in every pair. -/
def ValidL (l : List (Fin n × Fin n)) : Prop := ∀ p ∈ l, p.1 ≠ p.2

theorem prodL_nil : prodL ([] : List (Fin n × Fin n)) = 1 := by
  simp [prodL]

theorem prodL_cons (p : Fin n × Fin n) (l : List (Fin n × Fin n)) :
    prodL (p :: l) = rowAdd p.1 p.2 * prodL l := by
  simp [prodL]

theorem prodL_append (l l' : List (Fin n × Fin n)) : prodL (l ++ l') = prodL l * prodL l' := by
  simp [prodL, List.prod_append]

theorem det_prodL : ∀ l : List (Fin n × Fin n), ValidL l → (prodL l).det = 1
  | [], _ => by rw [prodL_nil, Matrix.det_one]
  | p :: l, hl => by
    rw [prodL_cons, Matrix.det_mul, det_rowAdd (hl p List.mem_cons_self),
      det_prodL l (fun q hq => hl q (List.mem_cons_of_mem _ hq)), one_mul]

theorem prodL_mul_reverse : ∀ l : List (Fin n × Fin n), ValidL l →
    prodL l * prodL l.reverse = 1
  | [], _ => by simp [prodL_nil]
  | p :: l, hl => by
    rw [List.reverse_cons, prodL_append, prodL_cons, prodL_cons, prodL_nil, Matrix.mul_one,
      Matrix.mul_assoc, ← Matrix.mul_assoc (prodL l),
      prodL_mul_reverse l (fun q hq => hl q (List.mem_cons_of_mem _ hq)), Matrix.one_mul,
      rowAdd_mul_self (hl p List.mem_cons_self)]

/-- `B` is obtained from `A` by at most `len` row additions (`i ≠ j`). -/
def Reach (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (len : ℕ) : Prop :=
  ∃ l : List (Fin n × Fin n), ValidL l ∧ l.length ≤ len ∧ B = prodL l * A

theorem Reach.refl (A : Matrix (Fin n) (Fin n) (ZMod 2)) (len : ℕ) : Reach A A len :=
  ⟨[], fun _ h => by simp at h, Nat.zero_le _, by rw [prodL_nil, Matrix.one_mul]⟩

theorem Reach.step (A : Matrix (Fin n) (Fin n) (ZMod 2)) {i j : Fin n} (h : i ≠ j) :
    Reach A (rowAdd i j * A) 1 := by
  refine ⟨[(i, j)], fun p hp => ?_, le_rfl, by rw [prodL_cons, prodL_nil, Matrix.mul_one]⟩
  rw [List.mem_singleton] at hp
  rw [hp]
  exact h

theorem Reach.trans {A B C : Matrix (Fin n) (Fin n) (ZMod 2)} {m m' : ℕ} (h1 : Reach A B m)
    (h2 : Reach B C m') : Reach A C (m + m') := by
  obtain ⟨l, hl, hlen, rfl⟩ := h1
  obtain ⟨l', hl', hlen', rfl⟩ := h2
  refine ⟨l' ++ l, fun p hp => ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · exact hl' p hp
    · exact hl p hp
  · rw [List.length_append]
    omega
  · rw [prodL_append, Matrix.mul_assoc]

theorem Reach.mono {A B : Matrix (Fin n) (Fin n) (ZMod 2)} {m m' : ℕ} (h : Reach A B m)
    (hm : m ≤ m') : Reach A B m' := by
  obtain ⟨l, hl, hlen, rfl⟩ := h
  exact ⟨l, hl, hlen.trans hm, rfl⟩

theorem Reach.det_eq {A B : Matrix (Fin n) (Fin n) (ZMod 2)} {m : ℕ} (h : Reach A B m) :
    B.det = A.det := by
  obtain ⟨l, hl, _, rfl⟩ := h
  rw [Matrix.det_mul, det_prodL l hl, one_mul]

/-- The first `k` columns of `A` are those of the identity. -/
def ColsId (A : Matrix (Fin n) (Fin n) (ZMod 2)) (k : ℕ) : Prop :=
  ∀ a b : Fin n, (b : ℕ) < k → A a b = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) a b

/-- In `𝔽₂`, `x ≠ 1 → x = 0`. -/
theorem zmod2_eq_zero_of_ne_one : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by
  decide

/-- Pivot existence: if `det A` is a unit and the first `k` columns of `A` are those of `1`,
some row `r ≥ k` has `A r k = 1` (read off `(A⁻¹ A) k k = 1`). -/
theorem exists_pivot (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : IsUnit A.det) (k : Fin n)
    (hc : ColsId A k) : ∃ r : Fin n, (k : ℕ) ≤ r ∧ A r k = 1 := by
  have hN : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul (A := A) hA
  have hNcol : ∀ a j : Fin n, (j : ℕ) < k →
      A⁻¹ a j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) a j := by
    intro a j hj
    have h1 := congrFun (congrFun hN a) j
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at h1
    · rwa [hc j j hj, Matrix.one_apply_eq, mul_one] at h1
    · intro r _ hrj
      rw [hc r j hj, Matrix.one_apply_ne hrj, mul_zero]
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'
  by_contra hne
  push Not at hne
  have h1 := congrFun (congrFun hN k) k
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_zero] at h1
  · exact zero_ne_one h1
  · intro r _
    by_cases hr : (k : ℕ) ≤ r
    · rw [zmod2_eq_zero_of_ne_one _ (hne r hr), mul_zero]
    · have hr' : (r : ℕ) < k := lt_of_not_ge hr
      have hkr : k ≠ r := fun h => by rw [h] at hr'; exact lt_irrefl _ hr'
      rw [hNcol k r hr', Matrix.one_apply_ne hkr, zero_mul]

/-- Pivot step: at most one row addition makes the pivot `A k k` equal to `1`. -/
theorem pivot_step (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : IsUnit A.det) (k : Fin n)
    (hc : ColsId A k) : ∃ A₁, Reach A A₁ 1 ∧ ColsId A₁ k ∧ A₁ k k = 1 := by
  obtain ⟨r, hkr, hr⟩ := exists_pivot A hA k hc
  by_cases hkk : A k k = 1
  · exact ⟨A, Reach.refl A 1, hc, hkk⟩
  · have hrk : k ≠ r := by
      rintro rfl
      exact hkk hr
    refine ⟨rowAdd k r * A, Reach.step A hrk, fun a b hb => ?_, ?_⟩
    · rw [rowAdd_mul_apply]
      by_cases ha : a = k
      · have hkb : k ≠ b := fun h => by rw [h] at hb; exact lt_irrefl _ hb
        have hrb : r ≠ b := fun h => by rw [← h] at hb; omega
        rw [if_pos ha, hc a b hb, hc r b hb, ha, Matrix.one_apply_ne hkb,
          Matrix.one_apply_ne hrb, add_zero]
      · rw [if_neg ha, add_zero, hc a b hb]
    · rw [rowAdd_mul_apply, if_pos rfl, hr, zmod2_eq_zero_of_ne_one _ hkk, zero_add]

/-- Adding row `k` to every row of a duplicate-free list `T ∌ k` (closed formula). -/
theorem prodL_col_mul_apply (A : Matrix (Fin n) (Fin n) (ZMod 2)) (k : Fin n) :
    ∀ T : List (Fin n), T.Nodup → k ∉ T → ∀ a b : Fin n,
      (prodL (T.map fun i => (i, k)) * A) a b = A a b + (if a ∈ T then A k b else 0)
  | [], _, _, a, b => by simp [prodL_nil]
  | i :: T, hT, hk, a, b => by
    have hiT : i ∉ T := (List.nodup_cons.mp hT).1
    have hT' : T.Nodup := (List.nodup_cons.mp hT).2
    have hkT : k ∉ T := fun h => hk (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, prodL_cons]
    rw [Matrix.mul_assoc, rowAdd_mul_apply, prodL_col_mul_apply A k T hT' hkT a b,
      prodL_col_mul_apply A k T hT' hkT k b, if_neg hkT, add_zero]
    by_cases ha : a = i
    · rw [if_pos ha, ha, if_neg hiT, if_pos List.mem_cons_self, add_zero]
    · have hmem : a ∈ i :: T ↔ a ∈ T := by simp [ha]
      by_cases haT : a ∈ T
      · rw [if_neg ha, if_pos haT, if_pos (hmem.mpr haT), add_zero]
      · rw [if_neg ha, if_neg haT, if_neg (fun h => haT (hmem.mp h))]
        simp only [add_zero]

/-- Clearing step: with pivot `A k k = 1`, adding row `k` to every other row with a `1` in
column `k` makes column `k` that of the identity and keeps the first `k` columns. -/
theorem clear_step (A : Matrix (Fin n) (Fin n) (ZMod 2)) (k : Fin n) (hc : ColsId A k)
    (hkk : A k k = 1) : ∃ B, Reach A B n ∧ ColsId B ((k : ℕ) + 1) := by
  obtain ⟨T, hTdef⟩ : ∃ T : List (Fin n),
      T = (Finset.univ.filter fun i => i ≠ k ∧ A i k = 1).toList := ⟨_, rfl⟩
  have hmemT : ∀ a, a ∈ T ↔ a ≠ k ∧ A a k = 1 := by
    intro a
    simp [hTdef]
  have hT : T.Nodup := by
    rw [hTdef]
    exact Finset.nodup_toList _
  have hkT : k ∉ T := fun h => ((hmemT k).mp h).1 rfl
  refine ⟨prodL (T.map fun i => (i, k)) * A, ⟨T.map fun i => (i, k), ?_, ?_, rfl⟩, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact ((hmemT i).mp hi).1
  · rw [List.length_map, hTdef, Finset.length_toList]
    calc _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  · intro a b hb
    rw [prodL_col_mul_apply A k T hT hkT a b]
    by_cases hbk : (b : ℕ) < k
    · have hkb : k ≠ b := fun h => by rw [h] at hbk; exact lt_irrefl _ hbk
      rw [hc k b hbk, Matrix.one_apply_ne hkb, hc a b hbk, ite_self, add_zero]
    · have hbk' : b = k := Fin.ext (by omega)
      rw [hbk', hkk]
      by_cases hak : a = k
      · rw [if_neg (by rw [hak]; exact hkT), add_zero, hak, hkk, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hak]
        by_cases h1 : A a k = 1
        · rw [if_pos ((hmemT a).mpr ⟨hak, h1⟩), h1]
          decide
        · rw [if_neg (fun h => h1 ((hmemT a).mp h).2), add_zero,
            zmod2_eq_zero_of_ne_one _ h1]

/-- One column of Gauss–Jordan elimination: at most `n + 1` row additions. -/
theorem column_step (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : IsUnit A.det) (k : Fin n)
    (hc : ColsId A k) : ∃ B, Reach A B (1 + n) ∧ ColsId B ((k : ℕ) + 1) := by
  obtain ⟨A₁, h₁, hc₁, hkk₁⟩ := pivot_step A hA k hc
  obtain ⟨B, h₂, hcB⟩ := clear_step A₁ k hc₁ hkk₁
  exact ⟨B, h₁.trans h₂, hcB⟩

/-- After `k ≤ n` columns: at most `k (n + 1)` row additions. -/
theorem elim_cols (M : Matrix (Fin n) (Fin n) (ZMod 2)) (hM : IsUnit M.det) :
    ∀ k : ℕ, k ≤ n → ∃ B, Reach M B (k * (n + 1)) ∧ ColsId B k
  | 0, _ => ⟨M, Reach.refl M _, fun _ b hb => absurd hb (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    obtain ⟨B, hB, hcB⟩ := elim_cols M hM k (by omega)
    have hBu : IsUnit B.det := by
      rw [hB.det_eq]
      exact hM
    obtain ⟨C, hC, hcC⟩ := column_step B hBu ⟨k, by omega⟩ hcB
    refine ⟨C, (hB.trans hC).mono ?_, hcC⟩
    have h : (k + 1) * (n + 1) = k * (n + 1) + (n + 1) := by ring
    omega

/-- `n(n+1) ≤ n(n−1) + 3n` in `ℕ`. -/
theorem len_bound (n : ℕ) : n * (n + 1) ≤ n * (n - 1) + 3 * n := by
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    nlinarith

end AppCLayerAlg

/-- **Lemma A.10 (`lem:transfer-phase`) row additions** (`BinaryRowAdditionsStmt`): every binary `n × n` matrix with unit
determinant is the product of a list of at most `n(n+1) ≤ n(n−1) + 3n` row additions
`rowAdd i j` with `i ≠ j`. -/
theorem binaryRowAdditions_holds : BinaryRowAdditionsStmt := by
  intro n M hM
  obtain ⟨B, ⟨l, hl, hlen, hB⟩, hcB⟩ := elim_cols M hM n le_rfl
  have hB1 : B = 1 := by
    ext a b
    exact hcB a b b.isLt
  rw [hB1] at hB
  have h2 : M * prodL l = 1 := mul_eq_one_comm.mp hB.symm
  refine ⟨l.reverse, fun p hp => hl p (List.mem_reverse.mp hp), ?_, ?_⟩
  · rw [List.length_reverse]
    exact hlen.trans (len_bound n)
  · show M = prodL l.reverse
    calc M = M * (prodL l * prodL l.reverse) := by rw [prodL_mul_reverse l hl, Matrix.mul_one]
      _ = M * prodL l * prodL l.reverse := by rw [Matrix.mul_assoc]
      _ = prodL l.reverse := by rw [h2, Matrix.one_mul]

end SubNLogN.Math.Networks
