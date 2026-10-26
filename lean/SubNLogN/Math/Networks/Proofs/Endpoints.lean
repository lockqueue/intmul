import SubNLogN.Math.Networks.PhaseFrames

/-!
# Endpoint certificates B2, C3 ([OAI26] Prop. 7 and Prop. 8 endpoints), part 1

Proofs of `Prop7EndpointStmt` (`BitFrames.lean`) and `TpowMulStmt` (`PhaseFrames.lean`), plus the
generic label/projection lemmas used for the complex endpoints in `Endpoints2.lean`
(Appendix D.2, Proposition D.3 (`oai:networks`, `oai:prop8`); [OAI26, §§3.4–3.5, Props. 7–8]).

All helpers live in the namespace `SubNLogN.Math.Networks.EndpointsAux`; only the contract theorems
`prop7Endpoint_holds`, `tpowMul_holds` are at top level. The bit endpoint identity is proved for every
`h ≠ 9` (`EndpointsAux.prop7Endpoint_gen`) and specialized to `h = 100`.

## Plan
1. Generic label lemma (any field `K`, factor form `β` on `K^h`, cube form `β₃` on `K^{[h]³}` with
   `β₃(u⊗v⊗w, u'⊗v'⊗w') = β(u,u') β(v,v') β(w,w')`):
   `labelSub β (labU a) = K ∙ u_a` (`u_a = t_{a₁} ⊗ t_{a₂} ⊗ t_{a₃}`), and, when every
   `β(t_{a_k}, t_{a_k}) ≠ 0`, `labelSub β (labUperp a) = β₃.orthogonal (K ∙ u_a)`.
   `⊆`: factorwise orthogonality. `⊇`: every pure tensor splits as
   `f⊗g⊗k = (f-πf)⊗g⊗k + πf⊗(g-πg)⊗k + πf⊗πg⊗(k-πk) + πf⊗πg⊗πk` (`π` = projection onto `⟨t⟩`
   along `t^⊥` in the relevant factor), the first three terms lie in the summands of `labUperp a`,
   the last in `K ∙ u_a`; every cube function is a sum of pure tensors, and
   `K ∙ u_a ⊓ (K ∙ u_a)^⊥ = 0`, so the inclusion is an equality.
   If `β₃` is symmetric and nondegenerate then `((K ∙ u_a)^⊥)^⊥ = K ∙ u_a`; hence both labels are
   complemented by their orthogonals and `P_{U_a^⊥} + P_{U_a} = 1`.
2. Bit network (B2): `β(t,t) = 3 - 9/9 = 2`; `(I + J/(9-h))(I - J/9) = I` for `h ≠ 9` (as
   `J² = hJ`), so the cube form is nondegenerate (`kron3` is multiplicative);
   `labelSub β labFull = ⊤`, `projAlong β₃ ⊤ = id`.
3. Tensor powers: `tpow k (A * B) = tpow k A * tpow k B` (`Fintype.prod_sum`).
-/

namespace SubNLogN.Math.Networks

namespace EndpointsAux

open Matrix

/-! ### Sums over the cube -/

lemma sum_cube_mul {R : Type*} [CommSemiring R] {h : ℕ} (f g k : Fin h → R) :
    ∑ p : Cube h, f p.1 * g p.2.1 * k p.2.2 = (∑ i, f i) * (∑ j, g j) * (∑ l, k l) := by
  simp only [Fintype.sum_prod_type]
  rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, mul_assoc]

lemma card_cube (h : ℕ) : Fintype.card (Cube h) = h ^ 3 := by
  simp only [Fintype.card_prod, Fintype.card_fin]; ring

section Generic

variable {K : Type*} [Field K] {h : ℕ}

/-! ### Pure tensors and label semantics -/

lemma pure3_smul_smul_smul (a b c : K) (u v w : Fin h → K) :
    pure3 (a • u) (b • v) (c • w) = (a * b * c) • pure3 u v w := by
  funext p; simp only [pure3, Pi.smul_apply, smul_eq_mul]; ring

lemma pure3_split (f g k f' g' k' : Fin h → K) :
    pure3 f g k = pure3 (f - f') g k + pure3 f' (g - g') k + pure3 f' g' (k - k') +
      pure3 f' g' k' := by
  funext p; simp only [pure3, Pi.add_apply, Pi.sub_apply]; ring

lemma pure3_single (i : Cube h) :
    (fun j : Cube h => if i = j then (1 : K) else 0) =
      pure3 (fun j => if i.1 = j then 1 else 0) (fun j => if i.2.1 = j then 1 else 0)
        (fun j => if i.2.2 = j then 1 else 0) := by
  funext j
  obtain ⟨i1, i2, i3⟩ := i
  obtain ⟨j1, j2, j3⟩ := j
  simp only [pure3, Prod.mk.injEq]
  by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = j2 <;> by_cases h3 : i3 = j3 <;> simp [h1, h2, h3]

/-- A submodule containing every pure tensor is everything. -/
lemma mem_of_pure3_mem (P : Submodule K (Cube h → K)) (hP : ∀ u v w, pure3 u v w ∈ P)
    (x : Cube h → K) : x ∈ P := by
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  rw [pure3_single]
  exact hP _ _ _

variable (β : LinearMap.BilinForm K (Fin h → K))

lemma labelSub_cons (σ : Summand h) (L : SymLabel h) :
    labelSub β (σ :: L) = summandSub β σ ⊔ labelSub β L := rfl

lemma labelSub_nil : labelSub β ([] : SymLabel h) = ⊥ := rfl

lemma summandSub_le_labelSub {σ : Summand h} {L : SymLabel h} (hσ : σ ∈ L) :
    summandSub β σ ≤ labelSub β L := by
  induction L with
  | nil => simp at hσ
  | cons τ L ih =>
    rw [labelSub_cons]
    rcases List.mem_cons.1 hσ with rfl | h'
    · exact le_sup_left
    · exact le_sup_of_le_right (ih h')

lemma labelSub_le {L : SymLabel h} {P : Submodule K (Cube h → K)}
    (hL : ∀ σ ∈ L, summandSub β σ ≤ P) : labelSub β L ≤ P := by
  induction L with
  | nil => exact bot_le
  | cons τ L ih =>
    rw [labelSub_cons]
    exact sup_le (hL τ List.mem_cons_self) (ih fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ))

lemma pure3_mem_summandSub {σ : Summand h} {u v w : Fin h → K}
    (hu : u ∈ tokSub β σ.1) (hv : v ∈ tokSub β σ.2.1) (hw : w ∈ tokSub β σ.2.2) :
    pure3 u v w ∈ summandSub β σ :=
  Submodule.subset_span ⟨u, hu, v, hv, w, hw, rfl⟩

/-- `U_a = K ∙ (t_{a₁} ⊗ t_{a₂} ⊗ t_{a₃})` (no hypothesis on `β`). -/
theorem labelSub_labU (a : Addr h) :
    labelSub β (labU a) = K ∙ pure3 (ind a.1) (ind a.2.1) (ind a.2.2) := by
  rw [labU, labelSub_cons, labelSub_nil, sup_bot_eq]
  apply le_antisymm
  · rw [summandSub, Submodule.span_le]
    rintro x ⟨u, hu, v, hv, w, hw, rfl⟩
    change u ∈ K ∙ ind a.1 at hu
    change v ∈ K ∙ ind a.2.1 at hv
    change w ∈ K ∙ ind a.2.2 at hw
    obtain ⟨c1, rfl⟩ := Submodule.mem_span_singleton.1 hu
    obtain ⟨c2, rfl⟩ := Submodule.mem_span_singleton.1 hv
    obtain ⟨c3, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [SetLike.mem_coe, pure3_smul_smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact pure3_mem_summandSub β (σ := (.line a.1, .line a.2.1, .line a.2.2))
      (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)
      (Submodule.mem_span_singleton_self _)

/-- `𝓕 = F ⊗ F ⊗ F` is everything (no hypothesis on `β`). -/
theorem labelSub_labFull : labelSub β (labFull : SymLabel h) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  apply mem_of_pure3_mem
  intro u v w
  exact summandSub_le_labelSub β (σ := (.full, .full, .full)) (List.mem_singleton_self _)
    (pure3_mem_summandSub β (σ := (.full, .full, .full)) Submodule.mem_top Submodule.mem_top
      Submodule.mem_top)

end Generic

/-- The component of `f` that is `β`-orthogonal to `t` (any bilinear form, `β t t ≠ 0`). -/
lemma perp_part_mem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (β : LinearMap.BilinForm K V) {t : V} (ht : β t t ≠ 0) (f : V) :
    f - (β t f / β t t) • t ∈ β.orthogonal (K ∙ t) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
  rw [map_smul, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, smul_eq_mul,
    div_mul_cancel₀ _ ht, sub_self, mul_zero]

/-! ### The key lemma: `U_a^⊥ = labUperp a`, and projections -/

section KeyLemma

variable {K : Type*} [Field K] {h : ℕ}
variable (β : LinearMap.BilinForm K (Fin h → K)) (β3 : LinearMap.BilinForm K (Cube h → K))

/-- The cube form factorizes on pure tensors. -/
def CubeFac : Prop :=
  ∀ u v w u' v' w' : Fin h → K, β3 (pure3 u v w) (pure3 u' v' w') = β u u' * β v v' * β w w'

/-- Key lemma: if the cube form factorizes on pure tensors and `β(t_{a_k}, t_{a_k}) ≠ 0` for
`k = 1, 2, 3`, then the symbolic label `labUperp a` means `(K ∙ u_a)^⊥`. -/
theorem labelSub_labUperp (hfac : CubeFac β β3) (a : Addr h)
    (h1 : β (ind a.1) (ind a.1) ≠ 0) (h2 : β (ind a.2.1) (ind a.2.1) ≠ 0)
    (h3 : β (ind a.2.2) (ind a.2.2) ≠ 0) :
    labelSub β (labUperp a) = β3.orthogonal (K ∙ pure3 (ind a.1) (ind a.2.1) (ind a.2.2)) := by
  have huu : β3 (pure3 (ind a.1) (ind a.2.1) (ind a.2.2))
      (pure3 (ind a.1) (ind a.2.1) (ind a.2.2)) ≠ 0 := by
    rw [hfac]; exact mul_ne_zero (mul_ne_zero h1 h2) h3
  have hc := LinearMap.BilinForm.isCompl_span_singleton_orthogonal huu
  have hle : labelSub β (labUperp a) ≤
      β3.orthogonal (K ∙ pure3 (ind a.1) (ind a.2.1) (ind a.2.2)) := by
    apply labelSub_le
    intro σ hσ
    simp only [labUperp, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rw [summandSub, Submodule.span_le]
    rcases hσ with rfl | rfl | rfl
    · rintro x ⟨f, hf, g, -, k, -, rfl⟩
      have hf' : f ∈ β.orthogonal (K ∙ ind a.1) := hf
      have h0 : β (ind a.1) f = 0 :=
        LinearMap.BilinForm.mem_orthogonal_iff.1 hf' _ (Submodule.mem_span_singleton_self _)
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
      rw [map_smul, LinearMap.smul_apply, hfac, h0]; simp
    · rintro x ⟨f, -, g, hg, k, -, rfl⟩
      have hg' : g ∈ β.orthogonal (K ∙ ind a.2.1) := hg
      have h0 : β (ind a.2.1) g = 0 :=
        LinearMap.BilinForm.mem_orthogonal_iff.1 hg' _ (Submodule.mem_span_singleton_self _)
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
      rw [map_smul, LinearMap.smul_apply, hfac, h0]; simp
    · rintro x ⟨f, -, g, -, k, hk, rfl⟩
      have hk' : k ∈ β.orthogonal (K ∙ ind a.2.2) := hk
      have h0 : β (ind a.2.2) k = 0 :=
        LinearMap.BilinForm.mem_orthogonal_iff.1 hk' _ (Submodule.mem_span_singleton_self _)
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
      rw [map_smul, LinearMap.smul_apply, hfac, h0]; simp
  have hsup : ∀ x, x ∈ (K ∙ pure3 (ind a.1) (ind a.2.1) (ind a.2.2)) ⊔ labelSub β (labUperp a) := by
    intro x
    apply mem_of_pure3_mem
    intro f g k
    rw [pure3_split f g k ((β (ind a.1) f / β (ind a.1) (ind a.1)) • ind a.1)
      ((β (ind a.2.1) g / β (ind a.2.1) (ind a.2.1)) • ind a.2.1)
      ((β (ind a.2.2) k / β (ind a.2.2) (ind a.2.2)) • ind a.2.2)]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · refine Submodule.mem_sup_right (summandSub_le_labelSub β (σ := (.perp a.1, .full, .full))
        (by simp [labUperp]) ?_)
      exact pure3_mem_summandSub β (σ := (.perp a.1, .full, .full)) (perp_part_mem β h1 f)
        Submodule.mem_top Submodule.mem_top
    · refine Submodule.mem_sup_right (summandSub_le_labelSub β
        (σ := (.line a.1, .perp a.2.1, .full)) (by simp [labUperp]) ?_)
      exact pure3_mem_summandSub β (σ := (.line a.1, .perp a.2.1, .full))
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) (perp_part_mem β h2 g)
        Submodule.mem_top
    · refine Submodule.mem_sup_right (summandSub_le_labelSub β
        (σ := (.line a.1, .line a.2.1, .perp a.2.2)) (by simp [labUperp]) ?_)
      exact pure3_mem_summandSub β (σ := (.line a.1, .line a.2.1, .perp a.2.2))
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) (perp_part_mem β h3 k)
    · refine Submodule.mem_sup_left ?_
      rw [pure3_smul_smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  apply le_antisymm hle
  intro x hx
  obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 (hsup x)
  have hs' : s ∈ β3.orthogonal (K ∙ pure3 (ind a.1) (ind a.2.1) (ind a.2.2)) := by
    have := Submodule.sub_mem _ hx (hle hl)
    rwa [add_sub_cancel_right] at this
  rw [Submodule.disjoint_def.1 hc.disjoint s hs hs', zero_add]
  exact hl

end KeyLemma

section Proj

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For a symmetric nondegenerate form and `β u u ≠ 0`: `((K ∙ u)^⊥)^⊥ = K ∙ u`. -/
theorem orth_orth_span (β3 : LinearMap.BilinForm K V) (hsymm : ∀ x y, β3 x y = β3 y x)
    (hnd : ∀ m, (∀ n, β3 n m = 0) → m = 0) {u : V} (huu : β3 u u ≠ 0) :
    β3.orthogonal (β3.orthogonal (K ∙ u)) = K ∙ u := by
  have hc := LinearMap.BilinForm.isCompl_span_singleton_orthogonal huu
  have hdec : ∀ x : V, ∃ s ∈ K ∙ u, ∃ o ∈ β3.orthogonal (K ∙ u), s + o = x := fun x =>
    Submodule.mem_sup.1 (by rw [hc.sup_eq_top]; exact Submodule.mem_top)
  have hle : K ∙ u ≤ β3.orthogonal (β3.orthogonal (K ∙ u)) := by
    intro s hs
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hsymm]
    exact LinearMap.BilinForm.mem_orthogonal_iff.1 hn s hs
  refine le_antisymm ?_ hle
  intro x hx
  obtain ⟨s, hs, o, ho, rfl⟩ := hdec x
  have ho' : o ∈ β3.orthogonal (β3.orthogonal (K ∙ u)) := by
    have := Submodule.sub_mem _ hx (hle hs)
    rwa [add_sub_cancel_left] at this
  have ho0 : o = 0 := by
    apply hnd
    intro n
    obtain ⟨s', hs', o', ho'', rfl⟩ := hdec n
    rw [map_add, LinearMap.add_apply, LinearMap.BilinForm.mem_orthogonal_iff.1 ho s' hs',
      LinearMap.BilinForm.mem_orthogonal_iff.1 ho' o' ho'', add_zero]
  rw [ho0, add_zero]; exact hs

lemma projAlong_eq_projection (β : LinearMap.BilinForm K V) (U W : Submodule K V)
    (hW : β.orthogonal U = W) (hc : IsCompl U W) : projAlong β U = U.projection W hc := by
  subst hW
  unfold projAlong
  rw [dif_pos hc]

lemma projAlong_bot (β : LinearMap.BilinForm K V) : projAlong β ⊥ = 0 := by
  unfold projAlong
  split_ifs with hc
  · ext x
    simp
  · rfl

lemma projAlong_top (β : LinearMap.BilinForm K V) (hnd : ∀ m, (∀ n, β n m = 0) → m = 0) :
    projAlong β ⊤ = LinearMap.id := by
  have hbot : β.orthogonal ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_bot]
    exact hnd m fun n => LinearMap.BilinForm.mem_orthogonal_iff.1 hm n Submodule.mem_top
  rw [projAlong_eq_projection β ⊤ ⊥ hbot isCompl_top_bot]
  ext x
  rw [LinearMap.id_apply]
  exact Submodule.projection_apply_of_mem_left _ Submodule.mem_top

lemma projAlong_span_apply (β : LinearMap.BilinForm K V) {u : V} (huu : β u u ≠ 0) (z : V) :
    projAlong β (K ∙ u) z = (β u z / β u u) • u := by
  have hc := LinearMap.BilinForm.isCompl_span_singleton_orthogonal huu
  rw [projAlong_eq_projection β _ _ rfl hc]
  conv_lhs => rw [← add_sub_cancel ((β u z / β u u) • u) z]
  rw [map_add, Submodule.projection_apply_of_mem_left hc
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)),
    Submodule.projection_apply_of_mem_right hc (perp_part_mem β huu z), add_zero]

lemma projAlong_perp_apply (β : LinearMap.BilinForm K V) (hsymm : ∀ x y, β x y = β y x)
    (hnd : ∀ m, (∀ n, β n m = 0) → m = 0) {u : V} (huu : β u u ≠ 0) (z : V) :
    projAlong β (β.orthogonal (K ∙ u)) z = z - (β u z / β u u) • u := by
  have hc := LinearMap.BilinForm.isCompl_span_singleton_orthogonal huu
  rw [projAlong_eq_projection β _ _ (orth_orth_span β hsymm hnd huu) hc.symm,
    Submodule.projection_eq_self_sub_projection hc z, ← projAlong_eq_projection β _ _ rfl hc,
    projAlong_span_apply β huu z]

/-- `P_{U^⊥} + P_U = 1` for `U = K ∙ u`, `β u u ≠ 0`, `β` symmetric and nondegenerate. -/
lemma projAlong_perp_add (β : LinearMap.BilinForm K V) (hsymm : ∀ x y, β x y = β y x)
    (hnd : ∀ m, (∀ n, β n m = 0) → m = 0) {u : V} (huu : β u u ≠ 0) :
    projAlong β (β.orthogonal (K ∙ u)) + projAlong β (K ∙ u) = LinearMap.id := by
  ext z
  rw [LinearMap.add_apply, LinearMap.id_apply, projAlong_perp_apply β hsymm hnd huu,
    projAlong_span_apply β huu, sub_add_cancel]

end Proj

/-! ### Kronecker cubes and Gram-matrix forms -/

section Kron

variable {K : Type*} [Field K] {h : ℕ}

lemma kron3_mul (A B C A' B' C' : Matrix (Fin h) (Fin h) K) :
    kron3 A B C * kron3 A' B' C' = kron3 (A * A') (B * B') (C * C') := by
  ext p r
  simp only [Matrix.mul_apply, kron3]
  rw [← sum_cube_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

lemma kron3_one : kron3 (1 : Matrix (Fin h) (Fin h) K) 1 1 = 1 := by
  ext ⟨p1, p2, p3⟩ ⟨q1, q2, q3⟩
  simp only [kron3, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> by_cases h3 : p3 = q3 <;> simp [h1, h2, h3]

/-- The form of a Kronecker cube factorizes on pure tensors. -/
lemma toBilin'_kron3_pure3 (G : Matrix (Fin h) (Fin h) K) (u v w u' v' w' : Fin h → K) :
    Matrix.toBilin' (kron3 G G G) (pure3 u v w) (pure3 u' v' w') =
      Matrix.toBilin' G u u' * Matrix.toBilin' G v v' * Matrix.toBilin' G w w' := by
  simp only [Matrix.toBilin'_apply, pure3, kron3]
  rw [← sum_cube_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sum_cube_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

lemma toBilin'_comm {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (hM : ∀ i j, M i j = M j i) (x y : n → K) : Matrix.toBilin' M x y = Matrix.toBilin' M y x := by
  simp only [Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hM j i]; ring

/-- A matrix with a left inverse gives a (right-)nondegenerate form. -/
lemma toBilin'_nondeg {n : Type*} [Fintype n] [DecidableEq n] (M N : Matrix n n K)
    (hNM : N * M = 1) (m : n → K) (hm : ∀ x, Matrix.toBilin' M x m = 0) : m = 0 := by
  have hv : M *ᵥ m = 0 := by
    funext p
    have := hm (Pi.single p 1)
    rw [Matrix.toBilin'_apply', single_dotProduct, one_mul] at this
    exact this
  calc m = (N * M) *ᵥ m := by rw [hNM, Matrix.one_mulVec]
    _ = N *ᵥ (M *ᵥ m) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]

lemma ind_mul_self {h : ℕ} (t : Tri h) (i : Fin h) : (ind t i : K) * ind t i = ind t i := by
  unfold ind; split_ifs <;> simp

lemma sum_ind (t : Tri h) : ∑ i, (ind t i : K) = 3 := by
  unfold ind
  rw [Fintype.sum_ite_mem, Finset.sum_const, t.2]
  simp

end Kron

/-! ### The bit network (B2) -/

section Bit

lemma G0_apply (h : ℕ) (i j : Fin h) : G0 h i j = (if i = j then 1 else 0) - (9 : ℚ)⁻¹ := by
  simp [G0, Matrix.one_apply]

lemma betaB_apply (h : ℕ) (x y : Fin h → ℚ) :
    betaB h x y = ∑ i, x i * y i - (9 : ℚ)⁻¹ * ((∑ i, x i) * (∑ j, y j)) := by
  rw [betaB, Matrix.toBilin'_apply, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [G0_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `⟨t_T, t_T⟩ = 3 - 9/9 = 2` for the bit factor form. -/
lemma betaB_ind_self (h : ℕ) (t : Tri h) : betaB h (ind t) (ind t) = 2 := by
  rw [betaB_apply]
  simp only [ind_mul_self, sum_ind]
  norm_num

lemma betaB_ind_ne (h : ℕ) (t : Tri h) : betaB h (ind t) (ind t) ≠ 0 := by
  rw [betaB_ind_self]; norm_num

/-- `I + J/(9 - h)`, the inverse of the bit Gram matrix `I - J/9` when `h ≠ 9`. -/
def G0inv (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  1 + ((9 : ℚ) - h)⁻¹ • Matrix.of (fun _ _ => (1 : ℚ))

lemma G0inv_mul_G0 (h : ℕ) (h9 : h ≠ 9) : G0inv h * G0 h = 1 := by
  have h9' : (9 : ℚ) - h ≠ 0 := by
    intro hq
    apply h9
    have : (h : ℚ) = 9 := by linarith
    exact_mod_cast this
  ext i j
  have e : ∀ k : Fin h, G0inv h i k * G0 h k j =
      (if i = k then (if k = j then (1 : ℚ) else 0) else 0) - (9 : ℚ)⁻¹ * (if i = k then 1 else 0)
        + ((9 : ℚ) - h)⁻¹ * (if k = j then 1 else 0) - ((9 : ℚ) - h)⁻¹ * (9 : ℚ)⁻¹ := by
    intro k
    simp only [G0inv, G0_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, mul_one]
    split_ifs <;> ring
  rw [Matrix.mul_apply]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.one_apply]
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

lemma G0_symm (h : ℕ) (i j : Fin h) : G0 h i j = G0 h j i := by
  rw [G0_apply, G0_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij.symm]
  · rw [if_neg hij, if_neg (Ne.symm hij)]

lemma betaB3_fac (h : ℕ) : CubeFac (betaB h) (betaB3 h) := fun u v w u' v' w' =>
  toBilin'_kron3_pure3 (G0 h) u v w u' v' w'

lemma betaB3_symm (h : ℕ) (x y : Cube h → ℚ) : betaB3 h x y = betaB3 h y x :=
  toBilin'_comm _ (fun p q => by
    show G0 h p.1 q.1 * G0 h p.2.1 q.2.1 * G0 h p.2.2 q.2.2 =
      G0 h q.1 p.1 * G0 h q.2.1 p.2.1 * G0 h q.2.2 p.2.2
    rw [G0_symm h p.1 q.1, G0_symm h p.2.1 q.2.1, G0_symm h p.2.2 q.2.2]) x y

lemma betaB3_nondeg (h : ℕ) (h9 : h ≠ 9) (m : Cube h → ℚ) (hm : ∀ n, betaB3 h n m = 0) :
    m = 0 :=
  toBilin'_nondeg _ (kron3 (G0inv h) (G0inv h) (G0inv h))
    (by rw [kron3_mul, G0inv_mul_G0 h h9, kron3_one]) m hm

/-- B2 for every `h ≠ 9`: `M_{sink(ρ(w))} - M_{source(w)} = I_m` for every role `w`
(on `X_a`: `P_{U_a^⊥} + P_{U_a} = I`; on the other roles `P_𝓕 - 0 = I`). -/
theorem prop7Endpoint_gen (h : ℕ) (h9 : h ≠ 9) :
    ∀ w : Role .bit h, frameB (.sink w.rho) - frameB (.source w) = 1 := by
  have hfull : projAlong (betaB3 h) (labelSub (betaB h) labFull) = 1 := by
    rw [labelSub_labFull, projAlong_top _ (betaB3_nondeg h h9)]; rfl
  intro w
  cases w with
  | X a =>
    have huu : betaB3 h (pure3 (ind a.1) (ind a.2.1) (ind a.2.2))
        (pure3 (ind a.1) (ind a.2.1) (ind a.2.2)) ≠ 0 := by
      rw [betaB3_fac h]
      exact mul_ne_zero (mul_ne_zero (betaB_ind_ne _ _) (betaB_ind_ne _ _)) (betaB_ind_ne _ _)
    show projAlong (betaB3 h) (labelSub (betaB h) (labUperp a)) -
      -projAlong (betaB3 h) (labelSub (betaB h) (labU a)) = 1
    rw [labelSub_labUperp (betaB h) (betaB3 h) (betaB3_fac h) a (betaB_ind_ne _ _)
      (betaB_ind_ne _ _) (betaB_ind_ne _ _), labelSub_labU, sub_neg_eq_add,
      projAlong_perp_add _ (betaB3_symm h) (betaB3_nondeg h h9) huu]
    rfl
  | Y a =>
    show projAlong (betaB3 h) (labelSub (betaB h) labFull) - 0 = 1
    rw [sub_zero, hfull]
  | side j ι p =>
    show projAlong (betaB3 h) (labelSub (betaB h) labFull) - 0 = 1
    rw [sub_zero, hfull]
  | center j ι c =>
    show projAlong (betaB3 h) (labelSub (betaB h) labFull) - 0 = 1
    rw [sub_zero, hfull]

end Bit

/-! ### Tensor powers over columns -/

section Tpow

theorem tpow_mul {ι : Type*} [Fintype ι] (k : ℕ) (A B : Matrix ι ι ℂ) :
    tpow k (A * B) = tpow k A * tpow k B := by
  ext x y
  simp only [tpow, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]

theorem tpow_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (d : ι → ℂ) :
    tpow k (Matrix.diagonal d) = Matrix.diagonal fun x => ∏ c, d (x c) := by
  ext x y
  simp only [tpow, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hxy
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg hc)

theorem tpow_one {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    tpow k (1 : Matrix ι ι ℂ) = 1 := by
  rw [← Matrix.diagonal_one, tpow_diagonal]
  simp

theorem tpow_smul {ι : Type*} [Fintype ι] (k : ℕ) (c : ℂ) (A : Matrix ι ι ℂ) :
    tpow k (c • A) = c ^ k • tpow k A := by
  ext x y
  simp only [tpow, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end Tpow

end EndpointsAux

/-! ### Contract theorems -/

/-- **B2** ([OAI26, §3.4, Prop. 7]), `h = 100`:
`M_{sink(ρ(w))} - M_{source(w)} = I_m` for every role `w`. -/
theorem prop7Endpoint_holds : Prop7EndpointStmt :=
  EndpointsAux.prop7Endpoint_gen 100 (by norm_num)

/-- Tensor powers are multiplicative ([OAI26, §3.5, Prop. 8]). -/
theorem tpowMul_holds : TpowMulStmt := fun k A B => EndpointsAux.tpow_mul k A B

end SubNLogN.Math.Networks
