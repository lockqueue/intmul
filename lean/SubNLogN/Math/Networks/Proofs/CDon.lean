import SubNLogN.Math.Networks.AppCFun3

/-!
# Layer assembly for Proposition A.11: `C` on groups of selected bits

Proof of `CDonStmt` (`AppCFun3.lean`; Proposition A.11 (`prop:prop14-param`),
Appendix A.6 (`sec:transfer-layer`), eq. (`eq:oai-h0-transfer`)): `CDon S` applies `C = aI + bX` (`a = (1+i)/2`, `b = (1−i)/2`) on the
selected bits in `S` and the identity on the others. We prove
1. `CDon univ = CD D` (`C^{⊗D}`);
2. `CDon ∅ = id`;
3. `CDon S ∘ CDon T = CDon (S ∪ T)` for disjoint `S`, `T`;
4. on one bit, `CDon {j}` is the individual kernel
   `C(u,v) = ((u+v+i(u−v))/2, (u+v−i(u−v))/2)`.

## Plan
* The kernel of `CDon S` factorizes over coordinates: with `kS S j x y = C(x,y)` for `j ∈ S` and
  `[x = y]` for `j ∉ S`, the kernel is `∏_j kS S j (e j) (e' j)` (`kernel_eq_prod`).
* (3): exchange the two sums, merge the products (`Finset.prod_mul_distrib`) and write the sum over
  the intermediate index `e'' : Fin D → Bool` of a product as the product of per-coordinate sums
  over `Bool` (`Fintype.prod_sum`); per coordinate, `Σ_b kS S j x b · kS T j b y = kS (S∪T) j x y`
  because at most one of `S`, `T` contains `j` and the other factor is an indicator.
* (4): only `e' = e[j↦false]` and `e' = e[j↦true]` contribute (`Fintype.sum_eq_add`).

Helper declarations live in the namespace `SubNLogN.Math.Networks.CDonAux`; the main theorem
`cdon_holds` is in `SubNLogN.Math.Networks`.
-/

namespace SubNLogN.Math.Networks

namespace CDonAux

/-- The one-bit kernel `C(x, y)`: `a` on the diagonal, `b` off it. -/
noncomputable def kc (x y : Bool) : ℂ := if x = y then ka else kb

/-- Per-coordinate kernel of `CDon S`: `C(x,y)` on the bits of `S`, the indicator `[x = y]`
elsewhere. -/
noncomputable def kS {D : ℕ} (S : Finset (Fin D)) (j : Fin D) (x y : Bool) : ℂ :=
  if j ∈ S then kc x y else if x = y then 1 else 0

/-- The kernel of `CDon S` is the product over coordinates of the per-coordinate kernels. -/
lemma kernel_eq_prod {D : ℕ} (S : Finset (Fin D)) (e e' : Fin D → Bool) :
    (if ∀ j, j ∉ S → e j = e' j then ∏ j ∈ S, (if e j = e' j then ka else kb) else 0) =
      ∏ j, kS S j (e j) (e' j) := by
  by_cases h : ∀ j, j ∉ S → e j = e' j
  · rw [if_pos h]
    have hsub : ∏ j ∈ S, kS S j (e j) (e' j) = ∏ j, kS S j (e j) (e' j) :=
      Finset.prod_subset (Finset.subset_univ S) (fun j _ hj => by simp [kS, hj, h j hj])
    rw [← hsub]
    exact Finset.prod_congr rfl fun j hj => by simp [kS, kc, hj]
  · rw [if_neg h]
    push Not at h
    obtain ⟨j, hjS, hj⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [kS, hjS, hj])

/-- `CDon` in product form. -/
lemma cdon_eq_prod {D : ℕ} (S : Finset (Fin D)) (z : (Fin D → Bool) → ℂ) (e : Fin D → Bool) :
    CDon S z e = ∑ e' : Fin D → Bool, (∏ j, kS S j (e j) (e' j)) * z e' := by
  simp only [CDon, kernel_eq_prod]

/-- Per-coordinate composition for disjoint `S`, `T`. -/
lemma sum_kS_mul_kS {D : ℕ} {S T : Finset (Fin D)} (hST : Disjoint S T) (j : Fin D)
    (x y : Bool) : ∑ b : Bool, kS S j x b * kS T j b y = kS (S ∪ T) j x y := by
  by_cases hS : j ∈ S
  · have hT : j ∉ T := Finset.disjoint_left.mp hST hS
    cases x <;> cases y <;> simp [kS, kc, hS, hT]
  · by_cases hT : j ∈ T
    · cases x <;> cases y <;> simp [kS, kc, hS, hT]
    · cases x <;> cases y <;> simp [kS, hS, hT]

/-- (1) `CDon univ = C^{⊗D}`. -/
theorem cdon_univ (D : ℕ) (z : (Fin D → Bool) → ℂ) : CDon Finset.univ z = CD D z := by
  funext e
  simp [CDon, CD]

/-- (2) `CDon ∅ = id`. -/
theorem cdon_empty (D : ℕ) (z : (Fin D → Bool) → ℂ) : CDon (∅ : Finset (Fin D)) z = z := by
  funext e
  simp only [CDon]
  rw [Fintype.sum_eq_single e]
  · simp
  · intro e' he'
    have hc : ¬ ∀ j, j ∉ (∅ : Finset (Fin D)) → e j = e' j := fun hc =>
      he' (funext fun j => (hc j (Finset.notMem_empty j)).symm)
    rw [if_neg hc, zero_mul]

/-- (3) `CDon S ∘ CDon T = CDon (S ∪ T)` for disjoint `S`, `T`. -/
theorem cdon_union (D : ℕ) (S T : Finset (Fin D)) (z : (Fin D → Bool) → ℂ)
    (hST : Disjoint S T) : CDon S (CDon T z) = CDon (S ∪ T) z := by
  funext e
  simp only [cdon_eq_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => ?_
  simp only [← mul_assoc, ← Finset.sum_mul, ← Finset.prod_mul_distrib]
  congr 1
  rw [show (∑ e'' : Fin D → Bool, ∏ j, kS S j (e j) (e'' j) * kS T j (e'' j) (e' j)) =
      ∏ j, ∑ b : Bool, kS S j (e j) b * kS T j b (e' j) from
    (Fintype.prod_sum (fun j (b : Bool) => kS S j (e j) b * kS T j b (e' j))).symm]
  exact Finset.prod_congr rfl fun j _ => sum_kS_mul_kS hST j (e j) (e' j)

/-- (4) On one bit, `CDon {j}` is the individual kernel
`C(u,v) = ((u+v+i(u−v))/2, (u+v−i(u−v))/2)`. -/
theorem cdon_single (D : ℕ) (j : Fin D) (z : (Fin D → Bool) → ℂ) (e : Fin D → Bool) :
    CDon {j} z e =
      let u := z (Function.update e j false)
      let v := z (Function.update e j true)
      if e j = false then (u + v + Complex.I * (u - v)) / 2
      else (u + v - Complex.I * (u - v)) / 2 := by
  have hne : Function.update e j false ≠ Function.update e j true := by
    intro hab
    have := congrFun hab j
    simp at this
  have hcond : ∀ b : Bool, ∀ i, i ∉ ({j} : Finset (Fin D)) → e i = Function.update e j b i := by
    intro b i hi
    rw [Function.update_of_ne (by simpa using hi)]
  simp only [CDon]
  rw [Fintype.sum_eq_add _ _ hne]
  · rw [if_pos (hcond false), if_pos (hcond true), Finset.prod_singleton, Finset.prod_singleton,
      Function.update_self, Function.update_self]
    cases e j <;> simp [ka, kb] <;> ring
  · rintro x ⟨hxa, hxb⟩
    rw [if_neg, zero_mul]
    intro hx
    have hx' : x = Function.update e j (x j) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · rw [Function.update_of_ne hi]; exact (hx i (by simpa using hi)).symm
    cases hxj : x j
    · exact hxa (hx'.trans (by rw [hxj]))
    · exact hxb (hx'.trans (by rw [hxj]))

end CDonAux

open CDonAux in
/-- **Layer assembly** (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`), eq. (`eq:oai-h0-transfer`)): `CDonStmt` —
`CDon univ = C^{⊗D}`, `CDon ∅ = id`, `CDon S ∘ CDon T = CDon (S ∪ T)` for disjoint `S`, `T`, and
`CDon {j}` is the individual kernel `C(u,v)`. Unconditional (no hypotheses). -/
theorem cdon_holds : CDonStmt :=
  ⟨cdon_univ, cdon_empty, cdon_union, cdon_single⟩

end SubNLogN.Math.Networks
