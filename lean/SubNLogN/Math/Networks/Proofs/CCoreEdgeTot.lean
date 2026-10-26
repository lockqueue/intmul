import SubNLogN.Math.Networks.Proofs.CCoreEdgeCore

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations, part 3: the total matrix of an edge program is `(C_V C_U⁻¹)^{⊗f}`

For the proof of `CCoreNode.CoreEdgeRoleSpecStmt` (final theorem in `Proofs/CCoreEdge.lean`). The
edge program `coreEdgeOps` realizes (in core coordinates, `CCoreEdgeCore.lean`) the matrix
`P_M^{⊗f} · (Π_t K_{e_t}^{ε_t})^{⊗f} (time order) · P_{M'}^{⊗f}`. Here we show (`edge_total`):
* the translation kernels commute (`Kv_commute`), so the time order does not matter;
* `P_M (Π_t K_{e_t}^{ε_t}) P_{M'} = Π_{v∈B} K_v^{ε_v}` (`edgeRealization_holds`);
* `Π_{v∈B} K_v^{ε_v} = C_V C_U⁻¹` ([OAI26] Prop. 8, given as the hypothesis `hP8`; frames invertible,
  `ComplexCorollary.isUnit_det_frameC`), and tensor powers are multiplicative (`tpowMul_holds`).
Also `isONB_length_le` (an orthonormal list has at most `mH` vectors; argument of
`Proofs/CCoreWF.lean`, reproved here). Namespace `SubNLogN.Math.Networks.CCoreEdgeAux`.
-/

namespace SubNLogN.Math.Networks

namespace CCoreEdgeAux

/-! ## 10. Orthonormal lists are short -/

theorem dotC_comm' (u v : Pt 100) : dotC u v = dotC v u := by
  unfold dotC
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem dotC_sum_smul' {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) (v : ι → Pt 100) (u : Pt 100) :
    dotC (∑ i ∈ s, g i • v i) u = ∑ i ∈ s, g i * dotC (v i) u := by
  unfold dotC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

/-- An orthonormal list is linearly independent. -/
theorem isONB_linearIndependent' {E : Submodule (ZMod 2) (Pt 100)} {B : List (Pt 100)}
    (hB : IsONB E B) : LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i) := by
  obtain ⟨hnorm, hpair, -⟩ := hB
  have horth : ∀ i j : Fin B.length, i ≠ j → dotC (B.get i) (B.get j) = 0 := by
    intro i j hij
    have hp := List.pairwise_iff_getElem.1 hpair
    rcases lt_or_gt_of_ne hij with h | h
    · simpa [List.get_eq_getElem] using hp i.val j.val i.isLt j.isLt h
    · rw [dotC_comm']
      simpa [List.get_eq_getElem] using hp j.val i.val j.isLt i.isLt h
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have h := congrArg (fun x => dotC x (B.get i)) hsum
  try simp only at h
  rw [dotC_sum_smul', Finset.sum_eq_single i, hnorm _ (List.get_mem _ _), mul_one] at h
  · rw [h]
    unfold dotC
    simp
  · intro j _ hji
    rw [horth j i hji, mul_zero]
  · intro his
    exact absurd hi his

/-- An orthonormal basis of a subspace of `𝔽₂^{mH}` has at most `mH` vectors. -/
theorem isONB_length_le' {E : Submodule (ZMod 2) (Pt 100)} {B : List (Pt 100)} (hB : IsONB E B) :
    B.length ≤ mH := by
  have h := (isONB_linearIndependent' hB).fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h
  simpa [Cube] using h

/-! ## 11. Tensor powers and translation kernels -/

theorem tpow_list_prod {h : ℕ} (f : ℕ) (l : List (Matrix (Pt h) (Pt h) ℂ)) :
    tpow f l.prod = (l.map (tpow f)).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.prod_nil]
    exact ComplexCorollary.tpow_one f
  | cons a l ih => rw [List.prod_cons, tpowMul_holds, ih, List.map_cons, List.prod_cons]

theorem tpow_inv (f : ℕ) (A : Matrix (Pt 100) (Pt 100) ℂ) (hA : IsUnit A.det) :
    (tpow f A)⁻¹ = tpow f A⁻¹ :=
  Matrix.inv_eq_right_inv (by
    rw [← tpowMul_holds, Matrix.mul_nonsing_inv A hA, ComplexCorollary.tpow_one])

theorem Xv_mul (u v : Pt 100) : Xv u * Xv v = Xv (u + v) := by
  ext x y
  simp only [Matrix.mul_apply, Xv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, add_assoc]

/-- Translation kernels commute. -/
theorem Kv_commute (u v : Pt 100) (ε ε' : ℤ) : Commute (Kv u ε) (Kv v ε') := by
  have hX : Commute (Xv u) (Xv v) := by
    show Xv u * Xv v = Xv v * Xv u
    rw [Xv_mul, Xv_mul, add_comm]
  have key : ∀ a b c d : ℂ, Commute (a • (1 : Matrix (Pt 100) (Pt 100) ℂ) + b • Xv u)
      (c • (1 : Matrix (Pt 100) (Pt 100) ℂ) + d • Xv v) := by
    intro a b c d
    refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
    · exact ((Commute.refl 1).smul_left a).smul_right c
    · exact ((Commute.one_left (Xv v)).smul_left a).smul_right d
    · exact ((Commute.one_right (Xv u)).smul_left b).smul_right c
    · exact (hX.smul_left b).smul_right d
  unfold Kv
  split_ifs <;> apply key

theorem list_prod_reverse_of_commute {M : Type*} [Monoid M] (l : List M)
    (h : ∀ a ∈ l, ∀ b ∈ l, Commute a b) : l.reverse.prod = l.prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, List.prod_append, List.prod_singleton, List.prod_cons,
      ih (fun x hx y hy => h x (by simp [hx]) y (by simp [hy]))]
    exact (Commute.list_prod_right l a (fun x hx => h a (by simp) x (by simp [hx]))).eq.symm

/-- `list_prod_reverse_of_commute` for matrices on `Pt h` (stated for a general `h`, so that the
instances are unified at a variable `h`, not at `h = 100`). -/
theorem mat_prod_reverse {h : ℕ} (l : List (Matrix (Pt h) (Pt h) ℂ))
    (hc : ∀ a ∈ l, ∀ b ∈ l, Commute a b) : l.reverse.prod = l.prod :=
  list_prod_reverse_of_commute l hc

/-- **Total matrix of an edge program**: `P_M^{⊗f} (Π_t K_{e_t}^{ε_t})^{⊗f} P_{M'}^{⊗f}` (kernels in
time order) equals `C_V^{⊗f} (C_U^{⊗f})⁻¹`, for an extension `M` of the residual basis `B` whose
kernel product gives the frame step (`hP8`, [OAI26] Prop. 8). -/
theorem edge_total (e : Vertex .complex 100 × Vertex .complex 100) (B : List (Pt 100))
    (hlen : B.length ≤ mH)
    (hP8 : frameC e.2 = (B.map fun v => Kv v (epsC e v)).prod * frameC e.1)
    (M M' : Matrix (Cube 100) (Cube 100) (ZMod 2)) (hMM' : M * M' = 1)
    (hcol : ∀ (t : ℕ) (ht : t < B.length) (htm : t < mH), ∀ p,
      M p (cubeEquiv.symm ⟨t, htm⟩) = B.get ⟨t, ht⟩ p) (f : ℕ) :
    tpow f (permOp M) * ((((List.range B.length).zip (B.map (epsC e))).map
        (fun p => tpow f (Kv (Pi.single (slotCoord p.1) 1) p.2))).reverse.prod *
      tpow f (permOp M')) =
      tpow f (frameC e.2) * (tpow f (frameC e.1))⁻¹ := by
  obtain ⟨L, hL⟩ : ∃ L : List (Matrix (Pt 100) (Pt 100) ℂ),
      L = ((List.range B.length).zip (B.map (epsC e))).map
        (fun p => Kv (Pi.single (slotCoord p.1) 1) p.2) := ⟨_, rfl⟩
  have hmap : (((List.range B.length).zip (B.map (epsC e))).map
      (fun p => tpow f (Kv (Pi.single (slotCoord p.1) 1) p.2))) = L.map (tpow f) := by
    rw [hL, List.map_map]
    rfl
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, Commute a b := by
    intro a ha b hb
    rw [hL, List.mem_map] at ha hb
    obtain ⟨p, -, rfl⟩ := ha
    obtain ⟨q, -, rfl⟩ := hb
    exact Kv_commute _ _ _ _
  have hrev : (L.map (tpow f)).reverse.prod = tpow f L.prod := by
    rw [← List.map_reverse, ← tpow_list_prod, mat_prod_reverse L hcomm]
  obtain ⟨cs, hcs⟩ : ∃ cs : List (Cube 100), cs = (List.range B.length).map slotCoord := ⟨_, rfl⟩
  have hLcs : L = (B.zip cs).map fun p => Kv (Pi.single p.2 1) (epsC e p.1) := by
    rw [hL, hcs]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  have hER := edgeRealization_holds 100 B (epsC e) M M' cs hMM' (by rw [hcs]; simp) (by
    intro i hi hc
    have him : i < mH := lt_of_lt_of_le hi hlen
    funext p
    rw [EdgeRealAux.mulVec_single_one_apply]
    have hci : cs.get ⟨i, hc⟩ = cubeEquiv.symm ⟨i, him⟩ := by
      subst hcs
      simp [slotCoord_of_lt him]
    rw [hci, hcol i hi him p])
  have hU := ComplexCorollary.isUnit_det_frameC e.1
  have hprod : (B.map fun v => Kv v (epsC e v)).prod = frameC e.2 * (frameC e.1)⁻¹ := by
    rw [hP8, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]
  rw [hmap, hrev, ← tpowMul_holds, ← tpowMul_holds, ← Matrix.mul_assoc, hLcs, ← hER, hprod,
    tpowMul_holds, tpow_inv f _ hU]

end CCoreEdgeAux

end SubNLogN.Math.Networks
