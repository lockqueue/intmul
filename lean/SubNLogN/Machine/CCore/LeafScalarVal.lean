/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarDefs

/-!
# C-core scalar row: value math (`CCore/LeafScalarVal.lean`)

The scalar row `gateFn j ι r` of the C-core (`CCore/SkelDefs.lean`, `rowUpd` read through
`roleIdxN`) is a sparse linear update: every role `w` is changed to
`w + Σ_{(c, w') ∈ rowTerms j ι r w} c • w'`, where the list of terms is empty unless `w` is a
target of the row. With `ε = rowSign j r ∈ {±1}`:
* `V` (copy): side wire `A_{ST}` ← `+ ε x_T`;
* `G` (gather): central wire `C_i` ← `+ ε Σ_{T ∋ i} x_T`, `C_*` ← `+ ε Σ_T x_T`;
* `J` (side injection): target `y_S` ← `+ Σ_{T nbr S} ε·coefJ(S,T) A_{ST}` (`coefJ = ±1/2`);
* `R` (scatter): target `y_S` ← `+ Σ_{i ∈ S} (ε/2) C_i − (ε/2) C_*`.
Proved (helpers in `ScalarValAux`): the decomposition over `ℂ` (`rowUpdOp_eq_terms`), its version
with coefficients in `LeafScalarAux.Coef = {±1, ±1/2}` (`rowTermsOpC_val`), and sources are never
targets (`rowTermsOpC_source`, `rowTermsN_source`); on role indices `Fin Wn` this gives
`gateFn_eq_terms`, and `scalarRowVal_holds : LeafScalarAux.ScalarRowValStmt` with witness
`ScalarValAux.rowTermsN`. The term lists are built from `Finset.toList` (noncomputable; never
enumerated). `W = Wn` is never computed.
-/

namespace SubNLogN.Machine.CCore

open SubNLogN.Math.Networks

namespace ScalarValAux

/-- The sign `ε` of row `(j, r)` as a complex number. -/
noncomputable def epsC (j : Stage) (r : Fin 8) : ℂ := ((rowSign j r : ℤ) : ℂ)

/-- Gather terms of a central wire. -/
noncomputable def gatherTerms (j : Stage) (ι : Fix 100) (ε : ℂ) :
    Center .complex 100 → List (ℂ × Role .complex 100)
  | .inl i => (Finset.univ.filter (fun T : Tri 100 => i ∈ T.1)).toList.map
      (fun T => (ε, srcRole j ι T))
  | .inr _ => (Finset.univ : Finset (Tri 100)).toList.map (fun T => (ε, srcRole j ι T))

/-- Side-injection terms of a target `y_S`. -/
noncomputable def sideTerms (j : Stage) (ι : Fix 100) (ε : ℂ) (S : Tri 100) :
    List (ℂ × Role .complex 100) :=
  (Finset.univ : Finset {T : Tri 100 // Nbr .complex S T}).toList.map
    (fun T => (ε * coefJ .complex (2⁻¹ : ℂ) S T.1, Role.side j ι ⟨(S, T.1), T.2⟩))

/-- Scatter terms of a target `y_S`. -/
noncomputable def scatterTerms (j : Stage) (ι : Fix 100) (ε : ℂ) (S : Tri 100) :
    List (ℂ × Role .complex 100) :=
  S.1.toList.map (fun i => (ε * 2⁻¹, Role.center j ι (.inl i))) ++
    [(-(ε * 2⁻¹), Role.center (κ := .complex) j ι (.inr ()))]

/-- The terms of row `(j, ι, r)` at target role `w` (empty if `w` is not a target). -/
noncomputable def rowTermsOp (j : Stage) (ι : Fix 100) (ε : ℂ) :
    Op → Role .complex 100 → List (ℂ × Role .complex 100)
  | .V, .side j' ι' p => if j' = j ∧ ι' = ι then [(ε, srcRole j ι p.1.2)] else []
  | .G, .center j' ι' c => if j' = j ∧ ι' = ι then gatherTerms j ι ε c else []
  | .J, w => match tgtTriple? j ι w with
      | some S => sideTerms j ι ε S
      | none => []
  | .R, w => match tgtTriple? j ι w with
      | some S => scatterTerms j ι ε S
      | none => []
  | _, _ => []

/-- The decomposition at the role level, for any operation and sign, in any `ℂ`-module. -/
theorem rowUpdOp_eq_terms (j : Stage) (ι : Fix 100) (op : Op) (ε : ℂ) {M : Type*}
    [AddCommGroup M] [Module ℂ M] (s : Role .complex 100 → M) (w : Role .complex 100) :
    rowUpd .complex (2⁻¹ : ℂ) j ι op ε s w =
      s w + ((rowTermsOp j ι ε op w).map (fun p => p.1 • s p.2)).sum := by
  cases op with
  | V =>
    cases w with
    | side j' ι' p =>
      simp only [rowUpd, rowTermsOp]
      split_ifs <;> simp
    | X a => simp [rowUpd, rowTermsOp]
    | Y a => simp [rowUpd, rowTermsOp]
    | center j' ι' c => simp [rowUpd, rowTermsOp]
  | G =>
    cases w with
    | center j' ι' c =>
      simp only [rowUpd, rowTermsOp]
      split_ifs
      · cases c with
        | inl i =>
          simp [gatherTerms, gatherVal, Finset.smul_sum]
        | inr u =>
          simp [gatherTerms, gatherVal, Finset.smul_sum]
      · simp
    | X a => simp [rowUpd, rowTermsOp]
    | Y a => simp [rowUpd, rowTermsOp]
    | side j' ι' p => simp [rowUpd, rowTermsOp]
  | J =>
    simp only [rowUpd, rowTermsOp]
    cases tgtTriple? j ι w with
    | none => simp
    | some S =>
      simp [sideTerms, sideVal, Finset.smul_sum, smul_smul]
  | R =>
    simp only [rowUpd, rowTermsOp]
    cases tgtTriple? j ι w with
    | none => simp
    | some S =>
      simp only [scatterTerms, scatterVal, List.map_append, List.map_map, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [Function.comp_def, Finset.sum_map_toList, smul_sub, Finset.smul_sum, smul_sub,
        Finset.smul_sum]
      simp only [smul_smul, neg_smul, sub_eq_add_neg]

/-! ### Coefficients as `LeafScalarAux.Coef` -/

open LeafScalarAux

/-- `±1` as a coefficient. -/
def sgnCoef (pos : Bool) : Coef := if pos then .pos else .neg

/-- `±1/2` as a coefficient. -/
def halfCoef (pos : Bool) : Coef := if pos then .halfPos else .halfNeg

/-- The real sign `±1` of a Boolean. -/
noncomputable def sgnC (pos : Bool) : ℂ := if pos then 1 else -1

theorem sgnCoef_val (pos : Bool) : (sgnCoef pos).val = sgnC pos := by
  cases pos <;> rfl

theorem halfCoef_val (pos : Bool) : (halfCoef pos).val = sgnC pos * 2⁻¹ := by
  cases pos <;> simp [halfCoef, Coef.val, sgnC]

theorem sgnC_not (pos : Bool) : sgnC (!pos) = -sgnC pos := by
  cases pos <;> simp [sgnC]

theorem halfCoef_not_val (pos : Bool) : (halfCoef (!pos)).val = -(sgnC pos * 2⁻¹) := by
  cases pos <;> simp [halfCoef, Coef.val, sgnC]

theorem halfCoef_J_val (pos : Bool) (S T : Tri 100) :
    (halfCoef (pos == decide (inter S T = 0))).val = sgnC pos * coefJ .complex (2⁻¹ : ℂ) S T := by
  by_cases h : inter S T = 0 <;> cases pos <;> simp [halfCoef, Coef.val, sgnC, coefJ, h]

/-- Gather terms with `Coef` coefficients. -/
noncomputable def gatherTermsC (j : Stage) (ι : Fix 100) (pos : Bool) :
    Center .complex 100 → List (Coef × Role .complex 100)
  | .inl i => (Finset.univ.filter (fun T : Tri 100 => i ∈ T.1)).toList.map
      (fun T => (sgnCoef pos, srcRole j ι T))
  | .inr _ => (Finset.univ : Finset (Tri 100)).toList.map (fun T => (sgnCoef pos, srcRole j ι T))

/-- Side-injection terms with `Coef` coefficients. -/
noncomputable def sideTermsC (j : Stage) (ι : Fix 100) (pos : Bool) (S : Tri 100) :
    List (Coef × Role .complex 100) :=
  (Finset.univ : Finset {T : Tri 100 // Nbr .complex S T}).toList.map
    (fun T => (halfCoef (pos == decide (inter S T.1 = 0)), Role.side j ι ⟨(S, T.1), T.2⟩))

/-- Scatter terms with `Coef` coefficients. -/
noncomputable def scatterTermsC (j : Stage) (ι : Fix 100) (pos : Bool) (S : Tri 100) :
    List (Coef × Role .complex 100) :=
  S.1.toList.map (fun i => (halfCoef pos, Role.center j ι (.inl i))) ++
    [(halfCoef (!pos), Role.center (κ := .complex) j ι (.inr ()))]

/-- Row terms with `Coef` coefficients (`pos` encodes the sign of the row). -/
noncomputable def rowTermsOpC (j : Stage) (ι : Fix 100) (pos : Bool) :
    Op → Role .complex 100 → List (Coef × Role .complex 100)
  | .V, .side j' ι' p => if j' = j ∧ ι' = ι then [(sgnCoef pos, srcRole j ι p.1.2)] else []
  | .G, .center j' ι' c => if j' = j ∧ ι' = ι then gatherTermsC j ι pos c else []
  | .J, w => match tgtTriple? j ι w with
      | some S => sideTermsC j ι pos S
      | none => []
  | .R, w => match tgtTriple? j ι w with
      | some S => scatterTermsC j ι pos S
      | none => []
  | _, _ => []

/-- The `Coef` terms evaluate to the complex terms. -/
theorem rowTermsOpC_val (j : Stage) (ι : Fix 100) (pos : Bool) (op : Op) (w : Role .complex 100) :
    (rowTermsOpC j ι pos op w).map (fun p => (p.1.val, p.2)) = rowTermsOp j ι (sgnC pos) op w := by
  cases op with
  | V =>
    cases w <;> simp only [rowTermsOpC, rowTermsOp] <;> try split_ifs
    all_goals simp [sgnCoef_val]
  | G =>
    cases w with
    | center j' ι' c =>
      simp only [rowTermsOpC, rowTermsOp]
      split_ifs
      · cases c <;> simp [gatherTermsC, gatherTerms, sgnCoef_val]
      · rfl
    | X a => rfl
    | Y a => rfl
    | side j' ι' p => rfl
  | J =>
    simp only [rowTermsOpC, rowTermsOp]
    cases tgtTriple? j ι w with
    | none => rfl
    | some S => simp [sideTermsC, sideTerms, halfCoef_J_val]
  | R =>
    simp only [rowTermsOpC, rowTermsOp]
    cases tgtTriple? j ι w with
    | none => rfl
    | some S => simp [scatterTermsC, scatterTerms, halfCoef_val, sgnC_not, neg_mul]

/-- Sources of terms are never targets. -/
theorem rowTermsOpC_source (j : Stage) (ι : Fix 100) (pos : Bool) (op : Op)
    (w : Role .complex 100) (p : Coef × Role .complex 100) (hp : p ∈ rowTermsOpC j ι pos op w) :
    rowTermsOpC j ι pos op p.2 = [] := by
  have hsrc : ∀ (op' : Op) (T : Tri 100), op' = .V ∨ op' = .G →
      rowTermsOpC j ι pos op' (srcRole j ι T) = [] := by
    intro op' T hop
    unfold srcRole
    rcases hop with rfl | rfl <;> split_ifs <;> rfl
  cases op with
  | V =>
    cases w with
    | side j' ι' q =>
      simp only [rowTermsOpC] at hp
      split_ifs at hp
      · simp only [List.mem_singleton] at hp
        subst hp
        exact hsrc .V _ (Or.inl rfl)
      · simp at hp
    | X a => simp [rowTermsOpC] at hp
    | Y a => simp [rowTermsOpC] at hp
    | center j' ι' c => simp [rowTermsOpC] at hp
  | G =>
    cases w with
    | center j' ι' c =>
      simp only [rowTermsOpC] at hp
      split_ifs at hp
      · cases c with
        | inl i =>
          simp only [gatherTermsC, List.mem_map] at hp
          obtain ⟨T, -, rfl⟩ := hp
          exact hsrc .G _ (Or.inr rfl)
        | inr u =>
          simp only [gatherTermsC, List.mem_map] at hp
          obtain ⟨T, -, rfl⟩ := hp
          exact hsrc .G _ (Or.inr rfl)
      · simp at hp
    | X a => simp [rowTermsOpC] at hp
    | Y a => simp [rowTermsOpC] at hp
    | side j' ι' q => simp [rowTermsOpC] at hp
  | J =>
    simp only [rowTermsOpC] at hp
    cases h : tgtTriple? j ι w with
    | none => rw [h] at hp; simp at hp
    | some S =>
      rw [h] at hp
      simp only [sideTermsC, List.mem_map] at hp
      obtain ⟨T, -, rfl⟩ := hp
      rfl
  | R =>
    simp only [rowTermsOpC] at hp
    cases h : tgtTriple? j ι w with
    | none => rw [h] at hp; simp at hp
    | some S =>
      rw [h] at hp
      simp only [scatterTermsC, List.mem_append, List.mem_map, List.mem_singleton] at hp
      rcases hp with ⟨i, -, rfl⟩ | rfl <;> rfl

/-- `rowSign j r = ±1`. -/
theorem rowSign_cases (j : Stage) (r : Fin 8) : rowSign j r = 1 ∨ rowSign j r = -1 := by
  revert j r
  decide

/-- The row sign as `sgnC` of a Boolean. -/
theorem rowSign_eq_sgnC (j : Stage) (r : Fin 8) :
    ((rowSign j r : ℤ) : ℂ) = sgnC (decide (rowSign j r = 1)) := by
  rcases rowSign_cases j r with h | h <;> simp [sgnC, h]

/-- The term function at the role level for row `(j, ι, r)`. -/
noncomputable def rowTermsRole (j : Stage) (ι : Fix 100) (r : Fin 8) (w : Role .complex 100) :
    List (Coef × Role .complex 100) :=
  rowTermsOpC j ι (decide (rowSign j r = 1)) (rowOp j r) w

/-- The term function on role indices `Fin Wn`. -/
noncomputable def rowTermsN (j : Stage) (ι : Fix 100) (r : Fin 8) (idx : Fin Wn) :
    List (Coef × Fin Wn) :=
  (rowTermsRole j ι r (roleIdxN.symm idx)).map (fun p => (p.1, roleIdxN p.2))

theorem rowTermsN_source (j : Stage) (ι : Fix 100) (r : Fin 8) (idx : Fin Wn) (c : Coef)
    (s : Fin Wn) (h : (c, s) ∈ rowTermsN j ι r idx) : rowTermsN j ι r s = [] := by
  simp only [rowTermsN, List.mem_map] at h
  obtain ⟨p, hp, hps⟩ := h
  have hs : s = roleIdxN p.2 := (congrArg Prod.snd hps).symm
  subst hs
  simp only [rowTermsN, Equiv.symm_apply_apply, rowTermsRole]
  rw [rowTermsOpC_source j ι _ _ _ p hp, List.map_nil]

theorem gateFn_eq_terms (j : Stage) (ι : Fix 100) (r : Fin 8) (rr : ℕ)
    (vals : Fin Wn → Fin rr → ℂ) (idx : Fin Wn) :
    gateFn j ι r vals idx =
      vals idx + ((rowTermsN j ι r idx).map fun p => p.1.val • vals p.2).sum := by
  unfold gateFn
  rw [rowUpdOp_eq_terms, rowSign_eq_sgnC, ← rowTermsOpC_val]
  simp only [rowTermsN, rowTermsRole, List.map_map, Equiv.apply_symm_apply]
  rfl

end ScalarValAux

/-- **Scalar row value math**: the static term description of every scalar row of the C-core
(`LeafScalarAux.ScalarRowValStmt`). -/
theorem scalarRowVal_holds : LeafScalarAux.ScalarRowValStmt :=
  ⟨ScalarValAux.rowTermsN, ScalarValAux.rowTermsN_source, ScalarValAux.gateFn_eq_terms⟩


end SubNLogN.Machine.CCore
