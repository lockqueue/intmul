import SubNLogN.Math.Networks.Proofs.CCoreRole

/-!
# Naturality of the scalar rows under linear maps (Lemma A.10 (`lem:transfer-phase`) node)

`rowUpd_natural`: for every `κ`, `h`, coefficient ring `R`, `R`-modules `M`, `M'` and `R`-linear
`φ : M →ₗ[R] M'`, applying `φ` after one schedule row equals running the row on the values
`φ ∘ s`. No hypotheses beyond linearity: every row update is built from additions, scalar
multiplications, finite sums and (complex scatter) one subtraction, all of which `φ` preserves.
-/

namespace SubNLogN.Math.Networks.CCoreNode.Natural

/-- A schedule row commutes with any linear map applied to every role value. -/
theorem rowUpd_natural {κ : Kind} {h : ℕ} {R M M' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (φ : M →ₗ[R] M') (half : R) (j : Stage)
    (ι : Fix h) (op : Op) (ε : R) (s : Role κ h → M) (w : Role κ h) :
    φ (rowUpd κ half j ι op ε s w) = rowUpd κ half j ι op ε (fun w' => φ (s w')) w := by
  cases op with
  | V =>
    cases w with
    | side j' ι' p =>
      simp only [rowUpd]
      split_ifs <;> simp only [map_add, map_smul]
    | X a => rfl
    | Y a => rfl
    | center j' ι' c' => rfl
  | G =>
    cases w with
    | center j' ι' c' =>
      simp only [rowUpd]
      split_ifs
      · rw [map_add, map_smul]
        congr 2
        cases c' with
        | inl i => simp only [gatherVal, map_sum]
        | inr u => simp only [gatherVal, map_sum]
      · rfl
    | X a => rfl
    | Y a => rfl
    | side j' ι' p => rfl
  | J =>
    simp only [rowUpd]
    cases hS : tgtTriple? j ι w with
    | none => rfl
    | some S =>
      show φ (s w + ε • sideVal κ half j ι s S) =
        φ (s w) + ε • sideVal κ half j ι (fun w' => φ (s w')) S
      simp only [map_add, map_smul, sideVal, map_sum]
  | R =>
    simp only [rowUpd]
    cases hS : tgtTriple? j ι w with
    | none => rfl
    | some S =>
      show φ (s w + ε • scatterVal κ half j ι s S) =
        φ (s w) + ε • scatterVal κ half j ι (fun w' => φ (s w')) S
      cases κ with
      | bit => simp only [map_add, map_smul, scatterVal, map_sum]
      | complex => simp only [map_add, map_smul, scatterVal, map_sum, map_sub]

end SubNLogN.Math.Networks.CCoreNode.Natural
