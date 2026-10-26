import SubNLogN.Math.Networks.Cert
import SubNLogN.Math.Networks.AppCShear

/-!
# Networks: functional specification of the Lemma A.6 (`lem:transfer-shear`) specialization, and class totals for general `h`

1. **Lemma A.6 (`lem:transfer-shear`) specialized modulo `q^b`**. For factorization data that
   is valid at the prime `q` (Cert.lean: `FacData.Valid`), the address shear `(H, D) ↦ (H + A D, D)`
   modulo `Q = q^b` equals the composite of the streaming maps `D ← E₂ D`, `H ← E₁⁻¹ H`, the pivot
   triples (each with exactly one interchange), `H ← E₁ H`, `D ← E₂⁻¹ D`, all reduced mod `Q`; and the
   diagonal entries of the reduced triangular factors are units mod `Q`, so every streaming update
   is a unit multiplication plus a controlled shift. This is the functional content of
   `lem:transfer-shear` that the machine kernel realizes.
2. **Class totals for every `h ≥ 7`** (closed-form polynomial identities in `h`): the name-level checker totals are the
   closed forms `s_b(h)`, `s_c(h)` symbolically in `h` (not only at `h = 100`).
-/

namespace SubNLogN.Math.Networks

/-- CONTRACT (Lemma A.6 (`lem:transfer-shear`) specialized mod `q^b`). -/
def C4SpecializeStmt : Prop :=
  ∀ (q b : ℕ) (A : Matrix (Fin mH) (Fin mH) ℚ) (F : FacData), q.Prime → F.Valid q A →
    shearHD (A.map (ratMod (q ^ b))) =
      linD (F.E₂'.map (ratMod (q ^ b))) ∘ linH (F.E₁.map (ratMod (q ^ b))) ∘
        (F.piv.foldr (fun p g => pivotTriple p.1 p.2 ∘ g) id) ∘
        linH (F.E₁'.map (ratMod (q ^ b))) ∘ linD (F.E₂.map (ratMod (q ^ b))) ∧
    ∀ i, IsUnit (ratMod (q ^ b) (F.E₁ i i)) ∧ IsUnit (ratMod (q ^ b) (F.E₁' i i)) ∧
      IsUnit (ratMod (q ^ b) (F.E₂ i i)) ∧ IsUnit (ratMod (q ^ b) (F.E₂' i i))

/-- CONTRACT (class totals for general `h`). For every `h ≥ 7` the name-level
checker's weighted totals equal the closed forms `s_b(h) = W_b m − N + 2L_b` and
`s_c(h) = W_c m − 2N + 2L_c` (Spec.lean). (At `h = 100` this is `rank_total_bit/complex`.) -/
def TotalsGenStmt : Prop :=
  ∀ h : ℕ, 7 ≤ h → Cell.totalBit h = tripleSb h ∧ Cell.totalComplex h = tripleSc h

end SubNLogN.Math.Networks
