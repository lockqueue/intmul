import SubNLogN.Math.Bridge.Operators

/-!
# Bridge: Lemma 4.2 (`lem:bridge-A`), the triangular Poisson identity

Exact identity, no rounding. The proof uses the Poisson summation of `Kernel.lean`
(`carrier_poisson`) per axis, the mixed-radix digit congruences of Lemma 4.2 (`lem:bridge-A`), and
exchange of absolutely convergent sums. (Names `LemmaA*`/`lemmaA*` reflect an earlier draft (bridge Lemma A), kept for stability.)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-! ## Lemma 4.2 (bridge Lemma A) (`lem:bridge-A`) -/

/-- CONTRACT, Lemma 4.2 (bridge Lemma A) (`lem:bridge-A`, eq. (`eq:lemma-A`)): with `U = S_2⋯S_d x` and
`Z = F_R x`, `F_t U = A_2 A_3 ⋯ A_d Z` (operators composing from right to left; `F_t U` read in
frequency order). -/
def LemmaAStmt : Prop :=
  ∀ {d : ℕ} (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (x : Fin (totalLen t) → ℂ) (u : Idx t),
    dftTensor t (spreadAll α t (x ∘ encIn t)) u =
      Matrix.mulVec (aliasProd α t) (dft (totalLen t) x) (encFreq t u)

/-- CONTRACT, Lemma 4.2 (bridge Lemma A) explicit form (`lem:bridge-A`, eq. (`eq:lemma-A-explicit`)):
`(F_t U)_u = ∑_{m∈ℤ^{d-1}} [∏_{h≥2} G((u_h+1/2)/t_h - m_h)] Z_{(f(u) - ∑_h m_h R/A_h) mod R}`. -/
def LemmaA_explicitStmt : Prop :=
  ∀ {d : ℕ} (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (x : Fin (totalLen t) → ℂ) (u : Idx t),
    dftTensor t (spreadAll α t (x ∘ encIn t)) u =
      ∑' m : ({i : Fin d // (i : ℕ) ≠ 0} → ℤ),
        (∏ i : {i : Fin d // (i : ℕ) ≠ 0},
            (kernelG α ((((u i.1 : Fin (t i.1)) : ℕ) + 1 / 2 : ℝ) / (t i.1 : ℝ) - (m i : ℝ)) : ℂ)) *
          dft (totalLen t) x (shiftFin (encFreq t u)
            (-(∑ i : {i : Fin d // (i : ℕ) ≠ 0}, m i * (aliasStep t i.1 : ℤ))))

end SubNLogN.Math.Bridge
