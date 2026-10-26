import SubNLogN.Math.Bridge.LemmaA
import SubNLogN.Math.Bridge.LemmaB_Scalar

/-!
# Bridge: Lemma 4.4 (`lem:bridge-B`), operator parts

The norms of `A_h`, `B_h`, the inverse of the cyclic bidiagonal operator, and the product
bound with the total alias error (eq. (`eq:lemma-B-total`), using Lemma 4.2 (`lem:bridge-A`)). (Names `LemmaB*`/`lemmaB*` reflect an earlier draft (bridge Lemma B), kept for stability.)
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(i) (`lem:bridge-B`): `‖A_h‖_∞ ≤ 1` and `‖B_h‖_∞ ≤ 1` (paper axis
`h = i+1 ≥ 2`). -/
def LemmaB_iStmt : Prop :=
  ∀ {d : ℕ} (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (i : Fin d) (_hi : (i : ℕ) ≠ 0),
    opNormInf (Matrix.toLin' (aliasMatrix α t i)) ≤ 1 ∧
      opNormInf (Matrix.toLin' (truncMatrix α t i)) ≤ 1

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(ii) (`lem:bridge-B`): omitted aliases, `‖A_h - B_h‖_∞ < 0.120·2^{-ω}`. -/
def LemmaB_iiStmt : Prop :=
  ∀ {d : ℕ} (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (i : Fin d) (_hi : (i : ℕ) ≠ 0),
    opNormInf (Matrix.toLin' (aliasMatrix α t i - truncMatrix α t i)) <
      0.120 * (2 : ℝ) ^ (-(ω : ℤ))

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(v) (`lem:bridge-B`): on a cycle of every length `L ≥ 1` the operator
`Z_j ↦ c_0 Z_j + c_1 Z_{j-1}` is invertible with `‖B^{-1}‖_∞ ≤ 1/|c_0 - c_1| ≤ 4t/7`, the first
inequality being an equality for even `L`. -/
def LemmaB_vStmt : Prop :=
  ∀ (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : ℕ) (_ht : 2 ≤ t ∧ ∃ a : ℕ, t = 2 ^ a) (u : ℕ) (_hu : u < t) (L : ℕ) (_hL : 1 ≤ L),
    let c0 := kernelG α ((u + 1 / 2) / t)
    let c1 := kernelG α ((u + 1 / 2) / t - 1)
    IsUnit (cycBidiag (c0 : ℂ) (c1 : ℂ) L).det ∧
      opNormInf (Matrix.toLin' (cycBidiag (c0 : ℂ) (c1 : ℂ) L)⁻¹) ≤ 1 / |c0 - c1| ∧
      1 / |c0 - c1| ≤ 4 * (t : ℝ) / 7 ∧
      (Even L → opNormInf (Matrix.toLin' (cycBidiag (c0 : ℂ) (c1 : ℂ) L)⁻¹) = 1 / |c0 - c1|)

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(v) consequence (`lem:bridge-B`): `B_h` is invertible and
`‖B_h^{-1}‖_∞ ≤ 4t_h/7 ≤ t_h`. -/
def LemmaB_v_axisStmt : Prop :=
  ∀ {d : ℕ} (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (i : Fin d) (_hi : (i : ℕ) ≠ 0),
    IsUnit (truncMatrix α t i).det ∧
      opNormInf (Matrix.toLin' (truncMatrix α t i)⁻¹) ≤ 4 * (t i : ℝ) / 7 ∧
      4 * (t i : ℝ) / 7 ≤ t i

/-- CONTRACT, Lemma 4.4 (bridge Lemma B)(vi) (`lem:bridge-B`, eq. (`eq:lemma-B-total`)): `‖(B_2⋯B_d)^{-1}‖_∞ ≤ (4/7)^{d-1} R/t_1 ≤ R/t_1`,
and for `Y = F_t U`, `‖(B_2⋯B_d)^{-1} Y - F_R x‖_∞ ≤ 0.120 (d-1) (R/t_1) 2^{-ω} ‖x‖_∞`. Here
`R/t_1 = ∏_{h≥2} t_h` and `Y` is read in frequency order. -/
def LemmaB_viStmt : Prop :=
  ∀ {d : ℕ} (ω : ℕ) (_hω : 8 ≤ ω) (α : ℝ) (_hα : AlphaAdmissible ω α) (t : Fin d → ℕ) (_ht : ShapeOK t) (hd : 1 ≤ d) (x : Fin (totalLen t) → ℂ),
    opNormInf (Matrix.toLin' (truncProd α t)⁻¹) ≤
        (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) ∧
      (4 / 7 : ℝ) ^ (d - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) ≤
        (totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ) ∧
      ‖Matrix.mulVec (truncProd α t)⁻¹
            (fun f => dftTensor t (spreadAll α t (x ∘ encIn t)) ((encFreq t).symm f)) -
          dft (totalLen t) x‖ ≤
        0.120 * ((d : ℝ) - 1) * ((totalLen t : ℝ) / (t ⟨0, hd⟩ : ℝ)) * (2 : ℝ) ^ (-(ω : ℤ)) * ‖x‖

end SubNLogN.Math.Bridge
