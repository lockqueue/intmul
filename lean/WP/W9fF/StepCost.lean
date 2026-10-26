import WP.W9fF.StepEv
import WP.W9fF.Bound
import WP.W9f.Spec

/-!
# WP.W9fF.StepCost — widths and costs of the recurrence step blocks

With the input bounds `βstep H` (inputs `Y ≤ H`, divisor/multiplier/shift `≤ H`, zPart, zHom, `μ`,
`SS ≤ H+1`, constants `≤ 1`, everything else `≤ solW H`), the abstract interpretation of
`WP.W9fF.Bound` keeps every intermediate of a coordinate step `≤ 4H+7` bits (dividend `2H+2`,
Barrett products `≤ 4H+5`, outputs `3H+6`), all below the declared width `solW H = 8(H+1)`:
* `pStepP_cost`: one zPart step = 10 products and 24 small ops at width `solW H`;
* `pStepF_cost`: one zPart and one zHom step = 20 products and 48 small ops.
-/

namespace WP.W9fF

open TMFw TMFw.Contracts WP.W9f

/-- Input bit-length bounds of the step blocks. -/
def βstep (H : ℕ) : V → ℕ := fun v => match v with
  | .Y1 | .Y2 | .DA | .MC | .HV => H
  | .Z1 | .Z2 | .G1 | .G2 | .MU | .SS => H + 1
  | .ZERO | .ONE => 1
  | _ => solW H

theorem pStepP_cost (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) (env : V → ℤ)
    (hw : ∀ v, bitLen (env v).natAbs ≤ βstep H v) :
    pStepP.cost Op.sem (kap C Mul (solW H)) env ≤
      10 * (C * Mul (solW H) + C + 20 * solW H + 43) +
      24 * (C * (2 * solW H + 1) + 20 * solW H + 43) ∧
    ∀ v, bitLen (ev pStepP env v).natAbs ≤ solW H := by
  have hchk : sChk (orc C Mul (solW H)) (solW H) pStepP (βstep H) := by
    simp only [pStepP, pRec, pDivRB, block, op, sChk, sBnd, eChk, eRb, orc_rb, orcRb,
      Function.update_apply, reduceCtorEq, ↓reduceIte, βstep, solW]
    omega
  obtain ⟨h1, h2⟩ := sBnd_sound (orc_sound C Mul (solW H)) pStepP (βstep H) env hchk hw
  refine ⟨h2.trans ?_, fun v => (h1 v).trans ?_⟩
  · simp only [pStepP, pRec, pDivRB, block, op, sU, eU, orc_U, orcU]
    by_contra hc
    omega
  · cases v <;> simp only [pStepP, pRec, pDivRB, block, op, sBnd, eRb, orc_rb, orcRb,
      Function.update_apply, reduceCtorEq, ↓reduceIte, βstep, solW] <;> omega

theorem pStepF_cost (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) (env : V → ℤ)
    (hw : ∀ v, bitLen (env v).natAbs ≤ βstep H v) :
    pStepF.cost Op.sem (kap C Mul (solW H)) env ≤
      20 * (C * Mul (solW H) + C + 20 * solW H + 43) +
      48 * (C * (2 * solW H + 1) + 20 * solW H + 43) ∧
    ∀ v, bitLen (ev pStepF env v).natAbs ≤ solW H := by
  have hchk : sChk (orc C Mul (solW H)) (solW H) pStepF (βstep H) := by
    simp only [pStepF, pStepP, pStepH, pRec, pDivRB, block, op, sChk, sBnd, eChk, eRb, orc_rb,
      orcRb, Function.update_apply, reduceCtorEq, ↓reduceIte, βstep, solW]
    omega
  obtain ⟨h1, h2⟩ := sBnd_sound (orc_sound C Mul (solW H)) pStepF (βstep H) env hchk hw
  refine ⟨h2.trans ?_, fun v => (h1 v).trans ?_⟩
  · simp only [pStepF, pStepP, pStepH, pRec, pDivRB, block, op, sU, eU, orc_U, orcU]
    by_contra hc
    omega
  · simp only [pStepF, pStepP, pStepH, pRec, pDivRB, block, op, sBnd, eRb, orc_rb,
      orcRb, Function.update_apply, reduceCtorEq, ↓reduceIte, βstep, solW]
    cases v <;> simp only [reduceCtorEq, ↓reduceIte] <;> omega

#assert_std_axioms pStepP_cost pStepF_cost

end WP.W9fF
