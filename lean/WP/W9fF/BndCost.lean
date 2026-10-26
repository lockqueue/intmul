import WP.W9fF.Bnd
import WP.W9fF.Comb
import WP.W9fF.Bound
import WP.W9f.Spec

/-!
# WP.W9fF.BndCost — widths and costs of the boundary and combine blocks

By the abstract interpretation of `WP.W9fF.Bound` (`sBnd_sound` with `orc_sound` at the declared
product width `W = solW H = 8(H+1)`):
* `pBnd_cost`: from inputs `Y0 ≤ H`, `zPart, zHom ≤ H+1`, `a, c ≤ H`, `SS ≤ H+1` bits, every
  intermediate stays `≤ 5H+7` bits, and the cost is at most 15 products, 2 rounded divisions and
  6 additions at width `W`;
* `pComb_cost`: from `zPart, zHom, SS ≤ H+1`, `Z0, HALF, S2 ≤ H`, every intermediate stays
  `≤ 2H+4` bits; 6 products and 8 small ops (6 additions, 2 shifts).
-/

namespace WP.W9fF

open TMFw TMFw.Contracts WP.W9f

/-- Input bit-length bounds of `pBnd`. -/
def βBnd (H : ℕ) : V → ℕ := fun v => match v with
  | .Y01 | .Y02 | .MC | .DA => H
  | .Z1 | .Z2 | .G1 | .G2 | .SS => H + 1
  | _ => solW H

/-- Input bit-length bounds of `pComb`. -/
def βComb (H : ℕ) : V → ℕ := fun v => match v with
  | .W1 | .W2 | .HALF | .S2 => H
  | .Z1 | .Z2 | .G1 | .G2 | .SS => H + 1
  | _ => solW H

theorem pBnd_cost (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) (env : V → ℤ)
    (hall : ∀ v, bitLen (env v).natAbs ≤ solW H)
    (hY1 : bitLen (env .Y01).natAbs ≤ H) (hY2 : bitLen (env .Y02).natAbs ≤ H)
    (hZ1 : bitLen (env .Z1).natAbs ≤ H + 1) (hZ2 : bitLen (env .Z2).natAbs ≤ H + 1)
    (hG1 : bitLen (env .G1).natAbs ≤ H + 1) (hG2 : bitLen (env .G2).natAbs ≤ H + 1)
    (hmc : bitLen (env .MC).natAbs ≤ H) (hda : bitLen (env .DA).natAbs ≤ H)
    (hss : bitLen (env .SS).natAbs ≤ H + 1) :
    pBnd.cost Op.sem (kap C Mul (solW H)) env ≤
      15 * (C * Mul (solW H) + C + 20 * solW H + 43) +
      2 * (C * (solW H * solW H + 2 * solW H + 1) + 20 * solW H + 43) +
      6 * (C * (2 * solW H + 1) + 20 * solW H + 43) ∧
    ∀ v, bitLen (ev pBnd env v).natAbs ≤ solW H := by
  have hβ : ∀ v, bitLen (env v).natAbs ≤ βBnd H v := by
    intro v
    cases v <;> first | exact hall _ | assumption
  have hchk : sChk (orc C Mul (solW H)) (solW H) pBnd (βBnd H) := by
    simp only [pBnd, block, op, sChk, sBnd, eChk, eRb, orc_rb, orcRb, Function.update_apply,
      reduceCtorEq, ↓reduceIte, βBnd, solW]
    omega
  obtain ⟨h1, h2⟩ := sBnd_sound (orc_sound C Mul (solW H)) pBnd (βBnd H) env hchk hβ
  refine ⟨h2.trans ?_, fun v => (h1 v).trans ?_⟩
  · simp only [pBnd, block, op, sU, eU, orc_U, orcU]
    by_contra hc
    omega
  · cases v <;> simp only [pBnd, block, op, sBnd, eRb, orc_rb, orcRb, Function.update_apply,
      reduceCtorEq, ↓reduceIte, βBnd, solW] <;> omega

theorem pComb_cost (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) (env : V → ℤ)
    (hall : ∀ v, bitLen (env v).natAbs ≤ solW H)
    (hZ1 : bitLen (env .Z1).natAbs ≤ H + 1) (hZ2 : bitLen (env .Z2).natAbs ≤ H + 1)
    (hG1 : bitLen (env .G1).natAbs ≤ H + 1) (hG2 : bitLen (env .G2).natAbs ≤ H + 1)
    (hW1 : bitLen (env .W1).natAbs ≤ H) (hW2 : bitLen (env .W2).natAbs ≤ H)
    (hss : bitLen (env .SS).natAbs ≤ H + 1) (hhalf : bitLen (env .HALF).natAbs ≤ H)
    (hs2 : bitLen (env .S2).natAbs ≤ H) :
    pComb.cost Op.sem (kap C Mul (solW H)) env ≤
      6 * (C * Mul (solW H) + C + 20 * solW H + 43) +
      8 * (C * (2 * solW H + 1) + 20 * solW H + 43) ∧
    ∀ v, bitLen (ev pComb env v).natAbs ≤ solW H := by
  have hβ : ∀ v, bitLen (env v).natAbs ≤ βComb H v := by
    intro v
    cases v <;> first | exact hall _ | assumption
  have hchk : sChk (orc C Mul (solW H)) (solW H) pComb (βComb H) := by
    simp only [pComb, block, op, sChk, sBnd, eChk, eRb, orc_rb, orcRb, Function.update_apply,
      reduceCtorEq, ↓reduceIte, βComb, solW]
    omega
  obtain ⟨h1, h2⟩ := sBnd_sound (orc_sound C Mul (solW H)) pComb (βComb H) env hchk hβ
  refine ⟨h2.trans ?_, fun v => (h1 v).trans ?_⟩
  · simp only [pComb, block, op, sU, eU, orc_U, orcU]
    omega
  · cases v <;> simp only [pComb, block, op, sBnd, eRb, orc_rb, orcRb, Function.update_apply,
      reduceCtorEq, ↓reduceIte, βComb, solW] <;> omega

#assert_std_axioms pBnd_cost pComb_cost

end WP.W9fF
