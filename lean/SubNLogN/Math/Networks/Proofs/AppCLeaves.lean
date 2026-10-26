import SubNLogN.Math.Networks.AppCShear
import SubNLogN.Math.Networks.AppCLayer

/-!
# Proofs of small Appendix A leaves

Proofs of `ThreeShearsSwapStmt`, `RowPaddingLtStmt`, `PivotTripleEqStmt`, `RunEightSpecStmt`,
`Row46AdmissibleStmt` (statements in `AppCShear.lean`, `AppCLayer.lean`).
-/

namespace SubNLogN.Math.Networks

theorem threeShearsSwap_holds : ThreeShearsSwapStmt := by
  intro m Q x
  refine Prod.ext ?_ ?_
  · show x.1 + (x.2 - x.1) = x.2
    abel
  · show x.1 + (x.2 - x.1) - (x.2 - x.1) = x.1
    abel

theorem rowPaddingLt_holds : RowPaddingLtStmt := by
  intro R Wk hW hR
  have h1 : Wk * ((R + Wk - 1) / Wk) ≤ R + Wk - 1 := Nat.mul_div_le _ _
  omega

theorem pivotTripleEq_holds : PivotTripleEqStmt := by
  intro m Q i j x
  simp only [pivotTriple, Function.update_self, Function.update_idem, add_sub_cancel_right,
    Function.update_eq_self, Prod.mk.injEq, and_true]
  rw [add_comm]

theorem runEightSpec_holds : RunEightSpecStmt := by
  intro u w
  refine ⟨by simp [runEight, eightOps], ?_⟩
  have h1 : ∀ x : ℤ, (x + 1) % 2 = 1 - x % 2 := fun x => by omega
  have h3 : ∀ x : ℤ, (x + -1) % 2 = 1 - x % 2 := fun x => by omega
  rcases Int.emod_two_eq_zero_or_one u with hu | hu <;>
  rcases Int.emod_two_eq_zero_or_one w with hw | hw <;>
  simp [runEight, eightOps, hu, hw, h1, h3] <;> omega

theorem row46Admissible_holds : Row46AdmissibleStmt := by
  unfold Row46AdmissibleStmt xi46
  norm_num

end SubNLogN.Math.Networks
